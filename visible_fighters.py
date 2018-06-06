min_python_version = (3, 6)
import sys, os, string, tempfile, pickle, pickletools, lzma, textwrap, enum, bisect, hashlib, functools, operator, locale, argparse, io
from collections import namedtuple, OrderedDict, defaultdict, deque
from collections.abc import Sequence
from time import localtime, mktime, strftime
from random import random, randrange, uniform, normalvariate, sample
from base64 import b85encode, b85decode
from heapq import nlargest, nsmallest
from math import floor, ceil, exp, log, e, pi, erf, fsum
from contextlib import suppress, AbstractContextManager
from unittest import TestCase, TestSuite, TextTestRunner, defaultTestLoader
app_version, save_version = (0, 2), 1

# FORMAT_RAW не хранит эти настройки в сжатом потоке, поэтому для распаковки нужно указать те же, которыми упаковывались.
LZMA_OPTIONS = {'format': lzma.FORMAT_RAW, 'filters': [{'id': lzma.FILTER_LZMA2, 'preset': lzma.PRESET_DEFAULT}]}

# для default-параметров, где допустимо None
sentinel = object()

# impossible()
# impossible("сообщение")
# impossible(значение, "сообщение")
# "сообщение" может быть строкой или функцией без аргументов.
def impossible(*args):
	desc = args[-1] if args else None
	if callable(desc): desc = desc()
	value = f" ({args[0]})" if len(args) == 2 else ""
	raise AssertionError("Внутренняя ошибка" + ((": " if ": " not in desc else ", ") + desc if desc else "") + value + ".")

# 1. check(what, cond, errmsg)
# Возвращает what, если всё хорошо (cond), иначе возбуждает impossible. (cond может также быть функцией от what).
# Короче, assert с возвращаемым значением, чтобы всё в одну строку ебашить))0.
# Например: hp = check(new_hp, new_hp > 0, "недопустимое значение hp").
#
# 2. check(условие 1, impossible при невыполнении условия 1, ...)
def check(*args):
	if len(args) == 3:
		what, cond, errmsg = args[0], args[1], args[2]
		return what if (cond(what) if callable(cond) else cond) else impossible(what, errmsg)
	else:
		for i in range(len(args) // 2):
			if not args[2*i]: impossible(args[2*i+1])
		return args[0]

def throw(ecls, *args):
	raise ecls(*args)

# форматирует множественное число по правилам языка
# plural(3, "{N} слон{/а/ов}") → "3 слона"
def plural(n, fmt):
	form = ( # № формы в {один/два/много}
		2 if n % 10 == 0 or n % 10 >= 5 or n // 10 % 10 == 1 else # 7 слон_ов — форма 2
		0 if n % 10 == 1 else # 1 слон_ — форма 0
		1) # 3 слон_а — форма 1

	# преобразование фрагмента внутри {}: {N} либо {a/b/c}
	def handle(piece): return "" if not piece else str(n) if piece == 'N' else piece.split('/', 2)[form]

	# None вместо self вроде работает, не хочу объект создавать
	return "".join(literal + handle(bracketed) for literal, bracketed, _, _ in string.Formatter.parse(None, fmt))

def cap_first(s):
	return s[:1].upper() + s[1:]

# highlight_variant("y/n", 0) = "Y/n"
def highlight_variant(s, id):
	return "/".join(part.upper() if i == id else part for i, part in enumerate(s.split("/")))

# применяется в зеркалящихся элементах интерфейса
# left_to_right("HP", "[######....]", "6/10")            = "HP [######....] 6/10"
# left_to_right("HP", "[....######]", "6/10", flip=True) = "6/10 [....######] HP"
def left_to_right(*what, sep=" ", flip=False):
	return sep.join(filter(None, reversed(what) if flip else what))

def join_with_lastsep(seq, sep, lastsep):
	if not isinstance(seq, Sequence): seq = list(seq)
	return (sep.join(seq[:-1]) + lastsep if len(seq) > 1 else "") + (seq[-1] if seq else "")

def makefuncs():
	def maybewrite(filename, string):
		if filename:
			with open(filename, 'w', encoding='utf-8-sig') as f: f.write(string)
		return string

	# Сжимает строку в кашу, которую можно будет записать в исходнике короче оригинала.
	# Опционально читает из файла, записывает в файл и/или форматирует через pretty_decl.
	def pack_str(src=None, encoding='koi8-r', *, infile=None, outfile=None, pretty=True, **prettyargs):
		if infile:
			with open(infile, 'r', encoding='utf-8-sig') as f: src = f.read()
		result = b85encode(lzma.compress(src.encode(encoding), **LZMA_OPTIONS)).decode('ascii')
		return maybewrite(outfile, pretty_decl(result, **prettyargs) if pretty else result)

	# Распаковывает результат pack_str, опционально в файл.
	def unpack_str(src, encoding='koi8-r', *, outfile=None):
		return maybewrite(outfile, ''.join(lzma.decompress(b85decode(src), **LZMA_OPTIONS).decode(encoding)))
	return pack_str, unpack_str
pack_str, unpack_str = makefuncs(); del makefuncs

# Красивенько форматирует строку (предположительно длинную, предположительно результат pack_str) в питонье объявление.
# длина ограничивается width с учётом prefix, pad и кавычек; символы НЕ эскейпаются, поэтому при "\ в строке результат будет не валиден.
def pretty_decl(s, width=160, prefix="", pad="\t", cont_pad=None, multiline=False):
	if width < 1: raise ValueError("width должна быть >= 1")
	if cont_pad is None: cont_pad = "" if multiline else pad
	def pieces_gen():
		sp = 0
		start = pad + prefix
		opening_quotes = ending_quotes = '"""' if multiline else '"'
		cont_opening_quotes, cont_ending_quotes = "" if multiline else '"', "" if multiline else '"\\'
		if len(start) + len(opening_quotes) >= width: yield start + "\\"; start = cont_pad
		start += opening_quotes
		if multiline and len(start) + len('\\') >= width: yield start + "\\"; start = cont_pad

		while True:
			if len(s) - sp <= max(0, width - len(start) - len(ending_quotes)): yield start + s[sp:] + ending_quotes; return
			take = max(1, width - (len(start) + len(cont_ending_quotes)))
			yield start + s[sp:sp+take] + cont_ending_quotes; sp += take
			start = cont_pad + cont_opening_quotes
	return "\n".join(pieces_gen())

# Выбирает взвешенно-случайный элемент итерируемой последовательности, т. е. не требует len (в отличие от random.choice).
# «King of the hill» отсюда: https://eli.thegreenplace.net/2010/01/22/weighted-random-generation-in-python.
def choose(iterable, get_weight=lambda item, index: 1, default=sentinel, return_index=False):
	best, best_index, sum = default, -1, 0
	for index, item in enumerate(iterable):
		w = get_weight(item, index)
		if w > 0:
			sum += w
			if uniform(0, sum) <= w: best, best_index = item, index
			# uniform(a, b) может оказаться равен b из-за погрешностей, поэтому ни сравнивать uniform < w, ни пропускать сюда нулевые веса нельзя
	return ((best, best_index) if return_index else best) if best is not sentinel else throw(IndexError, "Ничего не выбрано.")

# common_prefix_len("привет", "прийти") = 3
def common_prefix_len(a, b):
	n, lim = 0, min(len(a), len(b))
	while n < lim and a[n]==b[n]: n += 1
	return n

# subseq_occurences генерирует все вхождения подпоследовательности ss в src
# Например: subseq_occurences("AB", "AABB") → [0, 2], [0, 3], [1, 2], [1, 3]
#                                    0123
#
# Внимание: для оптимизации возвращаемый список переиспользуется, его нельзя хранить, не скопировав.
#           т. е. не работает list(subseq_occurences(...)), зато работает list(occ[:] for occ in subseq_occurences(...))
#
# Внимание-2: экспоненциальная сложность в «плохих» случаях (ss="A"*5, src="A"*20).
def subseq_occurences(ss, src):
	p = [0] * len(ss)
	def reset(start):
		for i in range(start, len(ss)):
			p[i] = src.find(ss[i], (p[i-1]+1) if i > 0 else 0)
			if p[i] < 0: return False
		return True
	digit, lowest = -1, len(ss) - 1

	while True:
		if reset(digit+1): yield p; digit = lowest
		while digit >= 0:
			p[digit] = src.find(ss[digit], p[digit]+1)
			if p[digit] >= 0: break
			digit -= 1
		else: return

# поддержка key для функций из bisect (https://bugs.python.org/issue4356, https://stackoverflow.com/a/39501468)
def makefuncs():
	class KeyWrapper:
		def __init__(self, list, key): self.list, self.key = list, key
		def __getitem__(self, i): return self.key(self.list[i])
		def __len__(self): return len(self.list)

	def with_key(origf):
		def keyed(a, x, L=0, R=None, key=None):
			return origf(a if key is None else KeyWrapper(a, key), x if key is None else key(x), L, R if R is not None else len(a))
		return keyed
	bisect_left, bisect_right = with_key(bisect.bisect_left), with_key(bisect.bisect_right)
	def insort_right(a, x, L=0, R=None, key=None): a.insert(bisect_right(a, x, L, R, key), x)
	return bisect_left, bisect_right, insort_right
bisect_left, bisect_right, insort_right = makefuncs(); del makefuncs

# Наивный байесовский классификатор, украденный из https://habrahabr.ru/post/120194/.
# Коллбэк, передаваемый в конструктор, должен извлекать из классифицируемого объекта значащие признаки.
# guess возвращает (1) наиболее вероятный класс и (2) отрыв от предыдущего, приведённый к [0; 1] (или None, None).
# Например, пусть он угадывает пол по первой и двум последним буквам имени:
#
# guesser = BayesianGuesser(lambda name: ('0:'+name[0], '-2:'+name[-2], '-1:'+name[-1]))
# guesser.train({'Петя': 'M', 'Коля': 'M', 'Вера': 'F', ...})
# cls, margin = guesser.guess('Витя')
#
# Как учитывать margin — решать пользователю. Можно подобрать эмпирическое правило вроде
# if margin > 0.4: (воспользоваться результатом) else: (придумать что-то другое).
class BayesianGuesser:
	# Чтобы можно было передавать в samples как словарь, так и список пар.
	def pairs(self, samples): return samples.items() if isinstance(samples, dict) else samples

	def __init__(self, get_feats, samples=None, cheat=False):
		self.get_feats      = get_feats
		self.total_samples  = 0
		self.total_of_class = defaultdict(lambda: 0)
		self.total_of_cfeat = defaultdict(lambda: 0)
		self.cheat          = {} if cheat else None
		if samples: self.train(samples)

	def train(self, samples):
		for sample, cls in self.pairs(samples):
			if self.cheat is not None:
				self.cheat[sample] = cls if sample not in self.cheat or self.cheat[sample] == cls else None
			self.total_of_class[cls] += 1
			for feat in filter(None, self.get_feats(sample)):
				self.total_of_cfeat[cls, feat] += 1
			self.total_samples += 1

	# cfeat_prob — это P(wi|c) из статьи http://bazhenov.me/blog/2012/06/11/naive-bayes.html.
	# По ней же добавил аддитивное сглаживание (https://en.wikipedia.org/wiki/Additive_smoothing; в Хабро-варианте вместо него использовалась константа 1e-7).
	SMOOTH = 1.0
	def cfeat_prob(self, cls, feat, feats_count):
		# .get(), чтобы для несуществующих ключей не создавались дефолтные значения, иначе ломает методы, рассчитывающие, что там нет нулей.
		return (self.total_of_cfeat.get((cls, feat), 0) + self.SMOOTH) / (self.total_of_class.get(cls, 0) + self.SMOOTH * feats_count)

	def guess(self, sample):
		if self.cheat:
			precise = self.cheat.get(sample, None)
			if precise is not None: return precise, 1.0 # можно брать и этим весь класс заменять...

		feats = self.get_feats(sample)
		n_feats = sum(1 for feat in feats if feat)
		best_cls = best_prob = second_best_prob = None

		for cls, count in self.total_of_class.items():
			# prob — вероятность (логарифм вероятности) того, что объект, принадлежащий cls, имеет признаки sample
			Pc = count / self.total_samples
			prob = log(Pc) + sum(log(self.cfeat_prob(cls, feat, n_feats)) for feat in feats if feat)

			if not best_prob or prob > best_prob:
				best_cls, best_prob, second_best_prob = cls, prob, best_prob
			elif not second_best_prob or prob > second_best_prob:
				second_best_prob = prob

		return best_cls, 1.0 - exp(second_best_prob - best_prob) if second_best_prob is not None else 1.0 if best_prob is not None else None

	# оценивает точность классификации на тестовой выборке
	# TODO: переделать на http://bazhenov.me/blog/2012/07/21/classification-performance-evaluation.html.
	def success_rate(self, samples):
		success = total = 0
		for sample, ref_cls in self.pairs(samples):
			if self.guess(sample)[0] == ref_cls: success += 1
			total += 1
		return success / max(1, total)

	# статистика по наиболее информативным признакам, как в http://www.nltk.org/_modules/nltk/classify/naivebayes.html
	# возвращает список 3-тюплов (feat, cls, margin), например, (feat = "LAST_TWO_LETTERS:на", cls = Gender.FEMALE, margin = 12.5)
	# margin∈[1; +∞] — разрыв с наименее вероятным по feat. Возможно, больше смысла возвращать, наоборот, отрыв от второго самого вероятного, как в guess.
	#
	# Была бы полезнее функция most_informative_fnames, которая бы указывала, какие *категории* признаков
	# были самыми информативными, а какие только мешали (возможно, в связке с success_rate), но я не знаю, как это сделать :(
	# Явного деления на категории нет, но пользователь обычно что-то такое подразумевает, вот как в примере префикс LAST_TWO_LETTERS.
	def most_informative_feats(self, n=None):
		informative_feat = namedtuple('informative_feat', 'feat, cls, margin')
		class feat_info:
			__slots__ = ('min_prob', 'max_prob', 'max_prob_class', 'occurences')
			def __init__(self):
				self.min_prob, self.max_prob, self.max_prob_class, self.occurences = 1, -1, None, 0
		feats = defaultdict(lambda: feat_info())

		for (cls, feat), cf_count in self.total_of_cfeat.items():
			f = feats[feat]
			f.occurences += 1
			cf_prob = cf_count / self.total_of_class[cls]
			if cf_prob == 0: print(cls, feat, cf_count, self.total_of_class[cls])
			f.min_prob = min(f.min_prob, cf_prob)
			if cf_prob > f.max_prob: f.max_prob, f.max_prob_class = cf_prob, cls

		result_gen = (informative_feat(feat, f.max_prob_class, f.max_prob/f.min_prob) for feat, f in feats.items() if f.occurences > 1)
		key = lambda f: f.margin
		return sorted(result_gen, key=key, reverse=True) if n is None else nlargest(n, result_gen, key=key)

class Gender(enum.IntEnum):
	UNKNOWN, MALE, FEMALE, NEUTER, TOTAL = -1, 0, 1, 2, 3

	@staticmethod
	def detect(name):
		# С L2-L3 бессовестно нарушается предположение о независимости признаков, но результат вроде лучше, кхехех.
		oracle = BayesianGuesser(lambda w: (('F2', w[0:2]), ('L2', w[-2:]), ('L3', w[-3:])),
			samples = ((sample, gender)
				for samples_pack, gender in ((Gender.male_names_pack, Gender.MALE), (Gender.female_names_pack, Gender.FEMALE))
				for sample in unpack_str(samples_pack()).split()), cheat=True)

		best_guess, best_margin = Gender.UNKNOWN, None
		for _lit, word, _isend in Noun.split_into_words(name):
			guess, margin = oracle.guess(word.casefold())
			if guess is not None and (best_margin is None or margin > best_margin) and margin > 0.4:
				best_guess, best_margin = guess, margin

		return best_guess

	# victim.name + victim.gender.ize(" подверг{ся/лась/лось} изнасилованию со стороны ") + rapist.name.genitive
	def ize(self, fmt):
		def handle(piece):
			if not piece: return ""
			per_gender = piece.split('/', Gender.TOTAL-1)
			return per_gender[self if self != Gender.UNKNOWN and self < len(per_gender) else Gender.MALE]
		return "".join(literal + handle(bracketed) for literal, bracketed, _, _ in string.Formatter.parse(None, fmt))

	# Сжатые pack_str списки lowercase-имён, разделённых пробелом.
	@staticmethod
	def male_names_pack(): return ";0mn;L0te~u$B>F1OsY;-1iO%j(2PxkXp30T;>ulh~r>8L^Y6@cJnWVPg57y)Eqboold%o4FDp4Q4B8hptW8PU>n${Tm_(g^h^r%Fqq=xK2)75A<(E-15A1#;;3koI"\
	"a*+91hdY-P~GOyzOXp&=s4VS)}>Sc1smRJ=1fp&2<i-feINUu!;1~RQYud2#+a`B$>?hm0BGx4+cA9ajNWfp^L8iX8VjlxtvQ#+G}tC&o1**TTQhK)x0nT;YheH2JX0pD<n0pQkp0&B>OafM{`Wr$BQcB*G>"\
	"|QqZOB8uTyA&q==4P0Y5IlmwgK$9;udCbCxsqfa#;-qYkI}G>u<Dt=wqXxFD~_M4x1;!UlAK=_2W1Pn!zM-YLq%_U?AbbqjKcmgg*AO!WI^AH<PW2ugyp(TJ9~fuh7NFr!6)QhPMy%;o`)_a`5T;kx8ASDq>"\
	"&kTEL{O;ySs4Y0_py@E-dqqOzeDgykW^&7Z_VAw_+jPLdMOvW_=9`qA(a%F3@}_-btU33ZrInZ$eRvpz+pyN81Z;UChgfa<F*_f~=VVAh;7<MF~Lvg3+AH&0mI;vVUH!qnRJ_ukS-RhW2+(k?4*GaiF5mOCG"\
	"xYoAx%W5RrjBXfjXHoDKmp#ZA9!mVDsQ8asa6G&630f{&bOZs?xW}r#y;t{hSNkT!a1O`CfC%E{QDM#@s9wAE&FfLO!RonC+iW7ae#>fuRYO-GS2zk~%!dg}pRULL^L|<Ju>qfTxkvseaB4z+2I<mdoXbrzX"\
	"tvDWagL-7>fzMb<i}4^-#e9eEvK>W5KNuL&xIOR*JSoY>*8cc|Wpqow9_HHsbR};7I?fF}-Mv7B0SnOt*`l9GO?($!edszTHc(x%kTdayz5uQi&JB^vW@6s_S0nEZ=@c8WBACg8-fQuEE!1MzR^icBfMPts<"\
	"|wO~%-h5gG^+BqusX~PPwrtuG~zzl!KiQ~8P741S6Z8ZmDRKv86%XZ77&t+uiwjarNudO_^DGjZQyAKn}$MT+Jcw~Pqfb|=|iHtvBgAQ_Hk%jKd-KT8p2sSIqb=aM+rO~os!r#(v%{n59?u7V~atdi|S~R4("\
	"tgQD+$7>7y^VpME2lB<K!btU3&1Y9%+RkT|L*g!fT)!fG7x{$GOp(59iHITUJc#u={-4d<3(v+LE3^aX8KuUJX@Non?qgbq+w2VOC3Wa>Q94k4yj}$f&F*Hs!J9cU{JD<)?>}9MgzCVAwL^iHSS#!6!RmH}*"\
	"Z5qMbiNRnh8Xz%?P%+8PiYMhLoJzO{GeB<8J6F(%Ede)utC0|{%I7VD}dVBV@wlZHSkJ$hK*!u5W*;+Nf=_Lj2?h<ZLb*OZ@g36=QhxR5Er4JFX0(C-KrNtDZOA0sjto%Wmys6R+LD4F&M%OC!Izrn_FpdcF"\
	"UK_6M@ajEP{iY0=CSVEb2RKFCfe_=vP-Oc*vLk^5NbSpplu2YqL;hE^Me4~MoT0n*$;kKu!8%fU==m?gTHKE4}m7>~?Y<gH<Nb6lJZNDs%h&6L@WpF<E3RdALz%E5S>tR%=p$8xciObsKWt0?x`|DyAx(D4g"\
	"k@06WA4{kx@i{!HNX$Ol!%k!KYyOC?%Od4-ymvHJVRE&^-+{(9RQ=UD!s;@hW@F0Jjm8;C5diHo3nPjXDulEht42V}Bz`<_EPiv&!UNYff*8R&kIG-E*oj7Z0oC&0;a9v0%;?hvwooC+P_WBSz@u7Ex$F4vQ"\
	"!z=z00"

	@staticmethod
	def female_names_pack(): return ";0+T6c3l8qwbXgy{Sy6!=9&XmC4Wf-E37d?g7TwSdsUWs%HwV#sPx^La8Ust(}YhY+`_DI>rvda@(v@?o*m1wHDbA07E%|WW6F%8#pyR-^4ON<pvTfgGf^5q17~O"\
	"D$IB|7wYI4dF_WnF*^nSLPtrdJV>}`xE}=LM?)L=P2hYcJo8{i3yzG@q7ph4zKAA5kef&PjPZBX5Yc6}Lpc*S{%$G}r#Cqe;{)sz?6vmJWX^R{&5H6E1x{Q#>fV543j`dd_*})*$pBsET_!gG=i^3Lp(smnm"\
	"=&)L=J|=}(W=JFv4$!eAinM}`e-%#ISko!O-)*B^pS)$0+S#N@8^j+e8jLoeA!*SQ@j$KG4@fE|>|XfeGv`fR05G58PHtqy!-98xpNt>eU_}!AtVa~^*VeoiIkUIe_3G);(~@in-EWiDzx&~l5+<dUc-%=pV"\
	"B<bS&5Ey<k-6PpI@J8k&i4191iTgprE}OS9U@5RZs~ql?s={F2%tFt18NA){|?;q4a}%QE2sP733y%EO&GE4SW6uk8~CKmXkuFZC*^hV-5o26sheX5KA3UjNI-ezQ0tDD`LS<J0tXFBsn1ujMw=hhwU{y3kK"\
	"Y6Ss~RA3ziVMu#7vY>_Lc!$Km+EEMe}^KZRf&-zQJFpL8s8^P0wIF0HQi4LZa4``BEF|YZ40{Zf48cebKqo$)ZOy76_)P!RyTe1m4TnsETsW5~q=awZRr?O1DyvwAy$jzHz~|F3Kq%!K<LI3w)JM(=w7xwYZ"\
	"|=R8(oyezg+}&@hdq8kc_YmXwBjNtpkgEEZ}L8miUG@+xaS^dIYzZ+b;T8Vblq^srvPaP22AI@FiWh|nd!j>g~JdLM+ue|axH&EeJGD}zjkKd4W)++*)IQ=3?AlLNJJxRg8+={QgsH=sgfTPy6YX^Twy5Pbw"\
	"CB++IxSJGTAmk8Mh;{WBg&p$+ya$hH8t8-qSveYKyDzy6D?`JbteKLgLP>M@<<g@>nQW|=sok7lejm7YGG$l6qAs6lKdWLXdOjrh5r)|fXobcXdc0c1V+E3KI+&~GVa0bUEQyLSZKtd4Y4{%}VUa!cg1nO;P"\
	"ezZ<lUN$SRm`03v&~4D0(0FK-Y3B=C?U9gr=c69EMPH%7)}GN}AK%tsDF=i-iI7nUBb6DU%s9b+GuF;h2!N7&s@(;GfQ?`L?~zlpB0;htf4Uy35rc%!rf0T*`g@y(9P;wi`5Q*O3LJ@v9@Q7nhX2$|{-GZ>v"\
	"d~qJ&=7Paaahf2sd)R0FfU|y;7x3}?wAraj&FI+<aClALA7}RzCCSYIG3ocfO39?74(9Ek0ti6ushohko<Mf@XSawQQ6DGJJ#;3q(3I)R%<7i7wU-!WI8`F5!=dwI-Z6c$ue5T7!IQe=AfsUf;lrny&<>+hk"\
	"!0OXFWA~Pgf4mrt9zStg=3DP?2B;S~da9`xQpTz7Xh`l;UoGcM>98L`R2l;hab>+`ImuWL^pt=@j8V=J{P@O0vm=k?n{eVr-+HW`G$53|9x0Eq<y{--(W2JoMaeD8;m{1HfFD0?KT~;}x&t$oDCgaq+0t(8C"\
	")MsvO1C0}*v;l4_UT4zzB0jg4hRPIqfCOT}#`FoutGY8U^Ph4<+XD|+z3CSmJo#jRKdZl8<C*w3+?kYm?M{^+!$bLoYkf2LFYZl%0r=Z#hlo5Ns1kTYa7xa(zR1j}pT+bvmfh54c20{g!Xqy**6k3J!aIXP8"\
	"CF9H&I!9P3W#7GaE&IXrNb<uKLHwFr6TVWp;&O!C~t}&f_W>2@3pWpv3+mmNyXmRE$2wczTzyJ"

class Case(enum.IntEnum):
	NOMINATIVE, GENITIVE, DATIVE, ACCUSATIVE, INSTRUMENTAL, PREPOSITIONAL, TOTAL = 0, 1, 2, 3, 4, 5, 6
	@staticmethod
	def from_letter(letter):
		try:
			return Case('NGDAIP'.index(letter)) if letter else Case.NOMINATIVE
		except ValueError as e:
			raise ValueError(f"Неизвестный падеж: {letter}.") from e

# Noun.parse("маленьк{ий/ого/ому/ий/им/ом} член{/а/у//ом/е}").genitive == Noun.guess("маленький член").genitive == "маленького члена"
# Noun.parse("{кусок} угля").prepositional == "куском угля"
# Наследование от str нужно *исключительно* для того, чтобы можно было обращаться как с str, если достаточно словарной формы.
class Noun(str):
	def __new__(cls, pieces):
		if not isinstance(pieces, list): impossible(pieces, "исп. Noun.parse / Noun.guess" if isinstance(pieces, str) else "pieces")
		self = super().__new__(cls, Noun.join_pieces(pieces, Case.NOMINATIVE))
		self.pieces = pieces
		return self

	@staticmethod
	def join_pieces(pieces, case):
		return "".join(piece for literal, cases in pieces for piece in (literal, cases[case] if cases else ""))

	def __call__(self, case):
		return Noun.join_pieces(self.pieces, case)

	def __eq__(self, other):
		check(other, other.__class__ == Noun, lambda: f"вряд ли вы хотели сравнить с {other.__class__}")
		return isinstance(other, self.__class__) and self.pieces == other.pieces

	@staticmethod
	def append_pair(pieces, literal, cases): # ненужная оптимизация, чтобы не бить строку в месте, где guess_one так ничего и не придумала
		if pieces and not pieces[-1][1]:
			pieces[-1] = pieces[-1][0] + literal, cases
		else:
			pieces.append((literal, tuple(cases) if isinstance(cases, list) else cases))

	@staticmethod
	def parse(src, *, animate=False, gender=Gender.UNKNOWN, return_gender=False):
		pieces = []
		for literal, bracketed, spec, _ in string.Formatter.parse(None, src):
			if bracketed:
				cases = bracketed.split('/', Case.TOTAL-1)
				if len(cases) == 1:
					for sym in spec or '':
						if sym == 'a': animate = True
						elif sym == 'm': gender = Gender.MALE
						elif sym == 'f': gender = Gender.FEMALE
						elif sym == 'n': gender = Gender.NEUTER
						else: raise ValueError(f"\"{src}\": неожиданное вхождение \"{sym}\" в \"{spec}\".")
					Noun.append_pair(pieces, literal, None)
					Noun.guess_multi(pieces, cases[0], animate, gender)
					continue
				elif len(cases) != Case.TOTAL:
					raise ValueError(f"\"{src}\": должно быть 6 падежей {{A/B/.../F}}, \"{bracketed}\".")
			else:
				cases = None
			Noun.append_pair(pieces, literal, cases)

		r = Noun(pieces)
		return (r, gender) if return_gender else r

	@staticmethod
	def guess(src, *, animate=False, gender=Gender.UNKNOWN):
		pieces = []
		Noun.guess_multi(pieces, src, animate, gender)
		return Noun(pieces)

	@staticmethod
	def guess_multi(pieces, src, animate, gender):
		for literal, word, isend in Noun.split_into_words(src):
			base, cases = Noun.guess_one(word, animate, gender, maybe_adjective=not isend)
			Noun.append_pair(pieces, literal + base, cases)

	# мне очень влом тестировать все ветки, хотя надо бы
	@staticmethod
	def guess_one(word, animate, gender, maybe_adjective):
		def ngdip(nom, gen, dat, ins, pre): return (nom, gen, dat, gen if animate else nom, ins, pre)
		def yi(prev): return 'ы' if prev in 'бвдзлмнпрстфц' else 'и'
		def oe(prev): return 'е' if prev in 'нр' else 'о'
		vowels = 'аеёиоуыэюя'
		if maybe_adjective:
			if word.endswith('ый') and (gender == Gender.UNKNOWN or gender == Gender.MALE):
				return word[:-len('ый')], ngdip('ый', 'ого', 'ому', 'ым', 'ом')
			elif word.endswith('ий') and (gender == Gender.UNKNOWN or gender == Gender.MALE):
				return word[:-len('ий')], ngdip('ий', oe(word[-3:-2]) + 'го', oe(word[-3:-2]) + 'му', 'им', oe(word[-3:-2]) + 'м')
			elif word.endswith('ой') and (gender == Gender.UNKNOWN or gender == Gender.MALE):
				return word[:-len('ой')], ngdip('ой', 'ого', 'ому', yi(word[-3:-2])+'м', 'ом')
			elif word.endswith('ая') and (gender == Gender.UNKNOWN or gender == Gender.FEMALE):
				return word[:-len('ая')], ('ая', 'ой', 'ой', 'ую', 'ой', 'ой')
			elif word.endswith('яя') and (gender == Gender.UNKNOWN or gender == Gender.FEMALE):
				return word[:-len('яя')], ('яя', 'ей', 'ей', 'юю', 'ей', 'ей')
		if word.endswith('ия'):
			return word[:-len('я')], ('я', 'и', 'и', 'ю', 'ей', 'и')
		elif word.endswith('а'):
			return word[:-len('а')], ('а', yi(word[-2:-1]), 'е', 'у', 'ой', 'е')
		elif word.endswith('я'):
			return word[:-len('я')], ('я', 'и', 'е', 'ю', 'ей', 'е')
		elif any(word.endswith(sym) for sym in 'бвгджзклмнпрстфхцчшщ') and (gender == Gender.UNKNOWN or gender == Gender.MALE):
			if word.endswith('ок') or word.endswith('ёк'):
				before = ("й" if word[-3:-2] in vowels else "ь") if word[-2:-1] in 'ё' else ""
				return word[:-len('ок')], ngdip(word[-2:], before + 'ка', before + 'ку', before + 'ком', before + 'ке')
			elif word.endswith('ец'):
				if word[-3:-2] in vowels:
					return word[:-len('ец')], ngdip('ец', 'йца', 'йцу', 'йцом' if word[-4:-3] in 'у' else 'йцем', 'йце')
				else:
					return word[:-len('ец')], ngdip('ец', 'ца', 'цу', 'цом', 'це')
			else:
				return word, ngdip('', 'а', 'у', 'ом', 'е')
		elif word.endswith('й') and (gender == Gender.UNKNOWN or gender == Gender.MALE):
			return word[:-len('й')], ngdip('й', 'я', 'ю', 'ем', 'е')
		elif word.endswith('ь') and gender == Gender.FEMALE:
			return word[:-len('ь')], ('ь', 'и', 'и', 'ь', 'ью', 'и')
		elif word.endswith('ь') and (gender == Gender.UNKNOWN or gender == Gender.MALE):
			return word[:-len('ь')], ngdip('ь', 'я', 'ю', ('ё' if word.endswith('арь') else 'е') + 'м', 'е')
		else:
			return word, None

	@staticmethod
	def split_into_words(src):
		def is_word_char(ch): return 'а' <= ch <= 'я' or 'А' <= ch <= 'Я' or ch in 'ёЁ-'
		i = 0
		while i < len(src):
			lit_start = i
			while i < len(src) and not is_word_char(src[i]): i += 1
			word_start = i
			while i < len(src) and is_word_char(src[i]): i += 1
			yield src[lit_start:word_start], src[word_start:i], i == len(src)

	def src(self, sep="/"): return "".join(piece for literal, cases in self.pieces for piece in (literal, "{" + sep.join(cases) + "}" if cases else ""))
	def cap_first(self): return cap_first(self)

	names_pack = "-~*=uP+b6EwbQNB8YkMB>EYo0pG@2Gy)(};Q(<{OYfTwU^}XzStFJAUefGJ(sBrku?W_fUiN!?*4-~MSfyau%W+!~fkO}zE+8a8wWZilMI^L>hs?k#759QRL;(xh&fuF^YR;h^)lwqvKTOY"\
	"kNbZ=5;mUq;h??wGkL;sY)OMpXC$$-#LfC;rLRI<e5hYR^+P2OwNvh9**E}#Sbs1|&HyMc?gCIQ8f38Uh~f~XNTkn)~~+pFHLkI~t=o*K`dndQ<fw^G!8tPqWPN1%$U^Od@z3bM1gSV{WM;4vV1kAT3gqg02"\
	"h&`Iey3FHP-4GhMt4FI9p(I2YqxWk8KEgFUVb@1c^<&3S!-@F5bNxS|f`VK}jl9IL|_@^hxW2V!Q?iNd*!83BcW7=|4ygLvK63<UP^4h!9@4KQ~xcUr=$-S!WG<m#%vYnV;-L4;^D0gIfL}mD^Mw{2Oq268e"\
	"6HRtF_jtw&)26O!eM|QL1p*uZE6y^Wv8rmFg+(FIsakoUI(ujsz96+xjwx7#cB%)oEr8MvWdUx3tr5{C{Y>d6Ey}KxLRB@7-9OJsptI|gf4y5)pWC8AoiEi=!W%hg>C&t<rcjZYp!2ER1$th}q+GhVTCs$@%"\
	"h=9cSI$DZzJT-%ilhsr^D3DsTZ;zqJZI5b?j4`Ud@uryTCqWMO}!t0<1H79ZZ6Q1SR=j<`oh%4!!M5golaL=#jHK3-&Y6Od)50FT#UkS3&51BI)Ew?X?twuIPr8P4Tlf*p+9c<E{S3Q"

	adjs_pack = "-~}E6kX-;^u@*Ee{cN=|z9K_3hS1v_P@g`XiR+XK=j<U&<9u?9Y7pkD#ssC>3Q~MTp+2z_WOIm~(P4yn_Q3rBkLnNCB_+284gE!0yG%#;vZ}<=T+uQ_Vi-mHc^BO)2v?+T)!O1)Fh$HwjH8a"\
	"!wM6^qG=G95*_CQma`$`CK#3t6_>2hNWSz9LuRDH<vq(O{%;{*z=%X5>Z2e+stG>I;RqqA1X+tlwB_d>cQer(}2__*jqtP_rA49T0GT4BBkCJ(m>0HDw%#6<j*-%h0%$jr~GoP!+(Ag+_oVbGAv!ZinqRU$~"\
	"Qqhe&D3au2!Ii`29+Qb#bgnSub?i-e;esg4aYn|V2J*Q?NqDH2-Qni_h9Q|be8^6N1=pfV8=>81y8~{0+Wx{TaFMLJ^07J5=B5ZKhWJPU56Im>zeY=28;;(*={RCPqod=byk&VZt;jk%e;#mdU0;ZF$;WTuX"\
	"MZV+Bdv9sVH;i8r!-|B<Q$Gs!4xVAU6-}_X+N0b;##3oq@`mnD1w~s>atqHHozGHuw#k0E+=hV--4$tjkbCcCS*S{Yov5Sw#j>5=Y@FSpl2F-E%G{fuTKa2ItQ|~JI*^#59K(BZjJ9sA(u^f8gWfZW*n8!gV"\
	"39!wsOiub;8&K$`SPsR|SGfWQgb>QOy~hpC&^x`w@*k!WpBO#s5{z4)a6^+eNNXG?F5DS4!J~<pS@K;&h?Sr*RPW_rFfGH}|Kjb_q|_K-O(4!L(o_buIwXs$}<`sMVA292TkVZwUrXA^=p_Uvw~hzcf)0911"\
	"65fVr|k?FEl|WJv=C?3Y^>=E>#7*CnO#?O1x49<;aR92lTohUt*CqfiKv&nEx?"

	@staticmethod
	def feminize_adj(w):
		if w.endswith('ый') or w.endswith('ой'): return w[:-2] + 'ая'
		elif w.endswith('ий'): return w[:-2] + ('я' if w[-3:-2] in 'н' else 'а') + 'я'
		elif w.endswith('н'): return w + 'а'
		else: return w

	class RandomNamesExhausted(Exception): pass
	# ban(type, part) — условие реролла на основании неугодных слов.
	# see(type, part) получает напосмотреть части результата, когда он уже готов.
	# где type — 'adj' или 'noun', а part — соответственно, само прилагательное или существительное.
	@staticmethod
	def random_name(*, ban=None, see=None, return_gender=False):
		names, adjs = tuple(unpack_str(pack).split() for pack in (Noun.names_pack, Noun.adjs_pack))
		while True:
			if not adjs or not names: raise Noun.RandomNamesExhausted("Случайные имена закончились.")
			iadj, iname = randrange(len(adjs)), randrange(len(names))
			adj, name, gender = adjs[iadj], names[iname], Gender.MALE
			if name.endswith('{f}'): name, gender = name[:-len('{f}')], Gender.FEMALE
			if ban and ban('adj', adj): adjs = adjs[:iadj] + adjs[iadj+1:]; continue
			if ban and ban('noun', name): names = names[:iname] + names[iname+1:]; continue
			if gender == Gender.FEMALE: adj = Noun.feminize_adj(adj)

			# против «ангельских ангелов»
			adj_l2 = len(adj) - (2 if adj.endswith('й') else 0)
			px, shortest = common_prefix_len(adj.casefold(), name.casefold()), min(adj_l2, len(name))

			def false_positive():
				# «странный странник» — забавно, но OK
				# «бессмертный бес» etc. — OK; единственная тавтология с «бесом» — «бесноватый»
				# «голубой голем», «роковой рокер» — OK
				return adj.startswith("странн") or name == "бес" and not adj.startswith("бесн") or name in ("голем", "рокер")

			if shortest // 2 + (1 if shortest <= 3 else 0) < px and not false_positive():
				# не изменять оригинальные adjs/names
				if randrange(2) > 0: adjs = adjs[:iadj] + adjs[iadj+1:]
				else: names = names[:iname] + names[iname+1:]
				continue

			result = cap_first(adj) + ("" if adj.endswith('-') else " ") + name
			if see: see('adj', adj); see('name', name)
			result = Noun.guess(result, animate=True, gender=gender)
			return (result, gender) if return_gender else result
Noun.PLACEHOLDER = Noun.parse("{баг}")

def add_methods():
	# Объявляет Noun.genitive = property(lambda self: self(Case.GENITIVE)) и так для всех падежей.

	# Здесь и далее используется нечитаемая конструкция
	# > (lambda value: do_something_with(value))(get_value())
	# или чуть менее нечитаемая
	# > (lambda value=get_value(): do_something_with(value))()
	# вместо
	# > value = get_value()
	# > do_something_with(value).
	# Иногда это просто чтобы выебнуться, но иногда, в т. ч. здесь, без вспомогательной функции работать не будет из-за особенностей скоупинга в Python.
	# Объяснение: http://stupidpythonideas.blogspot.com/2016/01/for-each-loops-should-define-new.html.
	for case in Case:
		if case not in (Case.NOMINATIVE, Case.TOTAL):
			(lambda case=case: setattr(Noun, case.name.lower(), property(lambda self: self(case))))()
add_methods(); del add_methods

class TestCase(TestCase):
	def cases(self): return ()
	def one(self, *args): pass

	def test_cases(self):
		for args in self.cases(): self.one(*args)

class NounTest(TestCase):
	def cases(self): return (
		("Злобн{ый/ого/ому/ого/ым/ом} Буратино", "Злобн{ый|ого|ому|ого|ым|ом} Буратино"),
		(("Злобный Буратино", {'animate': True}), "Злобн{ый/ого/ому/ого/ым/ом} Буратино"),
		(("Рика", {'animate': True}), "Рик{а/и/е/у/ой/е}"),
		(("Слон", {'animate': True}), "Слон{/а/у/а/ом/е}"),
		("...{большой кусок} угля", "...больш{ой/ого/ому/ой/им/ом} кус{ок/ка/ку/ок/ком/ке} угля"))

	def one(self, base, expect_src):
		n = Noun.guess(base[0], **(base[1] if len(base) >= 2 else {})) if isinstance(base, tuple) else Noun.parse(base)
		self.assertEqual(n.src(sep='|' if isinstance(base, str) and '/' in base else '/'), expect_src, f"forms({base})")

def clamp(x, a, b): # эти странные конструкции — (бессмысленная) оптимизация общего случая (a <= x <= b) и паранойя x=NaN.
	return x if (x >= a) and (x <= b) else b if x > b else a

def mix(a, b, x):
	return b*x + a*(1-x)

# XOR с псевдослучайными числами, чтобы некоторые строки не светились в файлах в неизменном виде.
# http://www.pcg-random.org/
def pcgxor(seq, seed=0, mask=255):
	def pcg(state, inc):
		while True:
			# в оригинале состояние апдейтится *после*, наверное, чтобы не оставалось в памяти, но у меня тогда плохое первое число получается —
			# собственно, оригинальная не минимальная реализация его выбрасывает. Но тогда будет больше кода :C
			state = (state * 6364136223846793005 + inc) & 0xFFFFFFFFFFFFFFFF
			xs, rot = (state >> 45) ^ (state >> 27) & 0xFFFFFFFF, state >> 59
			xs = (xs >> rot) | (xs << (31 & -rot))
			yield from (xs>>r&mask for r in range(0, 32, 8))

	# эти ^ с нетривиальными числами так-то не нужны, просто seed=0 даёт 0 первым числом
	return bytes(b^r for b, r in zip(seq, pcg(seed^18446744073709551557, seed^2305843009213693951|1)))

# Хэш для команд, которые не должен узнать даже реверсер.
def b85digest(data):
	return b85encode(hashlib.blake2s(data.encode()).digest())

# округляет 8.2 до 8 с шансом 80% или 9 с шансом 20%
def rand_round(x):
	f = floor(x)
	d = x - f
	return f + int(d > 0 and random() < d)

# Интегрирование трапециями.
#            /---D---\
#  /---B----C    |    E
# A____|____|____|____|
#  step step step step
#
# Площадь трапеции с основаниями (L, R) и высотой step: 0.5 * (L + R) * step
# Сумма площадей: 0.5*(A + B)*step + 0.5*(B + C)*step + ... + 0.5*(D + E)*step = (0.5*A + B + C + D + 0.5*E) * step
def integrate(f, L, R, steps):
	return (fsum(f(L + (R - L) * (x/steps)) for x in range(1, steps)) + 0.5 * (f(L) + f(R))) * ((R - L) / steps)

# График распределения bell(min, avg, max) — график стандартного нормального распределения с отрезанными «хвостиками» за ±3,
# перемасштабированный из (-3, 0, 3) в (min, peak, max), где peak подбирается так, чтобы avg было средним значением.
#
#  |                      [avg]           |
#  |                        `  |          |
#  |                       ####|###       |
#  |                   ########|####      |
#  |                 ##########|#####     |
#  |              #############|######    |
#  |          #################|########  |
#  |###########################|##########|
# min                        peak        max
def makefuncs():
	def bell_with_peak(min, peak, max):
		if not min <= peak <= max: raise ValueError(f"Неверные параметры bell: min={min}, peak={peak}, max={max}, предполагается min <= peak <= max.")
		k = abs(normalvariate(0, 1/3))
		if k > 1: k = abs((random() + random() + random()) * (2/3) - 1) # Ц.П.Т.-фоллбэк на случай |normal| > 3, вообще можно им одним и обойтись :D
		d = min - peak if random() * (max - min) < peak - min else max - peak
		return clamp(peak + d * k, min, max)

	# Средним значением распределения с картинки будет
	# avg = peak + MC * (min - peak) + MC * (max - peak),
	# где MC — относительная X-координата центра масс половинки «колокола», т. е. приведённая из [peak; max] к [0; 1].
	# Выражая peak из avg, получим peak = (avg - (min + max) * MC) / (1 - 2 * MC).
	def deduce_peak(min, avg, max):
		return (avg - (min + max) * rel_3σ_MC) / (1 - 2 * rel_3σ_MC)

	def bell_with_avg(min, avg, max):
		return bell_with_peak(min, deduce_peak(min, avg, max), max)

	# http://www.wolframalpha.com/input/?i=int+(x-X)%2F(1*sqrt(2*pi))*e^-((x-0)^2%2F(2*1^2)),+x%3D0+to+3 — отсюда выразить X, и /3, т. к. формула была для σ=1.
	# Если прямо спросить solve (int (x-y)/(1/3*sqrt(2*pi))*e^-((x-0)^2/(2*1/3^2)), x=0 to 3) = 0 for y, оно отвечает через e^(81/2) — это сильная потеря точности.
	# Это значение приблизительное, т. к. не учитывает хвостики (у меня от http://sernam.ru/book_tp.php?id=60 мозг плавится). Либо можно их просто рероллить.
	rel_3σ_MC = (1-e**(-9/2))/(2*pi)**0.5/(0.5*erf(3/2**0.5))/3

	# Ванильная функция Гаусса — плотность вероятности normalvariate(mean, stddev).
	def gauss(x, mean, stddev):
		return exp(-abs(x - mean)**2 / (2*stddev**2)) / (stddev * (2 * pi) ** 0.5)

	# точное значение вероятности «трёх сигм» (99,7%), по которым обрезается normalvariate — erf(3/√2).
	S_under_3σ = erf(3/2**0.5)

	# Плотность вероятности bell_with_avg, т. е. функция с *приблизительно* (клятi хвостики) таким же графиком, как на картинке,
	# и интегралом по области определения = 1.
	def bell_with_avg_proba_dens(min, avg, max, x):
		peak = deduce_peak(min, avg, max)
		return gauss((peak - x) / (peak - min) if x < peak else (x - peak) / (max - peak), 0, 1/3) / S_under_3σ / (0.5 * (max - min)) if min <= x <= max else 0
	bell_with_avg.proba_dens = bell_with_avg_proba_dens

	return bell_with_avg
bell = makefuncs(); del makefuncs

class BellTest(TestCase):
	def cases(self): return (0, 7.2, 10, 1.0, 40),
	def one(self, L, avg, R, margin, steps):
		self.assertAlmostEqual(integrate(lambda x: bell.proba_dens(L, avg, R, x), L-margin, R+margin, steps), 1.0, delta=0.05)
		self.assertAlmostEqual(integrate(lambda x: x * bell.proba_dens(L, avg, R, x), L-margin, R+margin, steps), avg, delta=0.1)

class Distribution:
	class CantGuess(ValueError): pass
	def estimate_min(self): raise NotImplementedError("estimate_min")
	def estimate_avg(self): raise NotImplementedError("estimate_avg")
	def estimate_max(self): raise NotImplementedError("estimate_max")
	def roll(self): raise NotImplementedError("roll")
	# TODO: придумать что-нибудь с proba_dens, т. к. у константного распределения она вырождается в дельта-функцию T_T

	@staticmethod
	def guess(arg):
		if isinstance(arg, Distribution): return arg
		if isinstance(arg, (tuple, list)) and all(isinstance(x, (int, float)) for x in arg):
			if len(arg) == 1: return Distribution.Uniform(arg[0], arg[0])
			if len(arg) == 2: return Distribution.Uniform(*arg)
			if len(arg) == 3: return Distribution.Bell(*arg)
		raise Distribution.CantGuess(f"Ожидается распределение, получено: {arg}.")

def makeclasses():
	class Uniform(Distribution):
		def __init__(self, min, max): self.min, self.max = min, max
		def estimate_min(self): return self.min
		def estimate_avg(self): return 0.5 * (self.min + self.max)
		def estimate_max(self): return self.max
		def roll(self): return self.min if self.min == self.max else uniform(self.min, self.max)

	class Bell(Distribution):
		def __init__(self, min, avg, max): self.min, self.avg, self.max = min, avg, max
		def estimate_min(self): return self.min
		def estimate_avg(self): return self.avg
		def estimate_max(self): return self.max
		def roll(self): return bell(self.min, self.avg, self.max)
	return Uniform, Bell
Distribution.Uniform, Distribution.Bell = makeclasses(); del makeclasses

def trim_leading_spaces(s, start=0):
	pos = start
	while pos < len(s) and s[pos] == ' ': pos += 1
	return pos - start, s[:start] + s[pos:] if pos > start else s

# Главная причина существования этой функции в том, что textwrap.wrap, похоже, не обрабатывает \n.
#
# Также, если в строку добавлен |, то её хвост начнётся с этой позиции, например:
# wrap("Страх — |внутреннее состояние, обусловленное грозящим реальным или предполагаемым бедствием.", ...)
# ->
# Страх — внутреннее состояние, обусловленное
#         грозящим реальным или предполагаемым
#         бедствием.
def wrap(text, width):
	def wrap_paragraph(line, width):
		# извлечение управляющего |. До его вхождения, =| эскейпает дословный |.
		prefix, p = '', 0
		while p >= 0 and not prefix:
			p = line.find('|', p)
			if p > 0 and line[p-1] == '=':
				line = line[0:p-1] + line[p:]
			elif p >= 0:
				line = line[0:p] + line[p+1:]
				prefix = ' ' * p

		# drop_whitespace=True режет лишнее, например, пробел после запроса (y/N)
		pieces = textwrap.wrap(line, width, subsequent_indent=prefix, drop_whitespace=False)
		for i in range(1, len(pieces)): pieces[i] = trim_leading_spaces(pieces[i], len(prefix))[1]
		return pieces or ('',)

	return '\n'.join(wrapped_line for source_line in text.splitlines() for wrapped_line in wrap_paragraph(source_line, width))

# Другая обёртка над textwrap.wrap.
# Возвращает список записей (piece, start), где start — позиция этого фрагмента в исходной строке.
# Например: wrap_feedback("привет, как дела?", 7) => [('привет,', start=0), ('как', start=8), ('дела?', start=12)]
# Не поддерживает возможности предыдущего wrap (\n и |).
class WrapFeedback:
	__slots__ = 'piece', 'start'
	def __init__(self, piece, start): self.piece, self.start = piece, start

def wrap_feedback(text, width, maxlines=None):
	pieces = textwrap.wrap(text, width, drop_whitespace=False, max_lines=maxlines+1 if maxlines else None) or ("",) # а то отвечает [] на пустую строку
	result = [None] * min(len(pieces), maxlines if maxlines is not None else len(pieces))

	# Найти каждую строку результата в text. Предполагается, что это возможно.
	text_pos = 0
	for i in range(len(result)):
		# если textwrap.wrap() съедает что-то посередине, придётся искать как подпоследовательность, но пока вроде работает
		start_pos = text.index(pieces[i], text_pos)
		text_pos += len(pieces[i])
		# drop_whitespace=True режет лишнее, поэтому РУЧКАМИ.
		if i > 0:
			leading_spaces, pieces[i] = trim_leading_spaces(pieces[i])
			start_pos += leading_spaces
		result[i] = WrapFeedback(pieces[i], start_pos)

	return result

def exception_msg(e):
	return str(e) or repr(e)

# список команд, позволяющий сокращать их при отсутствии неоднозначностей
# guess возвращает (1) ассоциированную с командой функцию, (2) список вариантов при неоднозначности, (3) список подсказок при ошибке
# (всё это нужно сначала проверить на истинность, на данный момент всегда возвращается 0-1 из трёх)
#
# например:
# .add("hit", funcA)
# .add("hook", funcB)
# .guess("h") → None, ["hit", "hook"], None
# .guess("ho") → funcB, None, None
#
# .add("hit body", funcC)
# .guess("h b") → funcC, None, None
# .guess("h c") → None, None, ["hit body"]
#
# Также
# .add("a b", funcAB, "c d", funcABCD)
# эквивалентно
# .add("a b", funcAB)
# .add("a b c d", funcABCD)
class Commands:
	def __init__(self):
		self.root = Commands.node("", None)

	def add(self, *args):
		node = self.root
		iarg = 0
		while iarg < len(args):
			cmd, func = args[iarg], args[iarg+1]
			node = node.add(check(cmd, isinstance(cmd, str), "cmd?!"), check(func, "func?!"))
			iarg += 2

	def guess(self, input):
		def not_found():
			return None, None, self.suggest_something(input) or None

		def found(node):
			node = node.down_to_unambiguous()
			return node.func or None, None if node.func else self.suggest_something(start_node = node), None

		# best_subseq_matches делает практически всю грязную работу: выбирает из команд, для которых input является подпоследовательностью по символам,
		# «лучшие» по некоторым дополнительным критериям. После этого мало что остаётся сделать...
		matches = self.best_subseq_matches(input)
		if len(matches) == 1:
			return found(matches[0])
		elif not matches:
			return not_found()

		# ...разве что для красоты предусмотреть редкий случай, когда все найденные команды замаплены в одно действие, например, quit, exit и запрос «i».
		if matches[0].func and all(matches[i].func == matches[0].func for i in range(1, len(matches))):
			return found(matches[0])

		# Вернуть найденные варианты как подсказки. Если слишком много — выбрать случайные.
		MAX_ALTERNATIVES = 10
		if len(matches) > MAX_ALTERNATIVES: matches = [matches[i] for i in sorted(sample(range(len(matches)), MAX_ALTERNATIVES))]
		return None, [node.down_to_unambiguous().backtrack() for node in matches], None

	def best_subseq_matches(self, input):
		filtered_input = ''.join(sym for sym in input if self.classify_sym(sym) >= 0)

		# сколько последовательных символов inp, начиная со start, составляют подпоследовательность ref?
		# subseq_len("qualif", 0, "quod erat demonstrandum") = 3 ("qua")
		def subseq_len(inp, start, ref):
			iinp, iref = start, 0
			while iref < len(ref) and iinp < len(inp):
				if ref[iref] == inp[iinp]: iinp += 1
				iref += 1
			return iinp - start

		# sequences([1, 2, 5, 7, 10, 11, 12]) -> (1, 2), (5, 5), (7, 7), (10, 12)
		def sequences(ns):
			start = 0
			for i in range(1, len(ns)+1):
				if i == len(ns) or ns[i] != ns[i-1] + 1:
					yield ns[start], ns[i-1]
					start = i

		# Насколько хорошо узел найденной команды node соответствует вводу input?
		def score(node):
			best = None
			for occ in subseq_occurences(filtered_input, node.filtered_command):
				score = 0
				for a, b in sequences(occ):
					iword, word_start = node.word_from_sym_index(a)

					while word_start <= b:
						word_end = word_start + node.word_lens[iword] - 1
						start, end = max(a, word_start), min(b, word_end)
						d = end - start + 1

						# нелинейный бонус за идущие подряд символы, но в пределах слова (иначе из dex+ и spd+ по d+ выберет spd+)
						bonus = d*d

						# бонус за совпадение с префиксом слова (иначе предложит оба варианта из dex+ и spd+ по d+, или из remove 11 и remove 21 по remove 1)
						if start == word_start:
							bonus += 2*d
							# бонус за полное совпадение со словом, иначе по do A и do AB на do A предложит оба варианта
							if end == word_end: bonus += 1

						# совпадения в первых словах более значимы
						score += bonus / (1 + iword)
						word_start = word_end + 1
						iword += 1

				# бонус завершённой команде
				if node.func: score += 1

				if best is None or score > best: best = score
			return best

		def skip_spaces(start):
			while start < len(input) and self.classify_sym(input[start]) < 0: start += 1
			return start

		ongoing = [(self.root, skip_spaces(0))]
		best_nodes, best_score = [], None
		while ongoing:
			new_nodes = []
			for node, start in ongoing:
				start = skip_spaces(start + subseq_len(input, start, node.word))
				if start >= len(input):
					if node.parent: # это условие исключительно на случай input="", чтобы вернуло пустой список, а не пошло во все тяжкие.
						cur_score = score(node)
						if best_score is None or cur_score > best_score:
							best_nodes = [node]
							best_score = cur_score
						elif cur_score == best_score:
							best_nodes.append(node)
				else:
					new_nodes.extend((child, start) for child in node.childs.values())
			ongoing = new_nodes
		return best_nodes

	@staticmethod
	def classify_sym(sym): return (
		-1 if sym in string.whitespace else
		0 if 'a' <= sym <= 'z' or 'A' <= sym <= 'Z' else
		1 if sym in string.digits else
		2 if sym in '?' else
		3)

	@staticmethod
	def split(cmd):
		i, r, preved = 0, [], 0
		while i < len(cmd):
			start_cls = Commands.classify_sym(cmd[i])
			if start_cls >= 0:
				start = i
				while True:
					i += 1
					if i >= len(cmd) or Commands.classify_sym(cmd[i]) != start_cls: break
				r.append((cmd[preved:start], cmd[start:i]))
				preved = i
			else:
				i += 1
		return r

	def has_anything(self):
		return self.root.childs

	def suggest_something(self, input=sentinel, start_node=None):
		matches = [start_node or self.root]
		for _space, subcommand in Commands.split(input) if input is not sentinel else []:
			new_matches = [child for node in matches for cmd, child in node.childs.items() if cmd.startswith(subcommand)]
			if not new_matches: break
			matches = new_matches

		# если только один match, и это не корень (либо явно вызвано suggest_something() без input) —  развернуть в детей
		if len(matches) == 1 and not matches[0].func and matches[0].childs and (matches[0].parent or input is sentinel):
			matches = [match for match in matches[0].childs.values()]

		return [node.down_to_unambiguous().backtrack() for node in matches if node.parent]

	class node:
		__slots__ = 'childs', 'func', 'word', 'parent', 'space', 'word_lens', 'filtered_command'
		def __init__(self, word, parent, space=""):
			self.childs, self.func = OrderedDict(), None
			self.word, self.parent, self.space = word, parent, space

			# если node соответствует sp.dispell, в нём будет word = "dispell" и word_lens = [2, 1, 7]
			self.word_lens = parent.word_lens + [len(word)] if parent else []

			# Команда без пробелов для поиска соответствий. Манипуляции со словами (например, номер символа в word_from_sym_index) подразумевают именно её.
			self.filtered_command = (parent.filtered_command if parent else "") + word

		def add(self, cmd, func):
			node = self
			for space, subcommand in Commands.split(cmd):
				child = node.childs.get(subcommand, None)
				if not child:
					child = Commands.node(subcommand, node, space)
					node.childs[subcommand] = child
				node = child
			if node.func: raise RuntimeError("Команда {0} уже определена.".format(node.backtrack()))
			node.func = check(func, cmd)
			return node

		def backtrack(self):
			node, path = self, []
			while node.parent:
				path.append(node.space + node.word)
				node = node.parent
			return ''.join(reversed(path))

		def down_to_unambiguous(self):
			node = self
			while not node.func and len(node.childs) == 1 and node.parent: node = next(node for node in node.childs.values())
			return node

		def word_from_sym_index(self, start_sym):
			sym, iw = start_sym, 0
			while sym >= 0 and iw < len(self.word_lens):
				ns = sym - self.word_lens[iw]
				if ns < 0: return iw, start_sym - sym
				sym, iw = ns, iw + 1
			raise RuntimeError("sym вне слов")

class DummyCommands:
	@staticmethod
	def add(*args): pass

class CommandsTest(TestCase):
	def cases(self): return (
		(
			("one two three", "123"), ("one two four", "124"), ("one three six", "136"),
			("o t", None, ["one two", "one three six"], None), ("o t t", "123", None, None), ("o t s", "136", None, None),
		),
		(("spd-", "A"), ("sp.frailness", "B"), ("sp-", "A", None, None)),
		(("sp-", "A"), ("spd-", "B"), ("sp.frailness", "C"), ("sp-", "A", None, None)),
		(
			("1", "L1"), ("remove 10", "B"), ("remove 11", "C"), ("remove 21", "D"),
			("1", "L1", None, None), ("r1", None, ["remove 10", "remove 11"], None), ("r2", "D", None, None),
		),
		(("shop", "A"), ("shoot timestop", "B"), ("s", "A", None, None)),
		(("sp.dispell+", "A"), ("sp.frailness+", "B"), ("b.timestop-", "C"), ("il", "B", None, None), ("es", None, ["sp.frailness+", "b.timestop-"], None)),
		(("spd+", "A"), ("sp.frailness+", "B"), ("s+", "A", None, None)),
		(("rage V", "A"), ("rage Vo", "B"), ("rV", "A", None, None)),
		(("sp.fstorm+", "A"), ("sp.frailness+", "B"), ("fs+", "A", None, None)),
		(("dex+", "A"), ("spd+", "B"), ("d+", "A", None, None)))

	def one(self, *adds_and_queries):
		get_adds, get_queries = (lambda makegetf=(lambda itemlen: lambda: filter(lambda item: len(item) == itemlen, adds_and_queries)): (makegetf(2), makegetf(4)))()
		assert len(adds_and_queries) == sum(1 for items in (get_adds(), get_queries()) for item in items), adds_and_queries

		cmds = Commands()
		for add in get_adds(): cmds.add(*add)
		for query in get_queries():
			self.assertEqual(cmds.guess(query[0]), query[1:])

class MultipadMarkupError(Exception): pass

# ОЧЕ МАГИЧЕСКАЯ ФУНКЦИЯ (будет смешно, если такая есть готовая и более удобная).
# Выравнивает строки по именованным маркерам вида [имя].
#
# multipad([
#     "STR [A]5[B] -> [C]10[D]   [E]$100[F] / [G]1[H]",
#     "INT [A]10[B] -> [C]15[D]   [E]$150[F] / [G]1[H]",
#     "SPEED [A]15[B] -> [C]1000[D]   [E]$9999[F] / [G]99[H]"])
# ->
#    ["STR    5 ->   10    $100 /  1",
#     "INT   10 ->   15    $150 /  1",
#     "SPEED 15 -> 1000   $9999 / 99"]
#
# Если перед маркером нет пробела, текст перед ним выравнивается по правому краю.
# [ эскейпается как [[.
def multipad(lines):
	# двусвязный список-реестр маркеров
	# (...наверное, учитывая, что для has_after сейчас всё равно выполняется линейный обход, можно было бы сделать обычный массив с тем же успехом)
	first_marker = last_marker = None
	markers = dict() # отображение имени маркера в узел списка

	# в каждом маркере:
	# next, prev — следующий и предыдущий элементы списка
	# occurrences — список фрагментов, заканчивающихся этим маркером (т. е. у которых он в marker)
	# markers_after_this — только для того, чтобы отловить невыполнимый порядок маркеров, например, в multipad(["[B]zxc[A]vbn[C]", "[A]qwe[B]rty[C]"])
	# (в принципе, проверку невыполнимости можно вообще убрать, будет просто кривой результат)
	class Marker:
		__slots__ = ('next', 'prev', 'occurrences', 'markers_after_this')
		def __init__(self):
			self.next, self.prev, self.occurrences, self.markers_after_this = None, None, [], []

		def has_after(self, marker):
			m = self
			while m:
				m = m.next
				if m is marker: return True

		@property # имя только для ошибок, поэтому лучше не хранить, а искать медленно при необходимости
		def name(self): return next(name for name, marker in markers.items() if marker is self)

	# фрагмент строки
	# marker — маркер ПОСЛЕ него
	# marker_pos — отмеченное маркером место в исходной строке
	# fragment_index — индекс себя в списке фрагментов
	class Fragment:
		__slots__ = ('data', 'marker', 'marker_pos', 'line_index', 'fragment_index')
		def __init__(self, data, marker, marker_pos, line_index, fragment_index):
			self.data, self.marker, self.marker_pos, self.line_index, self.fragment_index = data, marker, marker_pos, line_index, fragment_index

	def make_marker_come_after(marker, after):
		after.markers_after_this.append(marker)
		if after in marker.markers_after_this:
			raise MultipadMarkupError(f"Циклическая зависимость между маркерами [{marker.name}] и [{after.name}].")
		if after.has_after(marker): return

		nonlocal first_marker, last_marker
		# удалить marker из списка
		if marker.prev:
			marker.prev.next = marker.next
		else:
			assert marker is first_marker and marker is not last_marker
			first_marker = marker.next
			first_marker.prev = None

		if marker.next:
			marker.next.prev = marker.prev
		else:
			assert marker is last_marker and marker is not first_marker
			last_marker = marker.prev
			last_marker.next = None

		# вставить marker в список после after
		marker.next = after.next
		marker.prev = after
		after.next  = marker
		if marker.next:
			marker.next.prev = marker
		else:
			assert after is last_marker
			last_marker = marker

	# soup[i] = список фрагментов (Fragment), соответствующих lines[i]
	soup = []
	for line_index, line in enumerate(lines):
		i, start, fragments, prev_marker = 0, 0, [], None
		while i < len(line):
			if line[i] == '[':
				if i + 1 < len(line) and line[i + 1] == '[':
					line = line[:i] + line[i + 1:]
					i += 1
				else:
					marker_end = line.find(']', i + 1)
					if marker_end < 0: raise RuntimeError("неэкранированный [: " + line)

					marker_name = line[i+1:marker_end]
					line = line[:i] + line[marker_end + 1:]

					marker = markers.get(marker_name, None)
					if not marker:
						marker = Marker()
						markers[marker_name] = marker
						marker.prev = last_marker
						if last_marker:
							last_marker.next = marker
						else:
							first_marker = marker
						last_marker = marker

					fragment = Fragment(line[start:i], marker, i, line_index, len(fragments))
					marker.occurrences.append(fragment)
					fragments.append(fragment)
					if prev_marker: make_marker_come_after(marker, prev_marker)
					prev_marker = marker
					start = i
			else:
				i += 1
		fragments.append(Fragment(line[start:], None, 0, 0, 0)) # см. (**fake_last_fragment)
		soup.append(fragments)

	# Теперь нужно пройтись по списку маркеров и все их выровнять.
	marker = first_marker
	while marker:
		target_pos = max(fragment.marker_pos for fragment in marker.occurrences)

		for fragment in marker.occurrences:
			pad_delta = target_pos - fragment.marker_pos
			if pad_delta == 0: continue

			# эвристика :\ так-то можно было бы управлять какими-нибудь спецсимволами в маркерах...
			if fragment.data and fragment.data[-1] in ' ':
				fragment.data = fragment.data + ' ' * pad_delta
			else:
				fragment.data = ' ' * pad_delta + fragment.data

			# -1 — после последних фрагментов строк, т. е. тех, которые Fragment(line[start:], None, 0, 0, 0) (**fake_last_fragment),
			# маркеров нет, а значит, и смещения корректировать не у чего
			for i in range(fragment.fragment_index, len(soup[fragment.line_index]) - 1):
				soup[fragment.line_index][i].marker_pos += pad_delta

		marker = marker.next

	return ["".join(frag.data for frag in fragments) for fragments in soup]
multipad.escape = (lambda escape_trans=str.maketrans({'[': '[['}): lambda line: line.translate(escape_trans))()

class MultipadTest(TestCase):
	def cases(self): return (
		(
			["STR [A]5[B] -> [C]10[D]   [E]$100[F] / [G]1[H]",
			 "INT [A]10[B] -> [C]15[D]   [E]$150[F] / [G]1[H]",
			 "SPEED [A]15[B] -> [C]1000[D]   [E]$9999[F] / [G]99[H]"],

			["STR    5 ->   10    $100 /  1",
			 "INT   10 ->   15    $150 /  1",
			 "SPEED 15 -> 1000   $9999 / 99"]
		),
		(["1[A]2[B]3", "4[B]5[A]6"], MultipadMarkupError))

	def one(self, input, expect):
		try:
			self.assertEqual(multipad(input), expect)
		except Exception as e:
			if not isinstance(e, expect): raise

def cls():
	os.system('cls' if os.name == 'nt' else 'clear')

# Эффект, наложенный на персонажа.
class Hex:
	ran_out = property(lambda self: self.turns <= 0)

	# reason для do_finish
	TIMEOUT, CANCELLED, TARGET_DIED = 'timeout', 'cancelled', 'target_died'

	def __init__(self, power, *, turns=None):
		self.applied = False
		self.master = self.victim = None
		self.power = check(power, power > 0, "power?!")
		if self.time_based:
			self.turns = self.turns_from_power(power) if turns is None else check(turns, turns > 0, "turns?!")
		else:
			self.turns = 1

	def apply(self, master, victim=None, arena=None):
		check(not self.applied, "already applied", master.alive, "мастер мёртв", not victim or victim.alive, "жертва мертва")
		self.master = check(master, isinstance(master, Fighter), "master?!")
		self.victim = check(victim or master, lambda victim: isinstance(victim, Fighter), "victim?!")
		with self.master.lock_caused_hexes() as caused_hexes: caused_hexes.add(self)
		with self.victim.lock_hexes() as hexes: hexes.add(self)
		self.do_start()
		self.applied = True

		# Хекс тикает в конце хода персонажа, на которого наложен. Багофича такого подхода в том, что если персонаж применил хекс сам на себя на своём ходу,
		# то хекс тикнет в конце этого же хода, т. е. практическая длительность окажется на единицу меньше.
		if self.time_based and self.master == self.victim and arena and arena.whose_turn() == self.master: self.turns += 1

	def unapply(self):
		check(self.applied, "not applied", self.ran_out, "not ran_out")
		with self.master.lock_caused_hexes() as caused_hexes: caused_hexes.remove(self)
		with self.victim.lock_hexes() as hexes: hexes.remove(self)

	def tick(self, arena):
		check(self.applied, "not applied", not self.ran_out, "хекс истёк")
		self.do_tick(arena)
		if self.ran_out: return

		if self.time_based:
			self.turns -= 1
			if self.ran_out: self.end(Hex.TIMEOUT)

	def cancel(self, reason=CANCELLED):
		check(self.applied, "not applied", not self.ran_out, "ran_out")
		self.turns = 0
		check(self.ran_out, "not ran_out after forced runout")
		self.end(reason)

	def do_start(self): pass
	def do_tick(self, arena): pass
	def do_finish(self, reason): pass

	def end(self, reason):
		self.unapply()
		self.do_finish(reason)

	def short_desc(self, cmd_prefix="", for_multipad=False, flip=False):
		# desc [cmd]cmd [turns]turns[/turns]
		# или
		# turns[/turns] cmd[/cmd] desc[/desc]
		desc = self.do_name()
		pow_desc = self.do_describe_power()
		if pow_desc: desc += ", " + pow_desc
		if for_multipad and flip: desc += "[/desc]"

		cmd = ("" if not for_multipad or flip else "[cmd]") + "(" + cmd_prefix + self.cmd() + ")" + ("[/cmd]" if for_multipad and flip else "")
		cmd = None
		turns = self.time_based and ("" if not for_multipad or flip else "[turns]") + str(self.turns) + "t" + ("[/turns]" if for_multipad else "")
		return left_to_right(desc, cmd, turns, flip=flip)

	@classmethod
	def generic_name(cls): return cls.do_generic_name()
	@classmethod
	def do_generic_name(cls): raise NotImplementedError("do_generic_name")

	def do_name(self): return self.generic_name()
	def do_describe_power(self): return None

	def detail(self): return self.do_detail()
	def do_detail(self): raise NotImplementedError("do_detail")

	def cmd(self): return self.do_cmd()
	def do_cmd(self): raise NotImplementedError("do_cmd")

	def turns_from_power(self, power): return self.do_turns_from_power(power)
	def do_turns_from_power(self, power): return 10

	npower = property(lambda self: self.power / self.BASELINE_POWER)
	BASELINE_POWER = 100
	dispellable = False
	time_based = True

	def __getstate__(self):
		check(self.applied, "not applied?!")
		return {k:v for k,v in self.__dict__.items() if k not in (
			'applied',         # резолвится здесь
			'victim'           # резолвится Fighter
			)}

	def __setstate__(self, state):
		self.__dict__.update(state)
		self.applied = True    # отбрасывается здесь

class RageHex(Hex):
	#  мин. 1.2x @ pow → 0
	#       1.5x @ BASELINE_POWER
	# макс. 5.0x @ pow = 1267
	physdam_x = property(lambda self: clamp(1.2 + 0.3 * self.npower, 1.2, 5.0))

	#  мин. 1.1x @ pow → 0
	#       1.2x @ BASELINE_POWER
	# макс. 2.2x @ pow = 1100
	backlash_x = property(lambda self: clamp(1.1 + 0.1 * self.npower, 1.1, 2.2))

	def do_start(self):
		self.victim.note(lambda sink: sink.youify("{Вы/F} приходит{е/} в ярость!", self.victim))

	def do_finish(self, reason):
		if reason in (Hex.TIMEOUT, Hex.CANCELLED): self.victim.note(lambda sink: sink.youify("{Вы/F} успокаивает{есь/ся}.", self.victim))

	@classmethod
	def do_generic_name(cls): return "Ярость"
	def do_describe_power(self):
		m = round(self.physdam_x, 1)
		return None if m == 1.5 else f"{m}x"

	def do_detail(self): return \
		"Увеличивает физическую атаку (x{0}) и любой получаемый урон (x{1}).".format(round(self.physdam_x, 1), round(self.backlash_x, 1))

	def do_cmd(self): return 'rage'
	def do_turns_from_power(self, power): return clamp(ceil(4*power**0.2), 3, 20)

class RageHexTest(TestCase):
	def __init__(self, *args, **kargs):
		super().__init__(*args, **kargs)
		self.dummy = RageHex.__new__(RageHex)

	def cases(self): return (-1000, 1.2, 1.1), (0, 1.2, 1.1), (Hex.BASELINE_POWER, 1.5, 1.2), (1100, 4.5, 2.2), (1267, 5, 2.2), (9999, 5, 2.2)
	def one(self, power, ref_physdam_x, ref_backlash_x):
		self.dummy.power = power
		self.assertEqual(round(self.dummy.physdam_x, 1), ref_physdam_x)
		self.assertEqual(round(self.dummy.backlash_x, 1), ref_backlash_x)

class DeathWordHex(Hex):
	def do_finish(self, reason):
		if reason == Hex.TIMEOUT:
			check(self.master.alive, "мастер мёртв", self.victim.alive, "жертва мертва")
			self.victim.die("в исполнение Смертного приговора")

	@classmethod
	def do_generic_name(cls): return "Смертный приговор"
	def do_detail(self): return \
		"Смерть через {turns}.\n"\
		"Вы можете снять этот хекс с помощью Развеивания либо убив мага, наложившего заклинание.".format(turns = plural(self.turns, "{N} ход{/а/ов}"))

	def do_cmd(self): return 'deathword'
	dispellable = True

class Bleeding(Hex):
	def __init__(self, power):
		super().__init__(power)
		self.precise_power = power
		self.precise_damage = 0

	@classmethod
	def do_generic_name(cls): return "Кровотечение"
	def do_name(self): return self.do_generic_name() + ("!!!" if self.npower > 3 else "!" if self.npower > 2 else "")
	def do_detail(self): return \
		"Отнимает HP (-{0}%/ход) и уменьшает ловкость (-{1}).".format(round(self.precise_hp_percentile_decay, 1), round(self.precise_dex_debuff))

	def do_tick(self, arena):
		self.precise_damage += self.precise_hp_percentile_decay/100 * self.victim.mhp
		dmg = floor(self.precise_damage)
		if dmg > 0:
			self.victim.ouch(dmg, arena, "от потери крови")
			self.precise_damage -= dmg
		self.precise_power = self.decay_power(self.precise_power)
		self.power = max(1, round(self.precise_power))

	def do_cmd(self): return 'bleeding'

	def decay_power(self, power): return power * self.POWER_DECAY
	def do_turns_from_power(self, power): return clamp(ceil(log(0.5 * self.BASELINE_POWER / power, self.POWER_DECAY)), 3, 20)

	precise_hp_percentile_decay = property(lambda self: clamp(2.5 * (self.npower**0.5 if self.npower > 1 else self.npower), 1, 5))
	precise_dex_debuff = property(lambda self: 3 * self.npower**0.5)
	POWER_DECAY = 0.9

# По инстансу на каждое запомненное заклинание у каждого бойца.
class Spell:
	LIST_ORDER = None
	@classmethod
	def name(cls, *, long=False): return cls.do_name(long)
	@classmethod
	def do_name(cls, long): raise NotImplementedError("do_name")

	@classmethod
	def cmd(cls): return cls.do_cmd()
	@classmethod
	def do_cmd(cls): raise NotImplementedError("do_cmd")

	def mp_cost(self): return self.do_mp_cost()
	def do_mp_cost(self): raise NotImplementedError("do_mp_cost")

class Upgrade:
	TARGET_CLASS = property(lambda self: Living)
	def __init__(self):
		self.applied = False
		self.target = None
		self.ap_taken, self.gold_taken = 0, 0

	def apply(self, target, ap=None, gold=None):
		check(not self.applied, "already applied")
		ap, gold = ap if ap is not None else self.ap_cost(target), gold if gold is not None else self.gold_cost(target)
		check(target.enough_ap_for(ap), "not enough AP")

		self.target = check(target, isinstance(target, self.TARGET_CLASS), "target?!")
		self.ap_taken, self.gold_taken = ap, gold
		self.do_apply(target)
		self.applied = True
		target.ap_used += ap
		target.upgrades.append(self)
		self.send_note(target, lambda sink, you: sink.you == you and self.apply_message(target))

	def revert(self, target):
		check(self.applied, "not applied", self.target == target, "target?!")
		target.upgrades.remove(self)
		target.ap_used -= self.ap_taken
		self.do_revert(target)
		self.send_note(target, lambda sink, you: sink.you == you and self.revert_message(target))
		self.applied = False

	def send_note(self, target, notef):
		you = self.do_note_target(target)
		you.note(lambda sink: notef(sink, you))

	def do_note_target(self, target): return target
	def do_apply(self, target): pass
	def do_revert(self, target): pass

	def apply_message(self, target): return self.do_apply_message(target)
	def revert_message(self, target): return self.do_revert_message(target)

	def do_apply_message(self, target): return f"Апгрейд приобретён за ${self.gold_taken}."
	def do_revert_message(self, target): return f"Апгрейд продан за ${self.refund()}."

	# Проверяет физическую возможность добавить апгрейд (но не цену в золоте).
	@classmethod
	def allow(cls, target, ignore_ap_cost=None):
		return cls.do_allow(target) and (ignore_ap_cost or target.enough_ap_for(cls))

	# По умолчанию апгрейд полагается уникальным.
	@classmethod
	def do_allow(cls, target): return not cls.find(target)

	# Находит апгрейд этого типа среди апгрейдов target, или возвращает None
	@classmethod
	def find(cls, target): return next(cls.find_all(target), None)

	@classmethod
	def last(cls, target): return next(cls.find_all(target, reverse=True), None)

	# Находит все апгрейды этого типа среди апгрейдов target (например, апгрейды статов можно взять несколько раз)
	@classmethod
	def find_all(cls, target, reverse=False): return (up for up in (reversed(target.upgrades) if reverse else target.upgrades) if isinstance(up, cls))

	@classmethod
	def count(cls, target): return sum(1 for up in cls.find_all(target))

	@classmethod
	def ap_cost(cls, target): return cls.do_ap_cost(target)

	@classmethod
	def do_ap_cost(cls, target): raise NotImplementedError("do_ap_cost")

	@classmethod
	def gold_cost(cls, target): return cls.do_gold_cost(target)

	@classmethod
	def do_gold_cost(cls, target): raise NotImplementedError("do_gold_cost")

	@classmethod
	def cmd(cls): return cls.do_cmd()
	@classmethod
	def do_cmd(cls): raise NotImplementedError("do_cmd")

	def refund(self):
		check(self.applied, "not applied")
		return max(int(0.5 * self.gold_taken), min(self.gold_taken, 1))

	def sell_accusative(self, target): return check(self.target == target, "target не совпадает") and self.do_sell_accusative(target)
	def do_sell_accusative(self, target): raise NotImplementedError("do_sell_accusative")

	@classmethod
	def cost_preface(cls, target): return cls.do_cost_preface(target)
	@classmethod
	def do_cost_preface(cls, target): raise NotImplementedError("do_cost_preface")

	@classmethod
	def shop_label(cls, target): return cls.do_shop_label(target)
	@classmethod
	def do_shop_label(cls, target): raise NotImplementedError("do_shop_label")

	def __getstate__(self):
		check(self.applied, "not applied?!")
		return {k:v for k,v in self.__dict__.items() if k not in (
			'applied', # резолвится здесь
			'target'   # резолвится Living
			)}

	def __setstate__(self, state):
		self.__dict__.update(state)
		self.applied = True # отбрасывается здесь

class FighterUpgrade(Upgrade):
	TARGET_CLASS = property(lambda self: Fighter)

class WeaponUpgrade(Upgrade):
	TARGET_CLASS = property(lambda self: Weapon)

class StatUpgrade(FighterUpgrade):
	STAT, AMOUNT, LIMIT = None, None, None
	statname, statgender = Noun.PLACEHOLDER, Gender.UNKNOWN

	def __init__(self):
		super().__init__()
		self.stat = check(self.STAT, self.STAT in {'str', 'int', 'dex', 'spd'}, "stat?!")
		self.amount = check(self.AMOUNT, 1 <= self.AMOUNT <= 100, "amount?!")

	def do_apply(self, target):
		self.set_base_stat(target, self.get_base_stat(target) + self.amount)

	def do_revert(self, target):
		self.set_base_stat(target, self.get_base_stat(target) - self.amount)

	@classmethod
	def do_allow(cls, target): return sum(up.AMOUNT for up in cls.find_all(target)) + cls.AMOUNT <= cls.LIMIT

	@classmethod
	def do_ap_cost(cls, target): return 1

	@classmethod
	def do_cmd(cls): return cls.STAT

	@classmethod
	def get_base_stat(cls, target): return getattr(target, 'base_' + cls.STAT)
	def set_base_stat(cls, target, value):
		with target.save_relative_vitals():
			setattr(target, 'base_' + cls.STAT, value)

	def do_sell_accusative(self, target): return "часть {0} {1} ({2} -> {3})".format(
		self.statgender.ize('свое{й/го}'), self.statname.genitive, self.get_base_stat(target), self.get_base_stat(target) - self.amount)

	@classmethod
	def do_cost_preface(cls, target):
		return "Тренировка {0} с {1} до {2} стоит".format(cls.statname.genitive, cls.get_base_stat(target), cls.get_base_stat(target) + cls.AMOUNT)

	@classmethod
	def do_shop_label(cls, target):
		return cls.STAT.upper() + " [cur]" + str(cls.get_base_stat(target)) + "[/cur]" + \
			(" -> [upd]" + str(cls.get_base_stat(target) + cls.AMOUNT) + "[/upd]" if cls.allow(target, ignore_ap_cost=True) else "") + " "

class StrUpgrade(StatUpgrade):
	STAT, AMOUNT, LIMIT = 'str', 5, 20
	statname, statgender = Noun.parse("{сила:f}", return_gender=True)

	@classmethod
	def do_gold_cost(cls, target): return 120 + 30 * cls.count(target)

	def do_apply_message(self, target): return "Ваши мускулы наливаются силой."
	def do_revert_message(self, target): return "Ваши мускулы слабеют."

class IntUpgrade(StatUpgrade):
	STAT, AMOUNT, LIMIT = 'int', 5, 20
	statname, statgender = Noun.parse("{интеллект}", return_gender=True)

	@classmethod
	def do_gold_cost(cls, target): return 135 + 35 * cls.count(target)

	def do_apply_message(self, target): return "Ваш ум заостряется."
	def do_revert_message(self, target): return "Вы начинаете хуже соображать."

class DexUpgrade(StatUpgrade):
	STAT, AMOUNT, LIMIT = 'dex', 5, 20
	statname, statgender = Noun.parse("{ловкость:f}", return_gender=True)

	@classmethod
	def do_gold_cost(cls, target): return 90 + 25 * cls.count(target)

	def do_apply_message(self, target): return "Ваши рефлексы улучшаются."
	def do_revert_message(self, target): return "Вы чувствуете себя {0}.".format(target.gender.ize("неповоротлив{ым/ой}"))

class SpeedUpgrade(StatUpgrade):
	STAT, AMOUNT, LIMIT = 'spd', 30, 150
	statname, statgender = Noun.parse("{скорость:f}", return_gender=True)

	@classmethod
	def do_gold_cost(cls, target): return 150 + 50 * sum(1 for up in cls.find_all(target))

	def do_apply_message(self, target): return "Ваша кровь бурлит!"
	def do_revert_message(self, target): return "Ваша кровь остывает..."

class Firestorm(Spell):
	LIST_ORDER = 0
	@classmethod
	def do_name(cls, long): return "Огненный шторм" if long else "Огн. шторм"

	@classmethod
	def do_cmd(cls): return 'fstorm'

	def do_mp_cost(self): return 6

class Dispell(Spell):
	LIST_ORDER = 1
	@classmethod
	def do_name(cls, long): return "Развеять"

	@classmethod
	def do_cmd(cls): return 'dispell'

	def do_mp_cost(self): return 2

class Frailness(Spell):
	LIST_ORDER = 2
	@classmethod
	def do_name(cls, long): return "Хрупкость"

	@classmethod
	def do_cmd(cls): return 'frailness'

	def do_mp_cost(self): return 3

class SpellUpgrade(FighterUpgrade):
	SPELL_CLASS = Spell
	def __init__(self):
		super().__init__()
		self.spell = None
		self.applied = None

	def do_apply(self, target):
		assert not self.spell
		spell_class = check(self.SPELL_CLASS, issubclass(self.SPELL_CLASS, Spell) and self.SPELL_CLASS is not Spell, "SPELL_CLASS?!")
		self.spell = spell_class()
		target.learn_spell(self.spell)

	def do_revert(self, target):
		target.forget_spell(self.spell)
		self.spell = None

	@classmethod
	def do_cmd(cls): return 'sp.' + cls.SPELL_CLASS.cmd()

	@classmethod
	def do_shop_label(cls, target): return "Заклинание: " + cls.SPELL_CLASS.name()

class FirestormSpellUpgrade(SpellUpgrade):
	SPELL_CLASS = Firestorm

	@classmethod
	def do_gold_cost(cls, target): return 150

	@classmethod
	def do_ap_cost(cls, target): return 2

	def do_sell_accusative(self, target): return "вашу магию Огненного шторма"

	@classmethod
	def do_cost_preface(cls, target): return "Вы научитесь применять Огненный шторм за"

	def do_apply_message(self, target): return "Теперь вы умеете обрушать на врагов мощный шторм!"
	def do_revert_message(self, target): return "Вы больше не можете управлять огненным вихрем."

class DispellSpellUpgrade(SpellUpgrade):
	SPELL_CLASS = Dispell

	@classmethod
	def do_gold_cost(cls, target): return 100

	@classmethod
	def do_ap_cost(cls, target): return 2

	def do_sell_accusative(self, target): return "вашу магию Развеивания"

	@classmethod
	def do_cost_preface(cls, target): return "Вы научитесь развеивать заклинания за"

	def do_apply_message(self, target): return "Вы обучаетесь Развеиванию!"
	def do_revert_message(self, target): return "Вы больше не можете развеивать заклинания."

class FrailnessSpellUpgrade(SpellUpgrade):
	SPELL_CLASS = Frailness

	@classmethod
	def do_gold_cost(cls, target): return 200

	@classmethod
	def do_ap_cost(cls, target): return 3

	def do_sell_accusative(self, target): return "вашу магию Хрупкости"

	@classmethod
	def do_cost_preface(cls, target): return "Вы научитесь накладывать хрупкость на врагов за"

	def do_apply_message(self, target): return "Вы обучаетесь заклинанию Хрупкости!"
	def do_revert_message(self, target): return "Вы больше не можете ослаблять врагов."

class Ammunition:
	LIST_ORDER = None
	MAX_CHARGES = None
	INFINITE_CHARGES = None
	finite_charges = property(lambda self: self.MAX_CHARGES)

	# При повторных установках они попадают в self.secondary_installations, в weapon.ammos светится только «главная».
	# При удалении «главной» на её место встаёт одна из вторичных.
	# Например, зажигательные патроны используют это для расчёта мощности.
	def __init__(self):
		self.charges = check(self.MAX_CHARGES, not self.MAX_CHARGES or 1 <= self.MAX_CHARGES <= 99, "MAX_CHARGES?!")
		self.weapon = None
		self.secondary_installations = []
		self.upgrade = None

	def recharge_cost(self): return self.do_recharge_cost()
	def do_recharge_cost(self): raise NotImplementedError("do_recharge_cost")

	def has_charges(self): return not self.MAX_CHARGES or self.charges
	def draw_charge(self):
		check(self.has_charges(), "нет зарядов")
		self.charges -= 1
		check(self.charges >= 0, "charges < 0")

	def needs_recharging(self):
		return self.MAX_CHARGES and self.charges < self.MAX_CHARGES

	def recharge(self):
		self.charges = check(self.MAX_CHARGES, "бесконечные заряды")

	@classmethod
	def find(cls, target): return next((ammo for ammo in target.ammos if isinstance(ammo, cls)), None)

	def install(self, target, upgrade):
		check(not self.weapon, "already installed")
		self.weapon = check(target, isinstance(target, Weapon), "target?!")
		self.upgrade = check(upgrade, not upgrade or isinstance(upgrade, WeaponUpgrade), "upgrade?!")
		prev = self.find(target)
		if prev:
			prev.secondary_installations.append(self)
		else:
			insort_right(self.weapon.ammos, self, key=lambda ammo: ammo.LIST_ORDER)

	def uninstall(self, target, upgrade):
		check(self.weapon, "not installed", self.weapon == target, "target?!", self.upgrade == upgrade, "upgrade?!")
		main = check(self.find(target), "not in target.ammos?!")

		if main != self:
			# удаляется вторичная установка — просто убрать из списка вторичных
			main.secondary_installations.remove(self)
		elif self.secondary_installations:
			# удаляется главная установка, имеющая вторичные — поставить одну из них главной
			main_index = next(i for i, ammo in enumerate(target.ammos) if ammo == self)
			target.ammos[main_index] = self.secondary_installations.pop()
			target.ammos[main_index].secondary_installations = self.secondary_installations
			self.secondary_installations = []
		else:
			# убрать по-нормальному
			self.weapon.ammos.remove(self)
		self.weapon = self.upgrade = None

	def times(self): return 1 + len(self.secondary_installations)

	@classmethod
	def human_times(cls, times): return cls.do_human_times(times)
	@classmethod
	def do_human_times(cls, times): return f"+{times}"

	@classmethod
	def name(cls, target): return cls.do_name(target)
	@classmethod
	def do_name(cls, target): raise NotImplementedError("do_name")

	@classmethod
	def name_up(cls, target, up): return cls.do_name_up(target, up)
	@classmethod
	def do_name_up(cls, target, up): pass

	def short_name(self): return self.do_short_name()
	def do_short_name(self): raise NotImplementedError("do_short_name")

	@classmethod
	def cmd(cls): return cls.do_cmd()
	@classmethod
	def do_cmd(cls): raise NotImplementedError("do_cmd")

	def __getstate__(self):
		return {k:v for k, v in self.__dict__.items() if k not in (
			'weapon', # резолвится Weapon
			)}

class IncendiaryAmmunition(Ammunition):
	LIST_ORDER = 0
	MAX_CHARGES = Ammunition.INFINITE_CHARGES

	@classmethod
	def do_human_times(cls, times): return f"+{3 * times}"

	@classmethod
	def do_name(cls, target): return "зажиг. патроны" + (cls.name_up(target, 0) or "")

	@classmethod
	def do_name_up(cls, target, up):
		ammo = cls.find(target)
		times = (ammo.times() if ammo else 0) + up
		return times and cls.human_times(times)

	def do_short_name(self): return f"заж.{self.human_times(self.times)}"

	@classmethod
	def do_cmd(cls): return 'incendiary'

class SilenceAmmunition(Ammunition):
	LIST_ORDER = 1
	MAX_CHARGES = 3

	def do_recharge_cost(self): return 50
	@classmethod
	def do_name(cls, target): return "тишина"
	def do_short_name(self): return "тиш."

	@classmethod
	def do_cmd(cls): return 'silence'

class TimestopAmmunition(Ammunition):
	LIST_ORDER = 2
	MAX_CHARGES = 2

	def do_recharge_cost(self): return 100
	@classmethod
	def do_name(cls, target): return "ост. времени"
	def do_short_name(self): return "врем."

	@classmethod
	def do_cmd(cls): return 'timestop'

class AmmunitionUpgrade(WeaponUpgrade):
	AMMUNITION_CLASS = Ammunition
	def __init__(self):
		super().__init__()
		self.ammo = None

	def do_apply(self, target):
		check(not self.ammo, "ammo")
		ammo_class = check(self.AMMUNITION_CLASS, lambda ammo_class: issubclass(ammo_class, Ammunition) and ammo_class is not Ammunition, "AMMUNITION_CLASS?!")
		self.ammo = ammo_class()
		self.ammo.install(target, self)

	def do_revert(self, target):
		check(self.ammo, "ammo")
		self.ammo.uninstall(target, self)

	def do_note_target(self, target): return target.owner

	@classmethod
	def do_cmd(cls): return 'b.' + cls.AMMUNITION_CLASS.cmd()

	@classmethod
	def genitive_ammunition_module_name(cls): raise NotImplementedError("genitive_ammunition_module_name")

	def do_sell_accusative(self, target):
		msg = ("снятие усовершенствования модуля " if self.count(target) > 1 else "ваш модуль ") + self.genitive_ammunition_module_name()
		cur = self.ammo.name_up(target, 0)
		targ = self.ammo.name_up(target, -1)
		if cur and targ: msg += " (" + cur + " -> " + targ + ")"
		elif cur: msg += cur
		return msg

	@classmethod
	def do_cost_preface(cls, target):
		ammo = cls.AMMUNITION_CLASS.find(target)
		cur  = ammo and ammo.name_up(target, 0)
		targ = ammo and ammo.name_up(target, +1)
		return ("Усовершенствование" if ammo else "Установка") + " модуля " + cls.genitive_ammunition_module_name() + \
			((" с " + cur if cur else "") + " до " + targ if targ else "") + " обойдётся в"

	@classmethod
	def do_shop_label(cls, target):
		name = multipad.escape(target.name) + ": " + cls.AMMUNITION_CLASS.name(target)
		if cls.allow(target, ignore_ap_cost=True):
			targ = cls.AMMUNITION_CLASS.name_up(target, up=+1)
			if targ: name += (" -> " if cls.AMMUNITION_CLASS.name_up(target, up=0) else "") + targ
		return name

class IncendiaryAmmunitionUpgrade(AmmunitionUpgrade):
	AMMUNITION_CLASS = IncendiaryAmmunition

	@classmethod
	def do_allow(cls, target): return cls.count(target) + 1 <= 3

	@classmethod
	def do_ap_cost(cls, target): return 1

	@classmethod
	def do_gold_cost(cls, target): return 100 + 30 * cls.count(target)

	@classmethod
	def genitive_ammunition_module_name(cls): return "зажигательных патронов"

class SilenceAmmunitionUpgrade(AmmunitionUpgrade):
	AMMUNITION_CLASS = SilenceAmmunition

	@classmethod
	def do_ap_cost(cls, target): return 2

	@classmethod
	def do_gold_cost(cls, target): return 200

	@classmethod
	def genitive_ammunition_module_name(cls): return "патронов тишины"

class TimestopAmmunitionUpgrade(AmmunitionUpgrade):
	AMMUNITION_CLASS = TimestopAmmunition
	@classmethod
	def do_ap_cost(cls, target): return 3

	@classmethod
	def do_gold_cost(cls, target): return 350

	@classmethod
	def genitive_ammunition_module_name(cls): return "патронов остановки времени"

class FighterAttribute:
	def __init__(self):
		self.fighter = None

	def set_fighter(self, fighter):
		check(not self.fighter, "двойной set_fighter")
		self.fighter = fighter

	def reset_fighter(self, fighter):
		check(self.fighter == fighter, lambda: "fighter не соответствует прежнему" if self.fighter else "fighter не задан")
		self.fighter = None

	def __getstate__(self):
		return {k: v for k, v in self.__dict__.items() if k not in (
			'fighter', # резолвится Fighter
			)}

class Special(FighterAttribute):
	LIST_ORDER = None
	def __init__(self):
		super().__init__()

	def name(self): return self.do_name()
	def do_name(self): raise NotImplementedError("do_name")

	def do_ouch(self, arena): pass
	def do_tick(self, arena): pass

class RageOnLowHP(Special):
	LIST_ORDER = 1
	def __init__(self, *, red_zone=0.5):
		super().__init__()
		self.proceed = False
		self.red_zone = red_zone

	def do_name(self): return "Ярость"

	def do_ouch(self, arena):
		if not self.proceed and self.fighter.hp <= ceil(self.fighter.mhp * self.red_zone):
			RageHex(32 * (max(10, self.fighter.str) * self.fighter.xl)**0.5).apply(self.fighter, arena=arena)
			self.proceed = True

# Универсальная атака «чего угодно чем угодно». Реализует общее для атак поведение, такое как взаимодействие с бронёй и хексами.
# Можно не проводить атаку, а просто оценить интересующие показатели (урон, шанс попадания).
class Beam:
	# AC — показатель брони. В общем случае обеспечивает как относительное (постоянный процент), так и абсолютное (случайное от 0 до max) снижение урона.
	# pierce регулирует абсолютную составляющую: атака с pierce=0.5 проигнорирует 50% абсолютного снижения, pierce=1.0 оставит только относительное.
	@staticmethod
	def ac_reduction(ac, pierce=0):
		relative = 1 - (1 + ac/8)**-0.5
		check(relative, 0 <= relative <= 1, "relative")
		absolute_avg = ac/6 * max(0, 1-check(pierce, 0 <= pierce <= 1, "pierce"))
		absolute_max = ac/3 * max(0, 1-pierce)
		return relative, absolute_avg, absolute_max

	@staticmethod
	def apply_ac(damage, ac, pierce=0):
		relative_reduction, absolute_reduction_avg, absolute_reduction_max = Beam.ac_reduction(ac, pierce)
		return max(0, damage * (1 - relative_reduction) - (bell(0, absolute_reduction_avg, absolute_reduction_max) if absolute_reduction_max else 0))

	# TODO: придумать + проверить формулу
	@staticmethod
	def ac_reduced_avg_and_max(min, avg, max, ac, pierce):
		raise NotImplementedError("ac_reduced_avg_and_max")

	class Ongoing:
		def __init__(self):
			self.hp = 0
			self.denorm_ac, self.denorm_pierce = 0, 0

		def add_hp_damage(self, hp_dam, ac=0, pierce=0):
			self.hp += hp_dam
			self.denorm_ac += hp_dam * ac
			self.denorm_pierce += hp_dam * pierce

		def normalized_ac(self): return self.denorm_ac / (self.hp or 1)
		def normalized_pierce(self): return self.denorm_pierce / (self.hp or 1)

	class Element:
		def do_apply(self, target, ongoing): raise NotImplementedError("do_apply")

	class Plain(Element):
		def __init__(self, amount):
			self.amount_dis = Distribution.guess(amount)

	class Physical(Plain):
		def __init__(self, amount, pierce=0):
			super().__init__(amount)
			self.pierce = pierce

		def do_apply(self, target, ongoing):
			ongoing.add_hp_damage(self.amount_dis.roll(), target.ac, self.pierce)

	class Fire(Plain):
		def do_apply(self, target, ongoing):
			ongoing.add_hp_damage(self.amount_dis.roll(), target.ac * 0.8)

	def __init__(self, master, target, arena):
		self.master, self.target, self.arena = master, target, arena

	def launch(self):
		to_hit = self.on_tohit()
		if to_hit is not None:
			ev, cumulative = check(self.on_ev(), "on_ev"), self.on_cumulative()
			dodged, chance, roll = self.arena.dodge(to_hit, ev, cumulative=cumulative)
			if dodged:
				self.on_dodged(chance, roll)
				return

		elements = self.get_elements()
		ongoing = self.Ongoing()
		for elem in elements:
			elem.do_apply(self.target, ongoing)

		precise_hp = Beam.apply_ac(ongoing.hp, ongoing.normalized_ac(), ongoing.normalized_pierce())
		for hex in self.master.hexes:
			if isinstance(hex, RageHex): precise_hp *= hex.physdam_x
		for hex in self.target.hexes:
			if isinstance(hex, RageHex): precise_hp *= hex.backlash_x

		rounded_hp = rand_round(precise_hp)
		self.target.ouch(rounded_hp, self.arena, self.on_death_cause, self.on_death_note, hook=lambda fatal: self.on_hp_damage(rounded_hp, fatal))

	def on_tohit(self): return None
	def on_ev(self): return self.target.ev
	def on_cumulative(self): return None
	def on_dodged(self, chance, roll): pass
	def on_elements(self): return 1.0
	def on_hp_damage(self, hp, fatal): pass
	def on_death_cause(self): return "от полученных ран"
	def on_death_note(self, sink): return self.target.default_death_note(sink)

	def get_elements(self):
		elements = self.on_elements()
		try:
			elements = (self.Physical(elements),)
		except Distribution.CantGuess:
			elements = check((elements,) if isinstance(elements, self.Element) else list(filter(None, elements or ())),
				lambda elements: all(isinstance(elem, self.Element) for elem in elements), f"{elements}: ожидается список Element")
		return elements

class UnarmedAttack(FighterAttribute):
	class Beam(Beam):
		def __init__(self, ua, target, arena):
			super().__init__(ua.fighter, target, arena)
			self.ua = check(ua, isinstance(ua, UnarmedAttack), "ua")

		def on_tohit(self): return 10 + self.master.dex

	def attack(self, target, arena):
		self.beam(target, arena).launch()

	def beam(self, target, arena):
		return self.Beam(self, target, arena)

class BareHands(UnarmedAttack):
	class Beam(UnarmedAttack.Beam):
		def on_dodged(self, chance, roll):
			def get_note(sink):
				how = "едва " if roll - 0.05 < chance else "легко " if roll - 0.2 > chance else ""
				return sink.youify("{Вы/F} " + how + "уклоняет{есь/ся}", self.target) + " от " + sink.youify("{вашего /}удара{/ F:G}", self.master) + "."
			self.arena.note(get_note)

		def on_elements(self): return self.Physical(tuple(x * self.master.str for x in (0, 0.12, 0.2)))
		def on_hp_damage(self, hp, fatal):
			def get_note(sink):
				msg = sink.youify("{Вы/F}", self.master)
				if hp:
					msg += sink.youify(" наносит{е/} удар", self.master)
					msg += sink.youify(" сам{и//а/о} по себе" if self.master == self.target else " по {вам/F:D}" if not fatal else "", self.target)
				else:
					msg += sink.youify(" касает{есь/ся} ", self.master)
					msg += sink.youify("сам{и//а/о} себя" if self.master == self.target else "{вас/F:G}", self.target)
				msg += self.note_bare_hands(sink) + f" ({hp})"
				if fatal: msg += sink.youify(" и умирает{е/}" if self.master == self.target else ", и {вы/F} умирает{е/}", self.target)
				return msg + "."
			self.arena.note(get_note)

		def note_bare_hands(self, sink):
			bh_noticed = sink.extra_prop('bh_noticed', lambda: {})
			if self.ua not in bh_noticed:
				bh_noticed[self.ua] = True
				return " голыми руками"
			else:
				return ""

		def on_death_note(self, sink): pass

class Teeth(UnarmedAttack):
	class Beam(UnarmedAttack.Beam):
		def on_dodged(self, chance, roll):
			def get_note(sink):
				how = "едва " if roll - 0.05 < chance else "легко " if roll - 0.2 > chance else ""
				return sink.youify("{Вы/F} " + how + "уклоняет{есь/ся}", self.target) + " от " + sink.youify("{вас/F:G}", self.master) + "."
			self.arena.note(get_note)

		def on_elements(self): return self.Physical(tuple(x * self.master.str for x in (0, 0.12, 0.2)))

		def on_hp_damage(self, hp, fatal):
			def get_note(sink):
				msg = sink.youify("{Вы/F}", self.master)
				if hp:
					msg += sink.youify(" " + ("перекусывает{е/} " if fatal else "кусает{е/} "), self.master)
					if fatal:
						msg += sink.youify("сам{и//а/о} себе" if self.master == self.target else "{вам/F:D}", self.target) + " сонную артерию"
					else:
						msg += sink.youify("сам{и//а/о} себя" if self.master == self.target else "{вас/F:A}", self.target)
				else:
					msg += sink.youify(" скользит{е/} зубами ", self.master)
					msg += sink.youify("сам{и//а/о} по себе" if self.master == self.target else "по {вам/F:G}", self.target)
				msg += f" ({hp})"
				if fatal: msg += sink.youify(" и умирает{е/}" if self.master == self.target else ", и {вы/F} умирает{е/}", self.target)
				return msg + "."
			self.arena.note(get_note)

		def on_death_note(self, sink): pass

# Механизм подписки на сообщения о боевых и не очень событиях.
# Сообщение может быть сообщено разным sink по-разному: одной — «вы ударили Грязекраба», другой то же самое — «Рика ударила Грязекраба»
# (с этим разбирается автор сообщения и передаёт в note либо строку, либо функцию от sink, возвращающую строку).
# Через on_note разные режимы по-разному реагируют на эти сообщения: на арене (ArenaView) они добавляются в лог, в магазине — отображаются как more().
# Я на самом деле не уверен, что обычно понимают под термином sink :)
class MessageSink:
	def __init__(self, you, on_note, *, FICTIVE=False):
		if not FICTIVE:
			self.you = you
			self.on_note = on_note
			self.extra_props = {}

	def receive_note(self, msg):
		msg = check(msg(self) if callable(msg) else msg, lambda msg: not msg or isinstance(msg, str), "должна быть строка")
		if msg: self.on_note(cap_first(msg))

	# {вы/не вы}, {вы/F:падеж}, {вы/не вы мужского рода/не вы женского рода...}
	# Ориентировано на сообщения, которые должны быть сообщены тому, о ком идёт речь (sink.you), как о «вас», а остальным — как о «гражданине N».
	# Например,
	# sink.youify("{Вас/F:G} нет в списке.", fighter)
	# вернёт "Вас нет в списке", когда fighter == sink.you, и f"{fighter.name.genitive} нет в списке" — в противном случае.
	def youify(self, src, fighter):
		def handle(piece, spec):
			if piece is None: return ""
			pieces = piece.split('/')
			if len(pieces) < 2: raise ValueError(f"Строка содержит менее двух фрагментов (a/b): {piece}.")
			if fighter == self.you: p = pieces[0]
			else: p = pieces[min(len(pieces) - 1, 1 + min(fighter.gender if fighter.gender != Gender.UNKNOWN else Gender.MALE, len(pieces) - 2))]
			i = 0
			while i < len(p):
				if p[i] == 'F':
					name = fighter.name(Case.from_letter(spec))
					p = p[:i] + name + p[i+1:]
					i += len(name)
				else:
					i += 1
			return p
		return "".join(literal + handle(bracketed, spec) for literal, bracketed, spec, _ in string.Formatter.parse(None, src))

	def extra_prop(self, name, default_ctr):
		value = self.extra_props.get(name, None)
		if value is None:
			value = default_ctr()
			self.extra_props[name] = value
		return value

# arena.note("сообщение")
# -или-
# who = ...
# arena.note(lambda sink: "Вы обосрались." if who == sink.you else who.name + " обосрался.")
class MessageBroadcaster:
	def __init__(self):
		self.sinks = []

	def add_sink(self, sink):
		check(sink not in self.sinks, lambda: f"add_sink({sink}) вызвана дважды")
		self.sinks.append(sink)
		check(len(self.sinks) == 1, "Нет, в принципе это возможно (иначе зачем было вообще городить sinks[]), но сейчас, когда игрок ровно один — означает баг.")

	def remove_sink(self, sink):
		self.sinks.remove(sink)

	def note(self, msg):
		for sink in self.sinks:
			sink.receive_note(msg)

class Living:
	ap_limit = property(lambda self: 1 + 2*(self.xl - 1))

	def __init__(self):
		self.xp = 0
		self.xl = 1
		self.ap_used = 0
		self.name = Noun.PLACEHOLDER
		self.gender = Gender.UNKNOWN
		self.upgrades = []

	def receive_xp(self, amount):
		self.xp += check(amount, amount >= 0, "amount")
		def will_levelup(): return self.xp >= self.xp_for_levelup() and self.xl < self.LEVEL_CAP
		if will_levelup():
			with self.save_relative_vitals():
				while True:
					self.xp -= self.xp_for_levelup()
					self.level_up()
					if not will_levelup(): break
		if self.xl == self.LEVEL_CAP: self.xp = 0

	def drain_xp(self, amount):
		self.xp -= check(amount, amount >= 0, "amount")
		def will_lose_level(): return self.xp < 0 and self.xl > 1
		if will_lose_level():
			with self.save_relative_vitals():
				while True:
					self.xp += self.xp_for_levelup(self.xl - 1)
					self.level_down()
					if not will_lose_level(): break
		self.xp = max(self.xp, 0)

	def level_up(self):
		self.xl += 1
		assert 1 <= self.xl <= self.LEVEL_CAP

	def level_down(self):
		self.xl -= 1
		assert 1 <= self.xl <= self.LEVEL_CAP
		while self.ap_used > self.ap_limit and self.upgrades: self.upgrades[-1].revert(self)

	LEVEL_CAP = 1
	def xp_for_levelup(self, xl=None):
		if xl is None: xl = self.xl
		return 10 * xl

	def enough_ap_for(self, upgrade_or_whatever):
		ap_cost = (
			upgrade_or_whatever if isinstance(upgrade_or_whatever, int) else
			upgrade_or_whatever.ap_cost(self))

		return self.ap_used + ap_cost <= self.ap_limit

	def next_percentage(self):
		return floor(self.xp / self.xp_for_levelup() * 100) if self.xl < self.LEVEL_CAP else None

	# под for_multipad подразумевается for_shop
	def living_desc(self, for_multipad=False):
		name = self.name.cap_first()
		show_ap = for_multipad or self.xp > 0 or self.xl > 1 or self.ap_used > 0
		return ("{name}: {xlmp}{xl}" + (", {ap_mp}умения: {0.ap_used}/{0.ap_limit}" if show_ap else "")).format(
			self, xl = self.xl_desc(self.xl, self.next_percentage(), short=for_multipad, show_nx=not for_multipad),
			name = multipad.escape(name) if for_multipad else name,
			xlmp = "[lv]" if for_multipad else "",
			ap_mp = "[ap]" if for_multipad else "")

	@staticmethod
	def xl_desc(xl, next_percentage, short=None, show_nx=True):
		lv_word = "lv." if short else "уровень "
		nx_word = "" if short else "след. "
		return f"{lv_word}{xl}" + (f" ({nx_word}{next_percentage}%)" if show_nx and next_percentage is not None else "")

	class RelativeVitals(AbstractContextManager):
		def __init__(self, char): self.char = char
		def __exit__(self, *poxui): pass

	def save_relative_vitals(self): return self.RelativeVitals(self)

	def __getstate__(self):
		return {k:
			v.value if k == 'gender' else
			('g' + str(v) if v == Noun.guess(v, gender=self.gender, animate=isinstance(self, Fighter)) else 'p' + v.src()) if k == 'name' else
			v
			for k, v in self.__dict__.items()}

	def __setstate__(self, state):
		def unpack_name(n):
			return (
				Noun.parse(n[1:]) if n.startswith('p') else
				Noun.guess(n[1:], gender=Gender(state['gender']), animate=isinstance(self, Fighter)) if n.startswith('g') else
				throw(pickle.UnpicklingError, "name"))

		self.__init__()
		self.__dict__.update((k,
			Gender(v) if k == 'gender' else
			unpack_name(v) if k == 'name' else
			v)
			for k, v in state.items())
		for up in self.upgrades: up.target = self # отбрасывается Upgrade

class Fighter(Living, MessageBroadcaster):
	hp    = property(lambda self: self.cur_hp)
	mhp   = property(lambda self: max(1, round((self.base_mhp + 5 * (self.xl - 1)**0.77) * (1 + (self.base_str - 10) / 10)**0.77)))
	dead  = property(lambda self: not not self.death_cause)
	alive = property(lambda self: not self.dead)
	mp    = property(lambda self: self.cur_mp)
	mmp   = property(lambda self: round(self.base_mmp * (1 + (self.base_int - 10) / 10)))
	str   = property(lambda self: self.base_str)
	int   = property(lambda self: self.base_int)
	dex   = property(lambda self: self.base_dex)
	spd   = property(lambda self: self.base_spd)
	ac    = property(lambda self: self.base_ac)
	ev    = property(lambda self: max(0, self.base_ev + (self.dex - 10)//2))
	LEVEL_CAP = 7

	def __init__(self):
		Living.__init__(self)
		MessageBroadcaster.__init__(self)
		self.base_mhp = 10
		self.base_mmp = 10
		self.base_str = 10
		self.base_int = 10
		self.base_dex = 10
		self.base_spd = 100
		self.base_ac = 0
		self.base_ev = 10
		self.death_cause = None

		self.hexes = []
		self.caused_hexes = set()
		self.hexes_lock = None
		self.unarmed = None
		self.weapon = None
		self.spells = []
		self.specials = []

		self.cur_hp = self.mhp
		self.cur_mp = self.mmp

	def ouch(self, hp_dam, arena, death_cause, death_note=None, hook=lambda fatal: None):
		check(hp_dam >= 0, "hp_dam?!", death_cause, "death_cause?!")

		if not self.dead:
			self.cur_hp -= hp_dam
			if self.cur_hp <= 0:
				self.die(death_cause, death_note, hook=lambda: hook(True))
			else:
				hook(False)
				for sp in self.specials:
					sp.do_ouch(arena)

	def die(self, cause, death_note=None, hook=lambda: None):
		check(not self.dead, "not dead", cause, "cause?!")
		with self.lock_hexes() as hexes:
			for hex in hexes:
				hex.cancel(Hex.TARGET_DIED)

		self.death_cause = check(cause() if callable(cause) else cause, lambda death_cause: isinstance(death_cause, str) and death_cause, "death_cause")
		self.note(death_note or self.default_death_note)
		if hook: hook()

		with self.lock_caused_hexes() as caused_hexes:
			for hex in caused_hexes:
				if isinstance(hex, DeathWordHex):
					def death_word_cancellation_note(sink):
						return sink.youify("{Вы/F} больше не чувствует{е/} дыхание смерти.", hex.victim)
					hex.victim.note(death_word_cancellation_note)
					hex.cancel()

	def default_death_note(self, sink):
		return sink.youify("{вы/F} умирает{е/} ", self) + self.death_cause + "."

	def end_turn(self, arena):
		with self.lock_hexes() as hexes:
			for hex in hexes:
				check(hex.victim == self, "hex.victim != self", not hex.ran_out, "ran_out")
				hex.tick(arena)

		if self.alive:
			for sp in self.specials:
				sp.do_tick(arena)

	def set_weapon(self, weapon):
		if self.weapon: self.weapon.owner = None
		self.weapon = weapon
		if self.weapon: self.weapon.owner = self

	def learn_spell(self, spell):
		check(spell not in self.spells, "already in spells",
			all(not isinstance(spell, type(sp)) and not isinstance(sp, type(spell)) for sp in self.spells), "duplicate spell")
		insort_right(self.spells, spell, key=lambda spell: spell.LIST_ORDER)

	def forget_spell(self, spell):
		self.spells.remove(spell)

	# Если по Fighter.hexes или Fighter.caused_hexes нужно пройтись операцией, которая потенциально меняет этот же список, то вместо
	# > for hex in fighter.hexes: ...
	# следует делать
	# > with fighter.lock_hexes() as hexes:
	# >     for hex in hexes: ...
	# Запросы на добавление и удаление будут отложены до выхода из (самого первого) with, кроме того, удалённые элементы не засветятся в последующих итерациях.
	class HexesLock:
		Query = namedtuple('query', 'cntr, op, item')
		def __init__(self, fighter):
			self.fighter, self.queries, self.enters = fighter, [], 0

		def enter(self):
			assert self.fighter.hexes_lock == (self if self.enters > 0 else None), f"hexes_lock = {self.fighter.hexes_lock}, enters = {self.enters}"
			self.enters, self.fighter.hexes_lock = self.enters + 1, self

		def leave(self):
			assert self.fighter.hexes_lock is self
			self.enters = check(self.enters - 1, lambda e: e >= 0, "enters")
			if self.enters == 0:
				for q in self.queries:
					(q.cntr.remove if q.op == 'rem' else (getattr(q.cntr, 'append', None) or q.cntr.add) if q.op == 'add' else impossible(q.op, "op"))(q.item)
				self.fighter.hexes_lock = None

		class Context:
			def __init__(self, fighter, cntr): self.fighter, self.cntr, self.lock = fighter, cntr, None
			def __enter__(self): self.lock = self.fighter.hexes_lock or self.fighter.HexesLock(self.fighter); self.lock.enter(); return self
			def __exit__(self, et, e, tb): self.lock.leave(); self.lock = None
			def __iter__(self): yield from filter(lambda hex: not any(q == (self.cntr, 'rem', hex) for q in self.lock.queries), self.cntr)
			def add(self, hex): self.lock.queries.append(self.lock.Query(self.cntr, 'add', hex))
			def remove(self, hex): self.lock.queries.append(self.lock.Query(self.cntr, 'rem', hex))

	def lock_hexes(self): return self.HexesLock.Context(self, self.hexes)
	def lock_caused_hexes(self): return self.HexesLock.Context(self, self.caused_hexes)

	def add_special(self, special):
		assert not any((lambda a=special, b=type(sp): isinstance(a, b) or isinstance(b, a))() for sp in self.specials), "duplicate special"
		special.set_fighter(self)
		insort_right(self.specials, special, key=lambda special: special.LIST_ORDER)

	def remove_special(self, special):
		self.specials.remove(special)
		special.reset_fighter(self)

	def set_unarmed(self, unarmed):
		if self.unarmed: self.unarmed.reset_fighter(self)
		self.unarmed = unarmed
		if unarmed: unarmed.set_fighter(self)

	def has_magic(self):
		return self.spells and self.mmp

	def generic_bar(self, name, cur, max, flip):
		return left_to_right(name + ("" if flip else ":"), Con.vital_bar(cur, max, flip=flip), f"{cur}/{max}", flip=flip)
	def hp_bar(self, flip=False): return self.generic_bar("HP", self.hp, self.mhp, flip)
	def mp_bar(self, flip=False): return self.generic_bar("MP", self.mp, self.mmp, flip)

	def act_skip_turn(self):
		def get_note(sink):
			return sink.youify("{Вы/F} пропускает{е/} ход.", self)
		self.note(get_note)

	def attack_unarmed(self, target, arena):
		check(self.unarmed, "не задан флавор атаки голыми руками", self.alive, "dead")
		self.unarmed.attack(target, arena)

	# сохранить соотношения HP/MP к максимумам, если какое-то действие потенциально изменит их лимит.
	class RelativeVitals(Living.RelativeVitals):
		def __init__(self, char):
			super().__init__(char)
			self.relative_hp = char.hp / char.mhp
			self.relative_mp = char.mp / char.mmp if char.mmp > 0 else 1.0

		def __exit__(self, et, e, tb):
			self.char.cur_hp = clamp(round(self.char.mhp * self.relative_hp), 1, self.char.mhp)
			self.char.cur_mp = clamp(round(self.char.mmp * self.relative_mp), min(1, self.char.mmp), self.char.mmp)
			super().__exit__(et, e, tb)

	def __getstate__(self):
		assert not self.hexes_lock
		return {k: v for k, v in super().__getstate__().items() if k not in (
			'caused_hexes', # резолвятся здесь
			'death_cause',  # либо сохраняемый боец жив, либо эта информация не интересна
			'sinks',        # из MessageBroadcaster; подписчики по своей природе — динамическая штука, их не то что «можно не», а категорически нельзя сохранять
			'hexes_lock',   # динамическая штука
			) and not (k in ('hexes', 'spells', 'specials', 'unarmed', 'weapon') and not v)}

	def __setstate__(self, state):
		super().__setstate__(state)
		self.weapon.owner = self # отбрасывается Weapon
		for hex in self.hexes:
			hex.victim = self                # отбрасывается Hex
			hex.master.caused_hexes.add(hex) # отбрасываются здесь
		for special in self.specials:
			special.fighter = self  # отбрасывается FighterAttribute
		if self.unarmed: self.unarmed.fighter = self # отбрасывается FighterAttribute

class Weapon(Living):
	ap_limit = property(lambda self: 1 + (self.xl - 1))
	LEVEL_CAP = 5

	def __init__(self):
		Living.__init__(self)
		self.owner = None
		self.ammos = []

	def __getstate__(self):
		return {k:v for k, v in super().__getstate__().items() if k not in (
			'owner', # резолвится Fighter
			)
			and not (k == 'ammos' and not self.ammos)}

	def __setstate__(self, state):
		super().__setstate__(state)
		for ammo in self.ammos: ammo.weapon = self # отбрасывается Ammunition

class Arena(MessageBroadcaster, MessageSink):
	BASELINE_SPD = 100

	class Battler: # Gladiator слишком длинно
		def __init__(self, fighter, squad_id, ai, shortcut, game):
			self.fighter    = fighter
			self.squad_id   = squad_id
			self.ai         = ai
			self.initiative = 0        # время до хода этого участника; после хода увеличивается на значение, зависящее от SPD
			self.shortcut   = shortcut # сокращение, используемое в командах и на шкале инициативы
			self.game       = game

	class Squad:
		def __init__(self, id):
			self.id          = id
			self.members     = []
			self.max_members = None

	def __init__(self):
		MessageBroadcaster.__init__(self)
		MessageSink.__init__(self, None, None, FICTIVE=True)
		self.battlers   = []
		self.squads     = {}
		self.turn_queue = [] # battlers, отсортированные по initiative
		self.started = False
		self.inside_turn = False
		self.last_action_cost = None
		self.squads_frozen = False

	# Арена подписывается на сообщения от бойцов, чтобы переслать их своим подписчикам.
	# Т. е. MessageSink.receive_note перенаправляется в MessageBroadcaster.note.
	# Вместе с тем, MessageBroadcaster.note может быть вызвана и напрямую, когда сообщение сгенерировано не бойцом, а, например, самой ареной («тик!»).
	def receive_note(self, msg):
		self.note(msg)

	# shortcut_hint — список предпочтительных сокращений участника, либо строка-альтернативное имя для автогенерируемых сокращений.
	# например: add(fighter, squad_id, ai, "Ghost") -> автоматически сгенерируются G, Gh, Go... G2, G3...
	#           add(fighter, squad_id, ai, ("Fi", "Alt")) -> предпочтёт Fi или Alt, прежде чем пойти по автогенерируемым из fighter.name
	def add(self, fighter, squad_id, ai, *, shortcut_hint=None, force_delay=None, game=None):
		if any(battler.fighter == fighter for battler in self.battlers): impossible(f"{fighter.name} уже на арене")
		if self.started: fighter.add_sink(self)
		battler = Arena.Battler(fighter, squad_id, ai, self.generate_shortcut(fighter, shortcut_hint), game)
		if ai: ai.setup(fighter, self)
		self.battlers.append(battler)

		squad = self.force_squad(squad_id)
		assert squad.max_members is None or len(squad.members) < squad.max_members, f"{len(squad.members)} / {squad.max_members}"
		squad.members.append(battler)

		self.turn_queue.insert(0, battler)
		self.delay_by(battler, random() if force_delay is None else force_delay)

	def remove(self, battler):
		if check(battler, isinstance(battler, Arena.Battler), "battler").ai: battler.ai.teardown()
		self.battlers.remove(battler)
		self.squads[battler.squad_id].members.remove(battler)
		self.turn_queue.remove(battler)
		if self.started: battler.fighter.remove_sink(self)

	def dismiss(self):
		while self.battlers: self.remove(self.battlers[0])

	def allies(self, fighter):
		battler = self.as_battler(fighter)
		return (member.fighter for member in self.squads[battler.squad_id].members if member.fighter != fighter and member.fighter.alive)

	def enemies(self, fighter):
		battler = self.as_battler(fighter)
		return (member.fighter for squad_id, squad in self.squads.items() if squad_id != battler.squad_id for member in squad.members if member.fighter.alive)

	def as_battler(self, fighter):
		return next(b for b in self.battlers if b.fighter == fighter)

	def turn(self):
		check(self.started, "не вызвана start", not self.inside_turn, "уже внутри turn", self.battlers, "арена пуста")
		self.inside_turn = True
		self.last_action_cost = 1.0
		if self.turn_queue[0].ai: self.turn_queue[0].ai.turn()
		self.turn_queue[0].fighter.end_turn(self)
		self.delay_by(self.turn_queue[0], self.last_action_cost * uniform(0.8, 1.2))
		self.shift_delays()
		self.inside_turn = False

		corpses = [b for b in self.battlers if b.fighter.dead]
		for corpse in corpses: self.remove(corpse)

	def whose_turn(self):
		check(self.battlers, "арена пуста")
		return self.turn_queue[0].fighter

	def delay_by(self, battler, multiplier):
		index = self.turn_queue.index(check(battler, isinstance(battler, Arena.Battler), "battler"))
		battler.initiative += multiplier * Arena.BASELINE_SPD / max(battler.fighter.spd, 1)
		while index + 1 < len(self.turn_queue) and battler.initiative >= self.turn_queue[index + 1].initiative:
			self.turn_queue[index], index = self.turn_queue[index + 1], index + 1
		self.turn_queue[index] = battler

	def start(self):
		check(not self.started, "уже")
		for battler in self.battlers:
			battler.fighter.add_sink(self)
		self.shift_delays()
		self.started = True

		def note_group(sink, group, preface):
			dudes = list(group)
			if dudes:
				return "{0} вста{1}т {2}.".format(preface, "ё" if len(dudes) == 1 else "ю", join_with_lastsep((dude.name for dude in dudes), ", ", " и "))
		self.note(lambda sink: note_group(sink, self.enemies(sink.you), "против вас"))
		self.note(lambda sink: note_group(sink, self.allies(sink.you), "с вашей стороны"))

	def shift_delays(self):
		shift = self.turn_queue[0].initiative
		for battler in self.turn_queue:
			battler.initiative -= shift

	def suggest_shortcuts(self, name_or_list):
		# это не совсем транслитерация, неподходящие символы ~выбрасываются~.
		def transliterate(src):
			def split(s): return (sym.strip() for sym in s.split('|'))
			table = dict(zip(split("а|б|в|г|д|е|ж|з|и|й|к|л|м|н|о|п|р|с|т|у|ф|х|ц|ч |ш |щ  |ъ|ы|ь|э|ю |я |ё"),
			                 split("a|b|v|g|d|e|j|z|i|y|k|l|m|n|o|p|r|s|t|u|f|h|c|ch|sh|sch|'|y|'|e|yu|ya|yo")))
			pieces = (sym if 'a' <= sym <= 'z' or '0' <= sym <= '9' else table.get(sym, None) for sym in check(src, src == src.casefold(), "src"))
			return ''.join(piece for piece in pieces if piece)

		if isinstance(name_or_list, str):
			tr = transliterate(name_or_list.casefold())
			for isecond in range(len(tr)):
				yield cap_first(tr[0] + (tr[isecond] if isecond > 0 else "")) # Buddy → B, Bu, Bd, Bd, By
			i = 2 if tr else 1
			while True: yield cap_first((tr[0] if tr else "") + str(i)); i += 1
		else:
			yield from (check(single, single == cap_first(transliterate(single.casefold())), "wrong naming") for single in name_or_list)

	def generate_shortcut(self, fighter, hint):
		packs = (hint and self.suggest_shortcuts(hint), self.suggest_shortcuts(fighter.name))
		return next(shortcut for shortcut_pack in packs if shortcut_pack for shortcut in shortcut_pack if all(b.shortcut != shortcut for b in self.battlers))

	def force_squad(self, squad_id):
		squad = self.squads.get(squad_id, None)
		if not squad:
			if self.squads_frozen: raise RuntimeError("Добавление новых альянсов запрещено явным вызовом deny_any_new_squads.")
			squad = Arena.Squad(squad_id)
			self.squads[squad_id] = squad
		return squad

	def set_action_cost(self, fighter, cost):
		check(self.inside_turn, "not inside turn()", self.turn_queue[0].fighter == fighter, "not your turn")
		self.last_action_cost = cost

	def limit_squad_members(self, squad_id, limit):
		squad = self.force_squad(squad_id)
		check(len(squad.members) <= limit, "уже больше")
		squad.max_members = min(limit, squad.max_members if squad.max_members is not None else limit)

	def deny_any_new_squads(self):
		self.squads_frozen = True

	Cumulative = namedtuple('Cumulative', 'master, victim, attack')

	# Базовый шанс попадания составляет to-hit атакующего / (to-hit атакующего + EV цели)
	# (приходится вычислять явно, а не какие-нибудь d(hit) > d(EV), чтобы легко показать игроку процент)
	# Если задействована опция cumulative, при промахе to-hit переходит в бонус для конкретно этой атаки в следующий раз
	# (т. е. таким образом нельзя повысить шанс попадания патроном остановки времени, стреляя обычными).
	# Бонус накапливается неограниченно, но обнуляется при попадании.
	#
	# Этот же механизм используется для резистящихся заклинаний, только «to-hit» → power и «EV» → MR.
	# Я сначала хотел сделать бонусы невидимыми для обычных атак (только для заклинаний — для них как-то естественнее флавор,
	# что повторные применения накапливаются), но пусть будут явными. Может, жертва устаёт уворачиваться, а атакующий анализирует её паттерны движения.
	#
	# На данный момент бонусы кому-либо кроме игрока не начисляются (даже за заклинания).
	#
	# Если в cumulative нет master, накопление to_hit происходит независимо от него:
	# например, если шанс наложения хекса должен накапливаться независимо от того, один и тот же человек его кастует или нет.
	#
	# Есть другой вариант, возможно, лучший — выравнивание энтропии.
	# Например, в Path of Exile (http://www.pathofexile.com/forum/view-thread/11707/filter-account-type/staff/page/10#p748465)
	# вероятность попадания добавляется к (изначально случайному) счётчику, при превышении которым 1 засчитывается попадание и 1 вычитается.
	# Тогда при шансе попадания 0,6 и начальном счётчике 0,1
	# удар 0: counter = 0,1 — промах
	# удар 1: counter = 0,7 — промах
	# удар 2: counter = 1,3 — попадание, -1,0 → 0,3
	# удар 3: counter = 0,9 — промах
	# удар 4: counter = 1,5 — попадание, -1.0 → 0,5
	# удар 5: counter = 1,1 — попадание, -1.0 → 0,1
	def dodge(self, to_hit, ev, *, cumulative=None):
		hit_chance = self.hit_chance(to_hit, ev, cumulative=cumulative)
		hit_roll = random()
		dodged = hit_roll >= hit_chance
		return dodged, hit_chance, hit_roll

	def hit_chance(self, to_hit, ev, *, cumulative=None):
		return to_hit / (to_hit + ev)

# Дёргает бойца на арене за ниточки.
class AI:
	def __init__(self):
		self.fighter = self.arena = None

	def setup(self, fighter, arena):
		check(self.fighter, not self.fighter, "double setup")
		self.fighter, self.arena = fighter, arena

	def teardown(self):
		check(self.fighter, "double teardown")
		self.fighter = self.arena = None

	def note(self, *args, **kargs):
		self.fighter.note(*args, **kargs)

	def turn(self):
		self.do_turn()

	def do_turn(self): raise NotImplementedError("do_turn")

class PlayerAI(AI):
	def __init__(self):
		super().__init__()
		self.decision = None

	def decide(self, what):
		check(not self.decision, "decision already set")
		self.decision = what

	def do_turn(self):
		check(self.decision, "decision?!")
		self.decision(self)
		self.decision = None

class DummyAI(AI):
	def do_turn(self):
		chooses = []
		def make_look_with_hate_at(who):
			def note_msg(sink):
				return self.fighter.name + sink.youify(" с ненавистью смотрит на {вас/F:A}", who) + "."
			return lambda: self.note(note_msg)

		def make_look_with_love_at(who):
			def note_msg(sink):
				return self.fighter.name + sink.youify(" смотрит на {вас/F:A} с любовью.", who)
			return lambda: self.note(note_msg)

		def make_idle():
			def note_msg(sink):
				return self.fighter.name + " облизывается."
			return lambda: self.note(note_msg)

		for ally in self.arena.allies(self.fighter):
			chooses.append((1.0, make_look_with_love_at(ally)))

		for enemy in self.arena.enemies(self.fighter):
			chooses.append((1.0, make_look_with_hate_at(enemy)))
		chooses.append((1.0, make_idle()))

		choose(chooses, get_weight=lambda act, index: act[0])[1]()

class MeleeAI(AI):
	def __init__(self):
		super().__init__()
		self.lock_on = self.lock_interest = None

	def do_turn(self):
		if not self.lock_on or not self.lock_on.alive or self.lock_interest <= 0:
			target = choose(self.arena.enemies(self.fighter), default=None)
			if target:
				self.lock_on = target
				self.lock_interest = randrange(3, 6)
			else:
				self.lock_on = None

		if self.lock_on:
			if self.fighter.unarmed:
				self.fighter.attack_unarmed(self.lock_on, self.arena)
				self.lock_interest -= 1
			else:
				self.note(self.fighter.name + " не может найти свои руки (БАГ).")
		else:
			self.note(lambda sink: sink.youify("{Вы/F} облизывает{есь/ся}.", self.fighter))

# Поведение, основанное на взвешенно-случайном выборе из возможных действий.
# TODO
class RandomizedAI(AI):
	class ActionTrack:
		def __init__(self):
			self.soft_cooldown = 0
			self.hard_cooldown = 0

	class Option:
		def __init__(self, cb, id, weight, soft_cooldown_base, hard_cooldown):
			self.cb, self.id, self.weight, self.soft_cooldown_base, self.hard_cooldown = cb, id, weight, soft_cooldown_base, hard_cooldown

	def __init__(self):
		super().__init__()
		self.tracks = {}
		self.options = []

	def teardown(self):
		self.tracks = self.options = None

	def consider(self, id, cb, weight, *, soft_cooldown_base=0, hard_cooldown=0):
		self.options.append(self.Option(cb, id, weight, soft_cooldown_base, hard_cooldown))
	def do_considerations(self): raise NotImplementedError("do_considerations")

	def do_turn(self):
		options = self.do_considerations()
		raise NotImplementedError("do_turn")

class Con:
	# На данный момент сделано так, что чуть больше нуля даёт [#....] и чуть меньше максимума — [####.]
	@staticmethod
	def vital_bar(cur, max, divs=10, fillchar='#', emptychar='.', flip=False):
		fill = int(clamp(int(cur > 0) + (divs - 1) * (cur / (max or 1)), 0, divs))
		return f"[{{{int(flip)}}}{{{int(not flip)}}}]".format(fillchar * fill, emptychar * (divs - fill))

	@staticmethod
	def bullet_bar(cur, max, fillchar='#', emptychar='.'):
		return fillchar * cur + emptychar * (max - cur)

	# Раньше wrap() был устроен чуть сложнее, чтобы попытаться доходить до края терминала, когда возможно, но это не всегда работало:
	# нет гарантии, что консоль переведёт строку по достижении get_terminal_size.columns.
	@staticmethod
	def safe_width(width):
		return width - 1

class VitalBarTest(TestCase):
	def cases(self): return (0, 5, 5, 0), (1, 5, 5, 1), (2, 5, 5, 2), (3, 5, 5, 3), (4, 5, 5, 4), (5, 5, 5, 5), (0.001, 5, 5, 1), (4.999, 5, 5, 4), (1.4, 5, 5, 2)
	def one(self, cur, max, divs, expect_bars):
		self.assertEqual(Con.vital_bar(cur, max, divs), "[{0}{1}]".format('#' * expect_bars, '.' * (divs - expect_bars)))

class Mode:
	def __init__(self):
		self.session = None
		self.last_screen = self.last_input = ""
		self.invalidated = False

	def process(self):
		self.do_process()

	def render(self, lines, cmds):
		self.do_render(lines, cmds)
		if self.do_prompt: lines.append("\n> ")

	def do_process(self): pass
	def do_render(self, lines, cmds): raise NotImplementedError("do_render")

	def activate(self): self.do_activate()
	def deactivate(self): self.do_deactivate()
	def do_activate(self): pass
	def do_deactivate(self): pass

	def handle_command(self, cmds): return self.do_handle_command(cmds)
	def do_handle_command(self, cmd): return False

	def switch_to(self, mode):
		self.session.switch_to(mode)

	def revert(self, n=1):
		check(self.session.mode == self, "session.mode != self")
		return self.session.revert(n)

	# Обычно родительские режимы не перерендериваются, а используется запомненная с последнего render картинка.
	# invalidate форсирует перерисовку. Пример: после команды heal hp полоска немедленно перерисовывается, несмотря на то, что активно more-сообщение.
	def invalidate(self):
		self.invalidated = True
		return self.session.cls_once()

	def shortcut(self, mode, *a, **ka):
		mode = mode(*a, **ka)
		self.switch_to(mode)
		return mode

	def more(self, *a, **ka): return self.shortcut(More, *a, **ka)
	def prompt(self, *a, **ka): return self.shortcut(Prompt, *a, **ka)

	do_prompt = True
	do_cls    = True
	term_width = property(lambda self: self.session.term_width)
	term_height = property(lambda self: self.session.term_height)
	safe_term_width = property(lambda self: self.session.safe_term_width)
	prev_mode = False # запомнит предыдущий режим, т. о. к нему можно будет вернуться

class MainMenu(Mode):
	def do_render(self, lines, cmds):
		def add_multi(synonims, *args):
			for cmd in synonims:
				cmds.add(cmd, *args)

		ci = 1
		lines.extend([
			               "        VISIBLE FIGHTERS v.{0}       ".format(".".join(str(part) for part in app_version)),
			             "({0})        - новая игра -        (new)".format(ci)])
		add_multi((str(ci), 'new'), lambda: self.start_new_game(), '?', lambda: self.more("Начать новую игру."))
		ci += 1

		if os.path.exists(Game.SAVE_FOLDER):
			lines.append("({0})      - продолжить игру -    (load)".format(ci))
			add_multi((str(ci), 'load'), lambda: self.switch_to(LoadGame()), '?', lambda: self.more("Продолжить сохранённую игру."))
			ci += 1

		lines.extend([
			             "({0})         - справка -         (help)".format(ci),
			               "(0)          - выход -          (quit)"])
		add_multi((str(ci), 'help'), lambda: self.more(MainMenu.Help, do_cls=True), '?', lambda: self.more("Вывести справку об основных моментах."))
		add_multi(('0', 'quit', 'exit'), lambda: self.session.post_quit(), '?', lambda: self.more("Выйти из приложения."))

	def start_new_game(self):
		game = Game()
		game.gold = 100
		game.player = Fighter()
		game.player.set_unarmed(BareHands())
		game.player.set_weapon(Weapon())
		game.next_level = 1
		self.switch_to(AskName(game))

	Help = \
		"Ваш автомат — живой, и при использовании в бою ему будет перенаправлена часть опыта. Пули пробивают броню, но не масштабируются статами персонажа.\n"\
		"\n"\
		"Сила      (STR) — |влияет на силу ударов и максимум HP.\n"\
		"Интеллект (INT) — |на максимум маны, силу заклинаний и сопротивление магии.\n"\
		"Ловкость  (DEX) — |на точность атаки и шанс уворота.\n"\
		"Скорость  (SPD) — |на инициативу в бою. Например, если ваша скорость 150, а противника 100, "\
		                   "на три ваших действия будут приходиться два действия противника.\n"\
		"\n"\
		"Между боями вы можете тратить золото на апгрейды в пределах полученного опыта. Золото за даунгрейд компенсируется частично.\n"\
		"В игре 10 уровней. Сохранение выполняется автоматически.\n"\
		"\n"\
		"Можно сокращать команды: heal hp -> h h, b.fire? -> b.f?.\n"\
		"                                               ^       ^\n"\
		"                                       |\"?\" выводит справку по команде или подписанному элементу экрана."

class LoadGame(Mode):
	def __init__(self):
		super().__init__()
		self.first = 0
		self.show = None
		self.had_previews = None
		self.first_up = self.show_up = self.first_dn = self.show_dn = None
		self.something_new = self.up_new_miss = None
		self.display_order_keys = False

	def estimate_items_count(self, start, down=True):
		previews = self.session.previews
		reserve = 9
		ok_lines = ok_count = longest_desc = 0
		# ok_lines и ok_count — принятое число строк с описаниями сохранений и число самих сохранений.
		# Пока возможно, добавляем очередное сохранение.
		# reserve — всякие вопросики на экране, longest_desc — в диалогах загрузки и удаления какое-то из сохранений напечатается ещё раз.
		while down and start >= 0 or not down and start < len(previews.items):
			count = ok_count + 1
			index = start + count - 1 if down else start - count
			if down and index >= len(previews.items) or not down and index < 0:
				break # край списка

			desc_len = previews.items[index].load_screen_desc_lines() + 1 # пустая строка после описания
			lines = ok_lines + desc_len
			longest_desc = max(longest_desc, desc_len)

			# lines — строчки одних описаний, для окончательной оценки добавим к ним окружающие и сравним с term_height
			deco_lines = lines + longest_desc + reserve
			if (start if down else index) > 0: deco_lines += 2 # (up) + пустая строка
			if (index if down else start - 1) < len(previews.items) - 1: deco_lines += 2 # (down) + пустая строка
			if deco_lines <= self.session.term_height:
				ok_count, ok_lines = count, lines # и пробовать дальше!~
			else:
				break
		return min(max(2, ok_count), len(previews.items) - start if down else start)

	def do_process(self):
		previews = self.session.previews
		if not self.up_new_miss: self.up_new_miss = previews.update()
		self.something_new = self.up_new_miss
		if self.had_previews is None: self.had_previews = bool(previews.items)
		if not previews.items:
			return self.revert().more("Нет сохранений.", do_cls=self.had_previews)

		if self.first >= len(previews.items):
			# Если обзор уехал за последнее сохранение (мало ли они сами поудалялись), подвинуть на нижние видимые позиции.
			self.show = self.estimate_items_count(len(previews.items), down=False)
			self.first = len(previews.items) - self.show
		else:
			# Обычный сценарий: просто подогнать под экран.
			self.show = self.estimate_items_count(self.first, down=True)

		# Доступна ли прокрутка вниз, и какими будут новые first/show?
		if self.first + self.show < len(previews.items):
			self.first_dn = self.first + self.show
			self.show_dn  = self.estimate_items_count(self.first_dn)
			check(self.show_dn, self.show_dn > 0, "show_dn")
		else:
			self.first_dn = None

 		# То же для прокрутки вверх
		if self.first > 0:
			count = check(self.estimate_items_count(self.first, down=False), lambda count: count > 0, "count")
			self.first_up = self.first - count
			self.show_up = count
		else:
			self.first_up = None

	def do_render(self, lines, cmds):
		if self.first_up is not None:
			lines.append(f"({1 + self.first_up}–{1 + self.first_up + self.show_up - 1}) (up)")
			cmds.add('up', lambda: self.up(), '?', lambda: self.more("Прокрутить список вверх."))

		def describe_up_new_miss_onetime():
			um, self.up_new_miss = self.up_new_miss, None
			return um and "     ({0})".format("/".join(s for s in (um[0] and f"+{um[0]}", um[1] and f"-{um[1]}") if s))

		desc_pad = len(str(self.first + self.show)) + 3 # (, число, ), пробел
		for index, item in enumerate(self.session.previews.items[self.first:self.first + self.show]):
			for _tryIndex in range(2): # перестраховка, скорее всего, не нужно, но пусть будет
				try:
					lead = "\n" if item.index > self.first or self.first > 0 else ""
					lines.append(lead + self.save_desc(item, desc_pad, first_line_extra = index == 0 and describe_up_new_miss_onetime()))
					break
				except Exception as e:
					if not item.bad and _tryIndex == 0: self.session.previews.force_bad(item, e)
					else: raise
			if item.bad:
				cmds.add(str(1 + item.index), self.create_remove_request_handler(item, desc_pad), '?', lambda: self.more("Удалить это сохранение."))
			else:
				cmds.add(str(1 + item.index), self.create_load_request_handler(item, desc_pad), '?', lambda: self.more("Загрузить это сохранение."))
			if not item.seen:
				self.something_new = True # <enter> уберёт звёздочки, а не прокрутит экран
				item.seen = True # пользователь увидел — в следующий раз не рисовать звёздочку

		remove_inscriptions = ['remove <номер>']
		if self.session.previews.items:
			cmds.add('remove', self.create_remove_by_number_handler(desc_pad),
				'?', lambda: self.more("Удалить сохранение{0}.".format(" (спросит номер)" if len(self.session.previews.items) > 1 else "")))
		for item in self.session.previews.items[self.first:self.first + self.show]:
			cmds.add('remove ' + str(1 + item.index), self.create_remove_request_handler(item, desc_pad), '?', lambda: self.more("Удалить это сохранение."))

		if len(self.session.previews.items) > 1:
			cmds.add('remove all', self.create_batch_remove_handler(None, "все"), '?', lambda: self.more("Удалить все сохранения."))
			remove_inscriptions.append('remove all')

		if any(item.bad for item in self.session.previews.items):
			remove_inscriptions.append('remove bad')
			cmds.add('remove bad', self.create_batch_remove_handler(lambda item: item.bad, "повреждённые", default_yes=True),
				'?', lambda: self.more("Удалить повреждённые сохранения."))

		if self.first_dn is not None:
			lines.append(f"\n({1 + self.first_dn}–{1 + self.first_dn + self.show_dn - 1}) (down)")
			cmds.add('down', lambda: self.down(), '?', lambda: self.more("Прокрутить список вниз."))

		lines.append("\nУдалить сохранение ({0})".format(", ".join(remove_inscriptions)))
		lines.append("Вернуться в главное меню (quit)")
		cmds.add('force update', lambda: self.force_update(), '?', lambda: self.more("Перечитать содержимое папки с сохранениями."))
		cmds.add('quit', lambda: self.switch_to(MainMenu()), '?', lambda: self.more("Вернуться в главное меню."))

	def do_handle_command(self, cmd):
		if cmd == "":
			if not self.something_new:
				self.up_new_miss = self.session.previews.update()
				if not self.up_new_miss:
					if self.first_dn is not None: self.down()
					else: self.first = 0
			return True
		elif cmd == '*ok':
			self.display_order_keys = not self.display_order_keys
			return True

	def up(self):
		self.first = check(self.first_up, self.first_up is not None, "first_up?!") # а show всё равно обновится в process

	def down(self):
		self.first = check(self.first_dn, self.first_dn is not None, "first_dn?!")

	def save_desc(self, item, pad, first_line_extra=None):
		cmd = "({0}) ".format(1 + item.index).ljust(pad)
		return cmd + item.load_screen_desc(npad = pad, first_line_extra=first_line_extra, display_order_key=self.display_order_keys)

	def create_load_request_handler(self, item, desc_pad):
		check(item.preview, "preview?!")
		def confirm_load(input, mode):
			if not input or 'yes'.startswith(input):
				Game.load_nothrow(item, self, on_fail=lambda mode: mode.reverts(2))
			else:
				mode.revert()

		def handler():
			self.prompt("\n{0}\n\nЗагрузить эту игру? (Y/n) ".format(self.save_desc(item, desc_pad)), confirm_load)
		return handler

	def create_remove_request_handler(self, item, desc_pad, extra_reverts=0):
		def confirm_remove(input, mode):
			if not input and item.bad or input and 'yes'.startswith(input):
				Game.remove_save_nothrow(mode, item.full_save_path, item, extra_reverts=1 + extra_reverts, note_success=True)
			else:
				mode.revert(1 + extra_reverts)

		def handler():
			self.prompt(
				"\n{0}\n\nУдалить это сохранение? ({1}) ".format(self.save_desc(item, desc_pad), highlight_variant("y/n", 0 if item.bad else 1)),
				confirm_remove)
		return handler

	def create_remove_by_number_handler(self, desc_pad):
		def remove_by_number():
			count = len(self.session.previews.items)
			if count == 1:
				self.create_remove_request_handler(self.session.previews.items[0], desc_pad)()
			elif count:
				def handle_answer(input, mode):
					if not input:
						mode.revert()
						return

					try:
						index = int(input) - 1
						if index >= 0 and index < count:
							self.create_remove_request_handler(self.session.previews.items[index], desc_pad, extra_reverts=1)()
						else:
							raise ValueError("Неверный ввод.")
					except ValueError:
						mode.more("Нет таких.").reverts(2)
				self.prompt(f"Какое сохранение удалить? ({1} – {count}) ", handle_answer)
		return remove_by_number

	def create_batch_remove_handler(self, predicate, adjective, default_yes=False):
		def remove():
			total = sum(1 for item in self.session.previews.items if not predicate or predicate(item))
			def confirm(input, mode):
				removed = 0
				if (not input and default_yes) or input and 'yes'.startswith(input):
					for item in reversed(self.session.previews.items):
						if (not predicate or predicate(item)) and not Game.remove_save_nothrow(mode, item.full_save_path, item, extra_reverts=1):
							check(isinstance(self.session.mode, More), "сейчас должно висеть сообщение об ошибке remove_save_nothrow")
							self.session.mode.msg += "\n\n{0}, {1}.".format(plural(removed, "{N} файл{/а/ов} удал{ён/ены/ены}"),
								plural(total - removed, "{N} не обработан{/о/о}"))
							break
						removed += 1
					else:
						mode.more("{0} сохранения удалены.".format(cap_first(adjective))).reverts(2)
				else:
					mode.revert()
			self.prompt("Удалить {0}? ({1}) ".format(plural(total, "{N} сохранени{е/я/й}"), highlight_variant("y/n", 0 if default_yes else 1)), confirm)
		return remove

	def force_update(self):
		if self.last_input != 'force update': return self.more("force update — ответственная команда, введите полностью.")
		self.session.previews.post_force_update(silent=False)
		self.more("Обновление...")
	prev_mode = True

class More(Mode):
	do_prompt = False
	prev_mode = True

	def __init__(self, msg, do_cls=False):
		super().__init__()
		self.msg = msg
		self.do_cls = do_cls
		self._reverts = 1
		self.continuation = None

	def do_render(self, lines, cmds):
		lines.append(wrap(self.msg + ("" if self.input_comes else "\n<enter>"), self.safe_term_width))

	def do_handle_command(self, cmd):
		mode = self.revert(self._reverts) if self._reverts else self
		if self.continuation: self.continuation(mode)
		return True

	def then(self, what):
		check(not self.continuation, "Продолжение уже задано.")
		self.continuation = what

	def reverts(self, n):
		self._reverts = check(n, n >= 0, "n?!")
		return self
	input_comes = False

class Prompt(More):
	def __init__(self, msg, callback, casefold_input=True, *, do_cls=False):
		super().__init__(msg, do_cls)
		self.callback, self.casefold_input = callback, casefold_input

	def do_handle_command(self, cmd):
		cmd = cmd.strip()
		self.callback(cmd.casefold() if self.casefold_input else cmd, self)
		return True
	input_comes = True

# Прогресс игрока и информация о сейве.
class Game:
	SAVE_FOLDER, SAVE_SUFFIX = os.path.join(os.path.dirname(sys.executable if getattr(sys, 'frozen', False) else __file__), 'save'), ".sav"
	SAVE_FILE_BASE_NAME_DONT_TOUCH = '\x00/' # save_file_base_name нужна для обнаружения необходимости смены имени, это — маркер «не менять»
	MAGIC = b'H,/m seX}Y', 2942819, 127
	PLAYER_SQUAD = 0
	MONSTER_SQUAD = 1

	def __init__(self):
		self.character_uid  = None # Для отслеживания сохранений с одинаковыми именами персонажей.
		self.full_save_path = None
		self.rel_save_path  = None # используется как ключ в PreviewsList и при сравнении известных превью с результатами os.walk().
		                           # Весь этот цирк с full/rel обусловлен тем, что я иррационально не хочу дёргать os.path.basename(full_save_path).
		self.save_file_base_name = None # это НЕ имя файла, это его «основа» (с именем персонажа, etc.)
		                                # по несоответствию base_filename() обнаруживается необходимость переключиться на новый файл
		self.gold           = None
		self.player         = None
		self.next_level     = None
		self.god_mode       = False

	def enough_gold_for(self, cost):
		return self.gold >= cost

	def give_gold(self, amount):
		self.gold += amount

	def take_gold(self, amount):
		check(self.enough_gold_for(amount), "not enough gold")
		self.gold -= amount

	class BadSaveError(Exception): pass
	@staticmethod
	def corrupted_save_error(what=None):
		return Game.BadSaveError("Сохранение повреждено{0}.".format(f" ({what})" if what else ""))

	# Превью для быстрой загрузки. Сохранение состоит из Preview.to_list() и Game.to_complement()
	class Preview:
		__slots__ = (
			'character_uid', 'order_key',
			'player_name', 'player_level', 'player_next', 'weapon_name', 'weapon_level', 'weapon_next',
			'gold', 'next_level', 'timestamp', 'god_mode',
			'compress')

		def __init__(self, game=None, order_key=None, compress=True):
			self.order_key      = order_key
			self.character_uid  = game and game.character_uid
			self.player_name    = game and str(game.player.name)
			self.player_level   = game and game.player.xl
			self.player_next    = game and game.player.next_percentage()
			self.weapon_name    = game and str(game.player.weapon.name)
			self.weapon_level   = game and game.player.weapon.xl
			self.weapon_next    = game and game.player.weapon.next_percentage()
			self.gold           = game and game.gold
			self.next_level     = game and game.next_level
			self.timestamp      = game and localtime()
			self.god_mode       = game and game.god_mode
			self.compress       = compress

		store_fields = [('character_uid', int), ('order_key', int),
			('player_name', bytes), ('player_level', int), ('player_next', (int, type(None))),
			('weapon_name', bytes), ('weapon_level', int), ('weapon_next', (int, type(None))),
			('gold', int), ('next_level', int), ('timestamp', int)]
		unchanged_fields = ('character_uid', 'gold', 'next_level', 'god_mode')
		extra_flags = ['compress', 'god_mode']

		def to_list(self):
			check(self.order_key, self.order_key is not None, "order_key?!")
			# order_key начинается со второго бита, в младших хранятся extra_flags:
			# нулевой означает, используется ли сжатие (возможность его выключить поддерживается, потому что мне иногда интересно посмотреть, ЧО ТАМ)
			# первый хранит флаг god mode
			flag_bits = functools.reduce(operator.or_, (int(getattr(self, flag)) << i for i, flag in enumerate(Game.Preview.extra_flags)))
			return [save_version] + [
				int(mktime(self.timestamp)) if field == 'timestamp' else # секундной точности достаточно
				pcgxor(getattr(self, field).encode()) if field in ('player_name', 'weapon_name') else # не светить непосредственно
				self.order_key << len(Game.Preview.extra_flags) | flag_bits if field == 'order_key' else
				getattr(self, field)
				for field, _ in Game.Preview.store_fields]

		@staticmethod
		def from_list(d):
			pv = Game.Preview()
			if not isinstance(d, list) or len(d) < 1 or not isinstance(d[0], int):
				raise Game.corrupted_save_error()

			if d[0] != save_version or len(d) != 1 + len(Game.Preview.store_fields):
				raise Game.BadSaveError("Несовместимая версия сохранения.")  # хотя можно и совместимость устроить... даже просто не проверять

			for index, (field, field_type) in enumerate(Game.Preview.store_fields, 1):
				value = d[index]
				if not isinstance(value, field_type): raise Game.corrupted_save_error(f"{field}: {type(value)}")
				elif field == 'timestamp': pv.timestamp = localtime(value)
				elif field in ('player_name', 'weapon_name'): setattr(pv, field, pcgxor(value).decode())
				elif field == 'order_key':
					pv.order_key = value >> len(Game.Preview.extra_flags)
					for i, flag in enumerate(Game.Preview.extra_flags): setattr(pv, flag, bool(value & 1<<i))
				else: setattr(pv, field, value)
			return pv

	@staticmethod
	def load_preview(file):
		return Game.Preview.from_list(pickle.load(file))

	# Придумать основу имени файла. НУЖНО ПОАККУРАТНЕЕ, если игрок назвался чем-то типа ..\
	def base_filename(self):
		check(self.player, "player?!")
		def validate_char(i, c, s): return (
			'0' <= c <= '9' or
			'a' <= c <= 'z' or 'A' <= c <= 'Z' or
			'а' <= c <= 'я' or 'А' <= c <= 'Я' or c in 'ёЁ-!()[]' or c in ' .' and 0 < i < len(s)-1)

		def sanitize(name):
			return "".join(c for i, c in enumerate(name) if validate_char(i, c, name))

		return "{0} Lv.{1} ({2} Lv.{3}) D{4}".format(
			sanitize(self.player.name) or "Игрок", self.player.xl, sanitize(self.player.weapon.name) or "автомат", self.player.weapon.xl, self.next_level)

	def open_new_file(self):
		file, full_path, rel_path, base, num = None, None, None, self.base_filename(), None
		while True:
			try:
				rel_path  = base + (f" ({num})" if num else "") + Game.SAVE_SUFFIX
				full_path = os.path.join(self.SAVE_FOLDER, rel_path)
				file = open(full_path, 'x+b')
				break
			except FileExistsError:
				num = num + 1 if num else 2
			if num > 99: raise RuntimeError(f"Слишком много сохранений вида \"{base}\".")
		return file, full_path, rel_path, base

	@staticmethod
	def remove_from_save_folder(path, throw=True):
		try:
			os.remove(path)
			throw = False
			os.rmdir(Game.SAVE_FOLDER)
		except OSError:
			if throw: raise

	@staticmethod
	def remove_save(session, full_path, rel_path_or_item):
		Game.remove_from_save_folder(full_path)
		session.previews.note_remove(rel_path_or_item)

	@staticmethod
	def remove_save_nothrow(mode, full_path, rel_path_or_item, extra_reverts=0, then=None, note_success=False):
		try:
			Game.remove_save(mode.session, full_path, rel_path_or_item)
			if note_success:
				mode = mode.more("Сохранение удалено.").reverts(1 + extra_reverts)
				if then: mode.then(lambda mode: then(True, mode))
			elif then: then(True, mode)
			return True
		except Exception as e:
			mode = mode.more("Не удалось удалить сохранение.\n" + exception_msg(e)).reverts(1 + extra_reverts)
			if then: mode.then(lambda mode: then(False, mode))

	def will_autosave_to_new_file(self):
		return self.save_file_base_name != Game.SAVE_FILE_BASE_NAME_DONT_TOUCH and self.save_file_base_name != self.base_filename()

	def save(self, session, to_new_file=False, compress=True):
		# убедиться в существовании папки с сохранениями
		with suppress(FileExistsError):
			os.mkdir(Game.SAVE_FOLDER)

		# Придумать character_uid, если его ещё нет.
		# Единственное, для чего он нужен — суффиксы вида «-2» на экране загрузки для разных персонажей с одинаковыми именами.
		# Т. о. коллизии не критичны, 2**16=65536 достаточно. Ну не выведется с маленькой вероятностью суффикс, когда нужен, подумаешь.
		if self.character_uid is None:
			self.character_uid = randrange(2**16)

		# Вообще-то choose_order_key потенциально дёргает previews.update(), а она, в свою очередь, может сломать предположение,
		# что self.rel_save_path есть в previews. Это всё работает только благодаря удачному сочетанию случайностей:
		# больше никто не дёргает previews.update при активной Game, а сама choose_order_key дёргает,
		# только когда ей не сообщили имя существующего сохранения, что возможно только при to_new_file or not self.rel_save_path,
		# но в обоих этих случаях выполнение пойдёт по ветке note_add, т. е. полагается, что rel_save_path И НЕ БЫЛО в previews.
		#
		# Сейчас всё вроде бы стабильно работает без искусственной робастности, но когда-нибудь, возможно,
		# несуществующие rel_save_path, переданные в previews.note_update (а также существующие, переданные в note_add)
		# придётся там же тихо игнорировать/фиксить задним числом вместо ассертов.
		order_key = session.previews.choose_order_key(not to_new_file and self.rel_save_path)

		# Записать сразу в новый файл, если:
		# — это явно требуется (to_new_file=True)
		# -или-
		# — используется семантика автосохранения (to_new_file=False), но старого файла не было или игра хочет его сменить всё равно.
		#   Логика этого решения вынесена в will_autosave_to_new_file, т. к. интересна кое-кому извне.
		if to_new_file or self.will_autosave_to_new_file():
			file, full_path, rel_path, base = self.open_new_file()
			try:
				try:
					preview = self.save_to(file, order_key, compress=compress)
				finally:
					file.close()

				# Если это автосохранение, удалить старый файл.
				if not to_new_file and self.full_save_path:
					Game.remove_from_save_folder(self.full_save_path, throw=False)

					# Но пошаманить над превью так, чтобы оно осталось на месте — с корректными order_key разницы не будет,
					# но если они сбились, это, в отличие от .note_remove + .note_add, оставит превью в старом месте списка.
					session.previews.note_update(self.rel_save_path, preview, full_path, rel_path)
				else:
					session.previews.note_add(full_path, rel_path, preview)

				# в обоих случаях автосохранение впредь будет выполняться в новый файл.
				self.full_save_path, self.rel_save_path, self.save_file_base_name = full_path, rel_path, base
			except:
				Game.remove_from_save_folder(full_path, throw=False)
				raise
		else:
			# Сохранение в тот же файл: записать временный, затем атомарно заменить существующий.
			# (На самом деле лучше и для случая выше сохранять во временный, чтобы при выдёргивании вилки из розетки не оставлять недописанный .sav).
			tmp_fd, tmp_path = tempfile.mkstemp(suffix = ".tmp", prefix = self.base_filename(), dir = self.SAVE_FOLDER)
			# Не знаю, как с ними правильно работать, так что перестрахуюсь.
			try:
				with open(tmp_fd, 'wb') as file:
					tmp_fd = 'CLOSED'
					preview = self.save_to(file, order_key, compress=compress)
				os.replace(tmp_path, self.full_save_path)
				session.previews.note_update(self.rel_save_path, preview)
			except:
				if tmp_fd != 'CLOSED': os.close(tmp_fd)
				Game.remove_from_save_folder(tmp_path, throw=False)
				raise

	def save_nothrow(self, mode, then=None, note_success=False, to_new_file=False, extra_error_comment=None, compress=True):
		try:
			self.save(mode.session, to_new_file, compress=compress)
		except Exception as e:
			mode = mode.more("Не удалось сохранить игру{0}.\n".format(extra_error_comment or "") + exception_msg(e))
			if then: mode.then(lambda mode: then(False, mode))
		else:
			if note_success:
				mode = mode.more("Игра сохранена.")
				if then: mode.then(lambda mode: then(True, mode))
			elif then: then(True, mode)

	complement_fields = [('player', Fighter)]
	def to_complement(self):
		return [getattr(self, k) for k, _ in Game.complement_fields]

	@staticmethod
	def load_complement(file):
		complement = pickle.load(file)
		if not isinstance(complement, list) or len(complement) != len(Game.complement_fields): raise Game.corrupted_save_error('complement')
		for index, (field, field_type) in enumerate(Game.complement_fields):
			if not isinstance(complement[index], field_type): raise Game.corrupted_save_error(field + ": " + str(type(complement[index])))
		return complement

	@staticmethod
	def from_preview_and_complement(preview, complement, full_save_path, rel_save_path):
		g = Game()
		for k in Game.Preview.unchanged_fields:
			setattr(g, k, getattr(preview, k))
		for index, (k, _) in enumerate(Game.complement_fields):
			setattr(g, k, complement[index])

		g.full_save_path, g.rel_save_path = full_save_path, rel_save_path
		# если имя файла сформировано по тем же правилам, что сформировало бы само приложение...
		if os.path.basename(g.rel_save_path).startswith(g.base_filename()):
			g.save_file_base_name = g.base_filename() # ...то считать, что так и есть, и менять его как обычно
		else:
			# иначе пользователь переименовал файл (или изменились правила формирования имени, но этот случай опустим)
			# имя этого файла не будет меняться автоматически
			g.save_file_base_name = Game.SAVE_FILE_BASE_NAME_DONT_TOUCH
		return g

	def save_to(self, file, order_key, compress=True):
		preview = Game.Preview(game=self, order_key=order_key, compress=compress)
		file.write(pickletools.optimize(pickle.dumps(preview.to_list(), protocol=-1)))
		file.write(pcgxor(*Game.MAGIC))

		cf = lzma.open(file, 'wb', **LZMA_OPTIONS) if compress else file
		try:
			cf.write(pickletools.optimize(pickle.dumps(self.to_complement(), protocol=-1)))
		finally:
			if compress: cf.close()
		return preview

	@staticmethod
	def load(file, full_save_path, rel_save_path):
		# preview загружается с нуля, чтобы нельзя было читерить на несоответствии preview и complement, заменяя физический сейв при открытом экране загрузки :P
		# (как вариант, вообще не использовать preview на этом этапе, дублируя всю нужную информацию в complement)
		preview = Game.load_preview(file)
		if file.read(len(Game.MAGIC[0])) != pcgxor(*Game.MAGIC):
			raise Game.corrupted_save_error('magic')

		cf = lzma.open(file, 'rb', **LZMA_OPTIONS) if preview.compress else file
		try:
			complement = Game.load_complement(cf)
		finally:
			if preview.compress: cf.close()
		return Game.from_preview_and_complement(preview, complement, full_save_path, rel_save_path)

	@staticmethod
	def load_nothrow(pv, mode, on_fail=lambda mode: None, more_on_success=True):
		assert isinstance(pv, Session.PreviewsList.Item)
		try:
			with open(pv.full_save_path, 'rb') as f:
				game = Game.load(f, pv.full_save_path, pv.rel_save_path)
		except Exception as e:
			mode.session.previews.force_bad(pv, e)
			on_fail(mode.more("Не удалось загрузить игру.\n" + exception_msg(e)))
		else:
			then = lambda mode: mode.switch_to(Respite(game))
			if more_on_success: mode.more("Загрузка...").then(then)
			else: then(mode)

	def handle_command(self, input, mode):
		if len(input) == 24 and b85digest(input) == b'l-&0&k}RUvvTjw`?hXhD!&Nasi>_Nc9Q>XR^e=+*':
			was_in_god_mode, self.god_mode = self.god_mode, True
			return mode.more("Активирован режим отладки." if not was_in_god_mode else "Вы уже в режиме отладки.")
		elif len(input) == 15 and b85digest(input) == b't_$;wsqmu04xJmMznJeb0%0NrkcJ>-&y~;sRhAbz':
			was_in_god_mode, self.god_mode = self.god_mode, False
			return mode.more("Режим отладки деактивирован." if was_in_god_mode else "Вы не в режиме отладки.")

	def marks(self, lspace=False, rspace=False): # self может быть Preview
		return ((" " if lspace else "") + "*DEBUG*" + (" " if rspace else "")) if self.god_mode else ""

class NonCombatMode(Mode, MessageSink):
	def __init__(self, game):
		Mode.__init__(self)
		MessageSink.__init__(self, game.player, lambda msg: self.handle_note(msg))
		self.game = game
		self.log = ArenaView.MessageLog()

	def do_activate(self):
		self.game.player.add_sink(self)

	def do_deactivate(self):
		self.game.player.remove_sink(self)

	def do_handle_command(self, cmd):
		return self.game.handle_command(cmd, self)

	def handle_note(self, msg):
		self.log.add(msg)

	def check_for_pending_notes(self, *, extra_reverts=0, maybe=False):
		assert maybe or self.log.something_new, "ожидались сообщения"
		if self.log.something_new:
			self.more(" ".join(self.log.scroll(None, self.safe_term_width))).reverts(1 + extra_reverts)
			assert not self.log.something_new, "неадекватная something_new"
			self.log.clear()
		elif extra_reverts:
			self.session.revert(extra_reverts)

# Экран между боями.
class Respite(NonCombatMode):
	def __init__(self, game):
		super().__init__(game)

	def describe_player(self, player, cmds, pad):
		desc = player.living_desc()

		desc += "\n" + pad + player.hp_bar()
		if player.hp < player.mhp:
			cost = clamp(round((1 - player.hp / player.mhp) * 30 + 0.25 * (player.mhp - player.hp)), 1, 50)
			desc += "   восстановить: ${0}".format(cost)
			if self.game.enough_gold_for(cost):
				desc += " (heal hp)"
				def heal_hp():
					self.game.take_gold(cost)
					player.cur_hp = player.mhp
					player.note("Ваши раны исцелены.")
					self.invalidate().check_for_pending_notes()
				cmds.add('heal hp', heal_hp, '?', lambda: self.more("Полностью восстановить очки здоровья."))
			else:
				desc += " :("

		if player.has_magic():
			def dmp_func(d):
				def modify():
					player.cur_mp = clamp(player.cur_mp + d, 0, player.mmp)
					return modify
				return modify
			cmds.add('mp+', dmp_func(+1))
			cmds.add('mp-', dmp_func(-1))

			desc += "\n" + pad + player.mp_bar()
			if player.mp < player.mmp:
				cost = clamp(round((1 - player.mp / player.mmp) * 40 + 0.5 * (player.mmp - player.mp)), 1, 70)
				desc += "   восстановить: ${0}".format(cost)
				if self.game.enough_gold_for(cost):
					desc += " (heal mp)"
					def heal_mp():
						self.game.take_gold(cost)
						player.cur_mp = player.mmp
						player.note("Ваша магическая энергия восстановлена.")
						self.invalidate().check_for_pending_notes()
					cmds.add('heal mp', heal_mp, '?', lambda: self.more("Полностью восстановить ману."))
				else:
					desc += " :("
		return desc

	def describe_weapon(self, weapon, cmds, pad):
		desc = weapon.living_desc()

		lines = []
		for ammo in weapon.ammos:
			if ammo.finite_charges:
				line = "{pad}{bullet_name} [bullets]{bullets} [/bullets]".format(pad = pad,
					bullet_name = ammo.short_name(),
					bullets = Con.bullet_bar(ammo.charges, ammo.MAX_CHARGES))

				cmd = ammo.cmd()
				if ammo.has_charges():
					def make_shoot_func(ammo):
						def shoot():
							ammo.draw_charge()
						return shoot
					cmds.add('shoot ' + cmd, make_shoot_func(ammo))

				if ammo.needs_recharging():
					line += "перезарядка: [recharge_cost]${0}[/recharge_cost]".format(ammo.recharge_cost())
					if self.game.enough_gold_for(ammo.recharge_cost()):
						def make_reload_func(ammo):
							def reload():
								self.game.take_gold(ammo.recharge_cost())
								ammo.recharge()
							return reload
						line += f" [reload_cmd](reload {cmd})"
						cmds.add('reload ' + cmd, make_reload_func(ammo))
					else:
						line += " :("
				lines.append(line)
		if lines: desc += "\n" + "\n".join(multipad(lines))
		return desc

	def do_process(self):
		if self.game.player.hp > self.game.player.mhp: self.game.player.cur_hp = self.game.player.mhp
		if self.game.player.mp > self.game.player.mmp: self.game.player.cur_mp = self.game.player.mmp

	def do_render(self, lines, cmds):
		game = self.game
		player = game.player
		weapon = player.weapon
		lines.append(f"ЛАГЕРЬ{self.game.marks(lspace=True)}")
		lines.append(f"Золото: ${game.gold} (shop)\n")
		cmds.add('shop', lambda: self.switch_to(Shop(game)), '?', lambda: self.more("Магазин, где вы можете приобрести или продать апгрейды."))
		if self.game.god_mode:
			default = 100
			def add_cmd(default=default):
				def handle_gold_answer(input, mode):
					try:
						if input and 'quit'.startswith(input): mode.revert(); return
						amount, max = (int(input) if input else default), 10000
						if 0 <= amount <= max:
							game.give_gold(amount)
							mode.revert()
						else:
							raise ValueError("Слишком много." if amount > max else "Неверное количество.")
					except ValueError as e:
						mode.more(exception_msg(e))
				cmds.add('gold+', lambda: self.prompt(f"Сколько золота добавить? (ENTER — {default}) ", handle_gold_answer))
			add_cmd()

			for who, cmd, name in ((player, 'xp', ''),) + (((weapon, 'wxp', weapon.name),) if weapon else ()):
				for sign, case, verb, func in (('+', Case.DATIVE, 'сообщить', who.receive_xp), ('-', Case.GENITIVE, 'высосать', who.drain_xp)):
					default = who.xp_for_levelup() / 2
					if sign == '-' and default > who.xp: default = who.xp_for_levelup(max(1, who.xl - 1)) / 2

					def add_cmd(cmd=cmd+sign, name=name and name(case), verb=verb, default=default, func=func):
						def handle_xp_answer(input, mode):
							try:
								if input and 'quit'.startswith(input): mode.revert(); return
								amount, max = (float(input) if input else default), 10000
								if 0 <= amount <= max:
									func(amount)
									self.check_for_pending_notes(extra_reverts=1, maybe=True)
								else:
									raise ValueError("Слишком много." if amount > max else "Неверное количество.")
							except ValueError as e:
								mode.more(exception_msg(e)).reverts(2)
						cmds.add(cmd, lambda: self.prompt(f"Сколько опыта{name and ' '}{name} {verb}? (ENTER — {default}) ", handle_xp_answer))
					add_cmd()

		pad = " " * (min(len(player.name), len(player.weapon.name)) + 2)
		lines.append(self.describe_player(player, cmds, pad))
		if weapon: lines.append("\n" + self.describe_weapon(weapon, cmds, pad))

		lines.append("\nследующий уровень (next)")
		lines.append(  "выйти             (quit)")
		cmds.add('next', lambda: self.to_next_level(), '?', lambda: self.more("Взглянуть на следующего противника. Вы ещё сможете вернуться."))
		cmds.add('quit', lambda: self.quit(), '?', lambda: self.more("Выход в меню (с сохранением)."))

	def do_handle_command(self, cmd):
		if cmd == '*br':
			self.split_soul()
			return True
		else:
			return super().do_handle_command(cmd)

	def split_soul(self):
		# Если игра собиралась сохраняться в новый файл, и эта попытка провалилась, второй раз она попробует его же, что бессмысленно.
		# И наоборот, если игра сохранялась в старый файл, то неважно, удалось ли ей это — запрашивается второе сохранение в новый и переключение на него.
		do_second_anyway = not self.game.will_autosave_to_new_file()
		self.game.save_nothrow(self, extra_error_comment=do_second_anyway and " в старый файл",
			then=lambda success, mode: (success or do_second_anyway) and self.game.save_nothrow(mode, to_new_file=True, note_success=True))

	def quit(self):
		default_yes = self.last_input == 'quit'
		allow_suicide = self.game.full_save_path
		def handle_confirmation(input, mode):
			parts = input.split('/')
			if parts and any(part and 'yes'.startswith(part) for part in parts) or not input and default_yes:
				self.game.save_nothrow(mode, then=lambda success, mode: mode.switch_to(MainMenu()), compress='r' not in parts)
			elif input and 'quit'.startswith(input):
				mode.switch_to(MainMenu()) # без сохранения — но это долго объяснять пользователю, пусть с тем же успехом дропает игру без сохранения по Ctrl-C
			elif allow_suicide and 'suicide'.startswith(input) and len(input) >= len('sui'):
				def confirm(input, mode):
					if not input or 'yes'.startswith(input):
						Game.remove_save_nothrow(mode, self.game.full_save_path, self.game.rel_save_path,
							note_success=True, then=lambda success, mode: mode.switch_to(MainMenu()))
					else:
						mode.revert()
				mode.prompt("Это сотрёт сохранение. Вы уверены? (Y/n) ", confirm)
			else:
				mode.revert()

		self.prompt("Выйти из игры? ({0}) ".format(highlight_variant("y/n", 0 if default_yes else 1)), handle_confirmation)

	def do_activate(self):
		super().do_activate()
		self.session.globals.recent_fixed_name_proposals = 0

	def to_next_level(self):
		self.game.save_nothrow(self, then=lambda success, mode: self.to_arena_entrance())

	def to_arena_entrance(self):
		def before(arena):
			# За игроком всегда первый ход.
			arena.add(self.game.player, Game.PLAYER_SQUAD, PlayerAI(), game=self.game, force_delay=0)
		arena = FixedLevels.list[self.game.next_level-1].create_arena(before)
		self.switch_to(ArenaEntrance(self.game, arena, self.game.next_level))

class Shop(NonCombatMode):
	def __init__(self, game):
		super().__init__(game)

	def do_render(self, lines, cmds):
		game, player, weapon = self.game, self.game.player, self.game.player.weapon
		lines.append(f"МАГАЗИН{game.marks(lspace=True)}\n" +
			f"Золото: ${self.game.gold}\n" +
			"\n".join(multipad([player.living_desc(for_multipad=True), weapon.living_desc(for_multipad=True)])) +
			"\n")

		lines.append("Апгрейды:")

		def add_upgrade(lines, up, target):
			line = "    " + up.shop_label(target) + " [/label]"
			if up.allow(target, ignore_ap_cost=True):
				gold_cost = up.gold_cost(target)
				ap_cost   = up.ap_cost(target)
				enough_gold = game.enough_gold_for(gold_cost)
				enough_ap   = target.enough_ap_for(ap_cost)
				def parenthesize_if(str, cond): return f"({str})" if cond else str

				line += parenthesize_if(f"${gold_cost}[/gold]", not enough_gold) + \
					" [sep]/ [ap]" + \
					parenthesize_if(str(ap_cost) + "[/ap]", not enough_ap) + \
					"[/costs] "

			# TODO: вывод описания *И* всех цен по "upgrade_name?", вместо бесполезных upgrade_name+? etc.
			cmd_list = []
			if up.allow(target) and game.enough_gold_for(gold_cost):
				cmd = up.cmd() + '+'
				cmd_list.append(cmd)
				cmds.add(cmd, self.buy_upgrade_func(target, up), '?', lambda: self.more("Приобрести этот апгрейд."))

			last = up.last(target)
			if last:
				cmd = up.cmd() + '-'
				cmd_list.append(cmd)
				cmds.add(cmd, self.sell_upgrade_func(target, last), '?', lambda: self.more("Отказаться от этого апгрейда."))

			line += "[cmds]"
			if cmd_list: line += "(" + ", ".join(cmd_list) + ")"
			lines.append(line)

		# Ограничения на уровни нужны только чтобы у игрока глаза не разбежались.
		# Но учитывая, что уровни могут понижаться, был бы шанс попасть в ситуацию, когда имеющийся апгрейд невозможно продать,
		# поэтому дополнительно проверяется их наличие. (Альтернативно, проверять какой-нибудь max_xl_so_far и никогда не блокировать уже открытые.)
		def upgrades_section(ups, target, min_xl=None, prohibit=None, lead=""):
			section_lines = []
			for up in ups:
				if (not min_xl or target.xl >= min_xl) and (not prohibit or not prohibit(up)) or up.find(target):
					add_upgrade(section_lines, up, target)
			if section_lines:
				if lead is not None: lines.append(lead)
				lines.extend(multipad(section_lines))

		upgrades_section((StrUpgrade, IntUpgrade, DexUpgrade, SpeedUpgrade), player, lead=None)
		upgrades_section((IncendiaryAmmunitionUpgrade, SilenceAmmunitionUpgrade, TimestopAmmunitionUpgrade), weapon,
			min_xl=2, prohibit=lambda up: up == TimestopAmmunitionUpgrade and weapon.xl < 3)
		upgrades_section((FirestormSpellUpgrade, DispellSpellUpgrade, FrailnessSpellUpgrade), player, min_xl=2)

		lines.append("\nВернуться в лагерь (quit)")
		cmds.add('quit', lambda: self.switch_to(Respite(self.game)), '?', lambda: self.more("Вернуться в лагерь."))

	def buy_upgrade_func(self, target, up_cls):
		def buy():
			gold = up_cls.gold_cost(target)
			def confirm(input, mode):
				if input and 'yes'.startswith(input):
					self.game.take_gold(gold)
					up = up_cls()
					up.apply(target)
					self.check_for_pending_notes(extra_reverts=1)
				else:
					mode.revert()
			self.prompt("{0} ${1}. Продолжить? (y/N) ".format(up_cls.cost_preface(target), gold), confirm)
		return buy

	def sell_upgrade_func(self, target, up):
		def sell():
			gold = up.refund()
			def confirm(input, mode):
				if input and 'yes'.startswith(input):
					up.revert(target)
					self.game.give_gold(gold)
					self.check_for_pending_notes(extra_reverts=1)
				else:
					mode.revert()
			self.prompt("В обмен на {what} вы получите ${gold}. Продолжить? (y/N) ".format(what=up.sell_accusative(target), gold=gold), confirm)
		return sell

class ArenaEntrance(Mode):
	prev_mode = True
	def __init__(self, game, arena, floor_number):
		super().__init__()
		self.game  = game
		self.arena = arena
		self.floor_number = floor_number

	# Здесь выполняется эдакий вертикальный multipad, части выравниваются по высоте:
	#
	#   Обычный крыс Lv.1              Волшебный крыс Lv.1      <-- имя (desc[0])
	# HP: [##########] 10/10          HP: [##########] 10/10    <-- полоски HP/MP (desc[1])
	#                                 MP: [##########] 10/10
	#
	# Зубы        (unarmed)           Огн. шторм (V1)           <-- способности и т. п. (desc[2])
	# Ярость      (O1)
	#
	# AC/EV       0/10                AC/EV       0/10          <-- статы (desc[3])
	# STR/INT/DEX 5/10/10             STR/INT/DEX 5/15/10
	# SPD         100                 SPD         90
	def do_render(self, lines, cmds):
		max_width = 0
		descs     = []
		max_part_height = []
		for b in self.arena.battlers:
			if b.squad_id != Game.PLAYER_SQUAD:
				desc, width = self.describe_fighter(b.fighter, b)
				if not max_part_height:
					max_part_height = [len(part) for part in desc]
				else:
					assert len(desc) == len(max_part_height), f"describe_fighter: {len(desc)} vs. {len(max_part_height)}"
					for i in range(len(desc)): max_part_height[i] = max(max_part_height[i], len(desc[i]))
				max_width = max(max_width, width)
				descs.append(desc)

		if max_width * len(descs) > self.safe_term_width:
			impossible(f"информация о противниках не умещается на экран (max_width = {max_width} x{len(descs)}, safe_term_width = {self.safe_term_width})")

		first = len(lines)
		BORDER = 2
		next_command_reserve = 2
		lines.append(f"{self.floor_number}-й этаж{self.game.marks(lspace=True)}")
		empty_lines_before = (self.term_height - 1 - next_command_reserve - sum(max_part_height) - (len(lines) - first)) // 6
		lines.extend("" for i in range(empty_lines_before))
		centered_width = self.safe_term_width // len(descs)
		if centered_width > max_width + 10:
			centered_width = max_width + 10
			margin = " " * ((self.safe_term_width - len(descs) * centered_width) // 2)
		else:
			margin = ""
		lines.extend(margin + "".join((desc[part_index][line] if line < len(desc[part_index]) else "").ljust(max_width).center(centered_width) for desc in descs)
			for part_index, part_height in enumerate(max_part_height)
				for line in range(part_height))

		lines.extend("" for i in range(empty_lines_before))

		back = BORDER * " " + "Вернуться (quit)"
		nx = "Продолжить (next)"
		nxleft = self.safe_term_width - BORDER - len(nx)
		lines.append(back + " " * (nxleft - len(back)) + nx)
		cmds.add('quit', lambda: self.back_to_camp())
		cmds.add('next', lambda: self.to_arena())

	def do_handle_command(self, cmd):
		if cmd == "":
			question_id = 'enter_arena'
			def handle_answer(input, mode):
				if self.session.globals.judge_answer(question_id, input) == 0:
					mode.revert().to_arena()
				else:
					mode.revert()
			return self.prompt("Сразиться? ({0}) ".format(self.session.globals.highlight_answer(question_id)), handle_answer)
		else:
			return self.game.handle_command(cmd, self)

	def describe_fighter(self, fighter, battler):
		name_part = [f"{fighter.name.upper()} Lv.{fighter.xl} ({battler.shortcut})"]
		vitals_part = [fighter.hp_bar()]
		if fighter.has_magic(): vitals_part.append(fighter.mp_bar())
		vitals_part.append("")

		numeric_cmd = 1
		abil_part = []
		for sp in fighter.specials:
			abil_part.append("{0} [cmd]({1})".format(sp.name(), numeric_cmd))
			numeric_cmd += 1
		for spl in fighter.spells:
			abil_part.append("{0} [cmd]({1})".format(spl.name(long=True), numeric_cmd))
			numeric_cmd += 1
		if abil_part:
			abil_part.append("")
			abil_part = multipad(abil_part)

		def gen_nv(): return filter(lambda nv: nv[1], (("AC", fighter.ac), ("EV", fighter.ev)))
		ae = " [val]".join(filter(None, ("/".join(name for name, value in gen_nv()), "/".join(str(value) for name, value in gen_nv()))))
		def gen_nv(): return filter(lambda nv: nv[1] != 10, (("STR", fighter.base_str), ("INT", fighter.base_int), ("DEX", fighter.base_dex)))
		sid = " [val]".join(filter(None, ("/".join(name for name, value in gen_nv()), "/".join(str(value) for name, value in gen_nv()))))
		stats_part = multipad([part for part in (ae, sid, fighter.spd != 100 and f"SPD [val]{fighter.spd}") if part])

		parts = [name_part, vitals_part, abil_part, stats_part]
		width = max(len(line) for lines in parts for line in lines)
		name_part[0] = " " * ((width - len(name_part[0])) // 2) + name_part[0]
		return parts, width

	def back_to_camp(self):
		self.revert()

	def to_arena(self):
		def on_leave():
			self.arena.dismiss()
		self.switch_to(ArenaView(self.game, self.arena, self.game.player, on_leave))
		self.arena.start()

class ArenaView(Mode):
	class MessageLog:
		class Line:
			__slots__ = ('line', 'turn', 'pieces_count', 'next_sep')
			def __init__(self, line, turn):
				self.line = line
				self.turn = turn
				self.pieces_count = 1
				self.next_sep = " "
		MIN_MESSAGE_LIFE_TURNS = 10
		MIN_MESSAGES = 30

		def __init__(self):
			self.lines = []
			# scroll продолжит выдавать текст, начиная с lines[scroll_line].line[scroll_index] (но может вернуться выше, если упрётся в конец)
			self.scroll_line = 0
			self.scroll_index = 0
			self.last_message, self.last_message_reps = None, 0

		def add(self, msg, turn=None, *, next_sep=" ", start_new_line=None):
			if not start_new_line and msg == self.last_message:
				self.last_message_reps += 1
				return

			self.flush()
			self.last_message = msg

			# Критерии, по которым (не) начинается новая строка.
			# Совсем никогда не начинать нельзя, т. к. из истории не могут быть стёрты отдельные добавленные таким образом фрагменты — только строка целиком.
			# (Или всё-таки запоминать позиции кусков и стирать по одному?..)
			def allow_continuation(prev):
				# pieces_count — подушка безопасности, ожидается, что такого не будет в естественных сценариях
				return prev.pieces_count < 666

			if not start_new_line and self.lines and allow_continuation(self.lines[-1]):
				line = self.lines[-1]
				line.line += line.next_sep + msg
				line.turn = turn
				line.pieces_count += 1
			else:
				line = self.Line(msg, turn)
				self.lines.append(line)
			line.next_sep = next_sep

			# стереть старые строки
			erase = 0
			while erase < len(self.lines) and \
				(self.lines[erase].turn is None or (turn - self.lines[erase].turn) > self.MIN_MESSAGE_LIFE_TURNS) and \
				len(self.lines) - (erase + 1) >= self.MIN_MESSAGES:
				erase += 1

			if erase > 0:
				if self.scroll_line < erase:
					self.scroll_line, self.scroll_index = 0, 0
				else:
					self.scroll_line -= erase
				del self.lines[:erase]

		# 1. lines=число
		# Возвращает (1) последние не более чем lines строк, которые пользователь должен увидеть в окне лога, и (2) флаг, есть ли ещё.
		# Одновременно, если really не вернула False, лог прокручивается вниз на lines-1 либо до упора.
		# Можно было бы разделить эти шаги, но это будет сложнее и мне не нужно (по сути — отложить присваивание scroll_line/scroll_index).
		#
		# 2. lines=None
		# Работает как lines=∞, но не возвращает флаг и не повторяет ранее прокрученные сообщения.
		# Иными словами, просто возвращает сообщения с текущей позиции до конца.
		def scroll(self, lines, width, really=lambda pending: True):
			self.flush()
			# Попытаться идти с lines[scroll_line].line[scroll_index] до конца. Если конец не достигнут за lines — вернуть результат как промежуточный.
			wrapped = []
			for i, line in enumerate(self.lines[self.scroll_line:], self.scroll_line):
				offset = self.scroll_index if i == self.scroll_line else 0
				# Ограничение на 1 строку больше реального.
				w = wrap_feedback(line.line[offset:], width, lines and lines - len(wrapped) + 1)
				take = len(w) if lines is None else min(len(w), lines - len(wrapped))
				wrapped.extend(L.piece for L in w[:take])

				# Если результат вылез за реальное lines - len(wrapped), значит, lines строк переполнены — вернуть промежуточный результат.
				if take < len(w) or lines is None and i + 1 == len(self.lines):
					# Прокрутить лог. Если прокрутка на более чем одну строку, продолжить с последней включительно:
					# 1 Бла                3 Бла-бла-бла
					# 2 Бла-бла       =>   4 Бла-бла-бла-бла
					# 3 Бла-бла-бла        5 Бла-бла-бла-бла-бла
					if really(True): self.scroll_line, self.scroll_index = i, len(line.line) if lines is None else offset + (w[take-1 if lines > 1 else take].start)
					return wrapped if lines is None else (wrapped, True)

			# Конец достигнут? Тогда вернуть последние lines строк (возможно, уже виденных). Алгоритм с точностью до наоборот.
			wrapped = []
			if lines is None: return wrapped

			for i, line in zip(reversed(range(len(self.lines))), reversed(self.lines)):
				w = wrap_feedback(line.line, width)
				if i == len(self.lines) - 1 and really(False): self.scroll_line, self.scroll_index = i, w[-1].start if w else 0
				take = min(len(w), lines - len(wrapped))
				if take: wrapped = [L.piece for L in w[-take:]] + wrapped
				if take < len(w): break
			return wrapped, False

		something_new = property(lambda self: (self.scroll_line, self.scroll_index) <
			(len(self.lines) - 1, self.scroll_index if self.scroll_line == len(self.lines) else len(self.lines[self.scroll_line].line)))

		def flush(self):
			if self.last_message_reps:
				self.lines[-1].line += self.lines[-1].next_sep + f"(x{1 + self.last_message_reps})"
				self.lines[-1].next_sep = " "
				self.last_message, self.last_message_reps = None, 0

		def clear(self): self.__init__()

	def __init__(self, game, arena, player, on_leave):
		super().__init__()
		self.game, self.arena, self.player = game, arena, player
		self.on_leave = on_leave
		self.awaiting_decision = None
		self.player_ai = None
		self.atb_maximum = None

		def receive_note(msg):
			if self.player.alive:
				self.log.add(msg, self.next_player_turn)
			elif not self.death_message:
				# Хрупкое предположение, что первая заметка после смерти будет её описанием. Пока работает, но в будущем, возможно,
				# понадобится цеплять к note'ам дополнительную информацию для таких случаев.
				self.death_message = msg

		self.log = self.MessageLog()
		self.sink = MessageSink(player, receive_note)
		self.log_lines = None
		self.render_log = True
		self.log_area_height = None
		self.next_player_turn = -1
		self.your_turn_announced = False
		self.start_log_at = None
		self.extra_lines = None
		self.do_prompt = True
		self.death_message = None
		self.okay_to_skip_turns = False

	def do_activate(self):
		self.player_ai = self.arena.as_battler(self.player).ai
		check(self.player_ai, isinstance(self.player_ai, PlayerAI), "player.ai")
		self.atb_maximum = self.estimate_good_atb_maximum()
		self.arena.add_sink(self.sink)

	def do_deactivate(self):
		if self.on_leave: self.on_leave()
		self.arena.remove_sink(self.sink)

	def do_process(self):
		min_log_lines = self.min_log_lines()
		min_lines_total = (
			  self.min_lines_for_squads()
			+ self.min_action_lines()
			+ min_log_lines
			+ self.reserve_lines())
		if min_lines_total >= self.term_height: impossible(f"min_lines_total = {min_lines_total}, term_height = {self.term_height}")
		extra_lines = self.term_height - min_lines_total
		extra_log_lines = round(extra_lines/3/max(1, self.term_width/50))
		self.extra_lines = extra_lines - extra_log_lines

		self.awaiting_decision = False
		self.do_prompt = True
		self.log_area_height = min_log_lines + extra_log_lines
		self.render_log = True
		do_turn = True
		while do_turn:
			if not self.player.alive: do_turn = False
			elif self.arena.whose_turn() == self.player:
				if not self.player_ai.decision:
					self.awaiting_decision = True
					do_turn = False
				if not self.your_turn_announced:
					self.next_player_turn += 1
					put_extra_line = False and self.log.lines and len(self.log.lines[-1].line) > self.safe_term_width and self.log_area_height >= 7
					if put_extra_line:
						self.log.add("", turn=self.next_player_turn, start_new_line=True)
					self.log.add("_", turn=self.next_player_turn, next_sep="", start_new_line=True)
					self.your_turn_announced = True

			# условие в really означает «прокрутить, если сейчас будет сообщение с \n(...) или render()».
			# В противном случае продолжится process и пользователь какое-то время не увидит результат, поэтому скроллить его рано.
			self.log_lines, pending = self.log.scroll(self.log_area_height, self.safe_term_width, really=lambda pending: pending or not do_turn)
			if pending:
				self.disable_prompt_this_time()
				self.render_log = False
				self.invalidate().prompt("\n".join(self.log_lines) + "\n(...)", lambda _input, mode: mode.revert())
				return

			if do_turn:
				if self.arena.whose_turn() == self.player: self.your_turn_announced = False
				self.arena.turn()

		if not self.player.alive:
			self.disable_prompt_this_time()
			if self.game.rel_save_path:
				def handle_answer(input, mode):
					if not input or 'yes'.startswith(input):
						pv = self.session.previews.fn2it[self.game.rel_save_path]
						Game.load_nothrow(pv, self, more_on_success=False, on_fail=lambda mode: mode.then(lambda mode: mode.switch_to(MainMenu())))
					else:
						mode.switch_to(MainMenu())
				after_prompt = lambda input, mode: mode.prompt("Загрузить последнее сохранение? (Y/n) ", handle_answer)
			else:
				after_prompt = lambda input, mode: mode.switch_to(MainMenu())
			self.invalidate().prompt("\n..." + check(self.death_message, "нет сообщения о смерти"), after_prompt)

	def do_render(self, lines, cmds):
		start_lines = len(lines)
		reserve = self.reserve_lines()
		squadA, squadB = tuple(nsmallest(2, self.arena.squads.keys()))
		imA = self.build_squad_image(squadA, None, self.term_height - reserve - self.log_area_height - 1, False)
		imB = self.build_squad_image(squadB, None, self.term_height - reserve - self.log_area_height - 1, True)
		cmds_desc = self.build_commands_desc(cmds) if self.awaiting_decision else []
		cmds_desc_shift = len(imA) + (1 if cmds_desc else 0)

		for lineno in range(max(cmds_desc_shift + len(cmds_desc), len(imB))):
			left = imA[lineno] if lineno < len(imA) else cmds_desc[lineno - cmds_desc_shift] if 0 <= lineno - cmds_desc_shift < len(cmds_desc) else ""
			right = imB[lineno] if lineno < len(imB) else ""

			limit = self.safe_term_width
			if len(left) + len(right) > limit:
				left = left[:limit - len(right)]
				if len(left) + len(right) > limit: impossible(f"Строка не умещается в ширину консоли: {left}/{right}.")
			lines.append(left + " " * (limit - len(left) - len(right)) + right)

		lines_taken = len(lines) - start_lines
		self.start_log_at = min(
			lines_taken + 3 if self.start_log_at is None else self.start_log_at if self.start_log_at > lines_taken else lines_taken + 3,
			self.term_height - reserve - max(len(self.log_lines), self.log_area_height))

		lines.extend("" for _i in range(self.start_log_at - lines_taken))
		# ^ сработает и перед тем more с (...) при переполненном логе
		if self.render_log:
			lines.extend(self.log_lines)
			lines.extend("" for _i in range(self.log_area_height - len(self.log_lines)))

		if self.awaiting_decision:
			def hex_func(cls, fighter):
				def hex(ai):
					exist = next((hex for hex in fighter.hexes if isinstance(hex, cls)), None)
					if exist:
						if cls == Bleeding:
							exist.precise_power += 200
							exist.power = max(1, round(exist.precise_power))
							exist.turns = exist.turns_from_power(exist.power)
						elif cls == RageHex:
							exist.power += 100
							exist.turns += 10
						else: pass
					else:
						if cls == Bleeding: args = (200,)
						elif cls == RageHex: args = (100,)
						else: args = (100,)
						cls(*args).apply(self.player, fighter, arena=self.arena)

					def get_note(sink):
						return "Вы накладываете" + sink.youify("{ на себя/}", fighter) + " " + cls.generic_name() + sink.youify("{/ на F:A}", fighter) + "."
					ai.note(get_note)
				return lambda: self.decide(hex)
			for b in self.arena.battlers:
				cmds.add('bleed' + ('' if b.fighter == self.player else ' ' + b.shortcut), hex_func(Bleeding, b.fighter))
				cmds.add('rage' + ('' if b.fighter == self.player else ' ' + b.shortcut), hex_func(RageHex, b.fighter))
				cmds.add('deathword' + ('' if b.fighter == self.player else ' ' + b.shortcut), hex_func(DeathWordHex, b.fighter))
		cmds.add('quit', lambda: self.quit())

	def min_lines_for_squads(self):
		def get_max_members(squad):
			if squad.max_members is None: impossible(f"У стороны {squad.id} не ограничено число участников.")
			return squad.max_members
		max_members = max(get_max_members(squad) for squad in self.arena.squads.values())
		return max_members * (
			1 + # имя
			2 + # полоски HP/MP
			1)  # новая строка

	def min_action_lines(self):
		return 4

	def min_log_lines(self):
		return 3

	def reserve_lines(self):
		return 5

	def do_handle_command(self, cmd):
		if cmd == '*atb':
			return self.more(self.build_atb_scale())
		elif not cmd:
			if self.awaiting_decision:
				if self.okay_to_skip_turns:
					self.decide_to_skip_turn()
				else:
					question_id = 'skip_turn'
					def confirm_skip_turn(input, mode):
						if self.session.globals.judge_answer(question_id, input) == 0:
							self.okay_to_skip_turns = True
							self.decide_to_skip_turn()
						mode.revert()
					self.prompt("Пропустить ход? ({0}) ".format(self.session.globals.highlight_answer(question_id)), confirm_skip_turn)
			return True
		else:
			return self.game.handle_command(cmd, self)

	def decide(self, what):
		check(self.awaiting_decision, "не вовремя")
		self.player_ai.decide(what)

	def decide_to_skip_turn(self):
		self.decide(lambda ai: ai.fighter.act_skip_turn())

	def quit(self):
		self.game.save_nothrow(self, then=lambda success, mode: mode.switch_to(Respite(self.game)))

	def disable_prompt_this_time(self):
		self.do_prompt, self.last_input = False, ""

	def build_squad_image(self, squad, cmds, lines_limit, flip):
		squad = self.arena.squads[squad]
		class PerBattler:
			def __init__(self, fighter, battler):
				self.fighter, self.battler = fighter, battler
				self.lines = []
				self.hex_descs = []
				self.hexes_gen = iter(fighter.hexes)
		per_battler = []
		total_lines = max(0, len(squad.members) - 1) # пустые строки между описаниями участников

		# Обязательные строки.
		for b in squad.members:
			fighter = b.fighter
			im = PerBattler(fighter, b)
			# (N) Некромант AC:6 EV:10
			im.lines.append(left_to_right(f"({b.shortcut})",
				fighter.name.cap_first(), fighter.ac > 0 and f"AC:{fighter.ac}", fighter.ev > 0 and f"EV:{fighter.ev}", b.game and b.game.marks(), flip=flip))
			total_lines += 1

			if fighter.dead:
				im.lines.append("RIP")
				total_lines += 1
			else:
				im.lines.append(fighter.hp_bar(flip))
				total_lines += 1

				if fighter.has_magic():
					im.lines.append(fighter.mp_bar(flip))
					total_lines += 1
			per_battler.append(im)

		if lines_limit is not None and total_lines > lines_limit: raise RuntimeError(
			"Невозможно уложиться в {0}: {1}.".format(plural(lines_limit, "{N} лини{ю/и/й}"), plural(total_lines, "только неубираем{ая/ых/ых} уже {N}")))

		# Попробовать добавить информацию о хексах, т. е.
		#
		# Некромант (N) AC:6 EV:10
		# HP: [##########] 10/10
		# MP: [##########] 10/10
		# Кровотечение!  7t               <--- вот это
		# Паразит       10t (+1, N?)      <---
		#
		# Если все не поместятся, к последней строке описания добавляется (+количество, сокращение игрока?).

		cur = -1
		while lines_limit is None or total_lines < lines_limit:
			something_changed = False
			for i in range(len(per_battler)):
				cur = (cur + 1) % len(per_battler)
				im = per_battler[cur]
				fighter = im.fighter
				hex = next(im.hexes_gen, None)
				if hex:
					im.hex_descs.append(hex.short_desc(cmd_prefix=self.hex_cmd_prefix(hex, per_battler[i].battler), for_multipad=True, flip=flip))
					total_lines += 1
					something_changed = True
					if lines_limit is not None and total_lines >= lines_limit: break
			if not something_changed: break
		for im in per_battler:
			im.hex_descs = multipad(im.hex_descs)
			if next(im.hexes_gen, None):
				extra = 1 + sum(1 for hex in im.hexes_gen)
				hint = "  (+{extra}, {cmd}?)".format(extra=extra, cmd=im.battler.shortcut)
				if im.hex_descs: im.hex_descs[-1] += hint
				else: im.lines[-1] += hint

		result = [line
			for index, im in enumerate(per_battler)
				for lines in (im.lines, im.hex_descs, None if index + 1 == len(per_battler) else ("",))
					if lines is not None
						for line in lines]
		if len(result) != total_lines: impossible(f"len(result) = {len(result)}, total_lines = {total_lines}")
		return result

	def hex_cmd_prefix(self, hex, victim):
		check(victim, isinstance(victim, Arena.Battler), "victim")
		return "" if victim.fighter == self.player else victim.shortcut + "."

	# Шкала очерёдности хода. В итоге по ней мало что можно понять (и между render()'ами обычно все сделали ход и игрок снова в начале), так что не используется.
	def build_atb_scale(self):
		turn_queue = self.arena.turn_queue
		# Построить первоначальную шкалу.
		max_initiative = max(b.initiative for b in turn_queue)
		if self.atb_maximum is None or self.atb_maximum < max_initiative: self.atb_maximum = max_initiative
		if 0.6 * self.atb_maximum > max_initiative: self.atb_maximum = max(1.1 * max_initiative, self.estimate_good_atb_maximum())
		positions = [int(self.safe_term_width * b.initiative / (self.atb_maximum or 1)) for b in turn_queue]

		# Сдвинуть наложившихся юнитов так, чтобы они не накладывались, а были на шкале через пробел: R N Ne
		for i in range(len(positions) - 1):
			min_next_start = positions[i] + len(turn_queue[i].shortcut) + len(" ")
			if min_next_start > positions[i + 1]: positions[i + 1] = min_next_start

		# Попытаться сделать то же самое с юнитами, залезшими за правый край экрана.
		solve = positions[:]
		max_end = self.safe_term_width
		for i in range(len(solve) - 1, -1, -1):
			if solve[i] + len(turn_queue[i].shortcut) > max_end:
				solve[i] = max_end - len(turn_queue[i].shortcut)
			max_end = solve[i] - len(" ")
		# Пропустить результат, только если после этого никто не вылез за левый край (информация о левых ценнее), иначе оставить как было.
		if solve[0] >= 0: positions = solve
		# Наконец, отрезать торчащих справа (паранойя).
		while positions and positions[len(positions)-1] + len(turn_queue[len(positions)-1].shortcut) > self.safe_term_width: del positions[-1]

		# Теперь можно склеить всё в строку.
		def piece(i):
			if i%2 == 0:
				return (positions[i//2] - (positions[i//2-1] + len(turn_queue[i//2-1].shortcut) if i//2-1 >= 0 else 0)) * " "
			else:
				return turn_queue[i//2].shortcut
		return "".join(piece(i) for i in range(2*len(positions)))

	def estimate_good_atb_maximum(self):
		return 1.2 * self.arena.BASELINE_SPD / max(1, min(b.fighter.spd for b in self.arena.turn_queue))

	def build_commands_desc(self, cmds):
		desc = []
		if self.player.unarmed:
			desc.append("атака врукопашную (hit)")
			def create_hit():
				def hit(ai):
					adv = next(self.arena.enemies(self.player), None)
					if adv: self.player.attack_unarmed(adv, self.arena)
				return lambda: self.decide(hit)
			def create_help():
				help = "Атака голыми руками."
				return lambda: self.more(help)
			cmds.add('hit', create_hit(), '?', create_help())
		return desc

class FixedLevels:
	class One:
		@classmethod
		def create_arena(cls, before=None):
			arena = Arena()
			arena.limit_squad_members(Game.PLAYER_SQUAD, 3)
			arena.limit_squad_members(Game.MONSTER_SQUAD, 3)
			arena.deny_any_new_squads()
			if before: before(arena)
			cls.populate(arena)
			return arena

		@classmethod
		def populate(cls, arena): raise NotImplementedError("populate")

	class TestLevel_Rats(One):
		@classmethod
		def populate(cls, arena):
			rat = Fighter()
			rat.name = Noun.parse("{ручной крыс:a}")
			arena.add(rat, Game.PLAYER_SQUAD, None)

			rat = Fighter()
			rat.name = Noun.parse("{второй ручной крыс:a}")
			arena.add(rat, Game.PLAYER_SQUAD, DummyAI())

			rat = Fighter()
			rat.name = Noun.parse("{обычный крыс:a}")
			rat.add_special(RageOnLowHP())
			arena.add(rat, Game.MONSTER_SQUAD, None)

			rat = Fighter()
			rat.name = Noun.parse("{волшебный крыс:a}")
			with rat.save_relative_vitals():
				rat.base_mmp = 10
			rat.learn_spell(Firestorm())
			arena.add(rat, Game.MONSTER_SQUAD, DummyAI())

	class Level1_CaveRat(One):
		@classmethod
		def populate(cls, arena):
			rat = Fighter()
			rat.name, rat.gender = Noun.parse("{пещерная крыса:af}", return_gender=True)
			with rat.save_relative_vitals():
				rat.base_spd = 120
				rat.base_str = 8
				rat.set_unarmed(Teeth())
				rat.add_special(RageOnLowHP())
			arena.add(rat, Game.MONSTER_SQUAD, MeleeAI(), shortcut_hint="Rat")

	list = (Level1_CaveRat,)

class AskName(Prompt):
	def __init__(self, game, who=None, fixed=None, prefix=""):
		self.game, self.who = game, who or game.player
		prompt = prefix + (
			"Вам нужно зарегистрироваться, прежде чем вас официально освободят.\nКак вас зовут? " if self.who == self.game.player else
			"\nНазовите свой автомат, {0}: ".format(self.game.player.name) if self.who == self.game.player.weapon else
			impossible(self.who, "who"))
		super().__init__(prompt, lambda input, mode: self.handle_name_input(input, mode), casefold_input=False)
		self.fixed = fixed
		self.fixed_name_rejected = False

	def handle_name_input(self, input, mode):
		MIN, MAX = 3, 20
		gender = Gender.UNKNOWN
		fixed_proposed = False
		if not input or MIN <= len(input) <= MAX:
			if input:
				name = cap_first(input) if self.who == self.game.player else input
				if input == name: return self.complete_name(name, gender, mode)
			else:
				if self.who == self.game.player:
					# ну не дёргать же update на каждую has_namesakes_of, лучше уж руками.
					# previews.has_namesakes_of также проверяется в query_random_fixed_name.
					mode.session.previews.update()
					self.fixed = mode.session.globals.recent_fixed_name_proposals < 1 and self.query_random_fixed_name()
					if self.fixed:
						(name, gender), fixed_proposed = self.parse_fixed_player_name(self.fixed), True
						self.session.globals.recent_fixed_name_proposals += 1
					else:
						try:
							name, gender = Noun.random_name(
								ban=lambda type, part: (type, part) in self.session.globals.last_random_name_parts_seen or
									self.session.previews.has_namesakes_of(part, {'adj': 'prefix', 'noun': 'suffix'}[type]),
								see=lambda type, part: self.session.globals.last_random_name_parts_seen.append((type, part)), return_gender=True)
						except Noun.RandomNamesExhausted:
							return mode.more("Случайные имена закончились. Пожалуйста, придумайте своё.")
				elif self.who == self.game.player.weapon:
					if self.fixed and isinstance(self.fixed, tuple) and len(self.fixed) >= 2 and not self.fixed_name_rejected:
						name_src = choose(self.fixed[1]) if isinstance(self.fixed[1], tuple) else self.fixed[1]
						(name, gender), fixed_proposed = Noun.parse(name_src, gender=Gender.MALE, return_gender=True), True
					else:
						name, gender = Noun.parse("{Хуец}" if self.game.player.gender == Gender.FEMALE else "GAU-17", gender=Gender.MALE, return_gender=True)
				else: impossible(self.who, "who")

			def handle_answer(input, mode):
				if not input or 'yes'.startswith(input):
					self.complete_name(name, gender, mode)
				else:
					mode.revert()
					if fixed_proposed: self.fixed_name_rejected = True
			mode.prompt(
				"{0} {1} (Y/n) ".format(
					(f"Очень приятно, {name}." if input else f"Ваше имя — {name}.") if self.who == self.game.player else
					(f"В ваших руках {name}." if input else f"Имя вашего автомата — {name}.") if self.who == self.game.player.weapon else
					impossible(self.who, "who"),
					"Всё верно?" if input else "Продолжить?"), handle_answer)
		elif 'quit'.startswith(input):
			mode.revert()
		else:
			mode.more("{0}. Длина имени должна быть от {1} до {2}, либо \"q\"uit.".format(
				plural(len(input), "Введ{ён/ено/ено} {N} символ{/а/ов}"), MIN, plural(MAX, "{N} символ{/а/ов}")))

	def complete_name(self, name, gender, mode):
		prefix = ""
		# Найти среди предопределённых имён, даже если оно просто введено с клавиатуры.
		if gender == Gender.UNKNOWN and self.who == self.game.player and not isinstance(name, Noun):
			for index, fixed in enumerate(self.fixed_names):
				f_name, f_gender = self.parse_fixed_player_name(fixed)
				if str(f_name) == name:
					if index not in self.session.globals.last_fixed_names_seen: self.session.globals.last_fixed_names_seen.append(index)
					self.fixed, (name, gender) = fixed, (f_name, f_gender)
					prefix = ":3\n"
					break

		if gender == Gender.UNKNOWN and self.who == self.game.player:
			default_gender = Gender.detect(name)
			mode.prompt(prefix + "Вы мальчик или девочка? ({0}/q) ".format(highlight_variant("m/f", default_gender)),
				lambda input, mode: self.handle_gender_answer(input, mode, name, default_gender))
		else:
			self.complete(name, gender, prefix)

	def handle_gender_answer(self, input, mode, name, default_gender):
		check(self.who == self.game.player, "not player?!")
		if not input:                    gender = default_gender
		elif 'male'.startswith(input):   gender = Gender.MALE
		elif 'female'.startswith(input): gender = Gender.FEMALE
		else:                            gender = Gender.UNKNOWN # quit сюда же

		if gender != Gender.UNKNOWN:
			self.complete(name, gender)
		else:
			mode.revert()

	def complete(self, name, gender, prefix=""):
		if not isinstance(check(name, isinstance(name, str), "name"), Noun): name = Noun.guess(name, gender=gender, animate=True)
		self.who.name, self.who.gender = name, gender
		if self.who == self.game.player:
			# В handle_name_input выставляется fixed, т. о. если имя и пол на этот момент соответствуют последней fixed, полагается, что пользователь согласился.
			# Если бы не последующие запросы, опирающиеся на fixed с первого шага, было бы проще занулить fixed в начале handle_name_input.
			fixed = self.fixed and (name, gender) == self.parse_fixed_player_name(self.fixed) and self.fixed
			self.session.switch_to(AskName(self.game, self.game.player.weapon, fixed=fixed, prefix=prefix))
		elif self.who == self.game.player.weapon:
			self.game.save_nothrow(self, then=lambda success, mode: mode.switch_to(Respite(self.game)))
		else:
			impossible(self.who, "who")

	fixed_names = \
	(
		("{Рика:f}", "<photon eraser>"),
		("{Мадока:f}", ("{Розочка:f}",)),
		("{Фрисия:f}", "{Хвост}"),
	)

	def query_random_fixed_name(self):
		seen, previews = self.session.globals.last_fixed_names_seen, self.session.previews
		get_name_weight = lambda name, index: 0.0 if index in seen or previews.has_namesakes_of(Noun.parse(name[0] if isinstance(name, tuple) else name)) else 1.0
		name, index = choose(AskName.fixed_names, get_name_weight, None, return_index=True)
		if index >= 0:
			seen.append(index)
			return name

	def parse_fixed_player_name(self, fixed):
		return Noun.parse(fixed[0] if isinstance(fixed, tuple) else fixed, animate=True, gender=Gender.MALE, return_gender=True)

# Ввод-вывод, стек экранов, глобальности.
class Session:
	__slots__ = ('mode', 'quit_posted', 'cls_once_requested', 'term_width', 'term_height', 'safe_term_width', 'previews', 'globals')
	def __init__(self, start=None):
		self.mode               = None
		self.quit_posted        = False
		self.cls_once_requested = False
		self.term_width = self.term_height = self.safe_term_width = None
		self.previews           = Session.PreviewsList()
		self.globals            = Session.Globals()
		self.switch_to(start or MainMenu())

	def switch_to(self, new_mode, reverting=False):
		check(isinstance(new_mode.prev_mode, bool) or new_mode == self.mode.prev_mode, "prev_mode?!")
		if reverting:
			self.mode.deactivate()
		# запомнить prev_mode при условии, что а) это явно требуется (prev_mode = True) и б) это не возврат к prev_mode (проверено по reverting)
		elif new_mode.prev_mode:
			new_mode.prev_mode = self.mode
		else:
			# НЕ reverting и НЕ запоминаются предыдущие режимы: деактивировать их все.
			mode = self.mode
			while mode:
				mode.deactivate()
				mode = mode.prev_mode
		self.mode = new_mode
		self.mode.session = self
		if not reverting: self.mode.activate()
		self.mode.invalidated = False

	def revert(self, n=1):
		check(n > 0, "n?!")
		mode = self.mode
		while n > 0:
			mode = check(mode.prev_mode, isinstance(mode.prev_mode, Mode), "prev_mode?!")
			n -= 1
			self.switch_to(mode, reverting=True)
		return self.cls_once()

	def process(self):
		cmds = Commands()
		self.term_width, self.term_height = os.get_terminal_size()
		self.safe_term_width = Con.safe_width(self.term_width)
		self.check_term_size()
		while True:
			mode = self.mode
			self.mode.process()
			if mode == self.mode: break

		lines = []
		if self.cls_once_requested: self.render_prev_modes(lines)
		start_line = len(lines)
		mode.render(lines, cmds)
		mode.last_screen = "\n".join(lines[start_line:])
		screen = "\n".join(lines)

		# вся эта движуха с lines — раньше render() без задней мысли выводил всё print'ами —
		# нужна была для того, чтобы минимизировать время между cls и рисованием нового «экрана».
		# Можно было бы сделать двойную буферизацию, если бы был кроссплатформенный способ перемещать курсор в консоли...
		# (TODO: сделать её опционально. У меня нет Linux, чтобы тестировать как-их-там-спецпоследовательности / curses, но на Windows есть SetConsoleCursorPosition.)
		if mode.do_cls or self.cls_once_requested: cls()
		print(screen, end='')
		self.cls_once_requested = False

		has_default_commands = cmds.has_anything()
		if has_default_commands: self.add_default_commands(cmds)
		try:
			cmd = input()
			mode.last_input = cmd
		except (KeyboardInterrupt, EOFError) as e:
			self.post_quit()
			if isinstance(e, KeyboardInterrupt): print()
			return

		fn, matches, suggestions = cmds.guess(cmd)
		if fn: fn()
		elif mode.handle_command(cmd): pass
		elif matches: mode.more("Неоднозначная команда: {0}.".format(", ".join(matches)))
		elif suggestions: mode.more("Неизвестная команда. Попробуйте {0}.".format(", ".join(suggestions)))
		elif cmd and not cmd.isspace(): mode.more("Неизвестная команда." + (" Попробуйте \"?\"." if has_default_commands else ""))
		return not self.quit_posted

	def post_quit(self):
		self.quit_posted = True

	def check_term_size(self):
		min_term_width, min_term_height = 80, 25
		if self.term_width < min_term_width or self.term_height < min_term_height:
			self.mode.more(
				f"Размер консоли — {self.term_width}x{self.term_height}.\n"\
				f"Увеличьте хотя бы до {min_term_width}x{min_term_height}.", do_cls=True)

	def add_default_commands(self, cmds):
		cmds.add("?", lambda: self.mode.more(Session.list_available_commands(cmds)))

	@staticmethod
	def list_available_commands(cmds):
		av = ", ".join(cmd for cmd in cmds.suggest_something() if cmd != "?")
		return "Доступные команды: " + av + "." if av else "Нет доступных команд."

	def cls_once(self):
		self.cls_once_requested = True
		return self.mode

	# Чтобы, например, вложенные more-сообщения корректно убирались, оставляя предыдущие,
	# экран очищается и всё, что на нём должно было быть — перерисовывается.
	def render_prev_modes(self, lines):
		chain, mode = [], self.mode
		while mode:
			if mode != self.mode:
				chain.append(mode)
				if mode.invalidated:
					L = []
					mode.render(L, DummyCommands())
					mode.last_screen = "\n".join(L)
					mode.invalidated = False
			if mode.do_cls: break
			mode = mode.prev_mode
		lines.extend(mode.last_screen + mode.last_input for mode in reversed(chain))

	# Список всех сохранений.
	# Хранится в session (и вообще нужен) для того, чтобы не перечитывать их на каждый чих, такой как генерация нового order_key
	# (и, наоборот, обновлять при необходимости).
	# Если пользователь не будет хулиганить в папке save, каждое сохранение прочитается максимум по одному разу за сеанс,
	# поскольку Game.save и подобные методы дружат со списком и уведомляют его об изменениях.
	# Изменения в случае хулиганства (и в первый раз) обнаруживаются по os.walk(), так что механизм можно обмануть;
	# но максимум, что это собьёт — уникальность order_key и данные на экране загрузки.
	class PreviewsList:
		# Можно было бы засунуть поля в Preview и хранить сразу Preview, но там и так много всего.
		class Item:
			def __init__(self, full_save_path, rel_save_path):
				self.preview   = None # элементы PreviewsList.items имеют взаимоисключающе выставленные preview либо bad
				self.bad       = None # непустой список экземпляров исключений, если с сохранением проблемсы
				self.index     = None # индекс себя в items
				self.confirmed = None
				self.full_save_path = full_save_path
				self.rel_save_path = rel_save_path # = ключу fn2it
				self.namesake_index = None # приписывать -2, -3, etc. для одинаковых имён разных персонажей
				self.seen      = False

			def load_screen_desc(self, npad=0, first_line_extra=None, display_order_key=False):
				star = "" if self.seen else "*NEW* "
				pad = ' ' * (npad + len(star))
				if self.bad:
					lines = [line for e in self.bad for line in exception_msg(e).splitlines()]
					if not any(isinstance(e, Game.BadSaveError) for e in self.bad) and not any('оврежд' in line or 'orrupt' in line for line in lines):
						lines.insert(0, "Файл повреждён.")
					if first_line_extra: lines[0] += first_line_extra
					return "{star}{0}\n{pad}[{1}]".format(("\n" + pad).join(lines), self.full_save_path, pad=pad, star=star)
				else:
					pv = self.preview
					dup_desc = f"-{1+self.namesake_index}" if self.namesake_index >= 1 else ""
					return ("{star}{okey}{ts}{fle}\n" +
						"{pad}{pn}{dd} {pl}\n" +
						"{pad}{wn} {wl}\n" +
						"{pad}{gm}D:{coming} ${gold}").format(
							ts = '{}{}{}'.format(
								strftime('%d ', pv.timestamp).lstrip('0'),
								strftime('%B ', pv.timestamp).lower().replace('ь ', 'я ').replace('т ', 'та ').replace('й ', 'я '),
								strftime('%Y, %H:%M:%S', pv.timestamp)),
							fle = first_line_extra or "",
							pn = cap_first(pv.player_name), dd = dup_desc, pl = Living.xl_desc(pv.player_level, pv.player_next, short=True),
							wn = cap_first(pv.weapon_name), wl = Living.xl_desc(pv.weapon_level, pv.weapon_next, short=True),
							coming = pv.next_level, gold = pv.gold, gm = Game.marks(pv, rspace=True),
							pad = pad, star = star, okey = f"[order_key = {pv.order_key}] " if display_order_key else "")

			def load_screen_desc_lines(self):
				return 4 if self.preview else sum(len(exception_msg(e).splitlines()) + 2 for e in self.bad)

		__slots__= ('items', 'fn2it', 'max_order_key', 'last_listing', 'first_update')
		def __init__(self):
			self.items = self.fn2it = self.max_order_key = self.last_listing = self.first_update = None
			self.post_force_update()

		def post_force_update(self, silent=True):
			self.items  = []
			self.fn2it  = {} # ключ — имя файла относительно SAVE_FOLDER, значение — Item.
			self.max_order_key = -1
			self.last_listing = [] # содержимое SAVE_FOLDER в последний раз.
			self.first_update = silent # при silent: seen будет выставлена всем сохранениям, загруженным по post_force_update
			                           # (в т. ч. первый раз после создания PreviewsList), чтобы им не рисовались звёздочки

		# Обнаружить изменения в папке сохранений, или загрузить всё в первый раз.
		# Возвращает (число новых, число удалённых) НЕУЧТЁННЫХ ЧЕРЕЗ NOTE_ с последнего update (для отладки) или None вместо (0, 0)
		def update(self):
			listing = []
			with suppress(StopIteration):
				# walk: folder ⇒ dirpath, dirnames, filenames
				listing.extend(fn for fn in next(os.walk(Game.SAVE_FOLDER))[2] if fn.endswith(Game.SAVE_SUFFIX))
			listing.sort() # os.walk выдаёт произвольный порядок, для сравнений нужно сделать не произвольный
			if listing == self.last_listing: # LIKELY
				return

			assert self.sanitycheck()
			first_update, self.first_update = self.first_update, False
			# Добавить новые превью, удалить старые. Порядок и индексы собьются и будут исправлены позже одним махом
			# (чтобы на десяти тысячах сохранений не подвеситься на вставках в отсортированный список :))).
			appeared, missing = [], 0
			for item in self.items:
				item.confirmed = False # not confirmed будут вычеркнуты как более не существующие в папке

			for rel_path in listing:
				item = self.fn2it.get(rel_path, None)
				if item:
					# Файл существовал — чтобы не лезть совсем в дебри, предположим, что он не изменился.
					item.confirmed = True
				else:
					# Обнаружено новое превью. Загружаем!~
					item = Session.PreviewsList.Item(os.path.join(Game.SAVE_FOLDER, rel_path), rel_path)
					try:
						with open(item.full_save_path, 'rb') as f:
							item.preview = Game.load_preview(f)
					except Exception as e:
						self.force_bad(item, e)
					appeared.append(item)

			# Пройтись по items: удалить неподтверждённые (также из fn2it), упаковать подтверждённые по освободившимся местам...
			next_item = 0 # последний свободный слот items
			for item in self.items:
				if item.confirmed:
					self.items[next_item] = item
					next_item += 1
				else:
					missing += 1
					del self.fn2it[item.rel_save_path]

			# ...добавить новые...
			for item in appeared:
				item.seen = first_update
				if next_item < len(self.items): # новые вставляются в хвост, оставшийся от удалённых, пока возможно
					self.items[next_item] = item
				else:
					self.items.append(item)
				self.fn2it[item.rel_save_path] = item
				next_item += 1
			assert next_item <= len(self.items)
			del self.items[next_item:] # отрезать пустой хвост; если он был исчерпан, то next_item == len(items) и это no-op

			# ...заново отсортировать всё и выставить правильные индексы.
			# Более новые сохранения (с большим order_key) наверху; все повреждённые — в конце, т. е. их order_key полагается меньше всех остальных.
			self.items.sort(key=lambda item: -1 if item.bad else item.preview.order_key, reverse=True)
			self.fix_indices()

			# слишком много всего могло инвалидировать max_order_key, так что проще пересчитать его безусловно
			self.max_order_key = self.calculate_max_order_key()

			# различить на экране загрузки разных персонажей с одинаковыми именами
			self.update_namesakes()

			# последний штрих: запомнить состояние SAVE_FOLDER, под которое список подгонялся.
			self.last_listing = listing
			assert self.sanitycheck()
			return (len(appeared), missing) if (appeared or missing) and not first_update else None

		def note_add(self, full_save_path, rel_save_path, preview):
			assert self.sanitycheck()
			check(full_save_path, "full_save_path?!", rel_save_path, "rel_save_path?!")
			check(full_save_path, full_save_path.startswith(Game.SAVE_FOLDER), "абсолютный плес")
			check(rel_save_path, not rel_save_path.startswith(Game.SAVE_FOLDER) and full_save_path.endswith(rel_save_path), "относительный плес")
			if rel_save_path in self.fn2it: impossible("сохранение {0} уже существует, исп. note_update".format(rel_save_path)) # ух, паранойя замучила

			item = Session.PreviewsList.Item(full_save_path, rel_save_path)
			item.preview = preview
			item.index = self.find_position_for(item)
			item.seen = True

			self.items.insert(item.index, item)
			self.fix_indices(item.index + 1)
			self.fn2it[rel_save_path] = item
			insort_right(self.last_listing, rel_save_path)

			self.max_order_key = max(self.max_order_key, preview.order_key)
			self.update_namesakes(of=item.preview.player_name)
			assert self.sanitycheck()

		def note_update(self, rel_save_path, preview, new_full_save_path=None, new_rel_save_path=None):
			assert self.sanitycheck()
			item = self.fn2it[rel_save_path]
			assert item.rel_save_path == rel_save_path
			if new_rel_save_path is not None:
				assert new_full_save_path is not None
				assert new_rel_save_path not in self.fn2it, "сохранение {0} уже существует".format(new_rel_save_path)
				item.full_save_path, item.rel_save_path = new_full_save_path, new_rel_save_path

				del self.fn2it[rel_save_path]
				self.fn2it[new_rel_save_path] = item

				del self.last_listing[self.last_listing_index(rel_save_path)]
				insort_right(self.last_listing, new_rel_save_path)
			item.preview, item.bad = preview, None
			assert self.sanitycheck()

		def note_remove(self, item):
			assert self.sanitycheck()
			check(item, isinstance(item, (str, Session.PreviewsList.Item)), "item?!")
			if isinstance(item, str): item = self.fn2it[item]
			assert item is self.items[item.index], "сбился индекс"
			del self.fn2it[item.rel_save_path]
			del self.items[item.index]
			self.fix_indices(item.index)
			del self.last_listing[self.last_listing_index(item.rel_save_path)]
			if item.preview: self.bookkeep_removed_preview(item.preview)
			assert self.sanitycheck()

		def calculate_max_order_key(self):
			return max((item.preview.order_key for item in self.items if item.preview), default=-1)

		def fix_indices(self, start=0, end=None):
			for index in range(start, end if end is not None else len(self.items)):
				self.items[index].index = index

		def update_namesakes(self, of=None):
			def autoincrementing_dict(): d = defaultdict(lambda: len(d)); return d
			name_to_uid_to_namesake_index = defaultdict(lambda: autoincrementing_dict())

			for item in reversed(self.items):
				if item.preview and (of is None or item.preview.player_name == of):
					item.namesake_index = name_to_uid_to_namesake_index[item.preview.player_name][item.preview.character_uid]

		def choose_order_key(self, rel_save_path=None):
			if not rel_save_path: self.update()
			return self.fn2it[rel_save_path].preview.order_key if rel_save_path else self.max_order_key + 1

		def last_listing_index(self, rel_save_path):
			index = bisect_left(self.last_listing, rel_save_path)
			assert self.last_listing[index] == rel_save_path
			return index

		def force_bad(self, item, e):
			if not item.bad: item.bad = []
			item.bad.append(e)
			old_preview, item.preview = item.preview, None
			if item.index is not None:
				old_index = item.index
				assert self.items[item.index] is item
				del self.items[item.index]
				item.index = self.find_position_for(item)
				self.items.insert(item.index, item)
				self.fix_indices(*(item.index + 1, old_index + 1) if item.index < old_index else (old_index, item.index))
				assert self.sanitycheck()
			if old_preview: self.bookkeep_removed_preview(old_preview)

		def find_position_for(self, item):
			return bisect_left(self.items, item, key=lambda item: -(item.preview.order_key if item.preview else -1))

		def has_namesakes_of(self, name, mode='full'): # это очень медленно...
			name = name.casefold()
			hit = (lambda playername: playername == name) if mode == 'full' else \
				(lambda playername: playername.startswith(name)) if mode == 'prefix' else \
				(lambda playername: playername.endswith(name)) if mode == 'suffix' else throw(ValueError, f"Неверный mode: {mode}")
			return any(item.preview and hit(item.preview.player_name.casefold()) for item in self.items)

		def bookkeep_removed_preview(self, pv):
			if pv.order_key == self.max_order_key: self.max_order_key = self.calculate_max_order_key()
			self.update_namesakes(of=pv.player_name)

		# Этот класс ещё никогда не глючил, но он сложно устроен и я боюсь.
		def sanitycheck(self):
			assert len(self.items) == len(self.fn2it) == len(self.last_listing) and \
				set(item.rel_save_path for item in self.items) == \
				set(self.fn2it.keys()) == \
				set(self.last_listing) and \
				all(item.index == i for i, item in enumerate(self.items)), self.debug_repr()
			return True

		def debug_repr(self):
			def item_repr(item):
				pv = item.preview
				return "{0.index} {0.rel_save_path} ({1})".format(item, f"order_key = {pv.order_key}" if pv else "BAD" if item.bad else "???")

			return "\n\n".join(part for part in (
				"items ({0}):\n".format(len(self.items)) +
				"\n".join(item_repr(item) for item in self.items),
				"fn2it ({0}):\n".format(len(self.fn2it)) +
				"\n".join("{0}{1}".format(fn, " -> {0}".format(item.rel_save_path) if item.rel_save_path != fn else " (OK)") for fn, item in self.fn2it.items()),
				"last_listing ({0}):\n".format(len(self.last_listing)) +
				"\n".join(self.last_listing)))

	class Globals:
		def __init__(self):
			self.recent_fixed_name_proposals = 0
			self.last_fixed_names_seen       = deque(maxlen=(len(AskName.fixed_names) + 1) // 2)
			self.last_random_name_parts_seen = deque(maxlen=24)
			self.last_answers = {}

		def highlight_answer(self, id, pattern="y/n", default=1):
			last_answer = self.last_answers.get(id, None)
			return highlight_variant(pattern, last_answer if last_answer is not None else default)

		def judge_answer(self, id, input, default=1):
			answer = (0 if 'yes'.startswith(input) else 1) if input else self.last_answers.get(id, default)
			self.last_answers[id] = answer
			return answer

def parse_cmdline():
	ap = argparse.ArgumentParser()
	ap.add_argument('--test', action='store_true', dest='verbose_tests', help='verbose tests')
	return ap.parse_args()

def selftest(verbose):
	poop = io.StringIO()
	stats = TextTestRunner(stream=poop, verbosity=2 if verbose else 0, tb_locals=True).run(
		TestSuite(defaultTestLoader.loadTestsFromTestCase(value) for name, value in globals().items()
			if isinstance(value, type) and issubclass(value, TestCase) and value is not TestCase))

	if verbose or not stats.wasSuccessful():
		print(poop.getvalue().rstrip(), end='')
		input()
		if not stats.wasSuccessful(): exit()

def main():
	locale.setlocale(locale.LC_ALL, '') # чтобы даты по-русски печатались :|
	selftest(parse_cmdline().verbose_tests)
	session = Session()
	while session.process(): pass

if __name__ == "__main__": main()