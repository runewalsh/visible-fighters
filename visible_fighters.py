import sys, os, string, tempfile, pickle, pickletools, lzma, textwrap, math, time, enum, base64, heapq
from traceback import format_exc
from collections import namedtuple, OrderedDict, defaultdict, deque
from bisect import bisect_left, bisect_right, insort_right
from random import random, randrange, uniform
version, save_version = (0, 2), 0

class config:
	min_term_width, min_term_height = 80, 25

# FORMAT_RAW не хранит эти настройки в сжатом потоке, поэтому для распаковки нужно указать те же, которыми упаковывались.
LZMA_OPTIONS = {"format": lzma.FORMAT_RAW, "filters": [{"id": lzma.FILTER_LZMA2, "preset": lzma.PRESET_DEFAULT}]}

# для default-параметров, где допустимо None
sentinel = object()

def impossible(*args):
	if len(args) <= 1: raise AssertionError("Внутренняя ошибка" + (f": {args[0]}" if len(args) > 0 else "") + ".")
	elif len(args) == 2:
		what, desc = args[0], args[1]
		try:    what = f" ({what})"
		except: what = ""
		impossible(desc + what)
	else: raise TypeError(f"impossible: ожидаются 1 (сообщение) или 2 (значение + сообщение) аргумента, получено {len(args)}.")

# 1. check(what, cond, errmsg)
# Возвращает what, если всё хорошо (cond), иначе возбуждает impossible.
# Короче, assert с возвращаемым значением, чтобы всё в одну строку ебашить))0.
# Например: hp = check(new_hp, new_hp > 0, "недопустимое значение hp").
#
# 2. check(условие 1, impossible при невыполнении условия 1, ...)
def check(*args):
	if len(args) == 3:
		what, cond, errmsg = args[0], args[1], args[2]
		return what if cond else impossible(what, errmsg)
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
# left_to_right("HP", "######....", "6/10")            = "HP [######....] 6/10"
# left_to_right("HP", "....######", "6/10", flip=True) = "6/10 [....######] HP"
def left_to_right(*what, sep=" ", flip=False):
	def pieces():
		yield from (piece for piece in (reversed(what) if flip else what) if piece)
	return sep.join(pieces())

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
		result = base64.b85encode(lzma.compress(src.encode(encoding), **LZMA_OPTIONS)).decode('ascii')
		return maybewrite(outfile, pretty_decl(result, **prettyargs) if pretty else result)

	# Распаковывает результат pack_str, опционально в файл.
	def unpack_str(src, encoding='koi8-r', *, outfile=None):
		return maybewrite(outfile, ''.join(lzma.decompress(base64.b85decode(src), **LZMA_OPTIONS).decode(encoding)))
	return pack_str, unpack_str
pack_str, unpack_str = makefuncs(); del makefuncs

# Красивенько форматирует строку (предположительно длинную, предположительно результат pack_str) в питонье объявление.
# длина ограничивается width с учётом prefix, pad и кавычек; символы НЕ эскейпаются, поэтому при '\ в строке результат будет не валиден.
def pretty_decl(s, width=160, prefix="", pad="\t", cont_pad=None, multiline=False):
	if width < 1: raise ValueError("width должна быть >= 1")
	if cont_pad is None: cont_pad = "" if multiline else pad
	def pieces_gen():
		sp = 0
		start = pad + prefix
		opening_quotes = ending_quotes = '"""' if multiline else '"'
		cont_opening_quotes = cont_ending_quotes = ("" if multiline else '"')
		if len(start) + len(opening_quotes) >= width: yield start + "\\"; start = cont_pad
		start += opening_quotes
		if multiline and len(start) + len('\\') >= width: yield start + "\\"; start = cont_pad

		while True:
			if len(s) - sp <= max(0, width - len(start) - len(ending_quotes)): yield start + s[sp:] + ending_quotes; return
			take = max(1, width - (len(start) + len(cont_ending_quotes) + len('\\')))
			yield start + s[sp:sp+take] + cont_ending_quotes + '\\'; sp += take
			start = cont_pad + cont_opening_quotes
	return "\n".join(pieces_gen())

# Выбирает взвешенно-случайный элемент итерируемой последовательности, т. е. не требует len (в отличие от random.choice).
# «King of the hill» отсюда: https://eli.thegreenplace.net/2010/01/22/weighted-random-generation-in-python.
def choose(iterable, get_weight=lambda item, index: 1, default=sentinel):
	best, best_index, sum = default, -1, 0
	for index, item in enumerate(iterable):
		w = get_weight(item, index)
		if w > 0: # там внизу <= на случай uniform(a, b)==b, поэтому нужно явно отбросить элементы с нулевыми весами
			sum += w
			if uniform(0, sum) <= w: best, best_index = item, index
	if best is not sentinel: return best, best_index
	raise IndexError("Ничего не выбрано.")

# common_prefix_len("привет", "прийти") = 3
def common_prefix_len(a, b):
	n = 0
	while n < len(a) and n < len(b) and a[n]==b[n]: n += 1
	return n

# длина наибольшей общей подпоследовательности (https://en.wikipedia.org/wiki/Longest_common_subsequence_problem)
# например, lcs_len("гвозди", "вонзить") == 4 ("вози")
def lcs_len(aseq, bseq):
	LP = [0] * (1 + len(bseq))
	L  = [0] * (1 + len(bseq))
	for ia in range(1, 1 + len(aseq)):
		for ib in range(1, 1 + len(bseq)):
			L[ib] = LP[ib-1] + 1 if aseq[ia-1] == bseq[ib-1] else LP[ib] if LP[ib] >= L[ib-1] else L[ib-1]
		LP, L = L, LP
	return LP[len(bseq)]

# модификация lcs_len, возвращающая максимальную «оценку» среди общих подпоследовательностей
# lcs_len — частный случай lcs_score с оценкой 1 при равенстве элементов и 0 при неравенстве
# например:
# lcs_score(["раз", "blah", "два", "три"], ["раскол", "дворец", "nah", "триста"], lambda a, _ia, b, _ib: common_prefix_len(a, b)) =
# = 7 ("ра" + "дв" + "три")
def lcs_score(aseq, bseq, scoref):
	LP = [0] * (1 + len(bseq))
	L  = [0] * (1 + len(bseq))
	for ia in range(1, 1 + len(aseq)):
		for ib in range(1, 1 + len(bseq)):
			L[ib] = max(LP[ib-1] + scoref(aseq[ia-1], ia-1, bseq[ib-1], ib-1), LP[ib], L[ib-1])
		LP, L = L, LP
	return LP[len(bseq)]

# subseq_occurences генерирует все вхождения подпоследовательности ss в src
# Например: subseq_occurences("AB", "AABB") → [0, 2], [0, 3], [1, 2], [1, 3]
#                                    0123
# Внимание: для оптимизации возвращаемый список переиспользуется, его нельзя хранить, не скопировав.
def subseq_occurences(ss, src):
	p = [0] * len(ss)
	def reset(start):
		for i in range(start, len(ss)):
			p[i] = src.find(ss[i], (p[i-1]+1) if i > 0 else 0)
			if p[i] < 0: return False
		return True
	digits, digit = range(len(ss)-1, -1, -1), -1

	while reset(digit+1): # после for ниже предполагается, что digit будет тем, на котором брейкнулись — в Python это гарантируется
		yield p
		for digit in digits:
			p[digit] = src.find(ss[digit], p[digit]+1)
			if p[digit] >= 0: break
		else: return

# Наивный байесовский классификатор, украденный из https://habrahabr.ru/post/120194/.
# guess возвращает (1) наиболее вероятный класс и (2) отрыв от предыдущего, приведённый к [0; 1] (или None, None — пока такого не будет, но завтра...).
# Например, пусть он угадывает пол по первой и двум последним буквам имени:
#
# guesser = BayesianGuesser(lambda name: ('0:'+name[0], '-2:'+name[-2], '-1:'+name[-1]))
# guesser.train({'Петя': 'M', 'Коля': 'M', 'Вера': 'F', ...})
# cls, margin = guesser.guess('Витя')
#
# Как учитывать margin — решать пользователю. Можно подобрать эмпирическое правило вроде
# if margin > 0.4: (воспользоваться результатом) else: (придумать что-то другое).
#
# Коллбэк, передаваемый в конструктор, должен извлекать из классифицируемого объекта значащие признаки —
# то, что нейросеть делала бы автоматически... но не тянуть же её для такой ерунды хд, даже то, что есть, перебор.
# А вообще всё это из рук вон плохо работает, ну да ладно. В качестве моральной компенсации добавил читерскую проверку на точные совпадения.
class BayesianGuesser:
	# Чтобы можно было передавать в samples как словарь, так и список пар.
	def pairs(self, samples): return samples.items() if isinstance(samples, dict) else samples

	def __init__(self, get_feats, samples=None, cheat=True):
		self.get_feats      = get_feats
		self.total_samples  = 0
		self.total_of_class = defaultdict(lambda: 0)
		self.total_of_cfeat = defaultdict(lambda: 0)
		self.cheat          = {} if cheat else None
		if samples: self.train(samples)

	def train(self, samples):
		for sample, cls in self.pairs(samples):
			if self.cheat is not None:
				check(sample, sample not in self.cheat, "уже было") # хотя так-то есть смысл... можно вообще к сэмплам развесовки давать
				self.cheat[sample] = cls

			self.total_of_class[cls] += 1
			for feat in filter(None, self.get_feats(sample)):
				self.total_of_cfeat[cls, feat] += 1
			self.total_samples += 1

	# cfeat_prob — это P(wi|c) из статьи http://bazhenov.me/blog/2012/06/11/naive-bayes.html.
	# По ней же добавил сглаживание Лапласа (в Хабро-варианте вместо него использовалась константа 1e-7).
	# Внимание, я не уверен, действительно ли в знаменателе в качестве множителя должна быть feats_count, а не что-то ещё.
	# Формула сглаживания отсюда: https://en.wikipedia.org/wiki/Additive_smoothing.
	SMOOTH = 1.0
	def cfeat_prob(self, cls, feat, feats_count):
		return (self.total_of_cfeat[cls, feat] + self.SMOOTH) / (self.total_of_class[cls] + self.SMOOTH * feats_count)

	def guess(self, sample):
		if not self.total_samples: raise ValueError("Нет образцов!")
		if self.cheat:
			precise = self.cheat.get(sample, None)
			if precise is not None: return precise, 1.0 # можно брать и этим весь класс заменять...

		feats = self.get_feats(sample)
		n_feats = sum(1 for feat in feats if feat)
		best_cls = best_prob = second_best_prob = None

		for cls, count in self.total_of_class.items():
			# Pc для каждого класса можно посчитать один раз после тренировки (classes[cls] в хабро-варианте), но и так сойдёт
			Pc = count / self.total_samples
			prob = math.log(Pc) + sum(math.log(self.cfeat_prob(cls, feat, n_feats)) for feat in feats if feat)

			if not best_prob or prob > best_prob:
				best_cls, best_prob, second_best_prob = cls, prob, best_prob
			elif not second_best_prob or prob > second_best_prob:
				second_best_prob = prob

		check(best_cls, best_cls is not None, "best_cls?!")
		return best_cls, 1.0 - math.exp(second_best_prob - best_prob) if second_best_prob else 1.0

	# оценивает точность классификации на тестовой выборке
	def success_rate(self, samples):
		success = total = 0
		for sample, ref_cls in self.pairs(samples):
			if self.guess(sample)[0] == ref_cls: success += 1
			total += 1
		return success / max(1, total)

	# статистика по наиболее информативным признакам, как в http://www.nltk.org/_modules/nltk/classify/naivebayes.html
	# возвращает список 3-тюплов (feat, cls, margin), например, (feat = "LAST_TWO_LETTERS:на", cls = Gender.FEMALE, margin = 12.5)
	# (margin∈[1; +∞] — разрыв с наименее вероятным по feat. Возможно, больше смысла возвращать, наоборот, отрыв от второго самого вероятного, как в guess.
	#
	# Была бы полезнее функция most_informative_fnames, которая бы указывала, какие *категории* признаков
	# были самыми полезными, а какие только мешали (возможно, в связке с success_rate), но я не знаю, как это сделать :(
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
			f.min_prob = min(f.min_prob, cf_prob)
			if cf_prob > f.max_prob: f.max_prob, f.max_prob_class = cf_prob, cls

		result_gen = (informative_feat(feat, f.max_prob_class, f.max_prob/f.min_prob) for feat, f in feats.items() if f.occurences > 1)
		key = lambda f: f.margin
		return sorted(result_gen, key=key, reverse=True) if n is None else heapq.nlargest(n, result_gen, key=key)

class Gender(enum.IntEnum):
	UNKNOWN, MALE, FEMALE, NEUTER, TOTAL = -1, 0, 1, 2, 3

	@staticmethod
	def detect(name):
		# С L2-L3 бессовестно нарушается предположение о независимости признаков, но результат вроде лучше, кхехех.
		oracle = BayesianGuesser(lambda w: (('F2', w[0:2]), ('L2', w[-2:]), ('L3', w[-3:])),
			samples = {sample: gender
				for samples_pack, gender in ((Gender.male_names_pack(), Gender.MALE), (Gender.female_names_pack(), Gender.FEMALE))
				for sample in unpack_str(samples_pack).split()})

		best_guess, best_margin = Gender.UNKNOWN, None
		for _lit, word in Noun.split_into_words(name):
			guess, margin = oracle.guess(word.casefold())
			if guess is not None and (best_margin is None or margin > best_margin) and margin > 0.4:
				best_guess, best_margin = guess, margin

		return best_guess

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

class Case:
	NOMINATIVE, GENITIVE, DATIVE, ACCUSATIVE, INSTRUMENTAL, PREPOSITIONAL, TOTAL = 0, 1, 2, 3, 4, 5, 6

# Noun.parse("маленьк{ий/ого/ому/ий/им/ом} член{/а/у//ом/е}")(Case.GENITIVE) == Noun.guess("маленький член")(Case.GENITIVE) == "маленького члена"
# Noun("{кусок} угля")(Case.PREPOSITIONAL) == "куском угля"
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
		return "".join(piece for literal, cases in self.pieces for piece in (literal, cases[case] if cases else ""))

	def __eq__(self, other):
		return isinstance(other, self.__class__) and self.pieces == other.pieces

	@staticmethod
	def append_pair(pieces, literal, cases): # ненужная оптимизация, чтобы не бить строку в месте, где guess_one так ничего и не придумала
		if pieces and not pieces[-1][1]:
			pieces[-1] = pieces[-1][0] + literal, cases
		else:
			pieces.append((literal, cases))

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
		for literal, word in Noun.split_into_words(src):
			base, cases = Noun.guess_one(word, animate, gender)
			Noun.append_pair(pieces, literal + base, cases)

	# мне очень влом тестировать все ветки, хотя надо бы
	@staticmethod
	def guess_one(word, animate, gender):
		def ngdip(nom, gen, dat, ins, pre): return (nom, gen, dat, gen if animate else nom, ins, pre)
		def yi(prev): return 'ы' if prev in 'бвдзлмнпрстфц' else 'и'
		def oe(prev): return 'е' if prev in 'нр' else 'о'
		vowels = 'аеёиоуыэюя'
		if word.endswith('ый') and (gender == Gender.UNKNOWN or gender == Gender.MALE):
			return word[:-len('ый')], ngdip('ый', 'ого', 'ому', 'ым', 'ом')
		elif word.endswith('ий') and not word[1].isupper and (gender == Gender.UNKNOWN or gender == Gender.MALE):
			return word[:-len('ий')], ngdip('ий', oe(word[-3:-2]) + 'го', oe(word[-3:-2]) + 'му', 'им', oe(word[-3:-2]) + 'м')
		elif word.endswith('ой') and (gender == Gender.UNKNOWN or gender == Gender.MALE):
			return word[:-len('ой')], ngdip('ой', 'ого', 'ому', yi(word[-3:-2])+'м', 'ом')
		elif word.endswith('ая') and not word[1].isupper and (gender == Gender.UNKNOWN or gender == Gender.FEMALE):
			return word[:-len('ая')], ('ая', 'ой', 'ой', 'ую', 'ой', 'ой')
		elif word.endswith('яя') and (gender == Gender.UNKNOWN or gender == Gender.FEMALE):
			return word[:-len('яя')], ('яя', 'ей', 'ей', 'юю', 'ей', 'ей')
		elif word.endswith('а'):
			return word[:-len('а')], ('а', yi(word[-2:-1]), 'е', 'у', 'ой', 'е')
		elif word.endswith('я'):
			return word[:-len('я')], ('я', 'и', 'е', 'ю', 'ей', 'е')
		elif word.endswith(('б', 'в', 'г', 'д', 'ж', 'з', 'к', 'л', 'м', 'н', 'п', 'р', 'с', 'т', 'ф', 'х', 'ц', 'ч', 'ш', 'щ')) and \
			(gender == Gender.UNKNOWN or gender == Gender.MALE):
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
			return word[:-len('ь')], ngdip('ь', 'и', 'и', 'ью', 'и')
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
			yield src[lit_start:word_start], src[word_start:i]

	def src(self, sep="/"): return "".join(piece for literal, cases in self.pieces for piece in (literal, "{" + sep.join(cases) + "}" if cases else ""))

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
	unpacked_names_and_adjs = None

	@staticmethod
	def feminize_adj(w):
		if w.endswith('ый') or w.endswith('ой'): return w[:-2] + 'ая'
		elif w.endswith('ий'): return w[:-2] + ('я' if w[-3:-2] in 'н' else 'а') + 'я'
		elif w.endswith('н'): return w + 'а'
		else: return w

	@staticmethod
	def random_name(ban=None, see=None, *, return_gender=False):
		names, adjs = Noun.unpacked_names_and_adjs or tuple(unpack_str(pack).split() for pack in (Noun.names_pack, Noun.adjs_pack))
		if not Noun.unpacked_names_and_adjs: Noun.unpacked_names_and_adjs = names, adjs

		while True:
			if not adjs or not names: return None
			iadj, iname = randrange(len(adjs)), randrange(len(names))
			adj, name, gender = adjs[iadj], names[iname], Gender.MALE
			if name.endswith('{f}'): name, adj, gender = name[:-len('{f}')], Noun.feminize_adj(adj), Gender.FEMALE
			if ban and ban('adj', adj): adjs = adjs[:iadj] + adjs[iadj+1:]; continue
			if ban and ban('noun', name): names = names[:iname] + names[iname+1:]; continue

			# против «ангельских ангелов»
			adj_l2 = len(adj) - (2 if adj.endswith('й') else 0)
			px, shortest = common_prefix_len(adj.casefold(), name.casefold()), min(adj_l2, len(name))

			def specialcased_to_live():
				# «странный странник» — забавно, но OK
				# «бессмертный бес» etc. — OK; единственная тавтология с «бесом» — «бесноватый»
				return adj.startswith("странн") or name == "бес" and not adj.startswith("бесн")

			if (shortest + 1) // 2 < px and not specialcased_to_live():
				if randrange(2) > 0: adjs = adjs[:iadj] + adjs[iadj+1:]
				else:                names = names[:iname] + names[iname+1:]
				continue

			result = cap_first(adj) + ("" if adj.endswith('-') else " ") + name
			if see: see('adj', adj); see('name', name)
			result = Noun.guess(result, animate=True, gender=gender)
			return (result, gender) if return_gender else result

class Test:
	class Failed(Exception): pass
	def setup(self): pass
	def teardown(self): pass

	cases = None
	def one(self, *args): raise NotImplementedError("one(*cases[i])")
	def describe(self, *desc): return ""

	def expect_equal(self, got, expected, name, *desc):
		desc = self.describe(*desc)
		if got != expected: raise Test.Failed("{0}{1}{2} = {3}, ожидается {4}".format(desc, ": " if desc else "", name, got, expected))

class NounTest(Test):
	cases = \
		("Злобн{ый/ого/ому/ого/ым/ом} Буратино", "Злобн{ый|ого|ому|ого|ым|ом} Буратино"), \
		(("Злобный Буратино", {'animate': True}), "Злобн{ый/ого/ому/ого/ым/ом} Буратино"), \
		(("Рика", {'animate': True}), "Рик{а/и/е/у/ой/е}"), \
		(("Слон", {'animate': True}), "Слон{/а/у/а/ом/е}"), \
		("...{большой кусок} угля", "...больш{ой/ого/ому/ой/им/ом} кус{ок/ка/ку/ок/ком/ке} угля"), \

	def one(self, base, expect_src):
		n = Noun.guess(base[0], **(base[1] if len(base) >= 2 else {})) if isinstance(base, tuple) else Noun.parse(base)
		self.expect_equal(n.src(sep='|' if isinstance(base, str) and base.find('/') >= 0 else '/'), expect_src, "forms", base)
	def describe(self, base): return base

def clamp(x, a, b): # эти странные конструкции — (бессмысленная) оптимизация общего случая (a <= x <= b) и паранойя x=NaN.
	return x if (x >= a) and (x <= b) else b if x > b else a

def mix(a, b, x):
	return b*x + a*(1-x)

# XOR с псевдослучайными числами, чтобы некоторые строки не светились в файлах в неизменном виде >:3
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

# округляет 8.2 до 8 с шансом 80% или 9 с шансом 20%
def rand_round(x):
	f = math.floor(x)
	d = x - f
	return f + int(d > 0 and random() < d)

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

		return textwrap.wrap(line, width, subsequent_indent=prefix) or ('',)

	return '\n'.join(wrapped_line for source_line in text.splitlines() for wrapped_line in wrap_paragraph(source_line, width))

# Другая обёртка над textwrap.wrap.
# Возвращает список записей (piece, start, next), где next — позиция, с которой начинается следующая строка (для последней в text будет next = len(text)),
# а start — где начинается эта (т. е. без учёта граничных случаев [i].next == [i+1].start).
# Например: wrap_feedback("привет, как дела?", 7) => [('привет,', start=0, next=8>), ('как', start=8, next=12>), ('дела?', start=12, next=17>)]
# Не поддерживает возможности предыдущего wrap (\n и |).
class WrapFeedback:
	__slots__ = 'piece', 'start', 'next'
	def __init__(self, piece, start): self.piece, self.start, self.next = piece, start, None
	def __repr__(self): return f"{self.__class__.__name__}({repr(self.piece)}, start={self.start}, next={self.next}>)"

def wrap_feedback(text, width, maxlines=None):
	pieces = textwrap.wrap(text, width)
	result = [None] * min(len(pieces), maxlines if maxlines is not None else len(pieces))

	# Найти конец каждой строки результата в text. Предполагается, что это возможно.
	text_pos = 0
	for i in range(len(result) + 1): # + 1 нужно для уточнения последней next
		if i < len(pieces):
			start_pos = text.index(pieces[i], text_pos) # если textwrap.wrap() съедает что-то посередине, придётся искать как подпоследовательность, но пока вроде работает
			text_pos += len(pieces[i])
			if i < len(result): result[i] = WrapFeedback(pieces[i], start_pos) # next будет уточнён на следующей итерации

		# len(text) — случай самой-самой последней строки, т. е. для которой нет настоящего start_pos следующего piece
		if i > 0: result[i-1].next = start_pos if i < len(pieces) else len(text)
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
		self.root = Commands.node("", "", None)

	def add(self, *args):
		node = self.root
		iarg = 0
		while iarg < len(args):
			cmd, func = args[iarg], args[iarg+1]
			node = node.add(check(cmd, isinstance(cmd, str), "cmd?!"), check(func, func, "func?!"))
			iarg += 2

	def guess(self, input):
		def not_found():
			return None, None, self.suggest_something(input) or None

		def found(node):
			node = node.down_to_unambiguous()
			return node.func or None, None if node.func else self.suggest_something(start_node = node), None

		# Для каких команд input является подпоследовательностью по символам?
		sym_cs = self.subseq_matches(input)
		if len(sym_cs) == 1:
			return found(sym_cs[0]) # для ровно одной: это однозначный ответ
		elif not sym_cs:
			return not_found()      # ни для одной

		# для нескольких: просеять эти совпадения дальше, теперь по словам
		cs = sym_cs
		words = Commands.split(input)

		# Для каких из ранее найденных команд input является подпоследовательностью по словам, и насколько хорошей? Оценивается по длине LCS слов :)
		# Также отдаётся предпочтение менее многословным командам, чтобы на 1 и remove 1 ответило 1 (сейчас сделано через деление на порядковые номера слов).
		# Также бонусно учитывается общий префикс, чтобы на remove 10, remove 11, remove 21 и введённую remove 1 не называло в подсказках remove 21.
		# Также учитывается законченность команды (наличие node.func).
		word_cs = best_score = None
		for node in cs:
			cur_score = lcs_score(node.words, words, lambda a, _ia, b, _ib: (common_prefix_len(a, b) + lcs_len(a, b)**2) / (1 + max(_ia, _ib)))
			if best_score is None or cur_score > best_score or cur_score == best_score and node.func and not any(node.func for node in word_cs):
				word_cs = [node]
				best_score = cur_score
			elif cur_score == best_score and (node.func or any(not node.func for node in word_cs)):
				word_cs.append(node)

		if word_cs and len(word_cs) == 1: # Одна подошла лучше остальных: это однозначный (кхе-кхе) ответ.
			return found(word_cs[0])
		elif word_cs:
			cs = word_cs
		else:
			# Это НЕВОЗМОЖНО ввиду оценки через lcs_len. Но на случай, если логика оценки изменится, оставлю заглушку...
			return not_found() # Либо пойти дальше со старыми cs, предлагать АЛЬТЕРНАТИВЫ.

		# После всех пыток команда осталась неоднозначной, так и ответим.
		# Если слишком много вариантов — выбрать случайные.
		MAX_ALTERNATIVES = 10
		if len(cs) > MAX_ALTERNATIVES: cs = [cs[i] for i in sorted(random.sample(range(len(cs)), MAX_ALTERNATIVES))]
		return None, [node.down_to_unambiguous().backtrack() for node in cs], None

	# Основа guess: ищет среди всех команд те, для которых input является подпоследовательностью.
	# Если просто искать такие среди списка листовых, будет много паразитных при недописанном вводе
	# (например, когда есть heal hp, heal mp, subseq_matches на "h" вернёт единственный узел heal)
	# Кроме того, совпадения по идущим подряд символам получают бонус, чтобы на "il" предпочесть "silence" вместо "dispell".
	def subseq_matches(self, input):
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

		# Насколько хорошо узел найденной команды node соответствует вводу input.
		def score(node):
			best = None
			for occ in subseq_occurences(input, node.full_command):
				cur = 0
				for a, b in sequences(occ):
					cur += (b-a)*(b-a) # нелинейный бонус за идущие подряд символы
				if best is None or cur > best: best = cur
			return best

		ongoing = [(self.root, 0)]
		best_nodes, best_score = [], None
		while ongoing:
			new_nodes = []
			for node, start in ongoing:
				match_len = subseq_len(input, start, node.spaced_name)
				start += match_len
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
		0 if sym in string.ascii_letters else
		1 if sym in string.digits else
		2 if sym in '?' else
		3)

	@staticmethod
	def split(cmd, with_spaces=False):
		i, r, preved = 0, [], 0
		while i < len(cmd):
			start_cls = Commands.classify_sym(cmd[i])
			if start_cls >= 0:
				start = i
				while True:
					i += 1
					if i >= len(cmd) or Commands.classify_sym(cmd[i]) != start_cls: break
				r.append((cmd[preved:i], cmd[start:i]) if with_spaces else cmd[start:i])
				preved = i
			else:
				i += 1
		return r

	def has_anything(self):
		return self.root.childs

	def suggest_something(self, input=sentinel, start_node=None):
		matches = [start_node or self.root]
		for subcommand in Commands.split(input) if input is not sentinel else []:
			new_matches = [child for node in matches for cmd, child in node.childs.items() if cmd.startswith(subcommand)]
			if not new_matches: break
			matches = new_matches

		# если только один match, и это не корень (либо явно вызвано suggest_something() без input) —  развернуть в детей
		if len(matches) == 1 and not matches[0].func and matches[0].childs and matches[0].parent or input is sentinel:
			matches = [match for match in matches[0].childs.values()]

		return [node.down_to_unambiguous().backtrack() for node in matches if node.parent]

	class node:
		def __init__(self, spaced_name, unspaced_name, parent):
			self.childs = OrderedDict()
			self.func   = None
			self.spaced_name = spaced_name
			self.parent = parent
			self.words  = parent.words + [unspaced_name] if parent else []
			self.full_command = (parent.full_command if parent else "") + spaced_name

		def add(self, cmd, func):
			node = self
			for spaced_subcommand, subcommand in Commands.split(cmd, with_spaces=True):
				child = node.childs.get(subcommand, None)
				if not child:
					child = Commands.node(spaced_subcommand, subcommand, node)
					node.childs[subcommand] = child
				node = child
			if node.func: raise RuntimeError("Команда {0} уже определена.".format(node.backtrack()))
			node.func = check(func, func, cmd)
			return node

		def backtrack(self):
			return self.full_command

		def down_to_unambiguous(self):
			node = self
			while not node.func and len(node.childs) == 1 and node.parent: node = next(node for node in node.childs.values())
			return node

class DummyCommands:
	@staticmethod
	def add(*args): pass

class CommandsTest(Test):
	cases = \
		(
			(("one two three", "123"), ("one two four", "124"), ("one three six", "136")),
			(
				("o t", (None, ["one two", "one three six"], None)),
				("o t t", ("123", None, None)),
				("o t s", ("136", None, None)),
			)
		), \
		((("spd-", "A"), ("sp.frailness", "B")), ("sp-", ("A", None, None))), \
		((("sp-", "A"), ("spd-", "B"), ("sp.frailness", "C")), ("sp-", ("A", None, None))), \
		(
			(("1", "L1"), ("remove 10", "B"), ("remove 11", "C"), ("remove 21", "D")),
			(
				("1", ("L1", None, None)),
				("r1", (None, ["remove 10", "remove 11"], None)),
				("r2", ("D", None, None)),
			)
		), \
		((("shop", "A"), ("shoot timestop", "B")), ("s", ("A", None, None))), \
		((("sp.dispell+", "A"), ("sp.frailness+", "B"), ("b.timestop-", "C")), (("il", ("B", None, None)), ("es", (None, ["sp.frailness+", "b.timestop-"], None))))
	def one(self, adds, queries):
		cmds = Commands()
		for add in adds: cmds.add(*add)
		for query, expect in queries if isinstance(queries[0], tuple) else (queries,):
			self.expect_equal(cmds.guess(query), expect, "guess", adds, query)

	def describe(self, adds, query): return str(adds) + ", " + query

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
					line = line[:i + 1] + line[i + 2:]
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
		fragments.append(Fragment(line[start:], None, 0, 0, 0)) # см. (**1)
		soup.append(fragments)

	# Теперь нужно пройтись по списку маркеров и все их выровнять.
	marker = first_marker
	while marker:
		target_pos = max(fragment.marker_pos for fragment in marker.occurrences)

		for fragment in marker.occurrences:
			pad_delta = target_pos - fragment.marker_pos
			if pad_delta == 0: continue

			# эвристика :\ так-то можно было бы управлять какими-нибудь спецсимволами в маркерах...
			if fragment.data and fragment.data[-1] in ' .': # точка для тестов
				fragment.data = fragment.data + ' ' * pad_delta
			else:
				fragment.data = ' ' * pad_delta + fragment.data

			# -1 — после последних фрагментов строк, т. е. тех, которые Fragment(line[start:], None, 0, 0, 0) (**1),
			# маркеров нет, а значит, и смещения корректировать не у чего
			for i in range(fragment.fragment_index, len(soup[fragment.line_index]) - 1):
				soup[fragment.line_index][i].marker_pos += pad_delta

		marker = marker.next

	return ["".join(frag.data for frag in fragments) for fragments in soup]

def multipad_escape(line):
	i = 0
	while i < len(line):
		if line[i] == '[': line = line[:i+1] + line[i:]; i += 2
		else: i += 1
	return line

class MultipadTest(Test):
	cases = \
		(
			["STR [A]5[B] -> [C]10[D]   [E]$100[F] / [G]1[H]",
			 "INT [A]10[B] -> [C]15[D]   [E]$150[F] / [G]1[H]",
			 "SPEED [A]15[B] -> [C]1000[D]   [E]$9999[F] / [G]99[H]"],

			["STR    5 ->   10    $100 /  1",
			 "INT   10 ->   15    $150 /  1",
			 "SPEED 15 -> 1000   $9999 / 99"]
		), \
		(
			["STR.[A]5[B].->.[C]10[D]...[E]$100[F]./.[G]1[H]",
			 "INT.[C]10[E].->.[I]15",
			 "SPEED.[B]15[C].->.....[D]1000[E]....[I]$9999"],

			["STR. 5.->.      10... $100./.1",
			 "INT.                10.->.15",
			 "SPEED.  15.->.....1000....$9999"],
		), \
		(["1[A]2[B]3", "4[B]5[A]6"], ["MultipadMarkupError"])
	def one(self, input, expect):
		try:
			output = multipad(input)
		except MultipadMarkupError as e:
			output = [e.__class__.__name__]
		self.expect_equal("\n\n" + "\n".join(output), "\n\n" + "\n".join(expect), "output", "\n\n" + "\n".join(input))

	def describe(self, input): return input

def cls():
	os.system('cls' if os.name == 'nt' else 'clear')

# Эффект, наложенный на персонажа.
class Hex:
	ran_out = property(lambda self: self.turns <= 0)

	def __init__(self, power, turns):
		self.applied = False
		self.master = self.victim = None
		self.power = check(power, power > 0, "power?!")
		if self.time_based:
			self.turns = check(turns, turns > 0, "turns?!")
		else:
			self.turns = 1

	def apply(self, master, victim):
		check(not self.applied, "already applied", master.alive, "мастер мёртв", victim.alive, "жертва мертва")
		self.master = check(master, isinstance(master, Fighter), "master?!")
		self.victim = check(victim, isinstance(victim, Fighter), "victim?!")
		master.caused_hexes.add(self)
		victim.hexes.append(self)
		self.applied = True

	def unapply(self):
		check(self.applied, "not applied", self.ran_out, "not ran_out")
		self.master.caused_hexes.remove(self)
		self.victim.hexes.remove(self)

	def tick(self):
		check(self.applied, "not applied", not self.ran_out, "хекс истёк")
		self.do_tick()
		if self.ran_out: return

		if self.time_based:
			self.turns -= 1
			if self.ran_out: self.do_finish()

	def cancel(self):
		check(self.applied, "not applied")
		if self.ran_out: return
		self.turns = 0
		check(self.ran_out, "not ran_out after forced runout")
		self.do_cancel()

	def do_start(self): pass
	def do_tick(self): pass
	def do_finish(self): pass
	def do_cancel(self): pass

	def short(self, cmd_prefix="", for_multipad=False, flip=False):
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
	def do_generic_name(cls): raise NotImplementedError("do_class_name")

	def do_name(self): return self.generic_name()
	def do_describe_power(self): return None

	def detail(self): return self.do_detail()
	def do_detail(self): raise NotImplementedError("do_detail")

	def cmd(self): return self.do_cmd()
	def do_cmd(self): raise NotImplementedError("do_cmd")

	npower = property(lambda self: self.power / self.BASELINE_POWER)
	BASELINE_POWER = 100
	dispellable = False
	time_based = True

	def __getstate__(self):
		check(self.applied, "not applied?!")
		return {k:v for k,v in self.__dict__.items() if k not in (
			'applied',         # резолвится здесь
			)}

	def __setstate__(self, state):
		self.__dict__.update(state)
		self.applied = True                # отбрасывается здесь
		self.master.caused_hexes.add(self) # caused_hexes отбрасывается Fighter
		self.victim.hexes.append(self)     # hexes отбрасывается Fighter

class RageHex(Hex):
	#  мин. 1.2x @ pow → 0
	#       1.5x @ BASELINE_POWER
	# макс. 5.0x @ pow = 1267
	physdam_x = property(lambda self: clamp(1.2 + 0.3 * self.npower, 1.2, 5.0))

	#  мин. 1.1x @ pow → 0
	#       1.2x @ BASELINE_POWER
	# макс. 2.2x @ pow = 1100
	backlash_x = property(lambda self: clamp(1.1 + 0.1 * self.npower, 1.1, 2.2))

	@classmethod
	def do_generic_name(cls): return "Ярость"
	def do_describe_power(self):
		m = round(self.physdam_x, 1)
		return None if m == 1.5 else f"{m}x"

	def do_detail(self): return \
		"Увеличивает физическую атаку (x{0}) и любой получаемый урон (x{1}).".format(round(self.physdam_x, 1), round(self.backlash_x, 1))

	def do_cmd(self): return 'rage'

class RageHexTest(Test):
	def __init__(self): self.dummy = None
	def setup(self): self.dummy = RageHex.__new__(RageHex)

	cases = (-1000, 1.2, 1.1), (0, 1.2, 1.1), (Hex.BASELINE_POWER, 1.5, 1.2), (1100, 4.5, 2.2), (1267, 5, 2.2), (9999, 5, 2.2)
	def one(self, power, ref_physdam_x, ref_backlash_x):
		self.dummy.power = power
		self.expect_equal(round(self.dummy.physdam_x, 1), ref_physdam_x, "physdam_x")
		self.expect_equal(round(self.dummy.backlash_x, 1), ref_backlash_x, "backlash_x")
	def describe(self, *desc): return f"power = {self.dummy.power}"

class DeathWordHex(Hex):
	def do_finish(self):
		check(self.master.alive, "Смертный приговор пережил автора")
		if self.victim.alive:
			self.victim.die("в исполнение Смертного приговора", self.master)

	@classmethod
	def do_generic_name(cls): return "Смертный приговор"
	def do_detail(self): return \
		"Гарантированная смерть через {turns}.\n"\
		"Вы можете снять этот хекс с помощью Развеивания либо убив мага, наложившего заклинание.".format(turns = plural(self.turns, "{N} ход{/а/ов}"))

	def do_cmd(self): return 'deathword'
	dispellable = True

class Bleeding(Hex):
	def __init__(self, power):
		super().__init__(power, Bleeding.turns_from_power(power))
		self.precise_power = power
		self.precise_damage = 0

	@classmethod
	def do_generic_name(cls): return "Кровотечение"
	def do_name(self): return self.do_generic_name() + ("!!!" if self.npower > 3 else "!" if self.npower > 2 else "")
	def do_detail(self): return \
		"Отнимает HP (-{0}%/ход) и уменьшает ловкость (-{1}).".format(round(self.precise_hp_percentile_decay, 1), round(self.precise_dex_debuff))

	def do_tick(self):
		self.precise_damage += self.precise_hp_percentile_decay/100 * self.victim.mhp
		dmg = math.floor(self.precise_damage)
		if dmg > 0:
			self.victim.ouch(dmg, "от потери крови", self.master)
			self.precise_damage -= dmg
		self.precise_power = Bleeding.decay_power(self.precise_power)
		self.power = max(1, round(self.precise_power))

	def do_cmd(self): return 'bleeding'

	@staticmethod
	def decay_power(power): return power * Bleeding.POWER_DECAY

	@staticmethod
	def turns_from_power(power): return clamp(math.ceil(math.log(0.5 * Hex.BASELINE_POWER / power, Bleeding.POWER_DECAY)), 3, 20)

	precise_hp_percentile_decay = property(lambda self: clamp(2.5 * (self.npower**0.5 if self.npower > 1 else self.npower), 1, 5))
	precise_dex_debuff = property(lambda self: 3 * self.npower**0.5)
	POWER_DECAY = 0.9

# По инстансу на каждое запомненное заклинание у каждого бойца.
class Spell:
	LIST_ORDER = None
	@classmethod
	def name(cls): return cls.do_name()
	@classmethod
	def do_name(cls): raise NotImplementedError("do_name")

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

	def revert(self, target):
		check(self.applied, "not applied", self.target == target, "target?!")
		target.upgrades.remove(self)
		target.ap_used -= self.ap_taken
		self.applied = False
		self.do_revert(target)

	def do_apply(self, target): pass
	def do_revert(self, target): pass

	def apply_message(self, target): return self.do_apply_message(target)
	def revert_message(self, target): return self.do_revert_message(target)

	def do_apply_message(self, target): pass
	def do_revert_message(self, target): pass

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

	# Стоимость в AP.
	@classmethod
	def ap_cost(cls, target): return cls.do_ap_cost(target)

	@classmethod
	def do_ap_cost(cls, target): raise NotImplementedError("do_ap_cost")

	# Стоимость в золоте.
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
		return max(1, int(0.5 * self.gold_taken))

	@classmethod
	def sell_accusative(cls, target): return cls.do_sell_accusative(target)
	@classmethod
	def do_sell_accusative(cls, target): raise NotImplementedError("do_sell_accusative")

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

	def __init__(self):
		super().__init__()
		self.stat = check(self.STAT, self.STAT in {'str', 'int', 'dex', 'spd'}, "stat?!")
		self.amount = check(self.AMOUNT, 1 <= self.AMOUNT <= 100, "amount?!")

	def do_apply(self, target):
		with target.save_relative_vitals():
			setattr(target, 'base_' + self.stat, self.get_base_stat(target) + self.amount)

	def do_revert(self, target):
		with target.save_relative_vitals():
			setattr(target, 'base_' + self.stat, self.get_base_stat(target) - self.amount)

	@classmethod
	def do_allow(cls, target): return sum(up.AMOUNT for up in cls.find_all(target)) + cls.AMOUNT <= cls.LIMIT

	@classmethod
	def do_ap_cost(cls, target): return 1

	@classmethod
	def do_cmd(cls): return cls.STAT

	@classmethod
	def get_base_stat(cls, target): return getattr(target, 'base_' + cls.STAT)

	@classmethod
	def do_sell_accusative(cls, target): return "({0} -> {1})".format(cls.get_base_stat(target), cls.get_base_stat(target) - cls.AMOUNT)

	@classmethod
	def genitive_stat(cls): raise NotImplementedError("genitive_stat")

	@classmethod
	def do_cost_preface(cls, target):
		return "Тренировка " + cls.genitive_stat() + " с " + str(cls.get_base_stat(target)) + " до " + str(cls.get_base_stat(target) + cls.AMOUNT) + " стоит"

	@classmethod
	def shop_label(cls, target):
		return cls.STAT.upper() + " [cur]" + str(cls.get_base_stat(target)) + "[/cur]" + \
			(" -> [upd]" + str(cls.get_base_stat(target) + cls.AMOUNT) + "[/upd]" if cls.allow(target, ignore_ap_cost=True) else "") + " "

class StrUpgrade(StatUpgrade):
	STAT, AMOUNT, LIMIT = 'str', 5, 20

	@classmethod
	def do_gold_cost(cls, target): return 120 + 30 * cls.count(target)

	def do_apply_message(self, target): return "Ваши мускулы наливаются силой."
	def do_revert_message(self, target): return "Ваши мускулы слабеют."

	@classmethod
	def do_sell_accusative(cls, target): return "часть своей силы " + super().do_sell_accusative(target)
	@classmethod
	def genitive_stat(cls): return "силы"

class IntUpgrade(StatUpgrade):
	STAT, AMOUNT, LIMIT = 'int', 5, 20

	@classmethod
	def do_gold_cost(cls, target): return 135 + 35 * cls.count(target)

	def do_apply_message(self, target): return "Ваш ум заостряется."
	def do_revert_message(self, target): return "Вы начинаете хуже соображать."

	@classmethod
	def do_sell_accusative(cls, target): return "часть своего интеллекта " + super().do_sell_accusative(target)
	@classmethod
	def genitive_stat(cls): return "интеллекта"

class DexUpgrade(StatUpgrade):
	STAT, AMOUNT, LIMIT = 'dex', 5, 20

	@classmethod
	def do_gold_cost(cls, target): return 70 + 25 * cls.count(target)

	def do_apply_message(self, target): return "Ваши рефлексы улучшаются."
	def do_revert_message(self, target): return "Вы чувствуете себя {0}.".format(target.gender.ize("неповоротлив{ым/ой}"))

	@classmethod
	def do_sell_accusative(cls, target): return "часть своей ловкости " + super().do_sell_accusative(target)

	@classmethod
	def genitive_stat(cls): return "ловкости"

class SpeedUpgrade(StatUpgrade):
	STAT, AMOUNT, LIMIT = 'spd', 30, 150

	@classmethod
	def do_gold_cost(cls, target): return 150 + 50 * sum(1 for up in cls.find_all(target))

	def do_apply_message(self, target): return "Ваша кровь бурлит!"
	def do_revert_message(self, target): return "Ваша кровь остывает..."

	@classmethod
	def do_sell_accusative(cls, target): return "часть своей скорости " + super().do_sell_accusative(target)

	@classmethod
	def genitive_stat(cls): return "скорости"

class Firestorm(Spell):
	LIST_ORDER = 0
	@classmethod
	def do_name(cls): return "Огн. шторм"

	@classmethod
	def do_cmd(cls): return 'fstorm'

	def do_mp_cost(self): return 6

class Dispell(Spell):
	LIST_ORDER = 1
	@classmethod
	def do_name(cls): return "Развеять"

	@classmethod
	def do_cmd(cls): return 'dispell'

	def do_mp_cost(self): return 2

class Frailness(Spell):
	LIST_ORDER = 2
	@classmethod
	def do_name(cls): return "Хрупкость"

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
		check(not self.spell)
		spell_class = check(self.SPELL_CLASS, issubclass(self.SPELL_CLASS, Spell) and self.SPELL_CLASS is not Spell, "SPELL_CLASSs?!")
		self.spell = spell_class()
		target.learn_spell(self.spell)

	def do_revert(self, target):
		target.forget_spell(self.spell)
		self.spell = None

	@classmethod
	def do_cmd(cls): return 'sp.' + cls.SPELL_CLASS.cmd()

	@classmethod
	def shop_label(cls, target): return "Заклинание: " + cls.SPELL_CLASS.name()

	@classmethod
	def do_sell_accusative(cls, target): return "ваше " + cls.SPELL_CLASS.__name__

	@classmethod
	def do_cost_preface(cls, target): return cls.SPELL_CLASS.__name__ + " стоит"

class FirestormSpellUpgrade(SpellUpgrade):
	SPELL_CLASS = Firestorm

	@classmethod
	def do_gold_cost(cls, target): return 150

	@classmethod
	def do_ap_cost(cls, target): return 2

	@classmethod
	def do_sell_accusative(cls, target): return "вашу магию Огненного шторма"

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

	@classmethod
	def do_sell_accusative(cls, target): return "вашу магию Развеивания"

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

	@classmethod
	def do_sell_accusative(cls, target): return "вашу магию Хрупкости"

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
			self.weapon.ammos.insert(bisect_right([ammo.LIST_ORDER for ammo in self.weapon.ammos], self.LIST_ORDER), self)

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
		ammo_class = check(self.AMMUNITION_CLASS, issubclass(self.AMMUNITION_CLASS, Ammunition) and self.AMMUNITION_CLASS is not Ammunition,
			"AMMUNITION_CLASS?!")
		self.ammo = ammo_class()
		self.ammo.install(target, self)

	def do_revert(self, target):
		check(self.ammo, "ammo")
		self.ammo.uninstall(target, self)

	@classmethod
	def do_cmd(cls): return 'b.' + cls.AMMUNITION_CLASS.cmd()

	@classmethod
	def genitive_ammunition_module_name(cls): raise NotImplementedError("genitive_ammunition_module_name")

	@classmethod
	def do_sell_accusative(cls, target):
		msg = ("снятие усовершенствования модуля " if cls.count(target) > 1 else "ваш модуль ") + cls.genitive_ammunition_module_name()
		cur = cls.AMMUNITION_CLASS.name_up(target, 0)
		targ = cls.AMMUNITION_CLASS.name_up(target, -1)
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
	def shop_label(cls, target):
		name = multipad_escape(target.name) + ": " + cls.AMMUNITION_CLASS.name(target)
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

class Living:
	ap_limit = property(lambda self: 1 + 2*(self.xl - 1))
	PLACEHOLDER_NAME = Noun.parse("{баг}")

	def __init__(self):
		self.xp = 0
		self.xl = 1
		self.ap_used = 0
		self.name = Living.PLACEHOLDER_NAME
		self.gender = Gender.UNKNOWN
		self.upgrades = []

	def receive_xp(self, amount):
		self.xp += amount
		def will_levelup(): return self.xp >= self.xp_for_levelup(self.xl) and self.xl < self.LEVEL_CAP
		if will_levelup():
			with self.save_relative_vitals():
				while True:
					self.xp -= self.xp_for_levelup(self.xl)
					self.level_up()
					if not will_levelup(): break
		if self.xl == self.LEVEL_CAP: self.xp = 0

	def drain_xp(self, amount):
		self.xp -= amount
		while self.xp < 0 and self.xl > 1:
			self.xp += self.xp_for_levelup(self.xl - 1)
			self.level_down()
		self.xp = max(self.xp, 0)

	def level_up(self):
		self.xl += 1
		check(1 <= self.xl <= self.LEVEL_CAP)

	def level_down(self):
		self.xl -= 1
		check(1 <= self.xl <= self.LEVEL_CAP)
		while self.ap_used > self.ap_limit and self.upgrades: self.upgrades[-1].revert(self)

	LEVEL_CAP = 1
	def xp_for_levelup(self, xl):
		return 10 * xl

	def enough_ap_for(self, upgrade_or_whatever):
		ap_cost = (
			upgrade_or_whatever if isinstance(upgrade_or_whatever, int) else
			upgrade_or_whatever.ap_cost(self))

		return self.ap_used + ap_cost <= self.ap_limit

	def next_percentage(self):
		return math.floor(self.xp / self.xp_for_levelup(self.xl) * 100) if self.xl < self.LEVEL_CAP else None

	# под for_multipad подразумевается for_shop
	def living_desc(self, for_multipad=False):
		name = cap_first(self.name)
		show_ap = for_multipad or self.xp > 0 or self.xl > 1 or self.ap_used > 0
		return ("{name}: {xlmp}{xl}" + (", {ap_mp}умения: {0.ap_used}/{0.ap_limit}" if show_ap else "")).format(
			self, xl = self.xl_desc(self.xl, self.next_percentage(), short=for_multipad, show_nx=not for_multipad),
			name = multipad_escape(name) if for_multipad else name,
			xlmp = "[lv]" if for_multipad else "",
			ap_mp = "[ap]" if for_multipad else "")

	@staticmethod
	def xl_desc(xl, next_percentage, short=None, show_nx=True):
		lv_word = "lv." if short else "уровень "
		nx_word = "" if short else "след. "
		return f"{lv_word}{xl}" + (f" ({nx_word}{next_percentage}%)" if show_nx and next_percentage is not None else "")

	class RelativeVitals():
		def __init__(self, char): self.char = char
		def __enter__(self): return self
		def __exit__(self, et, e, tb): pass

	def save_relative_vitals(self): return self.RelativeVitals(self)

	def __getstate__(self):
		return {k:
			v.value if k == 'gender' else
			('g' + str(v) if v == Noun.guess(v) else 'p' + v.src()) if k == 'name' else
			v
			for k, v in self.__dict__.items()}

	def __setstate__(self, state):
		self.__init__()
		self.__dict__.update((k,
			Gender(v) if k == 'gender' else
			(Noun.parse(v[1:]) if v.startswith('p') else Noun.guess(v[1:]) if v.startswith('g') else throw(pickle.UnpicklingError, "name")) if k == 'name' else
			v)
			for k, v in state.items())
		for up in self.upgrades: up.target = self # отбрасывается Upgrade

class Fighter(Living):
	hp    = property(lambda self: self.cur_hp)
	mhp   = property(lambda self: max(1, round((self.base_mhp + 5 * (self.xl - 1)**0.77) * (1 + (self.str - 10) / 10))))
	dead  = property(lambda self: self.death_cause)
	alive = property(lambda self: not self.dead)
	mp    = property(lambda self: self.cur_mp)
	mmp   = property(lambda self: round(self.base_mmp * (1 + (self.int - 10) / 10)))
	str   = property(lambda self: self.base_str)
	int   = property(lambda self: self.base_int)
	dex   = property(lambda self: self.base_dex)
	spd   = property(lambda self: self.base_spd)
	ac    = property(lambda self: self.base_ac)
	ev    = property(lambda self: max(0, self.base_ev + (self.dex - 10)))
	LEVEL_CAP = 7

	def __init__(self):
		Living.__init__(self)
		self.base_mhp = 10
		self.base_mmp = 10
		self.base_str = 10
		self.base_int = 10
		self.base_dex = 10
		self.base_spd = 100
		self.base_ac = 0
		self.base_ev = 10
		self.death_cause = None
		self.arena = None

		self.hexes = []
		self.caused_hexes = set()
		self.weapon = None
		self.spells = []

		self.cur_hp = self.mhp
		self.cur_mp = self.mmp

	def ouch(self, hp_dam, death_cause, killer=None):
		check(hp_dam >= 0, "hp_dam?!", death_cause, "death_cause?!", not killer or isinstance(killer, Fighter), "killer?!")

		if not self.dead:
			self.cur_hp -= hp_dam
			if self.cur_hp <= 0: self.die(death_cause, killer)

	def die(self, cause, killer=None):
		check(not self.dead, "not dead", cause, "cause?!", not killer or isinstance(killer, Fighter), "killer?!")
		for hex in self.hexes:
			hex.cancel()

		for hex in self.caused_hexes:
			if isinstance(hex, DeathWordHex):
				hex.cancel()

		if killer: cause = f"{cause} ({killer.name})"
		self.death_cause = cause

	def end_turn(self):
		ran_out = []
		for hex in self.hexes:
			check(hex.victim == self, "hex.victim != self")
			if not hex.ran_out: hex.tick()
			if hex.ran_out: ran_out.append(hex)

		for hex in ran_out:
			hex.unapply()

	def set_weapon(self, weapon):
		if self.weapon: self.weapon.owner = None
		self.weapon = weapon
		if self.weapon: self.weapon.owner = self

	def learn_spell(self, spell):
		check(spell not in self.spells, "already in spells",
			all(not isinstance(spell, type(sp)) for sp in self.spells), "duplicate spell",
			all(not isinstance(sp, type(spell)) for sp in self.spells), "duplicate spell 2")
		self.spells.insert(bisect_right([spell.LIST_ORDER for spell in self.spells], spell.LIST_ORDER), spell)

	def forget_spell(self, spell):
		self.spells.remove(spell)

	def has_magic(self):
		return self.spells and self.mmp

	def actual_hexes(self):
		return (hex for hex in self.hexes if not hex.ran_out)

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

	def enter_arena(self, arena):
		check(not self.arena, "already on arena")
		self.arena = arena

	def leave_arena(self, arena):
		if self.arena != arena: impossible(f"arena: {self.arena}, new: {arena}")
		self.arena = None

	def __getstate__(self):
		check(not self.arena, "arena?!")
		return {k: v for k, v in super().__getstate__().items() if k not in (
			'hexes', 'caused_hexes', # резолвятся Hex
			'death_cause',           # либо сохраняемый боец жив, либо эта информация не интересна
			'arena'                  # сохраняются только в лагере~
			)}

	def __setstate__(self, state):
		super().__setstate__(state)
		self.weapon.owner = self # отбрасывается Weapon

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
			)}

	def __setstate__(self, state):
		super().__setstate__(state)
		for ammo in self.ammos: ammo.weapon = self # отбрасывается Ammunition

class Element:
	pass

class Damage:
	pass

class Arena:
	BASELINE_SPD = 100

	class Battler: # Gladiator слишком длинно
		def __init__(self, fighter, squad_id, ai, shortcut):
			self.fighter    = fighter
			self.squad_id   = squad_id
			self.ai         = ai
			self.initiative = 0        # время до хода этого участника; после хода увеличивается на значение, зависящее от SPD
			self.shortcut   = shortcut # сокращение, используемое в командах и на шкале инициативы

	class Squad:
		def __init__(self, id):
			self.id          = id
			self.members     = []
			self.max_members = None

	# Механизм подписки на сообщения о боевых событиях (note).
	# Сообщение может быть сообщено разным sink по-разному: одному — «вы ударили Грязекраба», другому то же самое — «Рика ударила Грязекраба».
	# Я на самом деле не уверен, что обычно понимают под термином sink :)
	class MessageSink:
		def __init__(self, you, note_callback=None):
			self.you = you
			self.note_callback = note_callback

		def note(self, msg): self.do_note(msg)

		def do_note(self, msg):
			if self.note_callback: self.note_callback(msg)
			else: raise NotImplementedError("do_note")

	def __init__(self):
		self.battlers   = []
		self.squads     = {}
		self.turn_queue = [] # battlers, отсортированные по initiative
		self.message_sinks = []
		self.started = False
		self.inside_turn = False
		self.action_cost = None
		self.squads_frozen = False

	# shortcut_hint — список предпочтительных сокращений участника, либо строка-альтернативное имя для автогенерируемых сокращений.
	# например: add(fighter, squad_id, ai, "Ghost") -> автоматически сгенерируются G, Gh, Go... G2, G3...
	#           add(fighter, squad_id, ai, ("Fi", "Alt")) -> предпочтёт Fi или Alt, прежде чем пойти по автогенерируемым
	def add(self, fighter, squad_id, ai, *, shortcut_hint=None):
		fighter.enter_arena(self)
		battler = Arena.Battler(fighter, squad_id, ai, self.generate_shortcut(fighter, shortcut_hint))
		if ai: ai.setup(fighter, self)
		self.battlers.append(battler)

		squad = self.force_squad(squad_id)
		check(squad.max_members is None or len(squad.members) < squad.max_members)
		squad.members.append(battler)

		self.turn_queue.insert(0, battler)
		self.delay_by(fighter, random())

	def remove(self, fighter):
		battler = self.as_battler(fighter)
		self.battlers.remove(battler)
		self.squads[battler.squad_id].members.remove(battler)
		self.turn_queue.remove(battler)
		if battler.ai: battler.ai.teardown()
		fighter.leave_arena(self)

	def dismiss(self):
		while self.battlers: self.remove(self.battlers[0].fighter)

	def allies(self, fighter):
		battler = self.as_battler(fighter)
		return (member.fighter for member in self.squads[battler.squad_id].members if member.fighter != fighter)

	def enemies(self, fighter):
		battler = self.as_battler(fighter)
		return (member.fighter for squad_id, squad in self.squads.items() if squad_id != battler.squad_id for member in squad.members)

	def as_battler(self, fighter):
		return next(b for b in self.battlers if b.fighter == fighter)

	# arena.note("сообщение")
	# -или-
	# who = ...
	# arena.note(lambda sink: "Вы обосрались." if who == sink.you else who.name + " обосрался.")
	def note(self, msg):
		for sink in self.message_sinks:
			if not isinstance(msg, str):
				msg = msg(sink)
				check(isinstance(msg, str), "должна быть строка")
			sink.note(msg)

	def turn(self):
		check(self.started, "не вызвана start", not self.inside_turn, "уже внутри turn")
		self.inside_turn = True
		self.action_cost = 1.0
		self.turn_queue[0].ai.turn()
		self.turn_queue[0].fighter.end_turn()
		self.delay_by(self.turn_queue[0].fighter, self.action_cost * uniform(0.8, 1/0.8))
		self.shift_delays()
		self.inside_turn = False

	def whose_turn(self):
		return self.turn_queue[0].fighter

	def delay_by(self, fighter, multiplier):
		battler = self.as_battler(fighter)
		index = self.turn_queue.index(battler)
		battler.initiative += multiplier * Arena.BASELINE_SPD / max(fighter.spd, 1)
		while index + 1 < len(self.turn_queue) and battler.initiative >= self.turn_queue[index + 1].initiative:
			self.turn_queue[index], index = self.turn_queue[index + 1], index + 1
		self.turn_queue[index] = battler

	def start(self):
		check(not self.started, "уже")
		self.shift_delays()
		self.started = True

	def shift_delays(self):
		shift = self.turn_queue[0].initiative
		for battler in self.turn_queue:
			battler.initiative -= shift

	def try_shortcut(self, shortcut):
		return all(b.shortcut != shortcut for b in self.battlers)

	def suggest_shortcuts(self, name_or_list):
		def transliterate(src):
			table = {'а': 'a', 'б': 'b', 'в': 'v', 'г': 'g', 'д': 'd', 'е': 'e', 'ё': 'yo', 'ж': 'j', 'з': 'z', 'и': 'i', 'й': 'y', 'к': 'k', 'л': 'l',
				'м': 'm', 'н': 'n', 'о': 'o', 'п': 'p', 'р': 'r', 'с': 's', 'т': 't', 'у': 'u', 'ф': 'f', 'х': 'h', 'ц': 'c', 'ч': 'ch', 'ш': 'sh',
				'щ': 'sch', 'ъ': '\'', 'ы': 'y', 'ь': '\'', 'э': 'e', 'ю': 'yu', 'я': 'ya'}
			result = []
			for sym in check(src, src == src.casefold(), "src"):
				if 'a' <= sym <= 'z' or '0' <= sym <= '9': tr = sym
				else: tr = table.get(sym, None)
				if tr: result.append(tr)
			return ''.join(result)

		if isinstance(name_or_list, str):
			tr = transliterate(name_or_list.casefold())
			if tr:
				if len(tr) <= 2:
					yield cap_first(tr)
				else:
					yield cap_first(tr[0])
					for isecond in range(1, len(tr)):
						yield cap_first(tr[0] + tr[isecond])
			i = 2 if tr else 1
			while True: yield cap_first((tr[0] if tr else "") + str(i)); i += 1
		else:
			yield from (check(single, single == cap_first(transliterate(single.casefold())), "wrong naming") for single in name_or_list)

	def generate_shortcut(self, fighter, hint):
		packs = (hint and self.suggest_shortcuts(hint), self.suggest_shortcuts(fighter.name))
		return next(shortcut for shortcut_pack in packs if shortcut_pack for shortcut in shortcut_pack if self.try_shortcut(shortcut))

	def force_squad(self, squad_id):
		squad = self.squads.get(squad_id, None)
		if not squad:
			if self.squads_frozen: raise RuntimeError("Добавление новых альянсов запрещено явным вызовом deny_any_new_squads.")
			squad = Arena.Squad(squad_id)
			self.squads[squad_id] = squad
		return squad

	def set_action_cost(self, fighter, cost):
		check(self.inside_turn, "not inside turn()", self.turn_queue[0].fighter == fighter, "not your turn")
		self.action_cost = cost

	def limit_squad_members(self, squad_id, limit):
		self.force_squad(squad_id).max_members = limit

	def deny_any_new_squads(self):
		self.squads_frozen = True

	def add_sink(self, sink):
		check(sink not in self.message_sinks)
		self.message_sinks.append(sink)

	def remove_sink(self, sink):
		self.message_sinks.remove(sink)

class AI:
	def __init__(self):
		self.fighter = None
		self.arena = None

	def setup(self, fighter, arena):
		check(self.fighter, not self.fighter, "double setup")
		self.fighter, self.arena = fighter, arena

	def teardown(self):
		check(self.fighter, "double teardown")
		self.fighter, self.arena = None, None

	def note(self, *args, **kargs):
		self.arena.note(*args, **kargs)

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
		self.decision()
		self.decision = None

class DummyAI(AI):
	def do_turn(self):
		chooses = []
		def make_look_with_hate_at(who):
			def note(sink):
				msg = cap_first(self.fighter.name) + " с ненавистью смотрит на "
				if who == sink.you: msg += "вас"
				else: msg += who.name(Case.ACCUSATIVE)
				msg += "."
				return msg
			return lambda: self.note(lambda sink: note(sink))

		def make_look_with_love_at(who):
			def note(sink):
				msg = cap_first(self.fighter.name) + " смотрит на "
				if who == sink.you: msg += "вас"
				else: msg += who.name(Case.ACCUSATIVE)
				msg += " с любовью."
				return msg
			return lambda: self.note(lambda sink: note(sink))

		def make_idle():
			def note(sink):
				return cap_first(self.fighter.name) + " облизывается."
			return lambda: self.note(lambda sink: note(sink))

		for ally in self.arena.allies(self.fighter):
			chooses.append((1.0, make_look_with_love_at(ally)))

		for enemy in self.arena.enemies(self.fighter):
			chooses.append((1.0, make_look_with_hate_at(enemy)))
		chooses.append((1.0, make_idle()))

		choose((act for act in chooses), get_weight=lambda act, index: act[0])[0][1]()

class Con:
	# На данный момент сделано так, что чуть больше нуля даёт [#....] и чуть меньше максимума — [####.]
	@staticmethod
	def vital_bar(cur, max, divs=10, fillchar='#', emptychar='.', reverse=False):
		fill = int(clamp(int(cur > 0) + (divs - 1) * (cur / (max or 1)), 0, divs))
		return ("[{1}{0}]" if reverse else "[{0}{1}]").format(fillchar * fill, emptychar * (divs - fill))

	@staticmethod
	def bullet_bar(cur, max, fillchar='#', emptychar='.'):
		return fillchar * cur + emptychar * (max - cur)

	# Раньше wrap() был устроен чуть сложнее, чтобы попытаться доходить до края терминала, когда возможно, но это не всегда работало:
	# нет гарантии, что консоль переведёт строку по достижении get_terminal_size.columns.
	@staticmethod
	def safe_width(width):
		return width - 1

class VitalBarTest(Test):
	cases = (0, 5, 5, 0), (1, 5, 5, 1), (2, 5, 5, 2), (3, 5, 5, 3), (4, 5, 5, 4), (5, 5, 5, 5), (0.001, 5, 5, 1), (4.999, 5, 5, 4), (1.4, 5, 5, 2)
	def one(self, cur, max, divs, expect_bars):
		self.expect_equal(Con.vital_bar(cur, max, divs), "[{0}{1}]".format('#' * expect_bars, '.' * (divs - expect_bars)), "vital_bar", cur, max)
	def describe(self, cur, max): return f"HP = {cur}/{max}"

class Mode:
	def __init__(self):
		self.session = None
		self.last_screen = self.last_input = ""

	def process(self):
		self.do_process()

	def render(self, lines, cmds):
		self.do_render(lines, cmds)
		if self.do_prompt: lines.append("\n> ")

	def do_process(self): pass
	def do_render(self, lines, cmds): raise NotImplementedError("do_render")
	def do_activate(self): pass

	def handle_command(self, cmds): return self.do_handle_command(cmds)
	def do_handle_command(self, cmd): return False

	def switch_to(self, mode):
		self.session.switch_to(mode)

	def revert(self, n=1):
		check(self.session.mode == self, "session.mode != self")
		return self.session.revert(n)

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
	safe_term_width = property(lambda self: Con.safe_width(self.session.term_width))
	prev_mode = False # запомнит предыдущий режим, т. о. к нему можно будет вернуться

class MainMenu(Mode):
	def do_render(self, lines, cmds):
		def add_multi(synonims, *args):
			for cmd in synonims:
				cmds.add(cmd, *args)

		ci = 1
		lines.extend([
			               "        VISIBLE FIGHTERS v.{0}       ".format(".".join(str(part) for part in version)),
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
		game.player.set_weapon(Weapon())
		game.next_level = 1
		self.switch_to(AskName(game))

	Help = \
		"Ваш автомат — живой, и при использовании в бою ему будет перенаправлена часть опыта. Пули пробивают броню, но не масштабируются статами персонажа.\n"\
		"\n"\
		"Сила      (STR) — |влияет на силу ударов и максимум HP.\n"\
		"Интеллект (INT) — |на максимум маны, силу заклинаний и сопротивление магии.\n"\
		"Ловкость  (DEX) — |на точность атаки, шанс уворота и критических ударов.\n"\
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
		return min(max(3, ok_count), len(previews.items) - start if down else start)

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
			count = self.estimate_items_count(self.first, down=False)
			check(count, count > 0, "count")
			self.first_up = self.first - count
			self.show_up = count
		else:
			self.first_up = None

	def do_render(self, lines, cmds):
		if self.first_up is not None:
			lines.append(f"({1 + self.first_up}–{self.first_up + self.show_up}) (up)")
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
			cmds.add('remove all', self.create_batch_remove_handler(None, "Все"), '?', lambda: self.more("Удалить все сохранения."))
			remove_inscriptions.append('remove all')

		if any(item.bad for item in self.session.previews.items):
			remove_inscriptions.append('remove bad')
			cmds.add('remove bad', self.create_batch_remove_handler(lambda item: item.bad, "Повреждённые", default_yes=True),
				'?', lambda: self.more("Удалить повреждённые сохранения."))

		if self.first_dn is not None:
			lines.append(f"\n({1 + self.first_dn}–{self.first_dn + self.show_dn}) (down)")
			cmds.add('down', lambda: self.down(), '?', lambda: self.more("Прокрутить список вниз."))

		lines.append("\nУдалить сохранение ({0})".format(", ".join(remove_inscriptions)))
		lines.append("Вернуться в главное меню (quit)")
		cmds.add('force update', lambda: self.force_update(), '?', lambda: self.more("Перечитать все сохранения."))
		cmds.add('quit', lambda: self.switch_to(MainMenu()), '?', lambda: self.more("Вернуться в главное меню."))

	def do_handle_command(self, cmd):
		if cmd == "":
			if not self.something_new:
				self.up_new_miss = self.session.previews.update()
				if not self.up_new_miss:
					if self.first_dn is not None: self.down()
					else: self.first = 0
			return True

	def up(self):
		self.first = check(self.first_up, self.first_up is not None, "first_up?!") # а show всё равно обновится в process

	def down(self):
		self.first = check(self.first_dn, self.first_dn is not None, "first_dn?!")

	def save_desc(self, item, pad, first_line_extra=None):
		cmd = "({0}) ".format(1 + item.index).ljust(pad)
		return cmd + item.load_screen_desc(npad = pad, first_line_extra=first_line_extra)

	def remove_save(self, item, extra_reverts=0, note_success=False):
		try:
			Game.remove_known_save(self.session, item.full_save_path, item)
			if note_success: self.more("Сохранение удалено.").reverts(1 + extra_reverts)
			return True
		except Exception as e:
			self.more("Не удалось удалить сохранение.\n" + exception_msg(e)).reverts(1 + extra_reverts)

	def create_load_request_handler(self, item, desc_pad):
		check(item.preview, "preview?!")
		def confirm_load(input, mode):
			if not input or 'yes'.startswith(input):
				try:
					with open(item.full_save_path, 'rb') as f:
						game = Game.load(f, item.full_save_path, item.rel_save_path)
				except Exception as e:
					mode.more("Не удалось загрузить игру.\n" + exception_msg(e)).reverts(2)
					self.session.previews.force_bad(item, e)
				else:
					mode.more("Загрузка...").then(lambda mode: mode.switch_to(Respite(game)))
			else:
				mode.revert()

		def handler():
			self.prompt("\n{0}\n\nЗагрузить эту игру? (Y/n) ".format(self.save_desc(item, desc_pad)), confirm_load)
		return handler

	def create_remove_request_handler(self, item, desc_pad, extra_reverts=0):
		def confirm_remove(input, mode):
			if not input and item.bad or input and 'yes'.startswith(input):
				self.remove_save(item, 1 + extra_reverts, note_success=True)
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

	def create_batch_remove_handler(self, predicate, capitalized_saves_desc, default_yes=False):
		def remove():
			total = sum(1 for item in self.session.previews.items if not predicate or predicate(item))
			def confirm(input, mode):
				removed = 0
				if (not input and default_yes) or input and 'yes'.startswith(input):
					for item in reversed(self.session.previews.items):
						if (not predicate or predicate(item)) and not self.remove_save(item, extra_reverts=1):
							check(isinstance(self.session.mode, More), "сейчас должно висеть сообщение об ошибке remove_save")
							self.session.mode.msg += "\n\n{0}, {1}.".format(plural(removed, "{N} файл{/а/ов} удал{ён/ены/ены}"),
								plural(total - removed, "{N} не обработан{/о/о}"))
							break
						removed += 1
					else:
						mode.more("{0} сохранения удалены.".format(capitalized_saves_desc)).reverts(2)
				else:
					mode.revert()
			self.prompt("Удалить {0}? (y/N) ".format(plural(total, "{N} сохранени{е/я/й}")), confirm)
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
		self.continuation = lambda mode: mode.revert(self._reverts)
		self.user_continuation = False

	def do_render(self, lines, cmds):
		lines.append(wrap(self.msg + ("" if self.input_comes else "\n<enter>"), self.safe_term_width))

	def do_handle_command(self, cmd):
		self.continuation(self)
		return True

	def then(self, what):
		check(not self.user_continuation, "Продолжение уже задано.")
		self.user_continuation = True
		self.continuation = what

	def reverts(self, n):
		self._reverts = check(n, n > 0, "n?!")
	input_comes = False

class Prompt(More):
	def __init__(self, msg, callback, casefold_input=True):
		super().__init__(msg)
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
			'gold', 'next_level', 'timestamp',
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
			self.timestamp      = game and time.localtime()
			self.compress       = compress

		store_fields = [('character_uid', int), ('order_key', int),
			('player_name', bytes), ('player_level', int), ('player_next', (int, type(None))),
			('weapon_name', bytes), ('weapon_level', int), ('weapon_next', (int, type(None))),
			('gold', int), ('next_level', int), ('timestamp', int)]

		def to_list(self):
			check(self.order_key, self.order_key is not None, "order_key?!")
			# save_version начинается с первого бита, а нулевой означает, используется ли сжатие
			# (возможность его выключить поддерживается, потому что мне иногда интересно посмотреть, ЧО ТАМ)
			return [save_version<<1 | int(self.compress)] + [
				int(time.mktime(self.timestamp)) if field == 'timestamp' else
				pcgxor(getattr(self, field).encode()) if field in ('player_name', 'weapon_name') else
				getattr(self, field)
				for field, _ in Game.Preview.store_fields]

		@staticmethod
		def from_list(d):
			pv = Game.Preview()
			if not isinstance(d, list) or len(d) < 1 or not isinstance(d[0], int):
				raise Game.corrupted_save_error()

			if d[0]>>1 != save_version or len(d) != 1 + len(Game.Preview.store_fields):
				raise Game.BadSaveError("Несовместимая версия сохранения.")  # хотя можно и совместимость устроить... даже просто не проверять
			pv.compress = bool(d[0] & 1)

			for index, (field, field_type) in enumerate(Game.Preview.store_fields, 1):
				value = d[index]
				if not isinstance(value, field_type): raise Game.corrupted_save_error(field + ": " + str(type(value)))
				elif field == 'timestamp': pv.timestamp = time.localtime(value)
				elif field in ('player_name', 'weapon_name'): setattr(pv, field, pcgxor(value).decode())
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
			'а' <= c <= 'я' or 'А' <= c <= 'Я' or c in 'ёЁ-!()[]' or c in ' .' and i > 0 and i < len(s)-1)

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
	def remove_from_save_folder(path):
		os.remove(path)
		try:
			os.rmdir(Game.SAVE_FOLDER)
		except OSError:
			pass

	@staticmethod
	def remove_known_save(session, full_path, rel_path_or_item):
		Game.remove_from_save_folder(full_path)
		session.previews.note_remove(rel_path_or_item)

	def will_autosave_to_new_file(self):
		return self.save_file_base_name != Game.SAVE_FILE_BASE_NAME_DONT_TOUCH and self.save_file_base_name != self.base_filename()

	def save(self, session, to_new_file=False, compress=True):
		# убедиться в существовании папки с сохранениями
		try:
			os.mkdir(Game.SAVE_FOLDER)
		except FileExistsError:
			pass

		# Придумать character_uid, если его ещё нет.
		# Единственное, для чего он нужен — суффиксы вида «-2» на экране загрузки для разных персонажей с одинаковыми именами.
		# Т. о. коллизии не критичны, 2**16=65536 достаточно. Ну не выведется с маленькой вероятностью суффикс, когда нужен, подумаешь.
		if self.character_uid is None:
			self.character_uid = randrange(2**16)

		# Вообще-то choose_order_key потенциально дёргает previews.update(), а она, в свою очередь, может сломать предположение,
		# что self.rel_save_path есть в previews. Это всё работает только благодаря удачному сочетанию случайностей
		# (choose_order_key дёргает update, только когда ему не сообщили имя существующего сохранения,
		# что возможно только при to_new_file or not self.rel_save_path, но в обоих этих случаях выполнение пойдёт по ветке note_add,
		# т. е. полагается, что rel_save_path И НЕ БЫЛО в previews).
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
					Game.remove_from_save_folder(self.full_save_path)

					# Но пошаманить над превью так, чтобы оно осталось на месте — с корректными order_key разницы не будет,
					# но если они сбились, это, в отличие от .note_remove + .note_add, оставит превью в старом месте списка.
					session.previews.note_update(self.rel_save_path, preview, full_path, rel_path)
				else:
					session.previews.note_add(full_path, rel_path, preview)

				# в обоих случаях автосохранение впредь будет выполняться в новый файл.
				self.full_save_path, self.rel_save_path, self.save_file_base_name = full_path, rel_path, base
			except:
				Game.remove_from_save_folder(full_path)
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
				Game.remove_from_save_folder(tmp_path)
				raise

	def save_nothrow(self, mode, then=None, note_success=False, to_new_file=False, extra_error_comment=None, compress=True):
		try:
			self.save(mode.session, to_new_file, compress=compress)
			if note_success:
				mode = mode.more("Игра сохранена.")
				if then: mode.then(lambda mode: then(True, mode.revert()))
			else:
				if then: then(True, mode)
			return True
		except Exception as e:
			mode = mode.more("Не удалось сохранить игру{0}.\n".format(extra_error_comment or "") + exception_msg(e))
			if then: mode.then(lambda mode: then(False, mode.revert()))

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
		for k in ('character_uid', 'gold', 'next_level'):
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

# Экран между боями.
class Respite(Mode):
	def __init__(self, game):
		super().__init__()
		self.game = game

	def describe_player(self, player, cmds, pad):
		desc = player.living_desc()

		need_heal_hp = player.hp < player.mhp
		def dhp_func(d):
			def modify():
				if d <= 0:
					player.ouch(-d, "dhp")
				else:
					player.cur_hp = min(player.cur_hp + d, player.mhp)
			return modify
		cmds.add('hp+', dhp_func(+1))
		cmds.add('hp-', dhp_func(-1))

		desc += "\n" +\
			pad + "HP: " + Con.vital_bar(player.hp, player.mhp) + f" {player.hp}/{player.mhp}"
		if need_heal_hp:
			cost = clamp(round((1 - player.hp / player.mhp) * 30 + 0.25 * (player.mhp - player.hp)), 1, 50)
			desc += " восстановить: ${0}".format(cost)
			if self.game.enough_gold_for(cost):
				desc += " (heal hp)"
				def heal_hp():
					self.game.take_gold(cost)
					player.cur_hp = player.mhp
					self.session.invalidate(self).more("Ваши раны исцелены.")
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

			need_heal_mp = player.mp < player.mmp
			desc += "\n" +\
				pad + "MP: " + Con.vital_bar(player.mp, player.mmp) + f" {player.mp}/{player.mmp}"
			if need_heal_mp:
				cost = clamp(round((1 - player.mp / player.mmp) * 40 + 0.5 * (player.mmp - player.mp)), 1, 70)
				desc += " восстановить: ${0}".format(cost)
				if self.game.enough_gold_for(cost):
					desc += " (heal mp)"
					def heal_mp():
						self.game.take_gold(cost)
						player.cur_mp = player.mmp
						self.session.invalidate(self).more("Ваша магическая энергия восстановлена.")
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
		game   = self.game
		player = game.player
		lines.append("ЛАГЕРЬ")
		lines.append(f"Золото: ${game.gold} (shop)\n")
		cmds.add('shop', lambda: self.switch_to(Shop(game)), '?', lambda: self.more("Магазин, где вы можете приобрести или продать апгрейды."))
		cmds.add('gold+', lambda: game.give_gold(100))
		cmds.add('xp+', lambda: player.receive_xp(10))
		cmds.add('xp-', lambda: player.drain_xp(10))
		cmds.add('wxp+', lambda: player.weapon.receive_xp(10))
		cmds.add('wxp-', lambda: player.weapon.drain_xp(10))

		pad = " " * (min(len(player.name), len(player.weapon.name)) + 2)
		lines.append(self.describe_player(player, cmds, pad))
		if player.weapon:
			lines.append("\n" + self.describe_weapon(player.weapon, cmds, pad))

		lines.append("\nследующий уровень (next)")
		lines.append(  "выйти             (quit)")
		cmds.add('next', lambda: self.to_next_level(), '?', lambda: self.more("Переход к следующему уровню."))
		cmds.add('quit', lambda: self.quit(), '?', lambda: self.more("Выход в меню (с сохранением)."))

	def do_handle_command(self, cmd):
		if cmd.strip() == 'split soul':
			self.split_soul()
			return True

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
			if input and 'yes'.startswith(input[:input.find('/')%(len(input)+1)]) or not input and default_yes:
				self.game.save_nothrow(mode, then=lambda success, mode: mode.switch_to(MainMenu()), compress=input.find('/r') < 0)
			elif input and 'quit'.startswith(input):
				mode.switch_to(MainMenu()) # без сохранения — но это долго объяснять пользователю, пусть просто не знает
			elif allow_suicide and 'suicide'.startswith(input) and len(input) >= 2:
				try:
					Game.remove_known_save(self.session, self.game.full_save_path, self.game.rel_save_path)
				except Exception as e:
					mode.more("Не удалось удалить сохранение.\n" + exception_msg(e)).then(lambda mode: mode.switch_to(MainMenu()))
				else:
					mode.switch_to(MainMenu())
			else:
				mode.revert()

		self.prompt("Выйти из игры? ({0}) ".format(highlight_variant("y/n", 0 if default_yes else 1)), handle_confirmation)

	def do_activate(self):
		self.session.globals.recent_fixed_name_proposals = 0

	def to_next_level(self):
		arena = Arena()
		arena.limit_squad_members(Game.PLAYER_SQUAD, 3)
		arena.limit_squad_members(Game.MONSTER_SQUAD, 3)
		arena.deny_any_new_squads()
		arena.add(self.game.player, Game.PLAYER_SQUAD, PlayerAI())

		rat = Fighter()
		rat.name = Noun.parse("{ручной крыс:a}")
		arena.add(rat, Game.PLAYER_SQUAD, DummyAI())

		rat = Fighter()
		rat.name = Noun.parse("{обычный крыс:a}")
		arena.add(rat, Game.MONSTER_SQUAD, DummyAI())

		rat = Fighter()
		rat.name = Noun.parse("{волшебный крыс:a}")
		with rat.save_relative_vitals():
			rat.base_mmp = 10
		rat.learn_spell(Firestorm())
		arena.add(rat, Game.MONSTER_SQUAD, DummyAI())
		arena.start()

		def on_leave():
			arena.dismiss()
		self.switch_to(ArenaView(self.game, arena, self.game.player, on_leave))

class Shop(Mode):
	prev_mode = True
	def __init__(self, game):
		super().__init__()
		self.game = game

	def do_render(self, lines, cmds):
		game, player, weapon = self.game, self.game.player, self.game.player.weapon
		lines.append("МАГАЗИН\n" +
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
		cmds.add('quit', lambda: self.revert(), '?', lambda: self.more("Вернуться в лагерь."))

	def buy_upgrade_func(self, target, up_cls):
		def buy():
			gold = up_cls.gold_cost(target)
			def confirm(input, mode):
				if input and 'yes'.startswith(input):
					self.game.take_gold(gold)
					up = up_cls()
					up.apply(target)

					msg = up.apply_message(target)
					# if msg: msg += f" (-${gold})"
					self.more(msg or f"Апгрейд приобретён за ${gold}.").reverts(2)
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
					msg = up.revert_message(target)
					# if msg: msg += f" (+${gold})"
					self.more(msg or f"Апгрейд продан за ${gold}.").reverts(2)
				else:
					mode.revert()
			self.prompt("В обмен на {what} вы получите ${gold}. Продолжить? (y/N) ".format(what=up.sell_accusative(target), gold=gold), confirm)
		return sell

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
			self.line_break_requested = False

		def add(self, msg, turn, *, next_sep=" "):
			# Критерии, по которым (не) начинается новая строка.
			# Совсем никогда не начинать нельзя, т. к. из истории не могут быть стёрты отдельные добавленные таким образом фрагменты — только строка целиком.
			def allow_continuation(prev):
				# pieces_count — подушка безопасности, ожидается, что такого не будет в естественных сценариях
				return not self.line_break_requested and prev.pieces_count < 666

			if self.lines and allow_continuation(self.lines[-1]):
				line = self.lines[-1]
				line.line += line.next_sep + msg
				line.turn = turn
				line.pieces_count += 1
			else:
				line = self.Line(msg, turn)
				self.lines.append(line)
				self.line_break_requested = False
			line.next_sep = next_sep

			# стереть старые строки
			erase = 0
			while erase < len(self.lines) and (turn - self.lines[erase].turn) > self.MIN_MESSAGE_LIFE_TURNS and len(self.lines) - (erase + 1) >= self.MIN_MESSAGES:
				erase += 1

			if erase > 0:
				if self.scroll_line < erase:
					self.scroll_line, self.scroll_index = 0, 0
				else:
					self.scroll_line -= erase
				del self.lines[:erase]

		# scroll возвращает (1) последние не более чем lines строк, которые пользователь должен увидеть в окне лога, и (2) флаг, есть ли ещё.
		# Одновременно, если really не вернула False, лог прокручивается вниз на lines-1 либо до упора.
		# Можно было бы разделить эти шаги, но это будет сложнее и мне не нужно (по сути — отложить присваивание scroll_line/scroll_index).
		def scroll(self, lines, width, really=lambda pending: True):
			# Попытаться идти с lines[scroll_line].line[scroll_index] до конца. Если конец не достигнут за lines — вернуть результат как промежуточный.
			wrapped = []
			last_line = last_index = None
			for i, line in enumerate(self.lines[self.scroll_line:], self.scroll_line):
				start = self.scroll_index if i == self.scroll_line else 0
				w = wrap_feedback(line.line[start:], width, lines - len(wrapped) + 1) # + 1 — отличить случай «есть ещё строки» от «больше нет строк»
				overflow = len(wrapped) + len(w) > lines
				if overflow: del w[lines - len(wrapped):]
				wrapped.extend(L.piece for L in w)

				if w: last_line, last_index = i, start + (w[-1].start if lines > 1 else w[-1].next)
				if overflow:
					# lines строк переполнены — вернуть промежуточный результат, продолжить с последней строки включительно
					# Бла         1        Бла-бла-бла 3
					# Бла-бла     2   =>   Бла-бла-бла-бла 4
					# Бла-бла-бла 3        Бла-бла-бла-бла-бла 5
					if really(True): self.scroll_line, self.scroll_index = (last_line, last_index) if last_line is not None else impossible()
					return wrapped, True

			# Конец достигнут? Тогда вернуть последние lines строк (возможно, уже виденных). Алгоритм с точностью до наоборот.
			wrapped, pos_saved = [], False
			for i in range(len(self.lines) - 1, -1, -1):
				w = wrap_feedback(self.lines[i].line, width)
				if not pos_saved and w:
					pos_saved = True
					if really(False): self.scroll_line, self.scroll_index = i, w[-1].start if lines > 1 else w[-1].next
				overflow = len(wrapped) + len(w) > lines
				if overflow: del w[:len(w) - (lines - len(wrapped))]
				wrapped = [L.piece for L in w] + wrapped
				if overflow: break
			return wrapped, False

		def post_line_break(self):
			self.line_break_requested = True

	def __init__(self, game, arena, player, on_leave):
		super().__init__()
		self.game  = game
		self.arena = arena
		self.player = player
		self.player_ai = arena.as_battler(player).ai
		check(self.player_ai, isinstance(self.player_ai, PlayerAI), "player.ai")
		self.on_leave = on_leave
		self.awaiting_decision = True
		self.atb_maximum = self.estimate_good_atb_maximum()

		self.log = ArenaView.MessageLog()
		self.sink = Arena.MessageSink(player, self.receive_note)
		self.arena.add_sink(self.sink)
		self.shown_log_lines = None
		self.next_player_turn = -1

	def do_process(self):
		self.awaiting_decision = False
		self.do_prompt = True
		log_area_height = 5
		do_turn = True
		while do_turn:
			if self.arena.whose_turn() == self.game.player and not self.player_ai.decision:
				do_turn = False
				self.log.post_line_break()

			lines, pending = self.log.scroll(log_area_height, self.safe_term_width, really=lambda pending: pending or not do_turn)
			if pending:
				self.shown_log_lines = None
				self.do_prompt = False
				self.session.invalidate(self).more("\n" + "\n".join(lines))
				return

			if do_turn:
				if self.arena.whose_turn() == self.game.player:
					self.next_player_turn += 1
					self.log.add("_", turn=self.next_player_turn, next_sep="")
				self.arena.turn()

		self.shown_log_lines = lines
		self.awaiting_decision = self.arena.whose_turn() == self.game.player

	def do_render(self, lines, cmds):
		squadA, squadB = tuple(heapq.nsmallest(2, self.arena.squads.keys()))
		imA = self.build_squad_image(squadA, None, None, False)
		imB = self.build_squad_image(squadB, None, None, True)
		for lineno in range(max(len(imA), len(imB))):
			left = imA[lineno] if lineno < len(imA) else ""
			right = imB[lineno] if lineno < len(imB) else ""

			limit = self.safe_term_width
			if len(left) + len(right) > limit:
				left = left[:limit - len(right)]
				if len(left) + len(right) > limit: raise RuntimeError(f"Строка не умещается в ширину консоли: {left + '/' + right}.")
			lines.append(left + " " * (limit - len(left) - len(right)) + right)

		if self.shown_log_lines:
			lines.append("")
			lines.extend(self.shown_log_lines)

		def hex_func(cls, fighter):
			def hex():
				def note(sink):
					msg = "Вы накладываете"
					if fighter == sink.you: msg += " на себя"
					msg += " " + cls.generic_name()
					if fighter != sink.you: msg += " на " + fighter.name(Case.ACCUSATIVE)
					msg += "."
					return msg
				self.arena.note(lambda sink: note(sink))
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
					elif cls == RageHex: args = (100, 10)
					else: args = (100, 10)
					cls(*args).apply(self.player, fighter)
			return lambda: self.decide(hex)
		for b in self.arena.battlers:
			cmds.add('bleed' + ('' if b.fighter == self.player else ' ' + b.shortcut), hex_func(Bleeding, b.fighter))
			cmds.add('rage' + ('' if b.fighter == self.player else ' ' + b.shortcut), hex_func(RageHex, b.fighter))
			cmds.add('deathword' + ('' if b.fighter == self.player else ' ' + b.shortcut), hex_func(DeathWordHex, b.fighter))
		cmds.add('quit', lambda: self.quit())

	def do_handle_command(self, cmd):
		if not cmd:
			if self.awaiting_decision:
				def skip_turn(sink):
					if sink.you == self.player: return "Вы пропускаете ход."
					else: return f"{cap_first(self.player.name)} пропускает ход."
				self.decide(lambda: self.arena.note(lambda sink: skip_turn(sink)))
			return True

	def decide(self, what):
		check(self.awaiting_decision, "не вовремя")
		self.player_ai.decide(what)

	def quit(self):
		self.arena.remove_sink(self.sink)
		if self.on_leave: self.on_leave()
		self.game.save_nothrow(self, then=lambda success, mode: mode.switch_to(Respite(self.game)))

	def build_squad_image(self, squad, cmds, lines_limit, flip):
		squad = self.arena.squads[squad]
		class PerBattler:
			def __init__(self, fighter, battler):
				self.fighter, self.battler = fighter, battler
				self.lines = []
				self.hex_descs = []
				self.hexes_gen = fighter.actual_hexes()
		per_battler = []
		total_lines = max(0, len(squad.members) - 1) # пустые строки между описаниями участников

		# Обязательные строки.
		for b in squad.members:
			fighter = b.fighter
			im = PerBattler(fighter, b)
			# (N) Некромант AC:6 EV:10
			im.lines.append(left_to_right(f"({b.shortcut})",
				cap_first(fighter.name), fighter.ac > 0 and f"AC:{fighter.ac}", fighter.ev > 0 and f"EV:{fighter.ev}", flip=flip))
			total_lines += 1

			if fighter.dead:
				im.lines.append("RIP")
				total_lines += 1
			else:
				def bar(name, cur, max):
					return left_to_right(name + ("" if flip else ":"), Con.vital_bar(cur, max), f"{cur}/{max}", flip=flip)
				im.lines.append(bar("HP", fighter.hp, fighter.mhp))
				total_lines += 1

				if fighter.has_magic():
					im.lines.append(bar("MP", fighter.mp, fighter.mmp))
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
					im.hex_descs.append(hex.short(cmd_prefix=self.hex_cmd_prefix(hex, per_battler[i].battler), for_multipad=True, flip=flip))
					total_lines += 1
					something_changed = True
					if lines_limit is not None and total_lines >= lines_limit: break
			if not something_changed: break
		for im in per_battler:
			im.hex_descs = multipad(im.hex_descs)

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

	# Шкала очерёдности хода. В итоге по ней мало что можно понять, так что не используется.
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

	def receive_note(self, msg):
		self.log.add(msg, self.next_player_turn)

class AskName(Prompt):
	def __init__(self, game, who=None, fixed=None):
		self.game, self.who = game, who or game.player
		prompt = (
			"Вам нужно зарегистрироваться, прежде чем вас официально освободят.\nКак вас зовут? " if self.who == self.game.player else
			"\nНазовите свой автомат, {0}: ".format(self.game.player.name) if self.who == self.game.player.weapon else
			impossible(self.who, "who"))
		super().__init__(prompt, lambda input, mode: self.handle_name_input(input, mode), casefold_input=False)
		self.fixed = fixed

	def handle_name_input(self, input, mode):
		MIN, MAX = 3, 20
		gender = Gender.UNKNOWN
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
						name, gender = Noun.parse(self.fixed[0] if isinstance(self.fixed, tuple) else self.fixed, animate=True, gender=Gender.MALE, return_gender=True)
						self.session.globals.recent_fixed_name_proposals += 1
					else:
						rand = Noun.random_name(
							ban = lambda type, part: part in self.session.globals.last_random_name_parts_seen or
								self.session.previews.has_namesakes_of(part, {'adj': 'prefix', 'noun': 'suffix'}[type]),
							see = lambda _type, part: self.session.globals.last_random_name_parts_seen.append(part), return_gender=True)
						if rand:
							name, gender = rand
						else:
							return mode.more("Случайные имена закончились. Пожалуйста, придумайте своё.")
				elif self.who == self.game.player.weapon:
					if self.fixed and isinstance(self.fixed, tuple) and len(self.fixed) >= 2:
						if isinstance(self.fixed[1], tuple):
							name_src, _index = choose(self.fixed[1])
						else:
							name_src = self.fixed[1]
						name, gender = Noun.parse(name_src, gender=Gender.MALE, return_gender=True)
					else:
						name, gender = Noun.parse("{Хуец}" if self.game.player.gender == Gender.FEMALE else "GAU-17", gender=Gender.MALE, return_gender=True)
				else: impossible(self.who, "who")

			mode.prompt(
				"{0} {1} (Y/n) ".format(
					(f"Очень приятно, {name}." if input else f"Ваше имя — {name}.") if self.who == self.game.player else
					(f"В ваших руках {name}." if input else f"Имя вашего автомата — {name}.") if self.who == self.game.player.weapon else
					impossible(self.who, "who"),
					"Всё верно?" if input else "Продолжить?"),
				lambda input, mode: self.complete_name(name, gender, mode) if not input or 'yes'.startswith(input) else mode.revert())
		elif 'quit'.startswith(input):
			mode.revert()
		else:
			mode.more("{0}. Длина имени должна быть от {1} до {2}.".format(
				plural(len(input), "Введ{ён/ено/ено} {N} символ{/а/ов}"), MIN, plural(MAX, "{N} символ{/а/ов}")))

	def complete_name(self, name, gender, mode):
		if gender == Gender.UNKNOWN and self.who == self.game.player:
			default_gender = Gender.detect(name)
			mode.prompt("Вы мальчик или девочка? ({0}/q) ".format(highlight_variant("m/f", default_gender)),
				lambda input, mode: self.handle_gender_answer(input, mode, name, default_gender))
		else:
			self.complete(name, gender)

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

	def complete(self, name, gender):
		it_was_user_input = not isinstance(check(name, isinstance(name, str), "name"), Noun)
		if it_was_user_input: name = Noun.guess(name, gender=gender, animate=True)
		self.who.name, self.who.gender = name, gender
		if self.who == self.game.player:
			# В handle_name_input выставляется fixed, т. о. если имя и пол на этот момент соответствуют последней fixed, полагается, что пользователь согласился.
			fixed = self.fixed and name == Noun.parse(self.fixed[0] if isinstance(self.fixed, tuple) else self.fixed) and self.fixed
			self.session.switch_to(AskName(self.game, self.game.player.weapon, fixed=fixed))
		elif self.who == self.game.player.weapon:
			self.game.save_nothrow(self, then=lambda success, mode: mode.switch_to(Respite(self.game)))
		else:
			impossible(self.who, "who")

	fixed_names = \
		"{Рика:f}", \
		("{Мадока:f}", ("{Розочка:f}",)), \
		("{Фрисия:f}", "{Хвост}")

	def query_random_fixed_name(self):
		seen, previews = self.session.globals.last_fixed_names_seen, self.session.previews
		get_name_weight = lambda name, index: 0.0 if index in seen or previews.has_namesakes_of(Noun.parse(name[0] if isinstance(name, tuple) else name)) else 1.0
		name, index = choose(AskName.fixed_names, get_name_weight, None)
		if index >= 0:
			seen.append(index)
			return name # else None

# Ввод-вывод, стек экранов, глобальности.
class Session:
	__slots__ = ('mode', 'quit_posted', 'cls_once_requested', 'term_width', 'term_height', 'previews', 'globals')
	def __init__(self, start=None):
		self.mode               = None
		self.quit_posted        = False
		self.cls_once_requested = False
		self.term_width = self.term_height = None
		self.previews           = Session.PreviewsList()
		self.globals            = Session.Globals()
		self.switch_to(start or MainMenu())

	def switch_to(self, new_mode, reverting=False):
		check(isinstance(new_mode.prev_mode, bool) or new_mode == self.mode.prev_mode, "prev_mode?!")
		# запомнить prev_mode только при условии, что а) это явно требуется (prev_mode = True) и б) это не возврат к prev_mode
		if new_mode.prev_mode and not reverting: new_mode.prev_mode = self.mode
		self.mode = new_mode
		self.mode.session = self
		if not reverting: self.mode.do_activate()

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
		# (TODO: сделать её опционально. У меня нет Linux, чтобы тестировать как-их-там-спецпоследовательности, но на Windows есть SetConsoleCursorPosition.)
		if self.mode.do_cls or self.cls_once_requested: cls()
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
		if self.term_width < config.min_term_width or self.term_height < config.min_term_height:
			self.mode.more(
				f"Размер консоли — {self.term_width}x{self.term_height}.\n"\
				f"Увеличьте хотя бы до {config.min_term_width}x{config.min_term_height}.", do_cls=True)

	def add_default_commands(self, cmds):
		cmds.add("?", lambda: self.mode.more(Session.list_available_commands(cmds)))

	@staticmethod
	def list_available_commands(cmds):
		av = ", ".join(cmd for cmd in cmds.suggest_something() if cmd != "?")
		return "Доступные команды: " + av + "." if av else "Нет доступных команд."

	def cls_once(self):
		self.cls_once_requested = True
		return self.mode

	# Обычно родительские режимы не перерендериваются, а используется запомненная с последнего render картинка.
	# invalidate форсирует перерисовку. Пример: после команды heal hp полоска немедленно перерисовывается, несмотря на то, что активно more-сообщение.
	def invalidate(self, mode):
		lines = []
		mode.render(lines, DummyCommands())
		mode.last_screen = "\n".join(lines)
		return self.cls_once()

	# Чтобы, например, вложенные more-сообщения корректно убирались, оставляя предыдущие,
	# экран очищается и всё, что на нём должно было быть — перерисовывается.
	def render_prev_modes(self, lines):
		chain, mode = [], self.mode
		while mode:
			if mode != self.mode: chain.append(mode)
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

			def load_screen_desc(self, npad=0, first_line_extra=None):
				star = "*NEW* "
				if not self.seen: npad += len(star)
				pad = ' ' * npad
				if self.bad:
					bad_msg = "\n".join((pad if i > 0 else "") + exception_msg(e) for i, e in enumerate(self.bad))
					if not bad_msg or not isinstance(self.bad, Game.BadSaveError) and bad_msg.find('оврежд') < 0 and bad_msg.find('orrupt') < 0:
						bad_msg = "Файл повреждён." + (("\n" + pad + bad_msg) if bad_msg else "")
					if first_line_extra:
						bad_msg = bad_msg.splitlines() or [""]
						bad_msg[0] += first_line_extra
						bad_msg = "\n".join(bad_msg)
					return "{0}\n{pad}[{1}]".format(bad_msg, self.full_save_path, pad = pad)
				else:
					pv = self.preview
					dup_desc = f"-{1+self.namesake_index}" if self.namesake_index >= 1 else ""
					return ("{star}{ts}{fle}\n" +
						"{pad}{pn}{dd} {pl}\n" +
						"{pad}{wn} {wl}\n" +
						"{pad}D:{coming} ${gold}").format(
						ts = time.asctime(pv.timestamp), fle = first_line_extra or "",
						pn = pv.player_name, dd = dup_desc, pl = Living.xl_desc(pv.player_level, pv.player_next, short=True),
						wn = cap_first(pv.weapon_name), wl = Living.xl_desc(pv.weapon_level, pv.weapon_next, short=True),
						coming = pv.next_level, gold = pv.gold,
						pad = pad, star = '' if self.seen else star)

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
			try:
				# walk: folder ⇒ dirpath, dirnames, filenames
				listing.extend(fn for fn in next(os.walk(Game.SAVE_FOLDER))[2] if fn.endswith(Game.SAVE_SUFFIX))
			except StopIteration:
				# Папки не существовало
				pass
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

			# помочь пользователю различить разных персонажей с одинаковыми именами
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

			if item.preview:
				# пересчитать max_order_key, если он соответствовал удалённой записи
				if item.preview.order_key == self.max_order_key: self.max_order_key = self.calculate_max_order_key()
				self.update_namesakes(of=item.preview.player_name)
			assert self.sanitycheck()

		def calculate_max_order_key(self):
			return max(self.order_keys(), default=-1)

		def order_keys(self, include_bad=False):
			return (item.preview.order_key if item.preview else -1 for item in self.items if item.preview or include_bad)

		def fix_indices(self, start=0, end=None):
			for index in range(start, end if end is not None else len(self.items)):
				self.items[index].index = index

		def update_namesakes(self, of=None):
			name2namesakes = dict()
			for item in reversed(self.items):
				pv = item.preview
				if not pv or of is not None and pv.player_name != of: continue

				namesakes = name2namesakes.get(pv.player_name, None)
				if not namesakes: namesakes = name2namesakes[pv.player_name] = dict()

				id = namesakes.get(pv.character_uid, None)
				if id is None: id = namesakes[pv.character_uid] = len(namesakes)
				item.namesake_index = id

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
			item.preview = None
			if item.index is not None:
				old_index = item.index
				assert self.items[item.index] is item
				del self.items[item.index]
				item.index = self.find_position_for(item)
				self.items.insert(item.index, item)
				self.fix_indices(*(item.index + 1, old_index + 1) if item.index < old_index else (old_index, item.index))
				assert self.sanitycheck()

		def find_position_for(self, item):
			return bisect_left(list(-order_key for order_key in self.order_keys(include_bad=True)), -(item.preview.order_key if item.preview else -1))

		def has_namesakes_of(self, name, mode='full'): # это очень медленно...
			name = name.casefold()
			hit = (lambda playername: playername == name) if mode == 'full' else \
				(lambda playername: playername.startswith(name)) if mode == 'prefix' else \
				(lambda playername: playername.endswith(name)) if mode == 'suffix' else impossible(mode, "mode")
			return any(item.preview and hit(item.preview.player_name.casefold()) for item in self.items)


		def sanitycheck(self):
			assert len(self.items) == len(self.fn2it) == len(self.last_listing) and \
				set(item.rel_save_path for item in self.items) == \
				set(self.fn2it.keys()) == \
				set(self.last_listing), self.debug_repr() and \
				all(item.index == i for i, item in enumerate(self.items))
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

def selftest():
	tests, fails = [], []
	account = False
	def run(name, cases, one):
		count = 0
		for case in cases:
			try:
				one(*case)
			except Exception as e:
				fails.append("Тест {0} #{1} {2}. {3}".format(name, count, "провален" if isinstance(e, Test.Failed) else "упал",
					exception_msg(e) if isinstance(e, Test.Failed) else format_exc()))
			count += 1
		if account: tests.append(name + (f" x{count}" if count > 1 else ""))

	if account: ticks = time.clock()
	for name, value in globals().items():
		if isinstance(value, type) and issubclass(value, Test) and value is not Test:
			test = value()
			test.setup()
			run(name[:-len("Test")] if name.endswith("Test") and len(name) > len("Test") else name, test.cases, test.one)
			test.teardown()
	if account: ticks = time.clock() - ticks

	if fails:
		raise Test.Failed("\n".join(fails))
	elif account:
		print("Тесты пройдены ({0} мс): {1}.".format(round(ticks*1000, 1), ", ".join(tests)))
		input()

def main():
	selftest()
	session = Session()
	while session.process(): pass

if __name__ == "__main__": main()