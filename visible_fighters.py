min_python_version = (3, 6) # меньше нельзя, f-строки слишком хороши...
import sys, os, os.path as path, tempfile, pickle, pickletools, lzma, textwrap, bisect, hashlib, functools, locale, argparse, io, re, heapq, sqlite3, code
from collections import namedtuple, OrderedDict, defaultdict, deque
from collections.abc import Sequence, Mapping
from enum import IntEnum
from string import Formatter, whitespace, digits
from time import localtime, mktime, strftime, strptime
from datetime import date
from random import random, randrange, uniform, normalvariate, sample, shuffle
from base64 import b85encode, b85decode
from math import floor, ceil, exp, log, log2, e, pi, erf, fsum
from numbers import Number
from contextlib import suppress, AbstractContextManager, closing
from operator import gt, ge, le, or_, itemgetter
from itertools import accumulate, count as infinite_range
from unittest import TestCase, TestSuite, TextTestRunner, defaultTestLoader
from warnings import warn, catch_warnings
from traceback import format_exc
app_version, save_version, HoF_version = (1, "01"), 1, 1
TRACEBACKS = False

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

def throw(e_or_cls, *args):
	raise e_or_cls(*args) if isinstance(e_or_cls, type) else e_or_cls

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
	return "".join(literal + handle(bracketed) for literal, bracketed, _spec, _conv in Formatter.parse(None, fmt))

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

# Сейчас не используется, т. к. крайние случаи практически не встречаются и достаточно "{:.0%}".format(value).
# Задумано, чтобы
# (1) округлять отображаемые оценки вверх в защите и вниз в атаке:
#     шанс в 1.1%, что враг попадёт по игроку, будет округлён до 2%, а что игрок попадёт по врагу — до 1%.
# (2) там, где на самом деле 0.1% или 99.9%, показывать 1% и 99% вместо 0% и 100%.
def percentage(value, rounding='round'):
	pp = (round if rounding == 'round' else ceil if rounding == 'up' else floor if rounding == 'down' else impossible(rounding, "rounding"))(100 * value)
	if pp == 0 and value > 0: pp = 1
	if pp == 100 and value < 1: pp = 99
	return pp

# используется для распределения строк по элементам интерфейса
# base — начальные значения, extra — сколько раскидать, lim — максимальные (опционально).
# например: dispense([1, 2, 3], 3) => [2, 3, 4], каждая получила по 1.
# другой пример (ниже описан по итерациям): dispense([1, 2, 3], 25, lim=[5, 10, 20]) => [5, 10, 16].
def dispense(base, extra, lim=None):
	assert not lim or len(lim) == len(base), "len(base) = {len(base)}, len(lim) = {len(lim)}"
	result = base[:]

	# йелдит (i, wanted), где i — индекс в result / lim, а wanted — максимум, сколько можно ещё упихать в эту ячейку (None, если сколько угодно).
	def eligible():
		for i in range(len(result)):
			if (lim and lim[i]) is None or lim[i] > result[i]:
				yield i, lim and lim[i] and lim[i] - result[i]

	# Раскидывать всем, кому раскидывается (кто eligible), поровну.
	# Для [1, 2, 3], extra=25, lim=[5, 10, 20] это сделает:
	# на первой итерации — [5, 6, 7], т. е. всем по 4, extra = 25 - 4×3 = 13
	# на второй итерации — [5, 10, 11], т. е. 2-й и 3-й по 4, extra = 13 - 4×2 = 5
	# на третьей итерации — [5, 10, 16], т. е. 3-й всё оставшееся, extra = 0
	while extra > 0:
		eligible_count, lesser_common_dose = 0, None

		for i, wanted in eligible():
			eligible_count += 1
			if wanted and (not lesser_common_dose or wanted < lesser_common_dose): lesser_common_dose = wanted

		if not eligible_count: break # выйти, если реципиентов не осталось
		for_one = min(filter(None, (max(extra // eligible_count, 1), lesser_common_dose)))

		for i, _wanted in eligible():
			assert _wanted is None or _wanted >= for_one
			result[i] += for_one
			extra -= for_one
			if extra <= 0: break # и внешний while тоже
	return result

# Строит таблицу по строкам (rows) и столбцам (columns), возвращает список str.
# rows и columns — последовательности чего угодно.
# get_cell получает по одному элементу из rows и columns, и должна вернуть текст в соотв. ячейке (можно None).
#
# например
# > pretty_table(('A', 'BB', 'CCC'), ('1', '2', '3', '4'), get_cell=lambda row, column: row + column)
# даёт
# ['  A1   A2   A3   A4',
#  ' BB1  BB2  BB3  BB4',
#  'CCC1 CCC2 CCC3 CCC4'].
def pretty_table(rows, columns, get_cell=lambda row, column: "-", width=None, *, ljust=lambda row, column: 0):
	data = []
	if not isinstance(columns, Sequence): columns = list(columns)
	col_pads = [0] * len(columns)

	for row in rows:
		row_data = []

		for column_index, column in enumerate(columns):
			cell_data = get_cell(row, column) or ""
			if len(cell_data) > col_pads[column_index]: col_pads[column_index] = len(cell_data)
			row_data.append((cell_data, ljust(row, column)))
		data.append(row_data)

	if width is not None:
		# не очень хорошая идея использовать здесь dispense... как минимум нужна другая стратегия, нежели используется там, ну да ладно.
		col_pads = dispense(col_pads, width - sum(col_pads) - max(0, len(col_pads) - 1) * len(" "),
			lim=[0 if column_index == 0 else round(1.5 * (col_pads[column_index] + 1)) for column_index in range(len(columns))])

	return [
		"".join(
			cell_data.rjust(col_pad - ljust).ljust(col_pad) + (" " if column_index + 1 < len(col_pads) else "")
			for column_index, ((cell_data, ljust), col_pad) in enumerate(zip(row_data, col_pads)))
		for _row_index, row_data in enumerate(data)]

def join_with_lastsep(seq, sep, lastsep):
	if not isinstance(seq, Sequence): seq = list(seq)
	return (sep.join(seq[:-1]) + lastsep if len(seq) > 1 else "") + (seq[-1] if seq else "")

def human_datetime(timestamp, do_date=True, do_sep=False, do_time=True):
	def custom_date(timestamp):
		with suppress(IndexError): return cap_first(("сегодня", "вчера", "позавчера")[date.today().toordinal() - date(*timestamp[:3]).toordinal()])

	return "{}{}{}".format(
		custom_date(timestamp) or "{}{}{}".format(
			strftime('%d ', timestamp).lstrip('0'),
			strftime('%B ', timestamp).lower().replace('ь ', 'я ').replace('т ', 'та ').replace('й ', 'я '), # Угу.
			strftime('%Y', timestamp)) if do_date else "",
		", " if do_sep or do_date and do_time else "",
		strftime('%H:%M', timestamp) if do_time else "")

# Base65536, обфусцированный клон https://github.com/Parkayun/base65536 (Python) / https://github.com/qntm/base65536 (TypeScript).
class b65k:
	BLOCK_START = list(accumulate({-1: 21, 0: 31, 25: 2, 106: 3, 109: 2, 110: 97, 111: 26, 114: 14, 118: 17, 120: 35, 122: 151}.get(i, 1) for i in range(-1, 256)))
	B2 = {v: k for k, v in enumerate(BLOCK_START, -1)}

	@classmethod
	def encode(b65k, value):
		return ''.join(chr((b65k.BLOCK_START[1 + value[x + 1] if x + 1 < len(value) else 0] << 8) + value[x]) for x in range(0, len(value), 2))

	@classmethod
	def decode(b65k, value):
		def gen():
			b2 = 0
			for code_point in map(ord, value):
				if b2 == -1: raise ValueError("base65536 sequence continued after final byte")
				try:
					b1, b2 = code_point & 0xFF, b65k.B2[code_point >> 8]
				except KeyError:
					raise ValueError(f"Invalid base65536 code point: {code_point}") from None
				yield b1
				if b2 != -1: yield b2
		return bytes(gen())

def makefuncs():
	def maybewrite(file, string):
		if file is not None:
			with open(file, 'w', encoding='utf-8-sig') if isinstance(file, str) else nullcontext(file) as f: f.write(string)
		return string
	dispatch = {'b85': (lambda blob: b85encode(blob).decode('ascii'), b85decode), 'b65k': (b65k.encode, b65k.decode)}
	def encode(blob, format='b65k'): return dispatch[format][0](blob)
	def decode(string, format='b65k'): return dispatch[format][1](string)

	# Сжимает строку в кашу, которую можно будет записать в исходнике короче оригинала.
	# Опционально читает из файла, записывает в файл и/или форматирует через pretty_decl.
	def pack_str(src=None, encoding='koi8-r', *, infile=None, outfile=None, format='b65k', **prettyargs):
		if infile is not None:
			with open(infile, 'r', encoding='utf-8-sig') if isinstance(infile, str) else nullcontext(infile) as f: src = f.read()
		result = encode(lzma.compress(src.encode(encoding), **LZMA_OPTIONS), format)
		return maybewrite(outfile, pretty_decl(result, **prettyargs) if prettyargs else result)

	# Распаковывает результат pack_str, опционально в файл.
	def unpack_str(src, encoding='koi8-r', *, outfile=None, format='b65k'):
		return maybewrite(outfile, lzma.decompress(decode(src, format), **LZMA_OPTIONS).decode(encoding))
	return encode, decode, pack_str, unpack_str
encode, decode, pack_str, unpack_str = makefuncs(); del makefuncs

# Красивенько форматирует строку (предположительно длинную, предположительно результат pack_str) в питонье объявление.
# длина ограничивается width с учётом prefix, pad и кавычек; символы НЕ эскейпаются, поэтому при "\ в строке результат будет не валиден.
def pretty_decl(s, width=160, prefix="", pad="\t", cont_pad=None, multiline=False):
	if width < 1: raise ValueError("width должна быть >= 1")
	if cont_pad is None: cont_pad = "" if multiline else pad
	def pieces_gen():
		sp = 0
		start = pad + prefix + ("" if multiline else "(")
		opening_quotes, ending_quotes = '"""' if multiline else '"', '"""' if multiline else '"'
		cont_opening_quotes, cont_ending_quotes = "" if multiline else '"', "" if multiline else '"'
		if len(start) + len(opening_quotes) >= width: yield start + ("\\" if multiline else ""); start = cont_pad
		start += opening_quotes
		if multiline and len(start) + len('\\') >= width: yield start + "\\"; start = cont_pad

		while True:
			if len(s) - sp <= max(0, width - len(start) - len(ending_quotes)): yield start + s[sp:] + ending_quotes + ("" if multiline else ")"); return
			take = max(1, width - (len(start) + len(cont_ending_quotes)))
			yield start + s[sp:sp+take] + cont_ending_quotes; sp += take
			start = cont_pad + cont_opening_quotes
	return "\n".join(pieces_gen())

def pickle_dump(obj, file=None):
	data = pickletools.optimize(pickle.dumps(obj, protocol=-1))
	if file: file.write(data)
	return data

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

def skip_whitespace(s, pos=0):
	while pos < len(s) and s[pos] in whitespace: pos += 1
	return pos

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
class SequenceMap:
	def __init__(self, list, key, start=0): self.list, self.key, self.start = list, key, start
	def __getitem__(self, i): return self.key(self.list[self.start + i if i >= 0 else i])
	def __len__(self): return len(self.list) - self.start

def makefuncs():
	def with_key(origf):
		def keyed(a, x, L=0, R=None, key=None):
			return origf(a if key is None else SequenceMap(a, key), x if key is None else key(x), L, len(a) if R is None else R)
		return keyed
	bisect_left, bisect_right = with_key(bisect.bisect_left), with_key(bisect.bisect_right)
	def insort_right(a, x, L=0, R=None, key=None): a.insert(bisect_right(a, x, L, R, key), x)
	return bisect_left, bisect_right, insort_right
bisect_left, bisect_right, insort_right = makefuncs(); del makefuncs

try:
	from contextlib import nullcontext
except ImportError:
	class nullcontext(AbstractContextManager):
		def __init__(self, enter_result=None): self.enter_result = enter_result
		def __enter__(self): return self.enter_result
		def __exit__(self, *excinfo): pass

# urllib.request тянет с собой 32 модуля, которые я не использую, хотелось бы по возможности этого избегать :X
if os.name == 'nt':
	from nturl2path import pathname2url
else:
	from urllib.request import pathname2url

def getattrs(obj, names):
	for name in names:
		yield name, getattr(obj, name)

def setattrs(obj, namevalues):
	for name, value in namevalues.items() if isinstance(namevalues, Mapping) else namevalues:
		setattr(obj, name, value)

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
				self.cheat[sample] = cls if self.cheat.get(sample, cls) == cls else None # противоречивые повторения sample дадут cheat[sample] = None.
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
			f.min_prob = min(f.min_prob, cf_prob)
			if cf_prob > f.max_prob: f.max_prob, f.max_prob_class = cf_prob, cls

		result_gen = (informative_feat(feat, f.max_prob_class, f.max_prob/f.min_prob) for feat, f in feats.items() if f.occurences > 1)
		key = lambda f: f.margin
		return sorted(result_gen, key=key, reverse=True) if n is None else heapq.nlargest(n, result_gen, key=key)

	# Чтобы можно было передавать в samples как словарь, так и список пар.
	def pairs(self, samples): return samples.items() if isinstance(samples, dict) else samples

# lang_packs('names', 'adjs') вернёт списки (1) существительных и (2) прилагательных.
# lang_packs('male', 'female') вернёт списки (1) мужских и (2) женских имён.
def lang_packs(*items):
	return itemgetter(*map({n: i for i, n in enumerate(('names', 'adjs', 'male', 'female'))}.get, items))(SequenceMap(unpack_str(
	"嗠䊊鉝销𥦵𥦭尚𡿚𦟩𨏠膟𧣛梽柏陓瑹艫脙𤏵𠇬𣖫𡬭𧱽𤖹𒆨𥛸𣋭𠐅𤮉㩅䠏𢎰𤶁𤢊屦𤽼㶐𥛸僚𣨺𦍤㡺𦐺鲪𥞪𦡒𦬏𢛔𠗢𠆹𢖁𡛅𢽖䒉隔𤲬呛榽𒁴鱒𔖖𢏔端藽𨕃𤞔𠙋蝃𠛉蓐㶀悵𣡔𦧄㾇駹𦑍𥩫𧎲鲒𢘮𨌃䪨𠙼𠞻𣲋㔦𡟅𢤉𤫢𢺂欑𧢐𠶞𣇛𣓞𥞏"
	"𣿙侞𢓏𦮙懒螷𠓔䒬𖦍𢙇𣆊𡯳𢦺𣠊𣾳繘𥓺曠𖤠𠚏𣓀覣𣆇绐淩𦨉蠆䀍𣋆㐍𥾡哑𧎪𤦸骇伭𨊅𧙵㟤𡋥𤺭𤋟𠬃𤅉嫾䋺框𡢒嚶𢷸𤸧𢱣𡟓䫮𢕋棁𤑲𦁣衲炼䀐𥔒牏𦃲𥪻𤇯邢𨂸𡀌𤏉𧎪𖤴𠞼𢎲钘𣓝𢠟𔔨𠁤驄𣇸𢅆𣧗𦒡𧩝舓浶𖣷㿆𢳓ꆮ聽𨗶㘅㐜𥐫𢐲"
	"𣂱𢍪窅𥘡辩𢙹𠄺䱨喾蚵庎𠩘𣁶𣨇𠘭䋒㕥𠥮䖭寑臽峩𥀭𡪮詂𡔵瓝经𣦠𡫫𤍿譛𦆟皢撝蟕僂鴹𥣩檬薦𡾑𧦠𦊩𠀅𥁞醤𣺺𣝚𤊄𥻋鋎𥑗𤁂𠚾䇴𢪊𢬋忳庙𡅛𧜆鰼近勮𤶟敼𡌂𣝚𓅁𤍍𠘟拣𡄗据𡧐塘䎾𤣺𤳔擃𨎎莝酗𣋅𢸽賟𥼇𥭻䯻𡉜𒇂𤘋𣂔𠘺䘪𠅩"
	"𦱬𧜸婴𠴍𧰏璡𧽮𡘶𢘮卤𡃧𠣰𤚠奞梼𐘊鸣𥋘𨖾𨉎卬𦋍𡦬𣮋𧿎𥲳頟讈𤉪桝𦻅𢎍纔𥊔𡔞𡰨飹𥭎𠉩恝𤓔𤼍𣃞𢈩𒄡𧙳尩𥾴㩞𧧈𥙍捺𥣘𢠌𡧕䦪𧰞𡜌覡𓄥𧰈㩠𧃍𤁝𡜤𥱜紼窜𔑄𣱠𠙖𥩒𔑊𖥈㳖㠻𦬳ꇩ𠊃𡎉𤱓剣𧗁𠠑𨂪聖釋𥧀宁嘁𣢝𧳋𨕔朦𤢝䱻食"
	"𠭎𣘞𣖶ꍢ𡌎𦃘𓆏𤋠𖣦𢸂𡽼卢𧛔𣩝狌𦿲鬸𖧡聳𦘐𦡍𐙣𡚀権𤩮𥽯𤋑𦲒聀咷𡅜𧧗兓鹙𣯊㔖筤𨏒𡹮𦉥惣𡳳韢𔕴𦓗柱䐬𧇚𡨒婌𨐥𦥶濖罱饚𣎖𡒃咙侱𢌸𣃾䮣𢦍蘆钲阩鹫雡𨊰䒥𥃠𠂏𣦜㰚𢽣𡫊𣦧𡴏𒇾𦡈纋𧌋洕𠐩䄼𤡡𤥾𢡫𨒮𡧄𧲪𥿌蟜堷砋𥁅𠝟"
	"𤶣邅𥀲㘪𣛁𠓸跆𖠶呼噛𧹌𠖥綨𦑲𔒉㰽䎰箖𠭤扡𢴲𤨂𤝼戸椊盞𨁯晜𧉹𡸗𡅣睒𧲹湼𤨏𢒁𧿦醨𨒳𥣚䝹𤚑𣰊𥿒𠛭嬸瓚𢪭𦘌瞗𣼚𔗌䉟尚𢐇𣄺䬄彯𢱏鈸𠼑𧏙葁钣𥙡蛟𧗐蔝𓊑峢𓊶𠤮䃒𠺢鷍𦱳𢶣瓁𥚆𥧔𧝮𧛷劖𦾘𢓑𡃖𧘈㱸𦱴𨇖𠼿𠒼𡀢䪞𨋢呩𨗨"
	"𧗋𡁼𤵇账𥳓𣑑襖踤鮘艈䫩𧾪啬𥤬𧵷𤀟夤𦢃倥𢲕𖤏𒈜𠘠𥰹𣸫𢅅随𥢤𐚇銴睮𤿐𧗗硉𣚡𡶞軯𤬗隔𠆔𓅄𣒠啮𣥏𧯜𡣟鱣䓚珟犗呁熝𥗿禶𢵲𠆷𨎕𧅀綢𐘭𢂍𡓈鯢莪𢨬𦏇豷𤐇𢄲𦝦帘䈠㢲攏𡌛𥭋𨔠䠬𡄙𠒐𡂧𥶠絨𧓡𢟃𠰨𒅫羷禿𣥖䃻豸頻𣹋浟𣨠蒷"
	"剴傶甚𦓺𦟑嵒飭臭緤ꇁ㳎㙯蕂ꈰ颏𒆙𦅉銵𥠑𢳘𢁨𡥠𢋪𥘳绨𡈾午𦱿𦗚𠌘𨂀𦰨靀囿儦赐𦓖賩甇賄𤯬𤑳𦅁碃𧣚𦏲𡫘𤷁𢌚墨䂎𧭺籢𣵷𧤅垆𧩎𨋾㷊属䧻㳍溪瑱𠐮𠎭嘗𣸨𡊡膴𠪗卽𣇵𠰖覉淗𢘲𤴫姊𢁽𥚾浝𢹪疤豉𡤮拿㨩𡗐杲㦶𣸧𧪂曚𡛏𤥸𣲒"
	"𧨶𤛏𡍍𨀼稣𡇬𣿷𤭞㾋𦧋𧹞磴𣚹𠱔虂㐓𥡳𦒷𠘆𥒔𥾣𒃦㘐𠮌䘉𤂺鄷𣄚𧺄䈒伓𧼮𧋳㔶𠄈𧆅縜芠𣅏𡼦𤂽𧍶𥫡䱤𥇳𦽤ꗭ鏼𣤚𢩢𢕪躪𠖌𒇓𣝩𥒫𧤪䒳蹢𡺦謾㨂㬹籍𠬽㙢𦿻夏𧴀𥶴㣻㐤霑妕枉ꕄ𧅡𨅌嶤啛狓𡂈䟝𤮽𤶷櫨𧼊𣮾俽钸𦵔𡏖㟮㵂䆱𢧣炗"
	"𧚲𧴎𤔏𧍫𣷍𢌦𦽏𥋋𦒺𧝚𧬝䄗丅𠴠𥱏䈭𡪩𡌈𡀂盎𣼔𧒔䡐𧑜妝欲𤈐𥲂𧟔僽睼䀸𡏤胨𠋤膍玙𥥔𥢊蕠𢮜畉𤖯𣔋神𠃶㦬𥅨䋡墀軺䧿𣏈逄ꕫ𢙳盝叢𤵿𥨚𧞖𢟠𣊲𥖽轼𡣬𢅢𧾣𐙀懦𦡂娝樮痉㒛𡲑䣚𥉟𨗅𢅹𤿶𠶈𐛸㖡㬼星㑹圌姶𧌲𦠎𡯐扔𦹁𧬀𢳈𦗨"
	"ꔌ𡞀𨄍𥰱幋𤲢𧜝蕺綠鈲𢬆𤌷揾𢿵𓌆䋭𦥣𣼌蠑𡕱𡀺䌳迓籭漻𡮓𦒿𢣼銒𨂧湼𠪸𡐳𧪚𤄦𧙟愴𤢟盯㻪㠴豈𧶲𠆝𤍗𡋄頇𣼒𥾂鷣呫䰶𢩆赆㗅搇䱅䏞𧯤禡𥣅𨅥黔𤜘𠚔𤶜𥲥䰷㘹𤯷𤊲𤼶𧑾郹鬳𥧶𡋔𢑋籐𡲸陠𦎽㩽镍鲀𢕄吡靓𓊃𣞤𣥍𡙙𡡆纤讓䙖鷹"
	"𥡰𧅚𨆾𤁃𣁥𣣇螁𡎀䒈𥖓𢸷𖡫𡫬䜆𐛛𣖖瘧鲈𣱔蝻ꎔ𣧲巊𠪘瘭𢊴𒁻𤢒㽕𦬥𤙦𣋯𥉸𤞲姐𥨗𦍭槰𧞖嶴𢂝𔔂𡚽𨌒遐𥤕𤐿𖦿𤛌䗱ꄳ𧲷𤿐ꆂ𦆙𥣭𠥫䕪𡝮犌䅩𠖅𦾩𤐮𦧌嗇嵑𥉑鶧𦕓𣬜𡗜蝪𤲴𤰝𣉹麒𧉉兮䟻㐷餬𤏕𒄆𢿑𠀂𓅔㬧ꎪ隕幢儡油㴰㽸𣬷𠓺"
	"𡼉茧𥍮𣮽𧷅玙𤾚儊𥷇䁭瀜𤊒𠺛誃输ꗸ𡄔𢘕ꎙ𧬗𡬢𦜿㐦𤣴𓉢𢧶捺𓇤𨖻𓅈𦡊𢴁𨎂銗𣹎𦺪涧槪舵録ꅄ𡶜颱𢖈𣭅𥂣𖢛魆𥱼钤𦛔𤜾𨉜𨕟繭𡧃蕳𥧃𒄑𧼞𧊞𠯘𢳌戵畟𠎧𡒵㟗𤅫𠋨𔐊𤞴㫡槛𧙲𢘰䀱𥘒𦼛ꇳ𠿜壘䈡𤌑䣭𔕶𨂴𠮜𢹗咴佁𠎜𥸪𣰃𢙺馲𓅪"
	"㫉賐蒾瘼𣒀崧𧳨𥐍ꗐ𓌯𧹘騎𤧎𤍼痂𡀷𤭳𠗯𡹊𧒂葺佊𔖤𨉨𦓝𔓏噰䒮𐛈𡶅𣝐䥕𒈚䁽𡓝𣬃𥹗薸𤍶睧𣟢𣵵鋊ꊸ竦𡠄庶紀沨𖡔䪦𣂝𠍈䈠𤡹𡘤ꆞ𡊳䖽𒂫𥳑簨鐦䊕濑涐𒄎ꍭ礴𠱬呡𨉗𠓰䉝𥦗𠏰𣟞𠈗𣫂瓾玌繮𧥄𥍶𣸇㖺𤣲𧛲媍𤷹鱰𓂹殢橐捋𢱖韴"
	"癉蘡𥹤𒇯𢕳𠋾𦯉𦋐皾𦣛𣍌咄𥫪𣓘𢅒𥰁桞𥬸𣓆疬㧢𤮻涤𠝷𠽲𡼫𥱸𧠠𨂊𦤫𨅚𠓊𠍲ꌿ瓃𥠍崠笼舮暝𦡪𠰔𖤜䘏詂𡬁𧹮𥕮斺𡼱𤳭闩𦥕䇕𠫤燶𥘡𓄹𡇲𣪍䟐𢡘𥐐𧪶𣉏耓豈嫺𥺌𧫫𤗢𦉓𧻆䥄𤕂䀸糐𣶈𡻂欣𧂃诏袏𨓖䞯𥅅𥕫𤗋𖣠𠻢鰅𓀞𤝱𣼀𣎉蝎𥯳"
	"𣏲䁟ꊳ癷𓊚呞𡕉𦀣𠗽䀣㭱𖣨𤾚𓄎𣷥諠𧁟𒂟𥆛𥅞瘺𤕥𧗋𧌁𧜫埘妀蕓㱏𧁅𦍶𨈙畋𖥜砌𡁛𡁛𢏙𦧝皍𤣦𠥚𢿱昔㝓𤓧𡟇𤠻恻𧩊𧴺唩𥀶疵𠗹𡱠𦞬𠭭贕屈𤽡𡼸絹馴詛𦨼𧡠ꔭ𡟃𣑋碼𓄢驄釁糐㠷𦂋𠵂揗𥣋嬃𣷹烬𦶡𧐰鞛甍𢕫𢋤揰𦚝ꕲ𨑉懕鴙煏𥩚"
	"𠨄𤎧㜗𦳲𡫰逞𨎧𒅓𨂇蕸𧏟𡀂𥀧𨌷䳪𣮢𨐫𥯔𢨍鑍𠿁杹畘涼𧻆䡿𢃧𥜔䍝𢌱怲梃櫙㱷𢹮𠯐𓎇褑𥼤耈𢾋𠾏𦮩𡈁𡷁𦯃𣐵恉𠆂䨉𧒽犠䡃𤀟𣨷諘貽𥪁𧤹𥣛烎𧽤𥖩𣘵𥨭𦹼𥍎鑙𢩽䅬𢚚潶短𧭠𔕣蹿𥋸癗𥕎𡨃戹𔗸𤵶廭䜅槵𨂫栣𥖸斫钋𣅡𦞋𣨳𧶐𦏅𤠁"
	"㱯牑彉𤠡𥔼𥨪𣏿𦞺㖰𦦟㻦𦦣𥀍篡𤁉𦸎㹱𨒣𡅡𧷳𤞼𢑖𦠔蘦𣻬㑋𢨹𦠨嵵傐𧽫𨍋吔很𣇙賭𦓤𡟄𤅽𥳖𠒲𧊮㻔癲𦑆㾻𧏬𤗰狽㩶𣪵𡧅𠝯𤈮𧇧𦜋襦𧗹綬𓏑𢵞铩沪慠𤘟𨎲𣲳𦜙盂ꔍ𐘡𤂥𧷚𦮓𨖟𠡼刑𢱔槩𠻀𥚙麺颓洿𣪄矕ꏚ骾𧤷蔶珘𧔬𠩇鵚鱓𥫒𧢧"
	"𡹐𓊕𡓼𒀝越𒆯𠢯𦱨槀𥯅𥁣𔔯𓄸蓋𡇔𤨉圹𖠱洔𦊘㘵搚瀮𠵈䩐𣗄𦀦𦺿䇙𒄊𣃠鐂諣堘𖦕詊𡾙犼𢩰𠈥𧴞𡶜伻㶦𤿖武𡋔𧯛睍𡊢𥣊䤳䎶𣖧㮶𦦦𔑈𠲝䪤㫤𢝜䉄𦣈𤃩哹蜤𠏋𠉉𢫵訦𦓬𥃰𤮢㺤竸財㜣𠠱𐘈𣙛𠢸𓈢婴𣢸𢯎𠽁𤽇𤅐𣩱𧱐喫禈𥄃𣥡专𣭉ᔀ"
	).split('/'), str.split))

def split_name_opts(name):
	literal, bracketed, _spec, _conv = next(Formatter.parse(None, name), ("", None, None, None))
	return literal, bracketed.split() if bracketed else ()

class Gender(IntEnum):
	UNKNOWN, MALE, FEMALE, NEUTER, TOTAL = -1, 0, 1, 2, 3

	@staticmethod
	def detect(name):
		# С L2-L3 бессовестно нарушается предположение о независимости признаков, но результат вроде лучше, кхехех.
		oracle = BayesianGuesser(lambda w: (('F2', w[0:2]), ('L2', w[-2:]), ('L3', w[-3:])),
			samples = ((sample, gender)
				for samples, gender in zip(lang_packs('male', 'female'), (Gender.MALE, Gender.FEMALE))
				for sample in samples), cheat=True)

		best_guess, best_margin = Gender.UNKNOWN, None
		for _lit, word, _isend in Noun.split_into_words(name):
			guess, margin = oracle.guess(word.casefold()) if word else (None, None)
			if guess is not None and (best_margin is None or margin > best_margin) and margin > 0.28:
				best_guess, best_margin = guess, margin

		return best_guess

	# victim.name + victim.gender.ize(" подверг{ся/лась/лось} изнасилованию со стороны ") + rapist.name.genitive
	def ize(self, fmt):
		def handle(piece):
			if not piece: return ""
			per_gender = piece.split('/')
			if not 1 <= len(per_gender) <= Gender.TOTAL:
				raise ValueError("\"{}\", \"{}\" — {}, ожидается 1–{}.".format(fmt, piece, plural(len(per_gender), "{N} значени{е/я/й}"), Gender.TOTAL))
			return per_gender[self if self != Gender.UNKNOWN and self < len(per_gender) else Gender.MALE]
		return "".join(literal + handle(bracketed) for literal, bracketed, _spec, _conv in Formatter.parse(None, fmt))

class Case(IntEnum):
	NOMINATIVE, GENITIVE, DATIVE, ACCUSATIVE, INSTRUMENTAL, PREPOSITIONAL, TOTAL = range(7)
	@staticmethod
	def from_letter(letter):
		try:
			return Case('NGDAIP'.index(letter)) if letter else Case.NOMINATIVE
		except ValueError:
			raise ValueError(f"Неизвестный падеж: {letter}.") from None

# Noun.parse("маленьк{ий/ого/ому/ий/им/ом} член{/а/у//ом/е}").genitive == Noun.guess("маленький член").genitive == "маленького члена"
# Noun.parse("{кусок} угля").prepositional == "куском угля"
# Наследование от str нужно *исключительно* для того, чтобы можно было обращаться как с str, если достаточно словарной формы.
class Noun(str):
	def __new__(cls, pieces):
		if not isinstance(pieces, list): impossible(pieces, "исп. Noun.parse / Noun.guess" if isinstance(pieces, str) else "pieces")
		self = super().__new__(cls, cls.join_pieces(pieces, Case.NOMINATIVE))
		return self

	def __init__(self, pieces):
		super().__init__()
		self.pieces = pieces

	@staticmethod
	def join_pieces(pieces, case):
		return "".join(piece for literal, cases in pieces for piece in (literal, cases[case] if cases else ""))

	def __call__(self, case):
		return self.join_pieces(self.pieces, case)

	def __eq__(self, other):
		check(other, other.__class__ == Noun, lambda: f"сравнение {self.__class__} с {other.__class__}")
		return isinstance(other, self.__class__) and self.pieces == other.pieces

	def __add__(self, other):
		if isinstance(other, str) and not isinstance(other, type(self)):
			pieces = self.pieces[:]
			self.append_pair(pieces, other, None)
			return type(self)(pieces)
		else: return NotImplemented

	@staticmethod
	def append_pair(pieces, literal, cases): # ненужная оптимизация, чтобы не бить строку в месте, где guess_one так ничего и не придумала
		if pieces and not pieces[-1][1]:
			pieces[-1] = pieces[-1][0] + literal, cases
		else:
			pieces.append((literal, cases))

	@staticmethod
	def parse(src, *, animate=False, gender=Gender.MALE, return_gender=False):
		pieces = []
		for literal, bracketed, spec, _ in Formatter.parse(None, src):
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
			if word.endswith(('ые', 'ие')):
				return word[:-len('е')], ngdip('е', 'х', 'м', 'ми', 'х')
		if word.endswith('ия'):
			return word[:-len('я')], ('я', 'и', 'и', 'ю', 'ей', 'и')
		elif word.endswith('а'):
			return word[:-len('а')], ('а', yi(word[-2:-1]), 'е', 'у', 'ой', 'е')
		elif word.endswith('я'):
			return word[:-len('я')], ('я', 'и', 'е', 'ю', 'ей', 'е')
		elif word.endswith('ок') or word.endswith('ёк'):
			before = ("й" if word[-3:-2] in vowels else "ь") if word[-2:-1] in 'ё' else ""
			return word[:-len('ок')], ngdip(word[-2:], before + 'ка', before + 'ку', before + 'ком', before + 'ке')
		elif word.endswith('ец'):
			if word[-3:-2] in vowels:
				return word[:-len('ец')], ngdip('ец', 'йца', 'йцу', 'йцом' if word[-4:-3] in 'у' else 'йцем', 'йце')
			else:
				return word[:-len('ец')], ngdip('ец', 'ца', 'цу', 'цом', 'це')
		elif word.endswith(tuple('бвгджзклмнпрстфхцчшщ')) and (gender == Gender.UNKNOWN or gender == Gender.MALE):
			return word, ngdip('', 'а', 'у', 'ом', 'е')
		elif word.endswith(('о', 'е')) and (gender == Gender.UNKNOWN and word[0] == word[0].lower() or gender == Gender.NEUTER):
			return word[:-len('о')], ngdip(word[-1], 'а', 'у', word[-1] + 'м', 'е')
		elif word.endswith('й') and (gender == Gender.UNKNOWN or gender == Gender.MALE):
			return word[:-len('й')], ngdip('й', 'я', 'ю', 'ем', 'е')
		elif word.endswith('ь') and gender == Gender.FEMALE:
			return word[:-len('ь')], ('ь', 'и', 'и', 'ь', 'ью', 'и')
		elif word.endswith('ь') and (gender == Gender.UNKNOWN or gender == Gender.MALE):
			return word[:-len('ь')], ngdip('ь', 'я', 'ю', ('ё' if word.endswith('арь') else 'е') + 'м', 'е')
		elif word.endswith('ы'):
			return word[:-len('ы')], ngdip('ы', '' if gender == Gender.FEMALE else 'ов', 'ам', 'ами', 'ах')
		else:
			return word, None

	@staticmethod
	def split_into_words(src):
		def is_word_char(ch): return 'а' <= ch <= 'я' or 'А' <= ch <= 'Я' or ch in 'ёЁ-' or 'a' <= ch <= 'z' or 'A' <= ch <= 'Z'
		i, last = 0, None
		while i < len(src):
			lit_start = i
			while i < len(src) and not is_word_char(src[i]): i += 1
			word_start = i
			while i < len(src) and is_word_char(src[i]): i += 1
			if i > word_start or i == len(src):
				if last: yield last + (False,)
				last = src[lit_start:word_start], src[word_start:i]
		if last: yield last + (True,)

	def src(self, sep="/"): return "".join(piece for literal, cases in self.pieces for piece in (literal, "{" + sep.join(cases) + "}" if cases else ""))
	def cap_first(self): return cap_first(self)

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
		names, adjs = lang_packs('names', 'adjs')
		while True:
			if not adjs or not names: raise Noun.RandomNamesExhausted()
			iadj, iname = randrange(len(adjs)), randrange(len(names))
			adj, (name, name_opts), gender = adjs[iadj], split_name_opts(names[iname]), Gender.MALE
			for opt in name_opts:
				if opt == 'f' and gender == Gender.MALE: gender = Gender.FEMALE
				else: impossible(opt, "opt")
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
			if see: see('adj', adj); see('noun', name)
			result = Noun.guess(result, animate=True, gender=gender)
			return (result, gender) if return_gender else result
Noun.PLACEHOLDER = Noun.parse("{баг}")

# Объявляет Noun.genitive = property(lambda self: self(Case.GENITIVE)) и так для всех падежей.
# Здесь и далее используется нечитаемая конструкция
#
# > (lambda value: do_something_with(value))(get_value())
#
# или чуть менее нечитаемая (хотя как посмотреть)
#
# > (lambda value=get_value(): do_something_with(value))()
#
# вместо
#
# > value = get_value()
# > do_something_with(value).
#
# Иногда это просто чтобы выебнуться, но иногда, в т. ч. здесь, без вспомогательной функции работать не будет из-за особенностей скоупинга в Python.
# Объяснение: http://stupidpythonideas.blogspot.com/2016/01/for-each-loops-should-define-new.html.
#
# TL;DR:
# For использует одну и ту же переменную, а не создаёт новую, так что она будет расшарена между замыканиями, созданными в теле цикла,
# и все они будут видеть её последнее значение. Так, здесь без лямбды, копирующей case в новый скоуп, все property будут указывать на case = Case.TOTAL.
# Pylint называет это «cell variable defined in loop».
setattrs(Noun, ((case.name.lower(), (lambda case=case: property(lambda self: self(case)))()) for case in Case if case not in (Case.NOMINATIVE, Case.TOTAL)))

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

# sign(x) * abs(x)**pow
def signed_pow(x, pow):
	return x ** pow if x >= 0 else -((-x) ** pow)

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
def digest(data, format='b65k'):
	return encode(hashlib.blake2s(data.encode()).digest(), format)

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
	def validate(min, peak, max):
		if not min <= peak <= max: raise ValueError(f"Неверные параметры bell: min={min}, peak={peak}, max={max}, предполагается min <= peak <= max.")

	def bell_with_peak(min, peak, max):
		validate(min, peak, max)
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
		validate(min, peak, max)
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
	def proba_dens(self, x): raise NotImplementedError("proba_dens")

	@staticmethod
	def guess(arg):
		if isinstance(arg, Distribution): return arg
		if isinstance(arg, (tuple, list)) and all(isinstance(x, Number) for x in arg):
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
		def proba_dens(self, x): return 1 / (self.max - self.min) if self.min <= x <= self.max else 0

	class Bell(Distribution):
		def __init__(self, min, avg, max): self.min, self.avg, self.max = min, avg, max
		def estimate_min(self): return self.min
		def estimate_avg(self): return self.avg
		def estimate_max(self): return self.max
		def roll(self): return bell(self.min, self.avg, self.max)
		def proba_dens(self, x): return bell.proba_dens(self.min, self.avg, self.max, x)
	return Uniform, Bell
Distribution.Uniform, Distribution.Bell = makeclasses(); del makeclasses

def trim_leading_spaces(s, start=0):
	pos = start
	while pos < len(s) and s[pos] == ' ': pos += 1
	return pos - start, s[:start] + s[pos:] if pos > start else s

# Главная причина существования этой функции в том, что textwrap.wrap, похоже, не обрабатывает \n.
#
# Также при markdown=True, если в строку добавлен |, то её хвост начнётся с этой позиции, например:
# wrap("Страх — |внутреннее состояние, обусловленное грозящим реальным или предполагаемым бедствием.", ..., markdown=True)
# ->
# Страх — внутреннее состояние, обусловленное
#         грозящим реальным или предполагаемым
#         бедствием.
def wrap(text, width, markdown=False):
	def wrap_paragraph(line, width):
		prefix = ''
		if markdown:
			p = 0
			while p < len(line):
				if line[p] == '\\': p += 2
				elif line[p] == '|':
					line = line[0:p] + line[p + 1:]
					prefix = ' ' * p
				else: p += 1

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
	msg = str(e)
	# Некоторые исключения выдают в str() самодостаточное сообщение об ошибке, некоторые — нет.
	# Например, ошибки ОС разворачиваются в красивые сообщения, а KeyError — в голый ключ.
	# Это попытка угадать такие случаи и дописать впереди тип, не трогая нормальные.
	if " " not in msg: msg = type(e).__name__ + (": " + msg if msg else "")
	if TRACEBACKS and sys.exc_info()[1] is e: msg = format_exc() + "\n" + msg
	return msg

# список команд, позволяющий сокращать их при отсутствии неоднозначностей
# guess возвращает
# (1) ассоциированную с командой функцию
# (2) список вариантов (при однозначности будет содержать единственный элемент)
# (3) список подсказок при ошибке
# (всё это нужно сначала проверить на истинность, на данный момент всегда возвращается либо (1)+(2) с одним элементом, либо (2), либо (3))
#
# например:
# .add("hit", funcA)
# .add("hook", funcB)
# .guess("h") → None, ["hit", "hook"], None
# .guess("ho") → funcB, ["hook"], None
#
# .add("hit body", funcC)
# .guess("h b") → funcC, ["hit body"], None
# .guess("h c") → None, None, ["hit body"]
#
# Также
# .add("a b", funcAB, "c d", funcABCD)
# эквивалентно
# .add("a b", funcAB)
# .add("a b c d", funcABCD)
#
# Этот класс переделывался уже раз 5, поэтому стоило бы переписать его с нуля, чтобы сделать вдвое короче
# и избавиться от странных вещей вроде «word_lens» и «filtered_*», но мне лень. ¯\(^͜^)/¯
class Commands:
	def __init__(self):
		self.root = Commands.node("", None)

	def add(self, *args):
		node = self.root
		if args and not isinstance(args[0], str):
			for cmd in args[0]: self.add(cmd, *args[1:])
			return

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
			return node.func or None, [node.backtrack()] if node.func else self.suggest_something(start_node = node), None

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
		-1 if sym in whitespace else
		0 if 'a' <= sym <= 'z' or 'A' <= sym <= 'Z' else
		1 if sym in digits else
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
		return not not self.root.childs

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
			("o t", None, ["one two", "one three six"], None), ("o t t", "123", ["one two three"], None), ("o t s", "136", ["one three six"], None)
		),
		(("spd-", "A"), ("sp.frailness", "B"), ("sp-", "A", ["spd-"], None)),
		(("sp-", "A"), ("spd-", "B"), ("sp.frailness", "C"), ("sp-", "A", ["sp-"], None)),
		(
			("1", "L1"), ("remove 10", "B"), ("remove 11", "C"), ("remove 21", "D"),
			("1", "L1", ["1"], None), ("r1", None, ["remove 10", "remove 11"], None), ("r2", "D", ["remove 21"], None)
		),
		(("shop", "A"), ("shoot timestop", "B"), ("s", "A", ["shop"], None)),
		(
			("sp.dispell+", "A"), ("sp.frailness+", "B"), ("b.timestop-", "C"),
			("il", "B", ["sp.frailness+"], None), ("es", None, ["sp.frailness+", "b.timestop-"], None)
		),
		(("spd+", "A"), ("sp.frailness+", "B"), ("s+", "A", ["spd+"], None)),
		(("rage V", "A"), ("rage Vo", "B"), ("rV", "A", ["rage V"], None)),
		(("sp.fstorm+", "A"), ("sp.frailness+", "B"), ("fs+", "A", ["sp.fstorm+"], None)),
		(("dex+", "A"), ("spd+", "B"), ("d+", "A", ["dex+"], None)))

	def one(self, *adds_and_queries):
		get_adds, get_queries = (lambda makegetf=(lambda itemlen: lambda: filter(lambda item: len(item) == itemlen, adds_and_queries)): (makegetf(2), makegetf(4)))()
		assert len(adds_and_queries) == sum(1 for items in (get_adds(), get_queries()) for item in items), adds_and_queries

		cmds = Commands()
		for add in get_adds(): cmds.add(*add)
		for query in get_queries():
			self.assertEqual(cmds.guess(query[0]), query[1:])

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
# По умолчанию, если перед маркером нет пробела, текст перед ним выравнивается по правому краю.
# Если в начало маркера дописана >, форсируется выравнивание по правому краю, если < — по левому.
# Эти символы не считаются частью маркера (A и >A будут объединены).
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
		__slots__ = ('data', 'marker', 'marker_pos', 'line_index', 'fragment_index', 'just')
		def __init__(self, data, marker, marker_pos, line_index, fragment_index, just):
			self.data, self.marker, self.marker_pos, self.line_index, self.fragment_index, self.just = data, marker, marker_pos, line_index, fragment_index, just

	def make_marker_come_after(marker, after):
		after.markers_after_this.append(marker)
		if after in marker.markers_after_this:
			raise ValueError(f"Циклическая зависимость между маркерами [{marker.name}] и [{after.name}].")
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
					just = 'auto'

					marker_name = line[i+1:marker_end]
					line = line[:i] + line[marker_end + 1:]

					if marker_name.startswith('>'):
						just, marker_name = 'left', marker_name[len('>'):]
					elif marker_name.startswith('<'):
						just, marker_name = 'right', marker_name[len('<'):]

					marker = markers.get(marker_name, None)
					if not marker:
						marker = markers[marker_name] = Marker()
						marker.prev = last_marker
						if last_marker:
							last_marker.next = marker
						else:
							first_marker = marker
						last_marker = marker

					fragment = Fragment(line[start:i], marker, i, line_index, len(fragments), just)
					marker.occurrences.append(fragment)
					fragments.append(fragment)
					if prev_marker: make_marker_come_after(marker, prev_marker)
					prev_marker = marker
					start = i
			else:
				i += 1
		fragments.append(Fragment(line[start:], None, 0, 0, 0, 'auto')) # см. (**fake_last_fragment)
		soup.append(fragments)

	# Теперь нужно пройтись по списку маркеров и все их выровнять.
	marker = first_marker
	while marker:
		target_pos = max(fragment.marker_pos for fragment in marker.occurrences)

		for fragment in marker.occurrences:
			pad_delta = target_pos - fragment.marker_pos
			if pad_delta == 0: continue

			if fragment.just == 'auto' and fragment.data and fragment.data[-1] in ' ' or fragment.just == 'right':
				fragment.data = fragment.data + ' ' * pad_delta
			else:
				fragment.data = ' ' * pad_delta + fragment.data

			# -1 — после последних фрагментов строк, т. е. тех, которые Fragment(line[start:], None, 0, 0, 0, 'auto') (**fake_last_fragment),
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
		(["1[A]2[B]3", "4[B]5[A]6"], ValueError))

	def one(self, input, expect):
		def do_mp(): return multipad(input)
		if isinstance(expect, type) and issubclass(expect, Exception):
			self.assertRaises(expect, do_mp)
		else:
			self.assertEqual(do_mp(), expect)

def cls():
	os.system('cls' if os.name == 'nt' else 'clear')

# Делает 2 бесполезных вещи:
# 1) преобразует исключения, бросаемые input() в ответ на EOF и Ctrl-C, в единообразное InputInterrupt.
#    InputInterrupt наследуется от SystemExit — это заставляет интерпретатор выходить тихо, а не с трейсбеком.
# 2) перед тем, как бросить InputInterrupt, на основании эмпирических догадок выводит пустую строку, если считает нужным (для красоты).
class InputInterrupt(SystemExit): pass
def hook(print, input):
	last_print_had_end = True
	def print2(*args, **kargs):
		nonlocal last_print_had_end
		last_print_had_end = 'end' in kargs
		print(*args, **kargs)

	def input2(*args, **kargs):
		try:
			return input(*args, **kargs)
		except (KeyboardInterrupt, EOFError) as e:
			if isinstance(e, KeyboardInterrupt) and last_print_had_end: print()
			raise InputInterrupt() from None
	return print2, input2
print, input = hook(print, input); del hook

# Универсальная атака «чего угодно чем угодно». Реализует общее для атак поведение, такое как взаимодействие с бронёй и хексами.
# Можно не проводить атаку, а просто оценить интересующие показатели (урон, шанс попадания).
class Beam:
	AC_reduction = namedtuple('AC_reduction', 'relative, absolute_avg, absolute_max')

	# AC — показатель брони. В общем случае обеспечивает как относительное (постоянный процент), так и абсолютное (случайное от 0 до max) снижение урона.
	# pierce регулирует абсолютную составляющую: атака с pierce=0.5 проигнорирует 50% абсолютного снижения, pierce=1.0 оставит только относительное.
	@staticmethod
	def ac_reduction(ac, pierce=0):
		relative = 1 - (1 + ac/10)**-0.4
		check(relative, 0 <= relative <= 1, "relative")
		absolute_avg = ac/7 * max(0, 1-check(pierce, 0 <= pierce <= 1, "pierce"))
		absolute_max = ac/4 * max(0, 1-pierce)
		return Beam.AC_reduction(relative, absolute_avg, absolute_max)

	def apply_ac(self, damage, ac, pierce=0):
		reduction = Beam.ac_reduction(ac, pierce)
		return max(0, damage * (1 - reduction.relative) - (bell(0, reduction.absolute_avg, reduction.absolute_max) if reduction.absolute_max else 0))

	class Ongoing:
		def __init__(self, mode='real'):
			self.mode = mode
			if self.mode != 'collect_elems':
				self.hp = 0
				self.denorm_ac, self.denorm_pierce = 0, 0

			if self.mode == 'collect_elems':
				self.per_name = OrderedDict()

		def add_hp_damage(self, elem, target, dis, ac=0, pierce=0, force=None):
			if force is not None: hp_dam = force
			elif self.mode == 'real': hp_dam = dis.roll()
			elif self.mode == 'collect_elems': hp_dam = dis.estimate_avg()
			else: impossible(self.mode, "mode")

			if isinstance(elem, Beam.Fire):
				barr = target.find_hex(BarrierHex)
				if barr: hp_dam *= (1 - barr.fire_resist())

				vuln = next((sp for sp in target.specials if isinstance(sp, FireVulnerability)), None)
				if vuln: hp_dam *= 1 + max(0, vuln.amount)

			elif isinstance(elem, Beam.Electricity):
				barr = target.find_hex(BarrierHex)
				if barr: hp_dam *= (1 - barr.elec_resist())

			if self.mode != 'collect_elems':
				self.hp += hp_dam
				self.denorm_ac += hp_dam * ac
				self.denorm_pierce += hp_dam * pierce

			if self.mode == 'collect_elems':
				self.per_name[elem.do_name()] = self.per_name.get(elem.do_name(), 0) + hp_dam

		def normalized_ac(self): return self.denorm_ac / (self.hp or 1)
		def normalized_pierce(self): return self.denorm_pierce / (self.hp or 1)

	class Element:
		def do_apply(self, target, ongoing, force=None): raise NotImplementedError("do_apply")
		def do_minmax(self, target): raise NotImplementedError("do_minmax")
		def do_proba_dens(self, target, x): raise NotImplementedError("do_proba_dens")
		def do_name(self): return None

	class Plain(Element):
		def __init__(self, amount):
			self.amount_dis = Distribution.guess(amount)

		def do_minmax(self, target):
			return self.amount_dis.estimate_min(), self.amount_dis.estimate_max()

		def do_proba_dens(self, target, x):
			return self.amount_dis.proba_dens(x)

	class Physical(Plain):
		def __init__(self, amount, pierce=0):
			super().__init__(amount)
			self.pierce = pierce

		def do_apply(self, target, ongoing, force=None):
			ongoing.add_hp_damage(self, target, self.amount_dis, target.ac, self.pierce, force)

	class Fire(Plain):
		def __init__(self, amount, pierce=0):
			super().__init__(amount)
			self.pierce = pierce

		def do_apply(self, target, ongoing, force=None):
			if target.preset == 'lightning': return
			ongoing.add_hp_damage(self, target, self.amount_dis, target.ac * 1.2, self.pierce, force)

		def do_name(self): return "огонь"

	class Electricity(Plain):
		def __init__(self, amount):
			super().__init__(amount)

		def do_apply(self, target, ongoing, force=None):
			if target.preset == 'lightning': return
			eff_ac = target.ac
			if not target.find_hex(BarrierHex): eff_ac /= 2
			ongoing.add_hp_damage(self, target, self.amount_dis, eff_ac, 0, force)

		def do_name(self): return "электричество"

	def __init__(self, master, target, arena, master_imagination=None, target_imagination=None):
		self.master, self.target, self.arena, self.master_imagination, self.target_imagination = master, target, arena, master_imagination, target_imagination

	def master_str(self): return self.master.calculate_str(self.master_imagination)
	def master_int(self): return self.master.calculate_int(self.master_imagination)
	def master_dex(self): return self.master.calculate_dex(self.master_imagination)
	def target_str(self): return self.target.calculate_str(self.target_imagination)
	def target_int(self): return self.target.calculate_int(self.target_imagination)
	def target_dex(self): return self.target.calculate_dex(self.target_imagination)

	def launch(self):
		to_hit = self.on_tohit()
		if to_hit is not None:
			ev, cumulative = check(self.on_ev(), "on_ev"), self.get_cumulative()
			dodged, chance, roll = self.arena.dodge(to_hit, ev, cumulative)
			if dodged:
				self.on_dodged(chance, roll)
				return

		elements = self.get_elements()
		ongoing = self.Ongoing()
		for elem in elements:
			elem.do_apply(self.target, ongoing)

		precise_hp = ongoing.hp
		precise_hp = self.apply_ac(precise_hp, ongoing.normalized_ac(), ongoing.normalized_pierce())
		precise_hp = self.post_ac(precise_hp)

		rounded_hp = rand_round(precise_hp)
		self.target.ouch(rounded_hp, self.master, self.arena, hook=lambda fatal: self.on_hp_damage(rounded_hp, fatal), account=self.on_account(), elems=elements)

	def post_ac(self, hp):
		multiplier = 1
		for hex in self.master.hexes:
			if isinstance(hex, RageHex): multiplier += hex.physdam_x - 1
		for hex in self.target.hexes:
			if isinstance(hex, RageHex): multiplier += hex.backlash_x - 1
		return hp * multiplier

	class DamageEstimation:
		def __init__(self, beam, *, do_elems=True, do_tohit=False):
			self.avg = 0
			self.max = 0

			elements = beam.get_elements()
			self.avg = self.integrate_damage(beam, elements, [None] * len(elements), 0)
			self.max = ceil(self.max)

			if do_elems:
				ongoing_elems = beam.Ongoing('collect_elems')
				for elem in elements:
					elem.do_apply(beam.target, ongoing_elems)
				total = sum(ongoing_elems.per_name.values())

				self.elem_parts = total and OrderedDict((name, dam/total) for name, dam in ongoing_elems.per_name.items() if name)

			if do_tohit:
				self.hit_chance = beam.hit_chance()

		# https://ru.wikipedia.org/wiki/Свёртка_(математический_анализ)#Свёртка_распределений
		# Для оценки урона берётся N-кратный интеграл по всем элементам и броне.
		# Т. о. N = len(elements) + 1.
		#
		# В chain запоминаются значения на текущей итерации — они нужны Ongoing для расчёта эффективных значений брони в каждом конкретном случае.
		# Например, если в конкретной атаке элемент A нанёс 20% общего урона, а B — 80%, при этом элемент A игнорирует 50% брони, а B — 0%,
		# финальный процент игнорируемой брони будет взвешенной суммой, 20%×50% + 80%×0% = 10%.
		def integrate_damage(self, beam, elements, chain, current):
			steps = 10

			if current >= len(elements):
				ongoing = beam.Ongoing()
				for element_index, element in enumerate(elements):
					element.do_apply(beam.target, ongoing, force=chain[element_index])

				reduction = Beam.ac_reduction(ongoing.normalized_ac(), ongoing.normalized_pierce())
				dam = ongoing.hp * (1 - reduction.relative)
				if reduction.absolute_max:
					dam = integrate(lambda x: max(0, dam - x) * bell.proba_dens(0, reduction.absolute_avg, reduction.absolute_max, x), 0, reduction.absolute_max, steps)
				dam = beam.post_ac(dam)

				self.max = max(self.max, dam)
				return dam
			else:
				L, R = elements[current].do_minmax(beam.target)
				def int_x(x):
					chain[current] = x
					return (elements[current].do_proba_dens(beam.target, x) if L < R else 1) * self.integrate_damage(beam, elements, chain, current + 1)
				return integrate(int_x, L, R, steps) if L < R else int_x(L)

		def describe_elem_parts(self):
			return ["{:.0%} {}".format(part, name) for name, part in (self.elem_parts.items() if self.elem_parts else ())]

	def estimate_damage(self, do_tohit=False):
		return self.DamageEstimation(self, do_tohit=do_tohit)

	def human_stats(self, *, do_avg=True, do_max=True, do_elems=True, do_tohit=True, do_eff=True, multiline=True, est=None):
		sep = "\n" if multiline else ", "
		est = est or self.estimate_damage(do_tohit=do_tohit)
		result = ""

		if do_tohit and est.hit_chance is not None:
			result += (sep if result else "") + ("Шанс попадания:" if multiline else "шанс попадания") + " {:.0%}".format(est.hit_chance)

		if do_avg:
			result += (sep if result else "") + ("Урон:" if multiline else "урон") + " ~{}".format(round(est.avg, 1))

			note_parts = []
			if do_tohit and est.hit_chance is not None and do_eff:
				# «Эффективный средний урон» — произведение среднего урона на шанс попадания.
				# Из-за Cumulative эта информация малополезна, тем не менее, мне так уютнее.
				# С умножением на фактическую вероятность попадания с учётом Cumulative, а не мгновенную, было бы больше смысла, но мне лень думать, как её рассчитать.
				eff_avg = est.avg * est.hit_chance
				if round(est.avg, 1) != round(eff_avg, 1): note_parts.append("эфф. ~{}".format(round(eff_avg, 1)))
			if do_max: note_parts.append("макс. {}".format(est.max))
			if do_elems: note_parts.extend(est.describe_elem_parts())
			if note_parts: result += " ({})".format(", ".join(note_parts))
		return result

	def get_cumulative(self):
		c = self.on_cumulative()
		return c and (c if isinstance(c, Arena.Cumulative) else Arena.Cumulative(self.master, self.target, *(c if isinstance(c, tuple) else (c,))))

	def on_tohit(self): return None
	def on_ev(self): return self.target.calculate_ev(self.target_imagination)
	def on_cumulative(self): return None
	def on_dodged(self, chance, roll): pass
	def on_elements(self): raise NotImplementedError("on_elements")
	def on_hp_damage(self, hp, fatal): pass
	def on_account(self): return 'master'

	def hit_chance(self):
		tohit = self.on_tohit()
		return tohit and Arena.hit_chance(self.arena, tohit, self.on_ev(), self.get_cumulative())

	def get_elements(self):
		elements = self.on_elements()
		try:
			elements = (self.Physical(elements),)
		except Distribution.CantGuess:
			elements = check((elements,) if isinstance(elements, self.Element) else list(filter(None, elements or ())),
				lambda elements: all(isinstance(elem, self.Element) for elem in elements), "ожидается список Element")
		return elements

	@staticmethod
	def damage_paren(hp, mp=None, prefix=" "):
		desc = " + ".join(filter(None, (hp and str(hp), mp and f"{mp} MP"))) or str(hp)
		return f"{prefix}({desc})"

class DamageEstimationTest(TestCase):
	class Beam(Beam):
		def on_elements(self): return (self.Physical((1, 2, 4)), self.Fire((0, 1, 3)))

	def cases(self): return (0, 100), (5, 70), (10, 40), (20, 8)

	def one(self, ac, hp):
		passes = 15
		total_hits = total_dam = 0

		for _passno in range(passes):
			dummy = Fighter()
			dummy.base_ac = ac
			with dummy.save_relative_vitals(): dummy.base_mhp = hp

			beam = self.Beam(dummy, dummy, None)
			while dummy.alive: beam.launch(); total_hits += 1
			total_dam += hp

		self.assertAlmostEqual(beam.estimate_damage().avg, total_dam/total_hits, delta=0.15)

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
		self.skip_turns = 0
		self.dispell_amount = 0 # хекс развеивается, когда dispell_amount >= power

	def apply(self, master, victim=None, arena=None):
		check(not self.applied, "already applied", master.alive, "мастер мёртв", not victim or victim.alive, "жертва мертва")
		self.master = check(master, isinstance(master, Fighter), "master?!")
		self.victim = check(victim or master, lambda victim: isinstance(victim, Fighter), "victim?!")

		merge_behavior = self.merge_behavior()
		actual = next((hex for hex in self.victim.hexes if isinstance(hex, type(self)) and hex.merge_behavior() == merge_behavior), self)
		if actual is self:
			# Наложить хекс впервые.
			with self.master.lock_caused_hexes() as caused_hexes: caused_hexes.add(self)
			with self.victim.lock_hexes() as hexes: hexes.add(self)
			self.do_start()
			self.applied = True
		else:
			# Объединить с уже существующим.
			succeed = False
			if merge_behavior == 'strongest':
				power = None
				if self.power >= actual.power: power = self.power

				turns = None
				if self.time_based and (ge if self.stronger_is_longer else le)(self.turns, actual.turns):
					turns = self.turns

				if power is not None or turns is not None:
					actual.change_power(power, turns)
					succeed = True
			elif merge_behavior == 'add':
				actual.change_power(actual.power + self.power)
				succeed = True
			else: impossible(merge_behavior, "merge_behavior")
			actual.do_merge(self, succeed)

		actual.touch(master, arena)

	def unapply(self):
		check(self.applied, "not applied", self.ran_out, "not ran_out")
		with self.master.lock_caused_hexes() as caused_hexes: caused_hexes.remove(self)
		with self.victim.lock_hexes() as hexes: hexes.remove(self)

	def touch(self, master, arena):
		def has_game(fighter):
			b = arena.as_battler(fighter, maybe=True)
			return b and b.game

		# В некоторых случаях лучше подкрутить фактическую длительность хекса.
		if self.time_based and arena and (
			# Случай 1. ХЕКСЫ В ХОД ЖЕРТВЫ
			# Хекс тикает в конце хода персонажа, на которого наложен. Багофича такого подхода в том, что если хекс применён на ходу этого же персонажа,
			# например, персонаж в свой ход наложил хекс сам на себя, то хекс тикнет в конце этого же хода, т. е. практическая длительность окажется на единицу меньше.
			# Чтобы это обойти, используется skip_turns, по сути добавляемый к длительности хекса (не отображаемой — turns, но фактической).
			arena.whose_turn() == self.victim

			# Случай 2. ХЕКСЫ ОТ ИМЕНИ ИГРОКА
			# Реальная длительность в (N + 1) нужна, чтобы, если наложить хекс, длящийся всего 1 ход, на противника, скорость которого равна твоей —
			# на твоём следующем ходу хекс ещё остался висеть. Иначе в глазах человека длительность 1 будет подозрительно похожа на 0, 2 — на 1, и т. д.
			# (С точки зрения механики этого НЕ следует делать, но...)
			or has_game(master)):

			self.skip_turns += 1

	def tick(self, arena):
		check(self.applied, "not applied", not self.ran_out, "хекс истёк")
		if self.time_based:
			if self.skip_turns:
				self.skip_turns -= 1
			else:
				self.turns -= 1

		self.do_tick(arena)
		if self.victim.alive and self.ran_out: self.end(self.TIMEOUT, arena)

	def cancel(self, reason=CANCELLED, arena=None):
		check(self.applied, "not applied", not self.ran_out, "ran_out")
		self.turns = 0
		check(self.ran_out, "not ran_out after forced runout")
		self.end(reason, arena)

	def do_start(self): pass
	def do_tick(self, arena): pass
	def do_finish(self, reason, arena): pass
	def do_change_power(self, power, turns): pass
	def do_merge(self, hex, succeed): pass
	def do_respite_remove_cost_verb_and_prefix(self, game): return None

	def end(self, reason, arena):
		self.unapply()
		self.do_finish(reason, arena)

	def short_desc(self, cmd_prefix="", for_multipad=False, flip=False, cmd=None):
		# desc [turns]turns[/turns] [cmd]cmd
		# или
		# cmd[/cmd] turns[/turns] desc[/desc]
		name = self.name(self, flip=flip)
		if for_multipad: name = multipad.escape(name)
		desc = cap_first(name)
		if for_multipad and flip: desc += "[/desc]"

		turns = self.time_based and ("" if not for_multipad or flip else "[turns]") + str(self.turns) + "t" + ("[/turns]" if for_multipad else "")
		cmd = cmd and ("" if not for_multipad or flip else "[cmd]") + "(" + cmd + ")" + ("[/cmd]" if for_multipad and flip else "")
		dispelling = None
		if self.dispell_amount:
			bar = self.dispelling_bar(flip=flip)
			if for_multipad: bar = multipad.escape(bar)
			dispelling = ("" if not for_multipad or flip else "[dis]") + bar + ("[/dis]" if for_multipad and flip else "")
		return left_to_right(desc, turns, dispelling, cmd, flip=flip)

	def change_power(self, power=None, turns=None):
		nturns = None
		if self.time_based:
			nturns = max(self.turns, self.turns_from_power(power)) if turns is None and power is not None else turns

		self.do_change_power(power if power is not None else self.power, nturns if nturns is not None else self.turns)

		if power is not None: self.power = power
		if nturns is not None: self.turns = nturns

	@classmethod
	def name(cls, instance=None, flip=False): return cls.do_name(instance, flip)
	@classmethod
	def do_name(cls, instance, flip): raise NotImplementedError("do_name")

	def detail(self, game): return self.do_detail(game)
	def do_detail(self, game): raise NotImplementedError("do_detail")

	@classmethod
	def cmd(cls): return cls.do_cmd()
	@classmethod
	def do_cmd(cls): raise NotImplementedError("do_cmd")

	def turns_from_power(self, power): return self.do_turns_from_power(power)
	def do_turns_from_power(self, power): return 10

	def victim_usefulness(self): return 'bad' # 'bad', 'mixed', 'good'
	def dispellable(self): return False
	def merge_behavior(self): return 'add' # 'add', 'strongest'
	time_based = True
	def stronger_is_longer(self): return self.turns_from_power(10) >= self.turns_from_power(1)

	def dispell(self, power, magical=True, hook=None, arena=None):
		assert not magical or self.dispellable()
		self.dispell_amount += power
		if self.dispell_amount >= self.power:
			if hook: hook(True, min(power / self.power, 1))
			self.cancel(arena=arena)
		else:
			if hook: hook(False, power / self.power)

	def dispelling_bar(self, flip=False):
		part = (self.power - self.dispell_amount) / self.power
		return left_to_right(Con.vital_bar(part, 1, 5, fillchar='=', flip=flip), "{}%".format(percentage(part)), flip=flip)

	def exclamations(self, power=None):
		if power is None: power = self.power
		return "!!!" if power >= 3.5 else "!" if power >= 2 else ""

	def __getstate__(self):
		check(self.applied, "not applied?!")
		return {k: v for k, v in self.__dict__.items() if not (
			k in (
				'applied',         # резолвится здесь
				'victim'           # резолвится Fighter
			) or k in ('skip_turns', 'dispell_amount') and not v or k == 'turns' and v == 1)}

	def __setstate__(self, state):
		self.__init__(1, turns=1)
		self.__dict__.update(state)
		self.applied = True    # отбрасывается здесь

class RageHex(Hex):
	#  мин. 1.2x @ pow → 0
	#       1.5x @ pow = 1
	# макс. 5.0x @ pow = 12.67
	physdam_x = property(lambda self: clamp(1.2 + 0.3 * self.power, 1.2, 5.0))

	#  мин. 1.1x @ pow → 0
	#       1.2x @ pow = 1
	# макс. 2.2x @ pow = 11
	backlash_x = property(lambda self: clamp(1.1 + 0.1 * self.power, 1.1, 2.2))

	def do_start(self):
		self.victim.note(lambda sink: sink.youify("{Вы/F} приходит{е/} в ярость!", self.victim))

	def do_finish(self, reason, arena):
		if reason in (Hex.TIMEOUT, Hex.CANCELLED): self.victim.note(lambda sink: sink.youify("{Вы/F} успокаивает{есь/ся}.", self.victim))

	@classmethod
	def do_name(cls, instance, flip):
		m = instance and round(instance.physdam_x, 1)
		return "ярость" + (f" {m}x" if m is not None and m != 1.5 else "")

	def do_detail(self, game): return \
		"Увеличивает физическую атаку (x{}) и любой получаемый урон (x{}).".format(round(self.physdam_x, 1), round(self.backlash_x, 1))

	@classmethod
	def do_cmd(cls): return 'rage'
	def do_turns_from_power(self, power): return clamp(ceil(10*power**0.2), 3, 20)

class RageHexTest(TestCase):
	def __init__(self, *args, **kargs):
		super().__init__(*args, **kargs)
		self.dummy = RageHex.__new__(RageHex)

	def cases(self): return (-10, 1.2, 1.1), (0, 1.2, 1.1), (1, 1.5, 1.2), (11, 4.5, 2.2), (12.67, 5, 2.2), (99.99, 5, 2.2)
	def one(self, power, ref_physdam_x, ref_backlash_x):
		self.dummy.power = power
		self.assertEqual(tuple(round(value, 1) for value in (self.dummy.physdam_x, self.dummy.backlash_x)), (ref_physdam_x, ref_backlash_x))

class DeathWordHex(Hex):
	def do_start(self):
		self.victim.note(lambda sink: sink.youify("{вы/F:G} получаете смертный приговор", self.victim) + ".")

	def do_finish(self, reason, arena):
		if reason == Hex.TIMEOUT:
			check(self.master.alive, "мастер мёртв", self.victim.alive, "жертва мертва")
			self.victim.die(arena, hook=lambda: self.victim.note(lambda sink: sink.youify("{Вы/F} умирает{е/} в исполнение Смертного приговора.", self.victim)))
		elif reason == Hex.CANCELLED:
			self.victim.note(lambda sink: sink.youify("{Вы/F} больше не чувствует{е/} дыхание смерти.", self.victim))

	@classmethod
	def do_name(cls, instance, flip): return "смертный приговор"
	def do_detail(self, game):
		msg = "Смерть через {turns}".format(turns = plural(self.turns, "{N} ход{/а/ов}"))
		if game and self.victim is game.player:
			msg += ", если маг, наложивший заклинание, останется жив к этому времени"
		return msg + "."

	def do_respite_remove_cost_verb_and_prefix(self, game):
		return 40 if self.turns >= 10 else 80, "снять", 'break'

	@classmethod
	def do_cmd(cls): return 'deathword'
	def do_turns_from_power(self, power): return clamp(ceil(16 * power**-0.7), 8, 20)
	def dispellable(self): return True
	def merge_behavior(self): return 'strongest'

	def do_tick(self, arena):
		if 1 <= self.turns <= 3:
			self.victim.note(lambda sink: sink.you == self.victim and (
				"Ваше время на исходе." if self.turns >= 3 else
				"Вы чувствуете себя {} на плаху.".format(sink.you.gender.ize("восходящ{им/ей}")) if self.turns == 2 else
				"Вы слышите свист гильотины."))

class Bleeding(Hex):
	def __init__(self, power, *, turns=None):
		super().__init__(power, turns=turns)
		self.precise_damage = 0

	@classmethod
	def do_name(cls, instance, flip): return "кровотечение" + (instance.exclamations() if instance else "")
	def do_detail(self, game): return "-{0}% HP/ход; уменьшает ловкость (-{1}).".format(round(self.precise_hp_percentile_decay), round(self.dex_debuff))

	def do_respite_remove_cost_verb_and_prefix(self, game):
		return clamp(round(self.turns * 2), 5, 30), "вылечить", 'cure'

	def do_start(self):
		self.victim.note(lambda sink: sink.youify("У {вас/F:G} идёт кровь", self.victim) + (self.exclamations() or "."))

	def do_tick(self, arena):
		self.precise_damage += self.precise_hp_percentile_decay/100 * self.victim.mhp
		dmg = floor(self.precise_damage)
		if dmg > 0:
			def get_note(sink, fatal):
				if fatal:
					msg = sink.youify("{Вы/F} умирает{е/} от потери крови", self.victim)
				else:
					msg = sink.youify("У {вас/F:G} идёт кровь", self.victim)
				return msg + Beam.damage_paren(dmg) + "."
			self.victim.ouch(dmg, self.master, arena, hook=lambda fatal: self.victim.note(lambda sink: get_note(sink, fatal)), count_as_attack=False)
			self.precise_damage -= dmg
		self.power = self.decay_power(self.power)

	def do_finish(self, reason, arena):
		if reason in (self.TIMEOUT, self.CANCELLED):
			self.victim.note(lambda sink: sink.youify("{ваше /}кровотечение{/ F:G} останавливается.", self.victim))

	def do_change_power(self, power, turns):
		if power >= self.power:
			self.victim.note(lambda sink: sink.youify("{ваше /}кровотечение{/ F:G} усиливается", self.victim) + (self.exclamations(power) or "."))

	@classmethod
	def do_cmd(cls): return 'bleeding'

	def decay_power(self, power): return power * self.POWER_DECAY
	def do_turns_from_power(self, power): return clamp(ceil(log(0.5 / power, self.POWER_DECAY)), 3, 20)

	precise_hp_percentile_decay = property(lambda self: clamp(2.5 * (self.power**0.75 if self.power > 1 else self.power), 1, 5))
	dex_debuff = property(lambda self: max(1, round(3 * self.power**0.5)))
	POWER_DECAY = 0.88

class FrailnessHex(Hex):
	@classmethod
	def do_name(cls, instance, flip): return "хрупкость"
	def do_detail(self, game):
		ac_with = self.victim.ac
		ac_without = self.victim.calculate_ac(Imagination().remove(self))
		if ac_without > ac_with:
			return "{} броню (AC-{}).".format("Нейтрализует" if ac_with == 0 else "Расщепляет", ac_without - ac_with)
		else:
			return "Нет видимого эффекта."

	def do_start(self):
		self.victim.note(lambda sink: sink.youify("{вы/F} становит{есь/ся} хрупк", self.victim) + self.victim.gender.ize("{им/ой}") + ".")

	def do_change_power(self, power, turns):
		if power >= self.power:
			self.victim.note(lambda sink: sink.youify("{ваша /}хрупкость{/ F:G} усугубляется.", self.victim))
		else:
			self.victim.note("Это не даёт ощутимого эффекта.")

	def do_finish(self, reason, arena):
		if reason in (self.TIMEOUT, self.CANCELLED):
			self.victim.note(lambda sink: sink.youify("{вы/F} оправляет{есь/ся} от хрупкости.", self.victim))

	def ac_malus(self, ac, power=None):
		if power is None: power = self.power
		relative = 1 - (1 + 0.5 * power)**-0.5
		absolute = 1.8 * power ** 0.8
		minimum = 3
		return max(0, min(ac, max(minimum, ceil(absolute + ac * relative))))

	@classmethod
	def do_cmd(cls): return 'frailness'
	def do_turns_from_power(self, power): return clamp(round(11 * power**0.5), 3, 20)
	def dispellable(self): return True

class Poison(Hex):
	def __init__(self, power, *, turns=None):
		super().__init__(power, turns=turns)
		self.hp_dam_per_turn = 1
		self.mp_dam_per_turn = 1
		self.kind = 'plain'

	@classmethod
	def do_name(cls, instance, flip):
		name = ("смертельный " if instance and instance.expected_total_damage() >= instance.victim.hp else "") + "яд"
		if instance and instance.kind == 'poison2': name += " II"
		return name

	@classmethod
	def do_cmd(cls): return 'poison'
	def do_detail(self, game):
		return "-{} HP{}/ход.".format(self.hp_dam_per_turn,
			" и MP" if self.hp_dam_per_turn == self.mp_dam_per_turn else " и {} MP".format(self.mp_dam_per_turn))
	def do_turns_from_power(self, power): return clamp(round(4 * power**0.5), 2, 20)

	def do_respite_remove_cost_verb_and_prefix(self, game):
		return clamp(round(self.turns * (1 + self.hp_dam_per_turn + 2 * self.mp_dam_per_turn)), 10, 50), "вылечить", 'cure'

	def expected_total_damage(self, power=None, turns=None):
		if turns is None: turns = self.turns
		return self.hp_dam_per_turn * turns

	def do_start(self):
		self.victim.note(lambda sink: sink.youify("{вы/F} отравлен{ы//а/о}", self.victim) + ".")

	def do_finish(self, reason, arena):
		if reason in (self.TIMEOUT, self.CANCELLED):
			def get_note(sink):
				return sink.youify("Действие яда{/ на F:G}", self.victim) + (" прекращается" if reason == self.CANCELLED else " заканчивается") + "."
			self.victim.note(get_note)

	def do_change_power(self, power, turns):
		if power >= self.power:
			def get_note(sink):
				if self.expected_total_damage() < self.victim.hp <= self.expected_total_damage(power, turns):
					return sink.youify("{вы/F} смертельно отравлен{ы//а/о}", self.victim) + "!"
				else:
					return sink.youify("{вы/F} ещё сильнее отравлен{ы//а/о}", self.victim) + "."
			self.victim.note(get_note)

	def do_tick(self, arena):
		dam = self.hp_dam_per_turn
		mp_dam = max(0, min(self.mp_dam_per_turn, self.victim.mp)) if self.victim.has_magic() else 0
		self.victim.cur_mp -= mp_dam
		def get_note(sink, fatal):
			if fatal:
				msg = sink.youify("{вы/F:G} умирает{е/} от яда", self.victim)
			else:
				msg = sink.youify("Яд течёт по{ вашим/} венам{/ F:G}", self.victim)
			return msg + Beam.damage_paren(dam, mp=mp_dam) + "."
		self.victim.ouch(dam, self.master, arena, hook=lambda fatal: self.victim.note(lambda sink: get_note(sink, fatal)), count_as_attack=False)

class FetterHex(Hex):
	time_based = False
	@classmethod
	def do_name(cls, instance, flip): return "оковы"

	@classmethod
	def do_cmd(cls): return 'fetter'
	def do_detail(self, game):
		ev_with = self.victim.ev
		ev_without = self.victim.calculate_ev(Imagination().remove(self))
		msg = "Не дают атаковать врукопашную"
		if ev_with < ev_without: msg += "; EV-{}".format(ev_without - ev_with)
		return msg + "."

	def do_start(self):
		self.victim.note(lambda sink: sink.youify("{вы/F} заключ{ены/ён/ена/ено} в оковы", self.victim) + ".")

	def do_finish(self, reason, arena):
		if reason in (self.TIMEOUT, self.CANCELLED):
			def get_note(sink):
				return sink.youify("{Вы/F:G} освобождает{есь/ся} от оков", self.victim) + "."
			self.victim.note(get_note)

	def dispellable(self): return True
	def ev_malus(self, ev, power=None):
		if power is None: power = self.power
		return max(0, min(ev, round(ev * (1 - (1 + power) ** -0.7))))

	def phys_break_power_dis(self, attacker):
		pow = 0.5 * (attacker.str / 10) ** 0.7
		return Distribution.Bell(pow * 0.3, pow, pow * 1.5)

	def phys_break(self, attacker, arena):
		attacker.note(lambda sink: sink.youify("{Вы/F} пытает{есь/ся} вырваться.", attacker))
		self.dispell(self.phys_break_power_dis(attacker).roll(), magical=False, arena=arena)
		arena.set_action_cost(attacker, max(0.5, 1 - attacker.str / 50))

	def phys_break_help(self):
		return "Вырваться из оков." + "\n" + Dispell.human_estimate_turns_left(self, self.phys_break_power_dis(self.victim))

class GraspHex(Hex):
	time_based = False
	def __init__(self, power, *, turns=None):
		super().__init__(power, turns=turns)
		self.ticks = 0
		self.struggled_on_this_turn = False

	@classmethod
	def do_name(cls, instance, flip): return "захват" + (instance.exclamations() if instance else "")

	@classmethod
	def do_cmd(cls): return 'grasp'

	def do_start(self):
		self.victim.note(lambda sink: sink.youify("{Вы/F} заключает{е/}", self.master) + sink.youify(" {вас/F:A} в свои объятия", self.victim) + ".")

	class AsphyxiationBeam(Beam):
		def __init__(self, grasp, master, target, arena, master_imagination=None, target_imagination=None):
			super().__init__(master, target, arena, master_imagination, target_imagination)
			self.grasp = grasp

		def on_elements(self):
			return self.Physical(tuple(self.grasp.power ** 0.7 * x for x in (0, 1, 2)), pierce=1)

		def on_hp_damage(self, hp, fatal):
			def get_note(sink):
				if hp:
					if fatal:
						msg = sink.youify("{Вы/F}", self.target) + Beam.damage_paren(hp) + sink.youify(" окончательно задыхает{есь/ся} в", self.target)
						msg += sink.youify("{ ваших/} объятиях{/ F:G}", self.master) + "."
					else:
						msg = sink.youify("{Вы/F} душит{е/}", self.master) + sink.youify(" {вас/F:A}", self.target) + Beam.damage_paren(hp) + "."
					return msg
			self.arena.note(get_note)

	def asphyxiation_beam(self, arena):
		return self.AsphyxiationBeam(self, self.master, self.victim, arena)

	def do_tick(self, arena):
		self.asphyxiation_beam(arena).launch()
		if self.struggled_on_this_turn:
			self.struggled_on_this_turn = False
		else:
			limit = self.master.str ** 0.5
			if self.power < limit: self.power = min(limit, self.power + self.master.str / 80)
			if self.dispell_amount: self.dispell_amount = max(0, self.dispell_amount - self.master.str / 200)
		self.ticks += 1

	def do_detail(self, game):
		ev_with = self.victim.ev
		ev_without = self.victim.calculate_ev(Imagination().remove(self))
		msg = "Не даёт атаковать врукопашную."
		if ev_with < ev_without: msg += "\nEV-{}.".format(ev_without - ev_with)
		msg += "\nУдушение: ~{} HP/ход.".format(round(self.asphyxiation_beam(None).estimate_damage().avg, 1))
		return msg

	def do_finish(self, reason, arena):
		if reason in (self.TIMEOUT, self.CANCELLED) and self.master.alive:
			def get_note(sink):
				return sink.youify("{Вы/F:G} освобождает{есь/ся} от", self.victim) + sink.youify("{ вашего/} захвата{/ F:G}", self.master) + "."
			self.victim.note(get_note)

		if arena:
			vb = arena.as_battler(self.victim, maybe=True)
			if vb: vb.set_cooldown('grasp_immunity', 1+randrange(2))

	def ev_malus(self, ev, power=None):
		if power is None: power = self.power
		return max(0, min(ev, round(ev * (1 - (1 + power) ** -0.7))))

	def phys_break_power_dis(self, attacker):
		pow = 0.75 * (attacker.str / self.master.str) ** 0.5
		return Distribution.Bell(pow * 0.3, pow, pow * 1.5)

	def phys_break(self, attacker, arena):
		self.struggled_on_this_turn = True
		attacker.note(lambda sink: sink.youify("{Вы/F} пытает{есь/ся} вырваться.", attacker))
		self.dispell(self.phys_break_power_dis(attacker).roll(), magical=False, arena=arena)
		arena.set_action_cost(attacker, max(0.5, 1 - attacker.str / 50))

	def phys_break_help(self):
		return "Вырваться из захвата." + "\n" + Dispell.human_estimate_turns_left(self, self.phys_break_power_dis(self.victim))

class SlimeHex(Hex):
	@classmethod
	def do_name(cls, instance, flip): return "слизь" + (instance.exclamations() if instance else "")

	@classmethod
	def do_cmd(cls): return 'slime'
	def do_detail(self, game):
		imag = Imagination().remove(self)
		v = self.victim
		str_wo, int_wo, dex_wo, spd_wo = v.calculate_str(imag), v.calculate_int(imag), v.calculate_dex(imag), v.calculate_spd(imag)
		str_with, int_with, dex_with, spd_with = v.str, v.int, v.dex, v.spd
		parts = [
			spd_with < spd_wo and "-{} SPD".format(spd_wo - spd_with),
			str_with < str_wo and "-{} STR".format(str_wo - str_with),
			int_with < int_wo and "-{} INT".format(int_wo - int_with),
			dex_with < dex_wo and "-{} DEX".format(dex_wo - dex_with)]
		return (", ".join(filter(None, parts)) or "Не оказывает эффекта") + "."
	def do_turns_from_power(self, power): return clamp(round(9 * power**0.5), 2, 20)

	def do_respite_remove_cost_verb_and_prefix(self, game):
		return clamp(round(self.turns * self.power), 10, 50), "снять", 'clean'

	def do_start(self):
		self.victim.note(lambda sink: sink.youify("{вы/F} покрывает{есь/ся} слизью", self.victim) + ".")

	def do_finish(self, reason, arena):
		if reason in (self.TIMEOUT, self.CANCELLED):
			def get_note(sink):
				return sink.youify("Слизь отстаёт от{ вашего/} тела{/ F:G}", self.victim) + "."
			self.victim.note(get_note)

	def do_change_power(self, power, turns):
		if power >= self.power:
			def get_note(sink):
				return sink.youify("Слой слизи на {вас/F:P} становится толще", self.victim) + "."
			self.victim.note(get_note)

	def speed_debuff(self, spd):
		relative = 1 - (1 + 0.2 * self.power ** 0.5) ** -0.5
		absolute = 10 * (0.5 + 0.5 * self.power ** 0.5)
		debuff = max(1, round(spd * relative + absolute))
		return min(debuff, spd // 2)

	def stat_debuff(self, stat):
		relative = 1 - (1 + 0.2 * self.power ** 0.5) ** -0.5
		absolute = 0.5 + 2 * self.power ** 0.5
		debuff = max(1, round(stat * relative + absolute))
		return min(debuff, stat // 2)

	def str_debuff(self, str): return self.stat_debuff(str)
	def int_debuff(self, int): return self.stat_debuff(int)
	def dex_debuff(self, dex): return self.stat_debuff(dex)

class ParasiteHex(Hex):
	@classmethod
	def do_name(cls, instance, flip): return "паразит"

	@classmethod
	def do_cmd(cls): return 'parasite'
	def do_detail(self, game):
		is_you = game and self.victim == game.player
		msg = "Внутри {} растут личинки с парализующими укусами.".format("вас" if is_you else self.victim.name.genitive)
		if is_you: msg += "\nВы можете заражать других."
		return msg
	def do_turns_from_power(self, power): return 13

	def do_respite_remove_cost_verb_and_prefix(self, game):
		return 300, "вылечить", 'cure'

	def do_start(self):
		self.victim.add_special(Impregnation(self))

	def do_finish(self, reason, arena):
		sp = next((sp for sp in self.victim.specials if isinstance(sp, Impregnation) and sp.hex == self), None)
		if sp: self.victim.remove_special(sp)

		if reason in (self.TIMEOUT, self.CANCELLED):
			def get_note(sink):
				return sink.youify("Личинки внутри {вас/F:G} погибают.", self.victim)
			self.victim.note(get_note)

	def do_tick(self, arena):
		if self.ran_out:
			Impregnation.give_birth(self.victim, arena)
			self.turns = randrange(12, 16)

class ParalysisHex(Hex):
	@classmethod
	def do_name(cls, instance, flip): return "паралич"

	@classmethod
	def do_cmd(cls): return 'paralysis'
	def do_detail(self, game):
		return "{} вы не сможете сделать ничего.".format("На следующем ходу" if self.turns == 1 else plural(self.turns, "Следующие {N} ход{/а/ов}"))
	def do_turns_from_power(self, power): return clamp(round(power ** 0.5), 1, 3)

	def do_start(self):
		self.victim.paralyze()

	def do_finish(self, reason, arena):
		self.victim.unparalyze()
		if reason in (self.TIMEOUT, self.CANCELLED):
			self.victim.note(lambda sink: sink.youify("{ваш /}паралич{/ F:G} проходит.", self.victim))

			if arena:
				vb = arena.as_battler(self.victim, maybe=True)
				if vb: vb.set_cooldown('paralysis_immunity', 2+randrange(2))

class SilenceHex(Hex):
	@classmethod
	def do_name(cls, instance, flip): return "тишина"

	@classmethod
	def do_cmd(cls): return 'silence'
	def do_detail(self, game): return "Не даёт читать заклинания."
	def do_turns_from_power(self, power): return clamp(rand_round(3.8 * power ** 0.4), 2, 12)
	def merge_behavior(self): return 'strongest'

	def do_respite_remove_cost_verb_and_prefix(self, game):
		return clamp(round(self.turns * 6), 10, 50), "снять", 'break'

	def do_start(self):
		self.victim.note(lambda sink: sink.youify("{Вас/F:A} окружает мёртвая тишина.", self.victim))

	def do_change_power(self, power, turns):
		if power >= self.power:
			self.victim.note(lambda sink: sink.youify("Тишина вокруг {вас/F:G} набирает силу.", self.victim))

	def do_finish(self, reason, arena):
		if reason in (self.TIMEOUT, self.CANCELLED):
			self.victim.note(lambda sink: sink.youify("Тишина вокруг {вас/F:G} рассеивается.", self.victim))

class BarrierHex(Hex):
	@classmethod
	def do_name(cls, instance, flip): return "барьер"
	@classmethod
	def do_cmd(cls): return 'barrier'
	def victim_usefulness(self): return 'good'
	def merge_behavior(self): return 'strongest'
	def do_detail(self, game): return "Щит против физического (+{} AC) и элементального (rFire+, rElec+) урона.".format(self.ac_bonus())
	def dispellable(self): return True

	def do_start(self):
		self.victim.note(lambda sink: sink.youify("Вокруг {вас/F:G} формируется защитный барьер.", self.victim))

	def do_finish(self, reason, arena):
		if reason in (self.CANCELLED, self.TIMEOUT):
			if arena:
				arena.note(lambda sink: sink.youify("Барьер вокруг {вас/F:G} рассеивается.", self.victim))
				vb = arena.as_battler(self.victim, maybe=True)
				if vb: vb.set_cooldown('barrier', 2)

	def do_turns_from_power(self, power): return clamp(round(8 * power ** 0.5), 4, 16)
	def ac_bonus(self): return max(3, round(9 * self.power ** 0.5))
	def fire_resist(self): return 1 - (1 + self.power) ** -0.5
	def elec_resist(self): return self.fire_resist()

# По инстансу на каждое запомненное заклинание у каждого бойца.
class Spell:
	LIST_ORDER = 0
	TARGETING = 'single' # 'single', 'mass', 'n/a', 'dispell-like', 'self'
	@classmethod
	def name(cls, mode): return cls.do_name(mode)
	@classmethod
	def do_name(cls, mode): raise NotImplementedError("do_name")

	@classmethod
	def cmd(cls): return cls.do_cmd()
	@classmethod
	def do_cmd(cls): raise NotImplementedError("do_cmd")

	def mp_cost(self): return self.do_mp_cost()
	def do_mp_cost(self): raise NotImplementedError("do_mp_cost")

	def validate_target(self, master, target, arena):
		if self.TARGETING == 'single':
			assert isinstance(target, Fighter), self
		elif self.TARGETING == 'mass' or self.TARGETING == 'n/a':
			assert not target, self
		elif self.TARGETING == 'dispell-like':
			assert Dispell.valid_target(master, target, arena), self
		elif self.TARGETING == 'self':
			assert master == target, self
		else: impossible(self.TARGETING, "targeting")

	def cast(self, master, target, arena):
		self.validate_target(master, target, arena)
		self.do_cast(master, target, arena)
	def do_cast(self, master, target, arena): raise NotImplementedError("do_cast")

	def attack_help(self, master, target, arena, game): return self.do_help(master, target, arena, game, 'attack')
	def entrance_help(self, master, target, arena, game): return self.do_help(master, target, arena, game, 'entrance')
	def do_help(self, master, target, arena, game, mode): raise NotImplementedError("do_help")
	def do_entrance_preview(self, master, target, arena): return None

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
		self.do_note_target(target).note(lambda sink: sink.you == self.do_note_target(target) and self.apply_message(target))

	def revert(self, target):
		check(self.applied, "not applied", self.target == target, "target?!")
		target.upgrades.remove(self)
		target.ap_used -= self.ap_taken
		self.do_revert(target)
		self.do_note_target(target).note(lambda sink: sink.you == self.do_note_target(target) and self.revert_message(target))
		self.applied = False

	def do_note_target(self, target): return target
	def do_apply(self, target): pass
	def do_revert(self, target): pass

	def apply_message(self, target): return self.do_apply_message(target)
	def revert_message(self, target): return self.do_revert_message(target)

	def do_apply_message(self, target): return None
	def do_revert_message(self, target): return None

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
	STAT = AMOUNT = LIMIT = None
	statname, statgender = Noun.PLACEHOLDER, Gender.UNKNOWN

	def __init__(self):
		super().__init__()
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

	def set_base_stat(self, target, value):
		with target.save_relative_vitals():
			setattr(target, 'base_' + self.STAT, value)

	def do_sell_accusative(self, target): return "часть {0} {1} ({2} -> {3})".format(
		self.statgender.ize('свое{го/й}'), self.statname.genitive, self.get_base_stat(target), self.get_base_stat(target) - self.amount)

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
	def do_gold_cost(cls, target): return 120 + 40 * cls.count(target)

	def do_apply_message(self, target): return "Ваши мускулы наливаются силой."
	def do_revert_message(self, target): return "Ваши мускулы слабеют."

class IntUpgrade(StatUpgrade):
	STAT, AMOUNT, LIMIT = 'int', 5, 20
	statname, statgender = Noun.parse("{интеллект}", return_gender=True)

	@classmethod
	def do_gold_cost(cls, target): return 130 + 45 * cls.count(target)

	def do_apply_message(self, target): return "Ваш ум заостряется."
	def do_revert_message(self, target): return "Вы начинаете хуже соображать."

class DexUpgrade(StatUpgrade):
	STAT, AMOUNT, LIMIT = 'dex', 5, 20
	statname, statgender = Noun.parse("{ловкость:f}", return_gender=True)

	@classmethod
	def do_gold_cost(cls, target): return 70 + 35 * cls.count(target)

	def do_apply_message(self, target): return "Ваши рефлексы улучшаются."
	def do_revert_message(self, target): return "Вы чувствуете себя {0}.".format(target.gender.ize("неповоротлив{ым/ой}"))

class SpeedUpgrade(StatUpgrade):
	STAT, AMOUNT, LIMIT = 'spd', 30, 150
	statname, statgender = Noun.parse("{скорость:f}", return_gender=True)

	@classmethod
	def do_gold_cost(cls, target): return 140 + 60 * sum(1 for up in cls.find_all(target))

	def do_apply_message(self, target): return "Ваша кровь бурлит!"
	def do_revert_message(self, target): return "Ваша кровь остывает..."

class Firestorm(Spell):
	LIST_ORDER = 0
	TARGETING = 'mass'

	@classmethod
	def do_name(cls, mode):
		return "огненный шторм" if mode == 'long' else "огн. шторм" if mode == 'short' else "шторм" if mode == 'veryshort' else impossible(mode, "mode")

	class Beam(Beam):
		def on_elements(self):
			pow = max(3, 4.5 + signed_pow(self.master_int(), 0.65))
			return Beam.Fire((pow/1.8, pow/1.2, pow*1.2))

		def on_hp_damage(self, hp, fatal):
			def get_note(sink):
				if hp:
					if fatal and self.target.flavored_death:
						msg = sink.youify("{Вы/F}", self.target) + Beam.damage_paren(hp) + sink.youify(" превращает{есь/ся} в кучку пепла.", self.target)
					elif hp >= 5:
						msg = ((self.target.gender.ize("опаленн{ый/ая/ое}, ") if self.target == sink.you else "") +
							sink.youify("{вы/}{/опаленн}{/ый/ая/ое}{/ F} корчит{есь/ся} от боли", self.target) + Beam.damage_paren(hp) + ".")
					else:
						msg = sink.youify("{вы/F} слегка опален{ы/}", self.target) + Beam.damage_paren(hp) + "."
				else:
					msg = sink.youify("Огонь не наносит {вам/F:D} заметного урона", self.target) + Beam.damage_paren(hp) + "."
				return msg
			self.arena.note(get_note)

		def on_account(self): return 'magical'

	@classmethod
	def do_cmd(cls): return 'fstorm'

	def do_mp_cost(self): return 6

	def do_cast(self, master, target, arena):
		master.note(lambda sink: sink.youify("{Вы/F} устремляет{е/} ладонь в небо, шепча заклинание.", master))
		victims = [victim for victim in arena.enemies(master)]

		def accusative_victims_enumeration(sink):
			counted = [False] * len(victims)
			victim_names = []
			for victim_index, victim in enumerate(victims):
				if counted[victim_index]: continue
				if victim is sink.you:
					victim_name = "вас"
				else:
					victim_name = victim.name.accusative

					n_buddies = 0
					buddies_gender, buddies_gender_set = Gender.UNKNOWN, False
					for buddy_index in range(victim_index + 1, len(victims)):
						buddy = victims[buddy_index]
						if buddy.name == victim.name:
							n_buddies += 1
							counted[buddy_index] = True
							if buddy.gender != Gender.UNKNOWN:
								if not buddies_gender_set:
									buddies_gender, buddies_gender_set = buddy.gender, True
								elif buddies_gender != buddy.gender:
									buddies_gender = Gender.UNKNOWN
					if n_buddies > 0: victim_name += " с " + buddies_gender.ize("{друзьями/подружками}" if n_buddies > 1 else "{другом/подружкой}")
				victim_names.append(victim_name)

			return join_with_lastsep(victim_names, ", ", " и ")

		master.note(lambda sink: "Огненный вихрь настигает {}!".format(accusative_victims_enumeration(sink)))
		for victim in victims:
			self.Beam(master, victim, arena).launch()

	def do_help(self, master, target, arena, game, mode):
		return ("Огненный вихрь, поражающий всех противников." +
			"\nУрон: " +
			self.estimate_mass_damage(arena.enemies(master), lambda target: self.Beam(master, target, arena), do_max=mode == 'entrance' or game.god_mode) +
			".")

	def do_entrance_preview(self, master, target, arena): return self.Beam(master, target, arena)

	@staticmethod
	def estimate_mass_damage(targets, make_beam, do_max):
		dam_descs = []
		for target in targets:
			est = make_beam(target).estimate_damage()
			avg_dam_str = "~" + str(round(est.avg, 1)) + (", макс. " + str(round(est.max, 1)) if do_max else "")

			try:
				item = next(dd for dd in dam_descs if dd[0] == avg_dam_str)
			except StopIteration:
				item = (avg_dam_str, [])
				dam_descs.append(item)
			if target.name not in item[1]: item[1].append(target.name)
		return " / ".join(avg_dam_str + (" ({})".format(", ".join(names)) if len(dam_descs) > 1 else "") for avg_dam_str, names in dam_descs)

class Dispell(Spell):
	LIST_ORDER = 1
	TARGETING = 'dispell-like'

	@classmethod
	def do_name(cls, mode): return "развеять" if mode == 'long' or mode == 'short' or mode == 'veryshort' else impossible(mode, "mode")

	@classmethod
	def do_cmd(cls): return 'dispell'

	def do_mp_cost(self): return 1

	@classmethod
	def valid_target(cls, master, target, arena):
		if isinstance(target, Hex):
			if not target.dispellable(): return False

			usefulness = target.victim_usefulness()
			if usefulness == 'mixed': return True

			if arena:
				are_enemies = arena.are_enemies(master, target.victim)
				if usefulness == 'bad': return not are_enemies
				elif usefulness == 'good': return are_enemies
				else: impossible(usefulness, "usefullness")

			return True

		elif isinstance(target, Fighter):
			return target.dispellable and arena.are_enemies(master, target)
		else: impossible(target, "target")

	def do_cast(self, master, target, arena):
		if isinstance(target, Hex):
			assert target.dispellable()
			def hook(completed, part):
				def get_note(sink):
					msg = sink.youify("{вы/F} стряхивает{е/} с", master)
					if master == target.victim: msg += " себя"
					else: msg += sink.youify(" {вас/F:G}", target.victim)
					msg += " невидимую " + ("паутину" if target.victim_usefulness() == 'bad' else "пылинку")
					percent = percentage(target.dispell_amount / target.power)
					if not completed: msg += ". {}: {}".format(cap_first(target.name()), plural(percent, "развеян{/о/о} {N}%"))
					return msg + "."
				master.note(get_note)

			power = self.dispell_hex_amount_dis(master, target, arena).roll()

			score_power = power * target.victim.mhp * 0.1
			usefulness = target.victim_usefulness()
			k = 0.5 if usefulness == 'mixed' else 1
			if arena:
				if usefulness == 'bad' and master != target.master or usefulness == 'mixed':
					target.master.count_an_attack(score_power * k, master, arena, 'magical', 1 * k)
				if usefulness == 'good' and master != target.victim or usefulness == 'mixed':
					target.victim.count_an_attack(score_power * k, master, arena, 'magical', 1 * k)

			target.dispell(power, hook=hook, arena=arena)
		elif isinstance(target, Fighter):
			assert target.dispellable
			hp = rand_round(self.dispell_creature_amount_dis(master, target, arena).roll())
			def hook(fatal):
				def get_note(sink):
					msg = sink.youify("{вы/F} " + ("залатали" if fatal else "латает{е/}") + " дыру в реальности", master)
					msg += sink.youify(" вокруг {вас/F:G}", target) + Beam.damage_paren(hp) + "."
					return msg
				master.note(get_note)
			etc = {}
			if target.preset == 'lightning': etc['dont_explode'] = True
			target.ouch(hp, master, arena, hook=hook, account='magical', etc=etc)
		else: impossible(target, "target")

	def dispell_creature_amount_dis(self, master, target, arena):
		check(target, isinstance(target, Fighter) and target.dispellable, "target")
		base = (0.5 * master.int + (1 - master.int ** -0.15) * target.mhp) * master.int / (master.int + 0.3 * target.int)
		return Distribution.Bell(0.5 * base, base, 1.5 * base)

	def dispell_hex_amount_dis(self, master, hex, arena):
		check(hex, isinstance(hex, Hex) and hex.dispellable(), "hex")
		base = 1.6 * master.int / (master.int + 0.3 * hex.master.int)
		return Distribution.Bell(0.5 * base, base, 1.5 * base)

	@classmethod
	def targets_on_fighter(cls, master, target, arena):
		check(target, isinstance(target, Fighter), "target")
		if cls.valid_target(master, target, arena): yield target
		for hex in target.hexes:
			if cls.valid_target(master, hex, arena): yield hex

	def do_help(self, master, target, arena, game, mode):
		if isinstance(target, Fighter):
			msg = "Нанести ~{} ед. урона призванно{} {}.".format(
				round(self.dispell_creature_amount_dis(master, target, arena).estimate_avg(), 1), target.gender.ize("{му/й}"), target.name.dative)
		elif isinstance(target, Hex):
			msg = "Развеять"
			if target.victim == game.player: msg += " с себя"
			msg += " " + target.name()
			if target.victim != game.player: msg += " с " + target.victim.name.genitive
			msg += ".\n" + self.human_estimate_turns_left(target, self.dispell_hex_amount_dis(master, target, arena))
		else: impossible(target, "target")
		return msg

	@staticmethod
	def human_estimate_turns_left(hex, decay_dis, respite=False):
		avg_turns, max_turns = tuple(max(1, ceil((hex.power - hex.dispell_amount) / sample)) for sample in (decay_dis.estimate_avg(), decay_dis.estimate_min()))
		if avg_turns == max_turns:
			if avg_turns == 1:
				msg = "Вы уверены в успехе{}.".format(" развеивания" if respite else "")
			else:
				msg = ("Для развеивания в" if respite else "В") + "ам понадобится " + plural(avg_turns, "{N} " + ("попыт{ка/ки/ок}" if respite else "ход{/а/ов}")) + "."
		else:
			msg = ("Для развеивания в" if respite else "В") + "ам понадобится ~{}, максимум {}.".format(
				avg_turns, plural(max_turns, "{N} " + ("попыт{ка/ки/ок}" if respite else "ход{/а/ов}")))
		return msg

class ResistibleSpell(Spell):
	def do_power(self, master, target, master_imagination=None, target_imagination=None): return master.calculate_int(master_imagination) / 10
	def do_mr(self, master, target, master_imagination=None, target_imagination=None): return target.calculate_int(target_imagination) / 20

	def save_throw(self, master, target, master_imagination=None, target_imagination=None):
		return (self.do_power(master, target, master_imagination, target_imagination), self.do_mr(master, target, master_imagination, target_imagination),
			Arena.Cumulative(master, target, self.cmd()))

	def chance(self, master, target, arena, master_imagination=None, target_imagination=None):
		return Arena.hit_chance(arena, *self.save_throw(master, target, master_imagination, target_imagination))

	# Ослабление силы, если хекс всё-таки успешно применён.
	# Сейчас выполняется на тот же процент (без Cumulative), т. е. сопротивление 30% даёт 30% шанс полного уклонения и 30% ослабление.
	def resistance(self, master, target, master_imagination=None, target_imagination=None):
		return 1 - self.chance(master, target, None, master_imagination, target_imagination)

	def power(self, master, target, master_imagination=None, target_imagination=None):
		pow = self.do_power(master, target, master_imagination, target_imagination)
		pow *= (1 - self.resistance(master, target, master_imagination, target_imagination))
		return pow

	def do_prologue(self, master, target, arena): pass
	def do_dodged(self, master, target, arena, chance, roll):
		arena.note(lambda sink: sink.youify("{Вы/F} не поддаёт{есь/ся}.", target))

	def do_entrance_preview(self, master, target, arena):
		return OrderedDict((('chance', "{:.0%}".format(self.chance(master, target, arena))),))

	def do_help(self, master, target, arena, game, mode):
		return (
			"Шанс: {:.0%}.".format(self.chance(master, target, arena)) if mode == 'attack' else
			"Сопротивление: {:.0%}.".format(self.resistance(master, target)) if mode == 'entrance' else impossible(mode, "mode"))

	def do_cast(self, master, target, arena):
		self.do_prologue(master, target, arena)
		dodged, chance, roll = arena.dodge(*self.save_throw(master, target))
		if dodged:
			self.do_dodged(master, target, arena, chance, roll)
		else:
			power = self.power(master, target)
			self.do_apply(power, master, target, arena)

	def do_apply(self, power, master, target, arena): raise NotImplementedError("do_apply")

class HexSpell(ResistibleSpell):
	hex_class = Hex
	@classmethod
	def do_cmd(cls): return cls.hex_class.do_cmd()

	def do_apply(self, power, master, target, arena):
		if master != target:
			score_power = power * target.mhp * 0.1
			target.count_an_attack(score_power, master, arena, 'magical', 1)
		self.hex_class(power).apply(master, target, arena)

class Frailness(HexSpell):
	LIST_ORDER = 2
	hex_class = FrailnessHex
	@classmethod
	def do_name(cls, mode): return "хрупкость" if mode == 'long' or mode == 'short' else "хрупк." if mode == 'veryshort' else impossible(mode, "mode")
	def do_mp_cost(self): return 3

	def do_prologue(self, master, target, arena):
		arena.note(lambda sink: sink.youify("{Вы/F} сдувает{е/} с ладони воображаемую пыль в", master) + sink.youify("{ вашу/} сторону{/ F:G}.", target))

	def ac_malus(self, master, target, arena, master_imagination=None, target_imagination=None):
		return FrailnessHex.ac_malus(None, target.ac, self.power(master, target, master_imagination, target_imagination))

	def do_entrance_preview(self, master, target, arena):
		malus = self.ac_malus(master, target, arena)
		return OrderedDict((*super().do_entrance_preview(master, target, arena).items(),) + (('dam', "AC-{}".format(malus) if malus > 0 else "—"),))

	def do_help(self, master, target, arena, game, mode):
		malus = self.ac_malus(master, target, arena)
		msg = ("Расщепляет броню (AC-{}).".format(malus) if malus > 0 else "Не возымеет эффекта.") + "\n"
		return msg + super().do_help(master, target, arena, game, mode)

class DeathWord(HexSpell):
	hex_class = DeathWordHex
	@classmethod
	def do_name(cls, mode): return "смертный приговор" if mode == 'long' or mode == 'short' else "приговор" if mode == 'veryshort' else impossible(mode, "mode")

	def do_mp_cost(self): return 4

	def do_prologue(self, master, target, arena):
		def get_note(sink):
			return (sink.youify("{Вы/F} перечёркивает{е/}", master) + sink.youify(" {вас/F:A}", target) + " движением" +
				(" костлявой" if master.is_bone else "") + " руки.")
		arena.note(get_note)

class Fetter(HexSpell):
	hex_class = FetterHex
	@classmethod
	def do_name(cls, mode): return "оковы" if mode == 'long' or mode == 'short' or mode == 'veryshort' else impossible(mode, "mode")

	def do_mp_cost(self): return 3

	def do_prologue(self, master, target, arena):
		def get_note(sink):
			return sink.youify("{Вы/F} проворачивает{е/} руку в", master) + sink.youify("{ вашу/} сторону{/ F:G}", target) + "."
		arena.note(get_note)

class PhantasmalGate(Spell):
	TARGETING = 'n/a'
	@classmethod
	def do_name(cls, mode):
		return "потусторонние врата" if mode == 'long' else "потуст. врата" if mode == 'short' else "врата" if mode == 'veryshort' else impossible(mode, "mode")

	@classmethod
	def do_cmd(cls): return 'o.w.gate'

	def do_help(self, master, target, arena, game, mode):
		return "Призывает призрака на сторону заклинателя."

	def do_mp_cost(self): return 5

	GHOST_SUBTYPES = {
		'magic': ("{волшебный призрак:a}", {'str_k': .5, 'int_k': 1, 'spd_k': 2}),
		'bread': ("{призрак:a} хлеба", {}),
		'pudding': ("{призрак:a} пудинга", {'str_k': 1, 'int_k': .5, 'dex_k': .5, 'spd_base': 80}),
		'war': ("{призрак:a} войны", {'dex_k': 1}),
		'gun': ("{призрак:a} пушки", {'str_k': .5, 'dex_k': 1, 'spd_k': 2}) }
	def do_cast(self, master, target, arena):
		master_b = arena.as_battler(master)
		existing = set()
		for b in arena.squads[master_b.squad_id].members:
			if b.fighter.preset == 'ghost':
				existing.add(b.fighter.props['ghost_subtype'])
		chosen = choose(self.GHOST_SUBTYPES.items(), lambda item, _index: 0 if item[0] in existing else 1, default=None)
		if chosen is None: chosen = choose(self.GHOST_SUBTYPES.items())
		subtype, (name, opts) = chosen

		ghost = Fighter()
		ghost.preset, ghost.summoned = 'ghost', True
		ghost.props['ghost_subtype'] = subtype
		ghost.name, ghost.gender = Noun.parse(name, return_gender=True)

		with ghost.save_relative_vitals():
			ghost.xl = max(1, rand_round(master.xl * (1 - (1 + master.int ** 0.5) ** -0.5)))
			base = master.int
			ghost.base_str = max(5, rand_round(base * opts.get('str_k', 1 / 1.5)))
			ghost.base_int = max(5, rand_round(base * opts.get('int_k', 1 / 1.5)))
			ghost.base_dex = max(5, rand_round(base * opts.get('dex_k', 1 / 1.5)))
			ghost.base_spd = opts.get('spd_base', 100) + opts.get('spd_k', 1) * master.int
		ghost.set_unarmed(BareHands())
		arena.add(ghost, master_b.squad_id, UniversalAI(), shortcut_hint="Ghost")
		arena.note(lambda sink: sink.youify("{вы/F} шепчет{е/} заклинание, и рядом с {вами/ним/ней}", master) + " материализуется " + ghost.name + ".")

class DrainLife(Spell):
	@classmethod
	def do_name(cls, mode):
		return "похищение жизни" if mode == 'long' else "похищ. жизни" if mode == 'short' else "вамп." if mode == 'veryshort' else impossible(mode, "mode")

	@classmethod
	def do_cmd(cls): return 'lifedrain'

	def do_help(self, master, target, arena, game, mode):
		dis = self.drain_dis(master, target)
		master_has_summons = any(isinstance(sp, PhantasmalGate) for sp in master.spells)
		return "Высасывает ~{} (макс. {}) ед. жизни противника и {}.".format(
			round(dis.estimate_avg(), 1), ceil(dis.estimate_max()),
			"{} часть {}".format(*("распределяет", "между заклинателем и его друзьями") if master_has_summons else ("передаёт", "заклинателю")))

	def drain_dis(self, master, target, master_imagination=None, target_imagination=None):
		master_int, target_int = master.calculate_int(master_imagination), target.calculate_int(target_imagination)
		base = master_int ** 0.7 * master_int / (master_int + 0.5 * target_int)
		return Distribution.Bell(0.5 * base, base, 1.2 * base)

	def do_mp_cost(self): return 3

	def do_cast(self, master, target, arena):
		amount = min(max(1, round(self.drain_dis(master, target).roll())), target.hp)
		heal = rand_round(amount / 2)
		heal_desc = ""
		if heal:
			heal_targets = [arena.as_battler(ally) for ally in arena.allies(master, include_itself=True) if ally.hp < ally.mhp]
			shuffle(heal_targets)
			healed = dispense([ally_b.fighter.hp for ally_b in heal_targets], heal, [ally_b.fighter.mhp for ally_b in heal_targets])
			heal_desc = ", ".join("{}+{}".format(ally.shortcut, rhp - ally.fighter.hp) for ally, rhp in zip(heal_targets, healed) if rhp > ally.fighter.hp)

		def hook(fatal):
			def get_note(sink):
				if fatal:
					msg = sink.youify("{Вы/F} высасывает{е/} из", master) + sink.youify(" {вас/F:G} остатки жизни", target)
				else:
					msg = sink.youify("{Вы/F} высасывает{е/} из", master) + sink.youify(" {вас/F:G} жизнь", target)
				return msg + " ({})".format(", ".join(filter(None, (str(amount), heal_desc)))) + "."
			arena.note(get_note)

		target.ouch(amount, master, arena, hook=hook, account='magical')
		if heal:
			for i, ally in enumerate(heal_targets):
				if healed[i] > ally.fighter.hp: ally.fighter.cur_hp = healed[i]

class Barrier(Spell):
	TARGETING = 'self'
	@classmethod
	def do_name(cls, mode):
		return "барьер" if mode == 'long' or mode == 'short' or mode == 'veryshort' else impossible(mode, "mode")

	@classmethod
	def do_cmd(cls): return 'barrier'

	def do_mp_cost(self): return 4
	def power(self, master): return master.int / 10

	def do_help(self, master, target, arena, game, mode):
		return BarrierHex(self.power(master)).detail(game)

	def do_cast(self, master, target, arena):
		arena.note(lambda sink: sink.youify("{Вы/F} проворачивает{есь/ся} на месте.", target))
		BarrierHex(self.power(master)).apply(master, target, arena)

class BallLightning(Spell):
	TARGETING = 'n/a'

	@classmethod
	def do_name(cls, mode):
		return "шаровая молния" if mode == 'long' else "шар. молния" if mode == 'short' else "шар. молн." if mode == 'veryshort' else impossible(mode, "mode")

	@classmethod
	def do_cmd(cls): return 'b.lightning'

	def do_help(self, master, target, arena, game, mode):
		est = self.beam(master, game.player, arena).estimate_damage()
		elem_parts = ", ".join(est.describe_elem_parts())
		return ("Призывает шаровую молнию, взрыв которой наносит урон (~{}, макс. {}{}) всем окружающим.\n\n"
			"При преждевременном уничтожении молния наносит меньший урон или не наносит урона вовсе. Также молния может быть развеяна.").format(
				round(est.avg, 1), round(est.max, 1), ", " + elem_parts if elem_parts else "")

	def do_mp_cost(self): return 5

	def do_cast(self, master, target, arena):
		lightning = Fighter()
		lightning.preset = 'lightning'
		lightning.summoned = True
		def exists(postfix):
			return any(b.fighter.preset == 'lightning' and b.fighter.props.get('lightning_postfix', None) == postfix for b in arena.battlers)
		postfix = None if not exists(None) else choose((postfix for postfix in map(chr, range(ord('A'), ord('Z'))) if not exists(postfix)), default=None)

		lightning.name, lightning.gender = Noun.parse("{шаровая молния:af}", return_gender=True)
		if postfix:
			lightning.name += f" {postfix}"
			lightning.props['lightning_postfix'] = postfix
		lightning.props['master'] = master
		lightning.props['remaining_life'] = lightning.props['orig_life'] = 3 + randrange(3)

		with lightning.save_relative_vitals():
			lightning.xl = 1
			lightning.base_mhp = 1
			lightning.base_ev = 18
			lightning.base_spd = 150
			lightning.add_special(BallLightningTimeoutAndExplodeOnDeathOrTouch())
		arena.add(lightning, arena.as_battler(master).squad_id, BallLightningAI(), shortcut_hint="Lightning")
		arena.note(lambda sink: sink.youify("{вы/F} трёт{е/} эбонитовую палочку о шерсть, и рядом с {вами/ним/ней}", master) + " всплывает " + lightning.name + ".")

	@classmethod
	def beam(cls, master, target, arena, power_mod=1):
		return cls.Beam(master, target, arena, power_mod=power_mod)

	class Beam(Beam):
		def __init__(self, master, target, arena, master_imagination=None, target_imagination=None, power_mod=1):
			super().__init__(master, target, arena, master_imagination, target_imagination)
			self.power_mod = power_mod

		def on_elements(self):
			pow = self.power_mod * max(3, 4.5 + signed_pow(self.master_int(), 0.65))
			return Beam.Electricity((pow/1.8, pow/1.2, pow*1.2))

		def on_hp_damage(self, hp, fatal):
			def get_note(sink):
				if hp:
					msg = sink.youify("{Вы/F} получает{е/}", self.target)
					spark_obj = " разряд тока"
					if fatal: msg += " смертельный"
					elif hp <= 3: msg += " лёгкий"; spark_obj = " удар током"
					msg += spark_obj
				else:
					msg = sink.youify("{Вы/F} остаёт{есь/ся} невредим{ы//а/о}", self.target)
				return msg + Beam.damage_paren(hp) + "."
			self.target.note(get_note)

	@classmethod
	def act_explode(cls, lightning, arena):
		assert lightning.dead
		fizzle, rem, orig = False, *(lightning.props[prop_name] for prop_name in ('remaining_life', 'orig_life'))
		if rem > 0 and random() < 0.9 * (rem / orig) ** 1.5: fizzle = True

		if fizzle:
			arena.note(lambda sink: sink.youify("{вы/F} тает{е/} в воздухе.", lightning))
		else:
			power_mod = 0.1 + 0.9 * (1 - rem / orig)
			arena.note(lambda sink: sink.youify("{вы/F}" + (" взрывает{есь/ся}!" if power_mod > 0.5 else " вспыхивает."), lightning))
			for victim_b in arena.battlers:
				if not victim_b.fighter.alive: continue # пропустит также саму эту молнию
				cls.beam(lightning.props['master'], victim_b.fighter, arena, power_mod).launch()

class Chronosphere(Spell):
	TARGETING = 'n/a'
	@classmethod
	def do_name(cls, mode):
		return "хроносфера" if mode == 'long' else "хроносф." if mode == 'short' else "хроно" if mode == 'veryshort' else impossible(mode, "mode")

	@classmethod
	def do_cmd(cls): return 'chronosphere'

	def do_mp_cost(self): return 9

	def do_help(self, master, target, arena, game, mode):
		return "Останавливает время для всех, кроме заклинателя, на {}.".format(plural(self.turns(master), "{N} ход{/а/ов}"))

	def turns(self, master):
		return 4

	def do_cast(self, master, target, arena):
		arena.note(lambda sink: sink.youify("{Вы/F} запускает{е/} руку в ткань 3+1-пространства.", master))
		arena.stop_time(self.turns(master))

class DrainXP(ResistibleSpell):
	@classmethod
	def do_name(cls, mode):
		return "высасывание опыта" if mode == 'long' else "высасывание" if mode == 'short' else "высас." if mode == 'veryshort' else impossible(mode, "mode")

	@classmethod
	def do_cmd(cls): return 'drain'

	def do_mp_cost(self): return 3

	def do_help(self, master, target, arena, game, mode):
		return ("Это может снизить ваш уровень. Если вы задействовали больше очков умений, чем позволяет новый уровень, "
			"вы будете терять апгрейды в порядке, обратном порядку приобретения.\n" + super().do_help(master, target, arena, game, mode))

	def do_dodged(self, master, target, arena, chance, roll):
		arena.note(lambda sink: sink.youify("{Вы/F} пытает{есь/ся} высосать", master) + sink.youify(" {вас/F:A}, но {вы/он/она/оно} не поддаёт{есь/ся}.", target))

	def do_apply(self, power, master, target, arena):
		amount = min(bell(power / 20, power / 10, power / 7), target.xl + target.xp / target.xp_for_levelup())
		xl, _xp = target.drain_xp(amount, relative=True, emulate=True)
		def get_note(sink):
			arena.note(lambda sink: sink.youify("{Вы/F} высасывает{е/}", master) + sink.youify(" {вас/F:A} через трубочку", target) + f" (-{amount:.0%}).")
		target.note(get_note)

		if xl != target.xl:
			target.note(lambda sink: sink.youify("{Вы/F} теперь уровня", target) + f" {xl}!")
		target.drain_xp(amount, relative=True)

class SpellUpgrade(FighterUpgrade):
	SPELL_CLASS = Spell
	def __init__(self):
		super().__init__()
		self.spell = self.applied = None

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
	def do_shop_label(cls, target): return "Заклинание: " + cap_first(cls.SPELL_CLASS.name('short'))

class FirestormSpellUpgrade(SpellUpgrade):
	SPELL_CLASS = Firestorm

	@classmethod
	def do_gold_cost(cls, target): return 160

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
	def do_ap_cost(cls, target): return 1

	def do_sell_accusative(self, target): return "вашу магию Развеивания"

	@classmethod
	def do_cost_preface(cls, target): return "Вы научитесь развеивать заклинания за"

	def do_apply_message(self, target): return "Вы обучаетесь Развеиванию!"
	def do_revert_message(self, target): return "Вы больше не можете развеивать заклинания."

class FrailnessSpellUpgrade(SpellUpgrade):
	SPELL_CLASS = Frailness

	@classmethod
	def do_gold_cost(cls, target): return 120

	@classmethod
	def do_ap_cost(cls, target): return 1

	def do_sell_accusative(self, target): return "вашу магию Хрупкости"

	@classmethod
	def do_cost_preface(cls, target): return "Вы научитесь накладывать хрупкость на врагов за"

	def do_apply_message(self, target): return "Вы обучаетесь заклинанию Хрупкости!"
	def do_revert_message(self, target): return "Вы больше не можете ослаблять врагов."

class Ammunition:
	LIST_ORDER = 0
	MAX_CHARGES = INFINITE_CHARGES = None
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
		if self.finite_charges:
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
			index = target.ammos.index(self)
			target.ammos[index] = self.secondary_installations.pop()
			target.ammos[index].secondary_installations = self.secondary_installations
			self.secondary_installations = []
		else:
			# убрать по-нормальному
			self.weapon.ammos.remove(self)
		self.weapon = self.upgrade = None

	def times(self): return 1 + len(self.secondary_installations)

	def battle_name(self): return self.do_name(self, self.weapon, 'battle')
	@classmethod
	def shop_name(cls, target): return cls.do_name(None, target, 'battle')
	def respite_name(self, target): return self.do_name(self, target, 'respite')
	@classmethod
	def noun_name(cls): return cls.do_name(None, None, 'noun')
	@classmethod
	def plural_name(cls): return cls.do_name(None, None, 'plural')

	@classmethod
	# mode = 'battle', 'respite', 'noun', 'plural'
	def do_name(cls, instance, target, mode): raise NotImplementedError("do_name")

	@classmethod
	def name_up(cls, target, up): return cls.do_name_up(target, up)
	@classmethod
	def do_name_up(cls, target, up): pass

	def do_to_hit_bonus(self): return 0

	@classmethod
	def cmd(cls): return cls.do_cmd()
	@classmethod
	def do_cmd(cls): raise NotImplementedError("do_cmd")

	def __getstate__(self):
		return {k:v for k, v in self.__dict__.items() if k not in (
			'weapon', # резолвится Weapon
			) and not (k in ('secondary_installations',) and not v or k == 'charges' and v == self.MAX_CHARGES)}

	def __setstate__(self, state):
		self.__init__()
		self.__dict__.update(state)

class IncendiaryAmmunition(Ammunition):
	LIST_ORDER = 0
	MAX_CHARGES = Ammunition.INFINITE_CHARGES

	@staticmethod
	def human_times(times): return f"+{3 * times}"

	@classmethod
	def do_name(cls, instance, target, mode):
		return (
			"зажиг. патроны" + (cls.name_up(target, 0) or "") if mode == 'battle' else
			f"заж.{instance.human_times(instance.times())}" if mode == 'respite' else
			Noun.parse("{зажигательный патрон}") if mode == 'noun' else Noun.parse("{зажигательные патроны}") if mode == 'plural' else impossible(mode, 'mode'))

	@classmethod
	def do_name_up(cls, target, up):
		ammo = cls.find(target)
		times = (ammo.times() if ammo else 0) + up
		return times and cls.human_times(times)

	@classmethod
	def do_cmd(cls): return 'incendiary'

class SilenceAmmunition(Ammunition):
	LIST_ORDER = 1
	MAX_CHARGES = 4

	def do_recharge_cost(self): return 60
	@classmethod
	def do_name(cls, instance, target, mode):
		return (
			"тишина" if mode == 'battle' else
			"тиш." if mode == 'respite' else
			Noun.parse(("{патроны}" if mode == 'plural' else "{патрон}") + " тишины") if mode in ('noun', 'plural') else impossible(mode, 'mode'))

	@classmethod
	def do_cmd(cls): return 'silence'

	def do_to_hit_bonus(self): return 18

class TimestopAmmunition(Ammunition):
	LIST_ORDER = 2
	MAX_CHARGES = 3
	turns = 3

	def do_recharge_cost(self): return 80
	@classmethod
	def do_name(cls, instance, target, mode):
		return (
			"ост. времени" if mode == 'battle' else
			"врем." if mode == 'respite' else
			Noun.parse(("{патроны}" if mode == 'plural' else "{патрон}") + " остановки времени") if mode in ('noun', 'plural') else impossible(mode, 'mode'))

	@classmethod
	def do_cmd(cls): return 'timestop'

	def do_to_hit_bonus(self): return 30

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
		name = multipad.escape(target.name.cap_first()) + ": " + cls.AMMUNITION_CLASS.shop_name(target)
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
	def do_gold_cost(cls, target): return 100 + 50 * cls.count(target)

	@classmethod
	def genitive_ammunition_module_name(cls): return "зажигательных патронов"

class SilenceAmmunitionUpgrade(AmmunitionUpgrade):
	AMMUNITION_CLASS = SilenceAmmunition

	@classmethod
	def do_ap_cost(cls, target): return 2

	@classmethod
	def do_gold_cost(cls, target): return 160

	@classmethod
	def genitive_ammunition_module_name(cls): return "патронов тишины"

class TimestopAmmunitionUpgrade(AmmunitionUpgrade):
	AMMUNITION_CLASS = TimestopAmmunition
	@classmethod
	def do_ap_cost(cls, target): return 2

	@classmethod
	def do_gold_cost(cls, target): return 200

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
	LIST_ORDER = 1
	def name(self): return self.do_name()
	def do_name(self): raise NotImplementedError("do_name")
	def detail(self, game): return self.do_detail(game)
	def do_detail(self, game): raise NotImplementedError("do_detail")

	def do_ouch(self, arena, elems, etc): pass
	def do_tick(self, arena): pass
	def do_die(self, arena, etc): pass

	def should_display(self): return self.do_should_display()
	def do_should_display(self): return True

class RageOnLowHP(Special):
	def __init__(self, *, red_zone=0.5):
		super().__init__()
		self.proceed = False
		self.red_zone = red_zone

	def do_name(self): return "Ярость"
	def do_detail(self, game):
		return "{}, {} до {} HP, приходит в ярость и начинает наносить и получать повышенный урон.".format(
			self.fighter.name.cap_first(), self.fighter.gender.ize("ранен{ый/ая}"), self.hp_threshold())

	def do_ouch(self, arena, elems, etc):
		if not self.proceed and self.fighter.hp <= self.hp_threshold():
			self.rage().apply(self.fighter, arena=arena)
			self.proceed = True

	def do_should_display(self): return not self.proceed

	def rage(self):
		return RageHex(0.32 * (max(10, self.fighter.str) * self.fighter.xl)**0.5)

	def hp_threshold(self):
		return ceil(self.fighter.mhp * self.red_zone)

class Thievery(Special):
	def do_name(self): return "Карманник"
	def do_detail(self, game):
		max_amount = self.max_amount(game.player, game)
		return "{} {}.\nУклонение: {:.0%}.".format(
			self.fighter.name.cap_first(),
			"может украсть до ${} золота за раз".format(max_amount) if max_amount < game.gold else "умеет красть золото",
			1-self.chance(game.player, None))

	def chance(self, victim, arena): return Arena.hit_chance(arena, *self.save_throw(victim))
	def save_throw(self, victim): return self.fighter.dex, victim.dex, Arena.Cumulative(self.fighter, victim, 'steal')
	def max_amount(self, victim, game):
		return max(10, round((3 * self.fighter.dex + 0.2 * max(0, game.gold)) * (self.fighter.dex / max(1, self.fighter.dex + victim.dex))))
	def roll(self, victim, game): return max(0, min(game.gold, randrange(self.max_amount(victim, game))))

	def act_steal_gold(self, target_b, arena):
		amount = self.roll(target_b.fighter, target_b.game)
		self.fighter.note("«Ну-ка, попрыгай!»")
		dodged, chance, roll = arena.dodge(*self.save_throw(target_b.fighter))
		if dodged:
			how = UnarmedAttack.Beam.how_dodged(chance, roll)
			def get_note(sink):
				return sink.youify("{вы/F}" + how + " защищает{е/} свой кошелёк от", target_b.fighter) + sink.youify(" {вас/F:G}", self.fighter) + "."
			self.fighter.note(get_note)
		elif amount:
			fully = amount == target_b.game.gold
			def get_note(sink):
				return (sink.youify("{вы/F} отбирает{е/}", self.fighter) + sink.youify(" у {вас/F:G}", target_b.fighter) +
					(" всё оставшееся золото (" if fully else " ") + "${}".format(amount) + (")" if fully else "") + ".")
			self.fighter.note(get_note)
			target_b.game.take_gold(amount)
		else:
			self.fighter.note(lambda sink: sink.youify("{вам/F:D} не удаётся отобрать золото у", self.fighter) + sink.youify(" {вас/F:G}", target_b.fighter) + ".")

class Grasp(Special):
	def save_throw(self, target, master_imagination=None, target_imagination=None):
		return (5 + self.fighter.calculate_dex(master_imagination), 0.5 * target.calculate_dex(target_imagination))

	def do_name(self): return "удушение"
	def do_detail(self, game):
		return "{} может крепко обвить противника, ограничив возможность вести рукопашный бой и нанося урон каждый ход.\nУклонение: {:.0%}.".format(
			self.fighter.name.cap_first(), 1 - Arena.hit_chance(None, *self.save_throw(game.player)))

	def act_grasp(self, target, arena):
		dodged, chance, roll = arena.dodge(*self.save_throw(target))
		if dodged:
			def get_note(sink):
				msg = sink.youify("{Вы/F} пытает{есь/ся} схватить", self.fighter)
				msg += sink.youify(" {вас/F:A}, но {вы/он/она/оно}", target)
				msg += UnarmedAttack.Beam.how_dodged(chance, roll, barely="в последний момент")
				msg += sink.youify(" уворачивает{есь/ся}", target)
				return msg + "."
			target.note(get_note)
		else:
			GraspHex(min(1, self.fighter.str / 10)).apply(self.fighter, target, arena)

class Impregnation(Special):
	def __init__(self, hex=None):
		super().__init__()
		self.hex = hex

	def do_name(self): return "паразиты"
	def do_detail(self, game):
		return "{} может отложить яйца внутрь{} противника.{}".format(
			self.fighter.name.cap_first(), " захваченного" if self.fighter.preset == 'tentacle' else "",
			"\nУклонение: {:.0%}".format(1 - Arena.hit_chance(None, *self.save_throw(game.player))) if game.player != self.fighter else "")
	def save_throw(self, target): return 5 + self.fighter.dex, 0.5 * target.dex, Arena.Cumulative(self.fighter, target, 'impregnate')

	def act_impregnate(self, target, arena):
		assert target.can_be_impregnated
		dodged, _chance, _roll = arena.dodge(*self.save_throw(target))
		def something(sink):
			return "личинок" if sink.you == self.fighter else "что-то"

		if dodged:
			def get_note(sink):
				msg = sink.youify("{Вы/F} пытает{есь/ся}", self.fighter)
				if self.fighter.is_mammal:
					msg += " поцеловать" + sink.youify(" {вас/F:A}, но {вы/он/она/оно} уворачивает{есь/ся}.", target)
				else:
					msg += " затолкнуть " + something(sink) + sink.youify(" внутрь {вас/F:G}, но {вы/он/она/оно} уворачивает{есь/ся}.", target)
				return msg
			arena.note(get_note)
		else:
			master_b = arena.as_battler(self.fighter)
			if master_b and master_b.game and master_b.game.performance and not master_b.game.performance.kiss:
				master_b.game.performance.kiss = target

			def get_note(sink):
				if self.fighter.is_mammal:
					msg = sink.youify("{Вы/F} целует{е/}", self.fighter) + sink.youify(" {вас/F:A}", target)
					msg += sink.youify(" и оставляет{е/}", self.fighter) + ("" if sink.you == self.fighter else " что-то") + sink.youify(" внутри {вас/него/неё}", target)
					msg += (" личинок" if sink.you == self.fighter else "")
				else:
					msg = sink.youify("{Вам/F:D} удаётся протолкнуть", self.fighter) + " " + something(sink)
					msg += sink.youify(" внутрь {вас/F:G}", target)
				msg += "."
				if target == sink.you: msg += " Ай, он{} шевел{}тся!".format(*("и", "я") if sink.you == self.fighter else ("о", "и"))
				return msg
			arena.note(get_note)

			ParasiteHex(1).apply(self.fighter, target, arena)

	@staticmethod
	def give_birth(mother, arena):
		mother_b = arena.as_battler(mother)
		space = []
		for squad_id, squad in arena.squads.items():
			if not arena.squads_are_enemies(squad_id, mother_b.squad_id): continue
			if squad.max_members is not None and len(squad.members) + 1 > squad.max_members: continue
			space.append(squad_id)

		if space:
			squad_id = choose(space)
			larva = Fighter()
			larva.name, larva.gender, larva.preset = Noun.parse("{личинка:af}") + " " + mother.name.genitive, Gender.FEMALE, 'larva'
			larva.summoned = True
			larva.dispellable = False
			with larva.save_relative_vitals():
				larva.base_mhp = 5
				larva.base_str = max(5, rand_round(uniform(mother.base_str / 4, mother.base_str / 3)))
				larva.base_dex = max(5, rand_round(uniform(mother.base_dex / 4, mother.base_dex / 3)))
			larva.set_unarmed(ParalyzingStinger())
			arena.add(larva, squad_id, UniversalAI(), shortcut_hint="Larva", force_delay=mother_b.initiative + uniform(0.1, 0.9) * arena.delay_base(larva))

		def get_note(sink):
			msg = sink.youify("Личинка вырывается из{ вашего/} тела{/ F:G}", mother)
			if space:
				you_b = arena.as_battler(sink.you, maybe=True)
				if you_b: msg += " и встаёт " + ("против вас" if arena.squads_are_enemies(squad_id, you_b.squad_id) else "с вашей стороны")
			else:
				msg += " и уползает восвояси"
			return msg + "."
		arena.note(get_note)

		Bleeding(bell(0.4, 0.7, 1.2)).apply(mother, arena=arena)

class Marauding(Special):
	def do_name(self): return "мародёр"
	def do_detail(self, game):
		return "{} может отнять оружие противника.\nУклонение: {:.0%}.".format(
			self.fighter.name.cap_first(), 1 - Arena.hit_chance(None, *self.save_throw(game.player)))
	def save_throw(self, victim): return self.fighter.dex, victim.dex, Arena.Cumulative(self.fighter, victim, 'steal_wpn')

	def act_maraud(self, target, arena):
		assert target.weapon and 'weapon_stolen_from' not in self.fighter.props
		dodged, chance, roll = arena.dodge(*self.save_throw(target))
		if dodged:
			def get_note(sink):
				msg = sink.youify("{Вы/F}", target) + UnarmedAttack.Beam.how_dodged(chance, roll, barely="в последний момент") + sink.youify(" отдёргивает{е/}", target)
				msg += target.weapon.gender.ize(" сво{й/ю/ё}") if target == sink.you else target.gender.ize(" {его/её}")
				msg += " " + target.weapon.name.accusative + sink.youify(" от {вас/F:G}", self.fighter)
				return msg + "."
			target.note(get_note)
		else:
			def get_note(sink):
				msg = sink.youify("{Вы/F} отбирает{е/}", self.fighter)
				msg += target.weapon.gender.ize(" ваш{/у/е}") if target == sink.you else target.gender.ize(" {его/её}")
				msg += " " + target.weapon.name.accusative
				return msg + "!"
			target.note(get_note)
			self.fighter.props['weapon_stolen_from'] = target
			weapon = target.weapon
			target.set_weapon(None)
			self.fighter.set_weapon(weapon)

class PsionicThievery(Special):
	def do_name(self): return "псионик"
	def do_detail(self, game):
		return "{} может заставить противника забыть заклинание.\nСопротивление: {:.0%}.".format(
			self.fighter.name.cap_first(), 1 - Arena.hit_chance(None, *self.save_throw(game.player)))
	def save_throw(self, victim): return self.fighter.int, victim.int, Arena.Cumulative(self.fighter, victim, 'steal_spl')

	def act_psi_steal(self, target, arena):
		assert any(isinstance(up, SpellUpgrade) for up in target.upgrades)
		dodged, chance, roll = arena.dodge(*self.save_throw(target))
		if dodged:
			def get_note(sink):
				msg = sink.youify("{Вы/F}", target) + UnarmedAttack.Beam.how_dodged(chance, roll) + sink.youify(" выдерживает{е/}", target)
				msg += sink.youify("{ вашу/} пси-атаку{/ F:G}", self.fighter)
				return msg + "."
			target.note(get_note)
		else:
			def get_note(sink):
				return sink.youify("{Вы/F} шарит{е/} в", self.fighter) + sink.youify("{ вашей/} памяти{/ F:G}...", target)
			target.note(get_note)
			up = choose(up for up in target.upgrades if isinstance(up, SpellUpgrade))
			up.revert(target)

class FireVulnerability(Special):
	def __init__(self, amount=0.2):
		super().__init__()
		self.amount = amount

	def do_name(self): return "Уязвимость к огню"
	def do_detail(self, game):
		return "{} получает на {:.0%} больший урон от огня.".format(self.fighter.name.cap_first(), self.amount)

class BallLightningTimeoutAndExplodeOnDeathOrTouch(Special):
	def do_ouch(self, arena, elems, etc):
		if elems and all(isinstance(elem, (Beam.Fire, Beam.Electricity)) for elem in elems): return
		self.fighter.die(arena, etc=etc)

	def do_tick(self, arena):
		remaining_life = self.fighter.props['remaining_life'] = self.fighter.props['remaining_life'] - 1
		if remaining_life <= 0: self.fighter.die(arena)

	def do_die(self, arena, etc):
		if 'dont_explode' not in etc:
			BallLightning.act_explode(self.fighter, arena)

	def do_name(self): return "Самоуничтожение"
	def do_detail(self, game):
		msg = "Осталось {}.".format(plural(self.fighter.props['remaining_life'], "{N} ход{/а/ов}"))
		msg += "\n" + BallLightning.beam(self.fighter.props['master'], game.player, None).human_stats()
		return msg

class UnarmedAttack(FighterAttribute):
	class Beam(Beam):
		def __init__(self, ua, target, arena, master_imagination=None, target_imagination=None):
			super().__init__(ua.fighter, target, arena, master_imagination, target_imagination)
			self.ua = check(ua, isinstance(ua, UnarmedAttack), "ua")

		def on_tohit(self): return 10 + self.master_dex()
		def on_cumulative(self): return 'unarmed'
		def on_account(self): return 'unarmed'

		@staticmethod
		def how_dodged(chance, roll, prefix=" ", barely="едва"):
			how = barely if roll * 0.8 < chance else "легко" if roll * 0.6 > chance else ""
			return (prefix if how else "") + how

		def dodge_msg(self, chance, roll, sink, *, your_gen="вашего", atk_gen="удара"):
			msg = sink.youify("{Вы/F}", self.target) + self.how_dodged(chance, roll) + sink.youify(" уклоняет{есь/ся}", self.target) + " от"
			if self.master == sink.you: msg += " " + your_gen
			if atk_gen: msg += " " + atk_gen
			return msg + sink.youify("{/ F:G}", self.master) + "."

	def attack(self, target, arena):
		self.beam(target, arena).launch()

	def beam(self, target, arena, master_imagination=None, target_imagination=None):
		return self.Beam(self, target, arena, master_imagination, target_imagination)

	def name(self): return self.do_name()
	def do_name(self): raise NotImplementedError("do_name")

	def detail(self, game): return self.do_detail(game)
	def do_detail(self, game): return self.beam(game.player, arena=None).human_stats(do_eff=False)

class BareHands(UnarmedAttack):
	class Beam(UnarmedAttack.Beam):
		def on_tohit(self): return 12 + 1.2 * self.master_dex()

		def on_dodged(self, chance, roll):
			self.arena.note(lambda sink: self.dodge_msg(chance, roll, sink, your_gen="вашего", atk_gen="удара"))

		def on_elements(self):
			return self.Physical(tuple(x * (1 + (self.master_str() - 10)/(5 if self.master_str() > 10 else 10)) for x in (0, 1.3, 2)))

		def on_hp_damage(self, hp, fatal):
			def get_note(sink):
				msg = sink.youify("{Вы/F}", self.master)
				if hp:
					msg += sink.youify(" наносит{е/} удар", self.master) + sink.youify(" по {вам/F:D}" if not fatal else "", self.target)
				else:
					msg += sink.youify(" касает{есь/ся} ", self.master) + sink.youify("{вас/F:G}", self.target)
				msg += self.note_bare_hands(sink) + Beam.damage_paren(hp)
				if fatal and self.target.flavored_death:
					verb = "умирает{е/}" if self.target.is_mammal else "рассыпает{есь/ся}" if self.target.is_bone else "погибает{е/}"
					msg += sink.youify(", и {вы/F} " + verb, self.target)
				return msg + "."
			self.arena.note(get_note)

		def note_bare_hands(self, sink):
			bh_noticed = sink.extra_prop('bh_noticed', lambda: {})
			if self.ua not in bh_noticed:
				bh_noticed[self.ua] = True
				return " голыми руками"
			else:
				return ""

	def do_name(self): return "руки"

class Teeth(UnarmedAttack):
	class Beam(UnarmedAttack.Beam):
		def on_dodged(self, chance, roll):
			self.arena.note(lambda sink: self.dodge_msg(chance, roll, sink, your_gen="вас", atk_gen=None))

		def on_elements(self):
			return self.Physical(tuple(x * (1 + (self.master_str() - 10)/(5 if self.master_str() > 10 else 10)) for x in (0, 1.2, 2)))

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
					msg += sink.youify("сам{и//а/о} по себе" if self.master == self.target else "по {вам/F:D}", self.target)
				msg += Beam.damage_paren(hp)
				if fatal: msg += sink.youify(" и умирает{е/}" if self.master == self.target else ", и {вы/F} умирает{е/}", self.target)
				return msg + "."
			self.arena.note(get_note)

	def do_name(self): return "зубы"

class Spines(UnarmedAttack):
	class Beam(UnarmedAttack.Beam):
		def on_dodged(self, chance, roll):
			self.arena.note(lambda sink: self.dodge_msg(chance, roll, sink, your_gen="ваших", atk_gen="шипов"))

		def on_tohit(self): return 18 + 1.2 * self.master_dex()
		def on_elements(self):
			return self.Physical(tuple(x * (1 + (self.master_str() - 10)/(5 if self.master_str() > 10 else 10)) for x in (0, 1, 3)))

		def on_hp_damage(self, hp, fatal):
			def get_note(sink):
				msg = sink.youify("{Вы/F}", self.master)
				if fatal:
					msg += sink.youify(" выворачивает{е/}", self.master) + sink.youify("{ ваши/} кишки{/ F:G} наружу", self.target)
				else:
					msg += sink.youify(" колет{е/}" if hp else " скользит{е/} по", self.master) + sink.youify((" {вас/F:A}" if hp else " {вам/F:D}") + " шипами", self.target)
				return msg + Beam.damage_paren(hp) + "."
			self.arena.note(get_note)

			if hp and not fatal and random() < hp / (hp + 1):
				Bleeding((0.5 + random()) * (hp / (hp + 3 * random())) * 0.5 * (self.master.xl + self.master_str()/5) ** 0.5).apply(self.master, self.target, self.arena)

	def do_name(self): return "шипы"
	def do_detail(self, game): return "Глубоко проникнув в тело, могут вызвать серьёзное кровотечение.\n" + super().do_detail(game)

class TeethAndClaws(UnarmedAttack):
	class Beam(UnarmedAttack.Beam):
		def __init__(self, ua, target, arena, master_imagination=None, target_imagination=None):
			super().__init__(ua, target, arena, master_imagination, target_imagination)
			self.flavor = 'teeth' if randrange(2) == 0 else 'claws'

		def on_dodged(self, chance, roll):
			if self.flavor == 'teeth':
				return Teeth.Beam.on_dodged(self, chance, roll)
			elif self.flavor == 'claws':
				self.arena.note(lambda sink: self.dodge_msg(chance, roll, sink, your_gen="ваших", atk_gen="когтей"))
			else: impossible(self.flavor, "flavor")

		def on_elements(self): return Teeth.Beam.on_elements(self)

		def on_hp_damage(self, hp, fatal):
			if self.flavor == 'teeth':
				return Teeth.Beam.on_hp_damage(self, hp, fatal)
			elif self.flavor == 'claws':
				def get_note(sink):
					msg = sink.youify("{Вы/F}" + (" вспарывает{е/}" if fatal else " царапает{е/}" if hp else " скользит{е/}"), self.master)
					msg += sink.youify("{ ваше/} брюхо{/ F:G}" if fatal else " {вас/F:A}" if hp else " по {вам/F:D}", self.target)
					msg += " когтями" + (", и" if fatal else "") + Beam.damage_paren(hp) + (sink.youify(" {вы/F} умирает{е/}", self.target) if fatal else "")
					return msg + "."
				self.arena.note(get_note)
			else: impossible(self.flavor, "flavor")

	def do_name(self): return "когти и зубы"

class SlimyTouch(UnarmedAttack):
	class Beam(UnarmedAttack.Beam):
		def on_dodged(self, chance, roll):
			self.arena.note(lambda sink: self.dodge_msg(chance, roll, sink, your_gen="вашего", atk_gen="броска"))

		def on_elements(self):
			base = 1 + (self.master_str() - 10)/(7 if self.master_str() > 10 else 10)
			return self.Physical(tuple(x * base for x in (0, 1, 2)))

		def on_hp_damage(self, hp, fatal):
			slimify = not fatal and random() < 1 - (2 + hp) ** -1
			def get_note(sink):
				if fatal:
					msg = sink.youify("{Вы/F} ломает{е/}", self.master) + sink.youify("{ вам/} позвоночник{/ F:D}", self.target)
				else:
					msg = sink.youify("{Вы/F}" + (" обвивает{е/}" if slimify else " хлещет{е/}"), self.master) + sink.youify(" {вас/F:A}", self.target)
				return msg + Beam.damage_paren(hp) + "."
			self.arena.note(get_note)

			if slimify:
				SlimeHex(bell(0.5, 1, 1.5) * ((self.master.str ** 0.5 + 0.4 * hp) / 8)).apply(self.master, self.target, self.arena)

	def do_name(self): return "слизь"
	def do_detail(self, game):
		return "{}\nПрикосновение {} оставляет слизь, которая замедляет движения и снижает статы.".format(super().do_detail(game), self.fighter.name.genitive)

class ParalyzingStinger(UnarmedAttack):
	class Beam(UnarmedAttack.Beam):
		def on_dodged(self, chance, roll):
			self.arena.note(lambda sink: self.dodge_msg(chance, roll, sink, your_gen="вашего", atk_gen="жала"))

		def on_tohit(self): return 24 + 1.2 * self.master_dex()
		def on_elements(self):
			return self.Physical(tuple(x * (1 + (self.master_str() - 10)/(5 if self.master_str() > 10 else 10)) for x in (0, 1, 2)), pierce=1)

		def on_hp_damage(self, hp, fatal):
			paralyze = (hp and not fatal and self.target.flavored_death and 'paralysis_immunity' not in self.arena.as_battler(self.target).cooldowns and
				not self.target.find_hex(ParalysisHex) and
				random() < hp / (hp + 1.5))

			def get_note(sink):
				if hp:
					msg = sink.youify("{Вы/F}" + (" парализует{е/}" if paralyze else " жалит{е/}"), self.master) + sink.youify(" {вас/F:A}", self.target)
					if fatal and self.target.flavored_death: msg += ", и"
				else:
					msg = sink.youify("{ваше /}жало{/ F:G} проходит вскользь", self.master)
				msg += Beam.damage_paren(hp)
				if fatal and self.target.flavored_death: msg += sink.youify(" {вы/он/она/оно} умирает{е/} от анафилаксии", self.target)
				return msg + "."
			self.arena.note(get_note)

			if paralyze:
				ParalysisHex(uniform(0.5, 2) * hp ** 0.5).apply(self.target)

	def do_name(self): return "жало"

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
		msg = check(msg if isinstance(msg, str) or not callable(msg) else msg(self), lambda msg: not msg or isinstance(msg, str), "должна быть строка")
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
			else: p = pieces[min(len(pieces) - 1, 1 + (fighter.gender if fighter.gender != Gender.UNKNOWN and 1 + fighter.gender < len(pieces) else Gender.MALE))]
			i = 0
			while i < len(p):
				if p[i] == 'F':
					name = fighter.name(Case.from_letter(spec))
					p = p[:i] + name + p[i+1:]
					i += len(name)
				else:
					i += 1
			return p
		return "".join(literal + handle(bracketed, spec) for literal, bracketed, spec, _ in Formatter.parse(None, src))

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
		assert sink not in self.sinks, f"add_sink({sink}) вызвана дважды"
		self.sinks.append(sink)
		# Нет, в принципе это возможно (иначе зачем было вообще городить sinks[]), но сейчас, когда игрок ровно один — означает баг.
		assert len(self.sinks) == 1, f"sinks = {self.sinks}"

	def remove_sink(self, sink, maybe=False):
		with suppress(ValueError) if maybe else nullcontext():
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

	def receive_xp(self, amount, emulate=False, relative=False):
		return self.modify_xp(check(amount, amount >= 0, "amount"), emulate, relative)

	def drain_xp(self, amount, emulate=False, relative=False):
		return self.modify_xp(-check(amount, amount >= 0, "amount"), emulate, relative)

	def modify_xp(self, amount, emulate, relative):
		if relative:
			denorm_xl = self.xl + self.xp / self.xp_for_levelup() + amount
			xl = clamp(floor(denorm_xl), 1, self.LEVEL_CAP)
			# С denorm_xl - xl ошибок в краевых случаях не бывает, ВРОДЕ КАК. denorm_xl % 1 изредка выдавала nx=100%: типа «уровень 2 (след. 100%)».
			xp = (denorm_xl - xl) * self.xp_for_levelup(xl) if 1 <= denorm_xl < self.LEVEL_CAP else 0
		else:
			xl, xp = self.xl, self.xp + amount
			if amount > 0:
				while xl < self.LEVEL_CAP and xp >= self.xp_for_levelup(xl):
					xp -= self.xp_for_levelup(xl)
					xl += 1
				if xl >= self.LEVEL_CAP: xp = 0
			elif amount < 0:
				while xl > 1 and xp < 0:
					xp += self.xp_for_levelup(xl - 1)
					xl -= 1
				if xp < 0: xp = 0

		if emulate:
			return xl, xp

		if self.xl != xl:
			with self.save_relative_vitals(): self.xl = xl
			if amount < 0:
				while self.ap_used > self.ap_limit and self.upgrades: self.upgrades[-1].revert(self)
		self.xp = xp

	LEVEL_CAP = 1
	def xp_for_levelup(self, xl=None):
		if xl is None: xl = self.xl
		return self.do_xp_for_levelup(xl)

	def do_xp_for_levelup(self, xl):
		return 10 * xl

	def enough_ap_for(self, upgrade_or_whatever):
		ap_cost = (
			upgrade_or_whatever if isinstance(upgrade_or_whatever, int) else
			upgrade_or_whatever.ap_cost(self))

		return self.ap_used + ap_cost <= self.ap_limit

	def next_percentage(self, xl=None, xp=None):
		if xl is None: xl = self.xl
		if xp is None: xp = self.xp
		return floor(xp / self.xp_for_levelup(xl) * 100) if xl < self.LEVEL_CAP else None

	class Snapshot:
		def __init__(self, xl, xp, xp_percent, ap_used=None, ap_limit=None):
			self.xl, self.xp, self.xp_percent, self.ap_used, self.ap_limit = xl, xp, xp_percent, ap_used, ap_limit

	def snapshot(self):
		return self.Snapshot(self.xl, self.xp, self.next_percentage(), self.ap_used, self.ap_limit)

	# под for_multipad подразумевается for_shop
	def living_desc(self, for_multipad=False, short=False, prev=None, name_ljust=None):
		name = self.name.cap_first()
		show_ap = for_multipad or ((self.ap_used != prev.ap_used or self.ap_limit != prev.ap_limit) if prev else (self.xp > 0 or self.xl > 1 or self.ap_used > 0))
		return "{name}: {name_ljust}{xl_mp}{xl}{aps}".format(
			name_ljust = " " * (name_ljust - len(name)) if name_ljust else "",
			xl = self.xl_desc(short=short or for_multipad, show_nx=not for_multipad, prev=prev),
			name = multipad.escape(name) if for_multipad else name,
			xl_mp = "[lv]" if for_multipad else "",
			aps = ", {ap_mp}умения: {ap}".format(
				ap = " -> ".join("{}/{}".format(used, limit) for used, limit in filter(None, (
					prev and (prev.ap_used != self.ap_used or prev.ap_limit != self.ap_limit) and (prev.ap_used, prev.ap_limit),
					(self.ap_used, self.ap_limit)))),
				ap_mp = "[ap]" if for_multipad else "") if show_ap else "")

	# Может быть self = None, в этом случае xp полагается результатом next_percentage.
	def xl_desc(self, xl=None, xp=None, short=False, show_nx=True, prev=None):
		if xl is None: xl = self.xl
		nx_percent = self.next_percentage(xl, xp) if self else xp

		return " -> ".join(
				"{}{}{nx}".format("lv." if short else "уровень ", xl,
					nx = " ({}{})".format(
						"" if short else "след. ",
						" -> ".join("{}%".format(nx_percent) for nx_percent in filter(lambda percent: percent is not None, (prev_percent, nx_percent))))
						if show_nx and nx_percent is not None else "")
				for xl, nx_percent, prev_percent in filter(None, (
					prev and prev.xl != xl and (prev.xl, prev.xp_percent, None),
					(xl, nx_percent, prev.xp_percent if prev and prev.xl == xl and prev.xp_percent != nx_percent else None))))

	class RelativeVitals(AbstractContextManager):
		def __init__(self, char): self.char = char
		def __exit__(self, *poxui): pass

	def save_relative_vitals(self): return self.RelativeVitals(self)

	def __getstate__(self):
		return {k:
			v.value if k == 'gender' else
			('g' + str(v) if v == Noun.guess(v, gender=self.gender, animate=isinstance(self, Fighter)) else 'p' + v.src()) if k == 'name' else
			v
			for k, v in self.__dict__.items()
				if not (k in ('upgrades', 'xp', 'ap_used') and not v)}

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

# Используется, когда нужно узнать, каким был бы параметр при наличии, или отсутствии, такого-то апгрейда или хекса.
# Например,
# imagination.add(StrUpgrade())
# fighter.calculate_mhp(imagination)
# — рассчитает максимальный HP с одним дополнительным апгрейдом силы.
#
# frailness = fighter.find_hex(FrailnessHex)
# imagination.remove(frailness)
# fighter.calculate_ac(imagination)
# — рассчитает AC без действующей хрупкости.
class Imagination:
	def __init__(self):
		self.added, self.removed = [], []

	def validate(self, part):
		check(part, isinstance(part, (Hex, Upgrade)), "imagination part")
		return part

	def add(self, part):
		self.added.append(self.validate(part))
		return self

	def remove(self, part):
		self.removed.append(self.validate(part))
		return self

	@classmethod
	def changes(cls, instance):
		if instance:
			for item in instance.added: yield item, True
			for item in instance.removed: yield item, False

	@classmethod
	def generic_query(cls, instance, list, item_cls):
		if instance:
			yield from filter(lambda item: item not in instance.removed, list)
			yield from filter(lambda item: isinstance(item, item_cls), instance.added)
		else:
			yield from list

	@classmethod
	def upgrades(cls, instance, pc): yield from cls.generic_query(instance, pc.upgrades, Upgrade)

	@classmethod
	def hexes(cls, instance, pc): yield from cls.generic_query(instance, pc.hexes, Hex)

def _to_props(attr, default=None):
	def get(self): return self.props.get(attr, default)
	def set(self, value): self.props[attr] = value
	return property(get, set)

class Fighter(Living, MessageBroadcaster):
	hp    = property(lambda self: self.cur_hp)
	mhp   = property(lambda self: self.calculate_mhp())
	dead  = property(lambda self: not self.alive)
	mp    = property(lambda self: self.cur_mp)
	mmp   = property(lambda self: self.calculate_mmp())
	str   = property(lambda self: self.calculate_str())
	int   = property(lambda self: self.calculate_int())
	dex   = property(lambda self: self.calculate_dex())
	spd   = property(lambda self: self.calculate_spd())
	ac    = property(lambda self: self.calculate_ac())
	ev    = property(lambda self: self.calculate_ev())
	LEVEL_CAP = 7

	def calculate_mhp(self, imagination=None):
		return max(1, round((self.base_mhp + 5 * (self.xl - 1)**0.77) * (1 + (self.calculate_str(imagination, 'hp') - 10) / 20)))

	def calculate_mmp(self, imagination=None):
		return max(0, round(self.base_mmp + 10 * signed_pow((self.calculate_int(imagination, 'mp') - 10) / 10, 1.0)))

	def calculate_str(self, imagination=None, mode='dynamic'):
		check(mode, mode in ('dynamic', 'hp'), "mode")
		value = self.base_str
		for item, added in Imagination.changes(imagination):
			if isinstance(item, StrUpgrade):
				value += item.AMOUNT if added else -item.AMOUNT
		for hex in Imagination.hexes(imagination, self):
			if mode != 'hp' and isinstance(hex, SlimeHex): value -= hex.str_debuff(value)
		return max(1, value)

	def calculate_int(self, imagination=None, mode='dynamic'):
		check(mode, mode in ('dynamic', 'mp'), "mode")
		value = self.base_int
		for item, added in Imagination.changes(imagination):
			if isinstance(item, IntUpgrade):
				value += item.AMOUNT if added else -item.AMOUNT
		for hex in Imagination.hexes(imagination, self):
			if mode != 'mp' and isinstance(hex, SlimeHex): value -= hex.int_debuff(value)
		return max(1, value)

	def calculate_dex(self, imagination=None):
		value = self.base_dex
		for item, added in Imagination.changes(imagination):
			if isinstance(item, DexUpgrade):
				value += item.AMOUNT if added else -item.AMOUNT
		for hex in Imagination.hexes(imagination, self):
			if isinstance(hex, SlimeHex): value -= hex.dex_debuff(value)
			elif isinstance(hex, Bleeding): value -= hex.dex_debuff
		return max(1, value)

	def calculate_spd(self, imagination=None):
		value = self.base_spd
		for item, added in Imagination.changes(imagination):
			if isinstance(item, SpeedUpgrade):
				value += item.AMOUNT if added else -item.AMOUNT
		for hex in Imagination.hexes(imagination, self):
			if isinstance(hex, SlimeHex): value -= hex.speed_debuff(value)
		return max(1, value)

	def calculate_ac(self, imagination=None):
		ac = self.base_ac
		frailness = barrier = None
		for hex in Imagination.hexes(imagination, self):
			if isinstance(hex, FrailnessHex): frailness = hex
			elif isinstance(hex, BarrierHex): barrier = hex
		if frailness: ac -= frailness.ac_malus(ac)
		if barrier: ac += barrier.ac_bonus()
		return ac

	def calculate_ev(self, imagination=None):
		ev = max(0, self.base_ev + (self.calculate_dex(imagination) - 10)//2)
		fetter = grasp = None
		for hex in Imagination.hexes(imagination, self):
			if isinstance(hex, FetterHex): fetter = hex
			elif isinstance(hex, GraspHex): grasp = hex
		if fetter: ev -= fetter.ev_malus(ev)
		if grasp: ev -= grasp.ev_malus(ev)
		return ev

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
		self.alive = True

		self.hexes = []
		self.caused_hexes = set()
		self.hexes_lock = None
		self.unarmed = None
		self.weapon = None
		self.spells = []
		self.specials = []

		self.cur_hp = self.mhp
		self.cur_mp = self.mmp
		self.props = {}

	def count_an_attack(self, weight, master, arena, account, count=1):
		assert arena
		def add_to(con, k=1):
			con.attacks += count * k
			con.weight += weight * k

		def add_from(master, k=1):
			add_to(arena.as_battler(self).received_attacks[master], k)

		if master:
			if account in ('master', 'unarmed', 'magical'): add_from(master)
			elif account == 'melee': add_from(master, 0.6); add_from(master.weapon, 0.4)
			elif account == 'ranged': add_from(master, 0.4); add_from(master.weapon, 0.6)
			else: impossible(account, "account")

			if master.alive:
				master_b = arena.as_battler(master, maybe=True)
				perf = master_b and master_b.game and master_b.game.performance
				if perf:
					if account == 'master': pass
					elif account in ('unarmed', 'melee', 'ranged', 'magical'): add_to(getattr(perf, account))
					else: impossible(account, "account")
		else:
			add_from(master) # засчитается «мистеру None»

	def ouch(self, hp_dam, master, arena, *, hook=lambda fatal: None, account='master', count_as_attack=True, elems=None, etc={}):
		check(hp_dam >= 0, "hp_dam?!")
		assert account in ('master', 'unarmed', 'melee', 'ranged', 'magical')
		if self.dead: return

		if arena:
			self.count_an_attack(hp_dam, master, arena, account, 1 if count_as_attack else 0)

		self.cur_hp -= hp_dam
		if self.cur_hp <= 0:
			self.die(arena, hook=lambda: hook(True), etc=etc)
		else:
			hook(False)
			for sp in self.specials:
				sp.do_ouch(arena, elems, etc)

	def die(self, arena, *, hook=lambda: None, etc={}):
		check(not self.dead, "not dead")
		self.alive = False
		if hook: hook()

		with self.lock_hexes() as hexes:
			for hex in hexes:
				if hex.ran_out: continue
				hex.cancel(Hex.TARGET_DIED)

		with self.lock_caused_hexes() as caused_hexes:
			for hex in caused_hexes:
				if hex.ran_out: continue
				if isinstance(hex, (DeathWordHex, GraspHex)):
					hex.cancel()

		for sp in self.specials:
			sp.do_die(arena, etc)

	def end_turn(self, arena):
		with self.lock_hexes() as hexes:
			for hex in hexes:
				if self.dead: break
				check(hex.victim == self, "hex.victim != self", not hex.ran_out, "ran_out")
				if isinstance(hex, DeathWordHex) and self.paralyzed(): continue
				hex.tick(arena)

		for sp in self.specials:
			if self.dead: break
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
		Query = namedtuple('Query', 'cntr, op, item')
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
			def __iter__(self): yield from filter(lambda hex: (self.cntr, 'rem', hex) not in self.lock.queries, self.cntr)
			def add(self, hex): self.lock.queries.append(self.lock.Query(self.cntr, 'add', hex))
			def remove(self, hex): self.lock.queries.append(self.lock.Query(self.cntr, 'rem', hex))

	def lock_hexes(self): return self.HexesLock.Context(self, self.hexes)
	def lock_caused_hexes(self): return self.HexesLock.Context(self, self.caused_hexes)

	def add_special(self, special):
		assert not any(isinstance(sp, type(special)) or isinstance(special, type(sp)) for sp in self.specials), f"duplicate special {special}"
		special.set_fighter(self)
		insort_right(self.specials, special, key=lambda special: special.LIST_ORDER)

	def remove_special(self, special):
		self.specials.remove(special)
		special.reset_fighter(self)

	def find_hex(self, hex_type):
		assert issubclass(hex_type, Hex), hex_type
		return next((hex for hex in self.hexes if isinstance(hex, hex_type)), None)

	def set_unarmed(self, unarmed):
		if self.unarmed: self.unarmed.reset_fighter(self)
		self.unarmed = unarmed
		if unarmed: unarmed.set_fighter(self)

	def has_magic(self):
		return self.spells and self.mmp

	def enough_mp(self, mp):
		return self.mp >= mp

	def consume_mp(self, mp):
		assert self.enough_mp(mp)
		self.cur_mp -= mp

	def castable_dispell(self):
		dispell = self.can_cast() and next((sp for sp in self.spells if isinstance(sp, Dispell)), None)
		return dispell and self.can_cast(dispell) and dispell

	def generic_bar(self, name, cur, max, flip):
		return left_to_right(name + ("" if flip else ":"), Con.vital_bar(cur, max, flip=flip), f"{cur}/{max}", flip=flip)
	def hp_bar(self, flip=False): return self.generic_bar("HP", self.hp, self.mhp, flip)
	def mp_bar(self, flip=False): return self.generic_bar("MP", self.mp, self.mmp, flip)

	def silenced(self): return self.find_hex(SilenceHex)

	def can_cast(self, spell=None):
		return not self.silenced() and (not spell or self.enough_mp(spell.mp_cost()))

	def act_skip_turn(self):
		def get_note(sink):
			return sink.youify("{Вы/F} пропускает{е/} ход.", self)
		self.note(get_note)

	def act_attack_unarmed(self, target, arena):
		self.unarmed.attack(target, arena)

	def act_weapon_melee(self, target, arena):
		self.weapon.kick(target, arena)

	def act_weapon_shoot(self, target, arena, ammo):
		self.weapon.shoot(target, arena, ammo)

	def act_weapon_rapid(self, targets, arena, ammo):
		self.weapon.rapid(targets, arena, ammo)

	def act_cast_spell(self, spell, target, arena):
		cost = spell.mp_cost()
		self.consume_mp(cost)
		spell.cast(self, target, arena)

	def paralyze(self):
		self.props['paralyzed'] = self.props.get('paralyzed', 0) + 1

	def paralyzed(self):
		return 'paralyzed' in self.props

	def unparalyze(self):
		self.props['paralyzed'] -= 1
		check(self.props['paralyzed'], lambda paralyzed: paralyzed >= 0, "paralyzed")
		if self.props['paralyzed'] == 0: del self.props['paralyzed']

	# сохранить соотношения HP/MP к максимумам, если какое-то действие потенциально изменит их лимит.
	class RelativeVitals(Living.RelativeVitals):
		def __init__(self, char):
			super().__init__(char)
			self.hp, self.mhp = char.hp, char.mhp
			self.mp, self.mmp = char.mp, char.mmp

		def __exit__(self, et, e, tb):
			if self.char.hp != self.hp or self.char.mhp != self.mhp:
				self.char.cur_hp = clamp(round(self.char.mhp * (self.hp / self.mhp)), min(1, self.char.mhp), self.char.mhp)
			if self.char.mp != self.mp or self.char.mmp != self.mmp:
				self.char.cur_mp = clamp(round(self.char.mmp * (self.mp / self.mmp if self.mmp > 0 else 1)), min(1, self.char.mmp), self.char.mmp)
			super().__exit__(et, e, tb)

	preset   = _to_props('preset')
	summoned = _to_props('summoned', False)

	@property
	def dispellable(self):
		try:
			return self.props['dispellable']
		except KeyError:
			return self.summoned

	@dispellable.setter
	def dispellable(self, value):
		self.props['dispellable'] = value

	transient = property(lambda self: self.summoned)
	is_mammal = property(lambda self: self.preset in ('player', 'rat', 'bear', 'thief', 'executioner', 'necromancer', 'magius', 'larva'))
	is_plant  = property(lambda self: self.preset in ('flower',))
	is_bone   = property(lambda self: self.preset in ('death',))
	is_ghost  = property(lambda self: self.preset in ('ghost'))
	flavored_death = property(lambda self: self.preset not in ('lightning',))
	can_be_impregnated = property(lambda self: not self.transient and not next((sp for sp in self.specials if isinstance(sp, Impregnation)), None))

	def __getstate__(self):
		assert not self.hexes_lock
		return {k: v for k, v in super().__getstate__().items() if k not in (
			'caused_hexes', # резолвятся здесь
			'alive',        # либо сохраняемый боец жив, либо эта информация не интересна
			'sinks',        # из MessageBroadcaster; подписчики по своей природе — динамическая штука, их не то что «можно не», а категорически нельзя сохранять
			'hexes_lock',   # динамическая штука
			) and not (
				k in ('hexes', 'spells', 'specials', 'unarmed', 'weapon', 'props') and not v
				or k == 'cur_hp' and v == self.mhp or k == 'cur_mp' and v == self.mmp)}

	def __setstate__(self, state):
		super().__setstate__(state)
		if self.weapon: self.weapon.owner = self # отбрасывается Weapon
		for hex in self.hexes:
			hex.victim = self                # отбрасывается Hex
			hex.master.caused_hexes.add(hex) # отбрасываются здесь
		for special in self.specials:
			special.fighter = self  # отбрасывается FighterAttribute
		if self.unarmed: self.unarmed.fighter = self # отбрасывается FighterAttribute
		if 'cur_hp' not in state: self.cur_hp = self.mhp
		if 'cur_mp' not in state: self.cur_mp = self.mmp
del _to_props

class Weapon(Living):
	ap_limit = property(lambda self: 1 + (self.xl - 1))
	LEVEL_CAP = 6

	def __init__(self):
		Living.__init__(self)
		self.owner, self.ammos = None, []

	def __getstate__(self):
		return {k: v for k, v in super().__getstate__().items() if k not in (
			'owner', # резолвится Fighter
			) and not (k in ('ammos') and not v)}

	def __setstate__(self, state):
		super().__setstate__(state)
		for ammo in self.ammos:
			ammo.weapon = self # отбрасывается Ammunition
			for second_ammo in ammo.secondary_installations: second_ammo.weapon = self

	class Beam(Beam):
		def __init__(self, weapon, target, arena, master_imagination=None, target_imagination=None):
			super().__init__(weapon.owner, target, arena, master_imagination, target_imagination)
			self.weapon = weapon

		def on_dodged(self, chance, roll):
			def get_note(sink):
				return sink.youify("{Вы/F} промахивает{есь/ся}", self.master) + " мимо " + sink.youify("{вас/F:G}", self.target) + "."
			self.arena.note(get_note)

	class MeleeBeam(Beam):
		def on_tohit(self): return 16 + self.master_dex()
		def on_account(self): return 'melee'
	ShotBeam = None

	class ShotBeamBase(Beam):
		def __init__(self, weapon, target, arena, ammo, mode='single', master_imagination=None, target_imagination=None):
			super().__init__(weapon, target, arena, master_imagination, target_imagination)
			self.ammo, self.mode = ammo, mode

		def on_tohit(self):
			return (
				5 + 0.65 * self.master_dex() + (self.ammo.do_to_hit_bonus() if self.ammo else 0) if self.mode == 'single' else

				# На данный момент точность очереди равна точности одиночного выстрела. Штраф — только отсутствие cumulative.
				5 + 0.65 * self.master_dex() if self.mode == 'rapid' else impossible(self.mode, 'mode'))
		def on_account(self): return 'ranged'
		def can(self, mode): return self.mode == 'single'

	def melee_beam(self, target, arena, master_imagination=None, target_imagination=None):
		return self.MeleeBeam(self, target, arena, master_imagination, target_imagination)

	def shot_beam(self, target, arena, ammo, mode='single', master_imagination=None, target_imagination=None):
		return check(self.ShotBeam, "cannot shoot")(self, target, arena, ammo, mode, master_imagination, target_imagination)

	def kick(self, target, arena):
		self.melee_beam(target, arena).launch()

	def shoot(self, target, arena, ammo):
		if ammo: ammo.draw_charge()
		if isinstance(ammo, TimestopAmmunition): self.owner.note("*Зайн!*")
		self.shot_beam(target, arena, ammo).launch()

	def rapid(self, targets, arena, ammo):
		self.owner.note(lambda sink: sink.youify("{Вы/F} стреляет{е/} очередью.", self.owner))
		n = 0
		def ratata():
			nonlocal n
			self.owner.note("Тра!" if n == 0 else "Та!")
			n += 1

		for target in targets:
			ratata()
			self.shot_beam(target, arena, ammo, mode='rapid').launch()

		while n < 3:
			ratata()

	def detail(self, game): return self.do_detail(game)
	def do_detail(self, game): return self.melee_beam(game.player, None).human_stats(do_eff=False)

class MachineGun(Weapon):
	class MeleeBeam(Weapon.MeleeBeam):
		def on_tohit(self):
			return 8 + self.master_dex()

		def on_elements(self):
			return self.Physical(tuple(x * (1 + (self.master_str() - 10)/(7 if self.master_str() > 10 else 10)) for x in (0, 1.6, 3)), pierce=0.2)

		def on_hp_damage(self, hp, fatal):
			def get_note(sink):
				msg = sink.youify("{Вы/F} ударяет{е/} ", self.master) + sink.youify("{вас/F:A}", self.target) + " прикладом"
				if fatal and self.target.flavored_death:
					if self.target.is_mammal:
						roll = randrange(2)
						if roll == 0:
							msg += " и" + Beam.damage_paren(hp) + sink.youify(" проламывает{е/} ", self.master) + sink.youify("{вам/ему/ей}", self.target) + " череп"
						else:
							msg += " и" + Beam.damage_paren(hp) + sink.youify(" ломает{е/} ", self.master) + sink.youify("{вам/ему/ей}", self.target) + " позвоночник"
					elif self.target.is_plant:
						msg += " и" + Beam.damage_paren(hp) + sink.youify(" сбивает{е/} ", self.master) + sink.youify("{вас/его/её}", self.target) + " с корней"
					elif self.target.is_bone:
						msg += ", и" + Beam.damage_paren(hp) + sink.youify(" {вы/он/она/оно} рассыпает{есь/ся}", self.target)
					else:
						msg += ", и" + Beam.damage_paren(hp) + sink.youify(" {вы/он/она/оно} погибает{е/}", self.target)
				elif hp:
					msg += Beam.damage_paren(hp)
				else:
					msg += ", но" + Beam.damage_paren(hp) + " не" + sink.youify("наносит{е/}", self.master) + " вреда"
				return msg + "."
			self.arena.note(get_note)

	class ShotBeam(Weapon.ShotBeamBase):
		def __init__(self, weapon, target, arena, ammo, mode='single', master_imagination=None, target_imagination=None):
			super().__init__(weapon, target, arena, ammo, mode, master_imagination, target_imagination)
			self.imagine_incendiary = 0

		def on_elements(self):
			elements = [self.Physical((0, 2.4, 7), pierce=1.0),]

			incendiary = self.imagine_incendiary
			if isinstance(self.ammo, IncendiaryAmmunition): incendiary += self.ammo.times()
			if incendiary > 0:elements.append(self.Fire((0, 1.5 * incendiary, 4.5 * incendiary), pierce=0.6))
			return elements

		def on_cumulative(self):
			return self.mode == 'single' and Arena.Cumulative(self.master, self.target, 'shot' + ('-' + self.ammo.cmd() if self.ammo else ''), 0.6)

		def on_dodged(self, chance, roll):
			if self.mode == 'rapid':
				def get_note(sink):
					return sink.youify("Пуля пролетает мимо {вас/F:G}", self.target) + "."
				self.arena.note(get_note)
			else:
				super().on_dodged(chance, roll)

		def on_hp_damage(self, hp, fatal):
			def get_note(sink):
				if self.mode == 'single': msg = sink.youify("{Вы/F} попадает{е/}", self.master)
				elif self.mode == 'rapid': msg = "Пуля попадает"
				else: impossible(self.mode, "mode")

				msg += " в" + sink.youify(" {вас/F:A}", self.target)
				master_b = self.arena.as_battler(self.master, maybe=True)
				if not (master_b and master_b.game) and self.mode == 'single':
					msg += " " + "пулей"

				if fatal and self.target.flavored_death:
					def heap_of(what, gender=Gender.UNKNOWN, plural=False, heap_adj=None):
						what_or_heap_adj = ""
						if isinstance(self.ammo, IncendiaryAmmunition):
							what_or_heap_adj = "дымящ{}ся".format("ую" if what is None else "их" if plural else gender.ize("е{го/й}"))

						return (
							(heap_adj + " " if heap_adj else "") +
							(what_or_heap_adj + " " if what_or_heap_adj and what is None else "") +
							"груду" +
							(" " + what_or_heap_adj if what_or_heap_adj and what is not None else "") +
							(" " + what if what else ""))

					msg += (" и" + Beam.damage_paren(hp) + sink.youify(" превращает" + ("{е/}" if self.mode == 'single' else ""), self.master) +
						sink.youify("{/ его/ её}" if self.mode == 'rapid' else " {вас/его/её}", self.target) +
						" в " + (
							heap_of("мяса", Gender.NEUTER) if self.target.is_mammal else
							heap_of("листьев", plural=True) if self.target.is_plant else
							heap_of("костей", plural=True) if self.target.is_bone else
							heap_of(None, heap_adj="бесформенную")) + ".")
				elif hp:
					msg += Beam.damage_paren(hp) + "."
				else:
					msg += ", но" + Beam.damage_paren(hp) + sink.youify(" не наносит" + ("{е/}" if self.mode == 'single' else "") + " вреда", self.master) + "."
				return msg
			self.arena.note(get_note)

			if not fatal:
				if isinstance(self.ammo, SilenceAmmunition):
					if self.target.silenced():
						self.arena.note("Тишина не срабатывает.")
					else:
						SilenceHex(bell(0.8, 1, 1.2)).apply(self.master, self.target, arena=self.arena)
				elif isinstance(self.ammo, TimestopAmmunition):
					self.arena.stop_time(self.ammo.turns)

class Dagger(Weapon):
	def __init__(self, coating=None):
		super().__init__()
		self.coating = check(coating, coating in (None, 'poison', 'poison2', 'runes'), "coating")
		self.name = Noun.parse("{{{}{}{}}}".format(
			"отравленный " if coating in ('poison', 'poison2') else "ритуальный " if coating == 'runes' else "",
			"клинок" if coating == 'runes' else "кинжал",
			" II" if coating == 'poison2' else ""))

	class MeleeBeam(Weapon.MeleeBeam):
		def on_elements(self):
			denom = 5 if self.weapon.coating not in ('poison', 'poison2', 'runes') and self.master_str() > 10 else 10
			return self.Physical(tuple(x * max(0.1, 1 + (self.master_str() - 10)/denom) for x in (0, 1.4, 3)), pierce=0.5)

		def on_hp_damage(self, hp, fatal):
			def get_note(sink):
				msg = sink.youify("{Вы/F}", self.master)
				if hp:
					if fatal:
						dw_roll = randrange(2)
						if dw_roll == 0: msg += sink.youify(" пронзает{е/}", self.master) + sink.youify("{ ваше/} сердце{/ F:G}", self.target)
						else: msg += sink.youify(" перерезает{е/}", self.master) + sink.youify("{ вашу/} глотку{/ F:G}", self.target)
					else:
						roll = randrange(2)
						if roll == 0: msg += sink.youify(" взмахивает{е/}", self.master)
						else: msg += sink.youify(" колет{е/}", self.master) + sink.youify(" {вас/F:A}", self.target)
				else:
					msg += sink.youify(" скользит{е/} по", self.master) + sink.youify(" {вам/F:D}", self.target)
				msg += (" клинком" if self.weapon.coating == 'runes' else " кинжалом") + Beam.damage_paren(hp)
				return msg + "."
			self.arena.note(get_note)

			if not fatal:
				if self.weapon.coating is None:
					pass
				elif self.weapon.coating in ('poison', 'poison2'):
					if hp and random() < hp / (hp + 1):
						poison = Poison(0.6 * hp ** 0.5)
						if self.weapon.coating == 'poison2':
							poison.kind = 'poison2'
							poison.hp_dam_per_turn = poison.mp_dam_per_turn = 2
						poison.apply(self.target, arena=self.arena)
				elif self.weapon.coating == 'runes':
					if self.master.mp < self.master.mmp and hp and random() < hp / (hp + 1):
						recover_mp = min(self.master.mmp - self.master.mp, rand_round(random() * (0.7 + 0.3 * random()) * hp))
						if recover_mp:
							self.master.note(lambda sink: sink.youify("{Вы/F} восстанавливает{е/}", self.master) + " {} MP".format(recover_mp) + ".")
							self.master.cur_mp += recover_mp
				else: impossible(self.weapon.coating, "coating")

	def do_detail(self, game):
		msg = super().do_detail(game)
		if self.coating in ('poison', 'poison2'):
			msg += "\nЯд отнимает HP и MP в течение нескольких ходов."
		elif self.coating == 'runes':
			msg += "\nВосполняет ману за счёт крови противника."
		return msg

class ExecutionerAxe(Weapon):
	def __init__(self):
		super().__init__()
		self.name = Noun.parse("{топор}")

	class MeleeBeam(Weapon.MeleeBeam):
		def on_elements(self):
			return self.Physical(tuple(x * max(0.1, 1 + (self.master_str() - 10)/5) for x in (0, 1.6, 3)))

		def on_hp_damage(self, hp, fatal):
			def get_note(sink):
				msg = sink.youify("{Вы/F}", self.master)
				if hp:
					roll = randrange(2)
					if roll == 0: msg += sink.youify(" взмахивает{е/}", self.master)
					else:
						if fatal: msg += sink.youify(" разрубает{е/}", self.master) + sink.youify("{ вас/F:G} пополам", self.target)
						else: msg += sink.youify(" рубит{е/}", self.master) + sink.youify(" {вас/F:A}", self.target)
					if not (roll == 1 and fatal): msg += " топором"
					if fatal and roll != 1: msg += " и"
					msg += Beam.damage_paren(hp)
					if fatal and roll != 1: msg += sink.youify(" разрубает{е/}", self.master) + sink.youify(" {вас/F:G} надвое", self.target)
				else:
					msg += sink.youify(" скользит{е/} по", self.master) + sink.youify(" {вам/F:D}", self.target) + " лезвием топора" + Beam.damage_paren(hp)
				return msg + "."
			self.arena.note(get_note)

class DeathScythe(Weapon):
	def __init__(self):
		super().__init__()
		self.name = Noun.parse("{коса} Смерти")

	class MeleeBeam(Weapon.MeleeBeam):
		def on_elements(self):
			return self.Physical(tuple(x * max(0.1, 1 + (self.master_str() - 10)/6) for x in (0, 1.3, 3)))

		def on_hp_damage(self, hp, fatal):
			def get_note(sink):
				msg = sink.youify("{Вы/F}", self.master)
				if hp:
					roll = randrange(2)
					if roll == 0: msg += sink.youify(" взмахивает{е/}", self.master)
					else:
						if fatal: msg += sink.youify(" прошивает{е/}", self.master) + sink.youify("{ вас/F:G}", self.target)
						else: msg += sink.youify(" ранит{е/}", self.master) + sink.youify(" {вас/F:A}", self.target)
					msg += " косой"
					if fatal and roll != 1: msg += " и"
					msg += Beam.damage_paren(hp)
					if fatal and roll == 1: msg += " насквозь"
					if fatal and roll != 1: msg += sink.youify(" разрубает{е/}", self.master) + sink.youify(" {вас/F:G} надвое", self.target)
				else:
					msg += sink.youify(" скользит{е/} по", self.master) + sink.youify(" {вам/F:D}", self.target) + " лезвием косы" + Beam.damage_paren(hp)
				return msg + "."
			self.arena.note(get_note)

			if hp:
				dw = self.target.find_hex(DeathWordHex)
				if dw and dw.turns > 1 and random() < 0.75 * hp / (hp + 3):
					nturns = dw.turns - 1
					if nturns >= 1:
						dw.turns = nturns
						self.arena.note(lambda sink: sink.you == self.target and "Вы слышите, как сыплется песок в часах.")

	def do_detail(self, game):
		return super().do_detail(game) + "\nПриближает исполнение Смертного приговора."

class Arena(MessageBroadcaster, MessageSink):
	BASELINE_SPD = 100

	class DamageContribution:
		def __init__(self):
			self.attacks, self.weight = 0, 0

		def __bool__(self):
			return bool(self.attacks or self.weight)

		def __str__(self):
			return "attacks = {}, weight = {:g}".format(self.attacks, self.weight)

	class Battler: # Gladiator слишком длинно
		def __init__(self, fighter, squad_id, ai, shortcut, game):
			self.fighter    = fighter
			self.squad_id   = squad_id
			self.ai         = ai
			self.initiative = 0        # время до хода этого участника; после хода увеличивается на значение, зависящее от SPD
			self.shortcut   = shortcut # сокращение, используемое в командах и на шкале инициативы
			self.game       = game

			# пока что багофича — кулдаун считается с текущим ходом, так что cooldown=2 реально даст передышку на 1 ход, а cooldown=1 не даст вообще.
			# Можно было бы сделать как с кулдаунами в RandomizedAI, т. е. не декрементировать только что выставленные.
			self.cooldowns  = defaultdict(lambda: 0)

			# атаки от имени этого бойца; { жертва ⇒ { ID атаки ⇒ to-hit } }
			self.outcoming_cumulatives = game and defaultdict(lambda: defaultdict(lambda: 0))

			# обезличенные атаки НА этого бойца; { ID атаки ⇒ to-hit }.
			self.incoming_cumulatives = not game and defaultdict(lambda: 0) or None

			# { Fighter ⇒ DamageContribution }, для раскидывания опыта
			self.received_attacks = defaultdict(lambda: Arena.DamageContribution())

		def cleanup_transient(self):
			if self.outcoming_cumulatives: self.outcoming_cumulatives.clear()
			if self.incoming_cumulatives: self.incoming_cumulatives.clear()
			with self.fighter.lock_hexes() as hexes:
				for hex in hexes:
					if not isinstance(hex, ParasiteHex): hex.cancel()

		def set_cooldown(self, id, value):
			self.cooldowns[id] = max(self.cooldowns[id], 1 + value)

		def process_cooldowns(self):
			expired = []
			for id, value in self.cooldowns.items():
				value -= 1
				if value > 0: self.cooldowns[id] = value
				else: expired.append(id)
			for id in expired:
				del self.cooldowns[id]

		def __getstate__(self):
			assert not self.game
			return {k:
				dict(v) if k == 'received_attacks' else
				v.__class__ if k == 'ai' else
				v
				for k, v in self.__dict__.items()
				if k not in ('outcoming_cumulatives', 'incoming_cumulatives', 'cooldowns')}

		def __setstate__(self, state):
			self.__init__(None, None, None, None, None)
			self.__dict__.update((k,
				v() if k == 'ai' else
				v)
				for k, v in state.items()
					if k not in ('received_attacks',))

			received_attacks = state.get('received_attacks', None)
			if received_attacks: self.received_attacks.update(received_attacks)

	class Squad:
		def __init__(self, id):
			self.id          = id
			self.members     = []
			self.max_members = None

	# Battler на минималках, необходимый для раскидывания опыта всем, кто его стукал.
	class BattlerShadow:
		def __init__(self, fighter, squad_id, received_attacks):
			self.fighter, self.squad_id, self.received_attacks = fighter, squad_id, received_attacks

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
		self.morgue = []
		self.shadows = []
		self.time_stop = 0

	# Арена подписывается на сообщения от бойцов, чтобы переслать их своим подписчикам.
	# Т. е. MessageSink.receive_note перенаправляется в MessageBroadcaster.note.
	# Вместе с тем, MessageBroadcaster.note может быть вызвана и напрямую, когда сообщение сгенерировано не бойцом, а, например, самой ареной («тик!»).
	def receive_note(self, msg):
		self.note(msg)

	# shortcut_hint — список предпочтительных сокращений участника, либо строка-альтернативное имя для автогенерируемых сокращений.
	# например: add(fighter, squad_id, ai, "Ghost") -> автоматически сгенерируются G, Gh, Go... G2, G3...
	#           add(fighter, squad_id, ai, ("Fi", "Alt")) -> предпочтёт Fi или Alt, прежде чем пойти по автогенерируемым из fighter.name
	# game должна задаваться только для игрока!
	def add(self, fighter, squad_id, ai, *, game=None, shortcut_hint=None, force_delay=None, to_left=False, force_turn_queue_position=None):
		battler = Arena.Battler(fighter, squad_id, ai, self.generate_shortcut(fighter, shortcut_hint), game)
		shadow_index, shadow = next(((index, shadow) for index, shadow in enumerate(self.shadows) if shadow.fighter == fighter), (None, None))
		if shadow:
			del self.shadows[shadow_index]
			battler.received_attacks.update(shadow.received_attacks)

		self.add_battler(battler, force_delay=force_delay, to_left=to_left, force_turn_queue_position=force_turn_queue_position)

	def add_battler(self, battler, force_delay=None, to_left=False, force_turn_queue_position=None):
		if any(b.fighter == battler.fighter for b in self.battlers): impossible(f"{battler.fighter.name} уже на арене")
		if self.started:
			battler.fighter.add_sink(self)
			if battler.ai: battler.ai.setup(battler.fighter, self)
		self.battlers.append(battler)

		squad = self.force_squad(battler.squad_id)
		assert squad.max_members is None or len(squad.members) < squad.max_members, f"{len(squad.members)} / {squad.max_members}"
		squad.members.append(battler)

		self.turn_queue.insert(0 if force_turn_queue_position is None else force_turn_queue_position, battler)
		if force_turn_queue_position is None:
			self.delay_by(battler, random() * self.delay_base(battler.fighter) if force_delay is None else force_delay, to_left=to_left)

	def remove(self, battler, shadow=None):
		assert shadow is None or shadow is self.morgue or shadow is self.shadows
		if shadow is not None and not battler.fighter.transient:
			shadow.append(self.BattlerShadow(battler.fighter, battler.squad_id, dict(battler.received_attacks)))

		if self.started and battler.ai: battler.ai.teardown()
		self.battlers.remove(battler)
		self.squads[battler.squad_id].members.remove(battler)
		self.turn_queue.remove(battler)
		if self.started: battler.fighter.remove_sink(self)

		# Убрать всё, что связано с battler, из всех cumulatives. Можно этого не делать, но на бесконечной арене это станет утечкой.
		for b in self.battlers:
			# incoming_cumulatives обезличены: кто-то мог неудачно наложить заклинание, умереть и эффект в виде повышенной вероятности останется.
			if b.outcoming_cumulatives:
				b.outcoming_cumulatives.pop(battler, None)

		# Убирать received_attacks НЕ нужно — они нужны для раскидывания опыта.
		# Если враг получил 60% урона от саммонов, после его смерти 60% опыта улетают в никуда, даже если саммоны давно исчезли.

	def allies(self, fighter, include_itself=False):
		battler = self.as_battler(fighter)
		return (member.fighter for member in self.squads[battler.squad_id].members if member.fighter != fighter or include_itself and member.fighter.alive)

	def squads_are_enemies(self, a, b):
		for v in (a, b): assert not isinstance(v, (Fighter, self.Battler))
		return a != b

	def are_enemies(self, a, b, maybe=False):
		ba = self.as_battler(a, maybe)
		bb = self.as_battler(b, maybe)
		return ba and bb and self.squads_are_enemies(ba.squad_id, bb.squad_id)

	def enemies(self, fighter):
		battler = self.as_battler(fighter)
		return (member.fighter
			for squad_id, squad in self.squads.items() if self.squads_are_enemies(squad_id, battler.squad_id)
				for member in squad.members if member.fighter.alive)

	def as_battler(self, fighter, maybe=False):
		try:
			return next(b for b in self.battlers if b.fighter == fighter)
		except StopIteration:
			return None if maybe else throw(RuntimeError, f"{fighter.name.cap_first()} не на арене.")

	def stop_time(self, turns):
		if self.time_stopped():
			self.note("*Клац* Ничего не происходит.")
		else:
			self.note("*Щ-щёлк!* Время останавливается.")
			self.time_stop = max(self.time_stop, 1 + turns)

	def time_stopped(self):
		return self.time_stop > 0

	def turn(self):
		check(self.started, "не вызвана start", not self.inside_turn, "уже внутри turn", self.battlers, "арена пуста")
		time_was_stopped_before = self.time_stopped()
		self.inside_turn = True
		self.last_action_cost = 1.0
		battler = self.turn_queue[0]
		if battler.fighter.paralyzed():
			if battler.fighter.props['paralyzed'] > 1:
				battler.fighter.note(lambda sink: sink.you == battler.fighter and "{Вы/F} парализован{ы//а/о}.")
		else:
			if battler.ai: battler.ai.turn()
			if battler.game and battler.game.performance: battler.game.performance.turns += 1

		if not self.time_stopped():
			self.delay_by(battler, self.delay_base(battler.fighter) * self.last_action_cost * uniform(0.8, 1.2))
			self.shift_delays()
		battler.fighter.end_turn(self)
		battler.process_cooldowns()

		if self.time_stopped():
			self.time_stop -= 1
			if not self.time_stopped(): self.note("*Вр-р-р* Время возобновляет свой бег.")
			elif time_was_stopped_before: self.note("*ТИК*")

		corpses = [b for b in self.battlers if b.fighter.dead]
		for corpse in corpses:
			victim = corpse.fighter.props.get('weapon_stolen_from', None)
			if victim and victim.alive and not victim.weapon:
				victim.note(lambda sink: sink.youify("{Вы/F} возвращает{е/} себе", victim) +
					(corpse.fighter.weapon.gender.ize(" сво{й/ю/ё}") if victim == sink.you else victim.gender.ize(" {его/её}") ) +
					" " + corpse.fighter.weapon.name.accusative + ".")
				weapon = corpse.fighter.weapon
				victim.set_weapon(weapon)

			self.remove(corpse, None if corpse.fighter.transient else self.morgue)
		self.inside_turn = False

	def whose_turn(self):
		check(self.battlers, "арена пуста")
		return self.turn_queue[0].fighter

	def delay_base(self, fighter):
		return self.BASELINE_SPD / max(fighter.spd, 1)

	def delay_by(self, battler, delay, to_left=False):
		index = self.turn_queue.index(check(battler, isinstance(battler, Arena.Battler), "battler"))
		battler.initiative += delay
		while index + 1 < len(self.turn_queue) and (gt if to_left else ge)(battler.initiative, self.turn_queue[index + 1].initiative):
			self.turn_queue[index], index = self.turn_queue[index + 1], index + 1
		self.turn_queue[index] = battler

	def start(self):
		check(not self.started, "уже")
		for battler in self.battlers:
			battler.fighter.add_sink(self)
			if battler.ai: battler.ai.setup(battler.fighter, self)
		self.shift_delays()
		self.started = True

		def note_group(sink, group, preface):
			dudes = list(group)
			if dudes:
				return "{0} вста{1}т {2}.".format(preface, "ё" if len(dudes) == 1 else "ю", join_with_lastsep((dude.name for dude in dudes), ", ", " и "))
		self.note(lambda sink: note_group(sink, self.enemies(sink.you), "против вас"))
		self.note(lambda sink: note_group(sink, self.allies(sink.you), "с вашей стороны"))

	def stop(self):
		check(self.started, "не вызвана start")
		for battler in self.battlers:
			if battler.ai: battler.ai.teardown()
			battler.fighter.remove_sink(self)
		self.started = False

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
			return ''.join(filter(None, pieces))

		if isinstance(name_or_list, str):
			tr = transliterate(name_or_list.casefold())
			for isecond in range(len(tr)):
				yield cap_first(tr[0] + (tr[isecond] if isecond > 0 else "")) # Buddy → B, Bu, Bd, Bd, By
			for i in infinite_range(2 if tr else 1):
				yield cap_first((tr[0] if tr else "") + str(i))
		else:
			for single in name_or_list:
				yield check(single, single == cap_first(transliterate(single.casefold())), "имя должно быть латиницей с большой буквы")

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

	class Cumulative:
		__slots__ = 'master', 'victim', 'attack_id', 'accum_k'

		def __init__(self, master, victim, attack_id, accum_k=1.0):
			self.master, self.victim, self.attack_id, self.accum_k = master, victim, attack_id, accum_k

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
	# удар 0: counter = 0,7 — промах
	# удар 1: counter = 1,3 — попадание, -1,0 → 0,3
	# удар 2: counter = 0,9 — промах
	# удар 3: counter = 1,5 — попадание, -1.0 → 0,5
	# удар 4: counter = 1,1 — попадание, -1.0 → 0,1
	def dodge(self, to_hit, ev, cumulative=None):
		hit_chance = self.hit_chance(to_hit, ev, cumulative)
		hit_roll = random()
		dodged = hit_roll >= hit_chance

		if cumulative and (not cumulative.master or self.as_battler(cumulative.master).game) and not self.as_battler(cumulative.victim).game:
			if dodged:
				# Аккумулировать: если есть cumulative.master — в его outcoming_cumulatives, иначе в incoming_cumulatives жертвы.
				# storage будет словарём attack_id ⇒ to-hit.
				if cumulative.master:
					storage = self.as_battler(cumulative.master).outcoming_cumulatives
					if storage is not None: storage = storage[cumulative.victim]
				else:
					storage = self.as_battler(cumulative.victim).incoming_cumulatives

				if storage is not None: storage[cumulative.attack_id] += to_hit * cumulative.accum_k
			else:
				# Сбросить (аналогично).
				if cumulative.master:
					storage = self.as_battler(cumulative.master).outcoming_cumulatives
					if storage: storage = storage.get(cumulative.victim, None)
				else:
					storage = self.as_battler(cumulative.victim).incoming_cumulatives

				if storage: storage.pop(cumulative.attack_id, None)

		return dodged, hit_chance, hit_roll

	def hit_chance(self, to_hit, ev, cumulative=None):
		# Допускается self=None.
		to_hit_bonus = 0
		if self and cumulative:
			if cumulative.master:
				storage = self.as_battler(cumulative.master).outcoming_cumulatives
				if storage:
					storage = storage.get(cumulative.victim, None)
					if storage: to_hit_bonus += storage.get(cumulative.attack_id, 0)

			storage = self.as_battler(cumulative.victim).incoming_cumulatives
			if storage: to_hit_bonus += storage.get(cumulative.attack_id, 0)

		actual_to_hit = to_hit + to_hit_bonus
		return actual_to_hit / (actual_to_hit + ev)

	def shortcut_or_name(self, fighter):
		b = self.as_battler(fighter, maybe=True)
		return b.shortcut if b else fighter.name

	def describe_per_battler(self, what):
		parts = []
		for battler in self.battlers:
			used = set()
			def norep(what, id,):
				result = " " * len(what) if id in used else what
				used.add(id)
				return result
			def shortcut(): return multipad.escape(norep(battler.shortcut, 'battler'))

			if what == 'cumulatives':
				for attack_id, to_hit_bonus in battler.incoming_cumulatives.items() if battler.incoming_cumulatives else ():
					parts.append("{} {} {} {}".format(shortcut(), norep("<=", 'lt-arr'), attack_id, to_hit_bonus))

				for victim, storage in battler.outcoming_cumulatives.items() if battler.outcoming_cumulatives else ():
					for attack_id, to_hit_bonus in storage.items():
						parts.append("{} {} {} {} {}".format(shortcut(), norep("=>", 'rt-arr'),
							norep(self.as_battler(victim).shortcut, 'victim'), attack_id, to_hit_bonus))

			elif what == 'received_attacks':
				for master, con in battler.received_attacks.items():
					if isinstance(master, Weapon):
						master_name = self.shortcut_or_name(master.owner) + "." + master.name
					else:
						master_name = self.shortcut_or_name(master)
					parts.append("{} {} [con]{}[/con] {}".format(shortcut(), norep("<=", 'lt-arr'), multipad.escape(master_name) + ":", con))

			else: impossible(what, "what")

		return "\n".join(multipad(parts)) or "Пусто."

	def describe_cumulatives(self):
		return self.describe_per_battler('cumulatives')

	def describe_received_attacks(self):
		return self.describe_per_battler('received_attacks')

	# (опыт, опыт_отн, золото, «серьёзность» — коэффициент к штрафам)
	def retreat_penalty(self, game, godly_peek=False):
		player = game.player

		# Коэффициент, применяемый к штрафам за побег — на данный момент как процентным, так и абсолютным
		# (т. е. base_penalty = 10% + 15 и master_k = 3 дадут actual_penalty = 30% + 45).
		# Зависит от уровня игрока и противников: побег от сильных монстров карается меньше.
		# TODO: поставить также в зависимость от теншна — штрафовать меньше за побег с 10% HP и т. п.?
		master_k = 1

		effective_enemies_xl = self.effective_enemies_xl(self.enemies(player))
		if player.xl < effective_enemies_xl:
			master_k = clamp(1 - (effective_enemies_xl - player.xl) / 5, 0, 1)
		elif player.xl > effective_enemies_xl:
			master_k = clamp(1 + (player.xl - effective_enemies_xl) / 5, 1, 2)

		if godly_peek:
			return effective_enemies_xl, master_k

		return clamp(0.1 * master_k, 0, 1), True, min(ceil(0.5 * game.gold), ceil((game.gold * 0.1 + 10) * master_k)) if game.gold > 0 else 0, master_k

	@staticmethod
	def effective_enemies_xl(enemies):
		# Для расчёта некоторых вещей используется суммарный «уровень» всех врагов.
		# 2 врага 5 уровня считаются 1 врагом 6-го.
		# Для этого берётся log2 от суммы всех 2^уровень.
		return log2(sum(2 ** enemy.xl for enemy in enemies if not enemy.transient) or 1)

	# Вызывается при побеге игрока с арены.
	# Очищает состояние, которое не должно сохраняться при возвращении на арену: призванных существ, хексы, cumulatives, остановку времени, etc.
	def cleanup_transient(self):
		for summon in [b for b in self.battlers if b.fighter.transient]:
			self.remove(summon)

		for b in self.battlers:
			if not b.game: b.cleanup_transient()

		self.time_stop = 0

	def xp_for(self, living, squad_id):
		xp = 0
		for corpse in self.morgue:
			if self.squads_are_enemies(corpse.squad_id, squad_id):
				ra = corpse.received_attacks.get(living, None)
				if ra:
					# 33% опыта раскидывается за количество атак, 67% — за их «вес» (обычно за вес принимается нанесённый урон).
					attacks_part = ra.attacks / (sum(con.attacks for con in corpse.received_attacks.values()) or 1)
					weights_part = ra.weight / (sum(con.weight for con in corpse.received_attacks.values()) or 1)
					total_part = (attacks_part + 2 * weights_part) / 3
					xp += 16 * corpse.fighter.xl ** 0.6 * total_part
		return xp

	def __getstate__(self):
		check(not self.inside_turn, "inside_turn", not self.started, "started")

		return {k:
			v
			for k, v in self.__dict__.items()
			if k not in ('sinks', 'last_action_cost', 'squads_frozen', 'turn_queue', 'squads')
				and not (k in ('morgue', 'shadows') and not v)}

	def __setstate__(self, state):
		self.__init__()
		self.__dict__.update(state)
		for b in self.battlers:
			self.force_squad(b.squad_id).members.append(b)
		self.turn_queue = sorted(self.battlers, key=lambda b: b.initiative)

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
	def do_describe_internals(self): return self.__class__.__name__

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

# Поведение, основанное на взвешенно-случайном выборе из возможных действий.
# Наследники переопределяют do_considerations, в котором описывают варианты действий через consider:
#
# def do_considerations(self):
# 	self.consider(lambda ai: ai.fighter.act_attack_unarmed(...), 'unarmed', weight=self.fighter.str / 10, soft_cooldown=5)
# 	self.consider(lambda ai: ai.fighter.act_weapon_shoot(...), 'shoot', weight=self.fighter.dex / 10, soft_cooldown=5)
#
# 	if self.fighter.can_cast(some_spell):
# 		self.consider(lambda ai: ai.fighter.act_cast_spell(some_spell, ...), 'some-spell', weight=0.5 * estimate_spell_effectiveness(),
# 			soft_cooldown=0.5, hard_cooldown=2)
#
# Soft cooldown:
# После выполнения действия его вес получает штраф (домножается на soft_cooldown_base), который развеивается в течение следующих soft_cooldown ходов.
# Это разнообразит поведение: ИИ будет менее охотно повторять одно и то же действие.
#
# Hard cooldown:
# Запрещает выполнение действия следующие hard_cooldown ходов.
class RandomizedAI(AI):
	class ActionTrack:
		def __init__(self):
			self.soft_cooldown_turns = 0
			self.soft_cooldown_k = 1
			self.hard_cooldown_turns = 0

	class Option:
		def __init__(self, cb, id, weight, soft_cooldown, hard_cooldown, soft_cooldown_base):
			self.cb, self.id, self.weight, self.soft_cooldown, self.hard_cooldown, self.soft_cooldown_base = \
				cb, id, weight, soft_cooldown, hard_cooldown, soft_cooldown_base

	def __init__(self):
		super().__init__()
		self.tracks = self.options = None

	def setup(self, fighter, arena):
		super().setup(fighter, arena)
		self.tracks, self.options = defaultdict(lambda: self.ActionTrack()), []

	def teardown(self):
		self.tracks = self.options = None
		super().teardown()

	def consider(self, cb, id, weight, *, soft_cooldown=0, hard_cooldown=0, soft_cooldown_base=0.5):
		track = self.tracks.get(id)
		if track:
			if track.hard_cooldown_turns > 0: return
			if track.soft_cooldown_turns: weight *= track.soft_cooldown_k
		self.options.append(self.Option(cb, id, weight, soft_cooldown, hard_cooldown, soft_cooldown_base))
	def do_considerations(self): raise NotImplementedError("do_considerations")

	def do_turn(self):
		self.do_considerations()
		option = choose(self.options, lambda item, _index: item.weight, None)
		self.options.clear()
		track = None

		if option:
			option.cb(self)

			if option.soft_cooldown:
				track = self.tracks[option.id]
				soft_cooldown_base = check(option.soft_cooldown_base, lambda soft_cooldown_base: 0 <= soft_cooldown_base < 1, "soft_cooldown_base")
				track.soft_cooldown_k = min(track.soft_cooldown_k, max(soft_cooldown_base ** 10, track.soft_cooldown_k * soft_cooldown_base))
				track.soft_cooldown_turns = max(track.soft_cooldown_turns, check(option.soft_cooldown, lambda soft_cooldown: soft_cooldown > 0, "soft_cooldown"))

			if option.hard_cooldown:
				track = self.tracks[option.id]
				track.hard_cooldown_turns = max(track.hard_cooldown_turns, check(option.hard_cooldown, lambda hard_cooldown: hard_cooldown > 0, "hard_cooldown"))
		else:
			self.note(lambda sink: sink.youify("{Вы/F} облизывает{есь/ся}. (БАГ)", self.fighter))

		self.tick(track)

	def tick(self, ignore_track):
		expired = []
		for action_id, track in self.tracks.items():
			if track is ignore_track: continue

			if track.hard_cooldown_turns:
				track.hard_cooldown_turns -= 1
			elif track.soft_cooldown_turns:
				track.soft_cooldown_k += (1 - track.soft_cooldown_k) / track.soft_cooldown_turns
				track.soft_cooldown_turns -= 1
				if not track.soft_cooldown_turns: track.soft_cooldown_k = 1

			if not track.soft_cooldown_turns and not track.hard_cooldown_turns:
				expired.append(action_id)

		for action_id in expired:
			del self.tracks[action_id]

	def do_describe_internals(self):
		desc = []
		for action_id, track in self.tracks.items():
			desc.append("{}: {}".format(action_id, ", ".join(filter(None, (
				track.soft_cooldown_turns and "soft_cooldown(k={}, turns={})".format(track.soft_cooldown_k, track.soft_cooldown_turns),
				track.hard_cooldown_turns and "hard_cooldown({})".format(track.hard_cooldown_turns)))) or "?!"))
		return "\n".join(desc) or "Ничего интересного."

class UniversalAI(RandomizedAI):
	def __init__(self):
		super().__init__()
		self.prev_target = None
		self.props = {}

	def do_considerations(self):
		enemies_count = 0
		for _target in self.arena.enemies(self.fighter):
			enemies_count += 1
		def inertly(target): return 1 if target == self.prev_target else 0.285

		for attack_type in ('unarmed', 'weapon_melee', 'weapon_ranged'):
			if (not self.fighter.unarmed if attack_type == 'unarmed' else
				not self.fighter.weapon if attack_type == 'weapon_melee' else
				not self.fighter.weapon or not self.fighter.weapon.ShotBeam if attack_type == 'weapon_ranged' else impossible(attack_type, "attack_type")):
				continue

			for target in self.arena.enemies(self.fighter):
				def consider(attack_type=attack_type, target=target):
					def attack(ai):
						if attack_type == 'unarmed': ai.fighter.act_attack_unarmed(target, ai.arena)
						elif attack_type == 'weapon_melee': ai.fighter.act_weapon_melee(target, ai.arena)
						elif attack_type == 'weapon_ranged':
							def ammo_weight(ammo, _index):
								if isinstance(ammo, SilenceAmmunition) and target.silenced() or isinstance(ammo, TimestopAmmunition) and ai.arena.time_stopped():
									return 0
								return 1. if ammo.finite_charges else 1.
							ammo = choose((ammo for ammo in ai.fighter.weapon.ammos if ammo.has_charges()), ammo_weight, default=None)
							ai.fighter.act_weapon_shoot(target, ai.arena, ammo)
						else: impossible(attack_type, "attack_type")
						self.prev_target = target
					weight = inertly(target) / enemies_count
					if attack_type == 'weapon_ranged': weight *= (1 + len(self.fighter.weapon.upgrades)) ** 0.5
					self.consider(attack, attack_type, weight, soft_cooldown_base=0.8, soft_cooldown=1)
				consider()

		if self.fighter.can_cast():
			for sp in self.fighter.spells:
				if not self.fighter.can_cast(sp): continue

				if isinstance(sp, ResistibleSpell):
					for target in self.arena.enemies(self.fighter):
						if isinstance(sp, HexSpell) and target.find_hex(sp.hex_class): continue
						if isinstance(sp, DrainXP) and target.xl == 1 and target.xp == 0: continue
						def consider(sp=sp, target=target):
							def attack(ai):
								self.fighter.act_cast_spell(sp, target, ai.arena)
								self.prev_target = target

							weight = inertly(target) / enemies_count
							if isinstance(sp, DeathWord): weight *= target.hp / max(self.fighter.str/2, target.mhp)
							self.consider(attack, sp.cmd(), weight, soft_cooldown=4 if isinstance(sp, DrainXP) else 6, soft_cooldown_base=0.1, hard_cooldown=2)
						consider()

				elif isinstance(sp, PhantasmalGate):
					squad = self.arena.squads[self.arena.as_battler(self.fighter).squad_id]
					if squad.max_members is not None and squad.max_members - len(squad.members) < 1: continue
					existing_ghosts = sum(1 for b in squad.members if b.fighter.preset == 'ghost')
					def consider(sp=sp):
						def summon(ai):
							self.fighter.act_cast_spell(sp, None, ai.arena)
						self.consider(summon, sp.cmd(), 1 / (1 + existing_ghosts), hard_cooldown=2, soft_cooldown=6, soft_cooldown_base=0.2)
					consider()

				elif isinstance(sp, DrainLife):
					wounded_score = 0
					for ally in self.arena.allies(self.fighter, include_itself=True):
						if ally.hp < ally.mhp:
							wounded_score += (1 - ally.hp / ally.mhp) * (ally.xl / self.fighter.xl if ally.xl < self.fighter.xl else 1)
					if wounded_score:
						best_estimated_drain = None
						for ipass in range(2):
							for target in self.arena.enemies(self.fighter):
								estimated_drain = sp.drain_dis(self.fighter, target).estimate_avg()
								if ipass == 0:
									best_estimated_drain = max(best_estimated_drain, estimated_drain) if best_estimated_drain is not None else estimated_drain
								else:
									def consider(sp=sp, target=target):
										def drain(ai):
											self.fighter.act_cast_spell(sp, target, ai.arena)
											self.prev_target = target
										self.consider(drain, sp.cmd(), wounded_score * (estimated_drain / best_estimated_drain) * inertly(target),
											soft_cooldown=3, soft_cooldown_base=0.2, hard_cooldown=1)
									consider()

				elif isinstance(sp, Barrier):
					if any(isinstance(hex, BarrierHex) for hex in self.fighter.hexes) or 'barrier' in self.arena.as_battler(self.fighter).cooldowns: continue
					def consider(sp=sp):
						def cast(ai):
							self.fighter.act_cast_spell(sp, self.fighter, ai.arena)
							self.props['barrier_cast'] = True
						weight = 3 if 'barrier_cast' not in self.props else 1
						weight *= clamp(0.7 * self.fighter.mhp / self.fighter.hp, 1, 5)
						weight += sum(6 / ally.props['remaining_life'] for ally in self.arena.allies(self.fighter) if ally.preset == 'lightning')

						self.consider(cast, 'barrier', weight, soft_cooldown=5, soft_cooldown_base=0.1, hard_cooldown=3)
					consider()

				elif isinstance(sp, BallLightning):
					squad = self.arena.squads[self.arena.as_battler(self.fighter).squad_id]
					if squad.max_members is None or squad.max_members - len(squad.members) >= 1:
						barrier_hex = self.fighter.find_hex(BarrierHex)
						barrier_spell = next((sp for sp in self.fighter.spells if isinstance(sp, Barrier)), None)
						good_barrier = barrier_hex and barrier_hex.turns >= 5
						if not good_barrier:
							if not barrier_spell or self.fighter.mp < sp.mp_cost() + barrier_spell.mp_cost(): continue

						existing_lightnings = sum(1 for b in squad.members if b.fighter.preset == 'lightning')
						weight = 1 / (1 + existing_lightnings) ** 1
						if not good_barrier: weight /= 2
						def consider(sp=sp):
							def conjure(ai):
								self.fighter.act_cast_spell(sp, None, ai.arena)
							self.consider(conjure, sp.cmd(), weight, hard_cooldown=1, soft_cooldown=7, soft_cooldown_base=0.1)
						consider()

				elif isinstance(sp, Chronosphere):
					def consider(sp=sp):
							def cast(ai):
								self.fighter.act_cast_spell(sp, None, ai.arena)
							self.consider(cast, sp.cmd(), 0.8, hard_cooldown=sp.turns(self.fighter) + 2, soft_cooldown=8, soft_cooldown_base=0.1)
					consider()

		for sp in self.fighter.specials:
			if isinstance(sp, Thievery):
				for target in self.arena.enemies(self.fighter):
					target_b = self.arena.as_battler(target)
					if not target_b.game or target_b.game.gold <= 0: continue

					def consider(sp=sp, target=target, target_b=target_b):
						def steal(ai):
							sp.act_steal_gold(target_b, ai.arena)
							self.prev_target = target
						self.consider(steal, 'steal', 0.5 * inertly(target) * min(target_b.game.gold ** 0.5 / 10, 3) / enemies_count,
							soft_cooldown=7, soft_cooldown_base=0.25, hard_cooldown=1)
					consider()

			elif isinstance(sp, Grasp):
				for target in self.arena.enemies(self.fighter):
					if 'grasp_immunity' in self.arena.as_battler(target).cooldowns: continue
					grasp = target.find_hex(GraspHex)
					if grasp: continue

					slime = target.find_hex(SlimeHex)
					def consider(sp=sp, target=target):
						def grasp(ai):
							sp.act_grasp(target, ai.arena)
						self.consider(grasp, 'grasp', (1 + (2 * slime.power if slime else 0)) * inertly(target) / enemies_count, soft_cooldown=4, soft_cooldown_base=0.2)
					consider()

			elif isinstance(sp, Impregnation):
				for target in self.arena.enemies(self.fighter):
					if target.can_be_impregnated:
						slime = target.find_hex(SlimeHex)
						if not slime: continue

						grasp = target.find_hex(GraspHex)
						if not grasp or grasp.ticks < 1: continue

						def consider(sp=sp, target=target):
							def impregnate(ai):
								sp.act_impregnate(target, ai.arena)
							self.consider(impregnate, 'impregnate',
								0.6 * clamp(self.fighter.mhp / self.fighter.hp, 1, 5) * (grasp.ticks ** 0.5 + slime.power ** 0.5) * inertly(target) / enemies_count)
						consider()

			elif isinstance(sp, Marauding):
				if 'stolen_weapon' not in self.fighter.props:
					for target in self.arena.enemies(self.fighter):
						if target.weapon:
							def consider(sp=sp, target=target):
								def maraud(ai):
									sp.act_maraud(target, ai.arena)
								self.consider(maraud, 'steal', (1 + len(target.weapon.upgrades)) ** 0.5 * inertly(target) / enemies_count,
									soft_cooldown=4, soft_cooldown_base=0.1, hard_cooldown=2)
							consider()

			elif isinstance(sp, PsionicThievery):
				for target in self.arena.enemies(self.fighter):
					if any(isinstance(up, SpellUpgrade) for up in target.upgrades):
						def consider(sp=sp, target=target):
							def psi_steal(ai):
								sp.act_psi_steal(target, ai.arena)
							self.consider(psi_steal, 'steal', 0.5 * sum(1 for up in target.upgrades if isinstance(up, SpellUpgrade)) ** 0.5 * inertly(target) / enemies_count,
								soft_cooldown=4, soft_cooldown_base=0.1, hard_cooldown=2)
						consider()

class BallLightningAI(AI):
	def do_turn(self):
		rem, orig = (self.fighter.props[prop_name] for prop_name in ('remaining_life', 'orig_life'))
		if rem > 1:
			self.arena.note(lambda sink: sink.youify("{Вы/F}" + (" угрожающе" if (rem - 1) <= orig // 2 else "") + " трещит{е/}.", self.fighter))

class Con:
	# На данный момент сделано так, что чуть больше нуля даёт [#....] и чуть меньше максимума — [####.]
	@staticmethod
	def vital_bar(cur, max, divs=10, fillchar='#', emptychar='.', prev=None, pluschar='+', minuschar='x', flip=False):
		def bars(cur, divs): return int(clamp(int(cur > 0) + cur * (divs - 1) / (max or 1), 0, divs))
		cur_bars = bars(cur, divs)
		prev_bars = cur_bars if prev is None else bars(prev, divs)
		fill_bars, extra_bars, extrachar = (prev_bars, cur_bars - prev_bars, pluschar) if cur_bars >= prev_bars else (cur_bars, prev_bars - cur_bars, minuschar)
		parts = fillchar * fill_bars, extrachar * extra_bars, emptychar * (divs - fill_bars - extra_bars)
		return "[{}]".format("".join(reversed(parts) if flip else parts))

	@staticmethod
	def bullet_bar(cur, max, fillchar='#', emptychar='.'):
		return fillchar * cur + emptychar * (max - cur)

	# Раньше wrap() был устроен чуть сложнее, чтобы попытаться доходить до края терминала, когда возможно, но это не всегда работало:
	# нет гарантии, что консоль переведёт строку по достижении get_terminal_size.columns.
	@staticmethod
	def safe_width(width):
		return width - 1

class VitalBarTest(TestCase):
	def cases(self): return (
		(0, 5, 5, "[.....]"), (1, 5, 5, "[#....]"), (2, 5, 5, "[##...]"), (3, 5, 5, "[###..]"), (4, 5, 5, "[####.]"), (5, 5, 5, "[#####]"),
		(0.001, 5, 5, "[#....]"), (4.999, 5, 5, "[####.]"), (1.4, 5, 5, "[##...]"),
		(4, 5, 5, {'prev': 2}, "[##++.]"), (2, 5, 5, {'prev': 4}, "[##xx.]"), (0, 5, 5, {'prev': 5}, "[xxxxx]"), (5, 5, 5, {'prev': 0}, "[+++++]"))

	def one(self, cur, max, divs, *etc):
		args, expect = {}, None
		for something in etc:
			if isinstance(something, dict): args.update(something)
			else: expect = something
		self.assertEqual(Con.vital_bar(cur, max, divs, **args), expect)

class Mode:
	def __init__(self):
		self.session = None
		self.last_screen = self.last_input = self.last_command_chosen = self.input_on_last_command_chosen = self.force_input = None
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

	def handle_command(self, cmd): return self.do_handle_command(cmd)
	def do_handle_command(self, cmd): return self.session.handle_command(cmd, self)

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
	def yes_no(self, *a, **ka): return self.shortcut(YesNo, *a, **ka)

	do_prompt = True
	do_cls    = True
	term_width = property(lambda self: self.session.term_width)
	term_height = property(lambda self: self.session.term_height)
	safe_term_width = property(lambda self: self.session.safe_term_width)
	prev_mode = False # запомнит предыдущий режим, т. о. к нему можно будет вернуться

class MainMenu(Mode):
	def do_render(self, lines, cmds):
		has_saves = any(Game.scan_saves())
		has_HoF = self.session.HoF.has_anything_to_display()
		has_orig = self.session.HoF.completed_once()

		ci = 1
		lines.extend([
			               "        VISIBLE FIGHTERS v.{0}       ".format(".".join(map(str, app_version))),
			             "({0})        - новая игра -       {1}".format(ci, ("(new" + ("*" if has_orig else "") + ")").rjust(len("(new*)")))])
		cmds.add((str(ci), 'new'), lambda: self.start_new_game(), '?', lambda: self.more("Начать новую игру."))
		if has_orig:
			cmds.add((str(ci) + '*', 'new*'), lambda: self.to_invisible_fighters(), '?', lambda: self.more("Оригинальная игра Invisible Fighters."))
		ci += 1

		if has_saves:
			lines.append("({0})        - продолжить -       (load)".format(ci))
			cmds.add((str(ci), 'load'), lambda: self.switch_to(LoadGame()), '?', lambda: self.more("Продолжить сохранённую игру."))
			ci += 1

		if has_HoF:
			lines.append("({0})         - мемориал -         (hof)".format(ci))
			cmds.add((str(ci), 'hof'), lambda: self.switch_to(HallOfFameView()), '?', lambda: self.more("Последние и лучшие результаты."))
			ci += 1

		lines.extend([
			             "({0})          - основы -         (help)".format(ci),
			               "(0)           - уйти -          (quit)"])
		cmds.add((str(ci), 'help'), lambda: self.more(MainMenu.Help, do_cls=True, markdown=True),
			'?', lambda: self.more("Вывести справку об основных моментах."))
		cmds.add(('0', 'quit'), lambda: self.session.post_quit(), '?', lambda: self.more("Выйти из приложения."))

	def start_new_game(self):
		game = Game()
		game.gold = 100
		game.player = Fighter()
		game.player.preset = 'player'
		game.player.set_unarmed(BareHands())
		game.player.set_weapon(MachineGun())
		game.next_level = 1
		self.switch_to(AskName(game))

	Help = (
		"Ваш автомат — живой, и при использовании в бою ему будет перенаправлена часть опыта. Пули пробивают броню, но не масштабируются статами персонажа.\n"
		"\n"
		"Сила      (STR) — |влияет на силу ударов и максимум HP.\n"
		"Интеллект (INT) — |на максимум маны, силу заклинаний и сопротивление магии.\n"
		"Ловкость  (DEX) — |на точность атаки и шанс уворота.\n"
		"Скорость  (SPD) — |на инициативу в бою. Например, если ваша скорость 150, а противника 100, "
		                   "на три ваших действия будут приходиться два действия противника.\n"
		"\n"
		"Между боями вы можете тратить золото на апгрейды в пределах полученного опыта. Золото за даунгрейд компенсируется частично.\n"
		"В игре 10 уровней. Сохранение выполняется автоматически.\n"
		"\n"
		"Можно сокращать команды: heal hp -> h h, b.fire? -> b.f?.\n"
		"                                               ^       ^\n"
		"                                       |\"?\" выводит справку по команде или подписанному элементу экрана.")

	def do_deactivate(self):
		self.session.globals.recent_fixed_name_proposals = 0
		self.session.HoF.close()

	def do_handle_command(self, cmd):
		if cmd == 'new*':
			self.to_invisible_fighters()
		else:
			return super().do_handle_command(cmd)
		return True

	def to_invisible_fighters(self):
		self.yes_no("Открыть оригинальную игру Invisible Fighters?", lambda mode: mode.switch_to(InvisibleFighters(extra_reverts=1)), default=0)

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
		while down and start >= 0 or not down and start <= len(previews.items):
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
			self.show_dn  = check(self.estimate_items_count(self.first_dn), lambda show_dn: show_dn > 0, "show_dn")
		else:
			self.first_dn = None

 		# То же для прокрутки вверх
		if self.first > 0:
			count = check(self.estimate_items_count(self.first, down=False), lambda count: count > 0, "count")
			self.first_up = self.first - count
			self.show_up = count if self.first_up > 0 else self.estimate_items_count(self.first_up)
		else:
			self.first_up = None

	def do_render(self, lines, cmds):
		if self.first_up is not None:
			has_start = self.first_up > 0
			lines.append("({}{}) (up{})".format(1 + self.first_up,
				"–{}".format(1 + self.first_up + self.show_up - 1) if self.show_up > 1 else "",
				", start" if has_start else ""))
			cmds.add('up', lambda: self.up(), '?', lambda: self.scroll_help(self, "вверх"))
			if has_start:
				cmds.add('start', lambda: self.up(to_start=True), '?', lambda: self.scroll_help(self, "в начало"))

		def describe_up_new_miss_onetime():
			um, self.up_new_miss = self.up_new_miss, None
			return um and "({0})".format("/".join(s for s in (um[0] and f"+{um[0]}", um[1] and f"-{um[1]}") if s))

		desc_pad = len(str(1 + self.first + self.show - 1)) + 3 # (, число, ), пробел
		for index, item in enumerate(self.session.previews.items[self.first:self.first + self.show]):
			for tryIndex in range(2): # перестраховка, скорее всего, не нужно, но пусть будет
				try:
					if item.index > self.first or self.first > 0: lines.append("")
					lines.append(self.save_desc(item, desc_pad, first_line_extra=index == 0 and describe_up_new_miss_onetime()))
					break
				except Exception as e:
					if not item.bad and tryIndex == 0: self.session.previews.force_bad(item, e)
					else: raise
			if item.bad:
				cmds.add(str(1 + item.index), (lambda item=item: lambda: self.remove(item, desc_pad))(), '?', lambda: self.more("Удалить это сохранение."))
			else:
				cmds.add(str(1 + item.index), (lambda item=item: lambda: self.load(item, desc_pad))(), '?', lambda: self.more("Загрузить это сохранение."))
			if not item.seen:
				self.something_new = True # <enter> уберёт звёздочки, а не прокрутит экран
				item.seen = True # пользователь увидел — в следующий раз не рисовать звёздочку

		if self.first_dn is not None:
			has_end = self.first_dn + self.show_dn < len(self.session.previews.items)
			lines.append("")
			lines.append("({}{}) (down{})".format(1 + self.first_dn,
				"–{}".format(1 + self.first_dn + self.show_dn - 1) if self.show_dn > 1 else "",
				", end" if has_end else ""))
			cmds.add('down', lambda: self.down(), '?', lambda: self.scroll_help(self, "вниз"))
			if has_end:
				cmds.add('end', lambda: self.down(to_end=True), '?', lambda: self.scroll_help(self, "в конец"))

		remove_inscriptions = ['remove <номер>']
		if self.session.previews.items:
			cmds.add('remove', lambda: self.remove_by_number(desc_pad),
				'?', lambda: self.more("Удалить сохранение{0}.".format(" (спросит номер)" if len(self.session.previews.items) > 1 else "")))
		for item in self.session.previews.items[self.first:self.first + self.show]:
			cmds.add('remove ' + str(1 + item.index), (lambda item=item: lambda: self.remove(item, desc_pad))(),
				'?', lambda: self.more("Удалить это сохранение."))

		if len(self.session.previews.items) > 1 and not all(item.bad for item in self.session.previews.items):
			cmds.add('remove all', lambda: self.batch_remove(None, "все"), '?', lambda: self.more("Удалить все сохранения."))
			remove_inscriptions.append('remove all')

		if any(item.bad for item in self.session.previews.items):
			remove_inscriptions.append('remove bad')
			cmds.add('remove bad', lambda: self.batch_remove(lambda item: item.bad, "повреждённые", default_yes=True),
				'?', lambda: self.more("Удалить повреждённые сохранения."))

		lines.append("\nУдалить сохранение ({0})".format(", ".join(remove_inscriptions)))
		lines.append("Вернуться в главное меню (quit)")
		cmds.add('quit', lambda: self.revert(), '?', lambda: self.more("Вернуться в главное меню."))

	def do_handle_command(self, cmd):
		if cmd == "":
			if not self.something_new:
				self.up_new_miss = self.session.previews.update()
				if not self.up_new_miss:
					if self.first_dn is not None: self.down()
					elif self.first > 0 and False:
						def confirmed(mode):
							mode.revert()
							self.first = 0
						self.yes_no("Вернуться в начало?", confirmed, default=1)
		elif cmd == '*update':
			# Перечитать содержимое папки с сохранениями.
			self.force_update()
		elif cmd == '*ok':
			# Отобразить вспомогательные параметры сохранений (order_key, character_uid).
			self.display_order_keys = not self.display_order_keys
		else:
			return super().do_handle_command(cmd)
		return True

	@staticmethod
	def scroll_help(mode, where):
		mode.more("Прокрутить список {}.".format(where))

	def up(self, to_start=False):
		self.first = 0 if to_start else check(self.first_up, self.first_up is not None, "first_up?!") # а show всё равно обновится в process

	def down(self, to_end=False):
		self.first = len(self.session.previews.items) if to_end else check(self.first_dn, self.first_dn is not None, "first_dn?!")

	def save_desc(self, item, pad, first_line_extra=None):
		cmd = "({0}) ".format(1 + item.index).ljust(pad)
		return cmd + item.load_screen_desc(self.session, npad=pad, first_line_extra=first_line_extra, display_order_key=self.display_order_keys)

	def load(self, item, desc_pad):
		assert item.preview
		self.yes_no("\n{0}\n\nЗагрузить эту игру?".format(self.save_desc(item, desc_pad)),
				lambda mode: Game.load_nothrow(item, self, on_fail=lambda mode: mode.revert()), default=0)

	def remove(self, item, desc_pad, extra_reverts=0, default_yes=sentinel):
		self.yes_no(
			"\n{0}\n\nУдалить это сохранение?".format(self.save_desc(item, desc_pad)),
			lambda mode: Game.remove_save_nothrow(mode, item.full_save_path, item, extra_reverts=1 + extra_reverts, note_success=True),
			default=0 if (default_yes if default_yes is not sentinel else item.bad) else 1)

	def remove_by_number(self, desc_pad):
		count = len(self.session.previews.items)
		if count == 1:
			self.remove(self.session.previews.items[0], desc_pad)
		elif count:
			def handle_answer(input, mode):
				if not input or 'quit'.startswith(input): mode.revert(); return
				try:
					index = int(input) - 1
					if index >= 0 and index < count: pass
					else: raise ValueError("Неверный ввод.")
				except ValueError:
					mode.more("Нет таких.").reverts(1)
					return
				self.remove(self.session.previews.items[index], desc_pad, extra_reverts=1, default_yes=True)

			self.prompt(f"Какое сохранение удалить? ({1} – {count}) ", handle_answer)

	def batch_remove(self, predicate, adjective, default_yes=False):
		total = sum(1 for item in self.session.previews.items if not predicate or predicate(item))
		def confirmed(mode):
			removed = 0
			for item in reversed(self.session.previews.items):
				if (not predicate or predicate(item)) and not Game.remove_save_nothrow(mode, item.full_save_path, item, extra_reverts=1):
					check(isinstance(self.session.mode, More), "сейчас должно висеть сообщение об ошибке remove_save_nothrow")
					self.session.mode.msg += "\n\n{0}, {1}.".format(plural(removed, "{N} файл{/а/ов} удал{ён/ены/ены}"),
						plural(total - removed, "{N} не обработан{/о/о}"))
					break
				removed += 1
			else:
				mode.more("{0} сохранения удалены.".format(cap_first(adjective))).reverts(1)
		self.yes_no("Удалить {0}?".format(plural(total, "{N} сохранени{е/я/й}")), confirmed, default=0 if default_yes else 1)

	def force_update(self):
		self.session.previews.post_force_update(silent=False)
		self.more("Обновление...")
	prev_mode = True

class HallOfFameView(Mode):
	prev_mode = True

	def __init__(self, highlight_rowid=None, highlight_rec=None, then=None):
		super().__init__()
		self.then = then
		if then: self.prev_mode = False
		self.highlight_rowid, self.highlight_rec = highlight_rowid, highlight_rec
		self.offset = self.offset_up = self.count_up = self.offset_dn = self.count_dn = None
		self.count = None
		self.order = self.failed = self.corrupted = self.drawn = None
		self.to_display = self.expected_lines_count = None

	def switch_to_order(self, order):
		self.order = order
		self.offset = None

	def do_activate(self):
		self.switch_to_order('score')

	def fail(self, e, corrupted=True):
		self.failed = exception_msg(e)
		self.corrupted = corrupted

	# Оценивает, сколько элементов будет видно на экране, начиная с позиции start (при движении вверх start не включается). mode — 'down', 'up', 'around'.
	# Возвращает (1) сами элементы, (2) итоговое число строк (вообще всех, добавляемых в do_render — с заголовком и т. п.), (3) новое значение start.
	# Для большего веселья в do_render стоит ассерт на точность числа строк.
	def fetch_for_display(self, start, mode):
		def calc_rec_lines(rec):
			return (
				1 + # имя игрока, счёт
				(1 if rec.wpn_name or rec.fights else 0) + # имя оружия, статистика по битвам
				1) # дата и время

		def calc_total_lines(items_count, rec_lines, start, count):
			return (
				2 + # заголовок + пустая строка
				(2 if start > 0 else 0) + # (up) + пустая строка
				rec_lines +
				items_count + # пустые строки после записей
				(2 if start + items_count < count else 0) + # (dn) + пустая строка
				1) # Вернуться в главное меню (quit)

		def try_order():
			dn = iter(self.session.HoF.fetch(self.order, start))
			up = iter(self.session.HoF.fetch(self.order, self.count - start, reverse=True))
			iteration = 0

			while dn or up:
				if dn and not (mode == 'up' and up):
					nx_dn = next(dn, None)
					if nx_dn: yield nx_dn, False
					else: dn = None

				if up and not (mode == 'down' and dn or mode == 'around' and iteration == 0):
					nx_up = next(up, None)
					if nx_up: yield nx_up, True
					else: up = None
				iteration += 1

		reserve = 6
		items, items_prepend, rec_lines = [], [], 0

		for (rowid, rec), prepend in try_order():
			(items_prepend if prepend else items).append((rowid, rec)) # Чтобы новый массив не создавать. Потом этот элемент убирается, если оказалось, что он лишний.
			new_rec_lines = rec_lines + calc_rec_lines(rec)
			new_total_lines = calc_total_lines(len(items_prepend) + len(items), new_rec_lines, start - len(items_prepend), self.count)

			if new_total_lines + reserve <= self.term_height or total_lines is None or (len(items_prepend) + len(items)) <= 3:
				rec_lines, total_lines = new_rec_lines, new_total_lines
			else:
				(items_prepend if prepend else items).pop()
				break

		items_prepend.reverse()
		return items_prepend + items, total_lines, start - len(items_prepend)

	def do_process(self):
		if self.failed: return
		failed = None

		# Здесь много паранойи (причём на данный момент выключенной через impossible).
		# При любой несостыковке (например — запомнено count = 30, а выборка вниз с 20-го насчитала 15 элементов, или, наоборот, выдала 0)
		# предполагается повторить процесс заново, а при превышении разумного числа таких повторений — выбросить ошибку.
		# Это будет иметь значение только в гипотетическом случае изменения таблицы извне.
		try:
			offset = self.offset
			go_from_end = False

			for _tryIndex in range(10):
				self.count = self.session.HoF.count()
				if not self.count:
					def then(mode):
						assert mode is self
						self.quit()
					self.to_display = None
					self.more("Мемориал пуст.", do_cls=self.drawn).then(then)
					return

				mode = 'down'
				if self.offset is None:
					if self.highlight_rowid is not None:
						# Прокрутить таблицу так, чтобы она была построена «вокруг» подсвеченной записи, по правилам fetch_for_display(mode='around').
						offset = self.session.HoF.offset(self.highlight_rec, self.highlight_rowid, self.order)
						mode = 'around'
					else:
						# Если подсвеченной записи не было — начать с первой записи.
						offset = 0
				elif go_from_end or offset >= self.count:
					# Пойти с конца.
					offset, mode, go_from_end = self.count, 'up', False

				to_display, self.expected_lines_count, new_offset = self.fetch_for_display(offset, mode)

				# Выбралось 0 элементов? Повторить, с конца.
				if not to_display:
					go_from_end = True
					impossible("RE:1")
					continue

				# Подсвеченной записи не оказалось на месте? Повторить.
				# Дополнительная паранойя: в дополнение к rowid проверяются большинство полей (включая имя и время).
				if self.offset is None and self.highlight_rowid is not None:
					def extract_fields(rec):
						yield from ((k, HallOfFame.pack_time(v) if k == 'timestamp' else v) for k, v in getattrs(rec, (col for col in rec.COLUMNS if col != 'fights')))

					if not (new_offset <= offset < new_offset + len(to_display) and to_display[offset - new_offset][0] == self.highlight_rowid and
						all(kv1 == kv2 for kv1, kv2 in zip(extract_fields(to_display[offset - new_offset][1]), extract_fields(self.highlight_rec)))):
						failed = RuntimeError("Запись не добавилась.")
						impossible(f"RE:2: offset = {offset}, new_offset = {new_offset}, to_display = {len(to_display)}, highlight_rowid = {self.highlight_rowid}, "
							f"actual_rowid = {new_offset <= offset < new_offset + len(to_display) and to_display[offset - new_offset][0]}")
						continue

				# Если ожидается, что будут элементы сверху/снизу — выбрать их и сохранить в offset_up/count_up/offset_dn/count_dn.
				# При несогласованности — повторить всё сначала.
				if new_offset > 0:
					to_display_up, _expected_lines_count_up, self.offset_up = self.fetch_for_display(new_offset, 'up')
					if not to_display_up or self.offset_up < 0 or self.offset_up + len(to_display_up) > self.count:
						impossible(f"RE:3: new_offset = {new_offset}, to_display = {len(to_display)}, offset_up = {self.offset_up}, to_display_up = {len(to_display_up)}, "
							f"count = {self.count}")
						continue
					self.count_up = len(to_display_up)
				else:
					self.offset_up = self.count_up = None

				if new_offset + len(to_display) < self.count:
					to_display_dn, _expected_lines_count_dn, self.offset_dn = self.fetch_for_display(new_offset + len(to_display), 'down')
					if not to_display_dn or self.offset_dn < 0 or self.offset_dn + len(to_display_dn) > self.count:
						impossible(f"RE:4: new_offset = {new_offset}, to_display = {len(to_display)}, offset_dn = {self.offset_dn}, to_display_dn = {len(to_display_dn)}, "
							f"count = {self.count}")
						continue
					self.count_dn = len(to_display_dn)
				else:
					self.offset_dn = self.count_dn = None

				# Ну, кажется, всё хорошо. Запомнить оставшуюся информацию для do_render и выйти.
				self.to_display, self.offset = to_display, new_offset
				break
			else:
				failed = failed or RuntimeError("Не удаётся построить устойчивый список. Попробуйте переоткрыть.")
				raise failed

		except Exception as e:
			self.fail(e, corrupted=e is not failed)
			return

	def same_orders(self, order_a, order_b):
		return all(rowid_a == rowid_b for (rowid_a, _rec_a), (rowid_b, _rec_b) in zip(self.session.HoF.fetch(order_a), self.session.HoF.fetch(order_b)))

	def do_render(self, lines, cmds):
		start = len(lines)
		if not self.failed and self.to_display is not None:
			record_lines = []
			what_is, transitions = [], []
			for target_order in ('score', 'time'):
				cmd, name, sort_instr = (
					('best', "лучшие", "очкам") if target_order == 'score' else
					('last', "последние", "времени") if target_order == 'time' else impossible(target_order, "order"))

				if target_order == self.order or self.same_orders(self.order, target_order):
					what_is.append(name)
				else:
					transitions.append("{} ({})".format(name, cmd))
					(lambda cmd=cmd, target_order=target_order, sort_instr=sort_instr:
						cmds.add(cmd, lambda: self.switch_to_order(target_order), '?', lambda: self.more("Отсортировать по {}.".format(sort_instr))))()

			pad = len(str(1 + self.offset + len(self.to_display) - 1)) + len("#. ")
			for index, (rowid, rec) in enumerate(self.to_display):
				human_no = 1 + self.offset + index
				you = rowid == self.highlight_rowid
				you_mark = "Вы> " if you else ""
				pad_this = pad
				if you: pad_this = max(pad_this, len(you_mark) + len(str(human_no)) + len("#. "))
				strno = 0

				def prefix():
					return ("{}#{}. ".format(you_mark, 1 + self.offset + index) if strno == 0 else "" if strno == 1 else "").ljust(pad_this)

				mark_mp = "[mark]"
				record_lines.append("{px}{player} {mark_mp}{mark} ({score})".format(px=prefix(), mark_mp=mark_mp,
					player = multipad.escape(rec.name),
					mark = rec.score_mark, score = rec.score))
				strno += 1

				if rec.wpn_name or rec.fights:
					record_lines.append("{px}{wpn_name}{and_fights}".format(px=prefix(),
						wpn_name = multipad.escape(rec.wpn_name) or "",
						and_fights = " {mark_mp}{fights}".format(mark_mp=mark_mp, fights=self.describe_fights(rec, (3 * self.safe_term_width) // 7)) if rec.fights else ""))
					strno += 1

				if index > 0 and self.to_display[index - 1][1].timestamp[:3] == rec.timestamp[:3]:
					ha = "\"\""
					target_len = len(human_datetime(self.to_display[index - 1][1].timestamp, do_time=False, do_sep=True))
					target_len_wo_ha = target_len - len(ha) - 1
					target_len_wo_ha -= target_len_wo_ha % 2
					h1 = "—".ljust(target_len_wo_ha // 2)
					h2 = "—".rjust(target_len_wo_ha - len(h1))
					date = (h1 + ha + h2).ljust(target_len)
				else:
					date = human_datetime(rec.timestamp, do_time=False, do_sep=True)

				record_lines.append(prefix() + date + human_datetime(rec.timestamp, do_date=False) + " " + mark_mp)
				strno += 1

				record_lines.append("")

			left = "{} БОЙЦЫ".format("/".join(what_is).upper())
			right = " {}".format(" ".join(transitions)) if transitions else ""
			lines.append(left + (" " * (self.safe_term_width - len(left) - len(right)) + right if right else ""))
			lines.append("")

			if self.offset_up is not None:
				has_start = self.offset_up > 0
				lines.append("{}(up{})".format(
					"#{}{}. ".format(1 + self.offset_up, "–{}".format(1 + self.offset_up + self.count_up - 1) if self.count_up != 1 else "").ljust(pad),
					", start" if has_start else ""))
				cmds.add('up', lambda: self.up(), '?', lambda: LoadGame.scroll_help(self, "вверх"))
				if has_start:
					cmds.add('start', lambda: self.up(to_start=True), '?', lambda: LoadGame.scroll_help(self, "в начало"))
				lines.append("")

			lines.extend(multipad(record_lines))

			if self.offset_dn is not None:
				has_end = self.offset_dn + self.count_dn < self.count
				lines.append("{}(down{})".format(
					"#{}{}. ".format(1 + self.offset_dn, "–{}".format(1 + self.offset_dn + self.count_dn - 1) if self.count_dn != 1 else "").ljust(pad),
					", end" if has_end else ""))
				cmds.add('down', lambda: self.down(), '?', lambda: LoadGame.scroll_help(self, "вниз"))
				if has_end:
					cmds.add('end', lambda: self.down(to_end=True), '?', lambda: LoadGame.scroll_help(self, "в конец"))
				lines.append("")

		if self.failed:
			lines.extend(("ОШИБКА", self.failed, ""))
			if self.corrupted:
				with suppress(OSError):
					if path.exists(self.session.HoF.filename):
						lines.append("Стереть (erase bad)")
						cmds.add('erase bad',
							lambda: self.yes_no("Вы уверены, что хотите стереть нечитаемый мемориал?", lambda mode: self.erase(mode, reverts=1), default=1),
							'?', "Стереть нечитаемый мемориал.")

		lines.append("Вернуться в главное меню (quit)")
		cmds.add('quit', lambda: self.quit(), '?', lambda: self.more("Вернуться в главное меню."))

		if not self.failed:
			assert len(lines) - start == self.expected_lines_count, f"{len(lines) - start} <-> расч. {self.expected_lines_count}"
		self.drawn = True

	def do_handle_command(self, cmd):
		if not cmd:
			if self.offset_dn is not None: self.down()
			elif self.offset_up is not None and False:
				def confirmed(mode):
					mode.revert()
					self.up(to_start=True)
				self.yes_no("Вернуться в начало?", confirmed, default=1)
		elif cmd[1 if cmd.startswith("*") else 0:] in ('clear', 'erase', 'wipe'):
			self.yes_no("Вы уверены, что хотите стереть все свидетельства былого величия?", lambda mode: self.erase(mode, reverts=1), default=1)
		else:
			return super().do_handle_command(cmd)
		return True

	def down(self, to_end=False):
		self.offset = self.count if to_end else check(self.offset_dn, self.offset_dn is not None, "offset_dn")

	def up(self, to_start=False):
		self.offset = 0 if to_start else check(self.offset_up, self.offset_up is not None, "offset_up")

	def describe_fights(self, rec, width):
		def build(cut):
			right = (len(rec.fights) - cut) // 2
			left = len(rec.fights) - cut - right

			def fights_pieces(fights):
				return (fight.mark if fight else "--" for fight in fights)
			left_pieces = fights_pieces(rec.fights[:left])
			ellipsis_pieces = ("(...)",) if cut else ()
			right_pieces = fights_pieces(rec.fights[len(rec.fights)-right:])
			return " ".join(piece for pieces in (left_pieces, ellipsis_pieces, right_pieces) for piece in pieces)

		# TODO: бинарный поиск...
		cut = 0
		while True:
			desc = build(cut)
			if len(desc) <= width or cut >= len(rec.fights): return desc
			cut += 1

	def erase(self, mode, reverts):
		self.session.HoF.close()
		try:
			Game.remove_from_save_folder(self.session.HoF.filename)
		except Exception as e:
			mode.more(exception_msg(e)).reverts(reverts)
			return
		self.failed = self.corrupted = None
		mode.more("Мемориал стёрт.").reverts(reverts)

	def quit(self):
		if self.then: self.then(self)
		else: self.revert()

class InvisibleFighters(Mode):
	prev_mode = True
	do_prompt = False
	do_cls = False

	def __init__(self, extra_reverts=0):
		super().__init__()
		self.extra_reverts, self.proceed = extra_reverts, False

	def do_process(self):
		if self.proceed: return
		self.proceed = True

		class externals:
			nouns, adjectives = tuple(tuple(cap_first(split_name_opts(item)[0].rstrip('-')) for item in items) for items in lang_packs('names', 'adjs'))
			save_folder = 'invisible_fighters'

		try:
			Game.ensure_save_folder()
			try:
				old_wd = os.getcwd()
				os.chdir(Game.SAVE_FOLDER)
				try:
					cls(); self.session.cls_once()
					exec(compile(self.src(), "invisible_fighters.py", 'exec'), {'EXTERNAL': externals, 'input': input, 'print': print, 'quit': sys.exit})
				except InputInterrupt:
					sys.exit()
				except SystemExit:
					pass
				finally:
					os.chdir(old_wd)
			finally:
				Game.remove_from_save_folder(path.join(Game.SAVE_FOLDER, externals.save_folder), mode='dir', throw=False)
		except Exception as e:
			self.more(exception_msg(e)).reverts(1 + self.extra_reverts)
		else:
			self.revert(1 + self.extra_reverts)

	# Изменения:
	# — -1 к ширине консоли для целей выравнивания.
	# — имя папки с сохранениями (не полное) задаётся извне (EXTERNAL.save_folder), а перед exec рабочий каталог меняется на её родителя Game.SAVE_FOLDER.
	# — из имён сохранений отфильтровываются слэши (т. к. они совпадают с именами файлов, и, например, ..\ приведёт к плохим вещам).
	# — существительные и прилагательные переиспользуются из Noun как EXTERNAL.nouns, EXTERNAL.adjectives.
	@staticmethod
	def src(): return unpack_str("𒃠䬧鉰䔀㖈㳼𦳘䧏荍䂗䅳𤏵㗢𠄩畘嚩𢳮澻𦩼肂䝾𥲜隀願𥬿顲𠫓勵𣱌籙𥮢珠閣𨔀骧樕ꈢ𤫋渪𤰉傞郂㮎𦏼𡜵㻙汼𢐤僻鄭䮵𠵞訢𥴦𣻜𣰮𦊸䗗𥻭𣍓𣽪𨓼婄拷𨇞䛠𦋲𧈥"
	"秉媩罪䪕䰰衞濳詫𤮜睿𧶆㝦氆𣤍𣠍𦼳㑕鱚𓊏𥐪𣾊鈞𢑀薯𥧞著倁𧏃𤵔𓄫𢧼𧏛潔𡟆𥝆糆𠃋早櫫𡢳𢎢跄鮪𥞟𤒵𧡲𢝁幆𠉞𔐼𧃥𥒝楘叇淴𠄔依𒁥煂𢈚䄔祋糢𤺫𧕱虋剐暚𠮡𧓤硙醿瑎㠺𣪘𥜣塖樊𧎿𡈓𣠭𤧺嘙𒊋哞𒋛𨇦𦷍𦓶𠘐㻵垫㾳篨𦺁𣃯𦎲"
	"嫄𡅨𥯓𣝬𡆫厯𧟇𦁋伿醳弘𦕑𠉖𦻗𥓃調𨈣𓅰𥌺𣮛𦪡䑄𧔆𢹤𦬧𦜊𣊜𥝸𠄴𦓦𣦻歰炅㫄𦆞𦻇𦣮腹躭徴㰹𐙋𔖧𡸑阝芏慓𤝦𧙣緵𢽙𦳒𧇐𢫼𣮄𠚗堥蒃𧺟𠓰𥘍搅𤰴𥶄𦔻𨌳銩𡌒㡲𢹯払𤂛㩩𢻹𢕜𣂣脙漩𥙙㰫倸𥗱䙉爺𠳼𨑞欨𦆛默𧱐𣡊𣐬挞䙩𖠻甤䬘"
	"𢟚䂞𣚇𠣷𥻂𠠚梄𣊯腼枪𥢮𤘀𔔃𣥄𠈑𣊭𠿽㑋瑖𤡆豼埆㼈𥅌耢楠𦻤嗺倓𡚕衩𥴘𤙒𤙕𣥅𣈾𠅌㲒㮆䛃𠌘繎𧄌𧻫𒂗𢴋胙𧛈𒀳𧟤珻𢫱邠曇𤼿䅁𢺨𦗷𢨠𒁱𠇵𣊗𣚽𢈋鸲攃筩德㗓𣴛𥴽𦬡𦶒氁𤜎𦪠姈暗𤘠𣰔𤵧𢟸𤮇挄㭖导盱拢骽𡵧𤲍𡳠𠡚𢓿𢁑𤺪试"
	"韢𠨘𢠆訋𢙐𧗩𣒀𦗠掼𠴞𧌟镢金𣌄𠡤ꎖ爌𡍗嫭𧴊谵𤇋侮𢩘𤋙𢈻𡟚䭏𤹩轀𧡘搟㻶𠛻𡣼𡠂𢳖𣟬嘴𥺁𢏕䝍鰧𦐺䤖𧺦𥆕谷𤯝𤈨𠚠㶲鋘𢮵𤤧蘖䕋𥋕𡢘喬𣶄𣗆𐘷𠦒麬𡧎ꕞ堐𧓍𢧸𠊱棇𡭊絊怡𥪃鍊壧𤵩㵺阈西痧詌𣜽𠈯漕誜𤄲𣜃𡢒㐕𦫤棂𤺢𥪩𣓒"
	"喑𦐂𢆗昁𦁋𠶧𡓁䳊䧸袃𧉚𥛦杗垭㺋䭚𥫪𣞥𠁱𦄞瀜𤹮𡈫𠳄𠋞𧨽𥸥跻绁𡟠䭄瓲𨇘𢃐澆𣵐ꈧ磦𡓏𧶔𠜽㤰𧉣𨓠𣁡𧗠㮪壑𦯤𐘹釳𦂇𓍐𒇫𡘸𥓀綅埁镄𠇳嘢𠣬溾𦓳𔗣䊑𠇳𤬗𣙵鱺𣕵𣪮㚂陊𥌨𢔟䭭𧼛𥯆壳𒅗柩㛴慪𣁬洁䖝𤚒𐚧𢠆𣙅𤚨𦿥綞𦳠璯𢜚"
	"𡽆䙳睑𓇢剽𤧶䳨傀䬣𔓭𡐆𡚎璷𨕄聝𡙆桮勣𠼰𡂓溆𠎏𤉠𧇣𥖶𨕂嘧𤪞雷𦕲亿䎦𣞟𦁴毠𣤠箎煀𣷖𣝯㭵嫴𧈜踅怇歜𥉮𠢧拻䦞甙𡘺鉡㖨𢶴𡎙䅤爏𥪲腒驮焨ꋋ𡽤㿩僚㾭𣊻𣩃䗒蚵𧧡𢂕𠖔醉𣪈槴鮢𠞁𢊽ꋏ𡇶𧃨䊧蹐𧵼𓃡𢇶漅𖡵糸螈𣤝㺋坎𦮜逫"
	"𠗁𣂤弣𧽣治嶇𧓽𐙴𧳶𡄳回𥸇𦖶投𨃅𦔖𦪟𥚮𥍚𥞊㹹㖛𣪷𡳨袹駜乺𡒠𨅝㴒奾𢟐𥿏𒃞𨒊𠂂䟴𡙍𡘱𣣷𢂥𧂞賻𧎹𦜱穕䣻暶搖笟㸷斵老痞𣚝𦫏𢒌𣀹鏿臵㷢𣾕𡏃顭婫𤞓垴蹣𧓧𥇤嬸㼲幋𠅃𠩿磤㠼䦪𡕦𦡺𥡋𣳔䙯𧍏𡝸禤𐛖漽𤂽瑀𒂛𢁞𤟗鄾䚈𧲨ꖨ"
	"𣐅𧼠𠘌瑝醦𧰪𤵶𠀄儚且𤸫𧟑災𥧐𢺩𨈧麳𤘂𔗛諾鱴𥩭𧢳ꗢ亽𐘿顢儃𣁠𠥭𨖶𓇃𦒔瓗𧢟荪𣩄𢸎𢺃𦓭朑𡀩䙂𤂂𦮸懒𡩥𢨿锒𦲟ꎤ㖢羹㮄𦗱𦦫槧𧇇𦑰劼𤝕𣈭䚔𣚉矨嫀𣚂鬅䗂𠙯𓌨𤠙𦸕𢹼𧍱玄𔓊𦪘𣛁𠡑𨊺𧙀ꈯ𧇛娐浦𢾞𐙕㴊逝祫葳𦞠𡠄𣂶𤢳𠩹"
	"腱𡫀𢸪詷𥶚𒁵𣤸䍚𠞬𧊩𢌮𡺂鄶ꌣ鄊ꖔ𒊹九𨋔𔑒䓔䑬𥹣䥒䖿顒𡓵藄民颜𤩺𒅞𧙳𧿆卯閺𣱥𦇜𨓪𦮰𡸒𡝵𤒸癵𓊣𠌆𥚽𓊖𠿣絻𣆠𣨾兮彫𠈔𡁣𤅰锛ꈶ𥬫𠞔蒪𧴫𦽡䬈贊𨖳灨奉楐𐛡畫趆𡃮䣗亭𢚑埕𡜆𣟺𥲑𤍊荾苰𠂹𡽢娞𠄎𦑰𨂮𣺧㶮䨰𥌼𧑛𖡀𣰻"
	"𥢿瓸樹𤑽蚛𣺺娥汒𒆶䌖脚虢𠍻一𠥡𠪍爝𡍌𢎚𦈓𧸹𦆖蘵𢌪𡎕僿𣳉誜𣚹𠳴𡓤𢔪𦞀鮂㷘塛𤳯紬啮𣢓𠀻𥐚𠧠弩𦄝𥬆姇𢧭𢫑𧈭𧂜𧊂𡒑𠜙𣟧𢱟𨊱𨅩𠶱𥇉𧁆𥸙𣐀𧽔辋説𢇬𥣭茈𣫏帓𧆋𧒅𣈹䣴邙元𠁩𤑼瞮雫𧨥㲂𢋣挃𒉛辉𧢴刑䪧𥸀𓊊軠𣏮𢝟𤂯噙"
	"𦪩𦁙𥴄垅𤟬𒄲悆䳹𠸿𢀜𡲊𨉺埘𔐌𠜋𢇷钦𥙇𢍇𡋒𠚀𦅺秸𦖷鰷𧎚製𓂴𦂰𧚵𧝧㵮𣱵𖦫𣢻𓊊ꏹ辙𠮠𨑝㔶祙𠠪稲𣛽獒𡣓妕𣪷䗨㼌𨖷𒉇㔅𦠟𓉻𥿉𦛛𦦩𠚑𡩅𣹦潇𣁦𒉖髪勖𔕁𧜑𠂑𡈓艴詥𡜸髹癘𤯂旷𢑛𢎦𤧋𥨌𠹿俍嫜𠬢𧍐𧜺贵禶爊朓贒𡑢褟𨑩𧌅"
	"鹾嫾鰁𣂺𧬞偑昈泞𣯫𦮡𤲻𡊝㜡迴𠺀㮢𢣊殠𡸌䨰畤𒇬𧖐帬聸𣬃𤢟㿏𦃨𣅧𧥾𡘠䬑塽𒆐𠴵秬𤘇𦜿䬜詤虻绤𦔲衎㬯𤮦爾𤇬ꊷ萸蘡嫝牄铤𥩏𤐵炵𥁗𤉑𥕁𢼂駷㽜𥜻轨藑𥉋䘅蔝𤛙鎯𥶻𢺫歘崠掆𧳁𥁘匋䍗𥖲巚䘭㪯𓏾璽鮂礖㶥𧥶𣱼𒄔魿権𢽷𠂈"
	"籶俢𨐯𐚏𠄣赬𦿖𢞖𡾚嚝性𢪔澣瘰佄𠋾𓏆𦓽𦭰㑙䩣䩟𧂣𤦇𦐭穚𦘼𡺸懹嘊鋅𧂭䢮腨蹔𥗠ꍲ𢦠𤞧镺抭𠥸氂𓆚𠪲𣠅魀那䱒䱭𨐤粄𦁠𡫠𧵒𤱲𣀦𡸖䭰𥂭卂𣇅𥣱雖慘𦲇䒒𧬽𧷗ꆎ䭺𥙛𥀕靫𠽩㣪𥯃儉椾鳶𠲅𡓣絃霝澴𥋫䲐竤𓁃𢥾𦱪鈹𡚀辡𡉫湃𡑎"
	"钎鏣纞䧑䏀餘汨烐庸翜𥳐婢𧳙㴮垕𤪪諹𖠖𨈍𢀦硧𦯹㹰赕腫𠣒𠓏𠔕𤢜㶼阊䰈𦝣𖡢𠾮𧅇𠶂𦴎𢄦𣠃𧧦䙯恷𥤫𥠋寥吿𦤾夈𢨹令𠅋𦙂𡬣𡜪燌曌𖣠狂盞𢩋𣨙𦮸𢯚𧳏𣇅𡧍𣓝𠊍𓏴㬥䃁𢘅𢪊𒁃䮓𧹼𣑳𤳮𢍶𣻶䱎䮵𒁯𧾩筗𡘓𤧣𢝿𡽖㬎䙽𥔴印甹𣓴𦿺"
	"顚𦣎𣹉諹𧙉𣨨𨂜𥖆𧆏㣈䳩惙𠘢𣝷朿𡃧𤊰𦯟躽无䄣𧇯觰凘𤅧憏娙ꌛ𠍕化畄挲㿿𡟼恡瑤粚猗𒃚矾经瓝𒂶𣙥𢀼偋𢝹㞝频雿𡗣𡾒𦨥𦼤鲍𠎪𤲻𡶱𣅧俬𔑬㹧𦩞社聀柶蔿𠙉𧙎𤤰嵍珱褮腊𣳟𨊱𤽱茀遴𤡕𖢶𥛇𦆙络𠥙袉𨖺𣕱𢰹𤽧㜼𥂓狤鍠讳𠄄𡌐"
	"㽥蟩𠠳𡛭𢹨𢥰譍玲𢛲𧠴𡎉浬顦䗻𥲶皦𧅞鲛𠘁𡝗𦚍𧴵靔𤶶𥐀𧹇䑂𧏛䦾皊𥲔轔𧳲藖𠞅𡮷𣦺姭𒅻𢤡𥵡𣖫闡𤿎瑬𓊫𣻯鵡𧗸ꉶ謜𡺋𤨼𢑠𡄸𥜥𤠃𥛚庳櫎𡭯䌀𤈱𤺆㑍𣬍纝𣕂绫𢌝𢎗患𤦦𡬾𠤅䰂潣ꕩ𒄐𣆗𠯒𣪹𦿊𡫫䌶鐅𢳤嶑𡹛𠌆錌𠑑鸹𠸳姪𦅻𔖋"
	"𢘥𣯡則胱𡭻𡠘𣛀趛𣗷䫗𠨃㢢𠜤𥫜侥雎𦹮𥶞渼䘐䛳𥐭𡋨㪉𡪥𨐺𡖺飰籗瞕𡬵𣛋𧚒𦍭駓蓻𤻾阢𦬬𠂨轋磩隴𠈫㦬㨝𥘥𦜬貭䛭𡑍筼𡭉𨂚𣊃坕ꌬ㵻𤠸𦦁𡔄𧉭䌠㔃𡒌𢡎墜𥏾𣙪𥛲𣎉蠑𒄕𔗪𣌶㛕𡠶蚣𠎶𨋝𡨍𢪽䬗𖧋釉𨗛𠉅𨋈𥓉𠒰𠈺𢢀𠶍挌𥴽𒃏𥌢"
	"䛭𡿘𦪛𤔼𥮤殒𡑪堃姦𡖩峍𠉣𢲟薛片𦈕𤈶𨔟𤥕𦵯𢗿攏𡙻笓𨏠𦼮𦵪𧿼𡾕𖤜灔希詴尧𠮊𧣐𠛡歑餲𖤄錰菴𥙱𧽨𖦷𥳥𡠄𡪁墴𧙪𣫵𤰀𡩮𒉕士埲亠𧠽坺𣁐㦂𡞄𤰘䲅弽𡛏㱊𡐙嶐㢇𤳩劺𨂧𦤹𦕼𥉏䊌䘽𢐸𥧶𧦮凥𓀿峺𔑙鋘𠪾𤪐巚橫髵𢜲蒝欸䏞𥗪㶫"
	"𣆊𥻢烔𤄭㚑𡷄䮡閯𤢮𓆄𣟎虰𧕐䂖㘘𧔇𡇙𧂩𥅱䲗媷𠐶餰𦹙𧒩𦝳榥𒆊𥏅扉𡷎𠆴瞸𦯮𤶞制𐚷𠦥𦉾㪖𢁳𠂔圲袐𥚌糎壗𥢣豻𥋁𧝤𢶒𦘨𣑇𥌩亃𠴚𔖑罠帡𓁭𠘉卵衃𦹈ꇎ𢡌核𥞸棱𠭠𠠲𥋁𥮤𥁓葜𤻡𠻊櫞鶢𢔴㱈𤣞嘕𣰷䅕𦼩蓄𡏍𡱈䫣绳𡠠隙𡁊铧㱍"
	"𢿿ꋸ䢃銙塿𥐕㣬𠃏僘𢼚𤶄𢁥枀棠𠕲𧌁𣚲㞐𨏝歶𦢏𡲀猃𣍼㿹𦚭貗𢗃𡵺𥾷𡂠㞙𥬂𧨆㶾蘩𔖶籷𓊛𤌍棣𢩏𤒜赜𥰇另𤣜𓄦楸㨷𠼔琁𦿑濖𠁓𢤤䕶𦑘㞩娠𠚀湳𨇋劣駳跄炔翰𢱬綩儙𣮛𦰗唜𣝳鶌𨔆ꗛ䅀泮𢅣𡭾悡𡜶焣荟𨓅𣱂砃䙑萻修𢼒𣮤𢟛𣬺𢃎"
	"𡁀晳𤞑𦏷朔鯀苈瘘𣔭𦉹𤔦𧁜㘷𠗷䣕𤏨䬾蟚𣉇鉌麋黪𧸃瑰𣥧𡧈𣊉𡊐處𥾿𥣞媠𠒊𖤡𒂸𤏫乷酎𣔸𣤣𤲾𠇚庶熢𥣷靹𧑁木抡棡𨑧𠍢𠖒𢪗仙𡳘𠧓咬誓𥕬𢴯𠻃瀚𦐖矶𤱢𧩲勞综𡤄𣸜𣜻嚑级𤾘𠤑𠒳𡠡䥵𧄮氻𠓠棨誂𦶜𥩍笡𡳭痌㶔𡲦ꉚ嶦𠞬𠣢𧎴𢧰"
	"椒鏕𠡢𤒽囡錍䢇𓁧挤㣓漛䦊𢞒𤎽怽𧹦𣟒𢾨𐚸縜𡦨铁𧨏楻𠮈扪𡼀簇𤝄𣍗脶娐𥇛䕡㽭𠛺憌𢪻𓋫𠫖𤳧涙𡶄颋獙桼𥖸𦴁曽𧰊隳𤮧餁緪𣸟𣥫𡌜𓌰𧺙畧𣿇𓀇㶩㿨𤦶琭䀆𠜌𧱼𣵝𣑂𤡫𤢽狞鴵𢣭㯥𢟇𠿅𦲜琕𡻠𨌛𤵙𧮦䑶𤨤蕗𥓘烾𦱟寞𡀲𧩷𤨏纖𦒓"
	"𡤭𢿥𧒶𤍐𡧆𦕬𡨷𥕩𥈼菌𣣚薤𤿅垠𒅿乣𧃅𧆿𥹨贕𤲞𤺈𢍝𣰈𣕺断穎𥄜𧝘軨𧧯𨓋𣒻𓉢𥷶䰢𨐸𧃼噆椷𧒞𣕳㟭𢯔𧕮𧔳𦛎綷罕𢮂𡝣𣞝𡫆嵟𔓟鱺𣮅螩篦𦍚萣鉮𡌨𢪁䄐𢺤𧝾稴𤌗𤴘𣣗𦛡鎁𧨞鐼㑣𤦀䫌𦶽𦳔𨐱䌾沷𤼋𢋛驫𠙅懆𠑼𧟘𤤛𣮫诽𣋩𠰐𡑑𤇉"
	"蟙𣏓𤜣椃𦵕𣆳蚎乤𣻟堀䪧𢽤婉垽ꊅ簙𦬔颥肅峛嶕𡿕𢃔纙𢯑𤹢觊𡏀掩𧪂𣹸紳撤𧝖耬噎𣓇𤯅䬟酨𡇩𢻪𡇝ꖬ㐟𣀍𡐾貛幑紺𣌷𧶖饍虭還这禃𨏑ꍫ𦮀𧩇萀𦠷𨗬𡧧𡔒呣𧤙𣘑䐟漳𡛠興𡌄覀𢅙𔖹搈𡥺鏣𠼾幸䱲𧲑蔞𦀮䢉住漹𣶘鉜𡏸𥺹𥤆雇𠼆詼"
	"𥲗𣈡𠈢𨅝𣻔𣐺𓅔䃆𡿄𠑉莖𦤼ꍫ鷬𦅤𣸔𤗉𧠶𦦮𦇯𦨆𢄪鑑𡼀𤜳芯𨀻祝𢥂鯨攃𧥢隻䕞𡥄蔂𦎏𤁫㝼𓌚𤏢䌍𢧧𦂆𠩲𤀦𠅺𤂨𤴌㱳偠𡝒㩠伶𡊂𦻁𨁤𦨒𦾠𥆴𧚕𠝽畃鬄騎㭎𧳾蕬𣓣𦕂𢏥㜘𤅑𥑼殣𨋓斉𓅡𤭙𣰈𡭚哰𣰦𦚽毄件卩别𣲄𖤔䗋𢄤薕凖顩𤜀撔"
	"颛褾枂𤞍𦛣𧾴䀣𠅕磖𤍢鰲𓀨㢪𠁨兤㾅𖡶䓯𠝂𖧌㭚𤏈𤗱錿戰鈄𢢲𥔒䘇敔𥌨𥶔𧿅𦐧𧱑䬎祝𧭱𥳤㷟𨂜ꋎ錪篠㵫𧓖扢腐𡝟䝈𦽌𤊖丅𧩳𔕝䱁袸𠇬𤙅𢟬鱋𢃫轑𦇵㬡𥡲箏秆𤙦ꆜ摮𓎉𠫂𥌳𢍩ꋳ𒉧𨃹迂赦𣈫胝墾𠸁䞘纤𤀁茶𨂪𤄀𡀰糾郲镈𤉷恄𦾤"
	"陜𒊤籑蝏苝皐𠳾𡎌𧖞𢍓𠆜欨𦨎檫𦈢𣷈𠯌𠦎𢒬押镔ꆅ𡐑験镕昡㨕𤊑峨樗𓀮玶㼎𥗔萴祐𦾢呒𥘄ꉴ𧥹搟𧏔㨣𦈜冣䊰𦷪𥡪頻峹𦇥𢇀𤩧𔕳䦢𖠄迠𡹁𢆩𨑬𤱉𔒲蚪𡼊𡱵摨瑧𧤚ꇝ鉔浛䋞罫嫗𢽇仟𔔄圫𐚑㮗𡁂躔𦨴䥩䘹𦜭𥞍𣐕谲𥹝𧾯恛劇𤫌𥇌𧂟"
	"縐讛𐘃𧸲𠰫𥑖𣫋䂅𨉜𣈸鰶鞩菘鹒㣔𢱷𡏗𡨦㬤𣮬嘫𧗰𦜤𤔦𢤖䳪𧢢媺𧼡𣣄𧋱𢷊烹𠰜𧐫䊄兏𐛳𔗙杶耉椺𧔆璱𖡒𣠀䛻𥙦鑗扜𓇄𦜸𣖲𧡭𠞽竓𥜹𥰠𥡮髑𠗄𧼱𢵎𥞢𤢈呚陔𓍭𡶟𤡅𣬼𤦑𡢇𡫹㚎𔕞𤰠𣣴𠗕𡅲𧧤𓉢𢼠ꍶ𖤛𥛅考𡧒𠍼𧝉㰪𣻢䬉𧂆𧆽𠂼毀"
	"苨𤉻𦅆柮箟𢊉𢖴ꄂ𦭫痹昩𢠢鰫䔦𣮑界𓉼𢶓颚僵𔑜𤧿𡴝醮钺𠩏𨊯𖤳洙滐𤡞獽䍹𦯔搯𦹣俎䅥珄踴𤡨橻䫿𥊌𣡶淐𢣒𠰸剕綔𦢱綽曱涍𧝩𡷬鋹𧄘𥰥弜窫𢉢𖧰𧷿鰅𧑏ꋴ𦪼瀠𣂦㦦𦴧𠾣𠞸𡰎徯䝛𧐣䤇𧛸𤍷䢩𡗓𦽫𠘸噔𔕃穒𣗯𤭿𣣏鸡圼𦪤𥱌憂伄"
	"萐𣒤𣝉舡馞紕䑣㠻鏼誻𧝸𧚹瑽䐞𦒒语𣲇螡綛𡠏菁艄𡺉㧋ꈐ觜𠑜𠽈䜔𥥕𥢊𢔚𦚸剐偊静為𨎲𦻐㣏鲇冽獶𡜿𠇄潣𦭐𦪣𤄦辀隅𤴤𧬌𠷾嗜嫯𡳿䦈璮𡆹𖥍𣺡𥲅𨁘𣯒杆䱩ꖙ饻𣻰𠰼呕𓊃𡪮弫𦣰𦥹䉆淥𢕋紘𠗱𣶴𓊜䓴倗䯖𧱍𔔴𧱹𣟠𠬝䙡𣽩𢼂𥕚搜"
	"𨂷𠹺振𥱍𧻰𦴶㹉𠉤𦠈盰𦎙𢠂𐚵仰煆𣋲図𦄅篼𠎇䲝𤐦𣔥𡤦𠃥㑡")

class More(Mode):
	do_prompt = False
	prev_mode = True

	def __init__(self, msg, do_cls=False, markdown=False):
		super().__init__()
		self.msg = msg
		self.do_cls, self.markdown = do_cls, markdown
		self._reverts = 0
		self.continuation = None

	def do_render(self, lines, cmds):
		lines.append(wrap((self.msg() if callable(self.msg) else self.msg) + ("" if self.input_comes else ""), self.safe_term_width, markdown=self.markdown))

	def do_handle_command(self, cmd):
		mode = self.revert(1 + self._reverts)
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
	def __init__(self, msg, callback, strip_input=True, casefold_input=True, do_cls=False):
		super().__init__(msg, do_cls)
		self.callback, self.strip_input, self.casefold_input = callback, strip_input, casefold_input

	def do_handle_command(self, cmd):
		if self.strip_input: cmd = cmd.strip()
		if self.casefold_input: cmd = cmd.casefold()
		self.callback(cmd, self)
		return True
	input_comes = True

class YesNo(Prompt):
	def __init__(self, msg, yes_cb, *, no_cb=None, default=0, extra_reverts=0, question_id=None):
		super().__init__(lambda: msg + " ({}) ".format(self.answers()), self.handle_answer)
		self.yes_cb, self.no_cb, self.default, self.extra_reverts, self.question_id = yes_cb, no_cb, default, extra_reverts, question_id

	def answers(self):
		if self.question_id:
			return self.session.globals.highlight_answer(self.question_id, default=self.default)
		else:
			return highlight_variant("y/n", self.default)

	def handle_answer(self, input, mode):
		if self.question_id:
			yes = self.session.globals.judge_answer(self.question_id, input, self.default) == 0
		else:
			yes = 'yes'.startswith(input) if input else self.default == 0

		if yes:
			self.yes_cb(mode)
		else:
			if self.no_cb: self.no_cb(mode)
			else: self.revert(1 + self.extra_reverts)

class BadDataError(Exception): pass
class BadVersionError(BadDataError): pass

# Прогресс игрока и информация о сейве.
class Game:
	SAVE_FOLDER, SAVE_SUFFIX = path.join(path.dirname(sys.executable if getattr(sys, 'frozen', False) else __file__), 'save'), ".sav"
	SAVE_FILE_BASE_NAME_DONT_TOUCH = '\x00/' # save_file_base_name нужна для обнаружения необходимости смены имени, это — маркер «не менять»
	MAGIC = b'H,/m seX}Y', 2942819, 127
	PLAYER_SQUAD = 0
	MONSTER_SQUAD = 1

	def __init__(self):
		self.character_uid  = None # Для отслеживания сохранений с одинаковыми именами персонажей.
		self.full_save_path = None
		self.rel_save_path  = None # используется как ключ в PreviewsList и при сравнении известных превью с результатами os.scandir().
		                           # Весь этот цирк с full/rel обусловлен тем, что я иррационально не хочу дёргать path.basename(full_save_path).
		self.save_file_base_name = None # это НЕ имя файла, это его «основа» (с именем персонажа, etc.)
		                                # по несоответствию base_filename() обнаруживается необходимость переключиться на новый файл
		self.gold           = 0
		self.player         = None
		self.next_level     = None
		self.god_mode       = False
		self.completed_fights = []
		self.hibernated_arena = None # сюда попадают враги, если игрок сбежал с арены. В следующий раз он встретится с ними снова, слегка подлечившимися.
		self.performance    = None # статистика по текущем бою — сохраняется между отступлениями, но стирается после победы и подведения итогов.

	def enough_gold_for(self, cost):
		return self.gold >= cost

	def give_gold(self, amount):
		self.gold += amount

	def take_gold(self, amount, *, allow_debt=False):
		if not allow_debt: check(self.enough_gold_for(amount), "not enough gold")
		self.gold -= amount

	def gold_str(self, gold=None):
		if gold is None: gold = self.gold
		return ('-' if gold < 0 else '') + f'${abs(gold)}'

	@staticmethod
	def corrupted(what=None):
		return BadDataError("Сохранение повреждено{0}.".format(f" ({what})" if what else ""))

	# Превью для быстрой загрузки. Сохранение состоит из Preview.to_list() и Complement.to_list().
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
			self.weapon_name    = game and game.player.weapon and str(game.player.weapon.name)
			self.weapon_level   = game and game.player.weapon and game.player.weapon.xl
			self.weapon_next    = game and game.player.weapon and game.player.weapon.next_percentage()
			self.gold           = game and game.gold
			self.next_level     = game and game.next_level
			self.timestamp      = game and localtime()
			self.god_mode       = game and game.god_mode
			self.compress       = compress

		store_fields = [('character_uid', int), ('order_key', int),
			('player_name', bytes), ('player_level', int), ('player_next', (int, type(None))),
			('weapon_name', (bytes, type(None))), ('weapon_level', (int, type(None))), ('weapon_next', (int, type(None))),
			('gold', int), ('next_level', int), ('timestamp', int)]
		extra_flags = ['compress', 'god_mode']

		def to_list(self):
			check(self.order_key, self.order_key is not None, "order_key?!")
			# order_key начинается со второго бита, в младших хранятся extra_flags:
			# нулевой означает, используется ли сжатие (возможность его выключить поддерживается, потому что мне иногда интересно посмотреть, ЧО ТАМ)
			# первый хранит флаг god mode
			flag_bits = functools.reduce(or_, (int(value) << index for index, (_name, value) in enumerate(getattrs(self, Game.Preview.extra_flags))))

			return [save_version] + [
				int(mktime(value)) if field == 'timestamp' else # секундной точности достаточно
				self.encode_name(value) if field in ('player_name', 'weapon_name') else # не светить непосредственно
				value << len(Game.Preview.extra_flags) | flag_bits if field == 'order_key' else
				value
				for field, value in getattrs(self, map(itemgetter(0), self.store_fields))]

		def encode_name(self, name):
			return name and pcgxor(name.encode())

		@staticmethod
		def from_list(d):
			pv = Game.Preview()
			if not isinstance(d, list) or len(d) < 1 or not isinstance(d[0], int):
				raise Game.corrupted("preview")

			if d[0] != save_version or len(d) != 1 + len(pv.store_fields):
				raise BadVersionError("Несовместимая версия сохранения.")  # хотя можно и совместимость устроить... даже просто не проверять

			for index, (field, field_types) in enumerate(pv.store_fields, 1):
				value = d[index]
				if not isinstance(value, field_types): raise Game.corrupted(f"{field}: {type(value)}")
				elif field == 'timestamp': value = localtime(value)
				elif field in ('player_name', 'weapon_name'): value = value and pcgxor(value).decode()
				elif field == 'order_key':
					for i, flag in enumerate(Game.Preview.extra_flags): setattr(pv, flag, bool(value & 1<<i))
					value >>= len(Game.Preview.extra_flags)
				setattr(pv, field, value)
			return pv

	# Complement устроено аналогично Preview, содержит дополнение Preview до полного состояния игры.
	class Complement:
		def __init__(self, game=None):
			self.player = game and game.player
			self.completed_fights = game and game.completed_fights
			self.hibernated_arena = game and game.hibernated_arena
			self.performance = game and game.performance

		store_fields = None # заполняется после определения Game, <Game.Complement.store_fields after game definition>

		def to_list(self):
			return [
				[fight and fight.pack() for fight in value] if field == 'completed_fights' else
				value
				for field, value in getattrs(self, map(itemgetter(0), self.store_fields))]

		@staticmethod
		def from_list(d):
			complement = Game.Complement()
			if not isinstance(d, list) or len(d) != len(complement.store_fields):
				raise Game.corrupted("complement")

			for index, (field, field_types) in enumerate(complement.store_fields):
				value = d[index]
				if not isinstance(value, field_types): raise Game.corrupted(f"{field}: {type(value)}")
				elif field == 'completed_fights': complement.completed_fights = [fight_pack and Game.CompletedFight.unpack(fight_pack) for fight_pack in value]
				else: setattr(complement, field, value)
			return complement

	# Поля Game, попадающие в preview/complement в неизменном виде.
	preview_verbatim = 'character_uid', 'gold', 'next_level', 'god_mode'
	complement_verbatim = 'player', 'completed_fights', 'hibernated_arena', 'performance'

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

		return "{pn} Lv.{pl}{wpn} D{nextl}".format(
			pn=sanitize(self.player.name) or "Игрок", pl=self.player.xl,
			wpn=" ({wn} Lv.{wl})".format(wn=sanitize(self.player.weapon.name) or "автомат", wl=self.player.weapon.xl) if self.player.weapon else "",
			nextl=self.next_level)

	@staticmethod
	def scan_saves():
		with suppress(OSError): # Есть смысл всё, кроме FileNotFoundError, выбрасывать наружу и как-нибудь обрабатывать в терминах Session, но мне лень.
		                        # (Пример: если заранее создать ФАЙЛ save, вылетит NotADirectoryError.)
			yield from (entry.name for entry in os.scandir(Game.SAVE_FOLDER) if entry.is_file and entry.name.endswith(Game.SAVE_SUFFIX))

	def open_new_file(self):
		base = self.base_filename()
		# Нельзя искать подходящее имя файла линейно без ограничения: https://randomascii.wordpress.com/2018/10/15/making-windows-slower-part-2-process-creation/.
		for num in range(1, 100):
			rel_path  = base + (f" ({num})" if num > 1 else "") + Game.SAVE_SUFFIX
			full_path = path.join(self.SAVE_FOLDER, rel_path)
			with suppress(FileExistsError): return open(full_path, 'x+b'), full_path, rel_path, base
		raise RuntimeError(f"Слишком много сохранений вида \"{base + Game.SAVE_SUFFIX}\".")

	@staticmethod
	def remove_from_save_folder(path, throw=True, mode='file'):
		try:
			(os.remove if mode == 'file' else os.rmdir if mode == 'dir' else impossible(mode, "mode"))(path)
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
				mode = mode.more("Сохранение удалено.").reverts(extra_reverts)
				if then: mode.then(lambda mode: then(True, mode))
			elif then: then(True, mode)
			return True
		except Exception as e:
			mode = mode.more("Не удалось удалить сохранение.\n" + exception_msg(e)).reverts(extra_reverts)
			if then: mode.then(lambda mode: then(False, mode))

	def will_autosave_to_new_file(self):
		return self.save_file_base_name != Game.SAVE_FILE_BASE_NAME_DONT_TOUCH and self.save_file_base_name != self.base_filename()

	@staticmethod
	def ensure_save_folder():
		with suppress(FileExistsError):
			os.mkdir(Game.SAVE_FOLDER)

	def save(self, session, to_new_file=False, compress=True):
		self.ensure_save_folder()

		# Придумать character_uid, если его ещё нет.
		# Пока что единственное, для чего он нужен — суффиксы вида «-2» на экране загрузки для разных персонажей с одинаковыми именами.
		if self.character_uid is None:
			self.character_uid = self.generate_character_uid(session)

		# order_key — поле, по которому сортируются превью на экране загрузки.
		# Файл свеженачатой игры будет вверху всех остальных, загруженной — останется на прежнем месте.
		order_key = session.previews.choose_order_key(not to_new_file and self.rel_save_path)

		# Записать сразу в новый файл, если:
		# — это явно требуется (to_new_file=True)
		# -или-
		# — используется семантика автосохранения (to_new_file=False), но старого файла не было или игра хочет его сменить всё равно.
		#   Логика этого решения вынесена в will_autosave_to_new_file, т. к. интересна кое-кому извне.
		if to_new_file or self.will_autosave_to_new_file():
			file, full_path, rel_path, base = self.open_new_file()
			try:
				with file:
					preview = self.save_to(file, order_key, compress=compress)

				# Если это автосохранение, удалить старый файл.
				if not to_new_file and self.full_save_path:
					Game.remove_from_save_folder(self.full_save_path, throw=False)

					# Но пошаманить над превью так, чтобы оно осталось на месте — с корректными order_key разницы не будет,
					# но если они сбились, это, в отличие от .note_remove + .note_add, оставит превью в старом месте списка.
					session.previews.note_update(self.full_save_path, self.rel_save_path, preview, full_path, rel_path)
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
			tmp_fd, tmp_path = tempfile.mkstemp(suffix=".tmp", prefix=self.base_filename(), dir=self.SAVE_FOLDER)
			# Не знаю, как с ними правильно работать, так что перестрахуюсь.
			try:
				with open(tmp_fd, 'wb') as file:
					tmp_fd = 'CLOSED'
					preview = self.save_to(file, order_key, compress=compress)
				os.replace(tmp_path, self.full_save_path)
				session.previews.note_update(self.full_save_path, self.rel_save_path, preview)
			except:
				if tmp_fd != 'CLOSED': os.close(tmp_fd)
				Game.remove_from_save_folder(tmp_path, throw=False)
				raise

	def generate_character_uid(self, session):
		session.previews.update()
		for _tryIndex in range(10):
			character_uid = randrange(2**16)
			# Коллизии не критичны (см. зачем вообще нужен character_uid), тем не менее, по возможности хотелось бы их избегать.
			if all(item.preview.character_uid != character_uid for item in session.previews.items if item.preview): return character_uid
		else:
			# Фоллбэк, гарантированно не совпадающий ни с одним из сейвов, ценой неограниченности сверху.
			return max(item.preview.character_uid for item in session.previews.items if item.preview) + 1 + randrange(2**16)

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

	@staticmethod
	def load_complement(file):
		return Game.Complement.from_list(pickle.load(file))

	@staticmethod
	def from_preview_and_complement(preview, complement, full_save_path, rel_save_path):
		g = Game()
		# Некоторые поля preview и complement напрямую соответствуют полям Game.
		for container, fields in ((preview, Game.preview_verbatim), (complement, Game.complement_verbatim)):
			setattrs(g, getattrs(container, fields))

		g.full_save_path, g.rel_save_path = full_save_path, rel_save_path
		# если имя файла сформировано по тем же правилам, что сформировало бы само приложение...
		if re.fullmatch(re.escape(g.base_filename()) + r"( \(\d+\))?", path.splitext(path.basename(g.rel_save_path))[0]):
			g.save_file_base_name = g.base_filename() # ...то считать, что так и есть, и менять его как обычно
		else:
			# иначе пользователь переименовал файл (или изменились правила формирования имени, но этот случай опустим)
			# имя этого файла не будет меняться автоматически
			g.save_file_base_name = Game.SAVE_FILE_BASE_NAME_DONT_TOUCH
		return g

	def save_to(self, file, order_key, compress=True):
		preview = Game.Preview(game=self, order_key=order_key, compress=compress)
		pickle_dump(preview.to_list(), file)
		file.write(pcgxor(*Game.MAGIC))

		complement = Game.Complement(game=self)
		with lzma.open(file, 'wb', **LZMA_OPTIONS) if compress else nullcontext(file) as cf:
			pickle_dump(complement.to_list(), cf)
		return preview

	@staticmethod
	def load(file, full_save_path, rel_save_path):
		# preview загружается с нуля, чтобы нельзя было читерить на несоответствии preview и complement, заменяя физический сейв при открытом экране загрузки :P
		# (как вариант, вообще не использовать preview на этом этапе, дублируя всю нужную информацию в complement)
		preview = Game.load_preview(file)
		if file.read(len(Game.MAGIC[0])) != pcgxor(*Game.MAGIC):
			raise Game.corrupted('magic')

		with lzma.open(file, 'rb', **LZMA_OPTIONS) if preview.compress else nullcontext(file) as cf:
			complement = Game.load_complement(cf)
		return Game.from_preview_and_complement(preview, complement, full_save_path, rel_save_path)

	@staticmethod
	def load_nothrow(pv, mode, on_fail=lambda mode: None, more_on_success=True):
		assert isinstance(pv, PreviewsList.Item)
		try:
			with open(pv.full_save_path, 'rb') as f:
				game = Game.load(f, pv.full_save_path, pv.rel_save_path)
		except Exception as e:
			mode.session.previews.force_bad(pv, e)
			mode.more("Не удалось загрузить игру.\n" + exception_msg(e)).then(lambda mode: on_fail(mode))
		else:
			then = lambda mode: mode.switch_to(Respite(game))
			if more_on_success: mode.more("Загрузка...").then(then)
			else: then(mode)

	def handle_command(self, input, mode):
		if self.god_mode:
			handled = True
			if input == '*forget':
				if self.hibernated_arena:
					self.forget_arena()
					mode.more("Арена забыта.")
				else:
					mode.more("Запомненной арены нет.")
			else:
				handled = False
			if handled: return True

		if input == '*perf':
			mode.more(str(self.performance) if self.performance else "Информации о бое нет.")
		elif len(input) == 24 and digest(input) == '𦊔揷憒𥶢𐚲𥽕䋮㰈諃瘱𣒋灛𨈜䊞擴𧦂':
			was_in_god_mode, self.god_mode = self.god_mode, True
			mode.more("Активирован режим отладки." if not was_in_god_mode else "Вы уже в режиме отладки.")
		elif len(input) == 15 and digest(input) == '㾮𡋳𧚩𤢢𢌎𢨛𡺿柯阂㤢𠲐騠𡯏㓐𡱕漗':
			was_in_god_mode, self.god_mode = self.god_mode, False
			mode.more("Режим отладки деактивирован." if was_in_god_mode else "Вы не в режиме отладки.")
		else:
			return False
		return True

	def marks(self, lspace=False, rspace=False): # self может быть Preview
		return ((" " if lspace else "") + "*DEBUG*" + (" " if rspace else "")) if self.god_mode else ""

	Grade = namedtuple('Grade', 'mark, verbal_desc, xp_percentage_mod')

	# каждый элемент начинается с минимального рейтинга и помимо него содержит произвольный набор из:
	# — буквенной оценки (сейчас распознаётся как «строка от 1 до 2 символов»)
	# — словесной оценки
	# — модификатора опыта
	grades = (
		(0, 'F', "ужасно!", -.20),
		(15, 'D-', "плохо!", -.15),
		(20, 'D'),
		(30, 'D+', "не очень", -.1),
		(35, 'C-'),
		(40, 'C', "сойдёт", 0),
		(50, 'C+'),
		(55, 'B-', "неплохо", +.1),
		(60, 'B'),
		(70, 'B+', "хорошо", +.15),
		(75, 'A-'),
		(80, 'A', "отлично", +.2),
		(95, 'A+'),
		(100, 'S', "превосходно", +.25))

	@staticmethod
	def grade_for_score(score):
		def search_backwards_for(cond, start_index, err_genitive):
			for grade in reversed(Game.grades[:start_index + 1]):
				for item in grade[1:]:
					if cond(item): return item
			raise RuntimeError(f"Не найдено {err_genitive} для score={score}.")

		grade_index = bisect_right(SequenceMap(Game.grades, lambda mark: mark[0], start=1), score)
		return Game.Grade._make(search_backwards_for(cond, grade_index, err_genitive)
			for cond, err_genitive in (
				(lambda item: isinstance(item, str) and 1 <= len(item) <= 2, "буквенной оценки"),
				(lambda item: isinstance(item, str) and len(item) > 2, "словесной оценки"),
				(lambda item: isinstance(item, Number), "модификатора опыта")))

	class CompletedFight:
		__slots__ = 'score', 'weight'
		def __init__(self, score, weight):
			self.score, self.weight = score, weight

		def pack(self):
			return (self.score, self.weight)

		@classmethod
		def unpack(cls, state):
			return cls(*state)

		def __getstate__(self): raise NotImplementedError("__getstate__")
		def __setstate__(self, state): raise NotImplementedError("__setstate__")

	# Данные, необходимые для подведения итогов текущего боя (оценки + раскидывание опыта между игроком и оружием).
	# Возможно, отложенного — т. е. либо игрок сейчас на арене, либо существует hibernated_arena, и теоретически это можно было бы упихнуть в Arena.
	class Performance:
		__slots__ = 'turns', 'escapes', 'unarmed', 'melee', 'ranged', 'magical', 'starting_hp_percent', 'starting_effective_enemies_xl', 'kiss'

		def __init__(self, game=None, arena=None):
			self.turns   = 0
			self.escapes = [] # список «серьёзностей» побегов — их оценивает Arena.retreat_penalty.
			self.unarmed, self.melee, self.ranged, self.magical = tuple(Arena.DamageContribution() for _index in range(4))
			self.starting_hp_percent = game.player.hp / game.player.mhp if game else 1
			self.starting_effective_enemies_xl = game and arena and arena.effective_enemies_xl(arena.enemies(game.player))
			self.kiss = None

		def __getstate__(self):
			return {name: value for name, value in getattrs(self, self.__slots__) if not (
				name in ('turns', 'escapes', 'unarmed', 'melee', 'ranged', 'magical', 'kiss') and not value
				or name == 'starting_hp_percent' and value == 1)}

		def __setstate__(self, state):
			self.__init__()
			setattrs(self, state)

		def __str__(self):
			nvs = [(name,
				"{:.0%}".format(value) if name == 'starting_hp_percent' else
				"{}".format(round(value, 2)) if name in ('starting_effective_enemies_xl',) else
				"[{}]".format(", ".join("{}".format(round(severeness, 2)) for severeness in value)) if name == 'escapes' else
				value)
				for name, value in getattrs(self, self.__slots__)
					if not (name in ('unarmed', 'melee', 'ranged', 'magical') and not value)]

			pad_not_too_large = max(len(name) for name, _value in nvs if len(name) < 10)
			return "\n".join("{} = {}".format(name.ljust(pad_not_too_large), value) for name, value in nvs) or "Пусто."

	def forget_arena(self):
		self.hibernated_arena = self.performance = None

# <Game.Complement.store_fields after game definition>
Game.Complement.store_fields = (('player', Fighter), ('completed_fights', list), ('hibernated_arena', (Arena, type(None))),
	('performance', (Game.Performance, type(None))))

class GameMode(Mode):
	def __init__(self, game):
		super().__init__()
		self.game, self.player = game, game.player
		self.exec_env = None

	def do_handle_command(self, cmd):
		return self.game.handle_command(cmd, self) or super().do_handle_command(cmd)

class NonCombatMode(GameMode, MessageSink):
	def __init__(self, game):
		GameMode.__init__(self, game)
		MessageSink.__init__(self, game.player, lambda msg: self.do_handle_note(msg))
		self.log = ArenaView.MessageLog()

	def do_activate(self):
		self.player.add_sink(self)

	def do_deactivate(self):
		self.player.remove_sink(self)

	def do_handle_note(self, msg):
		self.log.add(msg)

	def check_for_pending_notes(self, *, extra_reverts=0, maybe=False):
		assert maybe or self.log.something_new, "ожидались сообщения"
		if self.log.something_new:
			self.more("\n".join(self.log.scroll(None, self.safe_term_width))).reverts(extra_reverts)
			assert not self.log.something_new, "неадекватная something_new"
			self.log.clear()
		elif extra_reverts:
			self.session.revert(extra_reverts)

# Экран между боями.
class Respite(NonCombatMode):
	def __init__(self, game):
		super().__init__(game)

	@staticmethod
	def bars_pad(player):
		return " " * (2 + min(len(name) for name in filter(None, (player.name, player.weapon and player.weapon.name))))

	def describe_player(self, player, cmds, pad):
		mp_desc = []
		line = pad + "[name_pad]" + multipad.escape(player.hp_bar()) + "  [cure_verb]"
		if player.hp < player.mhp:
			# Лечение возможно в долг, т. к. если у игрока нет денег — у него и так проблемы.
			# Бесплатно/по сниженной цене лечить нежелательно, чтобы сократить пространство для эксплоитов.
			# Оно остаётся всё равно, в виде нобрейн-решения «если денег впритык, купить апгрейды и уже потом лечиться».
			# Можно запретить покупку апгрейдов при неполном здоровье, или лечение в долг, когда игроку есть что продать, но это как-то не по людски.
			cost = clamp(round((1 - player.hp / player.mhp) * 16 + 0.2 * (player.mhp - player.hp)), 1, 50)
			line += "восстановить: [cost]${0}".format(cost)
			notes = ["heal hp"]
			if not self.game.enough_gold_for(cost): notes.append("в долг")
			line += " [cure_cmd]({})".format(", ".join(notes))

			def add_heal_hp(cost=cost):
				def heal_hp():
					self.game.take_gold(cost, allow_debt=True)
					player.cur_hp = player.mhp
					player.note("Ваши раны исцелены.")
					self.invalidate().check_for_pending_notes()
				cmds.add('heal hp', heal_hp, '?', lambda: self.more("Полностью восстановить очки здоровья."))
			add_heal_hp()
		mp_desc.append(line)

		if player.has_magic():
			def dmp_func(d):
				def modify():
					player.cur_mp = clamp(player.cur_mp + d, 0, player.mmp)
					return modify
				return modify
			cmds.add('mp+', dmp_func(+1))
			cmds.add('mp-', dmp_func(-1))

			line = "[name_pad]" + multipad.escape(player.mp_bar())
			if player.mp < player.mmp:
				cost = clamp(round((1 - player.mp / player.mmp) * 45 + 0.9 * (player.mmp - player.mp)), 1, 70)
				line += " [cure_verb]восстановить: [cost]${0}".format(cost)
				if self.game.enough_gold_for(cost):
					line += " [cure_cmd](heal mp)"
					def add_heal_mp(cost=cost):
						def heal_mp():
							self.game.take_gold(cost)
							player.cur_mp = player.mmp
							player.note("Ваша магическая энергия восстановлена.")
							self.invalidate().check_for_pending_notes()
						cmds.add('heal mp', heal_mp, '?', lambda: self.more("Полностью восстановить ману."))
					add_heal_mp()
				else:
					line += " :("
			mp_desc.append(line)

		dispell = player.castable_dispell()
		for hex in player.hexes:
			cvp = hex.do_respite_remove_cost_verb_and_prefix(self.game)
			if cvp:
				cost, verb, prefix = cvp
				if cost > 0 and hex.dispell_amount > 0:
					cost = max(1, round(cost * (1 - hex.dispell_amount / hex.power)))
				if isinstance(hex, DeathWordHex) and not self.game.enough_gold_for(cost):
					cost = max(0, self.game.gold)

				prefixes = []
				can_cure = cost == 0 or self.game.enough_gold_for(cost)
				cure_cmd = can_cure and prefix + " " + hex.cmd()
				if can_cure: prefixes.append(prefix)

				dispell_cmd = dispell and hex.dispellable() and "dispell " + hex.cmd()
				if dispell_cmd: prefixes.append("dispell")
				cmds_enum = "/".join(prefixes)
				cmds_enum += (" " if cmds_enum else "") + hex.cmd()

				mp_desc.append(pad + hex.short_desc(for_multipad=True) + " [cure_verb]{}{}: [cost]{}{}{}".format(
					"" if can_cure else "(",
					verb,
					f"${cost}" if cost else "бесплатно",
					"" if can_cure else ")",
					f" [cure_cmd]({cmds_enum})" if cmds_enum else ""))

				if cure_cmd:
					def add_cure(cure_cmd=cure_cmd, hex=hex, cost=cost):
						def cure():
							if cost: self.game.take_gold(cost)
							hex.cancel()
							self.check_for_pending_notes()
						cmds.add(cure_cmd, cure, '?', lambda: self.more("{}\nСнять эффект: {}.".format(hex.detail(self.game), "${}".format(cost) if cost else "бесплатно")))
					add_cure()

				if dispell_cmd:
					def add_dispell(dispell_cmd=dispell_cmd, hex=hex):
						def cure():
							self.player.act_cast_spell(dispell, hex, None)
							self.check_for_pending_notes()
						def help():
							self.more("{}\n{}".format(
								hex.detail(self.game),
								Dispell.human_estimate_turns_left(hex, dispell.dispell_hex_amount_dis(self.player, hex, None), respite=True)))
						cmds.add(dispell_cmd, cure, '?', help)
					add_dispell()

				if not cure_cmd and not dispell_cmd:
					def add_help(hex=hex):
						def help(): self.more(hex.detail(self.game))
						cmds.add(hex.cmd(), help, '?', help)
					add_help()
		return player.living_desc() + "\n" + "\n".join(multipad(mp_desc))

	def describe_weapon(self, weapon, cmds, pad):
		desc = weapon.living_desc()

		lines = []
		for ammo in weapon.ammos:
			if ammo.finite_charges:
				line = "{pad}{bullet_name}".format(pad=pad, bullet_name=ammo.respite_name(weapon))
				if ammo.finite_charges:
					line += " [bullets]{bullets} [/bullets]".format(bullets=Con.bullet_bar(ammo.charges, ammo.MAX_CHARGES))

				cmd = ammo.cmd()
				if self.game.god_mode and ammo.has_charges():
					def make_shoot_func(ammo):
						def shoot():
							ammo.draw_charge()
						return shoot
					cmds.add('shoot ' + cmd, make_shoot_func(ammo))

				if ammo.needs_recharging():
					line += "перезарядка: [recharge_cost]${0}[/recharge_cost]".format(ammo.recharge_cost())
					if self.game.enough_gold_for(ammo.recharge_cost()):
						def make_reload_func(ammo=ammo):
							def reload():
								self.game.take_gold(ammo.recharge_cost())
								ammo.recharge()
								weapon.owner.note("Модуль перезаряжен.")
								self.invalidate().check_for_pending_notes()
							return reload
						line += f" [reload_cmd](reload {cmd})"
						cmds.add('reload ' + cmd, make_reload_func())
					else:
						line += " :("
				lines.append(line)
		if lines: desc += "\n" + "\n".join(multipad(lines))
		return desc

	def do_render(self, lines, cmds):
		game = self.game
		player = game.player
		weapon = player.weapon
		lines.append(f"ЛАГЕРЬ{self.game.marks(lspace=True)}")
		lines.append(f"Золото: {game.gold_str()} (shop)\n")
		cmds.add('shop', lambda: self.switch_to(Shop(game)), '?', lambda: self.more("Магазин, где вы можете приобрести или продать апгрейды."))
		if self.game.god_mode:
			default = 100
			def add_cmd(default=default):
				def handle_gold_answer(input, mode):
					try:
						if input and 'quit'.startswith(input): mode.revert(); return
						amount, max = (int(input) if input else default), 10000
						if amount <= max: pass
						else: raise ValueError(f"Слишком много, макс. {max}." if amount > max else "Неверное количество.")
					except ValueError as e:
						mode.more(exception_msg(e))
						return
					if amount >= 0: game.give_gold(amount)
					elif game.gold > 0: game.take_gold(min(-amount, game.gold))
					mode.revert()
				cmds.add('gold+', lambda: self.prompt(f"Сколько золота добавить (отнять)? (ENTER — {default}) ", handle_gold_answer))
			add_cmd()

			for who, cmd, name in ((player, 'xp', ''),) + (((weapon, 'wxp', weapon.name),) if weapon else ()):
				for sign, case, verb, func in (('+', Case.DATIVE, "сообщить", who.receive_xp), ('-', Case.GENITIVE, "высосать", who.drain_xp)):
					default, default_relative = 0.5, True

					def add_cmd(cmd=cmd+sign, name=name and name(case), verb=verb, default=default, default_relative=default_relative, func=func):
						def handle_xp_answer(input, mode):
							try:
								if input and 'quit'.startswith(input): mode.revert(); return
								if input:
									relative = False
									if input.endswith("%"): relative, input = True, input[:-len("%")]
									amount = float(input)
									if amount < 0: raise ValueError("Неверное количество.")
									if relative: amount /= 100
								else:
									amount, relative = default, default_relative
							except ValueError as e:
								mode.more(exception_msg(e)).reverts(1)
								return
							func(amount, relative=relative)
							self.check_for_pending_notes(extra_reverts=1, maybe=True)

						human_default = "{:.0%}".format(default) if default_relative else "{}".format(default)
						cmds.add(cmd, lambda: self.prompt(f"Сколько опыта{name and ' '}{name} {verb}? (ENTER — {human_default}) ", handle_xp_answer))
					add_cmd()

		pad = self.bars_pad(self.player)
		lines.append(self.describe_player(player, cmds, pad))
		if weapon: lines.append("\n" + self.describe_weapon(weapon, cmds, pad))

		lines.append("\nследующий уровень (next)")
		lines.append(  "выйти             (quit)")
		cmds.add('next', lambda: self.to_next_level(), '?', lambda: self.more("Взглянуть на следующего противника. Вы ещё сможете вернуться."))
		cmds.add('quit', lambda: self.quit(), '?', lambda: self.more("Выход в меню (с сохранением)."))

	def do_handle_command(self, cmd):
		if self.game.god_mode:
			handled = True
			if cmd == '*dropw':
				if self.player.weapon:
					self.more("Вы выбрасываете {}.".format(self.player.weapon.name.accusative))
					self.player.weapon = None
				else:
					self.more("У вас нет оружия.")
			elif cmd == '*acqw':
				if self.player.weapon:
					self.more("У вас уже есть оружие.")
				else:
					weapon = MachineGun()
					weapon.name = Noun.parse("{ржавый ствол}")
					self.player.set_weapon(weapon)
					self.more("Вы подбираете " + weapon.name.accusative + ".")
			elif cmd == '*jump':
				last = FixedLevels.count
				def handle_answer(input, mode):
					if not input or 'quit'.startswith(input): mode.revert(); return
					try:
						n = int(input)
						if not (1 <= n <= last): raise ValueError("Неверный уровень.")
					except ValueError as e:
						mode.more(exception_msg(e))
						return
					if self.game.next_level != n:
						self.game.forget_arena()
						self.game.next_level = n
						mode.more("Следующий уровень — {}!".format(self.game.next_level)).reverts(1)
					else:
						mode.revert()
				self.prompt("К какому уровню перейти ({}–{}, сейчас {})? ".format(1, FixedLevels.count, self.game.next_level), handle_answer)
			elif cmd == '*br':
				# Бэкапнуть текущее состояние игры и переключиться на новый файл.
				self.split_soul()
			else:
				handled = False
			if handled: return True

		if False:
			pass
		else:
			return super().do_handle_command(cmd)
		return True

	def do_handle_note(self, msg):
		self.log.add(msg, start_new_line=True)

	def split_soul(self):
		# Если игра собиралась сохраняться в новый файл, и эта попытка провалилась, второй раз она попробует его же, что бессмысленно.
		# И наоборот, если игра сохранялась в старый файл, то неважно, удалось ли ей это — запрашивается второе сохранение в новый и переключение на него.
		do_second_anyway = not self.game.will_autosave_to_new_file()
		self.game.save_nothrow(self, extra_error_comment=do_second_anyway and " в старый файл",
			then=lambda success, mode: (success or do_second_anyway) and self.game.save_nothrow(mode, to_new_file=True, note_success=True))

	def quit(self):
		default_yes = self.last_input == 'quit'
		allow_suicide = self.game.full_save_path
		def confirm(input, mode):
			parts = input.split('/')
			if parts and any(part and 'yes'.startswith(part) for part in parts) or not input and default_yes:
				self.game.save_nothrow(mode, then=lambda success, mode: mode.switch_to(MainMenu()), compress='r' not in parts)
			elif input and 'quit'.startswith(input):
				mode.switch_to(MainMenu()) # без сохранения — но это долго объяснять пользователю, пусть с тем же успехом дропает игру без сохранения по Ctrl-C
			elif allow_suicide and 'suicide'.startswith(input) and len(input) >= len('sui'):
				mode.yes_no("Это сотрёт сохранение. Вы уверены?",
					lambda mode: Game.remove_save_nothrow(mode, self.game.full_save_path, self.game.rel_save_path,
						note_success=True, then=lambda success, mode: mode.switch_to(MainMenu())), default=0)
			else:
				mode.revert()
		self.prompt("Выйти из игры? ({0}) ".format(highlight_variant("y/n", 0 if default_yes else 1)), confirm)

	def to_next_level(self):
		if self.game.hibernated_arena:
			arena = self.game.hibernated_arena
		else:
			arena = Arena()

		arena.limit_squad_members(Game.PLAYER_SQUAD, 3)
		arena.limit_squad_members(Game.MONSTER_SQUAD, 3)
		arena.deny_any_new_squads()

		# За игроком всегда первый ход.
		arena.add(self.player, Game.PLAYER_SQUAD, PlayerAI(), game=self.game, force_delay=0, to_left=True)

		if not self.game.hibernated_arena:
			FixedLevels.level(self.game.next_level).populate(arena)
		self.switch_to(ArenaEntrance(self.game, arena, self.game.next_level))

class Shop(NonCombatMode):
	def __init__(self, game):
		super().__init__(game)

	def do_handle_note(self, msg):
		self.log.add(msg, start_new_line=True)

	def reference_enemy(self):
		return FixedLevels.level(self.game.next_level).reference()

	class RenderContext:
		def __init__(self):
			self.lines_taken = 0

	def do_render(self, lines, cmds):
		ctx = self.RenderContext()
		start_lines = len(lines)
		lines.append(f"МАГАЗИН{self.game.marks(lspace=True)}")
		lines.append(f"Золото: {self.game.gold_str()}")
		desc = [self.player.living_desc(for_multipad=True)]
		if self.player.weapon: desc.append(self.player.weapon.living_desc(for_multipad=True))
		lines.extend(multipad(desc))
		lines.append("")

		lines.append("Апгрейды:")

		def add_upgrade(lines, up, target):
			line = "    " + up.shop_label(target) + " [/label]"
			if up.allow(target, ignore_ap_cost=True):
				gold_cost = up.gold_cost(target)
				ap_cost   = up.ap_cost(target)
				enough_gold = self.game.enough_gold_for(gold_cost)
				enough_ap   = target.enough_ap_for(ap_cost)
				def parenthesize_if(str, cond): return f"({str})" if cond else str

				line += parenthesize_if(f"${gold_cost}[/gold]", not enough_gold) + \
					" [sep]/ [ap]" + \
					parenthesize_if(str(ap_cost) + "[/ap]", not enough_ap) + \
					"[/costs] "

			cmd_list = []
			if up.allow(target) and self.game.enough_gold_for(gold_cost):
				cmd = up.cmd() + '+'
				cmd_list.append('+' if cmd_list else cmd)
				cmds.add(cmd, lambda: self.buy_upgrade(target, up, ctx), '?', lambda: self.more(self.imagine(up(), True)[0] or "Нет дополнительной информации."))

			last = up.last(target)
			if last:
				cmd = up.cmd() + '-'
				cmd_list.append('-' if cmd_list else cmd)
				cmds.add(cmd, lambda: self.sell_upgrade(target, last, ctx), '?', lambda: self.more(self.imagine(last, False)[0] or "Нет дополнительной информации."))

			line += "[cmds]"
			if cmd_list: line += "(" + ", ".join(cmd_list) + ")"
			lines.append(line)

		# Ограничения на уровни нужны только чтобы у игрока глаза не разбежались.
		# Но учитывая, что уровни могут понижаться, был бы шанс попасть в ситуацию, когда имеющийся апгрейд невозможно продать,
		# поэтому дополнительно проверяется их наличие. (Альтернативно, проверять какой-нибудь max_xl_so_far и никогда не блокировать уже открытые.)
		def upgrades_section(ups, target, min_xl=None, prohibit=None, lead=""):
			section_lines = []
			for up in ups:
				if (not min_xl or target.xl >= min_xl) and not (prohibit and prohibit(up)) and not (min_xl == target.xl == 1 and not target.xp) or up.find(target):
					add_upgrade(section_lines, up, target)
			if section_lines:
				if lead is not None: lines.append(lead)
				lines.extend(multipad(section_lines))

		upgrades_section((StrUpgrade, IntUpgrade, DexUpgrade, SpeedUpgrade), self.player, lead=None)
		if self.player.weapon:
			upgrades_section((IncendiaryAmmunitionUpgrade, SilenceAmmunitionUpgrade, TimestopAmmunitionUpgrade), self.player.weapon, min_xl=1,
				prohibit=lambda up: up == SilenceAmmunitionUpgrade and self.player.weapon.xl < 2 or up == TimestopAmmunitionUpgrade and self.player.weapon.xl < 3)
		upgrades_section((FirestormSpellUpgrade, DispellSpellUpgrade, FrailnessSpellUpgrade), self.player, min_xl=2)

		lines.append("\nВернуться в лагерь (quit)")
		cmds.add('quit', lambda: self.switch_to(Respite(self.game)), '?', lambda: self.more("Вернуться в лагерь."))
		ctx.lines_taken = len(lines) - start_lines

	def imagine(self, up, add):
		imagination = Imagination()
		(imagination.add if add else imagination.remove)(up)
		sandbagged = self.reference_enemy()

		lines = []
		def imagine_part(preface, cb):
			now = str(cb(None))
			then = str(cb(imagination))
			if now != then: lines.append("{}: [present]{}[/present] -> [future]{}.".format(preface, now, then))

		if isinstance(up, StrUpgrade):
			imagine_part("Макс. HP", lambda imagination: self.player.calculate_mhp(imagination))
			if self.player.unarmed:
				imagine_part("Удар по {}".format(sandbagged.name.dative),
					lambda imagination: "~{}".format(round(self.player.unarmed.beam(sandbagged, None, imagination).estimate_damage().avg, 1)))

		elif isinstance(up, IntUpgrade):
			imagine_part("Макс. MP", lambda imagination: self.player.calculate_mmp(imagination))
			for sp in self.player.spells:
				if isinstance(sp, Firestorm):
					imagine_part("Огненный шторм по {}".format(sandbagged.name.dative),
						lambda imagination: round(sp.Beam(self.player, sandbagged, None, imagination).estimate_damage().avg, 1))
				elif isinstance(sp, Frailness):
					imagine_part("Хрупкость на {}".format(sandbagged.name.accusative),
						lambda imagination: "{:.0%}/-{} AC".format(
							1 - sp.resistance(self.player, sandbagged, imagination), round(sp.ac_malus(self.player, sandbagged, None, imagination))))

			rs = next((sp for sp in sandbagged.spells if isinstance(sp, ResistibleSpell)), None)
			if rs: imagine_part("Сопротивление ({})".format(rs.name('long')),
				lambda imagination: "{:.0%}".format(rs.resistance(sandbagged, self.player, target_imagination=imagination)))

		elif isinstance(up, DexUpgrade):
			has_shot = self.player.weapon and self.player.weapon.ShotBeam
			imagine_part("Точность удара{} по {}".format("/выстрела" if has_shot else "", sandbagged.name.dative),
				lambda imagination: "{:.0%}".format(self.player.unarmed.beam(sandbagged, None, imagination).hit_chance()) +
					("/{:.0%}".format(self.player.weapon.shot_beam(sandbagged, None, None, master_imagination=imagination).hit_chance()) if has_shot else ""))
			if sandbagged.unarmed:
				imagine_part("Уклонение от {}".format(sandbagged.name.genitive),
					lambda imagination: "{:.0%}".format(1 - sandbagged.unarmed.beam(sandbagged, None, target_imagination=imagination).hit_chance()))
			if sandbagged.weapon:
				imagine_part("Уклонение от {}".format(sandbagged.name.genitive) + (" (" + sandbagged.weapon.name + ")" if sandbagged.unarmed else ""),
					lambda imagination: "{:.0%}".format(1 - sandbagged.weapon.melee_beam(sandbagged, None, target_imagination=imagination).hit_chance()))

		elif isinstance(up, IncendiaryAmmunitionUpgrade):
			def imagine_incendiary(imagination):
				incendiary = next((ammo for ammo in self.player.weapon.ammos if isinstance(ammo, IncendiaryAmmunition)), None)
				times = 0
				for item, added in Imagination.changes(imagination):
					if isinstance(item, IncendiaryAmmunitionUpgrade): times += (1 if added else -1)
				beam = self.player.weapon.shot_beam(sandbagged, None, incendiary, imagination)
				beam.imagine_incendiary = times
				return "~{}".format(round(beam.estimate_damage().avg, 1))
			imagine_part("Выстрел по {}".format(sandbagged.name.dative), imagine_incendiary)

		elif isinstance(up, SpellUpgrade):
			if add:
				lines.append("{}: {} MP.".format(cap_first(up.SPELL_CLASS.name('long')), up.SPELL_CLASS.do_mp_cost(None)))
				if isinstance(up, FirestormSpellUpgrade):
					lines.append("Урон по {}: [present]{}.".format(sandbagged.name.dative, round(Firestorm.Beam(self.player, sandbagged, None).estimate_damage().avg, 1)))
				elif isinstance(up, FrailnessSpellUpgrade):
					sp = Frailness()
					lines.append("На {} ({} AC): {:.0%}/-{} AC.".format(sandbagged.name.accusative, sandbagged.ac,
						1 - sp.resistance(self.player, sandbagged, imagination), round(sp.ac_malus(self.player, sandbagged, None, imagination))))

		return "\n".join(multipad(lines)), len(lines)

	def buy_upgrade(self, target, up_cls, ctx):
		up = up_cls()
		gold = up.gold_cost(target)
		def confirmed(mode):
			self.game.take_gold(gold)
			up.apply(target)
			if not self.log.something_new: self.player.note(lambda sink: sink.you == self.player and f"Апгрейд приобретён за ${gold}.")
			self.check_for_pending_notes(extra_reverts=1)

		im, im_lines = self.imagine(up_cls(), True)
		if im and ctx.lines_taken + im_lines + 5 + (1 if im_lines > 1 else 0) >= self.term_height: im = None
		msg = (im + "\n" + ("\n" if im_lines > 1 else "") if im else "") + "{} ${}. Продолжить?".format(up.cost_preface(target), gold)
		self.yes_no(msg, confirmed, default=1)

	def sell_upgrade(self, target, up, ctx):
		gold = up.refund()
		def confirmed(mode):
			up.revert(target)
			if not self.log.something_new: self.player.note(lambda sink: sink.you == self.player and f"Апгрейд продан за ${gold}.")
			self.game.give_gold(gold)
			self.check_for_pending_notes(extra_reverts=1)

		im, im_lines = self.imagine(up, False)
		if im and ctx.lines_taken + im_lines + 5 + (1 if im_lines > 1 else 0) >= self.term_height: im = None
		msg = (im + "\n" + ("\n" if im_lines > 1 else "") if im else "") + "В обмен на {} вы получите ${}. Продолжить?".format(up.sell_accusative(target), gold)
		self.yes_no(msg, confirmed, default=1)

class ArenaEntrance(GameMode):
	prev_mode = True
	def __init__(self, game, arena, floor_number):
		super().__init__(game)
		self.arena = arena
		self.floor_number = floor_number

	class DescribeFighterContext:
		def __init__(self): self.cmds_used = set()

		def make_cmd(self, cmd, prefix_func=lambda index: index):
			index = -1
			while True:
				uniquified = ("" if index < 0 else str(prefix_func(index))) + cmd
				if uniquified not in self.cmds_used:
					self.cmds_used.add(uniquified)
					return uniquified
				index += 1

	# Здесь выполняется эдакий вертикальный multipad, части выравниваются по высоте:
	#
	# Обычный крыс Lv.1 (O)           Волшебный крыс Lv.1 (V)   <-- имя (desc[0])
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
		ctx = self.DescribeFighterContext()
		max_width = 0
		descs     = []
		max_part_height = []
		for e in self.arena.enemies(self.player):
			desc, width = self.describe_fighter(e, self.arena.as_battler(e), cmds, ctx)
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
		lines.append("{} этаж{}".format(f"{self.floor_number}-й" if self.floor_number < FixedLevels.count else "Последний", self.game.marks(lspace=True)))
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
		lines.append(back + " " * (self.safe_term_width - BORDER - len(nx) - len(back)) + nx)
		cmds.add('quit', lambda: self.back_to_camp(), '?', lambda: self.more("Вернуться в лагерь."))
		cmds.add('next', lambda: self.next(), '?', lambda: self.more("Начать бой."))

	def do_handle_command(self, cmd):
		if cmd == "":
			self.yes_no("Сразиться?", lambda mode: mode.revert().to_arena(), question_id='enter_arena', default=1)
		else:
			return super().do_handle_command(cmd)
		return True

	@classmethod
	def build_abilities_help_4mp(cls, mode, fighter, battler, game, arena, cmds, ctx, flip=False):
		def battler_prefix_func(index):
			if index == 0: return battler.shortcut + '.'
			impossible(f"make_cmd: {battler.shortcut}")

		numeric_cmd = 1
		def make_numeric_cmd():
			nonlocal numeric_cmd
			result = ctx.make_cmd(str(numeric_cmd), battler_prefix_func)
			numeric_cmd += 1
			return result

		lines = []
		if fighter.unarmed:
			cmd = ctx.make_cmd('u', battler_prefix_func)
			lines.append("{0} [cmd]({1})".format(cap_first(fighter.unarmed.name()), cmd))
			cmds.add(cmd, lambda: mode.more(fighter.unarmed.name().upper() + "\n" + fighter.unarmed.detail(game)), '?', lambda: mode.more("Безоружная атака."))

		if fighter.weapon:
			cmd = ctx.make_cmd('w', battler_prefix_func)
			lines.append("{0} [cmd]({1})".format(fighter.weapon.name.cap_first(), cmd))
			cmds.add(cmd, lambda: mode.more(fighter.weapon.name.upper() + "\n" + fighter.weapon.detail(game)), '?', lambda: mode.more("Оружие."))

		for sp in fighter.specials:
			if not sp.should_display(): continue
			def add_sp(sp=sp):
				cmd = make_numeric_cmd()
				lines.append("{0} [cmd]({1})".format(cap_first(sp.name()), cmd))
				cmds.add(cmd, lambda: mode.more(sp.name().upper() + "\n" + sp.detail(game)), '?', lambda: mode.more("Особенность."))
			add_sp()

		for sp in fighter.spells:
			def add_spl(sp=sp):
				cmd = make_numeric_cmd()
				lines.append("{0} [cmd]({1})".format(cap_first(sp.name('long')), cmd))
				cmds.add(cmd, lambda: mode.more("{} ({} MP)\n{}".format(sp.name('long').upper(), sp.mp_cost(), sp.entrance_help(fighter, game.player, arena, game))),
					'?', lambda: mode.more("Заклинание."))
			add_spl()
		return lines

	def describe_fighter(self, fighter, battler, cmds, ctx):
		def add_help_cmd(cmd, func):
			cmds.add(cmd, func, '?', func)

		name_part = [f"{fighter.name.upper()} Lv.{fighter.xl} ({battler.shortcut})"]
		vitals_part = [fighter.hp_bar()]
		if fighter.has_magic(): vitals_part.append(fighter.mp_bar())
		vitals_part.append("")
		add_help_cmd(battler.shortcut,
			lambda: self.more(self.fighter_detail(fighter, disambiguate=any(id for id, enemy in enumerate(self.arena.enemies(self.player))))))

		abil_part = self.build_abilities_help_4mp(self, fighter, battler, self.game, self.arena, cmds, ctx)
		if abil_part:
			abil_part.append("")
			abil_part = multipad(abil_part)

		stats_part = multipad([part
			for part in (
				self.join_names_and_values(filter(lambda nv: nv[1], (("AC", fighter.ac), ("EV", fighter.ev)))),
				self.join_names_and_values(filter(lambda nv: nv[1] != 10, (("STR", fighter.base_str), ("INT", fighter.base_int), ("DEX", fighter.base_dex)))),
				fighter.base_spd != 100 and f"SPD [val]{fighter.base_spd}") if part])

		parts = [name_part, vitals_part, abil_part, stats_part]
		width = max(len(line) for lines in parts for line in lines)
		name_part[0] = " " * ((width - len(name_part[0])) // 2) + name_part[0]
		return parts, width

	@staticmethod
	def join_names_and_values(nv):
		names, values = tuple(zip(*nv)) or ((), ())
		return " [val]".join(filter(None, ("/".join(names), "/".join(map(str, values)))))

	ROW_NAMES = {'chance': "шанс", 'dam': "урон", 'effdam': "эфф. урон", 'maxdam': "макс. урон"}

	def fighter_detail(self, fighter, *, disambiguate=True):
		result = fighter.name.upper() if disambiguate else ""
		extra_sep = False
		def sep():
			nonlocal extra_sep
			if not result: return ""
			sep = "\n"
			if extra_sep:
				sep += "\n"
				extra_sep = False
			return sep

		if fighter.ac:
			reduction = Beam.ac_reduction(fighter.ac)
			result += sep() + "{} AC => снижение урона {:.0%} + ~{}".format(fighter.ac, reduction.relative, round(reduction.absolute_avg, 1))
			extra_sep = True

		footnotes = []
		columns = [(None, {})]

		def add_beam(name, beam, dam=True):
			est = beam.estimate_damage(do_tohit=True)
			if est.elem_parts:
				footnotes.append(", ".join(est.describe_elem_parts()))
				name += '*' * len(footnotes)

			columns.append((name, OrderedDict(filter(None, (
				est.hit_chance is not None and ('chance', "{:.0%}".format(est.hit_chance)),
				dam and ('dam', "~" + str(round(est.avg, 1))),
				dam and est.hit_chance is not None and ('effdam', '~' + str(round(est.avg * est.hit_chance, 1))),
				dam and self.game.god_mode and ('maxdam', str(est.max))
				)))))

		if self.player.unarmed:
			add_beam(self.player.unarmed.name(), self.player.unarmed.beam(fighter, self.arena))

		weapon = self.player.weapon
		if weapon:
			if weapon.MeleeBeam:
				add_beam("приклад", weapon.melee_beam(fighter, self.arena))

			if weapon.ShotBeam:
				ammo_descs = []
				had_shoot = False
				for ammo in weapon.ammos:
					if ammo.has_charges():
						if not ammo.finite_charges: had_shoot = True
						ammo_descs.append(ammo)

				if not had_shoot:
					ammo_descs.insert(0, None)

				for ammo in ammo_descs:
					add_beam(ammo.respite_name(weapon) if ammo else "выстрел", weapon.shot_beam(fighter, self.arena, ammo), dam=not ammo or not ammo.finite_charges)

		for spell in self.player.spells:
			epv = spell.do_entrance_preview(self.player, fighter, self.arena)
			if epv:
				if isinstance(epv, Beam): add_beam(spell.name('veryshort'), epv)
				elif isinstance(epv, dict): columns.append((spell.name('veryshort'), epv))
				else: impossible(epv, "do_entrance_preview")

		seen = set()
		rows = [None] + [categ for column in columns for categ in column[1] if categ not in seen and (seen.add(categ) or True)]

		# чтобы заголовки вида «тиш.» были выровнены со значениями по последней букве, а не точке.
		def hanging_tail(data):
			n = 0
			while n < len(data) and data[-1 - n] in ('.', '*'): n += 1
			return n

		table = pretty_table(sorted(rows, key=lambda row: 1 if row == 'effdam' else 2 if row == 'maxdam' else 0),
			columns,
			lambda row, column: column[0] if row is None else self.ROW_NAMES[row] if column[0] is None else column[1].get(row, None),
			self.safe_term_width,
			ljust=lambda row, column: hanging_tail(column[0]) if row is not None and column[0] is not None else 0)

		result += sep() + "\n".join(table)
		extra_sep = True

		for note_index, note in enumerate(footnotes):
			result += sep() + '*' * (1 + note_index) + note
		return result

	def back_to_camp(self):
		self.arena.remove(self.arena.as_battler(self.player), self.arena.shadows)
		self.revert()

	def next(self):
		# Секрет: игрока на арене нельзя сохранять (там ассерт стоит).
		# Чтобы это обойти, и чтобы об этом не знал никто «снаружи» (например, чтобы арене не пришлось фильтровать сохраняемых бойцов),
		# игрок убирается перед сохранением и восстанавливается после.
		#
		# Но можно посмотреть на это с другой стороны: с точки зрения пользователя игра сохраняется «как бы» в лагере (игрок попадёт туда после загрузки),
		# хотя на самом деле находится не в нём.
		# Такой финт ушами — эмуляция состояния «в лагере».
		#
		# Вообще есть смысл сохраняться сразу при входе на ArenaEntrance. Если однажды враги будут генерироваться, это снизит соблазн их рероллить.
		b = self.arena.as_battler(self.player)
		turn_queue_position = self.arena.turn_queue.index(b)
		self.arena.remove(b)

		# И арена запоминается здесь же (опять же, есть смысл делать это сразу при входе).
		self.game.hibernated_arena = self.arena

		def after_save():
			self.arena.add_battler(b, force_turn_queue_position=turn_queue_position)
			self.to_arena()
		self.game.save_nothrow(self, then=lambda success, mode: after_save())

	def to_arena(self):
		if not self.game.performance:
			self.game.performance = self.game.Performance(self.game, self.arena)

		def on_leave(av):
			av.arena.stop()
		self.switch_to(ArenaView(self.game, self.arena, on_leave))
		self.arena.start()

class ArenaView(GameMode):
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
			self.scroll_line = self.scroll_index = 0
			self.last_message, self.last_message_reps = None, 0

		def add(self, msg, turn=None, *, next_sep=" ", start_new_line=None):
			if (not start_new_line or self.lines and self.lines[-1].pieces_count == 1) and msg == self.last_message:
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
					self.scroll_line = self.scroll_index = 0
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

	# сейчас on_leave вызывается в очень тонкий момент (в Mode.do_deactivate лол), поэтому switch_to там делать нельзя.
	def __init__(self, game, arena, on_leave):
		super().__init__(game)
		self.arena = arena
		self.on_leave = on_leave
		self.awaiting_decision = self.your_turn_announced = self.okay_to_skip_turns = False
		self.player_ai = self.atb_maximum = self.outcome = self.prev_target = self.death_message = None

		def receive_note(msg):
			if self.player.alive:
				self.log.add(msg, self.current_player_turn)
			elif not self.death_message:
				# Хрупкое предположение, что первая заметка после смерти будет её описанием. Пока работает, но в будущем, возможно,
				# понадобится цеплять к note'ам дополнительную информацию для таких случаев.
				self.death_message = msg

		self.log = self.MessageLog()
		self.sink = MessageSink(self.player, receive_note)
		self.log_lines = self.log_area_height = self.start_log_at = None
		self.current_player_turn = -1
		self.your_turn_announced = False
		self.do_prompt = True

	def do_activate(self):
		self.player_ai = check(self.arena.as_battler(self.player).ai, lambda player_ai: isinstance(player_ai, PlayerAI), "player_ai")
		self.atb_maximum = self.estimate_good_atb_maximum()
		self.arena.add_sink(self.sink)

	def do_deactivate(self):
		if self.on_leave: self.on_leave(self)
		self.arena.remove_sink(self.sink)

	def do_process(self):
		layout = self.estimate_screen_layout()
		self.awaiting_decision = False
		self.do_prompt = True
		self.log_area_height = layout.log_lines
		do_turn = True

		while do_turn:
			if self.outcome: do_turn = False
			elif self.player.dead: self.outcome, do_turn = 'lost', False
			elif not next((enemy for enemy in self.arena.enemies(self.player) if not enemy.transient), None): self.outcome, do_turn = 'won', False
			elif self.arena.whose_turn() == self.player:
				if self.player.paralyzed():
					pass
				elif not self.player_ai.decision:
					self.awaiting_decision = True
					do_turn = False
				if not self.your_turn_announced: # and next(self.arena.enemies(self.player), None):
					self.current_player_turn += 1
					put_extra_line = self.log.lines and self.log_area_height >= 7 and len(self.log.lines[-1].line) > self.safe_term_width
					if put_extra_line:
						self.log.add("", turn=self.current_player_turn, start_new_line=True)
					self.log.add("_", turn=self.current_player_turn, next_sep="", start_new_line=True)
					self.your_turn_announced = True

			# условие в really означает «прокрутить, если сейчас будет сообщение с (...) или render()».
			# В противном случае продолжится process и пользователь какое-то время не увидит результат, поэтому скроллить его рано.
			self.log_lines, pending = self.log.scroll(self.log_area_height, self.safe_term_width, really=lambda pending: pending or not do_turn)
			if pending:
				self.disable_prompt_this_time().prompt("(...)", lambda _input, mode: mode.revert())
				return

			if do_turn:
				if self.arena.whose_turn() == self.player: self.your_turn_announced = False
				self.arena.turn()

		if self.outcome == 'lost':
			pv = self.session.previews.fn2it.get(self.game.rel_save_path, None)
			if pv:
				after_prompt = lambda input, mode: mode.yes_no("Загрузить последнее сохранение?",
					lambda mode: Game.load_nothrow(pv, mode, more_on_success=False, on_fail=lambda mode: mode.switch_to(MainMenu())),
					no_cb=lambda mode: mode.switch_to(MainMenu()))
			else:
				after_prompt = lambda input, mode: mode.switch_to(MainMenu())
			self.disable_prompt_this_time().prompt("\n..." + check(self.death_message, "нет сообщения о смерти"), after_prompt)

		elif self.outcome == 'won':
			self.disable_prompt_this_time().more("\nПобеда!").then(lambda mode: self.to_results(self.outcome))
		elif self.outcome == 'retreat':
			self.disable_prompt_this_time().prompt("", lambda input, mode: self.to_results(self.outcome))
		else: check(self.outcome, not self.outcome, 'outcome')

	def do_render(self, lines, cmds):
		layout = self.estimate_screen_layout()
		start_lines = len(lines)
		reserve = self.reserve_lines()
		squadA, squadB = tuple(self.arena.squads[squad_id] for squad_id in (Game.PLAYER_SQUAD, Game.MONSTER_SQUAD))
		displayed_hexes = set()
		displayed_battlers = []
		imA = self.build_squad_image(squadA, self.term_height - 1 - reserve - self.log_area_height, False, displayed_hexes, displayed_battlers)
		imB = self.build_squad_image(squadB, self.term_height - 1 - reserve - self.log_area_height, True, displayed_hexes, displayed_battlers)

		# там проверяется awaiting_decision
		cmds_desc = multipad(self.build_commands(cmds, layout.action_lines + layout.squad_lines - len(imA), displayed_hexes, displayed_battlers))

		for lineno in range(layout.squad_lines + layout.action_lines):
			left = imA[lineno] if lineno < len(imA) else cmds_desc[lineno - len(imA)] if 0 <= lineno - len(imA) < len(cmds_desc) else ""
			right = imB[lineno] if lineno < len(imB) else ""

			limit = self.safe_term_width
			if len(left) + len(right) > limit:
				overflow = len(left) + len(right) - limit
				if overflow <= len(right) // 2: right = right[overflow:]
				if len(left) + len(right) > limit: impossible(f"Строка не умещается в ширину консоли: {left}/{right}.")
			lines.append(left.ljust(limit - len(right)) + right)

		lines_taken = len(lines) - start_lines
		self.start_log_at = min(
			lines_taken + 3 if self.start_log_at is None or self.start_log_at < lines_taken else self.start_log_at,
			self.term_height - 1 - reserve - self.log_area_height)

		lines.extend("" for _i in range(self.start_log_at - lines_taken))
		lines.extend(self.log_lines)
		if self.do_prompt:
			lines.extend("" for _i in range(self.log_area_height - len(self.log_lines)))

		if self.game.god_mode:
			cmds.add('quit', lambda: self.to_results('godly_quit'))

	def min_lines_for_squads(self):
		return max(
			(sum(
				(1 + # имя
				1 + # полоска HP
				(1 if battler.fighter.has_magic() else 0) + # полоска MP
				1) # новая строка
				for battler in squad.members
			) for squad in self.arena.squads.values()), default=0)

	def max_lines_for_squads(self):
		def limit_for(squad):
			return check(squad.max_members, lambda max_members: max_members is not None, lambda: f"У стороны {squad.id} не ограничено число участников.") \
				if False else len(squad.members)

		return max(
			max(
				(
					1 + # имя
					2 + # полоски HP/MP
					4 + # 4 хекса
					1   # новая строка
				) * limit_for(squad),
				len(self.build_squad_image(squad))
			) for squad in self.arena.squads.values())

	def min_action_lines(self):
		return 4 # Игрок, новая строка, оружие, новая строка.

	def max_action_lines(self):
		return len(self.build_commands(None))

	def min_log_lines(self):
		return 3

	def reserve_lines(self):
		return 7 # как минимум 3 = (1) пустая строка перед приглашеним, (2) >приглашение и команда, (3) новая строка. Плюс чуть-чуть.

	def do_handle_command(self, cmd):
		if not cmd:
			if self.awaiting_decision:
				if self.okay_to_skip_turns:
					self.decide_to_skip_turn()
				else:
					def confirmed(mode):
						self.okay_to_skip_turns = True
						self.decide_to_skip_turn()
						mode.revert()
					self.yes_no("Пропустить ход?", confirmed, question_id='skip_turn', default=1)
		elif cmd == '*dd':
			self.more("\n\n".join("\n".join(f"{k}: {v}" for k, v in e.__dict__.items()) for e in self.arena.enemies(self.player)))
		elif cmd == '*atb':
			# Показать (нечитаемую) шкалу ATB.
			self.more(self.build_atb_scale())
		elif cmd == '*cums':
			# Показать отслеживаемые промахи.
			self.more(self.arena.describe_cumulatives())
		elif cmd == '*ra':
			# Показать урон, полученный всеми присутствующими.
			self.more(self.arena.describe_received_attacks())
		elif self.game.god_mode and cmd.startswith('*ai'):
			shortcut = cmd[skip_whitespace(cmd, len('*ai')):]
			for b in self.arena.battlers:
				if b.shortcut == shortcut:
					if b.ai: self.more(b.ai.do_describe_internals())
					else: self.more("{} не назначен ИИ.")
					break
			else: self.more("Нет такого бойца." if shortcut else "Задайте имя бойца.")
		else:
			return super().do_handle_command(cmd)
		return True

	def decide(self, what):
		check(self.awaiting_decision, "не вовремя")
		self.player_ai.decide(what)

	def decide_to_skip_turn(self):
		self.decide(lambda ai: ai.fighter.act_skip_turn())

	def disable_prompt_this_time(self, and_log=False):
		self.do_prompt, self.last_input, self.awaiting_decision = False, None, False
		return self.invalidate()

	def build_battler_header(self, b, flip, paren=True):
		# (N) Некромант AC:6 EV:10
		lines = []
		op, cp = ("(", ")") if paren else ("-", "-")
		lines.append(left_to_right(f"{op}{b.shortcut}{cp}",
			b.fighter.name.cap_first(), b.fighter.ac > 0 and f"AC:{b.fighter.ac}", b.fighter.ev > 0 and f"EV:{b.fighter.ev}", b.game and b.game.marks(), flip=flip))
		if b.fighter.dead:
			lines.append("RIP")
		else:
			lines.append(b.fighter.hp_bar(flip))

			if b.fighter.has_magic():
				lines.append(b.fighter.mp_bar(flip))
		return lines

	def build_squad_image(self, squad, lines_limit=None, flip=False, displayed_hexes=None, displayed_battlers=None):
		if not isinstance(squad, self.arena.Squad): squad = self.arena.squads[squad]
		class PerBattler:
			def __init__(self, battler, lines):
				self.battler = battler
				self.lines = lines
				self.hex_descs = []
				self.hexes_gen = iter(battler.fighter.hexes)

		per_battler, total_lines = [], 0
		# Обязательные строки.
		for b in squad.members:
			lines = self.build_battler_header(b, flip)
			per_battler.append(PerBattler(b, lines))
			total_lines += len(lines) + 1 # пустая строка после каждого участника

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
			for _i in range(len(per_battler)):
				cur = (cur + 1) % len(per_battler)
				im = per_battler[cur]
				hex = next(im.hexes_gen, None)
				if hex:
					if displayed_hexes is not None: displayed_hexes.add(hex)
					desc = hex.short_desc(for_multipad=True, flip=flip)
					im.hex_descs.append(desc)
					total_lines += 1
					something_changed = True
					if lines_limit is not None and total_lines >= lines_limit: break
			if not something_changed: break
		for im in per_battler:
			im.hex_descs = multipad(im.hex_descs)
			if next(im.hexes_gen, None):
				extra = 1 + sum(1 for hex in im.hexes_gen)
				hint = "  (+{extra}, {cmd})".format(extra=extra, cmd=im.battler.shortcut)
				if im.hex_descs: im.hex_descs[-1] += hint
				else: im.lines[-1] += hint

		if displayed_battlers is not None:
			line = 0
			for im in per_battler:
				displayed_battlers.append((im.battler, line, flip))
				line += len(im.lines) + len(im.hex_descs) + 1

		result = [line
			for im in per_battler
				for lines in (im.lines, im.hex_descs, ("",))
					if lines is not None
						for line in lines]
		assert len(result) == total_lines, f"len(result) = {len(result)}, total_lines = {total_lines}"
		return result

	class ScreenLayout:
		def __init__(self, av):
			lines = [av.min_lines_for_squads(), av.min_action_lines(), av.min_log_lines()]
			lim   = [av.max_lines_for_squads(), av.max_action_lines(), lines[2] + round((av.term_height - sum(lines))/3/max(1, av.term_width/50))]
			self.squad_lines, self.action_lines, self.log_lines = tuple(dispense(lines, av.term_height - av.reserve_lines() - sum(lines), lim=lim))

	def estimate_screen_layout(self):
		return self.ScreenLayout(self)

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

	def build_commands(self, cmds, lines_limit=None, displayed_hexes=None, displayed_battlers=None):
		desc = []
		if not self.awaiting_decision or self.player.dead: return desc

		fetter = grasp = fettered = None
		for hex in self.player.hexes:
			if isinstance(hex, FetterHex): fetter, fettered = hex, True
			elif isinstance(hex, GraspHex): grasp, fettered = hex, True

		def add(*,
			cmd_desc, cmd_base,
			perform=lambda target, ai: throw(NotImplementedError("perform")),
			help=lambda target: throw(NotImplementedError("help")),
			categ='player',
			desc_extra=None, extra_cmds=None,
			targeting='single',
			ljust_cmd=True,
			choose_target_name=None, choose_target_help=None, exec_hook=None and (lambda target, exec: exec()), validate_target=None):

			cmd_extra = ""

			def remember_and_decide(target, remember_target=None):
				if remember_target is True: remember_target = target
				if remember_target: self.prev_target = check(remember_target, isinstance(remember_target, Fighter), "remember_target")
				self.decide(lambda ai: perform(target, ai))

			def add_for_target(target, extra, remember_target=None, custom_exec=None, custom_help=None):
				exec = custom_exec or (lambda: remember_and_decide(target, remember_target))
				cmds.add(cmd_base + (' ' + extra if extra else ''), lambda: exec_hook(target, exec) if exec_hook else exec(),
					'?', lambda: self.more(custom_help() if custom_help else help(target)))

			n_targets = 0
			if targeting == 'single':
				default_target = self.prev_target
				# TODO:
				# Есть два врага — A и B.
				# Если ударить B, затем скастовать что-то на себя, затем ударить без параметра —
				# выберется A, т. к. запомненная цель — игрок — невалидна для удара.
				# Интуитивнее будет выбрать снова B, т. е. помнить не только самую последнюю цель, а выбирать последнюю подходящую из прежних.
				# Мне лень это делать, сейчас для обхода проблемы диспелл вообще не запоминает цель, если применён на заклинании.
				if (not default_target or default_target.dead or not self.arena.are_enemies(default_target, self.player, maybe=True)
					or validate_target and not validate_target(default_target)):
					default_target = next((target for target in self.arena.enemies(self.player) if not validate_target or validate_target(target)), None)
				if default_target:
					if cmds: add_for_target(default_target, None)

				for target in self.arena.enemies(self.player):
					if validate_target and not validate_target(target): continue
					if cmds: add_for_target(target, self.arena.as_battler(target).shortcut, remember_target=True)
					n_targets += 1
			elif targeting == 'mass' or targeting == 'n/a':
				if cmds: add_for_target(None, None)
				n_targets = None
			elif targeting == 'dispell-like':
				for b in self.arena.battlers:
					targets = list(Dispell.targets_on_fighter(self.player, b.fighter, self.arena))
					if targets:
						def add_targets(b=b, targets=targets):
							if len(targets) == 1:
								if cmds: add_for_target(targets[0], b.shortcut, remember_target=isinstance(targets[0], Fighter))
							else:
								check(choose_target_name, "choose_target_name", choose_target_help, "choose_target_help")
								if cmds:
									def name(target):
										if isinstance(target, Hex): return target.name(target)
										elif isinstance(target, Fighter): return target.name
										else: impossible(target, "target")
									def cmd(target):
										if isinstance(target, Hex): return target.cmd()
										elif isinstance(target, Fighter): return self.arena.as_battler(target).shortcut
										else: impossible(target, "target")
									def extra(target):
										if isinstance(target, Hex): return target.dispelling_bar()
										elif isinstance(target, Fighter): return target.hp_bar()
										else: impossible(target, "target")
									def choose(target):
										remember_and_decide(target, isinstance(target, Fighter))
									add_for_target(b.fighter, b.shortcut, remember_target=True,
										custom_exec=lambda: self.switch_to(ChooseTarget(choose_target_name(b.fighter, targets), targets, name, cmd, extra, choose, help)),
										custom_help=lambda: choose_target_help(b.fighter, targets))
						add_targets()
						n_targets += 1
			else: impossible(targeting, "targeting")

			if n_targets == 0: return
			if n_targets and n_targets > 1: cmd_extra = " цель"

			desc.append("[{categ}_cmd_desc]{cmd_desc} [{rjust_cmd}/{categ}_cmd_desc][{categ}_cmd]({cmd_base}{cmd_extra}{extra_cmds}){desc_extra}".format(
				categ=categ, rjust_cmd = '>' if not ljust_cmd else "",
				cmd_desc=cmd_desc, cmd_base=cmd_base, cmd_extra=cmd_extra, desc_extra=desc_extra or "",
				extra_cmds=", " + extra_cmds if extra_cmds else ""))

		first_player_line = len(desc)
		if fettered:
			fetter_index = 0
			for fet, mode in ((fetter, 'fetter'), (grasp, 'grasp')):
				if not fet: continue
				cmd = 'break' if fetter_index == 0 else 'break ' + mode if fetter_index == 1 else impossible("fetter_index")
				if cmds:
					def add_cmd(fet=fet):
						cmds.add(cmd, lambda: self.decide(lambda ai: fet.phys_break(self.player, self.arena)), '?', lambda: self.more(fet.phys_break_help()))
					add_cmd()
				desc.append("[player_cmd_desc]вырваться [player_cmd]({}) {}".format(cmd,
					" " + multipad.escape(fet.dispelling_bar()) if (not displayed_hexes or fet not in displayed_hexes) and fet.dispell_amount else ""))
				fetter_index += 1

		if self.player.unarmed and not fettered:
			def perform(target, ai):
				self.player.act_attack_unarmed(target, ai.arena)
			def help(target):
				return "Ударить {} голыми руками.\n{}".format(target.name.accusative, self.player.unarmed.beam(target, self.arena).human_stats(do_max=self.game.god_mode))
			add(cmd_desc="атака врукопашную", cmd_base='hit', perform=perform, help=help)

		if not fettered:
			desc.append("[player_cmd_desc]отступить [player_cmd](retreat)")
			if cmds:
				cmds.add('retreat', lambda: self.confirm_retreat(),
					'?', lambda: self.more("\n".join(filter(None, ("Сбежать из боя.", self.describe_retreat_consequences())))))

			impregnation = next((sp for sp in self.player.specials if isinstance(sp, Impregnation)), None)
			if impregnation:
				def perform(target, ai):
					impregnation.act_impregnate(target, ai.arena)
				def help(target):
					return "Заразить {} личинками.\nШанс: {:.0%}.".format(target.name.accusative, self.arena.hit_chance(*impregnation.save_throw(target)))
				add(cmd_desc="заразить", cmd_base='infest', perform=perform, help=help, validate_target=lambda target: target.can_be_impregnated)
		player_lines_before_spells = len(desc) - first_player_line

		if self.player.can_cast():
			more_than_one = any(index == 1 for index, spell in enumerate(self.player.spells) if self.player.can_cast(spell))

			for spell in self.player.spells:
				if self.player.can_cast(spell):
					def add_spell(spell=spell):
						choose_target_name = choose_target_help = None
						if isinstance(spell, Dispell):
							def choose_target_name(fighter, targets):
								return spell.name('long').upper() + " > " + fighter.name
							def choose_target_help(fighter, targets):
								hex, itself_too = next((target for target in targets if isinstance(target, Hex)), None), Dispell.valid_target(self.player, fighter, self.arena)
								msg = "Развеять"
								if itself_too: msg += (fighter.gender.ize(" сам{ого/у/о}") if hex else "") + " " + fighter.name.accusative + (" или" if hex else "")
								if hex:
									whomst = fighter.gender.ize("не{го/её}") if itself_too else "вас" if fighter is self.player else fighter.name.accusative
									msg += " наложенное на " + whomst + " заклинание"
								return msg + "."

						def exec_hook(target, exec):
							def confirmed(mode):
								mode.revert()
								exec()
							if isinstance(spell, Frailness) and not target.base_ac and not target.ac:
								self.yes_no("{} не имеет брони, и {} не будет иметь эффекта. Скастовать всё равно?".format(
									target.name.cap_first(), spell.name('long')), confirmed, default=1)
							else:
								exec()

						add(cmd_desc="{} [mp]{} MP".format(spell.name('short'), spell.mp_cost()),
							cmd_base=spell.cmd(), categ='spell' if more_than_one and player_lines_before_spells > 1 else 'player',
							perform=lambda target, ai: self.player.act_cast_spell(spell, target, ai.arena),
							help=lambda target: spell.attack_help(self.player, target, self.arena, self.game),
							targeting=spell.TARGETING,
							ljust_cmd=False,
							choose_target_name=choose_target_name, choose_target_help=choose_target_help, exec_hook=exec_hook)
					add_spell()

		if len(desc) > first_player_line:
			desc.append("")
		else:
			first_player_line = None

		weapon = self.player.weapon
		if weapon:
			first_weapon_line = len(desc)
			if weapon.MeleeBeam and not fettered:
				def perform(target, ai):
					self.player.act_weapon_melee(target, ai.arena)
				def help(target):
					return "Ударить {} прикладом {}.\n{}".format(target.name.accusative, weapon.name.genitive,
						weapon.melee_beam(target, self.arena).human_stats(do_max=self.game.god_mode))
				add(cmd_desc="удар прикладом", cmd_base='kick', perform=perform, help=help, categ='weapon')

			if weapon.ShotBeam:
				ammo_descs = []
				had_shoot = False
				rapid_targets = list(self.arena.enemies(self.player))
				can_rapid = len(rapid_targets) > 1

				for ammo in weapon.ammos:
					if ammo.has_charges():
						cmd, rapid_cmd = 'shoot', None
						if can_rapid and not ammo.finite_charges: rapid_cmd = 'rapid'
						if had_shoot or ammo.finite_charges:
							cmd += " " + ammo.cmd()
							if rapid_cmd: rapid_cmd += " " + ammo.cmd()
						else:
							had_shoot = True
						ammo_descs.append((ammo, cmd, can_rapid and rapid_cmd))

				if not had_shoot:
					ammo_descs.insert(0, (None, 'shoot', can_rapid and 'rapid'))

				for ammo, cmd, rapid_cmd in ammo_descs:
					def add_shoot(ammo=ammo, cmd=cmd):
						def perform(target, ai):
							self.player.act_weapon_shoot(target, ai.arena, ammo)

						def help(target):
							help_noun = ammo and ammo.noun_name()
							return "Выстрелить в {}{}.\n{}".format(target.name.accusative, (" " + help_noun.instrumental if help_noun else ""),
								weapon.shot_beam(target, self.arena, ammo).human_stats(do_max=self.game.god_mode))

						exec_hook = None
						if isinstance(ammo, SilenceAmmunition):
							def exec_hook(target, exec):
								def confirmed(mode):
									mode.revert()
									exec()
								if target.silenced():
									self.yes_no("{} уже под тишиной, новый заряд не продлит её. Выстрелить всё равно?".format(target.name.cap_first()), confirmed, default=1)
								elif not any(target.can_cast(sp) for sp in target.spells):
									self.yes_no("Вы собираетесь выстрелить тишиной, но {} {} никаких заклинаний. Выстрелить всё равно?".format(target.name.cap_first(),
										"и так не может произнести" if target.spells else "не знает"), confirmed, default=1)
								else:
									exec()
						elif isinstance(ammo, TimestopAmmunition):
							if self.arena.time_stopped():
								def exec_hook(target, exec):
									def confirmed(mode):
										mode.revert()
										exec()
									self.yes_no("Время уже остановлено, новый заряд не продлит эффект. Вы уверены?", confirmed, default=1)

						add(cmd_desc=ammo.battle_name() if ammo else "огонь", cmd_base=cmd, perform=perform, help=help, categ='weapon',
							desc_extra=ammo and ammo.finite_charges and " [bullets]" + Con.bullet_bar(ammo.charges, ammo.MAX_CHARGES),
							exec_hook=exec_hook, extra_cmds=rapid_cmd)

						if cmds and rapid_cmd:
							def rapid(ai):
								self.player.act_weapon_rapid(rapid_targets, self.arena, ammo)
							def help():
								return "Очередь{} по всем врагам.\nУрон: {}.".format(
									" " + ammo.plural_name().instrumental if ammo else "",
									Firestorm.estimate_mass_damage(rapid_targets,
										lambda target: self.player.weapon.shot_beam(target, self.arena, ammo, 'rapid'), do_max=self.game.god_mode))
							cmds.add(rapid_cmd, lambda: self.decide(rapid), '?', lambda: self.more(help()))
					add_shoot()

			if len(desc) > first_weapon_line:
				desc[first_weapon_line] = multipad.escape(weapon.name.cap_first()) + ": " + desc[first_weapon_line]
				desc.append("")

		if False and first_player_line is not None:
			desc[first_player_line] = multipad.escape(self.player.name) + ": " + desc[first_player_line]

		if lines_limit is not None and len(desc) > check(lines_limit, lines_limit >= 2, "lines_limit"):
			cut = len(desc) - lines_limit
			actual_commands_cut = sum(1 for lineno in range(len(desc) - 1 - cut, len(desc) - 1) if desc[lineno])
			del desc[-1-cut:-1]
			while len(desc) > 2 and not desc[-2]: del desc[-2]
			desc[-2] += " (+{}, cmds)".format(actual_commands_cut)
			if cmds: cmds.add('cmds', lambda: self.switch_to(ChooseCommandOnSeparateScreen(self)), '?', "Отобразить все команды.")

		if cmds and displayed_battlers:
			for db in displayed_battlers:
				def add_highlight(db=db):
					battler, start_line, flip = db
					def highlight():
						self.switch_to(InBattleBattlerDetail(battler, self, start_line, flip))
					cmds.add(battler.shortcut, highlight,
						'?', lambda: self.more("Отобразит информацию по " + ("вам" if battler.fighter == self.player else battler.fighter.name.dative) + "."))
				add_highlight()

		return desc

	def to_results(self, outcome):
		self.switch_to(BattleResults(self.game, self.arena, outcome))

	def confirm_retreat(self):
		def confirmed(mode):
			# Отступление выполняется немедленно, а не через decide, чтобы избежать тикания разных нехороших вещей в конце хода (Смертный приговор 1t, anyone?).
			check(self.outcome, not self.outcome, 'outcome')
			self.outcome = 'retreat'
			self.player.note(lambda sink: sink.youify("{Вы/F} сбегает{е/} из боя!", self.player))
			mode.revert()

		self.yes_no("\n".join(filter(None, (self.describe_retreat_consequences(), "Сбежать из боя?"))), confirmed, default=1)

	def describe_retreat_consequences(self):
		xp, xp_rel, gold, _severeness = self.arena.retreat_penalty(self.game)
		losses = []
		if xp:
			xl, xp = self.player.drain_xp(xp, relative=xp_rel, emulate=True)
			if xl != self.player.xl or xp != self.player.xp:
				if xl != self.player.xl or self.player.next_percentage() != self.player.next_percentage(xl, xp):
					clarification = self.player.xl_desc(xl, xp, short=True, prev=self.player.snapshot())
				else:
					clarification = "<1%"
				losses.append("опыт ({})".format(clarification))

		if gold:
			losses.append("${} (ост. ${})".format(gold, self.game.gold - gold))

		lines = []
		if self.game.god_mode:
			effective_enemies_xl, severeness = self.arena.retreat_penalty(self.game, godly_peek=True)
			lines.append("effective_enemies_xl = {}, severeness = {}".format(round(effective_enemies_xl, 2), round(severeness, 2)))
		if losses:
			lines.append("Вы потеряете {}.".format(join_with_lastsep(losses, ", ", " и ")))
		return "\n".join(lines)

class InBattleBattlerDetail(GameMode):
	prev_mode = True
	do_cls = True

	def __init__(self, battler, av, start_line, flip):
		super().__init__(av.game)
		self.battler, self.av, self.start_line, self.flip = battler, av, start_line, flip

	def do_render(self, lines, cmds):
		fighter = self.battler.fighter
		lines.extend("" for _ in range(self.start_line))
		desc = self.av.build_battler_header(self.battler, self.flip, paren=False)
		hexes_desc = []
		dispell = self.av.awaiting_decision and self.player.castable_dispell()
		for hex in fighter.hexes:
			dispell_cmd = dispell and Dispell.valid_target(self.player, hex, self.av.arena) and 'dispell ' + hex.cmd()
			hexes_desc.append(hex.short_desc(for_multipad=True, flip=self.flip, cmd = ", ".join(filter(None, (hex.cmd(), dispell_cmd)))))
			def add_commands(hex=hex):
				def help():
					self.more(hex.name(hex).upper() + "\n" + hex.detail(self.game))
				cmds.add(hex.cmd(), help, '?', help)

				if dispell_cmd:
					def decide_do_dispell():
						self.av.decide(lambda ai: ai.fighter.act_cast_spell(dispell, hex, self.av.arena))
						self.revert()
					cmds.add('dispell ' + hex.cmd(), decide_do_dispell, '?', lambda: self.more(dispell.attack_help(self.player, hex, self.av.arena, self.game)))
			add_commands()
		hexes_desc = multipad(hexes_desc)

		abil_desc = None
		if fighter is not self.player:
			ctx = ArenaEntrance.DescribeFighterContext()
			abil_desc = ArenaEntrance.build_abilities_help_4mp(self, fighter, self.battler, self.game, self.av.arena, cmds, ctx, flip=self.flip)
			abil_desc = multipad(abil_desc)

		stats_part = multipad(list(filter(None, (
			ArenaEntrance.join_names_and_values((name, str(value)) for name, value, base in nvbs if value != base or base != hide_base)
			+ (" ({})".format("/".join(str(base) for name, value, base in nvbs if value != base or base != hide_base))
				if any(value != base for name, value, base in nvbs) else "")

			for nvbs, hide_base in (
				((("STR", fighter.str, fighter.base_str), ("INT", fighter.int, fighter.base_int), ("DEX", fighter.dex, fighter.base_dex)), 10),
				((("SPD", fighter.spd, fighter.base_spd),), 100))))))
		pad_to = max((len(line) for lines in (abil_desc, stats_part, desc[1:]) if lines for line in lines), default=0)

		if hexes_desc:
			desc.extend(hexes_desc)
		desc.append("") # если hexes_desc не было — это пустая строка между шапкой и остальным

		if abil_desc:
			desc.extend(line.ljust(pad_to) for line in abil_desc)
			desc.append("")

		if stats_part:
			desc.extend(line.ljust(pad_to) for line in stats_part)
			desc.append("")

		if self.flip:
			for lineno, line in enumerate(desc):
				desc[lineno] = line.rjust(self.safe_term_width)
		lines.extend(desc)

		summ_start_line = len(lines)
		if fighter.transient:
			msg = "Это {} существо.".format("призванное" if fighter.dispellable else "временное")
			if self.av.arena.are_enemies(self.player, fighter):
				msg += " Вы не получите за него опыт, но и убивать его не обязательно для победы."
			lines.append(wrap(msg, self.safe_term_width))

		if self.av.arena.are_enemies(self.player, fighter):
			dispell = next((sp for sp in self.player.spells if isinstance(sp, Dispell)), None)
			if dispell and Dispell.valid_target(self.player, fighter, self.av.arena):
				if fighter.dispellable:
					if fighter.transient: lines.append("Также вы можете его развеять.")
					else: lines.append("Вы можете развеять это существо.")
				elif fighter.transient:
					if fighter.summoned: lines.append("Тем не менее, развеять его нельзя.")
		if summ_start_line != len(lines): lines.append("")

		if not hexes_desc and not abil_desc and not stats_part:
			lines.append("Это вы." if fighter == self.player else "На " + fighter.name.accusative + " не действует никаких эффектов.")
			lines.append("")
		lines.append("назад (<enter>)")

	def do_handle_command(self, cmd):
		if not cmd:
			self.revert()
		else:
			return False
		return True

class ChooseTarget(Mode):
	prev_mode = True

	def __init__(self, title, targets, name, cmd, extra, choose, help):
		super().__init__()
		self.title, self.targets, self.name, self.cmd, self.extra, self.choose, self.help = title, targets, name, cmd, extra, choose, help

	def do_render(self, lines, cmds):
		lines.append(self.title)
		lines.append("")

		desc = []
		for target in self.targets:
			cmd = self.cmd(target)
			extra = self.extra and self.extra(target)
			desc.append(multipad.escape(cap_first(self.name(target))) + " [cmd]({})".format(cmd) + (" [extra]" + multipad.escape(extra) if extra else ""))
			if cmds:
				def add_cmd(target=target):
					def cb():
						self.revert()
						self.choose(target)
					cmds.add(cmd, cb, '?', lambda: self.more(self.help(target)))
				add_cmd()
		if len(self.targets) > 1: desc.append("")
		desc.append("назад [cmd](quit)")
		if cmds: cmds.add('quit', lambda: self.revert(), '?', lambda: self.more("Передумать."))
		lines.extend(multipad(desc))

	def do_handle_command(self, cmd):
		if not cmd:
			self.revert()
		else:
			return super().do_handle_command(cmd)
		return True

class ChooseCommandOnSeparateScreen(GameMode):
	prev_mode = True

	def __init__(self, av):
		super().__init__(av.game)
		self.av = check(av, isinstance(av, ArenaView), "av")

	def do_render(self, lines, cmds):
		cmds_desc = self.av.build_commands(None)
		cmds_desc.append("назад [player_cmd](<enter>)")
		lines.extend(multipad(cmds_desc))

	def do_handle_command(self, cmd):
		if cmd: self.av.force_input = cmd
		self.revert().invalidate()
		return True

class BattleResults(NonCombatMode):
	def __init__(self, game, arena, outcome):
		super().__init__(game)
		self.arena, self.outcome = arena, outcome
		self.applied = False
		self.lines = None
		self.is_end = False

	@staticmethod
	def dscore_postfix(dscore, sign=True):
		return " [dscore_mp]({}{})".format("+" if sign and dscore > 0 else "", dscore) if dscore else ""

	def apply(self):
		assert not self.applied
		prev, prev_wpn, prev_gold = self.player.snapshot(), self.player.weapon and self.player.weapon.snapshot(), self.game.gold
		player_squad = Game.PLAYER_SQUAD
		self.lines = []
		player_xp = weapon_xp = None
		performance = self.game.performance

		alive_enemies = list(enemy for enemy in self.arena.enemies(self.player) if not enemy.transient)
		dead_enemies = list(c for c in self.arena.morgue if self.arena.squads_are_enemies(player_squad, c.squad_id))
		dead_enemies_enumeration = join_with_lastsep((corpse.fighter.name for corpse in dead_enemies), ", ", " и ")

		def detailed_title():
			return (", ".join(filter(None, (
				dead_enemies and dead_enemies_enumeration +
					" повержен{}".format(dead_enemies[0].fighter.gender.ize("{/а/о}") if len(dead_enemies) == 1 else "ы"),
				alive_enemies and (join_with_lastsep((e.name for e in alive_enemies), ", ", " и ") +
					" продолжа{}т стоять на пути".format("е" if len(alive_enemies) == 1 else "ю")))))).upper()

		if self.outcome == 'won':
			self.lines.append(detailed_title() or "ПОБЕДА")
			self.lines.append("")

			base_score = 50
			score = base_score
			score_desc = []
			def modify_score(delta, desc):
				nonlocal score
				score_desc.append(desc + self.dscore_postfix(delta))
				score += delta

			if performance.kiss:
				modify_score(+30, "Вы поцеловали {}.".format(performance.kiss.name.accusative))

			total = performance.unarmed.attacks + performance.melee.attacks + performance.ranged.attacks + performance.magical.attacks
			total_weight = performance.unarmed.weight + performance.melee.weight + performance.ranged.weight + performance.magical.weight
			if total:
				if performance.unarmed.attacks + performance.melee.attacks == total:
					modify_score(+30, "Вы сражались только врукопашную.")
				elif performance.melee.attacks + performance.ranged.attacks == total:
					modify_score(+30, "Вы сражались только оружием.")
				elif performance.magical.attacks == total:
					modify_score(+30, "Вы сражались только магией.")
				elif (total >= 6 and total_weight and
					(performance.unarmed.attacks + performance.melee.attacks) / total + (performance.unarmed.weight + performance.melee.weight) / total_weight > 1.6):
					modify_score(+20, "Вы сражались почти только врукопашную.")
				elif (total >= 6 and total_weight and
					(performance.melee.attacks + performance.ranged.attacks) / total + (performance.melee.weight + performance.ranged.weight) / total_weight > 1.6):
					modify_score(+20, "Вы сражались почти только оружием.")
				elif (total >= 6 and total_weight and
					(performance.magical.attacks) / total + (performance.magical.weight) / total_weight > 1.6):
					modify_score(+20, "Вы сражались почти только магией.")

			if (self.player.hp < self.player.mhp and (self.player.hp <= 2 or self.player.hp <= round(self.player.mhp * 0.15))
				and performance.starting_hp_percent > 0.5):
				modify_score(-clamp(round(self.player.mhp / (self.player.hp or 1)), 5, 15), "Вы едва уцелели.")

			if performance.escapes:
				modify_score(
					-round(sum((15 if i == 0 else 10 if i == 1 else 5) * min(1.2, severeness) for i, severeness in enumerate(performance.escapes))),
					"Вы{} сбегали из боя{}.".format(
					" " + ("дважды", "трижды", "четырежды")[len(performance.escapes) - 2] if 2 <= len(performance.escapes) <= 4 else "",
					plural(len(performance.escapes), " {N} раз{/а/}") if len(performance.escapes) > 4 else ""))

			if self.game.god_mode:
				score_desc.append("Вы в режиме отладки.")

			was_something = not not score_desc
			score_desc.insert(0, "{}{}".format("Победа." if score_desc else "Битва прошла нормально.",
				self.dscore_postfix(base_score, sign=False) if was_something else ""))
			self.lines.extend(multipad(score_desc))
			if was_something: self.lines.append("")

			unclamped_score = score
			score = clamp(score, 0, 100)

			grade = Game.grade_for_score(score)
			weight = self.arena.effective_enemies_xl(c.fighter for c in dead_enemies)
			fight, xp_percentage_mod = Game.CompletedFight(score, weight), grade.xp_percentage_mod

			self.lines.append("Рейтинг: {} ({}), {}{}.".format(grade.mark, unclamped_score if self.game.god_mode else score, grade.verbal_desc,
				", {}{:.0%} XP".format("+" if xp_percentage_mod >= 0 else "", xp_percentage_mod) if xp_percentage_mod else ""))
			self.lines.append("")

			level = self.game.next_level - 1
			self.game.completed_fights.extend(None for _i in range(len(self.game.completed_fights), level + 1))
			self.game.completed_fights[level] = fight

			player_xp = self.arena.xp_for(self.player, player_squad) * (1 + xp_percentage_mod)
			weapon_xp = self.player.weapon and self.arena.xp_for(self.player.weapon, player_squad) * (1 + xp_percentage_mod)

			self.player.receive_xp(player_xp)
			if weapon_xp: self.player.weapon.receive_xp(weapon_xp)
			self.game.give_gold(sum(200 + round(8 * corpse.fighter.xl ** 0.5) * 10 for corpse in dead_enemies))
			self.game.forget_arena()
			self.game.next_level += 1
			self.is_end = self.game.next_level > FixedLevels.count

		elif self.outcome == 'retreat' or self.outcome == 'godly_quit':
			if self.outcome == 'retreat':
				player_xp, xp_rel, gold, severeness = self.arena.retreat_penalty(self.game)
				self.player.drain_xp(player_xp, relative=xp_rel)
				if gold: self.game.take_gold(gold)
				performance.escapes.append(severeness)

				self.lines.append(detailed_title() or "ПОБЕГ")
				self.lines.append("")

				start = len(self.lines)
				if self.outcome == 'retreat':
					for enemy in alive_enemies:
						first_bar = True
						for bar_name, vcur, vmax, attr in filter(None, (("HP", enemy.hp, enemy.mhp, 'cur_hp'), enemy.has_magic() and ("MP", enemy.mp, enemy.mmp, 'cur_mp'))):
							heal = vcur < vmax and min(vmax - vcur, ceil(vmax * (1 / (3 + len(performance.escapes)))))
							if heal and heal > 0:
								enemy_name_or_pad = enemy.name.cap_first() + ":"
								if first_bar: first_bar = False
								else: enemy_name_or_pad = " " * len(enemy_name_or_pad)
								self.lines.append("{} {} {} {}/{} -> {}/{}".format(
									enemy_name_or_pad, bar_name, Con.vital_bar(vcur + heal, vmax, prev=vcur), vcur, vmax, vcur + heal, vmax))
								setattr(enemy, attr, vcur + heal)
				if len(self.lines) > start: self.lines.append("")

			elif self.outcome == 'godly_quit':
				self.lines.append("Бой прерван.")

			assert self.arena == self.game.hibernated_arena or (self.game.god_mode and not self.game.hibernated_arena), f"{self.arena} <-> {self.game.hibernated_arena}"
			self.arena.remove(self.arena.as_battler(self.player), self.arena.shadows)
			self.arena.cleanup_transient()

		else: impossible(self.outcome, 'outcome')

		with self.player.lock_hexes() as hexes:
			for hex in hexes:
				if isinstance(hex, (FetterHex, GraspHex)): hex.cancel()

		name_ljust = max(len(self.player.name), len(self.player.weapon.name) if weapon_xp else 0)
		if player_xp:
			self.lines.append(wrap(self.player.living_desc(prev=prev, short=True, name_ljust=name_ljust), self.safe_term_width))
			if False:
				self.lines.append(" " * (len(self.player.name) + 2) + self.player.hp_bar())
				if self.player.has_magic():
					self.lines.append(Respite.bars_pad(self.player) + self.player.mp_bar())
		if prev_gold != self.game.gold:
			abs_change = abs(self.game.gold - prev_gold)
			self.lines.append("{}{} ${} ({} ${})".format(" " * (2 + name_ljust) if player_xp else "",
				plural(abs_change, "получен{/ы/о}" if self.game.gold > prev_gold else "потерян{/ы/о}"), abs_change,
				"баланс:" if self.game.gold > prev_gold else plural(self.game.gold, "остал{ся/ись/ось}"), self.game.gold))
		self.lines.append("")

		if weapon_xp:
			self.lines.append(wrap(self.player.weapon.living_desc(prev=prev_wpn, short=True, name_ljust=name_ljust), self.safe_term_width))
			self.lines.append("")

		something = False
		count = len(self.lines)
		self.lines.extend(self.log.scroll(None, self.safe_term_width))
		something = something or len(self.lines) > count
		if something: self.lines.append("")

		self.applied = True

	def do_activate(self):
		super().do_activate()

		# Это ужасное место для передачи игроку опыта и прочего, в идеале этим должна заниматься арена. Но это было бы более громоздко.
		self.apply()

	def do_handle_note(self, msg):
		self.log.add(msg, start_new_line=True)

	def do_render(self, lines, cmds):
		assert self.applied
		lines.extend(self.lines)
		lines.append("продолжить (next)")
		cmds.add('next', lambda: self.proceed(), '?', lambda: self.more("Вернуться в лагерь."))

	def proceed(self):
		if self.is_end:
			timestamp = localtime()
			def quit(mode):
				mode.switch_to(MainMenu())

			mode = self
			if self.game.god_mode:
				mode.more("Вы в режиме отладки, рекорд не будет сохранён.").then(lambda mode: quit(mode))
				return

			summary_sxw = fsum(fight.score * fight.weight for fight in self.game.completed_fights if fight)
			summary_weight = fsum(fight.weight for fight in self.game.completed_fights if fight)
			summary_score = round(summary_sxw / summary_weight) if summary_weight else 0

			try:
				rec = HallOfFame.Record(str(self.player.name), self.player.weapon and str(self.player.weapon.name),
					[fight and HallOfFame.CompletedFight(Game.grade_for_score(fight.score).mark) for fight in self.game.completed_fights],
					summary_score,
					Game.grade_for_score(summary_score).mark,
					timestamp)
				rec_rowid = self.session.HoF.add(rec)

			except Exception as e:
				mode.more("Рекорд не сохранён.\n" + exception_msg(e)).then(quit)
				return

			def to_hof(mode):
				mode.switch_to(HallOfFameView(rec_rowid, rec, then=quit))

			if self.game.full_save_path and not self.game.god_mode:
				Game.remove_save_nothrow(self, self.game.full_save_path, self.game.rel_save_path, then=lambda success, mode: to_hof(mode))
				return

			to_hof(mode)
		else:
			self.game.save_nothrow(self, then=lambda success, mode: mode.switch_to(Respite(self.game)))

class FixedLevels:
	class One:
		index = None
		def populate(self, arena): self.do_populate(arena)
		def do_populate(self, arena): raise NotImplementedError("do_populate")

		def reference(self):
			arena = Arena()
			self.populate(arena)
			return arena.battlers[0].fighter

	class CaveRat(One):
		index = 1
		def do_populate(self, arena):
			rat = Fighter()
			rat.name, rat.gender, rat.preset = *Noun.parse("{пещерная крыса:af}", return_gender=True), 'rat'
			with rat.save_relative_vitals():
				rat.base_spd = 120
				rat.base_str = 8
				rat.set_unarmed(Teeth())
				rat.add_special(RageOnLowHP())
			arena.add(rat, Game.MONSTER_SQUAD, UniversalAI(), shortcut_hint="Rat")

	class ManEaterFlower(One):
		index = 2
		def do_populate(self, arena):
			flower = Fighter()
			flower.name, flower.gender, flower.preset = *Noun.parse("{человекоядный цветок}", return_gender=True), 'flower'
			with flower.save_relative_vitals():
				flower.xl = 2
				flower.base_ac = 3
				flower.base_ev = 5
				flower.base_str = 13
				flower.set_unarmed(Spines())
			arena.add(flower, Game.MONSTER_SQUAD, UniversalAI(), shortcut_hint="Flower")

	class Thief(One):
		index = 3
		def do_populate(self, arena):
			thief = Fighter()
			thief.name, thief.gender, thief.preset = *Noun.parse("{вор:a}", return_gender=True), 'thief'
			with thief.save_relative_vitals():
				thief.xl = 3
				thief.base_ac = 5
				thief.base_str = 12
				thief.base_int = 10
				thief.base_dex = 20
				thief.base_spd = 150
				thief.set_weapon(Dagger(coating='poison'))
				thief.add_special(Thievery())
			arena.add(thief, Game.MONSTER_SQUAD, UniversalAI(), shortcut_hint="Thief")

	class Bear(One):
		index = 4
		def do_populate(self, arena):
			bear = Fighter()
			bear.name, bear.gender, bear.preset = *Noun.parse("{медведь:a}", return_gender=True), 'bear'
			with bear.save_relative_vitals():
				bear.xl = 3
				bear.base_ac = 10
				bear.base_ev = 7
				bear.base_str = 20
				bear.set_unarmed(TeethAndClaws())
				bear.add_special(RageOnLowHP(red_zone=0.35))
			arena.add(bear, Game.MONSTER_SQUAD, UniversalAI(), shortcut_hint="Bear")

	class Executioner(One):
		index = 5
		def do_populate(self, arena):
			executioner = Fighter()
			executioner.name, executioner.gender, executioner.preset = *Noun.parse("{палач:a}", return_gender=True), 'executioner'
			with executioner.save_relative_vitals():
				executioner.xl = 4
				executioner.base_ac = 12
				executioner.base_ev = 9
				executioner.base_str = 20
				executioner.base_int = 20
				executioner.set_weapon(ExecutionerAxe())
				executioner.learn_spell(Fetter())
				executioner.learn_spell(DeathWord())
			arena.add(executioner, Game.MONSTER_SQUAD, UniversalAI(), shortcut_hint="Executioner")

	class Tentacle(One):
		index = 6
		def do_populate(self, arena):
			tentacle = Fighter()
			tentacle.name, tentacle.gender, tentacle.preset = *Noun.parse("{щупальце:n}", return_gender=True), 'tentacle'
			with tentacle.save_relative_vitals():
				tentacle.xl = 5
				tentacle.base_ac = 4
				tentacle.base_ev = 4
				tentacle.base_str = 25
				tentacle.base_dex = 15
				tentacle.base_spd = 130
				tentacle.set_unarmed(SlimyTouch())
				tentacle.add_special(Grasp())
				tentacle.add_special(Impregnation())
			arena.add(tentacle, Game.MONSTER_SQUAD, UniversalAI(), shortcut_hint="Tentacle")

	class Necromancer(One):
		index = 7
		def do_populate(self, arena):
			necromancer = Fighter()
			necromancer.name, necromancer.gender, necromancer.preset = *Noun.parse("{некромант:a}", return_gender=True), 'necromancer'
			with necromancer.save_relative_vitals():
				necromancer.xl = 5
				necromancer.base_ac = 5
				necromancer.base_str = 20
				necromancer.base_int = 25
				necromancer.base_spd = 140
				necromancer.set_weapon(Dagger())
				necromancer.learn_spell(PhantasmalGate())
				necromancer.learn_spell(DrainLife())
			arena.add(necromancer, Game.MONSTER_SQUAD, UniversalAI(), shortcut_hint="Necromancer")

	class MasterThief(One):
		index = 8
		def do_populate(self, arena):
			thief = Fighter()
			thief.name, thief.gender, thief.preset = *Noun.parse("{мастер:a}-{вор:a}", return_gender=True), 'm.thief'
			with thief.save_relative_vitals():
				thief.xl = 6
				thief.base_ac = 4
				thief.base_ev = 11
				thief.base_str = 15
				thief.base_int = 20
				thief.base_dex = 30
				thief.base_spd = 220
				thief.set_weapon(Dagger(coating='poison2'))
				thief.add_special(Thievery())
				thief.add_special(Marauding())
				thief.add_special(PsionicThievery())
			arena.add(thief, Game.MONSTER_SQUAD, UniversalAI(), shortcut_hint="Masterthief")

	class Magius(One):
		index = 9
		def do_populate(self, arena):
			magius = Fighter()
			magius.name, magius.gender, magius.preset = *Noun.parse("{Магиус:a}", return_gender=True), 'magius'
			with magius.save_relative_vitals():
				magius.xl = 6
				magius.base_ac = 4
				magius.base_ev = 8
				magius.base_str = 20
				magius.base_int = 30
				magius.base_dex = 15
				magius.base_spd = 160
				magius.set_weapon(Dagger(coating='runes'))
				magius.learn_spell(Barrier())
				magius.learn_spell(BallLightning())
				magius.learn_spell(Chronosphere())
			arena.add(magius, Game.MONSTER_SQUAD, UniversalAI(), shortcut_hint="Magius")

	class Death(One):
		index = 10
		def do_populate(self, arena):
			death = Fighter()
			death.name, death.gender, death.preset = *Noun.parse("{Смерть:af}", return_gender=True), 'death'
			with death.save_relative_vitals():
				death.xl = 7
				death.base_ac = 9
				death.base_str = 30
				death.base_int = 30
				death.base_spd = 150
				death.set_weapon(DeathScythe())
				death.learn_spell(DrainXP())
				death.learn_spell(DeathWord())
			arena.add(death, Game.MONSTER_SQUAD, UniversalAI(), shortcut_hint="Death")

	# динамически выставляются ниже
	count = 0
	level = staticmethod(lambda level_no: None)

def alter(FixedLevels):
	levels_gen = lambda: (lv for lv in FixedLevels.__dict__.values() if isinstance(lv, type) and issubclass(lv, FixedLevels.One) and lv is not FixedLevels.One)
	count = max(lv.index for lv in levels_gen())

	@staticmethod
	def level(level_no):
		lv = next((lv for lv in levels_gen() if lv.index == level_no), None)
		if not lv: raise ValueError(f"Уровень {level_no} не найден. ({1}–{count})")
		return lv()

	setattrs(FixedLevels, dict(level=level, count=count))
alter(FixedLevels); del alter

class AskName(Prompt):
	MAX_NAME_LENGTH = 35

	def __init__(self, game, who=None, fixed=None, prompt_prefix="", prev=None):
		self.game, self.who, self.prompt_prefix = game, who or game.player, prompt_prefix
		super().__init__(lambda: self.build_prompt(), lambda input, mode: self.handle_name_input(input, mode), casefold_input=False)
		self.fixed, self.fixed_name_rejected = fixed, False

	def build_prompt(self):
		return self.prompt_prefix + (
			"Вам нужно зарегистрироваться, прежде чем вас официально освободят.\nКак вас зовут?{quit_hint} " if self.who == self.game.player else
			"\nНазовите свой автомат, {player_name}{quit_hint}: " if self.who == self.game.player.weapon else
			impossible(self.who, "who")).format(player_name=self.game.player.name, quit_hint=" (quit — назад)" if self.session.globals.quit_hint_stage == 1 else "")

	def handle_name_input(self, input, mode):
		MIN_WITHOUT_CONFIRMATION = 3
		gender = Gender.UNKNOWN
		fixed_proposed = False
		if self.who == self.game.player: self.fixed = None

		if input and 'quit'.startswith(input):
			self.session.globals.quit_hint_stage = 2
			mode.revert()
		elif not input or len(input) <= self.MAX_NAME_LENGTH:
			if input:
				name = cap_first(input) if self.who == self.game.player else input
				if input == name and len(name) >= MIN_WITHOUT_CONFIRMATION: self.complete_name(name, gender, mode); return
			else:
				if self.who == self.game.player:
					# ну не дёргать же update на каждую has_namesakes_of, лучше уж руками.
					# previews.has_namesakes_of также проверяется в query_random_fixed_name.
					mode.session.previews.update()
					self.fixed = not self.fixed_name_rejected and mode.session.globals.recent_fixed_name_proposals < 1 and self.query_random_fixed_name()
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
							mode.more("Случайные имена закончились. Пожалуйста, придумайте своё.")
							self.bookkeep_quit_hint_stage()
							return
				elif self.who == self.game.player.weapon:
					if self.fixed and isinstance(self.fixed, tuple) and len(self.fixed) >= 2 and not self.fixed_name_rejected:
						name_src = choose(self.fixed[1]) if isinstance(self.fixed[1], tuple) else self.fixed[1]
						(name, gender), fixed_proposed = Noun.parse(name_src, gender=Gender.MALE, return_gender=True), True
					else:
						name, gender = Noun.parse("{Хуец}" if self.game.player.gender == Gender.FEMALE else "GAU-17", gender=Gender.MALE, return_gender=True)
				else: impossible(self.who, "who")

			def rejected(mode):
				if fixed_proposed:
					self.fixed_name_rejected = True
					if self.who == self.game.player: self.fixed = None
				self.bookkeep_quit_hint_stage()
				mode.revert()
			mode.yes_no(
				"{0} {1}".format(
					(f"Очень приятно, {name}." if input else f"Ваше имя — {name}.") if self.who == self.game.player else
					(f"В ваших руках {name}." if input else f"Имя вашего автомата — {name}.") if self.who == self.game.player.weapon else impossible(self.who, "who"),
					"Всё верно?" if input else "Продолжить?"),
					lambda mode: self.complete_name(name, gender, mode),
					no_cb=rejected, default=0 if not input or len(input) >= MIN_WITHOUT_CONFIRMATION else 1)
		else:
			mode.more("{0}. Длина имени должна быть не более {1}, либо \"q\"uit.".format(
				plural(len(input), "Введ{ён/ено/ено} {N} символ{/а/ов}"), plural(self.MAX_NAME_LENGTH, "{N} символ{/а/ов}")))

	def bookkeep_quit_hint_stage(self):
		if self.session.globals.quit_hint_stage < 2: self.session.globals.quit_hint_stage += 1

	def complete_name(self, name, gender, mode):
		prefix = ""
		def normalize_name(s):
			return s.casefold().replace("ё", "е")

		# Найти среди предопределённых имён, даже если оно просто введено с клавиатуры.
		if gender == Gender.UNKNOWN and self.who == self.game.player and not isinstance(name, Noun):
			for index, fixed in enumerate(self.fixed_names):
				f_name, f_gender = self.parse_fixed_player_name(fixed)
				if normalize_name(f_name) == normalize_name(name):
					with suppress(ValueError): self.session.globals.last_fixed_names_seen.remove(index)
					self.session.globals.last_fixed_names_seen.append(index)
					self.fixed, (name, gender) = fixed, (name, f_gender)
					prefix = ":3\n"
					break

		if gender == Gender.UNKNOWN and self.who == self.game.player:
			default_gender = Gender.detect(name)
			mode.prompt("{0}Вы мальчик или девочка? ({1}/q) ".format(prefix, highlight_variant("m/f", default_gender)),
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
			self.session.switch_to(AskName(self.game, self.game.player.weapon, fixed=self.fixed, prompt_prefix=prefix, prev=self))
		elif self.who == self.game.player.weapon:
			self.game.save_nothrow(self, then=lambda success, mode: mode.switch_to(Respite(self.game)))
		else:
			impossible(self.who, "who")

	fixed_names = \
	(
		("{Рика:f}", "<photon eraser>"),
		("{Мадока:f}", ("{Розочка:f}",)),
		("{Фрисия:f}", "{Хвост}"),
		("{Снегирёк:f}", "DEATH WING"),
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
class Session():
	def __init__(self, start=None):
		self.mode               = None
		self.quit_posted        = False
		self.cls_once_requested = False
		self.term_width = self.term_height = self.safe_term_width = None
		self.previews           = PreviewsList()
		self.HoF                = HallOfFame()
		self.globals            = Globals()
		self.inside_switch_to   = False
		self.switch_to(start or MainMenu())

	def switch_to(self, new_mode, reverting=False):
		check(isinstance(new_mode.prev_mode, bool) or new_mode == self.mode.prev_mode, "prev_mode?!", not self.inside_switch_to, "рекурсивный Session.switch_to")
		self.inside_switch_to = True
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
		self.inside_switch_to = False

	def revert(self, n=1):
		check(n > 0, "n?!")
		mode = self.mode
		while n > 0:
			mode = check(mode.prev_mode, isinstance(mode.prev_mode, Mode), "prev_mode?!")
			n -= 1
			self.switch_to(mode, reverting=True)
		return self.cls_once()

	def process(self):
		if self.quit_posted: return False

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

		if mode.force_input is None:
			# вся эта движуха с lines — раньше render() без задней мысли выводил всё print'ами —
			# нужна была для того, чтобы минимизировать время между cls и рисованием нового «экрана».
			# Можно было бы сделать двойную буферизацию, если бы был кроссплатформенный способ перемещать курсор в консоли...
			# (TODO: сделать её опционально.)
			if mode.do_cls or self.cls_once_requested: cls()
			print(screen, end='')
			self.cls_once_requested = False
		# ↑ а такие вот танцы с force_input в этом методе (как и сама force_input) нужны для работы ChooseCommandOnSeparateScreen.
		# Ввод экрана A передаётся B через force_input, как будто изначально был введён в B, и при этом не нужно моргать старой картинкой B лишний раз.

		had_custom_commands = cmds.has_anything()
		if had_custom_commands: self.add_default_commands(cmds)
		if mode.force_input is not None:
			cmd, mode.force_input = mode.force_input, None
		else:
			try:
				cmd = input()
			except SystemExit:
				self.post_quit()
				raise
		mode.last_input = cmd

		fn, matches, suggestions = cmds.guess(cmd)
		with catch_warnings(record=True) as warnings:
			if fn:
				def execute():
					mode.last_command_chosen, mode.input_on_last_command_chosen = matches[0], cmd
					fn()

				# Если, скажем, игрок использовал команду h, подразумевая hit, получил оковы и h стала означать shoot — на повторный ввод h спросить подтверждение.
				if (cmd and mode.input_on_last_command_chosen == cmd and matches and len(matches) == 1 and mode.last_command_chosen != matches[0]
					and common_prefix_len(mode.last_command_chosen, matches[0]) <= 2):
					self.mode.yes_no("Это значило {}, но теперь значит {}. Вы уверены?".format(mode.last_command_chosen, matches[0]),
						lambda mode: (mode.revert() or True) and execute(), default=1)
				else:
					execute()
			elif mode.handle_command(cmd): pass
			elif matches: mode.more("Неоднозначная команда: {0}.".format(", ".join(matches)))
			elif suggestions: mode.more("Неизвестная команда. Попробуйте {0}.".format(", ".join(suggestions)))
			elif cmd and not cmd.isspace(): mode.more("Неизвестная команда." + (" Попробуйте \"?\"." if had_custom_commands else ""))
			if warnings: self.mode.more("\n".join(str(warning.message) for warning in warnings))
		return not self.quit_posted

	def close(self):
		self.HoF.close()

	def post_quit(self):
		self.quit_posted = True

	def check_term_size(self):
		min_term_width, min_term_height = 80, 25
		if self.term_width < min_term_width or self.term_height < min_term_height:
			self.mode.more(
				f"Размер консоли — {self.term_width}x{self.term_height}.\n"\
				f"Увеличьте хотя бы до {min_term_width}x{min_term_height}.", do_cls=True)

	def add_default_commands(self, cmds):
		cmds.add("?", lambda: self.mode.more(self.list_available_commands(cmds)))

	def list_available_commands(self, cmds):
		enumeration = ", ".join(cmd for cmd in cmds.suggest_something() if cmd != "?")
		return "Доступные команды: {}.".format(enumeration) if enumeration else "Нет доступных команд."

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
		lines.extend((mode.last_screen or "") + (mode.last_input or "") for mode in reversed(chain) if mode.last_screen is not None)

	def handle_command(self, cmd, mode):
		if cmd == '/' and isinstance(mode, GameMode) and mode.game.god_mode:
			self.Exec(mode).prompt(mode)
		else:
			return False
		return True

	# Интерфейс к интерпретатору Питона, позволяющий внести произвольные, горячие изменения в состояние игры (player.name = ...).
	# Разумеется, требует game.god_mode :^)
	class Exec:
		def __init__(self, mode):
			self.lines, self.mode, self.reverts = [], mode, 0

		def prompt(self, mode):
			if self.mode.exec_env is None: self.mode.exec_env = {**self.mode.__dict__, **globals()}

			# Я видел баг, когда первой строкой вдруг начинает выводиться ... вместо >>>.
			# Это не критично само по себе, но может свидетельствовать о серьёзной ошибке в handle_line, разбалансирующей lines и reverts.
			# (Неудивительно, handle_line не образцово написана.)
			# Чтобы когда-нибудь его поймать, оставил первую лямбду лямбдой (а до этого должен сработать ассерт в начале handle_line).
			mode.prompt(lambda: "... " if self.lines else "Python {}.{}\nСправка: ?\n\n>>> ".format(*sys.version_info[:2]),
				lambda input, mode: self.handle_line(input, mode), strip_input=False, casefold_input=False)

		def reset(self):
			self.lines.clear()
			self.reverts = 0

		def handle_line(self, input, mode):
			assert len(self.lines) == self.reverts, f"lines: {len(self.lines)}, reverts: {self.reverts}"

			handled = True
			if not self.lines and not input or input and 'quit'.startswith(input):
				mode.revert(1 + self.reverts)
			elif input == '?':
				mode.more((
					"{cmds}\n"
					"(q)uit — выход\n"
					"(r)evert — стереть последнюю строку\n").format(
						cmds=", ".join(filter(None, (
							"game — игра", "player — игрок", hasattr(self.mode, 'arena') and "arena — арена")))))
			elif input and 'revert'.startswith(input):
				if self.lines:
					mode.revert()
					self.lines.pop()
					self.reverts -= 1
				else: mode.invalidate()
			else: handled = False
			if handled: return

			self.lines.append(input)
			source = "\n".join(self.lines)
			outcome = completed_mode = result = None

			try:
				# Э-ээ, у меня такое ощущение, что compile_command на каком-то этапе добавляет тупой print, независимо от параметра symbol.
				# Так что exec/eval'ить её результат нельзя. По нему только выносится суждение о завершённости введённого куска,
				# и он повторно передаётся в нормальный compile().
				if code.compile_command(source):
					for cmode, runf in (('eval', eval), ('exec', exec)):
						try:
							cc = compile(source, "<input>", cmode)
						except Exception as e:
							if cmode == 'exec': raise
						else:
							outcome, completed_mode = 'completed', cmode
							result = runf(cc, self.mode.exec_env)
							break
				else:
					outcome = 'incompleted'
			except Exception as e:
				handled, reset = False, True
				# Подсветить строкф и символ с ошибкой, как это делает стандартный интерпретатор.
				#                 ^
				#                 вот так.
				if outcome is None and isinstance(e, SyntaxError) and len(e.args) == 2:
					message, args2 = e.args
					if isinstance(args2, tuple) and len(args2) == 4:
						lineno, offset, text = args2[1], args2[2], args2[3]
						if isinstance(lineno, int) and isinstance(offset, int):
							if text is None and 1 <= lineno <= len(self.lines): text = self.lines[lineno-1]
							if isinstance(text, str) and 0 <= offset <= len(text):
								# Если ошибка в только что введённой строке — откатить только её.
								if self.lines and lineno == len(self.lines):
									self.lines.pop()
									reverts, reset = 0, False
								else:
									reverts = self.reverts

								borrow_pad = max(0, min(len(text) - len(text.lstrip()), offset - 1))
								mode.more("{}\n{pad}^\n{pad}{}".format(text.rstrip(), message, pad=text[:borrow_pad] + " " * (offset - 1 - borrow_pad))).reverts(reverts)
								handled = True
				if not handled: mode.more(exception_msg(e)).reverts(self.reverts)
				if reset: self.reset()
			else:
				if outcome == 'completed':
					if completed_mode == 'eval' and result is not None: mode.more(str(result)).reverts(self.reverts)
					elif self.reverts: mode.revert(self.reverts)
					else: mode.invalidate()
					self.reset()
				elif outcome == 'incompleted':
					self.reverts += 1
					self.prompt(mode) # запрос следующей строчки
				else: impossible(outcome, "outcome")

# Список всех сохранений.
# Хранится в session (и вообще нужен) для того, чтобы не перечитывать их на каждый чих, такой как генерация нового order_key
# (и, наоборот, обновлять при необходимости).
# Если пользователь не будет хулиганить в папке save, каждое сохранение прочитается максимум по одному разу за сеанс,
# поскольку Game.save и подобные методы дружат со списком и уведомляют его об изменениях.
# Изменения в случае хулиганства (и в первый раз) обнаруживаются по os.scandir(), так что механизм можно обмануть;
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

		def load_screen_desc(self, session, npad=0, first_line_extra=None, display_order_key=False):
			star = "" if self.seen else "*NEW* "
			pad = ' ' * (npad + len(star))
			if self.bad:
				lines = [line for e in self.bad for line in exception_msg(e).splitlines()]
				if not any(isinstance(e, BadDataError) for e in self.bad) and not any('оврежд' in line or 'orrupt' in line for line in lines):
					lines.insert(0, "Файл повреждён.")
				lines.append("[{}]".format(self.full_save_path))
			else:
				pv = self.preview
				timestamp = human_datetime(pv.timestamp)
				namesake = f"-{1+self.namesake_index}" if self.namesake_index >= 1 else ""

				lines = [
					"{ts}{okey}".format(ts=timestamp, okey=f" (order_key: {pv.order_key}, character_uid: {pv.character_uid})" if display_order_key else ""),
					"{pn}{namesake} {pl}".format(pn=cap_first(pv.player_name), namesake=namesake, pl=Living.xl_desc(None, pv.player_level, pv.player_next, short=True))]
				if pv.weapon_name is not None:
					lines.append("{wn} {wl}".format(wn=cap_first(pv.weapon_name), wl=Living.xl_desc(None, pv.weapon_level, pv.weapon_next, short=True)))
				lines.append(
					"{gm}D:{coming} {gold}".format(gm=Game.marks(pv, rspace=True), coming=pv.next_level, gold=Game.gold_str(None, pv.gold)))

			lines[0] = star + lines[0]
			if first_line_extra: lines[0] += " " * clamp(session.safe_term_width - len(lines[0]) - len(first_line_extra), 1, 3) + first_line_extra
			return ("\n" + pad).join(lines)

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
		listing = sorted(Game.scan_saves()) # os.scandir выдаёт произвольный порядок, для сравнений нужно сделать не произвольный
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
				item = PreviewsList.Item(path.join(Game.SAVE_FOLDER, rel_path), rel_path)
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
		item = self.fn2it.get(rel_save_path, None)
		if item:
			self.warn("add", rel_save_path, False)
			self.trusted_remove(item)
		self.trusted_add(full_save_path, rel_save_path, preview)
		assert self.sanitycheck()

	def note_update(self, full_save_path, rel_save_path, preview, new_full_save_path=None, new_rel_save_path=None):
		assert self.sanitycheck()
		item = self.fn2it.get(rel_save_path, None)
		if item:
			assert full_save_path == item.full_save_path, f"{full_save_path} <-> {item.full_save_path}"
			assert rel_save_path == item.rel_save_path, f"{rel_save_path} <-> {item.rel_save_path}"
			self.trusted_update(item, preview, new_full_save_path, new_rel_save_path)
		else:
			self.warn("update", rel_save_path, True)
			self.trusted_add(new_full_save_path or full_save_path, new_rel_save_path or rel_save_path, preview)
		assert self.sanitycheck()

	def note_remove(self, rel_path_or_item):
		assert self.sanitycheck()
		if isinstance(rel_path_or_item, str):
			rel_save_path = rel_path_or_item
			item = self.fn2it.get(rel_save_path, None)
			if not item: self.warn("remove", rel_save_path, True); return
		elif isinstance(rel_path_or_item, PreviewsList.Item):
			item = rel_path_or_item
			if item.rel_save_path not in self.fn2it: self.warn("remove", item.rel_save_path, True); return
		else: impossible(item, 'item')

		self.trusted_remove(item)
		assert self.sanitycheck()

	def warn(self, routine, rel_save_path, expected_to_exist):
		warn("Сохранени{} \"{}\" {} существовало! ({})".format("я" if expected_to_exist else "е", rel_save_path, "не" if expected_to_exist else "уже", routine))

	def trusted_add(self, full_save_path, rel_save_path, preview):
		check(full_save_path, "full_save_path?!", rel_save_path, "rel_save_path?!")
		check(full_save_path, full_save_path.startswith(Game.SAVE_FOLDER), "абсолютный плес")
		check(rel_save_path, not rel_save_path.startswith(Game.SAVE_FOLDER) and full_save_path.endswith(rel_save_path), "относительный плес")

		item = PreviewsList.Item(full_save_path, rel_save_path)
		item.preview = preview
		item.index = self.find_position_for(item)
		item.seen = True

		self.items.insert(item.index, item)
		self.fix_indices(item.index + 1)
		self.fn2it[rel_save_path] = item
		insort_right(self.last_listing, rel_save_path)

		self.max_order_key = max(self.max_order_key, preview.order_key)
		self.update_namesakes(of=item.preview.player_name)

	def trusted_update(self, item, preview, new_full_save_path=None, new_rel_save_path=None):
		if new_rel_save_path is not None:
			assert new_full_save_path is not None
			assert new_rel_save_path not in self.fn2it, "сохранение {0} уже существует".format(new_rel_save_path)
			rel_save_path = item.rel_save_path
			item.full_save_path, item.rel_save_path = new_full_save_path, new_rel_save_path

			del self.fn2it[rel_save_path]
			self.fn2it[new_rel_save_path] = item

			del self.last_listing[self.last_listing_index(rel_save_path)]
			insort_right(self.last_listing, new_rel_save_path)
		item.preview, item.bad = preview, None

	def trusted_remove(self, item):
		assert item is self.items[item.index], "сбился индекс"
		del self.fn2it[item.rel_save_path]
		del self.items[item.index]
		self.fix_indices(item.index)
		del self.last_listing[self.last_listing_index(item.rel_save_path)]
		if item.preview: self.bookkeep_removed_preview(item.preview)

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
		item = self.fn2it.get(rel_save_path, None)
		if item:
			return item.preview.order_key
		else:
			if rel_save_path: self.warn("choose_order_key", rel_save_path, True)
			self.update()
			return self.max_order_key + 1

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
		self.last_fixed_names_seen       = deque(maxlen=min(12, (len(AskName.fixed_names) + 1) // 2))
		self.last_random_name_parts_seen = deque(maxlen=24)
		self.last_answers = {}
		self.quit_hint_stage = 0 # 0 — пока не отображается, 1 — отображается, 2 — уже не отображается

	def highlight_answer(self, id, pattern="y/n", default=1):
		last_answer = self.last_answers.get(id, None)
		return highlight_variant(pattern, last_answer if last_answer is not None else default)

	def judge_answer(self, id, input, default=1):
		if input:
			answer = 0 if 'yes'.startswith(input) else 1
			self.last_answers[id] = answer
		else:
			answer = self.last_answers.get(id, default)
		return answer

# Зал славы. По аналогии со списком сохранений, экземпляр хранится в Session.
# После завершения игры нужно добавить сюда игрока, а затем отобразить зал, проскролленный на позицию в отсортированных списках, на которой оказался игрок.
# На SQLite это проблема (либо я не знаю способа),
# но было решено героически продолжать есть кактус и устраивать цирк с >, = >, = = > и HallOfFameView.do_process.
class HallOfFame:
	class CompletedFight:
		def __init__(self, mark):
			self.mark = mark

	class Record:
		__slots__ = COLUMNS = 'name', 'wpn_name', 'fights', 'score', 'score_mark', 'timestamp'
		def __init__(self, name, wpn_name, fights, score, score_mark, timestamp):
			self.name, self.wpn_name, self.fights, self.score, self.score_mark, self.timestamp = name, wpn_name, fights, score, score_mark, timestamp

	def __init__(self):
		self.filename = path.join(Game.SAVE_FOLDER, "殿堂")
		self.db = None

	def cursor(self, force=True):
		db = self.open(force=force)
		return closing(db.cursor()) if db else nullcontext()

	def open_db_file(self, path, existing=False):
		if not existing: Game.ensure_save_folder()
		return sqlite3.connect("file:{}?mode={}".format(pathname2url(path), "rw" if existing else "rwc"), uri=True, isolation_level=None)

	TABLES = (
		('t_records', *Record.COLUMNS),
		('t_meta', 'version'))

	INDEXES = (
		('i_records_in_score_order', 't_records', 'score', 'timestamp'),
		('i_records_in_timestamp_order', 't_records', 'timestamp', 'score'))

	# Q: Закрывается ли соединение, и где? A: Да какая разница?
	# (Ну, на самом деле сейчас оно таки закрывается в Session.close.)
	def open(self, force=True):
		if self.db: return self.db

		new = False
		try:
			self.db = self.open_db_file(self.filename, True)
		except sqlite3.OperationalError:
			# Файла не существовало.
			# Может быть любая другая проблема. Я не знаю, как отличить.
			# Можно проверять str(e) == "unable to open database file", но такая проверка будет первым, что сломается.
			if not force: return None

			self.db = self.open_db_file(self.filename, False)
			new = True

		try:
			with self.cursor() as cur:
				# Надёжность не нужна, выключить разную ерунду, дающую очереди диска на ровном месте (https://blog.devart.com/increasing-sqlite-performance.html).
				for k, v in dict(temp_store='memory', journal_mode='memory', synchronous='off', locking_mode='exclusive').items():
					cur.execute("pragma {} = {}".format(k, v))

				if new:
					# Создать пустые таблички.
					cur.execute("pragma auto_vacuum = full")
					for name, *columns in self.TABLES:
						cur.execute("create table {0}({1})".format(name, ", ".join(columns)))
					self.insert('t_meta', version=HoF_version)

					for name, table_name, *columns in self.INDEXES:
						cur.execute("create index {0} on {1}({2})".format(name, table_name, ", ".join(columns)))
				else:
					# Сначала проверить версию, если она есть (если нет — провалится проверка структуры).
					with suppress(sqlite3.OperationalError):
						ver = cur.execute("select version from t_meta").fetchone()
						if ver and ver[0] != HoF_version: raise BadVersionError("Несовместимая версия таблицы рекордов.")

					# Проверить структуру.
					expected = {(type, name): items for type, schema_part in (('table', self.TABLES), ('index', self.INDEXES)) for name, *items in schema_part}
					for type, name, tbl_name in cur.execute("select type, name, tbl_name from sqlite_master where name not like 'sqlite_%'"):
						try:
							items = expected.pop((type, name))
						except KeyError as e:
							raise self.corrupted(f"{type}:{name}") from e

						def verify_columns_with_pragma(expected, pragma_column):
							with self.cursor() as info_cur:
								ok, bad_column = self.column_names_match(expected, map(itemgetter(pragma_column), info_cur.execute(f"pragma {type}_info({name})")))
								if not ok: raise self.corrupted(f"{name}:{bad_column}")

						if type == 'table':
							verify_columns_with_pragma(items, 1)
							if name in ('t_meta',):
								count = self.count(name)
								if count != 1: raise self.corrupted(f"{name}({count})")
						elif type == 'index':
							expected_table, *expected_columns = items
							if expected_table != tbl_name: raise self.corrupted(f"{name}:{expected_table}")
							verify_columns_with_pragma(expected_columns, 2)
						else: impossible(type, "type")
					if expected: raise self.corrupted(next(name for type, name in expected))
		except:
			self.close()
			raise

		return self.db

	def close(self):
		if self.db:
			self.db.close()
			self.db = None

	def has_anything_to_display(self):
		try:
			return self.count()
		except (sqlite3.Error, BadDataError):
			return True # :^)

	def completed_once(self):
		try:
			return self.count()
		except (sqlite3.Error, BadDataError):
			return False

	def add(self, rec):
		return self.insert('t_records', **self.rec_to_columns(rec))

	def rec_to_columns(self, rec, columns=None):
		return {k:
			pickle_dump([f and f.mark for f in v]) if k == 'fights' else
			self.pack_time(v) if k == 'timestamp' else
			v
			for k, v in getattrs(rec, columns or rec.COLUMNS)}

	def count(self, table='t_records'):
		with self.cursor(force=False) as cur:
			return cur.execute("select count(*) from {}".format(table)).fetchone()[0] if cur else 0

	def offset(self, rec, rowid, order):
		fields = self.fields_order(order)

		# Вообще мне нужен ПОРЯДКОВЫЙ НОМЕР в выдаче ORDER BY.
		# Поскольку встроенная в Python версия SQLite этого не поддерживает,
		# да и вообще SQLite стала поддерживать ROW_NUMBER() в транке буквально на днях (август 2018 / v3.25.0, https://stackoverflow.com/a/51863033), чего уж там,
		# результат эмулируется как
		#
		# select count (*) from `t_records` where
		# 	`score` > :score or
		# 	`score` = :score and `time` > :time or
		# 	`score` = :score and `time` = :time and `rowid` > :rowid
		#
		# где список полей — зд. score, time, rowid — и их референсные значения задаются извне.

		with self.cursor(force=False) as cur:
			return cur.execute((
				"select count(*) from t_records where\n"
				"	{}").format(
					" or\n	".join(" and ".join(
						"{0} {1} :{0}".format(field, '=' if field_index + 1 < count else '>')
						for field_index, field in enumerate(fields[:count]))
					for count in range(1, 1 + len(fields)))),
				dict(**self.rec_to_columns(rec, ('score', 'timestamp')), rowid=rowid)).fetchone()[0] if cur else 0

	def fields_order(self, order):
		return (
			('score', 'timestamp') if order == 'score' else
			('timestamp', 'score') if order == 'time' else impossible(order, "order")) + ('rowid',)

	def fetch(self, order, offset=0, reverse=False):
		with self.cursor(force=False) as cur:
			if not cur: return
			use_offset = offset > 0

			for rowid, name, wpn_name, fights, score, score_mark, timestamp in cur.execute((
				"select rowid, {record_columns} from t_records\n"
				"	order by {order}{offset}").format(
					record_columns=", ".join(self.Record.COLUMNS),
					order=", ".join("{}{}".format(f, "" if reverse else " desc") for f in self.fields_order(order)),
					offset=" limit -1 offset :offset" if use_offset else ""),
				{**({'offset': offset} if use_offset else {})}):

				# Q: Когда закроется with-нутый cur, если генератор не проитерировался до конца? A: Да мне насрать.
				yield rowid, self.Record(
					name if self.name_ok(name) else throw(self.corrupted("name")),
					wpn_name or None if self.name_ok(wpn_name, optional=True) else throw(self.corrupted("wpn_name")),
					[None if mark is None else self.CompletedFight(mark if self.mark_ok(mark) else throw(self.corrupted("mark"))) for mark in pickle.loads(fights)]
						if isinstance(fights, bytes) else throw(self.corrupted("fights")),
					score if isinstance(score, int) and -1000 <= score <= 1000 else throw(self.corrupted("score")),
					score_mark if self.mark_ok(score_mark) else throw(self.corrupted("score_mark")),
					self.unpack_time(timestamp) if isinstance(timestamp, str) else throw(self.corrupted("timestamp")))

	def clear(self):
		with self.cursor(force=False) as cur:
			if cur: cur.execute("delete from t_records")

	def column_names_match(self, expected, actual):
		actual_gen = iter(actual)
		for stage in range(2):
			for exp_name in expected if stage == 0 else (None,):
				try:
					act_name = next(actual_gen)
				except StopIteration:
					return stage == 1, exp_name
				if stage == 1 or exp_name != act_name: return False, act_name if stage == 1 else exp_name

	def insert(self, table, **values):
		with self.cursor() as cur:
			return cur.execute(
				"insert into {0}({1}) values({2})".format(table, ", ".join(values), ", ".join(":" + col for col in values)),
				values).lastrowid

	def corrupted(self, what=None):
		return BadDataError("Таблица рекордов повреждена{}.".format(f" ({what})" if what else ""))

	def name_ok(self, name, optional=False): return isinstance(name, str) and 1 <= len(name) <= AskName.MAX_NAME_LENGTH or optional and name is None
	def mark_ok(self, mark): return isinstance(mark, str) and 1 <= len(mark) <= 2

	TIME_FORMAT = "%Y-%m-%d %H:%M:%S"
	pack_time = classmethod(lambda cls, timestamp: strftime(cls.TIME_FORMAT, timestamp))
	unpack_time = classmethod(lambda cls, timestring: strptime(timestring, cls.TIME_FORMAT))

def parse_args():
	ap = argparse.ArgumentParser()
	ap.add_argument('--test', action='store_true', dest='verbose_tests', help='verbose tests')
	ap.add_argument('--tracebacks', action='store_true', dest='tracebacks', help='display tracebacks even for catched exceptions (debug option)')
	return ap.parse_args()

def configure_and_test(args):
	global TRACEBACKS
	TRACEBACKS = args.tracebacks or TRACEBACKS
	selftest(args.verbose_tests)

def selftest(verbose):
	poop = io.StringIO()
	stats = TextTestRunner(stream=poop, verbosity=(0, 2)[verbose], tb_locals=True).run(TestSuite(
		defaultTestLoader.loadTestsFromTestCase(value) for name, value in globals().items()
			if isinstance(value, type) and issubclass(value, TestCase) and value is not TestCase
			and not (value is DamageEstimationTest and not verbose)))

	if verbose or not stats.wasSuccessful():
		print(poop.getvalue().rstrip(), end='')
		input()
		if not stats.wasSuccessful(): sys.exit()

def main():
	locale.setlocale(locale.LC_ALL, '') # чтобы даты по-русски печатались :|
	configure_and_test(parse_args())
	with closing(Session()) as session:
		while session.process(): pass

if __name__ == "__main__": main()