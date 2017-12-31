import sys, os, string, tempfile, pickle, pickletools, lzma, textwrap, math, time, enum, base64
from traceback import format_exc
from collections import namedtuple, OrderedDict, defaultdict, deque
from bisect import bisect_left, bisect_right, insort_right
from random import random, randrange, choice, uniform
version, save_version = (0, 2), 0

class config:
	min_term_width, min_term_height = 80, 25

# FORMAT_RAW не хранит эти настройки в сжатом потоке, поэтому для распаковки нужно указать те же, которыми упаковывались.
LZMA_OPTIONS = {"format": lzma.FORMAT_RAW, "filters": [{"id": lzma.FILTER_LZMA2, "preset": lzma.PRESET_DEFAULT}]}
# для default-параметров, где допустимо None
sentinel = object()

def internalerror(*args):
	if len(args) == 1: raise AssertionError(f"Внутренняя ошибка: {args[0]}.")
	elif len(args) == 2:
		what, desc = args[0], args[1]
		try:
			what = f" ({what})"
		except:
			what = ""
		internalerror(desc + what)
	else: raise TypeError(f"internalerror: ожидаются 1 (сообщение) или 2 (значение + сообщение) аргумента, получено {len(args)}.")

# 1. check(what, cond, errmsg)
# Возвращает what, если всё хорошо (cond), иначе возбуждает internalerror.
# Короче, assert с возвращаемым значением, чтобы всё в одну строку ебашить))0.
# Например: hp = check(new_hp, new_hp > 0, "недопустимое значение hp").
#
# 2. check(условие 1, internalerror при невыполнении условия 1, ...)
def check(*args):
	if len(args) == 3:
		what, cond, errmsg = args[0], args[1], args[2]
		return what if cond else internalerror(what, errmsg)
	else:
		for i in range(len(args) // 2):
			if not args[2*i]: internalerror(args[2*i+1])
		return args[0]

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

# Сжимает строку в кашу, которую можно будет записать в исходнике короче оригинала.
def pack_str(src):
	return ''.join(chr(b) for b in base64.b64encode(lzma.compress(src.encode('koi8-r'), **LZMA_OPTIONS)))

# Распаковывает результат pack_str.
def unpack_str(b):
	return ''.join(lzma.decompress(base64.b64decode(b), **LZMA_OPTIONS).decode('koi8-r'))

# Красивенько форматирует строку (предположительно длинную, предположительно результат pack_str) в питонье объявление.
def pretty_decl(s, width=155, prefix="", pad="\t"):
	def pieces_gen():
		pos = max(0, width-len(prefix))
		yield '"' + s[:pos] + '"' + ("\\" if pos < len(s) else "") if pos > 0 else '\\' if s else '""'
		yield from (pad + '"' + s[pos:pos+width] + '"' + ("\\" if pos+width < len(s) else "") for pos in range(pos, len(s), width))
	return pad + prefix + "\n".join(pieces_gen())

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

# Наибольшая общая подпоследовательность. https://en.wikipedia.org/wiki/Longest_common_subsequence_problem
# lcs("гвозди", "вонзить") == "вози"
# eqf — равенство элементов a и b
#
# Пусть нужно рассчитать LCS(a[:NA], b[:NB]).
# Если последние буквы одинаковые, она будет равна LCS(a[:NA-1], b[:NB-1]) + эта буква.
# Иначе — max(LCS(a[:NA-1], b), LCS(a, b[:NB-1])).
# Т. о. для LCS[a:NA, b[:NB]] нужно знать решения для всех предыдущих NA и NB.
# Это можно сделать, заполнив таблицу, где элемент X, Y — LCS(a[:X+1], b[:Y+1]), и равен
# максимуму соседей сверху и слева (если эта буква не совпадает) или соседу сверху-слева+1 (если буква совпадает и т. о. продолжает последовательность).
# Пусть A = "вонзить", B = "гвозди".
#   в о н з и т ь     в о н з и т ь     в о н з и т ь     в о н з и т ь     в о н з и т ь     в о н з и т ь
# г 0 0 0 0 0 0 0   г 0 0 0 0 0 0 0   г 0 0 0 0 0 0 0   г 0 0 0 0 0 0 0   г 0 0 0 0 0 0 0   г 0 0 0 0 0 0 0
# в                 в 1 0 0 0 0 0 0   в 1 0 0 0 0 0 0   в 1 0 0 0 0 0 0   в 1 0 0 0 0 0 0   в 1 0 0 0 0 0 0
# о                 о                 о 1 2 2 2 2 2 2   о 1 2 2 2 2 2 2   о 1 2 2 2 2 2 2   о 1 2 2 2 2 2 2
# з                 з                                   з 1 2 2 3 3 3 3   з 1 2 2 3 3 3 3   з 1 2 2 3 3 3 3
# д                 д                                                     д 1 2 2 3 3 3 3   д 1 2 2 3 3 3 3
# и                 и                                                     и                 и 1 2 2 3 4 4 4
# В нижней правой ячейке — длина ответа. Для расчёта таблицы достаточно хранить два последних ряда.
# Чтобы восстановить саму последовательность, нужно помнить, откуда получен ответ в ячейке X, Y, это делается в trace:
# trace[x, y] = 0 — сдвинуться влево-вверх (взять символ)
# trace[x, y] = 1 — сдвинуться влево (пропустить символ A)
# trace[x, y] = 2 — сдвинуться вверх (пропустить символ B).
# ...только вместо x, y используется ofs = x*len(a) + y, чтобы с точки зрения языка это был одномерный массив.
# (чтобы найти ВСЕ подпоследовательности, придётся добавлять trace = 3 :^) но это сложнее и я не уверен, что там не экспоненциальная сложность.
def lcs(aseq, bseq, eqf=lambda a, b: a == b):
	LP = (1 + len(bseq)) * [0] # предыдущий ряд
	L  = (1 + len(bseq)) * [0] # рассчитываемый ряд
	trace = len(aseq) * len(bseq) * [0]
	ofs = 0
	for ia in range(1, 1 + len(aseq)): # сдвиг на единицу и L/LP на ячейку больше, чтобы не проверять крайний случай с пустым префиксом
		for ib in range(1, 1 + len(bseq)):
			# Если A[ia] = B[ib], LCS(ia, ib) = LCS(ia-1, ib-1). Например, LCS("дождь", "червь") = LCS("дожд", "черв") + "ь"
			# Иначе LCS(ia, ib) = max(LCS(ia-1, ib), LCS(ia, ib-1).
			L[ib], trace[ofs] = (LP[ib-1] + 1, 0) if eqf(aseq[ia-1], bseq[ib-1]) else (LP[ib], 1) if LP[ib] >= L[ib-1] else (L[ib-1], 2)
			ofs += 1
		LP, L = L, LP

	# ia — индекс символа в строке A, который берётся либо нет (можно вместо него отслеживать ib/B с тем же успехом)
	# rem — оставшаяся длина подпоследовательности
	ofs, ia, rem = ofs-1, len(aseq), LP[len(bseq)]
	result = [None] * rem
	dispatch = ((1, 1, len(bseq)+1), (1, 0, len(bseq)), (0, 0, 1))  # -ia, -rem, -ofs для каждого возможного значения trace
	while rem > 0:
		dis = dispatch[trace[ofs]]
		ia, rem, ofs = ia - dis[0], rem - dis[1], ofs - dis[2]
		if dis[1]: result[rem] = aseq[ia]
	return result if isinstance(result, type(aseq)) else ''.join(result) if issubclass(type(aseq), str) else type(aseq)(result)
# (в итоге я это не использую, ну и ладно)

# упрощённая версия lcs(), если не нужна сама последовательность, а только длина
def lcs_len(aseq, bseq, eqf=lambda a, b: a == b):
	LP = [0] * (1 + len(bseq))
	L  = [0] * (1 + len(bseq))
	for ia in range(1, 1 + len(aseq)):
		for ib in range(1, 1 + len(bseq)):
			L[ib] = LP[ib-1] + 1 if eqf(aseq[ia-1], bseq[ib-1]) else LP[ib] if LP[ib] >= L[ib-1] else L[ib-1]
		LP, L = L, LP
	return LP[len(bseq)]

# is_subseq("вози", "гвозди") == True
def is_subseq(seq, ref, eqf=lambda a, b: a == b):
	ref_iter = iter(ref)
	for item in seq:
		while True:
			ref_item = next(ref_iter, sentinel)
			if ref_item is sentinel: return False
			if eqf(item, ref_item): break
	return True

# модификация lcs_len, возвращающая максимальную «оценку» среди общих подпоследовательностей
# lcs_len — частный случай lcs_score с оценкой 1 при равенстве элементов и 0 при неравенстве
# например:
# lcs_score(["раз", "blah", "два", "три"], ["раскол", "дворец", "nah", "триста"], lambda a, _ia, b, _ib: common_prefix_len(a, b)) =
# = 7 ("ра" + "дв" + "три")
# если сильно нужно, то по аналогии с lcs() можно восстановить саму последовательность, но мне не нужно :)
def lcs_score(aseq, bseq, scoref):
	LP = [0] * (1 + len(bseq))
	L  = [0] * (1 + len(bseq))
	for ia in range(1, 1 + len(aseq)):
		for ib in range(1, 1 + len(bseq)):
			L[ib] = max(LP[ib-1] + scoref(aseq[ia-1], ia-1, bseq[ib-1], ib-1), LP[ib], L[ib-1])
		LP, L = L, LP
	return LP[len(bseq)]

# Наивный байесовский классификатор, украденный из https://habrahabr.ru/post/120194/.
# guess возвращает (1) наиболее вероятный класс и (2) отрыв от предыдущего, приведённый к [0; 1] (или None, None — пока такого не будет, но завтра...).
# Например, пусть он угадывает пол по первой и двум последним буквам имени:
#
# guesser = BayesianGuesser(lambda name: ('F'+name[0], 'S'+name[-2], 'L'+name[-1]))
# guesser.train({'Петя': Gender.MALE, 'Коля': Gender.MALE, 'Вера': Gender.FEMALE, ...})
# cls, margin = guesser.guess('Витя')
#
# Как учитывать margin — решать пользователю. Можно подобрать эмпирическое правило вроде
# if margin > 0.4: (воспользоваться результатом) else: (придумать что-то другое).
#
# Коллбэк, передаваемый в конструктор, должен извлекать из классифицируемого объекта значащие признаки —
# то, что нейросеть делала бы автоматически... но не тянуть же её для такой ерунды хд, даже то, что есть, перебор.
# А вообще всё это из рук вон плохо работает, ну да ладно. В качестве моральной компенсации добавил читерскую проверку на точные совпадения.
# TODO: сделать статистику по наиболее информативным признакам, как в http://www.nltk.org/_modules/nltk/classify/naivebayes.html.
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

	# оценивает точность классификации — нет большого смысла вызывать на тренировочных образцах, результаты будут слишком оптимистичными
	def success_rate(self, samples):
		success = total = 0
		for sample, ref_cls in self.pairs(samples):
			if self.guess(sample)[0] == ref_cls: success += 1
			total += 1
		return success / max(1, total)

class Gender(enum.IntEnum):
	UNKNOWN, MALE, FEMALE, NEUTER, TOTAL = -1, 0, 1, 2, 3

	@staticmethod
	def detect(name):
		# С L2-L3 бессовестно нарушается предположение о независимости признаков, но результат вроде лучше, кхехех.
		oracle = BayesianGuesser(lambda w: ('F2:'+w[0:2], 'L2:'+w[-2:], 'L3:'+w[-3:]),
			samples = {sample: gender
				for samples_pack, gender in ((Gender.male_names_pack(), Gender.MALE), (Gender.female_names_pack(), Gender.FEMALE))
				for sample in unpack_str(samples_pack).split()})

		best_guess, best_margin = Gender.UNKNOWN, None
		for _lit, word in Noun.split_into_words(name):
			guess, margin = oracle.guess(word.lower())
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
	def male_names_pack(): return "4AqtBUFdAGCwlhFhBANqgdz3DgmOd2wekFq0tVzmEi+I42A7RDWQmHbzL4VPUxfX1Bw4CZ1OuosNACJ/UQwu9KC1Xg9gG9inXAWgffRMCvUwmOLkPlSdKiHQqFcDT"\
	"Hog4qhokzlaYGoEs87AUN3m0b6wOO/oONxz1qVUAAUb3mnmTFBpCOoMf30f+5/Diw2+UipO4caYrvzJ6GsSAGjrWtsxfO+M3m9Y83Yn5BoLqhatOZfHNNgmZJui++JbM3Cat5gFnWtg/+A8Uyas5O0S35D9"\
	"1vrqP8vK/vc/CiMxjA80kC2XbchDvlxud/Ho9ETdafqF8LYB7LniFmZwJ4UeXnJZDQZresW562+0fOhjo6AvLvVtDpsnwl8RG2n14zgHmsEkcWqUOmtgIOHCo3Lk34Q+9rPCFhZwN5Otia/NSCha7i2yr9D"\
	"FyKctNg+Gtw/z4eLExXLw6fqRSZ2jKmJf7FrApK3iOrmCadJmRPAe+ymisqEWhOUhws2fxEIhRX2eTpISz7KONzv60fARysqvY/hqbPgJdZhQmcR767M+Raa7h4MH4R/Sq4Dqqy73VoH5YNacM+Pxwiey44"\
	"o+N09Y3eIe6XvC1Nr1997SSFWYeIrSLituMx6DMJY7H59rn1feY8J8iiNzhFs2us/EoQCqvMKtXrxRNHt4E0hTqQGJOA1L+nh8ZqBJ6+IRsx9JQkGsBAZA3ie4+JYpR/EpHiFLDTAuUzdV2/QgihN9t8bID"\
	"tJqsl71CHnWPsJaVhVVHXZlRF9dN+tGtvyRO/wFImYAJDqyvdxoDb9BrTgedYN6ZOiBz1hKi/EgVMV8h+6yHUVFPxgY0rg98Ak8KcnG1v74g2V0S78e5tsAdCVu/jrODT3dvUCEAQvRBNmin0lNfBddfeg6"\
	"JzZQXbKQM/GGvgCuFM4NkctmYt78VyPvDukUG7EimMmD3mvxfC3UYthW4dFWgGI8weYoq5nM28QSNKryt7A6zAxP7mFDNOI+2cGocCQZzzGRV1qbgJXVtBkZI5SnFhCSja/fy3OlxTlz+KlTN23gaQebhkJ"\
	"j2oKYCU+0zynpQ6K8scVEXvZxaFw/r65/GsJZOznsyYlHCTwdnZLYNtKUIqcP62FVY4tBoYvqaJEO7AkWKwnCqRgChD9E9uBE4+QjS1168K4eaYUhXT3Xt8JroBqAKAigx7nRmg/nzU1bVkzrsPt82nwEs6"\
	"/akp5CcTjOFV4NVVadZYhJdQ5Ak2FWS3JyxFkej0wAIsiorCc25bHld13GceWnh5Mc04g+YNgy4omJO/DBJzthN/Y9maKdP0JV0epkwDUh1NoaEB1GCLpfvrV35iTmrU0xJs2sfvgxYwMJa5oW66olYN6qU"\
	"JOGQCk9eljfwvV+uOKX3Zz2lrMLiHo+OdeUn3MJlfjouJApwg0l0KfQ7wgXSZTLbh8jMhid9pwLqD9IOiiZ9gjLH/59v8HGcaAgGu1BH1nocansSYolgoRYQpl4VL8Uq39hQkvdzfrnQw6MOXQrP/quU5V9"\
	"4ZnosXyjgZBaQIYf4banqBtJzxboCJaVNaHHCpWi2o5selhfSOtdLG2/LJKINXNxZXA++QpW4SjALkU962FUqKEHIAiJy9rjZZQUgvvrYhW6B901kfFnNR9LqCjxOTypSMw+28NOY/Nr/oiuyyLlc7x3NFV"\
	"hcrXE34HGNlT91TrC6jKgZmPK043GGUkRAO0zCyOKEyqEtB2rRkDLJH48cCx+c87CA9c2ghjBO4/KX6nYiUZ6AdXy4OFXvArM6NMFtlAhyFCwy0/Ao1pPuev471MxScQA"

	@staticmethod
	def female_names_pack(): return "4A0TBXZdAGC11Hni/RL9heaaA1Ylf0kEK6wxQ4Lyo1h7VZZ5yuNuIqj03ZlwUQEf04RPJdzCrHDrUdy08g4j0p4dy7I1YrlZFlIXoGPKjKLF6Tdg8tiW5qDH0kQ"\
	"zURpAA2dn5cfLKp61tqkRMZOo9tmQIDVP0j8HYzwiJC6hOA7u9wTYB8/HdJvl3qK87JVKF6pJMj6ZLyd9/D7JTxIxHWsue6qgGitrzJdLhcR648/+iTuIFMaQCmmLHDEQLpMvuoyQyIC0TYCO9Vce2cEg2Z"\
	"8bfDv4Fpb5i8IWedJ2G3bosFqrPiaFWWZIJBEO0LEkirSCjn8VTtlY0ynC322jXZ+8ZZPa2aRJG8QfKRqMNqAhadET8UCt2g9IKibsXvjjM+dNXQAwn+JObmTFw4J3fZ+MH9xgRRL8rEcU8NfWvBY5s7fY9"\
	"erp0tOSbAndb5PWv/vhkRImpZV43Ek/YOM+RM2Kr5aRud1fOtT8zM7296AEvBYHpXPYKh0iSOhu6X5Y7nmt+AigOQADagjO/w7c8w3MqEIrp/viCXhd2U0YsexYSx0YG/ikzGhiWv0n5XXx3R0riqmbYwc+"\
	"mHHkSEB55VDrjpf5sW9NAgcNSqnPV7FGmx/UtZgx2I/fA/6rGiByv2thVsRMlFD2lgFcQAPmjkXzfLNt58KEvsFfqEGn0OlNz2A8AKI6J0Ki1pT5UhvqaxILHm5my9p90bnTyaJHMxYIpqnB680CBN7L16i"\
	"Kcs8Sp5GDtcEWaUq3Uo+02nglvnHBtS7KKR/Bq6CuC3yVTtMykk21uKLjVFRp1H61EwzQMI2lGpd+8ZaUhntJmP+dLBZqExqq1cryKms+9B/rkm96RUMaCshH9LBev3DtJy861JfOiNAlv47G3916H4TEf3"\
	"kvPs3h1d8rg0yIP6hPt9xj7zdTm1htkwO1cbiUPBLpOFAZN6BCZFsr7K5pi0z6EH0EJSTRZjRX0lwulwjZB+L/5bbPP0STcl8nZKtzXp6y1CbjKrT63e9nM1d9MoTgUIpLeOSz/5hSGnqknUHOeo3F8HY0J"\
	"Tb5IRft7XqGcGBMWAZap23HmZzw3mV2P+Mw2k/UvdxACaNwBsclUxoTokBCEOQPcGHoXq/IqATqbWd+tE5YXjYrsJhGjHjQbdCb0HholWnnC1rtkZB656MeuUVfocDWntFhH9/WYCkHhD2JkFEII5UZocw4"\
	"wX8z1s5SCICSfKrdBYKAjV/875FTsyJBsiF/uh6qEYOEz6ZntoD6e5uGHPLy1PkbRrwKHImJHtUX0Ib/1Ez+oR82stBVj9AQdCRxWM1qqXj7jDAvZHjgTWy47pgSNY5vec7kdJIeQbV5AL49bWM4l6itgHJ"\
	"+hRX0goGPJfavsDvbDpD8ddDwzEg0UdnLwzvW7qykPybkVmsnmBfqiQhkOj8xEdvKgjqehhzJMlrGGA6jCeagp5mCOTNCvSG4BIeALjdnPTV6T1cO0Kbr7+6ssj5vUJFgBlo2Acz7FUbFvhDomJTibn93Ei"\
	"JcREeHceGcSC/cu/6gZF4KFekU4T/m+V1kSrLJg5HtiCBibKOeZoAZBQxXB5UtfqpQ34mOXzz03G8oxbSuA8BclwLKbMXjFa/jyPcplXHxqNXQwxsRqhzF1AMRdWmSapfdDrRueY2NZUVOd2swS8VtJzCGj"\
	"3RqF/+XhffpDyt68MEmYetpxa1YBm6fi8fYz7GckGPXSv7otKNz6YWgf6ZT/W6lvGTnjVYOm8NgQZAzZDS462VmBMtr4dstWXGF+aHgAvu/DqQE5cyPPiGKOTlVRC8CEnnBPzvjxEgPnM4Gl1V10XJbNwYK"\
	"aVthHxfOQfX4rjGdfGZPt5Wf3/8u25NnZWhx5ioIXM/owAA="

class Case:
	NOMINATIVE, GENITIVE, DATIVE, ACCUSATIVE, INSTRUMENTAL, PREPOSITIONAL, TOTAL = 0, 1, 2, 3, 4, 5, 6

# Noun("маленьк{ий/ого/ому/ий/им/ом} член{/а/у//ом/е}")(Case.GENITIVE) == Noun.guess("маленький член")(Case.GENITIVE) == "маленького члена"
# Noun("{кусок} угля")(Case.PREPOSITIONAL) == "куском угля"
class Noun:
	def __init__(self, src, gender=Gender.UNKNOWN):
		self.pieces = src if isinstance(src, list) else Noun.parse(src)
		self.gender = gender

	def __call__(self, case):
		return "".join(piece for literal, cases in self.pieces for piece in (literal, cases[case] if cases else ""))

	@staticmethod
	def append_pair(pieces, literal, cases): # ненужная оптимизация, чтобы не бить строку в месте, где guess_one так ничего и не придумала
		if pieces and not pieces[-1][1]:
			pieces[-1] = pieces[-1][0] + literal, cases
		else:
			pieces.append((literal, cases))

	@staticmethod
	def parse(src):
		pieces = []
		for literal, bracketed, spec, _ in string.Formatter.parse(None, src):
			if bracketed:
				cases = bracketed.split('/', Case.TOTAL-1)
				if len(cases) == 1:
					animate, gender = False, Gender.UNKNOWN
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
		return pieces

	@staticmethod
	def guess(src, animate=False, gender=Gender.UNKNOWN):
		pieces = []
		Noun.guess_multi(pieces, src, animate, gender)
		return Noun(pieces, gender)

	@staticmethod
	def guess_multi(pieces, src, animate, gender):
		for literal, word in Noun.split_into_words(src):
			base, cases = Noun.guess_one(word, animate, gender)
			Noun.append_pair(pieces, literal + base, cases)

	@staticmethod
	def guess_one(word, animate, gender):
		def ngdip(nom, gen, dat, ins, pre): return (nom, gen, dat, gen if animate else nom, ins, pre)
		def yi(prev): return 'ы' if prev in 'бвдзлмнпрстфц' else 'и'
		def oe(prev): return 'е' if prev in 'н' else 'о'
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
		elif word.endswith('а'):
			return word[:-len('а')], ('а', yi(word[-2:-1]), 'е', 'у', 'ой', 'е')
		elif word.endswith('я'):
			return word[:-len('я')], ('я', 'и', 'е', 'ю', 'ей', 'е')
		elif word.endswith(('б', 'в', 'г', 'д', 'ж', 'з', 'к', 'л', 'м', 'н', 'п', 'р', 'с', 'т', 'ф', 'х', 'ц', 'ч', 'ш', 'щ')) and \
			(gender == Gender.UNKNOWN or gender == Gender.MALE):
			if word.endswith('ок'):
				return word[:-len('ок')], ngdip('ок', 'ка', 'ку', 'ком', 'ке')
			else:
				return word, ngdip('', 'а', 'у', 'ом', 'е')
		elif word.endswith('й') and (gender == Gender.UNKNOWN or gender == Gender.MALE):
			return word[:-len('й')], ngdip('й', 'я', 'ю', 'ем', 'е')
		elif word.endswith('ь') and (gender == Gender.UNKNOWN or gender == Gender.MALE):
			return word[:-len('ь')], ngdip('ь', 'я', 'ю', ('ё' if word.endswith('арь') else 'е') + 'м', 'е')
		else:
			return word, None

	@staticmethod
	def split_into_words(src):
		def is_word_char(ch): return 'а' <= ch <= 'я' or 'А' <= ch <= 'Я' or ch in 'ёЁ'
		i = 0
		while i < len(src):
			lit_start = i
			while i < len(src) and not is_word_char(src[i]): i += 1
			word_start = i
			while i < len(src) and is_word_char(src[i]): i += 1
			yield src[lit_start:word_start], src[word_start:i]

	def src(self, sep="/"): return "".join(piece for literal, cases in self.pieces for piece in (literal, "{" + sep.join(cases) + "}" if cases else ""))

	# Спасибо, дядя!
	names = "аватар алкаш анархист ангел аноним Антон атронах бандит батя бес биомусор бодибилдер боец бомж борец брат братишка быдлан великан весельчак ветеран воин волшебник вор ворчун вымогатель глаз глист гном говнарь голем грешник гусь девственник демон дерьмодемон Джон дракон дрищ друг дружище Ероха зверь змей Иван идиот имитатор инвалид инспектор камень карасик Кирилл клинок клоун коллекционер конь крокодил крыс лазутчик лектор лещ маг майор мастер молочник мститель музыкант Нариман наркоман насильник натурал невидимка одиночка отшельник охотник патимейкер паук Петрович петух пидор планктон подлещик пожиратель полковник поп призыватель рай рак рокер сатанист священник скоморох слоник содомит солдат соратник сталкер старатель старик странник студент сыч таран титан товарищ трюкач тян{f} убийца ублюдок угар ужас фаллос фантом философ хикки химик хитрец художник человек червь шайтан шакал шаман шахтёр школьник шторм шутник эксперт эльф" # pylint: disable=line-too-long

	adjs = "адский алкоголический альфа- анальный ангельский астероидный аффективный безголовый безграмотный безногий безрукий бесноватый беспутный бессмертный блаженный боевой бойцовский болотный большой буйный быстрый великий весёлый военный воздушный волшебный вражеский вселенский всемогущий галактический глубоководный голубой горный горячий грустный девственный демонический деревянный дикий доверчивый домашний древний дружеский дырявый ёбаный железный жёлтый живой жирный законный зелёный зловещий золотой интернациональный искусственный истинный каменный компьютерный королевский космический красный легендарный легкомысленный лесной летающий лимонный лунный маленький мамкин межпространственный молочный молчаливый морозный мстительный мёртвый невидимый незаконный ненужный неповторимый нескучный неудержимый нищий обдристанный обсидиановый обычный огненный одинокий октариновый омега- опасный оранжевый отверженный очковый петушиный пидорский поддельный подзаборный подземный праведный провинциальный пьяный райский раковый речной розовый роковой рыбный свободный святой священный сексуальный семейный серебрянный сильный синий скучный смелый смертельный смертный снежный солнечный степной странный титанический тупой тёмный ублюдочный угольный унылый успешный хитрый честный чёрный шоколадный штормовой шутливый" # pylint: disable=line-too-long

	@staticmethod
	def feminize_adj(w):
		if w.endswith('ый') or w.endswith('ой'): return w[:-2] + 'ая'
		elif w.endswith('ий'): return w[:-2] + ('я' if w[-3:-2] in 'н' else 'а') + 'я'
		elif w.endswith('н'): return w + 'а'
		else: return w

	@staticmethod
	def random_name():
		adj, name, gender = choice(Noun.adjs.split()), choice(Noun.names.split()), Gender.MALE
		if name.endswith('{f}'):
			name, adj, gender = name[:-len('{f}')], Noun.feminize_adj(adj), Gender.FEMALE
		return cap_first(adj) + ("" if adj.endswith('-') else " ") + name, gender

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
		(
			("Злобн{ый/ого/ому/ого/ым/ом} Буратино", "Злобн{ый|ого|ому|ого|ым|ом} Буратино"),
			(("Злобный Буратино", {'animate': True}), "Злобн{ый/ого/ому/ого/ым/ом} Буратино"),
			(("Рика", {'animate': True}), "Рик{а/и/е/у/ой/е}"),
			(("Слон", {'animate': True}), "Слон{/а/у/а/ом/е}"),
			("...{большой кусок} угля", "...больш{ой/ого/ому/ой/им/ом} кус{ок/ка/ку/ок/ком/ке} угля"),
		)
	def one(self, base, expect_src):
		n = Noun.guess(base[0], **(base[1] if len(base) >= 2 else {})) if isinstance(base, tuple) else Noun(base)
		self.expect_equal(n.src(sep='|' if isinstance(base, str) and base.find('/') >= 0 else '/'), expect_src, "forms", base)
	def describe(self, base): return base

def clamp(x, a, b): # эти странные конструкции — (бессмысленная) оптимизация общего случая (a <= x <= b) и паранойя x=NaN.
	return x if (x >= a) and (x <= b) else b if x > b else a

# XOR с псевдослучайными числами, чтобы некоторые строки не светились в файлах в неизменном виде >:3
# www.pcg-random.org
def pcgxor(seq, seed=0, mask=255):
	def pcg(state, inc):
		while True:
			state = (state * 6364136223846793005 + inc) & 0xFFFFFFFFFFFFFFFF # ой, не надо было так делать, ну ладно, мне лень магические строки переделывать
			xs, rot = (state >> 45) ^ (state >> 27) & 0xFFFFFFFF, state >> 59 # (в оригинале предлагается обновить state ПОСЛЕ, чтобы затруднить поиск в памяти etc.)
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
	# раньше было устроено чуть сложнее, чтобы попытаться доходить до края терминала, когда возможно
	# это не всегда работало (нет гарантии, что консоль переведёт строку по достижении get_terminal_size.columns)
	# поэтому убрал, но осталось переразбито на функции

	def safe_width(width): # менее некрасиво никогда не доходить до края терминала, чем рисковать перевести строку дважды
		return width - 1
	width = safe_width(width)

	lines = []
	def handle(line, width):
		any = False

		# извлечение управляющего |. До его вхождения, =| эскейпает дословный |.
		prefix, p = '', 0
		while p >= 0 and not prefix:
			p = line.find('|', p)
			if p > 0 and line[p-1] == '=':
				line = line[0:p-1] + line[p:]
			elif p >= 0:
				line = line[0:p] + line[p+1:]
				prefix = ' ' * p

		for line in textwrap.wrap(line, width, subsequent_indent=prefix, drop_whitespace=False):
			any = True
			lines.append(line)

		if not any:
			lines.append('')

	for line in text.splitlines():
		handle(line, width)

	return '\n'.join(lines)

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
	leaf = namedtuple('leaf', 'node, raw, words')
	def __init__(self):
		self.root = Commands.node(None, None)
		self.leafs = []

	def add(self, *args):
		node, raw, words = self.root, None, None

		iarg = 0
		while iarg < len(args):
			cmd, func = args[iarg], args[iarg+1]
			check(cmd, isinstance(cmd, str), "cmd?!")
			check(func, func, "func?!")

			new_words = Commands.split(cmd)
			if not new_words: raise ValueError(f"Пустая команда.")
			raw = (raw + (" " if Commands.classify_sym(new_words[0][0:1]) == Commands.classify_sym(raw[-1:]) else "") + cmd) if raw else cmd
			if words: words = words + new_words # нельзя делать extend, эти words лежат в предыдущем leaf
			else: words = new_words

			node = node.add(cmd, func)
			self.leafs.append(Commands.leaf(node, raw, words))
			iarg += 2

	def guess(self, input):
		def suggestions_on_error():
			return None, None, self.suggest_something(input) or None

		def found(node):
			node = node.down_to_unambiguous()
			return (node.func, None, None) if node.func else (None, self.suggest_something(start_node = node) or None, None)

		words = Commands.split(input)
		if not words: return None, None, None # ...а то он много чего придумает

		# Для каких команд input является подпоследовательностью по символам?
		# Может быть смысл использовать модификацию (omg) lcs_score, которая бы давала бонусы за подряд идущие символы,
		# чтобы на "il" предпочесть "silence" вместо "dispell"
		sym_cs = [leaf for leaf in self.leafs if is_subseq(input, leaf.raw)]
		if len(sym_cs) == 1:
			# для ровно одной: это однозначный ответ
			return sym_cs[0].node.func, None, None
		elif not sym_cs:
			# ни для одной: подсказать хоть что-нибудь
			return suggestions_on_error()
		else:
			# Возьмём догадки по подпоследовательностям за основу.
			cs = sym_cs

			# Но раз по символам слишком много всего, будем анализировать по словам.
			# Приоритетно рассмотреть подпоследовательности с полными совпадениями слов, если таковые есть.
			precise_cs = best_score = None
			for leaf in sym_cs:
				cur_score = lcs_len(leaf.words, words)
				if cur_score and (best_score is None or cur_score > best_score):
					best_score = cur_score
					precise_cs = [leaf]
				elif cur_score == best_score:
					precise_cs.append(leaf)
			if precise_cs and len(precise_cs) == 1:
				return found(precise_cs[0].node)
			elif precise_cs:
				cs = precise_cs

			# Для каких подпоследовательностей по символам input является подпоследовательностью по словам, и насколько хорошей? Оценивается по длине LCS слов :)
			# Также пропускаются менее многословные команды, чтобы на 1 и remove 1 ответило 1.
			# Также бонусно учитывается общий префикс, чтобы на remove 10, remove 11, remove 21 и введённую remove 1 не называло в подсказках remove 21.
			word_cs = best_score = None
			for leaf in cs:
				cur_score = lcs_score(leaf.words, words, lambda a, _ia, b, _ib: common_prefix_len(a, b) + lcs_len(a, b))
				if best_score is None or cur_score > best_score or cur_score == best_score and len(leaf.words) < len(word_cs[0].words):
					word_cs = [leaf]
					best_score = cur_score
				elif cur_score == best_score and len(leaf.words) == len(word_cs[0].words):
					word_cs.append(leaf)

			if word_cs and len(word_cs) == 1: # Одна подошла лучше остальных: это однозначный (кхе-кхе) ответ.
				return found(word_cs[0].node)
			elif word_cs:
				cs = word_cs
			else:
				# Это НЕВОЗМОЖНО ввиду оценки через lcs_len. Но на случай, если логика оценки изменится, оставлю заглушку...
				return suggestions_on_error() # Либо cs = word_cs и пойти дальше.

			# После всех пыток команда осталась неоднозначной, так и ответим.
			# Если слишком много вариантов — выбрать случайные.
			MAX_ALTERNATIVES = 10
			if len(cs) > MAX_ALTERNATIVES: cs = [cs[i] for i in sorted(random.sample(range(len(cs)), MAX_ALTERNATIVES))]
			return None, [leaf.raw for leaf in cs], None

	@staticmethod
	def classify_sym(sym): return (
		-1 if sym in string.whitespace else
		0 if sym in string.ascii_letters else
		1 if sym in string.digits else
		2 if sym in '?' else
		3)

	@staticmethod
	def split(cmd, seps=False):
		i, r, preved = 0, [], 0
		while i < len(cmd):
			start_cls = Commands.classify_sym(cmd[i])
			if start_cls >= 0:
				start = i
				while True:
					i += 1
					if i >= len(cmd) or Commands.classify_sym(cmd[i]) != start_cls: break
				part = cmd[start:i]
				r.append((cmd[preved:start], part) if seps else part)
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
		if len(matches) == 1 and not matches[0].func and matches[0].childs and (matches[0].parent or input is sentinel):
			matches = [match for match in matches[0].childs.values()]

		return [node.down_to_unambiguous().backtrack() for node in matches if node.parent]

	class node:
		def __init__(self, name, parent, space=""):
			self.childs = OrderedDict()
			self.func   = None
			self.name   = name
			self.space  = space
			self.parent = parent

		def add(self, cmd, func):
			node = self
			for space, subcommand in Commands.split(cmd, seps=True):
				child = node.childs.get(subcommand, None)
				if not child:
					child = Commands.node(subcommand, node, space)
					node.childs[subcommand] = child
				node = child
			if node.func: raise RuntimeError("Команда {0} уже определена.".format(node.backtrack()))
			node.func = check(func, func, cmd)
			return node

		def backtrack(self, as_list=False):
			node, path = self, []
			while node.parent:
				path.append(node)
				node = node.parent
			if as_list: return [node.name for node in path]
			return ''.join(node.space + node.name for node in reversed(path))

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
				("o t", (None, ["one two three", "one two four", "one three six"], None)),
				("o t t", ("123", None, None)),
				("o t s", ("136", None, None)),
			)
		), \
		((("spd-", "A"), ("sp.frailness", "B")), ("sp-", ("A", None, None))), \
		((("sp-", "A"), ("spd-", "B"), ("sp.frailness", "C")), ("sp-", ("A", None, None))), \
		(
			(("1", "L1"), ("remove 1", "A"), ("remove 10", "B"), ("remove 11", "C"), ("remove 21", "D")),
			(
				("r1", ("A", None, None)),
				("r2", ("D", None, None)),
			)
		)
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
			(
				["STR [A]5[B] -> [C]10[D]   [E]$100[F] / [G]1[H]",
				 "INT [A]10[B] -> [C]15[D]   [E]$150[F] / [G]1[H]",
				 "SPEED [A]15[B] -> [C]1000[D]   [E]$9999[F] / [G]99[H]"],

				["STR    5 ->   10    $100 /  1",
				 "INT   10 ->   15    $150 /  1",
				 "SPEED 15 -> 1000   $9999 / 99"]
			),
			(
				["STR.[A]5[B].->.[C]10[D]...[E]$100[F]./.[G]1[H]",
				 "INT.[C]10[E].->.[I]15",
				 "SPEED.[B]15[C].->.....[D]1000[E]....[I]$9999"],

				["STR. 5.->.      10... $100./.1",
				 "INT.                10.->.15",
				 "SPEED.  15.->.....1000....$9999"],
			),
			(["1[A]2[B]3", "4[B]5[A]6"], ["MultipadMarkupError"])
		)
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
		check(not self.applied, "already applied")
		self.master = check(master, isinstance(master, Fighter), "master?!")
		self.victim = check(victim, isinstance(victim, Fighter), "victim?!")
		master.caused_hexes.add(self)
		victim.hexes.add(self)
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

	def short(self):
		desc = self.do_name()
		pow_desc = self.do_describe_power()
		if pow_desc: desc += ", " + pow_desc
		if self.time_based: desc += ": " + plural(self.turns, "{N} ход{/а/ов}")
		return desc

	def do_name(self): raise NotImplementedError("do_name")
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
		self.victim.hexes.add(self)        # hexes отбрасывается Fighter

class RageHex(Hex):
	#  мин. 1.2x @ pow → 0
	#       1.5x @ BASELINE_POWER
	# макс. 5.0x @ pow = 1267
	physdam_x = property(lambda self: clamp(1.2 + 0.3 * self.npower, 1.2, 5.0))

	#  мин. 1.1x @ pow → 0
	#       1.2x @ BASELINE_POWER
	# макс. 2.2x @ pow = 1100
	backlash_x = property(lambda self: clamp(1.1 + 0.1 * self.npower, 1.1, 2.2))

	def do_name(self): return "Ярость"
	def do_describe_power(self):
		m = round(self.physdam_x, 1)
		return None if m == 1.5 else f"{m}x"

	def do_detail(self): return \
		"Увеличивает физическую атаку (x{0}) и любой получаемый урон (x{1}).".format(round(self.physdam_x, 1), round(self.backlash_x, 1))

	def do_cmd(self): return 'rage'

class RageHexTest(Test):
	def __init__(self): self.dummy = None
	def setup(self): self.dummy = RageHex.__new__(RageHex)

	cases = ((-1000, 1.2, 1.1), (0, 1.2, 1.1), (Hex.BASELINE_POWER, 1.5, 1.2), (1100, 4.5, 2.2), (1267, 5, 2.2), (9999, 5, 2.2))
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

	def do_name(self): return "Смертный приговор"
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

	def do_name(self): return "Кровотечение" + ("!!!" if self.npower > 3 else "!" if self.npower > 2 else "")
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

	@classmethod
	def mp_cost(cls, self): return cls.do_mp_cost()

	@classmethod
	def do_mp_cost(cls): raise NotImplementedError("do_mp_cost")

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
		rv = target.save_relative_vitals()
		setattr(target, 'base_' + self.stat, self.get_base_stat(target) + self.amount)
		target.restore_relative_vitals(rv)

	def do_revert(self, target):
		rv = target.save_relative_vitals()
		setattr(target, 'base_' + self.stat, self.get_base_stat(target) - self.amount)
		target.restore_relative_vitals(rv)

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

	@classmethod
	def do_mp_cost(cls): return 6

class Dispell(Spell):
	LIST_ORDER = 1
	@classmethod
	def do_name(cls): return "Развеять"

	@classmethod
	def do_cmd(cls): return 'dispell'

	@classmethod
	def do_mp_cost(cls, self): return 2

class Frailness(Spell):
	LIST_ORDER = 2
	@classmethod
	def do_name(cls): return "Хрупкость"

	@classmethod
	def do_cmd(cls): return 'frailness'

	@classmethod
	def do_mp_cost(cls): return 3

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
	MAX_CHARGES = 5

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

	def __init__(self):
		self.xp = 0
		self.xl = 1
		self.ap_used = 0
		self.name = "Баг"
		self.gender = Gender.UNKNOWN
		self.upgrades = []

	def receive_xp(self, amount):
		self.xp += amount
		def will_levelup(): return self.xp >= self.xp_for_levelup(self.xl) and self.xl < self.LEVEL_CAP
		if will_levelup():
			rv = self.save_relative_vitals()
			while True:
				self.xp -= self.xp_for_levelup(self.xl)
				self.level_up()
				if not will_levelup(): break
			self.restore_relative_vitals(rv)
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

	def save_relative_vitals(self): return None
	def restore_relative_vitals(self, saved): pass

	def __getstate__(self):
		return {
			k: v.value if k == 'gender' else v
			for k, v in self.__dict__.items()}

	def __setstate__(self, state):
		self.__init__()
		self.__dict__.update(
			(k, Gender(v) if k == 'gender' else v)
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

		self.hexes = set()
		self.caused_hexes = set()
		self.weapon = None
		self.spells = []

		self.cur_hp = self.mhp
		self.cur_mp = self.mmp
		self.ai = None

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
			hex.tick()
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

	# сохранить соотношения HP/MP к максимумам, если какое-то действие потенциально изменит их лимит.
	relative_vitals = namedtuple('relative_vitals', 'hp, mp')
	def save_relative_vitals(self): return self.relative_vitals(self.hp / self.mhp, self.mp / self.mmp)
	def restore_relative_vitals(self, saved):
		self.cur_hp = clamp(round(self.mhp * saved.hp), 1, self.mhp)
		self.cur_mp = clamp(round(self.mmp * saved.mp), 1, self.mmp)

	def __getstate__(self):
		check(self.ai, not self.ai, "ai?!")
		return {k: v for k, v in super().__getstate__().items() if k not in (
			'hexes', 'caused_hexes', # резолвятся Hex
			'ai',                    # он как негр, его не должно быть
			'death_cause'            # либо сохраняемый боец жив, либо эта информация не интересна
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

class Damage:
	pass

class Arena:
	pass

class AI:
	pass

class Con:
	# На данный момент сделано так, что чуть больше нуля даёт [#....] и чуть меньше максимума — [####.]
	# Также с текущей формулой на [#....] придётся вдвое больше пространства cur, чем на остальные деления (кроме [#####]), ну и ладно, мне лень думать
	@staticmethod
	def vital_bar(cur, max, divs=10, fillchar='#', emptychar='.'):
		fill = int(clamp(divs * (cur / (max or 1)), 0 if cur <= 0 else 1, divs))
		return "[{0}{1}]".format(fillchar * fill, emptychar * (divs - fill))

	@staticmethod
	def bullet_bar(cur, max, fillchar='#', emptychar='.'):
		return fillchar * cur + emptychar * (max - cur)

class VitalBarTest(Test):
	cases = ((0, 5, 5, 0), (1, 5, 5, 1), (2, 5, 5, 2), (3, 5, 5, 3), (4, 5, 5, 4), (5, 5, 5, 5), (0.001, 5, 5, 1), (4.999, 5, 5, 4), (1.4, 5, 5, 1))
	def one(self, cur, max, divs, expect_bars):
		self.expect_equal(Con.vital_bar(cur, max, divs), "[{0}{1}]".format('#' * expect_bars, '.' * (divs - expect_bars)), "vital_bar", cur, max)
	def describe(self, cur, max): return f"HP = {cur}/{max}"

class Mode:
	def __init__(self):
		self.session = None
		self.last_input = ""

	def process(self):
		self.do_process()

	def render(self, cmds):
		self.do_render(cmds)
		if self.do_prompt: print('\n> ', end='')

	def do_process(self): pass
	def do_render(self, cmds): raise NotImplementedError("do_render")
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

	def more(self, *a, **ka): return self.shortcut(MoreMessage, *a, **ka)
	def prompt(self, *a, **ka): return self.shortcut(Prompt, *a, **ka)

	do_prompt = True
	do_cls    = True
	term_width = property(lambda self: self.session.term_width)
	term_height = property(lambda self: self.session.term_height)
	prev_mode = False # запомнит предыдущий режим, т. о. к нему можно будет вернуться

class MainMenu(Mode):
	def do_render(self, cmds):
		def add_multi(synonims, *args):
			for cmd in synonims:
				cmds.add(cmd, *args)

		ci = 1
		msg = \
			           "        VISIBLE FIGHTERS v.{0}       \n".format(".".join(str(part) for part in version)) + \
			         "({0})        - новая игра -        (new)".format(ci)
		add_multi((str(ci), 'new'), lambda: self.start_new_game(), '?', lambda: self.more("Начать новую игру."))
		ci += 1

		if os.path.exists(Game.SAVE_FOLDER):
			msg += "\n({0})      - продолжить игру -    (load)".format(ci)
			add_multi((str(ci), 'load'), lambda: self.switch_to(LoadGame()), '?', lambda: self.more("Продолжить сохранённую игру."))
			ci += 1

		msg += \
			       "\n({0})         - справка -         (help)\n".format(ci) + \
			           "(0)          - выход -          (quit)"
		add_multi((str(ci), 'help'), lambda: self.more(MainMenu.Help, do_cls=True), '?', lambda: self.more("Вывести справку об основных моментах."))
		add_multi(('0', 'quit', 'exit'), lambda: self.session.post_quit(), '?', lambda: self.more("Выйти из приложения."))
		print(msg)

	def start_new_game(self):
		game = Game()
		game.gold = 100
		game.player = Fighter()
		game.player.set_weapon(Weapon())
		game.next_level = 1
		self.switch_to(AskName(game))

	Help = \
		"Ваш автомат — живой, и при использовании в бою ему будет перенаправлена часть опыта. Пули пробивают броню, но хуже масштабируются статами персонажа.\n"\
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
		self.something_new = None

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
		previews.update()
		if self.had_previews is None: self.had_previews = bool(previews.items)
		if not previews.items:
			return self.revert().more("Нет сохранений.", do_cls=self.had_previews)
		self.something_new = previews.up_new_miss

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

	def do_render(self, cmds):
		if self.first_up is not None:
			print(f"({1 + self.first_up}–{self.first_up + self.show_up}) (up)")
			cmds.add('up', lambda: self.up(), '?', lambda: self.more("Прокрутить список вверх."))

		desc_pad = len(str(self.first + self.show)) + 3 # (, число, ), пробел
		for item in self.session.previews.items[self.first : self.first + self.show]:
			for _tryIndex in range(2): # перестраховка, скорее всего, не нужно, но пусть будет
				try:
					um = self.session.previews.up_new_miss
					up_miss = um and any(um) and "  ({0})".format("/".join(s for s in (um[0] and f"+{um[0]}", um[1] and f"-{um[1]}") if s))
					self.session.previews.up_new_miss = None
					print(("\n" if item.index > self.first or self.first > 0 else "") + self.save_desc(item, desc_pad, first_line_extra = up_miss))
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
		cmds.add('remove', self.create_remove_by_number_handler(desc_pad),
			'?', lambda: self.more("Удалить сохранение{0}.".format(" (спросит номер)" if len(self.session.previews.items) > 1 else "")))
		for item in self.session.previews.items[self.first : self.first + self.show]:
			cmds.add('remove ' + str(1 + item.index), self.create_remove_request_handler(item, desc_pad), '?', lambda: self.more("Удалить это сохранение."))

		if len(self.session.previews.items) > 1:
			cmds.add('remove all', self.create_batch_remove_handler(None, "Все"), '?', lambda: self.more("Удалить все сохранения."))
			remove_inscriptions.append('remove all')

		if any(item.bad for item in self.session.previews.items):
			remove_inscriptions.append('remove bad')
			cmds.add('remove bad', self.create_batch_remove_handler(lambda item: item.bad, "Повреждённые", default_yes=True),
				'?', lambda: self.more("Удалить повреждённые сохранения."))

		if self.first_dn is not None:
			print(f"\n({1 + self.first_dn}–{self.first_dn + self.show_dn}) (down)")
			cmds.add('down', lambda: self.down(), '?', lambda: self.more("Прокрутить список вниз."))

		print("\nУдалить сохранение ({0})".format(", ".join(remove_inscriptions)))
		print("Вернуться в главное меню (quit)")
		cmds.add('force update', lambda: self.force_update(), '?', lambda: self.more("Перечитать все сохранения."))
		cmds.add('quit', lambda: self.switch_to(MainMenu()), '?', lambda: self.more("Вернуться в главное меню."))

	def do_handle_command(self, cmd):
		if cmd == "":
			if self.first_dn is not None: self.down(from_enter=True)
			else: self.first = 0
			return True

	def up(self):
		self.first = check(self.first_up, self.first_up is not None, "first_up?!") # а show всё равно обновится в process

	def down(self, from_enter=False):
		if from_enter:
			if self.something_new or self.session.previews.up_new_miss: return
			self.session.previews.update()
			if self.session.previews.up_new_miss: return
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
			if len(self.session.previews.items) == 1:
				self.create_remove_request_handler(self.session.previews.items[0], desc_pad)()
			else:
				def handle_answer(input, mode):
					if not input:
						mode.revert()
						return

					try:
						index = int(input) - 1
						if index >= 0 and index < len(self.session.previews.items):
							self.create_remove_request_handler(self.session.previews.items[index], desc_pad, extra_reverts=1)()
						else:
							raise ValueError("Неверный ввод.")
					except ValueError:
						mode.more("Нет таких.").reverts(2)
				self.prompt(f"Какое сохранение удалить? ({1 + self.first} – {self.first + self.show}) ", handle_answer)
		return remove_by_number

	def create_batch_remove_handler(self, predicate, capitalized_saves_desc, default_yes=False):
		def remove():
			total = sum(1 for item in self.session.previews.items if not predicate or predicate(item))
			def confirm(input, mode):
				removed = 0
				if (not input and default_yes) or input and 'yes'.startswith(input):
					for item in reversed(self.session.previews.items):
						if (not predicate or predicate(item)) and not self.remove_save(item, extra_reverts=1):
							check(isinstance(self.session.mode, MoreMessage), "сейчас должно висеть сообщение об ошибке remove_save")
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
		self.session.previews.post_force_update()
		self.more("Обновление...")
	prev_mode = True

class MoreMessage(Mode):
	do_prompt = False
	prev_mode = True

	def __init__(self, msg, do_cls=False):
		super().__init__()
		self.msg = msg
		self.do_cls = do_cls
		self._reverts = 1
		self.continuation = lambda mode: mode.revert(self._reverts)
		self.user_continuation = False

	def do_render(self, cmds):
		print(wrap(self.msg + ("" if self.input_comes else "\n<enter>"), self.term_width), end='')

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

class Prompt(MoreMessage):
	def __init__(self, msg, callback, lowercase_input=True):
		super().__init__(msg)
		self.callback, self.lowercase_input = callback, lowercase_input

	def do_handle_command(self, cmd):
		cmd = cmd.strip()
		self.callback(cmd.lower() if self.lowercase_input else cmd, self)
		return True
	input_comes = True

# Прогресс игрока и информация о сейве.
class Game:
	SAVE_FOLDER, SAVE_SUFFIX = os.path.join(os.path.dirname(sys.executable if getattr(sys, 'frozen', False) else __file__), 'save'), ".sav"
	SAVE_FILE_BASE_NAME_DONT_TOUCH = '\x00/' # save_file_base_name нужна для обнаружения необходимости смены имени, это — маркер «не менять»
	MAGIC = b'H,/m seX}Y', 2942819, 127

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
			self.player_name    = game and game.player.name
			self.player_level   = game and game.player.xl
			self.player_next    = game and game.player.next_percentage()
			self.weapon_name    = game and game.player.weapon.name
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
					self.session.cls_once().more("Ваши раны исцелены.")
				cmds.add('heal hp', heal_hp, '?', lambda: self.more("Полностью восстановить очки здоровья."))
			else:
				desc += " :("

		if player.spells:
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
						self.session.cls_once().more("Ваша магическая энергия восстановлена.")
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

	def do_render(self, cmds):
		game   = self.game
		player = game.player
		print("ЛАГЕРЬ")
		print(f"Золото: ${game.gold} (shop)\n")
		cmds.add('shop', lambda: self.switch_to(Shop(game)), '?', lambda: self.more("Магазин, где вы можете приобрести или продать апгрейды."))
		cmds.add('gold+', lambda: game.give_gold(100))
		cmds.add('xp+', lambda: player.receive_xp(10))
		cmds.add('xp-', lambda: player.drain_xp(10))
		cmds.add('wxp+', lambda: player.weapon.receive_xp(10))
		cmds.add('wxp-', lambda: player.weapon.drain_xp(10))

		pad = " " * (min(len(player.name), len(player.weapon.name)) + 2)
		print(self.describe_player(player, cmds, pad))
		if player.weapon:
			print("\n" + self.describe_weapon(player.weapon, cmds, pad))

		print("\nследующий уровень (next)"
			  "\nвыйти             (quit)")
		cmds.add('next', lambda: self.more("Переход к следующему уровню — TODO"), '?', lambda: self.more("Переход к следующему уровню."))
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

class Shop(Mode):
	prev_mode = True
	def __init__(self, game):
		super().__init__()
		self.game = game

	def do_render(self, cmds):
		game, player, weapon = self.game, self.game.player, self.game.player.weapon
		print("МАГАЗИН\n" +
			f"Золото: ${self.game.gold}\n" +
			"\n".join(multipad([player.living_desc(for_multipad=True), weapon.living_desc(for_multipad=True)])) +
			"\n")

		print("Апгрейды:")

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
		def upgrades_section(ups, target, min_xl=None, prohibit=None, lead="\n"):
			lines = []
			for up in ups:
				if (not min_xl or target.xl >= min_xl) and (not prohibit or not prohibit(up)) or up.find(target):
					add_upgrade(lines, up, target)
			if lines: print(lead + "\n".join(multipad(lines)))

		upgrades_section((StrUpgrade, IntUpgrade, DexUpgrade, SpeedUpgrade), player, lead='')
		upgrades_section((IncendiaryAmmunitionUpgrade, SilenceAmmunitionUpgrade, TimestopAmmunitionUpgrade), weapon,
			min_xl=2, prohibit=lambda up: up == TimestopAmmunitionUpgrade and weapon.xl < 3)
		upgrades_section((FirestormSpellUpgrade, DispellSpellUpgrade, FrailnessSpellUpgrade), player, min_xl=2)

		print("\nВернуться в лагерь (quit)")
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

class AskName(Prompt):
	def __init__(self, game, who=None, fixed=None):
		self.game, self.who = game, who or game.player
		prompt = (
			"Вам нужно зарегистрироваться, прежде чем вас официально освободят.\nКак вас зовут? " if self.who == self.game.player else
			"\nНазовите свой автомат, {0}: ".format(self.game.player.name) if self.who == self.game.player.weapon else
			internalerror(self.who, "who"))
		super().__init__(prompt, self.handle_name_input, lowercase_input=False)
		self.fixed = fixed

	def handle_name_input(self, input, mode):
		MIN, MAX = 3, 20
		gender = Gender.UNKNOWN
		if not input or MIN <= len(input) <= MAX:
			if input:
				name = cap_first(input) if self.who == self.game.player else input
				if input == name: return self.complete_name(mode, name, gender)
			else:
				if self.who == self.game.player:
					# ну не дёргать же update на каждую has_namesakes_of, лучше уж руками.
					# previews.has_namesakes_of также проверяется в query_random_fixed_name.
					mode.session.previews.update()
					self.fixed = mode.session.globals.recent_fixed_name_proposals < 1 and self.query_random_fixed_name()
					if self.fixed:
						name, gender = self.fixed[0], self.fixed[1]
					else:
						MAX_REROLLS = 10
						for _roll in range(1 + MAX_REROLLS):
							name, gender = Noun.random_name()
							if not mode.session.previews.has_namesakes_of(name): break
				elif self.who == self.game.player.weapon:
					if self.fixed and len(self.fixed) >= 4:
						name, gender = self.fixed[2], self.fixed[3]
					else:
						name, gender = "Хуец" if self.game.player.gender == Gender.FEMALE else "GAU-17", Gender.MALE
				else: internalerror(self.who, "who")

			mode.prompt(
				"{0} {1} (Y/n) ".format(
					(f"Очень приятно, {name}." if input else f"Ваше имя — {name}.") if self.who == self.game.player else
					(f"В ваших руках {name}." if input else f"Имя вашего автомата — {name}.") if self.who == self.game.player.weapon else
					internalerror(self.who, "who"),
					"Всё верно?" if input else "Продолжить?"),
				lambda input, mode: self.handle_name_confirmation(input, mode, name, gender))
		elif len(input) <= 1:
			mode.revert()
		else:
			mode.more("{0}. Длина имени должна быть от {1} до {2}.".format(
				plural(len(input), "Введ{ён/ено/ено} {N} символ{/а/ов}"), MIN, plural(MAX, "{N} символ{/а/ов}")))

	def handle_name_confirmation(self, input, mode, name, gender):
		if not input or 'yes'.startswith(input):
			self.complete_name(mode, name, gender)
		else:
			mode.revert()

	def complete_name(self, mode, name, gender):
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
		elif 'quit'.startswith(input):   mode.switch_to(MainMenu()); return
		else:                            gender = Gender.UNKNOWN

		if gender != Gender.UNKNOWN:
			self.complete(name, gender)
		else:
			mode.revert()

	def complete(self, name, gender):
		self.who.name, self.who.gender = name, gender
		if self.who == self.game.player:
			# В handle_name_input выставляется fixed, т. о. если имя и пол на этот момент соответствуют последней fixed, полагается, что пользователь согласился.
			self.session.switch_to(AskName(self.game, self.game.player.weapon, fixed=self.fixed and self.fixed[0:2] == (name, gender) and self.fixed))
		elif self.who == self.game.player.weapon:
			self.game.save_nothrow(self, then=lambda success, mode: mode.switch_to(Respite(self.game)))
		else:
			internalerror(self.who, "who")

	fixed_names = (("Рика", Gender.FEMALE), ("Мадока", Gender.FEMALE, "Розочка", Gender.FEMALE), ("Фрисия", Gender.FEMALE, "Хвост", Gender.MALE))

	def query_random_fixed_name(self):
		seen, previews = self.session.globals.last_fixed_names_seen, self.session.previews
		name, index = choose(AskName.fixed_names, lambda name, index: 0.0 if index in seen or previews.has_namesakes_of(name[0]) else 1.0, None)
		if index >= 0:
			seen.append(index)
			self.session.globals.recent_fixed_name_proposals += 1
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

		if self.mode.do_cls or self.cls_once_requested: cls()
		if self.cls_once_requested:
			self.cls_once_requested = False
			self.rerender_mode_stack_behind_current_mode()

		mode.render(cmds)
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

	# Чтобы, например, вложенные more-сообщения корректно убирались, оставляя предыдущие,
	# экран очищается и всё, что на нём должно было быть — перерисовывается.
	def rerender_mode_stack_behind_current_mode(self):
		chain = []
		mode = self.mode
		while mode:
			chain.append(mode)
			if mode.do_cls: break
			mode = mode.prev_mode

		for mode in chain[-1:0:-1]:
			mode.render(DummyCommands)
			print(mode.last_input)

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

		__slots__= ('items', 'fn2it', 'max_order_key', 'last_listing', 'first_update', 'up_new_miss')
		def __init__(self):
			self.items = self.fn2it = self.max_order_key = self.last_listing = self.first_update = self.up_new_miss = None
			self.post_force_update()

		def post_force_update(self):
			self.items  = []
			self.fn2it  = {} # ключ — имя файла относительно SAVE_FOLDER, значение — Item.
			self.max_order_key = -1
			self.last_listing = [] # содержимое SAVE_FOLDER в последний раз.
			self.first_update = True # seen будет выставлена всем сохранениям, загруженным по post_force_update
			                         # (в т. ч. первый раз после создания PreviewsList), чтобы им не рисовались звёздочки
			self.up_new_miss = None  # (число новых, число удалённых) НЕУЧТЁННЫХ ЧЕРЕЗ NOTE_ с последнего раза (для отладки)

		# Обнаружить изменения в папке сохранений, или загрузить всё в первый раз.
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
				item.seen = self.first_update
				if next_item < len(self.items): # новые вставляются в хвост, оставшийся от удалённых, пока возможно
					self.items[next_item] = item
				else:
					self.items.append(item)
				self.fn2it[item.rel_save_path] = item
				next_item += 1
			assert next_item <= len(self.items)
			del self.items[next_item:] # отрезать пустой хвост; если он был исчерпан, то next_item == len(items) и это no-op
			self.up_new_miss = (len(appeared), missing) if (appeared or missing) and not self.first_update else None
			self.first_update = False

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

		def note_add(self, full_save_path, rel_save_path, preview):
			assert self.sanitycheck()
			check(full_save_path, "full_save_path?!", rel_save_path, "rel_save_path?!")
			check(full_save_path, full_save_path.startswith(Game.SAVE_FOLDER), "абсолютный плес")
			check(rel_save_path, not rel_save_path.startswith(Game.SAVE_FOLDER) and full_save_path.endswith(rel_save_path), "относительный плес")
			if rel_save_path in self.fn2it: internalerror("сохранение {0} уже существует, исп. note_update".format(rel_save_path)) # ух, паранойя замучила

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

		def has_namesakes_of(self, name): # это очень медленно, но пока не горит, чтобы усложнять всё, добавляя dict() тёзок...
			name = name.lower()
			return any(item.preview and item.preview.player_name.lower() == name for item in self.items)

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