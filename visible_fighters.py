import os, string, pickle, textwrap, time, math, random
from collections import OrderedDict
version = (0, 2)

class config:
	min_term_width, min_term_height = 80, 25

def internalerror(*args):
	if len(args) == 1: raise Exception(f"Внутренняя ошибка: {args[0]}.")
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
# Например: hp = check(new_hp, new_hp > 0, "недопустимое значение hp").
#
# 2. check(условие 1, internalerror при невыполнении условия 1, ...)
def check(*args):
	if len(args) == 3:
		what, cond, errmsg = args[0], args[1], args[2]
		return what if cond else internalerror(errmsg, what)
	else:
		for i in range(len(args) // 2):
			if not args[2*i]: internalerror(args[2*i+1])

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

def clamp(n, a, b):
	return n if (n >= a) and (n <= b) else b if n > b else a

# округляет 8.2 до 8 с шансом 80% или 9 с шансом 20%
def rand_round(x):
	f = math.floor(x)
	d = x - f
	return f + int(d > 0 and random.random() < d)

# Главная причина существования этой функции в том, что textwrap.wrap, похоже, не обрабатывает \n.
#
# Если в строку добавлен |, то её хвост начнётся с этой позиции, например:
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

class Test:
	class Failed(Exception): pass
	def setup(self): pass
	def teardown(self): pass
	def describe(self, *desc): return ""

	cases = None
	def one(self, *args): raise NotImplementedError("one(*cases[i])")

	def expect_equal(self, got, expected, name, *desc):
		desc = self.describe(*desc)
		if got != expected: raise Test.Failed("{0}{1}{2} = {3}, ожидается {4}".format(desc, ": " if desc else "", name, got, expected))

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
# Можно использовать составные команды (без них реализация укладывалась в 15 строк, хех мда):
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
		self.root = Commands.node(None, None)

	def add(self, *args):
		# можно сделать nodes = [self.root] и убрать node, но это будет создавать мусор,
		# реально нужный, только когда используется форма .add(("a", "a_synonym"), funcA, ...)
		node, nodes = self.root, None

		iarg = 0
		while iarg < len(args):
			cmd, func = args[iarg], args[iarg+1]
			iarg += 2

			if isinstance(cmd, str):
				if node: node = node.add(cmd, func)
				if nodes:
					for i in range(len(nodes)):
						nodes[i] = nodes[i].add(cmd, func)
			else:
				new_nodes = []
				for one in cmd:
					if node: new_nodes.append(node.add(one, func))
					if nodes: new_nodes.extend(node.add(one, func) for node in nodes)
				node, nodes = None, new_nodes

	# Пока на всякий случай оставлю.
	def guess_v1(self, input):
		def suggestions(node): # В корне потенциально много команд, так что подсказывать только для частично введённых, т. е. имеющих node.parent.
			return node.parent and [child.backtrack() for child in node.childs.values()]

		node = self.root
		for subcommand in Commands.split(input):
			child = node.childs.get(subcommand, None) # точное совпадение
			if child:
				node = child
			else:
				matching = [child for cmd, child in node.childs.items() if cmd.startswith(subcommand)] # неточные совпадения
				if len(matching) == 1:
					node = matching[0]
				else:
					return None, matching and [child.backtrack() for child in matching] or None, not matching and suggestions(node) or None

		while node != self.root and len(node.childs) == 1 and not node.func: # однозначные продолжения команды, например, введено hit и есть только hit body
			node = next(iter(node.childs.values()))
		return node.func, not node.func and suggestions(node) or None, None

	# Засрал всё до магии, которую сам с трудом понимаю, зато теперь угадывает "hit body strong" по "h b s", даже если есть другие команды на "h" или "h b".
	def guess_v2(self, input):
		def suggestions(matches, unfold):
			# Развернуть детей? Например, развернёт матч "hit body" в гипотетические "hit body strong" и "hit body weak"
			unfold = unfold or len(matches) == 1

			# В корне потенциально много команд, так что подсказывать только для частично введённых, т. е. имеющих node.parent.
			return [node.backtrack() for match in matches for node in (match.childs.values() if match.childs and match.parent and unfold else (match,)) if node.parent]

		matches = [self.root]
		for subcommand in Commands.split(input):
			new_matches = []
			for node in matches:
				child = node.childs.get(subcommand, None) # точное совпадение
				if child:
					new_matches.append(child)
				else:
					new_matches.extend(child for cmd, child in node.childs.items() if cmd.startswith(subcommand)) # неточные совпадения

			if not new_matches: # введено a b c, когда есть только a b → возврат подсказок по a b
				return None, None, suggestions(matches, False) or None
			matches = new_matches

		for i, node in enumerate(matches):
			while node.parent and len(node.childs) == 1 and not node.func: # однозначные продолжения команды, например, введено hit и есть только hit body
				node = matches[i] = next(iter(node.childs.values()))

		# "or None" — чтобы в тестах можно было проверять на равенство, не заботясь о False или [].
		return len(matches) == 1 and matches[0].func or None, (len(matches) > 1 or not matches[0].func) and suggestions(matches, len(matches) == 1) or None, None
	
	def guess(self, input):
		return self.guess_v2(input)

	@staticmethod
	def split(cmd):
		i, r = 0, []
		while i < len(cmd):
			start_cls = Commands.classify_sym(cmd[i])
			if start_cls >= 0:
				start = i
				while i+1 < len(cmd) and Commands.classify_sym(cmd[i+1]) == start_cls: i += 1
				r.append(cmd[start:i+1])
			i += 1
		return r

	@staticmethod
	def classify_sym(sym): return (
		-1 if sym in string.whitespace else
		0 if sym in string.ascii_letters else
		1 if sym in string.digits else
		2)
	
	class node:
		def __init__(self, name, parent):
			self.childs = OrderedDict()
			self.func   = None
			self.name   = name
			self.parent = parent

		def add(self, cmd, func):
			node = self
			for subcommand in Commands.split(cmd):
				child = node.childs.get(subcommand, None)
				if not child:
					child = Commands.node(subcommand, node)
					node.childs[subcommand] = child
				node = child
			if node.func: raise Exception("Команда {0} уже определена.".format(node.backtrack()))
			node.func = func
			return node
		
		def backtrack(self):
			node, path = self, []
			while node.parent:
				path.append(node.name)
				node = node.parent

			# в command? пробел не нужен (можно, но не смотрится), в command subcommand — нужен
			def choose_separator_before(i):
				return "" if Commands.classify_sym(path[i][0]) != Commands.classify_sym(path[i+1][-1]) else " "
			return ''.join(path[i//2] if i%2 == 0 else choose_separator_before(i//2) for i in range(2*len(path)-2, -1, -1))

class DummyCommands:
	@staticmethod
	def add(*args): pass

class CommandsTest(Test):
	def describe(self, adds, query):
		return str(adds) + ", " + query

	cases = \
		(
			(
				(("one two three", "123"), ("one two four", "124"), ("one three six", "136")),
				(
					("o t", (None, ["one two", "one three six"], None)),
					("o t t", ("123", None, None)),
					("o t s", ("136", None, None)),
				)
			),
		)
	def one(self, adds, queries):
		cmds = Commands()
		for add in adds: cmds.add(*add)
		for query, expect in queries:
			self.expect_equal(cmds.guess(query), expect, "guess", adds, query)

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
		check(self.applied, "not applied", self.ran_out, "not ran_out",
			self in self.victim.hexes, "hex not in self.hexes", self in self.master.caused_hexes, "hex not in master.caused_hexes")
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

	npower = property(lambda self: self.power / Hex.BASELINE_POWER)
	BASELINE_POWER = 100
	dispellable = False
	time_based = True

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

	def do_cmd(self): return "rage"

class RageHexTest(Test):
	def setup(self): self.dummy = RageHex.__new__(RageHex)
	def describe(self, *desc): return f"power = {self.dummy.power}"

	cases = ((-1000, 1.2, 1.1), (0, 1.2, 1.1), (Hex.BASELINE_POWER, 1.5, 1.2), (1100, 4.5, 2.2), (1267, 5, 2.2), (9999, 5, 2.2))
	def one(self, power, ref_physdam_x, ref_backlash_x):
		self.dummy.power = power
		self.expect_equal(round(self.dummy.physdam_x, 1), ref_physdam_x, "physdam_x")
		self.expect_equal(round(self.dummy.backlash_x, 1), ref_backlash_x, "backlash_x")

class DeathWordHex(Hex):
	def do_finish(self):
		check(self.master.alive, "Смертный приговор пережил автора")
		if self.victim.alive:
			self.victim.die("в исполнение Смертного приговора", self.master)

	def do_name(self): return "Смертный приговор"
	def do_detail(self): return \
		"Гарантированная смерть через {turns}.\n"\
		"Вы можете снять этот хекс с помощью Развеивания либо убив мага, наложившего заклинание.".format(turns = plural(self.turns, "{N} ход{/а/ов}"))

	def do_cmd(self): return "deathword"
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

	def do_cmd(self): return "bleeding"

	@staticmethod
	def decay_power(power): return power * Bleeding.POWER_DECAY

	@staticmethod
	def turns_from_power(power): return clamp(math.ceil(math.log(0.5 * Hex.BASELINE_POWER / power, Bleeding.POWER_DECAY)), 3, 20)

	precise_hp_percentile_decay = property(lambda self: clamp(2.5 * (self.npower**0.5 if self.npower > 1 else self.npower), 1, 5))
	precise_dex_debuff = property(lambda self: 3 * self.npower**0.5)
	POWER_DECAY = 0.9

class Spell:
	pass

class Upgrade:
	TARGET_CLASS = property(lambda self: Living)
	def __init__(self):
		self.applied = False
		self.target = None
		self.ap_taken, self.gold_taken = 0, 0

	def apply(self, target, ap=None, gold=None):
		check(not self.applied, "already applied")
		ap, gold = ap if ap is not None else self.ap_cost(target), gold if gold is not None else self.gold_cost(target)
		check(target.ap_used + ap <= target.ap_limit, "not enough AP")

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

	# Проверяет физическую возможность добавить апгрейд (но не цену в золоте).
	@classmethod
	def allow(cls, target):
		return cls.do_allow(target) and target.enough_ap_for(cls)

	# По умолчанию апгрейд полагается уникальным.
	@classmethod
	def do_allow(cls, target): return not cls.find(target)

	# Находит апгрейд этого типа среди апгрейдов target, или возвращает None
	@classmethod
	def find(cls, target): return next(cls.find_all(target), None)

	# Находит все апгрейды этого типа среди апгрейдов target (например, апгрейды статов можно взять несколько раз)
	@classmethod
	def find_all(cls, target): return (up for up in target.upgrades if isinstance(up, cls))

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
		setattr(target, 'base_' + self.stat, getattr(target, 'base_' + self.stat) + self.amount)

	def do_revert(self, target):
		setattr(target, 'base_' + self.stat, getattr(target, 'base_' + self.stat) - self.amount)

	@classmethod
	def do_allow(cls, target): return sum(up.AMOUNT for up in cls.find_all(target)) + cls.AMOUNT <= cls.LIMIT

	@classmethod
	def do_ap_cost(cls, target): return 1

	@classmethod
	def do_cmd(cls): return cls.STAT

class StrUpgrade(StatUpgrade):
	STAT, AMOUNT, LIMIT = 'str', 5, 20

	@classmethod
	def do_gold_cost(cls, target): return 120 + 30 * cls.count(target)

class IntUpgrade(StatUpgrade):
	STAT, AMOUNT, LIMIT = 'int', 5, 20

	@classmethod
	def do_gold_cost(cls, target): return 135 + 35 * cls.count(target)

class DexUpgrade(StatUpgrade):
	STAT, AMOUNT, LIMIT = 'dex', 5, 20

	@classmethod
	def do_gold_cost(cls, target): return 70 + 25 * cls.count(target)

class SpeedUpgrade(StatUpgrade):
	STAT, AMOUNT, LIMIT = 'spd', 30, 150

	@classmethod
	def do_gold_cost(cls, target): return 150 + 50 * sum(1 for up in cls.find_all(target))

class SpellUpgrade(FighterUpgrade):
	def __init__(self, spell):
		super().__init__()
		self.spell = check(spell, isinstance(spell, Spell), "spell?!")
		self.applied = None

	def do_apply(self, target):
		target.learn_spell(self.spell)

	def do_revert(self, target):
		target.forget_spell(self.spell)

class AmmunitionKind:
	LIST_ORDER = None
	MAX_CHARGES = None
	INFINITE_CHARGES = None

	def __init__(self):
		self.charges = check(self.MAX_CHARGES, not self.MAX_CHARGES or 1 <= self.MAX_CHARGES <= 99, "MAX_CHARGES?!")

class IncendiaryAmmunition(AmmunitionKind):
	LIST_ORDER = 0
	MAX_CHARGES = AmmunitionKind.INFINITE_CHARGES

class SilenceAmmunition(AmmunitionKind):
	LIST_ORDER = 1
	MAX_CHARGES = 5

class TimestopAmmunition(AmmunitionKind):
	LIST_ORDER = 2
	MAX_CHARGES = 2

class AmmunitionUpgrade(WeaponUpgrade):
	AMMUNITION_CLASS = AmmunitionKind

	def do_apply(self, target):
		ammo_class = check(self.AMMUNITION_CLASS, issubclass(self.AMMUNITION_CLASS, AmmunitionKind) and self.AMMUNITION_CLASS is not AmmunitionKind, "AMMUNITION_CLASS?!")
		target.install_special_ammo(ammo_class)

	def do_revert(self, target):
		target.uninstall_special_ammo(ammo_class)

class IncendiaryAmmunitionUpgrade(AmmunitionUpgrade):
	AMMUNITION_CLASS = IncendiaryAmmunition

	@classmethod
	def do_allow(cls, target): return cls.count(target) + 1 <= 3

	@classmethod
	def do_ap_cost(cls, target): return 1

	@classmethod
	def do_gold_cost(cls, target): return 100 + 30 * cls.count(target)

class SilenceAmmunitionUpgrade(AmmunitionUpgrade):
	@classmethod
	def do_ap_cost(cls, target): return 2

	@classmethod
	def do_gold_cost(cls, target): return 200

class TimestopAmmunitionUpgrade(AmmunitionUpgrade):
	@classmethod
	def do_ap_cost(cls, target): return 3

	@classmethod
	def do_gold_cost(cls, target): return 350

class Gender:
	MALE   = 0
	FEMALE = 1

class Living:
	ap_limit = property(lambda self: 1 + 2*(self.xl - 1))

	def __init__(self):
		self.xp = 0
		self.xl = 1
		self.ap_used = 0
		self.name = "Баг"
		self.upgrades = []

	def receive_xp(self, amount):
		self.xp += amount
		while self.xp >= self.xp_for_levelup(self.xl) and self.xl < self.LEVEL_CAP:
			self.xp -= self.xp_for_levelup(self.xl)
			self.level_up()

	def level_up(self):
		self.xl += 1

	LEVEL_CAP = 1
	def xp_for_levelup(self, xl):
		return 10 * xl

	def enough_ap_for(self, upgrade_or_whatever):
		ap_cost = (
			upgrade_or_whatever if isinstance(upgrade_or_whatever, int) else
			upgrade_or_whatever.ap_cost(self))

		return self.ap_used + ap_cost <= self.ap_limit

class Fighter(Living):
	hp   = property(lambda self: self.cur_hp)
	mhp  = property(lambda self: max(1, round(self.base_mhp * (1 + (self.str - 10) / 10))))
	dead = property(lambda self: not not self.death_cause)
	alive = property(lambda self: not self.dead)
	mp   = property(lambda self: self.cur_mp)
	mmp  = property(lambda self: round(self.base_mmp * (1 + (self.int - 10) / 10)))
	str  = property(lambda self: self.base_str)
	int  = property(lambda self: self.base_int)
	dex  = property(lambda self: self.base_dex)
	spd  = property(lambda self: self.base_spd)
	ac   = property(lambda self: self.base_ac)
	ev   = property(lambda self: max(0, self.base_ev + (self.dex - 10)))
	LEVEL_CAP = 7

	def __init__(self):
		Living.__init__(self)
		self.name     = "Баг"
		self.base_mhp = 10
		self.base_mmp = 10
		self.base_str = 10
		self.base_int = 10
		self.base_dex = 10
		self.base_spd = 100
		self.base_ac = 0
		self.base_ev = 10
		self.death_cause = None
		self.gender = Gender.MALE

		self.hexes = set()
		self.caused_hexes = set()
		self.weapon = None

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
			hex.tick()
			if hex.ran_out: ran_out.append(hex)

		for hex in ran_out:
			hex.unapply()

	def set_weapon(self, weapon):
		if self.weapon: self.weapon.owner = None
		self.weapon = weapon
		self.weapon.owner = self

class Weapon(Living):
	ap_limit = property(lambda self: 1 + (self.xl - 1))
	LEVEL_CAP = 5

	def __init__(self):
		Living.__init__(self)
		self.name = "Баг"
		self.owner = None

class Arena:
	pass

class Con:
	# На данный момент сделано так, что чуть больше нуля даёт [#....] и чуть меньше максимума — [####.]
	@staticmethod
	def vital_bar(cur, max, divs=10, fillchar='#', emptychar='.'):
		fill = int(clamp(divs * (cur / max), 0 if cur <= 0 else 1, divs))
		return "[{0}{1}]".format(fillchar * fill, emptychar * (divs - fill))

	@staticmethod
	def bullet_bar(cur, max, fillchar='#', emptychar='.'):
		return fillchar * cur + emptychar * (max - cur)

class VitalBarTest(Test):
	def describe(self, cur, max): return f"HP = {cur}/{max}"

	cases = ((0, 5, 5, 0), (1, 5, 5, 1), (2, 5, 5, 2), (3, 5, 5, 3), (4, 5, 5, 4), (5, 5, 5, 5), (0.001, 5, 5, 1), (4.999, 5, 5, 4), (1.4, 5, 5, 1))
	def one(self, cur, max, divs, expect_bars):
		self.expect_equal(Con.vital_bar(cur, max, divs), "[{0}{1}]".format('#' * expect_bars, '.' * (divs - expect_bars)), "vital_bar", cur, max)

class Mode:
	def __init__(self):
		self.session = None
		self.last_input = None

	def render(self, cmds): self.do_render(cmds)
	def do_render(self, cmds): raise NotImplementedError("do_render")

	def handle_command(self, cmds): return self.do_handle_command(cmds)
	def do_handle_command(self, cmd): return False

	def switch_to(self, mode):
		self.session.switch_to(mode)

	def revert(self):
		check(self.session.mode == self, "session.mode != self")
		return self.session.revert()

	def more(self, msg, do_cls=False):
		self.switch_to(MoreMessage(msg, do_cls))

	do_prompt = True
	do_cls    = True
	term_width = property(lambda self: self.session.term_width)
	term_height = property(lambda self: self.session.term_height)
	prev_mode = False # запомнит предыдущий режим, т. о. к нему можно будет вернуться

class MainMenu(Mode):
	def do_render(self, cmds):
		print(
			"        VISIBLE FIGHTERS v.{0}       \n"\
			"(1)        - новая игра -        (new)\n"\
			"(2)      - загрузить игру -     (load)\n"\
			"(3)         - справка -         (help)\n"\
			"(0)          - выход -          (quit)".format(".".join(str(part) for part in version)))

		cmds.add(('1', 'new'), lambda: self.switch_to(AskName()), '?', lambda: self.more("Начать новую игру."))
		cmds.add(('2', 'load'), lambda: self.switch_to(MainMenu()), '?', lambda: self.more("Продолжить сохранённую игру."))
		cmds.add(('3', 'help'), lambda: self.more(MainMenu.Help, do_cls=True), '?', lambda: self.more("Вывести справку об основных моментах."))
		cmds.add(('0', 'quit'), lambda: self.session.post_quit(), '?', lambda: self.more("Выйти из приложения."))

	Help = \
		"Ваш автомат — живой, и при использовании в бою ему будет перенаправлена часть опыта. Пули пробивают броню, но не масштабируются статами персонажа.\n"\
		"\n"\
		"Сила      (STR) — |влияет на силу ударов и максимум HP.\n"\
		"Интеллект (INT) — |на максимум маны, силу заклинаний и сопротивление магии.\n"\
		"Ловкость  (DEX) — |на точность ударов, шанс уворота и критических ударов.\n"\
		"Скорость  (SPD) — |на инициативу в бою. Например, если ваша скорость 150, а противника 100, на три ваших действия будут приходиться два действия противника.\n"\
		"\n"\
		"Между боями вы можете тратить золото на апгрейды в пределах полученного опыта. Золото за даунгрейд компенсируется частично.\n"\
		"В игре 10 уровней.\n"\
		"\n"\
		"Можно сокращать команды до префиксов: heal hp -> h h, b.fire? -> b.f?.\n"\
		"                                                            ^       ^\n"\
		"                                                    |\"?\" выводит справку по команде или подписанному элементу экрана."

class MoreMessage(Mode):
	do_prompt = False
	prev_mode = True

	def __init__(self, msg, do_cls=False):
		self.msg = msg
		self.do_cls = do_cls

	def do_render(self, cmds):
		print(wrap(self.msg + ("" if self.input_comes else "\n<enter>"), self.term_width), end='')

	def do_handle_command(self, cmd):
		self.revert()
		return True
	input_comes = False

class Prompt(MoreMessage):
	def __init__(self, msg, callback):
		super().__init__(msg)
		self.callback = callback

	def do_handle_command(self, cmd):
		self.callback(cmd.strip(), self)
		return True
	input_comes = True

# Весь прогресс игрока.
class GameState:
	def __init__(self):
		self.gold       = 0
		self.player     = Fighter()
		self.player.name = "Рика"
		self.player.set_weapon(Weapon())
		self.player.weapon.name = "Хуец"
		self.player.receive_xp(160)
		StrUpgrade().apply(self.player, 1, 1)
		IntUpgrade().apply(self.player, 1, 1)
		DexUpgrade().apply(self.player, 1, 1)
		self.next_level = 0

# Экран между боями.
class Respite(Mode):
	def __init__(self, game):
		self.game = game

	def describe_living(self, being):
		next = being.xl < being.LEVEL_CAP and math.floor(being.xp / being.xp_for_levelup(being.xl) * 1000) / 10
		desc = "{0.name}: уровень {0.xl}{1}, умения: {0.ap_used}/{0.ap_limit}".format(being, f" (след. {next:.0f}%)" if next is not False else "")
		return desc

	def describe_player(self, player, cmds):
		desc = self.describe_living(player)
		name_pad = " " * (min(len(player.name), len(player.weapon.name)) + 2)
		allow_str_up = StrUpgrade.allow(player)
		allow_int_up = IntUpgrade.allow(player)
		allow_dex_up = DexUpgrade.allow(player)
		allow_spd_up = SpeedUpgrade.allow(player)

		desc += "\n" +\
			name_pad + "HP: " + Con.vital_bar(player.hp, player.mhp) + f" {player.hp}/{player.mhp}\n" + \
			name_pad + "MP: " + Con.vital_bar(player.mp, player.mmp) + f" {player.mp}/{player.mmp}\n" + \
			name_pad + f"STR {player.str}" + (" (" + StrUpgrade.cmd() + "+)" if allow_str_up else "") + "\n" + \
			name_pad + f"INT {player.int}" + (" (" + IntUpgrade.cmd() + "+)" if allow_int_up else "") + "\n" + \
			name_pad + f"DEX {player.dex}" + (" (" + DexUpgrade.cmd() + "+)" if allow_dex_up else "") + "\n" + \
			name_pad + f"SPD {player.spd}" + (" (" + SpeedUpgrade.cmd() + "+)" if allow_spd_up else "")

		if allow_str_up: cmds.add(StrUpgrade.cmd() + '+', lambda: StrUpgrade().apply(player))
		if allow_int_up: cmds.add(IntUpgrade.cmd() + '+', lambda: IntUpgrade().apply(player))
		if allow_dex_up: cmds.add(DexUpgrade.cmd() + '+', lambda: DexUpgrade().apply(player))
		if allow_spd_up: cmds.add(SpeedUpgrade.cmd() + '+', lambda: SpeedUpgrade().apply(player))

		disable_cmds = set()
		prev = {}
		for up in player.upgrades:
			duplicate = prev.get(type(up), None)
			if duplicate: disable_cmds.add(duplicate)
			prev[type(up)] = up

		for up in player.upgrades:
			remove_cmd = up not in disable_cmds and up.cmd() + '-'
			help_cmd = up not in disable_cmds and up.cmd() + '?'
			desc += "\n" + name_pad + type(up).__name__ + f": {up.ap_taken} AP, ${up.gold_taken}" + (f" ({remove_cmd})" if remove_cmd else "")

			if remove_cmd:
				def make_revert_func(up):
					def revert():
						up.revert(player)
					return revert
				cmds.add(remove_cmd, make_revert_func(up))

			if help_cmd: cmds.add(help_cmd, lambda: self.more("TODO: описание апгрейда"))

		def confirm_quit(input, mode):
			if input.lower() == 'y': mode.switch_to(MainMenu())
			else: mode.revert()
		cmds.add('quit', lambda: self.switch_to(Prompt("Выйти без сохранения? (y/N) ", confirm_quit)))
		return desc

	def describe_weapon(self, weapon, cmds):
		desc = self.describe_living(weapon)
		name_pad = " " * (min(len(weapon.name), len(weapon.owner.name)) + 2)
		return desc

	def do_render(self, cmds):
		game   = self.game
		player = game.player
		print(f"Золото: ${game.gold} (shop)\n")
		cmds.add('shop', lambda: self.more("Магазин: TODO"), '?', lambda: self.more("Магазин, где вы можете приобрести или продать апгрейды."))

		print(self.describe_player(player, cmds))

		if player.weapon:
			print("\n" + self.describe_weapon(player.weapon, cmds))

class AskName(Prompt):
	def __init__(self, game=None, who=None):
		if not game: game = GameState()
		if not who: who = game.player

		super().__init__("Как вас зовут? " if who == game.player else "\nНазовите свой автомат: " if who == game.player.weapon else internalerror(who, "who"), self.handle_name_input)
		self.game = game
		self.who = who

	def handle_name_input(self, input, mode):
		MIN, MAX = 3, 20
		if not input or MIN <= len(input) <= MAX:
			if input:
				name = input[0].capitalize() + input[1:]
				if input == name: return self.complete(name)
			else:
				name = self.who.name

			mode.switch_to(Prompt(
				"{0} — {1}. Продолжить? (Y/n/q) ".format(
					"Ваше имя" if self.who == self.game.player else "Имя вашего автомата" if self.who == self.game.player.weapon else internalerror(who, "who"),
					name),
				lambda input, mode: self.handle_name_confirmation(input, mode, name)))
		else:
			mode.more("{0}. Длина имени должна быть от {1} до {2}.".format(plural(len(input), "Введ{ён/ено/ено} {N} символ{/а/ов}"), MIN, plural(MAX, "{N} символ{/а/ов}")))

	def handle_name_confirmation(self, input, mode, name):
		if not input or input.lower() == 'y':
			self.complete(name)
		elif 'quit'.startswith(input.lower()):
			mode.switch_to(MainMenu())
		else:
			mode.revert()

	def complete(self, name):
		if self.who == self.game.player:
			self.game.player.name = name
			self.session.switch_to(AskName(self.game, self.game.player.weapon))
		elif self.who == self.game.player.weapon:
			self.game.player.weapon.name = name
			self.session.switch_to(Respite(self.game))
		else:
			internalerror(who, "who")

# Ввод-вывод и стек экранов.
class Session:
	def __init__(self, start=None):
		self.mode = None
		self.term_width, self.term_height = None, None
		self.quit_posted = False
		self.cls_once_requested = False
		self.switch_to(start or MainMenu())

	def switch_to(self, new_mode, reverting=False):
		check(isinstance(new_mode.prev_mode, bool) or new_mode == self.mode.prev_mode, "prev_mode?!")
		# запомнить prev_mode только при условии, что а) это явно требуется (prev_mode = True) и б) это не возврат к prev_mode
		if new_mode.prev_mode and not reverting: new_mode.prev_mode = self.mode
		self.mode = new_mode
		self.mode.session = self

	def revert(self):
		prev_mode = check(self.mode.prev_mode, isinstance(self.mode.prev_mode, Mode), "prev_mode?!")
		self.switch_to(prev_mode, reverting=True)
		self.cls_once()
		return prev_mode

	def process(self):
		cmds = Commands()
		self.term_width, self.term_height = os.get_terminal_size()
		self.check_term_size()

		if self.mode.do_cls or self.cls_once_requested: cls()
		if self.cls_once_requested:
			self.cls_once_requested = False
			self.rerender_mode_stack_behind_current_mode()

		self.mode.render(cmds)
		has_default_commands = cmds.root.childs
		if has_default_commands: self.add_default_commands(cmds)
		if self.mode.do_prompt: print('\n> ', end='')
		try:
			cmd = input()
			self.mode.last_input = cmd
		except KeyboardInterrupt:
			self.post_quit()
			return print()

		fn, matches, suggestions = cmds.guess(cmd)
		if fn: fn()
		elif self.mode.handle_command(cmd): pass
		elif matches: self.mode.more("Неоднозначная команда: {0}.".format(", ".join(matches)))
		elif suggestions: self.mode.more("Неизвестная команда. Попробуйте {0}.".format(", ".join(suggestions)))
		elif cmd and not cmd.isspace(): self.mode.more("Неизвестная команда." + (" Попробуйте \"?\"." if has_default_commands else ""))
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
		list = []
		for cmd, node in cmds.root.childs.items():
			while not node.func and len(node.childs) == 1: node = next(node for node in node.childs.values())
			list.append(node.backtrack())

		av = ", ".join(cmd for cmd in list if cmd != "?")
		return "Доступные команды: " + av + "." if av else "Нет доступных команд."

	def cls_once(self):
		self.cls_once_requested = True

	# Чтобы, например, вложенные more-сообщения корректно убирались, оставляя предыдущие,
	# экран очищается и всё, что на нём должно было быть — перерисовывается.
	def rerender_mode_stack_behind_current_mode(self):
		chain = []
		mode = self.mode.prev_mode
		while mode:
			chain.append(mode)
			if mode.do_cls: break
			mode = mode.prev_mode

		for mode in reversed(chain):
			mode.render(DummyCommands)
			if mode.do_prompt: print("\n> ", end='')
			print(mode.last_input)

def selftest():
	tests, fails = [], []
	account = False
	def run(name, cases, one):
		count = 0
		for case in cases:
			try:
				one(*case)
			except Exception as e:
				fails.append("Тест {0} #{1} {2}. {3}".format(name, count, "провален" if isinstance(e, Test.Failed) else "упал", ''.join(e.args)))
			count += 1
		if account: tests.append(name + f" x{count}" if count > 1 else "")

	ticks = time.clock()
	for name, value in globals().items():
		if isinstance(value, type) and issubclass(value, Test) and value is not Test:
			test = value()
			test.setup()
			run(name[:-len("Test")] if name.endswith("Test") and len(name) > len("Test") else name, test.cases, test.one)
			test.teardown()
	ticks = time.clock() - ticks

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