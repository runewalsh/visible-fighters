import os, string, pickle, textwrap, math, random, traceback, tempfile, time
from collections import namedtuple, OrderedDict
version = (0, 2)

class config:
	min_term_width, min_term_height = 80, 25

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

def exception_msg(e):
	return str(e) or repr(e)

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

	# Засрал всё до магии, которую сам с трудом понимаю, зато теперь угадывает "hit body strong" по "h b s", даже если есть другие команды на "h" или "h b".
	def guess(self, input):
		def suggestions(matches):
			# Развернуть детей? Например, развернёт матч "hit body" в гипотетические "hit body strong" и "hit body weak"
			unfold = len(matches) == 1 and (len(matches[0].childs) > 1 or not matches[0].func)

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
				return None, None, suggestions(matches) or None
			matches = new_matches

		for i in range(len(matches)):
			matches[i] = matches[i].down_to_unambiguous() # однозначные продолжения команды, например, введено hit и есть только hit body

		# "or None" — чтобы в тестах можно было проверять на равенство, не заботясь о False или [].
		return len(matches) == 1 and matches[0].func or None, (len(matches) > 1 or not matches[0].func) and suggestions(matches) or None, None

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
		0 if sym in string.ascii_letters or sym in string.digits else
		1)

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
			if node.func: raise RuntimeError("Команда {0} уже определена.".format(node.backtrack()))
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

		def down_to_unambiguous(self):
			node = self
			while not node.func and len(node.childs) == 1 and node.parent: node = next(node for node in node.childs.values())
			return node

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

	npower = property(lambda self: self.power / self.BASELINE_POWER)
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

	def do_cmd(self): return 'rage'

class RageHexTest(Test):
	def __init__(self): self.dummy = None
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
		rv = target.save_relative_vitals()
		setattr(target, 'base_' + self.stat, getattr(target, 'base_' + self.stat) + self.amount)
		target.restore_relative_vitals(rv)

	def do_revert(self, target):
		rv = target.save_relative_vitals()
		setattr(target, 'base_' + self.stat, getattr(target, 'base_' + self.stat) - self.amount)
		target.restore_relative_vitals(rv)

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
			self.weapon.ammos.append(self)
			self.weapon.ammos.sort(key=lambda ammo: ammo.LIST_ORDER)

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

	def short_name(self): return self.do_short_name()
	def do_short_name(self): raise NotImplementedError("do_short_name")

	def cmd(self): return self.do_cmd()
	def do_cmd(self): raise NotImplementedError("do_cmd")

class IncendiaryAmmunition(Ammunition):
	LIST_ORDER = 0
	MAX_CHARGES = Ammunition.INFINITE_CHARGES

	def times(self):
		return 1 + (len(self.secondary_installations) if self.secondary_installations else 0)

	def do_short_name(self): return f"заж.+{3 * self.times()}"
	def do_cmd(self): return 'shoot'

class SilenceAmmunition(Ammunition):
	LIST_ORDER = 1
	MAX_CHARGES = 5

	def do_recharge_cost(self): return 50
	def do_short_name(self): return "тиш."
	def do_cmd(self): return 'silence'

class TimestopAmmunition(Ammunition):
	LIST_ORDER = 2
	MAX_CHARGES = 2

	def do_recharge_cost(self): return 100
	def do_short_name(self): return "врем."
	def do_cmd(self): return 'timestop'

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

class IncendiaryAmmunitionUpgrade(AmmunitionUpgrade):
	AMMUNITION_CLASS = IncendiaryAmmunition

	@classmethod
	def do_allow(cls, target): return cls.count(target) + 1 <= 3

	@classmethod
	def do_ap_cost(cls, target): return 1

	@classmethod
	def do_gold_cost(cls, target): return 100 + 30 * cls.count(target)

	@classmethod
	def do_cmd(cls): return 'incendiary'

class SilenceAmmunitionUpgrade(AmmunitionUpgrade):
	AMMUNITION_CLASS = SilenceAmmunition

	@classmethod
	def do_ap_cost(cls, target): return 2

	@classmethod
	def do_gold_cost(cls, target): return 200

	@classmethod
	def do_cmd(cls): return 'silence'

class TimestopAmmunitionUpgrade(AmmunitionUpgrade):
	AMMUNITION_CLASS = TimestopAmmunition
	@classmethod
	def do_ap_cost(cls, target): return 3

	@classmethod
	def do_gold_cost(cls, target): return 350

	@classmethod
	def do_cmd(cls): return 'timestop'

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

	def save_relative_vitals(self): return None
	def restore_relative_vitals(self, saved): pass

class Fighter(Living):
	hp    = property(lambda self: self.cur_hp)
	mhp   = property(lambda self: max(1, round(self.base_mhp * (1 + (self.str - 10) / 10))))
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
		if self.weapon: self.weapon.owner = self

	# сохранить соотношения HP/MP к максимумам, если какое-то действие потенциально изменит их лимит.
	relative_vitals = namedtuple('relative_vitals', 'hp, mp')
	def save_relative_vitals(self): return self.relative_vitals(self.hp / self.mhp, self.mp / self.mmp)
	def restore_relative_vitals(self, saved):
		self.cur_hp = clamp(round(self.mhp * saved.hp), 1, self.mhp)
		self.cur_mp = clamp(round(self.mmp * saved.mp), 1, self.mmp)

class Weapon(Living):
	ap_limit = property(lambda self: 1 + (self.xl - 1))
	LEVEL_CAP = 5

	def __init__(self):
		Living.__init__(self)
		self.name = "Баг"
		self.owner = None
		self.ammos = []

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
		self.last_input = ""

	def process(self):
		self.do_process()

	def render(self, cmds, emergency=None):
		self.do_render(cmds)
		if self.do_prompt: print('\n> ', end='')

	def do_process(self): pass
	def do_render(self, cmds): raise NotImplementedError("do_render")

	def handle_command(self, cmds): return self.do_handle_command(cmds)
	def do_handle_command(self, cmd): return False

	def switch_to(self, mode):
		self.session.switch_to(mode)

	def revert(self, n=1):
		check(self.session.mode == self, "session.mode != self")
		return self.session.revert(n)

	def more(self, msg, do_cls=False):
		more = MoreMessage(msg, do_cls)
		self.switch_to(more)
		return more

	do_prompt = True
	do_cls    = True
	term_width = property(lambda self: self.session.term_width)
	term_height = property(lambda self: self.session.term_height)
	prev_mode = False # запомнит предыдущий режим, т. о. к нему можно будет вернуться

class MainMenu(Mode):
	def do_render(self, cmds):
		ci = 1
		msg = \
			           "        VISIBLE FIGHTERS v.{0}       \n".format(".".join(str(part) for part in version)) + \
			         "({0})        - новая игра -        (new)".format(ci)
		cmds.add((str(ci), 'new'), lambda: self.start_new_game(), '?', lambda: self.more("Начать новую игру."))
		ci += 1

		if os.path.exists(Game.SAVE_BASE):
			msg += "\n({0})      - продолжить игру -    (load)".format(ci)
			cmds.add((str(ci), 'load'), lambda: self.switch_to(LoadGame()), '?', lambda: self.more("Продолжить сохранённую игру."))
			ci += 1

		msg += \
			       "\n({0})         - справка -         (help)\n".format(ci) + \
			           "(0)          - выход -          (quit)"
		cmds.add((str(ci), 'help'), lambda: self.more(MainMenu.Help, do_cls=True), '?', lambda: self.more("Вывести справку об основных моментах."))
		cmds.add(('0', 'quit'), lambda: self.session.post_quit(), '?', lambda: self.more("Выйти из приложения."))
		print(msg)

	def start_new_game(self):
		game = Game()
		game.gold = 300
		game.player = Fighter()
		game.player.name = "Рика"
		game.player.set_weapon(Weapon())
		game.player.weapon.name = "<gun of genocide>"
		game.player.receive_xp(160)
		StrUpgrade().apply(game.player, 1, 1)
		IntUpgrade().apply(game.player, 1, 1)
		DexUpgrade().apply(game.player, 1, 1)
		game.next_level = 1

		game.player.weapon.receive_xp(100)
		TimestopAmmunitionUpgrade().apply(game.player.weapon, 1, 1)
		IncendiaryAmmunitionUpgrade().apply(game.player.weapon, 1, 1)
		SilenceAmmunitionUpgrade().apply(game.player.weapon, 1, 1)
		IncendiaryAmmunitionUpgrade().apply(game.player.weapon, 1, 1)

		self.switch_to(AskName(game))

	Help = \
		"Ваш автомат — живой, и при использовании в бою ему будет перенаправлена часть опыта. Пули пробивают броню, но не масштабируются статами персонажа.\n"\
		"\n"\
		"Сила      (STR) — |влияет на силу ударов и максимум HP.\n"\
		"Интеллект (INT) — |на максимум маны, силу заклинаний и сопротивление магии.\n"\
		"Ловкость  (DEX) — |на точность ударов, шанс уворота и критических ударов.\n"\
		"Скорость  (SPD) — |на инициативу в бою. Например, если ваша скорость 150, а противника 100, "\
		                   "на три ваших действия будут приходиться два действия противника.\n"\
		"\n"\
		"Между боями вы можете тратить золото на апгрейды в пределах полученного опыта. Золото за даунгрейд компенсируется частично.\n"\
		"В игре 10 уровней. Сохранение в основной сейв выполняется автоматически, можно переключиться на новый файл скрытой командой backup.\n"\
		"\n"\
		"Можно сокращать команды до префиксов: heal hp -> h h, b.fire? -> b.f?.\n"\
		"                                                            ^       ^\n"\
		"                                                    |\"?\" выводит справку по команде или подписанному элементу экрана."

class LoadGame(Mode):
	def __init__(self):
		super().__init__()
		self.previews = Game.load_previews(include_bad = True)
		self.first    = 0
		self.had_previews = len(self.previews)
		self.step = None

		name2namesakes = dict()
		for pv in self.previews:
			namesakes = name2namesakes.get(pv.player_name, None)
			if not namesakes:
				namesakes = dict()
				name2namesakes[pv.player_name] = namesakes

			dup_index = namesakes.get(pv.character_uid, None)
			if not dup_index:
				dup_index = len(namesakes) + 1
				namesakes[pv.character_uid] = dup_index
			if dup_index > 1: pv.dup_suffix = dup_index

	def do_process(self):
		# пессимистическая оценка... можно смотреть по точному числу строк, но это будет сложнее
		# - 10 — число дополнительных строк на экране, помимо описаний
		# LINES + 1 — между описаниями пустая строка
		# - 1 — в подтверждениях описание сейва дублируется
		self.step = max(3, (self.term_height - 10) // (Game.Preview.LOAD_SCREEN_DESC_LINES + 1) - 1)
		if not self.previews:
			self.revert()
			self.session.mode.more("Нет сохранений.", do_cls=self.had_previews)

		if self.first >= self.step and self.first - self.step + self.num_to_show(self.first - self.step) >= self.first + self.num_to_show(self.first):
			self.first -= self.step

	def do_render(self, cmds):
		check(self.step, "step?!")
		show = self.num_to_show(self.first)
		end = self.first + show

		if self.first > 0:
			print("({0}) (up)".format(f"{max(1, 1 + self.first - self.step)}–{self.first}"))
			cmds.add('up', lambda: self.up(self.step), '?', lambda: self.more("Прокрутить список вверх."))

		desc_pad = len(str(end)) + 3 # (, число, ), пробел
		for index, pv in enumerate(self.previews[self.first : end], self.first):
			for _tryIndex in range(2): # перестраховка, скорее всего, не нужно, но пусть будет
				try:
					print(("\n" if index > self.first or self.first > 0 else "") + self.indexed_save_desc(index, desc_pad))
					break
				except:
					print(traceback.format_exc())
					self.previews[index].bad = True
			if pv.bad:
				cmds.add(str(1 + index), self.create_remove_request_handler(index, desc_pad), '?', lambda: self.more("Удалить это сохранение."))
			else:
				cmds.add(str(1 + index), self.create_load_request_handler(index, desc_pad), '?', lambda: self.more("Загрузить это сохранение."))

		remove_inscriptions = ['remove <номер>']
		cmds.add('remove', self.create_remove_by_number_handler(desc_pad),
			'?', lambda: self.more("Удалить сохранение{0}.".format(" (спросит номер)" if len(self.previews) > 1 else "")))

		if len(self.previews) > 1:
			cmds.add('remove all', self.create_batch_remove_handler(None, "Все"), '?', lambda: self.more("Удалить все сохранения."))
			remove_inscriptions.append('remove all')

		if any(pv.bad for pv in self.previews):
			remove_inscriptions.append('remove bad')
			cmds.add('remove bad', self.create_batch_remove_handler(lambda pv: pv.bad, "Повреждённые"), '?', lambda: self.more("Удалить повреждённые сохранения."))

		for index in range(self.first, end):
			cmds.add('remove ' + str(1 + index), self.create_remove_request_handler(index, desc_pad), '?', lambda: self.more("Удалить это сохранение."))

		if end < len(self.previews):
			print("\n({0}) (down)".format(f"{1 + end}–{1 + end + self.num_to_show(end) - 1}"))
			cmds.add('down', lambda: self.down(show), '?', lambda: self.more("Прокрутить список вниз."))

		print("\nУдалить сохранение ({0})".format(", ".join(remove_inscriptions)))
		print("Вернуться в главное меню (quit)")
		cmds.add('quit', lambda: self.switch_to(MainMenu()), '?', lambda: self.more("Вернуться в главное меню."))

	def do_handle_command(self, cmd):
		if cmd == "":
			if self.first + self.num_to_show(self.first) >= len(self.previews):
				self.first = 0
			else:
				self.down(self.num_to_show(self.first))
			return True

	def up(self, by):
		self.first = max(0, self.first - by)

	def down(self, by):
		self.first = max(0, min(len(self.previews) - 1, self.first + by))

	def num_to_show(self, first):
		return min(self.step, len(self.previews) - first)

	def indexed_save_desc(self, index, pad):
		cmd = "({0}) ".format(1 + index).ljust(pad)
		return cmd + self.previews[index].load_screen_desc(pad = pad)

	def remove_save(self, index, extra_reverts):
		try:
			Game.remove_save(self.previews[index].save_file_path)
			del self.previews[index]
			return True
		except Exception as e:
			self.more("Не удалось удалить сохранение.\n" + exception_msg(e)).reverts(1 + extra_reverts)

	def create_load_request_handler(self, index, desc_pad):
		pv = self.previews[index]
		def confirm_load(input, mode):
			if not input or input.lower() == 'y':
				try:
					with open(pv.save_file_path, 'rb') as f:
						game = Game.load(f, pv)
				except Exception as e:
					mode.more("Не удалось загрузить игру.\n" + (exception_msg(e) or repr(e))).reverts(2)
					return
				mode.more("Загрузка...").then(lambda mode: mode.switch_to(Respite(game)))
			else:
				mode.revert()

		def handler():
			self.switch_to(Prompt("\n{0}\n\nЗагрузить эту игру? (Y/n) ".format(self.indexed_save_desc(index, desc_pad)), confirm_load))
		return handler

	def create_remove_request_handler(self, index, desc_pad, extra_reverts=0):
		pv = self.previews[index]
		def confirm_remove(input, mode):
			if not input and pv.bad or input.lower() == 'y':
				if not self.remove_save(index, 1 + extra_reverts): return
				mode.more("Сохранение удалено.").reverts(2 + extra_reverts)
			else:
				mode.revert(1 + extra_reverts)

		def handler():
			self.switch_to(Prompt("\n{0}\n\nУдалить это сохранение? ({1}/{2}) ".format(
				self.indexed_save_desc(index, desc_pad),
				'Y' if pv.bad else 'y', 'n' if pv.bad else 'N'), confirm_remove))
		return handler

	def create_remove_by_number_handler(self, desc_pad):
		def remove_by_number():
			def handle_answer(input, mode):
				if not input:
					mode.revert()
					return

				try:
					id = int(input) - 1
					if id >= 0 and id < len(self.previews):
						self.create_remove_request_handler(id, desc_pad, extra_reverts=1)()
					else:
						raise ValueError("Неверный ввод.")
				except ValueError:
					mode.more("???").reverts(2)

			if len(self.previews) == 1:
				self.create_remove_request_handler(0, desc_pad)()
			else:
				self.switch_to(Prompt(f"Какое сохранение удалить? ({1 + self.first} – {1 + self.first + self.num_to_show(self.first) - 1}) ", handle_answer))
		return remove_by_number

	def create_batch_remove_handler(self, predicate, capitalized_saves_desc):
		def remove():
			count = sum(1 for pv in self.previews if not predicate or predicate(pv))
			def confirm(input, mode):
				if input.lower() == 'y':
					for index in reversed(range(len(self.previews))):
						if not self.remove_save(index, 1): return
					mode.more("{0} сохранения удалены.".format(capitalized_saves_desc)).reverts(2)
				else:
					mode.revert()
			self.switch_to(Prompt("Удалить {0}? (y/N) ".format(plural(count, "{N} сохранени{е/я/й}")), confirm))
		return remove
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
	def __init__(self, msg, callback):
		super().__init__(msg)
		self.callback = callback

	def do_handle_command(self, cmd):
		self.callback(cmd.strip(), self)
		return True
	input_comes = True

# Прогресс игрока и информация о сейве.
class Game:
	SAVE_BASE = os.path.join(os.path.dirname(__file__), 'save')
	SAVE_SUFFIX = ".sav"

	def __init__(self):
		# Для отслеживания сохранений с одинаковыми именами персонажей.
		self.character_uid  = None
		self.order_key      = None
		self.save_file_path = None
		self.save_file_base_name = None
		self.gold           = None
		self.player         = None
		self.next_level     = None

	def take_gold(self, amount):
		check(self.gold >= amount, "not enough gold")
		self.gold -= amount

	@staticmethod
	def corrupted_save_error(what=None):
		return Exception("Сохранение повреждено{0}.".format(f" ({what})" if what else ""))

	# Превью для быстрой загрузки. Сохранение состоит из Preview.to_dict() и Game.to_complement()
	class Preview:
		def __init__(self, game=None, order_key=None, bad=None):
			self.bad            = bad
			self.version        = version
			self.save_file_path  = None # выставляется в load_previews
			self.character_uid  = game and game.character_uid
			self.order_key      = order_key or game and game.order_key
			self.player_name    = game and game.player.name
			self.player_level   = game and game.player.xl
			self.player_next    = game and Respite.next_percentage(game.player)
			self.weapon_name    = game and game.player.weapon.name
			self.weapon_level   = game and game.player.weapon.xl
			self.weapon_next    = game and Respite.next_percentage(game.player.weapon)
			self.gold           = game and game.gold
			self.next_level     = game and game.next_level
			self.timestamp      = game and time.localtime()
			self.dup_suffix     = None # приписывать -2, -3, etc. для одинаковых имён разных персонажей

		store_fields = {
			'version': tuple,
			'character_uid': str, 'order_key': int,
			'player_name': str, 'player_level': int, 'player_next': (float, type(None)),
			'weapon_name': str, 'weapon_level': int, 'weapon_next': (float, type(None)),
			'gold': int, 'next_level': int, 'timestamp': time.struct_time }

		def to_dict(self):
			return { k: getattr(self, k) for k in Game.Preview.store_fields }

		@staticmethod
		def from_dict(d):
			pv = Game.Preview()
			if not isinstance(d, dict) or len(d) != len(Game.Preview.store_fields) or 'version' not in d:
				raise Game.corrupted_save_error()

			if d['version'] != version or d.keys() != Game.Preview.store_fields.keys():
				raise Exception("Несовместимая версия сохранения.")  # хотя можно и совместимость устроить... даже просто не проверять

			for field, field_type in Game.Preview.store_fields.items():
				value = d[field]
				if not isinstance(value, field_type): raise Game.corrupted_save_error(field + ": " + str(type(value)))
				setattr(pv, field, value)
			return pv

		LOAD_SCREEN_DESC_LINES = 4
		def load_screen_desc(self, pad=0):
			pad = ' ' * pad
			if self.bad:
				bad_msg = self.bad is not True and exception_msg(self.bad)
				if not bad_msg or bad_msg.index("оврежд") < 0:
					bad_msg = "Файл повреждён." + (("\n" + pad + bad_msg) if bad_msg else "")
				return "{0}\n{pad}[{1}]".format(bad_msg, self.save_file_path, pad = pad)
			else:
				player_next_desc = f" ({self.player_next:.0f}%)" if self.player_next is not None else ""
				weapon_next_desc = f" ({self.weapon_next:.0f}%)" if self.weapon_next is not None else ""
				dup_desc = f"-{self.dup_suffix}" if self.dup_suffix else ""
				return ("{ts}\n" +
					"{pad}{pn}{dd} Lv.{pl}{pnx}\n" +
					"{pad}{wn} Lv.{wl}{wnx}\n{pad}D:{coming} ${gold}").format(
					ts = time.asctime(self.timestamp),
					pn = self.player_name, dd = dup_desc, pl = self.player_level, pnx = player_next_desc,
					wn = self.weapon_name, wl = self.weapon_level, wnx = weapon_next_desc,
					coming = self.next_level, gold = self.gold,
					pad = pad)

	# Возвращает массив экземпляров Preview.
	@staticmethod
	def load_previews(include_bad=False):
		result = []
		try:
			dirpath, _dirnames, filenames = next(os.walk(Game.SAVE_BASE))
			for fn in filenames:
				full = os.path.join(dirpath, fn)
				try:
					with open(full, 'rb') as f: preview = Game.load_preview(f)
				except Exception as e:
					if not include_bad: continue
					preview = Game.Preview(bad=e)
				preview.save_file_path = full
				result.append(preview)
		except StopIteration:
			# Папки не существовало
			pass

		start = 0
		for i in range(1, len(result) + 1):
			if i == len(result) or result[i].bad != result[start].bad:
				if not result[start].bad: result[start:i] = sorted(result[start:i], key=lambda pv: pv.order_key, reverse=True)
				start = i
		return result

	@staticmethod
	def load_preview(file):
		preview = Game.Preview.from_dict(pickle.load(file))
		return preview

	@staticmethod
	def generate_order_key():
		k = -1
		for pv in Game.load_previews():
			k = max(k, pv.order_key)
		return k + 1

	# Придумать основу имени файла. НУЖНО ПОАККУРАТНЕЕ, если игрок назвался чем-то типа ..\
	def base_filename(self):
		check(self.character_uid, "character_uid?!", self.player, "player?!")
		def sanitize(name):
			return "".join(c if
				'0' <= c <= '9' or
				'a' <= c <= 'z' or 'A' <= c <= 'Z' or
				'а' <= c <= 'я' or 'А' <= c <= 'Я' or c == 'ё' or c == 'Ё'
				else '_'
				for c in name)
		return "{0} Lv.{1} ({2} Lv.{3}) D{4}".format(
			sanitize(self.player.name), self.player.xl, sanitize(self.player.weapon.name), self.player.weapon.xl, self.next_level)

	def open_new_file(self):
		file, path, base, num = None, None, self.base_filename(), None
		while True:
			try:
				path = os.path.join(self.SAVE_BASE, base + (f" ({num})" if num else "")) + Game.SAVE_SUFFIX
				file = open(path, 'x+b')
				break
			except FileExistsError:
				num = num + 1 if num else 2
			if num > 99: raise RuntimeError(f"Слишком много сохранений вида \"{base}\".")
		return file, path, base

	@staticmethod
	def remove_save(path):
		os.remove(path)
		try:
			os.rmdir(Game.SAVE_BASE)
		except OSError:
			pass

	# to_new_file=False — автосохранение, выставит self.save_file_*.
	def save(self, to_new_file=False):
		# убедиться в существовании папки с сохранениями
		try:
			os.mkdir(Game.SAVE_BASE)
		except FileExistsError:
			pass

		# Придумать character_uid, если его ещё нет.
		if not self.character_uid:
			self.character_uid = format(random.randrange(2**128), 'x')

		# Придумать order_key, если его ещё нет, или если нужно сохранить в новый файл.
		if not self.order_key or to_new_file:
			order_key = Game.generate_order_key()

			# Если его нет — он запоминается.
			if not self.order_key: self.order_key = order_key
		else:
			order_key = self.order_key

		# Записать сразу в новый файл, если:
		# — это явно требуется (to_new_file=True)
		# -или-
		# — это автосохранение (to_new_file=False), но базовое имя файла изменилось или не существовало
		if to_new_file or self.base_filename() != self.save_file_base_name:
			file, path, base = self.open_new_file()
			try:
				try:
					self.save_to(file, order_key)
				finally:
					file.close()

				# если это автосохранение, удалить старый файл.
				if not to_new_file:
					if self.save_file_path: Game.remove_save(self.save_file_path)

				# save_file_* и order_key на данный момент актуализируются всегда
				self.save_file_path = path
				self.save_file_base_name = base
				self.order_key = order_key
			except:
				Game.remove_save(path)
				raise
		else:
			# Базовое имя файла не изменилось (и существовало): записать файл во временный, затем атомарно заменить существующий.
			tmp_fd, tmp_path = tempfile.mkstemp(suffix = ".tmp", prefix = os.path.join(self.SAVE_BASE, self.base_filename()))
			# Не знаю, как с ними правильно работать, так что перестрахуюсь.
			try:
				with open(tmp_fd, 'wb') as file:
					tmp_fd = 'CLOSED'
					self.save_to(file, order_key)
				os.replace(tmp_path, self.save_file_path)
			except:
				if tmp_fd != 'CLOSED': os.close(tmp_fd)
				Game.remove_save(tmp_path)
				raise

	def save_nothrow(self, mode, then=None, note_success=False, to_new_file=False):
		try:
			self.save(to_new_file)
			if note_success:
				mode = mode.more("Игра сохранена.")
				if then: mode.then(lambda mode: then(True, mode))
			else:
				if then: then(True, mode)
			return True
		except Exception as e:
			mode = mode.more("Не удалось сохранить игру.\n" + exception_msg(e))
			if then: mode.then(lambda mode: then(False, mode))

	preview_complement_fields = { 'player': Fighter }
	def to_complement(self):
		return { k: getattr(self, k) for k in Game.preview_complement_fields }

	@staticmethod
	def from_preview_and_complement(preview, complement, save_file_path):
		if not isinstance(complement, dict): raise Game.corrupted_save_error('complement')
		if complement.keys() != Game.preview_complement_fields.keys(): raise Game.corrupted_save_error('complement')

		g = Game()
		g.character_uid = preview.character_uid
		g.order_key     = preview.order_key
		g.gold          = preview.gold
		g.next_level    = preview.next_level
		for k in Game.preview_complement_fields:
			setattr(g, k, complement[k])

		g.save_file_path = save_file_path
		g.save_file_base_name = g.base_filename()
		return g

	def save_to(self, file, order_key):
		preview = Game.Preview(self, order_key=order_key)
		pickle.dump(preview.to_dict(), file)
		complement = self.to_complement()
		pickle.dump(complement, file)

	@staticmethod
	def load(file, preview):
		true_preview = Game.load_preview(file)
		complement = pickle.load(file)
		return Game.from_preview_and_complement(true_preview, complement, preview.save_file_path)

# Экран между боями.
class Respite(Mode):
	def __init__(self, game):
		super().__init__()
		self.game = game

	@staticmethod
	def next_percentage(being):
		return math.floor(being.xp / being.xp_for_levelup(being.xl) * 1000) / 10 if being.xl < being.LEVEL_CAP else None

	def describe_living(self, being):
		next = Respite.next_percentage(being)
		desc = "{0.name}: уровень {0.xl}{1}, умения: {0.ap_used}/{0.ap_limit}".format(being, f" ({next:.0f}%)" if next is not None else "")
		return desc

	def describe_player(self, player, cmds):
		desc = self.describe_living(player)
		name_pad = " " * (min(len(player.name), len(player.weapon.name)) + 2)

		need_heal_hp = player.hp < player.mhp
		need_heal_mp = player.mp < player.mmp

		def dhp_func(d):
			def modify():
				if d <= 0:
					player.ouch(-d, "dhp")
				else:
					player.cur_hp = min(player.cur_hp + d, player.mhp)
			return modify
		cmds.add('hp+', dhp_func(+1))
		cmds.add('hp-', dhp_func(-1))

		def dmp_func(d):
			def modify():
				player.cur_mp = clamp(player.cur_mp + d, 0, player.mmp)
			return modify
		cmds.add('mp+', dmp_func(+1))
		cmds.add('mp-', dmp_func(-1))

		desc += "\n" +\
			name_pad + "HP: " + Con.vital_bar(player.hp, player.mhp) + f" {player.hp}/{player.mhp}"
		if need_heal_hp:
			cost = clamp(round((1 - player.hp / player.mhp) * 30 + 0.25 * (player.mhp - player.hp)), 1, 50)
			desc += " восстановить: ${0}".format(cost)
			if self.game.gold >= cost:
				desc += " (heal hp)"
				def heal_hp():
					self.game.take_gold(cost)
					player.cur_hp = player.mhp
				cmds.add('heal hp', heal_hp, '?', lambda: self.more("Полностью восстановить очки здоровья."))
			else:
				desc += " :("

		desc += "\n" +\
			name_pad + "MP: " + Con.vital_bar(player.mp, player.mmp) + f" {player.mp}/{player.mmp}"
		if need_heal_mp:
			cost = clamp(round((1 - player.mp / player.mmp) * 20 + 0.25 * (player.mmp - player.mp)), 1, 70)
			desc += " восстановить: ${0}".format(cost)
			if self.game.gold >= cost:
				desc += " (heal mp)"
				def heal_mp():
					self.game.take_gold(cost)
					player.cur_mp = player.mmp
				cmds.add('heal mp', heal_mp, '?', lambda: self.more("Полностью восстановить ману."))
			else:
				desc += " :("
		return desc

	def describe_weapon(self, weapon, cmds):
		desc = self.describe_living(weapon)
		name_pad = " " * (min(len(weapon.name), len(weapon.owner.name)) + 2)

		max_short_name_len    = 0
		max_bullet_bar_len    = 0
		max_recharge_cost_len = 0

		for pass_ in range(2):
			for ammo in weapon.ammos:
				if ammo.finite_charges:
					if pass_ == 0:
						max_short_name_len    = max(max_short_name_len, len(ammo.short_name()))
						max_bullet_bar_len    = max(max_bullet_bar_len, ammo.MAX_CHARGES)
						if ammo.needs_recharging():
							max_recharge_cost_len = max(max_recharge_cost_len, len(str(ammo.recharge_cost())))
					else:
						desc += "\n{pad}{bullet_name} {bullets}".format(
							pad = name_pad,
							bullet_name = ammo.short_name().ljust(max_short_name_len),
							bullets = Con.bullet_bar(ammo.charges, ammo.MAX_CHARGES).ljust(max_bullet_bar_len))

						cmd = ammo.cmd()
						if ammo.has_charges():
							def make_shoot_func(ammo):
								def shoot():
									ammo.draw_charge()
								return shoot
							cmds.add('shoot ' + cmd, make_shoot_func(ammo))

						if ammo.needs_recharging():
							pad_cost = " " * (max_recharge_cost_len - len(str(ammo.recharge_cost())))
							desc += " перезарядка: ${0}".format(ammo.recharge_cost()) + pad_cost
							if self.game.gold >= ammo.recharge_cost():
								def make_reload_func(ammo):
									def reload():
										self.game.take_gold(ammo.recharge_cost())
										ammo.recharge()
									return reload
								desc += f" (reload {cmd})"
								cmds.add('reload ' + cmd, make_reload_func(ammo))
							else:
								desc += " :("
		return desc

	def do_render(self, cmds):
		game   = self.game
		player = game.player
		print(f"Золото: ${game.gold} (shop)\n")
		cmds.add('shop', lambda: self.more("Магазин: TODO"), '?', lambda: self.more("Магазин, где вы можете приобрести или продать апгрейды."))

		print(self.describe_player(player, cmds))

		if player.weapon:
			print("\n" + self.describe_weapon(player.weapon, cmds))

		print("\nследующий уровень (next)"
			  "\nвыйти             (quit)")
		cmds.add('next', lambda: self.more("Переход к следующему уровню — TODO"), '?', lambda: self.more("Переход к следующему уровню."))
		cmds.add('quit', lambda: self.quit(), '?', lambda: self.more("Выход в меню, можно одновременно удалить сохранение."))

	def do_handle_command(self, cmd):
		if cmd.strip() == 'backup':
			self.backup()
			return True

	def backup(self):
		self.game.save_nothrow(self, to_new_file=True, note_success=True)

	def quit(self):
		default_yes = self.last_input == 'quit'
		def handle_confirmation(input, mode):
			if input.lower() == 'y' or not input and default_yes:
				self.game.save_nothrow(mode, then=lambda success, mode: mode.switch_to(MainMenu()))
			elif input and 'suicide'.startswith(input.lower()):
				if self.game.save_file_path:
					try:
						Game.remove_save(self.game.save_file_path)
						mode.switch_to(MainMenu())
					except Exception as e:
						mode.more("Не удалось удалить сохранение.\n" + exception_msg(e)).then(lambda mode: mode.switch_to(MainMenu()))
			else:
				mode.revert()

		msg = "Выйти из игры? ({0}/{1}, suicide — не оставлять сохранение) ".format('Y' if default_yes else 'y', 'n' if default_yes else 'N')
		self.switch_to(Prompt(msg, handle_confirmation))

class AskName(Prompt):
	def __init__(self, game=None, who=None, cr=True):
		if not game: game = Game()
		if not who: who = game.player

		prompt = (
			"Вам нужно зарегистрироваться, прежде чем вас официально освободят.\nКак вас зовут? " if who == game.player else
			"{0}Назовите свой автомат, {1}: ".format("\n" if cr else "", game.player.name) if who == game.player.weapon else
			internalerror(who, "who"))
		super().__init__(prompt, self.handle_name_input)
		self.game = game
		self.who = who
		self.cr_next = True

	def handle_name_input(self, input, mode):
		MIN, MAX = 3, 20
		if not input or MIN <= len(input) <= MAX:
			if input:
				name = input[0].capitalize() + input[1:]
				if input == name:
					self.cr_next = False
					return self.complete(name)
			else:
				name = self.who.name

			mode.switch_to(Prompt(
				"{0} {1} (Y/n/q) ".format(
					(f"Очень приятно, {name}." if input else f"Ваше имя — {name}.") if self.who == self.game.player else
					(f"В ваших руках {name}." if input else f"Имя вашего автомата — {name}.") if self.who == self.game.player.weapon else
					internalerror(self.who, "who"),
					"Всё верно?" if input else "Продолжить?"),
				lambda input, mode: self.handle_name_confirmation(input, mode, name)))
		else:
			mode.more("{0}. Длина имени должна быть от {1} до {2}.".format(
				plural(len(input), "Введ{ён/ено/ено} {N} символ{/а/ов}"), MIN, plural(MAX, "{N} символ{/а/ов}")))

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
			self.session.switch_to(AskName(self.game, self.game.player.weapon, self.cr_next))
		elif self.who == self.game.player.weapon:
			self.game.player.weapon.name = name
			self.game.save_nothrow(self, then=lambda success, mode: mode.switch_to(Respite(self.game)))
		else:
			internalerror(self.who, "who")

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

	def revert(self, n=1):
		check(n > 0, "n?!")
		mode = self.mode
		while n > 0:
			mode = check(mode.prev_mode, isinstance(mode.prev_mode, Mode), "prev_mode?!")
			n -= 1
			self.switch_to(mode, reverting=True)
		self.cls_once()
		return mode

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

		self.mode.render(cmds)
		has_default_commands = cmds.root.childs
		if has_default_commands: self.add_default_commands(cmds)
		try:
			cmd = input()
			self.mode.last_input = cmd
		except (KeyboardInterrupt, EOFError) as e:
			self.post_quit()
			if isinstance(e, KeyboardInterrupt): print()
			return

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
		list = (node.down_to_unambiguous().backtrack() for node in cmds.root.childs.values())
		av = ", ".join(cmd for cmd in list if cmd != "?")
		return "Доступные команды: " + av + "." if av else "Нет доступных команд."

	def cls_once(self):
		self.cls_once_requested = True

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

def selftest():
	tests, fails = [], []
	account = False
	def run(name, cases, one):
		count = 0
		for case in cases:
			try:
				one(*case)
			except Exception as e:
				fails.append("Тест {0} #{1} {2}. {3}".format(name, count,
					"провален" if isinstance(e, Test.Failed) else "упал",
					''.join(e.args) if isinstance(e, Test.Failed) else traceback.format_exc()))
			count += 1
		if account: tests.append(name + f" x{count}" if count > 1 else "")

	if account:
		ticks = time.clock()
	for name, value in globals().items():
		if isinstance(value, type) and issubclass(value, Test) and value is not Test:
			test = value()
			test.setup()
			run(name[:-len("Test")] if name.endswith("Test") and len(name) > len("Test") else name, test.cases, test.one)
			test.teardown()
	if account:
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