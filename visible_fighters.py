import string, pickle
from collections import namedtuple, OrderedDict
version = (0, 1)

def internalerror(desc):
	raise Exception("Внутренняя ошибка: {0}.".format(desc))

# sanitycheck(условие 1, internalerror при невыполнении условия 1, ...)
def sanitycheck(*args):
	for i in range(len(args) // 2):
		if not args[2*i]: internalerror(args[2*i + 1])

# возвращает what, если всё хорошо (cond), иначе возбуждает internalerror
# например: hp = check(new_hp, new_hp > 0, "недопустимое значение hp")
def check(what, cond, errmsg):
	if cond: return what
	try:
		s = " ({0})".format(what)
	except:
		s = ""
	internalerror(errmsg + s)

# форматирует множественное число по правилам языка
# plural(3, "{N} слон{/а/ов}") → "3 слона"
def plural(n, fmt):
	form = ( # № формы в {один/два/много}
		2 if n % 10 == 0 or n % 10 >= 4 or n // 10 % 10 == 1 else # 7 слон_ов — форма 2
		0 if n % 10 == 1 else # 1 слон_ — форма 0
		1) # 3 слон_а — форма 1

	# преобразование фрагмента внутри {}: {N} либо {a/b/c}
	def handle(piece): return "" if not piece else str(n) if piece == 'N' else piece.split('/', 2)[form]

	# None вместо self вроде работает, не хочу объект создавать
	return "".join(literal + handle(bracketed) for literal, bracketed, _, _ in string.Formatter.parse(None, fmt))

def clamp(n, a, b):
	return n if (n >= a) and (n <= b) else b if n > b else a

# список команд, позволяющий сокращать их при отсутствии неоднозначностей
# guess возвращает (1) ассоциированную с командой функцию и (2) список вариантов (то и другое можно использовать только после проверки на истинность)
# например:
# .add("hit", funcA)
# .add("hook", funcB)
# .guess("h") → None, ["hit", "hook"]
# .guess("ho") → funcB, None
class Commands:
	def __init__(self):
		self.cmds = OrderedDict()

	def add(self, cmd, func):
		if isinstance(cmd, str):
			self._add_one(cmd, func)
		else:
			for one in cmd:
				self._add_one(one, func)

	def _add_one(self, cmd, func):
		if cmd in self.cmds: raise Exception("Команда {0} уже определена.".format(cmd))
		self.cmds[cmd] = func

	def guess(self, input):
		precise = self.cmds.get(input, None) # приоритет у точных совпадений
		if precise: return precise, None
		matching = [(cmd, func) for cmd, func in self.cmds.items() if cmd.startswith(input)]
		if len(matching) >= 1 and all(func == matching[0][1] for _cmd, func in matching[1:]): return matching[0][1], None
		return None, [cmd for cmd, _func in matching]

# Эффект, наложенный на персонажа.
class HexBase:
	ran_out = property(lambda self: self.turns <= 0)

	def __init__(self, master, victim, power, turns):
		self.master = check(master, isinstance(master, Fighter), "master?!")
		self.victim = check(victim, isinstance(victim, Fighter), "victim?!")
		self.power = check(power, power > 0, "power?!")
		self.turns = check(turns, turns > 0, "turns?!")
		master.caused_hexes.add(self)
		victim.hexes.add(self)

	def tick(self):
		sanitycheck(self in self.victim.hexes, "self not in victim.hexes", self in self.master.caused_hexes, "self not in master.caused_hexes",
			not self.ran_out, "хекс истёк")
		self.do_tick()
		if self.ran_out: return

		self.turns -= 1
		if self.ran_out: self.do_finish()

	def cancel(self):
		if self.ran_out: return
		self.turns = 0
		self.do_cancel(self)

	def do_start(self): pass
	def do_tick(self): pass
	def do_finish(self): pass
	def do_cancel(self): pass

	def short(self):
		desc = self.do_name()
		pow_desc = self.do_describe_power()
		if pow_desc: desc += ", " + pow_desc
		desc += ": " + plural(self.turns, "{N} ход{/а/ов}")
		return desc

	def do_name(self): internalerror("do_name?!")
	def do_describe_power(self): internalerror("do_describe_power?!")

	def detail(self): return self.do_detail()
	def do_detail(self): internalerror("do_detail?!")

	def cmd(self): return self.do_cmd()
	def do_cmd(self): internalerror("do_cmd?!")

	BASELINE_POWER = 100
	dispellable = False

class RageHex(HexBase):
	#  мин. 1.2x @ pow → 0
	#       1.5x @ BASELINE_POWER
	# макс. 5.0x @ pow = 1267
	physdam_x = property(lambda self: clamp(1.2 + 0.3 * (self.power / HexBase.BASELINE_POWER), 1.2, 5.0))

	#  мин. 1.1x @ pow → 0
	#       1.2x @ BASELINE_POWER
	# макс. 2.2x @ pow = 1100
	backlash_x = property(lambda self: clamp(1.1 + 0.1 * (self.power / HexBase.BASELINE_POWER), 1.1, 2.2))

	def do_name(self): return "Ярость"
	def do_describe_power(self):
		m = round(self.physdam_x, 1)
		return None if m == 1.5 else "{0}x".format(m)

	def do_detail(self): return \
		"Увеличивает физическую атаку (x{0}) и любой получаемый урон (x{1}).\n"\
		"Нельзя развеять.".format(round(self.physdam_x, 1), round(self.backlash_x, 1))

	def do_cmd(self): return "rage"

class DeathWordHex(HexBase):
	def do_finish(self):
		sanitycheck(self.master.alive, "Смертный приговор пережил автора")
		if self.victim.alive: self.victim.ouch(self.victim.hp, "в исполнение Смертного приговора")

	def do_name(self): return "Смертный приговор"
	def do_describe_power(self): return None

	def do_detail(self): return \
		"Гарантированная смерть через {turns}.\n"\
		"Вы можете снять этот хекс с помощью Развеивания либо убив мага, наложившего заклинание.".format(turns = plural(self.turns, "{N} ход{/а/ов}"))

	def do_cmd(self): return "deathword"
	dispellable = True

class Fighter:
	hp   = property(lambda self: self.cur_hp)
	mhp  = property(lambda self: self.base_mhp)
	dead = property(lambda self: not not self.death_cause)
	alive = property(lambda self: not self.dead)
	mp   = property(lambda self: self.cur_mp)
	mmp  = property(lambda self: self.base_mmp)

	def __init__(self):
		self.base_mhp = self.cur_hp = 1
		self.death_cause = None

		self.base_mmp = self.cur_mp = 1
		self.hexes = set()
		self.caused_hexes = set()

	def ouch(self, hp_dam, death_cause):
		sanitycheck(hp_dam >= 0, "hp_dam?!", death_cause, "death_cause?!")

		if not self.dead:
			self.cur_hp -= hp_dam
			if self.cur_hp <= 0: self.die(death_cause)
			
	def die(self, cause):
		sanitycheck(not self.dead, "not dead", cause, "cause?!")
		for hex in self.caused_hexes:
			if isinstance(hex, DeathWordHex):
				hex.cancel()
		self.death_cause = cause

	def end_turn(self):
		ran_out = []
		for hex in self.hexes:
			sanitycheck(hex.victim == self, "hex.victim != self")
			hex.tick()
			if hex.ran_out: ran_out.append(hex)

		for hex in ran_out:
			self.hexes.remove(hex)
			hex.master.caused_hexes.remove(hex)

class State:
	def __init__(self):
		self.session = None

	def render(self, cmds): internalerror("render?!")
	def handle_command(self, cmd): return False

class MainMenu(State):
	def render(self, cmds):
		print(
			"=== VISIBLE FIGHTERS v.{0} ===\n"\
			"(1)     - новая игра -\n"\
			"(2)   - загрузить игру -\n"\
			"(3)      - справка -\n"\
			"(0)       - выход -".format(".".join(str(part) for part in version)))

		cmds.add(('1', 'newgame'), lambda: self.session.switch_to(MainMenu()))
		cmds.add(('2', 'load'), lambda: self.session.switch_to(MainMenu()))
		cmds.add(('3', 'help'), lambda: self.session.switch_to(MainMenu()))
		cmds.add(('0', 'quit'), lambda: self.session.post_quit())

class HelpScreen(State):
	def render(self, cmds):
		print(
			"Ваш автомат — живой, и при использовании в бою ему будет перенаправлена часть опыта. Пули пробивают броню, но не масштабируются статами персонажа.\n"\
			"Сила      (STR) — влияет на силу ударов и максимум HP.\n"\
			"Интеллект (INT) — на максимум маны, силу заклинаний и сопротивление магии.\n"\
			"Ловкость  (DEX) — на точность ударов, шанс уворота и критических ударов.\n"\
			"Скорость  (SPD) — на инициативу в бою. Например, если ваша скорость 150, а противника 100, на три ваших действия будут приходиться два действия противника.\n"\
			"Между боями вы можете тратить золото на апгрейды в пределах полученного опыта. Золото за даунгрейд компенсируется частично.\n"\
			"В игре 10 уровней.\n"\
			"<ENTER>")

	def handle_command(self, cmd):
		self.session.switch_to(MainMenu())
		return True

class Session:
	def __init__(self):
		self.quit_posted = False
		self.switch_to(MainMenu())

	def switch_to(self, new_mode):
		self.mode = new_mode
		self.mode.session = self

	def process(self):
		cmds = Commands()
		self.mode.render(cmds)
		print()
		cmd = input()

		fn, matches = cmds.guess(cmd)
		if fn: fn()
		elif matches: print("Неоднозначная команда: {0}.".format(", ".join(matches)))
		elif not self.mode.handle_command(input): print("Неизвестная команда.")
		print()

		return self.mode if not self.quit_posted else None

	def post_quit(self):
		self.quit_posted = True

def main():
	session = Session()
	while session.process(): pass

if __name__ == "__main__": main()