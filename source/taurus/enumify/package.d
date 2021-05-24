module taurus.enumify;

import localimport;

/**
Defines a new member. `Args` follows the construction format of `Tuple`.

Params:
	name = member name
	Args = types and names(optional)

Examples:
---
enum Foo { A, B }
@Member!("A")
@Member!("B", int, "name")
@Member!("C", byte, long)
@Member!("D", float, char, "name")
@Member!("E", Foo, "nameA", Tuple!(uint, uint), "nameB")
---
*/
struct Member(Args ...)
	if (Args.length > 0
		&& from.std.traits.isSomeString!(typeof(Args[0]))
		&& __traits(compiles, { static if (Args.length > 1) from.std.typecons.Tuple!(Args[1 .. $]) t; })
	)
{}

@safe pure nothrow @nogc unittest {
	assert(!__traits(compiles, Member!()));
	assert(!__traits(compiles, Member!(int)));
	assert(!__traits(compiles, Member!("name", "foo")));
	assert(!__traits(compiles, Member!("name", int, "foo", "bar")));
	assert(!__traits(compiles, Member!("name", int, "foo", short, "foo")));

	assert( __traits(compiles, Member!("A")));
	assert( __traits(compiles, Member!("B", int, "name")));
	assert( __traits(compiles, Member!("C", byte, long)));
	assert( __traits(compiles, Member!("D", float, char, "name")));
	assert( __traits(compiles, Member!("E", int, "nameA", from.std.typecons.Tuple!(uint, uint), "nameB")));
}

/**
Generate an enum like struct of dynamic values.

Each Member will generate:
 * a *static* method used to instatiate
 * a *struct* to store the data
 * a *private ctor*

Examples:
---
import sumtype;

struct Message {
	@Member!("Move", int, "x", int, "y")
	@Member!("Echo", string)
	@Member!("ChangeColor", uint, uint, uint)
	@Member!("Quit")
	mixin enumify;
}

with (Message) {
Message m = Echo("");
assert(m.match!(
	(echo _) => true,
	_ => false
));

m = ChangeColor(3, 255, 123);
assert(
	m.match!(
		(changecolor c) => c.handle,
		_ => changecolor.handle.init
	) == from.std.typecons.tuple(3, 255, 123)
);
}
---

GenMethods:
```d
static Move(int, int) { ... }
static Echo(string) { ... }
static ChangeColor(uint, uint, uint) { ... }
static Quit() { ... }
```

GenStructs:
 ```d
move { Tuple!(int, "x", int, "y") handle; ... }
echo { string handle; ... }
changecolor { Tuple!(uint, uint, uint) handle; ... }
quit { ... }
```

SumType:
```d
immutable SumType!(move, echo, changecolor, quit) handle;
```

AliasThis: all variables `handle` have `alias this`
```d
alias handle this;
```
*/
mixin template enumify(from.std.typecons.Flag!"defautToString" defautToString = from.std.typecons.Flag!"defautToString".yes)
{
	// takes all attributes used before the mixin call
	private struct _udahelper() {}

	import std.format : format;
	import std.meta : AliasSeq, Filter, staticMap;
	import std.traits : isType, getUDAs, TemplateArgsOf;
	import std.typecons : Tuple, tuple;
	import std.string : toLower;

	import sumtype;

	// Member attribute iteration
	static foreach (attr; getUDAs!(_udahelper, Member))
	{
		static if (TemplateArgsOf!attr.length == 1)
		{
			/*
			Member with name only
			@Member!("None")
			---
			public struct none {
				string toString()() {
					return "None";
				}
			}

			private this(none payload) {
				handle = payload;
			}

			public static None()() {
				return typeof(this)(none());
			}
			---
			*/

			// create struct
			mixin(`public struct `, TemplateArgsOf!attr[0].toLower, ` {
				string toString()() { return "`, TemplateArgsOf!attr[0], `"; }
			}`);

			// create ctor
			mixin(`private this()(`, TemplateArgsOf!attr[0].toLower,` payload) {
				handle = payload;
			}`);

			// create static method
			mixin(`public static `, TemplateArgsOf!attr[0], `()() {
				return typeof(this)(`, TemplateArgsOf!attr[0].toLower,`());
			}`);
		}
		else static if (TemplateArgsOf!attr.length == 2)
		{
			/*
			Member one type
			@Member!("Some", string)
			---
			public struct some {
				string handle;
				alias handle this;

				version (D_BetterC) {} else
				string toString()() {
					return handle.format!"Some(%s)";
				}
			}

			private this(some payload) {
				handle = payload;
			}

			public static Some()(string seq) {
				return typeof(this)(some(seq));
			}
			---
			*/

			// create struct
			mixin(`public struct `, TemplateArgsOf!attr[0].toLower, ` {
				`, TemplateArgsOf!attr[1].stringof, ` handle;
				alias handle this;

				version (D_BetterC) {} else
				string toString()() {
					return handle.format!"`, TemplateArgsOf!attr[0], `(%s)";
				}
			}`);

			// create ctor
			mixin(`private this()(`, TemplateArgsOf!attr[0].toLower, ` payload) {
				handle = payload;
			}`);

			// create static method
			mixin(`public static `, TemplateArgsOf!attr[0], `()(`, TemplateArgsOf!attr[1].stringof, ` seq) {
				return typeof(this)(`, TemplateArgsOf!attr[0].toLower, `(seq));
			}`);
		}
		else
		{
			/*
			Member with either types only or types with names
			@Member!("Some", int, "val")
			---
			public struct some {
				Tuple!(int, "val") handle;
				alias handle this;

				version (D_BetterC) {} else
				string toString()() {
					return handle.format!"Some(%s)";
				}
			}

			private this(some payload) {
				handle = payload;
			}

			public static Some()(AliasSeq!int seq) {
				return typeof(this)(some(seq));
			}
			---
			*/

			// create struct
			mixin(`public struct `, TemplateArgsOf!attr[0].toLower, ` {
				`, Tuple!(TemplateArgsOf!attr[1 .. $]).stringof, ` handle;
				alias handle this;

				version (D_BetterC) {} else
				string toString()() {
					import std.range : iota;
					return format!"`, TemplateArgsOf!attr[0], `(%-(%s, %))"(mixin(
						format!"[%(handle[%s].format!\"%%s\"%|, %)]"(handle.length.iota)
					));
				}
			}`);

			// create ctor
			mixin(`private this()(`, TemplateArgsOf!attr[0].toLower, ` payload) {
				handle = payload;
			}`);

			// create static method
			mixin(`public static `, TemplateArgsOf!attr[0], `()(AliasSeq!`, Filter!(isType, TemplateArgsOf!attr[1 .. $]).stringof, ` seq) {
				return typeof(this)(`, TemplateArgsOf!attr[0].toLower, `(`, Tuple!(TemplateArgsOf!attr[1 .. $]).stringof,`(seq)));
			}`);
		}
	}

	/**
	Converts the first element of T to lower and adds a comma
	---
	assert(__front!(Member!"Thing") == tuple(['t', 'h', 'i', 'n', 'g'], ","));
	---
	*/
	private enum __front(T) = AliasSeq!(TemplateArgsOf!T[0].toLower, ",");
	static assert(__front!(Member!"Thing") == tuple(['t', 'h', 'i', 'n', 'g'], ","));

	/*
	generate SumType
	@Member!("Thing")
	@Member!("Ding")
	---
	private SumType!(thing, ding) handle;
	---
	*/
	mixin(`public immutable SumType!(`, staticMap!(__front, getUDAs!(_udahelper, Member)), `) handle;`);
	alias handle this;

	// create opAssign
	public void opAssign(E : typeof(this))(auto ref E rhs) {
		import std.traits : Unqual;
		(() @trusted pure nothrow @nogc => (cast(Unqual!(typeof(handle))) handle) = rhs.handle)();
	}

	// create toString
	version (D_BetterC) {} else
	static if (defautToString)
	public string toString() inout {
		import std.traits : Unqual;
		return (cast(Unqual!(typeof(handle))) handle).format!"%s";
	}
}

/// Every type of member
@safe pure nothrow @nogc unittest {
	import sumtype;

	static struct Foo {
		@Member!("Thing")
		@Member!("Ding", char)
		@Member!("Ming", int, "val")
		mixin enumify;
	}

	Foo foo = Foo.Ming(4);

	assert(foo.match!(
		(Foo.ming) => true,
		_ => false,
	));

	assert(Foo.init == Foo.Thing());

	assert(Foo.init.match!(
		(Foo.thing) => true,
		_ => false,
	));

	debug assert(from.std.conv.to!string(foo) == "Ming(4)");
	debug assert(from.std.format!"%s"(foo) == "Ming(4)");
}

/// A known type
@safe pure nothrow @nogc unittest {
	import sumtype;

	static struct Option(T) {
		@Member!("None")
		@Member!("Some", T)
		mixin enumify;
	}

	Option!int o;
	assert(o == Option!int.None);

	o = Option!int.Some(2);
	assert(o == Option!int.Some(2));
	assert(is(typeof(o.handle) == immutable SumType!(Option!int.none, Option!int.some)));

	// FIXME: https://issues.dlang.org/show_bug.cgi?id=21975
	assert(o.handle.match!(
		(Option!int.some s) => s > 0,
		_ => false
	));

	assert(!__traits(compiles, { o = Option!int.some(4); }));
}

/// Rustlings example
@safe pure nothrow @nogc unittest {
	import sumtype;

	static struct Message {
		@Member!("Move", int, "x", int, "y")
		@Member!("Echo", string)
		@Member!("ChangeColor", uint, uint, uint)
		@Member!("Quit")
		mixin enumify;

		bool isMove() {
			return handle.match!(
				(move _) => true,
				_ => false
			);
		}
	}

	with (Message) {
	assert(Move(4, 5).isMove());

	Message m = Echo("");
	assert(m.match!(
		(echo _) => true,
		_ => false
	));

	m = ChangeColor(3, 255, 123);
	assert(
		m.match!(
			(changecolor c) => c.handle,
			_ => changecolor.handle.init
		) == from.std.typecons.tuple(3, 255, 123));
	}
}
