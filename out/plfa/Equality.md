---
src       : src/plfa/Equality.lagda
title     : "Equality: Equality and equational reasoning"
layout    : page
prev      : /Relations/
permalink : /Equality/
next      : /Isomorphism/
---

<pre class="Agda">{% raw %}<a id="171" class="Keyword">module</a> <a id="178" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}" class="Module">plfa.Equality</a> <a id="192" class="Keyword">where</a>{% endraw %}</pre>

Much of our reasoning has involved equality.  Given two terms `M`
and `N`, both of type `A`, we write `M ≡ N` to assert that `M` and `N`
are interchangeable.  So far we have treated equality as a primitive,
here we show how to define it as an inductive datatype.


## Imports

This chapter has no imports.  Every chapter in this book, and nearly
every module in the Agda standard library, imports equality.
Since we define equality here, any import would create a conflict.


## Equality

We declare equality as follows:
<pre class="Agda">{% raw %}<a id="744" class="Keyword">data</a> <a id="_≡_"></a><a id="749" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">_≡_</a> <a id="753" class="Symbol">{</a><a id="754" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#754" class="Bound">A</a> <a id="756" class="Symbol">:</a> <a id="758" class="PrimitiveType">Set</a><a id="761" class="Symbol">}</a> <a id="763" class="Symbol">(</a><a id="764" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#764" class="Bound">x</a> <a id="766" class="Symbol">:</a> <a id="768" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#754" class="Bound">A</a><a id="769" class="Symbol">)</a> <a id="771" class="Symbol">:</a> <a id="773" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#754" class="Bound">A</a> <a id="775" class="Symbol">→</a> <a id="777" class="PrimitiveType">Set</a> <a id="781" class="Keyword">where</a>
  <a id="_≡_.refl"></a><a id="789" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#789" class="InductiveConstructor">refl</a> <a id="794" class="Symbol">:</a> <a id="796" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#764" class="Bound">x</a> <a id="798" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="800" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#764" class="Bound">x</a>{% endraw %}</pre>
In other words, for any type `A` and for any `x` of type `A`, the
constructor `refl` provides evidence that `x ≡ x`. Hence, every value
is equal to itself, and we have no other way of showing values
equal.  The definition features an asymmetry, in that the
first argument to `_≡_` is given by the parameter `x : A`, while the
second is given by an index in `A → Set`.  This follows our policy
of using parameters wherever possible.  The first argument to `_≡_`
can be a parameter because it doesn't vary, while the second must be
an index, so it can be required to be equal to the first.

We declare the precedence of equality as follows:
<pre class="Agda">{% raw %}<a id="1465" class="Keyword">infix</a> <a id="1471" class="Number">4</a> <a id="1473" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">_≡_</a>{% endraw %}</pre>
We set the precedence of `_≡_` at level 4, the same as `_≤_`,
which means it binds less tightly than any arithmetic operator.
It associates neither to left nor right; writing `x ≡ y ≡ z`
is illegal.


## Equality is an equivalence relation

An equivalence relation is one which is reflexive, symmetric, and transitive.
Reflexivity is built-in to the definition of equality, via the
constructor `refl`.  It is straightforward to show symmetry:
<pre class="Agda">{% raw %}<a id="sym"></a><a id="1944" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1944" class="Function">sym</a> <a id="1948" class="Symbol">:</a> <a id="1950" class="Symbol">∀</a> <a id="1952" class="Symbol">{</a><a id="1953" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1953" class="Bound">A</a> <a id="1955" class="Symbol">:</a> <a id="1957" class="PrimitiveType">Set</a><a id="1960" class="Symbol">}</a> <a id="1962" class="Symbol">{</a><a id="1963" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1963" class="Bound">x</a> <a id="1965" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1965" class="Bound">y</a> <a id="1967" class="Symbol">:</a> <a id="1969" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1953" class="Bound">A</a><a id="1970" class="Symbol">}</a>
  <a id="1974" class="Symbol">→</a> <a id="1976" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1963" class="Bound">x</a> <a id="1978" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="1980" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1965" class="Bound">y</a>
    <a id="1986" class="Comment">-----</a>
  <a id="1994" class="Symbol">→</a> <a id="1996" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1965" class="Bound">y</a> <a id="1998" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="2000" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1963" class="Bound">x</a>
<a id="2002" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1944" class="Function">sym</a> <a id="2006" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#789" class="InductiveConstructor">refl</a> <a id="2011" class="Symbol">=</a> <a id="2013" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#789" class="InductiveConstructor">refl</a>{% endraw %}</pre>
How does this proof work? The argument to `sym` has type `x ≡ y`, but
on the left-hand side of the equation the argument has been
instantiated to the pattern `refl`, which requires that `x` and `y`
are the same.  Hence, for the right-hand side of the equation we need
a term of type `x ≡ x`, and `refl` will do.

It is instructive to develop `sym` interactively.  To start, we supply
a variable for the argument on the left, and a hole for the body on
the right:

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
    sym e = {! !}

If we go into the hole and type `C-c C-,` then Agda reports:

    Goal: .y ≡ .x
    ————————————————————————————————————————————————————————————
    e  : .x ≡ .y
    .y : .A
    .x : .A
    .A : Set

If in the hole we type `C-c C-c e` then Agda will instantiate `e` to
all possible constructors, with one equation for each. There is only
one possible constructor:

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
    sym refl = {! !}

If we go into the hole again and type `C-c C-,` then Agda now reports:

     Goal: .x ≡ .x
     ————————————————————————————————————————————————————————————
     .x : .A
     .A : Set

This is the key step---Agda has worked out that `x` and `y` must be
the same to match the pattern `refl`!

Finally, if we go back into the hole and type `C-c C-r` it will
instantiate the hole with the one constructor that yields a value of
the expected type:

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
    sym refl = refl

This completes the definition as given above.

Transitivity is equally straightforward:
<pre class="Agda">{% raw %}<a id="trans"></a><a id="3688" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3688" class="Function">trans</a> <a id="3694" class="Symbol">:</a> <a id="3696" class="Symbol">∀</a> <a id="3698" class="Symbol">{</a><a id="3699" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3699" class="Bound">A</a> <a id="3701" class="Symbol">:</a> <a id="3703" class="PrimitiveType">Set</a><a id="3706" class="Symbol">}</a> <a id="3708" class="Symbol">{</a><a id="3709" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3709" class="Bound">x</a> <a id="3711" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3711" class="Bound">y</a> <a id="3713" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3713" class="Bound">z</a> <a id="3715" class="Symbol">:</a> <a id="3717" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3699" class="Bound">A</a><a id="3718" class="Symbol">}</a>
  <a id="3722" class="Symbol">→</a> <a id="3724" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3709" class="Bound">x</a> <a id="3726" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="3728" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3711" class="Bound">y</a>
  <a id="3732" class="Symbol">→</a> <a id="3734" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3711" class="Bound">y</a> <a id="3736" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="3738" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3713" class="Bound">z</a>
    <a id="3744" class="Comment">-----</a>
  <a id="3752" class="Symbol">→</a> <a id="3754" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3709" class="Bound">x</a> <a id="3756" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="3758" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3713" class="Bound">z</a>
<a id="3760" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3688" class="Function">trans</a> <a id="3766" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#789" class="InductiveConstructor">refl</a> <a id="3771" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#789" class="InductiveConstructor">refl</a>  <a id="3777" class="Symbol">=</a>  <a id="3780" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#789" class="InductiveConstructor">refl</a>{% endraw %}</pre>
Again, a useful exercise is to carry out an interactive development,
checking how Agda's knowledge changes as each of the two arguments is
instantiated.

## Congruence and substitution {#cong}

Equality satisfies _congruence_.  If two terms are equal,
they remain so after the same function is applied to both:
<pre class="Agda">{% raw %}<a id="cong"></a><a id="4120" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4120" class="Function">cong</a> <a id="4125" class="Symbol">:</a> <a id="4127" class="Symbol">∀</a> <a id="4129" class="Symbol">{</a><a id="4130" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4130" class="Bound">A</a> <a id="4132" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4132" class="Bound">B</a> <a id="4134" class="Symbol">:</a> <a id="4136" class="PrimitiveType">Set</a><a id="4139" class="Symbol">}</a> <a id="4141" class="Symbol">(</a><a id="4142" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4142" class="Bound">f</a> <a id="4144" class="Symbol">:</a> <a id="4146" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4130" class="Bound">A</a> <a id="4148" class="Symbol">→</a> <a id="4150" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4132" class="Bound">B</a><a id="4151" class="Symbol">)</a> <a id="4153" class="Symbol">{</a><a id="4154" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4154" class="Bound">x</a> <a id="4156" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4156" class="Bound">y</a> <a id="4158" class="Symbol">:</a> <a id="4160" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4130" class="Bound">A</a><a id="4161" class="Symbol">}</a>
  <a id="4165" class="Symbol">→</a> <a id="4167" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4154" class="Bound">x</a> <a id="4169" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="4171" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4156" class="Bound">y</a>
    <a id="4177" class="Comment">---------</a>
  <a id="4189" class="Symbol">→</a> <a id="4191" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4142" class="Bound">f</a> <a id="4193" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4154" class="Bound">x</a> <a id="4195" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="4197" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4142" class="Bound">f</a> <a id="4199" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4156" class="Bound">y</a>
<a id="4201" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4120" class="Function">cong</a> <a id="4206" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4206" class="Bound">f</a> <a id="4208" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#789" class="InductiveConstructor">refl</a>  <a id="4214" class="Symbol">=</a>  <a id="4217" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#789" class="InductiveConstructor">refl</a>{% endraw %}</pre>

Congruence of functions with two arguments is similar:
<pre class="Agda">{% raw %}<a id="cong₂"></a><a id="4302" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4302" class="Function">cong₂</a> <a id="4308" class="Symbol">:</a> <a id="4310" class="Symbol">∀</a> <a id="4312" class="Symbol">{</a><a id="4313" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4313" class="Bound">A</a> <a id="4315" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4315" class="Bound">B</a> <a id="4317" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4317" class="Bound">C</a> <a id="4319" class="Symbol">:</a> <a id="4321" class="PrimitiveType">Set</a><a id="4324" class="Symbol">}</a> <a id="4326" class="Symbol">(</a><a id="4327" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4327" class="Bound">f</a> <a id="4329" class="Symbol">:</a> <a id="4331" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4313" class="Bound">A</a> <a id="4333" class="Symbol">→</a> <a id="4335" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4315" class="Bound">B</a> <a id="4337" class="Symbol">→</a> <a id="4339" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4317" class="Bound">C</a><a id="4340" class="Symbol">)</a> <a id="4342" class="Symbol">{</a><a id="4343" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4343" class="Bound">u</a> <a id="4345" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4345" class="Bound">x</a> <a id="4347" class="Symbol">:</a> <a id="4349" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4313" class="Bound">A</a><a id="4350" class="Symbol">}</a> <a id="4352" class="Symbol">{</a><a id="4353" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4353" class="Bound">v</a> <a id="4355" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4355" class="Bound">y</a> <a id="4357" class="Symbol">:</a> <a id="4359" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4315" class="Bound">B</a><a id="4360" class="Symbol">}</a>
  <a id="4364" class="Symbol">→</a> <a id="4366" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4343" class="Bound">u</a> <a id="4368" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="4370" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4345" class="Bound">x</a>
  <a id="4374" class="Symbol">→</a> <a id="4376" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4353" class="Bound">v</a> <a id="4378" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="4380" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4355" class="Bound">y</a>
    <a id="4386" class="Comment">-------------</a>
  <a id="4402" class="Symbol">→</a> <a id="4404" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4327" class="Bound">f</a> <a id="4406" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4343" class="Bound">u</a> <a id="4408" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4353" class="Bound">v</a> <a id="4410" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="4412" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4327" class="Bound">f</a> <a id="4414" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4345" class="Bound">x</a> <a id="4416" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4355" class="Bound">y</a>
<a id="4418" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4302" class="Function">cong₂</a> <a id="4424" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4424" class="Bound">f</a> <a id="4426" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#789" class="InductiveConstructor">refl</a> <a id="4431" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#789" class="InductiveConstructor">refl</a>  <a id="4437" class="Symbol">=</a>  <a id="4440" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#789" class="InductiveConstructor">refl</a>{% endraw %}</pre>

Equality is also a congruence in the function position of an application.
If two functions are equal, then applying them to the same term
yields equal terms:
<pre class="Agda">{% raw %}<a id="cong-app"></a><a id="4628" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4628" class="Function">cong-app</a> <a id="4637" class="Symbol">:</a> <a id="4639" class="Symbol">∀</a> <a id="4641" class="Symbol">{</a><a id="4642" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4642" class="Bound">A</a> <a id="4644" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4644" class="Bound">B</a> <a id="4646" class="Symbol">:</a> <a id="4648" class="PrimitiveType">Set</a><a id="4651" class="Symbol">}</a> <a id="4653" class="Symbol">{</a><a id="4654" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4654" class="Bound">f</a> <a id="4656" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4656" class="Bound">g</a> <a id="4658" class="Symbol">:</a> <a id="4660" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4642" class="Bound">A</a> <a id="4662" class="Symbol">→</a> <a id="4664" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4644" class="Bound">B</a><a id="4665" class="Symbol">}</a>
  <a id="4669" class="Symbol">→</a> <a id="4671" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4654" class="Bound">f</a> <a id="4673" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="4675" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4656" class="Bound">g</a>
    <a id="4681" class="Comment">---------------------</a>
  <a id="4705" class="Symbol">→</a> <a id="4707" class="Symbol">∀</a> <a id="4709" class="Symbol">(</a><a id="4710" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4710" class="Bound">x</a> <a id="4712" class="Symbol">:</a> <a id="4714" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4642" class="Bound">A</a><a id="4715" class="Symbol">)</a> <a id="4717" class="Symbol">→</a> <a id="4719" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4654" class="Bound">f</a> <a id="4721" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4710" class="Bound">x</a> <a id="4723" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="4725" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4656" class="Bound">g</a> <a id="4727" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4710" class="Bound">x</a>
<a id="4729" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4628" class="Function">cong-app</a> <a id="4738" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#789" class="InductiveConstructor">refl</a> <a id="4743" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4743" class="Bound">x</a> <a id="4745" class="Symbol">=</a> <a id="4747" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#789" class="InductiveConstructor">refl</a>{% endraw %}</pre>

Equality also satisfies *substitution*.
If two values are equal and a predicate holds of the first then it also holds of the second:
<pre class="Agda">{% raw %}<a id="subst"></a><a id="4910" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4910" class="Function">subst</a> <a id="4916" class="Symbol">:</a> <a id="4918" class="Symbol">∀</a> <a id="4920" class="Symbol">{</a><a id="4921" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4921" class="Bound">A</a> <a id="4923" class="Symbol">:</a> <a id="4925" class="PrimitiveType">Set</a><a id="4928" class="Symbol">}</a> <a id="4930" class="Symbol">{</a><a id="4931" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4931" class="Bound">x</a> <a id="4933" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4933" class="Bound">y</a> <a id="4935" class="Symbol">:</a> <a id="4937" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4921" class="Bound">A</a><a id="4938" class="Symbol">}</a> <a id="4940" class="Symbol">(</a><a id="4941" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4941" class="Bound">P</a> <a id="4943" class="Symbol">:</a> <a id="4945" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4921" class="Bound">A</a> <a id="4947" class="Symbol">→</a> <a id="4949" class="PrimitiveType">Set</a><a id="4952" class="Symbol">)</a>
  <a id="4956" class="Symbol">→</a> <a id="4958" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4931" class="Bound">x</a> <a id="4960" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="4962" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4933" class="Bound">y</a>
    <a id="4968" class="Comment">---------</a>
  <a id="4980" class="Symbol">→</a> <a id="4982" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4941" class="Bound">P</a> <a id="4984" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4931" class="Bound">x</a> <a id="4986" class="Symbol">→</a> <a id="4988" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4941" class="Bound">P</a> <a id="4990" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4933" class="Bound">y</a>
<a id="4992" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4910" class="Function">subst</a> <a id="4998" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4998" class="Bound">P</a> <a id="5000" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#789" class="InductiveConstructor">refl</a> <a id="5005" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5005" class="Bound">px</a> <a id="5008" class="Symbol">=</a> <a id="5010" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5005" class="Bound">px</a>{% endraw %}</pre>


## Chains of equations

Here we show how to support reasoning with chains of equations, as
used throughout the book.  We package the declarations into a module,
named `≡-Reasoning`, to match the format used in Agda's standard
library:
<pre class="Agda">{% raw %}<a id="5274" class="Keyword">module</a> <a id="≡-Reasoning"></a><a id="5281" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5281" class="Module">≡-Reasoning</a> <a id="5293" class="Symbol">{</a><a id="5294" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5294" class="Bound">A</a> <a id="5296" class="Symbol">:</a> <a id="5298" class="PrimitiveType">Set</a><a id="5301" class="Symbol">}</a> <a id="5303" class="Keyword">where</a>

  <a id="5312" class="Keyword">infix</a>  <a id="5319" class="Number">1</a> <a id="5321" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5369" class="Function Operator">begin_</a>
  <a id="5330" class="Keyword">infixr</a> <a id="5337" class="Number">2</a> <a id="5339" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5449" class="Function Operator">_≡⟨⟩_</a> <a id="5345" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5534" class="Function Operator">_≡⟨_⟩_</a>
  <a id="5354" class="Keyword">infix</a>  <a id="5361" class="Number">3</a> <a id="5363" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5649" class="Function Operator">_∎</a>

  <a id="≡-Reasoning.begin_"></a><a id="5369" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5369" class="Function Operator">begin_</a> <a id="5376" class="Symbol">:</a> <a id="5378" class="Symbol">∀</a> <a id="5380" class="Symbol">{</a><a id="5381" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5381" class="Bound">x</a> <a id="5383" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5383" class="Bound">y</a> <a id="5385" class="Symbol">:</a> <a id="5387" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5294" class="Bound">A</a><a id="5388" class="Symbol">}</a>
    <a id="5394" class="Symbol">→</a> <a id="5396" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5381" class="Bound">x</a> <a id="5398" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="5400" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5383" class="Bound">y</a>
      <a id="5408" class="Comment">-----</a>
    <a id="5418" class="Symbol">→</a> <a id="5420" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5381" class="Bound">x</a> <a id="5422" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="5424" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5383" class="Bound">y</a>
  <a id="5428" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5369" class="Function Operator">begin</a> <a id="5434" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5434" class="Bound">x≡y</a>  <a id="5439" class="Symbol">=</a>  <a id="5442" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5434" class="Bound">x≡y</a>

  <a id="≡-Reasoning._≡⟨⟩_"></a><a id="5449" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5449" class="Function Operator">_≡⟨⟩_</a> <a id="5455" class="Symbol">:</a> <a id="5457" class="Symbol">∀</a> <a id="5459" class="Symbol">(</a><a id="5460" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5460" class="Bound">x</a> <a id="5462" class="Symbol">:</a> <a id="5464" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5294" class="Bound">A</a><a id="5465" class="Symbol">)</a> <a id="5467" class="Symbol">{</a><a id="5468" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5468" class="Bound">y</a> <a id="5470" class="Symbol">:</a> <a id="5472" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5294" class="Bound">A</a><a id="5473" class="Symbol">}</a>
    <a id="5479" class="Symbol">→</a> <a id="5481" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5460" class="Bound">x</a> <a id="5483" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="5485" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5468" class="Bound">y</a>
      <a id="5493" class="Comment">-----</a>
    <a id="5503" class="Symbol">→</a> <a id="5505" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5460" class="Bound">x</a> <a id="5507" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="5509" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5468" class="Bound">y</a>
  <a id="5513" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5513" class="Bound">x</a> <a id="5515" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5449" class="Function Operator">≡⟨⟩</a> <a id="5519" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5519" class="Bound">x≡y</a>  <a id="5524" class="Symbol">=</a>  <a id="5527" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5519" class="Bound">x≡y</a>

  <a id="≡-Reasoning._≡⟨_⟩_"></a><a id="5534" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5534" class="Function Operator">_≡⟨_⟩_</a> <a id="5541" class="Symbol">:</a> <a id="5543" class="Symbol">∀</a> <a id="5545" class="Symbol">(</a><a id="5546" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5546" class="Bound">x</a> <a id="5548" class="Symbol">:</a> <a id="5550" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5294" class="Bound">A</a><a id="5551" class="Symbol">)</a> <a id="5553" class="Symbol">{</a><a id="5554" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5554" class="Bound">y</a> <a id="5556" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5556" class="Bound">z</a> <a id="5558" class="Symbol">:</a> <a id="5560" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5294" class="Bound">A</a><a id="5561" class="Symbol">}</a>
    <a id="5567" class="Symbol">→</a> <a id="5569" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5546" class="Bound">x</a> <a id="5571" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="5573" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5554" class="Bound">y</a>
    <a id="5579" class="Symbol">→</a> <a id="5581" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5554" class="Bound">y</a> <a id="5583" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="5585" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5556" class="Bound">z</a>
      <a id="5593" class="Comment">-----</a>
    <a id="5603" class="Symbol">→</a> <a id="5605" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5546" class="Bound">x</a> <a id="5607" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="5609" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5556" class="Bound">z</a>
  <a id="5613" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5613" class="Bound">x</a> <a id="5615" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5534" class="Function Operator">≡⟨</a> <a id="5618" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5618" class="Bound">x≡y</a> <a id="5622" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5534" class="Function Operator">⟩</a> <a id="5624" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5624" class="Bound">y≡z</a>  <a id="5629" class="Symbol">=</a>  <a id="5632" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#3688" class="Function">trans</a> <a id="5638" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5618" class="Bound">x≡y</a> <a id="5642" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5624" class="Bound">y≡z</a>

  <a id="≡-Reasoning._∎"></a><a id="5649" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5649" class="Function Operator">_∎</a> <a id="5652" class="Symbol">:</a> <a id="5654" class="Symbol">∀</a> <a id="5656" class="Symbol">(</a><a id="5657" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5657" class="Bound">x</a> <a id="5659" class="Symbol">:</a> <a id="5661" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5294" class="Bound">A</a><a id="5662" class="Symbol">)</a>
      <a id="5670" class="Comment">-----</a>
    <a id="5680" class="Symbol">→</a> <a id="5682" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5657" class="Bound">x</a> <a id="5684" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="5686" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5657" class="Bound">x</a>
  <a id="5690" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5690" class="Bound">x</a> <a id="5692" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5649" class="Function Operator">∎</a>  <a id="5695" class="Symbol">=</a>  <a id="5698" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#789" class="InductiveConstructor">refl</a>

<a id="5704" class="Keyword">open</a> <a id="5709" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5281" class="Module">≡-Reasoning</a>{% endraw %}</pre>
This is our first use of a nested module. It consists of the keyword
`module` followed by the module name and any parameters, explicit or
implicit, the keyword `where`, and the contents of the module indented.
Modules may contain any sort of declaration, including other nested modules.
Nested modules are similar to the top-level modules that constitute
each chapter of this book, save that the body of a top-level module
need not be indented.  Opening the module makes all of the definitions
available in the current environment.

As an example, let's look at a proof of transitivity
as a chain of equations:
<pre class="Agda">{% raw %}<a id="trans′"></a><a id="6356" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6356" class="Function">trans′</a> <a id="6363" class="Symbol">:</a> <a id="6365" class="Symbol">∀</a> <a id="6367" class="Symbol">{</a><a id="6368" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6368" class="Bound">A</a> <a id="6370" class="Symbol">:</a> <a id="6372" class="PrimitiveType">Set</a><a id="6375" class="Symbol">}</a> <a id="6377" class="Symbol">{</a><a id="6378" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6378" class="Bound">x</a> <a id="6380" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6380" class="Bound">y</a> <a id="6382" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6382" class="Bound">z</a> <a id="6384" class="Symbol">:</a> <a id="6386" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6368" class="Bound">A</a><a id="6387" class="Symbol">}</a>
  <a id="6391" class="Symbol">→</a> <a id="6393" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6378" class="Bound">x</a> <a id="6395" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="6397" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6380" class="Bound">y</a>
  <a id="6401" class="Symbol">→</a> <a id="6403" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6380" class="Bound">y</a> <a id="6405" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="6407" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6382" class="Bound">z</a>
    <a id="6413" class="Comment">-----</a>
  <a id="6421" class="Symbol">→</a> <a id="6423" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6378" class="Bound">x</a> <a id="6425" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="6427" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6382" class="Bound">z</a>
<a id="6429" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6356" class="Function">trans′</a> <a id="6436" class="Symbol">{</a><a id="6437" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6437" class="Bound">A</a><a id="6438" class="Symbol">}</a> <a id="6440" class="Symbol">{</a><a id="6441" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6441" class="Bound">x</a><a id="6442" class="Symbol">}</a> <a id="6444" class="Symbol">{</a><a id="6445" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6445" class="Bound">y</a><a id="6446" class="Symbol">}</a> <a id="6448" class="Symbol">{</a><a id="6449" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6449" class="Bound">z</a><a id="6450" class="Symbol">}</a> <a id="6452" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6452" class="Bound">x≡y</a> <a id="6456" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6456" class="Bound">y≡z</a> <a id="6460" class="Symbol">=</a>
  <a id="6464" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5369" class="Function Operator">begin</a>
    <a id="6474" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6441" class="Bound">x</a>
  <a id="6478" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5534" class="Function Operator">≡⟨</a> <a id="6481" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6452" class="Bound">x≡y</a> <a id="6485" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5534" class="Function Operator">⟩</a>
    <a id="6491" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6445" class="Bound">y</a>
  <a id="6495" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5534" class="Function Operator">≡⟨</a> <a id="6498" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6456" class="Bound">y≡z</a> <a id="6502" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5534" class="Function Operator">⟩</a>
    <a id="6508" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6449" class="Bound">z</a>
  <a id="6512" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5649" class="Function Operator">∎</a>{% endraw %}</pre>
According to the fixity declarations, the body parses as follows:

    begin (x ≡⟨ x≡y ⟩ (y ≡⟨ y≡z ⟩ (z ∎)))

The application of `begin` is purely cosmetic, as it simply returns
its argument.  That argument consists of `_≡⟨_⟩_` applied to `x`,
`x≡y`, and `y ≡⟨ y≡z ⟩ (z ∎)`.  The first argument is a term, `x`,
while the second and third arguments are both proofs of equations, in
particular proofs of `x ≡ y` and `y ≡ z` respectively, which are
combined by `trans` in the body of `_≡⟨_⟩_` to yield a proof of `x ≡
z`.  The proof of `y ≡ z` consists of `_≡⟨_⟩_` applied to `y`, `y≡z`,
and `z ∎`.  The first argument is a term, `y`, while the second and
third arguments are both proofs of equations, in particular proofs of
`y ≡ z` and `z ≡ z` respectively, which are combined by `trans` in the
body of `_≡⟨_⟩_` to yield a proof of `y ≡ z`.  Finally, the proof of
`z ≡ z` consists of `_∎` applied to the term `z`, which yields `refl`.
After simplification, the body is equivalent to the term:

    trans x≡y (trans y≡z refl)

We could replace any use of a chain of equations by a chain of
applications of `trans`; the result would be more compact but harder
to read.  The trick behind `∎` means that a chain of equalities
simplifies to a chain of applications of `trans` than ends in `trans e
refl`, where `e` is a term that proves some equality, even though `e`
alone would do.


## Chains of equations, another example

As a second example of chains of equations, we repeat the proof that addition
is commutative.  We first repeat the definitions of naturals and addition.
We cannot import them because (as noted at the beginning of this chapter)
it would cause a conflict:
<pre class="Agda">{% raw %}<a id="8213" class="Keyword">data</a> <a id="ℕ"></a><a id="8218" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="Datatype">ℕ</a> <a id="8220" class="Symbol">:</a> <a id="8222" class="PrimitiveType">Set</a> <a id="8226" class="Keyword">where</a>
  <a id="ℕ.zero"></a><a id="8234" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8234" class="InductiveConstructor">zero</a> <a id="8239" class="Symbol">:</a> <a id="8241" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="Datatype">ℕ</a>
  <a id="ℕ.suc"></a><a id="8245" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8245" class="InductiveConstructor">suc</a>  <a id="8250" class="Symbol">:</a> <a id="8252" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="Datatype">ℕ</a> <a id="8254" class="Symbol">→</a> <a id="8256" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="Datatype">ℕ</a>

<a id="_+_"></a><a id="8259" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">_+_</a> <a id="8263" class="Symbol">:</a> <a id="8265" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="Datatype">ℕ</a> <a id="8267" class="Symbol">→</a> <a id="8269" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="Datatype">ℕ</a> <a id="8271" class="Symbol">→</a> <a id="8273" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="Datatype">ℕ</a>
<a id="8275" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8234" class="InductiveConstructor">zero</a>    <a id="8283" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="8285" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8285" class="Bound">n</a>  <a id="8288" class="Symbol">=</a>  <a id="8291" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8285" class="Bound">n</a>
<a id="8293" class="Symbol">(</a><a id="8294" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8245" class="InductiveConstructor">suc</a> <a id="8298" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8298" class="Bound">m</a><a id="8299" class="Symbol">)</a> <a id="8301" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="8303" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8303" class="Bound">n</a>  <a id="8306" class="Symbol">=</a>  <a id="8309" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8245" class="InductiveConstructor">suc</a> <a id="8313" class="Symbol">(</a><a id="8314" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8298" class="Bound">m</a> <a id="8316" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="8318" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8303" class="Bound">n</a><a id="8319" class="Symbol">)</a>{% endraw %}</pre>

To save space we postulate (rather than prove in full) two lemmas:
<pre class="Agda">{% raw %}<a id="8413" class="Keyword">postulate</a>
  <a id="+-identity"></a><a id="8425" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8425" class="Postulate">+-identity</a> <a id="8436" class="Symbol">:</a> <a id="8438" class="Symbol">∀</a> <a id="8440" class="Symbol">(</a><a id="8441" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8441" class="Bound">m</a> <a id="8443" class="Symbol">:</a> <a id="8445" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="Datatype">ℕ</a><a id="8446" class="Symbol">)</a> <a id="8448" class="Symbol">→</a> <a id="8450" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8441" class="Bound">m</a> <a id="8452" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="8454" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8234" class="InductiveConstructor">zero</a> <a id="8459" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="8461" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8441" class="Bound">m</a>
  <a id="+-suc"></a><a id="8465" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8465" class="Postulate">+-suc</a> <a id="8471" class="Symbol">:</a> <a id="8473" class="Symbol">∀</a> <a id="8475" class="Symbol">(</a><a id="8476" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8476" class="Bound">m</a> <a id="8478" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8478" class="Bound">n</a> <a id="8480" class="Symbol">:</a> <a id="8482" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="Datatype">ℕ</a><a id="8483" class="Symbol">)</a> <a id="8485" class="Symbol">→</a> <a id="8487" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8476" class="Bound">m</a> <a id="8489" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="8491" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8245" class="InductiveConstructor">suc</a> <a id="8495" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8478" class="Bound">n</a> <a id="8497" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="8499" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8245" class="InductiveConstructor">suc</a> <a id="8503" class="Symbol">(</a><a id="8504" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8476" class="Bound">m</a> <a id="8506" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="8508" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8478" class="Bound">n</a><a id="8509" class="Symbol">)</a>{% endraw %}</pre>
This is our first use of a _postulate_.  A postulate specifies a
signature for an identifier but no definition.  Here we postulate
something proved earlier to save space.  Postulates must be used with
caution.  If we postulate something false then we could use Agda to
prove anything whatsoever.

We then repeat the proof of commutativity:
<pre class="Agda">{% raw %}<a id="+-comm"></a><a id="8875" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8875" class="Function">+-comm</a> <a id="8882" class="Symbol">:</a> <a id="8884" class="Symbol">∀</a> <a id="8886" class="Symbol">(</a><a id="8887" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8887" class="Bound">m</a> <a id="8889" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8889" class="Bound">n</a> <a id="8891" class="Symbol">:</a> <a id="8893" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="Datatype">ℕ</a><a id="8894" class="Symbol">)</a> <a id="8896" class="Symbol">→</a> <a id="8898" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8887" class="Bound">m</a> <a id="8900" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="8902" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8889" class="Bound">n</a> <a id="8904" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="8906" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8889" class="Bound">n</a> <a id="8908" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="8910" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8887" class="Bound">m</a>
<a id="8912" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8875" class="Function">+-comm</a> <a id="8919" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8919" class="Bound">m</a> <a id="8921" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8234" class="InductiveConstructor">zero</a> <a id="8926" class="Symbol">=</a>
  <a id="8930" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5369" class="Function Operator">begin</a>
    <a id="8940" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8919" class="Bound">m</a> <a id="8942" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="8944" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8234" class="InductiveConstructor">zero</a>
  <a id="8951" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5534" class="Function Operator">≡⟨</a> <a id="8954" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8425" class="Postulate">+-identity</a> <a id="8965" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8919" class="Bound">m</a> <a id="8967" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5534" class="Function Operator">⟩</a>
    <a id="8973" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8919" class="Bound">m</a>
  <a id="8977" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5449" class="Function Operator">≡⟨⟩</a>
    <a id="8985" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8234" class="InductiveConstructor">zero</a> <a id="8990" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="8992" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8919" class="Bound">m</a>
  <a id="8996" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5649" class="Function Operator">∎</a>
<a id="8998" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8875" class="Function">+-comm</a> <a id="9005" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9005" class="Bound">m</a> <a id="9007" class="Symbol">(</a><a id="9008" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8245" class="InductiveConstructor">suc</a> <a id="9012" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9012" class="Bound">n</a><a id="9013" class="Symbol">)</a> <a id="9015" class="Symbol">=</a>
  <a id="9019" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5369" class="Function Operator">begin</a>
    <a id="9029" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9005" class="Bound">m</a> <a id="9031" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="9033" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8245" class="InductiveConstructor">suc</a> <a id="9037" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9012" class="Bound">n</a>
  <a id="9041" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5534" class="Function Operator">≡⟨</a> <a id="9044" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8465" class="Postulate">+-suc</a> <a id="9050" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9005" class="Bound">m</a> <a id="9052" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9012" class="Bound">n</a> <a id="9054" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5534" class="Function Operator">⟩</a>
    <a id="9060" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8245" class="InductiveConstructor">suc</a> <a id="9064" class="Symbol">(</a><a id="9065" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9005" class="Bound">m</a> <a id="9067" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="9069" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9012" class="Bound">n</a><a id="9070" class="Symbol">)</a>
  <a id="9074" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5534" class="Function Operator">≡⟨</a> <a id="9077" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4120" class="Function">cong</a> <a id="9082" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8245" class="InductiveConstructor">suc</a> <a id="9086" class="Symbol">(</a><a id="9087" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8875" class="Function">+-comm</a> <a id="9094" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9005" class="Bound">m</a> <a id="9096" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9012" class="Bound">n</a><a id="9097" class="Symbol">)</a> <a id="9099" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5534" class="Function Operator">⟩</a>
    <a id="9105" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8245" class="InductiveConstructor">suc</a> <a id="9109" class="Symbol">(</a><a id="9110" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9012" class="Bound">n</a> <a id="9112" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="9114" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9005" class="Bound">m</a><a id="9115" class="Symbol">)</a>
  <a id="9119" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5449" class="Function Operator">≡⟨⟩</a>
    <a id="9127" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8245" class="InductiveConstructor">suc</a> <a id="9131" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9012" class="Bound">n</a> <a id="9133" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="9135" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#9005" class="Bound">m</a>
  <a id="9139" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5649" class="Function Operator">∎</a>{% endraw %}</pre>
The reasoning here is similar to that in the
preceding section.  We use
`_≡⟨⟩_` when no justification is required.
One can think of `_≡⟨⟩_` as equivalent to `_≡⟨ refl ⟩_`.

Agda always treats a term as equivalent to its
simplified term.  The reason that one can write

      suc (n + m)
    ≡⟨⟩
      suc n + m

is because Agda treats both terms as the same.
This also means that one could instead interchange
the lines and write

      suc n + m
    ≡⟨⟩
      suc (n + m)

and Agda would not object. Agda only checks that the terms separated
by `≡⟨⟩` have the same simplified form; it's up to us to write them in
an order that will make sense to the reader.


#### Exercise `≤-reasoning` (stretch)

The proof of monotonicity from
Chapter [Relations]({{ site.baseurl }}{% link out/plfa/Relations.md%})
can be written in a more readable form by using an analogue of our
notation for `≡-reasoning`.  Define `≤-reasoning` analogously, and use
it to write out an alternative proof that addition is monotonic with
regard to inequality.  Rewrite both `+-monoˡ-≤` and `+-mono-≤`.

<pre class="Agda">{% raw %}<a id="10204" class="Comment">-- Your code goes here</a>{% endraw %}</pre>



## Rewriting

Consider a property of natural numbers, such as being even.
We repeat the earlier definition:
<pre class="Agda">{% raw %}<a id="10362" class="Keyword">data</a> <a id="even"></a><a id="10367" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10367" class="Datatype">even</a> <a id="10372" class="Symbol">:</a> <a id="10374" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="Datatype">ℕ</a> <a id="10376" class="Symbol">→</a> <a id="10378" class="PrimitiveType">Set</a>
<a id="10382" class="Keyword">data</a> <a id="odd"></a><a id="10387" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10387" class="Datatype">odd</a>  <a id="10392" class="Symbol">:</a> <a id="10394" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="Datatype">ℕ</a> <a id="10396" class="Symbol">→</a> <a id="10398" class="PrimitiveType">Set</a>

<a id="10403" class="Keyword">data</a> <a id="10408" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10367" class="Datatype">even</a> <a id="10413" class="Keyword">where</a>

  <a id="even.even-zero"></a><a id="10422" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10422" class="InductiveConstructor">even-zero</a> <a id="10432" class="Symbol">:</a> <a id="10434" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10367" class="Datatype">even</a> <a id="10439" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8234" class="InductiveConstructor">zero</a>

  <a id="even.even-suc"></a><a id="10447" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10447" class="InductiveConstructor">even-suc</a> <a id="10456" class="Symbol">:</a> <a id="10458" class="Symbol">∀</a> <a id="10460" class="Symbol">{</a><a id="10461" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10461" class="Bound">n</a> <a id="10463" class="Symbol">:</a> <a id="10465" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="Datatype">ℕ</a><a id="10466" class="Symbol">}</a>
    <a id="10472" class="Symbol">→</a> <a id="10474" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10387" class="Datatype">odd</a> <a id="10478" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10461" class="Bound">n</a>
      <a id="10486" class="Comment">------------</a>
    <a id="10503" class="Symbol">→</a> <a id="10505" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10367" class="Datatype">even</a> <a id="10510" class="Symbol">(</a><a id="10511" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8245" class="InductiveConstructor">suc</a> <a id="10515" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10461" class="Bound">n</a><a id="10516" class="Symbol">)</a>

<a id="10519" class="Keyword">data</a> <a id="10524" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10387" class="Datatype">odd</a> <a id="10528" class="Keyword">where</a>
  <a id="odd.odd-suc"></a><a id="10536" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10536" class="InductiveConstructor">odd-suc</a> <a id="10544" class="Symbol">:</a> <a id="10546" class="Symbol">∀</a> <a id="10548" class="Symbol">{</a><a id="10549" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10549" class="Bound">n</a> <a id="10551" class="Symbol">:</a> <a id="10553" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="Datatype">ℕ</a><a id="10554" class="Symbol">}</a>
    <a id="10560" class="Symbol">→</a> <a id="10562" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10367" class="Datatype">even</a> <a id="10567" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10549" class="Bound">n</a>
      <a id="10575" class="Comment">-----------</a>
    <a id="10591" class="Symbol">→</a> <a id="10593" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10387" class="Datatype">odd</a> <a id="10597" class="Symbol">(</a><a id="10598" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8245" class="InductiveConstructor">suc</a> <a id="10602" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10549" class="Bound">n</a><a id="10603" class="Symbol">)</a>{% endraw %}</pre>
In the previous section, we proved addition is commutative.  Given
evidence that `even (m + n)` holds, we ought also to be able to take
that as evidence that `even (n + m)` holds.

Agda includes special notation to support just this kind of reasoning,
the `rewrite` notation we encountered earlier.
To enable this notation, we use pragmas to tell Agda which type
corresponds to equality:
<pre class="Agda">{% raw %}<a id="11017" class="Symbol">{-#</a> <a id="11021" class="Keyword">BUILTIN</a> EQUALITY <a id="11038" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">_≡_</a> <a id="11042" class="Symbol">#-}</a>{% endraw %}</pre>

We can then prove the desired property as follows:
<pre class="Agda">{% raw %}<a id="even-comm"></a><a id="11122" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11122" class="Function">even-comm</a> <a id="11132" class="Symbol">:</a> <a id="11134" class="Symbol">∀</a> <a id="11136" class="Symbol">(</a><a id="11137" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11137" class="Bound">m</a> <a id="11139" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11139" class="Bound">n</a> <a id="11141" class="Symbol">:</a> <a id="11143" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="Datatype">ℕ</a><a id="11144" class="Symbol">)</a>
  <a id="11148" class="Symbol">→</a> <a id="11150" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10367" class="Datatype">even</a> <a id="11155" class="Symbol">(</a><a id="11156" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11137" class="Bound">m</a> <a id="11158" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="11160" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11139" class="Bound">n</a><a id="11161" class="Symbol">)</a>
    <a id="11167" class="Comment">------------</a>
  <a id="11182" class="Symbol">→</a> <a id="11184" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10367" class="Datatype">even</a> <a id="11189" class="Symbol">(</a><a id="11190" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11139" class="Bound">n</a> <a id="11192" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="11194" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11137" class="Bound">m</a><a id="11195" class="Symbol">)</a>
<a id="11197" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11122" class="Function">even-comm</a> <a id="11207" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11207" class="Bound">m</a> <a id="11209" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11209" class="Bound">n</a> <a id="11211" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11211" class="Bound">ev</a>  <a id="11215" class="Keyword">rewrite</a> <a id="11223" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8875" class="Function">+-comm</a> <a id="11230" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11209" class="Bound">n</a> <a id="11232" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11207" class="Bound">m</a>  <a id="11235" class="Symbol">=</a>  <a id="11238" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11211" class="Bound">ev</a>{% endraw %}</pre>
Here `ev` ranges over evidence that `even (m + n)` holds, and we show
that it also provides evidence that `even (n + m)` holds.  In
general, the keyword `rewrite` is followed by evidence of an
equality, and that equality is used to rewrite the type of the
goal and of any variable in scope.

It is instructive to develop `even-comm` interactively.  To start, we
supply variables for the arguments on the left, and a hole for the
body on the right:

    even-comm : ∀ (m n : ℕ)
      → even (m + n)
        ------------
      → even (n + m)
    even-comm m n ev = {! !}

If we go into the hole and type `C-c C-,` then Agda reports:

    Goal: even (n + m)
    ————————————————————————————————————————————————————————————
    ev : even (m + n)
    n  : ℕ
    m  : ℕ

Now we add the rewrite:

    even-comm : ∀ (m n : ℕ)
      → even (m + n)
        ------------
      → even (n + m)
    even-comm m n ev rewrite +-comm n m = {! !}

If we go into the hole again and type `C-c C-,` then Agda now reports:

    Goal: even (m + n)
    ————————————————————————————————————————————————————————————
    ev : even (m + n)
    n  : ℕ
    m  : ℕ

The arguments have been swapped in the goal.  Now it is trivial to see
that `ev` satisfies the goal, and typing `C-c C-a` in the hole causes
it to be filled with `ev`.  The command `C-c C-a` performs an
automated search, including checking whether a variable in scope has
the same type as the goal.


## Multiple rewrites

One may perform multiple rewrites, each separated by a vertical bar.  For instance,
here is a second proof that addition is commutative, relying on rewrites rather
than chains of equalities:
<pre class="Agda">{% raw %}<a id="+-comm′"></a><a id="12914" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12914" class="Function">+-comm′</a> <a id="12922" class="Symbol">:</a> <a id="12924" class="Symbol">∀</a> <a id="12926" class="Symbol">(</a><a id="12927" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12927" class="Bound">m</a> <a id="12929" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12929" class="Bound">n</a> <a id="12931" class="Symbol">:</a> <a id="12933" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="Datatype">ℕ</a><a id="12934" class="Symbol">)</a> <a id="12936" class="Symbol">→</a> <a id="12938" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12927" class="Bound">m</a> <a id="12940" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="12942" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12929" class="Bound">n</a> <a id="12944" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="12946" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12929" class="Bound">n</a> <a id="12948" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="12950" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12927" class="Bound">m</a>
<a id="12952" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12914" class="Function">+-comm′</a> <a id="12960" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8234" class="InductiveConstructor">zero</a>    <a id="12968" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12968" class="Bound">n</a>  <a id="12971" class="Keyword">rewrite</a> <a id="12979" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8425" class="Postulate">+-identity</a> <a id="12990" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12968" class="Bound">n</a>             <a id="13004" class="Symbol">=</a>  <a id="13007" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#789" class="InductiveConstructor">refl</a>
<a id="13012" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12914" class="Function">+-comm′</a> <a id="13020" class="Symbol">(</a><a id="13021" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8245" class="InductiveConstructor">suc</a> <a id="13025" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13025" class="Bound">m</a><a id="13026" class="Symbol">)</a> <a id="13028" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13028" class="Bound">n</a>  <a id="13031" class="Keyword">rewrite</a> <a id="13039" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8465" class="Postulate">+-suc</a> <a id="13045" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13028" class="Bound">n</a> <a id="13047" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13025" class="Bound">m</a> <a id="13049" class="Symbol">|</a> <a id="13051" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#12914" class="Function">+-comm′</a> <a id="13059" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13025" class="Bound">m</a> <a id="13061" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13028" class="Bound">n</a>  <a id="13064" class="Symbol">=</a>  <a id="13067" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#789" class="InductiveConstructor">refl</a>{% endraw %}</pre>
This is far more compact.  Among other things, whereas the previous
proof required `cong suc (+-comm m n)` as the justification to invoke
the inductive hypothesis, here it is sufficient to rewrite with
`+-comm m n`, as rewriting automatically takes congruence into
account.  Although proofs with rewriting are shorter, proofs as chains
of equalities are easier to follow, and we will stick with the latter
when feasible.


## Rewriting expanded

The `rewrite` notation is in fact shorthand for an appropriate use of `with`
abstraction:
<pre class="Agda">{% raw %}<a id="even-comm′"></a><a id="13632" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13632" class="Function">even-comm′</a> <a id="13643" class="Symbol">:</a> <a id="13645" class="Symbol">∀</a> <a id="13647" class="Symbol">(</a><a id="13648" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13648" class="Bound">m</a> <a id="13650" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13650" class="Bound">n</a> <a id="13652" class="Symbol">:</a> <a id="13654" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="Datatype">ℕ</a><a id="13655" class="Symbol">)</a>
  <a id="13659" class="Symbol">→</a> <a id="13661" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10367" class="Datatype">even</a> <a id="13666" class="Symbol">(</a><a id="13667" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13648" class="Bound">m</a> <a id="13669" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="13671" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13650" class="Bound">n</a><a id="13672" class="Symbol">)</a>
    <a id="13678" class="Comment">------------</a>
  <a id="13693" class="Symbol">→</a> <a id="13695" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10367" class="Datatype">even</a> <a id="13700" class="Symbol">(</a><a id="13701" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13650" class="Bound">n</a> <a id="13703" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="13705" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13648" class="Bound">m</a><a id="13706" class="Symbol">)</a>
<a id="13708" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13632" class="Function">even-comm′</a> <a id="13719" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13719" class="Bound">m</a> <a id="13721" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13721" class="Bound">n</a> <a id="13723" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13723" class="Bound">ev</a> <a id="13726" class="Keyword">with</a>   <a id="13733" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13719" class="Bound">m</a> <a id="13735" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="13737" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13721" class="Bound">n</a>  <a id="13740" class="Symbol">|</a> <a id="13742" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8875" class="Function">+-comm</a> <a id="13749" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13719" class="Bound">m</a> <a id="13751" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13721" class="Bound">n</a>
<a id="13753" class="Symbol">...</a>                  <a id="13774" class="Symbol">|</a> <a id="13776" class="DottedPattern Symbol">.(</a><a id="13778" class="DottedPattern Bound">n</a> <a id="13780" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="DottedPattern Function Operator">+</a> <a id="13782" class="DottedPattern Bound">m</a><a id="13783" class="DottedPattern Symbol">)</a> <a id="13785" class="Symbol">|</a> <a id="13787" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#789" class="InductiveConstructor">refl</a>       <a id="13798" class="Symbol">=</a> <a id="13800" class="Bound">ev</a>{% endraw %}</pre>
In general, one can follow `with` by any number of expressions,
separated by bars, where each following equation has the same number
of patterns.  We often write expressions and the corresponding
patterns so they line up in columns, as above. Here the first column
asserts that `m + n` and `n + m` are identical, and the second column
justifies that assertion with evidence of the appropriate equality.
Note also the use of the _dot pattern_, `.(n + m)`.  A dot pattern
consists of a dot followed by an expression, and is used when other
information forces the value matched to be equal to the value of the
expression in the dot pattern.  In this case, the identification of
`m + n` and `n + m` is justified by the subsequent matching of
`+-comm m n` against `refl`.  One might think that the first clause is
redundant as the information is inherent in the second clause, but in
fact Agda is rather picky on this point: omitting the first clause or
reversing the order of the clauses will cause Agda to report an error.
(Try it and see!)

In this case, we can avoid rewrite by simply applying the substitution
function defined earlier:
<pre class="Agda">{% raw %}<a id="even-comm″"></a><a id="14963" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14963" class="Function">even-comm″</a> <a id="14974" class="Symbol">:</a> <a id="14976" class="Symbol">∀</a> <a id="14978" class="Symbol">(</a><a id="14979" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14979" class="Bound">m</a> <a id="14981" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14981" class="Bound">n</a> <a id="14983" class="Symbol">:</a> <a id="14985" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8218" class="Datatype">ℕ</a><a id="14986" class="Symbol">)</a>
  <a id="14990" class="Symbol">→</a> <a id="14992" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10367" class="Datatype">even</a> <a id="14997" class="Symbol">(</a><a id="14998" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14979" class="Bound">m</a> <a id="15000" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="15002" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14981" class="Bound">n</a><a id="15003" class="Symbol">)</a>
    <a id="15009" class="Comment">------------</a>
  <a id="15024" class="Symbol">→</a> <a id="15026" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10367" class="Datatype">even</a> <a id="15031" class="Symbol">(</a><a id="15032" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14981" class="Bound">n</a> <a id="15034" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8259" class="Function Operator">+</a> <a id="15036" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14979" class="Bound">m</a><a id="15037" class="Symbol">)</a>
<a id="15039" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14963" class="Function">even-comm″</a> <a id="15050" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15050" class="Bound">m</a> <a id="15052" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15052" class="Bound">n</a>  <a id="15055" class="Symbol">=</a>  <a id="15058" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4910" class="Function">subst</a> <a id="15064" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#10367" class="Datatype">even</a> <a id="15069" class="Symbol">(</a><a id="15070" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8875" class="Function">+-comm</a> <a id="15077" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15050" class="Bound">m</a> <a id="15079" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#15052" class="Bound">n</a><a id="15080" class="Symbol">)</a>{% endraw %}</pre>
Nonetheless, rewrite is a vital part of the Agda toolkit.  We will use
it sparingly, but it is occasionally essential.


## Leibniz equality

The form of asserting equality that we have used is due to Martin
Löf, and was published in 1975.  An older form is due to Leibniz, and
was published in 1686.  Leibniz asserted the _identity of
indiscernibles_: two objects are equal if and only if they satisfy the
same properties. This principle sometimes goes by the name Leibniz'
Law, and is closely related to Spock's Law, "A difference that makes
no difference is no difference".  Here we define Leibniz equality,
and show that two terms satisfy Leibniz equality if and only if they
satisfy Martin Löf equality.

Leibniz equality is usually formalised to state that `x ≐ y` holds if
every property `P` that holds of `x` also holds of `y`.  Perhaps
surprisingly, this definition is sufficient to also ensure the
converse, that every property `P` that holds of `y` also holds of `x`.

Let `x` and `y` be objects of type `A`. We say that `x ≐ y` holds if
for every predicate `P` over type `A` we have that `P x` implies `P y`:
<pre class="Agda">{% raw %}<a id="_≐_"></a><a id="16227" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16227" class="Function Operator">_≐_</a> <a id="16231" class="Symbol">:</a> <a id="16233" class="Symbol">∀</a> <a id="16235" class="Symbol">{</a><a id="16236" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16236" class="Bound">A</a> <a id="16238" class="Symbol">:</a> <a id="16240" class="PrimitiveType">Set</a><a id="16243" class="Symbol">}</a> <a id="16245" class="Symbol">(</a><a id="16246" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16246" class="Bound">x</a> <a id="16248" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16248" class="Bound">y</a> <a id="16250" class="Symbol">:</a> <a id="16252" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16236" class="Bound">A</a><a id="16253" class="Symbol">)</a> <a id="16255" class="Symbol">→</a> <a id="16257" class="PrimitiveType">Set₁</a>
<a id="16262" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16227" class="Function Operator">_≐_</a> <a id="16266" class="Symbol">{</a><a id="16267" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16267" class="Bound">A</a><a id="16268" class="Symbol">}</a> <a id="16270" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16270" class="Bound">x</a> <a id="16272" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16272" class="Bound">y</a> <a id="16274" class="Symbol">=</a> <a id="16276" class="Symbol">∀</a> <a id="16278" class="Symbol">(</a><a id="16279" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16279" class="Bound">P</a> <a id="16281" class="Symbol">:</a> <a id="16283" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16267" class="Bound">A</a> <a id="16285" class="Symbol">→</a> <a id="16287" class="PrimitiveType">Set</a><a id="16290" class="Symbol">)</a> <a id="16292" class="Symbol">→</a> <a id="16294" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16279" class="Bound">P</a> <a id="16296" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16270" class="Bound">x</a> <a id="16298" class="Symbol">→</a> <a id="16300" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16279" class="Bound">P</a> <a id="16302" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16272" class="Bound">y</a>{% endraw %}</pre>
We cannot write the left-hand side of the equation as `x ≐ y`,
and instead we write `_≐_ {A} x y` to provide access to the implicit
parameter `A` which appears on the right-hand side.

This is our first use of _levels_.  We cannot assign `Set` the type
`Set`, since this would lead to contradictions such as Russell's
Paradox and Girard's Paradox.  Instead, there is a hierarchy of types,
where `Set : Set₁`, `Set₁ : Set₂`, and so on.  In fact, `Set` itself
is just an abbreviation for `Set₀`.  Since the equation defining `_≐_`
mentions `Set` on the right-hand side, the corresponding signature
must use `Set₁`.  We say a bit more about levels below.

Leibniz equality is reflexive and transitive,
where the first follows by a variant of the identity function
and the second by a variant of function composition:
<pre class="Agda">{% raw %}<a id="refl-≐"></a><a id="17142" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17142" class="Function">refl-≐</a> <a id="17149" class="Symbol">:</a> <a id="17151" class="Symbol">∀</a> <a id="17153" class="Symbol">{</a><a id="17154" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17154" class="Bound">A</a> <a id="17156" class="Symbol">:</a> <a id="17158" class="PrimitiveType">Set</a><a id="17161" class="Symbol">}</a> <a id="17163" class="Symbol">{</a><a id="17164" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17164" class="Bound">x</a> <a id="17166" class="Symbol">:</a> <a id="17168" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17154" class="Bound">A</a><a id="17169" class="Symbol">}</a>
  <a id="17173" class="Symbol">→</a> <a id="17175" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17164" class="Bound">x</a> <a id="17177" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16227" class="Function Operator">≐</a> <a id="17179" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17164" class="Bound">x</a>
<a id="17181" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17142" class="Function">refl-≐</a> <a id="17188" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17188" class="Bound">P</a> <a id="17190" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17190" class="Bound">Px</a>  <a id="17194" class="Symbol">=</a>  <a id="17197" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17190" class="Bound">Px</a>

<a id="trans-≐"></a><a id="17201" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17201" class="Function">trans-≐</a> <a id="17209" class="Symbol">:</a> <a id="17211" class="Symbol">∀</a> <a id="17213" class="Symbol">{</a><a id="17214" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17214" class="Bound">A</a> <a id="17216" class="Symbol">:</a> <a id="17218" class="PrimitiveType">Set</a><a id="17221" class="Symbol">}</a> <a id="17223" class="Symbol">{</a><a id="17224" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17224" class="Bound">x</a> <a id="17226" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17226" class="Bound">y</a> <a id="17228" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17228" class="Bound">z</a> <a id="17230" class="Symbol">:</a> <a id="17232" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17214" class="Bound">A</a><a id="17233" class="Symbol">}</a>
  <a id="17237" class="Symbol">→</a> <a id="17239" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17224" class="Bound">x</a> <a id="17241" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16227" class="Function Operator">≐</a> <a id="17243" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17226" class="Bound">y</a>
  <a id="17247" class="Symbol">→</a> <a id="17249" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17226" class="Bound">y</a> <a id="17251" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16227" class="Function Operator">≐</a> <a id="17253" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17228" class="Bound">z</a>
    <a id="17259" class="Comment">-----</a>
  <a id="17267" class="Symbol">→</a> <a id="17269" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17224" class="Bound">x</a> <a id="17271" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16227" class="Function Operator">≐</a> <a id="17273" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17228" class="Bound">z</a>
<a id="17275" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17201" class="Function">trans-≐</a> <a id="17283" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17283" class="Bound">x≐y</a> <a id="17287" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17287" class="Bound">y≐z</a> <a id="17291" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17291" class="Bound">P</a> <a id="17293" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17293" class="Bound">Px</a>  <a id="17297" class="Symbol">=</a>  <a id="17300" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17287" class="Bound">y≐z</a> <a id="17304" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17291" class="Bound">P</a> <a id="17306" class="Symbol">(</a><a id="17307" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17283" class="Bound">x≐y</a> <a id="17311" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17291" class="Bound">P</a> <a id="17313" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17293" class="Bound">Px</a><a id="17315" class="Symbol">)</a>{% endraw %}</pre>

Symmetry is less obvious.  We have to show that if `P x` implies `P y`
for all predicates `P`, then the implication holds the other way round
as well:
<pre class="Agda">{% raw %}<a id="sym-≐"></a><a id="17493" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17493" class="Function">sym-≐</a> <a id="17499" class="Symbol">:</a> <a id="17501" class="Symbol">∀</a> <a id="17503" class="Symbol">{</a><a id="17504" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17504" class="Bound">A</a> <a id="17506" class="Symbol">:</a> <a id="17508" class="PrimitiveType">Set</a><a id="17511" class="Symbol">}</a> <a id="17513" class="Symbol">{</a><a id="17514" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17514" class="Bound">x</a> <a id="17516" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17516" class="Bound">y</a> <a id="17518" class="Symbol">:</a> <a id="17520" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17504" class="Bound">A</a><a id="17521" class="Symbol">}</a>
  <a id="17525" class="Symbol">→</a> <a id="17527" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17514" class="Bound">x</a> <a id="17529" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16227" class="Function Operator">≐</a> <a id="17531" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17516" class="Bound">y</a>
    <a id="17537" class="Comment">-----</a>
  <a id="17545" class="Symbol">→</a> <a id="17547" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17516" class="Bound">y</a> <a id="17549" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16227" class="Function Operator">≐</a> <a id="17551" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17514" class="Bound">x</a>
<a id="17553" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17493" class="Function">sym-≐</a> <a id="17559" class="Symbol">{</a><a id="17560" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17560" class="Bound">A</a><a id="17561" class="Symbol">}</a> <a id="17563" class="Symbol">{</a><a id="17564" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17564" class="Bound">x</a><a id="17565" class="Symbol">}</a> <a id="17567" class="Symbol">{</a><a id="17568" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17568" class="Bound">y</a><a id="17569" class="Symbol">}</a> <a id="17571" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17571" class="Bound">x≐y</a> <a id="17575" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17575" class="Bound">P</a>  <a id="17578" class="Symbol">=</a>  <a id="17581" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17663" class="Function">Qy</a>
  <a id="17586" class="Keyword">where</a>
    <a id="17596" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17596" class="Function">Q</a> <a id="17598" class="Symbol">:</a> <a id="17600" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17560" class="Bound">A</a> <a id="17602" class="Symbol">→</a> <a id="17604" class="PrimitiveType">Set</a>
    <a id="17612" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17596" class="Function">Q</a> <a id="17614" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17614" class="Bound">z</a> <a id="17616" class="Symbol">=</a> <a id="17618" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17575" class="Bound">P</a> <a id="17620" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17614" class="Bound">z</a> <a id="17622" class="Symbol">→</a> <a id="17624" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17575" class="Bound">P</a> <a id="17626" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17564" class="Bound">x</a>
    <a id="17632" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17632" class="Function">Qx</a> <a id="17635" class="Symbol">:</a> <a id="17637" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17596" class="Function">Q</a> <a id="17639" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17564" class="Bound">x</a>
    <a id="17645" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17632" class="Function">Qx</a> <a id="17648" class="Symbol">=</a> <a id="17650" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17142" class="Function">refl-≐</a> <a id="17657" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17575" class="Bound">P</a>
    <a id="17663" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17663" class="Function">Qy</a> <a id="17666" class="Symbol">:</a> <a id="17668" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17596" class="Function">Q</a> <a id="17670" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17568" class="Bound">y</a>
    <a id="17676" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17663" class="Function">Qy</a> <a id="17679" class="Symbol">=</a> <a id="17681" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17571" class="Bound">x≐y</a> <a id="17685" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17596" class="Function">Q</a> <a id="17687" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17632" class="Function">Qx</a>{% endraw %}</pre>
Given `x ≐ y`, a specific `P`, and a proof of `P y`, we have to
construct a proof of `P x`.  To do so, we instantiate the equality
with a predicate `Q` such that `Q z` holds if `P z` implies `P x`.
The property `Q x` is trivial by reflexivity, and hence `Q y` follows
from `x ≐ y`.  But `Q y` is exactly a proof of what we require, that
`P y` implies `P x`.

We now show that Martin Löf equality implies
Leibniz equality, and vice versa.  In the forward direction, if we know
`x ≡ y` we need for any `P` to take evidence of `P x` to evidence of `P y`,
which is easy since equality of `x` and `y` implies that any proof
of `P x` is also a proof of `P y`:
<pre class="Agda">{% raw %}<a id="≡-implies-≐"></a><a id="18368" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18368" class="Function">≡-implies-≐</a> <a id="18380" class="Symbol">:</a> <a id="18382" class="Symbol">∀</a> <a id="18384" class="Symbol">{</a><a id="18385" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18385" class="Bound">A</a> <a id="18387" class="Symbol">:</a> <a id="18389" class="PrimitiveType">Set</a><a id="18392" class="Symbol">}</a> <a id="18394" class="Symbol">{</a><a id="18395" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18395" class="Bound">x</a> <a id="18397" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18397" class="Bound">y</a> <a id="18399" class="Symbol">:</a> <a id="18401" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18385" class="Bound">A</a><a id="18402" class="Symbol">}</a>
  <a id="18406" class="Symbol">→</a> <a id="18408" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18395" class="Bound">x</a> <a id="18410" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="18412" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18397" class="Bound">y</a>
    <a id="18418" class="Comment">-----</a>
  <a id="18426" class="Symbol">→</a> <a id="18428" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18395" class="Bound">x</a> <a id="18430" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16227" class="Function Operator">≐</a> <a id="18432" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18397" class="Bound">y</a>
<a id="18434" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18368" class="Function">≡-implies-≐</a> <a id="18446" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18446" class="Bound">x≡y</a> <a id="18450" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18450" class="Bound">P</a>  <a id="18453" class="Symbol">=</a>  <a id="18456" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#4910" class="Function">subst</a> <a id="18462" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18450" class="Bound">P</a> <a id="18464" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18446" class="Bound">x≡y</a>{% endraw %}</pre>
This direction follows from substitution, which we showed earlier.

In the reverse direction, given that for any `P` we can take a proof of `P x`
to a proof of `P y` we need to show `x ≡ y`:
<pre class="Agda">{% raw %}<a id="≐-implies-≡"></a><a id="18683" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18683" class="Function">≐-implies-≡</a> <a id="18695" class="Symbol">:</a> <a id="18697" class="Symbol">∀</a> <a id="18699" class="Symbol">{</a><a id="18700" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18700" class="Bound">A</a> <a id="18702" class="Symbol">:</a> <a id="18704" class="PrimitiveType">Set</a><a id="18707" class="Symbol">}</a> <a id="18709" class="Symbol">{</a><a id="18710" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18710" class="Bound">x</a> <a id="18712" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18712" class="Bound">y</a> <a id="18714" class="Symbol">:</a> <a id="18716" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18700" class="Bound">A</a><a id="18717" class="Symbol">}</a>
  <a id="18721" class="Symbol">→</a> <a id="18723" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18710" class="Bound">x</a> <a id="18725" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#16227" class="Function Operator">≐</a> <a id="18727" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18712" class="Bound">y</a>
    <a id="18733" class="Comment">-----</a>
  <a id="18741" class="Symbol">→</a> <a id="18743" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18710" class="Bound">x</a> <a id="18745" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="18747" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18712" class="Bound">y</a>
<a id="18749" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18683" class="Function">≐-implies-≡</a> <a id="18761" class="Symbol">{</a><a id="18762" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18762" class="Bound">A</a><a id="18763" class="Symbol">}</a> <a id="18765" class="Symbol">{</a><a id="18766" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18766" class="Bound">x</a><a id="18767" class="Symbol">}</a> <a id="18769" class="Symbol">{</a><a id="18770" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18770" class="Bound">y</a><a id="18771" class="Symbol">}</a> <a id="18773" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18773" class="Bound">x≐y</a>  <a id="18778" class="Symbol">=</a>  <a id="18781" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18855" class="Function">Qy</a>
  <a id="18786" class="Keyword">where</a>
    <a id="18796" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18796" class="Function">Q</a> <a id="18798" class="Symbol">:</a> <a id="18800" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18762" class="Bound">A</a> <a id="18802" class="Symbol">→</a> <a id="18804" class="PrimitiveType">Set</a>
    <a id="18812" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18796" class="Function">Q</a> <a id="18814" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18814" class="Bound">z</a> <a id="18816" class="Symbol">=</a> <a id="18818" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18766" class="Bound">x</a> <a id="18820" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#749" class="Datatype Operator">≡</a> <a id="18822" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18814" class="Bound">z</a>
    <a id="18828" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18828" class="Function">Qx</a> <a id="18831" class="Symbol">:</a> <a id="18833" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18796" class="Function">Q</a> <a id="18835" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18766" class="Bound">x</a>
    <a id="18841" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18828" class="Function">Qx</a> <a id="18844" class="Symbol">=</a> <a id="18846" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#789" class="InductiveConstructor">refl</a>
    <a id="18855" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18855" class="Function">Qy</a> <a id="18858" class="Symbol">:</a> <a id="18860" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18796" class="Function">Q</a> <a id="18862" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18770" class="Bound">y</a>
    <a id="18868" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18855" class="Function">Qy</a> <a id="18871" class="Symbol">=</a> <a id="18873" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18773" class="Bound">x≐y</a> <a id="18877" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18796" class="Function">Q</a> <a id="18879" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18828" class="Function">Qx</a>{% endraw %}</pre>
The proof is similar to that for symmetry of Leibniz equality. We take
`Q` to be the predicate that holds of `z` if `x ≡ z`. Then `Q x` is
trivial by reflexivity of Martin Löf equality, and hence `Q y`
follows from `x ≐ y`.  But `Q y` is exactly a proof of what we
require, that `x ≡ y`.

(Parts of this section are adapted from *≐≃≡: Leibniz Equality is
Isomorphic to Martin-Löf Identity, Parametrically*, by Andreas Abel,
Jesper Cockx, Dominique Devries, Andreas Nuyts, and Philip Wadler,
draft, 2017.)


## Universe polymorphism {#unipoly}

As we have seen, not every type belongs to `Set`, but instead every
type belongs somewhere in the hierarchy `Set₀`, `Set₁`, `Set₂`, and so on,
where `Set` abbreviates `Set₀`, and `Set₀ : Set₁`, `Set₁ : Set₂`, and so on.
The definition of equality given above is fine if we want to compare two
values of a type that belongs to `Set`, but what if we want to compare
two values of a type that belongs to `Set ℓ` for some arbitrary level `ℓ`?

The answer is _universe polymorphism_, where a definition is made
with respect to an arbitrary level `ℓ`. To make use of levels, we
first import the following:
<pre class="Agda">{% raw %}<a id="20050" class="Keyword">open</a> <a id="20055" class="Keyword">import</a> <a id="20062" href="Level.html" class="Module">Level</a> <a id="20068" class="Keyword">using</a> <a id="20074" class="Symbol">(</a><a id="20075" href="Agda.Primitive.html#408" class="Postulate">Level</a><a id="20080" class="Symbol">;</a> <a id="20082" href="Agda.Primitive.html#657" class="Primitive Operator">_⊔_</a><a id="20085" class="Symbol">)</a> <a id="20087" class="Keyword">renaming</a> <a id="20096" class="Symbol">(</a><a id="20097" href="Agda.Primitive.html#611" class="Primitive">zero</a> <a id="20102" class="Symbol">to</a> <a id="20105" href="Agda.Primitive.html#611" class="Primitive">lzero</a><a id="20110" class="Symbol">;</a> <a id="20112" href="Agda.Primitive.html#627" class="Primitive">suc</a> <a id="20116" class="Symbol">to</a> <a id="20119" href="Agda.Primitive.html#627" class="Primitive">lsuc</a><a id="20123" class="Symbol">)</a>{% endraw %}</pre>
We rename constructors `zero` and `suc` to `lzero` and `lsuc` to avoid confusion
between levels and naturals.

Levels are isomorphic to natural numbers, and have similar constructors:

    lzero : Level
    lsuc  : Level → Level

The names `Set₀`, `Set₁`, `Set₂`, and so on, are abbreviations for

    Set lzero
    Set (lsuc lzero)
    Set (lsuc (lsuc lzero))

and so on. There is also an operator

    _⊔_ : Level → Level → Level

that given two levels returns the larger of the two.

Here is the definition of equality, generalised to an arbitrary level:
<pre class="Agda">{% raw %}<a id="20707" class="Keyword">data</a> <a id="_≡′_"></a><a id="20712" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20712" class="Datatype Operator">_≡′_</a> <a id="20717" class="Symbol">{</a><a id="20718" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20718" class="Bound">ℓ</a> <a id="20720" class="Symbol">:</a> <a id="20722" href="Agda.Primitive.html#408" class="Postulate">Level</a><a id="20727" class="Symbol">}</a> <a id="20729" class="Symbol">{</a><a id="20730" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20730" class="Bound">A</a> <a id="20732" class="Symbol">:</a> <a id="20734" class="PrimitiveType">Set</a> <a id="20738" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20718" class="Bound">ℓ</a><a id="20739" class="Symbol">}</a> <a id="20741" class="Symbol">(</a><a id="20742" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20742" class="Bound">x</a> <a id="20744" class="Symbol">:</a> <a id="20746" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20730" class="Bound">A</a><a id="20747" class="Symbol">)</a> <a id="20749" class="Symbol">:</a> <a id="20751" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20730" class="Bound">A</a> <a id="20753" class="Symbol">→</a> <a id="20755" class="PrimitiveType">Set</a> <a id="20759" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20718" class="Bound">ℓ</a> <a id="20761" class="Keyword">where</a>
  <a id="_≡′_.refl′"></a><a id="20769" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20769" class="InductiveConstructor">refl′</a> <a id="20775" class="Symbol">:</a> <a id="20777" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20742" class="Bound">x</a> <a id="20779" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20712" class="Datatype Operator">≡′</a> <a id="20782" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20742" class="Bound">x</a>{% endraw %}</pre>
Similarly, here is the generalised definition of symmetry:
<pre class="Agda">{% raw %}<a id="sym′"></a><a id="20867" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20867" class="Function">sym′</a> <a id="20872" class="Symbol">:</a> <a id="20874" class="Symbol">∀</a> <a id="20876" class="Symbol">{</a><a id="20877" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20877" class="Bound">ℓ</a> <a id="20879" class="Symbol">:</a> <a id="20881" href="Agda.Primitive.html#408" class="Postulate">Level</a><a id="20886" class="Symbol">}</a> <a id="20888" class="Symbol">{</a><a id="20889" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20889" class="Bound">A</a> <a id="20891" class="Symbol">:</a> <a id="20893" class="PrimitiveType">Set</a> <a id="20897" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20877" class="Bound">ℓ</a><a id="20898" class="Symbol">}</a> <a id="20900" class="Symbol">{</a><a id="20901" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20901" class="Bound">x</a> <a id="20903" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20903" class="Bound">y</a> <a id="20905" class="Symbol">:</a> <a id="20907" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20889" class="Bound">A</a><a id="20908" class="Symbol">}</a>
  <a id="20912" class="Symbol">→</a> <a id="20914" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20901" class="Bound">x</a> <a id="20916" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20712" class="Datatype Operator">≡′</a> <a id="20919" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20903" class="Bound">y</a>
    <a id="20925" class="Comment">------</a>
  <a id="20934" class="Symbol">→</a> <a id="20936" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20903" class="Bound">y</a> <a id="20938" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20712" class="Datatype Operator">≡′</a> <a id="20941" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20901" class="Bound">x</a>
<a id="20943" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20867" class="Function">sym′</a> <a id="20948" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20769" class="InductiveConstructor">refl′</a> <a id="20954" class="Symbol">=</a> <a id="20956" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#20769" class="InductiveConstructor">refl′</a>{% endraw %}</pre>
For simplicity, we avoid universe polymorphism in the definitions given in
the text, but most definitions in the standard library, including those for
equality, are generalised to arbitrary levels as above.

Here is the generalised definition of Leibniz equality:
<pre class="Agda">{% raw %}<a id="_≐′_"></a><a id="21250" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21250" class="Function Operator">_≐′_</a> <a id="21255" class="Symbol">:</a> <a id="21257" class="Symbol">∀</a> <a id="21259" class="Symbol">{</a><a id="21260" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21260" class="Bound">ℓ</a> <a id="21262" class="Symbol">:</a> <a id="21264" href="Agda.Primitive.html#408" class="Postulate">Level</a><a id="21269" class="Symbol">}</a> <a id="21271" class="Symbol">{</a><a id="21272" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21272" class="Bound">A</a> <a id="21274" class="Symbol">:</a> <a id="21276" class="PrimitiveType">Set</a> <a id="21280" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21260" class="Bound">ℓ</a><a id="21281" class="Symbol">}</a> <a id="21283" class="Symbol">(</a><a id="21284" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21284" class="Bound">x</a> <a id="21286" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21286" class="Bound">y</a> <a id="21288" class="Symbol">:</a> <a id="21290" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21272" class="Bound">A</a><a id="21291" class="Symbol">)</a> <a id="21293" class="Symbol">→</a> <a id="21295" class="PrimitiveType">Set</a> <a id="21299" class="Symbol">(</a><a id="21300" href="Agda.Primitive.html#627" class="Primitive">lsuc</a> <a id="21305" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21260" class="Bound">ℓ</a><a id="21306" class="Symbol">)</a>
<a id="21308" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21250" class="Function Operator">_≐′_</a> <a id="21313" class="Symbol">{</a><a id="21314" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21314" class="Bound">ℓ</a><a id="21315" class="Symbol">}</a> <a id="21317" class="Symbol">{</a><a id="21318" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21318" class="Bound">A</a><a id="21319" class="Symbol">}</a> <a id="21321" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21321" class="Bound">x</a> <a id="21323" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21323" class="Bound">y</a> <a id="21325" class="Symbol">=</a> <a id="21327" class="Symbol">∀</a> <a id="21329" class="Symbol">(</a><a id="21330" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21330" class="Bound">P</a> <a id="21332" class="Symbol">:</a> <a id="21334" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21318" class="Bound">A</a> <a id="21336" class="Symbol">→</a> <a id="21338" class="PrimitiveType">Set</a> <a id="21342" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21314" class="Bound">ℓ</a><a id="21343" class="Symbol">)</a> <a id="21345" class="Symbol">→</a> <a id="21347" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21330" class="Bound">P</a> <a id="21349" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21321" class="Bound">x</a> <a id="21351" class="Symbol">→</a> <a id="21353" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21330" class="Bound">P</a> <a id="21355" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21323" class="Bound">y</a>{% endraw %}</pre>
Before the signature used `Set₁` as the type of a term that includes
`Set`, whereas here the signature uses `Set (lsuc ℓ)` as the type of a
term that includes `Set ℓ`.

Further information on levels can be found in the [Agda Wiki][wiki].

[wiki]: http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.UniversePolymorphism


## Standard library

Definitions similar to those in this chapter can be found in the
standard library:
<pre class="Agda">{% raw %}<a id="21820" class="Comment">-- import Relation.Binary.PropositionalEquality as Eq</a>
<a id="21874" class="Comment">-- open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)</a>
<a id="21938" class="Comment">-- open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)</a>{% endraw %}</pre>
Here the imports are shown as comments rather than code to avoid
collisions, as mentioned in the introduction.


## Unicode

This chapter uses the following unicode:

    ≡  U+2261  IDENTICAL TO (\==, \equiv)
    ⟨  U+27E8  MATHEMATICAL LEFT ANGLE BRACKET (\<)
    ⟩  U+27E9  MATHEMATICAL RIGHT ANGLE BRACKET (\>)
    ∎  U+220E  END OF PROOF (\qed)
    ≐  U+2250  APPROACHES THE LIMIT (\.=)
    ℓ  U+2113  SCRIPT SMALL L (\ell)
    ⊔  U+2294  SQUARE CUP (\lub)
    ₀  U+2080  SUBSCRIPT ZERO (\_0)
    ₁  U+2081  SUBSCRIPT ONE (\_1)
    ₂  U+2082  SUBSCRIPT TWO (\_2)
