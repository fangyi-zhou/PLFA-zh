---
src       : src/plfa/Relations.lagda
title     : "Relations: Inductive definition of relations"
layout    : page
prev      : /Induction/
permalink : /Relations/
next      : /Equality/
---

<pre class="Agda">{% raw %}<a id="170" class="Keyword">module</a> <a id="177" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}" class="Module">plfa.Relations</a> <a id="192" class="Keyword">where</a>{% endraw %}</pre>

After having defined operations such as addition and multiplication,
the next step is to define relations, such as _less than or equal_.

## Imports

<pre class="Agda">{% raw %}<a id="373" class="Keyword">import</a> <a id="380" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="418" class="Symbol">as</a> <a id="421" class="Module">Eq</a>
<a id="424" class="Keyword">open</a> <a id="429" href="Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="432" class="Keyword">using</a> <a id="438" class="Symbol">(</a><a id="439" href="Agda.Builtin.Equality.html#83" class="Datatype Operator">_≡_</a><a id="442" class="Symbol">;</a> <a id="444" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="448" class="Symbol">;</a> <a id="450" href="Relation.Binary.PropositionalEquality.html#1170" class="Function">cong</a><a id="454" class="Symbol">;</a> <a id="456" href="Relation.Binary.PropositionalEquality.Core.html#838" class="Function">sym</a><a id="459" class="Symbol">)</a>
<a id="461" class="Keyword">open</a> <a id="466" class="Keyword">import</a> <a id="473" href="Data.Nat.html" class="Module">Data.Nat</a> <a id="482" class="Keyword">using</a> <a id="488" class="Symbol">(</a><a id="489" href="Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="490" class="Symbol">;</a> <a id="492" href="Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="496" class="Symbol">;</a> <a id="498" href="Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a><a id="501" class="Symbol">;</a> <a id="503" href="Agda.Builtin.Nat.html#230" class="Primitive Operator">_+_</a><a id="506" class="Symbol">;</a> <a id="508" href="Agda.Builtin.Nat.html#433" class="Primitive Operator">_*_</a><a id="511" class="Symbol">;</a> <a id="513" href="Agda.Builtin.Nat.html#320" class="Primitive Operator">_∸_</a><a id="516" class="Symbol">)</a>
<a id="518" class="Keyword">open</a> <a id="523" class="Keyword">import</a> <a id="530" href="Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="550" class="Keyword">using</a> <a id="556" class="Symbol">(</a><a id="557" href="Data.Nat.Properties.html#9708" class="Function">+-comm</a><a id="563" class="Symbol">;</a> <a id="565" href="Data.Nat.Properties.html#9272" class="Function">+-suc</a><a id="570" class="Symbol">)</a>
<a id="572" class="Keyword">open</a> <a id="577" class="Keyword">import</a> <a id="584" href="Data.List.html" class="Module">Data.List</a> <a id="594" class="Keyword">using</a> <a id="600" class="Symbol">(</a><a id="601" href="Agda.Builtin.List.html#80" class="Datatype">List</a><a id="605" class="Symbol">;</a> <a id="607" href="Data.List.Base.html#8785" class="InductiveConstructor">[]</a><a id="609" class="Symbol">;</a> <a id="611" href="Agda.Builtin.List.html#132" class="InductiveConstructor Operator">_∷_</a><a id="614" class="Symbol">)</a>
<a id="616" class="Keyword">open</a> <a id="621" class="Keyword">import</a> <a id="628" href="Function.html" class="Module">Function</a> <a id="637" class="Keyword">using</a> <a id="643" class="Symbol">(</a><a id="644" href="Function.html#1068" class="Function">id</a><a id="646" class="Symbol">;</a> <a id="648" href="Function.html#769" class="Function Operator">_∘_</a><a id="651" class="Symbol">)</a>
<a id="653" class="Keyword">open</a> <a id="658" class="Keyword">import</a> <a id="665" href="Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="682" class="Keyword">using</a> <a id="688" class="Symbol">(</a><a id="689" href="Relation.Nullary.html#464" class="Function Operator">¬_</a><a id="691" class="Symbol">)</a>
<a id="693" class="Keyword">open</a> <a id="698" class="Keyword">import</a> <a id="705" href="Data.Empty.html" class="Module">Data.Empty</a> <a id="716" class="Keyword">using</a> <a id="722" class="Symbol">(</a><a id="723" href="Data.Empty.html#243" class="Datatype">⊥</a><a id="724" class="Symbol">;</a> <a id="726" href="Data.Empty.html#360" class="Function">⊥-elim</a><a id="732" class="Symbol">)</a>{% endraw %}</pre>


## Defining relations

The relation _less than or equal_ has an infinite number of
instances.  Here are a few of them:

    0 ≤ 0     0 ≤ 1     0 ≤ 2     0 ≤ 3     ...
              1 ≤ 1     1 ≤ 2     1 ≤ 3     ...
                        2 ≤ 2     2 ≤ 3     ...
                                  3 ≤ 3     ...
                                            ...

And yet, we can write a finite definition that encompasses
all of these instances in just a few lines.  Here is the
definition as a pair of inference rules:

    z≤n --------
        zero ≤ n

        m ≤ n
    s≤s -------------
        suc m ≤ suc n

And here is the definition in Agda:
<pre class="Agda">{% raw %}<a id="1409" class="Keyword">data</a> <a id="_≤_"></a><a id="1414" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">_≤_</a> <a id="1418" class="Symbol">:</a> <a id="1420" href="Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="1422" class="Symbol">→</a> <a id="1424" href="Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="1426" class="Symbol">→</a> <a id="1428" class="PrimitiveType">Set</a> <a id="1432" class="Keyword">where</a>

  <a id="_≤_.z≤n"></a><a id="1441" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1441" class="InductiveConstructor">z≤n</a> <a id="1445" class="Symbol">:</a> <a id="1447" class="Symbol">∀</a> <a id="1449" class="Symbol">{</a><a id="1450" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1450" class="Bound">n</a> <a id="1452" class="Symbol">:</a> <a id="1454" href="Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="1455" class="Symbol">}</a>
      <a id="1463" class="Comment">--------</a>
    <a id="1476" class="Symbol">→</a> <a id="1478" href="Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="1483" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="1485" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1450" class="Bound">n</a>

  <a id="_≤_.s≤s"></a><a id="1490" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="1494" class="Symbol">:</a> <a id="1496" class="Symbol">∀</a> <a id="1498" class="Symbol">{</a><a id="1499" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1499" class="Bound">m</a> <a id="1501" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1501" class="Bound">n</a> <a id="1503" class="Symbol">:</a> <a id="1505" href="Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="1506" class="Symbol">}</a>
    <a id="1512" class="Symbol">→</a> <a id="1514" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1499" class="Bound">m</a> <a id="1516" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="1518" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1501" class="Bound">n</a>
      <a id="1526" class="Comment">-------------</a>
    <a id="1544" class="Symbol">→</a> <a id="1546" href="Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="1550" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1499" class="Bound">m</a> <a id="1552" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="1554" href="Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="1558" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1501" class="Bound">n</a>{% endraw %}</pre>
Here `z≤n` and `s≤s` (with no spaces) are constructor names, while
`zero ≤ n`, and `m ≤ n` and `suc m ≤ suc n` (with spaces) are types.
This is our first use of an _indexed_ datatype, where the type `m ≤ n`
is indexed by two naturals, `m` and `n`.  In Agda any line beginning
with two or more dashes is a comment, and here we have exploited that
convention to write our Agda code in a form that resembles the
corresponding inference rules, a trick we will use often from now on.

Both definitions above tell us the same two things:

* _Base case_: for all naturals `n`, the proposition `zero ≤ n` holds.
* _Inductive case_: for all naturals `m` and `n`, if the proposition
  `m ≤ n` holds, then the proposition `suc m ≤ suc n` holds.

In fact, they each give us a bit more detail:

* _Base case_: for all naturals `n`, the constructor `z≤n`
  produces evidence that `zero ≤ n` holds.
* _Inductive case_: for all naturals `m` and `n`, the constructor
  `s≤s` takes evidence that `m ≤ n` holds into evidence that
  `suc m ≤ suc n` holds.

For example, here in inference rule notation is the proof that
`2 ≤ 4`:

      z≤n -----
          0 ≤ 2
     s≤s -------
          1 ≤ 3
    s≤s ---------
          2 ≤ 4

And here is the corresponding Agda proof:
<pre class="Agda">{% raw %}<a id="2836" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#2836" class="Function">_</a> <a id="2838" class="Symbol">:</a> <a id="2840" class="Number">2</a> <a id="2842" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="2844" class="Number">4</a>
<a id="2846" class="Symbol">_</a> <a id="2848" class="Symbol">=</a> <a id="2850" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="2854" class="Symbol">(</a><a id="2855" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="2859" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1441" class="InductiveConstructor">z≤n</a><a id="2862" class="Symbol">)</a>{% endraw %}</pre>




## Implicit arguments

This is our first use of implicit arguments.  In the definition of
inequality, the two lines defining the constructors use `∀`, very
similar to our use of `∀` in propositions such as:

    +-comm : ∀ (m n : ℕ) → m + n ≡ n + m

However, here the declarations are surrounded by curly braces `{ }`
rather than parentheses `( )`.  This means that the arguments are
_implicit_ and need not be written explicitly; instead, they are
_inferred_ by Agda's typechecker. Thus, we write `+-comm m n` for the
proof that `m + n ≡ n + m`, but `z≤n` for the proof that `zero ≤ n`,
leaving `n` implicit.  Similarly, if `m≤n` is evidence that `m ≤ n`,
we write `s≤s m≤n` for evidence that `suc m ≤ suc n`, leaving both `m`
and `n` implicit.

If we wish, it is possible to provide implicit arguments explicitly by
writing the arguments inside curly braces.  For instance, here is the
Agda proof that `2 ≤ 4` repeated, with the implicit arguments made
explicit:
<pre class="Agda">{% raw %}<a id="3857" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#3857" class="Function">_</a> <a id="3859" class="Symbol">:</a> <a id="3861" class="Number">2</a> <a id="3863" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="3865" class="Number">4</a>
<a id="3867" class="Symbol">_</a> <a id="3869" class="Symbol">=</a> <a id="3871" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="3875" class="Symbol">{</a><a id="3876" class="Number">1</a><a id="3877" class="Symbol">}</a> <a id="3879" class="Symbol">{</a><a id="3880" class="Number">3</a><a id="3881" class="Symbol">}</a> <a id="3883" class="Symbol">(</a><a id="3884" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="3888" class="Symbol">{</a><a id="3889" class="Number">0</a><a id="3890" class="Symbol">}</a> <a id="3892" class="Symbol">{</a><a id="3893" class="Number">2</a><a id="3894" class="Symbol">}</a> <a id="3896" class="Symbol">(</a><a id="3897" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1441" class="InductiveConstructor">z≤n</a> <a id="3901" class="Symbol">{</a><a id="3902" class="Number">2</a><a id="3903" class="Symbol">}))</a>{% endraw %}</pre>
One may also identify implicit arguments by name:
<pre class="Agda">{% raw %}<a id="3981" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#3981" class="Function">_</a> <a id="3983" class="Symbol">:</a> <a id="3985" class="Number">2</a> <a id="3987" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="3989" class="Number">4</a>
<a id="3991" class="Symbol">_</a> <a id="3993" class="Symbol">=</a> <a id="3995" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="3999" class="Symbol">{</a><a id="4000" class="Argument">m</a> <a id="4002" class="Symbol">=</a> <a id="4004" class="Number">1</a><a id="4005" class="Symbol">}</a> <a id="4007" class="Symbol">{</a><a id="4008" class="Argument">n</a> <a id="4010" class="Symbol">=</a> <a id="4012" class="Number">3</a><a id="4013" class="Symbol">}</a> <a id="4015" class="Symbol">(</a><a id="4016" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="4020" class="Symbol">{</a><a id="4021" class="Argument">m</a> <a id="4023" class="Symbol">=</a> <a id="4025" class="Number">0</a><a id="4026" class="Symbol">}</a> <a id="4028" class="Symbol">{</a><a id="4029" class="Argument">n</a> <a id="4031" class="Symbol">=</a> <a id="4033" class="Number">2</a><a id="4034" class="Symbol">}</a> <a id="4036" class="Symbol">(</a><a id="4037" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1441" class="InductiveConstructor">z≤n</a> <a id="4041" class="Symbol">{</a><a id="4042" class="Argument">n</a> <a id="4044" class="Symbol">=</a> <a id="4046" class="Number">2</a><a id="4047" class="Symbol">}))</a>{% endraw %}</pre>
In the latter format, you may only supply some implicit arguments:
<pre class="Agda">{% raw %}<a id="4142" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#4142" class="Function">_</a> <a id="4144" class="Symbol">:</a> <a id="4146" class="Number">2</a> <a id="4148" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="4150" class="Number">4</a>
<a id="4152" class="Symbol">_</a> <a id="4154" class="Symbol">=</a> <a id="4156" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="4160" class="Symbol">{</a><a id="4161" class="Argument">n</a> <a id="4163" class="Symbol">=</a> <a id="4165" class="Number">3</a><a id="4166" class="Symbol">}</a> <a id="4168" class="Symbol">(</a><a id="4169" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="4173" class="Symbol">{</a><a id="4174" class="Argument">n</a> <a id="4176" class="Symbol">=</a> <a id="4178" class="Number">2</a><a id="4179" class="Symbol">}</a> <a id="4181" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1441" class="InductiveConstructor">z≤n</a><a id="4184" class="Symbol">)</a>{% endraw %}</pre>
It is not permitted to swap implicit arguments, even when named.


## Precedence

We declare the precedence for comparison as follows:
<pre class="Agda">{% raw %}<a id="4345" class="Keyword">infix</a> <a id="4351" class="Number">4</a> <a id="4353" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">_≤_</a>{% endraw %}</pre>
We set the precedence of `_≤_` at level 4, so it binds less tightly
that `_+_` at level 6 and hence `1 + 2 ≤ 3` parses as `(1 + 2) ≤ 3`.
We write `infix` to indicate that the operator does not associate to
either the left or right, as it makes no sense to parse `1 ≤ 2 ≤ 3` as
either `(1 ≤ 2) ≤ 3` or `1 ≤ (2 ≤ 3)`.


## Decidability

Given two numbers, it is straightforward to compute whether or not the
first is less than or equal to the second.  We don't give the code for
doing so here, but will return to this point in
Chapter [Decidable]({{ site.baseurl }}{% link out/plfa/Decidable.md%}).


## Properties of ordering relations

Relations pop up all the time, and mathematicians have agreed
on names for some of the most common properties.

* _Reflexive_. For all `n`, the relation `n ≤ n` holds.
* _Transitive_. For all `m`, `n`, and `p`, if `m ≤ n` and
`n ≤ p` hold, then `m ≤ p` holds.
* _Anti-symmetric_. For all `m` and `n`, if both `m ≤ n` and
`n ≤ m` hold, then `m ≡ n` holds.
* _Total_. For all `m` and `n`, either `m ≤ n` or `n ≤ m`
holds.

The relation `_≤_` satisfies all four of these properties.

There are also names for some combinations of these properties.

* _Preorder_. Any relation that is reflexive and transitive.
* _Partial order_. Any preorder that is also anti-symmetric.
* _Total order_. Any partial order that is also total.

If you ever bump into a relation at a party, you now know how
to make small talk, by asking it whether it is reflexive, transitive,
anti-symmetric, and total. Or instead you might ask whether it is a
preorder, partial order, or total order.

Less frivolously, if you ever bump into a relation while reading a
technical paper, this gives you a way to orient yourself, by checking
whether or not it is a preorder, partial order, or total order.  A
careful author will often call out these properties---or their
lack---for instance by saying that a newly introduced relation is a
partial order but not a total order.


#### Exercise `orderings` {#orderings}

Give an example of a preorder that is not a partial order.

<pre class="Agda">{% raw %}<a id="6422" class="Comment">-- Your code goes here</a>{% endraw %}</pre>

Give an example of a partial order that is not a total order.

<pre class="Agda">{% raw %}<a id="6533" class="Comment">-- Your code goes here</a>{% endraw %}</pre>

## Reflexivity

The first property to prove about comparison is that it is reflexive:
for any natural `n`, the relation `n ≤ n` holds.  We follow the
convention in the standard library and make the argument implicit,
as that will make it easier to invoke reflexivity:
<pre class="Agda">{% raw %}<a id="≤-refl"></a><a id="6849" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6849" class="Function">≤-refl</a> <a id="6856" class="Symbol">:</a> <a id="6858" class="Symbol">∀</a> <a id="6860" class="Symbol">{</a><a id="6861" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6861" class="Bound">n</a> <a id="6863" class="Symbol">:</a> <a id="6865" href="Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="6866" class="Symbol">}</a>
    <a id="6872" class="Comment">-----</a>
  <a id="6880" class="Symbol">→</a> <a id="6882" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6861" class="Bound">n</a> <a id="6884" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="6886" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6861" class="Bound">n</a>
<a id="6888" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6849" class="Function">≤-refl</a> <a id="6895" class="Symbol">{</a><a id="6896" href="Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="6900" class="Symbol">}</a>   <a id="6904" class="Symbol">=</a>  <a id="6907" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1441" class="InductiveConstructor">z≤n</a>
<a id="6911" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6849" class="Function">≤-refl</a> <a id="6918" class="Symbol">{</a><a id="6919" href="Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="6923" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6923" class="Bound">n</a><a id="6924" class="Symbol">}</a>  <a id="6927" class="Symbol">=</a>  <a id="6930" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="6934" class="Symbol">(</a><a id="6935" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6849" class="Function">≤-refl</a> <a id="6942" class="Symbol">{</a><a id="6943" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#6923" class="Bound">n</a><a id="6944" class="Symbol">})</a>{% endraw %}</pre>
The proof is a straightforward induction on the implicit argument `n`.
In the base case, `zero ≤ zero` holds by `z≤n`.  In the inductive
case, the inductive hypothesis `≤-refl {n}` gives us a proof of `n ≤
n`, and applying `s≤s` to that yields a proof of `suc n ≤ suc n`.

It is a good exercise to prove reflexivity interactively in Emacs,
using holes and the `C-c C-c`, `C-c C-,`, and `C-c C-r` commands.


## Transitivity

The second property to prove about comparison is that it is
transitive: for any naturals `m`, `n`, and `p`, if `m ≤ n` and `n ≤ p`
hold, then `m ≤ p` holds.  Again, `m`, `n`, and `p` are implicit:
<pre class="Agda">{% raw %}<a id="≤-trans"></a><a id="7593" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7593" class="Function">≤-trans</a> <a id="7601" class="Symbol">:</a> <a id="7603" class="Symbol">∀</a> <a id="7605" class="Symbol">{</a><a id="7606" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7606" class="Bound">m</a> <a id="7608" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7608" class="Bound">n</a> <a id="7610" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7610" class="Bound">p</a> <a id="7612" class="Symbol">:</a> <a id="7614" href="Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="7615" class="Symbol">}</a>
  <a id="7619" class="Symbol">→</a> <a id="7621" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7606" class="Bound">m</a> <a id="7623" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="7625" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7608" class="Bound">n</a>
  <a id="7629" class="Symbol">→</a> <a id="7631" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7608" class="Bound">n</a> <a id="7633" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="7635" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7610" class="Bound">p</a>
    <a id="7641" class="Comment">-----</a>
  <a id="7649" class="Symbol">→</a> <a id="7651" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7606" class="Bound">m</a> <a id="7653" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="7655" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7610" class="Bound">p</a>
<a id="7657" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7593" class="Function">≤-trans</a> <a id="7665" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1441" class="InductiveConstructor">z≤n</a>       <a id="7675" class="Symbol">_</a>          <a id="7686" class="Symbol">=</a>  <a id="7689" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1441" class="InductiveConstructor">z≤n</a>
<a id="7693" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7593" class="Function">≤-trans</a> <a id="7701" class="Symbol">(</a><a id="7702" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="7706" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7706" class="Bound">m≤n</a><a id="7709" class="Symbol">)</a> <a id="7711" class="Symbol">(</a><a id="7712" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="7716" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7716" class="Bound">n≤p</a><a id="7719" class="Symbol">)</a>  <a id="7722" class="Symbol">=</a>  <a id="7725" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="7729" class="Symbol">(</a><a id="7730" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7593" class="Function">≤-trans</a> <a id="7738" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7706" class="Bound">m≤n</a> <a id="7742" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7716" class="Bound">n≤p</a><a id="7745" class="Symbol">)</a>{% endraw %}</pre>
Here the proof is by induction on the _evidence_ that `m ≤ n`.  In the
base case, the first inequality holds by `z≤n` and must show `zero ≤
p`, which follows immediately by `z≤n`.  In this case, the fact that
`n ≤ p` is irrelevant, and we write `_` as the pattern to indicate
that the corresponding evidence is unused.

In the inductive case, the first inequality holds by `s≤s m≤n`
and the second inequality by `s≤s n≤p`, and so we are given
`suc m ≤ suc n` and `suc n ≤ suc p`, and must show `suc m ≤ suc p`.
The inductive hypothesis `≤-trans m≤n n≤p` establishes
that `m ≤ p`, and our goal follows by applying `s≤s`.

The case `≤-trans (s≤s m≤n) z≤n` cannot arise, since the first
inequality implies the middle value is `suc n` while the second
inequality implies that it is `zero`.  Agda can determine that such a
case cannot arise, and does not require (or permit) it to be listed.

Alternatively, we could make the implicit parameters explicit:
<pre class="Agda">{% raw %}<a id="≤-trans′"></a><a id="8722" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8722" class="Function">≤-trans′</a> <a id="8731" class="Symbol">:</a> <a id="8733" class="Symbol">∀</a> <a id="8735" class="Symbol">(</a><a id="8736" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8736" class="Bound">m</a> <a id="8738" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8738" class="Bound">n</a> <a id="8740" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8740" class="Bound">p</a> <a id="8742" class="Symbol">:</a> <a id="8744" href="Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="8745" class="Symbol">)</a>
  <a id="8749" class="Symbol">→</a> <a id="8751" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8736" class="Bound">m</a> <a id="8753" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="8755" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8738" class="Bound">n</a>
  <a id="8759" class="Symbol">→</a> <a id="8761" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8738" class="Bound">n</a> <a id="8763" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="8765" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8740" class="Bound">p</a>
    <a id="8771" class="Comment">-----</a>
  <a id="8779" class="Symbol">→</a> <a id="8781" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8736" class="Bound">m</a> <a id="8783" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="8785" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8740" class="Bound">p</a>
<a id="8787" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8722" class="Function">≤-trans′</a> <a id="8796" href="Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="8804" class="Symbol">_</a>       <a id="8812" class="Symbol">_</a>       <a id="8820" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1441" class="InductiveConstructor">z≤n</a>       <a id="8830" class="Symbol">_</a>          <a id="8841" class="Symbol">=</a>  <a id="8844" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1441" class="InductiveConstructor">z≤n</a>
<a id="8848" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8722" class="Function">≤-trans′</a> <a id="8857" class="Symbol">(</a><a id="8858" href="Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="8862" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8862" class="Bound">m</a><a id="8863" class="Symbol">)</a> <a id="8865" class="Symbol">(</a><a id="8866" href="Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="8870" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8870" class="Bound">n</a><a id="8871" class="Symbol">)</a> <a id="8873" class="Symbol">(</a><a id="8874" href="Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="8878" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8878" class="Bound">p</a><a id="8879" class="Symbol">)</a> <a id="8881" class="Symbol">(</a><a id="8882" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="8886" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8886" class="Bound">m≤n</a><a id="8889" class="Symbol">)</a> <a id="8891" class="Symbol">(</a><a id="8892" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="8896" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8896" class="Bound">n≤p</a><a id="8899" class="Symbol">)</a>  <a id="8902" class="Symbol">=</a>  <a id="8905" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="8909" class="Symbol">(</a><a id="8910" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8722" class="Function">≤-trans′</a> <a id="8919" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8862" class="Bound">m</a> <a id="8921" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8870" class="Bound">n</a> <a id="8923" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8878" class="Bound">p</a> <a id="8925" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8886" class="Bound">m≤n</a> <a id="8929" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8896" class="Bound">n≤p</a><a id="8932" class="Symbol">)</a>{% endraw %}</pre>
One might argue that this is clearer or one might argue that the extra
length obscures the essence of the proof.  We will usually opt for
shorter proofs.

The technique of induction on evidence that a property holds (e.g.,
inducting on evidence that `m ≤ n`)---rather than induction on 
values of which the property holds (e.g., inducting on `m`)---will turn
out to be immensely valuable, and one that we use often.

Again, it is a good exercise to prove transitivity interactively in Emacs,
using holes and the `C-c C-c`, `C-c C-,`, and `C-c C-r` commands.


## Anti-symmetry

The third property to prove about comparison is that it is
antisymmetric: for all naturals `m` and `n`, if both `m ≤ n` and `n ≤
m` hold, then `m ≡ n` holds:
<pre class="Agda">{% raw %}<a id="≤-antisym"></a><a id="9694" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9694" class="Function">≤-antisym</a> <a id="9704" class="Symbol">:</a> <a id="9706" class="Symbol">∀</a> <a id="9708" class="Symbol">{</a><a id="9709" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9709" class="Bound">m</a> <a id="9711" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9711" class="Bound">n</a> <a id="9713" class="Symbol">:</a> <a id="9715" href="Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="9716" class="Symbol">}</a>
  <a id="9720" class="Symbol">→</a> <a id="9722" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9709" class="Bound">m</a> <a id="9724" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="9726" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9711" class="Bound">n</a>
  <a id="9730" class="Symbol">→</a> <a id="9732" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9711" class="Bound">n</a> <a id="9734" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="9736" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9709" class="Bound">m</a>
    <a id="9742" class="Comment">-----</a>
  <a id="9750" class="Symbol">→</a> <a id="9752" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9709" class="Bound">m</a> <a id="9754" href="Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="9756" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9711" class="Bound">n</a>
<a id="9758" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9694" class="Function">≤-antisym</a> <a id="9768" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1441" class="InductiveConstructor">z≤n</a>       <a id="9778" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1441" class="InductiveConstructor">z≤n</a>        <a id="9789" class="Symbol">=</a>  <a id="9792" href="Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
<a id="9797" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9694" class="Function">≤-antisym</a> <a id="9807" class="Symbol">(</a><a id="9808" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="9812" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9812" class="Bound">m≤n</a><a id="9815" class="Symbol">)</a> <a id="9817" class="Symbol">(</a><a id="9818" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="9822" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9822" class="Bound">n≤m</a><a id="9825" class="Symbol">)</a>  <a id="9828" class="Symbol">=</a>  <a id="9831" href="Relation.Binary.PropositionalEquality.html#1170" class="Function">cong</a> <a id="9836" href="Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="9840" class="Symbol">(</a><a id="9841" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9694" class="Function">≤-antisym</a> <a id="9851" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9812" class="Bound">m≤n</a> <a id="9855" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9822" class="Bound">n≤m</a><a id="9858" class="Symbol">)</a>{% endraw %}</pre>
Again, the proof is by induction over the evidence that `m ≤ n`
and `n ≤ m` hold.

In the base case, both inequalities hold by `z≤n`, and so we are given
`zero ≤ zero` and `zero ≤ zero` and must show `zero ≡ zero`, which
follows by reflexivity.  (Reflexivity of equality, that is, not
reflexivity of inequality.)

In the inductive case, the first inequality holds by `s≤s m≤n` and the
second inequality holds by `s≤s n≤m`, and so we are given `suc m ≤ suc n`
and `suc n ≤ suc m` and must show `suc m ≡ suc n`.  The inductive
hypothesis `≤-antisym m≤n n≤m` establishes that `m ≡ n`, and our goal
follows by congruence.

#### Exercise `≤-antisym-cases` {#leq-antisym-cases} 

The above proof omits cases where one argument is `z≤n` and one
argument is `s≤s`.  Why is it ok to omit them?

<pre class="Agda">{% raw %}<a id="10670" class="Comment">-- Your code goes here</a>{% endraw %}</pre>


## Total

The fourth property to prove about comparison is that it is total:
for any naturals `m` and `n` either `m ≤ n` or `n ≤ m`, or both if
`m` and `n` are equal.

We specify what it means for inequality to be total:
<pre class="Agda">{% raw %}<a id="10940" class="Keyword">data</a> <a id="Total"></a><a id="10945" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10945" class="Datatype">Total</a> <a id="10951" class="Symbol">(</a><a id="10952" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10952" class="Bound">m</a> <a id="10954" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10954" class="Bound">n</a> <a id="10956" class="Symbol">:</a> <a id="10958" href="Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="10959" class="Symbol">)</a> <a id="10961" class="Symbol">:</a> <a id="10963" class="PrimitiveType">Set</a> <a id="10967" class="Keyword">where</a>

  <a id="Total.forward"></a><a id="10976" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10976" class="InductiveConstructor">forward</a> <a id="10984" class="Symbol">:</a>
      <a id="10992" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10952" class="Bound">m</a> <a id="10994" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="10996" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10954" class="Bound">n</a>
      <a id="11004" class="Comment">---------</a>
    <a id="11018" class="Symbol">→</a> <a id="11020" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10945" class="Datatype">Total</a> <a id="11026" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10952" class="Bound">m</a> <a id="11028" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10954" class="Bound">n</a>

  <a id="Total.flipped"></a><a id="11033" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11033" class="InductiveConstructor">flipped</a> <a id="11041" class="Symbol">:</a>
      <a id="11049" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10954" class="Bound">n</a> <a id="11051" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="11053" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10952" class="Bound">m</a>
      <a id="11061" class="Comment">---------</a>
    <a id="11075" class="Symbol">→</a> <a id="11077" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10945" class="Datatype">Total</a> <a id="11083" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10952" class="Bound">m</a> <a id="11085" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10954" class="Bound">n</a>{% endraw %}</pre>
Evidence that `Total m n` holds is either of the form
`forward m≤n` or `flipped n≤m`, where `m≤n` and `n≤m` are
evidence of `m ≤ n` and `n ≤ m` respectively.

(For those familiar with logic, the above definition
could also be written as a disjunction. Disjunctions will
be introduced in Chapter [Connectives]({{ site.baseurl }}{% link out/plfa/Connectives.md%}).)

This is our first use of a datatype with _parameters_,
in this case `m` and `n`.  It is equivalent to the following
indexed datatype:
<pre class="Agda">{% raw %}<a id="11575" class="Keyword">data</a> <a id="Total′"></a><a id="11580" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11580" class="Datatype">Total′</a> <a id="11587" class="Symbol">:</a> <a id="11589" href="Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="11591" class="Symbol">→</a> <a id="11593" href="Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="11595" class="Symbol">→</a> <a id="11597" class="PrimitiveType">Set</a> <a id="11601" class="Keyword">where</a>

  <a id="Total′.forward′"></a><a id="11610" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11610" class="InductiveConstructor">forward′</a> <a id="11619" class="Symbol">:</a> <a id="11621" class="Symbol">∀</a> <a id="11623" class="Symbol">{</a><a id="11624" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11624" class="Bound">m</a> <a id="11626" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11626" class="Bound">n</a> <a id="11628" class="Symbol">:</a> <a id="11630" href="Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="11631" class="Symbol">}</a>
    <a id="11637" class="Symbol">→</a> <a id="11639" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11624" class="Bound">m</a> <a id="11641" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="11643" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11626" class="Bound">n</a>
      <a id="11651" class="Comment">----------</a>
    <a id="11666" class="Symbol">→</a> <a id="11668" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11580" class="Datatype">Total′</a> <a id="11675" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11624" class="Bound">m</a> <a id="11677" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11626" class="Bound">n</a>

  <a id="Total′.flipped′"></a><a id="11682" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11682" class="InductiveConstructor">flipped′</a> <a id="11691" class="Symbol">:</a> <a id="11693" class="Symbol">∀</a> <a id="11695" class="Symbol">{</a><a id="11696" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11696" class="Bound">m</a> <a id="11698" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11698" class="Bound">n</a> <a id="11700" class="Symbol">:</a> <a id="11702" href="Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="11703" class="Symbol">}</a>
    <a id="11709" class="Symbol">→</a> <a id="11711" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11698" class="Bound">n</a> <a id="11713" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="11715" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11696" class="Bound">m</a>
      <a id="11723" class="Comment">----------</a>
    <a id="11738" class="Symbol">→</a> <a id="11740" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11580" class="Datatype">Total′</a> <a id="11747" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11696" class="Bound">m</a> <a id="11749" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11698" class="Bound">n</a>{% endraw %}</pre>
Each parameter of the type translates as an implicit parameter of each
constructor.  Unlike an indexed datatype, where the indexes can vary
(as in `zero ≤ n` and `suc m ≤ suc n`), in a parameterised datatype
the parameters must always be the same (as in `Total m n`).
Parameterised declarations are shorter, easier to read, and
occasionally aid Agda's termination checker, so we will use them in
preference to indexed types when possible.

With that preliminary out of the way, we specify and prove totality:
<pre class="Agda">{% raw %}<a id="≤-total"></a><a id="12284" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12284" class="Function">≤-total</a> <a id="12292" class="Symbol">:</a> <a id="12294" class="Symbol">∀</a> <a id="12296" class="Symbol">(</a><a id="12297" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12297" class="Bound">m</a> <a id="12299" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12299" class="Bound">n</a> <a id="12301" class="Symbol">:</a> <a id="12303" href="Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="12304" class="Symbol">)</a> <a id="12306" class="Symbol">→</a> <a id="12308" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10945" class="Datatype">Total</a> <a id="12314" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12297" class="Bound">m</a> <a id="12316" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12299" class="Bound">n</a>
<a id="12318" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12284" class="Function">≤-total</a> <a id="12326" href="Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="12334" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12334" class="Bound">n</a>                         <a id="12360" class="Symbol">=</a>  <a id="12363" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10976" class="InductiveConstructor">forward</a> <a id="12371" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1441" class="InductiveConstructor">z≤n</a>
<a id="12375" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12284" class="Function">≤-total</a> <a id="12383" class="Symbol">(</a><a id="12384" href="Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12388" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12388" class="Bound">m</a><a id="12389" class="Symbol">)</a> <a id="12391" href="Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>                      <a id="12417" class="Symbol">=</a>  <a id="12420" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11033" class="InductiveConstructor">flipped</a> <a id="12428" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1441" class="InductiveConstructor">z≤n</a>
<a id="12432" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12284" class="Function">≤-total</a> <a id="12440" class="Symbol">(</a><a id="12441" href="Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12445" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12445" class="Bound">m</a><a id="12446" class="Symbol">)</a> <a id="12448" class="Symbol">(</a><a id="12449" href="Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12453" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12453" class="Bound">n</a><a id="12454" class="Symbol">)</a> <a id="12456" class="Keyword">with</a> <a id="12461" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12284" class="Function">≤-total</a> <a id="12469" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12445" class="Bound">m</a> <a id="12471" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12453" class="Bound">n</a>
<a id="12473" class="Symbol">...</a>                        <a id="12500" class="Symbol">|</a> <a id="12502" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10976" class="InductiveConstructor">forward</a> <a id="12510" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12510" class="Bound">m≤n</a>  <a id="12515" class="Symbol">=</a>  <a id="12518" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10976" class="InductiveConstructor">forward</a> <a id="12526" class="Symbol">(</a><a id="12527" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="12531" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12510" class="Bound">m≤n</a><a id="12534" class="Symbol">)</a>
<a id="12536" class="Symbol">...</a>                        <a id="12563" class="Symbol">|</a> <a id="12565" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11033" class="InductiveConstructor">flipped</a> <a id="12573" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12573" class="Bound">n≤m</a>  <a id="12578" class="Symbol">=</a>  <a id="12581" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11033" class="InductiveConstructor">flipped</a> <a id="12589" class="Symbol">(</a><a id="12590" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="12594" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12573" class="Bound">n≤m</a><a id="12597" class="Symbol">)</a>{% endraw %}</pre>
In this case the proof is by induction over both the first
and second arguments.  We perform a case analysis:

* _First base case_: If the first argument is `zero` and the
  second argument is `n` then the forward case holds,
  with `z≤n` as evidence that `zero ≤ n`.

* _Second base case_: If the first argument is `suc m` and the
  second argument is `zero` then the flipped case holds, with
  `z≤n` as evidence that `zero ≤ suc m`.

* _Inductive case_: If the first argument is `suc m` and the
  second argument is `suc n`, then the inductive hypothesis
  `≤-total m n` establishes one of the following:

  + The forward case of the inductive hypothesis holds with `m≤n` as
    evidence that `m ≤ n`, from which it follows that the forward case of the
    proposition holds with `s≤s m≤n` as evidence that `suc m ≤ suc n`.

  + The flipped case of the inductive hypothesis holds with `n≤m` as
    evidence that `n ≤ m`, from which it follows that the flipped case of the
    proposition holds with `s≤s n≤m` as evidence that `suc n ≤ suc m`.

This is our first use of the `with` clause in Agda.  The keyword
`with` is followed by an expression and one or more subsequent lines.
Each line begins with an ellipsis (`...`) and a vertical bar (`|`),
followed by a pattern to be matched against the expression
and the right-hand side of the equation.

Every use of `with` is equivalent to defining a helper function.  For
example, the definition above is equivalent to the following:
<pre class="Agda">{% raw %}<a id="≤-total′"></a><a id="14105" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14105" class="Function">≤-total′</a> <a id="14114" class="Symbol">:</a> <a id="14116" class="Symbol">∀</a> <a id="14118" class="Symbol">(</a><a id="14119" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14119" class="Bound">m</a> <a id="14121" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14121" class="Bound">n</a> <a id="14123" class="Symbol">:</a> <a id="14125" href="Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="14126" class="Symbol">)</a> <a id="14128" class="Symbol">→</a> <a id="14130" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10945" class="Datatype">Total</a> <a id="14136" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14119" class="Bound">m</a> <a id="14138" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14121" class="Bound">n</a>
<a id="14140" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14105" class="Function">≤-total′</a> <a id="14149" href="Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="14157" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14157" class="Bound">n</a>        <a id="14166" class="Symbol">=</a>  <a id="14169" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10976" class="InductiveConstructor">forward</a> <a id="14177" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1441" class="InductiveConstructor">z≤n</a>
<a id="14181" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14105" class="Function">≤-total′</a> <a id="14190" class="Symbol">(</a><a id="14191" href="Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14195" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14195" class="Bound">m</a><a id="14196" class="Symbol">)</a> <a id="14198" href="Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>     <a id="14207" class="Symbol">=</a>  <a id="14210" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11033" class="InductiveConstructor">flipped</a> <a id="14218" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1441" class="InductiveConstructor">z≤n</a>
<a id="14222" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14105" class="Function">≤-total′</a> <a id="14231" class="Symbol">(</a><a id="14232" href="Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14236" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14236" class="Bound">m</a><a id="14237" class="Symbol">)</a> <a id="14239" class="Symbol">(</a><a id="14240" href="Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14244" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14244" class="Bound">n</a><a id="14245" class="Symbol">)</a>  <a id="14248" class="Symbol">=</a>  <a id="14251" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14283" class="Function">helper</a> <a id="14258" class="Symbol">(</a><a id="14259" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14105" class="Function">≤-total′</a> <a id="14268" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14236" class="Bound">m</a> <a id="14270" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14244" class="Bound">n</a><a id="14271" class="Symbol">)</a>
  <a id="14275" class="Keyword">where</a>
  <a id="14283" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14283" class="Function">helper</a> <a id="14290" class="Symbol">:</a> <a id="14292" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10945" class="Datatype">Total</a> <a id="14298" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14236" class="Bound">m</a> <a id="14300" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14244" class="Bound">n</a> <a id="14302" class="Symbol">→</a> <a id="14304" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10945" class="Datatype">Total</a> <a id="14310" class="Symbol">(</a><a id="14311" href="Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14315" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14236" class="Bound">m</a><a id="14316" class="Symbol">)</a> <a id="14318" class="Symbol">(</a><a id="14319" href="Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14323" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14244" class="Bound">n</a><a id="14324" class="Symbol">)</a>
  <a id="14328" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14283" class="Function">helper</a> <a id="14335" class="Symbol">(</a><a id="14336" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10976" class="InductiveConstructor">forward</a> <a id="14344" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14344" class="Bound">m≤n</a><a id="14347" class="Symbol">)</a>  <a id="14350" class="Symbol">=</a>  <a id="14353" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10976" class="InductiveConstructor">forward</a> <a id="14361" class="Symbol">(</a><a id="14362" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="14366" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14344" class="Bound">m≤n</a><a id="14369" class="Symbol">)</a>
  <a id="14373" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14283" class="Function">helper</a> <a id="14380" class="Symbol">(</a><a id="14381" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11033" class="InductiveConstructor">flipped</a> <a id="14389" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14389" class="Bound">n≤m</a><a id="14392" class="Symbol">)</a>  <a id="14395" class="Symbol">=</a>  <a id="14398" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11033" class="InductiveConstructor">flipped</a> <a id="14406" class="Symbol">(</a><a id="14407" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="14411" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14389" class="Bound">n≤m</a><a id="14414" class="Symbol">)</a>{% endraw %}</pre>
This is also our first use of a `where` clause in Agda.  The keyword `where` is
followed by one or more definitions, which must be indented.  Any variables
bound on the left-hand side of the preceding equation (in this case, `m` and
`n`) are in scope within the nested definition, and any identifiers bound in the
nested definition (in this case, `helper`) are in scope in the right-hand side
of the preceding equation.

If both arguments are equal, then both cases hold and we could return evidence
of either.  In the code above we return the forward case, but there is a
variant that returns the flipped case:
<pre class="Agda">{% raw %}<a id="≤-total″"></a><a id="15052" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15052" class="Function">≤-total″</a> <a id="15061" class="Symbol">:</a> <a id="15063" class="Symbol">∀</a> <a id="15065" class="Symbol">(</a><a id="15066" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15066" class="Bound">m</a> <a id="15068" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15068" class="Bound">n</a> <a id="15070" class="Symbol">:</a> <a id="15072" href="Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="15073" class="Symbol">)</a> <a id="15075" class="Symbol">→</a> <a id="15077" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10945" class="Datatype">Total</a> <a id="15083" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15066" class="Bound">m</a> <a id="15085" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15068" class="Bound">n</a>
<a id="15087" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15052" class="Function">≤-total″</a> <a id="15096" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15096" class="Bound">m</a>       <a id="15104" href="Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>                      <a id="15130" class="Symbol">=</a>  <a id="15133" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11033" class="InductiveConstructor">flipped</a> <a id="15141" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1441" class="InductiveConstructor">z≤n</a>
<a id="15145" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15052" class="Function">≤-total″</a> <a id="15154" href="Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="15162" class="Symbol">(</a><a id="15163" href="Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="15167" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15167" class="Bound">n</a><a id="15168" class="Symbol">)</a>                   <a id="15188" class="Symbol">=</a>  <a id="15191" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10976" class="InductiveConstructor">forward</a> <a id="15199" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1441" class="InductiveConstructor">z≤n</a>
<a id="15203" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15052" class="Function">≤-total″</a> <a id="15212" class="Symbol">(</a><a id="15213" href="Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="15217" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15217" class="Bound">m</a><a id="15218" class="Symbol">)</a> <a id="15220" class="Symbol">(</a><a id="15221" href="Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="15225" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15225" class="Bound">n</a><a id="15226" class="Symbol">)</a> <a id="15228" class="Keyword">with</a> <a id="15233" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15052" class="Function">≤-total″</a> <a id="15242" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15217" class="Bound">m</a> <a id="15244" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15225" class="Bound">n</a>
<a id="15246" class="Symbol">...</a>                        <a id="15273" class="Symbol">|</a> <a id="15275" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10976" class="InductiveConstructor">forward</a> <a id="15283" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15283" class="Bound">m≤n</a>   <a id="15289" class="Symbol">=</a>  <a id="15292" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10976" class="InductiveConstructor">forward</a> <a id="15300" class="Symbol">(</a><a id="15301" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="15305" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15283" class="Bound">m≤n</a><a id="15308" class="Symbol">)</a>
<a id="15310" class="Symbol">...</a>                        <a id="15337" class="Symbol">|</a> <a id="15339" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11033" class="InductiveConstructor">flipped</a> <a id="15347" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15347" class="Bound">n≤m</a>   <a id="15353" class="Symbol">=</a>  <a id="15356" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11033" class="InductiveConstructor">flipped</a> <a id="15364" class="Symbol">(</a><a id="15365" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="15369" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15347" class="Bound">n≤m</a><a id="15372" class="Symbol">)</a>{% endraw %}</pre>
It differs from the original code in that it pattern
matches on the second argument before the first argument.


## Monotonicity

If one bumps into both an operator and an ordering at a party, one may ask if
the operator is _monotonic_ with regard to the ordering.  For example, addition
is monotonic with regard to inequality, meaning:

    ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q

The proof is straightforward using the techniques we have learned, and is best
broken into three parts. First, we deal with the special case of showing
addition is monotonic on the right:
<pre class="Agda">{% raw %}<a id="+-monoʳ-≤"></a><a id="15977" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15977" class="Function">+-monoʳ-≤</a> <a id="15987" class="Symbol">:</a> <a id="15989" class="Symbol">∀</a> <a id="15991" class="Symbol">(</a><a id="15992" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15992" class="Bound">m</a> <a id="15994" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15994" class="Bound">p</a> <a id="15996" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15996" class="Bound">q</a> <a id="15998" class="Symbol">:</a> <a id="16000" href="Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="16001" class="Symbol">)</a>
  <a id="16005" class="Symbol">→</a> <a id="16007" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15994" class="Bound">p</a> <a id="16009" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="16011" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15996" class="Bound">q</a>
    <a id="16017" class="Comment">-------------</a>
  <a id="16033" class="Symbol">→</a> <a id="16035" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15992" class="Bound">m</a> <a id="16037" href="Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16039" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15994" class="Bound">p</a> <a id="16041" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="16043" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15992" class="Bound">m</a> <a id="16045" href="Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16047" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15996" class="Bound">q</a>
<a id="16049" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15977" class="Function">+-monoʳ-≤</a> <a id="16059" href="Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="16067" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16067" class="Bound">p</a> <a id="16069" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16069" class="Bound">q</a> <a id="16071" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16071" class="Bound">p≤q</a>  <a id="16076" class="Symbol">=</a>  <a id="16079" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16071" class="Bound">p≤q</a>
<a id="16083" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15977" class="Function">+-monoʳ-≤</a> <a id="16093" class="Symbol">(</a><a id="16094" href="Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="16098" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16098" class="Bound">m</a><a id="16099" class="Symbol">)</a> <a id="16101" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16101" class="Bound">p</a> <a id="16103" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16103" class="Bound">q</a> <a id="16105" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16105" class="Bound">p≤q</a>  <a id="16110" class="Symbol">=</a>  <a id="16113" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1490" class="InductiveConstructor">s≤s</a> <a id="16117" class="Symbol">(</a><a id="16118" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15977" class="Function">+-monoʳ-≤</a> <a id="16128" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16098" class="Bound">m</a> <a id="16130" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16101" class="Bound">p</a> <a id="16132" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16103" class="Bound">q</a> <a id="16134" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16105" class="Bound">p≤q</a><a id="16137" class="Symbol">)</a>{% endraw %}</pre>
The proof is by induction on the first argument.

* _Base case_: The first argument is `zero` in which case
  `zero + p ≤ zero + q` simplifies to `p ≤ q`, the evidence
  for which is given by the argument `p≤q`.

* _Inductive case_: The first argument is `suc m`, in which case
  `suc m + p ≤ suc m + q` simplifies to `suc (m + p) ≤ suc (m + q)`.
  The inductive hypothesis `+-monoʳ-≤ m p q p≤q` establishes that
  `m + p ≤ m + q`, and our goal follows by applying `s≤s`.

Second, we deal with the special case of showing addition is
monotonic on the left. This follows from the previous
result and the commutativity of addition:
<pre class="Agda">{% raw %}<a id="+-monoˡ-≤"></a><a id="16793" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16793" class="Function">+-monoˡ-≤</a> <a id="16803" class="Symbol">:</a> <a id="16805" class="Symbol">∀</a> <a id="16807" class="Symbol">(</a><a id="16808" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16808" class="Bound">m</a> <a id="16810" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16810" class="Bound">n</a> <a id="16812" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16812" class="Bound">p</a> <a id="16814" class="Symbol">:</a> <a id="16816" href="Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="16817" class="Symbol">)</a>
  <a id="16821" class="Symbol">→</a> <a id="16823" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16808" class="Bound">m</a> <a id="16825" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="16827" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16810" class="Bound">n</a>
    <a id="16833" class="Comment">-------------</a>
  <a id="16849" class="Symbol">→</a> <a id="16851" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16808" class="Bound">m</a> <a id="16853" href="Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16855" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16812" class="Bound">p</a> <a id="16857" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="16859" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16810" class="Bound">n</a> <a id="16861" href="Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16863" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16812" class="Bound">p</a>
<a id="16865" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16793" class="Function">+-monoˡ-≤</a> <a id="16875" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16875" class="Bound">m</a> <a id="16877" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16877" class="Bound">n</a> <a id="16879" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16879" class="Bound">p</a> <a id="16881" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16881" class="Bound">m≤n</a>  <a id="16886" class="Keyword">rewrite</a> <a id="16894" href="Data.Nat.Properties.html#9708" class="Function">+-comm</a> <a id="16901" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16875" class="Bound">m</a> <a id="16903" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16879" class="Bound">p</a> <a id="16905" class="Symbol">|</a> <a id="16907" href="Data.Nat.Properties.html#9708" class="Function">+-comm</a> <a id="16914" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16877" class="Bound">n</a> <a id="16916" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16879" class="Bound">p</a>  <a id="16919" class="Symbol">=</a> <a id="16921" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15977" class="Function">+-monoʳ-≤</a> <a id="16931" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16879" class="Bound">p</a> <a id="16933" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16875" class="Bound">m</a> <a id="16935" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16877" class="Bound">n</a> <a id="16937" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16881" class="Bound">m≤n</a>{% endraw %}</pre>
Rewriting by `+-comm m p` and `+-comm n p` converts `m + p ≤ n + p` into
`p + m ≤ p + n`, which is proved by invoking `+-monoʳ-≤ p m n m≤n`.

Third, we combine the two previous results:
<pre class="Agda">{% raw %}<a id="+-mono-≤"></a><a id="17151" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17151" class="Function">+-mono-≤</a> <a id="17160" class="Symbol">:</a> <a id="17162" class="Symbol">∀</a> <a id="17164" class="Symbol">(</a><a id="17165" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17165" class="Bound">m</a> <a id="17167" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17167" class="Bound">n</a> <a id="17169" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17169" class="Bound">p</a> <a id="17171" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17171" class="Bound">q</a> <a id="17173" class="Symbol">:</a> <a id="17175" href="Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="17176" class="Symbol">)</a>
  <a id="17180" class="Symbol">→</a> <a id="17182" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17165" class="Bound">m</a> <a id="17184" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="17186" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17167" class="Bound">n</a>
  <a id="17190" class="Symbol">→</a> <a id="17192" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17169" class="Bound">p</a> <a id="17194" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="17196" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17171" class="Bound">q</a>
    <a id="17202" class="Comment">-------------</a>
  <a id="17218" class="Symbol">→</a> <a id="17220" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17165" class="Bound">m</a> <a id="17222" href="Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="17224" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17169" class="Bound">p</a> <a id="17226" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1414" class="Datatype Operator">≤</a> <a id="17228" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17167" class="Bound">n</a> <a id="17230" href="Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="17232" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17171" class="Bound">q</a>
<a id="17234" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17151" class="Function">+-mono-≤</a> <a id="17243" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17243" class="Bound">m</a> <a id="17245" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17245" class="Bound">n</a> <a id="17247" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17247" class="Bound">p</a> <a id="17249" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17249" class="Bound">q</a> <a id="17251" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17251" class="Bound">m≤n</a> <a id="17255" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17255" class="Bound">p≤q</a>  <a id="17260" class="Symbol">=</a>  <a id="17263" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7593" class="Function">≤-trans</a> <a id="17271" class="Symbol">(</a><a id="17272" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16793" class="Function">+-monoˡ-≤</a> <a id="17282" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17243" class="Bound">m</a> <a id="17284" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17245" class="Bound">n</a> <a id="17286" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17247" class="Bound">p</a> <a id="17288" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17251" class="Bound">m≤n</a><a id="17291" class="Symbol">)</a> <a id="17293" class="Symbol">(</a><a id="17294" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15977" class="Function">+-monoʳ-≤</a> <a id="17304" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17245" class="Bound">n</a> <a id="17306" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17247" class="Bound">p</a> <a id="17308" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17249" class="Bound">q</a> <a id="17310" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17255" class="Bound">p≤q</a><a id="17313" class="Symbol">)</a>{% endraw %}</pre>
Invoking `+-monoˡ-≤ m n p m≤n` proves `m + p ≤ n + p` and invoking
`+-monoʳ-≤ n p q p≤q` proves `n + p ≤ n + q`, and combining these with
transitivity proves `m + p ≤ n + q`, as was to be shown.


#### Exercise `*-mono-≤` (stretch)

Show that multiplication is monotonic with regard to inequality.

<pre class="Agda">{% raw %}<a id="17638" class="Comment">-- Your code goes here</a>{% endraw %}</pre>


## Strict inequality {#strict-inequality}

We can define strict inequality similarly to inequality:
<pre class="Agda">{% raw %}<a id="17787" class="Keyword">infix</a> <a id="17793" class="Number">4</a> <a id="17795" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17805" class="Datatype Operator">_&lt;_</a>

<a id="17800" class="Keyword">data</a> <a id="_&lt;_"></a><a id="17805" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17805" class="Datatype Operator">_&lt;_</a> <a id="17809" class="Symbol">:</a> <a id="17811" href="Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="17813" class="Symbol">→</a> <a id="17815" href="Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="17817" class="Symbol">→</a> <a id="17819" class="PrimitiveType">Set</a> <a id="17823" class="Keyword">where</a>

  <a id="_&lt;_.z&lt;s"></a><a id="17832" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17832" class="InductiveConstructor">z&lt;s</a> <a id="17836" class="Symbol">:</a> <a id="17838" class="Symbol">∀</a> <a id="17840" class="Symbol">{</a><a id="17841" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17841" class="Bound">n</a> <a id="17843" class="Symbol">:</a> <a id="17845" href="Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="17846" class="Symbol">}</a>
      <a id="17854" class="Comment">------------</a>
    <a id="17871" class="Symbol">→</a> <a id="17873" href="Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="17878" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17805" class="Datatype Operator">&lt;</a> <a id="17880" href="Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="17884" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17841" class="Bound">n</a>

  <a id="_&lt;_.s&lt;s"></a><a id="17889" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17889" class="InductiveConstructor">s&lt;s</a> <a id="17893" class="Symbol">:</a> <a id="17895" class="Symbol">∀</a> <a id="17897" class="Symbol">{</a><a id="17898" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17898" class="Bound">m</a> <a id="17900" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17900" class="Bound">n</a> <a id="17902" class="Symbol">:</a> <a id="17904" href="Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="17905" class="Symbol">}</a>
    <a id="17911" class="Symbol">→</a> <a id="17913" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17898" class="Bound">m</a> <a id="17915" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17805" class="Datatype Operator">&lt;</a> <a id="17917" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17900" class="Bound">n</a>
      <a id="17925" class="Comment">-------------</a>
    <a id="17943" class="Symbol">→</a> <a id="17945" href="Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="17949" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17898" class="Bound">m</a> <a id="17951" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17805" class="Datatype Operator">&lt;</a> <a id="17953" href="Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="17957" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17900" class="Bound">n</a>{% endraw %}</pre>
The key difference is that zero is less than the successor of an
arbitrary number, but is not less than zero.

Clearly, strict inequality is not reflexive. However it is
_irreflexive_ in that `n < n` never holds for any value of `n`.
Like inequality, strict inequality is transitive.
Strict inequality is not total, but satisfies the closely related property of
_trichotomy_: for any `m` and `n`, exactly one of `m < n`, `m ≡ n`, or `m > n`
holds (where we define `m > n` to hold exactly when `n < m`).
It is also monotonic with regards to addition and multiplication.

Most of the above are considered in exercises below.  Irreflexivity
requires negation, as does the fact that the three cases in
trichotomy are mutually exclusive, so those points are deferred to
Chapter [Negation]({{ site.baseurl }}{% link out/plfa/Negation.md%}).

It is straightforward to show that `suc m ≤ n` implies `m < n`,
and conversely.  One can then give an alternative derivation of the
properties of strict inequality, such as transitivity, by
exploiting the corresponding properties of inequality.

#### Exercise `<-trans` (recommended) {#less-trans}

Show that strict inequality is transitive.

<pre class="Agda">{% raw %}<a id="19127" class="Comment">-- Your code goes here</a>{% endraw %}</pre>

#### Exercise `trichotomy` {#trichotomy}

Show that strict inequality satisfies a weak version of trichotomy, in
the sense that for any `m` and `n` that one of the following holds:
  * `m < n`,
  * `m ≡ n`, or
  * `m > n`.

Define `m > n` to be the same as `n < m`.
You will need a suitable data declaration,
similar to that used for totality.
(We will show that the three cases are exclusive after we introduce
[negation]({{ site.baseurl }}{% link out/plfa/Negation.md%}).)

<pre class="Agda">{% raw %}<a id="19616" class="Comment">-- Your code goes here</a>{% endraw %}</pre>

#### Exercise `+-mono-<` {#plus-mono-less}

Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.

<pre class="Agda">{% raw %}<a id="19841" class="Comment">-- Your code goes here</a>{% endraw %}</pre>

#### Exercise `≤-iff-<` (recommended) {#leq-iff-less}

Show that `suc m ≤ n` implies `m < n`, and conversely.

<pre class="Agda">{% raw %}<a id="20000" class="Comment">-- Your code goes here</a>{% endraw %}</pre>

#### Exercise `<-trans-revisited` {#less-trans-revisited}

Give an alternative proof that strict inequality is transitive,
using the relating between strict inequality and inequality and
the fact that inequality is transitive.

<pre class="Agda">{% raw %}<a id="20276" class="Comment">-- Your code goes here</a>{% endraw %}</pre>


## Even and odd

As a further example, let's specify even and odd numbers.  Inequality
and strict inequality are _binary relations_, while even and odd are
_unary relations_, sometimes called _predicates_:
<pre class="Agda">{% raw %}<a id="20531" class="Keyword">data</a> <a id="even"></a><a id="20536" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20536" class="Datatype">even</a> <a id="20541" class="Symbol">:</a> <a id="20543" href="Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="20545" class="Symbol">→</a> <a id="20547" class="PrimitiveType">Set</a>
<a id="20551" class="Keyword">data</a> <a id="odd"></a><a id="20556" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20556" class="Datatype">odd</a>  <a id="20561" class="Symbol">:</a> <a id="20563" href="Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="20565" class="Symbol">→</a> <a id="20567" class="PrimitiveType">Set</a>

<a id="20572" class="Keyword">data</a> <a id="20577" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20536" class="Datatype">even</a> <a id="20582" class="Keyword">where</a>

  <a id="even.zero"></a><a id="20591" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20591" class="InductiveConstructor">zero</a> <a id="20596" class="Symbol">:</a>
      <a id="20604" class="Comment">---------</a>
      <a id="20620" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20536" class="Datatype">even</a> <a id="20625" href="Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>

  <a id="even.suc"></a><a id="20633" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20633" class="InductiveConstructor">suc</a>  <a id="20638" class="Symbol">:</a> <a id="20640" class="Symbol">∀</a> <a id="20642" class="Symbol">{</a><a id="20643" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20643" class="Bound">n</a> <a id="20645" class="Symbol">:</a> <a id="20647" href="Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="20648" class="Symbol">}</a>
    <a id="20654" class="Symbol">→</a> <a id="20656" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20556" class="Datatype">odd</a> <a id="20660" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20643" class="Bound">n</a>
      <a id="20668" class="Comment">------------</a>
    <a id="20685" class="Symbol">→</a> <a id="20687" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20536" class="Datatype">even</a> <a id="20692" class="Symbol">(</a><a id="20693" href="Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="20697" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20643" class="Bound">n</a><a id="20698" class="Symbol">)</a>

<a id="20701" class="Keyword">data</a> <a id="20706" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20556" class="Datatype">odd</a> <a id="20710" class="Keyword">where</a>

  <a id="odd.suc"></a><a id="20719" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20719" class="InductiveConstructor">suc</a>   <a id="20725" class="Symbol">:</a> <a id="20727" class="Symbol">∀</a> <a id="20729" class="Symbol">{</a><a id="20730" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20730" class="Bound">n</a> <a id="20732" class="Symbol">:</a> <a id="20734" href="Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="20735" class="Symbol">}</a>
    <a id="20741" class="Symbol">→</a> <a id="20743" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20536" class="Datatype">even</a> <a id="20748" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20730" class="Bound">n</a>
      <a id="20756" class="Comment">-----------</a>
    <a id="20772" class="Symbol">→</a> <a id="20774" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20556" class="Datatype">odd</a> <a id="20778" class="Symbol">(</a><a id="20779" href="Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="20783" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20730" class="Bound">n</a><a id="20784" class="Symbol">)</a>{% endraw %}</pre>
A number is even if it is zero or the successor of an odd number,
and odd if it is the successor of an even number.

This is our first use of a mutually recursive datatype declaration.
Since each identifier must be defined before it is used, we first
declare the indexed types `even` and `odd` (omitting the `where`
keyword and the declarations of the constructors) and then
declare the constructors (omitting the signatures `ℕ → Set`
which were given earlier).

This is also our first use of _overloaded_ constructors,
that is, using the same name for constructors of different types.
Here `suc` means one of three constructors:

    suc : ℕ → ℕ

    suc : ∀ {n : ℕ}
      → odd n
        ------------
      → even (suc n)

    suc : ∀ {n : ℕ}
      → even n
        -----------
      → odd (suc n)

Similarly, `zero` refers to one of two constructors. Due to how it
does type inference, Agda does not allow overloading of defined names,
but does allow overloading of constructors.  It is recommended that
one restrict overloading to related meanings, as we have done here,
but it is not required.

We show that the sum of two even numbers is even:
<pre class="Agda">{% raw %}<a id="e+e≡e"></a><a id="21960" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21960" class="Function">e+e≡e</a> <a id="21966" class="Symbol">:</a> <a id="21968" class="Symbol">∀</a> <a id="21970" class="Symbol">{</a><a id="21971" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21971" class="Bound">m</a> <a id="21973" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21973" class="Bound">n</a> <a id="21975" class="Symbol">:</a> <a id="21977" href="Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="21978" class="Symbol">}</a>
  <a id="21982" class="Symbol">→</a> <a id="21984" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20536" class="Datatype">even</a> <a id="21989" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21971" class="Bound">m</a>
  <a id="21993" class="Symbol">→</a> <a id="21995" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20536" class="Datatype">even</a> <a id="22000" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21973" class="Bound">n</a>
    <a id="22006" class="Comment">------------</a>
  <a id="22021" class="Symbol">→</a> <a id="22023" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20536" class="Datatype">even</a> <a id="22028" class="Symbol">(</a><a id="22029" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21971" class="Bound">m</a> <a id="22031" href="Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="22033" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21973" class="Bound">n</a><a id="22034" class="Symbol">)</a>

<a id="o+e≡o"></a><a id="22037" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22037" class="Function">o+e≡o</a> <a id="22043" class="Symbol">:</a> <a id="22045" class="Symbol">∀</a> <a id="22047" class="Symbol">{</a><a id="22048" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22048" class="Bound">m</a> <a id="22050" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22050" class="Bound">n</a> <a id="22052" class="Symbol">:</a> <a id="22054" href="Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="22055" class="Symbol">}</a>
  <a id="22059" class="Symbol">→</a> <a id="22061" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20556" class="Datatype">odd</a> <a id="22065" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22048" class="Bound">m</a>
  <a id="22069" class="Symbol">→</a> <a id="22071" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20536" class="Datatype">even</a> <a id="22076" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22050" class="Bound">n</a>
    <a id="22082" class="Comment">-----------</a>
  <a id="22096" class="Symbol">→</a> <a id="22098" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20556" class="Datatype">odd</a> <a id="22102" class="Symbol">(</a><a id="22103" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22048" class="Bound">m</a> <a id="22105" href="Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="22107" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22050" class="Bound">n</a><a id="22108" class="Symbol">)</a>

<a id="22111" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21960" class="Function">e+e≡e</a> <a id="22117" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20591" class="InductiveConstructor">zero</a>     <a id="22126" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22126" class="Bound">en</a>  <a id="22130" class="Symbol">=</a>  <a id="22133" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22126" class="Bound">en</a>
<a id="22136" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21960" class="Function">e+e≡e</a> <a id="22142" class="Symbol">(</a><a id="22143" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20633" class="InductiveConstructor">suc</a> <a id="22147" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22147" class="Bound">om</a><a id="22149" class="Symbol">)</a> <a id="22151" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22151" class="Bound">en</a>  <a id="22155" class="Symbol">=</a>  <a id="22158" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20633" class="InductiveConstructor">suc</a> <a id="22162" class="Symbol">(</a><a id="22163" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22037" class="Function">o+e≡o</a> <a id="22169" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22147" class="Bound">om</a> <a id="22172" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22151" class="Bound">en</a><a id="22174" class="Symbol">)</a>

<a id="22177" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22037" class="Function">o+e≡o</a> <a id="22183" class="Symbol">(</a><a id="22184" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20719" class="InductiveConstructor">suc</a> <a id="22188" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22188" class="Bound">em</a><a id="22190" class="Symbol">)</a> <a id="22192" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22192" class="Bound">en</a>  <a id="22196" class="Symbol">=</a>  <a id="22199" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#20719" class="InductiveConstructor">suc</a> <a id="22203" class="Symbol">(</a><a id="22204" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21960" class="Function">e+e≡e</a> <a id="22210" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22188" class="Bound">em</a> <a id="22213" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22192" class="Bound">en</a><a id="22215" class="Symbol">)</a>{% endraw %}</pre>
Corresponding to the mutually recursive types, we use two mutually recursive
functions, one to show that the sum of two even numbers is even, and the other
to show that the sum of an odd and an even number is odd.

This is our first use of mutually recursive functions.  Since each identifier
must be defined before it is used, we first give the signatures for both
functions and then the equations that define them.

To show that the sum of two even numbers is even, consider the
evidence that the first number is even. If it is because it is zero,
then the sum is even because the second number is even.  If it is
because it is the successor of an odd number, then the result is even
because it is the successor of the sum of an odd and an even number,
which is odd.

To show that the sum of an odd and even number is odd, consider the
evidence that the first number is odd. If it is because it is the
successor of an even number, then the result is odd because it is the
successor of the sum of two even numbers, which is even.

#### Exercise `o+o≡e` (stretch) {#odd-plus-odd}

Show that the sum of two odd numbers is even.

<pre class="Agda">{% raw %}<a id="23369" class="Comment">-- Your code goes here</a>{% endraw %}</pre>

#### Exercise `Bin-predicates` (stretch) {#Bin-predicates}

Recall that 
Exercise [Bin]({{ site.baseurl }}{% link out/plfa/Naturals.md%}#Bin)
defines a datatype `Bin` of bitstrings representing natural numbers.
Representations are not unique due to leading zeros.
Hence, eleven may be represented by both of the following:

    x1 x1 x0 x1 nil
    x1 x1 x0 x1 x0 x0 nil

Define a predicate

    Can : Bin → Set

over all bitstrings that holds if the bitstring is canonical, meaning
it has no leading zeros; the first representation of eleven above is
canonical, and the second is not.  To define it, you will need an
auxiliary predicate

    One : Bin → Set

that holds only if the bistring has a leading one.  A bitstring is
canonical if it has a leading one (representing a positive number) or
if it consists of a single zero (representing zero).

Show that increment preserves canonical bitstrings:

    Can x
    ------------
    Can (inc x)

Show that converting a natural to a bitstring always yields a
canonical bitstring:

    ----------
    Can (to n)

Show that converting a canonical bitstring to a natural
and back is the identity:

    Can x
    ---------------
    to (from x) ≡ x

(Hint: For each of these, you may first need to prove related
properties of `One`.)

<pre class="Agda">{% raw %}<a id="24663" class="Comment">-- Your code goes here</a>{% endraw %}</pre>

## Standard library

Definitions similar to those in this chapter can be found in the standard library:
<pre class="Agda">{% raw %}<a id="24815" class="Keyword">import</a> <a id="24822" href="Data.Nat.html" class="Module">Data.Nat</a> <a id="24831" class="Keyword">using</a> <a id="24837" class="Symbol">(</a><a id="24838" href="Data.Nat.Base.html#845" class="Datatype Operator">_≤_</a><a id="24841" class="Symbol">;</a> <a id="24843" href="Data.Nat.Base.html#868" class="InductiveConstructor">z≤n</a><a id="24846" class="Symbol">;</a> <a id="24848" href="Data.Nat.Base.html#910" class="InductiveConstructor">s≤s</a><a id="24851" class="Symbol">)</a>
<a id="24853" class="Keyword">import</a> <a id="24860" href="Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="24880" class="Keyword">using</a> <a id="24886" class="Symbol">(</a><a id="24887" href="Data.Nat.Properties.html#2115" class="Function">≤-refl</a><a id="24893" class="Symbol">;</a> <a id="24895" href="Data.Nat.Properties.html#2308" class="Function">≤-trans</a><a id="24902" class="Symbol">;</a> <a id="24904" href="Data.Nat.Properties.html#2165" class="Function">≤-antisym</a><a id="24913" class="Symbol">;</a> <a id="24915" href="Data.Nat.Properties.html#2420" class="Function">≤-total</a><a id="24922" class="Symbol">;</a>
                                  <a id="24958" href="Data.Nat.Properties.html#12667" class="Function">+-monoʳ-≤</a><a id="24967" class="Symbol">;</a> <a id="24969" href="Data.Nat.Properties.html#12577" class="Function">+-monoˡ-≤</a><a id="24978" class="Symbol">;</a> <a id="24980" href="Data.Nat.Properties.html#12421" class="Function">+-mono-≤</a><a id="24988" class="Symbol">)</a>{% endraw %}</pre>
In the standard library, `≤-total` is formalised in terms of
disjunction (which we define in
Chapter [Connectives]({{ site.baseurl }}{% link out/plfa/Connectives.md%})),
and `+-monoʳ-≤`, `+-monoˡ-≤`, `+-mono-≤` are proved differently than here,
and more arguments are implicit.


## Unicode

This chapter uses the following unicode:

    ≤  U+2264  LESS-THAN OR EQUAL TO (\<=, \le)
    ≥  U+2265  GREATER-THAN OR EQUAL TO (\>=, \ge)
    ˡ  U+02E1  MODIFIER LETTER SMALL L (\^l)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)

The commands `\^l` and `\^r` give access to a variety of superscript
leftward and rightward arrows in addition to superscript letters `l` and `r`.
