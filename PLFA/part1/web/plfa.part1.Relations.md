---
title     : "Relations: Inductive definition of relations"
permalink : /Relations/
---

<pre class="Agda"><a id="101" class="Keyword">module</a> <a id="108" href="plfa.part1.Relations.html" class="Module">plfa.part1.Relations</a> <a id="129" class="Keyword">where</a>
</pre>
After having defined operations such as addition and multiplication,
the next step is to define relations, such as _less than or equal_.

## Imports

<pre class="Agda"><a id="298" class="Keyword">import</a> <a id="305" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="343" class="Symbol">as</a> <a id="346" class="Module">Eq</a>
<a id="349" class="Keyword">open</a> <a id="354" href="Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="357" class="Keyword">using</a> <a id="363" class="Symbol">(</a><a id="364" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">_≡_</a><a id="367" class="Symbol">;</a> <a id="369" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a><a id="373" class="Symbol">;</a> <a id="375" href="Relation.Binary.PropositionalEquality.Core.html#1139" class="Function">cong</a><a id="379" class="Symbol">)</a>
<a id="381" class="Keyword">open</a> <a id="386" class="Keyword">import</a> <a id="393" href="Data.Nat.html" class="Module">Data.Nat</a> <a id="402" class="Keyword">using</a> <a id="408" class="Symbol">(</a><a id="409" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="410" class="Symbol">;</a> <a id="412" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a><a id="416" class="Symbol">;</a> <a id="418" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a><a id="421" class="Symbol">;</a> <a id="423" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">_+_</a><a id="426" class="Symbol">)</a>
<a id="428" class="Keyword">open</a> <a id="433" class="Keyword">import</a> <a id="440" href="Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="460" class="Keyword">using</a> <a id="466" class="Symbol">(</a><a id="467" href="Data.Nat.Properties.html#13404" class="Function">+-comm</a><a id="473" class="Symbol">;</a> <a id="475" href="Data.Nat.Properties.html#13227" class="Function">+-identityʳ</a><a id="486" class="Symbol">)</a>
</pre>

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
<pre class="Agda"><a id="1151" class="Keyword">data</a> <a id="_≤_"></a><a id="1156" href="plfa.part1.Relations.html#1156" class="Datatype Operator">_≤_</a> <a id="1160" class="Symbol">:</a> <a id="1162" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="1164" class="Symbol">→</a> <a id="1166" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="1168" class="Symbol">→</a> <a id="1170" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="1174" class="Keyword">where</a>

  <a id="_≤_.z≤n"></a><a id="1183" href="plfa.part1.Relations.html#1183" class="InductiveConstructor">z≤n</a> <a id="1187" class="Symbol">:</a> <a id="1189" class="Symbol">∀</a> <a id="1191" class="Symbol">{</a><a id="1192" href="plfa.part1.Relations.html#1192" class="Bound">n</a> <a id="1194" class="Symbol">:</a> <a id="1196" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="1197" class="Symbol">}</a>
      <a id="1205" class="Comment">--------</a>
    <a id="1218" class="Symbol">→</a> <a id="1220" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a> <a id="1225" href="plfa.part1.Relations.html#1156" class="Datatype Operator">≤</a> <a id="1227" href="plfa.part1.Relations.html#1192" class="Bound">n</a>

  <a id="_≤_.s≤s"></a><a id="1232" href="plfa.part1.Relations.html#1232" class="InductiveConstructor">s≤s</a> <a id="1236" class="Symbol">:</a> <a id="1238" class="Symbol">∀</a> <a id="1240" class="Symbol">{</a><a id="1241" href="plfa.part1.Relations.html#1241" class="Bound">m</a> <a id="1243" href="plfa.part1.Relations.html#1243" class="Bound">n</a> <a id="1245" class="Symbol">:</a> <a id="1247" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="1248" class="Symbol">}</a>
    <a id="1254" class="Symbol">→</a> <a id="1256" href="plfa.part1.Relations.html#1241" class="Bound">m</a> <a id="1258" href="plfa.part1.Relations.html#1156" class="Datatype Operator">≤</a> <a id="1260" href="plfa.part1.Relations.html#1243" class="Bound">n</a>
      <a id="1268" class="Comment">-------------</a>
    <a id="1286" class="Symbol">→</a> <a id="1288" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="1292" href="plfa.part1.Relations.html#1241" class="Bound">m</a> <a id="1294" href="plfa.part1.Relations.html#1156" class="Datatype Operator">≤</a> <a id="1296" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="1300" href="plfa.part1.Relations.html#1243" class="Bound">n</a>
</pre>Here `z≤n` and `s≤s` (with no spaces) are constructor names, while
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
<pre class="Agda"><a id="2566" href="plfa.part1.Relations.html#2566" class="Function">_</a> <a id="2568" class="Symbol">:</a> <a id="2570" class="Number">2</a> <a id="2572" href="plfa.part1.Relations.html#1156" class="Datatype Operator">≤</a> <a id="2574" class="Number">4</a>
<a id="2576" class="Symbol">_</a> <a id="2578" class="Symbol">=</a> <a id="2580" href="plfa.part1.Relations.html#1232" class="InductiveConstructor">s≤s</a> <a id="2584" class="Symbol">(</a><a id="2585" href="plfa.part1.Relations.html#1232" class="InductiveConstructor">s≤s</a> <a id="2589" href="plfa.part1.Relations.html#1183" class="InductiveConstructor">z≤n</a><a id="2592" class="Symbol">)</a>
</pre>



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
<pre class="Agda"><a id="3575" href="plfa.part1.Relations.html#3575" class="Function">_</a> <a id="3577" class="Symbol">:</a> <a id="3579" class="Number">2</a> <a id="3581" href="plfa.part1.Relations.html#1156" class="Datatype Operator">≤</a> <a id="3583" class="Number">4</a>
<a id="3585" class="Symbol">_</a> <a id="3587" class="Symbol">=</a> <a id="3589" href="plfa.part1.Relations.html#1232" class="InductiveConstructor">s≤s</a> <a id="3593" class="Symbol">{</a><a id="3594" class="Number">1</a><a id="3595" class="Symbol">}</a> <a id="3597" class="Symbol">{</a><a id="3598" class="Number">3</a><a id="3599" class="Symbol">}</a> <a id="3601" class="Symbol">(</a><a id="3602" href="plfa.part1.Relations.html#1232" class="InductiveConstructor">s≤s</a> <a id="3606" class="Symbol">{</a><a id="3607" class="Number">0</a><a id="3608" class="Symbol">}</a> <a id="3610" class="Symbol">{</a><a id="3611" class="Number">2</a><a id="3612" class="Symbol">}</a> <a id="3614" class="Symbol">(</a><a id="3615" href="plfa.part1.Relations.html#1183" class="InductiveConstructor">z≤n</a> <a id="3619" class="Symbol">{</a><a id="3620" class="Number">2</a><a id="3621" class="Symbol">}))</a>
</pre>One may also identify implicit arguments by name:
<pre class="Agda"><a id="3687" href="plfa.part1.Relations.html#3687" class="Function">_</a> <a id="3689" class="Symbol">:</a> <a id="3691" class="Number">2</a> <a id="3693" href="plfa.part1.Relations.html#1156" class="Datatype Operator">≤</a> <a id="3695" class="Number">4</a>
<a id="3697" class="Symbol">_</a> <a id="3699" class="Symbol">=</a> <a id="3701" href="plfa.part1.Relations.html#1232" class="InductiveConstructor">s≤s</a> <a id="3705" class="Symbol">{</a><a id="3706" class="Argument">m</a> <a id="3708" class="Symbol">=</a> <a id="3710" class="Number">1</a><a id="3711" class="Symbol">}</a> <a id="3713" class="Symbol">{</a><a id="3714" class="Argument">n</a> <a id="3716" class="Symbol">=</a> <a id="3718" class="Number">3</a><a id="3719" class="Symbol">}</a> <a id="3721" class="Symbol">(</a><a id="3722" href="plfa.part1.Relations.html#1232" class="InductiveConstructor">s≤s</a> <a id="3726" class="Symbol">{</a><a id="3727" class="Argument">m</a> <a id="3729" class="Symbol">=</a> <a id="3731" class="Number">0</a><a id="3732" class="Symbol">}</a> <a id="3734" class="Symbol">{</a><a id="3735" class="Argument">n</a> <a id="3737" class="Symbol">=</a> <a id="3739" class="Number">2</a><a id="3740" class="Symbol">}</a> <a id="3742" class="Symbol">(</a><a id="3743" href="plfa.part1.Relations.html#1183" class="InductiveConstructor">z≤n</a> <a id="3747" class="Symbol">{</a><a id="3748" class="Argument">n</a> <a id="3750" class="Symbol">=</a> <a id="3752" class="Number">2</a><a id="3753" class="Symbol">}))</a>
</pre>In the latter format, you can choose to only supply some implicit arguments:
<pre class="Agda"><a id="3846" href="plfa.part1.Relations.html#3846" class="Function">_</a> <a id="3848" class="Symbol">:</a> <a id="3850" class="Number">2</a> <a id="3852" href="plfa.part1.Relations.html#1156" class="Datatype Operator">≤</a> <a id="3854" class="Number">4</a>
<a id="3856" class="Symbol">_</a> <a id="3858" class="Symbol">=</a> <a id="3860" href="plfa.part1.Relations.html#1232" class="InductiveConstructor">s≤s</a> <a id="3864" class="Symbol">{</a><a id="3865" class="Argument">n</a> <a id="3867" class="Symbol">=</a> <a id="3869" class="Number">3</a><a id="3870" class="Symbol">}</a> <a id="3872" class="Symbol">(</a><a id="3873" href="plfa.part1.Relations.html#1232" class="InductiveConstructor">s≤s</a> <a id="3877" class="Symbol">{</a><a id="3878" class="Argument">n</a> <a id="3880" class="Symbol">=</a> <a id="3882" class="Number">2</a><a id="3883" class="Symbol">}</a> <a id="3885" href="plfa.part1.Relations.html#1183" class="InductiveConstructor">z≤n</a><a id="3888" class="Symbol">)</a>
</pre>It is not permitted to swap implicit arguments, even when named.

We can ask Agda to use the same inference to try and infer an _explicit_ term,
by writing `_`. For instance, we can define a variant of the proposition
`+-identityʳ` with implicit arguments:
<pre class="Agda"><a id="+-identityʳ′"></a><a id="4159" href="plfa.part1.Relations.html#4159" class="Function">+-identityʳ′</a> <a id="4172" class="Symbol">:</a> <a id="4174" class="Symbol">∀</a> <a id="4176" class="Symbol">{</a><a id="4177" href="plfa.part1.Relations.html#4177" class="Bound">m</a> <a id="4179" class="Symbol">:</a> <a id="4181" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="4182" class="Symbol">}</a> <a id="4184" class="Symbol">→</a> <a id="4186" href="plfa.part1.Relations.html#4177" class="Bound">m</a> <a id="4188" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="4190" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a> <a id="4195" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="4197" href="plfa.part1.Relations.html#4177" class="Bound">m</a>
<a id="4199" href="plfa.part1.Relations.html#4159" class="Function">+-identityʳ′</a> <a id="4212" class="Symbol">=</a> <a id="4214" href="Data.Nat.Properties.html#13227" class="Function">+-identityʳ</a> <a id="4226" class="Symbol">_</a>
</pre>We use `_` to ask Agda to infer the value of the _explicit_ argument from
context. There is only one value which gives us the correct proof, `m`, so Agda
happily fills it in.
If Agda fails to infer the value, it reports an error.


## Precedence

We declare the precedence for comparison as follows:
<pre class="Agda"><a id="4540" class="Keyword">infix</a> <a id="4546" class="Number">4</a> <a id="4548" href="plfa.part1.Relations.html#1156" class="Datatype Operator">_≤_</a>
</pre>We set the precedence of `_≤_` at level 4, so it binds less tightly
than `_+_` at level 6 and hence `1 + 2 ≤ 3` parses as `(1 + 2) ≤ 3`.
We write `infix` to indicate that the operator does not associate to
either the left or right, as it makes no sense to parse `1 ≤ 2 ≤ 3` as
either `(1 ≤ 2) ≤ 3` or `1 ≤ (2 ≤ 3)`.


## Decidability

Given two numbers, it is straightforward to compute whether or not the
first is less than or equal to the second.  We don't give the code for
doing so here, but will return to this point in
Chapter [Decidable](/Decidable/).


## Inversion

In our definitions, we go from smaller things to larger things.
For instance, from `m ≤ n` we can conclude `suc m ≤ suc n`,
where `suc m` is bigger than `m` (that is, the former contains
the latter), and `suc n` is bigger than `n`. But sometimes we
want to go from bigger things to smaller things.

There is only one way to prove that `suc m ≤ suc n`, for any `m`
and `n`.  This lets us invert our previous rule.
<pre class="Agda"><a id="inv-s≤s"></a><a id="5552" href="plfa.part1.Relations.html#5552" class="Function">inv-s≤s</a> <a id="5560" class="Symbol">:</a> <a id="5562" class="Symbol">∀</a> <a id="5564" class="Symbol">{</a><a id="5565" href="plfa.part1.Relations.html#5565" class="Bound">m</a> <a id="5567" href="plfa.part1.Relations.html#5567" class="Bound">n</a> <a id="5569" class="Symbol">:</a> <a id="5571" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="5572" class="Symbol">}</a>
  <a id="5576" class="Symbol">→</a> <a id="5578" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="5582" href="plfa.part1.Relations.html#5565" class="Bound">m</a> <a id="5584" href="plfa.part1.Relations.html#1156" class="Datatype Operator">≤</a> <a id="5586" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="5590" href="plfa.part1.Relations.html#5567" class="Bound">n</a>
    <a id="5596" class="Comment">-------------</a>
  <a id="5612" class="Symbol">→</a> <a id="5614" href="plfa.part1.Relations.html#5565" class="Bound">m</a> <a id="5616" href="plfa.part1.Relations.html#1156" class="Datatype Operator">≤</a> <a id="5618" href="plfa.part1.Relations.html#5567" class="Bound">n</a>
<a id="5620" href="plfa.part1.Relations.html#5552" class="Function">inv-s≤s</a> <a id="5628" class="Symbol">(</a><a id="5629" href="plfa.part1.Relations.html#1232" class="InductiveConstructor">s≤s</a> <a id="5633" href="plfa.part1.Relations.html#5633" class="Bound">m≤n</a><a id="5636" class="Symbol">)</a> <a id="5638" class="Symbol">=</a> <a id="5640" href="plfa.part1.Relations.html#5633" class="Bound">m≤n</a>
</pre>Here `m≤n` (with no spaces) is a variable name while
`m ≤ n` (with spaces) is a type, and the latter
is the type of the former.  It is a common convention
in Agda to derive a variable name by removing
spaces from its type.

Not every rule is invertible; indeed, the rule for `z≤n` has
no non-implicit hypotheses, so there is nothing to invert.
But often inversions of this kind hold.

Another example of inversion is showing that there is
only one way a number can be less than or equal to zero.
<pre class="Agda"><a id="inv-z≤n"></a><a id="6152" href="plfa.part1.Relations.html#6152" class="Function">inv-z≤n</a> <a id="6160" class="Symbol">:</a> <a id="6162" class="Symbol">∀</a> <a id="6164" class="Symbol">{</a><a id="6165" href="plfa.part1.Relations.html#6165" class="Bound">m</a> <a id="6167" class="Symbol">:</a> <a id="6169" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="6170" class="Symbol">}</a>
  <a id="6174" class="Symbol">→</a> <a id="6176" href="plfa.part1.Relations.html#6165" class="Bound">m</a> <a id="6178" href="plfa.part1.Relations.html#1156" class="Datatype Operator">≤</a> <a id="6180" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a>
    <a id="6189" class="Comment">--------</a>
  <a id="6200" class="Symbol">→</a> <a id="6202" href="plfa.part1.Relations.html#6165" class="Bound">m</a> <a id="6204" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="6206" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a>
<a id="6211" href="plfa.part1.Relations.html#6152" class="Function">inv-z≤n</a> <a id="6219" href="plfa.part1.Relations.html#1183" class="InductiveConstructor">z≤n</a> <a id="6223" class="Symbol">=</a> <a id="6225" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
</pre>
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


#### Exercise `orderings` (practice) {#orderings}

Give an example of a preorder that is not a partial order.

<pre class="Agda"><a id="7731" class="Comment">-- Your code goes here</a>
</pre>
Give an example of a partial order that is not a total order.

<pre class="Agda"><a id="7830" class="Comment">-- Your code goes here</a>
</pre>
## Reflexivity

The first property to prove about comparison is that it is reflexive:
for any natural `n`, the relation `n ≤ n` holds.  We follow the
convention in the standard library and make the argument implicit,
as that will make it easier to invoke reflexivity:
<pre class="Agda"><a id="≤-refl"></a><a id="8134" href="plfa.part1.Relations.html#8134" class="Function">≤-refl</a> <a id="8141" class="Symbol">:</a> <a id="8143" class="Symbol">∀</a> <a id="8145" class="Symbol">{</a><a id="8146" href="plfa.part1.Relations.html#8146" class="Bound">n</a> <a id="8148" class="Symbol">:</a> <a id="8150" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="8151" class="Symbol">}</a>
    <a id="8157" class="Comment">-----</a>
  <a id="8165" class="Symbol">→</a> <a id="8167" href="plfa.part1.Relations.html#8146" class="Bound">n</a> <a id="8169" href="plfa.part1.Relations.html#1156" class="Datatype Operator">≤</a> <a id="8171" href="plfa.part1.Relations.html#8146" class="Bound">n</a>
<a id="8173" href="plfa.part1.Relations.html#8134" class="Function">≤-refl</a> <a id="8180" class="Symbol">{</a><a id="8181" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a><a id="8185" class="Symbol">}</a> <a id="8187" class="Symbol">=</a> <a id="8189" href="plfa.part1.Relations.html#1183" class="InductiveConstructor">z≤n</a>
<a id="8193" href="plfa.part1.Relations.html#8134" class="Function">≤-refl</a> <a id="8200" class="Symbol">{</a><a id="8201" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="8205" href="plfa.part1.Relations.html#8205" class="Bound">n</a><a id="8206" class="Symbol">}</a> <a id="8208" class="Symbol">=</a> <a id="8210" href="plfa.part1.Relations.html#1232" class="InductiveConstructor">s≤s</a> <a id="8214" href="plfa.part1.Relations.html#8134" class="Function">≤-refl</a>
</pre>The proof is a straightforward induction on the implicit argument `n`.
In the base case, `zero ≤ zero` holds by `z≤n`.  In the inductive
case, the inductive hypothesis `≤-refl {n}` gives us a proof of `n ≤
n`, and applying `s≤s` to that yields a proof of `suc n ≤ suc n`.

It is a good exercise to prove reflexivity interactively in Emacs,
using holes and the `C-c C-c`, `C-c C-,`, and `C-c C-r` commands.


## Transitivity

The second property to prove about comparison is that it is
transitive: for any naturals `m`, `n`, and `p`, if `m ≤ n` and `n ≤ p`
hold, then `m ≤ p` holds.  Again, `m`, `n`, and `p` are implicit:
<pre class="Agda"><a id="≤-trans"></a><a id="8855" href="plfa.part1.Relations.html#8855" class="Function">≤-trans</a> <a id="8863" class="Symbol">:</a> <a id="8865" class="Symbol">∀</a> <a id="8867" class="Symbol">{</a><a id="8868" href="plfa.part1.Relations.html#8868" class="Bound">m</a> <a id="8870" href="plfa.part1.Relations.html#8870" class="Bound">n</a> <a id="8872" href="plfa.part1.Relations.html#8872" class="Bound">p</a> <a id="8874" class="Symbol">:</a> <a id="8876" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="8877" class="Symbol">}</a>
  <a id="8881" class="Symbol">→</a> <a id="8883" href="plfa.part1.Relations.html#8868" class="Bound">m</a> <a id="8885" href="plfa.part1.Relations.html#1156" class="Datatype Operator">≤</a> <a id="8887" href="plfa.part1.Relations.html#8870" class="Bound">n</a>
  <a id="8891" class="Symbol">→</a> <a id="8893" href="plfa.part1.Relations.html#8870" class="Bound">n</a> <a id="8895" href="plfa.part1.Relations.html#1156" class="Datatype Operator">≤</a> <a id="8897" href="plfa.part1.Relations.html#8872" class="Bound">p</a>
    <a id="8903" class="Comment">-----</a>
  <a id="8911" class="Symbol">→</a> <a id="8913" href="plfa.part1.Relations.html#8868" class="Bound">m</a> <a id="8915" href="plfa.part1.Relations.html#1156" class="Datatype Operator">≤</a> <a id="8917" href="plfa.part1.Relations.html#8872" class="Bound">p</a>
<a id="8919" href="plfa.part1.Relations.html#8855" class="Function">≤-trans</a> <a id="8927" href="plfa.part1.Relations.html#1183" class="InductiveConstructor">z≤n</a>       <a id="8937" class="Symbol">_</a>          <a id="8948" class="Symbol">=</a>  <a id="8951" href="plfa.part1.Relations.html#1183" class="InductiveConstructor">z≤n</a>
<a id="8955" href="plfa.part1.Relations.html#8855" class="Function">≤-trans</a> <a id="8963" class="Symbol">(</a><a id="8964" href="plfa.part1.Relations.html#1232" class="InductiveConstructor">s≤s</a> <a id="8968" href="plfa.part1.Relations.html#8968" class="Bound">m≤n</a><a id="8971" class="Symbol">)</a> <a id="8973" class="Symbol">(</a><a id="8974" href="plfa.part1.Relations.html#1232" class="InductiveConstructor">s≤s</a> <a id="8978" href="plfa.part1.Relations.html#8978" class="Bound">n≤p</a><a id="8981" class="Symbol">)</a>  <a id="8984" class="Symbol">=</a>  <a id="8987" href="plfa.part1.Relations.html#1232" class="InductiveConstructor">s≤s</a> <a id="8991" class="Symbol">(</a><a id="8992" href="plfa.part1.Relations.html#8855" class="Function">≤-trans</a> <a id="9000" href="plfa.part1.Relations.html#8968" class="Bound">m≤n</a> <a id="9004" href="plfa.part1.Relations.html#8978" class="Bound">n≤p</a><a id="9007" class="Symbol">)</a>
</pre>Here the proof is by induction on the _evidence_ that `m ≤ n`.  In the
base case, the first inequality holds by `z≤n` and must show `zero ≤ p`,
which follows immediately by `z≤n`.  In this case, the fact that
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
<pre class="Agda"><a id="≤-trans′"></a><a id="9972" href="plfa.part1.Relations.html#9972" class="Function">≤-trans′</a> <a id="9981" class="Symbol">:</a> <a id="9983" class="Symbol">∀</a> <a id="9985" class="Symbol">(</a><a id="9986" href="plfa.part1.Relations.html#9986" class="Bound">m</a> <a id="9988" href="plfa.part1.Relations.html#9988" class="Bound">n</a> <a id="9990" href="plfa.part1.Relations.html#9990" class="Bound">p</a> <a id="9992" class="Symbol">:</a> <a id="9994" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="9995" class="Symbol">)</a>
  <a id="9999" class="Symbol">→</a> <a id="10001" href="plfa.part1.Relations.html#9986" class="Bound">m</a> <a id="10003" href="plfa.part1.Relations.html#1156" class="Datatype Operator">≤</a> <a id="10005" href="plfa.part1.Relations.html#9988" class="Bound">n</a>
  <a id="10009" class="Symbol">→</a> <a id="10011" href="plfa.part1.Relations.html#9988" class="Bound">n</a> <a id="10013" href="plfa.part1.Relations.html#1156" class="Datatype Operator">≤</a> <a id="10015" href="plfa.part1.Relations.html#9990" class="Bound">p</a>
    <a id="10021" class="Comment">-----</a>
  <a id="10029" class="Symbol">→</a> <a id="10031" href="plfa.part1.Relations.html#9986" class="Bound">m</a> <a id="10033" href="plfa.part1.Relations.html#1156" class="Datatype Operator">≤</a> <a id="10035" href="plfa.part1.Relations.html#9990" class="Bound">p</a>
<a id="10037" href="plfa.part1.Relations.html#9972" class="Function">≤-trans′</a> <a id="10046" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a>    <a id="10054" class="Symbol">_</a>       <a id="10062" class="Symbol">_</a>       <a id="10070" href="plfa.part1.Relations.html#1183" class="InductiveConstructor">z≤n</a>       <a id="10080" class="Symbol">_</a>          <a id="10091" class="Symbol">=</a>  <a id="10094" href="plfa.part1.Relations.html#1183" class="InductiveConstructor">z≤n</a>
<a id="10098" href="plfa.part1.Relations.html#9972" class="Function">≤-trans′</a> <a id="10107" class="Symbol">(</a><a id="10108" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="10112" href="plfa.part1.Relations.html#10112" class="Bound">m</a><a id="10113" class="Symbol">)</a> <a id="10115" class="Symbol">(</a><a id="10116" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="10120" href="plfa.part1.Relations.html#10120" class="Bound">n</a><a id="10121" class="Symbol">)</a> <a id="10123" class="Symbol">(</a><a id="10124" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="10128" href="plfa.part1.Relations.html#10128" class="Bound">p</a><a id="10129" class="Symbol">)</a> <a id="10131" class="Symbol">(</a><a id="10132" href="plfa.part1.Relations.html#1232" class="InductiveConstructor">s≤s</a> <a id="10136" href="plfa.part1.Relations.html#10136" class="Bound">m≤n</a><a id="10139" class="Symbol">)</a> <a id="10141" class="Symbol">(</a><a id="10142" href="plfa.part1.Relations.html#1232" class="InductiveConstructor">s≤s</a> <a id="10146" href="plfa.part1.Relations.html#10146" class="Bound">n≤p</a><a id="10149" class="Symbol">)</a>  <a id="10152" class="Symbol">=</a>  <a id="10155" href="plfa.part1.Relations.html#1232" class="InductiveConstructor">s≤s</a> <a id="10159" class="Symbol">(</a><a id="10160" href="plfa.part1.Relations.html#9972" class="Function">≤-trans′</a> <a id="10169" href="plfa.part1.Relations.html#10112" class="Bound">m</a> <a id="10171" href="plfa.part1.Relations.html#10120" class="Bound">n</a> <a id="10173" href="plfa.part1.Relations.html#10128" class="Bound">p</a> <a id="10175" href="plfa.part1.Relations.html#10136" class="Bound">m≤n</a> <a id="10179" href="plfa.part1.Relations.html#10146" class="Bound">n≤p</a><a id="10182" class="Symbol">)</a>
</pre>One might argue that this is clearer or one might argue that the extra
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
antisymmetric: for all naturals `m` and `n`, if both `m ≤ n` and
`n ≤ m` hold, then `m ≡ n` holds:
<pre class="Agda"><a id="≤-antisym"></a><a id="10931" href="plfa.part1.Relations.html#10931" class="Function">≤-antisym</a> <a id="10941" class="Symbol">:</a> <a id="10943" class="Symbol">∀</a> <a id="10945" class="Symbol">{</a><a id="10946" href="plfa.part1.Relations.html#10946" class="Bound">m</a> <a id="10948" href="plfa.part1.Relations.html#10948" class="Bound">n</a> <a id="10950" class="Symbol">:</a> <a id="10952" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="10953" class="Symbol">}</a>
  <a id="10957" class="Symbol">→</a> <a id="10959" href="plfa.part1.Relations.html#10946" class="Bound">m</a> <a id="10961" href="plfa.part1.Relations.html#1156" class="Datatype Operator">≤</a> <a id="10963" href="plfa.part1.Relations.html#10948" class="Bound">n</a>
  <a id="10967" class="Symbol">→</a> <a id="10969" href="plfa.part1.Relations.html#10948" class="Bound">n</a> <a id="10971" href="plfa.part1.Relations.html#1156" class="Datatype Operator">≤</a> <a id="10973" href="plfa.part1.Relations.html#10946" class="Bound">m</a>
    <a id="10979" class="Comment">-----</a>
  <a id="10987" class="Symbol">→</a> <a id="10989" href="plfa.part1.Relations.html#10946" class="Bound">m</a> <a id="10991" href="Agda.Builtin.Equality.html#150" class="Datatype Operator">≡</a> <a id="10993" href="plfa.part1.Relations.html#10948" class="Bound">n</a>
<a id="10995" href="plfa.part1.Relations.html#10931" class="Function">≤-antisym</a> <a id="11005" href="plfa.part1.Relations.html#1183" class="InductiveConstructor">z≤n</a>       <a id="11015" href="plfa.part1.Relations.html#1183" class="InductiveConstructor">z≤n</a>        <a id="11026" class="Symbol">=</a>  <a id="11029" href="Agda.Builtin.Equality.html#207" class="InductiveConstructor">refl</a>
<a id="11034" href="plfa.part1.Relations.html#10931" class="Function">≤-antisym</a> <a id="11044" class="Symbol">(</a><a id="11045" href="plfa.part1.Relations.html#1232" class="InductiveConstructor">s≤s</a> <a id="11049" href="plfa.part1.Relations.html#11049" class="Bound">m≤n</a><a id="11052" class="Symbol">)</a> <a id="11054" class="Symbol">(</a><a id="11055" href="plfa.part1.Relations.html#1232" class="InductiveConstructor">s≤s</a> <a id="11059" href="plfa.part1.Relations.html#11059" class="Bound">n≤m</a><a id="11062" class="Symbol">)</a>  <a id="11065" class="Symbol">=</a>  <a id="11068" href="Relation.Binary.PropositionalEquality.Core.html#1139" class="Function">cong</a> <a id="11073" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="11077" class="Symbol">(</a><a id="11078" href="plfa.part1.Relations.html#10931" class="Function">≤-antisym</a> <a id="11088" href="plfa.part1.Relations.html#11049" class="Bound">m≤n</a> <a id="11092" href="plfa.part1.Relations.html#11059" class="Bound">n≤m</a><a id="11095" class="Symbol">)</a>
</pre>Again, the proof is by induction over the evidence that `m ≤ n`
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

#### Exercise `≤-antisym-cases` (practice) {#leq-antisym-cases}

The above proof omits cases where one argument is `z≤n` and one
argument is `s≤s`.  Why is it ok to omit them?

<pre class="Agda"><a id="11905" class="Comment">-- Your code goes here</a>
</pre>

## Total

The fourth property to prove about comparison is that it is total:
for any naturals `m` and `n` either `m ≤ n` or `n ≤ m`, or both if
`m` and `n` are equal.

We specify what it means for inequality to be total:
<pre class="Agda"><a id="12163" class="Keyword">data</a> <a id="Total"></a><a id="12168" href="plfa.part1.Relations.html#12168" class="Datatype">Total</a> <a id="12174" class="Symbol">(</a><a id="12175" href="plfa.part1.Relations.html#12175" class="Bound">m</a> <a id="12177" href="plfa.part1.Relations.html#12177" class="Bound">n</a> <a id="12179" class="Symbol">:</a> <a id="12181" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="12182" class="Symbol">)</a> <a id="12184" class="Symbol">:</a> <a id="12186" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="12190" class="Keyword">where</a>

  <a id="Total.forward"></a><a id="12199" href="plfa.part1.Relations.html#12199" class="InductiveConstructor">forward</a> <a id="12207" class="Symbol">:</a>
      <a id="12215" href="plfa.part1.Relations.html#12175" class="Bound">m</a> <a id="12217" href="plfa.part1.Relations.html#1156" class="Datatype Operator">≤</a> <a id="12219" href="plfa.part1.Relations.html#12177" class="Bound">n</a>
      <a id="12227" class="Comment">---------</a>
    <a id="12241" class="Symbol">→</a> <a id="12243" href="plfa.part1.Relations.html#12168" class="Datatype">Total</a> <a id="12249" href="plfa.part1.Relations.html#12175" class="Bound">m</a> <a id="12251" href="plfa.part1.Relations.html#12177" class="Bound">n</a>

  <a id="Total.flipped"></a><a id="12256" href="plfa.part1.Relations.html#12256" class="InductiveConstructor">flipped</a> <a id="12264" class="Symbol">:</a>
      <a id="12272" href="plfa.part1.Relations.html#12177" class="Bound">n</a> <a id="12274" href="plfa.part1.Relations.html#1156" class="Datatype Operator">≤</a> <a id="12276" href="plfa.part1.Relations.html#12175" class="Bound">m</a>
      <a id="12284" class="Comment">---------</a>
    <a id="12298" class="Symbol">→</a> <a id="12300" href="plfa.part1.Relations.html#12168" class="Datatype">Total</a> <a id="12306" href="plfa.part1.Relations.html#12175" class="Bound">m</a> <a id="12308" href="plfa.part1.Relations.html#12177" class="Bound">n</a>
</pre>Evidence that `Total m n` holds is either of the form
`forward m≤n` or `flipped n≤m`, where `m≤n` and `n≤m` are
evidence of `m ≤ n` and `n ≤ m` respectively.

(For those familiar with logic, the above definition
could also be written as a disjunction. Disjunctions will
be introduced in Chapter [Connectives](/Connectives/).)

This is our first use of a datatype with _parameters_,
in this case `m` and `n`.  It is equivalent to the following
indexed datatype:
<pre class="Agda"><a id="12783" class="Keyword">data</a> <a id="Total′"></a><a id="12788" href="plfa.part1.Relations.html#12788" class="Datatype">Total′</a> <a id="12795" class="Symbol">:</a> <a id="12797" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="12799" class="Symbol">→</a> <a id="12801" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="12803" class="Symbol">→</a> <a id="12805" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="12809" class="Keyword">where</a>

  <a id="Total′.forward′"></a><a id="12818" href="plfa.part1.Relations.html#12818" class="InductiveConstructor">forward′</a> <a id="12827" class="Symbol">:</a> <a id="12829" class="Symbol">∀</a> <a id="12831" class="Symbol">{</a><a id="12832" href="plfa.part1.Relations.html#12832" class="Bound">m</a> <a id="12834" href="plfa.part1.Relations.html#12834" class="Bound">n</a> <a id="12836" class="Symbol">:</a> <a id="12838" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="12839" class="Symbol">}</a>
    <a id="12845" class="Symbol">→</a> <a id="12847" href="plfa.part1.Relations.html#12832" class="Bound">m</a> <a id="12849" href="plfa.part1.Relations.html#1156" class="Datatype Operator">≤</a> <a id="12851" href="plfa.part1.Relations.html#12834" class="Bound">n</a>
      <a id="12859" class="Comment">----------</a>
    <a id="12874" class="Symbol">→</a> <a id="12876" href="plfa.part1.Relations.html#12788" class="Datatype">Total′</a> <a id="12883" href="plfa.part1.Relations.html#12832" class="Bound">m</a> <a id="12885" href="plfa.part1.Relations.html#12834" class="Bound">n</a>

  <a id="Total′.flipped′"></a><a id="12890" href="plfa.part1.Relations.html#12890" class="InductiveConstructor">flipped′</a> <a id="12899" class="Symbol">:</a> <a id="12901" class="Symbol">∀</a> <a id="12903" class="Symbol">{</a><a id="12904" href="plfa.part1.Relations.html#12904" class="Bound">m</a> <a id="12906" href="plfa.part1.Relations.html#12906" class="Bound">n</a> <a id="12908" class="Symbol">:</a> <a id="12910" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="12911" class="Symbol">}</a>
    <a id="12917" class="Symbol">→</a> <a id="12919" href="plfa.part1.Relations.html#12906" class="Bound">n</a> <a id="12921" href="plfa.part1.Relations.html#1156" class="Datatype Operator">≤</a> <a id="12923" href="plfa.part1.Relations.html#12904" class="Bound">m</a>
      <a id="12931" class="Comment">----------</a>
    <a id="12946" class="Symbol">→</a> <a id="12948" href="plfa.part1.Relations.html#12788" class="Datatype">Total′</a> <a id="12955" href="plfa.part1.Relations.html#12904" class="Bound">m</a> <a id="12957" href="plfa.part1.Relations.html#12906" class="Bound">n</a>
</pre>Each parameter of the type translates as an implicit parameter of each
constructor.  Unlike an indexed datatype, where the indexes can vary
(as in `zero ≤ n` and `suc m ≤ suc n`), in a parameterised datatype
the parameters must always be the same (as in `Total m n`).
Parameterised declarations are shorter, easier to read, and
occasionally aid Agda's termination checker, so we will use them in
preference to indexed types when possible.

With that preliminary out of the way, we specify and prove totality:
<pre class="Agda"><a id="≤-total"></a><a id="13480" href="plfa.part1.Relations.html#13480" class="Function">≤-total</a> <a id="13488" class="Symbol">:</a> <a id="13490" class="Symbol">∀</a> <a id="13492" class="Symbol">(</a><a id="13493" href="plfa.part1.Relations.html#13493" class="Bound">m</a> <a id="13495" href="plfa.part1.Relations.html#13495" class="Bound">n</a> <a id="13497" class="Symbol">:</a> <a id="13499" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="13500" class="Symbol">)</a> <a id="13502" class="Symbol">→</a> <a id="13504" href="plfa.part1.Relations.html#12168" class="Datatype">Total</a> <a id="13510" href="plfa.part1.Relations.html#13493" class="Bound">m</a> <a id="13512" href="plfa.part1.Relations.html#13495" class="Bound">n</a>
<a id="13514" href="plfa.part1.Relations.html#13480" class="Function">≤-total</a> <a id="13522" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a>    <a id="13530" href="plfa.part1.Relations.html#13530" class="Bound">n</a>                         <a id="13556" class="Symbol">=</a>  <a id="13559" href="plfa.part1.Relations.html#12199" class="InductiveConstructor">forward</a> <a id="13567" href="plfa.part1.Relations.html#1183" class="InductiveConstructor">z≤n</a>
<a id="13571" href="plfa.part1.Relations.html#13480" class="Function">≤-total</a> <a id="13579" class="Symbol">(</a><a id="13580" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="13584" href="plfa.part1.Relations.html#13584" class="Bound">m</a><a id="13585" class="Symbol">)</a> <a id="13587" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a>                      <a id="13613" class="Symbol">=</a>  <a id="13616" href="plfa.part1.Relations.html#12256" class="InductiveConstructor">flipped</a> <a id="13624" href="plfa.part1.Relations.html#1183" class="InductiveConstructor">z≤n</a>
<a id="13628" href="plfa.part1.Relations.html#13480" class="Function">≤-total</a> <a id="13636" class="Symbol">(</a><a id="13637" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="13641" href="plfa.part1.Relations.html#13641" class="Bound">m</a><a id="13642" class="Symbol">)</a> <a id="13644" class="Symbol">(</a><a id="13645" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="13649" href="plfa.part1.Relations.html#13649" class="Bound">n</a><a id="13650" class="Symbol">)</a> <a id="13652" class="Keyword">with</a> <a id="13657" href="plfa.part1.Relations.html#13480" class="Function">≤-total</a> <a id="13665" href="plfa.part1.Relations.html#13641" class="Bound">m</a> <a id="13667" href="plfa.part1.Relations.html#13649" class="Bound">n</a>
<a id="13669" class="Symbol">...</a>                        <a id="13696" class="Symbol">|</a> <a id="13698" href="plfa.part1.Relations.html#12199" class="InductiveConstructor">forward</a> <a id="13706" href="plfa.part1.Relations.html#13706" class="Bound">m≤n</a>  <a id="13711" class="Symbol">=</a>  <a id="13714" href="plfa.part1.Relations.html#12199" class="InductiveConstructor">forward</a> <a id="13722" class="Symbol">(</a><a id="13723" href="plfa.part1.Relations.html#1232" class="InductiveConstructor">s≤s</a> <a id="13727" href="plfa.part1.Relations.html#13706" class="Bound">m≤n</a><a id="13730" class="Symbol">)</a>
<a id="13732" class="Symbol">...</a>                        <a id="13759" class="Symbol">|</a> <a id="13761" href="plfa.part1.Relations.html#12256" class="InductiveConstructor">flipped</a> <a id="13769" href="plfa.part1.Relations.html#13769" class="Bound">n≤m</a>  <a id="13774" class="Symbol">=</a>  <a id="13777" href="plfa.part1.Relations.html#12256" class="InductiveConstructor">flipped</a> <a id="13785" class="Symbol">(</a><a id="13786" href="plfa.part1.Relations.html#1232" class="InductiveConstructor">s≤s</a> <a id="13790" href="plfa.part1.Relations.html#13769" class="Bound">n≤m</a><a id="13793" class="Symbol">)</a>
</pre>In this case the proof is by induction over both the first
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
<pre class="Agda"><a id="≤-total′"></a><a id="15289" href="plfa.part1.Relations.html#15289" class="Function">≤-total′</a> <a id="15298" class="Symbol">:</a> <a id="15300" class="Symbol">∀</a> <a id="15302" class="Symbol">(</a><a id="15303" href="plfa.part1.Relations.html#15303" class="Bound">m</a> <a id="15305" href="plfa.part1.Relations.html#15305" class="Bound">n</a> <a id="15307" class="Symbol">:</a> <a id="15309" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="15310" class="Symbol">)</a> <a id="15312" class="Symbol">→</a> <a id="15314" href="plfa.part1.Relations.html#12168" class="Datatype">Total</a> <a id="15320" href="plfa.part1.Relations.html#15303" class="Bound">m</a> <a id="15322" href="plfa.part1.Relations.html#15305" class="Bound">n</a>
<a id="15324" href="plfa.part1.Relations.html#15289" class="Function">≤-total′</a> <a id="15333" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a>    <a id="15341" href="plfa.part1.Relations.html#15341" class="Bound">n</a>        <a id="15350" class="Symbol">=</a>  <a id="15353" href="plfa.part1.Relations.html#12199" class="InductiveConstructor">forward</a> <a id="15361" href="plfa.part1.Relations.html#1183" class="InductiveConstructor">z≤n</a>
<a id="15365" href="plfa.part1.Relations.html#15289" class="Function">≤-total′</a> <a id="15374" class="Symbol">(</a><a id="15375" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="15379" href="plfa.part1.Relations.html#15379" class="Bound">m</a><a id="15380" class="Symbol">)</a> <a id="15382" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a>     <a id="15391" class="Symbol">=</a>  <a id="15394" href="plfa.part1.Relations.html#12256" class="InductiveConstructor">flipped</a> <a id="15402" href="plfa.part1.Relations.html#1183" class="InductiveConstructor">z≤n</a>
<a id="15406" href="plfa.part1.Relations.html#15289" class="Function">≤-total′</a> <a id="15415" class="Symbol">(</a><a id="15416" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="15420" href="plfa.part1.Relations.html#15420" class="Bound">m</a><a id="15421" class="Symbol">)</a> <a id="15423" class="Symbol">(</a><a id="15424" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="15428" href="plfa.part1.Relations.html#15428" class="Bound">n</a><a id="15429" class="Symbol">)</a>  <a id="15432" class="Symbol">=</a>  <a id="15435" href="plfa.part1.Relations.html#15467" class="Function">helper</a> <a id="15442" class="Symbol">(</a><a id="15443" href="plfa.part1.Relations.html#15289" class="Function">≤-total′</a> <a id="15452" href="plfa.part1.Relations.html#15420" class="Bound">m</a> <a id="15454" href="plfa.part1.Relations.html#15428" class="Bound">n</a><a id="15455" class="Symbol">)</a>
  <a id="15459" class="Keyword">where</a>
  <a id="15467" href="plfa.part1.Relations.html#15467" class="Function">helper</a> <a id="15474" class="Symbol">:</a> <a id="15476" href="plfa.part1.Relations.html#12168" class="Datatype">Total</a> <a id="15482" href="plfa.part1.Relations.html#15420" class="Bound">m</a> <a id="15484" href="plfa.part1.Relations.html#15428" class="Bound">n</a> <a id="15486" class="Symbol">→</a> <a id="15488" href="plfa.part1.Relations.html#12168" class="Datatype">Total</a> <a id="15494" class="Symbol">(</a><a id="15495" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="15499" href="plfa.part1.Relations.html#15420" class="Bound">m</a><a id="15500" class="Symbol">)</a> <a id="15502" class="Symbol">(</a><a id="15503" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="15507" href="plfa.part1.Relations.html#15428" class="Bound">n</a><a id="15508" class="Symbol">)</a>
  <a id="15512" href="plfa.part1.Relations.html#15467" class="Function">helper</a> <a id="15519" class="Symbol">(</a><a id="15520" href="plfa.part1.Relations.html#12199" class="InductiveConstructor">forward</a> <a id="15528" href="plfa.part1.Relations.html#15528" class="Bound">m≤n</a><a id="15531" class="Symbol">)</a>  <a id="15534" class="Symbol">=</a>  <a id="15537" href="plfa.part1.Relations.html#12199" class="InductiveConstructor">forward</a> <a id="15545" class="Symbol">(</a><a id="15546" href="plfa.part1.Relations.html#1232" class="InductiveConstructor">s≤s</a> <a id="15550" href="plfa.part1.Relations.html#15528" class="Bound">m≤n</a><a id="15553" class="Symbol">)</a>
  <a id="15557" href="plfa.part1.Relations.html#15467" class="Function">helper</a> <a id="15564" class="Symbol">(</a><a id="15565" href="plfa.part1.Relations.html#12256" class="InductiveConstructor">flipped</a> <a id="15573" href="plfa.part1.Relations.html#15573" class="Bound">n≤m</a><a id="15576" class="Symbol">)</a>  <a id="15579" class="Symbol">=</a>  <a id="15582" href="plfa.part1.Relations.html#12256" class="InductiveConstructor">flipped</a> <a id="15590" class="Symbol">(</a><a id="15591" href="plfa.part1.Relations.html#1232" class="InductiveConstructor">s≤s</a> <a id="15595" href="plfa.part1.Relations.html#15573" class="Bound">n≤m</a><a id="15598" class="Symbol">)</a>
</pre>This is also our first use of a `where` clause in Agda.  The keyword `where` is
followed by one or more definitions, which must be indented.  Any variables
bound on the left-hand side of the preceding equation (in this case, `m` and
`n`) are in scope within the nested definition, and any identifiers bound in the
nested definition (in this case, `helper`) are in scope in the right-hand side
of the preceding equation.

If both arguments are equal, then both cases hold and we could return evidence
of either.  In the code above we return the forward case, but there is a
variant that returns the flipped case:
<pre class="Agda"><a id="≤-total″"></a><a id="16224" href="plfa.part1.Relations.html#16224" class="Function">≤-total″</a> <a id="16233" class="Symbol">:</a> <a id="16235" class="Symbol">∀</a> <a id="16237" class="Symbol">(</a><a id="16238" href="plfa.part1.Relations.html#16238" class="Bound">m</a> <a id="16240" href="plfa.part1.Relations.html#16240" class="Bound">n</a> <a id="16242" class="Symbol">:</a> <a id="16244" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="16245" class="Symbol">)</a> <a id="16247" class="Symbol">→</a> <a id="16249" href="plfa.part1.Relations.html#12168" class="Datatype">Total</a> <a id="16255" href="plfa.part1.Relations.html#16238" class="Bound">m</a> <a id="16257" href="plfa.part1.Relations.html#16240" class="Bound">n</a>
<a id="16259" href="plfa.part1.Relations.html#16224" class="Function">≤-total″</a> <a id="16268" href="plfa.part1.Relations.html#16268" class="Bound">m</a>       <a id="16276" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a>                      <a id="16302" class="Symbol">=</a>  <a id="16305" href="plfa.part1.Relations.html#12256" class="InductiveConstructor">flipped</a> <a id="16313" href="plfa.part1.Relations.html#1183" class="InductiveConstructor">z≤n</a>
<a id="16317" href="plfa.part1.Relations.html#16224" class="Function">≤-total″</a> <a id="16326" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a>    <a id="16334" class="Symbol">(</a><a id="16335" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="16339" href="plfa.part1.Relations.html#16339" class="Bound">n</a><a id="16340" class="Symbol">)</a>                   <a id="16360" class="Symbol">=</a>  <a id="16363" href="plfa.part1.Relations.html#12199" class="InductiveConstructor">forward</a> <a id="16371" href="plfa.part1.Relations.html#1183" class="InductiveConstructor">z≤n</a>
<a id="16375" href="plfa.part1.Relations.html#16224" class="Function">≤-total″</a> <a id="16384" class="Symbol">(</a><a id="16385" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="16389" href="plfa.part1.Relations.html#16389" class="Bound">m</a><a id="16390" class="Symbol">)</a> <a id="16392" class="Symbol">(</a><a id="16393" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="16397" href="plfa.part1.Relations.html#16397" class="Bound">n</a><a id="16398" class="Symbol">)</a> <a id="16400" class="Keyword">with</a> <a id="16405" href="plfa.part1.Relations.html#16224" class="Function">≤-total″</a> <a id="16414" href="plfa.part1.Relations.html#16389" class="Bound">m</a> <a id="16416" href="plfa.part1.Relations.html#16397" class="Bound">n</a>
<a id="16418" class="Symbol">...</a>                         <a id="16446" class="Symbol">|</a> <a id="16448" href="plfa.part1.Relations.html#12199" class="InductiveConstructor">forward</a> <a id="16456" href="plfa.part1.Relations.html#16456" class="Bound">m≤n</a>  <a id="16461" class="Symbol">=</a>  <a id="16464" href="plfa.part1.Relations.html#12199" class="InductiveConstructor">forward</a> <a id="16472" class="Symbol">(</a><a id="16473" href="plfa.part1.Relations.html#1232" class="InductiveConstructor">s≤s</a> <a id="16477" href="plfa.part1.Relations.html#16456" class="Bound">m≤n</a><a id="16480" class="Symbol">)</a>
<a id="16482" class="Symbol">...</a>                         <a id="16510" class="Symbol">|</a> <a id="16512" href="plfa.part1.Relations.html#12256" class="InductiveConstructor">flipped</a> <a id="16520" href="plfa.part1.Relations.html#16520" class="Bound">n≤m</a>  <a id="16525" class="Symbol">=</a>  <a id="16528" href="plfa.part1.Relations.html#12256" class="InductiveConstructor">flipped</a> <a id="16536" class="Symbol">(</a><a id="16537" href="plfa.part1.Relations.html#1232" class="InductiveConstructor">s≤s</a> <a id="16541" href="plfa.part1.Relations.html#16520" class="Bound">n≤m</a><a id="16544" class="Symbol">)</a>
</pre>It differs from the original code in that it pattern
matches on the second argument before the first argument.


## Monotonicity

If one bumps into both an operator and an ordering at a party, one may ask if
the operator is _monotonic_ with regard to the ordering.  For example, addition
is monotonic with regard to inequality, meaning:

    ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q

The proof is straightforward using the techniques we have learned, and is best
broken into three parts. First, we deal with the special case of showing
addition is monotonic on the right:
<pre class="Agda"><a id="+-monoʳ-≤"></a><a id="17137" href="plfa.part1.Relations.html#17137" class="Function">+-monoʳ-≤</a> <a id="17147" class="Symbol">:</a> <a id="17149" class="Symbol">∀</a> <a id="17151" class="Symbol">(</a><a id="17152" href="plfa.part1.Relations.html#17152" class="Bound">n</a> <a id="17154" href="plfa.part1.Relations.html#17154" class="Bound">p</a> <a id="17156" href="plfa.part1.Relations.html#17156" class="Bound">q</a> <a id="17158" class="Symbol">:</a> <a id="17160" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="17161" class="Symbol">)</a>
  <a id="17165" class="Symbol">→</a> <a id="17167" href="plfa.part1.Relations.html#17154" class="Bound">p</a> <a id="17169" href="plfa.part1.Relations.html#1156" class="Datatype Operator">≤</a> <a id="17171" href="plfa.part1.Relations.html#17156" class="Bound">q</a>
    <a id="17177" class="Comment">-------------</a>
  <a id="17193" class="Symbol">→</a> <a id="17195" href="plfa.part1.Relations.html#17152" class="Bound">n</a> <a id="17197" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="17199" href="plfa.part1.Relations.html#17154" class="Bound">p</a> <a id="17201" href="plfa.part1.Relations.html#1156" class="Datatype Operator">≤</a> <a id="17203" href="plfa.part1.Relations.html#17152" class="Bound">n</a> <a id="17205" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="17207" href="plfa.part1.Relations.html#17156" class="Bound">q</a>
<a id="17209" href="plfa.part1.Relations.html#17137" class="Function">+-monoʳ-≤</a> <a id="17219" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a>    <a id="17227" href="plfa.part1.Relations.html#17227" class="Bound">p</a> <a id="17229" href="plfa.part1.Relations.html#17229" class="Bound">q</a> <a id="17231" href="plfa.part1.Relations.html#17231" class="Bound">p≤q</a>  <a id="17236" class="Symbol">=</a>  <a id="17239" href="plfa.part1.Relations.html#17231" class="Bound">p≤q</a>
<a id="17243" href="plfa.part1.Relations.html#17137" class="Function">+-monoʳ-≤</a> <a id="17253" class="Symbol">(</a><a id="17254" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="17258" href="plfa.part1.Relations.html#17258" class="Bound">n</a><a id="17259" class="Symbol">)</a> <a id="17261" href="plfa.part1.Relations.html#17261" class="Bound">p</a> <a id="17263" href="plfa.part1.Relations.html#17263" class="Bound">q</a> <a id="17265" href="plfa.part1.Relations.html#17265" class="Bound">p≤q</a>  <a id="17270" class="Symbol">=</a>  <a id="17273" href="plfa.part1.Relations.html#1232" class="InductiveConstructor">s≤s</a> <a id="17277" class="Symbol">(</a><a id="17278" href="plfa.part1.Relations.html#17137" class="Function">+-monoʳ-≤</a> <a id="17288" href="plfa.part1.Relations.html#17258" class="Bound">n</a> <a id="17290" href="plfa.part1.Relations.html#17261" class="Bound">p</a> <a id="17292" href="plfa.part1.Relations.html#17263" class="Bound">q</a> <a id="17294" href="plfa.part1.Relations.html#17265" class="Bound">p≤q</a><a id="17297" class="Symbol">)</a>
</pre>The proof is by induction on the first argument.

* _Base case_: The first argument is `zero` in which case
  `zero + p ≤ zero + q` simplifies to `p ≤ q`, the evidence
  for which is given by the argument `p≤q`.

* _Inductive case_: The first argument is `suc n`, in which case
  `suc n + p ≤ suc n + q` simplifies to `suc (n + p) ≤ suc (n + q)`.
  The inductive hypothesis `+-monoʳ-≤ n p q p≤q` establishes that
  `n + p ≤ n + q`, and our goal follows by applying `s≤s`.

Second, we deal with the special case of showing addition is
monotonic on the left. This follows from the previous
result and the commutativity of addition:
<pre class="Agda"><a id="+-monoˡ-≤"></a><a id="17941" href="plfa.part1.Relations.html#17941" class="Function">+-monoˡ-≤</a> <a id="17951" class="Symbol">:</a> <a id="17953" class="Symbol">∀</a> <a id="17955" class="Symbol">(</a><a id="17956" href="plfa.part1.Relations.html#17956" class="Bound">m</a> <a id="17958" href="plfa.part1.Relations.html#17958" class="Bound">n</a> <a id="17960" href="plfa.part1.Relations.html#17960" class="Bound">p</a> <a id="17962" class="Symbol">:</a> <a id="17964" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="17965" class="Symbol">)</a>
  <a id="17969" class="Symbol">→</a> <a id="17971" href="plfa.part1.Relations.html#17956" class="Bound">m</a> <a id="17973" href="plfa.part1.Relations.html#1156" class="Datatype Operator">≤</a> <a id="17975" href="plfa.part1.Relations.html#17958" class="Bound">n</a>
    <a id="17981" class="Comment">-------------</a>
  <a id="17997" class="Symbol">→</a> <a id="17999" href="plfa.part1.Relations.html#17956" class="Bound">m</a> <a id="18001" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="18003" href="plfa.part1.Relations.html#17960" class="Bound">p</a> <a id="18005" href="plfa.part1.Relations.html#1156" class="Datatype Operator">≤</a> <a id="18007" href="plfa.part1.Relations.html#17958" class="Bound">n</a> <a id="18009" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="18011" href="plfa.part1.Relations.html#17960" class="Bound">p</a>
<a id="18013" href="plfa.part1.Relations.html#17941" class="Function">+-monoˡ-≤</a> <a id="18023" href="plfa.part1.Relations.html#18023" class="Bound">m</a> <a id="18025" href="plfa.part1.Relations.html#18025" class="Bound">n</a> <a id="18027" href="plfa.part1.Relations.html#18027" class="Bound">p</a> <a id="18029" href="plfa.part1.Relations.html#18029" class="Bound">m≤n</a>  <a id="18034" class="Keyword">rewrite</a> <a id="18042" href="Data.Nat.Properties.html#13404" class="Function">+-comm</a> <a id="18049" href="plfa.part1.Relations.html#18023" class="Bound">m</a> <a id="18051" href="plfa.part1.Relations.html#18027" class="Bound">p</a> <a id="18053" class="Symbol">|</a> <a id="18055" href="Data.Nat.Properties.html#13404" class="Function">+-comm</a> <a id="18062" href="plfa.part1.Relations.html#18025" class="Bound">n</a> <a id="18064" href="plfa.part1.Relations.html#18027" class="Bound">p</a>  <a id="18067" class="Symbol">=</a> <a id="18069" href="plfa.part1.Relations.html#17137" class="Function">+-monoʳ-≤</a> <a id="18079" href="plfa.part1.Relations.html#18027" class="Bound">p</a> <a id="18081" href="plfa.part1.Relations.html#18023" class="Bound">m</a> <a id="18083" href="plfa.part1.Relations.html#18025" class="Bound">n</a> <a id="18085" href="plfa.part1.Relations.html#18029" class="Bound">m≤n</a>
</pre>Rewriting by `+-comm m p` and `+-comm n p` converts `m + p ≤ n + p` into
`p + m ≤ p + n`, which is proved by invoking `+-monoʳ-≤ p m n m≤n`.

Third, we combine the two previous results:
<pre class="Agda"><a id="+-mono-≤"></a><a id="18287" href="plfa.part1.Relations.html#18287" class="Function">+-mono-≤</a> <a id="18296" class="Symbol">:</a> <a id="18298" class="Symbol">∀</a> <a id="18300" class="Symbol">(</a><a id="18301" href="plfa.part1.Relations.html#18301" class="Bound">m</a> <a id="18303" href="plfa.part1.Relations.html#18303" class="Bound">n</a> <a id="18305" href="plfa.part1.Relations.html#18305" class="Bound">p</a> <a id="18307" href="plfa.part1.Relations.html#18307" class="Bound">q</a> <a id="18309" class="Symbol">:</a> <a id="18311" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="18312" class="Symbol">)</a>
  <a id="18316" class="Symbol">→</a> <a id="18318" href="plfa.part1.Relations.html#18301" class="Bound">m</a> <a id="18320" href="plfa.part1.Relations.html#1156" class="Datatype Operator">≤</a> <a id="18322" href="plfa.part1.Relations.html#18303" class="Bound">n</a>
  <a id="18326" class="Symbol">→</a> <a id="18328" href="plfa.part1.Relations.html#18305" class="Bound">p</a> <a id="18330" href="plfa.part1.Relations.html#1156" class="Datatype Operator">≤</a> <a id="18332" href="plfa.part1.Relations.html#18307" class="Bound">q</a>
    <a id="18338" class="Comment">-------------</a>
  <a id="18354" class="Symbol">→</a> <a id="18356" href="plfa.part1.Relations.html#18301" class="Bound">m</a> <a id="18358" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="18360" href="plfa.part1.Relations.html#18305" class="Bound">p</a> <a id="18362" href="plfa.part1.Relations.html#1156" class="Datatype Operator">≤</a> <a id="18364" href="plfa.part1.Relations.html#18303" class="Bound">n</a> <a id="18366" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="18368" href="plfa.part1.Relations.html#18307" class="Bound">q</a>
<a id="18370" href="plfa.part1.Relations.html#18287" class="Function">+-mono-≤</a> <a id="18379" href="plfa.part1.Relations.html#18379" class="Bound">m</a> <a id="18381" href="plfa.part1.Relations.html#18381" class="Bound">n</a> <a id="18383" href="plfa.part1.Relations.html#18383" class="Bound">p</a> <a id="18385" href="plfa.part1.Relations.html#18385" class="Bound">q</a> <a id="18387" href="plfa.part1.Relations.html#18387" class="Bound">m≤n</a> <a id="18391" href="plfa.part1.Relations.html#18391" class="Bound">p≤q</a>  <a id="18396" class="Symbol">=</a>  <a id="18399" href="plfa.part1.Relations.html#8855" class="Function">≤-trans</a> <a id="18407" class="Symbol">(</a><a id="18408" href="plfa.part1.Relations.html#17941" class="Function">+-monoˡ-≤</a> <a id="18418" href="plfa.part1.Relations.html#18379" class="Bound">m</a> <a id="18420" href="plfa.part1.Relations.html#18381" class="Bound">n</a> <a id="18422" href="plfa.part1.Relations.html#18383" class="Bound">p</a> <a id="18424" href="plfa.part1.Relations.html#18387" class="Bound">m≤n</a><a id="18427" class="Symbol">)</a> <a id="18429" class="Symbol">(</a><a id="18430" href="plfa.part1.Relations.html#17137" class="Function">+-monoʳ-≤</a> <a id="18440" href="plfa.part1.Relations.html#18381" class="Bound">n</a> <a id="18442" href="plfa.part1.Relations.html#18383" class="Bound">p</a> <a id="18444" href="plfa.part1.Relations.html#18385" class="Bound">q</a> <a id="18446" href="plfa.part1.Relations.html#18391" class="Bound">p≤q</a><a id="18449" class="Symbol">)</a>
</pre>Invoking `+-monoˡ-≤ m n p m≤n` proves `m + p ≤ n + p` and invoking
`+-monoʳ-≤ n p q p≤q` proves `n + p ≤ n + q`, and combining these with
transitivity proves `m + p ≤ n + q`, as was to be shown.


#### Exercise `*-mono-≤` (stretch)

Show that multiplication is monotonic with regard to inequality.

<pre class="Agda"><a id="18762" class="Comment">-- Your code goes here</a>
</pre>

## Strict inequality {#strict-inequality}

We can define strict inequality similarly to inequality:
<pre class="Agda"><a id="18899" class="Keyword">infix</a> <a id="18905" class="Number">4</a> <a id="18907" href="plfa.part1.Relations.html#18917" class="Datatype Operator">_&lt;_</a>

<a id="18912" class="Keyword">data</a> <a id="_&lt;_"></a><a id="18917" href="plfa.part1.Relations.html#18917" class="Datatype Operator">_&lt;_</a> <a id="18921" class="Symbol">:</a> <a id="18923" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="18925" class="Symbol">→</a> <a id="18927" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="18929" class="Symbol">→</a> <a id="18931" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="18935" class="Keyword">where</a>

  <a id="_&lt;_.z&lt;s"></a><a id="18944" href="plfa.part1.Relations.html#18944" class="InductiveConstructor">z&lt;s</a> <a id="18948" class="Symbol">:</a> <a id="18950" class="Symbol">∀</a> <a id="18952" class="Symbol">{</a><a id="18953" href="plfa.part1.Relations.html#18953" class="Bound">n</a> <a id="18955" class="Symbol">:</a> <a id="18957" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="18958" class="Symbol">}</a>
      <a id="18966" class="Comment">------------</a>
    <a id="18983" class="Symbol">→</a> <a id="18985" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a> <a id="18990" href="plfa.part1.Relations.html#18917" class="Datatype Operator">&lt;</a> <a id="18992" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="18996" href="plfa.part1.Relations.html#18953" class="Bound">n</a>

  <a id="_&lt;_.s&lt;s"></a><a id="19001" href="plfa.part1.Relations.html#19001" class="InductiveConstructor">s&lt;s</a> <a id="19005" class="Symbol">:</a> <a id="19007" class="Symbol">∀</a> <a id="19009" class="Symbol">{</a><a id="19010" href="plfa.part1.Relations.html#19010" class="Bound">m</a> <a id="19012" href="plfa.part1.Relations.html#19012" class="Bound">n</a> <a id="19014" class="Symbol">:</a> <a id="19016" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="19017" class="Symbol">}</a>
    <a id="19023" class="Symbol">→</a> <a id="19025" href="plfa.part1.Relations.html#19010" class="Bound">m</a> <a id="19027" href="plfa.part1.Relations.html#18917" class="Datatype Operator">&lt;</a> <a id="19029" href="plfa.part1.Relations.html#19012" class="Bound">n</a>
      <a id="19037" class="Comment">-------------</a>
    <a id="19055" class="Symbol">→</a> <a id="19057" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="19061" href="plfa.part1.Relations.html#19010" class="Bound">m</a> <a id="19063" href="plfa.part1.Relations.html#18917" class="Datatype Operator">&lt;</a> <a id="19065" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="19069" href="plfa.part1.Relations.html#19012" class="Bound">n</a>
</pre>The key difference is that zero is less than the successor of an
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
Chapter [Negation](/Negation/).

It is straightforward to show that `suc m ≤ n` implies `m < n`,
and conversely.  One can then give an alternative derivation of the
properties of strict inequality, such as transitivity, by
exploiting the corresponding properties of inequality.

#### Exercise `<-trans` (recommended) {#less-trans}

Show that strict inequality is transitive. Use a direct proof. (A later
exercise exploits the relation between < and ≤.)

<pre class="Agda"><a id="20302" class="Comment">-- Your code goes here</a>
</pre>
#### Exercise `trichotomy` (practice) {#trichotomy}

Show that strict inequality satisfies a weak version of trichotomy, in
the sense that for any `m` and `n` that one of the following holds:
* `m < n`,
* `m ≡ n`, or
* `m > n`.

Define `m > n` to be the same as `n < m`.
You will need a suitable data declaration,
similar to that used for totality.
(We will show that the three cases are exclusive after we introduce
[negation](/Negation/).)

<pre class="Agda"><a id="20781" class="Comment">-- Your code goes here</a>
</pre>
#### Exercise `+-mono-<` (practice) {#plus-mono-less}

Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.

<pre class="Agda"><a id="21005" class="Comment">-- Your code goes here</a>
</pre>
#### Exercise `≤→<, <→≤` (recommended) {#leq-iff-less}

Show that `suc m ≤ n` implies `m < n`, and conversely.

<pre class="Agda"><a id="21153" class="Comment">-- Your code goes here</a>
</pre>
#### Exercise `<-trans-revisited` (practice) {#less-trans-revisited}

Give an alternative proof that strict inequality is transitive,
using the relation between strict inequality and inequality and
the fact that inequality is transitive.

<pre class="Agda"><a id="21428" class="Comment">-- Your code goes here</a>
</pre>

## Even and odd

As a further example, let's specify even and odd numbers.  Inequality
and strict inequality are _binary relations_, while even and odd are
_unary relations_, sometimes called _predicates_:
<pre class="Agda"><a id="21671" class="Keyword">data</a> <a id="even"></a><a id="21676" href="plfa.part1.Relations.html#21676" class="Datatype">even</a> <a id="21681" class="Symbol">:</a> <a id="21683" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="21685" class="Symbol">→</a> <a id="21687" href="Agda.Primitive.html#388" class="Primitive">Set</a>
<a id="21691" class="Keyword">data</a> <a id="odd"></a><a id="21696" href="plfa.part1.Relations.html#21696" class="Datatype">odd</a>  <a id="21701" class="Symbol">:</a> <a id="21703" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a> <a id="21705" class="Symbol">→</a> <a id="21707" href="Agda.Primitive.html#388" class="Primitive">Set</a>

<a id="21712" class="Keyword">data</a> <a id="21717" href="plfa.part1.Relations.html#21676" class="Datatype">even</a> <a id="21722" class="Keyword">where</a>

  <a id="even.zero"></a><a id="21731" href="plfa.part1.Relations.html#21731" class="InductiveConstructor">zero</a> <a id="21736" class="Symbol">:</a>
      <a id="21744" class="Comment">---------</a>
      <a id="21760" href="plfa.part1.Relations.html#21676" class="Datatype">even</a> <a id="21765" href="Agda.Builtin.Nat.html#221" class="InductiveConstructor">zero</a>

  <a id="even.suc"></a><a id="21773" href="plfa.part1.Relations.html#21773" class="InductiveConstructor">suc</a>  <a id="21778" class="Symbol">:</a> <a id="21780" class="Symbol">∀</a> <a id="21782" class="Symbol">{</a><a id="21783" href="plfa.part1.Relations.html#21783" class="Bound">n</a> <a id="21785" class="Symbol">:</a> <a id="21787" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="21788" class="Symbol">}</a>
    <a id="21794" class="Symbol">→</a> <a id="21796" href="plfa.part1.Relations.html#21696" class="Datatype">odd</a> <a id="21800" href="plfa.part1.Relations.html#21783" class="Bound">n</a>
      <a id="21808" class="Comment">------------</a>
    <a id="21825" class="Symbol">→</a> <a id="21827" href="plfa.part1.Relations.html#21676" class="Datatype">even</a> <a id="21832" class="Symbol">(</a><a id="21833" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="21837" href="plfa.part1.Relations.html#21783" class="Bound">n</a><a id="21838" class="Symbol">)</a>

<a id="21841" class="Keyword">data</a> <a id="21846" href="plfa.part1.Relations.html#21696" class="Datatype">odd</a> <a id="21850" class="Keyword">where</a>

  <a id="odd.suc"></a><a id="21859" href="plfa.part1.Relations.html#21859" class="InductiveConstructor">suc</a>  <a id="21864" class="Symbol">:</a> <a id="21866" class="Symbol">∀</a> <a id="21868" class="Symbol">{</a><a id="21869" href="plfa.part1.Relations.html#21869" class="Bound">n</a> <a id="21871" class="Symbol">:</a> <a id="21873" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="21874" class="Symbol">}</a>
    <a id="21880" class="Symbol">→</a> <a id="21882" href="plfa.part1.Relations.html#21676" class="Datatype">even</a> <a id="21887" href="plfa.part1.Relations.html#21869" class="Bound">n</a>
      <a id="21895" class="Comment">-----------</a>
    <a id="21911" class="Symbol">→</a> <a id="21913" href="plfa.part1.Relations.html#21696" class="Datatype">odd</a> <a id="21917" class="Symbol">(</a><a id="21918" href="Agda.Builtin.Nat.html#234" class="InductiveConstructor">suc</a> <a id="21922" href="plfa.part1.Relations.html#21869" class="Bound">n</a><a id="21923" class="Symbol">)</a>
</pre>A number is even if it is zero or the successor of an odd number,
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
<pre class="Agda"><a id="e+e≡e"></a><a id="23087" href="plfa.part1.Relations.html#23087" class="Function">e+e≡e</a> <a id="23093" class="Symbol">:</a> <a id="23095" class="Symbol">∀</a> <a id="23097" class="Symbol">{</a><a id="23098" href="plfa.part1.Relations.html#23098" class="Bound">m</a> <a id="23100" href="plfa.part1.Relations.html#23100" class="Bound">n</a> <a id="23102" class="Symbol">:</a> <a id="23104" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="23105" class="Symbol">}</a>
  <a id="23109" class="Symbol">→</a> <a id="23111" href="plfa.part1.Relations.html#21676" class="Datatype">even</a> <a id="23116" href="plfa.part1.Relations.html#23098" class="Bound">m</a>
  <a id="23120" class="Symbol">→</a> <a id="23122" href="plfa.part1.Relations.html#21676" class="Datatype">even</a> <a id="23127" href="plfa.part1.Relations.html#23100" class="Bound">n</a>
    <a id="23133" class="Comment">------------</a>
  <a id="23148" class="Symbol">→</a> <a id="23150" href="plfa.part1.Relations.html#21676" class="Datatype">even</a> <a id="23155" class="Symbol">(</a><a id="23156" href="plfa.part1.Relations.html#23098" class="Bound">m</a> <a id="23158" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="23160" href="plfa.part1.Relations.html#23100" class="Bound">n</a><a id="23161" class="Symbol">)</a>

<a id="o+e≡o"></a><a id="23164" href="plfa.part1.Relations.html#23164" class="Function">o+e≡o</a> <a id="23170" class="Symbol">:</a> <a id="23172" class="Symbol">∀</a> <a id="23174" class="Symbol">{</a><a id="23175" href="plfa.part1.Relations.html#23175" class="Bound">m</a> <a id="23177" href="plfa.part1.Relations.html#23177" class="Bound">n</a> <a id="23179" class="Symbol">:</a> <a id="23181" href="Agda.Builtin.Nat.html#203" class="Datatype">ℕ</a><a id="23182" class="Symbol">}</a>
  <a id="23186" class="Symbol">→</a> <a id="23188" href="plfa.part1.Relations.html#21696" class="Datatype">odd</a> <a id="23192" href="plfa.part1.Relations.html#23175" class="Bound">m</a>
  <a id="23196" class="Symbol">→</a> <a id="23198" href="plfa.part1.Relations.html#21676" class="Datatype">even</a> <a id="23203" href="plfa.part1.Relations.html#23177" class="Bound">n</a>
    <a id="23209" class="Comment">-----------</a>
  <a id="23223" class="Symbol">→</a> <a id="23225" href="plfa.part1.Relations.html#21696" class="Datatype">odd</a> <a id="23229" class="Symbol">(</a><a id="23230" href="plfa.part1.Relations.html#23175" class="Bound">m</a> <a id="23232" href="Agda.Builtin.Nat.html#336" class="Primitive Operator">+</a> <a id="23234" href="plfa.part1.Relations.html#23177" class="Bound">n</a><a id="23235" class="Symbol">)</a>

<a id="23238" href="plfa.part1.Relations.html#23087" class="Function">e+e≡e</a> <a id="23244" href="plfa.part1.Relations.html#21731" class="InductiveConstructor">zero</a>     <a id="23253" href="plfa.part1.Relations.html#23253" class="Bound">en</a>  <a id="23257" class="Symbol">=</a>  <a id="23260" href="plfa.part1.Relations.html#23253" class="Bound">en</a>
<a id="23263" href="plfa.part1.Relations.html#23087" class="Function">e+e≡e</a> <a id="23269" class="Symbol">(</a><a id="23270" href="plfa.part1.Relations.html#21773" class="InductiveConstructor">suc</a> <a id="23274" href="plfa.part1.Relations.html#23274" class="Bound">om</a><a id="23276" class="Symbol">)</a> <a id="23278" href="plfa.part1.Relations.html#23278" class="Bound">en</a>  <a id="23282" class="Symbol">=</a>  <a id="23285" href="plfa.part1.Relations.html#21773" class="InductiveConstructor">suc</a> <a id="23289" class="Symbol">(</a><a id="23290" href="plfa.part1.Relations.html#23164" class="Function">o+e≡o</a> <a id="23296" href="plfa.part1.Relations.html#23274" class="Bound">om</a> <a id="23299" href="plfa.part1.Relations.html#23278" class="Bound">en</a><a id="23301" class="Symbol">)</a>

<a id="23304" href="plfa.part1.Relations.html#23164" class="Function">o+e≡o</a> <a id="23310" class="Symbol">(</a><a id="23311" href="plfa.part1.Relations.html#21859" class="InductiveConstructor">suc</a> <a id="23315" href="plfa.part1.Relations.html#23315" class="Bound">em</a><a id="23317" class="Symbol">)</a> <a id="23319" href="plfa.part1.Relations.html#23319" class="Bound">en</a>  <a id="23323" class="Symbol">=</a>  <a id="23326" href="plfa.part1.Relations.html#21859" class="InductiveConstructor">suc</a> <a id="23330" class="Symbol">(</a><a id="23331" href="plfa.part1.Relations.html#23087" class="Function">e+e≡e</a> <a id="23337" href="plfa.part1.Relations.html#23315" class="Bound">em</a> <a id="23340" href="plfa.part1.Relations.html#23319" class="Bound">en</a><a id="23342" class="Symbol">)</a>
</pre>Corresponding to the mutually recursive types, we use two mutually recursive
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

<pre class="Agda"><a id="24484" class="Comment">-- Your code goes here</a>
</pre>
#### Exercise `Bin-predicates` (stretch) {#Bin-predicates}

Recall that
Exercise [Bin](/Naturals/#Bin)
defines a datatype `Bin` of bitstrings representing natural numbers.
Representations are not unique due to leading zeros.
Hence, eleven may be represented by both of the following:

    ⟨⟩ I O I I
    ⟨⟩ O O I O I I

Define a predicate

    Can : Bin → Set

over all bitstrings that holds if the bitstring is canonical, meaning
it has no leading zeros; the first representation of eleven above is
canonical, and the second is not.  To define it, you will need an
auxiliary predicate

    One : Bin → Set

that holds only if the bitstring has a leading one.  A bitstring is
canonical if it has a leading one (representing a positive number) or
if it consists of a single zero (representing zero).

Show that increment preserves canonical bitstrings:

    Can b
    ------------
    Can (inc b)

Show that converting a natural to a bitstring always yields a
canonical bitstring:

    ----------
    Can (to n)

Show that converting a canonical bitstring to a natural
and back is the identity:

    Can b
    ---------------
    to (from b) ≡ b

Hint: For each of these, you may first need to prove related
properties of `One`. It may also help to prove the following:

    One b
    ----------
    1 ≤ from b

    1 ≤ n
    ---------------------
    to (2 * n) ≡ (to n) O

<pre class="Agda"><a id="25894" class="Comment">-- Your code goes here</a>
</pre>
## Standard library

Definitions similar to those in this chapter can be found in the standard library:
<pre class="Agda"><a id="26034" class="Keyword">import</a> <a id="26041" href="Data.Nat.html" class="Module">Data.Nat</a> <a id="26050" class="Keyword">using</a> <a id="26056" class="Symbol">(</a><a id="26057" href="Data.Nat.Base.html#1544" class="Datatype Operator">_≤_</a><a id="26060" class="Symbol">;</a> <a id="26062" href="Data.Nat.Base.html#1567" class="InductiveConstructor">z≤n</a><a id="26065" class="Symbol">;</a> <a id="26067" href="Data.Nat.Base.html#1609" class="InductiveConstructor">s≤s</a><a id="26070" class="Symbol">)</a>
<a id="26072" class="Keyword">import</a> <a id="26079" href="Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="26099" class="Keyword">using</a> <a id="26105" class="Symbol">(</a><a id="26106" href="Data.Nat.Properties.html#4574" class="Function">≤-refl</a><a id="26112" class="Symbol">;</a> <a id="26114" href="Data.Nat.Properties.html#4757" class="Function">≤-trans</a><a id="26121" class="Symbol">;</a> <a id="26123" href="Data.Nat.Properties.html#4624" class="Function">≤-antisym</a><a id="26132" class="Symbol">;</a> <a id="26134" href="Data.Nat.Properties.html#4869" class="Function">≤-total</a><a id="26141" class="Symbol">;</a>
                                  <a id="26177" href="Data.Nat.Properties.html#18035" class="Function">+-monoʳ-≤</a><a id="26186" class="Symbol">;</a> <a id="26188" href="Data.Nat.Properties.html#17945" class="Function">+-monoˡ-≤</a><a id="26197" class="Symbol">;</a> <a id="26199" href="Data.Nat.Properties.html#17789" class="Function">+-mono-≤</a><a id="26207" class="Symbol">)</a>
</pre>In the standard library, `≤-total` is formalised in terms of
disjunction (which we define in
Chapter [Connectives](/Connectives/)),
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
