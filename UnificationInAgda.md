<pre><style type="text/css">
    <!--
      body {
        color: #000000;
        background-color: #ffffff;
      }
      .agda2-highlight-bound-variable {
      }
      .agda2-highlight-catchall-clause {
        /* agda2-highlight-catchall-clause-face */
        background-color: #f5f5f5;
      }
      .agda2-highlight-datatype {
        /* agda2-highlight-datatype-face */
        color: #0000cd;
      }
      .agda2-highlight-field {
        /* agda2-highlight-field-face */
        color: #ee1289;
      }
      .agda2-highlight-function {
        /* agda2-highlight-function-face */
        color: #0000cd;
      }
      .agda2-highlight-inductive-constructor {
        /* agda2-highlight-inductive-constructor-face */
        color: #008b00;
      }
      .agda2-highlight-keyword {
        /* agda2-highlight-keyword-face */
        color: #cd6600;
      }
      .agda2-highlight-module {
        /* agda2-highlight-module-face */
        color: #a020f0;
      }
      .agda2-highlight-number {
        /* agda2-highlight-number-face */
        color: #a020f0;
      }
      .agda2-highlight-operator {
      }
      .agda2-highlight-postulate {
        /* agda2-highlight-postulate-face */
        color: #0000cd;
      }
      .agda2-highlight-primitive {
        /* agda2-highlight-primitive-face */
        color: #0000cd;
      }
      .agda2-highlight-primitive-type {
        /* agda2-highlight-primitive-type-face */
        color: #0000cd;
      }
      .agda2-highlight-record {
        /* agda2-highlight-record-face */
        color: #0000cd;
      }
      .agda2-highlight-symbol {
        /* agda2-highlight-symbol-face */
        color: #404040;
      }
      .agda2-highlight-unsolved-constraint {
        /* agda2-highlight-unsolved-constraint-face */
        background-color: #ffff00;
      }
      .agda2-highlight-unsolved-meta {
        /* agda2-highlight-unsolved-meta-face */
        background-color: #ffff00;
      }
      .comment {
        /* font-lock-comment-face */
        color: #b22222;
      }
      .comment-delimiter {
        /* font-lock-comment-delimiter-face */
        color: #b22222;
      }
      .default {
        /* default */
        color: #000000;
        background-color: #ffffff;
      }

      code {
        white-space: pre;
        background-color: #f6f8fa;
        display: inline-block
      }
      blockquote {
        padding: 0 1em;
        color: #6a737d;
        border-left: 0.25em solid #d1d5da;
      }

      a:hover {
        text-decoration: underline;
      }
    -->
    </style></pre># Unification in Agda

<pre><span class="agda2-highlight-keyword">module</span> <span class="agda2-highlight-module">UnificationInAgda</span> <span class="agda2-highlight-keyword">where</span>
</pre>
## Preface

Agda is a wonderful language and its unification engines are exemplary, practical, improve over time and work predictably well. Unification engines are one notable distiction between Agda and other dependently typed languages (such as Idris 1, Coq, Lean, etc). I'm saying "unification engines", because there are two of them:

- unification used for getting convenient and powerful pattern matching
- unification used for inferring values of implicit arguments

These are two completely distinct machineries. This tutorial covers only the latter, because the former is already elaborated in detail (and implemented) by Jesper Cockx: see his exceptionally well-writted [PhD thesis](https://jesper.sikanda.be/files/thesis-final-digital.pdf) -- it's an entire high-quality book. Section "3.6 Related work" of it shortly describes differences between the requirements for the two unifications engines.

This tutorial primarily targets

- users of Agda who want to understand how to write code to make more things inferrable
- a general audience curious about dependent types and what can be done with them
- people implementing powerful dependently typed languages (most of what is described here are tricks that I use in may day-to-day work (when it involves Agda) and I'd definitely want to see them available in languages that are yet to come)

Higher-order unification is not covered. It's a highly advanced topic and from the user's perspective diving into higher-order unification has a rather big cost/benefit ratio: I don't remember tweaking my code to fit it into the pattern fragment or doing anything else of this kind to help Agda unify things in the higher-order case. Agda would barely be usable without the built-in higher-order unification, but it's mostly invisible to the user and just works.

Analogously, no attempt to dissect Agda's internals is performed. Agda is well-designed enough not to force the user to worry about the peculiarities of the implementation (like when something gets postponed or in what order equations get solved). If you do want to learn about the internals, I recommend reading [Type checking in the presence of meta-variables](https://www.researchgate.net/publication/228571999_Type_checking_in_the_presence_of_meta-variables) and [Higher-Order Dynamic Pattern Unification for Dependent Types and Records](www.cse.chalmers.se/~abela/unif-sigma-long.pdf).

## Intro

Agda only infers values that are uniquely determined by the current context. I.e. Agda doesn't try to guess: it either fails to infer a value or infers the definitive one. Even though this makes the unification algorithm weaker than it could be, it also makes it reliable and predictable. Whenever Agda infers something, you can be sure that this is the thing that you wanted and not just a random guess that would be different if you provided more information to the type checker (but Agda does have a guessing machinery called [Agsy](https://agda.readthedocs.io/en/v2.6.0.1/tools/auto.html) that can be used interactively, so that no guessing needs to be done by the type checker and everything inferred is visible to the user).

We'll look into basics of type inference in Agda and then move to more advanced patterns. But first, some imports:

## Imports

<pre><span class="agda2-highlight-keyword">open</span> <span class="agda2-highlight-keyword">import</span> <span class="agda2-highlight-module">Level</span> <span class="agda2-highlight-keyword">renaming</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-primitive">suc</span> <span class="agda2-highlight-symbol">to</span> <span class="agda2-highlight-primitive">lsuc</span><span class="agda2-highlight-symbol">;</span> <span class="agda2-highlight-primitive">zero</span> <span class="agda2-highlight-symbol">to</span> <span class="agda2-highlight-primitive">lzero</span><span class="agda2-highlight-symbol">)</span>
<span class="agda2-highlight-keyword">open</span> <span class="agda2-highlight-keyword">import</span> <span class="agda2-highlight-module">Function.Core</span> <span class="agda2-highlight-keyword">using</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-operator"><span class="agda2-highlight-function">_&#8728;_</span></span><span class="agda2-highlight-symbol">;</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">_&#8715;_</span></span><span class="agda2-highlight-symbol">;</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">case_of_</span></span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-keyword">renaming</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-operator"><span class="agda2-highlight-function">_|&gt;_</span></span> <span class="agda2-highlight-symbol">to</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">_&amp;_</span></span><span class="agda2-highlight-symbol">)</span>
<span class="agda2-highlight-keyword">open</span> <span class="agda2-highlight-keyword">import</span> <span class="agda2-highlight-module">Relation.Binary.PropositionalEquality</span>
<span class="agda2-highlight-keyword">open</span> <span class="agda2-highlight-keyword">import</span> <span class="agda2-highlight-module">Data.Unit.Base</span> <span class="agda2-highlight-keyword">using</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-record">&#8868;</span><span class="agda2-highlight-symbol">;</span> <span class="agda2-highlight-inductive-constructor">tt</span><span class="agda2-highlight-symbol">)</span>
<span class="agda2-highlight-keyword">open</span> <span class="agda2-highlight-keyword">import</span> <span class="agda2-highlight-module">Data.Bool.Base</span> <span class="agda2-highlight-keyword">using</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-datatype">Bool</span><span class="agda2-highlight-symbol">;</span> <span class="agda2-highlight-inductive-constructor">true</span><span class="agda2-highlight-symbol">;</span> <span class="agda2-highlight-inductive-constructor">false</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-keyword">renaming</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-operator"><span class="agda2-highlight-function">_&#8744;_</span></span> <span class="agda2-highlight-symbol">to</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">_||_</span></span><span class="agda2-highlight-symbol">;</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">_&#8743;_</span></span> <span class="agda2-highlight-symbol">to</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">_&amp;&amp;_</span></span><span class="agda2-highlight-symbol">)</span>
<span class="agda2-highlight-keyword">open</span> <span class="agda2-highlight-keyword">import</span> <span class="agda2-highlight-module">Data.Nat.Base</span>  <span class="agda2-highlight-keyword">using</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-datatype">&#8469;</span><span class="agda2-highlight-symbol">;</span> <span class="agda2-highlight-inductive-constructor">zero</span><span class="agda2-highlight-symbol">;</span> <span class="agda2-highlight-inductive-constructor">suc</span><span class="agda2-highlight-symbol">;</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-primitive">_+_</span></span><span class="agda2-highlight-symbol">;</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-primitive">_*_</span></span><span class="agda2-highlight-symbol">;</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-primitive">_&#8760;_</span></span><span class="agda2-highlight-symbol">)</span>
<span class="agda2-highlight-keyword">open</span> <span class="agda2-highlight-keyword">import</span> <span class="agda2-highlight-module">Data.Product</span> <span class="agda2-highlight-keyword">using</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-operator"><span class="agda2-highlight-function">_&#215;_</span></span><span class="agda2-highlight-symbol">;</span> <span class="agda2-highlight-record">&#931;</span><span class="agda2-highlight-symbol">;</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">_,_</span></span><span class="agda2-highlight-symbol">;</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">_,&#8242;_</span></span><span class="agda2-highlight-symbol">)</span>
</pre>
## Basics of type inference

<pre><span class="agda2-highlight-keyword">module</span> <span class="agda2-highlight-module">BasicsOfTypeInference</span> <span class="agda2-highlight-keyword">where</span>
</pre>
Some preliminaries: the type of lists is defined as

<pre>  <span class="agda2-highlight-keyword">infixr</span> <span class="agda2-highlight-number">5</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">_&#8759;_</span></span>

  <span class="agda2-highlight-keyword">data</span> <span class="agda2-highlight-datatype">List</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-primitive-type">Set</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-primitive-type">Set</span> <span class="agda2-highlight-keyword">where</span>
    <span class="agda2-highlight-inductive-constructor">[]</span>  <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">List</span> <span class="agda2-highlight-bound-variable">A</span>
    <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">_&#8759;_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">List</span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">List</span> <span class="agda2-highlight-bound-variable">A</span>
</pre>
Agda sees `[]` as having the following type: `∀ {A} -> List A`, however if you ask Agda what the type of `[]` is (by creating a hole in this module via `_ = ?`, putting there `[]` and typing `C-c C-d`. Or you can open the current module via `open BasicsOfTypeInference` and type `C-c C-d []` without introducing a hole), you'll get something like

    List _A_42

(where `42` is some arbitrary number that Agda uses to distinguish between variables that have identical textual names, but are bound in distinct places)

That `_A_42` is a metavariable and Agda expects it to be resolved in the current context. If the context does not provide enough information for resolution to happen, Agda just reports that the metavariable is not resolved, i.e. Agda doesn't accept the code.

In contrast, Haskell is perfectly fine with `[]` and infers its type as `forall a. [a]`.

So Agda and Haskell think of `[]` having the same type

    ∀ {A} -> List A  -- in Agda
    forall a. [a]    -- in Haskell

but Haskell infers this type on the top level unlike Agda which expects `A` to be either resolved or explicitly bound.

You can make Agda infer the same type that Haskell infers by explicitly binding a type variable via a lambda:

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-symbol">&#955;</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">A</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-inductive-constructor">[]</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">A</span><span class="agda2-highlight-symbol">}</span>
</pre>
(`_ = <...>` is an anonymous definition: we ask Agda to type check something, but don't care about giving it a name, because not going to use it later)

This definition is accepted, which means that Agda inferred its type successfully.

Note that

    _ {A} = [] {A}

means the same thing as the previous expression, but doesn't type check. It's just a syntactic limitation: certain things are allowed in patterns but not in lambdas and vice versa.

Agda can infer monomorphic types directly without any hints:

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-inductive-constructor">true</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-inductive-constructor">[]</span>
</pre>
Type inference works not only with lambdas binding implicit arguments, but also explicit ones. And types of latter arguments can depend on earlier arguments. E.g.

<pre>  <span class="agda2-highlight-function">id&#8321;</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-symbol">&#955;</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-primitive-type">Set</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">x</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-bound-variable">A</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">x</span>
</pre>
is the regular `id` function, which is spelled as

```haskell
id :: forall a. a -> a
id x = x
```

in Haskell.

Partially or fully applied `id₁` doesn't need a type signature either:

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">id&#8321;</span>
  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">id&#8321;</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-datatype">Bool</span><span class="agda2-highlight-symbol">}</span>
  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">id&#8321;</span> <span class="agda2-highlight-inductive-constructor">true</span>
</pre>
You can even interleave implicit and expicit arguments and partial applications (and so full ones as well) will still be inferrable:

<pre>  <span class="agda2-highlight-function">const</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-symbol">&#955;</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-primitive-type">Set</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">x</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-bound-variable">A</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">B</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-primitive-type">Set</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">y</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-bound-variable">B</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">x</span>
  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">const</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-datatype">Bool</span><span class="agda2-highlight-symbol">}</span>
  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">const</span> <span class="agda2-highlight-inductive-constructor">true</span>
</pre>
## `let`, `where`, `mutual`

<pre><span class="agda2-highlight-keyword">module</span> <span class="agda2-highlight-module">LetWhereMutual</span> <span class="agda2-highlight-keyword">where</span>
</pre>
In Agda bindings that are not marked with `abstract` are transparent, i.e. writing, say, `let v = e in b` is the same thing as directly substituting `e` for `v` in `b` (`[e/v]b`). For example all of these type check:

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">Bool</span>
  <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-keyword">let</span> <span class="agda2-highlight-bound-variable">&#120121;</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-datatype">Bool</span>
          <span class="agda2-highlight-bound-variable">t</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-bound-variable">&#120121;</span>
          <span class="agda2-highlight-bound-variable">t</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-inductive-constructor">true</span>
      <span class="agda2-highlight-keyword">in</span> <span class="agda2-highlight-bound-variable">t</span>

  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">Bool</span>
  <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">t</span> <span class="agda2-highlight-keyword">where</span>
    <span class="agda2-highlight-function">&#120121;</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-datatype">Bool</span>
    <span class="agda2-highlight-function">t</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-function">&#120121;</span>
    <span class="agda2-highlight-function">t</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-inductive-constructor">true</span>

  <span class="agda2-highlight-function">&#120121;</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-datatype">Bool</span>
  <span class="agda2-highlight-function">t</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-function">&#120121;</span>
  <span class="agda2-highlight-function">t</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-inductive-constructor">true</span>
  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">Bool</span>
  <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">t</span>
</pre>
Unlike Haskell Agda does not have let-generalization, i.e. this valid Haskell code:

```haskell
p :: (Bool, Integer)
p = let i x = x in (i True, i 1)
```

has to be written either with an explicit type signature for `i`:

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">Bool</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">&#215;</span></span> <span class="agda2-highlight-datatype">&#8469;</span>
  <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-keyword">let</span> <span class="agda2-highlight-bound-variable">i</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-primitive-type">Set</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">A</span>
          <span class="agda2-highlight-bound-variable">i</span> <span class="agda2-highlight-bound-variable">x</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-bound-variable">x</span>
      <span class="agda2-highlight-keyword">in</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">i</span> <span class="agda2-highlight-inductive-constructor">true</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">,</span></span> <span class="agda2-highlight-bound-variable">i</span> <span class="agda2-highlight-number">1</span><span class="agda2-highlight-symbol">)</span>
</pre>
or in an equivalent way like

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">Bool</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">&#215;</span></span> <span class="agda2-highlight-datatype">&#8469;</span>
  <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-keyword">let</span> <span class="agda2-highlight-bound-variable">i</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-symbol">&#955;</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">A</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">x</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-bound-variable">A</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">x</span>
      <span class="agda2-highlight-keyword">in</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">i</span> <span class="agda2-highlight-inductive-constructor">true</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">,</span></span> <span class="agda2-highlight-bound-variable">i</span> <span class="agda2-highlight-number">1</span><span class="agda2-highlight-symbol">)</span>
</pre>
So Agda infers polymorphic types neither on the top level nor locally.

In Haskell types of bindings can be inferred from how those bindings are used later. E.g. the inferred type of a standalone

    one = 1

is `Integer` (see [monomorphism restriction](https://wiki.haskell.org/Monomorphism_restriction)), but in

    one = 1
    one' = one :: Word

the inferred type of `one` is `Word` rather than `Integer`.

This is not the case in Agda, e.g. a type for

    i = λ x -> x

is not going to be inferred regardless of how this definition is used later. However if you use `let`, `where` or `mutual` inference is possible:

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-keyword">let</span> <span class="agda2-highlight-bound-variable">i</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-symbol">&#955;</span> <span class="agda2-highlight-bound-variable">x</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">x</span> <span class="agda2-highlight-keyword">in</span> <span class="agda2-highlight-bound-variable">i</span> <span class="agda2-highlight-inductive-constructor">true</span>

  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">i</span> <span class="agda2-highlight-inductive-constructor">true</span> <span class="agda2-highlight-keyword">where</span> <span class="agda2-highlight-function">i</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-symbol">&#955;</span> <span class="agda2-highlight-bound-variable">x</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">x</span>

  <span class="agda2-highlight-keyword">mutual</span>
    <span class="agda2-highlight-function">i</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-symbol">&#955;</span> <span class="agda2-highlight-bound-variable">x</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">x</span>
    <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">i</span> <span class="agda2-highlight-inductive-constructor">true</span>
</pre>
In general, definitions in a `mutual` block share the same context, which makes it possible to infer more things than with consecutive standalone definitions. It's occasionally useful to create a bogus `mutual` block when you want the type of a definition to be inferred based on its use.

## An underspecified argument example

<pre><span class="agda2-highlight-keyword">module</span> <span class="agda2-highlight-module">UnderspecifiedArgument</span> <span class="agda2-highlight-keyword">where</span>
</pre>
Another difference between Haskell and Agda is that Agda doesn't allow to leave ambiguous types. Consider a classic example: the `I` combinator can be defined in terms of the `S` and `K` combinators. In Haskell we can express that as

    k :: a -> b -> a
    k x y = x

    s :: (a -> b -> c) -> (a -> b) -> a -> c
    s f g x = f x (g x)

    i :: a -> a
    i = s k k

and [it'll type check](https://ideone.com/mZQM1f). However the Agda's equivalent

<pre>  <span class="agda2-highlight-function">K</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-bound-variable">B</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-primitive-type">Set</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">B</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">A</span>
  <span class="agda2-highlight-function">K</span> <span class="agda2-highlight-bound-variable">x</span> <span class="agda2-highlight-bound-variable">y</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-bound-variable">x</span>

  <span class="agda2-highlight-function">S</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-bound-variable">B</span> <span class="agda2-highlight-bound-variable">C</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-primitive-type">Set</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">B</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">C</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">B</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">C</span>
  <span class="agda2-highlight-function">S</span> <span class="agda2-highlight-bound-variable">f</span> <span class="agda2-highlight-bound-variable">g</span> <span class="agda2-highlight-bound-variable">x</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-bound-variable">f</span> <span class="agda2-highlight-bound-variable">x</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">g</span> <span class="agda2-highlight-bound-variable">x</span><span class="agda2-highlight-symbol">)</span>

  <span class="agda2-highlight-function">I</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">&#8704;</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">A</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">A</span>
  <span class="agda2-highlight-function">I</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">S</span> <span class="agda2-highlight-function">K</span> <span class="agda2-highlight-function"><span class="agda2-highlight-unsolved-meta">K</span></span>
</pre>
results in the last `K` being highlighted with yellow (which means that not all metavariables were resolved). To see why, let's reduce `S K K` a bit:

    λ x -> K x (K x)

this computes to `λ x -> x` as expected, but the problem is that in the expression above the `K x` argument is underspecified: a `K` must receive a particular `B`, but we neither explicitly specify a `B`, nor can it be inferred from the context as the entire `K x` argument is thrown away by the outer `K`.

To fix this we can explicitly specify a `B` (any of type `Set` will work, let's pick `ℕ`):

<pre>  <span class="agda2-highlight-function">I&#8242;</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">&#8704;</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">A</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">A</span>
  <span class="agda2-highlight-function">I&#8242;</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">S</span> <span class="agda2-highlight-function">K</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-function">K</span> <span class="agda2-highlight-symbol">{</span>B <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-datatype">&#8469;</span><span class="agda2-highlight-symbol">})</span>
</pre>
In general, Agda expects all implicits (and metavariables in general) to be resolved and won't gloss over such details the way Haskell does. Agda is a proof assistant and under the [Curry-Howard correspondence](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence) each argument to a function represents a certain logical assumption and every such assumption must be fulfilled at the call site either explicitly or in an automated manner.

## InferenceAndPatternMatching

<pre><span class="agda2-highlight-keyword">module</span> <span class="agda2-highlight-module">InferenceAndMatching</span> <span class="agda2-highlight-keyword">where</span>
</pre>
Unrestricted pattern matching generally breaks type inference. Take for instance

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function"><span class="agda2-highlight-unsolved-meta">_</span></span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-symbol"><span class="agda2-highlight-unsolved-meta">&#955;</span></span><span class="agda2-highlight-unsolved-meta"> </span><span class="agda2-highlight-keyword"><span class="agda2-highlight-unsolved-meta">where</span></span>
          <span class="agda2-highlight-inductive-constructor"><span class="agda2-highlight-unsolved-meta">zero</span></span><span class="agda2-highlight-unsolved-meta">    </span><span class="agda2-highlight-symbol"><span class="agda2-highlight-unsolved-meta">-&gt;</span></span><span class="agda2-highlight-unsolved-meta"> </span><span class="agda2-highlight-inductive-constructor"><span class="agda2-highlight-unsolved-meta">true</span></span>
          <span class="agda2-highlight-symbol"><span class="agda2-highlight-unsolved-meta">(</span></span><span class="agda2-highlight-inductive-constructor"><span class="agda2-highlight-unsolved-meta">suc</span></span><span class="agda2-highlight-unsolved-meta"> </span><span class="agda2-highlight-symbol"><span class="agda2-highlight-unsolved-meta">_)</span></span><span class="agda2-highlight-unsolved-meta"> </span><span class="agda2-highlight-symbol"><span class="agda2-highlight-unsolved-meta">-&gt;</span></span><span class="agda2-highlight-unsolved-meta"> </span><span class="agda2-highlight-inductive-constructor"><span class="agda2-highlight-unsolved-meta">false</span></span>
</pre>
which is a direct counterpart of Haskell's

    isZero = \case
        0 -> True
        _ -> False


Agda colors the entire snippet in yellow meaning it's unable to resolve the generated metavariables. "What's the problem? The inferred type should be just `ℕ -> Bool`" -- you might think. Such a type works indeed:

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">&#8469;</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">Bool</span>
  <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-symbol">&#955;</span> <span class="agda2-highlight-keyword">where</span>
          <span class="agda2-highlight-inductive-constructor">zero</span>    <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-inductive-constructor">true</span>
          <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-inductive-constructor">suc</span> <span class="agda2-highlight-symbol">_)</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-inductive-constructor">false</span>
</pre>
But here's another thing that works:

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">&#8469;</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">&amp;</span></span> <span class="agda2-highlight-symbol">&#955;</span> <span class="agda2-highlight-keyword">where</span>
                         <span class="agda2-highlight-inductive-constructor">zero</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">Bool</span>
                         <span class="agda2-highlight-symbol"><span class="agda2-highlight-catchall-clause">_</span></span>    <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">Bool</span>
  <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-symbol">&#955;</span> <span class="agda2-highlight-keyword">where</span>
          <span class="agda2-highlight-inductive-constructor">zero</span>    <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-inductive-constructor">true</span>
          <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-inductive-constructor">suc</span> <span class="agda2-highlight-symbol">_)</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-inductive-constructor">false</span>
</pre>
Recall that we're in a dependently typed language and here the type of the result of a function can depend on the argument of that function. And both the

    ℕ -> Bool

    (n : ℕ) -> n & λ where
                       zero -> Bool
                       _    -> Bool

types are correct for that function. Even though they are "morally" the same, they are not definitionally equal and there's a huge difference between them: the former one doesn't have a dependency and the latter one has.

There is a way to tell Agda that pattern matching is non-dependent: use `case-of`, e.g.

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-symbol">&#955;</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">&#8469;</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">case</span></span> <span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">of</span></span> <span class="agda2-highlight-symbol">&#955;</span> <span class="agda2-highlight-keyword">where</span>
          <span class="agda2-highlight-inductive-constructor">zero</span>    <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-inductive-constructor">true</span>
          <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-inductive-constructor">suc</span> <span class="agda2-highlight-symbol">_)</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-inductive-constructor">false</span>
</pre>
type checks. `case_of_` is just a definition in the standard library that at the term level is essentially

    case x of f = f x

and at the type level it restricts the type of `f` to be a non-dependent function.

Annotating `n` with its type, `ℕ`, is mandatory in this case. It seems Agda is not able to conclude that if a value is matched against a pattern, then the value must have the same type as the pattern.

Even this doesn't type check:

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function"><span class="agda2-highlight-unsolved-meta">_</span></span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-symbol">&#955;</span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-bound-variable">n</span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-symbol">-&gt;</span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-operator"><span class="agda2-highlight-function"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-unsolved-constraint">case</span></span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-bound-variable">n</span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-operator"><span class="agda2-highlight-function"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-unsolved-constraint">of</span></span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-symbol">&#955;</span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-keyword">where</span></span></span>
          <span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-inductive-constructor">zero</span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta">    </span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-symbol">-&gt;</span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-inductive-constructor">zero</span></span></span>
          <span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-symbol">(</span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-inductive-constructor">suc</span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-bound-variable">n</span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-symbol">)</span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-symbol">-&gt;</span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-bound-variable">n</span></span></span>
</pre>
even though Agda really could figure out that if `zero` is returned from one of the branches, then the type of the result is `ℕ`, and since `n` is returned from the other branch and pattern matching is non-dependent, `n` must have the same type. See [#2834](https://github.com/agda/agda/issues/2834) for why Agda doesn't attempt to be clever here.

There's a funny syntactical way to tell Agda that a function is non-dependent: just do not bind a variable at the type level. This type checks:

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">&#8469;</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-symbol">_</span>
  <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-symbol">&#955;</span> <span class="agda2-highlight-keyword">where</span>
          <span class="agda2-highlight-inductive-constructor">zero</span>    <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-inductive-constructor">true</span>
          <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-inductive-constructor">suc</span> <span class="agda2-highlight-symbol">_)</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-inductive-constructor">false</span>
</pre>
while this doesn't:

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">&#8469;</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-symbol"><span class="agda2-highlight-unsolved-meta">_</span></span>
  <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-symbol">&#955;</span> <span class="agda2-highlight-keyword">where</span>
          <span class="agda2-highlight-inductive-constructor">zero</span>    <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-inductive-constructor">true</span></span></span>
          <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-inductive-constructor">suc</span> <span class="agda2-highlight-symbol">_)</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-inductive-constructor">false</span></span></span>
</pre>
In the latter case Agda treats `_` as being porentially dependent on `n`, since `n` is explicitly bound. And in the former case there can't be any dependency on a non-existing variable.

## InferenceAndConstructors

<pre><span class="agda2-highlight-keyword">module</span> <span class="agda2-highlight-module">InferenceAndConstructors</span> <span class="agda2-highlight-keyword">where</span>
</pre>
Since tuples are dependent, this

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-number">1</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor"><span class="agda2-highlight-unsolved-meta">,</span></span></span> <span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-number">2</span></span></span><span class="agda2-highlight-symbol">)</span>
</pre>
results in unresolved metas as all of these

    ℕ × ℕ

    Σ ℕ λ where
            zero -> ℕ
            _    -> ℕ

    Σ ℕ λ where
            1 -> ℕ
            _ -> Bool

are valid types for this expression, which is similar to what we've considered in the previous section, except here not all of the types are "morally the same": the last one is very different to the first two.

As in the case of functions you can use a non-dependent alternative

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-number">1</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">,&#8242;</span></span> <span class="agda2-highlight-number">2</span><span class="agda2-highlight-symbol">)</span>
</pre>
(`_,′_` is a non-dependent version of `_,_`)

to tell Agda not to worry about potential dependencies.

## Unification intro

<pre><span class="agda2-highlight-keyword">module</span> <span class="agda2-highlight-module">UnificationIntro</span> <span class="agda2-highlight-keyword">where</span>
</pre>
The following definitions type check:

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-symbol">(&#955;</span> <span class="agda2-highlight-bound-variable">x</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">x</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-number">1</span>
  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-symbol">(&#955;</span> <span class="agda2-highlight-bound-variable">x</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-number">2</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-number">1</span>
</pre>
reassuring that Agda's type checker is not based on some simple bidirectional typing rules (if you're not familier with those, see [Bidirectional Typing Rules: A Tutorial](http://www.davidchristiansen.dk/tutorials/bidirectional.pdf), but the type checker does have a bidirectional interface ([`inferExpr`](https://hackage.haskell.org/package/Agda-2.6.1/docs/Agda-TheTypeChecker.html#v:inferExpr) & [`checkExpr`](https://hackage.haskell.org/package/Agda-2.6.1/docs/Agda-TheTypeChecker.html#v:checkExpr)) where type inference is defined in terms of type checking for the most part:

    -- | Infer the type of an expression. Implemented by checking against a meta variable. <...>
    inferExpr :: A.Expr -> TCM (Term, Type)

which means that any definition of the following form:

    name = term

can be equally written as

    name : _
    name = term

since Agda elaborates `_` to a fresh metavariable and then type checks `term` againt it, which amounts to unifying the inferred type of `term` with the meta. If the inferred type doesn't contain metas itself, then the meta standing for `_` is resolved as that type and the definition is accepted. So type inference is just a particular form of unification.

You can put `_` basically anywhere and let Agda infer what term/type it stands for. For example:

<pre>  <span class="agda2-highlight-function">id&#8322;</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-primitive-type">Set</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-symbol">_</span>
  <span class="agda2-highlight-function">id&#8322;</span> <span class="agda2-highlight-bound-variable">x</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-bound-variable">x</span>
</pre>
Here Agda binds the `x` variable and records that it has type `A` and when the `x` variable is returned as a result, Agda unifies the expected type `_` with the actual type of `x`, which is `A`. Thus the definition above elaborates to

<pre>  <span class="agda2-highlight-function">id&#8322;&#8242;</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-primitive-type">Set</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">A</span>
  <span class="agda2-highlight-function">id&#8322;&#8242;</span> <span class="agda2-highlight-bound-variable">x</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-bound-variable">x</span>
</pre>
This definition:

<pre>  <span class="agda2-highlight-function">id&#8323;</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-primitive-type">Set</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">A</span>
  <span class="agda2-highlight-function">id&#8323;</span> <span class="agda2-highlight-bound-variable">x</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-bound-variable">x</span>
</pre>
elaborates to the same result in a similar fashion, except now Agda first records that the type of `x` is a meta and when `x` is returned as a result, Agda unifies that meta with the expected type, i.e. `A`, and so the meta gets resolved as `A`.

An `id` function that receives an explicit type:

<pre>  <span class="agda2-highlight-function">id&#8324;</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-primitive-type">Set</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">A</span>
  <span class="agda2-highlight-function">id&#8324;</span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-bound-variable">x</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-bound-variable">x</span>
</pre>
can be called as

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">id&#8324;</span> <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-inductive-constructor">true</span>
</pre>
and the `_` will be inferred as `Bool`.

It's also possible to explicitly specify an implicit type by `_`, which is essentially a no-op:

<pre>  <span class="agda2-highlight-function">id&#8325;</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-primitive-type">Set</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">A</span>
  <span class="agda2-highlight-function">id&#8325;</span> <span class="agda2-highlight-bound-variable">x</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-bound-variable">x</span>

  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">id&#8325;</span> <span class="agda2-highlight-symbol">{_}</span> <span class="agda2-highlight-inductive-constructor">true</span>
</pre>
## Implicit arguments

<pre><span class="agda2-highlight-keyword">module</span> <span class="agda2-highlight-module">ImplicitArgumens</span> <span class="agda2-highlight-keyword">where</span>
</pre>
As we've just seen implicit arguments and metavariable are closely related. Agda's internal theory has metas in it, so inference of implicit arguments amounts to turning an implicit into a metavariable and resolving it later. The complicated part however is that it's not always obvious where to bound an implicit.

For example, it may come as a surprise, but

    _ : ∀ {A : Set} -> A -> A
    _ = λ {A : Set} x -> x

gives a type error. This is because Agda greedily binds implicits, so the `A` at the term level gets automatically bound on the lhs (left-hand side, i.e. before `=`), which gives you

    _ : ∀ {A : Set} -> A -> A
    _ {_} = <your_code_goes_here>

where `{_}` stands for `{A}`. So you can't bind `A` by a lambda, because it's already silently bound for you. Although it's impossible to reference that type variable unless you explicitly name it as in

<pre>  <span class="agda2-highlight-function">id</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-primitive-type">Set</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">A</span>
  <span class="agda2-highlight-function">id</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">A</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-symbol">&#955;</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">x</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-bound-variable">A</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">x</span>
</pre>
There is a notorious bug that has been in Agda for ages (even since its creation probably?) called The Hidden Lambda Bug:

- tracked in [this issue](https://github.com/agda/agda/issues/1079)
- discussed in detail in [this issue](https://github.com/agda/agda/issues/2099)
- there even an entire [MSc thesis](http://www2.tcs.ifi.lmu.de/~abel/MScThesisJohanssonLloyd.pdf) about it
- and a [possible solution](https://github.com/AndrasKovacs/elaboration-zoo/tree/master/experimental/poly-instantiation)

So while the turn-implicits-into-metas approach works well, it has its edge cases. In practice, it's not a big deal to insert an implicit lambda to circumvent the bug, but it's not always clear that Agda throws a type error because of this bug and not due to something else (e.g. I was completely lost in [this case](https://github.com/agda/agda/issues/1095)). So beware.

## Inferring implicits

<pre><span class="agda2-highlight-keyword">module</span> <span class="agda2-highlight-module">InferringImplicits</span> <span class="agda2-highlight-keyword">where</span>
</pre>
As we've seen previously the following code type checks fine:

<pre>  <span class="agda2-highlight-function">id</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-primitive-type">Set</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">A</span>
  <span class="agda2-highlight-function">id</span> <span class="agda2-highlight-bound-variable">x</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-bound-variable">x</span>

  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">id</span> <span class="agda2-highlight-inductive-constructor">true</span>
</pre>
Here `A` is bound implicitly in `id`, but Agda is able to infer that in this case `A` should be instantiated to `Bool` and so Agda elaborates the expression to `id {Bool} true`.

This is something that Haskell would infer as well. The programmer would hate to explicitly write out the type of every single argument, so programming languages often allow not to specify types when they can be inferred from the context. Agda is quite unique here however, because it can infer a lot more than other languages (even similar dependently typed ones) due to bespoke machineries handling various common patterns. But let's start with basics.

## Arguments of data types

<pre><span class="agda2-highlight-keyword">module</span> <span class="agda2-highlight-module">ArgumentsOfDataTypes</span> <span class="agda2-highlight-keyword">where</span>
  <span class="agda2-highlight-keyword">open</span> <span class="agda2-highlight-module">BasicsOfTypeInference</span>
</pre>
Agda can infer parameters/indices of a data type from a value of that data type. For example if you have a function

<pre>  <span class="agda2-highlight-function">listId</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">&#8704;</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">A</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">List</span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">List</span> <span class="agda2-highlight-bound-variable">A</span>
  <span class="agda2-highlight-function">listId</span> <span class="agda2-highlight-bound-variable">xs</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-bound-variable">xs</span>
</pre>
then the implicit `A` can be inferred from a list:

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">listId</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-number">1</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-number">2</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-inductive-constructor">[]</span><span class="agda2-highlight-symbol">)</span>
</pre>
Unless, of course, `A` can't be determined from the list alone. E.g. if we pass an empty list to `f`, Agda will mark `listId` with yellow and display an unresolved metavariable `_A`:

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function"><span class="agda2-highlight-unsolved-meta">listId</span></span> <span class="agda2-highlight-inductive-constructor">[]</span>
</pre>
Another example of this situation is when the list is not empty, but the type of its elements can't be inferred, e.g.

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">listId</span> <span class="agda2-highlight-symbol">((&#955;</span> <span class="agda2-highlight-bound-variable"><span class="agda2-highlight-unsolved-meta">x</span></span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">x</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-inductive-constructor">[]</span><span class="agda2-highlight-symbol">)</span>
</pre>
Here the type of `x` can be essentially anything (`ℕ`, `List Bool`, `⊤ × Bool -> ℕ`, etc), so Agda asks to provide missing details. Which we can do either by supplying a value for the implicit argument explicitly

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">listId</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-datatype">&#8469;</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">&#8469;</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">((&#955;</span> <span class="agda2-highlight-bound-variable">x</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">x</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-inductive-constructor">[]</span><span class="agda2-highlight-symbol">)</span>
</pre>
or by annotating `x` with a type

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">listId</span> <span class="agda2-highlight-symbol">((&#955;</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">x</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">&#8469;</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">x</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-inductive-constructor">[]</span><span class="agda2-highlight-symbol">)</span>
</pre>
or just by providing a type signature

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">List</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-datatype">&#8469;</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">&#8469;</span><span class="agda2-highlight-symbol">)</span>
  <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">listId</span> <span class="agda2-highlight-symbol">((&#955;</span> <span class="agda2-highlight-bound-variable">x</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">x</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-inductive-constructor">[]</span><span class="agda2-highlight-symbol">)</span>
</pre>
All these definitions are equivalent.

So "`A` is inferrable from a `List A`" doesn't mean that you can pass any list in and magically synthesize the type of its elements -- only that if that type is already known at the call site, then you don't need to explicitly specify it to apply `listId` to the list as it'll be inferred for you. "Already known at the call site" doesn't mean that the type of elements needs to be inferrable -- sometimes it can be derived from the context, for example:

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-inductive-constructor">suc</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-function">listId</span> <span class="agda2-highlight-symbol">((&#955;</span> <span class="agda2-highlight-bound-variable">x</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">x</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-inductive-constructor">[]</span><span class="agda2-highlight-symbol">)</span>
</pre>
The implicit `A` gets inferred here: since all elements of a list have the same type, the type of `λ x -> x` must be the same as the type of `suc`, which is known to be `ℕ -> ℕ`, hence the type of `λ x -> x` is also `ℕ -> ℕ`.

### Comparison to Haskell

In Haskell it's also the case that `a` is inferrable form a `[a]`: when the programmer writes

    sort :: Ord a => [a] -> [a]

Haskell is always able to infer `a` from the given list (provided `a` is known at the call site: `sort []` is as meaningless in Haskell as it is in Agda) and thus figure out what the appropriate `Ord a` instance is. However, another difference between Haskell and Agda is that whenever Haskell sees that some implicit variables (i.e. those bound by `forall <list_of_vars> .`) can't be inferred in the general case, Haskell, unlike Agda, will complain. E.g. consider the following piece of code:

    {-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, TypeFamilies #-}

    class C a b where
      f :: a -> Int

    instance b ~ () => C Bool b where
      f _ = 0

    main = print $ f True

Even though at the call site (`f True`) `b` is determined via the `b ~ ()` constraint of the `C Bool b` instance and so there is no ambiguity, Haskell still complains about the definition of the `C` class itself:

    • Could not deduce (C a b0)
      from the context: C a b
        bound by the type signature for:
                   f :: forall a b. C a b => a -> Int
        at prog.hs:6:3-15
      The type variable ‘b0’ is ambiguous

The type of the `f` function mentions the `b` variable in the `C a b` constraint, but that variable is not mentioned anywhere else and hence can't be inferred in the general case, so Haskell complains, because by default it wants all type variables to be inferrable upfront regardless of whether at the call site it would be possible to infer a variable in some cases or not. We can override the default behavior by enabling the `AllowAmbiguousTypes` extension, which makes the code type check without any additional changes.

Agda's unification capabilities are well above Haskell's ones, so Agda doesn't attempt to predict what can and can't be inferred and allows us to make anything implicit deferring resolution problems to the call site (i.e. it's like having `AllowAmbiguousTypes` globally enabled in Haskell). In fact, you can make implicit even such things that are pretty much guaranteed to never have any chance of being inferred, for example

<pre>  <span class="agda2-highlight-function">const-zero&#7522;</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-symbol"><span class="agda2-highlight-bound-variable">_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">&#8469;</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">&#8469;</span>
  <span class="agda2-highlight-function">const-zero&#7522;</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-inductive-constructor">zero</span>
</pre>
## Under the hood

<pre><span class="agda2-highlight-keyword">module</span> <span class="agda2-highlight-module">UnderTheHood</span> <span class="agda2-highlight-keyword">where</span>
  <span class="agda2-highlight-keyword">open</span> <span class="agda2-highlight-module">BasicsOfTypeInference</span>
</pre>
### Example 1

Returning to our `listId` example, when the user writes

<pre>  <span class="agda2-highlight-function">listId</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">&#8704;</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">A</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">List</span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">List</span> <span class="agda2-highlight-bound-variable">A</span>
  <span class="agda2-highlight-function">listId</span> <span class="agda2-highlight-bound-variable">xs</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-bound-variable">xs</span>

  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">listId</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-number">1</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-number">2</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-inductive-constructor">[]</span><span class="agda2-highlight-symbol">)</span>
</pre>
here is what happens under the hood:

1. the implicit `A` gets instantiated as a metavariable `_A`
2. the type of the instantiated `listId` becomes `List _A -> List _A`
3. `List _A` (what the instantiated `listId` expects as an argument) gets unified with `List ℕ` (the type of the actual argument). We'll write this as `List _A =?= List ℕ`
4. From unification's point of view type constructors are injective, hence `List _A =?= List ℕ` simplifies to `_A =?= ℕ`, which immediately gets solved as `_A := ℕ`

And this is how Agda figures out that `A` gets instantiated by `ℕ`.

### Example 2

Similarly, when the user writes

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-inductive-constructor">suc</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-function">listId</span> <span class="agda2-highlight-symbol">((&#955;</span> <span class="agda2-highlight-bound-variable">x</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">x</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-inductive-constructor">[]</span><span class="agda2-highlight-symbol">)</span>
</pre>
1. the implicit `A` gets instantiated as a metavariable `_A`
2. the type of the instantiated `listId` becomes `List _A -> List _A`
3. `List _A` (what the instantiated `listId` expects as an argument) gets unified with `List (_B -> _B)` (the type of the actual argument). `_B` is another metavariable. Recall that we don't know the type of `x` and hence we simply make it a meta
4. `List _A` (this time the type of the result that `listId` returns) also gets unified with the expected type, which is `ℕ -> ℕ`, because `suc` prepended to the result of the `listId` application is of this type
5. we get the following [unification problem](https://en.wikipedia.org/wiki/Unification_(computer_science)#Unification_problem,_solution_set) consisting of two equations:

       List _A =?= List (_B -> _B)
       List _A =?= List (ℕ -> ℕ)

6. as before we can simplify the equations by stripping `List`s from both the sides of each of them:

       _A =?= _B -> _B
       _A =?= ℕ -> ℕ

7. the second equation gives us `A := ℕ -> ℕ` and it only remains to solve

       ℕ -> ℕ =?= _B -> _B

8. which is easy: `_B := ℕ`. The full solution of the unification problem is

       _B := ℕ
       _A := ℕ -> ℕ

### Example 3

When the user writes

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-symbol">&#955;</span> <span class="agda2-highlight-bound-variable">xs</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-inductive-constructor">suc</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-function">listId</span> <span class="agda2-highlight-bound-variable">xs</span>
</pre>
1. the yet-unknown type of `xs` elaborates to a metavariable, say, `_LA`
2. the implicit `A` of `listId` elaborates to a metavariable `_A`
3. `List _A` (what the instantiated `listId` expects as an argument) gets unified with `_LA` (the type of the actual argument)
4. `List _A` (this time the type of the result that `listId` returns) also gets unified with the expected type, which is `ℕ -> ℕ`, because `suc` prepended to the result of the `listId` application is of this type
5. we get the following unification problem consisting of two equations:

       List _A =?= _LA
       List _A =?= List (ℕ -> ℕ)

6. `_A` gets solved as `_A := ℕ -> ℕ`
7. and `_LA` gets solved as `_LA := List (ℕ -> ℕ)`
8. so the final solution is

       _A := ℕ -> ℕ
       _LA := List (ℕ -> ℕ)

But note that we could first resolve `_LA` as `List _A`, then resolve `_A` and then instantiate it in `List _A` (what `_LA` was resolved to), which would give us the same final solution.

In general, there are many possible routes that one can take when solving a unification problem, but some of them are less straightforward (and thus less efficient) than others. Such details are beyond the scope of this document, here we are only interested in unification problems that get generated during type checking and solutions to them. Arriving at those solutions is a pretty technical (and incredibly convoluted) thing.

## Nicer notation

In the previous section we were stripping `List` from both the sides of an equation. We were able to do this, because from the unification's point of view type constructors are injective (this has nothing to do with the [`--injective-type-constructors`](https://github.com/agda/agda/blob/10d704839742c332dc85f1298b80068ce4db6693/test/Succeed/InjectiveTypeConstructors.agda) pragma that [makes Agda anti-classical](https://lists.chalmers.se/pipermail/agda/2010/001526.html)). I.e. `List A` uniquely determines `A`.

We'll denote "`X` uniquely determines `Y`" (the notation comes from the [bidirectional typechecking](https://ncatlab.org/nlab/show/bidirectional+typechecking) discipline) as `X ⇉ Y`. So `List A ⇉ A`.

An explicitly provided argument (i.e. `x` in either `f x` or `f {x}`) uniquely determines the type of that argument. We'll denote that as `(x : A) ⇉ A`.

We'll denote "`X` does not uniquely determine `Y`" as `X !⇉ Y`.

We'll also abbreviate

    X ⇉ Y₁
    X ⇉ Y₂
    ...
    X ⇉ yₙ

as

    X ⇉ Y₁ , Y₂ ... Yₙ

(and similarly for `!⇉`).

We'll denote "`X` can be determined in the current context" by

    ⇉ X

Finally, we'll have derivitation trees like

    X        Y
    →→→→→→→→→→
      Z₁ , Z₂        A
      →→→→→→→→→→→→→→→→
             B

which reads as "if `X` and `Y` are determined in the current context, then it's possible to determine `Z₁` and `Z₂`, having which together with `A` determined in the current context, is enough to determine `B`".

## Type functions

<pre><span class="agda2-highlight-keyword">module</span> <span class="agda2-highlight-module">TypeFunctions</span> <span class="agda2-highlight-keyword">where</span>
  <span class="agda2-highlight-keyword">open</span> <span class="agda2-highlight-module">BasicsOfTypeInference</span>
</pre>
Analogously to `listId` we can define `fId` that works for any `F : Set -> Set`, including `List`:

<pre>  <span class="agda2-highlight-function">fId</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">&#8704;</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">F</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-primitive-type">Set</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-primitive-type">Set</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">A</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">F</span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">F</span> <span class="agda2-highlight-bound-variable">A</span>
  <span class="agda2-highlight-function">fId</span> <span class="agda2-highlight-bound-variable">a</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-bound-variable">a</span>
</pre>
Unfortunately applying `fId` to a list without explicitly instantiating `F` as `List`

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function"><span class="agda2-highlight-unsolved-meta">fId</span></span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-number">1</span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-unsolved-constraint">&#8759;</span></span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-number">2</span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-unsolved-constraint">&#8759;</span></span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-inductive-constructor">[]</span></span></span><span class="agda2-highlight-symbol">)</span>
</pre>
results in both `F` and `A` not being resolved. This might be surprising, but there is a good reason for this behavior: there are multiple ways `F` and `A` can be instantiated, so Agda doesn't attempt to pick a random one. Here's the solution that the user would probably have had in their mind:

    _F := List
    _A := ℕ

but this one is also valid:

    _F := λ _ -> List ℕ
    _A := Bool

i.e. `F` ignores `A` and just returns `List ℕ`:

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">fId</span> <span class="agda2-highlight-symbol">{&#955;</span> <span class="agda2-highlight-symbol"><span class="agda2-highlight-bound-variable">_</span></span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">List</span> <span class="agda2-highlight-datatype">&#8469;</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-datatype">Bool</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-number">1</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-number">2</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-inductive-constructor">[]</span><span class="agda2-highlight-symbol">)</span>
</pre>
Even if you specify `A = ℕ`, `F` still can be either `List` or `λ _ -> List ℕ`, so you have to specify `F` (and then the problem reduces to the one that we considered earlier, hence there is no need to also specify `A`):

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">fId</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-datatype">List</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-number">1</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-number">2</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-inductive-constructor">[]</span><span class="agda2-highlight-symbol">)</span>
</pre>
Therefore, `F A` (where `F` is a type variable) uniquely determines neither `F` nor `A`, i.e. `F A !⇉ F , A`.

### Comparison to Haskell

A type application of a variable is injective in Haskell. I.e. unification of `f a` and `g b` (where `f` and `g` are type variables) forces unification of `a` and `b`, as well as unification of `f` and `g`. I.e. not only does `f a ⇉ a` hold for arbitrary type variable `f`, but also `f a ⇉ f`. This makes it possible to define functions like

    fmap :: Functor f => (a -> b) -> f a -> f b

and use them without compulsively specifying `f` at the call site each time.

Haskell is able to infer `f`, because no analogue of Agda's `λ _ -> List ℕ` is possible in Haskell as its surface language doesn't have type lambdas. You can't pass a type family as `f` either. Therefore there exists only one solution for "unify `f a` with `List Int`" in Haskell and it's the expected one:

    f := List
    a := Int

For a type family `F` we have `F a !⇉ a` (just like in Agda), unless `F` is an [injective type family](https://gitlab.haskell.org/ghc/ghc/wikis/injective-type-families).

## Data constructors

<pre><span class="agda2-highlight-keyword">module</span> <span class="agda2-highlight-module">DataConstructors</span> <span class="agda2-highlight-keyword">where</span>
</pre>
Data constructors are injective from the unification point of view and from the theoretical point of view as well (unlike type constructors). E.g. consider the type of vectors (a vector is a list whose length is statically known):

<pre>  <span class="agda2-highlight-keyword">infixr</span> <span class="agda2-highlight-number">5</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">_&#8759;&#7525;_</span></span>
  <span class="agda2-highlight-keyword">data</span> <span class="agda2-highlight-datatype">Vec</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-primitive-type">Set</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">&#8469;</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-primitive-type">Set</span> <span class="agda2-highlight-keyword">where</span>
    <span class="agda2-highlight-inductive-constructor">[]&#7525;</span>  <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">Vec</span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-number">0</span>
    <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">_&#8759;&#7525;_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">&#8704;</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">n</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">Vec</span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">Vec</span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-inductive-constructor">suc</span> <span class="agda2-highlight-bound-variable">n</span><span class="agda2-highlight-symbol">)</span>
</pre>
The `head` function is defined like that over `Vec`:

<pre>  <span class="agda2-highlight-function">head&#7525;</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">&#8704;</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-bound-variable">n</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">Vec</span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-inductive-constructor">suc</span> <span class="agda2-highlight-bound-variable">n</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">A</span>
  <span class="agda2-highlight-function">head&#7525;</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">x</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-symbol">_)</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-bound-variable">x</span>
</pre>
I.e. we require an input vector to have at least one element and return that first element.

`n` can be left implicit, because `suc n ⇉ n`. In general, for a constructor `C` the following holds:

    C x₁ x₂ ... xₙ ⇉ x₁ , x₂ ... xₙ

A simple test:

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">head&#7525;</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-number">0</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-inductive-constructor">[]&#7525;</span><span class="agda2-highlight-symbol">)</span>
</pre>
Here we pass a one-element vector to `headᵥ` and Agda succesfully infers the implicit `n` of `headᵥ` to be `0` (i.e. no elements in the vector apart from the first one).

During unification the implicit `n` gets instantiated to a metavariable, say, `_n` and `suc _n` (the expected length of the vector) gets unified with `suc zero` (i.e. 1, the actual length of the vector), which amounts to unifying `_n` with `zero`, which immediately results in `n := zero`.

Instead of having a constant vector, we can have a vector of an unspecified length and infer that length by providing `n` to `headᵥ` explicitly, as in

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-symbol">&#955;</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">n</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-bound-variable">xs</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-function">head&#7525;</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-datatype">&#8469;</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">n</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-bound-variable">xs</span>
</pre>
The type of that definition is `∀ {n} -> Vec ℕ (suc n) -> ℕ`.

We started by binding two variables without specifying their types, but those got inferred from how arguments are used by `headᵥ`.

Note that `_⇉_` is transitive, i.e. if `X ⇉ Y` and `Y ⇉ Z`, then `X ⇉ Z`. For example, since `Vec A n ⇉ n` (due to `Vec` being a type constructor) and `suc n ⇉ n` (due to `suc` being a data constructor), we have `Vec A (suc n) ⇉ n` (by transitivity of `_⇉_`).

## Reduction

If `X` reduces to `Y` (we'll denote that as `X ~> Y`) and `Y ⇉ Z`, then `X ⇉ Z`.

E.g. if we define an alternative version of `headᵥ` that uses `1 +_` instead of `suc`:

<pre>  <span class="agda2-highlight-function">head&#7525;&#8314;</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">&#8704;</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-bound-variable">n</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">Vec</span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-number">1</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-primitive">+</span></span> <span class="agda2-highlight-bound-variable">n</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">A</span>
  <span class="agda2-highlight-function">head&#7525;&#8314;</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">x</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-symbol">_)</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-bound-variable">x</span>
</pre>
the `n` will still be inferrable:

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">head&#7525;&#8314;</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-number">0</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-inductive-constructor">[]&#7525;</span><span class="agda2-highlight-symbol">)</span>
</pre>
This is because `1 + n` reduces to `suc n`, so the two definitions are equivalent.

Note that Agda looks under lambdas when reducing an expression, so for example `λ n -> 1 + n` and `λ n -> suc n` are two definitionally equal terms:

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">(&#955;</span> <span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-number">1</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-primitive">+</span></span> <span class="agda2-highlight-bound-variable">n</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-datatype">&#8801;</span></span> <span class="agda2-highlight-symbol">(&#955;</span> <span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-inductive-constructor">suc</span> <span class="agda2-highlight-bound-variable">n</span><span class="agda2-highlight-symbol">)</span>
  <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-inductive-constructor">refl</span>
</pre>
Note also that Agda does not look under pattern matching lambdas, so for example these two functions

    λ{ zero -> zero; (suc n) -> 1 + n }
    λ{ zero -> zero; (suc n) -> suc n }

are not considered definitionally equal. In fact, even

    _ : _≡_ {A = ℕ -> ℕ}
        (λ{ zero -> zero; (suc n) -> suc n })
        (λ{ zero -> zero; (suc n) -> suc n })
    _ = refl

is an error despite the two functions being syntactically equal. Here's the funny error:

    (λ { zero → zero ; (suc n) → suc n }) x !=
    (λ { zero → zero ; (suc n) → suc n }) x of type ℕ
    when checking that the expression refl has type
    (λ { zero → zero ; (suc n) → suc n }) ≡
    (λ { zero → zero ; (suc n) → suc n })

## Pattern matching

Generally speaking, pattern matching breaks inference. We'll consider various cases, but to start with the simplest ones we need to introduce a slightly weird definition of the plus operator:

<pre><span class="agda2-highlight-keyword">module</span> <span class="agda2-highlight-module">WeirdPlus</span> <span class="agda2-highlight-keyword">where</span>
  <span class="agda2-highlight-keyword">open</span> <span class="agda2-highlight-module">DataConstructors</span>

  <span class="agda2-highlight-operator"><span class="agda2-highlight-function">_+&#8242;_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">&#8469;</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">&#8469;</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">&#8469;</span>
  <span class="agda2-highlight-inductive-constructor">zero</span>  <span class="agda2-highlight-operator"><span class="agda2-highlight-function">+&#8242;</span></span> <span class="agda2-highlight-bound-variable">m</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-bound-variable">m</span>
  <span class="agda2-highlight-inductive-constructor">suc</span> <span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">+&#8242;</span></span> <span class="agda2-highlight-bound-variable">m</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-primitive">+</span></span> <span class="agda2-highlight-inductive-constructor">suc</span> <span class="agda2-highlight-bound-variable">m</span>
</pre>
because the usual one

    _+_ : ℕ -> ℕ -> ℕ
    zero  + m = m
    suc n + m = suc (n + m)

is subject to certain unification heuristics, which the weird one doesn't trigger.

We'll be using the following function for demonstration purposes:

<pre>  <span class="agda2-highlight-function">id&#7525;&#8314;</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">&#8704;</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-bound-variable">m</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">Vec</span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">+&#8242;</span></span> <span class="agda2-highlight-bound-variable">m</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">Vec</span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">+&#8242;</span></span> <span class="agda2-highlight-bound-variable">m</span><span class="agda2-highlight-symbol">)</span>
  <span class="agda2-highlight-function">id&#7525;&#8314;</span> <span class="agda2-highlight-bound-variable">xs</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-bound-variable">xs</span>
</pre>
### A constant argument

`idᵥ⁺` applied to a constant vector

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function"><span class="agda2-highlight-unsolved-meta">id&#7525;&#8314;</span></span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-number">1</span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-unsolved-constraint">&#8759;&#7525;</span></span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-number">2</span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-unsolved-constraint">&#8759;&#7525;</span></span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-inductive-constructor">[]&#7525;</span></span></span><span class="agda2-highlight-symbol">)</span>
</pre>
gives us yellow, because Agda turns the implicit `n` and `m` into metavariables `_n` and `_m` and tries to unify the expected length of a vector (`_n +′ _m`) with the actual one (`2`) and there are multiple solutions to this problem, e.g.

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">id&#7525;&#8314;</span> <span class="agda2-highlight-symbol">{</span>n <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-number">1</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">{</span>m <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-number">1</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-number">1</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-number">2</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-inductive-constructor">[]&#7525;</span><span class="agda2-highlight-symbol">)</span>
  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">id&#7525;&#8314;</span> <span class="agda2-highlight-symbol">{</span>n <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-number">2</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">{</span>m <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-number">0</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-number">1</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-number">2</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-inductive-constructor">[]&#7525;</span><span class="agda2-highlight-symbol">)</span>
</pre>
Howewer as per the previous the section, we do not really need to specify `m`, since `_+′_` is defined by recursion on `n` and hence for it to reduce it suffices to specify only `n`:

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">id&#7525;&#8314;</span> <span class="agda2-highlight-symbol">{</span>n <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-number">1</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-number">1</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-number">2</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-inductive-constructor">[]&#7525;</span><span class="agda2-highlight-symbol">)</span>
</pre>
since with `n` specified this way the `_n` metavariable gets resolved as `_n := 1` and the expected length of an argument, `_n +′ _m`, becomes `suc m`, which Agda knows how to unify with `2` (the length of the actual argument).

Specifying `m` instead of `n` won't work though:

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function"><span class="agda2-highlight-unsolved-meta">id&#7525;&#8314;</span></span> <span class="agda2-highlight-symbol">{</span>m <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-number">1</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-number">1</span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-unsolved-constraint">&#8759;&#7525;</span></span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-number">2</span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-unsolved-constraint">&#8759;&#7525;</span></span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-inductive-constructor">[]&#7525;</span></span></span><span class="agda2-highlight-symbol">)</span>
</pre>
Agda can't resolve `_n`. This is because `_+′_` is defined by pattern matching on its first variable, so `1 +′ m` reduces to `suc m`, but `n +′ 1` is stuck and doesn't reduce to anything when `n` is a variable/metavariable/any stuck term. So even though there's a single solution to the

    n +′ 1 =?= 2

unification problem, Agda is not able to come up with it, because this would require arbitrary search in the general case and Agda's unification machinery carefully avoids any such strategies.

### A non-constant argument

`idᵥ⁺` applied to a non-constant vector has essentially the same inference properties.

Without specializing the implicit arguments we get yellow:

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-symbol">&#955;</span> <span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-bound-variable">m</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">xs</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">Vec</span> <span class="agda2-highlight-datatype">&#8469;</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">+&#8242;</span></span> <span class="agda2-highlight-bound-variable">m</span><span class="agda2-highlight-symbol">))</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-function"><span class="agda2-highlight-unsolved-meta">id&#7525;&#8314;</span></span> <span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-bound-variable">xs</span></span></span>
</pre>
Specializing `m` doesn't help, still yellow:

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-symbol">&#955;</span> <span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-bound-variable">m</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">xs</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">Vec</span> <span class="agda2-highlight-datatype">&#8469;</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">+&#8242;</span></span> <span class="agda2-highlight-bound-variable">m</span><span class="agda2-highlight-symbol">))</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-function"><span class="agda2-highlight-unsolved-meta">id&#7525;&#8314;</span></span> <span class="agda2-highlight-symbol">{</span>m <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-bound-variable">m</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-bound-variable">xs</span></span></span>
</pre>
And specializing `n` (with or without `m`) allows Agda to resolve all the metas:

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-symbol">&#955;</span> <span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-bound-variable">m</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">xs</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">Vec</span> <span class="agda2-highlight-datatype">&#8469;</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">+&#8242;</span></span> <span class="agda2-highlight-bound-variable">m</span><span class="agda2-highlight-symbol">))</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-function">id&#7525;&#8314;</span> <span class="agda2-highlight-symbol">{</span>n <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-bound-variable">n</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-bound-variable">xs</span>
  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-symbol">&#955;</span> <span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-bound-variable">m</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">xs</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">Vec</span> <span class="agda2-highlight-datatype">&#8469;</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">+&#8242;</span></span> <span class="agda2-highlight-bound-variable">m</span><span class="agda2-highlight-symbol">))</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-function">id&#7525;&#8314;</span> <span class="agda2-highlight-symbol">{</span>n <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-bound-variable">n</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">{</span>m <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-bound-variable">m</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-bound-variable">xs</span>
</pre>
### Examples

So we have the following rule of thumb: whenever the type of function `h` mentions function `f` at the type level, every argument that gets pattern matched on in `f` (including any internal function calls) should be made explicit in `h` and every other argument can be left implicit (there are a few exceptions to this rule, which we'll consider below, but it applies in most cases).

#### Example 1

`idᵥ⁺` mentions `_+′_` in its type:

    idᵥ⁺ : ∀ {A n m} -> Vec A (n +′ m) -> Vec A (n +′ m)

and `_+′_` pattern matches on `n`, hence Agda won't be able to infer `n`, i.e. the user will have to provide and so it should be made explicit:

    idᵥ⁺ : ∀ {A m} n -> Vec A (n +′ m) -> Vec A (n +′ m)

At the same time `_+′_` doesn't match on its second argument, `m`, hence we leave it implicit.

#### Example 2

A function mentioning `_∸_`

    _-_ : ℕ -> ℕ -> ℕ
    n     - zero  = n
    zero  - suc m = zero
    suc n - suc m = n - m

at type level has to receive both the arguments that get fed to `_∸_` explicitly as `_∸_` matches on both of them:

<pre>  <span class="agda2-highlight-function">id&#7525;&#8315;</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">&#8704;</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">A</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-bound-variable">m</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">Vec</span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-primitive">&#8760;</span></span> <span class="agda2-highlight-bound-variable">m</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">Vec</span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-primitive">&#8760;</span></span> <span class="agda2-highlight-bound-variable">m</span><span class="agda2-highlight-symbol">)</span>
  <span class="agda2-highlight-function">id&#7525;&#8315;</span> <span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-bound-variable">m</span> <span class="agda2-highlight-bound-variable">xs</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-bound-variable">xs</span>
</pre>
and none of

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">id&#7525;&#8315;</span> <span class="agda2-highlight-number">2</span> <span class="agda2-highlight-symbol"><span class="agda2-highlight-unsolved-meta">_</span></span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-number">1</span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-unsolved-constraint">&#8759;&#7525;</span></span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-inductive-constructor">[]&#7525;</span></span></span><span class="agda2-highlight-symbol">)</span>  <span class="comment">-- `m` can't be inferred</span>
  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">id&#7525;&#8315;</span> <span class="agda2-highlight-symbol"><span class="agda2-highlight-unsolved-meta">_</span></span> <span class="agda2-highlight-number">1</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-number">1</span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-unsolved-constraint">&#8759;&#7525;</span></span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-inductive-constructor">[]&#7525;</span></span></span><span class="agda2-highlight-symbol">)</span>  <span class="comment">-- `n` can't be inferred</span>
</pre>
is accepted unlike

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">id&#7525;&#8315;</span> <span class="agda2-highlight-number">2</span> <span class="agda2-highlight-number">1</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-number">1</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-inductive-constructor">[]&#7525;</span><span class="agda2-highlight-symbol">)</span>
</pre>
#### Example 3

A function mentioning `_*_`

    _*_ : ℕ -> ℕ -> ℕ
    zero  * m = zero
    suc n * m = m + n * m

at the type level has to receive both the arguments that get fed to `_*_` explicitly, even though `_*_` doesn't directly match on `m`. This is because in the second clause `_*_` expands to `_+_`, which does match on `m`. So it's

<pre>  <span class="agda2-highlight-function">id&#7525;*</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">&#8704;</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">A</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-bound-variable">m</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">Vec</span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-primitive">*</span></span> <span class="agda2-highlight-bound-variable">m</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">Vec</span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-primitive">*</span></span> <span class="agda2-highlight-bound-variable">m</span><span class="agda2-highlight-symbol">)</span>
  <span class="agda2-highlight-function">id&#7525;*</span> <span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-bound-variable">m</span> <span class="agda2-highlight-bound-variable">xs</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-bound-variable">xs</span>
</pre>
and none of

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">id&#7525;*</span> <span class="agda2-highlight-number">2</span> <span class="agda2-highlight-symbol"><span class="agda2-highlight-unsolved-meta">_</span></span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-number">1</span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-unsolved-constraint">&#8759;&#7525;</span></span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-number">2</span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-unsolved-constraint">&#8759;&#7525;</span></span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-inductive-constructor">[]&#7525;</span></span></span><span class="agda2-highlight-symbol">)</span>  <span class="comment">-- `m` can't be inferred</span>
  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">id&#7525;*</span> <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-number">1</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-number">1</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-number"><span class="agda2-highlight-unsolved-meta">2</span></span><span class="agda2-highlight-unsolved-meta"> </span><span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor"><span class="agda2-highlight-unsolved-meta">&#8759;&#7525;</span></span></span><span class="agda2-highlight-unsolved-meta"> </span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-inductive-constructor">[]&#7525;</span></span></span><span class="agda2-highlight-symbol">)</span>  <span class="comment">-- `n` can't be inferred</span>
</pre>
type check, unlike

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">id&#7525;*</span> <span class="agda2-highlight-number">2</span> <span class="agda2-highlight-number">1</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-number">1</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-number">2</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-inductive-constructor">[]&#7525;</span><span class="agda2-highlight-symbol">)</span>
</pre>
#### Example 4

With this definition:

<pre>  <span class="agda2-highlight-function">ignore2</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">&#8704;</span> <span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-bound-variable">m</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">Vec</span> <span class="agda2-highlight-datatype">&#8469;</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">+&#8242;</span></span> <span class="agda2-highlight-bound-variable">m</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">Vec</span> <span class="agda2-highlight-datatype">&#8469;</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">m</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">+&#8242;</span></span> <span class="agda2-highlight-bound-variable">n</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">&#8469;</span>
  <span class="agda2-highlight-function">ignore2</span> <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-number">0</span>
</pre>
it suffices to explicitly provide either `n` or `m`:

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">ignore2</span> <span class="agda2-highlight-number">2</span> <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-number">1</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-number">2</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-number">3</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-inductive-constructor">[]&#7525;</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-number">4</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-number">5</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-number">6</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-inductive-constructor">[]&#7525;</span><span class="agda2-highlight-symbol">)</span>
  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">ignore2</span> <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-number">1</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-number">1</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-number">2</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-number">3</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-inductive-constructor">[]&#7525;</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-number">4</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-number">5</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-number">6</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-inductive-constructor">[]&#7525;</span><span class="agda2-highlight-symbol">)</span>
</pre>
This is because with explicitly provided `n` Agda can determine `m` from `n +′ m` and with explicitly provided `m` Agda can determine `n` from `m +′ n`.

#### Example 5

In the following definition we have multiple mentions of `_+′_` at the type level:

<pre>  <span class="agda2-highlight-function">ignore2p</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">&#8704;</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">m</span> <span class="agda2-highlight-bound-variable">p</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">Vec</span> <span class="agda2-highlight-datatype">&#8469;</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">+&#8242;</span></span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">m</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">+&#8242;</span></span> <span class="agda2-highlight-bound-variable">p</span><span class="agda2-highlight-symbol">))</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">Vec</span> <span class="agda2-highlight-datatype">&#8469;</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">+&#8242;</span></span> <span class="agda2-highlight-bound-variable">m</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">&#8469;</span>
  <span class="agda2-highlight-function">ignore2p</span> <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-number">0</span>
</pre>
and three variables used as arguments to `_+′_`, yet only the `n` variable needs to be bound explicitly. This is due to the fact that it's enough to know `n` to determine what `m` is (from `Vec ℕ (n +′ m)`) and then knowing both `n` and `m` is enough to determine what `p` is (from `Vec ℕ (n +′ (m +′ p))`). Which can be written as

         n
         →
    n    m
    →→→→→→
       p

Note that the order of the `Vec` arguments doesn't matter, Agda will postpone resolving a metavariable until there is enough info to resolve it.

A test:

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">ignore2p</span> <span class="agda2-highlight-number">1</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-number">3</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-number">4</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-number">5</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-number">6</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-inductive-constructor">[]&#7525;</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-number">1</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-number">2</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-inductive-constructor">[]&#7525;</span><span class="agda2-highlight-symbol">)</span>
</pre>
#### Example 6

A very similar example:

<pre>  <span class="agda2-highlight-function">ignore1p</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">&#8704;</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">m</span> <span class="agda2-highlight-bound-variable">p</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">Vec</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-datatype">Vec</span> <span class="agda2-highlight-datatype">&#8469;</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">+&#8242;</span></span> <span class="agda2-highlight-bound-variable">m</span><span class="agda2-highlight-symbol">))</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">+&#8242;</span></span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">m</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">+&#8242;</span></span> <span class="agda2-highlight-bound-variable">p</span><span class="agda2-highlight-symbol">))</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">&#8469;</span>
  <span class="agda2-highlight-function">ignore1p</span> <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-number">0</span>
</pre>
Just like in the previous case it's enough to provide only `n` explicitly as the same

         n
         →
    n    m
    →→→→→→
       p

logic applies. Test:

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">ignore1p</span> <span class="agda2-highlight-number">1</span> <span class="agda2-highlight-symbol">((</span><span class="agda2-highlight-number">1</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-number">2</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-inductive-constructor">[]&#7525;</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-number">3</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-number">4</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-inductive-constructor">[]&#7525;</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-number">5</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-number">6</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-inductive-constructor">[]&#7525;</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-inductive-constructor">[]&#7525;</span><span class="agda2-highlight-symbol">)</span>
</pre>
#### Large elimination

<pre><span class="agda2-highlight-keyword">module</span> <span class="agda2-highlight-module">LargeElimination</span> <span class="agda2-highlight-keyword">where</span>
  <span class="agda2-highlight-keyword">open</span> <span class="agda2-highlight-module">BasicsOfTypeInference</span>
</pre>
So far we've been talking about functions that pattern match on terms and return terms, but in Agda we can also pattern match on terms and return types. Consider

<pre>  <span class="agda2-highlight-function">ListOfBoolOr&#8469;</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">Bool</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-primitive-type">Set</span>
  <span class="agda2-highlight-function">ListOfBoolOr&#8469;</span> <span class="agda2-highlight-inductive-constructor">false</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-datatype">List</span> <span class="agda2-highlight-datatype">Bool</span>
  <span class="agda2-highlight-function">ListOfBoolOr&#8469;</span> <span class="agda2-highlight-inductive-constructor">true</span>  <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-datatype">List</span> <span class="agda2-highlight-datatype">&#8469;</span>
</pre>
This function matches on a `Bool` argument and returns *the type* of lists with the type of elements depending on the `Bool` argument.

Having an identity function over a `ListOfBoolOrℕ b`

<pre>  <span class="agda2-highlight-function">idListOfBoolOr&#8469;</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">b</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">Bool</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-function">ListOfBoolOr&#8469;</span> <span class="agda2-highlight-bound-variable">b</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-function">ListOfBoolOr&#8469;</span> <span class="agda2-highlight-bound-variable">b</span>
  <span class="agda2-highlight-function">idListOfBoolOr&#8469;</span> <span class="agda2-highlight-bound-variable">xs</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-bound-variable">xs</span>
</pre>
we can show that the implicit `b` can't be inferred, as this:

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function"><span class="agda2-highlight-unsolved-meta">idListOfBoolOr&#8469;</span></span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-number">1</span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-unsolved-constraint">&#8759;</span></span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-number">2</span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-unsolved-constraint">&#8759;</span></span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-number">3</span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-unsolved-constraint">&#8759;</span></span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-inductive-constructor">[]</span></span></span><span class="agda2-highlight-symbol">)</span>
</pre>
results in unresolved metas, while this:

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">idListOfBoolOr&#8469;</span> <span class="agda2-highlight-symbol">{</span>b <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-inductive-constructor">true</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-number">1</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-number">2</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-number">3</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-inductive-constructor">[]</span><span class="agda2-highlight-symbol">)</span>
</pre>
is accepted by the type checker.

The reason for this behavior is the same as with all the previous examples: pattern matching blocks inference and `ListOfBoolOrℕ` is a pattern matching function.

### Generalization

<pre><span class="agda2-highlight-keyword">module</span> <span class="agda2-highlight-module">Generalization</span> <span class="agda2-highlight-keyword">where</span>
</pre>
In general: given a function `f` that receives `n` arguments on which there's pattern matching anywhere in the definition of `f` (including calls to other functions in the body of `f`) and `m` arguments on which there is no pattern matching, we have the following rule (for simplicity of presentation we place `pᵢ` before `xⱼ`, but the same rule works when they're interleaved)

    p₁    ...    pₙ        (f p₁ ... pₙ x₁ ... xₘ)
    →→→→→→→→→→→→→→→→→→→→→→→→→→→→→→→→→→→→→→→→→→→→→→
                  x₁    ...    xₘ

i.e. if every `pᵢ` can be inferred from the current context, then every `xⱼ` can be inferred from `f p₁ ... pₙ x₁ ... xₘ`.

There is an important exception from this rule and this is what comes next.

### [Constructor-headed functions](https://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.FindingTheValuesOfImplicitArguments)

<pre><span class="agda2-highlight-keyword">module</span> <span class="agda2-highlight-module">ConstructorHeadedFunctions</span> <span class="agda2-highlight-keyword">where</span>
  <span class="agda2-highlight-keyword">open</span> <span class="agda2-highlight-module">BasicsOfTypeInference</span>
  <span class="agda2-highlight-keyword">open</span> <span class="agda2-highlight-module">DataConstructors</span>
</pre>
Consider a definition of `ListOfBoolOrℕ` that is slightly different from the previous one, but is isomorphic to it:

<pre>  <span class="agda2-highlight-function">BoolOr&#8469;</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">Bool</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-primitive-type">Set</span>
  <span class="agda2-highlight-function">BoolOr&#8469;</span> <span class="agda2-highlight-inductive-constructor">false</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-datatype">Bool</span>
  <span class="agda2-highlight-function">BoolOr&#8469;</span> <span class="agda2-highlight-inductive-constructor">true</span>  <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-datatype">&#8469;</span>

  <span class="agda2-highlight-function">ListOfBoolOr&#8469;&#8242;</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">Bool</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-primitive-type">Set</span>
  <span class="agda2-highlight-function">ListOfBoolOr&#8469;&#8242;</span> <span class="agda2-highlight-bound-variable">b</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-datatype">List</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-function">BoolOr&#8469;</span> <span class="agda2-highlight-bound-variable">b</span><span class="agda2-highlight-symbol">)</span>
</pre>
Here `ListOfBoolOrℕ′` does not do any pattern matching itself and instead immediately returns `List (BoolOrℕ b)` with pattern matching performed in `BoolOrℕ b`. There's still pattern matching on `b` and the fact that it's inside another function call in the body of `ListOfBoolOrℕ′` does not change anything as we've discussed previously. Yet `id` defined over such lists:

<pre>  <span class="agda2-highlight-function">idListOfBoolOr&#8469;&#8242;</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">b</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">Bool</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-function">ListOfBoolOr&#8469;&#8242;</span> <span class="agda2-highlight-bound-variable">b</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-function">ListOfBoolOr&#8469;&#8242;</span> <span class="agda2-highlight-bound-variable">b</span>
  <span class="agda2-highlight-function">idListOfBoolOr&#8469;&#8242;</span> <span class="agda2-highlight-bound-variable">xs</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-bound-variable">xs</span>
</pre>
does not require the user to provide `b` explicitly, i.e. the following type checks just fine:

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">idListOfBoolOr&#8469;&#8242;</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-number">1</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-number">2</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-number">3</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-inductive-constructor">[]</span><span class="agda2-highlight-symbol">)</span>
</pre>
This works as follows: the expected type of an argument (`ListOfBoolOrℕ′ _b`) gets unified with the actual one (`List ℕ`):

    ListOfBoolOrℕ′ _b =?= List ℕ

after expanding `ListOfBoolOrℕ′` we get

    List (BoolOrℕ _b) =?= List ℕ

as usual `List` gets stripped from both the sides of the equation:

    BoolOrℕ _b =?= ℕ

and here Agda has a special rule, quoting the wiki:

> If all right hand sides of a function definition have distinct (type or value) constructor heads, we can deduce the shape of the arguments to the function by looking at the head of the expected result.

In our case two "constructor heads" in the definition of `BoolOrℕ` are `Bool` and `ℕ`, which are distinct, and that makes Agda see that `BoolOrℕ` is injective, so unifying `BoolOrℕ _b` with `ℕ` amounts to finding the clause where `ℕ` is returted from `BoolOrℕ`, which is

    BoolOrℕ true  = ℕ

and this determines that for the result to be `ℕ` the value of `_b` must be `true`, so the unification problem gets solved as

    _b := true

`BoolOrℕ` differs from

    ListOfBoolOrℕ : Bool -> Set
    ListOfBoolOrℕ false = List Bool
    ListOfBoolOrℕ true  = List ℕ

in that the latter definition has the same head in both the clauses (`List`) and so the heuristic doesn't apply. Even though Agda really could have figured out that `ListOfBoolOrℕ` is also injective. I.e. the fact that `ListOfBoolOrℕ` is not consdered invertible is more of an implementation detail than a theoretical limination.

Here's an example of a theoretical limitation: a definition like

<pre>  <span class="agda2-highlight-function">BoolOrBool</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">Bool</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-primitive-type">Set</span>
  <span class="agda2-highlight-function">BoolOrBool</span> <span class="agda2-highlight-inductive-constructor">true</span>  <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-datatype">Bool</span>
  <span class="agda2-highlight-function">BoolOrBool</span> <span class="agda2-highlight-inductive-constructor">false</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-datatype">Bool</span>
</pre>
can't be inverted, because the result (`Bool` in both the cases) does not determine the argument (either `true` or `false`).

#### Example 1: universe of types

There's a standard technique ([the universe pattern](https://groups.google.com/forum/#!msg/idris-lang/N9_pVqG8dO8/mHlNmyL6AwAJ)) that allows us to get ad hoc polymorphism (a.k.a. type classes) for a closed set of types in a dependently typed world.

We introduce a universe of types, which is a data type containing tags for actual types:

<pre>  <span class="agda2-highlight-keyword">data</span> <span class="agda2-highlight-datatype">Uni</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-primitive-type">Set</span> <span class="agda2-highlight-keyword">where</span>
    <span class="agda2-highlight-inductive-constructor">bool</span> <span class="agda2-highlight-inductive-constructor">nat</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">Uni</span>
    <span class="agda2-highlight-inductive-constructor">list</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">Uni</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">Uni</span>
</pre>
interpret those tags as types that they encode:

<pre>  <span class="agda2-highlight-operator"><span class="agda2-highlight-function">&#10214;_&#10215;</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">Uni</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-primitive-type">Set</span>
  <span class="agda2-highlight-operator"><span class="agda2-highlight-function">&#10214;</span></span> <span class="agda2-highlight-inductive-constructor">bool</span>   <span class="agda2-highlight-operator"><span class="agda2-highlight-function">&#10215;</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-datatype">Bool</span>
  <span class="agda2-highlight-operator"><span class="agda2-highlight-function">&#10214;</span></span> <span class="agda2-highlight-inductive-constructor">nat</span>    <span class="agda2-highlight-operator"><span class="agda2-highlight-function">&#10215;</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-datatype">&#8469;</span>
  <span class="agda2-highlight-operator"><span class="agda2-highlight-function">&#10214;</span></span> <span class="agda2-highlight-inductive-constructor">list</span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">&#10215;</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-datatype">List</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">&#10214;</span></span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">&#10215;</span></span>
</pre>
and then mimic the `Eq` type class for the types from this universe by directly defining equality functions:

<pre>  <span class="agda2-highlight-operator"><span class="agda2-highlight-function">_==Bool_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">Bool</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">Bool</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">Bool</span>
  <span class="agda2-highlight-inductive-constructor">true</span>  <span class="agda2-highlight-operator"><span class="agda2-highlight-function">==Bool</span></span> <span class="agda2-highlight-inductive-constructor">true</span>  <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-inductive-constructor">true</span>
  <span class="agda2-highlight-inductive-constructor">false</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">==Bool</span></span> <span class="agda2-highlight-inductive-constructor">false</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-inductive-constructor">true</span>
  <span class="agda2-highlight-symbol"><span class="agda2-highlight-catchall-clause">_</span></span><span class="agda2-highlight-catchall-clause">     </span><span class="agda2-highlight-operator"><span class="agda2-highlight-function"><span class="agda2-highlight-catchall-clause">==Bool</span></span></span><span class="agda2-highlight-catchall-clause"> </span><span class="agda2-highlight-symbol"><span class="agda2-highlight-catchall-clause">_</span></span>     <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-inductive-constructor">false</span>

  <span class="agda2-highlight-operator"><span class="agda2-highlight-function">_==&#8469;_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">&#8469;</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">&#8469;</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">Bool</span>
  <span class="agda2-highlight-inductive-constructor">zero</span>  <span class="agda2-highlight-operator"><span class="agda2-highlight-function">==&#8469;</span></span> <span class="agda2-highlight-inductive-constructor">zero</span>  <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-inductive-constructor">true</span>
  <span class="agda2-highlight-inductive-constructor">suc</span> <span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">==&#8469;</span></span> <span class="agda2-highlight-inductive-constructor">suc</span> <span class="agda2-highlight-bound-variable">m</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">==&#8469;</span></span> <span class="agda2-highlight-bound-variable">m</span>
  <span class="agda2-highlight-symbol"><span class="agda2-highlight-catchall-clause">_</span></span><span class="agda2-highlight-catchall-clause">     </span><span class="agda2-highlight-operator"><span class="agda2-highlight-function"><span class="agda2-highlight-catchall-clause">==&#8469;</span></span></span><span class="agda2-highlight-catchall-clause"> </span><span class="agda2-highlight-symbol"><span class="agda2-highlight-catchall-clause">_</span></span>     <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-inductive-constructor">false</span>

  <span class="agda2-highlight-keyword">mutual</span>
    <span class="agda2-highlight-operator"><span class="agda2-highlight-function">_==List_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">&#8704;</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">A</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">List</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">&#10214;</span></span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">&#10215;</span></span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">List</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">&#10214;</span></span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">&#10215;</span></span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">Bool</span>
    <span class="agda2-highlight-inductive-constructor">[]</span>       <span class="agda2-highlight-operator"><span class="agda2-highlight-function">==List</span></span> <span class="agda2-highlight-inductive-constructor">[]</span>       <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-inductive-constructor">true</span>
    <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">x</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-bound-variable">xs</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">==List</span></span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">y</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-bound-variable">ys</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">x</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">==</span></span> <span class="agda2-highlight-bound-variable">y</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">&amp;&amp;</span></span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">xs</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">==List</span></span> <span class="agda2-highlight-bound-variable">ys</span><span class="agda2-highlight-symbol">)</span>
    <span class="agda2-highlight-symbol"><span class="agda2-highlight-catchall-clause">_</span></span><span class="agda2-highlight-catchall-clause">        </span><span class="agda2-highlight-operator"><span class="agda2-highlight-function"><span class="agda2-highlight-catchall-clause">==List</span></span></span><span class="agda2-highlight-catchall-clause"> </span><span class="agda2-highlight-symbol"><span class="agda2-highlight-catchall-clause">_</span></span>        <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-inductive-constructor">false</span>

    <span class="agda2-highlight-operator"><span class="agda2-highlight-function">_==_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">&#8704;</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">A</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">&#10214;</span></span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">&#10215;</span></span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">&#10214;</span></span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">&#10215;</span></span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">Bool</span>
    <span class="agda2-highlight-operator"><span class="agda2-highlight-function">_==_</span></span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-inductive-constructor">nat</span>   <span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-bound-variable">x</span> <span class="agda2-highlight-bound-variable">y</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-bound-variable">x</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">==&#8469;</span></span>    <span class="agda2-highlight-bound-variable">y</span>
    <span class="agda2-highlight-operator"><span class="agda2-highlight-function">_==_</span></span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-inductive-constructor">bool</span>  <span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-bound-variable">x</span> <span class="agda2-highlight-bound-variable">y</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-bound-variable">x</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">==Bool</span></span> <span class="agda2-highlight-bound-variable">y</span>
    <span class="agda2-highlight-operator"><span class="agda2-highlight-function">_==_</span></span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-inductive-constructor">list</span> <span class="agda2-highlight-bound-variable">A</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-bound-variable">x</span> <span class="agda2-highlight-bound-variable">y</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-bound-variable">x</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">==List</span></span> <span class="agda2-highlight-bound-variable">y</span>
</pre>
`_==_` checks equality of two elements from any type from the universe.

Note that `_==List_` is defined mutually with `_==_`, because elements of lists can be of any type from the universe, i.e. they can also be lists, hence the mutual recursion.

A few tests:

<pre>  <span class="comment">-- Check equality of two equal elements of `&#8469;`.</span>
  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-number">42</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">==</span></span> <span class="agda2-highlight-number">42</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-datatype">&#8801;</span></span> <span class="agda2-highlight-inductive-constructor">true</span>
  <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-inductive-constructor">refl</span>

  <span class="comment">-- Check equality of two non-equal elements of `List Bool`.</span>
  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">((</span><span class="agda2-highlight-inductive-constructor">true</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-inductive-constructor">[]</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">==</span></span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-inductive-constructor">false</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-inductive-constructor">[]</span><span class="agda2-highlight-symbol">))</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-datatype">&#8801;</span></span> <span class="agda2-highlight-inductive-constructor">false</span>
  <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-inductive-constructor">refl</span>

  <span class="comment">-- Check equality of two equal elements of `List (List &#8469;)`.</span>
  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">(((</span><span class="agda2-highlight-number">4</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-number">81</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-inductive-constructor">[]</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-number">57</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-number">2</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-inductive-constructor">[]</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-inductive-constructor">[]</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">==</span></span> <span class="agda2-highlight-symbol">((</span><span class="agda2-highlight-number">4</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-number">81</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-inductive-constructor">[]</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-number">57</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-number">2</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-inductive-constructor">[]</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-inductive-constructor">[]</span><span class="agda2-highlight-symbol">))</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-datatype">&#8801;</span></span> <span class="agda2-highlight-inductive-constructor">true</span>
  <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-inductive-constructor">refl</span>

  <span class="comment">-- Check equality of two non-equal elements of `List (List &#8469;)`.</span>
  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">(((</span><span class="agda2-highlight-number">4</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-number">81</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-inductive-constructor">[]</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-number">57</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-number">2</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-inductive-constructor">[]</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-inductive-constructor">[]</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">==</span></span> <span class="agda2-highlight-symbol">((</span><span class="agda2-highlight-number">4</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-number">81</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-inductive-constructor">[]</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-inductive-constructor">[]</span><span class="agda2-highlight-symbol">))</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-datatype">&#8801;</span></span> <span class="agda2-highlight-inductive-constructor">false</span>
  <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-inductive-constructor">refl</span>
</pre>
It's possible to leave `A` implicit in `_==_` and get it inferred in the tests above precisely because `⟦_⟧` is constructor-headed. If we had `bool₁` and `bool₂` tags both mapping to `Bool`, inference for `_==_` would not work for booleans, lists of booleans etc. In the version of Agda I'm using inference for naturals, lists of naturals etc still works though, if an additional `bool` is added to the universe, i.e. breaking constructor-headedness of a function for certain arguments does not result in inference being broken for others.

#### Example 2: `boolToℕ`

Constructor-headed functions can also return values rather than types. For example this function:

<pre>  <span class="agda2-highlight-function">boolTo&#8469;</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">Bool</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">&#8469;</span>
  <span class="agda2-highlight-function">boolTo&#8469;</span> <span class="agda2-highlight-inductive-constructor">false</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-inductive-constructor">zero</span>
  <span class="agda2-highlight-function">boolTo&#8469;</span> <span class="agda2-highlight-inductive-constructor">true</span>  <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-inductive-constructor">suc</span> <span class="agda2-highlight-inductive-constructor">zero</span>
</pre>
is constructor-headed, because in the two clauses heads are constructors and they're different (`zero` vs `suc`).

So if we define a version of `id` that takes a `Vec` with either 0 or 1 element:

<pre>  <span class="agda2-highlight-function">idVecAsMaybe</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">&#8704;</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">b</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">Vec</span> <span class="agda2-highlight-datatype">&#8469;</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-function">boolTo&#8469;</span> <span class="agda2-highlight-bound-variable">b</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">Vec</span> <span class="agda2-highlight-datatype">&#8469;</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-function">boolTo&#8469;</span> <span class="agda2-highlight-bound-variable">b</span><span class="agda2-highlight-symbol">)</span>
  <span class="agda2-highlight-function">idVecAsMaybe</span> <span class="agda2-highlight-bound-variable">xs</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-bound-variable">xs</span>
</pre>
then it won't be necessary to specify `b`:

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">idVecAsMaybe</span> <span class="agda2-highlight-inductive-constructor">[]&#7525;</span>
  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">idVecAsMaybe</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-number">0</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-inductive-constructor">[]&#7525;</span><span class="agda2-highlight-symbol">)</span>
</pre>
as Agda knows how to solve `boolToℕ _b =?= zero` or `boolToℕ _b =?= suc zero` due to `boolToℕ` being invertible.

`idVecAsMaybe` supplied with a vector of length greater than `1` correctly gives an error (as opposed to merely reporting that there's an unsolved meta):

    -- suc _n_624 != zero of type ℕ
    _ = idVecAsMaybe (0 ∷ᵥ 1 ∷ᵥ []ᵥ)

Note that `boolToℕ` defined like that:

<pre>  <span class="agda2-highlight-function">boolTo&#8469;&#8242;</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">Bool</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">&#8469;</span>
  <span class="agda2-highlight-function">boolTo&#8469;&#8242;</span> <span class="agda2-highlight-inductive-constructor">false</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-inductive-constructor">zero</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-primitive">+</span></span> <span class="agda2-highlight-inductive-constructor">zero</span>
  <span class="agda2-highlight-function">boolTo&#8469;&#8242;</span> <span class="agda2-highlight-inductive-constructor">true</span>  <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-inductive-constructor">suc</span> <span class="agda2-highlight-inductive-constructor">zero</span>
</pre>
is not considered to be constructor-headed, because Agda does not attempt to unfold recursive definitions in the RHS of a clause of a function. With this definition the second test in

<pre>  <span class="agda2-highlight-function">idVecAsMaybe&#8242;</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">&#8704;</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">b</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">Vec</span> <span class="agda2-highlight-datatype">&#8469;</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-function">boolTo&#8469;&#8242;</span> <span class="agda2-highlight-bound-variable">b</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">Vec</span> <span class="agda2-highlight-datatype">&#8469;</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-function">boolTo&#8469;&#8242;</span> <span class="agda2-highlight-bound-variable">b</span><span class="agda2-highlight-symbol">)</span>
  <span class="agda2-highlight-function">idVecAsMaybe&#8242;</span> <span class="agda2-highlight-bound-variable">xs</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-bound-variable">xs</span>

  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">idVecAsMaybe&#8242;</span> <span class="agda2-highlight-inductive-constructor">[]&#7525;</span>
  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function"><span class="agda2-highlight-unsolved-meta">idVecAsMaybe&#8242;</span></span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-number">0</span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-unsolved-constraint">&#8759;&#7525;</span></span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-inductive-constructor">[]&#7525;</span></span></span><span class="agda2-highlight-symbol">)</span>
</pre>
is yellow. But not the first one. I guess with `idVecAsMaybe′ []ᵥ` Agda tries to unify `zero` (the actual length of the vector) with both the RHSes of `boolToℕ′` and since `zero` is definitely not equal to `suc zero`, only the `zero + zero` case remains, so Agda finally decides to reduce that expression to find out that it indeed equals to `zero`.

### Constructor/argument-headed functions

<pre><span class="agda2-highlight-keyword">module</span> <span class="agda2-highlight-module">ConstructorArgumentHeadedFunctions</span> <span class="agda2-highlight-keyword">where</span>
  <span class="agda2-highlight-keyword">open</span> <span class="agda2-highlight-module">DataConstructors</span>
</pre>
Recall that we've been using a weird definition of plus

> because the usual one
>
>     _+_ : ℕ -> ℕ -> ℕ
>     zero  + m = m
>     suc n + m = suc (n + m)
>
> is subject to certain unification heuristics, which the weird one doesn't trigger.

The usual definition is this one:

    _+_ : ℕ -> ℕ -> ℕ
    zero  + m = m
    suc n + m = suc (n + m)

As you can see here we return one of the arguments in the first clause and the second clause is constructor-headed. Just like for regular constructor-headed function, Agda has enhanced inference for functions of this kind as well.

Quoting the [changelog](https://github.com/agda/agda/blob/064095e14042bdf64c7d7c97c2869f63f5f1f8f6/doc/release-notes/2.5.4.md#pattern-matching):

> Improved constraint solving for pattern matching functions
> Constraint solving for functions where each right-hand side has a distinct rigid head has been extended to also cover the case where some clauses return an argument of the function. A typical example is append on lists:
>
>     _++_ : {A : Set} → List A → List A → List A
>     []       ++ ys = ys
>     (x ∷ xs) ++ ys = x ∷ (xs ++ ys)
>
> Agda can now solve constraints like ?X ++ ys == 1 ∷ ys when ys is a neutral term.

#### Example 1: back to `idᵥ⁺`

Now if we come back to this example (TODO: add proper quote rendering somehow?):

<blockquote>
<p><code>idᵥ⁺</code> applied to a non-constant vector has essentially the same inference properties.</p>
<p>Without specializing the implicit arguments we get yellow:</p>
<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-symbol">&#955;</span> <span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-bound-variable">m</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">xs</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">Vec</span> <span class="agda2-highlight-datatype">&#8469;</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">+&#8242;</span></span> <span class="agda2-highlight-bound-variable">m</span><span class="agda2-highlight-symbol">))</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-function"><span class="agda2-highlight-unsolved-meta">id&#7525;&#8314;</span></span> <span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-bound-variable">xs</span></span></span>
</pre>
<p>Specializing <code>m</code> doesn't help, still yellow:</p>
<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-symbol">&#955;</span> <span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-bound-variable">m</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">xs</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">Vec</span> <span class="agda2-highlight-datatype">&#8469;</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">+&#8242;</span></span> <span class="agda2-highlight-bound-variable">m</span><span class="agda2-highlight-symbol">))</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-function"><span class="agda2-highlight-unsolved-meta">id&#7525;&#8314;</span></span> <span class="agda2-highlight-symbol">{</span>m <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-bound-variable">m</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-bound-variable">xs</span></span></span>
</pre>
</blockquote>

but if define `idᵥ⁺` over `_+_` rather than `_+′_`:

<pre>  <span class="agda2-highlight-function">id&#7525;&#8314;</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">&#8704;</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-bound-variable">m</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">Vec</span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-primitive">+</span></span> <span class="agda2-highlight-bound-variable">m</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">Vec</span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-primitive">+</span></span> <span class="agda2-highlight-bound-variable">m</span><span class="agda2-highlight-symbol">)</span>
  <span class="agda2-highlight-function">id&#7525;&#8314;</span> <span class="agda2-highlight-bound-variable">xs</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-bound-variable">xs</span>
</pre>
then supplying only `m` explicitly:

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-symbol">&#955;</span> <span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-bound-variable">m</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">xs</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">Vec</span> <span class="agda2-highlight-datatype">&#8469;</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-primitive">+</span></span> <span class="agda2-highlight-bound-variable">m</span><span class="agda2-highlight-symbol">))</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-function">id&#7525;&#8314;</span> <span class="agda2-highlight-symbol">{</span>m <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-bound-variable">m</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-bound-variable">xs</span>
</pre>
satisfies the type checker.

And

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-symbol">&#955;</span> <span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-bound-variable">m</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">xs</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">Vec</span> <span class="agda2-highlight-datatype">&#8469;</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-primitive">+</span></span> <span class="agda2-highlight-bound-variable">m</span><span class="agda2-highlight-symbol">))</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-function"><span class="agda2-highlight-unsolved-meta">id&#7525;&#8314;</span></span> <span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-bound-variable">xs</span></span></span>
</pre>
still gives yellow, because it's still inherently ambiguous.

Additionally, this now also type checks:

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">id&#7525;&#8314;</span> <span class="agda2-highlight-symbol">{</span>m <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-number">0</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-number">1</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-number">2</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-inductive-constructor">[]&#7525;</span><span class="agda2-highlight-symbol">)</span>
</pre>
This is because instantiating `m` at `0` in `idᵥ⁺` makes `_+_` constructor-headed, because if we inline `m` in the definition of `_+_`, we'll get:

    _+0 : ℕ -> ℕ
    zero  +0 = zero
    suc n +0 = suc (n +0)

which is clearly constructor-headed.

And

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function"><span class="agda2-highlight-unsolved-meta">id&#7525;&#8314;</span></span> <span class="agda2-highlight-symbol">{</span>m <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-number">1</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-number">1</span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-unsolved-constraint">&#8759;&#7525;</span></span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-number">2</span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-unsolved-constraint">&#8759;&#7525;</span></span></span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"> </span></span><span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-inductive-constructor">[]&#7525;</span></span></span><span class="agda2-highlight-symbol">)</span>
</pre>
still does not type check, because inlining `m` as `1` does not make `_+_` constructor-headed:

    _+1 : ℕ -> ℕ
    zero  +1 = suc zero
    suc n +1 = suc (n +1)

#### Example 2: polyvariadic `zip`

<pre><span class="agda2-highlight-keyword">module</span> <span class="agda2-highlight-module">PolyvariadicZip</span> <span class="agda2-highlight-keyword">where</span>
  <span class="agda2-highlight-keyword">open</span> <span class="agda2-highlight-keyword">import</span> <span class="agda2-highlight-module">Data.List.Base</span> <span class="agda2-highlight-symbol">as</span> <span class="agda2-highlight-module">List</span>
  <span class="agda2-highlight-keyword">open</span> <span class="agda2-highlight-keyword">import</span> <span class="agda2-highlight-module">Data.Vec.Base</span> <span class="agda2-highlight-symbol">as</span> <span class="agda2-highlight-module">Vec</span> <span class="agda2-highlight-keyword">renaming</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">_&#8759;_</span></span> <span class="agda2-highlight-symbol">to</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">_&#8759;&#7525;_</span></span><span class="agda2-highlight-symbol">;</span> <span class="agda2-highlight-inductive-constructor">[]</span> <span class="agda2-highlight-symbol">to</span> <span class="agda2-highlight-inductive-constructor">[]&#7525;</span><span class="agda2-highlight-symbol">)</span>
</pre>
We can define this family of functions over vectors:

    replicate : ∀ {n} → A → Vec A n
    map : ∀ {n} → (A → B) → Vec A n → Vec B n
    zipWith : ∀ {n} → (A → B → C) → Vec A n → Vec B n → Vec C n
    zipWith3 : ∀ {n} → (A → B → C → D) → Vec A n → Vec B n → Vec C n → Vec D n

(the Agda stdlib provides all of those but the last one)

Can we define a generic function that covers all of the above? Its type signature should look like this:

    (A₁ -> A₂ -> ... -> B) -> Vec A₁ n -> Vec A₂ n -> ... -> Vec B n

Yes: we can parameterize a function by a list of types and compute those n-ary types from the list. Folding a list of types into a type, given also the type of the result, is trivial:

<pre>  <span class="agda2-highlight-function">ToFun</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">List</span> <span class="agda2-highlight-primitive-type">Set</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-primitive-type">Set</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-primitive-type">Set</span>
  <span class="agda2-highlight-function">ToFun</span>  <span class="agda2-highlight-inductive-constructor">[]</span>      <span class="agda2-highlight-bound-variable">B</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-bound-variable">B</span>
  <span class="agda2-highlight-function">ToFun</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-bound-variable">As</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-bound-variable">B</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-function">ToFun</span> <span class="agda2-highlight-bound-variable">As</span> <span class="agda2-highlight-bound-variable">B</span>
</pre>
This allows us to compute the n-ary type of the function. In order to compute the n-ary type of the result we need to map the list of types with `λ A -> Vec A n` and turn `B` (the type of the resulting of the zipping function) into `Vec B n` (the type of the final result):

<pre>  <span class="agda2-highlight-function">ToVecFun</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">List</span> <span class="agda2-highlight-primitive-type">Set</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-primitive-type">Set</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">&#8469;</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-primitive-type">Set</span>
  <span class="agda2-highlight-function">ToVecFun</span> <span class="agda2-highlight-bound-variable">As</span> <span class="agda2-highlight-bound-variable">B</span> <span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">ToFun</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-function">List.map</span> <span class="agda2-highlight-symbol">(&#955;</span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">Vec</span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-bound-variable">n</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-bound-variable">As</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-datatype">Vec</span> <span class="agda2-highlight-bound-variable">B</span> <span class="agda2-highlight-bound-variable">n</span><span class="agda2-highlight-symbol">)</span>
</pre>
It only remains to recurse on the list of types in an auxiliary function (n-ary `(<*>)`, using Haskell jargon) and define `zipN` in terms of that function:

<pre>  <span class="agda2-highlight-function">apN</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">&#8704;</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">As</span> <span class="agda2-highlight-bound-variable">B</span> <span class="agda2-highlight-bound-variable">n</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">Vec</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-function">ToFun</span> <span class="agda2-highlight-bound-variable">As</span> <span class="agda2-highlight-bound-variable">B</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-function">ToVecFun</span> <span class="agda2-highlight-bound-variable">As</span> <span class="agda2-highlight-bound-variable">B</span> <span class="agda2-highlight-bound-variable">n</span>
  <span class="agda2-highlight-function">apN</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-inductive-constructor">[]</span><span class="agda2-highlight-symbol">}</span>     <span class="agda2-highlight-bound-variable">ys</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-bound-variable">ys</span>
  <span class="agda2-highlight-function">apN</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;</span></span> <span class="agda2-highlight-bound-variable">As</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-bound-variable">fs</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-symbol">&#955;</span> <span class="agda2-highlight-bound-variable">xs</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-function">apN</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">As</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">fs</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">&#8859;</span></span> <span class="agda2-highlight-bound-variable">xs</span><span class="agda2-highlight-symbol">)</span>

  <span class="agda2-highlight-function">zipN</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">&#8704;</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">As</span> <span class="agda2-highlight-bound-variable">B</span> <span class="agda2-highlight-bound-variable">n</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-function">ToFun</span> <span class="agda2-highlight-bound-variable">As</span> <span class="agda2-highlight-bound-variable">B</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-function">ToVecFun</span> <span class="agda2-highlight-bound-variable">As</span> <span class="agda2-highlight-bound-variable">B</span> <span class="agda2-highlight-bound-variable">n</span>
  <span class="agda2-highlight-function">zipN</span> <span class="agda2-highlight-bound-variable">f</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-function">apN</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-function">Vec.replicate</span> <span class="agda2-highlight-bound-variable">f</span><span class="agda2-highlight-symbol">)</span>
</pre>
Some tests verifying that the function does what it's supposed to:

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-function">zipN</span> <span class="agda2-highlight-number">1</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-datatype">&#8801;</span></span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-number">1</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-number">1</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-number">1</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-inductive-constructor">[]&#7525;</span><span class="agda2-highlight-symbol">)</span>
  <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-inductive-constructor">refl</span>

  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-function">zipN</span> <span class="agda2-highlight-inductive-constructor">suc</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-number">1</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-number">2</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-number">3</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-inductive-constructor">[]&#7525;</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-datatype">&#8801;</span></span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-number">2</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-number">3</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-number">4</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-inductive-constructor">[]&#7525;</span><span class="agda2-highlight-symbol">)</span>
  <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-inductive-constructor">refl</span>

  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-function">zipN</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-primitive">_+_</span></span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-number">1</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-number">2</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-number">3</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-inductive-constructor">[]&#7525;</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-number">4</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-number">5</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-number">6</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-inductive-constructor">[]&#7525;</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-datatype">&#8801;</span></span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-number">5</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-number">7</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-number">9</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-inductive-constructor">[]&#7525;</span><span class="agda2-highlight-symbol">)</span>
  <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-inductive-constructor">refl</span>
</pre>
Note how we do not provide the list of types explicitly in any of these cases, even though there's pattern matching on that list.

Your first guess is probably that Agda can infer the list of types from the type of the function passed to `zipN`. I.e. the type of `_+_` is `ℕ -> ℕ -> ℕ` and so it corresponds to `Fun (ℕ ∷ ℕ ∷ []) ℕ`. But that is not really clear to Agda as this snippet:

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-function">ToFun</span> <span class="agda2-highlight-symbol"><span class="agda2-highlight-unsolved-meta">_</span></span> <span class="agda2-highlight-symbol"><span class="agda2-highlight-unsolved-meta">_</span></span> <span class="agda2-highlight-operator"><span class="agda2-highlight-datatype">&#8801;</span></span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-datatype">&#8469;</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">&#8469;</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">&#8469;</span><span class="agda2-highlight-symbol">)</span>
  <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-inductive-constructor">refl</span></span></span>
</pre>
gives yellow. And this is for a good reason, there are three ways to compute `ℕ -> ℕ -> ℕ` with `ToFun`:

    ToFun (ℕ ∷ ℕ ∷ [])  ℕ             -- The obvious one.
    ToFun (ℕ ∷ [])     (ℕ -> ℕ)       -- A sneaky one.
    ToFun []           (ℕ -> ℕ -> ℕ)  -- Another sneaky one.

So the `ToFun _As _B =?= ℕ -> ℕ -> ℕ` unification problem does not have a single solution and hence can't be solved by Agda.

However Agda sees that `zipN _+_` is applied to two vectors and the result is also a vector and since in the type signature of `zipN`

    zipN : ∀ {As B n} -> ToFun As B -> ToVecFun As B n

the types of the arguments and the result are computed from `ToVecFun As B n`, we have the following unification problem:

    ToVecFun _As _B _n =?= Vec ℕ m -> Vec ℕ m -> Vec ℕ m

which Agda can immediately solve as

    _As := ℕ ∷ ℕ ∷ []
    _B  := ℕ
    _n  := m

And indeed there's no yellow here:

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">&#8704;</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">m</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-function">ToVecFun</span> <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-datatype">&#8801;</span></span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-datatype">Vec</span> <span class="agda2-highlight-datatype">&#8469;</span> <span class="agda2-highlight-bound-variable">m</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">Vec</span> <span class="agda2-highlight-datatype">&#8469;</span> <span class="agda2-highlight-bound-variable">m</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-datatype">Vec</span> <span class="agda2-highlight-datatype">&#8469;</span> <span class="agda2-highlight-bound-variable">m</span><span class="agda2-highlight-symbol">)</span>
  <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-inductive-constructor">refl</span>
</pre>
The reason for that is that `ToVecFun` does not return an arbitrary `B` in the `[]` case like `ToFun` -- `ToVecFun` always returns a `Vec` in the `[]` case, so resolving metas as

    _As := ℕ ∷ []
    _B  := ℕ -> ℕ
    _n  := m

is not possible as that would compute to `Vec ℕ m -> Vec (ℕ -> ℕ) m` rather than `Vec ℕ m -> Vec ℕ m -> Vec ℕ m`.

Hence there's no ambiguity now and since `ToVecFun` also returns a `_->_` in the `_∷_` case, that function is constructor-headed (as `Vec` and `_->_` are two different type constructors) and Agda knows how to infer the list of types.

If we omit the resulting vector, we'll get yellow:

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-function"><span class="agda2-highlight-unsolved-meta">zipN</span></span><span class="agda2-highlight-unsolved-meta"> </span><span class="agda2-highlight-operator"><span class="agda2-highlight-primitive"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-unsolved-constraint">_+_</span></span></span></span><span class="agda2-highlight-unsolved-meta"> </span><span class="agda2-highlight-symbol"><span class="agda2-highlight-unsolved-meta">(</span></span><span class="agda2-highlight-number"><span class="agda2-highlight-unsolved-meta">1</span></span><span class="agda2-highlight-unsolved-meta"> </span><span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor"><span class="agda2-highlight-unsolved-meta">&#8759;&#7525;</span></span></span><span class="agda2-highlight-unsolved-meta"> </span><span class="agda2-highlight-number"><span class="agda2-highlight-unsolved-meta">2</span></span><span class="agda2-highlight-unsolved-meta"> </span><span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor"><span class="agda2-highlight-unsolved-meta">&#8759;&#7525;</span></span></span><span class="agda2-highlight-unsolved-meta"> </span><span class="agda2-highlight-number"><span class="agda2-highlight-unsolved-meta">3</span></span><span class="agda2-highlight-unsolved-meta"> </span><span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor"><span class="agda2-highlight-unsolved-meta">&#8759;&#7525;</span></span></span><span class="agda2-highlight-unsolved-meta"> </span><span class="agda2-highlight-inductive-constructor"><span class="agda2-highlight-unsolved-meta">[]&#7525;</span></span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-number">4</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-number">5</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-number">6</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-inductive-constructor">[]&#7525;</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-datatype">&#8801;</span></span> <span class="agda2-highlight-symbol">_</span>
  <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-inductive-constructor">refl</span>

</pre>
as a standlone

    ToVecFun _As _B _n =?= Vec ℕ m -> Vec ℕ m -> _R

is inherently ambiguous again and Agda would need to do some non-trivial proof search in order to realize that `_R` can't be an `_->_` due to the other equation:

    ToFun _As _B =?= ℕ -> ℕ -> ℕ

Omitting an argument also results in metas not being resolved:

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-function">zipN</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-primitive">_+_</span></span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-number">1</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-number">2</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-number">3</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-inductive-constructor">[]&#7525;</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-datatype">&#8801;</span></span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-number">5</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-number">7</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-number">9</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-inductive-constructor">&#8759;&#7525;</span></span> <span class="agda2-highlight-inductive-constructor">[]&#7525;</span><span class="agda2-highlight-symbol">)</span>
  <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-inductive-constructor"><span class="agda2-highlight-unsolved-meta">refl</span></span>
</pre>
but that is something that I can't explain, I can't spot any problem with solving

    ToVecFun _As _B _n ≡ (Vec ℕ m -> _ -> Vec ℕ m)

with

    _As := Vec ℕ m ∷ Vec ℕ m ∷ []
    _B  := Vec ℕ m
    _n  := m

Note also that constructor-headedness is compositional. The

    ToVecFun _As _B _n =?= Vec ℕ m -> Vec ℕ m -> Vec ℕ m

problem expands to

    ToFun (List.map (λ A -> Vec A n) _As) (Vec _B _n) =?= Vec ℕ m -> Vec ℕ m -> Vec ℕ m

Agda sees that the RHS was computed from the `_∷_` case of `ToFun`, but the actual argument of `ToFun` is not a meta or a `_∷_` already, it's a `List.map (λ A -> Vec A n) _As` and so Agda needs to invert `List.map` for unification to proceed. Which is no problem, since `List.map` is also constructor-headed.

## Eta-rules

<pre><span class="agda2-highlight-keyword">module</span> <span class="agda2-highlight-module">EtaRules</span> <span class="agda2-highlight-keyword">where</span>
</pre>
Agda implements eta-rules for [negative types](https://ncatlab.org/nlab/show/negative+type).

One such rule is that a function is definitionally equal to its eta-expanded version:

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">&#8704;</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-primitive-type">Set</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">B</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-primitive-type">Set</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">f</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">&#8704;</span> <span class="agda2-highlight-bound-variable">x</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">B</span> <span class="agda2-highlight-bound-variable">x</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">f</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-datatype">&#8801;</span></span> <span class="agda2-highlight-symbol">(&#955;</span> <span class="agda2-highlight-bound-variable">x</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">f</span> <span class="agda2-highlight-bound-variable">x</span><span class="agda2-highlight-symbol">))</span>
  <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-symbol">&#955;</span> <span class="agda2-highlight-bound-variable">f</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-inductive-constructor">refl</span>
</pre>
Usefulness of this eta-rule is not something that one thinks of much, but that is only until they try to work in a language that doesn't support the rule (spoiler: it's a huge pain).

All records support eta-rules by default (that can be switched off for a single record via an explicit [`no-eta-equality`](https://agda.readthedocs.io/en/v2.6.1/language/record-types.html#eta-expansion) mark or for all records in a file via `{-# OPTIONS --no-eta-equality #-}` at the beginning of the file).

The simplest record is one with no fields:

<pre>  <span class="agda2-highlight-keyword">record</span> <span class="agda2-highlight-record">Unit</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-primitive-type">Set</span> <span class="agda2-highlight-keyword">where</span>
    <span class="agda2-highlight-keyword">constructor</span> <span class="agda2-highlight-inductive-constructor">unit</span>
</pre>
The eta-rule for `Unit` is "all terms of type `Unit` are equal to `unit`":

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">u</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-record">Unit</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">u</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-datatype">&#8801;</span></span> <span class="agda2-highlight-inductive-constructor">unit</span>
  <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-symbol">&#955;</span> <span class="agda2-highlight-bound-variable">u</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-inductive-constructor">refl</span>
</pre>
Consequently, since all terms of type `Unit` are equal to `unit`, they are also equal to each other:

<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">u1</span> <span class="agda2-highlight-bound-variable">u2</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-record">Unit</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">u1</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-datatype">&#8801;</span></span> <span class="agda2-highlight-bound-variable">u2</span>
  <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-symbol">&#955;</span> <span class="agda2-highlight-bound-variable">u1</span> <span class="agda2-highlight-bound-variable">u2</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-inductive-constructor">refl</span>
</pre>
This eta-rule applies to `⊤`, precisely because `⊤` is defined as a record with no fields.

For a record with fields the eta-rule is "an element of the record is always the constructor of the record applied to its fields". For example:

<pre>  <span class="agda2-highlight-keyword">record</span> <span class="agda2-highlight-record">Triple</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-bound-variable">B</span> <span class="agda2-highlight-bound-variable">C</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-primitive-type">Set</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-primitive-type">Set</span> <span class="agda2-highlight-keyword">where</span>
    <span class="agda2-highlight-keyword">constructor</span> <span class="agda2-highlight-inductive-constructor">triple</span>
    <span class="agda2-highlight-keyword">field</span>
      <span class="agda2-highlight-field">fst</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-bound-variable">A</span>
      <span class="agda2-highlight-field">snd</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-bound-variable">B</span>
      <span class="agda2-highlight-field">thd</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-bound-variable">C</span>
  <span class="agda2-highlight-keyword">open</span> <span class="agda2-highlight-module">Triple</span>

  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">&#8704;</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-bound-variable">B</span> <span class="agda2-highlight-bound-variable">C</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">t</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-record">Triple</span> <span class="agda2-highlight-bound-variable">A</span> <span class="agda2-highlight-bound-variable">B</span> <span class="agda2-highlight-bound-variable">C</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">t</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-datatype">&#8801;</span></span> <span class="agda2-highlight-inductive-constructor">triple</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-field">fst</span> <span class="agda2-highlight-bound-variable">t</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-field">snd</span> <span class="agda2-highlight-bound-variable">t</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-field">thd</span> <span class="agda2-highlight-bound-variable">t</span><span class="agda2-highlight-symbol">)</span>
  <span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-symbol">&#955;</span> <span class="agda2-highlight-bound-variable">t</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-inductive-constructor">refl</span>
</pre>
Supporting eta-equality for sum types is [possible in theory](https://ncatlab.org/nlab/show/sum+type#as_a_positive_type), but Agda does not implement that. Any `data` definition in Agda does not support eta-equality, including an empty `data` declaration like

<pre>  <span class="agda2-highlight-keyword">data</span> <span class="agda2-highlight-datatype">Empty</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-primitive-type">Set</span> <span class="agda2-highlight-keyword">where</span>
</pre>
(which is always isomorphic to `Data.Empty.⊥` and is how `⊥` is defined in the first place).

Eta-rules for records may seem not too exciting, but there are a few important use cases.






### Computing predicates

### N-ary things

  -- _ : Vec.map suc (1 ∷ᵥ 2 ∷ᵥ 3 ∷ᵥ []ᵥ) ≡ _
  -- _ = refl

  -- _ : Vec.zipWith _+_ (1 ∷ᵥ 2 ∷ᵥ 3 ∷ᵥ []ᵥ) (4 ∷ᵥ 5 ∷ᵥ 6 ∷ᵥ []ᵥ) ≡ _
  -- _ = refl

  -- _ : zipN suc (1 ∷ᵥ 2 ∷ᵥ 3 ∷ᵥ []ᵥ) ≡ _
  -- _ = refl

  -- _ : zipN _+_ (1 ∷ᵥ 2 ∷ᵥ 3 ∷ᵥ []ᵥ) (4 ∷ᵥ 5 ∷ᵥ 6 ∷ᵥ []ᵥ) ≡ _
  -- _ = refl

  -- _ : zipN {_ ∷ []} suc (1 ∷ᵥ 2 ∷ᵥ 3 ∷ᵥ []ᵥ) ≡ _
  -- _ = refl

  -- _ : zipN {_ ∷ _ ∷ []} _+_ (1 ∷ᵥ 2 ∷ᵥ 3 ∷ᵥ []ᵥ) (4 ∷ᵥ 5 ∷ᵥ 6 ∷ᵥ []ᵥ) ≡ _
  -- _ = refl




## Universe levels

<pre><span class="agda2-highlight-keyword">module</span> <span class="agda2-highlight-module">UniverseLevels</span> <span class="agda2-highlight-keyword">where</span>
</pre>
There are a bunch of definitional equalities associated with universe levels. Without them universe polymorphism would be nearly unusable. Here are the equalities:

<pre><span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">&#8704;</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">&#945;</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-primitive">lzero</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-primitive">&#8852;</span></span> <span class="agda2-highlight-bound-variable">&#945;</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-datatype">&#8801;</span></span> <span class="agda2-highlight-bound-variable">&#945;</span>
<span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-inductive-constructor">refl</span>

<span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">&#8704;</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">&#945;</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">&#945;</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-primitive">&#8852;</span></span> <span class="agda2-highlight-bound-variable">&#945;</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-datatype">&#8801;</span></span> <span class="agda2-highlight-bound-variable">&#945;</span>
<span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-inductive-constructor">refl</span>

<span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">&#8704;</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">&#945;</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-primitive">lsuc</span> <span class="agda2-highlight-bound-variable">&#945;</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-primitive">&#8852;</span></span> <span class="agda2-highlight-bound-variable">&#945;</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-datatype">&#8801;</span></span> <span class="agda2-highlight-primitive">lsuc</span> <span class="agda2-highlight-bound-variable">&#945;</span>
<span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-inductive-constructor">refl</span>

<span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">&#8704;</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">&#945;</span> <span class="agda2-highlight-bound-variable">&#946;</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-bound-variable">&#945;</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-primitive">&#8852;</span></span> <span class="agda2-highlight-bound-variable">&#946;</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-datatype">&#8801;</span></span> <span class="agda2-highlight-bound-variable">&#946;</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-primitive">&#8852;</span></span> <span class="agda2-highlight-bound-variable">&#945;</span>
<span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-inductive-constructor">refl</span>

<span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">&#8704;</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">&#945;</span> <span class="agda2-highlight-bound-variable">&#946;</span> <span class="agda2-highlight-bound-variable">&#947;</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">&#945;</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-primitive">&#8852;</span></span> <span class="agda2-highlight-bound-variable">&#946;</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-primitive">&#8852;</span></span> <span class="agda2-highlight-bound-variable">&#947;</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-datatype">&#8801;</span></span> <span class="agda2-highlight-bound-variable">&#945;</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-primitive">&#8852;</span></span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">&#946;</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-primitive">&#8852;</span></span> <span class="agda2-highlight-bound-variable">&#947;</span><span class="agda2-highlight-symbol">)</span>
<span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-inductive-constructor">refl</span>

<span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">&#8704;</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">&#945;</span> <span class="agda2-highlight-bound-variable">&#946;</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-primitive">lsuc</span> <span class="agda2-highlight-bound-variable">&#945;</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-primitive">&#8852;</span></span> <span class="agda2-highlight-primitive">lsuc</span> <span class="agda2-highlight-bound-variable">&#946;</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-datatype">&#8801;</span></span> <span class="agda2-highlight-primitive">lsuc</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">&#945;</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-primitive">&#8852;</span></span> <span class="agda2-highlight-bound-variable">&#946;</span><span class="agda2-highlight-symbol">)</span>
<span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-inductive-constructor">refl</span>
</pre>
A demonstration of how Agda can greatly simplify level expressions using the above identites:

<pre><span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-symbol">&#8704;</span> <span class="agda2-highlight-symbol">{</span><span class="agda2-highlight-bound-variable">&#945;</span> <span class="agda2-highlight-bound-variable">&#946;</span> <span class="agda2-highlight-bound-variable">&#947;</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-primitive">lsuc</span> <span class="agda2-highlight-bound-variable">&#945;</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-primitive">&#8852;</span></span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">&#947;</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-primitive">&#8852;</span></span> <span class="agda2-highlight-primitive">lsuc</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-primitive">lsuc</span> <span class="agda2-highlight-bound-variable">&#946;</span><span class="agda2-highlight-symbol">))</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-primitive">&#8852;</span></span> <span class="agda2-highlight-primitive">lzero</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-primitive">&#8852;</span></span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">&#946;</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-primitive">&#8852;</span></span> <span class="agda2-highlight-bound-variable">&#947;</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-datatype">&#8801;</span></span> <span class="agda2-highlight-primitive">lsuc</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">&#945;</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-primitive">&#8852;</span></span> <span class="agda2-highlight-primitive">lsuc</span> <span class="agda2-highlight-bound-variable">&#946;</span><span class="agda2-highlight-symbol">)</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-primitive">&#8852;</span></span> <span class="agda2-highlight-bound-variable">&#947;</span>
<span class="agda2-highlight-symbol">_</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-inductive-constructor">refl</span>
</pre>
These special rules also give us an ability to define a less-than-or-equal-to relation on levels:

<pre><span class="agda2-highlight-operator"><span class="agda2-highlight-function">_&#8804;&#8467;_</span></span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-postulate">Level</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-postulate">Level</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-primitive-type">Set</span>
<span class="agda2-highlight-bound-variable">&#945;</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">&#8804;&#8467;</span></span> <span class="agda2-highlight-bound-variable">&#946;</span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-bound-variable">&#945;</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-primitive">&#8852;</span></span> <span class="agda2-highlight-bound-variable">&#946;</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-datatype">&#8801;</span></span> <span class="agda2-highlight-bound-variable">&#946;</span>
</pre>
which in turn allows to [emulate cumulativity of universes](http://effectfully.blogspot.com/2016/07/cumu.html) in Agda (although there is an experimental option [`--cumulativity`](https://agda.readthedocs.io/en/latest/language/cumulativity.html) that makes the universe hierarchy cumulative).

The list of equalities shown above is not exhaustive. E.g. if during type checking Agda comes up with the following constraint:

    α <= β <= α

it gets solved as `α ≡ β`.











{-

## Inconvenient recursion

Vector.foldl

## A function is not dependent enough

-- ᵏ′ : ∀ {α β} {A : Set α} {B : A -> Set β} -> (∀ {x} -> B x) -> ∀ x -> B x
-- ᵏ′ y x = y

mention the Kipling paper

## mention the Jigger

## Talk about heterogeneous equality?

## η-laws

## auto

-- If (n ∸ m) is in canonical form,
-- then (n ≤ℕ m) reduces either to (⊤) or to (⊥).
-- The value of (⊤) can be inferred automatically,
-- which is exploited by the (ᵀ≤ᵀ) constructor of the (_≤_) datatype.
-- It would be nice to have a type error, when (n ≤ℕ m) reduces to (⊥).
_≤ℕ_ : ℕ -> ℕ -> Set
0     ≤ℕ _     = ⊤
suc _ ≤ℕ 0     = ⊥
suc n ≤ℕ suc m = n ≤ℕ m


record Is {α} {A : Set α} (x : A) : Set α where
  ¡ = x
open Is

! : ∀ {α} {A : Set α} -> (x : A) -> Is x
! _ = _

_-⁺_ : ∀ {m} -> ℕ -> Is (suc m) -> ℕ
n -⁺ im = n ∸ ¡ im

## Inferring functions

mention _% = _∘_?

mention Jesper's work and the green slime problem?

lazily match on index of a singleton, then match on the singleton where it's needed


  1OrDouble : Bool -> ℕ -> ℕ
  1OrDouble false n = suc zero
  1OrDouble true  n = 0 + 0

  _ : 1OrDouble _ 0 ≡ 1
  _ = refl
</pre>
  </body>
</html>
