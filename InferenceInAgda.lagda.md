# Inference in Agda

```agda
module InferenceInAgda where
```

This is a tutorial on how Agda infers things.

As [pointed out](https://www.reddit.com/r/agda/comments/jo4hh8/inference_in_agda) by @gallais, some links are messed up. If the address of this page starts with "https://htmlpreview.github.io" (`htmlpreview` turned out to have a [critical bug](https://github.com/htmlpreview/htmlpreview.github.com/issues/43)), please [visit this page](https://raw.githack.com/effectfully/inference-in-agda/master/InferenceInAgda.html) and read the tutorial there if you want to have the correct links. Sorry for the inconvenience.

For sources, issue reports or contributing go to [the GitHub page](https://github.com/effectfully/inference-in-agda).

## Preface

Agda is a wonderful language and its unification engines are exemplary, practical, improve over time and work predictably well. Unification engines are one notable distiction between Agda and other dependently typed languages (such as Idris 1, Coq, Lean, etc). I'm saying "unification engines", because there are two of them:

- unification used for getting convenient and powerful pattern matching
- unification used for inferring values of implicit arguments

These are two completely distinct machineries. This tutorial covers only the latter for the moment being as it's what gives Agda its inference capabilities. I'll probably say a few words about the former once I forget how hard it is to write long technical texts.

This tutorial primarily targets

- users of Agda who want to understand how to write code to make more things inferrable
- a general audience curious about dependent types and what can be done with them
- people implementing powerful dependently typed languages and looking for features to support (most of what is described here are tricks that I use in may day-to-day work (when it involves Agda) and I'd definitely want to see them available in languages that are yet to come)

Higher-order unification is not covered. It's a highly advanced topic and from the user's perspective diving into higher-order unification has a rather big cost/benefit ratio: I don't remember tweaking my code to fit it into the pattern fragment or doing anything else of this kind to help Agda unify things in the higher-order case. Agda would barely be usable without the built-in higher-order unification, but it's mostly invisible to the user and just works.

Analogously, no attempt to dissect Agda's internals is performed. Agda is well-designed enough not to force the user to worry about the peculiarities of the implementation (like when something gets postponed or in what order equations get solved). If you do want to learn about the internals, I recommend reading [Type checking in the presence of meta-variables](https://www.researchgate.net/publication/228571999_Type_checking_in_the_presence_of_meta-variables) and [Higher-Order Dynamic Pattern Unification for Dependent Types and Records](http://www.cse.chalmers.se/~abela/unif-sigma-long.pdf).

And if you want to learn about internals of unification powering the pattern matching engine, then it's all elaborated in detail by Jesper Cockx in his [PhD thesis](https://jesper.sikanda.be/files/thesis-final-digital.pdf). Section "3.6 Related work" of it shortly describes differences between the requirements for the two kinds of unification.

## Intro

Agda only infers values that are uniquely determined by the current context. I.e. Agda doesn't try to guess: it either fails to infer a value or infers the definitive one. Even though this makes the unification algorithm weaker than it could be, it also makes it reliable and predictable. Whenever Agda infers something, you can be sure that this is the thing that you wanted and not just a random guess that would be different if you provided more information to the type checker (but Agda does have a guessing machinery called [Agsy](https://agda.readthedocs.io/en/v2.6.0.1/tools/auto.html) that can be used interactively, so that no guessing needs to be done by the type checker and everything inferred is visible to the user).

We'll look into basics of type inference in Agda and then move to more advanced patterns. But first, some imports:

## Imports

```agda
open import Level renaming (suc to lsuc; zero to lzero)
open import Function using (_$_; _$′_; _∘_; _∘′_; _∋_; case_of_) renaming (_|>_ to _&_; _|>′_ to _&′_)
open import Relation.Binary.PropositionalEquality
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Bool.Base using (Bool; true; false; not) renaming (_∨_ to _||_; _∧_ to _&&_)
open import Data.Nat.Base  using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Data.Product using (_×_; Σ; _,_; _,′_)
```

## Basics of type inference

```agda
module BasicsOfTypeInference where
```

Some preliminaries: the type of lists is defined as (ignoring universe polymorphism)

```agda
  infixr 5 _∷_

  data List (A : Set) : Set where
    []  : List A
    _∷_ : A -> List A -> List A
```

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

```agda
  _ = λ {A} -> [] {A}
```

(`_ = <...>` is an anonymous definition: we ask Agda to type check something, but don't bother giving it a name, because we're not going to use it later)

This definition is accepted, which means that Agda has inferred its type successfully.

Note that

      _ {A} = [] {A}

means the same thing as the previous expression, but doesn't type check. It's just a syntactic limitation: certain things are allowed in patterns but not in lambdas and vice versa.

Agda can infer monomorphic types directly without any hints:

```agda
  _ = true ∷ []
```

Type inference works not only with lambdas binding implicit arguments, but also explicit ones. And types of latter arguments can depend on earlier arguments. E.g.

```agda
  id₁ = λ {A : Set} (x : A) -> x
```

is the regular `id` function spelled as

      id :: forall a. a -> a
      id x = x

in Haskell.

Partially or fully applied `id₁` doesn't need a type signature either:

```agda
  _ = id₁
  _ = id₁ {Bool}
  _ = id₁ true
```

You can even interleave implicit and explicit arguments and partial applications (and so full ones as well) will still be inferrable:

```agda
  const = λ {A : Set} (x : A) {B : Set} (y : B) -> x
  _ = const {Bool}
  _ = const true
```

Finally, you don't need to specify a type signature for an alias, even if that alias has a different fixity than what it's defined in terms of. My favourite example is this:

```agda
  _∘ = _∘_
```

It's an operator that allows us to compose a function with an n-ary function. In Haskell we have libraries like [composition](https://hackage.haskell.org/package/composition) that define a bunch of n-ary composition operators like

      (.*) :: (c -> d) -> (a -> b -> c) -> a -> b -> d
      (.**) :: (d -> e) -> (a -> b -> c -> d) -> a -> b -> c -> e
      etc

but in Agda we can get away with a single additional postfix operator and construct all of the above on the fly. For example:

```agda
  -- Composing `suc` with 2-ary `_+_`
  _ = suc ∘ ∘ _+_

  -- Composing `suc` with a random 3-ary function.
  _ = suc ∘ ∘ ∘ f where
    f = λ (x y z : ℕ) -> 0
```

Note that `_∘` and `_∘_` are two different operators (in particular, the former is postfix and the latter is infix) that happen to be called the same. We could have called `_∘` differently of course, but since Agda is able to distinguish between the two based on how they're used (there's no `∘_` and so Agda knows that the only way to parse `suc ∘ ∘ ∘ f` is `((suc ∘) ∘) ∘ f`, which is exactly what one'd write in Haskell), it's just nice to make the two operators share the name.

## `let`, `where`, `mutual`

```agda
module LetWhereMutual where
```

In Agda bindings that are not marked with `abstract` are transparent, i.e. writing, say, `let v = e in b` is the same thing as directly substituting `e` for `v` in `b` (`[e/v]b`). For example all of these type check:

```agda
  _ : Bool
  _ = let 𝔹 = Bool
          t : 𝔹
          t = true
      in t

  _ : Bool
  _ = t where
    𝔹 = Bool
    t : 𝔹
    t = true

  𝔹 = Bool
  t : 𝔹
  t = true
  _ : Bool
  _ = t
```

Unlike Haskell Agda does not have [let-generalization](https://www.haskell.org/ghc/blog/20100930-LetGeneralisationInGhc7.html), i.e. this valid Haskell code:

      p :: (Bool, Integer)
      p = let i x = x in (i True, i 1)

has to be written either with an explicit type signature for `i`:

```agda
  _ : Bool × ℕ
  _ = let i : {A : Set} -> A -> A
          i x = x
      in (i true , i 1)
```

or in an equivalent way like

```agda
  _ : Bool × ℕ
  _ = let i = λ {A} (x : A) -> x
      in (i true , i 1)
```

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

```agda
  _ = let i = λ x -> x in i true

  _ = i true where i = λ x -> x

  mutual
    i = λ x -> x
    _ = i true
```

In general, definitions in a `let`/`where`/`mutual` block share the same context, which makes it possible to infer more things than with consecutive standalone definitions. It's occasionally useful to create a bogus `mutual` block when you want the type of a definition to be inferred based on its use.

## Unification intro

```agda
module UnificationIntro where
```

The following definitions type check:

```agda
  _ = (λ x -> x) 1
  _ = (λ x -> 2) 1
```

reassuring that Agda's type checker is not based on some simple bidirectional typing rules (if you're not familier with those, see [Bidirectional Typing Rules: A Tutorial](http://www.davidchristiansen.dk/tutorials/bidirectional.pdf)), but the type checker does have a bidirectional interface ([`inferExpr`](https://hackage.haskell.org/package/Agda-2.6.1/docs/Agda-TheTypeChecker.html#v:inferExpr) & [`checkExpr`](https://hackage.haskell.org/package/Agda-2.6.1/docs/Agda-TheTypeChecker.html#v:checkExpr)) where type inference is defined in terms of type checking for the most part:

      -- | Infer the type of an expression. Implemented by checking against a meta variable. <...>
      inferExpr :: A.Expr -> TCM (Term, Type)

which means that any definition of the following form:

      name = term

can be equally written as

      name : _
      name = term

since Agda elaborates `_` to a fresh metavariable and then type checks `term` against it, which amounts to unifying the inferred type of `term` with the meta. If the inferred type doesn't contain metas itself, then the meta standing for `_` is resolved as that type and the definition is accepted (if the inferred type does contain metas, things get more difficult and we're not going to describe all the gory details here). So type inference is just a particular form of unification.

You can put `_` basically anywhere and let Agda infer what term/type it stands for. For example:

```agda
  id₂ : {A : Set} -> A -> _
  id₂ x = x
```

Here Agda binds the `x` variable and records that it has type `A` and when the `x` variable is returned as a result, Agda unifies the expected type `_` with the actual type of `x`, which is `A`. Thus the definition above elaborates to

```agda
  id₂′ : {A : Set} -> A -> A
  id₂′ x = x
```

This definition:

```agda
  id₃ : {A : Set} -> _ -> A
  id₃ x = x
```

elaborates to the same result in a similar fashion, except now Agda first records that the type of `x` is a meta and when `x` is returned as a result, Agda unifies that meta with the expected type, i.e. `A`, and so the meta gets resolved as `A`.

An `id` function that receives an explicit type:

```agda
  id₄ : (A : Set) -> _ -> A
  id₄ A x = x
```

can be called as

```agda
  _ = id₄ _ true
```

and the `_` will be inferred as `Bool`.

It's also possible to explicitly specify an implicit type by `_`, which is essentially a no-op:

```agda
  id₅ : {A : Set} -> A -> A
  id₅ x = x

  _ = id₅ {_} true
```

## Inference and pattern matching

```agda
module InferenceAndPatternMatching where
```

Unrestricted pattern matching breaks type inference. Take for instance

```agda
  _ = λ where
          zero    -> true
          (suc _) -> false
```

which is a direct counterpart of Haskell's

      isZero = \case
          0 -> True
          _ -> False

The latter is accepted by Haskell, but the former is not accepted by Agda: Agda colors the entire snippet in yellow meaning it's unable to resolve the generated metavariables. "What's the problem? The inferred type should be just `ℕ -> Bool`" -- you might think. Such a type works indeed:

```agda
  _ : ℕ -> Bool
  _ = λ where
          zero    -> true
          (suc _) -> false
```

But here's another thing that works:

```agda
  _ : (n : ℕ) -> n & λ where
                         zero -> Bool
                         _    -> Bool
  _ = λ where
          zero    -> true
          (suc _) -> false
```

Recall that we're in a dependently typed language and here the type of the result of a function can depend on the argument of that function. And both the

      ℕ -> Bool

      (n : ℕ) -> n & λ where
                         zero -> Bool
                         _    -> Bool

types are correct for that function. Even though they are "morally" the same, they are not definitionally equal and there's a huge difference between them: the former one doesn't have a dependency and the latter one has.

There is a way to tell Agda that pattern matching is non-dependent: use `case_of_`, e.g.

```agda
  _ = λ (n : ℕ) -> case n of λ where
          zero    -> true
          (suc _) -> false
```

type checks. `case_of_` is just a definition in the standard library that at the term level is essentially

      case x of f = f x

and at the type level it restricts the type of `f` to be a non-dependent function.

Analogously, this is yellow:

```agda
  _ = λ (n : ℕ) -> n & λ where
          zero    -> true
          (suc _) -> false
```

due to `_&_` being dependent:

      _&_ : {A : Set} {B : A -> Set} -> ∀ x -> (∀ x -> B x) -> B x
      x & f = f x

While this is fine:

```agda
  _ = λ (n : ℕ) -> n &′ λ where
          zero    -> true
          (suc _) -> false
```

due to `_&′_` being non-dependent:

      _&′_ : {A B : Set} -> A -> (A -> B) -> B
      x &′ f = f x

Agda's stdlib provides several intentionally non-dependent functions (e.g. `_∘′_`, `_$′_` and `case_of_` that we've already seen) to enable the user to get improved inference in the non-dependent case.

Note that annotating `n` with its type, `ℕ`, is mandatory in all the cases above. Agda is not able to conclude that if a value is matched against a pattern, then the value must have the same type as the pattern.

Even this doesn't type check:

```agda
  _ = λ n -> case n of λ where
          zero    -> zero
          (suc n) -> n
```

even though Agda really could figure out that if `zero` is returned from one of the branches, then the type of the result is `ℕ`, and since `n` is returned from the other branch and pattern matching is non-dependent, `n` must have the same type. See [#2834](https://github.com/agda/agda/issues/2834) for why Agda doesn't attempt to be clever here.

There's a funny syntactical way to tell Agda that a function is non-dependent: just do not bind a variable at the type level. This type checks:

```agda
  _ : ℕ -> _
  _ = λ where
          zero    -> true
          (suc _) -> false
```

while this doesn't:

```agda
  _ : (n : ℕ) -> _
  _ = λ where
          zero    -> true
          (suc _) -> false
```

In the latter case Agda treats `_` as being potentially dependent on `n`, since `n` is explicitly bound. And in the former case there can't be any dependency on a non-existing variable.

## Inference and constructors

```agda
module InferenceAndConstructors where
```

Since tuples are dependent, this

```agda
  _ = (1 , 2)
```

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

```agda
  _ = (1 ,′ 2)
```

(`_,′_` is a non-dependent version of `_,_`)

to tell Agda not to worry about potential dependencies.

## Implicit arguments

```agda
module ImplicitArgumens where
```

As we've seen implicit arguments and metavariables are closely related. Agda's internal theory has metas in it, so inference of implicit arguments amounts to turning an implicit into a metavariable and resolving it later. The complicated part however is that it's not completely obvious where implicits get inserted.

For example, it may come as a surprise, but

      _ : ∀ {A : Set} -> A -> A
      _ = λ {A : Set} x -> x

gives a type error. This is because Agda greedily binds implicits, so the `A` at the term level gets automatically bound on the lhs (left-hand side, i.e. before `=`), which gives you essentially this:

      _ : ∀ {A : Set} -> A -> A
      _ {_} = <your_code_goes_here>

where `{_}` stands for `{A}`. So you can't bind `A` by a lambda, because it's already silently bound for you. Although it's impossible to reference that type variable unless you explicitly name it as in

```agda
  id : {A : Set} -> A -> A
  id {A} = λ (x : A) -> x
```

Not only does Agda eagerly binds implicits, but it also inserts them eagerly at the call site. E.g.

```agda
  id-id : {A : Set} -> A -> A
  id-id = id id
```

elaborates to

```agda
  id-id₁ : {A : Set} -> A -> A
  id-id₁ {A} = id {A -> A} (id {A})
```

I.e. the inner `id` gets implicitly instantiated and only then fed to the outer `id`. Hence the outer `id` is instantiated at `A -> A`, which is the type of the inner instantiated `id`.

An alternative could be

      id-id₂ : {A : Set} -> A -> A
      id-id₂ {A} = id { {A : Set} -> A -> A } id {A}

Here the inner `id` doesn't get instantiated and gets fed to the outer `id` as is. Hence the outer `id` is instantiated at `{A : Set} -> A -> A`, which is the type of the inner uninstantiated `id`.

(Except that definition does not type check, because `{A : Set} -> A -> A` is of type `Set₁` rather than `Set` and we don't bother fixing this with proper universe polymorphism as those details are irrelevant for explaining how implicits get inserted)

Eager insertion of implicits is the reason why Agda infers the type of `[]` as `List _A_42`: `[]` gets elaborated to `[] {_}`, because the explicit argument `A` of `List` is implicit for the constructors of `List` (i.e. `[]` and `_∷_`) and that implicit gets eagerly inserted.

One exception to the general rule that implicits get bound and inserted eagerly is aliases: a definition of the form `<name1> = <name2>` doesn't need a type signature (as we saw before with the `_∘ = _∘_` example) and gets accepted as is regardless of whether `<name2>` has any leading implicit arguments or not. Basically, `<name1>` inherits its type signature from `<name2>` without any further elaboration.

There is a notorious bug related to insertion of implicit lambdas that has been in Agda for ages (even since its creation probably?) called The Hidden Lambda Bug. I'm not going to describe the bug here as details change across different version of Agda, but here are some links:

- tracked in [this issue](https://github.com/agda/agda/issues/1079)
- discussed in detail in [this issue](https://github.com/agda/agda/issues/2099)
- there's even an entire [MSc thesis](http://www2.tcs.ifi.lmu.de/~abel/MScThesisJohanssonLloyd.pdf) about it
- and a [plausible solution](https://github.com/AndrasKovacs/implicit-fun-elaboration/blob/master/paper.pdf)

So while Agda's elaborations works well, it has its edge cases. In practice, it's not a big deal to insert an implicit lambda to circumvent the bug, but it's not always clear that Agda throws a type error because of this bug and not due to something else (e.g. I was completely lost in [this case](https://github.com/agda/agda/issues/1095)). So beware.

## An underspecified argument example

```agda
module UnderspecifiedArgument where
```

Another difference between Haskell and Agda is that Agda is not happy about ambiguous types that don't really affect anything. Consider a classic example: the `I` combinator can be defined in terms of the `S` and `K` combinators. In Haskell we can express that as

      k :: a -> b -> a
      k x y = x

      s :: (a -> b -> c) -> (a -> b) -> a -> c
      s f g x = f x (g x)

      i :: a -> a
      i = s k k

and [it'll type check](https://ideone.com/mZQM1f). However the Agda's equivalent

```agda
  K : {A B : Set} -> A -> B -> A
  K x y = x

  S : {A B C : Set} -> (A -> B -> C) -> (A -> B) -> A -> C
  S f g x = f x (g x)

  I : ∀ {A} -> A -> A
  I = S K K
```

results in the last `K` being highlighted in yellow (which means that not all metavariables were resolved). To see why, let's inline `S` and see if the problem persists:

```agda
  _ : ∀ {A} -> A -> A
  _ = λ x -> K x (K x)
```

It does. So the problem is that in the expression above the final `K x` argument is underspecified: a `K` must receive a particular `B`, but we neither explicitly specify a `B`, nor it can be inferred from the context as the entire `K x` argument is thrown away by the outer `K`.

To fix this we can explicitly specify a `B` (any of type `Set` will work, let's pick `ℕ`):

```agda
  _ : ∀ {A} -> A -> A
  _ = S K (K {B = ℕ})
```

In general, Agda expects all implicits (and metavariables in general) to be resolved and won't gloss over such details the way Haskell does. Agda is a proof assistant and under the [Curry-Howard correspondence](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence) each argument to a function represents a certain logical assumption and every such assumption must be fulfilled at the call site either explicitly or in an automated manner.

## Not dependent enough

```agda
module NotDependentEnough where
```

Speaking of `K`, what do you think its most general type is, in Agda? Recall that we were using this definition in the previous section:

```agda
  K₀ : {A : Set} {B : Set} -> A -> B -> A
  K₀ x y = x
```

Looking at that type signature, we can think of making the type of the second argument dependent on the first argument:

```agda
  K₁ : {A : Set} {B : A -> Set} -> ∀ x -> B x -> A
```

This version looks more general, but it's in fact not, as `K₁` can be expressed in terms of `K₀`:

```agda
  K₁ x = K₀ x
```

Basically, if you have an `x` to pass to `K₀`, then you can use that same `x` to apply a `B : A -> Set` to it to get `B x` of type `Set` and since the non-dependent `K` does not restrict the type of its second argument in any way, `B x` is good enough, and the fact that it mentions the particular `x` being passed as a first term-level argument, is just irrelevant. If we fully spell it out:

```agda
  K₁′ : {A : Set} {B : A -> Set} -> ∀ x -> B x -> A
  K₁′ {A} {B} x y = K₀ {A} {B x} x y
```

Note that we had to eta-expand the definition of `K₁`. If we don't do that, we'll get an error:

      -- Cannot instantiate the metavariable _360 to solution B x
      -- since it contains the variable x
      -- which is not in scope of the metavariable
      K₁ : {A : Set} {B : A -> Set} -> ∀ x -> B x -> A
      K₁ = K₀

This is because this definition of `K₁` elaborates to `K₁ {_} {_} = K₀ {_} {_}` due to eager insertion of implicits and the last `_` can't be resolved, because as we can see in `K₁′` it has to be `B x`, but `x` is not bound on the lhs and so Agda complains about it.

`K₀` in turn can be expressed in terms of `K₁`:

```agda
  K₀-via-K₁ : {A B : Set} -> A -> B -> A
  K₀-via-K₁ = K₁
```

Basically, `K₁` expects a `A -> Set` and we can create one from `B : Set` via `λ _ -> B`.

So `K₀` and `K₁` are equally powerful. And note how in both the `K₀`-via-`K₁` and `K₁`-via-`K₀` cases Agda successfully infers implicits.

So is `K₀`/`K₁` the best we can do? Nope, here's a twist: we can make the type of the result depend on the second argument (the one that gets dropped), which in turn requires to reflect the dependency in the type of the first argument (the one that gets returned), so we end up with

```agda
  -- ᵈ for "dependent".
  Kᵈ : {A : Set} {B : A -> Set} -> (∀ {x} -> B x) -> ∀ x -> B x
  Kᵈ y x = y
```

Compare this to regular function application:

```agda
  apply : {A : Set} {B : A -> Set} -> (∀ x -> B x) -> ∀ x -> B x
  apply f x = f x
```

I.e. `Kᵈ` is implicit function application.

"You're making it up! `Kᵈ` elaborates to `λ y x -> y {x}`, how is that a `K` combinator?"

Here is how: first of all, `K₀` can be directly defined via `Kᵈ`:

```agda
  K₀-via-Kᵈ : {A B : Set} -> A -> B -> A
  K₀-via-Kᵈ x = Kᵈ x
```

But most importantly `Kᵈ` expresses the "drop the second argument, return the first one" idea better than than the non-dependent `K` as the former can be used where the latter fails. For example, in the [Outrageous but Meaningful Coincidences](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.379.3169&rep=rep1&type=pdf) paper the author stumbles upon a few expressions involving `K` that look like they should type check, but they don't, despite the fact that a bunch of very similar expressions also involving `K` type check perfectly well. So the author inlines the definition of `K` and writes in a footnote:

> It’s frankly astonishing how effective Agda’s implicit syntax mechanism turns out to be. The trouble is that the system’s limits are far from clear. It is hard to tell what shouldn’t work, and what is rather a lacuna.

However in this case the problem is not with Agda not being able to infer something, but rather the type of `K` being too restrictive. If we use the dependent version of `K` instead, then [everything type checks](https://github.com/effectfully/random-stuff/blob/07253f395c63813abb64a08045e22ae8412e5be6/Kipling.agda#L110-L114).

Note that we had to eta-expand `K₀-via-Kᵈ`, but this time for a different reason. If we make it

      K₀-via-Kᵈ′ : {A B : Set} -> A -> B -> A
      K₀-via-Kᵈ′ {A} {B} = {!Kᵈ {B} {λ _ -> A}!}

and ask for the type of the expression in the hole, we'll see

      Goal: A -> B -> A
      Have: ({B} -> A) -> B -> A

and `A` and `{B} -> A` are two distinct types that fail to unify. While an expression of type `A` can be used wherever a `{B} -> A` is expected as Agda will realize that an implicit variable of type `B` can be simply ignored, and so this is why eta-expaning the definition solves the problem.

Is `Kᵈ` the best we can do? Well, Agda has explicit universe polymorphism, so we can and should make the definition universe-polymorphic:

```agda
  Kᵈ′ : ∀ {α β} {A : Set α} {B : A -> Set β} -> (∀ {x} -> B x) -> ∀ x -> B x
  Kᵈ′ y x = y
```

Which gives us a reasonably general definition that works in most practical cases, but here's an example of where it fails:

      -- Set (lsuc (lsuc α)) != Set _β_382
      -- when checking that the expression Set α has type Set (lsuc α)
      _ = Kᵈ′ (λ {α} -> Set α)

This is because the type of `Set α` is `Set (lsuc α)` where `α` is an (implicit) argument, i.e. the universe where `B` lies depends on the received value and `Kᵈ′` does not support this due to `β` not depending on an `A` in the type of `B`: `A -> Set β`.

We can support this use case by turning `β` into a function from `A`:

```agda
  Kᵈ′′ : ∀ {α} {A : Set α} {β : A -> Level} {B : ∀ x -> Set (β x)} -> (∀ {x} -> B x) -> ∀ x -> B x
  Kᵈ′′ y x = y
```

Now the example type checks:

```agda
  _ = Kᵈ′′ (λ {α} -> Set α)
```

But that is rarely needed in practice and not making `β` a function is good enough most of the time.

In general, an attempt to apply a higher-order function expecting a non-dependent function as its argument to a dependent function results in an error talking about a variable not being in scope of a metavariable. As a quick example, having a random dependently typed function:

```agda
  BoolOrℕ : Bool -> Set
  BoolOrℕ true  = Bool
  BoolOrℕ false = ℕ

  falseOrZero : (b : Bool) -> BoolOrℕ b
  falseOrZero true  = false
  falseOrZero false = 0
```

we can trigger the error by trying to feed `falseOrZero` to `_$′_` (which expects a non-dependent function):

      -- Cannot instantiate the metavariable _401 to solution BoolOrℕ b
      -- since it contains the variable b
      -- which is not in scope of the metavariable
      _ = falseOrZero $′ true

The exact error message depends on the version of Agda used, though.

But note that

1. this error can be triggered in different cases as well, as we saw with `K₁ = K₀`
2. applying a higher-order function to an unexpectedly dependent function can give a different error, as we saw with `Kᵈ′′ (λ {α} -> Set α)`

Anyway, in my experience being able to make sense of that particular error is really helpful.

## Inferring implicits

```agda
module InferringImplicits where
```

As we've seen previously the following code type checks fine:

```agda
  id : {A : Set} -> A -> A
  id x = x

  _ = id true
```

Here `A` is bound implicitly in `id`, but Agda is able to infer that in this case `A` should be instantiated to `Bool` and so Agda elaborates the expression to `id {Bool} true`.

This is something that Haskell would infer as well. The programmer would hate to explicitly write out the type of every single argument, so programming languages often allow the user not to specify types when they can be inferred from the context. Agda is quite unique here however, because it can infer a lot more than other languages (even similar dependently typed ones) due to bespoke machineries handling various common patterns. But let's start with the basics.

## Arguments of data types

```agda
module ArgumentsOfDataTypes where
  open BasicsOfTypeInference
```

Agda can infer parameters/indices of a data type from a value of that data type. For example if you have a function

```agda
  listId : ∀ {A} -> List A -> List A
  listId xs = xs
```

then the implicit `A` can be inferred from a list:

```agda
  _ = listId (1 ∷ 2 ∷ [])
```

Unless, of course, `A` can't be determined from the list alone. E.g. if we pass an empty list to `f`, Agda will mark `listId` with yellow and display an unresolved metavariable `_A`:

```agda
  _ = listId []
```

Another example of this situation is when the list is not empty, but the type of its elements can't be inferred, e.g.

```agda
  _ = listId ((λ x -> x) ∷ [])
```

Here the type of `x` can be essentially anything (`ℕ`, `List Bool`, `⊤ × Bool -> ℕ`, etc), so Agda asks to provide missing details. Which we can do either by supplying a value for the implicit argument explicitly

```agda
  _ = listId {ℕ -> ℕ} ((λ x -> x) ∷ [])
```

or by annotating `x` with a type

```agda
  _ = listId ((λ (x : ℕ) -> x) ∷ [])
```

or just by providing a type signature

```agda
  _ : List (ℕ -> ℕ)
  _ = listId ((λ x -> x) ∷ [])
```

All these definitions are equivalent.

So "`A` is inferrable from a `List A`" doesn't mean that you can pass any list in and magically synthesize the type of its elements -- only that if that type is already known at the call site, then you don't need to explicitly specify it to apply `listId` to the list as it'll be inferred for you. "Already known at the call site" doesn't mean that the type of elements needs to be inferrable -- sometimes it can be derived from the context, for example:

```agda
  _ = suc ∷ listId ((λ x -> x) ∷ [])
```

The implicit `A` gets inferred here: since all elements of a list have the same type, the type of `λ x -> x` must be the same as the type of `suc`, which is known to be `ℕ -> ℕ`, hence the type of `λ x -> x` is also `ℕ -> ℕ`.

### Comparison to Haskell

In Haskell it's also the case that `a` is inferrable form a `[a]`: when the programmer writes

    `  sort :: Ord a => [a] -> [a]

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

Agda's unification capabilities are well above Haskell's ones, so Agda doesn't attempt to predict what can and can't be inferred and allows us to make anything implicit, deferring resolution problems to the call site (i.e. it's like having `AllowAmbiguousTypes` globally enabled in Haskell). In fact, you can make implicit even such things that are pretty much guaranteed to never have any chance of being inferred, for example

```agda
  const-zeroᵢ : {ℕ} -> ℕ  -- `{ℕ}` is a shorthand for `{_ : ℕ}`
  const-zeroᵢ = zero
```

as even

```agda
  const-zeroᵢ′ : {ℕ} -> ℕ
  const-zeroᵢ′ = const-zeroᵢ
```

results in unresolved metas, because it elaborates to

```agda
  const-zeroᵢ′-elaborated : {ℕ} -> ℕ
  const-zeroᵢ′-elaborated {_} = const-zeroᵢ {_}
```

(due to eager insertion of implicits) and the fact that there's a variable of type `ℕ` bound in the current scope (regardless of whether it's bound explicitly or implicitly) does not have any effect on how implicits get resolved in the body of the definition. Metavariable resolution does not come up with instantiations for metavariables at random by looking at the local or global scope, it only determines what instantiations are bound to be by solving unification problems that arise during type checking.

But note that even though a value of type `{ℕ} -> ℕ` is not very useful on its own, having such a value as an argument like this:

```agda
  at1 : ({ℕ} -> ℕ) -> ℕ
  at1 f = f {1}
```

can be useful occasionally, because it gives you an API where the caller can decide if they want to bind the additional implicit variable or not. Here's an example for each of the cases:

```agda
  _ = at1 2
  _ = at1 λ {n} -> n
```

Thus, [covariantly positioned](https://en.wikipedia.org/wiki/Covariance_and_contravariance_(computer_science)#Function_types) implicits that are not determined by explicit arguments can be handy for providing defaults or additional data that the caller is usually not interested in, but occasionally is, and so the data is hidden in an implicit.

By the way, if you do need to resolve things based on the current scope, then Agda has [instance arguments](https://agda.readthedocs.io/en/latest/language/instance-arguments.html) for that (they are similar to Haskell's type classes, but do not obey [global uniqueness of instances](http://blog.ezyang.com/2014/07/type-classes-confluence-coherence-global-uniqueness), because [it's hard](https://github.com/AndrasKovacs/pny1-assignment/blob/292e0fc28d7c27b35240d4f9d014bdf4db3afc62/DepTC.md#4-coherent-classes-in-dependent-languages)), for example

```agda
  const-zeroᵢᵢ : {{ℕ}} -> ℕ
  const-zeroᵢᵢ = zero

  const-zeroᵢᵢ′ : {{ℕ}} -> ℕ
  -- Explicitly inserting `{{_}}` just to show that there's no interference with how instance
  -- arguments get inserted.
  const-zeroᵢᵢ′ {{_}} = const-zeroᵢᵢ
```

does not result in unresolved metas.

### Under the hood

```agda
module UnderTheHood where
  open BasicsOfTypeInference
```

#### Example 1: `listId (1 ∷ 2 ∷ [])`

Returning to our `listId` example, when the user writes

```agda
  listId : ∀ {A} -> List A -> List A
  listId xs = xs

  _ = listId (1 ∷ 2 ∷ [])
```

here is what happens under the hood:

1. the implicit `A` gets instantiated as a metavariable `_A`
2. the type of the instantiated `listId` becomes `List _A -> List _A`
3. `List _A` (what the instantiated `listId` expects as an argument) gets unified with `List ℕ` (the type of the actual argument). We'll write this as `List _A =?= List ℕ`
4. From unification's point of view type constructors are injective, hence `List _A =?= List ℕ` simplifies to `_A =?= ℕ`, which immediately gets solved as `_A := ℕ`

And this is how Agda figures out that `A` gets instantiated by `ℕ`.

#### Example 2: `suc ∷ listId ((λ x -> x) ∷ [])`

Similarly, when the user writes

```agda
  _ = suc ∷ listId ((λ x -> x) ∷ [])
```

1. the implicit `A` gets instantiated as a metavariable `_A`
2. the type of the instantiated `listId` becomes `List _A -> List _A`
3. `List _A` (what the instantiated `listId` expects as an argument) gets unified with `List (_B -> _B)` (the type of the actual argument). `_B` is another metavariable. Recall that we don't know the type of `x` and hence we simply make it a meta
4. `List _A` (this time the type of the result that `listId` returns) also gets unified with the expected type, which is `List (ℕ -> ℕ)`, because `suc` prepended to the result of the `listId` application is of this type
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

#### Example 3: `λ xs -> suc ∷ listId xs`

When the user writes

```agda
  _ = λ xs -> suc ∷ listId xs
```

1. the yet-unknown type of `xs` elaborates to a metavariable, say, `_LA`
2. the implicit `A` of `listId` elaborates to a metavariable `_A`
3. `List _A` (what the instantiated `listId` expects as an argument) gets unified with `_LA` (the type of the actual argument)
4. `List _A` (this time the type of the result that `listId` returns) also gets unified with the expected type, which is `ℕ -> ℕ`, because `suc` prepended to the result of the `listId` application is of this type
5. we get a unification problem consisting of two equations:

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

Finally, we'll have derivation trees like

      X        Y
      →→→→→→→→→→
        Z₁ , Z₂        A
        →→→→→→→→→→→→→→→→
               B

which reads as "if `X` and `Y` are determined in the current context, then it's possible to determine `Z₁` and `Z₂`, having which together with `A` determined in the current context, is enough to determine `B`".

## Type functions

```agda
module TypeFunctions where
  open BasicsOfTypeInference
```

Analogously to `listId` we can define `fId` that works for any `F : Set -> Set`, including `List`:

```agda
  fId : ∀ {F : Set -> Set} {A} -> F A -> F A
  fId a = a
```

Unfortunately applying `fId` to a list without explicitly instantiating `F` as `List`

```agda
  _ = fId (1 ∷ 2 ∷ [])
```

results in both `F` and `A` not being resolved. This might be surprising, but there is a good reason for this behavior: there are multiple ways `F` and `A` can be instantiated. Here's the solution that the user would probably have had in their mind:

      _F := List
      _A := ℕ

which is what a first-order unification engine would come up with. But Agda's unification engine is [higher-order](https://stackoverflow.com/a/2504347/3237465) and so this solution is also valid:

      _F := λ _ -> List ℕ
      _A := Bool

i.e. `F` ignores `A` and just returns `List ℕ`:

```agda
  _ = fId {λ _ -> List ℕ} {Bool} (1 ∷ 2 ∷ [])
```

Given that there are two valid solutions, Agda does not pick one at random and instead reports that there's ambiguity.

Even if you specify `A = ℕ`, `F` still can be either `List` or `λ _ -> List ℕ`, so you have to specify `F` (and then the problem reduces to the one that we considered earlier, hence there is no need to also specify `A`):

```agda
  _ = fId {List} (1 ∷ 2 ∷ [])
```

Therefore, `F A` (where `F` is a bound variable) uniquely determines neither `F` nor `A`, i.e. `F A !⇉ F , A`.

[Andreas Abel](https://github.com/andreasabel)'s commented:

> Future research could improve on unification via an analysis in which situation the chosen solution does not matter (however, I never got around to do this research).
>
> The example you give is such an instance: it does not matter how we solve `_F _A =?= List ℕ`, because the solutions of `_F` and `_A` can never flow out of the expression `fId _F _A (1 ∷ 2 ∷ []) : _F _A`.

### Comparison to Haskell

A type application of a variable is injective in Haskell. I.e. unification of `f a` and `g b` (where `f` and `g` are type variables) forces unification of `a` and `b`, as well as unification of `f` and `g`. I.e. not only does `f a ⇉ a` hold for arbitrary type variable `f`, but also `f a ⇉ f`. This makes it possible to define functions like

      fmap :: Functor f => (a -> b) -> f a -> f b

and use them without compulsively specifying `f` at the call site each time.

Haskell is able to infer `f`, because no analogue of Agda's `λ _ -> List ℕ` is possible in Haskell as its surface language doesn't have type lambdas. You can't pass a type family as `f` either. Therefore there exists only one solution for "unify `f a` with `List Int`" in Haskell and it's the expected one:

      f := List
      a := Int

For a type family `F` we have `F a !⇉ a` (just like in Agda), unless `F` is an [injective type family](https://gitlab.haskell.org/ghc/ghc/wikis/injective-type-families).

## Data constructors

```agda
module DataConstructors where
```

Data constructors are injective from the unification point of view and from the theoretical point of view as well (unlike type constructors). E.g. consider the type of vectors (a vector is a list whose length is statically known):

```agda
  infixr 5 _∷ᵥ_
  data Vec (A : Set) : ℕ -> Set where
    []ᵥ  : Vec A 0
    _∷ᵥ_ : ∀ {n} -> A -> Vec A n -> Vec A (suc n)
```

The `head` function is defined like that over `Vec`:

```agda
  headᵥ : ∀ {A n} -> Vec A (suc n) -> A
  headᵥ (x ∷ᵥ _) = x
```

I.e. we require an input vector to have at least one element and return that first element.

`n` can be left implicit, because `suc n ⇉ n`. In general, for a constructor `C` the following holds:

      C x₁ x₂ ... xₙ ⇉ x₁ , x₂ ... xₙ

A simple test:

```agda
  _ = headᵥ (0 ∷ᵥ []ᵥ)
```

Here we pass a one-element vector to `headᵥ` and Agda succesfully infers the implicit `n` of `headᵥ` to be `0` (i.e. no elements in the vector apart from the first one).

During unification the implicit `n` gets instantiated to a metavariable, say, `_n`, and `suc _n` (the expected length of the vector) gets unified with `suc zero` (i.e. 1, the actual length of the vector), which amounts to unifying `_n` with `zero`, which immediately results in `n := zero`.

Instead of having a constant vector, we can have a vector of an unspecified length and infer that length by providing `n` to `headᵥ` explicitly, as in

```agda
  _ = λ {n} xs -> headᵥ {ℕ} {n} xs
```

The type of that definition is `∀ {n} -> Vec ℕ (suc n) -> ℕ`.

We started by binding two variables without specifying their types, but those got inferred from how arguments are used by `headᵥ`.

Note that `_⇉_` is transitive, i.e. if `X ⇉ Y` and `Y ⇉ Z`, then `X ⇉ Z`. For example, since `Vec A n ⇉ n` (due to `Vec` being a type constructor) and `suc n ⇉ n` (due to `suc` being a data constructor), we have `Vec A (suc n) ⇉ n` (by transitivity of `_⇉_`).

## Reduction

If `X` reduces to `Y` (we'll denote that as `X ~> Y`) and `Y ⇉ Z`, then `X ⇉ Z`.

E.g. if we define an alternative version of `headᵥ` that uses `1 +_` instead of `suc`:

```agda
  headᵥ⁺ : ∀ {A n} -> Vec A (1 + n) -> A
  headᵥ⁺ (x ∷ᵥ _) = x
```

the `n` will still be inferrable:

```agda
  _ = headᵥ⁺ (0 ∷ᵥ []ᵥ)
```

This is because `1 + n` reduces to `suc n`, so the two definitions are equivalent.

Note however that a "morally" equivalent definition:

      headᵥ⁺-wrong : ∀ {A n} -> Vec A (n + 1) -> A
      headᵥ⁺-wrong (x ∷ᵥ _) = x

does not type check giving:

      I'm not sure if there should be a case for the constructor _∷ᵥ_,
      because I get stuck when trying to solve the following unification
      problems (inferred index ≟ expected index):
        suc n ≟ n₁ + 1
      when checking that the pattern x ∷ᵥ _ has type Vec A (n + 1)

That's because `_+_` is defined by pattern matching on its left operand, so `1 + n` computes while `n + 1` is stuck and does not compute as `n` is a variable rather than an expression starting with a constructor of `ℕ`. `headᵥ⁺-wrong` is a contrived example, but this problem can arise in real cases, for example consider a naive attempt to define the `reverse` function over `Vec` using an accumulator, the helper type checks perfectly:

```agda
  reverse-go : ∀ {A n m} -> Vec A m -> Vec A n -> Vec A (n + m)
  reverse-go acc  []ᵥ      = acc
  reverse-go acc (x ∷ᵥ xs) = x ∷ᵥ reverse-go acc xs
```

but the final definition gives an error:

      -- _n_390 + 0 != n of type ℕ
      reverse-wrong : ∀ {A n} -> Vec A n -> Vec A n
      reverse-wrong xs = reverse-go []ᵥ xs

That's because `reverse-go` is appled to `[]ᵥ` of type `Vec A 0` and `xs` of type `Vec A n`, so it returns a `Vec A (n + 0)`, which is not definitionally the same thing as `Vec A n`. We could prove that `n + 0` equals `n` for any `n` and use that proof to rewrite `Vec A (n + 0)` into `Vec A n`, but that would make it harder to prove properties about `reverse` defined this way.

The usual way of approaching this problem is by generalizing the helper. In the case of `reverse` we can generalize the helper to the regular `foldl` function and define `reverse` in terms of that -- that's what [they do](https://github.com/agda/agda-stdlib/blob/7c8c17b407c14c5828b8755abb7584a4878286da/src/Data/Vec/Base.agda#L270-L271) in the standard library. See [this Stack Overflow question and answer](https://stackoverflow.com/questions/33345899/how-to-enumerate-the-elements-of-a-list-by-fins-in-linear-time) for a more complex and elaborated example. Anyway, end of digression.

Agda looks under lambdas when reducing an expression, so for example `λ n -> 1 + n` and `λ n -> suc n` are two definitionally equal terms:

```agda
  _ : (λ n -> 1 + n) ≡ (λ n -> suc n)
  _ = refl
```

But Agda does not look under pattern matching lambdas, so for example these two functions

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

```agda
module WeirdPlus where
  open DataConstructors

  _+′_ : ℕ -> ℕ -> ℕ
  zero  +′ m = m
  suc n +′ m = n + suc m
```

because the usual one

      _+_ : ℕ -> ℕ -> ℕ
      zero  + m = m
      suc n + m = suc (n + m)

is subject to certain unification heuristics, which the weird one doesn't trigger.

We'll be using the following function for demonstration purposes:

```agda
  idᵥ⁺ : ∀ {A n m} -> Vec A (n +′ m) -> Vec A (n +′ m)
  idᵥ⁺ xs = xs
```

### A constant argument

`idᵥ⁺` applied to a constant vector

```agda
  _ = idᵥ⁺ (1 ∷ᵥ 2 ∷ᵥ []ᵥ)
```

gives us yellow, because Agda turns the implicit `n` and `m` into metavariables `_n` and `_m` and tries to unify the expected length of a vector (`_n +′ _m`) with the actual one (`2`) and there are multiple solutions to this problem, e.g.

```agda
  _ = idᵥ⁺ {n = 1} {m = 1} (1 ∷ᵥ 2 ∷ᵥ []ᵥ)
  _ = idᵥ⁺ {n = 2} {m = 0} (1 ∷ᵥ 2 ∷ᵥ []ᵥ)
```

Howewer as per the previous the section, we do not really need to specify `m`, since `_+′_` is defined by recursion on `n` and hence for it to reduce it suffices to specify only `n`:

```agda
  _ = idᵥ⁺ {n = 1} (1 ∷ᵥ 2 ∷ᵥ []ᵥ)
```

since with `n` specified this way the `_n` metavariable gets resolved as `_n := 1` and the expected length of an argument, `_n +′ _m`, becomes `suc m`, which Agda knows how to unify with `2` (the length of the actual argument).

Specifying `m` instead of `n` won't work though:

```agda
  _ = idᵥ⁺ {m = 1} (1 ∷ᵥ 2 ∷ᵥ []ᵥ)
```

Agda can't resolve `_n`. This is because `_+′_` is defined by pattern matching on its first variable, so `1 +′ m` reduces to `suc m`, but `n +′ 1` is stuck and doesn't reduce to anything when `n` is a variable/metavariable/any stuck term. So even though there's a single solution to the

      n +′ 1 =?= 2

unification problem, Agda is not able to come up with it, because this would require unbounded search in the general case and Agda's unification machinery carefully avoids any such strategies.

### A non-constant argument

`idᵥ⁺` applied to a non-constant vector has essentially the same inference properties.

Without specializing the implicit arguments we get yellow:

```agda
  _ = λ n m (xs : Vec ℕ (n +′ m)) -> idᵥ⁺ xs
```

Specializing `m` doesn't help, still yellow:

```agda
  _ = λ n m (xs : Vec ℕ (n +′ m)) -> idᵥ⁺ {m = m} xs
```

And specializing `n` (with or without `m`) allows Agda to resolve all the metas:

```agda
  _ = λ n m (xs : Vec ℕ (n +′ m)) -> idᵥ⁺ {n = n} xs
  _ = λ n m (xs : Vec ℕ (n +′ m)) -> idᵥ⁺ {n = n} {m = m} xs
```

### Examples

So we have the following rule of thumb: whenever the type of function `h` mentions function `f` at the type level, every argument that gets pattern matched on in `f` (including any internal function calls) should be made explicit in `h` and every other argument can be left implicit (there are a few exceptions to this rule, which we'll consider below, but it applies in most cases).

#### Example 1: `_+′_`

`idᵥ⁺` mentions `_+′_` in its type:

      idᵥ⁺ : ∀ {A n m} -> Vec A (n +′ m) -> Vec A (n +′ m)

and `_+′_` pattern matches on `n`, hence Agda won't be able to infer `n`, i.e. the user will have to provide it and so it should be made explicit:

      idᵥ⁺ : ∀ {A m} n -> Vec A (n +′ m) -> Vec A (n +′ m)

Since `_+′_` doesn't match on its second argument, `m`, we leave it implicit.

#### Example 2: `_∸_`

A function mentioning `_∸_`

      _-_ : ℕ -> ℕ -> ℕ
      n     - zero  = n
      zero  - suc m = zero
      suc n - suc m = n - m

at type level has to receive both the arguments that get fed to `_∸_` explicitly as `_∸_` matches on both of them:

```agda
  idᵥ⁻ : ∀ {A} n m -> Vec A (n ∸ m) -> Vec A (n ∸ m)
  idᵥ⁻ n m xs = xs
```

and none of

```agda
  _ = idᵥ⁻ 2 _ (1 ∷ᵥ []ᵥ)  -- `m` can't be inferred
  _ = idᵥ⁻ _ 1 (1 ∷ᵥ []ᵥ)  -- `n` can't be inferred
```

is accepted unlike

```agda
  _ = idᵥ⁻ 2 1 (1 ∷ᵥ []ᵥ)
```

#### Example 3: `_*_`

A function mentioning `_*_`

      _*_ : ℕ -> ℕ -> ℕ
      zero  * m = zero
      suc n * m = m + n * m

at the type level has to receive both the arguments that get fed to `_*_` explicitly, even though `_*_` doesn't directly match on `m`. This is because in the second clause `_*_` expands to `_+_`, which does match on `m`. So it's

```agda
  idᵥ* : ∀ {A} n m -> Vec A (n * m) -> Vec A (n * m)
  idᵥ* n m xs = xs
```

and none of

```agda
  _ = idᵥ* 2 _ (1 ∷ᵥ 2 ∷ᵥ []ᵥ)  -- `m` can't be inferred
  _ = idᵥ* _ 1 (1 ∷ᵥ 2 ∷ᵥ []ᵥ)  -- `n` can't be inferred
```

type check, unlike

```agda
  _ = idᵥ* 2 1 (1 ∷ᵥ 2 ∷ᵥ []ᵥ)
```

#### Example 4: `_+′_`, two arguments

With this definition:

```agda
  ignore2 : ∀ n m -> Vec ℕ (n +′ m) -> Vec ℕ (m +′ n) -> ℕ
  ignore2 _ _ _ _ = 0
```

it suffices to explicitly provide either `n` or `m`:

```agda
  _ = ignore2 2 _ (1 ∷ᵥ 2 ∷ᵥ 3 ∷ᵥ []ᵥ) (4 ∷ᵥ 5 ∷ᵥ 6 ∷ᵥ []ᵥ)
  _ = ignore2 _ 1 (1 ∷ᵥ 2 ∷ᵥ 3 ∷ᵥ []ᵥ) (4 ∷ᵥ 5 ∷ᵥ 6 ∷ᵥ []ᵥ)
```

This is because with explicitly provided `n` Agda can determine `m` from `n +′ m` and with explicitly provided `m` Agda can determine `n` from `m +′ n`.

#### Example 5: nested `_+′_`, two arguments

In the following definition we have multiple mentions of `_+′_` at the type level:

```agda
  ignore2p : ∀ {m p} n -> Vec ℕ (n +′ (m +′ p)) -> Vec ℕ (n +′ m) -> ℕ
  ignore2p _ _ _ = 0
```

and three variables used as arguments to `_+′_`, yet only the `n` variable needs to be bound explicitly. This is due to the fact that it's enough to know `n` to determine what `m` is (from `Vec ℕ (n +′ m)`) and then knowing both `n` and `m` is enough to determine what `p` is (from `Vec ℕ (n +′ (m +′ p))`). Which can be written as

           n
           →
      n    m
      →→→→→→
         p

Note that the order of the `Vec` arguments doesn't matter, Agda will postpone resolving a metavariable until there is enough info to resolve it.

A test:

```agda
  _ = ignore2p 1 (3 ∷ᵥ 4 ∷ᵥ 5 ∷ᵥ 6 ∷ᵥ []ᵥ) (1 ∷ᵥ 2 ∷ᵥ []ᵥ)
```

#### Example 6: nested `_+′_`, one argument

A very similar example:

```agda
  ignore1p : ∀ {m p} n -> Vec (Vec ℕ (n +′ m)) (n +′ (m +′ p)) -> ℕ
  ignore1p _ _ = 0
```

Just like in the previous case it's enough to provide only `n` explicitly as the same

           n
           →
      n    m
      →→→→→→
         p

logic applies. Test:

```agda
  _ = ignore1p 1 ((1 ∷ᵥ 2 ∷ᵥ []ᵥ) ∷ᵥ (3 ∷ᵥ 4 ∷ᵥ []ᵥ) ∷ᵥ (5 ∷ᵥ 6 ∷ᵥ []ᵥ) ∷ᵥ []ᵥ)
```

#### Large elimination

```agda
module LargeElimination where
  open BasicsOfTypeInference
```

So far we've been talking about functions that pattern match on terms and return terms, but in Agda we can also pattern match on terms and return types. Consider

```agda
  ListOfBoolOrℕ : Bool -> Set
  ListOfBoolOrℕ false = List Bool
  ListOfBoolOrℕ true  = List ℕ
```

This function matches on a `Bool` argument and returns *the type* of lists with the type of elements depending on the `Bool` argument.

Having an identity function over a `ListOfBoolOrℕ b`

```agda
  idListOfBoolOrℕ : {b : Bool} -> ListOfBoolOrℕ b -> ListOfBoolOrℕ b
  idListOfBoolOrℕ xs = xs
```

we can show that the implicit `b` can't be inferred, as this:

```agda
  _ = idListOfBoolOrℕ (1 ∷ 2 ∷ 3 ∷ [])
```

results in unresolved metas, while this:

```agda
  _ = idListOfBoolOrℕ {b = true} (1 ∷ 2 ∷ 3 ∷ [])
```

is accepted by the type checker.

The reason for this behavior is the same as with all the previous examples: pattern matching blocks inference and `ListOfBoolOrℕ` is a pattern matching function.

### Generalization

```agda
module Generalization where
```

In general: given a function `f` that receives `n` arguments on which there's pattern matching anywhere in the definition of `f` (including calls to other functions in the body of `f`) and `m` arguments on which there is no pattern matching, we have the following rule (for simplicity of presentation we place `pᵢ` before `xⱼ`, but the same rule works when they're interleaved)

      p₁    ...    pₙ        (f p₁ ... pₙ x₁ ... xₘ)
      →→→→→→→→→→→→→→→→→→→→→→→→→→→→→→→→→→→→→→→→→→→→→→
                    x₁    ...    xₘ

i.e. if every `pᵢ` can be inferred from the current context, then every `xⱼ` can be inferred from `f p₁ ... pₙ x₁ ... xₘ`.

There is an important exception from this rule and this is what comes next.

### [Constructor-headed functions](https://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.FindingTheValuesOfImplicitArguments)

```agda
module ConstructorHeadedFunctions where
  open BasicsOfTypeInference
  open DataConstructors
```

Consider a definition of `ListOfBoolOrℕ` that is slightly different from the previous one, but is isomorphic to it:

```agda
  BoolOrℕ : Bool -> Set
  BoolOrℕ false = Bool
  BoolOrℕ true  = ℕ

  ListOfBoolOrℕ′ : Bool -> Set
  ListOfBoolOrℕ′ b = List (BoolOrℕ b)
```

Here `ListOfBoolOrℕ′` does not do any pattern matching itself and instead immediately returns `List (BoolOrℕ b)` with pattern matching performed in `BoolOrℕ b`. There's still pattern matching on `b` and the fact that it's inside another function call in the body of `ListOfBoolOrℕ′` should not change anything as we've discussed previously. Yet `id` defined over such lists:

```agda
  idListOfBoolOrℕ′ : {b : Bool} -> ListOfBoolOrℕ′ b -> ListOfBoolOrℕ′ b
  idListOfBoolOrℕ′ xs = xs
```

does not require the user to provide `b` explicitly, i.e. the following type checks just fine:

```agda
  _ = idListOfBoolOrℕ′ (1 ∷ 2 ∷ 3 ∷ [])
```

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

in that the latter definition has the same head in both the clauses (`List`) and so the heuristic doesn't apply. Even though Agda really could have figured out that `ListOfBoolOrℕ` is also injective (the fact that `ListOfBoolOrℕ` is not consdered invertible is more of an implementation detail than a theoretical limination).

Here's an example of a theoretical limitation: a definition like

```agda
  BoolOrBool : Bool -> Set
  BoolOrBool true  = Bool
  BoolOrBool false = Bool
```

can't be inverted, because the result (`Bool` in both the cases) does not determine the argument (either `true` or `false`).

#### Example 1: universe of types

There's a standard technique ([the universe pattern](https://groups.google.com/forum/#!msg/idris-lang/N9_pVqG8dO8/mHlNmyL6AwAJ)) that allows us to get ad hoc polymorphism (a.k.a. type classes) for a closed set of types in a dependently typed world.

We introduce a universe of types, which is a data type containing tags for actual types:

```agda
  data Uni : Set where
    bool nat : Uni
    list : Uni -> Uni
```

interpret those tags as types that they encode:

```agda
  ⟦_⟧ : Uni -> Set
  ⟦ bool   ⟧ = Bool
  ⟦ nat    ⟧ = ℕ
  ⟦ list A ⟧ = List ⟦ A ⟧
```

and then mimic the `Eq` type class for the types from this universe by directly defining equality functions:

```agda
  _==Bool_ : Bool -> Bool -> Bool
  true  ==Bool true  = true
  false ==Bool false = true
  _     ==Bool _     = false

  _==ℕ_ : ℕ -> ℕ -> Bool
  zero  ==ℕ zero  = true
  suc n ==ℕ suc m = n ==ℕ m
  _     ==ℕ _     = false

  mutual
    _==List_ : ∀ {A} -> List ⟦ A ⟧ -> List ⟦ A ⟧ -> Bool
    []       ==List []       = true
    (x ∷ xs) ==List (y ∷ ys) = (x == y) && (xs ==List ys)
    _        ==List _        = false

    _==_ : ∀ {A} -> ⟦ A ⟧ -> ⟦ A ⟧ -> Bool
    _==_ {nat   } x y = x ==ℕ    y
    _==_ {bool  } x y = x ==Bool y
    _==_ {list A} x y = x ==List y
```

`_==_` checks equality of two elements from any type from the universe.

Note that `_==List_` is defined mutually with `_==_`, because elements of lists can be of any type from the universe, i.e. they can also be lists, hence the mutual recursion.

A few tests:

```agda
  -- Check equality of two equal elements of `ℕ`.
  _ : (42 == 42) ≡ true
  _ = refl

  -- Check equality of two non-equal elements of `List Bool`.
  _ : ((true ∷ []) == (false ∷ [])) ≡ false
  _ = refl

  -- Check equality of two equal elements of `List (List ℕ)`.
  _ : (((4 ∷ 81 ∷ []) ∷ (57 ∷ 2 ∷ []) ∷ []) == ((4 ∷ 81 ∷ []) ∷ (57 ∷ 2 ∷ []) ∷ [])) ≡ true
  _ = refl

  -- Check equality of two non-equal elements of `List (List ℕ)`.
  _ : (((4 ∷ 81 ∷ []) ∷ (57 ∷ 2 ∷ []) ∷ []) == ((4 ∷ 81 ∷ []) ∷ [])) ≡ false
  _ = refl
```

It's possible to leave `A` implicit in `_==_` and get it inferred in the tests above precisely because `⟦_⟧` is constructor-headed. If we had `bool₁` and `bool₂` tags both mapping to `Bool`, inference for `_==_` would not work for booleans, lists of booleans etc. In the version of Agda I'm using inference for naturals, lists of naturals etc still works though, if an additional `bool` is added to the universe, i.e. breaking constructor-headedness of a function for certain arguments does not result in inference being broken for others.

#### Example 2: `boolToℕ`

Constructor-headed functions can also return values rather than types. For example this function:

```agda
  boolToℕ : Bool -> ℕ
  boolToℕ false = zero
  boolToℕ true  = suc zero
```

is constructor-headed, because in the two clauses heads are constructors and they're different (`zero` vs `suc`).

So if we define a version of `id` that takes a `Vec` with either 0 or 1 element:

```agda
  idVecAsMaybe : ∀ {b} -> Vec ℕ (boolToℕ b) -> Vec ℕ (boolToℕ b)
  idVecAsMaybe xs = xs
```

then it won't be necessary to specify `b`:

```agda
  _ = idVecAsMaybe []ᵥ
  _ = idVecAsMaybe (0 ∷ᵥ []ᵥ)
```

as Agda knows how to solve `boolToℕ _b =?= zero` or `boolToℕ _b =?= suc zero` due to `boolToℕ` being invertible.

`idVecAsMaybe` supplied with a vector of length greater than `1` correctly gives an error (as opposed to merely reporting that there's an unsolved meta):

      -- suc _n_624 != zero of type ℕ
      _ = idVecAsMaybe (0 ∷ᵥ 1 ∷ᵥ []ᵥ)

Note that `boolToℕ` defined like that:

```agda
  boolToℕ′ : Bool -> ℕ
  boolToℕ′ false = zero + zero
  boolToℕ′ true  = suc zero
```

is not considered to be constructor-headed, because Agda does not attempt to unfold recursive definitions in the RHS of a clause of a function. With this definition the second test in

```agda
  idVecAsMaybe′ : ∀ {b} -> Vec ℕ (boolToℕ′ b) -> Vec ℕ (boolToℕ′ b)
  idVecAsMaybe′ xs = xs

  _ = idVecAsMaybe′ []ᵥ
  _ = idVecAsMaybe′ (0 ∷ᵥ []ᵥ)
```

is yellow. But not the first one. I guess with `idVecAsMaybe′ []ᵥ` Agda tries to unify `zero` (the actual length of the vector) with both the RHSes of `boolToℕ′` and since `zero` is definitely not equal to `suc zero`, only the `zero + zero` case remains, so Agda finally decides to reduce that expression to find out that it indeed equals to `zero`.

### Constructor/argument-headed functions

```agda
module ConstructorArgumentHeadedFunctions where
  open DataConstructors
```

Recall that we've been using a weird definition of plus

> because the usual one
>
>       _+_ : ℕ -> ℕ -> ℕ
>       zero  + m = m
>       suc n + m = suc (n + m)
>
> is subject to certain unification heuristics, which the weird one doesn't trigger.

As you can see in the usual definition we return one of the arguments in the first clause and the second clause starts with a constructor. Just like for regular constructor-headed functions, Agda has enhanced inference for functions of this kind as well.

Quoting the [changelog](https://github.com/agda/agda/blob/064095e14042bdf64c7d7c97c2869f63f5f1f8f6/doc/release-notes/2.5.4.md#pattern-matching):

> Improved constraint solving for pattern matching functions
> Constraint solving for functions where each right-hand side has a distinct rigid head has been extended to also cover the case where some clauses return an argument of the function. A typical example is append on lists:
>
>       _++_ : {A : Set} → List A → List A → List A
>       []       ++ ys = ys
>       (x ∷ xs) ++ ys = x ∷ (xs ++ ys)
>
> Agda can now solve constraints like `?X ++ ys == 1 ∷ ys` when `ys` is a neutral term.

#### Example 1: back to `idᵥ⁺`

Now if we come back to this example:

<blockquote>
<p><code>idᵥ⁺</code> applied to a non-constant vector has essentially the same inference properties.</p>
<p>Without specializing the implicit arguments we get yellow:</p>
<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-symbol">&#955;</span> <span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-bound-variable">m</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">xs</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">Vec</span> <span class="agda2-highlight-datatype">&#8469;</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">+&#8242;</span></span> <span class="agda2-highlight-bound-variable">m</span><span class="agda2-highlight-symbol">))</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-function"><span class="agda2-highlight-unsolved-meta">id&#7525;&#8314;</span></span> <span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-bound-variable">xs</span></span></span>
</pre>
<p>Specializing <code>m</code> doesn't help, still yellow:</p>
<pre>  <span class="agda2-highlight-symbol"><span class="agda2-highlight-function">_</span></span> <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-symbol">&#955;</span> <span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-bound-variable">m</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">xs</span> <span class="agda2-highlight-symbol">:</span> <span class="agda2-highlight-datatype">Vec</span> <span class="agda2-highlight-datatype">&#8469;</span> <span class="agda2-highlight-symbol">(</span><span class="agda2-highlight-bound-variable">n</span> <span class="agda2-highlight-operator"><span class="agda2-highlight-function">+&#8242;</span></span> <span class="agda2-highlight-bound-variable">m</span><span class="agda2-highlight-symbol">))</span> <span class="agda2-highlight-symbol">-&gt;</span> <span class="agda2-highlight-function"><span class="agda2-highlight-unsolved-meta">id&#7525;&#8314;</span></span> <span class="agda2-highlight-symbol">{</span>m <span class="agda2-highlight-symbol">=</span> <span class="agda2-highlight-bound-variable">m</span><span class="agda2-highlight-symbol">}</span> <span class="agda2-highlight-unsolved-constraint"><span class="agda2-highlight-unsolved-meta"><span class="agda2-highlight-bound-variable">xs</span></span></span>
</pre>
</blockquote>

but define `idᵥ⁺` over `_+_` rather than `_+′_`:

```agda
  idᵥ⁺ : ∀ {A n m} -> Vec A (n + m) -> Vec A (n + m)
  idᵥ⁺ xs = xs
```

then supplying only `m` explicitly:

```agda
  _ = λ n m (xs : Vec ℕ (n + m)) -> idᵥ⁺ {m = m} xs
```

satisfies the type checker due to `_+_` being constructor/argument-headed.

And

```agda
  _ = λ n m (xs : Vec ℕ (n + m)) -> idᵥ⁺ xs
```

still gives yellow, because it's still inherently ambiguous.

Additionally, this now also type checks:

```agda
  _ = idᵥ⁺ {m = 0} (1 ∷ᵥ 2 ∷ᵥ []ᵥ)
```

This is because instantiating `m` at `0` in `idᵥ⁺` makes `_+_` constructor-headed, because if we inline `m` in the definition of `_+_`, we'll get:

      _+0 : ℕ -> ℕ
      zero  +0 = zero
      suc n +0 = suc (n +0)

which is clearly constructor-headed.

And

```agda
  _ = idᵥ⁺ {m = 1} (1 ∷ᵥ 2 ∷ᵥ []ᵥ)
```

still does not type check, because inlining `m` as `1` does not make `_+_` constructor-headed:

      _+1 : ℕ -> ℕ
      zero  +1 = suc zero
      suc n +1 = suc (n +1)

#### Example 2: polyvariadic `zipWith`: list-based

```agda
module PolyvariadicZipWith where
  open import Data.List.Base as List
  open import Data.Vec.Base as Vec renaming (_∷_ to _∷ᵥ_; [] to []ᵥ)
```

We can define this family of functions over vectors:

      replicate : ∀ {m} → A → Vec A m
      map : ∀ {m} → (A → B) → Vec A m → Vec B m
      zipWith : ∀ {m} → (A → B → C) → Vec A m → Vec B m → Vec C m
      zipWith3 : ∀ {m} → (A → B → C → D) → Vec A m → Vec B m → Vec C m → Vec D m

(the Agda stdlib provides all of those but the last one)

Can we define a generic function that covers all of the above? Its type signature should look like this:

      (A₁ -> A₂ -> ... -> B) -> Vec A₁ m -> Vec A₂ m -> ... -> Vec B m

Yes: we can parameterize a function by a list of types and compute those n-ary types from the list. Folding a list of types into a type, given also the type of the result, is trivial:

```agda
  ToFun : List Set -> Set -> Set
  ToFun  []      B = B
  ToFun (A ∷ As) B = A -> ToFun As B
```

This allows us to compute the n-ary type of the function. In order to compute the n-ary type of the result we need to map the list of types with `λ A -> Vec A m` and turn `B` (the type of the resulting of the zipping function) into `Vec B m` (the type of the final result):

```agda
  ToVecFun : List Set -> Set -> ℕ -> Set
  ToVecFun As B m = ToFun (List.map (λ A -> Vec A m) As) (Vec B m)
```

It only remains to recurse on the list of types in an auxiliary function (n-ary `(<*>)`, in Haskell jargon) and define `zipWithN` in terms of that function (we use `Vec.zipWith _$_` instead of `_⊛_`, because the latter has a [slightly broken inference](https://github.com/agda/agda-stdlib/issues/1338) in some versions of the standard library):

```agda
  apN : ∀ {As B m} -> Vec (ToFun As B) m -> ToVecFun As B m
  apN {[]}     ys = ys
  apN {A ∷ As} fs = λ xs -> apN {As} (Vec.zipWith _$_ fs xs)

  zipWithN : ∀ {As B m} -> ToFun As B -> ToVecFun As B m
  zipWithN f = apN (Vec.replicate f)
```

Some tests verifying that the function does what it's supposed to:

```agda
  _ : zipWithN 1 ≡ (1 ∷ᵥ 1 ∷ᵥ 1 ∷ᵥ []ᵥ)
  _ = refl

  _ : zipWithN suc (1 ∷ᵥ 2 ∷ᵥ 3 ∷ᵥ []ᵥ) ≡ (2 ∷ᵥ 3 ∷ᵥ 4 ∷ᵥ []ᵥ)
  _ = refl

  _ : zipWithN _+_ (1 ∷ᵥ 2 ∷ᵥ 3 ∷ᵥ []ᵥ) (4 ∷ᵥ 5 ∷ᵥ 6 ∷ᵥ []ᵥ) ≡ (5 ∷ᵥ 7 ∷ᵥ 9 ∷ᵥ []ᵥ)
  _ = refl
```

Note how we do not provide the list of types explicitly in any of these cases, even though there's pattern matching on that list.

Your first guess is probably that Agda can infer the list of types from the type of the function passed to `zipWithN`. I.e. the type of `_+_` is `ℕ -> ℕ -> ℕ` and so it corresponds to `Fun (ℕ ∷ ℕ ∷ []) ℕ`. But that is not really clear to Agda as this snippet:

```agda
  _ : ToFun _ _ ≡ (ℕ -> ℕ -> ℕ)
  _ = refl
```

gives yellow. And this is for a good reason, there are three ways to compute `ℕ -> ℕ -> ℕ` with `ToFun`:

      ToFun (ℕ ∷ ℕ ∷ [])  ℕ             -- The obvious one.
      ToFun (ℕ ∷ [])     (ℕ -> ℕ)       -- A sneaky one.
      ToFun []           (ℕ -> ℕ -> ℕ)  -- Another sneaky one.

So the `ToFun _As _B =?= ℕ -> ℕ -> ℕ` unification problem does not have a single solution and hence can't be solved by Agda.

However Agda sees that `zipWithN _+_` is applied to two vectors and the result is also a vector and since in the type signature of `zipWithN`

      zipWithN : ∀ {As B n} -> ToFun As B -> ToVecFun As B n

the types of the arguments and the result are computed from `ToVecFun As B n`, we have the following unification problem:

      ToVecFun _As _B _n =?= Vec ℕ m -> Vec ℕ m -> Vec ℕ m

which Agda can immediately solve as

      _As := ℕ ∷ ℕ ∷ []
      _B  := ℕ
      _n  := m

And indeed there's no yellow here:

```agda
  _ : ∀ {m} -> ToVecFun _ _ _ ≡ (Vec ℕ m -> Vec ℕ m -> Vec ℕ m)
  _ = refl
```

The reason for that is that `ToVecFun` does not return an arbitrary `B` in the `[]` case like `ToFun` -- `ToVecFun` always returns a `Vec` in the `[]` case, so resolving metas as

      _As := ℕ ∷ []
      _B  := ℕ -> ℕ
      _n  := m

is not possible as that would compute to `Vec ℕ m -> Vec (ℕ -> ℕ) m` rather than `Vec ℕ m -> Vec ℕ m -> Vec ℕ m`.

Hence there's no ambiguity now and since `ToVecFun` also returns a `_->_` in the `_∷_` case, that function is constructor-headed (as `Vec` and `_->_` are two different type constructors) and Agda knows how to infer the list of types.

If we omit the resulting vector, we'll get yellow:

```agda
  _ : zipWithN _+_ (1 ∷ᵥ 2 ∷ᵥ 3 ∷ᵥ []ᵥ) (4 ∷ᵥ 5 ∷ᵥ 6 ∷ᵥ []ᵥ) ≡ _
  _ = refl
```

as a standlone

      ToVecFun _As _B _n =?= Vec ℕ m -> Vec ℕ m -> _R

is inherently ambiguous again and Agda would need to do some non-trivial proof search in order to realize that `_R` can't be an `_->_` because of what the other equation is:

      ToFun _As _B =?= ℕ -> ℕ -> ℕ

However, by specifying `B` to something that is clearly different from `->`, we can turn `ToFun` (a constructor/argument-headed function) into a proper constructor-headed function. This type checks:

```agda
  _ : ToFun _ ℕ ≡ (ℕ -> ℕ -> ℕ)
  _ = refl
```

And hence we can omit the resulting vector, if `B` is specified, because knowing `B` and the type of the zipping function is sufficient for inverting `ToFun` and inferring `As`:

```agda
  _ : zipWithN {B = ℕ} _+_ (1 ∷ᵥ 2 ∷ᵥ 3 ∷ᵥ []ᵥ) (4 ∷ᵥ 5 ∷ᵥ 6 ∷ᵥ []ᵥ) ≡ _
  _ = refl
```

We don't need to invert `ToFun` when the _spine_ of `As` is provided explicitly:

```agda
  _ : zipWithN {As = _ ∷ _ ∷ []} _+_ (1 ∷ᵥ 2 ∷ᵥ 3 ∷ᵥ []ᵥ) (4 ∷ᵥ 5 ∷ᵥ 6 ∷ᵥ []ᵥ) ≡ _
  _ = refl
```

as Agda only needs to know the spine of `As` and not the actual types stored in the list in order for `ToFun` to compute (since `ToFun` is defined by pattern matching on the spine of its argument and so the actual elements of the list are computationally irrelevant). `ToFun (_A₁ ∷ _A₂ ∷ []) _B` computes to `_A₁ -> _A₂ -> _B` and unifying that type with `ℕ -> ℕ -> ℕ` is a trivial task.

Omitting a second vector still allows Agda to infer everything:

```agda
  _ : zipWithN _+_ (1 ∷ᵥ 2 ∷ᵥ 3 ∷ᵥ []ᵥ) _ ≡ (5 ∷ᵥ 7 ∷ᵥ 9 ∷ᵥ []ᵥ)
  _ = refl
```

as it only needs to solve

      ToVecFun _As _B _n =?= Vec ℕ m -> _ -> Vec ℕ m

as

      _As := Vec ℕ m ∷ Vec ℕ m ∷ []
      _B  := Vec ℕ m
      _n  := m

(which is possible due to the type of result being the concrete `Vec`, disjoint with `_->_`) and then solve all the pointwise equations:

      1 + _ =?= 5
      2 + _ =?= 6
      3 + _ =?= 7

by reducing them to

      suc _             =?= suc (suc (suc (suc (suc _))))
      suc (suc _)       =?= suc (suc (suc (suc (suc (suc _)))))
      suc (suc (suc _)) =?= suc (suc (suc (suc (suc (suc (suc _))))))

(due to `_+_` being defined by pattern matching on its first argument) and then inverting all the `suc`s.

Omitting a first vector gives yellow, though:

```agda
  _ : zipWithN _+_ _ (4 ∷ᵥ 5 ∷ᵥ 6 ∷ᵥ []ᵥ) ≡ (5 ∷ᵥ 7 ∷ᵥ 9 ∷ᵥ []ᵥ)
  _ = refl
```

as the version of Agda that I'm using can't solve equations like

```agda
  _ : _ + 4 ≡ 5
  _ = refl
```

due `_ + 4` being stuck and not reducing to anything. Even though Agda could potentially solve such equations, given the constructor/variable-headedness of `_+_`.

Finally, constructor-headedness is compositional. The

      ToVecFun _As _B _n =?= Vec ℕ m -> Vec ℕ m -> Vec ℕ m

problem expands to

      ToFun (List.map (λ A -> Vec A m) _As) (Vec _B _n) =?= Vec ℕ m -> Vec ℕ m -> Vec ℕ m

Agda sees that the RHS was computed from the `_∷_` case of `ToFun`, but the actual argument of `ToFun` is not a meta or a `_∷_` already, it's a `List.map (λ A -> Vec A m) _As` and so Agda needs to invert `List.map` for unification to proceed. Which is no problem, since `List.map` is also constructor-headed.

## Eta-rules

```agda
module EtaRules where
```

Agda implements eta-rules for [negative types](https://ncatlab.org/nlab/show/negative+type).

One such rule is that a function is definitionally equal to its eta-expanded version:

```agda
  _ : ∀ {A : Set} {B : A -> Set} -> (f : ∀ x -> B x) -> f ≡ (λ x -> f x)
  _ = λ f -> refl
```

Usefulness of this eta-rule is not something that one thinks of much, but that is only until they try to work in a language that doesn't support the rule (spoiler: it's a huge pain).

All records support eta-rules by default (that can be switched off for a single record via an explicit [`no-eta-equality`](https://agda.readthedocs.io/en/latest/language/record-types.html#eta-expansion) mark or for all records in a file via `{-# OPTIONS --no-eta-equality #-}` at the beginning of the file).

The simplest record is one with no fields:

```agda
  record Unit : Set where
    constructor unit
```

The eta-rule for `Unit` is "all terms of type `Unit` are _definitionally_ equal to `unit`":

```agda
  _ : (u : Unit) -> u ≡ unit
  _ = λ u -> refl
```

Consequently, since all terms of type `Unit` are equal to `unit`, they are also equal to each other:

```agda
  _ : (u1 u2 : Unit) -> u1 ≡ u2
  _ = λ u1 u2 -> refl
```

Since Agda knows that any value of type `Unit` is in fact `unit`, Agda can infer the value of any implicit argument of type `Unit`. I.e. `A` and `{_ : Unit} -> A` are isomorphic for any `A`:

```agda
  _ : {A : Set} -> A -> {_ : Unit} -> A
  _ = λ x -> x

  _ : {A : Set} -> ({_ : Unit} -> A) -> A
  _ = λ x -> x
```

This eta-rule applies to `⊤` as well, precisely because `⊤` is defined as a record with no fields.

For a record with fields the eta-rule is "an element of the record is always the constructor of the record applied to its fields". For example:

```agda
  record Triple (A B C : Set) : Set where
    constructor triple
    field
      fst : A
      snd : B
      thd : C
  open Triple

  _ : ∀ {A B C} -> (t : Triple A B C) -> t ≡ triple (fst t) (snd t) (thd t)
  _ = λ t -> refl
```

Correspondingly, since Agda knows that any value of type `Triple A B C` is `triple` applied to some argument, these two types are isomorphic:

      ∀ {x y z} -> D x y z
      {(triple x y z) : Triple A B C} -> D x y z

for any `A`, `B`, `C`, `D` as witnessed by

```agda
  _ : ∀ {A B C} {D : A -> B -> C -> Set} -> ({(triple x y z) : Triple A B C} -> D x y z) -> ∀ {x y z} -> D x y z
  _ = λ d -> d

  _ : ∀ {A B C} {D : A -> B -> C -> Set} -> (∀ {x y z} -> D x y z) -> {(triple x y z) : Triple A B C} -> D x y z
  _ = λ d -> d
```

We'll consider the opportunities that this feature gives us a bit later.

Supporting eta-equality for sum types is [possible in theory](https://ncatlab.org/nlab/show/sum+type#as_a_positive_type), but Agda does not implement that. Any `data` definition in Agda does not support eta-equality, including an empty `data` declaration like

```agda
  data Empty : Set where
```

(which is always isomorphic to `Data.Empty.⊥` and is how `⊥` is defined in the first place).

Eta-rules for records may seem not too exciting, but there are a few important use cases.

### Computing predicates: division

Consider the division function (defined by repeated subtraction in a slightly weird way to please the termination checker):

```agda
module Div-v1 where
  open import Data.List.Base as List
  open import Data.Maybe.Base

  -- This function divides its first argument by the successor of the second one via repeated
  -- subtraction.
  _`div-suc`_ : ℕ -> ℕ -> ℕ
  n `div-suc` m = go n m where
    go : ℕ -> ℕ -> ℕ
    go  0       m      = 0
    go (suc n)  0      = suc (go n m)
    go (suc n) (suc m) = go n m

  _`div`_ : ℕ -> ℕ -> Maybe ℕ
  n `div` 0     = nothing
  n `div` suc m = just (n `div-suc` m)
```

An attempt to divide a natural number by `0` results in `nothing`, otherwise we get the quotient wrapped in `just`.

We can check that all natural numbers up to `12` get divided by `3` correctly:

```agda
  _ : List.map (λ n -> n `div` 3) (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ 10 ∷ 11 ∷ 12 ∷ [])
    ≡ List.map  just              (0 ∷ 0 ∷ 0 ∷ 1 ∷ 1 ∷ 1 ∷ 2 ∷ 2 ∷ 2 ∷ 3 ∷ 3  ∷ 3  ∷ 4  ∷ [])
  _ = refl
```

and that an attempt to divide any number by `0` will give us `nothing`:

```agda
  _ : ∀ n -> n `div` 0 ≡ nothing
  _ = λ n -> refl
```

This all works as expected, however we can redefine the division function is a way that allows us to

1. not wrap the result in `Maybe`
2. easily recover the original definition

Here's how:

```agda
module Div-v2 where
  open Div-v1 using (_`div-suc`_)

  open import Data.List.Base as List
  open import Data.Maybe.Base

  _≢0 : ℕ -> Set
  _≢0 0 = ⊥
  _≢0 _ = ⊤

  _`div`_ : ℕ -> ∀ m -> {m ≢0} -> ℕ
  _`div`_ n  0      {()}
  _`div`_ n (suc m)      = n `div-suc` m  -- The worker is the same as in the original version.
```

Now instead of returning a `Maybe` we require the caller to provide a proof that the divisor is not zero. And the original definition can be recovered as

```agda
  _`div-original`_ : ℕ -> ℕ -> Maybe ℕ
  n `div-original` 0     = nothing
  n `div-original` suc m = just (n `div` suc m)
```

There exist a bunch of blogposts advocating a similar style of programming:

1. [Parse, don't validate](https://lexi-lambda.github.io/blog/2019/11/05/parse-don-t-validate/)
2. [Type Safety Back and Forth](https://www.parsonsmatt.org/2017/10/11/type_safety_back_and_forth.html)
3. [The golden rule of software quality](http://www.haskellforall.com/2020/07/the-golden-rule-of-software-quality.html)

However all those blogposts talk about introducing separate data types for expressing invariants, while what we do here instead is use the regular type of natural numbers and add an additional type-level predicate computing to `⊥` (a type, for which no value can be provided), if the divisor is zero, and `⊤` (a type with a single value) otherwise. I.e. the only way to provide a value of type `m ≢0` is to make this predicate compute to `⊤`, which requires `m` to be a `suc` of some natural number.

What Agda makes nice is that we don't need to ask the caller to provide a proof explicitly when `m` is in [WHNF](https://wiki.haskell.org/Weak_head_normal_form) (i.e. `m` is either `zero` or `suc m'` for some `m'`, definitionally), which enables us to leave the `m ≢0` argument implicit. The reason for that is when the outermost constructor of `m` is known, we have two cases:

1. it's `zero`: `zero ≢0` reduces to `⊥` and no value of that type can be provided, hence there's no point in making that argument explicit as the user will have to reconsider what they're doing anyway
2. it's `suc`: `suc m' ≢0` reduces to `⊤` and due to the eta-rule of `⊤`, the value of `⊤` can be inferred automatically

Let us now see how this works in practice. Here we divide all numbers up to `12` by `4`:

```agda
  _ : List.map (λ n -> n `div` 4) (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ 10 ∷ 11 ∷ 12 ∷ [])
    ≡                             (0 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 2 ∷ 2 ∷ 2  ∷ 2  ∷ 3  ∷ [])
  _ = refl
```

Note how we don't need to provide any proof that the divisor is not equal to zero, Agda figures that out itself.

An attempt to divide a number by `0` gives us an unresolved metavariable of type `⊥` (note the yellow):

```agda
  -- _1254 : ⊥
  _ : ∀ n -> n `div` 0 ≡ n `div` 0
  _ = λ n -> refl
```

(if you're curious whether it's possible to throw an actual error instead of having an unresolved metavariable, then Agda does allow us to do that via [Reflection](https://agda.readthedocs.io/en/latest/language/reflection.html), see [this file](https://github.com/effectfully/random-stuff/blob/0857360c917a834a0473ab68fcf24c05960fc335/ThrowOnZero.agda))

So in short, the eta-rule of `⊤` allows for convenient APIs when there are computational properties involved and it's fine to force upon the caller to specify enough info to make the property compute. In the above cases we only required a single argument to be in WHNF, but in other cases it can be necessary to have multiple arguments in [canonical form](https://ncatlab.org/nlab/show/canonical+form) (see [this Stackoverflow question and answer](https://stackoverflow.com/questions/33270639/so-whats-the-point) for an example).

If we attempt to call ``_`div`_`` with the divisor argument not being in WHNF, we'll get yellow:

```agda
  _ : ℕ -> ∀ m -> {m ≢0} -> ℕ
  _ = λ n m -> n `div` m
```

since it's not possible to infer the value of type `m ≢0` when the type is stuck and can't reduce to anything. Which is rather inconvenient as we now have to explicitly thread the divisor-not-equal-to-zero proof through every function that eventually defers to ``_`div`_``. See the next section for an alternative solution.

### Bonus: singletons

Instead of checking if a value satisfies a certain predicate, we can sometimes provide that value in a [correct by construction](http://wiki.c2.com/?CorrectByConstruction) manner. In the case of division we need to ensure that the divisor is not zero, so we could have a special type of non-zero natural numbers for that:

```agda
  data ℕ₁ : Set where
    suc₁ : ℕ -> ℕ₁
```

and define:

```agda
  _`div₁`_ : ℕ -> ℕ₁ -> ℕ
  n `div₁` suc₁ m = n `div-suc` m
```

This is essentially what the "Parse, don't validate" approach referenced earlier is about.

However in a dependently typed language we don't actually need to create a bespoke data type for the purpose of ensuring that a value is an application of a certain constructor. Instead we can define a singleton type that allows us to promote any value to the type level:

```agda
  data Promote {A : Set} : A -> Set where
    promote : ∀ x -> Promote x
```

(there's only one value of type `Promote x`: `promote x` -- hence why it's called a singleton).

Now the useful thing about this type is that it allows us to promote an arbitrary value to the type level, in particular we can promote an application of `suc` to a type variable:

```agda
  _`divᵖ`_ : ∀ {m} -> ℕ -> Promote (suc m) -> ℕ
  n `divᵖ` promote (suc m) = n `div-suc` m
```

This ensures that the second argument is `promote` applied to a natural number and that natural number is of the `suc m` form for some `m`, which is exactly the invariant that we want to express. Note how Agda does not ask to handle a

      n `divᵖ` promote 0 = ?

case, as it knows that this case cannot occur.

We can check that the implicit `m` can be inferred without any problems:

```agda
  _ : ∀ {m} -> ℕ -> Promote (suc m) -> ℕ
  _ = λ n m -> n `divᵖ` m
```

which clearly has to be the case as `m` is an argument to a data constructor (`suc`) and the application (`suc m`) is an argument to a type constructor (`Promote`) and type and data constructors are inference-friendly due to them being invertible as we discussed before.

A test:

```agda
  _ : List.map (λ n -> n `divᵖ` promote 4) (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ 10 ∷ 11 ∷ 12 ∷ [])
    ≡                                      (0 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 2 ∷ 2 ∷ 2  ∷ 2  ∷ 3  ∷ [])
  _ = refl
```

An attempt to divide a number by `0` results in a somewhat readable type error (as opposed to an unsolved meta of type `⊥` as before):

      -- zero !=< suc _m_1287 of type ℕ
      -- when checking that the expression promote 0 has type
      -- Promote (suc _m_1287)
      _ : ∀ n -> n `divᵖ` promote 0 ≡ n `divᵖ` promote 0
      _ = λ n -> refl

And we can of course provide a function that tries to parse a natural number as an application of `suc` and either fails (when the number is `0`) or returns a `Promote (suc m)` for some `m`:

```agda
  open import Data.Product

  parseNonZero : ℕ -> Maybe (∃ (Promote ∘ suc))
  parseNonZero  zero   = nothing
  parseNonZero (suc n) = just (n , promote _)
```

Finally, there's one more use case for `promote`. Let's say you have some statically known list of numbers

```agda
  listOfNumbers : List ℕ
  listOfNumbers = 1 ∷ 2 ∷ 3 ∷ 4 ∷ []
```

and you want to extract the second number from the list. Direct pattern matching does not work:

```agda
  secondNumber-direct : ℕ
  secondNumber-direct with listOfNumbers
  ... | _ ∷ two ∷ _ = two
```

Agda colors the matching line, 'cause it wants you to handle the `[]` and `_ ∷ []` cases as well. This is because internally a `with`-abstraction is [translated to an auxiliary function](https://agda.readthedocs.io/en/v2.6.1/language/with-abstraction.html#helper-functions) and the actual pattern matching happens in this function, but at that point we've already generalized the specific list to a variable of type `List ℕ` and lost the information that the original list (that gets passed as an argument to the function) is of a particular spine.

But we can preserve the information that the list is of a particular spine by reflecting that spine at the type level via `Promote`:

```agda
  secondNumber : ℕ
  secondNumber with promote listOfNumbers
  ... | promote (_ ∷ two ∷ _) = two
```

which makes Agda accept the definition.

### Generating type-level data

```agda
module PolyvariadicZipWithNoGo where
  open import Data.Vec.Base as Vec renaming (_∷_ to _∷ᵥ_; [] to []ᵥ)
```

#### Polyvariadic `zipWith`: a no go

Recall this reasoning from the `PolyvariadicZipWith` module:

> We don't need `ToFun` to be invertible when the _spine_ of `As` is provided explicitly:
>
>       _ : zipWithN {As = _ ∷ _ ∷ []} _+_ (1 ∷ᵥ 2 ∷ᵥ 3 ∷ᵥ []ᵥ) (4 ∷ᵥ 5 ∷ᵥ 6 ∷ᵥ []ᵥ) ≡ _
>       _ = refl
>
> as Agda only needs to know the spine of `As` and not the actual types stored in the list in order for `ToFun` to compute (since `ToFun` is defined by pattern matching on the spine of its argument and so the actual elements of the list are computationally irrelevant). `ToFun (_A₁ ∷ _A₂ ∷ []) _B` computes to `_A₁ -> _A₂ -> _B` and unifying that type with `ℕ -> ℕ -> ℕ` is a trivial task.

Can we somehow make that more ergonomic and allow the user to specify the length of the list of types (i.e. just a number) instead of the spine of that list, which is awkward? One option is to still use a list of types, but provide a wrapper that receives a natural number and turns every `suc` into a `∀` binding a type. All types bound this way then get fed one by one to a continuation that assembles them in a list and once `zero` is reached the wrapper calls the original function and passes the collected list of types as an argument. This is what they do in the [Arity-Generic Datatype-Generic Programming](http://www.seas.upenn.edu/~sweirich/papers/aritygen.pdf) paper. However this approach is rather tedious as it introduces a level of indirection that makes it harder to prove things about n-ary functions defined this way (and generally handle them at the type level). It also doesn't play well with universe polymorphism, since in order to handle an n-ary function receiving arguments lying in different universes we need another data structure storing the level of each of the universes and making that structure also a list entails the necessity to provide another wrapper on top of the existing one, which is just a mess.

One idea that comes to mind is to store types in a vector rather than a list. A vector is indexed by its length, so if we explicitly provide the length of a vector, Agda will be able to infer its spine and we won't need to specify it explicitly, right? Not quite.

Having these definitions:

```agda
  ToFunᵥ : ∀ {n} -> Vec Set n -> Set -> Set
  ToFunᵥ  []ᵥ      B = B
  ToFunᵥ (A ∷ᵥ As) B = A -> ToFunᵥ As B

  idNᵥ : ∀ {B} n {As : Vec Set n} -> ToFunᵥ As B -> ToFunᵥ As B
  idNᵥ _ y = y
```

(`idNᵥ` receives an n-ary function and returns it back. `n` specifies how many arguments that function takes) we can check if `As` is inferrable in `idNᵥ`:

```agda
  _ = idNᵥ 2 _+_
```

Nope, it's not. Even though we know that we've specified enough information to determine what `As` is, we see yellow nevertheless. But if the spine of `As` is provided explicitly, then everything type checks:

```agda
  _ = idNᵥ 2 {_ ∷ᵥ _ ∷ᵥ []ᵥ} _+_
```

"But `2` determines that spine!" -- well, yes, but Agda doesn't see that.

We can force Agda to infer the spine of the vector by using a constructor-headed function matching on the vector and returning its length. We then need to equate the result of that function with the actual length provided as the `n` argument. The function looks like this:

```agda
  length-deep : ∀ {n} -> Vec Set n -> ℕ
  length-deep  []ᵥ      = 0
  length-deep (_ ∷ᵥ xs) = suc (length-deep xs)
```

The idea is that since we know the length of the vector (by means of it being provided as an argument) and `length-deep` returns precisely that length, we can make Agda invert the constructor-headed `length-deep` (and thus infer the spine of the vector) by unifying the provided and the computed lengths. However that last unification part is tricky: in Haskell one can just use `~` (see [GHC User's Guide](https://downloads.haskell.org/~ghc/8.8.4/docs/html/users_guide/glasgow_exts.html#equality-constraints)) and that will force unification at the call site (or require the constraint to bubble up), but Agda doesn't seem to have an analogous primitive. We can cook it up from instance arguments though, but first here's an explicit version:

```agda
  idNᵥₑ : ∀ {B} n {As : Vec Set n} -> length-deep As ≡ n -> ToFunᵥ As B -> ToFunᵥ As B
  idNᵥₑ _ _ y = y
```

`idNᵥₑ` does not use the equality proof that it asks for, but the caller has to provide a proof anyway and so `refl` provided as a proof will force unification of `length-deep As` and `n` as Agda has to check that those two terms are actually the same thing (as `refl` claims them to be). And this unification is the only thing we need to get `length-deep` inverted and thus the spine of `As` inferred. We can check that there's indeed no yellow now:

```agda
  _ = idNᵥₑ 2 refl _+_
```

Of course providing `refl` manually is laborious and since it's the only constructor of `_≡_` we can ask Agda to come up with it automatically via instance arguments:

```agda
  idNᵥᵢ : ∀ {B} n {As : Vec Set n} -> {{length-deep As ≡ n}} -> ToFunᵥ As B -> ToFunᵥ As B
  idNᵥᵢ _ y = y
```

It's nearly the same function as the previous one, but now Agda implicitly inserts `refl` instead of asking the user to insert it explicitly. A test:

```agda
  _ = idNᵥᵢ 2 _+_
```

Summarizing, `Vec` is as inference-friendly as `List` (i.e. not very friendly) when it comes to n-ary operations (we could use the same equate-the-expected-length-with-the-provided-one trick for `List` as well). And it's also impossible to store types from different universes in a `Vec`.

But there's a better way to store types.

#### Polyvariadic `zipWith`: eta-based

```agda
module PolyvariadicZipWithEtaBased where
  open import Data.Vec.Base as Vec renaming (_∷_ to _∷ᵥ_; [] to []ᵥ)
```

Here's an inference-friendly data structure:

```agda
  -- Same as `⊤`, but lives in `Set₁` rather than `Set`.
  record ⊤₁ : Set₁ where
    constructor tt₁

  -- This function is constructor-headed.
  Sets : ℕ -> Set₁
  Sets  0      = ⊤₁
  Sets (suc n) = Set × Sets n
```

`Sets n` computes to the `n`-ary product of `Set`s, for example `Sets 3` reduces to `Set × Set × Set × ⊤₁`. I.e. `Sets n` is isomorphic to `Vec Set n`, but since the former computes to a bunch of products and Agda has eta-rules for those, inferring a whole `Sets n` value amounts only to inferring each particular type from that structure, which is not the case for `Vec Set n` as we've seen previously (we know that `n` does determine the spine of a `Vec`, but Agda does not attempt to infer that spine).

Here's a quick test that `Sets` does have better inference properties than `Vec`:

```agda
  -- `n` can be inferred from `Sets n`, hence can be left it implicit.
  -- As before, this function is constructor/argument-headed.
  ToFun : ∀ {n} -> Sets n -> Set -> Set
  ToFun {0}      tt₁     B = B
  ToFun {suc n} (A , As) B = A -> ToFun As B

  idN : ∀ {B} n {As : Sets n} -> ToFun As B -> ToFun As B
  idN _ y = y

  _ = idN 2 _+_
```

Type checks perfectly.

Now we can proceed to defining `Sets`-based polyvariadic `zipWith`. For that we'll neeed a way to map elements of a `Sets` with a function:

```agda
  -- This function is constructor-headed as its `Vec`-based analogue.
  mapSets : ∀ {n} -> (Set -> Set) -> Sets n -> Sets n
  mapSets {0}     F  tt₁     = tt₁
  mapSets {suc n} F (A , As) = F A , mapSets F As
```

And the rest is the same as the previous version except `List` is replaced by `Sets n`:

```agda
  -- As before, even though this function delegates to `ToFun`, it's constructor-headed
  -- (as opposed to the constructor/argument-headed `ToFun`), because the `B` of `ToFun` gets
  -- instantiated with `Vec B m` and so the two clauses of `ToFun` become disjoint (because `Vec`
  -- and `->` are two distinct type constructors).
  ToVecFun : ∀ {n} -> Sets n -> Set -> ℕ -> Set
  ToVecFun As B m = ToFun (mapSets (λ A -> Vec A m) As) (Vec B m)

  -- Here `Sets n` is implicit, so in order to infer `n` from it, Agda needs to be able to infer
  -- `As`. As before, it's not possible to infer `As` from the type of the argument, but is
  -- possible to infer it from the type of the result.
  apN : ∀ {n B m} {As : Sets n} -> Vec (ToFun As B) m -> ToVecFun As B m
  apN {0}     ys = ys
  apN {suc n} fs = λ xs -> apN (zipWith _$_ fs xs)

  zipWithN : ∀ n {B m} {As : Sets n} -> ToFun As B -> ToVecFun As B m
  zipWithN _ f = apN (Vec.replicate f)
```

Note that `n` is an explicit argument in `zipWithN`. Providing `n` explicitly is useful when `As` can't be inferred otherwise. We'll consider such cases, but first let's check that all previous tests still pass. No need to specify `n` when when all arguments and the result are explicitly provided (which makes it possible for Agda to invert `ToVecFun` and infer `As`, as before)

```agda
  _ : zipWithN _ 1 ≡ (1 ∷ᵥ 1 ∷ᵥ 1 ∷ᵥ []ᵥ)
  _ = refl

  _ : zipWithN _ suc (1 ∷ᵥ 2 ∷ᵥ 3 ∷ᵥ []ᵥ) ≡ (2 ∷ᵥ 3 ∷ᵥ 4 ∷ᵥ []ᵥ)
  _ = refl

  _ : zipWithN _ _+_ (1 ∷ᵥ 2 ∷ᵥ 3 ∷ᵥ []ᵥ) (4 ∷ᵥ 5 ∷ᵥ 6 ∷ᵥ []ᵥ) ≡ (5 ∷ᵥ 7 ∷ᵥ 9 ∷ᵥ []ᵥ)
  _ = refl
```

No need to specify `n` when either `B` or the spine of `As` is specified (which makes it possible for Agda to invert `ToFun` and infer `As`, as before)

```agda
  _ : zipWithN _ {B = ℕ} suc (1 ∷ᵥ 2 ∷ᵥ 3 ∷ᵥ []ᵥ) ≡ _
  _ = refl

  _ : zipWithN _ {As = _ , _ , tt₁} _+_ (1 ∷ᵥ 2 ∷ᵥ 3 ∷ᵥ []ᵥ) (4 ∷ᵥ 5 ∷ᵥ 6 ∷ᵥ []ᵥ) ≡ _
  _ = refl
```

I.e. the `Sets`-based `zipWithN` is at least as good inference-wise as its `List`-based counterpart. But now we can also just specify the arity (`n`) of the zipping function without specifying `B` or the spine of `As` as the spine of `As` can be inferred from `n` due to `Sets` being defined by pattern matching on `n` and computing to an `n`-ary product (which is inference-friendly due to the eta-rule of `_×_`):

```agda
  _ : zipWithN 1 suc (1 ∷ᵥ 2 ∷ᵥ 3 ∷ᵥ []ᵥ) ≡ _
  _ = refl

  _ : zipWithN 2 _+_ (1 ∷ᵥ 2 ∷ᵥ 3 ∷ᵥ []ᵥ) (4 ∷ᵥ 5 ∷ᵥ 6 ∷ᵥ []ᵥ) ≡ _
  _ = refl

  _ : zipWithN 2 _+_ (1 ∷ᵥ 2 ∷ᵥ 3 ∷ᵥ []ᵥ) (4 ∷ᵥ 5 ∷ᵥ 6 ∷ᵥ []ᵥ) ≡ _
  _ = refl
```

This approach generalizes to dependently typed functions as well as full universe polymorpism, see [this Stack Overflow question and answer](https://stackoverflow.com/q/29179508/3237465) for an elaborated example. And it's possible to write a general machinery that supports both non-dependent and dependent n-ary functions, see this [blog post](http://effectfully.blogspot.com/2016/04/generic-universe-polymorphic.html).

## Universe levels

```agda
module UniverseLevels where
```

One another thing that Agda's unification engine handles specially is universe levels: there are a bunch of definitional equalities associated with them. Without that universe polymorphism would be nearly unusable. Here are the equalities:

```agda
  _ : ∀ {α} -> lzero ⊔ α ≡ α
  _ = refl

  _ : ∀ {α} -> α ⊔ α ≡ α
  _ = refl

  _ : ∀ {α} -> lsuc α ⊔ α ≡ lsuc α
  _ = refl

  _ : ∀ {α β} -> α ⊔ β ≡ β ⊔ α
  _ = refl

  _ : ∀ {α β γ} -> (α ⊔ β) ⊔ γ ≡ α ⊔ (β ⊔ γ)
  _ = refl

  _ : ∀ {α β} -> lsuc α ⊔ lsuc β ≡ lsuc (α ⊔ β)
  _ = refl
```

A demonstration of how Agda can greatly simplify level expressions using the above identites:

```agda
  _ : ∀ {α β γ} -> lsuc α ⊔ (γ ⊔ lsuc (lsuc β)) ⊔ lzero ⊔ (β ⊔ γ) ≡ lsuc (α ⊔ lsuc β) ⊔ γ
  _ = refl
```

These special rules also give us the ability to define a less-than-or-equal-to relation on levels:

```agda
  _≤ℓ_ : Level -> Level -> Set
  α ≤ℓ β = α ⊔ β ≡ β
```

which in turn allows us to [emulate cumulativity of universes](http://effectfully.blogspot.com/2016/07/cumu.html) in Agda (although there is an experimental option [`--cumulativity`](https://agda.readthedocs.io/en/latest/language/cumulativity.html) that makes the universe hierarchy cumulative).

The list of equalities shown above is not exhaustive. E.g. if during type checking Agda comes up with the following constraint:

      α <= β <= α

it gets solved as `α ≡ β`.

## Epilogue

This tutorial covers a single topic of inference in Agda and doesn't even get into actually hardcore things like higher-order unification, the Miller's pattern fragment and all this kind of stuff that Agda has under the hood. Now imagine how much can be written about all the features available in Agda.

Maybe one day.

## Acknowledgements

Huge "thank you" goes to major contributors:

- Andreas Abel
