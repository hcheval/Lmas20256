

/- ### LAB 4: Rewriting, induction -/

/-
  ## Rewriting

  If we know that two expressions are equal, say in the form of a hypothesis
  `h : a = b`, common sense says that we should be able to replace `a`
  with `b` in any context and get the same thing.

  This is done by the `rewrite` tactic:
    given `h : a = b`
    and a goal containing `a`, let's say of the form `Goal(a)`,
    `rewrite [h]` will transform the goal into `Goal(b)`
-/

example (a b c d : Nat) : a = b → c = d → a + c = b + d := by
  intros h₁ h₂
  rewrite [h₁] -- transform ⊢ a + c = b + d into ⊢ b + c = b + d
  rewrite [h₂] -- transform ⊢ b + c = b + d into ⊢ b + d = b + d
  rfl -- the two sides are now identical

example (a b c d : Nat) : a = b → c = d → a + c = b + d := by
  intros h₁ h₂
  rewrite [h₁, h₂] -- rewrite actually can take a list of hypothesis to be rewritten successively
  rfl -- the two sides are now identical

/-
  `rewrite [h]` performs a *left-to-right* rewrite using `h`,
  meaning that if `h : a = b`, it rewrites `a` into `b`.
  You can use `rewrite [← h]` in order to rewrite from right to left,
  from `b` into `a`.
-/
example (a b : Nat) : a = b → a > 0 → b > 0 := by
  intros h₁ h₂
  -- we want to rewrite the goal `⊢ b > 0` into `⊢ a > 0` using `h : a = b`
  -- so we need to rewrite from right to left
  rewrite [← h₁]
  exact h₂


/-
  Of course, if `a` and `b` are equal, then we can replace them also in any hypothesis,
  not just in the goal. This is done with `rewrite [h] at h'`
-/
#check Nat.le_of_lt
example (a b : Nat) (h₁ : a = b) (h₂ : 0 < a) : 0 ≤ b := by
  rewrite [h₁] at h₂
  exact Nat.le_of_lt h₂

/-
  Rewriting works not only on equalities, but also on equivalences (i.e. `Iff` or `↔`).
  For example, to prove the `example` below, we can rewrite along
  `Classical.not_not` which is a theorem stating that `∀ p : Prop, ¬¬p ↔ p`.
-/

#check Classical.not_not
example (p q : Prop) : ¬¬p ∧ ¬¬q → p ∧ q := by
  intros h
  rewrite [Classical.not_not] at h
  rewrite [Classical.not_not] at h
  exact h


/- *Exercse:* Prove the following equivalent characterization of `0` -/
example (a : Nat) : (∀ x : Nat, x + a = x) ↔ a = 0 := sorry



/-
  Sometimes you need to specify which subexpression to rewrite
  out of multiple possibilities. By default, `rewrite` will apply to the first match.
-/
#check Nat.add_comm
example (a b c : Nat) : (a + b) * (a + c) = (b + a) * (c + a) := by
  rewrite [Nat.add_comm] -- `a + b` ----> `b + a`
  /-
    If we do `rewrite [Nat.add_comm]` it will rewrite `b + a` back into `a + b`, not what we want
  -/
  rewrite [Nat.add_comm a c]
  rfl



/-
  *Exercise:*  Prove the following standard equality about `(a + b) ^ 2` using rewrites.
  The following standard library lemmas should suffice.
-/
#check Nat.pow_two
#check Nat.mul_add
#check Nat.add_mul
#check Nat.mul_comm
#check Nat.add_assoc
#check Nat.two_mul
#check Nat.mul_assoc


example (a b : Nat) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := sorry






/-
  ## Induction

  The `induction` tactic performs induction.
  There are many versions to consider, but for now we will consider the familiar
  induction on natural numbers.

  Within a proof with goal `p n` (for `p : Nat → Prop` and `n : Nat`),
  doing `induction n` will produce two subgoals:
    - the base case: prove `p 0`
    - the inductive case: prove `p (n + 1)` with an additional hypothesis asserting `p n` (the induction hypothesis)
-/


theorem zero_add : ∀ n : Nat, 0 + n = n := by
  intros n
  induction n
  case zero =>
    -- base case; this is trivial by computation
    rfl
  case succ n' ih =>
    -- inductive case: assume in `ih` that the claim holds for `n'` and prove it for `succ n'` (a.k.a `n' + 1`)
    rewrite [Nat.add_succ]
    rewrite [ih]
    rfl

/- *Exercise:* Prove the following mimicking the proof of `zero_add`
  Explore the standard library for a lemma to replace the previous use of `Nat.add_succ`.
-/

example : ∀ n : Nat, 1 * n = n := sorry

namespace Hidden

  /-
    In order to avoid the temptation of cheating with the standard library,
    let us roll our own definition of natural numbers and addition in the following,
    just like we did in Lab 1.
  -/

  inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat


  def MyNat.add (n m : MyNat) : MyNat :=
    match m with
    | zero => n
    | succ m' => succ (add n m')

  open MyNat

  -- The following are trivial definitional lemmas you can use in order to unfold the definition
  theorem add_zero : ∀ n : MyNat, add n zero = n := by intros _; rfl

  theorem add_succ : ∀ n m : MyNat, add n (succ m) = succ (add n m) := by intros _ _; rfl

  /- *Exercise:* Prove the following -/
  theorem zero_add : ∀ n : MyNat, add zero n = n := sorry

  theorem succ_add : ∀ n m : MyNat, add (succ n) m = succ (add n m) := sorry

  theorem add_comm : ∀ n m : MyNat, add n m = add m n := sorry

  theorem add_assoc : ∀ n m k : MyNat, add (add n m) k = add n (add m k) := sorry

end Hidden




/-
  Recall that propositions are types and proofs are functions.
  In lab 2, we have seen this briefly in relation to propositional logic,
  where we proved some theorems by simply writing functions of the desired type,
  rather than using tactic blocks with `by`.

  The natural question is what is the functional programming counterpart of induction?
  The answer is recursion.
  If we want to prove that `∀ n : Nat, p n` (for some property `p : Nat → Prop`),
  what we need to do is write a function of this type, i.e.
  a function `f` which maps any `n : Nat` to a proof of `p n`
  (note how this return type depends on `n`, making this a dependent function type).
  Proving this by induction simply means defining `f` by recursion and pattern matching.
  The induction hypothesis is simply the result of the recursive call:
  when we prove the claim for `n + 1` (i.e. define the `f` for `n + 1`),
  we call the function recursively on `n` to obtain the result `f n`
  and use it for the case of `n + 1`.

  This is not just a metaphor, in Lean recursion and induction are the exact same thing under the hood.

  Below is a version of `zero_add` using recursion and pattern matching.
  We still open `by` blocks in each branch of the `match`, the point is just
  that the overall structure of induction is implemented with recursion.
-/

theorem zero_add_rec : ∀ n : Nat, 0 + n = n :=
  fun n => match n with
  | Nat.zero =>
    by rfl
  | Nat.succ n' =>
    let ih := zero_add n'
    by
      rewrite [Nat.add_succ]
      rewrite [ih]
      rfl





/-
  Crucially, induction is no way limited or special to the natural numbers,
  but it is inherently tied to the general notion of inductive types.
  We can do induction on any variable of an inductive type, with cases
  corresponding to its constructors.

  For example, recall that lists are also an inductive type:
  inductive List (α : Type) where
  | nil : List α
  | cons : α → List α → List α

  To prove by induction on `xs` that `∀ xs : List α, p xs`, we need
    - to prove `p []` (the base case)
    - to prove, from an induction hypothesis `ih : p t`,
      that `p (h :: t)` holds, for any head `h`.
-/

section

  variable {α β : Type}

  /-
    Let's prove that mapping a function on a list preserves the length,
    (the `List.length_map` theorem from the standard library)
  -/
  example (f : α → β) : ∀ xs : List α, (xs.map f).length = xs.length := by
    intros xs
    induction xs
    case nil =>
      -- base case: prove that ([].map f).length = [].length
      -- this is trivial (could be done simply by `rfl` but we unfold the definitions step by step for pedagogical reasons)
      rewrite [List.map_nil]
      rewrite [List.length_nil]
      rewrite [List.length_nil]
      rfl
    case cons h t ih =>
      -- induction case: prove that ((h :: t).map f).length = (h :: t).length
      -- assuming that `ih : (t.map f).length = t.length

      -- The proof is almost immediate if we just recall the definitions of the functions.
      -- It should hold by definition that `(h :: t).map f = f h :: t.map f`
      -- and that `(h :: t).length = t.length + 1`
      -- and there are lemmas asserting exactly this (whose names are reasonably easy to guess, you should try to get to used to the naming conventions)
      rewrite [List.map_cons]
      rewrite [List.length_cons]
      rewrite [ih]
      rfl



  -- recall the list reversal function, which we can implement as follows
  def List.myReverse (xs : List α) : List α :=
    match xs with
    | [] => []
    | x :: xs => xs.myReverse ++ [x]

  /-
    We will need the following trivial lemmas in order to easily compute our function in the subsequent proofs.
  -/

  theorem List.myReverse_nil : ([] : List α).myReverse = [] := by rfl

  theorem List.myReverse_cons {h : α} {t : List α} :
    (h :: t).myReverse = t.myReverse ++ [h] := by rfl

  /- *Exercise:* Prove the following -/
  -- Relevant lemmas for the first one:
  #check List.length_append
  #check List.length_cons
  #check List.length_nil
  -- For the other ones, try to explore the standard library to find the necessary lemmas

  example : ∀ xs : List α, xs.myReverse.length = xs.length := sorry

/- *Exercise:* Prove the following -/
  example : ∀ xs ys : List α, (xs ++ ys).myReverse = ys.myReverse ++ xs.myReverse := sorry

/- *Exercise:* Prove the following -/
  example : ∀ xs : List α, xs.myReverse.myReverse = xs := sorry


end
