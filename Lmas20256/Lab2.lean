
/- ### LAB 2: Propositional logic -/

open Classical

set_option autoImplicit false

/-
  We will now begin to see Lean also as an interactive theorem prover,
  and we will slowly build our way up towards proving more and more complex theorems.
  In this lab, we start with the most elementary of all, propositional logic.

  Let us first introduce a new type, called `Prop`, which is the type of propositions.
  We won't yet concern ourselves with what this means (it actually doesn't mean that much).
  Examples of propositions are equalities, like the ones we've seen in Lab1.
-/
#check Prop
#check 5 = 3
#check 5 = 5
#check 5 ≠ 3

-- Fermat's last theorem is another `Prop`
#check ∀ n > 2, ∀ a > 0, ∀ b > 0, ∀ c > 0, a^n + b^n ≠ c^n

/-
  The idea to see a programming language as a logical system
  is know as *propositions as types* or the *Curry-Howard correspondence https://en.wikipedia.org/wiki/Curry-Howard_correspondence*
  The simple, yet powerful observation is that one can see the types of a programming language
  as propositions, and the programs of that type as *proofs* of the corresponding proposition.
  You might ask "ok, let's say I have a type `A`. What is then its corresponding proposition".
  It is simply `A` itself, there's nothing behind it, it is just a matter of how we think of it.

  In practice, for Lean, this manifests itself as follows.
  A proposition is itself a type. If `p : Prop`, we can speak of terms `h` of type `p`.
  We interpret an `h : p` as a *proof* of `p`, so we could say that `p` is the type of all its proofs (but this is just a conceptualization).
  Proving a proposition `p` therefore means providing some term of type `p` (showing the nonemptiness of the type).
  For instance, `rfl` from Lab1 is such term of type `x = x`, and therefore a proof that `x = x`.
-/
#check (rfl : 5 = 5)

/-

  Recall some of the standard logical connectives of propositional logic:
    - implication
    - conjunction ("and")
    - disjunction ("or")
    - negation

  Let's see what they look like in Lean.

  Implication is `p → q`, that is, it is simply the function type, no further definition needed.
  The intuition is that a proof `h : p → q` is a function that transforms proofs of `p` into proofs of `q`.
-/

/-
  Using `variable`, we can consider in this section some arbitrary propositions `p`, `q` and `r`,
  as if we said *let p, q and r be any propositions*.
-/

variable (p q r : Prop)

#check p → q

/-
  `And` is defined as follows.
  structure And (p q : Prop) where
    left : p
    right : q
  The intuition is that a proof of `And p q` is, by definition, simply a pair of a proof of `p` and a proof of `q`.
  The notation `p ∧ q` is used in practice for `And p q`.
-/
#check And
#print And
#check And p q
#check And.intro -- the constructor of the type
#check And.left
#check And.right

/-
  ## Or
  inductive Or (p q : Prop) where
  | inl : p → Or p q
  | inr : q → Or p q
  The intuition is that a proof of `Or p q` is, by definition, either a proof of `p` or a proof of `q`.
  The notation `p ∨ q` is used in practice for `Or p q`.
-/
#check Or
#check Or p q
#check Or.inl
#check Or.inr

/-
  There is also a proposition called `False`, which has no proof.
  The definition is as an inducitve type with no constrcutors.
-/
#print False
#check False.elim -- recall the principle that from `False` we can prove anything

/-
  ## Not
  Negation is defined by `Not p := p → False`.
  That is, a proof of `Not p` is a function which transforms proofs of `p` into proofs of `False`,
  which cannot exist, and therefore neither can proofs of `p`.
  The notation `¬p` is used in practice.
-/
#check Not
#check Not p
#print Not

/-
  Therefore, strictly speaking, we don't need to know anything new in order to prove propositional theorems.
  It's a matter of knowing how the types are defined, and then it's just functional programming with them.
-/

-- all we have to do is write a well-typed function (you can think of `theorem` as being the same as `def`)
theorem foo : p ∨ (q → r) → (¬p ∧ q → r) :=
  fun h => match h with
  | Or.inl hp => fun h' =>
    let h_absurd : False := h'.left hp
    False.elim h_absurd
  | Or.inr hqr => fun h' => hqr h'.right

-- The reflexivity of implication is actually just the identity function
theorem imp_relf: p → p := fun h => h



/-
  **Exercise**: Prove the following:
-/
theorem modus_ponens : (p → q) → p → q := sorry

theorem and_commutative : p ∧ q → q ∧ p := sorry

theorem or_commutatitve : p ∨ q → q ∨ p := sorry

/-
  Bonus (only if you happen to know Haskell, otherwise ignore): open ghci and check the type of the `$` operator.
  Do you see the connection?

  Actually, all the proofs of this Lab could be carried out in the same sense in Haskell or any language
  that similarly allows for generic functions (though such languages will likely be inconsistent as logical system because of unbounded recursion).

  In the next lab, we will see how the expressiveness of Lean allows us to go far beyond propositional logic.
-/


/-
  In principle, any theorem can be proved by simply writing a function of the appropriate type
  (the type of the theorem's statement), like above.
  This can quickly get unwieldy for complex proofs, so Lean offers a different embedded language called *tactic mode*.
  At any point in a proof, there is a *proof state* composed of a number of hypotheses and a number of goals needing to be proved.
  A tactic changes the proof state, until no more goals are left, and the theorem is proved.
-/

theorem modus_ponens_tactics : p → (p → q) → q := by --we enter tactic mode with `by`. Note the infoview on the right.
  -- we need to prove an implication. We first suppose its premise.
  intros hp -- suppose a proof of `p → q` exists, and call it `h_imp_q`
            -- note the change in the proof state
  -- we still have an implication to prove, so we again assume its premise.
  intros hpq
  -- we need to prove `q`. We can obtain `q` from the conclusion of `hpq` if we provide the right premise to it
  apply hpq -- the goal would follow from `hpq` if we proved its required conclusion. Note the goal change
  -- the goal is now just an assumption
  assumption

theorem and_commutative_tactics : p ∧ q → q ∧ p := by --we enter tactic mode with `by`. Note the infoview on the right.
  -- we need to prove an implication. We first suppose its premise
  intros hpq -- suppose a proof of `p wedge q` exists, and call it `hpq`
             -- note the change in the proof state
  -- we know p ∧ q, and from it can obtain both `p` and `q` by
  rcases hpq with ⟨hp, hq⟩
  -- we need to prove `q ∧ p`. We know this can be proved from `And.intro`
  apply And.intro
  -- in order to apply `And.intro` we need to to have both a proof of `p` and a proof of `q`
  -- Lean produced two new goals, both of which are trivial two solve
  case left => assumption
  case right => assumption

theorem or_commutatitve_tactics : p ∨ q → q ∨ p := by
  -- we need to prove an implication. We first suppose its premise
  intros hpq
  -- we have a proof of `p ∨ q` as hypothesis. This means that at least one of them is true,
  -- and we consider both cases. Note that the proof has now split into two subproofs.
  cases hpq
  -- the case when `p` is true, which is called `inl` (this is a fixed name); we name `hp` the hypothesis for this case
  case inl hp =>
    apply Or.inr
    assumption
  -- the case when `q` is true, which is called `inr` (this is a fixed name); we name `hq` the hypothesis for this case
  case inr hq =>
    apply Or.inl
    assumption

/-
  The following tactic cheat sheet might be useful `https://github.com/madvorak/lean4-cheatsheet/blob/main/lean-tactics.pdf`
  Usually, tactic mode and term mode may be freely combined.
  For instance, a more concise version of the above may be:
-/
theorem and_comm_tactics' : p ∧ q → q ∧ p := by
  intros hpq
  cases hpq with | intro hp hq =>
  exact And.intro hq hp -- `exact e` closes the proof if `e` has exactly the required type

/-
  **Exercise**: Prove the following. `example` is just a `theorem` without a name (we couldn't be bothered to invent names for all of these)
-/
example : p ∧ q → q ∨ p := sorry


example : p → (¬p) → False := sorry


example : p → (¬p) → q := sorry


example : p ∧ (¬p) → q := sorry

-- you can also use the `contradiction` tactic to automatically discharge the goal when you have both a statement and its negation as hypotheses
example : p → ¬¬p := sorry



/-
  There is one more construct we need introduce before having the full propositional logic:
  the law of excludded middle `p ∨ ¬p`.  While all the other propositional principles
  derive naturally from the definitions of the logical connectives, this one has to be introduced essentially as an axiom:
-/
#check em


/-
  In order to use it, we can simply to `cases` on it, since it is an `or`.
  But there is a tactic called `by_cases` which does this automatically:
  `by_cases h : p` produces two subproofs, asking us to prove our goal assuming that `p` is true,
  and assuming that `¬p` is true in the other case.
  The following is a standard example of a theorem that cannot be proved without excludded middle
  (they are in fact equivalent)
  **Exercise**:
-/
example : ¬¬p → p := sorry

/-
  (Use `Iff.intro` to split the equivalence into two implications).
  **Exercise**:
-/
example : (p ∧ q → r) ↔ (p → q → r) := sorry

example : (p → q) ↔ (¬q → ¬p) := sorry

example : (p → q) ↔ (¬p ∨ q) := sorry

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry

example : ¬(p ∧ q) ↔ ¬p ∨ ¬q := sorry

-- This is called `Peirce's law`, and is yet another principle equivalent to the law of excludded middle
-- and can be seen as the Curry-Howard counterpart of the `call/cc` construct https://en.wikipedia.org/wiki/Call-with-current-continuation
-- This has always seemed rather mysterious to me, but maybe you understand it better.
example : (((p → q) → p) → p) := sorry
