
/-
  ### Introduction

  Goals of this lab:
    + learning the basics of Lean and more generally those of interactive theorem proving
    + implementing some of the logical systems you will learn in the course

  Lean is an interactive theorem prover and a functional programming language
  with a rich type systems based on *dependent type theory*.
  Beyond programming, the expressiveness of the type system will allow us to state *theorems* and prove them,
  as we will see in future labs.

-/


/-
  ### LAB 1: Basics of functional programming in Lean
  In future labs, we will mostly focus on theorem proving,
  but we begin with a brief tour of functional programming in Lean.
  *Contents*:
    Basic syntax
    Defining new types
    Inductive types, pattern matching and recursion
    Provably correct programs
-/

/- ## BASIC SYNTAX -/

/-
  We can use the `#check` command to see the type of a term.
-/
#check 7
#check true
#check "hello world"
#check Nat
#check Bool
#check String
#check Nat → String


/-
  Tip: You can hover over unicode symbols to see how to input them.
  For example `→` is typed `\to`.
-/

-- Ignore the following line
set_option autoImplicit false


/-
  ## Defining functions
  We can define functions using the following syntax.
-/
def plus5 (n : Nat) : Nat := n + 5

def hello (name : String) : String := "Hello " ++ name

/-
  Types may be omitted when Lean is able to infer them.
-/
def plus5' (n : Nat) := n + 5

def plus5'' (n) := n + 5

/-
  We can evaluate a function with `#eval`.
-/
#eval plus5 8

/-
  Lambda expressions (also known as lambda abstractions, anonymous functions, closures) are first-class objects in Lean.
  Below, `fun n : Nat => n + 5` is a term representing the function that maps `n` to `n + 5`.
  We could have also defined our `plus5` function to simply be this lambda expression.
-/
#check fun n : Nat => n + 5

def plus5''' := fun n : Nat => n + 5

/-
  Note that plus5, plus5', plus5'' and plus5''' are all the *same* definition,
  just written in different notations.
-/

/-
  ## Currying.
  Functions with multiple arguments are usually *curried*.
  Consider the addition on natural numbers, `Nat.add`, which should take two `Nat`s and return a `Nat`.
  Its type is `Nat → Nat → Nat`, which is the same as `Nat → (Nat → Nat)` (i.e. `→` is right associative).
  `Nat.add` takes a natural number `n` and returns a function `Nat.add n : Nat → Nat` (the function adding `n` to its argument).
  `Nat.add n` is also called a *partial application* of `Nat.add`.
  If we further apply it to an `n : Nat`, we get `(Nat.add n) m : Nat` (the sum between `n` and `m`).
  Function application is left associative, so we simply write `Nat.add n m`.
-/

-- Nat → (Nat → Nat)
#check Nat.add
#check Nat.add 5
#check Nat.add 5 7
#eval Nat.add 5 7

/-
  Even one more way to write `plus5`, as a partial application of `Nat.add` to `5`:
-/
def plus5'''' := Nat.add 5


/-
  To see some more interesting example, let's introduce the type `List α` of
  lists of elements of type `α`
-/
#check List
#check [1, 2, 3]
#check ["a", "b", "c"]

/-
  We will come back to lists later.
  For now, we can use them through the essential functional programming operations:
  `List.map f [x₁, x₂, ..., xₙ] = [f x₁, f x₂, ..., f xₙ]`
  `List.filter p xs = [xᵢ ∈ xs | p xs = true]`
  `List.foldl op init [x₁, x₂, ... xₙ] = (...((init op x₁) op x₂ ... ) ... op xₙ`
  Use `#check` to see the actual types of these.
-/

def sumOfSquares (numbers : List Nat) : Nat :=
  List.foldl (fun n m => n + m) 0 (List.map (fun n => n * n) numbers)

/- There is also the `method` syntax, where instead of `List.map f numbers` we can write `numbers.map f`,
   (this is because `map` is in the `List` namespace)
-/
def sumOfSquares' (numbers : List Nat) : Nat :=
  (numbers.map (fun n => n * n)).foldl (fun n m => n + m) 0

/-
  **Exercise**: write a function which computes the product of all non-zero
  numbers in a list.
-/
def prodNonZero (numbers : List Nat) : Nat := sorry



/-
  ## DEFINING NEW TYPES
  We've seen some builtin types, like `Nat` or `String`.
  Defining new types is one of the most important aspects of working in Lean,
  and next we will see some of ways of doing this.
-/

/-
  A *structure*, like in most programming language (called "record", etc. in other languages),
  is a tuple made of a number of named fields of potentially different types.
-/
structure Student where
  name : String
  group : Nat
  grade : Nat

#check Student

def namesOfStudentsWhoPassed (students : List Student) : List String :=
  students.filter (fun student => student.grade > 5) |>.map Student.name

/-
  **Exercise**:
    Uncomment the next `def` and define a term `me` of type `Student` as below, by filling the underscores.
    In Lean, you can always place an underscore where a term is expected,
    and the infoview will show you its expected type if you move the carret over it.
-/
def me : Student := sorry

/-
  We can access the fields of structure using dot notations,
  like in the following example (also called projection notation).
-/
def personToString : Student → String :=
  fun student => student.name ++ " " ++ (toString student.group)


/-
  ## INDUCTIVE TYPES, PATTERN MATCHING AND RECURSION
  Inductive types (related to algebraic datatypes in other languages)
  are defined by specifying all the ways their terms can be constructed.
  The ways a term of an inductive type can, by definition,
  be constructed are called *constructors* and are functions whose return type has to be the inductive type being defined.
-/

namespace Hidden

  /-
    Again in the `Hidden` namespace to avoid naming conflicts,
    below is the definition of the `Nat` type we used earlier.
  -/

  inductive Nat where
  | zero : Nat
  | succ : Nat → Nat

  -- zero : Nat
  -- one = succ zero : Nat
  -- two = succ (succ zero) : Nat

  /-
    The constructors are `zero` and `succ`.
    This means that terms of type `Nat` are all either `zero` or of the form `succ n` for some `n : Nat`.
  -/

end Hidden

/-
  The constructors of `Nat` are not in the global namespace; their full names are `Nat.zero` and `Nat.succ`.
  We open the `Nat` namespace to have them available.
-/
open Nat

/-
  Functions on inductive types are defined using *recursion* and *pattern matching*.
-/
def isZero (n : Nat) : Bool :=
  match n with
  | zero => true
  | succ m => false


/-
  Definitions by pattern matching can also be recursive.
-/
def nthSum (n : Nat) : Nat :=
  match n with
  | zero => zero
  | succ n => (succ n) + nthSum n

/-
  There are builtin notations like `0` for `zero` and `n + 1` for `succ n` but they are the same thing under the hood.
-/
def nthSum' (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => (n + 1) + nthSum n

/-
  Warning!
  By default, all functions need to terminate.
  This is important for the logical consistency of the system.
  If it can not tell that function terminate, Lean will give an error.
  This may happen when the function indeed does not terminate (as in the example below),
  or when it does terminate but Lean cannot figure out by itself how to prove termination.
-/

def nonterminating (n : Nat) : Nat :=
  nonterminating (n + 1)

/-
  **Exercise**:
    Using pattern matching, define the `factorial` function, computing the factorial of a natural number.
-/
def factorial (n : Nat) : Nat := sorry

/-
  We can also prove theorems in Lean. This is not the subject of today's lab,
  but if your definition is correct the line below will not give an error
  and will be a formal proof of the fact that `factorial 5 = 120`.
-/
example : factorial 5 = 120 := rfl


/-
  Another common type in a functional programming, builtin in Lean, is the `Option` type, which is parametric in a type.
  Given a type `α`, `Option α` has two constructors, `none : Option α` and `some : α → Option α`.
  A term of type `Option α` is either `none` or of the form `some a`, for some `a : α`.
  `Option` is commonly used to indicate error values, with `none` representing an error
  and `some a` a valid value.
-/

namespace Hidden

  inductive Option (α : Type) where
  | none : Option α
  | some : α → Option α

end Hidden

/-
  Subtraction on natural numbers is ill-behaved, in the sense that one cannot meaningfully subtract m from n when `n < m`.
  Lean's builtin subtraction returns `0` for `n - m` when `n < m`.
  **Exercise**:
    Define the `sub?` function below, return the right results of `n - m` when `n ≥ m` and an error otherwise.
  Hint:
    Use the `if ... then ... else ...` expression.
-/


def sub? (n m : Nat) : Option Nat := sorry

-- sub? 5 3 = some 2
-- sub? 2 7 = none




/-
  **Exercise**:
    Define, without using the builtin `Nat.add` or `+`, the `myAdd` function below, adding two natural numbers.
-/


def myAdd (n m : Nat) : Nat := sorry


/-
  Like with `factorial`, if your definition is correct, the example below should give no errors.
-/
example : myAdd 28 49 = 77 := rfl


/-
  Depending on the way you defined `myAdd`, one of the `theorem`s below will probably be correct,
  but the other will still give an error,
  so you will have formally proved either that `0 + n = n` or that `n + 0 = n` for all natural numbers `n`.
  Try to guess which one will succeed and then uncomment both theorems to see what happens.
-/
-- 0 + n = n
-- theorem zero_add : ∀ n : Nat, myAdd 0 n = n := fun n => rfl

-- n + 0 = n
-- theorem add_zero : ∀ n : Nat, myAdd n 0 = n := fun n => rfl


namespace Hidden

  inductive List (α : Type) where
  | nil : List α
  | cons : α → List α → List α

  /-
    Lists are defined as 'cons lists'.
    That is, by definition, a list is either empty, or of the form:
    "an element (called head) prepended (called consed) to another list (called tail)".
  -/

  -- ["a", "b", "c"]                 = cons a (cons b (cons c nil))
  -- or with the nicer notation      = a :: b :: c :: []
end Hidden

def List.myLength {α : Type} (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | h :: t => List.myLength t + 1

def List.myMap {α β : Type} (f : α → β) (as : List α) : List β :=
  match as with
  | [] => []
  | h :: t => (f h) :: (List.myMap f t)

/- **Exercise**: define by recursion the `sum` function which computes the sum of a list -/
def List.mySum (xs : List Nat) : Nat := sorry

/- **Exercise**: define by recursion the `filter` function from before -/
def List.myFilter {α : Type} (p : α → Bool) (xs : List α) : List α := sorry



/-
  Let's see a slightly more 'real-world' example of using `Option` combined with `List`.
-/
def sumStringNumbers (numbers : List String) : Nat :=
  let numbers : List (Option Nat) := numbers.map String.toNat? -- some strings may not be numbers!
  let numbers : List (Option Nat) := numbers.filter Option.isSome
  let numbers : List Nat := numbers.map Option.get!
  numbers.sum

/-
  As a side note, you can even do for loops!
  If you ever used Haskell, you are hopefully shocked by this,
  but there is in reality no mutability, it's just `do` notation magic.
  You can do `#print sumList` to see what it desugars to (don't worry about understanding it).

  We won't come back to this style of writing.
-/
def sumStringNumbers' (numbers : List String) : Nat := Id.run do -- ignore this
  let mut sum := 0
  for number in numbers do
    -- fancy Rust-like `if let`
    if let some number := number.toNat? then
      sum := sum + number
  return sum


/- ## PROVABLY CORRECT PROGRAMS -/

/-
  In `sumStringNumbers`, we ran into the situation that parsing strings as nats
  may not always succeed.
  What we did there, was to filter only those items for which it did (those satisfying `isSome`),
  and then extract the value wrapped inside `Option`, using `Option.get!`.
  But `Option.get!` is forceful: what could `Option.get! none` return?
  Uncomment the line below.
-/
-- #eval Option.get! (none : Option Nat)


/-
  Indeed, it cannot return anything; there is no way to write a generic function of type
  `Option α → α` since you cannot produce an `α` from `none`.
  `Option.get!` throws a runtime panic.
  Of course, it might not hard to convince ourselves that this situation will not occur in our
  `sumStringNumbers`, but is there a better way?
-/

/-
  What if we were to implement a function which returns the element at a given index from a list?
  A first idea would be `List.atIndex` below.
  Note that we encounter a problem: what if there is no element at the given index,
  i.e. the index is out of bounds.
  We could throw a runtime panic.
-/
def List.atIndex! {α : Type} [Inhabited α] (xs : List α) (index : Nat) : α :=
  match xs with
  -- if we reached index 0, so we just return the first element,
  -- otherwise we keep going in the remainder of the list
  | x :: xs => if index = 0 then x else List.atIndex! xs (index - 1)
  -- we went over the entire list and we still haven't reached index `0`,
  -- therefore the index out of bounds.
  -- What do we do? PANIC!
  | [] => panic! "Index out of bounds"

#eval ["a", "b", "c"].atIndex! 2
#eval ["a", "b", "c"].atIndex! 4

/-
  A more type-safe alternative would be to return an `Option Nat` instead,
  returning `none` if the index is out of bounds.
-/
def List.atIndex? {α : Type} (xs : List α) (index : Nat) : Option α :=
  match xs with
  -- if we reached index 0, so we just return the first element,
  -- otherwise we keep going in the remainder of the list
  | x :: xs => if index = 0 then some x else List.atIndex? xs (index - 1)
  -- we went over the entire list and we still haven't reached index `0`,
  -- therefore the index out of bounds.
  -- Stop panicking, just return `none`
  | [] => none

#eval ["a", "b", "c"].atIndex? 2
#eval ["a", "b", "c"].atIndex? 4


/-
  These approaches can be encountered in many modern languages.
  But in Lean, we may provide yet another solution:
    we can require a *proof* that index is within bounds.
-/
def List.atIndex {α : Type} (xs : List α) (index : Nat) (proof : index < xs.length) : α :=
  match xs, index with
  -- Lean understands that this case is now impossible
  -- because we would have a hypothesis that `index < xs.length = 0`, which is false
  -- for any natural number.
  -- The bad case is provably not reachable, guaranteed by the `proof` argument.
  | [], _ => by contradiction
  -- nothing new
  | x :: xs, 0 => x
  -- for the recursive call, we need to pass a proof that
  -- `index + 1 < (x :: xs).length + 1`, for which we appeal to the standard library
  | x :: xs, index + 1 => xs.atIndex index (Nat.le_of_succ_le_succ proof)

#eval ["a", "b", "c"].atIndex 2 (by simp)
-- the last argument is a formal proof of the condition, we ignore for now how this works
#eval ["a", "b", "c"].atIndex 4 (by simp)
/-
  Error: the condition is false; we cannot prove it and therefore cannot call the function
  Important! This is not, in general, a simple check that `2 < 4`,
  but a *mathematical proof* that can be given for symbolic variables.

  Note: The functions we implemented actually mimic the Lean List API:
  `xs[i]`, `xs[i]!`, and `xs[i]?`
-/


/-
  Let's see another example: lists parametrized by length (commonly known as vectors in this kind of languages).
  `Vec α n` defined below is the type of lists of elements of type `α` and of length `n`.
  We define them as pairs between a list and a proof that the list indeed has that length.
-/
structure Vec (α : Type) (n : Nat) where
  content : List α
  proof : content.length = n

/-
  In order to actually construct an element of this type, as with all structures,
  we need to give values for the fields: a list, and a proof that it has the stated length
-/
def someRandomVec : Vec String 5 :=
  { content := ["hello", "world", "has", "length", "5"], proof := by simp }

def someVecOfWrongLength : Vec String 10:= -- type
  { content := ["this", "doesn't", "have", "10", "words"], proof := by simp }
-- Error: this cannot typed as `Vec String 10`

/-
  General append function between vectors.
  Note how in order to write this function we need to *prove* that:
  for any lists `x` and `y` the length of their concatenation is the sum of their lengths.
-/
def Vec.append {α : Type} {n m : Nat} (x : Vec α n) (y : Vec α m) : Vec α (n + m) :=
  {
    -- this is the returned list
    content := x.content ++ y.content,
    -- this is the proof, you don't need to understand it now;
    -- we essentially apply the `List.length_append` lemma from the standard library;
    -- but feel free to step through the proof and to look at the lemma we used
    proof := match x, y with
      | ⟨xcontent, xproof⟩, ⟨ycontent, yproof⟩ => by
        dsimp
        rw [← xproof]
        rw [← yproof]
        exact List.length_append

  }


/-
  `Vec.repeat n a returns the vector [a, a, ..., a] (n times)..
  Note how we need to prove that the length is correct.
  We could moreover prove that `∀ x, x ∈ Vec.repeat n a, x = a`,
  which would looks like a complete specification of the function
-/
def Vec.repeat {α : Type} (n : Nat) (a : α) : Vec α n :=
  {
    content := List.range n |>.map (fun _ => a),
    proof := by
      rw [List.length_map]
      rw [List.length_range]
  }



/- ## EXTRA: BINARY TREES -/

inductive BTree (α : Type) where
| node : α → BTree α → BTree α → BTree α
| empty : BTree α
deriving Repr -- this is just so that we may print it


def someRandomTree : BTree Nat :=
  .node 1
    (.node 2
      (.node 3
        (.node 4 .empty .empty)
        (.node 5 .empty .empty)
      )
      .empty
    )
    (.node 6
      (.node 7 .empty .empty)
      (.node 9 .empty .empty)
    )

/-
  **Exercise**: define a function that determines whether a binary tree contains a certain value in one of its nodes
-/
def BTree.contains {α : Type} (tree : BTree α) (value : α) : Bool := sorry

/-
  **Exercise**: define a function that computes the depth of a binary tree
-/
def BTree.depth {α : Type} (tree : BTree α) : Nat := sorry


/-
  **Exercise**: Implement a "pretty printing function" for binary trees that
  prints the nodes (into a String) on new lines, displaying the tree structure
  by levels of indentation
-/
#eval someRandomTree -- ugly
/-
  We want to print it as:
1
  2
      3
          4
          5
  6
      7
      9
-/


#check Nat.repeat


/-
  `[ToString α]` is a *typeclass parameter*.
  The only you need to know about it is that it allows you to call the function
  `toString` on an term of type `α`.
-/
def BTree.prettyPrint {α : Type} [ToString α] (indentLevel : Nat := 0) (tree : BTree α) : String := sorry

/- You won't see the proper output by just `#eval` (it will show `\n` characters instead of new lines)
   Test your function instead by uncommenting the lines below.
-/
-- -- The famous `IO` monad, don't think about it, we just use it for properly printing the output
-- def runPrintBTree : IO Unit := do
--   IO.println someRandomTree.prettyPrint

-- #eval runPrintBTree
