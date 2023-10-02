import LoVe.LoVelib

/- # FPV Homework 4: Functional Programming

Homework must be done in accordance with the course policies on collaboration
and academic integrity.

Replace the placeholders (e.g., `:= sorry`) with your solutions. When you are
finished, submit *only* this file to the appropriate Gradescope assignment.
Remember that the autograder does not determine your final grade. -/


namespace LoVe


/- ## Question 1 (4 points): Dot Notation 

After defining structures and inductive types, functions that operate on these
types can be accessed through the dot notation. This is syntactically similar to 
methods in Object-Oriented Programming. This question will guide you through
how to use it. 

First, we define a structure: -/

section

structure Point (α : Type) where
  x : α
  y : α
  deriving Repr   -- For display in `#eval`

/- It comes with some existing functions: -/

#check Point       -- a Type
#check @Point.rec  -- the eliminator
#check @Point.mk   -- the constructor
#check @Point.x    -- a projection
#check @Point.y    -- a projection

#eval Point.x (Point.mk 10 20)
#eval Point.y (Point.mk 10 20)
#check Point.mk 10 20

/- You can avoid the prefix `Point` by using the command `open Point`. -/

open Point

example {α : Type} (a b : α) : x (mk a b) = a :=
  rfl

example {α : Type} (a b : α) : y (mk a b) = b :=
  rfl


/- Given `p : Point Nat`, the dot notation `p.x` is shorthand for `Point.x p`. 
This provides a convenient way of accessing the fields of a structure. -/

def p := Point.mk 10 20

#check p.x  -- ℕ
#eval p.x   -- 10
#eval p.y   -- 20


/- The dot notation is convenient not just for accessing the projections of a
structure, but also for applying functions defined in a namespace with the same
name. For example, since `p : Point`, the expression `p.add q` is shorthand for
`Point.add p q` in the example below.-/

def Point.add (p q : Point Nat) :=
  mk (p.x + q.x) (p.y + q.y)

def q : Point Nat := Point.mk 30 40

#eval p.add q  -- {x := 40, y := 60}

/- More generally, given an expression `p.foo x y z` where `p : Point`, Lean
will insert `p` at the first argument to `Point.foo` of type `Point`. For
example, with the definition of scalar multiplication below, `p.smul 3` is
interpreted as `Point.smul 3 p`. -/

def Point.smul (n : Nat) (p : Point Nat) :=
  Point.mk (n * p.x) (n * p.y)

#eval p
#eval p.smul 3  -- {x := 3, y := 6}

/- It is common to use a similar trick with the `List.map` function, which takes
a list as its second non-implicit argument. -/

#check @List.map

def xs : List Nat := [1, 2, 3]
def f : Nat → Nat := fun x => x * x

/- We want to calculate -/

#eval List.map f xs -- [1, 4, 9]

/- 1.1 (1 point). Write an `#eval` statement with dot notation achieving the
same effect as the above. Check that they output the same values. -/

-- write your solution here

end

end LoVe
--sol

/- 1.2 (1 point). Define the function `List.mySum` that sums the elements of a
`List ℕ`, using dot notation where applicable. -/

def List.mySum : List ℕ → ℕ 
:= sorry

namespace LoVe

/- 1.3 (1 point). Write an `#eval` statement using dot notation that achieves
the same effect as the one below: -/

#eval List.mySum [1, 2, 3, 4]  -- 10
-- write your solution here

/-
Dot notation even works for proofs! If `hpq : P ∧ Q`, then `hpq.left : P` 
is syntax for `And.left hpq`. (Note that `∧` is syntax for the Proposition `And`.)

1.4 (1 point). Write as short of a term mode proof as you can of the 
following lemma, using dot notation at least once:
-/

lemma dotAndSwap (P Q R : Prop) (hpq : P ∧ Q ∧ R) : Q ∧ P := 
sorry 




/- ## Question 2 (8 points + 1 bonus point): Queue Equivalence

A *queue* is one of the most fundamental data structures used in computer
science. It holds a collection of values for future retrieval. Values can be
added to a queue by *enqueueing* them, then retrieved later by *dequeueing*.
Queues are a "first in, first out" data structure: each dequeue operation
returns the oldest remaining value in the queue. (Hence the name: the first
person to enter a line ("queue") is, analogously, the first person to exit it.)
Here's an example of a sequence of queue operations, starting with an empty
queue:

  Initial Queue: front || back
  Enqueue 3
  -> Queue: front |3| back
  Enqueue 4
  -> Queue: front |3 4| back
  Dequeue
  -> Queue: front |4| back (return 3 to caller)
  Enqueue 7
  -> Queue: front |4 7| back

Notice that we never specified *how* a queue does this, or even what type of
data a queue actually is (is it a list? a tree? a function?). In fact, as a user
of a queue, we don't need to know the answers to these questions! As the above
example shows, a queue implementation only needs to allow us to
  (1) construct an empty queue,
  (2) add items to an existing queue, and
  (3) dequeue items from an existing queue
even if we don't know how those operations occur under the hood! This is the
power of *abstraction*, which you may have seen in other CS settings (think of
signatures in ML or interfaces in object-oriented languages).

One of the key benefits of abstraction is *modularity*: the ability to
substitute one queue implementation for another without having to modify our
client code. This allows, for instance, for a user to replace an existing queue
implementation with a more efficient one.

But how do we know that the new implementation will behave equivalently to the
old one? By proving it, of course! In this exercise, you'll do the following:

* Write a simple queue implementation that will serve as a specification for
  the correctness of other queue implementations.
* Prove that a more efficient queue implementation (which we provide) is
  equivalent to your reference implementation and therefore correct.

Note: throughout this problem, you're free to use built-in `List` functions and
lemmas. -/

/- 2.1 (3 points). Implement `SimpleQueue` below as a straightforward reference
implementation of a queue. Your implementation should comprise the following:

* `SimpleQueue.emp : SimpleQueue α`, an empty queue
* `SimpleQueue.enq : SimpleQueue α → α → SimpleQueue α`, a function that
  enqueues a value onto an existing queue (i.e., `SimpleQueue.enq sq x` should
  evaluate to the queue resulting from sticking `x` at the back of the queue
  represented by `sq`)
* `SimpleQueue.deq : SimpleQueue α → Option (α × SimpleQueue α)`, a function
  that dequeues from an existing queue. This should return `none` if called on
  an empty queue; otherwise, it should return `some` applied to a tuple
  containing the dequeued element in the first position and the rest of the
  queue in the second

Notice that we have specified that, under the hood, `SimpleQueue` is implemented
as a `List`. **Do not change this!**

As a reminder, your implementation should be *obviously correct*. (You can
assume any `List` library fuctions "obviously" do what they're supposed to.
However, in the interest of simplicity and to make the proofs easier, we
recommend limiting your use of library functions; our solution uses only one.)
Do not worry about efficiency concerns -- the goal here is to provide a
reference implementation that can be used to verify other, more efficient
implementations. -/

-- Note: we use `abbrev` rather than `def` for technical reasons; you can treat
-- this as a definition
abbrev SimpleQueue (α : Type) := List α

namespace SimpleQueue

variable {α : Type}

-- Implement the required `SimpleQueue` functionality here

end SimpleQueue

/- Below, we provide an alternative queue implementation. This one makes use of
two lists. The first list stores the frontmost portion of the queue in order of
enqueueing, so that, if the first list is not empty, it stores the the next
element to be dequeued at its head. The second list stores the backmost portion
of the queue in *reverse* order of enqueueing, so that, if the second list is
nonempty, it stores the most recently enqueued element at its head. When we
dequeue, we take from the head of the first list if it's nonempty; otherwise, we
reverse the second list, make it our new first list, and take from its head.

As it turns out, this implementation is more efficient than `SimpleQueue`: all
`EfficientQueue` operations run in amortized constant time.

Take a moment to look through our implementation and make sure you understand
how it works. (It might help to try writing a few tests with `#eval` and
examining the output.) Don't skip this step -- you'll need to fully understand
how `EfficientQueue` works in order to complete the rest of this question! -/

abbrev EfficientQueue (α : Type) := List α × List α

namespace EfficientQueue

variable {α : Type}

def emp : EfficientQueue α := ([], [])

def enq : EfficientQueue α → α → EfficientQueue α
  | (f, b), x => (f, x :: b)

def deq : (q : EfficientQueue α) → Option (α × EfficientQueue α)
  -- If the front list is nonempty, its head is the next element to deqeueue
  | (f :: fs, bs) => some (f, (fs, bs))
  -- If the front list is empty, we can turn the back list into the new front
  -- list by reversing it (recall that `fs` and `bs` have opposite orderings)
  | ([], bs) =>
    match List.reverse bs with
    | [] => none
    | f :: fs => some (f, (fs, []))

end EfficientQueue

/- While `EfficientQueue` is more efficient, it is also more complex: it is not
immediately clear that it is correct. To prove that it is correct, you'll prove
that it is equivalent to `SimpleQueue`, your reference queue implementation.

2.2 (1 point). To start, we'll define a relation `EfficientQueue.Equiv` between
`SimpleQueue`s and `EfficientQueue`s that holds just when an `EfficientQueue`
and a `SimpleQueue` "represent the same queue." By this we mean the following:
we have an abstract mental notion of what a queue is, and `SimpleQueue` and
`EfficientQueue` are two different ways of representing that notion
computationally; we want `Equiv` to tell us when those two representations are
representing the same abstract, "Platonic-ideal" queue.

Note: defining this relation correctly is critical to the remaining parts. Make
sure you're confident in your solution!

Hint 1: It might help to start with some examples. How might you represent the
queue containing 4 at the front, 5 in the middle, and 6 at the back as a
`SimpleQueue` and as an `EfficientQueue`?

Hint 2: You might find it useful to think about why the following fact is true:
multiple distinct `EfficientQueue`s can represent the same abstract queue.

Hint 3: Remember that you can access the elements of a tuple `t` either using
pattern-matching or as `t.fst` and `t.snd`. -/


def Equiv {α : Type} : SimpleQueue α → EfficientQueue α → Prop
  := sorry

/- 2.3 (1 point). Now that we can express the notion of a `SimpleQueue` and an
`EfficientQueue` being "the same queue" using the `Equiv` relation, prove that
the empty `SimpleQueue` and the empty `EfficientQueue` in fact represent the
same queue.

Note: don't mind the explicit `(α := α)` argument -- that's just there to help
Lean figure out the types. -/

theorem emp_equiv {α : Type} :
  Equiv (α := α) SimpleQueue.emp EfficientQueue.emp :=
  sorry

/- 2.4 (1 point). Now we must prove that `EfficientQueue.enq` behaves
equivalently to `SimpleQueue.enq`. But what does it mean for functions on
different queue representations to "behave equivalently?"
  
Recall that *equal* functions take *equal* inputs to *equal* outputs. We'll
define equivalence of function on queues similarly, though we'll want to
consider the *equivalence*, rather than the *equality*, of
differently-represented queues.

We obtain a notion of queue-function equivalence by modifying our notion of
function equality to account for our value-level notion of queue equivalence.
We do this by substituting the word "equivalent" (referring to the `Equiv`
relation you just wrote) for "equal" any time we're talking about values that
are queues. That is, *equivalent* functions take *equal* non-queue inputs and/or
*equivalent* queue inputs to *equal* non-queue outputs and/or *equivalent* queue
outputs.

Thus, to show that our two `enq` functions are equivalent, we must show that for
*equal* values `x : α` and `y : α`, and *equivalent* queues `sq : SimpleQueue α`
and `eq : EfficientQueue α`, we have that `sq.enq x` and `eq.enq y` are
*equivalent* queues. Of course, there's no reason to make `x` and `y` distinct
variables since they are equal (not merely equivalent), so we can simply phrase
this as "`sq.enq x` and `eq.enq x` are equivalent queues" and eliminate `y`.

Make sure to take a second to convince yourself that this is a correct statement
of the equivalence of the two `enq` functions. Then, prove this equivalence,
which we've stated below. -/

-- Here's a lemma you might find helpful:
#check List.append_assoc

theorem enq_equiv {α : Type} :
  ∀ (sq : SimpleQueue α) (eq : EfficientQueue α) (x : α),
  Equiv sq eq → Equiv (sq.enq x) (eq.enq x) :=
  sorry

-- The lemma below is just for the bonus; you won't need it for part 5
theorem reverse_cons_exists {α : Type} :
  ∀ (x : α) (xs : List α), ∃ (y : α) (ys : List α),
  List.reverse (x :: xs) = y :: ys
  | x, [] => Exists.intro x (Exists.intro [] rfl)
  | x, x' :: xs =>
    have ih := reverse_cons_exists x' xs
    ih.elim (λ y h => h.elim (λ ys h' =>
      Exists.intro y <| Exists.intro (ys ++ [x]) <|
        Trans.trans (Trans.trans (List.reverse_cons x (x' :: xs))
                      (congrArg (· ++ [x]) h'))
              (List.cons_append y ys [x])))

/- 2.5 (2 points). Finally, we have `deq`. For this problem, your task is only
to *state* the proposition that we would need to prove to show that
`SimpleQueue.deq` and `EfficientQueue.deq` are equivalent: replace `True` below
with a statement of this property. You do *not* need to actually prove it!
(That's the bonus below.) 

Hint 1: Remember that all of the connectives and quantifiers we've covered so
far in the course are at your disposal.

Hint 2: It might help to consider different cases. (What connective do we use
for those?)

Hint 3: When stating the equivalence of tuples of a value and a queue (things
like `α × SimpleQueue α`), it might be helpful to think about phrasing it in
terms of there *existing* some expression to which a given tuple is equal that
has the desired properties. -/

theorem deq_equiv {α : Type} :
  True
  := sorry

/- 2.6 (1 bonus point). Prove `deq_equiv` above.

Note: this is a tricky proof, and you'll likely need to make use of several
library lemmas. A key to making this proof manageable is careful case-work: we
recommend using pattern-matching (rather than the `cases` tactic) to set up the
cases of your proof optimally. Below are a couple of lemmas you might find
helpful: -/

#check List.append_assoc
#check reverse_cons_exists





/- ## Question 3 (7 points): Heterogeneous Lists

We've become familiar with `List`s, which contain multiple ordered values of the
same type. But what if we want to store values of different types? Can this be
done in a type-safe way?

Yes! Below we define `HList`, a type of *heterogeneous lists*. While `List` is
parametrized by a single type (e.g., a `List String` contains `String`s, and a
`List Bool` contains `Bool`s), `HList` is parametrized by a *list* of types.
Each element of this type-level list defines the type of the entry at the same
position in the `HList`. For instance, an `HList [Nat, String, Bool]` contains a
natural number in the first position, a string in the second position, and a
boolean in the third position. Be sure you see how this achieved by the
following inductive definition. -/

inductive HList : List Type → Type 1
  | nil : HList []
  | cons {α : Type} {αs : List Type} : α → HList αs → HList (α :: αs)

/- The following declarations are necessary to enable custom `HList` notation
and evaluation of `HList`s with `#eval`. You do not need to understand them, and
we suggest you "collapse" them in VS Code by hovering over the line number next
to `section` and clicking the arrow that appears. -/
section
infixr:67 " ::: " => HList.cons

syntax "H[" withoutPosition(term,*) "]"  : term
macro_rules
  | `(H[ $[$elems],* ]) => do
      elems.foldrM (β := Lean.Term) (init := (← `(HList.nil))) λ x k =>
        `(HList.cons $x $k)

instance : Std.ToFormat (HList []) := ⟨λ _ => .nil⟩
instance {α} [Std.ToFormat α] : Std.ToFormat (HList [α]) :=
  ⟨λ H[x] => Std.ToFormat.format x⟩
instance {α αs} [Std.ToFormat α] [Std.ToFormat (HList αs)] :
  Std.ToFormat (HList (α :: αs)) :=
  ⟨λ (HList.cons x xs) =>
    Std.ToFormat.format x ++ ("," ++ Std.Format.line) ++ Std.ToFormat.format xs⟩
instance {αs} [Std.ToFormat (HList αs)] : Repr (HList αs) := ⟨λ xs _ => 
  Std.Format.bracket "H[" (Std.ToFormat.format xs) "]"⟩

instance : ToString (HList []) := ⟨λ _ => "H[]"⟩
instance {α} [ToString α] : ToString (HList [α]) :=
  ⟨λ H[x] => s!"H[{toString x}]"⟩
instance {α αs} [ToString α] [ToString (HList αs)] :
  ToString (HList (α :: αs)) :=
  ⟨λ (HList.cons x xs) =>
    "H[" ++ toString x ++ ", " ++ ((toString xs).drop 2).dropRight 1 ++ "]"⟩

@[app_unexpander HList.nil] def unexpandHListNil : Lean.PrettyPrinter.Unexpander
  | `($(_)) => `(H[])

@[app_unexpander HList.cons]
def unexpandHListCons : Lean.PrettyPrinter.Unexpander
  | `($(_) $x H[])      => `(H[$x])
  | `($(_) $x H[$xs,*]) => `(H[$x, $xs,*])
  | _                  => throw ()
end

-- We can write `HList`s using a syntax similar to lists:
#check H[]
#check 3 ::: "hi" ::: H[]
#check H[9, "hello", true]
#check H[("value", 4), (λ x => x + 1)]

/- If we write a function that adds, removes, or changes the types of elements
in an `HList`, therefore, we must also reflect these changes at the type level.
For instance, consider the function `HList.snoc` (which appends an element to
the end of an `HList`) below. Notice the parallel between the type it returns
and the structure of the data it returns!

Note: this is just a demonstration of how to declare a function on `HList`s.
Do not use `snoc` in any of the problems below! -/

def HList.snoc {α : Type} {αs : List Type} : HList αs → α → HList (αs ++ [α])
  | HList.nil      , y => HList.cons y HList.nil
  | HList.cons x xs, y => HList.cons x (HList.snoc xs y)

#check HList.snoc H[14, true] 52
#eval HList.snoc H[14, true] 52

/- 3.1 (1 point). Write a function `append` that appends two `HList`s together.
You'll need to complete the type as well as implement the function! -/

def HList.append {αs βs : List Type} : HList αs → HList βs → sorry
  := sorry


/- Heterogeneous lists can be used in conjunction with traditional lists to
store multi-typed tabular data (similar to Pyret, for those who are familiar).
We can think of some `αs : List Type` as indicating the type stored in each
column and treat an `HList αs` as a row. Since every row contains the same types
as the others, a collection of such rows would simply be a list of values of
type `HList αs`. Therefore, a table, which is a collection of rows, is
represented by a value of type `List (HList αs)`. For instance, the following
table is represented by a `List (HList [String, String, Nat])`:

------------------------------
| "Providence" | "RI" | 2912 |
| "Pawtucket"  | "RI" | 2860 |
| "Boston"     | "MA" | 2110 |
------------------------------

But we can also think of a table as a collection of columns: each column
contains data of a single type and so is a traditional `List`, but since each
column has a different type, the collection of all the columns must be an
`HList`. For instance, the column-wise representation of the above would have
type `HList [List String, List String, List Nat]`.

Since these representations are storing equivalent data, it would be useful to
be able to convert between them. This conversion will be our focus for the rest
of this question.

3.2 (1 point). Let `αs : List Type` represent the types stored in a given row of
a table with row-wise representation of type `List (HList αs)`. Complete the
definition of a function below that maps `αs` to some `βs : List Type` such that
`HList βs` is the type of the column-wise representation of that same table.

**Note**: Due to a Lean bug (sorry), you may not use `List.map` in your
implementation of `columnwiseType`. (Note that you *may* use `List.map`
elsewhere in this problem!) -/

def columnwiseType : List Type → List Type
  | [] => []
  | x :: xs =>
    sorry

/- 3.3 (2 points). Now that we can state its type, implement the function
`listHlistToHlistList` that converts the row-wise representation of a table
into a column-wise representation.

Hint: Notice that we've put `αs` to the right of the colon in the definition, so
you'll need to match both it and the input list in your pattern-match. (I wonder
why we'd do that...) -/

-- You may use these helper functions in your solution
def HList.hd {α αs} : HList (α :: αs) → α
  | HList.cons x _ => x

def HList.tl {α αs} : HList (α :: αs) → HList αs
  | HList.cons _ xs => xs

def listHlistToHlistList :
  ∀ {αs : List Type}, List (HList αs) → HList (columnwiseType αs)
  := sorry

/- But what about the other direction? We might be tempted to declare a function
that turns a collection of columns into a collection of rows. That function
might have this signature: -/

opaque hlistListToListHlist :
  ∀ {αs : List Type}, HList (columnwiseType αs) → List (HList αs)

/- We can describe the type of behavior we expect this function to have. For
instance, `hlistListToListHlist` shouldn't change the number of rows in a table:
the number of rows in the column-wise representation we give the function
should be equal to the number of rows in the row-wise representation we get out.

We define this property below in the case of a two-column table below. (Notice
that we're just *defining* the property; we haven't proved it!) -/

def length_hllh : Prop :=
  ∀ (α β : Type) (t : HList (columnwiseType [α, β])),
  List.length (hlistListToListHlist t) = List.length (HList.hd t)


/- 3.4 (2 points). But, in fact, we cannot define a function with this behavior!
Prove that `length_hllh` is false. This shows that, regardless of how we try to
implement a function `hlistListToListHlist`, it *cannot* have the property
`length_hllh`.

Hint 1: Read `length_hllh` carefully. It might not say exactly what we claimed.

Hint 2: You may find `Empty.elim` helpful. -/

#check @Empty.elim

-- Here's a helper function you might also find helpful: if a list of `τ`s has
-- length 1, then we can obtain a `τ` from it (if needed, you can change `1` to
-- any positive value below and the definition will still compile):
def pickFromSingletonList {τ} : ∀ {xs : List τ}, List.length xs = 1 → τ
  | x :: _, _ => x

theorem length_hllh_false : ¬ length_hllh :=
  sorry


/- 3.5 (1 point). In fact, without using features of Lean we haven't yet seen,
we can only write down one function with type
`∀ {αs : List Type}, HList (columnwise_type αs) → List (HList αs)`,
and it does not satisfy the property in `length_hllh`. Describe this function's
behavior and why it is the only function with this type. Then explain what we
would need to be able to assume about the argument to `hlistListToListHlist` in
order to create a function that inverts the row-column representation as we
desire. -/

/-
Write your answer to part 5 here.
-/




/- A final note! This is not the only possible encoding of a heterogeneous list.
Below, we declare a type `HList'` that stores heterogeneously typed data but
does *not* contain any data about the types it contains at type level. We also
declare a function `HList'.append` that appends two heterogeneous lists of this
type. -/

inductive HList'
  | nil : HList'
  | cons {α : Type} : α → HList' → HList'

def HList'.append : HList' → HList' → HList'
  | HList'.nil,       ys => ys
  | HList'.cons x xs, ys => HList'.cons x (HList'.append xs ys)

/- Food for thought: what are some pros and cons of this approach compared to
`HList`? (How easy is each to declare? To extract data from? How confident
are you that each `append` function is correct by virtue of the fact that it
type-checks?)

We won't be grading your answers here, but if you'd like to share your thoughts,
we're happy to read them! -/

--sol