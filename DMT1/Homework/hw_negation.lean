/-
EXERCISE #1: Finish this proof.
The following theorem shows that *or is commutative*.
That is, if P ∨ Q  and Q ∨ P are equivalent: either
both true or both false at the same time. Recall that
(P ∨ Q) if and only if (Q ∨ P) is true if and only if
P ∨ Q → Q ∨ P and also that Q ∨ P → P ∨ Q. Applying
Iff.intro to proofs of these implications, one going
in the forward (left to right direction) and the other
in the backwards direction (right to left) then you
be handed a proof of P ∨ Q ↔ Q ∨ P.

We construct this proof top down, by applying Iff.intro
to two as yet not fully developed proofs of the two
implications. We then fill in definitions of those
proofs, and when we're done doing that, Lean accepts
that we've proved the equivalence.
-/
theorem orComm (P Q : Prop) : (P ∨ Q) ↔ (Q ∨ P) :=
Iff.intro
  (fun porq =>
  match porq with
  | Or.inl p => Or.inr p
  | Or.inr q => Or.inl q
  )  -- forward direction
  (fun qorp =>
  match qorp with
  | Or.inl q => Or.inr q
  | Or.inr p => Or.inl p
  )  -- backward direction

/-
Exercise #2: State and prove the theorem that Or is associative.
-/
theorem orAssoc (P Q R : Prop) : (P ∨ (Q ∨ R)) ↔ ((P ∨ Q) ∨ R) :=
Iff.intro
( fun pandq =>
match pandq with
| Or.inl p => Or.inl (Or.inl p)
| Or.inr (Or.inl q) => Or.inl (Or.inr q)
| Or.inr (Or.inr r) => (Or.inr r)
)
( fun qandp =>
match qandp with
| Or.inl (Or.inl p) => (Or.inl p)
| Or.inl (Or.inr q) => Or.inr (Or.inl q)
| Or.inr r => Or.inr (Or.inr r)
)


/-
Exercise #3: Is Or transitive? If we know P ∨ Q and we know Q ∨ R
then do we know P ∨ R for sure? If so prove it, if not in English
just give a counterexample: What's a situation where the premises
of this implication are true but the conclusion is false. You can
just argue here in terms of truth values.
-/
theorem orTrans (P Q R : Prop) : (P ∨ Q) → (Q ∨ R) → (P ∨ R) :=
_

/- No, or is not transitive. In this case, we don't know P ∨ R because
this would imply that with every Q follows an R, and that with every
P follows a Q. A counterexample could be: let P = False, Q = true, and R = false.
P ∨ Q = true, Q ∨ R = true, but P ∩r Q = false, proving that Or is not
transitive. -/


/-
Exercise #4: Formally state and prove the following conjecture:
∧ distributes over ∨. This is like saying * distributes over +
in arithmetic. In math, for example, 3 * (4 + 5) = 3 * 4 + 3 * 5.
This what we mean by *multiplication distributes over addition.*
In logic we mean A ∧ (B ∨ C) ↔ (A ∧ B) ∨ (A ∧ C). Formally state
and prove this equivalence.
-/
theorem andDistrib (A B C : Prop) : (A ∧ (B ∨ C)) ↔ ((A ∧ B) ∨ (A ∧ C)) :=
Iff.intro
  (fun h =>
    match h with
    | And.intro a (Or.inl b) => Or.inl (And.intro a b)
    | And.intro a (Or.inr c) => Or.inr (And.intro a c))
  (fun h =>
    match h with
    | Or.inl (And.intro a b) => And.intro a (Or.inl b)
    | Or.inr (And.intro a c) => And.intro a (Or.inr c))
