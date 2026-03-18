import Mathlib
import Ainfinity.Grading

open CategoryTheory Finset AInfinityCategoryTheory

noncomputable section

namespace AInfinityAlgebraTheory

universe u v
variable {β : Type v} [Grading β]

abbrev GradedRModule (R : Type u) [CommRing R] :=
  GradedObject β (ModuleCat.{u} R)

structure AInfinityAlgebraData (R : Type u) [CommRing R] where
  A : GradedRModule (β := β) (R := R)

  m :
    (n : ℕ) →
    (deg : Fin n → β) →
    MultilinearMap R (fun i => A (deg i))
      (A ((∑ i, deg i) + shift_ofInt (2 - (n : ℤ))))


namespace AInfinityAlgebraData

variable {R : Type u} [CommRing R]

abbrev validStasheffIndices (n r s : ℕ) : Prop :=
  1 ≤ s ∧ r + s ≤ n

/-- Helper: degree function for the inner portion of the Stasheff composition. -/
-- returns function that takes in i -> deg[r+i]
def stasheffDegIn
    (deg : Fin n → β)
    (r s : ℕ)
    (hr : r + s ≤ n) : Fin s → β :=
  fun i => deg ⟨r + i.val, by omega⟩

/-- Helper: inner degree (the degree of the result of the inner multilinear map). -/
--  deg[r+1] + ... + deg[r+s] + 2-s
-- in bocklandt, this is the deg of term after we apply b_s, the one in the middle
def stasheffInnerDeg
    (deg : Fin n → β)
    (r s : ℕ)
    (hr : r + s ≤ n) : β :=
  (∑ j : Fin s, stasheffDegIn deg r s hr j) + shift_ofInt (2 - (s : ℤ))

/-- Helper: the data bundle (degree, element) for each position in the outer map. -/
-- so apply (1^⊗r ⊗ b_s ⊗ 1^⊗t) on n elements. we now have n+1-s elements.
-- the below function takes in index i and gives u the degre and element
def stasheffOuterData
    {X : AInfinityAlgebraData (β := β) R}
    {n : ℕ}
    (deg : Fin n → β)
    (x : ∀ i, X.A (deg i))
    (r s : ℕ)
    (hs : 1 ≤ s)
    (hr : r + s ≤ n)
    (inner : X.A (stasheffInnerDeg deg r s hr))
    (i : Fin (n + 1 - s)) : (d : β) × X.A d :=
  if h1 : i.val < r then
    ⟨deg ⟨i.val, by omega⟩, x ⟨i.val, by omega⟩⟩
  else if _ : i.val = r then
    ⟨stasheffInnerDeg deg r s hr, inner⟩
  else
    ⟨deg ⟨i.val + s - 1, by omega⟩, x ⟨i.val + s - 1, by omega⟩⟩

/-- Helper: the outer degree function. -/
def stasheffDegOut
    (deg : Fin n → β)
    (r s : ℕ)
    (hs : 1 ≤ s)
    (hr : r + s ≤ n) : Fin (n + 1 - s) → β :=
  fun i =>
    if h1 : i.val < r then
      deg ⟨i.val, by omega⟩
    else if _ : i.val = r then
      stasheffInnerDeg deg r s hr
    else
      deg ⟨i.val + s - 1, by omega⟩

lemma shift_ofInt_combine {n s : ℕ} (hsn : s ≤ n) :
    shift_ofInt (β := β) (2 - (s : ℤ)) + shift_ofInt (2 - ((n + 1 - s : ℕ) : ℤ)) =
    shift_ofInt (3 - (n : ℤ)) := by
    have : 3 - (n : ℤ) = 2 - (s : ℤ) + 2 - ((n + 1 - s : ℕ) : ℤ) := by
      have hle : s ≤ n + 1 := Nat.le_succ_of_le hsn
      rw [Nat.cast_sub hle]
      push_cast
      omega
    rw [this]
    conv =>
      rhs
      arg 1
      rw [Int.add_sub_assoc (2 - (s : ℤ))]
    unfold shift_ofInt
    symm
    apply map_add

--looks good. the statement is correct. proof we dont care
lemma stasheffDegOut_sum_core
    (deg : Fin n → β)
    (r s : ℕ)
    (hs : 1 ≤ s)
    (hr : r + s ≤ n) :
    (∑ i : Fin (n + 1 - s), stasheffDegOut deg r s hs hr i) =
    (∑ i : Fin n, deg i) + shift_ofInt (2 - (s : ℤ)) := by
  unfold stasheffDegOut;
  rw [ show ( Finset.univ : Finset ( Fin ( n + 1 - s ) ) ) = Finset.univ.filter ( fun i : Fin ( n + 1 - s ) => i.val < r ) ∪ Finset.univ.filter ( fun i : Fin ( n + 1 - s ) => i.val = r ) ∪ Finset.univ.filter ( fun i : Fin ( n + 1 - s ) => i.val > r ) from ?_, Finset.sum_union, Finset.sum_union ];
  · rw [ show ( Finset.univ.filter fun i : Fin ( n + 1 - s ) => ( i : ℕ ) < r ) = Finset.image ( fun i : Fin r => ⟨ i, by omega ⟩ ) Finset.univ from ?_, show ( Finset.univ.filter fun i : Fin ( n + 1 - s ) => ( i : ℕ ) = r ) = { ⟨ r, by omega ⟩ } from ?_, show ( Finset.univ.filter fun i : Fin ( n + 1 - s ) => ( i : ℕ ) > r ) = Finset.image ( fun i : Fin ( n - r - s ) => ⟨ r + 1 + i, by omega ⟩ ) Finset.univ from ?_ ];
    · rw [ Finset.sum_image, Finset.sum_image ] <;> norm_num;
      · rw [ show ( Finset.univ : Finset ( Fin n ) ) = Finset.image ( fun i : Fin r => ⟨ i, by linarith [ Fin.is_lt i ] ⟩ ) Finset.univ ∪ Finset.image ( fun i : Fin s => ⟨ r + i, by linarith [ Fin.is_lt i ] ⟩ ) Finset.univ ∪ Finset.image ( fun i : Fin ( n - r - s ) => ⟨ r + s + i, by omega ⟩ ) Finset.univ from ?_, Finset.sum_union, Finset.sum_union ];
        · rw [ Finset.sum_image, Finset.sum_image, Finset.sum_image ] <;> norm_num;
          · unfold stasheffInnerDeg;
            unfold stasheffDegIn; ring;
            grind;
          · exact fun i j h => by simpa [ Fin.ext_iff ] using h;
          · exact fun i j h => by simpa [ Fin.ext_iff ] using h;
          · exact fun i j h => by simpa [ Fin.ext_iff ] using h;
        · norm_num [ Finset.disjoint_left ];
          grind;
        · norm_num [ Finset.disjoint_right ];
          grind;
        · ext ⟨ i, hi ⟩ ; simp +decide [ Finset.mem_union, Finset.mem_image ];
          by_cases hi' : i < r;
          · exact Or.inl ⟨ ⟨ i, by linarith ⟩, rfl ⟩;
          · by_cases hi'' : i < r + s;
            · exact Or.inr <| Or.inl ⟨ ⟨ i - r, by omega ⟩, by simp +decide [ Nat.add_sub_of_le ( le_of_not_gt hi' ) ] ⟩;
            · exact Or.inr <| Or.inr <| ⟨ ⟨ i - ( r + s ), by omega ⟩, by norm_num; omega ⟩;
      · exact fun i j h => by simpa [ Fin.ext_iff ] using h;
      · exact fun i j h => by simpa [ Fin.ext_iff ] using h;
    · -- To prove equality of finite sets, we show each set is a subset of the other.
      apply Finset.ext
      intro i
      simp [Finset.mem_image];
      exact ⟨ fun hi => ⟨ ⟨ i - ( r + 1 ), by omega ⟩, by erw [ Fin.ext_iff ] ; norm_num; omega ⟩, by rintro ⟨ a, rfl ⟩ ; exact Nat.lt_of_lt_of_le ( by simp +arith +decide ) ( Nat.le_add_right _ _ ) ⟩;
    · ext ⟨ i, hi ⟩ ; aesop;
    · ext ⟨i, hi⟩; simp [Finset.mem_image];
      exact ⟨ fun hi' => ⟨ ⟨ i, by omega ⟩, rfl ⟩, fun ⟨ a, ha ⟩ => by linarith [ Fin.is_lt a ] ⟩;
  · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith;
  · simp +contextual [ Finset.disjoint_left ];
    exact fun a ha => ha.elim ( fun ha => le_of_lt ha ) fun ha => ha.le;
  · ext i; cases lt_trichotomy i.val r <;> aesop;


-- r+t+1 = n-s +1
lemma stasheffDegOut_sum
    (deg : Fin n → β)
    (r s : ℕ)
    (hs : 1 ≤ s)
    (hr : r + s ≤ n) :
    (∑ i : Fin (n + 1 - s), stasheffDegOut deg r s hs hr i) +
      shift_ofInt (2 - ((n + 1 - s : ℕ) : ℤ)) =
    (∑ i : Fin n, deg i) + shift_ofInt (3 - (n : ℤ)) := by
  rw [stasheffDegOut_sum_core deg r s hs hr, add_assoc,
      shift_ofInt_combine (by omega : s ≤ n)]


-- all we need is r+s+t = n, r>=0, t>=0, s>0

def stasheffTerm
  (X : AInfinityAlgebraData R)
  (n : ℕ)
  (deg : Fin n → β)
  (x : ∀ i, X.A (deg i))
  (r s : ℕ)
  (hs : 1 ≤ s)
  (hr : r + s ≤ n) :
  X.A ((∑ i, deg i) + shift_ofInt (3 - (n : ℤ))) :=
by
  /-
  This is the place where the real implementation goes.

  Recommended pattern:
    let degIn : Fin s → β := ...
    let xIn   : ∀ i : Fin s, X.A (degIn i) := ...
    let inner : X.A (...) := X.m s degIn xIn

    let degOut : Fin (n + 1 - s) → β := ...
    let xOut   : ∀ i : Fin (n + 1 - s), X.A (degOut i) := ...

    have hdeg : ... = ((∑ i, deg i) + shiftOfInt (β := β) (3 - (n : ℤ))) := ...
    exact cast (by rw [hdeg]) (X.m (n + 1 - s) degOut xOut)

  Keeping these as local lets is usually better than making all of them top-level defs.
  -/

  -- Inner application
  let degIn := stasheffDegIn deg r s hr
  let xIn : ∀ i : Fin s, X.A (degIn i) := fun i => x ⟨r + i.val, by omega⟩
  let inner := X.m s degIn xIn
  -- Outer application
  let outerN := n + 1 - s
  let data := stasheffOuterData deg x r s hs hr inner
  let degOut : Fin outerN → β := fun i => (data i).1
  let xOut : ∀ i : Fin outerN, X.A (degOut i) := fun i => (data i).2
  have hdegOut : degOut = stasheffDegOut deg r s hs hr := by
    ext i
    simp only [degOut, data, stasheffOuterData, stasheffDegOut]
    split_ifs <;> rfl
  let outer := X.m outerN degOut xOut
  have hdeg : (∑ i : Fin outerN, degOut i) + shift_ofInt (2 - (outerN : ℤ)) =
    (∑ i : Fin n, deg i) + shift_ofInt (3 - (n : ℤ)) := by
    rw [hdegOut]
    exact stasheffDegOut_sum deg r s hs hr
  exact hdeg ▸ outer




/--
A single summand in the Stasheff sum, returning `0` when the indices are invalid.
This is the object that appears inside the double finite sum.
-/
def stasheffSummand
  (X : AInfinityAlgebraData (β := β) R)
  (n : ℕ)
  (deg : Fin n → β)
  (x : ∀ i, X.A (deg i))
  (r s : ℕ) :
  X.A ((∑ i, deg i) + shift_ofInt (3 - (n : ℤ))) :=
  if h : validStasheffIndices n r s then
    X.stasheffTerm n deg x r s h.1 h.2
  else
    0

/-- The full Stasheff sum in arity `n`. -/
def stasheffSum
  (X : AInfinityAlgebraData (β := β) R)
  (n : ℕ)
  (deg : Fin n → β)
  (x : ∀ i, X.A (deg i)) :
  X.A ((∑ i, deg i) + shift_ofInt (3 - (n : ℤ))) :=
  ∑ r ∈ Finset.range (n + 1),
    ∑ s ∈ Finset.Ico 1 (n - r + 1),
      X.stasheffSummand n deg x r s

/-- The Stasheff identities as a property of the raw A∞ data. -/
def satisfiesStasheff
  (X : AInfinityAlgebraData (β := β) R) : Prop :=
  ∀ (n : ℕ) (deg : Fin n → β) (x : ∀ i, X.A (deg i)),
    X.stasheffSum n deg x = 0

/-- If the indices are valid, the summand is exactly the corresponding term. -/
--this trivial gang
lemma stasheffSummand_eq_term
  (X : AInfinityAlgebraData (β := β) R)
  (n : ℕ)
  (deg : Fin n → β)
  (x : ∀ i, X.A (deg i))
  (r s : ℕ)
  (h : validStasheffIndices n r s) :
  X.stasheffSummand n deg x r s
    = X.stasheffTerm n deg x r s h.1 h.2 := by

  unfold stasheffSummand; aesop


/-- If the indices are invalid, the summand vanishes. -/
lemma stasheffSummand_eq_zero
  (X : AInfinityAlgebraData (β := β) R)
  (n : ℕ)
  (deg : Fin n → β)
  (x : ∀ i, X.A (deg i))
  (r s : ℕ)
  (h : ¬ validStasheffIndices n r s) :
  X.stasheffSummand n deg x r s = 0 := by
  unfold AInfinityAlgebraData.stasheffSummand; aesop

end AInfinityAlgebraData

/-- An A∞-algebra is raw data together with the Stasheff identities. -/
structure AInfinityAlgebra (R : Type u) [CommRing R]
  extends AInfinityAlgebraData (β := β) R where
  stasheff :
    AInfinityAlgebraData.satisfiesStasheff
      (β := β) toAInfinityAlgebraData

namespace AInfinityAlgebra

variable {R : Type u} [CommRing R]

/-- Re-export the Stasheff identity in a convenient form. -/
lemma stasheff_eq_zero
  (X : AInfinityAlgebra (β := β) R)
  (n : ℕ)
  (deg : Fin n → β)
  (x : ∀ i, X.A (deg i)) :
  X.toAInfinityAlgebraData.stasheffSum n deg x = 0 :=
  X.stasheff n deg x

end AInfinityAlgebra

end AInfinityAlgebraTheory
