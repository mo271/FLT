/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib.Algebra.Quaternion -- probably get away with less
import Mathlib.RingTheory.HopfAlgebra
import Mathlib.Algebra.Lie.OfAssociative


/-!
# Characteristic predicate for central simple algebras

In this file we define the predicate `IsCentralSimple K D` where `K` is a field
and `D` is a (noncommutative) `K`-algebra.

Note that the predicate makes sense just for `K` a `CommRing` but it doesn't give the
right definition; for a commutative ring base one should use the theory of Azumaya algebras.
This adds an extra layer of complication which we don't need. In fact ideals of `K`
immediately give rise to nontrivial quotients of `D` so there are no central simple
algebras in this case according to our definition.

-/

universe u v w

structure IsCentralSimple
    (K : Type u) [Field K] (D : Type v) [Ring D] [Algebra K D] : Prop where
  is_central : ∀ d : D, d ∈ Subring.center D → ∃ k : K, d = algebraMap K D k
  is_simple : IsSimpleOrder (RingCon D)

variable (K : Type u) [Field K]

theorem MatrixRing.isCentralSimple (ι : Type v) (hι : Fintype ι) (hnonempty : Nonempty ι) [DecidableEq ι] :
    IsCentralSimple K (Matrix ι ι K) := by
  constructor
  · intro d hd
    obtain ⟨h1, _, _ , _⟩ := hd
    have ⟨k, hk⟩ : ∃ k : K, d = Matrix.diagonal (fun i => k) := by
      use d hnonempty.some hnonempty.some
      have h_diag : ∀ i j : ι, d i i = d j j := by
        intro i j
        set M := (Matrix.stdBasisMatrix i j (1 : K))
        specialize h1 M
        have eq_entry : (d * M) i j =
            (M * d) i j := by
          rw [h1]
        simp [M] at eq_entry
        exact eq_entry
      ext i j
      by_cases hij : i = j
      · simp only [hij, Matrix.diagonal, Matrix.of_apply, ↓reduceIte]
        exact h_diag j hnonempty.some
      · simp at hij
        simp only [ne_eq, hij, not_false_eq_true, Matrix.diagonal_apply_ne]
        let M := Matrix.stdBasisMatrix j j ( (1 : K))
        specialize h1 M
        have eq_entry : (d * M) i j = (M * d) i j := by
          rw [h1]
        simp only [Matrix.diagonal_one, M, Matrix.StdBasisMatrix.mul_right_apply_same, mul_one,
            Matrix.StdBasisMatrix.mul_left_apply_of_ne _ _ _  _ _ hij] at eq_entry
        ring_nf at eq_entry
        exact eq_entry
    exact Exists.intro k hk
  · sorry

namespace IsCentralSimple

variable (D : Type v) [Ring D] [Algebra K D] (h : IsCentralSimple K D)

/-
\begin{lemma}
    \label{IsCentralSimple.baseChange}
    If $D$ is a central simple algebra over~$K$ and $L/K$ is a field extension, then $L\otimes_KD$
    is a central simple algebra over~$L$.
\end{lemma}
\begin{proof}
    This is not too hard: it's lemma b of section 12.4 in Peirce's "Associative algebras".
    Will maybe write more on Saturday.
\end{proof}
-/

open scoped TensorProduct

lemma baseChange (L : Type w) [Field L] [Algebra K L] : IsCentralSimple L (L ⊗[K] D) := by
    constructor
    · sorry
    · sorry

end IsCentralSimple
-- restrict to 4d case
-- theorem exists_quaternionAlgebra_iso (hK : (2 : K) ≠ 0) :
--     ∃ a b : K, Nonempty (D ≃ₐ[K] ℍ[K, a, b]) := sorry
