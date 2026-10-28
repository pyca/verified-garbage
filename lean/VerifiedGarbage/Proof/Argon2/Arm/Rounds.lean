module

public import VerifiedGarbage.Proof.Argon2.Arm.Gb
import VerifiedGarbage.Proof.Argon2.Permutation
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# Argon2 on ARMv7: the row and column permutations

As on x86 (`Proof/Argon2/X86/Rounds.lean`): P on any injectively selected
row or column (`permuteAt_ok`). The code addresses the words of `index₀` at
`r3`, which is `8e` bytes past the base `B`: it permutes those of `index`,
`e` words on. The passes over the rows and columns are in
`Proof/Argon2/Arm/Pass.lean`.
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm

open VG VG.Arm VG.Spec.Argon2
open VG.Proof.Argon2
open VG.Proof.Sha512.Arm (Reg64)

/-- The selected sixteen words and the unchanged words outside them. -/
def Holds (index : Fin 16 → Fin 128) (b : Block) (v : Vector Word 16) (m : Mem)
    (B : BitVec 32) : Prop :=
  gather index (working m B) = v ∧ ∀ k : Fin 128, (∀ j, index j ≠ k) → (working m B)[k] = b[k]

/-- The base and the permissions of `scratch`, with `r3` `8e` bytes past the base. -/
def At (B : BitVec 32) (e : Nat) (s : State) : Prop :=
  s.gpr .r3 = B + BitVec.ofNat 32 (8 * e) ∧ Reg64 s.wr B 2048

theorem At.of_step {B : BitVec 32} {e : Nat} {s t : State} {v : Block} (h : At B e s)
    (st : Step B s v t) : At B e t :=
  ⟨st.keep.r3.trans h.1, st.keep.wr ▸ h.2⟩

section
variable {B : BitVec 32} (hfit : B.toNat + 4096 ≤ 2 ^ 32)
  (index index₀ : Fin 16 → Fin 128) (e : Nat) (hidx : ∀ k, (index k).val = (index₀ k).val + e)

include hfit hidx

/-- One GB advances the selected row or column and preserves its complement:
the code GB on `index₀`, with `r3` `8e` bytes on, is GB on `index`. -/
theorem step_ok (hi : Function.Injective index) {s : State}
    (hs : At B e s) (base : Block) (v : Vector Word 16) (hv : Holds index base v s.mem B)
    (a b c d : Fin 16) (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (had : a.val ≠ d.val)
    (hbc : b.val ≠ c.val) (hbd : b.val ≠ d.val) (hcd : c.val ≠ d.val) :
    WP isa (Impl.Argon2.Arm.gbAt (index₀ a).val (index₀ b).val (index₀ c).val (index₀ d).val) s
      fun t => Holds index base (GB v a b c d) t.mem B ∧ ∃ w, Step B s w t := by
  refine (gbAt_ok hfit hs.1 hs.2 (index a) (index b) (index c) (index d)
    (hidx a) (hidx b) (hidx c) (hidx d)).mono fun t st => ?_
  refine ⟨⟨?_, ?_⟩, _, st⟩
  · rw [st.working, gather_mixWords index hi, hv.1, GB_eq_mixWords v hab hac had hbc hbd hcd]
  · intro k hn
    rw [st.working]
    have ne' (j : Fin 16) : (index j).val ≠ k.val := fun h => hn j (Fin.ext h)
    simp only [mixWords, Fin.getElem_fin, Vector.getElem_set, ne', ite_false]
    exact hv.2 k hn

/-- P on any injectively selected row or column. -/
theorem permuteAt_holds (hi : Function.Injective index) {s : State}
    (hs : At B e s) (base : Block) (v : Vector Word 16) (hv : Holds index base v s.mem B) :
    WP isa (Impl.Argon2.Arm.permuteAt index₀) s fun t =>
      Holds index base (permute v) t.mem B ∧ ∃ w, Step B s w t := by
  have advance (t : State) (v' : Vector Word 16)
      (h : Holds index base v' t.mem B ∧ ∃ w, Step B s w t)
      (a b c d : Fin 16)
      (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (had : a.val ≠ d.val)
      (hbc : b.val ≠ c.val) (hbd : b.val ≠ d.val) (hcd : c.val ≠ d.val) :
      WP isa (Impl.Argon2.Arm.gbAt (index₀ a).val (index₀ b).val (index₀ c).val (index₀ d).val)
        t fun u => Holds index base (GB v' a b c d) u.mem B ∧ ∃ w, Step B s w u := by
    obtain ⟨hh, w, st⟩ := h
    refine (step_ok hfit index index₀ e hidx hi (hs.of_step st) base v' hh a b c d
      hab hac had hbc hbd hcd).mono ?_
    rintro u ⟨hu, w', st'⟩
    exact ⟨hu, w', st.trans st'⟩
  unfold Impl.Argon2.Arm.permuteAt
  apply WP.seq
  refine (advance s _ ⟨hv, _, ⟨.refl s, rfl, Frame.refl _ _⟩⟩ 0 4 8 12
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s1 h1
  apply WP.seq
  refine (advance s1 _ h1 1 5 9 13
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s2 h2
  apply WP.seq
  refine (advance s2 _ h2 2 6 10 14
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s3 h3
  apply WP.seq
  refine (advance s3 _ h3 3 7 11 15
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s4 h4
  apply WP.seq
  refine (advance s4 _ h4 0 5 10 15
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s5 h5
  apply WP.seq
  refine (advance s5 _ h5 1 6 11 12
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s6 h6
  apply WP.seq
  refine (advance s6 _ h6 2 7 8 13
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s7 h7
  exact advance s7 _ h7 3 4 9 14
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The row/column code meets the specification's gather, P, scatter definition. -/
theorem permuteAt_ok (hi : Function.Injective index) {s : State} (hs : At B e s) :
    WP isa (Impl.Argon2.Arm.permuteAt index₀) s
      (Step B s (Spec.Argon2.permuteAt index (working s.mem B))) := by
  refine (permuteAt_holds hfit index index₀ e hidx hi hs (working s.mem B)
    (gather index (working s.mem B)) ⟨rfl, fun _ _ => rfl⟩).mono ?_
  rintro t ⟨ht, w, st⟩
  exact ⟨st.keep, eq_scatter index hi _ _ _ ht.1 ht.2, st.frame⟩

end

end VG.Proof.Argon2.Arm
