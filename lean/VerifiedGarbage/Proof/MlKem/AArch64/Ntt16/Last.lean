module

public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Idx

/-!
# ML-KEM's 16-bit NTT on AArch64: the last two layers of a block

`lastTwo p q' …` (`Impl/MlKem/AArch64/Ntt16.lean`) transposes the 16
coefficients of `p` and `q'` (`trn1`, `trn2` on doublewords, then on words)
so that the pairs of layers 6 and 7 are in the same lanes, and back. The
permutations of the offsets (`t1d`, `t2d`, `t1s`, `t2s`) and the registers it
uses (`lastRegs`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem VG.Spec.MlKem
open Impl.MlKem.AArch64.Ntt16

/-- The offsets after a permutation. -/
def applyPerm (c : Nat → Bool) (i₁ i₂ : Nat → Nat) (ox oy : List Nat) : List Nat :=
  (List.range 8).map fun e => if c e then ox.getD (i₁ e) 0 else oy.getD (i₂ e) 0

theorem permO_apply (c : Nat → Bool) (i₁ i₂ : Nat → Nat) (ox oy : List Nat) :
    permO ox oy c i₁ i₂ (applyPerm c i₁ i₂ ox oy) = true := by
  simp only [permO, applyPerm, List.all_eq_true, List.mem_range, beq_iff_eq]
  intro e he
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range he]
  rfl

/-- `trn1`, `trn2` on doublewords and words, as offsets. -/
def t1d (ox oy : List Nat) : List Nat := applyPerm (fun e => decide (e < 4)) (fun e => e) (fun e => e - 4) ox oy
def t2d (ox oy : List Nat) : List Nat := applyPerm (fun e => decide (e < 4)) (fun e => e + 4) (fun e => e) ox oy
def t1s (ox oy : List Nat) : List Nat :=
  applyPerm (fun e => e / 2 % 2 == 0) (fun e => e) (fun e => e - 2) ox oy
def t2s (ox oy : List Nat) : List Nat :=
  applyPerm (fun e => e / 2 % 2 == 0) (fun e => e + 2) (fun e => e) ox oy

private theorem idx_d1 : ∀ e < 8, (if decide (e < 4) then e else e - 4) < 8 := by decide
private theorem idx_d2 : ∀ e < 8, (if decide (e < 4) then e + 4 else e) < 8 := by decide
private theorem idx_s1 : ∀ e < 8, (if (e / 2 % 2 == 0) then e else e - 2) < 8 := by decide
private theorem idx_s2 : ∀ e < 8, (if (e / 2 % 2 == 0) then e + 2 else e) < 8 := by decide

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

/-- The registers `lastTwo` changes. -/
abbrev lastRegs (p q' : VReg) : List VReg := [.v4, .v5, .v16, .v17, p, q']

end

end VG.Proof.MlKem.AArch64.Ntt16
