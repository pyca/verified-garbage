module

public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Impl.Rsa.AArch64.Keys
public import VerifiedGarbage.Proof.Bignum.Layout

/-!
# RSA private keys on AArch64: what the batched inverse's proofs share

The semantics of the instructions the batched inverse adds to those `brun`
knows (`sbc`, `umov`, `extr`), and the vector registers that code writing
none keeps (`WP.vfix`): `Keys.inverse` keeps `d`, the matrix and the saved
registers in the lanes of `v16`–`v19` across its loops.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64

section
variable {s : State}

theorem exec_sbc_x {d n m : Reg} :
    exec (.sbc .x d n m) s = some (s.write .x d (s.gpr n + ~~~s.gpr m + BitVec.ofNat 64 s.c.toNat)) := rfl

theorem exec_umov_x {d : Reg} {n : VReg} {i : Nat} (h : i < 2) :
    exec (.umov .x d n i) s = some (s.write .x d ((s.v n).extractLsb' (64 * i) 64)) := by
  simp only [exec, Size.bits, show i * 64 < 128 by omega, ite_true]

theorem exec_extr_x {d n m : Reg} {lsb : Nat} (h : lsb < 64) :
    exec (.extr .x d n m lsb) s = some (s.write .x d ((s.gpr n ++ s.gpr m).extractLsb' lsb 64)) := by
  simp only [exec, Size.bits, State.read, h, ite_true, BitVec.setWidth_eq]

end

/-- Code that writes no vector register keeps them all. -/
theorem WP.vfix {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q)
    (hc : c.allInstrs (fun i => (vdstOf i).isNone) = true) :
    WP isa c s fun t => Q t ∧ t.v = s.v := by
  obtain ⟨tr, t, he, hq⟩ := h
  refine ⟨tr, t, he, hq, funext fun r => Exec.vec (fun i hi e => ?_) he⟩
  rw [Code.allInstrs_eq, List.all_eq_true] at hc
  have := hc i hi
  rw [e] at this
  exact absurd this (by simp)

open VG.Impl.Rsa.AArch64.Keys

theorem mulBitsF_vnone (r : Reg) : ∀ f j, (mulBitsF r f j).all (fun i => (vdstOf i).isNone) = true
  | 0, _ => rfl
  | f + 1, j => by
    rw [mulBitsF]; split
    · rfl
    · simp only [List.all_append, mulBitsF_vnone r f (j / 2)]
      split <;> rfl

theorem base_vnone (j : Nat) (r : Reg) : (base j r).all (fun i => (vdstOf i).isNone) = true := by
  unfold base baseRep mulBits
  split
  · simp only [List.all_append, List.all_replicate]; simp [vdstOf]
  · simp only [List.all_append, mulBitsF_vnone]; rfl
open VG.Proof.Bignum in
/-- Arrays `j ≠ k` of `w + 2` words: any parts of them are apart. -/
theorem slot_apart {w j k a b : Nat} (h : j ≠ k) (ha : a ≤ 8 * (w + 2)) (hb : b ≤ 8 * (w + 2)) :
    slot w j + a ≤ slot w k ∨ slot w k + b ≤ slot w j := by
  rcases slot_sep (w := w) h with h' | h' <;> [exact .inl (by omega); exact .inr (by omega)]

end VG.Proof.Rsa.AArch64
