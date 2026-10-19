module

public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Shape
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.X86_64.Words

/-! # FFDH parameter candidates on x86-64: public bit-mask selection -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem cmov_reg_value (s : State) (cc : Cond) (d r : Reg) :
    execCmov cc d (.reg r) s = (eval cc s).map
      (fun c => s.setReg d (if c then s.gpr r else s.gpr d)) := by
  simp only [execCmov, readSrc, Option.bind_some]
  congr 1
  funext c
  cases c
  · simp only [Bool.false_eq_true, ↓reduceIte]
    symm
    simp only [State.setReg]
    congr 1
    funext r'
    split <;> simp_all
  · rfl

theorem masks_ok {s : State} {j : Nat} (hj : j < 8) (hd : s.gpr .rdx = BitVec.ofNat 64 j) :
    WP isa (.block maskLookup) s fun t => t.gpr .r8 = BitVec.ofNat 64 (2 ^ j - 1) ∧
      t.gpr .r9 = BitVec.ofNat 64 (2 ^ j) ∧ t.mem = s.mem ∧ Keep [.rdx, .r8, .r9, .r10] s t := by
  refine WP.mono (WP.keep [.rdx, .r8, .r9, .r10] (Q := fun t =>
    t.gpr .r8 = BitVec.ofNat 64 (2 ^ j - 1) ∧ t.gpr .r9 = BitVec.ofNat 64 (2 ^ j) ∧ t.mem = s.mem) ?_ (by decide +kernel))
    fun _ ⟨⟨h8, h9, hm⟩, k⟩ => ⟨h8, h9, hm, k⟩
  have hcode : maskLookup = ([.mov32 .r8 (.imm 127), .mov32 .r9 (.imm 128)] : List Instr) ++
      maskCase 0 ++ maskCase 1 ++ maskCase 2 ++ maskCase 3 ++ maskCase 4 ++ maskCase 5 ++ maskCase 6 := by
    decide +kernel
  rw [hcode]
  simp only [maskCase, List.cons_append, List.nil_append]
  have he : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    xrun [hd, cmov_reg_value, eval]

/-- Select the two masks for the actual requested bit width. -/
theorem shapeMasks_ok {s : State} {bits : Nat} (hb : 1 ≤ bits) (hk : bits < 2 ^ 31)
    (hd : s.gpr .rdx = BitVec.ofNat 64 bits) :
    WP isa (.block shapeMasks) s fun t =>
      t.gpr .r8 = BitVec.ofNat 64 (2 ^ ((bits - 1) % 8) - 1) ∧
      t.gpr .r9 = BitVec.ofNat 64 (2 ^ ((bits - 1) % 8)) ∧ t.mem = s.mem ∧
      Keep [.rdx, .r8, .r9, .r10] s t := by
  have hsub : BitVec.ofNat 64 bits - 1 = BitVec.ofNat 64 (bits - 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
    omega
  have hand : BitVec.ofNat 64 (bits - 1) &&& 7 = BitVec.ofNat 64 ((bits - 1) % 8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat, show (7 : BitVec 64).toNat = 7 from rfl]
    rw [Nat.mod_eq_of_lt (show bits - 1 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show (bits - 1) % 8 < 2 ^ 64 by omega)]
    exact Nat.and_two_pow_sub_one_eq_mod (bits - 1) 3
  unfold shapeMasks
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rdx] (Q := fun t =>
    t.gpr .rdx = BitVec.ofNat 64 ((bits - 1) % 8) ∧ t.mem = s.mem)
    (by xrun [hd, hsub, hand, show BitVec.signExtend 64 (7 : BitVec 32) = 7 from by decide]) rfl) fun u ⟨⟨hdu, hmu⟩, ku⟩ => ?_
  exact WP.mono (masks_ok (by omega) hdu) fun t ⟨hm, hh, hmem, k⟩ =>
    ⟨hm, hh, hmem.trans hmu, (ku.trans k).mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
