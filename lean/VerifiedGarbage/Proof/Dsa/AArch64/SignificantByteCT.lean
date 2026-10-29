module
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Impl.Dsa.AArch64.Checks

import VerifiedGarbage.Proof.Dsa.AArch64.Significant
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Impl.Dsa.AArch64.Checks
meta import VerifiedGarbage.Proof.Dsa.AArch64.Significant
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import Aesop.BuiltinRules
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Timing of one public modulus-width scan byte -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure ScanBytePublic where
  pointer : Addr
  remaining : Nat
  found : Nat × Byte
  value : Byte

def ScanBytePre (p : ScanBytePublic) (s : State) : Prop :=
  s.gpr .x1 = p.pointer ∧ s.gpr .x9 = BitVec.ofNat 64 p.remaining ∧
  s.gpr .x8 = BitVec.ofNat 64 p.found.1 ∧ s.gpr .x10 = p.found.2.zeroExtend 64 ∧
  s.mem p.pointer = p.value ∧ InRegions (s.rd ++ s.wr) p.pointer 1 ∧ p.found.1 < 2 ^ 64

def ScanChoosePre (p : ScanBytePublic) (s : State) : Prop :=
  s.gpr .x1 = p.pointer ∧ s.gpr .x9 = BitVec.ofNat 64 p.remaining ∧
  s.gpr .x8 = BitVec.ofNat 64 p.found.1 ∧ s.gpr .x10 = p.found.2.zeroExtend 64 ∧
  s.gpr .x3 = p.value.zeroExtend 64 ∧ p.found.1 < 2 ^ 64

theorem significantChoose_ct : RelCT isa (Two ScanChoosePre) Checks.significantChoose (fun _ _ => True) := by
  exact two_taint [.x8, .x3, .x9]
    (pins_of (fun p r => if r = .x8 then BitVec.ofNat 64 p.found.1 else
      if r = .x3 then p.value.zeroExtend 64 else BitVec.ofNat 64 p.remaining) (by
        intro p s h r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.2.2.1
        · exact h.2.2.2.2.1
        · exact h.2.1)) (by taint_decide)

theorem significantByte_ct : RelCT isa (Two ScanBytePre) Checks.significantByte (fun _ _ => True) := by
  unfold Checks.significantByte seqs
  refine RelCT.seq (two_piece (Ψ := ScanChoosePre) [.x1, .x8]
    (pins_of (fun p r => if r = .x1 then p.pointer else BitVec.ofNat 64 p.found.1) (by
      intro p s h r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1
      · exact h.2.2.1)) (by taint_decide) ?_) ?_
  · intro p s ⟨hsi, hcx, h8, h9, hm, hr, hf⟩
    refine WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = p.value.zeroExtend 64) ?_ rfl rfl rfl)
      fun t ⟨ha, hk⟩ => ⟨(hk.gpr .x1 (by decide)).trans hsi,
        (hk.gpr .x9 (by decide)).trans hcx, (hk.gpr .x8 (by decide)).trans h8,
        (hk.gpr .x10 (by decide)).trans h9, ha, hf⟩
    brun [hsi, hm, hr, read_one]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.zeroExtend]
    have := p.value.isLt
    omega
  refine RelCT.seq (two_post (Ψ := fun (p : ScanBytePublic) t =>
    t.gpr .x1 = p.pointer ∧ t.gpr .x9 = BitVec.ofNat 64 p.remaining) significantChoose_ct ?_) ?_
  · intro p s ⟨hsi, hcx, h8, h9, ha, hz⟩
    exact WP.mono (significantChoose_ok h8 h9 ha hcx hz) fun t ⟨_, _, _, hk⟩ =>
      ⟨(hk.gpr .x1 (by decide)).trans hsi, (hk.gpr .x9 (by decide)).trans hcx⟩
  · exact two_taint [.x1, .x9]
      (pins_of (fun p r => if r = .x1 then p.pointer else BitVec.ofNat 64 p.remaining) (by
        intro p s h r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1
        · exact h.2)) (by taint_decide)

end VG.Proof.Dsa.AArch64
