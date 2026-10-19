module
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Finish
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8StepCT

import VerifiedGarbage.Proof.MlKem.AArch64.Rej8LoopCT
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Finish
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Impl.MlKem.AArch64.Encode
import VerifiedGarbage.Proof.Blowfish.AArch64.Lanes
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Lanes
import VerifiedGarbage.Proof.MlKem.AArch64.Coeff16
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lane
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Mem
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Table
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Accept
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8BatchCT
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8BodyCT
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Constants
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Decode
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Invariant
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Loop
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Memory
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Public
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8ScalarCT
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Steps
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Zero
import VerifiedGarbage.Proof.MlKem.Compress
meta import VerifiedGarbage.Impl.MlKem.AArch64.Encode
meta import VerifiedGarbage.Proof.Blowfish.AArch64.Lanes
meta import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Lanes
meta import VerifiedGarbage.Proof.MlKem.AArch64.Coeff16
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lane
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Mem
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Table
meta import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
meta import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Accept
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Advance
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Decode
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Invariant
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Loop
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Memory
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Steps
meta import VerifiedGarbage.Proof.MlKem.Compress

/-! # The complete SIMD/scalar rejection loop has public-seed-only timing -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

def finish : Prog isa := .seq fix (.block [.subImm .x .x0 .x4 1,.lsr .x .x0 .x0 63])

theorem finish_ct : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x3,.x4])) finish := by
  unfold finish
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x3,.x4])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem loop_relCT {w16 : Bool} {initial : List Zq} {N : Nat} {B : Nat → Byte} {bP aP : Addr}
    {s₀ u₀ : State} (ps : EnvW w16 N B bP aP s₀) (pu : EnvW w16 N B bP aP u₀)
    (hsp : s₀.sp=u₀.sp) (htab : s₀.gpr .x16=u₀.gpr .x16) (hN : 0<N) (hm : N%4=0) :
    RelCT isa (PairInvW w16 initial N B bP aP s₀ u₀ 0) (Impl.MlKem.AArch64.Rej8.rejLoop w16)
      (fun s u => PostW w16 initial N B aP s₀ s ∧ PostW w16 initial N B aP u₀ u) := by
  have hct : RelCT isa (PairInvW w16 initial N B bP aP s₀ u₀ 0) (Impl.MlKem.AArch64.Rej8.rejLoop w16)
      (fun _ _ => True) := by
    refine RelCT.seq (iters_relCT ps pu hsp htab hN hm) ?_
    intro s u tr ur s' u' hp es eu
    have hs := hp.1.acc
    have hu := hp.2.acc
    have htr := finish_ct s u tr ur s' u' trivial trivial
      ⟨hs.sp.trans (hsp.trans hu.sp.symm),fun r hr => by
        have hr' : r=.x3 ∨ r=.x4 := by
          simpa only [Taint.ofRegs,RegSet.mem_ofList,List.mem_cons,List.not_mem_nil,or_false] using hr
        rcases hr' with rfl|rfl
        · rw [hs.x3,hu.x3]
        · exact BitVec.eq_of_toNat_eq (hs.x4.trans hu.x4.symm)⟩ es eu
    exact ⟨htr,trivial⟩
  intro s u tr ur s' u' hp es eu
  have htr := (hct s u tr ur s' u' hp es eu).1
  obtain ⟨_,a,ea,ha⟩ := loop_ok ps hN hm hp.1 hp.2.2.1
  obtain ⟨_,b,eb,hb⟩ := loop_ok pu hN hm hp.2.1 hp.2.2.2
  obtain ⟨_,rfl⟩ := Exec.det es ea
  obtain ⟨_,rfl⟩ := Exec.det eu eb
  exact ⟨htr,ha,hb⟩

end VG.Proof.MlKem.AArch64.Rej8
