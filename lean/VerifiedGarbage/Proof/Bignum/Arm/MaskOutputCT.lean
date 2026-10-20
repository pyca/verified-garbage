module
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.Bignum.Arm.MaskOutput
public import VerifiedGarbage.Proof.Mont.Words

import VerifiedGarbage.Proof.Bignum.Arm.MaskBytesCT
import VerifiedGarbage.Proof.Bignum.Arm.MaskOutputArgs
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Impl.Bignum.Arm.MaskOutput
meta import VerifiedGarbage.Proof.Mont.Words
meta import VerifiedGarbage.Proof.Bignum.Arm.MaskBytesCT
meta import VerifiedGarbage.Proof.Bignum.Arm.MaskOutputArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # The output acceptance bit affects bytes and return status, never leakage -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont

theorem maskOutputArgs_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block maskOutputArgs) (fun _ _ => True) := by
  have head : RelCT isa (fun s t => s.sp = t.sp)
      (.block [.mov .r0 (.reg .r4), .mov .lr (.reg .r6)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  have tail : RelCT isa (fun s t => s.sp = t.sp)
      (.block [.mov .r2 (.imm 0), .dp .sub .r2 .r2 (.reg .r4)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  exact RelCT.block_append (M := isa) (l₁ := [.mov .r0 (.reg .r4), .mov .lr (.reg .r6)])
    (l₂ := [.ldrSp .r4 48, .mov .r2 (.imm 0), .dp .sub .r2 .r2 (.reg .r4)])
    ((relCT_keep_sp head (fun _ _ h => h)).seq
      (RelCT.block_append (M := isa) (l₁ := [.ldrSp .r4 48])
        (l₂ := [.mov .r2 (.imm 0), .dp .sub .r2 .r2 (.reg .r4)]) ((loadStack_ct .r4 48).seq tail)))

structure MaskOutputInput (dst : BitVec 32) (k : Nat) (s : State) : Prop where
  ptr : s.gpr .r4 = dst
  count : s.gpr .r6 = BitVec.ofNat 32 k
  stackFit : s.sp.toNat + 52 ≤ 2 ^ 32
  read : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 48) 4

theorem maskOutput_ct {dst : BitVec 32} {k : Nat} :
    RelCT isa (fun s t => MaskOutputInput dst k s ∧ MaskOutputInput dst k t ∧ s.sp = t.sp)
      maskOutput (fun _ _ => True) := by
  let P := fun (s t : State) => MaskOutputInput dst k s ∧ MaskOutputInput dst k t ∧ s.sp = t.sp
  let Q := fun s : State => s.gpr .r0 = dst ∧ s.gpr .lr = BitVec.ofNat 32 k
  have args := (maskOutputArgs_ct.mono (P' := P) (fun _ _ h => h.2.2) (fun _ _ h => h)).wp
    (F₁ := Q) (F₂ := Q) (fun s t h => ⟨
      WP.mono (maskOutputArgs_ok s h.1.stackFit h.1.read) (fun _ j => ⟨j.1.trans h.1.ptr, j.2.1.trans h.1.count⟩),
      WP.mono (maskOutputArgs_ok t h.2.1.stackFit h.2.1.read) (fun _ j => ⟨j.1.trans h.2.1.ptr, j.2.1.trans h.2.1.count⟩)⟩)
  have loop : RelCT isa (fun s t => True ∧ Q s ∧ Q t) maskBytes (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact ⟨maskBytes_ct s t tr1 tr2 u v trivial trivial
      ⟨h.2.1.1.trans h.2.2.1.symm, h.2.1.2.trans h.2.2.2.symm⟩ e1 e2, trivial⟩
  have ret : RelCT isa (fun _ _ => True) (.block [.mov .r0 (.reg .r4)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  exact args.seq (loop.seq ret)

end VG.Proof.Bignum.Arm
