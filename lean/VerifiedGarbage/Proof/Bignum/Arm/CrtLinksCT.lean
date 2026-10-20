module
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.Bignum.Arm.CrtSetup
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace

import VerifiedGarbage.Proof.Bignum.Arm.StageCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtStrides
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Impl.Bignum.Arm.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.Arm.Workspace
meta import VerifiedGarbage.Proof.Bignum.Arm.StageCT
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtStrides
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # CRT link setup uses only public buffer geometry -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont

structure CrtLinksInput (base : BitVec 32) (size w : Nat) (s : State) : Prop where
  workspace : Workspace s base size
  ptr : s.gpr .r0 = base
  count : s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w

theorem crt_links_ct {base : BitVec 32} {size w : Nat} (fit : 52 ≤ size) :
    RelCT isa (fun s t => CrtLinksInput base size w s ∧ CrtLinksInput base size w t) links (fun _ _ => True) := by
  let P := CrtLinksInput base size w
  let Q := fun s : State => s.gpr .r0 = base ∧ s.gpr .r7 = BitVec.ofNat 32 w ∧
    s.gpr .r1 = BitVec.ofNat 32 (stride w) ∧ s.gpr .r2 = base
  have head : RelCT isa (fun s t => P s ∧ P t) (.block linkStride) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.ptr.trans h.2.ptr.symm
  have wp (s : State) (h : P s) : WP isa (.block linkStride) s Q := by
    refine WP.mono (crt_linkStride_ok s h.workspace fit h.ptr h.count) ?_
    rintro t ⟨width, step, current, _, rest⟩
    exact ⟨(rest.gpr .r0 (by simp)).trans h.ptr, width, step, current⟩
  have tail : RelCT isa (fun s t => Q s ∧ Q t) linksTail (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r7, .r1, .r2]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.1.1.trans h.2.1.symm
    · exact h.1.2.1.trans h.2.2.1.symm
    · exact h.1.2.2.1.trans h.2.2.2.1.symm
    · exact h.1.2.2.2.trans h.2.2.2.2.symm
  exact (pair_posts head wp).seq tail

end VG.Proof.Bignum.Arm
