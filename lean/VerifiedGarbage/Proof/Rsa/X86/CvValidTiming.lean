module
public import VerifiedGarbage.Proof.Rsa.X86.CvBody
public import VerifiedGarbage.Proof.Rsa.X86.CvPair

import VerifiedGarbage.Proof.Rsa.X86.CvDispatchTiming
import VerifiedGarbage.Proof.Rsa.X86.CvSizedTiming
import VerifiedGarbage.Proof.Rsa.X86.CvValid
import VerifiedGarbage.Proof.Bignum.X86.PublicDispatch
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # CRT limb-width selection depends only on the public modulus length -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum.X86 VG.Proof.Dsa.X86 VG.Impl.Bignum.X86
open VG.Impl.Rsa.X86.CrtValues

theorem Pair.keepMem {g : CallGeometry} {s t u v : State} {regs : List Reg} (h : Pair g s t)
    (ks : Keeps regs s u) (kt : Keeps regs t v) (di : .edi ∉ regs) (sp : .esp ∉ regs)
    (ms : u.mem = s.mem) (mt : v.mem = t.mem) : Pair g u v :=
  h.after (h.left.after ks di sp (by rw [ms]; exact Frame.refl _ _))
    (h.right.after kt di sp (by rw [mt]; exact Frame.refl _ _)) ks kt sp

theorem valid_relCT (g : CallGeometry) (len : Lengths g) :
    RelCT isa (Pair g) valid (fun _ _ => True) := by
  let p := fun s t => Pair g s t ∧ s.gpr .eax = BitVec.ofNat 32 g.n ∧ t.gpr .eax = BitVec.ofNat 32 g.n
  have setup : RelCT isa (Pair g)
      (.block [.mov .eax (.mem (PublicFn.argument 7)), .alu .add .eax (.imm 7), .shift .shr .eax 3]) p := by
    intro s t tr ur sf tf h es et
    have trace : RelCT isa (VG.X86.Taint.Agree argumentTaint)
        (.block [.mov .eax (.mem (PublicFn.argument 7)), .alu .add .eax (.imm 7), .shift .shr .eax 3])
        (VG.X86.Taint.Agree argumentTaint) := checkedProgramChange (hint := .block []) rfl rfl
    obtain ⟨ws, ms, ks⟩ := wp_result (width_ok len.upper
      (by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using (h.left.arguments 7 (by decide)).readSrc)) es
    obtain ⟨wt, mt, kt⟩ := wp_result (width_ok len.upper
      (by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using (h.right.arguments 7 (by decide)).readSrc)) et
    exact ⟨(trace _ _ _ _ _ _ h.agree es et).1,
      h.keepMem ks kt (by decide) (by decide) ms mt, len.width ▸ ws, len.width ▸ wt⟩
  refine VG.RelCT.seq setup ?_
  apply dispatch_relCT PublicFn.widths g.n p
    (by rw [len.width]; exact publicWidths_member len.lower len.upper) (by decide)
    (fun _ _ h => h.2)
  · intro s t u v h ks kt ms mt
    exact ⟨h.1.keepMem ks kt (by simp) (by simp) ms mt,
      (ks.1 .eax (by simp)).trans h.2.1, (kt.1 .eax (by simp)).trans h.2.2⟩
  · exact (sized_relCT g).mono (fun _ _ h => h.1) (fun _ _ h => h)

end VG.Proof.Rsa.X86.CrtValues
