module

public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishAdd
public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.Code
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddCall
import VerifiedGarbage.Proof.Framework.Lit

/-! Exact final point copies retain canonical coordinates and the memory frame. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Weierstrass.AArch64.P521Native

def finishCopyPoint : List Instr := copyPt 9 ⟨1072,1144,1216⟩ ⟨1288,1360,1432⟩

theorem finish_copy_source149 : outerBlock149.take 54=finishCopyPoint := by lit_decide

theorem finish_copy_source166 : outerBlock166.drop 53=finishCopyPoint := by lit_decide

theorem finish_copy_point_ok {base : Addr} {s : State} (hs : Scr s base 8192) :
    WP isa (.block finishCopyPoint) s fun t =>
      wordsVal t.mem base 1072 9=wordsVal s.mem base 1288 9 ∧
      wordsVal t.mem base 1144 9=wordsVal s.mem base 1360 9 ∧
      wordsVal t.mem base 1216 9=wordsVal s.mem base 1432 9 ∧
      KeepRegs [.x1] s t ∧ Unch base [(1072,72),(1144,72),(1216,72)] s.mem t.mem := by
  exact VG.Proof.Weierstrass.AArch64.copyPt_ok hs (n:=9)
    (o:=⟨1072,1144,1216⟩) (a:=⟨1288,1360,1432⟩)
    (by decide) (by decide) (by decide) (by decide) (by decide)

end VG.Proof.Weierstrass.AArch64.P521Native
