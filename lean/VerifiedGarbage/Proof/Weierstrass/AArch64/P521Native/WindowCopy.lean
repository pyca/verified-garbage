module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowDoublePair
public import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddCall
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-! Copy the fifth double back to the accumulator before signed addition. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Proof.Mont.AArch64.P521Field
open VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass.AArch64.P521Native

 def windowCopy : List Instr := copyPt 9 ⟨1072,1144,1216⟩ ⟨1288,1360,1432⟩

 theorem window_copy_source : outerBlock142.take 54=windowCopy := by decide

 theorem window_copy_ok {base : Addr} {s : State} (hs : Scr s base 8192)
    (bound : canonicalPoint s.mem base 1288) :
    WP isa (.block windowCopy) s fun t =>
      canonicalPoint t.mem base 1072 ∧ ordinaryPoint t.mem base 1072=ordinaryPoint s.mem base 1288 ∧
      KeepRegs [.x1] s t ∧ Unch base [(1072,72),(1144,72),(1216,72)] s.mem t.mem := by
  refine WP.mono (VG.Proof.Weierstrass.AArch64.copyPt_ok hs (n:=9)
    (o:=⟨1072,1144,1216⟩) (a:=⟨1288,1360,1432⟩)
    (by decide) (by decide) (by decide) (by decide) (by decide)) fun t ⟨ex,ey,ez,k,f⟩ => ?_
  refine ⟨?_,?_,k,f⟩
  · change wordsVal t.mem base 1072 9<_ ∧ wordsVal t.mem base 1144 9<_ ∧ wordsVal t.mem base 1216 9<_
    rw [ex,ey,ez]
    exact bound
  · change (Fin.ofNat _ (wordsVal t.mem base 1072 9),Fin.ofNat _ (wordsVal t.mem base 1144 9),
      Fin.ofNat _ (wordsVal t.mem base 1216 9))=_
    rw [ex,ey,ez]
    rfl

end VG.Proof.Weierstrass.AArch64.P521Native
