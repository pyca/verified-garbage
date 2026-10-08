import VerifiedGarbage.Proof.Weierstrass.X86.NafDigitTiming
import VerifiedGarbage.Proof.Weierstrass.X86.NafStep

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

def NafRunPair (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C)
    (β : Nat → BitVec 8) (e : Nat) (counter : BitVec 32) (s t : State) : Prop :=
  (∃ E,FieldPair K.M base size C.p (·∈nafSlots K) (nafLive K) E counter s t) ∧
    NafCore K C base size P β e s ∧ NafCore K C base size P β e t

theorem nafDigit_relCT {F : Spec.Weierstrass.Mont.Modulus}
    {K : WinCfg} {C : Curve} {base : Addr} {size wk k j : Nat} {P : Point C}
    (hL : NafLay K size) (hJ : K.J=65) (hW : WkOk F K.M C.p size wk (·∈nafSlots K))
    (hBitsWk : K.bits+260≤wk) (hm : UnitMod C.p (2^(64*K.M.n)))
    (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p) (hj : j<257) (hP : onCurve C P=true)
    (hc : NafDigitChecks K F) :
    RelCT isa (NafRunPair K C base size P (Naf5.byte k) (2*Naf5.residual k (j+1)) (BitVec.ofNat 32 j))
      (Naf.digit K F)
      (NafRunPair K C base size P (Naf5.byte k) (Naf5.residual k j) (BitVec.ofNat 32 j)) := by
  have raw : RelCT isa (NafRunPair K C base size P (Naf5.byte k) (2*Naf5.residual k (j+1)) (BitVec.ofNat 32 j))
      (Naf.digit K F)
      (fun s t => ∃ E,FieldPair K.M base size C.p (·∈nafSlots K) (nafLive K) E (BitVec.ofNat 32 j) s t) := by
    intro s t ts tt u v ⟨⟨E,h⟩,cs,ct⟩ es et
    exact nafDigit_fields_relCT hL hJ hW hm hOne hj hc _ _ _ _ _ _
      ⟨h,cs.stable.bits j hj,ct.stable.bits j hj⟩ es et
  exact raw.wp (fun s t ⟨⟨_,h⟩,cs,ct⟩ =>
    ⟨WP.mono (nafDigit_ok hL hJ hW hBitsWk hm hC ha hOne hj hP cs h.count₁) (fun _ h => h.2),
     WP.mono (nafDigit_ok hL hJ hW hBitsWk hm hC ha hOne hj hP ct h.count₂) (fun _ h => h.2)⟩)

theorem nafDoubleCore_relCT {counter : BitVec 32} {F : Spec.Weierstrass.Mont.Modulus}
    {K : WinCfg} {C : Curve} {base : Addr} {size wk e : Nat} {P : Point C} {β : Nat → BitVec 8}
    (hL : NafLay K size) (hJ : K.J=65) (hW : WkOk F K.M C.p size wk (·∈nafSlots K))
    (hBitsWk : K.bits+260≤wk) (hm : UnitMod C.p (2^(64*K.M.n)))
    (hC : Law C) (ha : AM3 C) (hP : onCurve C P=true)
    (hd : ScratchCT (fprog F (dblJMul K.S K.R K.D)))
    (hcp : ScratchCT (.block (copyPt K.M.n K.R K.D))) :
    RelCT isa (NafRunPair K C base size P β e counter)
      (.seq (fprog F (dblJMul K.S K.R K.D)) (.block (copyPt 4 K.R K.D)))
      (NafRunPair K C base size P β (2*e) counter) := by
  have raw := (RelCT.exists_ (fun E => nafDouble_relCT (E:=E) (counter:=counter)
    (base:=base) hL hW hm hd hcp)).mono
    (P':=NafRunPair K C base size P β e counter) (fun _ _ h => h.1) (fun _ _ h => h)
  exact raw.wp (fun _ _ ⟨_,cs,ct⟩ =>
    ⟨WP.mono (nafDoubleCore_ok hL hW hBitsWk hJ hm hC ha hP cs) (fun _ h => h.2),
     WP.mono (nafDoubleCore_ok hL hW hBitsWk hJ hm hC ha hP ct) (fun _ h => h.2)⟩)

end VG.Proof.Weierstrass.X86
