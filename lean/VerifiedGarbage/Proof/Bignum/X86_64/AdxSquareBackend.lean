import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRawCrossCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRaw
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledMontCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8CT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareDispatch
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledChoiceCT

/-! ## AdxTiledSquareRawCT -/
section

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxTiledProduct (Layout GoodV pins_goodV)

theorem rawCross_fw {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8) (ha1 : a≠aAcc)
    (ha2 : a≠aTmp) (L : Layout) (s : State) (h : GoodV ps L s) :
    WP isa (AdxTiledSquare.rawCross ca) s (GoodV ps L) := by
  obtain ⟨⟨mi,hg⟩,hv⟩ := h
  exact WP.mono (rawCross_ok hg.scr hg.rdi hg.hdr hv pa L.hZ L.hw L.hwN L.hn ha ha1 ha2)
    fun _ ⟨_,_,o,k⟩ => AdxTiledProduct.GoodV.of_outside ⟨⟨mi,hg⟩,hv⟩ o k

def Ready (ps : List (Nat × Nat)) (a : Nat) (L : Layout) (s : State) : Prop :=
  GoodV ps L s ∧ s.gpr .r8=off L.B (slot L.w aAcc+16) ∧
    s.gpr .r9=off L.B (slot L.w a) ∧ s.gpr .rbx=BitVec.ofNat 64 L.w

theorem setup_ready {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (L : Layout) (s : State)
    (h : GoodV ps L s) : WP isa (.block (Adx.setup ca)) s (Ready ps a L) := by
  obtain ⟨⟨mi,hg⟩,hv⟩ := h
  exact WP.mono (adxSetupV_ok hg.scr hg.rdi hg.hdr L.hZ (hv.at pa) (hv.lt pa)) fun _ ⟨p9,_,p8,pbx,m,k⟩ =>
    ⟨⟨⟨mi,hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,m ▸ hg.hdr⟩,m ▸ hv⟩,p8,p9,pbx⟩

theorem raw_ct {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8) (ha1 : a≠aAcc)
    (ha2 : a≠aTmp)
    {h₁ h₂ h₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (Adx.setup ca)) h₁).isSome=true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca ca)) h₂).isSome=true)
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxTri8.setup ca)) h₃).isSome=true) :
    RelCT isa (Two (GoodV ps)) (AdxTiledSquare.rawSquare ca) (fun _ _ => True) := by
  unfold AdxTiledSquare.rawSquare
  refine RelCT.seq (two_post (rawCross_ct pa ha ha1 ha2 hS hR hT) (rawCross_fw pa ha ha1 ha2)) ?_
  refine RelCT.seq (two_piece [.rdi] (pins_goodV ps) hS (setup_ready pa)) ?_
  refine two_taint [.rdi,.r8,.r9,.rbx] ?_ (by taint_decide)
  intro L s t hs ht r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact pins_goodV ps L s t hs.1 ht.1 .rdi (by simp)
  · exact hs.2.1.trans ht.2.1.symm
  · exact hs.2.2.1.trans ht.2.2.1.symm
  · exact hs.2.2.2.trans ht.2.2.2.symm

theorem raw_fw {ps : List (Nat × Nat)} {ca a : Nat} (pa : (ca, a) ∈ ps) (ha : a<8) (ha1 : a≠aAcc)
    (ha2 : a≠aTmp) (L : Layout) (s : State) (h : GoodV ps L s) :
    WP isa (AdxTiledSquare.rawSquare ca) s (GoodV ps L) := by
  obtain ⟨⟨mi,hg⟩,hv⟩ := h
  exact WP.mono (rawSquare_ok hg.scr hg.rdi hg.hdr L.hZ L.hwN L.hn L.hw hv pa ha ha1 ha2)
    fun _ ⟨_,_,o,k⟩ => AdxTiledProduct.GoodV.of_outside ⟨⟨mi,hg⟩,hv⟩ o k

end VG.Proof.Bignum.X86_64.AdxTiledSquare

end

/-! ## AdxTiledSquareMontCT -/
section

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

open VG.Proof.Bignum.X86_64.AdxTiledProduct (Layout GoodV pins_goodV)

theorem montSquare_ct {ps : List (Nat × Nat)} {co ca o a : Nat} (po : (co, o) ∈ ps) (pa : (ca, a) ∈ ps)
    (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    {h₁ h₂ h₃ h₄ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (Adx.setup ca)) h₁).isSome=true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca ca)) h₂).isSome=true)
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (Adx.finishBases co)) h₃).isSome=true)
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxTri8.setup ca)) h₄).isSome=true) :
    RelCT isa (Two (GoodV ps)) (AdxTiledSquare.montSquare co ca) (fun _ _ => True) :=
  RelCT.seq (two_post (raw_ct pa ha ha1 ha2 hS hR hT) (raw_fw pa ha ha1 ha2))
    (AdxTiledProduct.redcFinish_ct (P := fun _ => ps) (L := id) (O := fun _ => o) (fun _ => po) hF)

end VG.Proof.Bignum.X86_64.AdxTiledSquare

end

/-! ## AdxTiledSquareDispatchCT -/
section

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.Adx
open VG.Proof.Bignum.X86_64

theorem aligned_ct {o a : Nat} (ho : o<8) (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    {h₁ h₂ h₃ h₄ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (setup a)) h₁).isSome=true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup a a)) h₂).isSome=true)
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (finishBases o)) h₃).isSome=true)
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxTri8.setup a)) h₄).isSome=true) :
    RelCT isa (Two fun L s => AdxSquare.GW L s ∧ L.w%8=0)
      (AdxTiledSquare.montSquare o a) (fun _ _ => True) := by
  intro s t ts tt s' t' ⟨L,⟨⟨⟨mi,gs,hZ⟩,sz⟩,h8⟩,⟨⟨⟨mj,gt,_⟩,_⟩,_⟩⟩ es et
  have hw := sz.lt
  have hp := sz.2.1
  let R : AdxTiledProduct.Layout := ⟨L.B,L.Z,L.w,L.w/8,hZ,hw,by omega,by omega⟩
  exact montSquare_ct (ps := [(o,o),(a,a),(a,a)]) (.head _) (.tail _ (.head _)) ha ha1 ha2 hS hR hF hT
    _ _ _ _ _ _ ⟨R,⟨⟨mi,gs⟩,gs.hdr.ops3 ho ha ha⟩,⟨mj,gt⟩,gt.hdr.ops3 ho ha ha⟩ es et

theorem alignedChoice_ct {o a : Nat} (ho : o<8) (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    {h₁ h₂ h₃ h₄ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (setup a)) h₁).isSome=true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup a a)) h₂).isSome=true)
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (finishBases o)) h₃).isSome=true)
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxTri8.setup a)) h₄).isSome=true) :
    RelCT isa (Two AdxSquare.GW) (AdxTiledSquare.alignedChoice o a) (fun _ _ => True) := by
  unfold AdxTiledSquare.alignedChoice
  refine RelCT.seq (two_piece (Ψ := fun L s => AdxSquare.GW L s ∧ s.zf=some (decide (L.w%8=0)))
    [.rdi] AdxSquare.pins_gw (by taint_decide) ?_) ?_
  · intro L s ⟨⟨mi,hg,hZ⟩,sz⟩
    exact WP.mono (AdxSquare.redcTest_ok hg.scr hg.rdi hg.hdr hZ (by have := sz.lt; omega))
      fun _ ⟨z,m,k⟩ => ⟨⟨⟨mi,⟨hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,m ▸ hg.hdr⟩,hZ⟩,sz⟩,z⟩
  refine two_ite (fun L s t hs ht => by simp only [eval,hs.2,ht.2]) ?_ ?_
  · refine two_map id (fun L s ⟨⟨h,z⟩,e⟩ => ⟨h,?_⟩) (aligned_ct ho ha ha1 ha2 hS hR hF hT)
    simp only [eval,z,Option.some.injEq,decide_eq_true_eq] at e
    exact e
  · exact two_map id (fun _ _ h => h.1.1) (AdxSquare.montSquare_ct ho ha ha1 ha2 hS hF)

theorem choice_ct {o a : Nat} (ho : o<8) (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    {h₀ h₁ h₂ h₃ h₄ h₅ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hM : (taint.check (Taint.ofRegs [.rdi]) (.block (bases o a a aN aAcc aTmp)) h₀).isSome=true)
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (setup a)) h₁).isSome=true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (rowBase a)) h₂).isSome=true)
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (finishBases o)) h₃).isSome=true)
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup a a)) h₄).isSome=true)
    (hTri : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxTri8.setup a)) h₅).isSome=true) :
    RelCT isa (Two GoodW) (AdxTiledSquare.choice o a) (fun _ _ => True) := by
  unfold AdxTiledSquare.choice
  refine RelCT.seq (two_piece (Ψ := fun L s => GoodW L s ∧ s.zf=some (decide (SizeOk L.w)))
    [.rdi] pins_goodW (by taint_decide) ?_) ?_
  · intro L s ⟨mi,hg,hZ⟩
    exact WP.mono (sizeTest_ok hg.scr hg.rdi hg.hdr hZ) fun _ ⟨z,m,k⟩ =>
      ⟨⟨mi,⟨hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,m ▸ hg.hdr⟩,hZ⟩,z⟩
  refine two_ite (fun L s t hs ht => by simp only [eval,hs.2,ht.2]) ?_ ?_
  · refine two_map id (fun L s ⟨⟨h,z⟩,e⟩ => ⟨h,?_⟩) (alignedChoice_ct ho ha ha1 ha2 hS hT hF hTri)
    simp only [eval,z,Option.some.injEq,decide_eq_true_eq] at e
    exact e
  · exact two_map id (fun _ _ h => h.1.1) (montMulAdx_ct ho ha ha ha1 ha2 ha1 ha2 hM hS hR hF)

end VG.Proof.Bignum.X86_64.AdxTiledSquare

end

/-! ## AdxSquareBackend -/
section

/-! The ADX Montgomery backend with specialized squaring. -/
namespace VG.Proof.Bignum.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.Adx
open VG.Proof.MlKem.X86_64

theorem squareDispatch_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hB : wv s.mem B (slot w b) w < wv s.mem B (slot w aN) w) :
    WP isa (AdxSquare.montMul o a b) s fun t =>
      wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w b) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  unfold AdxSquare.montMul
  by_cases hab : a ≠ b
  · rw [ite_eq_right hab]
    exact montMulAdx_ok hs hdi hH hZ hw hw' ho ha hb ho1 ho2 ha1 ha2 hb1 hb2 hinv hB
  have hab : a = b := Classical.not_not.mp hab
  rw [ite_eq_left hab]
  subst b
  refine WP.seq (WP.mono (sizeTest_ok hs hdi hH hZ) fun s₁ ⟨hz, hm₁, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  have hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hdi
  rw [← hm₁] at hinv hB hH ⊢
  have post : ∀ t, (wv t.mem B (slot w o) w < wv s₁.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s₁.mem B (slot w aN) w =
        wv s₁.mem B (slot w a) w * wv s₁.mem B (slot w a) w % wv s₁.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s₁.mem t.mem ∧ Keep mmRegs s₁ t) →
      (wv t.mem B (slot w o) w < wv s₁.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s₁.mem B (slot w aN) w =
        wv s₁.mem B (slot w a) w * wv s₁.mem B (slot w a) w % wv s₁.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s₁.mem t.mem ∧ Keep mmRegs s t) :=
    fun t ⟨h1, h2, h3, k⟩ => ⟨h1, h2, h3, (k₁.trans k).mono (by decide)⟩
  by_cases h4 : SizeOk w
  · refine WP.ite true (by simp [eval, hz, h4]) (fun _ => WP.mono (AdxSquare.montSquare_ok hs₁ hdi₁ hH hZ hw hw' ho ha ho1 ho2 ha1 ha2 hinv hB) post) (by simp)
  · refine WP.ite false (by simp [eval, hz, h4]) (by simp) (fun _ =>
      WP.mono (montMulAdx_ok hs₁ hdi₁ hH hZ hw hw' ho ha ha ho1 ho2 ha1 ha2 ha1 ha2 hinv hB) post)

theorem squareDispatch_ct {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    {hc₀ hc₁ hc₂ hc₃ hc₄ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hM : (taint.check (Taint.ofRegs [.rdi]) (.block (bases o a b aN aAcc aTmp)) hc₀).isSome = true)
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (setup b)) hc₁).isSome = true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (rowBase a)) hc₂).isSome = true)
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (finishBases o)) hc₃).isSome = true)
    (hA : (taint.check (Taint.ofRegs [.rdi]) (.block (setup a)) hc₄).isSome = true) :
    RelCT isa (Two GoodW) (AdxSquare.montMul o a b) (fun _ _ => True) := by
  have old := montMulAdx_ct ho ha hb ha1 ha2 hb1 hb2 hM hS hR hF
  unfold AdxSquare.montMul
  by_cases hab : a ≠ b
  · rw [ite_eq_right hab]; exact old
  rw [ite_eq_left (Classical.not_not.mp hab)]
  refine RelCT.seq (two_piece (Ψ := fun L s => GoodW L s ∧ s.zf = some (decide (SizeOk L.w))) [.rdi] pins_goodW
    (by taint_decide) fun L s ⟨mi, hg, hZ⟩ => WP.mono (sizeTest_ok hg.scr hg.rdi hg.hdr hZ) fun t ⟨hz, hm, k⟩ =>
      ⟨⟨mi, ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi, hm ▸ hg.hdr⟩, hZ⟩, hz⟩) ?_
  refine two_ite (fun L s₁ s₂ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) ?_ ?_
  · refine two_map id (fun L s ⟨⟨hg, hz⟩, he⟩ => ⟨hg, ?_⟩)
      (AdxSquare.montSquare_ct ho ha ha1 ha2 hA hF)
    simp only [eval, hz, Option.some.injEq, decide_eq_true_eq] at he
    exact he
  · exact two_map id (fun L s h => h.1.1) old

theorem tiledDispatch_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hB : wv s.mem B (slot w b) w < wv s.mem B (slot w aN) w) :
    WP isa (AdxTiledSquare.dispatch o a b) s fun t =>
      wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w b) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  unfold AdxTiledSquare.dispatch
  by_cases hab : a=b
  · rw [ite_eq_left hab]
    subst b
    exact AdxTiledSquare.choice_ok hs hdi hH hZ hw hw' ho ha ho1 ho2 ha1 ha2 hinv hB
  · rw [ite_eq_right hab]
    exact AdxTiledProduct.choice_ok hs hdi hH hZ hw hw' ho ha hb ho1 ho2 ha1 ha2 hb1 hb2 hinv hB

theorem tiledDispatch_ct {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    {hc₀ hc₁ hc₂ hc₃ hc₄ hc₅ hc₆ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hM : (taint.check (Taint.ofRegs [.rdi]) (.block (bases o a b aN aAcc aTmp)) hc₀).isSome = true)
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (setup b)) hc₁).isSome = true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (rowBase a)) hc₂).isSome = true)
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (finishBases o)) hc₃).isSome = true)
    (hA : (taint.check (Taint.ofRegs [.rdi]) (.block (setup a)) hc₄).isSome = true)
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup a b)) hc₅).isSome = true)
    (hTri : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxTri8.setup a)) hc₆).isSome = true) :
    RelCT isa (Two GoodW) (AdxTiledSquare.dispatch o a b) (fun _ _ => True) := by
  unfold AdxTiledSquare.dispatch
  by_cases hab : a=b
  · rw [ite_eq_left hab]
    subst b
    exact AdxTiledSquare.choice_ct ho ha ha1 ha2 hM hA hR hF hT hTri
  · rw [ite_eq_right hab]
    exact AdxTiledProduct.choice_ct ho ha hb ha1 ha2 hb1 hb2 hM hS hR hF hT

/-- Montgomery multiplication with a specialized ADX square. -/
def Mont.adxSquare : Mont where
  mm := AdxTiledSquare.dispatch
  ok hg hZ hw hw' _ _ _ ho ha hb d1 d2 d3 d4 d5 d6 hinv hB :=
    WP.mono (tiledDispatch_ok hg.scr hg.rdi hg.hdr hZ hw hw' ho ha hb d1 d2 d3 d4 d5 d6 hinv hB)
      fun t' ⟨h1, h2, h3, k⟩ => ⟨⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi, h3.hdr hg.hdr⟩,
        h1, h2, h3, k⟩
  ct := by
    intro o a b h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    exact tiledDispatch_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)

end VG.Proof.Bignum.X86_64

end
