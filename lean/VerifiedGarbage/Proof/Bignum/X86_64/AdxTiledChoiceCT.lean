import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledMontCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareCT

/-! ## AdxTiledChoice -/
section

namespace VG.Proof.Bignum.X86_64.AdxTiledProduct
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.Adx
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

theorem alignedChoice_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hB : wv s.mem B (slot w b) w < wv s.mem B (slot w aN) w) :
    WP isa (AdxTiledProduct.alignedChoice o a b) s fun t =>
      wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w b) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  unfold AdxTiledProduct.alignedChoice
  refine WP.seq (WP.mono (AdxSquare.redcTest_ok hs hdi hH hZ (by omega)) fun s₁ ⟨hz, hm₁, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  have hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hdi
  rw [← hm₁] at hinv hB hH ⊢
  have post : ∀ t, (wv t.mem B (slot w o) w < wv s₁.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s₁.mem B (slot w aN) w =
        wv s₁.mem B (slot w a) w * wv s₁.mem B (slot w b) w % wv s₁.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s₁.mem t.mem ∧ Keep mmRegs s₁ t) →
      (wv t.mem B (slot w o) w < wv s₁.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s₁.mem B (slot w aN) w =
        wv s₁.mem B (slot w a) w * wv s₁.mem B (slot w b) w % wv s₁.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s₁.mem t.mem ∧ Keep mmRegs s t) :=
    fun t ⟨h1, h2, h3, k⟩ => ⟨h1, h2, h3, (k₁.trans k).mono (by decide)⟩
  by_cases h8 : w%8=0
  · refine WP.ite true (by simp [eval,hz,h8]) (fun _ => WP.mono
      (montMul_ok hs₁ hdi₁ hH hZ (by omega : w=8*(w/8)) (by omega) hw' (hH.ops3 ho ha hb) (.head _) (.tail _ (.head _)) (.tail _ (.tail _ (.head _))) ho ha hb ho1 ho2 ha1 ha2 hb1 hb2 hinv hB) post) (by simp)
  · refine WP.ite false (by simp [eval,hz,h8]) (by simp) (fun _ =>
      WP.mono (montMulAdx_ok hs₁ hdi₁ hH hZ hw hw' ho ha hb ho1 ho2 ha1 ha2 hb1 hb2 hinv hB) post)

theorem choice_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hB : wv s.mem B (slot w b) w < wv s.mem B (slot w aN) w) :
    WP isa (AdxTiledProduct.choice o a b) s fun t =>
      wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w b) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  unfold AdxTiledProduct.choice
  refine WP.seq (WP.mono (sizeTest_ok hs hdi hH hZ) fun s₁ ⟨hz, hm₁, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  have hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hdi
  rw [← hm₁] at hinv hB hH ⊢
  have post : ∀ t, (wv t.mem B (slot w o) w < wv s₁.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s₁.mem B (slot w aN) w =
        wv s₁.mem B (slot w a) w * wv s₁.mem B (slot w b) w % wv s₁.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s₁.mem t.mem ∧ Keep mmRegs s₁ t) →
      (wv t.mem B (slot w o) w < wv s₁.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s₁.mem B (slot w aN) w =
        wv s₁.mem B (slot w a) w * wv s₁.mem B (slot w b) w % wv s₁.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s₁.mem t.mem ∧ Keep mmRegs s t) :=
    fun t ⟨h1, h2, h3, k⟩ => ⟨h1, h2, h3, (k₁.trans k).mono (by decide)⟩
  by_cases h8 : SizeOk w
  · refine WP.ite true (by simp [eval,hz,h8]) (fun _ => WP.mono
      (alignedChoice_ok hs₁ hdi₁ hH hZ hw hw' ho ha hb ho1 ho2 ha1 ha2 hb1 hb2 hinv hB) post) (by simp)
  · refine WP.ite false (by simp [eval,hz,h8]) (by simp) (fun _ =>
      WP.mono (montMulAdx_ok hs₁ hdi₁ hH hZ hw hw' ho ha hb ho1 ho2 ha1 ha2 hb1 hb2 hinv hB) post)

end VG.Proof.Bignum.X86_64.AdxTiledProduct

end

/-! ## AdxTiledChoiceCT -/
section

namespace VG.Proof.Bignum.X86_64.AdxTiledProduct
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.Adx
open VG.Proof.Bignum.X86_64

theorem aligned_ct {o a b : Nat} (ho : o<8) (ha : a<8) (hb : b<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hb1 : b≠aAcc) (hb2 : b≠aTmp)
    {h₁ h₂ h₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (setup b)) h₁).isSome=true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup a b)) h₂).isSome=true)
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (finishBases o)) h₃).isSome=true) :
    RelCT isa (Two fun L s => AdxSquare.GW L s ∧ L.w%8=0)
      (AdxTiledProduct.montMul o a b) (fun _ _ => True) := by
  intro s t ts tt s' t' ⟨L,⟨⟨⟨mi,gs,hZ⟩,sz⟩,h8⟩,⟨⟨⟨mj,gt,_⟩,_⟩,_⟩⟩ es et
  have hw := sz.lt
  have hp := sz.2.1
  let R : Layout := ⟨L.B,L.Z,L.w,L.w/8,hZ,hw,by omega,by omega⟩
  exact montMul_ct (ps := [(o,o),(a,a),(b,b)]) (.head _) (.tail _ (.head _)) (.tail _ (.tail _ (.head _))) ha hb ha1 ha2 hb1 hb2 hS hR hF
    _ _ _ _ _ _ ⟨R,⟨⟨mi,gs⟩,gs.hdr.ops3 ho ha hb⟩,⟨mj,gt⟩,gt.hdr.ops3 ho ha hb⟩ es et

theorem alignedChoice_ct {o a b : Nat} (ho : o<8) (ha : a<8) (hb : b<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hb1 : b≠aAcc) (hb2 : b≠aTmp)
    {h₀ h₁ h₂ h₃ h₄ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hM : (taint.check (Taint.ofRegs [.rdi]) (.block (bases o a b aN aAcc aTmp)) h₀).isSome=true)
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (setup b)) h₁).isSome=true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (rowBase a)) h₂).isSome=true)
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (finishBases o)) h₃).isSome=true)
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup a b)) h₄).isSome=true) :
    RelCT isa (Two AdxSquare.GW) (AdxTiledProduct.alignedChoice o a b) (fun _ _ => True) := by
  unfold AdxTiledProduct.alignedChoice
  refine RelCT.seq (two_piece (Ψ := fun L s => AdxSquare.GW L s ∧ s.zf=some (decide (L.w%8=0)))
    [.rdi] AdxSquare.pins_gw (by taint_decide) ?_) ?_
  · intro L s ⟨⟨mi,hg,hZ⟩,sz⟩
    exact WP.mono (AdxSquare.redcTest_ok hg.scr hg.rdi hg.hdr hZ (by have := sz.lt; omega))
      fun _ ⟨z,m,k⟩ => ⟨⟨⟨mi,⟨hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,m ▸ hg.hdr⟩,hZ⟩,sz⟩,z⟩
  refine two_ite (fun L s t hs ht => by simp only [eval,hs.2,ht.2]) ?_ ?_
  · refine two_map id (fun L s ⟨⟨h,z⟩,e⟩ => ⟨h,?_⟩) (aligned_ct ho ha hb ha1 ha2 hb1 hb2 hS hT hF)
    simp only [eval,z,Option.some.injEq,decide_eq_true_eq] at e
    exact e
  · exact two_map id (fun _ _ h => h.1.1.1) (montMulAdx_ct ho ha hb ha1 ha2 hb1 hb2 hM hS hR hF)

theorem choice_ct {o a b : Nat} (ho : o<8) (ha : a<8) (hb : b<8)
    (ha1 : a≠aAcc) (ha2 : a≠aTmp) (hb1 : b≠aAcc) (hb2 : b≠aTmp)
    {h₀ h₁ h₂ h₃ h₄ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hM : (taint.check (Taint.ofRegs [.rdi]) (.block (bases o a b aN aAcc aTmp)) h₀).isSome=true)
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (setup b)) h₁).isSome=true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (rowBase a)) h₂).isSome=true)
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (finishBases o)) h₃).isSome=true)
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup a b)) h₄).isSome=true) :
    RelCT isa (Two GoodW) (AdxTiledProduct.choice o a b) (fun _ _ => True) := by
  unfold AdxTiledProduct.choice
  refine RelCT.seq (two_piece (Ψ := fun L s => GoodW L s ∧ s.zf=some (decide (SizeOk L.w)))
    [.rdi] pins_goodW (by taint_decide) ?_) ?_
  · intro L s ⟨mi,hg,hZ⟩
    exact WP.mono (sizeTest_ok hg.scr hg.rdi hg.hdr hZ) fun _ ⟨z,m,k⟩ =>
      ⟨⟨mi,⟨hg.scr.congr k.2.2,(k.gpr (by decide)).trans hg.rdi,m ▸ hg.hdr⟩,hZ⟩,z⟩
  refine two_ite (fun L s t hs ht => by simp only [eval,hs.2,ht.2]) ?_ ?_
  · refine two_map id (fun L s ⟨⟨h,z⟩,e⟩ => ⟨h,?_⟩) (alignedChoice_ct ho ha hb ha1 ha2 hb1 hb2 hM hS hR hF hT)
    simp only [eval,z,Option.some.injEq,decide_eq_true_eq] at e
    exact e
  · exact two_map id (fun _ _ h => h.1.1) (montMulAdx_ct ho ha hb ha1 ha2 hb1 hb2 hM hS hR hF)

end VG.Proof.Bignum.X86_64.AdxTiledProduct

end
