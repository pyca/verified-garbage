import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledChoiceCT

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
    WP isa (AdxTiledProduct.dispatch o a b) s fun t =>
      wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w b) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  unfold AdxTiledProduct.dispatch
  by_cases hab : a=b
  · rw [ite_eq_left hab]
    exact squareDispatch_ok hs hdi hH hZ hw hw' ho ha hb ho1 ho2 ha1 ha2 hb1 hb2 hinv hB
  · rw [ite_eq_right hab]
    exact AdxTiledProduct.choice_ok hs hdi hH hZ hw hw' ho ha hb ho1 ho2 ha1 ha2 hb1 hb2 hinv hB

theorem tiledDispatch_ct {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    {hc₀ hc₁ hc₂ hc₃ hc₄ hc₅ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hM : (taint.check (Taint.ofRegs [.rdi]) (.block (bases o a b aN aAcc aTmp)) hc₀).isSome = true)
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (setup b)) hc₁).isSome = true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (rowBase a)) hc₂).isSome = true)
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (finishBases o)) hc₃).isSome = true)
    (hA : (taint.check (Taint.ofRegs [.rdi]) (.block (setup a)) hc₄).isSome = true)
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup a b)) hc₅).isSome = true) :
    RelCT isa (Two GoodW) (AdxTiledProduct.dispatch o a b) (fun _ _ => True) := by
  unfold AdxTiledProduct.dispatch
  by_cases hab : a=b
  · rw [ite_eq_left hab]
    exact squareDispatch_ct ho ha hb ha1 ha2 hb1 hb2 hM hS hR hF hA
  · rw [ite_eq_right hab]
    exact AdxTiledProduct.choice_ct ho ha hb ha1 ha2 hb1 hb2 hM hS hR hF hT

/-- Montgomery multiplication with a specialized ADX square. -/
def Mont.adxSquare : Mont where
  mm := AdxTiledProduct.dispatch
  ok hg hZ hw hw' _ _ _ ho ha hb d1 d2 d3 d4 d5 d6 hinv hB :=
    WP.mono (tiledDispatch_ok hg.scr hg.rdi hg.hdr hZ hw hw' ho ha hb d1 d2 d3 d4 d5 d6 hinv hB)
      fun t' ⟨h1, h2, h3, k⟩ => ⟨⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi, h3.hdr hg.hdr⟩,
        h1, h2, h3, k⟩
  ct := by
    intro o a b h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    exact tiledDispatch_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)

end VG.Proof.Bignum.X86_64
