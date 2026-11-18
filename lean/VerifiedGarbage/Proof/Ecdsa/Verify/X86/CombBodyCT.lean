module
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombCT
public import VerifiedGarbage.Proof.Ecdsa.X86.CombCode
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombFrontCT
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombTailCT
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombPointTail
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafCallerKeep

import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafCallerCT
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombFinalCT
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombMidCT
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombMain
import VerifiedGarbage.Proof.Ecdsa.X86.CombCT
import VerifiedGarbage.Proof.Ecdsa.X86.CombMain

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86

theorem vPoints_rel (hc : CfgOk p256Comb) (hC : Law p256Comb.C)
    (hT : CombTbls p256Comb) (hd : CombOk p256Comb p256d) (ham3 : AM3 p256Comb.C)
    {s₀ t₀ : State} {extra₁ extra₂ : List Region}
    (hp : VPre p256Comb s₀ extra₁) (hq : VPre p256Comb t₀ extra₂)
    (ht₁ : VCombTables p256Comb p256d s₀) (ht₂ : VCombTables p256Comb p256d t₀)
    (he : s₀.gpr .esp = t₀.gpr .esp) (ha : ∀ j < 4, arg s₀ j = arg t₀ j)
    (hv : VInputEq p256Comb s₀ t₀)
    (hg : s₀.gpr .eax = t₀.gpr .eax) (hspG : SpOk p256Comb.gMul 20) :
    RelCT isa (fun s t => Mid p256Comb s₀ (ptr s₀ 3) s ∧ Mid p256Comb t₀ (ptr t₀ 3) t)
      (Impl.Ecdsa.Verify.X86.Cfg.pointsComb p256Comb) (fun _ _ => True) := by
  have hspG' : SpOk p256Comb.gMul p256Comb.stk := ⟨hspG.1, Nat.le_trans hspG.2 (Cfg.stk_ge _)⟩
  have hsp20 : ∀ {u₀ u : State} {extra : List Region}, VPre p256Comb u₀ extra →
      Keep p256Comb u₀ (ptr u₀ 3) u → 20 ≤ (u.gpr .esp).toNat := fun hp k => by
    rw [k.esp]; exact Nat.le_trans (Cfg.stk_ge _) hp.sp_lo
  have bits := vBits_rel.mono
    (P' := fun s t => Mid p256Comb s₀ (ptr s₀ 3) s ∧ Mid p256Comb t₀ (ptr t₀ 3) t)
    (fun _ _ h => vKeepArgAgree hp hq h.1.keep h.2.keep he ha) (fun _ _ _ => trivial)
  have bits' := bits.wp (F₁ := VCombInput p256Comb s₀ (ptr s₀ 3))
    (F₂ := VCombInput p256Comb t₀ (ptr t₀ 3)) (by
      intro s t h
      change WP isa vBitsCode s (VCombInput p256Comb s₀ (ptr s₀ 3)) ∧
        WP isa vBitsCode t (VCombInput p256Comb t₀ (ptr t₀ 3))
      exact ⟨vBits_ok hc h.1, vBits_ok hc h.2⟩)
  have hCo : ∀ d, p256Comb.comb = some d → CombOk p256Comb d := by
    intro d h; have e : p256d = d := Option.some.inj h; rw [← e]; exact hd
  have multCT : RelCT isa (fun s t => True ∧
      VCombInput p256Comb s₀ (ptr s₀ 3) s ∧ VCombInput p256Comb t₀ (ptr t₀ 3) t)
      p256Comb.gMul (fun _ _ => True) := by
    intro s t tr₁ tr₂ s' t' h e₁ e₂
    obtain ⟨_, S, T⟩ := h
    obtain ⟨tb₁, ap₁⟩ := vTables_keep ht₁ S.toKeep
    obtain ⟨tb₂, ap₂⟩ := vTables_keep ht₂ T.toKeep
    have hb : ptr s₀ 3 = ptr t₀ 3 := congrArg (BitVec.setWidth 64) (ha 3 (by decide))
    have T' := T
    rw [← hb] at T'
    obtain ⟨k₁, hk₁, b₁⟩ := S.scalar
    obtain ⟨k₂, hk₂, b₂⟩ := T'.scalar
    exact gMul_rel hc hC hT hd S.scr T'.scr S.fixed T'.fixed
      hk₁ hk₂ b₁ b₂ tb₁ tb₂ ht₁.2.1 ap₁ ap₂ (hsp20 hp S.toKeep) (hsp20 hq T.toKeep) hg
      (vKeepCombWf hp S.toKeep) (vKeepCombWf hq T.toKeep)
      (by rw [S.wr, T.wr, hp.wr, hq.wr]; simp only [ptr, ha 3 (by decide)])
      (by rw [S.esp, T.esp, he])
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  have functional : ∀ {u₀ u : State} {extra : List Region}, VPre p256Comb u₀ extra → VCombTables p256Comb p256d u₀ →
      VCombInput p256Comb u₀ (ptr u₀ 3) u →
      WP isa p256Comb.gMul u (VPointInput u₀ (ptr u₀ 3)) := by
    intro u₀ u extra hp ht S
    obtain ⟨k, hk, b⟩ := S.scalar
    refine S.toKeep.withSp hspG' (WP.mono (gMul_ok' hc hC hT hCo S.scr S.fixed
      hk S.rx S.ry S.rz b ?_ (hsp20 hp S.toKeep) hspG) fun t h f => ⟨S.toKeep.gMul hc h.1 h.2.1 f,S.values.transfer (by
        intro i hi
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl|rfl|rfl <;>
          exact sv_unch h.2.1 hc.n10 S.scr.nowrap (by decide) (apart_gW (by decide) (by decide)))⟩)
    intro d h
    have e : p256d = d := Option.some.inj h
    subst d
    obtain ⟨tb, ap⟩ := vTables_keep ht S.toKeep
    exact ⟨tb, ht.2.1, ap⟩
  have mult := multCT.wp (F₁ := VPointInput s₀ (ptr s₀ 3))
    (F₂ := VPointInput t₀ (ptr t₀ 3))
    (fun _ _ h => ⟨functional hp ht₁ h.2.1, functional hq ht₂ h.2.2⟩)
  exact bits'.seq (mult.seq ((vPointTail_rel hc hC ham3 hp hq he ha hv).mono
    (fun _ _ h => h.2) (fun _ _ _ => trivial)))

/-- The taint checks of the stages of P-256's verification. -/
theorem p256VerifyCT : VerifyStagesCT p256Comb := ⟨vFront_rel, vMid_rel, vFinal_rel⟩

end VG.Proof.Ecdsa.Verify.X86
