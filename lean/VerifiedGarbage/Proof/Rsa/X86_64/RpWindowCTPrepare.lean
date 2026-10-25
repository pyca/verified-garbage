module

import VerifiedGarbage.Proof.Rsa.X86_64.RpWindowCTLoop
import VerifiedGarbage.Proof.Rsa.X86_64.RpCT4
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpWindowCTLoop
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpCT4
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpFrame
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Rsa.X86_64.RpCT5

/-! # Recovery windows: constant-time table preparation -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt)
open Rp (copyA_gct mm_gct)

namespace RecoveryWindow

/-- Copies while preparing powers preserve the live arithmetic bounds. -/
theorem prepare_copy_ct (o a : Nat) (ho : o ∈ [aY, aE, aD]) (ha : a ∈ [aY, aG, aO]) (hne : o ≠ a)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base a .rsi ++ base o .rbx))
      VG.Impl.Rsa.X86_64.copyWords) hint).isSome = true) :
    RelCT isa (Two (Rp.BT true)) (copyA o a) (Two (Rp.BT true)) := by
  refine copyA_gct RpP.B RpP.Z (fun p => wk p.k) (fun _ _ h => h.ws) ht fun p s h => ?_
  obtain ⟨minv, N, r, t, hc, hy, hg, hx⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho ha
  have hz := hc.hZ16
  have hn : 0 < N := by have := hc.n1; omega
  have ho16 : o < 16 := by rcases ho with rfl | rfl | rfl <;> decide
  have ha16 : a < 16 := by rcases ha with rfl | rfl | rfl <;> decide
  have hco : o ∉ cArr := by rcases ho with rfl | rfl | rfl <;> decide
  have hgo : aG ≠ o := by rcases ho with rfl | rfl | rfl <;> decide
  have hxo : aXm ≠ o := by rcases ho with rfl | rfl | rfl <;> decide
  have hbound : wv s.mem p.B (slot (wk p.k) a) (wk p.k) < N := by
    rcases ha with rfl | rfl | rfl
    · exact hy
    · exact hg
    · rw [hc.ho]; exact Nat.mod_lt _ hn
  refine WP.mono (copy_ok hc ho16 ha16 hne hco) fun u ⟨hc', hf, k, hv⟩ => ?_
  refine ⟨minv, N, r, t, hc', ?_, ?_, fun _ => ?_⟩
  · by_cases he : o = aY
    · subst o; rw [hv]; exact hbound
    · rw [hf.rg_wv hz (by simp) (by decide) (by simpa using Ne.symm he) (by omega)]; exact hy
  · rw [hf.rg_wv hz (by simp) (by decide) (by simpa using hgo) (by omega)]; exact hg
  · rw [hf.rg_wv hz (by simp) (by decide) (by simpa using hxo) (by omega)]; exact hx rfl

theorem prepare_mul_ct (M : Mont) (sqr : Bool) : RelCT isa (Two (Rp.BT true))
    (M.mm aY aY (if sqr then aY else aXm)) (Two (Rp.BT true)) := by
  have hb8 : (if sqr then aY else aXm) < 8 := by cases sqr <;> decide
  have hb1 : (if sqr then aY else aXm) ≠ aAcc := by cases sqr <;> decide
  have hb2 : (if sqr then aY else aXm) ≠ aTmp := by cases sqr <;> decide
  refine mm_gct RpP.B RpP.Z (fun p => wk p.k) (fun _ _ h => h.ws) M
    (by cases sqr <;> unfold MmUse <;> decide) fun p s h => ?_
  obtain ⟨minv, N, r, t, hc, hy, hg, hx⟩ := h
  refine WP.mono (mul_ok M hc (a := aY) (b := if sqr then aY else aXm)
    (by decide) hb8 (by decide) (by decide) hb1 hb2 (by cases sqr; exact hx rfl; exact hy))
    fun u ⟨hc', hf, k, hy', _⟩ => ?_
  exact ⟨minv, N, r, t, hc', hy',
    by rw [hf.rg_wv hc.hZ16 (by simp) (by decide) (by decide) (by omega)]; exact hg,
    fun _ => by rw [hf.rg_wv hc.hZ16 (by simp) (by decide) (by decide) (by omega)]; exact hx rfl⟩

theorem prepare_ct (M : Mont) : RelCT isa (Two Rp.EX) (windowPowers M.mm) fun _ _ => True := by
  simp only [windowPowers, seqs]
  refine RelCT.seq (R := Two (Rp.BT true))
    (copyA_gct RpP.B RpP.Z (fun p => wk p.k) (fun _ _ ⟨_, _, _, _, _, hc, _⟩ => hc.ws)
      (by taint_decide) fun p s h => ?_)
    (RelCT.seq (prepare_copy_ct aY aG (by decide) (by decide) (by decide) (by taint_decide))
      (RelCT.seq (prepare_mul_ct M true)
        (RelCT.seq (prepare_copy_ct aE aY (by decide) (by decide) (by decide) (by taint_decide))
          (RelCT.seq (prepare_mul_ct M false)
            (RelCT.seq (prepare_copy_ct aD aY (by decide) (by decide) (by decide) (by taint_decide))
              ((prepare_copy_ct aY aO (by decide) (by decide) (by decide) (by taint_decide)).mono
                (fun _ _ h => h) (fun _ _ _ => trivial)))))))
  obtain ⟨minv, N, r, t, g, hc, hg, _, hy⟩ := h
  have hn : 0 < N := by have := hc.n1; omega
  refine WP.mono (copy_ok hc (o := aXm) (a := aG) (by decide) (by decide) (by decide) (by decide))
    fun u ⟨hc', hf, k, hx⟩ => ?_
  exact ⟨minv, N, r, t, hc',
    by rw [hf.rg_wv hc.hZ16 (by simp) (by decide) (by decide) (by omega), hy]; exact Nat.mod_lt _ hn,
    by rw [hf.rg_wv hc.hZ16 (by simp) (by decide) (by decide) (by omega)]; exact hg,
    fun _ => by rw [hx]; exact hg⟩

/-- Table preparation and every window preserve the original leakage policy. -/
theorem exp_ct (M : Mont) : RelCT isa (Two Rp.EX) (windowExp M.mm) fun _ _ => True := by
  unfold windowExp
  refine RelCT.seq (R := Two EX) (two_post (prepare_ct M) fun p s h => ?_)
    ((expLoop_ct M).mono (fun _ _ h => h) (fun _ _ _ => trivial))
  obtain ⟨minv, N, r, t, g, hc, hg, hgm, _⟩ := h
  exact WP.mono (powers_ok M hc hg hgm) fun u ⟨hc', _, _, hp, hy⟩ =>
    ⟨minv, N, r, t, g, hc', hp, hp.g1lt, hp.g1, hy⟩

end RecoveryWindow
end VG.Proof.Rsa.X86_64
