module

public import VerifiedGarbage.Proof.Ecdh.AArch64.MulJ4
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy

/-! # The existing inversion with a separately located scalar bit table -/

@[expose] public section

namespace VG.Proof.Ecdh.AArch64.P521.Window

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont
open VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Ecdsa.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Spec.Weierstrass

def windowCfg (c : Cfg) (bits windows : Nat) : WinCfg :=
  { c.winCfg Impl.Ecdh.AArch64.PX Impl.Ecdh.AArch64.PY with bits := bits, J := windows }

theorem inverse_for (c : Cfg) (hc : CfgOk c) (bits windows : Nat) {base : Addr}
    (hw : ∀ w ∈ chainWc c, w = ((windowCfg c bits windows).M.tmp, 8 * c.n) ∨
      ((windowCfg c bits windows).M.mo + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ (windowCfg c bits windows).M.mo) ∧
      ∀ x ∈ winSlots (windowCfg c bits windows), x + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ x)
    (hb : ∀ w ∈ invJW c, bits + 4 * windows ≤ w.1 ∨ w.1 + w.2 ≤ bits) :
    InvSpecW (windowCfg c bits windows) c.C base size (Impl.Ecdh.AArch64.Cfg.invJ c) (invJClob c.n) (invJW c) := by
  have h7 := hc.n10
  refine ⟨fun t ht hM hz => ?_, fun w hw' => ?_, hb⟩
  · rw [Impl.Ecdh.AArch64.Cfg.invJ]
    refine WP.seq (WP.mono (pPow_ok hc.toBaseCfgOk ht hM hz) fun t₁ ⟨K₁, U₁, lt₁, v₁⟩ => ?_)
    have ht₁ := ht.of_keepRegs K₁ (x0_not_powClob h7)
    refine WP.mono (copy_ok (size := size) c.n ht₁ (o := c.sl TX) (a := c.sl ACC)
      (sl_le c h7 (by decide)) (sl_le c h7 (by decide)) (sl_mod8 c _) (sl_mod8 c _)
      ((sl_apart c (i := TX) (j := ACC) (by decide)).elim
        (fun h => Or.inl (Nat.le_trans (Nat.le_add_right _ _) h)) Or.inr))
      fun t₂ ⟨v₂, K₂, O₂⟩ => ?_
    refine ⟨(K₁.mono fun r hr => List.mem_append_right _ hr).trans
        (K₂.mono fun r hr => by
          rw [List.mem_singleton.mp hr]; exact List.mem_append_left _ (combClob_mem (by simp))),
      (U₁.trans O₂.unch).mono fun w hw => by simpa [invJW] using hw, ?_, ?_⟩
    · show wordsVal t₂.mem base (c.sl TX) c.n < c.C.p
      rw [v₂]; exact lt₁
    · show toM _ _ (wordsVal t₂.mem base (c.sl TX) c.n) = toM _ _ (wordsVal t.mem base (c.sl RZ) c.n) ^ _
      rw [v₂]; exact v₁
  · simp only [invJW, List.mem_append, List.mem_singleton] at hw'
    rcases hw' with hw' | rfl
    · rcases hw w hw' with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inl rfl

end VG.Proof.Ecdh.AArch64.P521.Window
