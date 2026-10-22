module

import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Square
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Counter
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Frame
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Weierstrass.AArch64.Pow
public import VerifiedGarbage.Impl.EcKey.Compressed.AArch64.Decompress
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Fixed

/-! # The tested power in one P-224 descent round -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps)

theorem descentPower_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State} {j : Nat}
    (hs : Scr s base size) (hM : ModOkA c.MP' size c.C.p s.mem base)
    (hlt : sv c base s T0 < c.C.p) (hj : 1 ≤ j) (hj' : j < 2 ^ 31)
    (hword : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (Impl.EcKey.Compressed.AArch64.descentPower c) s fun s' =>
      KeepRegs (powClob c.n) s s' ∧ Unch base (slW c [T3, TMP]) s.mem s'.mem ∧
      sv c base s' T3 < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' T3) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s T0) ^ (2 ^ (j - 1)) := by
  have h7 := hc.n10
  have h0 := hc.n0
  have hn := hs.nowrap
  have h3 := sl_le c h7 (i := T3) (by decide)
  have h2 := sl_le c h7 (i := T2) (by decide)
  change WP isa (.seq (.block (copy c.n (c.sl T3) (c.sl T0) ++
    [decCounter]))
    (Impl.EcKey.Compressed.AArch64.squarePower c)) s _
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok c.n hs h3 (sl_le c h7 (by decide)) (sl_mod8 c T3) (sl_mod8 c T0)
    (by have := sl_apart c (i := T3) (j := T0) (by decide); omega)) fun s₁ ⟨v₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have U₁ : Unch base (slW c [T3, TMP]) s.mem s₁.mem := slot_frame (by simp) (Nat.le_refl _) O₁
  have w₁ : s₁.gpr .x19 = BitVec.ofNat 64 j := (k₁.gpr _ (by decide)).trans hword
  refine WP.mono (decCounter_ok s₁ hj (by omega) w₁) fun s₃ ⟨hb₃, k₃⟩ => ?_
  have hs₃ := hs₁.of_keeps k₃ (by decide)
  have m₃ : s₃.mem = s₁.mem := k₃.mem
  have M₃ : ModOkA c.MP' size c.C.p s₃.mem base := modP_of hc (by
    rw [m₃, O₁.wordsVal (sl_apart c (i := MP) (j := T3) (by decide)) (by
      have := sl_le c h7 (i := MP) (by decide); omega)]
    exact hM.val)
  refine WP.mono (squarePower_ok hc hs₃ M₃
    (by change wordsVal _ _ _ _ < _; rw [m₃, v₁]; exact hlt) hb₃ (by omega))
    fun t ⟨kt, Ut, lt, vt⟩ => ?_
  refine ⟨?_, ?_, lt, ?_⟩
  · have K₁ : KeepRegs (powClob c.n) s s₁ := k₁.mono (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      simp [powClob, clob])
    exact (K₁.trans ((Keeps.regs k₃).mono (by simp [powClob]))).trans kt
  · rw [m₃] at Ut
    exact unch_same U₁ Ut
  · change toM c.C.p (2 ^ (64 * c.n)) (sv c base t T3) =
      toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl T0) c.n) ^ (2 ^ (j - 1))
    simpa only [sv, m₃, v₁] using vt

end VG.Proof.EcKey.Compressed.AArch64
