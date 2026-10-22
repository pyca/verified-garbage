module

public import VerifiedGarbage.Impl.EcKey.Compressed.Arm.Decompress
import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Frame
import VerifiedGarbage.Proof.Ecdsa.Arm.SlotOps
import VerifiedGarbage.Proof.Ecdsa.Arm.Middle
import VerifiedGarbage.Proof.Weierstrass.Arm.Copy
public import VerifiedGarbage.Proof.Ecdsa.Arm.Main
import VerifiedGarbage.Proof.Ecdh.Arm.Peer
import VerifiedGarbage.Proof.Weierstrass.Arm.Fprog
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Ecdsa.Arm.Fixed

/-! # Select the correction factor of the P-224 descent -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Impl.Ecdh.Arm (W0)
open VG.Proof.Ecdsa.Arm VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm VG.Proof.Ecdh.Arm
open VG.Proof.X25519.Arm (Rest wp_mov wp_dp op2_reg op2_imm dpVal)

theorem zero_ok {c : Cfg} {s : State} {base : Addr} {a : Nat} (hs : Scr s base size) (h0 : 0 < c.n)
    (ha : a + 8 * c.n ≤ size) :
    WP isa (.block (Impl.EcKey.Compressed.Arm.zeroMask c a)) s fun t =>
      t.gpr .r5 = mask32 (wordsVal s.mem base a c.n = 0) ∧
      Rest [.r4, .r5] s t ∧ t.mem = s.mem := by
  unfold Impl.EcKey.Compressed.Arm.zeroMask
  refine VG.Proof.X25519.Arm.WP.append (nonzero_ok c hs h0 ha) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => ?_
  refine wp_dp (op2_reg _ _) fun s₃ u₃ => ?_
  refine wp_dp (op2_imm (by decide)) fun t u₄ => WP.block_nil ?_
  refine ⟨?_, k₁.trans ((u₂.rest (by simp)).trans ((u₃.rest (by simp)).trans (u₄.rest (by simp)))), ?_⟩
  · rw [u₄.gpr, u₃.gpr, u₂.gpr, u₂.other _ (by decide), e₁]
    simp only [dpVal]
    rw [mask_not]
    simp only [ne_eq, Decidable.not_not]
  · rw [u₄.mem, u₃.mem, u₂.mem, m₁]

theorem descentChoose_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hf : Far s base 8192) (_hM : ModOkW c.MP' size c.C.p s.mem base)
    (ht : sv c base s T3 < c.C.p) (hcval : sv c base s T1 < c.C.p)
    (hOne : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p) :
    WP isa (Impl.EcKey.Compressed.Arm.descentChoose c) s fun t =>
      Rest Mont.callClob s t ∧ Unch base (slWk c [W0, T4, TMP]) s.mem t.mem ∧
      sv c base t T4 < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t T4) =
        if toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) = 1 then 1
        else toM c.C.p (2 ^ (64 * c.n)) (sv c base s T1) := by
  have h7 := hc.n10
  have h0 := hc.n0
  have hn := hs.nowrap
  have hp := hc.p_ge
  have hW := sl_le c h7 (i := W0) (by decide)
  have hT := sl_le c h7 (i := T3) (by decide)
  have hC := sl_le c h7 (i := T1) (by decide)
  have hB := sl_le c h7 (i := T4) (by decide)
  have hO := sl_le c h7 (i := ONEP) (by decide)
  have hOlt : sv c base s ONEP < c.C.p := by rw [hOne]; exact Nat.mod_lt _ (by omega)
  rw [Impl.EcKey.Compressed.Arm.descentChoose]
  refine WP.seq (WP.mono (slSub_ok hc.fp (MP'_n c) h7 hs hf (o := W0) (a := T3) (b := ONEP)
    (by decide) (by decide) (by decide) ht hOlt) fun s₁ ⟨k₁, e₁⟩ => ?_)
  change sv c base s₁ W0 = (sv c base s T3 + c.C.p - sv c base s ONEP) % c.C.p at e₁
  have hs₁ := k₁.scr hs
  have lt₁ : sv c base s₁ W0 < c.C.p := by
    rw [e₁]; exact Nat.mod_lt _ (by omega)
  have v₁ : toM c.C.p (2 ^ (64 * c.n)) (sv c base s₁ W0) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) - 1 := by
    rw [e₁, toM_sub (by omega), hOne, toM_one (unitMod_pow_two hc.p_odd (64 * c.n))]
  have z₁ : sv c base s₁ W0 = 0 ↔ toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) = 1 := by
    rw [← toM_eq_zero_iff (unitMod_pow_two hc.p_odd (64 * c.n)) lt₁, v₁]
    constructor <;> intro h <;> grind
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (zero_ok hs₁ h0 hW) fun s₂ ⟨mask₂, k₂, m₂⟩ => ?_
  simp only [mask32, show wordsVal s₁.mem base (c.sl W0) c.n = sv c base s₁ W0 from rfl, z₁] at mask₂
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => ?_
  have hs₃ := (hs₁.of_rest k₂ (by decide)).of_rest (u₃.rest (ws := [.r10]) (by simp)) (by decide)
  refine WP.mono (sel_ok (decide (toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) = 1)) (2 * c.n) hs₃
    (by rw [u₃.gpr, mask₂]; simp only [decide_eq_true_eq]) (by omega) (by omega) (by omega)
    (by have := sl_apart c (i := T4) (j := T1) (by decide); omega)
    (by have := sl_apart c (i := T4) (j := ONEP) (by decide); omega))
    fun t ⟨v₄, k₄, O₄⟩ => ?_
  have mem₃ : s₃.mem = s₁.mem := u₃.mem.trans m₂
  have C₃ : sv c base s₃ T1 = sv c base s T1 := by
    rw [sv, mem₃]; exact sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)
  have O₃ : sv c base s₃ ONEP = sv c base s ONEP := by
    rw [sv, mem₃]; exact sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)
  rw [show 4 * (2 * c.n) = 8 * c.n by omega] at O₄
  simp only [← wordsVal_eq_val32] at v₄
  change sv c base t T4 = _ at v₄
  simp only [decide_eq_true_eq] at v₄
  change sv c base t T4 = if _ then sv c base s₃ ONEP else sv c base s₃ T1 at v₄
  rw [C₃, O₃] at v₄
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ((k₁.rest.trans (k₂.mono (by decide))).trans
      (u₃.rest (by simp [Mont.callClob, clob]))).trans (k₄.mono (by decide))
  · have U₁ : Unch base (slWk c [W0, T4, TMP]) s.mem s₁.mem :=
      unch_slots (MP'_n c) rfl k₁.unch (by simp) (by simp)
    apply unch_same U₁
    rw [← mem₃]
    exact (slot_frame (slots := [W0, T4, TMP]) (by simp) (Nat.le_refl _) O₄).mono
      (fun w hw => List.mem_append_left _ hw)
  · rw [v₄]; split
    · exact hOlt
    · exact hcval
  · rw [v₄]; split
    · rw [hOne, toM_one (unitMod_pow_two hc.p_odd (64 * c.n))]
    · rfl

end VG.Proof.EcKey.Compressed.Arm
