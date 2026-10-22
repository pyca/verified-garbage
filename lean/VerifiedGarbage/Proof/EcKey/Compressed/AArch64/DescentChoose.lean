module

public import VerifiedGarbage.Impl.EcKey.Compressed.AArch64.Decompress
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Frame
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
import VerifiedGarbage.Proof.Ecdsa.AArch64.Middle
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Proof.Weierstrass.AArch64.Unch
import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
import VerifiedGarbage.Proof.Mont.AArch64.Ops
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Fixed

/-! # Select the correction factor of the P-224 descent -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdh.AArch64 (W0)
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Ecdh.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

theorem descentChoose_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkA c.MP' size c.C.p s.mem base)
    (ht : sv c base s T3 < c.C.p) (hcval : sv c base s T1 < c.C.p)
    (hOne : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p) :
    WP isa (.block (Impl.EcKey.Compressed.AArch64.descentChoose c)) s fun t =>
      KeepRegs (clob c.n) s t ∧ Unch base (slW c [W0, T4, TMP]) s.mem t.mem ∧
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
  rw [Impl.EcKey.Compressed.AArch64.descentChoose, List.append_assoc, List.append_assoc,
    WP.block_append_iff]
  refine WP.mono (sub_ok hs hM (MP'_A c) hW hT hO (sl_mod8 c W0) (sl_mod8 c T3) (sl_mod8 c ONEP) ht hOlt)
    fun s₁ ⟨k₁, e₁⟩ => ?_
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
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok c hs₁ h0 hW (sl_mod8 c W0)) fun s₂ ⟨mask₂, k₂⟩ => ?_
  simp only [mask, show wordsVal s₁.mem base (c.sl W0) c.n = sv c base s₁ W0 from rfl, z₁] at mask₂
  rw [WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.addImm .x .x3 .x2 0]) s₂ (fun s₃ =>
      s₃.gpr .x3 = s₂.gpr .x2 ∧ Keeps [.x3] s₂ s₃) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
      show (0 : Nat) < 4096 by decide, ite_true, RegUpd.gpr_write_self,
      BitVec.setWidth_eq, BitVec.add_zero, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_singleton] at hr
    exact RegUpd.gpr_write_of_ne _ _ _ hr) fun s₃ ⟨m₃, k₃⟩ => ?_
  have hs₃ := (hs₁.of_keeps k₂ (by decide)).of_keeps k₃ (by decide)
  refine WP.mono (sel_ok (decide (toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) = 1)) c.n hs₃
    (by rw [m₃, mask₂]; simp only [decide_eq_true_eq]) hB hC hO (sl_mod8 c T4) (sl_mod8 c T1) (sl_mod8 c ONEP)
    (by have := sl_apart c (i := T4) (j := T1) (by decide); omega)
    (by have := sl_apart c (i := T4) (j := ONEP) (by decide); omega))
    fun t ⟨v₄, k₄, O₄⟩ => ?_
  have mem₃ : s₃.mem = s₁.mem := k₃.mem.trans k₂.mem
  have C₃ : sv c base s₃ T1 = sv c base s T1 := by
    rw [sv, mem₃]; exact sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)
  have O₃ : sv c base s₃ ONEP = sv c base s ONEP := by
    rw [sv, mem₃]; exact sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)
  change sv c base t T4 = _ at v₄
  simp only [decide_eq_true_eq] at v₄
  change sv c base t T4 = if _ then sv c base s₃ ONEP else sv c base s₃ T1 at v₄
  rw [C₃, O₃] at v₄
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (((⟨k₁.gpr, k₁.rd, k₁.wr, k₁.sp⟩ : KeepRegs (clob c.n) s s₁).trans
      ((Keeps.regs k₂).mono (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [clob]))).trans
      ((Keeps.regs k₃).mono (by intro r hr; obtain rfl := List.mem_singleton.mp hr; simp [clob]))).trans (k₄.mono (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp [clob]))
  · have U₁ : Unch base (slW c [W0, T4, TMP]) s.mem s₁.mem :=
      unch_slots (MP'_n c) rfl k₁.unch (by simp) (by simp)
    apply unch_same U₁
    rw [← mem₃]
    exact slot_frame (by simp) (Nat.le_refl _) O₄
  · rw [v₄]; split
    · exact hOlt
    · exact hcval
  · rw [v₄]; split
    · rw [hOne, toM_one (unitMod_pow_two hc.p_odd (64 * c.n))]
    · rfl

end VG.Proof.EcKey.Compressed.AArch64
