module

import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Frame
public import VerifiedGarbage.Impl.EcKey.Compressed.AArch64.Decompress
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Parity
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
import VerifiedGarbage.Proof.Ecdsa.AArch64.Middle
import VerifiedGarbage.Proof.Mont.AArch64.Ops
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Proof.Weierstrass.AArch64.Unch
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Fixed

/-! # Leave Montgomery form and choose between the two canonical roots -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdh.AArch64 (QY W0)
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

structure SelectPost (c : Cfg) (base : Addr) (s s' : State) : Prop where
  scr : Scr s' base size
  mod : ModOkA c.MP' size c.C.p s'.mem base
  keep : KeepRegs (clob c.n) s s'
  unch : Unch base (slW c [QY, W0, TMP]) s.mem s'.mem
  lt : sv c base s' QY < c.C.p
  val : Fin.ofNat c.C.p (sv c base s' QY) =
    let y := toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)
    if y.val % 2 = (word s.mem base (c.sl D)).toNat % 2 then y else -y

theorem selectRoot_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkA c.MP' size c.C.p s.mem base)
    (hOne : sv c base s ONE = 1) (hZero : sv c base s ZERO = 0) :
    WP isa (Impl.EcKey.Compressed.AArch64.selectRoot c) s (SelectPost c base s) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hp3 := hc.p_ge
  have hY := sl_le c h7 (i := QY) (by decide)
  have hZ := sl_le c h7 (i := ZERO) (by decide)
  have hW := sl_le c h7 (i := W0) (by decide)
  have hD := sl_le c h7 (i := D) (by decide)
  have hMP := sl_le c h7 (i := MP) (by decide)
  change WP isa (.seq (opProg c.MP' (.mul (c.sl QY) (c.sl ACC) (c.sl ONE)))
    (.block (opCode c.MP' (.sub (c.sl W0) (c.sl ZERO) (c.sl QY)) ++
      Impl.EcKey.Compressed.AArch64.parityMask c ++ sel c.n (c.sl QY) (c.sl QY) (c.sl W0)))) s _
  rw [mulPP_eq_op _ _ _ (by
    intro h
    have := sl_inj c hc.n0 h
    contradiction)]
  refine WP.seq (WP.mono (slMulP_ok hc hs hM (o := QY) (a := ACC) (b := ONE)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [hOne]; omega))
    fun s₁ ⟨k₁, lt₁, e₁⟩ => ?_)
  have hs₁ := k₁.scr hs
  have hM₁ := hM.keepA64 (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  have normal : Fin.ofNat c.C.p (sv c base s₁ QY) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) :=
    toM_one_mul (unitMod_pow_two hc.p_odd (64 * c.n)) (by simpa only [hOne] using e₁)
  have normalVal : sv c base s₁ QY =
      (toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)).val := by
    simpa only [Fin.val_ofNat, Nat.mod_eq_of_lt lt₁] using congrArg Fin.val normal
  have zero₁ : sv c base s₁ ZERO = 0 :=
    (sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)).trans hZero
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (sub_ok hs₁ hM₁ (MP'_A c) hW hZ hY (sl_mod8 c W0) (sl_mod8 c ZERO) (sl_mod8 c QY)
    (by change sv c base s₁ ZERO < c.C.p; rw [zero₁]; omega)
    lt₁) fun s₂ ⟨k₂, e₂⟩ => ?_
  change sv c base s₂ W0 = (sv c base s₁ ZERO + c.C.p - sv c base s₁ QY) % c.C.p at e₂
  have hs₂ := k₂.scr hs₁
  have hM₂ := hM₁.keepA64 (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₂ (by decide) (by decide)
  have y₂ : sv c base s₂ QY = sv c base s₁ QY :=
    sv_keep (MP'_n c) rfl h7 hn k₂ (by decide) (by decide) (by decide)
  have negLt : sv c base s₂ W0 < c.C.p := by
    rw [e₂]
    exact Nat.mod_lt _ (by omega)
  have negVal : Fin.ofNat c.C.p (sv c base s₂ W0) = -(Fin.ofNat c.C.p (sv c base s₁ QY)) := by
    apply Fin.ext
    simp only [Fin.val_ofNat, Fin.neg_def]
    rw [show sv c base s₂ W0 = (sv c base s₁ ZERO + c.C.p - sv c base s₁ QY) % c.C.p from e₂,
      zero₁, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt lt₁]
  have U₁₂ : Unch base (slW c [QY, W0, TMP]) s.mem s₂.mem :=
    unch_same (unch_slots (MP'_n c) rfl k₁.unch (by simp) (by simp))
      (unch_slots (MP'_n c) rfl k₂.unch (by simp) (by simp))
  have tag₂ : word s₂.mem base (c.sl D) = word s.mem base (c.sl D) :=
    U₁₂.word (fun w hw => by
      have := (apart_slW (c := c) (by decide : D ∉ [QY, W0, TMP])) w hw
      omega) (by have := hs.nowrap; omega)
  rw [WP.block_append_iff]
  refine WP.mono (parityMask_ok hs₂ h0 (by omega) (by omega)) fun s₃ ⟨mask₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  refine WP.mono (sel_ok (decide (sv c base s₂ QY % 2 ≠ (word s₂.mem base (c.sl D)).toNat % 2)) c.n hs₃
    (by simpa only [mask, decide_eq_true_eq] using mask₃)
    hY hY hW (sl_mod8 c QY) (sl_mod8 c QY) (sl_mod8 c W0) (Or.inl (Nat.le_refl _))
    (by have := sl_apart c (i := QY) (j := W0) (by decide); omega)) fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  have hM₄ : ModOkA c.MP' size c.C.p s₄.mem base := modP_of hc (by
    rw [O₄.wordsVal (d := c.sl MP) (k := c.n)
      (sl_apart c (i := MP) (j := QY) (by decide)) (by omega), k₃.mem]
    exact hM₂.val)
  have e₄' : sv c base s₄ QY =
      if sv c base s₂ QY % 2 ≠ (word s₂.mem base (c.sl D)).toNat % 2 then
        sv c base s₂ W0 else sv c base s₂ QY := by
    simpa only [sv, k₃.mem, decide_eq_true_eq] using e₄
  refine ⟨hs₄, hM₄, ?_, ?_, ?_, ?_⟩
  · have k₁' : KeepRegs (clob c.n) s s₁ := ⟨k₁.gpr, k₁.rd, k₁.wr, k₁.sp⟩
    have k₂' : KeepRegs (clob c.n) s₁ s₂ := ⟨k₂.gpr, k₂.rd, k₂.wr, k₂.sp⟩
    exact ((k₁'.trans k₂').trans ((Keeps.regs k₃).mono (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [clob]))).trans
        (k₄.mono (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
                     rcases hr with rfl | rfl <;> simp [clob]))
  · apply unch_same U₁₂
    rw [← k₃.mem]
    exact slot_frame (by simp) (Nat.le_refl _) O₄
  · rw [e₄']
    split
    · exact negLt
    · rw [y₂]
      exact lt₁
  · change Fin.ofNat c.C.p (sv c base s₄ QY) =
      if (toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)).val % 2 =
        (word s.mem base (c.sl D)).toNat % 2 then _ else _
    rw [y₂, tag₂, normalVal] at e₄'
    by_cases hm : (toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)).val % 2 =
        (word s.mem base (c.sl D)).toNat % 2
    · rw [ite_eq_left hm]
      rw [ite_eq_right (not_not_intro hm)] at e₄'
      rw [e₄']
      exact Fin.ext (Nat.mod_eq_of_lt (toM _ _ _).isLt)
    · rw [ite_eq_right hm]
      rw [ite_eq_left hm] at e₄'
      rw [e₄', negVal, normal]

end VG.Proof.EcKey.Compressed.AArch64
