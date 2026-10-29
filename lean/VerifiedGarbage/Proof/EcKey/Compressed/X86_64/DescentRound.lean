module

public import VerifiedGarbage.Impl.EcKey.Compressed.Root
public import VerifiedGarbage.Impl.EcKey.Compressed.X86_64.Decompress
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Fixed

import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.Counter
import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.Frame
import VerifiedGarbage.Proof.Weierstrass.X86_64.Pow
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Ecdsa.X86_64.Stages
import VerifiedGarbage.Proof.Ecdsa.X86_64.Layout
import VerifiedGarbage.Proof.Weierstrass.X86_64.Unch
import VerifiedGarbage.Proof.Ecdsa.X86_64.SlotOps
import VerifiedGarbage.Proof.Ecdsa.X86_64.Middle
import VerifiedGarbage.Proof.Weierstrass.RootPowers
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Ecdh.X86_64.Peer
import VerifiedGarbage.Proof.Mont.X86_64.Ops
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Ecdsa.X86_64.Lays
import VerifiedGarbage.Proof.Weierstrass.X86_64.Fprog
/-! # One machine round refines the functional P-224 root descent -/

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/X86_64/Square.lean`, which only this module imported.
section

/-! # Repeated squaring for the P-224 root descent

The backwards invariant `current^(2^remaining) = original^(2^count)`
avoids any assumption about the input being a square or nonzero.
-/

section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont.X86_64 VG.Proof.Mont
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.X25519.X86_64 (Keeps)

structure SquareInv (c : Cfg) (base : Addr) (count : Nat) (s₀ s : State) (j : Nat) : Prop where
  scr : Scr s base size
  mod : ModOkW c.MP' size c.C.p s.mem base
  rbx : s.gpr .rbx = BitVec.ofNat 64 j
  keep : KeepRegs (powClob c.n) s₀ s
  unch : Unch base (slW c [T3, TMP]) s₀.mem s.mem
  lt : sv c base s T3 < c.C.p
  val : toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) ^ (2 ^ j) =
    toM c.C.p (2 ^ (64 * c.n)) (sv c base s₀ T3) ^ (2 ^ count)

theorem squareStep_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {count j : Nat}
    (hj : 1 ≤ j) (hcount : count < 2 ^ 31) (hjc : j ≤ count) {s₀ s : State}
    (I : SquareInv c base count s₀ s j) :
    WP isa (Impl.EcKey.Compressed.X86_64.squareStep c T3) s fun s' =>
      SquareInv c base count s₀ s' (j - 1) ∧ s'.zf = some (decide (j - 1 = 0)) := by
  have h7 := hc.n10
  have hn := I.scr.nowrap
  rw [Impl.EcKey.Compressed.X86_64.squareStep, WP.block_append_iff]
  refine WP.mono (slMul_ok (MP'_n c) (MP'_tmp c) (MP'_mo c) h7 I.scr I.mod
    (o := T3) (a := T3) (b := T3) (by decide) (by decide) (by decide) (by decide) I.lt)
    fun s₁ ⟨k₁, lt₁, e₁⟩ => ?_
  have hs₁ := k₁.scr I.scr
  have hm₁ := I.mod.keep (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  have hb₁ : s₁.gpr .rbx = BitVec.ofNat 64 j :=
    (k₁.gpr _ (rbx_not_clob c.n)).trans I.rbx
  have U₁ : Unch base (slW c [T3, TMP]) s.mem s₁.mem :=
    unch_slots (MP'_n c) rfl k₁.unch (by simp) (by simp)
  have v₁ : toM c.C.p (2 ^ (64 * c.n)) (sv c base s₁ T3) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) ^ 2 := by
    rw [toM_mul (unitMod_pow_two hc.p_odd (64 * c.n)) e₁, Lean.Grind.Semiring.pow_two]
  rw [show ([.alu .sub .rbx (.imm 1), .alu .test .rbx (.reg .rbx)] : List Instr) =
      [.alu .sub .rbx (.imm 1)] ++ [.alu .test .rbx (.reg .rbx)] from rfl,
    WP.block_append_iff]
  refine WP.mono (decRbx_ok s₁ hj (by omega) hb₁) fun s₂ ⟨hb₂, k₂⟩ => ?_
  refine WP.mono (testRbx_ok s₂ (by omega) hb₂) fun s₃ ⟨hz₃, k₃⟩ => ?_
  have m₃ : s₃.mem = s₁.mem := k₃.2.1.trans k₂.2.1
  refine ⟨⟨(hs₁.of_keeps k₂ (by decide)).of_keeps k₃ (by decide), by rw [m₃]; exact hm₁,
    by rw [k₃.1 _ (by decide), hb₂], ?_, ?_, by rw [sv, m₃]; exact lt₁, ?_⟩, hz₃⟩
  · refine ⟨fun r hr => ?_, ?_, ?_⟩
    · have hr' : r ∉ clob c.n := fun h => hr (List.mem_cons_of_mem _ h)
      have hrb : r ≠ .rbx := fun h => hr (h ▸ List.mem_cons_self ..)
      rw [k₃.1 _ (by simp), k₂.1 _ (by simp [hrb]), k₁.gpr r hr', I.keep.gpr r hr]
    · rw [k₃.2.2.1, k₂.2.2.1, k₁.rd, I.keep.rd]
    · rw [k₃.2.2.2, k₂.2.2.2, k₁.wr, I.keep.wr]
  · rw [m₃]
    exact (I.unch.trans U₁).mono (by intro w hw; simpa only [List.mem_append, or_self] using hw)
  · rw [sv, m₃]
    change toM c.C.p (2 ^ (64 * c.n)) (sv c base s₁ T3) ^ (2 ^ (j - 1)) = _
    rw [v₁, pow_mul_exponents,
      show 2 * 2 ^ (j - 1) = 2 ^ j by
        calc
          2 * 2 ^ (j - 1) = 2 ^ (j - 1) * 2 := Nat.mul_comm _ _
          _ = 2 ^ (j - 1 + 1) := (Nat.pow_succ _ _).symm
          _ = 2 ^ j := by rw [Nat.sub_add_cancel hj]]
    exact I.val

theorem squareLoop_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {count : Nat} {s : State}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hlt : sv c base s T3 < c.C.p) (hb : s.gpr .rbx = BitVec.ofNat 64 count)
    (hcount : count < 2 ^ 31) (hpos : 1 ≤ count) :
    WP isa (.loop (Impl.EcKey.Compressed.X86_64.squareStep c T3) .ne) s fun s' =>
      KeepRegs (powClob c.n) s s' ∧ Unch base (slW c [T3, TMP]) s.mem s'.mem ∧
      sv c base s' T3 < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' T3) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) ^ (2 ^ count) := by
  apply countLoop_ok (Inv := fun j t => SquareInv c base count s t j)
    (fun j t hj hjc hi => squareStep_ok hc hj hcount hjc hi) (n := count)
  · intro t I
    refine ⟨I.keep, I.unch, I.lt, ?_⟩
    simpa only [Nat.pow_zero, Lean.Grind.Semiring.pow_one] using I.val
  · exact hpos
  · exact ⟨hs, hM, hb, ⟨fun _ _ => rfl, rfl, rfl⟩, Unch.refl _ _ _, hlt, rfl⟩

theorem squarePower_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {count : Nat} {s : State}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hlt : sv c base s T3 < c.C.p) (hb : s.gpr .rbx = BitVec.ofNat 64 count)
    (hcount : count < 2 ^ 31) :
    WP isa (Impl.EcKey.Compressed.X86_64.squarePower c) s fun s' =>
      KeepRegs (powClob c.n) s s' ∧ Unch base (slW c [T3, TMP]) s.mem s'.mem ∧
      sv c base s' T3 < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' T3) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) ^ (2 ^ count) := by
  rw [Impl.EcKey.Compressed.X86_64.squarePower]
  refine WP.seq (WP.mono (testRbx_ok s (by omega) hb) fun s₁ ⟨hz₁, k₁⟩ => ?_)
  have hs₁ := hs.of_keeps k₁ (by decide)
  refine WP.ite (decide (count = 0)) hz₁ (fun hz => ?_) (fun hn => ?_)
  · have hn : count = 0 := of_decide_eq_true hz
    apply WP.block_nil
    refine ⟨(Keeps.regs k₁).mono (by simp), ?_, ?_, ?_⟩
    · rw [k₁.2.1]
      exact Unch.refl _ _ _
    · rw [sv, k₁.2.1]
      exact hlt
    · rw [sv, k₁.2.1, hn, Nat.pow_zero, Lean.Grind.Semiring.pow_one]
  · have hn : count ≠ 0 := of_decide_eq_false hn
    refine WP.mono (squareLoop_ok hc hs₁ (k₁.2.1 ▸ hM) (by rw [sv, k₁.2.1]; exact hlt)
      (by rw [k₁.1 _ (by decide), hb]) hcount (by omega)) fun t ⟨kt, Ut, lt, vt⟩ => ?_
    refine ⟨((Keeps.regs k₁).mono (by simp)).trans kt, ?_, lt, ?_⟩
    · rw [← k₁.2.1]
      exact Ut
    · simpa only [sv, k₁.2.1] using vt

end VG.Proof.EcKey.Compressed.X86_64
end

end

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/X86_64/DescentPower.lean`, which only this module imported.
section

/-! # The tested power in one P-224 descent round -/

section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.X25519.X86_64 (Keeps)

theorem descentPower_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State} {j : Nat}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hlt : sv c base s T0 < c.C.p) (hj : 1 ≤ j) (hj' : j < 2 ^ 31)
    (hword : word s.mem base (c.sl T2) = BitVec.ofNat 64 j) :
    WP isa (Impl.EcKey.Compressed.X86_64.descentPower c).inline s fun s' =>
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
    ([.mov .rbx (.mem (sc (c.sl T2)))] ++ [.alu .sub .rbx (.imm 1)])))
    (Impl.EcKey.Compressed.X86_64.squarePower c)) s _
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok c.n hs h3 (sl_le c h7 (by decide))
    (by have := sl_apart c (i := T3) (j := T0) (by decide); omega)) fun s₁ ⟨v₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have U₁ : Unch base (slW c [T3, TMP]) s.mem s₁.mem := slot_frame (by simp) (Nat.le_refl _) O₁
  have w₁ : word s₁.mem base (c.sl T2) = BitVec.ofNat 64 j := by
    rw [O₁.word (by have := sl_apart c (i := T2) (j := T3) (by decide); omega) (by omega), hword]
  rw [WP.block_append_iff]
  refine WP.mono (loadRbx_ok hs₁ (d := c.sl T2) (by omega)) fun s₂ ⟨hb₂, k₂⟩ => ?_
  rw [w₁] at hb₂
  refine WP.mono (decRbx_ok s₂ hj (by omega) hb₂) fun s₃ ⟨hb₃, k₃⟩ => ?_
  have hs₃ := (hs₁.of_keeps k₂ (by decide)).of_keeps k₃ (by decide)
  have m₃ : s₃.mem = s₁.mem := k₃.2.1.trans k₂.2.1
  have M₃ : ModOkW c.MP' size c.C.p s₃.mem base := modP_of hc (by
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
    exact ((K₁.trans ((Keeps.regs k₂).mono (by simp [powClob]))).trans
      ((Keeps.regs k₃).mono (by simp [powClob]))).trans kt
  · rw [m₃] at Ut
    exact unch_same U₁ Ut
  · change toM c.C.p (2 ^ (64 * c.n)) (sv c base t T3) =
      toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl T0) c.n) ^ (2 ^ (j - 1))
    simpa only [sv, m₃, v₁] using vt

end VG.Proof.EcKey.Compressed.X86_64
end

end

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/X86_64/DescentChoose.lean`, which only this module imported.
section

/-! # Select the correction factor of the P-224 descent -/

section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Impl.Ecdh.X86_64 (W0)
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64 VG.Proof.Ecdh.X86_64
open VG.Proof.X25519.X86_64 (Keeps)

theorem descentChoose_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (ht : sv c base s T3 < c.C.p) (hcval : sv c base s T1 < c.C.p)
    (hOne : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p) :
    WP isa (.block (Impl.EcKey.Compressed.X86_64.descentChoose c)) s fun t =>
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
  have ha := slots_apart (MP'_n c) (MP'_tmp c) (MP'_mo c)
    (o := W0) (a := T3) (b := ONEP) (by decide)
  rw [Impl.EcKey.Compressed.X86_64.descentChoose, List.append_assoc, List.append_assoc,
    WP.block_append_iff]
  refine WP.mono (sub_ok hs hM hW hT hO ha.1 ha.2.1 ha.2.2.1 ha.2.2.2 ht hOlt)
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
  refine WP.mono (zero_ok c hs₁ h0 hW) fun s₂ ⟨mask₂, k₂⟩ => ?_
  simp only [mask, show wordsVal s₁.mem base (c.sl W0) c.n = sv c base s₁ W0 from rfl, z₁] at mask₂
  rw [WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.mov .rcx (.reg .rdx)]) s₂ (fun s₃ =>
      s₃.gpr .rcx = s₂.gpr .rdx ∧ Keeps [.rcx] s₂ s₃) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
      RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s₃ ⟨m₃, k₃⟩ => ?_
  have hs₃ := (hs₁.of_keeps k₂ (by decide)).of_keeps k₃ (by decide)
  refine WP.mono (sel_ok (decide (toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) = 1)) c.n hs₃
    (by rw [m₃, mask₂]; simp only [decide_eq_true_eq]) hB hC hO
    (by have := sl_apart c (i := T4) (j := T1) (by decide); omega)
    (by have := sl_apart c (i := T4) (j := ONEP) (by decide); omega))
    fun t ⟨v₄, k₄, O₄⟩ => ?_
  have mem₃ : s₃.mem = s₁.mem := k₃.2.1.trans k₂.2.1
  have C₃ : sv c base s₃ T1 = sv c base s T1 := by
    rw [sv, mem₃]; exact sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)
  have O₃ : sv c base s₃ ONEP = sv c base s ONEP := by
    rw [sv, mem₃]; exact sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)
  change sv c base t T4 = _ at v₄
  simp only [decide_eq_true_eq] at v₄
  change sv c base t T4 = if _ then sv c base s₃ ONEP else sv c base s₃ T1 at v₄
  rw [C₃, O₃] at v₄
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (((⟨k₁.gpr, k₁.rd, k₁.wr⟩ : KeepRegs (clob c.n) s s₁).trans
      ((Keeps.regs k₂).mono (by intro r hr; obtain rfl := List.mem_singleton.mp hr; simp [clob]))).trans
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

end VG.Proof.EcKey.Compressed.X86_64
end

end

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/X86_64/DescentUpdate.lean`, which only this module imported.
section

/-! # The field updates in one P-224 descent round -/

section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Weierstrass
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

def descentN : List FOp :=
  [.mul ACC ACC T4, .mul T4 T4 T4, .mul T0 T0 T4, .mul T1 T1 T1]
abbrev descentFields : List Nat := [ACC, T0, T1, T4]
abbrev descentWritten : List Nat := [ACC, T0, T1, T4, TMP]

theorem descentOps_eq (c : Cfg) : Impl.EcKey.Compressed.X86_64.descentOps c =
    descentN.map (FOp.rename c.sl) := rfl

theorem descentN_run {F : Type} [Lean.Grind.CommRing F] (e : Nat → F) :
    runOps descentN e ACC = e ACC * e T4 ∧
    runOps descentN e T0 = e T0 * (e T4 * e T4) ∧
    runOps descentN e T1 = e T1 * e T1 := by
  simp only [descentN, runOps_cons, runOps_nil, FOp.run, Function.update_apply]
  simp only [ACC, T0, T1, T4, Nat.reduceEqDiff, ↓reduceIte, and_self]

theorem descentN_reads : readsOk descentN descentFields = true := by decide
theorem descentN_slots : ∀ op ∈ descentN, ∀ x ∈ op.out :: op.ins, x ∈ descentFields := by decide
theorem descentN_out : ∀ op ∈ descentN, op.out ∈ descentWritten := by decide

structure DescentUpdatePost (c : Cfg) (base : Addr) (s s' : State) : Prop where
  scr : Scr s' base size
  keep : KeepRegs (clob c.n) s s'
  unch : Unch base (slW c descentWritten) s.mem s'.mem
  lt : ∀ i ∈ [ACC, T0, T1], sv c base s' i < c.C.p
  r : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' ACC) =
    toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s T4)
  t : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' T0) =
    toM c.C.p (2 ^ (64 * c.n)) (sv c base s T0) *
      (toM c.C.p (2 ^ (64 * c.n)) (sv c base s T4) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s T4))
  c : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' T1) =
    toM c.C.p (2 ^ (64 * c.n)) (sv c base s T1) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s T1)

theorem descentUpdate_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hlt : ∀ i ∈ descentFields, sv c base s i < c.C.p) :
    WP isa (Impl.Weierstrass.X86_64.fprogB c.MP'
      (Impl.EcKey.Compressed.X86_64.descentOps c)).inline s (DescentUpdatePost c base s) := by
  have h7 := hc.n10
  have hL : Lay c.MP' size (· ∈ descentFields.map c.sl) := lay_map hc rfl rfl rfl (by decide)
  have I : Inv c.MP' base size c.C.p (· ∈ descentFields.map c.sl) (descentFields.map c.sl)
      (fun o => toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base o c.n)) s := by
    refine ⟨hs, hM, fun _ h => h, ?_, fun _ _ => rfl⟩
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact hlt i hi
  rw [descentOps_eq]
  refine WP.mono (fprogB_ok hL (unitMod_pow_two hc.p_odd (64 * c.n)) _ I
    (fun op hop x hx => ?_) (readsOk_rename c.sl descentN_reads)) fun t ⟨PK, IT⟩ => ?_
  · obtain ⟨op₀, h₀, rfl⟩ := List.mem_map.mp hop
    have hx' : x ∈ (op₀.out :: op₀.ins).map c.sl := by
      cases op₀ <;> simpa [FOp.rename, FOp.out, FOp.ins] using hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    exact List.mem_map_of_mem (descentN_slots _ h₀ _ hi)
  have hw {i : Nat} (hi : i ∈ [ACC, T0, T1]) :
      c.sl i ∈ validAfter (descentN.map (FOp.rename c.sl)) (descentFields.map c.sl) := by
    apply (mem_validAfter _ _).mpr
    exact Or.inl (List.mem_map_of_mem (by
      have sub : ∀ i ∈ [ACC, T0, T1], i ∈ descentFields := by decide
      exact sub i hi))
  have val {i : Nat} (hi : i ∈ [ACC, T0, T1]) := IT.val _ (hw hi)
  have vr := val (i := ACC) (by simp)
  have vt := val (i := T0) (by simp)
  have vc := val (i := T1) (by simp)
  rw [congrFun (runOps_rename c.sl descentN _ fun _ _ y h => sl_inj c hc.n0 h) ACC,
    (descentN_run _).1] at vr
  rw [congrFun (runOps_rename c.sl descentN _ fun _ _ y h => sl_inj c hc.n0 h) T0,
    (descentN_run _).2.1] at vt
  rw [congrFun (runOps_rename c.sl descentN _ fun _ _ y h => sl_inj c hc.n0 h) T1,
    (descentN_run _).2.2] at vc
  refine ⟨PK.scr hs, ⟨PK.gpr, PK.rd, PK.wr⟩, ?_, fun i hi => IT.lt _ (hw hi), vr, vt, vc⟩
  apply PK.unch.mono
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hw
    obtain ⟨op, hop, rfl⟩ := List.mem_map.mp ho
    obtain ⟨op₀, h₀, rfl⟩ := List.mem_map.mp hop
    exact List.mem_map.mpr ⟨op₀.out, descentN_out _ h₀, by rw [FOp.out_rename]; rfl⟩
  · obtain rfl := List.mem_singleton.mp hw
    exact List.mem_map_of_mem (by decide)

end VG.Proof.EcKey.Compressed.X86_64
end

end

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Impl.Ecdh.X86_64 (W0)
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Impl.EcKey.Compressed (rootDescent)

def roundSlots : List Nat := [T3, W0, T4, TMP, ACC, T0, T1, T2]

abbrev fieldAt (c : Cfg) (base : Addr) (s : State) (i : Nat) :=
  toM c.C.p (2 ^ (64 * c.n)) (sv c base s i)

structure DescentRoundPost (c : Cfg) (base : Addr) (j : Nat) (s s' : State) : Prop where
  scr : Scr s' base size
  keep : KeepRegs (powClob c.n) s s'
  unch : Unch base (slW c roundSlots) s.mem s'.mem
  lt : ∀ i ∈ [ACC, T0, T1], sv c base s' i < c.C.p
  counter : word s'.mem base (c.sl T2) = BitVec.ofNat 64 (j - 1)
  zf : s'.zf = some (decide (j - 1 = 0))
  descent : rootDescent (j - 1) (fieldAt c base s' ACC) (fieldAt c base s' T0) (fieldAt c base s' T1) =
    rootDescent j (fieldAt c base s ACC) (fieldAt c base s T0) (fieldAt c base s T1)

theorem descentRound_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State} {j : Nat}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hlt : ∀ i ∈ [ACC, T0, T1], sv c base s i < c.C.p)
    (hOne : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p)
    (hj : 1 ≤ j) (hj' : j < 2 ^ 31)
    (hword : word s.mem base (c.sl T2) = BitVec.ofNat 64 j) :
    WP isa (Impl.EcKey.Compressed.X86_64.descentRound c).inline s (DescentRoundPost c base j s) := by
  have h7 := hc.n10
  have h0 := hc.n0
  have hn := hs.nowrap
  change WP isa (.seq (Impl.EcKey.Compressed.X86_64.descentPower c).inline
    (.seq (.block (Impl.EcKey.Compressed.X86_64.descentChoose c))
      (.seq (Impl.Weierstrass.X86_64.fprogB c.MP' (Impl.EcKey.Compressed.X86_64.descentOps c)).inline
        (.block (Impl.EcKey.Compressed.X86_64.descentCounter c))))) s _
  refine WP.seq (WP.mono (descentPower_ok hc hs hM (hlt _ (by simp)) hj hj' hword)
    fun s₁ ⟨k₁, U₁, lt₁, v₁⟩ => ?_)
  have hs₁ := hs.of_keepRegs k₁ (rdi_not_powClob _)
  have e₁ {i : Nat} (hi : i < 45) (hw : i ∉ [T3, TMP]) : sv c base s₁ i = sv c base s i :=
    sv_unch U₁ h7 hn hi (apart_slW hw)
  have M₁ : ModOkW c.MP' size c.C.p s₁.mem base := modP_of hc (by
    change sv c base s₁ MP = _
    rw [e₁ (by decide) (by decide)]; exact hM.val)
  refine WP.seq (WP.mono (descentChoose_ok hc hs₁ M₁ lt₁
    (by rw [e₁ (by decide) (by decide)]; exact hlt _ (by simp))
    (by rw [e₁ (by decide) (by decide)]; exact hOne)) fun s₂ ⟨k₂, U₂, lt₂, v₂⟩ => ?_)
  have hs₂ := hs₁.of_keepRegs k₂ (rdi_not_clob _)
  have e₂ {i : Nat} (hi : i < 45) (hw : i ∉ [W0, T4, TMP]) : sv c base s₂ i = sv c base s₁ i :=
    sv_unch U₂ h7 hn hi (apart_slW hw)
  have M₂ : ModOkW c.MP' size c.C.p s₂.mem base := modP_of hc (by
    change sv c base s₂ MP = _
    rw [e₂ (by decide) (by decide)]; exact M₁.val)
  have b₂ : fieldAt c base s₂ T4 =
      if fieldAt c base s T0 ^ (2 ^ (j - 1)) = 1 then 1 else fieldAt c base s T1 := by
    unfold fieldAt
    rw [v₂, v₁, e₁ (by decide) (by decide)]
  refine WP.seq (WP.mono (descentUpdate_ok hc hs₂ M₂ (by
    intro i hi
    have sub : ∀ i ∈ descentFields, i ∈ [ACC, T0, T1] ∨ i = T4 := by decide
    rcases sub i hi with h | rfl
    · have hi45 : i < 45 := (by decide : ∀ i ∈ [ACC, T0, T1], i < 45) i h
      have hn₁ : i ∉ [T3, TMP] := (by decide : ∀ i ∈ [ACC, T0, T1], i ∉ [T3, TMP]) i h
      have hn₂ : i ∉ [W0, T4, TMP] := (by decide : ∀ i ∈ [ACC, T0, T1], i ∉ [W0, T4, TMP]) i h
      rw [e₂ hi45 hn₂, e₁ hi45 hn₁]; exact hlt i h
    · exact lt₂)) fun s₃ V => ?_)
  have U₁₂ := unch_same (slots_widen U₁ (by decide : ∀ i ∈ [T3, TMP], i ∈ roundSlots))
    (slots_widen U₂ (by decide : ∀ i ∈ [W0, T4, TMP], i ∈ roundSlots))
  have U₁₂₃ := unch_same U₁₂ (slots_widen V.unch (by decide : ∀ i ∈ descentWritten, i ∈ roundSlots))
  have w₃ : word s₃.mem base (c.sl T2) = BitVec.ofNat 64 j := by
    have U : Unch base (slW c [T3, W0, T4, TMP, ACC, T0, T1]) s.mem s₃.mem :=
      unch_same (unch_same (slots_widen U₁ (by decide)) (slots_widen U₂ (by decide)))
        (slots_widen V.unch (by decide))
    rw [U.word (fun w hw => by
      have := apart_slW (c := c) (by decide : T2 ∉ [T3, W0, T4, TMP, ACC, T0, T1]) w hw
      omega) (by have := sl_le c h7 (i := T2) (by decide); omega), hword]
  refine WP.mono (descentCounter_ok V.scr (by have := sl_le c h7 (i := T2) (by decide); omega)
    hj (by omega) w₃) fun s₄ ⟨word₄, zf₄, k₄, O₄⟩ => ?_
  have e₄ {i : Nat} (hi : i < 45) (hw : i ≠ T2) : sv c base s₄ i = sv c base s₃ i :=
    O₄.wordsVal (by have := sl_apart c hw; omega) (by have := sl_le c h7 hi; omega)
  refine ⟨V.scr.of_keepRegs k₄ (by decide), ?_,
    unch_same U₁₂₃ (slot_frame (by decide : T2 ∈ roundSlots) (by omega) O₄), ?_, word₄, zf₄, ?_⟩
  · exact ((k₁.trans (k₂.mono (fun _ h => List.mem_cons_of_mem _ h))).trans
      (V.keep.mono (fun _ h => List.mem_cons_of_mem _ h))).trans (k₄.mono (by simp [powClob]))
  · intro i hi
    have hi45 : i < 45 := (by decide : ∀ i ∈ [ACC, T0, T1], i < 45) i hi
    have hn₂ : i ≠ T2 := (by decide : ∀ i ∈ [ACC, T0, T1], i ≠ T2) i hi
    rw [e₄ hi45 hn₂]; exact V.lt i hi
  · have r₄ : fieldAt c base s₄ ACC = fieldAt c base s ACC * fieldAt c base s₂ T4 := by
      rw [fieldAt, e₄ (by decide) (by decide), V.r, e₂ (by decide) (by decide), e₁ (by decide) (by decide)]
    have t₄ : fieldAt c base s₄ T0 = fieldAt c base s T0 * (fieldAt c base s₂ T4 * fieldAt c base s₂ T4) := by
      rw [fieldAt, e₄ (by decide) (by decide), V.t, e₂ (by decide) (by decide), e₁ (by decide) (by decide)]
    have c₄ : fieldAt c base s₄ T1 = fieldAt c base s T1 * fieldAt c base s T1 := by
      rw [fieldAt, e₄ (by decide) (by decide), V.c, e₂ (by decide) (by decide), e₁ (by decide) (by decide)]
    conv_rhs => rw [show j = j - 1 + 1 by omega, rootDescent]
    simp only [pow_eq_npow]
    rw [r₄, t₄, c₄, b₂]

end VG.Proof.EcKey.Compressed.X86_64
