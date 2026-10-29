module

public import VerifiedGarbage.Impl.EcKey.Compressed.Root
public import VerifiedGarbage.Impl.EcKey.Compressed.AArch64.Decompress
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Fixed

import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.DescentChoose
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Counter
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Frame
import VerifiedGarbage.Proof.Weierstrass.AArch64.Pow
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Ecdh.AArch64.Validate
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
import VerifiedGarbage.Proof.Ecdsa.AArch64.Middle
import VerifiedGarbage.Proof.Weierstrass.AArch64.Unch
import VerifiedGarbage.Proof.Weierstrass.RootPowers
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Weierstrass.AArch64.Fprog
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Spec.Weierstrass
/-! # One machine round refines the functional P-224 root descent -/

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/AArch64/Square.lean`, which only this module imported.
section

/-! # Repeated squaring for the P-224 descent -/

section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

 structure SquareInv (c : Cfg) (base : Addr) (count : Nat) (s₀ s : State) (j : Nat) : Prop where
  scr : Scr s base size
  mod : ModOkA c.MP' size c.C.p s.mem base
  counter : s.gpr .x19 = BitVec.ofNat 64 j
  keep : KeepRegs (powClob c.n) s₀ s
  unch : Unch base (slW c [T3, TMP]) s₀.mem s.mem
  lt : sv c base s T3 < c.C.p
  val : toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) ^ (2 ^ j) =
    toM c.C.p (2 ^ (64 * c.n)) (sv c base s₀ T3) ^ (2 ^ count)

 theorem squareStep_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {count j : Nat}
    (hj : 1 ≤ j) (hcount : count < 2 ^ 31) (hjc : j ≤ count) {s₀ s : State}
    (I : SquareInv c base count s₀ s j) :
    WP isa (Impl.EcKey.Compressed.AArch64.squareStep c T3) s fun t =>
      SquareInv c base count s₀ t (j - 1) ∧ t.gpr .x19 = BitVec.ofNat 64 (j - 1) := by
  have h7 := hc.n10
  have hn := I.scr.nowrap
  have hT := sl_le c h7 (i := T3) (by decide)
  rw [Impl.EcKey.Compressed.AArch64.squareStep, WP.block_append_iff]
  refine WP.mono (mulOp_ok I.scr I.mod (MP'_A c) hT hT hT
    (sl_mod8 c T3) (sl_mod8 c T3) (sl_mod8 c T3) I.lt)
    fun s₁ ⟨k₁, lt₁, e₁⟩ => ?_
  have hs₁ := k₁.scr I.scr
  have hm₁ := I.mod.keepA64 (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  have hb₁ : s₁.gpr .x19 = BitVec.ofNat 64 j :=
    (k₁.gpr _ (x19_not_clob c.n)).trans I.counter
  have U₁ : Unch base (slW c [T3, TMP]) s.mem s₁.mem :=
    unch_slots (MP'_n c) rfl k₁.unch (by simp) (by simp)
  have v₁ : toM c.C.p (2 ^ (64 * c.n)) (sv c base s₁ T3) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) ^ 2 := by
    have e : sv c base s₁ T3 * 2 ^ (64 * c.n) % c.C.p =
        sv c base s T3 * sv c base s T3 % c.C.p := e₁
    rw [toM_mul (unitMod_pow_two hc.p_odd (64 * c.n)) e, Lean.Grind.Semiring.pow_two]
  refine WP.mono (decCounter_ok s₁ hj (by omega) hb₁) fun t ⟨hb₂, k₂⟩ => ?_
  refine ⟨⟨hs₁.of_keeps k₂ (by decide), by rw [k₂.mem]; exact hm₁, hb₂,
    ?_, ?_, by rw [sv, k₂.mem]; exact lt₁, ?_⟩, hb₂⟩
  · have K : KeepRegs (powClob c.n) s s₁ :=
      ⟨fun r hr => k₁.gpr r (fun h => hr (List.mem_cons_of_mem _ h)), k₁.rd, k₁.wr, k₁.sp⟩
    exact (I.keep.trans K).trans ((Keeps.regs k₂).mono (by simp [powClob]))
  · rw [k₂.mem]
    exact (I.unch.trans U₁).mono (by intro w hw; simpa only [List.mem_append, or_self] using hw)
  · rw [sv, k₂.mem]
    change toM c.C.p (2 ^ (64 * c.n)) (sv c base s₁ T3) ^ (2 ^ (j - 1)) = _
    rw [v₁, pow_mul_exponents,
      show 2 * 2 ^ (j - 1) = 2 ^ j by
        calc
          2 * 2 ^ (j - 1) = 2 ^ (j - 1) * 2 := Nat.mul_comm _ _
          _ = 2 ^ (j - 1 + 1) := (Nat.pow_succ _ _).symm
          _ = 2 ^ j := by rw [Nat.sub_add_cancel hj]]
    exact I.val

 theorem squareLoop_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {count : Nat} {s : State}
    (hs : Scr s base size) (hM : ModOkA c.MP' size c.C.p s.mem base)
    (hlt : sv c base s T3 < c.C.p) (hb : s.gpr .x19 = BitVec.ofNat 64 count)
    (hcount : count < 2 ^ 31) (hpos : 1 ≤ count) :
    WP isa (.loop (Impl.EcKey.Compressed.AArch64.squareStep c T3) (.nonzero .x .x19)) s fun t =>
      KeepRegs (powClob c.n) s t ∧ Unch base (slW c [T3, TMP]) s.mem t.mem ∧
      sv c base t T3 < c.C.p ∧ toM c.C.p (2 ^ (64 * c.n)) (sv c base t T3) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) ^ (2 ^ count) := by
  apply countLoop_ok (Inv := fun j t => SquareInv c base count s t j) (by omega)
    (fun j t hj hjc hi => squareStep_ok hc hj hcount hjc hi) (n := count)
  · intro t I
    refine ⟨I.keep, I.unch, I.lt, ?_⟩
    simpa only [Nat.pow_zero, Lean.Grind.Semiring.pow_one] using I.val
  · exact hpos
  · exact ⟨hs, hM, hb, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, Unch.refl _ _ _, hlt, rfl⟩

 theorem squarePower_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {count : Nat} {s : State}
    (hs : Scr s base size) (hM : ModOkA c.MP' size c.C.p s.mem base)
    (hlt : sv c base s T3 < c.C.p) (hb : s.gpr .x19 = BitVec.ofNat 64 count)
    (hcount : count < 2 ^ 31) :
    WP isa (Impl.EcKey.Compressed.AArch64.squarePower c) s fun t =>
      KeepRegs (powClob c.n) s t ∧ Unch base (slW c [T3, TMP]) s.mem t.mem ∧
      sv c base t T3 < c.C.p ∧ toM c.C.p (2 ^ (64 * c.n)) (sv c base t T3) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) ^ (2 ^ count) := by
  have ev : isa.eval (.zero .x .x19) s = some (decide (count = 0)) := by
    change some (s.read .x .x19 == 0) = _
    rw [read_x, hb]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro h
      have := congrArg BitVec.toNat h
      change count % 2 ^ 64 = 0 at this
      rwa [Nat.mod_eq_of_lt (show count < 2 ^ 64 by omega)] at this
    · intro h; subst h; rfl
  apply WP.ite _ ev
  · intro hz
    have hz : count = 0 := of_decide_eq_true hz
    apply WP.block_nil
    refine ⟨⟨fun _ _ => rfl, rfl, rfl, rfl⟩, Unch.refl _ _ _, hlt, ?_⟩
    rw [hz, Nat.pow_zero, Lean.Grind.Semiring.pow_one]
  · intro hz
    exact squareLoop_ok hc hs hM hlt hb hcount (by have := of_decide_eq_false hz; omega)

end VG.Proof.EcKey.Compressed.AArch64
end

end

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/AArch64/DescentPower.lean`, which only this module imported.
section

/-! # The tested power in one P-224 descent round -/

section

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
end

end

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/AArch64/DescentUpdate.lean`, which only this module imported.
section

/-! # The field updates in one P-224 descent round -/

section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

def descentN : List FOp :=
  [.mul ACC ACC T4, .mul T4 T4 T4, .mul T0 T0 T4, .mul T1 T1 T1]
abbrev descentFields : List Nat := [ACC, T0, T1, T4]
abbrev descentWritten : List Nat := [ACC, T0, T1, T4, TMP]

theorem descentOps_eq (c : Cfg) : Impl.EcKey.Compressed.AArch64.descentOps c =
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
    (hs : Scr s base size) (hM : ModOkA c.MP' size c.C.p s.mem base)
    (hlt : ∀ i ∈ descentFields, sv c base s i < c.C.p) :
    WP isa (Impl.Weierstrass.AArch64.fprogB c.MP'
      (Impl.EcKey.Compressed.AArch64.descentOps c)) s (DescentUpdatePost c base s) := by
  have h7 := hc.n10
  have hL : Lay c.MP' size (· ∈ descentFields.map c.sl) := lay_map hc rfl rfl rfl (by decide)
  have hAl : Aligned c.MP' (· ∈ descentFields.map c.sl) := ⟨fun x hx => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact sl_mod8 c i, MP'_A c, fun f m h => (hc.call_p f m h).2⟩
  have I : Inv c.MP' base size c.C.p (· ∈ descentFields.map c.sl) (descentFields.map c.sl)
      (fun o => toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base o c.n)) s := by
    refine ⟨hs, hM, fun _ h => h, ?_, fun _ _ => rfl⟩
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact hlt i hi
  rw [descentOps_eq]
  refine WP.mono (fprogB_ok hL hAl (unitMod_pow_two hc.p_odd (64 * c.n)) _ I
    (fun op hop x hx => ?_) (by
      intro op hop
      apply Low.of_call
      intro f m h x hx
      obtain ⟨op₀, hop₀, rfl⟩ := List.mem_map.mp hop
      have hx' : x ∈ (op₀.out :: op₀.ins).map c.sl := by
        cases op₀ <;> simpa [FOp.rename, FOp.out, FOp.ins] using hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
      have hi' := descentN_slots op₀ hop₀ i hi
      have H : ∀ i ∈ descentFields, i < 45 ∧ i ≠ TMP := by decide
      exact sl_own_fn c h7 (H i hi').1 (H i hi').2)
    (readsOk_rename c.sl descentN_reads)) fun t ⟨PK, IT⟩ => ?_
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
  have H : ∀ op ∈ descentN, op.out ≠ TMP ∧ op.out ≠ 54 ∧ op.out ≠ 61 ∧ op.out ≠ 82 := by decide
  rw [congrFun (runOps_rename c.sl descentN _ fun op hop y h => sl_inj c hc.n0 h (.inr (H op hop).2) (.inl (H op hop).1)) ACC,
    (descentN_run _).1] at vr
  rw [congrFun (runOps_rename c.sl descentN _ fun op hop y h => sl_inj c hc.n0 h (.inr (H op hop).2) (.inl (H op hop).1)) T0,
    (descentN_run _).2.1] at vt
  rw [congrFun (runOps_rename c.sl descentN _ fun op hop y h => sl_inj c hc.n0 h (.inr (H op hop).2) (.inl (H op hop).1)) T1,
    (descentN_run _).2.2] at vc
  refine ⟨PK.scr hs, ⟨PK.gpr, PK.rd, PK.wr, PK.sp⟩, ?_, fun i hi => IT.lt _ (hw hi), vr, vt, vc⟩
  apply PK.unch.mono
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hw
    obtain ⟨op, hop, rfl⟩ := List.mem_map.mp ho
    obtain ⟨op₀, h₀, rfl⟩ := List.mem_map.mp hop
    exact List.mem_map.mpr ⟨op₀.out, descentN_out _ h₀, by rw [FOp.out_rename]; rfl⟩
  · obtain rfl := List.mem_singleton.mp hw
    exact List.mem_map_of_mem (by decide)

end VG.Proof.EcKey.Compressed.AArch64
end

end

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Impl.Ecdh.AArch64 (W0)
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.EcKey.Compressed (rootDescent)

def roundSlots : List Nat := [T3, W0, T4, TMP, ACC, T0, T1]

abbrev fieldAt (c : Cfg) (base : Addr) (s : State) (i : Nat) :=
  toM c.C.p (2 ^ (64 * c.n)) (sv c base s i)

structure DescentBodyPost (c : Cfg) (base : Addr) (j : Nat) (s s' : State) : Prop where
  scr : Scr s' base size
  keep : KeepRegs (powClob c.n) s s'
  unch : Unch base (slW c roundSlots) s.mem s'.mem
  lt : ∀ i ∈ [ACC, T0, T1], sv c base s' i < c.C.p
  descent : rootDescent (j - 1) (fieldAt c base s' ACC) (fieldAt c base s' T0) (fieldAt c base s' T1) =
    rootDescent j (fieldAt c base s ACC) (fieldAt c base s T0) (fieldAt c base s T1)

theorem descentBody_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State} {j : Nat}
    (hs : Scr s base size) (hM : ModOkA c.MP' size c.C.p s.mem base)
    (hlt : ∀ i ∈ [ACC, T0, T1], sv c base s i < c.C.p)
    (hOne : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p)
    (hj : 1 ≤ j) (hj' : j < 2 ^ 31)
    (hword : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (Impl.EcKey.Compressed.AArch64.descentBody c) s (DescentBodyPost c base j s) := by
  have h7 := hc.n10
  have h0 := hc.n0
  have hn := hs.nowrap
  change WP isa (.seq (Impl.EcKey.Compressed.AArch64.descentPower c)
    (.seq (.block (Impl.EcKey.Compressed.AArch64.descentChoose c))
      (Impl.Weierstrass.AArch64.fprogB c.MP' (Impl.EcKey.Compressed.AArch64.descentOps c)))) s _
  refine WP.seq (WP.mono (descentPower_ok hc hs hM (hlt _ (by simp)) hj hj' hword)
    fun s₁ ⟨k₁, U₁, lt₁, v₁⟩ => ?_)
  have hs₁ := hs.of_keepRegs k₁ (x0_not_powClob _)
  have e₁ {i : Nat} (hi : i < 45) (hw : i ∉ [T3, TMP]) : sv c base s₁ i = sv c base s i :=
    sv_unch U₁ h7 hn hi (apart_slW hw)
  have M₁ : ModOkA c.MP' size c.C.p s₁.mem base := modP_of hc (by
    change sv c base s₁ MP = _
    rw [e₁ (by decide) (by decide)]; exact hM.val)
  refine WP.seq (WP.mono (descentChoose_ok hc hs₁ M₁ lt₁
    (by rw [e₁ (by decide) (by decide)]; exact hlt _ (by simp))
    (by rw [e₁ (by decide) (by decide)]; exact hOne)) fun s₂ ⟨k₂, U₂, lt₂, v₂⟩ => ?_)
  have hs₂ := hs₁.of_keepRegs k₂ (by intro h; exact (by decide : VG.AArch64.Reg.x0 ∉ VG.Proof.Mont.AArch64.clobAll) (VG.Proof.Mont.AArch64.mem_clobAll h))
  have e₂ {i : Nat} (hi : i < 45) (hw : i ∉ [W0, T4, TMP]) : sv c base s₂ i = sv c base s₁ i :=
    sv_unch U₂ h7 hn hi (apart_slW hw)
  have M₂ : ModOkA c.MP' size c.C.p s₂.mem base := modP_of hc (by
    change sv c base s₂ MP = _
    rw [e₂ (by decide) (by decide)]; exact M₁.val)
  have b₂ : fieldAt c base s₂ T4 =
      if fieldAt c base s T0 ^ (2 ^ (j - 1)) = 1 then 1 else fieldAt c base s T1 := by
    unfold fieldAt
    rw [v₂, v₁, e₁ (by decide) (by decide)]
  refine WP.mono (descentUpdate_ok hc hs₂ M₂ (by
    intro i hi
    have sub : ∀ i ∈ descentFields, i ∈ [ACC, T0, T1] ∨ i = T4 := by decide
    rcases sub i hi with h | rfl
    · have hi45 : i < 45 := (by decide : ∀ i ∈ [ACC, T0, T1], i < 45) i h
      have hn₁ : i ∉ [T3, TMP] := (by decide : ∀ i ∈ [ACC, T0, T1], i ∉ [T3, TMP]) i h
      have hn₂ : i ∉ [W0, T4, TMP] := (by decide : ∀ i ∈ [ACC, T0, T1], i ∉ [W0, T4, TMP]) i h
      rw [e₂ hi45 hn₂, e₁ hi45 hn₁]; exact hlt i h
    · exact lt₂)) fun s₃ V => ?_
  have U₁₂ := unch_same (slots_widen U₁ (by decide : ∀ i ∈ [T3, TMP], i ∈ roundSlots))
    (slots_widen U₂ (by decide : ∀ i ∈ [W0, T4, TMP], i ∈ roundSlots))
  have U₁₂₃ := unch_same U₁₂ (slots_widen V.unch (by decide : ∀ i ∈ descentWritten, i ∈ roundSlots))
  refine ⟨V.scr, ?_, U₁₂₃, V.lt, ?_⟩
  · exact (k₁.trans (k₂.mono (fun _ h => List.mem_cons_of_mem _ h))).trans
      (V.keep.mono (fun _ h => List.mem_cons_of_mem _ h))
  · have r₄ : fieldAt c base s₃ ACC = fieldAt c base s ACC * fieldAt c base s₂ T4 := by
      rw [fieldAt, V.r, e₂ (by decide) (by decide), e₁ (by decide) (by decide)]
    have t₄ : fieldAt c base s₃ T0 = fieldAt c base s T0 * (fieldAt c base s₂ T4 * fieldAt c base s₂ T4) := by
      rw [fieldAt, V.t, e₂ (by decide) (by decide), e₁ (by decide) (by decide)]
    have c₄ : fieldAt c base s₃ T1 = fieldAt c base s T1 * fieldAt c base s T1 := by
      rw [fieldAt, V.c, e₂ (by decide) (by decide), e₁ (by decide) (by decide)]
    conv_rhs => rw [show j = j - 1 + 1 by omega, rootDescent]
    simp only [pow_eq_npow]
    rw [r₄, t₄, c₄, b₂]

 structure DescentRoundPost (c : Cfg) (base : Addr) (j : Nat) (s t : State) : Prop where
  scr : Scr t base size
  keep : KeepRegs (powClob c.n) s t
  unch : Unch base (slW c roundSlots) s.mem t.mem
  lt : ∀ i ∈ [ACC, T0, T1], sv c base t i < c.C.p
  counter : t.gpr .x19 = BitVec.ofNat 64 (j - 1)
  descent : rootDescent (j - 1) (fieldAt c base t ACC) (fieldAt c base t T0) (fieldAt c base t T1) =
    rootDescent j (fieldAt c base s ACC) (fieldAt c base s T0) (fieldAt c base s T1)

 theorem descentRound_ok {c : Cfg} (hc : BaseCfgOk c)
    (hV : ∀ i ∈ instrs (Impl.EcKey.Compressed.AArch64.descentBody c), vdstOf i ≠ some .v27)
    {base : Addr} {s : State} {j : Nat} (hs : Scr s base size)
    (hM : ModOkA c.MP' size c.C.p s.mem base)
    (hlt : ∀ i ∈ [ACC, T0, T1], sv c base s i < c.C.p)
    (hOne : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p)
    (hj : 1 ≤ j) (hj' : j < 2 ^ 31) (hcounter : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (Impl.EcKey.Compressed.AArch64.descentRound c) s (DescentRoundPost c base j s) := by
  refine WP.seq (WP.mono (saveCounter_ok s) fun u ⟨g, m, rd, wr, sp, saved⟩ => ?_)
  have hs₁ : Scr u base size := ⟨by rw [g]; exact hs.x0, by rw [wr]; exact hs.wr, hs.nowrap, hs.enc⟩
  have e (i : Nat) : sv c base u i = sv c base s i := by rw [sv, m]
  have M₁ : ModOkA c.MP' size c.C.p u.mem base := by rw [m]; exact hM
  refine WP.seq (WP.mono (VG.Proof.Ecdh.AArch64.WP.keepV hV
    (descentBody_ok hc hs₁ M₁ (by intro i hi; rw [e]; exact hlt i hi)
      (by rw [e]; exact hOne) hj hj' (by rw [g]; exact hcounter)))
    fun v ⟨R, hv⟩ => ?_)
  have counter : laneOf v .v27 0 = BitVec.ofNat 64 j := by
    change (v.v .v27).extractLsb' (64 * 0) 64 = _
    rw [hv]
    exact saved.trans hcounter
  refine WP.mono (descentCounter_ok hj (by omega) counter) fun t ⟨ct, K⟩ => ?_
  refine ⟨R.scr.of_keeps K (by decide), ?_, ?_, ?_, ct, ?_⟩
  · have K₁ : KeepRegs (powClob c.n) s u := ⟨fun r _ => congrFun g r, rd, wr, sp⟩
    exact (K₁.trans R.keep).trans ((Keeps.regs K).mono (by simp [powClob]))
  · simpa only [K.mem, m] using R.unch
  · intro i hi
    change wordsVal t.mem _ _ _ < _
    rw [K.mem]
    exact R.lt i hi
  · simpa only [fieldAt, sv, K.mem, m] using R.descent

end VG.Proof.EcKey.Compressed.AArch64
