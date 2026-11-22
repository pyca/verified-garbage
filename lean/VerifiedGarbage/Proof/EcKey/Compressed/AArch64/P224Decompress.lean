module

public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.DecompressMain
public import VerifiedGarbage.Impl.EcKey.Compressed.Root
public import VerifiedGarbage.Impl.EcKey.Compressed.AArch64.Decompress
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Fixed
import VerifiedGarbage.Proof.Weierstrass.AArch64.Fprog
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
import VerifiedGarbage.Proof.Ecdsa.AArch64.Middle
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Proof.Weierstrass.AArch64.Unch
import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
import VerifiedGarbage.Proof.Mont.AArch64.Ops
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
public import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract
import VerifiedGarbage.Proof.Weierstrass.AArch64.Pow
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Ecdh.AArch64.Validate
import VerifiedGarbage.Proof.Weierstrass.Sqrt
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.P224.Sqrt
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.LaneTaint
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneTaint
public import VerifiedGarbage.Spec.EcKey.P224
import VerifiedGarbage.Proof.Ecdsa.AArch64.P224.Verified
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Weierstrass.AArch64.P224Literals
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.P224Literals
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.AArch64
meta import VerifiedGarbage.Impl.Ecdsa.P224.AArch64
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
meta import VerifiedGarbage.Impl.EcKey.Compressed.AArch64.Decompress
meta import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Contract
public import VerifiedGarbage.Impl.Ecdsa.P224.AArch64
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec

/-! ### `EcKey.Compressed.AArch64.Tonelli`, which only this module used -/

section

/-! ### `EcKey.Compressed.AArch64.DescentRound`, which only this module used -/

section

/-! ### `EcKey.Compressed.AArch64.DescentChoose`, which only this module used -/

section

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
  obtain hW := sl_le c h7 (i := W0) (by decide)
  obtain hT := sl_le c h7 (i := T3) (by decide)
  obtain hC := sl_le c h7 (i := T1) (by decide)
  obtain hB := sl_le c h7 (i := T4) (by decide)
  obtain hO := sl_le c h7 (i := ONEP) (by decide)
  obtain hOlt : sv c base s ONEP < c.C.p := by rw [hOne]; exact Nat.mod_lt _ (by omega_using [ht])
  rw [Impl.EcKey.Compressed.AArch64.descentChoose, List.append_assoc, List.append_assoc,
    WP.block_append_iff]
  refine WP.mono (subOp_ok hs hM (MP'_A c) hW hT hO (sl_mod8 c W0) (sl_mod8 c T3) (sl_mod8 c ONEP) ht hOlt)
    fun s₁ ⟨k₁, e₁⟩ => ?_
  change sv c base s₁ W0 = (sv c base s T3 + c.C.p - sv c base s ONEP) % c.C.p at e₁
  obtain hs₁ := k₁.scr hs
  obtain lt₁ : sv c base s₁ W0 < c.C.p := by
    rw [e₁]; exact Nat.mod_lt _ (by omega_using [ht])
  obtain v₁ : toM c.C.p (2 ^ (64 * c.n)) (sv c base s₁ W0) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) - 1 := by
    rw [e₁, toM_sub (by omega_using [hOlt]), hOne, toM_one (unitMod_pow_two hc.p_odd (64 * c.n))]
  obtain z₁ : sv c base s₁ W0 = 0 ↔ toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) = 1 := by
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
  obtain hs₃ := (hs₁.of_keeps k₂ (by decide)).of_keeps k₃ (by decide)
  refine WP.mono (sel_ok (decide (toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) = 1)) c.n hs₃
    (by rw [m₃, mask₂]; simp only [decide_eq_true_eq]) hB hC hO (sl_mod8 c T4) (sl_mod8 c T1) (sl_mod8 c ONEP)
    (by have := sl_apart c (i := T4) (j := T1) (by decide); omega_using [this])
    (by have := sl_apart c (i := T4) (j := ONEP) (by decide); omega_using [this]))
    fun t ⟨v₄, k₄, O₄⟩ => ?_
  obtain mem₃ : s₃.mem = s₁.mem := k₃.mem.trans k₂.mem
  obtain C₃ : sv c base s₃ T1 = sv c base s T1 := by
    rw [sv, mem₃]; exact sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)
  obtain O₃ : sv c base s₃ ONEP = sv c base s ONEP := by
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

end

end

/-! ### `EcKey.Compressed.AArch64.Counter`, which only this module used -/

section

/-! # Retain the public outer counter across the inner squaring loop -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps)

 theorem saveCounter_ok (s : State) :
    WP isa (.block [.vop (.ins .d2 .v27 0 .x19)]) s fun t =>
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      laneOf t .v27 0 = s.gpr .x19 := by
  exact WP.mono (insOf_ok [(.x19, .v27, 0)] s (by decide) (by decide))
    fun _ ⟨g, m, r, w, sp, L, _⟩ => ⟨g, m, r, w, sp, L (.x19, .v27, 0) (by simp)⟩

 theorem descentCounter_ok {s : State} {j : Nat} (hj : 1 ≤ j) (hj' : j < 2 ^ 64)
    (hcounter : laneOf s .v27 0 = BitVec.ofNat 64 j) :
    WP isa (.block Impl.EcKey.Compressed.AArch64.descentCounter) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (j - 1) ∧ Keeps [.x19] s t := by
  change WP isa (.block (umovOf [(.x19, .v27, 0)] ++ [decCounter])) s _
  rw [WP.block_append_iff]
  refine WP.mono (umovOf_ok [(.x19, .v27, 0)] s (by decide) (by decide))
    fun t ⟨m, r, w, sp, L, G⟩ => ?_
  obtain e : t.gpr .x19 = BitVec.ofNat 64 j := (L (.x19, .v27, 0) (by simp)).trans hcounter
  refine WP.mono (decCounter_ok t hj hj' e) fun u ⟨v, K⟩ => ?_
  refine ⟨v, ?_⟩
  obtain K₁ : Keeps [.x19] s t := ⟨G, m, r, w, sp⟩
  exact K₁.trans K

end VG.Proof.EcKey.Compressed.AArch64

end

end

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
  obtain hT := sl_le c h7 (i := T3) (by decide)
  rw [Impl.EcKey.Compressed.AArch64.squareStep, WP.block_append_iff]
  refine WP.mono (mulOp_ok I.scr I.mod (MP'_A c) hT hT hT
    (sl_mod8 c T3) (sl_mod8 c T3) (sl_mod8 c T3) I.lt)
    fun s₁ ⟨k₁, lt₁, e₁⟩ => ?_
  obtain hs₁ := k₁.scr I.scr
  obtain hm₁ := I.mod.keepA64 (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  obtain hb₁ : s₁.gpr .x19 = BitVec.ofNat 64 j :=
    (k₁.gpr _ (x19_not_clob c.n)).trans I.counter
  obtain U₁ : Unch base (slW c [T3, TMP]) s.mem s₁.mem :=
    unch_slots (MP'_n c) rfl k₁.unch (by simp) (by simp)
  obtain v₁ : toM c.C.p (2 ^ (64 * c.n)) (sv c base s₁ T3) =
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
  obtain ev : isa.eval (.zero .x .x19) s = some (decide (count = 0)) := by
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
    obtain hz : count = 0 := of_decide_eq_true hz
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
  obtain h3 := sl_le c h7 (i := T3) (by decide)
  obtain h2 := sl_le c h7 (i := T2) (by decide)
  change WP isa (.seq (.block (copy c.n (c.sl T3) (c.sl T0) ++
    [decCounter]))
    (Impl.EcKey.Compressed.AArch64.squarePower c)) s _
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok c.n hs h3 (sl_le c h7 (by decide)) (sl_mod8 c T3) (sl_mod8 c T0)
    (by have := sl_apart c (i := T3) (j := T0) (by decide); omega)) fun s₁ ⟨v₁, k₁, O₁⟩ => ?_
  obtain hs₁ := hs.of_keepRegs k₁ (by decide)
  obtain U₁ : Unch base (slW c [T3, TMP]) s.mem s₁.mem := slot_frame (by simp) (Nat.le_refl _) O₁
  obtain w₁ : s₁.gpr .x19 = BitVec.ofNat 64 j := (k₁.gpr _ (by decide)).trans hword
  refine WP.mono (decCounter_ok s₁ hj (by omega) w₁) fun s₃ ⟨hb₃, k₃⟩ => ?_
  obtain hs₃ := hs₁.of_keeps k₃ (by decide)
  have m₃ : s₃.mem = s₁.mem := k₃.mem
  obtain M₃ : ModOkA c.MP' size c.C.p s₃.mem base := modP_of hc (by
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
  obtain hL : Lay c.MP' size (· ∈ descentFields.map c.sl) := lay_map hc rfl rfl rfl (by decide)
  obtain hAl : Aligned c.MP' (· ∈ descentFields.map c.sl) := ⟨fun x hx => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact sl_mod8 c i, MP'_A c, fun f m h => (hc.call_p f m h).2⟩
  obtain I : Inv c.MP' base size c.C.p (· ∈ descentFields.map c.sl) (descentFields.map c.sl)
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
      obtain hx' : x ∈ (op₀.out :: op₀.ins).map c.sl := by
        cases op₀ <;> simpa [FOp.rename, FOp.out, FOp.ins] using hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
      obtain hi' := descentN_slots op₀ hop₀ i hi
      obtain H : ∀ i ∈ descentFields, i < 45 ∧ i ≠ TMP := by decide
      exact sl_own_fn c h7 (H i hi').1 (H i hi').2)
    (readsOk_rename c.sl descentN_reads)) fun t ⟨PK, IT⟩ => ?_
  · obtain ⟨op₀, h₀, rfl⟩ := List.mem_map.mp hop
    obtain hx' : x ∈ (op₀.out :: op₀.ins).map c.sl := by
      cases op₀ <;> simpa [FOp.rename, FOp.out, FOp.ins] using hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    exact List.mem_map_of_mem (descentN_slots _ h₀ _ hi)
  have hw {i : Nat} (hi : i ∈ [ACC, T0, T1]) :
      c.sl i ∈ validAfter (descentN.map (FOp.rename c.sl)) (descentFields.map c.sl) := by
    apply (mem_validAfter _ _).mpr
    exact Or.inl (List.mem_map_of_mem (by
      obtain sub : ∀ i ∈ [ACC, T0, T1], i ∈ descentFields := by decide
      exact sub i hi))
  have val {i : Nat} (hi : i ∈ [ACC, T0, T1]) := IT.val _ (hw hi)
  obtain vr := val (i := ACC) (by simp)
  obtain vt := val (i := T0) (by simp)
  obtain vc := val (i := T1) (by simp)
  obtain H : ∀ op ∈ descentN, op.out ≠ TMP ∧ op.out ≠ 54 ∧ op.out ≠ 61 ∧ op.out ≠ 82 := by decide
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
  obtain hs₁ := hs.of_keepRegs k₁ (x0_not_powClob _)
  have e₁ {i : Nat} (hi : i < 45) (hw : i ∉ [T3, TMP]) : sv c base s₁ i = sv c base s i :=
    sv_unch U₁ h7 hn hi (apart_slW hw)
  obtain M₁ : ModOkA c.MP' size c.C.p s₁.mem base := modP_of hc (by
    change sv c base s₁ MP = _
    rw [e₁ (by decide) (by decide)]; exact hM.val)
  refine WP.seq (WP.mono (descentChoose_ok hc hs₁ M₁ lt₁
    (by rw [e₁ (by decide) (by decide)]; exact hlt _ (by simp))
    (by rw [e₁ (by decide) (by decide)]; exact hOne)) fun s₂ ⟨k₂, U₂, lt₂, v₂⟩ => ?_)
  obtain hs₂ := hs₁.of_keepRegs k₂ (by intro h; exact (by decide : VG.AArch64.Reg.x0 ∉ VG.Proof.Mont.AArch64.clobAll) (VG.Proof.Mont.AArch64.mem_clobAll h))
  have e₂ {i : Nat} (hi : i < 45) (hw : i ∉ [W0, T4, TMP]) : sv c base s₂ i = sv c base s₁ i :=
    sv_unch U₂ h7 hn hi (apart_slW hw)
  obtain M₂ : ModOkA c.MP' size c.C.p s₂.mem base := modP_of hc (by
    change sv c base s₂ MP = _
    rw [e₂ (by decide) (by decide)]; exact M₁.val)
  obtain b₂ : fieldAt c base s₂ T4 =
      if fieldAt c base s T0 ^ (2 ^ (j - 1)) = 1 then 1 else fieldAt c base s T1 := by
    unfold fieldAt
    rw [v₂, v₁, e₁ (by decide) (by decide)]
  refine WP.mono (descentUpdate_ok hc hs₂ M₂ (by
    intro i hi
    obtain sub : ∀ i ∈ descentFields, i ∈ [ACC, T0, T1] ∨ i = T4 := by decide
    rcases sub i hi with h | rfl
    · have hi45 : i < 45 := (by decide : ∀ i ∈ [ACC, T0, T1], i < 45) i h
      obtain hn₁ : i ∉ [T3, TMP] := (by decide : ∀ i ∈ [ACC, T0, T1], i ∉ [T3, TMP]) i h
      obtain hn₂ : i ∉ [W0, T4, TMP] := (by decide : ∀ i ∈ [ACC, T0, T1], i ∉ [W0, T4, TMP]) i h
      rw [e₂ hi45 hn₂, e₁ hi45 hn₁]; exact hlt i h
    · exact lt₂)) fun s₃ V => ?_
  obtain U₁₂ := unch_same (slots_widen U₁ (by decide : ∀ i ∈ [T3, TMP], i ∈ roundSlots))
    (slots_widen U₂ (by decide : ∀ i ∈ [W0, T4, TMP], i ∈ roundSlots))
  obtain U₁₂₃ := unch_same U₁₂ (slots_widen V.unch (by decide : ∀ i ∈ descentWritten, i ∈ roundSlots))
  refine ⟨V.scr, ?_, U₁₂₃, V.lt, ?_⟩
  · exact (k₁.trans (k₂.mono (fun _ h => List.mem_cons_of_mem _ h))).trans
      (V.keep.mono (fun _ h => List.mem_cons_of_mem _ h))
  · have r₄ : fieldAt c base s₃ ACC = fieldAt c base s ACC * fieldAt c base s₂ T4 := by
      rw [fieldAt, V.r, e₂ (by decide) (by decide), e₁ (by decide) (by decide)]
    obtain t₄ : fieldAt c base s₃ T0 = fieldAt c base s T0 * (fieldAt c base s₂ T4 * fieldAt c base s₂ T4) := by
      rw [fieldAt, V.t, e₂ (by decide) (by decide), e₁ (by decide) (by decide)]
    obtain c₄ : fieldAt c base s₃ T1 = fieldAt c base s T1 * fieldAt c base s T1 := by
      rw [fieldAt, V.c, e₂ (by decide) (by decide), e₁ (by decide) (by decide)]
    conv_rhs => rw [show j = j - 1 + 1 by omega_using [hj], rootDescent]
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
  obtain hs₁ : Scr u base size := ⟨by rw [g]; exact hs.x0, by rw [wr]; exact hs.wr, hs.nowrap, hs.enc⟩
  have e (i : Nat) : sv c base u i = sv c base s i := by rw [sv, m]
  obtain M₁ : ModOkA c.MP' size c.C.p u.mem base := by rw [m]; exact hM
  refine WP.seq (WP.mono (VG.Proof.Ecdh.AArch64.WP.keepV hV
    (descentBody_ok hc hs₁ M₁ (by intro i hi; rw [e]; exact hlt i hi)
      (by rw [e]; exact hOne) hj hj' (by rw [g]; exact hcounter)))
    fun v ⟨R, hv⟩ => ?_)
  obtain counter : laneOf v .v27 0 = BitVec.ofNat 64 j := by
    change (v.v .v27).extractLsb' (64 * 0) 64 = _
    rw [hv]
    exact saved.trans hcounter
  refine WP.mono (descentCounter_ok hj (by omega_using [hj']) counter) fun t ⟨ct, K⟩ => ?_
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

end

end

/-! # P-224's machine candidate refines the shared root algorithm -/

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/AArch64/TonelliPowers.lean`, which only this module imported.
section

/-! # The two fixed powers that initialize P-224's descent -/

section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdh.AArch64 (W2)
open VG.Impl.EcKey.Compressed.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

 abbrev tonelliPowerWrites (c : Cfg) := rootWrites c ++ slW c [T5] ++ rootWrites c

 theorem tonelliPowers_ok {c : Cfg} (hc : BaseCfgOk c) (hcall : RootCall c)
    (hR : ChainOk (rootChain c ((rootQ c + 1) / 2)) ((rootQ c + 1) / 2))
    (hQ : ChainOk (rootChain c (rootQ c)) (rootQ c))
    {base : Addr} {s : State} (hs : Scr s base size)
    (hM : ModOkA c.MP' size c.C.p s.mem base) (hB : sv c base s W2 < c.C.p) :
    WP isa (tonelliPowers c) s fun t =>
      KeepRegs (powClob c.n) s t ∧ Unch base (tonelliPowerWrites c) s.mem t.mem ∧
      sv c base t ACC < c.C.p ∧ sv c base t T5 < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t ACC) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) ^ rootQ c ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t T5) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) ^ ((rootQ c + 1) / 2) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  change WP isa (.seq (rootPower c ((rootQ c + 1) / 2))
    (.seq (.block (copy c.n (c.sl T5) (c.sl ACC))) (rootPower c (rootQ c)))) s _
  refine WP.seq (WP.mono (rootPower_ok hc hcall hR hs hM hB)
    fun s₁ ⟨k₁, U₁, lt₁, v₁⟩ => ?_)
  obtain hs₁ := hs.of_keepRegs k₁ (x0_not_powClob _)
  have e₁ {i : Nat} (hi : i < 45) (hw : i ∉ rootSlots) :
      sv c base s₁ i = sv c base s i := sv_unch U₁ h7 hn hi (apart_rootWrites hc hi hw)
  refine WP.seq (WP.mono (copy_ok c.n hs₁ (sl_le c h7 (by decide)) (sl_le c h7 (by decide))
    (sl_mod8 c T5) (sl_mod8 c ACC)
    (by have := sl_apart c (i := T5) (j := ACC) (by decide); omega)) fun s₂ ⟨v₂, k₂, O₂⟩ => ?_)
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have e₂ {i : Nat} (hi : i < 45) (hw : i ≠ T5) : sv c base s₂ i = sv c base s₁ i :=
    O₂.wordsVal (sl_apart c hw) (by have := sl_le c h7 hi; omega)
  obtain M₂ : ModOkA c.MP' size c.C.p s₂.mem base := modP_of hc (by
    change sv c base s₂ MP = _
    rw [e₂ (by decide) (by decide), e₁ (by decide) (by decide)]; exact hM.val)
  refine WP.mono (rootPower_ok hc hcall hQ hs₂ M₂
    (by rw [e₂ (by decide) (by decide), e₁ (by decide) (by decide)]; exact hB))
    fun t ⟨kt, Ut, ltt, vt⟩ => ?_
  obtain et : sv c base t T5 = sv c base s₂ T5 :=
    sv_unch Ut h7 hn (by decide) (apart_rootWrites hc (by decide) (by decide))
  refine ⟨(k₁.trans (k₂.mono (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr; simp [powClob, clob]))).trans kt,
    (U₁.trans O₂.unch).trans Ut, ltt, ?_, ?_, ?_⟩
  · rw [et]
    change wordsVal s₂.mem base (c.sl T5) c.n < _
    rw [v₂]; exact lt₁
  · rw [vt, e₂ (by decide) (by decide), e₁ (by decide) (by decide)]
  · rw [et]
    change toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₂.mem base (c.sl T5) c.n) = _
    rw [v₂]; exact v₁

end VG.Proof.EcKey.Compressed.AArch64
end

end

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/AArch64/TonelliSetup.lean`, which only this module imported.
section

/-! # Initialize P-224's descent from its two computed powers -/

section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Impl.EcKey.Compressed.AArch64 (rootQ)
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

theorem tonelliSetup_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hr : sv c base s T5 < c.C.p) (ht : sv c base s ACC < c.C.p) :
    WP isa (.block (Impl.EcKey.Compressed.AArch64.tonelliSetup c)) s fun t =>
      KeepRegs [.x1, .x19] s t ∧ Unch base (slW c [T0, ACC, T1]) s.mem t.mem ∧
      (∀ i ∈ [ACC, T0, T1], sv c base t i < c.C.p) ∧
      t.gpr .x19 = BitVec.ofNat 64 95 ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t ACC) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s T5) ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t T0) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t T1) =
        Spec.Weierstrass.pow (Fin.ofNat c.C.p 11) (rootQ c) := by
  have h7 := hc.n10
  have h0 := hc.n0
  have hn := hs.nowrap
  obtain hT0 := sl_le c h7 (i := T0) (by decide)
  obtain hACC := sl_le c h7 (i := ACC) (by decide)
  obtain hT5 := sl_le c h7 (i := T5) (by decide)
  obtain hT1 := sl_le c h7 (i := T1) (by decide)
  rw [Impl.EcKey.Compressed.AArch64.tonelliSetup, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (copy_ok c.n hs hT0 hACC (sl_mod8 c T0) (sl_mod8 c ACC)
    (by have := sl_apart c (i := T0) (j := ACC) (by decide); omega)) fun s₁ ⟨v₁, k₁, O₁⟩ => ?_
  obtain hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok c.n hs₁ hACC hT5 (sl_mod8 c ACC) (sl_mod8 c T5)
    (by have := sl_apart c (i := ACC) (j := T5) (by decide); omega)) fun s₂ ⟨v₂, k₂, O₂⟩ => ?_
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  obtain r₂ : sv c base s₂ ACC = sv c base s T5 := by
    rw [sv, v₂, O₁.wordsVal (sl_apart c (i := T5) (j := T0) (by decide)) (by omega)]
  obtain t₂ : sv c base s₂ T0 = sv c base s ACC := by
    rw [sv, O₂.wordsVal (sl_apart c (i := T0) (j := ACC) (by decide)) (by omega), v₁]
  let z := Spec.Weierstrass.pow (Fin.ofNat c.C.p 11) (rootQ c)
  have zR : c.mont z.val < 2 ^ (64 * c.n) := Nat.lt_trans
    (Nat.mod_lt _ (by have := hc.p_ge; omega)) hc.p_lt
  rw [WP.block_append_iff]
  refine WP.mono (setConst_ok hs₂ hT1 (sl_mod8 c T1) zR) fun s₃ ⟨v₃, k₃, O₃⟩ => ?_
  obtain hs₃ := hs₂.of_keepRegs k₃ (by decide)
  refine WP.mono (setCounter_ok s₃ (j := 95) (by decide)) fun t ⟨v₄, k₄⟩ => ?_
  have e₃ {i : Nat} (hi : i < 45) (hw : i ≠ T1) : sv c base s₃ i = sv c base s₂ i :=
    O₃.wordsVal (sl_apart c hw) (by have := sl_le c h7 hi; omega)
  have e₄ (i : Nat) : sv c base t i = sv c base s₃ i := by rw [sv, k₄.mem]
  obtain r₄ : sv c base t ACC = sv c base s T5 := by
    rw [e₄, e₃ (by decide) (by decide), r₂]
  obtain t₄ : sv c base t T0 = sv c base s ACC := by
    rw [e₄, e₃ (by decide) (by decide), t₂]
  obtain c₄ : sv c base t T1 = c.mont z.val := by
    rw [e₄]; exact v₃
  refine ⟨(((k₁.trans k₂).trans k₃).mono (by sub_regs)).trans
      ((Keeps.regs k₄).mono (by sub_regs)), ?_, ?_, ?_, by rw [r₄], by rw [t₄], ?_⟩
  · rw [k₄.mem]
    exact unch_same (unch_same (slot_frame (by simp) (Nat.le_refl _) O₁)
      (slot_frame (by simp) (Nat.le_refl _) O₂)) (slot_frame (by simp) (Nat.le_refl _) O₃)
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · rw [r₄]; exact hr
    · rw [t₄]; exact ht
    · rw [c₄]; exact Nat.mod_lt _ (by have := hc.p_ge; omega)
  · exact v₄
  · rw [c₄, toM_cmont hc]
    exact Fin.ext (Nat.mod_eq_of_lt z.isLt)

end VG.Proof.EcKey.Compressed.AArch64
end

end

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/AArch64/DescentLoop.lean`, which only this module imported.
section

/-! # The P-224 machine loop computes the functional root descent -/

section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.EcKey.Compressed (rootDescent)

structure DescentInv (c : Cfg) (base : Addr) (count : Nat) (s₀ s : State) (j : Nat) : Prop where
  scr : Scr s base size
  mod : ModOkA c.MP' size c.C.p s.mem base
  one : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p
  counter : s.gpr .x19 = BitVec.ofNat 64 j
  keep : KeepRegs (powClob c.n) s₀ s
  unch : Unch base (slW c roundSlots) s₀.mem s.mem
  lt : ∀ i ∈ [ACC, T0, T1], sv c base s i < c.C.p
  val : rootDescent j (fieldAt c base s ACC) (fieldAt c base s T0) (fieldAt c base s T1) =
    rootDescent count (fieldAt c base s₀ ACC) (fieldAt c base s₀ T0) (fieldAt c base s₀ T1)

theorem descentLoop_ok {c : Cfg} (hc : BaseCfgOk c)
    (hV : ∀ i ∈ instrs (Impl.EcKey.Compressed.AArch64.descentBody c), vdstOf i ≠ some .v27) {base : Addr} {s : State} {count : Nat}
    (hs : Scr s base size) (hM : ModOkA c.MP' size c.C.p s.mem base)
    (hOne : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p)
    (hlt : ∀ i ∈ [ACC, T0, T1], sv c base s i < c.C.p)
    (hcount : 1 ≤ count) (hcount' : count < 2 ^ 31)
    (hword : s.gpr .x19 = BitVec.ofNat 64 count) :
    WP isa (.loop (Impl.EcKey.Compressed.AArch64.descentRound c) (.nonzero .x .x19)) s fun t =>
      KeepRegs (powClob c.n) s t ∧ Unch base (slW c roundSlots) s.mem t.mem ∧
      sv c base t ACC < c.C.p ∧ fieldAt c base t ACC =
        rootDescent count (fieldAt c base s ACC) (fieldAt c base s T0) (fieldAt c base s T1) := by
  have hn := hs.nowrap
  have h7 := hc.n10
  apply countLoop_ok (Inv := fun j t => DescentInv c base count s t j) (by omega) (n := count)
  · intro j t hj hjc I
    refine WP.mono (descentRound_ok hc hV I.scr I.mod I.lt I.one hj (by omega) I.counter)
      fun u R => ?_
    obtain M : ModOkA c.MP' size c.C.p u.mem base := modP_of hc (by
      rw [sv_unch R.unch h7 hn (by decide) (apart_slW (by decide : MP ∉ roundSlots))]
      exact I.mod.val)
    obtain one : sv c base u ONEP = 2 ^ (64 * c.n) % c.C.p := by
      rw [sv]
      rw [sv_unch R.unch h7 hn (by decide) (apart_slW (by decide : ONEP ∉ roundSlots))]
      exact I.one
    exact ⟨⟨R.scr, M, one, R.counter, I.keep.trans R.keep, unch_same I.unch R.unch,
      R.lt, R.descent.trans I.val⟩, R.counter⟩
  · intro t I
    exact ⟨I.keep, I.unch, I.lt _ (by simp), I.val⟩
  · exact hcount
  · exact ⟨hs, hM, hOne, hword, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, Unch.refl _ _ _, hlt, rfl⟩

end VG.Proof.EcKey.Compressed.AArch64
end

end

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Impl.Ecdh.AArch64 (W2)
open VG.Impl.EcKey.Compressed.AArch64 (rootQ rootChain)
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

 theorem candidateTonelli_correct {c : Cfg} (hc : BaseCfgOk c) (hcall : RootCall c) (hp : c.C.p % 4 ≠ 3)
    (hq : 0 < rootQ c)
    (hR : ChainOk (rootChain c ((rootQ c + 1) / 2)) ((rootQ c + 1) / 2))
    (hQ : ChainOk (rootChain c (rootQ c)) (rootQ c))
    (hV : ∀ i ∈ instrs (Impl.EcKey.Compressed.AArch64.descentBody c), vdstOf i ≠ some .v27) :
    CandidateCorrect c (fun a => Impl.EcKey.Compressed.rootTonelli a (rootQ c) 96 (Fin.ofNat c.C.p 11)) := by
  intro base s hs hM hB hO
  have h7 := hc.n10
  have hn := hs.nowrap
  simp only [Impl.EcKey.Compressed.AArch64.rootCandidate, hp, ↓reduceIte]
  change WP isa (.seq (Impl.EcKey.Compressed.AArch64.tonelliPowers c)
    (.seq (.block (Impl.EcKey.Compressed.AArch64.tonelliSetup c))
      (.loop (Impl.EcKey.Compressed.AArch64.descentRound c) (.nonzero .x .x19)))) s _
  refine WP.seq (WP.mono (tonelliPowers_ok hc hcall hR hQ hs hM hB)
    fun s₁ ⟨k₁, U₁, lt₁, ltR₁, t₁, r₁⟩ => ?_)
  obtain hs₁ := hs.of_keepRegs k₁ (x0_not_powClob _)
  refine WP.seq (WP.mono (tonelliSetup_ok hc hs₁ ltR₁ lt₁)
    fun s₂ ⟨k₂, U₂, lt₂, counter₂, r₂, t₂, c₂⟩ => ?_)
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  obtain U₁₂ : Unch base (candidateWrites c) s.mem s₂.mem := by
    apply unch_same (U₁.mono ?_) (U₂.mono ?_)
    · intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · rcases List.mem_append.mp hw with hw | hw
        · exact List.mem_append_left _ hw
        · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
          exact List.mem_append_right _ (List.mem_map_of_mem
            ((by decide : ∀ i ∈ [T5], i ∈ candidateSlots) i hi))
      · exact List.mem_append_left _ hw
    · intro w hw
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact List.mem_append_right _ (List.mem_map_of_mem
        ((by decide : ∀ i ∈ [T0, ACC, T1], i ∈ candidateSlots) i hi))
  obtain M₂ : ModOkA c.MP' size c.C.p s₂.mem base := modP_of hc (by
    rw [sv_unch U₁₂ h7 hn (by decide) (candidate_apart hc (by decide) (by decide))]
    exact hM.val)
  obtain one₂ : sv c base s₂ ONEP = 2 ^ (64 * c.n) % c.C.p := by
    rw [sv, sv_unch U₁₂ h7 hn (by decide) (candidate_apart hc (by decide) (by decide))]
    exact hO
  refine WP.mono (descentLoop_ok hc hV hs₂ M₂ one₂ lt₂ (by decide : 1 ≤ 95)
    (by decide : 95 < 2 ^ 31) counter₂) fun t ⟨kt, Ut, ltt, vt⟩ => ?_
  refine ⟨(k₁.trans (k₂.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp [powClob, clob]))).trans kt,
    unch_same U₁₂ (Ut.mono (by
      intro w hw
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact List.mem_append_right _ (List.mem_map_of_mem
        ((by decide : ∀ i ∈ roundSlots, i ∈ candidateSlots) i hi)))), ltt, ?_⟩
  change fieldAt c base t ACC = _
  rw [vt]
  change Impl.EcKey.Compressed.rootDescent 95
    (toM c.C.p (2 ^ (64 * c.n)) (sv c base s₂ ACC))
    (toM c.C.p (2 ^ (64 * c.n)) (sv c base s₂ T0))
    (toM c.C.p (2 ^ (64 * c.n)) (sv c base s₂ T1)) = _
  rw [r₂, t₂, c₂, r₁, t₁, rootTonelli_eq_descent _ _ _ _ hq]
  simp only [pow_eq_npow]

end VG.Proof.EcKey.Compressed.AArch64

end

end


/-! # Instantiate shared compression with P224's field configuration -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64.P224Decompress

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64
open VG.Proof.Ecdsa.AArch64.P224

 abbrev root (a : Spec.Weierstrass.Fe Spec.P224.curve) :=
  Impl.EcKey.Compressed.rootTonelli a ((Spec.P224.curve.p - 1) / 2 ^ 96) 96
    (Fin.ofNat Spec.P224.curve.p 11)

abbrev code : Prog isa := Impl.EcKey.Compressed.AArch64.decompress p224

materialize_shared baseline := code

 theorem ct : ConstantTime isa (decompressContract Spec.P224.curve root).pre
    (decompressContract Spec.P224.curve root).pub code := by
  apply VG.Taint.constantTime (A := LaneTaint.taint) (LaneTaint.ofRegs [.x0, .x1, .x2])
  · intro s₁ s₂ _ _ hp
    obtain ⟨hsp, hout, hpk, hws⟩ := hp
    refine ⟨⟨hsp, ?_⟩, by simp [LaneTaint.AgreeV, LaneTaint.ofRegs, LaneTaint.empty, LaneTaint.get]⟩
    intro r hr
    change r ∈ Taint.ofRegs [.x0, .x1, .x2] at hr
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hout
    · exact hpk
    · exact hws
  · taint_decide

 theorem sat : ∃ s, (Spec.EcKey.P224.inst.decompressPublicKeyContract abi 0).pre s := by
  have hlen : Spec.P224.curve.len = 28 := rfl
  sig_implies_sat [Spec.EcKey.P224.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
    Spec.EcKey.Instance.decompressPublicKeySig, hlen, Spec.EcKey.scratchWords,
    abi, argRegs, decompressSatState] [decompressSatState] using (decompressSatState 28)

 theorem chain_r : Proof.Weierstrass.AArch64.ChainOk
    (Impl.EcKey.Compressed.AArch64.rootChain p224
      ((Impl.EcKey.Compressed.AArch64.rootQ p224 + 1) / 2))
    ((Impl.EcKey.Compressed.AArch64.rootQ p224 + 1) / 2) := by
  apply Proof.Weierstrass.AArch64.ChainOk.of_check
  decide +kernel

 theorem chain_q : Proof.Weierstrass.AArch64.ChainOk
    (Impl.EcKey.Compressed.AArch64.rootChain p224 (Impl.EcKey.Compressed.AArch64.rootQ p224))
    (Impl.EcKey.Compressed.AArch64.rootQ p224) := by
  apply Proof.Weierstrass.AArch64.ChainOk.of_check
  decide +kernel

 theorem body_no_v27 : ∀ i ∈ instrs (Impl.EcKey.Compressed.AArch64.descentBody p224),
    vdstOf i ≠ some .v27 := by
  obtain h : (Impl.EcKey.Compressed.AArch64.descentBody p224).allInstrs
      (fun i => (vdstOf i).isNone) = true := by lit_decide
  intro i hi he
  obtain h' := List.all_eq_true.mp ((Code.allInstrs_eq _ _) ▸ h) i hi
  rw [he] at h'
  cases h'

 theorem verified (hL : Proof.Weierstrass.Law Spec.P224.curve)
    (hI : Proof.Weierstrass.AArch64.InvSounds) :
    Verified target code (Spec.EcKey.P224.inst.decompressPublicKeyContract abi 0) := by
  obtain hc := (p224_ok hI).toBaseCfgOk
  exact Verified.of_correct (decompress_correct p224 hc _
    (candidateTonelli_correct hc (rootCall_of hc (by decide)) (by decide +kernel) (by decide +kernel) chain_r chain_q body_no_v27)
    (by lit_decide) (by lit_decide) (by lit_decide)) ct
    (decompress_implies Spec.EcKey.P224.inst _
      (Proof.P224.rootFacts hL) sat)

end VG.Proof.EcKey.Compressed.AArch64.P224Decompress
