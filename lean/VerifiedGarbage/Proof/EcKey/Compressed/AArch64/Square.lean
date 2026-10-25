module

public import VerifiedGarbage.Impl.EcKey.Compressed.AArch64.Decompress
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Fixed
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
import VerifiedGarbage.Proof.Ecdsa.AArch64.Middle
import VerifiedGarbage.Proof.Weierstrass.AArch64.Unch
import VerifiedGarbage.Proof.Weierstrass.RootPowers
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Weierstrass.AArch64.Fprog
import VerifiedGarbage.Proof.Framework.Block

/-! # Repeated squaring for the P-224 descent -/

@[expose] public section

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
