module

public import VerifiedGarbage.Impl.EcKey.Compressed.X86_64.Decompress
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Layout
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Fixed
import VerifiedGarbage.Proof.Weierstrass.X86_64.Unch
import VerifiedGarbage.Proof.Ecdsa.X86_64.SlotOps
import VerifiedGarbage.Proof.Ecdsa.X86_64.Middle
import VerifiedGarbage.Proof.Weierstrass.RootPowers
import VerifiedGarbage.Proof.Weierstrass.X86_64.Pow
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop

/-! # Repeated squaring for the P-224 root descent

The backwards invariant `current^(2^remaining) = original^(2^count)`
avoids any assumption about the input being a square or nonzero.
-/

@[expose] public section

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
