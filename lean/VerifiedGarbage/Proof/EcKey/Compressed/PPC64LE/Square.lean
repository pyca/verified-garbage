module

public import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.Counter
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Layout
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.SlotOps
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Pow
public import VerifiedGarbage.Impl.EcKey.Compressed.PPC64LE.Decompress
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Keep
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# SEC 1 point decompression on PPC64LE: repeated squarings

`squarePower_ok`: `squarePower` squares `T3` as many times as `r31`'s low
word `i`, which it takes to zero: `T3 = T3^(2^i)`.
-/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Ecdsa.PPC64LE VG.Spec.Weierstrass

variable {c : Cfg}

/-- The squarings' invariant, with `k` squarings left of `i`. -/
structure SqInv (c : Cfg) (base : Addr) (s₀ : State) (j i : Nat) (s : State) (k : Nat) : Prop where
  ws : WsReg s base
  r31 : s.gpr .r31 = ctr j k
  le : k ≤ i
  rk : Rk powClob s₀ s
  unch : Unch base (callW c T3) s₀.mem s.mem
  lt : sv c base s T3 < c.C.p
  val : toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) =
    toM c.C.p (2 ^ (64 * c.n)) (sv c base s₀ T3) ^ (2 ^ (i - k))

theorem sq_pow {α : Type _} [Lean.Grind.CommRing α] (x : α) (m : Nat) :
    x ^ (2 ^ m) * x ^ (2 ^ m) = x ^ (2 ^ (m + 1)) := by
  rw [← Lean.Grind.Semiring.pow_add, Nat.pow_succ, Nat.mul_two]

/-- `T3 = T3^(2^i)`, for the low word `i` of `r31`, which ends zero. -/
theorem squarePower_ok (hc : CfgOk c) {base : Addr} {s : State} (hw : WsReg s base) {j i : Nat}
    (hi : i < 2 ^ 32) (h31 : s.gpr .r31 = ctr j i) (hlt : sv c base s T3 < c.C.p) :
    WP isa (Impl.EcKey.Compressed.PPC64LE.squarePower c) s fun s' =>
      WsReg s' base ∧ s'.gpr .r31 = ctr j 0 ∧ Rk powClob s s' ∧ Unch base (callW c T3) s.mem s'.mem ∧
      sv c base s' T3 < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' T3) = toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) ^ (2 ^ i) := by
  have h7 := hc.n10
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  refine WP.ite (decide (i = 0)) (eval_lo_zero hi h31) (fun h => ?_) (fun h => ?_)
  · have hi0 : i = 0 := of_decide_eq_true h
    subst hi0
    exact WP.block_nil ⟨hw, h31, Rk.refl _ _, Unch.refl _ _ _, hlt, by
      rw [Nat.pow_zero, Lean.Grind.Semiring.pow_one]⟩
  · have hi0 : i ≠ 0 := of_decide_eq_false h
    refine loopBy_ok (Inv := fun k s' => SqInv c base s j i s' k) (n := i)
      (fun k s' I => eval_lo_nonzero (by have := I.le; omega) I.r31) (fun k t hk hki I => ?_)
      (fun t I => ⟨I.ws, I.r31, I.rk, I.unch, I.lt, by rw [I.val, Nat.sub_zero]⟩) (by omega)
      ⟨hw, h31, Nat.le_refl _, Rk.refl _ _, Unch.refl _ _ _, hlt, by
        rw [Nat.sub_self, Nat.pow_zero, Lean.Grind.Semiring.pow_one]⟩
    refine WP.seq (WP.mono (slMul_ok hc.fp hc.fpk hc.fpm h7 I.ws (o := T3) (a := T3) (b := T3) (by decide)
      (by decide) (by decide) I.lt) fun t₁ ⟨k₁, U₁, lt₁, e₁⟩ => ?_)
    have r31₁ : t₁.gpr .r31 = ctr j k := by rw [k₁.gpr _ (by decide), I.r31]
    refine wp_step (exec_subi (by decide) (by decide)) (WP.block_nil ⟨I.ws.of_rk k₁ |>.of_kp
      (Kp.write _ _ (rs := [.r31]) (by decide)), ?_, by omega, ?_, ?_, lt₁, ?_⟩)
    · simp only [write_gpr, ite_true, r31₁]; exact ctr_dec hk (by omega)
    · exact (I.rk.trans (k₁.mono (by decide))).trans ((Kp.write _ _ (rs := [.r31]) (by decide)).rk)
    · simp only [write_mem]
      exact (I.unch.trans U₁).mono fun w hw' => (List.mem_append.mp hw').elim id id
    · show toM c.C.p (2 ^ (64 * c.n)) (sv c base t₁ T3) = _
      rw [toM_mul hpR e₁, I.val, sq_pow, show i - k + 1 = i - (k - 1) by omega]

end VG.Proof.EcKey.Compressed.PPC64LE
