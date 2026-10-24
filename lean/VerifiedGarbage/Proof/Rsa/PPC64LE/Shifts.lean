module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.Div
public import VerifiedGarbage.Proof.Rsa.PPC64LE.Loops
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontStep
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The shifts of the RSA key operations on PPC64LE

In place, over `n` digits at `dO` (the pointer in `r5`, the count in `r8`):

* `halfLoop_ok` (`countLoop .r8 halfBody`): each digit takes its upper 31
  bits and the low bit of the next, so that the `n` digits become the `n + 1`
  digits from `dO` halved: `2 [o]' + d₀ mod 2 = [o] + 2^(32 n) (dₙ mod 2)`.
* `shlLoop_ok` (`countLoop .r8 Div.shlBody`): `[o]' + 2^(32 n) c' = 2 [o] + c`,
  the carry `c` in and `c'` out in `r9`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Loops

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Impl.Rsa.PPC64LE VG.Impl.Rsa.PPC64LE.Keys

/-- A digit of the halving, on bit vectors. -/
theorem half_arith (x y : BitVec 32) :
    (((x.setWidth 64 >>> 1) ||| (y.setWidth 64 <<< 31)).setWidth 32).toNat =
      x.toNat / 2 + 2 ^ 31 * (y.toNat % 2) := by
  have hx := x.isLt
  have hy := y.isLt
  rw [BitVec.toNat_setWidth, BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
    toNat_ext32, toNat_ext32, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show y.toNat * 2 ^ 31 < 2 ^ 64 by omega_arith), Nat.mul_comm,
    Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt (show x.toNat / 2 ^ 1 < 2 ^ 31 by omega_arith)]
  omega_arith

/-- A digit of the left shift, on bit vectors: the low 32 bits and the carry. -/
theorem shl_arith (x : BitVec 32) (c : BitVec 64) (hc : c.toNat ≤ 1) :
    (((x.setWidth 64 <<< 1) ||| c).setWidth 32).toNat + 2 ^ 32 * (x.setWidth 64 >>> 31).toNat =
        2 * x.toNat + c.toNat ∧ (x.setWidth 64 >>> 31).toNat ≤ 1 := by
  have hx := x.isLt
  rw [BitVec.toNat_setWidth, BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
    toNat_ext32, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show x.toNat * 2 ^ 1 < 2 ^ 64 by omega_arith), Nat.mul_comm,
    ← Nat.two_pow_add_eq_or_of_lt (show c.toNat < 2 ^ 1 by omega_arith)]
  omega_arith

/-- The halving of the `n + 1` digits at `dO` into the `n` at `dO`. -/
theorem halfLoop_ok {s : State} {B : Addr} {Z dO n : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .r5 = off B dO) (h8 : s.gpr .r8 = BitVec.ofNat 64 n) (hn : 1 ≤ n) (hn' : n < 2 ^ 32)
    (hO : dO + 4 * (n + 1) ≤ Z) :
    WP isa (countLoop .r8 halfBody) s fun t =>
      2 * val32 t.mem B dO n + w32 s.mem B dO % 2 =
        val32 s.mem B dO n + 2 ^ (32 * n) * (w32 s.mem B (dO + 4 * n) % 2) ∧
      Outside B dO (4 * n) s.mem t.mem ∧ Keep loopRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r5 = off B (dO + 4 * i) ∧ Outside B dO (4 * i) s.mem t.mem ∧
      2 * val32 t.mem B dO i + w32 s.mem B dO % 2 =
        val32 s.mem B dO i + 2 ^ (32 * i) * (w32 s.mem B (dO + 4 * i) % 2) ∧
      Keep loopRegs s t
  refine WP.mono (wp_countdown (body := .block (halfBody ++ ([.subi .r8 .r8 1] : List Instr)))
    (cnt := .r8) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j5, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h5]; rfl, Outside.refl _ _ _ _, by simp [val32], Keep.refl _ _⟩ h8)
    fun t ⟨_, jout, jeq, jk⟩ => ⟨jeq, jout, jk⟩
  have hst : WP isa (.block (halfBody ++ ([.subi .r8 .r8 1] : List Instr))) t fun t' =>
      (t'.gpr .r5 = off B (dO + 4 * i + 4) ∧ t'.gpr .r8 = t.gpr .r8 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 4 * i))
          ((((t.mem.readW (off B (dO + 4 * i)) 32).setWidth 64 >>> 1) |||
            ((t.mem.readW (off B (dO + 4 * i + 4)) 32).setWidth 64 <<< 31)).setWidth 32)) ∧
      Keep loopRegs t t' := by
    refine WP.keep _ ?_ (by decide)
    prun [halfBody, j5, (hs.congr jk.wr).ld (show dO + 4 * i + 4 ≤ Z by omega_arith),
      (hs.congr jk.wr).ld (show dO + 4 * i + 4 + 4 ≤ Z by omega_arith),
      (hs.congr jk.wr).st (show dO + 4 * i + 4 ≤ Z by omega_arith)]
  refine WP.mono hst fun t' ⟨⟨l5, l8, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, jk.trans' lk⟩, l8⟩
  · rw [l5, show dO + 4 * i + 4 = dO + 4 * (i + 1) by omega_arith]
  · rw [lm]
    exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW32_outside _ B (d := dO + 4 * i) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  · have w0 : w32 t.mem B (dO + 4 * i) = w32 s.mem B (dO + 4 * i) :=
      jout.w32 (by omega_arith) (by omega_arith)
    have w1 : w32 t.mem B (dO + 4 * i + 4) = w32 s.mem B (dO + 4 * (i + 1)) := by
      rw [show dO + 4 * (i + 1) = dO + 4 * i + 4 by omega_arith]
      exact jout.w32 (by omega_arith) (by omega_arith)
    have k := half_arith (t.mem.readW (off B (dO + 4 * i)) 32) (t.mem.readW (off B (dO + 4 * i + 4)) 32)
    rw [lm, val32_write_top _ _ _ _ _ (by omega_arith), val32_succ s.mem B dO i, ← pow32_mul i, k]
    simp only [w32] at w0 w1 jeq ⊢
    rw [w0, w1]
    have hX := Nat.mod_add_div (s.mem.readW (off B (dO + 4 * i)) 32).toNat 2
    generalize 2 ^ (32 * i) = P at *
    grind

/-- The left shift of the `n` digits at `dO`, the carry in and out in `r9`. -/
theorem shlLoop_ok {s : State} {B : Addr} {Z dO n : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .r5 = off B dO) (h8 : s.gpr .r8 = BitVec.ofNat 64 n) (h9 : (s.gpr .r9).toNat ≤ 1)
    (hn : 1 ≤ n) (hn' : n < 2 ^ 32) (hO : dO + 4 * n ≤ Z) :
    WP isa (countLoop .r8 Div.shlBody) s fun t =>
      (t.gpr .r9).toNat ≤ 1 ∧
      val32 t.mem B dO n + 2 ^ (32 * n) * (t.gpr .r9).toNat = 2 * val32 s.mem B dO n + (s.gpr .r9).toNat ∧
      Outside B dO (4 * n) s.mem t.mem ∧ Keep loopRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r5 = off B (dO + 4 * i) ∧ (t.gpr .r9).toNat ≤ 1 ∧ Outside B dO (4 * i) s.mem t.mem ∧
      val32 t.mem B dO i + 2 ^ (32 * i) * (t.gpr .r9).toNat = 2 * val32 s.mem B dO i + (s.gpr .r9).toNat ∧
      Keep loopRegs s t
  refine WP.mono (wp_countdown (body := .block (Div.shlBody ++ ([.subi .r8 .r8 1] : List Instr)))
    (cnt := .r8) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j5, j9, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h5]; rfl, h9, Outside.refl _ _ _ _, by simp [val32], Keep.refl _ _⟩ h8)
    fun t ⟨_, j9, jout, jeq, jk⟩ => ⟨j9, jeq, jout, jk⟩
  have hst : WP isa (.block (Div.shlBody ++ ([.subi .r8 .r8 1] : List Instr))) t fun t' =>
      (t'.gpr .r5 = off B (dO + 4 * i + 4) ∧ t'.gpr .r8 = t.gpr .r8 - BitVec.ofNat 64 1 ∧
        t'.gpr .r9 = (t.mem.readW (off B (dO + 4 * i)) 32).setWidth 64 >>> 31 ∧
        t'.mem = t.mem.writeW (off B (dO + 4 * i))
          ((((t.mem.readW (off B (dO + 4 * i)) 32).setWidth 64 <<< 1) ||| t.gpr .r9).setWidth 32)) ∧
      Keep loopRegs t t' := by
    refine WP.keep _ ?_ (by decide)
    prun [Div.shlBody, j5, (hs.congr jk.wr).ld (show dO + 4 * i + 4 ≤ Z by omega_arith),
      (hs.congr jk.wr).st (show dO + 4 * i + 4 ≤ Z by omega_arith)]
  refine WP.mono hst fun t' ⟨⟨l5, l8, l9, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, jk.trans' lk⟩, l8⟩
  · rw [l5, show dO + 4 * i + 4 = dO + 4 * (i + 1) by omega_arith]
  · rw [l9]; exact (shl_arith _ _ j9).2
  · rw [lm]
    exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW32_outside _ B (d := dO + 4 * i) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  · have w0 : w32 t.mem B (dO + 4 * i) = w32 s.mem B (dO + 4 * i) :=
      jout.w32 (by omega_arith) (by omega_arith)
    have k := (shl_arith (t.mem.readW (off B (dO + 4 * i)) 32) _ j9).1
    rw [lm, l9, val32_write_top _ _ _ _ _ (by omega_arith), val32_succ s.mem B dO i, ← pow32_mul i]
    simp only [w32] at w0 ⊢
    rw [w0] at k
    generalize 2 ^ (32 * i) = P at *
    grind

end VG.Proof.Rsa.PPC64LE.Loops
