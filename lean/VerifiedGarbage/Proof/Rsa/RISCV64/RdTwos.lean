module

public import VerifiedGarbage.Proof.Rsa.RISCV64.RdOps
public import VerifiedGarbage.Proof.Rsa.RecoverDet
public import VerifiedGarbage.Proof.Rsa.RecoverDetModel
public import VerifiedGarbage.Proof.Rsa.KeyMath
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Rsa.InverseArithmetic
import VerifiedGarbage.Proof.Rsa.RISCV64.KeyInv
import VerifiedGarbage.Proof.Rsa.RISCV64.KeyDiv
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The halvings and the GCD of `vg_rsa_recover_primes_det` on RISC-V

* `twosInit_ok`, `twosBody_ok`, `twos_ok`: from `n` (narrow, `aN`) and `x = d e - 1`
  (wide, `wX`), `64 w` steps of `RecoverDet.twoStep` with `b = 64 W` on
  `(u, x, 2^k x)` (`twosSt`: narrow `aU`, narrow `aX2`, wide `wX3`), from
  `(n - 1, x mod 2^(64 w), x)`;
* `gcdStep_ok`, `gcd_ok`: the binary GCD on `([gU], [gV])` is `uvStep`, the
  `(u, v)` part of `KeyMath.invStep` (`invIter_uv`), so from `(x, u)`, `u`
  odd, it ends at `(0, gcd(x, u))` (`uv_done`), copied into the low half of
  the wide `wG`.
-/

@[expose] public section

namespace VG.Proof.Rsa

/-- `KeyMath.invStep`'s `(u, v)` part. -/
def uvStep (s : Nat × Nat) : Nat × Nat :=
  if s.1 % 2 = 1 then (if s.1 < s.2 then ((s.2 - s.1) / 2, s.1) else ((s.1 - s.2) / 2, s.2))
  else (s.1 / 2, s.2)

theorem invStep_uv (m : Nat) (st : Nat × Nat × Nat × Nat) :
    ((invStep m st).1, (invStep m st).2.1) = uvStep (st.1, st.2.1) := by
  obtain ⟨u, v, x₁, x₂⟩ := st
  simp only [invStep, uvStep]
  split <;> (try split) <;> rfl

/-- The `(u, v)` part of `invIter` ignores the cofactors. -/
theorem invIter_uv (m : Nat) (st : Nat × Nat × Nat × Nat) : ∀ k,
    ((invIter m k st).1, (invIter m k st).2.1) = uvStep^[k] (st.1, st.2.1)
  | 0 => rfl
  | k + 1 => by
    rw [Function.iterate_succ_apply', ← invIter_uv m st k]
    exact invStep_uv m _

/-- From `(a, m)` with `m` odd and `a m < 2^K`: `(0, gcd a m)`. -/
theorem uv_done {a m K : Nat} (hm : m % 2 = 1) (ha : a * m < 2 ^ K) :
    uvStep^[K] (a, m) = (0, Nat.gcd a m) := by
  have D := invIter_done (a := a) (K := K) hm ha
  dsimp only at D
  rw [← invIter_uv m (a, m, 1 % m, 0) K, D.1, D.2.1]

end VG.Proof.Rsa

namespace VG.Proof.Rsa.RISCV64.Keys

open VG VG.RISCV64 VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Rsa.RISCV64.Keys (seqs sub3 sel bitOf stBorrow andS half copy sOdd sB sC)
open VG.Impl.Rsa.RISCV64.RecoverDet (gcdStep gcd next gU gV gT1 gT2 gT3 aU aX2 wG cmpBody gcdBody)
open VG.Impl.Bignum.RISCV64 (countLoop)
open VG.Impl.Rsa.RISCV64.Keys (ptr mov)
open VG.Proof.Rsa.RISCV64.Loops (loopRegs Ahead out_step half64_arith)
open VG.Proof.Rsa (uvStep uv_done invU_arith borrow_iff)

/-- Index side conditions. -/
macro "rdidx" : tactic => `(tactic| ((try simp only [gU, gV, gT1, gT2, gT3, aU, aX2, wG, sOdd, sB, sC,
  hdr_eq, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, true_and,
  ne_eq]) <;> omega_arith))

/-! ## The GCD -/

/-- The registers of the GCD's steps. -/
abbrev gcdRegs : List Reg := .a5 :: opRegs

/-- The registers the GCD's pass changes. -/
abbrev gcdLRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6]

/-- The borrow of `[t1] - [t2]` over `n` words (`countLoop .t3 cmpBody`), from the borrow in `t4`. -/
theorem cmpLoop_ok {s : State} {B : Addr} {Z dA dB n : Nat} (hs : Scr s B Z)
    (h1 : s.gpr .t1 = off B dA) (h2 : s.gpr .t2 = off B dB) (h3 : s.gpr .t3 = BitVec.ofNat 64 n)
    (h4 : (s.gpr .t4).toNat ≤ 1) (hn : 1 ≤ n) (hn' : n < 2 ^ 32) (hA8 : dA % 8 = 0) (hB8 : dB % 8 = 0)
    (hA : dA + 8 * n ≤ Z) (hB : dB + 8 * n ≤ Z) :
    WP isa (countLoop .t3 cmpBody) s fun t =>
      (t.gpr .t4).toNat ≤ 1 ∧ t.mem = s.mem ∧
      (∃ x < 2 ^ (64 * n), x + wordsVal s.mem B dB n + (s.gpr .t4).toNat =
        wordsVal s.mem B dA n + 2 ^ (64 * n) * (t.gpr .t4).toNat) ∧ Keep loopRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t1 = off B (dA + 8 * i) ∧ t.gpr .t2 = off B (dB + 8 * i) ∧ (t.gpr .t4).toNat ≤ 1 ∧
      t.mem = s.mem ∧
      (∃ x < 2 ^ (64 * i), x + wordsVal s.mem B dB i + (s.gpr .t4).toNat =
        wordsVal s.mem B dA i + 2 ^ (64 * i) * (t.gpr .t4).toNat) ∧
      Keep loopRegs s t
  refine WP.mono (wp_countdown (body := .block (cmpBody ++ ([.addi .t3 .t3 (-1)] : List Instr)))
    (cnt := .t3) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j1, j2, j4, jm, ⟨x, hx, jeq⟩, jk⟩ hc => ?_)
    ⟨by rw [h1]; rfl, by rw [h2]; rfl, h4, rfl, ⟨0, by simp, by simp [wordsVal]⟩, Keep.refl _ _⟩ h3)
    fun t ⟨_, _, j4, jm, jx, jk⟩ => ⟨j4, jm, jx, jk⟩
  have hs' := hs.congr jk.2.2
  have hst : WP isa (.block (cmpBody ++ ([.addi .t3 .t3 (-1)] : List Instr))) t fun t' =>
      (t'.gpr .t1 = off B (dA + 8 * i + 8) ∧ t'.gpr .t2 = off B (dB + 8 * i + 8) ∧
        t'.gpr .t3 = t.gpr .t3 - BitVec.ofNat 64 1 ∧ t'.mem = t.mem ∧
        t'.gpr .t4 = ((if word t.mem B (dA + 8 * i) < word t.mem B (dB + 8 * i) then (1 : BitVec 64) else 0) |||
          (if word t.mem B (dA + 8 * i) - word t.mem B (dB + 8 * i) < t.gpr .t4 then 1 else 0))) ∧
      Keep loopRegs t t' := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [cmpBody, j1, j2, hs'.ld (show dA + 8 * i + 8 ≤ Z by omega_arith),
      hs'.ld (show dB + 8 * i + 8 ≤ Z by omega_arith),
      hs'.al8 (show dA + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith),
      hs'.al8 (show dB + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith)]
  refine WP.mono hst fun t' ⟨⟨l1, l2, l3, lm, lb⟩, lk⟩ =>
    ⟨⟨?_, ?_, ?_, by rw [lm, jm], ?_, Keep.trans' jk lk⟩, l3⟩
  · rw [l1, show dA + 8 * i + 8 = dA + 8 * (i + 1) by omega_arith]
  · rw [l2, show dB + 8 * i + 8 = dB + 8 * (i + 1) by omega_arith]
  · rw [lb]; exact (sub64_arith _ _ _ j4).2
  · have k := (sub64_arith (word t.mem B (dA + 8 * i)) (word t.mem B (dB + 8 * i)) (t.gpr .t4) j4).1
    rw [← lb, jm] at k
    refine ⟨x + 2 ^ (64 * i) * (word s.mem B (dA + 8 * i) - word s.mem B (dB + 8 * i) - t.gpr .t4).toNat,
      ?_, ?_⟩
    · have := (word s.mem B (dA + 8 * i) - word s.mem B (dB + 8 * i) - t.gpr .t4).isLt
      rw [Nat.mul_succ, Nat.pow_add]
      have : 2 ^ (64 * i) * ((word s.mem B (dA + 8 * i) - word s.mem B (dB + 8 * i) - t.gpr .t4).toNat + 1) ≤
          2 ^ (64 * i) * 2 ^ 64 := Nat.mul_le_mul_left _ this
      rw [Nat.mul_add, Nat.mul_one] at this
      omega
    · rw [wordsVal_succ_top s.mem B dB i, wordsVal_succ_top s.mem B dA i, Nat.mul_succ, Nat.pow_add]
      have e : 2 ^ (64 * i) * (word s.mem B (dA + 8 * i) - word s.mem B (dB + 8 * i) - t.gpr .t4).toNat +
          2 ^ (64 * i) * (word s.mem B (dB + 8 * i)).toNat + 2 ^ (64 * i) * (t.gpr .t4).toNat =
          2 ^ (64 * i) * (word s.mem B (dA + 8 * i)).toNat + 2 ^ (64 * i) * 2 ^ 64 * (t'.gpr .t4).toNat := by
        rw [← Nat.mul_add, ← Nat.mul_add, Nat.mul_assoc, ← Nat.mul_add, k]
      grind

/-- A word of `x ∧ mask`. -/
theorem and_mask64 (y : BitVec 64) (b : Bool) :
    (y &&& (if b then BitVec.allOnes 64 else 0)).toNat = if b then y.toNat else 0 := by
  cases b
  · show (y &&& 0#64).toNat = 0; rw [BitVec.and_zero]; rfl
  · show (y &&& BitVec.allOnes 64).toNat = y.toNat; rw [BitVec.and_allOnes]

/-- A word of a masked selection, `x ⊕ ((h ⊕ x) ∧ mask)`. -/
theorem xsel64 (x h : BitVec 64) (b : Bool) :
    x ^^^ ((h ^^^ x) &&& (if b then BitVec.allOnes 64 else 0)) = if b then h else x := by
  rw [BitVec.xor_comm]; exact select64_arith x h b

/-- Memory that agrees outside two ranges. -/
def Out2 (B : Addr) (a n b k : Nat) (m m' : Mem) : Prop :=
  ∀ x, (ofs B x < a ∨ a + n ≤ ofs B x) → (ofs B x < b ∨ b + k ≤ ofs B x) → m' x = m x

theorem Out2.word {m m' : Mem} {B : Addr} {a n b k d : Nat} (h : Out2 B a n b k m m')
    (h1 : d + 8 ≤ a ∨ a + n ≤ d) (h2 : d + 8 ≤ b ∨ b + k ≤ d) (hd : d + 8 ≤ 2 ^ 64) :
    word m' B d = word m B d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [ofs_off B (by omega_arith)]; omega_arith)
    (by rw [ofs_off B (by omega_arith)]; omega_arith)).symm).symm

theorem Out2.wordsVal {m m' : Mem} {B : Addr} {a n b k : Nat} (h : Out2 B a n b k m m') :
    ∀ {d j : Nat}, (d + 8 * j ≤ a ∨ a + n ≤ d) → (d + 8 * j ≤ b ∨ b + k ≤ d) → d + 8 * j ≤ 2 ^ 64 →
      VG.Proof.Mont.wordsVal m' B d j = VG.Proof.Mont.wordsVal m B d j
  | _, 0, _, _, _ => rfl
  | d, j + 1, h1, h2, h3 => by
    simp only [VG.Proof.Mont.wordsVal]
    rw [h.word (by omega_arith) (by omega_arith) (by omega_arith),
      h.wordsVal (d := d + 8) (j := j) (by omega_arith) (by omega_arith) (by omega_arith)]

/-- `x ⊕ ((x ⊕ y) ∧ mask)`. -/
theorem xsel64' (x y : BitVec 64) (b : Bool) :
    x ^^^ ((x ^^^ y) &&& (if b then BitVec.allOnes 64 else 0)) = if b then y else x := by
  rw [BitVec.xor_comm x y]; exact xsel64 x y b

/-- The step's pass over `n` words (`countLoop .t3 gcdBody`), `u` at `t0` and `v` at `t1`, the
masks of `c` and `odd` in `a4` and `a5`: `[v] := c ? [u] : [v]` and
`[u] := (c ? [v] : [u]) - (odd ? [v'] : 0)`, the borrow in and out in `t4`. -/
theorem gcdLoop_ok {s : State} {B : Addr} {Z dU dV n : Nat} (hs : Scr s B Z) {c o : Bool}
    (h0 : s.gpr .t0 = off B dU) (h1 : s.gpr .t1 = off B dV) (h3 : s.gpr .t3 = BitVec.ofNat 64 n)
    (h4 : (s.gpr .t4).toNat ≤ 1) (ha4 : s.gpr .a4 = if c then BitVec.allOnes 64 else 0)
    (ha5 : s.gpr .a5 = if o then BitVec.allOnes 64 else 0) (hn : 1 ≤ n) (hn' : n < 2 ^ 32)
    (hU8 : dU % 8 = 0) (hV8 : dV % 8 = 0) (hU : dU + 8 * n ≤ Z) (hV : dV + 8 * n ≤ Z)
    (dUV : dU + 8 * n ≤ dV ∨ dV + 8 * n ≤ dU) :
    WP isa (countLoop .t3 gcdBody) s fun t =>
      (t.gpr .t4).toNat ≤ 1 ∧
      wordsVal t.mem B dV n = (if c then wordsVal s.mem B dU n else wordsVal s.mem B dV n) ∧
      wordsVal t.mem B dU n + (if o then wordsVal t.mem B dV n else 0) + (s.gpr .t4).toNat =
        (if c then wordsVal s.mem B dV n else wordsVal s.mem B dU n) + 2 ^ (64 * n) * (t.gpr .t4).toNat ∧
      Out2 B dU (8 * n) dV (8 * n) s.mem t.mem ∧ Keep gcdLRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t0 = off B (dU + 8 * i) ∧ t.gpr .t1 = off B (dV + 8 * i) ∧ (t.gpr .t4).toNat ≤ 1 ∧
      Out2 B dU (8 * i) dV (8 * i) s.mem t.mem ∧
      wordsVal t.mem B dV i = (if c then wordsVal s.mem B dU i else wordsVal s.mem B dV i) ∧
      wordsVal t.mem B dU i + (if o then wordsVal t.mem B dV i else 0) + (s.gpr .t4).toNat =
        (if c then wordsVal s.mem B dV i else wordsVal s.mem B dU i) + 2 ^ (64 * i) * (t.gpr .t4).toNat ∧
      Keep gcdLRegs s t
  refine WP.mono (wp_countdown (body := .block (gcdBody ++ ([.addi .t3 .t3 (-1)] : List Instr)))
    (cnt := .t3) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j0, j1, j4, jout, jv, ju, jk⟩ hc => ?_)
    ⟨by rw [h0]; rfl, by rw [h1]; rfl, h4, fun _ _ _ => rfl, by cases c <;> simp [wordsVal],
      by cases c <;> cases o <;> simp [wordsVal], Keep.refl _ _⟩ h3)
    fun t ⟨_, _, j4, jout, jv, ju, jk⟩ => ⟨j4, jv, ju, jout, jk⟩
  have hs' := hs.congr jk.2.2
  have ja4 : t.gpr .a4 = if c then BitVec.allOnes 64 else 0 := (jk.gpr (r := .a4) (by decide)).trans ha4
  have ja5 : t.gpr .a5 = if o then BitVec.allOnes 64 else 0 := (jk.gpr (r := .a5) (by decide)).trans ha5
  generalize hu : word t.mem B (dU + 8 * i) = u
  generalize hv : word t.mem B (dV + 8 * i) = v
  have hst : WP isa (.block (gcdBody ++ ([.addi .t3 .t3 (-1)] : List Instr))) t fun t' =>
      (t'.gpr .t0 = off B (dU + 8 * i + 8) ∧ t'.gpr .t1 = off B (dV + 8 * i + 8) ∧
        t'.gpr .t3 = t.gpr .t3 - BitVec.ofNat 64 1 ∧
        t'.mem = (t.mem.writeW (off B (dV + 8 * i)) (v ^^^ ((u ^^^ v) &&& (if c then BitVec.allOnes 64 else 0)))).writeW
          (off B (dU + 8 * i)) ((u ^^^ ((u ^^^ v) &&& (if c then BitVec.allOnes 64 else 0))) -
            ((v ^^^ ((u ^^^ v) &&& (if c then BitVec.allOnes 64 else 0))) &&& (if o then BitVec.allOnes 64 else 0)) -
              t.gpr .t4) ∧
        t'.gpr .t4 = ((if u ^^^ ((u ^^^ v) &&& (if c then BitVec.allOnes 64 else 0)) <
              (v ^^^ ((u ^^^ v) &&& (if c then BitVec.allOnes 64 else 0))) &&& (if o then BitVec.allOnes 64 else 0)
            then (1 : BitVec 64) else 0) |||
          (if (u ^^^ ((u ^^^ v) &&& (if c then BitVec.allOnes 64 else 0))) -
              ((v ^^^ ((u ^^^ v) &&& (if c then BitVec.allOnes 64 else 0))) &&& (if o then BitVec.allOnes 64 else 0)) <
              t.gpr .t4 then 1 else 0))) ∧
      Keep gcdLRegs t t' := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [gcdBody, j0, j1, ja4, ja5, hu, hv, hs'.ld (show dU + 8 * i + 8 ≤ Z by omega_arith),
      hs'.ld (show dV + 8 * i + 8 ≤ Z by omega_arith),
      hs'.st (show dU + 8 * i + 8 ≤ Z by omega_arith), hs'.st (show dV + 8 * i + 8 ≤ Z by omega_arith),
      hs'.al8 (show dU + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith),
      hs'.al8 (show dV + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith)]
  refine WP.mono hst fun t' ⟨⟨l0, l1, l3, lm, lb⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, Keep.trans' jk lk⟩, l3⟩
  · rw [l0, show dU + 8 * i + 8 = dU + 8 * (i + 1) by omega_arith]
  · rw [l1, show dV + 8 * i + 8 = dV + 8 * (i + 1) by omega_arith]
  · rw [lb]; exact (sub64_arith _ _ _ j4).2
  · -- The frame: the two words written.
    intro x hx1 hx2
    have o1 := writeW_outside t.mem B (d := dV + 8 * i)
      (v ^^^ ((u ^^^ v) &&& (if c then BitVec.allOnes 64 else 0))) (by omega_arith)
    have o2 := writeW_outside (t.mem.writeW (off B (dV + 8 * i))
      (v ^^^ ((u ^^^ v) &&& (if c then BitVec.allOnes 64 else 0)))) B (d := dU + 8 * i)
      ((u ^^^ ((u ^^^ v) &&& (if c then BitVec.allOnes 64 else 0))) -
        ((v ^^^ ((u ^^^ v) &&& (if c then BitVec.allOnes 64 else 0))) &&& (if o then BitVec.allOnes 64 else 0)) -
          t.gpr .t4) (by omega_arith)
    rw [lm, o2 x (by omega_arith), o1 x (by omega_arith)]
    exact jout x (by omega_arith) (by omega_arith)
  all_goals
    have wu : u = word s.mem B (dU + 8 * i) := by
      rw [← hu]; exact jout.word (by omega_arith) (by omega_arith) (by omega_arith)
    have wv : v = word s.mem B (dV + 8 * i) := by
      rw [← hv]; exact jout.word (by omega_arith) (by omega_arith) (by omega_arith)
    have o2 := writeW_outside (t.mem.writeW (off B (dV + 8 * i))
      (v ^^^ ((u ^^^ v) &&& (if c then BitVec.allOnes 64 else 0)))) B (d := dU + 8 * i)
      ((u ^^^ ((u ^^^ v) &&& (if c then BitVec.allOnes 64 else 0))) -
        ((v ^^^ ((u ^^^ v) &&& (if c then BitVec.allOnes 64 else 0))) &&& (if o then BitVec.allOnes 64 else 0)) -
          t.gpr .t4) (by omega_arith)
    have o1 := writeW_outside t.mem B (d := dV + 8 * i)
      (v ^^^ ((u ^^^ v) &&& (if c then BitVec.allOnes 64 else 0))) (by omega_arith)
    have eV : wordsVal t'.mem B dV (i + 1) = wordsVal t.mem B dV i + 2 ^ (64 * i) * (if c then u else v).toNat := by
      rw [lm, o2.wordsVal (d := dV) (k := i + 1) (by omega_arith) (by omega_arith),
        fin64_wordsVal_write_top _ _ _ _ _ (by omega_arith), xsel64]
    rw [xsel64, xsel64'] at lb lm
    have eU : wordsVal t'.mem B dU (i + 1) = wordsVal t.mem B dU i +
        2 ^ (64 * i) * ((if c then v else u) - ((if c then u else v) &&& (if o then BitVec.allOnes 64 else 0)) -
          t.gpr .t4).toNat := by
      rw [lm, fin64_wordsVal_write_top _ _ _ _ _ (by omega_arith),
        (writeW_outside t.mem B (d := dV + 8 * i) (if c then u else v) (by omega_arith)).wordsVal (d := dU) (k := i)
          (by omega_arith) (by omega_arith)]
  · rw [eV, jv, wordsVal_succ_top s.mem B dU i, wordsVal_succ_top s.mem B dV i, wu, wv]
    cases c <;> rfl
  · have k := (sub64_arith (if c then v else u) ((if c then u else v) &&& (if o then BitVec.allOnes 64 else 0))
      (t.gpr .t4) j4).1
    rw [← lb, and_mask64] at k
    rw [eU, eV, wordsVal_succ_top s.mem B dU i, wordsVal_succ_top s.mem B dV i, Nat.mul_succ, Nat.pow_add, ← wu, ← wv]
    generalize ((if c then v else u) - ((if c then u else v) &&& (if o then BitVec.allOnes 64 else 0)) -
      t.gpr .t4).toNat = r at k ⊢
    generalize 2 ^ (64 * i) = P at ju ⊢
    rw [jv] at ju
    cases c <;> cases o <;> simp only [Bool.false_eq_true, ite_true, ite_false] at k ju ⊢ <;> grind

/-- The mask of a word's low bit. -/
theorem odd_mask (x : BitVec 64) :
    BitVec.ofNat 64 0 - (x &&& BitVec.ofNat 64 1) = if decide (x.toNat % 2 = 1) then BitVec.allOnes 64 else 0 := by
  have e := and_one_toNat x
  change (x &&& 1#64).toNat = _ at e
  rw [show BitVec.ofNat 64 1 = 1#64 from rfl, mask_of_slot _ (by rw [e]; omega_arith), e]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with z | z <;> simp [z]

theorem mask_and_mask (a b : Bool) :
    (if a then BitVec.allOnes 64 else (0 : BitVec 64)) &&& (if b then BitVec.allOnes 64 else 0) =
      if (a && b) then BitVec.allOnes 64 else 0 := by
  cases a <;> cases b <;> decide

/-- Two adjacent arrays' first `w` words changed: a frame of the two. -/
theorem Frame.of_out2 {B : Addr} {w j : Nat} {m m' : Mem}
    (h : Out2 B (arr w j) (8 * w) (arr w (j + 1)) (8 * w) m m') : Frame B w [j, j + 1] [] m m' := by
  intro x hx
  have h1 := hx (arr w j, S w) (by simp [ranges])
  have h2 := hx (arr w (j + 1), S w) (by simp [ranges])
  have hS : S w = 8 * (w + 2) := rfl
  exact h x (by omega_arith) (by omega_arith)

/-- `gcdStep`: `uvStep` on `([gU], [gV])`: the borrow of `u - v`, then one pass, then the halving. -/
theorem gcdStep_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N)
    (hN : 63 ≤ N) (hN' : N ≤ 2048) :
    WP isa gcdStep s fun t => Ws t B Z w N ∧
      Frame B w [gU, gV, gT1, gT2, gT3] [sOdd, sB, sC] s.mem t.mem ∧
      (num t.mem B w gU, num t.mem B w gV) = uvStep (num s.mem B w gU, num s.mem B w gV) ∧
      Keep gcdRegs s t := by
  have fU := h.arr_fit (j := gU) (by rdidx)
  have fV := h.arr_fit (j := gV) (by rdidx)
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wpos
  have := h.wle
  have aUV : arr w gV = arr w gU + S w := arr_succ w gU
  generalize hu : num s.mem B w gU = u
  generalize hv : num s.mem B w gV = v
  unfold gcdStep
  -- 1: the pointers, and the borrow of `u - v`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine ptr2_ok h (r := .t1) (r' := .t2) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (show gU < 2048 by decide) (show gV < 2048 by decide) fun x p1 p2 kx mx => ?_
  have hx := h.of_keep kx
  have hb : WP isa (.block [.li .t4 0, mov .t3 .s9]) x fun y =>
      (y.gpr .t1 = off B (arr w gU) ∧ y.gpr .t2 = off B (arr w gV) ∧ y.gpr .t3 = BitVec.ofNat 64 w ∧
        y.gpr .t4 = 0 ∧ y.mem = x.mem) ∧ Keep [.t3, .t4] x y := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [mov, fin64_exec_li_zero, hx.s9, add_ofNat_zero', p1, p2]
  refine WP.mono hb fun y ⟨⟨y1, y2, y3, y4, my⟩, ky⟩ => ?_
  have hy := hx.of_keep ky
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (cmpLoop_ok hy.scr y1 y2 y3 (by rw [y4]; decide) (by omega_arith) (by omega_arith)
    (arr_al _ _) (arr_al _ _) (by omega_arith) (by omega_arith)) fun z ⟨z4, mz, ⟨dx, hdx, zeq⟩, kz⟩ => ?_
  rw [y4, my, mx] at zeq
  change dx + num s.mem B w gV + 0 = num s.mem B w gU + _ at zeq
  rw [hu, hv, Nat.add_zero] at zeq
  have lt : (z.gpr .t4).toNat = 1 ↔ u < v := by
    have := borrow_iff zeq hdx z4; omega_arith
  have kyz : Keep loopRegs s z := Keep.trans' ((kx.trans ky).mono (by decide)) kz
  have hz := h.of_keep kyz
  -- 2: the masks of `odd` and `c = odd ∧ u < v`, and the pointers.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  simp only [List.append_assoc]
  refine ptr_ok hz (by decide) (by decide) (show gU < 2048 by decide) ?_
  rw [WP.block_append_iff]
  have mz' : z.mem = s.mem := by rw [mz, my, mx]
  have u0 : (word s.mem B (arr w gU)).toNat % 2 = u % 2 := by
    rw [← hu]; exact (wordsVal_mod2 s.mem B (d := arr w gU) (k := w) (by omega_arith)).symm
  have hb2 : WP isa (.block [.load .d .t5 .t0 0, .logicImm .and .t5 .t5 1, .li .t6 0, .sub .a5 .t6 .t5,
      .sub .a4 .t6 .t4, .logic .and .a4 .a4 .a5]) (z.write .t0 (off B (arr w gU))) fun y =>
        (y.gpr .a5 = (if decide (u % 2 = 1) then BitVec.allOnes 64 else 0) ∧
          y.gpr .a4 = (if (decide ((z.gpr .t4).toNat = 1) && decide (u % 2 = 1)) then BitVec.allOnes 64 else 0) ∧
          y.mem = z.mem) ∧ Keep [.t5, .t6, .a4, .a5] (z.write .t0 (off B (arr w gU))) y := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [add_ofNat_zero', fin64_exec_li_zero, hz.scr.ld (d := arr w gU) (n := 8) (by omega_arith),
      hz.scr.al8 (d := arr w gU) (by omega_arith) (arr_al _ _), mz']
    refine ⟨?_, ?_⟩
    · rw [show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl, odd_mask, u0]; rfl
    · rw [show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl, odd_mask, u0, mask_of_slot _ z4, mask_and_mask]
      congr 1
      rcases (show (z.gpr .t4).toNat = 0 ∨ (z.gpr .t4).toNat = 1 by omega_arith) with e | e <;> simp [e]
  refine WP.mono hb2 fun y2' ⟨⟨a5v, a4v, m2⟩, k2⟩ => ?_
  have k2' : Keep [.t0, .t5, .t6, .a4, .a5] z y2' := ((Keep.write _ _ _).trans k2).mono (by decide)
  have hy2 := hz.of_keep k2'
  refine ptr_ok hy2 (by decide) (by decide) (show gV < 2048 by decide) ?_
  have hb3 : WP isa (.block [.li .t4 0, mov .t3 .s9]) (y2'.write .t1 (off B (arr w gV))) fun y =>
      (y.gpr .t0 = off B (arr w gU) ∧ y.gpr .t1 = off B (arr w gV) ∧ y.gpr .t3 = BitVec.ofNat 64 w ∧
        y.gpr .t4 = 0 ∧ y.gpr .a4 = y2'.gpr .a4 ∧ y.gpr .a5 = y2'.gpr .a5 ∧ y.mem = y2'.mem) ∧
        Keep [.t3, .t4] (y2'.write .t1 (off B (arr w gV))) y := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    have y20 : y2'.gpr .t0 = off B (arr w gU) := by rw [k2.gpr (by decide)]; simp [VG.RISCV64.RegUpd.gpr_write]
    brun [mov, fin64_exec_li_zero, hy2.s9, add_ofNat_zero', y20]
  refine WP.mono hb3 fun y3' ⟨⟨q0, q1, q3, q4, q44, q45, m3⟩, k3⟩ => ?_
  have k3' : Keep [.t1, .t3, .t4] y2' y3' := ((Keep.write _ _ _).trans k3).mono (by decide)
  have hy3 := hy2.of_keep k3'
  -- 3: the pass.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (gcdLoop_ok hy3.scr (c := decide ((z.gpr .t4).toNat = 1) && decide (u % 2 = 1))
    (o := decide (u % 2 = 1)) q0 q1 q3 (by rw [q4]; decide) (by rw [q44, a4v]) (by rw [q45, a5v])
    (by omega_arith) (by omega_arith) (arr_al _ _) (arr_al _ _) (by omega_arith) (by omega_arith)
    (by omega_arith)) fun t4 ⟨b4, ev, eu, o4, kp⟩ => ?_
  have m3' : y3'.mem = s.mem := by rw [m3, m2, mz']
  rw [m3'] at ev o4
  rw [m3', q4] at eu
  change _ = if _ then num s.mem B w gU else num s.mem B w gV at ev
  change _ + _ + 0 = (if _ then num s.mem B w gV else num s.mem B w gU) + _ at eu
  rw [hu, hv] at ev eu
  have k4 : Keep gcdRegs s t4 :=
    Keep.trans' (Keep.trans' (kyz.mono (by decide)) (k2'.mono (by decide))) (Keep.trans' (k3'.mono (by decide))
      (kp.mono (by decide)))
  have h4 := h.of_keep k4
  -- 4: the halving.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have hzb : WP isa (.block [.li .t4 0]) t4 fun t5 =>
      (t5.gpr .t4 = 0 ∧ t5.mem = t4.mem) ∧ Keep [.t4] t4 t5 := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [fin64_exec_li_zero]
  refine WP.mono hzb fun t5 ⟨⟨z5, m5⟩, k5⟩ => ?_
  have h5 := h4.of_keep k5
  refine WP.mono (half_ok h5 (by rdidx) hN' (by rw [z5]; decide)) fun t ⟨h6, k6, e6, _, r6⟩ => ?_
  rw [z5, m5, show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero] at e6
  rw [m5] at k6
  have F4 : Frame B w [gU, gV] [] s.mem t4.mem := by
    exact (Frame.of_out2 (j := gU) o4).mono (by decide) (by simp)
  refine ⟨h6, (F4.trans k6.mono).mono, ?_, Keep.trans' k4 (Keep.trans' (k5.mono (by decide)) (r6.mono (by decide)))⟩
  have vt : num t.mem B w gV = num t4.mem B w gV := k6.num (by rdidx) (by simp) (h.fit64 (by rdidx))
  rw [vt, e6]
  change (wordsVal t4.mem B (arr w gU) w / 2, wordsVal t4.mem B (arr w gV) w) = _
  generalize hP : 2 ^ (64 * w) = P at eu
  have hR := wordsVal_lt t4.mem B (arr w gU) w
  have hU : u < P := hP ▸ hu ▸ wordsVal_lt _ _ _ _
  have hV : v < P := hP ▸ hv ▸ wordsVal_lt _ _ _ _
  rw [hP] at hR
  have hβ : (t4.gpr .t4).toNat = 0 ∨ (t4.gpr .t4).toNat = 1 := by omega_arith
  generalize (t4.gpr .t4).toNat = β at eu hβ
  generalize wordsVal t4.mem B (arr w gU) w = R at eu hR ⊢
  generalize wordsVal t4.mem B (arr w gV) w = V' at eu ev ⊢
  simp only [uvStep]
  rcases Nat.mod_two_eq_zero_or_one u with f | f
  · have c0 : (decide ((z.gpr .t4).toNat = 1) && decide (u % 2 = 1)) = false := by simp [f]
    have o0 : decide (u % 2 = 1) = false := by simp [f]
    rw [c0] at ev eu
    rw [o0] at eu
    simp only [Bool.false_eq_true, ite_false, Nat.add_zero] at ev eu
    have : R = u := by rcases hβ with e | e <;> rw [e] at eu <;> simp only [Nat.mul_zero, Nat.mul_one] at eu <;> omega
    simp [f, this, ev]
  · by_cases g : u < v
    · have cz : (z.gpr .t4).toNat = 1 := lt.mpr g
      simp only [cz, f, decide_true, Bool.and_self, ite_true, Nat.add_zero] at ev eu
      rw [ev] at eu
      have : R = v - u := by
        rcases hβ with e | e <;> rw [e] at eu <;> simp only [Nat.mul_zero, Nat.mul_one] at eu <;> omega
      simp [f, g, this, ev]
    · have cz : ¬(z.gpr .t4).toNat = 1 := fun e => g (lt.mp e)
      simp only [cz, f, decide_true, decide_false, Bool.false_and, Bool.false_eq_true, ite_false, ite_true,
        Nat.add_zero] at ev eu
      rw [ev] at eu
      have : R = u - v := by
        rcases hβ with e | e <;> rw [e] at eu <;> simp only [Nat.mul_zero, Nat.mul_one] at eu <;> omega
      simp [f, g, this, ev]

theorem shlk_ofNat (a k : Nat) : BitVec.ofNat 64 a <<< k = BitVec.ofNat 64 (2 ^ k * a) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mul_comm,
    Nat.mul_mod_mod]

/-- The GCD's count: `s7 := 32 w + 4 L`. -/
theorem gcdCount_ok {s : State} {B : Addr} {Z w N L : Nat} (h : Ws s B Z w N)
    (hl : s.gpr .s2 = BitVec.ofNat 64 L) :
    WP isa (.block [.shift .sll .d .s7 .s9 5, .shift .sll .d .t5 .s2 2, .add .s7 .s7 .t5]) s fun t =>
      (t.gpr .s7 = BitVec.ofNat 64 (32 * w + 4 * L) ∧ t.mem = s.mem) ∧ Keep [.s7, .t5] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [h.s9, hl, shlk_ofNat]
  exact (BitVec.ofNat_add _ _).symm

/-- The GCD's state after `i` iterations of two steps from `s0`. -/
structure GcdI (s0 : State) (B : Addr) (Z w N : Nat) (i : Nat) (t : State) : Prop where
  ws : Ws t B Z w N
  keep : Frame B w [gU, gV, gT1, gT2, gT3] [sOdd, sB, sC] s0.mem t.mem
  regs : Keep (.s7 :: gcdRegs) s0 t
  value : (num t.mem B w gU, num t.mem B w gV) = uvStep^[2 * i] (num s0.mem B w gU, num s0.mem B w gV)

theorem gcdBody_ok {s0 t : State} {B : Addr} {Z w N i : Nat} (hN : 63 ≤ N) (hN' : N ≤ 2048)
    (inv : GcdI s0 B Z w N i t) :
    WP isa (seqs [gcdStep, gcdStep, .block next]) t fun u =>
      GcdI s0 B Z w N (i + 1) u ∧ u.gpr .s7 = t.gpr .s7 - BitVec.ofNat 64 1 := by
  have h := inv.ws
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (gcdStep_ok h hN hN') fun t1 ⟨h1, k1, e1, r1⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (gcdStep_ok h1 hN hN') fun t2 ⟨h2, k2, e2, r2⟩ => ?_
  have hs : WP isa (.block next) t2 fun u =>
      (u.gpr .s7 = t2.gpr .s7 - BitVec.ofNat 64 1 ∧ u.mem = t2.mem) ∧ Keep [.s7] t2 u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [next]
  refine WP.mono hs fun u ⟨⟨u7, m2⟩, k3⟩ => ?_
  have r7 : t2.gpr .s7 = t.gpr .s7 := (r2.gpr (by decide)).trans (r1.gpr (by decide))
  refine ⟨⟨h2.of_keep k3, ?_, ?_, ?_⟩, by rw [u7, r7]⟩
  · rw [m2]; exact inv.keep.trans (k1.trans k2)
  · exact Keep.trans' inv.regs (Keep.mono ((r1.trans r2).trans k3) (by decide))
  · rw [m2, e2, e1, inv.value, show 2 * (i + 1) = 2 * i + 1 + 1 by omega_arith,
      Function.iterate_succ_apply', Function.iterate_succ_apply']

/-- `gcd`, narrow: `gcd(x, u)` from `x` in `aX2` and an odd `u` in `aU`, with
`x u < 2^(64 w + 8 L)` (`s2 = L = n_len`), into the low half of the wide `wG`,
its upper half kept (`hiW`, so a zero upper half makes the wide `wG` the GCD). -/
theorem gcd_ok {s : State} {B : Addr} {Z w N L : Nat} (h : Ws s B Z w N)
    (hN : 63 ≤ N) (hN' : N ≤ 2048) (hl : s.gpr .s2 = BitVec.ofNat 64 L) (hL : L < 2 ^ 32) :
    WP isa gcd s fun t => Ws t B Z w N ∧
      Frame B w [gU, gV, gT1, gT2, gT3, 2 * wG] [sOdd, sB, sC] s.mem t.mem ∧
      hiW t.mem B w wG = hiW s.mem B w wG ∧
      (num s.mem B w aU % 2 = 1 →
        num s.mem B w aX2 * num s.mem B w aU < 2 ^ (64 * w + 8 * L) →
        num t.mem B w (2 * wG) = Nat.gcd (num s.mem B w aX2) (num s.mem B w aU)) ∧
      Keep (.s7 :: gcdRegs) s t := by
  have := h.wle
  have := h.wpos
  have hS : S w = 8 * (w + 2) := rfl
  have nw := h.nowrap
  have fit := h.fits
  have fX := h.fit64 (j := aX2) (by rdidx)
  have fU := h.fit64 (j := aU) (by rdidx)
  have fV := h.fit64 (j := gV) (by rdidx)
  have a34 : arr w (2 * wG) + 8 * w + 8 * (w + 2) ≤ arr w gU := by
    simp only [arr, S, hdr_eq, wG, gU]; omega
  have fG : arr w (2 * wG) + 8 * w + 8 * (w + 2) ≤ 2 ^ 64 := by
    have := arr_mono (w := w) (show gU ≤ N by rdidx); omega
  generalize hx : num s.mem B w aX2 = x
  generalize hu : num s.mem B w aU = u
  unfold gcd
  -- The copies.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h (by rdidx) (by rdidx) hN' (by rdidx)) fun t1 ⟨h1, k1, e1, r1, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h1 (by rdidx) (by rdidx) hN' (by rdidx)) fun t2 ⟨h2, k2, e2, r2, _⟩ => ?_
  rw [k1.num (by rdidx) (by simp) fU, hu] at e2
  rw [hx] at e1
  have e1' : num t2.mem B w gU = x := by rw [k2.num (by rdidx) (by simp) (h1.fit64 (by rdidx)), e1]
  -- The count.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have hl2 : t2.gpr .s2 = BitVec.ofNat 64 L := by rw [r2.gpr (by decide), r1.gpr (by decide), hl]
  refine WP.mono (gcdCount_ok h2 hl2) fun t3 ⟨⟨c3, m3⟩, k3⟩ => ?_
  have h3 := h2.of_keep k3
  -- The loop.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have hK : 32 * w + 4 * L < 2 ^ 64 := by omega_arith
  refine WP.mono (wp_countdown (body := seqs [gcdStep, gcdStep, .block next]) (cnt := .s7)
    (N := 32 * w + 4 * L) hK (by omega_arith) (GcdI t3 B Z w N)
    (fun i _ t inv _ => gcdBody_ok hN hN' inv)
    ⟨h3, Frame.refl _ _ _ _ _, Keep.refl _ _, rfl⟩ c3) fun t4 inv => ?_
  -- The copy into `wG`.
  refine WP.mono (copy_ok inv.ws (by rdidx) (by rdidx) hN' (by rdidx)) fun t ⟨h5, k5, e5, r5, o5⟩ => ?_
  have F4 : Frame B w [gU, gV, gT1, gT2, gT3] [sOdd, sB, sC] s.mem t4.mem := by
    have F2 : Frame B w [gU, gV, gT1, gT2, gT3] [sOdd, sB, sC] s.mem t2.mem := Frame.join k1 k2
    have F3 := inv.keep
    rw [m3] at F3
    exact F2.trans F3
  refine ⟨h5, Frame.join F4 k5, ?_, fun hodd hlt => ?_, ?_⟩
  · simp only [hiW]
    rw [o5.wordsVal (.inr (by omega_arith)) fG]
    refine F4.words (fun j hj => ?_) (fun e he => ?_) fG
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      have := arr_mono (w := w) (show gU ≤ j by rcases hj with rfl | rfl | rfl | rfl | rfl <;> rdidx)
      omega_arith
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      have := hdr_le_arr w (2 * wG)
      rcases he with rfl | rfl | rfl <;> simp only [sOdd, sB, sC, hdr_eq] at * <;> omega_arith
  · rw [e5]
    have v := inv.value
    rw [m3, e1', show num t2.mem B w gV = u from e2] at v
    have D := uv_done (a := x) (m := u) (K := 2 * (32 * w + 4 * L)) hodd
      (by rw [show 2 * (32 * w + 4 * L) = 64 * w + 8 * L by omega_arith]; exact hlt)
    rw [D] at v
    exact (Prod.mk.inj v).2
  · exact Keep.trans' (Keep.trans' (Keep.mono r1 (by decide)) (Keep.trans' (Keep.mono r2 (by decide))
      (Keep.mono k3 (by decide)))) (Keep.trans' inv.regs (Keep.mono r5 (by decide)))

/-! ## The halvings -/

open VG.Impl.Rsa.RISCV64.RecoverDet (halfIfBody dblIf dblIfBody)
open VG.Impl.Rsa.RISCV64.RecoverDet (twosInit twosFlags halfIf twosBody twos ctxW ctxw aN aOne aT wX wX3 wT2
  sU sX sEven sBoth)

/-- The tail of `twosFlags`: `even := ¬u₀` and `both := ¬x₀ ∧ ¬u₀`, from the slots `sU`, `sX`. -/
theorem flagsTail_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N) :
    WP isa (.block [.load .d .t5 .s11 sU, .load .d .t6 .s11 sX, .logicImm .xor .t5 .t5 1,
        .logicImm .xor .t6 .t6 1, .store .d .t5 .s11 sEven, .logic .and .t6 .t6 .t5, .store .d .t6 .s11 sBoth]) s
      fun u => (u.mem = (s.mem.writeW (off B sEven) (word s.mem B sU ^^^ 1#64)).writeW (off B sBoth)
        ((word s.mem B sX ^^^ 1#64) &&& (word s.mem B sU ^^^ 1#64))) ∧ Keep [.t5, .t6] s u := by
  have nw := h.nowrap
  have hz := h.hdr_le
  simp only [hdr_eq] at hz
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [h.s11, h.scr.st (d := sEven) (n := 8) (by simp only [sEven]; omega_arith),
    h.scr.al8 (d := sEven) (by simp only [sEven]; omega_arith) (by decide),
    h.scr.st (d := sBoth) (n := 8) (by simp only [sBoth]; omega_arith),
    h.scr.al8 (d := sBoth) (by simp only [sBoth]; omega_arith) (by decide),
    h.scr.ld (d := sU) (n := 8) (by simp only [sU]; omega_arith),
    h.scr.al8 (d := sU) (by simp only [sU]; omega_arith) (by decide),
    h.scr.ld (d := sX) (n := 8) (by simp only [sX]; omega_arith),
    h.scr.al8 (d := sX) (by simp only [sX]; omega_arith) (by decide),
    show sU < 2048 by decide, show sX < 2048 by decide, show sEven < 2048 by decide,
    show sBoth < 2048 by decide, add_ofNat_zero']

/-- Index side conditions of the halvings. -/
macro "twidx" : tactic => `(tactic| ((try simp only [aN, aOne, aT, aU, aX2, wX, wX3, wT2, sU, sX, sEven, sBoth,
  hdr_eq, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, true_and,
  ne_eq]) <;> omega_arith))

/-- `twosFlags`: the low bits of `u` and `x`, `even := ¬u₀` and `both := ¬u₀ ∧ ¬x₀`. -/
theorem twosFlags_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N) (hN : 63 ≤ N)
    (hN' : N ≤ 2048) :
    WP isa (.block twosFlags) s fun t => Ws t B Z w N ∧ Frame B w [] [sU, sX, sEven, sBoth] s.mem t.mem ∧
      slot t.mem B sEven = (if num s.mem B w aU % 2 = 0 then 1 else 0) ∧
      slot t.mem B sBoth = (if num s.mem B w aU % 2 = 0 ∧ num s.mem B w aX2 % 2 = 0 then 1 else 0) ∧
      Keep opRegs s t := by
  have hsU : sU + 8 ≤ hdr := by decide
  have hsX : sX + 8 ≤ hdr := by decide
  have hsE : sEven + 8 ≤ hdr := by decide
  have hsB : sBoth + 8 ≤ hdr := by decide
  have fX := h.fit64 (j := aX2) (by twidx)
  unfold twosFlags
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (bitOf_ok h (by twidx) hN' hsU (by decide)) fun t1 ⟨h1, k1, o1, r1⟩ => ?_
  refine WP.mono (bitOf_ok h1 (by twidx) hN' hsX (by decide)) fun t2 ⟨h2, k2, o2, r2⟩ => ?_
  rw [k1.num (by simp) (by decide) fX] at o2
  have o1' : slot t2.mem B sU = num s.mem B w aU % 2 := by rw [k2.slot hsU (by decide), o1]
  refine WP.mono (flagsTail_ok h2) fun t ⟨mt, kt⟩ => ?_
  have nw := h2.nowrap
  have hz := h2.hdr_le
  simp only [hdr_eq] at hz
  have sw1 := slot_write (m := t2.mem) (B := B) (w := w) (d := sEven) (word t2.mem B sU ^^^ 1#64)
    (by simp only [sEven]; omega_arith)
  have sw2 := slot_write (m := t2.mem.writeW (off B sEven) (word t2.mem B sU ^^^ 1#64)) (B := B) (w := w)
    (d := sBoth) ((word t2.mem B sX ^^^ 1#64) &&& (word t2.mem B sU ^^^ 1#64)) (by simp only [sBoth]; omega_arith)
  rw [← mt] at sw2
  have bU : (word t2.mem B sU).toNat ≤ 1 := by change slot t2.mem B sU ≤ 1; rw [o1']; omega_arith
  have bX : (word t2.mem B sX).toNat ≤ 1 := by change slot t2.mem B sX ≤ 1; rw [o2]; omega_arith
  have xU : (word t2.mem B sU ^^^ 1#64).toNat = (num s.mem B w aU % 2 + 1) % 2 := by
    rw [xor_bits bU (by decide)]; change (slot t2.mem B sU + 1) % 2 = _; rw [o1']
  have xX : (word t2.mem B sX ^^^ 1#64).toNat = (num s.mem B w aX2 % 2 + 1) % 2 := by
    rw [xor_bits bX (by decide)]; change (slot t2.mem B sX + 1) % 2 = _; rw [o2]
  refine ⟨h2.of_keep kt, (k1.join k2 (js := []) (ds := [sU, sX, sEven, sBoth])).join
    (sw1.1.join sw2.1 (js := []) (ds := [sU, sX, sEven, sBoth])) (js := []) (ds := [sU, sX, sEven, sBoth]), ?_, ?_,
    Keep.trans' r1 (Keep.trans' r2 (Keep.mono kt (by decide)))⟩
  · rw [sw2.1.slot hsE (by decide), sw1.2, xU]
    rcases Nat.mod_two_eq_zero_or_one (num s.mem B w aU) with e | e <;> simp [e]
  · rw [sw2.2, and01 (by rw [xX]; omega_arith) (by rw [xU]; omega_arith), xX, xU]
    rcases Nat.mod_two_eq_zero_or_one (num s.mem B w aU) with e | e <;>
      rcases Nat.mod_two_eq_zero_or_one (num s.mem B w aX2) with f | f <;> simp [e, f]

/-- The masked halving over `n` words at `t0` (`countLoop .t3 halfIfBody`), the mask of `b` in
`a4`: `halfLoop_ok`'s words if `b`, else the same words. -/
theorem halfIfLoop_ok {s : State} {B : Addr} {Z dO n : Nat} (hs : Scr s B Z) {b : Bool}
    (h0 : s.gpr .t0 = off B dO) (h3 : s.gpr .t3 = BitVec.ofNat 64 n)
    (ha : s.gpr .a4 = if b then BitVec.allOnes 64 else 0) (hn : 1 ≤ n) (hn' : n < 2 ^ 32)
    (hO8 : dO % 8 = 0) (hO : dO + 8 * (n + 1) ≤ Z) :
    WP isa (countLoop .t3 halfIfBody) s fun t =>
      (if b then 2 * wordsVal t.mem B dO n + (word s.mem B dO).toNat % 2 =
          wordsVal s.mem B dO n + 2 ^ (64 * n) * ((word s.mem B (dO + 8 * n)).toNat % 2)
        else wordsVal t.mem B dO n = wordsVal s.mem B dO n) ∧
      Outside B dO (8 * n) s.mem t.mem ∧ Keep loopRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t0 = off B (dO + 8 * i) ∧ Outside B dO (8 * i) s.mem t.mem ∧
      (if b then 2 * wordsVal t.mem B dO i + (word s.mem B dO).toNat % 2 =
          wordsVal s.mem B dO i + 2 ^ (64 * i) * ((word s.mem B (dO + 8 * i)).toNat % 2)
        else wordsVal t.mem B dO i = wordsVal s.mem B dO i) ∧
      Keep [.t0, .t1, .t3, .t5, .t6] s t
  refine WP.mono (wp_countdown (body := .block (halfIfBody ++ ([.addi .t3 .t3 (-1)] : List Instr)))
    (cnt := .t3) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j0, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h0]; rfl, Outside.refl _ _ _ _, by cases b <;> simp [wordsVal], Keep.refl _ _⟩ h3)
    fun t ⟨_, jout, jeq, jk⟩ => ⟨jeq, jout, jk.mono (by decide)⟩
  have hs' := hs.congr jk.2.2
  have ja : t.gpr .a4 = if b then BitVec.allOnes 64 else 0 := (jk.gpr (r := .a4) (by decide)).trans ha
  have hst : WP isa (.block (halfIfBody ++ ([.addi .t3 .t3 (-1)] : List Instr))) t fun t' =>
      (t'.gpr .t0 = off B (dO + 8 * i + 8) ∧ t'.gpr .t3 = t.gpr .t3 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 8 * i))
          (word t.mem B (dO + 8 * i) ^^^ (((word t.mem B (dO + 8 * i) >>> 1 |||
            word t.mem B (dO + 8 * i + 8) <<< 63) ^^^ word t.mem B (dO + 8 * i)) &&&
              (if b then BitVec.allOnes 64 else 0)))) ∧
      Keep [.t0, .t1, .t3, .t5, .t6] t t' := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [halfIfBody, j0, ja, hs'.ld (show dO + 8 * i + 8 ≤ Z by omega_arith),
      hs'.ld (show dO + 8 * i + 8 + 8 ≤ Z by omega_arith),
      hs'.st (show dO + 8 * i + 8 ≤ Z by omega_arith),
      hs'.al8 (show dO + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith),
      hs'.al8 (show dO + 8 * i + 8 + 8 ≤ Z by omega_arith) (by omega_arith)]
  refine WP.mono hst fun t' ⟨⟨l0, l3, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, Keep.trans' jk lk⟩, l3⟩
  · rw [l0, show dO + 8 * i + 8 = dO + 8 * (i + 1) by omega_arith]
  · rw [lm]; exact out_step _ jout (by omega_arith)
  · have wa : word t.mem B (dO + 8 * i) = word s.mem B (dO + 8 * i) := jout.word (by omega_arith) (by omega_arith)
    have wb : word t.mem B (dO + 8 * i + 8) = word s.mem B (dO + 8 * i + 8) :=
      jout.word (by omega_arith) (by omega_arith)
    rw [lm, xsel64, fin64_wordsVal_write_top _ _ _ _ _ (by omega_arith), wa, wb, wordsVal_succ_top s.mem B dO i,
      show dO + 8 * (i + 1) = dO + 8 * i + 8 by omega_arith]
    cases b
    · simp only [Bool.false_eq_true, ite_false] at jeq ⊢
      rw [jeq]
    · simp only [ite_true] at jeq ⊢
      have k := half64_arith (word s.mem B (dO + 8 * i)) (word s.mem B (dO + 8 * i + 8))
      rw [Nat.mul_succ, Nat.pow_add]
      have e : 2 * (2 ^ (64 * i) * (word s.mem B (dO + 8 * i) >>> 1 ||| word s.mem B (dO + 8 * i + 8) <<< 63).toNat) +
          2 ^ (64 * i) * ((word s.mem B (dO + 8 * i)).toNat % 2) =
          2 ^ (64 * i) * (word s.mem B (dO + 8 * i)).toNat +
            2 ^ (64 * i) * 2 ^ 64 * ((word s.mem B (dO + 8 * i + 8)).toNat % 2) := by
        rw [Nat.mul_left_comm, ← Nat.mul_add, k, Nat.mul_add, Nat.mul_assoc]
      grind

/-- `halfIf j sl`: `[j]` halved if the slot `sl` holds 1, in one pass after word `w` := 0. -/
theorem halfIf_ok {s : State} {B : Addr} {Z w N j sl : Nat} (h : Ws s B Z w N) (hN : 63 ≤ N)
    (hN' : N ≤ 2048) (hj : j < N) (_hjT : j ≠ aT) (hsl : sl + 8 ≤ hdr) (hsl8 : sl % 8 = 0)
    (bit : slot s.mem B sl ≤ 1) :
    WP isa (halfIf j sl) s fun t => Ws t B Z w N ∧ Frame B w [aT, j] [] s.mem t.mem ∧
      num t.mem B w j = (if slot s.mem B sl = 0 then num s.mem B w j else num s.mem B w j / 2) ∧
      Keep opRegs s t := by
  have fit := h.arr_fit hj
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wpos
  have := h.wle
  have hz := h.hdr_le
  rw [halfIf]
  refine WP.seq ?_
  refine ptr_ok h (by decide) (by decide) (show j < 2048 by omega_arith) ?_
  have hb : WP isa (.block [.load .d .a4 .s11 sl, .li .t4 0, .sub .a4 .t4 .a4, .shift .sll .d .t5 .s9 3,
      .add .t5 .t0 .t5, .store .d .t4 .t5 0, mov .t3 .s9]) (s.write .t0 (off B (arr w j))) fun u =>
        (u.gpr .t0 = off B (arr w j) ∧ u.gpr .t3 = BitVec.ofNat 64 w ∧
          u.gpr .a4 = BitVec.ofNat 64 0 - word s.mem B sl ∧
          u.mem = s.mem.writeW (off B (arr w j + 8 * w)) (0 : BitVec 64)) ∧
        Keep [.t3, .t4, .t5, .a4] (s.write .t0 (off B (arr w j))) u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [mov, fin64_exec_li_zero, h.s9, h.s11, add_ofNat_zero', shl3_ofNat, off_add,
      h.scr.st (d := arr w j + 8 * w) (n := 8) (by omega_arith),
      h.scr.al8 (d := arr w j + 8 * w) (by omega_arith) (by have := arr_al w j; omega_arith),
      h.scr.ld (d := sl) (n := 8) (by have := h.hdr_le; omega_arith),
      h.scr.al8 (d := sl) (by have := h.hdr_le; omega_arith) hsl8,
      show sl < 2048 by have := hdr_eq; omega_arith]
    rfl
  refine WP.mono hb fun u ⟨⟨u0, u3, u4, mu⟩, ku⟩ => ?_
  have k₁ : Keep opRegs s u := ((Keep.write _ _ _).trans ku).mono (by decide)
  have hu : Ws u B Z w N := h.of_keep k₁
  rw [mask_of_slot _ bit] at u4
  refine WP.mono (halfIfLoop_ok hu.scr u0 u3 u4 (by omega_arith) (by omega_arith) (arr_al _ _) (by omega_arith))
    fun t ⟨teq, tout, kt⟩ => ?_
  have ow := writeW_outside s.mem B (d := arr w j + 8 * w) (0 : BitVec 64) (by omega_arith)
  rw [← mu] at ow
  have nu : num u.mem B w j = num s.mem B w j := ow.wordsVal (by omega_arith) (by omega_arith)
  have wz : word u.mem B (arr w j + 8 * w) = 0 := by rw [mu, word_writeW_self]
  refine ⟨hu.of_keep kt, ?_, ?_, Keep.trans' k₁ kt⟩
  · have f1 : Frame B w [aT, j] [] s.mem u.mem := by
      rw [mu]; exact Frame.of_arr (o := j) (d := 8 * w) (n := 8) (writeW_outside _ _ _ (by omega_arith))
        (by omega_arith) (by simp)
    exact f1.trans (Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using tout) (by omega_arith) (by simp))
  · change wordsVal t.mem B (arr w j) w = _
    rw [wz] at teq
    change _ = if (word s.mem B sl).toNat = 0 then wordsVal s.mem B (arr w j) w else wordsVal s.mem B (arr w j) w / 2
    change _ = if _ then num s.mem B w j else num s.mem B w j / 2
    rw [← nu]
    by_cases z : (word s.mem B sl).toNat = 0
    · simp only [z, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false, ite_true] at teq ⊢
      exact teq
    · simp only [z, ne_eq, not_false_eq_true, decide_true, ite_true, ite_false] at teq ⊢
      change 2 * wordsVal t.mem B (arr w j) w + _ = num u.mem B w j + _ at teq
      have m2 := wordsVal_mod2 u.mem B (d := arr w j) (k := w) (by omega_arith)
      change num u.mem B w j % 2 = _ at m2
      have z0 : (0 : BitVec 64).toNat % 2 = 0 := rfl
      rw [z0, Nat.mul_zero, Nat.add_zero] at teq
      change 2 * wordsVal t.mem B (arr w j) w + _ = wordsVal u.mem B (arr w j) w at teq
      change wordsVal u.mem B (arr w j) w % 2 = _ at m2
      show wordsVal t.mem B (arr w j) w = wordsVal u.mem B (arr w j) w / 2
      omega

/-- The masked doubling over `n` words at `t0` (`countLoop .t3 dblIfBody`), the mask of `b` in
`a4`: `shlLoop_ok`'s words if `b`, else the same words; the bit out in `t4` either way. -/
theorem dblIfLoop_ok {s : State} {B : Addr} {Z dO n : Nat} (hs : Scr s B Z) {b : Bool}
    (h0 : s.gpr .t0 = off B dO) (h3 : s.gpr .t3 = BitVec.ofNat 64 n) (h4 : (s.gpr .t4).toNat ≤ 1)
    (ha : s.gpr .a4 = if b then BitVec.allOnes 64 else 0) (hn : 1 ≤ n) (hn' : n < 2 ^ 32)
    (hO8 : dO % 8 = 0) (hO : dO + 8 * n ≤ Z) :
    WP isa (countLoop .t3 dblIfBody) s fun t =>
      (t.gpr .t4).toNat ≤ 1 ∧
      (if b then wordsVal t.mem B dO n + 2 ^ (64 * n) * (t.gpr .t4).toNat =
          2 * wordsVal s.mem B dO n + (s.gpr .t4).toNat
        else wordsVal t.mem B dO n = wordsVal s.mem B dO n) ∧
      Outside B dO (8 * n) s.mem t.mem ∧ Keep loopRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t0 = off B (dO + 8 * i) ∧ (t.gpr .t4).toNat ≤ 1 ∧ Outside B dO (8 * i) s.mem t.mem ∧
      (if b then wordsVal t.mem B dO i + 2 ^ (64 * i) * (t.gpr .t4).toNat =
          2 * wordsVal s.mem B dO i + (s.gpr .t4).toNat
        else wordsVal t.mem B dO i = wordsVal s.mem B dO i) ∧
      Keep [.t0, .t3, .t4, .t5, .t6] s t
  refine WP.mono (wp_countdown (body := .block (dblIfBody ++ ([.addi .t3 .t3 (-1)] : List Instr)))
    (cnt := .t3) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j0, j4, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h0]; rfl, h4, Outside.refl _ _ _ _, by cases b <;> simp [wordsVal], Keep.refl _ _⟩ h3)
    fun t ⟨_, j4, jout, jeq, jk⟩ => ⟨j4, jeq, jout, jk.mono (by decide)⟩
  have hs' := hs.congr jk.2.2
  have ja : t.gpr .a4 = if b then BitVec.allOnes 64 else 0 := (jk.gpr (r := .a4) (by decide)).trans ha
  have hst : WP isa (.block (dblIfBody ++ ([.addi .t3 .t3 (-1)] : List Instr))) t fun t' =>
      (t'.gpr .t0 = off B (dO + 8 * i + 8) ∧ t'.gpr .t3 = t.gpr .t3 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 8 * i))
          (word t.mem B (dO + 8 * i) ^^^ (((word t.mem B (dO + 8 * i) <<< 1 ||| t.gpr .t4) ^^^
            word t.mem B (dO + 8 * i)) &&& (if b then BitVec.allOnes 64 else 0))) ∧
        t'.gpr .t4 = word t.mem B (dO + 8 * i) >>> 63) ∧
      Keep [.t0, .t3, .t4, .t5, .t6] t t' := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [dblIfBody, j0, ja, hs'.ld (show dO + 8 * i + 8 ≤ Z by omega_arith),
      hs'.st (show dO + 8 * i + 8 ≤ Z by omega_arith),
      hs'.al8 (show dO + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith)]
  refine WP.mono hst fun t' ⟨⟨l0, l3, lm, l4⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, Keep.trans' jk lk⟩, l3⟩
  · rw [l0, show dO + 8 * i + 8 = dO + 8 * (i + 1) by omega_arith]
  · rw [l4]; exact (shl64_arith _ _ j4).2
  · rw [lm]; exact out_step _ jout (by omega_arith)
  · have wa : word t.mem B (dO + 8 * i) = word s.mem B (dO + 8 * i) := jout.word (by omega_arith) (by omega_arith)
    rw [lm, xsel64, fin64_wordsVal_write_top _ _ _ _ _ (by omega_arith), wa, wordsVal_succ_top s.mem B dO i]
    cases b
    · simp only [Bool.false_eq_true, ite_false] at jeq ⊢
      rw [jeq]
    · simp only [ite_true] at jeq ⊢
      have k := (shl64_arith (word s.mem B (dO + 8 * i)) (t.gpr .t4) j4).1
      rw [l4, wa, Nat.mul_succ, Nat.pow_add]
      have e : 2 ^ (64 * i) * (word s.mem B (dO + 8 * i) <<< 1 ||| t.gpr .t4).toNat +
          2 ^ (64 * i) * 2 ^ 64 * (word s.mem B (dO + 8 * i) >>> 63).toNat =
          2 * (2 ^ (64 * i) * (word s.mem B (dO + 8 * i)).toNat) + 2 ^ (64 * i) * (t.gpr .t4).toNat := by
        rw [Nat.mul_assoc, ← Nat.mul_add, k, Nat.mul_add, Nat.mul_left_comm]
      grind

/-- `dblIf j sl`: `[j]` doubled modulo `2^(64 w)` if the slot `sl` holds 1, in one pass. -/
theorem dblIf_ok {s : State} {B : Addr} {Z w N j sl : Nat} (h : Ws s B Z w N) (hj : j < N)
    (hN' : N ≤ 2048) (hsl : sl + 8 ≤ hdr) (hsl8 : sl % 8 = 0) (bit : slot s.mem B sl ≤ 1) :
    WP isa (dblIf j sl) s fun t => Ws t B Z w N ∧ Frame B w [j] [] s.mem t.mem ∧
      num t.mem B w j = (if slot s.mem B sl = 0 then num s.mem B w j else 2 * num s.mem B w j % 2 ^ (64 * w)) ∧
      Keep opRegs s t := by
  have fit := h.arr_fit hj
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wpos
  have := h.wle
  rw [dblIf]
  refine WP.seq ?_
  refine ptr_ok h (by decide) (by decide) (show j < 2048 by omega_arith) ?_
  have hb : WP isa (.block [.load .d .a4 .s11 sl, .li .t4 0, .sub .a4 .t4 .a4, mov .t3 .s9])
      (s.write .t0 (off B (arr w j))) fun u =>
        (u.gpr .t0 = off B (arr w j) ∧ u.gpr .t3 = BitVec.ofNat 64 w ∧ u.gpr .t4 = 0 ∧
          u.gpr .a4 = BitVec.ofNat 64 0 - word s.mem B sl ∧ u.mem = s.mem) ∧
        Keep [.t3, .t4, .a4] (s.write .t0 (off B (arr w j))) u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [mov, fin64_exec_li_zero, h.s9, h.s11, add_ofNat_zero',
      h.scr.ld (d := sl) (n := 8) (by have := h.hdr_le; omega_arith),
      h.scr.al8 (d := sl) (by have := h.hdr_le; omega_arith) hsl8,
      show sl < 2048 by have := hdr_eq; omega_arith]
    rfl
  refine WP.mono hb fun u ⟨⟨u0, u3, u4, ua, mu⟩, ku⟩ => ?_
  have k₁ : Keep opRegs s u := ((Keep.write _ _ _).trans ku).mono (by decide)
  have hu : Ws u B Z w N := h.of_keep k₁
  rw [mask_of_slot _ bit] at ua
  refine WP.mono (dblIfLoop_ok hu.scr u0 u3 (by rw [u4]; decide) ua (by omega_arith) (by omega_arith)
    (arr_al _ _) (by omega_arith)) fun t ⟨_, teq, tout, kt⟩ => ?_
  refine ⟨hu.of_keep kt, ?_, ?_, Keep.trans' k₁ kt⟩
  · rw [← mu]; exact Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using tout) (by omega_arith) (by simp)
  · change wordsVal t.mem B (arr w j) w = _
    rw [mu, u4] at teq
    change _ = if (word s.mem B sl).toNat = 0 then num s.mem B w j else 2 * num s.mem B w j % 2 ^ (64 * w)
    by_cases z : (word s.mem B sl).toNat = 0
    · simp only [z, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false, ite_true] at teq ⊢
      exact teq
    · simp only [z, ne_eq, not_false_eq_true, decide_true, ite_true, ite_false] at teq ⊢
      have z0 : (0 : BitVec 64).toNat = 0 := rfl
      rw [z0, Nat.add_zero] at teq
      rw [← teq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (wordsVal_lt _ _ _ _)]

/-- The registers the halvings and the GCD change. -/
abbrev rdRegs : List Reg := .s7 :: .s9 :: .s10 :: opRegs

/-- The halvings' state: `(u, x, 2^k x)`, narrow, narrow, wide. -/
def twosSt (m : Mem) (B : Addr) (w : Nat) : Nat × Nat × Nat :=
  (num m B w aU, num m B w aX2, num m B (W2 w) wX3)

theorem Frame.toNarrow1 {B : Addr} {w j : Nat} {ds : List Nat} {m m' : Mem}
    (h : Frame B (W2 w) [j] ds m m') : Frame B w [2 * j, 2 * j + 1] ds m m' := by
  simpa only [halves, List.flatMap_cons, List.flatMap_nil, List.append_nil] using h.toNarrow

/-- `twosBody`, narrow view to narrow view: one `twoStep` with `b = 64 W`. -/
theorem twosBody_ok {s : State} {B : Addr} {Z w N M : Nat} (h : Ws s B Z w N)
    (hN : 63 ≤ N) (hN' : N ≤ 2048) (hM : 20 ≤ M) (hMN : 2 * M ≤ N) (hW : W2 w ≤ 1024) :
    WP isa twosBody s fun t => Ws t B Z w N ∧
      Frame B w [aU, aX2, aT, 2 * wT2, 2 * wT2 + 1, 2 * wX3, 2 * wX3 + 1] [sU, sX, sEven, sBoth]
        s.mem t.mem ∧
      twosSt t.mem B w = VG.Proof.Rsa.RecoverDet.twoStep (64 * W2 w) (twosSt s.mem B w) ∧
      t.gpr .s7 = s.gpr .s7 - BitVec.ofNat 64 1 ∧ Keep rdRegs s t := by
  have hsE : sEven + 8 ≤ hdr := by decide
  have hsB : sBoth + 8 ≤ hdr := by decide
  have fU := h.fit64 (j := aU) (by twidx)
  have fX := h.fit64 (j := aX2) (by twidx)
  have hM' : M ≤ 2048 := by omega_arith
  generalize hu : num s.mem B w aU = u
  generalize hx : num s.mem B w aX2 = x
  generalize hX : num s.mem B (W2 w) wX3 = X
  unfold twosBody
  -- 1: the flags.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (twosFlags_ok h hN hN') fun t1 ⟨h1, k1, f1, g1, r1⟩ => ?_
  try simp only [hu, hx] at f1 g1
  -- 2: `u`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (halfIf_ok h1 hN hN' (by twidx) (by twidx) hsE (by decide) (by rw [f1]; split <;> omega_arith))
    fun t2 ⟨h2, k2, e2, r2⟩ => ?_
  rw [f1, k1.num (by simp) (by decide) fU, hu] at e2
  have g2 : slot t2.mem B sBoth = (if u % 2 = 0 ∧ x % 2 = 0 then 1 else 0) := by
    rw [k2.slot hsB (by simp), g1]
  -- 3: `x`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (halfIf_ok h2 hN hN' (by twidx) (by twidx) hsB (by decide) (by rw [g2]; split <;> omega_arith))
    fun t3 ⟨h3, k3, e3, r3⟩ => ?_
  rw [g2, k2.num (by simp [aT, aU, aX2]) (by simp) fX, k1.num (by simp) (by decide) fX, hx] at e3
  have g3 : slot t3.mem B sBoth = (if u % 2 = 0 ∧ x % 2 = 0 then 1 else 0) := by
    rw [k3.slot hsB (by simp), g2]
  have u3 : num t3.mem B w aU = (if (if u % 2 = 0 then 1 else 0) = 0 then u else u / 2) := by
    rw [k3.num (by simp [aT, aU, aX2]) (by simp) fU, e2]
  -- 4: the wide view.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (ctxW_ok h3 hW hMN) fun t4 ⟨⟨h4, m4⟩, k4⟩ => ?_
  have fX3 := h4.fit64 (j := wX3) (by twidx)
  have fT2 := h4.fit64 (j := wT2) (by twidx)
  have X4 : num t4.mem B (W2 w) wX3 = X := by
    rw [m4, k3.toWide.num (by decide) (by simp) fX3, k2.toWide.num (by decide) (by simp) fX3,
      k1.toWide.num (by simp) (by decide) fX3, hX]
  -- 5: `2^k x` doubled if both are even.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have g4 : slot t4.mem B sBoth = (if u % 2 = 0 ∧ x % 2 = 0 then 1 else 0) := by rw [m4, g3]
  refine WP.mono (dblIf_ok h4 (j := wX3) (by twidx) hM' hsB (by decide) (by rw [g4]; split <;> omega_arith))
    fun t7 ⟨h7, k7, e7, r7⟩ => ?_
  rw [g4, X4] at e7
  -- 8: the narrow view, a step less.
  show WP isa (.block (ctxw ++ next)) t7 _
  rw [WP.block_append_iff]
  refine WP.mono (ctxw_ok h7 h.wpos h.fits) fun t8 ⟨⟨h8, m8⟩, k8⟩ => ?_
  have hs : WP isa (.block next) t8 fun u =>
      (u.gpr .s7 = t8.gpr .s7 - BitVec.ofNat 64 1 ∧ u.mem = t8.mem) ∧ Keep [.s7] t8 u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [next]
  refine WP.mono hs fun t ⟨⟨u7, m9⟩, k9⟩ => ?_
  have W8 : Frame B w [2 * wT2, 2 * wT2 + 1, 2 * wX3, 2 * wX3 + 1] [] t4.mem t7.mem :=
    k7.toNarrow1.mono (by decide) (by simp)
  have fU' := h8.fit64 (j := aU) (by twidx)
  have fX' := h8.fit64 (j := aX2) (by twidx)
  refine ⟨h8.of_keep k9, ?_, ?_, ?_, ?_⟩
  · rw [m9, m8]
    have A : Frame B w [aU, aX2, aT, 2 * wT2, 2 * wT2 + 1, 2 * wX3, 2 * wX3 + 1] [sU, sX, sEven, sBoth]
        s.mem t3.mem :=
      (k1.join k2 (js := [aU, aX2, aT, 2 * wT2, 2 * wT2 + 1, 2 * wX3, 2 * wX3 + 1])
        (ds := [sU, sX, sEven, sBoth])).join k3
        (js := [aU, aX2, aT, 2 * wT2, 2 * wT2 + 1, 2 * wX3, 2 * wX3 + 1]) (ds := [sU, sX, sEven, sBoth])
    rw [← m4] at A
    exact A.join W8
  · have eU : num t.mem B w aU = (if (if u % 2 = 0 then 1 else 0) = 0 then u else u / 2) := by
      rw [m9, m8, W8.num (by simp [aU, wT2, wX3]) (by simp) fU', m4, u3]
    have eX : num t.mem B w aX2 = (if (if u % 2 = 0 ∧ x % 2 = 0 then 1 else 0) = 0 then x else x / 2) := by
      rw [m9, m8, W8.num (by simp [aX2, wT2, wX3]) (by simp) fX', m4, e3]
    have eW : num t.mem B (W2 w) wX3 = (if (if u % 2 = 0 ∧ x % 2 = 0 then 1 else 0) = 0 then X
        else 2 * X % 2 ^ (64 * W2 w)) := by
      rw [m9, m8, e7]
    simp only [twosSt, eU, eX, eW, hu, hx, hX, VG.Proof.Rsa.RecoverDet.twoStep]
    rcases Nat.mod_two_eq_zero_or_one u with a | a <;>
      rcases Nat.mod_two_eq_zero_or_one x with b | b <;> simp [a, b]
  · have r7 : t8.gpr .s7 = s.gpr .s7 := by
      rw [k8.gpr (by decide), r7.gpr (by decide), k4.gpr (by decide),
        r3.gpr (by decide), r2.gpr (by decide), r1.gpr (by decide)]
    rw [u7, r7]
  · exact Keep.trans' (Keep.mono r1 (by decide)) (Keep.trans' (Keep.mono r2 (by decide))
      (Keep.trans' (Keep.mono r3 (by decide)) (Keep.trans' (Keep.mono k4 (by decide))
          (Keep.trans' (Keep.mono r7 (by decide)) (Keep.trans' (Keep.mono k8 (by decide))
            (Keep.mono k9 (by decide)))))))

/-- A subtraction with its borrow is `wsub`. -/
theorem sub_eq_wsub {b x a c β : Nat} (e : x + c = a + 2 ^ b * β) (hx : x < 2 ^ b) (ha : a < 2 ^ b)
    (hc : c < 2 ^ b) (hβ : β ≤ 1) : x = VG.Proof.Rsa.RecoverDet.wsub b a c := by
  unfold VG.Proof.Rsa.RecoverDet.wsub
  rcases (show β = 0 ∨ β = 1 by omega_arith) with rfl | rfl
  · rw [show a + 2 ^ b - c = (a - c) + 2 ^ b by omega_arith, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  · rw [Nat.mod_eq_of_lt (by omega_arith)]; omega_arith

/-- `twosInit`, from the wide view: `2^k x := x`; `u := n - 1` and `x := x mod 2^(64 w)` (narrow);
`s7 := 64 w`; the narrow view after. -/
theorem twosInit_ok {s : State} {B : Addr} {Z w N M : Nat} (h : Ws s B Z (W2 w) M)
    (hw : 0 < w) (hNZ : arr w N ≤ Z) (hN : 63 ≤ N) (hN' : N ≤ 2048) (hM : 20 ≤ M) (hMN : 2 * M ≤ N)
    (h1 : num s.mem B w aOne = 0) :
    WP isa twosInit s fun t => Ws t B Z w N ∧
      Frame B w [2 * wX3, 2 * wX3 + 1, aOne, aU, aX2] [] s.mem t.mem ∧
      num t.mem B w aOne = 1 ∧
      twosSt t.mem B w = (VG.Proof.Rsa.RecoverDet.wsub (64 * w) (num s.mem B w aN) 1,
        num s.mem B (W2 w) wX % 2 ^ (64 * w), num s.mem B (W2 w) wX) ∧
      t.gpr .s7 = BitVec.ofNat 64 (64 * w) ∧ Keep rdRegs s t := by
  have hM' : M ≤ 2048 := by omega_arith
  have fXw := h.fit64 (j := wX) (by twidx)
  unfold twosInit
  -- 1: `2^k x := x` (wide).
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h (by twidx) (by twidx) hM' (by twidx)) fun t1 ⟨h1', k1, e1, r1, _⟩ => ?_
  -- 2: the narrow view.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (ctxw_ok h1' hw hNZ) fun t2 ⟨⟨h2, m2⟩, k2⟩ => ?_
  have fO := h2.fit64 (j := aOne) (by twidx)
  have fN := h2.fit64 (j := aN) (by twidx)
  have fX := h2.fit64 (j := 2 * wX) (by twidx)
  have fU := h2.fit64 (j := aU) (by twidx)
  have K1 := k1.toNarrow1
  -- 3: one.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (setOne_ok h2 (by twidx) hN') fun t3 ⟨h3, k3, e3, r3⟩ => ?_
  rw [m2, K1.num (by simp [aOne, wX3]) (by simp) fO, h1] at e3
  simp only [Nat.zero_div, Nat.mul_zero, Nat.add_zero] at e3
  -- 4: `u = n - 1`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h3 (by twidx) (by twidx) (by twidx) hN' (by twidx) (by twidx))
    fun t4 ⟨h4, k4, e4, b4, r4⟩ => ?_
  rw [e3, k3.num (by simp [aOne, aN]) (by simp) fN, m2, K1.num (by simp [aN, wX3]) (by simp) fN] at e4
  have u4 : num t4.mem B w aU = VG.Proof.Rsa.RecoverDet.wsub (64 * w) (num s.mem B w aN) 1 :=
    sub_eq_wsub e4 (wordsVal_lt _ _ _ _) (wordsVal_lt _ _ _ _) (Nat.one_lt_two_pow (by omega_arith)) b4
  -- 5: `x` (narrow).
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h4 (by twidx) (by twidx) hN' (by twidx)) fun t5 ⟨h5, k5, e5, r5, _⟩ => ?_
  rw [k4.num (by simp [aU, wX]) (by simp) fX, k3.num (by simp [aOne, wX]) (by simp) fX, m2,
    K1.num (by simp [wX, wX3]) (by simp) fX, num_low] at e5
  -- 6: the count.
  have hc : WP isa (.block [.shift .sll .d .s7 .s9 6]) t5 fun t =>
      (t.gpr .s7 = BitVec.ofNat 64 (64 * w) ∧ t.mem = t5.mem) ∧ Keep [.s7] t5 t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [h5.s9, shlk_ofNat]
  refine WP.mono hc fun t ⟨⟨c6, m6⟩, k6⟩ => ?_
  have fX3 := h1'.fit64 (j := wX3) (by twidx)
  have fA := h5.fit64 (j := aX2) (by twidx)
  refine ⟨h5.of_keep k6, ?_, ?_, ?_, c6, ?_⟩
  · rw [m6]
    have A := K1
    rw [← m2] at A
    exact (A.join k3 (js := [2 * wX3, 2 * wX3 + 1, aOne, aU, aX2]) (ds := [])).join
      (k4.join k5 (js := [2 * wX3, 2 * wX3 + 1, aOne, aU, aX2]) (ds := []))
      (js := [2 * wX3, 2 * wX3 + 1, aOne, aU, aX2]) (ds := [])
  · rw [m6, k5.num (by simp [aOne, aX2]) (by simp) fO, k4.num (by simp [aOne, aU]) (by simp) fO, e3]
  · simp only [twosSt]
    rw [m6, k5.num (by simp [aU, aX2]) (by simp) fU, u4, e5,
      k5.toWide.num (by decide) (by simp) fX3, k4.toWide.num (by decide) (by simp) fX3,
      k3.toWide.num (by decide) (by simp) fX3, m2, e1]
  · exact Keep.trans' (Keep.mono r1 (by decide)) (Keep.trans' (Keep.mono k2 (by decide))
      (Keep.trans' (Keep.mono r3 (by decide)) (Keep.trans' (Keep.mono r4 (by decide))
        (Keep.trans' (Keep.mono r5 (by decide)) (Keep.mono k6 (by decide))))))

/-- The halvings' state after `i` steps from `s0`. -/
structure TwosI (s0 : State) (B : Addr) (Z w N : Nat) (i : Nat) (t : State) : Prop where
  ws : Ws t B Z w N
  keep : Frame B w [aU, aX2, aT, 2 * wT2, 2 * wT2 + 1, 2 * wX3, 2 * wX3 + 1] [sU, sX, sEven, sBoth]
    s0.mem t.mem
  regs : Keep rdRegs s0 t
  value : twosSt t.mem B w = (VG.Proof.Rsa.RecoverDet.twoStep (64 * W2 w))^[i] (twosSt s0.mem B w)

/-- `twos`, from the wide view after `d e - 1`: `64 w` steps from `(n - 1, x mod 2^(64 w), x)`,
`n` narrow in `aN` and `x` wide in `wX`; the narrow view after. -/
theorem twos_ok {s : State} {B : Addr} {Z w N M : Nat} (h : Ws s B Z (W2 w) M)
    (hw : 0 < w) (hNZ : arr w N ≤ Z) (hN : 63 ≤ N) (hN' : N ≤ 2048) (hM : 20 ≤ M)
    (hMN : 2 * M ≤ N) (hW : W2 w ≤ 1024) (h1 : num s.mem B w aOne = 0) :
    WP isa twos s fun t => Ws t B Z w N ∧
      Frame B w [2 * wX3, 2 * wX3 + 1, aOne, aU, aX2, aT, 2 * wT2, 2 * wT2 + 1] [sU, sX, sEven, sBoth]
        s.mem t.mem ∧
      num t.mem B w aOne = 1 ∧
      twosSt t.mem B w = (VG.Proof.Rsa.RecoverDet.twoStep (64 * W2 w))^[64 * w]
        (VG.Proof.Rsa.RecoverDet.wsub (64 * w) (num s.mem B w aN) 1,
          num s.mem B (W2 w) wX % 2 ^ (64 * w), num s.mem B (W2 w) wX) ∧
      Keep rdRegs s t := by
  unfold twos
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (twosInit_ok h hw hNZ hN hN' hM hMN h1) fun t0 ⟨h0, k0, o0, e0, c0, r0⟩ => ?_
  have hK : 64 * w < 2 ^ 64 := by have := h0.wle; omega_arith
  refine WP.mono (wp_countdown (body := twosBody) (cnt := .s7) (N := 64 * w) hK (by omega_arith)
    (TwosI t0 B Z w N)
    (fun i _ t inv _ => WP.mono (twosBody_ok inv.ws hN hN' hM hMN hW) fun u ⟨hu, ku, eu, cu, ru⟩ =>
      ⟨⟨hu, inv.keep.trans ku, Keep.trans' inv.regs ru, by
        rw [eu, inv.value, Function.iterate_succ_apply']⟩, cu⟩)
    ⟨h0, Frame.refl _ _ _ _ _, Keep.refl _ _, rfl⟩ c0) fun t inv => ?_
  have fO := h0.fit64 (j := aOne) (by twidx)
  refine ⟨inv.ws, ?_, ?_, ?_, Keep.trans' r0 inv.regs⟩
  · exact k0.join inv.keep (js := [2 * wX3, 2 * wX3 + 1, aOne, aU, aX2, aT, 2 * wT2, 2 * wT2 + 1])
      (ds := [sU, sX, sEven, sBoth])
  · rw [inv.keep.num (by simp [aOne, aU, aX2, aT, wT2, wX3]) (by decide) fO, o0]
  · rw [inv.value, e0]

end VG.Proof.Rsa.RISCV64.Keys
