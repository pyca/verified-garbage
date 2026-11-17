module

public import VerifiedGarbage.Proof.Rsa.BoolNat
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Instr
import Mathlib.Tactic.Set
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import Mathlib.Tactic.Attr.Core
public import VerifiedGarbage.Impl.RsaKeyGen.Arm.Candidate
public import VerifiedGarbage.Proof.Rsa.Arm.KeyWs
import VerifiedGarbage.Proof.RsaKeyGen.Table
import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Basic
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Bignum.Arm.TrialDivision16
import VerifiedGarbage.Proof.RsaKeyGen.TrialMath
import Mathlib.Algebra.NeZero

/-! ### `Dsa.Arm.Prime.TrialP`, which only this module used -/

section

/-! # A candidate on ARMv7: trial division by one prime (`trialPrime_ok`)

For the prime `s` in `r3`: `−s⁻¹ mod 2^16` by Newton's iteration
(`entryS_ok`), the Montgomery reduction of `c`'s 16-bit halves
(`redc_ok`, a word at a time: `trialWord_ok`, all of them: `primeLoop_ok`),
and `r11 |= s ∣ c` (`trialFlag_ok`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Impl.RsaKeyGen VG.Proof.RsaKeyGen
open VG.Proof.Rsa (b2n)

/-! ## Words -/

theorem lo16 (v : BitVec 32) : ((v <<< 16) >>> 16).toNat = v.toNat % 2 ^ 16 := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    show 2 ^ 32 = 2 ^ 16 * 2 ^ 16 by rfl, Nat.mul_mod_mul_right, Nat.mul_div_cancel _ (Nat.two_pow_pos 16)]

theorem hi16 (v : BitVec 32) : (v >>> 16).toNat = v.toNat / 2 ^ 16 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- `(v − 1) >> 31` is 1 iff `v` is 0, for `v < 2^31`. -/
theorem isZero_bit {v : BitVec 32} (h : v.toNat < 2 ^ 31) :
    ((v - 1) >>> 31).toNat = if v.toNat = 0 then 1 else 0 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub]
  simp only [show (1 : BitVec 32).toNat = 1 from rfl]
  split <;> omega_arith

/-! ## Newton's iteration -/

/-- `r4 := r4 (2 − r3 r4)`. -/
theorem newton_ok {u : State} {rest : List Instr} {Q : State → Prop}
    (k : ∀ u', Rest [.r4, .r5, .r6] u u' → u'.mem = u.mem →
      u'.gpr .r4 = nstep (u.gpr .r3) (u.gpr .r4) → WP isa (.block rest) u' Q) :
    WP isa (.block (newton ++ rest)) u Q := by
  exact VG.Proof.Bignum.Arm.TrialDivision16.newton_ok k

/-- For the prime `s` in `r3`: `r4 := −s⁻¹ mod 2^16`, `r0 :=` the address of
`c`, `r1 := W − 2`, `r2 := 0`. -/
theorem entryS_ok {u : State} {B : BitVec 32} {Z W : Nat} (hw : Ws u B Z W nArr) (hW : 2 ≤ W)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ u', Rest [.r0, .r1, .r2, .r4, .r5, .r6] u u' → u'.mem = u.mem → Ws u' B Z W nArr →
      u'.gpr .r4 = ninv (u.gpr .r3) → u'.gpr .r0 = B + BitVec.ofNat 32 (arr W aC) →
      u'.gpr .r1 = BitVec.ofNat 32 (W - 2) → u'.gpr .r2 = 0 → WP isa (.block rest) u' Q) :
    WP isa (.block (entryS ++ rest)) u Q := by
  simp only [entryS, List.cons_append, List.append_assoc]
  refine wp_mov (op2_reg _ _) fun u1 v1 => newton_ok fun u2 k2 m2 e2 => newton_ok fun u3 k3 m3 e3 =>
    newton_ok fun u4 k4 m4 e4 => ?_
  simp only [List.nil_append]
  refine wp_mov (op2_imm (by decide)) fun u5 v5 => wp_dp (op2_reg _ _) fun u6 v6 =>
    wp_mov (op2_lsl (by decide)) fun u7 v7 => wp_mov (op2_lsr (by decide)) fun u8 v8 => ?_
  obtain k8 : Rest [.r0, .r1, .r2, .r4, .r5, .r6] u u8 :=
    (v1.rest (by simp)).trans ((k2.mono (by simp)).trans ((k3.mono (by simp)).trans ((k4.mono (by simp)).trans
      ((v5.rest (by simp)).trans ((v6.rest (by simp)).trans ((v7.rest (by simp)).trans (v8.rest (by simp))))))))
  obtain m8 : u8.mem = u.mem := by rw [v8.mem, v7.mem, v6.mem, v5.mem, m4, m3, m2, v1.mem]
  obtain hw8 := hw.rest k8
  obtain r3 : ∀ x : State, Rest [.r0, .r1, .r2, .r4, .r5, .r6] u x → x.gpr .r3 = u.gpr .r3 :=
    fun x h => h.gpr _ (by decide)
  obtain e8 : u8.gpr .r4 = ninv (u.gpr .r3) := by
    rw [v8.gpr, v7.gpr, v6.gpr, dpVal, v5.gpr, v5.other _ (by decide), e4, e3, e2, v1.gpr,
      r3 u3 ((v1.rest (by simp)).trans ((k2.mono (by simp)).trans (k3.mono (by simp)))),
      r3 u2 ((v1.rest (by simp)).trans (k2.mono (by simp))), r3 u1 (v1.rest (by simp))]
    rfl
  refine ptr_ok hw8 (r := .r0) (by decide) (by decide) fun u9 p9 k9 m9 hw9 => ?_
  refine wp_dp (op2_imm (by decide)) fun u10 v10 => wp_mov (op2_imm (by decide)) fun u11 v11 =>
    k u11 (k8.trans ((k9.mono (by simp)).trans ((v10.rest (by simp)).trans (v11.rest (by simp)))))
      (by rw [v11.mem, v10.mem, m9, m8]) (hw9.rest (ws := [.r1, .r2]) ((v10.rest (by simp)).trans (v11.rest (by simp))))
      (by rw [v11.other _ (by decide), v10.other _ (by decide), k9.gpr _ (by decide), e8])
      (by rw [v11.other _ (by decide), v10.other _ (by decide), p9]) ?_ (by rw [v11.gpr])
  rw [v11.other _ (by decide), v10.gpr, dpVal, hw9.r9]
  apply BitVec.eq_of_toNat_eq
  have : W < 2 ^ 32 := by have := hw.wle; omega_arith
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  simp only [show (2 : BitVec 32).toNat = 2 from rfl]
  omega_arith

/-! ## Montgomery reduction -/

/-- `acc := (acc + h) 2^(−16) mod s`, below `2 s`, for `h` in `r5`. -/
theorem redc_ok {u : State} {h acc s sv : Nat} (r5 : (u.gpr .r5).toNat = h) (hh : h < 2 ^ 16)
    (r2 : u.gpr .r2 = BitVec.ofNat 32 acc) (hacc : acc < 2 * s) (r4 : (u.gpr .r4).toNat = sv)
    (r3 : u.gpr .r3 = BitVec.ofNat 32 s) (hs : 3 ≤ s ∧ s < 8162) (hinv : (s * sv + 1) % 2 ^ 16 = 0)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ u', Rest [.r2, .r5, .r6] u u' → u'.mem = u.mem →
      (∀ a', a' < 2 * s → a' * 2 ^ 16 % s = (h + acc) % s → u'.gpr .r2 = BitVec.ofNat 32 a' →
        WP isa (.block rest) u' Q)) :
    WP isa (.block (redc ++ rest)) u Q := by
  exact VG.Proof.Bignum.Arm.TrialDivision16.redc_ok r5 hh r2 hacc r4 r3 hs hinv k

/-! ## A word of `c` -/

/-- After `j` words of `c` (at the key array `aC` of the memory `m`), for
the prime `s` in `r3` with `−s⁻¹ mod 2^16` in `r4`. -/
structure TW (B : BitVec 32) (Z W : Nat) (m : Mem) (s : Nat) (u₀ : State) (j : Nat) (u : State) : Prop where
  ws : Ws u B Z W nArr
  mem : u.mem = m
  rest : Rest [.r0, .r1, .r2, .r5, .r6] u₀ u
  r0 : u.gpr .r0 = B + BitVec.ofNat 32 (arr W aC + 4 * j)
  r1 : u.gpr .r1 = BitVec.ofNat 32 (W - 2 - j)
  acc : ∃ a, u.gpr .r2 = BitVec.ofNat 32 a ∧ a < 2 * s ∧
    a * 2 ^ (32 * j) % s = val32 m (State.addr B) (arr W aC) j % s

theorem trialWord_ok {B : BitVec 32} {Z W : Nat} {m : Mem} {s : Nat} {u₀ u : State} {j : Nat}
    (h : TW B Z W m s u₀ j u) (hj : j < W - 2) (hZ : arr W aC + 4 * W ≤ Z)
    (r3 : u₀.gpr .r3 = BitVec.ofNat 32 s) (hs : 3 ≤ s ∧ s < 8162)
    (hinv : (s * (u₀.gpr .r4).toNat + 1) % 2 ^ 16 = 0) :
    WP isa (.block trialWord) u fun u' => TW B Z W m s u₀ (j + 1) u' ∧ u'.z = decide (W - 2 - (j + 1) = 0) := by
  obtain ⟨hw, mem, rest, r0, r1, a, r2, ha, hc⟩ := h
  have hn := hw.nowrap
  have hW := hw.wle
  obtain ea : State.addr (u.gpr .r0 + BitVec.ofNat 32 0) = off (State.addr B) (arr W aC + 4 * j) := by
    rw [r0, BitVec.add_assoc, ← BitVec.ofNat_add]; exact hw.addr (by omega_arith)
  obtain rd : InRegions (u.rd ++ u.wr) (off (State.addr B) (arr W aC + 4 * j)) 4 := hw.read (by omega_arith)
  obtain r3u : u.gpr .r3 = BitVec.ofNat 32 s := by rw [rest.gpr _ (by decide), r3]
  obtain r4u : (u.gpr .r4).toNat = (u₀.gpr .r4).toNat := by rw [rest.gpr _ (by decide)]
  set x := w32 m (State.addr B) (arr W aC + 4 * j) with ex
  obtain rx : (u.mem.readW (off (State.addr B) (arr W aC + 4 * j)) 32).toNat = x := by rw [mem]
  simp only [trialWord, List.cons_append, List.append_assoc]
  refine wp_ldr (by decide) ea rd fun u1 v1 => wp_mov (op2_lsl (by decide)) fun u2 v2 =>
    wp_mov (op2_lsr (by decide)) fun u3 v3 => ?_
  obtain h3 : (u3.gpr .r5).toNat = x % 2 ^ 16 := by rw [v3.gpr, v2.gpr, lo16, v1.gpr, rx]
  obtain k3 : Rest [.r5] u u3 := (v1.rest (by simp)).trans ((v2.rest (by simp)).trans (v3.rest (by simp)))
  obtain m3 : u3.mem = u.mem := by rw [v3.mem, v2.mem, v1.mem]
  refine redc_ok h3 (Nat.mod_lt _ (by decide)) (by rw [k3.gpr _ (by decide), r2]) ha
    (by rw [k3.gpr _ (by decide), r4u]) (by rw [k3.gpr _ (by decide), r3u]) hs hinv
    fun u4 k4 m4 a1 ha1 hc1 r24 => ?_
  simp only [List.nil_append]
  obtain ea4 : State.addr (u4.gpr .r0 + BitVec.ofNat 32 0) = off (State.addr B) (arr W aC + 4 * j) := by
    rw [k4.gpr _ (by decide), k3.gpr _ (by decide)]; exact ea
  obtain rd4 : InRegions (u4.rd ++ u4.wr) (off (State.addr B) (arr W aC + 4 * j)) 4 := by
    rw [k4.rd, k4.wr, k3.rd, k3.wr]; exact rd
  refine wp_ldr (by decide) ea4 rd4 fun u5 v5 => wp_mov (op2_lsr (by decide)) fun u6 v6 => ?_
  obtain h6 : (u6.gpr .r5).toNat = x / 2 ^ 16 := by rw [v6.gpr, hi16, v5.gpr, m4, m3, rx]
  obtain k6 : Rest [.r5] u4 u6 := (v5.rest (by simp)).trans (v6.rest (by simp))
  obtain hx : x < 2 ^ 32 := (m.readW _ 32).isLt
  refine redc_ok h6 (by omega_arith) (by rw [k6.gpr _ (by decide), r24]) ha1
    (by rw [k6.gpr _ (by decide), k4.gpr _ (by decide), k3.gpr _ (by decide), r4u])
    (by rw [k6.gpr _ (by decide), k4.gpr _ (by decide), k3.gpr _ (by decide), r3u]) hs hinv
    fun u7 k7 m7 a2 ha2 hc2 r27 => ?_
  refine wp_dp (op2_imm (by decide)) fun u8 v8 => wp_subs (op2_imm (by decide)) fun u9 v9 z9 => WP.block_nil ?_
  obtain kall : Rest [.r0, .r1, .r2, .r5, .r6] u u9 :=
    ((k3.mono (by simp)).trans ((k4.mono (by simp)).trans ((k6.mono (by simp)).trans ((k7.mono (by simp)).trans
      ((v8.rest (by simp)).trans (v9.rest (by simp)))))))
  obtain m9 : u9.mem = m := by rw [v9.mem, v8.mem, m7, v6.mem, v5.mem, m4, m3, mem]
  obtain r1v : u9.gpr .r1 = BitVec.ofNat 32 (W - 2 - (j + 1)) := by
    rw [v9.gpr, v8.other _ (by decide), k7.gpr _ (by decide), k6.gpr _ (by decide), k4.gpr _ (by decide),
      k3.gpr _ (by decide), r1]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, ofNat_toNat_lt (by omega_arith), ofNat_toNat_lt (by omega_arith)]
    simp only [show (1 : BitVec 32).toNat = 1 from rfl]
    omega_arith
  refine ⟨⟨hw.rest kall, m9, rest.trans kall, ?_, r1v, a2, ?_, ha2, ?_⟩, ?_⟩
  · rw [v9.other _ (by decide), v8.gpr, dpVal, k7.gpr _ (by decide), k6.gpr _ (by decide), k4.gpr _ (by decide),
      k3.gpr _ (by decide), r0, BitVec.add_assoc, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl,
      ← BitVec.ofNat_add]
    congr 2
  · rw [v9.other _ (by decide), v8.other _ (by decide), r27]
  · rw [val32_succ, ← ex]
    exact trial_word16 (x := x) hc1 (by rw [hc2, Nat.add_comm]) hc
  · rw [z9, ← v9.gpr, r1v]
    by_cases h0 : W - 2 - (j + 1) = 0
    · simp [h0]
    · have : (BitVec.ofNat 32 (W - 2 - (j + 1))) ≠ 0 := fun e => h0 (by
        have := congrArg BitVec.toNat e; rw [ofNat_toNat_lt (by omega_arith)] at this; simpa using this)
      simpa [h0] using this

theorem isa_ne (s : State) : isa.eval .ne s = some (!s.z) := rfl

/-- All the words of `c`. -/
theorem primeLoop_ok {B : BitVec 32} {Z W : Nat} {m : Mem} {s : Nat} {u₀ u : State}
    (h : TW B Z W m s u₀ 0 u) (hW : 3 ≤ W) (hZ : arr W aC + 4 * W ≤ Z)
    (r3 : u₀.gpr .r3 = BitVec.ofNat 32 s) (hs : 3 ≤ s ∧ s < 8162)
    (hinv : (s * (u₀.gpr .r4).toNat + 1) % 2 ^ 16 = 0) :
    WP isa (.loop (.block trialWord) .ne) u (TW B Z W m s u₀ (W - 2)) := by
  refine WP.loop (M := isa) (fun n v => 0 < n ∧ n ≤ W - 2 ∧ TW B Z W m s u₀ (W - 2 - n) v)
    (fun n v ⟨hn, hn2, hu⟩ => ?_)
    (W - 2) u ⟨by omega_arith, Nat.le_refl _, by rw [Nat.sub_self]; exact h⟩
  refine WP.mono (trialWord_ok hu (by omega_arith) hZ r3 hs hinv) fun u' ⟨hu', z⟩ => ?_
  rw [isa_ne, z]
  by_cases h0 : n = 1
  · subst h0
    refine .inl ⟨by simp; omega_arith, ?_⟩
    rwa [show W - 2 - 1 + 1 = W - 2 by omega_arith] at hu'
  · refine .inr ⟨by simp; omega_arith, n - 1, by omega_arith, by omega_arith, by omega_arith, ?_⟩
    rwa [show W - 2 - n + 1 = W - 2 - (n - 1) by omega_arith] at hu'

/-- `r11 |=` whether `acc` (in `r2`) is 0 or `s` (in `r3`). -/
theorem trialFlag_ok {u : State} {a s : Nat} {f : Bool} (r2 : u.gpr .r2 = BitVec.ofNat 32 a) (ha : a < 2 * s)
    (r3 : u.gpr .r3 = BitVec.ofNat 32 s) (hs : s < 8162) (r11 : u.gpr .r11 = BitVec.ofNat 32 (b2n f))
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ u', Rest [.r5, .r6, .r11] u u' → u'.mem = u.mem →
      u'.gpr .r11 = BitVec.ofNat 32 (b2n (f || decide (a = 0 ∨ a = s))) → WP isa (.block rest) u' Q) :
    WP isa (.block (trialFlag ++ rest)) u Q := by
  simp only [trialFlag, List.cons_append, List.nil_append]
  refine wp_dp (op2_imm (by decide)) fun u1 v1 => wp_mov (op2_lsr (by decide)) fun u2 v2 =>
    wp_dp (op2_reg _ _) fun u3 v3 => wp_dp (op2_imm (by decide)) fun u4 v4 =>
      wp_mov (op2_lsr (by decide)) fun u5 v5 => wp_dp (op2_reg _ _) fun u6 v6 => wp_dp (op2_reg _ _) fun u7 v7 => ?_
  refine k u7 ((v1.rest (by simp)).trans ((v2.rest (by simp)).trans ((v3.rest (by simp)).trans ((v4.rest (by simp)).trans
    ((v5.rest (by simp)).trans ((v6.rest (by simp)).trans (v7.rest (by simp))))))))
    (by rw [v7.mem, v6.mem, v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]) ?_
  obtain ha' : a < 2 ^ 14 := by omega_arith
  obtain hs' : s < 2 ^ 14 := by omega_arith
  obtain b5 : u2.gpr .r5 = BitVec.ofNat 32 (b2n (decide (a = 0))) := by
    rw [v2.gpr, v1.gpr, dpVal, r2]
    apply BitVec.eq_of_toNat_eq
    rw [isZero_bit (by rw [ofNat_toNat_lt (by omega_arith)]; omega_arith), ofNat_toNat_lt (by omega_arith),
      ofNat_toNat_lt (by cases decide (a = 0) <;> decide)]
    by_cases h : a = 0 <;> simp [h, b2n]
  obtain b6 : u5.gpr .r6 = BitVec.ofNat 32 (b2n (decide (a = s))) := by
    rw [v5.gpr, v4.gpr, dpVal, v3.gpr, dpVal, v2.other _ (by decide), v1.other _ (by decide), r2,
      v2.other _ (by decide), v1.other _ (by decide), r3]
    obtain hx : (BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 s).toNat < 2 ^ 14 := by
      rw [BitVec.toNat_xor, ofNat_toNat_lt (by omega_arith), ofNat_toNat_lt (by omega_arith)]
      exact Nat.xor_lt_two_pow ha' hs'
    apply BitVec.eq_of_toNat_eq
    rw [isZero_bit (by omega_arith), ofNat_toNat_lt (by cases decide (a = s) <;> decide)]
    have : (BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 s).toNat = 0 ↔ a = s := by
      constructor
      · intro e
        obtain e' := congrArg BitVec.toNat (BitVec.xor_eq_zero_iff.mp (BitVec.eq_of_toNat_eq (by rw [e]; rfl)))
        rwa [ofNat_toNat_lt (by omega_arith), ofNat_toNat_lt (by omega_arith)] at e'
      · rintro rfl; simp
    by_cases h : a = s <;> simp [h, b2n] at this ⊢ <;> omega_arith
  obtain r11' : u6.gpr .r11 = BitVec.ofNat 32 (b2n f) := by
    rw [v6.other _ (by decide), v5.other _ (by decide), v4.other _ (by decide), v3.other _ (by decide),
      v2.other _ (by decide), v1.other _ (by decide), r11]
  obtain r5' : u5.gpr .r5 = BitVec.ofNat 32 (b2n (decide (a = 0))) := by
    rw [v5.other _ (by decide), v4.other _ (by decide), v3.other _ (by decide), b5]
  rw [v7.gpr, dpVal, r11', v6.gpr, dpVal, r5', b6]
  obtain e : decide (a = 0 ∨ a = s) = (decide (a = 0) || decide (a = s)) := by simp
  rw [e]
  generalize decide (a = 0) = x
  generalize decide (a = s) = y
  cases f <;> cases x <;> cases y <;> decide

/-- Trial division by the prime `s` in `r3`: `r11 |= s ∣ c`, for `c` the
`W − 2` words at the key array `aC`. -/
theorem trialPrime_ok {B : BitVec 32} {Z W : Nat} {m : Mem} {u : State} {s : Nat} {f : Bool} {rest : Prog isa}
    {Q : State → Prop} (hw : Ws u B Z W nArr) (hW : 3 ≤ W) (hWe : W % 2 = 0) (hZ : arr W aC + 4 * W ≤ Z)
    (mem : u.mem = m) (r3 : u.gpr .r3 = BitVec.ofNat 32 s) (hs : s % 2 = 1 ∧ 3 ≤ s ∧ s < 8162)
    (hinv : (s * (ninv (BitVec.ofNat 32 s)).toNat + 1) % 2 ^ 16 = 0) (r11 : u.gpr .r11 = BitVec.ofNat 32 (b2n f))
    (k : ∀ u', Rest [.r0, .r1, .r2, .r4, .r5, .r6, .r11] u u' → u'.mem = m →
      u'.gpr .r11 = BitVec.ofNat 32 (b2n (f || decide (val32 m (State.addr B) (arr W aC) (W - 2) % s = 0))) →
      WP isa rest u' Q) :
    WP isa (.block entryS) u fun u1 =>
      WP isa (.seq (.loop (.block trialWord) .ne) (.seq (.block trialFlag) rest)) u1 Q := by
  rw [← List.append_nil entryS]
  refine entryS_ok hw (by omega_arith) fun u1 k1 m1 hw1 e4 e0 e1 e2 => WP.block_nil ?_
  obtain r31 : u1.gpr .r3 = BitVec.ofNat 32 s := by rw [k1.gpr _ (by decide), r3]
  refine WP.seq (WP.mono (primeLoop_ok (u₀ := u1) ⟨hw1, m1.trans mem, Rest.refl _ _,
    by rw [Nat.mul_zero, Nat.add_zero]; exact e0, by rw [Nat.sub_zero]; exact e1,
    ⟨0, by rw [e2]; rfl, by omega_arith, by simp [val32]⟩⟩ hW hZ r31 ⟨hs.2.1, hs.2.2⟩
      (by rw [e4, r3]; exact hinv)) fun u2 h2 => ?_)
  obtain ⟨_, m2, k2, _, _, a, r2, ha, hc⟩ := h2
  refine WP.seq ?_
  rw [← List.append_nil trialFlag]
  refine trialFlag_ok r2 ha (by rw [k2.gpr _ (by decide), r31]) hs.2.2
    (by rw [k2.gpr _ (by decide), k1.gpr _ (by decide), r11]) fun u3 k3 m3 r113 => WP.block_nil ?_
  refine k u3 (((k1.trans (k2.mono (by simp))).mono (by simp)).trans (k3.mono (by simp))) (m3.trans m2) ?_
  rw [r113]
  obtain e64 : 32 * (W - 2) = 64 * ((W - 2) / 2) := by omega_arith
  rw [e64] at hc
  have := (VG.Proof.RsaKeyGen.trial_div hs.1 ha hc).symm
  rw [show decide (a = 0 ∨ a = s) = decide (val32 m (State.addr B) (arr W aC) (W - 2) % s = 0) from
    decide_eq_decide.mpr this]

end VG.Proof.Dsa.Arm.Prime

end

end

/-! ### `Dsa.Arm.Prime.Tab`, which only this module used -/

section

/-! # A candidate on ARMv7: the table of small primes written (`table_ok`)

`tabWrite a k` stores the words `a` to `a + k − 1` of the table, from a
`movw` and a `movt` each (`tabSteps_ok`); `table_ok`: the first 256 words,
and the other 256 for `w > 16`, over the key arrays 22–48 (`tabJs`), which
nothing else holds then.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Impl.RsaKeyGen VG.Proof.RsaKeyGen

/-- The arrays the table is written over. -/
def tabJs : List Nat := List.range' 22 27

/-- The table's words: 256, or 512 for `W ≥ 35` (`w > 16`). -/
def nT (W : Nat) : Nat := if 35 ≤ W then 512 else 256

theorem tabWord32_lo {j : Nat} (hj : j < 512) : tabWord32 j % 2 ^ 16 = tabEntry (2 * j) := by
  have := (tabEntry_facts (i := 2 * j) (by omega_arith)).2.2
  unfold tabWord32; omega_arith

theorem tabWord32_hi {j : Nat} (hj : j < 512) : tabWord32 j / 2 ^ 16 = tabEntry (2 * j + 1) := by
  have := (tabEntry_facts (i := 2 * j) (by omega_arith)).2.2
  unfold tabWord32; omega_arith

theorem tabWord32_lt {j : Nat} (hj : j < 512) : tabWord32 j < 2 ^ 32 := by
  have := (tabEntry_facts (i := 2 * j) (by omega_arith)).2.2
  have := (tabEntry_facts (i := 2 * j + 1) (by omega_arith)).2.2
  unfold tabWord32; omega_arith

theorem tab_movt {j : Nat} (hj : j < 512) :
    (BitVec.ofNat 16 (tabEntry (2 * j + 1)) ++
      ((BitVec.ofNat 16 (tabEntry (2 * j))).setWidth 32).extractLsb' 0 16 : BitVec 32) =
      BitVec.ofNat 32 (tabWord32 j) := by
  have e0 := (tabEntry_facts (i := 2 * j) (by omega_arith)).2.2
  have e1 := (tabEntry_facts (i := 2 * j + 1) (by omega_arith)).2.2
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_zero,
    ← Nat.shiftLeft_add_eq_or_of_lt (by omega_arith), Nat.shiftLeft_eq]
  unfold tabWord32
  omega_arith

theorem wp_movt' {s : State} {is : List Instr} {Q : State → Prop} {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm ++ (s.gpr d).extractLsb' 0 16 : BitVec 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movt d imm :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

/-- The words `a` to `a + k − 1` of the table, at offset `o` (in `r12`). -/
theorem tabSteps_ok {s : State} {B : BitVec 32} {Z W N : Nat} (hw : Ws s B Z W N) {o a : Nat}
    (r12 : s.gpr .r12 = B + BitVec.ofNat 32 o) :
    ∀ k, a + k ≤ 512 → o + 4 * (a + k) ≤ Z →
    WP isa (.block (tabWrite a k)) s fun s' =>
      (∀ j < k, w32 s'.mem (State.addr B) (o + 4 * (a + j)) = tabWord32 (a + j)) ∧ Rest [.r1] s s' ∧
      Outside (State.addr B) (o + 4 * a) (4 * k) s.mem s'.mem
  | 0, _, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Rest.refl _ _, Outside.refl _ _ _ _⟩
  | k + 1, hk, hz => by
    have hn := hw.nowrap
    rw [tabWrite, List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.append (tabSteps_ok hw r12 k (by omega_arith) (by omega_arith)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    simp only [tabStore]
    refine wp_movw fun s₂ u₂ => wp_movt' fun s₃ u₃ => ?_
    have k₃ : Rest [.r1] s s₃ := k₁.trans ((u₂.rest (by simp)).trans (u₃.rest (by simp)))
    have hw₃ := hw.rest k₃
    have ea : State.addr (s₃.gpr .r12 + BitVec.ofNat 32 (4 * (a + k))) =
        off (State.addr B) (o + 4 * (a + k)) := by
      rw [k₃.gpr _ (by decide), r12, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact hw.addr (by omega_arith)
    refine wp_str (by omega_arith) ea (hw₃.write (by omega_arith)) fun s₄ m₄ => WP.block_nil ?_
    have O₂ : Outside (State.addr B) (o + 4 * (a + k)) 4 s₁.mem s₄.mem := by
      rw [m₄.mem, u₃.mem, u₂.mem]; exact writeW32_outside _ _ _ (by omega_arith)
    refine ⟨fun j hj => ?_, k₃.trans (m₄.rest _),
      (O₁.mono (Nat.le_refl _) (by omega_arith)).trans (O₂.mono (by omega_arith) (by omega_arith))⟩
    rcases Nat.lt_or_ge j k with h | h
    · rw [O₂.w32 (by omega_arith) (by omega_arith), e₁ j h]
    · obtain rfl : j = k := by omega_arith
      rw [m₄.mem, u₃.mem, u₂.mem, w32_write_self, u₃.gpr, u₂.gpr, tab_movt (by omega_arith), BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (tabWord32_lt (by omega_arith))]

/-- Memory that changed only within the arrays `a` to `a + k − 1`. -/
theorem keep_span {B : BitVec 32} {w a k o n : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Outside (State.addr B) o n m m') (ho : arr w a ≤ o) (hn : o + n ≤ arr w (a + k))
    (hjs : ∀ j, a ≤ j → j < a + k → j ∈ js) : Keep B w js ds m m' := by
  intro x hx
  refine h x ?_
  by_contra hc
  have hS : 0 < S w := by simp only [S]; omega_arith
  have hlo : hdr ≤ ofs (State.addr B) x := by
    have : hdr ≤ arr w a := Nat.le_add_right _ _
    omega_arith
  obtain ⟨q, r, hr, hq⟩ : ∃ q r, r < S w ∧ ofs (State.addr B) x = hdr + q * S w + r :=
    ⟨(ofs (State.addr B) x - hdr) / S w, (ofs (State.addr B) x - hdr) % S w, Nat.mod_lt _ hS, by
      have := Nat.div_add_mod (ofs (State.addr B) x - hdr) (S w)
      rw [Nat.mul_comm] at this; omega_arith⟩
  have h1 : a * S w < (q + 1) * S w := by
    have : arr w a = hdr + a * S w := rfl
    rw [Nat.add_mul]; omega_arith
  have h2 : q * S w < (a + k) * S w := by
    have : arr w (a + k) = hdr + (a + k) * S w := rfl
    omega_arith
  have qa := Nat.lt_of_mul_lt_mul_right h1
  have qk := Nat.lt_of_mul_lt_mul_right h2
  have := hx (arr w q, S w) (by
    simp only [ranges, List.mem_append, List.mem_map]
    exact .inl ⟨q, hjs q (by omega_arith) qk, rfl⟩)
  simp only [arr] at this
  omega_arith

theorem tabJs_mem {j : Nat} (h1 : 22 ≤ j) (h2 : j < 22 + 27) : j ∈ tabJs := by
  simp only [tabJs, List.mem_range'_1]; omega_arith

theorem nT_le {W : Nat} (hw : 10 ≤ W) : aTab * 4 * (W + 2) + 4 * nT W ≤ 49 * (4 * (W + 2)) := by
  simp only [nT, aTab]; split <;> omega_arith

/-- The table: its first `nT W` words at the key array 22, written over the
arrays `tabJs`. -/
theorem table_ok {s : State} {B : BitVec 32} {Z W : Nat} (hw : Ws s B Z W nArr) (hW : 10 ≤ W) :
    WP isa (seqs table) s fun t => Ws t B Z W nArr ∧ Keep B W tabJs [] s.mem t.mem ∧
      (∀ j < nT W, w32 t.mem (State.addr B) (arr W aTab + 4 * j) = tabWord32 j) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hfit := hw.fits
  have hz : arr W aTab + 4 * nT W ≤ Z := by
    have := nT_le hW; simp only [arr, S, nArr, aTab] at *; omega_arith
  simp only [table, seqs]
  rw [List.append_assoc, List.append_assoc]
  refine WP.seq (ptr_ok hw (r := .r12) (by decide) (by decide) fun s1 p1 r1 m1 hw1 => ?_)
  refine WP.append (tabSteps_ok hw1 (o := arr W aTab) (a := 0) p1 256 (by decide)
    (by have := nT_le hW; simp only [nT] at hz; split at hz <;> omega_arith)) fun s2 ⟨e2, k2, O2⟩ => ?_
  have hw2 := hw1.rest k2
  -- `r1 := W ≥ 35`, and Z iff not.
  unfold bigW
  refine wp_subsC (op2_imm (by decide)) fun s3 u3 c3 => wp_movC (op2_imm (by decide)) fun s4 u4 c4 =>
    wp_adc (op2_imm (by decide)) fun s5 u5 => wp_cmp (op2_imm (by decide)) fun s6 f6 z6 => WP.block_nil ?_
  have k6 : Rest [.r1] s2 s6 := (u3.rest (by simp)).trans ((u4.rest (by simp)).trans ((u5.rest (by simp)).trans
    (f6.rest _)))
  have m6 : s6.mem = s2.mem := by rw [f6.mem, u5.mem, u4.mem, u3.mem]
  have hw6 := hw2.rest k6
  have r16 : (s5.gpr .r1).toNat = if 35 ≤ W then 1 else 0 := by
    rw [u5.gpr, u4.gpr, c4, c3, hw2.r9]
    have : W < 2 ^ 32 := by have := hw.wle; omega_arith
    have e : (BitVec.ofNat 32 W).toNat = W := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt this]
    by_cases h : 35 ≤ W <;> simp [h, e]
  have z6' : s6.z = decide (W < 35) := by
    rw [z6]
    by_cases h : 35 ≤ W
    · have : s5.gpr .r1 = 1 := BitVec.eq_of_toNat_eq (by rw [r16]; simp [h])
      rw [this]; simp; omega_arith
    · have : s5.gpr .r1 = 0 := BitVec.eq_of_toNat_eq (by rw [r16]; simp [h])
      rw [this]; simp; omega_arith
  have O0 : Outside (State.addr B) (arr W aTab) (4 * 256) s.mem s6.mem := by rw [m6, ← m1]; simpa using O2
  have sp6 : s6.sp = s.sp ∧ s6.rd = s.rd ∧ s6.wr = s.wr :=
    ⟨by rw [k6.sp, k2.sp, r1.sp], by rw [k6.rd, k2.rd, r1.rd], by rw [k6.wr, k2.wr, r1.wr]⟩
  refine WP.ite (s6.z) rfl (fun hz6 => ?_) (fun hz6 => ?_)
  · -- `W < 35`: the first 256 words alone.
    have hW' : ¬ 35 ≤ W := by
      intro h; rw [z6'] at hz6; simp at hz6; omega_arith
    refine WP.block_nil ⟨hw6, keep_span (a := aTab) (k := 27) O0 (Nat.le_refl _) ?_ fun j h1 h2 => tabJs_mem h1 h2,
      fun j hj => ?_, sp6⟩
    · have := nT_le hW; simp only [nT, hW', ↓reduceIte, arr, S, aTab] at *; omega_arith
    · simp only [nT, hW', ↓reduceIte] at hj
      rw [m6]; simpa using e2 j hj
  · -- `W ≥ 35`: the other 256 words too.
    have hW' : 35 ≤ W := by
      rw [z6'] at hz6; simp at hz6; omega_arith
    have hz' : arr W aTab + 4 * 512 ≤ Z := by simpa [nT, hW'] using hz
    have := hw.nowrap
    refine ptr_ok hw6 (r := .r12) (by decide) (by decide) (rest := tabWrite 256 256)
      fun s7 p7 r7 m7 hw7 => ?_
    rw [← List.append_nil (tabWrite 256 256)]
    refine WP.append (tabSteps_ok hw7 (o := arr W aTab) (a := 256) p7 256 (by decide)
      (by simp only [nT, hW', ↓reduceIte] at hz; omega_arith)) fun s8 ⟨e8, k8, O8⟩ => WP.block_nil ?_
    have O1 : Outside (State.addr B) (arr W aTab) (4 * 512) s.mem s8.mem :=
      (O0.mono (Nat.le_refl _) (by omega_arith)).trans (by rw [m7] at O8; exact O8.mono (by omega_arith) (by omega_arith))
    refine ⟨hw7.rest k8, keep_span (a := aTab) (k := 27) O1 (Nat.le_refl _) ?_ fun j h1 h2 => tabJs_mem h1 h2,
      fun j hj => ?_, ⟨by rw [k8.sp, r7.sp, sp6.1], by rw [k8.rd, r7.rd, sp6.2.1], by rw [k8.wr, r7.wr, sp6.2.2]⟩⟩
    · simp only [arr, S, aTab]; omega_arith
    · simp only [nT, hW', ↓reduceIte] at hj
      rcases Nat.lt_or_ge j 256 with h | h
      · rw [O8.w32 (by omega_arith) (by omega_arith), m7, m6]; simpa using e2 j h
      · have := e8 (j - 256) (by omega_arith)
        rwa [show 256 + (j - 256) = j by omega_arith] at this

end VG.Proof.Dsa.Arm.Prime

end

end

/-! # A candidate on ARMv7: trial division by the table (`trialLoop_ok`)

`TO … k`: after `k` words of the table (`2 k` primes), `r11` holds whether
one of them divides `c` (`tr`), `r12` points at word `k` and `lr` counts the
words left.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Impl.RsaKeyGen VG.Proof.RsaKeyGen
open VG.Proof.Rsa (b2n)

/-- Whether one of the first `n` entries of the table divides `c`. -/
def tr (n c : Nat) : Bool := (List.range n).any fun i => c % tabEntry i == 0

theorem tr_succ (n c : Nat) : tr (n + 1) c = (tr n c || decide (c % tabEntry n = 0)) := by
  simp only [tr, List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false]
  congr 1

theorem trialStep_eq : trialStep =
    .seq (.block [.ldr .r10 .r12 0, .dp .add .r12 .r12 (.imm 4)])
      (.seq (.block (([.mov .r3 (.shifted .r10 .lsl 16), .mov .r3 (.shifted .r3 .lsr 16)] : List Instr) ++ entryS))
        (.seq (.loop (.block trialWord) .ne) (.seq (.block trialFlag)
          (.seq (.block (([.mov .r3 (.shifted .r10 .lsr 16)] : List Instr) ++ entryS))
            (.seq (.loop (.block trialWord) .ne) (.seq (.block trialFlag) (.block [.subs .lr .lr (.imm 1)]))))))) :=
  rfl

/-- After `k` words of the table in `m`, for `c` the `W − 2` words at the key
array `aC`. -/
structure TO (B : BitVec 32) (Z W : Nat) (m : Mem) (u₀ : State) (k : Nat) (u : State) : Prop where
  ws : Ws u B Z W nArr
  mem : u.mem = m
  rest : Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r10, .r11, .r12, .lr] u₀ u
  r12 : u.gpr .r12 = B + BitVec.ofNat 32 (arr W aTab + 4 * k)
  lr : u.gpr .lr = BitVec.ofNat 32 (nT W - k)
  r11 : u.gpr .r11 = BitVec.ofNat 32 (b2n (tr (2 * k) (val32 m (State.addr B) (arr W aC) (W - 2))))

theorem w32_ofNat {m : Mem} {a : Addr} {x : Nat} (h : (m.readW a 32).toNat = x) : m.readW a 32 = BitVec.ofNat 32 x :=
  BitVec.eq_of_toNat_eq (by rw [h, BitVec.toNat_ofNat, ← h, Nat.mod_eq_of_lt (m.readW a 32).isLt])

/-- Word `k` of the table: its two primes. -/
theorem trialStep_ok {B : BitVec 32} {Z W : Nat} {m : Mem} {u₀ u : State} {k : Nat}
    (h : TO B Z W m u₀ k u) (hk : k < nT W) (hW : 10 ≤ W) (hWe : W % 2 = 0) (hZ : arr W nArr ≤ Z)
    (tab : ∀ j < nT W, w32 m (State.addr B) (arr W aTab + 4 * j) = tabWord32 j) :
    WP isa trialStep u fun u' => TO B Z W m u₀ (k + 1) u' ∧ u'.z = decide (nT W - (k + 1) = 0) := by
  obtain ⟨hw, mem, rest, r12, lr, r11⟩ := h
  have hn := hw.nowrap
  have hWl := hw.wle
  obtain hk512 : k < 512 := by simp only [nT] at hk; split at hk <;> omega_arith
  obtain hz : arr W aTab + 4 * nT W ≤ Z := by
    have := nT_le hW; simp only [arr, S, nArr, aTab] at *; omega_arith
  obtain hzc : arr W aC + 4 * W ≤ Z := by simp only [arr, S, nArr, aC] at *; omega_arith
  set c := val32 m (State.addr B) (arr W aC) (W - 2) with ec
  obtain ea : State.addr (u.gpr .r12 + BitVec.ofNat 32 0) = off (State.addr B) (arr W aTab + 4 * k) := by
    rw [r12, BitVec.add_assoc, ← BitVec.ofNat_add]; exact hw.addr (by omega_arith)
  obtain rd : InRegions (u.rd ++ u.wr) (off (State.addr B) (arr W aTab + 4 * k)) 4 := hw.read (by omega_arith)
  obtain tk : u.mem.readW (off (State.addr B) (arr W aTab + 4 * k)) 32 = BitVec.ofNat 32 (tabWord32 k) :=
    w32_ofNat (by rw [mem]; exact tab k hk)
  obtain e0 := tabEntry_facts (i := 2 * k) (by omega_arith)
  obtain e1 := tabEntry_facts (i := 2 * k + 1) (by omega_arith)
  rw [trialStep_eq]
  refine WP.seq (wp_ldr (by decide) ea rd fun u1 v1 => wp_dp (op2_imm (by decide)) fun u2 v2 => WP.block_nil ?_)
  obtain k2 : Rest [.r10, .r12] u u2 := (v1.rest (by simp)).trans (v2.rest (by simp))
  obtain r10 : u2.gpr .r10 = BitVec.ofNat 32 (tabWord32 k) := by rw [v2.other _ (by decide), v1.gpr, tk]
  obtain r12' : u2.gpr .r12 = B + BitVec.ofNat 32 (arr W aTab + 4 * (k + 1)) := by
    rw [v2.gpr, dpVal, v1.other _ (by decide), r12, BitVec.add_assoc, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl,
      ← BitVec.ofNat_add]
    congr 2
  obtain hw2 := hw.rest k2
  -- The first prime.
  refine WP.seq ?_
  refine WP.block_append (wp_mov (op2_lsl (by decide)) fun u3 v3 => wp_mov (op2_lsr (by decide)) fun u4 v4 =>
    WP.block_nil ?_)
  obtain k4 : Rest [.r3] u2 u4 := (v3.rest (by simp)).trans (v4.rest (by simp))
  obtain r34 : u4.gpr .r3 = BitVec.ofNat 32 (tabEntry (2 * k)) := by
    apply BitVec.eq_of_toNat_eq
    rw [v4.gpr, v3.gpr, lo16, r10, ofNat_toNat_lt (tabWord32_lt hk512), tabWord32_lo hk512,
      ofNat_toNat_lt (by omega_arith)]
  refine trialPrime_ok (f := tr (2 * k) c) (hw2.rest k4) (by omega_arith) hWe hzc (by rw [v4.mem, v3.mem, v2.mem, v1.mem, mem]) r34
    ⟨e0.1, e0.2.1, e0.2.2⟩ (ninv_tab (by omega_arith)) (by rw [k4.gpr _ (by decide), k2.gpr _ (by decide), r11])
    fun u5 k5 m5 r115 => ?_
  -- The second prime.
  refine WP.seq ?_
  refine WP.block_append (wp_mov (op2_lsr (by decide)) fun u6 v6 => WP.block_nil ?_)
  obtain k6 : Rest [.r3] u5 u6 := v6.rest (by simp)
  obtain r36 : u6.gpr .r3 = BitVec.ofNat 32 (tabEntry (2 * k + 1)) := by
    apply BitVec.eq_of_toNat_eq
    rw [v6.gpr, hi16, k5.gpr _ (by decide), k4.gpr _ (by decide), r10, ofNat_toNat_lt (tabWord32_lt hk512),
      tabWord32_hi hk512, ofNat_toNat_lt (by omega_arith)]
  obtain hw5 : Ws u5 B Z W nArr := (hw2.rest k4).rest k5
  refine trialPrime_ok (f := tr (2 * k) c || decide (c % tabEntry (2 * k) = 0)) (hw5.rest k6) (by omega_arith) hWe hzc
    (by rw [v6.mem, m5]) r36 ⟨e1.1, e1.2.1, e1.2.2⟩ (ninv_tab (by omega_arith)) (by rw [k6.gpr _ (by decide), r115])
    fun u7 k7 m7 r117 => ?_
  -- The count.
  refine wp_subs (op2_imm (by decide)) fun u8 v8 z8 => WP.block_nil ?_
  obtain kall : Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r10, .r11, .r12, .lr] u u8 :=
    (k2.mono (by simp)).trans ((k4.mono (by simp)).trans ((k5.mono (by simp)).trans ((k6.mono (by simp)).trans
      ((k7.mono (by simp)).trans (v8.rest (by simp))))))
  obtain lr8 : u8.gpr .lr = BitVec.ofNat 32 (nT W - (k + 1)) := by
    rw [v8.gpr, k7.gpr _ (by decide), k6.gpr _ (by decide), k5.gpr _ (by decide), k4.gpr _ (by decide),
      k2.gpr _ (by decide), lr]
    apply BitVec.eq_of_toNat_eq
    have : nT W ≤ 512 := by simp only [nT]; split <;> omega_arith
    rw [BitVec.toNat_sub, ofNat_toNat_lt (by omega_arith), ofNat_toNat_lt (by omega_arith)]
    simp only [show (1 : BitVec 32).toNat = 1 from rfl]
    omega_arith
  refine ⟨⟨hw.rest kall, by rw [v8.mem, m7], rest.trans kall, ?_, lr8, ?_⟩, ?_⟩
  · rw [v8.other _ (by decide), k7.gpr _ (by decide), k6.gpr _ (by decide), k5.gpr _ (by decide),
      k4.gpr _ (by decide), r12']
  · rw [v8.other _ (by decide), r117, show 2 * (k + 1) = 2 * k + 1 + 1 by omega_arith, tr_succ, tr_succ]
  · rw [z8, ← v8.gpr, lr8]
    have : nT W ≤ 512 := by simp only [nT]; split <;> omega_arith
    by_cases h0 : nT W - (k + 1) = 0
    · simp [h0]
    · have : (BitVec.ofNat 32 (nT W - (k + 1))) ≠ 0 := fun e => h0 (by
        have := congrArg BitVec.toNat e; rw [ofNat_toNat_lt (by omega_arith)] at this; simpa using this)
      simpa [h0] using this

/-- All the words of the table. -/
theorem trialLoop_ok {B : BitVec 32} {Z W : Nat} {m : Mem} {u₀ u : State}
    (h : TO B Z W m u₀ 0 u) (hW : 10 ≤ W) (hWe : W % 2 = 0) (hZ : arr W nArr ≤ Z)
    (tab : ∀ j < nT W, w32 m (State.addr B) (arr W aTab + 4 * j) = tabWord32 j) :
    WP isa (.loop trialStep .ne) u (TO B Z W m u₀ (nT W)) := by
  obtain hT : 0 < nT W := by simp only [nT]; split <;> omega_arith
  refine WP.loop (M := isa) (fun n v => 0 < n ∧ n ≤ nT W ∧ TO B Z W m u₀ (nT W - n) v)
    (fun n v ⟨hn, hn2, hu⟩ => ?_) (nT W) u ⟨hT, Nat.le_refl _, by rw [Nat.sub_self]; exact h⟩
  refine WP.mono (trialStep_ok hu (by omega_arith) hW hWe hZ tab) fun u' ⟨hu', z⟩ => ?_
  rw [isa_ne, z]
  by_cases h0 : n = 1
  · subst h0
    refine .inl ⟨by simp; omega_arith, ?_⟩
    rwa [show nT W - 1 + 1 = nT W by omega_arith] at hu'
  · refine .inr ⟨by simp; omega_arith, n - 1, by omega_arith, by omega_arith, by omega_arith, ?_⟩
    rwa [show nT W - n + 1 = nT W - (n - 1) by omega_arith] at hu'

end VG.Proof.Dsa.Arm.Prime
