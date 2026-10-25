module
public import VerifiedGarbage.Impl.RsaKeyGen.Arm.Candidate
public import VerifiedGarbage.Proof.Rsa.Arm.KeyWs
public import VerifiedGarbage.Proof.Rsa.RecoverExp
public import VerifiedGarbage.Proof.RsaKeyGen.Trial16
import VerifiedGarbage.Proof.Bignum.Arm.TrialDivision16

import VerifiedGarbage.Proof.RsaKeyGen.TrialMath
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Instr
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.NeZero
import Mathlib.Tactic.Set
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-! # A candidate on ARMv7: trial division by one prime (`prime_ok`)

For the prime `s` in `r3`: `−s⁻¹ mod 2^16` by Newton's iteration
(`entryS_ok`), the Montgomery reduction of `c`'s 16-bit halves
(`redc_ok`, a word at a time: `trialWord_ok`, all of them: `primeLoop_ok`),
and `r11 |= s ∣ c` (`trialFlag_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
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
  have k8 : Rest [.r0, .r1, .r2, .r4, .r5, .r6] u u8 :=
    (v1.rest (by simp)).trans ((k2.mono (by simp)).trans ((k3.mono (by simp)).trans ((k4.mono (by simp)).trans
      ((v5.rest (by simp)).trans ((v6.rest (by simp)).trans ((v7.rest (by simp)).trans (v8.rest (by simp))))))))
  have m8 : u8.mem = u.mem := by rw [v8.mem, v7.mem, v6.mem, v5.mem, m4, m3, m2, v1.mem]
  have hw8 := hw.rest k8
  have r3 : ∀ x : State, Rest [.r0, .r1, .r2, .r4, .r5, .r6] u x → x.gpr .r3 = u.gpr .r3 :=
    fun x h => h.gpr _ (by decide)
  have e8 : u8.gpr .r4 = ninv (u.gpr .r3) := by
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
  have ea : State.addr (u.gpr .r0 + BitVec.ofNat 32 0) = off (State.addr B) (arr W aC + 4 * j) := by
    rw [r0, BitVec.add_assoc, ← BitVec.ofNat_add]; exact hw.addr (by omega_arith)
  have rd : InRegions (u.rd ++ u.wr) (off (State.addr B) (arr W aC + 4 * j)) 4 := hw.read (by omega_arith)
  have r3u : u.gpr .r3 = BitVec.ofNat 32 s := by rw [rest.gpr _ (by decide), r3]
  have r4u : (u.gpr .r4).toNat = (u₀.gpr .r4).toNat := by rw [rest.gpr _ (by decide)]
  set x := w32 m (State.addr B) (arr W aC + 4 * j) with ex
  have rx : (u.mem.readW (off (State.addr B) (arr W aC + 4 * j)) 32).toNat = x := by rw [mem]
  simp only [trialWord, List.cons_append, List.append_assoc]
  refine wp_ldr (by decide) ea rd fun u1 v1 => wp_mov (op2_lsl (by decide)) fun u2 v2 =>
    wp_mov (op2_lsr (by decide)) fun u3 v3 => ?_
  have h3 : (u3.gpr .r5).toNat = x % 2 ^ 16 := by rw [v3.gpr, v2.gpr, lo16, v1.gpr, rx]
  have k3 : Rest [.r5] u u3 := (v1.rest (by simp)).trans ((v2.rest (by simp)).trans (v3.rest (by simp)))
  have m3 : u3.mem = u.mem := by rw [v3.mem, v2.mem, v1.mem]
  refine redc_ok h3 (Nat.mod_lt _ (by decide)) (by rw [k3.gpr _ (by decide), r2]) ha
    (by rw [k3.gpr _ (by decide), r4u]) (by rw [k3.gpr _ (by decide), r3u]) hs hinv
    fun u4 k4 m4 a1 ha1 hc1 r24 => ?_
  simp only [List.nil_append]
  have ea4 : State.addr (u4.gpr .r0 + BitVec.ofNat 32 0) = off (State.addr B) (arr W aC + 4 * j) := by
    rw [k4.gpr _ (by decide), k3.gpr _ (by decide)]; exact ea
  have rd4 : InRegions (u4.rd ++ u4.wr) (off (State.addr B) (arr W aC + 4 * j)) 4 := by
    rw [k4.rd, k4.wr, k3.rd, k3.wr]; exact rd
  refine wp_ldr (by decide) ea4 rd4 fun u5 v5 => wp_mov (op2_lsr (by decide)) fun u6 v6 => ?_
  have h6 : (u6.gpr .r5).toNat = x / 2 ^ 16 := by rw [v6.gpr, hi16, v5.gpr, m4, m3, rx]
  have k6 : Rest [.r5] u4 u6 := (v5.rest (by simp)).trans (v6.rest (by simp))
  have hx : x < 2 ^ 32 := (m.readW _ 32).isLt
  refine redc_ok h6 (by omega_arith) (by rw [k6.gpr _ (by decide), r24]) ha1
    (by rw [k6.gpr _ (by decide), k4.gpr _ (by decide), k3.gpr _ (by decide), r4u])
    (by rw [k6.gpr _ (by decide), k4.gpr _ (by decide), k3.gpr _ (by decide), r3u]) hs hinv
    fun u7 k7 m7 a2 ha2 hc2 r27 => ?_
  refine wp_dp (op2_imm (by decide)) fun u8 v8 => wp_subs (op2_imm (by decide)) fun u9 v9 z9 => WP.block_nil ?_
  have kall : Rest [.r0, .r1, .r2, .r5, .r6] u u9 :=
    ((k3.mono (by simp)).trans ((k4.mono (by simp)).trans ((k6.mono (by simp)).trans ((k7.mono (by simp)).trans
      ((v8.rest (by simp)).trans (v9.rest (by simp)))))))
  have m9 : u9.mem = m := by rw [v9.mem, v8.mem, m7, v6.mem, v5.mem, m4, m3, mem]
  have r1v : u9.gpr .r1 = BitVec.ofNat 32 (W - 2 - (j + 1)) := by
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
  have ha' : a < 2 ^ 14 := by omega_arith
  have hs' : s < 2 ^ 14 := by omega_arith
  have b5 : u2.gpr .r5 = BitVec.ofNat 32 (b2n (decide (a = 0))) := by
    rw [v2.gpr, v1.gpr, dpVal, r2]
    apply BitVec.eq_of_toNat_eq
    rw [isZero_bit (by rw [ofNat_toNat_lt (by omega_arith)]; omega_arith), ofNat_toNat_lt (by omega_arith),
      ofNat_toNat_lt (by cases decide (a = 0) <;> decide)]
    by_cases h : a = 0 <;> simp [h, b2n]
  have b6 : u5.gpr .r6 = BitVec.ofNat 32 (b2n (decide (a = s))) := by
    rw [v5.gpr, v4.gpr, dpVal, v3.gpr, dpVal, v2.other _ (by decide), v1.other _ (by decide), r2,
      v2.other _ (by decide), v1.other _ (by decide), r3]
    have hx : (BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 s).toNat < 2 ^ 14 := by
      rw [BitVec.toNat_xor, ofNat_toNat_lt (by omega_arith), ofNat_toNat_lt (by omega_arith)]
      exact Nat.xor_lt_two_pow ha' hs'
    apply BitVec.eq_of_toNat_eq
    rw [isZero_bit (by omega_arith), ofNat_toNat_lt (by cases decide (a = s) <;> decide)]
    have : (BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 s).toNat = 0 ↔ a = s := by
      constructor
      · intro e
        have e' := congrArg BitVec.toNat (BitVec.xor_eq_zero_iff.mp (BitVec.eq_of_toNat_eq (by rw [e]; rfl)))
        rwa [ofNat_toNat_lt (by omega_arith), ofNat_toNat_lt (by omega_arith)] at e'
      · rintro rfl; simp
    by_cases h : a = s <;> simp [h, b2n] at this ⊢ <;> omega_arith
  have r11' : u6.gpr .r11 = BitVec.ofNat 32 (b2n f) := by
    rw [v6.other _ (by decide), v5.other _ (by decide), v4.other _ (by decide), v3.other _ (by decide),
      v2.other _ (by decide), v1.other _ (by decide), r11]
  have r5' : u5.gpr .r5 = BitVec.ofNat 32 (b2n (decide (a = 0))) := by
    rw [v5.other _ (by decide), v4.other _ (by decide), v3.other _ (by decide), b5]
  rw [v7.gpr, dpVal, r11', v6.gpr, dpVal, r5', b6]
  have e : decide (a = 0 ∨ a = s) = (decide (a = 0) || decide (a = s)) := by simp
  rw [e]
  generalize decide (a = 0) = x
  generalize decide (a = s) = y
  cases f <;> cases x <;> cases y <;> decide

/-- Trial division by the prime `s` in `r3`: `r11 |= s ∣ c`, for `c` the
`W − 2` words at the key array `aC`. -/
theorem prime_ok {B : BitVec 32} {Z W : Nat} {m : Mem} {u : State} {s : Nat} {f : Bool} {rest : Prog isa}
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
  have r31 : u1.gpr .r3 = BitVec.ofNat 32 s := by rw [k1.gpr _ (by decide), r3]
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
  have e64 : 32 * (W - 2) = 64 * ((W - 2) / 2) := by omega_arith
  rw [e64] at hc
  have := (VG.Proof.RsaKeyGen.trial_div hs.1 ha hc).symm
  rw [show decide (a = 0 ∨ a = s) = decide (val32 m (State.addr B) (arr W aC) (W - 2) % s = 0) from
    decide_eq_decide.mpr this]

end VG.Proof.RsaKeyGen.Arm.Cand
