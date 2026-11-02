module

public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Impl.Bignum.RISCV64.Precompute
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The precomputed values of an RSA modulus on RISC-V: the check

`check_ok`: `check` leaves 0 in `s0` iff the `k` bytes at `N` make a valid
modulus (`Spec.Rsa.modulusValid`), for `64 ≤ k ≤ 1024`.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum.RISCV64
  VG.Impl.Bignum.RISCV64.Precompute

theorem read_byte64 (m : Mem) (a : Addr) : (m.read a 1).setWidth 64 = BitVec.ofNat 64 (m a).toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (m.read a 1).isLt (by decide)),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans (m a).isLt (by decide))]
  show (m.read (a + 1) 0 ++ m a).toNat = (m a).toNat
  rw [BitVec.toNat_append]
  simp [Mem.read]

theorem odd_xor (x : Nat) :
    BitVec.ofNat 64 x &&& 1#64 ^^^ 1#64 = 0 ↔ x % 2 = 1 := by
  have e : BitVec.ofNat 64 x &&& 1#64 = BitVec.ofNat 64 (x % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (1#64).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    simp only [BitVec.toNat_ofNat]
    omega_arith
  rw [e]
  rcases (show x % 2 = 0 ∨ x % 2 = 1 by omega_arith) with h | h <;> rw [h] <;> decide

theorem top_xor {x : Nat} (hx : x < 256) : BitVec.ofNat 64 x >>> 7 ^^^ 1#64 = 0 ↔ 128 ≤ x := by
  have e : BitVec.ofNat 64 x >>> 7 = BitVec.ofNat 64 (x / 128) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  rw [e]
  rcases (show x / 128 = 0 ∨ x / 128 = 1 by omega_arith) with h | h
  · rw [h]; constructor <;> intro h' <;> first | (exact absurd h' (by decide)) | omega_arith
  · rw [h]; constructor <;> intro <;> first | decide | omega_arith

theorem check1_ok {s : State} {N : Addr} {k : Nat} {nb : List Byte}
    (h7 : s.gpr .s7 = off N 0) (h8 : s.gpr .s8 = BitVec.ofNat 64 k) (hk : 64 ≤ k)
    (hlen : nb.length = k)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off N i) 1)
    (hb : ∀ i (h : i < k), s.mem (off N i) = nb[i]'(by omega_arith)) :
    WP isa (.block check1) s fun t =>
      ((t.gpr .s0 = 0 ↔ (nb[k - 1]'(by omega_arith)).toNat % 2 = 1) ∧
        t.gpr .t4 = BitVec.ofNat 64 (nb[0]'(by omega_arith)).toNat ∧ t.mem = s.mem) ∧
        Keep [.s0, .t4] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold check1
  have r0 := hrd 0 (by omega_arith)
  have rl := hrd (k - 1) (by omega_arith)
  have b0 := hb 0 (by omega_arith)
  have bl := hb (k - 1) (by omega_arith)
  brun [h7, h8, Nat.zero_add, off_sub N (show 1 ≤ k by omega_arith), r0, rl, read_byte64, b0, bl,
    exec_logicImm, BitVec.ofInt_ofNat]
  exact odd_xor _

theorem check2_ok {s : State} {k : Nat} {nb : List Byte}
    (h8 : s.gpr .s8 = BitVec.ofNat 64 k) (hk : 64 ≤ k) (hk' : k ≤ 1024) (hlen : nb.length = k)
    (i0 : s.gpr .s0 = 0 ↔ (nb[k - 1]'(by omega_arith)).toNat % 2 = 1)
    (i4 : s.gpr .t4 = BitVec.ofNat 64 (nb[0]'(by omega_arith)).toNat) :
    WP isa check2 s fun t =>
      (t.gpr .s0 = 0 ↔ Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) ∧ t.mem = s.mem ∧
        Keep [.s0, .t4, .t5] s t := by
  have hB0 := (nb[0]'(by omega_arith)).isLt
  have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true ↔ (1 ≤ (nb[0]'(by omega_arith)).toNat ∧
      (nb[k - 1]'(by omega_arith)).toNat % 2 = 1 ∧ 128 ≤ (k - 64) * 256 + (nb[0]'(by omega_arith)).toNat) := by
    rw [VG.Proof.Bignum.modulusValid_iff hlen hk hk']
    simp only [Bool.not_or, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt]
    omega_arith
  have hrest : ∀ t₂ : State, (t₂.gpr .s0 = 0 ↔ 1 ≤ (nb[0]'(by omega_arith)).toNat ∧
      (nb[k - 1]'(by omega_arith)).toNat % 2 = 1) → t₂.gpr .t4 = BitVec.ofNat 64 (nb[0]'(by omega_arith)).toNat →
      t₂.mem = s.mem → Keep [.s0, .t4] s t₂ →
      WP isa (.seq (.block [.addi .t5 .s8 (-64)])
        (.ite (.zero .t5) (.block [.shift .srl .d .t4 .t4 7, .logicImm .xor .t4 .t4 1,
          .logic .or .s0 .s0 .t4]) (.block []))) t₂ fun t =>
        (t.gpr .s0 = 0 ↔ Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) ∧ t.mem = s.mem ∧
          Keep [.s0, .t4, .t5] s t := by
    intro t₂ j0 j4 jm k₂
    refine WP.seq (WP.mono (WP.keep [.t5] (Q := fun t => t.gpr .t5 = BitVec.ofNat 64 (k - 64) ∧
      t.mem = t₂.mem) (by brun [k₂.gpr (r := .s8) (by decide), h8, Offset.ofNat_sub_ofNat hk]) (by rfl) (by rfl))
      fun t₃ ⟨⟨l5, lm⟩, k₃⟩ => ?_)
    have k23 := k₂.trans k₃
    refine WP.ite _ (Steps.eval_zero_ofNat _ _ (by omega_arith) l5) (fun hz => ?_) (fun hz => ?_)
    · refine WP.mono (WP.keep [.s0, .t4] (Q := fun t =>
        t.gpr .s0 = t₃.gpr .s0 ||| (BitVec.ofNat 64 (nb[0]'(by omega_arith)).toNat >>> 7 ^^^ 1#64) ∧
          t.mem = t₃.mem) (by brun [k₃.gpr (r := .t4) (by decide), j4, exec_logicImm, BitVec.ofInt_ofNat])
        (by rfl) (by rfl)) fun t ⟨⟨m0, mm⟩, k₄⟩ => ⟨?_, by rw [mm, lm, jm], (k23.trans k₄).mono (by decide)⟩
      rw [m0, show ∀ a b : BitVec 64, (a ||| b = 0 ↔ a = 0 ∧ b = 0) from fun _ _ => BitVec.or_eq_zero_iff,
        k₃.gpr (r := .s0) (by decide), j0, top_xor hB0, hv]
      have : k = 64 := by simp at hz; omega_arith
      subst this
      constructor <;> intro h <;> omega_arith
    · refine WP.block_nil ⟨?_, by rw [lm, jm], k23.mono (by decide)⟩
      rw [k₃.gpr (r := .s0) (by decide), j0, hv]
      have : k ≠ 64 := by simp at hz; omega_arith
      constructor <;> intro h <;> omega_arith
  unfold check2
  refine WP.seq (WP.ite _ (Steps.eval_zero_ofNat _ _ (by omega_arith) i4) (fun hz => ?_) (fun hz => ?_))
  · refine WP.mono (WP.keep [.s0] (Q := fun t => t.gpr .s0 = 1 ∧ t.mem = s.mem)
      (by brun [exec_li]; rfl) (by rfl) (by rfl))
      fun t₂ ⟨⟨m0, mm⟩, k₂⟩ => hrest t₂ ?_ (by rw [k₂.gpr (r := .t4) (by decide), i4]) mm (k₂.mono (by decide))
    have : (nb[0]'(by omega_arith)).toNat = 0 := by simpa using hz
    rw [m0, this]
    exact ⟨fun h => absurd h (by decide), fun h => absurd h.1 (by omega_arith)⟩
  · refine WP.block_nil (hrest s ?_ i4 rfl (Keep.refl _ _))
    have : (nb[0]'(by omega_arith)).toNat ≠ 0 := by simpa using hz
    rw [i0]; omega_arith

theorem check_ok {s : State} {N : Addr} {k : Nat} {nb : List Byte}
    (h7 : s.gpr .s7 = off N 0) (h8 : s.gpr .s8 = BitVec.ofNat 64 k) (hk : 64 ≤ k) (hk' : k ≤ 1024)
    (hlen : nb.length = k)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off N i) 1)
    (hb : ∀ i (h : i < k), s.mem (off N i) = nb[i]'(by omega_arith)) :
    WP isa check s fun t =>
      (t.gpr .s0 = 0 ↔ Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) ∧ t.mem = s.mem ∧
        Keep [.s0, .t4, .t5] s t := by
  unfold check
  refine WP.seq (WP.mono (check1_ok h7 h8 hk hlen hrd hb) fun t₁ ⟨⟨i0, i4, im⟩, k₁⟩ => ?_)
  refine WP.mono (check2_ok ((k₁.gpr (r := .s8) (by decide)).trans h8) hk hk' hlen i0 i4)
    fun t ⟨a, b, c⟩ => ⟨a, b.trans im, (k₁.trans c).mono (by decide)⟩

end VG.Proof.Bignum.RISCV64
