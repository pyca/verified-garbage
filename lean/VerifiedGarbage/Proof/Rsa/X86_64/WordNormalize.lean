module

public import VerifiedGarbage.Proof.Rsa.X86_64.WordSetup
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Bignum.X86_64.R2wDiv
import VerifiedGarbage.Proof.Bignum.X86_64.R2
import VerifiedGarbage.Proof.Bignum.X86_64.Row

/-! # Normalizing the private CRT divisor without a secret branch -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.WordDivide

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.WordDivide
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- Setting the high bit ensures the normalized quotient estimator's premise. -/
theorem high_or (x : BitVec 64) : 2 ^ 63 ≤ (x ||| BitVec.ofNat 64 (2 ^ 63)).toNat := by
  rw [BitVec.toNat_or, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide)]
  exact Nat.right_le_or

/-- A valid full-width factor already has the bit set. -/
theorem high_or_self (x : BitVec 64) (h : 2 ^ 63 ≤ x.toNat) : x ||| BitVec.ofNat 64 (2 ^ 63) = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide)]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_two_pow]
  by_cases hi : 63 = i
  · subst i
    have ht := Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt h x.isLt
    simp only [ht, decide_true, Bool.or_true]
  · simp only [hi, decide_false, Bool.or_false]

theorem normalize_ok {s : State} {B : Addr} {Z W : Nat} (h : Ws s B Z W) (hW : 4 ≤ W) :
    WP isa (.block normalize) s fun t =>
      t.mem = s.mem.writeW (off B (slot W aM + 8 * (W / 2 - 1)))
        (word s.mem B (slot W aM + 8 * (W / 2 - 1)) ||| BitVec.ofNat 64 (2 ^ 63)) ∧ Keep mmRegs s t := by
  have hw := h.w2
  have hM := h.sl (j := aM) (by decide)
  rw [show normalize = ws ++ (base aM .r10 ++
    [.shift .shr .r12 1, .mov .rax (.mem (ix .r10 .r12 (-8))),
      .movImm64 .rdx 9223372036854775808, .alu .or .rax (.reg .rdx), .store (ix .r10 .r12 (-8)) .rax]) by
      simp only [normalize, List.append_assoc], WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok aM (r := .r10) (by decide) ((k₁.gpr (by decide)).trans h.rdi) h9)
    fun s₂ ⟨h10, m₂, k₂⟩ => ?_
  have hs := h.scr.congr (k₁.trans k₂).2.2
  refine WP.mono (WP.keep [.r12, .rax, .rdx] (Q := fun t =>
    t.mem = s₂.mem.writeW (off B (slot W aM + 8 * (W / 2 - 1)))
      (word s₂.mem B (slot W aM + 8 * (W / 2 - 1)) ||| BitVec.ofNat 64 (2 ^ 63))) (by
    xrun [(k₂.gpr (by decide) : s₂.gpr .r12 = _), h12, shr1_ofNat W (by omega),
      State.ea, ix, addrm8 h10 (rfl : BitVec.ofNat 64 (W / 2) = _) (by omega),
      hs.ld (d := slot W aM + 8 * (W / 2 - 1)) (by omega),
      hs.st (d := slot W aM + 8 * (W / 2 - 1)) (by omega)]
    rfl) rfl) fun t ⟨m₃, k₃⟩ => ?_
  exact ⟨by rw [m₃, m₂, m₁], ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- A normalized top word makes the represented modulus positive. -/
theorem modulus_pos {m : Mem} {B : Addr} {e n : Nat} (hn : 1 ≤ n)
    (hd : 2 ^ 63 ≤ (word m B (e + 8 * (n - 1))).toNat) : 0 < wv m B e n := by
  have he : n = (n - 1) + 1 := by omega_using [hn]
  have ht : 0 < (word m B (e + 8 * (n - 1))).toNat := by omega_using [hd]
  have hp := Nat.mul_pos (Nat.two_pow_pos (64 * (n - 1))) ht
  rw [he, wv]
  omega_using [hp]

end VG.Proof.Rsa.X86_64.WordDivide
