import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Digit

/-! A register cancellation step, with memory safety independent of the inverse. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

theorem cols_mod (s : State) : cols s % 2 ^ 64 = (s.gpr .r8).toNat := by
  have h : cols s = (s.gpr .r8).toNat + 2 ^ 64 *
      ((s.gpr .r9).toNat + 2 ^ 64 * (s.gpr .r10).toNat + 2 ^ 128 * (s.gpr .r11).toNat +
      2 ^ 192 * (s.gpr .r12).toNat + 2 ^ 256 * (s.gpr .r13).toNat +
      2 ^ 320 * (s.gpr .r14).toNat + 2 ^ 384 * (s.gpr .r15).toNat) := by
    unfold cols; omega
  rw [h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (s.gpr .r8).isLt]

theorem cancel_low {s t : State} {B : Addr} {eN : Nat} {mi : BitVec 64}
    (hinv : ((word s.mem B eN).toNat * mi.toNat + 1) % 2 ^ 64 = 0)
    (heq : (t.gpr .rbx).toNat + 2 ^ 64 * cols t =
      cols s + (digitValue s mi).toNat * wv s.mem B eN 8) : t.gpr .rbx = 0 := by
  have e := congrArg (· % 2 ^ 64) heq
  have lo := mont_low (s.gpr .r8).toNat mi.toNat (word s.mem B eN).toNat hinv
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod,
    Nat.add_zero, Nat.mod_eq_of_lt (t.gpr .rbx).isLt, cols_mod,
    AdxSquare.wv_mod_word _ _ _ (show 1 ≤ 8 by decide), digitValue, BitVec.toNat_ofNat,
    Nat.mod_mod] at e
  apply BitVec.eq_of_toNat_eq
  change (t.gpr .rbx).toNat = 0
  rw [Nat.add_comm] at lo
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, Nat.mod_eq_of_lt (s.gpr .r8).isLt] at lo
  simp only [Nat.mod_mod, Nat.mod_eq_of_lt (s.gpr .r8).isLt,
    Nat.mod_eq_of_lt mi.isLt, Nat.mod_eq_of_lt (word s.mem B eN).isLt] at e lo
  exact e.trans lo

theorem headStep_ok {s : State} {B : Addr} {Z e eN k : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hc : s.gpr .rcx = off B e) (hp : s.gpr .rbp = off B eN)
    (he : e + 8 * k + 8 ≤ Z) (hN : eN + 64 ≤ Z) (hsep : eN + 64 ≤ e)
    (hm : readSrc s (.mem (hdr sMinv)) = some mi) :
    WP isa (AdxRotate8.headStep k) s fun t =>
      (((word s.mem B eN).toNat * mi.toNat + 1) % 2 ^ 64 = 0 →
        2 ^ 64 * cols t = cols s + (digitValue s mi).toNat * wv s.mem B eN 8) ∧
      word t.mem B (e + 8 * k) = digitValue s mi ∧
      Outside B (e + 8 * k) 8 s.mem t.mem ∧
      Keep [.rdx, .rax, .rbx, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  have hn := hs.nowrap
  unfold AdxRotate8.headStep
  refine WP.seq (WP.mono (digit_ok hs hc he hm) fun a ⟨hd, hv, ha, ka⟩ => ?_)
  have oa : Outside B (e + 8 * k) 8 s.mem a.mem := by
    rw [ha]; exact writeW_outside _ _ _ (by omega)
  refine WP.mono (core_mem (hs.congr ka.2.2) ((ka.gpr (by decide)).trans hp) hN)
    fun t ⟨ht, _, _, kt⟩ => ?_
  rw [hv, hd, oa.wv (by omega) (by omega)] at ht
  refine ⟨?_, ?_, ?_, (ka.trans kt.keep).mono (by decide)⟩
  · intro hi
    have low := cancel_low hi ht
    rw [low] at ht
    simpa only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.zero_add] using ht
  · rw [kt.2.1, ha, word_writeW_self]
  · rw [kt.2.1]; exact oa
end VG.Proof.Bignum.X86_64.AdxRotate8
