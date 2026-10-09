import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8HeadStep

/-! Eight cancellations determine a radix-512 multiplier. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

theorem headN_ok {s : State} {B : Addr} {Z e eN n : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hc : s.gpr .rcx = off B e) (hp : s.gpr .rbp = off B eN)
    (he : e + 8 * n ≤ Z) (hN : eN + 64 ≤ Z) (hsep : eN + 64 ≤ e)
    (hh : 8 * sMinv + 8 ≤ e) (hmi : word s.mem B (8 * sMinv) = mi) :
    WP isa (AdxRotate8.headN n) s fun t =>
      (((word s.mem B eN).toNat * mi.toNat + 1) % 2 ^ 64 = 0 →
        2 ^ (64 * n) * cols t = cols s + wv t.mem B e n * wv s.mem B eN 8) ∧
      Outside B e (8 * n) s.mem t.mem ∧
      Keep [.rdx, .rax, .rbx, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  induction n with
  | zero =>
    apply WP.block_nil
    exact ⟨fun _ => by simp only [wv, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_mul, Nat.add_zero], Outside.refl _ _ _ _, Keep.refl _ _⟩
  | succ n ih =>
    unfold AdxRotate8.headN
    refine WP.seq (WP.mono (ih (by omega)) fun a ⟨va, oa, ka⟩ => ?_)
    have sa := hs.congr ka.2.2
    have hna := sa.nowrap
    have ma : word a.mem B (8 * sMinv) = mi :=
      (oa.word (by omega) (by omega)).trans hmi
    have miRead : readSrc a (.mem (hdr sMinv)) = some mi := by
      rw [readSrc_word (d := 8 * sMinv) sa (by
        simp only [State.ea, hdr, (ka.gpr (by decide)).trans hdi, hdrOff]) (by omega), ma]
    refine WP.mono (headStep_ok sa ((ka.gpr (by decide)).trans hc)
      ((ka.gpr (by decide)).trans hp) (by omega) hN hsep miRead)
      fun t ⟨vt, digit, ot, kt⟩ => ?_
    have mn : wv a.mem B eN 8 = wv s.mem B eN 8 := oa.wv (by omega) (by omega)
    have mn0 : word a.mem B eN = word s.mem B eN := oa.word (by omega) (by omega)
    have lo : wv t.mem B e n = wv a.mem B e n := ot.wv (by omega) (by omega)
    refine ⟨?_, (oa.mono (o' := e) (n' := 8 * (n + 1)) (by omega) (by omega)).trans
      (ot.mono (o' := e) (n' := 8 * (n + 1)) (by omega) (by omega)), (ka.trans kt).mono (by decide)⟩
    intro hinv
    have ea := va hinv
    have et := vt (by rw [mn0]; exact hinv)
    rw [mn] at et
    rw [wv, lo, digit, pow64_succ]
    grind
end VG.Proof.Bignum.X86_64.AdxRotate8
