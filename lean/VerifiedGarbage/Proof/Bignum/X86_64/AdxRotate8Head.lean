module

public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Digit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRedcRow
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! ## AdxRotate8HeadStep -/

@[expose] public section

section

/-! A register cancellation step, with memory safety independent of the inverse. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

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

theorem headStep_ok {s : State} {B : Addr} {Z e eN m j : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hc : s.gpr .rcx = off B e) (hi : s.gpr .rsi = idx m)
    (hp : s.gpr .rbp = off B eN)
    (he : e + 8 * m + 8 * j + 8 ≤ Z) (hN : eN + 64 ≤ Z) (hsep : eN + 64 ≤ e)
    (hm : readSrc s (.mem (hdr sMinv)) = some mi) :
    WP isa (AdxRotate8.headStep j) s fun t =>
      (((word s.mem B eN).toNat * mi.toNat + 1) % 2 ^ 64 = 0 →
        2 ^ 64 * cols t = cols s + (digitValue s mi).toNat * wv s.mem B eN 8) ∧
      word t.mem B (e + 8 * m + 8 * j) = digitValue s mi ∧
      Outside B (e + 8 * m + 8 * j) 8 s.mem t.mem ∧
      Keep [.rdx, .rax, .rbx, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  have hn := hs.nowrap
  unfold AdxRotate8.headStep
  refine WP.seq (WP.mono (digit_ok hs hc hi he hm) fun a ⟨hd, hv, wa, oa, ka⟩ => ?_)
  refine WP.mono (core_mem (hs.congr ka.2.2) ((ka.gpr (by decide)).trans hp) hN)
    fun t ⟨ht, _, _, kt⟩ => ?_
  rw [hv, hd, oa.wv (by omega) (by omega)] at ht
  refine ⟨?_, ?_, ?_, (ka.trans kt.keep).mono (by decide)⟩
  · intro hinv
    have low := cancel_low hinv ht
    rw [low] at ht
    simpa only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.zero_add] using ht
  · rw [kt.2.1]; exact wa
  · rw [kt.2.1]; exact oa
end VG.Proof.Bignum.X86_64.AdxRotate8

end

/-! ## AdxRotate8Head -/
section

/-! Eight cancellations determine a radix-512 multiplier. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem headSteps_ok {s : State} {B : Addr} {Z e eN m n : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hc : s.gpr .rcx = off B e) (hi : s.gpr .rsi = idx m) (hp : s.gpr .rbp = off B eN)
    (he : e + 8 * m + 8 * n ≤ Z) (hN : eN + 64 ≤ Z) (hsep : eN + 64 ≤ e)
    (hh : 8 * sMinv + 8 ≤ e) (hmi : word s.mem B (8 * sMinv) = mi) :
    WP isa (AdxRotate8.headSteps n) s fun t =>
      (((word s.mem B eN).toNat * mi.toNat + 1) % 2 ^ 64 = 0 →
        2 ^ (64 * n) * cols t = cols s + wv t.mem B (e + 8 * m) n * wv s.mem B eN 8) ∧
      Outside B (e + 8 * m) (8 * n) s.mem t.mem ∧
      Keep [.rdx, .rax, .rbx, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  induction n with
  | zero =>
    apply WP.block_nil
    exact ⟨fun _ => by simp only [wv, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_mul, Nat.add_zero], Outside.refl _ _ _ _, Keep.refl _ _⟩
  | succ n ih =>
    unfold AdxRotate8.headSteps
    refine WP.seq (WP.mono (ih (by omega)) fun a ⟨va, oa, ka⟩ => ?_)
    have sa := hs.congr ka.2.2
    have hna := sa.nowrap
    have ma : word a.mem B (8 * sMinv) = mi :=
      (oa.word (by omega) (by omega)).trans hmi
    have miRead : readSrc a (.mem (hdr sMinv)) = some mi := by
      rw [readSrc_word (d := 8 * sMinv) sa (by
        simp only [State.ea, hdr, (ka.gpr (by decide)).trans hdi, hdrOff]) (by omega), ma]
    refine WP.mono (headStep_ok sa ((ka.gpr (by decide)).trans hc) ((ka.gpr (by decide)).trans hi)
      ((ka.gpr (by decide)).trans hp) (by omega) hN hsep miRead)
      fun t ⟨vt, digit, ot, kt⟩ => ?_
    have mn : wv a.mem B eN 8 = wv s.mem B eN 8 := oa.wv (by omega) (by omega)
    have mn0 : word a.mem B eN = word s.mem B eN := oa.word (by omega) (by omega)
    have lo : wv t.mem B (e + 8 * m) n = wv a.mem B (e + 8 * m) n := ot.wv (by omega) (by omega)
    refine ⟨?_, (oa.mono (o' := e + 8 * m) (n' := 8 * (n + 1)) (by omega) (by omega)).trans
      (ot.mono (o' := e + 8 * m) (n' := 8 * (n + 1)) (by omega) (by omega)), (ka.trans kt).mono (by decide)⟩
    intro hinv
    have ea := va hinv
    have et := vt (by rw [mn0]; exact hinv)
    rw [mn] at et
    rw [wv, lo, show e + 8 * m + 8 * n = e + 8 * m + 8 * n from rfl, digit, pow64_succ]
    grind

/-- The head loop's state after `j` iterations. -/
structure HeadInv (s₀ : State) (B : Addr) (Z e eN : Nat) (mi : BitVec 64) (j : Nat) (s : State) : Prop where
  scr : Scr s B Z
  rdi : s.gpr .rdi = B
  rcx : s.gpr .rcx = off B e
  rbp : s.gpr .rbp = off B eN
  rsi : s.gpr .rsi = idx (4 * j)
  val : ((word s₀.mem B eN).toNat * mi.toNat + 1) % 2 ^ 64 = 0 →
    2 ^ (64 * (4 * j)) * cols s = cols s₀ + wv s.mem B e (4 * j) * wv s₀.mem B eN 8
  out : Outside B e (8 * (4 * j)) s₀.mem s.mem
  keep : Keep [.rdx, .rax, .rbx, .rsi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s₀ s

theorem headLoop_ok {s : State} {B : Addr} {Z e eN : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hc : s.gpr .rcx = off B e) (hp : s.gpr .rbp = off B eN)
    (he : e + 8 * 8 ≤ Z) (hN : eN + 64 ≤ Z) (hsep : eN + 64 ≤ e)
    (hh : 8 * sMinv + 8 ≤ e) (hmi : word s.mem B (8 * sMinv) = mi) :
    WP isa AdxRotate8.headLoop s fun t =>
      (((word s.mem B eN).toNat * mi.toNat + 1) % 2 ^ 64 = 0 →
        2 ^ (64 * 8) * cols t = cols s + wv t.mem B e 8 * wv s.mem B eN 8) ∧
      Outside B e (8 * 8) s.mem t.mem ∧ t.gpr .rsi = off B e ∧
      Keep [.rdx, .rax, .rbx, .rsi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  unfold AdxRotate8.headLoop
  rw [show AdxRotate8.unroll = 4 from rfl]
  refine WP.seq (WP.mono (idxInit_ok s .rsi) fun a ⟨ia, ma, ka⟩ => ?_)
  have h0 : HeadInv s B Z e eN mi 0 a := ⟨hs.congr ka.2.2, (ka.gpr (by decide)).trans hdi,
    (ka.gpr (by decide)).trans hc, (ka.gpr (by decide)).trans hp, by simpa only [Nat.mul_zero] using ia,
    fun _ => by simp only [Nat.mul_zero, wv, Nat.pow_zero, Nat.one_mul, Nat.zero_mul, Nat.add_zero,
      cols_keep ka (by decide)],
    by rw [ma]; exact Outside.refl _ _ _ _, ka.mono (by decide)⟩
  refine WP.seq (WP.mono (wp_upto (a := 0) (N := 2) (by decide) (HeadInv s B Z e eN mi) ?body
    (fun _ h => h) h0) fun b hb => ?_)
  case body =>
    intro j _ hj b hb
    have hna := hb.scr.nowrap
    have mib : word b.mem B (8 * sMinv) = mi := (hb.out.word (by omega) (by omega)).trans hmi
    refine WP.seq (WP.mono (headSteps_ok (n := 4) hb.scr hb.rdi hb.rcx hb.rsi hb.rbp
      (by omega) hN hsep hh mib) fun c ⟨vc, oc, kc⟩ => ?_)
    refine WP.mono (idxAdd_ok ((kc.gpr (by decide)).trans hb.rsi) (by omega)) fun t ⟨it, zt, mt, kt⟩ => ?_
    have kct := kc.trans kt
    refine ⟨by rw [zt]; exact congrArg some (decide_eq_decide.mpr (by omega)), ⟨hb.scr.congr kct.2.2,
      (kct.gpr (by decide)).trans hb.rdi, (kct.gpr (by decide)).trans hb.rcx,
      (kct.gpr (by decide)).trans hb.rbp, by rw [it, Nat.mul_succ], ?_, ?_,
      (hb.keep.trans kct).mono (by decide)⟩⟩
    · intro hinv
      have wn : word b.mem B eN = word s.mem B eN := hb.out.word (by omega) (by omega)
      have vb := hb.val hinv
      have vc' := vc (by rw [wn]; exact hinv)
      rw [show wv b.mem B eN 8 = wv s.mem B eN 8 from hb.out.wv (by omega) (by omega)] at vc'
      rw [cols_keep kt (by decide), mt, show 4 * (j + 1) = 4 * j + 4 by omega, wv_add,
        show wv c.mem B e (4 * j) = wv b.mem B e (4 * j) from oc.wv (by omega) (by omega),
        show 64 * (4 * j + 4) = 64 * (4 * j) + 64 * 4 by omega, Nat.pow_add,
        show e + 8 * (4 * j) = e + 8 * (4 * j) from rfl]
      grind
    · rw [mt]
      exact (hb.out.mono (o' := e) (n' := 8 * (4 * (j + 1))) (by omega) (by omega)).trans
        (oc.mono (o' := e) (n' := 8 * (4 * (j + 1))) (by omega) (by omega))
  refine WP.mono (WP.keep [.rsi] (Q := fun t => t.gpr .rsi = b.gpr .rcx ∧ t.mem = b.mem) ?_ rfl)
    fun t ⟨⟨ht, mt⟩, kt⟩ => ?_
  · xrun []
  refine ⟨fun hinv => ?_, by rw [mt]; exact hb.out.mono (by omega) (by omega), ht.trans hb.rcx, (hb.keep.trans kt).mono (by decide)⟩
  have v := hb.val hinv
  rw [show 4 * 2 = 8 from rfl] at v
  rw [cols_keep kt (by decide), mt]
  exact v
end VG.Proof.Bignum.X86_64.AdxRotate8

end
