module

public import VerifiedGarbage.Impl.Bignum.X86_64.R2Squares
public import VerifiedGarbage.Proof.Bignum.X86_64.PubR2
import VerifiedGarbage.Proof.Framework.Omega

/-! # Counted R² squarings preserve the original arithmetic and frame -/

@[expose] public section
namespace VG.Proof.Bignum.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

theorem r2Counter_change {s t : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {v : Nat}
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z)
    (hm : t.mem = s.mem.writeW (off B (8 * sCnt)) (BitVec.ofNat 64 v))
    (hk : Keep [.rax] s t) :
    Good t B Z w mi ∧ word t.mem B (8 * sCnt) = BitVec.ofNat 64 v ∧
    (∀ a, a < 8 → wv t.mem B (slot w a) w = wv s.mem B (slot w a) w) ∧
    word t.mem B (slot w aN) = word s.mem B (slot w aN) ∧
    Frm B (r2Ranges w) s.mem t.mem := by
  have hn : B.toNat + slot w 8 ≤ 2 ^ 64 := by have := hg.scr.nowrap; omega
  refine ⟨⟨hg.scr.congr hk.2.2, (hk.gpr (by decide)).trans hg.rdi, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [hm]; exact Hdr.store hg.hdr (by decide) (by decide) _
  · rw [hm, word_writeW_self]
  · intro a ha; rw [hm, hdrStore_wv _ _ _ (by decide) ha hn]
  · rw [hm, hdrStore_word _ _ _ (by decide) (by decide) hn]
  · rw [hm]
    exact Frm.of_outside (writeW_outside _ _ _ (by
      have := hdr_lt_slot w 0 (show sCnt < 32 by decide)
      have := slot_le (w := w) (show 0 < 8 by decide)
      omega)) (by simp [r2Ranges])

theorem r2Squares_init {s : State} {B : Addr} {Z w n : Nat} {mi : BitVec 64}
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z) (hn : n + 1 < 2 ^ 32) :
    WP isa (.block (R2Squares.init n)) s fun t =>
      t.mem = s.mem.writeW (off B (8 * sCnt)) (BitVec.ofNat 64 (n + 1)) ∧ Keep [.rax] s t := by
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    t.mem = s.mem.writeW (off B (8 * sCnt)) (BitVec.ofNat 64 (n + 1))) ?_ rfl)
    fun t ⟨hm, hk⟩ => ⟨hm, hk⟩
  have cast : (BitVec.ofNat 32 (n + 1)).setWidth 64 = BitVec.ofNat 64 (n + 1) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  xrun [R2Squares.init, State.ea, hdr, hg.rdi, hdrOff, cast,
    hg.scr.st (d := 8 * sCnt) (by
      have := hdr_lt_slot w 0 (show sCnt < 32 by decide)
      have := slot_le (w := w) (show 0 < 8 by decide)
      omega)]

theorem r2Squares_next {s : State} {B : Addr} {Z w n : Nat} {mi : BitVec 64}
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z)
    (hn : word s.mem B (8 * sCnt) = BitVec.ofNat 64 n) (h1 : 1 ≤ n) (hb : n < 2 ^ 64) :
    WP isa (.block R2Squares.next) s fun t =>
      t.mem = s.mem.writeW (off B (8 * sCnt)) (BitVec.ofNat 64 (n - 1)) ∧
      t.zf = some (decide (n - 1 = 0)) ∧ Keep [.rax] s t := by
  have hr : 8 * sCnt + 8 ≤ Z := by
    have := hdr_lt_slot w 0 (show sCnt < 32 by decide)
    have := slot_le (w := w) (show 0 < 8 by decide)
    omega
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    t.mem = s.mem.writeW (off B (8 * sCnt)) (BitVec.ofNat 64 (n - 1)) ∧
    t.zf = some (decide (n - 1 = 0))) ?_ rfl) fun t ⟨⟨hm, hz⟩, hk⟩ => ⟨hm, hz, hk⟩
  xrun [R2Squares.next, State.ea, hdr, hg.rdi, hdrOff, hg.scr.ld hr, hg.scr.st hr, hn,
    ofNat64_pred h1 hb, ofNat64_beq_zero (show n - 1 < 2 ^ 64 by omega)]

theorem rolled_sqs_ok (M : Mont) {s : State} {B : Addr} {Z w n : Nat} {mi : BitVec 64}
    {N E : Nat} (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hn32 : n + 1 < 2 ^ 32) (hR : Nat.Coprime (2 ^ (64 * w)) N)
    (hn : wv s.mem B (slot w aN) w = N)
    (hinv : ((word s.mem B (slot w aN)).toNat * mi.toNat + 1) % 2 ^ 64 = 0)
    (hlt : wv s.mem B (slot w aR2) w < N)
    (hc : wv s.mem B (slot w aR2) w % N = 2 ^ E * 2 ^ (64 * w) % N) :
    WP isa (R2Squares.run M.mm n) s fun t => Good t B Z w mi ∧
      wv t.mem B (slot w aR2) w < N ∧
      wv t.mem B (slot w aR2) w % N = 2 ^ (2 ^ (n + 1) * E) * 2 ^ (64 * w) % N ∧
      Frm B (r2Ranges w) s.mem t.mem ∧ Keep mmRegs s t := by
  let I := fun k (t : State) => 1 ≤ k ∧ k ≤ n + 1 ∧ Good t B Z w mi ∧
    wv t.mem B (slot w aN) w = N ∧
    ((word t.mem B (slot w aN)).toNat * mi.toNat + 1) % 2 ^ 64 = 0 ∧
    wv t.mem B (slot w aR2) w < N ∧
    wv t.mem B (slot w aR2) w % N = 2 ^ (2 ^ (n + 1 - k) * E) * 2 ^ (64 * w) % N ∧
    word t.mem B (8 * sCnt) = BitVec.ofNat 64 k ∧
    Frm B (r2Ranges w) s.mem t.mem ∧ Keep mmRegs s t
  unfold R2Squares.run
  refine WP.seq (WP.mono (r2Squares_init hg hZ hn32) fun t ⟨hm, hk⟩ => ?_)
  obtain ⟨hgt, count, values, wordN, frame⟩ := r2Counter_change hg hZ hm hk
  have start : I (n + 1) t := ⟨by omega, by omega, hgt,
    by rw [values _ (by decide)]; exact hn, by rw [wordN]; exact hinv,
    by rw [values _ (by decide)]; exact hlt,
    by simp only [Nat.sub_self, Nat.pow_zero, Nat.one_mul]
       rw [values aR2 (by decide)]; exact hc,
    count, frame, hk.mono (by decide)⟩
  refine WP.loop I ?_ (n + 1) t start
  intro k u hu
  obtain ⟨h1, hb, hgu, nEq, inv, lt, val, count, frame, keep⟩ := hu
  refine WP.seq (WP.mono (sq_ok M hgu hZ hw hw' hR nEq inv lt val)
    fun v ⟨hgv, nEqv, invv, ltv, valv, arr, kv⟩ => ?_)
  have countv := (arr.hslot (show sCnt < 32 by decide)).trans count
  refine WP.mono (r2Squares_next hgv hZ countv h1 (by omega)) fun z ⟨hm, hz, kz⟩ => ?_
  obtain ⟨hgz, countz, values, wordN, ff⟩ := r2Counter_change hgv hZ hm kz
  have fz := (frame.trans (Frm.of_arrays arr (by simp [r2Ranges]))).trans ff
  have kz' : Keep mmRegs s z := ((keep.trans kv).trans kz).mono (by decide)
  have vz : wv z.mem B (slot w aR2) w % N =
      2 ^ (2 ^ (n + 1 - (k - 1)) * E) * 2 ^ (64 * w) % N := by
    have he : 2 * (2 ^ (n + 1 - k) * E) = 2 ^ (n + 1 - (k - 1)) * E := by
      rw [show n + 1 - (k - 1) = n + 1 - k + 1 by omega, Nat.pow_succ]
      ac_rfl
    rw [values _ (by decide), valv, he]
  by_cases hk : k = 1
  · subst k
    exact Or.inl ⟨by simp [eval, hz], hgz, by rw [values _ (by decide)]; exact ltv,
      by simpa using vz, fz, kz'⟩
  · refine Or.inr ⟨by simp [eval, hz, show k - 1 ≠ 0 by omega], k - 1, by omega,
      by omega, by omega, hgz, ?_, ?_, ?_, vz, countz, fz, kz'⟩
    · rw [values _ (by decide)]; exact nEqv
    · rw [wordN]; exact invv
    · rw [values _ (by decide)]; exact ltv

theorem rolled_sqs_spec (M : Mont) (n : Nat) (hn32 : n + 1 < 2 ^ 32) :
    R2SquareSpec (R2Squares.run M.mm n) (n + 1) := by
  intro t B Z w mi N E hg hZ hw hw' hR hn hinv hlt hc
  exact rolled_sqs_ok M hg hZ hw hw' hn32 hR hn hinv hlt hc

end VG.Proof.Bignum.X86_64
