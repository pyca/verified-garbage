import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Loop
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Edges

/-! Complete register-tiled REDC, with unconditional memory safety. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

theorem redc_ok {s : State} {B : Addr} {Z w n : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w mi)
    (hZ : slot w 8 ≤ Z) (hw : w = 8 * n) (hn : 0 < n) :
    WP isa AdxRotate8.redc s fun t =>
      (((word s.mem B (slot w aN)).toNat * mi.toNat + 1) % 2 ^ 64 = 0 →
        ∃ q < 2 ^ (64 * w),
          2 ^ (64 * w) * wv t.mem B (slot w aTmp) (w + 2) =
            wv s.mem B (slot w aAcc + 16) (2 * w) + q * wv s.mem B (slot w aN) w) ∧
      Outside B (slot w aAcc) (16 * w + 32) s.mem t.mem ∧ Keep mmRegs s t := by
  have hbound := hs.nowrap
  have hA := slot_le (w := w) (show aAcc < 8 by decide)
  have hT := slot_le (w := w) (show aTmp < 8 by decide)
  have hAT : slot w aAcc + 8 * (w + 2) = slot w aTmp := by unfold slot aAcc aTmp; omega
  have hsep : slot w aN + 8 * (w + 2) ≤ slot w aAcc := by unfold slot aN aAcc; omega
  have hhead : hdrBytes ≤ slot w aAcc := by unfold slot; omega
  unfold AdxRotate8.redc
  refine WP.seq (WP.mono (setup_ok hs hdi hH hZ) fun a ⟨hc, hz, oa, ka⟩ => ?_)
  have ha := hH.of_outside oa hhead
  have hi : RedcInv a B Z w 0 mi a := by
    refine ⟨hs.congr ka.2.2, ha,
      (ka.gpr (by decide)).trans hdi, by simpa only [Nat.mul_zero, Nat.add_zero] using hc,
      Keep.refl _ _, Outside.refl _ _ _ _, ?_⟩
    intro _
    refine ⟨0, by decide, ?_⟩
    simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero, Nat.pow_zero, Nat.one_mul,
      Nat.add_sub_cancel, hz, show (0 : BitVec 64).toNat = 0 from rfl, Nat.zero_mul]
  have loop : WP isa (.loop AdxRotate8.tile .ne) a (RedcInv a B Z w n mi) :=
    wp_upto (a := 0) (N := n) hn (RedcInv a B Z w · mi)
      (fun _ _ hlt _ h => tileStep_ok hZ hw hlt h) (fun _ h => h) hi
  refine WP.seq (WP.mono loop fun b hb => ?_)
  have bp : b.gpr .rcx = off B (slot w aTmp) := by
    rw [hb.rcx]; congr 1; omega
  refine WP.mono (finish_ok hb.scr hb.rdi hb.hdr hZ bp) fun t ⟨vt, ot, kt⟩ => ?_
  refine ⟨?_, ((oa.mono (o' := slot w aAcc) (n' := 16 * w + 32) (by omega) (by omega)).trans hb.out).trans
    (ot.mono (o' := slot w aAcc) (n' := 16 * w + 32) (by omega) (by omega)),
    (ka.trans (hb.keep.trans kt)).mono (by decide)⟩
  intro hinv
  have m0 : word a.mem B (slot w aN) = word s.mem B (slot w aN) := oa.word (by omega) (by omega)
  obtain ⟨q, hq, heq⟩ := hb.val (by rw [m0]; exact hinv)
  have inp : wv a.mem B (slot w aAcc + 16) (2 * w) = wv s.mem B (slot w aAcc + 16) (2 * w) :=
    oa.wv (by omega) (by omega)
  have modn : wv a.mem B (slot w aN) w = wv s.mem B (slot w aN) w := oa.wv (by omega) (by omega)
  rw [show 512 * n = 64 * w by omega] at hq heq
  rw [show slot w aAcc + 16 + 64 * n = slot w aTmp by omega,
    show 2 * w - 8 * n = w by omega, inp, modn] at heq
  exact ⟨q, hq, by rw [vt]; exact heq⟩
end VG.Proof.Bignum.X86_64.AdxRotate8
