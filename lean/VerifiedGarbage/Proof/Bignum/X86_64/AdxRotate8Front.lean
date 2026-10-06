import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8TileEdges

/-! The first block determines the cancellation digits and starts the sweep. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

theorem front_ok {s : State} {B : Addr} {Z w e n : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w mi)
    (hZ : slot w 8 ≤ Z) (hw : w = 8 * (n + 1)) (hc : s.gpr .rcx = off B e)
    (he : hdrBytes + 16 ≤ e) (heZ : e + 64 ≤ Z) (hsep : slot w aN + 8 * w ≤ e - 8) :
    WP isa AdxRotate8.tileFront s fun t =>
      (((word s.mem B (slot w aN)).toNat * mi.toNat + 1) % 2 ^ 64 = 0 →
        2 ^ 512 * cols t = wv s.mem B e 8 + wv t.mem B e 8 * wv s.mem B (slot w aN) 8) ∧
      word t.mem B (e - 8) = 0 ∧ t.gpr .rbp = off B (slot w aN + 64) ∧
      t.gpr .rsi = off B (e + 64) ∧ t.zf = some (decide (n = 0)) ∧
      Outside B (e - 8) 72 s.mem t.mem ∧ Keep [.rdx, .rax, .rbx, .rbp, .rsi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  have hn := hs.nowrap
  have hNs := slot_le (w := w) (show aN < 8 by decide)
  unfold AdxRotate8.tileFront
  refine WP.seq (WP.mono (tileBegin_ok hs hdi hH hZ hc heZ) fun a ⟨va, hp, ho, ma, ka⟩ => ?_)
  refine WP.seq (WP.mono (headN_ok (n := 8) (mi := mi) (hs.congr ka.2.2) ((ka.gpr (by decide)).trans hdi)
    ((ka.gpr (by decide)).trans hc) hp heZ (by omega) (by omega)
    (Nat.le_trans (by decide : 8 * sMinv + 8 ≤ hdrBytes + 16) he)
    (by rw [ma]; exact hH.hminv)) fun b ⟨vb, ob, kb⟩ => ?_)
  have kab := ka.trans kb
  have hbH : Hdr b.mem B w mi := (ma ▸ hH).of_outside ob (by omega)
  refine WP.seq (WP.mono (clearCarry_ok (hs.congr kab.2.2) ((kab.gpr (by decide)).trans hc)
    (by omega) (by omega)) fun c ⟨zc, oc, kc⟩ => ?_)
  have kabc := kab.trans kc
  have hcH := hbH.of_outside oc (by omega)
  have hcP : c.gpr .rbp = off B (slot w aN + 8 * 0) := by
    simpa only [Nat.mul_zero, Nat.add_zero] using ((kb.trans kc).gpr (r := .rbp) (by decide)).trans hp
  have hcO : c.gpr .rsi = off B (e + 8 * 0) := by
    simpa only [Nat.mul_zero, Nat.add_zero] using ((kb.trans kc).gpr (r := .rsi) (by decide)).trans ho
  refine WP.mono (nextBlock_ok (hs.congr kabc.2.2) ((kabc.gpr (by decide)).trans hdi)
    hcH hZ (by omega) hcP hcO) fun t ⟨pt, ot, zt, mt, kt⟩ => ?_
  have outb : Outside B e 64 s.mem b.mem := by rw [ma] at ob; exact ob
  have outc : Outside B (e - 8) 72 s.mem c.mem :=
    (outb.mono (by omega) (by omega)).trans (oc.mono (by omega) (by omega))
  have uc : wv c.mem B e 8 = wv b.mem B e 8 := oc.wv (by omega) (by omega)
  refine ⟨?_, by rw [mt]; exact zc, pt, ot, ?_, by rw [mt]; exact outc,
    (kabc.trans kt).mono (by decide)⟩
  · intro hi
    have hv := vb (by rw [ma]; exact hi)
    rw [ma, va, show 64 * 8 = 512 from rfl] at hv
    rw [cols_keep kt (by decide), cols_keep kc (by decide), mt, uc]
    exact hv
  · rw [zt]; exact congrArg some (decide_eq_decide.mpr (by omega))
end VG.Proof.Bignum.X86_64.AdxRotate8
