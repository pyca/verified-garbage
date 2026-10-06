import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Front

/-! A tile's exact reduction relation before its public pointer advance. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

theorem compute_ok {s : State} {B : Addr} {Z w e n : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w mi)
    (hZ : slot w 8 ≤ Z) (hw : w = 8 * (n + 1)) (hc : s.gpr .rcx = off B e)
    (he : hdrBytes + 16 ≤ e) (heZ : e + 8 * (w + 8) ≤ Z) (hsep : slot w aN + 8 * w ≤ e - 8) :
    WP isa AdxRotate8.tileCompute s fun t =>
      (((word s.mem B (slot w aN)).toNat * mi.toNat + 1) % 2 ^ 64 = 0 →
        ∃ q < 2 ^ 512,
          2 ^ 512 * (wv t.mem B (e + 64) w + 2 ^ (64 * w) * (t.gpr .rax).toNat) =
            wv s.mem B e (w + 8) + 2 ^ (64 * w) * (word s.mem B (e - 16)).toNat +
              q * wv s.mem B (slot w aN) w) ∧
      (t.gpr .rax).toNat ≤ 3 ∧ Outside B (e - 8) (8 * (w + 9)) s.mem t.mem ∧ t.gpr .rcx = off B e ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  unfold AdxRotate8.tileCompute
  refine WP.seq (WP.mono (front_ok hs hdi hH hZ hw hc he (by omega) hsep)
    fun a ⟨va, za, pa, oa, zfa, outa, ka⟩ => ?_)
  have ha := hH.of_outside outa (by omega)
  refine WP.seq (WP.mono (middles_ok (hs.congr ka.2.2) ha ((ka.gpr (by decide)).trans hdi)
    ((ka.gpr (by decide)).trans hc) pa oa zfa hZ hw he heZ hsep) fun b hb => ?_)
  have ob : Outside B (e - 8) (8 * (w + 9)) a.mem b.mem :=
    hb.out.outside (by omega) (by omega) (by omega) (by omega)
  have outab : Outside B (e - 8) (8 * (w + 9)) s.mem b.mem :=
    (outa.mono (by omega) (by omega)).trans ob
  have hbO : b.gpr .rsi = off B (e + 8 * w) := by rw [hb.rsi]; congr 1; omega
  refine WP.mono (tailCore_ok hb.scr hb.rcx hbO (by omega) (by omega) (by omega))
    fun t ⟨vt, bt, outt, kt⟩ => ?_
  refine ⟨?_, bt, outab.trans (outt.mono (by omega) (by omega)),
    (kt.gpr (by decide)).trans hb.rcx, (ka.trans (hb.keep.trans kt)).mono (by decide)⟩
  intro hi
  have h0 := va hi
  have h1 := hb.val
  have tm : wv a.mem B (e + 64) (8 * n) = wv s.mem B (e + 64) (8 * n) := outa.wv (by omega) (by omega)
  have nm : wv a.mem B (slot w aN + 64) (8 * n) = wv s.mem B (slot w aN + 64) (8 * n) :=
    outa.wv (by omega) (by omega)
  have topb : wv b.mem B (e + 8 * w) 8 = wv a.mem B (e + 8 * w) 8 := hb.out.wv (by omega) (by omega) (by omega)
  have topa : wv a.mem B (e + 8 * w) 8 = wv s.mem B (e + 8 * w) 8 := outa.wv (by omega) (by omega)
  have oldc : word b.mem B (e - 16) = word s.mem B (e - 16) := outab.word (by omega) (by omega)
  have lo : wv t.mem B (e + 64) (8 * n) = wv b.mem B (e + 64) (8 * n) := outt.wv (by omega) (by omega)
  rw [za, tm, nm] at h1
  simp only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at h1
  rw [topb, topa, oldc] at vt
  have hv := tile_combine (R := 2 ^ 512) (P := 2 ^ (512 * n))
    (H := cols a) (C := cols b + (word b.mem B (e - 8)).toNat)
    (Y := wv t.mem B (e + 8 * w) 8) (K := (t.gpr .rax).toNat)
    (V := wv s.mem B (e + 8 * w) 8) (Q := (word s.mem B (e - 16)).toNat) h0 h1 vt
  refine ⟨wv a.mem B e 8, ?_, ?_⟩
  · simpa only [show 64 * 8 = 512 from rfl] using wv_lt a.mem B e 8
  have pw : 2 ^ (64 * w) = 2 ^ (512 * n) * 2 ^ 512 := by
    rw [show 64 * w = 512 * n + 512 by omega, Nat.pow_add]
  have output : wv t.mem B (e + 64) w = wv b.mem B (e + 64) (8 * n) +
      2 ^ (512 * n) * wv t.mem B (e + 8 * w) 8 := by
    have hx := wv_add t.mem B (e + 64) (8 * n) 8
    rw [show 8 * n + 8 = w by omega, lo, show 64 * (8 * n) = 512 * n by omega,
      show e + 64 + 8 * (8 * n) = e + 8 * w by omega] at hx
    exact hx
  have input : wv s.mem B e (w + 8) =
      wv s.mem B e 8 + 2 ^ 512 * wv s.mem B (e + 64) (8 * n) +
        (2 ^ (512 * n) * 2 ^ 512) * wv s.mem B (e + 8 * w) 8 := by
    have hx := wv_add s.mem B e 8 (8 * n)
    rw [show 8 + 8 * n = w by omega, show 64 * 8 = 512 from rfl, show 8 * 8 = 64 from rfl] at hx
    have hy := wv_add s.mem B e w 8
    rw [pw] at hy
    omega_using [hx, hy]
  have modulus : wv s.mem B (slot w aN) w = wv s.mem B (slot w aN) 8 +
      2 ^ 512 * wv s.mem B (slot w aN + 64) (8 * n) := by
    have hx := wv_add s.mem B (slot w aN) 8 (8 * n)
    rw [show 8 + 8 * n = w by omega, show 64 * 8 = 512 from rfl, show 8 * 8 = 64 from rfl] at hx
    exact hx
  rw [output, input, modulus, pw]
  exact hv
end VG.Proof.Bignum.X86_64.AdxRotate8
