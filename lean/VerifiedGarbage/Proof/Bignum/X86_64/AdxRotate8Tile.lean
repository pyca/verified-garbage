import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Compute

/-! A whole cancellation tile, including the untouched high input words. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

theorem tile_ok {s : State} {B : Addr} {Z w e n L : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w mi)
    (hZ : slot w 8 ≤ Z) (hw : w = 8 * (n + 1)) (hc : s.gpr .rcx = off B e)
    (he : hdrBytes + 16 ≤ e) (heZ : e + 8 * L ≤ Z) (hL : w + 8 ≤ L)
    (hsep : slot w aN + 8 * w ≤ e - 8) :
    WP isa AdxRotate8.tile s fun t =>
      (((word s.mem B (slot w aN)).toNat * mi.toNat + 1) % 2 ^ 64 = 0 →
        ∃ q < 2 ^ 512,
          2 ^ 512 * (wv t.mem B (e + 64) (L - 8) + 2 ^ (64 * w) * (word t.mem B (e + 48)).toNat) =
            wv s.mem B e L + 2 ^ (64 * w) * (word s.mem B (e - 16)).toNat +
              q * wv s.mem B (slot w aN) w) ∧
      t.gpr .rcx = off B (e + 64) ∧ t.zf = some (decide (e + 64 = slot w aTmp)) ∧
      Outside B (e - 8) (8 * (w + 9)) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  unfold AdxRotate8.tile
  refine WP.seq (WP.mono (compute_ok hs hdi hH hZ hw hc he (by omega_using [he, heZ, hL, hw, hn]) hsep) fun a ⟨va, _, oa, hca, ka⟩ => ?_)
  have ha := hH.of_outside oa (by omega_using [he, heZ, hL, hw, hn])
  refine WP.mono (tileEnd_ok (hs.congr ka.2.2) ((ka.gpr (by decide)).trans hdi)
    ha hZ hca (by omega_using [he, heZ, hL, hw, hn]) (by omega_using [he, heZ, hL, hw, hn])) fun t ⟨wt, ct, zt, ot, kt⟩ => ?_
  refine ⟨?_, ct, zt, oa.trans (ot.mono (by omega_using [he, heZ, hL, hw, hn]) (by omega_using [he, heZ, hL, hw, hn])), (ka.trans kt).mono (by decide)⟩
  intro hi
  obtain ⟨q, hq, hv⟩ := va hi
  refine ⟨q, hq, ?_⟩
  have low : wv t.mem B (e + 64) w = wv a.mem B (e + 64) w := ot.wv (by omega_using [he, heZ, hL, hw, hn]) (by omega_using [he, heZ, hL, hw, hn])
  have outall := oa.trans (ot.mono (o' := e - 8) (n' := 8 * (w + 9)) (by omega_using [he, heZ, hL, hw, hn]) (by omega_using [he, heZ, hL, hw, hn]))
  have high : wv t.mem B (e + 8 * (w + 8)) (L - (w + 8)) =
      wv s.mem B (e + 8 * (w + 8)) (L - (w + 8)) := outall.wv (by omega_using [he, heZ, hL, hw, hn]) (by omega_using [he, heZ, hL, hw, hn])
  have hx := wv_add t.mem B (e + 64) w (L - (w + 8))
  rw [show w + (L - (w + 8)) = L - 8 by omega_using [he, heZ, hL, hw, hn],
    show e + 64 + 8 * w = e + 8 * (w + 8) by omega_using [he, heZ, hL, hw, hn], low, high] at hx
  have hy := wv_add s.mem B e (w + 8) (L - (w + 8))
  rw [show w + 8 + (L - (w + 8)) = L by omega_using [he, heZ, hL, hw, hn],
    show 64 * (w + 8) = 64 * w + 512 by omega_using [he, heZ, hL, hw, hn], Nat.pow_add] at hy
  rw [hx, hy, wt]
  have result := extend_high (R := 2 ^ 512) (P := 2 ^ (64 * w))
    (X := wv a.mem B (e + 64) w) (Y := wv s.mem B e (w + 8))
    (C := (a.gpr .rax).toNat) (D := (word s.mem B (e - 16)).toNat)
    (U := q) (N := wv s.mem B (slot w aN) w)
    (H := wv s.mem B (e + 8 * (w + 8)) (L - (w + 8))) hv
  exact result
end VG.Proof.Bignum.X86_64.AdxRotate8
