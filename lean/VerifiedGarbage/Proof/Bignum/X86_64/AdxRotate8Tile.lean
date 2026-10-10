import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8TileEdges

/-! ## AdxRotate8Front -/
section

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

end

/-! ## AdxRotate8Compute -/
section

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

end

/-! ## AdxRotate8Tile -/
section

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

end
