module
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrSq
public import VerifiedGarbage.Impl.MillerRabin.AArch64.Round
public import VerifiedGarbage.Proof.MillerRabin.Contract
public import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerSave

import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerContext
import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerRestore
import VerifiedGarbage.Proof.MillerRabin.AArch64.Correct
import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerKept
import VerifiedGarbage.Proof.MillerRabin.AArch64.Prepared
import VerifiedGarbage.Proof.Bignum.AArch64.MontFnVerified
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerSaved

/-! # Calling the shared prepared round from a larger workspace -/

@[expose] public section

namespace VG.Proof.MillerRabin.AArch64.Caller

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.RsaKeyGen VG.Proof.RsaKeyGen.AArch64
open VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Impl.MillerRabin.AArch64 VG.Impl.MillerRabin.AArch64.Caller
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.MontFn (numAt_eq)

theorem call_ok (M : Mont) (name : String) (hnf : (round M.mm).noFrames = true)
    {s : State} {B : Addr} {Z w c bm b : Nat}
    (hc : MrCtx s B Z w c bm) (he : ECtx s.mem B w c)
    (h4 : 4 ≤ w) (h128 : w ≤ 128) (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (ho : c % 2 = 1) (h3 : 3 ≤ c)
    (hx : wv s.mem B (slot w aXm) w = b % c * 2 ^ (64 * w) % c) :
    WP isa (call name (round M.mm)) s fun t =>
      t.gpr .x0 = B ∧ abiPreserved s t ∧
      Frame [⟨B, 8 * (32 + 28 * (w + 2))⟩] s.mem t.mem ∧
      ∃ m : Mem, Proof.MillerRabin.Round.Keeps Proof.MillerRabin.Round.compact B (32 + 28 * (w + 2)) w
        (savedMem s B w) m ∧ t.mem = m.writeW (off B (8 * kFlag)) (mask (Proof.MillerRabin.Round.round c b)) := by
  let n := 32 + 28 * (w + 2)
  have hn : n < 2 ^ 64 := by dsimp only [n]; omega_arith
  have hsize : 8 * n ≤ Z := by
    simp only [n, slot, hdrBytes, aE] at hEZ ⊢
    omega_arith
  have hpad : pad w + 16 ≤ Z := by
    have hs : slot w 16 ≤ Z := hc.ws.hZ
    simp only [pad, slot, hdrBytes, aOne] at hs ⊢
    omega_arith
  unfold VG.Impl.MillerRabin.AArch64.Caller.call
  refine WP.seq (WP.mono (save_ok hc.good.1 hc.good.2 h128) fun u ⟨hm, h19, h1, hk⟩ => ?_)
  obtain ⟨hcu, heu⟩ := save_context hc he hEZ hm hk
  have hxu : wv u.mem B (slot w aXm) w = b % c * 2 ^ (64 * w) % c := by
    rw [hm, (saved_outside s B w (by have := hc.ws.scr.nowrap; omega_arith)).wv
      (Or.inl (by simp only [pad, slot, hdrBytes, aOne, aXm]; omega_arith))
      (by
        have hsX := slot_le (w := w) (show aXm < 8 by decide)
        have hsZ := hc.good.2
        have hsN := hc.ws.scr.nowrap
        omega_arith)]
    exact hx
  let e := u.callEntry.withRegions [] [⟨B, 8 * n⟩]
  have hEB : e.gpr .x0 = B := (u.callEntry_gpr (by decide)).trans hcu.ws.x0
  have hEN : e.gpr .x1 = BitVec.ofNat 64 n := (u.callEntry_gpr (by decide)).trans h1
  have hpre : roundPre e := by
    unfold roundPre
    rw [hEB, hEN, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · change ([⟨B, 8 * n⟩] : List Region) = [⟨B, n * 8⟩]
      rw [Nat.mul_comm]
    · have := hc.ws.scr.nowrap
      omega_arith
    · change Proof.MillerRabin.Round.Layout Proof.MillerRabin.Round.compact u.mem B n
      exact layout_of_ctx hcu h4 h128
    · change Proof.MillerRabin.Round.Prepared Proof.MillerRabin.Round.compact u.mem B
      apply prepared_of_ctx hcu heu ho h3
      rw [hxu]
      exact Nat.mod_lt _ (by omega_arith)
  have hcover : Covers [⟨B, 8 * n⟩] u.wr := by
    apply Covers.one
    have hs := hcu.ws.scr.region (d := 0) (n := 8 * n) (by omega_arith) (by dsimp only [n]; omega_arith)
    simpa only [InRegions, off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] using hs
  have hfSave : Frame [⟨B, 8 * n⟩] s.mem u.mem := by
    rw [hm]
    unfold savedMem
    refine Frame.writeW (Frame.writeW (Frame.refl _ _) (r := ⟨B, 8 * n⟩) (by simp) _ ?_)
      (r := ⟨B, 8 * n⟩) (by simp) _ ?_
    · exact Offset.contains_base B (by simp only [pad, n, slot, hdrBytes, aOne]; omega_arith)
        (by have := hc.ws.scr.nowrap; omega_arith)
    · exact Offset.contains_base B (by simp only [pad, n, slot, hdrBytes, aOne]; omega_arith)
        (by have := hc.ws.scr.nowrap; omega_arith)
  refine WP.seq (WP.callV (round_correct M) hpre (Covers.right hcover) hcover ?_ hnf)
  intro v hrd hwr hsp hf hregs hnever hvcs hp
  change roundPost e (v.withRegions [] [⟨B, 8 * n⟩]) at hp
  unfold roundPost at hp
  rw [hEB, hEN, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at hp
  have hwE : Proof.Rsa.Mont.wOf e.mem B = w := ctx_width (s := u) hcu
  have hcNum : Proof.Rsa.Mont.numAt e.mem B w 0 = c := (numAt_eq u.mem B w 0).trans hcu.n
  dsimp only at hp
  rw [hwE, hcNum] at hp
  change (∀ b', Proof.Rsa.Mont.numAt u.mem B w 5 = b' % c * 2 ^ (64 * w) % c →
    ((v.gpr .x0).setWidth 32).toNat = if Proof.MillerRabin.Round.round c b' then 1 else 0) ∧
    Proof.MillerRabin.Round.Keeps Proof.MillerRabin.Round.compact B n w u.mem v.mem at hp
  have hr := hp.1 b (by rw [numAt_eq]; exact hxu)
  have hWS : Scr v B Z := hcu.ws.scr.congr hwr
  have hW : word v.mem B (8 * sW) = BitVec.ofNat 64 w :=
    (kept_header hp.2 (by dsimp only [n]; omega_arith) (by decide) (by decide)).trans hcu.ws.hw
  have hA : word v.mem B (8 * sArr aOne) = off B (slot w aOne) :=
    (kept_header hp.2 (by dsimp only [n]; omega_arith) (by decide) (by decide)).trans (hcu.ws.harr aOne (by decide))
  have hOld : word v.mem B (pad w) = s.gpr .x19 := by
    have hp0 := kept_padding hp.2 (by
      simp only [pad, n, slot, hdrBytes, aOne]
      omega_arith) (by decide : 0 ≤ 8)
    have hp' : word v.mem B (pad w) = word u.mem B (pad w) := by
      simpa only [Nat.add_zero] using hp0
    rw [hp', hm]
    exact saved_x19 s B w (by have := hc.ws.scr.nowrap; omega_arith)
  have hLr : word v.mem B (pad w + 8) = s.gpr .x30 := by
    rw [kept_padding hp.2 (by unfold pad; simp only [n, slot, hdrBytes, aOne]; omega_arith) (by decide : 8 ≤ 8)]
    rw [hm]
    exact saved_x30 s B w
  refine WP.mono (restore_ok hWS hc.good.2 h128 ((hregs .x19 (by simp [preserved]) (by decide)).trans h19)
    hW hA hr hOld hLr) ?_
  rintro t ⟨hmt, hB, h19t, h30t, kt⟩
  refine ⟨hB, ⟨?_, ?_, ?_⟩, ?_, v.mem, ?_, hmt⟩
  · intro r hr'
    by_cases h : r = .x19
    · subst r
      exact h19t
    by_cases h' : r = .x30
    · subst r
      exact h30t
    exact (kt.gpr r (by revert r; decide)).trans
      ((hregs r hr' h').trans (hk.gpr r (by revert r; decide)))
  · exact kt.sp.trans (hsp.trans hk.sp)
  · intro r hr'
    exact (kt.vcs r hr').trans ((hvcs r hr').trans (hk.vcs r hr'))
  · rw [hmt]
    apply Frame.writeW (hfSave.trans hf) (r := ⟨B, 8 * n⟩) (by simp)
    exact Offset.contains_base B (by simp only [n, kFlag, kPlen, sFn]; omega_arith) (by decide)
  · rw [← hm]
    exact hp.2

end VG.Proof.MillerRabin.AArch64.Caller
