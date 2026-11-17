module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRawCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowReset
public import VerifiedGarbage.Proof.Bignum.CrtWindowFrame
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowCore
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRawSquares
import VerifiedGarbage.Proof.Bignum.CrtWindowRelation

/-! ### `Bignum.AArch64.CrtWindowRawCore`, which this module and modules that import it used -/

section

/-! A window's Montgomery relation for arbitrary reduced table entries. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

theorem windowCore_raw_ok (M : Mont) (S : Selector) {s : State} {P : Addr} {w v : Nat}
    {mi : BitVec 64} {X Xc : Nat} (hc : TableCtx s P w mi X Xc)
    (ht : CrtWindowFive.CTab s.mem P w X False 0)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hy : wv s.mem P (slot w aY) w < X)
    (hv : v < 32) (hnib : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa (VG.Impl.Rsa.AArch64.WindowFive.windowCore M.mm S.code) s fun t =>
      TableCtx t P w mi X Xc ∧ wv t.mem P (slot w aY) w < X ∧
      wv t.mem P (slot w aY) w * (2 ^ (64 * w)) ^ 32 % X =
        wv s.mem P (slot w aY) w ^ 32 * wv s.mem P (slot w (8 + v)) w % X ∧
      Frm P (crtWinRanges w) s.mem t.mem ∧ Keep mmRegs s t ∧
      (∀ k < 32, k ≠ Crt.sEnt → k ≠ Crt.sJ →
        word t.mem P (8 * k) = word s.mem P (8 * k)) := by
  unfold VG.Impl.Rsa.AArch64.WindowFive.windowCore
  refine wp_seqs_append (by simp) (by simp) ?_
  refine WP.mono (squares_scaled_ok M 4 (k := 0) (A := wv s.mem P (slot w aY) w)
    hc hw hw' hy (by simp)) fun a ⟨ca,ya,va,ha,fa,ka⟩ => ?_
  have ta := ht.of_win fa hc.scrT.nowrap
  have et : wv a.mem P (slot w (8 + v)) w = wv s.mem P (slot w (8 + v)) w :=
    fa.wv_eq (fun r hr => by have := crtWinRanges_ent w v r hr; omega_using [this])
      (by have := CrtWindowFive.ent32_le w hv; have := hc.scrT.nowrap; omega_arith)
  simp only [seqs]
  refine WP.seq (WP.mono (S.ok ca hw hw' hv ta.tab
    (by rw [ha _ (by decide)]; exact hnib)) fun b ⟨cb,tb,fb,kb⟩ => ?_)
  have ey := selection_keeps_y fb ca.good.scr.nowrap
  refine WP.mono (M.mm_ok (o := aY) (a := aY) (b := Crt.aT) cb.good (Nat.le_refl _) hw
    (by omega_using [hw']) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) cb.inv (by rw [cb.n,tb]; exact ta.lt v hv))
    fun t ⟨_,yt,vt,hat,kt⟩ => ?_
  rw [cb.n] at yt vt
  have ft : Frm P (crtWinRanges w) b.mem t.mem := Frm.of_arrays hat (by simp [crtWinRanges])
  have vb : wv b.mem P (slot w aY) w * (2 ^ (64 * w)) ^ 31 % X =
      wv s.mem P (slot w aY) w ^ 32 % X := by rw [ey]; exact va
  have result := CrtWindowFive.product_scale vt vb
  rw [tb,et] at result
  refine ⟨cb.of_win ft kt.wr (kt.gpr .x0 (by decide)),yt,result,
    (fa.trans (fb.mono (selRanges_sub w))).trans ft,
    ((ka.trans kb).trans kt).mono (by decide),?_⟩
  intro k hk he hj
  rw [hat.hslot hk, fb.word_eq (fun r hr => by
    simp only [selRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · have := hdr_lt_slot w Crt.aT hk; simp only; omega_using [this]
    · simp only; omega_using [he]
    · simp only; omega_using [hj]) (by
      have := hdr_lt_slot w 8 hk
      have := ca.good.scr.nowrap
      omega_using [hk]), ha k hk]

end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-! The complete window body, including reset and caller-state preservation. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowFive (windowBody)

theorem windowBody_raw_ok (M : Mont) (S : Selector) {s : State} {P : Addr} {w v : Nat}
    {mi : BitVec 64} {X Xc : Nat} (hc : TableCtx s P w mi X Xc)
    (ht : CrtWindowFive.CTab s.mem P w X False 0)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hy : wv s.mem P (slot w aY) w < X)
    (hv : v < 32) (hnib : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa (windowBody M.mm S.code) s fun t =>
      TableCtx t P w mi X Xc ∧ wv t.mem P (slot w aY) w < X ∧
      wv t.mem P (slot w aY) w * (2 ^ (64 * w)) ^ 32 % X =
        wv s.mem P (slot w aY) w ^ 32 * wv s.mem P (slot w (8 + v)) w % X ∧
      word t.mem P (8 * Crt.sNib) = 0 ∧ word t.mem P (8 * Crt.sBit) = 0 ∧
      Frm P (rawWindowRanges w) s.mem t.mem ∧ Keep mmRegs s t ∧
      (∀ k < 32, k ≠ Crt.sEnt → k ≠ Crt.sJ → k ≠ Crt.sNib → k ≠ Crt.sBit →
        word t.mem P (8 * k) = word s.mem P (8 * k)) := by
  unfold windowBody
  refine WP.seq (WP.mono (windowCore_raw_ok M S hc ht hw hw' hy hv hnib)
    fun u ⟨cu,yu,vu,fu,ku,hu⟩ => ?_)
  refine WP.mono (resetWindow_ok cu) fun t ⟨ct,yt,nt,bt,ft,kt,hh⟩ => ?_
  refine ⟨ct,yt.symm ▸ yu,?_,nt,bt,(fu.trans ft).window_tight ?_,(ku.trans kt).mono (by decide),?_⟩
  · rw [yt]; exact vu
  · exact (hh _ (by decide) (by decide) (by decide)).trans
      (hu _ (by decide) (by decide) (by decide))
  · intro k hk he hj hn hb
    exact (hh k hk hn hb).trans (hu k hk he hj)

theorem windowBody_raw_ct (M : Mont) (S : Selector) :
    RelCT isa (Two RawWindowPre) (windowBody M.mm S.code) (fun _ _ => True) := by
  unfold windowBody
  refine RelCT.seq (two_post (Ψ := fun (p : XPub) s => s.gpr .x0 = off p.B p.o)
    (windowCore_raw_ct M S) ?_)
    (two_map (fun p : XPub => off p.B p.o) (fun _ _ h => h) resetWindow_ct)
  rintro p s ⟨mi,X,Xc,v,hc,ht,hy,hw,hw',hv,hn⟩
  exact WP.mono (windowCore_raw_ok M S hc ht hw hw' hy hv hn)
    fun t ⟨ct,_⟩ => ct.good.x0

end VG.Proof.Bignum.AArch64.WindowFive
