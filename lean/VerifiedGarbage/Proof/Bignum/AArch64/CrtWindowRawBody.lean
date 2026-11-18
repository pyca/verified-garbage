module

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowReset
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowCore
import VerifiedGarbage.Proof.Bignum.CrtWindowRelation
public import VerifiedGarbage.Proof.Bignum.CrtExp
import VerifiedGarbage.Proof.Bignum.FrameTrim
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTable

/-! ### `Bignum.AArch64.CrtWindowRawCT`, which this module and modules that import it used -/

section

/-! ### `Bignum.AArch64.CrtWindowRawSquares`, which this module and modules that import it used -/

section

/-! Montgomery scaling for arbitrary reduced accumulators, without a table-power assumption. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

theorem square_raw_ok (M : Mont) {s : State} {P : Addr} {w : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) (hw : 2 ≤ w) (hw' : w < 2 ^ 30)
    (hy : wv s.mem P (slot w aY) w < X) :
    WP isa (M.mm aY aY aY) s fun t => TableCtx t P w mi X Xc ∧
      wv t.mem P (slot w aY) w < X ∧
      wv t.mem P (slot w aY) w * 2 ^ (64 * w) % X =
        wv s.mem P (slot w aY) w * wv s.mem P (slot w aY) w % X ∧
      (∀ k < 32, word t.mem P (8 * k) = word s.mem P (8 * k)) ∧
      Frm P (crtWinRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (M.mm_ok (o := aY) (a := aY) (b := aY) hc.good (Nat.le_refl _) hw (by omega_using [hw'])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
    (by rw [hc.n]; exact hy)) fun t ⟨_,ht,hm,ha,kt⟩ => ?_
  rw [hc.n] at ht hm
  have hf : Frm P (crtWinRanges w) s.mem t.mem := Frm.of_arrays ha (by simp [crtWinRanges])
  exact ⟨hc.of_win hf kt.wr (kt.gpr .x0 (by decide)),ht,hm,fun k hk => ha.hslot hk,hf,kt⟩

theorem squares_scaled_ok (M : Mont) (n : Nat) {s : State} {P : Addr} {w k A : Nat}
    {mi : BitVec 64} {X Xc : Nat} (hc : TableCtx s P w mi X Xc)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hy : wv s.mem P (slot w aY) w < X)
    (hv : wv s.mem P (slot w aY) w * (2 ^ (64 * w)) ^ k % X = A % X) :
    WP isa (seqs (List.replicate (n + 1) (M.mm aY aY aY))) s fun t =>
      TableCtx t P w mi X Xc ∧ wv t.mem P (slot w aY) w < X ∧
      wv t.mem P (slot w aY) w * (2 ^ (64 * w)) ^ (2 ^ (n + 1) * k + (2 ^ (n + 1) - 1)) % X =
        A ^ (2 ^ (n + 1)) % X ∧
      (∀ i < 32, word t.mem P (8 * i) = word s.mem P (8 * i)) ∧
      Frm P (crtWinRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  induction n generalizing s k A with
  | zero =>
    exact WP.mono (square_raw_ok M hc hw hw' hy) fun t ⟨ct,yt,ht,hh,hf,hk⟩ =>
      ⟨ct,yt,CrtWindowFive.square_scale ht hv,hh,hf,hk⟩
  | succ n ih =>
    show WP isa (.seq (M.mm aY aY aY) (seqs (List.replicate (n + 1) (M.mm aY aY aY)))) s _
    refine WP.seq (WP.mono (square_raw_ok M hc hw hw' hy) fun u ⟨cu,yu,hu,hhu,fu,ku⟩ => ?_)
    refine WP.mono (ih (k := 2 * k + 1) (A := A ^ 2) cu yu (CrtWindowFive.square_scale hu hv))
      fun t ⟨ct,yt,vt,hht,ft,kt⟩ => ?_
    refine ⟨ct,yt,?_,fun i hi => (hht i hi).trans (hhu i hi),fu.trans ft,(ku.trans kt).mono (by decide)⟩
    have hp : 0 < 2 ^ (n + 1) := Nat.two_pow_pos _
    have he : 2 ^ (n + 1) * (2 * k + 1) + (2 ^ (n + 1) - 1) =
        2 ^ (n + 1 + 1) * k + (2 ^ (n + 1 + 1) - 1) := by
      rw [Nat.pow_succ 2 (n + 1), Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc]
      omega_using []
    rw [he] at vt
    have ep : (A ^ 2) ^ (2 ^ (n + 1)) = A ^ (2 ^ (n + 1 + 1)) := by
      rw [← Nat.pow_mul, Nat.mul_comm 2, ← Nat.pow_succ]
    rw [ep] at vt
    exact vt

end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-! Constant time for the raw relation, without table-power assumptions. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum

def RawWindowPre (p : XPub) (s : State) : Prop :=
  ∃ mi X Xc v, TableCtx s (off p.B p.o) p.wx mi X Xc ∧
    CrtWindowFive.CTab s.mem (off p.B p.o) p.wx X False 0 ∧
    wv s.mem (off p.B p.o) (slot p.wx aY) p.wx < X ∧
    2 ≤ p.wx ∧ p.wx < 2 ^ 30 ∧ v < 32 ∧
    word s.mem (off p.B p.o) (8 * Crt.sNib) = BitVec.ofNat 64 v

theorem rawSquare_post (M : Mont) {p : XPub} {s : State} (h : RawWindowPre p s) :
    WP isa (M.mm aY aY aY) s (RawWindowPre p) := by
  obtain ⟨mi,X,Xc,v,hc,ht,hy,hw,hw',hv,hn⟩ := h
  exact WP.mono (square_raw_ok M hc hw hw' hy) fun t ⟨ct,yt,_,hh,hf,_⟩ =>
    ⟨mi,X,Xc,v,ct,ht.of_win hf hc.scrT.nowrap,yt,hw,hw',hv,
      (hh _ (by decide)).trans hn⟩

theorem rawSquares_ct (M : Mont) (n : Nat) :
    RelCT isa (Two RawWindowPre)
      (seqs (List.replicate (n + 1) (M.mm aY aY aY))) (Two RawWindowPre) := by
  have one : RelCT isa (Two RawWindowPre) (M.mm aY aY aY) (Two RawWindowPre) :=
    two_post (Ψ := RawWindowPre)
      (two_map (fun p : XPub => p.ws)
        (fun _ _ ⟨mi,_,_,_,hc,_⟩ => ⟨mi,hc.good,Nat.le_refl _⟩)
        (M.ct (by simp [MmUse]))) (fun _ _ h => rawSquare_post M h)
  induction n with
  | zero => exact one
  | succ n ih => exact RelCT.seq one ih

theorem windowCore_raw_ct (M : Mont) (S : Selector) :
    RelCT isa (Two RawWindowPre)
      (VG.Impl.Rsa.AArch64.WindowFive.windowCore M.mm S.code) (fun _ _ => True) := by
  unfold VG.Impl.Rsa.AArch64.WindowFive.windowCore
  refine RelCT.seqs_append (by simp) (by simp) ?_
  refine RelCT.seq (rawSquares_ct M 4) ?_
  simp only [seqs]
  refine RelCT.seq (two_post (Ψ := fun p : XPub => GoodW p.ws)
    (two_map id ?_ S.ct) ?_)
    (two_map (fun p : XPub => p.ws) (fun _ _ h => h)
      (M.ct (o := aY) (a := aY) (b := Crt.aT) (by unfold MmUse; decide)))
  · rintro p s ⟨mi,X,Xc,v,hc,ht,_,hw,hw',hv,hn⟩
    exact ⟨mi,X,Xc,v,hc,hw,hw',hv,ht.tab,hn⟩
  · rintro p s ⟨mi,X,Xc,v,hc,ht,_,hw,hw',hv,hn⟩
    exact WP.mono (S.ok hc hw hw' hv ht.tab hn) fun t ⟨ct,_⟩ =>
      ⟨mi,ct.good,Nat.le_refl _⟩

end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-! ### `Bignum.CrtWindowFrame`, which this module and modules that import it used -/

section

/-! The window helper preserves the packed exponent word. -/

@[expose] public section
namespace VG.Proof.Bignum
open VG VG.Impl.Bignum VG.Impl.Bignum.Public

/-- A shared window touches four arithmetic arrays and four bookkeeping words. -/
def rawWindowRanges (w : Nat) : List (Nat × Nat) :=
  [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aY, 8 * (w + 2)),
    (slot w Crt.aT, 8 * (w + 2)), (8 * Crt.sBit, 8), (8 * Crt.sNib, 8),
    (8 * Crt.sEnt, 8), (8 * Crt.sJ, 8)]

theorem Frm.window_tight {B : Addr} {w : Nat} {m m' : Mem}
    (h : Frm B (crtWinRanges w) m m')
    (hv : word m' B (8 * Crt.sV) = word m B (8 * Crt.sV)) :
    Frm B (rawWindowRanges w) m m' := by
  apply Frm.drop_word (d := 8 * Crt.sV) _ hv
  exact h.mono (by simp [crtWinRanges, rawWindowRanges])

end VG.Proof.Bignum

end

end

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
