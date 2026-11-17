module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowCore
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTable
import VerifiedGarbage.Proof.Bignum.CrtWindowRelation

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
