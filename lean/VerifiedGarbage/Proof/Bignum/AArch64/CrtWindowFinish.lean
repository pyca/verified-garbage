module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPendingInv
import VerifiedGarbage.Proof.Bignum.AArch64.CrtExp
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowTail
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTable
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBuild
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowCore

/-! ### `Bignum.AArch64.CrtWindowFinishSquare`, which this module and modules that import it used -/

section

/-! Final pending bits need exactly their own count of squares, without padding. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep count_loop)
open VG.Impl.Rsa.AArch64.WindowFive (finishSquare)

theorem finishSquare_ok (M : Mont) {s : State} {P : Addr} {w b E : Nat}
    {mi : BitVec 64} {X Xc x : Nat} {Q : Prop}
    (hc : TableCtx s P w mi X Xc) (ht : CrtWindowFive.CTab s.mem P w X Q x)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) X)
    (hy : wv s.mem P (slot w aY) w < X)
    (hyv : Q → wv s.mem P (slot w aY) w % X = x ^ E * 2 ^ (64 * w) % X)
    (hb : 1 ≤ b) (bc : word s.mem P (8 * Crt.sBit) = BitVec.ofNat 64 b) :
    WP isa (finishSquare M.mm) s fun t =>
      TableCtx t P w mi X Xc ∧ CrtWindowFive.CTab t.mem P w X Q x ∧
      wv t.mem P (slot w aY) w < X ∧
      (Q → wv t.mem P (slot w aY) w % X = x ^ (2 * E) * 2 ^ (64 * w) % X) ∧
      word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 (b - 1) ∧
      t.gpr .x3 = BitVec.ofNat 64 (b - 1) ∧
      Frm P (crtWinRanges w) s.mem t.mem ∧ Keep mmRegs s t ∧
      (∀ k < 32, k ≠ Crt.sBit → word t.mem P (8 * k) = word s.mem P (8 * k)) := by
  unfold finishSquare
  refine WP.seq (WP.mono (crtSq_ok M hc.base hw hw' hR hy hyv)
    fun u ⟨_,yu,vu,hu,fu,ku⟩ => ?_)
  have cu := hc.of_win fu ku.wr (ku.gpr .x0 (by decide))
  have tu := ht.of_win fu hc.scrT.nowrap
  refine WP.mono (crtBitEnd_ok cu (b := b) (by rw [hu _ (by decide)]; exact bc) hb)
    fun t ⟨⟨hm,h3⟩,kt⟩ => ?_
  have out := writeW_outside u.mem P (d := 8 * Crt.sBit) (BitVec.ofNat 64 (b - 1)) (by decide)
  rw [← hm] at out
  have ft : Frm P (crtWinRanges w) u.mem t.mem := Frm.of_outside out (by simp [crtWinRanges])
  have ey : wv t.mem P (slot w aY) w = wv u.mem P (slot w aY) w :=
    out.wv (by have := hdr_lt_slot w aY (show Crt.sBit < 32 by decide); omega_using [this]) (by
      have := cu.good.scr.nowrap
      have := slot_le (w := w) (show aY < 8 by decide)
      omega_arith)
  refine ⟨cu.of_win ft kt.wr (kt.gpr .x0 (by decide)),tu.of_win ft cu.scrT.nowrap,
    ey.symm ▸ yu,?_,?_,h3,fu.trans ft,(ku.trans kt).mono (by decide),?_⟩
  · intro hQ; rw [ey]; exact vu hQ
  · rw [hm,word_writeW_self]
  · intro k hk he
    rw [hm,hdrStore_hdr _ _ _ (by decide) hk (Ne.symm he),hu k hk]

/-- State after `i` of the final `b` squarings. -/
def FinishInv (s : State) (P : Addr) (w : Nat) (mi : BitVec 64) (X Xc : Nat)
    (Q : Prop) (x E b i : Nat) (t : State) : Prop :=
  TableCtx t P w mi X Xc ∧ CrtWindowFive.CTab t.mem P w X Q x ∧
  wv t.mem P (slot w aY) w < X ∧
  (Q → wv t.mem P (slot w aY) w % X = x ^ (2 ^ i * E) * 2 ^ (64 * w) % X) ∧
  word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 (b - i) ∧
  Frm P (crtWinRanges w) s.mem t.mem ∧ Keep mmRegs s t ∧
  (∀ k < 32, k ≠ Crt.sBit → word t.mem P (8 * k) = word s.mem P (8 * k))

theorem finishSquares_ok (M : Mont) {s : State} {P : Addr} {w b E : Nat}
    {mi : BitVec 64} {X Xc x : Nat} {Q : Prop}
    (hc : TableCtx s P w mi X Xc) (ht : CrtWindowFive.CTab s.mem P w X Q x)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) X)
    (hy : wv s.mem P (slot w aY) w < X)
    (hyv : Q → wv s.mem P (slot w aY) w % X = x ^ E * 2 ^ (64 * w) % X)
    (hb : 1 ≤ b) (hb' : b < 5) (bc : word s.mem P (8 * Crt.sBit) = BitVec.ofNat 64 b) :
    WP isa (.loop (finishSquare M.mm) (.nonzero .x .x3)) s
      (FinishInv s P w mi X Xc Q x E b b) := by
  apply count_loop (cr := .x3) (n := b) hb (FinishInv s P w mi X Xc Q x E b)
  · intro i hi u hu
    obtain ⟨cu,tu,yu,vu,bc,fu,ku,hh⟩ := hu
    refine WP.mono (finishSquare_ok M cu tu hw hw' hR yu vu (by omega_using [hi]) bc)
      fun t ⟨ct,tt,yt,vt,bt,h3,ft,kt,hh'⟩ => ⟨?_,?_⟩
    · refine ⟨ct,tt,yt,?_,?_,fu.trans ft,(ku.trans kt).mono (by decide),
        fun k hk he => (hh' k hk he).trans (hh k hk he)⟩
      · intro hQ
        rw [vt hQ]
        congr 3
        simp only [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]
      · simpa only [Nat.sub_sub] using bt
    · rw [h3,cnt_ne (by omega_using [hb'])]
      omega_using [hi]
  · exact ⟨hc,ht,hy,by simpa using hyv,by simpa using bc,Frm.refl _ _ _,Keep.refl _ _,fun _ _ _ => rfl⟩

end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-! A final partial window consumes exactly the pending exponent bits. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowFive (finish)

theorem selectProduct_ok (M : Mont) (S : Selector) {s : State} {P : Addr} {w E v : Nat}
    {mi : BitVec 64} {X Xc x : Nat} {Q : Prop}
    (hc : TableCtx s P w mi X Xc) (ht : CrtWindowFive.CTab s.mem P w X Q x)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) X)
    (hyv : Q → wv s.mem P (slot w aY) w % X = x ^ E * 2 ^ (64 * w) % X)
    (hv : v < 32) (hn : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa (.seq S.code (M.mm aY aY Crt.aT)) s fun t =>
      TableCtx t P w mi X Xc ∧ CrtWindowFive.CTab t.mem P w X Q x ∧
      wv t.mem P (slot w aY) w < X ∧
      (Q → wv t.mem P (slot w aY) w % X = x ^ (E + v) * 2 ^ (64 * w) % X) ∧
      Frm P (crtWinRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.seq (WP.mono (S.ok hc hw hw' hv ht.tab hn)
    fun u ⟨cu,tu,fu,ku⟩ => ?_)
  have fu' := fu.mono (selRanges_sub w)
  have tabu := ht.of_win fu' hc.scrT.nowrap
  have ey := selection_keeps_y fu hc.good.scr.nowrap
  refine WP.mono (crtMulT_ok M (Q := Q) (x := x) (E := E) (v := v) cu.base hw hw' hR
    (by rw [tu]; exact ht.lt v hv)
    (by intro hQ; rw [ey]; exact hyv hQ)
    (by intro hQ; rw [tu]; exact ht.val hQ v hv))
    fun t ⟨_,yt,vt,_,ft,kt⟩ => ?_
  exact ⟨cu.of_win ft kt.wr (kt.gpr .x0 (by decide)),tabu.of_win ft cu.scrT.nowrap,
    yt,vt,fu'.trans ft,(ku.trans kt).mono (by decide)⟩

theorem finishLoad_ok {s : State} {P : Addr} {w b : Nat}
    {mi : BitVec 64} {X Xc : Nat} (hc : TableCtx s P w mi X Xc)
    (bc : word s.mem P (8 * Crt.sBit) = BitVec.ofNat 64 b) :
    WP isa (.block [ldh .x3 Crt.sBit]) s fun t =>
      (t.mem = s.mem ∧ t.gpr .x3 = BitVec.ofNat 64 b) ∧ Keep [.x3] s t := by
  refine WP.keep _ ?_ rfl rfl rfl
  brun [hc.good.x0,hdr_enc (show Crt.sBit < 32 by decide),hc.ld (i := Crt.sBit) (by decide),bc]

/-- No padding: the final exponent is precisely the completed prefix and
its pending `b` bits, including the empty-tail case. -/
theorem finish_ok (M : Mont) (S : Selector) {s : State} {P : Addr} {w b K : Nat}
    {mi : BitVec 64} {X Xc x : Nat} {Q : Prop}
    (hc : TableCtx s P w mi X Xc) (ht : CrtWindowFive.CTab s.mem P w X Q x)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) X)
    (hp : Pending s P w X Q x b K) :
    WP isa (finish M.mm S.code) s fun t =>
      TableCtx t P w mi X Xc ∧ CrtWindowFive.CTab t.mem P w X Q x ∧
      wv t.mem P (slot w aY) w < X ∧
      (Q → wv t.mem P (slot w aY) w % X = x ^ K * 2 ^ (64 * w) % X) ∧
      Frm P (crtWinRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  obtain ⟨E,v,hb,hv,hK,hy,hyv,hn,bc⟩ := hp
  unfold finish
  refine WP.seq (WP.mono (finishLoad_ok hc bc) fun u ⟨⟨hm,h3⟩,ku⟩ => ?_)
  have fu : Frm P (crtWinRanges w) s.mem u.mem := hm.symm ▸ Frm.refl _ _ _
  have cu := hc.of_win fu ku.wr (ku.gpr .x0 (by decide))
  have tu := ht.of_win fu hc.scrT.nowrap
  by_cases hz : b = 0
  · subst b
    have vv : v = 0 := by simpa using hv
    have ek : E = K := by simpa [vv] using hK
    refine WP.ite false ?_ (by simp) (fun _ => ?_)
    · change some (!(u.gpr .x3 == 0)) = some false
      rw [h3]; rfl
    · apply WP.block_nil
      exact ⟨cu,tu,hm.symm ▸ hy,by simpa [hm,← ek] using hyv,fu,ku.mono (by decide)⟩
  · refine WP.ite true ?_ (fun _ => ?_) (by simp)
    · change some (!(u.gpr .x3 == 0)) = some true
      rw [h3]
      have nz : BitVec.ofNat 64 b ≠ 0 := by
        intro h
        have he := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega_using [hb])] at he
        exact hz he
      rw [beq_eq_false_iff_ne.mpr nz]
      rfl
    · refine WP.seq (WP.mono (finishSquares_ok M (E := E) cu tu hw hw' hR (hm.symm ▸ hy)
        (by simpa [hm] using hyv) (by omega_using [hz]) hb (by simpa [hm] using bc))
        fun a ⟨ca,ta,_,va,_,fa,ka,ha⟩ => ?_)
      refine WP.mono (selectProduct_ok M S (E := 2 ^ b * E) (v := v) ca ta hw hw' hR va
        (by have := pending_lt16 hb hv; omega_using [this])
        (by rw [ha _ (by decide) (by decide),hm]; exact hn))
        fun t ⟨ct,tt,yt,vt,ft,kt⟩ => ?_
      refine ⟨ct,tt,yt,?_,(fu.trans fa).trans ft,((ku.trans ka).trans kt).mono (by decide)⟩
      intro hQ
      simpa only [Nat.mul_comm (2 ^ b) E,hK] using vt hQ

end VG.Proof.Bignum.AArch64.WindowFive
