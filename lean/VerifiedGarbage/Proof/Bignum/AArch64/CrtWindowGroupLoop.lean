module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPrefixInv
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowLoop
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowTail
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowLoadGroup
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowAppliedStep
import VerifiedGarbage.Proof.Bignum.CrtWindowFive
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowAdvance
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowLoopControl
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Framework.Block

/-! ### `Bignum.AArch64.CrtWindowAppliedBatch`, which only this module used -/

section

/-! ### `Bignum.AArch64.CrtWindowAppliedGroup`, which only this module used -/

section

/-! The arithmetic composition of all eight windows in a five-byte group. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowFive (appliedGroup)

theorem appliedGroup_ok (W : Window) (n : Nat) {t : State} {P : Addr} {w : Nat}
    {mi : BitVec 64} {X Xc x E V : Nat} {Q : Prop}
    (hn : n ≤ 8) (hc : TableCtx t P w mi X Xc)
    (ht : CrtWindowFive.CTab t.mem P w X Q x)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) X)
    (hy : wv t.mem P (slot w aY) w < X)
    (hyv : Q → wv t.mem P (slot w aY) w % X = x ^ E * 2 ^ (64 * w) % X)
    (hV : word t.mem P (8 * Crt.sV) = BitVec.ofNat 64 V) (hV' : V < 2 ^ 64)
    (hbit : word t.mem P (8 * Crt.sBit) = 0)
    (hnib : word t.mem P (8 * Crt.sNib) = 0) :
    WP isa (appliedGroup W.code n) t fun u =>
      TableCtx u P w mi X Xc ∧ CrtWindowFive.CTab u.mem P w X Q x ∧
      wv u.mem P (slot w aY) w < X ∧
      (Q → wv u.mem P (slot w aY) w % X =
        x ^ (E * 32 ^ n + V % 32 ^ n) * 2 ^ (64 * w) % X) ∧
      word u.mem P (8 * Crt.sV) = BitVec.ofNat 64 V ∧
      word u.mem P (8 * Crt.sBit) = 0 ∧ word u.mem P (8 * Crt.sNib) = 0 ∧
      Frm P (crtWinRanges w) t.mem u.mem ∧ Keep mmRegs t u := by
  induction n generalizing t E with
  | zero =>
    apply WP.block_nil
    exact ⟨hc, ht, hy, by simpa only [Nat.pow_zero, Nat.mul_one, Nat.mod_one, Nat.add_zero] using hyv, hV, hbit, hnib, Frm.refl _ _ _, Keep.refl _ _⟩
  | succ n ih =>
    unfold appliedGroup
    refine WP.seq (WP.mono (appliedStep_ok W hc ht hw hw' hR hy hyv hV hV'
      (shift := 5 * n) (by omega_using [hn])) fun a ⟨ca, ta, ya, va, hVa, ba, na, fa, ka⟩ => ?_)
    refine WP.mono (ih (by omega_using [hn]) ca ta ya va hVa ba na) fun u ⟨cu, tu, yu, vu, hVu, bu, nu, fu, ku⟩ =>
      ⟨cu, tu, yu, ?_, hVu, bu, nu, fa.trans fu, (ka.trans ku).mono (by decide)⟩
    intro hQ
    rw [vu hQ, CrtWindowFive.group_reconstruct]

end VG.Proof.Bignum.AArch64.WindowFive

end

end


/-! A complete five-byte group contributes exactly its 40 exponent bits. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowFive (appliedBatch)

theorem appliedBatch_ok (W : Window) {s : State} {P src : Addr} {w i : Nat}
    {mi : BitVec 64} {X Xc x E : Nat} {Q : Prop} {bs : List Byte}
    (hc : TableCtx s P w mi X Xc) (ht : CrtWindowFive.CTab s.mem P w X Q x)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) X)
    (hy : wv s.mem P (slot w aY) w < X)
    (hyv : Q → wv s.mem P (slot w aY) w % X = x ^ E * 2 ^ (64 * w) % X)
    (hbit : word s.mem P (8 * Crt.sBit) = 0)
    (hnib : word s.mem P (8 * Crt.sNib) = 0)
    (hbs : 5 ≤ bs.length) (hp : word s.mem P (8 * Crt.sExp) = src)
    (hi : word s.mem P (8 * Crt.sI) = BitVec.ofNat 64 i)
    (hld : ∀ j < 5, InRegions (s.rd ++ s.wr) ((src + BitVec.ofNat 64 i) + BitVec.ofNat 64 j) 1)
    (hb : ∀ j (hj : j < 5), s.mem ((src + BitVec.ofNat 64 i) + BitVec.ofNat 64 j) = bs[j]'(by omega_using [hbs, hj])) :
    WP isa (appliedBatch W.code) s fun t =>
      TableCtx t P w mi X Xc ∧ CrtWindowFive.CTab t.mem P w X Q x ∧
      wv t.mem P (slot w aY) w < X ∧
      (Q → wv t.mem P (slot w aY) w % X = x ^ (E * 256 ^ 5 + pre bs 5) * 2 ^ (64 * w) % X) ∧
      word t.mem P (8 * Crt.sBit) = 0 ∧ word t.mem P (8 * Crt.sNib) = 0 ∧
      Frm P (crtWinRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold appliedBatch
  refine WP.seq (WP.mono (loadGroup_ok hc hbs hp hi hld hb) fun u ⟨hm,ku⟩ => ?_)
  have ho := writeW_outside s.mem P (d := 8 * Crt.sV) (BitVec.ofNat 64 (pre bs 5)) (by decide)
  rw [← hm] at ho
  have fu : Frm P (crtWinRanges w) s.mem u.mem := Frm.of_outside ho (by simp [crtWinRanges])
  have cu := hc.of_win fu ku.wr (ku.gpr .x0 (by decide))
  have tu := ht.of_win fu hc.scrT.nowrap
  have yu : wv u.mem P (slot w aY) w = wv s.mem P (slot w aY) w :=
    ho.wv (by have := hdr_lt_slot w aY (show Crt.sV < 32 by decide); omega_using [this])
      (by have := hc.good.scr.nowrap; have := slot_le (w := w) (show aY < 8 by decide); omega_arith)
  have hV := pre_lt bs hbs
  refine WP.mono (appliedGroup_ok W 8 (Q := Q) (x := x) (E := E) (V := pre bs 5)
    (by decide) cu tu hw hw' hR (yu.symm ▸ hy) (fun hQ => by rw [yu]; exact hyv hQ)
    (by rw [hm,word_writeW_self]) (by omega_using [hV])
    (by rw [hm,hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact hbit)
    (by rw [hm,hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact hnib)) fun t ⟨ct,tt,yt,vt,_,bt,nt,ft,kt⟩ => ?_
  refine ⟨ct,tt,yt,?_,bt,nt,fu.trans ft,(ku.trans kt).mono (by decide)⟩
  intro hQ
  simpa only [show 32 ^ 8 = 256 ^ 5 from rfl, Nat.mod_eq_of_lt hV] using vt hQ

end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-! ### `Bignum.CrtWindowPrefix`, which only this module used -/

section

/-! Append a contiguous block of exponent bytes without padding. -/

@[expose] public section
namespace VG.Proof.Bignum.CrtWindowFive
open VG VG.Proof.Bignum

theorem pre_append_drop (bs : List Byte) (i n : Nat) (h : i+n ≤ bs.length) :
    pre bs i * 256 ^ n + pre (bs.drop i) n = pre bs (i+n) := by
  induction n with
  | zero => simp only [Nat.pow_zero,Nat.mul_one,pre_zero,Nat.add_zero]
  | succ n ih =>
    rw [← Nat.add_assoc] at h ⊢
    rw [pre_succ (bs.drop i) (by simp only [List.length_drop]; omega_using [h]),
      pre_succ bs (by omega_using [h]),← ih (by omega_using [h]),Nat.pow_succ]
    simp only [List.getElem_drop]
    grind

end VG.Proof.Bignum.CrtWindowFive

end

end


/-! One five-byte group advances the public index and the exact exponent prefix. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep count_loop)
open VG.Impl.Rsa.AArch64.WindowFive (groupBody)

theorem groupBody_ok (W : Window) {s t : State} {P ep : Addr} {w i : Nat}
    {mi : BitVec 64} {X Xc x : Nat} {Q : Prop} {bs : List Byte}
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) X)
    (hL : bs.length < 2 ^ 64) (hi : i+5 ≤ bs.length)
    (hread : ∀ j < bs.length, InRegions (s.rd ++ s.wr) (ep + BitVec.ofNat 64 j) 1)
    (hbytes : ∀ j (hj : j < bs.length), s.mem (ep + BitVec.ofNat 64 j) = bs[j])
    (hout : ∀ j < bs.length, slot w 8 + CrtWindowFive.tabBytes32 w ≤ ofs P (ep + BitVec.ofNat 64 j))
    (h : PrefixInv s P w mi X Xc Q x ep bs i 0 t) :
    WP isa (groupBody W.code) t fun u =>
      PrefixInv s P w mi X Xc Q x ep bs (i+5) 0 u ∧
      u.gpr .x9 = if i+10 ≤ bs.length then 1 else 0 := by
  obtain ⟨E,v,_,hv,hK,hy,hyv,hn,bc⟩ := h.pending
  have vv : v = 0 := by simpa using hv
  have ek : E = pre bs i := by simpa [vv] using hK
  have hld : ∀ j < 5, InRegions (t.rd ++ t.wr) ((ep + BitVec.ofNat 64 i) + BitVec.ofNat 64 j) 1 := by
    intro j hj
    rw [h.keep.rd,h.keep.wr,BitVec.add_assoc,ofNat_add_ofNat]
    exact hread (i+j) (by omega_using [hi, hj])
  have hby : ∀ j (hj : j < 5), t.mem ((ep + BitVec.ofNat 64 i) + BitVec.ofNat 64 j) =
      (bs.drop i)[j]'(by simp only [List.length_drop]; omega_using [hi, hj]) := by
    intro j hj
    rw [BitVec.add_assoc,ofNat_add_ofNat,List.getElem_drop]
    exact h.source hbytes hout (by omega_using [hi, hj])
  unfold groupBody
  refine WP.seq (WP.mono (appliedBatch_ok W (E := pre bs i) h.ctx h.tab hw hw' hR hy
    (by simpa only [ek] using hyv) (by simpa using bc) (by simpa [vv] using hn)
    (bs := bs.drop i) (by simp only [List.length_drop]; omega_using [hi]) h.exp h.idx hld hby)
    fun a ⟨ca,ta,ya,va,ba,na,fa,ka⟩ => ?_)
  have pa : Pending a P w X Q x 0 (pre bs (i+5)) := by
    refine ⟨pre bs (i+5),0,by decide,by decide,by simp,ya,?_,na,ba⟩
    simpa only [CrtWindowFive.pre_append_drop bs i 5 hi] using va
  have headers := fun {k : Nat} => win_header (k := k) fa
  rw [WP.block_append_iff]
  refine WP.mono (advance_pending 5 (by decide) ca ta pa
    ((headers (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.idx))
    fun b ⟨cb,tb,pb,ib,fb,kb,hb⟩ => ?_
  have eb := (hb _ (by decide) (by decide)).trans
    ((headers (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.exp)
  have lb := (hb _ (by decide) (by decide)).trans
    ((headers (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.len)
  refine WP.mono (haveFive_ok cb hi hL ib lb) fun u ⟨⟨hm,h9⟩,ku⟩ => ?_
  have fu : Frm P (crtWinRanges w) b.mem u.mem := hm.symm ▸ Frm.refl _ _ _
  refine ⟨⟨cb.of_win fu ku.wr (ku.gpr .x0 (by decide)),hm.symm ▸ tb,
    by simpa only [Pending,hm] using pb,hm.symm ▸ ib,hm.symm ▸ eb,hm.symm ▸ lb,?_,?_⟩,?_⟩
  · rw [hm]
    exact (h.frm.trans (fa.mono (CrtWindowFive.crtWinRanges_sub w))).trans fb
  · exact (((h.keep.trans ka).trans kb).trans ku).mono (by decide)
  · simpa only [show i+5+5 = i+10 by omega_using []] using h9

end VG.Proof.Bignum.AArch64.WindowFive
