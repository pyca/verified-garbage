module

public import VerifiedGarbage.Impl.Rsa.AArch64.WindowLoop
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPrefixInv
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBuild
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowLoadGroup
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTailByte
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowTail
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowAppliedStep
import VerifiedGarbage.Proof.Bignum.CrtWindowFive
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPendingInv
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTable
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Bignum.AArch64.CrtWindowAdvance`, which this module and modules that import it used -/

section

/-! ### `Bignum.AArch64.CrtWindowLoopControl`, which this module and modules that import it used -/

section

/-! All outer-loop tests depend only on the public exponent length and index. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowFive (haveFive advance loadTailByte remaining)

theorem haveFive_ok {s : State} {P : Addr} {w i L : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) (hi : i ≤ L) (hL : L < 2 ^ 64)
    (hidx : word s.mem P (8 * Crt.sI) = BitVec.ofNat 64 i)
    (hlen : word s.mem P (8 * Crt.sExpLen) = BitVec.ofNat 64 L) :
    WP isa (.block haveFive) s fun t =>
      (t.mem = s.mem ∧ t.gpr .x9 = if i + 5 ≤ L then 1 else 0) ∧ Keep [.x3,.x4,.x5,.x9] s t := by
  refine WP.keep _ ?_ rfl rfl rfl
  brun [haveFive,hc.good.x0,hdr_enc (show Crt.sI < 32 by decide),
    hdr_enc (show Crt.sExpLen < 32 by decide),hc.ld (i := Crt.sI) (by decide),
    hc.ld (i := Crt.sExpLen) (by decide),hidx,hlen,VG.Offset.ofNat_sub_ofNat hi,
    decide_eq_true_eq]
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show L-i < 2 ^ 64 by omega_using [hL])]
  change (if 18446744073709551616 ≤ L-i + 18446744073709551610 + 1 then (1#64) else 0) = _
  simp only [show (18446744073709551616 ≤ L-i + 18446744073709551610 + 1) ↔ i+5 ≤ L by omega_using []]
  rfl

theorem advance_ok (n : Nat) (hn : n < 4096) {s : State} {P : Addr} {w i : Nat}
    {mi : BitVec 64} {X Xc : Nat} (hc : TableCtx s P w mi X Xc)
    (hidx : word s.mem P (8 * Crt.sI) = BitVec.ofNat 64 i) :
    WP isa (.block (advance n)) s fun t =>
      t.mem = s.mem.writeW (off P (8 * Crt.sI)) (BitVec.ofNat 64 (i+n)) ∧ Keep [.x3] s t := by
  refine WP.keep _ ?_ rfl rfl rfl
  brun [advance,hc.good.x0,hdr_enc (show Crt.sI < 32 by decide),
    hc.ld (i := Crt.sI) (by decide),hc.st (i := Crt.sI) (by decide),hidx,hn,ofNat_add_ofNat]

theorem remaining_ok {s : State} {P : Addr} {w i L : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) (hi : i ≤ L)
    (hidx : word s.mem P (8 * Crt.sI) = BitVec.ofNat 64 i)
    (hlen : word s.mem P (8 * Crt.sExpLen) = BitVec.ofNat 64 L) :
    WP isa (.block remaining) s fun t =>
      (t.mem = s.mem ∧ t.gpr .x3 = BitVec.ofNat 64 (L-i)) ∧ Keep [.x3,.x4] s t := by
  refine WP.keep _ ?_ rfl rfl rfl
  brun [remaining,hc.good.x0,hdr_enc (show Crt.sI < 32 by decide),
    hdr_enc (show Crt.sExpLen < 32 by decide),hc.ld (i := Crt.sI) (by decide),
    hc.ld (i := Crt.sExpLen) (by decide),hidx,hlen,VG.Offset.ofNat_sub_ofNat hi]

end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-! Advancing the public byte index leaves the table and exponent unchanged. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowFive (advance)

theorem advance_pending (n : Nat) (hn : n < 4096) {s : State} {P : Addr} {w i b K : Nat}
    {mi : BitVec 64} {X Xc x : Nat} {Q : Prop}
    (hc : TableCtx s P w mi X Xc) (ht : CrtWindowFive.CTab s.mem P w X Q x)
    (hp : Pending s P w X Q x b K)
    (hidx : word s.mem P (8 * Crt.sI) = BitVec.ofNat 64 i) :
    WP isa (.block (advance n)) s fun t =>
      TableCtx t P w mi X Xc ∧ CrtWindowFive.CTab t.mem P w X Q x ∧
      Pending t P w X Q x b K ∧ word t.mem P (8 * Crt.sI) = BitVec.ofNat 64 (i+n) ∧
      Frm P (CrtWindowFive.crtExpRanges w) s.mem t.mem ∧ Keep [.x3] s t ∧
      (∀ k < 32, k ≠ Crt.sI → word t.mem P (8 * k) = word s.mem P (8 * k)) := by
  refine WP.mono (advance_ok n hn hc hidx) fun t ⟨hm,kt⟩ => ?_
  have out := writeW_outside s.mem P (d := 8 * Crt.sI) (BitVec.ofNat 64 (i+n)) (by decide)
  rw [← hm] at out
  have ft : Frm P (CrtWindowFive.crtExpRanges w) s.mem t.mem :=
    Frm.of_outside out (by simp [CrtWindowFive.crtExpRanges])
  have hh : ∀ k < 32, k ≠ Crt.sI → word t.mem P (8*k) = word s.mem P (8*k) := by
    intro k hk he
    rw [hm,hdrStore_hdr _ _ _ (by decide) hk (Ne.symm he)]
  have ea : ∀ j < 40, wv t.mem P (slot w j) w = wv s.mem P (slot w j) w := by
    intro j hj
    exact out.wv (by have := hdr_lt_slot w j (show Crt.sI < 32 by decide); omega_using [this]) (by
      have := hc.scrT.nowrap
      have hb := slot_mono w (show j+1 ≤ 40 by omega_using [hj])
      rw [slot_succ] at hb
      unfold slot hdrBytes CrtWindowFive.tabBytes32 at *
      omega_using [this, hb])
  refine ⟨hc.of_frm ft kt.wr (kt.gpr .x0 (by decide)),?_,?_,?_,ft,kt,hh⟩
  · exact ⟨(hh _ (by decide) (by decide)).trans ht.tab,
      fun j hj => (ea (8+j) (by omega_using [hj])).symm ▸ ht.lt j hj,
      fun hQ j hj => (ea (8+j) (by omega_using [hj])).symm ▸ ht.val hQ j hj⟩
  · obtain ⟨E,v,hb,hv,hK,hy,hyv,hv',hb'⟩ := hp
    exact ⟨E,v,hb,hv,hK,(ea aY (by decide)).symm ▸ hy,
      by simpa only [ea aY (by decide)] using hyv,
      (hh _ (by decide) (by decide)).trans hv',(hh _ (by decide) (by decide)).trans hb'⟩
  · rw [hm,word_writeW_self]

end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-! ### `Bignum.AArch64.CrtWindowGroups`, which the modules that import this one used -/

section

/-! ### `Bignum.AArch64.CrtWindowGroupLoop`, which this module and modules that import it used -/

section

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

end

end

/-! Consume all complete five-byte groups; the count depends only on length. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep count_loop)
open VG.Impl.Rsa.AArch64.WindowFive (expGroups)

theorem expGroups_ok (W : Window) {s t : State} {P ep : Addr} {w : Nat}
    {mi : BitVec 64} {X Xc x : Nat} {Q : Prop} {bs : List Byte}
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) X)
    (hL : bs.length < 2 ^ 64)
    (hread : ∀ j < bs.length, InRegions (s.rd ++ s.wr) (ep + BitVec.ofNat 64 j) 1)
    (hbytes : ∀ j (hj : j < bs.length), s.mem (ep + BitVec.ofNat 64 j) = bs[j])
    (hout : ∀ j < bs.length, slot w 8 + CrtWindowFive.tabBytes32 w ≤ ofs P (ep + BitVec.ofNat 64 j))
    (h : PrefixInv s P w mi X Xc Q x ep bs 0 0 t) :
    WP isa (expGroups W.code) t (PrefixInv s P w mi X Xc Q x ep bs (5*(bs.length/5)) 0) := by
  unfold expGroups
  refine WP.seq (WP.mono (haveFive_ok h.ctx (by omega_using []) hL h.idx h.len)
    fun a ⟨⟨hm,h9⟩,ka⟩ => ?_)
  have ha := h.keepMem hm ka (by decide) (by decide)
  by_cases hz : bs.length / 5 = 0
  · refine WP.ite false ?_ (by simp) (fun _ => ?_)
    · change some (!(a.gpr .x9 == 0)) = some false
      rw [h9]
      simp only [show ¬ 0+5 ≤ bs.length by omega_using [hz],ite_false]
      rfl
    · apply WP.block_nil
      simpa only [hz,Nat.mul_zero] using ha
  · refine WP.ite true ?_ (fun _ => ?_) (by simp)
    · change some (!(a.gpr .x9 == 0)) = some true
      rw [h9]
      simp only [show 0+5 ≤ bs.length by omega_using [hz],ite_true]
      rfl
    · apply count_loop (cr := .x9) (n := bs.length/5) (by omega_using [hz])
        (fun j => PrefixInv s P w mi X Xc Q x ep bs (5*j) 0)
      · intro j hj u hu
        refine WP.mono (groupBody_ok W hw hw' hR hL (by omega_using [hj]) hread hbytes hout hu)
          fun v ⟨hv,h9v⟩ => ⟨?_,?_⟩
        · simpa only [Nat.mul_add,Nat.mul_one] using hv
        · rw [h9v]
          split
          · change (1 ≠ 0 ↔ _)
            omega_arith
          · change (0 ≠ 0 ↔ _)
            omega_arith
      · simpa only [Nat.mul_zero] using ha

end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-! ### `Bignum.AArch64.CrtWindowTailLoop`, which this module and modules that import it used -/

section

/-! Trailing bytes extend the exact exponent prefix, carrying partial windows. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep count_loop)
open VG.Impl.Rsa.AArch64.WindowFive (tailBody)

theorem tailBody_ok (W : Window) {s t : State} {P ep : Addr} {w i b : Nat}
    {mi : BitVec 64} {X Xc x : Nat} {Q : Prop} {bs : List Byte}
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) X)
    (hi : i < bs.length)
    (hread : ∀ j < bs.length, InRegions (s.rd ++ s.wr) (ep + BitVec.ofNat 64 j) 1)
    (hbytes : ∀ j (hj : j < bs.length), s.mem (ep + BitVec.ofNat 64 j) = bs[j])
    (hout : ∀ j < bs.length, slot w 8 + CrtWindowFive.tabBytes32 w ≤ ofs P (ep + BitVec.ofNat 64 j))
    (h : PrefixInv s P w mi X Xc Q x ep bs i b t) :
    WP isa (tailBody W.code) t fun u =>
      PrefixInv s P w mi X Xc Q x ep bs (i+1) ((b+8)%5) u ∧
      u.gpr .x3 = BitVec.ofNat 64 (bs.length-(i+1)) := by
  unfold tailBody
  refine WP.seq (WP.mono (loadTailByte_ok h.ctx h.tab h.pending h.idx h.exp
    (by rw [h.keep.rd,h.keep.wr]; exact hread i hi) (h.source hbytes hout hi))
    fun a ⟨ca,ta,pa,va,fa,ka,ha⟩ => ?_)
  refine WP.seq (WP.mono (tailByte_ok W ca ta hw hw' hR pa (bs[i].isLt) va)
    fun c ⟨cc,tc,pc,fc,kc,_⟩ => ?_)
  have pc' : Pending c P w X Q x ((b+8)%5) (pre bs (i+1)) := by
    have he : pre bs i * 256 + bs[i].toNat = pre bs (i+1) := by
      rw [pre_succ bs hi,Nat.mul_comm (pre bs i) 256]
    simpa only [he] using pc
  have headers := fun {k : Nat} => win_header (k := k) fc
  have ic := (headers (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    ((ha _ (by decide) (by decide)).trans h.idx)
  have ec := (headers (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    ((ha _ (by decide) (by decide)).trans h.exp)
  have lc := (headers (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    ((ha _ (by decide) (by decide)).trans h.len)
  rw [WP.block_append_iff]
  refine WP.mono (advance_pending 1 (by decide) cc tc pc' ic)
    fun d ⟨cd,td,pd,id,fd,kd,hd⟩ => ?_
  have ed := (hd _ (by decide) (by decide)).trans ec
  have ld := (hd _ (by decide) (by decide)).trans lc
  refine WP.mono (remaining_ok cd (by omega_using [hi]) id ld) fun u ⟨⟨hm,h3⟩,ku⟩ => ?_
  have fu : Frm P (crtWinRanges w) d.mem u.mem := hm.symm ▸ Frm.refl _ _ _
  refine ⟨⟨cd.of_win fu ku.wr (ku.gpr .x0 (by decide)),hm.symm ▸ td,
    by simpa only [Pending,hm] using pd,hm.symm ▸ id,hm.symm ▸ ed,hm.symm ▸ ld,?_,?_⟩,h3⟩
  · rw [hm]
    exact (h.frm.trans ((fa.trans fc).mono (CrtWindowFive.crtWinRanges_sub w))).trans fd
  · exact ((((h.keep.trans ka).trans kc).trans kd).trans ku).mono (by decide)

end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-! Consume the remaining bytes, preserving the pending count across byte boundaries. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep count_loop)
open VG.Impl.Rsa.AArch64.WindowFive (expTail)

theorem expTail_ok (W : Window) {s t : State} {P ep : Addr} {w i : Nat}
    {mi : BitVec 64} {X Xc x : Nat} {Q : Prop} {bs : List Byte}
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) X)
    (hL : bs.length < 2 ^ 64) (hi : i ≤ bs.length)
    (hread : ∀ j < bs.length, InRegions (s.rd ++ s.wr) (ep + BitVec.ofNat 64 j) 1)
    (hbytes : ∀ j (hj : j < bs.length), s.mem (ep + BitVec.ofNat 64 j) = bs[j])
    (hout : ∀ j < bs.length, slot w 8 + CrtWindowFive.tabBytes32 w ≤ ofs P (ep + BitVec.ofNat 64 j))
    (h : PrefixInv s P w mi X Xc Q x ep bs i 0 t) :
    WP isa (expTail W.code) t
      (PrefixInv s P w mi X Xc Q x ep bs bs.length ((8*(bs.length-i))%5)) := by
  unfold expTail
  refine WP.seq (WP.mono (remaining_ok h.ctx hi h.idx h.len)
    fun a ⟨⟨hm,h3⟩,ka⟩ => ?_)
  have ha := h.keepMem hm ka (by decide) (by decide)
  by_cases hz : i = bs.length
  · refine WP.ite false ?_ (by simp) (fun _ => ?_)
    · change some (!(a.gpr .x3 == 0)) = some false
      rw [h3,hz,Nat.sub_self]; rfl
    · apply WP.block_nil
      simpa only [hz,Nat.sub_self,Nat.mul_zero,Nat.zero_mod] using ha
  · refine WP.ite true ?_ (fun _ => ?_) (by simp)
    · change some (!(a.gpr .x3 == 0)) = some true
      rw [h3]
      have nz : BitVec.ofNat 64 (bs.length-i) ≠ 0 := by
        intro he
        have he' := congrArg BitVec.toNat he
        simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show bs.length-i < 2 ^ 64 by omega_using [hL])] at he'
        change bs.length-i = 0 at he'
        omega_using [hi, hz, he']
      rw [beq_eq_false_iff_ne.mpr nz]; rfl
    · refine WP.mono (count_loop (cr := .x3) (n := bs.length-i) (by omega_using [hi, hz])
        (fun j => PrefixInv s P w mi X Xc Q x ep bs (i+j) ((8*j)%5)) ?_ ?_) fun u hu => ?_
      · intro j hj u hu
        refine WP.mono (tailBody_ok W hw hw' hR (by omega_using [hj]) hread hbytes hout hu)
          fun v ⟨hv,h3v⟩ => ⟨?_,?_⟩
        · have hb : ((8*j)%5+8)%5 = (8*(j+1))%5 := by omega_using []
          simpa only [hb,Nat.add_assoc] using hv
        · rw [h3v,cnt_ne (by omega_using [hL])]
          omega_using [hj]
      · simpa only [Nat.add_zero,Nat.mul_zero,Nat.zero_mod] using ha
      · simpa only [Nat.add_sub_of_le hi] using hu

end VG.Proof.Bignum.AArch64.WindowFive
