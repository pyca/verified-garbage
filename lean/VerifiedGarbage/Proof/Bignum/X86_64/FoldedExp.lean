module

import VerifiedGarbage.Proof.Bignum.X86_64.FoldedLoop
import VerifiedGarbage.Proof.Bignum.X86_64.PdExp
public import VerifiedGarbage.Proof.Rsa.X86_64.ExpCheck
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Impl.Rsa.X86_64.Folded
public import VerifiedGarbage.Proof.Bignum.EvenLast
public import VerifiedGarbage.Proof.Bignum.X86_64.Exp
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCounter
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

@[expose] public section

namespace VG.Proof.Bignum.X86_64.FoldedPublic
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64
open VG.Proof.Rsa.X86_64 (sat sat_lt)

theorem input_preserved {B : Addr} {w : Nat} {m m' : Mem}
    (h : Frm B (pExpRanges w) m m') (hb : B.toNat + slot w 8 ≤ 2^64) :
    wv m' B (slot w aX) w = wv m B (slot w aX) w := by
  apply h.wv_eq
  · intro r hr
    simp only [pExpRanges,pBitRanges,bitRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [slot,hdrBytes,sI,sV,sBit,Precomputed.sStarted,sFn,aX,aAcc,aTmp,aY] <;> omega
  · have := slot_le (w := w) (show aX < 8 by decide); omega

theorem sat_eq_65537 (e : Nat) : sat e = 65537 ↔ e = 65537 := by
  unfold sat
  split <;> omega

theorem dispatchTest_ok (s : State) {e : Nat} (he : s.gpr .r11 = BitVec.ofNat 64 (sat e)) :
    WP isa (.block [.alu .cmp .r11 (.imm 65537)]) s fun t =>
      t.zf = some (decide (e = 65537)) ∧ t.mem = s.mem ∧ Keep [.r11] s t := by
  have bound : sat e < 2^64 := by have := sat_lt e; omega
  refine WP.mono (WP.keep [.r11] (Q := fun t =>
    t.zf = some (decide (e = 65537)) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨hz,hm⟩,hk⟩ => ⟨hz,hm,hk⟩
  xrun [he,show BitVec.signExtend 64 (65537 : BitVec 32) = BitVec.ofNat 64 65537 from rfl,ofNat_sub_beq bound (show 65537 < 2^64 by decide)]
  exact decide_eq_decide.mpr (sat_eq_65537 e)

theorem src_bytesAt {s : State} {B : Addr} {Z : Nat} {p : Addr} {bs : List Byte} (h : VG.Proof.Bignum.X86_64.Src s B Z p bs) :
    Spec.Rsa.bytesAt s.mem p bs.length = bs := by
  apply List.ext_getElem (by rw [bytesAt_length])
  intro i h₁ h₂
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
  exact h.val i h₂

/-- `is65537`'s loads: `e` and its length from the header. -/
theorem is65537Load_ok {t : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {ep : Addr} {L : Nat}
    (hg : Good t B Z w mi) (hZ : slot w 8 ≤ Z) (he : word t.mem B (8*sE) = ep)
    (hlen : word t.mem B (8*sElen) = BitVec.ofNat 64 L) :
    WP isa (.block [.mov .r8 (.mem (hdr sE)), .mov .r9 (.mem (hdr sElen))]) t fun u =>
      u.gpr .r8 = ep ∧ u.gpr .r9 = BitVec.ofNat 64 L ∧ u.mem = t.mem ∧ Keep [.r8, .r9] t u := by
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  exact WP.mono (WP.keep [.r8, .r9] (Q := fun u => u.gpr .r8 = ep ∧ u.gpr .r9 = BitVec.ofNat 64 L ∧
      u.mem = t.mem) (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl sE (by decide), hl sElen (by decide), he, hlen]) rfl)
    fun u ⟨⟨h8, h9, hm⟩, k⟩ => ⟨h8, h9, hm, k⟩

/-- `is65537`'s check: ZF set iff `e` (the `L` bytes `eb` at `ep`, in `r8`
and `r9`) is 65537. -/
theorem is65537Check_ok {a : State} {B : Addr} {Z : Nat} {ep : Addr} {L : Nat} {eb : List Byte}
    (h8 : a.gpr .r8 = ep) (h9 : a.gpr .r9 = BitVec.ofNat 64 L) (hsrc : VG.Proof.Bignum.X86_64.Src a B Z ep eb)
    (hel : eb.length = L) (hL1 : 1 ≤ L) (hL' : L < 2^31) :
    WP isa (.seq Checked.expCheck (.block [.alu .cmp .r11 (.imm 65537)])) a fun u =>
      u.zf = some (decide (Spec.Rsa.os2ip eb = 65537)) ∧ u.mem = a.mem ∧ Keep [.rax, .r10, .r11] a u := by
  refine WP.seq (WP.mono (Rsa.X86_64.expCheckR_ok (eb := eb) h8 h9 hL1 (by omega)
    (fun i hi => hsrc.rd i (by omega))
    (by rw [← hel]; exact (src_bytesAt hsrc).symm)) fun b ⟨_, hmb, h11, kb⟩ => ?_)
  exact WP.mono (dispatchTest_ok b h11) fun u ⟨hz, hmu, ku⟩ =>
    ⟨hz, by rw [hmu, hmb], (kb.trans ku).mono (by decide)⟩

/-- `is65537`: ZF set iff `e` (the `L` bytes `eb` at `ep`) is 65537. -/
theorem is65537_ok {t : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {ep : Addr} {L : Nat} {eb : List Byte}
    (hg : Good t B Z w mi) (hZ : slot w 8 ≤ Z) (he : word t.mem B (8*sE) = ep)
    (hlen : word t.mem B (8*sElen) = BitVec.ofNat 64 L) (hsrc : VG.Proof.Bignum.X86_64.Src t B Z ep eb) (hel : eb.length = L)
    (hL1 : 1 ≤ L) (hL' : L < 2^31) :
    WP isa Folded.is65537 t fun u => u.zf = some (decide (Spec.Rsa.os2ip eb = 65537)) ∧ u.mem = t.mem ∧
      Keep [.rax, .r8, .r9, .r10, .r11] t u := by
  unfold Folded.is65537
  refine WP.seq (WP.mono (is65537Load_ok hg hZ he hlen) fun a ⟨h8, h9, hm, ka⟩ => ?_)
  have hs := hsrc.congr (by rw [hm]; exact InScr.refl _ _ _) ka.2.1 ka.2.2
  exact WP.mono (is65537Check_ok h8 h9 hs hel hL1 hL') fun u ⟨hz, hmu, ku⟩ =>
    ⟨hz, by rw [hmu, hm], (ka.trans ku).mono (by decide)⟩

/-- `exp65536`: `Y := X`, then sixteen squares. -/
theorem exp65536_ok (M : Mont) {s : State} {B : Addr} {Z w N X x : Nat} {mi : BitVec 64}
    (hc : ExpCtx s B Z w mi N X) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2^31)
    (hR : Nat.Coprime (2^(64*w)) N) (hX : X < N)
    (hx : X % N = x * 2^(64*w) % N) :
    WP isa (Folded.exp65536 M.mm) s fun t =>
      ExpCtx t B Z w mi N X ∧ wv t.mem B (slot w aY) w < N ∧
      wv t.mem B (slot w aY) w % N = x^65536 * 2^(64*w) % N ∧
      Frm B (pExpRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hb : B.toNat + slot w 8 ≤ 2^64 := by have := hc.good.scr.nowrap; omega
  unfold Folded.exp65536
  simp only [seqs]
  refine WP.seq (WP.mono (start_ok hc hZ (by omega) hw')
    fun a ⟨ca,ya,_,fa,ka⟩ => ?_)
  refine WP.seq (WP.mono (init_ok ca.good hZ) fun b ⟨mb,kb⟩ => ?_)
  have cb := ExpCtx.store ca hZ (i := sI) (by decide) (by decide) mb kb.2.2
    ((kb.gpr (by decide)).trans ca.good.rdi)
  have yb : wv b.mem B (slot w aY) w = X := by
    rw [mb,hdrStore_wv (i := sI) (j := aY) _ _ _ (by decide) (by decide) hb]; exact ya
  have countB : word b.mem B (8*sI) = 16 := by rw [mb,word_writeW_self]
  have fb : Frm B (pExpRanges w) a.mem b.mem := by
    rw [mb]
    exact Frm.of_outside (writeW_outside a.mem B (16 : BitVec 64) (d := 8*sI)
      (by have := hdr_lt_slot w 8 (show sI < 32 by decide); omega)) (by simp [pExpRanges])
  have fab : Frm B (pExpRanges w) s.mem b.mem :=
    (fa.mono (by simp [startRanges,pExpRanges,pBitRanges,bitRanges])).trans fb
  refine WP.mono (squares_ok M cb hZ hw hw' hR (by rw [yb]; exact hX)
    (by rw [yb]; exact hx) countB) fun c ic => ?_
  have fc : Frm B (pExpRanges w) b.mem c.mem :=
    ic.frame.mono (by simp [expRanges,pExpRanges,pBitRanges,bitRanges])
  have hv := ic.value
  rw [show (2 : Nat)^16 = 65536 by decide] at hv
  exact ⟨ic.ctx, ic.reduced, hv, fab.trans fc, ((ka.trans kb).trans ic.keep).mono (by decide)⟩

/-- `exp`: `x^(e-1) R`, by sixteen squares for `e = 65537` and the scan of
`e` with bit 0 of its last byte cleared otherwise. -/
theorem exp_ok (M : Mont) {s : State} {B : Addr} {Z w N X x : Nat} {mi : BitVec 64} {ep : Addr} {L : Nat}
    {eb : List Byte} (hc : ExpCtx s B Z w mi N X) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2^31)
    (hR : Nat.Coprime (2^(64*w)) N) (hX : X < N) (hx : X % N = x * 2^(64*w) % N)
    (he : word s.mem B (8*sE) = ep) (hlen : word s.mem B (8*sElen) = BitVec.ofNat 64 L)
    (hsrc : VG.Proof.Bignum.X86_64.Src s B Z ep eb) (hel : eb.length = L) (hL1 : 1 ≤ L) (hL' : L < 2^31)
    (hodd : Spec.Rsa.os2ip eb % 2 = 1) (h3 : 3 ≤ Spec.Rsa.os2ip eb) :
    WP isa (Folded.exp M.mm) s fun t => ExpCtx t B Z w mi N X ∧
      wv t.mem B (slot w aY) w < N ∧
      wv t.mem B (slot w aY) w % N = x^(Spec.Rsa.os2ip (evenLast eb)) * 2^(64*w) % N ∧
      Frm B (pExpRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hE := os2ip_evenLast hodd
  unfold Folded.exp
  refine WP.seq (WP.mono (is65537_ok hc.good hZ he hlen hsrc hel hL1 hL') fun a ⟨za, ma, ka⟩ => ?_)
  have ca : ExpCtx a B Z w mi N X := hc.mem ma ka (by decide)
  have fa : Frm B (pExpRanges w) s.mem a.mem := by rw [ma]; exact Frm.refl _ _ _
  refine WP.ite (decide (Spec.Rsa.os2ip eb = 65537)) (by simp [eval, za]) (fun hb => ?_) (fun hb => ?_)
  · have h65 : Spec.Rsa.os2ip eb = 65537 := by simpa using hb
    refine WP.mono (exp65536_ok M ca hZ hw hw' hR hX hx) fun t ⟨ct, lt, vt, ft, kt⟩ =>
      ⟨ct, lt, by rw [vt, show Spec.Rsa.os2ip (evenLast eb) = 65536 by omega], fa.trans ft,
        (ka.trans kt).mono (by decide)⟩
  · have hs := hsrc.congr (by rw [ma]; exact InScr.refl _ _ _) ka.2.1 ka.2.2
    refine WP.mono (pExpLoop_ok (M := M) (x := x) ca hZ hw hw' hR hX hx (by rw [ma]; exact he)
      (by rw [ma]; exact hlen) hel hL1 hL' (fun i hi => hs.rd i (by omega)) (fun i hi => hs.val i (by omega))
      (fun i hi => hs.out i (by omega))) fun t ⟨ct, yt, ft, kt⟩ => ?_
    rcases yt with ⟨h0, -⟩ | ⟨-, -, Y, hY, hYN, hYc⟩
    · omega
    exact ⟨ct, by rw [hY]; exact hYN, by rw [hY]; exact hYc, fa.trans ft, (ka.trans kt).mono (by decide)⟩

end VG.Proof.Bignum.X86_64.FoldedPublic
