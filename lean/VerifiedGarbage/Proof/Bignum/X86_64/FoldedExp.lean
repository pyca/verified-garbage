module

public import VerifiedGarbage.Proof.Bignum.X86_64.PdExp
public import VerifiedGarbage.Proof.Rsa.X86_64.ExpCheck
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Impl.Rsa.X86_64.Folded
public import VerifiedGarbage.Proof.Bignum.X86_64.Exp
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont

/-! ### `Bignum.X86_64.FoldedLoop`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86_64.FoldedCounter`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.Bignum.X86_64.FoldedPublic
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

theorem next_ok {s : State} {B : Addr} {Z w n : Nat} {mi : BitVec 64}
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z)
    (hn : 1 ≤ n) (hn' : n < 2^31)
    (hc : word s.mem B (8*sI) = BitVec.ofNat 64 n) :
    WP isa (.block Folded.next) s fun t =>
      t.mem = s.mem.writeW (off B (8*sI)) (BitVec.ofNat 64 (n-1)) ∧
      t.zf = some (decide (n-1 = 0)) ∧ Keep [.rax] s t := by
  have bound : 8*sI+8 ≤ Z := by
    have := hdr_lt_slot w 8 (show sI < 32 by decide)
    unfold sI sFn at *; omega_using [hZ, this]
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    t.mem = s.mem.writeW (off B (8*sI)) (BitVec.ofNat 64 (n-1)) ∧
    t.zf = some (decide (n-1 = 0))) ?_ rfl) fun t ⟨⟨hm,hz⟩,hk⟩ => ⟨hm,hz,hk⟩
  unfold Folded.next
  xrun [State.ea, hdr, hg.rdi, hdrOff, hg.scr.ld bound, hg.scr.st bound,
    hc, ofNat64_pred hn (by omega_using [hn']), ofNat64_beq_zero (show n-1 < 2^64 by omega_using [hn'])]

theorem init_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z) :
    WP isa (.block [.mov32 .rax (.imm 16), .store (hdr sI) .rax]) s fun t =>
      t.mem = s.mem.writeW (off B (8*sI)) (16 : BitVec 64) ∧ Keep [.rax] s t := by
  have bound : 8*sI+8 ≤ Z := by
    have := hdr_lt_slot w 8 (show sI < 32 by decide)
    unfold sI sFn at *; omega_using [hZ, this]
  exact WP.keep [.rax] (by xrun [State.ea,hdr,hg.rdi,hdrOff,hg.scr.st bound]; rfl) rfl

end VG.Proof.Bignum.X86_64.FoldedPublic

end

end

/-! ### `Bignum.X86_64.FoldedStep`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.Bignum.X86_64.FoldedPublic
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

theorem squareStep_ok (M : Mont) {s : State} {B : Addr} {Z w N X x E n : Nat} {mi : BitVec 64}
    (hc : ExpCtx s B Z w mi N X) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2^31)
    (hR : Nat.Coprime (2^(64*w)) N)
    (hY : wv s.mem B (slot w aY) w < N)
    (hy : wv s.mem B (slot w aY) w % N = x^E * 2^(64*w) % N)
    (hn : 1 ≤ n) (hn' : n < 2^31)
    (hcount : word s.mem B (8*sI) = BitVec.ofNat 64 n) :
    WP isa (Folded.squareStep M.mm) s fun t =>
      ExpCtx t B Z w mi N X ∧ wv t.mem B (slot w aY) w < N ∧
      wv t.mem B (slot w aY) w % N = x^(2*E) * 2^(64*w) % N ∧
      word t.mem B (8*sI) = BitVec.ofNat 64 (n-1) ∧
      t.zf = some (decide (n-1 = 0)) ∧
      Frm B (expRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hbound : B.toNat + slot w 8 ≤ 2^64 := by have := hc.good.scr.nowrap; omega_using [hZ, this]
  unfold Folded.squareStep
  refine WP.seq (WP.mono (M.mm_ok hc.good hZ hw hw' (o := aY) (a := aY) (b := aY)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hc.inv (by rw [hc.n]; exact hY)) fun a ⟨ga,ya,ea,fa,ka⟩ => ?_)
  rw [hc.n] at ya ea
  have ca := hc.of_arrays ga hZ (by omega_using [hw]) fa
  have va := VG.Proof.Bignum.mont_sq hR hy ea
  have countA : word a.mem B (8*sI) = BitVec.ofNat 64 n := by
    rw [fa.hslot (by decide)]; exact hcount
  refine WP.mono (next_ok ga hZ hn hn' countA) fun t ⟨mt,zt,kt⟩ => ?_
  have yt : wv t.mem B (slot w aY) w = wv a.mem B (slot w aY) w := by
    rw [mt, hdrStore_wv (i := sI) (j := aY) _ _ _ (by decide) (by decide) hbound]
  refine ⟨ExpCtx.store ca hZ (i := sI) (by decide) (by decide) mt kt.2.2
      ((kt.gpr (by decide)).trans ga.rdi), yt ▸ ya, ?_, ?_, zt, ?_,
    (ka.trans kt).mono (by decide)⟩
  · rw [yt]; exact va
  · rw [mt, word_writeW_self]
  · refine (Frm.of_arrays fa (by simp [expRanges,bitRanges])).trans ?_
    rw [mt]
    exact Frm.of_outside (writeW_outside a.mem B _ (d := 8*sI)
      (by have := ga.scr.nowrap; have := hdr_lt_slot w 8 (show sI < 32 by decide); omega_using [hbound, this]))
      (by simp [expRanges])

end VG.Proof.Bignum.X86_64.FoldedPublic

end

end

@[expose] public section

namespace VG.Proof.Bignum.X86_64.FoldedPublic
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

structure SquareInv (s₀ : State) (B : Addr) (Z w N X x : Nat) (mi : BitVec 64)
    (i : Nat) (s : State) : Prop where
  ctx : ExpCtx s B Z w mi N X
  reduced : wv s.mem B (slot w aY) w < N
  value : wv s.mem B (slot w aY) w % N = x^(2^i) * 2^(64*w) % N
  count : word s.mem B (8*sI) = BitVec.ofNat 64 (16-i)
  frame : Frm B (expRanges w) s₀.mem s.mem
  keep : Keep mmRegs s₀ s

theorem loopStep_ok (M : Mont) {s₀ s : State} {B : Addr} {Z w N X x i : Nat} {mi : BitVec 64}
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2^31)
    (hR : Nat.Coprime (2^(64*w)) N) (hi : i < 16)
    (h : SquareInv s₀ B Z w N X x mi i s) :
    WP isa (Folded.squareStep M.mm) s fun t =>
      t.zf = some (decide (i+1 = 16)) ∧ SquareInv s₀ B Z w N X x mi (i+1) t := by
  refine WP.mono (squareStep_ok M h.ctx hZ hw hw' hR h.reduced h.value
    (by omega_using [hi]) (by omega_using []) h.count) fun t ⟨ctx,lt,val,count,zf,frame,keep⟩ => ?_
  have hp : 2 * 2^i = 2^(i+1) := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [hp] at val
  refine ⟨?_,ctx,lt,val,?_,h.frame.trans frame,(h.keep.trans keep).mono (by decide)⟩
  · rw [zf]; congr 1; exact decide_eq_decide.mpr (by omega_using [hi])
  · simpa only [Nat.sub_sub] using count

theorem squares_ok (M : Mont) {s : State} {B : Addr} {Z w N X x : Nat} {mi : BitVec 64}
    (hc : ExpCtx s B Z w mi N X) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2^31)
    (hR : Nat.Coprime (2^(64*w)) N)
    (hY : wv s.mem B (slot w aY) w < N)
    (hy : wv s.mem B (slot w aY) w % N = x * 2^(64*w) % N)
    (hcount : word s.mem B (8*sI) = 16) :
    WP isa (.loop (Folded.squareStep M.mm) .ne) s
      (SquareInv s B Z w N X x mi 16) := by
  apply wp_upto (a := 0) (N := 16) (by decide)
    (SquareInv s B Z w N X x mi)
    (fun _ _ hi _ h => loopStep_ok M hZ hw hw' hR hi h) (fun _ h => h)
  exact ⟨hc,hY,by simpa only [Nat.pow_zero,Nat.pow_one] using hy,
    hcount,Frm.refl _ _ _,Keep.refl _ _⟩

end VG.Proof.Bignum.X86_64.FoldedPublic

end

end

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
      simp only [slot,hdrBytes,sI,sV,sBit,Precomputed.sStarted,sFn,aX,aAcc,aTmp,aY] <;> omega_using []
  · have := slot_le (w := w) (show aX < 8 by decide); omega_using [hb, this]

theorem sat_eq_65537 (e : Nat) : sat e = 65537 ↔ e = 65537 := by
  unfold sat
  split <;> omega_arith

theorem dispatchTest_ok (s : State) {e : Nat} (he : s.gpr .r11 = BitVec.ofNat 64 (sat e)) :
    WP isa (.block [.alu .cmp .r11 (.imm 65537)]) s fun t =>
      t.zf = some (decide (e = 65537)) ∧ t.mem = s.mem ∧ Keep [.r11] s t := by
  have bound : sat e < 2^64 := by have := sat_lt e; omega_using [this]
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
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega_using [hZ, this])
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
  refine WP.seq (WP.mono (Rsa.X86_64.expCheckR_ok (eb := eb) h8 h9 hL1 (by omega_using [hL'])
    (fun i hi => hsrc.rd i (by omega_using [hel, hi]))
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
  have hb : B.toNat + slot w 8 ≤ 2^64 := by have := hc.good.scr.nowrap; omega_using [hZ, this]
  unfold Folded.exp65536
  simp only [seqs]
  refine WP.seq (WP.mono (start_ok hc hZ (by omega_using [hw]) hw')
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
      (by have := hdr_lt_slot w 8 (show sI < 32 by decide); omega_using [hb, this])) (by simp [pExpRanges])
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
      ⟨ct, lt, by rw [vt, show Spec.Rsa.os2ip (evenLast eb) = 65536 by omega_using [hE, h65]], fa.trans ft,
        (ka.trans kt).mono (by decide)⟩
  · have hs := hsrc.congr (by rw [ma]; exact InScr.refl _ _ _) ka.2.1 ka.2.2
    refine WP.mono (pExpLoop_ok (M := M) (x := x) ca hZ hw hw' hR hX hx (by rw [ma]; exact he)
      (by rw [ma]; exact hlen) hel hL1 hL' (fun i hi => hs.rd i (by omega_using [hel, hi])) (fun i hi => hs.val i (by omega_using [hel, hi]))
      (fun i hi => hs.out i (by omega_using [hel, hi]))) fun t ⟨ct, yt, ft, kt⟩ => ?_
    rcases yt with ⟨h0, -⟩ | ⟨-, -, Y, hY, hYN, hYc⟩
    · omega
    exact ⟨ct, by rw [hY]; exact hYN, by rw [hY]; exact hYc, fa.trans ft, (ka.trans kt).mono (by decide)⟩

end VG.Proof.Bignum.X86_64.FoldedPublic
