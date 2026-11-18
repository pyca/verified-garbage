module

public import VerifiedGarbage.Impl.Rsa.AArch64.WindowLoop
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowHead
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtFrame
public import VerifiedGarbage.Proof.Bignum.CrtWindowFiveLayout
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPrefixInv
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTails
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowFinish

/-! ### `Bignum.AArch64.CrtWindowRun`, which this module and modules that import it used -/

section

/-! Complete exponentiation through shared five-bit windows and exact tails. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowFive (expRun)

theorem expRun_ok (W : Window) (M : Mont) (S : Selector) {s t : State} {P ep : Addr} {w : Nat}
    {mi : BitVec 64} {X Xc x : Nat} {Q : Prop} {bs : List Byte}
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) X)
    (hL : bs.length < 2 ^ 64)
    (hread : ∀ j < bs.length, InRegions (s.rd ++ s.wr) (ep + BitVec.ofNat 64 j) 1)
    (hbytes : ∀ j (hj : j < bs.length), s.mem (ep + BitVec.ofNat 64 j) = bs[j])
    (hout : ∀ j < bs.length, slot w 8 + CrtWindowFive.tabBytes32 w ≤ ofs P (ep + BitVec.ofNat 64 j))
    (h : PrefixInv s P w mi X Xc Q x ep bs 0 0 t) :
    WP isa (expRun W.code M.mm S.code) t fun u =>
      TableCtx u P w mi X Xc ∧ CrtWindowFive.CTab u.mem P w X Q x ∧
      wv u.mem P (slot w aY) w < X ∧
      (Q → wv u.mem P (slot w aY) w % X = x ^ Spec.Rsa.os2ip bs * 2 ^ (64 * w) % X) ∧
      Frm P (CrtWindowFive.crtExpRanges w) s.mem u.mem ∧ Keep mmRegs s u := by
  unfold expRun
  refine WP.seq (WP.mono (expGroups_ok W hw hw' hR hL hread hbytes hout h) fun a ha => ?_)
  refine WP.seq (WP.mono (expTail_ok W hw hw' hR hL (by omega_using []) hread hbytes hout ha) fun b hb => ?_)
  refine WP.mono (finish_ok M S hb.ctx hb.tab hw hw' hR hb.pending)
    fun u ⟨cu,tu,yu,vu,fu,ku⟩ => ?_
  exact ⟨cu,tu,yu,by simpa only [pre_len] using vu,
    hb.frm.trans (fu.mono (CrtWindowFive.crtWinRanges_sub w)),(hb.keep.trans ku).mono (by decide)⟩

end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-! ### `Bignum.AArch64.CrtWindowFrameContext`, which this module and modules that import it used -/

section

/-! The wider table leaves the modulus and prime workspace headers unchanged. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Proof.Bignum

theorem subCtx_of_wide {s t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {rs : List (Nat × Nat)}
    (h : SubCtx s B Z o w wx minv)
    (hwide : o + slot wx 8 + CrtWindowFive.tabBytes32 wx ≤ Z) (hf : Frm (off B o) rs s.mem t.mem)
    (hr : ∀ r ∈ rs, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot wx 8 + CrtWindowFive.tabBytes32 wx) (hwr : t.wr = s.wr)
    (h0 : t.gpr .x0 = s.gpr .x0) : SubCtx t B Z o w wx minv := by
  have hn := h.scr.nowrap
  have hi := hwide
  have hL : o + (slot wx 8 + CrtWindowFive.tabBytes32 wx) ≤ 2 ^ 64 := by omega_using [hwide, hn]
  have hr' : ∀ r ∈ rs, r.1 + r.2 ≤ slot wx 8 + CrtWindowFive.tabBytes32 wx := fun r hr' => (hr r hr').2
  have hh : ∀ i < 17, word t.mem (off B o) (8 * i) = word s.mem (off B o) (8 * i) := fun i hi' =>
    hf.word_eq (fun r hr' => Or.inl (by have := hr r hr'; omega_using [hi', this]))
      (by have : 8 * 32 ≤ slot wx 8 := by unfold slot hdrBytes; omega_using []
          omega_using [hi'])
  have hb : ∀ i < 32, word t.mem B (8 * i) = word s.mem B (8 * i) := fun i hi' =>
    hf.word_below hr' hL (by unfold slot hdrBytes at hL; omega_using [hL]) (by have := hdr_lt_slot w 8 hi'; have := h.lo; omega_arith)
  exact ⟨h.scr.congr hwr, h0.trans h.x0,
    ⟨(hh _ (by decide)).trans h.hdr.hw, (hh _ (by decide)).trans h.hdr.hminv,
      fun j hj => (hh _ (by unfold sArr; omega_using [hj])).trans (h.hdr.harr j hj)⟩,
    (hh _ (by decide)).trans h.link, (hb _ (by decide)).trans h.nw,
    fun j hj => (hb _ (by unfold sArr; omega_using [hj])).trans (h.narr j hj), h.lo, h.hi⟩

end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-! Five-bit prime exponentiation with an explicitly bounded wider table. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

theorem expLoop_ok (W : Window) (M : Mont) (S : Selector) {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {X x : Nat}
    {Q : Prop} (hc : SubCtx s B Z o w wx minv)
    (hwide : o + slot wx 8 + CrtWindowFive.tabBytes32 wx ≤ Z) (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hn : wv s.mem (off B o) (slot wx aN) wx = X)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hodd : X % 2 = 1)
    (hxl : wv s.mem (off B o) (slot wx Crt.aXc) wx < X)
    (hxc : Q → wv s.mem (off B o) (slot wx Crt.aXc) wx % X = x * 2 ^ (64 * wx) % X)
    (hyl : wv s.mem (off B o) (slot wx aY) wx < X)
    (hyc : Q → wv s.mem (off B o) (slot wx aY) wx % X = 2 ^ (64 * wx) % X)
    {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) {ep : Addr} {eb : List Byte}
    (hep : word s.mem B (8 * sp) = ep) (hel : word s.mem B (8 * sl) = BitVec.ofNat 64 eb.length)
    (hL1 : 1 ≤ eb.length) (hL2 : eb.length ≤ 1024) (he : Src s B Z ep eb) :
    WP isa (VG.Impl.Rsa.AArch64.WindowFive.expLoop W.code M.mm S.code sp sl) s fun t => SubCtx t B Z o w wx minv ∧
      wv t.mem (off B o) (slot wx aY) wx < X ∧
      (Q → wv t.mem (off B o) (slot wx aY) wx % X = x ^ Spec.Rsa.os2ip eb * 2 ^ (64 * wx) % X) ∧
      Frm (off B o) (CrtWindowFive.crtExpRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  have hi := hwide
  have hlo := hc.lo
  have hBn := hc.scr.nowrap
  have hT : Scr s (off B o) (slot wx 8 + CrtWindowFive.tabBytes32 wx) :=
    hc.scr.sub (by omega) (by unfold slot hdrBytes; omega)
  have hPn := hT.nowrap
  have h256 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_arith
  have hR : Nat.Coprime (2 ^ (64 * wx)) X := VG.Proof.Bignum.coprime_pow2 hodd _
  have hout : ∀ i < eb.length, slot wx 8 + CrtWindowFive.tabBytes32 wx ≤ ofs (off B o) (ep + BitVec.ofNat 64 i) := fun i hi' => by
    have := he.out i hi'
    rcases ofs_rebase B (ep + BitVec.ofNat 64 i) (o := o) (by omega_arith) with ⟨_, h2⟩ | ⟨h1, _⟩
    · omega_arith
    · omega_arith
  unfold VG.Impl.Rsa.AArch64.WindowFive.expLoop
  refine WP.seq (WP.mono (expHead_ok M hc hT hw2 hwx hw30 hn hinv hodd hxl hxc hyl hyc
    hsp hsl hep hel) fun t ht => ?_)
  refine WP.mono (expRun_ok W M S hw2 (by omega) hR (by omega) he.rd he.val hout ht)
    fun u ⟨_,_,yu,vu,fu,ku⟩ => ?_
  exact ⟨subCtx_of_wide hc hwide fu (CrtWindowFive.crtExpRanges_ok wx) ku.wr (ku.gpr .x0 (by decide)),
    yu,vu,fu,ku⟩

end VG.Proof.Bignum.AArch64.WindowFive
