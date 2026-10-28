module
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowLoop
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowFrameContext
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowHead
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRun
import VerifiedGarbage.Proof.Bignum.Math

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
