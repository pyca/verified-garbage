module

public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Impl.Dsa.X86_64.Joint
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Dsa.X86_64.Frame
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Dsa.X86_64.JointRun
import VerifiedGarbage.Proof.Dsa.X86_64.JointPrepare
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Dsa.Arithmetic

/-! # Loading and preparing both bases for joint DSA exponentiation -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.X86_64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem jointPower_ok (M : Mont) (Sq : MontS) {s : State} {B : Addr} {Z o w wx m : Nat}
    {minv : BitVec 64} (hc : SubCtx s B Z o w wx minv)
    (hw2 : 2 ≤ wx) (hw48 : wx ≤ 48) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hm : 1 < m) (hodd : m % 2 = 1) (hparent : 344 ≤ o)
    (hn : wv s.mem (off B o) (slot wx aN) wx = m)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    {gp yp : Addr} {gb yb : List Byte}
    (hg : word s.mem B (8 * arg) = gp)
    (hgl : word s.mem B (8 * argLen) = BitVec.ofNat 64 gb.length)
    (hgs : Src s B Z gp gb) (hg1 : 1 ≤ gb.length) (hgw : (gb.length + 7) / 8 ≤ wx)
    (hy : word s.mem B (8 * arg2) = yp)
    (hyl : word s.mem B (8 * arg2Len) = BitVec.ofNat 64 yb.length)
    (hys : Src s B Z yp yb) (hy1 : 1 ≤ yb.length) (hyw : (yb.length + 7) / 8 ≤ wx)
    {eb fb : List Byte} (he : Src s B Z (off B u) eb) (hf : Src s B Z (off B v) fb)
    (hlen : fb.length = eb.length) (hL0 : 0 < eb.length) (hL' : eb.length < 2 ^ 31)
    (hl : word s.mem B Field.qLen.offset = BitVec.ofNat 64 eb.length) :
    WP isa (Joint.power Sq.mm M.mm) s fun t =>
      SubCtx t B Z o w wx minv ∧ ModCtx t (off B o) (slot wx 8) wx minv m ∧
      wv t.mem (off B o) (slot wx aY) wx =
        (Spec.Dsa.powMod (Spec.Dsa.decodeBE gb) (Spec.Dsa.decodeBE eb) m *
         Spec.Dsa.powMod (Spec.Dsa.decodeBE yb) (Spec.Dsa.decodeBE fb) m) % m ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold Joint.power
  refine WP.seq (WP.mono (jointPrepare_ok M hc hw2 hw48 hwx hw30 hm hodd hn hinv
    hg hgl hgs hg1 hgw hy hyl hys hy1 hyw)
    fun s1 ⟨hc1, hm1, ht1, hy1, ho1, hf1, hk1⟩ => ?_)
  have hnow := hc.scr.nowrap
  have hhi := hc.hi
  have hsmall : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  have hlen1 : word s1.mem B Field.qLen.offset = BitVec.ofNat 64 eb.length := by
    rw [hf1.word_below (fun r hr => (workRanges_ok wx r hr).2)
      (by omega) (by omega) (show Field.qLen.offset + 8 ≤ o from hparent)]
    exact hl
  refine WP.mono (jointRun_ok M Sq hc1 hm1 hw2 (by omega) hm hodd ht1 hy1 ho1
    (work_source hc hf1 hk1 he) (work_source hc hf1 hk1 hf) hlen hL0 hL' (by omega) hlen1)
    fun t ⟨hct, hmt, hv, hft, hkt⟩ => ⟨hct, hmt, ?_, hf1.trans hft, (hk1.trans hkt).mono (by decide)⟩
  simpa only [VG.Proof.Dsa.powMod_eq, Nat.mul_mod_mod, Nat.mod_mul_mod] using hv

end VG.Proof.Dsa.X86_64
