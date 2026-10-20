module

public import VerifiedGarbage.Proof.Dsa.X86_64.ReadyCalls
import VerifiedGarbage.Proof.Dsa.X86_64.PublicPower
import Mathlib.Tactic.Set

/-! # Public exponentiation in the DSA parent workspace -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

/-- Complete parent-to-child exponentiation, with a reusable modulus and
an ordinary big-endian result. No primality assumption is required. -/
theorem corePublicPow_ok (M : Mont) (Sq : MontS) {s : State} {B : Addr} {Z o w wx m k : Nat}
    {minv parentMinv : BitVec 64}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B o wx m minv)
    (hZ : pWorkspace ≤ Z) (hlo : slot w 8 ≤ o)
    (hhi : o + slot wx 8 + tabBytes wx ≤ Z) (ho : o < 2 ^ 31)
    (hw2 : 2 ≤ wx) (hw48 : wx ≤ 48) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hm : 1 < m) (hodd : m % 2 = 1)
    (a b output : Operand) (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (houtp : pointerFits output.pointer) {ba bb : List Byte}
    (has : OperandBytes s B Z a ba) (hbs : OperandBytes s B Z b bb)
    (ha1 : 1 ≤ ba.length) (haw : (ba.length + 7) / 8 ≤ wx)
    (hb1 : 1 ≤ bb.length) (hb2 : bb.length ≤ 1024)
    (hl : word s.mem B output.length.offset = BitVec.ofNat 64 k)
    (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31) (hkw : wx = (k + 7) / 8)
    (hout : ∀ j < k, InRegions s.wr (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j) 1)
    (hprefix : ∀ j < k, Z ≤ ofs B (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j)) :
    WP isa (Core.publicPow Sq.mm M.mm o a b output) s fun t =>
      Good t B Z w parentMinv ∧ ChildReady t.mem B o wx m minv ∧
      Spec.Rsa.bytesAt t.mem (pointerValue s.mem B output.pointer) k =
        Spec.Dsa.encodeBE k (Spec.Dsa.powMod (Spec.Dsa.decodeBE ba) (Spec.Dsa.decodeBE bb) m) ∧
      CallFrame B o wx (pointerValue s.mem B output.pointer) k s.mem t.mem ∧ Keep coreRegs s t := by
  apply call3_ok hg child hZ hlo hhi ho a b output ha hb houtp hl hk1 hk' hkw hout hprefix
  intro u hc hchild hargs hf hk
  have hz : 176 ≤ Z := Nat.le_trans (by decide) hZ
  refine WP.mono (PublicPower.power_ok M Sq hc hw2 hw48 hwx hw30 hm hodd hchild.modulus hchild.inverse
    (by decide) (by decide) (by decide) (by decide)
    hargs.1 (hargs.2.1.trans has.length) (arguments_source hf hk hz has.source) ha1 haw
    hargs.2.2.1 (hargs.2.2.2.1.trans hbs.length) (arguments_source hf hk hz hbs.source) hb1 hb2)
    fun v ⟨hcv, hv, hmv, hfv, hkv⟩ => ⟨hcv, hmv, hv, hfv, hkv⟩

theorem readyPublicPow_ok (M : Mont) (Sq : MontS) {L : ExecutionLayout} {s : State} (h : Ready L s)
    (side : ModulusSide) (hm : 1 < side.value L) (hodd : side.value L % 2 = 1)
    (a b : Operand) {ba bb : List Byte} (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (has : OperandBytes s L.base activeBytes a ba) (hbs : OperandBytes s L.base activeBytes b bb)
    (ha1 : 1 ≤ ba.length) (haw : (ba.length + 7) / 8 ≤ side.words L)
    (hb1 : 1 ≤ bb.length) (hb2 : bb.length ≤ 1024)
    (d : Nat) (hd : activeBytes ≤ d) (hend : d + side.length L ≤ usedBytes) :
    WP isa (Core.publicPow Sq.mm M.mm side.offset a b ⟨.local d, side.lengthField⟩) s
      (CallResult L side d (Spec.Dsa.powMod (Spec.Dsa.decodeBE ba) (Spec.Dsa.decodeBE bb) (side.value L)) s) := by
  obtain ⟨hw2, hw48, hlo, ho, hhi, hk1, hk31⟩ := side.bounds L
  have hdp : pointerFits (.local d) := by
    change d < 2 ^ 31
    have : usedBytes < 2 ^ 31 := by decide
    omega
  refine WP.mono (corePublicPow_ok M Sq h.parent (h.child side) (by decide) hlo hhi ho
    hw2 hw48 hw48 (by decide) hm hodd a b ⟨.local d, side.lengthField⟩ ha hb hdp
    has hbs ha1 haw hb1 hb2 (h.length side) hk1 hk31 rfl
    (h.local_write hend) (h.local_out hd hend)) ?_
  intro t ⟨hp, hc, hv, hf, hk⟩
  exact ⟨h.afterCall side hp hc hf hk hd hend, hv, hf, hk⟩

end VG.Proof.Dsa.X86_64
