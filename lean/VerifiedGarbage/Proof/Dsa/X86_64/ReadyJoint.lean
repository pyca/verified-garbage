module

public import VerifiedGarbage.Proof.Dsa.X86_64.ReadyCalls

import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
import VerifiedGarbage.Proof.Dsa.X86_64.Call
import VerifiedGarbage.Proof.Dsa.X86_64.JointPower
/-! # Joint exponentiation preserving the DSA execution context -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/CoreJoint.lean`, which only this module imported.
section

/-! # Joint exponentiation in the DSA parent workspace -/

section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem coreJoint_ok (M : Mont) (Sq : MontS) {s : State} {B : Addr} {Z o w wx m k : Nat}
    {minv parentMinv : BitVec 64}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B o wx m minv)
    (hZ : pWorkspace ≤ Z) (hlo : slot w 8 ≤ o)
    (hhi : o + slot wx 8 + tabBytes wx ≤ Z) (ho : o < 2 ^ 31) (hparent : 344 ≤ o)
    (hw2 : 2 ≤ wx) (hw48 : wx ≤ 48) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hm : 1 < m) (hodd : m % 2 = 1)
    (a b output : Operand) (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (houtp : pointerFits output.pointer) {ba bb : List Byte}
    (has : OperandBytes s B Z a ba) (hbs : OperandBytes s B Z b bb)
    (ha1 : 1 ≤ ba.length) (haw : (ba.length + 7) / 8 ≤ wx)
    (hb1 : 1 ≤ bb.length) (hbw : (bb.length + 7) / 8 ≤ wx)
    {eb fb : List Byte} (he : Src s B Z (off B u) eb) (hf : Src s B Z (off B v) fb)
    (hlen : fb.length = eb.length) (hL0 : 0 < eb.length) (hL' : eb.length < 2 ^ 31)
    (hql : word s.mem B Field.qLen.offset = BitVec.ofNat 64 eb.length)
    (hl : word s.mem B output.length.offset = BitVec.ofNat 64 k)
    (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31) (hkw : wx = (k + 7) / 8)
    (hout : ∀ j < k, InRegions s.wr (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j) 1)
    (hprefix : ∀ j < k, Z ≤ ofs B (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j)) :
    WP isa (Core.joint Sq.mm M.mm o a b output) s fun t =>
      Good t B Z w parentMinv ∧ ChildReady t.mem B o wx m minv ∧
      Spec.Rsa.bytesAt t.mem (pointerValue s.mem B output.pointer) k =
        Spec.Dsa.encodeBE k (Spec.Dsa.powMod (Spec.Dsa.decodeBE ba) (Spec.Dsa.decodeBE eb) m *
          Spec.Dsa.powMod (Spec.Dsa.decodeBE bb) (Spec.Dsa.decodeBE fb) m % m) ∧
      CallFrame B o wx (pointerValue s.mem B output.pointer) k s.mem t.mem ∧ Keep coreRegs s t := by
  apply call3_ok hg child hZ hlo hhi ho a b output ha hb houtp hl hk1 hk' hkw hout hprefix
  intro st hc hchild hargs hframe hk
  have hz : 176 ≤ Z := Nat.le_trans (by decide) hZ
  have hq : word st.mem B Field.qLen.offset = BitVec.ofNat 64 eb.length := by
    rw [hframe.word_eq (by simp [argumentRanges, Field.offset]) (by decide)]
    exact hql
  exact jointPower_ok M Sq hc hw2 hw48 hwx hw30 hm hodd hparent hchild.modulus hchild.inverse
    hargs.1 (hargs.2.1.trans has.length) (arguments_source hframe hk hz has.source) ha1 haw
    hargs.2.2.1 (hargs.2.2.2.1.trans hbs.length) (arguments_source hframe hk hz hbs.source) hb1 hbw
    (arguments_source hframe hk hz he) (arguments_source hframe hk hz hf) hlen hL0 hL' hq

end VG.Proof.Dsa.X86_64
end

end

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem readyJoint_ok (M : Mont) (Sq : MontS) {L : ExecutionLayout} {s : State} (h : Ready L s)
    (hm : 1 < L.modulus) (hodd : L.modulus % 2 = 1)
    (a b : Operand) {ba bb : List Byte} (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (has : OperandBytes s L.base activeBytes a ba) (hbs : OperandBytes s L.base activeBytes b bb)
    (ha1 : 1 ≤ ba.length) (haw : (ba.length + 7) / 8 ≤ ModulusSide.p.words L)
    (hb1 : 1 ≤ bb.length) (hbw : (bb.length + 7) / 8 ≤ ModulusSide.p.words L)
    {eb fb : List Byte}
    (he : OperandBytes s L.base activeBytes (Core.scalar u) eb)
    (hf : OperandBytes s L.base activeBytes (Core.scalar v) fb)
    (hel : eb.length = L.qLen) (hfl : fb.length = L.qLen)
    (d : Nat) (hd : activeBytes ≤ d) (hend : d + ModulusSide.p.length L ≤ usedBytes) :
    WP isa (Core.joint Sq.mm M.mm ModulusSide.p.offset a b ⟨.local d, ModulusSide.p.lengthField⟩) s
      (CallResult L .p d (Spec.Dsa.powMod (Spec.Dsa.decodeBE ba) (Spec.Dsa.decodeBE eb) L.modulus *
        Spec.Dsa.powMod (Spec.Dsa.decodeBE bb) (Spec.Dsa.decodeBE fb) L.modulus % L.modulus) s) := by
  obtain ⟨hw2, hw48, hlo, ho, hhi, hk1, hk31⟩ := ModulusSide.p.bounds L
  have hdp : pointerFits (.local d) := by
    change d < 2 ^ 31
    have : usedBytes < 2 ^ 31 := by decide
    omega
  refine WP.mono (coreJoint_ok M Sq h.parent (h.child .p) (by decide) hlo hhi ho (by decide)
    hw2 hw48 hw48 (by decide) hm hodd a b ⟨.local d, ModulusSide.p.lengthField⟩ ha hb hdp
    has hbs ha1 haw hb1 hbw he.source hf.source (hel.trans hfl.symm).symm
    (by rw [hel]; exact L.widths.1) (by rw [hel]; have := L.widths; omega)
    (by simpa only [hel, ModulusSide.length, ModulusSide.lengthField] using h.length .q) (h.length .p) hk1 hk31 rfl
    (h.local_write hend) (h.local_out hd hend)) ?_
  intro t ⟨hp, hc, hv, hf, hk⟩
  exact ⟨h.afterCall .p hp hc hf hk hd hend, hv, hf, hk⟩


end VG.Proof.Dsa.X86_64
