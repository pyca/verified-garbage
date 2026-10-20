module

public import VerifiedGarbage.Proof.Dsa.AArch64.Call
import VerifiedGarbage.Proof.Dsa.AArch64.Add
import VerifiedGarbage.Proof.Framework.Block

/-! # Exponentiation and multiplication in the DSA parent workspace -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

/-- Complete modular addition call for two already reduced scalars. -/
theorem coreAdd_ok {s : State} {B : Addr} {Z w wx m k : Nat}
    {minv parentMinv : BitVec 64}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B qWorkspace wx m minv)
    (hZ : pWorkspace ≤ Z) (hlo : slot w 8 ≤ qWorkspace)
    (hhi : qWorkspace + slot wx 8 + tabBytes wx ≤ Z)
    (hw2 : 2 ≤ wx) (hw48 : wx ≤ 48) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (a b output : Operand) (ha : pointerFits a.pointer) (hb : pointerFits b.pointer)
    (houtp : pointerFits output.pointer) {ba bb : List Byte}
    (has : OperandBytes s B Z a ba) (hbs : OperandBytes s B Z b bb)
    (ha1 : 1 ≤ ba.length) (haw : (ba.length + 7) / 8 ≤ wx)
    (hb1 : 1 ≤ bb.length) (hbw : (bb.length + 7) / 8 ≤ wx)
    (haReduced : Spec.Dsa.decodeBE ba < m) (hbReduced : Spec.Dsa.decodeBE bb < m)
    (hl : word s.mem B output.length.offset = BitVec.ofNat 64 k)
    (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31) (hkw : wx = (k + 7) / 8)
    (hout : ∀ j < k, InRegions s.wr (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j) 1)
    (hprefix : ∀ j < k, Z ≤ ofs B (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j)) :
    WP isa (Core.add a b output) s fun t =>
      Good t B Z w parentMinv ∧ ChildReady t.mem B qWorkspace wx m minv ∧
      Spec.Rsa.bytesAt t.mem (pointerValue s.mem B output.pointer) k =
        Spec.Dsa.encodeBE k ((Spec.Dsa.decodeBE ba + Spec.Dsa.decodeBE bb) % m) ∧
      CallFrame B qWorkspace wx (pointerValue s.mem B output.pointer) k s.mem t.mem ∧ Keep coreRegs s t := by
  have h := call3_ok (body := seqs [Arithmetic.load aX arg argLen,
    Arithmetic.load aXm arg2 arg2Len, Crt.addMod aY aX aXm])
    hg child hZ hlo hhi (by decide) a b output ha hb houtp hl hk1 hk' hkw hout hprefix
    (value := (Spec.Dsa.decodeBE ba + Spec.Dsa.decodeBE bb) % m) ?_
  · change WP isa (.seq (.block _) (.seq (Arithmetic.load aX arg argLen)
      (.seq (Arithmetic.load aXm arg2 arg2Len) (.seq (Crt.addMod aY aX aXm) (seqs Core.finish))))) s _
    refine WP.seq (WP.mono (WP.seq_iff.mp h) fun u hu => ?_)
    exact WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp hu)) fun v hv =>
      WP.seq (WP.mono (WP.seq_iff.mp hv) fun z hz => WP.seq hz))
  intro u hc hchild hargs hf hk
  have hz : 176 ≤ Z := Nat.le_trans (by decide) hZ
  exact add_ok hc ⟨hc.good, hchild.modulus, hchild.inverse⟩ hw2 hw48 hwx hw30
    (by decide) (by decide) (by decide) (by decide)
    hargs.1 (hargs.2.1.trans has.length) (arguments_source hf hk hz has.source) ha1 haw
    hargs.2.2.1 (hargs.2.2.2.1.trans hbs.length) (arguments_source hf hk hz hbs.source) hb1 hbw
    haReduced hbReduced

end VG.Proof.Dsa.AArch64
