module
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Shape
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Bignum.X86_64.Words
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape


/-! # FFDH parameter candidates on x86-64: make p odd -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.ParameterCandidate

theorem setLow_ok {s : State} {op : Addr} {len : Nat} {b : Byte}
    (hk1 : 1 ≤ len) (hk : len < 2 ^ 31) (hp : s.gpr .r11 = off op len)
    (hrd : InRegions (s.rd ++ s.wr) (off op (len - 1)) 1) (hwr : InRegions s.wr (off op (len - 1)) 1)
    (hb : s.mem (off op (len - 1)) = b) :
    WP isa (.block setLow) s fun t => t.mem = s.mem.writeW (off op (len - 1)) (b ||| 1) ∧ Keep [.rax] s t := by
  have hsub : BitVec.ofNat 64 len + BitVec.ofInt 64 (-1) = BitVec.ofNat 64 (len - 1) := by
    rw [BitVec.ofInt_neg]
    change BitVec.ofNat 64 len + -(1 : BitVec 64) = _
    rw [BitVec.add_neg_eq_sub]
    exact ofNat64_pred hk1 (by omega)
  have he : off op len + BitVec.ofInt 64 (-1) = off op (len - 1) := by
    simp only [off, BitVec.add_assoc, hsub]
  have hbyte : (b.setWidth 64 ||| 1).setWidth 8 = b ||| 1 := by simp [BitVec.setWidth_or]
  exact WP.keep [.rax] (by unfold setLow; xrun [State.ea, hp, he, hrd, hwr, hb, hbyte]) rfl

end VG.Proof.Ffdh.X86_64.ParameterCandidate
