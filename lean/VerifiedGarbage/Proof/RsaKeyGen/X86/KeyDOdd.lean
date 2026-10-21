module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExponentFrame
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOddPrepare
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOddFinish

/-! # The native private exponent with a public odd exponent -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

theorem dOdd_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) (width : 2 ≤ n)
    (large : 3 ≤ val32 s.mem B kEv 2) (odd : val32 s.mem B kEv 2 % 2 = 1)
    (loaded : num s.mem B n aE = val32 s.mem B kEv 2) (one : num s.mem B n aOne = 1) :
    WP isa (dOdd n) s fun t =>
      Ws t B Z n 32 ∧ Outs B (exponentRanges n) s.mem t.mem ∧ slot t.mem B kOk ≤ 1 ∧
      Spec.Rsa.inverse (val32 s.mem B kEv 2) (num s.mem B n aL) =
        (if slot t.mem B kOk = 0 then none else some (num t.mem B n aD)) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  unfold dOdd
  refine WP.seq (WP.mono (dOddPrepare_ok h width large odd loaded one)
    fun u ⟨hu, Ou, P, Ku⟩ => ?_)
  refine WP.mono (dOddFinish_ok hu width large P) fun t ⟨ht, Ot, bit, inverse, Kt⟩ => ?_
  exact ⟨ht, Ou.trans (exponent_result_frame Ot), bit, inverse, Ku.trans Kt⟩

end VG.Proof.RsaKeyGen.X86.Key
