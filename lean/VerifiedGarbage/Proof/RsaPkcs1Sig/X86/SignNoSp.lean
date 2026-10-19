module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignPrivateCall
import VerifiedGarbage.Proof.Dsa.X86.RandomSignCorrect
import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety
import VerifiedGarbage.Proof.Framework.X86.CallWith

/-! # The signing frames preserve their stack pointers -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Sgn
open VG VG.X86 VG.Impl.RsaPkcs1Sig.X86.Sign
open VG.Proof.Rsa.X86.PrivChecked (CrtImpl privCode)

theorem body_noSp (v : CrtImpl) : NoSp (body (privName v) (privCode v)) := by
  unfold body afterEnc
  exact .seq' (.of_all (by decide +kernel)) (.seq' (.of_all (by decide +kernel))
    (.seq' (.of_all (by decide +kernel)) (.ite' (.of_all (by decide +kernel))
      (.seq' (.of_all (by decide +kernel))
        (.seq' (.call' (VG.Proof.Rsa.X86.PrivChecked.privateCode_noSp v)) (.of_all (by decide +kernel)))))))

theorem allocation_noSp (v : CrtImpl) :
    NoSp (.frame (.alloc frameBytes) (body (privName v) (privCode v)) (.free frameBytes)) := by
  intro i hi
  simp only [instrs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | hi) | rfl
  · rfl
  · exact body_noSp v i hi
  · rfl

theorem inner_noSp (v : CrtImpl) :
    NoSp (.seq (.frame (.alloc frameBytes) (body (privName v) (privCode v)) (.free frameBytes)) (.block restore)) :=
  .seq' (allocation_noSp v) (.of_all (by decide +kernel))

end VG.Proof.RsaPkcs1Sig.X86.Sgn
