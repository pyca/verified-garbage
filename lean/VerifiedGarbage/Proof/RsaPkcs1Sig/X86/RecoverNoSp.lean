module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverPublicCall
import VerifiedGarbage.Proof.Dsa.X86.RandomSignCorrect
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Weierstrass.PointContract

/-! # Verification uses its two stack frames without changing their pointers -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Impl.RsaPkcs1Sig.X86.Recover
open VG.Impl.RsaPkcs1Sig.X86.Verify (frameBytes)

theorem body_noSp (v : PublicImpl) : NoSp (body v.name v.code) := by
  unfold body
  exact .seq' (.of_all (by decide +kernel)) (.ite' (.of_all (by decide +kernel))
    (.seq' (.of_all (by decide +kernel)) (.seq' (.call' v.noSp) (.of_all (by decide +kernel)))))

theorem allocation_noSp (v : PublicImpl) :
    NoSp (.frame (.alloc frameBytes) (body v.name v.code) (.free frameBytes)) := by
  intro i hi
  simp only [instrs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | hi) | rfl
  · rfl
  · exact body_noSp v i hi
  · rfl

theorem inner_noSp (v : PublicImpl) :
    NoSp (.seq (.frame (.alloc frameBytes) (body v.name v.code) (.free frameBytes))
      (.block VG.Impl.RsaPkcs1Sig.X86.Sign.restore)) :=
  .seq' (allocation_noSp v) (.of_all (by decide +kernel))

end VG.Proof.RsaPkcs1Sig.X86.Rcv
