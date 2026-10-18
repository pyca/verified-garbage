module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptPublicCall
public import VerifiedGarbage.Proof.Dsa.X86.RandomSignCorrect

/-! # Stack-pointer preservation through the public RSA call -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Enc
open VG VG.X86 VG.Impl.RsaPkcs1Enc.X86.Encrypt

theorem body_noSp (v : PublicImpl) : NoSp (body v.name v.code) := by
  unfold body
  exact .seq' (.of_all (by decide +kernel)) (.seq' (.of_all (by decide +kernel))
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

end VG.Proof.RsaPkcs1Enc.X86.Enc
