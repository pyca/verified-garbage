module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.AttemptPublic
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.GenerateNativeTiming

/-! The complete attempt satisfies the reviewed native constant-time contract. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached

theorem attempt_constantTime (M : Mont) : ConstantTime isa attemptPre attemptPub (Generate.code M.mm) :=by
 intro s t ts tt u v hs ht hp es et
 let gs:=attempt_geometry hs
 let gt:=attempt_geometry ht
 have publicInfo:=attemptPub_front gs gt hp
 have first : NativeReady (attemptFront s gs) s :=⟨attemptRandom s,attempt_native_state gs⟩
 have second : NativeReady (attemptFront s gs) t :=by
  rw [publicInfo.1]
  exact ⟨attemptRandom t,attempt_native_state gt⟩
 exact ((generateNative_ct M) _ _ _ _ _ _ ⟨attemptFront s gs,first,second,publicInfo.2⟩ es et).1

end VG.Proof.Ffdh.AArch64.Cached
