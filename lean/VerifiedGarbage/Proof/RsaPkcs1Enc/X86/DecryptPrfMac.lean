module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptPrfFrames
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptHashLocal

/-! # Each PRF block is an HMAC of its complete encoded message under KDK -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

def prfMac (H : Fns) (len dst : Nat) : Prog isa :=
  .seq (callAfter (macInitArgs sKDK) H.hiN H.hiC)
    (.seq (callAfter (prfUpdArgs len) H.updN H.updC)
      (callAfter (prfFinArgs len dst) H.hfN H.hfC))

theorem prfMac_ok (v : VG.Proof.Sha256.X86.Variants.Backend)
    {g : Geometry} {bs : Fin 9 → List Byte} {s : State} {key text : List Byte}
    (h : Context g bs s) (dst i len : Nat)
    (counter : s.mem.readW (byteAddr g.stack + BitVec.ofNat 64 oI) 32 = BitVec.ofNat 32 i)
    (dstLow : 192 ≤ dst + 32 * i) (dstHigh : dst + 32 * i + 32 ≤ sHash)
    (lengthBound : len ≤ 16) (length : text.length = len)
    (keyBytes : Spec.Rsa.bytesAt s.mem (g.scratch sKDK 32).base 32 = key)
    (textBytes : Spec.Rsa.bytesAt s.mem (g.scratch sMsg len).base len = text) :
    WP isa (prfMac (hashFns v) len dst) s fun t => Context g bs t ∧
      Frame (hashWrites g) s.mem t.mem ∧ Frame (prfMacWrites g (dst + 32 * i)) s.mem t.mem ∧
      Keeps callClobbers s t ∧
      Spec.Rsa.bytesAt t.mem (g.scratch (dst + 32 * i) 32).base 32 = Spec.Hmac.hmac Spec.Hmac.sha256 key text := by
  have keyFits : key.length ≤ 64 := by
    rw [← keyBytes]
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
    decide
  unfold prfMac
  refine WP.seq (WP.mono (macStart_fine v h (by decide : 192 ≤ sKDK) (by decide : sKDK + 32 ≤ sHash) keyBytes) ?_)
  rintro a ⟨ha, Fa, FfineA, Ka, reprA⟩
  have textA := (macInit_bytes h (by decide : 192 ≤ sMsg)
    (by unfold sMsg sHash; omega : sMsg + len ≤ sHash) FfineA).trans textBytes
  have counterA := (hash_local h Fa (by decide : 80 ≤ oI)
    (by decide : oI + 4 ≤ VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes)).trans counter
  refine WP.seq (WP.mono (prfAbsorb_ok v ha keyFits reprA lengthBound textA) ?_)
  rintro b ⟨hb, Fb, FfineB, Kb, reprB⟩
  have counterB := (hash_local ha Fb (by decide : 80 ≤ oI)
    (by decide : oI + 4 ≤ VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes)).trans counterA
  refine WP.mono (prfFinish_ok v hb dst i len counterB dstLow dstHigh keyFits
    (by omega) length reprB) ?_
  rintro t ⟨ht, F, Ffine, K, bytes⟩
  exact ⟨ht, Fa.trans (Fb.trans F),
    (initFrame_prf (dst + 32 * i) FfineA).trans
      ((updateFrame_prf (dst + 32 * i) FfineB).trans (finalizeFrame_prf Ffine)),
    Ka.trans (Kb.trans K), bytes⟩

end VG.Proof.RsaPkcs1Enc.X86.Dec
