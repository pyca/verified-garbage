module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptPrfFinalizeArgs
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptMacFinalize
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptMacUpdate

/-! # Write the digest for one public PRF counter -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

theorem prfFinish_ok (v : VG.Proof.Sha256.X86.Variants.Backend)
    {g : Geometry} {bs : Fin 9 → List Byte} {s : State} {key text : List Byte}
    (h : Context g bs s) (dst i len : Nat)
    (counter : s.mem.readW (byteAddr g.stack + BitVec.ofNat 64 oI) 32 = BitVec.ofNat 32 i)
    (dstLow : 192 ≤ dst + 32 * i) (dstHigh : dst + 32 * i + 32 ≤ sHash)
    (keyFits : key.length ≤ 64) (textFits : text.length ≤ 1024)
    (length : text.length = len) (repr : MacRepr g key text s) :
    WP isa (callAfter (prfFinArgs len dst) (hashFns v).hfN (hashFns v).hfC) s fun t => Context g bs t ∧
      Frame (hashWrites g) s.mem t.mem ∧
      Frame ((macFinalizeWr g (dst + 32 * i) ++ [g.calleeRegion]) ++ [⟨byteAddr g.stack, 80⟩]) s.mem t.mem ∧
      Keeps callClobbers s t ∧
      Spec.Rsa.bytesAt t.mem (g.scratch (dst + 32 * i) 32).base 32 = Spec.Hmac.hmac Spec.Hmac.sha256 key text := by
  unfold callAfter
  refine WP.seq (WP.mono (prfFinArgs_ok h len dst i counter) ?_)
  rintro a ⟨ha, args, Fa, Ka⟩
  have args' : Arguments g (macFinalizeValues g (dst + 32 * i) (64 + text.length)) 6 a := by
    rw [length]
    exact args
  have reprA := macRepr_args h Fa repr
  refine WP.mono (macFinalize_call v ha args' dstLow dstHigh keyFits textFits reprA) ?_
  rintro t ⟨ht, F, Ffine, K, bytes⟩
  refine ⟨ht, (argsFrame_hash Fa).trans F, ?_, (Ka.mono (by decide)).trans K, bytes⟩
  exact (Fa.sub (by
    intro r hr
    exact ⟨r, List.mem_append_right _ hr, fun _ hx => hx⟩)).trans
      (Ffine.sub (by
        intro r hr
        exact ⟨r, List.mem_append_left _ hr, fun _ hx => hx⟩))

end VG.Proof.RsaPkcs1Enc.X86.Dec
