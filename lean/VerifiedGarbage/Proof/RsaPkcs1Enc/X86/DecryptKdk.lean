module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptKdkUpdate
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptMacFinalize

/-! # Derive KDK by HMAC-SHA-256 of the ciphertext under DH -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

theorem kdkFinalizeArguments {g : Geometry} {s : State} {text : List Byte}
    (a : Arguments g (fun j => (kdkFinalizePlan j).valueAt g) 6 s) (length : text.length = g.length) :
    Arguments g (macFinalizeValues g sKDK (64 + text.length)) 6 s := by
  intro j hj
  rw [a j hj]
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl
  · change g.workspace + BitVec.ofNat 32 sSt = g.workspace
    exact BitVec.add_zero _
  · rfl
  · change BitVec.ofNat 32 g.length + BitVec.ofNat 32 64 = BitVec.ofNat 32 (64 + text.length)
    rw [← BitVec.ofNat_add, length, Nat.add_comm]
  all_goals rfl

theorem kdkFinish_ok (v : VG.Proof.Sha256.X86.Variants.Backend)
    {g : Geometry} {bs : Fin 9 → List Byte} {s : State} {key text : List Byte}
    (h : Context g bs s) (keyFits : key.length ≤ 64) (repr : MacRepr g key text s)
    (length : text.length = g.length) :
    WP isa (callAfter kdkFinArgs (hashFns v).hfN (hashFns v).hfC) s fun t => Context g bs t ∧
      Frame (hashWrites g) s.mem t.mem ∧ Keeps callClobbers s t ∧
      Spec.Rsa.bytesAt t.mem (g.scratch sKDK 32).base 32 = Spec.Hmac.hmac Spec.Hmac.sha256 key text := by
  unfold callAfter
  refine WP.seq (WP.mono (kdkFinArgs_ok h) ?_)
  rintro a ⟨ha, args, Fa, Ka⟩
  refine WP.mono (macFinalize_call v ha (kdkFinalizeArguments args length)
    (by decide : 192 ≤ sKDK) (by decide : sKDK + 32 ≤ sHash)
    keyFits (by rw [length]; exact ha.valid.maxLength) (macRepr_args h Fa repr)) ?_
  rintro t ⟨ht, F, _, K, bytes⟩
  exact ⟨ht, (argsFrame_hash Fa).trans F, (Ka.mono (by decide)).trans K, bytes⟩

theorem kdkMac_ok (v : VG.Proof.Sha256.X86.Variants.Backend)
    {g : Geometry} {bs : Fin 9 → List Byte} {s : State} {DH : List Byte}
    (h : Context g bs s) (bytes : Spec.Rsa.bytesAt s.mem (g.scratch sDH 32).base 32 = DH) :
    WP isa (kdkMac (hashFns v)) s fun t => Context g bs t ∧
      Frame (hashWrites g) s.mem t.mem ∧ Keeps callClobbers s t ∧
      Spec.Rsa.bytesAt t.mem (g.scratch sKDK 32).base 32 = Spec.Hmac.hmac Spec.Hmac.sha256 DH (bs 3) := by
  have keyFits : DH.length ≤ 64 := by
    rw [← bytes]
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
    decide
  have length : (bs 3).length = g.length := (h.sources 3).length
  unfold kdkMac
  refine WP.seq (WP.mono (macStart_ok v h (by decide : 192 ≤ sDH) (by decide : sDH + 32 ≤ sHash) bytes) ?_)
  rintro a ⟨ha, Fa, Ka, reprA⟩
  refine WP.seq (WP.mono (kdkAbsorb_ok v ha keyFits reprA) ?_)
  rintro b ⟨hb, Fb, Kb, reprB⟩
  refine WP.mono (kdkFinish_ok v hb keyFits reprB length) ?_
  rintro t ⟨ht, F, K, digest⟩
  exact ⟨ht, Fa.trans (Fb.trans F), Ka.trans (Kb.trans K), digest⟩

end VG.Proof.RsaPkcs1Enc.X86.Dec
