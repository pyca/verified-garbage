module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptMacInit

/-! # Prepare and initialize an HMAC from a saved digest -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

theorem macStart_fine (v : VG.Proof.Sha256.X86.Variants.Backend)
    {g : Geometry} {bs : Fin 9 → List Byte} {s : State} {key : Nat} {K0 : List Byte}
    (h : Context g bs s) (keyLow : 192 ≤ key) (keyHigh : key + 32 ≤ sHash)
    (bytes : Spec.Rsa.bytesAt s.mem (g.scratch key 32).base 32 = K0) :
    WP isa (callAfter (macInitArgs key) (hashFns v).hiN (hashFns v).hiC) s fun t => Context g bs t ∧
      Frame (hashWrites g) s.mem t.mem ∧
      Frame ((macInitWr g ++ [g.calleeRegion]) ++ [⟨byteAddr g.stack, 80⟩]) s.mem t.mem ∧
      Keeps callClobbers s t ∧ MacRepr g K0 [] t := by
  have fit : key + 32 ≤ 8448 := by unfold sHash at keyHigh; omega
  unfold callAfter
  refine WP.seq (WP.mono (macInitArgs_ok h key) ?_)
  rintro a ⟨ha, args, Fa, Ka⟩
  refine WP.mono (macInit_call v ha args keyLow keyHigh ((scratchBytes_args h fit Fa).trans bytes)) ?_
  rintro t ⟨ht, F, Ffine, K, repr⟩
  refine ⟨ht, (argsFrame_hash Fa).trans F, ?_, (Ka.mono (by decide)).trans K, repr⟩
  exact (Fa.sub (by
    intro r hr
    exact ⟨r, List.mem_append_right _ hr, fun _ hx => hx⟩)).trans
      (Ffine.sub (by
        intro r hr
        exact ⟨r, List.mem_append_left _ hr, fun _ hx => hx⟩))

theorem macStart_ok (v : VG.Proof.Sha256.X86.Variants.Backend)
    {g : Geometry} {bs : Fin 9 → List Byte} {s : State} {key : Nat} {K0 : List Byte}
    (h : Context g bs s) (keyLow : 192 ≤ key) (keyHigh : key + 32 ≤ sHash)
    (bytes : Spec.Rsa.bytesAt s.mem (g.scratch key 32).base 32 = K0) :
    WP isa (callAfter (macInitArgs key) (hashFns v).hiN (hashFns v).hiC) s fun t => Context g bs t ∧
      Frame (hashWrites g) s.mem t.mem ∧ Keeps callClobbers s t ∧ MacRepr g K0 [] t := by
  refine WP.mono (macStart_fine v h keyLow keyHigh bytes) ?_
  rintro t ⟨ht, F, _, K, repr⟩
  exact ⟨ht, F, K, repr⟩

end VG.Proof.RsaPkcs1Enc.X86.Dec
