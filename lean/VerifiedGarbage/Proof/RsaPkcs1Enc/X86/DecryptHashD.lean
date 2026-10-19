module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptHashAbsorbD
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptHashFinalize

/-! # DH is SHA-256 of the entire fixed-width private exponent -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

theorem hashFinishD_ok (v : VG.Proof.Sha256.X86.Variants.Backend)
    {g : Geometry} {bs : Fin 9 → List Byte} {s : State} {D : List Byte}
    (h : Context g bs s) (repr : Spec.Sha256.Repr s.mem (g.scratch sSt 96).base D) (length : D.length = g.length) :
    WP isa (callAfter shaFinArgs (hashFns v).finN (hashFns v).finC) s fun t => Context g bs t ∧
      Frame (hashWrites g) s.mem t.mem ∧ Keeps callClobbers s t ∧
      Spec.Rsa.bytesAt t.mem (g.scratch sDH 32).base 32 = Spec.Sha256.hash D := by
  unfold callAfter
  refine WP.seq (WP.mono (shaFinArgs_ok h) ?_)
  rintro a ⟨ha, args, Fa, Ka⟩
  refine WP.mono (shaFinalize_call v ha args (repr_args h Fa repr) length) ?_
  rintro t ⟨ht, F, _, K, bytes⟩
  exact ⟨ht, (argsFrame_hash Fa).trans F, (Ka.mono (by decide)).trans K, bytes⟩

theorem hashD_ok (v : VG.Proof.Sha256.X86.Variants.Backend)
    {g : Geometry} {bs : Fin 9 → List Byte} {s : State} {D : List Byte}
    (h : Context g bs s) (bytes : Spec.Rsa.bytesAt s.mem (g.scratch sD g.length).base g.length = D) :
    WP isa (hashD (hashFns v)) s fun t => Context g bs t ∧
      Frame (hashWrites g) s.mem t.mem ∧ Keeps callClobbers s t ∧
      Spec.Rsa.bytesAt t.mem (g.scratch sDH 32).base 32 = Spec.Sha256.hash D := by
  have length : D.length = g.length := by
    rw [← bytes]
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  unfold hashD
  refine WP.seq (WP.mono (hashStartD_ok v h bytes) ?_)
  rintro a ⟨ha, Fa, Ka, reprA, bytesA⟩
  refine WP.seq (WP.mono (hashAbsorbD_ok v ha bytesA reprA) ?_)
  rintro b ⟨hb, Fb, Kb, reprB⟩
  refine WP.mono (hashFinishD_ok v hb reprB length) ?_
  rintro t ⟨ht, F, K, digest⟩
  exact ⟨ht, Fa.trans (Fb.trans F), Ka.trans (Kb.trans K), digest⟩

end VG.Proof.RsaPkcs1Enc.X86.Dec
