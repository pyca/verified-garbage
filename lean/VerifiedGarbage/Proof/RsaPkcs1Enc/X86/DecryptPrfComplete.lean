module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptPrfConfigs
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptPrfLoop
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptPrfAmInit

/-! # Complete length-output and alternative-message PRFs -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt
open VG.Proof.RsaPkcs1Enc

theorem clLoop_ok (v : VG.Proof.Sha256.X86.Variants.Backend)
    {g : Geometry} {bs : Fin 9 → List Byte} {s : State} {key : List Byte}
    (h : Context g bs s) (keyBytes : Spec.Rsa.bytesAt s.mem (g.scratch sKDK 32).base 32 = key) :
    WP isa (clLoop (hashFns v)) s fun t =>
      PrfInvariant g bs s clConfig key (Spec.Rsa.bytesAt s.mem (g.scratch sDH 32).base 32) 8 t := by
  unfold clLoop
  refine WP.seq (WP.mono (clInit_ok h) ?_)
  rintro a ⟨ha, Fa, Ka, counter, blocks, bytes⟩
  have initial : PrfInvariant g bs s clConfig key (Spec.Rsa.bytesAt s.mem (g.scratch sDH 32).base 32) 0 a :=
    ⟨ha, Fa, Ka.mono (by decide), counter, blocks,
      (bytes sKDK 32 (by decide)).trans keyBytes, bytes sDH 32 (by decide), by rfl⟩
  exact prfLoop_ok v initial (fun i bound a ha ptr ci _ =>
    clMessage_ok ha ptr ci (by change i < 8 at bound; omega))

theorem amLoop_ok (v : VG.Proof.Sha256.X86.Variants.Backend)
    {g : Geometry} {bs : Fin 9 → List Byte} {s : State} {key : List Byte}
    (h : Context g bs s) (keyBytes : Spec.Rsa.bytesAt s.mem (g.scratch sKDK 32).base 32 = key) :
    WP isa (amLoop (hashFns v)) s fun t =>
      PrfInvariant g bs s (amConfig g h.valid) key (Spec.Rsa.bytesAt s.mem (g.scratch sCL 256).base 256)
        ((g.length + 31) / 32) t := by
  unfold amLoop
  refine WP.seq (WP.mono (amInit_ok h) ?_)
  rintro a ⟨ha, Fa, Ka, counter, blocks, bytes⟩
  have initial : PrfInvariant g bs s (amConfig g h.valid) key (Spec.Rsa.bytesAt s.mem (g.scratch sCL 256).base 256) 0 a :=
    ⟨ha, Fa, Ka.mono (by decide), counter, blocks,
      (bytes sKDK 32 (by decide)).trans keyBytes, bytes sCL 256 (by decide), by rfl⟩
  exact prfLoop_ok v initial (fun i bound a ha ptr ci len =>
    amMessage_ok ha ptr ci (by
      change i < (g.length + 31) / 32 at bound
      have := h.valid.maxLength
      omega) len)

end VG.Proof.RsaPkcs1Enc.X86.Dec
