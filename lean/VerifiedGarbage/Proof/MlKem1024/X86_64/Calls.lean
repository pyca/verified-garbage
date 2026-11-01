module

public import VerifiedGarbage.Proof.MlKem.X86_64.EncBase
import VerifiedGarbage.Proof.MlKem1024.X86_64.CompressEncode
import VerifiedGarbage.Proof.MlKem1024.X86_64.DecodeDecompress
import VerifiedGarbage.Proof.MlKem1024.X86_64.CompressEncodeAvx2
import VerifiedGarbage.Proof.MlKem1024.X86_64.DecodeDecompressAvx2
public import VerifiedGarbage.Impl.MlKem1024.X86_64.Kem
public import VerifiedGarbage.Spec.MlKem.Contract1024
public import VerifiedGarbage.Proof.MlKem1024.Contract

/-!
# ML-KEM-1024 on x86-64: the compressions its functions run

`vg_mlkem1024_compress_encode` and `vg_mlkem1024_decode_decompress`, or their
AVX2 implementations, for its widths.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem1024.X86_64
open VG.Proof.MlKem VG.Proof.MlKem.X86_64

/-- The implementations of `vg_mlkem1024_compress_encode` and `vg_mlkem1024_decode_decompress`. -/
theorem ce1024I : ∀ cs : Codecs, CEImpl (ceN1024 cs) (ce1024 cs) Proof.MlKem1024.compressWidths
  | .base => ceImpl1024
  | .avx2 => ceImpl1024Y

theorem dd1024I : ∀ cs : Codecs, DDImpl (ddN1024 cs) (dd1024 cs) Proof.MlKem1024.compressWidths
  | .base => ddImpl1024
  | .avx2 => ddImpl1024Y

/-- The compressions it calls. -/
theorem calls1024 : KemCalls kem1024 Proof.MlKem1024.compressWidths Proof.MlKem1024.compressWidths :=
  ⟨ce1024I, dd1024I, by decide, by decide⟩

end VG.Proof.MlKem1024.X86_64
