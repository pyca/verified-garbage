module

public import VerifiedGarbage.Proof.MlKem.X86_64.Contracts
public import VerifiedGarbage.Spec.MlKem.Contract1024
public import VerifiedGarbage.Proof.MlKem1024.Contract

/-!
# ML-KEM-1024 on x86-64: the contracts of the compressions the proofs are written against

As `Proof/MlKem/X86_64/Contracts.lean`, for `vg_mlkem1024_compress_encode` and
`vg_mlkem1024_decode_decompress`, whose widths are ML-KEM-1024's
(`Proof.MlKem1024.compressWidths`).
-/

@[expose] public section

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Spec.MlKem

/-- `vg_mlkem1024_compress_encode(f = rdi, d = esi, out = rdx, len = rcx)`. -/
abbrev compressEncode1024K : Contract isa := compressEncodeWK Proof.MlKem1024.compressWidths

/-- `vg_mlkem1024_decode_decompress(b = rdi, len = rsi, d = edx, f = rcx)`. -/
abbrev decodeDecompress1024K : Contract isa := decodeDecompressWK Proof.MlKem1024.compressWidths

end VG.Proof.MlKem1024.X86_64
