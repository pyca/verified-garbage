module

public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.Stitch
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Impl.ForwardCall.X86_64

/-! # ChaCha20-Poly1305 entry points sharing the stitched fallbacks -/

@[expose] public section
namespace VG.Impl.ChaCha20Poly1305.X86_64.Shared
open VG.X86_64
open VG.Impl.ChaCha20Poly1305.X86_64.Stitch

deriving instance DecidableEq for Poly1305.X86_64.Blocks

/-- Allocate and wipe the ordinary working space. -/
def framed (c : Prog isa) : Prog isa :=
  StackScratch.X86_64.withStackArgScratchWipedX 1728 1 42 c

/-- The backend's framed body, without an entry-point fallback choice. -/
def body (enc : Bool) (x : ChaCha20.X86_64.Callee) (b : Poly1305.X86_64.Blocks) : Prog isa :=
  framed (if enc then
    if b = .avx2 then sealStitched { x with pass := 512 } .avx2 else «seal» x b
  else
    if b = .avx2 then openStitched x .avx2 else «open» x b)

/-- The body family follows the entry points' CPU variants. The stitched
VL body is shared by AVX-512's fallback and IFMA's opening window. -/
def bodyName (enc : Bool) (x : ChaCha20.X86_64.Callee) (b : Poly1305.X86_64.Blocks) : String :=
  "vg_chacha20_poly1305_" ++ (if enc then "seal" else "open") ++ "_body" ++
    (if b = .ifma then "_ifma" else (x.name.drop "vg_chacha20_xor".length).toString)

/-- Forward the tag, the sole stack argument. The eight-byte argument frame
and return address add sixteen stack bytes; the body owns the scratch frame. -/
def bodyCall (enc : Bool) (x : ChaCha20.X86_64.Callee) (b : Poly1305.X86_64.Blocks) : Prog isa :=
  ForwardCall.X86_64.forward 8 1 (bodyName enc x b) (body enc x b)

def smallCall (enc : Bool) (x : ChaCha20.X86_64.Callee) : Prog isa := bodyCall enc x .avx2

/-- VL's large-message code stays inline. The non-VL implementation uses
its callable body, as do the scalar, SSSE3, AVX2, and IFMA implementations. -/
def largeCode (enc : Bool) (x : ChaCha20.X86_64.Callee) : Prog isa :=
  if x.vl then framed (if enc then «seal» x .avx512 else «open» x .avx512)
  else bodyCall enc x .avx512

/-- Choose before allocating working space, so a fallback owns just one
scratch frame. The bulk kernels and length thresholds are unchanged. -/
def sealCode (x : ChaCha20.X86_64.Callee) : Poly1305.X86_64.Blocks → Prog isa
  | .avx512 => .seq (.block (smallTest (smallLim x.small.vl)))
    (Code.iteCold .b (smallCall true x.small) (largeCode true x))
  | b => bodyCall true x b

/-- Opening shares the same VL fallback between AVX-512 and IFMA. -/
def openCode (x : ChaCha20.X86_64.Callee) : Poly1305.X86_64.Blocks → Prog isa
  | .avx512 => .seq (.block (smallTest (openLim x.small.vl)))
    (Code.iteCold .b (smallCall false x.small) (largeCode false x))
  | .ifma => .seq (.block ifmaTest)
    (Code.iteCold .b (smallCall false ChaCha20.X86_64.Callee.avx512vl.small) (bodyCall false x .ifma))
  | b => bodyCall false x b

end VG.Impl.ChaCha20Poly1305.X86_64.Shared
