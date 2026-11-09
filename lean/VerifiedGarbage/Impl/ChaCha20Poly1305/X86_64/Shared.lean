module

public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.Stitch
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Impl.ForwardCall.X86_64

/-! # ChaCha20-Poly1305 entry points sharing the stitched fallbacks -/

@[expose] public section
namespace VG.Impl.ChaCha20Poly1305.X86_64.Shared
open VG.X86_64
open VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Impl.ChaCha20.X86_64 (at_)

deriving instance DecidableEq for Poly1305.X86_64.Blocks

/-- Allocate and wipe the ordinary working space. -/
def framed (c : Prog isa) : Prog isa :=
  StackScratch.X86_64.withStackArgScratchWipedX 1728 1 42 c

/-- `seal`'s framed body, without an entry-point fallback choice. -/
def body (x : ChaCha20.X86_64.Callee) (b : Poly1305.X86_64.Blocks) : Prog isa :=
  framed (if b = .avx2 then sealStitched { x with pass := 512 } .avx2 else «seal» x b)

/-- The body family follows the entry points' CPU variants. The stitched
VL body is shared by AVX-512's fallback and IFMA's opening window; `open`'s
AVX-512VL body for more data is `_avx512vl_large`. -/
def bodyName (enc : Bool) (x : ChaCha20.X86_64.Callee) (b : Poly1305.X86_64.Blocks) : String :=
  "vg_chacha20_poly1305_" ++ (if enc then "seal" else "open") ++ "_body" ++
    (if b = .ifma then "_ifma" else (x.name.drop "vg_chacha20_xor".length).toString) ++
    (if !enc && x.vl && b = .avx512 then "_large" else "")

/-- Forward the tag, the sole stack argument. The eight-byte argument frame
and return address add sixteen stack bytes; the body owns the scratch frame. -/
def bodyCall (x : ChaCha20.X86_64.Callee) (b : Poly1305.X86_64.Blocks) : Prog isa :=
  ForwardCall.X86_64.forward 8 1 (bodyName true x b) (body x b)

def smallCall (x : ChaCha20.X86_64.Callee) : Prog isa := bodyCall x .avx2

/-- VL's large-message code stays inline. The non-VL implementation uses
its callable body, as do the scalar, SSSE3, AVX2, and IFMA implementations. -/
def largeCode (x : ChaCha20.X86_64.Callee) : Prog isa :=
  if x.vl then framed («seal» x .avx512) else bodyCall x .avx512

/-- Choose before allocating working space, so a fallback owns just one
scratch frame. The bulk kernels and length thresholds are unchanged. -/
def sealCode (x : ChaCha20.X86_64.Callee) : Poly1305.X86_64.Blocks → Prog isa
  | .avx512 => .seq (.block (smallTest (smallLim x.small.vl)))
    (Code.iteCold .b (smallCall x.small) (largeCode x))
  | b => bodyCall x b

/-! ## Opening

`open` and `open_to` call the same functions, `vg_chacha20_poly1305_open_body*`,
whose code is what they share after their entries (`openInner`): from
`open`'s entry state, with the ciphertext's address in `r11` and the
destination's in `r8`. Each lays that entry out below its own stack
arguments, which no function may write: `work`, then `tag`, pushed, are the
callee's stack arguments (`callOpen`), below a word that keeps the callee's
`rsp` as a call from an aligned stack leaves it. -/

/-- The code of `vg_chacha20_poly1305_open_body*`: `openShared`, or the
stitched `openStitchedShared` with the AVX2 implementation of
`vg_poly1305_blocks`, after 41 bytes of padding (in `rax`, which it then
loads), which keep its code at the offsets (modulo 64) it had after the frame
of `work` and `mov r11, r8`, when it was inline there. -/
def openInner (x : ChaCha20.X86_64.Callee) (b : Poly1305.X86_64.Blocks) : Prog isa :=
  if b = .avx2 then .seq (.block (padIns .rax 41)) (openStitchedShared x .avx2) else openShared x b

/-- A call of the body, with `work` in `rax` and `tag` in `r10`, pushed
below `r11` (a word of padding). -/
def callOpen (x : ChaCha20.X86_64.Callee) (b : Poly1305.X86_64.Blocks) : Prog isa :=
  .frame (.push [.r11, .rax, .r10]) (.call (bodyName false x b) (openInner x b)) (.pop .r10 3)

/-- `open`'s entry, in its frame of `work`: the data is the ciphertext,
`work` and `tag` in `rax` and `r10`. -/
def openArgs : List Instr :=
  [.mov .r11 (.reg .r8), .mov .rax (.mem (at_ .rsp 16)), .mov .r10 (.mem (at_ .rsp 8))]

/-- `open` of an instance, without a choice by the length, in its frame of
`work`. -/
def openCall (x : ChaCha20.X86_64.Callee) (b : Poly1305.X86_64.Blocks) : Prog isa :=
  .seq (.block openArgs) (callOpen x b)

/-- Opening chooses as sealing does, and shares the AVX-512VL fallback
between AVX-512 and IFMA. -/
def openCode (x : ChaCha20.X86_64.Callee) : Poly1305.X86_64.Blocks → Prog isa
  | .avx512 => .seq (.block (smallTest (openLim x.small.vl)))
    (Code.iteCold .b (framed (openCall x.small .avx2)) (framed (openCall x .avx512)))
  | .ifma => .seq (.block ifmaTest)
    (Code.iteCold .b (framed (openCall ChaCha20.X86_64.Callee.avx512vl.small .avx2)) (framed (openCall x .ifma)))
  | b => framed (openCall x b)

end VG.Impl.ChaCha20Poly1305.X86_64.Shared
