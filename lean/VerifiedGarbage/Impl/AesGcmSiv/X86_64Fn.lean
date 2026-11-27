module

public import VerifiedGarbage.Impl.AesGcmSiv.X86_64Reg
public import VerifiedGarbage.Impl.AesGcmSiv.X86_64Stitch
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Impl.Scrub.X86_64.Fn

/-! # AES-GCM-SIV on x86-64: the functions as emitted

`vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open`: in registers, with
interleaved loops `lp` if any (`sealReg`, `openReg`, in 784 bytes of
stack), or over the callees `c` and the block function `e`, in 3856 bytes
(`sealSoft`, `openSoft`), and with the AVX2 copies, by the lengths unless
the code takes them already (`sealAvx2`, `openAvx2`). Each is followed by
its cleanup (`Impl.Scrub.X86_64.scrubAll v rb n`): every vector register at
the level `v` and every caller-saved register but the `rb` bits of the
result cleared, and its whole stack wiped.
-/

@[expose] public section

namespace VG.Impl.AesGcmSiv.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (VecLevel scrubAll)
open VG.Impl.AesGcm.X86_64 (Callees Fn at_)
open VG.Impl.StackScratch.X86_64 (withStackArgScratch)
open VG.Impl.AesGcmSiv.X86_64Stitch (Loops)

/-- `seal` in registers, with the loops `lp` if any. -/
def regSealCode : Option Loops → Prog isa
  | some lp => Impl.AesGcmSiv.X86_64Reg.sealL lp
  | none => Impl.AesGcmSiv.X86_64Reg.seal

/-- `open` in registers, as `regSealCode`. -/
def regOpenCode : Option Loops → Prog isa
  | some lp => Impl.AesGcmSiv.X86_64Reg.openL lp
  | none => Impl.AesGcmSiv.X86_64Reg.open

/-- `seal` over the callees `c` and `e`, with the loops `lp` if any. -/
def sealCode (c : Callees) (e : Fn) (wide : Bool) : Option Loops → Prog isa
  | some lp => Impl.AesGcmSiv.X86_64Stitch.«seal» lp c e wide
  | none => Impl.AesGcmSiv.X86_64.«seal» c e wide

/-- `open` over the callees `c` and `e`, as `sealCode`. -/
def openCode (c : Callees) (e : Fn) (wide : Bool) : Option Loops → Prog isa
  | some lp => Impl.AesGcmSiv.X86_64Stitch.«open» lp c e wide
  | none => Impl.AesGcmSiv.X86_64.«open» c e wide

/-- Clears the carry flag exactly when `len ||| aad_len` is 128 or more. -/
def cmpLens : List Instr :=
  [.mov .rax (.mem (at_ .rsp 8)), .alu .or .rax (.reg .r8), .alu .cmp .rax (.imm 128)]

/-- `wide` when the text or the additional data is 128 bytes or more, and
`narrow` otherwise. -/
def bySize (wide narrow : Prog isa) : Prog isa :=
  .seq (.block cmpLens) (Code.iteCold .ae wide narrow)

/-- `seal` with the AVX2 copies: by the lengths unless `w`, where the code
takes them already. -/
def sealAvx2Code (c : Callees) (e : Fn) (w : Bool) (lp : Option Loops) : Prog isa :=
  if w then withStackArgScratch 3848 2 (sealCode c e true lp)
  else bySize (withStackArgScratch 3848 2 (sealCode c e true lp)) (withStackArgScratch 3848 2 (sealCode c e false lp))

/-- `open` with the AVX2 copies, as `sealAvx2Code`. -/
def openAvx2Code (c : Callees) (e : Fn) (w : Bool) (lp : Option Loops) : Prog isa :=
  if w then withStackArgScratch 3848 2 (openCode c e true lp)
  else bySize (withStackArgScratch 3848 2 (openCode c e true lp)) (withStackArgScratch 3848 2 (openCode c e false lp))

/-- `Spec.GcmSiv.sealApi`'s function in registers, as emitted. -/
def sealReg (v : VecLevel) (lp : Option Loops) : Prog isa :=
  scrubAll v 0 784 (withStackArgScratch 776 2 (regSealCode lp))

/-- `Spec.GcmSiv.openApi`'s function in registers, as emitted. -/
def openReg (v : VecLevel) (lp : Option Loops) : Prog isa :=
  scrubAll v 32 784 (withStackArgScratch 776 2 (regOpenCode lp))

/-- `Spec.GcmSiv.sealApi`'s function over `c` and `e`, as emitted. -/
def sealSoft (v : VecLevel) (c : Callees) (e : Fn) (wide : Bool) (lp : Option Loops) : Prog isa :=
  scrubAll v 0 3856 (withStackArgScratch 3848 2 (sealCode c e wide lp))

/-- `Spec.GcmSiv.openApi`'s function over `c` and `e`, as emitted. -/
def openSoft (v : VecLevel) (c : Callees) (e : Fn) (wide : Bool) (lp : Option Loops) : Prog isa :=
  scrubAll v 32 3856 (withStackArgScratch 3848 2 (openCode c e wide lp))

/-- `Spec.GcmSiv.sealApi`'s function with the AVX2 copies, as emitted. -/
def sealAvx2 (v : VecLevel) (c : Callees) (e : Fn) (w : Bool) (lp : Option Loops) : Prog isa :=
  scrubAll v 0 3856 (sealAvx2Code c e w lp)

/-- `Spec.GcmSiv.openApi`'s function with the AVX2 copies, as emitted. -/
def openAvx2 (v : VecLevel) (c : Callees) (e : Fn) (w : Bool) (lp : Option Loops) : Prog isa :=
  scrubAll v 32 3856 (openAvx2Code c e w lp)

/-- The callees of a stub: every function's code empty, called by its own
name. -/
def stubCallees : Callees :=
  ⟨⟨"c", .block []⟩, ⟨"k", .block []⟩, ⟨"g", .block []⟩, ⟨"e", .block []⟩, ⟨"d", .block []⟩⟩

/-- The block function of a stub. -/
def stubEcb : Fn := ⟨"b", .block []⟩

end VG.Impl.AesGcmSiv.X86_64.Fn
