import VerifiedGarbage.Impl.Rsa.X86_64.Checked

import VerifiedGarbage.Impl.Rsa.X86_64.WordIO
import VerifiedGarbage.Impl.Rsa.X86_64.Compare8

namespace VG.Impl.Rsa.X86_64.Folded
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public

def next : List Instr :=
  [.mov .rax (.mem (hdr sI)), .alu .sub .rax (.imm 1), .store (hdr sI) .rax]

def squareStep (mm : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (mm aY aY aY) (.block next)

/-- Sixteen squarings, then combine the final exponent bit and conversion out. -/
def exp65537 (mm : Nat → Nat → Nat → Prog isa) : Prog isa :=
  seqs [Precomputed.start, .block [.mov32 .rax (.imm 16), .store (hdr sI) .rax],
    .loop (squareStep mm) .ne, mm aY aX aY]

/-- The computation, once the values are accepted. -/
def rest (mm : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  .block [.mov .rsi (.mem (hdr sIn)), .mov .rcx (.mem (hdr sK)), .mov .rbx (.mem (hdr (sArr aX)))],
  WordIO.load,
  -- The mask of `input < m`.
  .block [.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aX))),
    .mov .r10 (.mem (hdr (sArr aN))), .mov32 .rbp (.imm 0)],
  Compare8.code,
  -- `-m⁻¹`, and the number 1.
  .block ([.store (hdr sMask) .rbp, .mov .rbx (.mem (at0 .r10))] ++ minv ++
    [.store (hdr sMinv) .r15, .mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)]),
  setWord aOne .rcx,
  -- `X = input R mod m`, the exponentiation, and the result.
  mm aXm aX aR2, exp65537 mm,
  .block [.mov .rbx (.mem (hdr (sArr aY))), .mov .rsi (.mem (hdr sOut)), .mov .rcx (.mem (hdr sK)),
    .mov .r15 (.mem (hdr sMask))],
  WordIO.store,
  .block ([.mov .rax (.mem (hdr sMask)), .alu .and .rax (.imm 1)] ++ exit)]

def code (mm : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (.block Precomputed.entry)
    (.seq (seqs (Precomputed.loadWith Compare8.code)) (.ite .e fail (rest mm)))

def dispatch (mm : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (.block [.alu .cmp .r11 (.imm 65537)])
    (.ite .e (code mm) (Precomputed.code mm))

def checked (mm : Nat → Nat → Nat → Prog isa) : Prog isa :=
  Checked.guarded (dispatch mm)

end VG.Impl.Rsa.X86_64.Folded
