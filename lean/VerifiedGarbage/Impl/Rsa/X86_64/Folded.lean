import VerifiedGarbage.Impl.Rsa.X86_64.Checked
import VerifiedGarbage.Impl.Rsa.X86_64.WordIO
import VerifiedGarbage.Impl.Rsa.X86_64.Compare8

/-!
# `vg_rsa_public_precomputed_checked` on x86-64

`vg_rsa_public_precomputed`'s computation (`Impl/Rsa/X86_64.lean`) with
words in and out (`WordIO`, `Compare8`), for an odd `e` (`Checked.guarded`):
the exponentiation by `e - 1` (`Precomputed.expLoop`), then one
multiplication by the input itself, which adds the last bit of `e` and
leaves Montgomery form at once (`Y x R⁻¹ = x^e` for `Y = x^(e-1) R`).
-/

namespace VG.Impl.Rsa.X86_64.Folded
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public

/-- The computation, once the values are accepted. -/
def rest (mm : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  .block [.mov .rsi (.mem (hdr sIn)), .mov .rcx (.mem (hdr sK)), .mov .rbx (.mem (hdr (sArr aX)))],
  WordIO.load,
  -- The mask of `input < m`.
  .block [.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aX))),
    .mov .r10 (.mem (hdr (sArr aN))), .mov32 .rbp (.imm 0)],
  Compare8.code,
  -- `-m⁻¹`, and the number 1.
  .block (([.store (hdr sMask) .rbp, .mov .rbx (.mem (at0 .r10))] : List Instr) ++ minv ++
    ([.store (hdr sMinv) .r15, .mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)] : List Instr)),
  setWord aOne .rcx,
  -- `X = input R mod m`, the exponentiation, and the result.
  mm aXm aX aR2, Precomputed.expLoop mm, mm aY aX aY,
  .block [.mov .rbx (.mem (hdr (sArr aY))), .mov .rsi (.mem (hdr sOut)), .mov .rcx (.mem (hdr sK)),
    .mov .r15 (.mem (hdr sMask))],
  WordIO.store,
  .block (([.mov .rax (.mem (hdr sMask)), .alu .and .rax (.imm 1)] : List Instr) ++ exit)]

def code (mm : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (.block Precomputed.entry)
    (.seq (seqs (Precomputed.loadWith Compare8.code)) (.ite .e fail (rest mm)))

def checked (mm : Nat → Nat → Nat → Prog isa) : Prog isa :=
  Checked.guarded (code mm)

end VG.Impl.Rsa.X86_64.Folded
