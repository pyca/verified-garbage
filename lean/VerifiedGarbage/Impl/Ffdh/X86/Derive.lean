module

public import VerifiedGarbage.Impl.Ffdh.X86.KeyGen

/-!
# FFDH on i686: an imported scalar's public value

`vg_ffdh_derive_public`, on the operations of `Domain.lean`: x checked as a
scalar as `vg_ffdh_check_private` checks it (2 returned and zeros written
otherwise, the one branch on x); then `y = g^x mod p` over x's `x_len` bytes
(`powTop`), its range as the acceptance mask (a power of the checked
generator is in its subgroup), y written (zeros unless accepted) and
`3 − 2 flag` returned, without a branch.
-/

@[expose] public section
namespace VG.Impl.Ffdh.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt

/-- Wide slot `j`. -/
local notation:max "sl " j:max => Loc.slot Ctx.wide j
/-- A number of the wide context. -/
local notation "n1" => one Ctx.wide

namespace DerivePublic

/-- `(y, y_len, domain, domain_len, p_len, x, x_len, scratch, scratch_len)`: y the output (synthetic
argument 0, `p_len` bytes at 1), x as 10 and its length as 11. -/
def args : Args := { out := some 0, dom := 2, dlen := 3, plen := 4, x := some 5, ws := 7 }

/-- Zeros written for y, and 2 returned. -/
def fail : Prog isa :=
  .seq (.block [.mov .ecx (.imm 0), .store (sc accOff) .ecx]) (.seq (exportTo 0 1) (ret 2))

/-- `y = g^x mod p` (slot 6), its range as the acceptance; y written, and `3 − 2 flag` returned. -/
def tail : Prog isa :=
  .seq (powTop 10) <| .seq (rangeMask 6) <| .seq (.block [.store (sc accOff) .ecx]) <|
  .seq (copy (sl 6) (sl 19) n1) <| .seq (exportTo 0 1)
    (.block [.alu .add .eax (.reg .eax), .mov .ecx (.imm 3), .alu .sub .ecx (.reg .eax), .mov .eax (.reg .ecx)])

/-- p's setup, g and x, x checked as a scalar, then `tail`. -/
def body : Prog isa :=
  .seq pSetup <| .seq (load (sl 10) n1 4 5) <| .seq (load (sl 13) n1 10 11) <|
  .seq CheckPrivate.bound <| .seq CheckPrivate.scalarMask <| .seq testMask (.ite .e fail tail)

def code : Prog isa := wrap args body

end DerivePublic

end VG.Impl.Ffdh.X86
