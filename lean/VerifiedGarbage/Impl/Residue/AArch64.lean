module

public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# Clearing registers before returning (AArch64)

`withClears rs vs fl c` runs `c`, then zeroes the registers `rs` (`movz`)
and the vector registers `vs` (`movi v.2d, #0`), and, if `fl` names a
register, sets the flags from it (`tst fl, fl`), which is zero by then if it is
one of `rs`: what `c` leaves in them may be secret, which its caller cannot
clear. The clears run once, after `c`, on every path.
-/

@[expose] public section

namespace VG.Impl.Residue.AArch64

open VG.AArch64

/-- The instructions that clear `rs`, `vs` and, from `fl`, the flags. -/
def clears (rs : List Reg) (vs : List VReg) (fl : Option Reg) : List Instr :=
  rs.map (fun r => .movz .x r 0 0) ++ vs.map (fun v => .vop (.movi0 v)) ++
    match fl with
    | some r => [.tst .x r r]
    | none => []

/-- `c`, then the clears of `rs`, `vs` and the flags (`clears`). -/
def withClears (rs : List Reg) (vs : List VReg) (fl : Option Reg) (c : Prog isa) : Prog isa :=
  .seq c (.block (clears rs vs fl))

/-- `withClears rs vs fl c`, then the high halves of `hs` cleared from `z`
(`mov v.d[1], z`), which is zero by then if it is one of `rs`: the calling
convention preserves only the low halves of `v8`–`v15`, which `c` restores. -/
def withClearsHi (rs : List Reg) (vs : List VReg) (fl : Option Reg) (z : Reg) (hs : List VReg)
    (c : Prog isa) : Prog isa :=
  .seq c (.block (clears rs vs fl ++ hs.map (fun v => .vop (.ins .d2 v 1 z))))

end VG.Impl.Residue.AArch64
