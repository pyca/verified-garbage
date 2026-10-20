module

public import VerifiedGarbage.Impl.P384.Ops
public import VerifiedGarbage.Impl.Ecdh.AArch64

/-!
# P-384's Jacobian doubling for ECDH's window on AArch64, before allocation

`raw a b` is the window's doubling `dblJ` (3 products and 5 squares, `a = -3`)
from the point at `a` into the point at `b`, as a straight line of `Ops.op`.
The untrusted register allocator (`Impl/P256/VerifyRegisters.lean`, run by
`lean/GenerateP384Ecdh.lean`) keeps its values in the registers `regs`
(`x1`–`x17` and `x21`–`x25`, which ECDH saves on entry), stores only `b`'s
coordinates (`keep`), and spills to `spill`: the slots of the window's entry
`E`, the addition's temporaries and `tmp`, which hold nothing the window reads
after its doublings. Its output, `Impl/P384/EcdhAllocatedCode.lean`, is
checked against `raw` by certificates.
-/

@[expose] public section

namespace VG.Impl.P384.EcdhDouble
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64

/-- ECDH's window over P-384. -/
def K : WinCfg := Impl.Ecdsa.AArch64.p384.winCfg Impl.Ecdh.AArch64.PX Impl.Ecdh.AArch64.PY

/-- `b = 2 a` in Jacobian coordinates. -/
def raw (a b : Pt) : List Instr := (dblJ K.S a b).flatMap Ops.op

/-- The words of the point at `b`. -/
def keep (b : Pt) (off : Nat) : Bool := [b.x, b.y, b.z].any fun x => x ≤ off && off < x + 48

/-- The registers the allocation may use. -/
def regs : List Reg :=
  [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17,
   .x21, .x22, .x23, .x24, .x25]

/-- The slots spills may use. -/
def spillSlots : List Nat :=
  [K.E.x, K.E.y, K.E.z, K.S.t0, K.S.t1, K.S.t2, K.S.t3, K.S.t4, K.S.t5, K.M.tmp]

/-- Their words. -/
def spill : List Nat := spillSlots.flatMap fun x => (List.range 6).map (x + 8 * ·)

end VG.Impl.P384.EcdhDouble
