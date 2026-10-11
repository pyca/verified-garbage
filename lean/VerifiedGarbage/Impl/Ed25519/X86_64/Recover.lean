module

public import VerifiedGarbage.Impl.Ed25519.X86_64.FieldCheck

/-!
Recover a candidate x-coordinate from y, before checking its square and sign.

The square root's power `(u v⁷)^((p - 5) / 8)` of both points a verification decodes is
computed before either is decoded (`decodePowers`): the two exponentiations, each a long chain
of dependent multiplications, run side by side (`rootPower2`), so that each one's
multiplications overlap the other's. The candidate (`recoverCandidate`) then takes the power
from slot 15.
-/

@[expose] public section

namespace VG.Impl.Ed25519.X86_64

open VG.X86_64

/-- y is in slot 1: d into slot 16, `1` into slot 4, `u = y² - 1` into slot 6, `v = d y² + 1`
into slot 7 and `v³` into slot 9. -/
def recoverPrepOps : List FieldOp := [
  .const 16 Spec.Ed25519.d, .const 4 1, .sqr 5 1, .sub 6 5 4,
  .mul 7 16 1, .mul 7 7 1, .add 7 7 4,
  .sqr 8 7, .mul 9 8 7]

/-- `recoverPrepOps`, then the power's input `u v⁷` into slot `o`. -/
def rootInputOps (o : Slot) : List FieldOp := recoverPrepOps ++ [.sqr 10 9, .mul 10 10 7, .mul o 6 10]

def recoverFinishOps : List FieldOp := [
  .const 5 0, .sub 12 5 6, .mul 0 6 9, .mul 0 0 15, .mul 11 7 0, .mul 11 11 0]

/-- The candidate `u v³ (u v⁷)^((p - 5) / 8)` into slot 0, with the power in slot 15. -/
def recoverCandidate (fld : Arith) : Prog isa :=
  .block (fieldCode fld (recoverPrepOps ++ recoverFinishOps))

/-- Slots `o` and `o'` become slots `a` and `a'` squared `n` times, the two runs of squarings
interleaved (`rbx` counts them). -/
def sqn2 (fld : Arith) (o a o' a' : Slot) (n : Nat) : Prog isa :=
  .seq (.block (fieldCode fld [.sqr o a, .sqr o' a'] ++ [.mov32 .rbx (.imm (BitVec.ofNat 32 (n - 1)))]))
    (.loop (.block (fieldCode fld [.sqr o o, .sqr o' o'] ++ [.alu .sub .rbx (.imm 1)])) .ne)

/-- `rootPower`'s chain for slot 2 (into slot 15, through slots 14–17) and for slot 3 (into
slot 19, through slots 18–21) at once, each step beside its copy. -/
def rootPower2 (fld : Arith) : Prog isa :=
  .seq (.block (fieldCode fld [.sqr 14 2, .sqr 18 3])) <|
  .seq (.block (fieldCode fld [.sqr 15 14, .sqr 19 18, .sqr 15 15, .sqr 19 19])) <|
  .seq (.block (fieldCode fld [.mul 15 2 15, .mul 19 3 19, .mul 14 14 15, .mul 18 18 19,
    .sqr 16 14, .sqr 20 18, .mul 15 15 16, .mul 19 19 20])) <|
  .seq (sqn2 fld 16 15 20 19 5) <| .seq (.block (fieldCode fld [.mul 15 16 15, .mul 19 20 19])) <|
  .seq (sqn2 fld 16 15 20 19 10) <| .seq (.block (fieldCode fld [.mul 16 16 15, .mul 20 20 19])) <|
  .seq (sqn2 fld 17 16 21 20 20) <| .seq (.block (fieldCode fld [.mul 16 17 16, .mul 20 21 20])) <|
  .seq (sqn2 fld 16 16 20 20 10) <| .seq (.block (fieldCode fld [.mul 15 16 15, .mul 19 20 19])) <|
  .seq (sqn2 fld 16 15 20 19 50) <| .seq (.block (fieldCode fld [.mul 16 16 15, .mul 20 20 19])) <|
  .seq (sqn2 fld 17 16 21 20 100) <| .seq (.block (fieldCode fld [.mul 16 17 16, .mul 20 21 20])) <|
  .seq (sqn2 fld 16 16 20 20 50) <| .seq (.block (fieldCode fld [.mul 15 16 15, .mul 19 20 19])) <|
  .seq (sqn2 fld 15 15 19 19 2) (.block (fieldCode fld [.mul 15 15 2, .mul 19 19 3]))

end VG.Impl.Ed25519.X86_64
