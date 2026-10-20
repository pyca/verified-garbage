module

public import VerifiedGarbage.Impl.RsaPss.Arm
public import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Hash
public import VerifiedGarbage.Spec.Mgf1
import all Init.Data.Nat.Bitwise.Basic

/-!
# RSASSA-PSS on ARMv7: what the proofs need of the hash function

ARMv7 has one implementation of each hash function, so RSASSA-PSS is
registered once per hash function, and its proofs are generic over a
`PssHash`: its code (`Impl.RsaPss.Arm.Hash`), what the proofs know of it as
a Merkle–Damgård hash function (`Proof.Pbkdf2.Md.Arm.HashOK`, with which HMAC
and PBKDF2 call its compression function), that its streaming code's length
field is right (`LenOk`, each hash function's `Shape.len`), the hash function
as RSA's padding takes it (`G`), the taint checks of its length field and
digest code (once for each hash function), and that MGF1's message `H ‖ C`
and its padding fit one block.
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm
open VG.Proof.MdStream (Md)

/-- The length field code: from the byte count in `r4:r5`, the length field
at `r0 + N + B - L`, writing only `r9` (as `Shape.len`,
`Proof/MdStream/Arm/Common.lean`). -/
def LenOk {B N L : Nat} (md : Md B N L) (len : List Instr) : Prop :=
  ∀ s : State, (s.gpr .r0).toNat + (N + B) ≤ 2 ^ 32 →
    InRegions s.wr (State.addr (s.gpr .r0) + BitVec.ofNat 64 (N + (B - L))) L →
    WP isa (.block len) s fun s' => (∀ r, r ≠ .r9 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = VG.WriteBytes.writeBytes s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 (N + (B - L)))
        (md.lenOf (s.gpr .r5 ++ s.gpr .r4))

/-- A hash function, as RSASSA-PSS on ARMv7 uses it. -/
structure PssHash where
  /-- Its code. -/
  H : Impl.RsaPss.Arm.Hash
  /-- What the proofs know of its code as a Merkle–Damgård hash function. -/
  ok : Proof.Pbkdf2.Md.Arm.HashOK H.md
  /-- The length field. -/
  len : LenOk ok.md H.len
  lenAll : ∀ n, n < 2 ^ 32 → ok.md.lenOk n
  /-- The hash function as RSA's padding takes it. -/
  G : Spec.Mgf1.Hash
  hash : ∀ x, G.hash x = ok.SH.H.hash x
  glen : G.len = H.md.st.D
  /-- The taint checks of the digest code (from the hash value at `r0` to
  `r6`) and of the length field (at `r0`). -/
  outCk : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .r6]) (.block H.md.out) hc).isSome = true
  lenCk : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0]) (.block H.len) hc).isSome = true
  /-- MGF1's message `H ‖ C`, `0x80` and the length field fit one block. -/
  one : H.md.st.D + 5 + H.md.L ≤ H.md.st.B

end VG.Proof.RsaPss.Arm
