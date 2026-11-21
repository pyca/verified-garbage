module

public import VerifiedGarbage.Impl.Ffdh.VettedGroups
public import VerifiedGarbage.Impl.Ffdh.RISCV64.Domain

/-!
# Finite-field Diffie–Hellman on RISC-V: the standard domains

`vg_ffdh_check_domain`, as PPC64LE's (`Impl/Ffdh/PPC64LE/VettedValidation.lean`):
the domain is compared, byte by byte, with each standard domain of its
`p_len` in the table `tableSym` (`VettedGroups.tableWords`); a domain equal
to one is valid, and any other is checked in full (`Domain.checkDomain`).
The comparison uses only `t0`–`t6` and `a5`, and nothing in it branches on
the comparisons; the arguments are kept.
-/

@[expose] public section

namespace VG.Impl.Ffdh.RISCV64.VettedValidation

open VG VG.RISCV64 VG.Impl.Ffdh.VettedGroups

def tableSym : String := "VG_FFDH_VETTED_GROUPS_RISCV"

def tableConsts : List (String × List (BitVec 64)) := [(tableSym, tableWords)]

/-- A byte: the domain's (`a0`, `a1` bytes) at index `a1 − t2` against the
table's at `t0`, their `xor` or-ed into `t4`; `t0` advanced, `t2` counted
down. -/
def compareByte : List Instr :=
  [.sub .t1 .a1 .t2, .add .t1 .a0 .t1, .load .b .t3 .t1 0, .load .b .t1 .t0 0, .logic .xor .t3 .t3 .t1,
    .logic .or .t4 .t4 .t3, .addi .t0 .t0 1, .addi .t2 .t2 (-1)]

/-- `t4 := 0` exactly when the domain's `domain_len` bytes are those at `t0`. -/
def compare : Prog isa := .seq (.block [.addi .t2 .a1 0, .li .t4 0]) (.loop (.block compareByte) (.nonzero .t2))

/-- `t4 := 0` exactly when `p_len` is `g`'s and the domain is a prefix of
`g`'s, whose record is at `t5`. -/
def record (g : Group) : Prog isa :=
  .seq (.block [.addi .t3 .a2 (-(g.len : Int))])
    (.ite (.zero .t3) (.seq (.block [.addi .t0 .t5 8]) compare) (.block [.li .t4 1]))

/-- `a5 |= g.bits` if `t4 = 0`, without a branch: `t6 := (t4 = 0 ? -1 : 0) & bits`. -/
def accumulate (g : Group) : List Instr :=
  [.li .t6 0, .sltu .t6 .t6 .t4, .addi .t6 .t6 (-1), .logicImm .and .t6 .t6 (g.bits : Int), .logic .or .a5 .a5 .t6]

/-- `t5` advanced by `n < 4096` bytes. -/
def advance (n : Nat) : List Instr := [.addi .t5 .t5 ((n / 2 : Nat) : Int), .addi .t5 .t5 ((n - n / 2 : Nat) : Int)]

/-- `a5 |=` the bits of each of `gs` the domain matches, their records from
`t5` on. Every record is compared; nothing branches on the comparisons. -/
def scan : List Group → Prog isa
  | [] => .block []
  | g :: gs => .seq (record g) (.seq (.block (accumulate g ++ advance (8 + 3 * g.len))) (scan gs))

/-- `a5 :=` not zero exactly when the domain is one of the standard ones. -/
def recognize : Prog isa := .seq (.block [.lla .t5 tableSym, .li .a5 0]) (scan groups)

def code : Prog isa :=
  .seq recognize (.ite (.nonzero .a5) (.block [.li .a0 1]) VG.Impl.Ffdh.RISCV64.Domain.checkDomain)

end VG.Impl.Ffdh.RISCV64.VettedValidation
