module

public import VerifiedGarbage.Impl.Ffdh.VettedGroups
public import VerifiedGarbage.Impl.Ffdh.PPC64LE.Domain

/-! Exact standard-domain recognition using only caller-saved registers.
PPC64LE's static-address instruction changes LR; r12 preserves it across the scan.
The domain arguments, scratch, and stack remain untouched. -/

@[expose] public section
namespace VG.Impl.Ffdh.PPC64LE.VettedValidation
open VG VG.PPC64LE VG.Impl.Ffdh.VettedGroups

def tableSym : String := "VG_FFDH_VETTED_GROUPS_PPC"
def tableConsts : List (String × List (BitVec 64)) := [(tableSym, tableWords)]

/-- r3 is the source and r4 its public length; r8 is the table cursor.
Use r9 as the countdown, r10 as the OR of differences, and r0/r11 as temporaries. -/
def compareByte : List Instr := [.sub .r11 .r4 .r9, .add .r11 .r3 .r11,
  .lbz .r0 .r11 0, .lbz .r11 .r8 0, .logic .xor .r0 .r0 .r11,
  .logic .or .r10 .r10 .r0, .addi .r8 .r8 1, .subi .r9 .r9 1]

def compare : Prog isa := .seq (.block [.addi .r9 .r4 0, .li .r10 0])
  (.loop (.block compareByte) (.nonzero .d .r9))

def record (g : Group) (offset : Nat) : Prog isa :=
  .seq (.block [.subi .r0 .r5 g.len])
    (.ite (.zero .d .r0)
      (.seq (.block [.adrSym .r8 tableSym, .addi .r8 .r8 (offset + 8)]) compare)
      (.block [.li .r10 1]))

def scan : List Group → Nat → Prog isa
  | [], _ => .block [.li .r8 0]
  | g :: gs, offset => .seq (record g offset)
    (.ite (.zero .d .r10) (.block [.li .r8 g.bits]) (scan gs (offset + 8 + 3 * g.len)))

def recognize : Prog isa := .seq (.block [.mflr .r12])
  (.seq (scan groups 0) (.block [.mtlr .r12]))

def code : Prog isa := .seq recognize
  (.ite (.nonzero .d .r8) (.block [.li .r3 1]) VG.Impl.Ffdh.PPC64LE.Domain.checkDomain)

end VG.Impl.Ffdh.PPC64LE.VettedValidation
