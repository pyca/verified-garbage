module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-!
# PPC64LE: code that writes none of a set of registers

`avoids rs i`: instruction `i` writes no register of the set `rs` (a
`RegSet`, which the kernel tests with `Nat` arithmetic). Checking it on every
instruction of code (`Code.allInstrs`) is several times faster for the
kernel than `rs.all fun r => dstOf i != some r` with a list, which compares
each destination with each register (`nv_of_avoids`).
-/

@[expose] public section

namespace VG.PPC64LE

/-- Instruction `i` writes no register of `rs`. -/
def avoids (rs : RegSet Reg) (i : Instr) : Bool :=
  match dstOf i with
  | none => true
  | some d => !rs.mem d

theorem nv_of_avoids {c : Prog isa} {rs : List Reg}
    (h : c.allInstrs (avoids (RegSet.ofList rs)) = true) :
    ∀ r ∈ rs, ∀ i ∈ instrs c, dstOf i ≠ some r := by
  rw [Code.allInstrs_eq] at h
  intro r hr i hi e
  have hi' := List.all_eq_true.mp h i hi
  have hm : (RegSet.ofList rs).mem r = true := RegSet.mem_ofList.mpr hr
  simp only [avoids, e, hm, Bool.not_true, Bool.false_eq_true] at hi'

theorem all_of_avoids {l : List Instr} {rs : List Reg}
    (h : l.all (avoids (RegSet.ofList rs)) = true) :
    (l.all fun i => rs.all fun r => dstOf i != some r) = true := by
  refine List.all_eq_true.mpr fun i hi => List.all_eq_true.mpr fun r hr => bne_iff_ne.mpr fun e => ?_
  have hi' := List.all_eq_true.mp h i hi
  have hm : (RegSet.ofList rs).mem r = true := RegSet.mem_ofList.mpr hr
  simp only [avoids, e, hm, Bool.not_true, Bool.false_eq_true] at hi'

end VG.PPC64LE
