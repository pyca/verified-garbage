module

public import VerifiedGarbage.Impl.Aes.Arm.Alloc

/-! # ARMv7 register allocation with complemented circuit values

Use the existing allocator, with selected AND gates emitted as OR gates.
Their identifiers describe the De Morgan transformation of the SM4 circuit.
The generated instructions, rather than this allocator, are verified.
-/

@[expose] public section
namespace VG.Impl.Sm4.Arm

open VG.Arm VG.Impl.Aes.Arm VG.Impl.Aes.Circuit

/-- Replace the just-emitted AND with its De Morgan OR. -/
def asOr : List Instr → List Instr
  | .dp .and d n p :: rest => .dp .orr d n p :: rest
  | code => code

def allocateOr (sb : Reg) (outs : List (Nat × Reg)) (ors : List Nat) :
    Rest → Alloc → List Gate → Alloc
  | _, a, [] => a
  | r, a, g :: gs =>
    let a := Alloc.gate sb outs a g r
    let a := if ors.contains g.dst then { a with code := asOr a.code } else a
    allocateOr sb outs ors r.tail a gs

/-- Allocate the circuit, including its explicitly selected OR gates. -/
def compileOr (sb : Reg) (gs : List Gate) (ors : List Nat)
    (ins outs : List (Nat × Reg)) (free : List Reg)
    (ones onesVar fresh : Nat) (spill : List Nat) : List Instr :=
  let r := free.headD .r0
  let init : Alloc :=
    { regs := ins.map (fun (v, r) => (r, v)), slots := [(ones, onesVar)], free := free,
      freeSlots := spill, code := [] }
  let gs := splitXnor onesVar fresh gs
  let a := allocateOr sb outs ors (Rest.ofGates gs) init gs
  let a := Alloc.place sb a outs
  ([.mov r (.imm 0), .dp .sub r r (.imm 1), .str r sb (4 * ones)] : List Instr) ++ a.code.reverse

end VG.Impl.Sm4.Arm
