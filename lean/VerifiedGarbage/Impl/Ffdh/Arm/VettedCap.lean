module

public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey

/-! Install a recognized public scalar cap without duplicating the saved-slot stores. -/

@[expose] public section
namespace VG.Impl.Ffdh.Arm.VettedCap
open VG VG.Arm

structure Choice where
  bits : BitVec 16
  width : BitVec 16
  mask : BitVec 16

def choices : List Choice :=
  [⟨225, 29, 1⟩, ⟨275, 35, 7⟩, ⟨325, 41, 31⟩, ⟨375, 47, 127⟩, ⟨400, 50, 255⟩]

def test (c : Choice) : List Instr := [.movw .r12 c.bits, .cmp .r11 (.reg .r12)]
def selected (c : Choice) : List Instr := [.movw .r6 c.width, .movw .r3 c.mask]

def choose : List Choice → Prog isa
  | [] => .block []
  | c :: cs => .seq (.block (test c)) (.ite .eq (.block (selected c)) (choose cs))

def result : List Choice → BitVec 32 → BitVec 32 × BitVec 32 → BitVec 32 × BitVec 32
  | [], _, old => old
  | c :: cs, bits, old =>
    if bits - c.bits.setWidth 32 == 0 then (c.width.setWidth 32, c.mask.setWidth 32)
    else result cs bits old

def load : List Instr := [.ldrSp .r6 20, .ldrSp .r3 68]

def code : Prog isa := .seq (.block load)
  (.seq (choose choices) (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.boundSave))

end VG.Impl.Ffdh.Arm.VettedCap

@[expose] public section
namespace VG.Impl.Ffdh.Arm.VettedCap
open VG VG.Arm

/-- Recognized groups skip the general public-bound scan. -/
def bound (recognizer : Prog isa) : Prog isa :=
  .seq recognizer (.seq VG.Impl.Ffdh.Arm.Domain.testFlag
    (.ite .ne code VG.Impl.Ffdh.Arm.Domain.GenerateKey.bound))

end VG.Impl.Ffdh.Arm.VettedCap
