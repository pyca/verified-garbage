module

public import VerifiedGarbage.Impl.Dsa.Arm.Validate
public import VerifiedGarbage.Impl.Dsa.HelperLayout

/-! # Shared public-key validation on ARMv7

The nested arithmetic helpers save their registers at bytes 8–43. The outer
DSA entry saves its registers at bytes 128–163. This helper uses bytes
168–203, which neither validation nor its arithmetic touches.
-/

@[expose] public section
namespace VG.Impl.Dsa.Arm.PublicValidation
open VG VG.Arm VG.Impl.Dsa.Layout

def slots : List (Reg × Nat) :=
  [(.r4, 168), (.r5, 172), (.r6, 176), (.r7, 180), (.r8, 184),
    (.r9, 188), (.r10, 192), (.r11, 196), (.lr, 200)]

def save : List Instr := .mov .r12 (.reg .r0) :: slots.map fun (r, o) => .str r .r12 o

def restore : List Instr := slots.map fun (r, o) => .ldr r .r12 o

def body (pLen qLen : Nat) : Prog isa :=
  .seq (.block save) (.seq (Validate.publicKey pLen qLen) (.block restore))

def scratch : List (Nat × Nat) := [(0, 64), (116, 4), (168, 36), (256, 15456)]

def layout (pLen qLen : Nat) : Impl.Dsa.PublicValidation.Layout where
  pLen := pLen
  qLen := qLen
  pPointer := Layout.field .p
  qPointer := Layout.field .q
  gPointer := Layout.field .g
  yPointer := Layout.field .y
  mask := Layout.field .mask
  qMinusTwo := qMinusTwo
  scratch := scratch
  size := 15713

def name (pLen qLen : Nat) : String := s!"vg_dsa_public_validate_{(layout pLen qLen).pLen}_{(layout pLen qLen).qLen}"

/-- Pass the workspace and packed public key; keep r12 in a callee-saved
register across the call and its possible linker veneer. -/
def call (pLen qLen : Nat) : Prog isa :=
  .seq (.block [.mov .r11 (.reg .r12), .mov .r0 (.reg .r12), .movw .r1 2048,
      .ldr .r2 .r12 (Layout.field .p), .movw .r3 (BitVec.ofNat 16 (3 * pLen + qLen))])
    (.seq (.call (name pLen qLen) (body pLen qLen)) (.block [.mov .r12 (.reg .r11)]))

end VG.Impl.Dsa.Arm.PublicValidation
