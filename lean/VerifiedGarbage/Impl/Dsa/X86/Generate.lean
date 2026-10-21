module

public import VerifiedGarbage.Impl.Dsa.X86.Entry

/-! # DSA domain checking and key derivation on i686

Generation reuses the signer's Montgomery arithmetic and public-width
dispatch. A domain has only one generator, so its subgroup power is checked
once; it does not run the public-key validator with two copies of g.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generate
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Dsa.Layout

/-- Range and divisibility checks before the subgroup exponentiation. -/
def domain (pLen qLen : Nat) : Prog isa := Core.sequence [
  Validate.range pLen .p (.input .g) true,
  Validate.minus pLen .p 1 t,
  Core.reduce qLen (.imm (BitVec.ofNat 32 pLen)) (.local t) u,
  Validate.zero qLen (.local u)]

/-- The generator lies in the subgroup of order q. -/
def subgroupWith (pLen : Nat) (power : Prog isa) : Prog isa :=
  .seq power (Validate.isOne pLen (.local t))

def subgroup (pLen qLen : Nat) : Prog isa :=
  subgroupWith pLen (Core.power pLen qLen .p (.input .g) (.input .q) t)

/-- Accumulate every algebraic domain check under the shape mask. -/
def parameters (pLen qLen : Nat) : Prog isa :=
  .seq (domain pLen qLen) (subgroup pLen qLen)

/-- The shape checker also computes a digest-prefix width. Give its unused
length field the public p_len; generation never reads a digest. -/
def checkArguments : List (Nat × Field) :=
  [(0, .p), (2, .pLen), (3, .qLen), (2, .digestLen)]

/-- `vg_dsa_check_parameters(params, params_len, p_len, q_len,
scratch, scratch_len)`. -/
def checkEntry : List Instr :=
  Entry.openScratch 4 ++ Entry.saveArguments checkArguments ++ Entry.keyPointers

def checkSizedWith (compute : Nat → Nat → Prog isa) (pLen qLen : Nat) : Prog isa :=
  .seq (Shape.check pLen qLen)
    (.ite .e (.block [.mov .eax (.imm 0)])
      (.seq (compute pLen qLen) (.block SignVerify.result)))

def checkSized (pLen qLen : Nat) : Prog isa := checkSizedWith parameters pLen qLen

/-- Shared public-width dispatch for checking and derivation. -/
def dispatch (sized : Nat → Nat → Prog isa) : List (Nat × Nat) → Prog isa
  | [] => .block [.mov .eax (.imm 0)]
  | (pLen, qLen) :: rest =>
    .seq (Entry.widthMatch pLen qLen)
      (.ite .e (sized pLen qLen) (dispatch sized rest))

def checkDispatch (widths : List (Nat × Nat)) : Prog isa := dispatch checkSized widths

def checkParametersWith (sized : Nat → Nat → Prog isa) : Prog isa := Core.sequence [
  .block checkEntry,
  dispatch sized [(128, 20), (256, 28), (256, 32), (384, 32), (256, 20)],
  .block Entry.restore]

def checkParameters : Prog isa := checkParametersWith checkSized

def deriveArguments : List (Nat × Field) :=
  [(0, .out), (2, .p), (4, .pLen), (6, .qLen), (4, .digestLen), (5, .nonce)]

/-- `vg_dsa_derive_key(out, out_len, params, params_len, p_len, x,
q_len, scratch, scratch_len)`. The supplied scalar and computed y are
separate from the signer's nonce and signature. -/
def deriveEntry : List Instr :=
  Entry.openScratch 7 ++
  Entry.saveArguments deriveArguments ++ Entry.keyPointers

/-- Once the domain is checked, derive y and check both component ranges.
The identity `(g^x)^q = (g^q)^x` supplies y's subgroup check. -/
def deriveCompute (pLen qLen : Nat) : Prog isa := Core.sequence [
  parameters pLen qLen,
  Validate.range qLen .q (.input .nonce),
  Core.power pLen qLen .p (.input .g) (.input .nonce) t2,
  Validate.range pLen .p (.local t2) true]

def copyMaskedStep : List Instr :=
  [
    .movzx8 .eax (at_ .esi 0), .alu .and .eax (.reg .ebx), .store8 (at_ .edx 0) .al,
    .alu .add .esi (.imm 1), .alu .add .edx (.imm 1), .alu .sub .ecx (.imm 1)]

/-- Copy ecx bytes from esi to edx under the mask in ebx. -/
def copyMasked : Prog isa := .loop (.block copyMaskedStep) .ne

/-- Copy consecutive components, retaining the output cursor and mask. -/
def copyPart (input : Pointer) (len : Nat) : Prog isa :=
  .seq (.block (Core.pointer input ++ [.mov .ecx (.imm (BitVec.ofNat 32 len))])) copyMasked

def copyParts : List (Pointer × Nat) → Prog isa
  | [] => .block []
  | (input, len) :: rest =>
    .seq (copyPart input len) (copyParts rest)

/-- Output is p||q||g||y||x; edx advances continuously through all three
copies. The validation mask applies to every byte, including the domain. -/
def writeKey (pLen qLen : Nat) : Prog isa := Core.sequence [
  .block [
    .mov .ebx (.mem (sc (Layout.field .mask))),
    .mov .edx (.mem (sc (Layout.field .out)))],
  copyParts [(.input .p, 2 * pLen + qLen), (.local t2, pLen), (.input .nonce, qLen)],
  .block SignVerify.result]

/-- A rejected shape clears the entire packed private key. -/
def deriveFailure (pLen qLen : Nat) : Prog isa := Core.sequence [
  .block [
    .mov .esi (.mem (sc (Layout.field .out))),
    .mov .ecx (.imm (BitVec.ofNat 32 (3 * pLen + 2 * qLen))), .mov .eax (.imm 0)],
  .loop (.block [.store8 (at_ .esi 0) .al, .alu .add .esi (.imm 1),
    .alu .sub .ecx (.imm 1)]) .ne]

def deriveSizedWith (compute : Nat → Nat → Prog isa) (pLen qLen : Nat) : Prog isa :=
  .seq (Shape.check pLen qLen)
    (.ite .e (deriveFailure pLen qLen) (.seq (compute pLen qLen) (writeKey pLen qLen)))

def deriveSized (pLen qLen : Nat) : Prog isa := deriveSizedWith deriveCompute pLen qLen

def deriveDispatch (widths : List (Nat × Nat)) : Prog isa := dispatch deriveSized widths

def deriveKeyWith (sized : Nat → Nat → Prog isa) : Prog isa := Core.sequence [
  .block deriveEntry,
  dispatch sized [(128, 20), (256, 28), (256, 32), (384, 32), (256, 20)],
  .block Entry.restore]

def deriveKey : Prog isa := deriveKeyWith deriveSized

end VG.Impl.Dsa.X86.Generate
