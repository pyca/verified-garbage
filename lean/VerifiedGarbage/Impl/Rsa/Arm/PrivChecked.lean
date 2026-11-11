module

public import VerifiedGarbage.Impl.Bignum.Arm.PcFn
public import VerifiedGarbage.Impl.Bignum.Arm.CompareBytes
public import VerifiedGarbage.Impl.Bignum.Arm.CopyBytes

/-! # ARMv7 private RSA with public re-exponentiation before release

Calls the verified CRT, public precomputation, and precomputed public operation.
The CRT result stays in a private stack buffer until its public operation
matches the input. The release writes masked bytes and clears the temporary.
All calls and the release run regardless of secret acceptance or comparison.
-/

@[expose] public section
namespace VG.Impl.Rsa.Arm.PrivChecked
open VG VG.Arm

/-- Encodable, ABI-aligned inner frame, with outgoing arguments at 0..55. -/
def frameBytes : Nat := 3328
def oOut : Nat := 64
def oN : Nat := 68
def oK : Nat := 72
def oE : Nat := 76
def oIn : Nat := 84
def oR1 : Nat := 88
def oR3 : Nat := 92
/-- Maximum 1024-byte private intermediate. -/
def oM : Nat := 128
/-- Maximum 2048-byte public precomputation. -/
def oPre : Nat := 1152
/-- Incoming arguments follow the inner frame and the 56-byte register save. -/
def arg (j : Nat) : Nat := frameBytes + 56 + 4 * j

def preWords (r : Reg) : List Instr :=
  [.ldrSp r oK, .dp .add r r (.imm 7), .mov r (.shifted r .lsr 3), .mov r (.shifted r .lsl 1)]

def savedArguments : List (Reg × Nat) := [(.r0, oOut), (.r2, oN), (.r3, oK)]
def saveRegs : List Instr := .addSp .r12 0 :: savedArguments.map (fun p => .str p.1 .r12 p.2)
def saveIncomingSlot (j : Nat) : List Instr := [.ldrSp .r0 (arg j), .str .r0 .r12 (oE + 4 * j)]
def saveIncoming : List Instr := (List.range 3).flatMap saveIncomingSlot
def saveSlots : List Instr := saveRegs ++ saveIncoming

def copyArg (j : Nat) : List Instr := [.ldrSp .r0 (arg (j + 2)), .str .r0 .r12 (4 * j)]
def copyArgs : List Instr := (List.range 14).flatMap copyArg

def crtRegs : List Instr := [.addSp .r0 oM, .mov .r1 (.reg .r3)]
def crtArgs : List Instr := saveSlots ++ copyArgs ++ crtRegs

def saveResult (d : Nat) : List Instr := [.addSp .r12 0, .str .r0 .r12 d]
def copyIncoming (j d : Nat) : List Instr := [.ldrSp .r0 (arg j), .str .r0 .r12 d]
def preAddress (r : Reg) : List Instr := [.addSp r 0, .dp .add r r (.imm (BitVec.ofNat 32 oPre))]
def pcPrefix : List Instr := saveResult oR1 ++ copyIncoming 14 0 ++ copyIncoming 15 4 ++ preAddress .r0
def pcSuffix : List Instr := [.ldrSp .r2 oN, .ldrSp .r3 oK]
def pcArgs : List Instr := pcPrefix ++ preWords .r1 ++ pcSuffix

def copyRetained (i d : Nat) : List Instr := [.ldrSp .r0 (64 + 4 * i), .str .r0 .r12 d]
def storeTemporary : List Instr := [.addSp .r0 oM, .str .r0 .r12 8]
def pdPrefix : List Instr := saveResult oR3 ++ copyRetained 3 0 ++ copyRetained 4 4 ++
  storeTemporary ++ copyRetained 2 12 ++ copyIncoming 14 16 ++ copyIncoming 15 20
def pdSuffix : List Instr := [.ldrSp .r0 oOut, .ldrSp .r1 oK] ++ preAddress .r2 ++ preWords .r3
def pdArgs : List Instr := pdPrefix ++ pdSuffix

/-- Keep the three success bits in r4; compare output against the original input. -/
def cmpArgs : List Instr :=
  [.ldrSp .r4 oR1, .dp .and .r4 .r4 (.reg .r0), .ldrSp .r3 oR3,
   .dp .and .r4 .r4 (.reg .r3), .dp .and .r4 .r4 (.imm 1),
   .ldrSp .r0 oOut, .ldrSp .r1 oIn, .ldrSp .lr oK, .mov .r2 (.imm 0)]

/-- r3 = equality bit, r4 = return status, r2 = release mask. -/
def maskCore : List Instr :=
  [.mov .r3 (.imm 0), .dp .sub .r3 .r3 (.reg .r2), .dp .orr .r3 .r3 (.reg .r2),
   .mov .r3 (.shifted .r3 .lsr 31), .mov .r2 (.imm 1), .dp .sub .r3 .r2 (.reg .r3),
   .dp .and .r2 .r4 (.reg .r3), .mov .r12 (.imm 0), .dp .sub .r2 .r12 (.reg .r2),
   .dp .sub .r4 .r12 (.reg .r4), .mov .r12 (.imm 2), .dp .sub .r3 .r12 (.reg .r3),
   .dp .and .r4 .r4 (.reg .r3)]
def releaseArgs : List Instr := [.ldrSp .r0 oOut, .addSp .r1 oM, .ldrSp .lr oK, .mov .r12 (.imm 0)]
/-- Write only masked private bytes, clearing each temporary byte after use. -/
def releaseStep : List Instr :=
  [.ldrb .r3 .r1 0, .dp .and .r3 .r3 (.reg .r2), .strb .r3 .r0 0, .strb .r12 .r1 0,
   .dp .add .r0 .r0 (.imm 1), .dp .add .r1 .r1 (.imm 1), .subs .lr .lr (.imm 1)]
def release : Prog isa := .loop (.block releaseStep) .ne

def releaseTail : Prog isa := .seq (.block maskCore) (.seq (.block releaseArgs)
  (.seq release (.block [.mov .r0 (.reg .r4)])))
def tail : Prog isa := .seq (.block cmpArgs) (.seq Bignum.Arm.compareBytes releaseTail)
/-- Check a CRT result, given the stage that leaves the public precomputation
in the frame. -/
def checkWith (pcStage : Prog isa) (pdName : String) (pd : Prog isa) : Prog isa :=
  .seq (.block pcArgs) (.seq pcStage (.seq (.block pdArgs) (.seq (.call pdName pd) tail)))
def bodyWith (crtName : String) (crt : Prog isa) (chk : Prog isa) : Prog isa :=
  .seq (.block crtArgs) (.seq (.call crtName crt) chk)
def codeWith (body : Prog isa) : Prog isa :=
  .frame (.push [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr])
    (.seq (.frame (.alloc frameBytes) body (.free frameBytes))
      (.block Bignum.Arm.PcFn.restore)) (.pop .r12 56)

def check (pcName : String) (pc : Prog isa) (pdName : String) (pd : Prog isa) : Prog isa :=
  checkWith (.call pcName pc) pdName pd
def body (crtName : String) (crt : Prog isa) (pcName : String) (pc : Prog isa) (pdName : String) (pd : Prog isa) : Prog isa :=
  bodyWith crtName crt (check pcName pc pdName pd)
def code (crtName : String) (crt : Prog isa) (pcName : String) (pc : Prog isa) (pdName : String) (pd : Prog isa) : Prog isa :=
  codeWith (body crtName crt pcName pc pdName pd)

/-! ## `vg_rsa_private_checked_precomputed`

`vg_rsa_private_checked`'s arguments, then the key's precomputed values
`pre` and `pre_len` (incoming arguments 16 and 17). In place of
`vg_rsa_public_precompute`, its output, the first `2 w` words of `pre`, is
copied into the frame where that call wrote it, with its status 1; and in
place of `vg_rsa_private_crt`, `vg_rsa_private_crt_precomputed` is given
the rest of `pre`, the factors' `R²`. -/

/-- `pcArgs` leaves the frame's `pre` in r0 and `2 w` in r1: the `16 w` bytes
of the incoming `pre` into it, and the status 1. -/
def pcCopy : Prog isa :=
  .seq (.block [.mov .lr (.shifted .r1 .lsl 3), .ldrSp .r1 (arg 16)])
    (.seq Bignum.Arm.copyBytes (.block [.mov .r0 (.imm 1)]))
def checkP (pdName : String) (pd : Prog isa) : Prog isa := checkWith pcCopy pdName pd
/-- The outgoing arguments 14 and 15 of `vg_rsa_private_crt_precomputed`:
the factors' `R²`, `pre`'s words after its first `2 w`, and their number. -/
def r2Args : List Instr :=
  [.ldrSp .r0 (arg 17)] ++ preWords .r1 ++
    [.ldrSp .lr (arg 16), .dp .sub .r0 .r0 (.reg .r1), .dp .add .lr .lr (.shifted .r1 .lsl 3),
     .str .r0 .r12 60, .str .lr .r12 56]
def crtArgsP : List Instr := saveSlots ++ copyArgs ++ r2Args ++ crtRegs
/-- `bodyWith`, calling `vg_rsa_private_crt_precomputed` (`crtName`). -/
def bodyP (crtName : String) (crt : Prog isa) (pdName : String) (pd : Prog isa) : Prog isa :=
  .seq (.block crtArgsP) (.seq (.call crtName crt) (checkP pdName pd))
def codeP (crtName : String) (crt : Prog isa) (pdName : String) (pd : Prog isa) : Prog isa :=
  codeWith (bodyP crtName crt pdName pd)
end VG.Impl.Rsa.Arm.PrivChecked
