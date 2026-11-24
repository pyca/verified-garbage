module

public import VerifiedGarbage.Impl.AesGcm.AArch64.DirectGather.Medium

/-! Pass a contiguous input and output to the bounded gather kernel. The
descriptor and the first two outgoing stack arguments have the same layout. -/

@[expose] public section
namespace VG.Impl.AesGcm.AArch64.DirectGather.Contiguous

open VG.AArch64

/-- After allocating 32 bytes, the original tag address is above the frame.
The first two words hold the single descriptor `(data, len)`, also the
destination and length arguments. The other words hold the tag and link. -/
def setup : List Instr :=
  [.ldrSp .x9 32, .strSp .x6 0, .strSp .x7 8, .strSp .x9 16,
    .strSp .x30 24, .addSp .x6 0, .movz .x .x7 1 0]

/-- The gather ABI already provides its descriptor vector and count. Forward
the three stack arguments and keep the return address in the fourth slot. -/
def gatherSetup : List Instr :=
  [.ldrSp .x9 32, .ldrSp .x10 40, .ldrSp .x11 48, .strSp .x9 0,
    .strSp .x10 8, .strSp .x11 16, .strSp .x30 24]

/-- The frame holds the common ABI, including its single-descriptor form.
The callee and adapter have one combined register and stack cleanup. -/
def callFrame (args : List Instr) (name : String) (bytes : Nat) (body : Prog isa) : Prog isa :=
  .frame (.alloc 32)
      (.seq (.block args) (.seq (.call name (.frame (.alloc bytes) body (.free bytes)))
        (.block [.ldrSp .x30 24]))) (.free 32)

def boundedCall (args : List Instr) (name : String) (bytes : Nat) (body : Prog isa) : Prog isa :=
  Impl.Scrub.AArch64.scrubAll (bytes+32) 0 Fn.own (callFrame args name bytes body)

def shortName := "vg_aes_gcm_seal_short_aes_sha3"

def boundedSeal (args : List Instr) : Prog isa := boundedCall args shortName shortWork shortBody

/-- The in-place ABI carries its length in x7. A zero result in x10 selects
the bounded body for the standard nonce and at most one AAD block. -/
def guard : List Instr :=
  [.subImm .x .x10 .x3 12, imm .x9 17, .subs .x .x11 .x5 .x9, .csel .x .x10 .x9 .x10,
    imm .x9 97, .subs .x .x11 .x7 .x9, .csel .x .x10 .x9 .x10]

def selectSeal (other : Prog isa) : Prog isa := .seq (.block guard) (.ite (.zero .x .x10) (boundedSeal setup) other)

def sealWithPowers (c : Calls) (w : AesGcm.AArch64.Fn) : Prog isa :=
  if c.stitch && c.ctr.scratch == 0 then selectSeal (Fn.sealWithPowers c w)
  else Fn.sealWithPowers c w

end VG.Impl.AesGcm.AArch64.DirectGather.Contiguous

namespace VG.Impl.AesGcm.AArch64.DirectGather

/-- The hardware AES backend uses bounded leaves for standard nonces and a
single AAD block. Other records use the descriptor loop for general lengths. -/
def sealGather (v : Calls) : Prog AArch64.isa :=
  if v.stitch && v.ctr.scratch == 0 then
    chooseRecord 96 (Contiguous.boundedSeal Contiguous.gatherSetup) (chooseRecord 224 (Medium.leaf v.callees) (longSeal v))
  else longSeal v

end VG.Impl.AesGcm.AArch64.DirectGather
