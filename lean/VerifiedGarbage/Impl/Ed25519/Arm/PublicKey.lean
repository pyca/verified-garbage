module

public import VerifiedGarbage.Impl.Ed25519.Arm.Whole.Setup
public import VerifiedGarbage.Impl.Ed25519.Arm.Whole.Entry
public import VerifiedGarbage.Impl.Ed25519.Arm.Whole.Wipe
public import VerifiedGarbage.Impl.Ed25519.Arm.ScalarBase
public import VerifiedGarbage.Impl.Sha512.Arm.Stream
public import VerifiedGarbage.Spec.Sha512.Contract

@[expose] public section

namespace VG.Impl.Ed25519.Arm.PublicKey
open VG.Arm

def pruneLow : List Instr :=
  [.movw .r1 0xfff8, .movt .r1 0xffff, .dp .and .r0 .r0 (.reg .r1)]
def pruneHigh : List Instr :=
  [.movw .r1 0xffff, .movt .r1 0x3fff, .dp .and .r0 .r0 (.reg .r1),
    .movw .r1 0, .movt .r1 0x4000, .dp .orr .r0 .r0 (.reg .r1)]
def pruneWord (k : Nat) : List Instr :=
  [.ldrSp .r0 (184 + 4 * k)] ++ (if k = 0 then pruneLow else if k = 7 then pruneHigh else []) ++
    [.addSp .r12 24, .str .r0 .r12 (4 * k)]
def prune : List Instr := (List.range 8).flatMap pruneWord

open VG.Impl.Ed25519.Arm.Whole

def initArgs : List Instr := setup [(.r0, .caller 2 0)] []
def updateArgs : List Instr := setup [(.r0, .caller 2 0), (.r2, .const 0), (.r3, .const 0)]
  [.caller 1 0, .const 32, .caller 2 192]
def finalizeArgs : List Instr := setup [(.r0, .caller 2 0), (.r2, .const 32), (.r3, .const 0)]
  [.frame 184, .caller 2 192]
def baseArgs : List Instr := setup [(.r0, .caller 0 0), (.r1, .frame 24), (.r2, .caller 2 0)] []
def hash : Prog isa :=
  .seq (callWith initArgs Spec.Sha512.init512Api.name (Sha512.Arm.Stream.init Spec.Sha512.H0_512))
    (.seq (callWith updateArgs "vg_sha512_update_scratch" Sha512.Arm.Stream.update)
      (callWith finalizeArgs "vg_sha512_finalize_scratch" Sha512.Arm.Stream.finalize))
def wipe : List Instr := zeroWords 6 56
/-- The body after `digest`, which leaves the seed's SHA-512 digest at `frame 184`. -/
def bodyFrom (digest : Prog isa) : Prog isa := .seq digest (.seq (.block prune)
  (.seq (callWith baseArgs "vg_ed25519_scalar_base" scalarBase) (.block wipe)))
def body : Prog isa := bodyFrom hash
def code : Prog isa := wrap 3 body

/-- The pointers of the copy: the cached digest (the second argument) in `r1`, `frame 184`
in `r2`. -/
def copyArgs : List (Reg × Value) := [(.r1, .caller 1 0), (.r2, .frame 184)]

/-- The sixteen words at `r1` copied to `r2`. Word loads need no alignment (`TCB/Arm/Isa.lean`),
so the digest may be at any address. -/
def copyWords : List Instr :=
  (List.range 16).flatMap fun k => [.ldr .r0 .r1 (4 * k), .str .r0 .r2 (4 * k)]

/-- The seed's cached SHA-512 digest (the second argument) copied to `frame 184`, where
`hash` (and signing's `hashSeed`) leave the digest they compute. -/
def copyExpanded : Prog isa := .seq (.block (setup copyArgs [])) (.block copyWords)

/-- `vg_ed25519_public_key_expanded`: `code` from the seed's cached SHA-512 digest
(`publicKeyExpandedContract`), copied rather than computed. -/
def codeExpanded : Prog isa := wrap 3 (bodyFrom copyExpanded)

end VG.Impl.Ed25519.Arm.PublicKey
