module

public import VerifiedGarbage.Impl.AesGcm.AArch64.DirectGather

/-! Seal bounded records with one AES counter for the tag mask and one per
plaintext block. Two eight-block GHASH groups authenticate the padded record. -/

@[expose] public section
namespace VG.Impl.AesGcm.AArch64.DirectGather.Medium
open VG.AArch64

def work := 752
def keyO := 224
def authO := 480

abbrev setup := shortSetupAt (work+8)

/-- Zero both the CTR input and the right-aligned GHASH record, including the accumulator. -/
def zero : List Instr :=
  .vop (.movi0 .v0) :: (List.range 33).map fun i => .strq .v0 .x19 (keyO+16*i)

/-- With a known nonempty AAD the copy can start immediately at the word-count test. -/
def aadWith (early : Bool) : Prog isa :=
  let args := .block (Stitch.atP .x11 (authO+128) 0 ++ [mov .x12 .x4, mov .x13 .x24])
  if early then
    .ite (.zero .x .x24) (.block [])
      (.seq args (.seq (.block [.lsr .x .x14 .x13 2]) (.ite (.zero .x .x14) copyLoop copyW)))
  else .seq args copy

abbrev aad := aadWith false

def seed : List Instr :=
  [.ldr .x .x9 .x23 0, .ldr .w .x10 .x23 8, .vop (.ins .d2 .v31 0 .x9),
   .vop (.ins .s4 .v31 2 .x10), .movz .w .x12 256 1, .vop (.ins .s4 .v31 3 .x12),
   .strq .v31 .x19 0, mov .x0 .x21, mov .x1 .x22, mov .x2 .x19,
   ptr .x3 .x19 keyO, .lsr .x .x4 .x25 4, .addImm .x .x4 .x4 1, ptr .x5 .x19 (work-16), mov .x27 .x6, mov .x28 .x7]

def keys (c : Callees) : Prog isa := .seq (.block seed) (ctrCall c)

def cursors : List Instr :=
  [mov .x6 .x27, mov .x7 .x28, ptr .x1 .x19 (keyO+16), .ldrSp .x2 work] ++ Stitch.atP .x3 (authO+128) 1

def lengths := Stitch.lengthsAt (authO + 240)

def hashArgs : List Instr :=
  [ptr .x0 .x21 240, ptr .x1 .x19 (authO+256), ptr .x2 .x19 authO, imm .x3 16]

open Gcm.AArch64.Pmull in
def hash16 : List Instr :=
  (prologueT ++ powersS ++ Gcm.AArch64.Pmull.body 8 ++ Gcm.AArch64.Pmull.body 8) ++ [.vop (.rev .rev64b .v16 .v0)]

def tagOut (tagOff : Nat := work+16) := writeTag keyO tagOff

def finish (tagOff : Nat := work+16) : List Instr := lengths ++ (hashArgs ++ hash16) ++ tagOut tagOff ++ restore

def bodyWith (c : Callees) (endCode : Prog isa) : Prog isa :=
  .seq (.block setup) <| .seq (.block zero) <| .seq aad <| .seq (keys c) <|
  .seq (.block cursors) <| .seq shortLoop endCode

abbrev body (c : Callees) := bodyWith c (.block finish)

/-- All records use the same right-aligned sixteen-slot transcript. A record
of at most 128 bytes has six leading zero blocks. Up to 160 bytes it has four.
The public length chooses how much of the first eight-block group to hash. -/
def firstHashGroup (k : Nat) : Prog isa :=
  .block ((if k = 8 then [] else Gcm.AArch64.Pmull.advance (8-k)) ++ Gcm.AArch64.Pmull.body k)

def chooseGroup (n : Nat) (yes no : Prog isa) : Prog isa :=
  .seq (.block [.subImm .x .x11 .x26 n,.lsr .x .x11 .x11 63])
    (.ite (.nonzero .x .x11) yes no)

open Gcm.AArch64.Pmull in
def hashTrimmed : Prog isa :=
  .seq (.block prologueW) <|
  .seq (chooseGroup 129
    (.ite (.zero .x .x24) (chooseGroup 113 (.block (advance 8)) (firstHashGroup 1)) (firstHashGroup 2))
    (chooseGroup 161 (.ite (.zero .x .x24) (firstHashGroup 3) (firstHashGroup 4))
      (.ite (.zero .x .x24) (chooseGroup 193 (firstHashGroup 5) (firstHashGroup 7)) (firstHashGroup 8))))
    (.block (Gcm.AArch64.Pmull.body 8 ++ [.vop (.rev .rev64b .v16 .v0)]))

/-- Everything up to loading the tag pointer, before the final store. -/
def tagPrefix (tagOff : Nat := work+16) : List Instr :=
  [.ldrq .v0 .x19 keyO,.vop (.logic .eor .v16 .v16 .v0),.ldrSp .x10 tagOff]

def finishPrefix (tagOff : Nat := work+16) : Prog isa :=
  .seq (.seq (.block lengths) (.seq (.block hashArgs) hashTrimmed)) (.block (tagPrefix tagOff))

def finishCached (tagOff : Nat := work+16) : Prog isa := .seq (finishPrefix tagOff) (.block ([.strq .v16 .x10 0] ++ restore))

def leaf (c : Callees) : Prog isa :=
  Impl.Scrub.AArch64.scrubAll work 0 Fn.own (.frame (.alloc work) (body c) (.free work))

end VG.Impl.AesGcm.AArch64.DirectGather.Medium


namespace VG.Impl.AesGcm.AArch64.DirectGather

/-- The hardware AES backend uses bounded leaves for standard nonces and a
single AAD block. Other records use the descriptor loop for general lengths. -/
def sealGather (v : Calls) : Prog AArch64.isa :=
  if v.stitch && v.ctr.scratch == 0 then
    chooseShort (chooseRecord 224 (Medium.leaf v.callees) (longSeal v))
  else longSeal v

end VG.Impl.AesGcm.AArch64.DirectGather
