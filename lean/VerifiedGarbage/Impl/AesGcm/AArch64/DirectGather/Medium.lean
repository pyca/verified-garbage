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

def setup : List Instr :=
  [.addSp .x9 0] ++ save .x9 ++
  [mov .x19 .x9, mov .x21 .x0, mov .x22 .x1, mov .x23 .x2, mov .x24 .x5,
   .ldrSp .x26 (work+8), .addImm .x .x25 .x26 15, .lsr .x .x25 .x25 4, .lsl .x .x25 .x25 4]

/-- Zero both the CTR input and the right-aligned GHASH record, including the accumulator. -/
def zero : List Instr :=
  .vop (.movi0 .v0) :: (List.range 33).map fun i => .strq .v0 .x19 (keyO+16*i)

def aad : Prog isa :=
  .seq (.block (Stitch.atP .x11 (authO+128) 0 ++ [mov .x12 .x4, mov .x13 .x24])) copy

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

open Gcm.AArch64.Pmull in
def hash16With : List Instr :=
  (prologueW ++ Gcm.AArch64.Pmull.body 8 ++ Gcm.AArch64.Pmull.body 8) ++ [.vop (.rev .rev64b .v16 .v0)]

abbrev hashCore (cached : Bool) := if cached then hash16With else hash16

def tagOut := writeTag keyO (work+16)

def finishUsing (cached : Bool) : List Instr := lengths ++ (hashArgs ++ hashCore cached) ++ tagOut ++ restore

abbrev finish := finishUsing false

def bodyWith (c : Callees) (endCode : Prog isa) : Prog isa :=
  .seq (.block setup) <| .seq (.block zero) <| .seq aad <| .seq (keys c) <|
  .seq (.block cursors) <| .seq shortLoop endCode

abbrev body (c : Callees) := bodyWith c (.block finish)

/-- The outer contiguous adapter occupies 48 bytes. Its caller supplied the
powers pointer as the third stack argument. -/
def bodyCached (c : Callees) : Prog isa :=
  bodyWith c (.seq (.block [.ldrSp .x5 (work+48+16)]) (.block (finishUsing true)))

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
