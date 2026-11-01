module

import VerifiedGarbage.TCB.PPC64LE.Print
meta import VerifiedGarbage.TCB.PPC64LE.Print

/-!
# Golden tests for the PPC64LE instruction semantics

The ISA model is part of the TCB; these tests run each instruction on a
concrete state, so that the values they compute (in particular the word
forms, the byte-reversed accesses and the sign extension of `lis`) and when
they fault show up in review. The expected values were checked against the
same instructions run under QEMU's ppc64le emulation (`qemu-ppc64le`).
-/

namespace VG.Test.PPC64LE

open VG.PPC64LE

/-- `r3` points to 16 readable and writable bytes `0x00, 0x01, …, 0x0f` at
`0x1000`; `r4 = 0x8000_0001_f000_0001`, `r5 = 4`, `r6 = 0xffff_ffff_0123_4567`. -/
def s0 : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x80000001f0000001 | .r5 => 4 | .r6 => 0xffffffff01234567 | _ => 0
  lr := 0x4000
  sp := 0x2000
  mem a := a.setWidth 8
  rd := []
  wr := [⟨0x1000, 16⟩]

/-- `r7` after running `i` (the destination of every test). -/
def reg (i : Instr) : Option (BitVec 64) := (exec i s0).map (·.gpr .r7)

-- 64-bit arithmetic and logic.
#guard reg (.add .r7 .r4 .r6) == some 0x80000000f1234568
#guard reg (.sub .r7 .r5 .r4) == some 0x7ffffffe10000003
#guard reg (.addi .r7 .r6 0x7fff) == some 0xffffffff0123c566
#guard reg (.subi .r7 .r5 5) == some 0xffffffffffffffff
#guard reg (.subi .r7 .r5 32768) == some 0xffffffffffff8004
#guard reg (.li .r7 32767) == some 0x7fff
#guard reg (.lis .r7 0x7fff) == some 0x7fff0000
#guard reg (.lis .r7 0x8000) == some 0xffffffff80000000
#guard reg (.ori .r7 .r5 0xff00) == some 0xff04
#guard reg (.oris .r7 .r5 0xff00) == some 0xff000004
#guard reg (.logic .and .r7 .r4 .r6) == some 0x8000000100000001
#guard reg (.logic .or .r7 .r4 .r5) == some 0x80000001f0000005
#guard reg (.logic .xor .r7 .r4 .r6) == some 0x7ffffffef1234566
-- Multiplies: the low 64 bits of the product, and the high 64 bits of the
-- unsigned product (`r4` and `r6` have their top bits set, so a signed
-- `mulhd` would differ).
#guard reg (.mul .r7 .r4 .r6) == some 0x9234567691234567
#guard reg (.mulhu .r7 .r4 .r6) == some 0x800000017091a2b2
#guard reg (.mulhu .r7 .r6 .r5) == some 0x3
#guard reg (.mul .r7 .r6 .r5) == some 0xfffffffc048d159c
-- The carrying adds and subtracts: `r7` and CA after running `i` with CA set
-- to `c` before. `addc` and `subc` ignore CA; the extended forms add it;
-- `subc` and `sube` set CA iff there is no borrow.
def carry (i : Instr) (c : Bool) : Option (BitVec 64 × Bool) :=
  (exec i { s0 with ca := c }).map fun s => (s.gpr .r7, s.ca)
#guard [false, true].all fun c => carry (.addc .r7 .r4 .r6) c == some (0x80000000f1234568, true)
#guard [false, true].all fun c => carry (.addc .r7 .r5 .r6) c == some (0xffffffff0123456b, false)
#guard carry (.adde .r7 .r4 .r6) false == some (0x80000000f1234568, true)
#guard carry (.adde .r7 .r4 .r6) true == some (0x80000000f1234569, true)
#guard carry (.adde .r7 .r5 .r6) false == some (0xffffffff0123456b, false)
#guard carry (.adde .r7 .r5 .r6) true == some (0xffffffff0123456c, false)
#guard carry (.addze .r7 .r6) false == some (0xffffffff01234567, false)
#guard carry (.addze .r7 .r6) true == some (0xffffffff01234568, false)
#guard [false, true].all fun c => carry (.subc .r7 .r5 .r4) c == some (0x7ffffffe10000003, false)
#guard [false, true].all fun c => carry (.subc .r7 .r4 .r5) c == some (0x80000001effffffd, true)
#guard [false, true].all fun c => carry (.subc .r7 .r5 .r5) c == some (0, true)
#guard carry (.sube .r7 .r5 .r4) false == some (0x7ffffffe10000002, false)
#guard carry (.sube .r7 .r5 .r4) true == some (0x7ffffffe10000003, false)
#guard carry (.sube .r7 .r4 .r5) false == some (0x80000001effffffc, true)
#guard carry (.sube .r7 .r4 .r5) true == some (0x80000001effffffd, true)
#guard carry (.sube .r7 .r5 .r5) false == some (0xffffffffffffffff, false)
#guard carry (.sube .r7 .r5 .r5) true == some (0, true)
-- Nothing else sets CA, and nothing else reads it.
#guard carry (.add .r7 .r4 .r6) false == some (0x80000000f1234568, false)
#guard carry (.add .r7 .r4 .r6) true == some (0x80000000f1234568, true)

-- Word rotates and shifts read the low word and zero-extend the result.
#guard reg (.rotr .w .r7 .r4 4) == some 0x1f000000
#guard reg (.rotr .w .r7 .r6 0) == some 0x01234567
#guard reg (.lsr .w .r7 .r4 28) == some 0xf
#guard reg (.lsr .w .r7 .r6 0) == some 0x01234567
-- Doubleword rotates and shifts.
#guard reg (.rotr .d .r7 .r4 4) == some 0x180000001f000000
#guard reg (.lsr .d .r7 .r4 60) == some 0x8
#guard reg (.lsl .r7 .r6 32) == some 0x0123456700000000
#guard (reg (.rotr .w .r7 .r4 32)).isNone && (reg (.lsr .d .r7 .r4 64)).isNone &&
  (reg (.lsl .r7 .r4 64)).isNone

-- Loads are little-endian and zero-extended; the byte-reversed ones are big-endian.
#guard reg (.load .w .r7 .r3 4) == some 0x07060504
#guard reg (.load .d .r7 .r3 8) == some 0x0f0e0d0c0b0a0908
#guard reg (.lbz .r7 .r3 15) == some 0x0f
#guard reg (.loadRev .w .r7 .r3 .r5) == some 0x04050607
#guard reg (.loadRev .d .r7 .r3 .r5) == some 0x0405060708090a0b
#guard reg (.loadRev .d .r7 .r3 .r0) == some 0x0001020304050607
-- Out of the permitted regions, or with an unencodable displacement or `r0` as the base.
#guard (reg (.load .d .r7 .r3 9)).isNone
#guard (reg (.load .d .r7 .r3 6)).isNone
#guard (reg (.load .w .r7 .r3 32768)).isNone
#guard (reg (.load .w .r7 .r0 0)).isNone
#guard (reg (.loadRev .w .r7 .r0 .r3)).isNone
#guard (reg (.addi .r7 .r0 1)).isNone

def mem (i : Instr) (a : Addr) (n : Nat) : Option (BitVec (8 * n)) :=
  (exec i s0).map (·.mem.read a n)

-- Stores: the low bytes, little-endian; the byte-reversed ones big-endian.
#guard mem (.store .w .r6 .r3 0) 0x1000 8 == some 0x0706050401234567
#guard mem (.store .d .r4 .r3 8) 0x1008 8 == some 0x80000001f0000001
#guard mem (.stb .r6 .r3 3) 0x1000 4 == some 0x67020100
#guard mem (.storeRev .w .r6 .r3 .r5) 0x1004 4 == some 0x67452301
#guard mem (.storeRev .d .r4 .r3 .r5) 0x1004 8 == some 0x010000f001000080
#guard (mem (.store .w .r6 .r3 13) 0x1000 1).isNone

-- The link register.
#guard reg (.mflr .r7) == some 0x4000
#guard ((exec (.mtlr .r6) s0).map (·.lr)) == some 0xffffffff01234567

-- Conditions compare the word or the doubleword with zero.
#guard eval (.zero .w .r4) s0 == some false && eval (.zero .w .r7) s0 == some true
#guard eval (.zero .w .r4) { s0 with gpr := fun _ => 0x100000000 } == some true
#guard eval (.nonzero .d .r4) { s0 with gpr := fun _ => 0x100000000 } == some true
#guard eval (.nonzero .d .r4) { s0 with gpr := fun _ => 0 } == some false

-- A call leaves the next unknown values in `LR`, `r0`, `r11` and `r12`; the
-- return only goes back to that address.
def sCall : State := { s0 with unknowns := fun n => BitVec.ofNat 64 (n + 100) }
#guard (call sCall).map (fun s => (s.lr, s.gpr .r0, s.gpr .r11, s.gpr .r12, s.gpr .r3,
    s.unknowns 0)) == some (100, 101, 102, 103, 0x1000, 104)
#guard ((call sCall).bind fun s₁ => (ret s₁ s₁).map (·.lr)) == some 100
#guard ((call sCall).bind fun s₁ => ret s₁ { s₁ with lr := 0 }).isNone


/-! POWER8 vector cryptography. Expected results below were obtained from
QEMU 10.0.11, `qemu-ppc64le -cpu power8`, executing the Lean printer's
assembly assembled by GCC 14.2.0 with `-mcpu=power8`. Values are architectural
register order (most significant element first), not host memory order.
The cases cover all valid SHA selectors, every byte shift, and AES inverse
round key placement; these are instruction tests, not algorithm vectors. -/
def cryptoCases : List Instr :=
  ([false, true].flatMap fun inv => [false, true].map fun last =>
    .vop (.cipher inv last .v3 .v0 .v1)) ++
  [.vop (.sbox .v3 .v0)] ++
  ([false, true].flatMap fun st => (List.range 16).map fun six =>
    .vop (.sha256 .v3 .v0 st six)) ++
  ([false, true].flatMap fun st => [0, 2, 8, 10].map fun six =>
    .vop (.sha512 .v3 .v0 st six)) ++
  [.vop (.pmsumd .v3 .v0 .v1), .vop (.logic .and .v3 .v0 .v1),
   .vop (.logic .or .v3 .v0 .v1), .vop (.logic .xor .v3 .v0 .v1),
   .vop (.add false .v3 .v0 .v1), .vop (.add true .v3 .v0 .v1),
   .vop (.perm .v3 .v0 .v1 .v2)] ++
  ((List.range 16).map fun sh => .vop (.sldoi .v3 .v0 .v1 sh))

def cryptoInputs : List (BitVec 128) :=
  [0x00112233445566778899aabbccddeeff, 0x0f1e2d3c4b5a69788796a5b4c3d2e1f0,
   0x801f2091405f60917f0081a2c3e4f506]

def sVec : State := { s0 with
  vpr := fun r => if r = .v0 then cryptoInputs[0]! else if r = .v1 then cryptoInputs[1]!
    else if r = .v2 then cryptoInputs[2]! else 0 }

def cryptoExpected : List (BitVec 128) := [
  0x6c67cbe5bf3d920e2a90994011396b53, 0x6ce2812a50b441bb435736418850d21a,
  0x78178713c3c5fafe257639f90ac50aae, 0x5dd74f3ecdb9f086107b31c9e42b3296,
  0x638293c31bfc33f5c4eeacea4bc12816, 0x2e8ec606bf9fd7170cace4249dbdf535,
  0x2e8ec606bf9fd7170cace4244a93288e, 0x2e8ec606bf9fd717e02893359dbdf535,
  0x2e8ec606bf9fd717e02893354a93288e, 0x2e8ec6061fe45ff90cace4249dbdf535,
  0x2e8ec6061fe45ff90cace4244a93288e, 0x2e8ec6061fe45ff9e02893359dbdf535,
  0x2e8ec6061fe45ff9e02893354a93288e, 0xb55fe442bf9fd7170cace4249dbdf535,
  0xb55fe442bf9fd7170cace4244a93288e, 0xb55fe442bf9fd717e02893359dbdf535,
  0xb55fe442bf9fd717e02893354a93288e, 0xb55fe4421fe45ff90cace4249dbdf535,
  0xb55fe4421fe45ff90cace4244a93288e, 0xb55fe4421fe45ff9e02893359dbdf535,
  0xb55fe4421fe45ff9e02893354a93288e, 0x95148405b736a627d150c041f372e263,
  0x95148405b736a627d150c0414e3d93e0, 0x95148405b736a627f586285bf372e263,
  0x95148405b736a627f586285b4e3d93e0, 0x95148405394ae497d150c041f372e263,
  0x95148405394ae497d150c0414e3d93e0, 0x95148405394ae497f586285bf372e263,
  0x95148405394ae497f586285b4e3d93e0, 0x82f15f2cb736a627d150c041f372e263,
  0x82f15f2cb736a627d150c0414e3d93e0, 0x82f15f2cb736a627f586285bf372e263,
  0x82f15f2cb736a627f586285b4e3d93e0, 0x82f15f2c394ae497d150c041f372e263,
  0x82f15f2c394ae497d150c0414e3d93e0, 0x82f15f2c394ae497f586285bf372e263,
  0x82f15f2c394ae497f586285b4e3d93e0, 0xf708a27ff7e64c913ad57fa22a3b914c,
  0xf708a27ff7e64c91fb30c267bc8b79dc, 0xac47b510cbfc0eab3ad57fa22a3b914c,
  0xac47b510cbfc0eabfb30c267bc8b79dc, 0xf2cb94212f1649fc49702f9a94adf247,
  0xf2cb94212f1649fc9da7aeb7bf858c95, 0xd9e3eaf3fbc1c8d149702f9a94adf247,
  0xd9e3eaf3fbc1c8d19da7aeb7bf858c95, 0x47b847b847b847b847b847b847b847b8,
  0x00102030405060708090a0b0c0d0e0f0, 0x0f1f2f3f4f5f6f7f8f9fafbfcfdfefff,
  0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 0x0f2f4f6f8fafcfef1030506f90b0d0ef,
  0x0f2f4f6f8fafcfef1030507090b0d0ef, 0x00f0001e00f0001ef000112233445a66,
  0x00112233445566778899aabbccddeeff, 0x112233445566778899aabbccddeeff0f,
  0x2233445566778899aabbccddeeff0f1e, 0x33445566778899aabbccddeeff0f1e2d,
  0x445566778899aabbccddeeff0f1e2d3c, 0x5566778899aabbccddeeff0f1e2d3c4b,
  0x66778899aabbccddeeff0f1e2d3c4b5a, 0x778899aabbccddeeff0f1e2d3c4b5a69,
  0x8899aabbccddeeff0f1e2d3c4b5a6978, 0x99aabbccddeeff0f1e2d3c4b5a697887,
  0xaabbccddeeff0f1e2d3c4b5a69788796, 0xbbccddeeff0f1e2d3c4b5a69788796a5,
  0xccddeeff0f1e2d3c4b5a69788796a5b4, 0xddeeff0f1e2d3c4b5a69788796a5b4c3,
  0xeeff0f1e2d3c4b5a69788796a5b4c3d2, 0xff0f1e2d3c4b5a69788796a5b4c3d2e1]

#guard cryptoCases.map (fun i => (exec i sVec).map (·.vpr .v3)) == cryptoExpected.map some

-- Unencodable immediates and reserved SIX bits must fault.
#guard (exec (.vop (.sha256 .v3 .v0 false 16)) sVec).isNone
#guard [1, 4, 5, 15, 16].all fun six =>
  (exec (.vop (.sha512 .v3 .v0 true six)) sVec).isNone
#guard (exec (.vop (.sldoi .v3 .v0 .v1 16)) sVec).isNone

-- The high doubleword of MT VSR is defined, the low one is arbitrary.
-- Check with a nonzero unknown, so a spurious zero-fill cannot pass.
def sVU : State := { sVec with unknowns := fun i => BitVec.ofNat 64 (i + 123) }
#guard (exec (.mtvsrd .v3 .r4) sVU).map (·.vpr .v3) ==
  some 0x80000001f0000001000000000000007b
#guard (exec (.mtvsrd .v3 .r4) sVU).map (fun s => s.unknowns 0) == some 124
#guard (exec (.mfvsrd .r7 .v0) sVec).map (·.gpr .r7) == some 0x0011223344556677

-- LXVD2X loads the first memory doubleword into the HIGH register half.
#guard (exec (.lxvd2x .v3 .r3 .r0) sVec).map (·.vpr .v3) ==
  some 0x07060504030201000f0e0d0c0b0a0908
#guard (exec (.lxvd2x .v3 .r3 .r5) sVec).isNone -- crosses the permitted region
#guard (exec (.lxvd2x .v3 .r0 .r3) sVec).isNone -- forbidden RA=0 encoding
#guard (exec (.stxvd2x .v0 .r3 .r0) sVec).map (fun s => s.mem.read 0x1000 16) ==
  some 0x8899aabbccddeeff0011223344556677
#guard (exec (.stxvd2x .v0 .r3 .r5) sVec).isNone
#guard (exec (.stxvd2x .v0 .r0 .r3) sVec).isNone
-- Accesses need not be aligned; no LVX-style address rounding.
def sUnaligned : State := { sVec with wr := [⟨0x1000, 20⟩] }
#guard (exec (.lxvd2x .v3 .r3 .r5) sUnaligned).map (·.vpr .v3) ==
  some 0x0b0a090807060504131211100f0e0d0c
#guard addrs (.lxvd2x .v0 .r3 .r5) sVec == [0x1004]
#guard addrs (.stxvd2x .v0 .r3 .r5) sVec == [0x1004]

-- Modular addition carries between bits within a lane, never between lanes.
def sOnes : State := { sVec with vpr := fun r => if r = .v0 then -1 else 1 }
#guard (exec (.vop (.add false .v3 .v0 .v1)) sOnes).map (·.vpr .v3) ==
  some 0xffffffffffffffffffffffff00000000
#guard (exec (.vop (.add true .v3 .v0 .v1)) sOnes).map (·.vpr .v3) ==
  some 0xffffffffffffffff0000000000000000
-- Both 64x64 polynomial products contribute; the highest possible bit is 126.
def sPoly : State := { sVec with vpr := fun r =>
  if r = .v0 then 0x80000000000000000000000000000001
  else 0x80000000000000000000000000000003 }
#guard (exec (.vop (.pmsumd .v3 .v0 .v1)) sPoly).map (·.vpr .v3) ==
  some 0x40000000000000000000000000000003

-- VMX uses VR numbers; VSX uses the aliased VSR numbers (+32).
#guard Instr.asm (.lxvd2x .v19 .r3 .r4) == ["lxvd2x 51, %r3, %r4"]
#guard Instr.asm (.stxvd2x .v0 .r3 .r4) == ["stxvd2x 32, %r3, %r4"]
#guard Instr.asm (.mtvsrd .v0 .r3) == ["mtvsrd 32, %r3"]
#guard Instr.asm (.mfvsrd .r3 .v19) == ["mfvsrd %r3, 51"]
#guard Instr.asm (.vop (.cipher true true .v19 .v0 .v1)) ==
  ["vncipherlast %v19, %v0, %v1"]
#guard Instr.asm (.vop (.sha512 .v19 .v0 true 10)) ==
  ["vshasigmad %v19, %v0, 1, 10"]

#guard ([false, true].flatMap fun inv => [false, true].map fun last =>
  VOp.asm (.cipher inv last .v3 .v0 .v1)) == [
  "vcipher %v3, %v0, %v1", "vcipherlast %v3, %v0, %v1",
  "vncipher %v3, %v0, %v1", "vncipherlast %v3, %v0, %v1"]
#guard ([VOp.sbox .v3 .v0, .sha256 .v3 .v0 false 9, .pmsumd .v3 .v0 .v1,
  .logic .and .v3 .v0 .v1, .logic .or .v3 .v0 .v1, .logic .xor .v3 .v0 .v1,
  .add false .v3 .v0 .v1, .add true .v3 .v0 .v1, .perm .v3 .v0 .v1 .v2,
  .sldoi .v3 .v0 .v1 15].map VOp.asm) == [
  "vsbox %v3, %v0", "vshasigmaw %v3, %v0, 0, 9", "vpmsumd %v3, %v0, %v1",
  "vand %v3, %v0, %v1", "vor %v3, %v0, %v1", "vxor %v3, %v0, %v1",
  "vadduwm %v3, %v0, %v1", "vaddudm %v3, %v0, %v1", "vperm %v3, %v0, %v1, %v2",
  "vsldoi %v3, %v0, %v1, 15"]

-- Literal-table loads read the emitter's immutable words, independently
-- of the caller's permitted memory. Indexed addressing must still agree
-- with the static and table bounds, including a nonzero RB=r0 value.
def tableWords : List (BitVec 64) := [0x0123456789abcdef, 0xfedcba9876543210, 42]
def sTable : State := { sVec with
  gpr := fun r => if r = .r3 then 0x1000 else if r = .r4 then 8 else 0
  syms := fun _ => 0x1000
  rd := [], wr := [], mem := fun _ => 0 }
def tableLoad (a b : Reg) (ws := tableWords) : Instr :=
  .lxvd2xTbl .v19 a b "VG_TEST_PPC_TABLE" ws
#guard (exec (tableLoad .r3 .r0) sTable).map (·.vpr .v19) ==
  some 0x0123456789abcdeffedcba9876543210
#guard (exec (tableLoad .r3 .r4) sTable).map (·.vpr .v19) ==
  some 0xfedcba9876543210000000000000002a
#guard (exec (tableLoad .r0 .r3) sTable).isNone -- RA=0 encoding
#guard (exec (tableLoad .r3 .r4) { sTable with
  gpr := fun r => if r = .r3 then 0x1000 else 7 }).isNone -- unaligned index
#guard (exec (tableLoad .r3 .r4) { sTable with
  gpr := fun r => if r = .r3 then 0x1000 else 16 }).isNone -- only one word left
#guard (exec (tableLoad .r3 .r4 [1, 2]) sTable).isNone -- extends past table
#guard (exec (tableLoad .r3 .r0 []) sTable).isNone
#guard (exec (tableLoad .r3 .r0 [1]) sTable).isNone
#guard (exec (tableLoad .r3 .r0) { sTable with syms := fun _ => 0x2000 }).isNone
#guard (exec (tableLoad .r3 .r0) { sTable with
  gpr := fun r => if r = .r3 then 0x1000 else if r = .r0 then 8 else 0 }).map
  (·.vpr .v19) == some 0xfedcba9876543210000000000000002a
#guard (exec (tableLoad .r3 .r4) sTable).map
  (fun s => (s.gpr .r3, s.lr, s.ca, s.sp, s.unknowns 0, s.vpr .v0)) ==
  some (sTable.gpr .r3, sTable.lr, sTable.ca, sTable.sp, sTable.unknowns 0, sTable.vpr .v0)
#guard addrs (tableLoad .r3 .r4) sTable == [8]
#guard Instr.asm (tableLoad .r3 .r4) == ["lxvd2x 51, %r3, %r4"]
#guard printer.tables (tableLoad .r3 .r4) == [("VG_TEST_PPC_TABLE", tableWords)]
#guard printer.tables (.lxvd2x .v19 .r3 .r4) == []

end VG.Test.PPC64LE
