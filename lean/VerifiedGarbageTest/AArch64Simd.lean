module

public import VerifiedGarbage.TCB.AArch64.Print
public meta import VerifiedGarbage.TCB.AArch64.Print

/-!
# Semantics tests for the AArch64 AdvSIMD and cryptographic instructions

Each expected value was computed by the same instruction, in inline assembly
exactly as the printer prints it (checked below), in a program
cross-compiled with `aarch64-linux-gnu-gcc -march=armv8.4-a+crypto+sha3`
and run under `qemu-aarch64 -cpu max`'s emulation of an AArch64 CPU with
every feature, not on Arm hardware. Before each instruction the program
loaded `v0`–`v3`, `x1` and `x0` from the inputs below (the pseudorandom
values of a fixed seed; `v3`'s bytes are below 32, so that `tbl` sees
indices both inside and outside its table) and `0xdeadbeefdeadbeef`, and
afterwards stored `v0` (or `x0`, for `umov`). The instructions include forms
whose destination is also a source. This tests the transcription of the Arm
ARM's pseudocode (which lane is which, the operand roles of the SHA
instructions, the zeroing by a scalar write), which review of the TCB would
otherwise have to catch by eye.
-/

@[expose] public section

namespace VG.Test.AArch64Simd

open AArch64

/-- The inputs: `v0`, `v1`, `v2`, `v3`, `x1` for each of the two runs. -/
def input0 : BitVec 128 × BitVec 128 × BitVec 128 × BitVec 128 × BitVec 64 :=
  (0x47be5543e684460b8caafc59aff91663#128, 0xd5b39162c1984cc4c9c6de1db050fcb1#128,
    0x183bb3b2f27fe16536ca734e082da43c#128, 0x1e0f01110c03061910011d02150c161c#128, 0x9696613da12809ec#64)
def input1 : BitVec 128 × BitVec 128 × BitVec 128 × BitVec 128 × BitVec 64 :=
  (0x55eadb18f6d1d81649d2bf3ef06dbe6f#128, 0xdb26ce183543c96b9f9eb90b2c4563c4#128,
    0x384a612f2df0168eeee920eaf4a28fec#128, 0x1b1b1e000f0e031600001b10160a0f06#128, 0xd55f2bbb042e967b#64)

/-- The inputs of run `k`. -/
def input (k : Nat) : BitVec 128 × BitVec 128 × BitVec 128 × BitVec 128 × BitVec 64 :=
  if k = 0 then input0 else input1

/-- The state before run `k`: its inputs in `v0`–`v3` and `x1`,
`0xdeadbeefdeadbeef` in `x0`, and 32 bytes `17 i + 3` at `0x100`, readable
and writable. -/
def s (k : Nat) : State :=
  let (a, b, c, d, g) := input k
  { gpr := fun r => if r = .x1 then g else if r = .x2 then 0x100 else 0xdeadbeefdeadbeef
    sp := 0x1000
    v := fun r => if r = .v0 then a else if r = .v1 then b else if r = .v2 then c
      else if r = .v3 then d else 0
    mem := fun addr => if 0x100 ≤ addr.toNat ∧ addr.toNat < 0x120 then
      BitVec.ofNat 8 (17 * (addr.toNat - 0x100) + 3) else 0
    rd := []
    wr := [⟨0x100, 32⟩] }

/-- `v0` after `op` in run `k`. -/
def vrun (k : Nat) (op : VOp) : Option (BitVec 128) := (exec (.vop op) (s k)).map (·.v .v0)

/-- `x0` after `i` in run `k`. -/
def xrun (k : Nat) (i : Instr) : Option (BitVec 64) := (exec i (s k)).map (·.gpr .x0)

#guard vrun 0 (.mov .v0 .v1) == some 0xd5b39162c1984cc4c9c6de1db050fcb1#128
#guard vrun 0 (.movi0 .v0) == some 0x00000000000000000000000000000000#128
#guard vrun 0 (.dup .s4 .v0 .x1) == some 0xa12809eca12809eca12809eca12809ec#128
#guard vrun 0 (.dup .d2 .v0 .x1) == some 0x9696613da12809ec9696613da12809ec#128
#guard vrun 0 (.ins .s4 .v0 0 .x1) == some 0x47be5543e684460b8caafc59a12809ec#128
#guard vrun 0 (.ins .s4 .v0 1 .x1) == some 0x47be5543e684460ba12809ecaff91663#128
#guard vrun 0 (.ins .s4 .v0 2 .x1) == some 0x47be5543a12809ec8caafc59aff91663#128
#guard vrun 0 (.ins .s4 .v0 3 .x1) == some 0xa12809ece684460b8caafc59aff91663#128
#guard vrun 0 (.ins .d2 .v0 0 .x1) == some 0x47be5543e684460b9696613da12809ec#128
#guard vrun 0 (.ins .d2 .v0 1 .x1) == some 0x9696613da12809ec8caafc59aff91663#128
#guard vrun 0 (.dupS .v0 .v1 0) == some 0x000000000000000000000000b050fcb1#128
#guard vrun 0 (.dupS .v0 .v1 1) == some 0x000000000000000000000000c9c6de1d#128
#guard vrun 0 (.dupS .v0 .v1 2) == some 0x000000000000000000000000c1984cc4#128
#guard vrun 0 (.dupS .v0 .v1 3) == some 0x000000000000000000000000d5b39162#128
#guard vrun 0 (.logic .and .v0 .v1 .v2) == some 0x10339122c018404400c2520c0000a430#128
#guard vrun 0 (.logic .orr .v0 .v1 .v2) == some 0xddbbb3f2f3ffede5ffceff5fb87dfcbd#128
#guard vrun 0 (.logic .eor .v0 .v1 .v2) == some 0xcd8822d033e7ada1ff0cad53b87d588d#128
#guard vrun 0 (.logic .bic .v0 .v1 .v2) == some 0xc580004001800c80c9048c11b0505881#128
#guard vrun 0 (.logic .orn .v0 .v1 .v2) == some 0xf7f7dd6fcd985edec9f7debdf7d2fff3#128
#guard vrun 0 (.not .v0 .v1) == some 0x2a4c6e9d3e67b33b363921e24faf034e#128
#guard vrun 0 (.add .s4 .v0 .v1 .v2) == some 0xedef4514b4182e290091516bb87ea0ed#128
#guard vrun 0 (.sub .s4 .v0 .v1 .v2) == some 0xbd77ddb0cf186b5f92fc6acfa8235875#128
#guard vrun 0 (.shift .shl .s4 .v0 .v1 0) == some 0xd5b39162c1984cc4c9c6de1db050fcb1#128
#guard vrun 0 (.shift .shl .s4 .v0 .v1 7) == some 0xd9c8b100cc266200e36f0e80287e5880#128
#guard vrun 0 (.shift .shl .s4 .v0 .v1 31) == some 0x00000000000000008000000080000000#128
#guard vrun 0 (.shift .sli .s4 .v0 .v1 0) == some 0xd5b39162c1984cc4c9c6de1db050fcb1#128
#guard vrun 0 (.shift .sli .s4 .v0 .v1 7) == some 0xd9c8b143cc26620be36f0ed9287e58e3#128
#guard vrun 0 (.shift .sli .s4 .v0 .v1 31) == some 0x47be55436684460b8caafc59aff91663#128
#guard vrun 0 (.shift .ushr .s4 .v0 .v1 1) == some 0x6ad9c8b160cc266264e36f0e58287e58#128
#guard vrun 0 (.shift .ushr .s4 .v0 .v1 13) == some 0x0006ad9c00060cc200064e3600058287#128
#guard vrun 0 (.shift .ushr .s4 .v0 .v1 32) == some 0x00000000000000000000000000000000#128
#guard vrun 0 (.shift .sri .s4 .v0 .v1 1) == some 0x6ad9c8b1e0cc2662e4e36f0ed8287e58#128
#guard vrun 0 (.shift .sri .s4 .v0 .v1 13) == some 0x47bead9ce6860cc28cae4e36affd8287#128
#guard vrun 0 (.shift .sri .s4 .v0 .v1 32) == some 0x47be5543e684460b8caafc59aff91663#128
#guard vrun 0 (.perm .zip1 .s4 .v0 .v1 .v2) == some 0x36ca734ec9c6de1d082da43cb050fcb1#128
#guard vrun 0 (.perm .zip2 .s4 .v0 .v1 .v2) == some 0x183bb3b2d5b39162f27fe165c1984cc4#128
#guard vrun 0 (.perm .trn1 .s4 .v0 .v1 .v2) == some 0xf27fe165c1984cc4082da43cb050fcb1#128
#guard vrun 0 (.perm .trn2 .s4 .v0 .v1 .v2) == some 0x183bb3b2d5b3916236ca734ec9c6de1d#128
#guard vrun 0 (.perm .uzp1 .s4 .v0 .v1 .v2) == some 0xf27fe165082da43cc1984cc4b050fcb1#128
#guard vrun 0 (.perm .uzp2 .s4 .v0 .v1 .v2) == some 0x183bb3b236ca734ed5b39162c9c6de1d#128
#guard vrun 0 (.add .d2 .v0 .v1 .v2) == some 0xedef4515b4182e290091516bb87ea0ed#128
#guard vrun 0 (.sub .d2 .v0 .v1 .v2) == some 0xbd77ddafcf186b5f92fc6acfa8235875#128
#guard vrun 0 (.shift .shl .d2 .v0 .v1 0) == some 0xd5b39162c1984cc4c9c6de1db050fcb1#128
#guard vrun 0 (.shift .shl .d2 .v0 .v1 7) == some 0xd9c8b160cc266200e36f0ed8287e5880#128
#guard vrun 0 (.shift .shl .d2 .v0 .v1 63) == some 0x00000000000000008000000000000000#128
#guard vrun 0 (.shift .sli .d2 .v0 .v1 0) == some 0xd5b39162c1984cc4c9c6de1db050fcb1#128
#guard vrun 0 (.shift .sli .d2 .v0 .v1 7) == some 0xd9c8b160cc26620be36f0ed8287e58e3#128
#guard vrun 0 (.shift .sli .d2 .v0 .v1 63) == some 0x47be5543e684460b8caafc59aff91663#128
#guard vrun 0 (.shift .ushr .d2 .v0 .v1 1) == some 0x6ad9c8b160cc266264e36f0ed8287e58#128
#guard vrun 0 (.shift .ushr .d2 .v0 .v1 13) == some 0x0006ad9c8b160cc200064e36f0ed8287#128
#guard vrun 0 (.shift .ushr .d2 .v0 .v1 64) == some 0x00000000000000000000000000000000#128
#guard vrun 0 (.shift .sri .d2 .v0 .v1 1) == some 0x6ad9c8b160cc2662e4e36f0ed8287e58#128
#guard vrun 0 (.shift .sri .d2 .v0 .v1 13) == some 0x47bead9c8b160cc28cae4e36f0ed8287#128
#guard vrun 0 (.shift .sri .d2 .v0 .v1 64) == some 0x47be5543e684460b8caafc59aff91663#128
#guard vrun 0 (.perm .zip1 .d2 .v0 .v1 .v2) == some 0x36ca734e082da43cc9c6de1db050fcb1#128
#guard vrun 0 (.perm .zip2 .d2 .v0 .v1 .v2) == some 0x183bb3b2f27fe165d5b39162c1984cc4#128
#guard vrun 0 (.perm .trn1 .d2 .v0 .v1 .v2) == some 0x36ca734e082da43cc9c6de1db050fcb1#128
#guard vrun 0 (.perm .trn2 .d2 .v0 .v1 .v2) == some 0x183bb3b2f27fe165d5b39162c1984cc4#128
#guard vrun 0 (.perm .uzp1 .d2 .v0 .v1 .v2) == some 0x36ca734e082da43cc9c6de1db050fcb1#128
#guard vrun 0 (.perm .uzp2 .d2 .v0 .v1 .v2) == some 0x183bb3b2f27fe165d5b39162c1984cc4#128
#guard vrun 0 (.ext .v0 .v1 .v2 0) == some 0xd5b39162c1984cc4c9c6de1db050fcb1#128
#guard vrun 0 (.ext .v0 .v1 .v2 1) == some 0x3cd5b39162c1984cc4c9c6de1db050fc#128
#guard vrun 0 (.ext .v0 .v1 .v2 8) == some 0x36ca734e082da43cd5b39162c1984cc4#128
#guard vrun 0 (.ext .v0 .v1 .v2 15) == some 0x3bb3b2f27fe16536ca734e082da43cd5#128
#guard vrun 0 (.rev .rev32b .v0 .v1) == some 0x6291b3d5c44c98c11ddec6c9b1fc50b0#128
#guard vrun 0 (.rev .rev32h .v0 .v1) == some 0x9162d5b34cc4c198de1dc9c6fcb1b050#128
#guard vrun 0 (.rev .rev64b .v0 .v1) == some 0xc44c98c16291b3d5b1fc50b01ddec6c9#128
#guard vrun 0 (.rev .rev64s .v0 .v1) == some 0xc1984cc4d5b39162b050fcb1c9c6de1d#128
#guard vrun 0 (.tbl .v0 .v1 .v3) == some 0x00d5fc0062b0c60000fc005000620000#128
#guard vrun 0 (.umull false .v0 .v1 .v2) == some 0x2b2f84a73140b3d605a1f73f27f99d7c#128
#guard vrun 0 (.umull true .v0 .v1 .v2) == some 0x143aac04d7189c24b762ad9299ca8d54#128
#guard vrun 0 (.umlal false .v0 .v1 .v2) == some 0x72edd9eb17c4f9e1924cf398d7f2b3df#128
#guard vrun 0 (.umlal true .v0 .v1 .v2) == some 0x5bf90148bd9ce22f440da9ec49c3a3b7#128
#guard vrun 0 (.umullH false .v0 .v1 .v2) == some 0x2b2efa3c640ab3d605a17e10a21c9d7c#128
#guard vrun 0 (.umullH true .v0 .v1 .v2) == some 0x143a0841660c9c24b761ba6843968d54#128
#guard vrun 0 (.umlalH false .v0 .v1 .v2) == some 0x72ed4f7f4a8ef9e1924c7a695215b3df#128
#guard vrun 0 (.umlalH true .v0 .v1 .v2) == some 0x5bf85d844c90e22f440cb6c1f38fa3b7#128
#guard vrun 0 (.umullH false .v0 .v0 .v3) == some 0x08cb2caa1c980db20e77acac01eef4d4#128
#guard vrun 0 (.pmull false .v0 .v1 .v2) == some 0x1741493c224e681a0d98ad159b352e7c#128
#guard vrun 0 (.pmull true .v0 .v1 .v2) == some 0x0be6e7a8b9d9791a2b96e51a9bd89254#128
#guard vrun 0 (.aese .v0 .v1) == some 0xcc5087fd6ed31c8ac0d7671b4f9c93b5#128
#guard vrun 0 (.aesd .v0 .v1) == some 0xcbb8a37b74b7945f3df3bb8668c4887f#128
#guard vrun 0 (.aesmc .v0 .v1) == some 0x35ea400a1afb2e1eb614224c1f261286#128
#guard vrun 0 (.aesimc .v0 .v1) == some 0xfa478fa7ca42fea7d06f44372b902630#128
#guard vrun 0 (.sha1 .c .v0 .v1 .v2) == some 0x5fcd6c9bb21adb1251afbde31d3b9ccc#128
#guard vrun 0 (.sha1 .p .v0 .v1 .v2) == some 0xf94c971cd3cb11a22c739fd66779019c#128
#guard vrun 0 (.sha1 .m .v0 .v1 .v2) == some 0x5f93f06bcc0a45104995757229d0755c#128
#guard vrun 0 (.sha1h .v0 .v1) == some 0x0000000000000000000000006c143f2c#128
#guard vrun 0 (.sha1su0 .v0 .v1 .v2) == some 0x964338eca4ab5bdffddeda544150f454#128
#guard vrun 0 (.sha1su1 .v0 .v1) == some 0x17838b7f666faed29a65613acc7f90fc#128
#guard vrun 0 (.sha256h .v0 .v1 .v2) == some 0x83962e62fc642832bcc84a4e5b935e68#128
#guard vrun 0 (.sha256h2 .v0 .v1 .v2) == some 0xb08d09d6b223c9462ac54347417efecc#128
#guard vrun 0 (.sha256su0 .v0 .v1) == some 0x920527be01acadf8a74a7645cd937fbc#128
#guard vrun 0 (.sha256su1 .v0 .v1 .v2) == some 0x24c0f3e8fb3ca2bbfdec8b138662cd08#128
#guard vrun 0 (.sha512h .v0 .v1 .v2) == some 0xb9f500a529009b652f1de5e624404ede#128
#guard vrun 0 (.sha512h2 .v0 .v1 .v2) == some 0xfd4ab9e6b07a67152fcdcc94e07ca0f9#128
#guard vrun 0 (.sha512su0 .v0 .v1) == some 0x9c7779b0e57cd56834c2e4b7e762c632#128
#guard vrun 0 (.sha512su1 .v0 .v1 .v2) == some 0x074ce8dcceec869615fd4254e7abcb15#128
#guard vrun 0 (.eor3 .v0 .v1 .v2 .v3) == some 0xd38723c13fe4abb8ef0db051ad714e91#128
#guard vrun 0 (.bcax .v0 .v1 .v2 .v3) == some 0xd58323c033e4ada0ef0cbc51b8715c91#128
#guard vrun 0 (.rax1 .v0 .v1 .v2) == some 0xe5c4f60725678e0ea4523881a00bb4c9#128
#guard vrun 0 (.xar .v0 .v1 .v2 0) == some 0xcd8822d033e7ada1ff0cad53b87d588d#128
#guard vrun 0 (.xar .v0 .v1 .v2 1) == some 0xe6c4116819f3d6d0ff8656a9dc3eac46#128
#guard vrun 0 (.xar .v0 .v1 .v2 63) == some 0x9b1045a067cf5b43fe195aa770fab11b#128
#guard vrun 0 (.add .s4 .v0 .v0 .v0) == some 0x8f7caa86cd088c161955f8b25ff22cc6#128
#guard vrun 0 (.ext .v0 .v0 .v1 4) == some 0xb050fcb147be5543e684460b8caafc59#128
#guard vrun 0 (.aese .v0 .v0) == some 0x63636363636363636363636363636363#128
#guard vrun 0 (.sha256h .v0 .v0 .v2) == some 0x463c83aefb3d02a472b6c7db002c5499#128
#guard vrun 0 (.sha256su1 .v0 .v0 .v0) == some 0x5717bdb8b6c4bc6253476721e8a1413f#128
#guard vrun 0 (.sha512h .v0 .v0 .v0) == some 0xf4c536bb530108a80bd37236a4cc101d#128
#guard vrun 0 (.tbl .v0 .v0 .v3) == some 0x0047160043afaa00001600f900430000#128
#guard vrun 0 (.umlal true .v0 .v0 .v0) == some 0x5bd97611bc5dd5945c3cee8dc27b1adc#128
#guard vrun 0 (.umlalH true .v0 .v0 .v0) == some 0x5bd9464702e9d5945c3c7069c3231adc#128
#guard vrun 0 (.eor3 .v0 .v0 .v1 .v0) == some 0xd5b39162c1984cc4c9c6de1db050fcb1#128
#guard xrun 0 (.umov .w .x0 .v1 0) == some 0x00000000b050fcb1#64
#guard xrun 0 (.umov .w .x0 .v1 1) == some 0x00000000c9c6de1d#64
#guard xrun 0 (.umov .w .x0 .v1 2) == some 0x00000000c1984cc4#64
#guard xrun 0 (.umov .w .x0 .v1 3) == some 0x00000000d5b39162#64
#guard xrun 0 (.umov .x .x0 .v1 0) == some 0xc9c6de1db050fcb1#64
#guard xrun 0 (.umov .x .x0 .v1 1) == some 0xd5b39162c1984cc4#64
#guard vrun 1 (.mov .v0 .v1) == some 0xdb26ce183543c96b9f9eb90b2c4563c4#128
#guard vrun 1 (.movi0 .v0) == some 0x00000000000000000000000000000000#128
#guard vrun 1 (.dup .s4 .v0 .x1) == some 0x042e967b042e967b042e967b042e967b#128
#guard vrun 1 (.dup .d2 .v0 .x1) == some 0xd55f2bbb042e967bd55f2bbb042e967b#128
#guard vrun 1 (.ins .s4 .v0 0 .x1) == some 0x55eadb18f6d1d81649d2bf3e042e967b#128
#guard vrun 1 (.ins .s4 .v0 1 .x1) == some 0x55eadb18f6d1d816042e967bf06dbe6f#128
#guard vrun 1 (.ins .s4 .v0 2 .x1) == some 0x55eadb18042e967b49d2bf3ef06dbe6f#128
#guard vrun 1 (.ins .s4 .v0 3 .x1) == some 0x042e967bf6d1d81649d2bf3ef06dbe6f#128
#guard vrun 1 (.ins .d2 .v0 0 .x1) == some 0x55eadb18f6d1d816d55f2bbb042e967b#128
#guard vrun 1 (.ins .d2 .v0 1 .x1) == some 0xd55f2bbb042e967b49d2bf3ef06dbe6f#128
#guard vrun 1 (.dupS .v0 .v1 0) == some 0x0000000000000000000000002c4563c4#128
#guard vrun 1 (.dupS .v0 .v1 1) == some 0x0000000000000000000000009f9eb90b#128
#guard vrun 1 (.dupS .v0 .v1 2) == some 0x0000000000000000000000003543c96b#128
#guard vrun 1 (.dupS .v0 .v1 3) == some 0x000000000000000000000000db26ce18#128
#guard vrun 1 (.logic .and .v0 .v1 .v2) == some 0x180240082540000a8e88200a240003c4#128
#guard vrun 1 (.logic .orr .v0 .v1 .v2) == some 0xfb6eef3f3df3dfefffffb9ebfce7efec#128
#guard vrun 1 (.logic .eor .v0 .v1 .v2) == some 0xe36caf3718b3dfe5717799e1d8e7ec28#128
#guard vrun 1 (.logic .bic .v0 .v1 .v2) == some 0xc3248e101003c9611116990108456000#128
#guard vrun 1 (.logic .orn .v0 .v1 .v2) == some 0xdfb7ded8f74fe97b9f9eff1f2f5d73d7#128
#guard vrun 1 (.not .v0 .v1) == some 0x24d931e7cabc3694606146f4d3ba9c3b#128
#guard vrun 1 (.add .s4 .v0 .v1 .v2) == some 0x13712f476333dff98e87d9f520e7f3b0#128
#guard vrun 1 (.sub .s4 .v0 .v1 .v2) == some 0xa2dc6ce90753b2ddb0b5982137a2d3d8#128
#guard vrun 1 (.shift .shl .s4 .v0 .v1 0) == some 0xdb26ce183543c96b9f9eb90b2c4563c4#128
#guard vrun 1 (.shift .shl .s4 .v0 .v1 7) == some 0x93670c00a1e4b580cf5c858022b1e200#128
#guard vrun 1 (.shift .shl .s4 .v0 .v1 31) == some 0x00000000800000008000000000000000#128
#guard vrun 1 (.shift .sli .s4 .v0 .v1 0) == some 0xdb26ce183543c96b9f9eb90b2c4563c4#128
#guard vrun 1 (.shift .sli .s4 .v0 .v1 7) == some 0x93670c18a1e4b596cf5c85be22b1e26f#128
#guard vrun 1 (.shift .sli .s4 .v0 .v1 31) == some 0x55eadb18f6d1d816c9d2bf3e706dbe6f#128
#guard vrun 1 (.shift .ushr .s4 .v0 .v1 1) == some 0x6d93670c1aa1e4b54fcf5c851622b1e2#128
#guard vrun 1 (.shift .ushr .s4 .v0 .v1 13) == some 0x0006d9360001aa1e0004fcf50001622b#128
#guard vrun 1 (.shift .ushr .s4 .v0 .v1 32) == some 0x00000000000000000000000000000000#128
#guard vrun 1 (.shift .sri .s4 .v0 .v1 1) == some 0x6d93670c9aa1e4b54fcf5c859622b1e2#128
#guard vrun 1 (.shift .sri .s4 .v0 .v1 13) == some 0x55eed936f6d1aa1e49d4fcf5f069622b#128
#guard vrun 1 (.shift .sri .s4 .v0 .v1 32) == some 0x55eadb18f6d1d81649d2bf3ef06dbe6f#128
#guard vrun 1 (.perm .zip1 .s4 .v0 .v1 .v2) == some 0xeee920ea9f9eb90bf4a28fec2c4563c4#128
#guard vrun 1 (.perm .zip2 .s4 .v0 .v1 .v2) == some 0x384a612fdb26ce182df0168e3543c96b#128
#guard vrun 1 (.perm .trn1 .s4 .v0 .v1 .v2) == some 0x2df0168e3543c96bf4a28fec2c4563c4#128
#guard vrun 1 (.perm .trn2 .s4 .v0 .v1 .v2) == some 0x384a612fdb26ce18eee920ea9f9eb90b#128
#guard vrun 1 (.perm .uzp1 .s4 .v0 .v1 .v2) == some 0x2df0168ef4a28fec3543c96b2c4563c4#128
#guard vrun 1 (.perm .uzp2 .s4 .v0 .v1 .v2) == some 0x384a612feee920eadb26ce189f9eb90b#128
#guard vrun 1 (.add .d2 .v0 .v1 .v2) == some 0x13712f476333dff98e87d9f620e7f3b0#128
#guard vrun 1 (.sub .d2 .v0 .v1 .v2) == some 0xa2dc6ce90753b2ddb0b5982037a2d3d8#128
#guard vrun 1 (.shift .shl .d2 .v0 .v1 0) == some 0xdb26ce183543c96b9f9eb90b2c4563c4#128
#guard vrun 1 (.shift .shl .d2 .v0 .v1 7) == some 0x93670c1aa1e4b580cf5c859622b1e200#128
#guard vrun 1 (.shift .shl .d2 .v0 .v1 63) == some 0x80000000000000000000000000000000#128
#guard vrun 1 (.shift .sli .d2 .v0 .v1 0) == some 0xdb26ce183543c96b9f9eb90b2c4563c4#128
#guard vrun 1 (.shift .sli .d2 .v0 .v1 7) == some 0x93670c1aa1e4b596cf5c859622b1e26f#128
#guard vrun 1 (.shift .sli .d2 .v0 .v1 63) == some 0xd5eadb18f6d1d81649d2bf3ef06dbe6f#128
#guard vrun 1 (.shift .ushr .d2 .v0 .v1 1) == some 0x6d93670c1aa1e4b54fcf5c859622b1e2#128
#guard vrun 1 (.shift .ushr .d2 .v0 .v1 13) == some 0x0006d93670c1aa1e0004fcf5c859622b#128
#guard vrun 1 (.shift .ushr .d2 .v0 .v1 64) == some 0x00000000000000000000000000000000#128
#guard vrun 1 (.shift .sri .d2 .v0 .v1 1) == some 0x6d93670c1aa1e4b54fcf5c859622b1e2#128
#guard vrun 1 (.shift .sri .d2 .v0 .v1 13) == some 0x55eed93670c1aa1e49d4fcf5c859622b#128
#guard vrun 1 (.shift .sri .d2 .v0 .v1 64) == some 0x55eadb18f6d1d81649d2bf3ef06dbe6f#128
#guard vrun 1 (.perm .zip1 .d2 .v0 .v1 .v2) == some 0xeee920eaf4a28fec9f9eb90b2c4563c4#128
#guard vrun 1 (.perm .zip2 .d2 .v0 .v1 .v2) == some 0x384a612f2df0168edb26ce183543c96b#128
#guard vrun 1 (.perm .trn1 .d2 .v0 .v1 .v2) == some 0xeee920eaf4a28fec9f9eb90b2c4563c4#128
#guard vrun 1 (.perm .trn2 .d2 .v0 .v1 .v2) == some 0x384a612f2df0168edb26ce183543c96b#128
#guard vrun 1 (.perm .uzp1 .d2 .v0 .v1 .v2) == some 0xeee920eaf4a28fec9f9eb90b2c4563c4#128
#guard vrun 1 (.perm .uzp2 .d2 .v0 .v1 .v2) == some 0x384a612f2df0168edb26ce183543c96b#128
#guard vrun 1 (.ext .v0 .v1 .v2 0) == some 0xdb26ce183543c96b9f9eb90b2c4563c4#128
#guard vrun 1 (.ext .v0 .v1 .v2 1) == some 0xecdb26ce183543c96b9f9eb90b2c4563#128
#guard vrun 1 (.ext .v0 .v1 .v2 8) == some 0xeee920eaf4a28fecdb26ce183543c96b#128
#guard vrun 1 (.ext .v0 .v1 .v2 15) == some 0x4a612f2df0168eeee920eaf4a28fecdb#128
#guard vrun 1 (.rev .rev32b .v0 .v1) == some 0x18ce26db6bc943350bb99e9fc463452c#128
#guard vrun 1 (.rev .rev32h .v0 .v1) == some 0xce18db26c96b3543b90b9f9e63c42c45#128
#guard vrun 1 (.rev .rev64b .v0 .v1) == some 0x6bc9433518ce26dbc463452c0bb99e9f#128
#guard vrun 1 (.rev .rev64s .v0 .v1) == some 0x3543c96bdb26ce182c4563c49f9eb90b#128
#guard vrun 1 (.tbl .v0 .v1 .v3) == some 0x000000c4db262c00c4c400000043db9e#128
#guard vrun 1 (.umull false .v0 .v1 .v2) == some 0x94f6ec046339840e2a4e3fe384ba74b0#128
#guard vrun 1 (.umull true .v0 .v1 .v2) == some 0x3030297ec326ee68098edea60238eb5a#128
#guard vrun 1 (.umlal false .v0 .v1 .v2) == some 0xeae1c71d5a0b5c247420ff227528331f#128
#guard vrun 1 (.umlal true .v0 .v1 .v2) == some 0x861b0497b9f8c67e53619de4f2a6a9c9#128
#guard vrun 1 (.umullH false .v0 .v1 .v2) == some 0x94f62ace17ca840e2a4dc7aa381674b0#128
#guard vrun 1 (.umullH true .v0 .v1 .v2) == some 0x302fa8fc4e3cee68098eb5d011beeb5a#128
#guard vrun 1 (.umlalH false .v0 .v1 .v2) == some 0xeae105e60e9c5c24742086e82884331f#128
#guard vrun 1 (.umlalH true .v0 .v1 .v2) == some 0x861a8414450ec67e5361750e022ca9c9#128
#guard vrun 1 (.umullH false .v0 .v0 .v3) == some 0x0000000014377de014b2c2420b2cf79a#128
#guard vrun 1 (.pmull false .v0 .v1 .v2) == some 0x7c193c7b7397c25d5a1bf2afa5a486b0#128
#guard vrun 1 (.pmull true .v0 .v1 .v2) == some 0x103e08f3c079d0fc76eefe90abc383a2#128
#guard vrun 1 (.aese .v0 .v1) == some 0x2e29c163f63459ff864b8296194f6f62#128
#guard vrun 1 (.aesd .v0 .v1) == some 0x935de352e6eea5133327c9d94a742f0e#128
#guard vrun 1 (.aesmc .v0 .v1) == some 0x6dec2e845d7b12e01f2f44c72959e15f#128
#guard vrun 1 (.aesimc .v0 .v1) == some 0x7a57393f7a2135ba68a2334a2441ec47#128
#guard vrun 1 (.sha1 .c .v0 .v1 .v2) == some 0x20e6267153b708bc90c27c5893d60b8b#128
#guard vrun 1 (.sha1 .p .v0 .v1 .v2) == some 0x86625f77c2b3205ef638db8f02903493#128
#guard vrun 1 (.sha1 .m .v0 .v1 .v2) == some 0x211ca733716754f86cdf1aab4bbfce1e#128
#guard vrun 1 (.sha1h .v0 .v1) == some 0x0000000000000000000000000b1158f1#128
#guard vrun 1 (.sha1su0 .v0 .v1 .v2) == some 0xf23e033cf764ad5cf2d144ccf21ee995#128
#guard vrun 1 (.sha1su1 .v0 .v1) == some 0x1419aba15bee2c1cf922ecaadfe60ec8#128
#guard vrun 1 (.sha256h .v0 .v1 .v2) == some 0xe1c497d97746073f1651782da1393a02#128
#guard vrun 1 (.sha256h2 .v0 .v1 .v2) == some 0xb165c410862835898af9be50fd0f88ed#128
#guard vrun 1 (.sha256su0 .v0 .v1) == some 0x2b0c08c683a273c58f04e444cad41f5c#128
#guard vrun 1 (.sha256su1 .v0 .v1 .v2) == some 0x71e9213329a7bb97fbd2f25d99aa26bd#128
#guard vrun 1 (.sha512h .v0 .v1 .v2) == some 0xf92721648f00fd877ab443d1beac0b3c#128
#guard vrun 1 (.sha512h2 .v0 .v1 .v2) == some 0x379e146e30a774b6e2dcb854bd79d4ed#128
#guard vrun 1 (.sha512su0 .v0 .v1) == some 0xe05ada678228565c85de122042e15cd2#128
#guard vrun 1 (.sha512su1 .v0 .v1 .v2) == some 0x31accce537ca31778baf01787ecbbc7e#128
#guard vrun 1 (.eor3 .v0 .v1 .v2 .v3) == some 0xf877b13717bddcf3717782f1ceede32e#128
#guard vrun 1 (.bcax .v0 .v1 .v2 .v3) == some 0xfb66af3715b3dde3717799e1cce5e32c#128
#guard vrun 1 (.rax1 .v0 .v1 .v2) == some 0xabb20c466ea3e477424cf8dec5007c1d#128
#guard vrun 1 (.xar .v0 .v1 .v2 0) == some 0xe36caf3718b3dfe5717799e1d8e7ec28#128
#guard vrun 1 (.xar .v0 .v1 .v2 1) == some 0xf1b6579b8c59eff238bbccf0ec73f614#128
#guard vrun 1 (.xar .v0 .v1 .v2 63) == some 0xc6d95e6e3167bfcbe2ef33c3b1cfd850#128
#guard vrun 1 (.add .s4 .v0 .v0 .v0) == some 0xabd5b630eda3b02c93a57e7ce0db7cde#128
#guard vrun 1 (.ext .v0 .v0 .v1 4) == some 0x2c4563c455eadb18f6d1d81649d2bf3e#128
#guard vrun 1 (.aese .v0 .v0) == some 0x63636363636363636363636363636363#128
#guard vrun 1 (.sha256h .v0 .v0 .v2) == some 0x80ae076d625d53ae215e5681f75091a3#128
#guard vrun 1 (.sha256su1 .v0 .v0 .v0) == some 0xedd72c07230faae5779ef25211748f71#128
#guard vrun 1 (.sha512h .v0 .v0 .v0) == some 0x31d5206fb8a283ba6b40f2af7ed8989f#128
#guard vrun 1 (.tbl .v0 .v0 .v3) == some 0x0000006f55eaf0006f6f000000d155d2#128
#guard vrun 1 (.umlal true .v0 .v0 .v0) == some 0x72c0a80c2a33ea5637cab68bc2bee053#128
#guard vrun 1 (.umlalH true .v0 .v0 .v0) == some 0x72c014fcb253ea5637c915dfa6d2e053#128
#guard vrun 1 (.eor3 .v0 .v0 .v1 .v0) == some 0xdb26ce183543c96b9f9eb90b2c4563c4#128
#guard xrun 1 (.umov .w .x0 .v1 0) == some 0x000000002c4563c4#64
#guard xrun 1 (.umov .w .x0 .v1 1) == some 0x000000009f9eb90b#64
#guard xrun 1 (.umov .w .x0 .v1 2) == some 0x000000003543c96b#64
#guard xrun 1 (.umov .w .x0 .v1 3) == some 0x00000000db26ce18#64
#guard xrun 1 (.umov .x .x0 .v1 0) == some 0x9f9eb90b2c4563c4#64
#guard xrun 1 (.umov .x .x0 .v1 1) == some 0xdb26ce183543c96b#64

/-! ## Only the destination changes -/

/-- The registers other than `v0` and `x0` after `i` in run 0 are those before. -/
def others (i : Instr) : Bool :=
  match exec i (s 0) with
  | some t => [VReg.v1, .v2, .v3, .v7, .v16, .v31].all (fun r => t.v r == (s 0).v r) &&
    [Reg.x1, .x2, .x3, .x30].all (fun r => t.gpr r == (s 0).gpr r) && t.sp == (s 0).sp
  | none => false

#guard others (.vop (.aese .v0 .v1))
#guard others (.vop (.sha256h .v0 .v1 .v2))
#guard others (.vop (.ins .s4 .v0 1 .x1))
#guard others (.vop (.umlal true .v0 .v1 .v2))
#guard others (.vop (.umlalH true .v0 .v1 .v2))
#guard others (.umov .x .x0 .v1 1)
#guard (exec (.vop (.aese .v0 .v1)) (s 0)).map (·.gpr .x0) == some 0xdeadbeefdeadbeef

/-! ## Immediates that are not encodable fault -/

#guard vrun 0 (.ext .v0 .v1 .v2 16) == none
#guard vrun 0 (.shift .shl .s4 .v0 .v1 32) == none
#guard vrun 0 (.shift .sli .d2 .v0 .v1 64) == none
#guard vrun 0 (.shift .ushr .s4 .v0 .v1 0) == none
#guard vrun 0 (.shift .sri .s4 .v0 .v1 33) == none
#guard vrun 0 (.shift .ushr .d2 .v0 .v1 65) == none
#guard vrun 0 (.ins .s4 .v0 4 .x1) == none
#guard vrun 0 (.ins .d2 .v0 2 .x1) == none
#guard vrun 0 (.dupS .v0 .v1 4) == none
#guard vrun 0 (.xar .v0 .v1 .v2 64) == none
#guard xrun 0 (.umov .w .x0 .v1 4) == none
#guard xrun 0 (.umov .x .x0 .v1 2) == none

/-! ## Loads and stores of a vector register

`ldr q`/`str q` move 16 bytes, little-endian, at an offset that is a multiple
of 16 below 65536, within the permitted regions. -/

/-- The 16 bytes at `0x100 + o` in `s k`, little-endian. -/
def bytesAt (o : Nat) : BitVec 128 :=
  BitVec.ofNat 128 ((List.range 16).foldl (fun acc i => acc + (17 * (o + i) + 3) % 256 * 256 ^ i) 0)

#guard bytesAt 0 == 0x02f1e0cfbead9c8b7a69584736251403#128
#guard ((exec (.ldrq .v0 .x2 0) (s 0)).map (·.v .v0)) == some (bytesAt 0)
#guard ((exec (.ldrq .v0 .x2 16) (s 0)).map (·.v .v0)) == some (bytesAt 16)
#guard ((exec (.ldrq .v0 .x2 8) (s 0)).map (·.v .v0)) == none
#guard ((exec (.ldrq .v0 .x2 32) (s 0)).map (·.v .v0)) == none
#guard ((exec (.ldrq .v0 .x2 65536) (s 0)).map (·.v .v0)) == none
#guard ((exec (.strq .v1 .x2 16) (s 0)).bind fun t => (exec (.ldrq .v0 .x2 16) t).map (·.v .v0)) ==
  some ((s 0).v .v1)
#guard ((exec (.strq .v1 .x2 16) (s 0)).map fun t => (t.mem 0x10f, t.mem 0x110)) ==
  some (0x02, vbyte ((s 0).v .v1) 0)
#guard ((exec (.strq .v1 .x2 32) (s 0)).map (·.v .v0)) == none

/-! ## Printing -/

#guard Instr.asm (.vop (.mov .v0 .v1)) == ["mov v0.16b, v1.16b"]
#guard Instr.asm (.vop (.movi0 .v0)) == ["movi v0.2d, #0"]
#guard Instr.asm (.vop (.dup .s4 .v0 .x1)) == ["dup v0.4s, w1"]
#guard Instr.asm (.vop (.dup .d2 .v0 .x1)) == ["dup v0.2d, x1"]
#guard Instr.asm (.vop (.ins .s4 .v0 0 .x1)) == ["mov v0.s[0], w1"]
#guard Instr.asm (.vop (.ins .s4 .v0 1 .x1)) == ["mov v0.s[1], w1"]
#guard Instr.asm (.vop (.ins .s4 .v0 2 .x1)) == ["mov v0.s[2], w1"]
#guard Instr.asm (.vop (.ins .s4 .v0 3 .x1)) == ["mov v0.s[3], w1"]
#guard Instr.asm (.vop (.ins .d2 .v0 0 .x1)) == ["mov v0.d[0], x1"]
#guard Instr.asm (.vop (.ins .d2 .v0 1 .x1)) == ["mov v0.d[1], x1"]
#guard Instr.asm (.vop (.dupS .v0 .v1 0)) == ["dup s0, v1.s[0]"]
#guard Instr.asm (.vop (.dupS .v0 .v1 1)) == ["dup s0, v1.s[1]"]
#guard Instr.asm (.vop (.dupS .v0 .v1 2)) == ["dup s0, v1.s[2]"]
#guard Instr.asm (.vop (.dupS .v0 .v1 3)) == ["dup s0, v1.s[3]"]
#guard Instr.asm (.vop (.logic .and .v0 .v1 .v2)) == ["and v0.16b, v1.16b, v2.16b"]
#guard Instr.asm (.vop (.logic .orr .v0 .v1 .v2)) == ["orr v0.16b, v1.16b, v2.16b"]
#guard Instr.asm (.vop (.logic .eor .v0 .v1 .v2)) == ["eor v0.16b, v1.16b, v2.16b"]
#guard Instr.asm (.vop (.logic .bic .v0 .v1 .v2)) == ["bic v0.16b, v1.16b, v2.16b"]
#guard Instr.asm (.vop (.logic .orn .v0 .v1 .v2)) == ["orn v0.16b, v1.16b, v2.16b"]
#guard Instr.asm (.vop (.not .v0 .v1)) == ["not v0.16b, v1.16b"]
#guard Instr.asm (.vop (.add .s4 .v0 .v1 .v2)) == ["add v0.4s, v1.4s, v2.4s"]
#guard Instr.asm (.vop (.sub .s4 .v0 .v1 .v2)) == ["sub v0.4s, v1.4s, v2.4s"]
#guard Instr.asm (.vop (.shift .shl .s4 .v0 .v1 0)) == ["shl v0.4s, v1.4s, #0"]
#guard Instr.asm (.vop (.shift .shl .s4 .v0 .v1 7)) == ["shl v0.4s, v1.4s, #7"]
#guard Instr.asm (.vop (.shift .shl .s4 .v0 .v1 31)) == ["shl v0.4s, v1.4s, #31"]
#guard Instr.asm (.vop (.shift .sli .s4 .v0 .v1 0)) == ["sli v0.4s, v1.4s, #0"]
#guard Instr.asm (.vop (.shift .sli .s4 .v0 .v1 7)) == ["sli v0.4s, v1.4s, #7"]
#guard Instr.asm (.vop (.shift .sli .s4 .v0 .v1 31)) == ["sli v0.4s, v1.4s, #31"]
#guard Instr.asm (.vop (.shift .ushr .s4 .v0 .v1 1)) == ["ushr v0.4s, v1.4s, #1"]
#guard Instr.asm (.vop (.shift .ushr .s4 .v0 .v1 13)) == ["ushr v0.4s, v1.4s, #13"]
#guard Instr.asm (.vop (.shift .ushr .s4 .v0 .v1 32)) == ["ushr v0.4s, v1.4s, #32"]
#guard Instr.asm (.vop (.shift .sri .s4 .v0 .v1 1)) == ["sri v0.4s, v1.4s, #1"]
#guard Instr.asm (.vop (.shift .sri .s4 .v0 .v1 13)) == ["sri v0.4s, v1.4s, #13"]
#guard Instr.asm (.vop (.shift .sri .s4 .v0 .v1 32)) == ["sri v0.4s, v1.4s, #32"]
#guard Instr.asm (.vop (.perm .zip1 .s4 .v0 .v1 .v2)) == ["zip1 v0.4s, v1.4s, v2.4s"]
#guard Instr.asm (.vop (.perm .zip2 .s4 .v0 .v1 .v2)) == ["zip2 v0.4s, v1.4s, v2.4s"]
#guard Instr.asm (.vop (.perm .trn1 .s4 .v0 .v1 .v2)) == ["trn1 v0.4s, v1.4s, v2.4s"]
#guard Instr.asm (.vop (.perm .trn2 .s4 .v0 .v1 .v2)) == ["trn2 v0.4s, v1.4s, v2.4s"]
#guard Instr.asm (.vop (.perm .uzp1 .s4 .v0 .v1 .v2)) == ["uzp1 v0.4s, v1.4s, v2.4s"]
#guard Instr.asm (.vop (.perm .uzp2 .s4 .v0 .v1 .v2)) == ["uzp2 v0.4s, v1.4s, v2.4s"]
#guard Instr.asm (.vop (.add .d2 .v0 .v1 .v2)) == ["add v0.2d, v1.2d, v2.2d"]
#guard Instr.asm (.vop (.sub .d2 .v0 .v1 .v2)) == ["sub v0.2d, v1.2d, v2.2d"]
#guard Instr.asm (.vop (.shift .shl .d2 .v0 .v1 0)) == ["shl v0.2d, v1.2d, #0"]
#guard Instr.asm (.vop (.shift .shl .d2 .v0 .v1 7)) == ["shl v0.2d, v1.2d, #7"]
#guard Instr.asm (.vop (.shift .shl .d2 .v0 .v1 63)) == ["shl v0.2d, v1.2d, #63"]
#guard Instr.asm (.vop (.shift .sli .d2 .v0 .v1 0)) == ["sli v0.2d, v1.2d, #0"]
#guard Instr.asm (.vop (.shift .sli .d2 .v0 .v1 7)) == ["sli v0.2d, v1.2d, #7"]
#guard Instr.asm (.vop (.shift .sli .d2 .v0 .v1 63)) == ["sli v0.2d, v1.2d, #63"]
#guard Instr.asm (.vop (.shift .ushr .d2 .v0 .v1 1)) == ["ushr v0.2d, v1.2d, #1"]
#guard Instr.asm (.vop (.shift .ushr .d2 .v0 .v1 13)) == ["ushr v0.2d, v1.2d, #13"]
#guard Instr.asm (.vop (.shift .ushr .d2 .v0 .v1 64)) == ["ushr v0.2d, v1.2d, #64"]
#guard Instr.asm (.vop (.shift .sri .d2 .v0 .v1 1)) == ["sri v0.2d, v1.2d, #1"]
#guard Instr.asm (.vop (.shift .sri .d2 .v0 .v1 13)) == ["sri v0.2d, v1.2d, #13"]
#guard Instr.asm (.vop (.shift .sri .d2 .v0 .v1 64)) == ["sri v0.2d, v1.2d, #64"]
#guard Instr.asm (.vop (.perm .zip1 .d2 .v0 .v1 .v2)) == ["zip1 v0.2d, v1.2d, v2.2d"]
#guard Instr.asm (.vop (.perm .zip2 .d2 .v0 .v1 .v2)) == ["zip2 v0.2d, v1.2d, v2.2d"]
#guard Instr.asm (.vop (.perm .trn1 .d2 .v0 .v1 .v2)) == ["trn1 v0.2d, v1.2d, v2.2d"]
#guard Instr.asm (.vop (.perm .trn2 .d2 .v0 .v1 .v2)) == ["trn2 v0.2d, v1.2d, v2.2d"]
#guard Instr.asm (.vop (.perm .uzp1 .d2 .v0 .v1 .v2)) == ["uzp1 v0.2d, v1.2d, v2.2d"]
#guard Instr.asm (.vop (.perm .uzp2 .d2 .v0 .v1 .v2)) == ["uzp2 v0.2d, v1.2d, v2.2d"]
#guard Instr.asm (.vop (.ext .v0 .v1 .v2 0)) == ["ext v0.16b, v1.16b, v2.16b, #0"]
#guard Instr.asm (.vop (.ext .v0 .v1 .v2 1)) == ["ext v0.16b, v1.16b, v2.16b, #1"]
#guard Instr.asm (.vop (.ext .v0 .v1 .v2 8)) == ["ext v0.16b, v1.16b, v2.16b, #8"]
#guard Instr.asm (.vop (.ext .v0 .v1 .v2 15)) == ["ext v0.16b, v1.16b, v2.16b, #15"]
#guard Instr.asm (.vop (.rev .rev32b .v0 .v1)) == ["rev32 v0.16b, v1.16b"]
#guard Instr.asm (.vop (.rev .rev32h .v0 .v1)) == ["rev32 v0.8h, v1.8h"]
#guard Instr.asm (.vop (.rev .rev64b .v0 .v1)) == ["rev64 v0.16b, v1.16b"]
#guard Instr.asm (.vop (.rev .rev64s .v0 .v1)) == ["rev64 v0.4s, v1.4s"]
#guard Instr.asm (.vop (.tbl .v0 .v1 .v3)) == ["tbl v0.16b, {v1.16b}, v3.16b"]
#guard Instr.asm (.vop (.umull false .v0 .v1 .v2)) == ["umull v0.2d, v1.2s, v2.2s"]
#guard Instr.asm (.vop (.umull true .v0 .v1 .v2)) == ["umull2 v0.2d, v1.4s, v2.4s"]
#guard Instr.asm (.vop (.umlal false .v0 .v1 .v2)) == ["umlal v0.2d, v1.2s, v2.2s"]
#guard Instr.asm (.vop (.umlal true .v0 .v1 .v2)) == ["umlal2 v0.2d, v1.4s, v2.4s"]
#guard Instr.asm (.vop (.umullH false .v0 .v1 .v2)) == ["umull v0.4s, v1.4h, v2.4h"]
#guard Instr.asm (.vop (.umullH true .v0 .v1 .v2)) == ["umull2 v0.4s, v1.8h, v2.8h"]
#guard Instr.asm (.vop (.umlalH false .v0 .v1 .v2)) == ["umlal v0.4s, v1.4h, v2.4h"]
#guard Instr.asm (.vop (.umlalH true .v0 .v1 .v2)) == ["umlal2 v0.4s, v1.8h, v2.8h"]
#guard Instr.asm (.vop (.umullH false .v0 .v0 .v3)) == ["umull v0.4s, v0.4h, v3.4h"]
#guard Instr.asm (.vop (.umlalH true .v0 .v0 .v0)) == ["umlal2 v0.4s, v0.8h, v0.8h"]
#guard Instr.asm (.vop (.pmull false .v0 .v1 .v2)) == ["pmull v0.1q, v1.1d, v2.1d"]
#guard Instr.asm (.vop (.pmull true .v0 .v1 .v2)) == ["pmull2 v0.1q, v1.2d, v2.2d"]
#guard Instr.asm (.vop (.aese .v0 .v1)) == ["aese v0.16b, v1.16b"]
#guard Instr.asm (.vop (.aesd .v0 .v1)) == ["aesd v0.16b, v1.16b"]
#guard Instr.asm (.vop (.aesmc .v0 .v1)) == ["aesmc v0.16b, v1.16b"]
#guard Instr.asm (.vop (.aesimc .v0 .v1)) == ["aesimc v0.16b, v1.16b"]
#guard Instr.asm (.vop (.sha1 .c .v0 .v1 .v2)) == ["sha1c q0, s1, v2.4s"]
#guard Instr.asm (.vop (.sha1 .p .v0 .v1 .v2)) == ["sha1p q0, s1, v2.4s"]
#guard Instr.asm (.vop (.sha1 .m .v0 .v1 .v2)) == ["sha1m q0, s1, v2.4s"]
#guard Instr.asm (.vop (.sha1h .v0 .v1)) == ["sha1h s0, s1"]
#guard Instr.asm (.vop (.sha1su0 .v0 .v1 .v2)) == ["sha1su0 v0.4s, v1.4s, v2.4s"]
#guard Instr.asm (.vop (.sha1su1 .v0 .v1)) == ["sha1su1 v0.4s, v1.4s"]
#guard Instr.asm (.vop (.sha256h .v0 .v1 .v2)) == ["sha256h q0, q1, v2.4s"]
#guard Instr.asm (.vop (.sha256h2 .v0 .v1 .v2)) == ["sha256h2 q0, q1, v2.4s"]
#guard Instr.asm (.vop (.sha256su0 .v0 .v1)) == ["sha256su0 v0.4s, v1.4s"]
#guard Instr.asm (.vop (.sha256su1 .v0 .v1 .v2)) == ["sha256su1 v0.4s, v1.4s, v2.4s"]
#guard Instr.asm (.vop (.sha512h .v0 .v1 .v2)) == ["sha512h q0, q1, v2.2d"]
#guard Instr.asm (.vop (.sha512h2 .v0 .v1 .v2)) == ["sha512h2 q0, q1, v2.2d"]
#guard Instr.asm (.vop (.sha512su0 .v0 .v1)) == ["sha512su0 v0.2d, v1.2d"]
#guard Instr.asm (.vop (.sha512su1 .v0 .v1 .v2)) == ["sha512su1 v0.2d, v1.2d, v2.2d"]
#guard Instr.asm (.vop (.eor3 .v0 .v1 .v2 .v3)) == ["eor3 v0.16b, v1.16b, v2.16b, v3.16b"]
#guard Instr.asm (.vop (.bcax .v0 .v1 .v2 .v3)) == ["bcax v0.16b, v1.16b, v2.16b, v3.16b"]
#guard Instr.asm (.vop (.rax1 .v0 .v1 .v2)) == ["rax1 v0.2d, v1.2d, v2.2d"]
#guard Instr.asm (.vop (.xar .v0 .v1 .v2 0)) == ["xar v0.2d, v1.2d, v2.2d, #0"]
#guard Instr.asm (.vop (.xar .v0 .v1 .v2 1)) == ["xar v0.2d, v1.2d, v2.2d, #1"]
#guard Instr.asm (.vop (.xar .v0 .v1 .v2 63)) == ["xar v0.2d, v1.2d, v2.2d, #63"]
#guard Instr.asm (.vop (.add .s4 .v0 .v0 .v0)) == ["add v0.4s, v0.4s, v0.4s"]
#guard Instr.asm (.vop (.ext .v0 .v0 .v1 4)) == ["ext v0.16b, v0.16b, v1.16b, #4"]
#guard Instr.asm (.vop (.aese .v0 .v0)) == ["aese v0.16b, v0.16b"]
#guard Instr.asm (.vop (.sha256h .v0 .v0 .v2)) == ["sha256h q0, q0, v2.4s"]
#guard Instr.asm (.vop (.sha256su1 .v0 .v0 .v0)) == ["sha256su1 v0.4s, v0.4s, v0.4s"]
#guard Instr.asm (.vop (.sha512h .v0 .v0 .v0)) == ["sha512h q0, q0, v0.2d"]
#guard Instr.asm (.vop (.tbl .v0 .v0 .v3)) == ["tbl v0.16b, {v0.16b}, v3.16b"]
#guard Instr.asm (.vop (.umlal true .v0 .v0 .v0)) == ["umlal2 v0.2d, v0.4s, v0.4s"]
#guard Instr.asm (.vop (.eor3 .v0 .v0 .v1 .v0)) == ["eor3 v0.16b, v0.16b, v1.16b, v0.16b"]
#guard Instr.asm (.umov .w .x0 .v1 0) == ["umov w0, v1.s[0]"]
#guard Instr.asm (.umov .w .x0 .v1 1) == ["umov w0, v1.s[1]"]
#guard Instr.asm (.umov .w .x0 .v1 2) == ["umov w0, v1.s[2]"]
#guard Instr.asm (.umov .w .x0 .v1 3) == ["umov w0, v1.s[3]"]
#guard Instr.asm (.umov .x .x0 .v1 0) == ["umov x0, v1.d[0]"]
#guard Instr.asm (.umov .x .x0 .v1 1) == ["umov x0, v1.d[1]"]
#guard Instr.asm (.ldrq .v31 .x2 16) == ["ldr q31, [x2, #16]"]
#guard Instr.asm (.strq .v16 .x30 65520) == ["str q16, [x30, #65520]"]
#guard printer.enableFeature "aes" == [".arch_extension aes"]
#guard printer.disableFeature "sha3" == [".arch_extension nosha3"]

/-! ## CPU features -/

#guard isa.requires (.vop (.aese .v0 .v1)) == ["aes"]
#guard isa.requires (.vop (.aesimc .v0 .v1)) == ["aes"]
#guard isa.requires (.vop (.pmull true .v0 .v1 .v2)) == ["aes"]
#guard isa.requires (.vop (.sha1 .m .v0 .v1 .v2)) == ["sha2"]
#guard isa.requires (.vop (.sha1h .v0 .v1)) == ["sha2"]
#guard isa.requires (.vop (.sha256su1 .v0 .v1 .v2)) == ["sha2"]
#guard isa.requires (.vop (.sha512h2 .v0 .v1 .v2)) == ["sha3"]
#guard isa.requires (.vop (.eor3 .v0 .v1 .v2 .v3)) == ["sha3"]
#guard isa.requires (.vop (.xar .v0 .v1 .v2 3)) == ["sha3"]
#guard isa.requires (.vop (.tbl .v0 .v1 .v2)) == []
#guard isa.requires (.vop (.umullH true .v0 .v1 .v2)) == []
#guard isa.requires (.vop (.umlalH false .v0 .v1 .v2)) == []
#guard isa.requires (.vop (.umull false .v0 .v1 .v2)) == []
#guard isa.requires (.ldrq .v0 .x1 0) == []
#guard isa.requires (.umov .x .x0 .v1 0) == []
#guard !isa.writesSp (.vop (.add .s4 .v0 .v1 .v2))

/-! ## MUL, MLA, MLS, SQDMULH and UMIN

These expected values were computed on Arm hardware (an Apple M1 Max), by
the same instructions as the printer prints them (checked below), in inline
assembly that loaded `v0`–`v3` from the inputs above and stored `v0`
afterwards, as for the others. -/

#guard vrun 0 (.mul .v0 .v1 .v2) == some 0xd7189c2499ca8d543140b3d627f99d7c#128
#guard vrun 0 (.mul .v0 .v0 .v1) == some 0xa20096a6a398e46c4409c415ec31ee73#128
#guard vrun 0 (.mla .v0 .v1 .v2) == some 0x1ed6f167804ed35fbdebb02fd7f2b3df#128
#guard vrun 0 (.mla .v0 .v0 .v1) == some 0xe9beebe98a1d2a77d0b4c06e9c2b04d6#128
#guard vrun 0 (.mls .v0 .v1 .v2) == some 0x70a5b91f4cb9b8b75b6a488387ff78e7#128
#guard vrun 0 (.mls .v0 .v0 .v1) == some 0xa5bdbe9d42eb619f48a13844c3c727f0#128
#guard vrun 0 (.sqdmulh .v0 .v1 .v2) == some 0xf7fdf0a50694fed3e8ca22b2fae8a606#128
#guard vrun 0 (.sqdmulh .v0 .v0 .v1) == some 0xe84ab5030c6c935130db57ee31d1afb3#128
#guard vrun 0 (.sqdmulh .v0 .v3 .v1) == some 0xf61120c3fa24cdcbf9386307f2e5c349#128
#guard vrun 0 (.umin .v0 .v1 .v2) == some 0x183bb3b2c1984cc436ca734e082da43c#128
#guard vrun 0 (.umin .v0 .v0 .v1) == some 0x47be5543c1984cc48caafc59aff91663#128
#guard vrun 1 (.mul .v0 .v1 .v2) == some 0xc326ee680238eb5a6339840e84ba74b0#128
#guard vrun 1 (.mul .v0 .v0 .v1) == some 0x17e1da4008209732028605aaec95b9fc#128
#guard vrun 1 (.mla .v0 .v1 .v2) == some 0x1911c980f90ac370ad0c434c7528331f#128
#guard vrun 1 (.mla .v0 .v0 .v1) == some 0x6dccb558fef26f484c58c4e8dd03786b#128
#guard vrun 1 (.mls .v0 .v1 .v2) == some 0x92c3ecb0f498ecbce6993b306bb349bf#128
#guard vrun 1 (.mls .v0 .v0 .v1) == some 0x3e0900d8eeb140e4474cb99403d80473#128
#guard vrun 1 (.sqdmulh .v0 .v1 .v2) == some 0xefcb909f131dbd4c0cde241efc11b83f#128
#guard vrun 1 (.sqdmulh .v0 .v0 .v1) == some 0xe74428bafc2e06dec869d5f0fa9d487b#128
#guard vrun 1 (.sqdmulh .v0 .v3 .v1) == some 0xf83261050643c64dffffeb9f079f67c3#128
#guard vrun 1 (.umin .v0 .v1 .v2) == some 0x384a612f2df0168e9f9eb90b2c4563c4#128
#guard vrun 1 (.umin .v0 .v0 .v1) == some 0x55eadb183543c96b49d2bf3e2c4563c4#128

/-- `v0` after `sqdmulh v0.4s, v1.4s, v2.4s` with `v1 = x` and `v2 = y`. -/
def sqd (x y : BitVec 128) : Option (BitVec 128) :=
  (exec (.vop (.sqdmulh .v0 .v1 .v2)) { s 0 with v := fun r => if r = .v1 then x else if r = .v2 then y
    else 0 }).map (·.v .v0)

-- `-2 ^ 31` times `-1`, `-2 ^ 31 + 1`, `1` and `2 ^ 31 - 1` (on the M1 Max, as above).
#guard sqd 0x80000000800000008000000080000000#128 0x7fffffff0000000180000001ffffffff#128 ==
  some 0x80000001ffffffff7fffffff00000001#128
-- `-2 ^ 31` times `-2 ^ 31` saturates, and the model faults.
#guard sqd 0x80000000800000008000000080000000#128 0x00000001000000018000000000000001#128 == none

#guard Instr.asm (.vop (.mul .v0 .v1 .v2)) == ["mul v0.4s, v1.4s, v2.4s"]
#guard Instr.asm (.vop (.mla .v0 .v1 .v2)) == ["mla v0.4s, v1.4s, v2.4s"]
#guard Instr.asm (.vop (.mls .v0 .v1 .v2)) == ["mls v0.4s, v1.4s, v2.4s"]
#guard Instr.asm (.vop (.sqdmulh .v0 .v1 .v2)) == ["sqdmulh v0.4s, v1.4s, v2.4s"]
#guard Instr.asm (.vop (.umin .v0 .v1 .v2)) == ["umin v0.4s, v1.4s, v2.4s"]
#guard isa.requires (.vop (.sqdmulh .v0 .v1 .v2)) == []


/-! ### 16-bit lanes (`.8h`) and their products

Computed as above, under `qemu-aarch64 -cpu max`. -/

#guard vrun 0 (.dup .h8 .v0 .x1) == some 0x09ec09ec09ec09ec09ec09ec09ec09ec#128
#guard vrun 0 (.ins .h8 .v0 0 .x1) == some 0x47be5543e684460b8caafc59aff909ec#128
#guard vrun 0 (.ins .h8 .v0 3 .x1) == some 0x47be5543e684460b09ecfc59aff91663#128
#guard vrun 0 (.ins .h8 .v0 7 .x1) == some 0x09ec5543e684460b8caafc59aff91663#128
#guard vrun 0 (.add .h8 .v0 .v1 .v2) == some 0xedee4514b4172e290090516bb87da0ed#128
#guard vrun 0 (.sub .h8 .v0 .v1 .v2) == some 0xbd78ddb0cf196b5f92fc6acfa8235875#128
#guard vrun 0 (.shift .shl .h8 .v0 .v1 0) == some 0xd5b39162c1984cc4c9c6de1db050fcb1#128
#guard vrun 0 (.shift .shl .h8 .v0 .v1 5) == some 0xb6602c403300988038c0c3a00a009620#128
#guard vrun 0 (.shift .ushr .h8 .v0 .v1 1) == some 0x6ad948b160cc266264e36f0e58287e58#128
#guard vrun 0 (.shift .ushr .h8 .v0 .v1 16) == some 0x00000000000000000000000000000000#128
#guard vrun 0 (.shift .sshr .h8 .v0 .v1 3) == some 0xfab6f22cf8330998f938fbc3f60aff96#128
#guard vrun 0 (.shift .sshr .h8 .v0 .v1 16) == some 0xffffffffffff0000ffffffffffffffff#128
#guard vrun 0 (.shift .sri .h8 .v0 .v1 4) == some 0x4d5b5916ec1944cc8c9cfde1ab051fcb#128
#guard vrun 0 (.shift .sli .h8 .v0 .v1 9) == some 0x67bec5433084880b8caa3a59a1f96263#128
#guard vrun 0 (.perm .zip1 .h8 .v0 .v1 .v2) == some 0x36cac9c6734ede1d082db050a43cfcb1#128
#guard vrun 0 (.perm .zip2 .h8 .v0 .v1 .v2) == some 0x183bd5b3b3b29162f27fc198e1654cc4#128
#guard vrun 0 (.perm .trn1 .h8 .v0 .v1 .v2) == some 0xb3b29162e1654cc4734ede1da43cfcb1#128
#guard vrun 0 (.perm .trn2 .h8 .v0 .v1 .v2) == some 0x183bd5b3f27fc19836cac9c6082db050#128
#guard vrun 0 (.perm .uzp1 .h8 .v0 .v1 .v2) == some 0xb3b2e165734ea43c91624cc4de1dfcb1#128
#guard vrun 0 (.perm .uzp2 .h8 .v0 .v1 .v2) == some 0x183bf27f36ca082dd5b3c198c9c6b050#128
#guard vrun 0 (.cmeq .h8 .v0 .v1 .v1) == some 0xffffffffffffffffffffffffffffffff#128
#guard vrun 0 (.cmeq .h8 .v0 .v1 .v2) == some 0x00000000000000000000000000000000#128
#guard vrun 0 (.dupE .h8 .v0 .v1 0) == some 0xfcb1fcb1fcb1fcb1fcb1fcb1fcb1fcb1#128
#guard vrun 0 (.dupE .h8 .v0 .v1 5) == some 0xc198c198c198c198c198c198c198c198#128
#guard vrun 0 (.insE .h8 .v0 2 .v1 6) == some 0x47be5543e684460b8caa9162aff91663#128
#guard vrun 0 (.mulH .mul .v0 .v1 .v2) == some 0x08419c24ba688d54fa3cb3d67e109d7c#128
#guard vrun 0 (.mulH .mul .v0 .v0 .v1) == some 0x3fda96a66260e46c457cc4152dd0ee73#128
#guard vrun 0 (.mulH .mla .v0 .v1 .v2) == some 0x4ffff167a0ecd35f86e6b02f2e09b3df#128
#guard vrun 0 (.mulH .mla .v0 .v0 .v1) == some 0x8798ebe948e42a77d226c06eddc904d6#128
#guard vrun 0 (.mulH .mls .v0 .v1 .v2) == some 0x3f7db91f2c1cb8b7926e488331e978e7#128
#guard vrun 0 (.mulH .mls .v0 .v0 .v1) == some 0x07e4be9d8424619f472e3844822927f0#128
#guard vrun 0 (.mulH .sqdmulh .v0 .v1 .v2) == some 0xf7fe41f10695eda5e8c9e179fae8025f#128
#guard vrun 0 (.mulH .sqdmulh .v0 .v0 .v1) == some 0xe84ab6510c6c2a0130dc00f731d2ff6b#128
#guard vrun 0 (.mulH .sqrdmulh .v0 .v1 .v2) == some 0xf7fe41f10695eda5e8cae179fae9025f#128
#guard vrun 0 (.mulH .sqrdmulh .v0 .v0 .v1) == some 0xe84ab6510c6d2a0230dd00f831d2ff6c#128

#guard vrun 1 (.dup .h8 .v0 .x1) == some 0x967b967b967b967b967b967b967b967b#128
#guard vrun 1 (.ins .h8 .v0 0 .x1) == some 0x55eadb18f6d1d81649d2bf3ef06d967b#128
#guard vrun 1 (.ins .h8 .v0 3 .x1) == some 0x55eadb18f6d1d816967bbf3ef06dbe6f#128
#guard vrun 1 (.ins .h8 .v0 7 .x1) == some 0x967bdb18f6d1d81649d2bf3ef06dbe6f#128
#guard vrun 1 (.add .h8 .v0 .v1 .v2) == some 0x13702f476333dff98e87d9f520e7f3b0#128
#guard vrun 1 (.sub .h8 .v0 .v1 .v2) == some 0xa2dc6ce90753b2ddb0b5982137a3d3d8#128
#guard vrun 1 (.shift .shl .h8 .v0 .v1 0) == some 0xdb26ce183543c96b9f9eb90b2c4563c4#128
#guard vrun 1 (.shift .shl .h8 .v0 .v1 5) == some 0x64c0c300a8602d60f3c0216088a07880#128
#guard vrun 1 (.shift .ushr .h8 .v0 .v1 1) == some 0x6d93670c1aa164b54fcf5c85162231e2#128
#guard vrun 1 (.shift .ushr .h8 .v0 .v1 16) == some 0x00000000000000000000000000000000#128
#guard vrun 1 (.shift .sshr .h8 .v0 .v1 3) == some 0xfb64f9c306a8f92df3f3f72105880c78#128
#guard vrun 1 (.shift .sshr .h8 .v0 .v1 16) == some 0xffffffff0000ffffffffffff00000000#128
#guard vrun 1 (.shift .sri .h8 .v0 .v1 4) == some 0x5db2dce1f354dc9649f9bb90f2c4b63c#128
#guard vrun 1 (.shift .sli .h8 .v0 .v1 9) == some 0x4dea311886d1d6163dd2173e8a6d886f#128
#guard vrun 1 (.perm .zip1 .h8 .v0 .v1 .v2) == some 0xeee99f9e20eab90bf4a22c458fec63c4#128
#guard vrun 1 (.perm .zip2 .h8 .v0 .v1 .v2) == some 0x384adb26612fce182df03543168ec96b#128
#guard vrun 1 (.perm .trn1 .h8 .v0 .v1 .v2) == some 0x612fce18168ec96b20eab90b8fec63c4#128
#guard vrun 1 (.perm .trn2 .h8 .v0 .v1 .v2) == some 0x384adb262df03543eee99f9ef4a22c45#128
#guard vrun 1 (.perm .uzp1 .h8 .v0 .v1 .v2) == some 0x612f168e20ea8fecce18c96bb90b63c4#128
#guard vrun 1 (.perm .uzp2 .h8 .v0 .v1 .v2) == some 0x384a2df0eee9f4a2db2635439f9e2c45#128
#guard vrun 1 (.cmeq .h8 .v0 .v1 .v1) == some 0xffffffffffffffffffffffffffffffff#128
#guard vrun 1 (.cmeq .h8 .v0 .v1 .v2) == some 0x00000000000000000000000000000000#128
#guard vrun 1 (.dupE .h8 .v0 .v1 0) == some 0x63c463c463c463c463c463c463c463c4#128
#guard vrun 1 (.dupE .h8 .v0 .v1 5) == some 0x35433543354335433543354335433543#128
#guard vrun 1 (.insE .h8 .v0 2 .v1 6) == some 0x55eadb18f6d1d81649d2ce18f06dbe6f#128
#guard vrun 1 (.mulH .mul .v0 .v1 .v2) == some 0xa8fcee68b5d0eb5a2ace840ec7aa74b0#128
#guard vrun 1 (.mulH .mul .v0 .v0 .v1) == some 0xeebcda40ddb39732fd9c05aa8961b9fc#128
#guard vrun 1 (.mulH .mla .v0 .v1 .v2) == some 0xfee6c980aca1c37074a0434cb817331f#128
#guard vrun 1 (.mulH .mla .v0 .v0 .v1) == some 0x44a6b558d4846f48476ec4e879ce786b#128
#guard vrun 1 (.mulH .mls .v0 .v1 .v2) == some 0xaceeecb04101ecbc1f043b3028c349bf#128
#guard vrun 1 (.mulH .mls .v0 .v0 .v1) == some 0x672e00d8191e40e44c36b994670c0473#128
#guard vrun 1 (.mulH .sqdmulh .v0 .v1 .v2) == some 0xefcbda1b131df6610cdeedc1fc11a8a4#128
#guard vrun 1 (.mulH .sqdmulh .v0 .v0 .v1) == some 0xe7430e63fc2d1105c86923e6fa9dcce5#128
#guard vrun 1 (.mulH .sqrdmulh .v0 .v1 .v2) == some 0xefcbda1c131df6620cdeedc1fc12a8a5#128
#guard vrun 1 (.mulH .sqrdmulh .v0 .v0 .v1) == some 0xe7440e64fc2e1105c86a23e6fa9dcce5#128

#guard Instr.asm (.vop (.dup .h8 .v0 .x1)) == ["dup v0.8h, w1"]
#guard Instr.asm (.vop (.ins .h8 .v0 0 .x1)) == ["mov v0.h[0], w1"]
#guard Instr.asm (.vop (.ins .h8 .v0 3 .x1)) == ["mov v0.h[3], w1"]
#guard Instr.asm (.vop (.ins .h8 .v0 7 .x1)) == ["mov v0.h[7], w1"]
#guard Instr.asm (.vop (.add .h8 .v0 .v1 .v2)) == ["add v0.8h, v1.8h, v2.8h"]
#guard Instr.asm (.vop (.sub .h8 .v0 .v1 .v2)) == ["sub v0.8h, v1.8h, v2.8h"]
#guard Instr.asm (.vop (.shift .shl .h8 .v0 .v1 0)) == ["shl v0.8h, v1.8h, #0"]
#guard Instr.asm (.vop (.shift .shl .h8 .v0 .v1 5)) == ["shl v0.8h, v1.8h, #5"]
#guard Instr.asm (.vop (.shift .ushr .h8 .v0 .v1 1)) == ["ushr v0.8h, v1.8h, #1"]
#guard Instr.asm (.vop (.shift .ushr .h8 .v0 .v1 16)) == ["ushr v0.8h, v1.8h, #16"]
#guard Instr.asm (.vop (.shift .sshr .h8 .v0 .v1 3)) == ["sshr v0.8h, v1.8h, #3"]
#guard Instr.asm (.vop (.shift .sshr .h8 .v0 .v1 16)) == ["sshr v0.8h, v1.8h, #16"]
#guard Instr.asm (.vop (.shift .sri .h8 .v0 .v1 4)) == ["sri v0.8h, v1.8h, #4"]
#guard Instr.asm (.vop (.shift .sli .h8 .v0 .v1 9)) == ["sli v0.8h, v1.8h, #9"]
#guard Instr.asm (.vop (.perm .zip1 .h8 .v0 .v1 .v2)) == ["zip1 v0.8h, v1.8h, v2.8h"]
#guard Instr.asm (.vop (.perm .zip2 .h8 .v0 .v1 .v2)) == ["zip2 v0.8h, v1.8h, v2.8h"]
#guard Instr.asm (.vop (.perm .trn1 .h8 .v0 .v1 .v2)) == ["trn1 v0.8h, v1.8h, v2.8h"]
#guard Instr.asm (.vop (.perm .trn2 .h8 .v0 .v1 .v2)) == ["trn2 v0.8h, v1.8h, v2.8h"]
#guard Instr.asm (.vop (.perm .uzp1 .h8 .v0 .v1 .v2)) == ["uzp1 v0.8h, v1.8h, v2.8h"]
#guard Instr.asm (.vop (.perm .uzp2 .h8 .v0 .v1 .v2)) == ["uzp2 v0.8h, v1.8h, v2.8h"]
#guard Instr.asm (.vop (.cmeq .h8 .v0 .v1 .v1)) == ["cmeq v0.8h, v1.8h, v1.8h"]
#guard Instr.asm (.vop (.cmeq .h8 .v0 .v1 .v2)) == ["cmeq v0.8h, v1.8h, v2.8h"]
#guard Instr.asm (.vop (.dupE .h8 .v0 .v1 0)) == ["dup v0.8h, v1.h[0]"]
#guard Instr.asm (.vop (.dupE .h8 .v0 .v1 5)) == ["dup v0.8h, v1.h[5]"]
#guard Instr.asm (.vop (.insE .h8 .v0 2 .v1 6)) == ["mov v0.h[2], v1.h[6]"]
#guard Instr.asm (.vop (.mulH .mul .v0 .v1 .v2)) == ["mul v0.8h, v1.8h, v2.8h"]
#guard Instr.asm (.vop (.mulH .mul .v0 .v0 .v1)) == ["mul v0.8h, v0.8h, v1.8h"]
#guard Instr.asm (.vop (.mulH .mla .v0 .v1 .v2)) == ["mla v0.8h, v1.8h, v2.8h"]
#guard Instr.asm (.vop (.mulH .mla .v0 .v0 .v1)) == ["mla v0.8h, v0.8h, v1.8h"]
#guard Instr.asm (.vop (.mulH .mls .v0 .v1 .v2)) == ["mls v0.8h, v1.8h, v2.8h"]
#guard Instr.asm (.vop (.mulH .mls .v0 .v0 .v1)) == ["mls v0.8h, v0.8h, v1.8h"]
#guard Instr.asm (.vop (.mulH .sqdmulh .v0 .v1 .v2)) == ["sqdmulh v0.8h, v1.8h, v2.8h"]
#guard Instr.asm (.vop (.mulH .sqdmulh .v0 .v0 .v1)) == ["sqdmulh v0.8h, v0.8h, v1.8h"]
#guard Instr.asm (.vop (.mulH .sqrdmulh .v0 .v1 .v2)) == ["sqrdmulh v0.8h, v1.8h, v2.8h"]
#guard Instr.asm (.vop (.mulH .sqrdmulh .v0 .v0 .v1)) == ["sqrdmulh v0.8h, v0.8h, v1.8h"]
#guard isa.requires (.vop (.mulH .sqrdmulh .v0 .v1 .v2)) == []
/- Both lanes `-2^15`: SQDMULH and SQRDMULH saturate there, which the model makes a fault. -/
#guard (VOp.eval { s 0 with v := fun _ => 0x8000#128 } (.mulH .sqdmulh .v0 .v1 .v2)).isNone
#guard (VOp.eval { s 0 with v := fun _ => 0x8000#128 } (.mulH .sqrdmulh .v0 .v1 .v2)).isNone


/-! ### CMHI, CMHS, ADDV and UADDLV

Computed as above, under `qemu-aarch64 -cpu max`; the printed text was also
assembled by `llvm-mc -triple=aarch64`. Each comparison is run with its
sources both ways round, against itself (CMHI all zeros, CMHS all ones), and
with the destination as a source. ADDV and UADDLV write a scalar register:
the rest of `v0`, which held the input, is zero, also when `v0` is the
source. -/

#guard vrun 0 (.cmp .hi .b16 .v0 .v1 .v2) == some 0xffff000000ff00ffff00ff00ffffffff#128
#guard vrun 0 (.cmp .hi .b16 .v0 .v2 .v1) == some 0x0000ffffff00ff0000ff00ff00000000#128
#guard vrun 0 (.cmp .hi .b16 .v0 .v1 .v1) == some 0x00000000000000000000000000000000#128
#guard vrun 0 (.cmp .hi .b16 .v0 .v0 .v3) == some 0xffffffffffffff00ffffffffffff00ff#128
#guard vrun 0 (.cmp .hs .b16 .v0 .v1 .v2) == some 0xffff000000ff00ffff00ff00ffffffff#128
#guard vrun 0 (.cmp .hs .b16 .v0 .v2 .v1) == some 0x0000ffffff00ff0000ff00ff00000000#128
#guard vrun 0 (.cmp .hs .b16 .v0 .v1 .v1) == some 0xffffffffffffffffffffffffffffffff#128
#guard vrun 0 (.cmp .hs .b16 .v0 .v0 .v3) == some 0xffffffffffffff00ffffffffffffffff#128
#guard vrun 0 (.cmp .hi .h8 .v0 .v1 .v2) == some 0xffff000000000000ffffffffffffffff#128
#guard vrun 0 (.cmp .hi .h8 .v0 .v2 .v1) == some 0x0000ffffffffffff0000000000000000#128
#guard vrun 0 (.cmp .hi .h8 .v0 .v1 .v1) == some 0x00000000000000000000000000000000#128
#guard vrun 0 (.cmp .hi .h8 .v0 .v0 .v3) == some 0xffffffffffffffffffffffffffffffff#128
#guard vrun 0 (.cmp .hs .h8 .v0 .v1 .v2) == some 0xffff000000000000ffffffffffffffff#128
#guard vrun 0 (.cmp .hs .h8 .v0 .v2 .v1) == some 0x0000ffffffffffff0000000000000000#128
#guard vrun 0 (.cmp .hs .h8 .v0 .v1 .v1) == some 0xffffffffffffffffffffffffffffffff#128
#guard vrun 0 (.cmp .hs .h8 .v0 .v0 .v3) == some 0xffffffffffffffffffffffffffffffff#128
#guard vrun 0 (.cmp .hi .s4 .v0 .v1 .v2) == some 0xffffffff00000000ffffffffffffffff#128
#guard vrun 0 (.cmp .hi .s4 .v0 .v2 .v1) == some 0x00000000ffffffff0000000000000000#128
#guard vrun 0 (.cmp .hi .s4 .v0 .v1 .v1) == some 0x00000000000000000000000000000000#128
#guard vrun 0 (.cmp .hi .s4 .v0 .v0 .v3) == some 0xffffffffffffffffffffffffffffffff#128
#guard vrun 0 (.cmp .hs .s4 .v0 .v1 .v2) == some 0xffffffff00000000ffffffffffffffff#128
#guard vrun 0 (.cmp .hs .s4 .v0 .v2 .v1) == some 0x00000000ffffffff0000000000000000#128
#guard vrun 0 (.cmp .hs .s4 .v0 .v1 .v1) == some 0xffffffffffffffffffffffffffffffff#128
#guard vrun 0 (.cmp .hs .s4 .v0 .v0 .v3) == some 0xffffffffffffffffffffffffffffffff#128
#guard vrun 0 (.cmp .hi .d2 .v0 .v1 .v2) == some 0xffffffffffffffffffffffffffffffff#128
#guard vrun 0 (.cmp .hi .d2 .v0 .v2 .v1) == some 0x00000000000000000000000000000000#128
#guard vrun 0 (.cmp .hi .d2 .v0 .v1 .v1) == some 0x00000000000000000000000000000000#128
#guard vrun 0 (.cmp .hi .d2 .v0 .v0 .v3) == some 0xffffffffffffffffffffffffffffffff#128
#guard vrun 0 (.cmp .hs .d2 .v0 .v1 .v2) == some 0xffffffffffffffffffffffffffffffff#128
#guard vrun 0 (.cmp .hs .d2 .v0 .v2 .v1) == some 0x00000000000000000000000000000000#128
#guard vrun 0 (.cmp .hs .d2 .v0 .v1 .v1) == some 0xffffffffffffffffffffffffffffffff#128
#guard vrun 0 (.cmp .hs .d2 .v0 .v0 .v3) == some 0xffffffffffffffffffffffffffffffff#128
#guard vrun 0 (.addv .b16 .v0 .v1) == some 0x0000000000000000000000000000001b#128
#guard vrun 0 (.addv .b16 .v0 .v0) == some 0x00000000000000000000000000000004#128
#guard vrun 0 (.uaddlv .b16 .v0 .v1) == some 0x00000000000000000000000000000a1b#128
#guard vrun 0 (.uaddlv .b16 .v0 .v0) == some 0x00000000000000000000000000000804#128
#guard vrun 0 (.addv .h8 .v0 .v1) == some 0x0000000000000000000000000000ca55#128
#guard vrun 0 (.addv .h8 .v0 .v0) == some 0x000000000000000000000000000018ef#128
#guard vrun 0 (.uaddlv .h8 .v0 .v1) == some 0x0000000000000000000000000005ca55#128
#guard vrun 0 (.uaddlv .h8 .v0 .v0) == some 0x000000000000000000000000000418ef#128
#guard vrun 0 (.addv .s4 .v0 .v1) == some 0x0000000000000000000000001163b8f4#128
#guard vrun 0 (.addv .s4 .v0 .v0) == some 0x0000000000000000000000006ae6ae0a#128
#guard vrun 0 (.uaddlv .s4 .v0 .v1) == some 0x0000000000000000000000031163b8f4#128
#guard vrun 0 (.uaddlv .s4 .v0 .v0) == some 0x0000000000000000000000026ae6ae0a#128
#guard vrun 1 (.cmp .hi .b16 .v0 .v1 .v2) == some 0xff00ff00ff00ff000000ff0000000000#128
#guard vrun 1 (.cmp .hi .b16 .v0 .v2 .v1) == some 0x00ff00ff00ff00ffffff00ffffffffff#128
#guard vrun 1 (.cmp .hi .b16 .v0 .v1 .v1) == some 0x00000000000000000000000000000000#128
#guard vrun 1 (.cmp .hi .b16 .v0 .v0 .v3) == some 0xffffffffffffff00ffffffffffffffff#128
#guard vrun 1 (.cmp .hs .b16 .v0 .v1 .v2) == some 0xff00ff00ff00ff000000ff0000000000#128
#guard vrun 1 (.cmp .hs .b16 .v0 .v2 .v1) == some 0x00ff00ff00ff00ffffff00ffffffffff#128
#guard vrun 1 (.cmp .hs .b16 .v0 .v1 .v1) == some 0xffffffffffffffffffffffffffffffff#128
#guard vrun 1 (.cmp .hs .b16 .v0 .v0 .v3) == some 0xffffffffffffffffffffffffffffffff#128
#guard vrun 1 (.cmp .hi .h8 .v0 .v1 .v2) == some 0xffffffffffffffff0000ffff00000000#128
#guard vrun 1 (.cmp .hi .h8 .v0 .v2 .v1) == some 0x0000000000000000ffff0000ffffffff#128
#guard vrun 1 (.cmp .hi .h8 .v0 .v1 .v1) == some 0x00000000000000000000000000000000#128
#guard vrun 1 (.cmp .hi .h8 .v0 .v0 .v3) == some 0xffffffffffffffffffffffffffffffff#128
#guard vrun 1 (.cmp .hs .h8 .v0 .v1 .v2) == some 0xffffffffffffffff0000ffff00000000#128
#guard vrun 1 (.cmp .hs .h8 .v0 .v2 .v1) == some 0x0000000000000000ffff0000ffffffff#128
#guard vrun 1 (.cmp .hs .h8 .v0 .v1 .v1) == some 0xffffffffffffffffffffffffffffffff#128
#guard vrun 1 (.cmp .hs .h8 .v0 .v0 .v3) == some 0xffffffffffffffffffffffffffffffff#128
#guard vrun 1 (.cmp .hi .s4 .v0 .v1 .v2) == some 0xffffffffffffffff0000000000000000#128
#guard vrun 1 (.cmp .hi .s4 .v0 .v2 .v1) == some 0x0000000000000000ffffffffffffffff#128
#guard vrun 1 (.cmp .hi .s4 .v0 .v1 .v1) == some 0x00000000000000000000000000000000#128
#guard vrun 1 (.cmp .hi .s4 .v0 .v0 .v3) == some 0xffffffffffffffffffffffffffffffff#128
#guard vrun 1 (.cmp .hs .s4 .v0 .v1 .v2) == some 0xffffffffffffffff0000000000000000#128
#guard vrun 1 (.cmp .hs .s4 .v0 .v2 .v1) == some 0x0000000000000000ffffffffffffffff#128
#guard vrun 1 (.cmp .hs .s4 .v0 .v1 .v1) == some 0xffffffffffffffffffffffffffffffff#128
#guard vrun 1 (.cmp .hs .s4 .v0 .v0 .v3) == some 0xffffffffffffffffffffffffffffffff#128
#guard vrun 1 (.cmp .hi .d2 .v0 .v1 .v2) == some 0xffffffffffffffff0000000000000000#128
#guard vrun 1 (.cmp .hi .d2 .v0 .v2 .v1) == some 0x0000000000000000ffffffffffffffff#128
#guard vrun 1 (.cmp .hi .d2 .v0 .v1 .v1) == some 0x00000000000000000000000000000000#128
#guard vrun 1 (.cmp .hi .d2 .v0 .v0 .v3) == some 0xffffffffffffffffffffffffffffffff#128
#guard vrun 1 (.cmp .hs .d2 .v0 .v1 .v2) == some 0xffffffffffffffff0000000000000000#128
#guard vrun 1 (.cmp .hs .d2 .v0 .v2 .v1) == some 0x0000000000000000ffffffffffffffff#128
#guard vrun 1 (.cmp .hs .d2 .v0 .v1 .v1) == some 0xffffffffffffffffffffffffffffffff#128
#guard vrun 1 (.cmp .hs .d2 .v0 .v0 .v3) == some 0xffffffffffffffffffffffffffffffff#128
#guard vrun 1 (.addv .b16 .v0 .v1) == some 0x0000000000000000000000000000002c#128
#guard vrun 1 (.addv .b16 .v0 .v0) == some 0x00000000000000000000000000000089#128
#guard vrun 1 (.uaddlv .b16 .v0 .v1) == some 0x0000000000000000000000000000072c#128
#guard vrun 1 (.uaddlv .b16 .v0 .v0) == some 0x00000000000000000000000000000989#128
#guard vrun 1 (.addv .h8 .v0 .v1) == some 0x0000000000000000000000000000909e#128
#guard vrun 1 (.addv .h8 .v0 .v0) == some 0x0000000000000000000000000000b7d5#128
#guard vrun 1 (.uaddlv .h8 .v0 .v1) == some 0x0000000000000000000000000004909e#128
#guard vrun 1 (.uaddlv .h8 .v0 .v0) == some 0x0000000000000000000000000005b7d5#128
#guard vrun 1 (.addv .s4 .v0 .v1) == some 0x000000000000000000000000dc4eb452#128
#guard vrun 1 (.addv .s4 .v0 .v0) == some 0x00000000000000000000000086fd30db#128
#guard vrun 1 (.uaddlv .s4 .v0 .v1) == some 0x000000000000000000000001dc4eb452#128
#guard vrun 1 (.uaddlv .s4 .v0 .v0) == some 0x00000000000000000000000286fd30db#128

#guard Instr.asm (.vop (.cmp .hi .b16 .v0 .v1 .v2)) == ["cmhi v0.16b, v1.16b, v2.16b"]
#guard Instr.asm (.vop (.cmp .hi .b16 .v0 .v2 .v1)) == ["cmhi v0.16b, v2.16b, v1.16b"]
#guard Instr.asm (.vop (.cmp .hi .b16 .v0 .v1 .v1)) == ["cmhi v0.16b, v1.16b, v1.16b"]
#guard Instr.asm (.vop (.cmp .hi .b16 .v0 .v0 .v3)) == ["cmhi v0.16b, v0.16b, v3.16b"]
#guard Instr.asm (.vop (.cmp .hs .b16 .v0 .v1 .v2)) == ["cmhs v0.16b, v1.16b, v2.16b"]
#guard Instr.asm (.vop (.cmp .hs .b16 .v0 .v2 .v1)) == ["cmhs v0.16b, v2.16b, v1.16b"]
#guard Instr.asm (.vop (.cmp .hs .b16 .v0 .v1 .v1)) == ["cmhs v0.16b, v1.16b, v1.16b"]
#guard Instr.asm (.vop (.cmp .hs .b16 .v0 .v0 .v3)) == ["cmhs v0.16b, v0.16b, v3.16b"]
#guard Instr.asm (.vop (.cmp .hi .h8 .v0 .v1 .v2)) == ["cmhi v0.8h, v1.8h, v2.8h"]
#guard Instr.asm (.vop (.cmp .hi .h8 .v0 .v2 .v1)) == ["cmhi v0.8h, v2.8h, v1.8h"]
#guard Instr.asm (.vop (.cmp .hi .h8 .v0 .v1 .v1)) == ["cmhi v0.8h, v1.8h, v1.8h"]
#guard Instr.asm (.vop (.cmp .hi .h8 .v0 .v0 .v3)) == ["cmhi v0.8h, v0.8h, v3.8h"]
#guard Instr.asm (.vop (.cmp .hs .h8 .v0 .v1 .v2)) == ["cmhs v0.8h, v1.8h, v2.8h"]
#guard Instr.asm (.vop (.cmp .hs .h8 .v0 .v2 .v1)) == ["cmhs v0.8h, v2.8h, v1.8h"]
#guard Instr.asm (.vop (.cmp .hs .h8 .v0 .v1 .v1)) == ["cmhs v0.8h, v1.8h, v1.8h"]
#guard Instr.asm (.vop (.cmp .hs .h8 .v0 .v0 .v3)) == ["cmhs v0.8h, v0.8h, v3.8h"]
#guard Instr.asm (.vop (.cmp .hi .s4 .v0 .v1 .v2)) == ["cmhi v0.4s, v1.4s, v2.4s"]
#guard Instr.asm (.vop (.cmp .hi .s4 .v0 .v2 .v1)) == ["cmhi v0.4s, v2.4s, v1.4s"]
#guard Instr.asm (.vop (.cmp .hi .s4 .v0 .v1 .v1)) == ["cmhi v0.4s, v1.4s, v1.4s"]
#guard Instr.asm (.vop (.cmp .hi .s4 .v0 .v0 .v3)) == ["cmhi v0.4s, v0.4s, v3.4s"]
#guard Instr.asm (.vop (.cmp .hs .s4 .v0 .v1 .v2)) == ["cmhs v0.4s, v1.4s, v2.4s"]
#guard Instr.asm (.vop (.cmp .hs .s4 .v0 .v2 .v1)) == ["cmhs v0.4s, v2.4s, v1.4s"]
#guard Instr.asm (.vop (.cmp .hs .s4 .v0 .v1 .v1)) == ["cmhs v0.4s, v1.4s, v1.4s"]
#guard Instr.asm (.vop (.cmp .hs .s4 .v0 .v0 .v3)) == ["cmhs v0.4s, v0.4s, v3.4s"]
#guard Instr.asm (.vop (.cmp .hi .d2 .v0 .v1 .v2)) == ["cmhi v0.2d, v1.2d, v2.2d"]
#guard Instr.asm (.vop (.cmp .hi .d2 .v0 .v2 .v1)) == ["cmhi v0.2d, v2.2d, v1.2d"]
#guard Instr.asm (.vop (.cmp .hi .d2 .v0 .v1 .v1)) == ["cmhi v0.2d, v1.2d, v1.2d"]
#guard Instr.asm (.vop (.cmp .hi .d2 .v0 .v0 .v3)) == ["cmhi v0.2d, v0.2d, v3.2d"]
#guard Instr.asm (.vop (.cmp .hs .d2 .v0 .v1 .v2)) == ["cmhs v0.2d, v1.2d, v2.2d"]
#guard Instr.asm (.vop (.cmp .hs .d2 .v0 .v2 .v1)) == ["cmhs v0.2d, v2.2d, v1.2d"]
#guard Instr.asm (.vop (.cmp .hs .d2 .v0 .v1 .v1)) == ["cmhs v0.2d, v1.2d, v1.2d"]
#guard Instr.asm (.vop (.cmp .hs .d2 .v0 .v0 .v3)) == ["cmhs v0.2d, v0.2d, v3.2d"]
#guard Instr.asm (.vop (.addv .b16 .v0 .v1)) == ["addv b0, v1.16b"]
#guard Instr.asm (.vop (.addv .b16 .v0 .v0)) == ["addv b0, v0.16b"]
#guard Instr.asm (.vop (.uaddlv .b16 .v0 .v1)) == ["uaddlv h0, v1.16b"]
#guard Instr.asm (.vop (.uaddlv .b16 .v0 .v0)) == ["uaddlv h0, v0.16b"]
#guard Instr.asm (.vop (.addv .h8 .v0 .v1)) == ["addv h0, v1.8h"]
#guard Instr.asm (.vop (.addv .h8 .v0 .v0)) == ["addv h0, v0.8h"]
#guard Instr.asm (.vop (.uaddlv .h8 .v0 .v1)) == ["uaddlv s0, v1.8h"]
#guard Instr.asm (.vop (.uaddlv .h8 .v0 .v0)) == ["uaddlv s0, v0.8h"]
#guard Instr.asm (.vop (.addv .s4 .v0 .v1)) == ["addv s0, v1.4s"]
#guard Instr.asm (.vop (.addv .s4 .v0 .v0)) == ["addv s0, v0.4s"]
#guard Instr.asm (.vop (.uaddlv .s4 .v0 .v1)) == ["uaddlv d0, v1.4s"]
#guard Instr.asm (.vop (.uaddlv .s4 .v0 .v0)) == ["uaddlv d0, v0.4s"]
#guard isa.requires (.vop (.cmp .hi .b16 .v0 .v1 .v2)) == []
#guard isa.requires (.vop (.addv .b16 .v0 .v1)) == []
#guard isa.requires (.vop (.uaddlv .s4 .v0 .v1)) == []
/- `.2d` has no ADDV or UADDLV (`size = '11'` is reserved): the model faults. -/
#guard vrun 0 (.addv .d2 .v0 .v1) == none
#guard vrun 0 (.uaddlv .d2 .v0 .v1) == none

/-! ### MUL, MLA, MLS, SQDMULH and SQRDMULH (by element), 16-bit lanes

Computed as above, under `qemu-aarch64 -cpu max`; the printed text was also
assembled by `llvm-mc -triple=aarch64`, which rejects an element register
above `v15` (`Rm` has four bits for 16-bit elements). The element register
is also the destination (`v0`), and the destination is also a source. -/

#guard vrun 0 (.mulHE .mul .v0 .v1 .v2 0) == some 0xc1f4daf8bfa08df02268a2cc92c09d7c#128
#guard vrun 0 (.mulHE .mul .v0 .v1 .v2 3) == some 0x613e6354d1f0eaa8fa3c60e2ff20b9aa#128
#guard vrun 0 (.mulHE .mul .v0 .v1 .v2 7) == some 0x0841b196de08112c10a2e8af2270d4cb#128
#guard vrun 0 (.mulHE .mul .v0 .v1 .v0 5) == some 0x024c02886260ad10ee1894f4c9405144#128
#guard vrun 0 (.mulHE .mul .v0 .v0 .v1 6) == some 0x14bc96a602880b36231403126652a4e6#128
#guard vrun 0 (.mulHE .mla .v0 .v1 .v2 0) == some 0x09b2303ba624d3fbaf129f2542b9b3df#128
#guard vrun 0 (.mulHE .mla .v0 .v1 .v2 3) == some 0xa8fcb897b87430b386e65d3baf19d00d#128
#guard vrun 0 (.mulHE .mla .v0 .v1 .v2 7) == some 0x4fff06d9c48c57379d4ce508d269eb2e#128
#guard vrun 0 (.mulHE .mla .v0 .v1 .v0 5) == some 0x4a0a57cb48e4f31b7ac2914d793967a7#128
#guard vrun 0 (.mulHE .mla .v0 .v0 .v1 6) == some 0x5c7aebe9e90c5141afbeff6b164bbb49#128
#guard vrun 0 (.mulHE .mls .v0 .v1 .v2 0) == some 0x85ca7a4b26e4b81b6a42598d1d3978e7#128
#guard vrun 0 (.mulHE .mls .v0 .v1 .v2 3) == some 0xe680f1ef14945b63926e9b77b0d95cb9#128
#guard vrun 0 (.mulHE .mls .v0 .v1 .v2 7) == some 0x3f7da3ad087c34df7c0813aa8d894198#128
#guard vrun 0 (.mulHE .mls .v0 .v1 .v0 5) == some 0x457252bb842498fb9e926765e6b9c51f#128
#guard vrun 0 (.mulHE .mls .v0 .v0 .v1 6) == some 0x3302be9de3fc3ad56996f94749a7717d#128
#guard vrun 0 (.mulHE .sqdmulh .v0 .v1 .v2 0) == some 0x1e534f4d2cbdc8f726e0184b3921025f#128
#guard vrun 0 (.mulHE .sqdmulh .v0 .v1 .v2 3) == some 0xede4d0a6e54920dbe8c9f17edde3fe95#128
#guard vrun 0 (.mulHE .sqdmulh .v0 .v1 .v2 7) == some 0xf7feeb0ff42f0e88f5bcf995f0eaff5f#128
#guard vrun 0 (.mulHE .sqdmulh .v0 .v1 .v0 5) == some 0x086c16060c6cf0b70acb06bf0fdd00a8#128
#guard vrun 0 (.mulHE .sqdmulh .v0 .v0 .v1 6) == some 0xc200b6511606c37863ac03284528eca7#128
#guard vrun 0 (.mulHE .sqrdmulh .v0 .v1 .v2 0) == some 0x1e544f4e2cbdc8f726e0184b3921025f#128
#guard vrun 0 (.mulHE .sqrdmulh .v0 .v1 .v2 3) == some 0xede5d0a7e54a20dce8caf17fdde4fe95#128
#guard vrun 0 (.mulHE .sqrdmulh .v0 .v1 .v2 7) == some 0xf7feeb0ff4300e88f5bcf996f0eaff60#128
#guard vrun 0 (.mulHE .sqrdmulh .v0 .v1 .v0 5) == some 0x086c16060c6df0b70acc06bf0fde00a9#128
#guard vrun 0 (.mulHE .sqrdmulh .v0 .v0 .v1 6) == some 0xc200b6511606c37863ac03284529eca7#128
#guard vrun 1 (.mulHE .mul .v0 .v1 .v2 0) == some 0x4108662086c473a467a8bb245a9c74b0#128
#guard vrun 1 (.mulHE .mul .v0 .v1 .v2 3) == some 0xc996e3d8c3fbcc632acea50370cd0564#128
#guard vrun 1 (.mulHE .mul .v0 .v1 .v2 7) == some 0xa8fcd2f00d5ea0eeb3ace52ee3f2b6a8#128
#guard vrun 1 (.mulHE .mul .v0 .v1 .v0 5) == some 0x6e065198ddb3425b23fea3fb7255cb04#128
#guard vrun 1 (.mulHE .mul .v0 .v0 .v1 6) == some 0x59f0da405198f610e7b0d1d040382c68#128
#guard vrun 1 (.mulHE .mla .v0 .v1 .v2 0) == some 0x96f241387d954bbab17a7a624b09331f#128
#guard vrun 1 (.mulHE .mla .v0 .v1 .v2 3) == some 0x1f80bef0bacca47974a06441613ac3d3#128
#guard vrun 1 (.mulHE .mla .v0 .v1 .v2 7) == some 0xfee6ae08042f7904fd7ea46cd45f7517#128
#guard vrun 1 (.mulHE .mla .v0 .v1 .v0 5) == some 0xc3f02cb0d4841a716dd0633962c28973#128
#guard vrun 1 (.mulHE .mla .v0 .v0 .v1 6) == some 0xafdab5584869ce263182910e30a5ead7#128
#guard vrun 1 (.mulHE .mls .v0 .v1 .v2 0) == some 0x14e274f8700d6472e22a041a95d149bf#128
#guard vrun 1 (.mulHE .mls .v0 .v1 .v2 3) == some 0x8c54f74032d60bb31f041a3b7fa0b90b#128
#guard vrun 1 (.mulHE .mls .v0 .v1 .v2 7) == some 0xacee0828e97337289626da100c7b07c7#128
#guard vrun 1 (.mulHE .mls .v0 .v1 .v0 5) == some 0xe7e48980191e95bb25d41b437e18f36b#128
#guard vrun 1 (.mulHE .mls .v0 .v0 .v1 6) == some 0xfbfa00d8a539e2066222ed6eb0359207#128
#guard vrun 1 (.mulHE .sqdmulh .v0 .v1 .v2 0) == some 0x20442bb2d15d2fca54643e21d93ca8a4#128
#guard vrun 1 (.mulHE .sqdmulh .v0 .v1 .v2 3) == some 0x04eb06a9f8e307490cde0979fa16f2ae#128
#guard vrun 1 (.mulHE .sqdmulh .v0 .v1 .v2 7) == some 0xefcbea0d176ce7ffd59de0cb13772bdf#128
#guard vrun 1 (.mulHE .sqdmulh .v0 .v1 .v0 5) == some 0x02a40394fc2d03ea06ea0517fcd2f8d7#128
#guard vrun 1 (.mulHE .sqdmulh .v0 .v0 .v1 6) == some 0xde800e6303940f8fe337193f06121990#128
#guard vrun 1 (.mulHE .sqrdmulh .v0 .v1 .v2 0) == some 0x20452bb3d15d2fcb54653e21d93da8a5#128
#guard vrun 1 (.mulHE .sqrdmulh .v0 .v1 .v2 3) == some 0x04ec06aaf8e4074a0cde0979fa17f2ae#128
#guard vrun 1 (.mulHE .sqrdmulh .v0 .v1 .v2 7) == some 0xefcbea0e176ce7ffd59de0cc13782bdf#128
#guard vrun 1 (.mulHE .sqrdmulh .v0 .v1 .v0 5) == some 0x02a50395fc2e03eb06ea0517fcd3f8d8#128
#guard vrun 1 (.mulHE .sqrdmulh .v0 .v0 .v1 6) == some 0xde810e6403950f90e338194006131990#128

#guard Instr.asm (.vop (.mulHE .mul .v0 .v1 .v2 0)) == ["mul v0.8h, v1.8h, v2.h[0]"]
#guard Instr.asm (.vop (.mulHE .mul .v0 .v1 .v2 3)) == ["mul v0.8h, v1.8h, v2.h[3]"]
#guard Instr.asm (.vop (.mulHE .mul .v0 .v1 .v2 7)) == ["mul v0.8h, v1.8h, v2.h[7]"]
#guard Instr.asm (.vop (.mulHE .mul .v0 .v1 .v0 5)) == ["mul v0.8h, v1.8h, v0.h[5]"]
#guard Instr.asm (.vop (.mulHE .mul .v0 .v0 .v1 6)) == ["mul v0.8h, v0.8h, v1.h[6]"]
#guard Instr.asm (.vop (.mulHE .sqrdmulh .v0 .v1 .v15 3)) == ["sqrdmulh v0.8h, v1.8h, v15.h[3]"]

/- The index is below 8 and the element register one of `v0`–`v15`, or the
model faults; SQDMULH and SQRDMULH of `0x8000` by itself fault, as for the
vector forms. -/
#guard vrun 0 (.mulHE .mul .v0 .v1 .v2 8) == none
#guard vrun 0 (.mulHE .mul .v0 .v1 .v15 0) != none
#guard vrun 0 (.mulHE .mul .v0 .v1 .v16 0) == none
#guard (VOp.eval { s 0 with v := fun _ => 0x8000#128 } (.mulHE .sqdmulh .v0 .v1 .v2 0)).isNone
#guard (VOp.eval { s 0 with v := fun _ => 0x8000#128 } (.mulHE .sqrdmulh .v0 .v1 .v2 0)).isNone

end VG.Test.AArch64Simd
