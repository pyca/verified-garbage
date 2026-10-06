import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Pbkdf2.Scratch
import VerifiedGarbage.Proof.Framework.Arm.StackScratch

/-!
# PBKDF2 on ARMv7, with its working space on the stack

`vg_pbkdf2_hmac_<hash>` runs its `_scratch` form (`Instances.lean`,
`Sha256.lean`, `Sha224.lean`) in a frame that allocates the working space and
copies its three arguments passed on the stack (`c`, `out`, `out_len`)
(`Verified.stackScratch`): `pbkFramed`, for any instance, from the locality
of PBKDF2's pre- and postcondition (`Proof/Pbkdf2/Scratch.lean`). The frame
is `pbkFrame I` bytes: the working space, the copied arguments and the saved
registers, rounded up to a multiple of 32 bytes, which an ARM immediate
encodes. `pbkFrameSat` satisfies the precondition of the contract without
the working space.
-/

namespace VG.Proof.Pbkdf2.Whole.Arm

open VG.Arm

/-- The bytes of `pbkdf2`'s frame: its copy of its three stack arguments, the
saved registers and the working space, rounded up to a multiple of 32. -/
def pbkFrame (I : Spec.Hmac.Instance) : Nat := (12 + 8 + 8 * I.pbkdf2Scratch + 31) / 32 * 32

theorem pbkFramed {I : Spec.Hmac.Instance} {c : Prog isa} {bytes : Nat}
    (h : Verified Arm.target c (I.pbkdf2ScratchContract Arm.abi 24))
    (hb : Fits 3 bytes .u64 I.pbkdf2Scratch)
    (hsat : ∃ s, (I.pbkdf2Contract Arm.abi (24 + bytes)).pre s) :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch bytes 3 c)
      (I.pbkdf2Contract Arm.abi (24 + bytes)) :=
  Arm.Verified.stackScratch (sig := Spec.Pbkdf2.pbkdf2Sig) (nm := "scratch") (e := .u64)
    (n := I.pbkdf2Scratch) (pre := Spec.Pbkdf2.pbkdf2Pre I.S Arm.abi.ptrBits)
    (post := Spec.Pbkdf2.pbkdf2Post I.S Arm.abi.ptrBits) (wa := true) (stack := 24) (m := 3) h
    rfl rfl rfl hb
    (Pbkdf2.pbkdf2Pre_local I.S _) (Pbkdf2.pbkdf2Post_local I.S _) hsat

/-- A state satisfying `pbkdf2`'s precondition without the working space: an
empty password, salt and output, and `c = 1`; the stack arguments `1, 0x1200,
0` are at `0x8000`. -/
def pbkFrameSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r2 => 0x1100
    | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8000 then 0x01 else if a = 0x8005 then 0x12 else 0
  rd := [⟨0x1000, 0⟩, ⟨0x1100, 0⟩, ⟨0x8000, 12⟩]
  wr := [⟨0x1200, 0⟩]

theorem md5_pbkFrameSat :
    ∃ s, (Spec.Hmac.md5I.pbkdf2Contract Arm.abi (24 + pbkFrame Spec.Hmac.md5I)).pre s := by
  implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.md5I,
      Spec.Hmac.md5S, Spec.Hmac.md5, pbkFrame, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr]
    [pbkFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using pbkFrameSat

theorem sha1_pbkFrameSat :
    ∃ s, (Spec.Hmac.sha1I.pbkdf2Contract Arm.abi (24 + pbkFrame Spec.Hmac.sha1I)).pre s := by
  implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha1I,
      Spec.Hmac.sha1S, Spec.Hmac.sha1, pbkFrame, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr]
    [pbkFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using pbkFrameSat

theorem sha224_pbkFrameSat :
    ∃ s, (Spec.Hmac.sha224I.pbkdf2Contract Arm.abi (24 + pbkFrame Spec.Hmac.sha224I)).pre s := by
  implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha224I,
      Spec.Hmac.sha224S, Spec.Hmac.sha224, pbkFrame, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr]
    [pbkFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using pbkFrameSat

theorem sha256_pbkFrameSat :
    ∃ s, (Spec.Hmac.sha256I.pbkdf2Contract Arm.abi (24 + pbkFrame Spec.Hmac.sha256I)).pre s := by
  implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha256I,
      Spec.Hmac.sha256S, Spec.Hmac.sha256, pbkFrame, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr]
    [pbkFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using pbkFrameSat

theorem sha384_pbkFrameSat :
    ∃ s, (Spec.Hmac.sha384I.pbkdf2Contract Arm.abi (24 + pbkFrame Spec.Hmac.sha384I)).pre s := by
  implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha384I,
      Spec.Hmac.sha384S, Spec.Hmac.sha384, pbkFrame, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr]
    [pbkFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using pbkFrameSat

theorem sha512_pbkFrameSat :
    ∃ s, (Spec.Hmac.sha512I.pbkdf2Contract Arm.abi (24 + pbkFrame Spec.Hmac.sha512I)).pre s := by
  implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512I,
      Spec.Hmac.sha512S, Spec.Hmac.sha512, pbkFrame, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr]
    [pbkFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using pbkFrameSat

theorem sha512_224_pbkFrameSat :
    ∃ s, (Spec.Hmac.sha512_224I.pbkdf2Contract Arm.abi (24 + pbkFrame Spec.Hmac.sha512_224I)).pre s := by
  implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512_224I,
      Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, pbkFrame, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr]
    [pbkFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using pbkFrameSat

theorem sha512_256_pbkFrameSat :
    ∃ s, (Spec.Hmac.sha512_256I.pbkdf2Contract Arm.abi (24 + pbkFrame Spec.Hmac.sha512_256I)).pre s := by
  implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512_256I,
      Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, pbkFrame, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr]
    [pbkFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using pbkFrameSat

end VG.Proof.Pbkdf2.Whole.Arm
