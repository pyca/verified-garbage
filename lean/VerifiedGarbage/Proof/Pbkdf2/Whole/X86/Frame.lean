import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Pbkdf2.Scratch
import VerifiedGarbage.Proof.Framework.X86.StackScratch
import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface

/-!
# PBKDF2 on x86, with its working space on the stack

`vg_pbkdf2_hmac_<hash>` runs its `_scratch` form (`Instances.lean`, and the
SHA-256 backends' `Sha256.lean`) in a frame that allocates the working space
and copies the arguments passed on the stack (`Verified.stackScratch`):
`pbkFramed`, for any instance, from the locality of PBKDF2's pre- and
postcondition (`Proof/Pbkdf2/Scratch.lean`). `pbkFrameSat` satisfies the
precondition of the contract without the working space.

For a SHA-256 backend, `sha256_stack` and `sha224_stack` bound the stack the
code uses from what the backend proves of the functions it calls, and
`nosp_of_all` gives that it keeps `esp` from `Backend.pbkdf2Sp`.
-/

namespace VG.Proof.Pbkdf2.Whole.X86

open VG.X86
open VG.Proof.Sha256.X86.Variants (Backend)

/-- The bytes of `pbkdf2`'s frame: its return address, a copy of its seven
argument slots and the working space. -/
def pbkFrame (I : Spec.Hmac.Instance) : Nat := 8 + 28 + 8 * I.pbkdf2Scratch

theorem pbkFramed {I : Spec.Hmac.Instance} {c : Prog isa}
    (h : Verified X86.target c (I.pbkdf2ScratchContract X86.abi 76)) (hs : 8 * I.pbkdf2Scratch < 4060)
    (hsp : c.allInstrs (fun i => !Taint.clobbers i .esp) = true) (hd : stackUse c ≤ 76)
    (hsat : ∃ s, (I.pbkdf2Contract X86.abi (76 + pbkFrame I)).pre s) :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch (pbkFrame I) 7 c)
      (I.pbkdf2Contract X86.abi (76 + pbkFrame I)) :=
  X86.Verified.stackScratch (sig := Spec.Pbkdf2.pbkdf2Sig) (nm := "scratch") (e := .u64)
    (n := I.pbkdf2Scratch) (pre := Spec.Pbkdf2.pbkdf2Pre I.S X86.abi.ptrBits)
    (post := Spec.Pbkdf2.pbkdf2Post I.S X86.abi.ptrBits) (wa := true) (stack := 76)
    (bytes := pbkFrame I) h
    (by
      refine ⟨?_, by simp only [pbkFrame]; omega, by simp only [pbkFrame]; omega⟩
      change 8 + 4 * 7 + I.pbkdf2Scratch * 8 ≤ pbkFrame I
      simp only [pbkFrame]; omega)
    hsp hd (Pbkdf2.pbkdf2Pre_local I.S _) (Pbkdf2.pbkdf2Post_local I.S _) hsat rfl

/-- Memory holding the arguments `0x1000, 0, 0x1400, 0, 1, 0x1800, 0` of
`pbkdf2` at `0x6004`. -/
def pbkFrameMem : Mem := fun a =>
  if a = 0x6005 then 0x10 else if a = 0x600D then 0x14 else if a = 0x6014 then 1
  else if a = 0x6019 then 0x18 else 0

/-- A state satisfying `pbkdf2`'s precondition without the working space: an
empty password, salt and output, and `c = 1`, with the arguments writable. -/
def pbkFrameSat : State where
  gpr r := match r with
    | .esp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := pbkFrameMem
  rd := [⟨0x1000, 0⟩, ⟨0x1400, 0⟩]
  wr := [⟨0x1800, 0⟩, ⟨0x6004, 28⟩]

theorem clobbers_esp (i : Instr) : Taint.clobbers i .esp = isa.writesSp i := by
  cases i <;> rfl

theorem all_eq (p : Instr → Bool) (c : Prog isa) : c.all p = (VG.instrs c).all p := by
  induction c <;> simp_all [Code.all, VG.instrs, List.all_append, Bool.and_assoc]

/-- Code whose instructions never write `esp`, but by its frames, keeps it. -/
theorem nosp_of_all {c : Prog isa} (h : c.all (fun i => !isa.writesSp i) = true) : NoSp c := by
  intro i hi
  rw [all_eq, List.all_eq_true] at h
  rw [clobbers_esp]
  simpa using h i hi

/-- `c` writes `esp` only through its frames' pushes and pops, from no
instruction writing it but those. -/
theorem noEsp_of_all {c : Prog isa} (h : c.all (fun i => !isa.writesSp i) = true) :
    c.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq]
  exact List.all_eq_true.mpr fun i hi => by simp [nosp_of_all h i hi]

/-- PBKDF2-HMAC-SHA256 made with the backend `v` uses at most 76 bytes of
stack. -/
theorem sha256_stack (v : Backend) : stackUse v.F.pbkdf2 ≤ 76 := by
  have := v.stream.updSU; have := v.stream.finSU; have := v.initStack; have := v.finalizeStack; have := v.iterStack
  have hi : stackUse Impl.Sha256.X86.Stream.init ≤ 20 := by lit_decide
  simp only [Impl.Pbkdf2.Whole.X86.Fns.pbkdf2, Impl.Pbkdf2.Whole.X86.Fns.key,
    Impl.Pbkdf2.Whole.X86.Fns.hashKey, Impl.Pbkdf2.Whole.X86.Fns.setup, Impl.Pbkdf2.Whole.X86.Fns.block,
    Impl.Pbkdf2.Whole.X86.Fns.outLen, Impl.Pbkdf2.Whole.X86.Fns.outLoop, Impl.Pbkdf2.Stream.X86.copy,
    Impl.Pbkdf2.Stream.X86.Hash.callInit, Backend.F, Proof.Sha256.X86.Variants.pbkdf2Fns,
    Proof.Sha256.X86.Variants.fns, Proof.Sha256.X86.Variants.hmacHash, Proof.Pbkdf2.Md.X86.sha256M,
    stackUse, frameBytes, List.length_cons, List.length_nil, Nat.max_le] at *
  omega

/-- PBKDF2-HMAC-SHA224 made with the backend `v` uses at most 76 bytes of
stack. -/
theorem sha224_stack (v : Backend) : stackUse v.F224.pbkdf2 ≤ 76 := by
  have := v.stream.updSU; have := v.stream.finSU; have := v.init224Stack; have := v.finalize224Stack
  have := v.iter224Stack
  have hi : stackUse Impl.Sha256.X86.Stream.init224 ≤ 20 := by lit_decide
  simp only [Impl.Pbkdf2.Whole.X86.Fns.pbkdf2, Impl.Pbkdf2.Whole.X86.Fns.key,
    Impl.Pbkdf2.Whole.X86.Fns.hashKey, Impl.Pbkdf2.Whole.X86.Fns.setup, Impl.Pbkdf2.Whole.X86.Fns.block,
    Impl.Pbkdf2.Whole.X86.Fns.outLen, Impl.Pbkdf2.Whole.X86.Fns.outLoop, Impl.Pbkdf2.Stream.X86.copy,
    Impl.Pbkdf2.Stream.X86.Hash.callInit, Backend.F224, Proof.Sha256.X86.Variants.pbkdf2Fns224,
    Proof.Sha256.X86.Variants.fns224, Proof.Sha256.X86.Variants.hmacHash224,
    Proof.Pbkdf2.Md.X86.sha224M, stackUse, frameBytes, List.length_cons, List.length_nil,
    Nat.max_le] at *
  omega

theorem md5_pbkFrameSat :
    ∃ s, (Spec.Hmac.md5I.pbkdf2Contract X86.abi (76 + pbkFrame Spec.Hmac.md5I)).pre s := by
  implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.md5I,
      Spec.Hmac.md5S, Spec.Hmac.md5, pbkFrame, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [pbkFrameSat, pbkFrameMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using pbkFrameSat

theorem sha1_pbkFrameSat :
    ∃ s, (Spec.Hmac.sha1I.pbkdf2Contract X86.abi (76 + pbkFrame Spec.Hmac.sha1I)).pre s := by
  implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha1I,
      Spec.Hmac.sha1S, Spec.Hmac.sha1, pbkFrame, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [pbkFrameSat, pbkFrameMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using pbkFrameSat

theorem sha224_pbkFrameSat :
    ∃ s, (Spec.Hmac.sha224I.pbkdf2Contract X86.abi (76 + pbkFrame Spec.Hmac.sha224I)).pre s := by
  implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha224I,
      Spec.Hmac.sha224S, Spec.Hmac.sha224, pbkFrame, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [pbkFrameSat, pbkFrameMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using pbkFrameSat

theorem sha256_pbkFrameSat :
    ∃ s, (Spec.Hmac.sha256I.pbkdf2Contract X86.abi (76 + pbkFrame Spec.Hmac.sha256I)).pre s := by
  implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha256I,
      Spec.Hmac.sha256S, Spec.Hmac.sha256, pbkFrame, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [pbkFrameSat, pbkFrameMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using pbkFrameSat

theorem sha384_pbkFrameSat :
    ∃ s, (Spec.Hmac.sha384I.pbkdf2Contract X86.abi (76 + pbkFrame Spec.Hmac.sha384I)).pre s := by
  implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha384I,
      Spec.Hmac.sha384S, Spec.Hmac.sha384, pbkFrame, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [pbkFrameSat, pbkFrameMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using pbkFrameSat

theorem sha512_pbkFrameSat :
    ∃ s, (Spec.Hmac.sha512I.pbkdf2Contract X86.abi (76 + pbkFrame Spec.Hmac.sha512I)).pre s := by
  implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512I,
      Spec.Hmac.sha512S, Spec.Hmac.sha512, pbkFrame, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [pbkFrameSat, pbkFrameMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using pbkFrameSat

theorem sha512_224_pbkFrameSat :
    ∃ s, (Spec.Hmac.sha512_224I.pbkdf2Contract X86.abi (76 + pbkFrame Spec.Hmac.sha512_224I)).pre s := by
  implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512_224I,
      Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, pbkFrame, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [pbkFrameSat, pbkFrameMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using pbkFrameSat

theorem sha512_256_pbkFrameSat :
    ∃ s, (Spec.Hmac.sha512_256I.pbkdf2Contract X86.abi (76 + pbkFrame Spec.Hmac.sha512_256I)).pre s := by
  implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512_256I,
      Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, pbkFrame, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [pbkFrameSat, pbkFrameMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using pbkFrameSat

end VG.Proof.Pbkdf2.Whole.X86
