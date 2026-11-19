module

public import VerifiedGarbage.Proof.Framework.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sha1.Arm.Shared
public import VerifiedGarbage.Proof.Sha256.Arm.Shared
public import VerifiedGarbage.Proof.Sha512.Arm.Shared
public import VerifiedGarbage.Proof.MdStream.Arm.DigestInstances
public import VerifiedGarbage.Proof.Modes.Arm.ScrubCode
public import VerifiedGarbage.Proof.Sha1.PostOut
public import VerifiedGarbage.Proof.Sha256.PostOut
public import VerifiedGarbage.Proof.Sha512.PostOut
import VerifiedGarbage.Proof.Sha1.Arm.Lit
import VerifiedGarbage.Proof.Sha256.Arm.Lit
import VerifiedGarbage.Proof.Sha512.Arm.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Sha256.Scratch
import VerifiedGarbage.Proof.Sha512.Scratch
import VerifiedGarbage.Proof.Sha256.Digest
import VerifiedGarbage.Proof.Sha512.Digest
import VerifiedGarbage.Proof.Framework.Arm.StackScratch
meta import VerifiedGarbage.Proof.Framework.Arm.Scrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Sha1.Arm.Shared
meta import VerifiedGarbage.Proof.Sha256.Arm.Shared
meta import VerifiedGarbage.Proof.Sha512.Arm.Shared
meta import VerifiedGarbage.Proof.MdStream.Arm.DigestInstances
meta import VerifiedGarbage.Proof.Modes.Arm.ScrubCode
meta import VerifiedGarbage.Proof.Sha1.PostOut
meta import VerifiedGarbage.Proof.Sha256.PostOut
meta import VerifiedGarbage.Proof.Sha512.PostOut
meta import VerifiedGarbage.Proof.Sha1.Arm.Lit
meta import VerifiedGarbage.Proof.Sha256.Arm.Lit
meta import VerifiedGarbage.Proof.Sha512.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Sha256.Scratch
meta import VerifiedGarbage.Proof.Sha512.Scratch
meta import VerifiedGarbage.Proof.Sha256.Digest
meta import VerifiedGarbage.Proof.Sha512.Digest
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratch

/-!
# SHA-1 and SHA-2 on ARMv7, without secret residue

`init` writes only the streaming state, and has no frame: it is registered
with `Arm.Scrub.scrubReg`. Every other function keeps its working space in a
frame, the `stack` of its contract: `update` and `finalize` 176 bytes
(SHA-1, SHA-224, SHA-256) or 288 (SHA-384, SHA-512 and its truncations)
(`withStackScratch`), the scratch their compression functions use and the
copies of their stack arguments, and the one-shot `digest` `16 + dbytes`
(`withRegScratchWiped`, and the 16 bytes it pushes around `update`). Each is
registered with `Arm.Scrub.scrubRegF`: its code, then that stack zeroed,
then the registers a callee may change, but the result, and the flags set to
constants.

What `scrubRegF` needs of the code follows from its compression function's
alone, which `lit_decide` evaluates on its literal (`Proof/<Hash>/Arm/Lit.lean`):
the generic `update` and `finalize` (`Impl/MdStream/Arm.lean`) use the stack
only as the compression function does (`update_scrubArm`,
`finalize_scrubArm`), and `digest` adds its frame to what its streaming
functions use (`digest_scrubArm`). Their postconditions read the memory on
return only within their buffers (`Arm.Scrub.PostOut`, from the lemmas of
`Proof/<Hash>/PostOut.lean` that the other targets use).

HMAC, PBKDF2, DSA and Ed25519 call this code under internal names
(`vg_sha256_update_scratch`, …, `Proof/Pbkdf2/Stream/Arm/`), as it is
verified, without the wipe, and so does `digest`.
-/

@[expose] public section

namespace VG.Proof.MdStream.Arm.ShaScrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack VG.Proof.Modes.Arm

/-! ## The code: its frames, and no indirect call -/

/-- What `scrubRegF` needs of code `c`, with `n` bytes of stack. -/
abbrev ScrubOk (c : Prog isa) (n : Nat) : Prop := armStack c ≤ n ∧ noIcall c = true

theorem update_scrubArm (P : Impl.MdStream.Arm.Params) (name : String) {c : Prog isa} {n : Nat}
    (hc : ScrubOk c n) : ScrubOk (Impl.MdStream.Arm.update P name c) n := by
  simp only [ScrubOk, Impl.MdStream.Arm.update, Impl.MdStream.Arm.updateBody, Impl.MdStream.Arm.fill,
    Impl.MdStream.Arm.compressN, Impl.MdStream.Arm.compressWith, armStack, noIcall, hc.2, Bool.and_true,
    Nat.zero_max, Nat.max_zero, Nat.max_self, and_true] at hc ⊢
  exact hc

theorem finalize_scrubArm (P : Impl.MdStream.Arm.Params) (name : String) {c : Prog isa} {n : Nat}
    (hc : ScrubOk c n) : ScrubOk (Impl.MdStream.Arm.finalize P name c) n := by
  simp only [ScrubOk, Impl.MdStream.Arm.finalize, Impl.MdStream.Arm.finalizeBody,
    Impl.MdStream.Arm.compressAt, Impl.MdStream.Arm.compressWith, armStack, noIcall, hc.2, Bool.and_true,
    Nat.zero_max, Nat.max_zero, Nat.max_self, and_true] at hc ⊢
  exact hc

/-- A stack scratch buffer of `bytes` bytes. -/
theorem withStackScratch_scrubArm {bytes m n : Nat} {c : Prog isa} (hc : ScrubOk c n) :
    ScrubOk (Impl.StackScratch.Arm.withStackScratch bytes m c) (n + bytes) := by
  simp only [ScrubOk, Impl.StackScratch.Arm.withStackScratch, armStack, noIcall, hc.2, Bool.and_true,
    Nat.zero_max, and_true] at hc ⊢
  omega

/-- The one-shot digest, from its streaming functions'. -/
theorem digest_scrubArm (H : Impl.Pbkdf2.Stream.Arm.Hash) (hi : ScrubOk H.initC 0) (hu : ScrubOk H.updC 0)
    (hf : ScrubOk H.finC 0) :
    ScrubOk (Impl.MdStream.Arm.Digest.digest H) (16 + Impl.MdStream.Arm.Digest.dbytes H) := by
  refine withRegScratchWiped_scrubArm (n := 16) ?_
  simp only [ScrubOk, Nat.le_zero] at hi hu hf
  simp only [Impl.MdStream.Arm.Digest.digestMain, Impl.Pbkdf2.Stream.Arm.Hash.callInit,
    Impl.Pbkdf2.Stream.Arm.Hash.callFin, Impl.Pbkdf2.Stream.Arm.copy, armStack, noIcall, hi.1, hi.2, hu.1,
    hu.2, hf.1, hf.2, List.length_cons, List.length_nil, Bool.and_self, and_true]
  decide

theorem sha1_compress : ScrubOk Impl.Sha1.Arm.compress 0 := by lit_decide
theorem sha256_compress : ScrubOk Impl.Sha256.Arm.compress 0 := by lit_decide
theorem sha512_compress : ScrubOk Impl.Sha512.Arm.compress 0 := by lit_decide

theorem sha1_update : ScrubOk Impl.Sha1.Arm.Stream.update 0 := update_scrubArm _ _ sha1_compress
theorem sha1_finalize : ScrubOk Impl.Sha1.Arm.Stream.finalize 0 := finalize_scrubArm _ _ sha1_compress
theorem sha256_update : ScrubOk Impl.Sha256.Arm.Stream.update 0 := update_scrubArm _ _ sha256_compress
theorem sha256_finalize : ScrubOk Impl.Sha256.Arm.Stream.finalize 0 := finalize_scrubArm _ _ sha256_compress
theorem sha512_update : ScrubOk Impl.Sha512.Arm.Stream.update 0 := update_scrubArm _ _ sha512_compress
theorem sha512_finalize : ScrubOk Impl.Sha512.Arm.Stream.finalize 0 := finalize_scrubArm _ _ sha512_compress

/-- `init` is one block. -/
theorem block_scrubArm (is : List Instr) : ScrubOk (.block is) 0 := ⟨Nat.le_refl 0, rfl⟩

theorem frameOk_176 : FrameOk 176 := by decide
theorem frameOk_288 : FrameOk 288 := by decide

/-! ## SHA-256's frames

The shared contracts give `update` and `finalize` 608 bytes of scratch,
sized for x86-64's AVX2 compression function, but ARM's uses 160
(`Proof.Sha256.updateArm`). The public functions keep only those 160 bytes in
their frame, 176 with the stack arguments' copies (`withStackScratch 176`),
so that the wipe after them is of 176 bytes rather than 624. -/

theorem sha256UpdateW :
    Verified Arm.target Impl.Sha256.Arm.Stream.update (Proof.Sha256.updateScratchContractW 20 Arm.abi) :=
  Proof.Sha256.Arm.Stream.Update.update_verified.of_implies (by
    contract_implies [Proof.Sha256.updateScratchContractW, Proof.Sha256.updateScratchSigW,
      Proof.Sha256.updateArm, Proof.Sha256.countArm, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val, Arm.State.addr]
      [Proof.Sha256.Arm.Stream.Update.sat, MdStream.Arm.Update.sat, Impl.Sha256.Arm.Stream.params,
        Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using Proof.Sha256.Arm.Stream.Update.sat)

theorem sha256FinalizeW :
    Verified Arm.target Impl.Sha256.Arm.Stream.finalize (Proof.Sha256.finalizeScratchContractW 20 Arm.abi) :=
  Proof.Sha256.Arm.Stream.Finalize.finalize_verified.of_implies (by
    contract_implies [Proof.Sha256.finalizeScratchContractW, Proof.Sha256.finalizeScratchSigW,
      Proof.Sha256.finalizeArm, Proof.Sha256.countArm, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val, Arm.State.addr]
      [Proof.Sha256.Arm.Stream.Finalize.sat, MdStream.Arm.Finalize.sat, MdStream.Arm.Finalize.satBase,
        Impl.Sha256.Arm.Stream.params, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
      using Proof.Sha256.Arm.Stream.Finalize.sat)

theorem sha256Update176 : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratch 176 2 Impl.Sha256.Arm.Stream.update)
    (Spec.Sha256.updateContract Arm.abi 176) :=
  Arm.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 20) (stack := 0) (bytes := 176) (m := 2)
    sha256UpdateW (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sha256.updatePost_local _)
    (fun vs mm m₁ m₂ r hl _ hb h => Proof.Sha256.updatePostOut_local _ vs mm m₁ m₂ r hl hb h)
    (by implies_sat [Spec.Sha256.updateContract, Spec.Sha256.updateSig, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Sha256.Arm.Shared.updateFrameSat, MdStream.Arm.Update.sat, Impl.Sha256.Arm.Stream.params,
        Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using Proof.Sha256.Arm.Shared.updateFrameSat)

theorem sha256Finalize176 : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratch 176 1 Impl.Sha256.Arm.Stream.finalize)
    (Spec.Sha256.finalizeContract Arm.abi 176) :=
  Arm.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 20) (stack := 0) (bytes := 176) (m := 1)
    sha256FinalizeW (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sha256.finalizePost_local _)
    (fun vs mm m₁ m₂ r hl _ hb h => Proof.Sha256.finalizePostOut_local _ vs mm m₁ m₂ r hl hb h)
    (by implies_sat [Spec.Sha256.finalizeContract, Spec.Sha256.finalizeSig, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Sha256.Arm.Shared.finalizeFrameSat, MdStream.Arm.Finalize.satBase, Arm.stackArg,
        Arm.stackArgAddr, Mem.readW, Mem.read] using Proof.Sha256.Arm.Shared.finalizeFrameSat)

/-- `finKD` for SHA-224's digest of the messages hashed from its initial hash
value, with the 160 bytes of scratch the code uses. -/
def finalize224K : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 96⟩
    let out : Region := ⟨State.addr (stackArg s 0), 28⟩
    let scratch : Region := ⟨State.addr (stackArg s 1), 160⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    s.rd = [args] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + 96 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 28 ≤ 2 ^ 32 ∧
    (stackArg s 1).toNat + 160 ≤ 2 ^ 32 ∧ s.sp.toNat + 8 ≤ 2 ^ 32
  post s s' := ∀ m, Spec.Sha256.ReprFrom Spec.Sha256.H0_224 s.mem (State.addr (s.gpr .r0)) m →
    Proof.Sha256.countArm s = BitVec.ofNat 64 m.length →
    Spec.Sha256.bytesAt s'.mem (State.addr (stackArg s 0)) 28 = Spec.Sha256.sha224 m
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

/-- Rewrites `finKD` and `finalize224K` at a narrowed state. -/
macro "narrowK224" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| plain_simp_names simp only [MdStream.Arm.finKD, Proof.Sha256.countArm, finalize224K, MdStream.Arm.count,
                     VG.Arm.stackArg_withRegions, VG.Arm.stackArgAddr_withRegions, State.withRegions_gpr, State.withRegions_sp,
                     State.withRegions_mem, State.withRegions_rd, State.withRegions_wr] $(loc)?)

theorem finalize224K_verified (hsat : ∃ s, finalize224K.pre s) :
    Verified Arm.target Impl.Sha256.Arm.Stream.finalize224 finalize224K :=
  Verified.widen Proof.Sha256.Arm.Stream.Finalize.finalize224_verified
    (fun s => [⟨State.addr (s.gpr .r0), 96⟩, ⟨State.addr (stackArg s 0), 28⟩,
      ⟨State.addr (stackArg s 1), 160⟩])
    (fun _ h => by
      obtain ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂⟩ := h
      narrowK224
      exact ⟨h₁, rfl, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]; exact .cons ⟨rfl, Nat.le_refl _⟩ (.cons ⟨rfl, Nat.le_refl _⟩ (.cons ⟨rfl, Nat.le_refl _⟩ .nil)))
    (fun _ _ _ h => by
      narrowK224 at h ⊢
      intro m hr hc
      exact (h _ m hr trivial hc).trans (Proof.Sha256.sha224_eq m))
    (fun _ _ _ _ h => by
      narrowK224
      exact h) hsat

/-- A state satisfying `finalize224K.pre`. -/
def finalize224KSat : State :=
  { Proof.Sha256.Arm.Stream.Finalize.sat224 with wr := [⟨0x1000, 96⟩, ⟨0x2000, 28⟩, ⟨0x3000, 160⟩] }

theorem finalize224K_implies :
    finalize224K.Implies (Proof.Sha256.finalize224ScratchContractW 20 Arm.abi) := by
  contract_implies [Proof.Sha256.finalize224ScratchContractW, Proof.Sha256.finalize224ScratchSigW,
    Spec.Sha256.finalize224Post, finalize224K, Proof.Sha256.countArm, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finalize224KSat, Proof.Sha256.Arm.Stream.Finalize.sat224, MdStream.Arm.Finalize.satD,
      MdStream.Arm.Finalize.satBase, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using finalize224KSat

theorem sha224Finalize176 : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratch 176 1 Impl.Sha256.Arm.Stream.finalize224)
    (Spec.Sha256.finalize224Contract Arm.abi 176) :=
  Arm.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 20) (stack := 0) (bytes := 176) (m := 1)
    ((finalize224K_verified finalize224K_implies.sat_left).of_implies finalize224K_implies)
    (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sha256.finalize224Post_local _)
    (fun vs mm m₁ m₂ r hl _ hb h => Proof.Sha256.finalize224PostOut_local _ vs mm m₁ m₂ r hl hb h)
    (by implies_sat [Spec.Sha256.finalize224Contract, Spec.Sha256.finalize224Sig, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Sha256.Arm.Shared.finalize224FrameSat, MdStream.Arm.Finalize.satBase, Arm.stackArg,
        Arm.stackArgAddr, Mem.readW, Mem.read] using Proof.Sha256.Arm.Shared.finalize224FrameSat)

/-! ## SHA-512's frames

As SHA-256's: the shared contracts give 1376 bytes of scratch, ARM's
compression function uses 272 (`Proof.Sha512.updateArm`), and the public
functions keep only those in their frame, 288 bytes with the stack arguments'
copies. -/

theorem sha512UpdateW :
    Verified Arm.target Impl.Sha512.Arm.Stream.update (Proof.Sha512.updateScratchContractW 34 Arm.abi) :=
  Proof.Sha512.Arm.Stream.Update.update_verified.of_implies (by
    sig_implies [Proof.Sha512.updateScratchContractW, Proof.Sha512.updateScratchSigW,
      Proof.Sha512.updateArm, Proof.Sha512.countArm, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val, Arm.State.addr]
      [Proof.Sha512.Arm.Stream.Update.sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
      using Proof.Sha512.Arm.Stream.Update.sat)

theorem sha512FinalizeW :
    Verified Arm.target Impl.Sha512.Arm.Stream.finalize (Proof.Sha512.finalizeScratchContractW 34 Arm.abi) :=
  Proof.Sha512.Arm.Stream.Finalize.finalize_verified.of_implies (by
    contract_implies [Proof.Sha512.finalizeScratchContractW, Proof.Sha512.finalizeScratchSigW,
      Proof.Sha512.finalizeArm, Proof.Sha512.countArm, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val, Arm.State.addr]
      [Proof.Sha512.Arm.Stream.Finalize.sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
      using Proof.Sha512.Arm.Stream.Finalize.sat)

theorem sha512Update288 : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratch 288 2 Impl.Sha512.Arm.Stream.update)
    (Spec.Sha512.updateContract Arm.abi 288) :=
  Arm.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 34) (stack := 0) (bytes := 288) (m := 2)
    sha512UpdateW (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sha512.updatePost_local _)
    (fun vs mm m₁ m₂ r hl _ hb h => Proof.Sha512.updatePostOut_local _ vs mm m₁ m₂ r hl hb h)
    (by implies_sat [Spec.Sha512.updateContract, Spec.Sha512.updateSig, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Sha512.Arm.Shared.updateFrameSat, Proof.Sha512.Arm.Stream.Update.sat, Arm.stackArg,
        Arm.stackArgAddr, Mem.readW, Mem.read] using Proof.Sha512.Arm.Shared.updateFrameSat)

theorem sha512Finalize288 : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratch 288 1 Impl.Sha512.Arm.Stream.finalize)
    (Spec.Sha512.finalizeContract Arm.abi 288) :=
  Arm.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 34) (stack := 0) (bytes := 288) (m := 1)
    sha512FinalizeW (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sha512.finalizePost_local _)
    (fun vs mm m₁ m₂ r hl _ hb h => Proof.Sha512.finalizePostOut_local _ vs mm m₁ m₂ r hl hb h)
    (by implies_sat [Spec.Sha512.finalizeContract, Spec.Sha512.finalizeSig, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Sha512.Arm.Shared.finalizeFrameSat, MdStream.Arm.Finalize.satBase, Arm.stackArg,
        Arm.stackArgAddr, Mem.readW, Mem.read] using Proof.Sha512.Arm.Shared.finalizeFrameSat)

/-- `finKD` for the `D`-byte `digest` of the messages hashed from `iv`, with
the 272 bytes of scratch the code uses. -/
def finalizeDigestK (iv : Spec.Sha512.HashValue) (D : Nat) (digest : List Byte → List Byte) :
    Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 192⟩
    let out : Region := ⟨State.addr (stackArg s 0), D⟩
    let scratch : Region := ⟨State.addr (stackArg s 1), 272⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    s.rd = [args] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + 192 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + D ≤ 2 ^ 32 ∧
    (stackArg s 1).toNat + 272 ≤ 2 ^ 32 ∧ s.sp.toNat + 8 ≤ 2 ^ 32
  post s s' := ∀ m, Spec.Sha512.Repr iv s.mem (State.addr (s.gpr .r0)) m → m.length < 2 ^ 64 →
    Proof.Sha512.countArm s = BitVec.ofNat 64 m.length →
    Spec.Sha512.bytesAt s'.mem (State.addr (stackArg s 0)) D = digest m
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

/-- Rewrites `finKD` and `finalizeDigestK` at a narrowed state. -/
macro "narrowKD" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| plain_simp_names simp only [MdStream.Arm.finKD, Proof.Sha512.countArm, finalizeDigestK, MdStream.Arm.count,
                     VG.Arm.stackArg_withRegions, VG.Arm.stackArgAddr_withRegions, State.withRegions_gpr, State.withRegions_sp,
                     State.withRegions_mem, State.withRegions_rd, State.withRegions_wr] $(loc)?)

theorem finalizeDigestK_verified {code : Prog Arm.isa} {o : List Instr} {D : Nat}
    {iv : Spec.Sha512.HashValue} {digest : List Byte → List Byte}
    (hv : Verified Arm.target code
      (MdStream.Arm.finKD (P := { Impl.Sha512.Arm.Stream.params with out := o }) Proof.Sha512.md D))
    (hdg : ∀ m, (Proof.Sha512.md.hash iv m).take D = digest m)
    (hsat : ∃ s, (finalizeDigestK iv D digest).pre s) :
    Verified Arm.target code (finalizeDigestK iv D digest) :=
  Verified.widen hv
    (fun s => [⟨State.addr (s.gpr .r0), 192⟩, ⟨State.addr (stackArg s 0), D⟩,
      ⟨State.addr (stackArg s 1), 272⟩])
    (fun _ h => by
      obtain ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂⟩ := h
      narrowKD
      exact ⟨h₁, rfl, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]; exact .cons ⟨rfl, Nat.le_refl _⟩ (.cons ⟨rfl, Nat.le_refl _⟩ (.cons ⟨rfl, Nat.le_refl _⟩ .nil)))
    (fun _ _ _ h => by
      narrowKD at h ⊢
      intro m hr hl hc
      exact (h iv m hr hl hc).trans (hdg m))
    (fun _ _ _ _ h => by
      narrowKD
      exact h) hsat

/-- A state satisfying `finalizeDigestK.pre`. -/
def finalizeDigestKSat (D : Nat) : State :=
  { Proof.Sha512.Arm.Stream.Finalize.satD D with wr := [⟨0x1000, 192⟩, ⟨0x2000, D⟩, ⟨0x3000, 272⟩] }

theorem finalizeDigestK_implies48 (iv : Spec.Sha512.HashValue) (digest : List Byte → List Byte) :
    (finalizeDigestK iv 48 digest).Implies (Proof.Sha512.finalizeDigestScratchContractW 34 Arm.abi iv 48 digest 0) := by
  contract_implies [Proof.Sha512.finalizeDigestScratchContractW, Proof.Sha512.finalizeDigestScratchSigW,
    Spec.Sha512.finalizeDigestPost, finalizeDigestK, Proof.Sha512.countArm, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finalizeDigestKSat, Proof.Sha512.Arm.Stream.Finalize.satD, MdStream.Arm.Finalize.satD,
      MdStream.Arm.Finalize.satBase, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using finalizeDigestKSat 48

theorem finalizeDigest288_48 {code : Prog Arm.isa} {o : List Instr} {iv : Spec.Sha512.HashValue}
    {digest : List Byte → List Byte}
    (hv : Verified Arm.target code
      (MdStream.Arm.finKD (P := { Impl.Sha512.Arm.Stream.params with out := o }) Proof.Sha512.md 48))
    (hdg : ∀ m, (Proof.Sha512.md.hash iv m).take 48 = digest m) :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 288 1 code)
      (Spec.Sha512.finalizeDigestContract Arm.abi iv 48 digest 288) :=
  Arm.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 34) (stack := 0) (bytes := 288) (m := 1)
    ((finalizeDigestK_verified hv hdg (finalizeDigestK_implies48 iv digest).sat_left).of_implies
      (finalizeDigestK_implies48 iv digest))
    (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sha512.finalizeDigestPost_local _ _ _ _)
    (fun vs mm m₁ m₂ r hl _ hb h => Proof.Sha512.finalizeDigestPostOut_local _ _ _ _ vs mm m₁ m₂ r hl hb h)
    (by implies_sat [Spec.Sha512.finalizeDigestContract, Spec.Sha512.finalizeDigestSig, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Sha512.Arm.Shared.finalizeDigestFrameSat, MdStream.Arm.Finalize.satBase, Arm.stackArg,
        Arm.stackArgAddr, Mem.readW, Mem.read] using Proof.Sha512.Arm.Shared.finalizeDigestFrameSat 48)

theorem finalizeDigestK_implies32 (iv : Spec.Sha512.HashValue) (digest : List Byte → List Byte) :
    (finalizeDigestK iv 32 digest).Implies (Proof.Sha512.finalizeDigestScratchContractW 34 Arm.abi iv 32 digest 0) := by
  contract_implies [Proof.Sha512.finalizeDigestScratchContractW, Proof.Sha512.finalizeDigestScratchSigW,
    Spec.Sha512.finalizeDigestPost, finalizeDigestK, Proof.Sha512.countArm, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finalizeDigestKSat, Proof.Sha512.Arm.Stream.Finalize.satD, MdStream.Arm.Finalize.satD,
      MdStream.Arm.Finalize.satBase, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using finalizeDigestKSat 32

theorem finalizeDigest288_32 {code : Prog Arm.isa} {o : List Instr} {iv : Spec.Sha512.HashValue}
    {digest : List Byte → List Byte}
    (hv : Verified Arm.target code
      (MdStream.Arm.finKD (P := { Impl.Sha512.Arm.Stream.params with out := o }) Proof.Sha512.md 32))
    (hdg : ∀ m, (Proof.Sha512.md.hash iv m).take 32 = digest m) :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 288 1 code)
      (Spec.Sha512.finalizeDigestContract Arm.abi iv 32 digest 288) :=
  Arm.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 34) (stack := 0) (bytes := 288) (m := 1)
    ((finalizeDigestK_verified hv hdg (finalizeDigestK_implies32 iv digest).sat_left).of_implies
      (finalizeDigestK_implies32 iv digest))
    (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sha512.finalizeDigestPost_local _ _ _ _)
    (fun vs mm m₁ m₂ r hl _ hb h => Proof.Sha512.finalizeDigestPostOut_local _ _ _ _ vs mm m₁ m₂ r hl hb h)
    (by implies_sat [Spec.Sha512.finalizeDigestContract, Spec.Sha512.finalizeDigestSig, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Sha512.Arm.Shared.finalizeDigestFrameSat, MdStream.Arm.Finalize.satBase, Arm.stackArg,
        Arm.stackArgAddr, Mem.readW, Mem.read] using Proof.Sha512.Arm.Shared.finalizeDigestFrameSat 32)

theorem finalizeDigestK_implies28 (iv : Spec.Sha512.HashValue) (digest : List Byte → List Byte) :
    (finalizeDigestK iv 28 digest).Implies (Proof.Sha512.finalizeDigestScratchContractW 34 Arm.abi iv 28 digest 0) := by
  contract_implies [Proof.Sha512.finalizeDigestScratchContractW, Proof.Sha512.finalizeDigestScratchSigW,
    Spec.Sha512.finalizeDigestPost, finalizeDigestK, Proof.Sha512.countArm, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finalizeDigestKSat, Proof.Sha512.Arm.Stream.Finalize.satD, MdStream.Arm.Finalize.satD,
      MdStream.Arm.Finalize.satBase, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using finalizeDigestKSat 28

theorem finalizeDigest288_28 {code : Prog Arm.isa} {o : List Instr} {iv : Spec.Sha512.HashValue}
    {digest : List Byte → List Byte}
    (hv : Verified Arm.target code
      (MdStream.Arm.finKD (P := { Impl.Sha512.Arm.Stream.params with out := o }) Proof.Sha512.md 28))
    (hdg : ∀ m, (Proof.Sha512.md.hash iv m).take 28 = digest m) :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 288 1 code)
      (Spec.Sha512.finalizeDigestContract Arm.abi iv 28 digest 288) :=
  Arm.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 34) (stack := 0) (bytes := 288) (m := 1)
    ((finalizeDigestK_verified hv hdg (finalizeDigestK_implies28 iv digest).sat_left).of_implies
      (finalizeDigestK_implies28 iv digest))
    (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sha512.finalizeDigestPost_local _ _ _ _)
    (fun vs mm m₁ m₂ r hl _ hb h => Proof.Sha512.finalizeDigestPostOut_local _ _ _ _ vs mm m₁ m₂ r hl hb h)
    (by implies_sat [Spec.Sha512.finalizeDigestContract, Spec.Sha512.finalizeDigestSig, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Sha512.Arm.Shared.finalizeDigestFrameSat, MdStream.Arm.Finalize.satBase, Arm.stackArg,
        Arm.stackArgAddr, Mem.readW, Mem.read] using Proof.Sha512.Arm.Shared.finalizeDigestFrameSat 28)

theorem sha384Finalize288 : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratch 288 1
      (Impl.Sha512.Arm.Stream.finalizeDigest Impl.Sha512.Arm.Stream.params384))
    (Spec.Sha512.finalizeDigestContract Arm.abi Spec.Sha512.H0_384 48 Spec.Sha512.sha384 288) :=
  finalizeDigest288_48 Proof.Sha512.Arm.Stream.Finalize.finalize384_verified (fun _ => rfl)

theorem sha512_256Finalize288 : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratch 288 1
      (Impl.Sha512.Arm.Stream.finalizeDigest Impl.Sha512.Arm.Stream.params512_256))
    (Spec.Sha512.finalizeDigestContract Arm.abi Spec.Sha512.H0_512_256 32 Spec.Sha512.sha512_256 288) :=
  finalizeDigest288_32 Proof.Sha512.Arm.Stream.Finalize.finalize512_256_verified (fun _ => rfl)

theorem sha512_224Finalize288 : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratch 288 1
      (Impl.Sha512.Arm.Stream.finalizeDigest Impl.Sha512.Arm.Stream.params512_224))
    (Spec.Sha512.finalizeDigestContract Arm.abi Spec.Sha512.H0_512_224 28 Spec.Sha512.sha512_224 288) :=
  finalizeDigest288_28 Proof.Sha512.Arm.Stream.Finalize.finalize512_224_verified (fun _ => rfl)

/-! ## SHA-1 -/

/-- `vg_sha1_init`. -/
def sha1InitReg : Registration Spec.Sha1.initApi Arm.target :=
  scrubReg { code := Impl.Sha1.Arm.Stream.init, verified := Proof.Sha1.Arm.Shared.init } rfl

/-- `vg_sha1_update`. -/
def sha1UpdateReg : Registration Spec.Sha1.updateApi Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 176 2 Impl.Sha1.Arm.Stream.update
      verified := Proof.Sha1.Arm.Shared.update }
    (withStackScratch_scrubArm sha1_update).1 (withStackScratch_scrubArm sha1_update).2 frameOk_176
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha1.updatePost_out _)) rfl

/-- `vg_sha1_finalize`. -/
def sha1FinalizeReg : Registration Spec.Sha1.finalizeApi Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 176 1 Impl.Sha1.Arm.Stream.finalize
      verified := Proof.Sha1.Arm.Shared.finalize }
    (withStackScratch_scrubArm sha1_finalize).1 (withStackScratch_scrubArm sha1_finalize).2 frameOk_176
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha1.finalizePost_out _)) rfl

theorem sha1_digest : ScrubOk (Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha1H)
    (16 + Impl.MdStream.Arm.Digest.dbytes Proof.Pbkdf2.Stream.Arm.sha1H) :=
  digest_scrubArm _ (block_scrubArm _) sha1_update sha1_finalize

/-- `vg_sha1_digest`. -/
def sha1DigestReg : Registration Spec.Sha1.digestApi Arm.target :=
  scrubRegF {
      code := Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha1H
      verified := Proof.MdStream.Arm.Digest.sha1_digest }
    sha1_digest.1 sha1_digest.2 (by decide)
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha1.digestPost_out _)) rfl

/-! ## SHA-224 and SHA-256 -/

/-- `vg_sha224_init`. -/
def sha224InitReg : Registration Spec.Sha256.init224Api Arm.target :=
  scrubReg { code := Impl.Sha256.Arm.Stream.init224, verified := Proof.Sha256.Arm.Shared.init224 } rfl

/-- `vg_sha256_init`. -/
def sha256InitReg : Registration Spec.Sha256.initApi Arm.target :=
  scrubReg { code := Impl.Sha256.Arm.Stream.init, verified := Proof.Sha256.Arm.Shared.init } rfl

/-- `vg_sha256_update`, which SHA-224 shares. -/
def sha256UpdateReg : Registration Spec.Sha256.updateApi Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 176 2 Impl.Sha256.Arm.Stream.update
      verified := sha256Update176 }
    (withStackScratch_scrubArm sha256_update).1 (withStackScratch_scrubArm sha256_update).2 frameOk_176
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.updatePost_out _)) rfl

/-- `vg_sha256_finalize`. -/
def sha256FinalizeReg : Registration Spec.Sha256.finalizeApi Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 176 1 Impl.Sha256.Arm.Stream.finalize
      verified := sha256Finalize176 }
    (withStackScratch_scrubArm sha256_finalize).1 (withStackScratch_scrubArm sha256_finalize).2 frameOk_176
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.finalizePost_out _)) rfl

theorem sha224_finalize : ScrubOk Impl.Sha256.Arm.Stream.finalize224 0 :=
  finalize_scrubArm _ _ sha256_compress

/-- `vg_sha224_finalize`. -/
def sha224FinalizeReg : Registration Spec.Sha256.finalize224Api Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 176 1 Impl.Sha256.Arm.Stream.finalize224
      verified := sha224Finalize176 }
    (withStackScratch_scrubArm sha224_finalize).1 (withStackScratch_scrubArm sha224_finalize).2 frameOk_176
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.finalize224Post_out _)) rfl

theorem sha224_digest : ScrubOk (Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha224H)
    (16 + Impl.MdStream.Arm.Digest.dbytes Proof.Pbkdf2.Stream.Arm.sha224H) :=
  digest_scrubArm _ (block_scrubArm _) sha256_update sha256_finalize

theorem sha256_digest : ScrubOk (Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha256H)
    (16 + Impl.MdStream.Arm.Digest.dbytes Proof.Pbkdf2.Stream.Arm.sha256H) :=
  digest_scrubArm _ (block_scrubArm _) sha256_update sha256_finalize

/-- `vg_sha224_digest`. -/
def sha224DigestReg : Registration Spec.Sha256.digest224Api Arm.target :=
  scrubRegF {
      code := Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha224H
      verified := Proof.MdStream.Arm.Digest.sha224_digest }
    sha224_digest.1 sha224_digest.2 (by decide)
    (postOut_of_local (leak := none) ScrubAbi.plain
      (Proof.Sha256.digestPost_out 28 Spec.Sha256.sha224 _ (by decide))) rfl

/-- `vg_sha256_digest`. -/
def sha256DigestReg : Registration Spec.Sha256.digest256Api Arm.target :=
  scrubRegF {
      code := Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha256H
      verified := Proof.MdStream.Arm.Digest.sha256_digest }
    sha256_digest.1 sha256_digest.2 (by decide)
    (postOut_of_local (leak := none) ScrubAbi.plain
      (Proof.Sha256.digestPost_out 32 Spec.Sha256.hash _ (by decide))) rfl

/-! ## SHA-384, SHA-512, SHA-512/224 and SHA-512/256 -/

/-- `vg_sha384_init`. -/
def sha384InitReg : Registration Spec.Sha512.init384Api Arm.target :=
  scrubReg {
      code := Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_384
      verified := Proof.Sha512.Arm.Shared.init Spec.Sha512.H0_384 }
    rfl

/-- `vg_sha512_init`. -/
def sha512InitReg : Registration Spec.Sha512.init512Api Arm.target :=
  scrubReg {
      code := Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_512
      verified := Proof.Sha512.Arm.Shared.init Spec.Sha512.H0_512 }
    rfl

/-- `vg_sha512_224_init`. -/
def sha512_224InitReg : Registration Spec.Sha512.init512_224Api Arm.target :=
  scrubReg {
      code := Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_512_224
      verified := Proof.Sha512.Arm.Shared.init Spec.Sha512.H0_512_224 }
    rfl

/-- `vg_sha512_256_init`. -/
def sha512_256InitReg : Registration Spec.Sha512.init512_256Api Arm.target :=
  scrubReg {
      code := Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_512_256
      verified := Proof.Sha512.Arm.Shared.init Spec.Sha512.H0_512_256 }
    rfl

/-- `vg_sha512_update`, which the truncations share. -/
def sha512UpdateReg : Registration Spec.Sha512.updateApi Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 288 2 Impl.Sha512.Arm.Stream.update
      verified := sha512Update288 }
    (withStackScratch_scrubArm sha512_update).1 (withStackScratch_scrubArm sha512_update).2 frameOk_288
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.updatePost_out _)) rfl

/-- `vg_sha512_finalize`. -/
def sha512FinalizeReg : Registration Spec.Sha512.finalizeApi Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 288 1 Impl.Sha512.Arm.Stream.finalize
      verified := sha512Finalize288 }
    (withStackScratch_scrubArm sha512_finalize).1 (withStackScratch_scrubArm sha512_finalize).2 frameOk_288
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.finalizePost_out _)) rfl

theorem finalizeDigest_scrubArm (P : Impl.MdStream.Arm.Params) :
    ScrubOk (Impl.StackScratch.Arm.withStackScratch 288 1 (Impl.Sha512.Arm.Stream.finalizeDigest P)) 288 :=
  withStackScratch_scrubArm (n := 0) (finalize_scrubArm _ _ sha512_compress)

/-- `vg_sha384_finalize`. -/
def sha384FinalizeReg : Registration Spec.Sha512.finalize384Api Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 288 1
        (Impl.Sha512.Arm.Stream.finalizeDigest Impl.Sha512.Arm.Stream.params384)
      verified := sha384Finalize288 }
    (finalizeDigest_scrubArm _).1 (finalizeDigest_scrubArm _).2 frameOk_288
    (postOut_of_local (leak := none) ScrubAbi.plain
      (Proof.Sha512.finalizeDigestPost_out Spec.Sha512.H0_384 48 Spec.Sha512.sha384 _ (by decide))) rfl

/-- `vg_sha512_256_finalize`. -/
def sha512_256FinalizeReg : Registration Spec.Sha512.finalize512_256Api Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 288 1
        (Impl.Sha512.Arm.Stream.finalizeDigest Impl.Sha512.Arm.Stream.params512_256)
      verified := sha512_256Finalize288 }
    (finalizeDigest_scrubArm _).1 (finalizeDigest_scrubArm _).2 frameOk_288
    (postOut_of_local (leak := none) ScrubAbi.plain
      (Proof.Sha512.finalizeDigestPost_out Spec.Sha512.H0_512_256 32 Spec.Sha512.sha512_256 _ (by decide))) rfl

/-- `vg_sha512_224_finalize`. -/
def sha512_224FinalizeReg : Registration Spec.Sha512.finalize512_224Api Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 288 1
        (Impl.Sha512.Arm.Stream.finalizeDigest Impl.Sha512.Arm.Stream.params512_224)
      verified := sha512_224Finalize288 }
    (finalizeDigest_scrubArm _).1 (finalizeDigest_scrubArm _).2 frameOk_288
    (postOut_of_local (leak := none) ScrubAbi.plain
      (Proof.Sha512.finalizeDigestPost_out Spec.Sha512.H0_512_224 28 Spec.Sha512.sha512_224 _ (by decide))) rfl

theorem sha384_digest : ScrubOk (Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha384H)
    (16 + Impl.MdStream.Arm.Digest.dbytes Proof.Pbkdf2.Stream.Arm.sha384H) :=
  digest_scrubArm _ (block_scrubArm _) sha512_update sha512_finalize

theorem sha512_digest : ScrubOk (Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha512H')
    (16 + Impl.MdStream.Arm.Digest.dbytes Proof.Pbkdf2.Stream.Arm.sha512H') :=
  digest_scrubArm _ (block_scrubArm _) sha512_update sha512_finalize

theorem sha512_224_digest : ScrubOk (Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha512_224H)
    (16 + Impl.MdStream.Arm.Digest.dbytes Proof.Pbkdf2.Stream.Arm.sha512_224H) :=
  digest_scrubArm _ (block_scrubArm _) sha512_update sha512_finalize

theorem sha512_256_digest : ScrubOk (Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha512_256H)
    (16 + Impl.MdStream.Arm.Digest.dbytes Proof.Pbkdf2.Stream.Arm.sha512_256H) :=
  digest_scrubArm _ (block_scrubArm _) sha512_update sha512_finalize

/-- `vg_sha384_digest`. -/
def sha384DigestReg : Registration Spec.Sha512.digest384Api Arm.target :=
  scrubRegF {
      code := Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha384H
      verified := Proof.MdStream.Arm.Digest.sha384_digest }
    sha384_digest.1 sha384_digest.2 (by decide)
    (postOut_of_local (leak := none) ScrubAbi.plain
      (Proof.Sha512.digestPost_out 48 Spec.Sha512.sha384 _ (by decide))) rfl

/-- `vg_sha512_digest`. -/
def sha512DigestReg : Registration Spec.Sha512.digest512Api Arm.target :=
  scrubRegF {
      code := Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha512H'
      verified := Proof.MdStream.Arm.Digest.sha512_digest }
    sha512_digest.1 sha512_digest.2 (by decide)
    (postOut_of_local (leak := none) ScrubAbi.plain
      (Proof.Sha512.digestPost_out 64 Spec.Sha512.sha512 _ (by decide))) rfl

/-- `vg_sha512_224_digest`. -/
def sha512_224DigestReg : Registration Spec.Sha512.digest512_224Api Arm.target :=
  scrubRegF {
      code := Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha512_224H
      verified := Proof.MdStream.Arm.Digest.sha512_224_digest }
    sha512_224_digest.1 sha512_224_digest.2 (by decide)
    (postOut_of_local (leak := none) ScrubAbi.plain
      (Proof.Sha512.digestPost_out 28 Spec.Sha512.sha512_224 _ (by decide))) rfl

/-- `vg_sha512_256_digest`. -/
def sha512_256DigestReg : Registration Spec.Sha512.digest512_256Api Arm.target :=
  scrubRegF {
      code := Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha512_256H
      verified := Proof.MdStream.Arm.Digest.sha512_256_digest }
    sha512_256_digest.1 sha512_256_digest.2 (by decide)
    (postOut_of_local (leak := none) ScrubAbi.plain
      (Proof.Sha512.digestPost_out 32 Spec.Sha512.sha512_256 _ (by decide))) rfl

end VG.Proof.MdStream.Arm.ShaScrub
