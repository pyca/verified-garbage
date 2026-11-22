module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
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
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
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
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Sha256.Scratch
meta import VerifiedGarbage.Proof.Sha512.Scratch
meta import VerifiedGarbage.Proof.Sha256.Digest
meta import VerifiedGarbage.Proof.Sha512.Digest
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratch

/-!
# SHA-1 and SHA-2 on ARMv7, as emitted

Each function is its code with its cleanup (`Impl.Sha1.Arm.Fn`,
`Impl.Sha256.Arm.Fn`, `Impl.Sha512.Arm.Fn`), and the theorem of each, which
its registration binds, is below (`Proof.Sha1.Arm.Fn`, …). `init` writes
only the streaming state and has no frame (`Arm.Scrub.verifiedScrubbed`).
Every other function keeps its working space in a frame, the `stack` of its
contract: `update` and `finalize` 176 bytes (SHA-1, SHA-224, SHA-256) or 288
(SHA-384, SHA-512 and its truncations) (`withStackScratch`), the scratch
their compression functions use and the copies of their stack arguments,
and the one-shot `digest` `16 + dbytes` (`withRegScratch`, and the 16
bytes it pushes around `update`). The cleanup of each zeroes that stack,
then sets the registers a callee may change, but the result, and the flags
to constants (`Arm.Scrub.verifiedScrubbedAll`).

What the cleanup needs of the code (`CodeOk`, here `ScrubOk`) follows from
its compression function's alone, which `lit_decide` evaluates on its
literal (`Proof/<Hash>/Arm/Lit.lean`): the generic `update` and `finalize`
(`Impl/MdStream/Arm.lean`) use the stack only as the compression function
does (`update_scrubArm`, `finalize_scrubArm`), and `digest` as they do
(`digest_scrubArm`). Their
postconditions read the memory on return only within their buffers
(`Arm.Scrub.PostOut`, from the lemmas of `Proof/<Hash>/PostOut.lean` that the
other targets use).

HMAC, PBKDF2, DSA and Ed25519 call this code under internal names
(`vg_sha256_update_scratch`, …, `Proof/Pbkdf2/Stream/Arm/`), as it is
verified, without the wipe, and so does `digest`.
-/

@[expose] public section

namespace VG.Proof.MdStream.Arm.ShaScrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack VG.Proof.Modes.Arm

/-! ## The code: its frames, and no indirect call -/

/-- What `scrubAll` needs of code `c`, with `n` bytes of stack (`CodeOk`). -/
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

/-- A scratch buffer of `bytes` bytes, passed in a register. -/
theorem withRegScratch_scrubArm {bytes n : Nat} {r : Reg} {c : Prog isa} (hc : ScrubOk c n) :
    ScrubOk (Impl.StackScratch.Arm.withRegScratch bytes r c) (n + bytes) := by
  simp only [ScrubOk, Impl.StackScratch.Arm.withRegScratch, armStack, noIcall, hc.2, Bool.and_true,
    Nat.zero_max, and_true] at hc ⊢
  omega

theorem sha1_compress : ScrubOk Impl.Sha1.Arm.compress 0 := by lit_decide
theorem sha256_compress : ScrubOk Impl.Sha256.Arm.compress 0 := by lit_decide
theorem sha512_compress : ScrubOk Impl.Sha512.Arm.compress 0 := by lit_decide

theorem sha1_update : ScrubOk Impl.Sha1.Arm.Stream.update 0 := update_scrubArm _ _ sha1_compress
theorem sha1_finalize : ScrubOk Impl.Sha1.Arm.Stream.finalize 0 := finalize_scrubArm _ _ sha1_compress
theorem sha256_update : ScrubOk Impl.Sha256.Arm.Stream.update 0 := update_scrubArm _ _ sha256_compress
theorem sha256_finalize : ScrubOk Impl.Sha256.Arm.Stream.finalize 0 := finalize_scrubArm _ _ sha256_compress
theorem sha512_update : ScrubOk Impl.Sha512.Arm.Stream.update 0 := update_scrubArm _ _ sha512_compress
theorem sha512_finalize : ScrubOk Impl.Sha512.Arm.Stream.finalize 0 := finalize_scrubArm _ _ sha512_compress

/-- The one-shot digest, from its streaming functions' (for Ed25519's call
of SHA-512's, `Proof/Ed25519/Arm/Scrub.lean`). -/
theorem digest_scrubArm (H : Impl.Pbkdf2.Stream.Arm.Hash) (hi : ScrubOk H.initC 0) (hu : ScrubOk H.updC 0)
    (hf : ScrubOk H.finC 0) :
    ScrubOk (Impl.MdStream.Arm.Digest.digest H) (16 + Impl.MdStream.Arm.Digest.dbytes H) := by
  refine withRegScratch_scrubArm (n := 16) ?_
  simp only [ScrubOk, Nat.le_zero] at hi hu hf
  simp only [ScrubOk, Impl.MdStream.Arm.Digest.digestMain, Impl.Pbkdf2.Stream.Arm.Hash.callInit,
    Impl.Pbkdf2.Stream.Arm.Hash.callFin, Impl.Pbkdf2.Stream.Arm.copy, armStack, noIcall, hi.1, hi.2, hu.1,
    hu.2, hf.1, hf.2, List.length_cons, List.length_nil, Bool.and_self, and_true]
  decide

/-- `init` is one block. -/
theorem block_scrubArm (is : List Instr) : ScrubOk (.block is) 0 := ⟨Nat.le_refl 0, rfl⟩

theorem sha512_digest : ScrubOk (Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha512H')
    (16 + Impl.MdStream.Arm.Digest.dbytes Proof.Pbkdf2.Stream.Arm.sha512H') :=
  digest_scrubArm _ (block_scrubArm _) sha512_update sha512_finalize

theorem frameOk_176 : FrameOk 176 := by decide
theorem frameOk_288 : FrameOk 288 := by decide
theorem frameOk_320 : FrameOk 320 := by decide
theorem frameOk_344 : FrameOk 344 := by decide
theorem frameOk_584 : FrameOk 584 := by decide

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

theorem sha224_finalize : ScrubOk Impl.Sha256.Arm.Stream.finalize224 0 :=
  finalize_scrubArm _ _ sha256_compress

theorem finalizeDigest_scrubArm (P : Impl.MdStream.Arm.Params) :
    ScrubOk (Impl.StackScratch.Arm.withStackScratch 288 1 (Impl.Sha512.Arm.Stream.finalizeDigest P)) 288 :=
  withStackScratch_scrubArm (n := 0) (finalize_scrubArm _ _ sha512_compress)

end VG.Proof.MdStream.Arm.ShaScrub

/-! ## SHA-1 -/

namespace VG.Proof.Sha1.Arm.Fn

open VG VG.Arm VG.Arm.Scrub VG.Proof.MdStream.Arm.ShaScrub

/-- `vg_sha1_init`. -/
theorem init : VerifiedScrubbed target Impl.Sha1.Arm.Fn.init (Spec.Sha1.initContract abi) 0 :=
  verifiedScrubbed (api := Spec.Sha1.initApi)
    { code := Impl.Sha1.Arm.Stream.init, verified := Proof.Sha1.Arm.Shared.init } rfl

/-- `vg_sha1_update`. -/
theorem update : VerifiedScrubbed target Impl.Sha1.Arm.Fn.update (Spec.Sha1.updateContract abi 176) 0 :=
  verifiedScrubbedAll (api := Spec.Sha1.updateApi)
    { code := Impl.StackScratch.Arm.withStackScratch 176 2 Impl.Sha1.Arm.Stream.update
      verified := Proof.Sha1.Arm.Shared.update }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha1.updatePost_out _))
    (scrubSideF_of (withStackScratch_scrubArm sha1_update) frameOk_176 _)

/-- `vg_sha1_finalize`. -/
theorem finalize : VerifiedScrubbed target Impl.Sha1.Arm.Fn.finalize (Spec.Sha1.finalizeContract abi 176) 0 :=
  verifiedScrubbedAll (api := Spec.Sha1.finalizeApi)
    { code := Impl.StackScratch.Arm.withStackScratch 176 1 Impl.Sha1.Arm.Stream.finalize
      verified := Proof.Sha1.Arm.Shared.finalize }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha1.finalizePost_out _))
    (scrubSideF_of (withStackScratch_scrubArm sha1_finalize) frameOk_176 _)

/-- `vg_sha1_digest`. -/
theorem digest : VerifiedScrubbed target Impl.Sha1.Arm.Fn.digest (Spec.Sha1.digestContract abi 320) 0 :=
  verifiedScrubbedAll (api := Spec.Sha1.digestApi)
    { code := Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha1H
      verified := Proof.MdStream.Arm.Digest.sha1_digest }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha1.digestPost_out _))
    (scrubSideF_of (CodeOk.mono (digest_scrubArm Proof.Pbkdf2.Stream.Arm.sha1H (block_scrubArm _)
      sha1_update sha1_finalize) (by decide)) frameOk_320 _)

end VG.Proof.Sha1.Arm.Fn

/-! ## SHA-224 and SHA-256 -/

namespace VG.Proof.Sha256.Arm.Fn

open VG VG.Arm VG.Arm.Scrub VG.Proof.MdStream.Arm.ShaScrub

/-- `vg_sha224_init`. -/
theorem init224 : VerifiedScrubbed target Impl.Sha256.Arm.Fn.init224 (Spec.Sha256.init224Contract abi) 0 :=
  verifiedScrubbed (api := Spec.Sha256.init224Api)
    { code := Impl.Sha256.Arm.Stream.init224, verified := Proof.Sha256.Arm.Shared.init224 } rfl

/-- `vg_sha256_init`. -/
theorem init : VerifiedScrubbed target Impl.Sha256.Arm.Fn.init (Spec.Sha256.initContract abi) 0 :=
  verifiedScrubbed (api := Spec.Sha256.initApi)
    { code := Impl.Sha256.Arm.Stream.init, verified := Proof.Sha256.Arm.Shared.init } rfl

/-- `vg_sha256_update`, which SHA-224 shares. -/
theorem update : VerifiedScrubbed target Impl.Sha256.Arm.Fn.update (Spec.Sha256.updateContract abi 176) 0 :=
  verifiedScrubbedAll (api := Spec.Sha256.updateApi)
    { code := Impl.StackScratch.Arm.withStackScratch 176 2 Impl.Sha256.Arm.Stream.update
      verified := sha256Update176 }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.updatePost_out _))
    (scrubSideF_of (withStackScratch_scrubArm sha256_update) frameOk_176 _)

/-- `vg_sha256_finalize`. -/
theorem finalize :
    VerifiedScrubbed target Impl.Sha256.Arm.Fn.finalize (Spec.Sha256.finalizeContract abi 176) 0 :=
  verifiedScrubbedAll (api := Spec.Sha256.finalizeApi)
    { code := Impl.StackScratch.Arm.withStackScratch 176 1 Impl.Sha256.Arm.Stream.finalize
      verified := sha256Finalize176 }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.finalizePost_out _))
    (scrubSideF_of (withStackScratch_scrubArm sha256_finalize) frameOk_176 _)

/-- `vg_sha224_finalize`. -/
theorem finalize224 :
    VerifiedScrubbed target Impl.Sha256.Arm.Fn.finalize224 (Spec.Sha256.finalize224Contract abi 176) 0 :=
  verifiedScrubbedAll (api := Spec.Sha256.finalize224Api)
    { code := Impl.StackScratch.Arm.withStackScratch 176 1 Impl.Sha256.Arm.Stream.finalize224
      verified := sha224Finalize176 }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.finalize224Post_out _))
    (scrubSideF_of (withStackScratch_scrubArm sha224_finalize) frameOk_176 _)

/-- `vg_sha224_digest`. -/
theorem digest224 : VerifiedScrubbed target Impl.Sha256.Arm.Fn.digest224
    (Spec.Sha256.digestContract abi 28 Spec.Sha256.sha224 344) 0 :=
  verifiedScrubbedAll (api := Spec.Sha256.digest224Api)
    { code := Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha224H
      verified := Proof.MdStream.Arm.Digest.sha224_digest }
    (postOut_of_local (leak := none) ScrubAbi.plain
      (Proof.Sha256.digestPost_out 28 Spec.Sha256.sha224 _ (by decide)))
    (scrubSideF_of (CodeOk.mono (digest_scrubArm Proof.Pbkdf2.Stream.Arm.sha224H (block_scrubArm _)
      sha256_update sha256_finalize) (by decide)) frameOk_344 _)

/-- `vg_sha256_digest`. -/
theorem digest : VerifiedScrubbed target Impl.Sha256.Arm.Fn.digest
    (Spec.Sha256.digestContract abi 32 Spec.Sha256.hash 344) 0 :=
  verifiedScrubbedAll (api := Spec.Sha256.digest256Api)
    { code := Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha256H
      verified := Proof.MdStream.Arm.Digest.sha256_digest }
    (postOut_of_local (leak := none) ScrubAbi.plain
      (Proof.Sha256.digestPost_out 32 Spec.Sha256.hash _ (by decide)))
    (scrubSideF_of (CodeOk.mono (digest_scrubArm Proof.Pbkdf2.Stream.Arm.sha256H (block_scrubArm _)
      sha256_update sha256_finalize) (by decide)) frameOk_344 _)

end VG.Proof.Sha256.Arm.Fn

/-! ## SHA-384, SHA-512, SHA-512/224 and SHA-512/256 -/

namespace VG.Proof.Sha512.Arm.Fn

open VG VG.Arm VG.Arm.Scrub VG.Proof.MdStream.Arm.ShaScrub

/-- `vg_sha384_init`. -/
theorem init384 : VerifiedScrubbed target Impl.Sha512.Arm.Fn.init384 (Spec.Sha512.initContract abi Spec.Sha512.H0_384) 0 :=
  verifiedScrubbed (api := Spec.Sha512.init384Api)
    { code := Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_384
      verified := Proof.Sha512.Arm.Shared.init Spec.Sha512.H0_384 } rfl

/-- `vg_sha512_init`. -/
theorem init512 : VerifiedScrubbed target Impl.Sha512.Arm.Fn.init512 (Spec.Sha512.initContract abi Spec.Sha512.H0_512) 0 :=
  verifiedScrubbed (api := Spec.Sha512.init512Api)
    { code := Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_512
      verified := Proof.Sha512.Arm.Shared.init Spec.Sha512.H0_512 } rfl

/-- `vg_sha512_224_init`. -/
theorem init512_224 : VerifiedScrubbed target Impl.Sha512.Arm.Fn.init512_224 (Spec.Sha512.initContract abi Spec.Sha512.H0_512_224) 0 :=
  verifiedScrubbed (api := Spec.Sha512.init512_224Api)
    { code := Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_512_224
      verified := Proof.Sha512.Arm.Shared.init Spec.Sha512.H0_512_224 } rfl

/-- `vg_sha512_256_init`. -/
theorem init512_256 : VerifiedScrubbed target Impl.Sha512.Arm.Fn.init512_256 (Spec.Sha512.initContract abi Spec.Sha512.H0_512_256) 0 :=
  verifiedScrubbed (api := Spec.Sha512.init512_256Api)
    { code := Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_512_256
      verified := Proof.Sha512.Arm.Shared.init Spec.Sha512.H0_512_256 } rfl

/-- `vg_sha512_update`, which the truncations share. -/
theorem update : VerifiedScrubbed target Impl.Sha512.Arm.Fn.update (Spec.Sha512.updateContract abi 288) 0 :=
  verifiedScrubbedAll (api := Spec.Sha512.updateApi)
    { code := Impl.StackScratch.Arm.withStackScratch 288 2 Impl.Sha512.Arm.Stream.update
      verified := sha512Update288 }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.updatePost_out _))
    (scrubSideF_of (withStackScratch_scrubArm sha512_update) frameOk_288 _)

/-- `vg_sha512_finalize`. -/
theorem finalize :
    VerifiedScrubbed target Impl.Sha512.Arm.Fn.finalize (Spec.Sha512.finalizeContract abi 288) 0 :=
  verifiedScrubbedAll (api := Spec.Sha512.finalizeApi)
    { code := Impl.StackScratch.Arm.withStackScratch 288 1 Impl.Sha512.Arm.Stream.finalize
      verified := sha512Finalize288 }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.finalizePost_out _))
    (scrubSideF_of (withStackScratch_scrubArm sha512_finalize) frameOk_288 _)

/-- `vg_sha384_finalize`. -/
theorem finalize384 : VerifiedScrubbed target Impl.Sha512.Arm.Fn.finalize384
    (Spec.Sha512.finalizeDigestContract abi Spec.Sha512.H0_384 48 Spec.Sha512.sha384 288) 0 :=
  verifiedScrubbedAll (api := Spec.Sha512.finalize384Api)
    { code := Impl.StackScratch.Arm.withStackScratch 288 1
        (Impl.Sha512.Arm.Stream.finalizeDigest Impl.Sha512.Arm.Stream.params384)
      verified := sha384Finalize288 }
    (postOut_of_local (leak := none) ScrubAbi.plain
      (Proof.Sha512.finalizeDigestPost_out Spec.Sha512.H0_384 48 Spec.Sha512.sha384 _ (by decide)))
    (scrubSideF_of (finalizeDigest_scrubArm _) frameOk_288 _)

/-- `vg_sha512_256_finalize`. -/
theorem finalize512_256 : VerifiedScrubbed target Impl.Sha512.Arm.Fn.finalize512_256
    (Spec.Sha512.finalizeDigestContract abi Spec.Sha512.H0_512_256 32 Spec.Sha512.sha512_256 288) 0 :=
  verifiedScrubbedAll (api := Spec.Sha512.finalize512_256Api)
    { code := Impl.StackScratch.Arm.withStackScratch 288 1
        (Impl.Sha512.Arm.Stream.finalizeDigest Impl.Sha512.Arm.Stream.params512_256)
      verified := sha512_256Finalize288 }
    (postOut_of_local (leak := none) ScrubAbi.plain
      (Proof.Sha512.finalizeDigestPost_out Spec.Sha512.H0_512_256 32 Spec.Sha512.sha512_256 _ (by decide)))
    (scrubSideF_of (finalizeDigest_scrubArm _) frameOk_288 _)

/-- `vg_sha512_224_finalize`. -/
theorem finalize512_224 : VerifiedScrubbed target Impl.Sha512.Arm.Fn.finalize512_224
    (Spec.Sha512.finalizeDigestContract abi Spec.Sha512.H0_512_224 28 Spec.Sha512.sha512_224 288) 0 :=
  verifiedScrubbedAll (api := Spec.Sha512.finalize512_224Api)
    { code := Impl.StackScratch.Arm.withStackScratch 288 1
        (Impl.Sha512.Arm.Stream.finalizeDigest Impl.Sha512.Arm.Stream.params512_224)
      verified := sha512_224Finalize288 }
    (postOut_of_local (leak := none) ScrubAbi.plain
      (Proof.Sha512.finalizeDigestPost_out Spec.Sha512.H0_512_224 28 Spec.Sha512.sha512_224 _ (by decide)))
    (scrubSideF_of (finalizeDigest_scrubArm _) frameOk_288 _)

/-- `vg_sha384_digest`. -/
theorem digest384 : VerifiedScrubbed target Impl.Sha512.Arm.Fn.digest384
    (Spec.Sha512.digestContract abi 48 Spec.Sha512.sha384 584) 0 :=
  verifiedScrubbedAll (api := Spec.Sha512.digest384Api)
    { code := Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha384H
      verified := Proof.MdStream.Arm.Digest.sha384_digest }
    (postOut_of_local (leak := none) ScrubAbi.plain
      (Proof.Sha512.digestPost_out 48 Spec.Sha512.sha384 _ (by decide)))
    (scrubSideF_of (CodeOk.mono (digest_scrubArm Proof.Pbkdf2.Stream.Arm.sha384H (block_scrubArm _)
      sha512_update sha512_finalize) (by decide)) frameOk_584 _)

/-- `vg_sha512_digest`. -/
theorem digest512 : VerifiedScrubbed target Impl.Sha512.Arm.Fn.digest512
    (Spec.Sha512.digestContract abi 64 Spec.Sha512.sha512 584) 0 :=
  verifiedScrubbedAll (api := Spec.Sha512.digest512Api)
    { code := Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha512H'
      verified := Proof.MdStream.Arm.Digest.sha512_digest }
    (postOut_of_local (leak := none) ScrubAbi.plain
      (Proof.Sha512.digestPost_out 64 Spec.Sha512.sha512 _ (by decide)))
    (scrubSideF_of (CodeOk.mono (digest_scrubArm Proof.Pbkdf2.Stream.Arm.sha512H' (block_scrubArm _)
      sha512_update sha512_finalize) (by decide)) frameOk_584 _)

/-- `vg_sha512_224_digest`. -/
theorem digest512_224 : VerifiedScrubbed target Impl.Sha512.Arm.Fn.digest512_224
    (Spec.Sha512.digestContract abi 28 Spec.Sha512.sha512_224 584) 0 :=
  verifiedScrubbedAll (api := Spec.Sha512.digest512_224Api)
    { code := Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha512_224H
      verified := Proof.MdStream.Arm.Digest.sha512_224_digest }
    (postOut_of_local (leak := none) ScrubAbi.plain
      (Proof.Sha512.digestPost_out 28 Spec.Sha512.sha512_224 _ (by decide)))
    (scrubSideF_of (CodeOk.mono (digest_scrubArm Proof.Pbkdf2.Stream.Arm.sha512_224H (block_scrubArm _)
      sha512_update sha512_finalize) (by decide)) frameOk_584 _)

/-- `vg_sha512_256_digest`. -/
theorem digest512_256 : VerifiedScrubbed target Impl.Sha512.Arm.Fn.digest512_256
    (Spec.Sha512.digestContract abi 32 Spec.Sha512.sha512_256 584) 0 :=
  verifiedScrubbedAll (api := Spec.Sha512.digest512_256Api)
    { code := Impl.MdStream.Arm.Digest.digest Proof.Pbkdf2.Stream.Arm.sha512_256H
      verified := Proof.MdStream.Arm.Digest.sha512_256_digest }
    (postOut_of_local (leak := none) ScrubAbi.plain
      (Proof.Sha512.digestPost_out 32 Spec.Sha512.sha512_256 _ (by decide)))
    (scrubSideF_of (CodeOk.mono (digest_scrubArm Proof.Pbkdf2.Stream.Arm.sha512_256H (block_scrubArm _)
      sha512_update sha512_finalize) (by decide)) frameOk_584 _)

end VG.Proof.Sha512.Arm.Fn
