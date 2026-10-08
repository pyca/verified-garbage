import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Sha512.Arm.Compress
import VerifiedGarbage.Proof.Sha512.Arm.Stream.Finalize
import VerifiedGarbage.Proof.Sha512.Arm.Stream.Digest
import VerifiedGarbage.Proof.Sha512.Arm.Stream.Init
import VerifiedGarbage.Proof.Sha512.Arm.Stream.Update
import VerifiedGarbage.Spec.Sha512.Contract
import VerifiedGarbage.Proof.Sha512.Scratch
import VerifiedGarbage.Proof.Framework.Arm.StackScratch

/-!
# Sha512 on Arm: the shared contracts

The proofs are written against per-target contracts
(`Proof/Sha512/Arm/Compress.lean`); these theorems move them to the shared
contracts of `Spec/Sha512/Contract.lean`, which the artifacts are emitted
with.

The shared contracts give the functions more scratch than these ones use (1328
bytes for `compress`, 1376 for `update` and `finalize`, sized for the x86-64
AVX2 compression function): the per-target contracts are first widened to
that scratch (`Verified.widen`, the same code running with the same trace and
result), then moved to the shared ones.

`update` and `finalize` keep their working space in a frame of their own:
they are `updateScratch` and `finalizeScratch` (the shared contracts with
the working space as an argument, which HMAC's, PBKDF2's and Ed25519's code
calls) run in a frame that allocates it (`Verified.stackScratch`).
-/

namespace VG.Proof.Sha512.Arm.Shared

open _root_.VG.Arm

/-- `compressArm` with 1328 bytes of scratch. -/
def compressWide : Contract Arm.isa :=
  { Proof.Sha512.compressArm with
    pre := fun s =>
      let state : Region := ⟨State.addr (s.gpr .r0), 64⟩
      let blocks : Region := ⟨State.addr (s.gpr .r1), 128 * (s.gpr .r2).toNat⟩
      let scratch : Region := ⟨State.addr (s.gpr .r3), 1328⟩
      s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
      (s.gpr .r0).toNat + 64 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 128 * (s.gpr .r2).toNat ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 1328 ≤ 2 ^ 32 }

/-- `updateArm` with 1376 bytes of scratch. -/
def updateWide : Contract Arm.isa :=
  { Proof.Sha512.updateArm with
    pre := fun s =>
      let state : Region := ⟨State.addr (s.gpr .r0), 192⟩
      let data : Region := ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
      let scratch : Region := ⟨State.addr (stackArg s 2), 1376⟩
      let args : Region := ⟨stackArgAddr s 0, 12⟩
      s.rd = [data, args] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
      args.Disjoint state ∧ args.Disjoint scratch ∧
      (s.gpr .r0).toNat + 192 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 32 ∧
      (stackArg s 2).toNat + 1376 ≤ 2 ^ 32 ∧ s.sp.toNat + 12 ≤ 2 ^ 32 }

/-- `finalizeArm` with 1376 bytes of scratch. -/
def finalizeWide : Contract Arm.isa :=
  { Proof.Sha512.finalizeArm with
    pre := fun s =>
      let state : Region := ⟨State.addr (s.gpr .r0), 192⟩
      let out : Region := ⟨State.addr (stackArg s 0), 64⟩
      let scratch : Region := ⟨State.addr (stackArg s 1), 1376⟩
      let args : Region := ⟨stackArgAddr s 0, 8⟩
      s.rd = [args] ∧ s.wr = [state, out, scratch] ∧
      state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
      args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      (s.gpr .r0).toNat + 192 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 64 ≤ 2 ^ 32 ∧
      (stackArg s 1).toNat + 1376 ≤ 2 ^ 32 ∧ s.sp.toNat + 8 ≤ 2 ^ 32 }

theorem pfx {a : Addr} {m n : Nat} (h : Nat.ble m n = true) : Region.Prefix ⟨a, m⟩ ⟨a, n⟩ :=
  ⟨rfl, Nat.le_of_ble_eq_true h⟩
theorem sub224 (a : Addr) : Region.Sub ⟨a, 224⟩ ⟨a, 1328⟩ := Region.sub_prefix (by decide)
theorem sub272 (a : Addr) : Region.Sub ⟨a, 272⟩ ⟨a, 1376⟩ := Region.sub_prefix (by decide)
theorem le224 {x : Nat} (h : x + 1328 ≤ 2 ^ 32) : x + 224 ≤ 2 ^ 32 := by omega
theorem le272 {x : Nat} (h : x + 1376 ≤ 2 ^ 32) : x + 272 ≤ 2 ^ 32 := by omega

/-- Rewrites the per-target contracts at a narrowed state (`stackArg` does
not unfold cheaply). -/
macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [Proof.Sha512.compressArm, Proof.Sha512.updateArm, Proof.Sha512.finalizeArm,
    Proof.Sha512.countArm, compressWide, updateWide, finalizeWide, VG.Arm.stackArg_withRegions,
    VG.Arm.stackArgAddr_withRegions, State.withRegions_gpr, State.withRegions_sp, State.withRegions_mem,
    State.withRegions_rd, State.withRegions_wr] $(loc)?)

theorem compressWide_verified (hsat : ∃ s, compressWide.pre s) :
    Verified Arm.target Impl.Sha512.Arm.compress compressWide :=
  Verified.widen Proof.Sha512.Arm.Compress.compress_verified
    (fun s => [⟨State.addr (s.gpr .r0), 64⟩, ⟨State.addr (s.gpr .r3), 224⟩])
    (fun _ h => by
      obtain ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈⟩ := h
      narrow
      exact ⟨h₁, trivial, h₃.sub_right (sub224 _), h₄, h₅.sub_right (sub224 _), h₆, h₇, le224 h₈⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]; exact .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat

theorem updateWide_verified (hsat : ∃ s, updateWide.pre s) :
    Verified Arm.target Impl.Sha512.Arm.Stream.update updateWide :=
  Verified.widen Proof.Sha512.Arm.Stream.Update.update_verified
    (fun s => [⟨State.addr (s.gpr .r0), 192⟩, ⟨State.addr (stackArg s 2), 272⟩])
    (fun _ h => by
      obtain ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁⟩ := h
      narrow
      exact ⟨h₁, trivial, h₃.sub_right (sub272 _), h₄, h₅.sub_right (sub272 _), h₆,
        h₇.sub_right (sub272 _), h₈, h₉, le272 h₁₀, h₁₁⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]; exact .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat

theorem finalizeWide_verified (hsat : ∃ s, finalizeWide.pre s) :
    Verified Arm.target Impl.Sha512.Arm.Stream.finalize finalizeWide :=
  Verified.widen Proof.Sha512.Arm.Stream.Finalize.finalize_verified
    (fun s => [⟨State.addr (s.gpr .r0), 192⟩, ⟨State.addr (stackArg s 0), 64⟩,
      ⟨State.addr (stackArg s 1), 272⟩])
    (fun _ h => by
      obtain ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂⟩ := h
      narrow
      exact ⟨h₁, trivial, h₃, h₄.sub_right (sub272 _), h₅.sub_right (sub272 _), h₆, h₇,
        h₈.sub_right (sub272 _), h₉, h₁₀, le272 h₁₁, h₁₂⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]; exact .cons (pfx rfl) (.cons (pfx rfl) (.cons (pfx rfl) .nil)))
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat

/-- A state satisfying `compressWide.pre`. -/
def compressSat : State :=
  { Proof.Sha512.Arm.Compress.satState with wr := [⟨0x1000, 64⟩, ⟨0x3000, 1328⟩] }

/-- A state satisfying `updateWide.pre`. -/
def updateSat : State := { Proof.Sha512.Arm.Stream.Update.sat with wr := [⟨0x1000, 192⟩, ⟨0, 1376⟩] }

/-- A state satisfying `finalizeWide.pre`. -/
def finalizeSat : State :=
  { Proof.Sha512.Arm.Stream.Finalize.sat with wr := [⟨0x1000, 192⟩, ⟨0x2000, 64⟩, ⟨0x3000, 1376⟩] }

theorem compressWide_implies : compressWide.Implies (Spec.Sha512.compressContract Arm.abi) := by
  sig_implies [Spec.Sha512.compressContract, Spec.Sha512.compressSig, compressWide,
    Proof.Sha512.compressArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [compressSat, Proof.Sha512.Arm.Compress.satState, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
    Mem.read] using compressSat

theorem compress :
    Verified Arm.target Impl.Sha512.Arm.compress (Spec.Sha512.compressContract Arm.abi) :=
  (compressWide_verified compressWide_implies.sat_left).of_implies compressWide_implies

theorem init (iv : Spec.Sha512.HashValue) :
    Verified Arm.target (Impl.Sha512.Arm.Stream.init iv) (Spec.Sha512.initContract Arm.abi iv) :=
  (Proof.Sha512.Arm.Stream.init_verified iv).of_implies (by
    contract_implies [Spec.Sha512.initContract, Spec.Sha512.initSig, Proof.Sha512.initArm, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Sha512.Arm.Stream.initSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
      Mem.read] using Proof.Sha512.Arm.Stream.initSat)

theorem updateWide_implies : updateWide.Implies (Spec.Sha512.updateScratchContract Arm.abi) := by
  sig_implies [Spec.Sha512.updateScratchContract, Spec.Sha512.updateScratchSig, updateWide, Proof.Sha512.updateArm,
    Proof.Sha512.countArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [updateSat, Proof.Sha512.Arm.Stream.Update.sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
    Mem.read] using updateSat

theorem updateScratch :
    Verified Arm.target Impl.Sha512.Arm.Stream.update (Spec.Sha512.updateScratchContract Arm.abi) :=
  (updateWide_verified updateWide_implies.sat_left).of_implies updateWide_implies

theorem finalizeWide_implies : finalizeWide.Implies (Spec.Sha512.finalizeScratchContract Arm.abi) := by
  contract_implies [Spec.Sha512.finalizeScratchContract, Spec.Sha512.finalizeScratchSig, finalizeWide,
    Proof.Sha512.finalizeArm, Proof.Sha512.countArm, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr]
    [finalizeSat, Proof.Sha512.Arm.Stream.Finalize.sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
    Mem.read] using finalizeSat

theorem finalizeScratch :
    Verified Arm.target Impl.Sha512.Arm.Stream.finalize (Spec.Sha512.finalizeScratchContract Arm.abi) :=
  (finalizeWide_verified finalizeWide_implies.sat_left).of_implies finalizeWide_implies

/-- A state satisfying `update`'s precondition. -/
def updateFrameSat : State :=
  { Proof.Sha512.Arm.Stream.Update.sat with rd := [⟨0, 0⟩, ⟨0x4000, 8⟩], wr := [⟨0x1000, 192⟩] }

theorem update : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratch 1392 2 Impl.Sha512.Arm.Stream.update)
    (Spec.Sha512.updateContract Arm.abi 1392) :=
  Arm.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 172) (stack := 0) (bytes := 1392) (m := 2)
    updateScratch (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sha512.updatePost_local _)
    (by implies_sat [Spec.Sha512.updateContract, Spec.Sha512.updateSig, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [updateFrameSat, Proof.Sha512.Arm.Stream.Update.sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
        Mem.read] using updateFrameSat)

/-- A state satisfying `finalize`'s precondition. -/
def finalizeFrameSat : State :=
  { MdStream.Arm.Finalize.satBase with rd := [⟨0x5000, 4⟩], wr := [⟨0x1000, 192⟩, ⟨0x2000, 64⟩] }

theorem finalize : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratch 1392 1 Impl.Sha512.Arm.Stream.finalize)
    (Spec.Sha512.finalizeContract Arm.abi 1392) :=
  Arm.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 172) (stack := 0) (bytes := 1392) (m := 1)
    finalizeScratch (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sha512.finalizePost_local _)
    (by implies_sat [Spec.Sha512.finalizeContract, Spec.Sha512.finalizeSig, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [finalizeFrameSat, MdStream.Arm.Finalize.satBase, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
        Mem.read] using finalizeFrameSat)

/-! ## The truncated digests

`finalizeDigest` (SHA-384's, SHA-512/256's and SHA-512/224's `finalize`) is
verified against `finKD`; widened to the shared scratch, for the algorithm's
initial hash value, and with its working space in a frame of its own, it is
`Spec.Sha512.finalizeDigestContract`. -/

/-- `finalizeWide` for the `D`-byte `digest` of the messages hashed from `iv`. -/
def finalizeDigestWide (iv : Spec.Sha512.HashValue) (D : Nat) (digest : List Byte → List Byte) :
    Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 192⟩
    let out : Region := ⟨State.addr (stackArg s 0), D⟩
    let scratch : Region := ⟨State.addr (stackArg s 1), 1376⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    s.rd = [args] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + 192 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + D ≤ 2 ^ 32 ∧
    (stackArg s 1).toNat + 1376 ≤ 2 ^ 32 ∧ s.sp.toNat + 8 ≤ 2 ^ 32
  post s s' := ∀ m, Spec.Sha512.Repr iv s.mem (State.addr (s.gpr .r0)) m → m.length < 2 ^ 64 →
    Proof.Sha512.countArm s = BitVec.ofNat 64 m.length →
    Spec.Sha512.bytesAt s'.mem (State.addr (stackArg s 0)) D = digest m
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

/-- Rewrites `finKD` and `finalizeDigestWide` at a narrowed state. -/
macro "narrowD" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [MdStream.Arm.finKD, Proof.Sha512.countArm, finalizeDigestWide, MdStream.Arm.count,
    VG.Arm.stackArg_withRegions, VG.Arm.stackArgAddr_withRegions, State.withRegions_gpr, State.withRegions_sp,
    State.withRegions_mem, State.withRegions_rd, State.withRegions_wr] $(loc)?)

theorem finalizeDigestWide_verified {code : Prog Arm.isa} {o : List Instr} {D : Nat}
    {iv : Spec.Sha512.HashValue} {digest : List Byte → List Byte}
    (hv : Verified Arm.target code
      (MdStream.Arm.finKD (P := { Impl.Sha512.Arm.Stream.params with out := o }) Proof.Sha512.md D))
    (hdg : ∀ m, (Proof.Sha512.md.hash iv m).take D = digest m)
    (hsat : ∃ s, (finalizeDigestWide iv D digest).pre s) :
    Verified Arm.target code (finalizeDigestWide iv D digest) :=
  Verified.widen hv
    (fun s => [⟨State.addr (s.gpr .r0), 192⟩, ⟨State.addr (stackArg s 0), D⟩,
      ⟨State.addr (stackArg s 1), 272⟩])
    (fun _ h => by
      obtain ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂⟩ := h
      narrowD
      exact ⟨h₁, rfl, h₃, h₄.sub_right (sub272 _), h₅.sub_right (sub272 _), h₆, h₇,
        h₈.sub_right (sub272 _), h₉, h₁₀, le272 h₁₁, h₁₂⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]; exact .cons (pfx rfl) (.cons ⟨rfl, Nat.le_refl _⟩ (.cons (pfx rfl) .nil)))
    (fun _ _ _ h => by
      narrowD at h ⊢
      intro m hr hl hc
      exact (h iv m hr hl hc).trans (hdg m))
    (fun _ _ _ _ h => by narrowD; exact h) hsat

/-- A state satisfying `finalizeDigestWide.pre`. -/
def finalizeDigestSat (D : Nat) : State :=
  { Proof.Sha512.Arm.Stream.Finalize.satD D with wr := [⟨0x1000, 192⟩, ⟨0x2000, D⟩, ⟨0x3000, 1376⟩] }

theorem finalizeDigestWide_implies48 (iv : Spec.Sha512.HashValue) (digest : List Byte → List Byte) :
    (finalizeDigestWide iv 48 digest).Implies (finalizeDigestScratchContract Arm.abi iv 48 digest 0) := by
  contract_implies [Proof.Sha512.finalizeDigestScratchContract, Proof.Sha512.finalizeDigestScratchSig,
    Spec.Sha512.finalizeDigestPost, finalizeDigestWide, Proof.Sha512.countArm, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finalizeDigestSat, Proof.Sha512.Arm.Stream.Finalize.satD, MdStream.Arm.Finalize.satD,
      MdStream.Arm.Finalize.satBase, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using finalizeDigestSat 48

theorem finalizeDigestWide_implies32 (iv : Spec.Sha512.HashValue) (digest : List Byte → List Byte) :
    (finalizeDigestWide iv 32 digest).Implies (finalizeDigestScratchContract Arm.abi iv 32 digest 0) := by
  contract_implies [Proof.Sha512.finalizeDigestScratchContract, Proof.Sha512.finalizeDigestScratchSig,
    Spec.Sha512.finalizeDigestPost, finalizeDigestWide, Proof.Sha512.countArm, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finalizeDigestSat, Proof.Sha512.Arm.Stream.Finalize.satD, MdStream.Arm.Finalize.satD,
      MdStream.Arm.Finalize.satBase, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using finalizeDigestSat 32

theorem finalizeDigestWide_implies28 (iv : Spec.Sha512.HashValue) (digest : List Byte → List Byte) :
    (finalizeDigestWide iv 28 digest).Implies (finalizeDigestScratchContract Arm.abi iv 28 digest 0) := by
  contract_implies [Proof.Sha512.finalizeDigestScratchContract, Proof.Sha512.finalizeDigestScratchSig,
    Spec.Sha512.finalizeDigestPost, finalizeDigestWide, Proof.Sha512.countArm, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finalizeDigestSat, Proof.Sha512.Arm.Stream.Finalize.satD, MdStream.Arm.Finalize.satD,
      MdStream.Arm.Finalize.satBase, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using finalizeDigestSat 28

theorem finalizeDigestScratch {code : Prog Arm.isa} {o : List Instr} {D : Nat}
    {iv : Spec.Sha512.HashValue} {digest : List Byte → List Byte} (hD : D = 48 ∨ D = 32 ∨ D = 28)
    (hv : Verified Arm.target code
      (MdStream.Arm.finKD (P := { Impl.Sha512.Arm.Stream.params with out := o }) Proof.Sha512.md D))
    (hdg : ∀ m, (Proof.Sha512.md.hash iv m).take D = digest m) :
    Verified Arm.target code (finalizeDigestScratchContract Arm.abi iv D digest 0) := by
  have hi : (finalizeDigestWide iv D digest).Implies (finalizeDigestScratchContract Arm.abi iv D digest 0) := by
    rcases hD with rfl | rfl | rfl
    exacts [finalizeDigestWide_implies48 iv digest, finalizeDigestWide_implies32 iv digest,
      finalizeDigestWide_implies28 iv digest]
  exact (finalizeDigestWide_verified hv hdg hi.sat_left).of_implies hi

/-- A state satisfying `Spec.Sha512.finalizeDigestContract`'s precondition. -/
def finalizeDigestFrameSat (D : Nat) : State :=
  { MdStream.Arm.Finalize.satBase with rd := [⟨0x5000, 4⟩], wr := [⟨0x1000, 192⟩, ⟨0x2000, D⟩] }

theorem finalizeDigestStack48 {code : Prog Arm.isa} {iv : Spec.Sha512.HashValue}
    {digest : List Byte → List Byte}
    (hv : Verified Arm.target code (finalizeDigestScratchContract Arm.abi iv 48 digest 0)) :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 1392 1 code)
      (Spec.Sha512.finalizeDigestContract Arm.abi iv 48 digest 1392) :=
  Arm.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 172) (stack := 0) (bytes := 1392) (m := 1)
    hv (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sha512.finalizeDigestPost_local _ _ _ _)
    (by implies_sat [Spec.Sha512.finalizeDigestContract, Spec.Sha512.finalizeDigestSig, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [finalizeDigestFrameSat, MdStream.Arm.Finalize.satBase, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
        Mem.read] using finalizeDigestFrameSat 48)

theorem finalizeDigestStack32 {code : Prog Arm.isa} {iv : Spec.Sha512.HashValue}
    {digest : List Byte → List Byte}
    (hv : Verified Arm.target code (finalizeDigestScratchContract Arm.abi iv 32 digest 0)) :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 1392 1 code)
      (Spec.Sha512.finalizeDigestContract Arm.abi iv 32 digest 1392) :=
  Arm.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 172) (stack := 0) (bytes := 1392) (m := 1)
    hv (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sha512.finalizeDigestPost_local _ _ _ _)
    (by implies_sat [Spec.Sha512.finalizeDigestContract, Spec.Sha512.finalizeDigestSig, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [finalizeDigestFrameSat, MdStream.Arm.Finalize.satBase, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
        Mem.read] using finalizeDigestFrameSat 32)

theorem finalizeDigestStack28 {code : Prog Arm.isa} {iv : Spec.Sha512.HashValue}
    {digest : List Byte → List Byte}
    (hv : Verified Arm.target code (finalizeDigestScratchContract Arm.abi iv 28 digest 0)) :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 1392 1 code)
      (Spec.Sha512.finalizeDigestContract Arm.abi iv 28 digest 1392) :=
  Arm.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 172) (stack := 0) (bytes := 1392) (m := 1)
    hv (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sha512.finalizeDigestPost_local _ _ _ _)
    (by implies_sat [Spec.Sha512.finalizeDigestContract, Spec.Sha512.finalizeDigestSig, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [finalizeDigestFrameSat, MdStream.Arm.Finalize.satBase, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
        Mem.read] using finalizeDigestFrameSat 28)

theorem finalize384 : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratch 1392 1
      (Impl.Sha512.Arm.Stream.finalizeDigest Impl.Sha512.Arm.Stream.params384))
    (Spec.Sha512.finalizeDigestContract Arm.abi Spec.Sha512.H0_384 48 Spec.Sha512.sha384 1392) :=
  finalizeDigestStack48 (finalizeDigestScratch (.inl rfl) Proof.Sha512.Arm.Stream.Finalize.finalize384_verified (fun _ => rfl))

theorem finalize512_256 : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratch 1392 1
      (Impl.Sha512.Arm.Stream.finalizeDigest Impl.Sha512.Arm.Stream.params512_256))
    (Spec.Sha512.finalizeDigestContract Arm.abi Spec.Sha512.H0_512_256 32 Spec.Sha512.sha512_256 1392) :=
  finalizeDigestStack32 (finalizeDigestScratch (.inr (.inl rfl)) Proof.Sha512.Arm.Stream.Finalize.finalize512_256_verified (fun _ => rfl))

theorem finalize512_224 : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratch 1392 1
      (Impl.Sha512.Arm.Stream.finalizeDigest Impl.Sha512.Arm.Stream.params512_224))
    (Spec.Sha512.finalizeDigestContract Arm.abi Spec.Sha512.H0_512_224 28 Spec.Sha512.sha512_224 1392) :=
  finalizeDigestStack28 (finalizeDigestScratch (.inr (.inr rfl)) Proof.Sha512.Arm.Stream.Finalize.finalize512_224_verified (fun _ => rfl))

end VG.Proof.Sha512.Arm.Shared
