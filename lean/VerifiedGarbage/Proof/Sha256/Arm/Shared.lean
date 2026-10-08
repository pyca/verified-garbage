import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Sha256.Arm.Compress
import VerifiedGarbage.Proof.Sha256.Arm.Stream.Init
import VerifiedGarbage.Proof.Sha256.Arm.Stream.Md
import VerifiedGarbage.Proof.Sha256.Arm.Stream.Digest
import VerifiedGarbage.Spec.Sha256.Contract
import VerifiedGarbage.Proof.Sha256.Scratch
import VerifiedGarbage.Proof.Framework.Arm.StackScratch

/-!
# Sha256 on Arm: the shared contracts

The proofs are written against per-target contracts
(`Proof/Sha256/Arm/Contract.lean`); these theorems move them to the shared
contracts of `Spec/Sha256/Contract.lean`, which the artifacts are emitted
with.

The shared contracts give the functions more scratch than these ones use (560
bytes for `compress`, 608 for `update` and `finalize`, sized for the x86-64
AVX2 compression function): the per-target contracts are first widened to
that scratch (`Verified.widen`, the same code running with the same trace and
result), then moved to the shared ones.

`update` and `finalize` keep their working space in a frame of their own:
they are `updateScratch` and `finalizeScratch` (the shared contracts with
the working space as an argument, which HMAC's and PBKDF2's code calls) run
in a frame that allocates it (`Verified.stackScratch`).
-/

namespace VG.Proof.Sha256.Arm.Shared

open _root_.VG.Arm

/-- `compressArm` with 560 bytes of scratch. -/
def compressWide : Contract Arm.isa :=
  { Proof.Sha256.compressArm with
    pre := fun s =>
      let state : Region := ⟨State.addr (s.gpr .r0), 32⟩
      let blocks : Region := ⟨State.addr (s.gpr .r1), 64 * (s.gpr .r2).toNat⟩
      let scratch : Region := ⟨State.addr (s.gpr .r3), 560⟩
      s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
      (s.gpr .r0).toNat + 32 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 64 * (s.gpr .r2).toNat ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 560 ≤ 2 ^ 32 }

/-- `updateArm` with 608 bytes of scratch. -/
def updateWide : Contract Arm.isa :=
  { Proof.Sha256.updateArm with
    pre := fun s =>
      let state : Region := ⟨State.addr (s.gpr .r0), 96⟩
      let data : Region := ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
      let scratch : Region := ⟨State.addr (stackArg s 2), 608⟩
      let args : Region := ⟨stackArgAddr s 0, 12⟩
      s.rd = [data, args] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
      args.Disjoint state ∧ args.Disjoint scratch ∧
      (s.gpr .r0).toNat + 96 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 32 ∧
      (stackArg s 2).toNat + 608 ≤ 2 ^ 32 ∧ s.sp.toNat + 12 ≤ 2 ^ 32 }

/-- `finalizeArm` with 608 bytes of scratch. -/
def finalizeWide : Contract Arm.isa :=
  { Proof.Sha256.finalizeArm with
    pre := fun s =>
      let state : Region := ⟨State.addr (s.gpr .r0), 96⟩
      let out : Region := ⟨State.addr (stackArg s 0), 32⟩
      let scratch : Region := ⟨State.addr (stackArg s 1), 608⟩
      let args : Region := ⟨stackArgAddr s 0, 8⟩
      s.rd = [args] ∧ s.wr = [state, out, scratch] ∧
      state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
      args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      (s.gpr .r0).toNat + 96 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 32 ≤ 2 ^ 32 ∧
      (stackArg s 1).toNat + 608 ≤ 2 ^ 32 ∧ s.sp.toNat + 8 ≤ 2 ^ 32 }

theorem pfx {a : Addr} {m n : Nat} (h : Nat.ble m n = true) : Region.Prefix ⟨a, m⟩ ⟨a, n⟩ :=
  ⟨rfl, Nat.le_of_ble_eq_true h⟩
theorem sub112 (a : Addr) : Region.Sub ⟨a, 112⟩ ⟨a, 560⟩ := Region.sub_prefix (by decide)
theorem sub160 (a : Addr) : Region.Sub ⟨a, 160⟩ ⟨a, 608⟩ := Region.sub_prefix (by decide)
theorem le112 {x : Nat} (h : x + 560 ≤ 2 ^ 32) : x + 112 ≤ 2 ^ 32 := by omega
theorem le160 {x : Nat} (h : x + 608 ≤ 2 ^ 32) : x + 160 ≤ 2 ^ 32 := by omega

/-- Rewrites the per-target contracts at a narrowed state (`stackArg` does
not unfold cheaply). -/
macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [Proof.Sha256.compressArm, Proof.Sha256.updateArm, Proof.Sha256.finalizeArm,
    Proof.Sha256.countArm, compressWide, updateWide, finalizeWide, VG.Arm.stackArg_withRegions,
    VG.Arm.stackArgAddr_withRegions, State.withRegions_gpr, State.withRegions_sp, State.withRegions_mem,
    State.withRegions_rd, State.withRegions_wr] $(loc)?)

theorem compressWide_verified (hsat : ∃ s, compressWide.pre s) :
    Verified Arm.target Impl.Sha256.Arm.compress compressWide :=
  Verified.widen Proof.Sha256.Arm.compress_verified
    (fun s => [⟨State.addr (s.gpr .r0), 32⟩, ⟨State.addr (s.gpr .r3), 112⟩])
    (fun _ h => by
      obtain ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈⟩ := h
      narrow
      exact ⟨h₁, trivial, h₃.sub_right (sub112 _), h₄, h₅.sub_right (sub112 _), h₆, h₇, le112 h₈⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]; exact .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat

theorem updateWide_verified (hsat : ∃ s, updateWide.pre s) :
    Verified Arm.target Impl.Sha256.Arm.Stream.update updateWide :=
  Verified.widen Proof.Sha256.Arm.Stream.Update.update_verified
    (fun s => [⟨State.addr (s.gpr .r0), 96⟩, ⟨State.addr (stackArg s 2), 160⟩])
    (fun _ h => by
      obtain ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁⟩ := h
      narrow
      exact ⟨h₁, trivial, h₃.sub_right (sub160 _), h₄, h₅.sub_right (sub160 _), h₆,
        h₇.sub_right (sub160 _), h₈, h₉, le160 h₁₀, h₁₁⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]; exact .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat

theorem finalizeWide_verified (hsat : ∃ s, finalizeWide.pre s) :
    Verified Arm.target Impl.Sha256.Arm.Stream.finalize finalizeWide :=
  Verified.widen Proof.Sha256.Arm.Stream.Finalize.finalize_verified
    (fun s => [⟨State.addr (s.gpr .r0), 96⟩, ⟨State.addr (stackArg s 0), 32⟩,
      ⟨State.addr (stackArg s 1), 160⟩])
    (fun _ h => by
      obtain ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂⟩ := h
      narrow
      exact ⟨h₁, trivial, h₃, h₄.sub_right (sub160 _), h₅.sub_right (sub160 _), h₆, h₇,
        h₈.sub_right (sub160 _), h₉, h₁₀, le160 h₁₁, h₁₂⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]; exact .cons (pfx rfl) (.cons (pfx rfl) (.cons (pfx rfl) .nil)))
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat

/-- A state satisfying `compressWide.pre`. -/
def compressSat : State := { Proof.Sha256.Arm.satState with wr := [⟨0x1000, 32⟩, ⟨0x3000, 560⟩] }

/-- A state satisfying `updateWide.pre`. -/
def updateSat : State := { Proof.Sha256.Arm.Stream.Update.sat with wr := [⟨0x1000, 96⟩, ⟨0, 608⟩] }

/-- A state satisfying `finalizeWide.pre`. -/
def finalizeSat : State :=
  { Proof.Sha256.Arm.Stream.Finalize.sat with wr := [⟨0x1000, 96⟩, ⟨0x2000, 32⟩, ⟨0x3000, 608⟩] }

theorem compressWide_implies : compressWide.Implies (Spec.Sha256.compressContract Arm.abi) := by
  contract_implies [Spec.Sha256.compressContract, Spec.Sha256.compressSig, compressWide,
    Proof.Sha256.compressArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [compressSat, Proof.Sha256.Arm.satState, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
    Mem.read] using compressSat

theorem compress :
    Verified Arm.target Impl.Sha256.Arm.compress (Spec.Sha256.compressContract Arm.abi) :=
  (compressWide_verified compressWide_implies.sat_left).of_implies compressWide_implies

theorem init : Verified Arm.target Impl.Sha256.Arm.Stream.init (Spec.Sha256.initContract Arm.abi) :=
  Proof.Sha256.Arm.Stream.init_verified.of_implies (by
    contract_implies [Spec.Sha256.initContract, Spec.Sha256.initSig, Proof.Sha256.initArm, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Sha256.Arm.Stream.initSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
      Mem.read] using Proof.Sha256.Arm.Stream.initSat)

theorem init224 : Verified Arm.target Impl.Sha256.Arm.Stream.init224 (Spec.Sha256.init224Contract Arm.abi) :=
  Proof.Sha256.Arm.Stream.init224_verified.of_implies (by
    contract_implies [Spec.Sha256.init224Contract, Spec.Sha256.initSig, Proof.Sha256.initArm, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Sha256.Arm.Stream.initSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
      Mem.read] using Proof.Sha256.Arm.Stream.initSat)

theorem updateWide_implies : updateWide.Implies (Spec.Sha256.updateScratchContract Arm.abi) := by
  contract_implies [Spec.Sha256.updateScratchContract, Spec.Sha256.updateScratchSig, updateWide,
    Proof.Sha256.updateArm, Proof.Sha256.countArm, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr]
    [updateSat, Proof.Sha256.Arm.Stream.Update.sat, MdStream.Arm.Update.sat,
    Impl.Sha256.Arm.Stream.params, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
    Mem.read] using updateSat

theorem updateScratch :
    Verified Arm.target Impl.Sha256.Arm.Stream.update (Spec.Sha256.updateScratchContract Arm.abi) :=
  (updateWide_verified updateWide_implies.sat_left).of_implies updateWide_implies

theorem finalizeWide_implies : finalizeWide.Implies (Spec.Sha256.finalizeScratchContract Arm.abi) := by
  contract_implies [Spec.Sha256.finalizeScratchContract, Spec.Sha256.finalizeScratchSig, finalizeWide,
    Proof.Sha256.finalizeArm, Proof.Sha256.countArm, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr]
    [finalizeSat, Proof.Sha256.Arm.Stream.Finalize.sat, MdStream.Arm.Finalize.sat,
    MdStream.Arm.Finalize.satBase, Impl.Sha256.Arm.Stream.params, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
    Mem.read] using finalizeSat

theorem finalizeScratch :
    Verified Arm.target Impl.Sha256.Arm.Stream.finalize (Spec.Sha256.finalizeScratchContract Arm.abi) :=
  (finalizeWide_verified finalizeWide_implies.sat_left).of_implies finalizeWide_implies

/-- A state satisfying `update`'s precondition. -/
def updateFrameSat : State :=
  { MdStream.Arm.Update.sat Impl.Sha256.Arm.Stream.params with
    rd := [⟨0, 0⟩, ⟨0x4000, 8⟩], wr := [⟨0x1000, 96⟩] }

theorem update : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratch 624 2 Impl.Sha256.Arm.Stream.update)
    (Spec.Sha256.updateContract Arm.abi 624) :=
  Arm.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 76) (stack := 0) (bytes := 624) (m := 2)
    updateScratch (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sha256.updatePost_local _)
    (by implies_sat [Spec.Sha256.updateContract, Spec.Sha256.updateSig, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [updateFrameSat, MdStream.Arm.Update.sat, Impl.Sha256.Arm.Stream.params, Arm.stackArg,
        Arm.stackArgAddr, Mem.readW, Mem.read] using updateFrameSat)

/-- A state satisfying `finalize`'s precondition. -/
def finalizeFrameSat : State :=
  { MdStream.Arm.Finalize.satBase with rd := [⟨0x5000, 4⟩], wr := [⟨0x1000, 96⟩, ⟨0x2000, 32⟩] }

theorem finalize : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratch 624 1 Impl.Sha256.Arm.Stream.finalize)
    (Spec.Sha256.finalizeContract Arm.abi 624) :=
  Arm.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 76) (stack := 0) (bytes := 624) (m := 1)
    finalizeScratch (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sha256.finalizePost_local _)
    (by implies_sat [Spec.Sha256.finalizeContract, Spec.Sha256.finalizeSig, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [finalizeFrameSat, MdStream.Arm.Finalize.satBase, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
        Mem.read] using finalizeFrameSat)

/-! ## SHA-224's digest

`finalize224` is verified against `finKD`; widened to the shared scratch, for
SHA-224's initial hash value, and with its working space in a frame of its
own, it is `Spec.Sha256.finalize224Contract`. -/

/-- `finalizeWide` for SHA-224's digest of the messages hashed from its
initial hash value. -/
def finalize224Wide : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 96⟩
    let out : Region := ⟨State.addr (stackArg s 0), 28⟩
    let scratch : Region := ⟨State.addr (stackArg s 1), 608⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    s.rd = [args] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + 96 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 28 ≤ 2 ^ 32 ∧
    (stackArg s 1).toNat + 608 ≤ 2 ^ 32 ∧ s.sp.toNat + 8 ≤ 2 ^ 32
  post s s' := ∀ m, Spec.Sha256.ReprFrom Spec.Sha256.H0_224 s.mem (State.addr (s.gpr .r0)) m →
    Proof.Sha256.countArm s = BitVec.ofNat 64 m.length →
    Spec.Sha256.bytesAt s'.mem (State.addr (stackArg s 0)) 28 = Spec.Sha256.sha224 m
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

/-- Rewrites `finKD` and `finalize224Wide` at a narrowed state. -/
macro "narrow224" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [MdStream.Arm.finKD, Proof.Sha256.countArm, finalize224Wide, MdStream.Arm.count,
    VG.Arm.stackArg_withRegions, VG.Arm.stackArgAddr_withRegions, State.withRegions_gpr, State.withRegions_sp,
    State.withRegions_mem, State.withRegions_rd, State.withRegions_wr] $(loc)?)

theorem finalize224Wide_verified (hsat : ∃ s, finalize224Wide.pre s) :
    Verified Arm.target Impl.Sha256.Arm.Stream.finalize224 finalize224Wide :=
  Verified.widen Proof.Sha256.Arm.Stream.Finalize.finalize224_verified
    (fun s => [⟨State.addr (s.gpr .r0), 96⟩, ⟨State.addr (stackArg s 0), 28⟩,
      ⟨State.addr (stackArg s 1), 160⟩])
    (fun _ h => by
      obtain ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂⟩ := h
      narrow224
      exact ⟨h₁, rfl, h₃, h₄.sub_right (sub160 _), h₅.sub_right (sub160 _), h₆, h₇,
        h₈.sub_right (sub160 _), h₉, h₁₀, le160 h₁₁, h₁₂⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]; exact .cons (pfx rfl) (.cons ⟨rfl, Nat.le_refl _⟩ (.cons (pfx rfl) .nil)))
    (fun _ _ _ h => by
      narrow224 at h ⊢
      intro m hr hc
      exact (h _ m hr trivial hc).trans (Proof.Sha256.sha224_eq m))
    (fun _ _ _ _ h => by narrow224; exact h) hsat

/-- A state satisfying `finalize224Wide.pre`. -/
def finalize224Sat : State :=
  { Proof.Sha256.Arm.Stream.Finalize.sat224 with wr := [⟨0x1000, 96⟩, ⟨0x2000, 28⟩, ⟨0x3000, 608⟩] }

theorem finalize224Wide_implies : finalize224Wide.Implies (Proof.Sha256.finalize224ScratchContract Arm.abi) := by
  contract_implies [Proof.Sha256.finalize224ScratchContract, Proof.Sha256.finalize224ScratchSig,
    Spec.Sha256.finalize224Post, finalize224Wide, Proof.Sha256.countArm, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finalize224Sat, Proof.Sha256.Arm.Stream.Finalize.sat224, MdStream.Arm.Finalize.satD,
      MdStream.Arm.Finalize.satBase, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using finalize224Sat

theorem finalize224Scratch :
    Verified Arm.target Impl.Sha256.Arm.Stream.finalize224 (Proof.Sha256.finalize224ScratchContract Arm.abi) :=
  (finalize224Wide_verified finalize224Wide_implies.sat_left).of_implies finalize224Wide_implies

/-- A state satisfying `Spec.Sha256.finalize224Contract`'s precondition. -/
def finalize224FrameSat : State :=
  { MdStream.Arm.Finalize.satBase with rd := [⟨0x5000, 4⟩], wr := [⟨0x1000, 96⟩, ⟨0x2000, 28⟩] }

theorem finalize224 : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratch 624 1 Impl.Sha256.Arm.Stream.finalize224)
    (Spec.Sha256.finalize224Contract Arm.abi 624) :=
  Arm.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 76) (stack := 0) (bytes := 624) (m := 1)
    finalize224Scratch (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sha256.finalize224Post_local _)
    (by implies_sat [Spec.Sha256.finalize224Contract, Spec.Sha256.finalize224Sig, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [finalize224FrameSat, MdStream.Arm.Finalize.satBase, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
        Mem.read] using finalize224FrameSat)

end VG.Proof.Sha256.Arm.Shared
