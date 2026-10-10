import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Sm3.X86.Compress
import VerifiedGarbage.Proof.Sm3.X86.Stream.Init
import VerifiedGarbage.Proof.Sm3.X86.Stream.Md
import VerifiedGarbage.Spec.Sm3.Contract
import VerifiedGarbage.Proof.Sm3.X86.Lit
import VerifiedGarbage.Proof.Sm3.Scratch
import VerifiedGarbage.Proof.Framework.X86.StackScratch

/-!
# SM3 on x86: the shared contracts

The proofs are written against per-target contracts
(`Proof/Sm3/X86/Contract.lean`); these theorems move them to the shared
contracts of `Spec/Sm3/Contract.lean`, which the artifacts are emitted with.

The shared contract gives `compress` more scratch (576 bytes) than this one
uses (112), and that of `update` lets it write its arguments: the per-target
contracts are first widened to that scratch and to writable arguments
(`Verified.widen`, `Verified.narrowTo`, the same code running with the same
trace and result), then moved to the shared ones. `update` and `finalize` call the
compression function, using the 20 bytes of stack below the return address.

`update` and `finalize` keep their working space (20 words: the compression
function's 112 bytes, then what the streaming code saves) in a frame of their
own: they are `updateScratch` and `finalizeScratch` (the shared contracts
with the working space as an argument, `Proof/Sm3/Scratch.lean`) run in a
frame that allocates it (`Verified.stackScratch`).
-/

namespace VG.Proof.Sm3.X86.Shared

open _root_.VG.X86

/-- `updateX86` with its arguments writable. -/
def updateWide : Contract X86.isa :=
  { Proof.Sm3.updateX86 with
    pre := fun s =>
      let state : Region := ⟨(arg s 0).setWidth 64, 96⟩
      let data : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
      let scratch : Region := ⟨(arg s 5).setWidth 64, 160⟩
      let args : Region := ⟨argAddr s 0, 24⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 20, 20⟩
      s.rd = [data] ∧ s.wr = [state, scratch, args] ∧
      state.Disjoint scratch ∧ args.Disjoint state ∧ args.Disjoint scratch ∧
      data.Disjoint state ∧ data.Disjoint scratch ∧
      ret.Disjoint state ∧ ret.Disjoint scratch ∧ stack.Disjoint state ∧ stack.Disjoint scratch ∧
      stack.Disjoint data ∧
      (arg s 0).toNat + 96 ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧
      (arg s 5).toNat + 160 ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 }

/-- Rewrites the per-target contracts at a narrowed state (`arg` does not
unfold cheaply). -/
macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [Proof.Sm3.updateX86, updateWide, VG.X86.arg_withRegions, VG.X86.argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_mem, State.withRegions_rd, State.withRegions_wr] $(loc)?)

/-- `update` only reads its arguments. -/
theorem updateWide_verified (hsat : ∃ s, updateWide.pre s) :
    Verified X86.target Impl.Sm3.X86.Stream.update updateWide :=
  Verified.narrowTo Proof.Sm3.X86.Stream.Update.update_verified
    (fun s => [⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩, ⟨argAddr s 0, 24⟩])
    (fun s => [⟨(arg s 0).setWidth 64, 96⟩, ⟨(arg s 5).setWidth 64, 160⟩])
    (fun _ h => by
      obtain ⟨_, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇⟩ := h
      narrow
      exact ⟨trivial, trivial, h₃, h₆, h₇, h₄, h₅, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇⟩)
    (fun _ h => by
      obtain ⟨h₁, h₂, _⟩ := h
      rw [h₁, h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _), 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_singleton_self _))), 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp,
          by simp⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩)
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat

/-- A state satisfying `updateWide.pre`. -/
def updateSat : State :=
  { Proof.Sm3.X86.Stream.Update.sat with
    rd := [⟨0x2000, 0⟩], wr := [⟨0x1000, 96⟩, ⟨0x3000, 160⟩, ⟨0x5004, 24⟩] }

/-- `compressX86` with 576 bytes of scratch. -/
def compressWide : Contract X86.isa :=
  { Proof.Sm3.compressX86 with
    pre := fun s =>
      let state : Region := ⟨(arg s 0).setWidth 64, 32⟩
      let blocks : Region := ⟨(arg s 1).setWidth 64, 64 * (arg s 2).toNat⟩
      let scratch : Region := ⟨(arg s 3).setWidth 64, 576⟩
      let args : Region := ⟨argAddr s 0, 16⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      s.rd = [blocks, args] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
      args.Disjoint state ∧ args.Disjoint scratch ∧ ret.Disjoint state ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 64 * (arg s 2).toNat ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 576 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 }

theorem sub112 (a : Addr) : Region.Sub ⟨a, 112⟩ ⟨a, 576⟩ := Region.sub_prefix (by decide)

/-- A state satisfying `compressWide.pre`. -/
def compressSat : State := { Proof.Sm3.X86.satState with wr := [⟨0x1000, 32⟩, ⟨0x3000, 576⟩] }

/-- Rewrites the per-target contract at a narrowed state. -/
macro "narrowC" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [Proof.Sm3.compressX86, compressWide, VG.X86.arg_withRegions,
    VG.X86.argAddr_withRegions, State.withRegions_gpr, State.withRegions_mem, State.withRegions_rd,
    State.withRegions_wr] $(loc)?)

theorem compressWide_implies : compressWide.Implies (Spec.Sm3.compressContract X86.abi) := by
  contract_implies [Spec.Sm3.compressContract, Spec.Sm3.compressSig, compressWide,
    Proof.Sm3.compressX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [compressSat, Proof.Sm3.X86.satState, Proof.Sm3.X86.satMem, X86.arg, X86.argAddr, Mem.readW,
      Mem.read] using compressSat

theorem compressWide_verified : Verified X86.target Impl.Sm3.X86.compress compressWide :=
  Verified.widen Proof.Sm3.X86.compress_verified
    (fun s => [⟨(arg s 0).setWidth 64, 32⟩, ⟨(arg s 3).setWidth 64, 112⟩])
    (fun _ h => by
      obtain ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃⟩ := h
      narrowC
      exact ⟨h₁, trivial, h₃.sub_right (sub112 _), h₄, h₅.sub_right (sub112 _), h₆,
        h₇.sub_right (sub112 _), h₈, h₉.sub_right (sub112 _), h₁₀, h₁₁,
        Nat.le_trans (Nat.add_le_add_left (by decide : 112 ≤ 576) _) h₁₂, h₁₃⟩)
    (fun _ ⟨_, h₂, _⟩ => by
      rw [h₂]
      exact .cons ⟨rfl, Nat.le_refl _⟩ (.cons ⟨rfl, show 112 ≤ 576 by decide⟩ .nil))
    (fun _ _ _ h => by narrowC at h ⊢; exact h) (fun _ _ _ _ h => by narrowC; exact h)
    compressWide_implies.sat_left

theorem compress :
    Verified X86.target Impl.Sm3.X86.compress (Spec.Sm3.compressContract X86.abi) :=
  compressWide_verified.of_implies compressWide_implies

theorem init :
    Verified X86.target Impl.Sm3.X86.Stream.init (Spec.Sm3.initContract X86.abi) :=
  Proof.Sm3.X86.Stream.init_verified.of_implies (by
    contract_implies [Spec.Sm3.initContract, Spec.Sm3.initSig, Proof.Sm3.initX86,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [Proof.Sm3.X86.Stream.initSat, Proof.Sm3.X86.Stream.initSatMem, X86.arg, X86.argAddr, Mem.readW,
        Mem.read] using Proof.Sm3.X86.Stream.initSat)

theorem updateWide_implies : updateWide.Implies (Proof.Sm3.updateScratchContract X86.abi 20 20) := by
  contract_implies [Proof.Sm3.updateScratchContract, Proof.Sm3.updateScratchSig, Spec.Sm3.updateSig, updateWide,
    Proof.Sm3.updateX86, Proof.Sm3.countX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [updateSat, Proof.Sm3.X86.Stream.Update.sat, MdStream.X86.Update.sat, MdStream.X86.Update.sat₀,
      MdStream.X86.Update.satMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using updateSat

theorem updateScratch :
    Verified X86.target Impl.Sm3.X86.Stream.update (Proof.Sm3.updateScratchContract X86.abi 20 20) :=
  (updateWide_verified updateWide_implies.sat_left).of_implies updateWide_implies

theorem finalizeScratch :
    Verified X86.target Impl.Sm3.X86.Stream.finalize (Proof.Sm3.finalizeScratchContract X86.abi 20 20) :=
  Proof.Sm3.X86.Stream.Finalize.finalize_verified.of_implies (by
    contract_implies [Proof.Sm3.finalizeScratchContract, Proof.Sm3.finalizeScratchSig, Spec.Sm3.finalizeSig,
      Proof.Sm3.finalizeX86, Proof.Sm3.countX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [Proof.Sm3.X86.Stream.Finalize.sat, MdStream.X86.Finalize.sat, MdStream.X86.Finalize.sat₀,
        MdStream.X86.Finalize.satMem, Impl.Sm3.X86.Stream.params, X86.arg, X86.argAddr, Mem.readW,
        Mem.read] using Proof.Sm3.X86.Stream.Finalize.sat)

/-- A state satisfying `update`'s precondition. -/
def updateFrameSat : State :=
  { MdStream.X86.Update.sat₀ with rd := [⟨0x2000, 0⟩], wr := [⟨0x1000, 96⟩, ⟨0x5004, 20⟩] }

theorem update : Verified X86.target
    (Impl.StackScratch.X86.withStackScratch 188 5 Impl.Sm3.X86.Stream.update)
    (Spec.Sm3.updateContract X86.abi (20 + 188)) :=
  X86.Verified.stackScratch (sig := Spec.Sm3.updateSig) (nm := "scratch") (e := .u64) (n := 20)
    (stack := 20) (bytes := 188)
    (by rw [← Proof.Sm3.updateScratchContract_eq]; exact updateScratch) (by decide) (by lit_decide) (by lit_decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sm3.updatePost_local _)
    (by implies_sat [Spec.Sm3.updateContract, Spec.Sm3.updateSig, X86.abi, X86.argSlots, X86.argVal,
        X86.argBytes]
      [updateFrameSat, MdStream.X86.Update.sat₀, MdStream.X86.Update.satMem, X86.arg, X86.argAddr,
        Mem.readW, Mem.read] using updateFrameSat)

/-- A state satisfying `finalize`'s precondition. -/
def finalizeFrameSat : State :=
  { MdStream.X86.Finalize.sat₀ with wr := [⟨0x1000, 96⟩, ⟨0x2000, 32⟩, ⟨0x5004, 16⟩] }

theorem finalize : Verified X86.target
    (Impl.StackScratch.X86.withStackScratch 184 4 Impl.Sm3.X86.Stream.finalize)
    (Spec.Sm3.finalizeContract X86.abi (20 + 184)) :=
  X86.Verified.stackScratch (sig := Spec.Sm3.finalizeSig) (nm := "scratch") (e := .u64) (n := 20)
    (stack := 20) (bytes := 184)
    (by rw [← Proof.Sm3.finalizeScratchContract_eq]; exact finalizeScratch) (by decide) (by lit_decide) (by lit_decide)
    (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sm3.finalizePost_local _)
    (by implies_sat [Spec.Sm3.finalizeContract, Spec.Sm3.finalizeSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes]
      [finalizeFrameSat, MdStream.X86.Finalize.sat₀, MdStream.X86.Finalize.satMem, X86.arg,
        X86.argAddr, Mem.readW, Mem.read] using finalizeFrameSat)

end VG.Proof.Sm3.X86.Shared
