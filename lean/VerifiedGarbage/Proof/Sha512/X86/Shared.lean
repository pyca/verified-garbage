import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Sha512.X86.Compress
import VerifiedGarbage.Proof.Sha512.X86.Stream.Init
import VerifiedGarbage.Proof.Sha512.X86.Stream.Update
import VerifiedGarbage.Proof.Sha512.X86.Stream.Finalize
import VerifiedGarbage.Proof.Sha512.X86.Stream.Digest
import VerifiedGarbage.Spec.Sha512.Contract
import VerifiedGarbage.Proof.Sha512.X86.Lit
import VerifiedGarbage.Proof.Sha512.Scratch
import VerifiedGarbage.Proof.Framework.X86.StackScratch

/-!
# Sha512 on X86: the shared contracts

The proofs are written against per-target contracts
(`Proof/Sha512/X86/Compress.lean`); these theorems move them to the shared
contracts of `Spec/Sha512/Contract.lean`, which the artifacts are emitted
with.

The shared contracts give the functions more scratch than these ones use (1328
bytes for `compress`, 1376 for `update` and `finalize`, sized for the x86-64
AVX2 compression function): the per-target contracts are first widened to
that scratch (`Verified.widen`, the same code running with the same trace and
result), then moved to the shared ones. `update` and `finalize` call the
compression function, using the 20 bytes below the return address.

`update` and `finalize` keep their working space in a frame of their own:
they are `updateScratch` and `finalizeScratch` (the shared contracts with
the working space as an argument, which HMAC's, PBKDF2's and Ed25519's code
calls) run in a frame that allocates it (`Verified.stackScratch`).
-/

namespace VG.Proof.Sha512.X86.Shared

open _root_.VG.X86

/-- `compressX86` with 1328 bytes of scratch. -/
def compressWide : Contract X86.isa :=
  { Proof.Sha512.compressX86 with
    pre := fun s =>
      let state : Region := ⟨(arg s 0).setWidth 64, 64⟩
      let blocks : Region := ⟨(arg s 1).setWidth 64, 128 * (arg s 2).toNat⟩
      let scratch : Region := ⟨(arg s 3).setWidth 64, 1328⟩
      let args : Region := ⟨argAddr s 0, 16⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      s.rd = [blocks, args] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
      args.Disjoint state ∧ args.Disjoint scratch ∧ ret.Disjoint state ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 64 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 128 * (arg s 2).toNat ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 1328 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 }

/-- `updateX86` with 1376 bytes of scratch. -/
def updateWide : Contract X86.isa :=
  { Proof.Sha512.updateX86 with
    pre := fun s =>
      let state : Region := ⟨(arg s 0).setWidth 64, 192⟩
      let data : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
      let scratch : Region := ⟨(arg s 5).setWidth 64, 1376⟩
      let args : Region := ⟨argAddr s 0, 24⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 20, 20⟩
      s.rd = [data, args] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
      args.Disjoint state ∧ args.Disjoint scratch ∧
      ret.Disjoint state ∧ ret.Disjoint scratch ∧ stack.Disjoint state ∧ stack.Disjoint scratch ∧
      stack.Disjoint data ∧
      (arg s 0).toNat + 192 ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧
      (arg s 5).toNat + 1376 ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 }

/-- `finalizeX86` with 1376 bytes of scratch. -/
def finalizeWide : Contract X86.isa :=
  { Proof.Sha512.finalizeX86 with
    pre := fun s =>
      let state : Region := ⟨(arg s 0).setWidth 64, 192⟩
      let out : Region := ⟨(arg s 3).setWidth 64, 64⟩
      let scratch : Region := ⟨(arg s 4).setWidth 64, 1376⟩
      let args : Region := ⟨argAddr s 0, 20⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 20, 20⟩
      s.rd = [args] ∧ s.wr = [state, out, scratch] ∧
      state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
      args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
      stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
      (arg s 0).toNat + 192 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 64 ≤ 2 ^ 32 ∧
      (arg s 4).toNat + 1376 ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 }

theorem pfx {a : Addr} {m n : Nat} (h : Nat.ble m n = true) : Region.Prefix ⟨a, m⟩ ⟨a, n⟩ :=
  ⟨rfl, Nat.le_of_ble_eq_true h⟩
theorem sub224 (a : Addr) : Region.Sub ⟨a, 224⟩ ⟨a, 1328⟩ := Region.sub_prefix (by decide)
theorem sub272 (a : Addr) : Region.Sub ⟨a, 272⟩ ⟨a, 1376⟩ := Region.sub_prefix (by decide)
theorem le224 {x : Nat} (h : x + 1328 ≤ 2 ^ 32) : x + 224 ≤ 2 ^ 32 := by omega
theorem le272 {x : Nat} (h : x + 1376 ≤ 2 ^ 32) : x + 272 ≤ 2 ^ 32 := by omega

/-- Rewrites the per-target contracts at a narrowed state (`arg` does not
unfold cheaply). -/
macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [Proof.Sha512.compressX86, Proof.Sha512.updateX86, Proof.Sha512.finalizeX86,
    Proof.Sha512.countX86, compressWide, updateWide, finalizeWide, VG.X86.arg_withRegions,
    VG.X86.argAddr_withRegions, State.withRegions_gpr, State.withRegions_mem, State.withRegions_rd,
    State.withRegions_wr] $(loc)?)

theorem compressWide_verified (hsat : ∃ s, compressWide.pre s) :
    Verified X86.target Impl.Sha512.X86.compress compressWide :=
  Verified.widen Proof.Sha512.X86.Compress.compress_verified
    (fun s => [⟨(arg s 0).setWidth 64, 64⟩, ⟨(arg s 3).setWidth 64, 224⟩])
    (fun _ h => by
      obtain ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃⟩ := h
      narrow
      exact ⟨h₁, trivial, h₃.sub_right (sub224 _), h₄, h₅.sub_right (sub224 _), h₆, h₇.sub_right (sub224 _),
        h₈, h₉.sub_right (sub224 _), h₁₀, h₁₁, le224 h₁₂, h₁₃⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]; exact .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat

theorem updateWide_verified (hsat : ∃ s, updateWide.pre s) :
    Verified X86.target Impl.Sha512.X86.Stream.update updateWide :=
  Verified.widen Proof.Sha512.X86.Stream.Update.update_verified
    (fun s => [⟨(arg s 0).setWidth 64, 192⟩, ⟨(arg s 5).setWidth 64, 272⟩])
    (fun _ h => by
      obtain ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇⟩ := h
      narrow
      exact ⟨h₁, trivial, h₃.sub_right (sub272 _), h₄, h₅.sub_right (sub272 _), h₆,
        h₇.sub_right (sub272 _), h₈, h₉.sub_right (sub272 _), h₁₀, h₁₁.sub_right (sub272 _), h₁₂, h₁₃,
        h₁₄, le272 h₁₅, h₁₆, h₁₇⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]; exact .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat

theorem finalizeWide_verified (hsat : ∃ s, finalizeWide.pre s) :
    Verified X86.target Impl.Sha512.X86.Stream.finalize finalizeWide :=
  Verified.widen Proof.Sha512.X86.Stream.Finalize.finalize_verified
    (fun s => [⟨(arg s 0).setWidth 64, 192⟩, ⟨(arg s 3).setWidth 64, 64⟩,
      ⟨(arg s 4).setWidth 64, 272⟩])
    (fun _ h => by
      obtain ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉⟩ := h
      narrow
      exact ⟨h₁, trivial, h₃, h₄.sub_right (sub272 _), h₅.sub_right (sub272 _), h₆, h₇,
        h₈.sub_right (sub272 _), h₉, h₁₀, h₁₁.sub_right (sub272 _), h₁₂, h₁₃, h₁₄.sub_right (sub272 _),
        h₁₅, h₁₆, le272 h₁₇, h₁₈, h₁₉⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]; exact .cons (pfx rfl) (.cons (pfx rfl) (.cons (pfx rfl) .nil)))
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat

/-- A state satisfying `compressWide.pre`. -/
def compressSat : State :=
  { Proof.Sha512.X86.Compress.satState with wr := [⟨0x1000, 64⟩, ⟨0x3000, 1328⟩] }

/-- A state satisfying `updateWide.pre`. -/
def updateSat : State :=
  { Proof.Sha512.X86.Stream.Update.sat with wr := [⟨0x1000, 192⟩, ⟨0x3000, 1376⟩] }

/-- A state satisfying `finalizeWide.pre`. -/
def finalizeSat : State :=
  { Proof.Sha512.X86.Stream.Finalize.sat with
    wr := [⟨0x1000, 192⟩, ⟨0x2000, 64⟩, ⟨0x3000, 1376⟩] }

theorem compressWide_implies : compressWide.Implies (Spec.Sha512.compressContract X86.abi) := by
  sig_implies [Spec.Sha512.compressContract, Spec.Sha512.compressSig, compressWide,
    Proof.Sha512.compressX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [compressSat, Proof.Sha512.X86.Compress.satState, Proof.Sha512.X86.Compress.satMem, X86.arg,
      X86.argAddr, Mem.readW, Mem.read] using compressSat

theorem compress :
    Verified X86.target Impl.Sha512.X86.compress (Spec.Sha512.compressContract X86.abi) :=
  (compressWide_verified compressWide_implies.sat_left).of_implies compressWide_implies

theorem init (iv : Spec.Sha512.HashValue) :
    Verified X86.target (Impl.Sha512.X86.Stream.init iv) (Spec.Sha512.initContract X86.abi iv) :=
  (Proof.Sha512.X86.Stream.init_verified iv).of_implies (by
    sig_implies [Spec.Sha512.initContract, Spec.Sha512.initSig, Proof.Sha512.initX86,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [Proof.Sha512.X86.Stream.initSat, Proof.Sha512.X86.Stream.initSatMem, X86.arg, X86.argAddr, Mem.readW,
      Mem.read] using Proof.Sha512.X86.Stream.initSat)

theorem updateWide_implies : updateWide.Implies (Spec.Sha512.updateScratchContract X86.abi 20) := by
  sig_implies [Spec.Sha512.updateScratchContract, Spec.Sha512.updateScratchSig, updateWide, Proof.Sha512.updateX86,
    Proof.Sha512.countX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [updateSat, Proof.Sha512.X86.Stream.Update.sat, MdStream.X86.Update.sat, MdStream.X86.Update.sat₀,
      MdStream.X86.Update.satMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using updateSat

theorem updateScratch :
    Verified X86.target Impl.Sha512.X86.Stream.update (Spec.Sha512.updateScratchContract X86.abi 20) :=
  (updateWide_verified updateWide_implies.sat_left).of_implies updateWide_implies

theorem finalizeWide_implies : finalizeWide.Implies (Spec.Sha512.finalizeScratchContract X86.abi 20) := by
  contract_implies [Spec.Sha512.finalizeScratchContract, Spec.Sha512.finalizeScratchSig, finalizeWide,
    Proof.Sha512.finalizeX86, Proof.Sha512.countX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [finalizeSat, Proof.Sha512.X86.Stream.Finalize.sat, MdStream.X86.Finalize.satR, MdStream.X86.Finalize.sat₀,
      MdStream.X86.Finalize.satMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using finalizeSat

theorem finalizeScratch :
    Verified X86.target Impl.Sha512.X86.Stream.finalize (Spec.Sha512.finalizeScratchContract X86.abi 20) :=
  (finalizeWide_verified finalizeWide_implies.sat_left).of_implies finalizeWide_implies

/-- A state satisfying `update`'s precondition. -/
def updateFrameSat : State :=
  { MdStream.X86.Update.sat₀ with rd := [⟨0x2000, 0⟩, ⟨0x5004, 20⟩], wr := [⟨0x1000, 192⟩] }

theorem update : Verified X86.target
    (Impl.StackScratch.X86.withStackScratch 1404 5 Impl.Sha512.X86.Stream.update)
    (Spec.Sha512.updateContract X86.abi (20 + 1404)) :=
  X86.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 172) (stack := 20) (bytes := 1404)
    updateScratch (by decide) (by lit_decide) (by lit_decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sha512.updatePost_local _)
    (by implies_sat [Spec.Sha512.updateContract, Spec.Sha512.updateSig, X86.abi, X86.argSlots, X86.argVal,
        X86.argBytes]
      [updateFrameSat, MdStream.X86.Update.sat₀, MdStream.X86.Update.satMem, X86.arg, X86.argAddr,
        Mem.readW, Mem.read] using updateFrameSat)

/-- A state satisfying `finalize`'s precondition. -/
def finalizeFrameSat : State :=
  { MdStream.X86.Finalize.sat₀ with rd := [⟨0x5004, 16⟩], wr := [⟨0x1000, 192⟩, ⟨0x2000, 64⟩] }

theorem finalize : Verified X86.target
    (Impl.StackScratch.X86.withStackScratch 1400 4 Impl.Sha512.X86.Stream.finalize)
    (Spec.Sha512.finalizeContract X86.abi (20 + 1400)) :=
  X86.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 172) (stack := 20) (bytes := 1400)
    finalizeScratch (by decide) (by lit_decide) (by lit_decide)
    (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sha512.finalizePost_local _)
    (by implies_sat [Spec.Sha512.finalizeContract, Spec.Sha512.finalizeSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes]
      [finalizeFrameSat, MdStream.X86.Finalize.sat₀, MdStream.X86.Finalize.satMem, X86.arg,
        X86.argAddr, Mem.readW, Mem.read] using finalizeFrameSat)

/-! ## The truncated digests

`finalizeDigest` (SHA-384's, SHA-512/256's and SHA-512/224's `finalize`) is
verified against `finKD`; widened to the shared scratch, for the algorithm's
initial hash value, and with its working space in a frame of its own, it is
`Spec.Sha512.finalizeDigestContract`. -/

/-- `finalizeWide` for the `D`-byte `digest` of the messages hashed from `iv`. -/
def finalizeDigestWide (iv : Spec.Sha512.HashValue) (D : Nat) (digest : List Byte → List Byte) :
    Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 192⟩
    let out : Region := ⟨(arg s 3).setWidth 64, D⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 1376⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 20, 20⟩
    s.rd = [args] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + 192 ≤ 2 ^ 32 ∧ (arg s 3).toNat + D ≤ 2 ^ 32 ∧
    (arg s 4).toNat + 1376 ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post s s' := ∀ m, Spec.Sha512.Repr iv s.mem ((arg s 0).setWidth 64) m → m.length < 2 ^ 64 →
    Proof.Sha512.countX86 s = BitVec.ofNat 64 m.length →
    Spec.Sha512.bytesAt s'.mem ((arg s 3).setWidth 64) D = digest m
  pub s₁ s₂ :=
    s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

/-- Rewrites `finKD` and `finalizeDigestWide` at a narrowed state. -/
macro "narrowD" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [MdStream.X86.finKD, Proof.Sha512.countX86, finalizeDigestWide, MdStream.X86.count,
    VG.X86.arg_withRegions, VG.X86.argAddr_withRegions, State.withRegions_gpr, State.withRegions_mem,
    State.withRegions_rd, State.withRegions_wr] $(loc)?)

theorem finalizeDigestWide_verified {code : Prog X86.isa} {o : List Instr} {D : Nat}
    {iv : Spec.Sha512.HashValue} {digest : List Byte → List Byte}
    (hv : Verified X86.target code
      (MdStream.X86.finKD (P := { Impl.Sha512.X86.Stream.params with out := o }) md 272 D))
    (hdg : ∀ m, (md.hash iv m).take D = digest m) (hsat : ∃ s, (finalizeDigestWide iv D digest).pre s) :
    Verified X86.target code (finalizeDigestWide iv D digest) :=
  Verified.widen hv
    (fun s => [⟨(arg s 0).setWidth 64, 192⟩, ⟨(arg s 3).setWidth 64, D⟩,
      ⟨(arg s 4).setWidth 64, 272⟩])
    (fun _ h => by
      obtain ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉⟩ := h
      narrowD
      exact ⟨h₁, rfl, h₃, h₄.sub_right (sub272 _), h₅.sub_right (sub272 _), h₆, h₇,
        h₈.sub_right (sub272 _), h₉, h₁₀, h₁₁.sub_right (sub272 _), h₁₂, h₁₃, h₁₄.sub_right (sub272 _),
        h₁₅, h₁₆, le272 h₁₇, h₁₈, h₁₉⟩)
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
  { MdStream.X86.Finalize.satRD Impl.Sha512.X86.Stream.params 272 D with
    wr := [⟨0x1000, 192⟩, ⟨0x2000, D⟩, ⟨0x3000, 1376⟩] }

theorem finalizeDigestWide_implies48 (iv : Spec.Sha512.HashValue) (digest : List Byte → List Byte) :
    (finalizeDigestWide iv 48 digest).Implies (finalizeDigestScratchContract X86.abi iv 48 digest 20) := by
  contract_implies [Proof.Sha512.finalizeDigestScratchContract, Proof.Sha512.finalizeDigestScratchSig,
    Spec.Sha512.finalizeDigestPost, finalizeDigestWide, Proof.Sha512.countX86, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
    [finalizeDigestSat, MdStream.X86.Finalize.satRD, MdStream.X86.Finalize.sat₀,
      MdStream.X86.Finalize.satMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using finalizeDigestSat 48

theorem finalizeDigestWide_implies32 (iv : Spec.Sha512.HashValue) (digest : List Byte → List Byte) :
    (finalizeDigestWide iv 32 digest).Implies (finalizeDigestScratchContract X86.abi iv 32 digest 20) := by
  contract_implies [Proof.Sha512.finalizeDigestScratchContract, Proof.Sha512.finalizeDigestScratchSig,
    Spec.Sha512.finalizeDigestPost, finalizeDigestWide, Proof.Sha512.countX86, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
    [finalizeDigestSat, MdStream.X86.Finalize.satRD, MdStream.X86.Finalize.sat₀,
      MdStream.X86.Finalize.satMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using finalizeDigestSat 32

theorem finalizeDigestWide_implies28 (iv : Spec.Sha512.HashValue) (digest : List Byte → List Byte) :
    (finalizeDigestWide iv 28 digest).Implies (finalizeDigestScratchContract X86.abi iv 28 digest 20) := by
  contract_implies [Proof.Sha512.finalizeDigestScratchContract, Proof.Sha512.finalizeDigestScratchSig,
    Spec.Sha512.finalizeDigestPost, finalizeDigestWide, Proof.Sha512.countX86, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
    [finalizeDigestSat, MdStream.X86.Finalize.satRD, MdStream.X86.Finalize.sat₀,
      MdStream.X86.Finalize.satMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using finalizeDigestSat 28

theorem finalizeDigestScratch {code : Prog X86.isa} {o : List Instr} {D : Nat}
    {iv : Spec.Sha512.HashValue} {digest : List Byte → List Byte} (hD : D = 48 ∨ D = 32 ∨ D = 28)
    (hv : Verified X86.target code
      (MdStream.X86.finKD (P := { Impl.Sha512.X86.Stream.params with out := o }) md 272 D))
    (hdg : ∀ m, (md.hash iv m).take D = digest m) :
    Verified X86.target code (finalizeDigestScratchContract X86.abi iv D digest 20) := by
  have hi : (finalizeDigestWide iv D digest).Implies (finalizeDigestScratchContract X86.abi iv D digest 20) := by
    rcases hD with rfl | rfl | rfl
    exacts [finalizeDigestWide_implies48 iv digest, finalizeDigestWide_implies32 iv digest,
      finalizeDigestWide_implies28 iv digest]
  exact (finalizeDigestWide_verified hv hdg hi.sat_left).of_implies hi

/-- A state satisfying `Spec.Sha512.finalizeDigestContract`'s precondition. -/
def finalizeDigestFrameSat (D : Nat) : State :=
  { MdStream.X86.Finalize.sat₀ with rd := [⟨0x5004, 16⟩], wr := [⟨0x1000, 192⟩, ⟨0x2000, D⟩] }

theorem finalizeDigestStack48 {code : Prog X86.isa} {iv : Spec.Sha512.HashValue}
    {digest : List Byte → List Byte}
    (hv : Verified X86.target code (finalizeDigestScratchContract X86.abi iv 48 digest 20))
    (hsp : code.allInstrs (fun i => !Taint.clobbers i .esp) = true) (hd : stackUse code ≤ 20) :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 1400 4 code)
      (Spec.Sha512.finalizeDigestContract X86.abi iv 48 digest (20 + 1400)) :=
  X86.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 172) (stack := 20) (bytes := 1400)
    hv (by decide) hsp hd (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Sha512.finalizeDigestPost_local _ _ _ _)
    (by implies_sat [Spec.Sha512.finalizeDigestContract, Spec.Sha512.finalizeDigestSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes]
      [finalizeDigestFrameSat, MdStream.X86.Finalize.sat₀, MdStream.X86.Finalize.satMem, X86.arg,
        X86.argAddr, Mem.readW, Mem.read] using finalizeDigestFrameSat 48)

theorem finalizeDigestStack32 {code : Prog X86.isa} {iv : Spec.Sha512.HashValue}
    {digest : List Byte → List Byte}
    (hv : Verified X86.target code (finalizeDigestScratchContract X86.abi iv 32 digest 20))
    (hsp : code.allInstrs (fun i => !Taint.clobbers i .esp) = true) (hd : stackUse code ≤ 20) :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 1400 4 code)
      (Spec.Sha512.finalizeDigestContract X86.abi iv 32 digest (20 + 1400)) :=
  X86.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 172) (stack := 20) (bytes := 1400)
    hv (by decide) hsp hd (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Sha512.finalizeDigestPost_local _ _ _ _)
    (by implies_sat [Spec.Sha512.finalizeDigestContract, Spec.Sha512.finalizeDigestSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes]
      [finalizeDigestFrameSat, MdStream.X86.Finalize.sat₀, MdStream.X86.Finalize.satMem, X86.arg,
        X86.argAddr, Mem.readW, Mem.read] using finalizeDigestFrameSat 32)

theorem finalizeDigestStack28 {code : Prog X86.isa} {iv : Spec.Sha512.HashValue}
    {digest : List Byte → List Byte}
    (hv : Verified X86.target code (finalizeDigestScratchContract X86.abi iv 28 digest 20))
    (hsp : code.allInstrs (fun i => !Taint.clobbers i .esp) = true) (hd : stackUse code ≤ 20) :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 1400 4 code)
      (Spec.Sha512.finalizeDigestContract X86.abi iv 28 digest (20 + 1400)) :=
  X86.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 172) (stack := 20) (bytes := 1400)
    hv (by decide) hsp hd (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Sha512.finalizeDigestPost_local _ _ _ _)
    (by implies_sat [Spec.Sha512.finalizeDigestContract, Spec.Sha512.finalizeDigestSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes]
      [finalizeDigestFrameSat, MdStream.X86.Finalize.sat₀, MdStream.X86.Finalize.satMem, X86.arg,
        X86.argAddr, Mem.readW, Mem.read] using finalizeDigestFrameSat 28)

theorem finalize384 : Verified X86.target
    (Impl.StackScratch.X86.withStackScratch 1400 4
      (Impl.Sha512.X86.Stream.finalizeDigest Impl.Sha512.X86.Stream.params384))
    (Spec.Sha512.finalizeDigestContract X86.abi Spec.Sha512.H0_384 48 Spec.Sha512.sha384 (20 + 1400)) :=
  finalizeDigestStack48 (finalizeDigestScratch (.inl rfl) Proof.Sha512.X86.Stream.Finalize.finalize384_verified
    (fun _ => rfl)) (by lit_decide) (by lit_decide)

theorem finalize512_256 : Verified X86.target
    (Impl.StackScratch.X86.withStackScratch 1400 4
      (Impl.Sha512.X86.Stream.finalizeDigest Impl.Sha512.X86.Stream.params512_256))
    (Spec.Sha512.finalizeDigestContract X86.abi Spec.Sha512.H0_512_256 32 Spec.Sha512.sha512_256 (20 + 1400)) :=
  finalizeDigestStack32 (finalizeDigestScratch (.inr (.inl rfl))
    Proof.Sha512.X86.Stream.Finalize.finalize512_256_verified (fun _ => rfl)) (by lit_decide) (by lit_decide)

theorem finalize512_224 : Verified X86.target
    (Impl.StackScratch.X86.withStackScratch 1400 4
      (Impl.Sha512.X86.Stream.finalizeDigest Impl.Sha512.X86.Stream.params512_224))
    (Spec.Sha512.finalizeDigestContract X86.abi Spec.Sha512.H0_512_224 28 Spec.Sha512.sha512_224 (20 + 1400)) :=
  finalizeDigestStack28 (finalizeDigestScratch (.inr (.inr rfl))
    Proof.Sha512.X86.Stream.Finalize.finalize512_224_verified (fun _ => rfl)) (by lit_decide) (by lit_decide)

end VG.Proof.Sha512.X86.Shared
