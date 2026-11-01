module

public import VerifiedGarbage.Proof.Sha512.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
public import VerifiedGarbage.Proof.Sha512.PPC64LE.Compress
public import VerifiedGarbage.Proof.Sha512.PPC64LE.Stream.Finalize
import VerifiedGarbage.Proof.Sha512.PPC64LE.Stream.Init
public import VerifiedGarbage.Proof.Sha512.PPC64LE.Stream.Update
import VerifiedGarbage.Proof.Sha512.Scratch
public import VerifiedGarbage.Proof.Sha512.Digest
public import VerifiedGarbage.Spec.Sha512.Contract
import all Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Impl.Sha512.PPC64LE.Stream
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Sha512.PPC64LE.Contract
public import VerifiedGarbage.Spec.Sha512
public import VerifiedGarbage.TCB.Artifact

/-!
# Sha512 on PPC64LE: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/Sha512/PPC64LE/Contract.lean`); these theorems move
them to the shared contracts of `Spec/Sha512/Contract.lean`, which the
artifacts are emitted with.

The shared contracts give the functions more scratch than these ones use (1328
bytes for `compress`, 1376 for `update` and `finalize`, sized for the x86-64
AVX2 compression function): the per-target contracts are first widened to
that scratch (`Verified.widen`, the same code running with the same trace and
result), then moved to the shared ones: `update` and `finalize` (as opposed
to `updateScratch` and `finalizeScratch`, which other code calls) run in a
frame that allocates it (`Verified.stackScratch`).
-/

@[expose] public section

namespace VG.Proof.Sha512.PPC64LE.Shared

open _root_.VG.PPC64LE

/-- `compressPPC64LE` with 1328 bytes of scratch. -/
def compressWide : Contract PPC64LE.isa :=
  { Proof.Sha512.compressPPC64LE with
    pre := fun s =>
      let state : Region := ⟨s.gpr .r3, 64⟩
      let blocks : Region := ⟨s.gpr .r4, 128 * (s.gpr .r5).toNat⟩
      let scratch : Region := ⟨s.gpr .r6, 1328⟩
      s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch }

/-- `updatePPC64LE` with 1376 bytes of scratch. -/
def updateWide : Contract PPC64LE.isa :=
  { Proof.Sha512.updatePPC64LE with
    pre := fun s =>
      let state : Region := ⟨s.gpr .r3, 192⟩
      let data : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
      let scratch : Region := ⟨s.gpr .r7, 1376⟩
      s.rd = [data] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch }

/-- `finalizePPC64LE` with 1376 bytes of scratch. -/
def finalizeWide : Contract PPC64LE.isa :=
  { Proof.Sha512.finalizePPC64LE with
    pre := fun s =>
      let state : Region := ⟨s.gpr .r3, 192⟩
      let out : Region := ⟨s.gpr .r5, 64⟩
      let scratch : Region := ⟨s.gpr .r6, 1376⟩
      s.rd = [] ∧ s.wr = [state, out, scratch] ∧
      state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch }

theorem pfx {a : Addr} {m n : Nat} (h : Nat.ble m n = true) : Region.Prefix ⟨a, m⟩ ⟨a, n⟩ :=
  ⟨rfl, Nat.le_of_ble_eq_true h⟩
theorem sub176 (a : Addr) : Region.Sub ⟨a, 176⟩ ⟨a, 1328⟩ := Region.sub_prefix (by decide)
theorem sub224 (a : Addr) : Region.Sub ⟨a, 224⟩ ⟨a, 1376⟩ := Region.sub_prefix (by decide)

theorem compressWide_verified (hsat : ∃ s, compressWide.pre s) :
    Verified PPC64LE.target Impl.Sha512.PPC64LE.compress compressWide :=
  Verified.widen Proof.Sha512.PPC64LE.compress_verified
    (fun s => [⟨s.gpr .r3, 64⟩, ⟨s.gpr .r6, 176⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅⟩ => ⟨h₁, rfl, h₃.sub_right (sub176 _), h₄, h₅.sub_right (sub176 _)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat

theorem updateWide_verified (hsat : ∃ s, updateWide.pre s) :
    Verified PPC64LE.target Impl.Sha512.PPC64LE.Stream.update updateWide :=
  Verified.widen Proof.Sha512.PPC64LE.Stream.Update.update_verified
    (fun s => [⟨s.gpr .r3, 192⟩, ⟨s.gpr .r7, 224⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅⟩ => ⟨h₁, rfl, h₃.sub_right (sub224 _), h₄, h₅.sub_right (sub224 _)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat

theorem finalizeWide_verified (hsat : ∃ s, finalizeWide.pre s) :
    Verified PPC64LE.target Impl.Sha512.PPC64LE.Stream.finalize finalizeWide :=
  Verified.widen Proof.Sha512.PPC64LE.Stream.Finalize.finalize_verified
    (fun s => [⟨s.gpr .r3, 192⟩, ⟨s.gpr .r5, 64⟩, ⟨s.gpr .r6, 224⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅⟩ => ⟨h₁, rfl, h₃, h₄.sub_right (sub224 _), h₅.sub_right (sub224 _)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons (pfx rfl)
      (.cons (pfx rfl) .nil)))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat

/-- A state satisfying `compressWide.pre`. -/
def compressSat : State := { Proof.Sha512.PPC64LE.satState with wr := [⟨0x1000, 64⟩, ⟨0x3000, 1328⟩] }

/-- A state satisfying `updateWide.pre`. -/
def updateSat : State :=
  { Proof.Sha512.PPC64LE.Stream.Update.sat with wr := [⟨0x1000, 192⟩, ⟨0x3000, 1376⟩] }

/-- A state satisfying `finalizeWide.pre`. -/
def finalizeSat : State :=
  { Proof.Sha512.PPC64LE.Stream.Finalize.sat with
    wr := [⟨0x1000, 192⟩, ⟨0x2000, 64⟩, ⟨0x3000, 1376⟩] }

theorem compress :
    Verified PPC64LE.target Impl.Sha512.PPC64LE.compress (Proof.Sha512.compressContract PPC64LE.abi) := by
  have hi : compressWide.Implies (Proof.Sha512.compressContract PPC64LE.abi) := by
    contract_implies [Proof.Sha512.compressContract, Proof.Sha512.compressSig, compressWide,
      Proof.Sha512.compressPPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      [compressSat, Proof.Sha512.PPC64LE.satState] using compressSat
  exact (compressWide_verified hi.sat_left).of_implies hi

theorem init (iv : Spec.Sha512.HashValue) :
    Verified PPC64LE.target (Impl.Sha512.PPC64LE.Stream.init iv) (Spec.Sha512.initContract PPC64LE.abi iv) :=
  (Proof.Sha512.PPC64LE.Stream.init_verified iv).of_implies (by
    contract_implies [Spec.Sha512.initContract, Spec.Sha512.initSig, Proof.Sha512.initPPC64LE,
      PPC64LE.abi, PPC64LE.argRegs]
      [Proof.Sha512.PPC64LE.Stream.initSat] using Proof.Sha512.PPC64LE.Stream.initSat)

theorem updateScratch : Verified PPC64LE.target Impl.Sha512.PPC64LE.Stream.update
    (Proof.Sha512.updateScratchContract PPC64LE.abi) := by
  have hi : updateWide.Implies (Proof.Sha512.updateScratchContract PPC64LE.abi) := by
    contract_implies [Proof.Sha512.updateScratchContract, Proof.Sha512.updateScratchSig, updateWide,
      Proof.Sha512.updatePPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      [updateSat, Proof.Sha512.PPC64LE.Stream.Update.sat] using updateSat
  exact (updateWide_verified hi.sat_left).of_implies hi

theorem finalizeScratch : Verified PPC64LE.target Impl.Sha512.PPC64LE.Stream.finalize
    (Proof.Sha512.finalizeScratchContract PPC64LE.abi) := by
  have hi : finalizeWide.Implies (Proof.Sha512.finalizeScratchContract PPC64LE.abi) := by
    contract_implies [Proof.Sha512.finalizeScratchContract, Proof.Sha512.finalizeScratchSig,
      finalizeWide,
      Proof.Sha512.finalizePPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      [finalizeSat, Proof.Sha512.PPC64LE.Stream.Finalize.sat] using finalizeSat
  exact (finalizeWide_verified hi.sat_left).of_implies hi

/-- `update`: `updateScratch` with its working space in a frame of its own. -/
theorem update : Verified PPC64LE.target
    (Impl.StackScratch.PPC64LE.withStackScratch 1408 .r7 Impl.Sha512.PPC64LE.Stream.update)
    (Spec.Sha512.updateContract PPC64LE.abi (0 + 1408)) :=
  PPC64LE.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 172) (stack := 0) (bytes := 1408)
    updateScratch (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sha512.updatePost_local _)
    (PPC64LE.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-- `finalize`: `finalizeScratch` with its working space in a frame of its own. -/
theorem finalize : Verified PPC64LE.target
    (Impl.StackScratch.PPC64LE.withStackScratch 1408 .r6 Impl.Sha512.PPC64LE.Stream.finalize)
    (Spec.Sha512.finalizeContract PPC64LE.abi (0 + 1408)) :=
  PPC64LE.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 172) (stack := 0) (bytes := 1408)
    finalizeScratch (by decide) (by decide)
    (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sha512.finalizePost_local _)
    (PPC64LE.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-! ## The truncated digests

`finalize384`, `finalize512_256` and `finalize512_224` write the first 48,
32 and 28 bytes of the final hash value (`finalizeDPPC64LE`); for the
algorithm's initial hash value, that is its digest. Widened to the shared
scratch and with their working space in a frame of their own, they are
`Spec.Sha512.finalizeDigestContract`. -/

/-- `finalizeDPPC64LE D` with 1376 bytes of scratch, for the `D`-byte `digest`
of the messages hashed from `iv`. -/
def finalizeDigestWide (iv : Spec.Sha512.HashValue) (D : Nat) (digest : List Byte → List Byte) :
    Contract PPC64LE.isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 192⟩
    let out : Region := ⟨s.gpr .r5, D⟩
    let scratch : Region := ⟨s.gpr .r6, 1376⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch
  post s s' := ∀ m, Spec.Sha512.Repr iv s.mem (s.gpr .r3) m → m.length < 2 ^ 64 →
    s.gpr .r4 = BitVec.ofNat 64 m.length → Spec.Sha512.bytesAt s'.mem (s.gpr .r5) D = digest m
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

theorem finalizeDigestWide_of {code : Prog isa} {D : Nat} {iv : Spec.Sha512.HashValue}
    {digest : List Byte → List Byte} (hv : Verified PPC64LE.target code (Proof.Sha512.finalizeDPPC64LE D))
    (hdg : ∀ m, (Spec.Sha512.finalHash iv m).take D = digest m)
    (hsat : ∃ s, (finalizeDigestWide iv D digest).pre s) :
    Verified PPC64LE.target code (finalizeDigestWide iv D digest) :=
  Verified.widen hv
    (fun s => [⟨s.gpr .r3, 192⟩, ⟨s.gpr .r5, D⟩, ⟨s.gpr .r6, 224⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅⟩ => ⟨h₁, rfl, h₃, h₄.sub_right (sub224 _), h₅.sub_right (sub224 _)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons ⟨rfl, Nat.le_refl _⟩ (.cons (pfx rfl) .nil)))
    (fun _ _ _ h m hr hl hc => (h iv m hr hl hc).trans (hdg m)) (fun _ _ _ _ h => h) hsat

/-- A state satisfying `finalizeDigestWide.pre`. -/
def finalizeDigestSat (D : Nat) : State :=
  { Proof.Sha512.PPC64LE.Stream.Finalize.sat with
    wr := [⟨0x1000, 192⟩, ⟨0x2000, D⟩, ⟨0x3000, 1376⟩] }

theorem finalizeDigestScratchImplies48 (iv : Spec.Sha512.HashValue) (digest : List Byte → List Byte) :
    (finalizeDigestWide iv 48 digest).Implies (Proof.Sha512.finalizeDigestScratchContract PPC64LE.abi iv 48 digest 0) := by
  contract_implies [Proof.Sha512.finalizeDigestScratchContract, Proof.Sha512.finalizeDigestScratchSig,
    Spec.Sha512.finalizeDigestPost, finalizeDigestWide, PPC64LE.abi, PPC64LE.argRegs]
    [finalizeDigestSat, Proof.Sha512.PPC64LE.Stream.Finalize.sat] using finalizeDigestSat 48

theorem finalizeDigestScratchImplies32 (iv : Spec.Sha512.HashValue) (digest : List Byte → List Byte) :
    (finalizeDigestWide iv 32 digest).Implies (Proof.Sha512.finalizeDigestScratchContract PPC64LE.abi iv 32 digest 0) := by
  contract_implies [Proof.Sha512.finalizeDigestScratchContract, Proof.Sha512.finalizeDigestScratchSig,
    Spec.Sha512.finalizeDigestPost, finalizeDigestWide, PPC64LE.abi, PPC64LE.argRegs]
    [finalizeDigestSat, Proof.Sha512.PPC64LE.Stream.Finalize.sat] using finalizeDigestSat 32

theorem finalizeDigestScratchImplies28 (iv : Spec.Sha512.HashValue) (digest : List Byte → List Byte) :
    (finalizeDigestWide iv 28 digest).Implies (Proof.Sha512.finalizeDigestScratchContract PPC64LE.abi iv 28 digest 0) := by
  contract_implies [Proof.Sha512.finalizeDigestScratchContract, Proof.Sha512.finalizeDigestScratchSig,
    Spec.Sha512.finalizeDigestPost, finalizeDigestWide, PPC64LE.abi, PPC64LE.argRegs]
    [finalizeDigestSat, Proof.Sha512.PPC64LE.Stream.Finalize.sat] using finalizeDigestSat 28

theorem finalizeDigestScratchImplies (iv : Spec.Sha512.HashValue) (digest : List Byte → List Byte) {D : Nat}
    (hD : D = 48 ∨ D = 32 ∨ D = 28) :
    (finalizeDigestWide iv D digest).Implies (Proof.Sha512.finalizeDigestScratchContract PPC64LE.abi iv D digest 0) := by
  rcases hD with rfl | rfl | rfl
  exacts [finalizeDigestScratchImplies48 iv digest, finalizeDigestScratchImplies32 iv digest,
    finalizeDigestScratchImplies28 iv digest]

/-- A truncated digest's `finalize`, with its working space in a frame of its own. -/
theorem finalizeDigest_of {code : Prog isa} {D : Nat} {iv : Spec.Sha512.HashValue}
    {digest : List Byte → List Byte} (hD : D = 48 ∨ D = 32 ∨ D = 28)
    (hv : Verified PPC64LE.target code (Proof.Sha512.finalizeDPPC64LE D))
    (hdg : ∀ m, (Spec.Sha512.finalHash iv m).take D = digest m) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 1408 .r6 code)
      (Spec.Sha512.finalizeDigestContract PPC64LE.abi iv D digest (0 + 1408)) := by
  have hi := finalizeDigestScratchImplies iv digest hD
  have h := (finalizeDigestWide_of hv hdg hi.sat_left).of_implies hi
  rcases hD with rfl | rfl | rfl <;>
  exact PPC64LE.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 172) (stack := 0) (bytes := 1408)
    h (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sha512.finalizeDigestPost_local _ _ _ _)
    (PPC64LE.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

theorem finalize384 : Verified PPC64LE.target
    (Impl.StackScratch.PPC64LE.withStackScratch 1408 .r6 Impl.Sha512.PPC64LE.Stream.finalize384)
    (Spec.Sha512.finalizeDigestContract PPC64LE.abi Spec.Sha512.H0_384 48 Spec.Sha512.sha384 (0 + 1408)) :=
  finalizeDigest_of (.inl rfl) Proof.Sha512.PPC64LE.Stream.Finalize.finalize384_verified fun _ => rfl

theorem finalize512_256 : Verified PPC64LE.target
    (Impl.StackScratch.PPC64LE.withStackScratch 1408 .r6 Impl.Sha512.PPC64LE.Stream.finalize512_256)
    (Spec.Sha512.finalizeDigestContract PPC64LE.abi Spec.Sha512.H0_512_256 32 Spec.Sha512.sha512_256
      (0 + 1408)) :=
  finalizeDigest_of (.inr (.inl rfl)) Proof.Sha512.PPC64LE.Stream.Finalize.finalize512_256_verified fun _ => rfl

theorem finalize512_224 : Verified PPC64LE.target
    (Impl.StackScratch.PPC64LE.withStackScratch 1408 .r6 Impl.Sha512.PPC64LE.Stream.finalize512_224)
    (Spec.Sha512.finalizeDigestContract PPC64LE.abi Spec.Sha512.H0_512_224 28 Spec.Sha512.sha512_224
      (0 + 1408)) :=
  finalizeDigest_of (.inr (.inr rfl)) Proof.Sha512.PPC64LE.Stream.Finalize.finalize512_224_verified fun _ => rfl

end VG.Proof.Sha512.PPC64LE.Shared
