import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Sha512.AArch64.Compress
import VerifiedGarbage.Proof.Sha512.AArch64.Stream.Init
import VerifiedGarbage.Proof.Sha512.AArch64.Stream.Md
import VerifiedGarbage.Proof.Sha512.AArch64.Stream.Digest
import VerifiedGarbage.Spec.Sha512.Contract
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch

/-!
# Sha512 on AArch64: the shared contracts

The proofs are written against per-target contracts
(`Proof/Sha512/AArch64/Compress.lean`); these theorems move them to the shared
contracts of `Spec/Sha512/Contract.lean`, which the artifacts are emitted with.

The shared contracts give the functions more scratch than these ones use (1328
bytes for `compress`, 1376 for `update` and `finalize`, sized for the x86-64
AVX2 compression function): the per-target contracts are first widened to
that scratch (`Verified.widen`, the same code running with the same trace and
result), then moved to the shared ones.

`update_of` and `finalize_of` keep the working space in a frame of their
own: they are `updateScratch_of` and `finalizeScratch_of` (the shared
contracts with the working space as an argument, which HMAC's, PBKDF2's and
Ed25519's code calls) run in a frame that allocates it
(`Verified.stackScratch`).
-/

namespace VG.Proof.Sha512.AArch64.Shared

open _root_.VG.AArch64

/-- `compressAArch64` with 1328 bytes of scratch. -/
def compressWide : Contract AArch64.isa :=
  { Proof.Sha512.compressAArch64 with
    pre := fun s =>
      let state : Region := ⟨s.gpr .x0, 64⟩
      let blocks : Region := ⟨s.gpr .x1, 128 * (s.gpr .x2).toNat⟩
      let scratch : Region := ⟨s.gpr .x3, 1328⟩
      s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch }

/-- `updateAArch64` with 1376 bytes of scratch. -/
def updateWide : Contract AArch64.isa :=
  { Proof.Sha512.updateAArch64 with
    pre := fun s =>
      let state : Region := ⟨s.gpr .x0, 192⟩
      let data : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
      let scratch : Region := ⟨s.gpr .x4, 1376⟩
      let stack : Region := ⟨s.sp - 16, 16⟩
      s.rd = [data] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
      16 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch }

/-- `finalizeAArch64` with 1376 bytes of scratch. -/
def finalizeWide : Contract AArch64.isa :=
  { Proof.Sha512.finalizeAArch64 with
    pre := fun s =>
      let state : Region := ⟨s.gpr .x0, 192⟩
      let out : Region := ⟨s.gpr .x2, 64⟩
      let scratch : Region := ⟨s.gpr .x3, 1376⟩
      let stack : Region := ⟨s.sp - 16, 16⟩
      s.rd = [] ∧ s.wr = [state, out, scratch] ∧
      state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
      16 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch }

theorem pfx {a : Addr} {m n : Nat} (h : Nat.ble m n = true) : Region.Prefix ⟨a, m⟩ ⟨a, n⟩ :=
  ⟨rfl, Nat.le_of_ble_eq_true h⟩
theorem subC (a : Addr) : Region.Sub ⟨a, Impl.Sha512.AArch64.scratchBytes⟩ ⟨a, 1328⟩ :=
  Region.sub_prefix (by decide)
theorem subS (a : Addr) : Region.Sub ⟨a, Impl.Sha512.AArch64.scratchBytes + 48⟩ ⟨a, 1376⟩ :=
  Region.sub_prefix (by decide)

theorem compressWide_of {code : Prog isa} (hv : Verified AArch64.target code Proof.Sha512.compressAArch64) (hsat : ∃ s, compressWide.pre s) :
    Verified AArch64.target code compressWide :=
  Verified.widen hv
    (fun s => [⟨s.gpr .x0, 64⟩, ⟨s.gpr .x3, Impl.Sha512.AArch64.scratchBytes⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅⟩ => ⟨h₁, rfl, h₃.sub_right (subC _), h₄, h₅.sub_right (subC _)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat

theorem updateWide_of {code : Prog isa} (hv : Verified AArch64.target code Proof.Sha512.updateAArch64) (hsat : ∃ s, updateWide.pre s) :
    Verified AArch64.target code updateWide :=
  Verified.widen hv
    (fun s => [⟨s.gpr .x0, 192⟩, ⟨s.gpr .x4, Impl.Sha512.AArch64.scratchBytes + 48⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩ =>
      ⟨h₁, rfl, h₃.sub_right (subS _), h₄, h₅.sub_right (subS _), h₆, h₇, h₈,
        h₉.sub_right (subS _)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat

theorem finalizeWide_of {code : Prog isa} (hv : Verified AArch64.target code Proof.Sha512.finalizeAArch64) (hsat : ∃ s, finalizeWide.pre s) :
    Verified AArch64.target code finalizeWide :=
  Verified.widen hv
    (fun s => [⟨s.gpr .x0, 192⟩, ⟨s.gpr .x2, 64⟩, ⟨s.gpr .x3, Impl.Sha512.AArch64.scratchBytes + 48⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩ =>
      ⟨h₁, rfl, h₃, h₄.sub_right (subS _), h₅.sub_right (subS _), h₆, h₇, h₈,
        h₉.sub_right (subS _)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons (pfx rfl)
      (.cons (pfx rfl) .nil)))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat

/-- A state satisfying `compressWide.pre`. -/
def compressSat : State := { Proof.Sha512.AArch64.satState with wr := [⟨0x1000, 64⟩, ⟨0x3000, 1328⟩] }

/-- A state satisfying `updateWide.pre`. -/
def updateSat : State :=
  { Proof.Sha512.AArch64.Stream.Update.sat with wr := [⟨0x1000, 192⟩, ⟨0x3000, 1376⟩] }

/-- A state satisfying `finalizeWide.pre`. -/
def finalizeSat : State :=
  { Proof.Sha512.AArch64.Stream.Finalize.sat with
    wr := [⟨0x1000, 192⟩, ⟨0x2000, 64⟩, ⟨0x3000, 1376⟩] }

theorem compress_of {code : Prog isa} (hv : Verified AArch64.target code Proof.Sha512.compressAArch64) :
    Verified AArch64.target code (Spec.Sha512.compressContract AArch64.abi) := by
  have hi : compressWide.Implies (Spec.Sha512.compressContract AArch64.abi) := by
    sig_implies [Spec.Sha512.compressContract, Spec.Sha512.compressSig, compressWide,
      Proof.Sha512.compressAArch64, AArch64.abi, AArch64.argRegs]
      [compressSat, Proof.Sha512.AArch64.satState] using compressSat
  exact (compressWide_of hv hi.sat_left).of_implies hi

theorem init (iv : Spec.Sha512.HashValue) :
    Verified AArch64.target (Impl.Sha512.AArch64.Stream.init iv) (Spec.Sha512.initContract AArch64.abi iv) :=
  (Proof.Sha512.AArch64.Stream.init_verified iv).of_implies (by
    contract_implies [Spec.Sha512.initContract, Spec.Sha512.initSig, Proof.Sha512.initAArch64,
      AArch64.abi, AArch64.argRegs]
      [Proof.Sha512.AArch64.Stream.initSat] using Proof.Sha512.AArch64.Stream.initSat)

theorem updateScratch_of {code : Prog isa} (hv : Verified AArch64.target code Proof.Sha512.updateAArch64) :
    Verified AArch64.target code (Spec.Sha512.updateScratchContract AArch64.abi 16) := by
  have hi : updateWide.Implies (Spec.Sha512.updateScratchContract AArch64.abi 16) := by
    contract_implies [Spec.Sha512.updateScratchContract, Spec.Sha512.updateScratchSig, updateWide,
      Proof.Sha512.updateAArch64, AArch64.abi, AArch64.argRegs]
      [updateSat, Proof.Sha512.AArch64.Stream.Update.sat, MdStream.AArch64.Update.sat,
        Impl.Sha512.AArch64.Stream.params] using updateSat
  exact (updateWide_of hv hi.sat_left).of_implies hi

theorem finalizeScratch_of {code : Prog isa} (hv : Verified AArch64.target code Proof.Sha512.finalizeAArch64) :
    Verified AArch64.target code (Spec.Sha512.finalizeScratchContract AArch64.abi 16) := by
  have hi : finalizeWide.Implies (Spec.Sha512.finalizeScratchContract AArch64.abi 16) := by
    contract_implies [Spec.Sha512.finalizeScratchContract, Spec.Sha512.finalizeScratchSig, finalizeWide,
      Proof.Sha512.finalizeAArch64, AArch64.abi, AArch64.argRegs]
      [finalizeSat, Proof.Sha512.AArch64.Stream.Finalize.sat, MdStream.AArch64.Finalize.sat,
        Impl.Sha512.AArch64.Stream.params] using finalizeSat
  exact (finalizeWide_of hv hi.sat_left).of_implies hi

theorem compress : Verified AArch64.target Impl.Sha512.AArch64.compress (Spec.Sha512.compressContract AArch64.abi) :=
  compress_of Proof.Sha512.AArch64.compress_verified

/-- `update`: `updateScratch_of` with its working space in a frame of its own. -/
theorem update_of {code : Prog isa} (hv : Verified AArch64.target code Proof.Sha512.updateAArch64) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 1376 .x4 code)
      (Spec.Sha512.updateContract AArch64.abi (16 + 1376)) :=
  AArch64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 172) (stack := 16) (bytes := 1376)
    (updateScratch_of hv) (by decide) (by decide)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-- `finalize`: `finalizeScratch_of` with its working space in a frame of its own. -/
theorem finalize_of {code : Prog isa} (hv : Verified AArch64.target code Proof.Sha512.finalizeAArch64) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 1376 .x3 code)
      (Spec.Sha512.finalizeContract AArch64.abi (16 + 1376)) :=
  AArch64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 172) (stack := 16) (bytes := 1376)
    (finalizeScratch_of hv) (by decide) (by decide)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-! ## The truncated digests

`finalizeDigestWith` (SHA-384's, SHA-512/256's and SHA-512/224's
`finalize`) is verified against `finKD`; widened to the shared scratch, for
the algorithm's initial hash value, and with its working space in a frame of
its own, it is `Spec.Sha512.finalizeDigestContract`. -/

/-- `finalizeWide` for the `D`-byte `digest` of the messages hashed from `iv`. -/
def finalizeDigestWide (iv : Spec.Sha512.HashValue) (D : Nat) (digest : List Byte → List Byte) :
    Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 192⟩
    let out : Region := ⟨s.gpr .x2, D⟩
    let scratch : Region := ⟨s.gpr .x3, 1376⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch
  post s s' := ∀ m, Spec.Sha512.Repr iv s.mem (s.gpr .x0) m → m.length < 2 ^ 64 →
    s.gpr .x1 = BitVec.ofNat 64 m.length → Spec.Sha512.bytesAt s'.mem (s.gpr .x2) D = digest m
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

theorem finalizeDigestWide_of {code : Prog isa} {o : List Instr} {D : Nat} {iv : Spec.Sha512.HashValue}
    {digest : List Byte → List Byte}
    (hv : Verified AArch64.target code (MdStream.AArch64.finKD (P := { Stream.params with out := o }) md D))
    (hdg : ∀ m, (md.hash iv m).take D = digest m) (hsat : ∃ s, (finalizeDigestWide iv D digest).pre s) :
    Verified AArch64.target code (finalizeDigestWide iv D digest) :=
  Verified.widen hv
    (fun s => [⟨s.gpr .x0, 192⟩, ⟨s.gpr .x2, D⟩, ⟨s.gpr .x3, Impl.Sha512.AArch64.scratchBytes + 48⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩ =>
      ⟨h₁, rfl, h₃, h₄.sub_right (subS _), h₅.sub_right (subS _), h₆, h₇, h₈,
        h₉.sub_right (subS _)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons ⟨rfl, Nat.le_refl _⟩
      (.cons (pfx rfl) .nil)))
    (fun _ _ _ h m hr hl hc => (h iv m hr hl hc).trans (hdg m)) (fun _ _ _ _ h => h) hsat

/-- A state satisfying `finalizeDigestWide.pre`. -/
def finalizeDigestSat (D : Nat) : State :=
  { Proof.Sha512.AArch64.Stream.Finalize.satD D with
    wr := [⟨0x1000, 192⟩, ⟨0x2000, D⟩, ⟨0x3000, 1376⟩] }

theorem finalizeDigestScratchImplies48 (iv : Spec.Sha512.HashValue) (digest : List Byte → List Byte) :
    (finalizeDigestWide iv 48 digest).Implies (finalizeDigestScratchContract AArch64.abi iv 48 digest 16) := by
  contract_implies [Proof.Sha512.finalizeDigestScratchContract, Proof.Sha512.finalizeDigestScratchSig,
    Spec.Sha512.finalizeDigestPost, finalizeDigestWide, AArch64.abi, AArch64.argRegs]
    [finalizeDigestSat, Proof.Sha512.AArch64.Stream.Finalize.satD, MdStream.AArch64.Finalize.satD,
      Impl.Sha512.AArch64.Stream.params] using finalizeDigestSat 48

theorem finalizeDigestScratchImplies32 (iv : Spec.Sha512.HashValue) (digest : List Byte → List Byte) :
    (finalizeDigestWide iv 32 digest).Implies (finalizeDigestScratchContract AArch64.abi iv 32 digest 16) := by
  contract_implies [Proof.Sha512.finalizeDigestScratchContract, Proof.Sha512.finalizeDigestScratchSig,
    Spec.Sha512.finalizeDigestPost, finalizeDigestWide, AArch64.abi, AArch64.argRegs]
    [finalizeDigestSat, Proof.Sha512.AArch64.Stream.Finalize.satD, MdStream.AArch64.Finalize.satD,
      Impl.Sha512.AArch64.Stream.params] using finalizeDigestSat 32

theorem finalizeDigestScratchImplies28 (iv : Spec.Sha512.HashValue) (digest : List Byte → List Byte) :
    (finalizeDigestWide iv 28 digest).Implies (finalizeDigestScratchContract AArch64.abi iv 28 digest 16) := by
  contract_implies [Proof.Sha512.finalizeDigestScratchContract, Proof.Sha512.finalizeDigestScratchSig,
    Spec.Sha512.finalizeDigestPost, finalizeDigestWide, AArch64.abi, AArch64.argRegs]
    [finalizeDigestSat, Proof.Sha512.AArch64.Stream.Finalize.satD, MdStream.AArch64.Finalize.satD,
      Impl.Sha512.AArch64.Stream.params] using finalizeDigestSat 28

theorem finalizeDigestScratchImplies (iv : Spec.Sha512.HashValue) (digest : List Byte → List Byte) {D : Nat}
    (hD : D = 48 ∨ D = 32 ∨ D = 28) :
    (finalizeDigestWide iv D digest).Implies (finalizeDigestScratchContract AArch64.abi iv D digest 16) := by
  rcases hD with rfl | rfl | rfl
  exacts [finalizeDigestScratchImplies48 iv digest, finalizeDigestScratchImplies32 iv digest,
    finalizeDigestScratchImplies28 iv digest]

/-- `finalizeDigestWith`, with its working space in a frame of its own. -/
theorem finalizeDigest_of {code : Prog isa} {o : List Instr} {D : Nat} {iv : Spec.Sha512.HashValue}
    {digest : List Byte → List Byte} (hD : D = 48 ∨ D = 32 ∨ D = 28)
    (hv : Verified AArch64.target code (MdStream.AArch64.finKD (P := { Stream.params with out := o }) md D))
    (hdg : ∀ m, (md.hash iv m).take D = digest m) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 1376 .x3 code)
      (Spec.Sha512.finalizeDigestContract AArch64.abi iv D digest (16 + 1376)) := by
  have hi := finalizeDigestScratchImplies iv digest hD
  have h := (finalizeDigestWide_of hv hdg hi.sat_left).of_implies hi
  rcases hD with rfl | rfl | rfl <;>
  exact AArch64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 172) (stack := 16) (bytes := 1376)
    h (by decide) (by decide)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Sha512.AArch64.Shared
