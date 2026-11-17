module

public import VerifiedGarbage.Proof.Sha512.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Sha512.AArch64.Compress
import VerifiedGarbage.Proof.Sha512.AArch64.Stream.Init
public import VerifiedGarbage.Proof.Sha512.AArch64.Stream.Digest
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
public import VerifiedGarbage.Proof.Sha512.Digest
public import VerifiedGarbage.Impl.StackScratch.AArch64

/-!
# Sha512 on AArch64: the shared contracts

The proofs are written against per-target contracts
(`Proof/Sha512/AArch64/Compress.lean`); these theorems move them to the shared
contracts of `Spec/Sha512/Contract.lean`, which the artifacts are emitted with.

The shared contracts with the working space as an argument, which HMAC's,
PBKDF2's and Ed25519's code calls, give the functions more scratch than these
ones use (1376 bytes, sized for the x86-64 AVX2 compression function): the
per-target contracts are first widened to that scratch (`Verified.widen`, the
same code running with the same trace and result), then moved to the shared
ones (`updateScratch_of`, `finalizeScratch_of`).

`update_of`, `finalize_of` and `finalizeDigest_of` keep the working space in
a frame of their own, of the 688 bytes (`scratchBytes + 48`, 86 words) they
use: they are the same code against the shared contracts with that much
working space (`updateScratchContractW 86`, …), run in a frame that allocates
it (`Verified.stackScratch`).
-/

@[expose] public section

namespace VG.Proof.Sha512.AArch64.Shared

open _root_.VG.AArch64

/-- `updateAArch64` with `n` bytes of scratch. -/
def updateWide (n : Nat := 1376) : Contract AArch64.isa :=
  { Proof.Sha512.updateAArch64 with
    pre := fun s =>
      let state : Region := ⟨s.gpr .x0, 192⟩
      let data : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
      let scratch : Region := ⟨s.gpr .x4, n⟩
      let stack : Region := ⟨s.sp - 16, 16⟩
      s.rd = [data] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
      16 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch }

/-- `finalizeAArch64` with `n` bytes of scratch. -/
def finalizeWide (n : Nat := 1376) : Contract AArch64.isa :=
  { Proof.Sha512.finalizeAArch64 with
    pre := fun s =>
      let state : Region := ⟨s.gpr .x0, 192⟩
      let out : Region := ⟨s.gpr .x2, 64⟩
      let scratch : Region := ⟨s.gpr .x3, n⟩
      let stack : Region := ⟨s.sp - 16, 16⟩
      s.rd = [] ∧ s.wr = [state, out, scratch] ∧
      state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
      16 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch }

theorem pfx {a : Addr} {m n : Nat} (h : Nat.ble m n = true) : Region.Prefix ⟨a, m⟩ ⟨a, n⟩ :=
  ⟨rfl, Nat.le_of_ble_eq_true h⟩
theorem subS (a : Addr) {n : Nat} (h : Nat.ble 688 n = true) :
    Region.Sub ⟨a, Impl.Sha512.AArch64.scratchBytes + 48⟩ ⟨a, n⟩ :=
  Region.sub_prefix (Nat.le_of_ble_eq_true h)

theorem updateWide_of {code : Prog isa} {n : Nat} (hn : Nat.ble 688 n = true)
    (hv : Verified AArch64.target code Proof.Sha512.updateAArch64) (hsat : ∃ s, (updateWide n).pre s) :
    Verified AArch64.target code (updateWide n) :=
  Verified.widen hv
    (fun s => [⟨s.gpr .x0, 192⟩, ⟨s.gpr .x4, Impl.Sha512.AArch64.scratchBytes + 48⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩ =>
      ⟨h₁, rfl, h₃.sub_right (subS _ hn), h₄, h₅.sub_right (subS _ hn), h₆, h₇, h₈,
        h₉.sub_right (subS _ hn)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons (pfx hn) .nil))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat

theorem finalizeWide_of {code : Prog isa} {n : Nat} (hn : Nat.ble 688 n = true)
    (hv : Verified AArch64.target code Proof.Sha512.finalizeAArch64) (hsat : ∃ s, (finalizeWide n).pre s) :
    Verified AArch64.target code (finalizeWide n) :=
  Verified.widen hv
    (fun s => [⟨s.gpr .x0, 192⟩, ⟨s.gpr .x2, 64⟩, ⟨s.gpr .x3, Impl.Sha512.AArch64.scratchBytes + 48⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩ =>
      ⟨h₁, rfl, h₃, h₄.sub_right (subS _ hn), h₅.sub_right (subS _ hn), h₆, h₇, h₈,
        h₉.sub_right (subS _ hn)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons (pfx rfl)
      (.cons (pfx hn) .nil)))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat

/-- A state satisfying `(updateWide n).pre`. -/
def updateSat (n : Nat := 1376) : State :=
  { Proof.Sha512.AArch64.Stream.Update.sat with wr := [⟨0x1000, 192⟩, ⟨0x3000, n⟩] }

/-- A state satisfying `(finalizeWide n).pre`. -/
def finalizeSat (n : Nat := 1376) : State :=
  { Proof.Sha512.AArch64.Stream.Finalize.sat with
    wr := [⟨0x1000, 192⟩, ⟨0x2000, 64⟩, ⟨0x3000, n⟩] }

theorem init (iv : Spec.Sha512.HashValue) :
    Verified AArch64.target (Impl.Sha512.AArch64.Stream.init iv) (Spec.Sha512.initContract AArch64.abi iv) :=
  (Proof.Sha512.AArch64.Stream.init_verified iv).of_implies (by
    contract_implies [Spec.Sha512.initContract, Spec.Sha512.initSig, Proof.Sha512.initAArch64,
      AArch64.abi, AArch64.argRegs]
      [Proof.Sha512.AArch64.Stream.initSat] using Proof.Sha512.AArch64.Stream.initSat)

theorem updateScratch_of {code : Prog isa} (hv : Verified AArch64.target code Proof.Sha512.updateAArch64) :
    Verified AArch64.target code (Proof.Sha512.updateScratchContract AArch64.abi 16) := by
  have hi : updateWide.Implies (Proof.Sha512.updateScratchContract AArch64.abi 16) := by
    contract_implies [Proof.Sha512.updateScratchContract, Proof.Sha512.updateScratchSig, updateWide,
      Proof.Sha512.updateAArch64, AArch64.abi, AArch64.argRegs]
      [updateSat, Proof.Sha512.AArch64.Stream.Update.sat, MdStream.AArch64.Update.sat,
        Impl.Sha512.AArch64.Stream.params] using updateSat
  exact (updateWide_of rfl hv hi.sat_left).of_implies hi

/-- `update` against the shared contract with the 86 words of working space it
uses. -/
theorem updateScratchW_of {code : Prog isa} (hv : Verified AArch64.target code Proof.Sha512.updateAArch64) :
    Verified AArch64.target code (Proof.Sha512.updateScratchContractW 86 AArch64.abi 16) := by
  have hi : (updateWide 688).Implies (Proof.Sha512.updateScratchContractW 86 AArch64.abi 16) := by
    contract_implies [Proof.Sha512.updateScratchContractW, Proof.Sha512.updateScratchSigW, updateWide,
      Proof.Sha512.updateAArch64, AArch64.abi, AArch64.argRegs]
      [updateSat, Proof.Sha512.AArch64.Stream.Update.sat, MdStream.AArch64.Update.sat,
        Impl.Sha512.AArch64.Stream.params] using updateSat 688
  exact (updateWide_of rfl hv hi.sat_left).of_implies hi

theorem finalizeScratch_of {code : Prog isa} (hv : Verified AArch64.target code Proof.Sha512.finalizeAArch64) :
    Verified AArch64.target code (Proof.Sha512.finalizeScratchContract AArch64.abi 16) := by
  have hi : finalizeWide.Implies (Proof.Sha512.finalizeScratchContract AArch64.abi 16) := by
    contract_implies [Proof.Sha512.finalizeScratchContract, Proof.Sha512.finalizeScratchSig, finalizeWide,
      Proof.Sha512.finalizeAArch64, AArch64.abi, AArch64.argRegs]
      [finalizeSat, Proof.Sha512.AArch64.Stream.Finalize.sat, MdStream.AArch64.Finalize.sat,
        Impl.Sha512.AArch64.Stream.params] using finalizeSat
  exact (finalizeWide_of rfl hv hi.sat_left).of_implies hi

/-- `finalize` against the shared contract with the 86 words of working space
it uses. -/
theorem finalizeScratchW_of {code : Prog isa} (hv : Verified AArch64.target code Proof.Sha512.finalizeAArch64) :
    Verified AArch64.target code (Proof.Sha512.finalizeScratchContractW 86 AArch64.abi 16) := by
  have hi : (finalizeWide 688).Implies (Proof.Sha512.finalizeScratchContractW 86 AArch64.abi 16) := by
    contract_implies [Proof.Sha512.finalizeScratchContractW, Proof.Sha512.finalizeScratchSigW, finalizeWide,
      Proof.Sha512.finalizeAArch64, AArch64.abi, AArch64.argRegs]
      [finalizeSat, Proof.Sha512.AArch64.Stream.Finalize.sat, MdStream.AArch64.Finalize.sat,
        Impl.Sha512.AArch64.Stream.params] using finalizeSat 688
  exact (finalizeWide_of rfl hv hi.sat_left).of_implies hi

/-- `update`: `updateScratchW_of` with its working space in a frame of its own. -/
theorem update_of {code : Prog isa} (hv : Verified AArch64.target code Proof.Sha512.updateAArch64) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 688 .x4 code)
      (Spec.Sha512.updateContract AArch64.abi (16 + 688)) :=
  AArch64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 86) (stack := 16) (bytes := 688)
    (updateScratchW_of hv) (by decide) (by decide)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-- `finalize`: `finalizeScratchW_of` with its working space in a frame of its own. -/
theorem finalize_of {code : Prog isa} (hv : Verified AArch64.target code Proof.Sha512.finalizeAArch64) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 688 .x3 code)
      (Spec.Sha512.finalizeContract AArch64.abi (16 + 688)) :=
  AArch64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 86) (stack := 16) (bytes := 688)
    (finalizeScratchW_of hv) (by decide) (by decide)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-! ## The truncated digests

`finalizeDigestWith` (SHA-384's, SHA-512/256's and SHA-512/224's
`finalize`) is verified against `finKD`; widened to the shared scratch, for
the algorithm's initial hash value, and with the 688 bytes of working space it
uses in a frame of its own, it is `Spec.Sha512.finalizeDigestContract`. -/

/-- `finalizeWide 688` for the `D`-byte `digest` of the messages hashed from `iv`. -/
def finalizeDigestWide (iv : Spec.Sha512.HashValue) (D : Nat) (digest : List Byte → List Byte) :
    Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 192⟩
    let out : Region := ⟨s.gpr .x2, D⟩
    let scratch : Region := ⟨s.gpr .x3, 688⟩
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
      ⟨h₁, rfl, h₃, h₄.sub_right (subS _ rfl), h₅.sub_right (subS _ rfl), h₆, h₇, h₈,
        h₉.sub_right (subS _ rfl)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons ⟨rfl, Nat.le_refl _⟩
      (.cons (pfx rfl) .nil)))
    (fun _ _ _ h m hr hl hc => (h iv m hr hl hc).trans (hdg m)) (fun _ _ _ _ h => h) hsat

/-- A state satisfying `finalizeDigestWide.pre`. -/
def finalizeDigestSat (D : Nat) : State :=
  { Proof.Sha512.AArch64.Stream.Finalize.satD D with
    wr := [⟨0x1000, 192⟩, ⟨0x2000, D⟩, ⟨0x3000, 688⟩] }

theorem finalizeDigestScratchImplies48 (iv : Spec.Sha512.HashValue) (digest : List Byte → List Byte) :
    (finalizeDigestWide iv 48 digest).Implies
      (finalizeDigestScratchContractW 86 AArch64.abi iv 48 digest 16) := by
  contract_implies [Proof.Sha512.finalizeDigestScratchContractW, Proof.Sha512.finalizeDigestScratchSigW,
    Spec.Sha512.finalizeDigestPost, finalizeDigestWide, AArch64.abi, AArch64.argRegs]
    [finalizeDigestSat, Proof.Sha512.AArch64.Stream.Finalize.satD, MdStream.AArch64.Finalize.satD,
      Impl.Sha512.AArch64.Stream.params] using finalizeDigestSat 48

theorem finalizeDigestScratchImplies32 (iv : Spec.Sha512.HashValue) (digest : List Byte → List Byte) :
    (finalizeDigestWide iv 32 digest).Implies
      (finalizeDigestScratchContractW 86 AArch64.abi iv 32 digest 16) := by
  contract_implies [Proof.Sha512.finalizeDigestScratchContractW, Proof.Sha512.finalizeDigestScratchSigW,
    Spec.Sha512.finalizeDigestPost, finalizeDigestWide, AArch64.abi, AArch64.argRegs]
    [finalizeDigestSat, Proof.Sha512.AArch64.Stream.Finalize.satD, MdStream.AArch64.Finalize.satD,
      Impl.Sha512.AArch64.Stream.params] using finalizeDigestSat 32

theorem finalizeDigestScratchImplies28 (iv : Spec.Sha512.HashValue) (digest : List Byte → List Byte) :
    (finalizeDigestWide iv 28 digest).Implies
      (finalizeDigestScratchContractW 86 AArch64.abi iv 28 digest 16) := by
  contract_implies [Proof.Sha512.finalizeDigestScratchContractW, Proof.Sha512.finalizeDigestScratchSigW,
    Spec.Sha512.finalizeDigestPost, finalizeDigestWide, AArch64.abi, AArch64.argRegs]
    [finalizeDigestSat, Proof.Sha512.AArch64.Stream.Finalize.satD, MdStream.AArch64.Finalize.satD,
      Impl.Sha512.AArch64.Stream.params] using finalizeDigestSat 28

theorem finalizeDigestScratchImplies (iv : Spec.Sha512.HashValue) (digest : List Byte → List Byte) {D : Nat}
    (hD : D = 48 ∨ D = 32 ∨ D = 28) :
    (finalizeDigestWide iv D digest).Implies
      (finalizeDigestScratchContractW 86 AArch64.abi iv D digest 16) := by
  rcases hD with rfl | rfl | rfl
  exacts [finalizeDigestScratchImplies48 iv digest, finalizeDigestScratchImplies32 iv digest,
    finalizeDigestScratchImplies28 iv digest]

/-- `finalizeDigestWith`, with its working space in a frame of its own. -/
theorem finalizeDigest_of {code : Prog isa} {o : List Instr} {D : Nat} {iv : Spec.Sha512.HashValue}
    {digest : List Byte → List Byte} (hD : D = 48 ∨ D = 32 ∨ D = 28)
    (hv : Verified AArch64.target code (MdStream.AArch64.finKD (P := { Stream.params with out := o }) md D))
    (hdg : ∀ m, (md.hash iv m).take D = digest m) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 688 .x3 code)
      (Spec.Sha512.finalizeDigestContract AArch64.abi iv D digest (16 + 688)) := by
  have hi := finalizeDigestScratchImplies iv digest hD
  have h := (finalizeDigestWide_of hv hdg hi.sat_left).of_implies hi
  rcases hD with rfl | rfl | rfl <;>
  exact AArch64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 86) (stack := 16) (bytes := 688)
    h (by decide) (by decide)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Sha512.AArch64.Shared
