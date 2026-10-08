import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Sha256.AArch64.Compress
import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Init
import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Md
import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Digest
import VerifiedGarbage.Spec.Sha256.Contract
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch

/-!
# Sha256 on AArch64: the shared contracts

The proofs are written against per-target contracts
(`Proof/Sha256/AArch64/Contract.lean`); these theorems move them to the shared
contracts of `Spec/Sha256/Contract.lean`, which the artifacts are emitted with.

The shared contracts give the functions more scratch than these ones use (560
bytes for `compress`, 608 for `update` and `finalize`, sized for x86-64's AVX2
compression function): the per-target contracts are first widened to that
scratch (`Verified.widen`, the same code running with the same trace and
result), then moved to the shared ones.

`update_of` and `finalize_of` keep the working space in a frame of their
own: they are `updateScratch_of` and `finalizeScratch_of` (the shared
contracts with the working space as an argument, which HMAC's and PBKDF2's
code calls) run in a frame that allocates it (`Verified.stackScratch`).
-/

namespace VG.Proof.Sha256.AArch64.Shared

open _root_.VG.AArch64

/-- `compressAArch64` with 560 bytes of scratch. -/
def compressWide : Contract AArch64.isa :=
  { Proof.Sha256.compressAArch64 with
    pre := fun s =>
      let state : Region := ⟨s.gpr .x0, 32⟩
      let blocks : Region := ⟨s.gpr .x1, 64 * (s.gpr .x2).toNat⟩
      let scratch : Region := ⟨s.gpr .x3, 560⟩
      s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch }

/-- `updateAArch64` with 608 bytes of scratch. -/
def updateWide : Contract AArch64.isa :=
  { Proof.Sha256.updateAArch64 with
    pre := fun s =>
      let state : Region := ⟨s.gpr .x0, 96⟩
      let data : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
      let scratch : Region := ⟨s.gpr .x4, 608⟩
      let stack : Region := ⟨s.sp - 16, 16⟩
      s.rd = [data] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
      16 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch }

/-- `finalizeAArch64` with 608 bytes of scratch. -/
def finalizeWide : Contract AArch64.isa :=
  { Proof.Sha256.finalizeAArch64 with
    pre := fun s =>
      let state : Region := ⟨s.gpr .x0, 96⟩
      let out : Region := ⟨s.gpr .x2, 32⟩
      let scratch : Region := ⟨s.gpr .x3, 608⟩
      let stack : Region := ⟨s.sp - 16, 16⟩
      s.rd = [] ∧ s.wr = [state, out, scratch] ∧
      state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
      16 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch }

theorem pfx {a : Addr} {m n : Nat} (h : Nat.ble m n = true) : Region.Prefix ⟨a, m⟩ ⟨a, n⟩ :=
  ⟨rfl, Nat.le_of_ble_eq_true h⟩
theorem sub112 (a : Addr) : Region.Sub ⟨a, 112⟩ ⟨a, 560⟩ := Region.sub_prefix (by decide)
theorem sub160 (a : Addr) : Region.Sub ⟨a, 160⟩ ⟨a, 608⟩ := Region.sub_prefix (by decide)

theorem compressWide_of {code : Prog isa} (hv : Verified AArch64.target code Proof.Sha256.compressAArch64) (hsat : ∃ s, compressWide.pre s) :
    Verified AArch64.target code compressWide :=
  Verified.widen hv
    (fun s => [⟨s.gpr .x0, 32⟩, ⟨s.gpr .x3, 112⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅⟩ => ⟨h₁, rfl, h₃.sub_right (sub112 _), h₄, h₅.sub_right (sub112 _)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat

theorem updateWide_of {code : Prog isa} (hv : Verified AArch64.target code Proof.Sha256.updateAArch64) (hsat : ∃ s, updateWide.pre s) :
    Verified AArch64.target code updateWide :=
  Verified.widen hv
    (fun s => [⟨s.gpr .x0, 96⟩, ⟨s.gpr .x4, 160⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩ =>
      ⟨h₁, rfl, h₃.sub_right (sub160 _), h₄, h₅.sub_right (sub160 _), h₆, h₇, h₈,
        h₉.sub_right (sub160 _)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat

theorem finalizeWide_of {code : Prog isa} (hv : Verified AArch64.target code Proof.Sha256.finalizeAArch64) (hsat : ∃ s, finalizeWide.pre s) :
    Verified AArch64.target code finalizeWide :=
  Verified.widen hv
    (fun s => [⟨s.gpr .x0, 96⟩, ⟨s.gpr .x2, 32⟩, ⟨s.gpr .x3, 160⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩ =>
      ⟨h₁, rfl, h₃, h₄.sub_right (sub160 _), h₅.sub_right (sub160 _), h₆, h₇, h₈,
        h₉.sub_right (sub160 _)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons (pfx rfl) (.cons (pfx rfl) .nil)))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat

/-- A state satisfying `compressWide.pre`. -/
def compressSat : State := { Proof.Sha256.AArch64.satState with wr := [⟨0x1000, 32⟩, ⟨0x3000, 560⟩] }

/-- A state satisfying `updateWide.pre`. -/
def updateSat : State :=
  { Proof.Sha256.AArch64.Stream.Update.sat with wr := [⟨0x1000, 96⟩, ⟨0x3000, 608⟩] }

/-- A state satisfying `finalizeWide.pre`. -/
def finalizeSat : State :=
  { Proof.Sha256.AArch64.Stream.Finalize.sat with wr := [⟨0x1000, 96⟩, ⟨0x2000, 32⟩, ⟨0x3000, 608⟩] }

theorem compress_of {code : Prog isa} (hv : Verified AArch64.target code Proof.Sha256.compressAArch64) :
    Verified AArch64.target code (Spec.Sha256.compressContract AArch64.abi) := by
  have hi : compressWide.Implies (Spec.Sha256.compressContract AArch64.abi) := by
    contract_implies [Spec.Sha256.compressContract, Spec.Sha256.compressSig, compressWide,
      Proof.Sha256.compressAArch64, AArch64.abi, AArch64.argRegs]
      [compressSat, Proof.Sha256.AArch64.satState] using compressSat
  exact (compressWide_of hv hi.sat_left).of_implies hi

theorem init :
    Verified AArch64.target Impl.Sha256.AArch64.Stream.init (Spec.Sha256.initContract AArch64.abi) :=
  Proof.Sha256.AArch64.Stream.init_verified.of_implies (by
    contract_implies [Spec.Sha256.initContract, Spec.Sha256.initSig, Proof.Sha256.initAArch64,
      AArch64.abi, AArch64.argRegs]
      [Proof.Sha256.AArch64.Stream.initSat] using Proof.Sha256.AArch64.Stream.initSat)

theorem init224 :
    Verified AArch64.target Impl.Sha256.AArch64.Stream.init224 (Spec.Sha256.init224Contract AArch64.abi) :=
  Proof.Sha256.AArch64.Stream.init224_verified.of_implies (by
    contract_implies [Spec.Sha256.init224Contract, Spec.Sha256.initSig, Proof.Sha256.initAArch64,
      AArch64.abi, AArch64.argRegs]
      [Proof.Sha256.AArch64.Stream.initSat] using Proof.Sha256.AArch64.Stream.initSat)

theorem updateScratch_of {code : Prog isa} (hv : Verified AArch64.target code Proof.Sha256.updateAArch64) :
    Verified AArch64.target code (Spec.Sha256.updateScratchContract AArch64.abi 16) := by
  have hi : updateWide.Implies (Spec.Sha256.updateScratchContract AArch64.abi 16) := by
    contract_implies [Spec.Sha256.updateScratchContract, Spec.Sha256.updateScratchSig, updateWide,
      Proof.Sha256.updateAArch64, AArch64.abi, AArch64.argRegs]
      [updateSat, Proof.Sha256.AArch64.Stream.Update.sat, MdStream.AArch64.Update.sat,
        Impl.Sha256.AArch64.Stream.params] using updateSat
  exact (updateWide_of hv hi.sat_left).of_implies hi

theorem finalizeScratch_of {code : Prog isa} (hv : Verified AArch64.target code Proof.Sha256.finalizeAArch64) :
    Verified AArch64.target code (Spec.Sha256.finalizeScratchContract AArch64.abi 16) := by
  have hi : finalizeWide.Implies (Spec.Sha256.finalizeScratchContract AArch64.abi 16) := by
    contract_implies [Spec.Sha256.finalizeScratchContract, Spec.Sha256.finalizeScratchSig, finalizeWide,
      Proof.Sha256.finalizeAArch64, AArch64.abi, AArch64.argRegs]
      [finalizeSat, Proof.Sha256.AArch64.Stream.Finalize.sat, MdStream.AArch64.Finalize.sat,
        Impl.Sha256.AArch64.Stream.params] using finalizeSat
  exact (finalizeWide_of hv hi.sat_left).of_implies hi

theorem compress :
    Verified AArch64.target Impl.Sha256.AArch64.compress (Spec.Sha256.compressContract AArch64.abi) :=
  compress_of Proof.Sha256.AArch64.compress_verified

/-- `update`: `updateScratch_of` with its working space in a frame of its own. -/
theorem update_of {code : Prog isa} (hv : Verified AArch64.target code Proof.Sha256.updateAArch64) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 608 .x4 code)
      (Spec.Sha256.updateContract AArch64.abi (16 + 608)) :=
  AArch64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 76) (stack := 16) (bytes := 608)
    (updateScratch_of hv) (by decide) (by decide)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-- `finalize`: `finalizeScratch_of` with its working space in a frame of its own. -/
theorem finalize_of {code : Prog isa} (hv : Verified AArch64.target code Proof.Sha256.finalizeAArch64) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 608 .x3 code)
      (Spec.Sha256.finalizeContract AArch64.abi (16 + 608)) :=
  AArch64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 76) (stack := 16) (bytes := 608)
    (finalizeScratch_of hv) (by decide) (by decide)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-! ## SHA-224's digest

SHA-224's `finalize` (`Compress.finalize224`) is verified against `finKD`;
widened to the shared scratch, for SHA-224's initial hash value, and with its
working space in a frame of its own, it is `Spec.Sha256.finalize224Contract`. -/

/-- `finalizeWide` for SHA-224's digest of the messages hashed from its
initial hash value. -/
def finalize224Wide : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 96⟩
    let out : Region := ⟨s.gpr .x2, 28⟩
    let scratch : Region := ⟨s.gpr .x3, 608⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch
  post s s' := ∀ m, Spec.Sha256.ReprFrom Spec.Sha256.H0_224 s.mem (s.gpr .x0) m →
    s.gpr .x1 = BitVec.ofNat 64 m.length → Spec.Sha256.bytesAt s'.mem (s.gpr .x2) 28 = Spec.Sha256.sha224 m
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

theorem finalize224Wide_of {code : Prog isa}
    (hv : Verified AArch64.target code (MdStream.AArch64.finKD (P := Impl.Sha256.AArch64.Stream.params224) md 28))
    (hsat : ∃ s, finalize224Wide.pre s) :
    Verified AArch64.target code finalize224Wide :=
  Verified.widen hv
    (fun s => [⟨s.gpr .x0, 96⟩, ⟨s.gpr .x2, 28⟩, ⟨s.gpr .x3, 160⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩ =>
      ⟨h₁, rfl, h₃, h₄.sub_right (sub160 _), h₅.sub_right (sub160 _), h₆, h₇, h₈,
        h₉.sub_right (sub160 _)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons (pfx rfl) (.cons (pfx rfl) .nil)))
    (fun _ _ _ h m hr hc => (h _ m hr trivial hc).trans (sha224_eq m)) (fun _ _ _ _ h => h) hsat

/-- A state satisfying `finalize224Wide.pre`. -/
def finalize224Sat : State :=
  { Proof.Sha256.AArch64.Stream.Finalize.sat224 with wr := [⟨0x1000, 96⟩, ⟨0x2000, 28⟩, ⟨0x3000, 608⟩] }

theorem finalize224Scratch_of {code : Prog isa}
    (hv : Verified AArch64.target code (MdStream.AArch64.finKD (P := Impl.Sha256.AArch64.Stream.params224) md 28)) :
    Verified AArch64.target code (Proof.Sha256.finalize224ScratchContract AArch64.abi 16) := by
  have hi : finalize224Wide.Implies (Proof.Sha256.finalize224ScratchContract AArch64.abi 16) := by
    contract_implies [Proof.Sha256.finalize224ScratchContract, Proof.Sha256.finalize224ScratchSig,
      Spec.Sha256.finalize224Post, finalize224Wide, AArch64.abi, AArch64.argRegs]
      [finalize224Sat, Proof.Sha256.AArch64.Stream.Finalize.sat224, MdStream.AArch64.Finalize.satD,
        Impl.Sha256.AArch64.Stream.params] using finalize224Sat
  exact (finalize224Wide_of hv hi.sat_left).of_implies hi

/-- SHA-224's `finalize`: `finalize224Scratch_of` with its working space in a
frame of its own. -/
theorem finalize224_of {code : Prog isa}
    (hv : Verified AArch64.target code (MdStream.AArch64.finKD (P := Impl.Sha256.AArch64.Stream.params224) md 28)) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 608 .x3 code)
      (Spec.Sha256.finalize224Contract AArch64.abi (16 + 608)) :=
  AArch64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 76) (stack := 16) (bytes := 608)
    (finalize224Scratch_of hv) (by decide) (by decide)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Sha256.AArch64.Shared
