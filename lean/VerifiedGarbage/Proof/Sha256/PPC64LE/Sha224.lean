module

public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
public import VerifiedGarbage.Proof.Sha256.Digest
public import VerifiedGarbage.Proof.Sha256.PPC64LE.Stream.Finalize
public import VerifiedGarbage.Spec.Sha256.Contract
import VerifiedGarbage.Proof.Sha256.PPC64LE.Shared
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Sha256.PPC64LE.Stream.Init

/-!
# SHA-224 on PPC64LE: the shared contracts

Untrusted: everything here is checked by Lean. SHA-224 is SHA-256 from
another initial hash value (`init224`, `Proof/Sha256/PPC64LE/Stream/Init.lean`),
with its digest the first 7 words of the final hash value (`finalize224`,
`Proof/Sha256/PPC64LE/Stream/Finalize.lean`); its `update` is SHA-256's. As
in `Shared.lean`, the per-target contracts are moved to the shared ones of
`Spec/Sha256/Contract.lean`.
-/

@[expose] public section

namespace VG.Proof.Sha256.PPC64LE.Shared

open _root_.VG.PPC64LE

theorem init224 :
    Verified PPC64LE.target Impl.Sha256.PPC64LE.Stream.init224 (Spec.Sha256.init224Contract PPC64LE.abi) :=
  Proof.Sha256.PPC64LE.Stream.init224_verified.of_implies (by
    contract_implies [Spec.Sha256.init224Contract, Spec.Sha256.initSig, Proof.Sha256.initFromPPC64LE,
      PPC64LE.abi, PPC64LE.argRegs]
      [Proof.Sha256.PPC64LE.Stream.initSat] using Proof.Sha256.PPC64LE.Stream.initSat)

/-! ## SHA-224's digest

`finalize224` writes the first 7 words of the final hash value
(`finalizeNPPC64LE 7`); widened to the shared scratch, for SHA-224's initial
hash value, and with its working space in a frame of its own, it is
`Spec.Sha256.finalize224Contract`. -/

/-- `finalizeNPPC64LE 7` with 608 bytes of scratch, for SHA-224's digest of
the messages hashed from its initial hash value. -/
def finalize224Wide : Contract PPC64LE.isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 96⟩
    let out : Region := ⟨s.gpr .r5, 28⟩
    let scratch : Region := ⟨s.gpr .r6, 608⟩
    let stack : Region := ⟨s.sp - 48, 48⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    48 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch
  post s s' := ∀ m, Spec.Sha256.ReprFrom Spec.Sha256.H0_224 s.mem (s.gpr .r3) m →
    s.gpr .r4 = BitVec.ofNat 64 m.length → Spec.Sha256.bytesAt s'.mem (s.gpr .r5) 28 = Spec.Sha256.sha224 m
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

theorem finalize224Wide_verified (hsat : ∃ s, finalize224Wide.pre s) :
    Verified PPC64LE.target Impl.Sha256.PPC64LE.Stream.finalize224 finalize224Wide :=
  Verified.widen Proof.Sha256.PPC64LE.Stream.Finalize.finalize224_verified
    (fun s => [⟨s.gpr .r3, 96⟩, ⟨s.gpr .r5, 28⟩, ⟨s.gpr .r6, 160⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩ =>
      ⟨h₁, rfl, h₃, h₄.sub_right (sub160 _), h₅.sub_right (sub160 _), h₆, h₇, h₈,
        h₉.sub_right (sub160 _)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons (pfx rfl) (.cons (pfx rfl) .nil)))
    (fun _ _ _ h m hr hc => h _ m hr hc) (fun _ _ _ _ h => h) hsat

/-- A state satisfying `finalize224Wide.pre`. -/
def finalize224Sat : State :=
  { Proof.Sha256.PPC64LE.Stream.Finalize.sat with wr := [⟨0x1000, 96⟩, ⟨0x2000, 28⟩, ⟨0x3000, 608⟩] }

theorem finalize224Scratch :
    Verified PPC64LE.target Impl.Sha256.PPC64LE.Stream.finalize224
      (Proof.Sha256.finalize224ScratchContract PPC64LE.abi 48) := by
  have hi : finalize224Wide.Implies (Proof.Sha256.finalize224ScratchContract PPC64LE.abi 48) := by
    contract_implies [Proof.Sha256.finalize224ScratchContract, Proof.Sha256.finalize224ScratchSig,
      Spec.Sha256.finalize224Post, finalize224Wide, PPC64LE.abi, PPC64LE.argRegs]
      [finalize224Sat, Proof.Sha256.PPC64LE.Stream.Finalize.sat] using finalize224Sat
  exact (finalize224Wide_verified hi.sat_left).of_implies hi

/-- `finalize224`: `finalize224Scratch` with its working space in a frame of its own. -/
theorem finalize224 : Verified PPC64LE.target
    (Impl.StackScratch.PPC64LE.withStackScratch 640 .r6 Impl.Sha256.PPC64LE.Stream.finalize224)
    (Spec.Sha256.finalize224Contract PPC64LE.abi (48 + 640)) :=
  PPC64LE.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 76) (stack := 48) (bytes := 640)
    finalize224Scratch (by decide) (by decide)
    (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sha256.finalize224Post_local _)
    (PPC64LE.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Sha256.PPC64LE.Shared
