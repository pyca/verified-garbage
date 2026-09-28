import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.Hmac.Scratch
import VerifiedGarbage.Proof.Hmac.PPC64LE.Finalize
import VerifiedGarbage.Proof.Hmac.PPC64LE.Init
import VerifiedGarbage.Spec.Hmac.Generic

/-!
# HMAC-SHA-256 on PPC64LE: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/Hmac/PPC64LE/Contract.lean`); these theorems move
them to the contracts of `Spec/Hmac/Generic.lean` for SHA-256
(`VG.Spec.Hmac.sha256I`), which the artifacts are emitted with.

The shared contracts give the functions more scratch than these ones use (832
bytes, sized for the other targets' functions): the per-target contracts are
first widened to that scratch (`Verified.widen`, the same code running with
the same trace and result), then moved to the shared ones.
-/

namespace VG.Proof.Hmac.PPC64LE.Shared

open _root_.VG.PPC64LE

/-- `initSha256PPC64LE` with 832 bytes of scratch, of which the code uses 160. -/
def initWide : Contract PPC64LE.isa :=
  { Proof.Hmac.initSha256PPC64LE with
    pre := fun s =>
      let inner : Region := ⟨s.gpr .r3, 96⟩
      let outer : Region := ⟨s.gpr .r4, 96⟩
      let key : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
      let scratch : Region := ⟨s.gpr .r7, 832⟩
      let stack : Region := ⟨s.sp - 48, 48⟩
      (s.gpr .r6).toNat ≤ 64 ∧ s.rd = [key] ∧ s.wr = [inner, outer, scratch] ∧
      inner.Disjoint outer ∧ inner.Disjoint scratch ∧ outer.Disjoint scratch ∧
      key.Disjoint inner ∧ key.Disjoint outer ∧ key.Disjoint scratch ∧
      48 ≤ s.sp.toNat ∧ stack.Disjoint inner ∧ stack.Disjoint outer ∧ stack.Disjoint key ∧
      stack.Disjoint scratch }

/-- The regions `initSha256PPC64LE` lets the code write. -/
def initNarrowWr (s : State) : List Region :=
  [⟨s.gpr .r3, 96⟩, ⟨s.gpr .r4, 96⟩, ⟨s.gpr .r7, 160⟩]

theorem initWide_pre (s : State) (h : initWide.pre s) :
    Proof.Hmac.initSha256PPC64LE.pre (s.withRegions s.rd (initNarrowWr s)) :=
  let ⟨h₁, h₂, _, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄⟩ := h
  ⟨h₁, h₂, rfl, h₄, h₅.sub_right (Region.sub_of_ble rfl), h₆.sub_right (Region.sub_of_ble rfl), h₇,
    h₈, h₉.sub_right (Region.sub_of_ble rfl), h₁₀, h₁₁, h₁₂, h₁₃,
    h₁₄.sub_right (Region.sub_of_ble rfl)⟩

/-- A state satisfying `initWide.pre`. -/
def initWideSat : State :=
  { Proof.Hmac.PPC64LE.Init.sat with wr := [⟨0x1000, 96⟩, ⟨0x2000, 96⟩, ⟨0x4000, 832⟩] }

theorem initWide_implies :
    initWide.Implies (Spec.Hmac.sha256I.initScratchContract PPC64LE.abi 48) := by
  sig_implies [Spec.Hmac.Instance.initScratchContract, Spec.Hmac.initScratchContract,
    Spec.Hmac.initScratchSig, Spec.Hmac.initPre,
    Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, initWide,
    Proof.Hmac.initSha256PPC64LE, PPC64LE.abi, PPC64LE.argRegs]
    [initWideSat, Proof.Hmac.PPC64LE.Init.sat] using initWideSat

theorem initScratch : Verified PPC64LE.target Impl.Hmac.PPC64LE.init
    (Spec.Hmac.sha256I.initScratchContract PPC64LE.abi 48) :=
  have hsat := initWide_implies.sat_left
  (Verified.widen Proof.Hmac.PPC64LE.Init.init_verified initNarrowWr initWide_pre
    (fun _ h => by
      obtain ⟨_, _, h₃, _⟩ := h
      rw [h₃]
      exact .cons (Region.prefix_of_ble rfl) (.cons (Region.prefix_of_ble rfl)
        (.cons (Region.prefix_of_ble rfl) .nil)))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat).of_implies initWide_implies

/-- `finalizeSha256PPC64LE` with 832 bytes of scratch, of which the code uses
248. -/
def finalizeWide : Contract PPC64LE.isa :=
  { Proof.Hmac.finalizeSha256PPC64LE with
    pre := fun s =>
      let inner : Region := ⟨s.gpr .r3, 96⟩
      let outer : Region := ⟨s.gpr .r4, 96⟩
      let out : Region := ⟨s.gpr .r6, 32⟩
      let scratch : Region := ⟨s.gpr .r7, 832⟩
      let stack : Region := ⟨s.sp - 96, 96⟩
      s.rd = [outer] ∧ s.wr = [inner, out, scratch] ∧
      inner.Disjoint outer ∧ inner.Disjoint out ∧ inner.Disjoint scratch ∧
      outer.Disjoint out ∧ outer.Disjoint scratch ∧ out.Disjoint scratch ∧
      96 ≤ s.sp.toNat ∧ stack.Disjoint inner ∧ stack.Disjoint outer ∧ stack.Disjoint out ∧
      stack.Disjoint scratch }

/-- The regions `finalizeSha256PPC64LE` lets the code write. -/
def finalizeNarrowWr (s : State) : List Region :=
  [⟨s.gpr .r3, 96⟩, ⟨s.gpr .r6, 32⟩, ⟨s.gpr .r7, 248⟩]

theorem finalizeWide_pre (s : State) (h : finalizeWide.pre s) :
    Proof.Hmac.finalizeSha256PPC64LE.pre (s.withRegions s.rd (finalizeNarrowWr s)) :=
  let ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃⟩ := h
  ⟨h₁, rfl, h₃, h₄, h₅.sub_right (Region.sub_of_ble rfl), h₆, h₇.sub_right (Region.sub_of_ble rfl),
    h₈.sub_right (Region.sub_of_ble rfl), h₉, h₁₀, h₁₁, h₁₂, h₁₃.sub_right (Region.sub_of_ble rfl)⟩

/-- A state satisfying `finalizeWide.pre`. -/
def finalizeWideSat : State :=
  { Proof.Hmac.PPC64LE.Finalize.sat with wr := [⟨0x1000, 96⟩, ⟨0x5000, 32⟩, ⟨0x3000, 832⟩] }

theorem finalizeWide_implies :
    finalizeWide.Implies (Spec.Hmac.sha256I.finalizeScratchContract PPC64LE.abi 96) := by
  sig_implies [Spec.Hmac.Instance.finalizeScratchContract, Spec.Hmac.finalizeScratchContract,
    Spec.Hmac.finalizeScratchSig,
    Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, finalizeWide,
    Proof.Hmac.finalizeSha256PPC64LE, PPC64LE.abi, PPC64LE.argRegs]
    [finalizeWideSat, Proof.Hmac.PPC64LE.Finalize.sat] using finalizeWideSat

theorem finalizeScratch : Verified PPC64LE.target Impl.Hmac.PPC64LE.finalize
    (Spec.Hmac.sha256I.finalizeScratchContract PPC64LE.abi 96) :=
  have hsat := finalizeWide_implies.sat_left
  (Verified.widen Proof.Hmac.PPC64LE.Finalize.finalize_verified finalizeNarrowWr finalizeWide_pre
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]
      exact .cons (Region.prefix_of_ble rfl) (.cons (Region.prefix_of_ble rfl)
        (.cons (Region.prefix_of_ble rfl) .nil)))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat).of_implies finalizeWide_implies

/-- A state satisfying `init`'s precondition without the working space (a
one-byte key). -/
def initFrameSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 1
    | _ => 0
  lr := 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x3000, 1⟩]
  wr := [⟨0x1000, 96⟩, ⟨0x2000, 96⟩]

/-- A state satisfying `finalize`'s precondition without the working space. -/
def finFrameSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r6 => 0x3000
    | _ => 0
  lr := 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 96⟩]
  wr := [⟨0x1000, 96⟩, ⟨0x3000, 32⟩]

theorem initFrame_sat : ∃ s, (Spec.Hmac.sha256I.initContract PPC64LE.abi (48 + 864)).pre s := by
  implies_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
      Spec.Hmac.initPre, Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, PPC64LE.abi,
      PPC64LE.argRegs]
    [initFrameSat] using initFrameSat

theorem finFrame_sat :
    ∃ s, (Spec.Hmac.sha256I.finalizeContract PPC64LE.abi (96 + 864)).pre s := by
  implies_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract,
      Spec.Hmac.finalizeSig, Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, PPC64LE.abi,
      PPC64LE.argRegs]
    [finFrameSat] using finFrameSat

/-- `init`: `initScratch` with its working space in a frame of its own. -/
theorem init : Verified PPC64LE.target
    (Impl.StackScratch.PPC64LE.withStackScratch 864 .r7 Impl.Hmac.PPC64LE.init)
    (Spec.Hmac.sha256I.initContract PPC64LE.abi (48 + 864)) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Hmac.initSig Spec.Hmac.sha256I.S) (nm := "scratch")
    (e := .u64) (n := 104) (pre := Spec.Hmac.initPre Spec.Hmac.sha256I.S PPC64LE.abi.ptrBits)
    (post := Spec.Hmac.initPost Spec.Hmac.sha256I.S PPC64LE.abi.ptrBits) (wa := true) (stack := 48)
    (bytes := 864) initScratch (by decide) (by decide)
    (Proof.Hmac.initPre_local _ _) (Proof.Hmac.initPost_local _ _) initFrame_sat

/-- `finalize`: `finalizeScratch` with its working space in a frame of its own. -/
theorem finalize : Verified PPC64LE.target
    (Impl.StackScratch.PPC64LE.withStackScratch 864 .r7 Impl.Hmac.PPC64LE.finalize)
    (Spec.Hmac.sha256I.finalizeContract PPC64LE.abi (96 + 864)) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Hmac.finalizeSig Spec.Hmac.sha256I.S)
    (nm := "scratch") (e := .u64) (n := 104)
    (post := Spec.Hmac.finalizePost Spec.Hmac.sha256I.S PPC64LE.abi.ptrBits) (wa := true)
    (stack := 96) (bytes := 864) finalizeScratch (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Hmac.finalizePost_local _ _ Proof.Hmac.sha256_local (by decide)) finFrame_sat

end VG.Proof.Hmac.PPC64LE.Shared
