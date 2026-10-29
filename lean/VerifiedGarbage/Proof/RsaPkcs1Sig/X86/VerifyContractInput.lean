module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyContractGeometry
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyFnInput
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Precomputed

import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyRegions
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyGeometry
import VerifiedGarbage.Proof.Rsa.BytesFrame
/-! # Decode the shared verifier precondition into its frame and input geometry -/

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/VerifyABI.lean`, which only this module imported.
section

/-! # Resources supplied by the shared precomputed-verification signature -/

section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86
open VG.Proof.Dsa.X86 (argumentPointer)

structure VerifyABI (s : State) : Prop where
  stackLow : verifyStack ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 56 ≤ 2 ^ 32
  rd : s.rd = [⟨argumentPointer s 0, (arg s 1).toNat⟩, ⟨argumentPointer s 2, (arg s 3).toNat⟩, ⟨argumentPointer s 5, (arg s 6).toNat⟩, ⟨argumentPointer s 7, (arg s 8).toNat⟩, ⟨argumentPointer s 11, 8 * (arg s 12).toNat⟩]
  wr : s.wr = [⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩, ⟨argAddr s 0, 52⟩]
  sourceWorkspace0 : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩
  sourceWorkspace1 : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩
  sourceWorkspace2 : (⟨argumentPointer s 5, (arg s 6).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩
  sourceWorkspace3 : (⟨argumentPointer s 7, (arg s 8).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩
  sourceWorkspace4 : (⟨argumentPointer s 11, 8 * (arg s 12).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩
  workspaceArguments : (⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 52⟩
  stackSource0 : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨argumentPointer s 0, (arg s 1).toNat⟩
  stackSource1 : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨argumentPointer s 2, (arg s 3).toNat⟩
  stackSource2 : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨argumentPointer s 5, (arg s 6).toNat⟩
  stackSource3 : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨argumentPointer s 7, (arg s 8).toNat⟩
  stackSource4 : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨argumentPointer s 11, 8 * (arg s 12).toNat⟩
  stackWorkspace : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩
  stackArguments : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨argAddr s 0, 52⟩
  returnWorkspace : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩
  sourceFit0 : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  sourceFit1 : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32
  sourceFit2 : (arg s 5).toNat + (arg s 6).toNat ≤ 2 ^ 32
  sourceFit3 : (arg s 7).toNat + (arg s 8).toNat ≤ 2 ^ 32
  sourceFit4 : (arg s 11).toNat + 8 * (arg s 12).toNat ≤ 2 ^ 32
  workspaceFit : (arg s 9).toNat + 8 * (arg s 10).toNat ≤ 2 ^ 32
  valid : Spec.Rsa.lenValid (arg s 1).toNat
  ePositive : 1 ≤ (arg s 3).toNat
  eFits : (arg s 3).toNat ≤ (arg s 1).toNat
  space : Spec.Rsa.publicScratchWords (arg s 1).toNat ≤ (arg s 10).toNat
  preLength : (arg s 12).toNat = Spec.Rsa.precomputedWords (arg s 1).toNat

theorem verifyABI_of {s : State} (h : (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi verifyStack).pre s) : VerifyABI s := by
  sig_pre [Spec.RsaPkcs1Sig.verifyPrecomputedContract, Spec.RsaPkcs1Sig.verifyPrecomputedSig,
    abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor <;> simp only [verifyStack, Nat.mul_comm 8] at *
  all_goals first
    | with_reducible assumption
    | exact Region.Disjoint.symm (by with_reducible assumption)

end VG.Proof.RsaPkcs1Sig.X86.Ver
end

end

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/VerifyEntryInput.lean`, which only this module imported.
section

/-! # Native cdecl inputs before reserving the two wrapper frames -/

section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86 VG.Proof.Rsa.X86.PrivChecked VG.Impl.RsaPkcs1Sig.X86.Verify VG.Proof.Bignum.X86
open VG.Proof.Dsa.X86 (allocated)

structure EntryInput (g : Geometry) (bs : Fin 5 → List Byte) (s : State) : Prop where
  valid : g.Valid
  stackFit : verifyStack ≤ (s.gpr .esp).toNat
  base : g.stack = s.gpr .esp - 16 - BitVec.ofNat 32 VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes
  source : ∀ i, PublicBytes (g.sources i) (g.sourceLength i) (bs i) s
  workspaceWrite : InRegions s.wr (byteAddr g.workspace) (8 * g.scratchLength)
  argumentsRead : InRegions (s.rd ++ s.wr) g.argumentsRegion.base 52
  arguments : ∀ j < 13, s.mem.readW (byteAddr g.stack + BitVec.ofNat 64 (VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes + 20 + 4 * j)) 32 = g.argument j
  returnSeparate : ∀ r ∈ bodyWrites g, (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint r

theorem EntryInput.enteredSp {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : EntryInput g bs s) : (entered s).gpr .esp = g.stack := by
  rw [entered, VG.Proof.Dsa.X86.allocated_esp, pushed_esp]
  exact h.base.symm

theorem EntryInput.savedAddr {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : EntryInput g bs s) : ((pushed savedRegisters s).gpr .esp).setWidth 64 = g.savedRegion.base := by
  have eq : (pushed savedRegisters s).gpr .esp = g.stack + BitVec.ofNat 32 VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes := by
    rw [← h.enteredSp]
    exact (BitVec.sub_add_cancel _ _).symm
  rw [eq]
  exact h.valid.offsetAddr (by decide)

theorem EntryInput.enteredFrame {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : EntryInput g bs s) : Frame [g.savedRegion] s.mem (entered s).mem := by
  have f := pushed_frame (rs := savedRegisters) (s := s) (by decide)
    (by change 16 ≤ _; have := h.stackFit; unfold verifyStack at this; omega)
  unfold below at f
  rw [← pushed_esp] at f
  change Frame [⟨((pushed savedRegisters s).gpr .esp).setWidth 64, 16⟩] s.mem (entered s).mem at f
  rw [h.savedAddr] at f
  exact f

theorem entered_read {s : State} {p : Addr} {n : Nat} (read : InRegions (s.rd ++ s.wr) p n) :
    InRegions ((entered s).rd ++ (entered s).wr) p n := by
  obtain ⟨r, hr, hc⟩ := read
  refine ⟨r, ?_, hc⟩
  rcases List.mem_append.mp hr with hr | hr
  · exact List.mem_append_left _ hr
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))

theorem entered_write {s : State} {p : Addr} {n : Nat} (write : InRegions s.wr p n) :
    InRegions (entered s).wr p n := by
  obtain ⟨r, hr, hc⟩ := write
  exact ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), hc⟩
end VG.Proof.RsaPkcs1Sig.X86.Ver
end

end

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/VerifyEntryReady.lean`, which only this module imported.
section

/-! # Entering the wrapper preserves all sources and incoming arguments -/

section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86 VG.Proof.Rsa.X86.PrivChecked VG.Proof.Bignum.X86

theorem EntryInput.enteredSource {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : EntryInput g bs s) (i : Fin 5) :
    PublicBytes (g.sources i) (g.sourceLength i) (bs i) (entered s) := by
  refine ⟨(h.source i).fits, entered_read (h.source i).read, ?_⟩
  have sep : ∀ r ∈ [g.savedRegion], (g.sourceRegion i).Disjoint r := by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ((h.valid.stackSources i).sub_left h.valid.savedSub).symm
  exact (Rsa.rsa_bytes_frame h.enteredFrame (by have := (h.source i).fits; omega) sep).trans (h.source i).bytes

theorem EntryInput.enteredArguments {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : EntryInput g bs s) (j : Nat) (hj : j < 13) :
    (entered s).mem.readW (byteAddr g.stack + BitVec.ofNat 64 (VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes + 20 + 4 * j)) 32 = g.argument j := by
  have sep : ∀ r ∈ [g.savedRegion], g.argumentsRegion.Disjoint r := by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact (h.valid.stackArguments.sub_left h.valid.savedSub).symm
  have eq := h.enteredFrame.readW (r := g.argumentsRegion)
    (Offset.contains_base _ (by omega : 4 * j + 32 / 8 ≤ 52) (by omega)) sep (by decide : 32 / 8 < 2 ^ 64)
  have address : g.argumentsRegion.base + BitVec.ofNat 64 (4 * j) =
      byteAddr g.stack + BitVec.ofNat 64 (VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes + 20 + 4 * j) :=
    Offset.add_add _ _ _
  change (entered s).mem.readW (g.argumentsRegion.base + BitVec.ofNat 64 (4 * j)) 32 =
    s.mem.readW (g.argumentsRegion.base + BitVec.ofNat 64 (4 * j)) 32 at eq
  rw [address] at eq
  exact eq.trans (h.arguments j hj)

theorem EntryInput.ready {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : EntryInput g bs s) : FnInput g bs s := by
  refine ⟨h.stackFit, ⟨h.valid, h.enteredSp, ?_, h.enteredSource,
    entered_write h.workspaceWrite,
    entered_read h.argumentsRead, h.enteredArguments⟩, h.returnSeparate⟩
  refine ⟨by have := h.valid.stackHigh; omega, ?_⟩
  change (⟨byteAddr g.stack, VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes⟩ : Region) ∈
    ⟨byteAddr ((entered s).gpr .esp), VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes⟩ :: (pushed savedRegisters s).wr
  rw [h.enteredSp]
  exact List.mem_cons_self
end VG.Proof.RsaPkcs1Sig.X86.Ver
end

end

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86 VG.Proof.Bignum.X86
open VG.Proof.Dsa.X86 (argumentPointer)

theorem verify_contract_pre (s : State) (pre : (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi verifyStack).pre s) :
    FnInput (verifyGeometry s) (verifyBytes s) s := by
  have h := verifyABI_of pre
  have fits : ∀ i, ((verifyGeometry s).sources i).toNat + (verifyGeometry s).sourceLength i ≤ 2 ^ 32 := by
    intro i
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl
    exacts [h.sourceFit0, h.sourceFit1, h.sourceFit2, h.sourceFit3, h.sourceFit4]
  have geometry : (verifyGeometry s).Valid := by
    refine ⟨h.valid.1, h.valid.2, h.ePositive, h.eFits, (arg s 6).isLt, (arg s 8).isLt,
      h.preLength, h.space, ?_, ?_, fits, h.workspaceFit, ?_, ?_, ?_, ?_, ?_⟩
    · rw [verifyGeometry_stackNat s h.stackLow]
      have := h.stackLow
      simp only [verifyStack] at this
      omega
    · rw [verifyGeometry_stackNat s h.stackLow]
      have := h.stackBound
      simp only [VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes]
      omega
    · intro i
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl
      exacts [h.sourceWorkspace0, h.sourceWorkspace1, h.sourceWorkspace2, h.sourceWorkspace3, h.sourceWorkspace4]
    · rw [verifyGeometry_arguments s h.stackLow h.stackBound]; exact h.workspaceArguments
    · intro i
      rw [verifyGeometry_wholeStack s h.stackLow]
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl
      exacts [h.stackSource0, h.stackSource1, h.stackSource2, h.stackSource3, h.stackSource4]
    · rw [verifyGeometry_wholeStack s h.stackLow]; exact h.stackWorkspace
    · rw [verifyGeometry_wholeStack s h.stackLow, verifyGeometry_arguments s h.stackLow h.stackBound]
      exact h.stackArguments
  apply EntryInput.ready
  refine ⟨geometry, h.stackLow, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨fits i, ?_, rfl⟩
    refine ⟨(verifyGeometry s).sourceRegion i, List.mem_append_left _ ?_, Region.contains_self _ _⟩
    rw [h.rd]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  · rw [h.wr]
    exact ⟨_, by simp [verifyGeometry, byteAddr, argumentPointer], Region.contains_self _ _⟩
  · rw [verifyGeometry_arguments s h.stackLow h.stackBound]
    exact ⟨_, List.mem_append_right _ (by rw [h.wr]; simp), Region.contains_self _ _⟩
  · intro j hj
    have address : byteAddr (verifyGeometry s).stack + BitVec.ofNat 64 (VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes + 20 + 4 * j) = argAddr s j := by
      rw [← Offset.add_add]
      change (verifyGeometry s).argumentsRegion.base + BitVec.ofNat 64 (4 * j) = _
      rw [verifyGeometry_arguments s h.stackLow h.stackBound]
      simp only [argAddr, Nat.mul_zero, Nat.add_zero]
      have bound := h.stackBound
      have first := byteAddr_add (by omega : (s.gpr .esp).toNat + 4 < 2 ^ 32)
      have last := byteAddr_add (by omega : (s.gpr .esp).toNat + (4 + 4 * j) < 2 ^ 32)
      change byteAddr (s.gpr .esp + BitVec.ofNat 32 4) + BitVec.ofNat 64 (4 * j) = byteAddr (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * j))
      rw [first, last, Offset.add_add]
    rw [address]
    change arg s j = _
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [verifyGeometry, Geometry.argument, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    all_goals rfl
  · intro r hr
    have belowRet : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (verifyGeometry s).wholeStack := by
      rw [verifyGeometry_wholeStack s h.stackLow]
      have sep := Offset.disjoint_base ((s.gpr .esp).setWidth 64 - BitVec.ofNat 64 verifyStack)
        (Nat.le_refl verifyStack) (by decide : verifyStack + 4 ≤ 2 ^ 64)
      rw [BitVec.sub_add_cancel] at sep
      exact sep
    simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact belowRet.sub_right geometry.innerSub
    · exact belowRet.sub_right geometry.calleeSub
    · exact h.returnWorkspace

end VG.Proof.RsaPkcs1Sig.X86.Ver
