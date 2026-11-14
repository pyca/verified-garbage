module

public import VerifiedGarbage.Proof.Rc2.X86.Cbc.Verified
public import VerifiedGarbage.Proof.Rc2.CbcScratch
public import VerifiedGarbage.Impl.StackScratch.X86
import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Rc2.X86.Cbc.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rc2.X86.Cbc.Correct
import VerifiedGarbage.Proof.Rc2.X86.Cbc.ConstantTime

/-! # RC2-CBC in place on X86, with wiped stack working space -/
-- separate module: exporting CBC does not rebuild its existing streaming callers.

@[expose] public section

namespace VG.Proof.Rc2.X86.Cbc

open VG VG.X86

theorem wide_pre (d : Spec.Rc2.Direction) (s : State) (h : (wideContract d).pre s) :
    (contract d).pre (s.withRegions (narrowRd s) (narrowWr s)) := by
  simp only [contract, wideContract, narrowRd, narrowWr, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, arg_withRegions, argAddr_withRegions] at h ⊢
  exact ⟨trivial, trivial, h.2.2⟩

theorem wide_verified (d : Spec.Rc2.Direction) (hsat : ∃ s, (wideContract d).pre s) :
    Verified X86.target (Impl.Rc2.X86.Cbc.cbc d) (wideContract d) := by
  have narrowSat : ∃ s, (contract d).pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, wide_pre d s hs⟩
  have hc : ∀ s, (contract d).pre s → ∃ t s',
      Exec isa (Impl.Rc2.X86.Cbc.cbc d) s t s' ∧ abiPreserved s s' ∧ (contract d).post s s' := by
    intro s hs
    exact cbc_body_correct d s hs
  refine regionModel.verified_narrowTo (T := X86.target) (fun _ _ _ _ h => h)
    (Verified.of_correct hc (cbc_constantTime d) (.refl narrowSat))
    narrowRd narrowWr (wide_pre d) ?_ ?_ ?_ ?_ hsat
  · intro s h
    obtain ⟨rd, wr, _⟩ := h
    change Covers (narrowRd s ++ narrowWr s) (s.rd ++ s.wr)
    rw [rd, wr]
    intro p n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [narrowRd, narrowWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h | h <;> simp only [h, true_or, or_true]
  · intro s h
    obtain ⟨_, wr, _⟩ := h
    change Covers (narrowWr s) s.wr
    rw [wr]
    intro p n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [narrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h <;> simp only [h, true_or, or_true]
  · intro s s' _ h
    simpa only [regionModel, contract, wideContract, narrowRd, narrowWr, State.withRegions_gpr, State.withRegions_mem, State.withRegions_rd, State.withRegions_wr, arg_withRegions, argAddr_withRegions] using h
  · intro s₁ s₂ _ _ h
    simpa only [regionModel, contract, wideContract, narrowRd, narrowWr, State.withRegions_gpr, State.withRegions_mem, State.withRegions_rd, State.withRegions_wr, arg_withRegions, argAddr_withRegions] using h

def scratchSat : State where
  gpr r := if r = .esp then 0x6000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem p := if p = 0x6005 then 0x10 else if p = 0x6009 then 0x20 else
    if p = 0x600d then 0x30 else if p = 0x6015 then 0x40 else 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x4000, 512⟩, ⟨0x6004, 20⟩]

def frameSat : State := { scratchSat with wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x6004, 16⟩] }

theorem encryptChained_implies : (wideContract .encrypt).Implies
    (Proof.Rc2.cbcEncChainedScratchContract abi 64 16) where
  pre := by
    intro s h
    sig_pre [Proof.Rc2.cbcEncChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcEncChainedPost, wideContract, contract, abi, argSlots, argVal, argBytes, below] at h
    sig_split h
    sig_reduce [Proof.Rc2.cbcEncChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcEncChainedPost, wideContract, contract, abi, argSlots, argVal, argBytes, below]
    simp only [addr32, Nat.mul_comm] at *
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega_arith
      | (rw [Taint.sub_setWidth (by omega_arith)]
         first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  post := by
    intro s s' _ h
    sig_post [Proof.Rc2.cbcEncChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcEncChainedPost, wideContract, contract, abi, argSlots, argVal, argBytes, below]
    exact Proof.Rc2.cbcEncChainedPost_of_blocks (r := 0) h.1 h.2
  pub := by sig_implies_pub [Proof.Rc2.cbcEncChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcEncChainedPost, wideContract, contract, abi, argSlots, argVal, argBytes, below]
  sat := by sig_implies_sat [Proof.Rc2.cbcEncChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcEncChainedPost, wideContract, contract, abi, argSlots, argVal, argBytes, below] [scratchSat, arg, argAddr, Mem.readW, Mem.read] using scratchSat

theorem encryptChained_verified :
    Verified X86.target Impl.Rc2.X86.Cbc.encrypt
      (Proof.Rc2.cbcEncChainedScratchContract abi 64 16) :=
  Verified.of_implies (wide_verified .encrypt encryptChained_implies.sat_left) encryptChained_implies

theorem encryptChainedFrameSat : ∃ s, (Spec.Rc2.cbcEncryptChainedContract abi 560).pre s := by
  implies_sat [Spec.Rc2.cbcEncryptChainedContract, Spec.Rc2.cbcChainedSig, abi, argSlots, argVal, argBytes, below]
    [frameSat, scratchSat, arg, argAddr, Mem.readW, Mem.read] using frameSat

theorem encryptChained_framed :
    Verified X86.target
      (Impl.StackScratch.X86.withStackScratchWiped 544 4 128 Impl.Rc2.X86.Cbc.encrypt)
      (Spec.Rc2.cbcEncryptChainedContract abi 560) :=
  X86.Verified.stackScratchWiped (sig := Spec.Rc2.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 64) (post := Proof.Rc2.cbcEncChainedPost abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 544) encryptChained_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Rc2.cbcEncChainedPost_local _) (Proof.Rc2.cbcEncChainedPostOut_local _) encryptChainedFrameSat

theorem decryptChained_implies : (wideContract .decrypt).Implies
    (Proof.Rc2.cbcDecChainedScratchContract abi 64 16) where
  pre := by
    intro s h
    sig_pre [Proof.Rc2.cbcDecChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcDecChainedPost, wideContract, contract, abi, argSlots, argVal, argBytes, below] at h
    sig_split h
    sig_reduce [Proof.Rc2.cbcDecChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcDecChainedPost, wideContract, contract, abi, argSlots, argVal, argBytes, below]
    simp only [addr32, Nat.mul_comm] at *
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega_arith
      | (rw [Taint.sub_setWidth (by omega_arith)]
         first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  post := by
    intro s s' _ h
    sig_post [Proof.Rc2.cbcDecChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcDecChainedPost, wideContract, contract, abi, argSlots, argVal, argBytes, below]
    exact Proof.Rc2.cbcDecChainedPost_of_blocks (r := 0) h.1 h.2
  pub := by sig_implies_pub [Proof.Rc2.cbcDecChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcDecChainedPost, wideContract, contract, abi, argSlots, argVal, argBytes, below]
  sat := by sig_implies_sat [Proof.Rc2.cbcDecChainedScratchContract, Proof.Rc2.cbcChainedScratchSig, Spec.Rc2.cbcChainedSig, Proof.Rc2.cbcDecChainedPost, wideContract, contract, abi, argSlots, argVal, argBytes, below] [scratchSat, arg, argAddr, Mem.readW, Mem.read] using scratchSat

theorem decryptChained_verified :
    Verified X86.target Impl.Rc2.X86.Cbc.decrypt
      (Proof.Rc2.cbcDecChainedScratchContract abi 64 16) :=
  Verified.of_implies (wide_verified .decrypt decryptChained_implies.sat_left) decryptChained_implies

theorem decryptChainedFrameSat : ∃ s, (Spec.Rc2.cbcDecryptChainedContract abi 560).pre s := by
  implies_sat [Spec.Rc2.cbcDecryptChainedContract, Spec.Rc2.cbcChainedSig, abi, argSlots, argVal, argBytes, below]
    [frameSat, scratchSat, arg, argAddr, Mem.readW, Mem.read] using frameSat

theorem decryptChained_framed :
    Verified X86.target
      (Impl.StackScratch.X86.withStackScratchWiped 544 4 128 Impl.Rc2.X86.Cbc.decrypt)
      (Spec.Rc2.cbcDecryptChainedContract abi 560) :=
  X86.Verified.stackScratchWiped (sig := Spec.Rc2.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 64) (post := Proof.Rc2.cbcDecChainedPost abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 544) decryptChained_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Rc2.cbcDecChainedPost_local _) (Proof.Rc2.cbcDecChainedPostOut_local _) decryptChainedFrameSat

end VG.Proof.Rc2.X86.Cbc
