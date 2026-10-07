import VerifiedGarbage.Proof.Ed448.AArch64.VerifyMain
import VerifiedGarbage.Proof.Ed448.AArch64.VerifyCT.Front
import VerifiedGarbage.Proof.Ed448.AArch64.VerifyCT.Windows
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.ConstMem

/-!
# Ed448 verification's equation on AArch64: `Verified`

Untrusted: everything here is checked by Lean. Correctness including the ABI,
given decoding's agreement with the specification (`RecoverOk`, which the
registration files pass in); constant time (by taint tracking, phase by phase, `VerifyCT/`: the only
branches are on the counters, every address is an argument or the static's
address plus a constant or a counter, and the digits' masks only select); and a
concrete state satisfying the signature's contract, under the calling
convention with the comb's tables (`Abi.withConsts combConsts`). The contract lets timing depend on the inputs; the
code's depends on the pointers alone.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64

open VG.Impl.X448.AArch64.Base (combSym combWords combConsts)
open VG.Proof.X448.AArch64.Base (CombHeld combWords_length combConsts_eq satMem satMem_held)

def verifyEquationSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | _ => 0
  sp := 0x8000
  mem := satMem
  rd := [⟨0x1000, 57⟩, ⟨0x2000, 114⟩, ⟨0x3000, 57⟩, ⟨0x100000, 58368⟩]
  wr := [⟨0x4000, 8192⟩]
  syms _ := 0x100000

theorem verifyEquation_ok (hR : Proof.Ed448.RecoverOk) (s : State) (hs : verifyEquationLocal.pre s) :
    ∃ t s', Exec isa verifyEquation s t s' ∧ abiPreserved s s' ∧ verifyEquationLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := verifyEquation_correct hR hs
  exact ⟨t, s', he, ⟨h.1, Exec.sp he, h.2.1⟩, h.2.2⟩

theorem verifyEquation_ct :
    ConstantTime isa verifyEquationLocal.pre verifyEquationLocal.pub verifyEquation := by
  obtain ⟨_, e₁⟩ := front_ct
  obtain ⟨_, e₂⟩ := table_ct
  obtain ⟨_, e₃⟩ := sBase_ct
  obtain ⟨_, e₄⟩ := kWindows_ct
  obtain ⟨_, e₅⟩ := tail_ct
  refine VG.Taint.constantTime (A := taintS [combSym]) (Taint.ofRegs [.x0, .x1, .x2, .x3]) ?_
    (seq_ok e₁ (seq_ok e₂ (seq_ok e₃ (seq_ok e₄ e₅))))
  intro s₁ s₂ _ _ ⟨hsp, h0, h1, h2, h3, hsy⟩
  refine ⟨⟨hsp, fun r hr => ?_⟩, fun n hn => ?_⟩
  · simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [h0, h1, h2, h3]
  · simp only [List.mem_singleton] at hn; subst hn; exact hsy

theorem verifyEquation_eqOk (hR : Proof.Ed448.RecoverOk) : EqOk := ⟨verifyEquation_ok hR, verifyEquation_ct⟩

/-- The shared contract's precondition, from its facts. -/
theorem verifyEquation_spec_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .x0, 57⟩, ⟨s.gpr .x1, 114⟩, ⟨s.gpr .x2, 57⟩,
      ⟨s.syms combSym, 8 * combWords.length⟩])
    (hw : s.wr = [⟨s.gpr .x3, 8192⟩])
    (h1 : Region.Disjoint ⟨s.gpr .x0, 57⟩ ⟨s.gpr .x3, 8192⟩)
    (h2 : Region.Disjoint ⟨s.gpr .x1, 114⟩ ⟨s.gpr .x3, 8192⟩)
    (h3 : Region.Disjoint ⟨s.gpr .x2, 57⟩ ⟨s.gpr .x3, 8192⟩)
    (f0 : (s.gpr .x0).toNat + 57 ≤ 2 ^ 64) (f1 : (s.gpr .x1).toNat + 114 ≤ 2 ^ 64)
    (f2 : (s.gpr .x2).toNat + 57 ≤ 2 ^ 64) (f3 : (s.gpr .x3).toNat + 8192 ≤ 2 ^ 64)
    (ht : CombHeld s [⟨s.gpr .x3, 8192⟩]) :
    (Spec.Ed448.verifyEquationContract (AArch64.abi.withConsts combConsts)).pre s := by
  sig_pre [Spec.Ed448.verifyEquationContract, Spec.Ed448.verifyEquationSig, Spec.Ed448.scratchWords,
    AArch64.abi, AArch64.argRegs, combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨by rw [hrd]; rfl, held, fit, by rw [hw]; exact hdw, by rw [hrd]; rfl, hw, h1, h2, h3, f0, f1,
    f2, f3⟩

theorem verifyEquation_sat :
    (Spec.Ed448.verifyEquationContract (AArch64.abi.withConsts combConsts)).pre verifyEquationSat := by
  have hl := combWords_length
  have held : ∀ i < combWords.length, verifyEquationSat.mem.readW (verifyEquationSat.syms combSym +
      BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0 := satMem_held
  refine verifyEquation_spec_pre (by rw [hl]; rfl) rfl (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide)) (by decide) (by decide)
    (by decide) (by decide) ⟨held, ?_, ?_⟩
  all_goals rw [hl]
  · decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl; exact Region.disjoint_of_sep (by decide)

theorem verifyEquation_implies :
    verifyEquationLocal.Implies (Spec.Ed448.verifyEquationContract (AArch64.abi.withConsts combConsts)) where
  pre s h := by
    sig_pre [Spec.Ed448.verifyEquationContract, Spec.Ed448.verifyEquationSig, Spec.Ed448.scratchWords,
      AArch64.abi, AArch64.argRegs, combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
      stackBelow] at h
    obtain ⟨hd, hheld, hfit, hdw, ht, hw, h1, h2, h3, -, -, -, h4⟩ := h
    refine ⟨?_, hw, h1, h2, h3, h4, hheld, hfit, by rw [hw] at hdw; exact hdw⟩
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
  post s t _ h := by
    sig_post [Spec.Ed448.verifyEquationContract, Spec.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, AArch64.abi, AArch64.argRegs, combConsts_eq, Abi.withConsts]
    have h' : t.gpr .x0 = _ := h
    rw [h']
    generalize Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt s.mem (s.gpr .x0) 57)
      (Spec.Ed448.bytesAt s.mem (s.gpr .x1) 114) (Spec.Ed448.bytesAt s.mem (s.gpr .x2) 57) = b
    cases b <;> rfl
  pub s t _ _ h := by
    sig_pub [Spec.Ed448.verifyEquationContract, Spec.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, AArch64.abi, AArch64.argRegs, combConsts_eq, Abi.withConsts] at h
    obtain ⟨sp, hsy, -, pk, sig, ch, base⟩ := h
    exact ⟨sp, pk, sig, ch, base, hsy⟩
  sat := ⟨verifyEquationSat, verifyEquation_sat⟩

theorem verifyEquation_verified (hR : Proof.Ed448.RecoverOk) :
    Verified AArch64.target verifyEquation
      (Spec.Ed448.verifyEquationContract (AArch64.abi.withConsts combConsts)) :=
  Verified.of_correct (verifyEquation_ok hR) verifyEquation_ct verifyEquation_implies

end VG.Proof.Ed448.AArch64
