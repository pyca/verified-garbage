import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBaseCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBasePrecomputedCT

/-! The precomputed variant satisfies the same reviewed ABI contract. -/
namespace VG.Proof.Ed25519.X86_64
open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {fld : Arith} [EdArith fld]

theorem scalarBase_precomputed_ok [X25519.X86_64.DivstepInv] (s : State) (hs : scalarBaseLocal.pre s) :
    ∃ t s', Exec isa (scalarBase_precomputed fld) s t s' ∧
      abiPreserved s s' ∧ scalarBaseLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := scalarBase_correct_of_engine (scalarBasePrecomputedEngine fld)
    scalarBasePrecomputedEngine_ok hs
  exact ⟨t, s', he, abiPreserved_of_exec (by fld_lit_decide) he h.1, h.2⟩

theorem combConsts_eq : combConsts = [(combSym, combWords)] := rfl

/-- The memory of the contract's witness: the tables at `0x100000` (irreducible: unfolding it
in a definitional check would evaluate the tables). -/
@[irreducible] def combSatMem : Mem := constMem 0x100000 combWords

theorem combSatMem_held : ∀ i < 3072,
    combSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0 := by
  unfold combSatMem
  intro i hi
  exact constMem_held _ _ (by rw [combWords_length]; omega) i (by rw [combWords_length]; exact hi)

/-- A state satisfying the precondition. -/
def baseSatStateT : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := combSatMem
  rd := [⟨0x2000, 32⟩, ⟨0x100000, 24576⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x3000, 8192⟩]
  syms _ := 0x100000

/-- The shared contract's precondition, from its facts. -/
theorem scalarBase_spec_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .rsi, 32⟩, ⟨s.syms combSym, 24576⟩])
    (hw : s.wr = [⟨s.gpr .rdi, 32⟩, ⟨s.gpr .rdx, 8192⟩])
    (h1 : Region.Disjoint ⟨s.gpr .rdi, 32⟩ ⟨s.gpr .rsi, 32⟩)
    (h2 : Region.Disjoint ⟨s.gpr .rdi, 32⟩ ⟨s.gpr .rdx, 8192⟩)
    (h3 : Region.Disjoint ⟨s.gpr .rsi, 32⟩ ⟨s.gpr .rdx, 8192⟩)
    (r1 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdi, 32⟩) (r2 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rsi, 32⟩)
    (r3 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdx, 8192⟩)
    (f0 : (s.gpr .rdi).toNat + 32 ≤ 2 ^ 64) (f1 : (s.gpr .rsi).toNat + 32 ≤ 2 ^ 64)
    (f2 : (s.gpr .rdx).toNat + 8192 ≤ 2 ^ 64)
    (ht : CombHeld s [⟨s.gpr .rdi, 32⟩, ⟨s.gpr .rdx, 8192⟩, ⟨s.gpr .rsp, 8⟩]) :
    (Spec.Ed25519.scalarBaseContract (X86_64.abi.withConsts combConsts)).pre s := by
  sig_pre [Spec.Ed25519.scalarBaseContract, Spec.Ed25519.scalarBaseSig, Spec.Ed25519.scratchWords,
    X86_64.abi, X86_64.argRegs, combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow, combWords_length]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨by rw [hrd]; rfl, held, fit, by rw [hw]; exact fun r hr => hdw r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h]),
    hdw _ (by simp), by rw [hrd]; rfl, hw, h1, h2, h3, r1, r2, r3, f0, f1, f2⟩

theorem scalarBase_sat :
    (Spec.Ed25519.scalarBaseContract (X86_64.abi.withConsts combConsts)).pre baseSatStateT := by
  refine scalarBase_spec_pre rfl rfl (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (by decide) (by decide) (by decide) ⟨combSatMem_held, by decide, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)

theorem scalarBase_implies :
    scalarBaseLocal.Implies (Spec.Ed25519.scalarBaseContract (X86_64.abi.withConsts combConsts)) where
  pre s h := by
    sig_pre [Spec.Ed25519.scalarBaseContract, Spec.Ed25519.scalarBaseSig, Spec.Ed25519.scratchWords,
      X86_64.abi, X86_64.argRegs, combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
      stackBelow, combWords_length] at h
    obtain ⟨hd, hheld, hfit, hdw, hdr, ht, hw, -, h2, h3, r1, -, r3, -, -, f2⟩ := h
    refine ⟨?_, hw, h3, r1, r3, f2, hheld, hfit, fun r hr => ?_⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hdw _ (by rw [hw]; simp)
      · exact hdw _ (by rw [hw]; simp)
      · exact hdr
  post := by
    intro s s' _ h
    sig_post [Spec.Ed25519.scalarBaseContract, Spec.Ed25519.scalarBaseSig, Spec.Ed25519.scratchWords,
      X86_64.abi, X86_64.argRegs, combConsts_eq, Abi.withConsts, scalarBaseLocal]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Ed25519.scalarBaseContract, Spec.Ed25519.scalarBaseSig, Spec.Ed25519.scratchWords,
      X86_64.abi, X86_64.argRegs, combConsts_eq, Abi.withConsts] at h
    obtain ⟨h0, hs, h1, h2, h3⟩ := h
    exact ⟨h0, h1, h2, h3, hs⟩
  sat := ⟨baseSatStateT, scalarBase_sat⟩

theorem scalarBase_precomputed_verified [X25519.X86_64.DivstepInv] : Verified X86_64.target (scalarBase_precomputed fld)
    (Spec.Ed25519.scalarBaseContract (X86_64.abi.withConsts combConsts)) :=
  Verified.of_correct scalarBase_precomputed_ok scalarBase_precomputed_ct scalarBase_implies

end VG.Proof.Ed25519.X86_64
