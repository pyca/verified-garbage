import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBaseCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBasePrecomputedCT
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig

/-! The precomputed variant satisfies the same reviewed ABI contract, with 8 bytes of stack for
its call of `vg_gf25519_r64_invert`: correct and constant time as its code with the inversion
inlined (`Verified.of_inline`); callers get its correctness and constant time for states that
keep their buffers off those 8 bytes (`scalarBase_precomputed_ok`, `scalarBaseLocal.clear`). -/
namespace VG.Proof.Ed25519.X86_64
open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {fld : Arith} [EdArith fld]

theorem scalarBase_precomputed_okI [X25519.X86_64.DivstepInv] (s : State) (hs : scalarBaseLocal.pre s) :
    ∃ t s', Exec isa (scalarBase_precomputed fld).inline s t s' ∧
      abiPreserved s s' ∧ scalarBaseLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := scalarBase_correct_of_engine _ (scalarBasePrecomputedEngine_ok (fld := fld)) hs
  rw [← scalarBaseWith_inline] at he
  exact ⟨t, s', he, abiPreserved_of_exec (by rw [Code.allInstrs_inline]; fld_lit_decide) he h.1, h.2⟩

omit [EdArith fld] in
/-- The output is apart from the call's return address. -/
theorem scalarBase_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64) (hs : scalarBaseLocal.pre s)
    (hcl : Clear (hole (s.gpr .rsp)) s) (hp : scalarBaseLocal.post s b) :
    scalarBaseLocal.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain ⟨-, hw, -⟩ := hs
  have hb := Clear.wr_bytes hcl (p := s.gpr .rdi) (n := 32) (by rw [hw]; simp) (by decide)
  exact (bytes_patch hb).trans hp

/-- The code's correctness, for callers. -/
theorem scalarBase_precomputed_ok [X25519.X86_64.DivstepInv] :
    ∀ s, scalarBaseLocal.clear.pre s → ∃ t s', Exec isa (scalarBase_precomputed fld) s t s' ∧
      abiPreserved s s' ∧ scalarBaseLocal.post s s' :=
  ok_of_inline (by fld_lit_decide) scalarBase_precomputed_okI scalarBase_patch

/-- The code's constant time, for callers. -/
theorem scalarBase_precomputed_ctC [X25519.X86_64.DivstepInv] :
    ConstantTime isa scalarBaseLocal.clear.pre scalarBaseLocal.pub (scalarBase_precomputed fld) :=
  ct_of_inline (by fld_lit_decide)
    (fun s h => let ⟨t, s', e, _⟩ := scalarBase_precomputed_okI s h; ⟨t, s', e⟩) (fun _ _ h => h.1)
    scalarBase_precomputed_ct

theorem combConsts_eq : combConsts = [(combSym, combWords)] := rfl

/-- The memory of the contract's witness: the tables at `0x100000` (irreducible: unfolding it
in a definitional check would evaluate the tables). -/
@[irreducible] def combSatMem : Mem := constMem 0x100000 combWords

theorem combSatMem_held : ∀ i < combWordCount,
    combSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0 := by
  unfold combSatMem
  intro i hi
  exact constMem_held _ _ (by rw [combWords_length]; simp only [combWordCount]; omega) i
    (by rw [combWords_length]; exact hi)

/-- A state satisfying the precondition. -/
def baseSatStateT : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := combSatMem
  rd := [⟨0x2000, 32⟩, ⟨0x100000, 40448⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x3000, 8192⟩]
  syms _ := 0x100000

/-- The shared contract's precondition, from its facts. -/
theorem scalarBase_spec_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .rsi, 32⟩, ⟨s.syms combSym, 40448⟩])
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

/-- The shared contract's precondition with 8 bytes of stack, from its facts. -/
theorem scalarBase_spec_pre8 {s : State}
    (hrd : s.rd = [⟨s.gpr .rsi, 32⟩, ⟨s.syms combSym, 40448⟩])
    (hw : s.wr = [⟨s.gpr .rdi, 32⟩, ⟨s.gpr .rdx, 8192⟩])
    (h1 : Region.Disjoint ⟨s.gpr .rdi, 32⟩ ⟨s.gpr .rsi, 32⟩)
    (h2 : Region.Disjoint ⟨s.gpr .rdi, 32⟩ ⟨s.gpr .rdx, 8192⟩)
    (h3 : Region.Disjoint ⟨s.gpr .rsi, 32⟩ ⟨s.gpr .rdx, 8192⟩)
    (r1 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdi, 32⟩) (r2 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rsi, 32⟩)
    (r3 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdx, 8192⟩)
    (q1 : Region.Disjoint ⟨s.gpr .rsp - 8#64, 8⟩ ⟨s.gpr .rdi, 32⟩)
    (q2 : Region.Disjoint ⟨s.gpr .rsp - 8#64, 8⟩ ⟨s.gpr .rsi, 32⟩)
    (q3 : Region.Disjoint ⟨s.gpr .rsp - 8#64, 8⟩ ⟨s.gpr .rdx, 8192⟩)
    (f0 : (s.gpr .rdi).toNat + 32 ≤ 2 ^ 64) (f1 : (s.gpr .rsi).toNat + 32 ≤ 2 ^ 64)
    (f2 : (s.gpr .rdx).toNat + 8192 ≤ 2 ^ 64) (hsp : 8 ≤ (s.gpr .rsp).toNat)
    (ht : CombHeld s [⟨s.gpr .rdi, 32⟩, ⟨s.gpr .rdx, 8192⟩, ⟨s.gpr .rsp, 8⟩])
    (hq : Region.Disjoint ⟨s.syms combSym, 40448⟩ ⟨s.gpr .rsp - 8#64, 8⟩) :
    (Spec.Ed25519.scalarBaseContract (X86_64.abi.withConsts combConsts) 8).pre s := by
  sig_pre [Spec.Ed25519.scalarBaseContract, Spec.Ed25519.scalarBaseSig, Spec.Ed25519.scratchWords,
    X86_64.abi, X86_64.argRegs, combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow, combWords_length]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨hsp, by rw [hrd]; rfl, held, fit, by rw [hw]; exact fun r hr => hdw r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h]),
    hdw _ (by simp), hq, by rw [hrd]; rfl, hw, h1, h2, h3, r1, r2, r3, q1, q2, q3, f0, f1, f2⟩

theorem scalarBase_sat8 :
    (Spec.Ed25519.scalarBaseContract (X86_64.abi.withConsts combConsts) 8).pre baseSatStateT := by
  refine scalarBase_spec_pre8 rfl rfl (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide)) (by decide) (by decide)
    (by decide) (by decide) ⟨combSatMem_held, by decide, ?_⟩ (Region.disjoint_of_sep (by decide))
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)

/-- The contract with 8 bytes of stack, for the call's return address. -/
theorem scalarBase_implies8 :
    scalarBaseLocal.Implies (Spec.Ed25519.scalarBaseContract (X86_64.abi.withConsts combConsts) 8) :=
  scalarBase_implies.stack8 ⟨baseSatStateT, scalarBase_sat8⟩

theorem scalarBase_verified_of {c : Prog isa} (hc : c.InlineOk = true)
    (hcor : ∀ s, scalarBaseLocal.pre s →
      ∃ t s', Exec isa c.inline s t s' ∧ abiPreserved s s' ∧ scalarBaseLocal.post s s')
    (hct : ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub c.inline) :
    Verified X86_64.target c (Spec.Ed25519.scalarBaseContract (X86_64.abi.withConsts combConsts) 8) :=
  Verified.of_inline hc hcor hct scalarBase_implies8 (fun _ h => Sig.clear_of_pre_consts h)
    (fun s b hv u hs hp => scalarBase_patch s b hv u (scalarBase_implies8.pre s hs)
      (Sig.clear_of_pre_consts hs) hp)
    (fun s₁ s₂ h₁ h₂ hp => (scalarBase_implies8.pub s₁ s₂ h₁ h₂ hp).1)

theorem scalarBase_precomputed_verified [X25519.X86_64.DivstepInv] : Verified X86_64.target (scalarBase_precomputed fld)
    (Spec.Ed25519.scalarBaseContract (X86_64.abi.withConsts combConsts) 8) :=
  scalarBase_verified_of (by fld_lit_decide) scalarBase_precomputed_okI scalarBase_precomputed_ct

end VG.Proof.Ed25519.X86_64
