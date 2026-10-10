import VerifiedGarbage.Proof.Ed448.AArch64.Base.Main
import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
import VerifiedGarbage.Proof.X448.AArch64.Base.Erase
import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Ed448 base-point multiplication on AArch64: `Verified`

Correctness including the ABI; constant time (by taint tracking: the only
branches are on the counters, every address is an argument or the static's
address plus a constant or a counter, and the digits' masks only select); and
a concrete state satisfying the signature's contract, under the calling
convention with the comb's tables (`Abi.withConsts combConsts`).
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64.Base (combSym combWords combConsts)
open VG.Proof.X448.AArch64.Base (CombHeld combWords_length combConsts_eq satMem satMem_held)

theorem scalarBase_ok (s : State) (hs : scalarBaseLocal.pre s) :
    ∃ t s', Exec isa scalarBase s t s' ∧ abiPreserved s s' ∧ scalarBaseLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := scalarBase_correct hs
  exact ⟨t, s', he, ⟨h.1, Exec.sp he, h.2.1⟩, h.2.2⟩

/-- The analysis, of the code without what it does not read, its comb's field operations analysed
once each (`Proof/X448/AArch64/Base/Erase.lean`). -/
theorem scalarBase_check :
    ∃ h, ((taintS [combSym]).check (Taint.ofRegs [.x0, .x1, .x2]) scalarBase h).isSome = true := by
  apply exists_isSome_of_eraseT
  refine Split.exists_isSome (c' := ?c') ?s ⟨?h, ?g⟩
  case s =>
    simp only [scalarBase, encode, Code.eraseT, Impl.X448.AArch64.Fast.invert, ops_eraseT, sqn_eraseT]
    exact .seq (.refl _) (.seq (.loop _ (stepN_split 57)) (.seq (.refl _) (.refl _)))
  case g => taint_decide

theorem scalarBase_ct : ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub scalarBase :=
  let ⟨_, hc⟩ := scalarBase_check
  VG.Taint.constantTime (A := taintS [combSym]) (Taint.ofRegs [.x0, .x1, .x2])
    (fun _ _ _ _ ⟨hsp, h0, h1, h2, hsy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [h0, h1, h2]⟩, fun n hn => by
      simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩) hc

theorem scalarBase_baseOk : BaseOk := ⟨scalarBase_ok, scalarBase_ct⟩

/-- The shared contract's precondition, from its facts. -/
theorem scalarBase_spec_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .x1, 57⟩, ⟨s.syms combSym, 8 * combWords.length⟩])
    (hw : s.wr = [⟨s.gpr .x0, 57⟩, ⟨s.gpr .x2, 8192⟩])
    (h1 : Region.Disjoint ⟨s.gpr .x0, 57⟩ ⟨s.gpr .x1, 57⟩)
    (h2 : Region.Disjoint ⟨s.gpr .x0, 57⟩ ⟨s.gpr .x2, 8192⟩)
    (h3 : Region.Disjoint ⟨s.gpr .x1, 57⟩ ⟨s.gpr .x2, 8192⟩)
    (f0 : (s.gpr .x0).toNat + 57 ≤ 2 ^ 64) (f1 : (s.gpr .x1).toNat + 57 ≤ 2 ^ 64)
    (f2 : (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64)
    (ht : CombHeld s [⟨s.gpr .x0, 57⟩, ⟨s.gpr .x2, 8192⟩]) :
    (Spec.Ed448.scalarBaseContract (AArch64.abi.withConsts combConsts)).pre s := by
  sig_pre [Spec.Ed448.scalarBaseContract, Spec.Ed448.scalarBaseSig, Spec.Ed448.scratchWords,
    AArch64.abi, AArch64.argRegs, combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨by rw [hrd]; rfl, held, fit, by rw [hw]; exact hdw, by rw [hrd]; rfl, hw, h1, h2, h3, f0, f1, f2⟩

def scalarBaseSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | _ => 0
  sp := 0x8000
  mem := satMem
  rd := [⟨0x2000, 57⟩, ⟨0x100000, 58368⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x3000, 8192⟩]
  syms _ := 0x100000

theorem scalarBase_sat :
    (Spec.Ed448.scalarBaseContract (AArch64.abi.withConsts combConsts)).pre scalarBaseSat := by
  have hl := combWords_length
  have held : ∀ i < combWords.length, scalarBaseSat.mem.readW (scalarBaseSat.syms combSym +
      BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0 := satMem_held
  refine scalarBase_spec_pre (by rw [hl]; rfl) rfl (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide)) (by decide) (by decide)
    (by decide) ⟨held, ?_, ?_⟩
  all_goals rw [hl]
  · decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)

theorem scalarBase_implies : scalarBaseLocal.Implies
    (Spec.Ed448.scalarBaseContract (AArch64.abi.withConsts combConsts)) where
  pre s h := by
    sig_pre [Spec.Ed448.scalarBaseContract, Spec.Ed448.scalarBaseSig, Spec.Ed448.scratchWords,
      AArch64.abi, AArch64.argRegs, combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
      stackBelow] at h
    obtain ⟨hd, hheld, hfit, hdw, ht, hw, -, h2, h3, -, -, h5⟩ := h
    refine ⟨?_, hw, h2, h3, h5, hheld, hfit, by rw [hw] at hdw; exact hdw⟩
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
  post := by
    intro s s' _ h
    sig_post [Spec.Ed448.scalarBaseContract, Spec.Ed448.scalarBaseSig, Spec.Ed448.scratchWords,
      AArch64.abi, AArch64.argRegs, combConsts_eq, Abi.withConsts]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Ed448.scalarBaseContract, Spec.Ed448.scalarBaseSig, Spec.Ed448.scratchWords,
      AArch64.abi, AArch64.argRegs, combConsts_eq, Abi.withConsts] at h
    obtain ⟨hsp, hsy, h0, h1, h2⟩ := h
    exact ⟨hsp, h0, h1, h2, hsy⟩
  sat := ⟨scalarBaseSat, scalarBase_sat⟩

theorem scalarBase_verified :
    Verified AArch64.target scalarBase (Spec.Ed448.scalarBaseContract (AArch64.abi.withConsts combConsts)) :=
  Verified.of_correct scalarBase_ok scalarBase_ct scalarBase_implies

end VG.Proof.Ed448.AArch64
