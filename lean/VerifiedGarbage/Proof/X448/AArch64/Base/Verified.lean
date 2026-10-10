import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.X448.AArch64.Base.Main
import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
import VerifiedGarbage.Proof.X448.AArch64.Base.Erase
import VerifiedGarbage.Proof.Framework.Contract

/-!
# X448 of the base point on AArch64: `Verified`

Untrusted: everything here is checked by Lean. Constant time (by taint
tracking: the only branches are on the counters, every address is an argument
or the static's address plus a constant or a counter, and the digits' masks
only select), and the shared contract of `Spec/`, under the calling convention
with the comb's tables (`Abi.withConsts combConsts`).
-/

namespace VG.Proof.X448.AArch64.Base

open VG VG.AArch64 VG.Impl.X448.AArch64.Base

/-- The analysis, of the code without what it does not read, its comb's field operations analysed
once each (`Base/Erase.lean`). -/
theorem x448Base_check :
    ∃ h, ((taintS [combSym]).check (Taint.ofRegs [.x0, .x1, .x2]) Impl.X448.AArch64.Base.x448Base h).isSome =
      true := by
  apply exists_isSome_of_eraseT
  refine Split.exists_isSome (c' := ?c') ?s ⟨?h, ?g⟩
  case s =>
    simp only [x448Base, step, finish, Code.eraseT, Impl.X448.AArch64.Fast.invert, ops_eraseT, sqn_eraseT]
    exact .seq (.refl _) (.seq (.loop _ (stepN_split 56)) (.seq (.refl _) (.refl _)))
  case g => taint_decide

theorem x448Base_ct : ConstantTime isa Proof.X448.x448BaseAArch64.pre Proof.X448.x448BaseAArch64.pub
    Impl.X448.AArch64.Base.x448Base :=
  let ⟨_, hc⟩ := x448Base_check
  VG.Taint.constantTime (A := taintS [combSym]) (Taint.ofRegs [.x0, .x1, .x2])
    (fun _ _ _ _ ⟨h0, h1, h2, hsp, hsy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2⟩, fun n hn => by
      simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩) hc

/-- A state satisfying the precondition: the tables at `0x100000`. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x4000 | _ => 0
  sp := 0x8000
  mem := satMem
  rd := [⟨0x2000, 56⟩, ⟨0x100000, 58368⟩]
  wr := [⟨0x1000, 56⟩, ⟨0x4000, 8192⟩]
  syms _ := 0x100000

/-- The shared contract's precondition, from its facts. -/
theorem spec_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .x1, 56⟩, ⟨s.syms combSym, 8 * combWords.length⟩])
    (hw : s.wr = [⟨s.gpr .x0, 56⟩, ⟨s.gpr .x2, 8192⟩])
    (h1 : Region.Disjoint ⟨s.gpr .x0, 56⟩ ⟨s.gpr .x1, 56⟩)
    (h2 : Region.Disjoint ⟨s.gpr .x0, 56⟩ ⟨s.gpr .x2, 8192⟩)
    (h3 : Region.Disjoint ⟨s.gpr .x1, 56⟩ ⟨s.gpr .x2, 8192⟩)
    (f0 : (s.gpr .x0).toNat + 56 ≤ 2 ^ 64) (f1 : (s.gpr .x1).toNat + 56 ≤ 2 ^ 64)
    (f2 : (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64)
    (ht : CombHeld s [⟨s.gpr .x0, 56⟩, ⟨s.gpr .x2, 8192⟩]) :
    (Spec.X448.x448BaseContract (AArch64.abi.withConsts combConsts)).pre s := by
  sig_pre [Spec.X448.x448BaseContract, Spec.X448.x448BaseSig, AArch64.abi, AArch64.argRegs,
    combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨by rw [hrd]; rfl, held, fit, by rw [hw]; exact hdw, by rw [hrd]; rfl, hw, h1, h2, h3, f0, f1, f2⟩

theorem sat_spec : (Spec.X448.x448BaseContract (AArch64.abi.withConsts combConsts)).pre satState := by
  have hl := combWords_length
  have held : ∀ i < combWords.length, satState.mem.readW (satState.syms combSym +
      BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0 := satMem_held
  refine spec_pre (by rw [hl]; rfl) rfl (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide)) (by decide) (by decide)
    (by decide) ⟨held, ?_, ?_⟩
  all_goals rw [hl]
  · decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)

theorem implies : Proof.X448.x448BaseAArch64.Implies
    (Spec.X448.x448BaseContract (AArch64.abi.withConsts combConsts)) where
  pre s h := by
    sig_pre [Spec.X448.x448BaseContract, Spec.X448.x448BaseSig, AArch64.abi, AArch64.argRegs,
      combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
    obtain ⟨hd, hheld, hfit, hdw, ht, hw, -, h2, h3, -, -, h5⟩ := h
    refine ⟨?_, hw, h2, h3, h5, hheld, hfit, by rw [hw] at hdw; exact hdw⟩
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
  post := by
    intro s s' _ h
    sig_post [Spec.X448.x448BaseContract, Spec.X448.x448BaseSig, AArch64.abi, AArch64.argRegs,
      combConsts_eq, Abi.withConsts]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.X448.x448BaseContract, Spec.X448.x448BaseSig, AArch64.abi, AArch64.argRegs,
      combConsts_eq, Abi.withConsts] at h
    obtain ⟨hsp, hsy, h0, h1, h2⟩ := h
    exact ⟨h0, h1, h2, hsp, hsy⟩
  sat := ⟨satState, sat_spec⟩

theorem x448Base_ok (s : State) (hs : Proof.X448.x448BaseAArch64.pre s) :
    ∃ t s', Exec isa Impl.X448.AArch64.Base.x448Base s t s' ∧ abiPreserved s s' ∧
      Proof.X448.x448BaseAArch64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct (Pre.of s hs)
  exact ⟨t, s', he, ⟨h.1, Exec.sp he, h.2.1⟩, h.2.2⟩

theorem x448Base_verified :
    Verified AArch64.target Impl.X448.AArch64.Base.x448Base
      (Spec.X448.x448BaseContract (AArch64.abi.withConsts combConsts)) :=
  Verified.of_correct x448Base_ok x448Base_ct implies

end VG.Proof.X448.AArch64.Base
