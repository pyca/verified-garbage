import VerifiedGarbage.Proof.Cast5.AArch64.Key
import VerifiedGarbage.Proof.Cast5.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
import VerifiedGarbage.Spec.Cast5.Contract
import VerifiedGarbage.TCB.AArch64.Target

/-!
# CAST5 key expansion on AArch64: verified against the shared contract
-/

namespace VG.Proof.Cast5.AArch64

open VG VG.AArch64 VG.Impl.Cast5 VG.Impl.Cast5.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The contract the proof of key expansion is written against. -/
def keyX : Contract isa where
  pre s := KPre s
  post s s' :=
    Spec.Cast5.scheduleAt s'.mem (s.gpr .x2) =
      Spec.Cast5.expandKey (Spec.Cast5.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp ∧ s₁.syms s5678Sym = s₂.syms s5678Sym

/-- The registers key expansion writes. -/
def keyAll : List Reg := [.x0, .x1, .x2, .x4, .x9, .x10, .x11]

theorem preserved_keyAll : ∀ r ∈ preserved, r ∉ keyAll := by decide

theorem key_correct (s : State) (h : keyX.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ keyX.post s s' := by
  obtain ⟨t, s', he, hpost, hk⟩ := WP.keep keyAll (expandKey_ok s h) (by lit_decide) (by lit_decide)
    (by lit_decide)
  exact ⟨t, s', he, ⟨fun r hr => hk.gpr r (preserved_keyAll r hr), hk.sp, hk.vcs⟩, hpost⟩

/-- The public registers. -/
def keyPub : List Reg := [.x0, .x1, .x2, .x3]

theorem key_agree (s₁ s₂ : State) (_ : keyX.pre s₁) (_ : keyX.pre s₂) (h : keyX.pub s₁ s₂) :
    VG.AArch64.Taint.AgreeS [s5678Sym] (Taint.ofRegs keyPub) s₁ s₂ := by
  obtain ⟨h1, h2, h3, h4, hsp, hsy⟩ := h
  refine ⟨⟨hsp, fun r hr => ?_⟩, fun n hn => ?_⟩
  · have hr := Taint.mem_ofRegs.mp hr
    simp only [keyPub, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  · simp only [List.mem_singleton] at hn
    subst hn
    exact hsy

theorem expandKey_ct : ConstantTime isa keyX.pre keyX.pub expandKey :=
  VG.Taint.constantTime (A := taintS [s5678Sym]) (Taint.ofRegs keyPub) key_agree (by taint_decide)

theorem keyConsts_eq : keyConsts = [(s5678Sym, s5678)] := rfl
theorem s5678_length : s5678.length = 512 := table_length _ _ _ _

/-- The memory of the contract's witness: the table at `0x100000` (irreducible:
unfolding it in a definitional check would evaluate the table). -/
@[irreducible] def keySatMem : Mem := constMem 0x100000 s5678

theorem keySatMem_held : ∀ i < 512,
    keySatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = s5678.getD i 0 := by
  unfold keySatMem
  intro i hi
  exact constMem_held _ _ (by rw [s5678_length]; decide) i (by rw [s5678_length]; exact hi)

/-- A state satisfying key expansion's precondition: a 16-byte key. -/
def keySat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 16 | .x2 => 0x2000 | .x3 => 0x3000 | _ => 0
  sp := 0x8000
  mem := keySatMem
  rd := [⟨0x1000, 16⟩, ⟨0x100000, 4096⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 256⟩]
  syms _ := 0x100000

/-- The shared contract's precondition, from its facts. -/
theorem KPre.spec_pre {s : State} (h : KPre s) :
    (Spec.Cast5.expandKeyContract (AArch64.abi.withConsts keyConsts)).pre s := by
  sig_pre [Spec.Cast5.expandKeyContract, Spec.Cast5.expandKeySig, Spec.Cast5.expandKeyPre, AArch64.abi,
    AArch64.argRegs, keyConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow, s5678_length]
  refine ⟨by rw [h.rd]; rfl, h.held, h.fitT, fun r hr => ?_, by rw [h.rd]; rfl, h.wr, h.dkK, h.dkS,
    h.dKS, h.fk, h.fK, h.fS, h.len⟩
  rw [h.wr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.dTK
  · exact h.dTS

theorem key_implies : keyX.Implies (Spec.Cast5.expandKeyContract (AArch64.abi.withConsts keyConsts)) where
  pre s h := by
    sig_pre [Spec.Cast5.expandKeyContract, Spec.Cast5.expandKeySig, Spec.Cast5.expandKeyPre, AArch64.abi,
      AArch64.argRegs, keyConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow,
      s5678_length] at h
    obtain ⟨hdr, hheld, hfit, hdw, htk, hw, dkK, dkS, dKS, fk, fK, fS, hl⟩ := h
    refine ⟨?_, hw, hheld, hfit, hdw _ (by rw [hw]; exact List.mem_cons_self),
      hdw _ (by rw [hw]; exact List.mem_cons_of_mem _ List.mem_cons_self), dkK, dkS, dKS, fk, fK, fS, hl⟩
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, htk, hdr]
    rfl
  post s s' _ h := by
    sig_post [Spec.Cast5.expandKeyContract, Spec.Cast5.expandKeySig, Spec.Cast5.expandKeyPost, AArch64.abi,
      AArch64.argRegs, keyConsts_eq, Abi.withConsts]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Cast5.expandKeyContract, Spec.Cast5.expandKeySig, AArch64.abi, AArch64.argRegs, keyConsts_eq,
      Abi.withConsts] at h
    obtain ⟨hsp, hsy, h1, h2, h3, h4⟩ := h
    exact ⟨h1, h2, h3, h4, hsp, hsy⟩
  sat := ⟨keySat, KPre.spec_pre ⟨rfl, rfl, keySatMem_held, by decide, Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), by decide, by decide, by decide, by decide⟩⟩

theorem expandKey_verified :
    Verified AArch64.target expandKey (Spec.Cast5.expandKeyContract (AArch64.abi.withConsts keyConsts)) :=
  Verified.of_correct key_correct expandKey_ct key_implies

end VG.Proof.Cast5.AArch64
