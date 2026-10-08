import VerifiedGarbage.Proof.Cast5.X86_64.Key
import VerifiedGarbage.Proof.Cast5.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.X86_64.TaintSym
import VerifiedGarbage.Spec.Cast5.Contract
import VerifiedGarbage.TCB.X86_64.Target

/-!
# CAST5 key expansion on x86-64: verified against the shared contract
-/

namespace VG.Proof.Cast5.X86_64

open VG VG.X86_64 VG.Impl.Cast5.X86_64
open VG.Proof.MlKem.X86_64 (gprPreserved_of)

/-- The contract the proof of key expansion is written against. -/
def keyX : Contract isa where
  pre s := KPre s
  post s s' :=
    Spec.Cast5.scheduleAt s'.mem (s.gpr .rdx) =
      Spec.Cast5.expandKey (Spec.Cast5.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.syms s5678Sym = s₂.syms s5678Sym

theorem key_correct (s : State) (h : keyX.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ keyX.post s s' := by
  obtain ⟨t, s', he, hpost, hk, hf⟩ := expandKey_ok s h
  refine ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he (gprPreserved_of hk (by decide) hf ?_), hpost⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.dspK
  · exact h.dspS

/-- The public registers. -/
def keyPub : List Reg := [.rdi, .rsi, .rdx, .rcx]

theorem key_agree (s₁ s₂ : State) (_ : keyX.pre s₁) (_ : keyX.pre s₂) (h : keyX.pub s₁ s₂) :
    VG.X86_64.Taint.AgreeS [s5678Sym] (Taint.ofRegs keyPub) s₁ s₂ := by
  obtain ⟨h1, h2, h3, h4, hsy⟩ := h
  refine ⟨Taint.agree_ofRegs fun r hr => ?_, fun n hn => ?_⟩
  · simp only [keyPub, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  · simp only [List.mem_singleton] at hn
    subst hn
    exact hsy

theorem expandKey_ct : ConstantTime isa keyX.pre keyX.pub expandKey :=
  VG.Taint.constantTime (A := taintSym [s5678Sym]) (Taint.ofRegs keyPub) key_agree (by taint_decide)

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
    | .rdi => 0x1000 | .rsi => 16 | .rdx => 0x2000 | .rcx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := keySatMem
  rd := [⟨0x1000, 16⟩, ⟨0x100000, 4096⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 256⟩]
  syms _ := 0x100000

/-- The shared contract's precondition, from its facts. -/
theorem KPre.spec_pre {s : State} (h : KPre s)
    (dTsp : Region.Disjoint ⟨s.syms s5678Sym, 4096⟩ ⟨s.gpr .rsp, 8⟩) :
    (Spec.Cast5.expandKeyContract (X86_64.abi.withConsts keyConsts)).pre s := by
  sig_pre [Spec.Cast5.expandKeyContract, Spec.Cast5.expandKeySig, Spec.Cast5.expandKeyPre, X86_64.abi,
    X86_64.argRegs, keyConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow, s5678_length]
  refine ⟨by rw [h.rd]; rfl, h.held, h.fitT, fun r hr => ?_, dTsp, by rw [h.rd]; rfl, h.wr, h.dkK, h.dkS,
    h.dKS, h.dspk, h.dspK, h.dspS, h.fk, h.fK, h.fS, h.len⟩
  rw [h.wr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.dTK
  · exact h.dTS

theorem key_implies : keyX.Implies (Spec.Cast5.expandKeyContract (X86_64.abi.withConsts keyConsts)) where
  pre s h := by
    sig_pre [Spec.Cast5.expandKeyContract, Spec.Cast5.expandKeySig, Spec.Cast5.expandKeyPre, X86_64.abi,
      X86_64.argRegs, keyConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow,
      s5678_length] at h
    obtain ⟨hdr, hheld, hfit, hdw, -, htk, hw, dkK, dkS, dKS, dspk, dspK, dspS, fk, fK, fS, hl⟩ := h
    refine ⟨?_, hw, hheld, hfit, hdw _ (by rw [hw]; exact List.mem_cons_self),
      hdw _ (by rw [hw]; exact List.mem_cons_of_mem _ List.mem_cons_self), dkK, dkS, dKS, dspk, dspK, dspS,
      fk, fK, fS, hl⟩
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, htk, hdr]
    rfl
  post s s' _ h := by
    sig_post [Spec.Cast5.expandKeyContract, Spec.Cast5.expandKeySig, Spec.Cast5.expandKeyPost, X86_64.abi,
      X86_64.argRegs, keyConsts_eq, Abi.withConsts]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Cast5.expandKeyContract, Spec.Cast5.expandKeySig, X86_64.abi, X86_64.argRegs, keyConsts_eq,
      Abi.withConsts] at h
    obtain ⟨-, hsy, h1, h2, h3, h4⟩ := h
    exact ⟨h1, h2, h3, h4, hsy⟩
  sat := ⟨keySat, KPre.spec_pre ⟨rfl, rfl, keySatMem_held, by decide, Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), by decide, by decide, by decide, by decide⟩
    (Region.disjoint_of_sep (by decide))⟩

theorem expandKey_verified :
    Verified X86_64.target expandKey (Spec.Cast5.expandKeyContract (X86_64.abi.withConsts keyConsts)) :=
  Verified.of_correct key_correct expandKey_ct key_implies

end VG.Proof.Cast5.X86_64
