module

import VerifiedGarbage.Proof.Rc4.RISCV64.Apply
meta import VerifiedGarbage.Proof.Rc4.RISCV64.Apply
import VerifiedGarbage.Proof.Rc4.RISCV64.Init
meta import VerifiedGarbage.Proof.Rc4.RISCV64.Init
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Spec.Rc4.Contract
meta import VerifiedGarbage.Spec.Rc4.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Rc4.RISCV64.Lit
meta import VerifiedGarbage.Proof.Rc4.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rc4.Stream
meta import VerifiedGarbage.Proof.Rc4.Stream
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
meta import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Impl.Rc4.RISCV64
meta import VerifiedGarbage.Impl.Rc4.RISCV64
public import VerifiedGarbage.Proof.Rc4.RISCV64.Lookup
meta import VerifiedGarbage.Proof.Rc4.RISCV64.Lookup
public import VerifiedGarbage.Spec.Rc4
meta import VerifiedGarbage.Spec.Rc4
public import VerifiedGarbage.TCB.Artifact
meta import VerifiedGarbage.TCB.Artifact

/-!
# RC4 on RISC-V: verified against the shared contracts

The proofs are written against per-target contracts (`initX`, `applyX`),
which state the frame of 256 bytes below the stack pointer, and moved to the
shared contracts of `Spec/Rc4/Contract.lean` with `stack := 256`. The code
writes only temporaries and argument registers.
-/

@[expose] public section

namespace VG.Proof.Rc4.RISCV64
open VG VG.RISCV64 VG.Impl.Rc4.RISCV64 VG.Spec.Rc4 VG.Proof.Rc4

/-- The registers the code writes: no preserved register, nor `ra`. -/
def written : List Reg := [.t0, .t1, .t2, .t3, .t4, .t6, .a0, .a1, .a2, .a3, .a4, .a5, .a7]

/-- `Region.Disjoint` as `Mem.Sep`. -/
theorem sep_of_disjoint {r₁ r₂ : Region} (h : r₁.Disjoint r₂) : Mem.Sep r₁.base r₁.len r₂.base r₂.len :=
  fun x hx hy => h x (by simp only [Region.Contains]; omega) (by simp only [Region.Contains]; omega)

/-! ## Initialization -/

/-- The contract the proof of `vg_rc4_init` is written against. -/
def initX : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
    let ctx : Region := ⟨s.gpr .a2, 258⟩
    let stack : Region := ⟨s.sp - 256, 256⟩
    s.rd = [key] ∧ s.wr = [ctx] ∧ key.Disjoint ctx ∧
    s.sp.toNat % 16 = 0 ∧ 256 ≤ s.sp.toNat ∧ stack.Disjoint key ∧ stack.Disjoint ctx
  post s s' :=
    match Spec.Rc4.init (bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) with
    | .ok c => (s'.gpr .a0).setWidth 32 = 0 ∧ contextAt s'.mem (s.gpr .a2) = c
    | .error .invalidKeyLength => (s'.gpr .a0).setWidth 32 = 1
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.sp = s₂.sp

theorem init_correct (s : State) (hs : initX.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initX.post s s' := by
  obtain ⟨hrd, hwr, _, hal, hsp, hsk, hsc⟩ := hs
  have hp : InRegions s.wr (s.gpr .a2) 258 :=
    ⟨⟨s.gpr .a2, 258⟩, by rw [hwr]; exact List.mem_cons_self, Region.contains_self _ _⟩
  have hk : InRegions (s.rd ++ s.wr) (s.gpr .a0) (s.gpr .a1).toNat :=
    ⟨⟨s.gpr .a0, (s.gpr .a1).toNat⟩,
      by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _), Region.contains_self _ _⟩
  obtain ⟨tr, t, he, hpost, hkeep⟩ :=
    WP.keep written (init_ok s hal hsp hp hk (sep_symm (sep_of_disjoint hsk))
      (sep_of_disjoint hsc)) (by lit_decide) (by lit_decide)
  refine ⟨tr, t, he, abiPreserved_of_keep he hkeep (by decide) (by decide), ?_⟩
  unfold initX
  dsimp only
  revert hpost
  cases Spec.Rc4.init (bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) with
  | ok c => intro hpost; exact ⟨by rw [hpost.1]; rfl, hpost.2⟩
  | error e => cases e; intro hpost; rw [hpost]; rfl

theorem init_ct : ConstantTime isa initX.pre initX.pub init := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  refine ⟨h.2.2.2, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1

def initSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 1 | .a2 => 0x2000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 1⟩]
  wr := [⟨0x2000, 258⟩]

theorem init_verified : Verified RISCV64.target init (Spec.Rc4.initContract RISCV64.abi 256) :=
  Verified.of_correct init_correct init_ct (by
    sig_implies [Spec.Rc4.initContract, Spec.Rc4.initSig, Spec.Rc4.initPost, initX, RISCV64.abi,
      RISCV64.argRegs] [initSat]
      using initSat)

/-! ## The stream function -/

/-- The contract the proof of `vg_rc4_apply` is written against. -/
def applyX : Contract isa where
  pre s :=
    let ctx : Region := ⟨s.gpr .a0, 258⟩
    let data : Region := ⟨s.gpr .a1, (s.gpr .a2).toNat⟩
    let stack : Region := ⟨s.sp - 256, 256⟩
    s.rd = [] ∧ s.wr = [ctx, data] ∧ ctx.Disjoint data ∧
    s.sp.toNat % 16 = 0 ∧ 256 ≤ s.sp.toNat ∧ stack.Disjoint ctx ∧ stack.Disjoint data
  post s s' :=
    let result := update (contextAt s.mem (s.gpr .a0))
      (bytesAt s.mem (s.gpr .a1) (s.gpr .a2).toNat)
    contextAt s'.mem (s.gpr .a0) = result.1 ∧
      bytesAt s'.mem (s.gpr .a1) (s.gpr .a2).toNat = result.2
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.sp = s₂.sp ∧
    [(s₁.mem (s₁.gpr .a0 + 256)).toNat] = [(s₂.mem (s₂.gpr .a0 + 256)).toNat]

theorem apply_correct (s : State) (hs : applyX.pre s) :
    ∃ t s', Exec isa apply s t s' ∧ abiPreserved s s' ∧ applyX.post s s' := by
  obtain ⟨_, hwr, hcd, hal, hsp, hsc, hsd⟩ := hs
  have hp : InRegions s.wr (s.gpr .a0) 258 :=
    ⟨⟨s.gpr .a0, 258⟩, by rw [hwr]; exact List.mem_cons_self, Region.contains_self _ _⟩
  have hd : InRegions s.wr (s.gpr .a1) (s.gpr .a2).toNat :=
    ⟨⟨s.gpr .a1, (s.gpr .a2).toNat⟩, by rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self,
      Region.contains_self _ _⟩
  obtain ⟨tr, t, he, hpost, hkeep⟩ :=
    WP.keep written (apply_ok s hal hsp hp hd (sep_of_disjoint hcd) (sep_of_disjoint hsc)
      (sep_of_disjoint hsd)) (by lit_decide) (by lit_decide)
  exact ⟨tr, t, he, abiPreserved_of_keep he hkeep (by decide) (by decide), hpost⟩

structure EntryAgree (a b : State) : Prop where
  p : a.gpr .a0 = b.gpr .a0
  data : a.gpr .a1 = b.gpr .a1
  len : a.gpr .a2 = b.gpr .a2
  sp : a.sp = b.sp
  i : a.mem (a.gpr .a0 + 256#64) = b.mem (b.gpr .a0 + 256#64)

def ReadValid (s : State) : Prop := InRegions (s.rd ++ s.wr) (s.gpr .a0) 258

def startBlock : List Instr := [.load .b .a3 .a0 256, .load .b .t4 .a0 257, .li .t6 0]

/-- The PRGA index `i` is loaded from the context, where the taint analysis
takes it for secret: it may leak, so it is public. -/
theorem apply_start_ct : RelCT isa (fun a b => ReadValid a ∧ ReadValid b ∧ EntryAgree a b)
    (.block startBlock) fun a b => RISCV64.Taint.Agree (Taint.ofRegs [.a0, .a1, .a2, .a3]) a b := by
  intro a b tr tr' a' b' ⟨hpa, hpb, hab⟩ ea eb
  have hct : RelCT isa (fun a b => EntryAgree a b) (.block startBlock) fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a2]) (fun a b h => by
      refine ⟨h.sp, fun r hr => ?_⟩
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.p
      · exact h.data
      · exact h.len) (by taint_decide)
  obtain ⟨htrace, -⟩ := hct a b tr tr' a' b' hab ea eb
  obtain ⟨_, u, eu, hau⟩ := apply_start a hpa
  obtain ⟨_, rfl⟩ := Exec.det eu ea
  obtain ⟨_, v, ev, hbv⟩ := apply_start b hpb
  obtain ⟨_, rfl⟩ := Exec.det ev eb
  obtain ⟨_, _, _, _, ha0, ha1, ha2, ha3, _, _⟩ := hau
  obtain ⟨_, _, _, _, hb0, hb1, hb2, hb3, _, _⟩ := hbv
  refine ⟨htrace, ⟨(Exec.sp eu).trans (hab.sp.trans (Exec.sp ev).symm), fun r hr => ?_⟩⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ha0.trans (hab.p.trans hb0.symm)
  · exact ha1.trans (hab.data.trans hb1.symm)
  · exact ha2.trans (hab.len.trans hb2.symm)
  · rw [ha3, hb3, hab.i]

theorem apply_ct : ConstantTime isa ReadValid EntryAgree apply := by
  apply RelCT.constantTime (Q := fun _ _ => True)
  unfold apply
  refine RelCT.seq apply_start_ct (RelCT.ite ?_ ?_ ?_)
  · intro a b h
    rw [Steps.eval_zero, Steps.eval_zero, h.2 .a2 (by simp [Taint.mem_ofRegs])]
  · exact RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ h => ⟨h.1.1, by simp⟩)
      (by taint_decide)
  · exact RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3]) (fun _ _ h => h.1)
      (by taint_decide)

theorem apply_ct' : ConstantTime isa applyX.pre applyX.pub apply := by
  intro s₁ s₂ tr₁ tr₂ t₁ t₂ h₁ h₂ hp e₁ e₂
  have hv (s : State) (h : applyX.pre s) : ReadValid s :=
    ⟨⟨s.gpr .a0, 258⟩, List.mem_append_right _ (by rw [h.2.1]; exact List.mem_cons_self),
      Region.contains_self _ _⟩
  exact apply_ct s₁ s₂ tr₁ tr₂ t₁ t₂ (hv s₁ h₁) (hv s₂ h₂)
    ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, BitVec.eq_of_toNat_eq (List.cons.inj hp.2.2.2.2).1⟩ e₁ e₂

def applySat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 1 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 258⟩, ⟨0x2000, 1⟩]

theorem apply_verified : Verified RISCV64.target apply (Spec.Rc4.applyContract RISCV64.abi 256) :=
  Verified.of_correct apply_correct apply_ct' (by
    sig_implies [Spec.Rc4.applyContract, Spec.Rc4.applySig, Spec.Rc4.applyPost, Spec.Rc4.applyLeak,
      applyX, RISCV64.abi, RISCV64.argRegs] [applySat]
      using applySat)

end VG.Proof.Rc4.RISCV64
