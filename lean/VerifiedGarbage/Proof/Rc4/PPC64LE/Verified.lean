module

public import VerifiedGarbage.Proof.Rc4.PPC64LE.Apply
public import VerifiedGarbage.Proof.Rc4.PPC64LE.Init
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Spec.Rc4.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Rc4.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Rc4.PPC64LE.Apply
meta import VerifiedGarbage.Proof.Rc4.PPC64LE.Init
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Spec.Rc4.Contract
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Rc4.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Keep

/-! # RC4 on PPC64LE: verified against the shared contracts -/

@[expose] public section

namespace VG.Proof.Rc4.PPC64LE
open VG VG.PPC64LE VG.Impl.Rc4.PPC64LE VG.Spec.Rc4 VG.Proof.Rc4

/-- The registers the code writes: all volatile. -/
def written : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

/-! ## Initialization -/

/-- The contract the proof of `vg_rc4_init` is written against. -/
def initX : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let ctx : Region := ⟨s.gpr .r5, 258⟩
    s.rd = [key] ∧ s.wr = [ctx] ∧ key.Disjoint ctx
  post s s' :=
    match Spec.Rc4.init (bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat) with
    | .ok c => (s'.gpr .r3).setWidth 32 = 0 ∧ contextAt s'.mem (s.gpr .r5) = c
    | .error .invalidKeyLength => (s'.gpr .r3).setWidth 32 = 1
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧
    s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.sp = s₂.sp

theorem init_correct (s : State) (hs : initX.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initX.post s s' := by
  obtain ⟨hrd, hwr, hkc⟩ := hs
  have hp : InRegions s.wr (s.gpr .r5) 258 :=
    ⟨⟨s.gpr .r5, 258⟩, by rw [hwr]; exact List.mem_cons_self, Region.contains_self _ _⟩
  have hk : InRegions (s.rd ++ s.wr) (s.gpr .r3) (s.gpr .r4).toNat :=
    ⟨⟨s.gpr .r3, (s.gpr .r4).toNat⟩,
      by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _), Region.contains_self _ _⟩
  have hsep : Mem.Sep (s.gpr .r3) (s.gpr .r4).toNat (s.gpr .r5) 256 :=
    fun x hx hy => hkc x (by simp only [Region.Contains]; omega) (by simp only [Region.Contains]; omega)
  obtain ⟨tr, t, he, ⟨hpost, -⟩, hkeep⟩ :=
    WP.keep written (init_ok s hp hk hsep) (by lit_decide) (by lit_decide)
  refine ⟨tr, t, he, abiPreserved_of_keep he hkeep (by decide) (by lit_decide)
    (by rw [← Code.allInstrs_eq]; lit_decide), ?_⟩
  unfold initX
  dsimp only
  revert hpost
  cases Spec.Rc4.init (bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat) with
  | ok c => intro hpost; exact ⟨by rw [hpost.1]; rfl, hpost.2⟩
  | error e => cases e; intro hpost; rw [hpost]; rfl

theorem init_ct : ConstantTime isa initX.pre initX.pub init := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  refine ⟨h.2.2.2, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1

def initSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 1 | .r5 => 0x2000 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 1⟩]
  wr := [⟨0x2000, 258⟩]

theorem init_verified : Verified target init (Spec.Rc4.initContract abi) :=
  Verified.of_correct init_correct init_ct (by
    sig_implies [Spec.Rc4.initContract, Spec.Rc4.initSig, Spec.Rc4.initPost, initX, abi, argRegs]
      [initSat]
      using initSat)

/-! ## The stream function -/

/-- The contract the proof of `vg_rc4_apply` is written against. -/
def applyX : Contract isa where
  pre s :=
    let ctx : Region := ⟨s.gpr .r3, 258⟩
    let data : Region := ⟨s.gpr .r4, (s.gpr .r5).toNat⟩
    s.rd = [] ∧ s.wr = [ctx, data] ∧ ctx.Disjoint data
  post s s' :=
    let result := update (contextAt s.mem (s.gpr .r3))
      (bytesAt s.mem (s.gpr .r4) (s.gpr .r5).toNat)
    contextAt s'.mem (s.gpr .r3) = result.1 ∧
      bytesAt s'.mem (s.gpr .r4) (s.gpr .r5).toNat = result.2
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧
    s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.sp = s₂.sp ∧
    [(s₁.mem (s₁.gpr .r3 + 256)).toNat] = [(s₂.mem (s₂.gpr .r3 + 256)).toNat]

theorem apply_correct (s : State) (hs : applyX.pre s) :
    ∃ t s', Exec isa apply s t s' ∧ abiPreserved s s' ∧ applyX.post s s' := by
  obtain ⟨_, hwr, hcd⟩ := hs
  have hp : InRegions s.wr (s.gpr .r3) 258 :=
    ⟨⟨s.gpr .r3, 258⟩, by rw [hwr]; exact List.mem_cons_self, Region.contains_self _ _⟩
  have hd : InRegions s.wr (s.gpr .r4) (s.gpr .r5).toNat :=
    ⟨⟨s.gpr .r4, (s.gpr .r5).toNat⟩, by rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self,
      Region.contains_self _ _⟩
  have hsep : Mem.Sep (s.gpr .r3) 258 (s.gpr .r4) (s.gpr .r5).toNat :=
    fun x hx hy => hcd x (by simp only [Region.Contains]; omega) (by simp only [Region.Contains]; omega)
  obtain ⟨tr, t, he, ⟨hpost, -⟩, hkeep⟩ :=
    WP.keep written (apply_ok s hp hd hsep) (by lit_decide) (by lit_decide)
  exact ⟨tr, t, he, abiPreserved_of_keep he hkeep (by decide) (by lit_decide)
    (by rw [← Code.allInstrs_eq]; lit_decide), hpost⟩

structure EntryAgree (a b : State) : Prop where
  p : a.gpr .r3 = b.gpr .r3
  data : a.gpr .r4 = b.gpr .r4
  len : a.gpr .r5 = b.gpr .r5
  sp : a.sp = b.sp
  i : (contextAt a.mem (a.gpr .r3)).i = (contextAt b.mem (b.gpr .r3)).i

def ReadValid (s : State) : Prop := InRegions (s.rd ++ s.wr) (s.gpr .r3) 258

def startBlock : List Instr := [.lbz .r6 .r3 256, .lbz .r7 .r3 257, .li .r8 0]

/-- The PRGA index `i` is loaded from the context, where the taint analysis
takes it for secret: it may leak, so it is public. -/
theorem apply_start_ct : RelCT isa (fun a b => ReadValid a ∧ ReadValid b ∧ EntryAgree a b)
    (.block startBlock) fun a b => PPC64LE.Taint.Agree (PPC64LE.Taint.ofRegs [.r3, .r4, .r5, .r6]) a b := by
  intro a b tr tr' a' b' ⟨hpa, hpb, hab⟩ ea eb
  have hct : RelCT isa (fun a b => EntryAgree a b) (.block startBlock) fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.r3, .r4, .r5]) (fun a b h => by
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
  obtain ⟨_, _, _, ha0, ha1, ha2, ha6, _, _⟩ := hau
  obtain ⟨_, _, _, hb0, hb1, hb2, hb6, _, _⟩ := hbv
  refine ⟨htrace, ⟨(Exec.sp eu).trans (hab.sp.trans (Exec.sp ev).symm), fun r hr => ?_⟩⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ha0.trans (hab.p.trans hb0.symm)
  · exact ha1.trans (hab.data.trans hb1.symm)
  · exact ha2.trans (hab.len.trans hb2.symm)
  · rw [ha6, hb6, hab.i]

theorem apply_ct : ConstantTime isa ReadValid EntryAgree apply := by
  apply RelCT.constantTime (Q := fun _ _ => True)
  unfold apply
  refine RelCT.seq apply_start_ct (RelCT.ite ?_ ?_ ?_)
  · intro a b h
    simp only [eval, State.read, h.2 .r5 (by simp [PPC64LE.Taint.mem_ofRegs])]
  · exact RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ h => ⟨h.1.1, by simp⟩)
      (by taint_decide)
  · exact RelCT.taint (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6]) (fun _ _ h => h.1)
      (by taint_decide)

theorem apply_ct' : ConstantTime isa applyX.pre applyX.pub apply := by
  intro s₁ s₂ tr₁ tr₂ t₁ t₂ h₁ h₂ hp e₁ e₂
  have hv (s : State) (h : applyX.pre s) : ReadValid s :=
    ⟨⟨s.gpr .r3, 258⟩, List.mem_append_right _ (by rw [h.2.1]; exact List.mem_cons_self),
      Region.contains_self _ _⟩
  exact apply_ct s₁ s₂ tr₁ tr₂ t₁ t₂ (hv s₁ h₁) (hv s₂ h₂)
    ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, BitVec.eq_of_toNat_eq (List.cons.inj hp.2.2.2.2).1⟩ e₁ e₂

def applySat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 1 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 258⟩, ⟨0x2000, 1⟩]

theorem apply_verified : Verified target apply (Spec.Rc4.applyContract abi) :=
  Verified.of_correct apply_correct apply_ct' (by
    sig_implies [Spec.Rc4.applyContract, Spec.Rc4.applySig, Spec.Rc4.applyPost, Spec.Rc4.applyLeak,
      applyX, abi, argRegs] [applySat]
      using applySat)

end VG.Proof.Rc4.PPC64LE
