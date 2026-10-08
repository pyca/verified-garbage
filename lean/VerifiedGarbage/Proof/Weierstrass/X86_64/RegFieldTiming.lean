import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldTiming
import VerifiedGarbage.Proof.Framework.X86_64.KeepReg

/-! Public control registers alongside paired field environments. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.X25519.X86_64 (Keeps)

abbrev RegCT (rs : List Reg) (c : Prog isa) : Prop :=
  ConstantTime isa (fun _ => True) (X86_64.Taint.Agree (Taint.ofRegs rs)) c

theorem instrs_noClobber {c : Prog isa} {r : Reg}
    (h : c.allInstrs (fun i => !Taint.clobbers i r)=true) :
    ∀ i∈instrs c, Taint.clobbers i r=false := by
  rw [Code.allInstrs_eq,List.all_eq_true] at h
  intro i hi
  simpa using h i hi

theorem regFieldProgram_relCT {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} {V W : List Nat} {E F : Nat → Fin m} {c : Prog isa}
    {Pre Post : State → Prop} {rs : List Reg} (hc : RegCT rs c)
    (hp : ∀ s t, FieldPair M base size m Sl V E s t → Pre s → Pre t →
      X86_64.Taint.Agree (Taint.ofRegs rs) s t)
    (hw : ∀ s, Inv M base size m Sl V E s → Pre s →
      WP isa c s (fun t => Inv M base size m Sl W F t ∧ Post t)) :
    RelCT isa (fun s t => FieldPair M base size m Sl V E s t ∧ Pre s ∧ Pre t) c
      (fun s t => FieldPair M base size m Sl W F s t ∧ Post s ∧ Post t) := by
  have hct : RelCT isa (fun s t => FieldPair M base size m Sl V E s t ∧ Pre s ∧ Pre t) c
      (fun _ _ => True) := fun s t _ _ _ _ h es et =>
    ⟨hc _ _ _ _ _ _ trivial trivial (hp s t h.1 h.2.1 h.2.2) es et,trivial⟩
  exact (hct.wp (fun s t h => ⟨hw s h.1.1 h.2.1,hw t h.1.2 h.2.2⟩)).mono
    (fun _ _ h => h) (fun _ _ ⟨_,⟨is,ps⟩,⟨it,pt⟩⟩ => ⟨⟨is,it⟩,ps,pt⟩)

theorem keepsField_relCT {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fin m} {c : Prog isa}
    {Pre Post : State → Prop} {rs ws : List Reg} (hr : Reg.rdi∉ws)
    (hc : RegCT rs c)
    (hp : ∀ s t, FieldPair M base size m Sl V E s t → Pre s → Pre t →
      X86_64.Taint.Agree (Taint.ofRegs rs) s t)
    (hw : ∀ s, Inv M base size m Sl V E s → Pre s →
      WP isa c s (fun t => Post t ∧ Keeps ws s t)) :
    RelCT isa (fun s t => FieldPair M base size m Sl V E s t ∧ Pre s ∧ Pre t) c
      (fun s t => FieldPair M base size m Sl V E s t ∧ Post s ∧ Post t) :=
  regFieldProgram_relCT hc hp (fun s hi pre => WP.mono (hw s hi pre)
    (fun _ ⟨post,hk⟩ => ⟨hi.of_keeps hk hr,post⟩))

theorem relCT_keepGpr {P Q : State → State → Prop} {c : Prog isa} {r : Reg} {v : BitVec 64}
    (h : RelCT isa P c Q) (hk : ∀ i∈instrs c, Taint.clobbers i r=false) :
    RelCT isa (fun s t => P s t ∧ s.gpr r=v ∧ t.gpr r=v) c
      (fun s t => Q s t ∧ s.gpr r=v ∧ t.gpr r=v) := by
  intro s t ts tt s' t' ⟨hp,hs,ht⟩ es et
  obtain ⟨tr,hq⟩ := h _ _ _ _ _ _ hp es et
  exact ⟨tr,hq,(Exec.gpr hk es).trans hs,(Exec.gpr hk et).trans ht⟩

/-- `relCT_keepGpr`, for a register the code may write if it restores it
from an SSE register that holds it (`KeepReg.keeps`). -/
theorem relCT_keepGprS {P Q : State → State → Prop} {c : Prog isa} {r : Reg} {v : BitVec 64}
    (h : RelCT isa P c Q) (hk : KeepReg.keeps r c = true) :
    RelCT isa (fun s t => P s t ∧ s.gpr r=v ∧ t.gpr r=v) c
      (fun s t => Q s t ∧ s.gpr r=v ∧ t.gpr r=v) := by
  intro s t ts tt s' t' ⟨hp,hs,ht⟩ es et
  obtain ⟨tr,hq⟩ := h _ _ _ _ _ _ hp es et
  exact ⟨tr,hq,(Exec.gpr_keeps hk es).trans hs,(Exec.gpr_keeps hk et).trans ht⟩

end VG.Proof.Weierstrass.X86_64
