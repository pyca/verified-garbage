import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Domain
import VerifiedGarbage.Proof.Weierstrass.Unch

namespace VG.Proof.Weierstrass.AArch64.Forward
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

variable {α : Type} {D : Dom α} {v : α → BitVec 64 × Bool}
  {base : Addr} {size cap : Nat} {e : Env α} {s : State}

theorem arg_sound (h : Rel v base size e s) {use : Bool} {r : Reg} {a : α}
    (ha : arg D e use r=some a) (hu : use=true) : (v a).1=s.gpr r := by
  rw [arg,hu] at ha
  exact h.reg r a ha

theorem scalar_step (hD : D.Sound v) (hs : Scr s base cap) (he : Rel v base size e s)
    {op : Op} (hv : op.valid=true) {d a b c : Reg} (hd : d≠.x0)
    {va vb vc vd cf vr : α}
    (ha : arg D e op.useA a=some va) (hb : arg D e op.useB b=some vb)
    (hc : arg D e op.useC c=some vc) (hh : arg D e op.useD d=some vd)
    (hf : (if op.useCarry then e.carry else some D.zero)=some cf)
    (hr : D.applyOp op va vb vc vd cf=some vr) :
    ∃ t,exec (op.instr d a b c) s=some t ∧
      Rel v base size {e.setReg d vr with carry:=if op.flags then some vr else e.carry} t ∧
      Scr t base cap ∧ KeepRegs [d] s t ∧ Unch base [] s.mem t.mem := by
  obtain ⟨t,ht,td,tc,tg,tm,tr,tw,tsp,_⟩ := scalar_run op hv s d a b c
  have ve : op.eval (v va).1 (v vb).1 (v vc).1 (v vd).1 (v cf).2=
      op.eval (s.gpr a) (s.gpr b) (s.gpr c) (s.gpr d) s.c := op.eval_congr (arg_sound he ha) (arg_sound he hb) (arg_sound he hc) (arg_sound he hh)
    (by intro hu; rw [hu] at hf; exact he.carry cf hf)
  obtain ⟨vrw,vrc⟩ := hD.applyOp op va vb vc vd cf vr hr
  rw [ve] at vrw vrc
  have kr : KeepRegs [d] s t := ⟨fun r hn => tg r (by simpa only [List.mem_singleton] using hn),tr,tw,tsp⟩
  refine ⟨t,ht,⟨?_,?_,?_⟩,hs.of_keepRegs kr (by simpa only [List.mem_singleton,ne_eq,eq_comm] using hd),kr,?_⟩
  · intro r z hz
    change (if r=d then some vr else e.reg r)=some z at hz
    split at hz
    · rename_i eq; subst eq
      cases hz
      exact vrw.trans td.symm
    · rename_i ne
      exact (he.reg r z hz).trans (tg r ne).symm
  · intro off ho hb
    change (v (e.slot off)).1=_
    rw [tm]; exact he.slot off ho hb
  · intro z hz
    change (if op.flags then some vr else e.carry)=some z at hz
    split at hz
    · rename_i flag
      cases hz
      rw [tc,flag]
      exact vrc flag
    · rename_i flag
      rw [tc,ite_eq_right flag]
      exact he.carry z hz
  · intro x _; rw [tm]

theorem load_step (hs : Scr s base cap) (he : Rel v base size e s)
    {d : Reg} (hd : d≠.x0) {off : Nat} (ha : off%8=0) (hb : off+8≤size) (hcap : off+8≤cap) :
    ∃ t,exec (.ldr .x d .x0 off) s=some t ∧ Rel v base size (e.setReg d (e.slot off)) t ∧
      Scr t base cap ∧ KeepRegs [d] s t ∧ Unch base [] s.mem t.mem := by
  let t := s.write .x d (word s.mem base off)
  have kr : KeepRegs [d] s t := ⟨fun r hn => RegUpd.gpr_write_of_ne s .x _
    (by simpa only [List.mem_singleton] using hn),rfl,rfl,rfl⟩
  refine ⟨t,exec_ld hs hcap ha d,⟨?_,?_,?_⟩,
    hs.of_keepRegs kr (by simpa only [List.mem_singleton,ne_eq,eq_comm] using hd),kr,(by intro x _; rfl)⟩
  · intro r z hz
    change (if r=d then some (e.slot off) else e.reg r)=some z at hz
    split at hz
    · rename_i eq; subst eq
      cases hz
      rw [RegUpd.gpr_write_self,BitVec.setWidth_eq]
      exact he.slot off ha hb
    · rename_i ne
      rw [RegUpd.gpr_write_of_ne _ _ _ ne]
      exact he.reg r z hz
  · exact he.slot
  · exact he.carry

theorem store_step (hsize : size≤2^64) (hs : Scr s base cap) (he : Rel v base size e s)
    {r : Reg} {a : α} (hr : e.reg r=some a) {off : Nat} (ha : off%8=0) (hb : off+8≤size) (hcap : off+8≤cap) :
    ∃ t,exec (.str .x r .x0 off) s=some t ∧ Rel v base size (e.setSlot off a) t ∧
      Scr t base cap ∧ KeepRegs [] s t ∧ Unch base [(off,8)] s.mem t.mem := by
  have hw := writeW_outside s.mem base (s.gpr r) (by have := hs.nowrap; omega : off+8≤2^64)
  refine ⟨{s with mem:=s.mem.writeW (VG.Proof.Mont.off base off) (s.gpr r)},
    exec_st hs hcap ha r,⟨he.reg,?_,he.carry⟩,⟨hs.x0,hs.wr,hs.nowrap,hs.enc⟩,⟨fun _ _ => rfl,rfl,rfl,rfl⟩,hw.unch⟩
  intro j hj hjb
  change (v (if j=off then a else e.slot j)).1=_
  split
  · rename_i eq; subst j
    change (v a).1=word (s.mem.writeW (VG.Proof.Mont.off base off) (s.gpr r)) base off
    rw [word_writeW_self]
    exact he.reg r a hr
  · rename_i ne
    have hsep : j+8≤off ∨ off+8≤j := by omega
    have hj64 : j+8≤2^64 := by have := hs.nowrap; omega
    change (v (e.slot j)).1=word _ base j
    rw [hw.word hsep hj64]
    exact he.slot j hj hjb

def Decoded.bound : Decoded → Nat
  | .load _ off | .store _ off => off+8
  | _ => 0

def instrBound (i : Instr) : Nat := match decode i with
  | some v => v.val.bound
  | none => 0

def Decoded.clob : Decoded → List Reg
  | .scalar _ d _ _ _ | .load d _ => [d]
  | .store _ _ => []

def Decoded.writes : Decoded → List (Nat × Nat)
  | .store _ off => [(off,8)]
  | _ => []

theorem decodedStep_sound (hsize : size≤2^64) (hD : D.Sound v) (hs : Scr s base cap)
    (he : Rel v base size e s) {i : Decoded} {e' : Env α}
    (h : decodedStep D size e i=some e') (hcap : i.bound≤cap) :
    ∃ t,exec i.instr s=some t ∧ Rel v base size e' t ∧ Scr t base cap ∧
      KeepRegs i.clob s t ∧ Unch base i.writes s.mem t.mem := by
  cases i with
  | scalar op d a b c =>
    simp only [decodedStep] at h
    split at h
    · contradiction
    · rename_i hg
      have hd : d≠.x0 := by simp_all
      have hv : op.valid=true := by simp_all
      cases ha : arg D e op.useA a with
      | none => simp [ha] at h
      | some va =>
        cases hb : arg D e op.useB b with
        | none => simp [ha,hb] at h
        | some vb =>
          cases hc : arg D e op.useC c with
          | none => simp [ha,hb,hc] at h
          | some vc =>
            cases hh : arg D e op.useD d with
            | none => simp [ha,hb,hc,hh] at h
            | some vd =>
              cases hf : carryArg D e op with
              | none => simp [ha,hb,hc,hh,hf] at h
              | some cf =>
                cases hr : D.applyOp op va vb vc vd cf with
                | none => simp [ha,hb,hc,hh,hf,hr] at h
                | some vr =>
                  simp [ha,hb,hc,hh,hf,hr] at h
                  subst e'
                  exact scalar_step hD hs he hv hd ha hb hc hh hf hr
  | load d off =>
    simp only [decodedStep] at h
    split at h
    · contradiction
    · rename_i hg
      have hd : d≠.x0 := by simp_all
      have ha : off%8=0 := by simp_all
      have hb : off+8≤size := by simp_all
      cases h
      exact load_step hs he hd ha hb hcap
  | store r off =>
    simp only [decodedStep] at h
    split at h
    · contradiction
    · rename_i hg
      have ha : off%8=0 := by simp_all
      have hb : off+8≤size := by simp_all
      cases hr : e.reg r with
      | none => simp [hr] at h
      | some a =>
        simp only [hr,Option.map_some,Option.some.injEq] at h
        subst e'
        exact store_step hsize hs he hr ha hb hcap

def instrClob (i : Instr) : List Reg := match decode i with
  | some v => v.val.clob
  | none => []

def instrWrites (i : Instr) : List (Nat × Nat) := match decode i with
  | some v => v.val.writes
  | none => []

theorem step_sound (hsize : size≤2^64) (hD : D.Sound v) (hs : Scr s base cap)
    (he : Rel v base size e s) {i : Instr} {e' : Env α}
    (h : step D size e i=some e') (hcap : instrBound i≤cap) :
    ∃ t,exec i s=some t ∧ Rel v base size e' t ∧ Scr t base cap ∧
      KeepRegs (instrClob i) s t ∧ Unch base (instrWrites i) s.mem t.mem := by
  unfold step at h
  cases hi : decode i with
  | none => simp [hi] at h
  | some di =>
    simp only [hi] at h
    obtain ⟨t,ht,he,hs,hk,hu⟩ := decodedStep_sound hsize hD hs he h (by simpa only [instrBound,hi] using hcap)
    refine ⟨t,di.property ▸ ht,he,hs,?_,?_⟩
    · simpa only [instrClob,hi] using hk
    · simpa only [instrWrites,hi] using hu

theorem eval_sound (hsize : size≤2^64) (hD : D.Sound v) (hs : Scr s base cap)
    (he : Rel v base size e s) {is : List Instr} {e' : Env α}
    (h : eval D size is e=some e') (hcap : ∀ i∈is,instrBound i≤cap) :
    ∃ t,runBlock isa is s=some t ∧ Rel v base size e' t ∧ Scr t base cap ∧
      KeepRegs (is.flatMap instrClob) s t ∧
      Unch base (is.flatMap instrWrites) s.mem t.mem := by
  induction is generalizing e s with
  | nil =>
    cases h
    exact ⟨s,rfl,he,hs,⟨fun _ _ => rfl,rfl,rfl,rfl⟩,fun _ _ => rfl⟩
  | cons i is ih =>
    simp only [eval,Option.bind_eq_some_iff] at h
    obtain ⟨e₁,h₁,h₂⟩ := h
    obtain ⟨s₁,hs₁,he₁,hsc₁,hk₁,hu₁⟩ := step_sound hsize hD hs he h₁ (hcap i (by simp))
    obtain ⟨t,ht,he',hsc',hk₂,hu₂⟩ := ih hsc₁ he₁ h₂ (fun i hi => hcap i (by simp [hi]))
    refine ⟨t,?_,he',hsc',?_,?_⟩
    · simp only [runBlock_cons,hs₁,runStep_some]; exact ht
    · exact (hk₁.mono (fun r hr => List.mem_append_left _ hr)).trans
        (hk₂.mono (fun r hr => List.mem_append_right _ hr))
    · exact hu₁.trans hu₂

end VG.Proof.Weierstrass.AArch64.Forward
