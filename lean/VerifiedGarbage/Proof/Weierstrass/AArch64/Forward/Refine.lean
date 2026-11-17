module

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Proof.Mont.AArch64.Words
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Data
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Scalar
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `Weierstrass.AArch64.Forward.Run`, which this module and modules that import it used -/

section

@[expose] public section

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
  have hw := writeW_outside s.mem base (s.gpr r) (by have := hs.nowrap; omega_using [hsize, hb] : off+8≤2^64)
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
    have hsep : j+8≤off ∨ off+8≤j := by omega_using [ha, hj, ne]
    have hj64 : j+8≤2^64 := by have := hs.nowrap; omega_using [hsize, hjb]
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

end

end

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.Forward
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

private theorem readW_byte (m : Mem) (a : Addr) {t : Nat} (ht : t<8) :
    (m.readW a 64).extractLsb' (8*t) 8=m (a+BitVec.ofNat 64 t) := by
  change ((m.read a 8).setWidth 64).extractLsb' (8*t) 8=_
  rw [BitVec.setWidth_eq,Mem.extractLsb'_read _ _ ht]

theorem memory_eq {base : Addr} {size : Nat} (ha : size%8=0)
    {s a b : Mem} {W W' : List (Nat × Nat)}
    (hwa : ∀ w∈W,w.1+w.2≤size) (hwb : ∀ w∈W',w.1+w.2≤size)
    (hua : Unch base W s a) (hub : Unch base W' s b)
    (hw : ∀ off,off%8=0 → off+8≤size → word a base off=word b base off) : a=b := by
  funext x
  by_cases hx : ofs base x<size
  · let q := ofs base x/8*8
    let r := ofs base x%8
    have hr : r<8 := Nat.mod_lt _ (by decide)
    have hq : q%8=0 := by simp [q]
    have arith : ∀ n sz : Nat, sz%8=0 → n<sz → n/8*8+8≤sz := by intros; omega_arith
    have hb : q+8≤size := arith _ _ ha hx
    have he := congrArg (fun v : BitVec 64 => v.extractLsb' (8*r) 8) (hw q hq hb)
    rw [readW_byte _ _ hr,readW_byte _ _ hr] at he
    have eq : base+BitVec.ofNat 64 q+BitVec.ofNat 64 r=x := by
      rw [BitVec.add_assoc,←BitVec.ofNat_add]
      have hqr : q+r=ofs base x := by dsimp [q,r]; omega_using []
      rw [hqr]
      change base+BitVec.ofNat 64 (x-base).toNat=x
      rw [BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.add_comm,BitVec.sub_add_cancel]
    simpa only [off,eq] using he
  · exact (hua x (fun w wh => Or.inr (by have := hwa w wh; omega_using [hx, this]))).trans
      (hub x (fun w wh => Or.inr (by have := hwb w wh; omega_using [hx, this]))).symm

theorem post_of_runBlock {is : List Instr} {s t : State} {Q : State → Prop}
    (h : WP isa (.block is) s Q) (hr : runBlock isa is s=some t) : Q t := by
  induction is generalizing s with
  | nil => cases hr; exact WP.block_nil_iff.mp h
  | cons i is ih =>
    obtain ⟨s',hs',hq⟩ := WP.block_cons_iff.mp h
    change exec i s=some s' at hs'
    change (exec i s).bind (runBlock isa is)=some t at hr
    rw [hs'] at hr
    change runBlock isa is s'=some t at hr
    exact ih hq hr

theorem refine_wp {α : Type} {D : Dom α} {v : α → BitVec 64 × Bool}
    {base : Addr} {size cap : Nat} {e e₁ e₂ : Env α} {s : State}
    (hD : D.Sound v) (hs : Scr s base cap) (ha : size%8=0) (hsize : size≤2^64)
    (he : Rel v base size e s) {is js : List Instr}
    (hi : eval D size is e=some e₁) (hj : eval D size js e=some e₂)
    (hEq : ∀ off,off%8=0 → off+8≤size → e₁.slot off=e₂.slot off)
    (hwi : ∀ w∈is.flatMap instrWrites,w.1+w.2≤size)
    (hwj : ∀ w∈js.flatMap instrWrites,w.1+w.2≤size)
    (hci : ∀ i∈is,instrBound i≤cap) (hcj : ∀ i∈js,instrBound i≤cap)
    {Q : State → Prop} (hq : WP isa (.block is) s Q) :
    WP isa (.block js) s fun t => ∃ u,Q u ∧ t.mem=u.mem ∧
      KeepRegs (js.flatMap instrClob) s t := by
  obtain ⟨u,hu,heu,_,_,hmu⟩ := eval_sound hsize hD hs he hi hci
  obtain ⟨t,ht,het,_,hkt,hmt⟩ := eval_sound hsize hD hs he hj hcj
  apply WP.of_runBlock
  refine ⟨t,ht,u,post_of_runBlock hq hu,?_,hkt⟩
  apply memory_eq ha hwj hwi hmt hmu
  intro off ho hb
  exact (het.slot off ho hb).symm.trans ((congrArg (fun z => (v z).1) (hEq off ho hb).symm).trans
    (heu.slot off ho hb))

end VG.Proof.Weierstrass.AArch64.Forward
