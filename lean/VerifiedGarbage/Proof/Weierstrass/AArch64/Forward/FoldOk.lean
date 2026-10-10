import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ForwardOk

/-! `foldMoves` keeps every word a block leaves in memory: dropping a copy
`orr d a a` whose register `d` the rest of the block does not read before
writing it, and reading `a` instead of `d` in the next instruction, changes
only the dead register `d`. A step needs agreement only on the registers its
instruction reads (`readRegs`), and after it the two environments agree on
every register that is read later before it is written. -/

namespace VG.Proof.Weierstrass.AArch64.Forward
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64.Forward

variable {size : Nat}

/-- The environments hold the same words in the registers `P` names, the same
words in every slot and the same carry flag. -/
structure Agree (P : Reg → Prop) (e₁ e₂ : Env CVal) : Prop where
  reg : ∀ r,P r → (e₁.reg r).map Prod.fst=(e₂.reg r).map Prod.fst
  slot : ∀ off,(e₁.slot off).1=(e₂.slot off).1
  carry : e₁.carry.map Prod.snd=e₂.carry.map Prod.snd

theorem arg_agree {e₁ e₂ : Env CVal} {use : Bool} {r : Reg}
    (h : use=true → (e₁.reg r).map Prod.fst=(e₂.reg r).map Prod.fst) {v : CVal}
    (hv : arg concDom e₁ use r=some v) : ∃ v',arg concDom e₂ use r=some v' ∧ v'.1=v.1 := by
  cases use with
  | false => cases hv; exact ⟨_,rfl,rfl⟩
  | true =>
    have h := h rfl
    change e₁.reg r=some v at hv
    rw [hv] at h
    cases h₂ : e₂.reg r with
    | none => rw [h₂] at h; cases h
    | some w => rw [h₂] at h; simp at h; exact ⟨w,h₂,h.symm⟩

theorem carryArg_agree {e₁ e₂ : Env CVal} (h : e₁.carry.map Prod.snd=e₂.carry.map Prod.snd) {op : Op}
    {v : CVal} (hv : carryArg concDom e₁ op=some v) : ∃ v',carryArg concDom e₂ op=some v' ∧ v'.2=v.2 := by
  unfold carryArg at hv ⊢
  split at hv
  · rw [hv] at h
    cases h₂ : e₂.carry with
    | none => rw [h₂] at h; cases h
    | some w => rw [h₂] at h; simp at h; exact ⟨w,by simp [*],h.symm⟩
  · cases hv; exact ⟨_,by simp [*],rfl⟩

theorem readRegs_scalar (op : Op) (d a b c : Reg) :
    (op.useA=true → a∈readRegs (op.instr d a b c)) ∧ (op.useB=true → b∈readRegs (op.instr d a b c)) ∧
      (op.useC=true → c∈readRegs (op.instr d a b c)) ∧ (op.useD=true → d∈readRegs (op.instr d a b c)) := by
  cases op <;> simp [Op.useA,Op.useB,Op.useC,Op.useD,Op.instr,readRegs]

theorem writeReg_scalar (op : Op) (d a b c : Reg) : writeReg (op.instr d a b c)=some d := by
  cases op <;> rfl

/-- What a step leaves of two environments that agree on what it reads. -/
structure StepPost (j : Instr) (e₁ e₁' e₂ e₂' : Env CVal) : Prop where
  slot : ∀ off,(e₁'.slot off).1=(e₂'.slot off).1
  carry : e₁'.carry.map Prod.snd=e₂'.carry.map Prod.snd
  written : ∀ r,writeReg j=some r → (e₁'.reg r).map Prod.fst=(e₂'.reg r).map Prod.fst
  kept : ∀ r,writeReg j≠some r → e₁'.reg r=e₁.reg r ∧ e₂'.reg r=e₂.reg r

theorem step_agree {e₁ e₂ e₁' : Env CVal} {j : Instr} (h : Agree (·∈readRegs j) e₁ e₂)
    (hj : step concDom size e₁ j=some e₁') : ∃ e₂',step concDom size e₂ j=some e₂' ∧ StepPost j e₁ e₁' e₂ e₂' := by
  obtain ⟨⟨v,hv⟩,hdec,hstep⟩ := step_some hj
  subst hv
  cases v with
  | load d off =>
    obtain ⟨hd0,ho1,ho2,ho3,rfl⟩ := load_some hstep
    refine ⟨_,step_load hd0 ⟨ho1,ho2,ho3⟩,⟨fun off => h.slot off,h.carry,?_,?_⟩⟩
    · intro r hr; cases hr; simp [Env.setReg,h.slot off]
    · intro r hr
      have : r≠d := fun he => hr (by rw [he]; rfl)
      simp [Env.setReg,this]
  | store r off =>
    obtain ⟨⟨ho1,ho2,ho3⟩,x,hx,rfl⟩ := store_some hstep
    have hr := h.reg r (by simp [Decoded.instr,readRegs])
    rw [hx] at hr
    cases hy : e₂.reg r with
    | none => rw [hy] at hr; cases hr
    | some y =>
      rw [hy] at hr; simp at hr
      refine ⟨_,step_store ⟨ho1,ho2,ho3⟩ hy,⟨fun o => ?_,h.carry,fun _ hw => (by cases hw),fun _ _ => ⟨rfl,rfl⟩⟩⟩
      simp only [Env.setSlot]
      split
      · exact hr
      · exact h.slot o
  | scalar op d a b c =>
    obtain ⟨hA,hB,hC,hD⟩ := readRegs_scalar op d a b c
    simp only [decodedStep] at hstep
    split at hstep
    · cases hstep
    · rename_i hc
      simp only [bind,Option.bind_eq_some_iff,pure] at hstep
      obtain ⟨va,ha,vb,hb,vc,hcc,vd,hdd,cf,hf,vr,hr,he⟩ := hstep
      simp only [concDom,Option.some.injEq] at hr
      subst hr; cases he
      obtain ⟨va',ha',hva⟩ := arg_agree (fun u => h.reg a (hA u)) ha
      obtain ⟨vb',hb',hvb⟩ := arg_agree (fun u => h.reg b (hB u)) hb
      obtain ⟨vc',hc',hvc⟩ := arg_agree (fun u => h.reg c (hC u)) hcc
      obtain ⟨vd',hd',hvd⟩ := arg_agree (fun u => h.reg d (hD u)) hdd
      obtain ⟨cf',hf',hcf⟩ := carryArg_agree h.carry hf
      refine ⟨{e₂.setReg d (op.eval va'.1 vb'.1 vc'.1 vd'.1 cf'.2) with
        carry := if op.flags then some (op.eval va'.1 vb'.1 vc'.1 vd'.1 cf'.2) else e₂.carry},?_,?_⟩
      · have hdec' : decode (op.instr d a b c)=some ⟨.scalar op d a b c,rfl⟩ := hdec
        simp only [step,Decoded.instr,hdec']
        simp only [decodedStep,hc,ite_false,Bool.false_eq_true,bind,ha',hb',hc',hd',hf',Option.bind,pure]
        simp only [concDom]
      · refine ⟨fun off => h.slot off,?_,?_,?_⟩
        · dsimp only
          split
          · simp [hva,hvb,hvc,hvd,hcf]
          · exact h.carry
        · intro r hw
          rw [Decoded.instr,writeReg_scalar] at hw; cases hw
          simp [Env.setReg,hva,hvb,hvc,hvd,hcf]
        · intro r hw
          rw [Decoded.instr,writeReg_scalar] at hw
          have : r≠d := fun he => hw (by rw [he])
          simp [Env.setReg,this]

theorem regDead_cons (r : Reg) (j : Instr) (rest : List Instr) :
    regDead r (j::rest)=(if r∈readRegs j then false else if writeReg j=some r then true else regDead r rest) := by
  simp only [regDead,List.contains_iff_mem,beq_iff_eq]

theorem live_of_read {r : Reg} {j : Instr} {rest : List Instr} (h : r∈readRegs j) :
    regDead r (j::rest)=false := by
  simp [regDead_cons,h]

theorem live_of_kept {r : Reg} {j : Instr} {rest : List Instr} (hw : writeReg j≠some r)
    (h : regDead r rest=false) : regDead r (j::rest)=false := by
  rw [regDead_cons]
  split
  · rfl
  · simp [h]

/-- The renaming `foldMoves` applies to the instruction after a copy. -/
def ren (d a : Reg) (r : Reg) : Reg := if r==d then a else r

theorem renameRead_instr (d a : Reg) (op : Op) (d' x y z : Reg) :
    renameRead d a (op.instr d' x y z)=op.instr d' (ren d a x) (ren d a y) (ren d a z) := by
  cases op <;> rfl

/-- A scalar instruction decodes, after renaming, to its renamed operation. -/
theorem decode_rename {d a : Reg} (hd : d≠.x0) {i : Instr} {v : {v : Decoded // v.instr=i}}
    (h : decode i=some v) {op : Op} {d' x y z : Reg} (hv : v.val=.scalar op d' x y z) :
    (decode (renameRead d a i)).map Subtype.val=some (.scalar op d' (ren d a x) (ren d a y) (ren d a z)) := by
  obtain ⟨v,hvi⟩ := v
  dsimp only at hv
  subst hv; subst hvi
  have h0 : ren d a .x0=.x0 := by simp [ren,Ne.symm hd]
  have h' := congrArg (Option.map Subtype.val) h
  clear h
  rw [Decoded.instr,renameRead_instr]; simp only [Decoded.instr,Option.map_some] at h'
  cases op <;> simp only [Op.instr,decode] at h' ⊢ <;> dsimp only [Option.map] at h' ⊢ <;>
    simp only [Option.some.injEq,Decoded.scalar.injEq,eq_comm (a := Reg.x0)] at h' ⊢ <;> simp [h',h0]

/-- A scalar step reading through a renaming: if each register the
instruction reads holds the same word in `e₁` as its renaming in `e₂`, the
renamed instruction computes the same value from `e₂`. -/
theorem scalar_rename {e₁ e₂ e₁' : Env CVal} {op : Op} {d' x y z : Reg} (g : Reg → Reg)
    (hD : op.useD=true → (e₁.reg d').map Prod.fst=(e₂.reg d').map Prod.fst)
    (hr : ∀ r∈readRegs (op.instr d' x y z),(e₁.reg r).map Prod.fst=(e₂.reg (g r)).map Prod.fst)
    (hc : e₁.carry.map Prod.snd=e₂.carry.map Prod.snd)
    (hs : decodedStep concDom size e₁ (.scalar op d' x y z)=some e₁') :
    ∃ u,e₁'={e₁.setReg d' u with carry:=if op.flags then some u else e₁.carry} ∧
      decodedStep concDom size e₂ (.scalar op d' (g x) (g y) (g z))=
        some {e₂.setReg d' u with carry:=if op.flags then some u else e₂.carry} := by
  obtain ⟨hA,hB,hC,-⟩ := readRegs_scalar op d' x y z
  simp only [decodedStep] at hs ⊢
  split at hs
  · cases hs
  · rename_i hcnd
    simp only [bind,Option.bind_eq_some_iff,pure] at hs
    obtain ⟨va,ha,vb,hb,vc,hcc,vd,hdd,cf,hf,vr,hvr,he⟩ := hs
    simp only [concDom,Option.some.injEq] at hvr
    subst hvr; cases he
    obtain ⟨va',ha',hva⟩ := arg_agree (e₂ := {e₂ with reg:=fun r => e₂.reg (g r)})
      (fun u => hr x (hA u)) ha
    obtain ⟨vb',hb',hvb⟩ := arg_agree (e₂ := {e₂ with reg:=fun r => e₂.reg (g r)})
      (fun u => hr y (hB u)) hb
    obtain ⟨vc',hc',hvc⟩ := arg_agree (e₂ := {e₂ with reg:=fun r => e₂.reg (g r)})
      (fun u => hr z (hC u)) hcc
    obtain ⟨cf',hf',hcf⟩ := carryArg_agree hc hf
    obtain ⟨vd',hd',hvd⟩ := arg_agree (e₂ := e₂) hD hdd
    refine ⟨_,rfl,?_⟩
    simp only [arg] at ha' hb' hc' hd'
    simp only [hcnd,ite_false,Bool.false_eq_true,arg,bind,Option.bind,pure]
    rw [show (if op.useA then e₂.reg (g x) else some concDom.zero)=some va' from ha',
      show (if op.useB then e₂.reg (g y) else some concDom.zero)=some vb' from hb',
      show (if op.useC then e₂.reg (g z) else some concDom.zero)=some vc' from hc',
      show (if op.useD then e₂.reg d' else some concDom.zero)=some vd' from hd',hf']
    simp only [concDom,hva,hvb,hvc,hvd,hcf]

/-- Agreement on the registers `rest` reads before writing them. -/
abbrev Live (rest : List Instr) (e₁ e₂ : Env CVal) : Prop := Agree (fun r => regDead r rest=false) e₁ e₂

/-- An instruction both blocks run. -/
theorem live_step {e₁ e₂ e₁' : Env CVal} {j : Instr} {rest : List Instr} (h : Live (j::rest) e₁ e₂)
    (hj : step concDom size e₁ j=some e₁') : ∃ e₂',step concDom size e₂ j=some e₂' ∧ Live rest e₁' e₂' := by
  obtain ⟨e₂',he₂,hp⟩ := step_agree ⟨fun r hr => h.reg r (live_of_read hr),h.slot,h.carry⟩ hj
  refine ⟨e₂',he₂,⟨fun r hr => ?_,hp.slot,hp.carry⟩⟩
  by_cases hw : writeReg j=some r
  · exact hp.written r hw
  · obtain ⟨h₁,h₂⟩ := hp.kept r hw
    rw [h₁,h₂]
    exact h.reg r (live_of_kept hw hr)

theorem useD_of_renames {op : Op} {d a b c : Reg} (h : renames (op.instr d a b c)=true) : op.useD=false := by
  cases op <;> first | rfl | cases h

theorem step_of_decode {α : Type} {D : Dom α} {e : Env α} {j : Instr} {v : Decoded}
    (h : (decode j).map Subtype.val=some v) : step D size e j=decodedStep D size e v := by
  simp only [step]
  cases hd : decode j with
  | none => rw [hd] at h; cases h
  | some w => rw [hd] at h; cases h; rfl

/-- A copy `orr d a a` and the next instruction, against that instruction
reading `a` for `d`, when `d` is dead after them. -/
theorem fold_step {e₁ e₂ e₁a e₁b : Env CVal} {d a : Reg} {i : Instr} {is : List Instr}
    (h : Live ((.logic .orr .x d a a)::i::is) e₁ e₂) (hdead : regDead d is=true)
    (hx0 : (readRegs i).contains .x0=false) (hren : renames i=true)
    (h1 : step concDom size e₁ (.logic .orr .x d a a)=some e₁a) (h2 : step concDom size e₁a i=some e₁b) :
    ∃ e₂b,step concDom size e₂ (renameRead d a i)=some e₂b ∧ Live is e₁b e₂b := by
  have hd : d≠.x0 := by
    rintro rfl
    simp [step,decode,decodedStep] at h1
  obtain ⟨y,hy⟩ : ∃ y,e₁.reg a=some y := by
    cases hy : e₁.reg a with
    | none => simp [step,decode,decodedStep,arg,Op.useA,Op.valid,hy,hd,bind,Option.bind] at h1
    | some y => exact ⟨y,rfl⟩
  rw [step_copy hd hy] at h1
  cases h1
  have ha := h.reg a (live_of_read (by simp [readRegs]))
  have hwo : writeReg (.logic .orr .x d a a)=some d := rfl
  obtain ⟨⟨v,hv⟩,hdec,hs⟩ := step_some h2
  cases v with
  | load d'' off => subst hv; simp [Decoded.instr,readRegs] at hx0
  | store r off => subst hv; simp [Decoded.instr,readRegs] at hx0
  | scalar op d' x y' z =>
    subst hv
    have hD := useD_of_renames hren
    have hstep := step_of_decode (D := concDom) (size := size) (e := e₂) (decode_rename (a := a) hd hdec rfl)
    obtain ⟨u,rfl,hu⟩ := scalar_rename (e₁ := e₁.setReg d (y.1,false)) (e₂ := e₂) (op := op) (d' := d') (x := x) (y := y') (z := z)
      (ren d a) (fun h' => by rw [hD] at h'; cases h') (fun r hr => by
      by_cases hrd : r=d
      · subst hrd
        rw [show ren r a r=a by simp [ren],← ha,hy]
        simp [Env.setReg]
      · rw [show ren d a r=r by simp [ren,hrd]]
        simp only [Env.setReg,hrd,ite_false]
        exact h.reg r (live_of_kept (by rw [hwo]; simpa using Ne.symm hrd) (live_of_read hr))) h.carry hs
    refine ⟨_,hstep.trans hu,⟨fun r hr => ?_,fun off => h.slot off,?_⟩⟩
    · simp only [Env.setReg]
      by_cases hrd' : r=d'
      · simp [hrd']
      · have hrd : r≠d := by rintro rfl; rw [hdead] at hr; cases hr
        simp only [hrd',hrd,ite_false]
        refine h.reg r (live_of_kept (by rw [hwo]; simpa using Ne.symm hrd) (live_of_kept ?_ hr))
        rw [Decoded.instr,writeReg_scalar]; simpa using Ne.symm hrd'
    · dsimp only
      split
      · rfl
      · exact h.carry

/-- `foldMoves` from environments that agree on what the block reads: it
succeeds, and the slots and carry agree at the end. -/
theorem foldMoves_ok (is : List Instr) : ∀ {e₁ e₂ l : Env CVal},Live is e₁ e₂ →
    eval concDom size is e₁=some l → ∃ r,eval concDom size (foldMoves is) e₂=some r ∧ Live [] l r := by
  induction is using foldMoves.induct with
  | case1 d a b i is hc ih =>
    intro e₁ e₂ l h he
    have hc0 := hc
    simp only [Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true',bne_iff_ne] at hc
    obtain ⟨⟨⟨⟨rfl,hdead⟩,hx0⟩,-⟩,hren⟩ := hc
    rw [foldMoves.eq_1]; simp only [hc0,ite_true]
    simp only [eval] at he ⊢
    cases h1 : step concDom size e₁ (.logic .orr .x d a a) with
    | none => rw [h1] at he; cases he
    | some e₁a =>
      rw [h1,Option.bind_some] at he
      cases h2 : step concDom size e₁a i with
      | none => rw [h2] at he; cases he
      | some e₁b =>
        rw [h2,Option.bind_some] at he
        obtain ⟨e₂b,h3,h'⟩ := fold_step h hdead hx0 hren h1 h2
        rw [h3]
        exact ih h' he
  | case2 d a b i is hc ih =>
    intro e₁ e₂ l h he
    rw [foldMoves.eq_1]; simp only [hc,Bool.false_eq_true,ite_false]
    simp only [eval] at he ⊢
    cases h1 : step concDom size e₁ (.logic .orr .x d a b) with
    | none => rw [h1] at he; cases he
    | some e₁' =>
      rw [h1] at he
      obtain ⟨e₂',h2,h'⟩ := live_step h h1
      rw [h2]
      exact ih h' he
  | case3 i is hne ih =>
    intro e₁ e₂ l h he
    rw [foldMoves.eq_2 i is hne]
    simp only [eval] at he ⊢
    cases h1 : step concDom size e₁ i with
    | none => rw [h1] at he; cases he
    | some e₁' =>
      rw [h1] at he
      obtain ⟨e₂',h2,h'⟩ := live_step h h1
      rw [h2]
      exact ih h' he
  | case4 =>
    intro e₁ e₂ l h he
    cases he
    exact ⟨e₂,rfl,h⟩

end VG.Proof.Weierstrass.AArch64.Forward
