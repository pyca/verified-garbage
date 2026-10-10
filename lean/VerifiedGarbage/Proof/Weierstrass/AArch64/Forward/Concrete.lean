import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Refine
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Certificate

/-! The abstract interpreter over concrete words: every operation is evaluated,
so the domain is sound with no certificate. Two environments are `Equiv` when
their registers and slots hold the same words and their carries the same flag,
which is all the interpreter's steps read; a step from equivalent environments
gives equivalent environments. -/

namespace VG.Proof.Weierstrass.AArch64.Forward
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

/-- A word and a carry flag. -/
abbrev CVal := BitVec 64 × Bool

/-- The concrete domain: every operation is evaluated. -/
def concDom : Dom CVal where
  zero := (0,false)
  applyOp op a b c d f := some (op.eval a.1 b.1 c.1 d.1 f.2)

theorem concDom_sound : concDom.Sound id :=
  ⟨⟨rfl,rfl⟩,fun _ _ _ _ _ _ _ h => by cases h; exact ⟨rfl,fun _ => rfl⟩⟩

/-- The environment of a state: no register or carry known yet, every slot
the word in memory at its offset from `base`. -/
def concEnv (s : State) (base : Addr) : Env CVal :=
  ⟨fun _ => none,fun off => (s.mem.readW (base+BitVec.ofNat 64 off) 64,false),none⟩

theorem concEnv_rel (s : State) (base : Addr) (size : Nat) : Rel id base size (concEnv s base) s :=
  ⟨fun _ _ h => (by cases h),fun _ _ _ => rfl,fun _ h => (by cases h)⟩

/-- Registers and slots hold the same words, the carries the same flag. -/
structure Equiv (e₁ e₂ : Env CVal) : Prop where
  reg : ∀ r,(e₁.reg r).map Prod.fst=(e₂.reg r).map Prod.fst
  slot : ∀ off,(e₁.slot off).1=(e₂.slot off).1
  carry : e₁.carry.map Prod.snd=e₂.carry.map Prod.snd

theorem Equiv.refl (e : Env CVal) : Equiv e e := ⟨fun _ => rfl,fun _ => rfl,rfl⟩

theorem Equiv.symm {e₁ e₂ : Env CVal} (h : Equiv e₁ e₂) : Equiv e₂ e₁ :=
  ⟨fun r => (h.reg r).symm,fun off => (h.slot off).symm,h.carry.symm⟩

theorem Equiv.trans {e₁ e₂ e₃ : Env CVal} (h : Equiv e₁ e₂) (h' : Equiv e₂ e₃) : Equiv e₁ e₃ :=
  ⟨fun r => (h.reg r).trans (h'.reg r),fun off => (h.slot off).trans (h'.slot off),h.carry.trans h'.carry⟩

/-- Both are `none`, or both are `some` and related. -/
def ORel {β : Type} (R : β → β → Prop) : Option β → Option β → Prop
  | none,none => True
  | some a,some b => R a b
  | _,_ => False

private theorem map_fst_eq {a b : Option CVal} (h : a.map Prod.fst=b.map Prod.fst) :
    (a=none ↔ b=none) := by
  cases a <;> cases b <;> simp_all

theorem Equiv.setReg {e₁ e₂ : Env CVal} (h : Equiv e₁ e₂) (d : Reg) {x y : CVal} (hxy : x.1=y.1) :
    Equiv (e₁.setReg d x) (e₂.setReg d y) := by
  refine ⟨fun r => ?_,h.slot,h.carry⟩
  simp only [Env.setReg]
  split
  · simp [hxy]
  · exact h.reg r

theorem Equiv.setSlot {e₁ e₂ : Env CVal} (h : Equiv e₁ e₂) (off : Nat) {x y : CVal} (hxy : x.1=y.1) :
    Equiv (e₁.setSlot off x) (e₂.setSlot off y) := by
  refine ⟨h.reg,fun j => ?_,h.carry⟩
  simp only [Env.setSlot]
  split
  · exact hxy
  · exact h.slot j

private theorem arg_rel {e₁ e₂ : Env CVal} (h : Equiv e₁ e₂) (use : Bool) (r : Reg) :
    (arg concDom e₁ use r).map Prod.fst=(arg concDom e₂ use r).map Prod.fst := by
  cases use
  · rfl
  · exact h.reg r

private theorem carryArg_rel {e₁ e₂ : Env CVal} (h : Equiv e₁ e₂) (op : Op) :
    (carryArg concDom e₁ op).map Prod.snd=(carryArg concDom e₂ op).map Prod.snd := by
  unfold carryArg
  split
  · exact h.carry
  · rfl

private theorem bind_rel {β : Type} {f : β → β → Prop} {p : CVal → CVal → Prop}
    {a b : Option CVal} (hab : (a=none ↔ b=none)) (hp : ∀ x y,a=some x → b=some y → p x y)
    {g₁ g₂ : CVal → Option β}
    (hg : ∀ x y,p x y → ORel f (g₁ x) (g₂ y)) : ORel f (a.bind g₁) (b.bind g₂) := by
  cases a with
  | none => cases b with
    | none => trivial
    | some y => simp at hab
  | some x => cases b with
    | none => simp at hab
    | some y => exact hg x y (hp x y rfl rfl)

/-- A step from equivalent environments: both fail, or give equivalent ones. -/
theorem decodedStep_equiv {e₁ e₂ : Env CVal} (h : Equiv e₁ e₂) (size : Nat) (x : Decoded) :
    ORel Equiv (decodedStep concDom size e₁ x) (decodedStep concDom size e₂ x) := by
  cases x with
  | scalar op d a b c =>
    simp only [decodedStep]
    split
    · trivial
    · have ha := arg_rel h op.useA a
      have hb := arg_rel h op.useB b
      have hc := arg_rel h op.useC c
      have hd := arg_rel h op.useD d
      have hf := carryArg_rel h op
      refine bind_rel (p := fun x y => x.1=y.1) (map_fst_eq ha)
        (fun x y hx hy => by simp [hx,hy] at ha; exact ha) fun va va' hva => ?_
      refine bind_rel (p := fun x y => x.1=y.1) (map_fst_eq hb)
        (fun x y hx hy => by simp [hx,hy] at hb; exact hb) fun vb vb' hvb => ?_
      refine bind_rel (p := fun x y => x.1=y.1) (map_fst_eq hc)
        (fun x y hx hy => by simp [hx,hy] at hc; exact hc) fun vc vc' hvc => ?_
      refine bind_rel (p := fun x y => x.1=y.1) (map_fst_eq hd)
        (fun x y hx hy => by simp [hx,hy] at hd; exact hd) fun vd vd' hvd => ?_
      have hf' : (carryArg concDom e₁ op=none ↔ carryArg concDom e₂ op=none) := by
        cases h1 : carryArg concDom e₁ op <;> cases h2 : carryArg concDom e₂ op <;> simp_all
      refine bind_rel (p := fun x y => x.2=y.2) hf'
        (fun x y hx hy => by simp [hx,hy] at hf; exact hf) fun cf cf' hcf => ?_
      change ORel Equiv ((some (op.eval va.1 vb.1 vc.1 vd.1 cf.2)).bind _)
        ((some (op.eval va'.1 vb'.1 vc'.1 vd'.1 cf'.2)).bind _)
      rw [hva,hvb,hvc,hvd,hcf]
      refine ⟨fun r => ?_,h.slot,?_⟩
      · simp only [Env.setReg]
        split
        · rfl
        · exact h.reg r
      · split
        · rfl
        · exact h.carry
  | load d off =>
    simp only [decodedStep]
    split
    · trivial
    · exact h.setReg d (h.slot off)
  | store r off =>
    simp only [decodedStep]
    split
    · trivial
    · have hr := h.reg r
      cases h1 : e₁.reg r <;> cases h2 : e₂.reg r <;> simp_all [ORel]
      exact h.setSlot off hr

theorem ORel.bind {β γ : Type} {R : β → β → Prop} {S : γ → γ → Prop} {a b : Option β}
    (h : ORel R a b) {g₁ g₂ : β → Option γ} (hg : ∀ x y,R x y → ORel S (g₁ x) (g₂ y)) :
    ORel S (a.bind g₁) (b.bind g₂) := by
  cases a <;> cases b <;> first | trivial | exact absurd h id | exact hg _ _ h

/-- Running a block from equivalent environments: both fail, or end equivalent. -/
theorem eval_equiv {size : Nat} {e₁ e₂ : Env CVal} (h : Equiv e₁ e₂) (is : List Instr) :
    ORel Equiv (eval concDom size is e₁) (eval concDom size is e₂) := by
  induction is generalizing e₁ e₂ with
  | nil => exact h
  | cons i is ih =>
    simp only [eval]
    refine ORel.bind ?_ fun _ _ h' => ih h'
    simp only [step]
    cases decode i with
    | none => trivial
    | some v => exact decodedStep_equiv h size v.val

/-- `refine_wp` with the final slots equal as words. -/
theorem refine_words {α : Type} {D : Dom α} {v : α → BitVec 64 × Bool}
    {base : Addr} {size cap : Nat} {e e₁ e₂ : Env α} {s : State}
    (hD : D.Sound v) (hs : Scr s base cap) (ha : size%8=0) (hsize : size≤2^64)
    (he : Rel v base size e s) {is js : List Instr}
    (hi : eval D size is e=some e₁) (hj : eval D size js e=some e₂)
    (hEq : ∀ off,off%8=0 → off+8≤size → (v (e₁.slot off)).1=(v (e₂.slot off)).1)
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
  exact (het.slot off ho hb).symm.trans ((hEq off ho hb).symm.trans (heu.slot off ho hb))

end VG.Proof.Weierstrass.AArch64.Forward
