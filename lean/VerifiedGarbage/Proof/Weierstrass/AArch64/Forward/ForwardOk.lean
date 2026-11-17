module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.OptimizeK
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Certificate
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Refine

/-! ### `Weierstrass.AArch64.Forward.Concrete`, which this module and modules that import it used -/

section

/-! The abstract interpreter over concrete words: every operation is evaluated,
so the domain is sound with no certificate. Two environments are `Equiv` when
their registers and slots hold the same words and their carries the same flag,
which is all the interpreter's steps read; a step from equivalent environments
gives equivalent environments. -/

@[expose] public section

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

end

end

/-! `forward` keeps every word a block leaves in memory, for every block the
interpreter runs: a load whose word a register already holds becomes a copy of
that register (or nothing), and a `movz` of zero into a register holding zero
is dropped. The pass numbers the values it tracks; a valuation `ρ` of the
numbers describes the original block's environment, and the scheduled block's
environment holds the same words. -/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.Forward
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64.Forward

variable {size : Nat}

theorem eval_append {α : Type} (D : Dom α) (xs ys : List Instr) (e : Env α) :
    eval D size (xs ++ ys) e=(eval D size xs e).bind (eval D size ys) := by
  induction xs generalizing e with
  | nil => rfl
  | cons i xs ih =>
    simp only [List.cons_append,eval]
    cases step D size e i with
    | none => rfl
    | some e' => exact ih e'

theorem mem_put {β γ : Type} [BEq β] [LawfulBEq β] {k : β} {v : γ} {xs : List (β×γ)} {p : β×γ}
    (h : p∈put k v xs) : p=(k,v) ∨ (p∈xs ∧ p.1≠k) := by
  simp only [put,List.mem_cons,List.mem_filter,bne_iff_ne,ne_eq] at h
  rcases h with h | ⟨h,h'⟩
  · exact .inl h
  · exact .inr ⟨h,h'⟩

theorem mem_of_lookup {β γ : Type} [BEq β] [LawfulBEq β] {k : β} {v : γ} :
    ∀ {xs : List (β×γ)},xs.lookup k=some v → (k,v)∈xs
  | [],h => by cases h
  | (k',v')::xs,h => by
    simp only [List.lookup] at h
    split at h
    · rename_i hk
      cases h
      simp only [beq_iff_eq] at hk
      subst hk
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_lookup h)

/-- What `forward` knows: through `ρ`, the words of the registers and slots it
tracks in the original's environment, `0` the zero, and numbers no larger than
its last fresh one; the scheduled block's environment holds the same words. -/
structure FInv (ρ : Nat → BitVec 64) (s : FState) (eo ep : Env CVal) : Prop where
  equiv : Equiv eo ep
  zero : ρ 0=0
  regs : ∀ p∈s.1,∃ x,eo.reg p.1=some x ∧ x.1=ρ p.2
  mem : ∀ p∈s.2.1,(eo.slot p.1).1=ρ p.2
  regsLe : ∀ p∈s.1,p.2≤s.2.2.2
  memLe : ∀ p∈s.2.1,p.2≤s.2.2.2
  pos : 1≤s.2.2.2

theorem step_some {e e' : Env CVal} {i : Instr} (h : step concDom size e i=some e') :
    ∃ v : {v : Decoded // v.instr=i},decode i=some v ∧ decodedStep concDom size e v.val=some e' := by
  simp only [step] at h
  cases hd : decode i with
  | none => rw [hd] at h; cases h
  | some v => rw [hd] at h; exact ⟨v,rfl,h⟩

theorem load_some {e e' : Env CVal} {d : Reg} {off : Nat}
    (h : decodedStep concDom size e (.load d off)=some e') :
    d≠.x0 ∧ off%8=0 ∧ off+8≤size ∧ off<32768 ∧ e'=e.setReg d (e.slot off) := by
  simp only [decodedStep] at h
  split at h
  · cases h
  · rename_i hc
    simp only [Bool.or_eq_true,decide_eq_true_eq,Bool.not_eq_true',Bool.and_eq_false_imp,
      Bool.and_eq_true,decide_eq_true_eq,not_or] at hc
    cases h
    have := hc.1
    by_contra hn
    simp_all

theorem store_some {e e' : Env CVal} {r : Reg} {off : Nat}
    (h : decodedStep concDom size e (.store r off)=some e') :
    (off%8=0 ∧ off+8≤size ∧ off<32768) ∧ ∃ x,e.reg r=some x ∧ e'=e.setSlot off x := by
  simp only [decodedStep] at h
  split at h
  · cases h
  · rename_i hc
    cases hr : e.reg r with
    | none => rw [hr] at h; cases h
    | some x =>
      rw [hr] at h
      cases h
      refine ⟨?_,x,rfl,rfl⟩
      simpa [and_assoc] using hc

theorem scalar_some {e e' : Env CVal} {op : Op} {d a b c : Reg}
    (h : decodedStep concDom size e (.scalar op d a b c)=some e') :
    d≠.x0 ∧ e'.slot=e.slot ∧ (∀ r,r≠d → e'.reg r=e.reg r) ∧
      (∃ x,e'.reg d=some x ∧ (op.flags=false → e'.carry=e.carry) ∧
        ∃ va vb vc vd : CVal,∃ cf : CVal,x=op.eval va.1 vb.1 vc.1 vd.1 cf.2) := by
  simp only [decodedStep] at h
  split at h
  · cases h
  · rename_i hc
    have hd : d≠.x0 := by intro hd; subst hd; simp at hc
    simp only [bind,Option.bind_eq_some_iff,pure] at h
    obtain ⟨va,ha,vb,hb,vc,hcc,vd,hdd,cf,hf,vr,hr,he⟩ := h
    simp only [concDom,Option.some.injEq] at hr
    subst hr
    cases he
    refine ⟨hd,rfl,fun r hr => by simp [Env.setReg,hr],
      ⟨op.eval va.1 vb.1 vc.1 vd.1 cf.2,by simp [Env.setReg],?_,?_⟩⟩
    · intro hfl; simp [hfl]
    · exact ⟨va,vb,vc,vd,cf,rfl⟩

/-- `ρ` with the number `n` given the word `w`. -/
def upd (ρ : Nat → BitVec 64) (n : Nat) (w : BitVec 64) : Nat → BitVec 64 :=
  fun m => if m=n then w else ρ m

theorem upd_self (ρ : Nat → BitVec 64) (n : Nat) (w : BitVec 64) : upd ρ n w n=w := by simp [upd]

theorem upd_lt {ρ : Nat → BitVec 64} {n m : Nat} (w : BitVec 64) (h : m<n) : upd ρ n w m=ρ m := by
  simp [upd,Nat.ne_of_lt h]

/-- After a load of `off` into `d` numbered `value`. -/
theorem load_inv {ρ : Nat → BitVec 64} {s : FState} {eo ep ep' : Env CVal} (h : FInv ρ s eo ep)
    {d : Reg} {off value : Nat} {out : List Instr} {w : BitVec 64}
    (hval : (eo.slot off).1=upd ρ (s.2.2.2+1) w value) (hle : value≤s.2.2.2+1)
    (he : Equiv (eo.setReg d (eo.slot off)) ep') :
    FInv (upd ρ (s.2.2.2+1) w) (put d value s.1,put off value s.2.1,out,s.2.2.2+1)
      (eo.setReg d (eo.slot off)) ep' := by
  refine ⟨he,?_,?_,?_,?_,?_,by dsimp only; omega_arith⟩
  · rw [upd_lt _ (by have := h.pos; omega_arith)]; exact h.zero
  · dsimp only; intro p hp
    rcases mem_put hp with rfl | ⟨hp,hne⟩
    · exact ⟨_,by simp [Env.setReg],hval⟩
    · obtain ⟨x,hx,hx'⟩ := h.regs p hp
      refine ⟨x,by simp [Env.setReg,hne,hx],?_⟩
      rw [hx',upd_lt _ (by have := h.regsLe p hp; omega_arith)]
  · dsimp only; intro p hp
    rcases mem_put hp with rfl | ⟨hp,_⟩
    · exact hval
    · rw [upd_lt _ (by have := h.memLe p hp; omega_arith)]; exact h.mem p hp
  · dsimp only; intro p hp
    rcases mem_put hp with rfl | ⟨hp,_⟩
    · exact hle
    · have := h.regsLe p hp; omega_arith
  · dsimp only; intro p hp
    rcases mem_put hp with rfl | ⟨hp,_⟩
    · exact hle
    · have := h.memLe p hp; omega_arith

/-- After a store of `r`'s word `x` to `off`, numbered `value`. -/
theorem store_inv {ρ : Nat → BitVec 64} {s : FState} {eo ep ep' : Env CVal} (h : FInv ρ s eo ep)
    {r : Reg} {off value : Nat} {out : List Instr} {w : BitVec 64} {x : CVal} (hx : eo.reg r=some x)
    (hval : x.1=upd ρ (s.2.2.2+1) w value) (hle : value≤s.2.2.2+1)
    (he : Equiv (eo.setSlot off x) ep') :
    FInv (upd ρ (s.2.2.2+1) w) (put r value s.1,put off value s.2.1,out,s.2.2.2+1)
      (eo.setSlot off x) ep' := by
  refine ⟨he,?_,?_,?_,?_,?_,by dsimp only; omega_arith⟩
  · rw [upd_lt _ (by have := h.pos; omega_arith)]; exact h.zero
  · dsimp only; intro p hp
    rcases mem_put hp with rfl | ⟨hp,_⟩
    · exact ⟨x,hx,hval⟩
    · obtain ⟨y,hy,hy'⟩ := h.regs p hp
      exact ⟨y,hy,by rw [hy',upd_lt _ (by have := h.regsLe p hp; omega_arith)]⟩
  · dsimp only; intro p hp
    rcases mem_put hp with rfl | ⟨hp,hne⟩
    · simp only [Env.setSlot,ite_true]; exact hval
    · simp only [Env.setSlot,hne,ite_false]
      rw [upd_lt _ (by have := h.memLe p hp; omega_arith)]; exact h.mem p hp
  · dsimp only; intro p hp
    rcases mem_put hp with rfl | ⟨hp,_⟩
    · exact hle
    · have := h.regsLe p hp; omega_arith
  · dsimp only; intro p hp
    rcases mem_put hp with rfl | ⟨hp,_⟩
    · exact hle
    · have := h.memLe p hp; omega_arith

/-- After an instruction writing `d` (with `y`, numbered `nv`) and no slot. -/
theorem write_inv {ρ : Nat → BitVec 64} {s : FState} {eo eo' ep ep' : Env CVal} (h : FInv ρ s eo ep)
    {d : Reg} {nv : Nat} {out : List Instr} {w : BitVec 64} {y : CVal}
    (hs : eo'.slot=eo.slot) (hr : ∀ r,r≠d → eo'.reg r=eo.reg r) (hy : eo'.reg d=some y)
    (hval : y.1=upd ρ (s.2.2.2+1) w nv) (hle : nv≤s.2.2.2+1) (he : Equiv eo' ep') :
    FInv (upd ρ (s.2.2.2+1) w) (put d nv s.1,s.2.1,out,s.2.2.2+1) eo' ep' := by
  refine ⟨he,?_,?_,?_,?_,?_,by dsimp only; omega_arith⟩
  · rw [upd_lt _ (by have := h.pos; omega_arith)]; exact h.zero
  · dsimp only; intro p hp
    rcases mem_put hp with rfl | ⟨hp,hne⟩
    · exact ⟨y,hy,hval⟩
    · obtain ⟨x,hx,hx'⟩ := h.regs p hp
      exact ⟨x,by rw [hr _ hne,hx],by rw [hx',upd_lt _ (by have := h.regsLe p hp; omega_arith)]⟩
  · dsimp only; intro p hp
    rw [hs,upd_lt _ (by have := h.memLe p hp; omega_arith)]; exact h.mem p hp
  · dsimp only; intro p hp
    rcases mem_put hp with rfl | ⟨hp,_⟩
    · exact hle
    · have := h.regsLe p hp; omega_arith
  · dsimp only; intro p hp
    have := h.memLe p hp; omega_arith

theorem movz_zero (n : Nat) (a b c d : BitVec 64) (f : Bool) : ((Op.movz 0 n).eval a b c d f).1=0 := by
  simp [Op.eval,Op.useA,Op.useB,Op.useC,Op.useD,Op.useCarry,scalarState,Op.instr,exec,
    State.write,Size.bits,BitVec.setWidth_eq]
  split <;> rfl

theorem eval_single {α : Type} (D : Dom α) (j : Instr) (e : Env α) :
    eval D size [j] e=step D size e j := by
  simp only [eval]
  cases step D size e j <;> rfl

theorem step_copy {e : Env CVal} {d r : Reg} {y : CVal} (hd : d≠.x0) (hr : e.reg r=some y) :
    step concDom size e (.logic .orr .x d r r)=some (e.setReg d (y.1,false)) := by
  simp only [step,decode,decodedStep,bind,Option.bind,arg,carryArg,Op.useA,Op.useB,Op.useC,Op.useD,
    Op.useCarry,Op.valid,Op.flags,hr,concDom]
  simp [hd,eval_copy,Env.setReg]

theorem step_load {e : Env CVal} {d : Reg} {off : Nat} (hd : d≠.x0) (ho : off%8=0 ∧ off+8≤size ∧ off<32768) :
    step concDom size e (.ldr .x d .x0 off)=some (e.setReg d (e.slot off)) := by
  simp only [step,decode,decodedStep,bind,Option.bind]
  simp [hd,ho.1,ho.2.1,ho.2.2]

theorem step_store {e : Env CVal} {r : Reg} {off : Nat} {y : CVal} (ho : off%8=0 ∧ off+8≤size ∧ off<32768)
    (hr : e.reg r=some y) :
    step concDom size e (.str .x r .x0 off)=some (e.setSlot off y) := by
  simp only [step,decode,decodedStep,bind,Option.bind]
  simp [ho.1,ho.2.1,ho.2.2,hr]

theorem fwdStep_scalar (s : FState) {op : Op} (hop : ∀ n,op≠.movz 0 n) (d a b c : Reg) :
    fwdStep (op.instr d a b c) s=(put d (s.2.2.2+1) s.1,s.2.1,op.instr d a b c :: s.2.2.1,s.2.2.2+1) := by
  cases op with
  | movz v n =>
    have hv : v≠0 := fun h => hop n (by rw [h])
    simp only [Op.instr,fwdStep]
    split <;> first | rfl | simp_all
  | _ => rfl

theorem fwdStep_movz (s : FState) (n : Nat) (d a b c : Reg) :
    fwdStep ((Op.movz 0 n).instr d a b c) s=(put d 0 s.1,s.2.1,
      (if s.1.lookup d=some 0 then s.2.2.1 else (Op.movz 0 n).instr d a b c :: s.2.2.1),s.2.2.2+1) := rfl

/-- One step of the original block, against what `forward` emits for it. -/
theorem fwd_step {ρ : Nat → BitVec 64} {s : FState} {eo ep eo' : Env CVal}
    (h : FInv ρ s eo ep) {i : Instr} (hi : step concDom size eo i=some eo') :
    ∃ em ρ' ep',(fwdStep i s).2.2.1=em.reverse ++ s.2.2.1 ∧ eval concDom size em ep=some ep' ∧
      FInv ρ' (fwdStep i s) eo' ep' := by
  obtain ⟨⟨v,hv⟩,_,hstep⟩ := step_some hi
  subst hv
  cases v with
  | load d off =>
    obtain ⟨hd0,ho1,ho2,ho3,rfl⟩ := load_some hstep
    obtain ⟨value,hvdef⟩ : ∃ v,v=(s.2.1.lookup off).getD (s.2.2.2+1) := ⟨_,rfl⟩
    have hval : (eo.slot off).1=upd ρ (s.2.2.2+1) (eo.slot off).1 value := by
      cases hm : s.2.1.lookup off with
      | none => simp only [hvdef,hm,Option.getD_none,upd_self]
      | some w =>
        have hmem := mem_of_lookup hm
        simp only [hvdef,hm,Option.getD_some]
        rw [upd_lt _ (by have := h.memLe _ hmem; omega_arith)]
        exact h.mem _ hmem
    have hle : value≤s.2.2.2+1 := by
      cases hm : s.2.1.lookup off with
      | none => simp [hvdef,hm]
      | some w => have := h.memLe _ (mem_of_lookup hm); simp [hvdef,hm]; omega_arith
    -- the scheduled block skips the load, copies a register, or loads
    have hkeep : ∀ r x,(r,value)∈s.1 → eo.reg r=some x →
        Equiv (eo.setReg d (eo.slot off)) (ep.setReg d (x.1,false)) := by
      intro r x hr hx
      refine h.equiv.setReg d ?_
      obtain ⟨x',hx',hx''⟩ := h.regs _ hr
      rw [hx] at hx'; cases hx'
      dsimp only
      rw [hval,hx'',upd_lt _ (by have := h.regsLe _ hr; omega_arith)]
    by_cases hl : s.1.lookup d=some value
    · -- `d` already holds the word
      refine ⟨[],upd ρ (s.2.2.2+1) (eo.slot off).1,ep,?_,rfl,?_⟩
      · simp [Decoded.instr,fwdStep,← hvdef,hl]
      · have hm := mem_of_lookup hl
        obtain ⟨x,hx,hx'⟩ := h.regs _ hm
        have := hkeep d x hm hx
        subst hvdef
        refine load_inv h hval hle ?_
        refine this.trans ⟨fun r => ?_,fun _ => rfl,rfl⟩
        simp only [Env.setReg]
        split
        · rename_i hr; subst hr; have := h.equiv.reg r; rw [hx] at this
          cases hp : ep.reg r <;> simp_all
        · rfl
    · cases hf : s.1.find? (fun p => p.2==value) with
      | none =>
        refine ⟨[.ldr .x d .x0 off],upd ρ (s.2.2.2+1) (eo.slot off).1,ep.setReg d (ep.slot off),?_,?_,?_⟩
        · simp [Decoded.instr,fwdStep,← hvdef,hl,hf]
        · rw [eval_single]; exact step_load hd0 ⟨ho1,ho2,ho3⟩
        · subst hvdef; exact load_inv h hval hle (h.equiv.setReg d (h.equiv.slot off))
      | some p =>
        have hp := List.mem_of_find?_eq_some hf
        have hpv : p.2=value := by simpa [← hvdef] using List.find?_some hf
        have hpr : (p.1,value)∈s.1 := hpv ▸ hp
        obtain ⟨x,hx,_⟩ := h.regs _ hp
        by_cases hpd : p.1=d
        · refine ⟨[],upd ρ (s.2.2.2+1) (eo.slot off).1,ep,?_,rfl,?_⟩
          · simp [Decoded.instr,fwdStep,← hvdef,hl,hf,hpd]
          · have hk := hkeep p.1 x hpr hx
            subst hvdef
            refine load_inv h hval hle (hk.trans ⟨fun r => ?_,fun _ => rfl,rfl⟩)
            simp only [Env.setReg]
            split
            · rename_i hr; subst hr; have := h.equiv.reg r; rw [← hpd,hx] at this
              rw [← hpd]; cases hq : ep.reg p.1 <;> simp_all
            · rfl
        · have hxp := h.equiv.reg p.1
          rw [hx] at hxp
          cases hy : ep.reg p.1 with
          | none => rw [hy] at hxp; cases hxp
          | some y =>
            rw [hy] at hxp
            simp only [Option.map_some,Option.some.injEq] at hxp
            refine ⟨[.logic .orr .x d p.1 p.1],upd ρ (s.2.2.2+1) (eo.slot off).1,ep.setReg d (y.1,false),?_,?_,?_⟩
            · simp [Decoded.instr,fwdStep,← hvdef,hl,hf,hpd]
            · rw [eval_single]; exact step_copy hd0 hy
            · have := hkeep p.1 x hpr hx
              subst hvdef
              refine load_inv h hval hle ?_
              rw [hxp] at this
              exact this
  | store r off =>
    obtain ⟨⟨ho1,ho2,ho3⟩,x,hx,rfl⟩ := store_some hstep
    obtain ⟨value,hvdef⟩ : ∃ v,v=(s.1.lookup r).getD (s.2.2.2+1) := ⟨_,rfl⟩
    have hval : x.1=upd ρ (s.2.2.2+1) x.1 value := by
      cases hm : s.1.lookup r with
      | none => simp only [hvdef,hm,Option.getD_none,upd_self]
      | some w =>
        have hmem := mem_of_lookup hm
        obtain ⟨x',hx',hx''⟩ := h.regs _ hmem
        rw [hx] at hx'; cases hx'
        simp only [hvdef,hm,Option.getD_some]
        rw [upd_lt _ (by have := h.regsLe _ hmem; omega_arith)]
        exact hx''
    have hle : value≤s.2.2.2+1 := by
      cases hm : s.1.lookup r with
      | none => simp [hvdef,hm]
      | some w => have := h.regsLe _ (mem_of_lookup hm); simp [hvdef,hm]; omega_arith
    have hxp := h.equiv.reg r
    rw [hx] at hxp
    cases hy : ep.reg r with
    | none => rw [hy] at hxp; cases hxp
    | some y =>
      rw [hy] at hxp
      simp only [Option.map_some,Option.some.injEq] at hxp
      refine ⟨[.str .x r .x0 off],upd ρ (s.2.2.2+1) x.1,ep.setSlot off y,by simp [Decoded.instr,fwdStep],?_,?_⟩
      · rw [eval_single]; exact step_store ⟨ho1,ho2,ho3⟩ hy
      · have hst : fwdStep (Decoded.store r off).instr s=(put r value s.1,put off value s.2.1,
            .str .x r .x0 off :: s.2.2.1,s.2.2.2+1) := by simp [Decoded.instr,fwdStep,hvdef]
        rw [hst]
        exact store_inv h hx hval hle (h.equiv.setSlot off hxp)
  | scalar op d a b c =>
    obtain ⟨hd0,hsl,hrg,y,hy,hcar,va,vb,vc,vd,cf,hyv⟩ := scalar_some hstep
    have hrel := decodedStep_equiv h.equiv size (.scalar op d a b c)
    rw [hstep] at hrel
    cases hp : decodedStep concDom size ep (.scalar op d a b c) with
    | none => rw [hp] at hrel; exact absurd hrel id
    | some ep₁ =>
      rw [hp] at hrel
      have hrun : eval concDom size [op.instr d a b c] ep=some ep₁ := by
        rw [eval_single]; simp only [step]
        cases op <;> exact hp
      by_cases hmz : ∃ n,op=.movz 0 n
      · obtain ⟨n,rfl⟩ := hmz
        have hy0 : y.1=0 := by rw [hyv]; exact movz_zero _ _ _ _ _ _
        have hval : y.1=upd ρ (s.2.2.2+1) y.1 0 := by rw [upd_lt _ (by omega_arith),h.zero,hy0]
        by_cases hl : s.1.lookup d=some 0
        · refine ⟨[],upd ρ (s.2.2.2+1) y.1,ep,?_,rfl,?_⟩
          · rw [Decoded.instr,fwdStep_movz]; simp [hl]
          · refine write_inv h hsl hrg hy hval (by omega_arith) ⟨fun r => ?_,fun o => ?_,?_⟩
            · by_cases hr : r=d
              · subst hr
                obtain ⟨x,hx,hx'⟩ := h.regs _ (mem_of_lookup hl)
                have := h.equiv.reg r
                rw [hx] at this
                cases hq : ep.reg r with
                | none => rw [hq] at this; cases this
                | some z =>
                  rw [hq] at this
                  simp only [Option.map_some,Option.some.injEq] at this
                  rw [hy,Option.map_some,Option.map_some,hy0,← this,hx',h.zero]
              · rw [hrg r hr]; exact h.equiv.reg r
            · rw [hsl]; exact h.equiv.slot o
            · rw [hcar rfl]; exact h.equiv.carry
        · refine ⟨[(Op.movz 0 n).instr d a b c],upd ρ (s.2.2.2+1) y.1,ep₁,?_,hrun,?_⟩
          · rw [Decoded.instr,fwdStep_movz]; simp [hl]
          · exact write_inv h hsl hrg hy hval (by omega_arith) hrel
      · have hop : ∀ n,op≠.movz 0 n := fun n he => hmz ⟨n,he⟩
        refine ⟨[op.instr d a b c],upd ρ (s.2.2.2+1) y.1,ep₁,?_,hrun,?_⟩
        · simp [Decoded.instr,fwdStep_scalar s hop]
        · simp only [Decoded.instr,fwdStep_scalar s hop]
          exact write_inv h hsl hrg hy (upd_self _ _ _).symm (Nat.le_refl _) hrel

theorem fwd_fold (is : List Instr) : ∀ {ρ : Nat → BitVec 64} {s : FState} {eo ep l : Env CVal},
    FInv ρ s eo ep → eval concDom size is eo=some l →
    ∃ em ρ' ep',(is.foldl (fun s i => fwdStep i s) s).2.2.1=em.reverse ++ s.2.2.1 ∧
      eval concDom size em ep=some ep' ∧ FInv ρ' (is.foldl (fun s i => fwdStep i s) s) l ep' := by
  induction is with
  | nil =>
    intro ρ s eo ep l h hl
    cases hl
    exact ⟨[],ρ,ep,rfl,rfl,h⟩
  | cons i is ih =>
    intro ρ s eo ep l h hl
    simp only [eval] at hl
    cases hs : step concDom size eo i with
    | none => rw [hs] at hl; cases hl
    | some eo₁ =>
      rw [hs] at hl
      obtain ⟨em₁,ρ₁,ep₁,ho₁,he₁,h₁⟩ := fwd_step h hs
      obtain ⟨em₂,ρ₂,ep₂,ho₂,he₂,h₂⟩ := ih h₁ hl
      refine ⟨em₁ ++ em₂,ρ₂,ep₂,?_,?_,h₂⟩
      · rw [List.foldl_cons,ho₂,ho₁,List.reverse_append,List.append_assoc]
      · rw [eval_append,he₁]; exact he₂

/-- `forward` keeps the words a block leaves, for every block the interpreter runs. -/
theorem forward_ok {is : List Instr} {e l : Env CVal} (h : eval concDom size is e=some l) :
    ∃ r,eval concDom size (forward is) e=some r ∧ Equiv l r := by
  have h₀ : FInv (fun _ => 0) ([],[],[],1) e e :=
    ⟨Equiv.refl e,rfl,fun _ h => (by simp at h),fun _ h => (by simp at h),fun _ h => (by simp at h),
      fun _ h => (by simp at h),Nat.le_refl 1⟩
  obtain ⟨em,_,ep,ho,he,hf⟩ := fwd_fold is h₀ h
  refine ⟨ep,?_,hf.equiv⟩
  rw [forward_eq_fwd,ho,List.append_nil,List.reverse_reverse]
  exact he

end VG.Proof.Weierstrass.AArch64.Forward
