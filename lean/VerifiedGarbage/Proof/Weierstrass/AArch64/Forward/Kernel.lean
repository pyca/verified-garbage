import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Checked
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AllBelow
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.OptimizeK

/-! Kernel-evaluated twins of the certificate checks. The kernel reduces a
recursor (`Tree.rec`, `List.rec`, `Nat.rec`) directly, several times faster
than the `brecOn` encoding of structural recursion, the matchers of `do`
blocks and derived `DecidableEq` instances (and a `decide` over `Fin n` is
quadratic in `n`: see `Framework/AllBelow.lean`). Each twin is proved equal to
(or to imply) the definition it replaces, so the certificate's statements are
unchanged; the twins are only ever evaluated by the kernel. -/

namespace VG.Proof.Weierstrass.AArch64.Forward
open VG VG.AArch64

variable {α : Type}

private theorem rec_none_eq_bind {β γ : Type} (x : Option β) (g : β → Option γ) :
    Option.rec (motive := fun _ => Option γ) none g x=x.bind g := by cases x <;> rfl

private theorem bool_rec_eq {β : Type} (x y : β) (b : Bool) :
    Bool.rec (motive := fun _ => β) x y b=if b=true then y else x := by cases b <;> rfl

private theorem beq_dec (x y : Nat) : Nat.beq x y=decide (x=y) :=
  Bool.eq_iff_iff.mpr (by simp [Nat.beq_eq])

private theorem ble_dec (x y : Nat) : Nat.ble x y=decide (x≤y) :=
  Bool.eq_iff_iff.mpr (by simp [Nat.ble_eq])

private theorem blt_dec (x y : Nat) : Nat.blt x y=decide (x<y) :=
  Bool.eq_iff_iff.mpr (by simp [Nat.blt_eq])

/-- The kernel reduces `Nat.ble` natively; `Nat.blt` unfolds to it. -/
private theorem ble_blt {β : Type} (x y : β) (key k : Nat) :
    Bool.rec (motive := fun _ => β) x y (Nat.ble k key)=Bool.rec y x (Nat.blt key k) := by
  rw [ble_dec,blt_dec]
  by_cases h : key<k
  · have : ¬k≤key := by omega
    simp [h,this]
  · have : k≤key := by omega
    simp [h,this]

namespace Tree

noncomputable def lookupK (key : Nat) (t : Tree α) : Option α :=
  Tree.rec (motive := fun _ => Option α) none
    (fun k v _ _ l r => Bool.rec (Bool.rec l r (Nat.ble k key)) (some v) (Nat.beq key k)) t

theorem lookupK_eq (key : Nat) (t : Tree α) : lookupK key t=lookup key t := by
  induction t with
  | empty => rfl
  | node k v l r ihl ihr =>
    rw [lookup,← ihl,← ihr]
    change Bool.rec (motive := fun _ => Option α) (Bool.rec (lookupK key l) (lookupK key r) (Nat.ble k key))
      (some v) (Nat.beq key k)=_
    rw [ble_blt]
    cases Nat.beq key k <;> cases Nat.blt key k <;> rfl

noncomputable def insertK (key : Nat) (value : α) (t : Tree α) : Tree α :=
  Tree.rec (motive := fun _ => Tree α) (.node key value .empty .empty)
    (fun k v l r il ir => Bool.rec (Bool.rec (.node k v il r) (.node k v l ir) (Nat.ble k key))
      (.node k value l r) (Nat.beq key k)) t

theorem insertK_eq (key : Nat) (value : α) (t : Tree α) : insertK key value t=insert key value t := by
  induction t with
  | empty => rfl
  | node k v l r ihl ihr =>
    rw [insert,← ihl,← ihr]
    change Bool.rec (motive := fun _ => Tree α) (Bool.rec (.node k v (insertK key value l) r)
      (.node k v l (insertK key value r)) (Nat.ble k key)) (.node k value l r) (Nat.beq key k)=_
    rw [ble_blt]
    cases Nat.beq key k <;> cases Nat.blt key k <;> rfl

noncomputable def allK (P : Nat → α → Bool) (t : Tree α) : Bool :=
  Tree.rec (motive := fun _ => Bool) true
    (fun k v _ _ l r => Bool.rec false (Bool.rec false r l) (P k v)) t

theorem allK_eq (P : Nat → α → Bool) (t : Tree α) : allK P t=all P t := by
  induction t with
  | empty => rfl
  | node k v l r ihl ihr =>
    rw [all,← ihl,← ihr]
    change Bool.rec (motive := fun _ => Bool) false (Bool.rec false (allK P r) (allK P l)) (P k v)=_
    cases P k v <;> cases allK P l <;> rfl

end Tree

/-- An injective code of an operation, by `Op.rec`. -/
noncomputable def Op.codeK (op : Op) : Nat :=
  Op.rec 0 1 2 3 4 5 6 7 8 (fun o => LogicOp.rec 9 10 11 o) 12 13 14
    (fun n => 15+32*n) (fun n => 16+32*n) (fun n => 17+32*n)
    (fun v n => 18+32*(v.toNat+65536*n)) (fun v n => 19+32*(v.toNat+65536*n)) op

private def Op.ofCode (c : Nat) : Op :=
  let p := c/32
  match c%32 with
  | 0 => .add | 1 => .sub | 2 => .adds | 3 => .adcs | 4 => .subs | 5 => .sbcs
  | 6 => .adc | 7 => .sbc | 8 => .csel
  | 9 => .logic .and | 10 => .logic .orr | 11 => .logic .eor
  | 12 => .mul | 13 => .umulh | 14 => .madd
  | 15 => .lsl p | 16 => .lsr p | 17 => .extr p
  | 18 => .movz (BitVec.ofNat 16 (p%65536)) (p/65536)
  | _ => .movk (BitVec.ofNat 16 (p%65536)) (p/65536)

private theorem Op.ofCode_codeK (op : Op) : Op.ofCode op.codeK=op := by
  cases op with
  | logic o => cases o <;> rfl
  | lsl n | lsr n | extr n =>
    simp only [Op.codeK,Op.ofCode]
    rw [show (_+32*n)%32=_ from Nat.add_mul_mod_self_left _ 32 n]
    simp only []
    rw [show (_+32*n)/32=n by omega]
  | movz v n | movk v n =>
    have hv := v.isLt
    simp only [Op.codeK,Op.ofCode]
    rw [show (_+32*(v.toNat+65536*n))%32=_ from Nat.add_mul_mod_self_left _ 32 _]
    simp only []
    rw [show (_+32*(v.toNat+65536*n))/32=v.toNat+65536*n by omega,
      show (v.toNat+65536*n)%65536=v.toNat by omega,
      show (v.toNat+65536*n)/65536=n by omega,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  | _ => rfl

theorem Op.beq_codeK (a b : Op) : Nat.beq a.codeK b.codeK=decide (a=b) := by
  by_cases h : a=b
  · subst h; simp
  · have : a.codeK≠b.codeK := fun he => h (by rw [← Op.ofCode_codeK a,he,Op.ofCode_codeK])
    rw [decide_eq_false h]
    cases hb : Nat.beq a.codeK b.codeK
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) this

/-- `findNode` of an application, comparing operations by their codes. -/
noncomputable def findAppK (nodes : Certificate) (op : Op) (a b c d f : Nat) : Option Nat :=
  Option.rec none (fun i => Option.rec none (fun value =>
      Node.rec (motive := fun _ => Option Nat) none (fun _ => none)
        (fun op' a' b' c' d' f' => Bool.rec none (some i)
          (Nat.beq op'.codeK op.codeK && Nat.beq a' a && Nat.beq b' b && Nat.beq c' c &&
            Nat.beq d' d && Nat.beq f' f)) value)
      (nodes.nodes.lookupK i))
    (nodes.hints.lookupK (Node.app op a b c d f).key)

theorem findAppK_eq (nodes : Certificate) (op : Op) (a b c d f : Nat) :
    findAppK nodes op a b c d f=findNode nodes (.app op a b c d f) := by
  unfold findAppK findNode
  rw [Tree.lookupK_eq]
  cases nodes.hints.lookup (Node.app op a b c d f).key with
  | none => rfl
  | some i =>
    simp only []
    rw [Tree.lookupK_eq]
    cases nodes.nodes.lookup i with
    | none => rfl
    | some value =>
      simp only []
      cases value with
      | app op' a' b' c' d' f' =>
        simp only [Node.eqB,Op.beq_codeK]
        cases decide (op'=op) && Nat.beq a' a && Nat.beq b' b && Nat.beq c' c &&
          Nat.beq d' d && Nat.beq f' f <;> rfl
      | _ => rfl

/-- `certDom`, evaluated by recursors. -/
noncomputable def certDomK (nodes : Certificate) : Dom Nat where
  zero := 0
  applyOp op a b c d f :=
    Bool.rec (findAppK nodes op a b c d f) (some a) (Nat.beq op.codeK 10 && Nat.beq a b)

theorem certDomK_eq (nodes : Certificate) : certDomK nodes=certDom nodes := by
  unfold certDomK certDom
  congr
  funext op a b c d f
  have h10 : Nat.beq op.codeK 10=decide (op=.logic .orr) := Op.beq_codeK op (.logic .orr)
  rw [h10,findAppK_eq,bool_rec_eq,beq_dec]
  by_cases ho : op=.logic .orr <;> by_cases hab : a=b <;> simp [ho,hab]

/-- `regKey`, by `Reg.rec`. -/
noncomputable def regKeyK (r : Reg) : Nat :=
  Reg.rec 0 16 8 24 4 20 12 28 2 18 10 26 6 22 14 30 1 17 9 25 5 21 13 29 3 19 11 27 7 r

theorem regKeyK_eq (r : Reg) : regKeyK r=regKey r := by cases r <;> rfl

namespace FastEnv

noncomputable def regK (e : FastEnv α) (r : Reg) : Option α :=
  Option.rec (e.initial.reg r) some (e.regs.lookupK (regKeyK r))

noncomputable def argK (D : Dom α) (e : FastEnv α) (use : Bool) (r : Reg) : Option α :=
  Bool.rec (some D.zero) (e.regK r) use

noncomputable def okOff (size off : Nat) : Bool :=
  Nat.beq (off%8) 0 && Nat.ble (off+8) size && Nat.blt off 32768

theorem argK_eq (D : Dom α) (e : FastEnv α) (use : Bool) (r : Reg) :
    argK D e use r=arg D e.toEnv use r := by
  unfold argK arg regK
  cases use
  · rfl
  · change Option.rec (motive := fun _ => Option α) _ some (e.regs.lookupK (regKeyK r))=
      (e.regs.lookup (regKey r)).orElse fun _ => e.initial.reg r
    rw [Tree.lookupK_eq,regKeyK_eq]
    cases e.regs.lookup (regKey r) <;> rfl

theorem okOff_eq (size off : Nat) :
    okOff size off=(off%8=0 && off+8≤size && off<32768 : Bool) := by
  simp only [okOff,beq_dec,ble_dec,blt_dec]

theorem x0_key (d : Reg) : Nat.beq (regKey d) 0=decide (d=.x0) := by cases d <;> rfl

/-- The carry after an operation. A definition, not a recursor, so the kernel
reads a long chain of carries iteratively (its `whnf` unfolds definitions in a
loop but reduces nested recursors recursively). -/
noncomputable def carryK (flags : Bool) (vr : α) (c : Option α) : Option α :=
  Bool.rec c (some vr) flags

/-- `decodedStep`, evaluated by recursors. -/
noncomputable def stepK (D : Dom α) (size : Nat) (e : FastEnv α) (i : Decoded) : Option (FastEnv α) :=
  Decoded.rec
    (fun op d a b c => Bool.rec
      (Option.rec none (fun va => Option.rec none (fun vb => Option.rec none (fun vc =>
        Option.rec none (fun vd => Option.rec none (fun cf => Option.rec none (fun vr =>
          some ⟨e.initial,e.regs.insertK (regKeyK d) vr,e.slots,carryK op.flags vr e.carry⟩)
          (D.applyOp op va vb vc vd cf))
          (Bool.rec (some D.zero) e.carry op.useCarry))
          (argK D e op.useD d)) (argK D e op.useC c)) (argK D e op.useB b)) (argK D e op.useA a))
      none (Nat.beq (regKeyK d) 0 || !op.valid))
    (fun d off => Bool.rec none
      (some ⟨e.initial,e.regs.insertK (regKeyK d)
        (Option.rec (e.initial.slot off) (fun v => v) (e.slots.lookupK off)),e.slots,e.carry⟩)
      (!Nat.beq (regKeyK d) 0 && okOff size off))
    (fun r off => Bool.rec none
      (Option.rec none (fun v => some ⟨e.initial,e.regs,e.slots.insertK off v,e.carry⟩) (e.regK r))
      (okOff size off)) i

theorem regK_eq (e : FastEnv α) (r : Reg) : e.regK r=e.toEnv.reg r := by
  unfold regK
  change _=(e.regs.lookup (regKey r)).orElse fun _ => e.initial.reg r
  rw [Tree.lookupK_eq,regKeyK_eq]
  cases e.regs.lookup (regKey r) <;> rfl

private theorem slot_eq (e : FastEnv α) (off : Nat) :
    Option.rec (motive := fun _ => α) (e.initial.slot off) (fun v => v) (e.slots.lookupK off)=
      e.toEnv.slot off := by
  rw [Tree.lookupK_eq]
  change _=(e.slots.lookup off).getD (e.initial.slot off)
  cases e.slots.lookup off <;> rfl

theorem stepK_eq (D : Dom α) (size : Nat) (e : FastEnv α) (i : Decoded) :
    stepK D size e i=decodedStep D size e i := by
  have hc : e.toEnv.carry=e.carry := rfl
  cases i with
  | scalar => simp only [stepK,decodedStep,rec_none_eq_bind,bool_rec_eq,x0_key,argK_eq,carryK,
      carryArg,hc,bind,pure,setReg,withCarry,Tree.insertK_eq,regKeyK_eq]
  | load d off =>
    simp only [stepK,decodedStep,bool_rec_eq,x0_key,okOff_eq,slot_eq,setReg,Tree.insertK_eq,
      regKeyK_eq]
    generalize (decide (off%8=0) && decide (off+8≤size) && decide (off<32768))=ok
    cases decide (d=.x0) <;> cases ok <;> rfl
  | store r off =>
    simp only [stepK,decodedStep,rec_none_eq_bind,bool_rec_eq,okOff_eq,regK_eq]
    generalize (decide (off%8=0) && decide (off+8≤size) && decide (off<32768))=ok
    cases ok <;> try rfl
    simp only [↓reduceIte,Bool.not_true,Bool.false_eq_true]
    cases e.toEnv.reg r <;> simp [setSlot,Tree.insertK_eq]

/-- One instruction, then the rest (`k`). A definition, so the kernel takes
each instruction in its iterative loop rather than nesting recursors. -/
noncomputable def stepThen (D : Dom α) (size : Nat) (e : FastEnv α) (i : Instr)
    (k : FastEnv α → Option (FastEnv α)) : Option (FastEnv α) :=
  Option.rec none (fun v => Option.rec none k (stepK D size e v.val)) (decode i)

/-- `FastEnv.eval`, evaluated by recursors. -/
noncomputable def evalK (D : Dom α) (size : Nat) (is : List Instr) (e : FastEnv α) : Option (FastEnv α) :=
  List.rec (motive := fun _ => FastEnv α → Option (FastEnv α)) some
    (fun i _ ih e => stepThen D size e i ih) is e

theorem evalK_eq (D : Dom α) (size : Nat) (is : List Instr) (e : FastEnv α) :
    evalK D size is e=eval D size is e := by
  induction is generalizing e with
  | nil => rfl
  | cons i is ih =>
    change Option.rec (motive := fun _ => Option (FastEnv α)) none
      (fun v => Option.rec none (evalK D size is) (stepK D size e v.val)) (decode i)=_
    simp only [eval,step,bind,Option.bind]
    cases decode i with
    | none => rfl
    | some v =>
      simp only [stepK_eq]
      cases decodedStep D size e v.val with
      | none => rfl
      | some e' => exact ih e'

end FastEnv

/-- The finite part of an evaluation of the certificate's domain, by recursors. -/
noncomputable def evalDataK (nodes : Certificate) (size : Nat) (is : List Instr) (e : Env Nat) :
    Option (Tree Nat × Tree Nat × Option Nat) :=
  Option.rec none (fun f => some (FastEnv.data f))
    (FastEnv.evalK (certDomK nodes) size is (FastEnv.ofEnv e))

theorem eval_of_dataK {nodes : Certificate} {size : Nat} {is : List Instr} {e : Env Nat}
    {d : Tree Nat × Tree Nat × Option Nat} (h : evalDataK nodes size is e=some d) :
    eval (certDom nodes) size is e=some (fromData e d) := by
  apply eval_of_data
  unfold evalDataK at h
  rw [FastEnv.evalK_eq,certDomK_eq] at h
  unfold evalData
  revert h
  cases FastEnv.eval (certDom nodes) size is (FastEnv.ofEnv e) <;> intro h <;> cases h <;> rfl

/-- Every node is an input, the zero or an application of earlier nodes. -/
noncomputable def validK (nodes : Certificate) : Bool :=
  Option.rec false (fun n => Node.rec (motive := fun _ => Bool) true (fun _ => false)
      (fun _ _ _ _ _ _ => false) n) (nodes.nodes.lookupK 0) &&
    nodes.nodes.allK (fun i n => Node.rec (motive := fun _ => Bool) true (fun _ => true)
      (fun _ a b c d f => Nat.blt a i && Nat.blt b i && Nat.blt c i && Nat.blt d i &&
        Nat.blt f i) n)

theorem valid_of_validK {nodes : Certificate} (h : validK nodes=true) : CertValid nodes := by
  unfold validK at h
  rw [Bool.and_eq_true,Tree.lookupK_eq,Tree.allK_eq] at h
  obtain ⟨h0,ha⟩ := h
  refine ⟨?_,?_⟩
  · revert h0
    cases nodes.nodes.lookup 0 with
    | none => intro h; cases h
    | some n => cases n <;> intro h <;> first | rfl | cases h
  · rw [← ha]
    congr
    funext i n
    cases n with
    | app => exact Bool.eq_iff_iff.mpr (by simp [Node.before,Nat.blt_eq,and_assoc]; exact decide_eq_true_iff)
    | _ => rfl

/-- Word `i` of the certificate's extent is input `i+1`. -/
noncomputable def inputK (nodes : Certificate) (i : Nat) : Bool :=
  Option.rec false (fun n => Node.rec (motive := fun _ => Bool) false (fun off => Nat.beq off (8*i))
    (fun _ _ _ _ _ _ => false) n) (nodes.nodes.lookupK (i+1))

theorem inputs_of_allBelow {nodes : Certificate} {size : Nat}
    (h : allBelow (inputK nodes) (size/8)=true) : Inputs nodes size := by
  intro off ha hb
  have hi := of_allBelow h (off/8) (by omega)
  unfold inputK at hi
  rw [Tree.lookupK_eq] at hi
  have ho : 8*(off/8)=off := by omega
  revert hi
  cases nodes.nodes.lookup (off/8+1) with
  | none => intro h; cases h
  | some n =>
    cases n with
    | input o =>
      intro h
      have : o=8*(off/8) := Nat.eq_of_beq_eq_true h
      rw [this,ho]
    | _ => intro h; cases h

/-- The value of slot `off` of the finite part of an evaluation from `e`. -/
noncomputable def slotK (e : Env Nat) (d : Tree Nat × Tree Nat × Option Nat) (off : Nat) : Nat :=
  Option.rec (e.slot off) (fun v => v) (d.2.1.lookupK off)

theorem slotK_eq (e : Env Nat) (d : Tree Nat × Tree Nat × Option Nat) (off : Nat) :
    slotK e d off=(fromData e d).slot off := by
  unfold slotK
  rw [Tree.lookupK_eq]
  change _=(d.2.1.lookup off).getD (e.slot off)
  cases d.2.1.lookup off <;> rfl

/-- Both finite parts agree on every observed slot either one stores. -/
noncomputable def sameK (observe : Nat → Bool) (e : Env Nat) (l r : Tree Nat × Tree Nat × Option Nat) :
    Bool :=
  l.2.1.allK (fun off v => !observe off || Nat.beq v (slotK e r off)) &&
    r.2.1.allK (fun off v => !observe off || Nat.beq v (slotK e l off))

/-- Both evaluations agree on every observed slot. -/
theorem same_of_sameK {e : Env Nat} {l r : Tree Nat × Tree Nat × Option Nat}
    (observe : Nat → Prop) [DecidablePred observe]
    (h : sameK (fun off => decide (observe off)) e l r=true) :
    ∀ off,observe off → (fromData e l).slot off=(fromData e r).slot off := by
  intro off hv
  rw [sameK,Bool.and_eq_true,Tree.allK_eq,Tree.allK_eq] at h
  have hs (d : Tree Nat × Tree Nat × Option Nat) :
      slotK e d off=(d.2.1.lookup off).getD (e.slot off) := by
    rw [slotK_eq]; rfl
  rw [← slotK_eq,← slotK_eq,hs,hs]
  cases hl : l.2.1.lookup off with
  | some v =>
    have := Tree.lookup_all h.1 hl
    simp only [hv,decide_true,Bool.not_true,Bool.false_or,hs,Nat.beq_eq] at this
    exact this
  | none =>
    cases hr : r.2.1.lookup off with
    | some w =>
      have := Tree.lookup_all h.2 hr
      simp only [hv,decide_true,Bool.not_true,Bool.false_or,hs,Nat.beq_eq,hl] at this
      exact this.symm
    | none => rfl

/-- `p a` for every `a ∈ l`, by the kernel's `List.rec`. -/
noncomputable def listAllK {β : Type} (p : β → Bool) (l : List β) : Bool :=
  List.rec true (fun a _ r => p a && r) l

theorem of_listAllK {β : Type} {p : β → Bool} {l : List β} (h : listAllK p l=true) :
    ∀ a∈l,p a=true := by
  induction l with
  | nil => intro a ha; cases ha
  | cons b l ih =>
    have h' : (p b && listAllK p l)=true := h
    rw [Bool.and_eq_true] at h'
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact h'.1
    · exact ih h'.2 a ha

theorem bound_of_listAllK {is : List Instr} {cap : Nat}
    (h : listAllK (fun i => Nat.ble (instrBound i) cap) is=true) : ∀ i∈is,instrBound i≤cap :=
  fun i hi => Nat.le_of_ble_eq_true (of_listAllK h i hi)

/-- One decoding of `i` checks all three: its bound is at most `cap`, the
register it writes is in `regs` and the word it stores is inside `work`. -/
noncomputable def instrOkK (cap : Nat) (regs : RegSet Reg) (work : List (Nat × Nat)) (i : Instr) : Bool :=
  Option.rec true (fun v => Decoded.rec (motive := fun _ => Bool)
      (fun _ d _ _ _ => regs.mem d)
      (fun d off => Nat.ble (off+8) cap && regs.mem d)
      (fun _ off => Nat.ble (off+8) cap &&
        work.any fun w' => Nat.ble w'.1 off && Nat.ble (off+8) (w'.1+w'.2)) v.val)
    (decode i)

private theorem of_instrOkK {cap : Nat} {regs : RegSet Reg} {work : List (Nat × Nat)} {i : Instr}
    (h : instrOkK cap regs work i=true) :
    instrBound i≤cap ∧ (∀ r∈instrClob i,regs.mem r=true) ∧
      ∀ w∈instrWrites i,∃ w'∈work,w'.1≤w.1 ∧ w.1+w.2≤w'.1+w'.2 := by
  unfold instrOkK at h
  unfold instrBound instrClob instrWrites
  revert h
  cases decode i with
  | none => intro _; exact ⟨Nat.zero_le _,by simp,by simp⟩
  | some v =>
    rcases v with ⟨v,_⟩
    cases v with
    | scalar op d a b c =>
      intro h
      exact ⟨Nat.zero_le _,by simpa [Decoded.clob] using h,by simp [Decoded.writes]⟩
    | load d off =>
      intro h
      change (Nat.ble (off+8) cap && regs.mem d)=true at h
      rw [Bool.and_eq_true] at h
      exact ⟨Nat.le_of_ble_eq_true h.1,by simpa [Decoded.clob] using h.2,by simp [Decoded.writes]⟩
    | store r off =>
      intro h
      change (Nat.ble (off+8) cap && work.any fun w' => Nat.ble w'.1 off &&
        Nat.ble (off+8) (w'.1+w'.2))=true at h
      rw [Bool.and_eq_true] at h
      refine ⟨Nat.le_of_ble_eq_true h.1,by simp [Decoded.clob],?_⟩
      intro w hw
      simp only [Decoded.writes,List.mem_singleton] at hw
      subst hw
      obtain ⟨w',hw',hc⟩ := List.any_eq_true.mp h.2
      rw [Bool.and_eq_true] at hc
      exact ⟨w',hw',Nat.le_of_ble_eq_true hc.1,Nat.le_of_ble_eq_true hc.2⟩

theorem bound_of_instrOk {cap : Nat} {regs : RegSet Reg} {work : List (Nat × Nat)} {is : List Instr}
    (h : listAllK (instrOkK cap regs work) is=true) : ∀ i∈is,instrBound i≤cap :=
  fun i hi => (of_instrOkK (of_listAllK h i hi)).1

theorem clob_of_instrOk {cap : Nat} {regs : List Reg} {work : List (Nat × Nat)} {is : List Instr}
    (h : listAllK (instrOkK cap (RegSet.ofList regs) work) is=true) :
    ∀ r∈is.flatMap instrClob,r∈regs := by
  intro r hr
  obtain ⟨i,hi,hr⟩ := List.mem_flatMap.mp hr
  exact RegSet.mem_ofList.mp ((of_instrOkK (of_listAllK h i hi)).2.1 r hr)

theorem cover_of_instrOk {cap : Nat} {regs : RegSet Reg} {work : List (Nat × Nat)} {is : List Instr}
    (h : listAllK (instrOkK cap regs work) is=true) :
    ∀ w∈is.flatMap instrWrites,∃ w'∈work,w'.1≤w.1 ∧ w.1+w.2≤w'.1+w'.2 := by
  intro w hw
  obtain ⟨i,hi,hw⟩ := List.mem_flatMap.mp hw
  exact (of_instrOkK (of_listAllK h i hi)).2.2 w hw

/-- A store's word ends at its bound. -/
theorem writes_of_bound {is : List Instr} {cap : Nat} (h : ∀ i∈is,instrBound i≤cap) :
    ∀ w∈is.flatMap instrWrites,w.1+w.2≤cap := by
  intro w hw
  obtain ⟨i,hi,hw⟩ := List.mem_flatMap.mp hw
  refine Nat.le_trans ?_ (h i hi)
  unfold instrWrites at hw
  unfold instrBound
  revert hw
  cases decode i with
  | none => intro hw; cases hw
  | some v =>
    rcases v with ⟨v,_⟩
    cases v <;> simp [Decoded.writes,Decoded.bound]
    intro hw; subst hw; exact Nat.le_refl _

end VG.Proof.Weierstrass.AArch64.Forward
