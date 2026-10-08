import VerifiedGarbage.Impl.Weierstrass.X86_64.ForwardField
import VerifiedGarbage.Proof.Weierstrass.X86_64.ForwardStores
import VerifiedGarbage.Proof.Weierstrass.X86_64.Double4
import VerifiedGarbage.Proof.Weierstrass.X86_64.Blocks

/-! The forwarded program preserves field values, memory frames and its output cache. -/
namespace VG.Proof.Weierstrass.X86_64.ForwardField
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64
open VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass.X86_64.ForwardField
open VG.Proof.Mont VG.Proof.Mont.X86_64

theorem code_stores {M : Mod} (hn : M.n=4) (op : FOp) :
    ∃ is,code M op=is++stores (outputRegs M op) op.out := by
  cases op with
  | mul o a b =>
    simp only [code,opCode,mul,hn,show 4<7 from by decide,↓reduceIte,mulR,outputRegs,FOp.out]
    rcases prodK? M with _ | k
    · simp only [Nat.reduceEqDiff, false_and, and_false, ↓reduceIte]
      exact ⟨_,rfl⟩
    · dsimp only
      obtain ⟨X, hX⟩ : ∃ X, redRX M k o = X ++ stores sqLow o := ⟨_, rfl⟩
      split
      · exact ⟨_, by rw [sqrRX, hX, ← List.append_assoc]⟩
      · exact ⟨_, by rw [mulRX, hX, ← List.append_assoc]⟩
  | add o a b =>
    simp only [code,outputRegs,FOp.out]
    split
    · exact ⟨_,rfl⟩
    · simp only [opCode,add,hn,show 4<7 from by decide,↓reduceIte,addR]
      exact ⟨_,rfl⟩
  | sub o a b =>
    simp only [code,opCode,sub,outputRegs,FOp.out]
    split
    · exact ⟨_,rfl⟩
    · simp only [hn,show 4<7 from by decide,Nat.reduceEqDiff,and_false,↓reduceIte,subR]
      exact ⟨_,rfl⟩

theorem outputRegs_length {M : Mod} (hn : M.n=4) (op : FOp) :
    (outputRegs M op).length=4 := by
  cases op with
  | mul o a b => simp only [outputRegs]; split <;> simp [hn,sqLow]
  | add o a b => rfl
  | sub o a b => rfl

theorem outputRegs_nodup {M : Mod} (hn : M.n=4) (op : FOp) :
    (outputRegs M op).Nodup := by
  cases op with
  | mul o a b =>
    simp only [outputRegs]
    split
    · change ([.r12,.r13,.r14,.r15] : List Reg).Nodup
      decide
    · rw [hn]
      decide
  | add o a b => change ([.r8,.r9,.r10,.r11] : List Reg).Nodup; decide
  | sub o a b => change ([.r8,.r9,.r10,.r11] : List Reg).Nodup; decide

theorem code_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}
    (hL : Lay M size Sl) (hm : UnitMod m (2^(64*M.n)))
    {V : List Nat} {E : Nat → Fin m} {s : State} (hI : Inv M base size m Sl V E s)
    {op : FOp} (hS : ∀ x∈op.out::op.ins,Sl x) (hR : ∀ x∈op.ins,x∈V) :
    WP isa (.block (code M op)) s fun t =>
      OpKeep M base op.out s t ∧ Inv M base size m Sl (op.out::V) (op.run E) t := by
  cases op with
  | mul o a b => exact fop_ok hL hm hI hS hR
  | sub o a b => exact fop_ok hL hm hI hS hR
  | add o a b =>
    simp only [code]
    split
    · rename_i hab
      obtain ⟨rfl,hn⟩ := hab
      exact double4_inv_ok hn hL hI (hS _ (by simp [FOp.out])) (hR _ (by simp [FOp.ins]))
    · exact fop_ok hL hm hI hS hR

theorem step_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}
    (hn : M.n=4) (hL : Lay M size Sl) (hm : UnitMod m (2^(64*M.n)))
    {V : List Nat} {E : Nat → Fin m} {s : State} (hI : Inv M base size m Sl V E s)
    {op : FOp} (hS : ∀ x∈op.out::op.ins,Sl x) (hR : ∀ x∈op.ins,x∈V)
    {cs : Forward.Cache} (hc : Forward.Valid cs s) :
    WP isa (.block (Forward.block cs (code M op))) s fun t =>
      (OpKeep M base op.out s t ∧ Inv M base size m Sl (op.out::V) (op.run E) t) ∧
      Forward.Valid (outputCache M op) t := by
  apply Forward.block_wp hc
  obtain ⟨is,he⟩ := code_stores hn op
  have h := code_ok hL hm hI hS hR
  rw [he] at h ⊢
  apply Forward.block_stores_valid h (fun _ ht => ht.2.scr)
  · rw [outputRegs_length hn]
    have hle := hL.le op.out (hS _ (List.mem_cons_self ..))
    simpa only [hn] using hle
  · exact outputRegs_nodup hn op

theorem program_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}
    (hn : M.n=4) (hL : Lay M size Sl) (hm : UnitMod m (2^(64*M.n)))
    (ops : List FOp) {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) (hS : ∀ op∈ops,∀ x∈op.out::op.ins,Sl x)
    (hR : readsOk ops V=true) {cs : Forward.Cache} (hc : Forward.Valid cs s) :
    WP isa (program M cs ops) s fun t =>
      ProgKeep M base (ops.map FOp.out) s t ∧
      Inv M base size m Sl (validAfter ops V) (runOps ops E) t ∧
      Forward.Valid (lastCache M cs ops) t := by
  unfold program
  apply (blocks_wp _).mpr
  induction ops generalizing V E s cs with
  | nil => exact WP.block_nil ⟨ProgKeep.refl _ _ _ s,hI,hc⟩
  | cons op ops ih =>
    simp only [codes,List.flatten_cons]
    apply WP.block_append
    simp only [readsOk,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at hR
    refine WP.mono (step_ok hn hL hm hI (hS op (List.mem_cons_self ..)) hR.1 hc)
      fun u ⟨⟨ku,hu⟩,hcu⟩ => ?_
    refine WP.mono (ih hu (fun op' hop => hS op' (List.mem_cons_of_mem _ hop)) hR.2 hcu)
      fun t ⟨kt,ht,hct⟩ => ?_
    refine ⟨⟨fun r hr => (kt.gpr r hr).trans (ku.gpr r hr),kt.rd.trans ku.rd,
      kt.wr.trans ku.wr,fun x hx htmp => ?_⟩,ht,hct⟩
    rw [List.map_cons] at hx
    rw [kt.mem x (fun w hw => hx w (List.mem_cons_of_mem _ hw)) htmp,
      ku.mem x (hx _ (List.mem_cons_self ..)) htmp]

/-- One operation of `programB`'s plain form: a call where `opCall?` makes
one, else `code`. -/
theorem plainOp_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}
    (hL : Lay M size Sl) (hm : UnitMod m (2^(64*M.n)))
    {V : List Nat} {E : Nat → Fin m} {s : State} (hI : Inv M base size m Sl V E s)
    {op : FOp} (hS : ∀ x∈op.out::op.ins,Sl x) (hR : ∀ x∈op.ins,x∈V) :
    WP isa ((opCall? M op).getD (.block (code M op))).inline s fun t =>
      OpKeep M base op.out s t ∧ Inv M base size m Sl (op.out::V) (op.run E) t := by
  cases h : opCall? M op with
  | none => exact code_ok hL hm hI hS hR
  | some p =>
    have := opProg_ok hL hm hI hS hR
    simp only [opProg, h, Option.getD_some] at this ⊢
    exact this

theorem plain_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}
    (hL : Lay M size Sl) (hm : UnitMod m (2^(64*M.n))) :
    ∀ (ops : List FOp) {V : List Nat} {E : Nat → Fin m} {s : State},
      Inv M base size m Sl V E s → (∀ op∈ops,∀ x∈op.out::op.ins,Sl x) → readsOk ops V=true →
      WP isa (progs (ops.map fun op => (opCall? M op).getD (.block (code M op)))).inline s fun t =>
        ProgKeep M base (ops.map FOp.out) s t ∧
        Inv M base size m Sl (validAfter ops V) (runOps ops E) t
  | [], _, _, s, hI, _, _ => WP.block_nil ⟨ProgKeep.refl _ _ _ s, hI⟩
  | [op], V, E, s, hI, hS, hR => by
    simp only [readsOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hR
    refine WP.mono (plainOp_ok hL hm hI (hS op (List.mem_cons_self ..)) hR.1) fun s₁ ⟨k₁, I₁⟩ =>
      ⟨⟨k₁.gpr, k₁.rd, k₁.wr, fun x hx ht => k₁.mem x (hx _ (List.mem_cons_self ..)) ht⟩, I₁⟩
  | op :: op' :: ops, V, E, s, hI, hS, hR => by
    rw [readsOk, Bool.and_eq_true, List.all_eq_true] at hR
    simp only [decide_eq_true_eq] at hR
    show WP isa (.seq ((opCall? M op).getD (.block (code M op))).inline
      (progs ((op' :: ops).map fun op => (opCall? M op).getD (.block (code M op)))).inline) s _
    refine WP.seq (WP.mono (plainOp_ok hL hm hI (hS op (List.mem_cons_self ..)) hR.1) fun s₁ ⟨k₁, I₁⟩ => ?_)
    refine WP.mono (plain_ok hL hm (op' :: ops) I₁ (fun op'' h => hS op'' (List.mem_cons_of_mem _ h)) hR.2)
      fun s₂ ⟨k₂, I₂⟩ => ⟨⟨fun r hr => (k₂.gpr r hr).trans (k₁.gpr r hr), k₂.rd.trans k₁.rd,
        k₂.wr.trans k₁.wr, fun x hx ht => ?_⟩, I₂⟩
    rw [List.map_cons] at hx
    rw [k₂.mem x (fun w hw => hx w (List.mem_cons_of_mem _ hw)) ht,
      k₁.mem x (hx _ (List.mem_cons_self ..)) ht]

theorem program_inline (M : Mod) (cs : Forward.Cache) (ops : List FOp) :
    (program M cs ops).inline = program M cs ops := by
  rw [program, Code.inline_of_noCalls (blocks_noCalls _)]

theorem programB_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}
    (hL : Lay M size Sl) (hm : UnitMod m (2^(64*M.n)))
    (ops : List FOp) {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) (hS : ∀ op∈ops,∀ x∈op.out::op.ins,Sl x)
    (hR : readsOk ops V=true) :
    WP isa (programB M ops).inline s fun t =>
      ProgKeep M base (ops.map FOp.out) s t ∧
      Inv M base size m Sl (validAfter ops V) (runOps ops E) t := by
  rw [programB]
  split
  · rename_i h
    rw [program_inline]
    exact WP.mono (program_ok h.2 hL hm ops hI hS hR (fun _ h => by cases h))
      (fun _ h => ⟨h.1,h.2.1⟩)
  · exact plain_ok hL hm ops hI hS hR

end VG.Proof.Weierstrass.X86_64.ForwardField
