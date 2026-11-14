module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.ForwardField
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Fprog
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Forward
import VerifiedGarbage.Proof.Weierstrass.X86_64.ForwardStores
public import VerifiedGarbage.Impl.Mont.X86_64.Double4
public import VerifiedGarbage.Proof.Mont.X86_64.OpsReg
import VerifiedGarbage.Proof.Mont.X86_64.Chain
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Weierstrass.X86_64.Blocks

/-! ### `Weierstrass.X86_64.Double4`, which only this module used -/

section

/-! ### `Mont.X86_64.Double4`, which only this module used -/

section

/-! Register-only four-limb doubling and its canonical memory result. -/

@[expose] public section

namespace VG.Proof.Mont.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Proof.Mont
open VG.Proof.X25519.X86_64

private theorem regsVal_four (s : State) :
    regsVal s [.r8,.r9,.r10,.r11]=val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) := by
  simp only [regsVal,val4]
  omega_using []

theorem double4_sum_ok (s : State) :
    WP isa (.block Double4.sum) s fun t =>
      regsVal t [.r8,.r9,.r10,.r11]+2^256*(t.gpr .r12).toNat =
        2*regsVal s [.r8,.r9,.r10,.r11] ∧ Keeps [.r8,.r9,.r10,.r11,.r12] s t := by
  have h := chain_add (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11)
    (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11)
  apply WP.of_runBlock
  simp only [regsVal_four,val4,Double4.sum,runBlock_cons,runStep_some,runBlock_nil,exec,execAlu,
    readSrc,readSrc32,State.setReg32,Option.map_some,Option.bind_some,
    RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,RegUpd.cf_setReg,RegUpd.cf_arithFlags,
    ite_true,ite_false,reduceCtorEq,Option.some.injEq,exists_eq_left']
  refine ⟨?_,fun r hr => ?_,rfl,rfl,rfl⟩
  · simpa only [regsVal_four,val4,BitVec.ofNat_eq_ofNat,
      show (0#32).signExtend 64=0#64 from rfl,
      show (0#32).setWidth 64=0#64 from rfl,BitVec.zero_add,toNat_ofBool,Nat.two_mul] using h
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_setReg,RegUpd.gpr_arithFlags,
      hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,hr.2.2.2.2,ite_false]

theorem double4_ok {M : Mod} {s : State} {base : Addr} {size m a o : Nat}
    (hn : M.n=4) (hs : Scr s base size) (hM : ModOkW M size m s.mem base)
    (ha : a+32≤size) (ho : o+32≤size) (hx : wordsVal s.mem base a 4<m) :
    WP isa (.block (double4 M o a)) s fun t =>
      OpKeep M base o s t ∧ wordsVal t.mem base o 4=(2*wordsVal s.mem base a 4)%m := by
  rw [double4,List.append_assoc,List.append_assoc,WP.block_append_iff]
  refine WP.mono (loads_ok [.r8,.r9,.r10,.r11] hs ha (by constructor <;> decide)) fun u ⟨hu,ku⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (double4_sum_ok u) fun v ⟨hv,kv⟩ => ?_
  have hs₁ := hs.of_keeps ku (by decide)
  have hs₂ := hs₁.of_keeps kv (by decide)
  change regsVal u [.r8,.r9,.r10,.r11]=wordsVal s.mem base a 4 at hu
  rw [hu] at hv
  change regsVal v [.r8,.r9,.r10,.r11]+2^256*(v.gpr .r12).toNat=2*wordsVal s.mem base a 4 at hv
  rw [WP.block_append_iff]
  refine WP.mono (csubC_ok hs₂ (M:=M) (m:=m) (ts:=[.r8,.r9,.r10,.r11]) (top:=.r12)
    (by rw [hn]; rfl) hM.n0 (by omega_using [hn]) (by constructor <;> decide) hM.mo
    (by rw [kv.2.1,ku.2.1]; exact hM.val) (by rw [hn]; omega_using [hx, hv])) fun w ⟨hw,kw⟩ => ?_
  have hs₃ := hs₂.of_keeps kw (by decide)
  refine WP.mono (stores_ok [.r8,.r9,.r10,.r11] hs₃ ho (by decide)) fun t ⟨ht,kt,ot⟩ => ?_
  have kk : KeepRegs [.rax,.rcx,.rdx,.rbp,.r8,.r9,.r10,.r11,.r12] s t :=
    ((Keeps.regs ku).mono (by simp)).trans
      (((Keeps.regs kv).mono (by simp)).trans
        (((Keeps.regs kw).mono (by simp)).trans (kt.mono (by simp))))
  refine ⟨⟨fun r hr => kk.gpr r (fun h => hr ?_),kk.rd,kk.wr,?_⟩,?_⟩
  · rw [hn]
    apply List.mem_append_left
    change r∈[.rax,.rcx,.rdx,.rbp,.r8,.r9,.r10,.r11,.r12,.r13]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    rcases h with h|h|h|h|h|h|h|h|h <;> simp [h]
  · intro x hx _
    rw [hn] at hx
    rw [ot x hx,kw.2.1,kv.2.1,ku.2.1]
  · change wordsVal t.mem base o 4=regsVal w [.r8,.r9,.r10,.r11] at ht
    rw [ht,hw,hn,hv]

end VG.Proof.Mont.X86_64

end

end


/-! Register-only doubling preserves the field-program invariant. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64

theorem double4_inv_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}
    (hn : M.n=4) (hL : Lay M size Sl) {V : List Nat} {E : Nat → Fin m}
    {s : State} (hI : Inv M base size m Sl V E s) {o a : Nat}
    (ho : Sl o) (ha : a∈V) :
    WP isa (.block (double4 M o a)) s fun t =>
      OpKeep M base o s t ∧ Inv M base size m Sl (o::V) (Function.update E o (E a+E a)) t := by
  have hao := hL.le a (hI.sl a ha)
  have hoo := hL.le o ho
  have hlt := hI.lt a ha
  rw [hn] at hao hoo hlt
  refine WP.mono (double4_ok hn hI.scr hI.mod hao hoo hlt) fun t ⟨hk,he⟩ => ?_
  refine ⟨hk,hI.update hL ho hk ?_ ?_⟩
  · rw [hn,he]
    exact Nat.mod_lt _ (by have := NeZero.ne m; omega_using [hlt])
  · rw [hn,he,Nat.two_mul,toM_add]
    have hv := hI.val a ha
    rw [hn] at hv
    rw [hv]

end VG.Proof.Weierstrass.X86_64

end

end


/-! The forwarded program preserves field values, memory frames and its output cache. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64.ForwardField
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64
open VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass.X86_64.ForwardField
open VG.Proof.Mont VG.Proof.Mont.X86_64

theorem code_stores {M : Mod} (hn : M.n=4) (op : FOp) :
    ∃ is,code M op=is++stores (outputRegs M op) op.out := by
  cases op with
  | mul o a b =>
    simp only [code,opCode,mul,hn,show 4<7 from by decide,↓reduceIte,mulR,mulG,outputRegs,FOp.out]
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
