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
    exact ⟨_,rfl⟩
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
    · simp only [hn,show 4<7 from by decide,↓reduceIte,subR]
      exact ⟨_,rfl⟩

theorem outputRegs_length {M : Mod} (hn : M.n=4) (op : FOp) :
    (outputRegs M op).length=4 := by
  cases op <;> simp [outputRegs,hn]

theorem outputRegs_nodup {M : Mod} (hn : M.n=4) (op : FOp) :
    (outputRegs M op).Nodup := by
  cases op <;> simp only [outputRegs,hn] <;> decide

theorem code_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}
    (hn : M.n=4) (hL : Lay M size Sl) (hm : UnitMod m (2^(64*M.n)))
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
      subst b
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
  have h := code_ok hn hL hm hI hS hR
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

end VG.Proof.Weierstrass.X86_64.ForwardField
