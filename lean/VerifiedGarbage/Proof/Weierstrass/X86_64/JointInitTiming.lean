import VerifiedGarbage.Proof.Weierstrass.X86_64.JointSeed
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafCacheBuildTiming

/-! Shared field values through odd-table setup, cache construction and the seed. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

theorem jointTables_relCT {c : Joint.Cfg} {C : Curve} {base : Addr} {size : Nat} {E : Nat → Fe C}
    (hL : JointInitLayout c size) (hm : UnitMod C.p (2^(64*c.K.M.n)))
    (hOne : c.K.one<C.p) (ht : NafTableChecks c.K)
    (hc : ScratchCT (Naf.cacheTable c.K.M c.K.tbl c.cache 8)) :
    RelCT isa (FieldPair c.K.M base size C.p (·∈nafSlots c.K) (winRo c.K) E)
      (.seq (Naf.table c.K) (Naf.cacheTable c.K.M c.K.tbl c.cache 8))
      (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E' s t) := by
  apply RelCT.seq (nafTable_relCT hL.naf hL.count hm hL.tableSmall hOne ht)
  have cache : ∀ E',RelCT isa
      (FieldPair c.K.M base size C.p (·∈jointSlots c) (nafTableLive c.K 8) E')
      (Naf.cacheTable c.K.M c.K.tbl c.cache 8)
      (fun s t => ∃ E'',FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E'' s t) := by
    intro E'
    have hz : ∀ i<8,c.K.tbl+96*i+64∈nafTableLive c.K 8 := by
      intro i hi
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨3*i+2,List.mem_range.mpr (by omega),by omega⟩
    have sl : ∀ i<8,(c.cache+64*i∈jointSlots c) ∧ (c.cache+64*i+32∈jointSlots c) := by
      intro i hi
      constructor
      · exact List.mem_append_right _ (joint_cache_mem.mp (mem_cacheTableSlots.mpr ⟨i,hi,Or.inl rfl⟩))
      · exact List.mem_append_right _ (joint_cache_mem.mp (mem_cacheTableSlots.mpr ⟨i,hi,Or.inr rfl⟩))
    exact (nafCacheTable_relCT (E:=E') hL.layout.n hL.layout.lay hm 8 hz sl hc).mono
      (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub (fun x hx => by
        rcases List.mem_append.mp hx with hx|hx
        · exact List.mem_append_right _ (joint_tableLive hL.layout.n x hx)
        · exact List.mem_append_left _ (joint_cache_mem.mpr hx))⟩)
  refine (RelCT.exists_ cache).mono ?_ (fun _ _ h => h)
  intro s t ⟨E',hp,_,_⟩
  have lift {s : State} (hi : Inv c.K.M base size C.p (·∈nafSlots c.K) (nafTableLive c.K 8) E' s) :
      Inv c.K.M base size C.p (·∈jointSlots c) (nafTableLive c.K 8) E' s :=
    ⟨hi.scr,hi.mod,fun x hx => List.mem_append_left _ (List.mem_append_left _ (hi.sl x hx)),hi.lt,hi.val⟩
  exact ⟨E',lift hp.1,lift hp.2⟩

theorem jointSeed_relCT {c : Joint.Cfg} {C : Curve} {base : Addr} {size : Nat} {E : Nat → Fe C}
    (hL : JointLayout c size) (hOne : c.K.one<C.p)
    (hc : ScratchCT (.block (Jacobian.infinity c.K c.K.R))) :
    RelCT isa (FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E)
      (.block (Jacobian.infinity c.K c.K.R++([.mov32 .rbx (.imm 256)] : List Instr)))
      (FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c)
        (infinityEnv c.K.M C.p c.K.one E c.K.R)) := by
  have sl : ∀ x∈jacCoords c.K.R,x∈jointSlots c := by
    intro x hx
    simp only [jacCoords,jointSlots,nafSlots,winOther,rcbW,List.mem_append,
      List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  apply RelCT.block_append
  apply RelCT.seq (infinity_relCT hL.lay sl hOne hc)
  have ctr : ScratchCT (.block [.mov32 .rbx (.imm 256)]) :=
    VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)
  have step := keepsField_relCT (M:=c.K.M) (base:=base) (size:=size) (m:=C.p)
    (Sl:=(·∈jointSlots c)) (V:=jacCoords c.K.R++jointLive c)
    (E:=infinityEnv c.K.M C.p c.K.one E c.K.R) (Pre:=fun _ => True)
    (Post:=fun s => s.gpr .rbx=256) (by decide : Reg.rdi∉[Reg.rbx]) ctr
    (fun _ _ hp _ _ => fieldPair_public hp) (fun s _ _ => jointCounter_ok s)
  exact step.mono (fun _ _ h => ⟨h,trivial,trivial⟩)
    (fun _ _ h => h.1.sub (fun _ hx => List.mem_append_right _ hx))

end VG.Proof.Weierstrass.X86_64
