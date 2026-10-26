module
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointInitLayout
public import VerifiedGarbage.Proof.Weierstrass.X86_64.PointFieldTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableTimingInit
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableCoZTiming

import VerifiedGarbage.Proof.Weierstrass.X86_64.JointSeed
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafCacheBuildTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointLoopTiming
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto

/-! Shared field values through odd-table setup, cache construction and the seed. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

/-- The taint checks of the table: the co-Z table's (`Joint.Cfg.coZ`), or the other's. -/
def JointTableChecks (c : Joint.Cfg) : Prop :=
  if c.coZ then NafTableCoZChecks c.K else NafTableChecks c.K

theorem jointTables_relCT {c : Joint.Cfg} {C : Curve} {base : Addr} {size : Nat} {E : Nat → Fe C}
    (hL : JointInitLayout c size) (hm : UnitMod C.p (2^(64*c.K.M.n)))
    (hOne : c.K.one<C.p) (ht : JointTableChecks c)
    (hc : ScratchCT (Joint.cacheCode c).inline) :
    RelCT isa (FieldPair c.K.M base size C.p (·∈nafSlots c.K) (winRo c.K) E)
      (Code.seq (Joint.tableCode c) (Joint.cacheCode c)).inline
      (fun s t => ∃ E',FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E' s t) := by
  have tbl : RelCT isa (FieldPair c.K.M base size C.p (·∈nafSlots c.K) (winRo c.K) E)
      (Joint.tableCode c).inline (NafTablePair c.K C base size 8) := by
    by_cases h : c.coZ=true
    · simp only [Joint.tableCode,JointTableChecks,h,↓reduceIte] at ht ⊢
      exact nafTableCoZ_relCT hL.naf hL.count hm hL.tableSmall ht
    · simp only [Joint.tableCode,JointTableChecks,h,↓reduceIte,Bool.false_eq_true] at ht ⊢
      exact nafTable_relCT hL.naf hL.count hm hL.tableSmall hOne ht
  apply RelCT.seq tbl
  have cache : ∀ E',RelCT isa
      (FieldPair c.K.M base size C.p (·∈jointSlots c) (nafTableLive c.K 8) E')
      (Joint.cacheCode c).inline
      (fun s t => ∃ E'',FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E'' s t) := by
    intro E'
    have hCL := hL.cacheLay
    have code : RelCT isa
        (FieldPair c.K.M base size C.p (·∈jointSlots c) (nafTableLive c.K 8) E')
        (Joint.cacheCode c).inline
        (fun s t => ∃ E'',FieldPair c.K.M base size C.p (·∈jointSlots c)
          (cacheTableSlots c.K.M.n c.cache 8++nafTableLive c.K 8) E'' s t) := by
      revert hc
      rw [Joint.cacheCode]
      split
      · split
        · exact fun hc => (nafCacheUnrolled_relCT (E:=E') hL.layout.lay hm 8 hCL.hz hCL.cache hc).mono
            (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)
        · exact fun hc => (nafCacheStaged_relCT (E:=E') hL.layout.lay hm hCL hc).mono
            (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)
      · exact fun hc => (nafCacheTable_relCT (E:=E') hL.layout.lay hm hCL hc).mono
          (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)
    exact code.mono
      (fun _ _ h => h) (fun _ _ ⟨_,h⟩ => ⟨_,h.sub (fun x hx => by
        rcases List.mem_append.mp hx with hx|hx
        · exact List.mem_append_right _ (joint_tableLive x hx)
        · exact List.mem_append_left _ (joint_cache_mem.mpr hx))⟩)
  refine (RelCT.exists_ cache).mono ?_ (fun _ _ h => h)
  intro s t ⟨E',hp,_,_⟩
  have lift {s : State} (hi : Inv c.K.M base size C.p (·∈nafSlots c.K) (nafTableLive c.K 8) E' s) :
      Inv c.K.M base size C.p (·∈jointSlots c) (nafTableLive c.K 8) E' s :=
    ⟨hi.scr,hi.mod,fun x hx => List.mem_append_left _ (List.mem_append_left _ (hi.sl x hx)),hi.lt,hi.val⟩
  exact ⟨E',lift hp.1,lift hp.2⟩

theorem jointSeed_relCT {c : Joint.Cfg} {C : Curve} {base : Addr} {size : Nat} {E : Nat → Fe C}
    (hL : JointLayout c size) (hOne : c.K.one<C.p)
    (hc : ScratchCT (.block (Jacobian.infinity c.K c.K.R)))
    (ctr : ScratchCT (.block [.mov32 .rbx (.imm (BitVec.ofNat 32 (Joint.top c)))])) :
    RelCT isa (FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c) E)
      (.block (Jacobian.infinity c.K c.K.R++
        ([.mov32 .rbx (.imm (BitVec.ofNat 32 (Joint.top c)))] : List Instr)))
      (FieldPair c.K.M base size C.p (·∈jointSlots c) (jointLive c)
        (infinityEnv c.K.M C.p c.K.one E c.K.R)) := by
  have sl : ∀ x∈jacCoords c.K.R,x∈jointSlots c := by
    intro x hx
    simp only [jacCoords,jointSlots,nafSlots,winOther,rcbW,List.mem_append,
      List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  apply RelCT.block_append
  apply RelCT.seq (infinity_relCT hL.lay sl hOne hc)
  have step := keepsField_relCT (M:=c.K.M) (base:=base) (size:=size) (m:=C.p)
    (Sl:=(·∈jointSlots c)) (V:=jacCoords c.K.R++jointLive c)
    (E:=infinityEnv c.K.M C.p c.K.one E c.K.R) (Pre:=fun _ => True)
    (Post:=fun s => s.gpr .rbx=BitVec.ofNat 64 (Joint.top c)) (by decide : Reg.rdi∉[Reg.rbx]) ctr
    (fun _ _ hp _ _ => fieldPair_public hp) (fun s _ _ => jointCounter_ok s (by have := hL.n; have := joint_top_le c; omega))
  exact step.mono (fun _ _ h => ⟨h,trivial,trivial⟩)
    (fun _ _ h => h.1.sub (fun _ hx => List.mem_append_right _ hx))

end VG.Proof.Weierstrass.X86_64
