import VerifiedGarbage.Proof.Weierstrass.X86_64.NafCacheBuild
import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldTiming

/-! Exact cache environments relate the two public executions of table setup. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64

def cacheTableEnv {m : Nat} [NeZero m] (ptbl tbl : Nat) (E : Nat → Fin m) : Nat → Nat → Fin m
  | 0 => E
  | k+1 => runOps (Naf.cachePairOps ptbl tbl k) (cacheTableEnv ptbl tbl E k)

theorem nafCacheTable_fields_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hn : M.n=4) (hL : Lay M size Sl)
    (hm : UnitMod m (2^(64*M.n))) (k : Nat) {ptbl tbl : Nat}
    {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) (hZ : ∀ i<k,ptbl+96*i+64∈V)
    (hSl : ∀ i<k,Sl (tbl+64*i) ∧ Sl (tbl+64*i+32)) :
    WP isa (Naf.cacheTable M ptbl tbl k) s fun t =>
      Inv M base size m Sl (cacheTableSlots tbl k++V) (cacheTableEnv ptbl tbl E k) t := by
  induction k with
  | zero => exact WP.block_nil hI
  | succ k ih =>
    rw [Naf.cacheTable]
    apply WP.seq
    refine WP.mono (ih (fun i hi => hZ i (by omega)) (fun i hi => hSl i (by omega))) fun u iu => ?_
    refine WP.mono (nafCachePair_fields_ok hn hL hm iu
      (List.mem_append_right _ (hZ k (by omega))) (hSl k (by omega)).1 (hSl k (by omega)).2)
      fun t ⟨_,it⟩ => it.sub ?_
    intro x hx
    simp only [cacheTableSlots,Naf.cachePairOps,validAfter,FOp.out,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind

theorem nafCacheTable_relCT {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hn : M.n=4) (hL : Lay M size Sl)
    (hm : UnitMod m (2^(64*M.n))) (k : Nat) {ptbl tbl : Nat}
    {V : List Nat} {E : Nat → Fin m} (hZ : ∀ i<k,ptbl+96*i+64∈V)
    (hSl : ∀ i<k,Sl (tbl+64*i) ∧ Sl (tbl+64*i+32))
    (hc : ScratchCT (Naf.cacheTable M ptbl tbl k)) :
    RelCT isa (FieldPair M base size m Sl V E) (Naf.cacheTable M ptbl tbl k)
      (FieldPair M base size m Sl (cacheTableSlots tbl k++V) (cacheTableEnv ptbl tbl E k)) :=
  fieldProgram_relCT hc (fun _ hi => nafCacheTable_fields_ok hn hL hm k hi hZ hSl)

end VG.Proof.Weierstrass.X86_64
