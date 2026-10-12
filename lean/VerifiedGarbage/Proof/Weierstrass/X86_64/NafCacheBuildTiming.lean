import VerifiedGarbage.Proof.Weierstrass.X86_64.NafCacheBuild
import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldTiming

/-! Exact cache environments relate the two public executions of table setup. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64

theorem nafCacheTable_relCT {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hm : UnitMod m (2^(64*M.n))) {ptbl tbl e : Nat}
    {V : List Nat} {E : Nat → Fin m} (hC : CacheLoopLay M size Sl ptbl tbl e V)
    (hc : ScratchCT (Naf.cacheTable M ptbl tbl e).inline) :
    RelCT isa (FieldPair M base size m Sl V E) (Naf.cacheTable M ptbl tbl e).inline
      (FieldPair M base size m Sl (cacheTableSlots M.n tbl 8++V) (cacheTableEnv M.n ptbl tbl E 8)) :=
  fieldProgram_relCT hc (fun _ hi => WP.mono (nafCacheTable_fields_ok hL hm hC hi) fun _ h => h.2)

/-- `nafCacheTable_relCT`, for the loop's steps unrolled (`Naf.cacheStaged`). -/
theorem nafCacheStaged_relCT {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hm : UnitMod m (2^(64*M.n))) {ptbl tbl e : Nat}
    {V : List Nat} {E : Nat → Fin m} (hC : CacheLoopLay M size Sl ptbl tbl e V)
    (hc : ScratchCT (Naf.cacheStaged M ptbl tbl e).inline) :
    RelCT isa (FieldPair M base size m Sl V E) (Naf.cacheStaged M ptbl tbl e).inline
      (FieldPair M base size m Sl (cacheTableSlots M.n tbl 8++V) (cacheTableEnv M.n ptbl tbl E 8)) :=
  fieldProgram_relCT hc (fun _ hi => WP.mono (nafCacheStaged_fields_ok hL hm hC hi) fun _ h => h.2)

end VG.Proof.Weierstrass.X86_64
