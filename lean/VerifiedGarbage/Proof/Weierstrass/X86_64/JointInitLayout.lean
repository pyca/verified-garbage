module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointGenerator
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafCacheBuild
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableState
public import VerifiedGarbage.Proof.Weierstrass.JacMul
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafArith

/-! The table and cache initialization writes are separate from both scalar streams. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

/-- The slots the table and the cache write: those of `Naf.table` and the
cache's, and the selected pair (which the table by calls, `Joint.tableCall`,
writes `E`'s `Z²` and `Z³` to). -/
def jointInitWork (c : Joint.Cfg) : List Nat :=
  nafWrites c.K++jointCacheSlots c++[c.selected,c.selected+8*c.K.M.n]

def jointInitRanges (c : Joint.Cfg) : List (Nat×Nat) :=
  (jointInitWork c).map (·,8*c.K.M.n)++[(c.K.M.tmp,8*c.K.M.n)]

/-- What the cache's code and the joint loop need of the table of `Q`'s odd
multiples, however it is built, from `s` to `t`: the fields of the table,
`R` and `P` valid, the registers but `rbx` and the field arithmetic's kept,
the memory but `jointInitRanges`, and `P`, `a`, `3b` and zero unchanged, and
the eight entries `Q, 3Q, …, 15Q`. -/
structure JointTablePost (c : Joint.Cfg) (C : Curve) (base : Addr) (size : Nat) (Q : Point C)
    (s t : State) : Prop where
  field : Inv c.K.M base size C.p (·∈jointSlots c) (nafTableLive c.K 8) (tmv C c.K.M.n base t) t
  keep : KeepRegs (.rbx::clob c.K.M.n) s t
  unch : Unch base (jointInitRanges c) s.mem t.mem
  ro : ∀ x∈winRo c.K, tmv C c.K.M.n base t x=tmv C c.K.M.n base s x
  table : ∀ n,1≤n → n≤8 → InvJ C (tmv C c.K.M.n base t (c.K.tblPt n).x)
    (tmv C c.K.M.n base t (c.K.tblPt n).y) (tmv C c.K.M.n base t (c.K.tblPt n).z) (mul (2*n-1) Q)

/-- The table by calls of `C'`'s functions (`Joint.tableCall`) builds the
table, for any curve `C` whose doubling `c.dbl` is, from `Q` affine in `P`. -/
def JointTableCallOk (c : Joint.Cfg) (C' : Impl.Weierstrass.PointOps.Curve) (size : Nat) : Prop :=
  ∀ {C : Curve} {base : Addr} {Q : Point C} {s : State},
    UnitMod C.p (2^(64*c.K.M.n)) → Law C → JDblOk C c.dbl → c.K.one<C.p → onCurve C Q=true →
    Inv c.K.M base size C.p (·∈nafSlots c.K) (winRo c.K) (tmv C c.K.M.n base s) s →
    InvJ C (tmv C c.K.M.n base s c.K.P.x) (tmv C c.K.M.n base s c.K.P.y)
      (tmv C c.K.M.n base s c.K.P.z) Q →
    tmv C c.K.M.n base s c.K.P.z=1 →
    WP isa (Joint.tableCall c C').inline s (JointTablePost c C base size Q s)

structure JointInitLayout (c : Joint.Cfg) (size : Nat) : Prop where
  layout : JointLayout c size
  naf : NafLay c.K size
  count : 1≤c.K.J ∧ 4*c.K.J≤64*c.K.M.n+4
  tableSmall : c.K.tbl<2^31
  cacheSep : c.cache+128*c.K.M.n≤c.K.tbl ∨ c.K.tbl+216*c.K.M.n≤c.cache
  zeroCache : c.K.zero∉jointCacheSlots c
  bitsBounds : ∀ d∈[(c.K.bits,64*c.K.M.n+1),(c.gBits,jointGLen c)],d.1+d.2≤size
  bitsSep : ∀ d∈[(c.K.bits,64*c.K.M.n+1),(c.gBits,jointGLen c)],∀ w∈jointInitRanges c,
    d.1+d.2≤w.1 ∨ w.1+w.2≤d.1
  cacheSmall : c.cache<2^31
  cacheFar : ∀ x∈winRo c.K++winOther c.K,x+8*c.K.M.n≤c.cache ∨ c.cache+128*c.K.M.n≤x
  /-- The table by calls, where the code has it, builds the table. -/
  tableCall : c.coZ=false → ∀ C', c.pts=some C' → JointTableCallOk c C' size

theorem jointInit_sl (c : Joint.Cfg) : ∀ x∈jointInitWork c,x∈jointSlots c := by
  intro x hx
  simp only [jointInitWork,jointSlots,nafWrites,nafSlots,List.mem_append] at hx ⊢
  grind

theorem joint_cache_mem {c : Joint.Cfg} {x : Nat} :
    x∈cacheTableSlots c.K.M.n c.cache 8 ↔ x∈jointCacheSlots c := by
  rw [mem_cacheTableSlots]
  constructor
  · rintro ⟨i,hi,rfl|rfl⟩
    · exact List.mem_map.mpr ⟨2*i,List.mem_range.mpr (by omega_arith),by rw [slot_two_mul]⟩
    · exact List.mem_map.mpr ⟨2*i+1,List.mem_range.mpr (by omega_arith),
        by rw [slot_two_mul_add,Nat.add_assoc]⟩
  · intro hx
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    have hi' := List.mem_range.mp hi
    refine ⟨i/2,by omega_arith,?_⟩
    rcases Nat.mod_two_eq_zero_or_one i with h|h
    · left
      rw [show i=2*(i/2) by omega_arith,slot_two_mul,show 2*(i/2)/2=i/2 by omega_arith]
    · right
      rw [show i=2*(i/2)+1 by omega_arith,slot_two_mul_add,show (2*(i/2)+1)/2=i/2 by omega_arith,
        Nat.add_assoc]

theorem joint_tableLive {c : Joint.Cfg} :
    ∀ x∈winRo c.K++jacCoords c.K.R++nafTblSlots c.K,x∈nafTableLive c.K 8 := by
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · exact List.mem_append_left _ (List.mem_append_left _ hx)
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    have hi' := List.mem_range.mp hi
    by_cases h : i<24
    · exact List.mem_append_right _ (List.mem_map.mpr ⟨i,List.mem_range.mpr h,rfl⟩)
    · apply List.mem_append_left
      apply List.mem_append_right
      simp only [jacCoords,Naf.twice,WinCfg.tblPt,List.mem_cons,List.not_mem_nil,or_false]
      obtain rfl|rfl|rfl : i=24 ∨ i=25 ∨ i=26 := by omega_arith
      all_goals omega_arith

theorem jointCache_z (c : Joint.Cfg) :
    ∀ i<8,c.K.tbl+24*c.K.M.n*i+16*c.K.M.n∈nafTableLive c.K 8 := by
  intro i hi
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨3*i+2,List.mem_range.mpr (by omega_arith),
    by rw [slot_three_mul_two,Nat.add_assoc]⟩

/-- The cache loop's layout in the joint verifier, through `E`. -/
theorem JointInitLayout.cacheLay {c : Joint.Cfg} {size : Nat} (hL : JointInitLayout c size) :
    CacheLoopLay c.K.M size (·∈jointSlots c) c.K.tbl c.cache c.K.E.x (nafTableLive c.K 8) := by
  have hN := hL.naf
  have hn := hL.layout.n
  have eo : ∀ x∈jacCoords c.K.E,x∈winOther c.K := by
    intro x hx
    simp only [jacCoords,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  have ej : ∀ x∈jacCoords c.K.E,x∈jointSlots c := fun x hx =>
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (eo x hx))))
  have ex := hL.cacheFar c.K.E.x (List.mem_append_right _ (eo _ (by simp [jacCoords])))
  have ez := hL.cacheFar c.K.E.z (List.mem_append_right _ (eo _ (by simp [jacCoords])))
  have tx := hN.tbl c.K.E.x (List.mem_append_right _ (eo _ (by simp [jacCoords])))
  have tz := hN.tbl c.K.E.z (List.mem_append_right _ (eo _ (by simp [jacCoords])))
  rw [hN.exz] at ez tz
  have cs := hL.cacheSep
  refine ⟨hn,hL.tableSmall,hL.cacheSmall,by omega_arith,jointCache_z c,fun i hi => ?_,
    ⟨ej _ (by simp [jacCoords]),hN.exy ▸ ej _ (by simp [jacCoords]),
      hN.exz ▸ ej _ (by simp [jacCoords])⟩,by omega_arith,fun x hx => ?_⟩
  · exact ⟨List.mem_append_right _ (joint_cache_mem.mp (mem_cacheTableSlots.mpr ⟨i,hi,Or.inl rfl⟩)),
      List.mem_append_right _ (joint_cache_mem.mp (mem_cacheTableSlots.mpr ⟨i,hi,Or.inr rfl⟩))⟩
  · have far (y : Nat) (hy : y∈winRo c.K++winOther c.K) (hE : y∉jacCoords c.K.E) :
        (y+8*c.K.M.n≤c.K.E.x ∨ c.K.E.x+24*c.K.M.n≤y) ∧
        (y+8*c.K.M.n≤c.cache ∨ c.cache+128*c.K.M.n≤y) := by
      have hy' : y∈jointSlots c := List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ hy))
      have a0 := hL.layout.lay.apart y c.K.E.x hy' (ej _ (by simp [jacCoords]))
        (fun h => hE (by simp [jacCoords,h]))
      have a1 := hL.layout.lay.apart y c.K.E.y hy' (ej _ (by simp [jacCoords]))
        (fun h => hE (by simp [jacCoords,h]))
      have a2 := hL.layout.lay.apart y c.K.E.z hy' (ej _ (by simp [jacCoords]))
        (fun h => hE (by simp [jacCoords,h]))
      rw [hN.exy] at a1
      rw [hN.exz] at a2
      exact ⟨by omega_arith,hL.cacheFar y hy⟩
    simp only [nafTableLive,nafTableSlots,List.mem_append,List.mem_map,List.mem_range] at hx
    rcases hx with ((hx|hx)|hx)|⟨j,hj,rfl⟩
    · refine far x (List.mem_append_left _ hx) fun he => hN.ro x hx (eo x he)
    · refine far x (List.mem_append_right _ (by
        simp only [jacCoords,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,
          or_false] at hx ⊢
        grind)) fun he => ?_
      have hd := hN.nodup
      simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx he
      simp only [winOther,List.cons_append,List.nodup_cons,List.mem_cons,List.mem_append,
        not_or] at hd
      grind
    · simp only [jacCoords,Naf.twice,WinCfg.tblPt,List.mem_cons,List.not_mem_nil,or_false] at hx
      constructor <;> omega_arith
    · have := entry_end_le (8*c.K.M.n) (show j<24 by omega_arith)
      constructor <;> omega_arith

theorem JointGenerator.keep_init {c : Joint.Cfg} {C : Curve} {base T : Addr} {size : Nat}
    {G : Point C} {row : JointGeneratorRow c.K.M.n C G (jointGTop c)} {s t : State} {rs : List Reg}
    (h : JointGenerator c C base T size row s) (hL : JointLayout c size)
    (htmp : c.K.M.tmp+8*c.K.M.n≤size) (hk : KeepRegs rs s t)
    (hu : Unch base (jointInitRanges c) s.mem t.mem) (hs : t.syms=s.syms) :
    JointGenerator c C base T size row t := by
  intro a ha hb ho
  apply (h a ha hb ho).keep_of_mem hs hk.rd hk.wr
  intro z hz
  apply hu z
  intro w hw
  simp only [jointInitRanges,List.mem_append,List.mem_map,List.mem_singleton] at hw
  rcases hw with ⟨x,hx,rfl⟩|rfl
  · exact Or.inr (Nat.le_trans (hL.lay.le x (jointInit_sl c x hx)) hz)
  · exact Or.inr (Nat.le_trans htmp hz)

theorem jointInit_digits {c : Joint.Cfg} {size : Nat} (hL : JointInitLayout c size)
    {base : Addr} {s t : State} (hn : size≤2^64)
    (hu : Unch base (jointInitRanges c) s.mem t.mem) {d l : Nat}
    (hd : (d,l)∈[(c.K.bits,64*c.K.M.n+1),(c.gBits,jointGLen c)])
    {β : Nat → BitVec 8} (hb : ∀ i<l,s.mem (off base (d+i))=β i) :
    ∀ i<l,t.mem (off base (d+i))=β i := by
  intro i hi
  rw [hu.byte (fun w hw => ?_) (by have := hL.bitsBounds _ hd; dsimp only at this; omega_arith),hb i hi]
  have := hL.bitsSep _ hd w hw
  dsimp only at this
  omega_arith

end VG.Proof.Weierstrass.X86_64
