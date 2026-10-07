import VerifiedGarbage.Proof.Weierstrass.X86_64.JointGenerator
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTable
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafCacheBuild

/-! The table and cache initialization writes are separate from both scalar streams. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

def jointInitWork (c : Joint.Cfg) : List Nat := nafWrites c.K++jointCacheSlots c

def jointInitRanges (c : Joint.Cfg) : List (Nat×Nat) :=
  (jointInitWork c).map (·,8*c.K.M.n)++[(c.K.M.tmp,8*c.K.M.n)]

structure JointInitLayout (c : Joint.Cfg) (size : Nat) : Prop where
  layout : JointLayout c size
  naf : NafLay c.K size
  count : c.K.J=65
  tableSmall : c.K.tbl<2^31
  cacheSep : c.cache+512≤c.K.tbl ∨ c.K.tbl+864≤c.cache
  zeroCache : c.K.zero∉jointCacheSlots c
  bitsBounds : ∀ d∈[c.K.bits,c.gBits],d+257≤size
  bitsSep : ∀ d∈[c.K.bits,c.gBits],∀ w∈jointInitRanges c,d+257≤w.1 ∨ w.1+w.2≤d

theorem jointInit_sl (c : Joint.Cfg) : ∀ x∈jointInitWork c,x∈jointSlots c := by
  intro x hx
  simp only [jointInitWork,jointSlots,nafWrites,nafSlots,List.mem_append] at hx ⊢
  grind

theorem joint_cache_mem {c : Joint.Cfg} {x : Nat} : x∈cacheTableSlots c.cache 8 ↔ x∈jointCacheSlots c := by
  rw [mem_cacheTableSlots]
  constructor
  · rintro ⟨i,hi,rfl|rfl⟩
    · exact List.mem_map.mpr ⟨2*i,List.mem_range.mpr (by omega),by omega⟩
    · exact List.mem_map.mpr ⟨2*i+1,List.mem_range.mpr (by omega),by omega⟩
  · intro hx
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    have hi' := List.mem_range.mp hi
    exact ⟨i/2,by omega,by omega⟩

theorem joint_tableLive {c : Joint.Cfg} (hn : c.K.M.n=4) :
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
      simp only [jacCoords,Naf.twice,WinCfg.tblPt,hn,List.mem_cons,List.not_mem_nil,or_false]
      omega

theorem JointGenerator.keep_init {c : Joint.Cfg} {C : Curve} {base T : Addr} {size : Nat}
    {G : Point C} {row : JointGeneratorRow C G} {s t : State} {rs : List Reg}
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
    (hu : Unch base (jointInitRanges c) s.mem t.mem) {d : Nat} (hd : d∈[c.K.bits,c.gBits])
    {β : Nat → BitVec 8} (hb : ∀ i<257,s.mem (off base (d+i))=β i) :
    ∀ i<257,t.mem (off base (d+i))=β i := by
  intro i hi
  rw [hu.byte (fun w hw => ?_) (by have := hL.bitsBounds d hd; omega),hb i hi]
  have := hL.bitsSep d hd w hw
  omega

end VG.Proof.Weierstrass.X86_64
