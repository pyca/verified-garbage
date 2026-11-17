module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointGenerator
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafTableState
public import VerifiedGarbage.Proof.Weierstrass.JacMul
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafArith
public import VerifiedGarbage.Impl.Weierstrass.X86_64.NafCacheBuild
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Ladder
import VerifiedGarbage.Proof.Weierstrass.X86_64.ForwardField
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafAddress
import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafCopy
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelectPass
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacState
import VerifiedGarbage.Proof.Weierstrass.X86_64.Unch
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-! ### `Weierstrass.X86_64.NafCacheBuild`, which this module and modules that import it used -/

section

/-! Cached powers are canonical Montgomery values and preserve the source table. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.X25519.X86_64 (Keeps)

theorem nafCacheMul_fields_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hm : UnitMod m (2^(64*M.n))) {z o : Nat}
    {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) (hZ : z∈V) (h2 : Sl o) (h3 : Sl (o+8*M.n)) :
    WP isa (Naf.cacheMul M z o).inline s fun t =>
      ProgKeep M base ((Naf.cacheOps M.n z o).map FOp.out) s t ∧
      Inv M base size m Sl (validAfter (Naf.cacheOps M.n z o) V) (runOps (Naf.cacheOps M.n z o) E) t := by
  obtain hS : ∀ op∈Naf.cacheOps M.n z o,∀ x∈op.out::op.ins,Sl x := by
    intro op hop x hx
    simp only [Naf.cacheOps,List.mem_cons,List.not_mem_nil,or_false] at hop
    rcases hop with rfl|rfl <;>
      simp only [FOp.out,FOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
    · rcases hx with rfl|rfl|rfl
      · exact h2
      · exact hI.sl _ hZ
      · exact hI.sl _ hZ
    · rcases hx with rfl|rfl|rfl
      · exact h3
      · exact h2
      · exact hI.sl _ hZ
  obtain hR : readsOk (Naf.cacheOps M.n z o) V=true := by
    simp [Naf.cacheOps,readsOk,FOp.ins,FOp.out,hZ]
  rw [Naf.cacheMul]
  split
  · rw [ForwardField.program_inline]
    exact WP.mono (ForwardField.program_ok (by assumption : M.adx ∧ M.n=4).2 hL hm _ hI hS hR
      (fun _ h => by cases h))
      (fun _ h => ⟨h.1,h.2.1⟩)
  · exact (fprogB_ok hL hm _ hI hS hR)

theorem wordPieceOff_ok {w : Nat} (hw : 2≤w) (i : Nat) :
    Naf.wordPieceOff w i%8=0 ∧ Naf.wordPieceOff w i+16≤8*w := by
  unfold Naf.wordPieceOff
  split <;> omega_arith

theorem wordPieceOff_cover {w k : Nat} (hk : k<w) :
    ∃ i<(w+1)/2,Naf.wordPieceOff w i≤8*k ∧ 8*k<Naf.wordPieceOff w i+16 := by
  by_cases h : k/2+1<(w+1)/2
  · exact ⟨k/2,by omega_arith,by simp only [Naf.wordPieceOff,h,ite_true]; omega_arith⟩
  · refine ⟨(w+1)/2-1,by omega_arith,?_⟩
    obtain h' : ¬((w+1)/2-1+1<(w+1)/2) := by omega_arith
    simp only [Naf.wordPieceOff,h',ite_false]
    omega_arith

theorem mov_rax_rbx_ok (s : State) {j : Nat} (hc : s.gpr .rbx=BitVec.ofNat 64 j) :
    WP isa (.block [.mov .rax (.reg .rbx)]) s fun u =>
      u.gpr .rax=BitVec.ofNat 64 j ∧ Keeps [.rax] s u := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,readSrc,Option.map_some,
    RegUpd.gpr_setReg,ite_true,hc,Option.some.injEq,exists_eq_left']
  refine ⟨trivial,fun r hr => ?_,rfl,rfl,rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_setReg,hr,ite_false]

/-- `Z` of entry `j` of the table at `ptbl` into `z`. -/
theorem nafCacheLoad_ok {s : State} {base : Addr} {size n ptbl z j : Nat}
    (hs : Scr s base size) (hc : s.gpr .rbx=BitVec.ofNat 64 j)
    (hn : n=4 ∨ n=6 ∨ n=9) (hp : ptbl<2^31)
    (hZ : ptbl+24*n*j+16*n+8*n≤size) (hz : z+8*n≤size)
    (hSep : z+8*n≤ptbl+24*n*j+16*n ∨ ptbl+24*n*j+16*n+8*n≤z) :
    WP isa (.block (Naf.cacheLoad n ptbl z)) s fun t =>
      wordsVal t.mem base z n=wordsVal s.mem base (ptbl+24*n*j+16*n) n ∧
      KeepRegs [.rax,.rcx,.rdx] s t ∧ Outside base z (8*n) s.mem t.mem := by
  rw [Naf.cacheLoad,List.append_assoc,WP.block_append_iff]
  refine WP.mono (mov_rax_rbx_ok s hc) fun u ⟨iu,ku⟩ => ?_
  obtain su := hs.of_keeps ku (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (nafAddress_ok u su.rdi iu hp (by omega_arith)) fun v ⟨av,kv⟩ => ?_
  obtain sv := su.of_keeps kv (by decide)
  refine WP.mono (nafCopyPiecesAt_ok (a:=ptbl+24*n*j+16*n) (o:=z) (L:=8*n)
    ((n+1)/2) v sv hZ hz hSep (fun i _ => wordPieceOff_ok (by omega_arith) i)
    (fun i _ => by rw [ea_tblAt,av]; unfold off; rw [Offset.add_add]; simp only [Nat.add_assoc])
    (fun i _ => by rw [ea_sc,sv.rdi])) fun t ⟨et,ot,gt,rt,wt⟩ => ?_
  refine ⟨?_,⟨fun r hr => ?_,rt.trans (kv.2.2.1.trans ku.2.2.1),
    wt.trans (kv.2.2.2.trans ku.2.2.2)⟩,?_⟩
  · have e := nafCopyAt_wordsAt (d:=0) (w:=n) et (fun k _ hk => wordPieceOff_cover (by omega_arith))
    simp only [Nat.mul_zero,Nat.add_zero] at e
    rw [e,kv.2.1,ku.2.1]
  · rw [gt,kv.1 r hr,ku.1 r (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; exact fun he => hr (Or.inl he))]
  · rw [kv.2.1,ku.2.1] at ot
    exact ot

/-- The `16 n` bytes at `o` into entry `j` of the cache at `tbl`. -/
theorem nafCacheStore_ok {s : State} {base : Addr} {size n tbl o j : Nat}
    (hs : Scr s base size) (hc : s.gpr .rbx=BitVec.ofNat 64 j)
    (hn : n=4 ∨ n=6 ∨ n=9) (ht : tbl<2^31)
    (hT : tbl+16*n*j+16*n≤size) (ho : o+16*n≤size)
    (hSep : o+16*n≤tbl+16*n*j ∨ tbl+16*n*j+16*n≤o) :
    WP isa (.block (Naf.cacheStore n tbl o)) s fun t =>
      wordsVal t.mem base (tbl+16*n*j) n=wordsVal s.mem base o n ∧
      wordsVal t.mem base (tbl+16*n*j+8*n) n=wordsVal s.mem base (o+8*n) n ∧
      KeepRegs [.rax,.rcx,.rdx] s t ∧ Outside base (tbl+16*n*j) (16*n) s.mem t.mem := by
  rw [Naf.cacheStore,List.append_assoc,WP.block_append_iff]
  refine WP.mono (mov_rax_rbx_ok s hc) fun u ⟨iu,ku⟩ => ?_
  obtain su := hs.of_keeps ku (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (stridedAddress_ok u su.rdi iu ht (by omega_arith)) fun v ⟨av,kv⟩ => ?_
  obtain sv := su.of_keeps kv (by decide)
  refine WP.mono (nafCopyPiecesAt_ok (a:=o) (o:=tbl+16*n*j) (L:=16*n) (p:=fun i => 16*i)
    n v sv ho hT hSep.symm (fun i hi => ⟨by omega_arith,by omega_arith⟩)
    (fun i _ => by rw [ea_sc,sv.rdi])
    (fun i _ => by rw [ea_tblAt,av]; unfold off; rw [Offset.add_add])) fun t ⟨et,ot,gt,rt,wt⟩ => ?_
  obtain cov : ∀ k,k<2*n → ∃ i<n,16*i≤8*k ∧ 8*k<16*i+16 := fun k hk => ⟨k/2,by omega_arith,by omega_arith,by omega_arith⟩
  refine ⟨?_,?_,⟨fun r hr => ?_,rt.trans (kv.2.2.1.trans ku.2.2.1),
    wt.trans (kv.2.2.2.trans ku.2.2.2)⟩,?_⟩
  · have e := nafCopyAt_wordsAt (d:=0) (w:=n) et (fun k _ hk => cov k (by omega_arith))
    simp only [Nat.mul_zero,Nat.add_zero] at e
    rw [e,kv.2.1,ku.2.1]
  · have e := nafCopyAt_wordsAt (d:=n) (w:=n) et (fun k hk hk' => cov k (by omega_arith))
    rw [e,kv.2.1,ku.2.1]
  · rw [gt,kv.1 r hr,ku.1 r (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; exact fun he => hr (Or.inl he))]
  · rw [kv.2.1,ku.2.1] at ot
    exact ot

/-- The slots of the first `k` cache entries of `16 n` bytes: `Z²` and `Z³`. -/
def cacheTableSlots (n tbl : Nat) : Nat → List Nat
  | 0 => []
  | k+1 => [tbl+16*n*k,tbl+16*n*k+8*n]++cacheTableSlots n tbl k

theorem mem_cacheTableSlots {x n tbl k : Nat} :
    x∈cacheTableSlots n tbl k ↔ ∃ i<k,x=tbl+16*n*i ∨ x=tbl+16*n*i+8*n := by
  induction k with
  | zero => simp [cacheTableSlots]
  | succ k ih =>
    simp only [cacheTableSlots,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,ih]
    constructor
    · rintro ((h|h)|⟨i,hi,h⟩)
      · exact ⟨k,by omega_arith,Or.inl h⟩
      · exact ⟨k,by omega_arith,Or.inr h⟩
      · exact ⟨i,by omega_arith,h⟩
    · rintro ⟨i,hi,h⟩
      by_cases he : i=k
      · subst i; exact Or.inl h
      · exact Or.inr ⟨i,by omega_arith,h⟩

/-- The field values after the first `k` cache entries. -/
def cacheTableEnv {m : Nat} [NeZero m] (n ptbl tbl : Nat) (E : Nat → Fin m) : Nat → Nat → Fin m
  | 0 => E
  | k+1 => runOps (Naf.cacheOps n (ptbl+24*n*k+16*n) (tbl+16*n*k)) (cacheTableEnv n ptbl tbl E k)

theorem cacheTableEnv_other {m : Nat} [NeZero m] {n ptbl tbl : Nat} {E : Nat → Fin m} {x : Nat} :
    ∀ k,(∀ j<k,x≠tbl+16*n*j ∧ x≠tbl+16*n*j+8*n) → cacheTableEnv n ptbl tbl E k x=E x
  | 0,_ => rfl
  | k+1,h => by
    simp only [cacheTableEnv,Naf.cacheOps,runOps,List.foldl_cons,List.foldl_nil,FOp.run,
      Function.update_of_ne (h k (by omega_arith)).1,Function.update_of_ne (h k (by omega_arith)).2]
    exact cacheTableEnv_other k fun j hj => h j (by omega_arith)

/-- The cache keeps `Z²` and `Z³` of each entry. -/
theorem cacheTableEnv_entry {m : Nat} [NeZero m] {n ptbl tbl : Nat} {E : Nat → Fin m}
    (hn : 0<n) (hSep : tbl+128*n≤ptbl ∨ ptbl+192*n≤tbl) {i k : Nat} (hi : i<k) (hk : k≤8) :
    cacheTableEnv n ptbl tbl E k (tbl+16*n*i)=E (ptbl+24*n*i+16*n)*E (ptbl+24*n*i+16*n) ∧
    cacheTableEnv n ptbl tbl E k (tbl+16*n*i+8*n)=
      cacheTableEnv n ptbl tbl E k (tbl+16*n*i)*E (ptbl+24*n*i+16*n) := by
  induction k with
  | zero => omega_arith
  | succ k ih =>
    obtain hz : cacheTableEnv n ptbl tbl E k (ptbl+24*n*k+16*n)=E (ptbl+24*n*k+16*n) := by
      apply cacheTableEnv_other
      intro j hj
      have := entry_end_le (16*n) (show j<8 by omega_arith)
      have := entry_end_le (24*n) (show k<8 by omega_arith)
      omega_arith
    obtain h23 : tbl+16*n*k≠tbl+16*n*k+8*n := by omega_arith
    obtain hzk : ptbl+24*n*k+16*n≠tbl+16*n*k := by
      have := entry_end_le (16*n) (show k<8 by omega_arith)
      have := entry_end_le (24*n) (show k<8 by omega_arith)
      omega_arith
    by_cases he : i=k
    · subst i
      simp only [cacheTableEnv,Naf.cacheOps,runOps,List.foldl_cons,List.foldl_nil,FOp.run,
        Function.update_self,Function.update_of_ne h23,Function.update_of_ne hzk,hz]
      refine ⟨?_,?_⟩ <;> first | trivial | rfl
    · have hik : i<k := by omega_arith
      have := entry_end_le (16*n) hik
      obtain n2 : tbl+16*n*i≠tbl+16*n*k ∧ tbl+16*n*i≠tbl+16*n*k+8*n := ⟨by omega_arith,by omega_arith⟩
      obtain n3 : tbl+16*n*i+8*n≠tbl+16*n*k ∧ tbl+16*n*i+8*n≠tbl+16*n*k+8*n := ⟨by omega_arith,by omega_arith⟩
      simp only [cacheTableEnv,Naf.cacheOps,runOps,List.foldl_cons,List.foldl_nil,FOp.run,
        Function.update_of_ne n2.1,Function.update_of_ne n2.2,Function.update_of_ne n3.1,
        Function.update_of_ne n3.2]
      exact ih hik (by omega_arith)

/-- The slots the cache loop writes: the cache and `e`'s three. -/
def cacheLoopSlots (n tbl e : Nat) : List Nat := cacheTableSlots n tbl 8++[e,e+8*n,e+16*n]

/-- What the cache loop keeps. -/
structure CacheLoopKeep (M : Mod) (base : Addr) (tbl e : Nat) (s t : State) : Prop where
  regs : KeepRegs (.rbx::clob M.n) s t
  unch : Unch base ((cacheLoopSlots M.n tbl e).map (·,8*M.n)++[(M.tmp,8*M.n)]) s.mem t.mem

/-- The layout facts of the cache loop: the table's `Z`s are in `V`, apart
from the cache and from `e`'s three slots. -/
structure CacheLoopLay (M : Mod) (size : Nat) (Sl : Nat → Prop) (ptbl tbl e : Nat)
    (V : List Nat) : Prop where
  hn : M.n=4 ∨ M.n=6 ∨ M.n=9
  hp : ptbl<2^31
  ht : tbl<2^31
  sep : tbl+128*M.n≤ptbl ∨ ptbl+192*M.n≤tbl
  hz : ∀ i<8,ptbl+24*M.n*i+16*M.n∈V
  cache : ∀ i<8,Sl (tbl+16*M.n*i) ∧ Sl (tbl+16*M.n*i+8*M.n)
  he : Sl e ∧ Sl (e+8*M.n) ∧ Sl (e+16*M.n)
  ecache : e+24*M.n≤tbl ∨ tbl+128*M.n≤e
  hv : ∀ x∈V,(x+8*M.n≤e ∨ e+24*M.n≤x) ∧ (x+8*M.n≤tbl ∨ tbl+128*M.n≤x)

theorem CacheLoopLay.slots {M : Mod} {size : Nat} {Sl : Nat → Prop} {ptbl tbl e : Nat}
    {V : List Nat} (h : CacheLoopLay M size Sl ptbl tbl e V) :
    ∀ x∈cacheLoopSlots M.n tbl e,Sl x := by
  intro x hx
  simp only [cacheLoopSlots,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with hx|rfl|rfl|rfl
  · obtain ⟨i,hi,rfl|rfl⟩ := mem_cacheTableSlots.mp hx
    · exact (h.cache i hi).1
    · exact (h.cache i hi).2
  · exact h.he.1
  · exact h.he.2.1
  · exact h.he.2.2

/-- One entry of the cache loop. -/
theorem nafCacheStep_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hm : UnitMod m (2^(64*M.n)))
    {ptbl tbl e : Nat} {V : List Nat} (hC : CacheLoopLay M size Sl ptbl tbl e V)
    {E : Nat → Fin m} {s u : State} {i : Nat} (hi : i<8)
    (hc : u.gpr .rbx=BitVec.ofNat 64 i) (ku : CacheLoopKeep M base tbl e s u)
    (iu : Inv M base size m Sl (cacheTableSlots M.n tbl i++V) (cacheTableEnv M.n ptbl tbl E i) u) :
    WP isa (Naf.cacheStep M ptbl tbl e).inline u fun t =>
      t.gpr .rbx=BitVec.ofNat 64 (i+1) ∧ t.cf=some (decide (i+1<8)) ∧
      CacheLoopKeep M base tbl e s t ∧
      Inv M base size m Sl (cacheTableSlots M.n tbl (i+1)++V) (cacheTableEnv M.n ptbl tbl E (i+1)) t := by
  have hn := hC.hn
  obtain hn0 : 0<M.n := by omega_arith
  have hnw := iu.scr.nowrap
  obtain hzi := hC.hz i hi
  obtain hzV : ptbl+24*M.n*i+16*M.n∈cacheTableSlots M.n tbl i++V := List.mem_append_right _ hzi
  obtain hzS := iu.sl _ hzV
  obtain hzb := hL.le _ hzS
  obtain hzv := hC.hv _ hzi
  have hes := hC.he
  obtain heb := hL.le _ hes.2.2
  obtain hci := hC.cache i hi
  obtain hcb := hL.le _ hci.2
  have hEC := hC.ecache
  obtain hzc : cacheTableEnv M.n ptbl tbl E i (ptbl+24*M.n*i+16*M.n)=E (ptbl+24*M.n*i+16*M.n) :=
    cacheTableEnv_other i fun j hj => by
      have := entry_end_le (16*M.n) (show j<8 by omega_arith)
      have := hzv.2
      omega_arith
  simp only [Naf.cacheStep,Code.inline]
  apply WP.seq
  refine WP.mono (nafCacheLoad_ok iu.scr hc hn hC.hp hzb heb (by have := hzv.1; omega_arith))
    fun u1 ⟨w1,k1,o1⟩ => ?_
  obtain s1 := iu.scr.of_keepRegs k1 (by decide)
  obtain m1 : ModOkW M size m u1.mem base := iu.mod.unch o1.unch (by
    intro w hw
    rw [List.mem_singleton.mp hw]
    exact (hL.mo _ hes.2.2).symm) hnw
  obtain i1 : Inv M base size m Sl [e+16*M.n] (fun _ => E (ptbl+24*M.n*i+16*M.n)) u1 :=
    ⟨s1,m1,fun x hx => by rw [List.mem_singleton.mp hx]; exact hes.2.2,
      fun x hx => by rw [List.mem_singleton.mp hx,w1]; exact iu.lt _ hzV,
      fun x hx => by rw [List.mem_singleton.mp hx,w1,iu.val _ hzV,hzc]⟩
  apply WP.seq
  refine WP.mono (nafCacheMul_fields_ok hL hm i1 (List.mem_singleton_self _) hes.1 hes.2.1)
    fun u2 ⟨k2,i2⟩ => ?_
  obtain he2 : e≠e+8*M.n := by omega_arith
  obtain hez : e+16*M.n≠e := by omega_arith
  obtain v2 := i2.val e (by simp [validAfter,Naf.cacheOps,FOp.out])
  obtain v3 := i2.val (e+8*M.n) (by simp [validAfter,Naf.cacheOps,FOp.out])
  obtain l2 := i2.lt e (by simp [validAfter,Naf.cacheOps,FOp.out])
  obtain l3 := i2.lt (e+8*M.n) (by simp [validAfter,Naf.cacheOps,FOp.out])
  simp only [Naf.cacheOps,runOps,List.foldl_cons,List.foldl_nil,FOp.run,Function.update_self,
    Function.update_of_ne he2,Function.update_of_ne hez] at v2 v3
  obtain s2 := k2.scr s1
  rw [WP.block_append_iff]
  refine WP.mono (nafCacheStore_ok s2 ((k2.gpr _ (rbx_not_clob _)).trans
      ((k1.gpr _ (by decide)).trans hc)) hn hC.ht
      (by omega_arith) (by omega_arith) (by have := entry_end_le (16*M.n) (show i<8 by omega_arith); omega_arith))
    fun u3 ⟨w2,w3,k3,o3⟩ => ?_
  obtain c3 : u3.gpr .rbx=BitVec.ofNat 64 i :=
    (k3.gpr _ (by decide)).trans ((k2.gpr _ (rbx_not_clob _)).trans ((k1.gpr _ (by decide)).trans hc))
  refine WP.mono (nafTable_advance_ok hi c3) fun t ⟨ct,ft,kt⟩ => ?_
  obtain uw : Unch base (([(e+16*M.n,8*M.n)]++(((Naf.cacheOps M.n (e+16*M.n) e).map FOp.out).map
      (·,8*M.n)++[(M.tmp,8*M.n)]))++[(tbl+16*M.n*i,8*M.n),(tbl+16*M.n*i+8*M.n,8*M.n)])
      u.mem t.mem := by
    rw [kt.2.1]
    refine (o1.unch.trans k2.unch).trans fun x hx => o3 x ?_
    obtain a := hx _ (List.mem_cons_self ..)
    obtain b := hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    dsimp only at a b
    omega_arith
  obtain uwc : ∀ w∈([(e+16*M.n,8*M.n)]++(((Naf.cacheOps M.n (e+16*M.n) e).map FOp.out).map
      (·,8*M.n)++[(M.tmp,8*M.n)]))++[(tbl+16*M.n*i,8*M.n),(tbl+16*M.n*i+8*M.n,8*M.n)],
      w=(M.tmp,8*M.n) ∨ ∃ x∈cacheLoopSlots M.n tbl e,w=(x,8*M.n) := by
    intro w hw
    simp only [Naf.cacheOps,List.map_cons,List.map_nil,FOp.out,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false,or_assoc] at hw
    rcases hw with rfl|rfl|rfl|rfl|rfl|rfl
    · exact Or.inr ⟨_,by simp [cacheLoopSlots],rfl⟩
    · exact Or.inr ⟨_,by simp [cacheLoopSlots],rfl⟩
    · exact Or.inr ⟨_,by simp [cacheLoopSlots],rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨_,List.mem_append_left _ (mem_cacheTableSlots.mpr ⟨i,hi,Or.inl rfl⟩),rfl⟩
    · exact Or.inr ⟨_,List.mem_append_left _ (mem_cacheTableSlots.mpr ⟨i,hi,Or.inr rfl⟩),rfl⟩
  obtain regs : KeepRegs (.rbx::clob M.n) u t := by
    refine ⟨fun r hr => ?_,(kt.2.2.1.trans (k3.rd.trans (k2.rd.trans k1.rd))),
      (kt.2.2.2.trans (k3.wr.trans (k2.wr.trans k1.wr)))⟩
    simp only [List.mem_cons,not_or] at hr
    obtain hc' : ∀ r',r'∈[Reg.rax,.rcx,.rdx] → r'∈clob M.n := by
      intro r' h'
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h'
      rcases h' with rfl|rfl|rfl <;> simp [clob]
    rw [kt.1 r (by simpa using hr.1),k3.gpr r (fun h => hr.2 (hc' r h)),k2.gpr r hr.2,
      k1.gpr r (fun h => hr.2 (hc' r h))]
  obtain keep : CacheLoopKeep M base tbl e s t := by
    refine ⟨ku.regs.trans regs,(ku.unch.trans uw).mono fun w hw => ?_⟩
    rcases List.mem_append.mp hw with hw|hw
    · exact hw
    · rcases uwc w hw with rfl|⟨x,hx,rfl⟩
      · exact List.mem_append_right _ (List.mem_singleton_self _)
      · exact List.mem_append_left _ (List.mem_map.mpr ⟨x,hx,rfl⟩)
  obtain st : Scr t base size := iu.scr.of_keepRegs regs (by
    simp only [List.mem_cons,not_or]; exact ⟨by decide,rdi_not_clob _⟩)
  obtain mt : ModOkW M size m t.mem base := iu.mod.unch uw (fun w hw => by
    rcases uwc w hw with rfl|⟨x,hx,rfl⟩
    · exact iu.mod.sep
    · exact (hL.mo x (hC.slots x hx)).symm) hnw
  obtain same : ∀ x∈cacheTableSlots M.n tbl i++V,
      wordsVal t.mem base x M.n=wordsVal u.mem base x M.n := by
    intro x hx
    obtain hxS := iu.sl x hx
    obtain hxb := hL.le x hxS
    obtain hxt := hL.tmp x hxS
    obtain far : (x+8*M.n≤e ∨ e+24*M.n≤x) ∧
        (x+8*M.n≤tbl+16*M.n*i ∨ tbl+16*M.n*i+16*M.n≤x) := by
      rcases List.mem_append.mp hx with hx|hx
      · obtain ⟨j,hj,rfl|rfl⟩ := mem_cacheTableSlots.mp hx
        · have := entry_end_le (16*M.n) hj
          have := entry_end_le (16*M.n) (show j<8 by omega_arith)
          omega_arith
        · have := entry_end_le (16*M.n) hj
          have := entry_end_le (16*M.n) (show j<8 by omega_arith)
          omega_arith
      · have := hC.hv x hx
        have := entry_end_le (16*M.n) (show i<8 by omega_arith)
        omega_arith
    apply uw.wordsVal _ (by omega_arith)
    intro w hw
    simp only [Naf.cacheOps,List.map_cons,List.map_nil,FOp.out,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false,or_assoc] at hw
    rcases hw with rfl|rfl|rfl|rfl|rfl|rfl <;> dsimp only <;> omega_arith
  obtain hsl : ∀ x∈cacheTableSlots M.n tbl (i+1)++V,Sl x := by
    intro x hx
    simp only [cacheTableSlots,List.append_assoc,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false] at hx
    rcases hx with (rfl|rfl)|hx
    · exact hci.1
    · exact hci.2
    · exact iu.sl x (List.mem_append.mpr hx)
  obtain n2 : ∀ x∈cacheTableSlots M.n tbl i++V,x≠tbl+16*M.n*i ∧ x≠tbl+16*M.n*i+8*M.n := by
    intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · obtain ⟨j,hj,rfl|rfl⟩ := mem_cacheTableSlots.mp hx <;>
        · have := entry_end_le (16*M.n) hj
          exact ⟨by omega_arith,by omega_arith⟩
    · have := (hC.hv x hx).2
      have := entry_end_le (16*M.n) (show i<8 by omega_arith)
      exact ⟨by omega_arith,by omega_arith⟩
  obtain e23 : tbl+16*M.n*i+8*M.n≠tbl+16*M.n*i := by omega_arith
  obtain e3z : tbl+16*M.n*i≠ptbl+24*M.n*i+16*M.n := by
    have := entry_end_le (24*M.n) (show i<8 by omega_arith)
    have := entry_end_le (16*M.n) (show i<8 by omega_arith)
    have := hC.sep
    omega_arith
  obtain env2 : cacheTableEnv M.n ptbl tbl E (i+1) (tbl+16*M.n*i)=
      E (ptbl+24*M.n*i+16*M.n)*E (ptbl+24*M.n*i+16*M.n) := by
    simp only [cacheTableEnv,Naf.cacheOps,runOps,List.foldl_cons,List.foldl_nil,FOp.run,
      Function.update_self,Function.update_of_ne e23.symm,Function.update_of_ne e3z.symm,hzc]
  obtain env3 : cacheTableEnv M.n ptbl tbl E (i+1) (tbl+16*M.n*i+8*M.n)=
      E (ptbl+24*M.n*i+16*M.n)*E (ptbl+24*M.n*i+16*M.n)*E (ptbl+24*M.n*i+16*M.n) := by
    simp only [cacheTableEnv,Naf.cacheOps,runOps,List.foldl_cons,List.foldl_nil,FOp.run,
      Function.update_self,Function.update_of_ne e3z.symm,hzc]
  obtain envo : ∀ x∈cacheTableSlots M.n tbl i++V,
      cacheTableEnv M.n ptbl tbl E (i+1) x=cacheTableEnv M.n ptbl tbl E i x := by
    intro x hx
    simp only [cacheTableEnv,Naf.cacheOps,runOps,List.foldl_cons,List.foldl_nil,FOp.run,
      Function.update_of_ne (n2 x hx).1,Function.update_of_ne (n2 x hx).2]
  obtain wt2 : wordsVal t.mem base (tbl+16*M.n*i) M.n=wordsVal u2.mem base e M.n := by
    rw [kt.2.1,w2]
  obtain wt3 : wordsVal t.mem base (tbl+16*M.n*i+8*M.n) M.n=wordsVal u2.mem base (e+8*M.n) M.n := by
    rw [kt.2.1,w3]
  refine ⟨ct,ft,keep,st,mt,hsl,fun x hx => ?_,fun x hx => ?_⟩
  · simp only [cacheTableSlots,List.append_assoc,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false] at hx
    rcases hx with (rfl|rfl)|hx
    · rw [wt2]; exact l2
    · rw [wt3]; exact l3
    · have hx' := List.mem_append.mpr hx
      rw [same x hx']; exact iu.lt x hx'
  · simp only [cacheTableSlots,List.append_assoc,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false] at hx
    rcases hx with (rfl|rfl)|hx
    · rw [wt2,v2,env2]
    · rw [wt3,v3,env3]
    · have hx' := List.mem_append.mpr hx
      rw [same x hx',iu.val x hx',envo x hx']

theorem mov32_rbx_zero_ok (s : State) :
    WP isa (.block [.mov32 .rbx (.imm 0)]) s fun t =>
      t.gpr .rbx=BitVec.ofNat 64 0 ∧ Keeps [.rbx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,readSrc32,State.setReg32,
    Option.map_some,RegUpd.gpr_setReg,ite_true,Option.some.injEq,exists_eq_left']
  exact ⟨rfl,fun r hr => by simp only [List.mem_singleton] at hr; simp only [RegUpd.gpr_setReg,hr,ite_false],rfl,rfl,rfl⟩

/-- The cache loop: `Z²` and `Z³` of the eight entries. -/
theorem nafCacheTable_fields_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hm : UnitMod m (2^(64*M.n)))
    {ptbl tbl e : Nat} {V : List Nat} (hC : CacheLoopLay M size Sl ptbl tbl e V)
    {E : Nat → Fin m} {s : State} (hI : Inv M base size m Sl V E s) :
    WP isa (Naf.cacheTable M ptbl tbl e).inline s fun t =>
      CacheLoopKeep M base tbl e s t ∧
      Inv M base size m Sl (cacheTableSlots M.n tbl 8++V) (cacheTableEnv M.n ptbl tbl E 8) t := by
  simp only [Naf.cacheTable,Code.inline]
  apply WP.seq
  refine WP.mono (mov32_rbx_zero_ok s) fun u ⟨cu,ku⟩ => ?_
  obtain k0 : CacheLoopKeep M base tbl e s u :=
    ⟨⟨fun r hr => ku.1 r (fun h => hr (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp h)))),ku.2.2.1,ku.2.2.2⟩,
      by rw [ku.2.1]; exact Unch.refl _ _ _⟩
  obtain i0 : Inv M base size m Sl (cacheTableSlots M.n tbl 0++V) (cacheTableEnv M.n ptbl tbl E 0) u :=
    ⟨hI.scr.of_keeps ku (by decide),by rw [ku.2.1]; exact hI.mod,hI.sl,
      fun x hx => by rw [ku.2.1]; exact hI.lt x hx,fun x hx => by rw [ku.2.1]; exact hI.val x hx⟩
  refine WP.loop (M:=isa)
    (fun r t => r≤7 ∧ t.gpr .rbx=BitVec.ofNat 64 (7-r) ∧ CacheLoopKeep M base tbl e s t ∧
      Inv M base size m Sl (cacheTableSlots M.n tbl (7-r)++V) (cacheTableEnv M.n ptbl tbl E (7-r)) t)
    (fun r t ⟨hr,ct,kt,it⟩ => ?_) 7 u ⟨by decide,cu,k0,i0⟩
  refine WP.mono (nafCacheStep_ok hL hm hC (by omega_arith) ct kt it) fun t ⟨c,f,k,i⟩ => ?_
  by_cases hr0 : r=0
  · subst r
    exact Or.inl ⟨f,k,i⟩
  · refine Or.inr ⟨?_,r-1,by omega_arith,by omega_arith,?_⟩
    · change t.cf=some true
      rw [f]; congr 1; exact decide_eq_true (by omega_arith)
    · rw [show 7-(r-1)=7-r+1 from by omega_arith]
      exact ⟨c,k,i⟩

/-- The cache's values after the eight entries, in terms of the state's. -/
theorem cacheTable_current {M : Mod} {base : Addr} {size : Nat} {C : Spec.Weierstrass.Curve}
    {Sl : Nat → Prop} {ptbl tbl e : Nat} {V : List Nat} (hC : CacheLoopLay M size Sl ptbl tbl e V)
    {E : Nat → Fin C.p} {t : State}
    (it : Inv M base size C.p Sl (cacheTableSlots M.n tbl 8++V) (cacheTableEnv M.n ptbl tbl E 8) t) :
    Inv M base size C.p Sl (cacheTableSlots M.n tbl 8++V) (tmv C M.n base t) t ∧
      ∀ i<8,tmv C M.n base t (tbl+16*M.n*i)=
          tmv C M.n base t (ptbl+24*M.n*i+16*M.n)*tmv C M.n base t (ptbl+24*M.n*i+16*M.n) ∧
        tmv C M.n base t (tbl+16*M.n*i+8*M.n)=
          tmv C M.n base t (tbl+16*M.n*i)*tmv C M.n base t (ptbl+24*M.n*i+16*M.n) := by
  refine ⟨it.to_tmv,fun i hi => ?_⟩
  obtain hn0 : 0<M.n := by have := hC.hn; omega_arith
  have v (x : Nat) (hx : x∈cacheTableSlots M.n tbl 8++V) :
      tmv C M.n base t x=cacheTableEnv M.n ptbl tbl E 8 x := it.val x hx
  obtain hz := hC.hz i hi
  obtain ze : cacheTableEnv M.n ptbl tbl E 8 (ptbl+24*M.n*i+16*M.n)=E (ptbl+24*M.n*i+16*M.n) :=
    cacheTableEnv_other 8 fun j hj => by
      have := entry_end_le (16*M.n) hj
      have := (hC.hv _ hz).2
      omega_arith
  obtain h := cacheTableEnv_entry (E:=E) hn0 hC.sep hi (Nat.le_refl 8)
  rw [v _ (List.mem_append_right _ hz),ze,
    v _ (List.mem_append_left _ (mem_cacheTableSlots.mpr ⟨i,hi,Or.inl rfl⟩)),
    v _ (List.mem_append_left _ (mem_cacheTableSlots.mpr ⟨i,hi,Or.inr rfl⟩))]
  exact h



/-- The loop's first `k` steps, one after the other. -/
theorem nafCacheSteps_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hm : UnitMod m (2^(64*M.n)))
    {ptbl tbl e : Nat} {V : List Nat} (hC : CacheLoopLay M size Sl ptbl tbl e V)
    {E : Nat → Fin m} {s : State} :
    ∀ k ≤ 8, ∀ {u : State}, u.gpr .rbx=BitVec.ofNat 64 0 → CacheLoopKeep M base tbl e s u →
      Inv M base size m Sl (cacheTableSlots M.n tbl 0++V) (cacheTableEnv M.n ptbl tbl E 0) u →
      WP isa (Naf.cacheSteps M ptbl tbl e k).inline u fun t =>
        t.gpr .rbx=BitVec.ofNat 64 k ∧ CacheLoopKeep M base tbl e s t ∧
        Inv M base size m Sl (cacheTableSlots M.n tbl k++V) (cacheTableEnv M.n ptbl tbl E k) t
  | 0, _, _, cu, ku, iu => WP.block_nil ⟨cu,ku,iu⟩
  | k+1, hk, u, cu, ku, iu => by
    simp only [Naf.cacheSteps,Code.inline]
    exact WP.seq (WP.mono (nafCacheSteps_ok hL hm hC k (by omega_arith) cu ku iu) fun t ⟨ct,kt,it⟩ =>
      WP.mono (nafCacheStep_ok hL hm hC (by omega_arith) ct kt it) fun t' ⟨c',_,k',i'⟩ => ⟨c',k',i'⟩)

/-- The loop's eight steps unrolled (`Naf.cacheStaged`): as the loop. -/
theorem nafCacheStaged_fields_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hm : UnitMod m (2^(64*M.n)))
    {ptbl tbl e : Nat} {V : List Nat} (hC : CacheLoopLay M size Sl ptbl tbl e V)
    {E : Nat → Fin m} {s : State} (hI : Inv M base size m Sl V E s) :
    WP isa (Naf.cacheStaged M ptbl tbl e).inline s fun t =>
      CacheLoopKeep M base tbl e s t ∧
      Inv M base size m Sl (cacheTableSlots M.n tbl 8++V) (cacheTableEnv M.n ptbl tbl E 8) t := by
  simp only [Naf.cacheStaged,Code.inline]
  apply WP.seq
  refine WP.mono (mov32_rbx_zero_ok s) fun u ⟨cu,ku⟩ => ?_
  obtain k0 : CacheLoopKeep M base tbl e s u :=
    ⟨⟨fun r hr => ku.1 r (fun h => hr (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp h)))),ku.2.2.1,ku.2.2.2⟩,
      by rw [ku.2.1]; exact Unch.refl _ _ _⟩
  obtain i0 : Inv M base size m Sl (cacheTableSlots M.n tbl 0++V) (cacheTableEnv M.n ptbl tbl E 0) u :=
    ⟨hI.scr.of_keeps ku (by decide),by rw [ku.2.1]; exact hI.mod,hI.sl,
      fun x hx => by rw [ku.2.1]; exact hI.lt x hx,fun x hx => by rw [ku.2.1]; exact hI.val x hx⟩
  exact WP.mono (nafCacheSteps_ok hL hm hC 8 (Nat.le_refl 8) cu k0 i0) fun _ ⟨_,k,i⟩ => ⟨k,i⟩

/-- `nafCacheTable_current_ok`, for the steps unrolled. -/
theorem nafCacheStaged_current_ok {M : Mod} {base : Addr} {size : Nat} {C : Spec.Weierstrass.Curve}
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hm : UnitMod C.p (2^(64*M.n)))
    {ptbl tbl e : Nat} {V : List Nat} (hC : CacheLoopLay M size Sl ptbl tbl e V)
    {E : Nat → Fin C.p} {s : State} (hI : Inv M base size C.p Sl V E s) :
    WP isa (Naf.cacheStaged M ptbl tbl e).inline s fun t =>
      CacheLoopKeep M base tbl e s t ∧
      Inv M base size C.p Sl (cacheTableSlots M.n tbl 8++V) (tmv C M.n base t) t ∧
      ∀ i<8,tmv C M.n base t (tbl+16*M.n*i)=
          tmv C M.n base t (ptbl+24*M.n*i+16*M.n)*tmv C M.n base t (ptbl+24*M.n*i+16*M.n) ∧
        tmv C M.n base t (tbl+16*M.n*i+8*M.n)=
          tmv C M.n base t (tbl+16*M.n*i)*tmv C M.n base t (ptbl+24*M.n*i+16*M.n) :=
  WP.mono (nafCacheStaged_fields_ok hL hm hC hI) fun _ ⟨kt,it⟩ => ⟨kt,cacheTable_current hC it⟩

/-- Each cache pair in terms of the source `Z` still in the resulting state. -/
theorem nafCacheTable_current_ok {M : Mod} {base : Addr} {size : Nat} {C : Spec.Weierstrass.Curve}
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hm : UnitMod C.p (2^(64*M.n)))
    {ptbl tbl e : Nat} {V : List Nat} (hC : CacheLoopLay M size Sl ptbl tbl e V)
    {E : Nat → Fin C.p} {s : State} (hI : Inv M base size C.p Sl V E s) :
    WP isa (Naf.cacheTable M ptbl tbl e).inline s fun t =>
      CacheLoopKeep M base tbl e s t ∧
      Inv M base size C.p Sl (cacheTableSlots M.n tbl 8++V) (tmv C M.n base t) t ∧
      ∀ i<8,tmv C M.n base t (tbl+16*M.n*i)=
          tmv C M.n base t (ptbl+24*M.n*i+16*M.n)*tmv C M.n base t (ptbl+24*M.n*i+16*M.n) ∧
        tmv C M.n base t (tbl+16*M.n*i+8*M.n)=
          tmv C M.n base t (tbl+16*M.n*i)*tmv C M.n base t (ptbl+24*M.n*i+16*M.n) :=
  WP.mono (nafCacheTable_fields_ok hL hm hC hI) fun _ ⟨kt,it⟩ => ⟨kt,cacheTable_current hC it⟩

/-! ## The cache unrolled -/

theorem nafCachePair_fields_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hm : UnitMod m (2^(64*M.n))) {ptbl tbl i : Nat}
    {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) (hZ : ptbl+24*M.n*i+16*M.n∈V)
    (h2 : Sl (tbl+16*M.n*i)) (h3 : Sl (tbl+16*M.n*i+8*M.n)) :
    WP isa (Naf.cachePair M ptbl tbl i).inline s fun t =>
      ProgKeep M base ((Naf.cachePairOps M.n ptbl tbl i).map FOp.out) s t ∧
      Inv M base size m Sl (validAfter (Naf.cachePairOps M.n ptbl tbl i) V)
        (runOps (Naf.cachePairOps M.n ptbl tbl i) E) t := by
  obtain hS : ∀ op∈Naf.cachePairOps M.n ptbl tbl i,∀ x∈op.out::op.ins,Sl x := by
    intro op hop x hx
    simp only [Naf.cachePairOps,List.mem_cons,List.not_mem_nil,or_false] at hop
    rcases hop with rfl|rfl <;>
      simp only [FOp.out,FOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
    · rcases hx with rfl|rfl|rfl
      · exact h2
      · exact hI.sl _ hZ
      · exact hI.sl _ hZ
    · rcases hx with rfl|rfl|rfl
      · exact h3
      · exact h2
      · exact hI.sl _ hZ
  obtain hR : readsOk (Naf.cachePairOps M.n ptbl tbl i) V=true := by
    simp [Naf.cachePairOps,readsOk,FOp.ins,FOp.out,hZ]
  rw [Naf.cachePair]
  split
  · rw [ForwardField.program_inline]
    exact WP.mono (ForwardField.program_ok (by assumption : M.adx ∧ M.n=4).2 hL hm _ hI hS hR
      (fun _ h => by cases h))
      (fun _ h => ⟨h.1,h.2.1⟩)
  · exact (fprogB_ok hL hm _ hI hS hR)

theorem nafCachePair_ok {M : Mod} {base : Addr} {size : Nat} {C : Spec.Weierstrass.Curve}
    {Sl : Nat → Prop} (hn : M.n=4 ∨ M.n=6 ∨ M.n=9) (hL : Lay M size Sl)
    (hm : UnitMod C.p (2^(64*M.n))) {ptbl tbl i : Nat}
    (hSep : tbl+16*M.n*(i+1)≤ptbl ∨ ptbl+24*M.n*(i+1)≤tbl)
    {V : List Nat} {E : Nat → Fin C.p} {s : State}
    (hI : Inv M base size C.p Sl V E s) (hZ : ptbl+24*M.n*i+16*M.n∈V)
    (h2 : Sl (tbl+16*M.n*i)) (h3 : Sl (tbl+16*M.n*i+8*M.n)) :
    WP isa (Naf.cachePair M ptbl tbl i).inline s fun t =>
      ProgKeep M base [tbl+16*M.n*i,tbl+16*M.n*i+8*M.n] s t ∧
      Inv M base size C.p Sl ([tbl+16*M.n*i,tbl+16*M.n*i+8*M.n]++V) (tmv C M.n base t) t ∧
      tmv C M.n base t (tbl+16*M.n*i)=E (ptbl+24*M.n*i+16*M.n)*E (ptbl+24*M.n*i+16*M.n) ∧
      tmv C M.n base t (tbl+16*M.n*i+8*M.n)=
        tmv C M.n base t (tbl+16*M.n*i)*E (ptbl+24*M.n*i+16*M.n) := by
  rw [Nat.mul_succ,Nat.mul_succ] at hSep
  obtain hz2 : ptbl+24*M.n*i+16*M.n≠tbl+16*M.n*i := by omega_arith
  obtain h23 : tbl+16*M.n*i≠tbl+16*M.n*i+8*M.n := by omega_arith
  obtain hp := nafCachePair_fields_ok hL hm hI hZ h2 h3
  refine WP.mono hp fun t ⟨kt,it⟩ => ?_
  obtain iv : Inv M base size C.p Sl ([tbl+16*M.n*i,tbl+16*M.n*i+8*M.n]++V)
      (runOps (Naf.cachePairOps M.n ptbl tbl i) E) t := it.sub (by
    intro x hx
    simp only [Naf.cachePairOps,validAfter,FOp.out,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false] at hx ⊢
    grind)
  obtain v2 := iv.val (tbl+16*M.n*i) (by simp)
  obtain v3 := iv.val (tbl+16*M.n*i+8*M.n) (by simp)
  simp only [Naf.cachePairOps,runOps,List.foldl_cons,List.foldl_nil,FOp.run,
    Function.update_self,Function.update_of_ne hz2,Function.update_of_ne h23] at v2 v3
  refine ⟨kt,iv.to_tmv,v2,?_⟩
  unfold tmv
  rw [v2]
  exact v3

theorem nafCacheUnrolled_ok {M : Mod} {base : Addr} {size : Nat} {C : Spec.Weierstrass.Curve}
    {Sl : Nat → Prop} (hn : M.n=4 ∨ M.n=6 ∨ M.n=9) (hL : Lay M size Sl)
    (hm : UnitMod C.p (2^(64*M.n))) (k : Nat) {ptbl tbl : Nat}
    (hSep : tbl+16*M.n*k≤ptbl ∨ ptbl+24*M.n*k≤tbl)
    {V : List Nat} {E : Nat → Fin C.p} {s : State}
    (hI : Inv M base size C.p Sl V E s) (hZ : ∀ i<k,ptbl+24*M.n*i+16*M.n∈V)
    (hSl : ∀ i<k,Sl (tbl+16*M.n*i) ∧ Sl (tbl+16*M.n*i+8*M.n)) :
    WP isa (Naf.cacheUnrolled M ptbl tbl k).inline s fun t =>
      ProgKeep M base (cacheTableSlots M.n tbl k) s t ∧
      Inv M base size C.p Sl (cacheTableSlots M.n tbl k++V) (tmv C M.n base t) t ∧
      ∀ i<k,tmv C M.n base t (tbl+16*M.n*i)=E (ptbl+24*M.n*i+16*M.n)*E (ptbl+24*M.n*i+16*M.n) ∧
        tmv C M.n base t (tbl+16*M.n*i+8*M.n)=tmv C M.n base t (tbl+16*M.n*i)*E (ptbl+24*M.n*i+16*M.n) := by
  induction k with
  | zero => exact WP.block_nil ⟨ProgKeep.refl _ _ _ s,hI.to_tmv,fun _ h => by omega_arith⟩
  | succ k ih =>
    obtain hk := entry_le (16*M.n) (show k≤k+1 by omega_arith)
    obtain hk' := entry_le (24*M.n) (show k≤k+1 by omega_arith)
    rw [Naf.cacheUnrolled]
    apply WP.seq
    refine WP.mono (ih (by omega_arith) (fun i hi => hZ i (by omega_arith))
      (fun i hi => hSl i (by omega_arith))) fun u ⟨ku,iu,hu⟩ => ?_
    obtain hW : ∀ x∈cacheTableSlots M.n tbl k,Sl x := by
      intro x hx
      obtain ⟨j,hj,rfl|rfl⟩ := mem_cacheTableSlots.mp hx
      · exact (hSl j (by omega_arith)).1
      · exact (hSl j (by omega_arith)).2
    obtain zu : tmv C M.n base u (ptbl+24*M.n*k+16*M.n)=E (ptbl+24*M.n*k+16*M.n) := by
      unfold tmv
      rw [ku.slot hL hI.scr hW (hI.sl _ (hZ k (by omega_arith))) ?_,hI.val _ (hZ k (by omega_arith))]
      intro hz
      obtain ⟨j,hj,hj'⟩ := mem_cacheTableSlots.mp hz
      have := entry_end_le (16*M.n) hj
      rw [Nat.mul_succ,Nat.mul_succ] at hSep
      omega_arith
    refine WP.mono (nafCachePair_ok hn hL hm hSep iu
      (List.mem_append_right _ (hZ k (by omega_arith)))
      (hSl k (by omega_arith)).1 (hSl k (by omega_arith)).2) fun t ⟨kt,it,h2,h3⟩ => ?_
    obtain hWp : ∀ x∈[tbl+16*M.n*k,tbl+16*M.n*k+8*M.n],Sl x := by
      intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl
      · exact (hSl k (by omega_arith)).1
      · exact (hSl k (by omega_arith)).2
    have old (x : Nat) (hx : Sl x) (hnot : x∉[tbl+16*M.n*k,tbl+16*M.n*k+8*M.n]) :
        tmv C M.n base t x=tmv C M.n base u x := by
      unfold tmv
      rw [kt.slot hL iu.scr hWp hx hnot]
    refine ⟨(ku.mono (fun _ h => List.mem_append_right _ h)).trans
      (kt.mono (fun _ h => List.mem_append_left _ h)),?_,fun i hi => ?_⟩
    · simpa only [cacheTableSlots,List.append_assoc] using it
    · by_cases he : i=k
      · subst i
        rw [zu] at h2 h3
        exact ⟨h2,h3⟩
      · have hik : i<k := by omega_arith
        have := entry_end_le (16*M.n) hik
        obtain e2 := old (tbl+16*M.n*i) (hSl i hi).1 (by
          simp only [List.mem_cons,List.not_mem_nil,or_false]; omega_arith)
        obtain e3 := old (tbl+16*M.n*i+8*M.n) (hSl i hi).2 (by
          simp only [List.mem_cons,List.not_mem_nil,or_false]; omega_arith)
        rw [e2,e3]
        exact hu i hik

/-- Express each cache pair in terms of the source Z still in the resulting state. -/
theorem nafCacheUnrolled_current_ok {M : Mod} {base : Addr} {size : Nat} {C : Spec.Weierstrass.Curve}
    {Sl : Nat → Prop} (hn : M.n=4 ∨ M.n=6 ∨ M.n=9) (hL : Lay M size Sl)
    (hm : UnitMod C.p (2^(64*M.n))) (k : Nat) {ptbl tbl : Nat}
    (hSep : tbl+16*M.n*k≤ptbl ∨ ptbl+24*M.n*k≤tbl)
    {V : List Nat} {E : Nat → Fin C.p} {s : State}
    (hI : Inv M base size C.p Sl V E s) (hZ : ∀ i<k,ptbl+24*M.n*i+16*M.n∈V)
    (hSl : ∀ i<k,Sl (tbl+16*M.n*i) ∧ Sl (tbl+16*M.n*i+8*M.n)) :
    WP isa (Naf.cacheUnrolled M ptbl tbl k).inline s fun t =>
      ProgKeep M base (cacheTableSlots M.n tbl k) s t ∧
      Inv M base size C.p Sl (cacheTableSlots M.n tbl k++V) (tmv C M.n base t) t ∧
      ∀ i<k,tmv C M.n base t (tbl+16*M.n*i)=
          tmv C M.n base t (ptbl+24*M.n*i+16*M.n)*tmv C M.n base t (ptbl+24*M.n*i+16*M.n) ∧
        tmv C M.n base t (tbl+16*M.n*i+8*M.n)=
          tmv C M.n base t (tbl+16*M.n*i)*tmv C M.n base t (ptbl+24*M.n*i+16*M.n) := by
  refine WP.mono (nafCacheUnrolled_ok hn hL hm k hSep hI hZ hSl) fun t ⟨kt,it,ht⟩ =>
    ⟨kt,it,fun i hi => ?_⟩
  obtain hW : ∀ x∈cacheTableSlots M.n tbl k,Sl x := by
    intro x hx
    obtain ⟨j,hj,rfl|rfl⟩ := mem_cacheTableSlots.mp hx
    · exact (hSl j hj).1
    · exact (hSl j hj).2
  obtain ze : tmv C M.n base t (ptbl+24*M.n*i+16*M.n)=E (ptbl+24*M.n*i+16*M.n) := by
    unfold tmv
    rw [kt.slot hL hI.scr hW (hI.sl _ (hZ i hi)) ?_,hI.val _ (hZ i hi)]
    intro hz
    obtain ⟨j,hj,hj'⟩ := mem_cacheTableSlots.mp hz
    have := entry_end_le (16*M.n) hj
    have := entry_end_le (16*M.n) hi
    have := entry_end_le (24*M.n) hi
    have := entry_le (24*M.n) (Nat.zero_le i)
    omega_arith
  rw [ze]
  exact ht i hi

end VG.Proof.Weierstrass.X86_64

end

end

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
