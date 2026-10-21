module

import VerifiedGarbage.Proof.Mont.X86.CombStart
public import VerifiedGarbage.Proof.Mont.X86.CombColumns
public import VerifiedGarbage.Proof.Mont.X86.CombSubsets
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
public import VerifiedGarbage.Proof.Mont.X86.CombFrame
public import VerifiedGarbage.Proof.Mont.X86.PowerStep

/-! Compose initialization, column generation, and subset completion. -/

@[expose] public section
namespace VG.Proof.Mont.X86.Comb
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

/-- The arithmetic workspace and the retained context are the only writes. -/
def buildRanges (n context : Nat) : List (Nat × Nat) :=
  [(4,4),(28,4),(slot n 1,8*n),(slot n 2,16*n+4),
   (slot n 5,8*n),(slot n 6,8*n),(slot n 7,8*n),(context,272*n)]

theorem columns_prefix {n context size d : Nat} {base : Addr} {s t : Mem}
    (L : Layout n context size) (nw : base.toNat+size ≤ 2^32)
    (O : Outs base (columnRanges n context) s t)
    (lo : context ≤ d) (hi : d+8*n ≤ context+24*n) :
    wordsVal t base d n = wordsVal s base d n := by
  have h5 := L.slot (i := 5) (by decide)
  have h1 := L.slot (i := 1) (by decide)
  have h2 := L.slot (i := 3) (by decide)
  have hd := L.apart
  have hb := L.bound
  have hh := slot_header n 9
  change slot n 9 ≤ context at hd
  have sep : slot n 2 + (16*n+4) ≤ context := by
    simp only [slot,stride] at *; omega
  rw [wordsVal_eq_val32,wordsVal_eq_val32]
  exact O.val32 (by
    intro r hr; simp only [columnRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl <;> omega) (by omega)

theorem subsets_prefix {n context size d : Nat} {base : Addr} {s t : Mem}
    (L : Layout n context size) (nw : base.toNat+size ≤ 2^32)
    (O : Outs base (subsetRanges n context) s t)
    (lo : context ≤ d) (hi : d+8*n ≤ context+24*n) :
    wordsVal t base d n = wordsVal s base d n := by
  have h5 := L.slot (i := 5) (by decide)
  have h6 := L.slot (i := 6) (by decide)
  have h7 := L.slot (i := 7) (by decide)
  have h1 := L.slot (i := 1) (by decide)
  have hd := L.apart
  have hb := L.bound
  have hh := slot_header n 9
  change slot n 9 ≤ context at hd
  have sep : slot n 2 + (16*n+4) ≤ context := by
    simp only [slot,stride] at *; omega
  rw [wordsVal_eq_val32,wordsVal_eq_val32]
  exact O.val32 (by
    intro r hr; simp only [subsetRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega) (by omega)

theorem Columns.tableAt {n e context size m g : Nat} {base : Addr} {s t : State}
    (L : Layout n context size) (nw : base.toNat+size≤2^32)
    (I : Columns n context size m g (Spec.Rsa.FixedBaseComb.rows (32*e)) 4 base s t)
    (zeroEntry : wordsVal s.mem base (context+16*n) n=2^(64*n)%m) :
    TableAt n context m g (32*e) base (knownSubset 1) t.mem := by
  have bound := L.bound

  intro j hj hk
  rcases hk with zero | tooth
  · have eq : j=0 := by omega
    subst j
    have addr : entry n (context+16*n) 0 = context+16*n := by simp [entry]
    rw [addr,columns_prefix L nw I.mem (by omega) (by omega),zeroEntry]
    simp only [tableValue,VG.Proof.Rsa.FixedBaseComb.exponent_zero,VG.Proof.Bignum.powMod_eq,Nat.pow_zero]
    rw [Nat.mod_mul_mod,Nat.one_mul]
  · have jt : ∃ k, k≤4 ∧ j=2^k := by
      rcases tooth with rfl|rfl|rfl|rfl|rfl
      · exact ⟨0,by decide,rfl⟩
      · exact ⟨1,by decide,rfl⟩
      · exact ⟨2,by decide,rfl⟩
      · exact ⟨3,by decide,rfl⟩
      · exact ⟨4,by decide,rfl⟩
    obtain ⟨k,hk,rfl⟩ := jt
    rw [I.table k hk]
    unfold tableValue columnValue
    rw [VG.Proof.Rsa.FixedBaseComb.exponent_tooth _ _ (by omega),Nat.mul_comm k]


theorem build_ok {n e context size m : Nat} {base : Addr} {s : State}
    (L : Layout n context size) (C : Context n m base size s)
    (one : wordsVal s.mem base (slot n 3) n = 1)
    (r2 : wordsVal s.mem base (slot n 4) n = 2^(128*n) % m)
    (hd : 0 < Spec.Rsa.FixedBaseComb.rows (32*e))
    (hd32 : Spec.Rsa.FixedBaseComb.rows (32*e) < 2^32) :
    WP isa (VG.Impl.Mont.X86.Comb.combBuild n e context) s fun t =>
      Context n m base size t ∧
      wordsVal t.mem base context n = m ∧
      wordsVal t.mem base (context+8*n) n = 2^(128*n) % m ∧
      TableAt n context m (wordsVal s.mem base (slot n 5) n) (32*e) base (fun _ => True) t.mem ∧
      Outs base (buildRanges n context) s.mem t.mem ∧ Keeps powerClob s t := by
  have bound := L.bound
  have nw := C.scr.nowrap
  unfold VG.Impl.Mont.X86.Comb.combBuild VG.Impl.Mont.X86.Comb.seq
  simp only [List.foldr_cons,List.foldr_nil]
  refine WP.seq (WP.mono (buildStart_ok L C one r2) fun u ⟨Cu,Pu,Ru,Yu,Gu,Vu,Ou,Ku⟩ => ?_)
  have initial (g : Nat) : columnValue n m g (Spec.Rsa.FixedBaseComb.rows (32*e)) 0 = g*2^(64*n)%m := by
    simp only [columnValue,Nat.mul_zero,Nat.pow_zero,VG.Proof.Bignum.powMod_eq,Nat.pow_one]
    exact Nat.mod_mul_mod _ _ _
  refine WP.seq (WP.mono (buildColumns_ok L Cu hd hd32 (Vu.trans (initial _).symm)
    (Gu.trans (initial _).symm)) fun v I => ?_)
  have Tv := I.tableAt L nw Yu
  refine WP.seq (WP.mono (buildSubsets_ok L I.ctx Tv) fun t J => WP.block_nil ?_)
  refine ⟨J.ctx,?_,?_,?_,?_,(Ku.trans I.keeps).trans J.keeps⟩
  · rw [subsets_prefix L nw J.mem (by omega) (by omega),columns_prefix L nw I.mem (by omega) (by omega),Pu]
  · rw [subsets_prefix L nw J.mem (by omega) (by omega),columns_prefix L nw I.mem (by omega) (by omega),Ru]
  · intro j hj _; exact J.table j hj (.inl hj)
  · have a : Outs base (buildRanges n context) s.mem u.mem := Ou.mono (by
      intro r hr; simp only [startRanges,encodeRanges,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with (rfl|rfl|rfl|rfl)|rfl <;> simp [buildRanges])
    have b : Outs base (buildRanges n context) u.mem v.mem := widen I.mem (by
      intro r hr; simp only [columnRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl|rfl
      · exact ⟨_,by simp [buildRanges],Nat.le_refl _,Nat.le_refl _⟩
      · exact ⟨_,by simp [buildRanges],Nat.le_refl _,Nat.le_refl _⟩
      · exact ⟨_,by simp [buildRanges],Nat.le_refl _,Nat.le_refl _⟩
      · exact ⟨_,by simp [buildRanges],Nat.le_refl _,Nat.le_refl _⟩
      · exact ⟨(context,272*n),by simp [buildRanges],by omega,by omega⟩)
    have c : Outs base (buildRanges n context) v.mem t.mem := widen J.mem (by
      intro r hr; simp only [subsetRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact ⟨_,by simp [buildRanges],Nat.le_refl _,Nat.le_refl _⟩
      · exact ⟨_,by simp [buildRanges],Nat.le_refl _,Nat.le_refl _⟩
      · exact ⟨_,by simp [buildRanges],Nat.le_refl _,Nat.le_refl _⟩
      · exact ⟨_,by simp [buildRanges],Nat.le_refl _,Nat.le_refl _⟩
      · exact ⟨_,by simp [buildRanges],Nat.le_refl _,Nat.le_refl _⟩
      · exact ⟨_,by simp [buildRanges],Nat.le_refl _,Nat.le_refl _⟩
      · exact ⟨_,by simp [buildRanges],Nat.le_refl _,Nat.le_refl _⟩
      · exact ⟨(context,272*n),by simp [buildRanges],by omega,by omega⟩)
    exact (a.trans b).trans c

end VG.Proof.Mont.X86.Comb
