module
public import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.Descriptor
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Cmac.Spec

/-! Source and destination boundaries for a single descriptor. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.DirectGather
open VG VG.X86_64 Gather
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)
variable {s t : State} {M : CtxMode} {i pre : Nat}
abbrev dp (s : State) (i : Nat) := Src s+BitVec.ofNat 64 (16*i)
abbrev qPtr (s : State) (pre i : Nat) := sb s i+BitVec.ofNat 64 (skip pre i)
abbrev dPtr (s : State) (pre i : Nat) := Dst s+BitVec.ofNat 64 (consumed s pre i)
abbrev sz (s : State) (pre i : Nat) := sl s i-skip pre i
structure Geometry (s : State) (pre i : Nat) : Prop where
  skipBound : skip pre i≤sl s i
  pref : pre≤consumed s pre i
  total : consumed s pre i+sz s pre i≤L s
  next : consumed s pre (i+1)=consumed s pre i+sz s pre i
  plainLen : (plainPrefix s pre i).length=consumed s pre i
  plainNext : plainPrefix s pre (i+1)=plainPrefix s pre i ++ bytesAt s.mem (qPtr s pre i) (sz s pre i)

theorem geometry (h : Layout M s) (a : LoopAt M s pre i t) (hi : i<Cnt s) : Geometry s pre i := by
  have bound : gl s i + sl s i ≤ L s := h.glen ▸ (gl_succ s i ▸ gl_mono s (Nat.succ_le_of_lt hi))
  have first : pre≤sl s 0 := a.inFirst (by omega)
  cases i with
  | zero =>
    have eq : bytesAt s.mem (sb s 0) (sl s 0) = bytesAt s.mem (sb s 0) pre ++
        bytesAt s.mem (sb s 0+BitVec.ofNat 64 pre) (sl s 0-pre) := by
      rw [← bytesAt_add,Nat.add_sub_of_le first]
    have pt0 : pt s 0=[] := List.eq_nil_of_length_eq_zero (by rw [length_pt,gl_zero])
    rw [gl_zero,Nat.zero_add] at bound
    refine ⟨first,?_,?_,?_,?_,?_⟩
    · simp [consumed,skip,gl_zero]
    · simp [consumed,skip,gl_zero,sz]; omega
    · simp [consumed,skip,gl_succ,gl_zero,sz]; omega
    · simp [plainPrefix,consumed,skip,gl_zero,length_bytesAt]
    · simpa [plainPrefix,pt_succ,pt0,sz,qPtr,skip] using eq
  | succ j =>
    have atleast : pre≤gl s (j+1) := by
      apply Nat.le_trans first
      have g := gl_mono s (show 1≤j+1 by omega)
      have e : gl s 1=sl s 0 := by rw [show 1=0+1 from rfl,gl_succ,gl_zero,Nat.zero_add]
      exact e ▸ g
    refine ⟨by simp [skip],by simpa [consumed,skip] using atleast,by simpa [consumed,skip,sz] using bound,
      ?_,?_,?_⟩
    · simp [consumed,skip,sz,gl_succ]
    · simp [plainPrefix,consumed,skip,length_pt]
    · simp [plainPrefix,pt_succ,sz,qPtr,skip]

private theorem dsApart (h : Layout M s) : ∀ r∈changed s,(dsR s).Disjoint r := by
  intro r hr; simp only [changed,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · exact h.ds_w
  · exact h.ds_d
  · exact (h.b_ds.sub_left (below_sub (by decide) (by decide))).symm

theorem descriptor_input (h : Layout M s) (a : LoopAt M s pre i t) (hi : i<Cnt s) :
    DescriptorInput (W s) (dp s i) (sb s i) (Dst s+BitVec.ofNat 64 pre)
      (sl s i) (skip pre i) (consumed s pre i-pre) t := by
  have sub (off : Nat) (ho : off+8≤16) :
      (dsR s).Contains (dp s i+BitVec.ofNat 64 off) 8 := by
    rw [dp,BitVec.add_assoc,← BitVec.ofNat_add]
    exact Offset.contains_base _ (by omega) (by have := h.w_ds; omega)
  have f0 : (dsR s).Contains (dp s i) 8 := by simpa using sub 0 (by decide)
  have f8 := sub 8 (by decide)
  have covers : Covers [dsR s] (t.rd++t.wr) := by
    rw [a.rd,a.wr,h.rd]; exact covers_of_mem (by simp)
  refine ⟨a.env.r15,a.env.perm.w,a.desc,a.frame.readW f0 (dsApart h) (by decide),?_,a.skipAt,
    a.span,a.data,covers _ _ ⟨_,List.mem_singleton_self _,f0⟩,covers _ _ ⟨_,List.mem_singleton_self _,f8⟩⟩
  rw [a.frame.readW f8 (dsApart h) (by decide)]; simp [sl,dp]

theorem geometry_data (h : Layout M s) (a : LoopAt M s pre i t) (hi : i<Cnt s) :
    DataOk (W s+16#64) (W s) (SP s) t (qPtr s pre i) (sz s pre i) ∧
    DataW (K s) (W s+16#64) (W s) (SP s) t (dPtr s pre i) (sz s pre i) ∧
    (⟨qPtr s pre i,sz s pre i⟩ : Region).Disjoint ⟨dPtr s pre i,sz s pre i⟩ := by
  have g := geometry h a hi
  have m := slice_mem s hi
  obtain ⟨qd,_,qw⟩ := h.ls _ m
  have d := ((h.oneCtx M.ge).data.of_eq a.rd a.wr).drop (Nat.le_trans (Nat.le_add_right ..) g.total)
  have src : DataOk (W s+16#64) (W s) (SP s) t (sb s i) (sl s i) := by
    refine ⟨?_,BitVec.isLt _,h.w_ls _ m,qw.sub_right (Lay.wSub (by decide)),qw,
      (h.b_ls _ m).sub_left (below_sub (by decide) (by decide))⟩
    rw [a.rd,a.wr,h.rd]; exact covers_of_mem (by simp [m])
  exact ⟨src.drop g.skipBound,d.take (by have := g.total; omega),
    (qd.sub_left (Offset.sub_base _ (by have := g.skipBound; dsimp [sz]; omega))).sub_right
      (Offset.sub_base _ g.total)⟩

end VG.Proof.AesGcm.X86_64.DirectGather
