import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.RootTable
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def fiveGprs : List Reg := [.x2,.x3,.x4,.x5,.x7,.x8,.x10]
def fiveAdvance : List Instr := [.addImm .x .x2 .x2 128,
  .addImm .x .x3 .x3 480,.addImm .x .x4 .x4 480,.addImm .x .x5 .x5 480,
  .addImm .x .x7 .x7 480,.addImm .x .x8 .x8 480,.subImm .x .x10 .x10 1]

structure FiveAdvancePost (s t : State) : Prop where
  out : t.gpr .x2=s.gpr .x2+128
  x3 : t.gpr .x3=s.gpr .x3+480
  x4 : t.gpr .x4=s.gpr .x4+480
  x5 : t.gpr .x5=s.gpr .x5+480
  x7 : t.gpr .x7=s.gpr .x7+480
  x8 : t.gpr .x8=s.gpr .x8+480
  counter : t.gpr .x10=s.gpr .x10-1
  mem : t.mem=s.mem

theorem fiveAdvance_ok (s : State) :
    WP isa (.block fiveAdvance) s fun t =>
      (FiveAdvancePost s t ∧ Keep fiveGprs s t) ∧ t.v=s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold fiveAdvance
  arun
  constructor <;> rfl

private theorem root_inc (p : Addr) (u off : Nat) :
    (p+BitVec.ofNat 64 (480*u+off))+480=p+BitVec.ofNat 64 (480*(u+1)+off) := by
  rw [show 480*(u+1)+off=(480*u+off)+480 by omega]
  rw [BitVec.ofNat_add (480*u+off) 480,BitVec.add_assoc]
  rfl

theorem FiveAdvancePost.pointers {s t : State} {p : Addr} {u : Nat}
    (h : FiveAdvancePost s t) (hp : FivePointers s p u) : FivePointers t p (u+1) := by
  constructor
  · intro gap
    have he : t.gpr (innerBase gap)=s.gpr (innerBase gap)+480 := by
      unfold innerBase
      split
      · exact h.x3
      · split
        · exact h.x4
        · exact h.x5
    rw [he,hp.inner,root_inc]
  · intro len
    have he : t.gpr (tailBase len)=s.gpr (tailBase len)+480 := by
      unfold tailBase
      split
      · exact h.x7
      · exact h.x8
    rw [he,hp.tail,root_inc]

def fivePassMem (m : Mem) (p : Addr) (zi zt : Nat → Nat → Nat → Nat → Int) : Nat → Mem
  | 0 => m
  | u+1 => let m' := fivePassMem m p zi zt u
      let p' := p+BitVec.ofNat 64 (128*u)
      writeBank (fiveValues (readBank m' p' 16) (zi u) (zt u)) p' 16 m'

theorem fiveLoop_ok {s : State} {p : Addr} {r : Region} {zi zt : Nat → Nat → Nat → Nat → Int}
    (hT : RootTable s.mem p zi zt) (hptr : FivePointers s p 0)
    (hq : ∀ e < 4, vword (s.v .v16) e = 8380417#32)
    (hc : s.gpr .x10=8) (htr : expandedRegion p ∈ s.rd++s.wr) (hr : r ∈ s.wr)
    (hsep : (expandedRegion p).Disjoint r)
    (hcontains : ∀ u < 8, ∀ i : Fin 8, r.Contains
      ((s.gpr .x2+BitVec.ofNat 64 (128*u))+BitVec.ofNat 64 (16*i.val)) 16) :
    WP isa (.loop (.block (fiveSliceCode ++ fiveAdvance)) (.nonzero .x .x10)) s fun t =>
      Keep fiveGprs s t ∧ Frame [r] s.mem t.mem ∧ FivePointers t p 8 ∧
      t.gpr .x2=s.gpr .x2+1024 ∧ (∀ e < 4, vword (t.v .v16) e = 8380417#32) ∧
      t.mem=fivePassMem s.mem (s.gpr .x2) zi zt 8 := by
  let I := fun u t => Keep fiveGprs s t ∧ Frame [r] s.mem t.mem ∧ FivePointers t p u ∧
    t.gpr .x2=s.gpr .x2+BitVec.ofNat 64 (128*u) ∧
    (∀ e < 4, vword (t.v .v16) e = 8380417#32) ∧ t.mem=fivePassMem s.mem (s.gpr .x2) zi zt u
  apply VG.Proof.MlDsa.AArch64.Arith.wp_countdown (N := 8) (by decide) (by decide) I ?_ ?_ hc
  · intro u hu t ht _
    rcases ht with ⟨hk,hf,hp,hout,hqt,hm⟩
    have hTt := hT.frame hf (by intro r' hr'; have he := List.mem_singleton.mp hr'; subst r'; exact hsep)
    have roots := hTt.roots hu hp (by simpa only [hk.rd,hk.wr] using htr) hqt
    have hlocal : ∀ i : Fin 8, r.Contains (t.gpr .x2+BitVec.ofNat 64 (16*i.val)) 16 := by
      intro i
      rw [hout]
      exact hcontains u hu i
    refine fiveSlice_ok roots.1 roots.2 ?_ ?_ fun t₁ ⟨v,hv,hv₁⟩ => ?_
    · intro i
      exact ⟨r,List.mem_append_right _ (by simpa only [hk.wr] using hr),hlocal i⟩
    · intro i
      exact ⟨r,by simpa only [hk.wr] using hr,hlocal i⟩
    · have hk₁ : Keep [] t t₁ := (hv.keep.trans hv₁.keep).mono
      have hp₁ : FivePointers t₁ p u := by
        refine ⟨?_,?_⟩
        · simpa only [hv₁.gpr,hv.gpr] using hp.inner
        · simpa only [hv₁.gpr,hv.gpr] using hp.tail
      have hf₁ : Frame [r] s.mem t₁.mem := by
        rw [hv₁.mem]
        exact writeBank_frame _ _ _ (by simp) hlocal hf
      have hq₁ : ∀ e < 4, vword (t₁.v .v16) e = 8380417#32 := by
        intro e he
        rw [hv₁.v,hv.get .v16 (by decide)]
        exact hqt e he
      refine WP.mono (fiveAdvance_ok t₁) fun t₂ ⟨⟨ha,hk₂⟩,hvec₂⟩ => ?_
      refine ⟨⟨((hk.trans hk₁).trans hk₂).mono,?_,?_,?_,?_,?_⟩,?_⟩
      · simpa only [ha.mem] using hf₁
      · exact ha.pointers hp₁
      · rw [ha.out,hk₁.get .x2,hout]
        rw [show 128*(u+1)=128*u+128 by omega,BitVec.ofNat_add,BitVec.add_assoc]
        rfl
      · simpa only [hvec₂] using hq₁
      · rw [ha.mem,hv₁.mem]
        simp only [fiveSliceMem,hm,hout,fivePassMem]
      · rw [ha.counter,hk₁.get .x10]
        rfl
  · exact ⟨Keep.refl _ _,Frame.refl _ _,hptr,by simp,hq,rfl⟩

end VG.Proof.MlDsa.AArch64.Optimized
