import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallChunk

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (IPoly n)
open VG.Proof.MlDsa.AArch64.Sample.Ball (take_succ'')

abbrev Fold (τ : Nat) (h : Array Bool) (c : IPoly) (i : Nat) (L : List Byte) (t : Nat) :=
  bFold τ h (c,i) (L.take t)

theorem fold_end {τ : Nat} {h : Array Bool} {c : IPoly} {i t : Nat} {L : List Byte}
    (hd : (Fold τ h c i L t).2=256) : Fold τ h c i L L.length=Fold τ h c i L t := by
  simp only [Fold,List.take_length]
  calc
    bFold τ h (c,i) L = bFold τ h (c,i) (L.take t ++ L.drop t) := congrArg _ (List.take_append_drop t L).symm
    _ = Fold τ h c i L t := by rw [bFold_append,bFold_full hd]

structure ChunkAt (τ : Nat) (h : Array Bool) (a b : Addr) (c : IPoly) (i : Nat)
    (w : BitVec 64) (L : List Byte) (s₀ : State) (t : Nat) (s : State) : Prop where
  keep : Keep chunkRegs s₀ s
  frame : Frame [polyR a] s₀.mem s.mem
  x2 : s.gpr .x2=b+BitVec.ofNat 64 t
  x5 : (s.gpr .x5).toNat=L.length-t
  parser : Parser a (Fold τ h c i L t).1 (Fold τ h c i L t).2
    (w >>> ((Fold τ h c i L t).2-i)) s

structure ChunkPost (τ : Nat) (h : Array Bool) (a : Addr) (c : IPoly) (i : Nat)
    (w : BitVec 64) (L : List Byte) (s₀ s : State) : Prop where
  keep : Keep chunkRegs s₀ s
  frame : Frame [polyR a] s₀.mem s.mem
  parser : Parser a (Fold τ h c i L L.length).1 (Fold τ h c i L L.length).2
    (w >>> ((Fold τ h c i L L.length).2-i)) s

/-- Parse a nonempty finite byte chunk, stopping immediately after coefficient
256 is assigned. Unconsumed bytes then act identically in the pure fold. -/
theorem chunk_ok {τ i : Nat} {h : Array Bool} {a b : Addr} {c : IPoly} {w : BitVec 64}
    {L : List Byte} {s₀ : State} (hlen : 0<L.length) (hmax : L.length<2^64) (hi : i≤256)
    (hparser : Parser a c i w s₀) (h2 : s₀.gpr .x2=b) (h5 : (s₀.gpr .x5).toNat=L.length)
    (hbuf : ∀ j<L.length,s₀.mem (b+BitVec.ofNat 64 j)=L.getD j 0)
    (hin : ∀ j<L.length,InRegions (s₀.rd++s₀.wr) (b+BitVec.ofNat 64 j) 1)
    (hw : ∀ j<256,InRegions s₀.wr (coeffAddr a j) 4)
    (hsep : (⟨b,L.length⟩ : Region).Disjoint (polyR a))
    (hsign : ∀ j, i≤j → j<256 → (w >>> (j-i)).getLsbD 0=h.getD (j+τ-256) false) :
    WP isa Impl.MlDsa.AArch64.Optimized.Ball.loop s₀ (ChunkPost τ h a c i w L s₀) := by
  by_cases hd : i=256
  · refine WP.ite true (by rw [eval_zero,eq_zero_iff,hparser.x11,hd]; rfl)
      (fun _ => wp_nil ?_) (fun hh => nomatch hh)
    have he : Fold τ h c i L L.length=(c,i) := by
      simp only [Fold,List.take_length]; exact bFold_full hd _
    refine ⟨Keep.refl _ _,Frame.refl _ _,?_⟩
    simpa only [he,Nat.sub_self,BitVec.ushiftRight_zero] using hparser
  refine WP.ite false (by rw [eval_zero,eq_zero_iff,hparser.x11]; simp; omega)
    (fun hh => nomatch hh) (fun _ => ?_)
  let I : Nat → State → Prop := fun m s => ∃ t, m=L.length-t ∧ t<L.length ∧
    (Fold τ h c i L t).2<256 ∧ ChunkAt τ h a b c i w L s₀ t s
  refine WP.loop (M := isa) (body := Impl.MlDsa.AArch64.Optimized.Ball.earlyBody)
    (c := .nonzero .x .x5) I ?_ L.length s₀ ?_
  · rintro m s ⟨t,rfl,ht,hit,hs⟩
    have ge : i≤(Fold τ h c i L t).2 := bFold_ge (c,i) _
    have eqstep : Fold τ h c i L (t+1)=bStep τ h (Fold τ h c i L t) (L.getD t 0) := by
      simp only [Fold]; rw [take_succ'' L ht,bFold_snoc]
    have hmem : s.mem (s.gpr .x2)=L.getD t 0 := by
      rw [hs.x2,← hbuf t ht]
      exact hs.frame _ fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact hsep _ (Offset.contains_base _ (by omega) (by omega))
    have hp : Parser a (Fold τ h c i L t).1 (Fold τ h c i L t).2 (s.gpr .x9) s := by
      rw [hs.parser.x9]; exact hs.parser
    refine WP.mono (body_ok (τ := τ) (signs := h) (a := a) (c := (Fold τ h c i L t).1)
      (i := (Fold τ h c i L t).2) (b := L.length-t) (j := L.getD t 0) hit (by omega) (by omega) hp
      (by rw [hs.parser.x9]; exact hsign _ ge hit) hs.x5
      (by rw [hs.keep.rd,hs.keep.wr,hs.x2]; exact hin t ht) hmem
      (by rw [hs.keep.wr]; exact hw)) fun u ⟨ku,fu,u2,u5,up⟩ => ?_
    rw [← eqstep] at u5 up
    have gn : (Fold τ h c i L t).2≤(Fold τ h c i L (t+1)).2 := by
      rw [eqstep]; exact bStep_ge _ _
    have un : Parser a (Fold τ h c i L (t+1)).1 (Fold τ h c i L (t+1)).2
        (w >>> ((Fold τ h c i L (t+1)).2-i)) u := by
      rw [hs.parser.x9,← BitVec.shiftRight_add,
        show (Fold τ h c i L t).2-i+((Fold τ h c i L (t+1)).2-(Fold τ h c i L t).2) =
          (Fold τ h c i L (t+1)).2-i from by omega] at up
      exact up
    have kk : Keep chunkRegs s₀ u := (hs.keep.trans ku).mono (by decide)
    have ff := hs.frame.trans fu
    by_cases hf : (Fold τ h c i L (t+1)).2=256
    · refine .inl ⟨by rw [eval_nonzero,ne_zero_iff,u5,ifT hf]; rfl,kk,ff,?_⟩
      rw [fold_end hf]; exact un
    · rw [ifF hf] at u5
      by_cases he : t+1=L.length
      · refine .inl ⟨by rw [eval_nonzero,ne_zero_iff,u5]; simp; omega,kk,ff,?_⟩
        rwa [he] at un
      · refine .inr ⟨by rw [eval_nonzero,ne_zero_iff,u5]; simp; omega,L.length-(t+1),by omega,
          t+1,rfl,by omega,?_,kk,ff,?_,?_,un⟩
        · have := bFold_le (τ := τ) (h := h) (st := (c,i)) hi (L.take (t+1))
          change (Fold τ h c i L (t+1)).2≤256 at this
          omega
        · rw [u2,hs.x2,BitVec.add_assoc,BitVec.ofNat_add]; rfl
        · rw [u5]; omega
  · refine ⟨0,by omega,hlen,?_,Keep.refl _ _,Frame.refl _ _,?_,?_,?_⟩
    · simpa only [Fold,List.take_zero,bFold] using Nat.lt_of_le_of_ne hi hd
    · simpa using h2
    · simpa using h5
    · simpa only [Fold,List.take_zero,bFold,Nat.sub_self,BitVec.ushiftRight_zero] using hparser
end VG.Proof.MlDsa.AArch64.Optimized.Ball
