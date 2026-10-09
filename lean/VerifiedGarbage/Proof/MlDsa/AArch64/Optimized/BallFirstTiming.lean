import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallFirst
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallChunkTiming

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample
open VG.Proof.MlDsa.AArch64.Sample

structure FirstReady (a b : Addr) (τ : Nat) (X : List Byte) (s : State) : Prop where
  x25 : s.gpr .x25+840=b
  x26 : s.gpr .x26=a
  x27 : (s.gpr .x27).toNat=τ
  buf : ∀j<136,s.mem (b+BitVec.ofNat 64 j)=X.getD j 0
  zero : ∀j<256,Spec.MlDsa.coeffAt s.mem a j=0
  reads : Covers [⟨b,136⟩,polyR a] (s.rd++s.wr)
  writes : Covers [polyR a] s.wr

 theorem first_relCT {a b : Addr} {τ : Nat} {X : List Byte} (hX : X.length=136) (hτ : τ≤64)
    (hsep : (⟨b,136⟩ : Region).Disjoint (polyR a)) :
    RelCT isa (fun s t => FirstReady a b τ X s ∧ FirstReady a b τ X t ∧ s.sp=t.sp)
      Impl.MlDsa.AArch64.Optimized.Ball.first (fun _ _ => True) := by
  let rd : List Region := [⟨b,136⟩]
  let wr : List Region := [polyR a]
  have run (s : State) (hs : FirstReady a b τ X s) :
      ∃tr u,Exec isa Impl.MlDsa.AArch64.Optimized.Ball.first (s.withRegions rd wr) tr u := by
    obtain ⟨tr,u,he,_⟩ := first_ok (τ := τ) (s := s.withRegions rd wr) hX hs.x25 hs.x26 hs.x27 hτ
      (in_rd (in_regions (List.mem_singleton_self _) (by simp [Region.Contains])))
      (fun j hj => in_rd (in_regions (List.mem_singleton_self _) (Offset.contains_base _ (by omega) (by omega))))
      hs.buf (fun j hj => in_regions (List.mem_singleton_self _) (coeff_contains _ hj)) hsep hs.zero
    exact ⟨tr,u,he⟩
  refine RelCT.narrow rd wr
    (fun s t ht => ⟨⟨ht.1.reads,ht.1.writes⟩,⟨ht.2.1.reads,ht.2.1.writes⟩⟩)
    (fun s t ht => ⟨run s ht.1,run t ht.2.1⟩)
    (RelCT.taint (A := memTaint) (Taint.ofRegs [.x25,.x26,.x27]) ?_ (by taint_decide))
  intro s t hp
  obtain ⟨s₀,t₀,⟨hs,ht,hsp⟩,rfl,rfl⟩ := hp
  refine ⟨agree_of hsp (fun r hr => ?_),rfl,rfl,fun x hx => ?_⟩
  · rcases mem3 hr with rfl|rfl|rfl
    · change s₀.gpr .x25=t₀.gpr .x25
      have hh := congrArg (fun z : BitVec 64 => z-840) (hs.x25.trans ht.x25.symm)
      simpa only [BitVec.add_sub_cancel] using hh
    · exact hs.x26.trans ht.x26.symm
    · exact BitVec.eq_of_toNat_eq (hs.x27.trans ht.x27.symm)
  · obtain ⟨r,hr,hx⟩ := hx
    rcases mem2 hr with rfl|rfl
    · obtain ⟨j,hj,rfl⟩ := Proof.MlKem.AArch64.Sample.at_off hx
      exact (hs.buf j hj).trans (ht.buf j hj).symm
    · exact (Proof.MlKem.AArch64.Sample.byte_zero hs.zero hx).trans
        (Proof.MlKem.AArch64.Sample.byte_zero ht.zero hx).symm
end VG.Proof.MlDsa.AArch64.Optimized.Ball
