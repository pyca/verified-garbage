import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rel
import VerifiedGarbage.Proof.MlDsa.Pack.Coeffs
import VerifiedGarbage.Proof.MlKem.AArch64.Sample

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample
open VG.Proof.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.AArch64.Sample.Ball (CStored)

 theorem stored_bytes {m₁ m₂ : Mem} {a : Addr} {c : Spec.MlDsa.IPoly}
    (h₁ : CStored m₁ a c) (h₂ : CStored m₂ a c) {x : Addr} (hx : (polyR a).Contains x 1) : m₁ x=m₂ x := by
  apply Proof.MlDsa.Pack.bytes_of_words (N := 256) (p := a) ?_ hx
  apply List.map_congr_left
  intro j hj
  rw [h₁ j (List.mem_range.mp hj),h₂ j (List.mem_range.mp hj)]

structure ChunkReady (a b : Addr) (c : Spec.MlDsa.IPoly) (i : Nat) (w : BitVec 64)
    (L : List Byte) (s : State) : Prop where
  parser : Parser a c i w s
  x2 : s.gpr .x2=b
  x5 : (s.gpr .x5).toNat=L.length
  buf : ∀j<L.length,s.mem (b+BitVec.ofNat 64 j)=L.getD j 0
  reads : Covers [⟨b,L.length⟩,polyR a] (s.rd++s.wr)
  writes : Covers [polyR a] s.wr

 theorem chunk_relCT {τ i : Nat} {h : Array Bool} {a b : Addr} {c : Spec.MlDsa.IPoly} {w : BitVec 64}
    {L : List Byte} (hlen : 0<L.length) (hmax : L.length<2^64) (hi : i≤256)
    (hsep : (⟨b,L.length⟩ : Region).Disjoint (polyR a))
    (hsign : ∀j,i≤j → j<256 → (w >>> (j-i)).getLsbD 0=h.getD (j+τ-256) false) :
    RelCT isa (fun s t => ChunkReady a b c i w L s ∧ ChunkReady a b c i w L t ∧ s.sp=t.sp)
      Impl.MlDsa.AArch64.Optimized.Ball.loop (fun _ _ => True) := by
  let rd : List Region := [⟨b,L.length⟩]
  let wr : List Region := [polyR a]
  have run (s : State) (hs : ChunkReady a b c i w L s) :
      ∃tr u,Exec isa Impl.MlDsa.AArch64.Optimized.Ball.loop (s.withRegions rd wr) tr u := by
    obtain ⟨tr,u,he,_⟩ := chunk_ok (τ := τ) (h := h) (s₀ := s.withRegions rd wr) hlen hmax hi
      ⟨hs.parser.x26,hs.parser.x9,hs.parser.x10,hs.parser.x11,hs.parser.x12,hs.parser.x15,hs.parser.stored⟩ hs.x2 hs.x5 hs.buf
      (fun j hj => in_rd (in_regions (List.mem_singleton_self _) (Offset.contains_base _ (by omega) (by omega))))
      (fun j hj => in_regions (List.mem_singleton_self _) (coeff_contains _ hj)) hsep hsign
    exact ⟨tr,u,he⟩
  refine RelCT.narrow rd wr
    (fun s t ht => ⟨⟨ht.1.reads,ht.1.writes⟩,⟨ht.2.1.reads,ht.2.1.writes⟩⟩)
    (fun s t ht => ⟨run s ht.1,run t ht.2.1⟩)
    (RelCT.taint (A := memTaint) (Taint.ofRegs [.x2,.x5,.x9,.x10,.x11,.x12,.x15,.x26]) ?_ (by taint_decide))
  intro s t hp
  obtain ⟨s₀,t₀,⟨hs,ht,hsp⟩,rfl,rfl⟩ := hp
  refine ⟨agree_of hsp (fun r hr => ?_),rfl,rfl,fun x hx => ?_⟩
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact hs.x2.trans ht.x2.symm
    · exact BitVec.eq_of_toNat_eq (hs.x5.trans ht.x5.symm)
    · exact hs.parser.x9.trans ht.parser.x9.symm
    · exact BitVec.eq_of_toNat_eq (hs.parser.x10.trans ht.parser.x10.symm)
    · exact BitVec.eq_of_toNat_eq (hs.parser.x11.trans ht.parser.x11.symm)
    · exact BitVec.eq_of_toNat_eq (hs.parser.x12.trans ht.parser.x12.symm)
    · exact BitVec.eq_of_toNat_eq (hs.parser.x15.trans ht.parser.x15.symm)
    · exact hs.parser.x26.trans ht.parser.x26.symm
  · obtain ⟨r,hr,hx⟩ := hx
    rcases mem2 hr with rfl|rfl
    · obtain ⟨j,hj,rfl⟩ := Proof.MlKem.AArch64.Sample.at_off hx
      exact (hs.buf j hj).trans (ht.buf j hj).symm
    · exact stored_bytes hs.parser.stored ht.parser.stored hx
end VG.Proof.MlDsa.AArch64.Optimized.Ball
