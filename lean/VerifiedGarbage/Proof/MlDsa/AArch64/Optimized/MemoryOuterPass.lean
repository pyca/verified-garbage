import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryBank
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemorySchedule
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TraversalBank
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.OuterLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Representation

/-! ## From `MemoryOuter.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

/-- Memory supplies the strided bank's field interpretation. -/
theorem readBank_outer_field {m : Mem} {p : Addr} {w : Poly} {lo hi : Int}
    (h : SignedPolyIs m p w lo hi) {u : Nat} (hu : u<8) :
    BankField u (readBank m (coeffAddr p (4*u)) 128) w := by
  intro i e he
  rw [readBank_coeff m p (4*u) 32 i he]
  have hi : 4*u+32*i.val+e<n := by change 4*u+32*i.val+e<256; omega
  simpa only [Traversal.loc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h.value _ hi

/-- One complete strided slice advances the global field schedule without
changing any coefficient outside that slice. -/
theorem outerMemStep_field {m : Mem} {p : Addr} {w : Poly} {u : Nat} (hu : u<8)
    (h : SignedPolyIs m p w (-(15*8380417)) (15*8380417))
    (hb : BankBound (readBank m (coeffAddr p (4*u)) 128) 8380417) :
    SignedPolyIs (outerMemStep m (coeffAddr p (4*u)) (fun k => (zetaNat k : Int))) p
      (Traversal.run (Traversal.outerSlice u) w) (-(15*8380417)) (15*8380417) := by
  have hc := outerThree_field _ w hu hb (readBank_outer_field h hu)
  have bound : 4*u+32*7+4≤256 := by omega
  have atCoeff (k : Nat) (hk : k<n) (hu' : k%32/4=u) :
      coeffAt (outerMemStep m (coeffAddr p (4*u)) (fun k => (zetaNat k : Int))) p k =
      vword (outerValues (readBank m (coeffAddr p (4*u)) 128)
        (fun k => (zetaNat k : Int)) outerSteps)[k/32]! (k%4) := by
    have hi : k/32<8 := by change k<256 at hk; omega
    have he : k=4*u+32*(k/32)+k%4 := by omega
    unfold outerMemStep
    have hh := writeBank_coeff_at
      (outerValues (readBank m (coeffAddr p (4*u)) 128) (fun k => (zetaNat k : Int)) outerSteps)
      m p (by decide : 4≤32) bound ⟨k/32,hi⟩ (e := k%4) (by omega)
    rw [← he] at hh
    simpa only [getElem!_pos (outerValues (readBank m (coeffAddr p (4*u)) 128) (fun k => (zetaNat k : Int)) outerSteps) (k/32) hi] using hh
  have outside (k : Nat) (hk : k<n) (hu' : k%32/4≠u) :
      coeffAt (outerMemStep m (coeffAddr p (4*u)) (fun k => (zetaNat k : Int))) p k=coeffAt m p k := by
    unfold outerMemStep
    apply writeBank_coeff_outside (step := 32) (start := 4*u) _ _ _ bound hk
    intro i
    omega
  constructor
  · intro k hk
    by_cases hu' : k%32/4=u
    · rw [atCoeff k hk hu']
      have hi : k/32<8 := by change k<256 at hk; omega
      simpa only [getElem!_pos (outerValues (readBank m (coeffAddr p (4*u)) 128) (fun k => (zetaNat k : Int)) outerSteps) (k/32) hi] using hc.1 ⟨k/32,hi⟩ (k%4) (by omega)
    · rw [outside k hk hu']; exact h.bound k hk
  · intro k hk
    by_cases hu' : k%32/4=u
    · rw [atCoeff k hk hu']
      have hi : k/32<8 := by change k<256 at hk; omega
      have he : Traversal.loc u (k/32) (k%4)=k := by unfold Traversal.loc; omega
      simpa only [getElem!_pos (outerValues (readBank m (coeffAddr p (4*u)) 128) (fun k => (zetaNat k : Int)) outerSteps) (k/32) hi,he] using hc.2 ⟨k/32,hi⟩ (k%4) (by omega)
    · rw [outside k hk hu',h.value k hk,
        Traversal.run_outside _ _ _ (Traversal.outer_supported ⟨u,hu⟩) w hk hu']

end VG.Proof.MlDsa.AArch64.Optimized

end

/-! ## From `MemoryOuterPass.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- Earlier outer slices do not touch the canonical inputs of a later slice. -/
theorem outerPass_untouched (m : Mem) (p : Addr) (z : Nat → Int) {u k : Nat}
    (hu : u≤8) (hk : k<n) (hbefore : u≤k%32/4) :
    coeffAt (outerPassMem m p z u) p k=coeffAt m p k := by
  induction u with
  | zero => rfl
  | succ u ih =>
    rw [outerPassMem]
    unfold outerMemStep
    have hp : p+BitVec.ofNat 64 (16*u)=coeffAddr p (4*u) := by
      simp only [coeffAddr,show 4*(4*u)=16*u by omega]
    rw [hp]
    rw [writeBank_coeff_outside (step := 32) (start := 4*u) _ _ _ (by omega) hk (by
      intro i
      have hmod : k%32/4≠u := by omega
      omega)]
    exact ih (by omega) (by omega)

theorem canonicalWord_int (x : BitVec 32) (hx : x.toNat<q) : x.toInt=(x.toNat : Int) := by
  apply BitVec.toInt_eq_toNat_of_lt
  change x.toNat<8380417 at hx
  omega

theorem canonicalWord_field (x : BitVec 32) (hx : x.toNat<q) :
    ofInt x.toInt=ofNat x.toNat := by
  rw [canonicalWord_int x hx]
  apply Fin.ext
  change ((x.toNat : Int) % (q : Int)).toNat % q=x.toNat % q
  rw [← Int.natCast_emod,Int.toNat_natCast,Nat.mod_mod]

theorem canonical_signed {m : Mem} {p : Addr} {w : Poly} (h : PolyIs m p w) :
    SignedPolyIs m p w (-(15*8380417)) (15*8380417) := by
  constructor
  · intro k hk
    rw [canonicalWord_int _ (h.1 k hk)]
    have hb := h.1 k hk
    change (coeffAt m p k).toNat<8380417 at hb
    omega
  · intro k hk
    rw [canonicalWord_field _ (h.1 k hk),← polyAt_get _ _ hk,h.2]

/-- Composing all processed outer slices preserves a single global polynomial
interpretation; the next slice still reads its original canonical words. -/
theorem outerPass_field {m : Mem} {p : Addr} {w : Poly} (h : PolyIs m p w)
    {u : Nat} (hu : u≤8) :
    SignedPolyIs (outerPassMem m p (fun k => (zetaNat k : Int)) u) p
      (Traversal.run ((List.range u).flatMap Traversal.outerSlice) w) (-(15*8380417)) (15*8380417) := by
  induction u with
  | zero => exact canonical_signed h
  | succ u ih =>
    have hu' : u<8 := by omega
    have hb : BankBound (readBank (outerPassMem m p (fun k => (zetaNat k : Int)) u)
        (coeffAddr p (4*u)) 128) 8380417 := by
      intro i e he
      rw [readBank_coeff _ p (4*u) 32 i he]
      have hk : 4*u+32*i.val+e<n := by change 4*u+32*i.val+e<256; omega
      rw [outerPass_untouched m p _ (by omega) hk (by omega),canonicalWord_int _ (h.1 _ hk)]
      have hq := h.1 _ hk
      change (coeffAt m p (4*u+32*i.val+e)).toNat<8380417 at hq
      omega
    have hs := outerMemStep_field hu' (ih (by omega)) hb
    have hp : p+BitVec.ofNat 64 (16*u)=coeffAddr p (4*u) := by
      simp only [coeffAddr,show 4*(4*u)=16*u by omega]
    simpa only [outerPassMem,hp,List.range_succ,List.flatMap_append,
      List.flatMap_singleton,Traversal.run_append] using hs

theorem outerPass_all {m : Mem} {p : Addr} {w : Poly} (h : PolyIs m p w) :
    SignedPolyIs (outerPassMem m p (fun k => (zetaNat k : Int)) 8) p
      (Traversal.run Traversal.outerSchedule w) (-(15*8380417)) (15*8380417) :=
  outerPass_field h (by decide)

end VG.Proof.MlDsa.AArch64.Optimized

end
