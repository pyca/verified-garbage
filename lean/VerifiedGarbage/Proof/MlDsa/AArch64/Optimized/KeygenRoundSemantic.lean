import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenRoundMemory

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenRound
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (pR)
open VG.Proof.MlDsa.AArch64.Arith.Neon (coeffAt_write16 vword_read16 vector_contains)

theorem readWord (m : Mem) (p : Addr) (j : Nat) {e : Nat} (he : e<4) :
    vword (m.read (p+BitVec.ofNat 64 (16*j)) 16) e=coeffAt m p (4*j+e) := by
  rw [show 16*j=4*(4*j) by omega]
  change vword (m.read (coeffAddr p (4*j)) 16) e=_
  rw [VG.AArch64.vword_read16 _ _ he,coeffAddr_add]
  rfl

theorem writeOther {m : Mem} {p o : Addr} {j k : Nat} {v : BitVec 128}
    (hd : (pR p).Disjoint (pR o)) (hj : j<64) (hk : k<256) :
    coeffAt (m.write (o+BitVec.ofNat 64 (16*j)) 16 v) p k=coeffAt m p k := by
  have hf : Frame [pR o] m (m.write (o+BitVec.ofNat 64 (16*j)) 16 v) := by
    rw [show 16*j=4*(4*j) by omega]
    exact (Frame.refl _ _).write (by simp) _ (vector_contains o (by omega))
  exact coeffAt_frame hf (by simpa using hd) hk

theorem roundStep_high {m : Mem} {input high low : Addr} {j k : Nat}
    (hd : (pR high).Disjoint (pR low)) (hj : j<64) (hk : k<256) :
    coeffAt (roundStep input high low j m) high k=
      if 4*j≤k ∧ k<4*j+4 then highWord (coeffAt m input k) else coeffAt m high k := by
  unfold roundStep
  rw [writeOther hd hj hk,show 16*j=4*(4*j) by omega]
  change coeffAt (m.write (coeffAddr high (4*j)) 16 _) high k=_
  rw [coeffAt_write16 _ _ (by omega) _ hk]
  split
  · rename_i h
    change vword (wordVector _) (k-4*j)=_
    rw [wordVector_word _ (by omega)]
    have hr := readWord m input j (e:=k-4*j) (by omega)
    rw [show 16*j=4*(4*j) by omega,show 4*j+(k-4*j)=k by omega] at hr
    rw [hr]
  · rfl

theorem roundStep_low {m : Mem} {input high low : Addr} {j k : Nat}
    (hd : (pR high).Disjoint (pR low)) (hj : j<64) (hk : k<256) :
    coeffAt (roundStep input high low j m) low k=
      if 4*j≤k ∧ k<4*j+4 then lowWord (coeffAt m input k) else coeffAt m low k := by
  unfold roundStep
  rw [show 16*j=4*(4*j) by omega]
  rw [coeffAt_write16 _ _ (by omega) _ hk]
  split
  · rename_i h
    change vword (wordVector _) (k-4*j)=_
    rw [wordVector_word _ (by omega)]
    have hr := readWord m input j (e:=k-4*j) (by omega)
    rw [show 16*j=4*(4*j) by omega,show 4*j+(k-4*j)=k by omega] at hr
    rw [hr]
  · simpa only [show 16*j=4*(4*j) by omega] using
      (writeOther (m:=m) (p:=low) (o:=high) (j:=j) (k:=k)
        (v:=highVector (m.read (input+BitVec.ofNat 64 (4*(4*j))) 16)) hd.symm hj hk)

theorem roundRun_frame (m : Mem) (input high low : Addr) {j : Nat} (hj : j≤64) :
    Frame [pR high,pR low] m (roundRun m input high low j) := by
  induction j with
  | zero => exact Frame.refl _ _
  | succ j ih =>
    rw [roundRun_next]
    unfold roundStep
    rw [show 16*j=4*(4*j) by omega]
    exact ((ih (by omega)).write (by simp) _ (vector_contains high (by omega))).write
      (by simp) _ (vector_contains low (by omega))

theorem roundRun_prefix (m : Mem) (input high low : Addr)
    (hih : (pR input).Disjoint (pR high)) (hil : (pR input).Disjoint (pR low))
    (hhl : (pR high).Disjoint (pR low)) {j : Nat} (hj : j≤64) :
    ∀k<256,
      (coeffAt (roundRun m input high low j) high k=if k<4*j then highWord (coeffAt m input k) else coeffAt m high k) ∧
      (coeffAt (roundRun m input high low j) low k=if k<4*j then lowWord (coeffAt m input k) else coeffAt m low k) := by
  induction j with
  | zero => intro k hk; simp [roundRun]
  | succ j ih =>
    have hp := ih (by omega)
    have input_kept : ∀k<256,coeffAt (roundRun m input high low j) input k=coeffAt m input k := by
      intro k hk
      exact coeffAt_frame (roundRun_frame m input high low (by omega))
        (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl|rfl; exact hih; exact hil) hk
    intro k hk
    rw [roundRun_next,roundStep_high hhl (by omega) hk,roundStep_low hhl (by omega) hk]
    rw [(hp k hk).1,(hp k hk).2,input_kept k hk]
    by_cases before : k<4*j
    · simp only [ite_eq_right (by omega : ¬(4*j≤k ∧ k<4*j+4)),ite_eq_left before,ite_eq_left (by omega : k<4*(j+1))]
      exact ⟨trivial,trivial⟩
    · by_cases inside : k<4*j+4
      · simp only [ite_eq_left (by omega : 4*j≤k ∧ k<4*j+4),ite_eq_left (by omega : k<4*(j+1))]
        exact ⟨trivial,trivial⟩
      · simp only [ite_eq_right (by omega : ¬(4*j≤k ∧ k<4*j+4)),ite_eq_right before,ite_eq_right (by omega : ¬k<4*(j+1))]
        exact ⟨trivial,trivial⟩

end VG.Proof.MlDsa.AArch64.Optimized.KeygenRound
