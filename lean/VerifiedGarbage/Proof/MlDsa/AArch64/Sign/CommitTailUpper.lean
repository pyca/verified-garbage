import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailUpperWord
import VerifiedGarbage.Proof.Framework.Range

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

def seedPrefix (B : Spec.Sha3.State) (m : Mem) (p : Addr) (n : Nat) : Spec.Sha3.State :=
  Vector.ofFn fun i => if i.val<n then m.readW (p+BitVec.ofNat 64 (8*i.val)) 64 else B[i]

theorem seedPrefix_get (B : Spec.Sha3.State) (m : Mem) (p : Addr) (n i : Nat) (hi : i<25) :
    (seedPrefix B m p n)[i]! = if i<n then m.readW (p+BitVec.ofNat 64 (8*i)) 64 else B[i]! := by
  rw [VG.Proof.Sha3.getElem!_eq _ hi,VG.Proof.Sha3.getElem!_eq B hi]
  simp only [seedPrefix,Vector.getElem_ofFn,Fin.getElem_fin]

/-- Seed loads only replace the high lanes. -/
theorem upperWord_step {s : State} {A B : Spec.Sha3.State} {m : Mem} {p : Addr} {j : Nat}
    (hj : j<8) (hm : s.mem=m) (h4 : s.gpr .x4=p)
    (hp : Pairs s A (seedPrefix B m p j))
    (hin : InRegions (s.rd++s.wr) (p+BitVec.ofNat 64 (8*j)) 8) :
    WP isa (.block [.ldr .x .x7 .x4 (8*j),.vop (.ins .d2 (vreg j) 1 .x7)]) s fun t =>
      RegKeep [.x7] s t ∧ t.mem=m ∧ Pairs t A (seedPrefix B m p (j+1)) := by
  refine WP.mono (upperWord_ok ⟨by omega,by omega⟩ (by rw [h4]; exact hin))
    fun t ⟨hk,hmt,hv,ht⟩ => ⟨hk,hmt.trans hm,?_⟩
  intro i hi
  by_cases he : i=j
  · subst i
    rw [ht,hp j (by omega),upper_pair,hm,h4,seedPrefix_get _ _ _ _ _ (by omega),ite_eq_left (by omega)]
  · have hij : vreg i≠vreg j := by rw [ne_eq,vreg_inj i (by omega) j (by omega)]; exact he
    rw [hv _ hij,hp i hi,seedPrefix_get _ _ _ _ _ hi,seedPrefix_get _ _ _ _ _ hi]
    have hc : (i<j)↔(i<j+1) := by omega
    simp only [hc]

/-- All eight seed words are loaded without disturbing the commitment. -/
theorem upperWords_ok {s : State} {A B : Spec.Sha3.State} (hp : Pairs s A B)
    (hin : ∀j<8, InRegions (s.rd++s.wr) (s.gpr .x4+BitVec.ofNat 64 (8*j)) 8) :
    WP isa (.block ((List.range 8).flatMap fun j =>
      ([.ldr .x .x7 .x4 (8*j),.vop (.ins .d2 (vreg j) 1 .x7)] : List Instr))) s fun t =>
      RegKeep [.x7] s t ∧ t.mem=s.mem ∧ Pairs t A (seedPrefix B s.mem (s.gpr .x4) 8) := by
  let I := fun j t => RegKeep [.x7] s t ∧ t.mem=s.mem ∧
    Pairs t A (seedPrefix B s.mem (s.gpr .x4) j)
  have hz : seedPrefix B s.mem (s.gpr .x4) 0=B := by
    apply Vector.ext
    intro i hi
    simp only [seedPrefix,Vector.getElem_ofFn,Nat.not_lt_zero,ite_false,Fin.getElem_fin]
  refine wp_range_flatMap (M:=isa) I (fun j t hj ht => ?_) 8 (Nat.le_refl _) s ?_
  · rcases ht with ⟨hk,hm,hp⟩
    refine WP.mono (upperWord_step hj hm (hk.gpr .x4 (by decide)) hp ?_)
      fun u ⟨hk',hm',hp'⟩ => ⟨(hk.trans hk').mono (by simp),hm',hp'⟩
    rw [hk.rd,hk.wr]
    exact hin j hj
  · exact ⟨RegKeep.refl _ _,rfl,by rw [hz]; exact hp⟩

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
