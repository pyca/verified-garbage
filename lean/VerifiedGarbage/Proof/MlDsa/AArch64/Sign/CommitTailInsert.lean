import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailUpper

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (wp_vop)
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

def replaceWord (B : Spec.Sha3.State) (j : Nat) (w : BitVec 64) : Spec.Sha3.State :=
  Vector.ofFn fun i => if i.val=j then w else B[i]

theorem replaceWord_get (B : Spec.Sha3.State) (j : Nat) (w : BitVec 64)
    (i : Nat) (hi : i<25) :
    (replaceWord B j w)[i]! = if i=j then w else B[i]! := by
  rw [VG.Proof.Sha3.getElem!_eq _ hi,VG.Proof.Sha3.getElem!_eq B hi]
  simp only [replaceWord,Vector.getElem_ofFn,Fin.getElem_fin]

/-- A single high-lane insertion preserves every scalar register and the
independent low-lane SHAKE state. -/
theorem insertHigh_ok {s : State} {A B : Spec.Sha3.State} {j : Nat} {r : Reg}
    (hj : j<25) (hp : Pairs s A B) :
    WP isa (.block [.vop (.ins .d2 (vreg j) 1 r)]) s fun t =>
      RegKeep [] s t ∧ t.mem=s.mem ∧ Pairs t A (replaceWord B j (s.gpr r)) := by
  refine wp_vop (d:=vreg j) rfl fun t ht => WP.block_nil_iff.mpr
    ⟨RegKeep.vupd ht,ht.mem,?_⟩
  intro i hi
  by_cases he : i=j
  · subst i
    rw [ht.v,hp j hj,upper_pair,replaceWord_get _ _ _ _ hj,ite_eq_left rfl]
  · have hij : vreg i≠vreg j := by rw [ne_eq,vreg_inj i (by omega) j (by omega)]; exact he
    rw [ht.get _ hij,hp i hi,replaceWord_get _ _ _ _ hi,ite_eq_right he]

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
