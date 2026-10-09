import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejScalarTiming

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (eval_nonzero)
open VG.Impl.MlDsa.AArch64.Sample
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

private theorem guard_nonzero {s : State} (he : isa.eval (.nonzero .x .x16) s=some true)
    (hg : s.gpr .x16=s.gpr .x4*s.gpr .x5) :
    (s.gpr .x4).toNat≠0 ∧ (s.gpr .x5).toNat≠0 := by
  have hn : s.gpr .x16≠0#64 := by
    intro hz
    rw [eval_nonzero,hz] at he
    contradiction
  constructor
  · intro hz
    have hx : s.gpr .x4=0#64 := BitVec.eq_of_toNat_eq hz
    apply hn
    rw [hg,hx,BitVec.zero_mul]
  · intro hz
    have hx : s.gpr .x5=0#64 := BitVec.eq_of_toNat_eq hz
    apply hn
    rw [hg,hx,BitVec.mul_zero]

theorem scalarLoop_relCT {σ τ : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (hm : InputEq σ τ b n) (hsp : σ.sp=τ.sp) (hd : d<n)
    (hc : (parsed σ b L d).length<256) :
    RelCT isa (fun s t => ParseInv σ b p n L d s ∧ ParseInv τ b p n L d t)
      (.loop (.block (scalarChunk++rnAccept++([.mul .x .x16 .x4 .x5] : List Instr)))
        (.nonzero .x .x16)) (fun _ _ => True) := by
  let I := fun m s t => ∃j,j<n ∧ (parsed σ b L j).length<256 ∧ n-j=m ∧
    ParseInv σ b p n L j s ∧ ParseInv τ b p n L j t
  have hstep : ∀m,RelCT isa (I m)
      (.block (scalarChunk++rnAccept++([.mul .x .x16 .x4 .x5] : List Instr)))
      (fun s t => isa.eval (.nonzero .x .x16) s=isa.eval (.nonzero .x .x16) t ∧
        (isa.eval (.nonzero .x .x16) s=some false → True) ∧
        (isa.eval (.nonzero .x .x16) s=some true → ∃m'<m,I m' s t)) := by
    intro m s t tr ur s' t' hp es et
    obtain ⟨j,hj,hc',rfl,hp⟩ := hp
    obtain ⟨htrace,ha,hb,heq,hga,hgb⟩ := scalarLoopStep_relCT hs ht hm hsp hj hc' _ _ _ _ _ _ hp es et
    refine ⟨htrace,by rw [eval_nonzero,eval_nonzero,heq],fun _ => trivial,?_⟩
    intro hcontinue
    obtain ⟨h4,h5⟩ := guard_nonzero hcontinue hga
    rw [ha.x4] at h4
    rw [ha.x5] at h5
    have hj' : j+1<n := by have := ha.bound; omega
    have hc'' : (parsed σ b L (j+1)).length<256 := by omega
    exact ⟨n-(j+1),by omega,j+1,hj',hc'',rfl,ha,hb⟩
  exact (RelCT.loop I hstep (n-d)).mono
    (fun _ _ hp => ⟨d,hd,hc,rfl,hp⟩) (fun _ _ h => h)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
