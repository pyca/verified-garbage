import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejOutcome
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Verified

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64

def twoPreProps (s : State) : Prop := s.rd=[seedsR 2 s] ∧ s.wr=[aR 2 s,scrR s] ∧
  (seedsR 2 s).Disjoint (aR 2 s) ∧ (seedsR 2 s).Disjoint (scrR s) ∧
  (aR 2 s).Disjoint (scrR s)

theorem pre_two {σ : State} (h : (Spec.MlDsa.rejNTT2Contract AArch64.abi).pre σ) : Pre 2 σ := by
  have hp : ∀s,(Spec.MlDsa.rejNTT2Contract AArch64.abi).pre s → twoPreProps s := by
    sig_implies_pre [Spec.MlDsa.rejNTT2Contract,Spec.MlDsa.rejNTT2Sig,twoPreProps,
      seedsR,aR,scrR,seedP,aP,scr,AArch64.abi,AArch64.argRegs,
      VG.Proof.MlDsa.AArch64.Sample.Rej4.seedP,VG.Proof.MlDsa.AArch64.Sample.Rej4.aP,
      VG.Proof.MlDsa.AArch64.Sample.Rej4.scr,VG.Proof.MlDsa.AArch64.Sample.Rej4.scrR]
  obtain ⟨hr,hw,hsa,hss,has⟩ := hp σ h
  exact ⟨Or.inl rfl,hr,hw,hsa,hss,has⟩

theorem two_correct {σ : State} (h : (Spec.MlDsa.rejNTT2Contract AArch64.abi).pre σ) :
    WP isa Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code σ fun t =>
      abiPreserved σ t ∧ Outcome 2 σ t :=
  WP.mono (two_ok (pre_two h)) fun _ ht => ⟨ht.abi,ht.outcome⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
