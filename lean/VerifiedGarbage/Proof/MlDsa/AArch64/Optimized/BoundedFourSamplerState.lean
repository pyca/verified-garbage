import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejState
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentSeed

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

abbrev samplerSeed := ResidentRej.seedP
abbrev samplerOut := ResidentRej.aP
abbrev samplerScratch := ResidentRej.scr
abbrev samplerAt := ResidentRej.at'
abbrev SamplerEnv := ResidentRej.Env 4

def samplerSeeds (s : State) : Region := ⟨samplerSeed s,264⟩
def samplerOutput (s : State) : Region := ⟨samplerOut s,4096⟩
def samplerWorkspace (s : State) : Region := ⟨samplerScratch s,8192⟩
def samplerSeedAt (s : State) (i : Nat) : Addr := samplerSeed s+BitVec.ofNat 64 (66*i)
def samplerA (s : State) (i : Nat) : Spec.Sha3.State := ResidentMask.seedState s.mem (samplerSeedAt s i)

structure SamplerPre (s : State) : Prop where
 rd : s.rd=[samplerSeeds s]
 wr : s.wr=[samplerOutput s,samplerWorkspace s]
 seed_output : (samplerSeeds s).Disjoint (samplerOutput s)
 seed_work : (samplerSeeds s).Disjoint (samplerWorkspace s)
 output_work : (samplerOutput s).Disjoint (samplerWorkspace s)

theorem sampler_in_work {σ s : State} (hp : SamplerPre σ) (hw : s.wr=σ.wr)
    {d n : Nat} (hd : d+n≤8192) : InRegions s.wr (samplerAt σ d) n := by
  rw [hw,hp.wr]
  exact ⟨samplerWorkspace σ,by simp,Offset.contains_base (samplerScratch σ) hd (by omega)⟩

theorem sampler_in_seed {σ s : State} (hp : SamplerPre σ) (hr : s.rd=σ.rd)
    {d n : Nat} (hd : d+n≤264) : InRegions (s.rd++s.wr) (samplerSeed σ+BitVec.ofNat 64 d) n := by
  rw [hr,hp.rd]
  exact ⟨samplerSeeds σ,by simp,Offset.contains_base (samplerSeed σ) hd (by omega)⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
