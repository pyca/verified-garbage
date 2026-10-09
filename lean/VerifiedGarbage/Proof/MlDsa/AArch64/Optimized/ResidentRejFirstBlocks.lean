import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFive
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSqueezeSetup

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlDsa.AArch64.Optimized.Resident (permuted StreamOutput)
open VG.Proof.MlDsa.AArch64.Sample.Rej4 (bReg)

structure FirstBlocks (v : Nat) (σ t : State) : Prop where
  env : Env v σ t
  pairs : ∀p,2*p+1<v → PairAt t.mem (stateP σ p)
    (permuted (A0 σ (2*p)) 5) (permuted (A0 σ (2*p+1)) 5)
  bytes : ∀k<v,StreamOutput t.mem (bufP σ k) 10 5 (A0 σ k)
  counts : ∀k<v,t.mem.readW (countP σ k) 64=256

theorem firstFour_ok {σ s : State} (hp : Pre 4 σ) (he : Env 4 σ s)
    (hs : ∀p,2*p+1<4 → PairAt s.mem (stateP σ p) (A0 σ (2*p)) (A0 σ (2*p+1)))
    (hc : ∀k<4,s.mem.readW (countP σ k) 64=256)
    (h22 : s.gpr .x22=stateP σ 0) (h23 : s.gpr .x23=stateP σ 1)
    (hbuf : ∀k<4,s.gpr (bReg k)=bufP σ k) :
    WP isa (.seq (Impl.MlDsa.AArch64.Optimized.ResidentRej.five .x22 .x24 .x25)
      (Impl.MlDsa.AArch64.Optimized.ResidentRej.five .x23 .x26 .x27)) s (FirstBlocks 4 σ) := by
  apply WP.seq
  refine WP.mono (fiveEnv_ok hp he (by decide : 2*0+1<4) fiveRegisters0
    (hs 0 (by decide)) h22 (hbuf 0 (by decide)) (hbuf 1 (by decide)))
    fun u ⟨heu,hpu,hu0,hu1,hfu,hgu⟩ => ?_
  refine WP.mono (fiveEnv_ok hp heu (by decide : 2*1+1<4) fiveRegisters1
    (five_pair_keep (by decide : 0<2) (by decide : 1<2) (by decide) hfu (hs 1 (by decide)))
    (by rw [hgu .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h23)
    (by rw [hgu .x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hbuf 2 (by decide))
    (by rw [hgu .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hbuf 3 (by decide)))
    fun t ⟨het,hpt,ht2,ht3,hft,_⟩ => ?_
  refine ⟨het,?_,?_,?_⟩
  · intro p hpn
    rcases (show p=0 ∨ p=1 by omega) with rfl | rfl
    · exact five_pair_keep (by decide : 1<2) (by decide : 0<2) (by decide) hft hpu
    · exact hpt
  · intro k hk
    rcases (show k=0 ∨ k=1 ∨ k=2 ∨ k=3 by omega) with rfl | rfl | rfl | rfl
    · exact five_stream_keep (by decide : 1<2) (by decide : 0<4) (by decide) (by decide) hft hu0
    · exact five_stream_keep (by decide : 1<2) (by decide : 1<4) (by decide) (by decide) hft hu1
    · exact ht2
    · exact ht3
  · intro k hk
    rw [five_count_keep (by decide : 1<2) hk hft,five_count_keep (by decide : 0<2) hk hfu]
    exact hc k hk

theorem firstTwo_ok {σ s : State} (hp : Pre 2 σ) (he : Env 2 σ s)
    (hs : ∀p,2*p+1<2 → PairAt s.mem (stateP σ p) (A0 σ (2*p)) (A0 σ (2*p+1)))
    (hc : ∀k<2,s.mem.readW (countP σ k) 64=256)
    (h22 : s.gpr .x22=stateP σ 0)
    (hbuf : ∀k<2,s.gpr (bReg k)=bufP σ k) :
    WP isa (Impl.MlDsa.AArch64.Optimized.ResidentRej.five .x22 .x24 .x25) s (FirstBlocks 2 σ) := by
  refine WP.mono (fiveEnv_ok hp he (by decide : 2*0+1<2) fiveRegisters0
    (hs 0 (by decide)) h22 (hbuf 0 (by decide)) (hbuf 1 (by decide)))
    fun t ⟨het,hpt,ht0,ht1,hft,_⟩ => ?_
  refine ⟨het,?_,?_,?_⟩
  · intro p hpn
    have : p=0 := by omega
    subst p; exact hpt
  · intro k hk
    rcases (show k=0 ∨ k=1 by omega) with rfl | rfl
    · exact ht0
    · exact ht1
  · intro k hk
    rw [five_count_keep (by decide : 0<2) (by omega : k<4) hft]
    exact hc k hk

theorem firstFour_setup_ok {σ s : State} (hp : Pre 4 σ) (he : Env 4 σ s)
    (hs : ∀p,2*p+1<4 → PairAt s.mem (stateP σ p) (A0 σ (2*p)) (A0 σ (2*p+1)))
    (hc : ∀k<4,s.mem.readW (countP σ k) 64=256) :
    WP isa (.seq (.block (Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.squeezeSetup 0 5))
      (.seq (Impl.MlDsa.AArch64.Optimized.ResidentRej.five .x22 .x24 .x25)
        (Impl.MlDsa.AArch64.Optimized.ResidentRej.five .x23 .x26 .x27))) s (FirstBlocks 4 σ) := by
  apply WP.seq
  refine WP.mono (squeezeSetupZero_env he) fun t ⟨het,hm,h22,h23,hbuf⟩ => ?_
  exact firstFour_ok hp het (by simpa only [hm] using hs) (by simpa only [hm] using hc) h22 h23 hbuf

theorem firstTwo_setup_ok {σ s : State} (hp : Pre 2 σ) (he : Env 2 σ s)
    (hs : ∀p,2*p+1<2 → PairAt s.mem (stateP σ p) (A0 σ (2*p)) (A0 σ (2*p+1)))
    (hc : ∀k<2,s.mem.readW (countP σ k) 64=256) :
    WP isa (.seq (.block (Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.squeezeSetup 0 5))
      (Impl.MlDsa.AArch64.Optimized.ResidentRej.five .x22 .x24 .x25)) s (FirstBlocks 2 σ) := by
  apply WP.seq
  refine WP.mono (squeezeSetupZero_env he) fun t ⟨het,hm,h22,_,hbuf⟩ => ?_
  exact firstTwo_ok hp het (by simpa only [hm] using hs) (by simpa only [hm] using hc)
    h22 (fun k hk => hbuf k (by omega))

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
