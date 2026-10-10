import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecretCopy

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Call
open VG.Proof.MlDsa.KeyGen (seedS)
open VG.Spec.Sha3 (bytesAt)

structure SecretSeeds (p : Params) (σ : State) (r : Nat) (nonce : Nat→Nat) (j : Nat) (s : State) : Prop where
 ks : KSamp p σ (p.k*p.ℓ) r s
 done : ∀k<j,bytesAt s.mem (pa s (sc (1408+66*k))) 66=seedS (rho'Of p σ) (nonce k)

def secretSlotCode (j n : Nat) : Prog isa := .block
 (VG.Impl.MlDsa.AArch64.KeyGen.Optimized.secretSeedCopy j ++
   setB (sc (1408+66*j+64)) n ++ setB (sc (1408+66*j+65)) 0)

theorem secretSlot_ok {p : Params} (hF : PFacts p) {S : Nat} {σ : State} (hp : kgPre p S σ)
    {r j : Nat} (hr : r≤p.ℓ+p.k) (hj : j<4) {nonce : Nat→Nat} (hn : nonce j<256)
    {s : State} (h : SecretSeeds p σ r nonce j s) :
    WP isa (secretSlotCode j (nonce j)) s (SecretSeeds p σ r nonce (j+1)) := by
  have hkl:=hF.kl; have hl:=hF.l; have hk:=hF.k; have hsc:=scr_eq p
  have L:=h.ks.k1.kc.lay hF hp
  unfold secretSlotCode
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (secretSeedCopy_ok hF L hj) fun s1 ⟨hP1,hk1,hb1⟩=>?_
  have h1:=h.ks.keep hF hp hP1 (by unfold k1Chk kcChk; layd)
    (fun k hk=>by layd) (fun k hk=>by layd) (hk1.get .x24)
  have L1:=h1.k1.kc.lay hF hp
  refine WP.mono (setTwo_ok L1 (o := 1408+66*j+64) (a := nonce j) (b := 0)
    (by omega) (by layd) (by layd)) fun t ⟨hP2,hk2,hb2⟩=>?_
  refine ⟨h1.keep hF hp hP2 (by unfold k1Chk kcChk; layd)
    (fun k hk=>by layd) (fun k hk=>by layd) (hk2.get .x24),fun k hk=>?_⟩
  by_cases he : k=j
  · subst k
    rw [VG.Proof.MlKem.bytesAt_add t.mem _ 64 2,L1.keepBytes hP2 (by layd),
      sc_pa hP2,sc_pa hP1,hb1,h.ks.k1.sb,
      sc_add,←sc_pa hP1,hb2,VG.Proof.MlDsa.KeyGen.seedS_eq _ hn]
    rfl
  · rw [L1.keepBytes hP2 (by layd),L.keepBytes hP1 (by layd)]
    exact h.done k (by omega)


def secretSeedsCode (nonce : Nat→Nat) : List Instr :=
 (List.range 4).flatMap fun j=>VG.Impl.MlDsa.AArch64.KeyGen.Optimized.secretSeedCopy j ++
   setB (sc (1408+66*j+64)) (nonce j) ++ setB (sc (1408+66*j+65)) 0

theorem secretSeeds_ok {p : Params} (hF : PFacts p) {S : Nat} {σ : State} (hp : kgPre p S σ)
    {r : Nat} (hr : r≤p.ℓ+p.k) {nonce : Nat→Nat} (hn : ∀j<4,nonce j<256)
    {s : State} (h : KSamp p σ (p.k*p.ℓ) r s) :
    WP isa (.block (secretSeedsCode nonce)) s (SecretSeeds p σ r nonce 4) := by
  exact wp_range_flatMap (M := isa) (N := 4) (fun j t=>SecretSeeds p σ r nonce j t)
    (fun j t hj ht=>secretSlot_ok hF hp hr hj (hn j hj) ht) 4 (by omega) s
    ⟨h,fun _ hi=>False.elim (Nat.not_lt_zero _ hi)⟩

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
