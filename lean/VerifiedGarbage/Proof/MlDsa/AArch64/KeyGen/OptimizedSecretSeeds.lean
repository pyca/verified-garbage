import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Seed4
import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.OptimizedSecrets

/-! ## From `OptimizedSecretCopy.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Call
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.Sha3 (bytesAt)

/-- One half of a 66-byte secret seed. The destination register was initialized
once before the two copies, as in the selected implementation. -/
theorem secretCopyPart_ok {S : Nat} {p : Params} (hF : PFacts p) {s : State}
    (L : Lay S kgR (kgW p) s) {j b : Nat} (hj : j<4) (hb : b=0∨b=32)
    (hd : s.gpr .x10=pa s (sc (1408+66*j))) :
    WP isa (.block (VG.Impl.MlKem.AArch64.copy32 .x28 (oSB+b) .x10 b)) s fun t=>
      PPostB S s t [(sc (1408+66*j+b),32)] ∧ Keep [.x9] s t ∧
      bytesAt t.mem (pa s (sc (1408+66*j+b))) 32=bytesAt s.mem (pa s (sc (oSB+b))) 32 := by
  have hkl:=hF.kl; have hl:=hF.l; have hk:=hF.k; have hsc:=scr_eq p
  have hb64 : b+32≤64 := by omega
  have hb8 : b%8=0 := by rcases hb with rfl|rfl <;> decide
  have he : pa s (sc (1408+66*j))+BitVec.ofNat 64 b=pa s (sc (1408+66*j+b)) := sc_add _ _ _
  have hsep : sepB kgR (kgW p) (sc (oSB+b)) 32 (sc (1408+66*j+b)) 32=true := by layd
  have hread : inB (kgR++kgW p) (sc (oSB+b)) 32=true := by layd
  have hwrite : inB (kgW p) (sc (1408+66*j+b)) 32=true := by layd
  refine WP.mono (Proof.MlKem.AArch64.KeyGen.copy_ok (S := s.gpr .x28)
    (D := pa s (sc (1408+66*j))) (sb := .x28) (db := .x10) (so := oSB+b) (dO := b)
    (by decide) (by decide) (by dsimp only [oSB]; omega) ⟨hb8,by omega⟩
    (by rw [he]; change (⟨pa s (sc (oSB+b)),32⟩ : Region).Disjoint ⟨pa s (sc (1408+66*j+b)),32⟩; exact L.disj hsep) rfl hd
    (by change Covers [⟨pa s (sc (oSB+b)),32⟩] (s.rd++s.wr); exact L.cR hread) (by rw [he]; exact L.cW hwrite)) fun t ⟨ht,hf,hv⟩=>?_
  rw [he] at hf hv
  exact ⟨postB_of_keep ht (by decide) hf,ht,hv⟩


theorem secretSeedCopy_ok {S : Nat} {p : Params} (hF : PFacts p) {s : State}
    (L : Lay S kgR (kgW p) s) {j : Nat} (hj : j<4) :
    WP isa (.block (VG.Impl.MlDsa.AArch64.KeyGen.Optimized.secretSeedCopy j)) s fun t=>
      PPostB S s t [(sc (1408+66*j),32),(sc (1408+66*j+32),32)] ∧
      Keep [.x9,.x10] s t ∧
      bytesAt t.mem (pa s (sc (1408+66*j))) 64=bytesAt s.mem (pa s (sc oSB)) 64 := by
  have hkl:=hF.kl; have hl:=hF.l; have hk:=hF.k; have hsc:=scr_eq p
  unfold VG.Impl.MlDsa.AArch64.KeyGen.Optimized.secretSeedCopy
  rw [List.append_assoc]
  refine lea_ok (by decide) _ fun s1 h1 e1=>?_
  have hP1 : PPostB S s s1 [] := postB_of_keep h1.keep (by decide)
    (by rw [h1.mem]; exact Frame.refl _ _)
  have L1:=L.post hP1
  rw [WP.block_append_iff]
  refine WP.mono (secretCopyPart_ok hF L1 hj (b := 0) (Or.inl rfl)
    (by rw [sc_pa hP1]; exact e1)) fun s2 ⟨hP2,hk2,hb2⟩=>?_
  have L2:=L1.post hP2
  refine WP.mono (secretCopyPart_ok hF L2 hj (b := 32) (Or.inr rfl)
    (by rw [hk2.get .x10,sc_pa hP2,sc_pa hP1]; exact e1)) fun t ⟨hP3,hk3,hb3⟩=>?_
  have hP23:=PPostB.trans hP2 hP3 (by simp) (ws := [(sc (1408+66*j),32),(sc (1408+66*j+32),32)])
    (by simp) (by simp)
  refine ⟨PPostB.trans hP1 hP23 (by simp) (by simp) (fun _ h=>h),
    ((h1.keep.trans hk2).trans hk3).mono (by simp),?_⟩
  rw [VG.Proof.MlKem.bytesAt_add t.mem _ 32 32,VG.Proof.MlKem.bytesAt_add s.mem _ 32 32,sc_add,sc_add]
  have hkeep : keepB kgR (kgW p) [(sc (1408+66*j+32),32)] (sc (1408+66*j)) 32=true := by layd
  have hsrc : keepB kgR (kgW p) [(sc (1408+66*j),32)] (sc (oSB+32)) 32=true := by layd
  have hlo:=L2.keepBytes hP3 hkeep
  have hhi:=L1.keepBytes hP2 hsrc
  simp only [sc_pa hP3,sc_pa hP2,sc_pa hP1,Nat.add_zero] at hlo hhi hb2 hb3
  rw [hlo,hb2,hb3,hhi,h1.mem]

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized

end

/-! ## From `OptimizedSecretSeeds.lean` -/

section

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

end
