import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedHCountField

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

theorem passHintSum_field {m : Mem} {work challenge secret out aux : Addr} {e g n : Nat}
    (hn : n≤8) (he : e<4) (hg : IsG g) (c : CheckConstants)
    (hgamma : vword c.gamma e=BitVec.ofNat 32 g)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hd : (⟨aux,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,ResponseDecomposed m (pairPolyPtr out j) (pairPolyPtr aux j) g) :
    (passHintSum work out aux c (firstPassMem m work challenge secret 8) e n).toNat=
      sumN n (fun u => sumN 2 (fun p => sumN 8
        (fun j => (pairedHintPoly m challenge secret out aux g p)[4*u+32*j+e]!.toNat))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hpbound := passHintSum_bound work out aux c (firstPassMem m work challenge secret 8) he (by omega : n≤8)
    have hsbound := hintSum_bound
      (fun p => Inverse.rawFinalValues (readPair (firstPassMem m work challenge secret 8)
        (work+BitVec.ofNat 64 (16*n)) 128 p))
      (out+BitVec.ofNat 64 (16*n)) (aux+BitVec.ofNat 64 (16*n)) c
      (firstPassMem m work challenge secret 8) he
    rw [passHintSum,BitVec.toNat_add,Nat.mod_eq_of_lt (by omega),ih (by omega),sumN_succ]
    rw [hintSum_field (by omega) he hg c hgamma hc hs ho ha hd hp hy]

end VG.Proof.MlDsa.AArch64.Optimized.Paired
