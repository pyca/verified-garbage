import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedMaskCopy
import VerifiedGarbage.Spec.MlDsa.CommitTail
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCommitmentPack

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.Sign

/-- The cached stream is the final polynomial of the next attempt. -/
theorem nextNonce {p : Params} (hp : p=mlDsa65∨p=mlDsa87) (t : Nat) :
    p.ℓ*t+2*p.ℓ-1=p.ℓ*(t+1)+(p.ℓ-1) := by
  rcases hp with rfl|rfl <;> simp only [mlDsa65,mlDsa87] <;> omega

theorem nextNonce_bound {p : Params} (hp : p=mlDsa65∨p=mlDsa87) {t : Nat} (ht : t<814) :
    p.ℓ*t+2*p.ℓ-1<2^16 := by
  rcases hp with rfl|rfl <;> simp only [mlDsa65,mlDsa87] <;> omega

theorem nonceExtract_bytes {n : Nat} (hn : n<2^16) :
    [(BitVec.ofNat 64 n).extractLsb' 0 8,(BitVec.ofNat 64 n).extractLsb' 8 8]=integerToBytes n 2 := by
  have h := kappa_bytes hn
  have h0 (v : BitVec 64) : v.extractLsb' 0 8=v.setWidth 8 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat,BitVec.toNat_setWidth]
    rfl
  have h1 (v : BitVec 64) : v.extractLsb' 8 8=(v >>> 8).setWidth 8 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat,BitVec.toNat_setWidth,BitVec.toNat_ushiftRight]
  rw [h0,h1]
  exact h

theorem nextSeed {p : Params} (hp : p=mlDsa65∨p=mlDsa87) {t : Nat} (ht : t<814)
    {m : Mem} {a : Addr} {σ : State} {nonce : BitVec 64}
    (hs : Spec.Sha3.bytesAt m a 64=rppOf p σ)
    (hn : nonce=BitVec.ofNat 64 (p.ℓ*t+2*p.ℓ-1)) :
    commitTailSeed m a nonce=rppOf p σ++integerToBytes (p.ℓ*(t+1)+(p.ℓ-1)) 2 := by
  rw [commitTailSeed,hs,hn,nonceExtract_bytes (nextNonce_bound hp ht),nextNonce hp]

theorem nextPolynomial {p : Params} (hp : p=mlDsa65∨p=mlDsa87) {t : Nat} (ht : t<814)
    {m : Mem} {a : Addr} {σ : State} {nonce : BitVec 64}
    (hs : Spec.Sha3.bytesAt m a 64=rppOf p σ)
    (hn : nonce=BitVec.ofNat 64 (p.ℓ*t+2*p.ℓ-1)) :
    toRq (bitUnpack (H (commitTailSeed m a nonce) 640) 524287 524288)=
      Yv p σ (p.ℓ*(t+1)) (p.ℓ-1) := by
  rw [nextSeed hp ht hs hn]
  rcases hp with rfl|rfl <;> rfl

theorem nextMask {p : Params} (hp : p=mlDsa65∨p=mlDsa87) {t : Nat} (ht : t<814)
    {m : Mem} {a : Addr} {σ s : State} {nonce : BitVec 64}
    (hs : Spec.Sha3.bytesAt m a 64=rppOf p σ)
    (hn : nonce=BitVec.ofNat 64 (p.ℓ*t+2*p.ℓ-1))
    (hm : PolyIs s.mem (pa s t4P) (toRq (bitUnpack (H (commitTailSeed m a nonce) 640) 524287 524288))) :
    Mask p σ (t+1) s := by
  rw [nextPolynomial hp ht hs hn] at hm
  exact hm

theorem nextPolynomial_of_phase {p : Params} (hp : p=mlDsa65∨p=mlDsa87)
    {S t i : Nat} {σ s : State} (h : PositiveICh p S σ t i s)
    (hn : s.gpr .x9=BitVec.ofNat 64 (p.ℓ*t+2*p.ℓ-1)) :
    toRq (bitUnpack (H (commitTailSeed s.mem (pa s (VG.Impl.MlDsa.AArch64.Call.sc oMS)) (s.gpr .x9)) 640) 524287 524288)=
      Yv p σ (p.ℓ*(t+1)) (p.ℓ-1) :=
  nextPolynomial hp h.c.masks.l.t_lt h.c.masks.l.k.rpp hn

end VG.Proof.MlDsa.AArch64.Sign.Cached
