module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedMaskCopy
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCommitmentHash

import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedHashFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedHashSetup
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedMaskPrefixTailTiming
import VerifiedGarbage.Proof.MlDsa.CommitTailContract
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCommitmentPack

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Sign/CachedHashNonce.lean`, which only this module imported.
section

section

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
end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

theorem hash_ok {p : Params} (hp : p=mlDsa65 ∨ p=mlDsa87)
    {S : Nat} (hS : S<2^64) {σ s : State} {t : Nat}
    (h : PositiveICh p S σ t p.k s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Cached.hash p) s
      (fun u => PositiveIC p S σ t u ∧ Mask p σ (t+1) u) := by
  have hp3 : Ok3 p := by rcases hp with h|h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr h)
  unfold Impl.MlDsa.AArch64.Sign.Cached.hash
  refine WP.seq (WP.mono (hashSetup_ok hp3 h) fun a ⟨ha,hn,_⟩ => ?_)
  refine WP.mono (hashReady_phase hp hS ha) fun u ⟨hu,hm⟩ => ⟨hu,?_⟩
  rw [nextPolynomial_of_phase hp ha hn] at hm
  exact hm

theorem commit_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : p=mlDsa65 ∨ p=mlDsa87) {σ s : State} {t : Nat}
    (h : PositiveIL p S σ t s) (hm : t=0 ∨ Mask p σ t s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Cached.commit P p) s
      (fun u => PositiveIC p S σ t u ∧ Mask p σ (t+1) u) := by
  have hp3 : Ok3 p := by rcases hp with h|h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr h)
  unfold Impl.MlDsa.AArch64.Sign.Cached.commit
  refine WP.seq (WP.mono (masks_ok hP hp h hm) fun a ha => ?_)
  refine WP.seq (WP.mono (positiveRows_ok hp3 ha) fun b hb => ?_)
  refine WP.seq (WP.mono (positivePackRows_ok hP hp3 hb) fun c hc => ?_)
  exact hash_ok hp hP.s64 hc

end VG.Proof.MlDsa.AArch64.Sign.Cached
