module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPrefix
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPrefix
import VerifiedGarbage.Proof.Ecdsa.AArch64.Verified
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Verified
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvEarlyWrapped
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
public import VerifiedGarbage.Proof.P256.EcdhDouble.Certificate
public import VerifiedGarbage.Proof.P256.EcdhTable.Dblu
public import VerifiedGarbage.Proof.P256.EcdhTable.Zaddu
public import VerifiedGarbage.Proof.P256.Linear.WeakCertificate
public import VerifiedGarbage.Proof.P256.VerifyAllocated.CachedHead
public import VerifiedGarbage.Proof.P256.VerifyAllocated.JacTail
public import VerifiedGarbage.Proof.P256.VerifyAllocated.MixedHead
public import VerifiedGarbage.Proof.P256.VerifyAllocated.MixedTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticCachedHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticJacHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticJacTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticMixedHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticMixedTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticRR
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticTableHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticTableTail
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Ecdsa.P256
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.InvEarlyWrapped
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPoints
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPoints
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Verified
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedMain
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedMain
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPointsTiming
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPointsTiming
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.GContract
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacContract
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedRaw
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedScalars
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedRaw
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedScalars
import VerifiedGarbage.Proof.P256.Prime
meta import VerifiedGarbage.Proof.P256.Prime
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacChecks
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacChecks
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.GTable

/-! ## `AllocatedInverse` -/

@[expose] public section

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

/-- The wider inverse workspace remains within the existing 8 KB scratch buffer. -/
theorem allocatedInverse_fixed : FixedOk p256 invAllocatedOuterW := by unfold FixedOk; decide +kernel

theorem allocatedInverse_apart : ∀ i<45,i∉[ACC,TMP] → ∀ w∈invAllocatedOuterW,
    p256.sl i+8*p256.n≤w.1 ∨ w.1+w.2≤p256.sl i := by decide +kernel

theorem allocatedInverse_bound : ∀ w∈invAllocatedOuterW,w.1+w.2≤size := by decide

/-- P-256's powers' modulus modulo `n` is `MN'`: its inversions are inline. -/
theorem p256_invM (hI : InvSounds) {base : Addr} {m : Mem} (hm : ModOkA p256.MN' size p256.C.n m base) :
    ModOkA invAllocatedCfg.M size p256.C.n m base :=
  modOkA_inv (p256_ok hI) hm (.inr rfl) rfl rfl

theorem allocatedInverse_ok (hI : InvSounds) (hT : InvToM p256.C.n)
    {s : State} {base : Addr} (hs : Scr s base size)
    (hm : ModOkA p256.MN' size p256.C.n s.mem base)
    (hx : wordsVal s.mem base (p256.sl KM) p256.n<p256.C.n) :
    WP isa P256Allocated.inverse s fun t =>
      KeepRegs invAllocatedOuterRegs s t ∧ Unch base invAllocatedOuterW s.mem t.mem ∧
      wordsVal t.mem base (p256.sl ACC) p256.n<p256.C.n ∧
      toM p256.C.n (2^(64*p256.n)) (wordsVal t.mem base (p256.sl ACC) p256.n)=
        toM p256.C.n (2^(64*p256.n)) (wordsVal s.mem base (p256.sl KM) p256.n)^(p256.C.n-2) :=
  invAllocated_inverse_ok (by decide) VG.Proof.P256.n_prime hT
    (invLayN (p256_ok hI)) (unitMod_pow_two (p256_ok hI).n_odd _) hs (p256_invM hI hm) hx
    ((p256_ok hI).inv_n (by decide)).2

theorem allocatedMid_ok (hI : InvSounds) (hT : InvToM p256.C.n)
    {s₀ : State} {base : Addr} {g : Reg → BitVec 64} {s : State}
    (hf : Front p256 s₀ base g s) {rest : Prog isa} {Q : State → Prop}
    (h : ∀ t,Mid p256 s₀ base g t → WP isa rest t Q) :
    WP isa (.seq (Cfg.scalars p256) (.seq P256Allocated.inverse
      (.seq (Cfg.uv p256) rest))) s Q :=
  mid_with_inverse_ok (p256_ok hI) P256Allocated.inverse invAllocatedOuterRegs invAllocatedOuterW
    (by decide) allocatedInverse_fixed (fun hi hh => allocatedInverse_apart _ hi hh)
    allocatedInverse_bound (allocatedInverse_ok hI hT) hf h

theorem allocatedPrefix_ok (hI : InvSounds) (hT : InvToM p256.C.n)
    {s : State} (hp : VPreG s) :
    WP isa allocatedPrefix s fun t => ∃ g,Mid p256 s (s.gpr .x3) g t := by
  exact front_ok (p256_ok hI) hp.front fun g _ _ hf =>
    allocatedMid_ok hI hT hf fun _ hm => WP.block_nil ⟨g,hm⟩

theorem allocatedInverse_relCT (hI : InvSounds) (hT : InvToM p256.C.n)
    (s₀ t₀ : State) (hp : JacPublicG s₀ t₀) :
    RelCT isa (InversePair s₀ t₀) P256Allocated.inverse
      (AArch64.Taint.Agree (Taint.ofRegs [.x0])) := by
  intro s t ts tt s' t' ⟨hs,ht,hsp⟩ es et
  have hx := hs.eq (p256_ok hI) hp ht
  exact invAllocated_inverse_relCT (by decide) VG.Proof.P256.n_prime hT
    (invLayN (p256_ok hI)) (unitMod_pow_two (p256_ok hI).n_odd _)
    hs.lt ((p256_ok hI).inv_n (by decide)).2 _ _ _ _ _ _
    ⟨hs.scr,ht.scr,hsp,p256_invM hI hs.mod,p256_invM hI ht.mod,rfl,hx.symm⟩ es et

theorem allocatedUv_ct : FieldCT (Cfg.uv p256) := by jac_field_ct

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `AllocatedPreserved` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

/-- Both allocated stages restore the additional callee-saved registers before
returning to the unchanged verifier stages. -/
theorem allocatedVerify_restored (hL : Law Spec.P256.curve) (hO : PrimeOrder Spec.P256.curve) (hI : InvSounds)
    (hTInv : InvToM p256.C.n)
    (hTcomb : CombOkW Spec.P256.curve 9 1 Impl.P256.p256G9 Impl.P256.p256G9Start)
    {s t : State} {tr : List Leak} (hp : VPreG s)
    (he : Exec isa P256Allocated.verify s tr t) : ∀ r∈untouched,t.gpr r=s.gpr r := by
  refine allocatedVerify_extra_preserved (p256_ok hI)
    (fun _ h => allocatedPrefix_ok hI hTInv h) ?_
    (fun _ _ _ h m => Allocated.points_untouched (p256_ok hI) hL hO hTcomb h m) hp he
  intro s₀ a ha
  refine WP.mono (allocatedInverse_ok hI hTInv ha.scr ha.mod ha.lt) fun b hb r hr => ?_
  exact hb.1.gpr r ((show ∀ r∈untouched,r∉invAllocatedOuterRegs from by decide) r hr)

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `AllocatedVerified` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

theorem allocatedVerify_ok (hL : Law Spec.P256.curve) (hO : PrimeOrder Spec.P256.curve) (hI : InvSounds)
    (hN : InvToM p256.C.n)
    (hT : CombOkW Spec.P256.curve 9 1 Impl.P256.p256G9 Impl.P256.p256G9Start)
    {s : State} (h : VPreG s) :
    WP isa P256Allocated.verify s fun t =>
      (∀ r∈Cfg.saved.map Prod.fst,t.gpr r=s.gpr r) ∧ VPost p256 s t := by
  apply verify_of_joint_inverse (p256_ok hI) hL P256Allocated.inverse P256Allocated.points
    P256Allocated.verify (allocatedMid_ok hI hN) rfl ?_ h
  intro s₀ base g s hm ht P hp hr
  exact WP.mono (Allocated.points_ok (p256_ok hI) hL hO hT hm ht hp hr)
    fun _ ⟨hf,hrep,_⟩ => ⟨hf,hrep⟩

/-- The allocated verifier satisfies the existing correctness, ABI and public-input contract. -/
theorem allocatedVerify_verified (hL : Law Spec.P256.curve) (hO : PrimeOrder Spec.P256.curve) (hI : InvSounds)
    (hN : InvToM p256.C.n)
    (hT : CombOkW Spec.P256.curve 9 1 Impl.P256.p256G9 Impl.P256.p256G9Start) :
    Verified AArch64.target P256Allocated.verify
      (Spec.Ecdsa.P256.inst.verifyContract (AArch64.abi.withConsts P256Joint.p256v.combConsts)) := by
  refine ⟨fun s hs => ?_,?_,impliesG.sat⟩
  · obtain ⟨tr,t,he,ha,hp⟩ := allocatedVerify_a64_of_wp
      (fun _ hp => allocatedVerify_ok hL hO hI hN hT hp)
      (fun hp he => allocatedVerify_restored hL hO hI hN hT hp he) s (impliesG.pre _ hs)
    exact ⟨tr,t,he,ha,impliesG.post s t hs hp⟩
  · intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
    exact allocatedVerify_ct_of_points (fun _ hp => allocatedPrefix_ok hI hN hp)
      (allocatedPrefix_ct (p256_ok hI) (allocatedInverse_relCT hI hN) allocatedUv_ct)
      (fun _ _ ps pt => Allocated.allocatedPoints_relCT Allocated.raw_correct (p256_ok hI) hL hO hT ps pt)
      jointTail_ct _ _ _ _ _ _ (vpreG_of (impliesG.pre _ pre₁)) (vpreG_of (impliesG.pre _ pre₂))
      (jacPublicG_of_spec pub) e₁ e₂

end VG.Proof.Ecdsa.Verify.AArch64

end
