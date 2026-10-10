import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPrefix
import VerifiedGarbage.Proof.Ecdsa.AArch64.Verified
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvEarlyWrapped
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointPoints
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Verified
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedMain
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPointsTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacContract
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointCacheTiming

/-! ## `AllocatedInverse` -/

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
    (invLayN (p256_ok hI)) (unitMod_pow_two (p256_ok hI).n_odd _) hs hm hx
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
    {s : State} (hp : VPre p256 s) :
    WP isa allocatedPrefix s fun t => ∃ g,Mid p256 s (s.gpr .x3) g t := by
  exact front_ok (p256_ok hI) hp fun g _ _ hf =>
    allocatedMid_ok hI hT hf fun _ hm => WP.block_nil ⟨g,hm⟩

theorem allocatedInverse_relCT (hI : InvSounds) (hT : InvToM p256.C.n)
    (s₀ t₀ : State) (hp : JacPublic p256 s₀ t₀) :
    RelCT isa (InversePair s₀ t₀) P256Allocated.inverse
      (AArch64.Taint.Agree (Taint.ofRegs [.x0])) := by
  intro s t ts tt s' t' ⟨hs,ht,hsp⟩ es et
  have hx := hs.eq (p256_ok hI) hp ht
  exact invAllocated_inverse_relCT (by decide) VG.Proof.P256.n_prime hT
    (invLayN (p256_ok hI)) (unitMod_pow_two (p256_ok hI).n_odd _)
    hs.lt ((p256_ok hI).inv_n (by decide)).2 _ _ _ _ _ _
    ⟨hs.scr,ht.scr,hsp,hs.mod,ht.mod,rfl,hx.symm⟩ es et

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
theorem allocatedVerify_restored (hL : Law Spec.P256.curve) (hI : InvSounds)
    (hTInv : InvToM p256.C.n)
    (hTcomb : CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    {s t : State} {tr : List Leak} (hp : VPre p256 s)
    (he : Exec isa P256Allocated.verify s tr t) : ∀ r∈untouched,t.gpr r=s.gpr r := by
  refine allocatedVerify_extra_preserved (p256_ok hI)
    (fun _ h => allocatedPrefix_ok hI hTInv h) ?_
    (fun _ _ _ h m => Allocated.points_untouched (p256_ok hI) hL hTcomb h m) hp he
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

theorem allocatedVerify_ok (hL : Law Spec.P256.curve) (hI : InvSounds)
    (hN : InvToM p256.C.n)
    (hT : CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    {s : State} (h : VPre p256 s) :
    WP isa P256Allocated.verify s fun t =>
      (∀ r∈Cfg.saved.map Prod.fst,t.gpr r=s.gpr r) ∧ VPost p256 s t := by
  apply verify_of_joint_inverse (p256_ok hI) hL P256Allocated.inverse P256Allocated.points
    P256Allocated.verify (allocatedMid_ok hI hN) rfl ?_ h
  intro s₀ base g s hm ht P hp hr
  exact WP.mono (Allocated.points_ok (p256_ok hI) hL hT hm ht hp hr)
    fun _ ⟨hf,hrep,_⟩ => ⟨hf,hrep⟩

/-- The allocated verifier satisfies the existing correctness, ABI and public-input contract. -/
theorem allocatedVerify_verified (hL : Law Spec.P256.curve) (hI : InvSounds)
    (hN : InvToM p256.C.n)
    (hT : CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start) :
    Verified AArch64.target P256Allocated.verify
      (Spec.Ecdsa.P256.inst.verifyContract (AArch64.abi.withConsts p256.combConsts)) := by
  refine ⟨fun s hs => ?_,?_,implies.sat⟩
  · obtain ⟨tr,t,he,ha,hp⟩ := allocatedVerify_a64_of_wp
      (fun _ hp => allocatedVerify_ok hL hI hN hT hp)
      (fun hp he => allocatedVerify_restored hL hI hN hT hp he) s (implies.pre _ hs)
    exact ⟨tr,t,he,ha,implies.post s t hs hp⟩
  · intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
    exact allocatedVerify_ct_of_points (fun _ hp => allocatedPrefix_ok hI hN hp)
      (allocatedPrefix_ct (p256_ok hI) (allocatedInverse_relCT hI hN) allocatedUv_ct)
      (fun _ _ ps pt => Allocated.allocatedPoints_relCT Allocated.raw_correct (p256_ok hI) hL hT ps pt)
      jointTail_ct _ _ _ _ _ _ (jacPre_of (implies.pre _ pre₁)) (jacPre_of (implies.pre _ pre₂))
      (jacPublic_of_spec pub) e₁ e₂

end VG.Proof.Ecdsa.Verify.AArch64

end
