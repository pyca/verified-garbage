import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPrefix
import VerifiedGarbage.Proof.Ecdsa.AArch64.Verified
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvEarlyWrapped

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
