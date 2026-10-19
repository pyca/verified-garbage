module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Hash
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashFrame
import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Label
public import VerifiedGarbage.Impl.Bignum.AArch64.Core
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # The seed-width dispatch computes exactly DSA's specified seed hash -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Proof.RsaOaep.AArch64
open VG.Proof.Pbkdf2.Md.AArch64

theorem hashTest_ok {s : State} {F S : Addr} (L : Lay s F S)
    {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep s.mem F S V W)
    {len : Nat} (hll : W 26 = BitVec.ofNat 64 len) :
    WP isa (.block Impl.Dsa.AArch64.Generation.hashTest) s fun t =>
      t.gpr .x0 = BitVec.ofNat 64 len - 20 ∧ t.mem = s.mem ∧ Keep [.x0] s t := by
  refine WP.mono (WP.keep [.x0] (Q := fun t =>
    t.gpr .x0 = BitVec.ofNat 64 len - 20 ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun _ ⟨⟨hx, hm⟩, hk⟩ => ⟨hx, hm, hk⟩
  have hw : s.mem.readW (F + BitVec.ofNat 64 sLabLen) 64 = BitVec.ofNat 64 len :=
    (R.fr 26 (by decide)).trans hll
  unfold Impl.Dsa.AArch64.Generation.hashTest
  brun [exec_ldrSp (off := sLabLen) (by decide), L.sp,
    L.ld (d := sLabLen) (n := 8) (by decide), hw]
  rfl

theorem seedHash_frame_ok {G1 G256 : Impl.Pbkdf2.Md.AArch64.Hash}
    (h1 : Calls.StreamOK G1.stream) (h256 : Calls.StreamOK G256.stream)
    (he1 : ∀ x, Spec.Mgf1.sha1.hash x = h1.SH.H.hash x)
    (he256 : ∀ x, Spec.Mgf1.sha256.hash x = h256.SH.H.hash x)
    (hs1 : ∀ x, (Spec.Mgf1.sha1.hash x).length = G1.D)
    (hs256 : ∀ x, (Spec.Mgf1.sha256.hash x).length = G256.D)
    (hd1 : G1.D = 20) (hd256 : G256.D = 32)
    {s : State} {F S rp : Addr} {len : Nat} (hlen : len = 20 ∨ len = 32)
    (L : Lay s F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep s.mem F S V W) (A : LabAt s F S W rp len) :
    WP isa (Impl.Dsa.AArch64.Generation.seedHash G1 G256) s fun t =>
      Lay t F S ∧ Step F S [] s t ∧ Frame [⟨S, oRsa⟩, retR F] s.mem t.mem ∧
      ∃ V', Rep t.mem F S V' W ∧ (∀ x, ¬ inR (labR oDig) x → V' x = V x) ∧
        Spec.Rsa.bytesAt t.mem (off S oDig) len =
          Spec.Dsa.seedHash (8 * len) (Spec.Rsa.bytesAt s.mem rp len) := by
  unfold Impl.Dsa.AArch64.Generation.seedHash
  refine WP.seq (WP.mono (hashTest_ok L R A.hll) fun u ⟨hx, hm, hk⟩ => ?_)
  have Lu : Lay u F S := L.congr hk.sp hk.wr (by rw [hm])
  have Ru : Rep u.mem F S V W := hm ▸ R
  have Au : LabAt u F S W rp len := A.congr hk.rd hk.wr rfl rfl
  have pre : Step F S [] s u := by
    refine ⟨hk.rd, hk.wr, hk.sp, ?_, hk.vcs, ?_⟩
    · intro r hr _
      apply hk.gpr r
      intro he
      have heq : r = .x0 := List.mem_singleton.mp he
      subst r
      simp [preserved] at hr
    · rw [hm]
      exact Frame.refl _ _
  rcases hlen with rfl | rfl
  · refine WP.ite true (by simp [eval, State.read, Size.bits, hx]) (fun _ => ?_) (fun h => Bool.noConfusion h)
    refine WP.mono (hash_bytes_frame h1 he1 hs1 Lu Ru Au)
      fun t ⟨Lt, step, hframe, V', Rt, hf, hb⟩ => ?_
    refine ⟨Lt, pre.trans step, (by simpa only [hm] using hframe), V', Rt, hf, ?_⟩
    simpa only [hd1, hm, Spec.Dsa.seedHash, Nat.reduceMul, beq_self_eq_true,
      ite_true, Spec.Mgf1.sha1] using hb
  · refine WP.ite false (by simp [eval, State.read, Size.bits, hx]) (fun h => Bool.noConfusion h) (fun _ => ?_)
    refine WP.mono (hash_bytes_frame h256 he256 hs256 Lu Ru Au)
      fun t ⟨Lt, step, hframe, V', Rt, hf, hb⟩ => ?_
    refine ⟨Lt, pre.trans step, (by simpa only [hm] using hframe), V', Rt, hf, ?_⟩
    simpa only [hd256, hm, Spec.Dsa.seedHash, Nat.reduceMul,
      show (256 == 160) = false from rfl, Bool.false_eq_true, ite_false, Spec.Mgf1.sha256] using hb

end VG.Proof.Dsa.AArch64.Generation
