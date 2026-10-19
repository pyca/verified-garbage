module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.SeedSearch
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Hash
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.Omega

/-! # Native phase chaining stops on retry or witness exhaustion -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64

theorem successStatus_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) :
    WP isa (.block Impl.Dsa.AArch64.Generation.successStatus) s fun t =>
      eval (.zero .x .x3) t = some (W 19 == (1#64)) ∧ t.mem = s.mem ∧ Keep [.x3, .x4] s t := by
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun t =>
      eval (.zero .x .x3) t = some (W 19 == (1#64)) ∧ t.mem = s.mem) (by
    have hw : s.mem.readW (F + BitVec.ofNat 64 152) 64 = W 19 := R.fr 19 (by decide)
    unfold Impl.Dsa.AArch64.Generation.successStatus
    brun [exec_ldrSp (off := 152) (by decide), L.sp,
      L.ld (d := 152) (n := 8) (by decide), hw, eval]
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, beq_iff_eq, BitVec.sub_eq_iff_eq_add]
    change W 19 = (1#64) ↔ W 19 = (1#64)
    rfl) rfl rfl rfl) fun _ ⟨⟨hz, hm⟩, hk⟩ => ⟨hz, hm, hk⟩

theorem onSuccess_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    {next : Prog isa} {Q : State → Prop}
    (L : Lay s F S) (R : Rep s.mem F S V W)
    (accepted : ∀ t, t.mem = s.mem → Keep [.x3, .x4] s t → W 19 = 1 → WP isa next t Q)
    (rejected : ∀ t, t.mem = s.mem → Keep [.x3, .x4] s t → W 19 ≠ 1 → Q t) :
    WP isa (Impl.Dsa.AArch64.Generation.onSuccess next) s Q := by
  unfold Impl.Dsa.AArch64.Generation.onSuccess
  refine WP.seq (WP.mono (successStatus_ok L R) fun t ⟨hz, hm, hk⟩ => ?_)
  by_cases h : W 19 = 1
  · refine WP.ite true (by apply hz.trans; rw [h]; rfl)
      (fun _ => accepted t hm hk h) (fun he => Bool.noConfusion he)
  · refine WP.ite false (by exact hz.trans (congrArg some (beq_eq_false_iff_ne.mpr h)))
      (fun he => Bool.noConfusion he) (fun _ => WP.block_nil (rejected t hm hk h))

end VG.Proof.Dsa.AArch64.Generation
