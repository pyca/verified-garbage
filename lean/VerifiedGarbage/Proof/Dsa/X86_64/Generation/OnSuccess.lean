module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.SeedSearch
public import Mathlib.Tactic.Conv
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! # Native phase chaining stops on retry or witness exhaustion -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64

theorem successStatus_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) :
    WP isa (.block Impl.Dsa.X86_64.Generation.successStatus) s fun t =>
      t.zf = some (W 19 == 1) ∧ t.mem = s.mem ∧ Keep [.rax] s t := by
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
      t.zf = some (W 19 == 1) ∧ t.mem = s.mem) (by
    xrun [Impl.Dsa.X86_64.Generation.successStatus, ea_sp, L.rsp, L.ld (d := 152) (by decide),
      R.slot (d := 152) (k := 19) rfl (by decide) rfl]
    rw [sub_beq_zero]) rfl) fun _ ⟨⟨hz, hm⟩, hk⟩ => ⟨hz, hm, hk⟩

theorem onSuccess_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    {next : Prog isa} {Q : State → Prop}
    (L : Lay s F S) (R : Rep s.mem F S V W)
    (accepted : ∀ t, t.mem = s.mem → Keep [.rax] s t → W 19 = 1 → WP isa next t Q)
    (rejected : ∀ t, t.mem = s.mem → Keep [.rax] s t → W 19 ≠ 1 → Q t) :
    WP isa (Impl.Dsa.X86_64.Generation.onSuccess next) s Q := by
  unfold Impl.Dsa.X86_64.Generation.onSuccess
  refine WP.seq (WP.mono (successStatus_ok L R) fun t ⟨hz, hm, hk⟩ => ?_)
  by_cases h : W 19 = 1
  · refine WP.ite true (by simp only [eval, hz, h, beq_self_eq_true])
      (fun _ => accepted t hm hk h) (fun he => Bool.noConfusion he)
  · refine WP.ite false (by simp only [eval, hz, beq_eq_false_iff_ne.mpr h])
      (fun he => Bool.noConfusion he) (fun _ => WP.block_nil (rejected t hm hk h))

end VG.Proof.Dsa.X86_64.Generation
