import VerifiedGarbage.Proof.Ed448.Arm.Verify.Entry
import VerifiedGarbage.Proof.Ed448.Arm.Verify.CT
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.WrapCT
import VerifiedGarbage.Proof.Framework.Arm.Contract

/-!
# Ed448 verification on ARMv7: constant time, and `Verified`

`verify_ct`: the check of the context's length leaks nothing and branches
on a length; the frame around the body is constant time (`inner_ct`, from
`body_ct`). `verify_verified`: against `Spec.Ed448.verifyContract Arm.abi
280`, for any code of `vg_ed448_verify_equation` meeting its contract
(`EqOk`, `EqCT`): the registration file passes its own.
-/

namespace VG.Proof.Ed448.Arm.Verify

open VG VG.Arm VG.Impl.Ed448.Arm.Verify VG.Impl.Ed25519.Arm.Whole
open VG.Proof.Ed25519.Arm (Whole.base Whole.wrap_ct Whole.bodyRd Whole.bodyWr Whole.quiet_block_ct)

theorem lay_eq {s t : State} (hp : verifyLocal.pub s t) : lay s = lay t := by
  obtain ⟨sp, h0, h1, h2, h3, a0, a1, a2⟩ := hp
  simp only [lay, Whole.base, sp, h0, h1, h2, h3, a0, a1, a2]

/-- The frame around the body is constant time, for a context of fewer than 256 bytes. -/
theorem inner_ct (hv : EqOk) (hct : EqCT) :
    ConstantTime isa (fun s => verifyLocal.pre s ∧ (s.gpr .r2).toNat < 256) verifyLocal.pub (wrap 6 body) := by
  refine Whole.wrap_ct (by decide : 6 ≤ 6) (fun _ _ hp => hp.1) (fun _ hs => entry_below hs.1)
    (fun _ hs => by have := entry_top hs.1; omega) (fun _ hs => entry_read hs.1) ?_ ?_
  · intro s hs p hp
    exact WP.mono (body_ok hv (entry_ctx hs.1 hp) (lay_ok hs.1 hs.2) (entry_args hs.1 hp)) fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p, q, hpa, hqb, rfl, rfl⟩ ea eb
    have he := lay_eq hp
    have hq : Ctx (lay s) t.gpr q.mem (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)) :=
      he ▸ entry_ctx ht.1 hqb
    have hqa : Arguments (lay s) q.mem := he ▸ entry_args ht.1 hqb
    exact ⟨(body_ct hv hct (lay_ok hs.1 hs.2) (entry_args hs.1 hpa) hqa _ _ _ _ _ _
      ⟨⟨entry_ctx hs.1 hpa, trivial⟩, ⟨hq, trivial⟩⟩ ea eb).1, trivial⟩

theorem checked_pub {s t : State} (h : verifyLocal.pub s t) : verifyLocal.pub (checked s) (checked t) := h

theorem checked_lt {s : State} (h : isa.eval .eq (checked s) = some true) : (s.gpr .r2).toNat < 256 := by
  rw [VG.Proof.X25519.Arm.eval_eq, checked_z, shr8_eq_zero] at h
  exact of_decide_eq_true (Option.some.inj h)

theorem verify_ct (hv : EqOk) (hct : EqCT) : ConstantTime isa verifyLocal.pre verifyLocal.pub code := by
  apply RelCT.constantTime (Q := fun _ _ => True)
  unfold code
  have hblk := ((Whole.quiet_block_ct check (by
      intro i hi s
      simp only [check, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> rfl)).mono
    (P' := fun s₁ s₂ => verifyLocal.pre s₁ ∧ verifyLocal.pre s₂ ∧ verifyLocal.pub s₁ s₂)
    (fun _ _ h => h.2.2.1) (fun _ _ _ => trivial)).wpDep (F := fun σ s' => s' = checked σ)
      (fun s₁ s₂ _ => ⟨check_exec s₁, check_exec s₂⟩)
  refine RelCT.seq hblk (RelCT.ite ?_ ?_ ?_)
  · rintro _ _ ⟨_, σ₁, σ₂, hp, rfl, rfl⟩
    rw [VG.Proof.X25519.Arm.eval_eq, VG.Proof.X25519.Arm.eval_eq, checked_z, checked_z, hp.2.2.2.2.2.1]
  · rintro _ _ t₁ t₂ s₁' s₂' ⟨⟨_, σ₁, σ₂, hp, rfl, rfl⟩, hev⟩ e₁ e₂
    have l₁ := checked_lt hev
    have l₂ : (σ₂.gpr .r2).toNat < 256 := hp.2.2.2.2.2.1 ▸ l₁
    exact ⟨inner_ct hv hct _ _ _ _ _ _ ⟨checked_pre hp.1, l₁⟩ ⟨checked_pre hp.2.1, l₂⟩
      (checked_pub hp.2.2) e₁ e₂, trivial⟩
  · refine ((Whole.quiet_block_ct [.movw .r0 0] (by
      intro i hi s
      rw [List.mem_singleton.mp hi]; rfl)).mono ?_ (fun _ _ _ => trivial))
    rintro _ _ ⟨⟨_, σ₁, σ₂, hp, rfl, rfl⟩, _⟩
    exact hp.2.2.1

/-! ## The contract -/

def verifySatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0 | .r3 => 0x3000 | _ => 0
  sp := 0x9000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x9005 then 0x50 else if a = 0x900A then 0x01 else 0
  rd := [⟨0x1000, 57⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x5000, 114⟩, ⟨0x9000, 12⟩]
  wr := [⟨0x10000, 8192⟩]

private theorem argAddr_zero (s : State) : stackArgAddr s 0 = State.addr s.sp := by
  simp [stackArgAddr]

private theorem pre_bridge (s : State) (h : (Spec.Ed448.verifyContract Arm.abi 280).pre s) :
    verifyLocal.pre s := by
  sig_pre [Spec.Ed448.verifyContract, Spec.Ed448.verifySig,
    Spec.Ed448.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] at h
  sig_split h
  sig_reduce [verifyLocal, Arm.State.addr]
  sig_simp [argAddr_zero, Arm.State.addr] [] at *
  simp only [Arm.State.addr, show (280#64) = (280 : Addr) from rfl] at *
  sig_and_intros
  all_goals first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›

theorem verify_implies : verifyLocal.Implies (Spec.Ed448.verifyContract Arm.abi 280) where
  pre := pre_bridge
  post s t _ h := by
    sig_post [Spec.Ed448.verifyContract, Spec.Ed448.verifySig,
      Spec.Ed448.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    rw [BitVec.setWidth_append_eq_right]
    exact h
  pub s t _ _ h := by
    sig_pub [Spec.Ed448.verifyContract, Spec.Ed448.verifySig,
      Spec.Ed448.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] at h
    obtain ⟨sp, _, h0, h1, h2, h3, a0, a1, a2⟩ := h
    exact ⟨sp, h0, h1, h2, h3, a0, a1, a2⟩
  sat := by
    refine ⟨verifySatState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.Ed448.verifyContract, Spec.Ed448.verifySig,
        Spec.Ed448.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, verifySatState]
      decide +kernel

/-- `vg_ed448_verify` on ARMv7, for any code of `vg_ed448_verify_equation`
meeting its contract. -/
theorem verify_verified (hv : EqOk) (hct : EqCT) :
    Verified Arm.target code (Spec.Ed448.verifyContract Arm.abi 280) :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => verify_ok hv h) (verify_ct hv hct) (.refl verify_implies.sat_left))
    verify_implies

end VG.Proof.Ed448.Arm.Verify
