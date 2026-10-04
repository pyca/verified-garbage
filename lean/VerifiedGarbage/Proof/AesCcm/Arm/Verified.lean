import VerifiedGarbage.Proof.AesCcm.Arm.CTFn
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Spec.Ccm.Contract

/-!
# AES-CCM on ARMv7: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant
time, a state satisfying the precondition, and the shared contracts of
`Spec/Ccm/Contract.lean`, with 16 bytes of stack: each call pushes two
words, and `vg_cmac_aes_update` pushes two more for its own call of
`vg_aes_ctr32`.
-/

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Impl.AesCcm.Arm

/-- The entry invariant of both runs, from the precondition and the public data. -/
theorem entI_of {s : State} (h : onePre s) :
    EntI (s.gpr .r0) (arg s 4) s.sp (s.gpr .r2) (arg s 0) (arg s 2) (s.gpr .r1).toNat (s.gpr .r3).toNat
      (arg s 1).toNat (arg s 3).toNat (arg s 5).toNat s :=
  ⟨⟨args_of h, rfl, h.2.1, rfl, (ofNat_toNat32 _).symm, rfl, (ofNat_toNat32 _).symm, rfl, (ofNat_toNat32 _).symm⟩,
    rfl, (ofNat_toNat32 _).symm, rfl, (ofNat_toNat32 _).symm⟩

theorem entI_pub {s₁ s₂ : State} (h₂ : onePre s₂) (hq : onePub s₁ s₂) :
    EntI (s₁.gpr .r0) (arg s₁ 4) s₁.sp (s₁.gpr .r2) (arg s₁ 0) (arg s₁ 2) (s₁.gpr .r1).toNat (s₁.gpr .r3).toNat
      (arg s₁ 1).toNat (arg s₁ 3).toNat (arg s₁ 5).toNat s₂ := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, qa⟩ := hq
  have e := entI_of h₂
  rwa [← q₀, ← q₁, ← q₂, ← q₃, ← q₄, ← qa 0 (by decide), ← qa 1 (by decide), ← qa 2 (by decide),
    ← qa 3 (by decide), ← qa 4 (by decide), ← qa 5 (by decide)] at e

theorem one_ct {c : Prog isa}
    (hc : ∀ {k w sp N A D : BitVec 32} {R nl al n tl : Nat}, Lay k w sp → (R = 10 ∨ R = 12 ∨ R = 14) →
      al < 2 ^ 32 → 7 ≤ nl → nl ≤ 13 → n < 256 ^ (15 - nl) → n < 2 ^ 32 →
      Proof.AesGcm.Arm.CT (EntI k w sp N A D R nl al n tl) c)
    {pub : State → State → Prop} (hp : ∀ s₁ s₂, pub s₁ s₂ → onePub s₁ s₂) :
    ConstantTime isa onePre pub c := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂
  have Ar := args_of h₁
  exact (hc Ar.lay Ar.rounds Ar.al32 Ar.h7 Ar.h13 Ar.hn Ar.n32 _ _ _ _ _ _ ⟨entI_of h₁, entI_pub h₂ (hp _ _ hq)⟩
    e₁ e₂).1

theorem seal_ct : ConstantTime isa sealArm.pre sealArm.pub «seal» :=
  one_ct (fun L hR hal h7 h13 hn hn4 => seal_ctI L hR hal h7 h13 hn hn4) fun _ _ h => h

theorem open_ct : ConstantTime isa openArm.pre openArm.pub «open» :=
  one_ct (fun L hR hal h7 h13 hn hn4 => open_ctI L hR hal h7 h13 hn hn4) fun _ _ h => h.1

/-- A state satisfying the precondition of `vg_aes_ccm_seal` and
`vg_aes_ccm_open`: a 7-byte nonce, no associated data, no data, `work` at 0
and a 4-byte tag. -/
def sealSat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | .r3 => 7 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8014 then 4 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0, 0⟩, ⟨0x8000, 24⟩]
  wr := [⟨0, 0⟩, ⟨0, 2560⟩]

theorem seal_verified : Verified Arm.target «seal» (Spec.Ccm.sealContract Arm.abi 16) :=
  Verified.of_correct (fun _ hs => seal_wp hs) seal_ct (by
    sig_implies [Spec.Ccm.sealContract, Spec.Ccm.sealSig, sealArm, onePre, onePub, bel16, arg, args, roundsOk,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using sealSat)

/-- The leak `open` may have: whether it succeeds. -/
theorem leak_bool {a b : Bool} (h : [if a = true then 1 else 0] = [if b = true then 1 else 0]) : a = b := by
  cases a <;> cases b <;> simp_all

theorem open_verified : Verified Arm.target «open» (Spec.Ccm.openContract Arm.abi 16) :=
  Verified.of_correct (fun _ hs => open_wp hs) open_ct
    { pre := by
        sig_implies_pre [Spec.Ccm.openContract, Spec.Ccm.openSig, Spec.Ccm.sealSig, openArm, onePre, onePub, bel16,
          arg, args, roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by
        intro s s' _ h
        sig_eval [Spec.Ccm.openContract, Spec.Ccm.openSig, Spec.Ccm.sealSig, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        simp only [openArm, openRes, ciph, Arm.State.addr] at h
        have e : ∀ x y : BitVec 32, (x ++ y).setWidth 32 = y := fun _ _ => BitVec.setWidth_append_eq_right
        rw [e]
        exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.Ccm.openContract, Spec.Ccm.openSig, Spec.Ccm.sealSig, openArm, onePre, onePub, bel16, arg,
          args, roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] at h
        obtain ⟨hsp, hl, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5⟩ := h
        refine ⟨⟨hsp, h0, h1, h2, h3, fun i hi => ?_⟩, leak_bool hl⟩
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with
          rfl | rfl | rfl | rfl | rfl | rfl
        · exact a0
        · exact a1
        · exact a2
        · exact a3
        · exact a4
        · exact a5
      sat := by
        sig_implies_sat [Spec.Ccm.openContract, Spec.Ccm.openSig, Spec.Ccm.sealSig, openArm, onePre, onePub,
          bel16, arg, args, roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
          [sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using sealSat }

end VG.Proof.AesCcm.Arm
