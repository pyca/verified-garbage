import VerifiedGarbage.Proof.AesCcm.Arm.CTFn
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.AesCcm.Scratch

/-!
# AES-CCM on ARMv7: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant
time, states satisfying the preconditions, and the shared contracts of
`Spec/Ccm/Contract.lean` with the working space as a last argument
(`Proof/AesCcm/Scratch.lean`), with 16 bytes of stack: each call pushes two
words, and `vg_cmac_aes_update` pushes two more for its own call of
`vg_aes_ctr32`. `Frame.lean` allocates the working space.
-/

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Impl.AesCcm.Arm

/-- The entry invariant of a run, from the arguments. -/
theorem entI_of {s : State} {T : BitVec 32} {tl : Nat}
    (Ar : Args s (s.gpr .r0) (arg s 6) (s.gpr .r2) (arg s 0) (arg s 2) (s.gpr .r1).toNat (s.gpr .r3).toNat
      (arg s 1).toNat (arg s 3).toNat tl) (hT : arg s 4 = T) (htl : arg s 5 = BitVec.ofNat 32 tl)
    (hwr : ∀ r ∈ s.wr, (args s 7).Disjoint r) :
    EntI (s.gpr .r0) (arg s 6) s.sp (s.gpr .r2) (arg s 0) (arg s 2) T (s.gpr .r1).toNat (s.gpr .r3).toNat
      (arg s 1).toNat (arg s 3).toNat tl s :=
  ⟨⟨Ar, rfl, hwr, rfl, (ofNat_toNat32 _).symm, rfl, (ofNat_toNat32 _).symm, hT, htl, rfl⟩,
    rfl, (ofNat_toNat32 _).symm, rfl, (ofNat_toNat32 _).symm⟩

/-- The entry invariant of `seal`'s runs. -/
theorem entI_seal {s : State} (h : sealArm.pre s) :
    EntI (s.gpr .r0) (arg s 6) s.sp (s.gpr .r2) (arg s 0) (arg s 2) (arg s 4) (s.gpr .r1).toNat (s.gpr .r3).toNat
      (arg s 1).toNat (arg s 3).toNat (arg s 5).toNat s := by
  have A := args_of_seal h
  refine entI_of A.1.1 rfl (ofNat_toNat32 _).symm fun r hr => ?_
  rw [h.2.1] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact A.1.1.da.symm
  · exact A.2.2.symm
  · exact A.1.1.stk.aw

/-- The entry invariant of `open`'s runs. -/
theorem entI_open {s : State} (h : openArm.pre s) :
    EntI (s.gpr .r0) (arg s 6) s.sp (s.gpr .r2) (arg s 0) (arg s 2) (arg s 4) (s.gpr .r1).toNat (s.gpr .r3).toNat
      (arg s 1).toNat (arg s 3).toNat (arg s 5).toNat s := by
  have A := args_of_open h
  refine entI_of A.1.1 rfl (ofNat_toNat32 _).symm fun r hr => ?_
  rw [h.2.1] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact A.1.1.da.symm
  · exact A.1.1.stk.aw

/-- The second run, with the first's public arguments. -/
theorem entI_pub {pre : State → Prop}
    (hpre : ∀ {s}, pre s → EntI (s.gpr .r0) (arg s 6) s.sp (s.gpr .r2) (arg s 0) (arg s 2) (arg s 4)
      (s.gpr .r1).toNat (s.gpr .r3).toNat (arg s 1).toNat (arg s 3).toNat (arg s 5).toNat s)
    {s₁ s₂ : State} (h₂ : pre s₂) (hq : onePub s₁ s₂) :
    EntI (s₁.gpr .r0) (arg s₁ 6) s₁.sp (s₁.gpr .r2) (arg s₁ 0) (arg s₁ 2) (arg s₁ 4) (s₁.gpr .r1).toNat
      (s₁.gpr .r3).toNat (arg s₁ 1).toNat (arg s₁ 3).toNat (arg s₁ 5).toNat s₂ := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, qa⟩ := hq
  have e := hpre h₂
  rwa [← q₀, ← q₁, ← q₂, ← q₃, ← q₄, ← qa 0 (by decide), ← qa 1 (by decide), ← qa 2 (by decide),
    ← qa 3 (by decide), ← qa 4 (by decide), ← qa 5 (by decide), ← qa 6 (by decide)] at e

theorem one_ct {pre : State → Prop}
    (hpre : ∀ {s}, pre s → EntI (s.gpr .r0) (arg s 6) s.sp (s.gpr .r2) (arg s 0) (arg s 2) (arg s 4)
      (s.gpr .r1).toNat (s.gpr .r3).toNat (arg s 1).toNat (arg s 3).toNat (arg s 5).toNat s)
    {c : Prog isa}
    (hc : ∀ {k w sp N A D T : BitVec 32} {R nl al n tl : Nat}, Lay k w sp → (R = 10 ∨ R = 12 ∨ R = 14) →
      al < 2 ^ 32 → 7 ≤ nl → nl ≤ 13 → n < 256 ^ (15 - nl) → n < 2 ^ 32 →
      Proof.AesGcm.Arm.CT (EntI k w sp N A D T R nl al n tl) c)
    {pub : State → State → Prop} (hp : ∀ s₁ s₂, pub s₁ s₂ → onePub s₁ s₂) :
    ConstantTime isa pre pub c := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂
  have Ar := (hpre h₁).1.ar
  exact (hc Ar.lay Ar.rounds Ar.al32 Ar.h7 Ar.h13 Ar.hn Ar.n32 _ _ _ _ _ _ ⟨hpre h₁, entI_pub hpre h₂ (hp _ _ hq)⟩
    e₁ e₂).1

theorem seal_ct : ConstantTime isa sealArm.pre sealArm.pub «seal» :=
  one_ct entI_seal (fun L hR hal h7 h13 hn hn4 => seal_ctI L hR hal h7 h13 hn hn4) fun _ _ h => h

theorem open_ct : ConstantTime isa openArm.pre openArm.pub «open» :=
  one_ct entI_open (fun L hR hal h7 h13 hn hn4 => open_ctI L hR hal h7 h13 hn hn4) fun _ _ h => h.1

/-- A state satisfying the precondition of `vg_aes_ccm_seal`: a 7-byte nonce,
no associated data, no data, a 4-byte tag at `0x3000` and `work` at 0. -/
def sealSat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | .r3 => 7 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8014 then 4 else if a = 0x8011 then 0x30 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0, 0⟩, ⟨0x8000, 28⟩]
  wr := [⟨0, 0⟩, ⟨0x3000, 4⟩, ⟨0, 2560⟩]

/-- A state satisfying the precondition of `vg_aes_ccm_open`: as `sealSat`,
with the tag read only. -/
def openSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0, 0⟩, ⟨0x3000, 4⟩, ⟨0x8000, 28⟩], wr := [⟨0, 0⟩, ⟨0, 2560⟩] }

theorem seal_verified : Verified Arm.target «seal» (Proof.AesCcm.sealScratchContract Arm.abi 16) :=
  Verified.of_correct (fun _ hs => seal_wp hs) seal_ct (by
    sig_implies [Proof.AesCcm.sealScratchContract, Proof.AesCcm.sealScratchSig, Spec.Ccm.sealPre, Spec.Ccm.sealPost,
      sealArm, sealPre, oneLay, onePub, bel16, arg, args, roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val, Arm.State.addr]
      [sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using sealSat)

theorem open_verified : Verified Arm.target «open» (Proof.AesCcm.openScratchContract Arm.abi 16) :=
  Verified.of_correct (fun _ hs => open_wp hs) open_ct
    { pre := by
        sig_implies_pre [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre, Spec.Ccm.openLeak,
          openArm, openPre, oneLay, onePub, openLeak, bel16, arg, args, roundsOk, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by
        intro s s' _ h
        sig_eval [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPost, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        simp only [openArm, openRes, ciph, Arm.State.addr] at h
        have e : ∀ x y : BitVec 32, (x ++ y).setWidth 32 = y := fun _ _ => BitVec.setWidth_append_eq_right
        intro _
        rw [e]
        exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre, Spec.Ccm.openLeak,
          openArm, openPre, oneLay, onePub, openLeak, bel16, arg, args, roundsOk, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] at h
        obtain ⟨hsp, hl, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6⟩ := h
        refine ⟨⟨hsp, h0, h1, h2, h3, fun i hi => ?_⟩, hl⟩
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 by omega_arith) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact a0
        · exact a1
        · exact a2
        · exact a3
        · exact a4
        · exact a5
        · exact a6
      sat := by
        sig_implies_sat [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre, Spec.Ccm.openLeak,
          openArm, openPre, oneLay, onePub, openLeak, bel16, arg, args, roundsOk, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
          [openSat, sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using openSat }

end VG.Proof.AesCcm.Arm
