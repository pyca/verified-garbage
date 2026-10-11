import VerifiedGarbage.Proof.Ed25519.Arm.MulFnFn
import VerifiedGarbage.Proof.Ed25519.Arm.SpecConv
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Contract

/-!
# `vg_gf25519_r16_mul` on ARMv7, verified

The function (`mulFn_ok`) meets `mulContract` of
`Spec/X25519/Field16.lean` (`mul_arm`, against `mulArm`, the contract's
facts by register): its limbs and values are the proofs' (`limbAt_eq`,
`valAt_eq`). Constant time by taint tracking: only the pointer and the
offsets, in `r0`–`r3`, are public, and every address is `ws` plus a constant,
or an offset plus a constant or the rows' counter.
-/

namespace VG.Proof.Ed25519.Arm

open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm
open VG.Spec.X25519 (P)

namespace Mul

open VG.Spec.X25519.Field16 (limbAt valN valAt Limbs Fits)

/-- The facts of `mulContract` about the state, by register: `ws`, `o`, `a` and `b` in
`r0`–`r3`. -/
def armPre (s : State) : Prop :=
  s.rd = [] ∧ s.wr = [⟨State.addr (s.gpr .r0), 4096⟩] ∧ (s.gpr .r0).toNat + 4096 ≤ 2 ^ 32 ∧
    Fits (s.gpr .r1) ∧ Fits (s.gpr .r2) ∧ Fits (s.gpr .r3) ∧
    Limbs s.mem (State.addr (s.gpr .r0)) (s.gpr .r2) ∧ Limbs s.mem (State.addr (s.gpr .r0)) (s.gpr .r3)

/-- The value at the offset in `r`. -/
abbrev argV (m : Mem) (s : State) (r : Reg) : Nat := valAt m (State.addr (s.gpr .r0)) (s.gpr r)

/-- What two runs agree on: the stack pointer and the arguments. -/
def armPub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3

/-- `mulContract` on ARMv7. -/
def mulArm : Contract Arm.isa where
  pre := armPre
  post s s' := Limbs s'.mem (State.addr (s.gpr .r0)) (s.gpr .r1) ∧
    argV s'.mem s .r1 % P = argV s.mem s .r2 * argV s.mem s .r3 % P ∧
    Spec.X25519.Field16.Keeps (State.addr (s.gpr .r0)) (s.gpr .r1) s.mem s'.mem
  pub := armPub

theorem valN_eq (m : Mem) (ws : Addr) (o : BitVec 32) :
    ∀ n, valN m ws o n = val16 (limb m ws o.toNat) n
  | 0 => rfl
  | n + 1 => by rw [valN, val16, valN_eq m ws o n]; rfl

theorem valAt_eq (m : Mem) (ws : Addr) (o : BitVec 32) : valAt m ws o = V m ws o.toNat :=
  valN_eq m ws o 16

theorem lim_of_limbs {m : Mem} {ws : Addr} {o : BitVec 32} (h : Limbs m ws o) : Lim m ws o.toNat :=
  fun k hk => h k hk

theorem limbs_of_lim {m : Mem} {ws : Addr} {o : BitVec 32} (h : Lim m ws o.toNat) : Limbs m ws o :=
  fun k hk => h k hk

theorem keeps_of_frame {B : Addr} {o : Nat} {m m' : Mem}
    (hf : Frame [⟨B + BitVec.ofNat 64 o, 64⟩, ⟨B + BitVec.ofNat 64 ACC, 160⟩] m m') (ho : o + 64 ≤ ACC) :
    Spec.X25519.Field16.Keeps B (BitVec.ofNat 32 o) m m' := by
  intro i hi hown hoi
  have hA := ACC_eq
  have ho' : (BitVec.ofNat 32 o).toNat = o := toNat_imm (by omega)
  rw [ho'] at hoi
  simp only [Spec.X25519.Field16.wsBytes, Spec.X25519.Field16.ownAt, Spec.X25519.Field16.ownEnd,
    Spec.X25519.Field16.elemBytes, Spec.X25519.Field16.limbs] at hi hown hoi
  have hc : (⟨B + BitVec.ofNat 64 i, 1⟩ : Region).Contains (B + BitVec.ofNat 64 i) 1 := by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
  refine hf _ fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint _ (d := i) (n := 1) (e := o) (k := 64) (by omega) (by omega) (by omega) _ hc
  · exact Offset.disjoint _ (d := i) (n := 1) (e := ACC) (k := 160) (by omega) (by omega) (by omega) _ hc

theorem mul_arm (s : State) (hs : mulArm.pre s) :
    ∃ t s', Exec isa mulFn s t s' ∧ abiPreserved s s' ∧ mulArm.post s s' := by
  obtain ⟨_, hwr, hfit, f1, f2, f3, la, lb⟩ := hs
  have hA := ACC_eq
  have hc : CtxN 0 (s.gpr .r0) s := ⟨rfl, hfit, by rw [hwr]; exact List.mem_singleton_self _⟩
  have e : ∀ r, s.gpr r = BitVec.ofNat 32 (s.gpr r).toNat := fun r => by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  simp only [Fits, Spec.X25519.Field16.ownAt, Spec.X25519.Field16.elemBytes,
    Spec.X25519.Field16.limbs] at f1 f2 f3
  obtain ⟨t, s', he, hR, hF, hL, hV⟩ := mulFn_ok (o := (s.gpr .r1).toNat) (x := (s.gpr .r2).toNat)
    (y := (s.gpr .r3).toNat) (by omega) (by omega) (by omega) hc (e .r1) (e .r2) (e .r3) (lim_of_limbs la) (lim_of_limbs lb)
  refine ⟨t, s', he, ⟨fun r hr => hR.gpr r (by revert hr; cases r <;> decide), hR.sp⟩,
    limbs_of_lim hL, ?_, ?_⟩
  · rw [argV, argV, argV, valAt_eq, valAt_eq, valAt_eq]; exact hV
  · rw [e .r1]
    exact keeps_of_frame hF (by omega)

theorem armPub_agree {s₁ s₂ : State} (h : armPub s₁ s₂) :
    ∀ r ∈ [Reg.r0, .r1, .r2, .r3], s₁.gpr r = s₂.gpr r := by
  obtain ⟨_, h0, h1, h2, h3⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem mul_ct : ConstantTime isa mulArm.pre mulArm.pub mulFn :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by taint_decide)

/-- A state satisfying the precondition: `ws` at `0x1000`, the elements at offset 0, all zero. -/
def satF : State where
  gpr r := match r with
    | .r0 => 0x1000 | _ => 0
  sp := 0x10000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 4096⟩]

theorem limbs_zero (ws : Addr) : Limbs (fun _ => 0) ws 0 := by
  intro i _
  simp only [limbAt, Mem.readW, Mem.read]
  decide

theorem fits_zero : Fits 0 := by decide

theorem mul_sat : (Spec.X25519.Field16.mulContract Arm.abi).pre satF := by
  unfold Spec.X25519.Field16.mulContract
  exact Sig.contract_pre_of_check (by decide +kernel) (by
    sig_reduce [Sig.wfPre, Spec.X25519.Field16.sig, Arm.abi, Arm.argRegs, Arm.Loc.val, satF]
    exact ⟨by decide, fits_zero, fits_zero, fits_zero, limbs_zero _, limbs_zero _⟩)

theorem mulFn_verified : Verified Arm.target mulFn (Spec.X25519.Field16.mulContract Arm.abi) :=
  Verified.of_correct mul_arm mul_ct
    { pre := by sig_implies_pre [Spec.X25519.Field16.mulContract, Spec.X25519.Field16.sig, mulArm,
        armPre, armPub, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by sig_implies_post [Spec.X25519.Field16.mulContract, Spec.X25519.Field16.sig, mulArm,
        armPre, armPub, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      pub := by sig_implies_pub [Spec.X25519.Field16.mulContract, Spec.X25519.Field16.sig, mulArm,
        armPre, armPub, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := ⟨satF, mul_sat⟩ }

end Mul

end VG.Proof.Ed25519.Arm
