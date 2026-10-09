import VerifiedGarbage.Proof.X25519.Arm.Field16.Fn
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Contract

/-!
# `vg_gf25519_r16_mul` on ARMv7, verified

The function meets `mulContract` of `Spec/X25519/Field16.lean`, with no
stack: the proof against `mulF`, its facts by
register, which the contract implies; the contract's limbs and values are
the proofs' (`limbAt_eq`, `valAt_eq`), and the memory `mulFn_ok` keeps is
what `Keeps` says (`keeps_of_frame`). Constant time by taint tracking: only
the pointer and the offsets, in `r0`–`r3`, are public, and every address is
`ws`, or a pointer formed from it and an offset, plus a constant or the row
counter.
-/

namespace VG.Proof.X25519.Arm.Field16

open VG VG.Arm VG.Impl.X25519.Arm.Field16 VG.Proof.X25519.Arm
open VG.Spec.X25519 (P)
open VG.Spec.X25519.Field16 (limbAt valN valAt Limbs Fits Keeps)

/-- The precondition, by register: `ws` in `r0`, the offsets in `r1`–`r3`. -/
def fPre (s : State) : Prop :=
  s.rd = [] ∧ s.wr = [⟨State.addr (s.gpr .r0), 4096⟩] ∧ (s.gpr .r0).toNat + 4096 ≤ 2 ^ 32 ∧
    Fits (s.gpr .r1) ∧ Fits (s.gpr .r2) ∧ Fits (s.gpr .r3) ∧
    Limbs s.mem (State.addr (s.gpr .r0)) (s.gpr .r2) ∧ Limbs s.mem (State.addr (s.gpr .r0)) (s.gpr .r3)

/-- The value at the offset in `r`. -/
abbrev argV (m : Mem) (s : State) (r : Reg) : Nat := valAt m (State.addr (s.gpr .r0)) (s.gpr r)

/-- What two runs agree on: the stack pointer and the arguments. -/
def fPub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3

def mulF : Contract Arm.isa where
  pre := fPre
  post s s' := Limbs s'.mem (State.addr (s.gpr .r0)) (s.gpr .r1) ∧
    argV s'.mem s .r1 % P = argV s.mem s .r2 * argV s.mem s .r3 % P ∧
    Keeps (State.addr (s.gpr .r0)) (s.gpr .r1) s.mem s'.mem
  pub := fPub

theorem limbAt_eq (m : Mem) (ws : Addr) (o : BitVec 32) (i : Nat) :
    limbAt m ws o i = limb m ws o.toNat i := rfl

theorem valN_eq (m : Mem) (ws : Addr) (o : BitVec 32) :
    ∀ n, valN m ws o n = val16 (limb m ws o.toNat) n
  | 0 => rfl
  | n + 1 => by rw [valN, val16, valN_eq m ws o n, limbAt_eq]

theorem valAt_eq (m : Mem) (ws : Addr) (o : BitVec 32) : valAt m ws o = V m ws o.toNat :=
  valN_eq m ws o 16

/-- What the function keeps of `ws`: everything outside its frame. -/
theorem keeps_of_frame {b o : BitVec 32} {m m' : Mem}
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 o.toNat, 64⟩, ⟨State.addr b + BitVec.ofNat 64 ACC, 160⟩] m m') :
    Keeps (State.addr b) o m m' := by
  intro i hi hown ho
  have hA : ACC = 1472 := rfl
  simp only [Spec.X25519.Field16.wsBytes, Spec.X25519.Field16.ownAt, Spec.X25519.Field16.ownEnd,
    Spec.X25519.Field16.elemBytes, Spec.X25519.Field16.limbs] at hi hown ho
  have ho32 := o.isLt
  have hc : (⟨State.addr b + BitVec.ofNat 64 i, 1⟩ : Region).Contains (State.addr b + BitVec.ofNat 64 i) 1 := by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
  refine hf _ fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint _ (d := i) (n := 1) (e := o.toNat) (k := 64) (by omega) (by omega) (by omega) _ hc
  · exact Offset.disjoint _ (d := i) (n := 1) (e := ACC) (k := 160) (by omega) (by omega) (by omega) _ hc

theorem mul_arm (s : State) (hs : mulF.pre s) :
    ∃ t s', Exec isa mulFn s t s' ∧ abiPreserved s s' ∧ mulF.post s s' := by
  obtain ⟨_, hwr, hfit, ho, hx, hy, lx, ly⟩ := hs
  have hp : Pre (s.gpr .r0) (s.gpr .r1).toNat (s.gpr .r2).toNat (s.gpr .r3).toNat s :=
    ⟨⟨rfl, hfit, by rw [hwr]; exact List.mem_singleton_self _⟩, (by simp),
      (by simp), (by simp), ho, hx, hy, lx, ly⟩
  obtain ⟨t, s', he, hR, hF, hL, hV⟩ := mulFn_ok hp
  refine ⟨t, s', he, ⟨fun r hr => hR.gpr r (by revert hr; cases r <;> decide), hR.sp⟩, hL, ?_, keeps_of_frame hF⟩
  rw [argV, argV, argV, valAt_eq, valAt_eq, valAt_eq]
  exact hV

theorem fPub_agree {s₁ s₂ : State} (h : fPub s₁ s₂) : ∀ r ∈ [Reg.r0, .r1, .r2, .r3], s₁.gpr r = s₂.gpr r := by
  obtain ⟨_, h0, h1, h2, h3⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem gf25519_mul_ct : ConstantTime isa mulF.pre mulF.pub mulFn :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (fPub_agree hp)) (by taint_decide)

/-- A state satisfying the precondition: `ws` at `0x1000`, the elements at
offset 0, all zero, and the stack at `0x10000`. -/
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

theorem gf25519_mul_verified : Verified Arm.target mulFn (Spec.X25519.Field16.mulContract Arm.abi) :=
  Verified.of_correct mul_arm gf25519_mul_ct
    { pre := by sig_implies_pre [Spec.X25519.Field16.mulContract, Spec.X25519.Field16.sig, mulF, fPre,
        fPub, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by sig_implies_post [Spec.X25519.Field16.mulContract, Spec.X25519.Field16.sig, mulF, fPre,
        fPub, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      pub := by sig_implies_pub [Spec.X25519.Field16.mulContract, Spec.X25519.Field16.sig, mulF, fPre,
        fPub, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := ⟨satF, mul_sat⟩ }

end VG.Proof.X25519.Arm.Field16
