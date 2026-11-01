module

public import VerifiedGarbage.Proof.X448.Field56Contract
public import VerifiedGarbage.Proof.X448.Field56MulContract
import VerifiedGarbage.Proof.Ed448.AArch64.Point56.MulFn
import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Conv
public import VerifiedGarbage.Impl.X448.AArch64.Field56
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Proof.X448.AArch64.Mem
public import VerifiedGarbage.Proof.X448.Field
public import VerifiedGarbage.Proof.X448.Wide.Limbs
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Ed448
meta import VerifiedGarbage.Proof.Ed448.AArch64.Point56.MulFn
meta import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Conv
meta import VerifiedGarbage.Impl.X448.AArch64.Field56
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.X448.AArch64.Mem
meta import VerifiedGarbage.Proof.X448.Field
meta import VerifiedGarbage.Proof.X448.Wide.Limbs
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ed448
meta import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Field

/-!
# `vg_gf448_r56_mul` on AArch64, verified

The function meets `mulContract` of `Proof/X448/Field56MulContract.lean`, with no stack: the proof
against `mulF`, the contract's facts by register, from `mulFn_ok`. The elements as the contract
reads them are the proofs' (`Conv.lean`): the result's limbs are `prodOut`'s, below `Mb`
(`prod_bound`), and its value the product (`prod_val`); the bytes kept are those outside the
result and the operand sums. The callee-saved registers are restored (`MulPost`) and no
instruction writes `v8`–`v15`. Constant time by taint tracking: only the pointer and the
offsets, in `x0`–`x3`, are public, and every address is `ws` plus an offset plus a constant.
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Point56

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.Curve448.AArch64.Fast (KA)
open VG.Proof.X448.AArch64 (limbs ofs ofs_off)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib prodOut prod_val prod_bound)
open VG.Proof.X448.Field56 (elemAt LimbsLt Fits elemBytes opBound resBound own)

/-- The working space's facts: `ws` in `x0`, its 8192 bytes the only region. -/
def mPre (s : State) : Prop :=
  s.rd = [] ∧ s.wr = [⟨s.gpr .x0, 8192⟩] ∧ (s.gpr .x0).toNat + 8192 ≤ 2 ^ 64

def mulF : Contract AArch64.isa where
  pre s := mPre s ∧ Fits (s.gpr .x1) ∧ Fits (s.gpr .x2) ∧ Fits (s.gpr .x3) ∧
    ((s.gpr .x1).toNat + elemBytes ≤ (s.gpr .x3).toNat ∨
      (s.gpr .x3).toNat + elemBytes ≤ (s.gpr .x1).toNat) ∧
    LimbsLt s.mem (s.gpr .x0) (s.gpr .x2).toNat opBound ∧
    LimbsLt s.mem (s.gpr .x0) (s.gpr .x3).toNat opBound
  post s s' := LimbsLt s'.mem (s.gpr .x0) (s.gpr .x1).toNat resBound ∧
    elemAt s'.mem (s.gpr .x0) (s.gpr .x1).toNat =
      elemAt s.mem (s.gpr .x0) (s.gpr .x2).toNat * elemAt s.mem (s.gpr .x0) (s.gpr .x3).toNat ∧
    Proof.X448.Field56.Keeps (s.gpr .x0)
      (((s.gpr .x1).toNat, (s.gpr .x1).toNat + elemBytes) :: own) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

theorem elemAt_limbs (m : Mem) (ws : Addr) (o : Nat) :
    elemAt m ws o = VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN (limbs m ws o) 8) := by
  simp only [elemAt, Proof.X448.Field56.valAt, Proof.X448.Field56.limbs, valN_eq]
  rfl

/-- No instruction of the function writes `v8`–`v15`. -/
theorem mulFn_keepsV : Point56.mulFn.allInstrs keepsV = true := by decide +kernel

theorem mul_arm (s : State) (hs : mulF.pre s) :
    ∃ t s', Exec isa Point56.mulFn s t s' ∧ abiPreserved s s' ∧ mulF.post s s' := by
  obtain ⟨⟨_, hw, hn⟩, ho, ha, hb, hob, fa, fb⟩ := hs
  have e64 : elemBytes = 64 := rfl
  have eacc : Proof.X448.Field56.accAt = 3584 := rfl
  simp only [Fits, e64, eacc] at ho ha hb
  rw [e64] at hob
  have hp : MulPre s :=
    ⟨by rw [hw]; exact List.mem_singleton_self _, hn, ho, ha, hb, hob, fa, fb⟩
  obtain ⟨t, u, he, ⟨hg, h3, h12, hr, hwr, hsp, hv, hm⟩, hV⟩ :=
    WP.preservedV (mulFn_ok hp) mulFn_keepsV
  refine ⟨t, u, he, ⟨fun r hr' => hg r (by revert hr'; revert r; decide), hsp, hV⟩, ?_, ?_, ?_⟩
  · intro i hi
    change limbs u.mem _ _ i < _
    rw [hv i hi]
    exact prod_bound fa fb i hi
  · rw [elemAt_limbs, elemAt_limbs, elemAt_limbs, VG.Proof.X448.Wide.valN_congr hv]
    exact prod_val _ _
  · intro i hi hr'
    have hW : Proof.X448.Field56.wsBytes = 8192 := rfl
    rw [hW] at hi
    have h1 := hr' _ List.mem_cons_self
    have h2 := hr' _ (List.mem_cons_of_mem _ List.mem_cons_self)
    simp only [e64] at h1
    simp only [Proof.X448.Field56.accAt, Proof.X448.Field56.accEnd] at h2
    have ho' : ofs (s.gpr .x0) (s.gpr .x0 + BitVec.ofNat 64 i) = i := by
      have := ofs_off (s.gpr .x0) (d := 0) (i := i) (by omega)
      simp only [VG.Proof.X448.AArch64.off, BitVec.add_zero, Nat.zero_add] at this
      exact this
    exact hm _ (by rw [ho']; omega) (by rw [ho']; have : KA = 3584 := rfl; omega)

/-! ## Constant time -/

theorem mul_ct : ConstantTime isa mulF.pre mulF.pub Point56.mulFn :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ hp => ⟨hp.2.2.2.2, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hp.1
      · exact hp.2.1
      · exact hp.2.2.1
      · exact hp.2.2.2.1⟩) (by taint_decide)

/-! ## The shared contract -/

/-- A state satisfying the precondition: `ws` at `0x1000` holding zeros, the result and the
first operand at offset 0, the second at 64, and the stack at `0x10000`. -/
def mulSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x3 => 64 | _ => 0
  sp := 0x10000
  mem := fun _ => 0
  rd := []
  wr := [⟨0x1000, 8192⟩]

theorem mulSat_a : LimbsLt (fun _ => 0) 0x1000 0 opBound := by
  unfold LimbsLt; decide +kernel

theorem mulSat_b : LimbsLt (fun _ => 0) 0x1000 64 opBound := by
  unfold LimbsLt; decide +kernel

theorem mulFn_verified :
    Verified AArch64.target Point56.mulFn (Proof.X448.Field56.mulContract AArch64.abi) :=
  Verified.of_correct mul_arm mul_ct
    { pre := by sig_implies_pre [Proof.X448.Field56.mulContract, Proof.X448.Field56.mulSig, mulF, mPre,
        AArch64.abi, AArch64.argRegs]
      post := by sig_implies_post [Proof.X448.Field56.mulContract, Proof.X448.Field56.mulSig, mulF, mPre,
        AArch64.abi, AArch64.argRegs]
      pub := by sig_implies_pub [Proof.X448.Field56.mulContract, Proof.X448.Field56.mulSig, mulF, mPre,
        AArch64.abi, AArch64.argRegs]
      sat := ⟨mulSat, by
        unfold Proof.X448.Field56.mulContract
        exact Sig.contract_pre_of_check (by decide +kernel) (by
          sig_reduce [Sig.wfPre, Proof.X448.Field56.mulSig, AArch64.abi, AArch64.argRegs, mulSat]
          exact ⟨by decide, by decide, by decide, by decide, by decide, mulSat_a, mulSat_b⟩)⟩ }

end VG.Proof.Ed448.AArch64.Point56
