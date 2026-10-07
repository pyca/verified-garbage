import VerifiedGarbage.Proof.Weierstrass.Arm.MontContract
import VerifiedGarbage.Proof.Weierstrass.Arm.MontModuli
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Contract

/-!
# Montgomery arithmetic modulo the curves' `p` and `n`, as functions, on 32-bit ARM: verified

Each modulus of `Spec.Weierstrass.Mont.moduli` is one the functions support
(`ModOk`), so each of its functions meets the contract of its `Api`: the
proof against `mulArm`, `addArm` or `subArm`, which it implies, constant
time by taint tracking (only the pointer and the offsets, in `r0`–`r3`, are
public), and a state satisfying it (`sat`).
-/

namespace VG.Proof.Weierstrass.Arm.Mont

open VG VG.Arm VG.Impl.Weierstrass.Arm.Mont Spec.Weierstrass.Mont

theorem armPub_agree {s₁ s₂ : State} (h : armPub s₁ s₂) : ∀ r ∈ [Reg.r0, .r1, .r2, .r3], s₁.gpr r = s₂.gpr r := by
  obtain ⟨_, h0, h1, h2, h3⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem read_zero : ∀ (n : Nat) (a : Addr), (Mem.read (fun _ => 0) a n).toNat = 0
  | 0, _ => rfl
  | n + 1, a => by rw [VG.Proof.Mont.read_toNat_succ, read_zero n]; rfl

theorem numAt_zero (ws : Addr) (o : BitVec 32) (k : Nat) : numAt (fun _ => 0) ws o k = 0 :=
  read_zero _ _

/-- The witness's offsets satisfy the precondition, for any modulus. -/
theorem fit_zero (M : Modulus) (hk : M.k ≤ 9) : M.Fit 0 0 0 := by
  have h0 : (0 : BitVec 32).toNat = 0 := rfl
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Fits, ownAt, ownBytes, h0] <;> omega

/-- The witness satisfies `mul`'s precondition. -/
theorem mul_zero (M : Modulus) (hk : M.k ≤ 9) (hm : 0 < M.m) (ws : Addr) :
    M.Fit 0 0 0 ∧ numAt (fun _ => 0) ws 0 M.k < M.m :=
  ⟨fit_zero M hk, by rw [numAt_zero]; exact hm⟩

/-- The witness satisfies `add`'s precondition. -/
theorem add_zero (M : Modulus) (hk : M.k ≤ 9) (hm : 0 < M.m) (ws : Addr) :
    M.Fit 0 0 0 ∧ numAt (fun _ => 0) ws 0 M.k + numAt (fun _ => 0) ws 0 M.k < 2 * M.m :=
  ⟨fit_zero M hk, by rw [numAt_zero]; omega⟩

/-- The witness satisfies `sub`'s precondition. -/
theorem sub_zero (M : Modulus) (hk : M.k ≤ 9) (hm : 0 < M.m) (ws : Addr) :
    M.Fit 0 0 0 ∧ numAt (fun _ => 0) ws 0 M.k < M.m ∧ numAt (fun _ => 0) ws 0 M.k < M.m :=
  ⟨fit_zero M hk, by rw [numAt_zero]; exact hm, by rw [numAt_zero]; exact hm⟩

/-- A state satisfying the preconditions: `ws` at `0x1000`, the numbers at
offset 0, all zero. -/
def sat : State where
  gpr r := match r with
    | .r0 => 0x1000 | _ => 0
  sp := 0x10000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 8192⟩]

/-- The witness satisfies each function's precondition, for any modulus. -/
theorem mul_sat (M : Modulus) (hk : M.k ≤ 9) (hm : 0 < M.m) : (M.mulContract Arm.abi).pre sat :=
  Sig.contract_pre_of_check (by decide +kernel) (by
    sig_reduce [Sig.wfPre, sig, Arm.abi, Arm.argRegs, Arm.Loc.val, sat]
    exact ⟨by decide, mul_zero M hk hm _⟩)

theorem add_sat (M : Modulus) (hk : M.k ≤ 9) (hm : 0 < M.m) : (M.addContract Arm.abi).pre sat :=
  Sig.contract_pre_of_check (by decide +kernel) (by
    sig_reduce [Sig.wfPre, sig, Arm.abi, Arm.argRegs, Arm.Loc.val, sat]
    exact ⟨by decide, add_zero M hk hm _⟩)

theorem sub_sat (M : Modulus) (hk : M.k ≤ 9) (hm : 0 < M.m) : (M.subContract Arm.abi).pre sat :=
  Sig.contract_pre_of_check (by decide +kernel) (by
    sig_reduce [Sig.wfPre, sig, Arm.abi, Arm.argRegs, Arm.Loc.val, sat]
    exact ⟨by decide, sub_zero M hk hm _⟩)

theorem p224p_mul_ct : ConstantTime isa (mulArm p224p).pre (mulArm p224p).pub (mulFn p224p.k p224p.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by taint_decide)

theorem p224p_mul_verified : Verified Arm.target (mulFn p224p.k p224p.m) (p224p.mulContract Arm.abi) :=
  Verified.of_correct (mul_arm p224p_ok) p224p_mul_ct
    { pre := by sig_implies_pre [Modulus.mulContract, sig, arg, mulArm, armPre, armPub, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by sig_implies_post [Modulus.mulContract, sig, arg, mulArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      pub := by sig_implies_pub [Modulus.mulContract, sig, arg, mulArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := ⟨sat, mul_sat p224p (by decide) (VG.Proof.Mont.Arm.m_pos_of_inv p224p_ok.inv)⟩ }

theorem p224p_add_ct : ConstantTime isa (addArm p224p).pre (addArm p224p).pub (addFn p224p.k p224p.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by taint_decide)

theorem p224p_add_verified : Verified Arm.target (addFn p224p.k p224p.m) (p224p.addContract Arm.abi) :=
  Verified.of_correct (add_arm p224p_ok) p224p_add_ct
    { pre := by sig_implies_pre [Modulus.addContract, sig, arg, addArm, armPre, armPub, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by sig_implies_post [Modulus.addContract, sig, arg, addArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      pub := by sig_implies_pub [Modulus.addContract, sig, arg, addArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := ⟨sat, add_sat p224p (by decide) (VG.Proof.Mont.Arm.m_pos_of_inv p224p_ok.inv)⟩ }

theorem p224p_sub_ct : ConstantTime isa (subArm p224p).pre (subArm p224p).pub (subFn p224p.k p224p.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by taint_decide)

theorem p224p_sub_verified : Verified Arm.target (subFn p224p.k p224p.m) (p224p.subContract Arm.abi) :=
  Verified.of_correct (sub_arm p224p_ok) p224p_sub_ct
    { pre := by sig_implies_pre [Modulus.subContract, sig, arg, subArm, armPre, armPub, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by sig_implies_post [Modulus.subContract, sig, arg, subArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      pub := by sig_implies_pub [Modulus.subContract, sig, arg, subArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := ⟨sat, sub_sat p224p (by decide) (VG.Proof.Mont.Arm.m_pos_of_inv p224p_ok.inv)⟩ }

theorem p224n_mul_ct : ConstantTime isa (mulArm p224n).pre (mulArm p224n).pub (mulFn p224n.k p224n.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by taint_decide)

theorem p224n_mul_verified : Verified Arm.target (mulFn p224n.k p224n.m) (p224n.mulContract Arm.abi) :=
  Verified.of_correct (mul_arm p224n_ok) p224n_mul_ct
    { pre := by sig_implies_pre [Modulus.mulContract, sig, arg, mulArm, armPre, armPub, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by sig_implies_post [Modulus.mulContract, sig, arg, mulArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      pub := by sig_implies_pub [Modulus.mulContract, sig, arg, mulArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := ⟨sat, mul_sat p224n (by decide) (VG.Proof.Mont.Arm.m_pos_of_inv p224n_ok.inv)⟩ }

theorem p224n_add_ct : ConstantTime isa (addArm p224n).pre (addArm p224n).pub (addFn p224n.k p224n.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by taint_decide)

theorem p224n_add_verified : Verified Arm.target (addFn p224n.k p224n.m) (p224n.addContract Arm.abi) :=
  Verified.of_correct (add_arm p224n_ok) p224n_add_ct
    { pre := by sig_implies_pre [Modulus.addContract, sig, arg, addArm, armPre, armPub, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by sig_implies_post [Modulus.addContract, sig, arg, addArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      pub := by sig_implies_pub [Modulus.addContract, sig, arg, addArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := ⟨sat, add_sat p224n (by decide) (VG.Proof.Mont.Arm.m_pos_of_inv p224n_ok.inv)⟩ }

theorem p224n_sub_ct : ConstantTime isa (subArm p224n).pre (subArm p224n).pub (subFn p224n.k p224n.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by taint_decide)

theorem p224n_sub_verified : Verified Arm.target (subFn p224n.k p224n.m) (p224n.subContract Arm.abi) :=
  Verified.of_correct (sub_arm p224n_ok) p224n_sub_ct
    { pre := by sig_implies_pre [Modulus.subContract, sig, arg, subArm, armPre, armPub, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by sig_implies_post [Modulus.subContract, sig, arg, subArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      pub := by sig_implies_pub [Modulus.subContract, sig, arg, subArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := ⟨sat, sub_sat p224n (by decide) (VG.Proof.Mont.Arm.m_pos_of_inv p224n_ok.inv)⟩ }

theorem p256p_mul_ct : ConstantTime isa (mulArm p256p).pre (mulArm p256p).pub (mulFn p256p.k p256p.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by taint_decide)

theorem p256p_mul_verified : Verified Arm.target (mulFn p256p.k p256p.m) (p256p.mulContract Arm.abi) :=
  Verified.of_correct (mul_arm p256p_ok) p256p_mul_ct
    { pre := by sig_implies_pre [Modulus.mulContract, sig, arg, mulArm, armPre, armPub, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by sig_implies_post [Modulus.mulContract, sig, arg, mulArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      pub := by sig_implies_pub [Modulus.mulContract, sig, arg, mulArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := ⟨sat, mul_sat p256p (by decide) (VG.Proof.Mont.Arm.m_pos_of_inv p256p_ok.inv)⟩ }

theorem p256p_add_ct : ConstantTime isa (addArm p256p).pre (addArm p256p).pub (addFn p256p.k p256p.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by taint_decide)

theorem p256p_add_verified : Verified Arm.target (addFn p256p.k p256p.m) (p256p.addContract Arm.abi) :=
  Verified.of_correct (add_arm p256p_ok) p256p_add_ct
    { pre := by sig_implies_pre [Modulus.addContract, sig, arg, addArm, armPre, armPub, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by sig_implies_post [Modulus.addContract, sig, arg, addArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      pub := by sig_implies_pub [Modulus.addContract, sig, arg, addArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := ⟨sat, add_sat p256p (by decide) (VG.Proof.Mont.Arm.m_pos_of_inv p256p_ok.inv)⟩ }

theorem p256p_sub_ct : ConstantTime isa (subArm p256p).pre (subArm p256p).pub (subFn p256p.k p256p.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by taint_decide)

theorem p256p_sub_verified : Verified Arm.target (subFn p256p.k p256p.m) (p256p.subContract Arm.abi) :=
  Verified.of_correct (sub_arm p256p_ok) p256p_sub_ct
    { pre := by sig_implies_pre [Modulus.subContract, sig, arg, subArm, armPre, armPub, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by sig_implies_post [Modulus.subContract, sig, arg, subArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      pub := by sig_implies_pub [Modulus.subContract, sig, arg, subArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := ⟨sat, sub_sat p256p (by decide) (VG.Proof.Mont.Arm.m_pos_of_inv p256p_ok.inv)⟩ }

theorem p256n_mul_ct : ConstantTime isa (mulArm p256n).pre (mulArm p256n).pub (mulFn p256n.k p256n.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by taint_decide)

theorem p256n_mul_verified : Verified Arm.target (mulFn p256n.k p256n.m) (p256n.mulContract Arm.abi) :=
  Verified.of_correct (mul_arm p256n_ok) p256n_mul_ct
    { pre := by sig_implies_pre [Modulus.mulContract, sig, arg, mulArm, armPre, armPub, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by sig_implies_post [Modulus.mulContract, sig, arg, mulArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      pub := by sig_implies_pub [Modulus.mulContract, sig, arg, mulArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := ⟨sat, mul_sat p256n (by decide) (VG.Proof.Mont.Arm.m_pos_of_inv p256n_ok.inv)⟩ }

theorem p256n_add_ct : ConstantTime isa (addArm p256n).pre (addArm p256n).pub (addFn p256n.k p256n.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by taint_decide)

theorem p256n_add_verified : Verified Arm.target (addFn p256n.k p256n.m) (p256n.addContract Arm.abi) :=
  Verified.of_correct (add_arm p256n_ok) p256n_add_ct
    { pre := by sig_implies_pre [Modulus.addContract, sig, arg, addArm, armPre, armPub, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by sig_implies_post [Modulus.addContract, sig, arg, addArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      pub := by sig_implies_pub [Modulus.addContract, sig, arg, addArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := ⟨sat, add_sat p256n (by decide) (VG.Proof.Mont.Arm.m_pos_of_inv p256n_ok.inv)⟩ }

theorem p256n_sub_ct : ConstantTime isa (subArm p256n).pre (subArm p256n).pub (subFn p256n.k p256n.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by taint_decide)

theorem p256n_sub_verified : Verified Arm.target (subFn p256n.k p256n.m) (p256n.subContract Arm.abi) :=
  Verified.of_correct (sub_arm p256n_ok) p256n_sub_ct
    { pre := by sig_implies_pre [Modulus.subContract, sig, arg, subArm, armPre, armPub, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by sig_implies_post [Modulus.subContract, sig, arg, subArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      pub := by sig_implies_pub [Modulus.subContract, sig, arg, subArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := ⟨sat, sub_sat p256n (by decide) (VG.Proof.Mont.Arm.m_pos_of_inv p256n_ok.inv)⟩ }

theorem p384p_mul_ct : ConstantTime isa (mulArm p384p).pre (mulArm p384p).pub (mulFn p384p.k p384p.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by taint_decide)

theorem p384p_mul_verified : Verified Arm.target (mulFn p384p.k p384p.m) (p384p.mulContract Arm.abi) :=
  Verified.of_correct (mul_arm p384p_ok) p384p_mul_ct
    { pre := by sig_implies_pre [Modulus.mulContract, sig, arg, mulArm, armPre, armPub, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by sig_implies_post [Modulus.mulContract, sig, arg, mulArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      pub := by sig_implies_pub [Modulus.mulContract, sig, arg, mulArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := ⟨sat, mul_sat p384p (by decide) (VG.Proof.Mont.Arm.m_pos_of_inv p384p_ok.inv)⟩ }

theorem p384p_add_ct : ConstantTime isa (addArm p384p).pre (addArm p384p).pub (addFn p384p.k p384p.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by taint_decide)

theorem p384p_add_verified : Verified Arm.target (addFn p384p.k p384p.m) (p384p.addContract Arm.abi) :=
  Verified.of_correct (add_arm p384p_ok) p384p_add_ct
    { pre := by sig_implies_pre [Modulus.addContract, sig, arg, addArm, armPre, armPub, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by sig_implies_post [Modulus.addContract, sig, arg, addArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      pub := by sig_implies_pub [Modulus.addContract, sig, arg, addArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := ⟨sat, add_sat p384p (by decide) (VG.Proof.Mont.Arm.m_pos_of_inv p384p_ok.inv)⟩ }

theorem p384p_sub_ct : ConstantTime isa (subArm p384p).pre (subArm p384p).pub (subFn p384p.k p384p.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by taint_decide)

theorem p384p_sub_verified : Verified Arm.target (subFn p384p.k p384p.m) (p384p.subContract Arm.abi) :=
  Verified.of_correct (sub_arm p384p_ok) p384p_sub_ct
    { pre := by sig_implies_pre [Modulus.subContract, sig, arg, subArm, armPre, armPub, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by sig_implies_post [Modulus.subContract, sig, arg, subArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      pub := by sig_implies_pub [Modulus.subContract, sig, arg, subArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := ⟨sat, sub_sat p384p (by decide) (VG.Proof.Mont.Arm.m_pos_of_inv p384p_ok.inv)⟩ }

theorem p384n_mul_ct : ConstantTime isa (mulArm p384n).pre (mulArm p384n).pub (mulFn p384n.k p384n.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by taint_decide)

theorem p384n_mul_verified : Verified Arm.target (mulFn p384n.k p384n.m) (p384n.mulContract Arm.abi) :=
  Verified.of_correct (mul_arm p384n_ok) p384n_mul_ct
    { pre := by sig_implies_pre [Modulus.mulContract, sig, arg, mulArm, armPre, armPub, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by sig_implies_post [Modulus.mulContract, sig, arg, mulArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      pub := by sig_implies_pub [Modulus.mulContract, sig, arg, mulArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := ⟨sat, mul_sat p384n (by decide) (VG.Proof.Mont.Arm.m_pos_of_inv p384n_ok.inv)⟩ }

theorem p384n_add_ct : ConstantTime isa (addArm p384n).pre (addArm p384n).pub (addFn p384n.k p384n.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by taint_decide)

theorem p384n_add_verified : Verified Arm.target (addFn p384n.k p384n.m) (p384n.addContract Arm.abi) :=
  Verified.of_correct (add_arm p384n_ok) p384n_add_ct
    { pre := by sig_implies_pre [Modulus.addContract, sig, arg, addArm, armPre, armPub, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by sig_implies_post [Modulus.addContract, sig, arg, addArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      pub := by sig_implies_pub [Modulus.addContract, sig, arg, addArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := ⟨sat, add_sat p384n (by decide) (VG.Proof.Mont.Arm.m_pos_of_inv p384n_ok.inv)⟩ }

theorem p384n_sub_ct : ConstantTime isa (subArm p384n).pre (subArm p384n).pub (subFn p384n.k p384n.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by taint_decide)

theorem p384n_sub_verified : Verified Arm.target (subFn p384n.k p384n.m) (p384n.subContract Arm.abi) :=
  Verified.of_correct (sub_arm p384n_ok) p384n_sub_ct
    { pre := by sig_implies_pre [Modulus.subContract, sig, arg, subArm, armPre, armPub, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by sig_implies_post [Modulus.subContract, sig, arg, subArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      pub := by sig_implies_pub [Modulus.subContract, sig, arg, subArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := ⟨sat, sub_sat p384n (by decide) (VG.Proof.Mont.Arm.m_pos_of_inv p384n_ok.inv)⟩ }

theorem p521p_mul_ct : ConstantTime isa (mulArm p521p).pre (mulArm p521p).pub (mulFn p521p.k p521p.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by taint_decide)

theorem p521p_mul_verified : Verified Arm.target (mulFn p521p.k p521p.m) (p521p.mulContract Arm.abi) :=
  Verified.of_correct (mul_arm p521p_ok) p521p_mul_ct
    { pre := by sig_implies_pre [Modulus.mulContract, sig, arg, mulArm, armPre, armPub, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by sig_implies_post [Modulus.mulContract, sig, arg, mulArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      pub := by sig_implies_pub [Modulus.mulContract, sig, arg, mulArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := ⟨sat, mul_sat p521p (by decide) (VG.Proof.Mont.Arm.m_pos_of_inv p521p_ok.inv)⟩ }

theorem p521p_add_ct : ConstantTime isa (addArm p521p).pre (addArm p521p).pub (addFn p521p.k p521p.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by taint_decide)

theorem p521p_add_verified : Verified Arm.target (addFn p521p.k p521p.m) (p521p.addContract Arm.abi) :=
  Verified.of_correct (add_arm p521p_ok) p521p_add_ct
    { pre := by sig_implies_pre [Modulus.addContract, sig, arg, addArm, armPre, armPub, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by sig_implies_post [Modulus.addContract, sig, arg, addArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      pub := by sig_implies_pub [Modulus.addContract, sig, arg, addArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := ⟨sat, add_sat p521p (by decide) (VG.Proof.Mont.Arm.m_pos_of_inv p521p_ok.inv)⟩ }

theorem p521p_sub_ct : ConstantTime isa (subArm p521p).pre (subArm p521p).pub (subFn p521p.k p521p.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by taint_decide)

theorem p521p_sub_verified : Verified Arm.target (subFn p521p.k p521p.m) (p521p.subContract Arm.abi) :=
  Verified.of_correct (sub_arm p521p_ok) p521p_sub_ct
    { pre := by sig_implies_pre [Modulus.subContract, sig, arg, subArm, armPre, armPub, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by sig_implies_post [Modulus.subContract, sig, arg, subArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      pub := by sig_implies_pub [Modulus.subContract, sig, arg, subArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := ⟨sat, sub_sat p521p (by decide) (VG.Proof.Mont.Arm.m_pos_of_inv p521p_ok.inv)⟩ }

theorem p521n_mul_ct : ConstantTime isa (mulArm p521n).pre (mulArm p521n).pub (mulFn p521n.k p521n.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by taint_decide)

theorem p521n_mul_verified : Verified Arm.target (mulFn p521n.k p521n.m) (p521n.mulContract Arm.abi) :=
  Verified.of_correct (mul_arm p521n_ok) p521n_mul_ct
    { pre := by sig_implies_pre [Modulus.mulContract, sig, arg, mulArm, armPre, armPub, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by sig_implies_post [Modulus.mulContract, sig, arg, mulArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      pub := by sig_implies_pub [Modulus.mulContract, sig, arg, mulArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := ⟨sat, mul_sat p521n (by decide) (VG.Proof.Mont.Arm.m_pos_of_inv p521n_ok.inv)⟩ }

theorem p521n_add_ct : ConstantTime isa (addArm p521n).pre (addArm p521n).pub (addFn p521n.k p521n.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by taint_decide)

theorem p521n_add_verified : Verified Arm.target (addFn p521n.k p521n.m) (p521n.addContract Arm.abi) :=
  Verified.of_correct (add_arm p521n_ok) p521n_add_ct
    { pre := by sig_implies_pre [Modulus.addContract, sig, arg, addArm, armPre, armPub, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by sig_implies_post [Modulus.addContract, sig, arg, addArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      pub := by sig_implies_pub [Modulus.addContract, sig, arg, addArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := ⟨sat, add_sat p521n (by decide) (VG.Proof.Mont.Arm.m_pos_of_inv p521n_ok.inv)⟩ }

theorem p521n_sub_ct : ConstantTime isa (subArm p521n).pre (subArm p521n).pub (subFn p521n.k p521n.m) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by taint_decide)

theorem p521n_sub_verified : Verified Arm.target (subFn p521n.k p521n.m) (p521n.subContract Arm.abi) :=
  Verified.of_correct (sub_arm p521n_ok) p521n_sub_ct
    { pre := by sig_implies_pre [Modulus.subContract, sig, arg, subArm, armPre, armPub, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by sig_implies_post [Modulus.subContract, sig, arg, subArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      pub := by sig_implies_pub [Modulus.subContract, sig, arg, subArm, armPre, armPub, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := ⟨sat, sub_sat p521n (by decide) (VG.Proof.Mont.Arm.m_pos_of_inv p521n_ok.inv)⟩ }

end VG.Proof.Weierstrass.Arm.Mont
