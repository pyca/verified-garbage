import VerifiedGarbage.Proof.Weierstrass.AArch64.MontContract
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontModuli
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Montgomery products modulo the curves' `p` and `n`, as functions, on AArch64: verified

Each modulus of P-224, P-384 and P-521 is one the functions support
(`ModOk`), so each of its products meets the contract of its `Api`: the
proof against `mulA`, which it implies, constant time by `ct_zext` and taint
tracking (only the pointer and the offsets are public), and a state
satisfying it (`sat`).
-/

namespace VG.Proof.Weierstrass.AArch64.Mont

open VG VG.AArch64 VG.Impl.Weierstrass.AArch64.Mont Spec.Weierstrass.Mont

theorem read_zero : ∀ (n : Nat) (a : Addr), (Mem.read (fun _ => 0) a n).toNat = 0
  | 0, _ => rfl
  | n + 1, a => by rw [VG.Proof.Mont.read_toNat_succ, read_zero n]; rfl

theorem numAt_zero (ws : Addr) (o : BitVec 32) (k : Nat) : numAt (fun _ => 0) ws o k = 0 :=
  read_zero _ _

/-- A state satisfying the precondition: `ws` at `0x1000`, the numbers at
offset 0, all zero. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 8192⟩]

/-- The witness's offsets satisfy the precondition, for any modulus. -/
theorem fit_zero (M : Modulus) (hk : M.k ≤ 9) : M.Fit 0 0 0 := by
  have h0 : (0 : BitVec 32).toNat = 0 := rfl
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Fits, ownAt, ownBytes, h0] <;> omega

/-- The witness satisfies `mul`'s precondition. -/
theorem mul_zero (M : Modulus) (hk : M.k ≤ 9) (hm : 0 < M.m) (ws : Addr) :
    M.Fit 0 0 0 ∧ numAt (fun _ => 0) ws 0 M.k < M.m :=
  ⟨fit_zero M hk, by rw [numAt_zero]; exact hm⟩

theorem mul_sat (M : Modulus) (hk : M.k ≤ 9) (hm : 0 < M.m) : (M.mulContract AArch64.abi).pre sat :=
  Sig.contract_pre_of_check (by decide +kernel) (by
    sig_reduce [Sig.wfPre, sig, AArch64.abi, AArch64.argRegs, sat]
    exact ⟨by decide, mul_zero M hk hm _⟩)

theorem m_pos_of_inv {m x : Nat} (h : (m * x + 1) % 2 ^ 64 = 0) : 0 < m := by
  rcases Nat.eq_zero_or_pos m with rfl | h'
  · simp at h
  · exact h'

theorem p224p_mul_ct : ConstantTime isa (mulA p224p).pre (mulA p224p).pub (mulFn p224p.k p224p.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem p224p_mul_verified : Verified AArch64.target (mulFn p224p.k p224p.m) (p224p.mulContract AArch64.abi) :=
  Verified.of_correct (mul_a p224p_ok) p224p_mul_ct
    { pre := by sig_implies_pre [Modulus.mulContract, sig, argNum, mulA, aPre, aPub, AArch64.abi,
        AArch64.argRegs]
      post := by sig_implies_post [Modulus.mulContract, sig, argNum, mulA, aPre, aPub, AArch64.abi,
        AArch64.argRegs]
      pub := by sig_implies_pub [Modulus.mulContract, sig, argNum, mulA, aPre, aPub, AArch64.abi,
        AArch64.argRegs]
      sat := ⟨sat, mul_sat p224p (by decide) (m_pos_of_inv p224p_ok.inv)⟩ }

theorem p224n_mul_ct : ConstantTime isa (mulA p224n).pre (mulA p224n).pub (mulFn p224n.k p224n.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem p224n_mul_verified : Verified AArch64.target (mulFn p224n.k p224n.m) (p224n.mulContract AArch64.abi) :=
  Verified.of_correct (mul_a p224n_ok) p224n_mul_ct
    { pre := by sig_implies_pre [Modulus.mulContract, sig, argNum, mulA, aPre, aPub, AArch64.abi,
        AArch64.argRegs]
      post := by sig_implies_post [Modulus.mulContract, sig, argNum, mulA, aPre, aPub, AArch64.abi,
        AArch64.argRegs]
      pub := by sig_implies_pub [Modulus.mulContract, sig, argNum, mulA, aPre, aPub, AArch64.abi,
        AArch64.argRegs]
      sat := ⟨sat, mul_sat p224n (by decide) (m_pos_of_inv p224n_ok.inv)⟩ }

theorem p384p_mul_ct : ConstantTime isa (mulA p384p).pre (mulA p384p).pub (mulFn p384p.k p384p.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem p384p_mul_verified : Verified AArch64.target (mulFn p384p.k p384p.m) (p384p.mulContract AArch64.abi) :=
  Verified.of_correct (mul_a p384p_ok) p384p_mul_ct
    { pre := by sig_implies_pre [Modulus.mulContract, sig, argNum, mulA, aPre, aPub, AArch64.abi,
        AArch64.argRegs]
      post := by sig_implies_post [Modulus.mulContract, sig, argNum, mulA, aPre, aPub, AArch64.abi,
        AArch64.argRegs]
      pub := by sig_implies_pub [Modulus.mulContract, sig, argNum, mulA, aPre, aPub, AArch64.abi,
        AArch64.argRegs]
      sat := ⟨sat, mul_sat p384p (by decide) (m_pos_of_inv p384p_ok.inv)⟩ }

theorem p384n_mul_ct : ConstantTime isa (mulA p384n).pre (mulA p384n).pub (mulFn p384n.k p384n.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem p384n_mul_verified : Verified AArch64.target (mulFn p384n.k p384n.m) (p384n.mulContract AArch64.abi) :=
  Verified.of_correct (mul_a p384n_ok) p384n_mul_ct
    { pre := by sig_implies_pre [Modulus.mulContract, sig, argNum, mulA, aPre, aPub, AArch64.abi,
        AArch64.argRegs]
      post := by sig_implies_post [Modulus.mulContract, sig, argNum, mulA, aPre, aPub, AArch64.abi,
        AArch64.argRegs]
      pub := by sig_implies_pub [Modulus.mulContract, sig, argNum, mulA, aPre, aPub, AArch64.abi,
        AArch64.argRegs]
      sat := ⟨sat, mul_sat p384n (by decide) (m_pos_of_inv p384n_ok.inv)⟩ }

theorem p521p_mul_ct : ConstantTime isa (mulA p521p).pre (mulA p521p).pub (mulFn p521p.k p521p.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem p521p_mul_verified : Verified AArch64.target (mulFn p521p.k p521p.m) (p521p.mulContract AArch64.abi) :=
  Verified.of_correct (mul_a p521p_ok) p521p_mul_ct
    { pre := by sig_implies_pre [Modulus.mulContract, sig, argNum, mulA, aPre, aPub, AArch64.abi,
        AArch64.argRegs]
      post := by sig_implies_post [Modulus.mulContract, sig, argNum, mulA, aPre, aPub, AArch64.abi,
        AArch64.argRegs]
      pub := by sig_implies_pub [Modulus.mulContract, sig, argNum, mulA, aPre, aPub, AArch64.abi,
        AArch64.argRegs]
      sat := ⟨sat, mul_sat p521p (by decide) (m_pos_of_inv p521p_ok.inv)⟩ }

theorem p521n_mul_ct : ConstantTime isa (mulA p521n).pre (mulA p521n).pub (mulFn p521n.k p521n.m) :=
  ct_zext (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ hp => hp) (by taint_decide))

theorem p521n_mul_verified : Verified AArch64.target (mulFn p521n.k p521n.m) (p521n.mulContract AArch64.abi) :=
  Verified.of_correct (mul_a p521n_ok) p521n_mul_ct
    { pre := by sig_implies_pre [Modulus.mulContract, sig, argNum, mulA, aPre, aPub, AArch64.abi,
        AArch64.argRegs]
      post := by sig_implies_post [Modulus.mulContract, sig, argNum, mulA, aPre, aPub, AArch64.abi,
        AArch64.argRegs]
      pub := by sig_implies_pub [Modulus.mulContract, sig, argNum, mulA, aPre, aPub, AArch64.abi,
        AArch64.argRegs]
      sat := ⟨sat, mul_sat p521n (by decide) (m_pos_of_inv p521n_ok.inv)⟩ }

end VG.Proof.Weierstrass.AArch64.Mont
