import VerifiedGarbage.Proof.Weierstrass.X86.MontContract
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P224
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P256
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P384
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P521
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Montgomery arithmetic modulo the curves' `p` and `n`, as functions, on x86 (32-bit): verified

Each modulus of `Spec.Weierstrass.Mont.moduli` is one the functions support
(`FnOk`), so each of its functions meets the contract of its `Api`: the
proof against `mulX86`, `addX86` or `subX86`, which it implies, constant
time by taint tracking (only the stack pointer and the arguments, the
pointer and the offsets, are public; the word of the first argument is the
working space's base), and a state satisfying it (`sat`).
-/

namespace VG.Proof.Weierstrass.X86.Mont

open VG VG.X86 VG.Impl.Weierstrass.X86.Mont Spec.Weierstrass.Mont

/-- The taint analysis starts with the stack arguments public, and the word
holding `ws` known to be the base address of the writable region. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [8192], argLen := 20, argBases := [(4, 0)] }

theorem wf₀ {M : Modulus} {s : State} (hp : x86Pre M s) : VG.X86.Taint.Wf τ₀ s := by
  obtain ⟨hrd, hwr, haw, hrw, hra, hfit, hsp, -⟩ := hp
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hwr, τ₀], by simp [hwr], ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [τ₀]; omega, ?_⟩, ?_⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl; simp only [BitVec.toNat_setWidth]; omega
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl
    exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hrw haw
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    subst hp'
    refine ⟨by decide, ?_⟩
    simp [VG.X86.Taint.region, hwr, addr, arg, argAddr]

theorem agree₀ {M : Modulus} {s₁ s₂ : State} (h₁ : x86Pre M s₁) (h₂ : x86Pre M s₂)
    (hpub : x86Pub s₁ s₂) : VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, a0, a1, a2, a3⟩ := hpub
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ h₁, wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [h₁.2.1, h₂.2.1, a0]
  · simp only [τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (by have := h₁.2.2.2.2.2.2.1; omega) h4 hk,
      VG.X86.Taint.argByte_eq (by have := h₂.2.2.2.2.2.2.1; omega) h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    have : (k - 4) / 4 = 0 ∨ (k - 4) / 4 = 1 ∨ (k - 4) / 4 = 2 ∨ (k - 4) / 4 = 3 := by omega
    rcases this with h | h | h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1
    · exact congrArg _ a2
    · exact congrArg _ a3

theorem read_zero : ∀ (n : Nat) (a : Addr), (Mem.read (fun _ => 0) a n).toNat = 0
  | 0, _ => rfl
  | n + 1, a => by rw [VG.Proof.Mont.read_toNat_succ, read_zero n]; rfl

theorem numAt_zero (ws : Addr) (o : BitVec 32) (k : Nat) : numAt (fun _ => 0) ws o k = 0 :=
  read_zero _ _

/-- A state satisfying the preconditions: `ws` at address 0, the numbers at
offset 0, all zero, the arguments at `0x20004`. -/
def satState : State where
  gpr r := match r with
    | .esp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x20004, 16⟩]
  wr := [⟨0, 8192⟩]

theorem fit_zero (M : Modulus) (hk : M.k ≤ 9) : M.Fit 0 0 0 := by
  have h0 : (0 : BitVec 32).toNat = 0 := rfl
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Fits, ownAt, ownBytes, h0] <;> omega

theorem arg_sat (i : Nat) : arg satState i = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [arg, Mem.readW, BitVec.toNat_setWidth]
  show (Mem.read (fun _ => 0) _ _).toNat % _ = 0
  rw [read_zero]

theorem mul_sat (M : Modulus) (hk : M.k ≤ 9) (hm : 0 < M.m) : (M.mulContract X86.abi).pre satState :=
  Sig.contract_pre_of_check (by decide +kernel) (by
    sig_reduce [Sig.wfPre, sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_sat]
    exact ⟨by decide, fit_zero M hk, by rw [numAt_zero]; exact hm⟩)

theorem add_sat (M : Modulus) (hk : M.k ≤ 9) (hm : 0 < M.m) : (M.addContract X86.abi).pre satState :=
  Sig.contract_pre_of_check (by decide +kernel) (by
    sig_reduce [Sig.wfPre, sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_sat]
    exact ⟨by decide, fit_zero M hk, by rw [numAt_zero]; omega⟩)

theorem sub_sat (M : Modulus) (hk : M.k ≤ 9) (hm : 0 < M.m) : (M.subContract X86.abi).pre satState :=
  Sig.contract_pre_of_check (by decide +kernel) (by
    sig_reduce [Sig.wfPre, sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_sat]
    exact ⟨by decide, fit_zero M hk, by rw [numAt_zero]; exact hm, by rw [numAt_zero]; exact hm⟩)

theorem mul_implies (M : Modulus) (hk : M.k ≤ 9) (hm : 0 < M.m) : (mulX86 M).Implies (M.mulContract X86.abi) where
  pre := by sig_implies_pre [Modulus.mulContract, sig, mulX86, x86Pre, num, x86Pub, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
  post := by sig_implies_post [Modulus.mulContract, sig, mulX86, x86Pre, num, x86Pub, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
  pub := by sig_implies_pub [Modulus.mulContract, sig, mulX86, x86Pre, num, x86Pub, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
  sat := ⟨satState, mul_sat M hk hm⟩

theorem add_implies (M : Modulus) (hk : M.k ≤ 9) (hm : 0 < M.m) : (addX86 M).Implies (M.addContract X86.abi) where
  pre := by sig_implies_pre [Modulus.addContract, sig, addX86, x86Pre, num, x86Pub, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
  post := by sig_implies_post [Modulus.addContract, sig, addX86, x86Pre, num, x86Pub, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
  pub := by sig_implies_pub [Modulus.addContract, sig, addX86, x86Pre, num, x86Pub, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
  sat := ⟨satState, add_sat M hk hm⟩

theorem sub_implies (M : Modulus) (hk : M.k ≤ 9) (hm : 0 < M.m) : (subX86 M).Implies (M.subContract X86.abi) where
  pre := by sig_implies_pre [Modulus.subContract, sig, subX86, x86Pre, num, x86Pub, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
  post := by sig_implies_post [Modulus.subContract, sig, subX86, x86Pre, num, x86Pub, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
  pub := by sig_implies_pub [Modulus.subContract, sig, subX86, x86Pre, num, x86Pub, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
  sat := ⟨satState, sub_sat M hk hm⟩

theorem p224p_mul_ct : ConstantTime isa (mulX86 p224p).pre (mulX86 p224p).pub (mulFn p224p.k p224p.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by taint_decide)

theorem p224p_mul_verified : Verified X86.target (mulFn p224p.k p224p.m) (p224p.mulContract X86.abi) :=
  Verified.of_correct (mul_x86 p224p_ok) p224p_mul_ct (mul_implies p224p p224p_ok.k9 p224p_ok.mul.m_pos)

theorem p224p_add_ct : ConstantTime isa (addX86 p224p).pre (addX86 p224p).pub (addFn p224p.k p224p.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by taint_decide)

theorem p224p_add_verified : Verified X86.target (addFn p224p.k p224p.m) (p224p.addContract X86.abi) :=
  Verified.of_correct (add_x86 p224p_ok) p224p_add_ct (add_implies p224p p224p_ok.k9 p224p_ok.mul.m_pos)

theorem p224p_sub_ct : ConstantTime isa (subX86 p224p).pre (subX86 p224p).pub (subFn p224p.k p224p.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by taint_decide)

theorem p224p_sub_verified : Verified X86.target (subFn p224p.k p224p.m) (p224p.subContract X86.abi) :=
  Verified.of_correct (sub_x86 p224p_ok) p224p_sub_ct (sub_implies p224p p224p_ok.k9 p224p_ok.mul.m_pos)

theorem p224n_mul_ct : ConstantTime isa (mulX86 p224n).pre (mulX86 p224n).pub (mulFn p224n.k p224n.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by taint_decide)

theorem p224n_mul_verified : Verified X86.target (mulFn p224n.k p224n.m) (p224n.mulContract X86.abi) :=
  Verified.of_correct (mul_x86 p224n_ok) p224n_mul_ct (mul_implies p224n p224n_ok.k9 p224n_ok.mul.m_pos)

theorem p224n_add_ct : ConstantTime isa (addX86 p224n).pre (addX86 p224n).pub (addFn p224n.k p224n.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by taint_decide)

theorem p224n_add_verified : Verified X86.target (addFn p224n.k p224n.m) (p224n.addContract X86.abi) :=
  Verified.of_correct (add_x86 p224n_ok) p224n_add_ct (add_implies p224n p224n_ok.k9 p224n_ok.mul.m_pos)

theorem p224n_sub_ct : ConstantTime isa (subX86 p224n).pre (subX86 p224n).pub (subFn p224n.k p224n.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by taint_decide)

theorem p224n_sub_verified : Verified X86.target (subFn p224n.k p224n.m) (p224n.subContract X86.abi) :=
  Verified.of_correct (sub_x86 p224n_ok) p224n_sub_ct (sub_implies p224n p224n_ok.k9 p224n_ok.mul.m_pos)

theorem p256p_mul_ct : ConstantTime isa (mulX86 p256p).pre (mulX86 p256p).pub (mulFn p256p.k p256p.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by taint_decide)

theorem p256p_mul_verified : Verified X86.target (mulFn p256p.k p256p.m) (p256p.mulContract X86.abi) :=
  Verified.of_correct (mul_x86 p256p_ok) p256p_mul_ct (mul_implies p256p p256p_ok.k9 p256p_ok.mul.m_pos)

theorem p256p_add_ct : ConstantTime isa (addX86 p256p).pre (addX86 p256p).pub (addFn p256p.k p256p.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by taint_decide)

theorem p256p_add_verified : Verified X86.target (addFn p256p.k p256p.m) (p256p.addContract X86.abi) :=
  Verified.of_correct (add_x86 p256p_ok) p256p_add_ct (add_implies p256p p256p_ok.k9 p256p_ok.mul.m_pos)

theorem p256p_sub_ct : ConstantTime isa (subX86 p256p).pre (subX86 p256p).pub (subFn p256p.k p256p.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by taint_decide)

theorem p256p_sub_verified : Verified X86.target (subFn p256p.k p256p.m) (p256p.subContract X86.abi) :=
  Verified.of_correct (sub_x86 p256p_ok) p256p_sub_ct (sub_implies p256p p256p_ok.k9 p256p_ok.mul.m_pos)

theorem p256n_mul_ct : ConstantTime isa (mulX86 p256n).pre (mulX86 p256n).pub (mulFn p256n.k p256n.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by taint_decide)

theorem p256n_mul_verified : Verified X86.target (mulFn p256n.k p256n.m) (p256n.mulContract X86.abi) :=
  Verified.of_correct (mul_x86 p256n_ok) p256n_mul_ct (mul_implies p256n p256n_ok.k9 p256n_ok.mul.m_pos)

theorem p256n_add_ct : ConstantTime isa (addX86 p256n).pre (addX86 p256n).pub (addFn p256n.k p256n.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by taint_decide)

theorem p256n_add_verified : Verified X86.target (addFn p256n.k p256n.m) (p256n.addContract X86.abi) :=
  Verified.of_correct (add_x86 p256n_ok) p256n_add_ct (add_implies p256n p256n_ok.k9 p256n_ok.mul.m_pos)

theorem p256n_sub_ct : ConstantTime isa (subX86 p256n).pre (subX86 p256n).pub (subFn p256n.k p256n.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by taint_decide)

theorem p256n_sub_verified : Verified X86.target (subFn p256n.k p256n.m) (p256n.subContract X86.abi) :=
  Verified.of_correct (sub_x86 p256n_ok) p256n_sub_ct (sub_implies p256n p256n_ok.k9 p256n_ok.mul.m_pos)

theorem p384p_mul_ct : ConstantTime isa (mulX86 p384p).pre (mulX86 p384p).pub (mulFn p384p.k p384p.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by taint_decide)

theorem p384p_mul_verified : Verified X86.target (mulFn p384p.k p384p.m) (p384p.mulContract X86.abi) :=
  Verified.of_correct (mul_x86 p384p_ok) p384p_mul_ct (mul_implies p384p p384p_ok.k9 p384p_ok.mul.m_pos)

theorem p384p_add_ct : ConstantTime isa (addX86 p384p).pre (addX86 p384p).pub (addFn p384p.k p384p.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by taint_decide)

theorem p384p_add_verified : Verified X86.target (addFn p384p.k p384p.m) (p384p.addContract X86.abi) :=
  Verified.of_correct (add_x86 p384p_ok) p384p_add_ct (add_implies p384p p384p_ok.k9 p384p_ok.mul.m_pos)

theorem p384p_sub_ct : ConstantTime isa (subX86 p384p).pre (subX86 p384p).pub (subFn p384p.k p384p.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by taint_decide)

theorem p384p_sub_verified : Verified X86.target (subFn p384p.k p384p.m) (p384p.subContract X86.abi) :=
  Verified.of_correct (sub_x86 p384p_ok) p384p_sub_ct (sub_implies p384p p384p_ok.k9 p384p_ok.mul.m_pos)

theorem p384n_mul_ct : ConstantTime isa (mulX86 p384n).pre (mulX86 p384n).pub (mulFn p384n.k p384n.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by taint_decide)

theorem p384n_mul_verified : Verified X86.target (mulFn p384n.k p384n.m) (p384n.mulContract X86.abi) :=
  Verified.of_correct (mul_x86 p384n_ok) p384n_mul_ct (mul_implies p384n p384n_ok.k9 p384n_ok.mul.m_pos)

theorem p384n_add_ct : ConstantTime isa (addX86 p384n).pre (addX86 p384n).pub (addFn p384n.k p384n.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by taint_decide)

theorem p384n_add_verified : Verified X86.target (addFn p384n.k p384n.m) (p384n.addContract X86.abi) :=
  Verified.of_correct (add_x86 p384n_ok) p384n_add_ct (add_implies p384n p384n_ok.k9 p384n_ok.mul.m_pos)

theorem p384n_sub_ct : ConstantTime isa (subX86 p384n).pre (subX86 p384n).pub (subFn p384n.k p384n.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by taint_decide)

theorem p384n_sub_verified : Verified X86.target (subFn p384n.k p384n.m) (p384n.subContract X86.abi) :=
  Verified.of_correct (sub_x86 p384n_ok) p384n_sub_ct (sub_implies p384n p384n_ok.k9 p384n_ok.mul.m_pos)

theorem p521p_mul_ct : ConstantTime isa (mulX86 p521p).pre (mulX86 p521p).pub (mulFn p521p.k p521p.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by taint_decide)

theorem p521p_mul_verified : Verified X86.target (mulFn p521p.k p521p.m) (p521p.mulContract X86.abi) :=
  Verified.of_correct (mul_x86 p521p_ok) p521p_mul_ct (mul_implies p521p p521p_ok.k9 p521p_ok.mul.m_pos)

theorem p521p_add_ct : ConstantTime isa (addX86 p521p).pre (addX86 p521p).pub (addFn p521p.k p521p.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by taint_decide)

theorem p521p_add_verified : Verified X86.target (addFn p521p.k p521p.m) (p521p.addContract X86.abi) :=
  Verified.of_correct (add_x86 p521p_ok) p521p_add_ct (add_implies p521p p521p_ok.k9 p521p_ok.mul.m_pos)

theorem p521p_sub_ct : ConstantTime isa (subX86 p521p).pre (subX86 p521p).pub (subFn p521p.k p521p.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by taint_decide)

theorem p521p_sub_verified : Verified X86.target (subFn p521p.k p521p.m) (p521p.subContract X86.abi) :=
  Verified.of_correct (sub_x86 p521p_ok) p521p_sub_ct (sub_implies p521p p521p_ok.k9 p521p_ok.mul.m_pos)

theorem p521n_mul_ct : ConstantTime isa (mulX86 p521n).pre (mulX86 p521n).pub (mulFn p521n.k p521n.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by taint_decide)

theorem p521n_mul_verified : Verified X86.target (mulFn p521n.k p521n.m) (p521n.mulContract X86.abi) :=
  Verified.of_correct (mul_x86 p521n_ok) p521n_mul_ct (mul_implies p521n p521n_ok.k9 p521n_ok.mul.m_pos)

theorem p521n_add_ct : ConstantTime isa (addX86 p521n).pre (addX86 p521n).pub (addFn p521n.k p521n.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by taint_decide)

theorem p521n_add_verified : Verified X86.target (addFn p521n.k p521n.m) (p521n.addContract X86.abi) :=
  Verified.of_correct (add_x86 p521n_ok) p521n_add_ct (add_implies p521n p521n_ok.k9 p521n_ok.mul.m_pos)

theorem p521n_sub_ct : ConstantTime isa (subX86 p521n).pre (subX86 p521n).pub (subFn p521n.k p521n.m) :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁.1 h₂.1 hp) (by taint_decide)

theorem p521n_sub_verified : Verified X86.target (subFn p521n.k p521n.m) (p521n.subContract X86.abi) :=
  Verified.of_correct (sub_x86 p521n_ok) p521n_sub_ct (sub_implies p521n p521n_ok.k9 p521n_ok.mul.m_pos)

end VG.Proof.Weierstrass.X86.Mont
