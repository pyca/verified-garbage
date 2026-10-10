import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-! ## `MontContract` -/

section

/-!
# Montgomery products as functions on AArch64: the contracts

The facts of `mulContract` of `Spec/Weierstrass/Mont.lean` on AArch64, by
register (`mulA`: `ws` in `x0`, the offsets in `w1`–`w3`), and the functions
meet them (`mul_a`) for a modulus they support (`ModOk`): `numAt` reads what
`wordsVal` does (`numAt_eq`), and what the functions keep is what the
contract says (`keeps_of_kept`). The functions are constant time
(`ct_zext`): the zero-extension of the offsets leaves registers that two runs
agreeing on the offsets' low halves agree on, from which the rest is checked
by taint tracking.
-/

namespace VG.Proof.Weierstrass.AArch64.Mont

open VG VG.AArch64 VG.Impl.Weierstrass.AArch64.Mont VG.Proof.Mont
open VG.Spec.Weierstrass.Mont (numAt Keeps Modulus)

/-- What the functions' precondition says of the registers. -/
def aPre (M : Modulus) (s : State) : Prop :=
  s.rd = [] ∧ s.wr = [⟨s.gpr .x0, 8192⟩] ∧ (s.gpr .x0).toNat + 8192 ≤ 2 ^ 64 ∧
    M.Fit ((s.gpr .x1).setWidth 32) ((s.gpr .x2).setWidth 32) ((s.gpr .x3).setWidth 32)

/-- The number at the offset in `r`. -/
abbrev argNum (M : Modulus) (s : State) (r : Reg) : Nat :=
  numAt s.mem (s.gpr .x0) ((s.gpr r).setWidth 32) M.k

/-- What two runs agree on: the stack pointer, `ws` and the offsets. -/
def aPub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ (s₁.gpr .x1).setWidth 32 = (s₂.gpr .x1).setWidth 32 ∧
    (s₁.gpr .x2).setWidth 32 = (s₂.gpr .x2).setWidth 32 ∧
    (s₁.gpr .x3).setWidth 32 = (s₂.gpr .x3).setWidth 32

/-- `vg_<curve>_mul_mod_<p|n>(ws = x0, o = w1, a = w2, b = w3)`. -/
def mulA (M : Modulus) : Contract isa where
  pre s := aPre M s ∧ argNum M s .x3 < M.m
  post s s' :=
    numAt s'.mem (s.gpr .x0) ((s.gpr .x1).setWidth 32) M.k < M.m ∧
    numAt s'.mem (s.gpr .x0) ((s.gpr .x1).setWidth 32) M.k * M.R % M.m =
      argNum M s .x2 * argNum M s .x3 % M.m ∧
    Keeps M.k (s.gpr .x0) ((s.gpr .x1).setWidth 32) s.mem s'.mem
  pub := aPub

theorem numAt_eq (m : Mem) (ws : Addr) (o : BitVec 32) (k : Nat) :
    numAt m ws o k = wordsVal m ws o.toNat k :=
  read_eq_wordsVal m ws k o.toNat

theorem pre_of {M : Modulus} (hk : M.k ≤ 9) {s : State} (h : aPre M s) : Pre M.k 8192 s := by
  obtain ⟨h1, h2, h3, ho, ha, hb⟩ := h
  exact ⟨h1, h2, h3, by simp only [moAt]; omega, Nat.le_refl _, ho, ha, hb⟩

theorem keeps_of_kept {k : Nat} (hk : k ≤ 9) {ws : Addr} {o : BitVec 32} {m m' : Mem}
    (h : Kept k ws o.toNat m m') : Keeps k ws o m m' := by
  intro i hi hown ho
  simp only [Spec.Weierstrass.Mont.wsBytes] at hi
  have hown' := own_eq hk
  refine h _ ?_ ?_
  · rw [ofs_off0 ws (by omega)]; exact ho
  · rw [ofs_off0 ws (by omega)]
    simp only [own, moAt, Spec.Weierstrass.Mont.ownAt, Spec.Weierstrass.Mont.ownBytes] at hown hown' ⊢
    omega

theorem mul_a {M : Modulus} (hM : ModOk M.k M.m) (s : State) (hs : (mulA M).pre s) :
    ∃ t s', Exec isa (mulFn M.k M.m) s t s' ∧ abiPreserved s s' ∧ (mulA M).post s s' := by
  obtain ⟨t, s', he, A, K, ⟨V, C⟩, -, -, -, -⟩ := mulFn_ok hM (pre_of hM.n9 hs.1) (by rw [← numAt_eq]; exact hs.2)
  refine ⟨t, s', he, A, ?_, ?_, keeps_of_kept hM.n9 K⟩
  · rw [numAt_eq]; exact V
  · simp only [argNum, numAt_eq]; exact C

/-! ## Constant time -/

/-- The state after the zero-extension. -/
def zextState (s : State) : State :=
  ((s.write .w .x1 (s.read .w .x1 + 0)).write .w .x2 ((s.write .w .x1 (s.read .w .x1 + 0)).read .w .x2 + 0)).write
    .w .x3 (((s.write .w .x1 (s.read .w .x1 + 0)).write .w .x2
      ((s.write .w .x1 (s.read .w .x1 + 0)).read .w .x2 + 0)).read .w .x3 + 0)

theorem exec_zext {s s' : State} {t : List Leak} (h : Exec isa (.block zextCode) s t s') :
    t = [] ∧ s' = zextState s := by
  cases h with
  | block b =>
    simp only [zextCode, execBlock, exec, show (0 : Nat) < 4096 by decide, ite_true, addrs,
      Option.map_some, List.map_nil, List.nil_append, Option.some.injEq, Prod.mk.injEq] at b
    exact ⟨b.2.symm, b.1.symm⟩

/-- The zero-extension, then code that is constant time for states agreeing
on `x0`–`x3`: constant time for states agreeing on `x0` and the offsets' low
halves. -/
theorem ct_zext {Pre : State → Prop} {c : Prog isa}
    (h : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2, .x3])) c) :
    ConstantTime isa Pre aPub (.seq (.block zextCode) c) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ _ hp e₁ e₂
  obtain ⟨hsp, h0, h1, h2, h3⟩ := hp
  cases e₁ with
  | seq z₁ c₁ =>
    cases e₂ with
    | seq z₂ c₂ =>
      obtain ⟨rfl, rfl⟩ := exec_zext z₁
      obtain ⟨rfl, rfl⟩ := exec_zext z₂
      have ag : AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2, .x3]) (zextState s₁) (zextState s₂) := by
        refine ⟨hsp, fun r hr => ?_⟩
        simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;>
          simp only [zextState, State.write, State.read, reduceCtorEq, ite_false, ite_true, h0, h1, h2, h3]
      rw [h _ _ _ _ _ _ trivial trivial ag c₁ c₂]

end VG.Proof.Weierstrass.AArch64.Mont

end

/-! ## `MontModuli` -/

section

/-!
# Montgomery products as functions on AArch64: the moduli

The prime `p` of P-384 and of P-521 is one the functions support (`ModOk`).
-/

namespace VG.Proof.Weierstrass.AArch64.Mont

open Spec.Weierstrass.Mont

theorem p384p_ok : ModOk p384p.k p384p.m where
  hn := by decide
  m_lt := by decide +kernel
  inv := by decide +kernel
  red := by decide +kernel
  kind := .inl ⟨by decide +kernel, by decide +kernel⟩
  x6 := by decide +kernel
  loads := by decide +kernel
  lnd := by decide +kernel
  novec := by decide +kernel

theorem p521p_ok : ModOk p521p.k p521p.m where
  hn := by decide
  m_lt := by decide +kernel
  inv := by decide +kernel
  red := by decide +kernel
  kind := .inr ⟨by decide +kernel, friendly_of (by decide +kernel)⟩
  x6 := by decide +kernel
  loads := by decide +kernel
  lnd := by decide +kernel
  novec := by decide +kernel

end VG.Proof.Weierstrass.AArch64.Mont

end
