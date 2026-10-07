import VerifiedGarbage.Proof.Weierstrass.Arm.MontFn
import VerifiedGarbage.Proof.Mont.Read

/-!
# Montgomery arithmetic as functions on 32-bit ARM: the contracts

The facts of the contracts of `Spec/Weierstrass/Mont.lean` on 32-bit ARM, by
name (`armPre`, `mulArm`, `addArm`, `subArm`: `ws`, `o`, `a` and `b` in
`r0`–`r3`), and the functions meet them (`mul_arm`, `add_arm`, `sub_arm`)
for a modulus the functions support (`ModOk`): `numAt` reads what
`wordsVal` does (`numAt_eq`), and what the functions keep is what the
contracts say (`keeps_of_kept`).
-/

namespace VG.Proof.Weierstrass.Arm.Mont

open VG VG.Arm VG.Impl.Weierstrass.Arm.Mont VG.Proof.Mont
open VG.Spec.Weierstrass.Mont (numAt Keeps Modulus)

/-- What the three functions' preconditions share, by register. -/
def armPre (M : Modulus) (s : State) : Prop :=
  s.rd = [] ∧ s.wr = [⟨State.addr (s.gpr .r0), 8192⟩] ∧ (s.gpr .r0).toNat + 8192 ≤ 2 ^ 32 ∧
    M.Fit (s.gpr .r1) (s.gpr .r2) (s.gpr .r3)

/-- The number at the offset in `r`. -/
abbrev arg (M : Modulus) (s : State) (r : Reg) : Nat := numAt s.mem (State.addr (s.gpr .r0)) (s.gpr r) M.k

/-- What two runs agree on: the stack pointer and the arguments. -/
def armPub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3

/-- `vg_<curve>_mul_mod_<p|n>(ws = r0, o = r1, a = r2, b = r3)`. -/
def mulArm (M : Modulus) : Contract Arm.isa where
  pre s := armPre M s ∧ arg M s .r3 < M.m
  post s s' :=
    numAt s'.mem (State.addr (s.gpr .r0)) (s.gpr .r1) M.k < M.m ∧
    numAt s'.mem (State.addr (s.gpr .r0)) (s.gpr .r1) M.k * M.R % M.m =
      numAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r2) M.k *
        numAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r3) M.k % M.m ∧
    Keeps M.k (State.addr (s.gpr .r0)) (s.gpr .r1) s.mem s'.mem
  pub := armPub

/-- `vg_<curve>_add_mod_<p|n>(ws = r0, o = r1, a = r2, b = r3)`. -/
def addArm (M : Modulus) : Contract Arm.isa where
  pre s := armPre M s ∧ arg M s .r2 + arg M s .r3 < 2 * M.m
  post s s' :=
    numAt s'.mem (State.addr (s.gpr .r0)) (s.gpr .r1) M.k =
      (numAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r2) M.k +
        numAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r3) M.k) % M.m ∧
    Keeps M.k (State.addr (s.gpr .r0)) (s.gpr .r1) s.mem s'.mem
  pub := armPub

/-- `vg_<curve>_sub_mod_<p|n>(ws = r0, o = r1, a = r2, b = r3)`. -/
def subArm (M : Modulus) : Contract Arm.isa where
  pre s := armPre M s ∧ arg M s .r2 < M.m ∧ arg M s .r3 < M.m
  post s s' :=
    numAt s'.mem (State.addr (s.gpr .r0)) (s.gpr .r1) M.k =
      (numAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r2) M.k + M.m -
        numAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r3) M.k) % M.m ∧
    Keeps M.k (State.addr (s.gpr .r0)) (s.gpr .r1) s.mem s'.mem
  pub := armPub

theorem numAt_eq (m : Mem) (ws : Addr) (o : BitVec 32) (k : Nat) :
    numAt m ws o k = wordsVal m ws o.toNat k :=
  read_eq_wordsVal m ws k o.toNat

theorem pre_of {M : Modulus} {s : State} (h : armPre M s) : Pre M.k M.m s := by
  obtain ⟨h1, h2, h3, ho, ha, hb⟩ := h
  exact ⟨h1, h2, h3, ho, ha, hb⟩

theorem keeps_of_kept {k : Nat} (hk : k ≤ 9) {ws : Addr} {o : BitVec 32} {m m' : Mem}
    (h : Kept k ws o.toNat m m') : Keeps k ws o m m' := by
  intro i hi hown ho
  simp only [Spec.Weierstrass.Mont.wsBytes] at hi
  have hown' := own_le k hk
  refine h _ fun r hr => ?_
  rw [ofs_off0 ws (by omega)]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · omega
  · simp only [own] at hown' ⊢; omega

theorem mul_arm {M : Modulus} (hM : ModOk M.k M.m) (s : State) (hs : (mulArm M).pre s) :
    ∃ t s', Exec isa (mulFn M.k M.m) s t s' ∧ abiPreserved s s' ∧ (mulArm M).post s s' := by
  obtain ⟨t, s', he, A, K, ⟨V, C⟩, -⟩ := mulFn_ok hM (pre_of hs.1) (by rw [← numAt_eq]; exact hs.2)
  refine ⟨t, s', he, A, ?_, ?_, keeps_of_kept hM.n9 K⟩
  · rw [numAt_eq]; exact V
  · rw [numAt_eq, numAt_eq, numAt_eq]; exact C

theorem add_arm {M : Modulus} (hM : ModOk M.k M.m) (s : State) (hs : (addArm M).pre s) :
    ∃ t s', Exec isa (addFn M.k M.m) s t s' ∧ abiPreserved s s' ∧ (addArm M).post s s' := by
  obtain ⟨t, s', he, A, K, V, -⟩ := addFn_ok hM (pre_of hs.1) (by rw [← numAt_eq, ← numAt_eq]; exact hs.2)
  exact ⟨t, s', he, A, by rw [numAt_eq, numAt_eq, numAt_eq]; exact V, keeps_of_kept hM.n9 K⟩

theorem sub_arm {M : Modulus} (hM : ModOk M.k M.m) (s : State) (hs : (subArm M).pre s) :
    ∃ t s', Exec isa (subFn M.k M.m) s t s' ∧ abiPreserved s s' ∧ (subArm M).post s s' := by
  obtain ⟨t, s', he, A, K, V, -⟩ := subFn_ok hM (pre_of hs.1) (by rw [← numAt_eq]; exact hs.2.1)
    (by rw [← numAt_eq]; exact hs.2.2)
  exact ⟨t, s', he, A, by rw [numAt_eq, numAt_eq, numAt_eq]; exact V, keeps_of_kept hM.n9 K⟩

end VG.Proof.Weierstrass.Arm.Mont
