import VerifiedGarbage.Proof.Weierstrass.X86.MontModuli
import VerifiedGarbage.Proof.Mont.Read

/-!
# Montgomery arithmetic as functions on x86 (32-bit): the contracts

The facts of the contracts of `Spec/Weierstrass/Mont.lean` on x86, by name
(`x86Pre`, `mulX86`, `addX86`, `subX86`: `ws`, `o`, `a` and `b` on the stack),
and the functions meet them (`mul_x86`, `add_x86`, `sub_x86`) for a modulus
the functions support (`FnOk`): `numAt` reads what `val32` does
(`numAt_eq`), and what the functions keep is what the contracts say
(`keeps_of_outs`).
-/

namespace VG.Proof.Weierstrass.X86.Mont

open VG VG.X86 VG.Impl.Weierstrass.X86.Mont VG.Proof.Mont VG.Proof.Mont.X86
open VG.Spec.Weierstrass.Mont (numAt Keeps Modulus)

/-- What the three functions' preconditions share, by argument. -/
def x86Pre (M : Modulus) (s : State) : Prop :=
  let ws : Region := ⟨(arg s 0).setWidth 64, 8192⟩
  let args : Region := ⟨argAddr s 0, 16⟩
  let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
  s.rd = [args] ∧ s.wr = [ws] ∧ args.Disjoint ws ∧ ret.Disjoint ws ∧ ret.Disjoint args ∧
    (arg s 0).toNat + 8192 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧
    M.Fit (arg s 1) (arg s 2) (arg s 3)

/-- The number at the offset in argument `i`. -/
abbrev num (M : Modulus) (m : Mem) (s : State) (i : Nat) : Nat := numAt m ((arg s 0).setWidth 64) (arg s i) M.k

/-- What two runs agree on: the stack pointer and the arguments. -/
def x86Pub (s₁ s₂ : State) : Prop :=
  s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧ arg s₁ 2 = arg s₂ 2 ∧
    arg s₁ 3 = arg s₂ 3

/-- `vg_<curve>_mul_mod_<p|n>(ws, o, a, b)`. -/
def mulX86 (M : Modulus) : Contract X86.isa where
  pre s := x86Pre M s ∧ num M s.mem s 3 < M.m
  post s s' :=
    num M s'.mem s 1 < M.m ∧ num M s'.mem s 1 * M.R % M.m = num M s.mem s 2 * num M s.mem s 3 % M.m ∧
    Keeps M.k ((arg s 0).setWidth 64) (arg s 1) s.mem s'.mem
  pub := x86Pub

/-- `vg_<curve>_add_mod_<p|n>(ws, o, a, b)`. -/
def addX86 (M : Modulus) : Contract X86.isa where
  pre s := x86Pre M s ∧ num M s.mem s 2 + num M s.mem s 3 < 2 * M.m
  post s s' :=
    num M s'.mem s 1 = (num M s.mem s 2 + num M s.mem s 3) % M.m ∧
    Keeps M.k ((arg s 0).setWidth 64) (arg s 1) s.mem s'.mem
  pub := x86Pub

/-- `vg_<curve>_sub_mod_<p|n>(ws, o, a, b)`. -/
def subX86 (M : Modulus) : Contract X86.isa where
  pre s := x86Pre M s ∧ num M s.mem s 2 < M.m ∧ num M s.mem s 3 < M.m
  post s s' :=
    num M s'.mem s 1 = (num M s.mem s 2 + M.m - num M s.mem s 3) % M.m ∧
    Keeps M.k ((arg s 0).setWidth 64) (arg s 1) s.mem s'.mem
  pub := x86Pub

theorem numAt_eq (m : Mem) (ws : Addr) (o : BitVec 32) (k : Nat) :
    numAt m ws o k = val32 m ws o.toNat (2 * k) :=
  (read_eq_wordsVal m ws k o.toNat).trans (wordsVal_eq_val32 m ws o.toNat k)

theorem pre_of {M : Modulus} (hF : FnOk M) {s : State} (h : x86Pre M s) : Pre M.k s := by
  obtain ⟨h1, h2, h3, h4, -, h6, h7, ho, ha, hb⟩ := h
  exact ⟨h1, h2, h6, h7, h3, h4, hF.mul.k0, hF.k9, ho, ha, hb⟩

theorem keeps_of_outs {k : Nat} (hk : k ≤ 9) {s : State} {m m' : Mem}
    (h : Outs (wsOf s) (outs k s) m m') : Keeps k ((arg s 0).setWidth 64) (arg s 1) m m' := by
  intro i hi hown ho
  simp only [Spec.Weierstrass.Mont.wsBytes] at hi
  have hown' : own k + 64 * k = 4096 := by
    simp only [own, Spec.Weierstrass.Mont.ownAt, Spec.Weierstrass.Mont.ownBytes]; omega
  refine h _ fun r hr => ?_
  rw [ofs_off0 _ (by omega)]
  simp only [outs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ho
  · simp only [own] at hown' ⊢; omega

theorem mul_x86 {M : Modulus} (hF : FnOk M) (s : State) (hs : (mulX86 M).pre s) :
    ∃ t s', Exec isa (mulFn M.k M.m) s t s' ∧ abiPreserved s s' ∧ (mulX86 M).post s s' := by
  obtain ⟨t, s', he, A, K, V, C⟩ := mulFn_ok hF.mul (pre_of hF hs.1) (by rw [← numAt_eq]; exact hs.2)
  refine ⟨t, s', he, A, ?_, ?_, keeps_of_outs hF.k9 K⟩
  · rw [num, numAt_eq]; exact V
  · rw [num, num, num, numAt_eq, numAt_eq, numAt_eq]; exact C

theorem add_x86 {M : Modulus} (hF : FnOk M) (s : State) (hs : (addX86 M).pre s) :
    ∃ t s', Exec isa (addFn M.k M.m) s t s' ∧ abiPreserved s s' ∧ (addX86 M).post s s' := by
  obtain ⟨t, s', he, A, K, V⟩ := addFn_ok hF.mul (pre_of hF hs.1) (by rw [← numAt_eq, ← numAt_eq]; exact hs.2)
  exact ⟨t, s', he, A, by rw [num, num, num, numAt_eq, numAt_eq, numAt_eq]; exact V, keeps_of_outs hF.k9 K⟩

theorem sub_x86 {M : Modulus} (hF : FnOk M) (s : State) (hs : (subX86 M).pre s) :
    ∃ t s', Exec isa (subFn M.k M.m) s t s' ∧ abiPreserved s s' ∧ (subX86 M).post s s' := by
  obtain ⟨t, s', he, A, K, V⟩ := subFn_ok hF.mul (pre_of hF hs.1) (by rw [← numAt_eq]; exact hs.2.1)
    (by rw [← numAt_eq]; exact hs.2.2)
  exact ⟨t, s', he, A, by rw [num, num, num, numAt_eq, numAt_eq, numAt_eq]; exact V, keeps_of_outs hF.k9 K⟩

end VG.Proof.Weierstrass.X86.Mont
