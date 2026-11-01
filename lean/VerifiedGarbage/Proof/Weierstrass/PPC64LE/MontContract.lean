module

public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontFn
public import VerifiedGarbage.Proof.Weierstrass.MontContract
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Mont.Words

/-!
# Montgomery arithmetic modulo a curve's `p` or `n`, as functions, on PPC64LE: the contracts

The contracts the proofs are written against (`mulPPC`, `addPPC`, `subPPC`),
on the registers, which the shared contracts of `Proof/Weierstrass/MontContract.lean`
imply, and the functions meet them for any modulus they support
(`mul_ppc`, `add_ppc`, `sub_ppc`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE.Mont

open VG VG.PPC64LE VG.Impl.Weierstrass.PPC64LE.Mont VG.Proof.Mont
open VG.Impl.Weierstrass.Mont (numAt Keeps Modulus)

/-- The offset argument in `r`. -/
abbrev ofs32 (s : State) (r : Reg) : BitVec 32 := (s.gpr r).setWidth 32

/-- What the three functions' preconditions share, by register. -/
def ppcPre (M : Modulus) (s : State) : Prop :=
  s.rd = [] ∧ s.wr = [⟨s.gpr .r3, 8192⟩] ∧ (s.gpr .r3).toNat + 8192 ≤ 2 ^ 64 ∧
    M.Fit (ofs32 s .r4) (ofs32 s .r5) (ofs32 s .r6)

/-- The number at the offset in `r`. -/
abbrev arg (M : Modulus) (s : State) (r : Reg) : Nat := numAt s.mem (s.gpr .r3) (ofs32 s r) M.k

/-- What two runs agree on: the stack pointer and the arguments. -/
def ppcPub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ ofs32 s₁ .r4 = ofs32 s₂ .r4 ∧ ofs32 s₁ .r5 = ofs32 s₂ .r5 ∧
    ofs32 s₁ .r6 = ofs32 s₂ .r6

/-- `vg_<curve>_mul_mod_<p|n>(ws = r3, o = r4, a = r5, b = r6)`. -/
def mulPPC (M : Modulus) : Contract isa where
  pre s := ppcPre M s ∧ arg M s .r6 < M.m
  post s s' :=
    numAt s'.mem (s.gpr .r3) (ofs32 s .r4) M.k < M.m ∧
    numAt s'.mem (s.gpr .r3) (ofs32 s .r4) M.k * M.R % M.m = arg M s .r5 * arg M s .r6 % M.m ∧
    Keeps M.k (s.gpr .r3) (ofs32 s .r4) s.mem s'.mem
  pub := ppcPub

/-- `vg_<curve>_add_mod_<p|n>(ws = r3, o = r4, a = r5, b = r6)`. -/
def addPPC (M : Modulus) : Contract isa where
  pre s := ppcPre M s ∧ arg M s .r5 + arg M s .r6 < 2 * M.m
  post s s' :=
    numAt s'.mem (s.gpr .r3) (ofs32 s .r4) M.k = (arg M s .r5 + arg M s .r6) % M.m ∧
    Keeps M.k (s.gpr .r3) (ofs32 s .r4) s.mem s'.mem
  pub := ppcPub

/-- `vg_<curve>_sub_mod_<p|n>(ws = r3, o = r4, a = r5, b = r6)`. -/
def subPPC (M : Modulus) : Contract isa where
  pre s := ppcPre M s ∧ arg M s .r5 < M.m ∧ arg M s .r6 < M.m
  post s s' :=
    numAt s'.mem (s.gpr .r3) (ofs32 s .r4) M.k = (arg M s .r5 + M.m - arg M s .r6) % M.m ∧
    Keeps M.k (s.gpr .r3) (ofs32 s .r4) s.mem s'.mem
  pub := ppcPub

theorem numAt_eq (m : Mem) (ws : Addr) (o : BitVec 32) (k : Nat) :
    numAt m ws o k = wordsVal m ws o.toNat k :=
  read_eq_wordsVal m ws k o.toNat

theorem pre_of {M : Modulus} {s : State} (h : ppcPre M s) : Pre M.k s := by
  obtain ⟨-, h2, h3, ho, ha, hb⟩ := h
  exact ⟨h2, h3, ho, ha, hb⟩

theorem keeps_of_kept {k : Nat} (hk : k ≤ 9) {ws : Addr} {o : BitVec 32} {m m' : Mem}
    (h : Kept k ws o.toNat m m') : Keeps k ws o m m' := by
  intro i hi hown ho
  simp only [Impl.Weierstrass.Mont.wsBytes] at hi
  have hown' := own_le k hk
  refine h _ fun r hr => ?_
  rw [ofs_off0 ws (by omega)]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · omega
  · simp only [own] at hown' ⊢; omega

theorem mul_ppc {M : Modulus} (hM : ModOk M.k M.m) (s : State) (hs : (mulPPC M).pre s) :
    ∃ t s', Exec isa (mulFn M.k M.m) s t s' ∧ abiPreserved s s' ∧ (mulPPC M).post s s' := by
  obtain ⟨t, s', he, A, -, V, C, K⟩ := mulFn_ok hM (pre_of hs.1) (by have := hs.2; simp only [arg, numAt_eq] at this; exact this)
  refine ⟨t, s', he, A, ?_, ?_, keeps_of_kept hM.n9 K⟩
  · rw [numAt_eq]; exact V
  · simp only [arg, numAt_eq, Modulus.R]; exact C

theorem add_ppc {M : Modulus} (hM : ModOk M.k M.m) (s : State) (hs : (addPPC M).pre s) :
    ∃ t s', Exec isa (addFn M.k M.m) s t s' ∧ abiPreserved s s' ∧ (addPPC M).post s s' := by
  obtain ⟨t, s', he, A, -, V, K⟩ := addFn_ok hM (pre_of hs.1) (by have := hs.2; simp only [arg, numAt_eq] at this; exact this)
  exact ⟨t, s', he, A, by simp only [arg, numAt_eq]; exact V, keeps_of_kept hM.n9 K⟩

theorem sub_ppc {M : Modulus} (hM : ModOk M.k M.m) (s : State) (hs : (subPPC M).pre s) :
    ∃ t s', Exec isa (subFn M.k M.m) s t s' ∧ abiPreserved s s' ∧ (subPPC M).post s s' := by
  obtain ⟨t, s', he, A, -, V, K⟩ := subFn_ok hM (pre_of hs.1) (by have := hs.2.1; simp only [arg, numAt_eq] at this; exact this)
    (by have := hs.2.2; simp only [arg, numAt_eq] at this; exact this)
  exact ⟨t, s', he, A, by simp only [arg, numAt_eq]; exact V, keeps_of_kept hM.n9 K⟩

end VG.Proof.Weierstrass.PPC64LE.Mont
