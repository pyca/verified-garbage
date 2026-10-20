module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Prep
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# Timing of the public NAF's recoding

Two runs recoding the same scalar leak the same trace (`prep_relCT`): every
iteration branches and addresses by the residual, the constants, the count
and the digits' pointer, which both runs share.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.PubNaf

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64.PubNaf
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (read_x)

/-- The registers whose values the recoding's branches and addresses depend on. -/
def prepPublic (n : Nat) : List Reg := [.x0, .x19, .x20] ++ limbs n ++ csts n

/-- The recoding's pieces whose timing taint tracking checks. -/
structure PrepChecks (K : WinCfg) (src : Nat) : Prop where
  init : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0]))
    (.block (prepInit K src))
  step : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs (prepPublic K.M.n)))
    (prepStep K.M.n)

/-- Equal values of registers are equal registers. -/
theorem regsVal_inj {s t : State} : ∀ {rs : List Reg},
    regsVal s rs = regsVal t rs → ∀ r ∈ rs, s.gpr r = t.gpr r
  | [], _, r, hr => absurd hr List.not_mem_nil
  | q :: qs, h, r, hr => by
    simp only [regsVal] at h
    have := (s.gpr q).isLt; have := (t.gpr q).isLt
    have hq : s.gpr q = t.gpr q := BitVec.eq_of_toNat_eq (by omega)
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hq
    · exact regsVal_inj (by omega) r hr

/-- Two runs at the same point of the same recoding. -/
structure PrepPair (n : Nat) (base : Addr) (size bits k j : Nat) (s t : State) : Prop where
  left : PrepSt n base size bits k j s
  right : PrepSt n base size bits k j t
  sp : s.sp = t.sp

theorem PrepPair.public {n : Nat} {base : Addr} {size bits k j : Nat} {s t : State}
    (h : PrepPair n base size bits k j s t) :
    AArch64.Taint.Agree (Taint.ofRegs (prepPublic n)) s t := by
  have hv := regsVal_inj (h.left.value.trans h.right.value.symm)
  refine ⟨h.sp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, prepPublic, csts, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with ((rfl | rfl | rfl) | hr) | (rfl | rfl | rfl | rfl)
  · exact h.left.scr.x0.trans h.right.scr.x0.symm
  · exact h.left.count.trans h.right.count.symm
  · exact h.left.ptr.trans h.right.ptr.symm
  · exact hv r hr
  · exact h.left.mask.trans h.right.mask.symm
  · exact h.left.sign.trans h.right.sign.symm
  · exact h.left.zero.trans h.right.zero.symm
  · exact h.left.one.trans h.right.one.symm

theorem prepStep_relCT {K : WinCfg} {src : Nat} (hR : Regs K.M.n) (hc : PrepChecks K src)
    {base : Addr} {size k j : Nat} (hb : K.bits + (64 * K.M.n + 1) ≤ size) (hj : j < 64 * K.M.n + 1)
    (hv : Naf5.residual k j ≤ 2 ^ (64 * K.M.n)) :
    RelCT isa (PrepPair K.M.n base size K.bits k j) (prepStep K.M.n)
      (PrepPair K.M.n base size K.bits k (j + 1)) := by
  intro s t ts tt s' t' hp es et
  obtain ⟨_, _, xs, is, ks, _⟩ := prepStep_ok hR hp.left hb hj hv
  obtain ⟨_, _, xt, it, kt, _⟩ := prepStep_ok hR hp.right hb hj hv
  obtain ⟨_, rfl⟩ := Exec.det es xs
  obtain ⟨_, rfl⟩ := Exec.det et xt
  exact ⟨hc.step _ _ _ _ _ _ trivial trivial hp.public es et, is, it,
    ks.sp.trans (hp.sp.trans kt.sp.symm)⟩

theorem prepLoop_relCT {K : WinCfg} {src : Nat} (hR : Regs K.M.n) (hc : PrepChecks K src)
    {base : Addr} {size k : Nat} (hb : K.bits + (64 * K.M.n + 1) ≤ size)
    (hk : k < 2 ^ (64 * K.M.n)) :
    RelCT isa (PrepPair K.M.n base size K.bits k 0) (.loop (prepStep K.M.n) (.nonzero .x .x19))
      (fun _ _ => True) := by
  have hle := hR.le
  let D := 64 * K.M.n + 1
  let I := fun m s t => 1 ≤ m ∧ m ≤ D ∧ PrepPair K.M.n base size K.bits k (D - m) s t
  have step : ∀ m, RelCT isa (I m) (prepStep K.M.n) (fun s t =>
      eval (.nonzero .x .x19) s = eval (.nonzero .x .x19) t ∧
      (eval (.nonzero .x .x19) s = some false → True) ∧
      (eval (.nonzero .x .x19) s = some true → ∃ n < m, I n s t)) := by
    intro m
    by_cases hm : 1 ≤ m ∧ m ≤ D
    · have hp := Naf5.residual_boundB (B := 64 * K.M.n) (Nat.le_of_lt hk) (j := D - m) (by omega)
      have hv : Naf5.residual k (D - m) ≤ 2 ^ (64 * K.M.n) :=
        Nat.le_trans hp (Nat.pow_le_pow_right (by decide) (by omega))
      refine (prepStep_relCT hR hc hb (j := D - m) (by omega) hv).mono
        (P' := I m) (fun _ _ h => h.2.2) ?_
      intro s t hp
      have s19 : s.gpr .x19 = BitVec.ofNat 64 (m - 1) := by rw [hp.left.count]; congr 1; omega
      have t19 : t.gpr .x19 = BitVec.ofNat 64 (m - 1) := by rw [hp.right.count]; congr 1; omega
      refine ⟨by simp only [eval, read_x, s19, t19], fun _ => trivial, fun he => ?_⟩
      have hn : m - 1 ≠ 0 := by
        intro hz; simp only [eval, read_x, s19, hz] at he; cases he
      refine ⟨m - 1, by omega, by omega, by omega, ?_⟩
      have hj : D - (m - 1) = D - m + 1 := by omega
      rw [hj]; exact hp
    · exact RelCT.of_false (fun _ _ h => hm ⟨h.1, h.2.1⟩)
  exact (RelCT.loop I step D).mono (fun _ _ h => ⟨by omega, Nat.le_refl _, by simpa [D] using h⟩)
    (fun _ _ h => h)

/-- The recoding of the same scalar in two runs leaks the same trace. -/
theorem prep_relCT (K : WinCfg) (hR : Regs K.M.n) {base : Addr} {size src : Nat}
    (hsrc : src + 8 * K.M.n ≤ size) (hsrc8 : src % 8 = 0) (hbits : K.bits < 4096)
    (hb : K.bits + (64 * K.M.n + 1) ≤ size) (hc : PrepChecks K src) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧ s.sp = t.sp ∧
      wordsVal s.mem base src K.M.n = wordsVal t.mem base src K.M.n)
      (prep K src) (fun _ _ => True) := by
  intro s t ts tt s' t' hp es et
  have hi : RelCT isa (fun a b => Scr a base size ∧ Scr b base size ∧ a.sp = b.sp ∧
      wordsVal a.mem base src K.M.n = wordsVal s.mem base src K.M.n ∧
      wordsVal b.mem base src K.M.n = wordsVal s.mem base src K.M.n)
      (.block (prepInit K src)) (PrepPair K.M.n base size K.bits (wordsVal s.mem base src K.M.n) 0) := by
    intro a b ta tb a' b' hab ea eb
    obtain ⟨_, _, xa, ia, ka, _⟩ := init_ok K hR hab.1 hsrc hsrc8 hbits
    obtain ⟨_, _, xb, ib, kb, _⟩ := init_ok K hR hab.2.1 hsrc hsrc8 hbits
    obtain ⟨_, rfl⟩ := Exec.det ea xa
    obtain ⟨_, rfl⟩ := Exec.det eb xb
    rw [hab.2.2.2.1] at ia
    rw [hab.2.2.2.2] at ib
    have pub : AArch64.Taint.Agree (Taint.ofRegs [.x0]) a b := by
      refine ⟨hab.2.2.1, ?_⟩
      intro r hr; simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst r
      exact hab.1.x0.trans hab.2.1.x0.symm
    exact ⟨hc.init _ _ _ _ _ _ trivial trivial pub ea eb, ia, ib, ka.sp.trans (hab.2.2.1.trans kb.sp.symm)⟩
  rw [prep] at es et
  exact (RelCT.seq hi (prepLoop_relCT hR hc hb (wordsVal_lt ..))) _ _ _ _ _ _
    ⟨hp.1, hp.2.1, hp.2.2.1, rfl, hp.2.2.2.symm⟩ es et

end VG.Proof.Weierstrass.AArch64.PubNaf
