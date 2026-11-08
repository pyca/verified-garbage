module

public import VerifiedGarbage.Impl.Zeroize.PPC64LE
meta import VerifiedGarbage.Impl.Zeroize.PPC64LE
public import VerifiedGarbage.Proof.Zeroize.Common
meta import VerifiedGarbage.Proof.Zeroize.Common
public import VerifiedGarbage.Proof.Framework.PPC64LE.Run
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Zeroize.Contract
meta import VerifiedGarbage.Spec.Zeroize.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.Offset
import all Init.Data.Nat.Bitwise.Basic

/-!
# Zeroization on PPC64LE

Untrusted: everything here is checked by Lean. The same structure as the
AArch64 proof (`VG.Proof.Zeroize.AArch64`).
-/

@[expose] public section

namespace VG.Proof.Zeroize.PPC64LE
open VG VG.PPC64LE VG.Impl.Zeroize.PPC64LE

def contract : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .r3, (s.gpr .r4).toNat⟩]
  post s t := Spec.Zeroize.bytesAt t.mem (s.gpr .r3) (s.gpr .r4).toNat =
    Spec.Zeroize.zeros (s.gpr .r4).toNat
  pub s t := s.gpr .r3 = t.gpr .r3 ∧ s.gpr .r4 = t.gpr .r4 ∧ s.sp = t.sp

def Inv (s₀ : State) (i : Nat) (s : State) : Prop :=
  s.wr = s₀.wr ∧ s.gpr .r5 = 0 ∧ s.gpr .r3 = s₀.gpr .r3 + BitVec.ofNat 64 i ∧
  Prefix s.mem (s₀.gpr .r3) i ∧ Frame s₀.wr s₀.mem s.mem

theorem step_ok (word : Bool) (s₀ s : State) (hp : contract.pre s₀) (i : Nat)
    (hi : i + (if word then 8 else 1) ≤ (s₀.gpr .r4).toNat) (h : Inv s₀ i s) :
    WP isa (.block (step word)) s fun t =>
      Inv s₀ (i + (if word then 8 else 1)) t ∧
      t.gpr .r6 = s.gpr .r6 - 1 ∧ t.gpr .r4 = s.gpr .r4 := by
  obtain ⟨hw, ha, hd, hz, hf⟩ := h
  have hn := (s₀.gpr .r4).isLt
  have hc : (⟨s₀.gpr .r3, (s₀.gpr .r4).toNat⟩ : Region).Contains
      (s₀.gpr .r3 + BitVec.ofNat 64 i) (if word then 8 else 1) :=
    Offset.contains_base _ hi (by cases word <;> simp_all <;> omega)
  have hs : InRegions s.wr (s₀.gpr .r3 + BitVec.ofNat 64 i) (if word then 8 else 1) :=
    ⟨_, by rw [hw, hp.2]; simp, hc⟩
  have hmem := List.mem_singleton_self (⟨s₀.gpr .r3, (s₀.gpr .r4).toNat⟩ : Region)
  rw [← hp.2] at hmem
  rw [hw] at hs
  have hadd (k : Nat) : s₀.gpr .r3 + BitVec.ofNat 64 i + BitVec.ofNat 64 k =
      s₀.gpr .r3 + BitVec.ofNat 64 (i + k) := by rw [BitVec.add_assoc, BitVec.ofNat_add]
  cases word <;> simp only [Bool.false_eq_true, ↓reduceIte] at hi hc hs ⊢ <;> unfold step <;>
    crun [hd, ha, hs, hw, Inv, (show (0 : BitVec 64).setWidth 8 = 0 from rfl)]
  · exact ⟨hadd _, prefix_write hz (by omega), hf.write hmem _ hc⟩
  · exact ⟨hadd _, prefix_write hz (by omega), hf.write hmem _ hc⟩

theorem loop_ok (word : Bool) (s₀ s : State) (hp : contract.pre s₀) (i n : Nat)
    (hn : i + (if word then 8 else 1) * n ≤ (s₀.gpr .r4).toNat)
    (h : Inv s₀ i s) (hc : s.gpr .r6 = BitVec.ofNat 64 n) :
    WP isa (loop word) s fun t =>
      Inv s₀ (i + (if word then 8 else 1) * n) t ∧ t.gpr .r4 = s.gpr .r4 := by
  have hlt : n < 2 ^ 64 := by
    have := (s₀.gpr .r4).isLt
    cases word <;> simp only [↓reduceIte, Bool.false_eq_true] at hn <;> omega
  unfold loop
  by_cases he : n = 0
  · subst n
    refine WP.ite true (by simp [VG.PPC64LE.eval, State.read, hc]) (fun _ => WP.block_nil ?_)
      (by simp)
    simpa only [Nat.mul_zero, Nat.add_zero] using And.intro h (rfl : s.gpr .r4 = s.gpr .r4)
  · have hne : BitVec.ofNat 64 n ≠ (0 : BitVec 64) := by bv_omega
    refine WP.ite false (by simp only [VG.PPC64LE.eval, State.read, BitVec.setWidth_eq, hc,
      beq_eq_false_iff_ne.mpr hne]) (by simp) (fun _ => ?_)
    refine WP.loop (M := isa) (fun rem t => ∃ j, j < n ∧ rem = n - j ∧
      Inv s₀ (i + (if word then 8 else 1) * j) t ∧ t.gpr .r6 = BitVec.ofNat 64 (n-j) ∧
      t.gpr .r4 = s.gpr .r4) ?_ n s ?_
    · intro rem t ⟨j, hj, hr, ht, hct, hst⟩
      refine WP.mono (step_ok word s₀ t hp _ ?_ ht) fun u ⟨hu, hcu, hsu⟩ => ?_
      · cases word <;> simp only [↓reduceIte, Bool.false_eq_true] at hn ⊢ <;> omega
      have hpred : BitVec.ofNat 64 (n-j) - 1 = BitVec.ofNat 64 (n-(j+1)) := by bv_omega
      rw [hct, hpred] at hcu
      have hoff : i + (if word then 8 else 1) * j + (if word then 8 else 1) =
          i + (if word then 8 else 1) * (j+1) := by rw [Nat.mul_succ, Nat.add_assoc]
      rw [hoff] at hu
      by_cases hend : j + 1 = n
      · left
        refine ⟨by simp [VG.PPC64LE.eval, State.read, hcu, hend], ?_⟩
        rw [hend] at hu
        exact ⟨hu, hsu.trans hst⟩
      · right
        have hnz : BitVec.ofNat 64 (n-(j+1)) ≠ (0 : BitVec 64) := by bv_omega
        refine ⟨by simp only [VG.PPC64LE.eval, State.read, BitVec.setWidth_eq, hcu, bne,
          beq_eq_false_iff_ne.mpr hnz]; rfl, n-(j+1), by omega,
          j+1, by omega, rfl, hu, hcu, hsu.trans hst⟩
    · exact ⟨0, by omega, by omega, by simpa using h, by simpa using hc, rfl⟩

/-- The `m` doublewords after a zero prefix of `i` bytes, of a run of `stores`. -/
theorem stores_ok (s₀ s : State) (hp : contract.pre s₀) (i : Nat) (hi : i + 64 ≤ (s₀.gpr .r4).toNat)
    (h : Inv s₀ i s) (m : Nat) (hm : m ≤ 8) {rest : List Instr} {Φ : State → Prop}
    (cont : ∀ t, t.gpr = s.gpr → t.wr = s.wr → Prefix t.mem (s₀.gpr .r3) (i + 8 * m) →
      Frame s₀.wr s₀.mem t.mem → WP isa (.block rest) t Φ) :
    WP isa (.block (stores m ++ rest)) s Φ := by
  obtain ⟨hw, ha, hd, hz, hf⟩ := h
  have hn := (s₀.gpr .r4).isLt
  induction m generalizing rest Φ with
  | zero => exact cont s rfl rfl hz hf
  | succ m ih =>
    rw [stores, List.range_succ, List.map_append, List.append_assoc]
    refine ih (by omega) fun t hg hwt hzt hft => ?_
    have hc : (⟨s₀.gpr .r3, (s₀.gpr .r4).toNat⟩ : Region).Contains
        (s₀.gpr .r3 + BitVec.ofNat 64 (i + 8 * m)) (64 / 8) :=
      Offset.contains_base _ (by omega) (by omega)
    have hmem := List.mem_singleton_self (⟨s₀.gpr .r3, (s₀.gpr .r4).toNat⟩ : Region)
    rw [← hp.2] at hmem
    refine wp_std (a := s₀.gpr .r3 + BitVec.ofNat 64 (i + 8 * m)) (by decide) ⟨by omega, by omega⟩
      (by rw [hg, hd, BitVec.add_assoc, BitVec.ofNat_add]) ⟨_, by rw [hwt, hw, hp.2]; simp, hc⟩
      fun t' u => ?_
    have h5 : t.gpr .r5 = 0 := by rw [hg, ha]
    rw [h5] at u
    refine cont t' (by rw [u.gpr, hg]) (by rw [u.wr, hwt]) ?_ ?_
    · rw [u.mem]
      have := prefix_writeW (w := 64) hzt (by omega)
      rwa [show i + 8 * m + 64 / 8 = i + 8 * (m + 1) by omega] at this
    · rw [u.mem]; exact hft.writeW hmem _ hc

theorem wide_ok (s₀ s : State) (hp : contract.pre s₀) (i : Nat) (hi : i + 64 ≤ (s₀.gpr .r4).toNat)
    (h : Inv s₀ i s) :
    WP isa (.block wide) s fun t => Inv s₀ (i + 64) t ∧ t.gpr .r6 = s.gpr .r6 - 1 ∧ t.gpr .r4 = s.gpr .r4 := by
  unfold wide
  refine stores_ok s₀ s hp i hi h 8 (by decide) fun t hg hwt hzt hft => ?_
  refine wp_addi (by decide) (by decide) fun t₁ u₁ => wp_subi (by decide) (by decide) fun t₂ u₂ => wp_nil ?_
  refine ⟨⟨by rw [u₂.wr, u₁.wr, hwt, h.1], by rw [u₂.other _ (by decide), u₁.other _ (by decide), hg, h.2.1],
    ?_, by rw [u₂.mem, u₁.mem]; exact hzt, by rw [u₂.mem, u₁.mem]; exact hft⟩,
    by rw [u₂.gpr, u₁.other _ (by decide), hg]; rfl, by rw [u₂.other _ (by decide), u₁.other _ (by decide), hg]⟩
  rw [u₂.other _ (by decide), u₁.gpr, hg, h.2.2.1, BitVec.add_assoc, BitVec.ofNat_add]

theorem wideLoop_ok (s₀ s : State) (hp : contract.pre s₀) (i n : Nat)
    (hn : i + 64 * n ≤ (s₀.gpr .r4).toNat)
    (h : Inv s₀ i s) (hc : s.gpr .r6 = BitVec.ofNat 64 n) :
    WP isa wideLoop s fun t => Inv s₀ (i + 64 * n) t ∧ t.gpr .r4 = s.gpr .r4 := by
  have hlt : n < 2 ^ 64 := by have := (s₀.gpr .r4).isLt; omega
  unfold wideLoop
  by_cases he : n = 0
  · subst n
    refine WP.ite true (by simp [VG.PPC64LE.eval, State.read, hc]) (fun _ => WP.block_nil ?_)
      (by simp)
    simpa only [Nat.mul_zero, Nat.add_zero] using And.intro h (rfl : s.gpr .r4 = s.gpr .r4)
  · refine WP.ite false (eval_zero_ofNat s .r6 hlt hc |>.trans (by simp [he])) (by simp) (fun _ => ?_)
    refine WP.loop (M := isa) (fun rem t => ∃ j, j < n ∧ rem = n - j ∧
      Inv s₀ (i + 64 * j) t ∧ t.gpr .r6 = BitVec.ofNat 64 (n - j) ∧ t.gpr .r4 = s.gpr .r4) ?_ n s ?_
    · intro rem t ⟨j, hj, hr, ht, hct, hst⟩
      refine WP.mono (wide_ok s₀ t hp _ (by omega) ht) fun u ⟨hu, hcu, hsu⟩ => ?_
      have hpred : BitVec.ofNat 64 (n - j) - 1 = BitVec.ofNat 64 (n - (j + 1)) := by
        rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
      rw [hct, hpred] at hcu
      rw [show i + 64 * j + 64 = i + 64 * (j + 1) by omega] at hu
      have ev := eval_nonzero_ofNat' u .r6 (k := n - (j + 1)) (by omega) hcu
      by_cases hend : j + 1 = n
      · left
        refine ⟨by rw [ev]; simp [hend], ?_⟩
        rw [hend] at hu
        exact ⟨hu, hsu.trans hst⟩
      · right
        exact ⟨by rw [ev]; simp; omega, n - (j + 1), by omega, j + 1, by omega, rfl, hu, hcu, hsu.trans hst⟩
    · exact ⟨0, by omega, by omega, by simpa using h, by simpa using hc, rfl⟩

theorem and63 (x : BitVec 64) : x &&& 63 = BitVec.ofNat 64 (x.toNat % 64) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (63 : BitVec 64).toNat = 2 ^ 6 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  simp only [BitVec.toNat_ofNat]
  omega

theorem ofNat_shr3 {a : Nat} (ha : a < 2 ^ 64) : BitVec.ofNat 64 a >>> 3 = BitVec.ofNat 64 (a / 8) := by
  rw [count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]

theorem correct (s₀ : State) (hp : contract.pre s₀) :
    WP isa zeroize s₀ fun t => contract.post s₀ t ∧ Frame s₀.wr s₀.mem t.mem := by
  let n := (s₀.gpr .r4).toNat
  have hn : n < 2 ^ 64 := (s₀.gpr .r4).isLt
  have start : WP isa (.block [.li .r5 0, .lsr .d .r6 .r4 6]) s₀ fun t =>
      Inv s₀ 0 t ∧ t.gpr .r6 = BitVec.ofNat 64 (n / 64) ∧ t.gpr .r4 = s₀.gpr .r4 := by
    refine wp_li (by decide) fun t₁ u₁ => wp_lsr (by decide) fun t₂ u₂ => wp_nil ?_
    refine ⟨⟨by rw [u₂.wr, u₁.wr], by rw [u₂.other _ (by decide), u₁.gpr]; rfl,
      by rw [u₂.other _ (by decide), u₁.other _ (by decide)]; simp, fun j hj => absurd hj (Nat.not_lt_zero _),
      by rw [u₂.mem, u₁.mem]; exact Frame.refl _ _⟩, ?_, by rw [u₂.other _ (by decide), u₁.other _ (by decide)]⟩
    rw [u₂.gpr, u₁.other _ (by decide), shr64]
  unfold zeroize
  refine WP.seq (WP.mono start fun t ⟨ht, hc, hs⟩ => ?_)
  refine WP.seq (WP.mono (wideLoop_ok s₀ t hp 0 (n / 64) (by dsimp [n]; omega) ht hc)
    fun u ⟨hu, hsu⟩ => ?_)
  have hu4 : u.gpr .r4 = s₀.gpr .r4 := hsu.trans hs
  have mid : WP isa (.block [.li .r7 63, .logic .and .r6 .r4 .r7, .lsr .d .r6 .r6 3]) u fun v =>
      Inv s₀ (0 + 64 * (n / 64)) v ∧ v.gpr .r6 = BitVec.ofNat 64 (n % 64 / 8) ∧ v.gpr .r4 = s₀.gpr .r4 := by
    refine wp_li (by decide) fun v₁ w₁ => wp_and fun v₂ w₂ => wp_lsr (by decide) fun v₃ w₃ => wp_nil ?_
    refine ⟨⟨by rw [w₃.wr, w₂.wr, w₁.wr]; exact hu.1,
      by rw [w₃.other _ (by decide), w₂.other _ (by decide), w₁.other _ (by decide)]; exact hu.2.1,
      by rw [w₃.other _ (by decide), w₂.other _ (by decide), w₁.other _ (by decide)]; exact hu.2.2.1,
      by rw [w₃.mem, w₂.mem, w₁.mem]; exact hu.2.2.2.1, by rw [w₃.mem, w₂.mem, w₁.mem]; exact hu.2.2.2.2⟩, ?_,
      by rw [w₃.other _ (by decide), w₂.other _ (by decide), w₁.other _ (by decide), hu4]⟩
    rw [w₃.gpr, w₂.gpr, w₁.other _ (by decide), w₁.gpr, hu4, show (BitVec.ofNat 64 63) = (63 : BitVec 64) from rfl,
      and63, ofNat_shr3 (by omega)]
  refine WP.seq (WP.mono mid fun v ⟨hv, hcv, hv4⟩ => ?_)
  refine WP.seq (WP.mono (loop_ok true s₀ v hp (0 + 64 * (n / 64)) (n % 64 / 8) (by simp; dsimp [n]; omega)
    hv hcv) fun w ⟨hw, hsw⟩ => ?_)
  have mid2 : WP isa (.block [.li .r7 7, .logic .and .r6 .r4 .r7]) w fun x =>
      Inv s₀ (0 + 64 * (n / 64) + (if true then 8 else 1) * (n % 64 / 8)) x ∧
        x.gpr .r6 = BitVec.ofNat 64 (n % 8) := by
    refine wp_li (by decide) fun x₁ y₁ => wp_and fun x₂ y₂ => wp_nil ?_
    refine ⟨⟨by rw [y₂.wr, y₁.wr]; exact hw.1, by rw [y₂.other _ (by decide), y₁.other _ (by decide)]; exact hw.2.1,
      by rw [y₂.other _ (by decide), y₁.other _ (by decide)]; exact hw.2.2.1,
      by rw [y₂.mem, y₁.mem]; exact hw.2.2.2.1, by rw [y₂.mem, y₁.mem]; exact hw.2.2.2.2⟩, ?_⟩
    rw [y₂.gpr, y₁.other _ (by decide), y₁.gpr, hsw, hv4, show (BitVec.ofNat 64 7) = (7 : BitVec 64) from rfl, tail]
  refine WP.seq (WP.mono mid2 fun x ⟨hx, hcx⟩ => ?_)
  refine WP.mono (loop_ok false s₀ x hp _ (n % 8) (by simp; dsimp [n]; omega) hx hcx) fun y ⟨hy, _⟩ => ?_
  have he : 0 + 64 * (n / 64) + (if true then 8 else 1) * (n % 64 / 8) + (if false then 8 else 1) * (n % 8) = n := by
    simp; omega
  rw [he] at hy
  exact ⟨prefix_spec hy.2.2.2.1, hy.2.2.2.2⟩

def sat : State where
  gpr _ := 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0, 0⟩]

theorem verified : Verified target zeroize (Spec.Zeroize.zeroizeContract abi) := by
  apply Verified.of_correct (k := contract)
  · intro s hp
    obtain ⟨tr, t, he, ho, _⟩ := correct s hp
    refine ⟨tr, t, he, ⟨?_, Exec.sp he, Exec.lr he (by decide +kernel)
      (by rw [← Code.allInstrs_eq]; decide +kernel)⟩, ho⟩
    intro r hr
    have hc : ((instrs zeroize).all fun i => preserved.all fun r => dstOf i != some r) = true := by
      rw [← Code.allInstrs_eq]; decide +kernel
    apply Exec.gpr (fun i hi => ?_) he
    simpa using List.all_eq_true.mp (List.all_eq_true.mp hc i hi) r hr
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4]) ?_ (by taint_decide)
    intro s t _ _ h
    refine ⟨h.2.2, ?_⟩
    intro r hr
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1
    · exact h.2.1
  · sig_implies [Spec.Zeroize.zeroizeContract, Spec.Zeroize.zeroizeSig, contract, abi, argRegs]
      [sat] using sat

end VG.Proof.Zeroize.PPC64LE
