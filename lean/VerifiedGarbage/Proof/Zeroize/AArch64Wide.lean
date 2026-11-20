module

public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Impl.Zeroize.AArch64Wide
public import VerifiedGarbage.Proof.Framework.AArch64.ModeSim
import VerifiedGarbage.Proof.Ct.AArch64
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Zeroize.AArch64Wide
meta import VerifiedGarbage.Proof.Ct.AArch64
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Residue
meta import VerifiedGarbage.Proof.Framework.AArch64.Residue
public import VerifiedGarbage.Impl.Zeroize.AArch64
public import VerifiedGarbage.Proof.Zeroize.Common
public import VerifiedGarbage.Spec.Zeroize.Contract
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Impl.Zeroize.AArch64
meta import VerifiedGarbage.Proof.Zeroize.Common
meta import VerifiedGarbage.Spec.Zeroize.Contract
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.TCB.AArch64.Target

/-! ### `Zeroize.AArch64`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Zeroize.AArch64
open VG VG.AArch64 VG.Impl.Zeroize.AArch64 RegUpd

def contract : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .x0, (s.gpr .x1).toNat⟩]
  post s t := Spec.Zeroize.bytesAt t.mem (s.gpr .x0) (s.gpr .x1).toNat =
    Spec.Zeroize.zeros (s.gpr .x1).toNat
  pub s t := s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧ s.sp = t.sp

def Inv (s₀ : State) (i : Nat) (s : State) : Prop :=
  s.wr = s₀.wr ∧ s.gpr .x2 = 0 ∧ s.gpr .x0 = s₀.gpr .x0 + BitVec.ofNat 64 i ∧
  Prefix s.mem (s₀.gpr .x0) i ∧ Frame s₀.wr s₀.mem s.mem

theorem step_ok (word : Bool) (s₀ s : State) (hp : contract.pre s₀) (i : Nat)
    (hi : i + (if word then 8 else 1) ≤ (s₀.gpr .x1).toNat) (h : Inv s₀ i s) :
    WP isa (.block (step word)) s fun t =>
      Inv s₀ (i + (if word then 8 else 1)) t ∧
      t.gpr .x3 = s.gpr .x3 - 1 ∧ t.gpr .x1 = s.gpr .x1 := by
  obtain ⟨hw, ha, hd, hz, hf⟩ := h
  have hn := (s₀.gpr .x1).isLt
  have hc : (⟨s₀.gpr .x0, (s₀.gpr .x1).toNat⟩ : Region).Contains
      (s₀.gpr .x0 + BitVec.ofNat 64 i) (if word then 8 else 1) :=
    Offset.contains_base _ hi (by cases word <;> simp_all <;> omega_using [hi])
  have hs : InRegions s.wr (s₀.gpr .x0 + BitVec.ofNat 64 i) (if word then 8 else 1) :=
    ⟨_, by rw [hw, hp.2]; simp, hc⟩
  have hmem := List.mem_singleton_self (⟨s₀.gpr .x0, (s₀.gpr .x1).toNat⟩ : Region)
  rw [← hp.2] at hmem
  rw [hw] at hs
  have hadd (k : Nat) : s₀.gpr .x0 + BitVec.ofNat 64 i + BitVec.ofNat 64 k =
      s₀.gpr .x0 + BitVec.ofNat 64 (i + k) := by rw [BitVec.add_assoc, BitVec.ofNat_add]
  cases word <;> simp only [Bool.false_eq_true, ↓reduceIte] at hi hc hs ⊢ <;> unfold step <;>
    crun [hd, ha, hs, Inv, hw, State.store,
      (show (0 : BitVec 64).setWidth 32 = 0 from rfl),
      (show (0 : BitVec 32).setWidth 8 = 0 from rfl)]
  · exact ⟨hadd _, prefix_write hz (by dsimp [Size.bytes]; omega_using [hi]), hf.write hmem _ hc⟩
  · exact ⟨hadd _, prefix_write hz (by dsimp [Size.bytes]; omega_using [hi]), hf.write hmem _ hc⟩

theorem loop_ok (word : Bool) (s₀ s : State) (hp : contract.pre s₀) (i n : Nat)
    (hn : i + (if word then 8 else 1) * n ≤ (s₀.gpr .x1).toNat)
    (h : Inv s₀ i s) (hc : s.gpr .x3 = BitVec.ofNat 64 n) :
    WP isa (loop word) s fun t =>
      Inv s₀ (i + (if word then 8 else 1) * n) t ∧ t.gpr .x1 = s.gpr .x1 := by
  have hlt : n < 2 ^ 64 := by
    have := (s₀.gpr .x1).isLt
    cases word <;> simp only [↓reduceIte, Bool.false_eq_true] at hn <;> omega_using [hn]
  unfold loop
  by_cases he : n = 0
  · subst n
    refine WP.ite true (by simp [eval, State.read, hc]) (fun _ => WP.block_nil ?_) (by simp)
    simpa only [Nat.mul_zero, Nat.add_zero] using And.intro h (rfl : s.gpr .x1 = s.gpr .x1)
  · have hne : BitVec.ofNat 64 n ≠ (0 : BitVec 64) := by bv_omega
    refine WP.ite false (by simp only [eval, State.read, BitVec.setWidth_eq, hc, beq_eq_false_iff_ne.mpr hne]) (by simp) (fun _ => ?_)
    refine WP.loop (M := isa) (fun rem t => ∃ j, j < n ∧ rem = n - j ∧
      Inv s₀ (i + (if word then 8 else 1) * j) t ∧ t.gpr .x3 = BitVec.ofNat 64 (n-j) ∧
      t.gpr .x1 = s.gpr .x1) ?_ n s ?_
    · intro rem t ⟨j, hj, hr, ht, hct, hst⟩
      refine WP.mono (step_ok word s₀ t hp _ ?_ ht) fun u ⟨hu, hcu, hsu⟩ => ?_
      · cases word <;> simp only [↓reduceIte, Bool.false_eq_true] at hn ⊢ <;> omega_using [hj, hn]
      have hpred : BitVec.ofNat 64 (n-j) - 1 = BitVec.ofNat 64 (n-(j+1)) := by bv_omega
      rw [hct, hpred] at hcu
      have hoff : i + (if word then 8 else 1) * j + (if word then 8 else 1) =
          i + (if word then 8 else 1) * (j+1) := by rw [Nat.mul_succ, Nat.add_assoc]
      rw [hoff] at hu
      by_cases hend : j + 1 = n
      · left
        refine ⟨by simp [eval, State.read, hcu, hend], ?_⟩
        rw [hend] at hu
        exact ⟨hu, hsu.trans hst⟩
      · right
        have hnz : BitVec.ofNat 64 (n-(j+1)) ≠ (0 : BitVec 64) := by bv_omega
        refine ⟨by simp only [eval, State.read, BitVec.setWidth_eq, hcu, bne, beq_eq_false_iff_ne.mpr hnz]; rfl, n-(j+1), by omega_using [hj, hr],
          j+1, by omega_using [hj, hend], rfl, hu, hcu, hsu.trans hst⟩
    · exact ⟨0, by omega_using [he], by omega_using [], by simpa using h, by simpa using hc, rfl⟩

def sat : State where
  gpr _ := 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0, 0⟩]

end VG.Proof.Zeroize.AArch64

end

end

@[expose] public section

namespace VG.Proof.Zeroize.AArch64
open VG VG.AArch64 VG.Impl.Zeroize.AArch64 RegUpd

def InvV (s₀ : State) (i : Nat) (s : State) : Prop :=
  Inv s₀ i s ∧ s.v .v0 = 0

theorem wideStep_ok (s₀ s : State) (hp : contract.pre s₀) (i : Nat)
    (hi : i + 128 ≤ (s₀.gpr .x1).toNat) (h : InvV s₀ i s) :
    WP isa (.block wideStep) s fun t =>
      InvV s₀ (i + 128) t ∧ t.gpr .x3 = s.gpr .x3 - 1 ∧ t.gpr .x1 = s.gpr .x1 := by
  obtain ⟨⟨hw, ha, hd, hz, hf⟩, hv⟩ := h
  have hn := (s₀.gpr .x1).isLt
  have hc : ∀ k, k ≤ 112 → (⟨s₀.gpr .x0, (s₀.gpr .x1).toNat⟩ : Region).Contains
      (s₀.gpr .x0 + BitVec.ofNat 64 (i + k)) 16 :=
    fun k hk => Offset.contains_base _ (by omega_arith) (by omega_arith)
  have hm := List.mem_singleton_self (⟨s₀.gpr .x0, (s₀.gpr .x1).toNat⟩ : Region)
  rw [← hp.2] at hm
  have hs : ∀ k, k ≤ 112 → InRegions s₀.wr (s₀.gpr .x0 + BitVec.ofNat 64 (i + k)) 16 :=
    fun k hk => ⟨_, hm, hc k hk⟩
  have hadd (k : Nat) : s₀.gpr .x0 + BitVec.ofNat 64 i + BitVec.ofNat 64 k =
      s₀.gpr .x0 + BitVec.ofNat 64 (i + k) := by rw [BitVec.add_assoc, BitVec.ofNat_add]
  have s0 := hs 0 (by decide)
  have s16 := hs 16 (by decide)
  have s32 := hs 32 (by decide)
  have s48 := hs 48 (by decide)
  have s64 := hs 64 (by decide)
  have s80 := hs 80 (by decide)
  have s96 := hs 96 (by decide)
  have s112 := hs 112 (by decide)
  rw [Nat.add_zero] at s0
  unfold wideStep
  crun [hd, ha, hv, hw, hadd, s0, s16, s32, s48, s64, s80, s96, s112,
    InvV, Inv, State.store, Nat.add_zero]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  ·
    have h1 := prefix_write (k := 16) hz (by omega_arith)
    have h2 := prefix_write (k := 16) h1 (by omega_arith)
    have h3 := prefix_write (k := 16) h2 (by omega_arith)
    have h4 := prefix_write (k := 16) h3 (by omega_arith)
    have h5 := prefix_write (k := 16) h4 (by omega_arith)
    have h6 := prefix_write (k := 16) h5 (by omega_arith)
    have h7 := prefix_write (k := 16) h6 (by omega_arith)
    have h8 := prefix_write (k := 16) h7 (by omega_arith)
    simpa only [Nat.add_assoc, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] using h8
  ·
    have f1 := hf.write hm 0 (hc 0 (by decide))
    have f2 := f1.write hm 0 (hc 16 (by decide))
    have f3 := f2.write hm 0 (hc 32 (by decide))
    have f4 := f3.write hm 0 (hc 48 (by decide))
    have f5 := f4.write hm 0 (hc 64 (by decide))
    have f6 := f5.write hm 0 (hc 80 (by decide))
    have f7 := f6.write hm 0 (hc 96 (by decide))
    have f8 := f7.write hm 0 (hc 112 (by decide))
    simpa only [Nat.add_zero, BitVec.ofNat_eq_ofNat] using f8
  · simpa only [State.write, BitVec.ofNat_eq_ofNat] using hv

theorem wideLoop_ok (s₀ s : State) (hp : contract.pre s₀) (i n : Nat)
    (hn : i + 128 * n ≤ (s₀.gpr .x1).toNat)
    (h : InvV s₀ i s) (hc : s.gpr .x3 = BitVec.ofNat 64 n) :
    WP isa wideLoop s fun t =>
      InvV s₀ (i + 128 * n) t ∧ t.gpr .x1 = s.gpr .x1 := by
  have hlt : n < 2 ^ 64 := by
    have := (s₀.gpr .x1).isLt
    omega_arith
  unfold wideLoop
  by_cases he : n = 0
  · subst n
    refine WP.ite true (by simp [eval, State.read, hc]) (fun _ => WP.block_nil ?_) (by simp)
    simpa only [Nat.mul_zero, Nat.add_zero] using And.intro h (rfl : s.gpr .x1 = s.gpr .x1)
  · have hne : BitVec.ofNat 64 n ≠ (0 : BitVec 64) := by bv_omega
    refine WP.ite false (by simp only [eval, State.read, BitVec.setWidth_eq, hc, beq_eq_false_iff_ne.mpr hne]) (by simp) (fun _ => ?_)
    refine WP.loop (M := isa) (fun rem t => ∃ j, j < n ∧ rem = n - j ∧
      InvV s₀ (i + 128 * j) t ∧ t.gpr .x3 = BitVec.ofNat 64 (n-j) ∧
      t.gpr .x1 = s.gpr .x1) ?_ n s ?_
    · intro rem t ⟨j, hj, hr, ht, hct, hst⟩
      refine WP.mono (wideStep_ok s₀ t hp _ ?_ ht) fun u ⟨hu, hcu, hsu⟩ => ?_
      · omega_arith
      have hpred : BitVec.ofNat 64 (n-j) - 1 = BitVec.ofNat 64 (n-(j+1)) := by bv_omega
      rw [hct, hpred] at hcu
      have hoff : i + 128 * j + 128 =
          i + 128 * (j+1) := by rw [Nat.mul_succ, Nat.add_assoc]
      rw [hoff] at hu
      by_cases hend : j + 1 = n
      · left
        refine ⟨by simp [eval, State.read, hcu, hend], ?_⟩
        rw [hend] at hu
        exact ⟨hu, hsu.trans hst⟩
      · right
        have hnz : BitVec.ofNat 64 (n-(j+1)) ≠ (0 : BitVec 64) := by bv_omega
        refine ⟨by simp only [eval, State.read, BitVec.setWidth_eq, hcu, bne, beq_eq_false_iff_ne.mpr hnz]; rfl, n-(j+1), by omega_arith,
          j+1, by omega_arith, rfl, hu, hcu, hsu.trans hst⟩
    · exact ⟨0, by omega_arith, by omega_arith, by simpa using h, by simpa using hc, rfl⟩


theorem tail128 (x : BitVec 64) : x &&& 127 = BitVec.ofNat 64 (x.toNat % 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (127 : BitVec 64).toNat = 2 ^ 7 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  simp only [BitVec.toNat_ofNat]
  omega_arith

theorem wideCorrect (s₀ : State) (hp : contract.pre s₀) :
    WP isa zeroizeWide s₀ fun t => contract.post s₀ t ∧ Frame s₀.wr s₀.mem t.mem := by
  let n := (s₀.gpr .x1).toNat
  have start : WP isa (.block [.movz .x .x2 0 0, .lsr .x .x3 .x1 7, .movz .x .x4 127 0,
      .logic .and .x .x1 .x1 .x4, .vop (.dup .d2 .v0 .x2)]) s₀ fun t =>
      InvV s₀ 0 t ∧ t.gpr .x3 = BitVec.ofNat 64 (n / 128) ∧
      t.gpr .x1 = BitVec.ofNat 64 (n % 128) := by
    crun [InvV, Inv, Prefix, shr64, tail128, VOp.eval, State.setV, ofVDwords,
      (show BitVec.setWidth 64 (127#16) = (127 : BitVec 64) from rfl)]
    exact ⟨⟨by omega_arith, Frame.refl _ _⟩, rfl, tail128 _⟩
  unfold zeroizeWide
  refine WP.seq (WP.mono start fun t ⟨ht, hc, hs⟩ => ?_)
  refine WP.seq (WP.mono (wideLoop_ok s₀ t hp 0 (n / 128) (by dsimp [n]; omega_arith) ht hc)
    fun u ⟨hu, hsu⟩ => ?_)
  have mid : WP isa (.block [.lsr .x .x3 .x1 3, .movz .x .x4 7 0,
      .logic .and .x .x1 .x1 .x4]) u fun v =>
      Inv s₀ (128 * (n / 128)) v ∧
      v.gpr .x3 = BitVec.ofNat 64 ((n % 128) / 8) ∧
      v.gpr .x1 = BitVec.ofNat 64 (n % 8) := by
    have hu' : Inv s₀ (128 * (n / 128)) u := by simpa using hu.1
    have hsmall : (BitVec.ofNat 64 (n % 128)).toNat = n % 128 := by simp; omega_arith
    crun [Inv, hsu, hs, count, tail, hsmall,
      (show BitVec.setWidth 64 (7#16) = (7 : BitVec 64) from rfl)]
    refine ⟨hu', ?_⟩
    have hh := tail (BitVec.ofNat 64 (n % 128))
    rw [hsmall] at hh
    have he : n % 128 % 8 = n % 8 := by omega_arith
    simpa only [he, BitVec.ofNat_eq_ofNat] using hh
  refine WP.seq (WP.mono mid fun v ⟨hv, hcv, hsv⟩ => ?_)
  refine WP.seq (WP.mono (loop_ok true s₀ v hp (128 * (n / 128)) ((n % 128) / 8)
    (by dsimp [n]; omega_arith) hv hcv) fun w ⟨hw, hsw⟩ => ?_)
  have last : WP isa (.block [.addImm .x .x3 .x1 0]) w fun z =>
      Inv s₀ (128 * (n / 128) + 8 * ((n % 128) / 8)) z ∧
      z.gpr .x3 = BitVec.ofNat 64 (n % 8) := by
    crun [Inv, hsw, hsv]
    exact hw
  refine WP.seq (WP.mono last fun z ⟨hz, hcz⟩ => ?_)
  refine WP.mono (loop_ok false s₀ z hp _ (n % 8) (by dsimp [n]; omega_arith) hz hcz)
    fun w ⟨hw, _⟩ => ?_
  have hn : 128 * (n / 128) + 8 * ((n % 128) / 8) + (if false then 8 else 1) * (n % 8) = n := by
    simp; omega_arith
  rw [hn] at hw
  exact ⟨prefix_spec hw.2.2.2.1, hw.2.2.2.2⟩

/-- It never touches PSTATE.DIT, so its callers' runs need not agree on it
(`Contract.ditFree`). -/
theorem wide_noDit : zeroizeWide.all (fun i => !i.touchesDit) = true := by decide

theorem wideVerified : Verified target zeroizeWide (Spec.Zeroize.zeroizeContract abi) := by
  apply Verified.of_correct (k := contract)
  · intro s hp
    obtain ⟨tr, t, he, ho, _⟩ := wideCorrect s hp
    refine ⟨tr, t, he, ⟨?_, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, ho⟩
    intro r hr
    have hc := instrs_keeps (c := zeroizeWide) (rs := preserved) (by decide +kernel)
    apply Exec.gpr (fun i hi => ?_) he
    simpa using List.all_eq_true.mp (List.all_eq_true.mp hc i hi) r hr
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1]) ?_ (by taint_decide)
    intro s t _ _ h
    refine ⟨h.2.2, ?_⟩
    intro r hr
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1
    · exact h.2.1
  · sig_implies [Spec.Zeroize.zeroizeContract, Spec.Zeroize.zeroizeSig, contract, abi, argRegs] [sat] using sat

/-- `vg_zeroize` returns without secret residue: it reads no memory, so what
it leaves is a function of its arguments (`Residue.noResidue_of_blind`). -/
theorem wide_noResidue (k : Contract isa) (r : Nat) : NoResidue zeroizeWide k r :=
  Residue.noResidue_of_blind (by decide) k r

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Zeroize.AArch64.wide_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Zeroize.AArch64.zeroizeWide
      (Spec.Zeroize.zeroizeContract AArch64.abi) 0 :=
  ⟨Proof.Zeroize.AArch64.wideVerified,
    Proof.Zeroize.AArch64.wide_noResidue _ _⟩

end VG.Proof.Zeroize.AArch64
