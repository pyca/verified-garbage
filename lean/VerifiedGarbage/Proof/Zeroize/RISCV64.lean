module

public import VerifiedGarbage.Impl.Zeroize.RISCV64
meta import VerifiedGarbage.Impl.Zeroize.RISCV64
public import VerifiedGarbage.Proof.Zeroize.Common
meta import VerifiedGarbage.Proof.Zeroize.Common
public import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
meta import VerifiedGarbage.Proof.Framework.RISCV64.Inline
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Zeroize.Contract
meta import VerifiedGarbage.Spec.Zeroize.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import all Init.Data.Nat.Bitwise.Basic

/-!
# Zeroization on RISC-V

Untrusted: everything here is checked by Lean. The structure of the PPC64LE
proof (`VG.Proof.Zeroize.PPC64LE`), with a byte loop first up to the first
8-byte aligned address, so that the doubleword stores are aligned.
-/

@[expose] public section

namespace VG.Proof.Zeroize.RISCV64
open VG VG.RISCV64 VG.Impl.Zeroize.RISCV64

def contract : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .a0, (s.gpr .a1).toNat⟩]
  post s t := Spec.Zeroize.bytesAt t.mem (s.gpr .a0) (s.gpr .a1).toNat =
    Spec.Zeroize.zeros (s.gpr .a1).toNat
  pub s t := s.gpr .a0 = t.gpr .a0 ∧ s.gpr .a1 = t.gpr .a1 ∧ s.sp = t.sp

def Inv (s₀ : State) (i : Nat) (s : State) : Prop :=
  s.wr = s₀.wr ∧ s.gpr .t0 = 0 ∧ s.gpr .a0 = s₀.gpr .a0 + BitVec.ofNat 64 i ∧
  Prefix s.mem (s₀.gpr .a0) i ∧ Frame s₀.wr s₀.mem s.mem

/-- The size of a step's store. -/
abbrev sz (word : Bool) : Nat := if word then 8 else 1

theorem step_ok (word : Bool) (s₀ s : State) (hp : contract.pre s₀) (i : Nat)
    (hi : i + sz word ≤ (s₀.gpr .a1).toNat)
    (hal : word = true → (s₀.gpr .a0 + BitVec.ofNat 64 i).toNat % 8 = 0) (h : Inv s₀ i s) :
    WP isa (.block (step word)) s fun t =>
      Inv s₀ (i + sz word) t ∧ t.gpr .t1 = s.gpr .t1 - 1 ∧ t.gpr .a1 = s.gpr .a1 := by
  obtain ⟨hw, ha, hd, hz, hf⟩ := h
  have hn := (s₀.gpr .a1).isLt
  have hc : (⟨s₀.gpr .a0, (s₀.gpr .a1).toNat⟩ : Region).Contains
      (s₀.gpr .a0 + BitVec.ofNat 64 i) (sz word) :=
    Offset.contains_base _ hi (by cases word <;> simp_all <;> omega)
  have hs : InRegions s.wr (s₀.gpr .a0 + BitVec.ofNat 64 i) (sz word) :=
    ⟨_, by rw [hw, hp.2]; simp, hc⟩
  have hmem := List.mem_singleton_self (⟨s₀.gpr .a0, (s₀.gpr .a1).toNat⟩ : Region)
  rw [← hp.2] at hmem
  rw [hw] at hs
  have hadd (k : Nat) : s₀.gpr .a0 + BitVec.ofNat 64 i + BitVec.ofNat 64 k =
      s₀.gpr .a0 + BitVec.ofNat 64 (i + k) := by rw [BitVec.add_assoc, BitVec.ofNat_add]
  cases word
  · simp only [sz, Bool.false_eq_true, ↓reduceIte] at hi hc hs ⊢
    unfold step
    crun [hd, ha, hs, hw, Inv]
    exact ⟨hadd 1, by rw [show BitVec.setWidth 8 (0#64) = (0 : BitVec (8 * 1)) from rfl]; exact prefix_write hz (by omega),
      hf.write hmem _ hc⟩
  · simp only [sz, ↓reduceIte] at hi hc hs ⊢
    have hal := hal rfl
    unfold step
    crun [hd, ha, hs, hw, Inv, hal]
    exact ⟨hadd 8, prefix_write hz (by omega), hf.write hmem _ hc⟩

theorem aligned_step {x : BitVec 64} (h : x.toNat % 8 = 0) (j : Nat) :
    (x + BitVec.ofNat 64 (8 * j)).toNat % 8 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem loop_ok (word : Bool) (s₀ s : State) (hp : contract.pre s₀) (i n : Nat)
    (hn : i + sz word * n ≤ (s₀.gpr .a1).toNat)
    (hal : word = true → 0 < n → (s₀.gpr .a0 + BitVec.ofNat 64 i).toNat % 8 = 0)
    (h : Inv s₀ i s) (hc : s.gpr .t1 = BitVec.ofNat 64 n) :
    WP isa (loop word) s fun t => Inv s₀ (i + sz word * n) t ∧ t.gpr .a1 = s.gpr .a1 := by
  have hlt : n < 2 ^ 64 := by
    have := (s₀.gpr .a1).isLt
    cases word <;> simp only [sz, ↓reduceIte, Bool.false_eq_true] at hn <;> omega
  unfold loop
  by_cases he : n = 0
  · subst n
    refine WP.ite true (by simp [VG.RISCV64.eval, hc]) (fun _ => WP.block_nil ?_) (by simp)
    simpa only [Nat.mul_zero, Nat.add_zero] using And.intro h (rfl : s.gpr .a1 = s.gpr .a1)
  · have hne : BitVec.ofNat 64 n ≠ (0 : BitVec 64) := by bv_omega
    refine WP.ite false (by simp only [VG.RISCV64.eval, hc, beq_eq_false_iff_ne.mpr hne]) (by simp)
      (fun _ => ?_)
    refine WP.loop (M := isa) (fun rem t => ∃ j, j < n ∧ rem = n - j ∧
      Inv s₀ (i + sz word * j) t ∧ t.gpr .t1 = BitVec.ofNat 64 (n-j) ∧
      t.gpr .a1 = s.gpr .a1) ?_ n s ?_
    · intro rem t ⟨j, hj, hr, ht, hct, hst⟩
      have hal' : word = true → (s₀.gpr .a0 + BitVec.ofNat 64 (i + sz word * j)).toNat % 8 = 0 := by
        intro hw; subst hw
        rw [BitVec.ofNat_add, ← BitVec.add_assoc]
        exact aligned_step (hal rfl (by omega)) j
      refine WP.mono (step_ok word s₀ t hp _ ?_ hal' ht) fun u ⟨hu, hcu, hsu⟩ => ?_
      · cases word <;> simp only [sz, ↓reduceIte, Bool.false_eq_true] at hn ⊢ <;> omega
      have hpred : BitVec.ofNat 64 (n-j) - 1 = BitVec.ofNat 64 (n-(j+1)) := by bv_omega
      rw [hct, hpred] at hcu
      have hoff : i + sz word * j + sz word = i + sz word * (j+1) := by
        rw [Nat.mul_succ, Nat.add_assoc]
      rw [hoff] at hu
      by_cases hend : j + 1 = n
      · left
        refine ⟨by simp [VG.RISCV64.eval, hcu, hend], ?_⟩
        rw [hend] at hu
        exact ⟨hu, hsu.trans hst⟩
      · right
        have hnz : BitVec.ofNat 64 (n-(j+1)) ≠ (0 : BitVec 64) := by bv_omega
        refine ⟨by simp only [VG.RISCV64.eval, hcu, bne, beq_eq_false_iff_ne.mpr hnz]; rfl,
          n-(j+1), by omega, j+1, by omega, rfl, hu, hcu, hsu.trans hst⟩
    · exact ⟨0, by omega, by omega, by simpa using h, by simpa using hc, rfl⟩

/-- The bytes before the first 8-byte aligned address at or after `p`. -/
def headLen (p : BitVec 64) : Nat := (2 ^ 64 - p.toNat) % 8

theorem neg_and7 (p : BitVec 64) : (0 - p) &&& 7 = BitVec.ofNat 64 (headLen p) := by
  rw [tail]
  congr 1
  rw [BitVec.toNat_sub, show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero]
  unfold headLen
  have := p.isLt
  omega

/-- `neg_and7` and `tail` with the literals `crun` leaves. -/
theorem neg_and7' (p : BitVec 64) :
    BitVec.ofNat 64 0 - p &&& BitVec.ofNat 64 7 = BitVec.ofNat 64 (headLen p) := neg_and7 p

theorem tail' (x : BitVec 64) : x &&& BitVec.ofNat 64 7 = BitVec.ofNat 64 (x.toNat % 8) := tail x

theorem headLen_aligned (p : BitVec 64) : (p + BitVec.ofNat 64 (headLen p)).toNat % 8 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  unfold headLen
  have := p.isLt
  omega

theorem head_ok (s₀ : State) :
    WP isa head s₀ fun t =>
      Inv s₀ 0 t ∧ t.gpr .t1 = BitVec.ofNat 64 (min (s₀.gpr .a1).toNat (headLen (s₀.gpr .a0))) ∧
      t.gpr .a1 = BitVec.ofNat 64 ((s₀.gpr .a1).toNat - min (s₀.gpr .a1).toNat (headLen (s₀.gpr .a0))) := by
  let L := (s₀.gpr .a1).toNat
  let H := headLen (s₀.gpr .a0)
  have hH : H < 8 := Nat.mod_lt _ (by decide)
  have hL := (s₀.gpr .a1).isLt
  unfold head
  refine WP.seq ?_
  refine WP.mono (Q := fun (t : State) => Inv s₀ 0 t ∧ t.gpr .t1 = BitVec.ofNat 64 H ∧
    t.gpr .a1 = s₀.gpr .a1 ∧ t.gpr .t2 = if s₀.gpr .a1 < BitVec.ofNat 64 H then 1 else 0) ?_
    fun (t : State) ⟨ht, h1, ha1, h2⟩ => ?_
  · crun [Inv, Prefix]
    exact ⟨⟨by omega, Frame.refl _ _⟩, neg_and7' _, by rw [neg_and7']⟩
  · refine WP.seq ?_
    by_cases hlt : L < H
    · have hlt' : s₀.gpr .a1 < BitVec.ofNat 64 H := by
        rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hlt
      refine WP.ite true (by simp [VG.RISCV64.eval, h2, hlt']) (fun _ => ?_) (by simp)
      refine WP.mono (Q := fun (u : State) => Inv s₀ 0 u ∧ u.gpr .t1 = s₀.gpr .a1 ∧ u.gpr .a1 = s₀.gpr .a1) ?_
        fun (u : State) ⟨hu, h1u, hau⟩ => ?_
      · obtain ⟨hw, ht0, ha0, hz, hf⟩ := ht
        crun [ha1, Inv, hw, ht0, ha0, hz, hf]
      · obtain ⟨hw, ht0, ha0, hz, hf⟩ := hu
        crun [h1u, hau, Inv, hw, ht0, ha0, hz, hf, BitVec.sub_self]
        refine ⟨?_, ?_⟩
        · rw [Nat.min_eq_left (by omega)]; simp
        · rw [Nat.min_eq_left (by omega), Nat.sub_self]
    · have hge : ¬ s₀.gpr .a1 < BitVec.ofNat 64 H := by
        rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hlt
      refine WP.ite false (by simp [VG.RISCV64.eval, h2, hge]) (by simp) (fun _ => ?_)
      refine WP.block_nil ?_
      obtain ⟨hw, ht0, ha0, hz, hf⟩ := ht
      crun [h1, ha1, Inv, hw, ht0, ha0, hz, hf]
      refine ⟨?_, ?_⟩
      · rw [Nat.min_eq_right (by omega)]
      · rw [Nat.min_eq_right (by omega)]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := H) (by omega)]
        omega

theorem correct (s₀ : State) (hp : contract.pre s₀) :
    WP isa zeroize s₀ fun t => contract.post s₀ t ∧ Frame s₀.wr s₀.mem t.mem := by
  let n := (s₀.gpr .a1).toNat
  let h := min n (headLen (s₀.gpr .a0))
  have hn := (s₀.gpr .a1).isLt
  unfold zeroize
  refine WP.seq (WP.mono (head_ok s₀) fun t ⟨ht, hc, hs⟩ => ?_)
  refine WP.seq (WP.mono (loop_ok false s₀ t hp 0 h (by simp [sz]; omega) (by simp) ht hc)
    fun u ⟨hu, hsu⟩ => ?_)
  simp only [sz, Bool.false_eq_true, ↓reduceIte, Nat.one_mul, Nat.zero_add] at hu
  have mid : WP isa (.block [.shift .srl .d .t1 .a1 3, .logicImm .and .a1 .a1 7]) u fun v =>
      Inv s₀ h v ∧ v.gpr .t1 = BitVec.ofNat 64 ((n - h) / 8) ∧
      v.gpr .a1 = BitVec.ofNat 64 ((n - h) % 8) := by
    obtain ⟨hw, ht0, ha0, hz, hf⟩ := hu
    crun [hsu, hs, count, tail]
    refine ⟨⟨hw, ht0, ha0, hz, hf⟩, ?_, ?_⟩
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · rw [tail', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := n - h) (by omega)]
  refine WP.seq (WP.mono mid fun v ⟨hv, hcv, hav⟩ => ?_)
  have hal : true = true → 0 < (n - h) / 8 → (s₀.gpr .a0 + BitVec.ofNat 64 h).toNat % 8 = 0 := by
    intro _ hpos
    have : h = headLen (s₀.gpr .a0) := Nat.min_eq_right (by
      have : headLen (s₀.gpr .a0) < 8 := Nat.mod_lt _ (by decide)
      omega)
    rw [this]; exact headLen_aligned _
  refine WP.seq (WP.mono (loop_ok true s₀ v hp h ((n - h) / 8) (by simp [sz]; omega) hal hv hcv)
    fun w ⟨hw, haw⟩ => ?_)
  simp only [sz, ↓reduceIte] at hw
  have tailp : WP isa (.block [.addi .t1 .a1 0]) w fun x =>
      Inv s₀ (h + 8 * ((n - h) / 8)) x ∧ x.gpr .t1 = BitVec.ofNat 64 ((n - h) % 8) := by
    obtain ⟨hw', ht0, ha0, hz, hf⟩ := hw
    crun [haw, hav]
    exact ⟨hw', ht0, ha0, hz, hf⟩
  refine WP.seq (WP.mono tailp fun x ⟨hx, hcx⟩ => ?_)
  refine WP.mono (loop_ok false s₀ x hp _ ((n - h) % 8) (by simp [sz]; omega) (by simp) hx hcx)
    fun y ⟨hy, _⟩ => ?_
  have he : h + 8 * ((n - h) / 8) + sz false * ((n - h) % 8) = n := by simp [sz]; omega
  rw [he] at hy
  exact ⟨prefix_spec hy.2.2.2.1, hy.2.2.2.2⟩

def sat : State where
  gpr _ := 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0, 0⟩]

theorem verified : Verified target zeroize (Spec.Zeroize.zeroizeContract abi) := by
  apply Verified.of_correct (k := contract)
  · intro s hp
    obtain ⟨tr, t, he, ho, _⟩ := correct s hp
    refine ⟨tr, t, he, ⟨?_, Exec.sp he, Exec.gpr (fun i hi => ?_) he⟩, ho⟩
    · intro r hr
      have hc : ((instrs zeroize).all fun i => preserved.all fun r => dstOf i != some r) = true := by
        rw [← Code.allInstrs_eq]; decide +kernel
      apply Exec.gpr (fun i hi => ?_) he
      simpa using List.all_eq_true.mp (List.all_eq_true.mp hc i hi) r hr
    · have hc : ((instrs zeroize).all fun i => dstOf i != some .ra) = true := by
        rw [← Code.allInstrs_eq]; decide +kernel
      simpa using List.all_eq_true.mp hc i hi
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1]) ?_ (by taint_decide)
    intro s t _ _ h
    refine ⟨h.2.2, ?_⟩
    intro r hr
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1
    · exact h.2.1
  · sig_implies [Spec.Zeroize.zeroizeContract, Spec.Zeroize.zeroizeSig, contract, abi, argRegs]
      [sat] using sat

end VG.Proof.Zeroize.RISCV64
