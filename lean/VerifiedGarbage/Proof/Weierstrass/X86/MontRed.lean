module

public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Impl.Mont.X86.Sparse
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.TCB.X86.Isa
import VerifiedGarbage.TCB.X86.State
public import VerifiedGarbage.Proof.Weierstrass.X86.MontBase
import VerifiedGarbage.Proof.Mont.X86.Row
import VerifiedGarbage.Proof.Mont.X86.Chain
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! ### `Mont.X86.SparseChain`, which only this module used -/

section

/-! # Carry and borrow chains for sparse x86 reduction -/

@[expose] public section

namespace VG.Proof.Mont.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Proof.Mont

theorem sparseChain_succ (acc : Nat) (op op' : AluOp) (k : Nat) :
    sparseChain acc op op' (k + 1) = sparseChain acc op op' k ++
      sparseStep acc k (if k = 0 then op else op') (k == 0) := by
  simp only [sparseChain, List.range_succ, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

def multiWeight (useQ : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => multiWeight useQ k + if useQ k then 2 ^ (32 * k) else 0

theorem multiChain_succ (acc : Nat) (useQ : Nat → Bool) (k : Nat) :
    multiChain acc useQ (k + 1) = multiChain acc useQ k ++
      sparseStep acc k (if k = 0 then .add else .adc) (useQ k) := by
  simp only [multiChain, List.range_succ, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

end VG.Proof.Mont.X86

end

end


/-!
# Montgomery arithmetic as functions on x86 (32-bit): P-256's sparse reduction

`p256Red acc` (`Impl/Mont/X86/Sparse.lean`) on the window at `[ebp + acc]`,
the working space at `ebp` (`Bx`): the proofs of `Proof/Mont/X86/P256Red.lean`
and the chains it is built from, for the window addressed from `ebp`.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.Mont

open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Mont
open VG.Proof.Mont VG.Proof.Mont.X86


/-- A word of an addition, with the carry in `cin` (none for `add`). -/
theorem sparseStepAddB_ok {s : State} {base : Addr} {size : Nat} (hb : Bx s base size) {op : AluOp} {cin : Bool}
    (hop : (op = .add ∧ cin = false) ∨ (op = .adc ∧ s.cf = some cin)) {acc j : Nat} (first : Bool)
    (hacc : acc + 4 * j + 4 ≤ size) :
    WP isa (.block (sparseStep acc j op first)) s fun u =>
      Outside base (acc + 4 * j) 4 s.mem u.mem ∧
      (∃ c, u.cf = some c ∧ w32 u.mem base (acc + 4 * j) + 2 ^ 32 * c.toNat =
        w32 s.mem base (acc + 4 * j) + (if first then (s.gpr .ecx).toNat else 0) + cin.toNat) ∧
      Keeps [.eax] s u := by
  have hn := hb.nowrap
  simp only [sparseStep]
  refine wp_movS (readSrc_bp hb hacc) fun s₁ u₁ cf₁ => ?_
  have hb₁ := hb.of_keeps u₁.keeps (by decide)
  have hx := (s.mem.readW (off base (acc + 4 * j)) 32).isLt
  have hv : readSrc s₁ (if first then .reg .ecx else .imm 0) = some (if first then s.gpr .ecx else 0) := by
    cases first <;> simp only [Bool.false_eq_true, ite_false, ite_true, readSrc]
    exact congrArg some (u₁.other _ (by decide))
  have hy := (s.gpr .ecx).isLt
  rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, hc⟩
  · refine wp_addS hv fun s₂ u₂ c₂ => ?_
    have hb₂ := hb₁.of_keeps u₂.keeps (by decide)
    refine wp_storeS (hb₂.ea (d := acc + 4 * j) (by omega_arith)) (hb₂.write (n := 4) (by omega_arith))
      fun s₃ m₃ => WP.block_nil ⟨?_, ⟨_, by rw [m₃.cf, c₂], ?_⟩, (u₁.keeps.trans (u₂.keeps)).trans (m₃.keeps _)⟩
    · rw [m₃.mem, u₂.mem, u₁.mem]; exact writeW32_outside _ _ _ (by omega_arith)
    · rw [m₃.mem, w32_write_self, u₂.gpr, BitVec.toNat_add, u₁.gpr]
      simp only [w32]
      have hvn : (if first then s.gpr .ecx else (0 : BitVec 32)).toNat = (if first then (s.gpr .ecx).toNat else 0) := by cases first <;> rfl
      rw [hvn]
      have hy' : (if first then (s.gpr .ecx).toNat else 0) < 2 ^ 32 := by cases first <;> simp_all
      by_cases h : 2 ^ 32 ≤ (s.mem.readW (off base (acc + 4 * j)) 32).toNat +
          (if first then (s.gpr .ecx).toNat else 0) <;>
        simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega_arith
  · refine wp_adcS hv (by rw [cf₁]; exact hc) fun s₂ u₂ c₂ => ?_
    have hb₂ := hb₁.of_keeps u₂.keeps (by decide)
    refine wp_storeS (hb₂.ea (d := acc + 4 * j) (by omega_arith)) (hb₂.write (n := 4) (by omega_arith))
      fun s₃ m₃ => WP.block_nil ⟨?_, ⟨_, by rw [m₃.cf, c₂], ?_⟩, (u₁.keeps.trans (u₂.keeps)).trans (m₃.keeps _)⟩
    · rw [m₃.mem, u₂.mem, u₁.mem]; exact writeW32_outside _ _ _ (by omega_arith)
    · rw [m₃.mem, w32_write_self, u₂.gpr, add3_toNat, u₁.gpr]
      simp only [w32]
      have := Bool.toNat_le cin
      have hvn : (if first then s.gpr .ecx else (0 : BitVec 32)).toNat = (if first then (s.gpr .ecx).toNat else 0) := by cases first <;> rfl
      rw [hvn]
      have hy' : (if first then (s.gpr .ecx).toNat else 0) < 2 ^ 32 := by cases first <;> simp_all
      by_cases h : 2 ^ 32 ≤ (s.mem.readW (off base (acc + 4 * j)) 32).toNat +
          (if first then (s.gpr .ecx).toNat else 0) + cin.toNat <;>
        simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega_arith

/-- A word of a subtraction, with the borrow in `cin` (none for `sub`). -/
theorem sparseStepSubB_ok {s : State} {base : Addr} {size : Nat} (hb : Bx s base size) {op : AluOp} {cin : Bool}
    (hop : (op = .sub ∧ cin = false) ∨ (op = .sbb ∧ s.cf = some cin)) {acc j : Nat} (first : Bool)
    (hacc : acc + 4 * j + 4 ≤ size) :
    WP isa (.block (sparseStep acc j op first)) s fun u =>
      Outside base (acc + 4 * j) 4 s.mem u.mem ∧
      (∃ c, u.cf = some c ∧ w32 u.mem base (acc + 4 * j) + (if first then (s.gpr .ecx).toNat else 0) + cin.toNat =
        w32 s.mem base (acc + 4 * j) + 2 ^ 32 * c.toNat) ∧
      Keeps [.eax] s u := by
  have hn := hb.nowrap
  simp only [sparseStep]
  refine wp_movS (readSrc_bp hb hacc) fun s₁ u₁ cf₁ => ?_
  have hb₁ := hb.of_keeps u₁.keeps (by decide)
  have hx := (s.mem.readW (off base (acc + 4 * j)) 32).isLt
  have hv : readSrc s₁ (if first then .reg .ecx else .imm 0) = some (if first then s.gpr .ecx else 0) := by
    cases first <;> simp only [Bool.false_eq_true, ite_false, ite_true, readSrc]
    exact congrArg some (u₁.other _ (by decide))
  have hy := (s.gpr .ecx).isLt
  rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, hc⟩
  · refine wp_subS hv fun s₂ u₂ c₂ => ?_
    have hb₂ := hb₁.of_keeps u₂.keeps (by decide)
    refine wp_storeS (hb₂.ea (d := acc + 4 * j) (by omega_arith)) (hb₂.write (n := 4) (by omega_arith))
      fun s₃ m₃ => WP.block_nil ⟨?_, ⟨_, by rw [m₃.cf, c₂], ?_⟩, (u₁.keeps.trans (u₂.keeps)).trans (m₃.keeps _)⟩
    · rw [m₃.mem, u₂.mem, u₁.mem]; exact writeW32_outside _ _ _ (by omega_arith)
    · rw [m₃.mem, w32_write_self, u₂.gpr, sub_toNat, u₁.gpr]
      simp only [w32]
      have hvn : (if first then s.gpr .ecx else (0 : BitVec 32)).toNat = (if first then (s.gpr .ecx).toNat else 0) := by cases first <;> rfl
      rw [hvn]
      have hy' : (if first then (s.gpr .ecx).toNat else 0) < 2 ^ 32 := by cases first <;> simp_all
      by_cases h : (s.mem.readW (off base (acc + 4 * j)) 32).toNat <
          (if first then (s.gpr .ecx).toNat else 0) <;>
        simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega_arith
  · refine wp_sbbS hv (by rw [cf₁]; exact hc) fun s₂ u₂ c₂ => ?_
    have hb₂ := hb₁.of_keeps u₂.keeps (by decide)
    refine wp_storeS (hb₂.ea (d := acc + 4 * j) (by omega_arith)) (hb₂.write (n := 4) (by omega_arith))
      fun s₃ m₃ => WP.block_nil ⟨?_, ⟨_, by rw [m₃.cf, c₂], ?_⟩, (u₁.keeps.trans (u₂.keeps)).trans (m₃.keeps _)⟩
    · rw [m₃.mem, u₂.mem, u₁.mem]; exact writeW32_outside _ _ _ (by omega_arith)
    · rw [m₃.mem, w32_write_self, u₂.gpr, sub3_toNat, u₁.gpr]
      simp only [w32]
      have := Bool.toNat_le cin
      have hvn : (if first then s.gpr .ecx else (0 : BitVec 32)).toNat = (if first then (s.gpr .ecx).toNat else 0) := by cases first <;> rfl
      rw [hvn]
      have hy' : (if first then (s.gpr .ecx).toNat else 0) < 2 ^ 32 := by cases first <;> simp_all
      by_cases h : (s.mem.readW (off base (acc + 4 * j)) 32).toNat <
          (if first then (s.gpr .ecx).toNat else 0) + cin.toNat <;>
        simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega_arith



theorem multiChainB_ok {s : State} {base : Addr} {size : Nat} (hb : Bx s base size)
    {acc w : Nat}
    (hw : acc = w) (useQ : Nat → Bool) :
    ∀ k, w + 4 * (k + 1) ≤ size →
    WP isa (.block (multiChain acc useQ (k + 1))) s fun u =>
      Outside base w (4 * (k + 1)) s.mem u.mem ∧
      (∃ c, u.cf = some c ∧ val32 u.mem base w (k + 1) + 2 ^ (32 * (k + 1)) * c.toNat =
        val32 s.mem base w (k + 1) + (s.gpr .ecx).toNat * multiWeight useQ (k + 1)) ∧ Keeps [.eax] s u
  | 0, hsz => by
    change WP isa (.block (sparseStep acc 0 .add (useQ 0))) s _
    refine WP.mono (sparseStepAddB_ok hb (.inl ⟨rfl, rfl⟩) (useQ 0) (j := 0) (by omega_arith))
      fun u ⟨O, ⟨c, hc, V⟩, K⟩ => ?_
    simp only [Nat.mul_zero, Nat.add_zero, hw, Bool.toNat_false] at O V
    refine ⟨O, ⟨c, hc, ?_⟩, K⟩
    simp only [val32, Nat.mul_zero, Nat.add_zero, multiWeight, Nat.pow_zero, Nat.zero_add]
    cases h : useQ 0 <;> simp only [h, Bool.false_eq_true, ite_false, ite_true, Nat.mul_zero, Nat.mul_one] at V ⊢ <;> exact V
  | k + 1, hsz => by
    have hn := hb.nowrap
    rw [multiChain_succ]
    simp only [Nat.add_one_ne_zero, ite_false]
    refine WP.block_append (WP.mono (multiChainB_ok hb hw useQ k (by omega_arith))
      fun s₁ ⟨O₁, ⟨c₁, hc₁, V₁⟩, K₁⟩ => ?_)
    have hb₁ := hb.of_keeps K₁ (by decide)
    refine WP.mono (sparseStepAddB_ok hb₁ (.inr ⟨rfl, hc₁⟩) (useQ (k + 1)) (j := k + 1) (by omega_arith))
      fun u ⟨O, ⟨c, hc, V⟩, K⟩ => ?_
    have he : acc + 4 * (k + 1) = w + 4 * (k + 1) := by omega_arith
    rw [he] at O V
    rw [O₁.w32 (by omega_arith) (by omega_arith), K₁.1 .ecx (by decide)] at V
    refine ⟨(O₁.mono (Nat.le_refl _) (by omega_arith)).trans (O.mono (by omega_arith) (by omega_arith)),
      ⟨c, hc, ?_⟩, K₁.trans K⟩
    rw [val32_succ u.mem, val32_succ s.mem, O.val32 (by omega_arith) (by omega_arith), pow32_succ (k + 1), multiWeight]
    generalize 2 ^ (32 * (k + 1)) = P at *
    cases h : useQ (k + 1) <;> simp only [h, Bool.false_eq_true, ite_false, ite_true] at V ⊢ <;> grind


theorem sparseChainSubB_ok {s : State} {base : Addr} {size : Nat} (hb : Bx s base size)
    {acc w : Nat}
    (hw : acc = w) :
    ∀ k, w + 4 * (k + 1) ≤ size →
    WP isa (.block (sparseChain acc .sub .sbb (k + 1))) s fun u =>
      Outside base w (4 * (k + 1)) s.mem u.mem ∧
      (∃ c, u.cf = some c ∧ val32 u.mem base w (k + 1) + (s.gpr .ecx).toNat =
        val32 s.mem base w (k + 1) + 2 ^ (32 * (k + 1)) * c.toNat) ∧ Keeps [.eax] s u
  | 0, hsz => by
    change WP isa (.block (sparseStep acc 0 .sub true)) s _
    refine WP.mono (sparseStepSubB_ok hb (.inl ⟨rfl, rfl⟩) true (j := 0) (by omega_arith))
      fun u ⟨O, ⟨c, hc, V⟩, K⟩ => ?_
    simp only [Nat.mul_zero, Nat.add_zero, hw, ite_true, Bool.toNat_false] at O V
    refine ⟨O, ⟨c, hc, ?_⟩, K⟩
    simpa only [val32, Nat.mul_zero, Nat.add_zero] using V
  | k + 1, hsz => by
    have hn := hb.nowrap
    rw [sparseChain_succ]
    simp only [Nat.add_one_ne_zero, ite_false, beq_eq_false_iff_ne.mpr (Nat.add_one_ne_zero k)]
    refine WP.block_append (WP.mono (sparseChainSubB_ok hb hw k (by omega_arith))
      fun s₁ ⟨O₁, ⟨c₁, hc₁, V₁⟩, K₁⟩ => ?_)
    have hb₁ := hb.of_keeps K₁ (by decide)
    refine WP.mono (sparseStepSubB_ok hb₁ (.inr ⟨rfl, hc₁⟩) false (j := k + 1) (by omega_arith))
      fun u ⟨O, ⟨c, hc, V⟩, K⟩ => ?_
    have he : acc + 4 * (k + 1) = w + 4 * (k + 1) := by omega_arith
    rw [he] at O V
    simp only [Bool.false_eq_true, ite_false, Nat.add_zero] at V
    rw [O₁.w32 (by omega_arith) (by omega_arith)] at V
    refine ⟨(O₁.mono (Nat.le_refl _) (by omega_arith)).trans (O.mono (by omega_arith) (by omega_arith)),
      ⟨c, hc, ?_⟩, K₁.trans K⟩
    rw [val32_succ u.mem, val32_succ s.mem, O.val32 (by omega_arith) (by omega_arith), pow32_succ (k + 1)]
    generalize 2 ^ (32 * (k + 1)) = P at *
    grind


theorem positiveB_ok {s : State} {base : Addr} {size : Nat} (hb : Bx s base size)
    {acc w : Nat}
    (hw : acc = w) (hsz : w + 40 ≤ size) :
    WP isa (.block (multiChain (acc + 12) positiveMask 7)) s fun u =>
      Outside base w 40 s.mem u.mem ∧
      (∃ c : Bool, val32 u.mem base w 10 + 2 ^ 320 * c.toNat =
        val32 s.mem base w 10 + (s.gpr .ecx).toNat * (2 ^ 96 + 2 ^ 192 + 2 ^ 256)) ∧ Keeps [.eax] s u := by
  have hn := hb.nowrap
  refine WP.mono (multiChainB_ok hb (w := w + 12) (by omega_arith) positiveMask 6 (by omega_arith))
    fun u ⟨O, ⟨c, _, V⟩, K⟩ => ⟨O.mono (by omega_arith) (by omega_arith), ⟨c, ?_⟩, K⟩
  have hv : multiWeight positiveMask 7 = 1 + 2 ^ 96 + 2 ^ 160 := by decide +kernel
  rw [hv] at V
  rw [show 10 = 3 + 7 from rfl, val32_append u.mem base w 3 7, val32_append s.mem base w 3 7,
    O.val32 (d := w) (k := 3) (by omega_arith) (by omega_arith)]
  simp only [Nat.reduceMul, Nat.reduceAdd] at V ⊢
  omega_arith

theorem sparseShiftSubB_ok {s : State} {base : Addr} {size : Nat} (hb : Bx s base size)
    {acc w j k N : Nat}
    (hw : acc = w) (hN : N = j + (k + 1)) (hsz : w + 4 * N ≤ size) :
    WP isa (.block (sparseChain (acc + 4 * j) .sub .sbb (k + 1))) s fun u =>
      Outside base w (4 * N) s.mem u.mem ∧
      (∃ c : Bool, val32 u.mem base w N + 2 ^ (32 * j) * (s.gpr .ecx).toNat =
        val32 s.mem base w N + 2 ^ (32 * N) * c.toNat) ∧ Keeps [.eax] s u := by
  have hn := hb.nowrap
  refine WP.mono (sparseChainSubB_ok hb (w := w + 4 * j) (by omega_arith) k (by omega_arith))
    fun u ⟨O, ⟨c, _, V⟩, K⟩ => ⟨O.mono (by omega_arith) (by omega_arith), ⟨c, ?_⟩, K⟩
  rw [hN, val32_append u.mem base w j (k + 1), val32_append s.mem base w j (k + 1), O.val32 (d := w) (k := j) (by omega_arith) (by omega_arith), pow32_add]
  generalize 2 ^ (32 * j) = P at *
  generalize 2 ^ (32 * (k + 1)) = Q at *
  grind


/-- Clearing the low word subtracts exactly that word. -/
theorem clearLowB_ok {s : State} {base : Addr} {size : Nat} (hb : Bx s base size)
    {acc w : Nat}
    (hw : acc = w) (hsz : w + 40 ≤ size) :
    WP isa (.block [.mov .eax (.imm 0), .store { base := .ebp, disp := acc } .eax]) s fun u =>
      Outside base w 40 s.mem u.mem ∧
      val32 u.mem base w 10 + w32 s.mem base w = val32 s.mem base w 10 ∧ Keeps [.eax] s u := by
  have hn := hb.nowrap
  refine wp_movS rfl fun s₁ u₁ _ => ?_
  have hb₁ := hb.of_keeps u₁.keeps (by decide)
  refine wp_storeS (hb₁.ea (d := acc) (by omega_arith)) (hb₁.write (n := 4) (by omega_arith))
    fun u m => WP.block_nil ?_
  have hm : u.mem = s.mem.writeW (off base w) (0 : BitVec 32) := by rw [m.mem, u₁.mem, u₁.gpr, hw]
  have O := writeW32_outside s.mem base (d := w) (0 : BitVec 32) (by omega_arith)
  rw [← hm] at O
  refine ⟨O.mono (Nat.le_refl _) (by omega_arith), ?_, u₁.keeps.trans (m.keeps _)⟩
  change w32 u.mem base w + 2 ^ 32 * val32 u.mem base (w + 4) 9 + _ =
    w32 s.mem base w + 2 ^ 32 * val32 s.mem base (w + 4) 9
  rw [O.val32 (by omega_arith) (by omega_arith), hm, w32_write_self]
  change 0 + _ + _ = _
  omega_arith

theorem p256RedB_ok {s : State} {base : Addr} {size : Nat} (hb : Bx s base size)
    {acc w : Nat}
    (hw : acc = w) (hsz : w + 40 ≤ size)
    (hq : (s.gpr .ecx).toNat = w32 s.mem base w)
    (hlt : val32 s.mem base w 10 + (s.gpr .ecx).toNat *
      (2 ^ 256 - 2 ^ 224 + 2 ^ 192 + 2 ^ 96 - 1) < 2 ^ 320) :
    WP isa (.block (p256Red acc)) s fun u =>
      Outside base w 40 s.mem u.mem ∧
      val32 u.mem base w 10 = val32 s.mem base w 10 + (s.gpr .ecx).toNat *
        (2 ^ 256 - 2 ^ 224 + 2 ^ 192 + 2 ^ 96 - 1) ∧ Keeps [.eax] s u := by
  simp only [p256Red, List.append_assoc]
  refine WP.block_append (WP.mono (clearLowB_ok hb hw hsz) fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
  have hb₁ := hb.of_keeps K₁ (by decide)
  refine WP.block_append (WP.mono (positiveB_ok hb₁ hw hsz)
    fun s₂ ⟨O₂, ⟨c₂, V₂⟩, K₂⟩ => ?_)
  have hb₂ := hb₁.of_keeps K₂ (by decide)
  refine WP.mono (sparseShiftSubB_ok hb₂ hw (N := 10) (j := 7) (k := 2) rfl hsz)
    fun u ⟨O₃, ⟨c₃, V₃⟩, K₃⟩ => ⟨(O₁.trans O₂).trans O₃, ?_, (K₁.trans K₂).trans K₃⟩
  rw [K₁.1 .ecx (by decide)] at V₂
  rw [K₂.1 .ecx (by decide), K₁.1 .ecx (by decide)] at V₃
  have hu := val32_lt u.mem base w 10
  omega_arith

/-! ## P-521's reduction

`p521Red acc` on the window of twenty words at `[ebp + acc]`: for
`p = 2^521 - 1` and `q` the window's low word, the window `+ q p` is the
window with its low word cleared and `q 2^9` added at word 16.
-/

/-- A word of the window cleared. -/
theorem clearWordB_ok {s : State} {base : Addr} {size : Nat} (hb : Bx s base size) {w : Nat}
    (hsz : w + 4 ≤ size) :
    WP isa (.block [.mov .eax (.imm 0), .store (bp w) .eax]) s fun u =>
      Outside base w 4 s.mem u.mem ∧ w32 u.mem base w = 0 ∧ u.cf = s.cf ∧ Keeps [.eax] s u := by
  have hn := hb.nowrap
  refine wp_movS rfl fun s₁ u₁ c₁ => ?_
  have hb₁ := hb.of_keeps u₁.keeps (by decide)
  refine wp_storeS (hb₁.ea (d := w) (by omega_arith)) (hb₁.write (n := 4) (by omega_arith))
    fun u m => WP.block_nil ⟨?_, ?_, by rw [m.cf, c₁], u₁.keeps.trans (m.keeps _)⟩
  · rw [m.mem, u₁.mem]; exact writeW32_outside _ _ _ (by omega_arith)
  · rw [m.mem, w32_write_self, u₁.gpr]; rfl

/-- `edx:ecx = 2^9 ecx`. -/
theorem shift9_ok {s : State} :
    WP isa (.block shift9) s fun u =>
      u.mem = s.mem ∧ (u.gpr .ecx).toNat + 2 ^ 32 * (u.gpr .edx).toNat = (s.gpr .ecx).toNat * 512 ∧
      Keeps [.eax, .ecx, .edx] s u := by
  unfold shift9
  refine wp_movS rfl fun s₁ u₁ _ => ?_
  refine wp_movS rfl fun s₂ u₂ _ => ?_
  refine wp_mul fun s₃ u₃ => ?_
  refine wp_movS rfl fun u u₄ _ => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · have ha : (s₂.gpr .eax).toNat = (s.gpr .ecx).toNat := by rw [u₂.other .eax (by decide), u₁.gpr]
    have hd : (s₂.gpr .edx).toNat = 512 := by rw [u₂.gpr]; rfl
    have hq := (s.gpr .ecx).isLt
    rw [u₄.gpr, u₄.other .edx (by decide), u₃.eax, u₃.edx, ha, hd, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_arith
  · refine ⟨fun r hr => ?_, by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd], by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₄.other r hr.2.1, u₃.other r hr.1 hr.2.2, u₂.other r hr.2.2, u₁.other r hr.1]

theorem val32_20 (mem : Mem) (base : Addr) (w : Nat) :
    val32 mem base w 20 = w32 mem base w + 2 ^ 32 * val32 mem base (w + 4) 15 +
      2 ^ 512 * (w32 mem base (w + 64) + 2 ^ 32 * w32 mem base (w + 68) + 2 ^ 64 * w32 mem base (w + 72) +
        2 ^ 96 * w32 mem base (w + 76)) := by
  rw [show 20 = 16 + 4 from rfl, val32_append mem base w 16 4]
  simp only [val32, Nat.reduceMul, Nat.reduceAdd, Nat.add_assoc]
  omega_arith

theorem p521RedB_ok {s : State} {base : Addr} {size : Nat} (hb : Bx s base size)
    {acc w : Nat}
    (hw : acc = w) (hsz : w + 80 ≤ size)
    (hq : (s.gpr .ecx).toNat = w32 s.mem base w)
    (hlt : val32 s.mem base w 20 + (s.gpr .ecx).toNat * (2 ^ 521 - 1) < 2 ^ 640) :
    WP isa (.block (p521Red acc)) s fun u =>
      Outside base w 80 s.mem u.mem ∧
      val32 u.mem base w 20 = val32 s.mem base w 20 + (s.gpr .ecx).toNat * (2 ^ 521 - 1) ∧
      Keeps [.eax, .ecx, .edx] s u := by
  subst hw
  have hn := hb.nowrap
  simp only [p521Red, List.append_assoc]
  refine WP.block_append (WP.mono (clearWordB_ok hb (w := acc) (by omega_arith)) fun s₁ ⟨O₁, Z₁, _, K₁⟩ => ?_)
  have hb₁ := hb.of_keeps K₁ (by decide)
  refine WP.block_append (WP.mono shift9_ok fun s₂ ⟨M₂, P₂, K₂⟩ => ?_)
  have hb₂ := hb₁.of_keeps K₂ (by decide)
  rw [K₁.1 .ecx (by decide)] at P₂
  refine WP.block_append (WP.mono (sparseStepAddB_ok hb₂ (op := .add) (cin := false) (.inl ⟨rfl, rfl⟩)
    (acc := acc) (j := 16) true (by omega_arith)) fun s₃ ⟨O₃, ⟨c₃, cf₃, V₃⟩, K₃⟩ => ?_)
  have hb₃ := hb₂.of_keeps K₃ (by decide)
  refine WP.block_append (wp_movS rfl fun s₄ u₄ cf₄ => WP.block_nil ?_)
  have hb₄ := hb₃.of_keeps u₄.keeps (by decide)
  refine WP.block_append (WP.mono (sparseStepAddB_ok hb₄ (op := .adc) (cin := c₃)
    (.inr ⟨rfl, by rw [cf₄, cf₃]⟩) (acc := acc) (j := 17) true (by omega_arith))
    fun s₅ ⟨O₅, ⟨c₅, cf₅, V₅⟩, K₅⟩ => ?_)
  have hb₅ := hb₄.of_keeps K₅ (by decide)
  refine WP.block_append (WP.mono (sparseStepAddB_ok hb₅ (op := .adc) (cin := c₅) (.inr ⟨rfl, cf₅⟩)
    (acc := acc) (j := 18) false (by omega_arith)) fun s₆ ⟨O₆, ⟨c₆, cf₆, V₆⟩, K₆⟩ => ?_)
  have hb₆ := hb₅.of_keeps K₆ (by decide)
  refine WP.mono (sparseStepAddB_ok hb₆ (op := .adc) (cin := c₆) (.inr ⟨rfl, cf₆⟩)
    (acc := acc) (j := 19) false (by omega_arith)) fun u ⟨O₇, ⟨c₇, _, V₇⟩, K₇⟩ => ?_
  -- The registers the additions read.
  have e₃ : (s₂.gpr .ecx).toNat + 2 ^ 32 * (s₄.gpr .ecx).toNat = (s.gpr .ecx).toNat * 512 := by
    rw [u₄.gpr, K₃.1 .edx (by decide)]; exact P₂
  simp only [Bool.false_eq_true, ite_false, ite_true, Bool.toNat_false, Nat.reduceMul, Nat.add_zero] at V₃ V₅ V₆ V₇
  -- The memory of each state, word by word.
  have m₂ : s₂.mem = s₁.mem := M₂
  have m₄ : s₄.mem = s₃.mem := u₄.mem
  rw [m₂] at O₃ V₃
  rw [m₄] at O₅ V₅
  refine ⟨?_, ?_, ?_⟩
  · exact (((((O₁.mono (Nat.le_refl _) (by omega_arith)).trans (m₂ ▸ Outside.refl _ _ _ _)).trans
      (O₃.mono (by omega_arith) (by omega_arith))).trans (m₄ ▸ Outside.refl _ _ _ _)).trans
      (O₅.mono (by omega_arith) (by omega_arith))).trans
      ((O₆.mono (by omega_arith) (by omega_arith)).trans (O₇.mono (by omega_arith) (by omega_arith)))
  · have low : val32 u.mem base (acc + 4) 15 = val32 s.mem base (acc + 4) 15 := by
      rw [O₇.val32 (by omega_arith) (by omega_arith), O₆.val32 (by omega_arith) (by omega_arith),
        O₅.val32 (by omega_arith) (by omega_arith), O₃.val32 (by omega_arith) (by omega_arith),
        O₁.val32 (by omega_arith) (by omega_arith)]
    have w0 : w32 u.mem base acc = 0 := by
      rw [O₇.w32 (by omega_arith) (by omega_arith), O₆.w32 (by omega_arith) (by omega_arith),
        O₅.w32 (by omega_arith) (by omega_arith), O₃.w32 (by omega_arith) (by omega_arith), Z₁]
    have a16 : w32 u.mem base (acc + 64) = w32 s₃.mem base (acc + 64) := by
      rw [O₇.w32 (by omega_arith) (by omega_arith), O₆.w32 (by omega_arith) (by omega_arith),
        O₅.w32 (by omega_arith) (by omega_arith)]
    have a17 : w32 u.mem base (acc + 68) = w32 s₅.mem base (acc + 68) := by
      rw [O₇.w32 (by omega_arith) (by omega_arith), O₆.w32 (by omega_arith) (by omega_arith)]
    have a18 : w32 u.mem base (acc + 72) = w32 s₆.mem base (acc + 72) := by
      rw [O₇.w32 (by omega_arith) (by omega_arith)]
    have b16 : w32 s₁.mem base (acc + 64) = w32 s.mem base (acc + 64) := O₁.w32 (by omega_arith) (by omega_arith)
    have b17 : w32 s₃.mem base (acc + 68) = w32 s.mem base (acc + 68) := by
      rw [O₃.w32 (by omega_arith) (by omega_arith), O₁.w32 (by omega_arith) (by omega_arith)]
    have b18 : w32 s₅.mem base (acc + 72) = w32 s.mem base (acc + 72) := by
      rw [O₅.w32 (by omega_arith) (by omega_arith), O₃.w32 (by omega_arith) (by omega_arith),
        O₁.w32 (by omega_arith) (by omega_arith)]
    have b19 : w32 s₆.mem base (acc + 76) = w32 s.mem base (acc + 76) := by
      rw [O₆.w32 (by omega_arith) (by omega_arith), O₅.w32 (by omega_arith) (by omega_arith),
        O₃.w32 (by omega_arith) (by omega_arith), O₁.w32 (by omega_arith) (by omega_arith)]
    rw [b16] at V₃
    rw [b17] at V₅
    rw [b18] at V₆
    rw [b19] at V₇
    have hu := val32_lt u.mem base acc 20
    rw [val32_20] at hlt hu ⊢
    rw [val32_20 s.mem, low, w0, a16, a17, a18]
    have c7 := Bool.toNat_le c₇
    omega_arith
  · exact ((((((K₁.mono (by decide)).trans K₂).trans (K₃.mono (by decide))).trans (u₄.keeps.mono (by decide))).trans
      (K₅.mono (by decide))).trans (K₆.mono (by decide))).trans (K₇.mono (by decide))


end VG.Proof.Weierstrass.X86.Mont
