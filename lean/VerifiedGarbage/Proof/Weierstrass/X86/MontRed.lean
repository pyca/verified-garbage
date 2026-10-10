import VerifiedGarbage.Proof.Weierstrass.X86.MontRow
import VerifiedGarbage.Proof.Mont.X86.SparseChain

/-!
# Montgomery arithmetic as functions on x86 (32-bit): P-256's sparse reduction

`p256Red acc` (`Impl/Mont/X86/Sparse.lean`) on the window at `[ebp + acc]`,
the working space at `ebp` (`Bx`): the proofs of `Proof/Mont/X86/P256Red.lean`
and the chains it is built from, for the window addressed from `ebp`.
-/

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


end VG.Proof.Weierstrass.X86.Mont
