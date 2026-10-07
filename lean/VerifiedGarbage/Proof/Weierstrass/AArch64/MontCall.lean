import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Impl.Weierstrass.AArch64

/-!
# Calls of the Montgomery products, on AArch64

`mulCall f n m o a b` (`Impl/Weierstrass/AArch64.lean`) calls the function
`f`, whose code is `Mont.mulFn n m`, on the working space at `x0` and the
offsets `o`, `a` and `b`, keeping `x30` in `v29` (`mulCall_ok`): for a
modulus whose products are calls (`Mod.call`), with the temporary area where
the function stores the modulus (`moAt`), it does what the inline product
does (`Proof/Mont/AArch64/Ops.lean`'s `mul_ok`): it changes only the
registers `clob`, the number at `o` and the temporary area (`OpKeep`).
-/

namespace VG.Proof.Weierstrass.AArch64.Mont

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Impl.Weierstrass.AArch64.Mont
open VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps)

/-- Every register. -/
def allRegs : List Reg := [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13,
  .x14, .x15, .x16, .x17, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x30]

theorem mem_allRegs (r : Reg) : r ∈ allRegs := by cases r <;> decide

/-- The registers a product keeps are `x0`, `x30` and the callee-saved ones. -/
theorem not_clob {n : Nat} (hn : n = 4 ∨ n = 6 ∨ n = 9) {r : Reg} (h : r ∉ clob n) :
    r = .x0 ∨ r = .x30 ∨ r ∈ preserved := by
  have : ∀ n, (n = 4 ∨ n = 6 ∨ n = 9) → ∀ r ∈ allRegs, r ∉ clob n → r = .x0 ∨ r = .x30 ∨ r ∈ preserved := by
    intro n hn; rcases hn with rfl | rfl | rfl <;> decide
  exact this n hn r (mem_allRegs r) h

theorem v29_not_slot : ∀ i < 8, VReg.v29 ≠ (slot i).1 := by decide

/-- The arguments: `x30` into lane 0 of `v29`, the offsets into `x1`–`x3`. -/
theorem args_ok (s : State) {o a b : Nat} (ho : o < 2 ^ 16) (ha : a < 2 ^ 16) (hb : b < 2 ^ 16) :
    WP isa (.block [.vop (.ins .d2 .v29 0 .x30), .movz .x .x1 (BitVec.ofNat 16 o) 0,
      .movz .x .x2 (BitVec.ofNat 16 a) 0, .movz .x .x3 (BitVec.ofNat 16 b) 0]) s fun s₁ =>
      (s₁.gpr .x1).toNat = o ∧ (s₁.gpr .x2).toNat = a ∧ (s₁.gpr .x3).toNat = b ∧
      Keeps [.x1, .x2, .x3] s s₁ ∧ (s₁.v .v29).extractLsb' 0 64 = s.gpr .x30 := by
  apply WP.of_runBlock
  simp only [runBlock_cons, exec_ins (show 0 < 2 by decide), runStep_some]
  simp only [runBlock_cons, exec, show 16 * 0 < Size.x.bits by decide, ite_true, runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']
  have v : ∀ v : BitVec 16, ∀ x, x < 2 ^ 16 → v = BitVec.ofNat 16 x →
      ((BitVec.setWidth Size.x.bits v <<< (16 * 0) : BitVec 64)).toNat = x := by
    intro v x hx e; subst e
    simp only [Nat.mul_zero, BitVec.shiftLeft_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    simp only [Size.bits]; omega
  refine ⟨?_, ?_, ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, ?_⟩
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, BitVec.setWidth_eq]
    exact v _ _ ho rfl
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, BitVec.setWidth_eq]
    exact v _ _ ha rfl
  · simp only [RegUpd.gpr_write, ite_true, BitVec.setWidth_eq]
    exact v _ _ hb rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false, RegUpd.gpr_setV]
  · simp only [RegUpd.v_write, RegUpd.v_setV_self]
    have := extract_setLane (s.v .v29) (s.gpr .x30) (i := 0) (j := 0) (by decide) (by decide)
    simpa using this

/-- `x30` back from lane 0 of `v29`. -/
theorem lr_ok (s : State) :
    WP isa (.block [.umov .x .x30 .v29 0]) s fun s' =>
      s'.gpr .x30 = (s.v .v29).extractLsb' 0 64 ∧ Keeps [.x30] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, exec_umov (show 0 < 2 by decide), runStep_some, runBlock_nil,
    Option.some.injEq, exists_eq_left', Nat.mul_zero]
  refine ⟨by simp [RegUpd.gpr_write], fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

/-- The callee's contract at a call: from the arguments, `mulFn_ok`'s
postcondition. -/
def callK (n m W : Nat) (base : Addr) (o a b : Nat) (mem : Mem) : Contract isa where
  pre t := Pre n W t ∧ t.gpr .x0 = base ∧ arg t .x1 = o ∧ arg t .x2 = a ∧ arg t .x3 = b ∧
    t.mem = mem ∧ wordsVal mem base b n < m
  post t t' := abiPreserved t t' ∧ Kept n base o t.mem t'.mem ∧
    (wordsVal t'.mem base o n < m ∧
      wordsVal t'.mem base o n * 2 ^ (64 * n) % m = wordsVal t.mem base a n * wordsVal t.mem base b n % m) ∧
    t'.gpr .x0 = t.gpr .x0 ∧ ∀ d, (∀ i < 8, d ≠ (slot i).1) → t'.v d = t.v d
  pub _ _ := True

theorem arg_of {v : BitVec 64} {x : Nat} (h : v.toNat = x) : (v.setWidth 32).toNat = x % 2 ^ 32 := by
  rw [BitVec.toNat_setWidth, h]

/-- `[o] = [a] [b] R⁻¹ mod m` by a call of `vg_<curve>_mul_mod_<p|n>`, as the
inline product (`mul_ok`). -/
theorem mulCall_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOkA M size m s.mem base) {f : String} (hH : ModOk M.n m) (htmp : M.tmp = moAt M.n) {o a b : Nat} (ho : o + 8 * M.n ≤ own M.n)
    (ha : a + 8 * M.n ≤ own M.n) (hb : b + 8 * M.n ≤ own M.n) (hB : wordsVal s.mem base b M.n < m) :
    WP isa (mulCall f M.n m o a b) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n < m ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % m =
        wordsVal s.mem base a M.n * wordsVal s.mem base b M.n % m := by
  have hn9 := hH.n9
  have hown := own_eq hn9
  obtain ⟨hmo1, hmo2, hmo8⟩ := moAt_facts hn9 hH.n4
  have htsz := hM.tmp
  rw [htmp] at htsz
  have hnw := hs.nowrap
  rw [mulCall]
  refine WP.seq (WP.mono (args_ok s (by omega) (by omega) (by omega)) fun s₁ ⟨g1, g2, g3, K₁, L₁⟩ => ?_)
  have x0₁ : s₁.gpr .x0 = base := (K₁.gpr _ (by decide)).trans hs.x0
  have hcov : Covers [⟨base, moAt M.n + 8 * M.n⟩] s₁.wr := by
    rw [K₁.wr]
    exact Covers.one ⟨_, hs.wr, by
      have := hs.contains (d := 0) (n := moAt M.n + 8 * M.n) (by omega) (by omega)
      simpa [off] using this⟩
  have hW : moAt M.n + 8 * M.n ≤ size := htsz
  have a1 : ((s₁.gpr .x1).setWidth 32).toNat = o := by rw [arg_of g1]; omega
  have a2 : ((s₁.gpr .x2).setWidth 32).toNat = a := by rw [arg_of g2]; omega
  have a3 : ((s₁.gpr .x3).setWidth 32).toNat = b := by rw [arg_of g3]; omega
  have ce : ∀ r ∈ [Reg.x0, .x1, .x2, .x3], (s₁.callEntry.withRegions [] [⟨base, moAt M.n + 8 * M.n⟩]).gpr r =
      s₁.gpr r := fun r hr => by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)]
  refine WP.seq (WP.callV (k := callK M.n m (moAt M.n + 8 * M.n) base o a b s.mem)
    (fun t ⟨hp, e0, e1, e2, e3, em, hb'⟩ => by
      obtain ⟨tr, t', he, A, K, V, R0, -, -, Vv⟩ := mulFn_ok hH hp (by rw [e0, e3, em]; exact hb')
      refine ⟨tr, t', he, A, A, by rw [← e0, ← e1]; exact K, by rw [← e0, ← e1, ← e2, ← e3]; exact V,
        R0, Vv⟩)
    (rd := []) (wr := [⟨base, moAt M.n + 8 * M.n⟩]) ?_ (Covers.right hcov) hcov ?_ rfl)
  · have c0 := ce .x0 (by simp)
    have c1 := ce .x1 (by simp)
    have c2 := ce .x2 (by simp)
    have c3 := ce .x3 (by simp)
    refine ⟨⟨rfl, by rw [c0, x0₁]; rfl, by rw [c0, x0₁]; omega, Nat.le_refl _, by omega, ?_, ?_, ?_⟩,
      by rw [c0, x0₁], ?_, ?_, ?_, by rw [State.withRegions_mem, State.callEntry_mem, K₁.mem], hB⟩
    · simp only [arg]; rw [c1, a1]; exact ho
    · simp only [arg]; rw [c2, a2]; exact ha
    · simp only [arg]; rw [c3, a3]; exact hb
    · simp only [arg]; rw [c1, a1]
    · simp only [arg]; rw [c2, a2]
    · simp only [arg]; rw [c3, a3]
  · intro s₂ r₂ w₂ p₂ _ hpres _ _ ⟨_, K, ⟨V, C⟩, R0, Vv⟩
    simp only [State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr] at K V C R0
    have Vv' : ∀ d, (∀ i < 8, d ≠ (slot i).1) → s₂.v d = s₁.v d := Vv
    rw [K₁.mem] at K C
    refine WP.mono (lr_ok s₂) fun s₃ ⟨l₃, k₃⟩ => ?_
    have x0₂ : s₂.gpr .x0 = s.gpr .x0 := by
      rw [R0, State.callEntry_gpr _ (by decide), K₁.gpr _ (by decide)]
    refine ⟨⟨fun r hr => ?_, by rw [k₃.rd, r₂, K₁.rd], by rw [k₃.wr, w₂, K₁.wr], by rw [k₃.sp, p₂, K₁.sp],
      fun x hx hx' => ?_⟩, by rw [k₃.mem]; exact V, by rw [k₃.mem]; exact C⟩
    · by_cases h30 : r = .x30
      · subst h30; rw [l₃, Vv' _ v29_not_slot, L₁]
      rcases not_clob hH.hn hr with rfl | rfl | hp
      · rw [k₃.gpr _ (by decide), x0₂]
      · exact absurd rfl h30
      · rw [k₃.gpr r (by simpa using h30), hpres r hp h30, K₁.gpr r (by
          intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl | rfl <;> exact absurd hp (by decide))]
    · rw [k₃.mem]
      exact K x hx (by rw [← htmp]; exact hx')

end VG.Proof.Weierstrass.AArch64.Mont
