module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFnG
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# Calls of the Montgomery products, on AArch64

`mulCall f n m o a b` (`Impl/Weierstrass/AArch64.lean`) calls the function
`f`, whose code is `Mont.mulFn n m`, on the working space at `x0` and the
offsets `o`, `a` and `b`, keeping `x30` in `v29` (`mulCall_ok`): for a
modulus whose products are calls (`callOf`), with the temporary area in the
function's own working space (`moAt`), it does what the inline product
does (`Proof/Mont/AArch64/Ops.lean`'s `mul_ok`): it changes only the
registers `clob`, the number at `o` and the temporary area (`OpKeep`).
-/

@[expose] public section

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
theorem not_clob {n : Nat} (hn : n = 4 ∨ n = 6 ∨ n = 8 ∨ n = 9) {r : Reg} (h : r ∉ clob n) :
    r = .x0 ∨ r = .x30 ∨ r ∈ preserved := by
  have : ∀ n, (n = 4 ∨ n = 6 ∨ n = 8 ∨ n = 9) → ∀ r ∈ allRegs, r ∉ clob n → r = .x0 ∨ r = .x30 ∨ r ∈ preserved := by
    intro n hn; rcases hn with rfl | rfl | rfl | rfl <;> decide
  exact this n hn r (mem_allRegs r) h

theorem v29_not_slot : ∀ i < 10, VReg.v29 ≠ (slot i).1 := by decide

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
    simp only [Size.bits]; omega_arith
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

/-- The callee's contract at a call: from the arguments, the postcondition of
`mulFn_ok` (for `F` the product and `pre` that `[b]` is below `m`) or
`sqrFn384_ok` (the square, `[a]` below `p`). -/
def callK (n m W : Nat) (base : Addr) (o a b : Nat) (mem : Mem) (pre : Nat → Nat → Prop)
    (F : Nat → Nat → Nat) : Contract isa where
  pre t := Pre n W t ∧ t.gpr .x0 = base ∧ arg t .x1 = o ∧ arg t .x2 = a ∧ arg t .x3 = b ∧
    t.mem = mem ∧ pre (wordsVal mem base a n) (wordsVal mem base b n)
  post t t' := abiPreserved t t' ∧ Kept n base o t.mem t'.mem ∧
    (wordsVal t'.mem base o n < m ∧
      wordsVal t'.mem base o n * 2 ^ (64 * n) % m = F (wordsVal t.mem base a n) (wordsVal t.mem base b n) % m) ∧
    t'.gpr .x0 = t.gpr .x0 ∧ t'.v .v29 = t.v .v29
  pub _ _ := True

theorem arg_of {v : BitVec 64} {x : Nat} (h : v.toNat = x) : (v.setWidth 32).toNat = x % 2 ^ 32 := by
  rw [BitVec.toNat_setWidth, h]

theorem mulFn_noFrames (n m : Nat) : (mulFn n m).noFrames = true := by
  unfold mulFn; split <;> (try split) <;> rfl

/-- `[o] = F [a] [b] R⁻¹ mod m` by a call of a function whose code `code`
does that from operands with `pre`, as the inline product (`mul_ok`). -/
theorem callProgV29_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOkA M size m s.mem base) (hn : M.n = 6 ∨ M.n = 8 ∨ M.n = 9) (htmp : M.tmp = moAt M.n) {o a b : Nat}
    (ho : o + 8 * M.n ≤ own M.n) (ha : a + 8 * M.n ≤ own M.n) (hb : b + 8 * M.n ≤ own M.n)
    {f : String} {code : Prog isa} (hnf : code.noFrames = true) (pre : Nat → Nat → Prop)
    (F : Nat → Nat → Nat) (hpre : pre (wordsVal s.mem base a M.n) (wordsVal s.mem base b M.n))
    (hcode : ∀ {W : Nat} {t : State}, Pre M.n W t →
      pre (wordsVal t.mem (t.gpr .x0) (arg t .x2) M.n) (wordsVal t.mem (t.gpr .x0) (arg t .x3) M.n) →
      WP isa code t fun t' => abiPreserved t t' ∧ Kept M.n (t.gpr .x0) (arg t .x1) t.mem t'.mem ∧
        (wordsVal t'.mem (t.gpr .x0) (arg t .x1) M.n < m ∧
        wordsVal t'.mem (t.gpr .x0) (arg t .x1) M.n * 2 ^ (64 * M.n) % m =
          F (wordsVal t.mem (t.gpr .x0) (arg t .x2) M.n) (wordsVal t.mem (t.gpr .x0) (arg t .x3) M.n) % m) ∧
        t'.gpr .x0 = t.gpr .x0 ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
        t'.v .v29 = t.v .v29) :
    WP isa (callProg f code o a b) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n < m ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % m =
        F (wordsVal s.mem base a M.n) (wordsVal s.mem base b M.n) % m := by
  have hn9 : M.n ≤ 9 := by rcases hn with h | h | h <;> omega_arith
  have hn4 : 4 ≤ M.n := by rcases hn with h | h | h <;> omega_arith
  have hown := own_eq hn9
  obtain ⟨hmo1, hmo2, hmo8⟩ := moAt_facts hn9 hn4
  have htsz := hM.tmp
  rw [htmp] at htsz
  have hnw := hs.nowrap
  rw [callProg]
  refine WP.seq (WP.mono (args_ok s (by omega_arith) (by omega_arith) (by omega_arith)) fun s₁ ⟨g1, g2, g3, K₁, L₁⟩ => ?_)
  have x0₁ : s₁.gpr .x0 = base := (K₁.gpr _ (by decide)).trans hs.x0
  have hcov : Covers [⟨base, moAt M.n + 8 * M.n⟩] s₁.wr := by
    rw [K₁.wr]
    exact Covers.one ⟨_, hs.wr, by
      have := hs.contains (d := 0) (n := moAt M.n + 8 * M.n) (by omega_arith) (by omega_arith)
      simpa [off] using this⟩
  have hW : moAt M.n + 8 * M.n ≤ size := htsz
  have a1 : ((s₁.gpr .x1).setWidth 32).toNat = o := by rw [arg_of g1]; omega_arith
  have a2 : ((s₁.gpr .x2).setWidth 32).toNat = a := by rw [arg_of g2]; omega_arith
  have a3 : ((s₁.gpr .x3).setWidth 32).toNat = b := by rw [arg_of g3]; omega_arith
  have ce : ∀ r ∈ [Reg.x0, .x1, .x2, .x3], (s₁.callEntry.withRegions [] [⟨base, moAt M.n + 8 * M.n⟩]).gpr r =
      s₁.gpr r := fun r hr => by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)]
  refine WP.seq (WP.callV (k := callK M.n m (moAt M.n + 8 * M.n) base o a b s.mem pre F)
    (fun t ⟨hp, e0, e1, e2, e3, em, hb'⟩ => by
      obtain ⟨tr, t', he, A, K, V, R0, -, -, Vv⟩ := hcode hp (by rw [e0, e2, e3, em]; exact hb')
      refine ⟨tr, t', he, A, A, by rw [← e0, ← e1]; exact K, by rw [← e0, ← e1, ← e2, ← e3]; exact V,
        R0, Vv⟩)
    (rd := []) (wr := [⟨base, moAt M.n + 8 * M.n⟩]) ?_ (Covers.right hcov) hcov ?_ hnf)
  · have c0 := ce .x0 (by simp)
    have c1 := ce .x1 (by simp)
    have c2 := ce .x2 (by simp)
    have c3 := ce .x3 (by simp)
    refine ⟨⟨rfl, by rw [c0, x0₁]; rfl, by rw [c0, x0₁]; omega_arith, Nat.le_refl _, by omega_arith, ?_, ?_, ?_⟩,
      by rw [c0, x0₁], ?_, ?_, ?_, by rw [State.withRegions_mem, State.callEntry_mem, K₁.mem], hpre⟩
    · simp only [arg]; rw [c1, a1]; exact ho
    · simp only [arg]; rw [c2, a2]; exact ha
    · simp only [arg]; rw [c3, a3]; exact hb
    · simp only [arg]; rw [c1, a1]
    · simp only [arg]; rw [c2, a2]
    · simp only [arg]; rw [c3, a3]
  · intro s₂ r₂ w₂ p₂ _ hpres _ _ ⟨_, K, ⟨V, C⟩, R0, Vv⟩
    simp only [State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr] at K V C R0
    have Vv' : s₂.v .v29 = s₁.v .v29 := Vv
    rw [K₁.mem] at K C
    refine WP.mono (lr_ok s₂) fun s₃ ⟨l₃, k₃⟩ => ?_
    have x0₂ : s₂.gpr .x0 = s.gpr .x0 := by
      rw [R0, State.callEntry_gpr _ (by decide), K₁.gpr _ (by decide)]
    refine ⟨⟨fun r hr => ?_, by rw [k₃.rd, r₂, K₁.rd], by rw [k₃.wr, w₂, K₁.wr], by rw [k₃.sp, p₂, K₁.sp],
      fun x hx hx' => ?_⟩, by rw [k₃.mem]; exact V, by rw [k₃.mem]; exact C⟩
    · by_cases h30 : r = .x30
      · subst h30; rw [l₃, Vv', L₁]
      rcases not_clob (.inr hn) hr with rfl | rfl | hp
      · rw [k₃.gpr _ (by decide), x0₂]
      · exact absurd rfl h30
      · rw [k₃.gpr r (by simpa using h30), hpres r hp h30, K₁.gpr r (by
          intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl | rfl <;> exact absurd hp (by decide))]
    · rw [k₃.mem]
      exact K x hx (by rw [← htmp]; exact hx')

theorem callProg_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOkA M size m s.mem base) (hn : M.n = 6 ∨ M.n = 8 ∨ M.n = 9) (htmp : M.tmp = moAt M.n) {o a b : Nat}
    (ho : o + 8 * M.n ≤ own M.n) (ha : a + 8 * M.n ≤ own M.n) (hb : b + 8 * M.n ≤ own M.n)
    {f : String} {code : Prog isa} (hnf : code.noFrames = true) (pre : Nat → Nat → Prop)
    (F : Nat → Nat → Nat) (hpre : pre (wordsVal s.mem base a M.n) (wordsVal s.mem base b M.n))
    (hcode : ∀ {W : Nat} {t : State}, Pre M.n W t →
      pre (wordsVal t.mem (t.gpr .x0) (arg t .x2) M.n) (wordsVal t.mem (t.gpr .x0) (arg t .x3) M.n) →
      WP isa code t fun t' => abiPreserved t t' ∧ Kept M.n (t.gpr .x0) (arg t .x1) t.mem t'.mem ∧
        (wordsVal t'.mem (t.gpr .x0) (arg t .x1) M.n < m ∧
        wordsVal t'.mem (t.gpr .x0) (arg t .x1) M.n * 2 ^ (64 * M.n) % m =
          F (wordsVal t.mem (t.gpr .x0) (arg t .x2) M.n) (wordsVal t.mem (t.gpr .x0) (arg t .x3) M.n) % m) ∧
        t'.gpr .x0 = t.gpr .x0 ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
        ∀ d, (∀ i < 10, d ≠ (slot i).1) → t'.v d = t.v d) :
    WP isa (callProg f code o a b) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n < m ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % m =
        F (wordsVal s.mem base a M.n) (wordsVal s.mem base b M.n) % m := by
  apply callProgV29_ok hs hM hn htmp ho ha hb hnf pre F hpre
  intro W t hp ha'
  exact WP.mono (hcode hp ha') fun u ⟨hA,hK,hV,h0,hr,hw,hv⟩ =>
    ⟨hA,hK,hV,h0,hr,hw,hv .v29 v29_not_slot⟩

/-- `[o] = [a] [b] R⁻¹ mod m` by a call of `vg_<curve>_mul_mod_<p|n>`, as the
inline product (`mul_ok`). -/
theorem mulCall_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOkA M size m s.mem base) {f : String} (hH : ModOk M.n m) (htmp : M.tmp = moAt M.n) {o a b : Nat} (ho : o + 8 * M.n ≤ own M.n)
    (ha : a + 8 * M.n ≤ own M.n) (hb : b + 8 * M.n ≤ own M.n) (hB : wordsVal s.mem base b M.n < m) :
    WP isa (mulCall f M.n m o a b) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n < m ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % m =
        wordsVal s.mem base a M.n * wordsVal s.mem base b M.n % m :=
  callProg_ok hs hM (by
    rcases hH with h | h
    · rcases h.hn with hn | hn
      · exact .inl hn
      · exact .inr (.inr hn)
    · exact h.hn) htmp ho ha hb (mulFn_noFrames M.n m) (fun _ B => B < m) (· * ·) hB
    fun hp hb' => mulFn_ok hH hp hb'

/-- `[o] = [a]^2 2^-384 mod p` by a call of `vg_p384_sqr_mod_p`, as the inline
product of `[a]` by itself (`mul_ok`). -/
theorem sqrCall_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod}
    (hM : ModOkA M size p384 s.mem base) (hn : M.n = 6) (htmp : M.tmp = moAt M.n) {o a : Nat}
    (ho : o + 8 * M.n ≤ own M.n) (ha : a + 8 * M.n ≤ own M.n) (hA : wordsVal s.mem base a M.n < p384) :
    WP isa (sqrCall o a) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n < p384 ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % p384 =
        wordsVal s.mem base a M.n * wordsVal s.mem base a M.n % p384 := by
  have := callProg_ok (f := Impl.Weierstrass.Mont.p384p.fn "sqr") hs hM (.inl hn) htmp ho ha ha
    (code := sqrFn384) rfl (fun A _ => A < p384) (fun A _ => A * A) hA
    (fun {W t} hp ha' => by rw [hn] at hp ha' ⊢; exact sqrFn384_ok hp ha')
  exact this

end VG.Proof.Weierstrass.AArch64.Mont
