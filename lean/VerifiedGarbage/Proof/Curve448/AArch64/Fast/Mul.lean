module

public import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Bounds
public import VerifiedGarbage.Proof.Curve448.AArch64.Fast.MOp
import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Finish
import VerifiedGarbage.Proof.Curve448.AArch64.Fast.ColEnd
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Prelude
import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Columns

/-! ### `Curve448.AArch64.Fast.Loop`, which only this module used -/

section

/-!
# The four columns of a product

Untrusted: everything here is checked by Lean. For any registers and steps
whose accumulators `L` and `H` hold coefficients `d` and `d + 4` of `r` after
column `d` (`hsem`), the columns stage the limbs of both carry chains and
leave their last carries in `CL` and `CH`.
-/

@[expose] public section

namespace VG.Proof.Curve448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Fast
open VG.Impl.X448.AArch64 (ld st ACC)
open VG.Proof.X448.Wide (radix pair)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside writeW_outside limbs)

/-- The registers a column may write. -/
def colWrites (R : Regs) (accs : List Acc) : List Reg := writes R accs ++ [CL, CH]

/-- What the columns guarantee after `n` of them. -/
structure ColInv (base : Addr) (o : Nat) (r : Nat → Nat) (s t : State) (n : Nat) : Prop where
  scr : Scr t base
  mask : t.gpr MASK = BitVec.ofNat 64 (2 ^ 56 - 1)
  zero : t.gpr ZERO = 0
  out : Outside base o 64 s.mem t.mem
  lo : ∀ k < n, (word t.mem base (o + 8 * k)).toNat = chainLimb r 0 k
  hi : ∀ k < n, (word t.mem base (o + 8 * (4 + k))).toNat = chainLimb r 4 k
  cl : 0 < n → (t.gpr CL).toNat = chain r 0 n
  ch : 0 < n → (t.gpr CH).toNat = chain r 4 n

theorem colEnd_ok {s : State} {base : Addr} (hs : Scr s base) (t : Reg) (a : Acc) (c : Reg)
    (first : Bool) {ro : Reg} {D o k : Nat} (hpo : PtrOk s base ro D o) (hk : k < 8) (h₁ : t ≠ a.lo)
    (h₂ : t ≠ a.hi) (h₃ : t ≠ ro)
    (h₄ : a.lo ≠ a.hi) (h₅ : a.lo ≠ ZERO) (h₆ : MASK ∉ [a.lo, a.hi]) (h₇ : a.lo ≠ .x3)
    (h₈ : a.hi ≠ .x3) (h₉ : a.lo ≠ .x12) (h₁₀ : a.hi ≠ .x12) (h₁₁ : a.lo ≠ ro) (h₁₂ : a.hi ≠ ro)
    (hm : s.gpr MASK = BitVec.ofNat 64 (2 ^ 56 - 1)) (hz : s.gpr ZERO = 0)
    {V cin : Nat} (hV : accVal s a = V) (hc : first = false → (s.gpr c).toNat = cin)
    (h0 : first = true → cin = 0) (hlt : V + cin < 2 ^ 120) :
    WP isa (.block (colEnd t a c first ro D k)) s fun u =>
      u.mem = s.mem.writeW (off base (o + 8 * k)) (BitVec.ofNat 64 ((V + cin) % radix)) ∧
      (u.gpr c).toNat = (V + cin) / radix ∧ Keeps [a.lo, a.hi, t, c] s u := by
  have ho : o + 64 ≤ 8192 := hpo.fit
  have hal := hpo.al
  have hDl := hpo.lt
  cases first
  · simp only [colEnd, Bool.false_eq_true, ite_false, List.cons_append, List.nil_append]
    rw [show (Instr.adds .x a.lo a.lo c :: Instr.adc .x a.hi a.hi ZERO ::
        [Instr.logic .and .x t a.lo MASK, .str .x t ro (D + 8 * k), .extr .x c a.hi a.lo 56]) =
        [Instr.adds .x a.lo a.lo c, .adc .x a.hi a.hi ZERO] ++
        [Instr.logic .and .x t a.lo MASK, .str .x t ro (D + 8 * k), .extr .x c a.hi a.lo 56] from rfl,
      WP.block_append_iff]
    have hc' := hc rfl
    refine WP.mono (carryIn_ok s a c h₄ h₅ hz (by rw [hV, hc']; omega_arith)) fun u ⟨uv, um, uk⟩ => ?_
    have us : Scr u base := hs.of_keeps uk (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨⟨Ne.symm h₇, Ne.symm h₈⟩, ⟨Ne.symm h₉, Ne.symm h₁₀⟩⟩)
    have um' : u.gpr MASK = BitVec.ofNat 64 (2 ^ 56 - 1) := by rw [uk.1 _ h₆, hm]
    have up : PtrOk u base ro D o := hpo.of_keeps uk (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨Ne.symm h₁₁, Ne.symm h₁₂⟩)
    refine WP.mono (stage_ok us t a c (up.ptr (8 * k)) (by omega_arith) (by omega_arith) (by omega_arith) h₁ h₂ h₃ um'
      (by rw [uv, hV, hc']; omega_arith))
      fun w ⟨wm, wc, wk⟩ => ⟨?_, ?_, ?_⟩
    · rw [wm, uv, um, hV, hc']
    · rw [wc, uv, hV, hc']
    · refine (uk.mono ?_).trans (wk.mono ?_) <;> intro r hr <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢ <;>
        rcases hr with h | h <;> simp [h]
  · simp only [colEnd, ite_true, List.nil_append]
    have hc' := h0 rfl
    subst hc'
    refine WP.mono (stage_ok hs t a c (hpo.ptr (8 * k)) (by omega_arith) (by omega_arith) (by omega_arith) h₁ h₂ h₃ hm
      (by rw [hV]; omega_arith))
      fun w ⟨wm, wc, wk⟩ => ⟨?_, ?_, ?_⟩
    · rw [wm, hV, Nat.add_zero]
    · rw [wc, hV, Nat.add_zero]
    · refine wk.mono ?_
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h <;> simp [h]

/-- The carry and constant registers are not written by the steps, by `decide`. -/
abbrev ColRegs (R : Regs) (accs : List Acc) : Prop :=
  MASK ∉ colWrites R accs ∧ ZERO ∉ colWrites R accs ∧ CL ∉ writes R accs ∧ CH ∉ writes R accs ∧
  CL ≠ CH ∧ Reg.x3 ∉ [CL, CH] ∧ Reg.x12 ∉ [CL, CH]

theorem word_stage {m : Mem} {base : Addr} {o k j : Nat} (ho : o + 64 ≤ 8192) (hk : k < 8)
    (hj : j < 8) (v : BitVec 64) :
    word (m.writeW (off base (o + 8 * k)) v) base (o + 8 * j) =
      if j = k then v else word m base (o + 8 * j) := by
  rw [VG.Proof.Curve448.AArch64.Fast.word_writeW m base (by omega_arith) (by omega_arith) (by omega_arith)]
  by_cases h : j = k
  · rw [ite_eq_left (by omega_arith), ite_eq_left h]
  · rw [ite_eq_right (by omega_arith), ite_eq_right h]

theorem stage_outside (m : Mem) (base : Addr) {o k : Nat} (ho : o + 64 ≤ 8192) (hk : k < 8)
    (v : BitVec 64) : Outside base o 64 m (m.writeW (off base (o + 8 * k)) v) := by
  exact (writeW_outside m base v (by omega_arith)).mono (by omega_arith) (by omega_arith)

section
variable {R : Regs} {accs : List Acc} {L H : Acc} {col : Nat → List MOp} {rb ro : Reg} {db b od o : Nat}
  {r : Nat → Nat} {base : Addr}

theorem column_ok (hG : Good R accs) (hC : ColRegs R accs) (hL : L ∈ accs) (hH : H ∈ accs)
    (hLH : L ≠ H) (hrb : rb ∉ colWrites R accs) (hro : ro ∉ colWrites R accs)
    (hfit : Fits r) {d : Nat} (hd : d < 4) (hops : (col d).all (opOk (writes R accs) accs) = true)
    {t : State} {s : State} (hi : ColInv base o r s t d) (hpb : PtrOk t base rb db b)
    (hpo : PtrOk t base ro od o)
    (hsem : ∀ e, sem (srcVal t base b) e (col d) L = r d ∧ sem (srcVal t base b) e (col d) H = r (d + 4)) :
    WP isa (.block ((col d).flatMap (MOp.code R rb db) ++ colEnd R.t L CL (d == 0) ro od d ++
        colEnd R.t H CH (d == 0) ro od (d + 4))) t fun w =>
      ColInv base o r s w (d + 1) ∧ Keeps (colWrites R accs) t w ∧ Outside base o 64 t.mem w.mem := by
  obtain ⟨hM, hZ, hCL, hCH, hCC, h3, h12⟩ := hC
  have ho : o + 64 ≤ 8192 := hpo.fit
  have hrbw : rb ∉ writes R accs := fun h => hrb (List.mem_append_left _ h)
  have hrow : ro ∉ writes R accs := fun h => hro (List.mem_append_left _ h)
  have nM : MASK ∉ writes R accs := fun h => hM (List.mem_append_left _ h)
  have nZ : ZERO ∉ writes R accs := fun h => hZ (List.mem_append_left _ h)
  obtain ⟨Llh, Llo, Lhi⟩ := hG.acc hL
  obtain ⟨Hlh, Hlo, Hhi⟩ := hG.acc hH
  have x3w : Reg.x3 ∉ writes R accs := hG.2.2.2.2.2.1
  have x12w : Reg.x12 ∉ writes R accs := hG.2.2.2.2.2.2
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (mops_ok hG hrbw (col d) hops hi.scr hpb (v := srcVal t base b) (fun _ _ => rfl)
    (e := fun a => (accVal t a : Int)) (fun a _ => self_emod (pair_lt _ _))) fun u ⟨uv, um, uk⟩ => ?_
  have us : Scr u base := hG.scr hi.scr uk (fun _ h => h)
  obtain ⟨sL, sH⟩ := hsem (fun a => (accVal t a : Int))
  have rL : accVal u L = r d := exact_of_emod (uv L hL) sL (by
    have := hfit.low d hd; simp only [M]; omega_arith)
  have rH : accVal u H = r (4 + d) := exact_of_emod (uv H hH) (by rw [sH, Nat.add_comm]) (by
    have := hfit.high d hd; simp only [M]; omega_arith)
  have um' : u.gpr MASK = BitVec.ofNat 64 (2 ^ 56 - 1) := by rw [uk.1 _ nM, hi.mask]
  have uz : u.gpr ZERO = 0 := by rw [uk.1 _ nZ, hi.zero]
  have tne : ∀ a ∈ accs, R.t ≠ a.lo ∧ R.t ≠ a.hi := fun a ha => by
    obtain ⟨-, h1, h2⟩ := hG.acc ha
    exact ⟨fun e => h1 (by simp [e]), fun e => h2 (by simp [e])⟩
  have t3 : R.t ≠ ro := fun e => hrow (e ▸ t_mem)
  have up : PtrOk u base ro od o := hpo.of_keeps uk hrow
  have nmem : ∀ {q : Reg} {a : Acc}, a ∈ accs → q ∉ writes R accs → q ∉ [a.lo, a.hi] := by
    intro q a ha hq hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h
    · exact hq (h ▸ lo_mem ha)
    · exact hq (h ▸ hi_mem ha)
  rw [WP.block_append_iff]
  have hcL : (d == 0) = false → (u.gpr CL).toNat = chain r 0 d := fun h => by
    rw [uk.1 _ hCL]; exact hi.cl (by simp at h; omega_arith)
  have h0L : (d == 0) = true → chain r 0 d = 0 := fun h => by
    simp at h; subst h; rfl
  refine WP.mono (colEnd_ok us R.t L CL (d == 0) (k := d) up (by omega_arith) (tne L hL).1 (tne L hL).2 t3 Llh
    (fun e => nZ (e ▸ lo_mem hL)) (nmem hL nM) (fun e => x3w (e ▸ lo_mem hL))
    (fun e => x3w (e ▸ hi_mem hL)) (fun e => x12w (e ▸ lo_mem hL)) (fun e => x12w (e ▸ hi_mem hL))
    (fun e => hrow (e ▸ lo_mem hL)) (fun e => hrow (e ▸ hi_mem hL))
    um' uz rL hcL h0L (hfit.low d hd)) fun w ⟨wm, wc, wk⟩ => ?_
  have lnot : ∀ {q : Reg}, q ∉ writes R accs → q ≠ CL → q ∉ [L.lo, L.hi, R.t, CL] := by
    intro q hq hc hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h
    · exact hq (h ▸ lo_mem hL)
    · exact hq (h ▸ hi_mem hL)
    · exact hq (h ▸ t_mem)
    · exact hc h
  have ws : Scr w base := us.of_keeps wk (by
    refine ⟨lnot x3w (fun e => h3 (by simp [e])), lnot x12w (fun e => h12 (by simp [e]))⟩)
  have wM : w.gpr MASK = BitVec.ofNat 64 (2 ^ 56 - 1) := by
    rw [wk.1 _ (lnot nM (fun e => hM (by simp [colWrites, e]))), um']
  have wZ : w.gpr ZERO = 0 := by
    rw [wk.1 _ (lnot nZ (fun e => hZ (by simp [colWrites, e]))), uz]
  have wH : accVal w H = r (4 + d) := by
    obtain ⟨d1, d2⟩ := hG.disj hH hL (Ne.symm hLH)
    rw [accVal_keep wk (fun e => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at e
        rcases e with e | e | e | e
        · exact d1 (by simp [e])
        · exact d1 (by simp [e])
        · exact (tne H hH).1 e.symm
        · exact hCL (e ▸ lo_mem hH))
      (fun e => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at e
        rcases e with e | e | e | e
        · exact d2 (by simp [e])
        · exact d2 (by simp [e])
        · exact (tne H hH).2 e.symm
        · exact hCL (e ▸ hi_mem hH)), rH]
  have wp : PtrOk w base ro od o := up.of_keeps wk (lnot hrow (fun e => hro (by simp [colWrites, e])))
  have hcH : (d == 0) = false → (w.gpr CH).toNat = chain r 4 d := fun h => by
    rw [wk.1 _ (lnot hCH (Ne.symm hCC)), uk.1 _ hCH]; exact hi.ch (by simp at h; omega_arith)
  have h0H : (d == 0) = true → chain r 4 d = 0 := fun h => by
    simp at h; subst h; rfl
  refine WP.mono (colEnd_ok ws R.t H CH (d == 0) (k := d + 4) wp (by omega_arith) (tne H hH).1 (tne H hH).2 t3
    Hlh (fun e => nZ (e ▸ lo_mem hH)) (nmem hH nM) (fun e => x3w (e ▸ lo_mem hH))
    (fun e => x3w (e ▸ hi_mem hH)) (fun e => x12w (e ▸ lo_mem hH)) (fun e => x12w (e ▸ hi_mem hH))
    (fun e => hrow (e ▸ lo_mem hH)) (fun e => hrow (e ▸ hi_mem hH))
    wM wZ wH hcH h0H (hfit.high d hd)) fun x ⟨xm, xc, xk⟩ => ?_
  have hnot : ∀ {q : Reg}, q ∉ writes R accs → q ≠ CH → q ∉ [H.lo, H.hi, R.t, CH] := by
    intro q hq hc hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h
    · exact hq (h ▸ lo_mem hH)
    · exact hq (h ▸ hi_mem hH)
    · exact hq (h ▸ t_mem)
    · exact hc h
  have rad : ∀ n, n % radix < 2 ^ 64 := fun n => Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
  have tw : Outside base o 64 t.mem x.mem := by
    rw [xm, wm, um]
    exact (stage_outside _ _ ho (by omega_arith) _).trans (stage_outside _ _ ho (by omega_arith) _)
  have sub : ∀ q ∈ writes R accs, q ∈ colWrites R accs := fun q h => List.mem_append_left _ h
  refine ⟨⟨ws.of_keeps xk ⟨hnot x3w (fun e => h3 (by simp [e])), hnot x12w (fun e => h12 (by simp [e]))⟩,
    by rw [xk.1 _ (hnot nM (fun e => hM (by simp [colWrites, e]))), wM],
    by rw [xk.1 _ (hnot nZ (fun e => hZ (by simp [colWrites, e]))), wZ],
    hi.out.trans tw, fun k hk => ?_, fun k hk => ?_, fun _ => ?_, fun _ => ?_⟩,
    (uk.mono sub).trans ((wk.mono ?_).trans (xk.mono ?_)), tw⟩
  · rw [xm, word_stage ho (by omega_arith) (by omega_arith), ite_eq_right (by omega_arith), wm, word_stage ho (by omega_arith) (by omega_arith)]
    by_cases h : k = d
    · rw [ite_eq_left h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (rad _), h]
      simp only [chainLimb, Nat.zero_add]
    · rw [ite_eq_right h, um]; exact hi.lo k (by omega_arith)
  · rw [xm, show 4 + k = k + 4 by omega_arith, word_stage ho (by omega_arith) (by omega_arith)]
    by_cases h : k + 4 = d + 4
    · rw [ite_eq_left h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (rad _), show k = d by omega_arith]
      simp only [chainLimb]
    · rw [ite_eq_right h, wm, word_stage ho (by omega_arith) (by omega_arith), ite_eq_right (by omega_arith), um,
        show k + 4 = 4 + k by omega_arith]
      exact hi.hi k (by omega_arith)
  · rw [xk.1 _ (hnot hCL hCC), wc]
    simp only [chain, Nat.zero_add]
  · rw [xc]
    simp only [chain]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with h | h | h | h
    · exact sub _ (h ▸ lo_mem hL)
    · exact sub _ (h ▸ hi_mem hL)
    · exact sub _ (h ▸ t_mem)
    · rw [h]; simp [colWrites]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with h | h | h | h
    · exact sub _ (h ▸ lo_mem hH)
    · exact sub _ (h ▸ hi_mem hH)
    · exact sub _ (h ▸ t_mem)
    · rw [h]; simp [colWrites]

theorem columns_ok (hG : Good R accs) (hC : ColRegs R accs) (hL : L ∈ accs) (hH : H ∈ accs)
    (hLH : L ≠ H) (hrb : rb ∉ colWrites R accs) (hro : ro ∉ colWrites R accs)
    (hfit : Fits r) (hops : ∀ d < 4, (col d).all (opOk (writes R accs) accs) = true)
    (P : State → Prop)
    (hP : ∀ t u, P t → Keeps (colWrites R accs) t u → Outside base o 64 t.mem u.mem → P u)
    (hsem : ∀ d < 4, ∀ t, P t → ∀ e,
      sem (srcVal t base b) e (col d) L = r d ∧ sem (srcVal t base b) e (col d) H = r (d + 4))
    {s : State} (hs : Scr s base) (hpb : PtrOk s base rb db b) (hpo : PtrOk s base ro od o) (hP0 : P s)
    (hm : s.gpr MASK = BitVec.ofNat 64 (2 ^ 56 - 1)) (hz : s.gpr ZERO = 0) :
    WP isa (.block (columns R rb db L H col ro od)) s fun t =>
      P t ∧ ColInv base o r s t 4 ∧ Keeps (colWrites R accs) s t := by
  let inv := fun n (t : State) => P t ∧ ColInv base o r s t n ∧ Keeps (colWrites R accs) s t
  refine wp_range_flatMap (M := isa) (N := 4) inv (fun n t hn ⟨tp, ti, tk⟩ => ?_) 4 (by decide) s
    ⟨hP0, ⟨hs, hm, hz, Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _), fun h => absurd h (Nat.lt_irrefl _),
      fun h => absurd h (Nat.lt_irrefl _)⟩, Keeps.refl _ _⟩
  exact WP.mono (column_ok hG hC hL hH hLH hrb hro hfit hn (hops n hn) ti (hpb.of_keeps tk hrb)
    (hpo.of_keeps tk hro) (hsem n hn t tp))
    fun u ⟨ui, uk, uo⟩ => ⟨hP t u tp uk uo, ui, tk.trans uk⟩

end

end VG.Proof.Curve448.AArch64.Fast

end

end


/-!
# Multiplication

Untrusted: everything here is checked by Lean. `mul o a b` writes the
limbs `out r` of the reduced schoolbook coefficients `r` of `[a] * [b]` to
`o`, for operand limbs below `Ib`.
-/

@[expose] public section

namespace VG.Proof.Curve448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Fast
open VG.Impl.X448.AArch64 (ld st ACC)
open VG.Proof.X448.Wide (radix pair rows reduced)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside Outside2 writeW_outside limbs FieldMem ofs)

/-- The registers every field operation may write. -/
def clob : List Reg :=
  [.x0, .x2, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x13, .x14, .x15, .x16, .x17,
    .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28]

def kakb (rb : Reg) (b : Nat) : List Instr :=
  (List.range 4).flatMap (fun i =>
    [.add .x Mul.R.p0 (Mul.A i) (Mul.A (i + 4)), st Mul.R.p0 (KA + 8 * i),
      .ldr .x Mul.R.t rb (b + 8 * i), .ldr .x Mul.R.p1 rb (b + 32 + 8 * i),
      .add .x Mul.R.t Mul.R.t Mul.R.p1, st Mul.R.t (KB + 8 * i)])

theorem mulAt_split (ra : Reg) (a : Nat) (rb : Reg) (b : Nat) (ro : Reg) (o : Nat) :
    mulAt ra a rb b ro o = loadA ra a ++ consts ++ kakb rb b ++
      columns Mul.R rb b Mul.L Mul.H Mul.column ro o ++ finish ro o :=
  rfl

theorem kakb_ok {s : State} {base : Addr} (hs : Scr s base) {rb : Reg} {D b : Nat}
    (hp : PtrOk s base rb D b) (hb : b + 64 ≤ ACC) (hrb : rb ∉ [Reg.x10, .x11, .x13]) :
    WP isa (.block (kakb rb D)) s fun t =>
      (∀ i < 4, word t.mem base (KA + 8 * i) = s.gpr (Mul.A i) + s.gpr (Mul.A (i + 4))) ∧
      (∀ i < 4, word t.mem base (KB + 8 * i) =
        word s.mem base (b + 8 * i) + word s.mem base (b + 32 + 8 * i)) ∧
      Outside base KA 64 s.mem t.mem ∧ Keeps [.x10, .x11, .x13] s t := by
  have hA : ACC = 3584 := rfl
  have hKA : KA = 3584 := rfl
  have hKB : KB = 3616 := rfl
  let inv := fun n (t : State) =>
    (∀ i < n, word t.mem base (KA + 8 * i) = s.gpr (Mul.A i) + s.gpr (Mul.A (i + 4))) ∧
    (∀ i < n, word t.mem base (KB + 8 * i) =
      word s.mem base (b + 8 * i) + word s.mem base (b + 32 + 8 * i)) ∧
    Outside base KA 64 s.mem t.mem ∧ Keeps [.x10, .x11, .x13] s t
  refine wp_range_flatMap (M := isa) (N := 4) inv (fun n t hn ⟨ta, tb, tO, tk⟩ => ?_) 4 (by decide) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
      Outside.refl _ _ _ _, Keeps.refl _ _⟩
  have ts : Scr t base := hs.of_keeps tk (by decide)
  have treg : ∀ i < 8, t.gpr (Mul.A i) = s.gpr (Mul.A i) := fun i hi => tk.1 _ (A_ne i hi)
  have tw : ∀ d, d + 8 ≤ KA → word t.mem base d = word s.mem base d := fun d hd =>
    tO.word (Or.inl hd) (by omega_arith)
  refine WP.mono (kakbStep_ok ts (hp.of_keeps tk hrb) hb hrb hn) fun u ⟨ua, ub, uo, uk, uw⟩ => ?_
  refine ⟨fun i hi => ?_, fun i hi => ?_, tO.trans uo, tk.trans uk⟩
  · by_cases h : i = n
    · subst h; rw [ua, treg i (by omega_arith), treg (i + 4) (by omega_arith)]
    · rw [uw _ (by omega_arith) (by omega_arith) (by omega_arith)]; exact ta i (by omega_arith)
  · by_cases h : i = n
    · subst h; rw [ub, tw _ (by omega_arith), tw _ (by omega_arith)]
    · rw [uw _ (by omega_arith) (by omega_arith) (by omega_arith)]; exact tb i (by omega_arith)

theorem mul_good : Good Mul.R [Mul.L, Mul.H, Mul.X, Mul.Y] := by decide
theorem mul_colRegs : ColRegs Mul.R [Mul.L, Mul.H, Mul.X, Mul.Y] := by decide
theorem mul_ops : ∀ d < 4, (Mul.column d).all
    (opOk (writes Mul.R [Mul.L, Mul.H, Mul.X, Mul.Y]) [Mul.L, Mul.H, Mul.X, Mul.Y]) = true := by
  decide

theorem A_consts : ∀ i < 8, Mul.A i ∉ [MASK, ZERO] := by decide

theorem A_colWrites : ∀ i < 8, Mul.A i ∉ colWrites Mul.R [Mul.L, Mul.H, Mul.X, Mul.Y] := by decide

/-- The product's limbs, from the operands' limbs. -/
abbrev prodOut (f g : Nat → Nat) : Nat → Nat := out (reduced (rows f g 8))

theorem fits_of {f g : Nat → Nat} (hf : ∀ i < 8, f i < Ib) (hg : ∀ i < 8, g i < Ib) :
    Fits (reduced (rows f g 8)) :=
  fits fun k _ => reduced_le (fun i hi => Nat.le_sub_one_of_lt (hf i hi))
    (fun i hi => Nat.le_sub_one_of_lt (hg i hi)) k

theorem stage_limbs {base : Addr} {o : Nat} {r : Nat → Nat} {s t : State} (hi : ColInv base o r s t 4) :
    ∀ i < 8, (word t.mem base (o + 8 * i)).toNat =
      (if i < 4 then chainLimb r 0 i else chainLimb r 4 (i - 4)) := by
  intro i hi'
  by_cases h : i < 4
  · rw [ite_eq_left h]; exact hi.lo i h
  · rw [ite_eq_right h, show i = 4 + (i - 4) by omega_arith]
    rw [hi.hi (i - 4) (by omega_arith)]; simp

theorem finVal_out (r : Nat → Nat) :
    ∀ i < 8, finVal (fun i => if i < 4 then chainLimb r 0 i else chainLimb r 4 (i - 4))
      (chain r 0 4) (chain r 4 4) i = out r i := by
  intro i hi
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega_arith
  all_goals simp only [finVal, out]; rfl

theorem aRegs_clob : ∀ r ∈ aRegs, r ∈ clob := by decide
theorem consts_clob : ∀ r ∈ [MASK, ZERO], r ∈ clob := by decide
theorem kakb_clob : ∀ r ∈ [Reg.x10, .x11, .x13], r ∈ clob := by decide
theorem colWrites_clob : ∀ r ∈ colWrites Mul.R [Mul.L, Mul.H, Mul.X, Mul.Y], r ∈ clob := by decide
theorem finish_clob : ∀ r ∈ [Reg.x4, .x5, .x6, .x7, .x8], r ∈ clob := by decide

/-- **A product** of operands each addressed by a register plus a displacement (`PtrOk`), at
offsets `a`, `b` and `o` of the working space below the coefficients: the result's limbs, and
only the result's 64 bytes and the operand sums' 64 bytes (`KA`) written. The pointers of `b` and
`o` are not among the registers the product writes, nor `a`'s among those the operand loads write. -/
theorem mulAt_ok {s : State} {base : Addr} (hs : Scr s base) {ra rb ro : Reg} {da db od a b o : Nat}
    (hpa : PtrOk s base ra da a) (hpb : PtrOk s base rb db b) (hpo : PtrOk s base ro od o)
    (hra : ra ∉ aRegs) (hrb : rb ∉ clob) (hro : ro ∉ clob)
    (ho : o + 64 ≤ ACC) (hb : b + 64 ≤ ACC) (hob : o + 64 ≤ b ∨ b + 64 ≤ o)
    (fa : ∀ i < 8, limbs s.mem base a i < Ib) (fb : ∀ i < 8, limbs s.mem base b i < Ib) :
    WP isa (.block (mulAt ra da rb db ro od)) s fun t =>
      (∀ i < 8, limbs t.mem base o i = prodOut (limbs s.mem base a) (limbs s.mem base b) i) ∧
      Outside2 base o 64 KA 64 s.mem t.mem ∧ Keeps clob s t := by
  have hA : ACC = 3584 := rfl
  have hKA : KA = 3584 := rfl
  have hKB : KB = 3616 := rfl
  let f := limbs s.mem base a
  let g := limbs s.mem base b
  have nclob : ∀ {r : Reg} {rs : List Reg}, r ∉ clob → (∀ q ∈ rs, q ∈ clob) → r ∉ rs :=
    fun hr hs h => hr (hs _ h)
  rw [mulAt_split, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadA_ok hs hpa hra) fun t1 ⟨a1, m1, k1⟩ => ?_
  have s1 : Scr t1 base := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (consts_ok t1) fun t2 ⟨mk2, z2, m2, k2⟩ => ?_
  have s2 : Scr t2 base := s1.of_keeps k2 (by decide)
  have pb2 : PtrOk t2 base rb db b :=
    (hpb.of_keeps k1 (nclob hrb aRegs_clob)).of_keeps k2 (nclob hrb consts_clob)
  have po2 : PtrOk t2 base ro od o :=
    (hpo.of_keeps k1 (nclob hro aRegs_clob)).of_keeps k2 (nclob hro consts_clob)
  rw [WP.block_append_iff]
  refine WP.mono (kakb_ok s2 pb2 hb (nclob hrb kakb_clob)) fun t3 ⟨ka3, kb3, o3, k3⟩ => ?_
  have s3 : Scr t3 base := s2.of_keeps k3 (by decide)
  have pb3 : PtrOk t3 base rb db b := pb2.of_keeps k3 (nclob hrb kakb_clob)
  have po3 : PtrOk t3 base ro od o := po2.of_keeps k3 (nclob hro kakb_clob)
  have A3 : ∀ i < 8, (t3.gpr (Mul.A i)).toNat = f i := by
    intro i hi
    rw [k3.1 _ (A_ne i hi), k2.1 _ (A_consts i hi), a1 i hi]
  have g3 : ∀ j < 8, word t3.mem base (b + 8 * j) = word s.mem base (b + 8 * j) := by
    intro j hj
    rw [o3.word (Or.inl (by omega_arith)) (by omega_arith), m2, m1]
  have sumlt : ∀ x y : BitVec 64, x.toNat < Ib → y.toNat < Ib → (x + y).toNat = x.toNat + y.toNat :=
    fun x y hx hy => by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by simp only [Ib] at hx hy; omega_arith)]
  have hfit := fits_of fa fb
  let P := fun (t : State) =>
    (∀ i < 8, t.gpr (Mul.A i) = t3.gpr (Mul.A i)) ∧
    (∀ d, d + 8 ≤ 8192 → (d + 8 ≤ o ∨ o + 64 ≤ d) → word t.mem base d = word t3.mem base d)
  have hP : ∀ t u, P t → Keeps (colWrites Mul.R [Mul.L, Mul.H, Mul.X, Mul.Y]) t u →
      Outside base o 64 t.mem u.mem → P u := by
    intro t u ⟨pa, pm⟩ k o
    exact ⟨fun i hi => (k.1 _ (A_colWrites i hi)).trans (pa i hi),
      fun d hd hd' => (o.word hd' hd).trans (pm d hd hd')⟩
  have hsem : ∀ d < 4, ∀ t, P t → ∀ e,
      sem (srcVal t base b) e (Mul.column d) Mul.L = reduced (rows f g 8) d ∧
      sem (srcVal t base b) e (Mul.column d) Mul.H = reduced (rows f g 8) (d + 4) := by
    intro d hd t ⟨pa, pm⟩ e
    have va : ∀ i < 8, srcVal t base b (.reg (Mul.A i)) = f i := fun i hi => by
      simp only [srcVal]; rw [pa i hi, A3 i hi]
    have vb : ∀ j < 8, srcVal t base b (.arg j) = g j := fun j hj => by
      simp only [srcVal]; rw [pm _ (by omega_arith) (by omega_arith), g3 j hj]
    refine mulCol_ok f g (srcVal t base b) ?_ ?_ ?_ e hd
    · intro i j hi hj
      change ((srcVal t base b (.reg (Mul.A i)) : Nat) : Int) * (srcVal t base b (.arg j) : Nat) = _
      rw [va i (by omega_arith), vb j (by omega_arith)]
    · intro i j hi hj
      change ((srcVal t base b (.reg (Mul.A (i + 4))) : Nat) : Int) *
        (srcVal t base b (.arg (j + 4)) : Nat) = _
      rw [va _ (by omega_arith), vb _ (by omega_arith)]
    · intro i j hi hj
      change ((word t.mem base (KA + 8 * i)).toNat : Int) * ((word t.mem base (KB + 8 * j)).toNat : Int) = _
      have e1 : ∀ i < 8, (t2.gpr (Mul.A i)).toNat = f i := fun i hi => by
        rw [k2.1 _ (A_consts i hi), a1 i hi]
      rw [pm _ (by omega_arith) (by omega_arith), pm _ (by omega_arith) (by omega_arith), ka3 i hi, kb3 j hj,
        m2, m1]
      have x1 := sumlt (t2.gpr (Mul.A i)) (t2.gpr (Mul.A (i + 4)))
        (by rw [e1 i (by omega_arith)]; exact fa i (by omega_arith)) (by rw [e1 (i + 4) (by omega_arith)]; exact fa _ (by omega_arith))
      have gb : word s.mem base (b + 32 + 8 * j) = word s.mem base (b + 8 * (j + 4)) := by
        rw [show b + 32 + 8 * j = b + 8 * (j + 4) by omega_arith]
      have x2 := sumlt (word s.mem base (b + 8 * j)) (word s.mem base (b + 32 + 8 * j))
        (fb j (by omega_arith)) (by rw [gb]; exact fb _ (by omega_arith))
      rw [x1, x2, e1 i (by omega_arith), e1 (i + 4) (by omega_arith), gb]
      push_cast
      rfl
  rw [WP.block_append_iff]
  refine WP.mono (columns_ok mul_good mul_colRegs (by decide) (by decide) (by decide)
    (nclob hrb colWrites_clob) (nclob hro colWrites_clob) hfit mul_ops P hP hsem s3 pb3 po3
    ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
    (by rw [k3.1 _ (by decide)]; exact mk2) (by rw [k3.1 _ (by decide)]; exact z2))
    fun t4 ⟨p4, i4, k4⟩ => ?_
  have hcl := i4.cl (by decide)
  have hch := i4.ch (by decide)
  have lb : ∀ j < 8, (if j < 4 then chainLimb (reduced (rows f g 8)) 0 j
      else chainLimb (reduced (rows f g 8)) 4 (j - 4)) < radix := fun j _ => by
    split <;> exact Nat.mod_lt _ (by decide)
  refine WP.mono (finish_ok i4.scr (po3.of_keeps k4 (nclob hro colWrites_clob))
    (nclob hro finish_clob) i4.mask (stage_limbs i4) lb hcl hch hfit.c₀ hfit.c₄)
    fun t5 ⟨v5, o5, k5⟩ => ⟨fun i hi => by rw [v5 i hi, finVal_out _ i hi], ?_, ?_⟩
  · intro x h1 h2
    simp only [ofs] at h1 h2
    rw [o5 x (by simp only [ofs]; omega_arith), i4.out x (by simp only [ofs]; omega_arith),
      o3 x (by simp only [ofs]; omega_arith), m2, m1]
  · refine (k1.mono ?_).trans ((k2.mono ?_).trans ((k3.mono ?_).trans ((k4.mono ?_).trans (k5.mono ?_))))
    all_goals intro r hr; revert r; decide

theorem mul_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : o + 64 ≤ ACC) (ho8 : o % 8 = 0) (ha : a + 64 ≤ ACC) (ha8 : a % 8 = 0)
    (hb : b + 64 ≤ ACC) (hb8 : b % 8 = 0) (hob : o + 64 ≤ b ∨ b + 64 ≤ o)
    (fa : ∀ i < 8, limbs s.mem base a i < Ib) (fb : ∀ i < 8, limbs s.mem base b i < Ib) :
    WP isa (.block (mul o a b)) s fun t =>
      (∀ i < 8, limbs t.mem base o i = prodOut (limbs s.mem base a) (limbs s.mem base b) i) ∧
      FieldMem base o s.mem t.mem ∧ Keeps clob s t := by
  have hA : ACC = 3584 := rfl
  have hKA : KA = 3584 := rfl
  refine WP.mono (mulAt_ok hs (PtrOk.x3 hs ha8 (by omega_arith)) (PtrOk.x3 hs hb8 (by omega_arith))
    (PtrOk.x3 hs ho8 (by omega_arith)) (by decide) (by decide) (by decide) ho hb hob fa fb)
    fun t ⟨tv, tm, tk⟩ => ⟨tv, fun x h1 h2 => tm x (by omega_arith) (by omega_arith), tk⟩

end VG.Proof.Curve448.AArch64.Fast
