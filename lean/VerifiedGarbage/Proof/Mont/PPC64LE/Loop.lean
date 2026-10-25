module

public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Mont.PPC64LE
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Mont.PPC64LE.Words
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# Montgomery arithmetic on PPC64LE: the loop of the multiplication

An iteration of the loop (`row`), for word `k` of `[a]`, adds `u [b]` to the
accumulator's `n + 1` words at `[acc]`, which hold `T < 2m`, the top word
of the sum in `r12` (`rowB`), then adds `q m` and stores the sum one word
down (`rowM`):
`q = t₀ m' mod 2⁶⁴` makes the sum's low word zero, so the accumulator then
holds `(T + u B + q m) / 2⁶⁴`, below `2m` again (`row_ok`). The loop runs it
`n` times (`loop_ok`).
-/

@[expose] public section

namespace VG.Proof.Mont.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Mont.PPC64LE VG.Proof.Mont

/-- A row's sum stays below `2m` once divided. -/
theorem row_lt {T u B q m : Nat} (hT : T < 2 * m) (hu : u < 2 ^ 64) (hB : B < m) (hq : q < 2 ^ 64) :
    T + u * B + q * m < 2 ^ 64 * (2 * m) := by
  have h1 : u * B ≤ (2 ^ 64 - 1) * B := Nat.mul_le_mul_right _ (by omega_arith)
  have h2 : q * m ≤ (2 ^ 64 - 1) * m := Nat.mul_le_mul_right _ (by omega_arith)
  have h3 : (2 ^ 64 - 1) * B ≤ (2 ^ 64 - 1) * m := Nat.mul_le_mul_left _ (by omega_arith)
  omega_arith

/-- The low word of a number. -/
theorem wordsVal_low (m : Mem) (base : Addr) (d k : Nat) :
    wordsVal m base d (k + 1) % 2 ^ 64 = (word m base d).toNat := by
  rw [wordsVal, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (BitVec.isLt _)

theorem wordsVal_two (m : Mem) (base : Addr) (d : Nat) :
    wordsVal m base d 2 = (word m base d).toNat + 2 ^ 64 * (word m base (d + 8)).toNat := by
  simp only [wordsVal, Nat.mul_zero, Nat.add_zero]

/-- The arithmetic of `rowM`: the accumulator, one word down, and the carry
out, times `2⁶⁴`, are the sum `T₁ + q m`. -/
theorem rowM_math {T1 t0 W F m m0 M' q r4 L5 r5 V ca R : Nat}
    (hT1 : T1 = t0 + 2 ^ 64 * (W + R * F)) (hm : m = m0 + 2 ^ 64 * M')
    (h4 : 2 ^ 64 * r4 = q * m0 + t0) (h5 : L5 + R * r5 = W + q * M' + r4) (h6 : V + 2 ^ 128 * ca = F + r5) :
    2 ^ 64 * (L5 + R * V) + 2 ^ 64 * R * 2 ^ 128 * ca = T1 + q * m := by
  subst hT1 hm
  have e : 2 ^ 64 * (L5 + R * V) + 2 ^ 64 * R * 2 ^ 128 * ca = 2 ^ 64 * (L5 + R * r5) + 2 ^ 64 * R * F := by
    rw [show 2 ^ 64 * R * 2 ^ 128 * ca = 2 ^ 64 * R * (2 ^ 128 * ca) by grind]
    have := congrArg (2 ^ 64 * R * ·) h6
    simp only [Nat.mul_add] at this
    grind
  rw [e, h5]
  grind

/-! ## An iteration -/

/-- The offsets of a multiplication: `[a]`, `[b]` and the modulus in the
working space and apart from the accumulator (`n + 1` words at `acc`, and
`m'` above them). -/
structure MulLay (M : Mod) (size acc a b : Nat) : Prop where
  n0 : 0 < M.n
  acc_le : acc + 8 * (M.n + 2) ≤ size
  a_le : a + 8 * M.n ≤ size
  b_le : b + 8 * M.n ≤ size
  mo_le : M.mo + 8 * M.n ≤ size
  acc4 : acc % 4 = 0
  sa : a + 8 * M.n ≤ acc ∨ acc + 8 * (M.n + 2) ≤ a
  sb : b + 8 * M.n ≤ acc ∨ acc + 8 * (M.n + 2) ≤ b
  smo : M.mo + 8 * M.n ≤ acc ∨ acc + 8 * (M.n + 2) ≤ M.mo

/-- The registers the loop writes. -/
def clob : List Reg := [.r0, .r5, .r7, .r8, .r9, .r10, .r11, .r12]

/-- The invariant of the loop, before the iteration for word `k` of `[a]`:
the accumulator's `n + 1` words hold `T < 2m` with `2^(64 k) T ≡ A B`, for
the low `k` words `A` of `[a]`; `r5` points to word `k`, `r7` to the
modulus, and `r8` counts the words left. -/
structure LoopInv (base : Addr) (M : Mod) (acc a b m k : Nat) (s t : State) : Prop where
  r3 : At t base .r3 0
  r5 : At t base .r5 (a + 8 * k)
  r6 : At t base .r6 b
  r7 : At t base .r7 M.mo
  r8 : t.gpr .r8 = BitVec.ofNat 64 (M.n - k)
  out : Outside base acc (8 * (M.n + 1)) s.mem t.mem
  kp : Kp clob s t
  lt : wordsVal t.mem base acc (M.n + 1) < 2 * m
  cong : ∃ U, 2 ^ (64 * k) * wordsVal t.mem base acc (M.n + 1) =
    wordsVal s.mem base a k * wordsVal s.mem base b M.n + U * m

theorem kp_clob {s t : State} (h : Kp clob s t) {r : Reg} (hr : r ∉ clob := by decide) : t.gpr r = s.gpr r :=
  h.gpr r hr

theorem row_eq (M : Mod) (acc : Nat) : row M acc =
    ([.load .d .r9 .r5 0, .li .r0 0] : List Instr) ++ (macs .r6 0 acc acc M.n ++
    (([.load .d .r10 wb (acc + 8 * M.n), .addc .r10 .r10 .r0, .store .d .r10 wb (acc + 8 * M.n), .li .r12 0,
      .addze .r12 .r12] : List Instr) ++
    (([.load .d .r11 wb acc, .load .d .r10 wb (acc + 8 * (M.n + 1)), .mul .r9 .r11 .r10, .load .d .r10 .r7 0,
      .mulhu .r0 .r9 .r10, .mul .r10 .r9 .r10, .addc .r10 .r10 .r11, .addze .r0 .r0] : List Instr) ++
    (macs .r7 8 (acc + 8) acc (M.n - 1) ++
    (([.load .d .r10 wb (acc + 8 * M.n), .addc .r10 .r10 .r0, .store .d .r10 wb (acc + 8 * (M.n - 1)),
      .addze .r12 .r12, .store .d .r12 wb (acc + 8 * M.n)] : List Instr) ++
    ([.addi .r5 .r5 8, .subi .r8 .r8 1] : List Instr)))))) := by
  simp only [row, rowB, rowM, List.append_assoc]

/-- An iteration of the loop. -/
theorem row_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {M : Mod} {acc a b m k : Nat}
    (hL : MulLay M size acc a b) (hk : k < M.n) (hm : wordsVal s.mem base M.mo M.n = m)
    (hinv : (m * (word s.mem base (acc + 8 * (M.n + 1))).toNat + 1) % 2 ^ 64 = 0)
    (hB : wordsVal s.mem base b M.n < m) {t : State} (I : LoopInv base M acc a b m k s t) :
    WP isa (.block (row M acc)) t fun u => LoopInv base M acc a b m (k + 1) s u := by
  have hn := hs.nowrap
  have hs15 := hs.small
  obtain ⟨n0, acc_le, a_le, b_le, mo_le, acc4, sa, sb, smo⟩ := hL
  obtain ⟨N, hN⟩ : ∃ N, M.n = N + 1 := ⟨M.n - 1, by omega⟩
  have ht := I.kp.ws hs
  rw [row_eq]
  -- u
  have hat : word t.mem base (a + 8 * k + 0) = word s.mem base (a + 8 * k) :=
    I.out.word (by omega) (by omega)
  refine wp_append (wp_step (ld_ok ht I.r5 (by decide) (by decide) (d := 0) (by omega))
    (wp_step (exec_li (by decide)) (WP.block_nil ?_)))
  rw [hat]
  generalize hu : word s.mem base (a + 8 * k) = u
  -- T += u [b]
  refine wp_append (WP.mono (macs_ok ((ht.write _ _).write _ _) ((I.r6.write _).write _) ((I.r3.write _).write _)
    (rs := .r6) (src := 0) (rd := acc) (dst := acc) (W := M.n) (by decide) (by decide) acc4 acc4 (by omega)
    (by omega) (by omega) (Nat.le_refl _) (by omega) (Nat.le_refl _)) fun t₂ ⟨O₂, V₂, K₂⟩ => ?_)
  simp only [write_gpr, write_mem, reduceCtorEq, ite_false, ite_true, Nat.add_zero] at O₂ V₂
  rw [show (BitVec.ofNat 64 0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at V₂
  have K₁₂ : Kp [.r0, .r9, .r10, .r11, .r12] t t₂ :=
    ((Kp.write t _ (by decide)).trans (Kp.write _ _ (by decide))).trans (K₂.mono (by decide))
  refine wp_append (WP.mono (topB_ok (K₁₂.ws ht) (K₁₂.at I.r3) (d := acc + 8 * M.n) (by omega) (by omega))
    fun t₃ ⟨O₃, V₃, K₃⟩ => ?_)
  have K₁₃ : Kp [.r0, .r9, .r10, .r11, .r12] t t₃ := K₁₂.trans (K₃.mono (by decide))
  have Ot₃ : Outside base acc (8 * (M.n + 1)) s.mem t₃.mem :=
    I.out.trans ((O₂.mono (Nat.le_refl _) (by omega)).trans (O₃.mono (by omega) (by omega)))
  -- The accumulator after the first row, with its top word in `r12`: `T₁ = T + u B`.
  generalize hT : wordsVal t.mem base acc (M.n + 1) = T at I
  generalize hTB : wordsVal s.mem base b M.n = B at hB
  have hbt : wordsVal t.mem base b M.n = B := by rw [← hTB]; exact I.out.wordsVal (by omega) (by omega)
  rw [hbt] at V₂
  generalize hc₃ : (t₃.gpr .r12).toNat = c₃ at V₃
  have hT1 : wordsVal t₃.mem base acc (M.n + 1) + 2 ^ (64 * (M.n + 1)) * c₃ = T + u.toNat * B := by
    rw [wordsVal_succ_top, O₃.wordsVal (by omega) (by omega), show 64 * (M.n + 1) = 64 + 64 * M.n by omega,
      Nat.pow_add, ← hT, wordsVal_succ_top]
    have h2 : word t₂.mem base (acc + 8 * M.n) = word t.mem base (acc + 8 * M.n) := O₂.word (by omega) (by omega)
    rw [h2] at V₃
    generalize 2 ^ (64 * M.n) = P at *
    have e := congrArg (P * ·) V₃
    simp only [Nat.mul_add] at e
    grind
  generalize hT1v : wordsVal t₃.mem base acc (M.n + 1) + 2 ^ (64 * (M.n + 1)) * c₃ = T1 at hT1
  -- q, and the first step of its row.
  refine wp_append (WP.mono (qStart_ok (K₁₃.ws ht) (K₁₃.at I.r3) (K₁₃.at I.r7) (a := acc)
    (mi := acc + 8 * (M.n + 1)) acc4 (by omega) (by omega) (by omega) (by omega))
    fun t₄ ⟨q₄, ⟨lo, hlo, V₄⟩, M₄, K₄⟩ => ?_)
  have hmi : word t₃.mem base (acc + 8 * (M.n + 1)) = word s.mem base (acc + 8 * (M.n + 1)) :=
    Ot₃.word (by omega) (by omega)
  have hm0 : word t₃.mem base M.mo = word s.mem base M.mo := Ot₃.word (by omega) (by omega)
  have ht0 : (word t₃.mem base acc).toNat = T1 % 2 ^ 64 := by
    rw [← hT1v, show 64 * (M.n + 1) = 64 + 64 * M.n by omega, Nat.pow_add, Nat.mul_assoc, Nat.add_mul_mod_self_left,
      wordsVal_low]
  rw [hmi, ht0] at q₄
  rw [hm0, ht0] at V₄
  generalize hq : (t₄.gpr .r9).toNat = q at q₄ V₄
  have hq64 : q < 2 ^ 64 := hq ▸ BitVec.isLt _
  generalize hM' : wordsVal s.mem base (M.mo + 8) N = M'
  have hmM : m = (word s.mem base M.mo).toNat + 2 ^ 64 * M' := by
    rw [← hm, ← hM', hN]; rfl
  have hlo0 : lo = 0 := by
    have hl := mont_low (T1 % 2 ^ 64) (word s.mem base (acc + 8 * (M.n + 1))).toNat m hinv
    rw [← q₄, hmM] at hl
    have : (lo + 2 ^ 64 * (t₄.gpr .r0).toNat) % 2 ^ 64 = lo := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo]
    rw [V₄] at this
    rw [← this]
    have e : T1 % 2 ^ 64 + q * ((word s.mem base M.mo).toNat + 2 ^ 64 * M') =
      (q * (word s.mem base M.mo).toNat + T1 % 2 ^ 64) + 2 ^ 64 * (q * M') := by grind
    rw [e, Nat.add_mul_mod_self_left] at hl
    exact hl
  rw [hlo0, Nat.zero_add] at V₄
  -- The rest of the modulus's row.
  have h7₄ : At t₄ base .r7 M.mo := K₄.at (K₁₃.at I.r7)
  refine wp_append (WP.mono (macs_ok (K₄.ws (K₁₃.ws ht)) h7₄ (K₄.at (K₁₃.at I.r3)) (rs := .r7) (K := M.mo) (src := 8)
    (rd := acc + 8) (dst := acc) (W := M.n - 1) (by decide) (by decide) (by omega) acc4 (by omega) (by omega)
    (by omega) (by omega) (by omega) (Nat.le_refl _)) fun t₅ ⟨O₅, V₅, K₅⟩ => ?_)
  rw [M₄, hq] at V₅
  refine wp_append (WP.mono (topQ_ok (K₅.ws (K₄.ws (K₁₃.ws ht))) (K₅.at (K₄.at (K₁₃.at I.r3)))
    (e := acc + 8 * (M.n - 1)) (f := acc + 8 * M.n) (by omega) (by omega) (by omega)) fun t₆ ⟨O₆, V₆, K₆⟩ => ?_)
  have K₃₆ : Kp [.r0, .r9, .r10, .r11, .r12] t₃ t₆ :=
    ((K₄.mono (by decide)).trans (K₅.mono (by decide))).trans (K₆.mono (by decide))
  -- The pointers and the count.
  refine wp_step (exec_addi (by decide) (by decide)) ?_
  refine wp_step (exec_subi (by decide) (by decide)) (WP.block_nil ?_)
  have Ot₆ : Outside base acc (8 * (M.n + 1)) s.mem t₆.mem := by
    rw [← M₄] at Ot₃
    exact Ot₃.trans ((O₅.mono (Nat.le_refl _) (by omega)).trans (O₆.mono (by omega) (by omega)))
  -- The accumulator after the second row.
  have hf₅ : word t₅.mem base (acc + 8 * M.n) = word t₃.mem base (acc + 8 * M.n) := by
    rw [← M₄]; exact O₅.word (by omega) (by omega)
  have h12₅ : (t₅.gpr .r12).toNat = c₃ := by
    rw [K₅.g (r := .r12) (by decide), K₄.g (r := .r12) (by decide), hc₃]
  rw [hf₅, h12₅] at V₆
  have hM't : wordsVal t₃.mem base (M.mo + 8) (M.n - 1) = M' := by
    rw [← hM', show M.n - 1 = N by omega]; exact Ot₃.wordsVal (by omega) (by omega)
  rw [hM't] at V₅
  have hT1s : T1 = T1 % 2 ^ 64 + 2 ^ 64 * (wordsVal t₃.mem base (acc + 8) (M.n - 1) + 2 ^ (64 * (M.n - 1)) *
      ((word t₃.mem base (acc + 8 * M.n)).toNat + 2 ^ 64 * c₃)) := by
    rw [← ht0, ← hT1v]
    have e1 : wordsVal t₃.mem base acc (M.n + 1) = (word t₃.mem base acc).toNat +
        2 ^ 64 * wordsVal t₃.mem base (acc + 8) M.n := rfl
    have e2 := wordsVal_succ_top t₃.mem base (acc + 8) (M.n - 1)
    rw [show M.n - 1 + 1 = M.n by omega, show acc + 8 + 8 * (M.n - 1) = acc + 8 * M.n by omega] at e2
    have e3 : 2 ^ (64 * (M.n + 1)) = 2 ^ 64 * 2 ^ (64 * (M.n - 1)) * 2 ^ 64 := by
      rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
    rw [e1, e2, e3]
    generalize 2 ^ (64 * (M.n - 1)) = R
    grind
  have hT' : wordsVal t₆.mem base acc (M.n + 1) = wordsVal t₅.mem base acc (M.n - 1) + 2 ^ (64 * (M.n - 1)) *
      ((word t₆.mem base (acc + 8 * (M.n - 1))).toNat + 2 ^ 64 * (word t₆.mem base (acc + 8 * M.n)).toNat) := by
    rw [show M.n + 1 = M.n - 1 + 2 by omega, wordsVal_append, wordsVal_two, O₆.wordsVal (by omega) (by omega),
      show acc + 8 * (M.n - 1) + 8 = acc + 8 * M.n by omega]
  have hmath := rowM_math hT1s hmM V₄ V₅ V₆
  rw [← hT'] at hmath
  have hrow := row_lt I.lt u.isLt hB hq64
  have hX : 2 * m ≤ 2 ^ (64 * (M.n - 1)) * 2 ^ 128 := by
    have : m < 2 ^ (64 * M.n) := by rw [← hm]; exact wordsVal_lt _ _ _ _
    rw [← Nat.pow_add, show 64 * (M.n - 1) + 128 = 64 * M.n + 64 by omega, Nat.pow_add]
    have : 2 ≤ 2 ^ 64 := by decide
    have := Nat.mul_le_mul_left (2 ^ (64 * M.n)) this
    omega
  have hca : t₆.ca.toNat = 0 := by
    rcases Nat.eq_zero_or_pos t₆.ca.toNat with h | h
    · exact h
    · exfalso
      have : 2 ^ 64 * (2 ^ (64 * (M.n - 1)) * 2 ^ 128) ≤ 2 ^ 64 * 2 ^ (64 * (M.n - 1)) * 2 ^ 128 * t₆.ca.toNat := by
        rw [Nat.mul_assoc (2 ^ 64)]; exact Nat.le_mul_of_pos_right _ h
      have := Nat.mul_le_mul_left (2 ^ 64) hX
      rw [hT1] at hmath
      omega
  rw [hca, Nat.mul_zero, Nat.add_zero, hT1] at hmath
  generalize hT'v : wordsVal t₆.mem base acc (M.n + 1) = T' at hmath
  refine ⟨?_, ?_, ?_, ?_, ?_, Ot₆, ?_, ?_, ?_⟩
  · simp only [At, write_gpr, reduceCtorEq, ite_false]; rw [K₃₆.g, K₁₃.g]; exact I.r3
  · simp only [At, write_gpr, reduceCtorEq, ite_false, ite_true]
    rw [K₃₆.g, K₁₃.g, I.r5, off_add, show a + 8 * k + 8 = a + 8 * (k + 1) by omega]
  · simp only [At, write_gpr, reduceCtorEq, ite_false]; rw [K₃₆.g, K₁₃.g]; exact I.r6
  · simp only [At, write_gpr, reduceCtorEq, ite_false]; rw [K₃₆.g, K₁₃.g]; exact I.r7
  · simp only [write_gpr, reduceCtorEq, ite_false, ite_true]
    rw [K₃₆.g, K₁₃.g, I.r8]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have : M.n < 2 ^ 15 := by omega
    omega
  · exact I.kp.trans (((K₁₃.trans K₃₆).mono (by decide)).trans
      ((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide))))
  · simp only [write_mem]
    rw [hT'v]
    have : 2 ^ 64 * T' < 2 ^ 64 * (2 * m) := by omega
    exact Nat.lt_of_mul_lt_mul_left this
  · obtain ⟨U, hU⟩ := I.cong
    rw [hT, hTB] at hU
    refine ⟨U + q * 2 ^ (64 * k), ?_⟩
    simp only [write_mem]
    rw [hT'v]
    have hA : wordsVal s.mem base a (k + 1) = wordsVal s.mem base a k + 2 ^ (64 * k) * u.toNat := by
      rw [wordsVal_succ_top, hu]
    rw [hA, show 64 * (k + 1) = 64 * k + 64 by omega, Nat.pow_add, Nat.mul_assoc, hmath, Nat.mul_add, Nat.mul_add, hU]
    grind

end VG.Proof.Mont.PPC64LE

namespace VG.Proof.Mont.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Mont.PPC64LE VG.Proof.Mont

theorem eval_nonzero_ofNat {s : State} {r : Reg} {x : Nat} (h : s.gpr r = BitVec.ofNat 64 x) (hx : x < 2 ^ 64) :
    isa.eval (.nonzero .d r) s = some (decide (x ≠ 0)) := by
  simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, h, Option.some.injEq]
  by_cases hx0 : x = 0
  · subst hx0; rfl
  · have : BitVec.ofNat 64 x ≠ 0 := fun e => hx0 (by
      have := congrArg BitVec.toNat e
      rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at this)
    exact (bne_iff_ne.mpr this).trans (decide_eq_true hx0).symm

/-- The loop of `mul`: from the invariant at word 0 to the invariant at `n`. -/
theorem loop_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {M : Mod} {acc a b m : Nat}
    (hL : MulLay M size acc a b) (hm : wordsVal s.mem base M.mo M.n = m)
    (hinv : (m * (word s.mem base (acc + 8 * (M.n + 1))).toNat + 1) % 2 ^ 64 = 0)
    (hB : wordsVal s.mem base b M.n < m) {t : State} (h0 : LoopInv base M acc a b m 0 s t) :
    WP isa (.loop (.block (row M acc)) (.nonzero .d .r8)) t fun u => LoopInv base M acc a b m M.n s u := by
  have hD15 : M.n < 2 ^ 15 := by have := hs.small; have := hL.acc_le; omega_arith
  refine WP.loop (M := isa)
    (fun n t' => ∃ k, n = M.n - k ∧ k < M.n ∧ LoopInv base M acc a b m k s t') ?_ M.n t ⟨0, rfl, hL.n0, h0⟩
  rintro n t' ⟨k, rfl, hk, I⟩
  refine WP.mono (row_ok hs hL hk hm hinv hB I) fun u I' => ?_
  have he := eval_nonzero_ofNat I'.r8 (x := M.n - (k + 1)) (by omega_arith)
  by_cases hk1 : k + 1 = M.n
  · exact .inl ⟨by rw [he]; simp [hk1], hk1 ▸ I'⟩
  · exact .inr ⟨by rw [he]; simp; omega_arith, M.n - (k + 1), by omega_arith, k + 1, rfl, by omega_arith, I'⟩

end VG.Proof.Mont.PPC64LE
