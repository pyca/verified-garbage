module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Mac
import VerifiedGarbage.Proof.Mont.X86.Square.Scalar
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.Step
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.SelectX

/-! # A product row at a run-time width

`mulRow`'s loop, four words or one at a time: after `j` words, with the pointers
at word `p` (`Run`), the accumulator's first `j` words and the carry `ebx` hold
`c` times the source's first `j` words, plus (for an added row) the
accumulator's first `j` words before. `rowLoop_ok`: the loop; the tails carry
`ebx` into the two words after (`tailAdd_ok`, its sum if it fits) or write them (`tailSet_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

/-- After `j` words of a row, its pointers at word `p`. -/
structure Run (set : Bool) (s₀ : State) (W : Addr) (x y N j p : Nat) (t : State) : Prop where
  keep : Keeps [.eax, .ebx, .edx, .ebp, .edi, .esi] s₀ t
  px : PtrAt t W .edi (x + 4 * p)
  py : PtrAt t W .ebp (y + 4 * p)
  cnt : (t.gpr .esi).toNat = 4 * (N - p)
  pj : p ≤ j
  frame : Outside W y (4 * j) s₀.mem t.mem
  value : val32 t.mem W y j + 2 ^ (32 * j) * (t.gpr .ebx).toNat =
    (if set then 0 else val32 s₀.mem W y j) + (s₀.gpr .ecx).toNat * val32 s₀.mem W x j

theorem acc_step {V K P T X c Xs b lo hi : Nat} (hv : V + P * K = b + c * Xs)
    (hl : lo + 2 ^ 32 * hi = c * X + K + T) :
    V + P * lo + P * 2 ^ 32 * hi = (b + P * T) + c * (Xs + P * X) := by
  have e : P * lo + P * 2 ^ 32 * hi = P * (c * X + K + T) := by rw [← hl, Nat.mul_add, Nat.mul_assoc]
  rw [Nat.add_assoc, e]
  grind

variable {is : List Instr} {Q : State → Prop}

/-- One word of a row, at the pointers' displacement `4 (j - p)`. -/
theorem run_mac {set : Bool} {s₀ t : State} {W : Addr} {Z x y N j p : Nat} (hw : Ws s₀ W Z)
    (hxz : x + 4 * N ≤ Z) (hyz : y + 4 * (N + 2) ≤ Z) (sep : x + 4 * N ≤ y ∨ y + 4 * (N + 2) ≤ x)
    (R : Run set s₀ W x y N j p t) (hj : j < N) {d : Nat} (hd : 4 * (j - p) = d)
    (k : ∀ u, Run set s₀ W x y N (j + 1) p u → WP isa (.block is) u Q) :
    WP isa (.block ((if set then macSet else macWord) d ++ is)) t Q := by
  subst hd
  have hn := hw.nowrap
  have pj := R.pj
  have ht := hw.of_keeps R.keep
  have ex : x + 4 * p + 4 * (j - p) = x + 4 * j := by omega
  have ey : y + 4 * p + 4 * (j - p) = y + 4 * j := by omega
  have X : w32 t.mem W (x + 4 * j) = w32 s₀.mem W (x + 4 * j) := R.frame.w32 (by omega) (by omega)
  have T : w32 t.mem W (y + 4 * j) = w32 s₀.mem W (y + 4 * j) := R.frame.w32 (by omega) (by omega)
  have ecx : (t.gpr .ecx).toNat = (s₀.gpr .ecx).toNat := by rw [R.keep.1 _ (by decide)]
  have post : ∀ (u : State) (v : Nat), u.mem = t.mem.writeW (off W (y + 4 * j)) (BitVec.ofNat 32 v) →
      Keeps [.eax, .ebx, .edx] t u →
      v % 2 ^ 32 + 2 ^ 32 * (u.gpr .ebx).toNat =
        (s₀.gpr .ecx).toNat * w32 s₀.mem W (x + 4 * j) + (t.gpr .ebx).toNat +
          (if set then 0 else w32 s₀.mem W (y + 4 * j)) →
      Run set s₀ W x y N (j + 1) p u := by
    intro u v mu Ku vu
    have Ow := writeW32_outside t.mem W (d := y + 4 * j) (BitVec.ofNat 32 v) (by omega)
    rw [← mu] at Ow
    refine ⟨R.keep.trans (Ku.mono (by decide)), ?_, ?_, ?_, by omega,
      (R.frame.mono (Nat.le_refl _) (by omega)).trans (Ow.mono (by omega) (by omega)), ?_⟩
    · rw [PtrAt, Ku.1 _ (by decide)]; exact R.px
    · rw [PtrAt, Ku.1 _ (by decide)]; exact R.py
    · rw [Ku.1 _ (by decide)]; exact R.cnt
    · have lo : w32 u.mem W (y + 4 * j) = v % 2 ^ 32 := by
        rw [mu, w32_write_self, BitVec.toNat_ofNat]
      have pre : val32 u.mem W y j = val32 t.mem W y j := Ow.val32 (.inl (by omega)) (by omega)
      rw [val32_succ, pre, lo, val32_succ s₀.mem W x j, show 32 * (j + 1) = 32 * j + 32 by omega,
        Nat.pow_add]
      have V := R.value
      cases set
      · simp only [Bool.false_eq_true, ite_false] at V vu ⊢
        rw [val32_succ s₀.mem W y j]
        exact acc_step V vu
      · simp only [ite_true, Nat.add_zero] at V vu ⊢
        have := acc_step (T := 0) V (by rw [Nat.add_zero]; exact vu)
        simpa only [Nat.mul_zero, Nat.add_zero] using this
  cases set
  · simp only [Bool.false_eq_true, ite_false]
    refine macWord_ok ht R.px R.py (by omega) (by omega) fun u mu bu Ku => k u (post u _ (by rw [mu, ey]) Ku ?_)
    rw [bu, ex, ey, X, T, ecx, Nat.mod_add_div]
    simp
  · simp only [ite_true]
    refine macSet_ok ht R.px R.py (by omega) (by omega) fun u mu bu Ku => k u (post u _ (by rw [mu, ey]) Ku ?_)
    rw [bu, ex, X, ecx, Nat.mod_add_div]
    simp

/-- The pointers moved up to word `j`, `k = j - p` words. -/
theorem run_adv {set : Bool} {s₀ t : State} {W : Addr} {x y N j p : Nat}
    (R : Run set s₀ W x y N j p t) (hjN : j ≤ N) (hk : 4 * (j - p) < 2 ^ 32) {d : Nat} (hd : 4 * (j - p) = d)
    (k : ∀ u, Run set s₀ W x y N j j u → u.zf = some (decide (j = N)) → WP isa (.block is) u Q) :
    WP isa (.block (advance d ++ is)) t Q := by
  subst hd
  have pj := R.pj
  simp only [advance, List.cons_append, List.nil_append]
  refine wp_addS rfl fun u₁ U₁ _ => wp_addS rfl fun u₂ U₂ _ => VG.Proof.Bignum.X86.CrtRt.wp_subXm rfl fun u U z _ => ?_
  have K : Keeps [.ebp, .edi, .esi] t u :=
    ((U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))).trans (U.keeps.mono (by decide))
  have m : u.mem = t.mem := by rw [U.mem, U₂.mem, U₁.mem]
  have hb : 4 * (N - p) < 2 ^ 32 := by have := (t.gpr .esi).isLt; rw [R.cnt] at this; exact this
  have esi : (u.gpr .esi).toNat = 4 * (N - j) := by
    rw [U.gpr, U₂.other _ (by decide), U₁.other _ (by decide), BitVec.toNat_sub, R.cnt, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hk]
    omega
  refine k u ⟨R.keep.trans (K.mono (by decide)), ?_, ?_, esi, Nat.le_refl _, by rw [m]; exact R.frame, ?_⟩ ?_
  · rw [PtrAt, U.other _ (by decide), U₂.other _ (by decide), U₁.gpr, ptr_add R.px, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hk]
    congr 2; omega
  · rw [PtrAt, U.other _ (by decide), U₂.gpr, U₁.other _ (by decide), ptr_add R.py, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hk]
    congr 2; omega
  · rw [m, U.other _ (by decide), U₂.other _ (by decide), U₁.other _ (by decide)]; exact R.value
  · have hz : u.gpr .esi = u₂.gpr .esi - BitVec.ofNat 32 (4 * (j - p)) := U.gpr
    rw [z, ← hz]
    congr 1
    by_cases e : j = N
    · simp only [e, decide_true, beq_iff_eq]
      exact BitVec.eq_of_toNat_eq (by rw [esi, e, Nat.sub_self]; rfl)
    · simp only [e, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro z0
      have := congrArg BitVec.toNat z0
      rw [esi] at this
      exact e (by simp at this; omega)

theorem Run.flags {set : Bool} {s₀ t u : State} {W : Addr} {x y N j p : Nat}
    (R : Run set s₀ W x y N j p t) (F : Fupd t u) : Run set s₀ W x y N j p u := by
  refine ⟨R.keep.trans (F.keeps _), ?_, ?_, ?_, R.pj, ?_, ?_⟩
  · simpa only [PtrAt, F.gpr] using R.px
  · simpa only [PtrAt, F.gpr] using R.py
  · simpa only [F.gpr] using R.cnt
  · simpa only [F.mem] using R.frame
  · simpa only [F.gpr, F.mem] using R.value

/-- `mulRow`'s loop. -/
abbrev rowBody (set : Bool) : Prog isa :=
  let mac := if set then macSet else macWord
  .seq (.block [.alu .cmp .esi (.imm 16)])
    (.seq (.ite .ae (.block (mac 0 ++ (mac 4 ++ (mac 8 ++ (mac 12 ++ advance 16))))) (.block (mac 0 ++ advance 4)))
      (.block [.alu .cmp .esi (.imm 0)]))

theorem rowLoop_ok {set : Bool} {s : State} {W : Addr} {Z x y N : Nat} (hw : Ws s W Z) (hN : 0 < N)
    (hxz : x + 4 * N ≤ Z) (hyz : y + 4 * (N + 2) ≤ Z) (sep : x + 4 * N ≤ y ∨ y + 4 * (N + 2) ≤ x)
    (px : PtrAt s W .edi x) (py : PtrAt s W .ebp y) (cnt : (s.gpr .esi).toNat = 4 * N)
    (ebx : s.gpr .ebx = 0) :
    WP isa (.loop (rowBody set) .ne) s (Run set s W x y N N N) := by
  have small : 4 * N < 2 ^ 32 := by have := (s.gpr .esi).isLt; omega
  have initial : Run set s W x y N 0 0 s := by
    refine ⟨Keeps.refl _ _, by simpa using px, by simpa using py, by simpa using cnt, Nat.le_refl _,
      Outside.refl _ _ _ _, ?_⟩
    simp [val32, ebx]
  refine WP.loop (M := isa)
    (fun rem t => ∃ i, rem = N - i ∧ i < N ∧ Run set s W x y N i i t) ?_ N s ⟨0, rfl, hN, initial⟩
  rintro rem t ⟨i, rfl, hi, R⟩
  have finish {u : State} {i' : Nat} (hi' : i < i') (hiN : i' ≤ N) (J : Run set s W x y N i' i' u)
      (z : u.zf = some (decide (i' = N))) :
      WP isa (.block [.alu .cmp .esi (.imm 0)]) u fun v =>
        (eval .ne v = some false ∧ Run set s W x y N N N v) ∨
        eval .ne v = some true ∧ ∃ rem', rem' < N - i ∧ ∃ i'', rem' = N - i'' ∧ i'' < N ∧
          Run set s W x y N i'' i'' v := by
    refine wp_cmpS rfl fun v F Z => WP.block_nil ?_
    have J' := J.flags F
    have word : u.gpr .esi = BitVec.ofNat 32 (4 * (N - i')) :=
      BitVec.eq_of_toNat_eq (by rw [J.cnt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
    have zero : v.zf = some (decide (i' = N)) := by
      rw [Z, word]
      change some ((BitVec.ofNat 32 (4 * (N - i')) - 0#32 == 0#32)) = _
      simp only [BitVec.sub_zero]
      apply congrArg some
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, decide_eq_true_eq]
      constructor
      · intro H
        have Hn := congrArg BitVec.toNat H
        simp only [BitVec.toNat_ofNat] at Hn
        omega
      · intro done
        simp [done]
    by_cases done : i' = N
    · exact .inl ⟨by simp only [eval, zero, done, decide_true, Option.map_some, Bool.not_true], done ▸ J'⟩
    · exact .inr ⟨by simp only [eval, zero, decide_eq_false done, Option.map_some, Bool.not_false],
        N - i', by omega, i', rfl, by omega, J'⟩
  refine WP.seq (VG.Proof.Mont.X86.Square.wp_cmpCF rfl fun u F C => WP.block_nil ?_)
  have R' := R.flags F
  have choose : eval .ae u = some (!decide (4 * (N - i) < 16)) := by
    change u.cf.map not = _
    rw [C, R.cnt]
    rfl
  refine WP.seq (WP.ite (!decide (4 * (N - i) < 16)) choose ?_ ?_)
  · intro yes
    have ik : i + 4 ≤ N := by
      have ge : ¬4 * (N - i) < 16 := by simpa using yes
      omega
    refine run_mac hw hxz hyz sep R' (by omega) (by omega) fun u₁ R₁ => ?_
    refine run_mac hw hxz hyz sep R₁ (by omega) (by omega) fun u₂ R₂ => ?_
    refine run_mac hw hxz hyz sep R₂ (by omega) (by omega) fun u₃ R₃ => ?_
    refine run_mac hw hxz hyz sep R₃ (by omega) (by omega) fun u₄ R₄ => ?_
    rw [← List.append_nil (advance 16)]
    exact run_adv R₄ (by omega) (by omega) (by omega) fun v J z => WP.block_nil (finish (by omega) (by omega) J z)
  · intro _
    refine run_mac hw hxz hyz sep R' hi (by omega) fun u₁ R₁ => ?_
    rw [← List.append_nil (advance 4)]
    exact run_adv R₁ (by omega) (by omega) (by omega) fun v J z => WP.block_nil (finish (by omega) (by omega) J z)

/-- The added row's tail: the carry `ebx` into the two words at `ebp = y + 4 N`, when the sum fits. -/
theorem tailAdd_ok {s₀ t : State} {W : Addr} {Z x y N : Nat} (hw : Ws s₀ W Z)
    (hyz : y + 4 * (N + 2) ≤ Z) (R : Run false s₀ W x y N N N t)
    (k : ∀ u, Keeps [.eax] t u → Outside W y (4 * (N + 2)) s₀.mem u.mem →
      (val32 s₀.mem W y (N + 2) + (s₀.gpr .ecx).toNat * val32 s₀.mem W x N < 2 ^ (32 * (N + 2)) →
        val32 u.mem W y (N + 2) = val32 s₀.mem W y (N + 2) + (s₀.gpr .ecx).toNat * val32 s₀.mem W x N) →
      WP isa (.block is) u Q) :
    WP isa (.block (([.mov .eax (.mem (at_ .ebp 0)), .alu .add .eax (.reg .ebx), .store (at_ .ebp 0) .eax,
      .mov .eax (.mem (at_ .ebp 4)), .alu .adc .eax (.imm 0), .store (at_ .ebp 4) .eax] : List Instr) ++ is)) t Q := by
  have hn := hw.nowrap
  have ht := hw.of_keeps R.keep
  simp only [List.cons_append, List.nil_append]
  refine wp_movS (readSrc_ptr ht R.py (d := 0) (by omega)) fun s₁ u₁ _ => ?_
  refine wp_addS rfl fun s₂ u₂ c₂ => ?_
  have K₂ : Keeps [.eax] t s₂ := (u₁.keeps.trans u₂.keeps)
  have py₂ : PtrAt s₂ W .ebp (y + 4 * N) := by rw [PtrAt, K₂.1 _ (by decide)]; exact R.py
  have hw₂ := ht.of_keeps K₂
  refine wp_storeS (by simpa using ea_ptr hw₂ py₂ (d := 0) (by omega)) (ws_write hw₂ (by omega)) fun s₃ m₃ => ?_
  have K₃ : Keeps [.eax] t s₃ := K₂.trans (m₃.keeps _)
  have py₃ : PtrAt s₃ W .ebp (y + 4 * N) := by rw [PtrAt, K₃.1 _ (by decide)]; exact R.py
  have hw₃ := ht.of_keeps K₃
  refine wp_movS (readSrc_ptr hw₃ py₃ (d := 4) (by omega)) fun s₄ u₄ cf₄ => ?_
  refine wp_adcS rfl (by rw [cf₄, m₃.cf]; exact c₂) fun s₅ u₅ _ => ?_
  have K₅ : Keeps [.eax] t s₅ := (K₃.trans u₄.keeps).trans u₅.keeps
  have py₅ : PtrAt s₅ W .ebp (y + 4 * N) := by rw [PtrAt, K₅.1 _ (by decide)]; exact R.py
  have hw₅ := ht.of_keeps K₅
  refine wp_storeS (by simpa using ea_ptr hw₅ py₅ (d := 4) (by omega)) (ws_write hw₅ (by omega)) fun u m₆ => ?_
  have K : Keeps [.eax] t u := K₅.trans (m₆.keeps _)
  -- The memory.
  have mt₂ : s₂.mem = t.mem := by rw [u₂.mem, u₁.mem]
  have m5 : s₅.mem = s₃.mem := by rw [u₅.mem, u₄.mem]
  rw [mt₂] at m₃
  rw [m5, m₃.mem] at m₆
  have W₀ := writeW32_outside t.mem W (d := y + 4 * N) (s₂.gpr .eax) (by omega)
  have W₁ := writeW32_outside (t.mem.writeW (off W (y + 4 * N)) (s₂.gpr .eax)) W (d := y + 4 * N + 4)
    (s₅.gpr .eax) (by omega)
  rw [← m₆.mem] at W₁
  have O2 : Outside W (y + 4 * N) 8 t.mem u.mem :=
    (W₀.mono (Nat.le_refl _) (by omega)).trans (W₁.mono (by omega) (by omega))
  have O : Outside W y (4 * (N + 2)) s₀.mem u.mem :=
    (R.frame.mono (Nat.le_refl _) (by omega)).trans (O2.mono (by omega) (by omega))
  refine k u K O fun hlt => ?_
  -- The words: the run's `N` words, then the two carried into.
  have T₀ : w32 t.mem W (y + 4 * N) = w32 s₀.mem W (y + 4 * N) := R.frame.w32 (by omega) (by omega)
  have T₁ : w32 t.mem W (y + 4 * N + 4) = w32 s₀.mem W (y + 4 * N + 4) := R.frame.w32 (by omega) (by omega)
  have pre : val32 u.mem W y N = val32 t.mem W y N := O2.val32 (.inl (by omega)) (by omega)
  have a₂ : s₂.gpr .eax = t.mem.readW (off W (y + 4 * N)) 32 + t.gpr .ebx := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), Nat.add_zero]
  have h0 : ∀ v : BitVec 32, v + 0 = v := BitVec.add_zero
  have a₅ : s₅.gpr .eax = s₃.mem.readW (off W (y + 4 * N + 4)) 32 +
      (BitVec.ofBool (decide (2 ^ 32 ≤ (s₁.gpr .eax).toNat + (s₁.gpr .ebx).toNat))).setWidth 32 := by
    rw [u₅.gpr, u₄.gpr, h0]
  rw [u₁.gpr, u₁.other _ (by decide), Nat.add_zero, m₃.mem] at a₅
  have t₁ : w32 (t.mem.writeW (off W (y + 4 * N)) (s₂.gpr .eax)) W (y + 4 * N + 4) = w32 t.mem W (y + 4 * N + 4) :=
    W₀.w32 (.inr (by omega)) (by omega)
  have hval : val32 u.mem W y (N + 2) = val32 u.mem W y N + 2 ^ (32 * N) *
      (w32 u.mem W (y + 4 * N) + 2 ^ 32 * w32 u.mem W (y + 4 * N + 4)) := by
    rw [val32_append]; simp only [val32, Nat.mul_zero, Nat.add_zero]
  have hval₀ : val32 s₀.mem W y (N + 2) = val32 s₀.mem W y N + 2 ^ (32 * N) *
      (w32 s₀.mem W (y + 4 * N) + 2 ^ 32 * w32 s₀.mem W (y + 4 * N + 4)) := by
    rw [val32_append]; simp only [val32, Nat.mul_zero, Nat.add_zero]
  have wN : w32 u.mem W (y + 4 * N) = (w32 t.mem W (y + 4 * N) + (t.gpr .ebx).toNat) % 2 ^ 32 := by
    rw [W₁.w32 (.inl (by omega)) (by omega), w32_write_self, a₂, BitVec.toNat_add]
  have wN1 : w32 u.mem W (y + 4 * N + 4) = (w32 t.mem W (y + 4 * N + 4) +
      (decide (2 ^ 32 ≤ w32 t.mem W (y + 4 * N) + (t.gpr .ebx).toNat)).toNat) % 2 ^ 32 := by
    rw [m₆.mem, w32_write_self, a₅, BitVec.toNat_add, ofBool_toNat]
    simp only [w32, Nat.add_zero] at t₁ ⊢
    rw [t₁]
  rw [T₀] at wN wN1
  rw [T₁] at wN1
  rw [hval, pre, wN, wN1, hval₀]
  have V := R.value
  simp only [Bool.false_eq_true, ite_false] at V
  have Kl := (t.gpr .ebx).isLt
  have T0l : w32 s₀.mem W (y + 4 * N) < 2 ^ 32 := (s₀.mem.readW _ 32).isLt
  have T1l : w32 s₀.mem W (y + 4 * N + 4) < 2 ^ 32 := (s₀.mem.readW _ 32).isLt
  generalize w32 s₀.mem W (y + 4 * N) = T0 at *
  generalize w32 s₀.mem W (y + 4 * N + 4) = T1 at *
  generalize (t.gpr .ebx).toNat = K at *
  rw [hval₀] at hlt
  have hP : 0 < 2 ^ (32 * N) := Nat.two_pow_pos _
  have small : K + T0 + 2 ^ 32 * T1 < 2 ^ 64 := by
    refine Nat.lt_of_mul_lt_mul_left (a := 2 ^ (32 * N)) ?_
    rw [show 2 ^ (32 * N) * 2 ^ 64 = 2 ^ (32 * (N + 2)) by rw [← Nat.pow_add]; congr 1]
    rw [Nat.mul_add (2 ^ (32 * N)), Nat.mul_add (2 ^ (32 * N))]
    rw [Nat.mul_add (2 ^ (32 * N))] at hlt
    omega
  have words : (T0 + K) % 2 ^ 32 + 2 ^ 32 * ((T1 + (decide (2 ^ 32 ≤ T0 + K)).toNat) % 2 ^ 32) =
      K + T0 + 2 ^ 32 * T1 := by
    by_cases hc : 2 ^ 32 ≤ T0 + K <;>
      simp only [hc, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega
  rw [words, Nat.mul_add (2 ^ (32 * N)), Nat.mul_add (2 ^ (32 * N)), Nat.mul_add (2 ^ (32 * N))]
  omega

/-- The first row's tail: the carry `ebx` and zero into the two words at `ebp = y + 4 N`. -/
theorem tailSet_ok {s₀ t : State} {W : Addr} {Z x y N : Nat} (hw : Ws s₀ W Z)
    (hyz : y + 4 * (N + 2) ≤ Z) (R : Run true s₀ W x y N N N t)
    (k : ∀ u, Keeps [.eax] t u → Outside W y (4 * (N + 2)) s₀.mem u.mem →
      val32 u.mem W y (N + 2) = (s₀.gpr .ecx).toNat * val32 s₀.mem W x N → WP isa (.block is) u Q) :
    WP isa (.block (([.store (at_ .ebp 0) .ebx, .mov .eax (.imm 0), .store (at_ .ebp 4) .eax] : List Instr) ++ is)) t Q := by
  have hn := hw.nowrap
  have ht := hw.of_keeps R.keep
  simp only [List.cons_append, List.nil_append]
  refine wp_storeS (by simpa using ea_ptr ht R.py (d := 0) (by omega)) (ws_write ht (by omega)) fun s₁ m₁ => ?_
  refine wp_movS rfl fun s₂ u₂ _ => ?_
  have K₂ : Keeps [.eax] t s₂ := (m₁.keeps _).trans u₂.keeps
  have py₂ : PtrAt s₂ W .ebp (y + 4 * N) := by rw [PtrAt, K₂.1 _ (by decide)]; exact R.py
  have hw₂ := ht.of_keeps K₂
  refine wp_storeS (by simpa using ea_ptr hw₂ py₂ (d := 4) (by omega)) (ws_write hw₂ (by omega)) fun u m₃ => ?_
  have K : Keeps [.eax] t u := K₂.trans (m₃.keeps _)
  have m₂ : s₂.mem = t.mem.writeW (off W (y + 4 * N)) (t.gpr .ebx) := by rw [u₂.mem, m₁.mem]
  rw [m₂, u₂.gpr] at m₃
  have W₀ := writeW32_outside t.mem W (d := y + 4 * N) (t.gpr .ebx) (by omega)
  have W₁ := writeW32_outside (t.mem.writeW (off W (y + 4 * N)) (t.gpr .ebx)) W (d := y + 4 * N + 4) 0 (by omega)
  rw [← m₃.mem] at W₁
  have O2 : Outside W (y + 4 * N) 8 t.mem u.mem :=
    (W₀.mono (Nat.le_refl _) (by omega)).trans (W₁.mono (by omega) (by omega))
  refine k u K ((R.frame.mono (Nat.le_refl _) (by omega)).trans (O2.mono (by omega) (by omega))) ?_
  have pre : val32 u.mem W y N = val32 t.mem W y N := O2.val32 (.inl (by omega)) (by omega)
  have wN : w32 u.mem W (y + 4 * N) = (t.gpr .ebx).toNat := by
    rw [W₁.w32 (.inl (by omega)) (by omega), w32_write_self]
  have wN1 : w32 u.mem W (y + 4 * N + 4) = 0 := by rw [m₃.mem, w32_write_self]; rfl
  rw [val32_append]
  simp only [val32, Nat.mul_zero, Nat.add_zero]
  rw [pre, wN, wN1, Nat.mul_zero, Nat.add_zero]
  have V := R.value
  simpa only [ite_true, Nat.zero_add] using V

end VG.Proof.Rsa.X86.InvBatchRt
