module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Prepare
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Ctx
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Stage
public import VerifiedGarbage.Impl.Bignum.X86.PrivPre
public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86.PrecomputeRt.Copy
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedRt.Key
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Validate
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Powers
import VerifiedGarbage.Proof.Framework.Offset

/-! # A factor's `R² mod p` at a run-time width (x86)

The count `w_p = max(2, ⌈L / 8⌉)` of a factor of `L` bytes (the header word
at `lenOff`), computed without a branch (`primeWords_ok`), and one doubled
`128 w_p` times modulo the context's modulus: `2^(128 w_p) mod M`
(`r2Prime_ok`), as `CrtRt.powerTwo` doubles to its own exponent.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PrivPre

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Impl.Bignum.X86.PrivPre (shl primeWords prepCore chunks reduceX fixStart fixStep fixMore r2Fix primeIn factorTest factor)
open VG.Proof.Bignum.X86.PublicRt (count1_zf countLoop widthB_ok wb)
open VG.Impl.Bignum.X86.PublicRt (widthB)

theorem dbl_pow (x k : Nat) : (x + x) * 2 ^ k = x * 2 ^ (k + 1) := by
  rw [Nat.pow_succ, ← Nat.two_mul, Nat.mul_comm 2 x, Nat.mul_assoc, Nat.mul_comm 2]

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `shl r k`: `r` doubled `k` times. -/
theorem shl_ok {r : Reg} (k : Nat)
    (h : ∀ u, Keeps [r] s u → u.mem = s.mem → (u.gpr r).toNat = (s.gpr r).toNat * 2 ^ k % 2 ^ 32 →
      WP isa (.block is) u Q) :
    WP isa (.block (shl r k ++ is)) s Q := by
  induction k generalizing s with
  | zero => exact h s (Keeps.refl _ _) rfl (by simp [Nat.mod_eq_of_lt (s.gpr r).isLt])
  | succ k ih =>
    simp only [shl, List.cons_append]
    refine wp_addS rfl fun t a _ => ih fun u K m e => h u ((a.keeps.mono fun _ h => h).trans K) (by rw [m, a.mem]) ?_
    rw [e, a.gpr, BitVec.toNat_add, Nat.mod_mul_mod, dbl_pow]

end

theorem primeWords_val (L : Nat) (h1 : 1 ≤ L) (h : L < 2 ^ 32 - 8) :
    let r := ((BitVec.ofNat 32 L + 7) >>> 3 : BitVec 32)
    (r + (r - 2) >>> 31).toNat = Spec.Rsa.primeWords L := by
  intro r
  have er : r.toNat = (L + 7) / 8 := by
    simp only [r, BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [show (7 : BitVec 32).toNat = 7 from rfl, Nat.mod_eq_of_lt (a := L) (by omega),
      Nat.mod_eq_of_lt (a := L + 7) (by omega)]
  simp only [Spec.Rsa.primeWords, Spec.Rsa.modulusWords]
  by_cases hs : 2 ≤ (L + 7) / 8
  · have et : ((r - 2) >>> 31).toNat = 0 := by
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow, er]
      rw [show (2 : BitVec 32).toNat = 2 from rfl] <;> omega
    rw [BitVec.toNat_add, er, et] <;> omega
  · have e1 : (L + 7) / 8 = 1 := by omega
    have et : ((r - 2) >>> 31).toNat = 1 := by
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow, er, e1]
      rw [show (2 : BitVec 32).toNat = 2 from rfl] <;> omega
    rw [BitVec.toNat_add, er, et, e1] <;> omega

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

/-- The count of a factor's doublings: `128 w_p`. -/
abbrev r2Exp (L : Nat) : Nat := 128 * Spec.Rsa.primeWords L

/-- `prepCore`: `prepBase` but its power of two. -/
theorem prepCore_ok (h : In Ex base bytes len args s) (c : Ctx) :
    WP isa (prepCore c) s fun u =>
      Frame (frameR base (s.gpr .esp) (baseR len c)) s.mem u.mem ∧
      sv u.mem base len c 0 = safeM (sv s.mem base len c 0) ∧ sv u.mem base len c 3 = 1 ∧
      (safeM (sv s.mem base len c 0) * w32 u.mem base invOff + 1) % 2 ^ 32 = 0 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have nw' := h.scratch.nowrap
  have f8 := h.slot_fit c (j := 8) (by decide)
  have g := bc_ge h.lower' c
  have bw := bc_eq_cwc len c
  have s01 : lo len (.slot c 0) + st len c ≤ lo len (.slot c 1) := sl_le (len := len) c (by decide)
  have s13 : lo len (.slot c 1) + st len c ≤ lo len (.slot c 3) := sl_le (len := len) c (by decide)
  have s34 : lo len (.slot c 3) + st len c ≤ lo len (.slot c 4) := sl_le (len := len) c (by decide)
  have s47 : lo len (.slot c 4) + st len c ≤ lo len (.slot c 7) := sl_le (len := len) c (by decide)
  have s78 : lo len (.slot c 7) + st len c ≤ lo len (.slot c 8) := sl_le (len := len) c (by decide)
  have z0 : lo len (.slot c 0) = numBase := sl_zero len c
  have est : st len c = 2 * bc len c + 32 := rfl
  have nb : numBase = 3336 := rfl
  have cb1 : cb len (one c) = bc len c := by simp [cb, one]
  have cw1 : cw len (one c) = cwc len c := by simp [cw, cwc, cb, one]
  have hk : ∃ k, cwc len c = k + 1 := ⟨cwc len c - 1, by omega_arith⟩
  obtain ⟨k, ek⟩ := hk
  have fitP : ∀ p ∈ baseR len c, p.1 + p.2 ≤ bytes := by
    intro p hp
    simp only [baseR, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> (try simp only [invOff]) <;> omega_arith
  let M₀ := sv s.mem base len c 0
  unfold prepCore
  -- One in slot 3, three in slot 7.
  refine WP.seq (WP.mono (setSmall_ok (x := .slot c 3) h (one_ok c) (by rw [cb1]; omega_arith) (v := 1) (by decide))
    fun u₁ ⟨O₁, V₁, K₁⟩ => ?_)
  simp only [cb1, cw1] at O₁ V₁
  have h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega_arith))
  refine WP.seq (WP.mono (setSmall_ok (x := .slot c 7) h₁ (one_ok c) (by rw [cb1]; omega_arith) (v := 3) (by decide))
    fun u₂ ⟨O₂, V₂, K₂⟩ => ?_)
  simp only [cb1, cw1] at O₂ V₂
  have h₂ := h₁.keep K₂ (by decide) (by decide) (O₂.mono (Nat.zero_le _) (by omega_arith))
  have M₂ : val32 u₂.mem base numBase (cwc len c) = M₀ := by
    rw [O₂.val32 (by omega_arith) (by omega_arith), O₁.val32 (by omega_arith) (by omega_arith), ← z0]
  have one₂ : val32 u₂.mem base (lo len (.slot c 3)) (cwc len c) = 1 := by
    rw [O₂.val32 (by omega_arith) (by omega_arith), V₁]
  -- `ecx`: whether the modulus is above one.
  refine WP.seq (WP.mono (lessThan_ok (a := .slot c 3) (b := .slot c 0) h₂ (one_ok c) (by rw [cb1]; omega_arith)
    (by rw [cb1]; omega_arith)) fun u₃ ⟨m₃, e₃, K₃⟩ => ?_)
  simp only [cw1, one₂, z0, M₂] at e₃
  have h₃ := h₂.regs (K₃.mono (by decide) : Keeps [.eax, .ecx, .edx, .ebp, .esi] u₂ u₃) m₃
  -- `ecx`: whether it is to be replaced.
  refine WP.seq (wp_movS (readSrc_sc h₃.scratch (d := numBase) (by omega_arith)) fun v₁ a₁ _ => ?_)
  refine wp_logicS (.inl rfl) rfl fun v₂ a₂ => wp_movS rfl fun v₃ a₃ _ => wp_subS rfl fun v₄ a₄ _ => ?_
  refine wp_logicS (.inl rfl) rfl fun v₅ a₅ => wp_logicS (.inr rfl) rfl fun v₆ a₆ => WP.block_nil ?_
  have mem₆ : v₆.mem = u₂.mem := by rw [a₆.mem, a₅.mem, a₄.mem, a₃.mem, a₂.mem, a₁.mem, m₃]
  have par : (u₂.mem.readW (off base numBase) 32).toNat % 2 = M₀ % 2 := by
    rw [← M₂, ek, VG.Proof.Mont.X86.Dynamic.val32_parity]
  have edx₂ : v₂.gpr .edx = u₂.mem.readW (off base numBase) 32 &&& 1 := by
    rw [a₂.gpr]; show v₁.gpr .edx &&& 1 = _; rw [a₁.gpr, m₃]
  have eax₄ : v₄.gpr .eax = (0 : BitVec 32) - (u₂.mem.readW (off base numBase) 32 &&& 1) := by
    rw [a₄.gpr, a₃.gpr, a₃.other _ (by decide), edx₂]
  have ecx₄ : v₄.gpr .ecx = cmask (decide (1 < M₀)) := by
    rw [a₄.other _ (by decide), a₃.other _ (by decide), a₂.other _ (by decide), a₁.other _ (by decide), e₃]
  have ecx₅ : v₅.gpr .ecx = v₄.gpr .ecx &&& v₄.gpr .eax := by rw [a₅.gpr]; rfl
  have ecx₆ : v₆.gpr .ecx = cmask (!(decide (1 < M₀) && decide (M₀ % 2 = 1))) := by
    rw [a₆.gpr]
    show v₅.gpr .ecx ^^^ BitVec.allOnes 32 = _
    rw [ecx₅, ecx₄, eax₄, zero_sub_and_one, par, cmask_and, cmask_not]
  have K₆ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v₆ :=
    (((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₃.mono (by decide))).trans
      ((((((a₁.keeps.mono (by decide)).trans (a₂.keeps.mono (by decide))).trans (a₃.keeps.mono (by decide))).trans
        (a₄.keeps.mono (by decide))).trans (a₅.keeps.mono (by decide))).trans (a₆.keeps.mono (by decide)))
  have h₆ := h₂.regs ((K₃.mono (by decide) : Keeps [.eax, .ecx, .edx, .ebp, .esi] u₂ u₃).trans
    ((((((a₁.keeps.mono (by decide)).trans (a₂.keeps.mono (by decide))).trans (a₃.keeps.mono (by decide))).trans
        (a₄.keeps.mono (by decide))).trans (a₅.keeps.mono (by decide))).trans (a₆.keeps.mono (by decide))) :
      Keeps [.eax, .ecx, .edx, .ebp, .esi] u₂ v₆) mem₆
  -- The modulus replaced by three where it is to be.
  refine WP.seq (WP.mono (select_ok (x := .slot c 7) (d := .slot c 0) h₆ (one_ok c) (by rw [cb1]; omega_arith)
    (by rw [cb1]; omega_arith) (by rw [cb1]; simp only [Apart]; omega_arith) ecx₆) fun u₇ ⟨O₇, V₇, K₇⟩ => ?_)
  simp only [cb1, cw1] at O₇ V₇
  have safe₇ : val32 u₇.mem base numBase (cwc len c) = safeM M₀ := by
    rw [← z0, V₇, mem₆]
    have three : val32 u₂.mem base (lo len (.slot c 7)) (cwc len c) = 3 := V₂
    rw [three, z0, M₂]
    unfold safeM
    by_cases hp : 1 < M₀ ∧ M₀ % 2 = 1
    · have e : (!(decide (1 < M₀) && decide (M₀ % 2 = 1))) = false := by simp [hp.1, hp.2]
      rw [e]; simp [hp]
    · have e : (!(decide (1 < M₀) && decide (M₀ % 2 = 1))) = true := by
        simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega_arith
      rw [e]; simp [hp]
  have h₇ := h₆.keep K₇ (by decide) (by decide) (O₇.mono (Nat.zero_le _) (by omega_arith))
  -- The inverse.
  have odd₇ : w32 u₇.mem base numBase % 2 = 1 := by
    rw [← VG.Proof.Mont.X86.Dynamic.val32_parity u₇.mem base numBase k, ← ek, safe₇]; exact safeM_odd _
  refine WP.mono (VG.Proof.Mont.X86.Dynamic.setupInverse_ok h₇.scratch (mo := numBase) (inv := invOff) (by omega_arith)
    (by simp only [invOff]; omega_arith) odd₇) fun u ⟨I₈, O₈, K₈⟩ => ?_
  have M₈ : val32 u.mem base numBase (cwc len c) = safeM M₀ := by
    rw [O₈.val32 (by simp only [invOff]; omega_arith) (by omega_arith), safe₇]
  refine ⟨?_, ?_, ?_, ?_, K₆.trans ((K₇.mono (by decide)).trans (K₈.mono (by decide)))⟩
  · have F₁ := frameR_of_outside (sp := s.gpr .esp) (ws := baseR len c) O₁ (by omega_arith) (by simp)
    have F₂ := frameR_of_outside (sp := s.gpr .esp) (ws := baseR len c) O₂ (by omega_arith) (by simp)
    have F₇ := frameR_of_outside (sp := s.gpr .esp) (ws := baseR len c) O₇ (by omega_arith) (by simp)
    have F₈ := frameR_of_outside (sp := s.gpr .esp) (ws := baseR len c) O₈ (by simp only [invOff]; omega_arith) (by simp)
    rw [mem₆] at F₇
    exact ((F₁.trans F₂).trans F₇).trans F₈
  · simp only [sv, z0]; rw [M₈]; simp only [M₀, sv, z0]
  · simp only [sv]
    rw [O₈.val32 (by simp only [invOff]; omega_arith) (by omega_arith), O₇.val32 (by omega_arith) (by omega_arith), mem₆,
      one₂]
  · rw [← safe₇, ek, val32, Nat.add_mul, Nat.mul_assoc, Nat.add_right_comm, Nat.add_mul_mod_self_left]
    exact I₈


/-- `x`, `R² mod n` as `loadX` leaves it: the wide slot 18's `2 B` bytes. -/
abbrev xv (m : Mem) (base : Addr) (len : Nat) : Nat := val32 m base (lo len (.slot .wide 18)) (2 * cwc len .wide)

theorem bc_wide_le (len : Nat) : bc len .wide ≤ 2 * bc len .half := by simp only [bc]; omega

theorem mod_mul_eq {a b k M : Nat} (h : a % M = b % M) : a * k % M = b * k % M := by
  rw [Nat.mul_mod, h, ← Nat.mul_mod]

/-- Two Montgomery reductions of the low half and one of the high half, added. -/
theorem redc2 {a b c R M lo hi : Nat} (V3 : c * R % M = lo * 1 % M) (V4 : a * R % M = c * 1 % M)
    (V5 : b * R % M = hi * 1 % M) : (a + b) % M * (R * R) % M = (lo + R * hi) % M := by
  rw [Nat.mul_one] at V3 V4 V5
  have e1 : a * R * R % M = lo % M := by rw [Nat.mul_mod (a * R), V4, ← Nat.mul_mod, V3]
  have e2 : b * R * R % M = hi * R % M := by rw [Nat.mul_mod (b * R), V5, ← Nat.mul_mod]
  rw [Nat.mod_mul_mod, Nat.add_mul, ← Nat.mul_assoc, ← Nat.mul_assoc, Nat.add_mod, e1, e2, ← Nat.add_mod,
    Nat.mul_comm hi R]

/-- The ranges `reduceX` and `r2Fix` change. -/
abbrev redR (len : Nat) (c : Ctx) : List (Nat × Nat) :=
  [(lo len (.slot c 1), 3 * bc len c + 56), (lo len (.slot c 4), bc len c), (lo len (.slot c 5), bc len c),
    (lo len (.slot c 6), bc len c)]

theorem redR_fit (h : In Ex base bytes len args s) (c : Ctx) : ∀ q ∈ redR len c, q.1 + q.2 ≤ bytes := by
  have f8 := h.slot_fit c (j := 8) (by decide)
  have est : st len c = 2 * bc len c + 32 := rfl
  have e4 : lo len (.slot c 4) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
  have e5 : lo len (.slot c 5) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
  have e6 : lo len (.slot c 6) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
  have p1 := slot_past1 len c (j := 8) (by decide)
  intro q hq
  simp only [redR, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith

theorem redR_low (len : Nat) (c : Ctx) : ∀ q ∈ redR len c, numBase + bc len c ≤ q.1 := by
  have e1 : lo len (.slot c 1) = numBase + st len c := by simp [lo]
  have est : st len c = 2 * bc len c + 32 := rfl
  have e14 : lo len (.slot c 1) + st len c ≤ lo len (.slot c 4) := sl_le c (by decide)
  have e45 : lo len (.slot c 4) + st len c ≤ lo len (.slot c 5) := sl_le c (by decide)
  have e56 : lo len (.slot c 5) + st len c ≤ lo len (.slot c 6) := sl_le c (by decide)
  intro q hq
  simp only [redR, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith

/-- `reduceX`: `x R⁻ᴷ mod M` into slot 4 for `K = chunks c`, for `x` below `2^(8 B)`. -/
theorem reduceX_ok {c : Ctx} {M : Nat} (C : CtxOk Ex base bytes len args c M s) (h3 : sv s.mem base len c 3 = 1)
    (hX : xv s.mem base len < 2 ^ (8 * bc len .wide)) :
    WP isa (reduceX c) s fun u =>
      CtxOk Ex base bytes len args c M u ∧ sv u.mem base len c 3 = 1 ∧ sv u.mem base len c 4 < M ∧
      sv u.mem base len c 4 * 2 ^ (8 * bc len c * chunks c) % M = xv s.mem base len % M ∧
      Frame (frameR base (s.gpr .esp) (redR len c)) s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  have h := C.inp
  have nw := h.scratch.nowrap
  have bl := h.bytes_lt
  have hM := C.gt
  have fit := redR_fit h c
  have low := redR_low len c
  have W18 := h.wide_fit (j := 18) (by decide)
  have bww := bc_eq_cwc len .wide
  have e9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide := rfl
  have e18w : lo len (.slot .wide 18) = numBase + 18 * st len .wide := rfl
  have estw : st len .wide = 2 * bc len .wide + 32 := rfl
  have nb : numBase = 3336 := rfl
  have one3 : ∀ {t : State}, sv t.mem base len c 3 = 1 → sv t.mem base len c 3 < M := fun e => by rw [e]; exact hM
  cases c with
  | wide =>
    have cb1 : cb len (one .wide) = bc len .wide := by simp [cb, one]
    have cw1 : cw len (one .wide) = cwc len .wide := by simp [cw, cwc, cb, one]
    have f8 := h.slot_fit .wide (j := 8) (by decide)
    have e5 : lo len (.slot .wide 5) = numBase + 5 * st len .wide := rfl
    have e8 : lo len (.slot .wide 8) = numBase + 8 * st len .wide := rfl
    -- `x` is its low half.
    have split := val32_append s.mem base (lo len (.slot .wide 18)) (cwc len .wide) (cwc len .wide)
    rw [show cwc len .wide + cwc len .wide = 2 * cwc len .wide by omega] at split
    have xlo : xv s.mem base len = val32 s.mem base (lo len (.slot .wide 18)) (cwc len .wide) := by
      have hp : 2 ^ (8 * bc len .wide) = 2 ^ (32 * cwc len .wide) := by congr 1; omega
      have hB : val32 s.mem base (lo len (.slot .wide 18) + 4 * cwc len .wide) (cwc len .wide) = 0 := by
        refine Nat.eq_zero_of_not_pos fun hne => ?_
        have := Nat.mul_le_mul_left (2 ^ (32 * cwc len .wide)) hne
        simp only [xv] at hX; rw [split, hp] at hX; omega
      simp only [xv]; rw [split, hB, Nat.mul_zero, Nat.add_zero]
    simp only [reduceX]
    refine WP.seq (WP.mono (copy_ok h (x := .slot .wide 18) (d := .slot .wide 5) (one_ok .wide)
      (by rw [cb1]; omega) (by rw [cb1]; omega) (by rw [cb1]; exact .inl (by omega))) fun u₁ ⟨O₁, V₁, K₁⟩ => ?_)
    rw [cb1] at O₁
    rw [cw1] at V₁
    have F₁ : Frame (frameR base (s.gpr .esp) [(lo len (.slot .wide 5), bc len .wide)]) s.mem u₁.mem :=
      frameR_of_outside O₁ (by omega) (by simp)
    have C₁ := C.keepF K₁ (by decide) (by decide) F₁ (by simp; omega) (by simp; omega)
    have sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
    have e3 : sv u₁.mem base len .wide 3 = 1 := by
      have a := slot_apart len .wide (o := 5) (j := 3) (by decide)
      have e38 : lo len (.slot .wide 3) + st len .wide ≤ lo len (.slot .wide 8) := sl_le .wide (by decide)
      simp only [sv] at h3 ⊢; rw [O₁.val32 (by rcases a with a | a <;> [exact .inl (by omega); exact .inr a])
        (by omega)]; exact h3
    refine WP.mono (cmul_ok C₁ (o := 4) (a := 5) (b := 3) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (one3 e3)) fun u ⟨C₂, K₂, F₂, L₂, V₂⟩ => ?_
    refine ⟨C₂, by rw [mulR_sv C₁.inp F₂ C₁.inp.room (by decide) (by decide) (by decide) (by decide) (by decide), e3],
      L₂, ?_, ?_, (K₁.mono (by decide)).trans (K₂.mono (by decide))⟩
    · rw [show chunks .wide = 1 from rfl, Nat.mul_one, V₂, e3, Nat.mul_one, xlo]
      simp only [sv]; rw [V₁]
    · rw [sp₁] at F₂
      exact (frameR_widen F₁ (by simp)).trans (frameR_widen F₂ (by simp))
  | half =>
    obtain ⟨cwle, cw8, bh, h0, h5, h8, sth, top⟩ := HalfLay.mk' h
    have cb1 : cb len (one .half) = bc len .half := by simp [cb, one]
    have cw1 : cw len (one .half) = cwc len .half := by simp [cw, cwc, cb, one]
    have bwh := bc_wide_le len
    have bhw := bc_le_wide len .half
    have h6 : lo len (.slot .half 6) = numBase + 6 * st len .half := rfl
    have h4 : lo len (.slot .half 4) = numBase + 4 * st len .half := rfl
    have h3e : lo len (.slot .half 3) = numBase + 3 * st len .half := rfl
    have RR : 2 ^ (8 * bc len .half * 2) = 2 ^ (8 * bc len .half) * 2 ^ (8 * bc len .half) := by
      rw [← Nat.pow_add]; congr 1; omega
    -- `x` is its low `2 Bh` bytes, its low half and its high half.
    have xlo : xv s.mem base len = val32 s.mem base (lo len (.slot .wide 18)) (2 * cwc len .half) := by
      have split := val32_append s.mem base (lo len (.slot .wide 18)) (2 * cwc len .half)
        (2 * cwc len .wide - 2 * cwc len .half)
      rw [show 2 * cwc len .half + (2 * cwc len .wide - 2 * cwc len .half) = 2 * cwc len .wide by omega] at split
      have hp : 2 ^ (8 * bc len .wide) ≤ 2 ^ (32 * (2 * cwc len .half)) := Nat.pow_le_pow_right (by decide) (by omega)
      by_contra hne
      have := Nat.mul_le_mul_left (2 ^ (32 * (2 * cwc len .half)))
        (show 1 ≤ val32 s.mem base (lo len (.slot .wide 18) + 4 * (2 * cwc len .half))
          (2 * cwc len .wide - 2 * cwc len .half) from Nat.pos_of_ne_zero fun e => by
            simp only [xv] at hne; rw [split, e] at hne; simp at hne)
      simp only [xv] at hX
      omega
    have halves := val32_append s.mem base (lo len (.slot .wide 18)) (cwc len .half) (cwc len .half)
    rw [show cwc len .half + cwc len .half = 2 * cwc len .half by omega,
      show lo len (.slot .wide 18) + 4 * cwc len .half = lo len (.slot .wide 18) + bc len .half by omega,
      show 2 ^ (32 * cwc len .half) = 2 ^ (8 * bc len .half) by congr 1; omega] at halves
    simp only [reduceX]
    -- The low half into slot 5, the high half into slot 6.
    refine WP.seq (WP.mono (copy_ok h (x := .slot .wide 18) (d := .slot .half 5) (one_ok .half)
      (by rw [cb1]; omega) (by rw [cb1, h5]; omega) (by rw [cb1, h5]; exact .inl (by omega))) fun u₁ ⟨O₁, V₁, K₁⟩ => ?_)
    rw [cb1] at O₁
    rw [cw1] at V₁
    have sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
    have F₁ : Frame (frameR base (s.gpr .esp) [(lo len (.slot .half 5), bc len .half)]) s.mem u₁.mem :=
      frameR_of_outside O₁ (by omega) (by simp)
    have C₁ := C.keepF K₁ (by decide) (by decide) F₁ (by simp; omega) (by simp; omega)
    refine WP.seq (WP.mono (copyHigh_ok C₁.inp (j := 18) (d := 6) (by omega) (by omega) (by omega))
      fun u₂ ⟨O₂, V₂, K₂⟩ => ?_)
    rw [cw1, O₁.val32 (.inr (by omega)) (by omega)] at V₂
    have sp₂ : u₂.gpr .esp = s.gpr .esp := (K₂.1 _ (by decide)).trans sp₁
    have F₂ : Frame (frameR base (u₁.gpr .esp) [(lo len (.slot .half 6), bc len .half)]) u₁.mem u₂.mem :=
      frameR_of_outside O₂ (by omega) (by simp)
    have C₂ := C₁.keepF K₂ (by decide) (by decide) F₂ (by simp; omega) (by simp; omega)
    have L₂ : sv u₂.mem base len .half 5 = val32 s.mem base (lo len (.slot .wide 18)) (cwc len .half) := by
      simp only [sv]; rw [O₂.val32 (.inl (by omega)) (by omega), V₁]
    have H₂ : sv u₂.mem base len .half 6 = val32 s.mem base (lo len (.slot .wide 18) + bc len .half) (cwc len .half) := by
      simp only [sv]; rw [V₂]
    have one₂ : sv u₂.mem base len .half 3 = 1 := by
      simp only [sv] at h3 ⊢
      rw [O₂.val32 (.inl (by omega)) (by omega), O₁.val32 (.inl (by omega)) (by omega)]; exact h3
    -- `lo R⁻¹`, then `lo R⁻²` in slot 4.
    refine WP.seq (WP.mono (cmul_ok C₂ (o := 4) (a := 5) (b := 3) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (one3 one₂)) fun u₃ ⟨C₃, K₃, F₃, L₃, V₃⟩ => ?_)
    have mk3 : ∀ k, 3 ≤ k → k ≤ 8 → k ≠ 4 → sv u₃.mem base len .half k = sv u₂.mem base len .half k :=
      fun k a b c => mulR_sv C₂.inp F₃ C₂.inp.room (by decide) (by decide) a b c
    have one₃ : sv u₃.mem base len .half 3 = 1 := by rw [mk3 3 (by decide) (by decide) (by decide), one₂]
    refine WP.seq (WP.mono (cmul_ok C₃ (o := 4) (a := 4) (b := 3) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (one3 one₃)) fun u₄ ⟨C₄, K₄, F₄, L₄, V₄⟩ => ?_)
    have mk4 : ∀ k, 3 ≤ k → k ≤ 8 → k ≠ 4 → sv u₄.mem base len .half k = sv u₂.mem base len .half k :=
      fun k a b c => (mulR_sv C₃.inp F₄ C₃.inp.room (by decide) (by decide) a b c).trans (mk3 k a b c)
    have one₄ : sv u₄.mem base len .half 3 = 1 := by rw [mk4 3 (by decide) (by decide) (by decide), one₂]
    -- `hi R⁻¹` in slot 5.
    refine WP.seq (WP.mono (cmul_ok C₄ (o := 5) (a := 6) (b := 3) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (one3 one₄)) fun u₅ ⟨C₅, K₅, F₅, L₅, V₅⟩ => ?_)
    have mk5 : ∀ k, 3 ≤ k → k ≤ 8 → k ≠ 5 → sv u₅.mem base len .half k = sv u₄.mem base len .half k :=
      fun k a b c => mulR_sv C₄.inp F₅ C₄.inp.room (by decide) (by decide) a b c
    have one₅ : sv u₅.mem base len .half 3 = 1 := by rw [mk5 3 (by decide) (by decide) (by decide), one₄]
    have a₅ : sv u₅.mem base len .half 4 < sv u₅.mem base len .half 0 := by
      rw [mk5 4 (by decide) (by decide) (by decide), C₅.mod]; exact L₄
    have b₅ : sv u₅.mem base len .half 5 < sv u₅.mem base len .half 0 := by rw [C₅.mod]; exact L₅
    -- Their sum.
    refine WP.mono (addMod_ok C₅.inp .half (o := 4) (a := 4) (b := 5) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) a₅ b₅) fun u ⟨F₆, V₆, K₆⟩ => ?_
    have sp₅ : u₅.gpr .esp = s.gpr .esp := by
      rw [K₅.1 _ (by decide), K₄.1 _ (by decide), K₃.1 _ (by decide), sp₂]
    have C₆ := C₅.keepF K₆ (by decide) (by decide) F₆ (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      have p1 := slot_past1 len .half (j := 8) (by decide)
      have e48 : lo len (.slot .half 4) + st len .half ≤ lo len (.slot .half 8) := sl_le .half (by decide)
      rcases hq with rfl | rfl <;> dsimp only <;> omega) (by
      intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      have e1 : lo len (.slot .half 1) = numBase + st len .half := by simp [lo]
      rcases hq with rfl | rfl <;> dsimp only <;> omega)
    have keep6 : sv u.mem base len .half 3 = sv u₅.mem base len .half 3 := by
      have e1 : lo len (.slot .half 1) = numBase + st len .half := by simp [lo]
      have p1 := slot_past1 len .half (j := 3) (by decide)
      refine frameR_val32 F₆ C₅.inp.room nw (by omega) ?_ ?_
      · intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl <;> dsimp only <;> omega
      · intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        have p8 := slot_past1 len .half (j := 8) (by decide)
        have e48 : lo len (.slot .half 4) + st len .half ≤ lo len (.slot .half 8) := sl_le .half (by decide)
        rcases hq with rfl | rfl <;> dsimp only <;> omega
    refine ⟨C₆, by rw [keep6, one₅], ?_, ?_, ?_, ?_⟩
    · rw [V₆, C₅.mod]; exact Nat.mod_lt _ (by omega)
    · rw [V₆, C₅.mod, mk5 4 (by decide) (by decide) (by decide), show chunks .half = 2 from rfl, RR, xlo, halves]
      exact redc2 (by rw [V₃, L₂, one₂]) (by rw [V₄, one₃, Nat.mul_one])
        (by rw [V₅, mk4 6 (by decide) (by decide) (by decide), H₂, one₄])
    · have sp₃ : u₃.gpr .esp = s.gpr .esp := (K₃.1 _ (by decide)).trans sp₂
      have sp₄ : u₄.gpr .esp = s.gpr .esp := (K₄.1 _ (by decide)).trans sp₃
      rw [sp₁] at F₂
      rw [sp₂] at F₃
      rw [sp₃] at F₄
      rw [sp₄] at F₅
      rw [sp₅] at F₆
      refine (((((frameR_widen F₁ (by simp)).trans (frameR_widen F₂ (by simp))).trans (frameR_widen F₃ (by simp))).trans
        (frameR_widen F₄ (by simp))).trans (frameR_widen F₅ (by simp))).trans (frameR_widen F₆ ?_)
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., Nat.le_refl _, by dsimp only; omega⟩
      · exact ⟨(lo len (.slot .half 4), bc len .half), by simp, Nat.le_refl _, Nat.le_refl _⟩
    · exact ((((((K₁.trans K₂).trans (K₃.mono (by decide))).trans (K₄.mono (by decide))).trans
        (K₅.mono (by decide))).trans K₆))


/-- `r2Fix`'s counts: `128 w_p + 8 Bc K` for `K = chunks c`, and `128 w = 16 B`. -/
abbrev fixA (L len : Nat) (c : Ctx) : Nat := r2Exp L + 8 * bc len c * chunks c
abbrev fixB (len : Nat) : Nat := 16 * bc len .wide

theorem fixB_le (L len : Nat) (c : Ctx) : fixB len ≤ fixA L len c + 8 * bc len c * 2 := by
  simp only [fixA, fixB, r2Exp]; cases c <;> simp only [bc, chunks] <;> omega_arith

theorem chunks_le (c : Ctx) : chunks c ≤ 2 := by cases c <;> decide

/-- `ebx = 128 w = 16 B`, compared with `esi`. -/
theorem cmpB_ok (h : In Ex base bytes len args s) {A : Nat} (ev : (s.gpr .esi).toNat = A) :
    WP isa (.block (widthB 0 .ebx ++ (shl .ebx 4 ++ ([.alu .cmp .esi (.reg .ebx)] : List Instr)))) s fun u =>
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u ∧ u.mem = s.mem ∧
      (u.gpr .esi).toNat = A ∧ (u.gpr .ebx).toNat = fixB len ∧
      isa.eval .b u = some (decide (A < fixB len)) := by
  have hup := h.upper'
  have hbw := bc_le hup .wide
  refine widthB_ok h.width hup fun u₁₁ K₁₁ m₁₁ e₁₁ => shl_ok 4 fun u₁₂ K₁₂ m₁₂ e₁₂ => ?_
  refine wp_cmpC rfl fun u f cfl => WP.block_nil ?_
  have ebx : (u₁₂.gpr .ebx).toNat = fixB len := by
    rw [e₁₂, e₁₁, BitVec.toNat_ofNat]
    have : wb len = bc len .wide := rfl
    simp only [fixB]; omega_arith
  have esi : (u₁₂.gpr .esi).toNat = A := by rw [K₁₂.1 _ (by decide), K₁₁.1 _ (by decide)]; exact ev
  refine ⟨((K₁₁.mono (by decide)).trans (K₁₂.mono (by decide))).trans (f.keeps _), by rw [f.mem, m₁₂, m₁₁],
    by rw [f.gpr]; exact esi, by rw [f.gpr]; exact ebx, ?_⟩
  rw [esi, ebx] at cfl; exact cfl

/-- `esi - 128 w`, for `128 w ≤ esi`, and whether it is zero. -/
theorem subB_ok (h : In Ex base bytes len args s) {A : Nat} (ev : (s.gpr .esi).toNat = A) (hA : fixB len ≤ A) :
    WP isa (.block (widthB 0 .ebx ++ shl .ebx 4 ++ ([.alu .sub .esi (.reg .ebx)] : List Instr))) s fun u =>
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u ∧ u.mem = s.mem ∧
      (u.gpr .esi).toNat = A - fixB len ∧ u.zf = some (decide (A - fixB len = 0)) := by
  have hup := h.upper'
  have hbw := bc_le hup .wide
  simp only [List.append_assoc]
  refine widthB_ok h.width hup fun u₁₁ K₁₁ m₁₁ e₁₁ => shl_ok 4 fun u₁₂ K₁₂ m₁₂ e₁₂ => ?_
  refine wp_sub fun u a z => WP.block_nil ?_
  have ebx : (u₁₂.gpr .ebx).toNat = fixB len := by
    rw [e₁₂, e₁₁, BitVec.toNat_ofNat]
    have : wb len = bc len .wide := rfl
    simp only [fixB]; omega_arith
  have esi : (u₁₂.gpr .esi).toNat = A := by rw [K₁₂.1 _ (by decide), K₁₁.1 _ (by decide)]; exact ev
  have esiu : (u.gpr .esi).toNat = A - fixB len := by
    rw [a.gpr, BitVec.toNat_sub, esi, ebx]; omega_arith
  refine ⟨((K₁₁.mono (by decide)).trans (K₁₂.mono (by decide))).trans (a.keeps.mono (by decide)),
    by rw [a.mem, m₁₂, m₁₁], esiu, ?_⟩
  rw [z, ← a.gpr]
  by_cases hg : A - fixB len = 0
  · have : u.gpr .esi = 0 := BitVec.eq_of_toNat_eq (by rw [esiu, hg]; rfl)
    rw [this]; simp [hg]
  · have : u.gpr .esi ≠ 0 := fun e => hg (by rw [← esiu, e]; rfl)
    simp only [beq_eq_false_iff_ne.mpr this, hg, decide_false]

theorem fixStart_ok (h : In Ex base bytes len args s) {i : Nat} (hi : i < 18) (c : Ctx)
    (hL1 : 1 ≤ (args i).toNat) (hL : (args i).toNat ≤ len) :
    WP isa (.block (fixStart i c)) s fun u =>
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u ∧ u.mem = s.mem ∧
      (u.gpr .esi).toNat = fixA (args i).toNat len c ∧ (u.gpr .ebx).toNat = fixB len ∧
      isa.eval .b u = some (decide (fixA (args i).toNat len c < fixB len)) := by
  have hup := h.upper'
  have hb := bc_le hup c
  have hbw := bc_le hup .wide
  have ck := chunks_le c
  let L := (args i).toNat
  have pw : Spec.Rsa.primeWords L ≤ 128 := by
    simp only [Spec.Rsa.primeWords, Spec.Rsa.modulusWords]; omega_arith
  simp only [fixStart, primeWords, List.cons_append, List.append_assoc]
  refine wp_movS (h.arg hi) fun u₁ a₁ _ => ?_
  refine wp_addS rfl fun u₂ a₂ _ => wp_shr (by decide) fun u₃ a₃ _ => wp_movS rfl fun u₄ a₄ _ => ?_
  refine wp_subS rfl fun u₅ a₅ _ => wp_shr (by decide) fun u₆ a₆ _ => wp_addS rfl fun u₇ a₇ _ => ?_
  refine shl_ok 7 fun u₈ K₈ m₈ e₈ => ?_
  have K₈' : Keeps [.esi, .eax] s u₈ :=
    ((((((((a₁.keeps.mono (by decide)).trans (a₂.keeps.mono (by decide))).trans (a₃.keeps.mono (by decide))).trans
      (a₄.keeps.mono (by decide))).trans (a₅.keeps.mono (by decide))).trans (a₆.keeps.mono (by decide))).trans
      (a₇.keeps.mono (by decide))).trans (K₈.mono (by decide)))
  have m₈' : u₈.mem = s.mem := by rw [m₈, a₇.mem, a₆.mem, a₅.mem, a₄.mem, a₃.mem, a₂.mem, a₁.mem]
  have esi₈ : (u₈.gpr .esi).toNat = r2Exp L := by
    have r₁ : u₁.gpr .esi = BitVec.ofNat 32 L := by
      apply BitVec.eq_of_toNat_eq
      rw [a₁.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)]
    have r₃ : u₃.gpr .esi = (BitVec.ofNat 32 L + 7) >>> 3 := by rw [a₃.gpr, a₂.gpr, r₁]
    have e₇ : u₇.gpr .esi = u₃.gpr .esi + (u₃.gpr .esi - 2) >>> 31 := by
      rw [a₇.gpr, a₆.other _ (by decide), a₅.other _ (by decide), a₄.other _ (by decide), a₆.gpr, a₅.gpr,
        a₄.gpr]
    have pv := primeWords_val L hL1 (by omega_arith)
    rw [e₈, e₇, r₃, pv]
    simp only [r2Exp]; omega_arith
  have h₈ := h.regs (K₈'.mono (by decide) : Keeps [.eax, .esi] s u₈) m₈'
  refine widthC_ok (k := 0) (c := c) (r := .edx) h₈.width hup fun u₉ K₉ m₉ e₉ => ?_
  refine shl_ok 3 fun u₁₀ K₁₀ m₁₀ e₁₀ => ?_
  have edx : (u₁₀.gpr .edx).toNat = 8 * bc len c := by
    rw [e₁₀, e₉, BitVec.toNat_ofNat]; omega_arith
  have esi₁₀ : (u₁₀.gpr .esi).toNat = r2Exp L := by rw [K₁₀.1 _ (by decide), K₉.1 _ (by decide)]; exact esi₈
  have K₁₀' : Keeps [.eax, .esi, .edx] s u₁₀ :=
    ((K₈'.mono (by decide)).trans (K₉.mono (by decide))).trans (K₁₀.mono (by decide))
  have m₁₀' : u₁₀.mem = s.mem := by rw [m₁₀, m₉, m₈']
  have tail : ∀ v : State, Keeps [.eax, .esi, .edx] s v → v.mem = s.mem →
      (v.gpr .esi).toNat = fixA L len c →
      WP isa (.block (widthB 0 .ebx ++ (shl .ebx 4 ++ ([.alu .cmp .esi (.reg .ebx)] : List Instr)))) v fun u =>
        Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u ∧ u.mem = s.mem ∧
        (u.gpr .esi).toNat = fixA L len c ∧ (u.gpr .ebx).toNat = fixB len ∧
        isa.eval .b u = some (decide (fixA L len c < fixB len)) := fun v Kv mv ev =>
    WP.mono (cmpB_ok (h.regs (Kv.mono (by decide) : Keeps [.eax, .esi, .edx] s v) mv) ev)
      fun u ⟨K, m, e, b, f⟩ => ⟨(Kv.mono (by decide)).trans K, m.trans mv, e, b, f⟩
  have re : r2Exp L ≤ 16384 := by simp only [r2Exp]; omega_arith
  cases c with
  | wide =>
    simp only [chunks, List.replicate, List.cons_append, List.nil_append]
    refine wp_addS rfl fun v a _ => tail v (K₁₀'.trans (a.keeps.mono (by decide))) (by rw [a.mem, m₁₀']) ?_
    rw [a.gpr, BitVec.toNat_add, esi₁₀, edx]
    simp only [fixA, show chunks .wide = 1 from rfl]; omega_arith
  | half =>
    simp only [chunks, List.replicate, List.cons_append, List.nil_append]
    refine wp_addS rfl fun v₁ b₁ _ => wp_addS rfl fun v a _ => tail v
      ((K₁₀'.trans (b₁.keeps.mono (by decide))).trans (a.keeps.mono (by decide))) (by rw [a.mem, b₁.mem, m₁₀']) ?_
    rw [a.gpr, BitVec.toNat_add, b₁.gpr, BitVec.toNat_add, esi₁₀, b₁.other _ (by decide), edx]
    simp only [fixA, show chunks .half = 2 from rfl]; omega_arith

/-- `fixStep`: `esi` up by `8 Bc`, compared with `128 w`. -/
theorem fixStep_ok (h : In Ex base bytes len args s) {c : Ctx} {A : Nat} (hesi : (s.gpr .esi).toNat = A)
    (hA : A + 8 * bc len c < 2 ^ 32) :
    WP isa (.block (fixStep c)) s fun u =>
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u ∧ u.mem = s.mem ∧
      (u.gpr .esi).toNat = A + 8 * bc len c ∧ (u.gpr .ebx).toNat = fixB len ∧
      isa.eval .b u = some (decide (A + 8 * bc len c < fixB len)) := by
  have hup := h.upper'
  have hb := bc_le hup c
  simp only [fixStep, List.append_assoc, List.cons_append, List.nil_append]
  refine widthC_ok (k := 0) (c := c) (r := .edx) h.width hup fun u₂ K₂ m₂ e₂ => ?_
  refine shl_ok 3 fun u₃ K₃ m₃ e₃ => ?_
  refine wp_addS rfl fun u₄ a₄ _ => ?_
  have edx : (u₃.gpr .edx).toNat = 8 * bc len c := by rw [e₃, e₂, BitVec.toNat_ofNat]; omega_arith
  have K₃' : Keeps [.edx] s u₃ := (K₂.mono (by decide)).trans K₃
  have esi₄ : (u₄.gpr .esi).toNat = A + 8 * bc len c := by
    rw [a₄.gpr, BitVec.toNat_add, K₃'.1 _ (by decide), hesi, edx]; omega_arith
  have K₄ : Keeps [.edx, .esi] s u₄ := (K₃'.mono (by decide)).trans (a₄.keeps.mono (by decide))
  have m₄ : u₄.mem = s.mem := by rw [a₄.mem, m₃, m₂]
  exact WP.mono (cmpB_ok (h.regs K₄ m₄) esi₄) fun u ⟨Ku, mu, esiu, ebxu, cfu⟩ =>
    ⟨(K₄.mono (by decide)).trans Ku, mu.trans m₄, esiu, ebxu, cfu⟩

/-- `r2Fix`'s subtraction, as bit vectors: `esi - 128 w`, and whether it is zero. -/
theorem subBv_ok (h : In Ex base bytes len args s) :
    WP isa (.block (widthB 0 .ebx ++ shl .ebx 4 ++ ([.alu .sub .esi (.reg .ebx)] : List Instr))) s fun u =>
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u ∧ u.mem = s.mem ∧
      u.gpr .esi = s.gpr .esi - BitVec.ofNat 32 (fixB len) ∧ u.zf = some (u.gpr .esi == 0) := by
  have hup := h.upper'
  have hbw := bc_le hup .wide
  simp only [List.append_assoc]
  refine widthB_ok h.width hup fun u₁₁ K₁₁ m₁₁ e₁₁ => shl_ok 4 fun u₁₂ K₁₂ m₁₂ e₁₂ => ?_
  refine wp_sub fun u a z => WP.block_nil ?_
  have ebx : u₁₂.gpr .ebx = BitVec.ofNat 32 (fixB len) := by
    apply BitVec.eq_of_toNat_eq
    rw [e₁₂, e₁₁, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have : wb len = bc len .wide := rfl
    simp only [fixB]; omega_arith
  have esi : u₁₂.gpr .esi = s.gpr .esi := by rw [K₁₂.1 _ (by decide), K₁₁.1 _ (by decide)]
  refine ⟨((K₁₁.mono (by decide)).trans (K₁₂.mono (by decide))).trans (a.keeps.mono (by decide)),
    by rw [a.mem, m₁₂, m₁₁], by rw [a.gpr, esi, ebx], by rw [z, a.gpr]⟩

theorem fixA_le {L len : Nat} (hL : L ≤ len) (hup : len ≤ 1024) (c : Ctx) : fixA L len c ≤ 32768 := by
  have hb := bc_le hup c
  have ck := chunks_le c
  have pw : Spec.Rsa.primeWords L ≤ 128 := by
    simp only [Spec.Rsa.primeWords, Spec.Rsa.modulusWords]; omega_arith
  have := Nat.mul_le_mul (show 8 * bc len c ≤ 8192 by omega_arith) ck
  simp only [fixA, r2Exp]; omega_arith

/-- One more reduction: `T R⁻¹ mod M` in slot 4, and `esi` up by `8 Bc`, compared with `ebx`. -/
theorem fixMore_ok {c : Ctx} {M : Nat} (C : CtxOk Ex base bytes len args c M s) (h3 : sv s.mem base len c 3 = 1)
    {A : Nat} (hesi : (s.gpr .esi).toNat = A) (hA : A + 8 * bc len c < 2 ^ 32) :
    WP isa (fixMore c) s fun u =>
      CtxOk Ex base bytes len args c M u ∧ sv u.mem base len c 3 = 1 ∧ sv u.mem base len c 4 < M ∧
      sv u.mem base len c 4 * 2 ^ (8 * bc len c) % M = sv s.mem base len c 4 % M ∧
      (u.gpr .esi).toNat = A + 8 * bc len c ∧ (u.gpr .ebx).toNat = fixB len ∧
      isa.eval .b u = some (decide (A + 8 * bc len c < fixB len)) ∧
      Frame (frameR base (s.gpr .esp) (mulR len c 4)) s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have hup := C.inp.upper'
  have hb := bc_le hup c
  unfold fixMore
  refine WP.seq (WP.mono (cmul_ok C (o := 4) (a := 4) (b := 3) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [h3]; exact C.gt)) fun u₁ ⟨C₁, K₁, F₁, L₁, V₁⟩ => ?_)
  have one₁ : sv u₁.mem base len c 3 = 1 := by
    rw [mulR_sv C.inp F₁ C.inp.room (by decide) (by decide) (by decide) (by decide) (by decide), h3]
  have esi₁ : (u₁.gpr .esi).toNat = A := by rw [K₁.1 _ (by decide), hesi]
  refine WP.mono (fixStep_ok C₁.inp esi₁ hA) fun u ⟨Kt, mt, esiu, ebxu, cfu⟩ => ?_
  refine ⟨C₁.regs Kt mt, by simp only [sv] at one₁ ⊢; rw [mt]; exact one₁, by simp only [sv] at L₁ ⊢; rw [mt]; exact L₁,
    ?_, esiu, ebxu, cfu, by rw [mt]; exact F₁, (K₁.mono (by decide)).trans Kt⟩
  simp only [sv] at V₁ ⊢; rw [mt, V₁, show val32 s.mem base (lo len (.slot c 3)) (cwc len c) = 1 from h3, Nat.mul_one]

/-- `g` doublings of slot 4. -/
theorem dbl_ok {c : Ctx} {M : Nat} (C : CtxOk Ex base bytes len args c M s) {g : Nat} (hg : 0 < g) (hesi : (s.gpr .esi).toNat = g) (h4 : sv s.mem base len c 4 < M) :
    WP isa (.loop (doubleStep c) .ne) s fun u =>
      CtxOk Ex base bytes len args c M u ∧ sv u.mem base len c 3 = sv s.mem base len c 3 ∧
      sv u.mem base len c 4 = sv s.mem base len c 4 * 2 ^ g % M ∧
      Frame (frameR base (s.gpr .esp) [(lo len (.slot c 1), bc len c + 4), (lo len (.slot c 4), bc len c)]) s.mem
        u.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have h := C.inp
  have nw' := h.scratch.nowrap
  have f8 := h.slot_fit c (j := 8) (by decide)
  have est : st len c = 2 * bc len c + 32 := rfl
  have bw := bc_eq_cwc len c
  have s14 : lo len (.slot c 1) + st len c ≤ lo len (.slot c 3) := sl_le (len := len) c (by decide)
  have s34 : lo len (.slot c 3) + st len c ≤ lo len (.slot c 4) := sl_le (len := len) c (by decide)
  have s48 : lo len (.slot c 4) + st len c ≤ lo len (.slot c 8) := sl_le (len := len) c (by decide)
  have z0 : lo len (.slot c 0) = numBase := sl_zero len c
  have e1 : lo len (.slot c 1) = numBase + st len c := by simp [lo]
  let ws : List (Nat × Nat) := [(lo len (.slot c 1), bc len c + 4), (lo len (.slot c 4), bc len c)]
  have fit : ∀ p ∈ ws, p.1 + p.2 ≤ bytes := by
    intro p hp
    simp only [ws, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> dsimp only <;> omega_arith
  have low : ∀ p ∈ ws, numBase + bc len c ≤ p.1 := by
    intro p hp
    simp only [ws, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> dsimp only <;> omega_arith
  have keep3 : ∀ {m m' : Mem}, Frame (frameR base (s.gpr .esp) ws) m m' →
      sv m' base len c 3 = sv m base len c 3 := fun F =>
    frameR_val32 F h.room nw' (by omega_arith) (by
      intro p hp
      simp only [ws, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> dsimp only <;> omega_arith) fit
  let I : Nat → State → Prop := fun j t =>
    CtxOk Ex base bytes len args c M t ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧
      Frame (frameR base (s.gpr .esp) ws) s.mem t.mem ∧
      sv t.mem base len c 4 = sv s.mem base len c 4 * 2 ^ j % M ∧ (t.gpr .esi).toNat = g - j
  have I₀ : I 0 s := ⟨C, Keeps.refl _ _, Frame.refl _ _, by rw [Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt h4],
    by rw [hesi]; rfl⟩
  refine WP.mono (countLoop (N := g) hg I ?_ I₀) fun t ⟨Ct, Kt, Ft, Vt, _⟩ =>
    ⟨Ct, keep3 Ft, Vt, Ft, Kt⟩
  rintro j t hj ⟨Ct, Kt, Ft, Vt, esit⟩
  have hM' : 0 < M := by have := Ct.gt; omega_arith
  refine WP.mono (doubleStep_ok Ct.inp c (by rw [Vt, Ct.mod]; exact Nat.mod_lt _ hM'))
    fun u ⟨Fu, Vu, esiu, zu, Ku⟩ => ?_
  obtain ⟨c₁, c₂⟩ := count1_zf esit hj
  have spt : t.gpr .esp = s.gpr .esp := Kt.1 _ (by decide)
  rw [spt] at Fu
  refine ⟨⟨Ct.keepF Ku (by decide) (by decide) (by rw [spt]; exact Fu) fit low, Kt.trans Ku, Ft.trans Fu, ?_,
    by rw [esiu]; exact c₁⟩, by rw [zu, c₂]⟩
  rw [Vu, Vt, Ct.mod, ← Nat.add_mod, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_two]

/-- `2^e mod M` from `v R^K ≡ X ≡ 2^B` and `g` doublings, for `e + K = B + g`. -/
theorem fix_final {v M X K e g B : Nat} (cop : Nat.Coprime (2 ^ K) M) (hv : v * 2 ^ K % M = X % M)
    (hX : X % M = 2 ^ B % M) (hg : e + K = B + g) : v * 2 ^ g % M = 2 ^ e % M := by
  refine VG.Proof.Bignum.mont_cancel cop ?_
  rw [Nat.mul_right_comm, mod_mul_eq (hv.trans hX), ← Nat.pow_add, ← Nat.pow_add, hg]

/-- The ranges `r2Fix` changes. -/
theorem fixR_sub (len : Nat) (c : Ctx) :
    (∀ q ∈ mulR len c 4, ∃ q' ∈ redR len c, q'.1 ≤ q.1 ∧ q.1 + q.2 ≤ q'.1 + q'.2) ∧
      ∀ q ∈ [(lo len (.slot c 1), bc len c + 4), (lo len (.slot c 4), bc len c)],
        ∃ q' ∈ redR len c, q'.1 ≤ q.1 ∧ q.1 + q.2 ≤ q'.1 + q'.2 := by
  constructor <;> intro q hq <;> simp only [mulR, List.mem_cons, List.not_mem_nil, or_false] at hq <;>
    rcases hq with rfl | rfl
  · exact ⟨(lo len (.slot c 4), bc len c), by simp, Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨(lo len (.slot c 1), 3 * bc len c + 56), by simp, Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨(lo len (.slot c 1), 3 * bc len c + 56), by simp, Nat.le_refl _, by dsimp only; omega⟩
  · exact ⟨(lo len (.slot c 4), bc len c), by simp, Nat.le_refl _, Nat.le_refl _⟩

/-- `r2Fix`: from `T R^K ≡ x` in slot 4 (`K = chunks c`), `2^(128 w_p) mod M` when `x ≡ 2^(128 w)`. -/
theorem r2Fix_ok {c : Ctx} {M : Nat} (C : CtxOk Ex base bytes len args c M s) (h3 : sv s.mem base len c 3 = 1)
    {i : Nat} (hi : i < 18) (hL1 : 1 ≤ (args i).toNat) (hL : (args i).toNat ≤ len) {X : Nat}
    (h4 : sv s.mem base len c 4 < M) (hR : sv s.mem base len c 4 * 2 ^ (8 * bc len c * chunks c) % M = X % M) :
    WP isa (r2Fix i c) s fun u =>
      CtxOk Ex base bytes len args c M u ∧
      (X % M = 2 ^ fixB len % M → sv u.mem base len c 4 = 2 ^ r2Exp (args i).toNat % M) ∧
      Frame (frameR base (s.gpr .esp) (redR len c)) s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have hup := C.inp.upper'
  have hb := bc_le hup c
  have hbw := bc_le hup .wide
  have bwh := bc_wide_le len
  have bhw := bc_le_wide len c
  have ck := chunks_le c
  have rg := fixR_sub len c
  have pw : Spec.Rsa.primeWords (args i).toNat ≤ 128 := by
    simp only [Spec.Rsa.primeWords, Spec.Rsa.modulusWords]; omega_arith
  have pw2 : 2 ≤ Spec.Rsa.primeWords (args i).toNat := by simp only [Spec.Rsa.primeWords]; omega_arith
  have hA : (fixA (args i).toNat len c) ≤ 16384 + 16384 := by
    have := Nat.mul_le_mul (show 8 * bc len c ≤ 8192 by omega_arith) ck
    simp only [fixA, r2Exp]; omega_arith
  -- After `E` more reductions, `E` at most two and `128 w ≤ (fixA (args i).toNat len c) + 8 Bc E`.
  let P : Nat → State → Prop := fun E u =>
    E ≤ 2 ∧ CtxOk Ex base bytes len args c M u ∧ sv u.mem base len c 3 = 1 ∧ sv u.mem base len c 4 < M ∧
      sv u.mem base len c 4 * 2 ^ (8 * bc len c * (chunks c + E)) % M = X % M ∧
      (u.gpr .esi).toNat = (fixA (args i).toNat len c) + 8 * bc len c * E ∧ (u.gpr .ebx).toNat = (fixB len) ∧ (fixB len) ≤ (fixA (args i).toNat len c) + 8 * bc len c * E ∧
      Frame (frameR base (s.gpr .esp) (redR len c)) s.mem u.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u
  have step : ∀ {E : Nat} {u v : State}, sv u.mem base len c 4 * 2 ^ (8 * bc len c * (chunks c + E)) % M = X % M →
      sv v.mem base len c 4 * 2 ^ (8 * bc len c) % M = sv u.mem base len c 4 % M →
      sv v.mem base len c 4 * 2 ^ (8 * bc len c * (chunks c + (E + 1))) % M = X % M := by
    intro E u v hu hv
    rw [show 8 * bc len c * (chunks c + (E + 1)) = 8 * bc len c + 8 * bc len c * (chunks c + E) by
        rw [Nat.add_succ, Nat.mul_succ, Nat.add_comm],
      Nat.pow_add, ← Nat.mul_assoc, mod_mul_eq hv, hu]
  unfold r2Fix
  refine WP.seq (WP.mono (fixStart_ok C.inp hi c hL1 hL) fun u₁ ⟨K₁, m₁, esi₁, ebx₁, cf₁⟩ => ?_)
  have C₁ := C.regs K₁ m₁
  have sv₁ : ∀ j, sv u₁.mem base len c j = sv s.mem base len c j := fun j => by simp only [sv]; rw [m₁]
  have sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  have F₁ : Frame (frameR base (s.gpr .esp) (redR len c)) s.mem u₁.mem := by rw [m₁]; exact Frame.refl _ _
  have P₀ : (fixB len) ≤ (fixA (args i).toNat len c) → P 0 u₁ := fun hBA => ⟨by decide, C₁, by rw [sv₁]; exact h3, by rw [sv₁]; exact h4,
    by rw [sv₁, Nat.add_zero]; exact hR, by rw [esi₁, Nat.mul_zero, Nat.add_zero], ebx₁, by omega_arith, F₁, K₁⟩
  refine WP.seq (WP.mono (Q := fun u => ∃ E, P E u) ?_ fun u ⟨E, PE⟩ => ?_)
  · refine WP.ite (decide ((fixA (args i).toNat len c) < (fixB len))) cf₁ (fun hAB => ?_) (fun hBA => WP.block_nil ⟨0, P₀ (by
      have := of_decide_eq_false hBA; omega_arith)⟩)
    have hAB' : (fixA (args i).toNat len c) < (fixB len) := of_decide_eq_true hAB
    refine WP.seq (WP.mono (fixMore_ok C₁ (by rw [sv₁]; exact h3) esi₁ (by omega_arith))
      fun u₂ ⟨C₂, one₂, L₂, V₂, esi₂, ebx₂, cf₂, F₂, K₂⟩ => ?_)
    have sp₂ : u₂.gpr .esp = s.gpr .esp := (K₂.1 _ (by decide)).trans sp₁
    rw [sp₁] at F₂
    have F₂' := F₁.trans (frameR_widen F₂ rg.1)
    have R₂ := step (E := 0) (by rw [sv₁, Nat.add_zero]; exact hR) V₂
    refine WP.ite (decide ((fixA (args i).toNat len c) + 8 * bc len c < (fixB len))) cf₂ (fun hAB₂ => ?_) (fun hBA₂ => WP.block_nil
      ⟨1, by decide, C₂, one₂, L₂, R₂, by rw [esi₂, Nat.mul_one], ebx₂,
        by have := of_decide_eq_false hBA₂; rw [Nat.mul_one]; omega_arith, F₂', K₁.trans K₂⟩)
    refine WP.mono (fixMore_ok C₂ one₂ esi₂ (by omega_arith)) fun u ⟨C₃, one₃, L₃, V₃, esi₃, ebx₃, _, F₃, K₃⟩ =>
      ⟨2, by decide, C₃, one₃, L₃, step (E := 1) R₂ V₃, by rw [esi₃]; omega_arith, ebx₃, ?_,
        F₂'.trans (by rw [← sp₂]; exact frameR_widen F₃ rg.1), (K₁.trans K₂).trans K₃⟩
    -- `128 w ≤ 128 w_p + 8 Bc (K + 2)`.
    exact fixB_le _ _ _
  -- The doublings.
  obtain ⟨E2, CE, oneE, LE, RE, esiE, ebxE, BAE, FE, KE⟩ := PE
  let g := (fixA (args i).toNat len c) + 8 * bc len c * E - (fixB len)
  have spE : u.gpr .esp = s.gpr .esp := KE.1 _ (by decide)
  have cop : Nat.Coprime (2 ^ (8 * bc len c * (chunks c + E))) M := VG.Proof.Bignum.coprime_pow2 CE.odd _
  have expo : r2Exp (args i).toNat + 8 * bc len c * (chunks c + E) = (fixB len) + g := by
    simp only [g, fixA] at *; rw [Nat.mul_add]; omega_arith
  refine WP.seq (WP.mono (subB_ok CE.inp esiE BAE) fun v ⟨Kv, mv, esiv, z⟩ => ?_)
  have Cv := CE.regs Kv mv
  have svv : ∀ j, sv v.mem base len c j = sv u.mem base len c j := fun j => by simp only [sv]; rw [mv]
  have Fv : Frame (frameR base (s.gpr .esp) (redR len c)) s.mem v.mem := by rw [mv]; exact FE
  have Kvs : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v := KE.trans Kv
  refine WP.ite (decide (g = 0)) (by simp only [eval]; rw [z]) (fun hg => WP.block_nil ?_) (fun hg => ?_)
  · have hg0 : g = 0 := of_decide_eq_true hg
    refine ⟨Cv, fun hX => ?_, Fv, Kvs⟩
    rw [svv]
    have := fix_final (g := 0) cop RE hX (by rw [expo, hg0])
    rwa [Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt LE] at this
  · have hg0 : 0 < g := Nat.pos_of_ne_zero (of_decide_eq_false hg)
    refine WP.mono (dbl_ok Cv hg0 (by rw [esiv]) (by rw [svv]; exact LE)) fun w ⟨Cw, _, Vw, Fw, Kw⟩ =>
      ⟨Cw, fun hX => by rw [Vw, svv]; exact fix_final cop RE hX expo, ?_, Kvs.trans Kw⟩
    have spv : v.gpr .esp = s.gpr .esp := (Kv.1 _ (by decide)).trans spE
    rw [spv] at Fw
    exact Fv.trans (frameR_widen Fw rg.2)


/-- The ranges of the working space `primeIn` changes, but its output's: `prepare`'s (the factor
into slot 0 among them), and slots 5 and 6, where `reduceX` puts the chunks of `x`. -/
abbrev primeR (len : Nat) (c : Ctx) : List (Nat × Nat) :=
  [(invOff, 4), (lo len (.slot c 0), bc len c), (lo len (.slot c 1), 3 * bc len c + 56),
    (lo len (.slot c 3), bc len c), (lo len (.slot c 4), bc len c), (lo len (.slot c 5), bc len c),
    (lo len (.slot c 6), bc len c), (lo len (.slot c 7), bc len c)]

theorem redR_sub (len : Nat) (c : Ctx) : ∀ q ∈ redR len c, q ∈ primeR len c := by
  intro q hq
  simp only [redR, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> simp

theorem primeR_fit (h : In Ex base bytes len args s) (c : Ctx) : ∀ q ∈ primeR len c, q.1 + q.2 ≤ bytes := by
  have f8 := h.slot_fit c (j := 8) (by decide)
  have s01 : lo len (.slot c 0) + st len c ≤ lo len (.slot c 1) := sl_le (len := len) c (by decide)
  have s13 : lo len (.slot c 1) + st len c ≤ lo len (.slot c 3) := sl_le (len := len) c (by decide)
  have s34 : lo len (.slot c 3) + st len c ≤ lo len (.slot c 4) := sl_le (len := len) c (by decide)
  have s45 : lo len (.slot c 4) + st len c ≤ lo len (.slot c 5) := sl_le (len := len) c (by decide)
  have s56 : lo len (.slot c 5) + st len c ≤ lo len (.slot c 6) := sl_le (len := len) c (by decide)
  have s67 : lo len (.slot c 6) + st len c ≤ lo len (.slot c 7) := sl_le (len := len) c (by decide)
  have s78 : lo len (.slot c 7) + st len c ≤ lo len (.slot c 8) := sl_le (len := len) c (by decide)
  have est : st len c = 2 * bc len c + 32 := rfl
  have lo0 : numBase ≤ lo len (.slot c 0) := by simp [lo]
  have nb : numBase = 3336 := rfl
  intro q hq
  simp only [primeR, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;>
    (try simp only [invOff]) <;> omega_arith

theorem primeR2_fit (h : In Ex base bytes len args s) :
    ∀ q ∈ primeR len .half ++ primeR len .wide, q.1 + q.2 ≤ bytes := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact primeR_fit h .half q hq
  · exact primeR_fit h .wide q hq

/-- `primeR`'s ranges end below the wide slot 9, and miss the word at `accOff`. -/
theorem primeR_below (h : In Ex base bytes len args s) (c : Ctx) : ∀ q ∈ primeR len c,
    q.1 + q.2 ≤ lo len (.slot .wide 9) ∧ (accOff + 4 ≤ q.1 ∨ q.1 + q.2 ≤ accOff) := by
  have hw : lo len (.slot c 8) + st len c ≤ lo len (.slot .wide 9) := by
    cases c
    · have := sl_le (len := len) .wide (i := 8) (j := 9) (by decide); exact this
    · exact half_in_wide h (by decide)
  have s01 : lo len (.slot c 0) + st len c ≤ lo len (.slot c 1) := sl_le (len := len) c (by decide)
  have s13 : lo len (.slot c 1) + st len c ≤ lo len (.slot c 3) := sl_le (len := len) c (by decide)
  have s34 : lo len (.slot c 3) + st len c ≤ lo len (.slot c 4) := sl_le (len := len) c (by decide)
  have s45 : lo len (.slot c 4) + st len c ≤ lo len (.slot c 5) := sl_le (len := len) c (by decide)
  have s56 : lo len (.slot c 5) + st len c ≤ lo len (.slot c 6) := sl_le (len := len) c (by decide)
  have s67 : lo len (.slot c 6) + st len c ≤ lo len (.slot c 7) := sl_le (len := len) c (by decide)
  have s78 : lo len (.slot c 7) + st len c ≤ lo len (.slot c 8) := sl_le (len := len) c (by decide)
  have est : st len c = 2 * bc len c + 32 := rfl
  have lo0 : numBase ≤ lo len (.slot c 0) := by simp [lo]
  have nb : numBase = 3336 := rfl
  intro q hq
  simp only [primeR, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;>
    (try simp only [invOff, accOff]) <;> omega_arith

theorem primeR2_below (h : In Ex base bytes len args s) : ∀ q ∈ primeR len .half ++ primeR len .wide,
    q.1 + q.2 ≤ lo len (.slot .wide 9) ∧ (accOff + 4 ≤ q.1 ∨ q.1 + q.2 ≤ accOff) := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact primeR_below h .half q hq
  · exact primeR_below h .wide q hq

theorem primeIn_ok (h : In Ex base bytes len args s) (f : Nat) {i : Nat} (hi : i < 18) (o : Nat) (c : Ctx) {p : Nat}
    (hx : lo len (.slot .wide f) + bc len c ≤ bytes)
    (hxd : Apart (lo len (.slot c 0)) (bc len c) (lo len (.slot .wide f)) (bc len c))
    (hod : lo len (.slot .wide o) + bc len c ≤ bytes)
    (hoa : ∀ q ∈ primeR len c, q.1 + q.2 ≤ lo len (.slot .wide o))
    (hp : val32 s.mem base (lo len (.slot .wide f)) (cwc len c) = p)
    (hL1 : 1 ≤ (args i).toNat) (hL : (args i).toNat ≤ len)
    (hpL : p < 2 ^ (8 * (args i).toNat))
    (hb : 8 * Spec.Rsa.primeWords (args i).toNat ≤ bc len c)
    (hX : xv s.mem base len < 2 ^ (8 * bc len .wide)) :
    WP isa (primeIn f i o c) s fun u =>
      Frame (frameR base (s.gpr .esp) ((lo len (.slot .wide o), bc len c) :: primeR len c)) s.mem u.mem ∧
      (xv s.mem base len % safeM p = 2 ^ fixB len % safeM p →
        val32 u.mem base (lo len (.slot .wide o)) (2 * Spec.Rsa.primeWords (args i).toNat) =
          2 ^ r2Exp (args i).toNat % safeM p) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have nw' := h.scratch.nowrap
  have f8 := h.slot_fit c (j := 8) (by decide)
  have g := bc_ge h.lower' c
  have bw := bc_eq_cwc len c
  have s01 : lo len (.slot c 0) + st len c ≤ lo len (.slot c 1) := sl_le (len := len) c (by decide)
  have s13 : lo len (.slot c 1) + st len c ≤ lo len (.slot c 3) := sl_le (len := len) c (by decide)
  have s34 : lo len (.slot c 3) + st len c ≤ lo len (.slot c 4) := sl_le (len := len) c (by decide)
  have s47 : lo len (.slot c 4) + st len c ≤ lo len (.slot c 7) := sl_le (len := len) c (by decide)
  have s78 : lo len (.slot c 7) + st len c ≤ lo len (.slot c 8) := sl_le (len := len) c (by decide)
  have est : st len c = 2 * bc len c + 32 := rfl
  have lo0 : numBase ≤ lo len (.slot c 0) := by simp [lo]
  have nb : numBase = 3336 := rfl
  have hup := h.upper'
  have cb1 : cb len (one c) = bc len c := by simp [cb, one]
  have cw1 : cw len (one c) = cwc len c := by simp [cw, cwc, cb, one]
  have fitB : ∀ q ∈ baseR len c, q.1 + q.2 ≤ bytes := baseR_fit h c
  have fitR : ∀ q ∈ primeR len c, q.1 + q.2 ≤ bytes := primeR_fit h c
  have baseSub : ∀ q ∈ baseR len c, ∃ q' ∈ primeR len c,
      q'.1 ≤ q.1 ∧ q.1 + q.2 ≤ q'.1 + q'.2 := by
    intro q hq
    simp only [baseR, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨(invOff, 4), by simp, Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨(lo len (.slot c 0), bc len c), by simp, Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨(lo len (.slot c 1), 3 * bc len c + 56), by simp, Nat.le_refl _, by dsimp only; omega_arith⟩
    · exact ⟨(lo len (.slot c 3), bc len c), by simp, Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨(lo len (.slot c 4), bc len c), by simp, Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨(lo len (.slot c 7), bc len c), by simp, Nat.le_refl _, Nat.le_refl _⟩
  have primeSub : ∀ q ∈ primeR len c, q ∈ (lo len (.slot .wide o), bc len c) :: primeR len c :=
    fun q hq => List.mem_cons_of_mem _ hq
  let L := (args i).toNat
  let w := Spec.Rsa.primeWords L
  have pw2 : 2 ≤ w := by simp only [w, Spec.Rsa.primeWords]; omega_arith
  have pwL : 8 * L ≤ 64 * w := by
    simp only [w, Spec.Rsa.primeWords, Spec.Rsa.modulusWords]; omega_arith
  unfold primeIn
  -- The factor into slot 0.
  refine WP.seq (WP.mono (copy_ok h (x := .slot .wide f) (d := .slot c 0) (one_ok c) (by rw [cb1]; exact hx)
    (by rw [cb1]; omega_arith) (by rw [cb1]; exact hxd)) fun u₁ ⟨O₁, V₁, K₁⟩ => ?_)
  rw [cb1] at O₁
  rw [cw1, hp] at V₁
  have h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega_arith))
  have sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  have F₁ : Frame (frameR base (s.gpr .esp) (primeR len c)) s.mem u₁.mem :=
    frameR_of_outside O₁ (by omega_arith) (by simp)
  -- Made safe, with its constants.
  refine WP.seq (WP.mono (prepCore_ok h₁ c) fun u₂ ⟨F₂, M₂, one₂, I₂, K₂⟩ => ?_)
  have h₂ := h₁.keepF K₂ (by decide) (by decide) F₂ fitB
  have sp₂ : u₂.gpr .esp = s.gpr .esp := (K₂.1 _ (by decide)).trans sp₁
  rw [sp₁] at F₂
  have V₁' : sv u₁.mem base len c 0 = p := by simp only [sv]; rw [V₁]
  have M₂' : sv u₂.mem base len c 0 = safeM p := by rw [M₂, V₁']
  have C₂ : CtxOk Ex base bytes len args c (safeM p) u₂ :=
    ⟨h₂, M₂', safeM_gt _, safeM_odd _, by rw [V₁'] at I₂; exact I₂⟩
  have F₁₂ : Frame (frameR base (s.gpr .esp) (primeR len c)) s.mem u₂.mem := F₁.trans (frameR_widen F₂ baseSub)
  have W18 := h.wide_fit (j := 18) (by decide)
  have bww := bc_eq_cwc len .wide
  have e9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide := rfl
  have e18w : lo len (.slot .wide 18) = numBase + 18 * st len .wide := rfl
  have X₂ : xv u₂.mem base len = xv s.mem base len :=
    low_keep h F₁₂ h.room fitR (fun q hq => (primeR_below h c q hq).1) (by omega_arith) (by omega_arith)
  -- `x R⁻ᴷ`, then `R_p² mod p`, in slot 4.
  refine WP.seq (WP.mono (reduceX_ok C₂ one₂ (by rw [X₂]; exact hX)) fun u₃ ⟨C₃, one₃, L₃, R₃, F₃, K₃⟩ => ?_)
  rw [sp₂] at F₃
  refine WP.seq (WP.mono (r2Fix_ok C₃ one₃ hi hL1 hL L₃ R₃) fun u₄ ⟨C₄, V₄, F₄, K₄⟩ => ?_)
  have sp₃ : u₃.gpr .esp = s.gpr .esp := (K₃.1 _ (by decide)).trans sp₂
  rw [sp₃] at F₄
  have h₃ := C₄.inp
  have F₃₄ : Frame (frameR base (s.gpr .esp) (primeR len c)) u₂.mem u₄.mem :=
    frameR_mono (F₃.trans F₄) (redR_sub len c)
  -- Into the wide slot `o`.
  have h4o : lo len (.slot c 4) + bc len c ≤ lo len (.slot .wide o) :=
    hoa (lo len (.slot c 4), bc len c) (by simp)
  refine WP.mono (copy_ok h₃ (x := .slot c 4) (d := .slot .wide o) (one_ok c) (by rw [cb1]; omega_arith)
    (by rw [cb1]; exact hod) (by rw [cb1]; exact .inr h4o)) fun u ⟨O, V, K⟩ => ?_
  rw [cb1] at O
  rw [cw1] at V
  have Fo : Frame (frameR base (s.gpr .esp) ((lo len (.slot .wide o), bc len c) :: primeR len c)) u₄.mem u.mem :=
    frameR_of_outside O (by omega_arith) (List.mem_cons_self ..)
  refine ⟨(frameR_mono (F₁₂.trans F₃₄) primeSub).trans Fo, fun hXp => ?_,
    (((K₁.mono (by decide)).trans K₂).trans (K₃.mono (by decide))).trans (K₄.trans (K.mono (by decide)))⟩
  have V₃ := V₄ (by rw [X₂]; exact hXp)
  have hV : 2 ^ r2Exp L % safeM p < 2 ^ (32 * (2 * w)) := by
      have hs : safeM p < 2 ^ (32 * (2 * w)) := by
        unfold safeM; split
        · exact Nat.lt_of_lt_of_le hpL (Nat.pow_le_pow_right (by decide) (by omega_arith))
        · exact Nat.lt_of_lt_of_le (by decide : 3 < 2 ^ 4) (Nat.pow_le_pow_right (by decide) (by omega_arith))
      exact Nat.lt_trans (Nat.mod_lt _ (by have := safeM_gt p; omega_arith)) hs
  refine val32_low (b := cwc len c - 2 * w) ?_ hV
  have ew : w = Spec.Rsa.primeWords (args i).toNat := rfl
  rw [show 2 * w + (cwc len c - 2 * w) = cwc len c by rw [ew]; omega_arith, V]
  exact V₃


/-- The ranges of the working space `factor f o` changes: `primeR` of both
widths, and the output, the wide slot `o`, as many bytes as either width has. -/
abbrev factorR (len o : Nat) : List (Nat × Nat) :=
  (lo len (.slot .wide o), bc len .half) :: (lo len (.slot .wide o), bc len .wide) ::
    (primeR len .half ++ primeR len .wide)

/-- `factor`'s test: the length of argument `i` against the half context's `Bc + 1`. -/
theorem factorTest_ok (h : In Ex base bytes len args s) {i : Nat} (hi : i < 18) :
    WP isa (.block (factorTest i)) s fun u => Keeps [.eax, .edx] s u ∧ u.mem = s.mem ∧
      isa.eval .b u = some (decide ((args i).toNat < bc len .half + 1)) := by
  have hb := bc_le h.upper' .half
  simp only [factorTest, List.cons_append]
  refine wp_movS (h.arg hi) fun u₁ a₁ _ => ?_
  have h₁ := h.regs a₁.keeps a₁.mem
  refine widthC_ok (k := 0) (c := .half) (r := .edx) h₁.width h.upper' fun u₂ K₂ m₂ e₂ => ?_
  refine wp_addS rfl fun u₃ a₃ _ => wp_cmpC rfl fun u₄ f₄ c₄ => WP.block_nil ?_
  have K₄ : Keeps [.eax, .edx] s u₄ :=
    (((a₁.keeps.mono (by decide)).trans (K₂.mono (by decide))).trans (a₃.keeps.mono (by decide))).trans
      (f₄.keeps _)
  have m₄ : u₄.mem = s.mem := by rw [f₄.mem, a₃.mem, m₂, a₁.mem]
  have eax : (u₃.gpr .eax).toNat = (args i).toNat := by
    rw [a₃.other _ (by decide), K₂.1 _ (by decide), a₁.gpr]
  have edx : (u₃.gpr .edx).toNat = bc len .half + 1 := by
    rw [a₃.gpr, e₂, BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
    omega_arith
  rw [eax, edx] at c₄
  exact ⟨K₄, m₄, c₄⟩

/-- A factor of `L` bytes (the header word at `lenOff`) in the wide slot `f`:
its `R_p² mod p` into the wide slot `o`, at half the width if `L` fits it. -/
theorem factor_ok (h : In Ex base bytes len args s) {f i o : Nat} (hf9 : 9 ≤ f) (hf : f ≤ 17) (hi : i < 18)
    (ho16 : 16 ≤ o) (ho : o ≤ 17) {p : Nat}
    (hp : val32 s.mem base (lo len (.slot .wide f)) (cwc len .wide) = p)
    (hL1 : 1 ≤ (args i).toNat) (hL : (args i).toNat ≤ len)
    (hpL : p < 2 ^ (8 * (args i).toNat)) (hX : xv s.mem base len < 2 ^ (8 * bc len .wide)) :
    WP isa (factor f i o) s fun u =>
      Frame (frameR base (s.gpr .esp) (factorR len o)) s.mem u.mem ∧
      (xv s.mem base len % safeM p = 2 ^ fixB len % safeM p →
        val32 u.mem base (lo len (.slot .wide o)) (2 * Spec.Rsa.primeWords (args i).toNat) =
          2 ^ r2Exp (args i).toNat % safeM p) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have hb := bc_le h.upper' .half
  have f0 := h.slot_fit .half (j := 0) (by decide)
  have ff := h.slot_fit .wide (j := f) (by omega_arith)
  have lo0 : numBase ≤ lo len (.slot .half 0) := by simp [lo]
  have bw := bc_eq_cwc len .wide
  have bwh := bc_le_wide len .half
  have dh := bc_dvd len .half
  have dw := bc_dvd len .wide
  have gh := bc_ge h.lower' .half
  have lw := len_le_bc len
  obtain ⟨cwle, cw8, bh, h0, _, h8, sth, top⟩ := HalfLay.mk' h
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have el : ∀ j, lo len (.slot .wide j) = numBase + j * st len .wide := fun _ => rfl
  have e0 : lo len (.slot .wide 0) = numBase := sl_zero len .wide
  have ef9 := Nat.mul_le_mul_right (st len .wide) hf9
  have e9 := el 9
  have efl := el f
  have eo := el o
  have fo := h.slot_fit .wide (j := o) (by omega_arith)
  have lo9 : lo len (.slot .wide 9) ≤ lo len (.slot .wide o) := by
    have := Nat.mul_le_mul_right (st len .wide) (show 9 ≤ o by omega_arith); omega_arith
  let L := (args i).toNat
  unfold factor
  refine WP.seq (WP.mono (factorTest_ok h hi) fun u₄ ⟨K₄, m₄, c₄⟩ => ?_)
  have h₄ := h.regs K₄ m₄
  have sp : u₄.gpr .esp = s.gpr .esp := K₄.1 _ (by decide)
  have hp' : val32 u₄.mem base (lo len (.slot .wide f)) (cwc len .wide) = p := by rw [m₄, hp]
  have X₄ : xv u₄.mem base len = xv s.mem base len := by simp only [xv]; rw [m₄]
  have hX₄ : xv u₄.mem base len < 2 ^ (8 * bc len .wide) := by rw [X₄]; exact hX
  have finish : ∀ (c : Ctx) (u : State),
      (Frame (frameR base (u₄.gpr .esp) ((lo len (.slot .wide o), bc len c) :: primeR len c)) u₄.mem u.mem ∧
      (xv u₄.mem base len % safeM p = 2 ^ fixB len % safeM p →
        val32 u.mem base (lo len (.slot .wide o)) (2 * Spec.Rsa.primeWords L) = 2 ^ r2Exp L % safeM p) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] u₄ u) →
      Frame (frameR base (s.gpr .esp) (factorR len o)) s.mem u.mem ∧
      (xv s.mem base len % safeM p = 2 ^ fixB len % safeM p →
        val32 u.mem base (lo len (.slot .wide o)) (2 * Spec.Rsa.primeWords L) = 2 ^ r2Exp L % safeM p) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
    intro c u ⟨F, V, K⟩
    rw [m₄, sp] at F
    refine ⟨frameR_mono F fun q hq => ?_, fun e => V (by rw [X₄]; exact e), (K₄.mono (by decide)).trans K⟩
    simp only [factorR, List.mem_cons, List.mem_append] at hq ⊢
    cases c <;> rcases hq with rfl | hq <;> simp_all
  refine WP.ite _ c₄ (fun nar => ?_) (fun wid => ?_)
  · have hLh : L ≤ bc len .half := by have := of_decide_eq_true nar; omega_arith
    have pw : 8 * Spec.Rsa.primeWords L ≤ bc len .half := by
      simp only [Spec.Rsa.primeWords, Spec.Rsa.modulusWords]; omega_arith
    have hph : val32 u₄.mem base (lo len (.slot .wide f)) (cwc len .half) = p := by
      refine CrtRt.val32_low (b := cwc len .wide - cwc len .half) (by
        rw [show cwc len .half + (cwc len .wide - cwc len .half) = cwc len .wide by omega_arith]; exact hp') ?_
      exact Nat.lt_of_lt_of_le hpL (Nat.pow_le_pow_right (by decide) (by omega_arith))
    exact WP.mono (primeIn_ok h₄ f hi o .half (by omega_arith) (by rw [h0]; exact .inl (by omega_arith))
      (by omega_arith) (fun q hq => Nat.le_trans (primeR_below h₄ .half q hq).1 lo9) hph hL1 hL hpL pw hX₄) (finish .half)
  · have pw : 8 * Spec.Rsa.primeWords L ≤ bc len .wide := by
      simp only [Spec.Rsa.primeWords, Spec.Rsa.modulusWords]; omega_arith
    exact WP.mono (primeIn_ok h₄ f hi o .wide (by omega_arith) (by rw [e0]; exact .inl (by omega_arith))
      (by omega_arith) (fun q hq => Nat.le_trans (primeR_below h₄ .wide q hq).1 lo9) hp' hL1 hL hpL pw hX₄) (finish .wide)

/-- `factorR`'s ranges: in the working space, apart from the word at `accOff`,
and either below the wide slot 9 or the slot `o`, of at most `Bw` bytes. -/
theorem factorR_props (h : In Ex base bytes len args s) {o : Nat} (ho16 : 16 ≤ o) (ho : o ≤ 17) :
    ∀ q ∈ factorR len o, q.1 + q.2 ≤ bytes ∧ (accOff + 4 ≤ q.1 ∨ q.1 + q.2 ≤ accOff) ∧
      (q.1 + q.2 ≤ lo len (.slot .wide 9) ∨ (q.1 = lo len (.slot .wide o) ∧ q.2 ≤ bc len .wide)) := by
  have fo := h.slot_fit .wide (j := o) (by omega_arith)
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have lo0 : numBase ≤ lo len (.slot .wide o) := by simp [lo]
  have nb : numBase = 3336 := rfl
  have bwh := bc_le_wide len .half
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact ⟨by dsimp only; omega_arith, .inl (by dsimp only; simp only [accOff]; omega_arith),
      .inr ⟨rfl, bwh⟩⟩
  rcases List.mem_cons.mp hq with rfl | hq'
  · exact ⟨by dsimp only; omega_arith, .inl (by dsimp only; simp only [accOff]; omega_arith),
      .inr ⟨rfl, Nat.le_refl _⟩⟩
  · exact ⟨primeR2_fit h q hq', (primeR2_below h q hq').2, .inl (primeR2_below h q hq').1⟩

/-- `factorR`'s ranges miss bytes 32 to 48 of the working space. -/
theorem factorR_saved {o : Nat} : ∀ q ∈ factorR len o, 48 ≤ q.1 ∨ q.1 + q.2 ≤ 32 := by
  have lo0 : ∀ c j, numBase ≤ lo len (.slot c j) := fun c j => by simp [lo]
  have nb : numBase = 3336 := rfl
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact .inl (by have := lo0 .wide o; dsimp only; omega)
  rcases List.mem_cons.mp hq with rfl | hq
  · exact .inl (by have := lo0 .wide o; dsimp only; omega)
  rcases List.mem_append.mp hq with hq | hq <;>
    simp only [primeR, List.mem_cons, List.not_mem_nil, or_false] at hq <;>
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> (try simp only [invOff]) <;>
    first | exact .inr (by decide) | exact .inl (Nat.le_trans (by decide : (48 : Nat) ≤ numBase) (lo0 _ _))

end

end VG.Proof.Bignum.X86.PrivPre
