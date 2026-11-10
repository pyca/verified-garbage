module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Prepare
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
open VG.Impl.Bignum.X86.PrivPre (shl primeWords r2Prime primeIn factor)
open VG.Proof.Bignum.X86.PublicRt (count1_zf countLoop)

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

theorem r2Prime_ok (h : In Ex base bytes len args s) {i : Nat} (hi : i < 18) (c : Ctx)
    (hM : 1 < sv s.mem base len c 0) (hL1 : 1 ≤ (args i).toNat) (hL : (args i).toNat ≤ len) :
    WP isa (r2Prime i c) s fun u =>
      Frame (frameR base (s.gpr .esp) (powR len c)) s.mem u.mem ∧
      sv u.mem base len c 4 = 2 ^ r2Exp (args i).toNat % sv s.mem base len c 0 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have nw' := h.scratch.nowrap
  have f8 := h.slot_fit c (j := 8) (by decide)
  have g := bc_ge h.lower' c
  have hb := bc_le h.upper' c
  have bw := bc_eq_cwc len c
  have hup := h.upper'
  have s01 : lo len (.slot c 0) + st len c ≤ lo len (.slot c 1) := sl_le (len := len) c (by decide)
  have s14 : lo len (.slot c 1) + st len c ≤ lo len (.slot c 4) := sl_le (len := len) c (by decide)
  have s48 : lo len (.slot c 4) + st len c ≤ lo len (.slot c 8) := sl_le (len := len) c (by decide)
  have z0 : lo len (.slot c 0) = numBase := sl_zero len c
  have est : st len c = 2 * bc len c + 32 := rfl
  have cb1 : cb len (one c) = bc len c := by simp [cb, one]
  have cw1 : cw len (one c) = cwc len c := by simp [cw, cwc, cb, one]
  have fit : ∀ p ∈ powR len c, p.1 + p.2 ≤ bytes := by
    intro p hp
    simp only [powR, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> dsimp only <;> omega_arith
  let L := (args i).toNat
  have pw : Spec.Rsa.primeWords L ≤ 128 := by
    simp only [Spec.Rsa.primeWords, Spec.Rsa.modulusWords]; omega_arith
  have pw2 : 2 ≤ Spec.Rsa.primeWords L := by simp only [Spec.Rsa.primeWords]; omega_arith
  unfold r2Prime
  refine WP.seq (WP.mono (setSmall_ok (x := .slot c 4) h (one_ok c) (by rw [cb1]; omega_arith) (v := 1) (by decide))
    fun u₀ ⟨O₀, V₀, K₀⟩ => ?_)
  simp only [cb1, cw1] at O₀ V₀
  have h₀ := h.keep K₀ (by decide) (by decide) (O₀.mono (Nat.zero_le _) (by omega_arith))
  have M₀ : sv u₀.mem base len c 0 = sv s.mem base len c 0 := O₀.val32 (by omega_arith) (by omega_arith)
  simp only [primeWords, List.cons_append]
  refine WP.seq (wp_movS (h₀.arg hi) fun u₁ a₁ _ => ?_)
  refine wp_addS rfl fun u₂ a₂ _ => wp_shr (by decide) fun u₃ a₃ _ => wp_movS rfl fun u₄ a₄ _ => ?_
  refine wp_subS rfl fun u₅ a₅ _ => wp_shr (by decide) fun u₆ a₆ _ => wp_addS rfl fun u₇ a₇ _ => ?_
  refine shl_ok 7 fun u₈ K₈ m₈ e₈ => WP.block_nil ?_
  have K₈' : Keeps [.esi, .eax] u₀ u₈ :=
    ((((((((a₁.keeps.mono (by decide)).trans (a₂.keeps.mono (by decide))).trans (a₃.keeps.mono (by decide))).trans
      (a₄.keeps.mono (by decide))).trans (a₅.keeps.mono (by decide))).trans (a₆.keeps.mono (by decide))).trans
      (a₇.keeps.mono (by decide))).trans (K₈.mono (by decide)))
  have m₈' : u₈.mem = u₀.mem := by rw [m₈, a₇.mem, a₆.mem, a₅.mem, a₄.mem, a₃.mem, a₂.mem, a₁.mem]
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
  have h₈ := h₀.regs (K₈'.mono (by decide) : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] u₀ u₈) m₈'
  have sp₈ : u₈.gpr .esp = s.gpr .esp := by rw [K₈'.1 _ (by decide), K₀.1 _ (by decide)]
  let M := sv s.mem base len c 0
  let I : Nat → State → Prop := fun j t =>
    Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] u₈ t ∧
      Frame (frameR base (s.gpr .esp) (powR len c)) u₈.mem t.mem ∧
      sv t.mem base len c 4 = 2 ^ j % M ∧ (t.gpr .esi).toNat = r2Exp L - j
  have I₀ : I 0 u₈ := ⟨Keeps.refl _ _, Frame.refl _ _,
    by rw [m₈']; simp only [sv] at V₀ ⊢; rw [V₀, Nat.pow_zero, Nat.mod_eq_of_lt hM], by rw [esi₈]; rfl⟩
  refine WP.mono (countLoop (N := r2Exp L) (by simp only [r2Exp]; omega_arith) I ?_ I₀) fun t ⟨Kt, Ft, Vt, _⟩ => ?_
  · rintro j t hj ⟨Kt, Ft, Vt, esit⟩
    have ht := h₈.keepF Kt (by decide) (by decide) (by rw [sp₈]; exact Ft) fit
    have Mt : sv t.mem base len c 0 = M := by
      have := frameR_val32 (d := lo len (.slot c 0)) (k := cwc len c) Ft h.room nw' (by omega_arith) (by
        intro p hp
        simp only [powR, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> dsimp only <;> omega_arith) fit
      simp only [sv]; rw [this, m₈']; exact M₀
    have hM' : 0 < M := by omega_arith
    refine WP.mono (doubleStep_ok ht c (by rw [Vt, Mt]; exact Nat.mod_lt _ hM'))
      fun u ⟨Fu, Vu, esiu, zu, Ku⟩ => ?_
    obtain ⟨c₁, c₂⟩ := count1_zf esit hj
    have spt : t.gpr .esp = s.gpr .esp := by rw [Kt.1 _ (by decide), sp₈]
    refine ⟨⟨Kt.trans Ku, Ft.trans (by rw [← spt]; exact Fu), ?_, by rw [esiu]; exact c₁⟩, by rw [zu, c₂]⟩
    rw [Vu, Vt, Mt, ← Nat.add_mod, ← Nat.two_mul, Nat.mul_comm, ← Nat.pow_succ]
  · have K₈s : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u₈ := (K₀.mono (by decide)).trans (K₈'.mono (by decide))
    refine ⟨?_, Vt, K₈s.trans Kt⟩
    rw [← m₈'] at O₀
    exact (frameR_of_outside O₀ (by omega_arith) (by simp [powR])).trans Ft

/-- The ranges of the working space `primeIn` changes, but its output's: `prepBase`'s (the factor
into slot 0 among them). -/
abbrev primeR (len : Nat) (c : Ctx) : List (Nat × Nat) := baseR len c

theorem primeIn_ok (h : In Ex base bytes len args s) (f : Nat) {i : Nat} (hi : i < 18) (o : Nat) (c : Ctx) {p : Nat}
    (hx : lo len (.slot .wide f) + bc len c ≤ bytes)
    (hxd : Apart (lo len (.slot c 0)) (bc len c) (lo len (.slot .wide f)) (bc len c))
    (hod : lo len (.slot .wide o) + bc len c ≤ bytes)
    (hoa : ∀ q ∈ baseR len c, q.1 + q.2 ≤ lo len (.slot .wide o))
    (hp : val32 s.mem base (lo len (.slot .wide f)) (cwc len c) = p)
    (hL1 : 1 ≤ (args i).toNat) (hL : (args i).toNat ≤ len)
    (hpL : p < 2 ^ (8 * (args i).toNat))
    (hb : 8 * Spec.Rsa.primeWords (args i).toNat ≤ bc len c) :
    WP isa (primeIn f i o c) s fun u =>
      Frame (frameR base (s.gpr .esp) ((lo len (.slot .wide o), bc len c) :: baseR len c)) s.mem u.mem ∧
      val32 u.mem base (lo len (.slot .wide o)) (2 * Spec.Rsa.primeWords (args i).toNat) =
        2 ^ r2Exp (args i).toNat % safeM p ∧
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
  have fitB : ∀ q ∈ baseR len c, q.1 + q.2 ≤ bytes := by
    intro q hq
    simp only [baseR, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> (try simp only [invOff]) <;> omega_arith
  have powSub : ∀ q ∈ powR len c, q ∈ baseR len c := by
    intro q hq; simp only [powR, baseR, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    rcases hq with rfl | rfl <;> simp
  have baseSub : ∀ q ∈ baseR len c, q ∈ (lo len (.slot .wide o), bc len c) :: baseR len c :=
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
  have F₁ : Frame (frameR base (s.gpr .esp) ((lo len (.slot .wide o), bc len c) :: baseR len c)) s.mem u₁.mem :=
    frameR_of_outside O₁ (by omega_arith) (by simp [baseR])
  -- Made safe, with its constants.
  refine WP.seq (WP.mono (prepBase_ok h₁ c) fun u₂ ⟨F₂, M₂, _, _, _, K₂⟩ => ?_)
  have h₂ := h₁.keepF K₂ (by decide) (by decide) F₂ fitB
  have sp₂ : u₂.gpr .esp = s.gpr .esp := (K₂.1 _ (by decide)).trans sp₁
  rw [sp₁] at F₂
  have M₂' : sv u₂.mem base len c 0 = safeM p := by rw [M₂]; simp only [sv]; rw [V₁]
  -- `R_p² mod p` in slot 4.
  refine WP.seq (WP.mono (r2Prime_ok h₂ hi c (by rw [M₂']; exact safeM_gt p) hL1 hL) fun u₃ ⟨F₃, V₃, K₃⟩ => ?_)
  rw [sp₂] at F₃
  rw [M₂'] at V₃
  have h₃ := h₂.keepF K₃ (by decide) (by decide) (by rw [sp₂]; exact F₃) fun q hq => fitB q (powSub q hq)
  have sp₃ : u₃.gpr .esp = s.gpr .esp := (K₃.1 _ (by decide)).trans sp₂
  -- Into the wide slot `o`.
  have h4o : lo len (.slot c 4) + bc len c ≤ lo len (.slot .wide o) :=
    hoa _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..)))))
  refine WP.mono (copy_ok h₃ (x := .slot c 4) (d := .slot .wide o) (one_ok c) (by rw [cb1]; omega_arith)
    (by rw [cb1]; exact hod) (by rw [cb1]; exact .inr h4o)) fun u ⟨O, V, K⟩ => ?_
  rw [cb1] at O
  rw [cw1] at V
  have Fo : Frame (frameR base (s.gpr .esp) ((lo len (.slot .wide o), bc len c) :: baseR len c)) u₃.mem u.mem :=
    frameR_of_outside O (by omega_arith) (List.mem_cons_self ..)
  refine ⟨((F₁.trans (frameR_mono F₂ baseSub)).trans
      (frameR_mono F₃ fun q hq => baseSub q (powSub q hq))).trans Fo, ?_,
    (((K₁.mono (by decide)).trans K₂).trans K₃).trans (K.mono (by decide))⟩
  · have hV : 2 ^ r2Exp L % safeM p < 2 ^ (32 * (2 * w)) := by
      have hs : safeM p < 2 ^ (32 * (2 * w)) := by
        unfold safeM; split
        · exact Nat.lt_of_lt_of_le hpL (Nat.pow_le_pow_right (by decide) (by omega_arith))
        · exact Nat.lt_of_lt_of_le (by decide : 3 < 2 ^ 4) (Nat.pow_le_pow_right (by decide) (by omega_arith))
      exact Nat.lt_trans (Nat.mod_lt _ (by have := safeM_gt p; omega_arith)) hs
    refine val32_low (b := cwc len c - 2 * w) ?_ hV
    have ew : w = Spec.Rsa.primeWords (args i).toNat := rfl
    rw [show 2 * w + (cwc len c - 2 * w) = cwc len c by rw [ew]; omega_arith, V]
    exact V₃


theorem primeR_fit (h : In Ex base bytes len args s) (c : Ctx) : ∀ q ∈ primeR len c, q.1 + q.2 ≤ bytes := by
  have f8 := h.slot_fit c (j := 8) (by decide)
  have s01 : lo len (.slot c 0) + st len c ≤ lo len (.slot c 1) := sl_le (len := len) c (by decide)
  have s13 : lo len (.slot c 1) + st len c ≤ lo len (.slot c 3) := sl_le (len := len) c (by decide)
  have s34 : lo len (.slot c 3) + st len c ≤ lo len (.slot c 4) := sl_le (len := len) c (by decide)
  have s47 : lo len (.slot c 4) + st len c ≤ lo len (.slot c 7) := sl_le (len := len) c (by decide)
  have s78 : lo len (.slot c 7) + st len c ≤ lo len (.slot c 8) := sl_le (len := len) c (by decide)
  have est : st len c = 2 * bc len c + 32 := rfl
  have lo0 : numBase ≤ lo len (.slot c 0) := by simp [lo]
  have nb : numBase = 3336 := rfl
  intro q hq
  simp only [primeR, baseR, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;>
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
  have s47 : lo len (.slot c 4) + st len c ≤ lo len (.slot c 7) := sl_le (len := len) c (by decide)
  have s78 : lo len (.slot c 7) + st len c ≤ lo len (.slot c 8) := sl_le (len := len) c (by decide)
  have est : st len c = 2 * bc len c + 32 := rfl
  have lo0 : numBase ≤ lo len (.slot c 0) := by simp [lo]
  have nb : numBase = 3336 := rfl
  intro q hq
  simp only [primeR, baseR, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;>
    (try simp only [invOff, accOff]) <;> omega_arith

theorem primeR2_below (h : In Ex base bytes len args s) : ∀ q ∈ primeR len .half ++ primeR len .wide,
    q.1 + q.2 ≤ lo len (.slot .wide 9) ∧ (accOff + 4 ≤ q.1 ∨ q.1 + q.2 ≤ accOff) := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact primeR_below h .half q hq
  · exact primeR_below h .wide q hq

/-- The ranges of the working space `factor f o` changes: `primeR` of both
widths, and the output, the wide slot `o`, as many bytes as either width has. -/
abbrev factorR (len o : Nat) : List (Nat × Nat) :=
  (lo len (.slot .wide o), bc len .half) :: (lo len (.slot .wide o), bc len .wide) ::
    (primeR len .half ++ primeR len .wide)

/-- A factor of `L` bytes (the header word at `lenOff`) in the wide slot `f`:
its `R_p² mod p` into the wide slot `o`, at half the width if `L` fits it. -/
theorem factor_ok (h : In Ex base bytes len args s) {f i o : Nat} (hf9 : 9 ≤ f) (hf : f ≤ 17) (hi : i < 18)
    (ho16 : 16 ≤ o) (ho : o ≤ 17) {p : Nat}
    (hp : val32 s.mem base (lo len (.slot .wide f)) (cwc len .wide) = p)
    (hL1 : 1 ≤ (args i).toNat) (hL : (args i).toNat ≤ len)
    (hpL : p < 2 ^ (8 * (args i).toNat)) :
    WP isa (factor f i o) s fun u =>
      Frame (frameR base (s.gpr .esp) (factorR len o)) s.mem u.mem ∧
      val32 u.mem base (lo len (.slot .wide o)) (2 * Spec.Rsa.primeWords (args i).toNat) =
        2 ^ r2Exp (args i).toNat % safeM p ∧
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
  simp only [List.cons_append]
  refine WP.seq (wp_movS (h.arg hi) fun u₁ a₁ _ => ?_)
  have h₁ := h.regs a₁.keeps a₁.mem
  refine widthC_ok (k := 0) (c := .half) (r := .edx) h₁.width h.upper' fun u₂ K₂ m₂ e₂ => ?_
  refine wp_addS rfl fun u₃ a₃ _ => wp_cmpC rfl fun u₄ f₄ c₄ => WP.block_nil ?_
  have K₄ : Keeps [.eax, .edx] s u₄ :=
    (((a₁.keeps.mono (by decide)).trans (K₂.mono (by decide))).trans (a₃.keeps.mono (by decide))).trans
      (f₄.keeps _)
  have m₄ : u₄.mem = s.mem := by rw [f₄.mem, a₃.mem, m₂, a₁.mem]
  have h₄ := h.regs K₄ m₄
  have eax : (u₃.gpr .eax).toNat = L := by
    rw [a₃.other _ (by decide), K₂.1 _ (by decide), a₁.gpr]
  have edx : (u₃.gpr .edx).toNat = bc len .half + 1 := by
    rw [a₃.gpr, e₂, BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
    omega_arith
  rw [eax, edx] at c₄
  have sp : u₄.gpr .esp = s.gpr .esp := K₄.1 _ (by decide)
  have hp' : val32 u₄.mem base (lo len (.slot .wide f)) (cwc len .wide) = p := by rw [m₄, hp]
  have finish : ∀ (c : Ctx) (u : State),
      (Frame (frameR base (u₄.gpr .esp) ((lo len (.slot .wide o), bc len c) :: baseR len c)) u₄.mem u.mem ∧
      val32 u.mem base (lo len (.slot .wide o)) (2 * Spec.Rsa.primeWords L) = 2 ^ r2Exp L % safeM p ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] u₄ u) →
      Frame (frameR base (s.gpr .esp) (factorR len o)) s.mem u.mem ∧
      val32 u.mem base (lo len (.slot .wide o)) (2 * Spec.Rsa.primeWords L) = 2 ^ r2Exp L % safeM p ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
    intro c u ⟨F, V, K⟩
    rw [m₄, sp] at F
    refine ⟨frameR_mono F fun q hq => ?_, V, (K₄.mono (by decide)).trans K⟩
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
      (by omega_arith) (fun q hq => Nat.le_trans (primeR_below h₄ .half q hq).1 lo9) hph hL1 hL hpL pw) (finish .half)
  · have pw : 8 * Spec.Rsa.primeWords L ≤ bc len .wide := by
      simp only [Spec.Rsa.primeWords, Spec.Rsa.modulusWords]; omega_arith
    exact WP.mono (primeIn_ok h₄ f hi o .wide (by omega_arith) (by rw [e0]; exact .inl (by omega_arith))
      (by omega_arith) (fun q hq => Nat.le_trans (primeR_below h₄ .wide q hq).1 lo9) hp' hL1 hL hpL pw) (finish .wide)

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
    simp only [primeR, baseR, List.mem_cons, List.not_mem_nil, or_false] at hq <;>
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> (try simp only [invOff]) <;>
    first | exact .inr (by decide) | exact .inl (Nat.le_trans (by decide : (48 : Nat) ≤ numBase) (lo0 _ _))

end

end VG.Proof.Bignum.X86.PrivPre
