module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Prepare
public import VerifiedGarbage.Impl.Bignum.X86.PrivPre
public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute
import VerifiedGarbage.Proof.Framework.Omega

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
open VG.Impl.Bignum.X86.PrivPre (shl primeWords r2Prime)
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

theorem r2Prime_ok (h : In Ex base bytes len args s) (c : Ctx) (hM : 1 < sv s.mem base len c 0)
    (hL1 : 1 ≤ w32 s.mem base lenOff) (hL : w32 s.mem base lenOff ≤ len) :
    WP isa (r2Prime c) s fun u =>
      Frame (frameR base (s.gpr .esp) (powR len c)) s.mem u.mem ∧
      sv u.mem base len c 4 = 2 ^ r2Exp (w32 s.mem base lenOff) % sv s.mem base len c 0 ∧
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
  let L := w32 s.mem base lenOff
  have pw : Spec.Rsa.primeWords L ≤ 128 := by
    simp only [Spec.Rsa.primeWords, Spec.Rsa.modulusWords]; omega_arith
  have pw2 : 2 ≤ Spec.Rsa.primeWords L := by simp only [Spec.Rsa.primeWords]; omega_arith
  unfold r2Prime
  refine WP.seq (WP.mono (setSmall_ok (x := .slot c 4) h (one_ok c) (by rw [cb1]; omega_arith) (v := 1) (by decide))
    fun u₀ ⟨O₀, V₀, K₀⟩ => ?_)
  simp only [cb1, cw1] at O₀ V₀
  have h₀ := h.keep K₀ (by decide) (by decide) (O₀.mono (Nat.zero_le _) (by omega_arith))
  have M₀ : sv u₀.mem base len c 0 = sv s.mem base len c 0 := O₀.val32 (by omega_arith) (by omega_arith)
  have L₀ : w32 u₀.mem base lenOff = L := by
    have := O₀.val32 (d := lenOff) (k := 1) (.inl (by simp only [lenOff, numBase] at *; omega_arith))
      (by simp only [lenOff]; omega_arith)
    simpa [w32_val32_one] using this
  simp only [primeWords, List.cons_append]
  refine WP.seq (wp_movS (readSrc_sc h₀.scratch (d := lenOff) (by simp only [lenOff, numBase] at *; omega_arith))
    fun u₁ a₁ _ => ?_)
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
      rw [a₁.gpr, BitVec.toNat_ofNat, ← L₀]
      simp only [w32]
      exact (Nat.mod_eq_of_lt (BitVec.isLt _)).symm
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

end

end VG.Proof.Bignum.X86.PrivPre
