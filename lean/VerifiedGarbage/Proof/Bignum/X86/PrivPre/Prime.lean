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
open VG.Impl.Bignum.X86.PrivPre (shl primeWords r2Prime writePrime copyWords outOff primeIn factor)
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

/-- The `8 w_p` bytes of slot 4 to `P + y`, where the header word at
`outOff` points, which then points past them. -/
theorem writePrime_ok (h : In Ex base bytes len args s) (c : Ctx) {P : Addr} {L' y : Nat}
    (hpw : InRegions s.wr P L') (hn : P.toNat + L' ≤ 2 ^ 32) (hap : Region.Disjoint ⟨P, L'⟩ ⟨base, bytes⟩)
    (hL1 : 1 ≤ w32 s.mem base lenOff) (hL : w32 s.mem base lenOff ≤ len)
    (ho : w32 s.mem base outOff = P.toNat + y)
    (hy : y + 8 * Spec.Rsa.primeWords (w32 s.mem base lenOff) ≤ L')
    (hb : 8 * Spec.Rsa.primeWords (w32 s.mem base lenOff) ≤ bc len c) :
    WP isa (writePrime c) s fun u =>
      (∃ m₁, Outside base outOff 4 s.mem m₁ ∧
        Outside P y (8 * Spec.Rsa.primeWords (w32 s.mem base lenOff)) m₁ u.mem) ∧
      val32 u.mem P y (2 * Spec.Rsa.primeWords (w32 s.mem base lenOff)) =
        val32 s.mem base (lo len (.slot c 4)) (2 * Spec.Rsa.primeWords (w32 s.mem base lenOff)) ∧
      w32 u.mem base outOff = (P.toNat + y + 8 * Spec.Rsa.primeWords (w32 s.mem base lenOff)) % 2 ^ 32 ∧
      Keeps [.eax, .ecx, .edx, .ebp, .esi] s u := by
  have nw' := h.scratch.nowrap
  have f8 := h.slot_fit c (j := 8) (by decide)
  have g := bc_ge h.lower' c
  have s48 : lo len (.slot c 4) + st len c ≤ lo len (.slot c 8) := sl_le (len := len) c (by decide)
  have est : st len c = 2 * bc len c + 32 := rfl
  have nb : numBase = 3336 := rfl
  have oo : outOff = 4 := rfl
  have hup := h.upper'
  have f0 := h.slot_fit c (j := 0) (by decide)
  have lo0 : numBase ≤ lo len (.slot c 0) := by simp [lo]
  have s04 : lo len (.slot c 0) + st len c ≤ lo len (.slot c 4) := sl_le (len := len) c (by decide)
  let L := w32 s.mem base lenOff
  let w := Spec.Rsa.primeWords L
  have pw : w ≤ 128 := by simp only [w, Spec.Rsa.primeWords, Spec.Rsa.modulusWords]; omega_arith
  have pw2 : 2 ≤ w := by simp only [w, Spec.Rsa.primeWords]; omega_arith
  have hP := P.isLt
  unfold writePrime
  simp only [primeWords, List.append_assoc, List.cons_append]
  refine WP.seq (WP.mono (Q := fun (t : State) => Keeps [.eax, .ecx, .edx, .ebp, .esi] s t ∧
    t.mem = s.mem.writeW (off base outOff) (BitVec.ofNat 32 (P.toNat + y + 8 * w)) ∧
    PtrAt t base .esi (lo len (.slot c 4)) ∧ PtrAt t P .ebp y ∧ (t.gpr .ecx).toNat = 4 * (2 * w)) ?_
    fun t ⟨Kt, mt, esit, ebpt, ecxt⟩ => ?_)
  · refine ptrTo_ok (r := .esi) (t := .edx) (by decide) (by decide) h.edi h.width h.upper' (by omega_arith)
      fun u₁ K₁ m₁ P₁ => ?_
    have h₁ := h.regs (K₁.mono (by decide) : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u₁) m₁
    refine wp_movS (readSrc_sc h₁.scratch (d := lenOff) (by simp only [lenOff]; omega_arith))
      fun u₂ a₂ _ => ?_
    refine wp_addS rfl fun u₃ a₃ _ => wp_shr (by decide) fun u₄ a₄ _ => wp_movS rfl fun u₅ a₅ _ => ?_
    refine wp_subS rfl fun u₆ a₆ _ => wp_shr (by decide) fun u₇ a₇ _ => wp_addS rfl fun u₈ a₈ _ => ?_
    refine shl_ok 3 fun u₉ K₉ m₉ e₉ => ?_
    have K₉' : Keeps [.edx, .esi, .ecx, .eax] s u₉ :=
      (((((((((K₁.mono (by decide)).trans (a₂.keeps.mono (by decide))).trans (a₃.keeps.mono (by decide))).trans
        (a₄.keeps.mono (by decide))).trans (a₅.keeps.mono (by decide))).trans (a₆.keeps.mono (by decide))).trans
        (a₇.keeps.mono (by decide))).trans (a₈.keeps.mono (by decide))).trans (K₉.mono (by decide)))
    have m₉' : u₉.mem = s.mem := by rw [m₉, a₈.mem, a₇.mem, a₆.mem, a₅.mem, a₄.mem, a₃.mem, a₂.mem, m₁]
    have h₉ := h.regs (K₉'.mono (by decide) : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u₉) m₉'
    refine wp_movS (readSrc_sc h₉.scratch (d := outOff) (by simp only [outOff, winOff]; omega_arith))
      fun u₁₀ a₁₀ _ => wp_movS rfl fun u₁₁ a₁₁ _ => wp_addS rfl fun u₁₂ a₁₂ _ => ?_
    have K₁₂ : Keeps [.edx, .esi, .ecx, .eax, .ebp] s u₁₂ :=
      ((K₉'.mono (by decide)).trans (a₁₀.keeps.mono (by decide))).trans
        ((a₁₁.keeps.mono (by decide)).trans (a₁₂.keeps.mono (by decide)))
    have m₁₂ : u₁₂.mem = s.mem := by rw [a₁₂.mem, a₁₁.mem, a₁₀.mem, m₉']
    have h₁₂ := h.regs (K₁₂.mono (by decide) : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u₁₂) m₁₂
    refine wp_storeS (h₁₂.scratch.ea (d := outOff) (by simp only [outOff, winOff]; omega_arith))
      (h₁₂.scratch.write (d := outOff) (by simp only [outOff, winOff]; omega_arith)) fun u₁₃ s₁₃ => WP.block_nil ?_
    have r₂ : u₂.gpr .ecx = BitVec.ofNat 32 L := by
      apply BitVec.eq_of_toNat_eq
      rw [a₂.gpr, BitVec.toNat_ofNat, m₁]
      simp only [L, w32]
      exact (Nat.mod_eq_of_lt (BitVec.isLt _)).symm
    have e₈ : u₈.gpr .ecx = u₄.gpr .ecx + (u₄.gpr .ecx - 2) >>> 31 := by
      rw [a₈.gpr, a₇.other _ (by decide), a₆.other _ (by decide), a₅.other _ (by decide), a₇.gpr, a₆.gpr,
        a₅.gpr]
    have r₄ : u₄.gpr .ecx = (BitVec.ofNat 32 L + 7) >>> 3 := by rw [a₄.gpr, a₃.gpr, r₂]
    have pv := primeWords_val L hL1 (by omega_arith)
    have ecx₁₂ : (u₁₂.gpr .ecx).toNat = 4 * (2 * w) := by
      rw [a₁₂.other _ (by decide), a₁₁.other _ (by decide), a₁₀.other _ (by decide), e₉, e₈, r₄, pv]
      omega_arith
    have ebp₁₀ : (u₁₀.gpr .ebp).toNat = P.toNat + y := by rw [a₁₀.gpr, m₉', ← ho]
    have ebp₁₂ : (u₁₂.gpr .ebp).toNat = P.toNat + y := by
      rw [a₁₂.other _ (by decide), a₁₁.other _ (by decide), ebp₁₀]
    have ecx₁₁ : (u₁₁.gpr .ecx).toNat = 4 * (2 * w) := by rw [← ecx₁₂, a₁₂.other _ (by decide)]
    have eax₁₂ : u₁₂.gpr .eax = BitVec.ofNat 32 (P.toNat + y + 8 * w) := by
      apply BitVec.eq_of_toNat_eq
      rw [a₁₂.gpr, a₁₁.gpr, BitVec.toNat_add, ebp₁₀, ecx₁₁, BitVec.toNat_ofNat]
      omega_arith
    refine ⟨(K₁₂.mono (by decide)).trans ((s₁₃.keeps []).mono fun _ h => by simp at h), by rw [s₁₃.mem, m₁₂, eax₁₂], ?_, ?_, ?_⟩
    · show (u₁₃.gpr .esi).toNat = _
      rw [s₁₃.gpr, a₁₂.other _ (by decide), a₁₁.other _ (by decide), a₁₀.other _ (by decide), K₉.1 _ (by decide),
        a₈.other _ (by decide), a₇.other _ (by decide), a₆.other _ (by decide), a₅.other _ (by decide),
        a₄.other _ (by decide), a₃.other _ (by decide), a₂.other _ (by decide)]
      exact P₁
    · show (u₁₃.gpr .ebp).toNat = _
      rw [s₁₃.gpr, ebp₁₂, Nat.mod_eq_of_lt (by omega_arith)]
    · rw [s₁₃.gpr]; exact ecx₁₂
  · have ew : w = Spec.Rsa.primeWords (w32 s.mem base lenOff) := rfl
    have ht : Ws t base bytes := ⟨by rw [Kt.2.2]; exact h.ws.wr, h.ws.nowrap⟩
    refine WP.mono (PrecomputeRt.copyOutLoop_ok (W := base) (L := bytes) ht (by rw [Kt.2.2]; exact hpw) hn hap
      (by omega_arith) (by rw [ew]; omega_arith) (by rw [ew]; omega_arith) esit ebpt ecxt) fun u ⟨Ou, Vu, Ku⟩ => ?_
    have hw4 : 4 * (2 * w) = 8 * w := by omega_arith
    rw [hw4] at Ou
    have Oh := writeW32_outside s.mem base (d := outOff) (BitVec.ofNat 32 (P.toNat + y + 8 * w))
      (by simp only [outOff, winOff]; omega)
    rw [← mt] at Oh
    refine ⟨⟨t.mem, Oh, Ou⟩, ?_, ?_, Kt.trans (Ku.mono (by decide))⟩
    · rw [Vu]
      exact Oh.val32 (.inr (by simp only [outOff, winOff]; omega_arith)) (by rw [ew]; omega_arith)
    · have := PrecomputedRt.val32_apart (base := P) (P := base) (L := bytes) (d := outOff) (k := 1) Ou (by omega_arith) hap.symm
        (by simp only [outOff, winOff]; omega_arith)
      rw [w32_val32_one, w32_val32_one, mt, w32_write_self, BitVec.toNat_ofNat] at this
      exact this

/-- The ranges of the working space `primeIn` changes: `prepBase`'s (the
factor into slot 0 among them), and the header word at `outOff`. -/
abbrev primeR (len : Nat) (c : Ctx) : List (Nat × Nat) := (outOff, 4) :: baseR len c

theorem primeIn_ok (h : In Ex base bytes len args s) (f : Nat) (c : Ctx) {p : Nat}
    (hx : lo len (.slot .wide f) + bc len c ≤ bytes)
    (hxd : Apart (lo len (.slot c 0)) (bc len c) (lo len (.slot .wide f)) (bc len c))
    (hp : val32 s.mem base (lo len (.slot .wide f)) (cwc len c) = p)
    (hL1 : 1 ≤ w32 s.mem base lenOff) (hL : w32 s.mem base lenOff ≤ len)
    (hpL : p < 2 ^ (8 * w32 s.mem base lenOff))
    (hb : 8 * Spec.Rsa.primeWords (w32 s.mem base lenOff) ≤ bc len c)
    {P : Addr} {L' y : Nat} (hpw : InRegions s.wr P L') (hn : P.toNat + L' ≤ 2 ^ 32)
    (hap : Region.Disjoint ⟨P, L'⟩ ⟨base, bytes⟩) (ho : w32 s.mem base outOff = P.toNat + y)
    (hy : y + 8 * Spec.Rsa.primeWords (w32 s.mem base lenOff) ≤ L') :
    WP isa (primeIn f c) s fun u =>
      (∃ m₁, Frame (frameR base (s.gpr .esp) (primeR len c)) s.mem m₁ ∧
        Outside P y (8 * Spec.Rsa.primeWords (w32 s.mem base lenOff)) m₁ u.mem) ∧
      val32 u.mem P y (2 * Spec.Rsa.primeWords (w32 s.mem base lenOff)) =
        2 ^ r2Exp (w32 s.mem base lenOff) % safeM p ∧
      w32 u.mem base outOff = (P.toNat + y + 8 * Spec.Rsa.primeWords (w32 s.mem base lenOff)) % 2 ^ 32 ∧
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
  have fitP : ∀ q ∈ primeR len c, q.1 + q.2 ≤ bytes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · simp only [outOff, winOff]; omega_arith
    · exact fitB q hq
  -- The header words `lenOff` and `outOff` are outside every range `prepBase` changes.
  have hdr : ∀ {d : Nat}, 4 ≤ d → d + 4 ≤ numBase → ∀ {sp : BitVec 32} {m m' : Mem},
      CallRoom sp base bytes → Frame (frameR base sp (baseR len c)) m m' → w32 m' base d = w32 m base d := by
    intro d hd4 hdn sp m m' R F
    have := frameR_val32 (d := d) (k := 1) F R nw' (by omega_arith) (by
      intro q hq
      simp only [baseR, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> (try simp only [invOff]) <;> omega_arith)
      fitB
    simpa only [w32_val32_one] using this
  have powSub : ∀ q ∈ powR len c, q ∈ baseR len c := by
    intro q hq; simp only [powR, baseR, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    rcases hq with rfl | rfl <;> simp
  have baseSub : ∀ q ∈ baseR len c, q ∈ primeR len c := fun q hq => List.mem_cons_of_mem _ hq
  let L := w32 s.mem base lenOff
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
    frameR_of_outside O₁ (by omega_arith) (by simp [primeR, baseR])
  have hdr₁ : ∀ {d : Nat}, 4 ≤ d → d + 4 ≤ numBase → w32 u₁.mem base d = w32 s.mem base d := by
    intro d hd4 hdn
    have := O₁.val32 (d := d) (k := 1) (.inl (by omega_arith)) (by omega_arith)
    simpa only [w32_val32_one] using this
  -- Made safe, with its constants.
  refine WP.seq (WP.mono (prepBase_ok h₁ c) fun u₂ ⟨F₂, M₂, _, _, _, K₂⟩ => ?_)
  have h₂ := h₁.keepF K₂ (by decide) (by decide) F₂ fitB
  have sp₂ : u₂.gpr .esp = s.gpr .esp := (K₂.1 _ (by decide)).trans sp₁
  rw [sp₁] at F₂
  have hdr₂ : ∀ {d : Nat}, 4 ≤ d → d + 4 ≤ numBase → w32 u₂.mem base d = w32 s.mem base d :=
    fun hd4 hdn => (hdr hd4 hdn h.room F₂).trans (hdr₁ hd4 hdn)
  have L₂ : w32 u₂.mem base lenOff = L := hdr₂ (by decide) (by decide)
  have M₂' : sv u₂.mem base len c 0 = safeM p := by rw [M₂]; simp only [sv]; rw [V₁]
  -- `R_p² mod p` in slot 4.
  refine WP.seq (WP.mono (r2Prime_ok h₂ c (by rw [M₂']; exact safeM_gt p) (by rw [L₂]; exact hL1)
    (by rw [L₂]; exact hL)) fun u₃ ⟨F₃, V₃, K₃⟩ => ?_)
  rw [sp₂] at F₃
  rw [L₂, M₂'] at V₃
  have h₃ := h₂.keepF K₃ (by decide) (by decide) (by rw [sp₂]; exact F₃) fun q hq => fitB q (powSub q hq)
  have sp₃ : u₃.gpr .esp = s.gpr .esp := (K₃.1 _ (by decide)).trans sp₂
  have hdr₃ : ∀ {d : Nat}, 4 ≤ d → d + 4 ≤ numBase → w32 u₃.mem base d = w32 s.mem base d :=
    fun hd4 hdn => (hdr hd4 hdn h.room (frameR_mono F₃ powSub)).trans (hdr₂ hd4 hdn)
  have L₃ : w32 u₃.mem base lenOff = L := hdr₃ (by decide) (by decide)
  have o₃ : w32 u₃.mem base outOff = P.toNat + y := (hdr₃ (by decide) (by decide)).trans ho
  have wr₃ : u₃.wr = s.wr := by rw [K₃.2.2, K₂.2.2, K₁.2.2]
  -- Written to `P + y`.
  refine WP.mono (writePrime_ok h₃ c (by rw [wr₃]; exact hpw) hn hap (by rw [L₃]; exact hL1) (by rw [L₃]; exact hL)
    o₃ (by rw [L₃]; exact hy) (by rw [L₃]; exact hb)) fun u ⟨⟨m₂, Oh, OP⟩, V, W, K⟩ => ?_
  rw [L₃] at OP V W
  have Fh : Frame (frameR base (s.gpr .esp) (primeR len c)) u₃.mem m₂ :=
    frameR_of_outside Oh (by simp only [outOff, winOff]; omega_arith) (List.mem_cons_self ..)
  refine ⟨⟨m₂, ((F₁.trans (frameR_mono F₂ baseSub)).trans (frameR_mono F₃ fun q hq => baseSub q (powSub q hq))).trans Fh,
    OP⟩, ?_, W, (((K₁.mono (by decide)).trans K₂).trans K₃).trans (K.mono (by decide))⟩
  rw [V]
  have hV : 2 ^ r2Exp L % safeM p < 2 ^ (32 * (2 * w)) := by
    have hs : safeM p < 2 ^ (32 * (2 * w)) := by
      unfold safeM; split
      · exact Nat.lt_of_lt_of_le hpL (Nat.pow_le_pow_right (by decide) (by omega_arith))
      · exact Nat.lt_of_lt_of_le (by decide : 3 < 2 ^ 4) (Nat.pow_le_pow_right (by decide) (by omega_arith))
    exact Nat.lt_trans (Nat.mod_lt _ (by have := safeM_gt p; omega_arith)) hs
  refine val32_low (b := cwc len c - 2 * w) ?_ hV
  have ew : w = Spec.Rsa.primeWords (w32 s.mem base lenOff) := rfl
  rw [show 2 * w + (cwc len c - 2 * w) = cwc len c by rw [ew]; omega_arith]
  exact V₃
/-- `In`, after code that changes the registers `regs` and the memory only
within `[P + y, P + y + n)` of a region `⟨P, L'⟩` apart from the stack
arguments. -/
theorem in_keepOut (h : In Ex base bytes len args s) {t : State} {regs : List Reg} (K : Keeps regs s t)
    (di : .edi ∉ regs) (sp : .esp ∉ regs) {P : Addr} {y n L' : Nat} (O : Outside P y n s.mem t.mem)
    (hyn : y + n ≤ L') (hPa : ∀ i < 18, Region.Disjoint ⟨VG.Proof.Dsa.X86.stackAddress s i, 4⟩ ⟨P, L'⟩) :
    In Ex base bytes len args t := by
  refine ⟨h.scratch.of_keeps K di sp, h.lower, h.upper, fun i hi => ⟨(h.stack i hi).stack.keep K sp, ?_⟩,
    h.outLen, by rw [K.1 _ sp]; exact h.room, by rw [K.1 _ sp]; exact h.top, h.need, h.hbase, h.hbytes,
    by rw [K.2.1, K.2.2]; exact h.extra⟩
  rw [← (h.stack i hi).value]
  unfold VG.Proof.Dsa.X86.stackValue
  rw [show VG.Proof.Dsa.X86.stackAddress t i = VG.Proof.Dsa.X86.stackAddress s i by
    simp only [VG.Proof.Dsa.X86.stackAddress, K.1 _ sp]]
  apply Mem.readW_congr
  intro j hj
  exact PrecomputedRt.outside_apart O hyn fun hc =>
    hPa i hi _ (Offset.contains_base _ (by omega) (by omega)) hc

/-- A factor of `L` bytes (the header word at `lenOff`) in the wide slot `f`:
its `R_p² mod p` to `P + y`, at half the width if `L` fits it. -/
theorem factor_ok (h : In Ex base bytes len args s) {f : Nat} (hf9 : 9 ≤ f) (hf : f ≤ 17) {p : Nat}
    (hp : val32 s.mem base (lo len (.slot .wide f)) (cwc len .wide) = p)
    (hL1 : 1 ≤ w32 s.mem base lenOff) (hL : w32 s.mem base lenOff ≤ len)
    (hpL : p < 2 ^ (8 * w32 s.mem base lenOff))
    {P : Addr} {L' y : Nat} (hpw : InRegions s.wr P L') (hn : P.toNat + L' ≤ 2 ^ 32)
    (hap : Region.Disjoint ⟨P, L'⟩ ⟨base, bytes⟩) (ho : w32 s.mem base outOff = P.toNat + y)
    (hy : y + 8 * Spec.Rsa.primeWords (w32 s.mem base lenOff) ≤ L') :
    WP isa (factor f) s fun u =>
      (∃ m₁, Frame (frameR base (s.gpr .esp) (primeR len .half ++ primeR len .wide)) s.mem m₁ ∧
        Outside P y (8 * Spec.Rsa.primeWords (w32 s.mem base lenOff)) m₁ u.mem) ∧
      val32 u.mem P y (2 * Spec.Rsa.primeWords (w32 s.mem base lenOff)) =
        2 ^ r2Exp (w32 s.mem base lenOff) % safeM p ∧
      w32 u.mem base outOff = (P.toNat + y + 8 * Spec.Rsa.primeWords (w32 s.mem base lenOff)) % 2 ^ 32 ∧
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
  let L := w32 s.mem base lenOff
  unfold factor
  simp only [List.cons_append]
  refine WP.seq (wp_movS (readSrc_sc h.scratch (d := lenOff) (by simp only [lenOff, numBase] at *; omega_arith))
    fun u₁ a₁ _ => ?_)
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
  have wr₄ : u₄.wr = s.wr := K₄.2.2
  have finish : ∀ (c : Ctx) (u : State),
      ((∃ m₁, Frame (frameR base (u₄.gpr .esp) (primeR len c)) u₄.mem m₁ ∧
        Outside P y (8 * Spec.Rsa.primeWords (w32 u₄.mem base lenOff)) m₁ u.mem) ∧
      val32 u.mem P y (2 * Spec.Rsa.primeWords (w32 u₄.mem base lenOff)) =
        2 ^ r2Exp (w32 u₄.mem base lenOff) % safeM p ∧
      w32 u.mem base outOff = (P.toNat + y + 8 * Spec.Rsa.primeWords (w32 u₄.mem base lenOff)) % 2 ^ 32 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] u₄ u) →
      (∃ m₁, Frame (frameR base (s.gpr .esp) (primeR len .half ++ primeR len .wide)) s.mem m₁ ∧
        Outside P y (8 * Spec.Rsa.primeWords L) m₁ u.mem) ∧
      val32 u.mem P y (2 * Spec.Rsa.primeWords L) = 2 ^ r2Exp L % safeM p ∧
      w32 u.mem base outOff = (P.toNat + y + 8 * Spec.Rsa.primeWords L) % 2 ^ 32 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
    intro c u ⟨⟨m₁, F, O⟩, V, W, K⟩
    rw [m₄, sp] at F
    rw [m₄] at O V W
    refine ⟨⟨m₁, frameR_mono F fun q hq => ?_, O⟩, V, W, (K₄.mono (by decide)).trans K⟩
    cases c <;> first | exact List.mem_append_left _ hq | exact List.mem_append_right _ hq
  refine WP.ite _ c₄ (fun nar => ?_) (fun wid => ?_)
  · have hLh : L ≤ bc len .half := by have := of_decide_eq_true nar; omega_arith
    have pw : 8 * Spec.Rsa.primeWords L ≤ bc len .half := by
      simp only [Spec.Rsa.primeWords, Spec.Rsa.modulusWords]; omega_arith
    have hph : val32 u₄.mem base (lo len (.slot .wide f)) (cwc len .half) = p := by
      refine CrtRt.val32_low (b := cwc len .wide - cwc len .half) (by
        rw [show cwc len .half + (cwc len .wide - cwc len .half) = cwc len .wide by omega_arith]; exact hp') ?_
      exact Nat.lt_of_lt_of_le hpL (Nat.pow_le_pow_right (by decide) (by omega_arith))
    exact WP.mono (primeIn_ok h₄ f .half (by omega_arith) (by rw [h0]; exact .inl (by omega_arith)) hph
      (by rw [m₄]; exact hL1) (by rw [m₄]; exact hL) (by rw [m₄]; exact hpL) (by rw [m₄]; exact pw)
      (by rw [wr₄]; exact hpw) hn hap (by rw [m₄]; exact ho) (by rw [m₄]; exact hy)) (finish .half)
  · have pw : 8 * Spec.Rsa.primeWords L ≤ bc len .wide := by
      simp only [Spec.Rsa.primeWords, Spec.Rsa.modulusWords]; omega_arith
    exact WP.mono (primeIn_ok h₄ f .wide (by omega_arith) (by rw [e0]; exact .inl (by omega_arith)) hp'
      (by rw [m₄]; exact hL1) (by rw [m₄]; exact hL) (by rw [m₄]; exact hpL) (by rw [m₄]; exact pw)
      (by rw [wr₄]; exact hpw) hn hap (by rw [m₄]; exact ho) (by rw [m₄]; exact hy)) (finish .wide)

/-- `In`, after code that changes the registers `regs`, the working space's
ranges `ws` (and the stack below it), then the memory within
`[P + y, P + y + n)` of a region apart from the stack arguments. -/
theorem in_keepFOut (h : In Ex base bytes len args s) {t : State} {regs : List Reg} (K : Keeps regs s t)
    (di : .edi ∉ regs) (sp : .esp ∉ regs) {ws : List (Nat × Nat)} {m₁ : Mem}
    (F : Frame (frameR base (s.gpr .esp) ws) s.mem m₁) (hfit : ∀ p ∈ ws, p.1 + p.2 ≤ bytes)
    {P : Addr} {y n L' : Nat} (O : Outside P y n m₁ t.mem) (hyn : y + n ≤ L')
    (hPa : ∀ i < 18, Region.Disjoint ⟨VG.Proof.Dsa.X86.stackAddress s i, 4⟩ ⟨P, L'⟩) :
    In Ex base bytes len args t := by
  let t' : State := { t with mem := m₁ }
  have K' : Keeps regs s t' := ⟨K.1, K.2.1, K.2.2⟩
  have h' := h.keepF K' di sp F hfit
  have hPa' : ∀ i < 18, Region.Disjoint ⟨VG.Proof.Dsa.X86.stackAddress t' i, 4⟩ ⟨P, L'⟩ := by
    intro i hi
    rw [show VG.Proof.Dsa.X86.stackAddress t' i = VG.Proof.Dsa.X86.stackAddress s i by
      simp only [VG.Proof.Dsa.X86.stackAddress, t', K.1 _ sp]]
    exact hPa i hi
  exact in_keepOut h' (regs := []) ⟨fun _ _ => rfl, rfl, rfl⟩ (by decide) (by decide) O hyn hPa'

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
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;>
    (try simp only [invOff, outOff, winOff]) <;> omega_arith

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
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;>
    (try simp only [invOff, outOff, winOff, accOff]) <;> omega_arith

theorem primeR2_below (h : In Ex base bytes len args s) : ∀ q ∈ primeR len .half ++ primeR len .wide,
    q.1 + q.2 ≤ lo len (.slot .wide 9) ∧ (accOff + 4 ≤ q.1 ∨ q.1 + q.2 ≤ accOff) := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact primeR_below h .half q hq
  · exact primeR_below h .wide q hq

end

end VG.Proof.Bignum.X86.PrivPre
