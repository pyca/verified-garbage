module

public import VerifiedGarbage.Impl.Bignum.X86.CrtRt
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
public import VerifiedGarbage.Proof.Bignum.X86.CrtInputs
import VerifiedGarbage.Proof.Framework.Omega

/-! # The widths, slots and pointers of private CRT at a run-time width

The width of a context in bytes (`bc`: `B` wide, `Bh` half), the stride of
its slots (`st`), the offset of a number (`lo`) and of a count of bytes
(`cb`); `widthC` leaves `bc` in its register (`widthC_ok`), `ptrTo` a
pointer to a number (`ptrTo_ok`) and `cntTo` a count (`cntTo_ok`). `In`:
what every piece needs of its inputs.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt
open VG.Proof.Bignum.X86.PublicRt (wb wb_le wb_ge adds_ok wp_shr widthB_ok)
open VG.Impl.Bignum.X86.PublicRt (argAt widthB)

/-- The modulus's words of 64 bits. -/
abbrev mw (len : Nat) : Nat := Spec.Rsa.modulusWords len

/-- The bytes of a number of the context. -/
def bc (len : Nat) : Ctx → Nat
  | .wide => 8 * mw len
  | .half => 8 * ((mw len + 1) / 2)

/-- The stride of the context's slots. -/
abbrev st (len : Nat) (c : Ctx) : Nat := 2 * bc len c + 32

/-- The offset of a number. -/
def lo (len : Nat) : Loc → Nat
  | .slot c j => numBase + j * st len c
  | .fixed o => o

/-- A count of bytes. -/
def cb (len : Nat) (n : Cnt) : Nat := (if n.two then 2 else 1) * bc len n.c + n.extra

/-- The bytes the working space needs: the header, the product and its
multiplicand, and 28 wide slots. -/
abbrev need (len : Nat) : Nat := numBase + 28 * st len .wide

theorem bc_le {len : Nat} (hl : len ≤ 1024) (c : Ctx) : bc len c ≤ 1024 := by
  cases c <;> simp only [bc, mw, Spec.Rsa.modulusWords] <;> omega

theorem bc_ge {len : Nat} (hl : 64 ≤ len) (c : Ctx) : 32 ≤ bc len c := by
  have h := hl
  cases c
  · simp only [bc, mw, Spec.Rsa.modulusWords]; omega
  · simp only [bc, mw, Spec.Rsa.modulusWords]; omega

theorem bc_half_le (len : Nat) : bc len .half ≤ bc len .wide + 8 := by
  simp only [bc]; omega

theorem bc_half_le' (len : Nat) : 2 * bc len .half ≤ bc len .wide + 8 := by
  simp only [bc]; omega

theorem bc_dvd (len : Nat) (c : Ctx) : bc len c % 8 = 0 := by
  cases c <;> simp only [bc] <;> omega

theorem len_le_bc (len : Nat) : len ≤ bc len .wide := by
  simp only [bc, mw, Spec.Rsa.modulusWords]; omega

theorem bc_wide (len : Nat) : bc len .wide = wb len := rfl

theorem lo_slot (len : Nat) (c : Ctx) (j : Nat) : lo len (.slot c j) = numBase + j * st len c := rfl

/-- A slot of a context ends before the next. -/
theorem lo_succ (len : Nat) (c : Ctx) (j : Nat) :
    lo len (.slot c (j + 1)) = lo len (.slot c j) + st len c := by
  simp only [lo]; rw [Nat.succ_mul]; omega

theorem lo_lt {len : Nat} (hl : len ≤ 1024) (c : Ctx) {j : Nat} (hj : j ≤ 28) :
    lo len (.slot c j) + st len c ≤ numBase + 29 * 2080 := by
  have := bc_le hl c
  have : j * st len c ≤ 28 * 2080 := Nat.mul_le_mul hj (by simp only [st]; omega)
  simp only [lo, st] at *; omega

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `widthC k c r`: `r = bc len c`. -/
theorem widthC_ok {k len : Nat} {c : Ctx} {r : Reg}
    (hr : readSrc s (.mem (argAt k 1)) = some (BitVec.ofNat 32 len)) (hl : len ≤ 1024)
    (kk : ∀ t, Keeps [r] s t → t.mem = s.mem → t.gpr r = BitVec.ofNat 32 (bc len c) → WP isa (.block is) t Q) :
    WP isa (.block (widthC k c r ++ is)) s Q := by
  cases c with
  | wide => exact widthB_ok hr hl kk
  | half =>
    simp only [widthC, List.append_assoc, List.cons_append, List.nil_append]
    refine widthB_ok hr hl fun s₁ K₁ m₁ e₁ => wp_shr (by decide) fun s₂ u₂ => wp_addS rfl fun s₃ u₃ _ => ?_
    refine wp_shr (by decide) fun s₄ u₄ => wp_addS rfl fun s₅ u₅ _ => wp_addS rfl fun s₆ u₆ _ => ?_
    refine wp_addS rfl fun s₇ u₇ _ => ?_
    have w : ∀ {a b c : State}, Keeps [r] a b → Keeps [r] b c → Keeps [r] a c := fun h₁ h₂ => h₁.trans h₂
    refine kk s₇ (w (w (w (w (w (w K₁ u₂.keeps) u₃.keeps) u₄.keeps) u₅.keeps) u₆.keeps) u₇.keeps)
      (by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]) ?_
    rw [u₇.gpr, u₆.gpr, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, e₁]
    apply BitVec.eq_of_toNat_eq
    have hw := wb_le hl
    have e1 : (1 : BitVec 32).toNat = 1 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, e1]
    simp only [wb, bc, mw] at *
    have : Spec.Rsa.modulusWords len ≤ 128 := by simp only [Spec.Rsa.modulusWords]; omega
    rw [Nat.mod_eq_of_lt (a := 8 * Spec.Rsa.modulusWords len) (by omega)]
    omega

/-- `strideC c t`: `t = st len c`. -/
theorem strideC_ok {len : Nat} {c : Ctx} {t : Reg}
    (hr : readSrc s (.mem (argAt 0 1)) = some (BitVec.ofNat 32 len)) (hl : len ≤ 1024)
    (kk : ∀ u, Keeps [t] s u → u.mem = s.mem → u.gpr t = BitVec.ofNat 32 (st len c) → WP isa (.block is) u Q) :
    WP isa (.block (strideC c t ++ is)) s Q := by
  simp only [strideC, List.append_assoc, List.cons_append, List.nil_append]
  refine widthC_ok hr hl fun s₁ K₁ m₁ e₁ => wp_addS rfl fun s₂ u₂ _ => wp_addS rfl fun s₃ u₃ _ => ?_
  refine kk s₃ ((K₁.trans u₂.keeps).trans u₃.keeps) (by rw [u₃.mem, u₂.mem, m₁]) ?_
  rw [u₃.gpr, u₂.gpr, e₁]
  apply BitVec.eq_of_toNat_eq
  have := bc_le hl c
  have e32 : (32 : BitVec 32).toNat = 32 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, e32, st]
  rw [Nat.mod_eq_of_lt (a := bc len c) (by omega)]
  omega

/-- `ptrTo x r t`: `r` points to the number at `lo len x`; only `r` and `t` change. -/
theorem ptrTo_ok {base : Addr} {len : Nat} {x : Loc} {r t : Reg} (hrt : r ≠ t) (hte : t ≠ .edi)
    (hedi : (s.gpr .edi).toNat = base.toNat)
    (hr : readSrc s (.mem (argAt 0 1)) = some (BitVec.ofNat 32 len)) (hl : len ≤ 1024)
    (hx : lo len x < 2 ^ 32)
    (kk : ∀ u, Keeps [r, t] s u → u.mem = s.mem → PtrAt u base r (lo len x) → WP isa (.block is) u Q) :
    WP isa (.block (ptrTo x r t ++ is)) s Q := by
  cases x with
  | fixed o =>
    simp only [ptrTo, List.cons_append, List.nil_append]
    refine wp_movS rfl fun s₁ u₁ _ => wp_addS rfl fun s₂ u₂ _ => ?_
    refine kk s₂ ((u₁.keeps.trans u₂.keeps).mono (by simp)) (by rw [u₂.mem, u₁.mem]) ?_
    rw [PtrAt, u₂.gpr, u₁.gpr, BitVec.toNat_add, hedi, BitVec.toNat_ofNat]
    simp only [lo] at hx ⊢
    rw [Nat.mod_eq_of_lt (a := o) (by omega)]
  | slot c j =>
    simp only [ptrTo, List.append_assoc, List.cons_append, List.nil_append]
    refine strideC_ok hr hl fun s₁ K₁ m₁ e₁ => wp_movS rfl fun s₂ u₂ _ => wp_addS rfl fun s₃ u₃ _ => ?_
    refine adds_ok hrt j fun u K m e => ?_
    have et : s₃.gpr t = BitVec.ofNat 32 (st len c) := by
      rw [u₃.other _ hrt.symm, u₂.other _ hrt.symm, e₁]
    have edi₁ : s₁.gpr .edi = s.gpr .edi := K₁.1 _ (by simp [hte.symm])
    have K₃ : Keeps [r] s₁ u := (u₂.keeps.trans u₃.keeps).trans K
    refine kk u ((K₁.mono (by simp)).trans (K₃.mono (by simp))) (by rw [m, u₃.mem, u₂.mem, m₁]) ?_
    rw [PtrAt, e, u₃.gpr, u₂.gpr, et, edi₁]
    have := bc_le hl c
    have hS : (BitVec.ofNat 32 (st len c)).toNat = st len c := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by simp only [st]; omega)
    simp only [lo] at hx ⊢
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hS, hedi]
    rw [Nat.mod_eq_of_lt (a := numBase) (by simp only [numBase]; omega),
      Nat.mod_eq_of_lt (a := j * st len c) (by omega), Nat.mod_add_mod, Nat.add_assoc]

/-- `cntTo n r`: `r = cb len n`. -/
theorem cntTo_ok {len : Nat} {n : Cnt} {r : Reg}
    (hr : readSrc s (.mem (argAt 0 1)) = some (BitVec.ofNat 32 len)) (hl : len ≤ 1024) (he : n.extra ≤ 64)
    (kk : ∀ u, Keeps [r] s u → u.mem = s.mem → u.gpr r = BitVec.ofNat 32 (cb len n) → WP isa (.block is) u Q) :
    WP isa (.block (cntTo n r ++ is)) s Q := by
  obtain ⟨c, two, extra⟩ := n
  simp only at he
  have hb := bc_le hl c
  simp only [cntTo, List.append_assoc]
  refine widthC_ok hr hl fun s₁ K₁ m₁ e₁ => ?_
  have step2 : ∀ {u : State}, Keeps [r] s u → u.mem = s.mem → u.gpr r = BitVec.ofNat 32
      ((if two then 2 else 1) * bc len c) →
      WP isa (.block ((if extra = 0 then [] else [.alu .add r (.imm (BitVec.ofNat 32 extra))]) ++ is)) u Q := by
    intro u K m e
    split
    · rename_i h0
      refine kk u K m ?_
      rw [e, cb, h0, Nat.add_zero]
    · refine wp_addS rfl fun v uv _ => kk v (K.trans uv.keeps) (by rw [uv.mem, m]) ?_
      rw [uv.gpr, e, cb]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      have : (if two then 2 else 1) * bc len c ≤ 2048 := by split <;> omega
      rw [Nat.mod_eq_of_lt (a := extra) (by omega), Nat.mod_eq_of_lt (a := _ * bc len c) (by omega)]
  cases two with
  | false => exact step2 K₁ m₁ (by rw [e₁]; simp)
  | true =>
    simp only [ite_true, List.cons_append, List.nil_append]
    refine wp_addS rfl fun v uv _ => step2 (K₁.trans uv.keeps) (by rw [uv.mem, m₁]) ?_
    rw [uv.gpr, e₁]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, ite_true]
    rw [Nat.mod_eq_of_lt (a := bc len c) (by omega)]
    omega

end

end VG.Proof.Bignum.X86.CrtRt
