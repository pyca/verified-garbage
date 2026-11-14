module

public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeRt.In
public import VerifiedGarbage.Impl.Bignum.X86.R2Words
import VerifiedGarbage.Proof.Framework.Omega

/-! # `R2Words` on x86: the top words' pointers

`width4` leaves `4 W' = 4 ⌈n_len / 4⌉` in its register (`width4_ok`), and
`topPtr r j i t` a pointer to word `W' - i` of number `j` (`topPtr_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.R2Words

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86.PublicRt VG.Impl.Bignum.X86.R2Words VG.Proof.Bignum.X86.PrecomputeRt

/-- `M`'s words up to its top word: `⌈len / 4⌉`. -/
abbrev wp (len : Nat) : Nat := (len + 3) / 4

theorem wp_le_nw {len : Nat} : 4 * wp len ≤ wb len := by
  simp only [wp, wb, Spec.Rsa.modulusWords]; omega_using []

/-- `width4 r`: `r = 4 W'`. -/
theorem width4_ok {s : State} {is : List Instr} {Q : State → Prop} {len : Nat} {r : Reg} {op : MemOp}
    (hr : readSrc s (.mem op) = some (BitVec.ofNat 32 len)) (hl : len ≤ 1024)
    (kk : ∀ t, Keeps [r] s t → t.mem = s.mem → t.gpr r = BitVec.ofNat 32 (4 * wp len) → WP isa (.block is) t Q) :
    WP isa (.block (width4 r op ++ is)) s Q := by
  simp only [width4, List.cons_append, List.nil_append]
  refine wp_movS hr fun s₁ u₁ _ => wp_addS rfl fun s₂ u₂ _ => VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun s₃ u₃ => ?_
  refine wp_addS rfl fun s₄ u₄ _ => wp_addS rfl fun s₅ u₅ _ => ?_
  have w : ∀ {a b c : State}, Keeps [r] a b → Keeps [r] b c → Keeps [r] a c := fun h₁ h₂ => h₁.trans h₂
  refine kk s₅ (w (w (w (w u₁.keeps u₂.keeps) u₃.keeps) u₄.keeps) u₅.keeps)
    (by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]) ?_
  rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]
  apply BitVec.eq_of_toNat_eq
  have h3 : (BitVec.ofNat 32 len + 3).toNat = len + 3 := by
    have e3 : (3 : BitVec 32).toNat = 3 := rfl
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, e3, Nat.mod_eq_of_lt (a := len) (by omega_using [hl])]
    omega_using [hl]
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, h3, BitVec.toNat_ofNat, wp, Nat.shiftRight_eq_div_pow]
  omega_using []

/-- `topPtr r j i t`: `r = edi + 256 + j B + 4 W' - 4 i`, `t = 4 W'`. -/
theorem topPtr_ok {s : State} {is : List Instr} {Q : State → Prop} {base : Addr} {bytes len : Nat}
    {args : Nat → BitVec 32} {j i : Nat} {r t : Reg} (h : PcIn base bytes len args s)
    (hrt : r ≠ t) (hre : r ≠ .edi) (hte : t ≠ .edi) (hrs : r ≠ .esp) (hts : t ≠ .esp) (hj : j ≤ 8)
    (hi : 4 * i ≤ numAt len j + 4 * wp len)
    (kk : ∀ u, Keeps [r, t] s u → u.mem = s.mem → PtrAt u base r (numAt len j + 4 * wp len - 4 * i) →
      u.gpr t = BitVec.ofNat 32 (4 * wp len) → WP isa (.block is) u Q) :
    WP isa (.block (topPtr r j i t ++ is)) s Q := by
  have hw := wb_le h.upper
  simp only [topPtr, List.append_assoc, List.cons_append]
  refine slotPtr_ok hrt hte h.edi h.width h.upper hj fun u₁ K₁ m₁ p₁ _ => ?_
  have h₁ := h.keep K₁ (by simp [hre.symm, hte.symm]) (by simp [hrs.symm, hts.symm])
    (by rw [m₁]; exact Outside.refl _ _ _ _)
  refine width4_ok h₁.width h.upper fun u₂ K₂ m₂ e₂ => wp_addS rfl fun u₃ U₃ _ => wp_subS rfl fun u₄ U₄ _ => ?_
  have K : Keeps [r, t] s u₄ := (K₁.trans (K₂.mono (by simp))).trans
    ((U₃.keeps.mono (by simp)).trans (U₄.keeps.mono (by simp)))
  refine kk u₄ K (by rw [U₄.mem, U₃.mem, m₂, m₁]) ?_ (by rw [U₄.other _ hrt.symm, U₃.other _ hrt.symm, e₂])
  have nw := h.scratch.nowrap
  have hu := h.upper
  have hjw := Nat.mul_le_mul hj hw
  have hp₂ : PtrAt u₂ base r (numAt len j) := by rw [PtrAt, K₂.1 _ (by simp [hrt])]; exact p₁
  rw [PtrAt, U₄.gpr, U₃.gpr, e₂]
  have h4 : (BitVec.ofNat 32 (4 * wp len)).toNat = 4 * wp len := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by simp only [wp]; omega_using [hu])
  have hi4 : (BitVec.ofNat 32 (4 * i)).toNat = 4 * i := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by simp only [numAt, numOff, wp] at hi hjw ⊢; omega_using [hi, hu, hjw])
  rw [BitVec.toNat_sub, BitVec.toNat_add, hp₂, h4, hi4]
  have := base.isLt
  omega_using [hi, hi4]

end VG.Proof.Bignum.X86.R2Words
