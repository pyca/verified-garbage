module

public import VerifiedGarbage.Impl.Bignum.X86.PublicRt
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Framework.Omega

/-! # The width and the pointers of public RSA at a run-time width

`widthB` leaves `B = 8 ⌈n_len / 8⌉` in its register (`widthB_ok`), `offAt`
the offset `256 + j B` of number `j` (`offAt_ok`) and `slotPtr` a pointer to
it (`slotPtr_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt

/-- The bytes of a number: `8 ⌈len / 8⌉`. -/
abbrev wb (len : Nat) : Nat := 8 * Spec.Rsa.modulusWords len

/-- The offset of number `j`. -/
abbrev numAt (len j : Nat) : Nat := numOff + j * wb len

theorem wb_le {len : Nat} (hl : len ≤ 1024) : wb len ≤ 1024 := by
  simp only [wb, Spec.Rsa.modulusWords]; omega

theorem wb_ge {len : Nat} (hl : 64 ≤ len) : 64 ≤ wb len := by
  simp only [wb, Spec.Rsa.modulusWords]; omega

theorem len_le_wb (len : Nat) : len ≤ wb len := by
  simp only [wb, Spec.Rsa.modulusWords]; omega

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_shr {d : Reg} {n : Nat} (hn : 1 ≤ n ∧ n ≤ 31)
    (k : ∀ t, Upd s t d (s.gpr d >>> n) → WP isa (.block is) t Q) :
    WP isa (.block (.shift .shr d n :: is)) s Q :=
  cons (by simp only [exec, execShift, hn, and_self, ite_true]; rfl) (k _ (Upd.setFlags _ _ _ _ _ _ _))

/-- `r += t`, `j` times. -/
theorem adds_ok {r t : Reg} (hrt : r ≠ t) (j : Nat)
    (k : ∀ u, Keeps [r] s u → u.mem = s.mem →
      u.gpr r = s.gpr r + BitVec.ofNat 32 (j * (s.gpr t).toNat) → WP isa (.block is) u Q) :
    WP isa (.block (List.replicate j (.alu .add r (.reg t)) ++ is)) s Q := by
  induction j generalizing s with
  | zero => exact k s (Keeps.refl _ _) rfl (by simp)
  | succ j ih =>
    rw [List.replicate_succ, List.cons_append]
    refine wp_addS rfl fun s₁ u₁ _ => ih fun u K m e => k u (u₁.keeps.trans K) (m.trans u₁.mem) ?_
    rw [e, u₁.gpr, u₁.other _ hrt.symm, BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.succ_mul, Nat.add_comm]
end

/-- `widthB k r`: `r = B`. -/
theorem widthB_ok {s : State} {is : List Instr} {Q : State → Prop} {k len : Nat} {r : Reg}
    (hr : readSrc s (.mem (argAt k 1)) = some (BitVec.ofNat 32 len)) (hl : len ≤ 1024)
    (kk : ∀ t, Keeps [r] s t → t.mem = s.mem → t.gpr r = BitVec.ofNat 32 (wb len) → WP isa (.block is) t Q) :
    WP isa (.block (widthB k r ++ is)) s Q := by
  simp only [widthB, List.cons_append, List.nil_append]
  refine wp_movS hr fun s₁ u₁ _ => wp_addS rfl fun s₂ u₂ _ => wp_shr (by decide) fun s₃ u₃ => ?_
  refine wp_addS rfl fun s₄ u₄ _ => wp_addS rfl fun s₅ u₅ _ => wp_addS rfl fun s₆ u₆ _ => ?_
  have w : ∀ {a b c : State}, Keeps [r] a b → Keeps [r] b c → Keeps [r] a c := fun h₁ h₂ => h₁.trans h₂
  refine kk s₆ (w (w (w (w (w u₁.keeps u₂.keeps) u₃.keeps) u₄.keeps) u₅.keeps) u₆.keeps)
    (by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]) ?_
  rw [u₆.gpr, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]
  apply BitVec.eq_of_toNat_eq
  have h7 : (BitVec.ofNat 32 len + 7).toNat = len + 7 := by
    have e7 : (7 : BitVec 32).toNat = 7 := rfl
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, e7, Nat.mod_eq_of_lt (a := len) (by omega)]
    omega
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, h7, BitVec.toNat_ofNat, wb, Spec.Rsa.modulusWords,
    Nat.shiftRight_eq_div_pow]
  omega

/-- `offAt r j t`: `r = 256 + j B`, `t = B`. -/
theorem offAt_ok {s : State} {is : List Instr} {Q : State → Prop} {len j : Nat} {r t : Reg} (hrt : r ≠ t)
    (hr : readSrc s (.mem (argAt 0 1)) = some (BitVec.ofNat 32 len)) (hl : len ≤ 1024) (hj : j ≤ 8)
    (kk : ∀ u, Keeps [r, t] s u → u.mem = s.mem → u.gpr r = BitVec.ofNat 32 (numAt len j) →
      u.gpr t = BitVec.ofNat 32 (wb len) → WP isa (.block is) u Q) :
    WP isa (.block (offAt r j t ++ is)) s Q := by
  have hw := wb_le hl
  simp only [offAt, List.append_assoc, List.cons_append]
  refine widthB_ok hr hl fun s₁ K₁ m₁ e₁ => wp_movS rfl fun s₂ u₂ _ => adds_ok hrt j fun u K m e => ?_
  have et : s₂.gpr t = BitVec.ofNat 32 (wb len) := by rw [u₂.other _ hrt.symm, e₁]
  refine kk u ((K₁.mono (by simp)).trans ((u₂.keeps.trans K).mono (by simp)))
    (by rw [m, u₂.mem, m₁]) ?_ (by rw [K.1 _ (by simp [hrt.symm]), et])
  rw [e, u₂.gpr, et]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, numAt, numOff]
  have : j * wb len ≤ 8 * 1024 := Nat.mul_le_mul hj hw
  rw [Nat.mod_eq_of_lt (a := wb len) (by omega), Nat.mod_eq_of_lt (a := j * wb len) (by omega)]

/-- `slotPtr r j t`: `r = edi + 256 + j B`, `t = B`. -/
theorem slotPtr_ok {s : State} {is : List Instr} {Q : State → Prop} {base : Addr} {len j : Nat} {r t : Reg}
    (hrt : r ≠ t) (hte : t ≠ .edi) (hedi : (s.gpr .edi).toNat = base.toNat)
    (hr : readSrc s (.mem (argAt 0 1)) = some (BitVec.ofNat 32 len)) (hl : len ≤ 1024) (hj : j ≤ 8)
    (kk : ∀ u, Keeps [r, t] s u → u.mem = s.mem → PtrAt u base r (numAt len j) →
      u.gpr t = BitVec.ofNat 32 (wb len) → WP isa (.block is) u Q) :
    WP isa (.block (slotPtr r j t ++ is)) s Q := by
  have hw := wb_le hl
  simp only [slotPtr, List.append_assoc, List.cons_append]
  refine widthB_ok hr hl fun s₁ K₁ m₁ e₁ => wp_movS rfl fun s₂ u₂ _ => wp_addS rfl fun s₃ u₃ _ => ?_
  refine adds_ok hrt j fun u K m e => ?_
  have et : s₃.gpr t = BitVec.ofNat 32 (wb len) := by
    rw [u₃.other _ hrt.symm, u₂.other _ hrt.symm, e₁]
  have edi₁ : s₁.gpr .edi = s.gpr .edi := K₁.1 _ (by simp [hte.symm])
  have K₃ : Keeps [r] s₁ u := (u₂.keeps.trans u₃.keeps).trans K
  refine kk u ((K₁.mono (by simp)).trans (K₃.mono (by simp)))
    (by rw [m, u₃.mem, u₂.mem, m₁]) ?_ (by rw [K.1 _ (by simp [hrt.symm]), et])
  rw [PtrAt, e, u₃.gpr, u₂.gpr, et, edi₁]
  have : j * wb len ≤ 8 * 1024 := Nat.mul_le_mul hj hw
  have hB : (BitVec.ofNat 32 (wb len)).toNat = wb len := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hB, hedi, numAt, numOff]
  rw [Nat.mod_eq_of_lt (a := 256) (by omega), Nat.mod_eq_of_lt (a := j * wb len) (by omega), Nat.mod_add_mod,
    Nat.add_assoc]

end VG.Proof.Bignum.X86.PublicRt
