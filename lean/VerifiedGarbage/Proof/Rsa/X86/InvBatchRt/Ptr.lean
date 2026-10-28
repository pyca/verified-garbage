module

public import VerifiedGarbage.Impl.Rsa.X86.InvBatchRt
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
import VerifiedGarbage.Proof.Framework.Omega

/-! # Pointers and counts of the run-time-width batch

`ptr_ok`: a pointer at a `Ref`, `offset w arr + 2 w · half + byte` for the
modulus's `w` words (`4 n` bytes with `n = w / 2`); `nBytes_ok` and
`nBytesLess_ok`: the bytes of `n + e` and `n - 1` words.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Bignum.X86.PublicRt (wp_shr adds_ok)
open VG.Proof.Rsa.X86.Keys (arr)

/-- A `Ref`'s offset in the working space, for arrays of `w` words. -/
def rv (w : Nat) (x : Ref) : Nat := VG.Impl.Rsa.X86.InvBatch.offset w x.arr + x.half * (2 * w) + x.byte

theorem offset_eq (w j : Nat) : VG.Impl.Rsa.X86.InvBatch.offset w j = arr w j := by
  simp only [VG.Impl.Rsa.X86.InvBatch.offset, arr, VG.Proof.Rsa.X86.Keys.S, VG.Impl.Rsa.X86.Keys.hdr]
  rw [show 4 * (w + 2) = 4 * w + 8 by omega]

variable {L : Lay} {B : Addr} {len : Nat} {is : List Instr} {s : State} {Q : State → Prop}

/-- `ptr r x t`: `r` at `x`. -/
theorem ptr_ok {r t : Reg} {x : Ref} (hl : LenSrc L s len) (hle : len ≤ 4096)
    (hedi : (s.gpr .edi).toNat = B.toNat) (hrt : r ≠ t) (hte : t ≠ .edi) (hb : rv (kw len) x < 2 ^ 32)
    (k : ∀ u, Keeps [r, t] s u → u.mem = s.mem → PtrAt u B r (rv (kw len) x) → WP isa (.block is) u Q) :
    WP isa (.block (ptr L r x t ++ is)) s Q := by
  have hw := kw_bound hle
  have ha : arr (kw len) x.arr < 2 ^ 32 := by
    have := offset_eq (kw len) x.arr; simp only [rv] at hb; omega
  simp only [ptr, List.append_assoc]
  refine arrPtr_ok hl hle hedi hrt hte ha fun u K m P T => ?_
  -- The `n`-word steps.
  have half : ∀ {is' : List Instr} {Q' : State → Prop}, (∀ v, Keeps [r, t] s v → v.mem = s.mem →
      PtrAt v B r (arr (kw len) x.arr + x.half * (2 * kw len)) → WP isa (.block is') v Q') →
      WP isa (.block ((if x.half = 0 then [] else
        [.alu .sub t (.imm 8), .shift .shr t 1] ++ List.replicate x.half (.alu .add r (.reg t))) ++ is')) u Q' := by
    intro is' Q' k'
    split
    · next h =>
      rw [List.nil_append]
      refine k' u K m ?_
      rw [h, Nat.zero_mul, Nat.add_zero]; exact P
    · next h =>
      simp only [List.cons_append, List.nil_append]
      refine wp_subS rfl fun u₁ U₁ _ => wp_shr (by decide) fun u₂ U₂ _ => ?_
      have t₂ : (u₂.gpr t).toNat = 2 * kw len := by
        rw [U₂.gpr, BitVec.toNat_ushiftRight, U₁.gpr, BitVec.toNat_sub, T, Nat.shiftRight_eq_div_pow]
        simp only [show (8 : BitVec 32).toNat = 8 from rfl]; omega
      refine adds_ok hrt x.half fun v V mv ev => k' v ?_ ?_ ?_
      · exact ((K.trans (U₁.keeps.mono (by simp))).trans (U₂.keeps.mono (by simp))).trans (V.mono (by simp))
      · rw [mv, U₂.mem, U₁.mem, m]
      · have r₂ : u₂.gpr r = u.gpr r := by rw [U₂.other _ hrt, U₁.other _ hrt]
        rw [PtrAt, ev, r₂, t₂, BitVec.toNat_add, BitVec.toNat_ofNat, P]
        generalize x.half * (2 * kw len) = H
        omega
  refine half fun v V mv pv => ?_
  split
  · next h =>
    rw [List.nil_append]
    refine k v V mv ?_
    rw [show rv (kw len) x = arr (kw len) x.arr + x.half * (2 * kw len) by simp only [rv, offset_eq, h, Nat.add_zero]]
    exact pv
  · next h =>
    simp only [List.cons_append, List.nil_append]
    refine wp_addS rfl fun z Z _ => k z (V.trans (Z.keeps.mono (by simp))) (by rw [Z.mem, mv]) ?_
    rw [PtrAt, Z.gpr, BitVec.toNat_add, pv, rv, offset_eq, BitVec.toNat_ofNat]
    generalize x.half * (2 * kw len) = H at *
    omega

/-- `nBytes r e`: `r = 4 (n + e)` for `w = 2 n`. -/
theorem nBytes_ok {r : Reg} {e : Nat} (hl : LenSrc L s len) (hle : len ≤ 4096) (he : e ≤ 4)
    (k : ∀ u, Keeps [r] s u → u.mem = s.mem → (u.gpr r).toNat = 2 * kw len + 4 * e → WP isa (.block is) u Q) :
    WP isa (.block (nBytes L r e ++ is)) s Q := by
  have hw := kw_bound hle
  simp only [nBytes, List.append_assoc, List.cons_append, List.nil_append]
  refine bytesB_ok hl hle fun u K m E => wp_shr (by decide) fun u₁ U₁ _ => ?_
  have r₁ : (u₁.gpr r).toNat = 2 * kw len := by
    rw [U₁.gpr, BitVec.toNat_ushiftRight, E, Nat.shiftRight_eq_div_pow]; omega
  split
  · next h =>
    rw [List.nil_append]
    exact k u₁ (K.trans U₁.keeps) (by rw [U₁.mem, m]) (by rw [r₁, h, Nat.mul_zero, Nat.add_zero])
  · next h =>
    simp only [List.cons_append, List.nil_append]
    refine wp_addS rfl fun z Z _ => k z ((K.trans U₁.keeps).trans Z.keeps) (by rw [Z.mem, U₁.mem, m]) ?_
    rw [Z.gpr, BitVec.toNat_add, r₁, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 4 * e) (by omega)]
    omega

/-- `nBytesLess r`: `r = 4 (n - 1)` for `w = 2 n`, `n ≥ 1`. -/
theorem nBytesLess_ok {r : Reg} (hl : LenSrc L s len) (hle : len ≤ 4096) (hn : 2 ≤ kw len)
    (k : ∀ u, Keeps [r] s u → u.mem = s.mem → (u.gpr r).toNat = 2 * kw len - 4 → WP isa (.block is) u Q) :
    WP isa (.block (nBytesLess L r ++ is)) s Q := by
  have hw := kw_bound hle
  simp only [nBytesLess, List.append_assoc, List.cons_append, List.nil_append]
  refine bytesB_ok hl hle fun u K m E => wp_shr (by decide) fun u₁ U₁ _ => wp_subS rfl fun z Z _ => ?_
  refine k z ((K.trans U₁.keeps).trans Z.keeps) (by rw [Z.mem, U₁.mem, m]) ?_
  rw [Z.gpr, BitVec.toNat_sub, U₁.gpr, BitVec.toNat_ushiftRight, E, Nat.shiftRight_eq_div_pow]
  simp only [show (4 : BitVec 32).toNat = 4 from rfl]
  omega

end VG.Proof.Rsa.X86.InvBatchRt
