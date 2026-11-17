module

import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Prepare
import VerifiedGarbage.Proof.Rc4.AArch64.Rows
import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Impl.MlKem.AArch64.Cbd16
import VerifiedGarbage.Proof.Blowfish.AArch64.Lanes
import VerifiedGarbage.Proof.Framework.AArch64.Simd
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
public import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Base
public import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Lanes
public import VerifiedGarbage.Proof.MlKem.AArch64.Common
public import VerifiedGarbage.Proof.MlKem.Mem16Bytes
import VerifiedGarbage.Proof.MlKem.AArch64.Coeff16

/-! ### `MlKem.AArch64.Cbd16W.Loop`, which this module and modules that import it used -/

section

/-! ### `MlKem.AArch64.Cbd16.Input`, which only this module used -/

section

/-! # Input bytes and the CBD2 specification -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Cbd16
open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem

theorem G_nibble (s : State) {i : Nat} (hi : i < 256) :
    (Cbd2.G s i).toNat =
      ((nibble (BitVec.ofNat 8 (Cbd2.byte s (i/2))) (i%2 != 0)).toNat + 3327)%3329 := by
  have hv := (Cbd2.B s).getD (i/2) 0 |>.isLt
  have hn := (nibble_values (Cbd2.byte s (i/2)) hv (i%2 != 0)).2
  rw [hn, Cbd2.G, samplePolyCBD2_val _ (show i < n from hi)]
  have hmod : (cbdX (VG.Proof.MlKem.nibble (Cbd2.B s) i) + q -
    cbdY (VG.Proof.MlKem.nibble (Cbd2.B s) i))%q < 2^32 := by
    have := Nat.mod_lt (cbdX (VG.Proof.MlKem.nibble (Cbd2.B s) i) + q -
      cbdY (VG.Proof.MlKem.nibble (Cbd2.B s) i)) (show 0<q by decide)
    exact Nat.lt_trans this (by decide)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmod]
  unfold VG.Proof.MlKem.nibble
  rcases (by omega_using [] : i%2 = 0 ∨ i%2 = 1) with h | h <;> simp [h,q,Cbd2.byte]

end VG.Proof.MlKem.AArch64.Cbd16

end

end

/-! ### `MlKem.AArch64.Cbd16W.Grp`, which only this module used -/

section

/-!
# `vg_mlkem16_cbd2` on AArch64: sixteen coefficients from their nibbles

`grp16`: the nibbles `f ≤ 4` of sixteen coefficients, in the bytes of `v4`,
are looked up in the tables of the low and high bytes of `(f - 2) mod q`
(`loV`, `hiV`), and the two bytes of each coefficient interleaved.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Cbd16W

open VG VG.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.MlKem.AArch64.Cbd16 (grp16)

/-- The low bytes of `(f - 2) mod q` at byte `f ≤ 4` of each doubleword. -/
def loV : BitVec 128 := ofVDwords 0x00000002010000FF 0x00000002010000FF
/-- Their high bytes. -/
def hiV : BitVec 128 := ofVDwords 0x0D0C 0x0D0C

theorem tables_val : ∀ f < 5,
    (vbyte loV f).toNat = (f + 3327) % 3329 % 256 ∧ (vbyte hiV f).toNat = (f + 3327) % 3329 / 256 := by
  decide

/-- The bytes of a table lookup of indices `F e ≤ 4`. -/
theorem vbyte_tbl {T x : BitVec 128} {F : Nat → Nat} (hx : ∀ e < 16, (vbyte x e).toNat = F e)
    (hf : ∀ e < 16, F e ≤ 4) {e : Nat} (he : e < 16) :
    vbyte (ofVBytes fun i => if (vbyte x i).toNat < 16 then vbyte T (vbyte x i).toNat else 0) e =
      vbyte T (F e) := by
  rw [vbyte_ofVBytes _ he, hx e he, ite_eq_left (by have := hf e he; omega_using [this])]

/-- The interleaved bytes of the coefficient of nibble `F (b / 2)`. -/
theorem vbyte_zip_tbl {lo hi : BitVec 128} {F : Nat → Nat} (hf : ∀ e < 16, F e ≤ 4)
    (hl : ∀ e < 16, vbyte lo e = vbyte loV (F e)) (hh : ∀ e < 16, vbyte hi e = vbyte hiV (F e))
    {b : Nat} (hb : b < 16) :
    (vbyte (VPermOp.eval .zip1 .b16 lo hi) b).toNat = (F (b / 2) + 3327) % 3329 / 256 ^ (b % 2) % 256 ∧
      (vbyte (VPermOp.eval .zip2 .b16 lo hi) b).toNat =
        (F (8 + b / 2) + 3327) % 3329 / 256 ^ (b % 2) % 256 := by
  rw [VG.Proof.Blowfish.AArch64.vbyte_zip1 _ _ hb, VG.Proof.Blowfish.AArch64.vbyte_zip2 _ _ hb]
  have t1 := tables_val (F (b / 2)) (by have := hf (b / 2) (by omega_using [hb]); omega_using [this])
  have t2 := tables_val (F (8 + b / 2)) (by have := hf (8 + b / 2) (by omega_using [hb]); omega_using [this])
  rcases Nat.mod_two_eq_zero_or_one b with h | h
  · rw [ite_eq_left h, ite_eq_left h, hl _ (by omega_using [hb]), hl _ (by omega_using [hb]), t1.1, t2.1, h,
      Nat.pow_zero, Nat.div_one, Nat.div_one]
    exact ⟨rfl, rfl⟩
  · rw [ite_eq_right (by omega_using [h]), ite_eq_right (by omega_using [h]), hh _ (by omega_using [hb]), hh _ (by omega_using [hb]), t1.2,
      t2.2, h, Nat.pow_one]
    have e : ∀ f, (f + 3327) % 3329 / 256 % 256 = (f + 3327) % 3329 / 256 := fun f =>
      Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by have := Nat.mod_lt (f + 3327) (show 3329 > 0 by decide); omega_using []))
    rw [e, e]
    exact ⟨rfl, rfl⟩

section
variable {rest : List Instr} {Q : State → Prop}

theorem grp16_ok {s : State} {off : Nat} {a : Addr} {F : Nat → Nat}
    (ho : off % 16 = 0 ∧ off + 16 < 4096 * 16)
    (ha : s.gpr .x1 + BitVec.ofNat 64 off = a) (hin : InRegions s.wr a 16)
    (hin' : InRegions s.wr (a + BitVec.ofNat 64 16) 16)
    (hlo : s.v .v16 = loV) (hhi : s.v .v17 = hiV)
    (hx : ∀ e < 16, (vbyte (s.v .v4) e).toNat = F e) (hf : ∀ e < 16, F e ≤ 4)
    (k : ∀ t (x y : BitVec 128), t.gpr = s.gpr → t.rd = s.rd → t.wr = s.wr → t.sp = s.sp →
      (∀ r, r ≠ .v5 → r ≠ .v6 → r ≠ .v7 → t.v r = s.v r) →
      t.mem = (s.mem.write a 16 x).write (a + BitVec.ofNat 64 16) 16 y →
      (∀ b < 16, (vbyte x b).toNat = (F (b / 2) + 3327) % 3329 / 256 ^ (b % 2) % 256) →
      (∀ b < 16, (vbyte y b).toNat = (F (8 + b / 2) + 3327) % 3329 / 256 ^ (b % 2) % 256) →
      WP isa (.block rest) t Q) :
    WP isa (.block (grp16 off ++ rest)) s Q := by
  unfold grp16
  simp only [List.cons_append, List.nil_append]
  refine wp_vop rfl fun s1 h1 => wp_vop rfl fun s2 h2 => wp_vop rfl fun s3 h3 =>
    wp_vop rfl fun s4 h4 => ?_
  have l5 : ∀ e < 16, vbyte (s2.v .v5) e = vbyte loV (F e) := fun e he => by
    rw [h2.get .v5, h1.v, hlo]; exact vbyte_tbl hx hf he
  have l6 : ∀ e < 16, vbyte (s2.v .v6) e = vbyte hiV (F e) := fun e he => by
    rw [h2.v, h1.get .v4, h1.get .v17, hhi]; exact vbyte_tbl hx hf he
  refine wp_strq (a := a) ⟨ho.1, by omega_using [ho]⟩ (by rw [h4.gpr, h3.gpr, h2.gpr, h1.gpr]; exact ha)
    (by rw [h4.wr, h3.wr, h2.wr, h1.wr]; exact hin) fun s5 h5 => ?_
  refine wp_strq (a := a + BitVec.ofNat 64 16) ⟨by omega_using [ho], ho.2⟩
    (by rw [h5.gpr, h4.gpr, h3.gpr, h2.gpr, h1.gpr, ← ha, BitVec.add_assoc, ← BitVec.ofNat_add])
    (by rw [h5.wr, h4.wr, h3.wr, h2.wr, h1.wr]; exact hin') fun s6 h6 => ?_
  refine k s6 (s3.v .v7) (s4.v .v5) (by rw [h6.gpr, h5.gpr, h4.gpr, h3.gpr, h2.gpr, h1.gpr])
    (by rw [h6.rd, h5.rd, h4.rd, h3.rd, h2.rd, h1.rd]) (by rw [h6.wr, h5.wr, h4.wr, h3.wr, h2.wr, h1.wr])
    (by rw [h6.sp, h5.sp, h4.sp, h3.sp, h2.sp, h1.sp]) (fun r r5 r6 r7 => ?_) ?_
    (fun b hb => ?_) (fun b hb => ?_)
  · rw [h6.v, h5.v, h4.get r r5, h3.get r r7, h2.get r r6, h1.get r r5]
  · rw [h6.mem, h5.mem, h4.mem, h3.mem, h2.mem, h1.mem, h5.v, h4.get .v7]
  · rw [h3.v]; exact (vbyte_zip_tbl hf l5 l6 hb).1
  · rw [h4.v, h3.get .v5, h3.get .v6]; exact (vbyte_zip_tbl hf l5 l6 hb).2

end
end VG.Proof.MlKem.AArch64.Cbd16W

end

end


/-! # `vg_mlkem16_cbd2` on AArch64: eight iterations of 32 coefficients -/

@[expose] public section

namespace VG.Proof.MlKem

open VG VG.AArch64 VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- AArch64 contract for `vg_mlkem16_cbd2(b = x0, f = x1)`: writes
`SamplePolyCBD₂` of the 128 bytes at `b` to `f` with 16-bit coefficients,
reduced. The code may read `b` and write `f`, which do not overlap. -/
def cbd2_16AArch64 : Contract AArch64.isa where
  pre s :=
    s.rd = [⟨s.gpr .x0, 128⟩] ∧ s.wr = [⟨s.gpr .x1, 512⟩] ∧
    Region.Disjoint ⟨s.gpr .x0, 128⟩ ⟨s.gpr .x1, 512⟩
  post s s' := PolyIsW 16 s'.mem (s.gpr .x1) (samplePolyCBD 2 (bytesAt s.mem (s.gpr .x0) 128))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp

end VG.Proof.MlKem

namespace VG.Proof.MlKem.AArch64.Cbd16W

open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Proof.MlKem.AArch64.Cbd16
open VG.Proof.Rc4.AArch64
open VG.Impl.MlKem.AArch64.Cbd16 (grp16 half16 body16 code16 tables constant prepare)
open VG.Spec.Sha3 (bytesAt)

section
variable (s₀ : State)

/-- The output. -/
abbrev fR : Region := ⟨Cbd2.fP s₀, 512⟩
/-- Coefficient `i` of the output. -/
abbrev coef (i : Nat) : Nat := ((samplePolyCBD 2 (Cbd2.B s₀))[i]!).val
/-- Byte `j` of the output: byte `j % 2` of coefficient `j / 2`. -/
def L (j : Nat) : Byte := bytesW16 (coef s₀) j
/-- The nibble of coefficient `32 k + i`. -/
abbrev nib (k i : Nat) : Nat :=
  (Cbd16.nibble (BitVec.ofNat 8 (Cbd2.byte s₀ (16 * k + i / 2))) (i % 2 != 0)).toNat

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [Cbd2.bR s₀]
  wr : s₀.wr = [fR s₀]
  disj : (Cbd2.bR s₀).Disjoint (fR s₀)

theorem Pre.byte_eq {s₀ : State} (hp : Pre s₀) {m : Mem} (hf : Frame [fR s₀] s₀.mem m)
    {j : Nat} (hj : j < 128) : (m (Cbd2.bP s₀ + BitVec.ofNat 64 j)).toNat = Cbd2.byte s₀ j := by
  rw [byte_frame (len := 128) hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.disj)
    (by decide) hj]
  show _ = ((bytesAt s₀.mem (Cbd2.bP s₀) 128).getD j 0).toNat
  rw [bytesAt_getD _ _ hj]

theorem nib_le (s₀ : State) (k i : Nat) : nib s₀ k i ≤ 4 :=
  (nibble_values _ (byte_lt _) _).1

/-- The bytes of the output, from the nibbles. -/
theorem L_nib (s₀ : State) {k i b : Nat} (hk : k < 8) (hi : i < 32) (hb : b < 2) :
    (L s₀ (64 * k + 2 * i + b)).toNat = (nib s₀ k i + 3327) % 3329 / 256 ^ b % 256 := by
  have hc : coef s₀ (32 * k + i) = (nib s₀ k i + 3327) % 3329 := by
    have h := G_nibble s₀ (i := 32 * k + i) (by omega_using [hk, hi])
    rw [Cbd2.G, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans (Fin.isLt _) (by decide)),
      show (32 * k + i) / 2 = 16 * k + i / 2 by omega_using [], show (32 * k + i) % 2 = i % 2 by omega_using []] at h
    exact h
  rw [L, bytesW16, BitVec.toNat_ofNat, show (64 * k + 2 * i + b) / 2 = 32 * k + i by omega_using [hb],
    show (64 * k + 2 * i + b) % 2 = b by omega_using [hb], hc]

/-- The constants of the loop. -/
structure Consts (s : State) : Prop where
  lo : s.v .v16 = loV
  hi : s.v .v17 = hiV
  c18 : s.v .v18 = broadcast 0x55
  c19 : s.v .v19 = broadcast 0x33
  c20 : s.v .v20 = broadcast 0x22
  c21 : s.v .v21 = broadcast 15

theorem Consts.of {s t : State} (h : Consts s) (hv : ∀ r, r ≠ .v0 → r ≠ .v1 → r ≠ .v2 → r ≠ .v3 →
    r ≠ .v4 → r ≠ .v5 → r ≠ .v6 → r ≠ .v7 → t.v r = s.v r) : Consts t :=
  ⟨by rw [hv _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact h.lo,
   by rw [hv _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact h.hi,
   by rw [hv _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact h.c18,
   by rw [hv _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact h.c19,
   by rw [hv _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact h.c20,
   by rw [hv _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact h.c21⟩

/-- The bytes of the output before the loop. -/
abbrev old (s₀ : State) (j : Nat) : Byte := s₀.mem (Cbd2.fP s₀ + BitVec.ofNat 64 j)

structure Inv (s₀ : State) (k : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x0 : s.gpr .x0 = Cbd2.bP s₀ + BitVec.ofNat 64 (16 * k)
  x1 : s.gpr .x1 = Cbd2.fP s₀ + BitVec.ofNat 64 (64 * k)
  count : (s.gpr .x10).toNat = 8 - k
  consts : Consts s
  out : BytesUpTo s.mem (Cbd2.fP s₀) 512 (64 * k) (L s₀) (old s₀)
  frame : Frame [fR s₀] s₀.mem s.mem

section
variable {rest : List Instr} {Q : State → Prop}

/-- Half an iteration: the 16 coefficients `32 k + 16 c + e`. -/
theorem half_ok {s₀ s : State} {k c off : Nat} (hk : k < 8) (hc : c < 2) (hoff : off = 32 * c)
    {part : VPermOp}
    (hw : s.wr = [fR s₀]) (hx1 : s.gpr .x1 = Cbd2.fP s₀ + BitVec.ofNat 64 (64 * k))
    (hcs : Consts s)
    (hv : ∀ e < 16, (vbyte (VPermOp.eval part .b16 (s.v .v2) (s.v .v3)) e).toNat = nib s₀ k (16 * c + e))
    (hout : BytesUpTo s.mem (Cbd2.fP s₀) 512 (64 * k + 32 * c) (L s₀) (old s₀))
    (hfr : Frame [fR s₀] s₀.mem s.mem)
    (k' : ∀ t, t.gpr = s.gpr → t.rd = s.rd → t.wr = s.wr → t.sp = s.sp →
      (∀ r, r ≠ .v4 → r ≠ .v5 → r ≠ .v6 → r ≠ .v7 → t.v r = s.v r) →
      BytesUpTo t.mem (Cbd2.fP s₀) 512 (64 * k + 32 * c + 32) (L s₀) (old s₀) →
      Frame [fR s₀] s₀.mem t.mem → WP isa (.block rest) t Q) :
    WP isa (.block (half16 off part ++ rest)) s Q := by
  subst hoff
  unfold half16
  simp only [List.cons_append, List.nil_append]
  refine wp_vop rfl fun s1 h1 => ?_
  have ea : Cbd2.fP s₀ + BitVec.ofNat 64 (64 * k) + BitVec.ofNat 64 (32 * c) =
      Cbd2.fP s₀ + BitVec.ofNat 64 (64 * k + 32 * c) := ptr_add _ _ _
  refine grp16_ok (F := fun e => nib s₀ k (16 * c + e)) (a := Cbd2.fP s₀ + BitVec.ofNat 64 (64 * k + 32 * c))
    (by omega_using [hc])
    (by rw [h1.gpr, hx1]; exact ea)
    (by rw [h1.wr, hw]; exact in_regions (List.mem_singleton_self _) (contains_off (by omega_using [hk, hc]) (by decide)))
    (by rw [h1.wr, hw, ptr_add]
        exact in_regions (List.mem_singleton_self _) (contains_off (by omega_using [hk, hc]) (by decide)))
    (by rw [h1.get .v16]; exact hcs.lo) (by rw [h1.get .v17]; exact hcs.hi)
    (by rw [h1.v]; exact hv) (fun e _ => nib_le _ _ _) fun t x y g rd wr sp tv tm hx hy => ?_
  have o1 := BytesUpTo.writeN (n := 16) hout (by decide) (by omega_using [hk, hc]) (x := x) fun b hb => by
    apply BitVec.eq_of_toNat_eq
    rw [show 64 * k + 32 * c + b = 64 * k + 2 * (16 * c + b / 2) + b % 2 by omega_using [],
      L_nib s₀ hk (by omega_using [hc, hb]) (Nat.mod_lt _ (by decide))]
    exact hx b hb
  have o2 := BytesUpTo.writeN (n := 16) o1 (by decide) (by omega_using [hk, hc]) (x := y) fun b hb => by
    apply BitVec.eq_of_toNat_eq
    rw [show 64 * k + 32 * c + 16 + b = 64 * k + 2 * (16 * c + (8 + b / 2)) + b % 2 by omega_using [],
      L_nib s₀ hk (by omega_using [hc, hb]) (Nat.mod_lt _ (by decide))]
    exact hy b hb
  refine k' t (g.trans h1.gpr) (rd.trans h1.rd) (wr.trans h1.wr) (sp.trans h1.sp)
    (fun r r4 r5 r6 r7 => by rw [tv r r5 r6 r7, h1.get r r4]) ?_ ?_
  · rw [tm, h1.mem, ptr_add, show 64 * k + 32 * c + 32 = 64 * k + 32 * c + 16 + 16 by omega_using []]
    exact o2
  · rw [tm, h1.mem]
    exact (hfr.write (n := 16) (List.mem_singleton_self _) _ (contains_off (by omega_using [hk, hc]) (by decide))).write
      (n := 16) (List.mem_singleton_self _) _ (by rw [ptr_add]; exact contains_off (by omega_using [hk, hc]) (by decide))

end

end VG.Proof.MlKem.AArch64.Cbd16W

end

end

/-! # `vg_mlkem16_cbd2` on AArch64: an iteration, and the loop -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Cbd16W

open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Proof.MlKem.AArch64.Cbd16
open VG.Proof.Rc4.AArch64
open VG.Impl.MlKem.AArch64.Cbd16 (half16 body16 code16 tables constant prepare)

theorem read_input {s₀ s : State} (hp : Pre s₀) {k : Nat} (hk : k < 8)
    (h : Inv s₀ k s) {e : Nat} (he : e < 16) :
    vbyte (s.mem.read (s.gpr .x0) 16) e = BitVec.ofNat 8 (Cbd2.byte s₀ (16 * k + e)) := by
  rw [VG.Proof.Rc4.AArch64.vbyte_read _ _ he, h.x0, ptr_add]
  apply BitVec.eq_of_toNat_eq
  rw [hp.byte_eq h.frame (by omega_using [hk, he]), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (byte_lt _)]

theorem step {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 8)
    {s : State} (h : Inv s₀ k s) : WP isa (.block body16) s fun t =>
      Inv s₀ (k + 1) t ∧ ((t.gpr .x10).toNat ≠ 0 ↔ k + 1 ≠ 8) := by
  unfold body16
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_ldrq (a := s.gpr .x0) (by decide) (by simp) ?_ fun s1 h1 => ?_
  · rw [h.rd, h.wr, hp.rd, hp.wr, h.x0]
    exact in_rd (in_regions (List.mem_singleton_self _) (contains_off (by omega_using [hk]) (by decide)))
  rw [WP.block_append_iff]
  refine WP.mono (prepare_ok s1
    (by rw [h1.get .v18]; exact h.consts.c18)
    (by rw [h1.get .v19]; exact h.consts.c19)
    (by rw [h1.get .v20]; exact h.consts.c20)
    (by rw [h1.get .v21]; exact h.consts.c21)) ?_
  intro s2 ⟨v2, v3, m2, g2, rd2, wr2, sp2, hv2⟩
  have mem2 : s2.mem = s.mem := m2.trans h1.mem
  have gpr2 : s2.gpr = s.gpr := g2.trans h1.gpr
  have cs2 : Consts s2 := h.consts.of fun r r0 r1 r2 r3 _ _ _ _ => by
    rw [hv2 r r0 r1 r2 r3, h1.get r r0]
  have nl : ∀ e < 16,
      (vbyte (VPermOp.eval .zip1 .b16 (s2.v .v2) (s2.v .v3)) e).toNat = nib s₀ k (16 * 0 + e) ∧
      (vbyte (VPermOp.eval .zip2 .b16 (s2.v .v2) (s2.v .v3)) e).toNat = nib s₀ k (16 * 1 + e) := by
    intro e he
    rw [v2, v3, h1.v, (byte_zip_nibbles _ he).1, (byte_zip_nibbles _ he).2,
      read_input hp hk h (by omega_using [he]), read_input hp hk h (by omega_using [he])]
    simp only [nib, show 16 * 0 + e = e by omega_using [], show (16 * 1 + e) / 2 = 8 + e / 2 by omega_using [],
      show (16 * 1 + e) % 2 = e % 2 by omega_using [], and_self]
  have hw : s2.wr = [fR s₀] := by rw [wr2, h1.wr, h.wr, hp.wr]
  refine half_ok (c := 0) hk (by decide) rfl hw (by rw [gpr2, h.x1]) cs2 (fun e he => (nl e he).1)
    (by rw [mem2]; exact h.out) (by rw [mem2]; exact h.frame)
    fun s3 g3 rd3 wr3 sp3 hv3 o3 f3 => ?_
  refine half_ok (c := 1) hk (by decide) rfl (by rw [wr3]; exact hw) (by rw [g3, gpr2, h.x1])
    (cs2.of fun r _ _ _ _ r4 r5 r6 r7 => hv3 r r4 r5 r6 r7)
    (fun e he => by
      rw [hv3 .v2 (by decide) (by decide) (by decide) (by decide),
        hv3 .v3 (by decide) (by decide) (by decide) (by decide)]
      exact (nl e he).2)
    o3 f3 fun s4 g4 rd4 wr4 sp4 hv4 o4 f4 => ?_
  have gp4 : s4.gpr = s.gpr := (g4.trans g3).trans gpr2
  have scalar : WP isa (.block [.addImm .x .x0 .x0 16, .addImm .x .x1 .x1 64,
      .subImm .x .x10 .x10 1]) s4 fun t =>
      Only [.x0, .x1, .x10] s4 t ∧
      t.gpr .x0 = s4.gpr .x0 + 16 ∧ t.gpr .x1 = s4.gpr .x1 + 64 ∧
      (t.gpr .x10).toNat = 8 - (k + 1) := by
    refine wp_addImm (by decide) fun s5 h5 e5 => wp_addImm (by decide) fun s6 h6 e6 =>
      wp_subImm (by decide) fun s7 h7 e7 => wp_nil ?_
    refine ⟨((h5.trans h6).trans h7).mono (by decide), ?_, ?_, ?_⟩
    · rw [h7.get .x0, h6.get .x0, e5]; rfl
    · rw [h7.get .x1, e6, h5.get .x1]; rfl
    · rw [e7, toNat_sub_n (by rw [h6.get .x10, h5.get .x10, gp4, h.count]; simp; omega_using [hk]),
        h6.get .x10, h5.get .x10, gp4, h.count]
      simp; omega_using []
  refine WP.mono (WP.keepV (by decide) scalar) ?_
  intro s7 ⟨⟨kept, xx0, xx1, cnt⟩, vv⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, cnt, ?_, ?_, ?_⟩, by rw [cnt]; omega_using [hk]⟩
  · rw [kept.rd, rd4, rd3, rd2, h1.rd, h.rd]
  · rw [kept.wr, wr4, wr3, wr2, h1.wr, h.wr]
  · rw [kept.sp, sp4, sp3, sp2, h1.sp, h.sp]
  · rw [xx0, gp4, h.x0, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ptr_add]
    congr 2
  · rw [xx1, gp4, h.x1, show (64 : BitVec 64) = BitVec.ofNat 64 64 from rfl, ptr_add]
    congr 2
  · exact cs2.of fun r _ _ _ _ r4 r5 r6 r7 => by rw [vv, hv4 r r4 r5 r6 r7, hv3 r r4 r5 r6 r7]
  · rw [kept.mem, show 64 * (k + 1) = 64 * k + 32 * 1 + 32 by omega_using []]; exact o4
  · rw [kept.mem]; exact f4

theorem init (s : State) : WP isa (.block (tables ++ constant .v18 .b16 0x55 ++
    constant .v19 .b16 0x33 ++ constant .v20 .b16 0x22 ++ constant .v21 .b16 15 ++
    ([.movz .x .x10 8 0] : List Instr))) s (Inv s 0) := by
  unfold tables constant
  rrun [List.append_assoc, List.cons_append, List.nil_append, RegUpd.sp_write, RegUpd.sp_setV]
  refine ⟨rfl, rfl, rfl, ?_, ?_, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_, ?_⟩
  · change s.gpr .x0 = Cbd2.bP s + BitVec.ofNat 64 (16 * 0)
    simp [Cbd2.bP]
  · change s.gpr .x1 = Cbd2.fP s + BitVec.ofNat 64 (64 * 0)
    simp [Cbd2.fP]
  · exact BytesUpTo.zero _
  · exact Frame.refl _ _

theorem loop_ok {s₀ : State} (hp : Pre s₀) : WP isa code16 s₀ (Inv s₀ 8) := by
  apply WP.seq
  refine WP.mono (init s₀) ?_
  intro s hs
  exact count_loop (by decide) (Inv s₀) (fun k hk t ht => step hp hk ht) hs

end VG.Proof.MlKem.AArch64.Cbd16W
