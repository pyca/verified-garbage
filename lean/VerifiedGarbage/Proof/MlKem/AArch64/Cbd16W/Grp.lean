module

public import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Input
public import VerifiedGarbage.Spec.MlKem.Kpke16

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
  rw [vbyte_ofVBytes _ he, hx e he, ite_eq_left (by have := hf e he; omega)]

/-- The interleaved bytes of the coefficient of nibble `F (b / 2)`. -/
theorem vbyte_zip_tbl {lo hi : BitVec 128} {F : Nat → Nat} (hf : ∀ e < 16, F e ≤ 4)
    (hl : ∀ e < 16, vbyte lo e = vbyte loV (F e)) (hh : ∀ e < 16, vbyte hi e = vbyte hiV (F e))
    {b : Nat} (hb : b < 16) :
    (vbyte (VPermOp.eval .zip1 .b16 lo hi) b).toNat = (F (b / 2) + 3327) % 3329 / 256 ^ (b % 2) % 256 ∧
      (vbyte (VPermOp.eval .zip2 .b16 lo hi) b).toNat =
        (F (8 + b / 2) + 3327) % 3329 / 256 ^ (b % 2) % 256 := by
  rw [VG.Proof.Blowfish.AArch64.vbyte_zip1 _ _ hb, VG.Proof.Blowfish.AArch64.vbyte_zip2 _ _ hb]
  have t1 := tables_val (F (b / 2)) (by have := hf (b / 2) (by omega); omega)
  have t2 := tables_val (F (8 + b / 2)) (by have := hf (8 + b / 2) (by omega); omega)
  rcases Nat.mod_two_eq_zero_or_one b with h | h
  · rw [ite_eq_left h, ite_eq_left h, hl _ (by omega), hl _ (by omega), t1.1, t2.1, h,
      Nat.pow_zero, Nat.div_one, Nat.div_one]
    exact ⟨rfl, rfl⟩
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), hh _ (by omega), hh _ (by omega), t1.2,
      t2.2, h, Nat.pow_one]
    have e : ∀ f, (f + 3327) % 3329 / 256 % 256 = (f + 3327) % 3329 / 256 := fun f =>
      Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by have := Nat.mod_lt (f + 3327) (show 3329 > 0 by decide); omega))
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
  refine wp_strq (a := a) ⟨ho.1, by omega⟩ (by rw [h4.gpr, h3.gpr, h2.gpr, h1.gpr]; exact ha)
    (by rw [h4.wr, h3.wr, h2.wr, h1.wr]; exact hin) fun s5 h5 => ?_
  refine wp_strq (a := a + BitVec.ofNat 64 16) ⟨by omega, ho.2⟩
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
