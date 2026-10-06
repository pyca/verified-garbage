import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyShift

/-!
# RSASSA-PSS verification on AArch64: the checks on `EM`

The accumulator `acc` of failed checks starts with `EM`'s last byte `⊕
0xbc`, its leading byte if `lo = 1`, and the top bits of `maskedDB`
(`acc0_ok`); `posCheck` adds the byte after the padding `⊕ 1` (or 1 if there
is none) and the salt's length `⊕` the expected one (`posCheck_ok`);
`cmpH` adds the digest `⊕ H` and returns 1 if `acc = 0` (`cmpH_ok`).
`copyDb` copies `DB` to `Y` (`copyDb_ok`), `verifyNb` sets `nbm`
(`verifyNb_ok`), and `expLen` the expected salt length (`expLen_ok`).
-/

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz wp_addImm wp_subImm wp_lsr wp_ldrb wp_and wp_eor
  wp_orr wp_sub wp_add eval_zero)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_mov wp_countdown wp_ldrSp setWidth_ofNat16)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)

/-- `acc0`: `EM`'s last byte `⊕ 0xbc`, its first byte if `lo = 1`, and the top
bits of `maskedDB`'s first byte, `c` the mask of `maskedDB`'s first byte. -/
theorem acc0_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} (R : Rep t.mem S V) {k lo : Nat}
    {c : BitVec 64} (hk : 1 ≤ k) (hk2 : k ≤ 1024) (hlo : lo ≤ 1) (h23 : t.gpr .x23 = BitVec.ofNat 64 k)
    (h24 : t.gpr .x24 = off S (oEm + lo)) (hLo : t.mem.readW (off F sLo) 64 = BitVec.ofNat 64 lo)
    (hC : t.mem.readW (off F sC) 64 = c) :
    WP isa (.block acc0) t fun t' => Only [.x10, .x9, .x26, .x11, .x12] t t' ∧
      t'.gpr .x26 = ((V (oEm + k - 1)).setWidth 64 ^^^ BitVec.ofNat 64 0xbc) |||
        ((V oEm).setWidth 64 &&& (0#64 - BitVec.ofNat 64 lo)) |||
        ((V (oEm + lo)).setWidth 64 &&& (c ^^^ BitVec.ofNat 64 0xFF)) := by
  have c1 : oEm = 2560 := rfl
  have c6 : oRsa = 8192 := rfl
  have hrs : ∀ {u : State}, u.sp = F → u.rd = t.rd → u.wr = t.wr → ∀ {d : Nat}, d + 8 ≤ frameBytes →
      InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 d) 8 := fun hsp hrd hwr _ hd => by
    rw [hsp, hrd, hwr]; exact L.fld hd
  unfold acc0 ld
  refine wp_addImm (by decide) fun u₁ o₁ e₁ => wp_add fun u₂ o₂ e₂ => wp_subImm (by decide) fun u₃ o₃ e₃ => ?_
  have a₃ : u₃.gpr .x9 = off S (oEm + k - 1) := by
    rw [e₃, e₂, o₁.get .x23, h23, e₁, L.x20, off_add, off_sub _ (by omega)]
  have h10 : u₃.gpr .x10 = off S oEm := by rw [o₃.get .x10, o₂.get .x10, e₁, L.x20]
  have O₃ : Only [.x10, .x9] t u₃ := (o₁.trans (o₂.trans o₃)).mono
  refine wp_ldrb (by decide) (by rw [a₃, BitVec.add_zero]) (by rw [O₃.rd, O₃.wr]; exact L.ld (by omega))
    fun u₄ o₄ e₄ => wp_movz fun u₅ o₅ e₅ => wp_eor fun u₆ o₆ e₆ => ?_
  refine wp_ldrb (by decide) (by rw [o₆.get .x10, o₅.get .x10, o₄.get .x10, h10, BitVec.add_zero])
    (by rw [o₆.rd, o₆.wr, o₅.rd, o₅.wr, o₄.rd, o₄.wr, O₃.rd, O₃.wr]; exact L.ld (by omega)) fun u₇ o₇ e₇ => ?_
  have O₇ : Only [.x10, .x9, .x26, .x11] t u₇ := (O₃.trans (o₄.trans (o₅.trans (o₆.trans o₇)))).mono
  refine wp_ldrSp (by decide) (hrs (by rw [O₇.sp, L.sp]) O₇.rd O₇.wr (by decide)) fun u₈ o₈ e₈ =>
    wp_movz fun u₉ o₉ e₉ => wp_sub fun u₁₀ o₁₀ e₁₀ => wp_and fun u₁₁ o₁₁ e₁₁ => wp_orr fun u₁₂ o₁₂ e₁₂ => ?_
  have O₁₂ : Only [.x10, .x9, .x26, .x11, .x12] t u₁₂ :=
    (O₇.trans (o₈.trans (o₉.trans (o₁₀.trans (o₁₁.trans o₁₂))))).mono
  refine wp_ldrb (by decide) (by rw [O₁₂.get .x24, h24, BitVec.add_zero])
    (by rw [O₁₂.rd, O₁₂.wr]; exact L.ld (by omega)) fun u₁₃ o₁₃ e₁₃ => ?_
  refine wp_ldrSp (by decide) (hrs (by rw [o₁₃.sp, O₁₂.sp, L.sp]) (by rw [o₁₃.rd, O₁₂.rd]) (by rw [o₁₃.wr, O₁₂.wr])
    (by decide)) fun u₁₄ o₁₄ e₁₄ => wp_movz fun u₁₅ o₁₅ e₁₅ => wp_eor fun u₁₆ o₁₆ e₁₆ =>
    wp_and fun u₁₇ o₁₇ e₁₇ => wp_orr fun u₁₈ o₁₈ e₁₈ => wp_nil
      ⟨(O₁₂.trans (o₁₃.trans (o₁₄.trans (o₁₅.trans (o₁₆.trans (o₁₇.trans o₁₈)))))).mono, ?_⟩
  have hm4 : t.mem (off S (oEm + k - 1)) = V (oEm + k - 1) := R _ (by omega)
  have hm10 : t.mem (off S oEm) = V oEm := R _ (by omega)
  have hm24 : t.mem (off S (oEm + lo)) = V (oEm + lo) := R _ (by omega)
  have cbc : (BitVec.ofNat 16 0xbc).setWidth 64 = BitVec.ofNat 64 0xbc := setWidth_ofNat16 (by decide)
  have cff : (BitVec.ofNat 16 0xFF).setWidth 64 = BitVec.ofNat 64 0xFF := setWidth_ofNat16 (by decide)
  have c00 : (BitVec.ofNat 16 0).setWidth 64 = 0#64 := setWidth_ofNat16 (by decide)
  have v6 : u₆.gpr .x26 = (V (oEm + k - 1)).setWidth 64 ^^^ BitVec.ofNat 64 0xbc := by
    rw [e₆, o₅.get .x26, e₄, e₅, O₃.mem, hm4, cbc]
  have v12 : u₁₂.gpr .x26 = u₆.gpr .x26 ||| ((V oEm).setWidth 64 &&& (0#64 - BitVec.ofNat 64 lo)) := by
    rw [e₁₂, o₁₁.get .x26, o₁₀.get .x26, o₉.get .x26, o₈.get .x26, o₇.get .x26, e₁₁, e₁₀, o₁₀.get .x11,
      o₉.get .x11, o₈.get .x11, e₇, e₉, o₉.get .x12, e₈, o₇.sp, o₆.sp, o₅.sp, o₄.sp, O₃.sp, L.sp, o₇.mem,
      o₆.mem, o₅.mem, o₄.mem, O₃.mem, hLo, hm10, c00]
  have m₁₂ : u₁₂.mem = t.mem := O₁₂.mem
  rw [e₁₈, e₁₇, e₁₆, e₁₅, o₁₅.get .x12, e₁₄, o₁₇.get .x26, o₁₆.get .x26, o₁₅.get .x26, o₁₄.get .x26,
    o₁₃.get .x26, v12, v6, o₁₆.get .x11, o₁₅.get .x11, o₁₄.get .x11, e₁₃, o₁₃.sp, O₁₂.sp, L.sp, o₁₃.mem, m₁₂, hC,
    hm24, cff]

/-- `posCheck`: the byte after the padding `⊕ 1` and the mask's top bit
(set if there is none) into `acc`, `pos` to its slot, and the salt's length
`⊕` the expected one, if one is expected. -/
theorem posCheck_ok {t : State} {F S : Addr} (L : Lay t F S) {acc m v any sv : BitVec 64} {pos db : Nat}
    (h13 : t.gpr .x13 = m) (h14 : t.gpr .x14 = BitVec.ofNat 64 pos) (h15 : t.gpr .x15 = v)
    (h26 : t.gpr .x26 = acc) (h25 : t.gpr .x25 = BitVec.ofNat 64 db) (hpos : pos < db)
    (hA : t.mem.readW (off F sAny) 64 = any) (hS : t.mem.readW (off F sSaltLen) 64 = sv) :
    WP isa posCheck t fun t' => Keep [.x9, .x15, .x13, .x26, .x16, .x11, .x12] t t' ∧
      t'.mem = t.mem.writeW (off F sPos) (BitVec.ofNat 64 pos) ∧
      t'.gpr .x26 = (acc ||| ((v ^^^ 1#64) ||| m >>> 63)) |||
        (if any = 0 then sv ^^^ BitVec.ofNat 64 (db - pos - 1) else 0) := by
  have hrs : ∀ {u : State}, u.sp = F → u.rd = t.rd → u.wr = t.wr → ∀ {d : Nat}, d + 8 ≤ frameBytes →
      InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 d) 8 := fun hsp hrd hwr _ hd => by
    rw [hsp, hrd, hwr]; exact L.fld hd
  have oz : ∀ x : BitVec 64, x ||| 0 = x := fun x => by ext i; simp
  unfold posCheck
  rw [List.append_assoc]
  refine WP.seq (WP.mono (Q := fun (u : State) => Keep [.x9, .x15, .x13, .x26, .x16, .x11] t u ∧
      u.mem = t.mem.writeW (off F sPos) (BitVec.ofNat 64 pos) ∧
      u.gpr .x26 = acc ||| ((v ^^^ 1#64) ||| m >>> 63) ∧ u.gpr .x11 = BitVec.ofNat 64 (db - pos - 1) ∧
      u.gpr .x9 = any) ?_ fun u ⟨K, hm, h26', h11, h9⟩ => ?_)
  · refine wp_movz fun u₁ o₁ e₁ => wp_eor fun u₂ o₂ e₂ => wp_lsr (by decide) fun u₃ o₃ e₃ =>
      wp_orr fun u₄ o₄ e₄ => wp_orr fun u₅ o₅ e₅ => ?_
    have O₅ : Only [.x9, .x15, .x13, .x26] t u₅ := (o₁.trans (o₂.trans (o₃.trans (o₄.trans o₅)))).mono
    refine st_slot (by rw [O₅.sp, L.sp]) (by decide) (by rw [O₅.wr]; exact L.fst (by decide))
      (fun u₆ k₆ m₆ x₆ => ?_) (by decide)
    refine wp_sub fun u₇ o₇ e₇ => wp_subImm (by decide) fun u₈ o₈ e₈ =>
      wp_ldrSp (by decide) (hrs (by rw [o₈.sp, o₇.sp, k₆.sp, O₅.sp, L.sp]) (by rw [o₈.rd, o₇.rd, k₆.rd, O₅.rd])
        (by rw [o₈.wr, o₇.wr, k₆.wr, O₅.wr]) (by decide)) fun u₉ o₉ e₉ => wp_nil
      ⟨(O₅.keep.trans (k₆.trans (o₇.keep.trans (o₈.keep.trans o₉.keep)))).mono, ?_, ?_, ?_, ?_⟩
    · rw [o₉.mem, o₈.mem, o₇.mem, m₆, O₅.get .x14, h14, O₅.mem]
    · have a15 : u₄.gpr .x15 = (v ^^^ 1#64) ||| m >>> 63 := by
        rw [e₄, e₃, o₃.get .x15, e₂, e₁, o₁.get .x15, h15, o₂.get .x13, o₁.get .x13, h13]; rfl
      rw [o₉.get .x26, o₈.get .x26, o₇.get .x26, k₆.get .x26, e₅, a15, o₄.get .x26, o₃.get .x26, o₂.get .x26,
        o₁.get .x26, h26]
    · rw [o₉.get .x11, e₈, e₇, k₆.get .x25, O₅.get .x25, h25, k₆.get .x14, O₅.get .x14, h14,
        Offset.ofNat_sub_ofNat (by omega), Offset.ofNat_sub_ofNat (by omega)]
    · rw [e₉, o₈.sp, o₇.sp, k₆.sp, O₅.sp, L.sp, o₈.mem, o₇.mem, m₆, O₅.mem,
        Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)]
      exact hA
  refine WP.ite _ (eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · rw [h9, beq_iff_eq] at hb
    refine wp_ldrSp (by decide) (hrs (by rw [K.sp, L.sp]) K.rd K.wr (by decide)) fun u₁ o₁ e₁ =>
      wp_eor fun u₂ o₂ e₂ => wp_orr fun u₃ o₃ e₃ => wp_nil
        ⟨(K.trans (o₁.keep.trans (o₂.keep.trans o₃.keep))).mono, by rw [o₃.mem, o₂.mem, o₁.mem, hm], ?_⟩
    rw [e₃, e₂, o₂.get .x26, o₁.get .x26, h26', o₁.get .x11, h11, e₁, K.sp, L.sp, hm,
      Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide), hS, ite_eq_left hb]
  · rw [h9, beq_eq_false_iff_ne] at hb
    exact wp_nil ⟨K.mono, hm, by rw [h26', ite_eq_right hb, oz]⟩

section
variable {H : Hash} (hH : HashOK H)

include hH in
/-- `DB` (`db` bytes at `scratch + e`) after `mHash` in `Y`. -/
theorem copyDb_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} (R : Rep t.mem S V) {e db : Nat}
    (hdb : 0 < db) (hfit : e + db ≤ oY) (h24 : t.gpr .x24 = off S e)
    (h25 : t.gpr .x25 = BitVec.ofNat 64 db) :
    WP isa (copyDb H) t fun t' => Keep [.x11, .x14, .x12, .x15] t t' ∧ Frame [⟨S, oRsa⟩] t.mem t'.mem ∧
      Rep t'.mem S (updL V (oY + 8 + H.D) ((List.range db).map fun i => V (e + i))) := by
  have hDN := hH.sizes.DN
  have hN := hH.N_le
  have c1 : oEm = 2560 := rfl
  have c2 : oY = 3584 := rfl
  have c6 : oRsa = 8192 := rfl
  unfold copyDb
  refine WP.seq (WP.mono (Q := fun (u : State) => Only [.x11, .x14, .x12] t u ∧ u.gpr .x11 = off S e ∧
      u.gpr .x14 = off S (oY + 8 + H.D) ∧ u.gpr .x12 = BitVec.ofNat 64 db) ?_ fun u ⟨O, h11, h14, h12⟩ => ?_)
  · exact wp_mov fun u₁ o₁ e₁ => wp_addImm (by omega) fun u₂ o₂ e₂ => wp_mov fun u₃ o₃ e₃ => wp_nil
      ⟨(o₁.trans (o₂.trans o₃)).mono, by rw [o₃.get .x11, o₂.get .x11, e₁, h24],
        by rw [o₃.get .x14, e₂, o₁.get .x20, L.x20], by rw [e₃, o₂.get .x25, o₁.get .x25, h25]⟩
  refine WP.mono (copyWithin_ok (L.congr O.sp O.wr (O.get .x20)) (O.mem ▸ R) hdb (by omega) (by omega)
    (by omega) h14 h11 h12) fun v ⟨k, f, r⟩ => ⟨(O.keep.trans k).mono, O.mem ▸ f, r⟩

include hH in
/-- `nbm = ⌊(dbLen + 7 + hLen + L) / B⌋ + 1` to its slot. -/
theorem verifyNb_ok {t : State} {F S : Addr} (L : Lay t F S) {db : Nat} (hdb : db ≤ 1024)
    (h25 : t.gpr .x25 = BitVec.ofNat 64 db) :
    WP isa (.block (verifyNb H)) t fun t' => Keep [.x9, .x16] t t' ∧
      t'.mem = t.mem.writeW (off F sNb) (BitVec.ofNat 64 ((db + 7 + H.D + H.P.L) / H.P.B + 1)) := by
  have hDN := hH.sizes.DN
  have hN := hH.N_le
  have hL := hH.L
  have hlg : 2 ^ lgB H = H.P.B ∧ lgB H < 64 := by
    unfold lgB
    rcases hH.sizes.B with h | h <;> rw [h]
    · rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.log2_two_pow]; decide
    · rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.log2_two_pow]; decide
  unfold verifyNb
  simp only [List.cons_append, List.nil_append]
  refine wp_addImm (by omega) fun u₁ o₁ e₁ => wp_lsr hlg.2 fun u₂ o₂ e₂ => wp_addImm (by decide) fun u₃ o₃ e₃ => ?_
  rw [← List.append_nil (st .x9 sNb)]
  have O₃ : Only [.x9] t u₃ := (o₁.trans (o₂.trans o₃)).mono
  refine st_slot (by rw [O₃.sp, L.sp]) (by decide) (by rw [O₃.wr]; exact L.fst (by decide))
    (fun u₄ k₄ m₄ _ => wp_nil ⟨(O₃.keep.trans k₄).mono, ?_⟩) (by decide)
  rw [m₄, O₃.mem, e₃, e₂, e₁, h25, BitVec.ofNat_add_ofNat, LenLoop.lsr_val (by omega), hlg.1,
    BitVec.ofNat_add_ofNat, show db + (7 + H.D + H.P.L) = db + 7 + H.D + H.P.L by omega]

/-- The OR of the first `j` values of `g`. -/
def orF (g : Nat → BitVec 64) : Nat → BitVec 64
  | 0 => 0
  | j + 1 => orF g j ||| g j

include hH in
/-- `acc` ORed with the digest `⊕ H` (at `DB + dbLen`), and `x0` the top bit
of `acc - 1`. -/
theorem cmpH_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} (R : Rep t.mem S V) {e db : Nat}
    {acc : BitVec 64} (hfit : e + db + H.D ≤ oY) (h21 : t.gpr .x21 = off S oDig) (h24 : t.gpr .x24 = off S e)
    (h25 : t.gpr .x25 = BitVec.ofNat 64 db) (h26 : t.gpr .x26 = acc) :
    WP isa (cmpH H) t fun t' => Only [.x11, .x10, .x12, .x9, .x15, .x26, .x0] t t' ∧
      t'.gpr .x0 = ((acc ||| orF (fun i => (V (oDig + i)).setWidth 64 ^^^ (V (e + db + i)).setWidth 64) H.D) -
        1#64) >>> 63 := by
  have hD := hH.sizes.D0
  have hDN := hH.sizes.DN
  have hN := hH.N_le
  have c2 : oY = 3584 := rfl
  have c3 : oDig = 2304 := rfl
  have c6 : oRsa = 8192 := rfl
  have oz : ∀ x : BitVec 64, x ||| 0 = x := fun x => by ext i; simp
  unfold cmpH
  refine WP.seq (WP.mono (Q := fun (u : State) => Only [.x11, .x10, .x12] t u ∧ u.gpr .x11 = off S oDig ∧
      u.gpr .x10 = off S (e + db) ∧ u.gpr .x12 = BitVec.ofNat 64 H.D) ?_ fun u ⟨O, h11, h10, h12⟩ => ?_)
  · exact wp_mov fun u₁ o₁ e₁ => wp_add fun u₂ o₂ e₂ => wp_movz fun u₃ o₃ e₃ => wp_nil
      ⟨(o₁.trans (o₂.trans o₃)).mono, by rw [o₃.get .x11, o₂.get .x11, e₁, h21],
        by rw [o₃.get .x10, e₂, o₁.get .x24, o₁.get .x25, h24, h25, off_add],
        by rw [e₃, setWidth_ofNat16 (by omega)]⟩
  have Lu : Lay u F S := L.congr O.sp O.wr (O.get .x20)
  have Ru : Rep u.mem S V := O.mem ▸ R
  refine WP.seq (WP.mono (wp_countdown (cnt := .x12) (N := H.D) (by omega) hD
    (fun j v => Only [.x9, .x15, .x26, .x11, .x10, .x12] u v ∧ v.gpr .x11 = off S (oDig + j) ∧
      v.gpr .x10 = off S (e + db + j) ∧
      v.gpr .x26 = acc ||| orF (fun i => (V (oDig + i)).setWidth 64 ^^^ (V (e + db + i)).setWidth 64) j)
    (fun j hj v ⟨hO, h11', h10', h26'⟩ _ => ?_)
    ⟨Only.refl _ _, by rw [Nat.add_zero, h11], by rw [Nat.add_zero, h10], by rw [O.get .x26, h26]; exact (oz _).symm⟩
    h12) fun v ⟨hO, _, _, h26'⟩ => ?_)
  · refine wp_ldrb (by decide) (by rw [h11', BitVec.add_zero]) (by rw [hO.rd, hO.wr]; exact Lu.ld (by omega))
      fun w₁ q₁ g₁ => ?_
    refine wp_ldrb (by decide) (by rw [q₁.get .x10, h10', BitVec.add_zero])
      (by rw [q₁.rd, q₁.wr, hO.rd, hO.wr]; exact Lu.ld (by omega)) fun w₂ q₂ g₂ => wp_eor fun w₃ q₃ g₃ =>
      wp_orr fun w₄ q₄ g₄ => wp_addImm (by decide) fun w₅ q₅ g₅ => wp_addImm (by decide) fun w₆ q₆ g₆ =>
      wp_subImm (by decide) fun w₇ q₇ g₇ => wp_nil ⟨⟨(hO.trans (q₁.trans (q₂.trans (q₃.trans (q₄.trans (q₅.trans
        (q₆.trans q₇))))))).mono, ?_, ?_, ?_⟩, ?_⟩
    · rw [q₇.get .x11, q₆.get .x11, g₅, q₄.get .x11, q₃.get .x11, q₂.get .x11, q₁.get .x11, h11', off_add,
        Nat.add_assoc]
    · rw [q₇.get .x10, g₆, q₅.get .x10, q₄.get .x10, q₃.get .x10, q₂.get .x10, q₁.get .x10, h10', off_add,
        Nat.add_assoc]
    · rw [q₇.get .x26, q₆.get .x26, q₅.get .x26, g₄, g₃, q₃.get .x26, q₂.get .x26, q₁.get .x26, h26', g₂,
        q₂.get .x9, g₁, q₁.mem, hO.mem, Ru _ (by omega), Ru _ (by omega), orF, BitVec.or_assoc]
    · rw [g₇, q₆.get .x12, q₅.get .x12, q₄.get .x12, q₃.get .x12, q₂.get .x12, q₁.get .x12]
  · exact wp_subImm (by decide) fun w₁ q₁ g₁ => wp_lsr (by decide) fun w₂ q₂ g₂ => wp_nil
      ⟨(O.trans (hO.trans (q₁.trans q₂))).mono, by rw [g₂, g₁, h26']⟩

theorem expLen_ok {t : State} {F S : Addr} (L : Lay t F S) {any sv : BitVec 64}
    (hA : t.mem.readW (off F sAny) 64 = any) (hS : t.mem.readW (off F sSaltLen) 64 = sv) :
    WP isa expLen t fun t' => Only [.x13, .x12] t t' ∧ t'.gpr .x12 = if any = 0 then sv else 0 := by
  unfold expLen ld
  refine WP.seq (wp_ldrSp (by decide) (by rw [L.sp]; exact L.fld (by decide)) fun u₁ o₁ e₁ => wp_nil ?_)
  rw [L.sp, hA] at e₁
  refine WP.ite _ (eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · rw [e₁, beq_iff_eq] at hb
    exact wp_ldrSp (by decide) (by rw [o₁.sp, o₁.rd, o₁.wr, L.sp]; exact L.fld (by decide)) fun u₂ o₂ e₂ => wp_nil
      ⟨(o₁.trans o₂).mono, by rw [e₂, o₁.sp, o₁.mem, L.sp, hS, ite_eq_left hb]⟩
  · rw [e₁, beq_eq_false_iff_ne] at hb
    exact wp_movz fun u₂ o₂ e₂ => wp_nil ⟨(o₁.trans o₂).mono, by rw [e₂, ite_eq_right hb]; rfl⟩

end

end VG.Proof.RsaPss.AArch64
