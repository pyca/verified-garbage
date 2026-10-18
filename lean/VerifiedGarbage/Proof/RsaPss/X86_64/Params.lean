module

public import VerifiedGarbage.Impl.RsaPss.X86_64
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Sel
import VerifiedGarbage.Proof.RsaPss.Params
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS on x86-64: the encoding's parameters

The code runs in RSAES-OAEP's frame and working space, so its proofs use
RSAES-OAEP's (`Lay`, `Rep`, …, `Proof/RsaOaep/X86_64/`). From the modulus'
first byte `n₀ ≠ 0` in `rax`, `smear` leaves `2^⌊log₂ n₀⌋ - 1` in `rdx`,
and ZF set iff `n₀ = 1` (`smear_ok`); `emLen` stores the mask `0xFF >>> z`
and `lo = k - emLen` to their slots and leaves `emLen` in `rax`, CF set iff
`emLen < hLen + 2` (`emLen_ok`, `hLen` in its slot); `saltFits` and
`dbSlots` compute the longest salt, `dbLen` and `DB`'s address.

The frame's words PSS uses: `sScr` (14), the arguments (`sOut`/`sSig` 21,
`sN` 22, `sK` 23, `sE` 24, `sEl` 25, `sScrLen` 26, `sDig` 27, `sSalt`/`sAny`
28, `sSaltLen`/`sSlen` 29), the mask (30), `lo` (31), `pos` (32, `sIdx`),
`DB`'s address (33), the shift's bits (34, `sA`), `dbLen` (44), and,
verifying, the accumulator (4) and the salt's length (5), and the selectors' (37 to 43, 45
to 50).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.Mgf1.X86_64 (sp ix at_ step byteLoop seqs)
open VG.Impl.RsaOaep.X86_64 (frameBytes sScr sN sK sHD oEm)
open VG.Proof.RsaOaep.X86_64 (Lay Rep upd slot_eq ea_sp ofNat_add_lit off_plus nW)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum (off)

/-- `n₀`, the first byte of `n` (whose address is in `sN`, word 22), into
`rax`, and ZF set iff it is zero. -/
theorem n0_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {p : Addr} (hn : W 22 = p) (hin : InRegions (u.rd ++ u.wr) p 1) :
    WP isa (.block n0) u fun u' => Keep [.rsi, .rax] u u' ∧ u'.mem = u.mem ∧
      u'.gpr .rax = BitVec.ofNat 64 (u.mem p).toNat ∧ u'.zf = some (decide ((u.mem p).toNat = 0)) := by
  refine WP.mono (WP.keep [.rsi, .rax] (Q := fun u' => u'.mem = u.mem ∧
    u'.gpr .rax = BitVec.ofNat 64 (u.mem p).toNat ∧ u'.zf = some (decide ((u.mem p).toNat = 0))) ?_ rfl)
    fun u' ⟨h, k⟩ => ⟨k, h⟩
  xrun [n0, ea_sp, L.rsp, L.ld (d := sN) (by decide), R.rd (d := sN) 22 rfl (by decide), hn,
    VG.Proof.RsaOaep.X86_64.ea_at0, hin]
  have he : BitVec.setWidth 64 (u.mem p) = BitVec.ofNat 64 (u.mem p).toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  refine ⟨he, ?_⟩
  rw [BitVec.and_self, he, VG.Proof.RsaOaep.X86_64.ofNat_beq_zero (by have := (u.mem p).isLt; omega)]

/-- What `smear` computes from `y`. -/
abbrev smearV (y : BitVec 64) : BitVec 64 :=
  y >>> 1 ||| y >>> 1 >>> 1 ||| (y >>> 1 ||| y >>> 1 >>> 1) >>> 2 |||
    (y >>> 1 ||| y >>> 1 >>> 1 ||| (y >>> 1 ||| y >>> 1 >>> 1) >>> 2) >>> 4

theorem smear_table : ∀ x < 256, x ≠ 0 → x ≠ 1 →
    ∃ j < 8, 2 ^ j ≤ x ∧ x < 2 ^ (j + 1) ∧ smearV (BitVec.ofNat 64 x) = BitVec.ofNat 64 (2 ^ j - 1) := by
  decide +kernel

theorem smear_val {x : Nat} (hx : x < 256) (h0 : x ≠ 0) :
    smearV (BitVec.ofNat 64 x) = if x = 1 then 0 else BitVec.ofNat 64 (2 ^ Nat.log2 x - 1) := by
  by_cases h1 : x = 1
  · subst h1; decide
  · obtain ⟨j, _, hl, hu, he⟩ := smear_table x hx h0 h1
    rw [ifn h1, he, RsaPss.log2_eq h0 hl hu]

theorem smear_ok (u : State) {x : Nat} (hx : x < 256) (h0 : x ≠ 0) (hax : u.gpr .rax = BitVec.ofNat 64 x) :
    WP isa (.block smear) u fun u' => Keep [.rax, .rdx] u u' ∧ u'.mem = u.mem ∧
      u'.gpr .rdx = (if x = 1 then 0 else BitVec.ofNat 64 (2 ^ Nat.log2 x - 1)) ∧
      u'.zf = some (decide (x = 1)) := by
  refine WP.keep [.rax, .rdx] (Q := fun u' => u'.mem = u.mem ∧
      u'.gpr .rdx = (if x = 1 then 0 else BitVec.ofNat 64 (2 ^ Nat.log2 x - 1)) ∧
      u'.zf = some (decide (x = 1))) ?_ rfl |> WP.mono <| fun u' ⟨h, k⟩ => ⟨k, h⟩
  xrun [smear, hax]
  have hs := smear_val hx h0
  unfold smearV at hs
  rw [hs]
  refine ⟨rfl, ?_⟩
  by_cases h1 : x = 1
  · subst h1; decide
  · have h2 : 2 ^ Nat.log2 x - 1 < 2 ^ 64 := by
      have := Nat.lt_pow_self (n := Nat.log2 x) (show 1 < 2 by decide)
      have : Nat.log2 x < 8 := (Nat.log2_lt h0).mpr hx
      have : 2 ^ Nat.log2 x ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have h3 : 2 ^ Nat.log2 x - 1 ≠ 0 := by
      have := (Nat.le_log2 h0).mpr (show 2 ^ 1 ≤ x by omega)
      have : 2 ^ 1 ≤ 2 ^ Nat.log2 x := Nat.pow_le_pow_right (by decide) this
      omega
    rw [ifn h1, BitVec.and_self]
    simp only [h1, decide_false]
    rw [beq_eq_false_iff_ne]
    intro h
    exact h3 (by have := congrArg BitVec.toNat h; simpa [Nat.mod_eq_of_lt h2] using this)

/-- `lo = k - emLen`: 1 if `n₀ = 1`. -/
def loV (x : Nat) : Nat := if x = 1 then 1 else 0

/-- The mask `0xFF >>> z`, as a word. -/
def maskV (x : Nat) : BitVec 64 := if x = 1 then BitVec.ofNat 64 0xFF else BitVec.ofNat 64 (2 ^ Nat.log2 x - 1)

theorem loV_le (x : Nat) : loV x ≤ 1 := by unfold loV; split <;> omega

/-- `emLen`: the mask (word 30), `lo` (31), and `emLen` compared with
`hLen + 2`, `hLen` in its slot (39). -/
theorem emLen_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {x k D : Nat} (hk : W 23 = BitVec.ofNat 64 k) (hD : W 39 = BitVec.ofNat 64 D)
    (hD64 : D ≤ 64) (hk1 : 1 ≤ k) (hk2 : k < 2 ^ 32)
    (hdx : u.gpr .rdx = (if x = 1 then 0 else BitVec.ofNat 64 (2 ^ Nat.log2 x - 1)))
    (hz : u.zf = some (decide (x = 1))) :
    WP isa emLen u fun u' => Lay u' F S ∧ Keep [.rdx, .r8, .rax, .r9] u u' ∧
      Rep u'.mem F S V (upd (upd W 30 (maskV x)) 31 (BitVec.ofNat 64 (loV x))) ∧
      u'.gpr .rax = BitVec.ofNat 64 (k - loV x) ∧ u'.cf = some (decide (k - loV x < D + 2)) := by
  have G := L.geo
  have hl := loV_le x
  refine WP.seq (WP.mono (Q := fun (v : State) => Keep [.rdx, .r8] u v ∧ v.mem = u.mem ∧ v.gpr .rdx = maskV x ∧
      v.gpr .r8 = BitVec.ofNat 64 (loV x)) ?_ fun v ⟨kv, hmv, hdv, h8v⟩ => ?_)
  · refine WP.ite (M := isa) _ (show isa.eval .e u = _ from hz) (fun hb => ?_) (fun hb => ?_)
    · rw [decide_eq_true_eq] at hb
      refine WP.mono (WP.keep [.rdx, .r8] (Q := fun v => v.mem = u.mem ∧ v.gpr .rdx = maskV x ∧
        v.gpr .r8 = BitVec.ofNat 64 (loV x)) ?_ rfl) fun v ⟨h, k'⟩ => ⟨k', h⟩
      xrun [maskV, loV, hb]
    · rw [decide_eq_false_iff_not] at hb
      refine WP.mono (WP.keep [.r8] (Q := fun v => v.mem = u.mem ∧
        v.gpr .r8 = BitVec.ofNat 64 (loV x)) ?_ rfl) fun v ⟨⟨h, h'⟩, k'⟩ =>
          ⟨k'.mono (by decide), h, by rw [k'.gpr (by decide), hdx, ifn hb, maskV, ifn hb], h'⟩
      xrun [loV, hb]
  have Lv : Lay v F S := L.congr (kv.gpr (by decide)) kv.2.2 (by rw [hmv])
  have Rv : Rep v.mem F S V W := hmv ▸ R
  have R1 := Rv.wf G (k := 30) (by decide) (maskV x)
  have R2 := R1.wf G (k := 31) (by decide) (BitVec.ofNat 64 (loV x))
  rw [show off F (8 * 30) = off F sC from rfl] at R1 R2
  rw [show off F (8 * 31) = off F sLo from rfl] at R2
  have h23 : ((v.mem.writeW (off F sC) (maskV x)).writeW (off F sLo) (BitVec.ofNat 64 (loV x))).readW
      (off F sK) 64 = BitVec.ofNat 64 k := by
    have := R2.fr 23 (by decide); simp only [upd, Nat.reduceEqDiff, ite_false] at this; rw [← hk, ← this]; rfl
  have h39 : ((v.mem.writeW (off F sC) (maskV x)).writeW (off F sLo) (BitVec.ofNat 64 (loV x))).readW
      (off F sHD) 64 = BitVec.ofNat 64 D := by
    have := R2.fr 39 (by decide); simp only [upd, Nat.reduceEqDiff, ite_false] at this; rw [← hD, ← this]; rfl
  refine WP.mono (WP.keep [.rax, .r9] (Q := fun w => w.mem = (v.mem.writeW (off F sC) (maskV x)).writeW (off F sLo)
      (BitVec.ofNat 64 (loV x)) ∧ w.gpr .rax = BitVec.ofNat 64 (k - loV x) ∧
      w.cf = some (decide (k - loV x < D + 2))) ?_ rfl) fun w ⟨⟨hm, ha, hc⟩, kw⟩ => ?_
  · xrun [ea_sp, Lv.rsp, Lv.st (d := sC) (by decide), Lv.st (d := sLo) (by decide), Lv.ld (d := sK) (by decide),
      Lv.ld (d := sHD) (by decide), hdv, h8v, h23, h39, VG.Offset.ofNat_sub_ofNat (show loV x ≤ k by omega),
      ofNat_add_lit]
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  refine ⟨Lv.of_rep' Rv (hm ▸ R2) (by simp [upd]) (kw.gpr (by decide)) kw.2.2, (kv.trans kw).mono (by decide),
    hm ▸ R2, ha, hc⟩

/-- `saltFits`: `a - (hLen + 2)`, compared with `rdx`. -/
theorem saltFits_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {D a : Nat} (hD : W 39 = BitVec.ofNat 64 D) {b : BitVec 64}
    (ha : D + 2 ≤ a) (ha' : a < 2 ^ 32) (hax : u.gpr .rax = BitVec.ofNat 64 a) (hdx : u.gpr .rdx = b) :
    WP isa (.block saltFits) u fun u' => Keep [.rax] u u' ∧ u'.mem = u.mem ∧
      u'.gpr .rax = BitVec.ofNat 64 (a - (D + 2)) ∧ u'.cf = some (decide (a - (D + 2) < b.toNat)) := by
  have h39 : u.mem.readW (off F sHD) 64 = BitVec.ofNat 64 D := by
    rw [show sHD = 8 * 39 from rfl]; exact (R.fr 39 (by decide)).trans hD
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = u.mem ∧ u'.gpr .rax = BitVec.ofNat 64 (a - (D + 2)) ∧
    u'.cf = some (decide (a - (D + 2) < b.toNat))) ?_ rfl) fun u' ⟨h, k⟩ => ⟨k, h⟩
  have e2 : BitVec.ofNat 64 (a - D) - 2 = BitVec.ofNat 64 (a - (D + 2)) := by
    rw [show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl, VG.Offset.ofNat_sub_ofNat (by omega)]; congr 1
  xrun [saltFits, ea_sp, L.rsp, L.ld (d := sHD) (by decide), h39, hax, hdx,
    VG.Offset.ofNat_sub_ofNat (show D ≤ a by omega), e2]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- `dbSlots`: `dbLen` (word 44) and `DB`'s address (33). -/
theorem dbSlots_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {a lo : Nat} (hlo : W 31 = BitVec.ofNat 64 lo)
    (hax : u.gpr .rax = BitVec.ofNat 64 a) :
    WP isa (.block dbSlots) u fun u' => Lay u' F S ∧ Keep [.rax, .rdx] u u' ∧
      Rep u'.mem F S V (upd (upd W 44 (BitVec.ofNat 64 (a + 1))) 33 (off S (oEm + lo))) := by
  have G := L.geo
  have hs := L.slot
  simp only [Bignum.word] at hs
  have R1 := R.wf G (k := 44) (by decide) (BitVec.ofNat 64 (a + 1))
  have R2 := R1.wf G (k := 33) (by decide) (off S (oEm + lo))
  rw [show off F (8 * 44) = off F sDb from rfl] at R1 R2
  rw [show off F (8 * 33) = off F sEb from rfl] at R2
  have h14 : (u.mem.writeW (off F sDb) (BitVec.ofNat 64 (a + 1))).readW (off F sScr) 64 = S := by
    have := R1.fr 14 (by decide); simp only [upd, Nat.reduceEqDiff, ite_false] at this
    rw [show (S : Addr) = W 14 from ((R.fr 14 (by decide)).symm.trans hs).symm, ← this]; rfl
  have h31 : (u.mem.writeW (off F sDb) (BitVec.ofNat 64 (a + 1))).readW (off F sLo) 64 = BitVec.ofNat 64 lo := by
    have := R1.fr 31 (by decide); simp only [upd, Nat.reduceEqDiff, ite_false] at this; rw [← hlo, ← this]; rfl
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun u' => u'.mem = (u.mem.writeW (off F sDb)
      (BitVec.ofNat 64 (a + 1))).writeW (off F sEb) (off S (oEm + lo))) ?_ rfl) fun u' ⟨hm, k⟩ => ?_
  · xrun [dbSlots, Impl.RsaOaep.X86_64.scr, Impl.Mgf1.X86_64.scr, Impl.RsaOaep.X86_64.lay, List.cons_append,
      List.nil_append, ea_sp, L.rsp, L.st (d := sDb) (by decide), L.ld (d := sScr) (by decide),
      L.ld (d := sLo) (by decide), L.st (d := sEb) (by decide), hax, h14, h31, ofNat_add_lit,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oEm < 2 ^ 31 by decide), off_plus]
  exact ⟨L.of_rep' R (hm ▸ R2) (by simp [upd]) (k.gpr (by decide)) k.2.2, k, hm ▸ R2⟩

/-- The mask fits in a byte. -/
theorem maskV_byte {x : Nat} (hx : x < 256) : maskV x = BitVec.setWidth 64 ((maskV x).setWidth 8) := by
  have hv : (maskV x).toNat < 2 ^ 8 := by
    unfold maskV
    split
    · decide
    · have hl : Nat.log2 x < 8 := by
        by_cases h0 : x = 0
        · subst h0; decide
        · exact (Nat.log2_lt h0).mpr hx
      have : 2 ^ Nat.log2 x ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
      rw [BitVec.toNat_ofNat]
      have : 2 ^ Nat.log2 x - 1 < 2 ^ 64 := by omega
      rw [Nat.mod_eq_of_lt this]
      omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt (by omega)]

end VG.Proof.RsaPss.X86_64
