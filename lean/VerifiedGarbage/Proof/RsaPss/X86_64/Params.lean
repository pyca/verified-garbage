import VerifiedGarbage.Proof.RsaPss.X86_64.Basic
import VerifiedGarbage.Proof.RsaPss.Params

/-!
# RSASSA-PSS on x86-64: the encoding's parameters

From the modulus' first byte `n₀ ≠ 0` in `rax`, `smear` leaves
`2^⌊log₂ n₀⌋ - 1` in `rdx`, and ZF set iff `n₀ = 1` (`smear_ok`); `emLen`
stores the mask `0xFF >>> z` and `lo = k - emLen` to their slots and leaves
`emLen` in `rax`, CF set iff `emLen < hLen + 2` (`emLen_ok`).
-/

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum.X86_64 (off)

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

theorem emLen_ok {H : Impl.Pbkdf2.Md.X86_64.Hash} (hD : H.D + 2 < 2 ^ 31) {u : State} {F S : Addr}
    (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem F S V W) {x k : Nat}
    (hk : W 17 = BitVec.ofNat 64 k) (hk1 : 1 ≤ k) (hk2 : k < 2 ^ 32)
    (hdx : u.gpr .rdx = (if x = 1 then 0 else BitVec.ofNat 64 (2 ^ Nat.log2 x - 1)))
    (hz : u.zf = some (decide (x = 1))) :
    WP isa (emLen H) u fun u' => Lay u' F S ∧ Keep [.rdx, .r8, .rax] u u' ∧
      Rep u'.mem F S V (upd (upd W 25 (maskV x)) 26 (BitVec.ofNat 64 (loV x))) ∧
      u'.gpr .rax = BitVec.ofNat 64 (k - loV x) ∧ u'.cf = some (decide (k - loV x < H.D + 2)) := by
  have G := L.geo
  have hl : loV x ≤ 1 := by unfold loV; split <;> omega
  -- The mask and `lo`.
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
  have R1 := Rv.wf G (k := 25) (by decide) (maskV x)
  have R2 := R1.wf G (k := 26) (by decide) (BitVec.ofNat 64 (loV x))
  rw [show off F (8 * 25) = off F sC from rfl] at R1 R2
  rw [show off F (8 * 26) = off F sLo from rfl] at R2
  have h17 : ((v.mem.writeW (off F sC) (maskV x)).writeW (off F sLo) (BitVec.ofNat 64 (loV x))).readW
      (off F sK) 64 = BitVec.ofNat 64 k := by
    have := R2.fr 17 (by decide); simp only [upd, Nat.reduceEqDiff, ite_false] at this; rw [← hk, ← this]; rfl
  refine WP.mono (WP.keep [.rax] (Q := fun w => w.mem = (v.mem.writeW (off F sC) (maskV x)).writeW (off F sLo)
      (BitVec.ofNat 64 (loV x)) ∧ w.gpr .rax = BitVec.ofNat 64 (k - loV x) ∧
      w.cf = some (decide (k - loV x < H.D + 2))) ?_ rfl) fun w ⟨⟨hm, ha, hc⟩, kw⟩ => ?_
  · xrun [ea_sp, Lv.rsp, Lv.st (d := sC) (by decide), Lv.st (d := sLo) (by decide), Lv.ld (d := sK) (by decide),
      hdv, h8v, h17, VG.Offset.ofNat_sub_ofNat (show loV x ≤ k by omega), VG.Proof.MlKem.X86_64.sx_ofNat hD]
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  refine ⟨Lv.congr (kw.gpr (by decide)) kw.2.2 ?_, (kv.trans kw).mono (by decide), hm ▸ R2, ha, hc⟩
  have h1 := R2.fr 21 (by decide)
  rw [← hm] at h1
  rw [slot_eq sScr 21 rfl, slot_eq sScr 21 rfl, h1, Rv.fr 21 (by decide)]
  simp [upd]

theorem saltFits_ok {H : Impl.Pbkdf2.Md.X86_64.Hash} (hD : H.D + 2 < 2 ^ 31) (u : State) {a : Nat} {b : BitVec 64}
    (ha : H.D + 2 ≤ a) (ha' : a < 2 ^ 32) (hax : u.gpr .rax = BitVec.ofNat 64 a) (hdx : u.gpr .rdx = b) :
    WP isa (.block (saltFits H)) u fun u' => Keep [.rax] u u' ∧ u'.mem = u.mem ∧
      u'.gpr .rax = BitVec.ofNat 64 (a - (H.D + 2)) ∧ u'.cf = some (decide (a - (H.D + 2) < b.toNat)) := by
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = u.mem ∧ u'.gpr .rax = BitVec.ofNat 64 (a - (H.D + 2)) ∧
    u'.cf = some (decide (a - (H.D + 2) < b.toNat))) ?_ rfl) fun u' ⟨h, k⟩ => ⟨k, h⟩
  xrun [saltFits, hax, hdx, VG.Proof.MlKem.X86_64.sx_ofNat hD, VG.Offset.ofNat_sub_ofNat ha]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem dbSlots_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {a lo : Nat} (hlo : W 26 = BitVec.ofNat 64 lo)
    (hax : u.gpr .rax = BitVec.ofNat 64 a) :
    WP isa (.block dbSlots) u fun u' => Lay u' F S ∧ Keep [.rax, .rdx] u u' ∧
      Rep u'.mem F S V (upd (upd W 24 (BitVec.ofNat 64 (a + 1))) 23 (off S (oEm + lo))) := by
  have G := L.geo
  have hs := L.slot
  simp only [Bignum.X86_64.word] at hs
  have R1 := R.wf G (k := 24) (by decide) (BitVec.ofNat 64 (a + 1))
  have R2 := R1.wf G (k := 23) (by decide) (off S (oEm + lo))
  rw [show off F (8 * 24) = off F sDb from rfl] at R1 R2
  rw [show off F (8 * 23) = off F sEb from rfl] at R2
  have h21 : (u.mem.writeW (off F sDb) (BitVec.ofNat 64 (a + 1))).readW (off F sScr) 64 = S := by
    have := R1.fr 21 (by decide); simp only [upd, Nat.reduceEqDiff, ite_false] at this
    rw [show (S : Addr) = W 21 from ((R.fr 21 (by decide)).symm.trans hs).symm, ← this]; rfl
  have h26 : (u.mem.writeW (off F sDb) (BitVec.ofNat 64 (a + 1))).readW (off F sLo) 64 = BitVec.ofNat 64 lo := by
    have := R1.fr 26 (by decide); simp only [upd, Nat.reduceEqDiff, ite_false] at this; rw [← hlo, ← this]; rfl
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun u' => u'.mem = (u.mem.writeW (off F sDb)
      (BitVec.ofNat 64 (a + 1))).writeW (off F sEb) (off S (oEm + lo))) ?_ rfl) fun u' ⟨hm, k⟩ => ?_
  · xrun [dbSlots, scr, List.cons_append, List.nil_append, ea_sp, L.rsp, L.st (d := sDb) (by decide),
      L.ld (d := sScr) (by decide), L.ld (d := sLo) (by decide), L.st (d := sEb) (by decide), hax, h21, h26,
      ofNat_add_lit, VG.Proof.MlKem.X86_64.sx_ofNat (show oEm < 2 ^ 31 by decide), off_plus]
  refine ⟨L.congr (k.gpr (by decide)) k.2.2 ?_, k, hm ▸ R2⟩
  have h1 := R2.fr 21 (by decide)
  rw [← hm] at h1
  rw [slot_eq sScr 21 rfl, slot_eq sScr 21 rfl, h1, R.fr 21 (by decide)]
  simp [upd]

end VG.Proof.RsaPss.X86_64
