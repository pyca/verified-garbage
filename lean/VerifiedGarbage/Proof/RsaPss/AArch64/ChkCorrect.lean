module

public import VerifiedGarbage.Proof.RsaPss.AArch64.ChkFrame
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hash
public import VerifiedGarbage.Proof.Mgf1.Basic
public import VerifiedGarbage.Proof.RsaPss.AArch64.Mgf
public import VerifiedGarbage.Proof.RsaPss.VerifyCases
import VerifiedGarbage.Proof.RsaPss.AArch64.SignEncOk
import VerifiedGarbage.Proof.RsaPss.AArch64.SignEnc
import VerifiedGarbage.Proof.RsaPss.AArch64.CtHash
import VerifiedGarbage.Proof.RsaPss.AArch64.CtComp
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.RsaPss.CtPad
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.RsaPss.EncBytes
import VerifiedGarbage.Proof.RsaPss.MgfBytes
public import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyShift
public import VerifiedGarbage.Spec.RsaPss
public import VerifiedGarbage.Proof.RsaPss.AArch64.Basic
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Encode
import VerifiedGarbage.Proof.RsaPss.AArch64.SignChecks
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `RsaPss.AArch64.FixedSaltCopy`, which this module and modules that import it used -/

section

/-! Copy the public number of salt bytes from the end of the decoded DB. -/

@[expose] public section
namespace VG.Proof.RsaPss.AArch64.FixedSalt
open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.RsaPss.AArch64.FixedSalt
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.MlKem.AArch64 (Only Keep wp_add wp_sub wp_addImm wp_nil eval_zero)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_ldrSp)

theorem copySalt_ok {H : Hash} (hH : HashOK H) {t : State} {F S : Addr}
    (L : Lay t F S) {V : Nat → Byte} (R : Rep t.mem S V) {e db sl : Nat}
    (he : oEm ≤ e) (hfit : e + db ≤ oY) (hsl : sl ≤ db) (hdb : db < 1024)
    (h24 : t.gpr .x24 = off S e) (h25 : t.gpr .x25 = BitVec.ofNat 64 db)
    (hs : t.mem.readW (off F sSaltLen) 64 = BitVec.ofNat 64 sl) :
    WP isa (copySalt H) t fun t' => Keep [.x11, .x12, .x14, .x15] t t' ∧
      Frame [⟨S, oRsa⟩] t.mem t'.mem ∧
      Rep t'.mem S (updL V (oY + 8 + H.D)
        ((List.range sl).map fun i => V (e + db - sl + i))) := by
  have hDN := hH.sizes.DN
  have hN := hH.N_le
  unfold copySalt
  refine WP.seq (WP.mono (Q := fun (u : State) => Only [.x11, .x12, .x14] t u ∧
      u.gpr .x11 = off S (e + db - sl) ∧
      u.gpr .x14 = off S (oY + 8 + H.D) ∧ u.gpr .x12 = BitVec.ofNat 64 sl) ?_
    fun u ⟨O, h11, h14, h12⟩ => ?_)
  · refine wp_add fun u₁ o₁ e₁ => wp_ldrSp (by decide)
      (by rw [o₁.sp, o₁.rd, o₁.wr]; exact ld_slot L (by decide)) fun u₂ o₂ e₂ =>
      wp_sub fun u₃ o₃ e₃ => wp_addImm (by unfold oY; omega) fun u₄ o₄ e₄ => wp_nil ?_
    refine ⟨(o₁.trans (o₂.trans (o₃.trans o₄))).mono, ?_, ?_, ?_⟩
    · rw [o₄.get .x11, e₃, o₂.get .x11, e₁, h24, h25, off_add,
        e₂, o₁.sp, L.sp, o₁.mem, hs, off_sub _ (by omega)]
    · rw [e₄, o₃.get .x20, o₂.get .x20, o₁.get .x20, L.x20]
    · rw [o₄.get .x12, o₃.get .x12, e₂, o₁.sp, L.sp, o₁.mem, hs]
  refine WP.ite _ (eval_zero _ _) (fun h => ?_) (fun h => ?_)
  · rw [h12] at h
    have h0 : sl = 0 := by
      have : (BitVec.ofNat 64 sl).toNat = 0 := by rw [beq_iff_eq.mp h]; rfl
      rw [BitVec.toNat_ofNat] at this
      omega
    subst h0
    refine wp_nil ⟨O.keep.mono, O.mem ▸ Frame.refl _ _, ?_⟩
    simp only [List.range_zero, List.map_nil, updL_nil]
    exact O.mem ▸ R
  · rw [h12] at h
    have h0 : 0 < sl := by
      rcases Nat.eq_zero_or_pos sl with e | e
      · subst e; simp at h
      · exact e
    refine WP.mono (copyWithin_ok (L.congr O.sp O.wr (O.get .x20)) (O.mem ▸ R)
      h0 (by unfold oY oRsa at *; omega) (by unfold oY oRsa; omega)
      (Or.inl (by omega)) h14 h11 h12) fun v ⟨k, f, r⟩ =>
        ⟨(O.keep.trans k).mono, O.mem ▸ f, r⟩

end VG.Proof.RsaPss.AArch64.FixedSalt

end

end

/-! ### `RsaPss.AArch64.VerifyB1`, which this module and modules that import it used -/

section

/-! ### `RsaPss.AArch64.VerifyParts`, which this module and modules that import it used -/

section

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

@[expose] public section

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
    rw [e₃, e₂, o₁.get .x23, h23, e₁, L.x20, off_add, off_sub _ (by omega_arith)]
  have h10 : u₃.gpr .x10 = off S oEm := by rw [o₃.get .x10, o₂.get .x10, e₁, L.x20]
  have O₃ : Only [.x10, .x9] t u₃ := (o₁.trans (o₂.trans o₃)).mono
  refine wp_ldrb (by decide) (by rw [a₃, BitVec.add_zero]) (by rw [O₃.rd, O₃.wr]; exact L.ld (by omega_arith))
    fun u₄ o₄ e₄ => wp_movz fun u₅ o₅ e₅ => wp_eor fun u₆ o₆ e₆ => ?_
  refine wp_ldrb (by decide) (by rw [o₆.get .x10, o₅.get .x10, o₄.get .x10, h10, BitVec.add_zero])
    (by rw [o₆.rd, o₆.wr, o₅.rd, o₅.wr, o₄.rd, o₄.wr, O₃.rd, O₃.wr]; exact L.ld (by omega_arith)) fun u₇ o₇ e₇ => ?_
  have O₇ : Only [.x10, .x9, .x26, .x11] t u₇ := (O₃.trans (o₄.trans (o₅.trans (o₆.trans o₇)))).mono
  refine wp_ldrSp (by decide) (hrs (by rw [O₇.sp, L.sp]) O₇.rd O₇.wr (by decide)) fun u₈ o₈ e₈ =>
    wp_movz fun u₉ o₉ e₉ => wp_sub fun u₁₀ o₁₀ e₁₀ => wp_and fun u₁₁ o₁₁ e₁₁ => wp_orr fun u₁₂ o₁₂ e₁₂ => ?_
  have O₁₂ : Only [.x10, .x9, .x26, .x11, .x12] t u₁₂ :=
    (O₇.trans (o₈.trans (o₉.trans (o₁₀.trans (o₁₁.trans o₁₂))))).mono
  refine wp_ldrb (by decide) (by rw [O₁₂.get .x24, h24, BitVec.add_zero])
    (by rw [O₁₂.rd, O₁₂.wr]; exact L.ld (by omega_arith)) fun u₁₃ o₁₃ e₁₃ => ?_
  refine wp_ldrSp (by decide) (hrs (by rw [o₁₃.sp, O₁₂.sp, L.sp]) (by rw [o₁₃.rd, O₁₂.rd]) (by rw [o₁₃.wr, O₁₂.wr])
    (by decide)) fun u₁₄ o₁₄ e₁₄ => wp_movz fun u₁₅ o₁₅ e₁₅ => wp_eor fun u₁₆ o₁₆ e₁₆ =>
    wp_and fun u₁₇ o₁₇ e₁₇ => wp_orr fun u₁₈ o₁₈ e₁₈ => wp_nil
      ⟨(O₁₂.trans (o₁₃.trans (o₁₄.trans (o₁₅.trans (o₁₆.trans (o₁₇.trans o₁₈)))))).mono, ?_⟩
  have hm4 : t.mem (off S (oEm + k - 1)) = V (oEm + k - 1) := R _ (by omega_arith)
  have hm10 : t.mem (off S oEm) = V oEm := R _ (by omega_arith)
  have hm24 : t.mem (off S (oEm + lo)) = V (oEm + lo) := R _ (by omega_arith)
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

/-- `posCheck`'s block: `acc`, `pos` to its slot, `dbLen - pos - 1`, and
`any_salt_len`. -/
theorem posCheckBlk_ok {t : State} {F S : Addr} (L : Lay t F S) {acc m v any : BitVec 64} {pos db : Nat}
    (h13 : t.gpr .x13 = m) (h14 : t.gpr .x14 = BitVec.ofNat 64 pos) (h15 : t.gpr .x15 = v)
    (h26 : t.gpr .x26 = acc) (h25 : t.gpr .x25 = BitVec.ofNat 64 db) (hpos : pos < db)
    (hA : t.mem.readW (off F sAny) 64 = any) :
    WP isa (.block (([movi .x9 1, .logic .eor .x .x15 .x15 .x9, .lsr .x .x13 .x13 63, .logic .orr .x .x15 .x15 .x13,
      .logic .orr .x .x26 .x26 .x15] : List Instr) ++ st .x14 sPos ++
        ([.sub .x .x11 .x25 .x14, .subImm .x .x11 .x11 1, ld .x9 sAny] : List Instr)))
      t fun u => Keep [.x9, .x15, .x13, .x26, .x16, .x11] t u ∧
        u.mem = t.mem.writeW (off F sPos) (BitVec.ofNat 64 pos) ∧
        u.gpr .x26 = acc ||| ((v ^^^ 1#64) ||| m >>> 63) ∧ u.gpr .x11 = BitVec.ofNat 64 (db - pos - 1) ∧
        u.gpr .x9 = any := by
  have hrs : ∀ {u : State}, u.sp = F → u.rd = t.rd → u.wr = t.wr → ∀ {d : Nat}, d + 8 ≤ frameBytes →
      InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 d) 8 := fun hsp hrd hwr _ hd => by
    rw [hsp, hrd, hwr]; exact L.fld hd
  rw [List.append_assoc]
  refine wp_movz fun u₁ o₁ e₁ => wp_eor fun u₂ o₂ e₂ => wp_lsr (by decide) fun u₃ o₃ e₃ =>
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
      Offset.ofNat_sub_ofNat (by omega_arith), Offset.ofNat_sub_ofNat (by omega_arith)]
  · rw [e₉, o₈.sp, o₇.sp, k₆.sp, O₅.sp, L.sp, o₈.mem, o₇.mem, m₆, O₅.mem,
      Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)]
    exact hA

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
  refine WP.seq (WP.mono (posCheckBlk_ok L h13 h14 h15 h26 h25 hpos hA) fun u ⟨K, hm, h26', h11, h9⟩ => ?_)
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
  · exact wp_mov fun u₁ o₁ e₁ => wp_addImm (by omega_arith) fun u₂ o₂ e₂ => wp_mov fun u₃ o₃ e₃ => wp_nil
      ⟨(o₁.trans (o₂.trans o₃)).mono, by rw [o₃.get .x11, o₂.get .x11, e₁, h24],
        by rw [o₃.get .x14, e₂, o₁.get .x20, L.x20], by rw [e₃, o₂.get .x25, o₁.get .x25, h25]⟩
  refine WP.mono (copyWithin_ok (L.congr O.sp O.wr (O.get .x20)) (O.mem ▸ R) hdb (by omega_arith) (by omega_arith)
    (by omega_arith) h14 h11 h12) fun v ⟨k, f, r⟩ => ⟨(O.keep.trans k).mono, O.mem ▸ f, r⟩

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
  refine wp_addImm (by omega_arith) fun u₁ o₁ e₁ => wp_lsr hlg.2 fun u₂ o₂ e₂ => wp_addImm (by decide) fun u₃ o₃ e₃ => ?_
  rw [← List.append_nil (st .x9 sNb)]
  have O₃ : Only [.x9] t u₃ := (o₁.trans (o₂.trans o₃)).mono
  refine st_slot (by rw [O₃.sp, L.sp]) (by decide) (by rw [O₃.wr]; exact L.fst (by decide))
    (fun u₄ k₄ m₄ _ => wp_nil ⟨(O₃.keep.trans k₄).mono, ?_⟩) (by decide)
  rw [m₄, O₃.mem, e₃, e₂, e₁, h25, BitVec.ofNat_add_ofNat, LenLoop.lsr_val (by omega_arith), hlg.1,
    BitVec.ofNat_add_ofNat, show db + (7 + H.D + H.P.L) = db + 7 + H.D + H.P.L by omega_arith]

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
        by rw [e₃, setWidth_ofNat16 (by omega_arith)]⟩
  have Lu : Lay u F S := L.congr O.sp O.wr (O.get .x20)
  have Ru : Rep u.mem S V := O.mem ▸ R
  refine WP.seq (WP.mono (wp_countdown (cnt := .x12) (N := H.D) (by omega_arith) hD
    (fun j v => Only [.x9, .x15, .x26, .x11, .x10, .x12] u v ∧ v.gpr .x11 = off S (oDig + j) ∧
      v.gpr .x10 = off S (e + db + j) ∧
      v.gpr .x26 = acc ||| orF (fun i => (V (oDig + i)).setWidth 64 ^^^ (V (e + db + i)).setWidth 64) j)
    (fun j hj v ⟨hO, h11', h10', h26'⟩ _ => ?_)
    ⟨Only.refl _ _, by rw [Nat.add_zero, h11], by rw [Nat.add_zero, h10], by rw [O.get .x26, h26]; exact (oz _).symm⟩
    h12) fun v ⟨hO, _, _, h26'⟩ => ?_)
  · refine wp_ldrb (by decide) (by rw [h11', BitVec.add_zero]) (by rw [hO.rd, hO.wr]; exact Lu.ld (by omega_arith))
      fun w₁ q₁ g₁ => ?_
    refine wp_ldrb (by decide) (by rw [q₁.get .x10, h10', BitVec.add_zero])
      (by rw [q₁.rd, q₁.wr, hO.rd, hO.wr]; exact Lu.ld (by omega_arith)) fun w₂ q₂ g₂ => wp_eor fun w₃ q₃ g₃ =>
      wp_orr fun w₄ q₄ g₄ => wp_addImm (by decide) fun w₅ q₅ g₅ => wp_addImm (by decide) fun w₆ q₆ g₆ =>
      wp_subImm (by decide) fun w₇ q₇ g₇ => wp_nil ⟨⟨(hO.trans (q₁.trans (q₂.trans (q₃.trans (q₄.trans (q₅.trans
        (q₆.trans q₇))))))).mono, ?_, ?_, ?_⟩, ?_⟩
    · rw [q₇.get .x11, q₆.get .x11, g₅, q₄.get .x11, q₃.get .x11, q₂.get .x11, q₁.get .x11, h11', off_add,
        Nat.add_assoc]
    · rw [q₇.get .x10, g₆, q₅.get .x10, q₄.get .x10, q₃.get .x10, q₂.get .x10, q₁.get .x10, h10', off_add,
        Nat.add_assoc]
    · rw [q₇.get .x26, q₆.get .x26, q₅.get .x26, g₄, g₃, q₃.get .x26, q₂.get .x26, q₁.get .x26, h26', g₂,
        q₂.get .x9, g₁, q₁.mem, hO.mem, Ru _ (by omega_arith), Ru _ (by omega_arith), orF, BitVec.or_assoc]
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

end

end

/-! ### `RsaPss.AArch64.VerifyScan`, which only this module used -/

section

/-!
# RSASSA-PSS verification on AArch64: the first nonzero byte of `DB`

`posScan` visits every byte of `DB` and keeps, under masks, the index and
the value of the first nonzero one, and a mask of all ones while there is
none (`posScan_ok`), which is the number of leading zero octets `lz`
(`lz_of_nz`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz wp_addImm wp_subImm wp_lsr wp_ldrb wp_and wp_orr
  wp_sub)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_mov wp_countdown)
open VG.Proof.RsaPss (lz)

/-- The first index below `j` at which `f` is not zero. -/
def nz (f : Nat → Byte) : Nat → Option Nat
  | 0 => none
  | j + 1 => match nz f j with
    | some i => some i
    | none => if f j = 0 then none else some j

theorem nz_none {f : Nat → Byte} : ∀ {j : Nat}, nz f j = none → ∀ i < j, f i = 0
  | 0, _, _, hi => absurd hi (by omega_using [])
  | j + 1, h, i, hi => by
    simp only [nz] at h
    split at h
    · cases h
    · rename_i h'
      by_cases e : f j = 0
      · rcases (by omega_using [hi] : i < j ∨ i = j) with hl | rfl
        · exact nz_none h' i hl
        · exact e
      · rw [ite_eq_right e] at h; cases h

theorem nz_some {f : Nat → Byte} : ∀ {j i : Nat}, nz f j = some i → i < j ∧ f i ≠ 0 ∧ ∀ k < i, f k = 0
  | 0, _, h => by cases h
  | j + 1, i, h => by
    simp only [nz] at h
    split at h
    · rename_i i' h'
      cases h
      obtain ⟨a, b, c⟩ := nz_some h'
      exact ⟨by omega_using [a], b, c⟩
    · rename_i h'
      by_cases e : f j = 0
      · rw [ite_eq_left e] at h; cases h
      · rw [ite_eq_right e] at h
        cases h
        exact ⟨by omega_using [], e, nz_none h'⟩

/-- The value of the first nonzero byte, or 0. -/
def nzV (f : Nat → Byte) (j : Nat) : Byte :=
  match nz f j with
  | some i => f i
  | none => 0

theorem zero_bit (b : Byte) : (BitVec.setWidth 64 b - BitVec.ofNat 64 1) >>> 63 = if b = 0 then 1#64 else 0#64 := by
  by_cases h : b = 0
  · subst h; rw [ite_eq_left rfl]; decide
  · rw [ite_eq_right h]
    obtain h' : b.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow]
    have := b.isLt
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := b.toNat) (by omega_using [])]
    exact Nat.div_eq_of_lt (by omega_using [h'])

theorem posScan_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} (R : Rep t.mem S V) {e db : Nat}
    (he : e + db ≤ oRsa) (hdb : 0 < db) (h24 : t.gpr .x24 = off S e) (h25 : t.gpr .x25 = BitVec.ofNat 64 db) :
    WP isa posScan t fun t' => Only [.x10, .x11, .x12, .x13, .x14, .x15, .x9, .x8, .x16, .x17] t t' ∧
      t'.gpr .x13 = (if nz (fun i => V (e + i)) db = none then BitVec.allOnes 64 else 0) ∧
      t'.gpr .x14 = BitVec.ofNat 64 ((nz (fun i => V (e + i)) db).getD 0) ∧
      t'.gpr .x15 = (nzV (fun i => V (e + i)) db).setWidth 64 := by
  have c6 : oRsa = 8192 := rfl
  unfold posScan
  refine WP.seq (WP.mono (Q := fun (u : State) => Only [.x10, .x11, .x12, .x13, .x14, .x15] t u ∧
      u.gpr .x10 = off S e ∧ u.gpr .x11 = 0#64 ∧ u.gpr .x12 = BitVec.ofNat 64 db ∧ u.gpr .x13 = BitVec.allOnes 64 ∧
      u.gpr .x14 = 0#64 ∧ u.gpr .x15 = 0#64) ?_ fun u ⟨O, h10, h11, h12, h13, h14, h15⟩ => ?_)
  · refine wp_mov fun u₁ o₁ e₁ => wp_movz fun u₂ o₂ e₂ => wp_mov fun u₃ o₃ e₃ => wp_movz fun u₄ o₄ e₄ =>
      wp_subImm (by decide) fun u₅ o₅ e₅ => wp_movz fun u₆ o₆ e₆ => wp_movz fun u₇ o₇ e₇ => wp_nil
        ⟨(o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans o₇)))))).mono, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [o₇.get .x10, o₆.get .x10, o₅.get .x10, o₄.get .x10, o₃.get .x10, o₂.get .x10, e₁, h24]
    · rw [o₇.get .x11, o₆.get .x11, o₅.get .x11, o₄.get .x11, o₃.get .x11, e₂]; rfl
    · rw [o₇.get .x12, o₆.get .x12, o₅.get .x12, o₄.get .x12, e₃, o₂.get .x25, o₁.get .x25, h25]
    · rw [o₇.get .x13, o₆.get .x13, e₅, e₄]; rfl
    · rw [o₇.get .x14, e₆]; rfl
    · rw [e₇]; rfl
  obtain Ru : Rep u.mem S V := O.mem ▸ R
  obtain Lu : Lay u F S := L.congr O.sp O.wr (O.get .x20)
  refine WP.mono (wp_countdown (cnt := .x12) (N := db) (by omega_using [he, c6]) hdb
    (fun j v => Only [.x9, .x8, .x16, .x17, .x10, .x11, .x12, .x13, .x14, .x15] u v ∧
      v.gpr .x10 = off S (e + j) ∧ v.gpr .x11 = BitVec.ofNat 64 j ∧
      v.gpr .x13 = (if nz (fun i => V (e + i)) j = none then BitVec.allOnes 64 else 0) ∧
      v.gpr .x14 = BitVec.ofNat 64 ((nz (fun i => V (e + i)) j).getD 0) ∧
      v.gpr .x15 = (nzV (fun i => V (e + i)) j).setWidth 64)
    (fun j hj v ⟨hO, h10', h11', h13', h14', h15'⟩ _ => ?_)
    ⟨Only.refl _ _, by rw [Nat.add_zero, h10], h11, by rw [h13]; rfl, by rw [h14]; rfl, by rw [h15]; rfl⟩ h12)
    fun v ⟨hO, _, _, h13', h14', h15'⟩ => ⟨(O.trans hO).mono, h13', h14', h15'⟩
  refine wp_ldrb (by decide) (by rw [h10', BitVec.add_zero]) (by rw [hO.rd, hO.wr]; exact Lu.ld (by omega_using [he, hj]))
    fun w₁ q₁ g₁ => ?_
  refine wp_subImm (by decide) fun w₂ q₂ g₂ => wp_lsr (by decide) fun w₃ q₃ g₃ => wp_subImm (by decide) fun w₄ q₄ g₄ =>
    wp_and fun w₅ q₅ g₅ => wp_and fun w₆ q₆ g₆ => wp_orr fun w₇ q₇ g₇ => wp_and fun w₈ q₈ g₈ =>
    wp_orr fun w₉ q₉ g₉ => wp_movz fun w₁₀ q₁₀ g₁₀ => wp_sub fun w₁₁ q₁₁ g₁₁ => wp_and fun w₁₂ q₁₂ g₁₂ =>
    wp_addImm (by decide) fun w₁₃ q₁₃ g₁₃ => wp_addImm (by decide) fun w₁₄ q₁₄ g₁₄ =>
    wp_subImm (by decide) fun w₁₅ q₁₅ g₁₅ => wp_nil ?_
  obtain Q : Only [.x9, .x8, .x16, .x17, .x14, .x15, .x13, .x10, .x11, .x12] v w₁₅ :=
    (q₁.trans (q₂.trans (q₃.trans (q₄.trans (q₅.trans (q₆.trans (q₇.trans (q₈.trans (q₉.trans (q₁₀.trans
      (q₁₁.trans (q₁₂.trans (q₁₃.trans (q₁₄.trans q₁₅)))))))))))))).mono
  generalize hb : V (e + j) = b
  obtain v9 : w₁.gpr .x9 = b.setWidth 64 := by rw [g₁, hO.mem, Ru _ (by omega_using [he, hj]), hb]
  obtain v8 : w₃.gpr .x8 = if b = 0 then 1#64 else 0#64 := by rw [g₃, g₂, v9, zero_bit]
  obtain v16 : w₅.gpr .x16 = (w₃.gpr .x8 - BitVec.ofNat 64 1) &&& v.gpr .x13 := by
    rw [g₅, g₄, q₄.get .x13, q₃.get .x13, q₂.get .x13, q₁.get .x13]
  obtain v14 : w₁₅.gpr .x14 = v.gpr .x14 ||| (BitVec.ofNat 64 j &&& w₅.gpr .x16) := by
    rw [q₁₅.get .x14, q₁₄.get .x14, q₁₃.get .x14, q₁₂.get .x14, q₁₁.get .x14, q₁₀.get .x14, q₉.get .x14,
      q₈.get .x14, g₇, g₆, q₆.get .x14, q₅.get .x14, q₄.get .x14, q₃.get .x14, q₂.get .x14, q₁.get .x14,
      q₅.get .x11, q₄.get .x11, q₃.get .x11, q₂.get .x11, q₁.get .x11, h11']
  obtain v15 : w₁₅.gpr .x15 = v.gpr .x15 ||| (b.setWidth 64 &&& w₅.gpr .x16) := by
    rw [q₁₅.get .x15, q₁₄.get .x15, q₁₃.get .x15, q₁₂.get .x15, q₁₁.get .x15, q₁₀.get .x15, g₉, g₈,
      q₈.get .x15, q₇.get .x15, q₆.get .x15, q₅.get .x15, q₄.get .x15, q₃.get .x15, q₂.get .x15, q₁.get .x15,
      q₇.get .x9, q₆.get .x9, q₅.get .x9, q₄.get .x9, q₃.get .x9, q₂.get .x9, v9, q₇.get .x16, q₆.get .x16]
  obtain v13 : w₁₅.gpr .x13 = v.gpr .x13 &&& (0#64 - w₃.gpr .x8) := by
    rw [q₁₅.get .x13, q₁₄.get .x13, q₁₃.get .x13, g₁₂, q₁₁.get .x13, q₁₀.get .x13, q₉.get .x13, q₈.get .x13,
      q₇.get .x13, q₆.get .x13, q₅.get .x13, q₄.get .x13, q₃.get .x13, q₂.get .x13, q₁.get .x13, g₁₁, g₁₀,
      q₁₀.get .x8, q₉.get .x8, q₈.get .x8, q₇.get .x8, q₆.get .x8, q₅.get .x8, q₄.get .x8]
    rfl
  obtain x10 : w₁₅.gpr .x10 = off S (e + (j + 1)) := by
    rw [q₁₅.get .x10, q₁₄.get .x10, g₁₃, q₁₂.get .x10, q₁₁.get .x10, q₁₀.get .x10, q₉.get .x10, q₈.get .x10,
      q₇.get .x10, q₆.get .x10, q₅.get .x10, q₄.get .x10, q₃.get .x10, q₂.get .x10, q₁.get .x10, h10', off_add,
      Nat.add_assoc]
  obtain x11 : w₁₅.gpr .x11 = BitVec.ofNat 64 (j + 1) := by
    rw [q₁₅.get .x11, g₁₄, q₁₃.get .x11, q₁₂.get .x11, q₁₁.get .x11, q₁₀.get .x11, q₉.get .x11, q₈.get .x11,
      q₇.get .x11, q₆.get .x11, q₅.get .x11, q₄.get .x11, q₃.get .x11, q₂.get .x11, q₁.get .x11, h11',
      BitVec.ofNat_add_ofNat]
  obtain x12 : w₁₅.gpr .x12 = v.gpr .x12 - BitVec.ofNat 64 1 := by
    rw [g₁₅, q₁₄.get .x12, q₁₃.get .x12, q₁₂.get .x12, q₁₁.get .x12, q₁₀.get .x12, q₉.get .x12, q₈.get .x12,
      q₇.get .x12, q₆.get .x12, q₅.get .x12, q₄.get .x12, q₃.get .x12, q₂.get .x12, q₁.get .x12]
  suffices key : w₁₅.gpr .x13 = (if nz (fun i => V (e + i)) (j + 1) = none then BitVec.allOnes 64 else 0) ∧
      w₁₅.gpr .x14 = BitVec.ofNat 64 ((nz (fun i => V (e + i)) (j + 1)).getD 0) ∧
      w₁₅.gpr .x15 = (nzV (fun i => V (e + i)) (j + 1)).setWidth 64 from
    ⟨⟨(hO.trans Q).mono, x10, x11, key.1, key.2.1, key.2.2⟩, x12⟩
  obtain hS : ∀ i, nz (fun i => V (e + i)) j = some i → nz (fun i => V (e + i)) (j + 1) = some i := fun i h => by
    simp only [nz, h]
  obtain hN0 : nz (fun i => V (e + i)) j = none → b = 0 → nz (fun i => V (e + i)) (j + 1) = none := fun h h0 => by
    simp only [nz, h, hb, h0, ite_true]
  obtain hN1 : nz (fun i => V (e + i)) j = none → b ≠ 0 → nz (fun i => V (e + i)) (j + 1) = some j := fun h h0 => by
    simp only [nz, h, hb, h0, ite_false]
  obtain az : ∀ x : BitVec 64, x &&& 0 = 0 := fun x => by ext i; simp
  obtain za : ∀ x : BitVec 64, 0 &&& x = 0 := fun x => by ext i; simp
  obtain oz : ∀ x : BitVec 64, x ||| 0 = x := fun x => by ext i; simp
  obtain zo : ∀ x : BitVec 64, 0 ||| x = x := fun x => by ext i; simp
  obtain aa : ∀ x : BitVec 64, x &&& BitVec.allOnes 64 = x := fun x => BitVec.and_allOnes
  have hb0 : (1#64 - BitVec.ofNat 64 1) = 0 := rfl
  have hb1 : (0#64 - BitVec.ofNat 64 1) = BitVec.allOnes 64 := rfl
  by_cases hN : nz (fun i => V (e + i)) j = none
  · rw [hN, ite_eq_left rfl] at h13'
    rw [hN] at h14'
    obtain h15'' : v.gpr .x15 = 0 := by rw [h15']; simp only [nzV, hN]; rfl
    by_cases b0 : b = 0
    · have e1 := hN0 hN b0
      rw [v8, ite_eq_left b0] at v16
      rw [v16, hb0, za] at v14 v15
      refine ⟨by rw [v13, h13', v8, ite_eq_left b0, e1, ite_eq_left rfl]; rfl, by rw [v14, h14', az, oz, e1],
        by rw [v15, h15'', az, oz]; simp only [nzV, e1]; rfl⟩
    · have e1 := hN1 hN b0
      rw [v8, ite_eq_right b0, hb1, h13', aa] at v16
      rw [v16] at v14 v15
      refine ⟨by rw [v13, h13', v8, ite_eq_right b0, e1]; rfl, by rw [v14, h14', aa]; simp [e1],
        by rw [v15, h15'', aa, zo]; simp only [nzV, e1, hb]⟩
  · obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hN
    obtain e1 := hS i hi
    rw [hi] at h13' h14'
    rw [h13', ite_eq_right (by simp), az] at v16
    rw [v16, az, oz] at v14 v15
    refine ⟨by rw [v13, h13', ite_eq_right (by simp), za, e1]; rfl, by rw [v14, h14', e1],
      by rw [v15, h15']; simp only [nzV, hi, e1]⟩

end VG.Proof.RsaPss.AArch64

end

end


/-!
# RSASSA-PSS verification on AArch64: unmasking `DB`

From RSAVP1's result in `EM`: the first checks into `acc` (`acc0`), `DB`
unmasked (`mgfXor`) and its top bits cleared (`clearTop`), its first
nonzero byte found (`posScan`) and checked (`posCheck`): `b1_ok`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)

/-- `EM` after the mask and `clearTop`, from `V`, with `DB` at `e`. -/
def wct (V : Nat → Byte) (mk : List Byte) (e db : Nat) (c : Byte) : Nat → Byte :=
  upd (mixV V mk e db) e (mixV V mk e db e &&& c)

/-- The mask: MGF1 of `H`, the `hLen` bytes after `DB`. -/
def mkB (G : Spec.Mgf1.Hash) (D : Nat) (V : Nat → Byte) (e db : Nat) : List Byte :=
  Spec.Mgf1.mgf1 G ((List.range D).map fun i => V (e + db + i)) db

/-- `acc` after `acc0`. -/
def acc0V (V : Nat → Byte) (k lo : Nat) (c : Byte) : BitVec 64 :=
  ((V (oEm + k - 1)).setWidth 64 ^^^ BitVec.ofNat 64 0xbc) |||
    ((V oEm).setWidth 64 &&& (0#64 - BitVec.ofNat 64 lo)) |||
    ((V (oEm + lo)).setWidth 64 &&& (c.setWidth 64 ^^^ BitVec.ofNat 64 0xFF))

/-- `acc` after `posCheck`, for `DB`'s bytes `f`. -/
def acc1V (a0 : BitVec 64) (f : Nat → Byte) (db : Nat) (any sv : BitVec 64) : BitVec 64 :=
  (a0 ||| (((nzV f db).setWidth 64 ^^^ 1#64) |||
    (if nz f db = none then BitVec.allOnes 64 else 0) >>> 63)) |||
    (if any = 0 then sv ^^^ BitVec.ofNat 64 (db - (nz f db).getD 0 - 1) else 0)

/-- After `posCheck`. -/
structure B1 (G : Spec.Mgf1.Hash) (D : Nat) (t : State) (F S : Addr) (V : Nat → Byte) (k lo db : Nat) (c : Byte)
    (any sv : BitVec 64) (u : State) : Prop where
  sp : u.sp = t.sp
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  cs : ∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x24, .x25], u.gpr r = t.gpr r
  v : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64
  fr : Frame (mgfWr F S ++ [slotR F sPos]) t.mem u.mem
  em : ∀ o, oEm ≤ o → o < oY → u.mem (off S o) = wct V (mkB G D V (oEm + lo) db) (oEm + lo) db c o
  pos : u.mem.readW (off F sPos) 64 =
    BitVec.ofNat 64 ((nz (fun i => wct V (mkB G D V (oEm + lo) db) (oEm + lo) db c (oEm + lo + i)) db).getD 0)
  acc : u.gpr .x26 = acc1V (acc0V V k lo c)
    (fun i => wct V (mkB G D V (oEm + lo) db) (oEm + lo) db c (oEm + lo + i)) db any sv
  sy : u.syms = t.syms

theorem nz_congr {f g : Nat → Byte} : ∀ {j : Nat}, (∀ i < j, f i = g i) → nz f j = nz g j
  | 0, _ => rfl
  | j + 1, h => by
    simp only [nz]
    rw [nz_congr (fun i hi => h i (by omega_using [hi])), h j (by omega_using [])]

theorem nzV_congr {f g : Nat → Byte} {j : Nat} (h : ∀ i < j, f i = g i) : nzV f j = nzV g j := by
  unfold nzV
  rw [← nz_congr h]
  split
  · rename_i i hi
    exact h i (nz_some hi).1
  · rfl

theorem nz_lt {f : Nat → Byte} {j : Nat} (hj : 0 < j) : (nz f j).getD 0 < j := by
  cases h : nz f j with
  | none => exact hj
  | some i => exact (nz_some h).1

section
variable {Gm : Impl.Pbkdf2.Md.AArch64.Stream} (hGm : VG.Proof.Pbkdf2.Md.AArch64.Calls.StreamOK Gm)
  {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hGm.SH.H.hash x) (hGl : Gs.len = Gm.D) (hGv : Proof.Mgf1.Valid Gs)
  {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns}

include hGh hGl hGv in
/-- From RSAVP1's result in `EM` (`V`), `DB` at `oEm + lo`, to `B1`. -/
theorem b1_ok {H : Hash} {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} (R : Rep t.mem S V)
    {k lo db : Nat} {c : Byte} {any sv : BitVec 64} (hk : lo + db + H.D + 1 = k) (hdb : 1 ≤ db)
    (hk2 : k ≤ 1024) (hlo : lo ≤ 1)
    (h23 : t.gpr .x23 = BitVec.ofNat 64 k) (h24 : t.gpr .x24 = off S (oEm + lo))
    (h25 : t.gpr .x25 = BitVec.ofNat 64 db) (hLo : t.mem.readW (off F sLo) 64 = BitVec.ofNat 64 lo)
    (hC : t.mem.readW (off F sC) 64 = c.setWidth 64) (hA : t.mem.readW (off F sAny) 64 = any)
    (hS : t.mem.readW (off F sSaltLen) 64 = sv) {p : Addr} (E : Env Gm g t F S p) {rest : Prog isa}
    {Q : State → Prop} (hQ : ∀ u, B1 Gs H.D t F S V k lo db c any sv u → WP isa rest u Q) :
    WP isa (seqs [.block acc0, mgfXor H g, .block clearTop, posScan, posCheck, rest]) t Q := by
  have c1 : oEm = 2560 := rfl
  have c2 : oY = 3584 := rfl
  have c6 : oRsa = 8192 := rfl
  obtain hW : ∀ {d : Nat}, d + 8 ≤ frameBytes → (d + 8 ≤ sNb ∨ sNb + 8 ≤ d) → (d + 8 ≤ sDone ∨ sDone + 8 ≤ d) →
      ∀ {m : Mem}, Frame (mgfWr F S) t.mem m → m.readW (off F d) 64 = t.mem.readW (off F d) 64 :=
    fun hd h1 h2 _ hf => slot_keep hf (L.slotW hd h1 h2)
  unfold seqs seqs seqs seqs seqs
  -- `acc0`.
  refine WP.seq (WP.mono_syms (acc0_ok L R (by omega_using [hk]) hk2 hlo h23 h24 hLo hC) fun u1 ⟨O1, x26₁⟩ sy1 => ?_)
  obtain L1 := L.congr O1.sp O1.wr (O1.get .x20)
  obtain R1 : Rep u1.mem S V := O1.mem ▸ R
  obtain E1 : Env Gm g u1 F S p := E.step L (by rw [O1.mem]; exact Frame.refl _ _) O1.rd O1.wr sy1
  -- The mask.
  refine WP.seq (WP.mono (mgfXor_ok hGm hGh hGl hGv L1 R1 (e := oEm + lo) (db := db) ⟨by omega_using [], hdb, by omega_using [hk, hk2, c1, c2]⟩
    (by rw [O1.get .x24, h24]) (by rw [O1.get .x25, h25]) E1)
    fun u2 ⟨sp2, rd2, wr2, cs2, v2, fr2, sy2, em2⟩ => ?_)
  obtain L2 := L1.congr sp2 wr2 (cs2 .x20 (by decide) (by decide))
  obtain F2 : Frame (mgfWr F S) t.mem u2.mem := by rw [O1.mem] at fr2; exact fr2
  -- `DB`'s top bits.
  refine WP.seq (WP.mono_syms (clearTop_ok L2 (fun _ _ => rfl) (e := oEm + lo) (c := c)
    (by rw [cs2 .x24 (by decide) (by decide), O1.get .x24, h24]) (by omega_using [hlo, c1, c6])
    (by rw [hW (by decide) (by decide) (by decide) F2, hC])) fun u3 ⟨k3, f3, R3⟩ sy3 => ?_)
  obtain L3 := L2.congr k3.sp k3.wr (k3.get .x20)
  obtain hX : ∀ {d : Nat}, d + 8 ≤ frameBytes → (d + 8 ≤ sNb ∨ sNb + 8 ≤ d) → (d + 8 ≤ sDone ∨ sDone + 8 ≤ d) →
      u3.mem.readW (off F d) 64 = t.mem.readW (off F d) 64 := fun hd h1 h2 => by
    rw [slot_keep f3 (L.slotSd hd), hW hd h1 h2 F2]
  -- The first nonzero byte.
  generalize hmk : mkB Gs H.D V (oEm + lo) db = mk
  have hmk' : Spec.Mgf1.mgf1 Gs ((List.range H.D).map fun i => V (oEm + lo + db + i)) db = mk := hmk
  rw [hmk'] at em2
  obtain hv : ∀ o, oEm ≤ o → o < oY →
      upd (fun o => u2.mem (off S o)) (oEm + lo) (u2.mem (off S (oEm + lo)) &&& c) o =
        wct V mk (oEm + lo) db c o := fun o h1 h2 => by
    unfold wct upd
    simp only []
    rw [em2 o h1 h2, em2 (oEm + lo) (by omega_using []) (by omega_using [hlo, c1, c2])]
  obtain hf : ∀ i < db, upd (fun o => u2.mem (off S o)) (oEm + lo) (u2.mem (off S (oEm + lo)) &&& c) (oEm + lo + i) =
      wct V mk (oEm + lo) db c (oEm + lo + i) := fun i hi => hv _ (by omega_using []) (by omega_using [hk, hk2, c1, c2, hi])
  refine WP.seq (WP.mono_syms (posScan_ok L3 R3 (e := oEm + lo) (db := db) (by omega_using [hk, hk2, c1, c6]) (by omega_using [hdb])
    (by rw [k3.get .x24, cs2 .x24 (by decide) (by decide), O1.get .x24, h24])
    (by rw [k3.get .x25, cs2 .x25 (by decide) (by decide), O1.get .x25, h25])) fun u4 ⟨O4, x13₄, x14₄, x15₄⟩ sy4 => ?_)
  rw [nz_congr hf] at x13₄ x14₄
  rw [nzV_congr hf] at x15₄
  obtain L4 := L3.congr O4.sp O4.wr (O4.get .x20)
  -- Its checks.
  refine WP.seq (WP.mono_syms (posCheck_ok L4 x13₄ x14₄ x15₄ (acc := acc0V V k lo c) (any := any) (sv := sv)
    (by rw [O4.get .x26, k3.get .x26, cs2 .x26 (by decide) (by decide), x26₁]; rfl)
    (by rw [O4.get .x25, k3.get .x25, cs2 .x25 (by decide) (by decide), O1.get .x25, h25]) (nz_lt (by omega_using [hdb]))
    (by rw [O4.mem, hX (by decide) (by decide) (by decide), hA])
    (by rw [O4.mem, hX (by decide) (by decide) (by decide), hS])) fun u5 ⟨k5, m5, x26₅⟩ sy5 => hQ u5 ?_)
  obtain R5 := R3.frame (m' := u5.mem) (rs := [slotR F sPos]) (by rw [m5, O4.mem]; exact frame_slot _ F sPos _)
    (L.slotS (by decide))
  subst hmk
  exact {
    sp := by rw [k5.sp, O4.sp, k3.sp, sp2, O1.sp]
    rd := by rw [k5.rd, O4.rd, k3.rd, rd2, O1.rd]
    wr := by rw [k5.wr, O4.wr, k3.wr, wr2, O1.wr]
    cs := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      · rw [k5.get _ (by decide), O4.get _ (by decide), k3.get _ (by decide), cs2 _ (by decide) (by decide),
          O1.get _ (by decide)]
    v := fun r hr => by rw [k5.vcs r hr, O4.vcs r hr, k3.vcs r hr, v2 r hr, O1.vcs r hr]
    fr := ((F2.mono (by simp)).trans ((f3.mono (by simp)).trans (by
      rw [m5, O4.mem]; exact (frame_slot _ F sPos _).mono (by simp))))
    em := fun o h1 h2 => by rw [R5 o (by omega_using [c2, c6, h2]), hv o h1 h2]
    pos := by rw [m5, Mem.readW_writeW_self64]
    acc := x26₅
    sy := by rw [sy5, sy4, sy3, sy2, sy1] }

end

end VG.Proof.RsaPss.AArch64

end

end

/-! ### `RsaPss.AArch64.VerifyLogic`, which only this module used -/

section

/-! ### `RsaPss.AArch64.VerifyB2`, which this module and modules that import it used -/

section

/-!
# RSASSA-PSS verification on AArch64: hashing `M'` and comparing

After `posCheck`: `M' = (0x00)⁸ ‖ mHash ‖ salt` in `Y` (`clearY`,
`copyDigest`, `copyDb`, `shift`), hashed (`verifyNb`, `ctHash`), and the
hash compared with `H` into `acc`, `x0 = 1` exactly when `acc = 0` (`cmpH`):
`b2_ok`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)

theorem orF_congr {g g' : Nat → BitVec 64} : ∀ {j : Nat}, (∀ i < j, g i = g' i) → orF g j = orF g' j
  | 0, _ => rfl
  | j + 1, h => by
    simp only [orF]
    rw [orF_congr (fun i hi => h i (by omega_using [hi])), h j (by omega_using [])]

/-- `M'`: eight zeros, `mHash` and the salt, the `db - pos - 1` bytes of
`DB` (`W`) after `pos`. -/
def msgV (mH : List Byte) (W : Nat → Byte) (db pos : Nat) : List Byte :=
  Spec.RsaPss.zeros 8 ++ mH ++ (List.range (db - pos - 1)).map fun i => W (pos + 1 + i)

theorem msgV_length (mH : List Byte) (W : Nat → Byte) (db pos : Nat) :
    (msgV mH W db pos).length = 8 + mH.length + (db - pos - 1) := by
  simp only [msgV, List.length_append, RsaPss.zeros_length, List.length_map, List.length_range]

/-- `x0` after `cmpH`, for `acc` and the hash `h` of `M'` against `H` in
`W` at `e + db`. -/
def resV (acc : BitVec 64) (h : List Byte) (W : Nat → Byte) (e db D : Nat) : BitVec 64 :=
  ((acc ||| orF (fun i => (h.getD i 0).setWidth 64 ^^^ (W (e + db + i)).setWidth 64) D) - 1#64) >>> 63

section
variable {H : Hash} (hH : HashOK H)

include hH in
/-- `Y` from `clearY`, `copyDigest`, `copyDb` and `shift` is `M'` padded
with zeros. -/
theorem msg_y {V0 : Nat → Byte} {W : Nat → Byte} {mH : List Byte} {e db pos i : Nat} (hm : mH.length = H.D)
    (hpos : pos < db) (hdb : db < 1024) (hi : i < 2048) :
    shW (updL (updL (clr V0 oY 2048) (oY + 8) mH) (oY + 8 + H.D)
      ((List.range db).map fun j => updL (clr V0 oY 2048) (oY + 8) mH (e + j))) (oY + 8 + H.D) db
      (fun j => W j) (pos + 1) (oY + i) = (msgV mH W db pos).getD i 0 := by
  have hDN := hH.sizes.DN
  have hN := hH.N_le
  unfold msgV
  rw [getD_app, getD_app]
  simp only [List.length_append, RsaPss.zeros_length, hm]
  by_cases h1 : i < 8
  · simp (disch := omega) only [shW, updL, clr, ↓ite_eq_left, ↓ite_eq_right]
    exact (RsaPss.zeros_getD _ _).symm
  by_cases h2 : i < 8 + H.D
  · simp (disch := omega) only [shW, updL, ↓ite_eq_left, ↓ite_eq_right]
    rw [show oY + i - (oY + 8) = i - 8 by omega_using []]
  by_cases h3 : i < 8 + H.D + db
  · simp (disch := omega) only [shW, ↓ite_eq_left, ↓ite_eq_right]
    unfold zf
    rw [show oY + i - (oY + 8 + H.D) + (pos + 1) = pos + 1 + (i - (8 + H.D)) by omega_using []]
    by_cases h4 : i - (8 + H.D) < db - pos - 1
    · rw [ite_eq_left (by omega_using [h4]), List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h4]
      rfl
    · rw [ite_eq_right (by omega_using [h4]), List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_none (by rw [List.length_range]; omega_using [h4])]
      rfl
  · simp (disch := omega) only [shW, updL, clr, ↓ite_eq_left, ↓ite_eq_right, hm, List.length_map,
      List.length_range]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_none (by rw [List.length_range]; omega_using [h3])]
    rfl

include hH in
/-- From `posCheck`'s state (`u`): `x0` is 1 exactly when `acc` is zero and
the hash of `M'` is `H`. -/
theorem b2_ok {u : State} {F S : Addr} (L : Lay u F S) {W : Nat → Byte} {e db pos : Nat} {acc : BitVec 64}
    {dig : Addr} (hEm : ∀ o, oEm ≤ o → o < oY → u.mem (off S o) = W o) (he : oEm ≤ e)
    (hfit : e + db + H.D ≤ oY) (hpos : pos < db) (hdb : db < 1024)
    (h19 : u.gpr .x19 = off S oSt) (h21 : u.gpr .x21 = off S oDig) (h24 : u.gpr .x24 = off S e)
    (h25 : u.gpr .x25 = BitVec.ofNat 64 db) (h26 : u.gpr .x26 = acc)
    (hP : u.mem.readW (off F sPos) 64 = BitVec.ofNat 64 pos) (hdg : u.mem.readW (off F sDig) 64 = dig)
    (hr : ∀ j < H.D, InRegions (u.rd ++ u.wr) (dig + BitVec.ofNat 64 j) 1)
    (hd : Region.Disjoint ⟨dig, H.D⟩ ⟨S, oRsa⟩) {f : MdFns} {dn : String} (hT : HT H dn f F u.mem u.syms)
    (hdo : DigOK H.P) :
    WP isa (seqs [clearY, copyDigest H, copyDb H, shift H, .block (verifyNb H), ctHash f H, cmpH H]) u
      fun u' => u'.sp = u.sp ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
        (∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x24, .x25], u'.gpr r = u.gpr r) ∧
        (∀ r ∈ preservedV, (u'.v r).extractLsb' 0 64 = (u.v r).extractLsb' 0 64) ∧
        Frame (mgfWr F S) u.mem u'.mem ∧
        u'.gpr .x0 = resV acc (hH.SH.H.hash (msgV (Spec.Rsa.bytesAt u.mem dig H.D) (fun i => W (e + i)) db pos))
          W e db H.D := by
  have hD := hH.sizes.D0
  have hDN := hH.sizes.DN
  have hN := hH.N_le
  have hL := hH.L
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have c1 : oEm = 2560 := rfl
  have c2 : oY = 3584 := rfl
  have c3 : oDig = 2304 := rfl
  have c6 : oRsa = 8192 := rfl
  unfold seqs seqs seqs seqs seqs seqs
  -- `Y` cleared.
  refine WP.seq (WP.mono_syms (clearY_ok L (V := fun o => u.mem (off S o)) (fun _ _ => rfl)) fun u1 ⟨k1, f1, R1⟩ sy1 => ?_)
  obtain L1 := L.congr k1.sp k1.wr (k1.get .x20)
  obtain hm1 : Spec.Rsa.bytesAt u1.mem dig H.D = Spec.Rsa.bytesAt u.mem dig H.D :=
    bytes_apartL f1 (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) (by omega_arith)
  -- `mHash`.
  refine WP.seq (WP.mono_syms (copyDigest_ok hH L1 R1 (dig := dig) (by rw [slot_keep f1 (L.slotSd (by decide)), hdg])
    (by rw [k1.rd, k1.wr]; exact hr) hd) fun u2 ⟨k2, f2, R2⟩ sy2 => ?_)
  rw [hm1] at R2
  generalize hmH : Spec.Rsa.bytesAt u.mem dig H.D = mH at R2
  obtain hml : mH.length = H.D := by rw [← hmH, VG.Proof.RsaPkcs1Sig.bytesAt_length]
  obtain L2 := L1.congr k2.sp k2.wr (k2.get .x20)
  -- `DB`.
  refine WP.seq (WP.mono_syms (copyDb_ok hH L2 R2 (e := e) (db := db) (by omega_arith) (by omega_arith)
    (by rw [k2.get .x24, k1.get .x24, h24]) (by rw [k2.get .x25, k1.get .x25, h25])) fun u3 ⟨k3, f3, R3⟩ sy3 => ?_)
  obtain L3 := L2.congr k3.sp k3.wr (k3.get .x20)
  obtain F3 : Frame [⟨S, oRsa⟩] u.mem u3.mem := f1.trans (f2.trans f3)
  -- The salt to `DB`'s place.
  refine WP.seq (WP.mono_syms (shift_ok H (by omega_arith) L3 R3 (W := fun j => W (e + j)) hpos hdb (by omega_arith)
    (fun m hm => ?_) (by rw [k3.get .x25, k2.get .x25, k1.get .x25, h25])
    (by rw [slot_keep F3 (L.slotSd (by decide)), hP])) fun u4 ⟨k4, f4, R4, x22₄⟩ sy4 => ?_)
  · unfold zf
    by_cases h : m < db
    · rw [ite_eq_left h]
      simp (disch := omega_arith) only [updL, clr, ↓ite_eq_left, ↓ite_eq_right, hml, List.length_map, List.length_range]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega_arith)]
      simp (disch := omega_arith) only [Option.map_some, Option.getD_some, ↓ite_eq_right]
      rw [show oY + 8 + H.D + m - (oY + 8 + H.D) = m by omega_arith, hEm _ (by omega_arith) (by omega_arith)]
    · rw [ite_eq_right h]
      simp (disch := omega_arith) only [updL, clr, ↓ite_eq_left, ↓ite_eq_right, hml, List.length_map, List.length_range]
  obtain L4 := L3.congr k4.sp k4.wr (k4.get .x20)
  -- `nbm`.
  refine WP.seq (WP.mono_syms (verifyNb_ok hH L4 (db := db) (by omega_arith)
    (by rw [k4.get .x25, k3.get .x25, k2.get .x25, k1.get .x25, h25])) fun u5 ⟨k5, m5⟩ sy5 => ?_)
  obtain L5 := L4.congr k5.sp k5.wr (k5.get .x20)
  obtain R5 := R4.frame (m' := u5.mem) (rs := [slotR F sNb]) (by rw [m5]; exact frame_slot _ F sNb _)
    (L.slotS (by decide))
  -- `Hash(M')`.
  generalize hmsg : msgV mH (fun i => W (e + i)) db pos = msg
  obtain hmsgl : msg.length = 8 + H.D + (db - pos - 1) := by rw [← hmsg, msgV_length, hml]
  obtain hnb1 := Nat.lt_div_mul_add (a := db + 7 + H.D + H.P.L) (b := H.P.B) hB0
  obtain hnb2 := Nat.div_mul_le_self (db + 7 + H.D + H.P.L) H.P.B
  obtain hnbB : ((db + 7 + H.D + H.P.L) / H.P.B + 1) * H.P.B =
      (db + 7 + H.D + H.P.L) / H.P.B * H.P.B + H.P.B := Nat.succ_mul _ _
  obtain g5 : ∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x24, .x25, .x26], u5.gpr r = u.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [k5.get _ (by decide), k4.get _ (by decide), k3.get _ (by decide), k2.get _ (by decide),
        k1.get _ (by decide)]
  obtain F5 : Frame (mgfWr F S) u.mem u5.mem :=
    (F3.trans f4).mono (by simp) |>.trans (by rw [m5]; exact (frame_slot _ F sNb _).mono (by simp))
  obtain hT5 : HT H dn f F u5.mem u5.syms := by rw [sy5, sy4, sy3, sy2, sy1]; exact hT.stepW L F5
  refine WP.seq (WP.mono (ctHash_ok hH L5 R5 (msg := msg) (nbm := (db + 7 + H.D + H.P.L) / H.P.B + 1)
    (by rw [g5 .x19 (by decide), h19]) (by rw [g5 .x21 (by decide), h21])
    (by rw [k5.get .x22, x22₄, hmsgl]) (by rw [m5, Mem.readW_writeW_self64]) (by rw [hmsgl, hnbB]; omega_arith)
    (by rw [hnbB]; omega_arith) (fun i hi => ?_) hT5 hdo) fun u6 ⟨O6, d6⟩ => ?_)
  · rw [← hmsg]
    exact msg_y hH hml hpos hdb (by rw [hnbB] at hi; omega_arith)
  obtain L6 := L5.congr O6.sp O6.wr (O6.cs .x20 (by decide))
  -- The comparison.
  refine WP.mono (cmpH_ok hH L6 (V := fun o => u6.mem (off S o)) (fun _ _ => rfl) (e := e) (db := db) (acc := acc)
    hfit (by rw [O6.cs .x21 (by decide), g5 .x21 (by decide), h21])
    (by rw [O6.cs .x24 (by decide), g5 .x24 (by decide), h24])
    (by rw [O6.cs .x25 (by decide), g5 .x25 (by decide), h25])
    (by rw [O6.cs .x26 (by decide), g5 .x26 (by decide), h26])) fun u7 ⟨O7, x0₇⟩ => ?_
  refine ⟨by rw [O7.sp, O6.sp, k5.sp, k4.sp, k3.sp, k2.sp, k1.sp], by rw [O7.rd, O6.rd, k5.rd, k4.rd, k3.rd, k2.rd, k1.rd],
    by rw [O7.wr, O6.wr, k5.wr, k4.wr, k3.wr, k2.wr, k1.wr], fun r hr => ?_,
    fun r hr => by rw [O7.vcs r hr, O6.vec r hr, k5.vcs r hr, k4.vcs r hr, k3.vcs r hr, k2.vcs r hr, k1.vcs r hr],
    by rw [O7.mem]; exact F5.trans (O6.fr.mono (by simp)), ?_⟩
  · have hr' := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [O7.get r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      O6.cs r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      g5 r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
  · rw [x0₇, resV]
    congr 2
    refine congrArg (acc ||| ·) (orF_congr fun i hi => ?_)
    rw [← off_add, byte_of_bytesAt d6 hi, O6.em _ (by omega_arith) (by omega_arith)]
    simp (disch := omega_arith) only [shW, updL, clr, ↓ite_eq_right]
    rw [hEm _ (by omega_arith) (by omega_arith)]

end

end VG.Proof.RsaPss.AArch64

end

end

/-!
# RSASSA-PSS verification on AArch64: what the result means

`vlogic`: `x0` after `cmpH` (`resV`, from `acc0V`, `acc1V` and the hash of
`M'`) is 1 exactly when the encoding is valid, byte by byte
(`VerifyCases.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64

open VG VG.Spec.Mgf1 VG.Impl.RsaPss.AArch64

theorem or_eq_zero64 (x y : BitVec 64) : x ||| y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    constructor
    · ext i hi; have := congrArg (·[i]) h; simp only [BitVec.getElem_or] at this ⊢; simp_all
    · ext i hi; have := congrArg (·[i]) h; simp only [BitVec.getElem_or] at this ⊢; simp_all
  · rintro ⟨rfl, rfl⟩; rfl

theorem xor_eq_zero64 (a b : BitVec 64) : a ^^^ b = 0 ↔ a = b := BitVec.xor_eq_zero_iff

theorem zext_inj (a b : Byte) : BitVec.setWidth 64 a = BitVec.setWidth 64 b ↔ a = b := by
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_setWidth] at this
    rwa [Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)] at this
  · rintro rfl; rfl

theorem zext_eq_zero (a : Byte) : BitVec.setWidth 64 a = 0 ↔ a = 0 := zext_inj a 0

theorem ff_bit (i : Nat) (hi : i < 64) : (255#64)[i] = decide (i < 8) := by
  rw [BitVec.getElem_eq_testBit_toNat]
  by_cases h : i < 8
  · revert h; revert i; decide
  · rw [decide_eq_false h]
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : (255#64).toNat < 2 ^ 8)
      (Nat.pow_le_pow_right (by decide) (by omega_arith)))

theorem zext_and_not (top c : Byte) :
    BitVec.setWidth 64 top &&& (BitVec.setWidth 64 c ^^^ 255#64) = BitVec.setWidth 64 (top &&& ~~~c) := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_xor, BitVec.getElem_setWidth, ff_bit i hi]
  by_cases h : i < 8
  · simp [h]
  · simp [h, BitVec.getLsbD_of_ge _ _ (by omega_arith : 8 ≤ i)]

theorem acc0V_eq_zero (V : Nat → Byte) (k : Nat) {lo : Nat} (c : Byte) (hlo : lo ≤ 1) :
    acc0V V k lo c = 0 ↔ V (oEm + k - 1) = 0xbc ∧ (lo = 1 → V oEm = 0) ∧ V (oEm + lo) &&& ~~~c = 0 := by
  unfold acc0V
  rw [or_eq_zero64, or_eq_zero64, xor_eq_zero64,
    show (BitVec.ofNat 64 0xbc : BitVec 64) = BitVec.setWidth 64 (0xbc : Byte) from rfl, zext_inj,
    show (BitVec.ofNat 64 0xFF : BitVec 64) = 255#64 from rfl, zext_and_not, zext_eq_zero]
  rcases (show lo = 0 ∨ lo = 1 by omega_arith) with rfl | rfl
  · simp only [show 0#64 - BitVec.ofNat 64 0 = 0 from rfl]
    simp
  · simp only [show 0#64 - BitVec.ofNat 64 1 = BitVec.allOnes 64 from rfl, BitVec.and_allOnes, zext_eq_zero]
    simp [and_assoc]

theorem acc1V_eq_zero (a0 : BitVec 64) (f : Nat → Byte) (db : Nat) (any sv : BitVec 64) :
    acc1V a0 f db any sv = 0 ↔ a0 = 0 ∧ nzV f db = 1 ∧ nz f db ≠ none ∧
      (any = 0 → sv = BitVec.ofNat 64 (db - (nz f db).getD 0 - 1)) := by
  unfold acc1V
  rw [or_eq_zero64, or_eq_zero64, or_eq_zero64, xor_eq_zero64,
    show (1#64 : BitVec 64) = BitVec.setWidth 64 (1 : Byte) from rfl, zext_inj]
  by_cases h : nz f db = none
  · simp [h]
  · rw [ite_eq_right h, show (0 : BitVec 64) >>> 63 = 0 from rfl]
    by_cases ha : any = 0 <;> simp [ha, h, and_assoc]

theorem orF_eq_zero (g : Nat → BitVec 64) : ∀ j, orF g j = 0 ↔ ∀ i < j, g i = 0
  | 0 => by simp [orF]
  | j + 1 => by
    rw [orF, or_eq_zero64, orF_eq_zero g j]
    constructor
    · rintro ⟨hi, hj⟩ i hi'
      exact if e : i = j then e ▸ hj else hi i (by omega_arith)
    · intro hi
      exact ⟨fun i hi' => hi i (by omega_arith), hi j (by omega_arith)⟩

theorem lt_or {x y : BitVec 64} {n : Nat} (hx : x.toNat < 2 ^ n) (hy : y.toNat < 2 ^ n) : (x ||| y).toNat < 2 ^ n := by
  rw [BitVec.toNat_or]; exact Nat.or_lt_two_pow hx hy

theorem lt_xor {x y : BitVec 64} {n : Nat} (hx : x.toNat < 2 ^ n) (hy : y.toNat < 2 ^ n) : (x ^^^ y).toNat < 2 ^ n := by
  rw [BitVec.toNat_xor]; exact Nat.xor_lt_two_pow hx hy

theorem lt_and {x y : BitVec 64} {n : Nat} (hx : x.toNat < 2 ^ n) : (x &&& y).toNat < 2 ^ n := by
  rw [BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_left hx

theorem lt_byte (b : Byte) {n : Nat} (hn : 8 ≤ n) : (b.setWidth 64).toNat < 2 ^ n := by
  rw [BitVec.toNat_setWidth]
  have := b.isLt
  have : 2 ^ 8 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
  omega_arith

theorem lt_ofNat {a n : Nat} (ha : a < 2 ^ n) : (BitVec.ofNat 64 a).toNat < 2 ^ n := by
  rw [BitVec.toNat_ofNat]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) ha

theorem orF_lt (g : Nat → BitVec 64) {n : Nat} (hg : ∀ i, (g i).toNat < 2 ^ n) : ∀ j, (orF g j).toNat < 2 ^ n
  | 0 => by simp [orF]; exact Nat.two_pow_pos n
  | j + 1 => lt_or (orF_lt g hg j) (hg j)

/-- `(y - 1) >>> 63`: 1 exactly when `y = 0`, for `y < 2⁶³`. -/
theorem top_sub (y : BitVec 64) (hy : y.toNat < 2 ^ 63) : (y - 1#64) >>> 63 = if y = 0 then 1#64 else 0#64 := by
  by_cases h : y = 0
  · subst h; decide
  · rw [ite_eq_right h]
    have h0 : y.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq e)
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]
    simp only [BitVec.toNat_ofNat]
    rw [show (2 ^ 64 - 1 % 2 ^ 64 + y.toNat) % 2 ^ 64 = y.toNat - 1 by omega_arith]
    exact Nat.div_eq_of_lt (by omega_arith)

theorem nz_lz (l : List Byte) : ∀ j ≤ l.length, nz (fun i => l.getD i 0) j = if lz l < j then some (lz l) else none
  | 0, _ => by simp [nz]
  | j + 1, hj => by
    have ih := nz_lz l j (by omega_arith)
    simp only [nz, ih]
    by_cases h : lz l < j
    · rw [ifp h]; exact (ifp (show lz l < j + 1 by omega_arith) _ _).symm
    · rw [ifn h]
      by_cases h' : lz l = j
      · subst h'
        rw [ifn (getD_lz_ne (by omega_arith)), ifp (by omega_arith)]
      · rw [ifp (getD_lt_lz (by omega_arith)), ifn (by omega_arith)]

section
variable {Hs Gs : Hash} (hGv : Proof.Mgf1.Valid Gs) {D : Nat} (hHl : Hs.len = D) {x : List Byte} {V : Nat → Byte}
  {k lo db : Nat} (hx : x.length = k) (hV : ∀ i < k, V (oEm + i) = x.getD i 0) (hdb : lo + db + D + 1 = k)

include hHl hx hV hdb in
/-- `H` in `EM`. -/
theorem vH_view : vH Hs (x.drop lo) db = (List.range D).map fun i => V (oEm + lo + db + i) := by
  unfold vH
  refine eq_range_map (by simp only [List.length_take, List.length_drop, hx]; omega_arith) fun i hi => ?_
  rw [show oEm + lo + db + i = oEm + (lo + db + i) by omega_arith, hV _ (by omega_arith)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
  rw [ifp (by omega_arith)]
  congr 2
  omega_arith

include hGv hHl hx hV hdb in
/-- `DB` in `EM`, unmasked and its top bits cleared. -/
theorem vDb_view {c : Byte} {z : Nat} (hc : c = (0xFF : Byte) >>> z) :
    ∀ i < db, wct V (mkB Gs D V (oEm + lo) db) (oEm + lo) db c (oEm + lo + i) =
      (vDb₂ Gs Hs (x.drop lo) db z).getD i 0 := by
  intro i hi
  have hmk : mkB Gs D V (oEm + lo) db = mgf1 Gs (vH Hs (x.drop lo) db) db := by
    rw [vH_view hHl hx hV hdb]; rfl
  have hml := Proof.Mgf1.mgf1_length hGv (vH Hs (x.drop lo) db) db
  have ht : ((x.drop lo).take db).length = db := by simp only [List.length_take, List.length_drop, hx]; omega_arith
  have hxi : ∀ j < db, ((x.drop lo).take db).getD j 0 = V (oEm + lo + j) := fun j hj => by
    rw [Nat.add_assoc, hV _ (by omega_arith)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
    rw [ifp hj]
  unfold vDb₂
  rw [clearTop_getD, hmk, hc]
  unfold wct upd mixV
  by_cases h0 : i = 0
  · subst h0
    rw [ifp rfl, ifp (by omega_arith), ifp (by omega_arith), xorBytes_getD (by omega_arith) (by omega_arith), hxi 0 hi]
    simp only [Nat.add_zero, Nat.sub_self]
  · rw [ifn h0, ifn (by omega_arith), ifp (by omega_arith), xorBytes_getD (by omega_arith) (by omega_arith), hxi i hi]
    congr 2
    omega_arith

end

theorem lt_shr63 (x : BitVec 64) : (x >>> 63).toNat < 2 ^ 11 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  have : x.toNat / 2 ^ 63 < 2 := Nat.div_lt_of_lt_mul (by omega_arith)
  omega_arith

/-- What `cmpH` ORs is below `2¹¹`. -/
theorem acc_lt (V : Nat → Byte) (k lo : Nat) (c : Byte) (f : Nat → Byte) (db : Nat) (any sv : BitVec 64)
    (g : Nat → BitVec 64) (D : Nat) (hdb : db < 2 ^ 11) (hs : any = 0 → sv.toNat < 2 ^ 11)
    (hg : ∀ i, (g i).toNat < 2 ^ 11) :
    (acc1V (acc0V V k lo c) f db any sv ||| orF g D).toNat < 2 ^ 63 := by
  have h11 : (2 : Nat) ^ 11 < 2 ^ 63 := by decide
  have hb : ∀ b : Byte, (b.setWidth 64).toNat < 2 ^ 11 := fun b => lt_byte b (by decide)
  have h0 : (acc0V V k lo c).toNat < 2 ^ 11 := by
    unfold acc0V
    exact lt_or (lt_or (lt_xor (hb _) (lt_ofNat (by decide))) (lt_and (hb _))) (lt_and (hb _))
  have h1 : (acc1V (acc0V V k lo c) f db any sv).toNat < 2 ^ 11 := by
    unfold acc1V
    refine lt_or (lt_or h0 (lt_or (lt_xor (hb _) (by decide)) (lt_shr63 _))) ?_
    split
    · rename_i ha
      exact lt_xor (hs ha) (lt_ofNat (by omega_arith))
    · exact Nat.two_pow_pos 11
  exact Nat.lt_trans (lt_or h1 (orF_lt g hg D)) h11

theorem list_eq_iff_getD {a b : List Byte} {n : Nat} (ha : a.length = n) (hb : b.length = n) :
    a = b ↔ ∀ i < n, a.getD i 0 = b.getD i 0 := by
  constructor
  · rintro rfl _ _; rfl
  · intro h
    apply List.ext_getElem (by omega_arith)
    intro i h₁ h₂
    have := h i (by omega_arith)
    rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁,
      List.getElem?_eq_getElem h₂] at this

theorem eq_ofNat_iff {a : Nat} (ha : a < 2 ^ 64) (b : BitVec 64) : b = BitVec.ofNat 64 a ↔ b.toNat = a := by
  constructor
  · rintro rfl; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  · intro h; apply BitVec.eq_of_toNat_eq; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]

/-- The salt after the first nonzero byte of `DB` (`f`, `dbL`). -/
theorem msgV_eq {f : Nat → Byte} {dbL : List Byte} {db : Nat} (hl : dbL.length = db)
    (hf : ∀ i < db, f i = dbL.getD i 0) (mH : List Byte) {p : Nat} (hp : p < db) :
    msgV mH f db p = Spec.RsaPss.zeros 8 ++ mH ++ dbL.drop (p + 1) := by
  unfold msgV
  refine congrArg (_ ++ ·) (eq_range_map (by rw [List.length_drop, hl]; omega_arith) fun i hi => ?_).symm
  rw [hf _ (by omega_arith)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- `x0` after `cmpH` is 1 exactly when the encoding in `x` is valid. -/
theorem vlogic {Hs Gs : Hash} (hHv : Proof.Mgf1.Valid Hs) (hGv : Proof.Mgf1.Valid Gs) {D : Nat} (hHl : Hs.len = D) {x : List Byte} {V : Nat → Byte}
    {k lo db : Nat} (hx : x.length = k) (hV : ∀ i < k, V (oEm + i) = x.getD i 0) (hdb : lo + db + D + 1 = k)
    (hdb1 : 1 ≤ db) (hlo : lo ≤ 1) (hk : k ≤ 1024) {mH : List Byte} (hm : mH.length = D) {c : Byte} {z : Nat}
    (hc : c = (0xFF : Byte) >>> z) {any sv : BitVec 64} (hs : any = 0 → sv.toNat < db) {b : Bool}
    (hb : b = true ↔ (lo = 1 → x.getD 0 0 = 0) ∧
      EncOk₂ Gs Hs mH (x.drop lo) (k - lo) z (if any = 0 then some sv.toNat else none)) :
    resV (acc1V (acc0V V k lo c) (fun i => wct V (mkB Gs D V (oEm + lo) db) (oEm + lo) db c (oEm + lo + i)) db any sv)
      (Hs.hash (msgV mH (fun i => wct V (mkB Gs D V (oEm + lo) db) (oEm + lo) db c (oEm + lo + i)) db
        ((nz (fun i => wct V (mkB Gs D V (oEm + lo) db) (oEm + lo) db c (oEm + lo + i)) db).getD 0)))
      (wct V (mkB Gs D V (oEm + lo) db) (oEm + lo) db c) (oEm + lo) db D = if b then 1#64 else 0#64 := by
  have hf := vDb_view hGv hHl hx hV hdb hc
  have hH : ∀ i < D, wct V (mkB Gs D V (oEm + lo) db) (oEm + lo) db c (oEm + lo + db + i) =
      (vH Hs (x.drop lo) db).getD i 0 := fun i hi => by
    rw [vH_view hHl hx hV hdb]
    unfold wct upd mixV
    rw [ifn (by omega), ifn (by omega), List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
    rfl
  have e1 : V (oEm + k - 1) = (x.drop lo).getD (k - lo - 1) 0 := by
    rw [show oEm + k - 1 = oEm + (k - 1) by omega, hV _ (by omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
    congr 2; omega
  have e2 : V oEm = x.getD 0 0 := hV 0 (by omega)
  have e3 : V (oEm + lo) = (x.drop lo).getD 0 0 := by
    rw [hV _ (by omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_zero]
  have hvl : (vH Hs (x.drop lo) db).length = D := by rw [vH_view hHl hx hV hdb, List.length_map, List.length_range]
  have hdbl : (vDb₂ Gs Hs (x.drop lo) db z).length = db := by
    rw [vDb₂, clearTop_length, Proof.Mgf1.xorBytes_length, Proof.Mgf1.mgf1_length hGv]
    simp only [List.length_take, List.length_drop, hx]; omega
  generalize wct V (mkB Gs D V (oEm + lo) db) (oEm + lo) db c = W at hf hH ⊢
  rw [resV, top_sub _ (acc_lt V k lo c _ db any sv _ D (by omega) (fun h => by have := hs h; omega)
    (fun i => lt_xor (lt_byte _ (by decide)) (lt_byte _ (by decide))))]
  suffices hy : acc1V (acc0V V k lo c) (fun i => W (oEm + lo + i)) db any sv |||
      orF (fun i => BitVec.setWidth 64 ((Hs.hash (msgV mH (fun i => W (oEm + lo + i)) db
        ((nz (fun i => W (oEm + lo + i)) db).getD 0))).getD i 0) ^^^ BitVec.setWidth 64 (W (oEm + lo + db + i))) D = 0 ↔
      (lo = 1 → x.getD 0 0 = 0) ∧ EncOk₂ Gs Hs mH (x.drop lo) (k - lo) z (if any = 0 then some sv.toNat else none) by
    rw [← hb] at hy
    by_cases h : b = true
    · rw [ifp (hy.mpr h), ifp h]
    · rw [ifn (fun e => h (hy.mp e)), ifn h]
  unfold EncOk₂
  rw [show k - lo - Hs.len - 1 = db by omega]
  generalize vDb₂ Gs Hs (x.drop lo) db z = dbL at hf hdbl ⊢
  have hnz : nz (fun i => W (oEm + lo + i)) db = if lz dbL < db then some (lz dbL) else none := by
    rw [nz_congr hf, nz_lz dbL db (by omega)]
  have hnzV : nzV (fun i => W (oEm + lo + i)) db = if lz dbL < db then dbL.getD (lz dbL) 0 else 0 := by
    rw [nzV_congr hf]
    unfold nzV
    rw [nz_lz dbL db (by omega)]
    by_cases hp : lz dbL < db
    · rw [ifp hp, ifp hp]
    · rw [ifn hp, ifn hp]
  rw [or_eq_zero64, acc1V_eq_zero, acc0V_eq_zero _ _ _ hlo, orF_eq_zero, hnz, hnzV, e1, e2, e3, ← hc]
  by_cases hp : lz dbL < db
  · simp only [hp, ↓reduceIte, Option.getD_some, ne_eq, reduceCtorEq, not_false_eq_true, true_and]
    rw [msgV_eq hdbl hf mH hp]
    have hz : ∀ i < D, (BitVec.setWidth 64 ((Hs.hash (Spec.RsaPss.zeros 8 ++ mH ++ dbL.drop (lz dbL + 1))).getD i 0) ^^^
        BitVec.setWidth 64 (W (oEm + lo + db + i)) = 0) ↔
        (Hs.hash (Spec.RsaPss.zeros 8 ++ mH ++ dbL.drop (lz dbL + 1))).getD i 0 = (vH Hs (x.drop lo) db).getD i 0 :=
      fun i hi => by rw [xor_eq_zero64, zext_inj, hH i hi]
    rw [show (∀ i < D, BitVec.setWidth 64 ((Hs.hash (Spec.RsaPss.zeros 8 ++ mH ++ dbL.drop (lz dbL + 1))).getD i 0) ^^^
        BitVec.setWidth 64 (W (oEm + lo + db + i)) = 0) ↔ _ from forall₂_congr hz,
      ← list_eq_iff_getD (by rw [hHv.2, hHl]) hvl]
    have hsl : ∀ {any : BitVec 64}, (any = 0 → sv = BitVec.ofNat 64 (db - lz dbL - 1)) ↔
        ((if any = 0 then some sv.toNat else none) = none ∨
          (if any = 0 then some sv.toNat else none) = some (db - 1 - lz dbL)) := fun {any} => by
      by_cases ha : any = 0
      · simp only [ha, ite_true, reduceCtorEq, false_or, Option.some.injEq, true_implies]
        rw [eq_ofNat_iff (by omega)]
        omega
      · rw [ite_eq_right ha]
        exact ⟨fun _ => .inl rfl, fun _ h => absurd h ha⟩
    rw [hsl]
    constructor
    · rintro ⟨⟨⟨hA, hP, hB⟩, hC, hS⟩, hH'⟩
      exact ⟨hP, hA, hB, hC, hS, hH'⟩
    · rintro ⟨hP, hA, hB, hC, hS, hH'⟩
      exact ⟨⟨⟨hA, hP, hB⟩, hC, hS⟩, hH'⟩
  · rw [ifn hp, ifn hp]
    constructor
    · rintro ⟨⟨_, _, h, _⟩, _⟩; exact absurd rfl h
    · rintro ⟨_, _, _, h, _⟩; exact absurd h hp

end VG.Proof.RsaPss.AArch64

end

end

/-! ### `RsaPss.AArch64.FixedSaltSelect`, which only this module used -/

section

/-! ### `RsaPss.AArch64.FixedSaltHash`, which only this module used -/

section

/-! Hashing the fixed-length salt after all encoding checks. -/

@[expose] public section
namespace VG.Proof.RsaPss.AArch64.FixedSalt
open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)

theorem fixed_msg_y {H : Hash} (hH : HashOK H) {u : State} {S : Addr}
    {W : Nat → Byte} {mH : List Byte} {e db pos i : Nat}
    (hm : mH.length = H.D) (hpos : pos < db) (hdb : db < 1024)
    (he : oEm ≤ e) (hfit : e + db + H.D ≤ oY)
    (hEm : ∀ o, oEm ≤ o → o < oY → u.mem (off S o) = W o) (hi : i < 2048) :
    updL (updL (clr (fun o => u.mem (off S o)) oY 2048) (oY + 8) mH)
      (oY + 8 + H.D)
      ((List.range (db - pos - 1)).map fun j =>
        updL (clr (fun o => u.mem (off S o)) oY 2048) (oY + 8) mH (e + db - (db - pos - 1) + j))
      (oY + i) = (msgV mH (fun j => W (e + j)) db pos).getD i 0 := by
  have hDN := hH.sizes.DN
  have hN := hH.N_le
  have hD := hH.sizes.D0
  unfold msgV
  rw [getD_app, getD_app]
  simp only [List.length_append, RsaPss.zeros_length, hm]
  by_cases h1 : i < 8
  · simp (disch := omega) only [updL, clr, ↓ite_eq_left, ↓ite_eq_right]
    exact (RsaPss.zeros_getD _ _).symm
  by_cases h2 : i < 8 + H.D
  · simp (disch := omega) only [updL, ↓ite_eq_left, ↓ite_eq_right]
    rw [show oY + i - (oY + 8) = i - 8 by omega]
  by_cases h3 : i - (8 + H.D) < db - pos - 1
  · simp (disch := omega) only [updL, clr, ↓ite_eq_left, ↓ite_eq_right, hm, List.length_map, List.length_range]
    rw [show oY + i - (oY + 8 + H.D) = i - (8 + H.D) by omega]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h3, Option.map_some, Option.getD_some]
    simp (disch := omega) only [↓ite_eq_right]
    rw [hEm _ (by omega) (by omega)]
    congr 1
    omega
  · simp (disch := omega) only [updL, clr, ↓ite_eq_left, ↓ite_eq_right, hm, List.length_map, List.length_range]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_none (by rw [List.length_range]; omega)]
    rfl

variable {H : Hash} (hH : HashOK H)
include hH in
theorem finish_ok {u : State} {F S : Addr} (L : Lay u F S) {W : Nat → Byte} {e db pos : Nat} {acc : BitVec 64}
    {dig : Addr} (hEm : ∀ o, oEm ≤ o → o < oY → u.mem (off S o) = W o) (he : oEm ≤ e)
    (hfit : e + db + H.D ≤ oY) (hpos : pos < db) (hdb : db < 1024)
    (h19 : u.gpr .x19 = off S oSt) (h21 : u.gpr .x21 = off S oDig) (h24 : u.gpr .x24 = off S e)
    (h25 : u.gpr .x25 = BitVec.ofNat 64 db) (h26 : u.gpr .x26 = acc)
    (hS : u.mem.readW (off F sSaltLen) 64 = BitVec.ofNat 64 (db - pos - 1)) (hdg : u.mem.readW (off F sDig) 64 = dig)
    (hr : ∀ j < H.D, InRegions (u.rd ++ u.wr) (dig + BitVec.ofNat 64 j) 1)
    (hd : Region.Disjoint ⟨dig, H.D⟩ ⟨S, oRsa⟩) {f : MdFns} {dn : String} (hT : HT H dn f F u.mem u.syms)
    (hdo : DigOK H.P) :
    WP isa (Impl.RsaPss.AArch64.FixedSalt.finish f H) u
      fun u' => u'.sp = u.sp ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
        (∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x24, .x25], u'.gpr r = u.gpr r) ∧
        (∀ r ∈ preservedV, (u'.v r).extractLsb' 0 64 = (u.v r).extractLsb' 0 64) ∧
        Frame (mgfWr F S) u.mem u'.mem ∧
        u'.gpr .x0 = resV acc (hH.SH.H.hash (msgV (Spec.Rsa.bytesAt u.mem dig H.D) (fun i => W (e + i)) db pos))
          W e db H.D := by
  have hD := hH.sizes.D0
  have hDN := hH.sizes.DN
  have hN := hH.N_le
  have hL := hH.L
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have c1 : oEm = 2560 := rfl
  have c2 : oY = 3584 := rfl
  have c3 : oDig = 2304 := rfl
  have c6 : oRsa = 8192 := rfl
  unfold Impl.RsaPss.AArch64.FixedSalt.finish seqs seqs seqs seqs seqs
  -- `Y` cleared.
  refine WP.seq (WP.mono_syms (clearY_ok L (V := fun o => u.mem (off S o)) (fun _ _ => rfl)) fun u1 ⟨k1, f1, R1⟩ sy1 => ?_)
  obtain L1 := L.congr k1.sp k1.wr (k1.get .x20)
  obtain hm1 : Spec.Rsa.bytesAt u1.mem dig H.D = Spec.Rsa.bytesAt u.mem dig H.D :=
    bytes_apartL f1 (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) (by omega_using [hDN, hN])
  -- `mHash`.
  refine WP.seq (WP.mono_syms (copyDigest_ok hH L1 R1 (dig := dig) (by rw [slot_keep f1 (L.slotSd (by decide)), hdg])
    (by rw [k1.rd, k1.wr]; exact hr) hd) fun u2 ⟨k2, f2, R2⟩ sy2 => ?_)
  rw [hm1] at R2
  generalize hmH : Spec.Rsa.bytesAt u.mem dig H.D = mH at R2
  obtain hml : mH.length = H.D := by rw [← hmH, VG.Proof.RsaPkcs1Sig.bytesAt_length]
  obtain L2 := L1.congr k2.sp k2.wr (k2.get .x20)
  obtain F3 : Frame [⟨S, oRsa⟩] u.mem u2.mem := f1.trans f2
  refine WP.seq (WP.mono_syms (copySalt_ok hH L2 R2 (e := e) (db := db) (sl := db - pos - 1)
    he (by omega_using [hfit]) (by omega_using []) hdb
    (by rw [k2.get .x24, k1.get .x24, h24])
    (by rw [k2.get .x25, k1.get .x25, h25])
    (by rw [slot_keep F3 (L.slotSd (by decide)), hS])) fun u4 ⟨k4, f4, R4⟩ sy4 => ?_)
  obtain L4 := L2.congr k4.sp k4.wr (k4.get .x20)
  -- `nbm`.
  refine WP.seq (WP.mono_syms (signLen_ok hH L4 (sl := db - pos - 1)
    (by rw [slot_keep (F3.trans f4) (L.slotSd (by decide)), hS]) (by omega_using [hdb]))
    fun u5 ⟨k5, x22₅, m5⟩ sy5 => ?_)
  obtain L5 := L4.congr k5.sp k5.wr (k5.get .x20)
  obtain R5 := R4.frame (m' := u5.mem) (rs := [slotR F sNb]) (by rw [m5]; exact frame_slot _ F sNb _)
    (L.slotS (by decide))
  -- `Hash(M')`.
  generalize hmsg : msgV mH (fun i => W (e + i)) db pos = msg
  obtain hmsgl : msg.length = 8 + H.D + (db - pos - 1) := by rw [← hmsg, msgV_length, hml]
  obtain hnb1 := Nat.lt_div_mul_add (a := 8 + H.D + (db - pos - 1) + H.P.L) (b := H.P.B) hB0
  obtain hnb2 := Nat.div_mul_le_self (8 + H.D + (db - pos - 1) + H.P.L) H.P.B
  obtain hnbB : ((8 + H.D + (db - pos - 1) + H.P.L) / H.P.B + 1) * H.P.B =
      (8 + H.D + (db - pos - 1) + H.P.L) / H.P.B * H.P.B + H.P.B := Nat.succ_mul _ _
  obtain g5 : ∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x24, .x25, .x26], u5.gpr r = u.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [k5.get _ (by decide), k4.get _ (by decide), k2.get _ (by decide),
        k1.get _ (by decide)]
  obtain F5 : Frame (mgfWr F S) u.mem u5.mem :=
    (F3.trans f4).mono (by simp) |>.trans (by rw [m5]; exact (frame_slot _ F sNb _).mono (by simp))
  obtain hT5 : HT H dn f F u5.mem u5.syms := by rw [sy5, sy4, sy2, sy1]; exact hT.stepW L F5
  refine WP.seq (WP.mono (ctHash_ok hH L5 R5 (msg := msg) (nbm := (8 + H.D + (db - pos - 1) + H.P.L) / H.P.B + 1)
    (by rw [g5 .x19 (by decide), h19]) (by rw [g5 .x21 (by decide), h21])
    (by rw [x22₅, hmsgl]) (by rw [m5, Mem.readW_writeW_self64]) (by rw [hmsgl, hnbB]; omega_using [hnb1])
    (by rw [hnbB]; omega_using [he, hfit, hpos, hdb, hD, hDN, hN, hL, hB0, hBl, c2, hnb1, hnb2, hnbB]) (fun i hi => ?_) hT5 hdo) fun u6 ⟨O6, d6⟩ => ?_)
  · rw [← hmsg]
    exact fixed_msg_y hH hml hpos hdb he hfit hEm (by rw [hnbB] at hi; omega_using [he, hfit, hpos, hdb, hD, hDN, hN, hL, hB0, hBl, c1, c2, hnb1, hnb2, hnbB, hi])
  obtain L6 := L5.congr O6.sp O6.wr (O6.cs .x20 (by decide))
  -- The comparison.
  refine WP.mono (cmpH_ok hH L6 (V := fun o => u6.mem (off S o)) (fun _ _ => rfl) (e := e) (db := db) (acc := acc)
    hfit (by rw [O6.cs .x21 (by decide), g5 .x21 (by decide), h21])
    (by rw [O6.cs .x24 (by decide), g5 .x24 (by decide), h24])
    (by rw [O6.cs .x25 (by decide), g5 .x25 (by decide), h25])
    (by rw [O6.cs .x26 (by decide), g5 .x26 (by decide), h26])) fun u7 ⟨O7, x0₇⟩ => ?_
  refine ⟨by rw [O7.sp, O6.sp, k5.sp, k4.sp, k2.sp, k1.sp], by rw [O7.rd, O6.rd, k5.rd, k4.rd, k2.rd, k1.rd],
    by rw [O7.wr, O6.wr, k5.wr, k4.wr, k2.wr, k1.wr], fun r hr => ?_,
    fun r hr => by rw [O7.vcs r hr, O6.vec r hr, k5.vcs r hr, k4.vcs r hr, k2.vcs r hr, k1.vcs r hr],
    by rw [O7.mem]; exact F5.trans (O6.fr.mono (by simp)), ?_⟩
  · have hr' := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [O7.get r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      O6.cs r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      g5 r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
  · rw [x0₇, resV]
    congr 2
    refine congrArg (acc ||| ·) (orF_congr fun i hi => ?_)
    rw [← off_add, byte_of_bytesAt d6 hi, O6.em _ (by omega_using [he]) (by omega_using [hfit, hi])]
    simp (disch := omega_using [hfit, hi]) only [updL, clr, ↓ite_eq_right]
    rw [hEm _ (by omega_using [he]) (by omega_using [hfit, hi])]


end VG.Proof.RsaPss.AArch64.FixedSalt

end

end


/-! A known salt length changes only the hash of already rejected encodings. -/

@[expose] public section
namespace VG.Proof.RsaPss.AArch64.FixedSalt
open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.MlKem.AArch64 (Only wp_nil eval_zero)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_ldrSp)

theorem resV_nonzero {acc : BitVec 64} (ha : acc.toNat < 2^63) (hn : acc ≠ 0)
    (h : List Byte) (W : Nat → Byte) (e db D : Nat) : resV acc h W e db D = 0 := by
  unfold resV
  rw [top_sub _ (lt_or ha (orF_lt _ (fun i => lt_xor (lt_byte _ (by decide)) (lt_byte _ (by decide))) D))]
  rw [ite_eq_right (fun he => hn (or_eq_zero64 _ _ |>.mp he).1)]
  rfl

variable {H : Hash} (hH : HashOK H)
include hH in
theorem select_ok {u : State} {F S : Addr} (L : Lay u F S) {W : Nat → Byte} {e db pos : Nat} {acc : BitVec 64}
    {dig : Addr} (hEm : ∀ o, oEm ≤ o → o < oY → u.mem (off S o) = W o) (he : oEm ≤ e)
    (hfit : e + db + H.D ≤ oY) (hpos : pos < db) (hdb : db < 1024)
    (h19 : u.gpr .x19 = off S oSt) (h21 : u.gpr .x21 = off S oDig) (h24 : u.gpr .x24 = off S e)
    (h25 : u.gpr .x25 = BitVec.ofNat 64 db) (h26 : u.gpr .x26 = acc)
    (hP : u.mem.readW (off F sPos) 64 = BitVec.ofNat 64 pos) (hdg : u.mem.readW (off F sDig) 64 = dig)
    (hr : ∀ j < H.D, InRegions (u.rd ++ u.wr) (dig + BitVec.ofNat 64 j) 1)
    (hd : Region.Disjoint ⟨dig, H.D⟩ ⟨S, oRsa⟩)
    {any : BitVec 64} {sl : Nat}
    (hAny : u.mem.readW (off F sAny) 64 = any)
    (hSl : u.mem.readW (off F sSaltLen) 64 = BitVec.ofNat 64 sl)
    (hFits : any = 0 → sl < db)
    (hMatch : any = 0 → acc = 0 → sl = db - pos - 1)
    (hAcc : acc.toNat < 2^63) {f : MdFns} {dn : String} (hT : HT H dn f F u.mem u.syms) (hdo : DigOK H.P) :
    WP isa (Impl.RsaPss.AArch64.FixedSalt.select f H) u
      fun u' => u'.sp = u.sp ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
        (∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x24, .x25], u'.gpr r = u.gpr r) ∧
        (∀ r ∈ preservedV, (u'.v r).extractLsb' 0 64 = (u.v r).extractLsb' 0 64) ∧
        Frame (mgfWr F S) u.mem u'.mem ∧
        u'.gpr .x0 = resV acc (hH.SH.H.hash (msgV (Spec.Rsa.bytesAt u.mem dig H.D) (fun i => W (e + i)) db pos))
          W e db H.D := by
  unfold Impl.RsaPss.AArch64.FixedSalt.select
  refine WP.seq (WP.of_syms (wp_ldrSp (by decide) (ld_slot L (by decide)) fun v O e9 => wp_nil fun sy => ?_))
  obtain hTv : HT H dn f F v.mem v.syms := by rw [sy, O.mem]; exact hT
  obtain Lv := L.congr O.sp O.wr (O.get .x20)
  obtain h9 : v.gpr .x9 = any := by rw [e9, L.sp, hAny]
  obtain hEmv : ∀ o, oEm ≤ o → o < oY → v.mem (off S o) = W o := by rw [O.mem]; exact hEm
  obtain h19v : v.gpr .x19 = off S oSt := by rw [O.get .x19, h19]
  obtain h21v : v.gpr .x21 = off S oDig := by rw [O.get .x21, h21]
  obtain h24v : v.gpr .x24 = off S e := by rw [O.get .x24, h24]
  obtain h25v : v.gpr .x25 = BitVec.ofNat 64 db := by rw [O.get .x25, h25]
  obtain h26v : v.gpr .x26 = acc := by rw [O.get .x26, h26]
  obtain hdgv : v.mem.readW (off F sDig) 64 = dig := by rw [O.mem, hdg]
  obtain hrv : ∀ j < H.D, InRegions (v.rd ++ v.wr) (dig + BitVec.ofNat 64 j) 1 := by
    rw [O.rd, O.wr]; exact hr
  refine WP.ite _ (eval_zero _ _) (fun ht => ?_) (fun hf => ?_)
  · have ha : any = 0 := by rw [h9] at ht; exact beq_iff_eq.mp ht
    obtain hslt := hFits ha
    obtain hp' : db - sl - 1 < db := by omega_using [hpos]
    obtain hrev : db - (db - sl - 1) - 1 = sl := by omega_using [hslt]
    refine WP.mono (finish_ok hH Lv hEmv he hfit hp' hdb h19v h21v h24v h25v h26v
      (by rw [O.mem, hrev, hSl]) hdgv hrv hd hTv hdo) fun t ⟨sp, rd, wr, cs, vs, fr, result⟩ => ?_
    refine ⟨sp.trans O.sp, rd.trans O.rd, wr.trans O.wr, ?_, ?_, O.mem ▸ fr, ?_⟩
    · intro r hr
      rw [cs r hr, O.get r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
    · intro r hr; rw [vs r hr, O.vcs r hr]
    · rw [result, O.mem]
      by_cases hz : acc = 0
      · have heq : db - sl - 1 = pos := by have := hMatch ha hz; omega_using [hpos, this]
        rw [heq]
      · rw [resV_nonzero hAcc hz, resV_nonzero hAcc hz]
  · refine WP.mono (b2_ok hH Lv hEmv he hfit hpos hdb h19v h21v h24v h25v h26v
      (by rw [O.mem, hP]) hdgv hrv hd hTv hdo) fun t ⟨sp, rd, wr, cs, vs, fr, result⟩ => ?_
    refine ⟨sp.trans O.sp, rd.trans O.rd, wr.trans O.wr, ?_, ?_, O.mem ▸ fr, ?_⟩
    · intro r hr
      rw [cs r hr, O.get r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
    · intro r hr; rw [vs r hr, O.vcs r hr]
    · simpa only [O.mem] using result

end VG.Proof.RsaPss.AArch64.FixedSalt

end

end


/-!
# EMSA-PSS's check of an encoding on AArch64: correctness after the prologue

The encoding copied to `EM` (`copyIn_okC`); after the checks of the lengths,
verification's checks of `EM` (`check_ok`): `x0` is 1 exactly when the
encoding is consistent with the digest (`EncOk`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Chk

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil wp_movz wp_addImm)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_mov)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.RsaPss (EncOk)
open VG.Proof.RsaPss.AArch64 (off off_add Lay Rep mgfWr slotR slot_keep updL b1_ok B1 wct mkB nz nz_lt resV msgV
  acc0V acc1V vlogic copyIn_ok bytes_apartL)
open VG.Proof.RsaPss.AArch64.Sgn (fb kR frame_sub frame_sub0 below_sub)

/-- What `chkK.post` asks of `x0`: the check with the hash function `Hs` (of
digests of `D` bytes) and MGF1's `Gs`. -/
def chkOut (D : Nat) (Hs Gs : Spec.Mgf1.Hash) (s : State) : Bool :=
  Spec.RsaPss.verifyEncoding Hs Gs (Spec.Rsa.bytesAt s.mem (s.gpr .x0) D)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat) (s.gpr .x3).toNat
    (Spec.RsaPss.expectedSaltLen (s.gpr .x4) ((s.gpr .x5).setWidth 32))

/-- The encoding, as the entry state gives it. -/
abbrev emB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat

/-- In the frame: the slots and the callee-saved registers' values. -/
structure MidC (s t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  v : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  fr : FrC s t.mem

theorem AtC.toMid {s u : State} (h : AtC s u) : MidC s u := ⟨h.sp, h.rd, h.wr, h.v, h.fr⟩

/-- `AtC` after code that writes registers other than ours, and nothing but
`EM` in memory. -/
theorem AtC.only {s u u' : State} (h : AtC s u) {rs : List Reg} (o : Only rs u u')
    (hr : ∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x1], r ∉ rs := by decide) : AtC s u' where
  sp := o.sp.trans h.sp
  rd := o.rd.trans h.rd
  wr := o.wr.trans h.wr
  x19 := (o.gpr .x19 (hr _ (by simp))).trans h.x19
  x20 := (o.gpr .x20 (hr _ (by simp))).trans h.x20
  x21 := (o.gpr .x21 (hr _ (by simp))).trans h.x21
  x23 := (o.gpr .x23 (hr _ (by simp))).trans h.x23
  x1 := (o.gpr .x1 (hr _ (by simp))).trans h.x1
  v := fun r hr' => (o.vcs r hr').trans (h.v r hr')
  mem := o.mem ▸ h.mem
  fr := o.mem ▸ h.fr
  lo := o.mem ▸ h.lo
  c := o.mem ▸ h.c

/-- `AtCT` after code that writes registers other than ours. -/
theorem AtCT.only {s u u' : State} (h : AtCT s u) {rs : List Reg} (o : Only rs u u') (hsy : u'.syms = u.syms)
    (hr : ∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x1], r ∉ rs := by decide) : AtCT s u' :=
  ⟨h.e.only o hr, o.mem ▸ h.wm, o.mem ▸ h.wi, o.mem ▸ h.wc, o.mem ▸ h.wd, hsy.trans h.sy⟩

/-- Our part of the working space. -/
theorem rsa_sub {D : Nat} {tsH tsG : List FnTable} {s : State} (hp : PreC D tsH tsG s) :
    Region.Sub ⟨s.gpr .x6, oRsa⟩ (sR s) := rsa_subC hp

/-- The 16 bytes below the frame, in the stack. -/
theorem below16_sub (s : State) : Region.Sub (below (fb s) 16) (kR 288 s) := fun x h =>
  below_sub 288 s x (Offset.sub_below (fb s) (a := 16) (n := 16) (b := 288) (m := 288) (by decide) (by decide) x h)

/-- Our working space and the frame, laid out. -/
theorem lay_of {D : Nat} {tsH tsG : List FnTable} {s w : State} (hp : PreC D tsH tsG s) (hsp : w.sp = fb s) (h20 : w.gpr .x20 = s.gpr .x6)
    (hwr : w.wr = ⟨fb s, frameBytes⟩ :: s.wr) : Lay w (fb s) (s.gpr .x6) := by
  obtain hfb := fb_toNat hp
  have := s.sp.isLt
  have hws := hp.ws
  have hhs := hp.hs
  exact {
    sp := hsp
    x20 := h20
    fw := by rw [hwr]; exact List.mem_cons_self
    sw := ⟨sR s, by rw [hwr, hp.hwr]; simp, ⟨rfl, show oRsa ≤ (s.gpr .x7).toNat * 8 by unfold oRsa Proof.RsaPss.encScratch at *; omega_using [hhs]⟩⟩
    Fw := by omega_using [hfb]
    Sw := by unfold oRsa Proof.RsaPss.encScratch at *; omega_using [hws, hhs]
    dFS := (hp.ks.sub_left (frame_sub0 288 s)).sub_right (rsa_sub hp)
    dB := (hp.ks.sub_left (below16_sub s)).sub_right (rsa_sub hp) }

/-- What the checks write keeps `FrC`. -/
theorem fr_mgf {D : Nat} {tsH tsG : List FnTable} {s : State} (hp : PreC D tsH tsG s) {m m' : Mem} (h : FrC s m)
    (hf : Frame (mgfWr (fb s) (s.gpr .x6) ++ [slotR (fb s) sPos]) m m') : FrC s m' := by
  refine h.frame hf (fun r hr => ?_) (fun r hr => ?_) <;>
  · simp only [mgfWr, slotR, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hp.ks.sub_left (frame_sub 288 s (by decide))).sub_right (rsa_sub hp)
    · exact Offset.disjoint_below _ (by omega_using [])
    · exact Offset.disjoint _ (by decide) (by decide) (by decide)
    · exact Offset.disjoint _ (by decide) (by decide) (by decide)
    · exact Offset.disjoint_below _ (by rw [mgfFrame_eq]; omega_using [])
    · exact Offset.disjoint _ (by decide) (by decide) (by decide)

/-- `AtC` after code that writes registers other than ours, and memory only
in our working space. -/
theorem AtC.keep {D : Nat} {tsH tsG : List FnTable} {s u u' : State} (hp : PreC D tsH tsG s) (h : AtC s u) {rs : List Reg} (k : Keep rs u u')
    (hf : Frame [⟨s.gpr .x6, oRsa⟩] u.mem u'.mem)
    (hr : ∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x1], r ∉ rs := by decide) : AtC s u' := by
  obtain hd : ∀ {d n : Nat}, d + n ≤ frameBytes →
      ∀ r ∈ [(⟨s.gpr .x6, oRsa⟩ : Region)], Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, n⟩ r := fun hdn r hr' => by
    rw [List.mem_singleton.mp hr']
    exact (hp.ks.sub_left (frame_sub 288 s hdn)).sub_right (rsa_sub hp)
  exact {
    sp := k.sp.trans h.sp
    rd := k.rd.trans h.rd
    wr := k.wr.trans h.wr
    x19 := (k.gpr .x19 (hr _ (by simp))).trans h.x19
    x20 := (k.gpr .x20 (hr _ (by simp))).trans h.x20
    x21 := (k.gpr .x21 (hr _ (by simp))).trans h.x21
    x23 := (k.gpr .x23 (hr _ (by simp))).trans h.x23
    x1 := (k.gpr .x1 (hr _ (by simp))).trans h.x1
    v := fun r hr' => (k.vcs r hr').trans (h.v r hr')
    mem := h.mem.trans (hf.mono (by simp))
    fr := h.fr.frame hf (hd (by decide)) (hd (by decide))
    lo := by rw [slot_keep (d := sLo) hf (hd (by decide))]; exact h.lo
    c := by rw [slot_keep (d := sC) hf (hd (by decide))]; exact h.c }

/-- The encoding copied to `EM`. -/
theorem copyIn_okC {D : Nat} {tsH tsG : List FnTable} {s u : State} (hp : PreC D tsH tsG s) (hu : AtC s u) :
    WP isa copyIn u fun t => AtC s t ∧
      (∀ i < (s.gpr .x2).toNat, t.mem (off (s.gpr .x6) (oEm + i)) = (emB s).getD i 0) ∧
      Frame [⟨s.gpr .x6, oRsa⟩] u.mem t.mem := by
  obtain hk1 := hp.k1; have hk2 := hp.k2
  have hwe := hp.we
  obtain L := lay_of hp hu.sp hu.x20 hu.wr
  unfold copyIn
  refine WP.seq (wp_mov fun u₁ o₁ e₁ => wp_addImm (by decide) fun u₂ o₂ e₂ => wp_mov fun u₃ o₃ e₃ => wp_nil ?_)
  obtain O : Only [.x11, .x14, .x12] u u₃ := (o₁.trans (o₂.trans o₃)).mono
  obtain L₃ := L.congr O.sp O.wr (O.get .x20)
  obtain hu₃ := hu.only O
  refine WP.mono (copyIn_ok L₃ (V := fun o => u₃.mem (off (s.gpr .x6) o)) (fun _ _ => rfl)
    (q := s.gpr .x1) (o := oEm) (n := (s.gpr .x2).toNat) (by omega_using [hk1]) (by unfold oEm oRsa; omega_using [hk2])
    (by rw [o₃.get .x14, e₂, o₁.get .x20, hu.x20])
    (by rw [o₃.get .x11, o₂.get .x11, e₁, hu.x1])
    (by rw [e₃, o₂.get .x23, o₁.get .x23, hu.x23, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (fun j hj => by
      rw [O.rd, O.wr, hu.rd, hp.hrd]
      exact ⟨emR s, by simp, Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩)
    (hp.es.sub_right (rsa_sub hp))) fun t ⟨K, F, R⟩ => ⟨hu₃.keep hp K F, fun i hi => ?_, by rw [← O.mem]; exact F⟩
  obtain hb : Spec.Rsa.bytesAt u₃.mem (s.gpr .x1) (s.gpr .x2).toNat = emB s :=
    bytes_apartL hu₃.mem (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hp.ke.sub_left (frame_sub0 288 s)).symm
      · exact hp.es.sub_right (rsa_sub hp)) (by omega_using [])
  rw [R (oEm + i) (by unfold oEm oRsa; omega_using [hk2, hi])]
  simp only [updL]
  rw [ite_eq_left ⟨by omega_using [], by rw [VG.Proof.RsaPkcs1Sig.bytesAt_length]; omega_using [hi]⟩, Nat.add_sub_cancel_left, hb]

/-- The slots of the table of `MdHash`, from the table at the entry. -/
theorem ht_of {H : Hash} {dn : String} {f : MdFns} {G : Impl.Pbkdf2.Md.AArch64.Stream}
    {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns} {s w : State} (ht : TabsAt H dn f G g (stackArg s 0) (stackArg s 1) s)
    (hw : AtCT s w) : HT H dn f (fb s) w.mem w.syms where
  wi := hw.wi.trans (ht.h0.trans (by rw [hw.sy]))
  wc := hw.wc.trans (ht.h3.trans (by rw [hw.sy]))
  wd := hw.wd.trans (ht.h4.trans (by rw [hw.sy]))
  fi := by rw [hw.sy]; exact ht.fi
  fc := by rw [hw.sy]; exact ht.fc
  fd := by rw [hw.sy]; exact ht.fd

/-- MGF1's working space, in ours. -/
theorem mgfScr_sub {D : Nat} {tsH tsG : List FnTable} {s : State} (hp : PreC D tsH tsG s) :
    Region.Sub ⟨off (s.gpr .x6) mgfOff, 8192⟩ (sR s) :=
  Offset.sub_base _ (by have := hp.hs; unfold mgfOff Proof.RsaPss.encScratch at *; omega_using [this])

/-- Where MGF1 works, and the table of `MdHash`, from the table at the entry. -/
theorem env_of {D : Nat} {tsH tsG : List FnTable} {H : Hash} {dn : String} {f : MdFns}
    {G : Impl.Pbkdf2.Md.AArch64.Stream} {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns} {s w : State}
    (hp : PreC D tsH tsG s) (ht : TabsAt H dn f G g (stackArg s 0) (stackArg s 1) s) (hw : AtCT s w) :
    Env G g w (fb s) (s.gpr .x6) (stackArg s 1) := by
  obtain hfb := fb_toNat hp
  have hsp1 := hp.sp1
  have hwtG := hp.wtG
  have hws := hp.ws
  have hhs := hp.hs
  obtain hS := mgfScr_sub hp
  obtain kG : ∀ {R : Region}, R.Sub (kR 288 s) → Region.Disjoint ⟨stackArg s 1, 88⟩ R := fun hR =>
    (hp.ktG.sub_left hR).symm
  obtain sG : ∀ {R : Region}, R.Sub (sR s) → Region.Disjoint ⟨stackArg s 1, 88⟩ R := fun hR =>
    (hp.stG.sub_left hR).symm
  obtain hd : ∀ r ∈ mgfWr (fb s) (s.gpr .x6) ++ [⟨off (s.gpr .x6) mgfOff, 8192⟩, slotR (fb s) sPos],
      Region.Disjoint ⟨stackArg s 1, 88⟩ r := by
    intro r hr
    simp only [mgfWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact sG (rsa_sub hp)
    · exact kG (below16_sub s)
    · exact kG (frame_sub 288 s (by decide))
    · exact kG (frame_sub 288 s (by decide))
    · rw [mgfFrame_eq]; exact (hp.ktG.sub_left (below_sub 288 s)).symm
    · exact sG hS
    · exact kG (frame_sub 288 s (by decide))
  obtain hd0 : ∀ r ∈ [(⟨fb s, frameBytes⟩ : Region), ⟨s.gpr .x6, oRsa⟩], Region.Disjoint ⟨stackArg s 1, 88⟩ r :=
    fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact kG (frame_sub0 288 s)
      · exact sG (rsa_sub hp)
  obtain hin : ∀ d, d + 8 ≤ 88 → InRegions (w.rd ++ w.wr) (off (stackArg s 1) d) 8 := fun d hd' => by
    rw [hw.e.rd, hp.hrd]
    exact ⟨tGR s, by simp, Offset.contains_base _ (k := 88) (by omega_using [hd']) (by omega_using [hd'])⟩
  exact {
    slot := hw.wm
    ok := by rw [hw.sy]; exact ht.gok
    rd := fun j hj => hin (8 * j) (by omega_using [hj])
    rdD := hin 48 (by decide)
    mem := fun m hm => by
      rw [hw.sy]
      exact ⟨TabMem.keep (TabMem.keep ht.gm hw.e.mem hd0) hm hd,
        ((tabG_keep hm hd (by decide)).trans (tabG_keep hw.e.mem hd0 (by decide))).trans ht.gD⟩
    sc := Covers.one (by
      rw [hw.e.wr, hp.hwr]
      exact ⟨sR s, by simp, Offset.contains_base _ (by unfold mgfOff Proof.RsaPss.encScratch at *; omega_using [hhs])
        (by unfold mgfOff; omega_using [])⟩)
    F288 := by rw [mgfFrame_eq]; unfold chkStack Sgn.stk at hsp1; omega_using [hfb, hsp1]
    dStk := by rw [mgfFrame_eq]; exact (hp.ks.sub_left (below_sub 288 s)).sub_right hS
    Sw := by simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; unfold mgfOff Proof.RsaPss.encScratch at *; omega_using [hws, hhs]
    dFw := (hp.ks.sub_left (frame_sub0 288 s)).sub_right hS }

section
variable {H : Hash} (hH : HashOK H) {Gm : Impl.Pbkdf2.Md.AArch64.Stream}
  (hGm : VG.Proof.Pbkdf2.Md.AArch64.Calls.StreamOK Gm) {Hs Gs : Spec.Mgf1.Hash}
  (hHs : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D) (hHv : Proof.Mgf1.Valid Hs)
  (hGh : ∀ x, Gs.hash x = hGm.SH.H.hash x) (hGl : Gs.len = Gm.D)
  (hGv : Proof.Mgf1.Valid Gs) {f : MdFns} {dn : String} (hdo : DigOK H.P) {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns}

include hH hHs hHl hHv hGh hGl hGv hdo in
/-- After the checks of the lengths: `EM` checked, `x0` 1 exactly when the
encoding is consistent. -/
theorem chkMain_ok {tsH tsG : List FnTable} {s u : State} (hp : PreC H.D tsH tsG s)
    (ht : TabsAt H dn f Gm g (stackArg s 0) (stackArg s 1) s) (hu : AtCT s u)
    (hem : ∀ i < (s.gpr .x2).toNat, u.mem (off (s.gpr .x6) (oEm + i)) = (emB s).getD i 0)
    (h9 : u.gpr .x9 = BitVec.ofNat 64 ((s.gpr .x2).toNat - (H.D + 2)))
    (hfit : H.D + 2 ≤ (s.gpr .x2).toNat)
    (hs : anyC s = 0 → (s.gpr .x4).toNat < (s.gpr .x2).toNat - H.D - 1) :
    WP isa (chkMain f H g) u fun t => MidC s t ∧ ∀ b : Bool, (b = true ↔ (0 = 1 → (emB s).getD 0 0 = 0) ∧
      Proof.RsaPss.EncOk₂ Gs Hs (Spec.Rsa.bytesAt s.mem (s.gpr .x0) H.D) ((emB s).drop 0) ((s.gpr .x2).toNat - 0) (zC s)
        (if anyC s = 0 then some (s.gpr .x4).toNat else none)) → t.gpr .x0 = if b then 1#64 else 0#64 := by
  obtain hk1 := hp.k1; have hk2 := hp.k2
  obtain hT0 := ht_of ht hu
  obtain E0 := env_of hp ht hu
  have hu := hu.e
  obtain L₀ := lay_of hp hu.sp hu.x20 hu.wr
  show WP isa (.seq (.block dbRegs) (seqs [.block acc0, mgfXor H g, .block clearTop, posScan, posCheck,
    FixedSalt.select f H])) u _
  refine WP.seq (WP.mono_syms (dbRegs_ok L₀ h9 hu.lo) fun t ⟨O, x25, x24⟩ sy => ?_)
  obtain hT1 : HT H dn f (fb s) t.mem t.syms := by rw [sy, O.mem]; exact hT0
  obtain E1 : Env Gm g t (fb s) (s.gpr .x6) (stackArg s 1) :=
    E0.step L₀ (by rw [O.mem]; exact Frame.refl _ _) O.rd O.wr sy
  obtain ht := hu.only O
  obtain L := lay_of hp ht.sp ht.x20 ht.wr
  generalize hk : (s.gpr .x2).toNat = k at hfit hs x25 hk1 hk2 hem
  obtain hkd : 0 + (k - H.D - 1) + H.D + 1 = k := by omega_using [hfit]
  obtain h25 : t.gpr .x25 = BitVec.ofNat 64 (k - H.D - 1) := by rw [x25]; congr 1; omega_using [hfit]
  obtain h23 : t.gpr .x23 = BitVec.ofNat 64 k := by rw [ht.x23, ← hk, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine (b1_ok hGm hGh hGl hGv (H := H) L (V := fun o => t.mem (off (s.gpr .x6) o)) (fun _ _ => rfl) (k := k)
    (lo := 0) (db := k - H.D - 1) (c := cC s) (any := anyC s) (sv := s.gpr .x4) hkd (by omega_using [hfit]) hk2 (Nat.zero_le 1)
    h23 x24 h25 ht.lo ht.c ht.fr.any ht.fr.sl E1
    (rest := Impl.RsaPss.AArch64.FixedSalt.select f H)
    fun u B => ?_ : WP isa (seqs [.block acc0, mgfXor H g, .block clearTop, posScan, posCheck,
      Impl.RsaPss.AArch64.FixedSalt.select f H]) t _)
  have gu : ∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x24, .x25], u.gpr r = t.gpr r := B.cs
  obtain hslot : ∀ d, d + 8 ≤ frameBytes →
      (d + 8 ≤ sNb ∨ sNb + 8 ≤ d) → (d + 8 ≤ sDone ∨ sDone + 8 ≤ d) →
      (d + 8 ≤ sPos ∨ sPos + 8 ≤ d) →
      u.mem.readW (off (fb s) d) 64 = t.mem.readW (off (fb s) d) 64 := by
    intro d hd hn hf hpos
    apply slot_keep B.fr
    intro r hr
    rcases List.mem_append.mp hr with h | h
    · exact L.slotW hd hn hf r h
    · rw [List.mem_singleton.mp h]
      exact Offset.disjoint _ hpos (by unfold frameBytes at hd; omega_using [hd]) (by decide)
  obtain hTu : HT H dn f (fb s) u.mem u.syms := by
    rw [B.sy]
    exact ⟨(hslot sIniH (by decide) (by decide) (by decide) (by decide)).trans hT1.wi,
      (hslot sCmpH (by decide) (by decide) (by decide) (by decide)).trans hT1.wc,
      (hslot sDigH (by decide) (by decide) (by decide) (by decide)).trans hT1.wd, hT1.fi, hT1.fc, hT1.fd⟩
  obtain hrd : ∀ j < H.D, InRegions (u.rd ++ u.wr) (s.gpr .x0 + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [B.rd, B.wr, ht.rd, hp.hrd]
    exact ⟨dgR H.D s, by simp, Offset.contains_base _ (by omega_using [hj]) (by have := hp.wd; omega_using [hj, this])⟩
  refine WP.mono (VG.Proof.RsaPss.AArch64.FixedSalt.select_ok hH (L.congr B.sp B.wr (gu .x20 (by decide)))
    (W := wct (fun o => t.mem (off (s.gpr .x6) o)) (mkB Gs H.D (fun o => t.mem (off (s.gpr .x6) o)) (oEm + 0)
      (k - H.D - 1)) (oEm + 0) (k - H.D - 1) (cC s)) (e := oEm + 0) (db := k - H.D - 1)
    B.em (by omega_using []) (by unfold oEm oY; omega_using [hfit, hk2])
    (nz_lt (by omega_using [hfit])) (by omega_using [hk2]) (by rw [gu .x19 (by decide), ht.x19]) (by rw [gu .x21 (by decide), ht.x21])
    (by rw [gu .x24 (by decide), x24]) (by rw [gu .x25 (by decide), h25]) B.acc B.pos
    (by rw [hslot sDig (by decide) (by decide) (by decide) (by decide)]; exact ht.fr.dig) hrd
    (hp.ds.sub_right (rsa_sub hp))
    (by rw [hslot sAny (by decide) (by decide) (by decide) (by decide)]; exact ht.fr.any)
    (sl := (s.gpr .x4).toNat)
    (by rw [hslot sSaltLen (by decide) (by decide) (by decide) (by decide), ht.fr.sl, BitVec.ofNat_toNat,
      BitVec.setWidth_eq])
    hs
    (by
      intro hany hacc
      obtain heq := (VG.Proof.RsaPss.AArch64.acc1V_eq_zero _ _ _ _ _).mp hacc
      exact (VG.Proof.RsaPss.AArch64.eq_ofNat_iff (by omega_using [hk]) _).mp (heq.2.2.2 hany))
    (by
      obtain hb := VG.Proof.RsaPss.AArch64.acc_lt (fun o => t.mem (off (s.gpr .x6) o)) k 0 (cC s)
        (fun i => wct (fun o => t.mem (off (s.gpr .x6) o))
          (mkB Gs H.D (fun o => t.mem (off (s.gpr .x6) o)) (oEm + 0) (k - H.D - 1))
          (oEm + 0) (k - H.D - 1) (cC s) (oEm + 0 + i))
        (k - H.D - 1) (anyC s) (s.gpr .x4) (fun _ => 0) 0 (by omega_using [hk2])
        (fun h => by have := hs h; omega_using [hk2, this]) (fun _ => by decide)
      simpa [VG.Proof.RsaPss.AArch64.orF] using hb) hTu hdo) fun u' ⟨sp', rd', wr', cs', v', fr', x0'⟩ =>
    ⟨?_, fun b hb => ?_⟩
  · exact ⟨by rw [sp', B.sp, ht.sp], by rw [rd', B.rd, ht.rd], by rw [wr', B.wr, ht.wr],
      fun r hr => by rw [v' r hr, B.v r hr, ht.v r hr],
      fr_mgf hp (fr_mgf hp ht.fr B.fr) (fr'.mono fun r hr => List.mem_append_left _ hr)⟩
  obtain hl : H.D ≤ 2 ^ 64 := by have := hp.wd; omega_using [this]
  obtain hd : ∀ r ∈ mgfWr (fb s) (s.gpr .x6) ++ [slotR (fb s) sPos], Region.Disjoint (dgR H.D s) r := fun r hr => by
    simp only [mgfWr, slotR, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hp.ds.sub_right (rsa_sub hp)
    · exact (hp.kd.sub_left (below16_sub s)).symm
    · exact (hp.kd.sub_left (frame_sub 288 s (by decide))).symm
    · exact (hp.kd.sub_left (frame_sub 288 s (by decide))).symm
    · rw [mgfFrame_eq]; exact (hp.kd.sub_left (below_sub 288 s)).symm
    · exact (hp.kd.sub_left (frame_sub 288 s (by decide))).symm
  obtain hdig : Spec.Rsa.bytesAt u.mem (s.gpr .x0) H.D = Spec.Rsa.bytesAt s.mem (s.gpr .x0) H.D := by
    rw [bytes_apartL B.fr hd hl]
    exact bytes_apartL ht.mem (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hp.kd.sub_left (frame_sub0 288 s)).symm
      · exact hp.ds.sub_right (rsa_sub hp)) hl
  rw [x0', hdig, ← funext hHs]
  refine vlogic hHv hGv hHl (x := emB s) (k := k) (lo := 0) (db := k - H.D - 1) (by rw [VG.Proof.RsaPkcs1Sig.bytesAt_length, hk]) (fun i hi => ?_) hkd
    (by omega_using [hfit]) (Nat.zero_le 1) hk2 (VG.Proof.RsaPkcs1Sig.bytesAt_length _ _ _) rfl (fun h => hs h) ?_
  · show t.mem (off (s.gpr .x6) (oEm + i)) = _
    rw [O.mem]; exact hem i hi
  exact hb

end

end VG.Proof.RsaPss.AArch64.Chk
