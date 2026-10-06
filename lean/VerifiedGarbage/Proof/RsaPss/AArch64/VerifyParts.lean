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

end VG.Proof.RsaPss.AArch64
