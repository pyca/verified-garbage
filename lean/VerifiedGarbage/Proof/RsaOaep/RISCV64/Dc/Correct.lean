module

-- separate module: it builds in parallel with the constant-time proofs (`CTBase` to `CTLabel`), which
-- `Verified` also needs.
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.MgfT
public import VerifiedGarbage.Proof.MdHashTable.RISCV64.Tables
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.ByLen
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Unmask
public import VerifiedGarbage.Proof.RsaOaep.Decode
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Hash
public import VerifiedGarbage.Proof.Mgf1.Basic
public import VerifiedGarbage.Proof.RsaPss.RISCV64.Pre
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.RsaOaep.Scan
import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Encode
import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Priv
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Main
import VerifiedGarbage.Proof.RsaPss.RISCV64.Shift

/-! ### `RsaOaep.RISCV64.Dc.Buf`, which this module and modules that import it used -/

section

/-!
# RSAES-OAEP decryption on RISC-V: the buffer

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Dc/Shift.lean`): `clearBuf_ok`, the buffer's 2048
bytes at `oBuf` cleared; `copyT_ok`, `T` copied to its start.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.RISCV64.Dec

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64 VG.Impl.RsaOaep.RISCV64.Dec VG.WriteBytes
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept wp_li wp_addi wp_subi wp_sll wp_nil fill_ok copy_ok)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.RsaOaep.RISCV64 (Base Fits view off off_off offs sc_inR sc_w view_wb sub_k)
open VG.Proof.Mgf1 (ifp ifn)

theorem offs' : oEm = 0 ∧ oSt = 1024 ∧ oDig = 1280 ∧ oBuf = 2560 ∧ oRsa = 8192 := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `bufBase`'s two steps: `scratch + oBuf`. -/
theorem bufBase_eq (p : Addr) : p + BitVec.ofNat 64 2047 + BitVec.ofNat 64 513 = off p oBuf := by
  rw [Offset.add_add]; rfl

section
variable {pc : Bool} {s : State} (P : PreD pc s) {m : Mem} {rc : Nat}
include P

/-- The buffer cleared. -/
theorem clearBuf_ok {t : State} (h : Base (SD s) (VD s rc) (withMem s m) t) :
    WP isa clearBuf t fun t' => Base (SD s) (VD s rc) (withMem s m) t' ∧ Kept [.a1, .t5, .t0] t t' ∧
      ∀ o < oRsa, view t'.mem (Sd s) o = if oBuf ≤ o ∧ o < oBuf + 2048 then 0 else view t.mem (Sd s) o := by
  obtain ⟨hE, hSt, hDg, hB, hRs⟩ := offs'
  have PF : Fits (SD s) (withMem s m) := fits P rfl rfl
  unfold clearBuf bufBase
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_addi (imm := 2047) fun t₁ o₁ e₁ => wp_addi (imm := 513) fun t₂ o₂ e₂ =>
    wp_li (imm := 1) (by decide) fun t₃ o₃ e₃ => wp_sll (sh := 11) (fun t₄ o₄ e₄ =>
    wp_li (imm := 0) (by decide) fun t₅ o₅ e₅ => wp_nil ?_) (by decide))
  have k₅ : Only [.a1, .t5, .t0] t t₅ := (o₁.trans (o₂.trans (o₃.trans (o₄.trans o₅)))).mono
  refine WP.mono (fill_ok (p := off (Sd s) oBuf) (n := 2048) (b := 0) (by decide) (by decide)
    (by rw [o₅.get .a1, o₄.get .a1, o₃.get .a1, e₂, e₁, h.s0]; exact bufBase_eq _)
    (by rw [o₅.get .t5, e₄, e₃]; decide) (by rw [e₅]; rfl)
    (sc_w PF (by rw [k₅.wr, h.wr]) (by omega_using [hB, hRs]))) fun t' ⟨hk, hm⟩ => ?_
  have hK : Kept [.a1, .t5, .t0] t t' := (k₅.keep.trans hk).mono
  have hm' : t'.mem = writeBytes t.mem (off (Sd s) oBuf) (List.replicate 2048 0) := by rw [hm, k₅.mem]
  refine ⟨h.wb PF hK (by rw [List.length_replicate]; omega_using [hB, hRs]) hm', hK, fun o ho => ?_⟩
  rw [hm', view_wb _ _ (by rw [List.length_replicate]; omega_using [hB, hRs]) ho, List.length_replicate]
  split
  · rename_i hc
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, ifp (by omega_using [hc])]; rfl
  · rfl

/-- `T` (`k - 2 D - 1` bytes at `1 + 2 D`) to the buffer. -/
theorem copyT_ok {H : Hash} {D : Nat} (hD : H.D = D) (hD64 : D ≤ 64) (hk : 2 * D + 2 ≤ kk s) {t : State}
    (h : Base (SD s) (VD s rc) (withMem s m) t) :
    WP isa (copyT H) t fun t' => Base (SD s) (VD s rc) (withMem s m) t' ∧ Kept [.t0, .a4, .a1, .a5] t t' ∧
      ∀ o < oRsa, view t'.mem (Sd s) o = if oBuf ≤ o ∧ o < oBuf + (kk s - (2 * D + 1)) then
        view t.mem (Sd s) (1 + 2 * D + (o - oBuf)) else view t.mem (Sd s) o := by
  obtain ⟨hE, hSt, hDg, hB, hRs⟩ := offs'
  have hk2 := P.k2
  have ek : kk s = (s.gpr .a4).toNat := rfl
  have PF : Fits (SD s) (withMem s m) := fits P rfl rfl
  subst hD
  unfold copyT bufBase
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_addi (imm := oEm + 1 + 2 * H.D) (h := by unfold oEm; omega_using [hD64]) fun t₁ o₁ e₁ =>
    wp_addi (imm := 2047) fun t₂ o₂ e₂ => wp_addi (imm := 513) fun t₃ o₃ e₃ =>
    wp_subi (imm := 2 * H.D + 1) (h := by omega_using [hD64]) fun t₄ o₄ e₄ => wp_nil ?_)
  have k₄ : Only [.a4, .a1, .a5] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  have hn : t₄.gpr .a5 = BitVec.ofNat 64 (kk s - (2 * H.D + 1)) := by
    rw [e₄, o₃.get .s1, o₂.get .s1, o₁.get .s1, Base.dk h, sub_k (by omega_using [ek, hk])]
  refine WP.mono (copy_ok (q := off (Sd s) (1 + 2 * H.D)) (p := off (Sd s) oBuf) (n := kk s - (2 * H.D + 1))
    (by omega_using [hk]) (by omega_using [ek]) (by rw [o₄.get .a1, e₃, e₂, o₁.get .s0, h.s0]; exact bufBase_eq _)
    (by rw [o₄.get .a4, o₃.get .a4, o₂.get .a4, e₁, h.s0, hE, Nat.zero_add]) hn
    (fun j hj => by
      rw [k₄.rd, k₄.wr, h.wr]
      show InRegions _ (off (off (Sd s) (1 + 2 * H.D)) j) 1
      rw [off_off]; exact sc_inR PF (by omega_using [hRs, hk2, ek, hj]) _)
    (sc_w PF (by rw [k₄.wr, h.wr]) (by omega_using [hB, hRs, hk2, ek]))
    (fun j hj i hi => by
      show off (off (Sd s) (1 + 2 * H.D)) j ≠ off (off (Sd s) oBuf) i
      rw [off_off, off_off]
      exact Offset.add_ofNat_ne _ (by omega_using [ek, hj]) (by omega_using [hB, hk2, ek, hi]) (by omega_using [hB, hk2, ek, hj]))) fun t' ⟨hk', hm⟩ => ?_
  have hK : Kept [.t0, .a4, .a1, .a5] t t' := (k₄.keep.trans hk').mono
  have hm' : t'.mem = writeBytes t.mem (off (Sd s) oBuf)
      (Spec.Rsa.bytesAt t.mem (off (Sd s) (1 + 2 * H.D)) (kk s - (2 * H.D + 1))) := by rw [hm, k₄.mem]
  refine ⟨h.wb PF hK (by rw [bytesAt_length]; omega_using [hB, hRs, hk2, ek]) hm', hK, fun o ho => ?_⟩
  rw [hm', view_wb _ _ (by rw [bytesAt_length]; omega_using [hB, hRs, hk2, ek]) ho, bytesAt_length]
  split
  · rename_i hc
    simp only [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (show o - oBuf < kk s - (2 * H.D + 1) by omega_using [hc]), Option.map_some, Option.getD_some]
    show t.mem (off (off (Sd s) (1 + 2 * H.D)) (o - oBuf)) = _
    rw [off_off]; rfl
  · rfl

end

end VG.Proof.RsaOaep.RISCV64.Dec

end

end

/-! ### `RsaOaep.RISCV64.Dc.Shift`, which this module and modules that import it used -/

section

/-!
# RSAES-OAEP decryption on RISC-V: the shift

Untrusted: everything here is checked by Lean. As RSASSA-PSS verification's
(`Proof/RsaPss/RISCV64/Shift.lean`), on the buffer at `oBuf`: `shiftPass_ok`,
a pass of the shift on its first `k` bytes, by bit 0 of `s8`, by `s9` bytes
(`passV`); `shift_ok`, the ten passes, by the bits of `idx + 1` (`shV`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.RISCV64.Dec

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64 VG.Impl.RsaOaep.RISCV64.Dec
open VG.Proof.RsaOaep.RISCV64 (Base Fits SC off off_off view view_w8 sc_in sc_inR sc_inW fx)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo wp_li wp_addi wp_subi wp_add wp_sub wp_mov wp_xor wp_and wp_srl
  wp_lbu wp_sb wp_nil)
open VG.Proof.Bignum.RISCV64 (wp_countdown)
open VG.Proof.RsaPss.RISCV64 (passV shV mask_odd sel_byte)
open VG.Proof.Mgf1 (ifp ifn)

section
variable {pc : Bool} {s : State} (P : PreD pc s) {m : Mem} {rc : Nat}
include P

/-- A pass, by bit 0 of `x` (`s8`) and `d` bytes (`s9`). -/
theorem shiftPass_ok {t : State} (h : Base (SD s) (VD s rc) (withMem s m) t)
    {x d : Nat} (h8 : t.gpr .s8 = BitVec.ofNat 64 x) (h9 : t.gpr .s9 = BitVec.ofNat 64 d) (hd : d ≤ 512) :
    WP isa shiftPass t fun t' => Base (SD s) (VD s rc) (withMem s m) t' ∧ Kept [.a1, .a2, .a3, .a4, .a5, .t1, .t2] t t' ∧
      ∀ o < oRsa, view t'.mem (Sd s) o = passV (view t.mem (Sd s)) oBuf (kk s) (x % 2 = 1) d o := by
  have F : Fits (SD s) (withMem s m) := fits P rfl rfl
  have hk2 := P.k2; have hk1 := P.k1
  have ek : kk s = (s.gpr .a4).toNat := rfl
  have hB : oBuf = 2560 := rfl
  have hR : oRsa = 8192 := rfl
  let b := oBuf
  let V := view t.mem (Sd s)
  let bit : Bool := x % 2 = 1
  unfold shiftPass bufBase
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_addi (imm := 2047) fun t₀ o₀ e₀ => wp_addi (imm := 513) fun t₁ o₁ e₁ =>
    wp_add fun t₂ o₂ e₂ => wp_li (imm := 1) (by decide) fun t₃ o₃ e₃ => wp_and fun t₄ o₄ e₄ =>
    wp_li (imm := 0) (by decide) fun t₅ o₅ e₅ => wp_sub fun t₆ o₆ e₆ => wp_mov fun t₇ o₇ e₇ => wp_nil ?_)
  have k₇ : Only [.a1, .a2, .a3, .a4, .a5] t t₇ :=
    (o₀.trans (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans o₇))))))).mono
  have a4 : t₁.gpr .a1 = off (Sd s) b := by
    rw [e₁, e₀, h.s0]; exact bufBase_eq _
  have g6 : t₇.gpr .a3 = if bit then BitVec.allOnes 64 else 0#64 := by
    rw [o₇.get .a3, e₆, e₅, o₅.get .a3, e₄, e₃, o₃.get .s8, o₂.get .s8, o₁.get .s8, o₀.get .s8, h8, mask_odd]
    simp only [bit, decide_eq_true_eq]
  have g7 : t₇.gpr .a5 = BitVec.ofNat 64 (kk s) := by
    rw [e₇, o₆.get .s1, o₅.get .s1, o₄.get .s1, o₃.get .s1, o₂.get .s1, o₁.get .s1, o₀.get .s1, Base.dk h]
    exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm
  refine WP.mono (wp_countdown (cnt := .a5) (N := kk s) (by omega_using [ek]) (by omega_using [hk1, ek])
    (fun i u => Base (SD s) (VD s rc) (withMem s m) u ∧ Kept [.a1, .a2, .a5, .t1, .t2] t₇ u ∧ u.gpr .a1 = off (Sd s) (b + i) ∧
      u.gpr .a2 = off (Sd s) (b + i + d) ∧ ∀ o < oRsa, view u.mem (Sd s) o =
        if b ≤ o ∧ o < b + i then (if bit then V (o + d) else V o) else V o) ?_
    ⟨h.only F k₇, Kept.refl _ _, by rw [o₇.get .a1, o₆.get .a1, o₅.get .a1, o₄.get .a1, o₃.get .a1, o₂.get .a1, a4]; rfl,
      by rw [o₇.get .a2, o₆.get .a2, o₅.get .a2, o₄.get .a2, o₃.get .a2, e₂, a4, o₁.get .s9, o₀.get .s9, h9]
         exact off_off _ _ _,
      fun o _ => by rw [ifn (by omega_using []), k₇.mem]⟩ g7) fun u ⟨bu, ou, _, _, vu⟩ =>
    ⟨bu, (k₇.keep.trans ou).mono, fun o ho => by rw [vu o ho]; rfl⟩
  intro i hi u ⟨bu, ou, u4, u5, vu⟩ _
  simp only [passBody, List.cons_append, List.nil_append]
  refine wp_lbu (a := off (Sd s) (b + i)) (by rw [u4, BitVec.add_zero])
    (by rw [bu.wr]; exact sc_inR F (by omega) _) fun u₁ p₁ f₁ => ?_
  refine wp_lbu (a := off (Sd s) (b + i + d)) (by rw [p₁.get .a2, u5, BitVec.add_zero])
    (by rw [p₁.rd, p₁.wr, bu.wr]; exact sc_inR F (by omega) _) fun u₂ p₂ f₂ => ?_
  refine wp_xor fun u₃ p₃ f₃ => wp_and fun u₄ p₄ f₄ => wp_xor fun u₅ p₅ f₅ => ?_
  have k₅ : Only [.t1, .t2] u u₅ := (p₁.trans (p₂.trans (p₃.trans (p₄.trans p₅)))).mono
  refine wp_sb (a := off (Sd s) (b + i)) (by rw [k₅.get .a1, u4, BitVec.add_zero])
    (by rw [k₅.wr, bu.wr]; exact sc_inW F (by omega)) fun u₆ m₆ => ?_
  refine wp_addi (imm := 1) fun u₇ p₇ f₇ => wp_addi (imm := 1) fun u₈ p₈ f₈ =>
    wp_subi (imm := 1) fun u₉ p₉ f₉ => wp_nil ?_
  have hm0 : u₅.mem = u.mem := k₅.mem
  have hb : (u₅.gpr .t1).setWidth 8 = if bit then V (b + i + d) else V (b + i) := by
    have va : u.mem (off (Sd s) (b + i)) = V (b + i) := by
      have := vu (b + i) (by omega); rw [ifn (by omega_using [])] at this; exact this
    have vb : u₁.mem (off (Sd s) (b + i + d)) = V (b + i + d) := by
      have := vu (b + i + d) (by omega); rw [ifn (by omega_using [])] at this; rw [p₁.mem]; exact this
    rw [f₅, p₄.get .t1, p₃.get .t1, p₂.get .t1, f₁, f₄, f₃, f₂, p₂.get .t1, f₁, va, vb, p₃.get .a3,
      p₂.get .a3, p₁.get .a3, ou.get .a3, g6]
    exact sel_byte _ _ bit
  have q : Kept [.t1, .t2, .a1, .a2, .a5] u u₉ :=
    (k₅.keep.trans (m₆.keep.trans (p₇.keep.trans (p₈.keep.trans p₉.keep)))).mono
  have hm : u₉.mem = u.mem.writeW (off (Sd s) (b + i)) (if bit then V (b + i + d) else V (b + i)) := by
    rw [p₉.mem, p₈.mem, p₇.mem, m₆.mem, hb, hm0]
  refine ⟨⟨bu.keep F q (R := [⟨off (Sd s) (b + i), 1⟩]) (by
      rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (sc_in (by omega))),
    ?_, ?_, ?_, fun o ho => ?_⟩, ?_⟩
  · exact (ou.trans q).mono
  · rw [p₉.get .a1, p₈.get .a1, f₇, m₆.gpr, k₅.get .a1, u4]; exact off_off _ _ _
  · rw [p₉.get .a2, f₈, p₇.get .a2, m₆.gpr, k₅.get .a2, u5]
    show off (off (Sd s) (b + i + d)) 1 = off (Sd s) (b + (i + 1) + d)
    rw [off_off, show b + i + d + 1 = b + (i + 1) + d by omega_using []]
  · rw [hm, view_w8 _ _ (by omega) ho, vu o ho]
    by_cases e : o = b + i
    · subst e
      rw [ifp (show b + i = b + i from rfl), ifp (show b ≤ b + i ∧ b + i < b + (i + 1) from ⟨by omega_using [], by omega_using []⟩)]
    · rw [ifn e]
      by_cases e' : b ≤ o ∧ o < b + i
      · rw [ifp e', ifp (show b ≤ o ∧ o < b + (i + 1) from ⟨e'.1, by omega_using [e']⟩)]
      · rw [ifn e', ifn (show ¬(b ≤ o ∧ o < b + (i + 1)) by omega_using [e, e'])]
  · rw [f₉, p₈.get .a5, p₇.get .a5, m₆.gpr, k₅.get .a5]

/-- The shift: `DB`'s place in `M'` by `pos + 1`, from `pos` in `s8`. -/
theorem shift_ok {t : State} (h : Base (SD s) (VD s rc) (withMem s m) t)
    {pos : Nat} (h6 : t.gpr .s6 = BitVec.ofNat 64 pos) (hp : pos < kk s) :
    WP isa shift t fun t' => Base (SD s) (VD s rc) (withMem s m) t' ∧
      Kept [.a1, .a2, .a3, .a4, .a5, .t1, .t2, .s10, .s8, .s9] t t' ∧
      ∀ o < oRsa, view t'.mem (Sd s) o = shV (view t.mem (Sd s)) oBuf (kk s) (pos + 1) 10 o := by
  have F : Fits (SD s) (withMem s m) := fits P rfl rfl
  have hk2 := P.k2
  have ek : kk s = (s.gpr .a4).toNat := rfl
  unfold shift
  refine WP.seq (wp_addi (imm := 1) fun t₁ o₁ e₁ => wp_li (imm := 1) (by decide) fun t₂ o₂ e₂ =>
    wp_li (imm := 10) (by decide) fun t₃ o₃ e₃ => wp_nil ?_)
  have k₃ : Only [.s8, .s9, .s10] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  let V := view t.mem (Sd s)
  refine WP.mono (wp_countdown (cnt := .s10) (N := 10) (by decide) (by decide)
    (fun j u => Base (SD s) (VD s rc) (withMem s m) u ∧ Kept [.a1, .a2, .a3, .a4, .a5, .t1, .t2, .s10, .s8, .s9] t u ∧
      u.gpr .s8 = BitVec.ofNat 64 ((pos + 1) / 2 ^ j) ∧ u.gpr .s9 = BitVec.ofNat 64 (2 ^ j) ∧
      ∀ o < oRsa, view u.mem (Sd s) o = shV V oBuf (kk s) (pos + 1) j o) ?_
    ⟨h.only F k₃, k₃.keep.mono, by rw [o₃.get .s8, o₂.get .s8, e₁, h6, ← BitVec.ofNat_add, Nat.pow_zero, Nat.div_one],
      by rw [o₃.get .s9, e₂], fun o _ => by rw [k₃.mem]; rfl⟩ (by rw [e₃]))
    fun u ⟨bu, ku, _, _, vu⟩ => ⟨bu, ku, vu⟩
  intro j hj u ⟨bu, ku, u8, u9, vu⟩ _
  have hp9 : 2 ^ j ≤ 512 := by
    have : 2 ^ j ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) (by omega_using [hj])
    exact this
  refine WP.seq (WP.mono (shiftPass_ok P bu u8 u9 hp9) fun u₁ ⟨b₁, k₁, v₁⟩ => ?_)
  refine wp_srl fun u₂ p₂ f₂ => wp_add fun u₃ p₃ f₃ => wp_subi (imm := 1) fun u₄ p₄ f₄ => wp_nil ?_
  have k₄ : Only [.s8, .s9, .s10] u₁ u₄ := (p₂.trans (p₃.trans p₄)).mono
  refine ⟨⟨b₁.only F k₄, (ku.trans (k₁.trans k₄.keep)).mono, ?_, ?_, fun o ho => ?_⟩, ?_⟩
  · rw [p₄.get .s8, p₃.get .s8, f₂, k₁.get .s8, u8, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.pow_one]
    have : (pos + 1) / 2 ^ j < 2 ^ 64 := by
      have := Nat.div_le_self (pos + 1) (2 ^ j); omega_using [hp, ek, this]
    rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt (by have := Nat.div_le_self ((pos + 1) / 2 ^ j) 2; omega_arith)]
  · rw [p₄.get .s9, f₃, p₂.get .s9, k₁.get .s9, u9, ← BitVec.ofNat_add, Nat.pow_succ, Nat.mul_two]
  · rw [k₄.mem, v₁ o ho]
    show passV (view u.mem (Sd s)) _ _ _ _ o = passV (shV V oBuf (kk s) (pos + 1) j) _ _ _ _ o
    unfold passV
    have e : ∀ o' < oRsa, view u.mem (Sd s) o' = shV V oBuf (kk s) (pos + 1) j o' := vu
    by_cases c : oBuf ≤ o ∧ o < oBuf + kk s
    · have hR : oRsa = 8192 := rfl
      have hB : oBuf = 2560 := rfl
      have := P.k2
      rw [ifp c, ifp c, e o ho, e (o + 2 ^ j) (by omega_using [hk2, ek, hp9, c, hR, hB])]
    · rw [ifn c, ifn c, e o ho]
  · rw [f₄, p₃.get .s10, p₂.get .s10, k₁.get .s10]

end

end VG.Proof.RsaOaep.RISCV64.Dec

end

end

/-! ### `RsaOaep.RISCV64.Dc.Scan`, which this module and modules that import it used -/

section

/-!
# RSAES-OAEP decryption on RISC-V: the scan

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Dc/Scan.lean`), register for register: `scan_ok`,
the scan of `T` (`scanS`, its masks from the top bits of `b - 1` and
`(b ⊕ 1) - 1`), then the accumulator ORed with `looking`. It reads our part
of the working space only, and keeps `Base`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.RISCV64.Dec

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64 VG.Impl.RsaOaep.RISCV64.Dec
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only wp_li wp_mov wp_addi wp_subi wp_add wp_sub wp_and wp_or wp_xor wp_srl
  wp_lbu wp_nil)
open VG.Proof.RsaOaep.RISCV64 (Base Fits view off off_off offs sc_inR sub_k)
open VG.Proof.Bignum.RISCV64 (wp_countdown)
open VG.Proof.RsaOaep (scanS zM mk zM_zx zM_zx1)
open VG.Proof.Mgf1 (ifp ifn)

/-! ## A byte's masks -/

/-- `(b - 1) >>> 63`: 1 if `b = 0`, 0 if not. -/
theorem zbit (b : Byte) : (b.setWidth 64 - BitVec.ofNat 64 1) >>> 63 = if b = 0 then 1#64 else 0#64 := by
  have hb := b.isLt
  have e : b = BitVec.ofNat 8 b.toNat := (BitVec.ofNat_toNat _ b).trans (BitVec.setWidth_eq _) |>.symm
  generalize b.toNat = n at hb e
  subst e
  revert n; decide +kernel

/-- `((b ⊕ 1) - 1) >>> 63`: 1 if `b = 1`, 0 if not. -/
theorem obit (b : Byte) : ((b.setWidth 64 ^^^ BitVec.ofNat 64 1) - BitVec.ofNat 64 1) >>> 63 =
    if b = 1 then 1#64 else 0#64 := by
  have hb := b.isLt
  have e : b = BitVec.ofNat 8 b.toNat := (BitVec.ofNat_toNat _ b).trans (BitVec.setWidth_eq _) |>.symm
  generalize b.toNat = n at hb e
  subst e
  revert n; decide +kernel

theorem masks (b : Byte) :
    ((if b = 0 then 1#64 else 0#64) ||| (if b = 1 then 1#64 else 0#64)) - BitVec.ofNat 64 1 =
      (zM (b.setWidth 64) ||| zM (b.setWidth 64 ^^^ 1)) ^^^ BitVec.allOnes 64 ∧
    BitVec.ofNat 64 0 - (if b = 1 then 1#64 else 0#64) = zM (b.setWidth 64 ^^^ 1) ∧
    (if b = 1 then 1#64 else 0#64) - BitVec.ofNat 64 1 = zM (b.setWidth 64 ^^^ 1) ^^^ BitVec.allOnes 64 := by
  rw [zM_zx, zM_zx1]
  by_cases h0 : b = 0
  · subst h0; simp only [mk]; decide
  by_cases h1 : b = 1
  · subst h1; simp only [mk]; decide
  simp only [mk, h0, h1, ite_false]; decide

/-! ## The scan's step -/

/-- The scan's registers after `i` bytes of `f`, at `b`. -/
structure ScanI (f : Nat → Byte) (c₀ : BitVec 64) (b : Addr) (i : Nat) (u : State) : Prop where
  a1 : u.gpr .a1 = off b i
  a3 : u.gpr .a3 = BitVec.ofNat 64 i
  a4 : u.gpr .a4 = (scanS f c₀ i).1
  s6 : u.gpr .s6 = (scanS f c₀ i).2.1
  s5 : u.gpr .s5 = (scanS f c₀ i).2.2

theorem scan_step {f : Nat → Byte} {c₀ : BitVec 64} {b : Addr} {i : Nat} {u u' : State} (I : ScanI f c₀ b i u)
    (z₁ o₁ zo : BitVec 64)
    (hz : z₁ = ((f i).setWidth 64 - BitVec.ofNat 64 1) >>> 63)
    (ho : o₁ = (((f i).setWidth 64 ^^^ BitVec.ofNat 64 1) - BitVec.ofNat 64 1) >>> 63)
    (hzo : zo = (z₁ ||| o₁) - BitVec.ofNat 64 1)
    (h24 : u'.gpr .s5 = u.gpr .s5 ||| (zo &&& u.gpr .a4))
    (h25 : u'.gpr .s6 = u.gpr .s6 ||| ((u.gpr .a3 &&& u.gpr .a4) &&& (BitVec.ofNat 64 0 - o₁)))
    (h7 : u'.gpr .a4 = u.gpr .a4 &&& (o₁ - BitVec.ofNat 64 1))
    (h4 : u'.gpr .a1 = u.gpr .a1 + BitVec.ofNat 64 1) (h6 : u'.gpr .a3 = u.gpr .a3 + BitVec.ofNat 64 1) :
    ScanI f c₀ b (i + 1) u' := by
  obtain ⟨m1, m2, m3⟩ := masks (f i)
  rw [zbit] at hz
  rw [obit] at ho
  subst hz ho hzo
  refine ⟨by rw [h4, I.a1]; exact off_off _ _ _, by rw [h6, I.a3, BitVec.ofNat_add], ?_, ?_, ?_⟩
  · rw [h7, m3, I.a4]; rfl
  · rw [h25, m2, I.s6, I.a3, I.a4]; rfl
  · rw [h24, m1, I.s5, I.a4]; rfl

section
variable {pc : Bool} {s : State} (P : PreD pc s) {m : Mem} {rc : Nat}
include P

/-- The scan of `T` (`k - 2 D - 1` bytes at `1 + 2 D`), then `acc ∨= looking`. -/
theorem scan_ok {H : Hash} {D : Nat} (hD : H.D = D) (hD64 : D ≤ 64) (hk : 2 * D + 2 ≤ kk s)
    {t : State} (h : Base (SD s) (VD s rc) (withMem s m) t) :
    WP isa (scan H) t fun t' => Base (SD s) (VD s rc) (withMem s m) t' ∧ t'.mem = t.mem ∧
      Only [.a1, .a2, .a3, .a4, .s6, .t3, .t1, .t2, .a7, .s5] t t' ∧
      t'.gpr .s5 = (scanS (fun i => view t.mem (Sd s) (1 + 2 * D + i)) (t.gpr .s5) (kk s - (2 * D + 1))).2.2 |||
        (scanS (fun i => view t.mem (Sd s) (1 + 2 * D + i)) (t.gpr .s5) (kk s - (2 * D + 1))).1 ∧
      t'.gpr .s6 = (scanS (fun i => view t.mem (Sd s) (1 + 2 * D + i)) (t.gpr .s5) (kk s - (2 * D + 1))).2.1 := by
  obtain ⟨hE, hSt, hDg, hCt, hRs⟩ := offs
  have hk2 := P.k2
  have ek : kk s = (s.gpr .a4).toNat := rfl
  have PF : Fits (SD s) (withMem s m) := fits P rfl rfl
  subst hD
  unfold scan tArgs
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_addi (imm := oEm + 1 + 2 * H.D) (h := by unfold oEm; omega_using [hD64]) fun t₁ o₁ e₁ =>
    wp_subi (imm := 2 * H.D + 1) (h := by omega_using [hD64]) fun t₂ o₂ e₂ =>
    wp_li (imm := 0) (by decide) fun t₃ o₃ e₃ => wp_li (imm := 0) (by decide) fun t₄ o₄ e₄ =>
    wp_subi (imm := 1) fun t₅ o₅ e₅ => wp_li (imm := 0) (by decide) fun t₆ o₆ e₆ => wp_nil ?_)
  have k₆ : Only [.a1, .a2, .a3, .a4, .s6] t t₆ := (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans o₆))))).mono
  generalize hf : (fun i => view t.mem (Sd s) (1 + 2 * H.D + i)) = f
  have I0 : ScanI f (t.gpr .s5) (off (Sd s) (1 + 2 * H.D)) 0 t₆ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [o₆.get .a1, o₅.get .a1, o₄.get .a1, o₃.get .a1, o₂.get .a1, e₁, h.s0, hE, Nat.zero_add]
      show _ = off (Sd s) (1 + 2 * H.D) + BitVec.ofNat 64 0
      rw [BitVec.add_zero]
    · rw [o₆.get .a3, o₅.get .a3, o₄.get .a3, e₃]
    · rw [o₆.get .a4, e₅, e₄]; rfl
    · rw [e₆]; rfl
    · rw [k₆.get .s5]; rfl
  refine WP.seq (WP.mono (wp_countdown (cnt := .a2) (N := kk s - (2 * H.D + 1)) (by omega_using [ek]) (by omega_using [hk])
    (fun i u => ScanI f (t.gpr .s5) (off (Sd s) (1 + 2 * H.D)) i u ∧
      Only [.t3, .a1, .a2, .a3, .a4, .t1, .t2, .a7, .s5, .s6] t₆ u) ?_
    ⟨I0, Only.refl _ _⟩ (by rw [o₆.get .a2, o₅.get .a2, o₄.get .a2, o₃.get .a2, e₂, o₁.get .s1, Base.dk h,
      sub_k (by omega_using [ek, hk])])) fun u ⟨I, o⟩ => ?_)
  · intro i hi u ⟨I, o⟩ _
    simp only [scanBody, List.cons_append, List.nil_append]
    refine wp_lbu (a := off (Sd s) (1 + 2 * H.D + i)) (by rw [I.a1, BitVec.add_zero, off_off])
      (by rw [o.rd, o.wr, k₆.rd, k₆.wr, h.wr]; exact sc_inR PF (by omega_using [hRs, hk2, ek, hi]) _) fun u₁ p₁ f₁ => ?_
    refine wp_subi (imm := 1) fun u₂ p₂ f₂ => wp_srl fun u₃ p₃ f₃ => wp_li (imm := 1) (by decide) fun u₄ p₄ f₄ =>
      wp_xor fun u₅ p₅ f₅ => wp_subi (imm := 1) fun u₆ p₆ f₆ => wp_srl fun u₇ p₇ f₇ => wp_or fun u₈ p₈ f₈ =>
      wp_subi (imm := 1) fun u₉ p₉ f₉ => wp_and fun u₁₀ p₁₀ f₁₀ => wp_or fun u₁₁ p₁₁ f₁₁ =>
      wp_li (imm := 0) (by decide) fun u₁₂ p₁₂ f₁₂ =>
      wp_sub fun u₁₃ p₁₃ f₁₃ => wp_and fun u₁₄ p₁₄ f₁₄ => wp_and fun u₁₅ p₁₅ f₁₅ => wp_or fun u₁₆ p₁₆ f₁₆ =>
      wp_subi (imm := 1) fun u₁₇ p₁₇ f₁₇ => wp_and fun u₁₈ p₁₈ f₁₈ => wp_addi (imm := 1) fun u₁₉ p₁₉ f₁₉ =>
      wp_addi (imm := 1) fun u₂₀ p₂₀ f₂₀ => wp_subi (imm := 1) fun u₂₁ p₂₁ f₂₁ => wp_nil ?_
    have q : Only [.a7, .t1, .t2, .s5, .t3, .s6, .a4, .a1, .a3, .a2] u u₂₁ :=
      (p₁.trans (p₂.trans (p₃.trans (p₄.trans (p₅.trans (p₆.trans (p₇.trans (p₈.trans (p₉.trans (p₁₀.trans
        (p₁₁.trans (p₁₂.trans (p₁₃.trans (p₁₄.trans (p₁₅.trans (p₁₆.trans (p₁₇.trans (p₁₈.trans (p₁₉.trans
        (p₂₀.trans p₂₁)))))))))))))))))))).mono
    have hb : u₁.gpr .a7 = (f i).setWidth 64 := by
      rw [f₁, o.mem, k₆.mem, ← hf]; rfl
    have a9 : Only [.a7, .t1, .t2] u u₉ :=
      (p₁.trans (p₂.trans (p₃.trans (p₄.trans (p₅.trans (p₆.trans (p₇.trans (p₈.trans p₉)))))))).mono
    have a7 : Only [.a7, .t1, .t2] u u₇ :=
      (p₁.trans (p₂.trans (p₃.trans (p₄.trans (p₅.trans (p₆.trans p₇)))))).mono
    have b12 : Only [.t1, .s5, .t3] u₇ u₁₂ := (p₈.trans (p₉.trans (p₁₀.trans (p₁₁.trans p₁₂)))).mono
    have b16 : Only [.t1, .s5, .t3, .s6] u₇ u₁₆ :=
      (b12.trans (p₁₃.trans (p₁₄.trans (p₁₅.trans p₁₆)))).mono
    have a15 : Only [.a7, .t1, .t2, .s5, .t3] u u₁₅ :=
      (a9.trans (p₁₀.trans (p₁₁.trans (p₁₂.trans (p₁₃.trans (p₁₄.trans p₁₅)))))).mono
    have a17 : Only [.a7, .t1, .t2, .s5, .t3, .s6] u u₁₇ := (a15.trans (p₁₆.trans p₁₇)).mono
    have c11 : Only [.a2, .t1, .s6, .t2, .a4, .a1, .a3, .t3] u₁₁ u₂₁ :=
      (p₁₂.trans (p₁₃.trans (p₁₄.trans (p₁₅.trans (p₁₆.trans (p₁₇.trans (p₁₈.trans (p₁₉.trans (p₂₀.trans
        p₂₁))))))))).mono
    have c16 : Only [.t2, .a4, .a1, .a3, .a2] u₁₆ u₂₁ :=
      (p₁₇.trans (p₁₈.trans (p₁₉.trans (p₂₀.trans p₂₁)))).mono
    have c18 : Only [.a1, .a3, .a2] u₁₈ u₂₁ := (p₁₉.trans (p₂₀.trans p₂₁)).mono
    have a18 : Only [.a7, .t1, .t2, .s5, .t3, .s6, .a4] u u₁₈ := (a17.trans p₁₈).mono
    have a20 : Only [.a7, .t1, .t2, .s5, .t3, .s6, .a4, .a1, .a3] u u₂₀ := (a18.trans (p₁₉.trans p₂₀)).mono
    refine ⟨⟨scan_step I (u₃.gpr .t1) (u₇.gpr .t2) (u₉.gpr .t1) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, (o.trans q).mono⟩, ?_⟩
    · rw [f₃, f₂, hb]
    · rw [f₇, f₆, f₅, f₄, p₄.get .a7, p₃.get .a7, p₂.get .a7, hb]
    · rw [f₉, f₈, p₇.get .t1, p₆.get .t1, p₅.get .t1, p₄.get .t1]
    · rw [c11.get .s5, f₁₁, f₁₀, p₁₀.get .s5, a9.get .s5, a9.get .a4]
    · rw [c16.get .s6, f₁₆, f₁₅, f₁₄, p₁₄.get .t3, f₁₃, f₁₂, b12.get .t2, a15.get .s6, (a9.trans
        (p₁₀.trans (p₁₁.trans (p₁₂.trans p₁₃)))).get .a3, (a9.trans (p₁₀.trans (p₁₁.trans (p₁₂.trans p₁₃)))).get .a4]
    · rw [c18.get .a4, f₁₈, f₁₇, b16.get .t2, a17.get .a4]
    · rw [p₂₁.get .a1, p₂₀.get .a1, f₁₉, a18.get .a1]
    · rw [p₂₁.get .a3, f₂₀, p₁₉.get .a3, a18.get .a3]
    · rw [f₂₁, a20.get .a2]
  refine wp_or fun w ow ew => wp_nil ?_
  have kk' : Only [.a1, .a2, .a3, .a4, .s6, .t3, .t1, .t2, .a7, .s5] t w := (k₆.trans (o.trans ow)).mono
  refine ⟨h.only PF kk', by rw [kk'.mem], kk'.mono, ?_, ?_⟩
  · rw [ew, I.s5, I.a4]
  · rw [ow.get .s6]; exact I.s6

end

end VG.Proof.RsaOaep.RISCV64.Dec

end

end

/-! ### `RsaOaep.RISCV64.Dc.Label`, which this module and modules that import it used -/

section

/-!
# RSAES-OAEP decryption on RISC-V: the label and `lHash`

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Dc/Label.lean`, `Dc/Scan.lean`), with the label and
its length loaded from our stack arguments 9 and 10 (`wp_argB`): its hash to
`scratch + oDig`, through the table that is our stack argument 15, of the
hash function `H` (`hashLabelT_ok`), and the accumulator of `EM`'s first byte
and `lHash' ⊕ lHash` (`accLh_ok`, `accG`), which reads our part of the
working space only.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.RISCV64.Dec

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64 VG.Impl.RsaOaep.RISCV64.Dec
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only wp_li wp_addi wp_subi wp_mov wp_xor wp_or wp_ld wp_lbu wp_addSp wp_nil)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.RsaOaep.RISCV64 (Base Fits SC Same view off offs hfits initT_ok updT_ok finT_ok bytes_entry sc_in sc_inR
  cR_sub only_pres TabS)
open VG.Impl.RsaOaep.RISCV64 (Fns hashLabelT)
open VG.Proof.Bignum.RISCV64 (wp_countdown)
open VG.Proof.RsaOaep (accG)

section
variable {pc : Bool} {s : State} (P : PreD pc s) {m : Mem} {rc : Nat}
include P

/-- A load of our stack argument `j` through `t6`, the entry stack pointer,
in the decoding, whose memory is that after the private operation, `m`. -/
theorem wp_argB (hm : Frame [kD pc s, scR s] s.mem m) {u : State} {r : Reg} {j : Nat} {is : List Instr}
    {Q : State → Prop} (hj : j < 17) (h6 : u.gpr .t6 = s.sp) (hrd : u.rd = s.rd)
    (hmu : Frame [Proof.RsaOaep.RISCV64.kR s, SC (SD s) s] m u.mem)
    (k : ∀ u', Only [r] u u' → u'.gpr r = stackArg s j → WP isa (.block is) u' Q)
    (ho : 8 * j < 2048 := by decide) :
    WP isa (.block (.load .d r .t6 (8 * j) :: is)) u Q := by
  refine wp_ld (a := stackArgAddr s j) (by rw [h6]; rfl) (arg_al P hj) ?_ (fun u' o e => k u' o ?_) ho
  · rw [hrd, P.hrd]; exact ⟨aR pc s, by simp, in_aR hj⟩
  · rw [e, stackArg, hmu.readW (in_aR hj) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact (P.ka.sub_left kR_sub).symm
        · exact (P.sa.sub_left (sc_sub P)).symm) (by decide),
      hm.readW (in_aR hj) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact P.ka.symm
        · exact P.sa.symm) (by decide)]

theorem hashLabelT_ok {H : Hash} (hH : HashOK H) (hF : H.F ≤ 208) (hm : Frame [kD pc s, scR s] s.mem m) {f : Fns}
    {p : Addr} (T : TabS H f 15 (SD s) (withMem s m) p) {t : State}
    (h : Base (SD s) (VD s rc) (withMem s m) t) (sy : t.syms = s.syms) :
    WP isa (hashLabelT f 15 Dec.labU Dec.labF) t fun t' => (Base (SD s) (VD s rc) (withMem s m) t' ∧
      (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧ Same (Sd s) t t' [(oSt, H.S), (oDig, H.D)] ∧
      Spec.Rsa.bytesAt t'.mem (off (Sd s) oDig) H.D =
        hH.SH.H.hash (Spec.Rsa.bytesAt m (stackArg s 9) (stackArg s 10).toNat)) ∧ t'.syms = s.syms := by
  have F := hfits hH
  have PF : Fits (SD s) (withMem s m) := fits P rfl rfl
  obtain ⟨_, _, _, _, _⟩ := offs
  have top : ∀ {u : State}, u.sp = fb s → u.sp + BitVec.ofNat 64 frameBytes = s.sp := fun hu => by
    rw [hu, BitVec.sub_add_cancel]
  refine WP.seq (WP.of_syms (wp_addi (imm := oSt) fun t₁ o₁ e₁ => wp_nil fun y₁ => ?_))
  have b₁ := h.only PF o₁
  have sy₁ : t₁.syms = (withMem s m).syms := y₁.trans sy
  refine WP.seq (WP.mono (initT_ok PF T hH hF b₁ sy₁ (by rw [e₁, h.s0])) fun t₂ ⟨⟨b₂, g₂, s₂, r₂⟩, y₂⟩ => ?_)
  unfold Dec.labU argBase
  refine WP.seq (WP.of_syms (wp_addSp (imm := frameBytes) (fun t₃ o₃ e₃ => wp_addi (imm := oSt) fun t₄ o₄ e₄ =>
    wp_li (imm := 0) (by decide) fun t₅ o₅ e₅ => ?_) (by decide)))
  have K₅ : Only [.t6, .a0, .a1] t₂ t₅ := (o₃.trans (o₄.trans o₅)).mono
  have g6 : t₅.gpr .t6 = s.sp := by rw [o₅.get .t6, o₄.get .t6, e₃, top b₂.sv.sp]
  refine wp_argB P hm (j := 9) (by decide) g6 (K₅.rd.trans b₂.rd) (by rw [K₅.mem]; exact b₂.mem)
    fun t₆ o₆ e₆ => wp_argB P hm (j := 10) (by decide) (by rw [o₆.get .t6, g6])
      ((o₆.rd.trans K₅.rd).trans b₂.rd) (by rw [o₆.mem, K₅.mem]; exact b₂.mem) fun t₇ o₇ e₇ => wp_nil fun y₇ => ?_
  have k₇ : Only [.t6, .a0, .a1, .a2, .a3] t₂ t₇ := (K₅.trans (o₆.trans o₇)).mono
  have b₇ := b₂.only PF k₇
  have hl : lR s ∈ s.rd := by rw [P.hrd]; simp
  have hb : Spec.Rsa.bytesAt t₇.mem (stackArg s 9) (stackArg s 10).toNat =
      Spec.Rsa.bytesAt m (stackArg s 9) (stackArg s 10).toNat :=
    bytes_entry b₇.mem (P.kl.sub_left kR_sub) ((P.ls.symm).sub_left (sc_sub P)) (by have := P.wl; omega_using [])
  refine WP.seq (WP.mono (updT_ok PF T hH hF b₇ (y₇.trans y₂) (dat := stackArg s 9) (len := (stackArg s 10).toNat)
    (by rw [o₇.get .a0, o₆.get .a0, o₅.get .a0, e₄, o₃.get .s0, b₂.s0])
    (by rw [o₇.get .a2, e₆])
    (by rw [e₇])
    (Covers.left (by rw [b₇.rd]; exact Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; exact hl))
    ((P.ls.sub_right (sc_sub P)).sub_right (sc_in (by omega_arith)))
    (P.kl.sub_left fun a ha => kR_sub a (cR_sub (withMem s m) a ha))) fun t₈ ⟨⟨b₈, g₈, s₈, r₈⟩, y₈⟩ => ?_)
  unfold Dec.labF argBase
  refine WP.seq (WP.of_syms (wp_addSp (imm := frameBytes) (fun t₉ o₉ e₉ => wp_addi (imm := oSt) fun t₁₀ o₁₀ e₁₀ => ?_)
    (by decide)))
  have g6' : t₁₀.gpr .t6 = s.sp := by rw [o₁₀.get .t6, e₉, top b₈.sv.sp]
  refine wp_argB P hm (j := 10) (by decide) g6' ((o₁₀.rd.trans o₉.rd).trans b₈.rd)
    (by rw [o₁₀.mem, o₉.mem]; exact b₈.mem) fun t₁₁ o₁₁ e₁₁ =>
      wp_addi (imm := oDig) (fun t₁₂ o₁₂ e₁₂ => wp_nil fun y₁₂ => ?_)
  have k₁₂ : Only [.t6, .a0, .a1, .a2] t₈ t₁₂ := (o₉.trans (o₁₀.trans (o₁₁.trans o₁₂))).mono
  have b₁₂ := b₈.only PF k₁₂
  have g1 : t₁₂.gpr .a1 = stackArg s 10 := by rw [o₁₂.get .a1, e₁₁]
  have hr : hH.SH.Repr t₁₂.mem (off (Sd s) oSt) (Spec.Rsa.bytesAt m (stackArg s 9) (stackArg s 10).toNat) := by
    rw [k₁₂.mem, ← hb]
    have := r₈ [] (by rw [k₇.mem]; exact r₂) (by rw [o₇.get .a1, o₆.get .a1, e₅]; rfl)
    simp only [List.nil_append] at this; exact this
  refine WP.mono (finT_ok PF T hH hF b₁₂ (y₁₂.trans y₈) (by rw [o₁₂.get .a0, o₁₁.get .a0, e₁₀, o₉.get .s0, b₈.s0])
    (by rw [e₁₂, o₁₁.get .s0, o₁₀.get .s0, o₉.get .s0, b₈.s0])) fun t' ⟨⟨b', g', s', r'⟩, y'⟩ =>
      ⟨⟨b', fun r hr' => ?_, ?_, ?_⟩, y'⟩
  · rw [g' r hr', only_pres k₁₂ (by decide) r hr', g₈ r hr', only_pres k₇ (by decide) r hr', g₂ r hr',
      only_pres o₁ (by decide) r hr']
  · have e : ∀ {a b : State}, a.mem = b.mem → ∀ rgs, Same (Sd s) a b rgs := fun e rgs => Same.of_mem e.symm rgs
    exact ((((((e o₁.mem.symm _).trans (s₂.mono (by simp))).trans (e k₇.mem.symm _)).trans
      (s₈.mono (by simp))).trans (e k₁₂.mem.symm _)).trans s')
  · exact r' _ hr (by rw [bytesAt_length]; have := (stackArg s 10).isLt; omega_using [])
      (by rw [g1, bytesAt_length, BitVec.ofNat_toNat, BitVec.setWidth_eq])

/-- `acc := EM[0] ∨ ⋁ (lHash'[i] ⊕ lHash[i])`, `lHash'` at `1 + D`, `lHash` at
`oDig`. -/
theorem accLh_ok {H : Hash} {D : Nat} (hD : H.D = D) (hD0 : 0 < D) (hD64 : D ≤ 64) (hk : 2 * D + 2 ≤ kk s)
    {t : State} (h : Base (SD s) (VD s rc) (withMem s m) t) :
    WP isa (accLh H) t fun t' => Base (SD s) (VD s rc) (withMem s m) t' ∧ t'.mem = t.mem ∧
      Only [.a4, .a5, .a6, .s5, .t1, .t2] t t' ∧
      t'.gpr .s5 = accG (view t.mem (Sd s) 0) (fun i => view t.mem (Sd s) (1 + D + i))
        (fun i => view t.mem (Sd s) (oDig + i)) D := by
  obtain ⟨hE, hSt, hDg, hCt, hRs⟩ := offs
  have hk2 := P.k2
  have ek : kk s = (s.gpr .a4).toNat := rfl
  have PF : Fits (SD s) (withMem s m) := fits P rfl rfl
  subst hD
  have rdw : ∀ {u : State}, u.rd = t.rd → u.wr = t.wr → ∀ {o : Nat}, o + 1 ≤ oRsa →
      InRegions (u.rd ++ u.wr) (off (Sd s) o) 1 := fun hr hw _ ho => by
    rw [hr, hw, h.wr]; exact sc_inR PF ho _
  unfold accLh
  refine WP.seq (wp_addi (imm := oEm + 1 + H.D) (h := by omega_using [hE, hD64]) fun t₁ o₁ e₁ =>
    wp_addi (imm := oDig) (h := by omega_using [hDg]) fun t₂ o₂ e₂ =>
    wp_lbu (a := off (Sd s) 0) (by rw [o₂.get .s0, o₁.get .s0, h.s0, hE])
      (rdw (o₂.rd.trans o₁.rd) (o₂.wr.trans o₁.wr) (by decide)) fun t₃ o₃ e₃ =>
    wp_li (imm := H.D) (by omega_using [hD64]) fun t₄ o₄ e₄ => wp_nil ?_)
  have k₄ : Only [.a4, .a5, .s5, .a6] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  refine WP.mono (wp_countdown (cnt := .a6) (N := H.D) (by omega_using [hD64]) hD0
    (fun i u => Only [.a4, .a5, .a6, .s5, .t1, .t2] t u ∧ u.gpr .a4 = off (Sd s) (1 + H.D + i) ∧
      u.gpr .a5 = off (Sd s) (oDig + i) ∧ u.gpr .s5 = accG (view t.mem (Sd s) 0)
        (fun i => view t.mem (Sd s) (1 + H.D + i)) (fun i => view t.mem (Sd s) (oDig + i)) i) ?_
    ⟨k₄.mono, by rw [o₄.get .a4, o₃.get .a4, o₂.get .a4, e₁, h.s0, hE]; rfl,
      by rw [o₄.get .a5, o₃.get .a5, e₂, o₁.get .s0, h.s0]; rfl,
      by rw [o₄.get .s5, e₃, o₂.mem, o₁.mem]; rfl⟩ (by rw [e₄]))
    fun u ⟨o, _, _, a⟩ => ⟨h.only PF o, o.mem, o, a⟩
  intro i hi u ⟨o, r4, r5, a⟩ _
  simp only [accBody, List.cons_append, List.nil_append]
  refine wp_lbu (a := off (Sd s) (1 + H.D + i)) (by rw [r4, BitVec.add_zero])
    (rdw o.rd o.wr (by omega_using [hRs, hD64, hi])) fun u₁ p₁ f₁ => ?_
  refine wp_lbu (a := off (Sd s) (oDig + i)) (by rw [p₁.get .a5, r5, BitVec.add_zero])
    (rdw (p₁.rd.trans o.rd) (p₁.wr.trans o.wr) (by omega_using [hDg, hRs, hD64, hi])) fun u₂ p₂ f₂ => ?_
  refine wp_xor fun u₃ p₃ f₃ => wp_or fun u₄ p₄ f₄ => wp_addi (imm := 1) fun u₅ p₅ f₅ =>
    wp_addi (imm := 1) fun u₆ p₆ f₆ => wp_subi (imm := 1) fun u₇ p₇ f₇ => wp_nil ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (o.trans (p₁.trans (p₂.trans (p₃.trans (p₄.trans (p₅.trans (p₆.trans p₇))))))).mono
  · rw [p₇.get .a4, p₆.get .a4, f₅, p₄.get .a4, p₃.get .a4, p₂.get .a4, p₁.get .a4, r4]
    show off (off (Sd s) (1 + H.D + i)) 1 = off (Sd s) (1 + H.D + i + 1); exact Proof.RsaOaep.RISCV64.off_off _ _ _
  · rw [p₇.get .a5, f₆, p₅.get .a5, p₄.get .a5, p₃.get .a5, p₂.get .a5, p₁.get .a5, r5]
    show off (off (Sd s) (oDig + i)) 1 = off (Sd s) (oDig + i + 1); exact Proof.RsaOaep.RISCV64.off_off _ _ _
  · rw [p₇.get .s5, p₆.get .s5, p₅.get .s5, f₄, p₃.get .s5, p₂.get .s5, p₁.get .s5, a, f₃, p₂.get .t1, f₁,
      f₂, p₁.mem, o.mem]; rfl
  · rw [f₇, p₆.get .a6, p₅.get .a6, p₄.get .a6, p₃.get .a6, p₂.get .a6, p₁.get .a6]

end

end VG.Proof.RsaOaep.RISCV64.Dec

end

end

/-! ### `RsaOaep.RISCV64.Dc.Out`, which this module and modules that import it used -/

section

/-! ### `RsaOaep.RISCV64.Dc.Written`, which this module and modules that import it used -/

section

/-!
# RSAES-OAEP decryption on RISC-V: what the outputs say

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Dc/Out.lean`): `dec_written`, from the
views of `EM` before and after its unmasking, `lHash` and the scan's
registers, the bytes of `out` (the buffer shifted by `idx + 1`, ANDed with
`ok`), `*msg_len` and the result are what `writtenDecrypt` asks of
`decOut`'s outcome.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.RISCV64.Dec

open VG
open VG.Proof.RsaOaep (mixV srcB mk scanS accG zM decOut decode_eq scanS_inv accG_eq_zero or_eq_zero mk_eq_zero
  scan_found scan_fail out_list out_zero lk bad srcB_eq scanS_congr map_range_getD')
open VG.Proof.Mgf1 (ifp ifn)

/-- A byte ANDed with a mask. -/
def andB (b : Byte) (msk : BitVec 64) : Byte := (b.setWidth 64 &&& msk).setWidth 8

theorem andB_ones (b : Byte) : andB b (BitVec.allOnes 64) = b := by
  simp only [andB, BitVec.and_allOnes]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (by have := b.isLt; omega_using []), Nat.mod_eq_of_lt (by have := b.isLt; omega_using [])]

theorem andB_zero (b : Byte) : andB b 0 = 0 := by
  simp only [andB]; rw [show BitVec.setWidth 64 b &&& 0 = 0 from BitVec.and_zero]; rfl

theorem mk_true {p : Prop} [Decidable p] (h : p) : mk p = BitVec.allOnes 64 := by simp [mk, h]
theorem mk_false {p : Prop} [Decidable p] (h : ¬ p) : mk p = 0 := by simp [mk, h]

theorem accG_congr (b : Byte) {f f' g g' : Nat → Byte} : ∀ n, (∀ i < n, f i = f' i) → (∀ i < n, g i = g' i) →
    accG b f g n = accG b f' g' n
  | 0, _, _ => rfl
  | n + 1, hf, hg => by
    simp only [accG]
    rw [accG_congr b n (fun i hi => hf i (by omega_using [hi])) (fun i hi => hg i (by omega_using [hi])), hf n (by omega_using []), hg n (by omega_using [])]

section
variable {Hs Gs : Spec.Mgf1.Hash} {D k : Nat} {lab : List Byte} {V0 V1 lh : Nat → Byte}
  {o : Spec.Rsa.Outcome} {mo : Mem} {out ml : Addr} {r : BitVec 64} {idx : Nat}

theorem dec_written (hGv : Proof.Mgf1.Valid Gs) (hHv : Proof.Mgf1.Valid Hs) (hHl : Hs.len = D) (hk : 2 * D + 2 ≤ k)
    (hk2 : k ≤ 1024)
    (h5 : ∀ x < k, V1 x = mixV (mixV V0 (Spec.Mgf1.mgf1 Gs (srcB V0 (1 + D) (k - D - 1)) D) 1 D)
      (Spec.Mgf1.mgf1 Gs (srcB (mixV V0 (Spec.Mgf1.mgf1 Gs (srcB V0 (1 + D) (k - D - 1)) D) 1 D) 1 D) (k - D - 1))
      (1 + D) (k - D - 1) x)
    (hlh : ∀ i < D, lh i = (Hs.hash lab).getD i 0)
    (hem : ∀ em, o = .ok em → em = (List.range k).map V0)
    (hidx : (scanS (fun i => V1 (1 + 2 * D + i)) (accG (V1 0) (fun i => V1 (1 + D + i)) lh D)
      (k - (2 * D + 1))).2.1 = BitVec.ofNat 64 idx)
    (hidx' : idx < k - (2 * D + 1) ∨ idx = 0)
    (hout : ∀ i < k, mo (out + BitVec.ofNat 64 i) =
      andB ((srcB V1 (1 + 2 * D) (k - (2 * D + 1))).getD (i + (idx + 1)) 0)
        (mk (rcOf o = 1 ∧ ((scanS (fun i => V1 (1 + 2 * D + i)) (accG (V1 0) (fun i => V1 (1 + D + i)) lh D)
          (k - (2 * D + 1))).2.2 ||| (scanS (fun i => V1 (1 + 2 * D + i))
            (accG (V1 0) (fun i => V1 (1 + D + i)) lh D) (k - (2 * D + 1))).1) = 0)))
    (hml : mo.readW ml 64 = (BitVec.ofNat 64 k - BitVec.ofNat 64 (2 * D + 2) - BitVec.ofNat 64 idx) &&&
      mk (rcOf o = 1 ∧ ((scanS (fun i => V1 (1 + 2 * D + i)) (accG (V1 0) (fun i => V1 (1 + D + i)) lh D)
          (k - (2 * D + 1))).2.2 ||| (scanS (fun i => V1 (1 + 2 * D + i))
            (accG (V1 0) (fun i => V1 (1 + D + i)) lh D) (k - (2 * D + 1))).1) = 0))
    (hr : r = (if rcOf o = 2 then 2#64 else 0#64) |||
      (mk (rcOf o = 1 ∧ ((scanS (fun i => V1 (1 + 2 * D + i)) (accG (V1 0) (fun i => V1 (1 + D + i)) lh D)
          (k - (2 * D + 1))).2.2 ||| (scanS (fun i => V1 (1 + 2 * D + i))
            (accG (V1 0) (fun i => V1 (1 + D + i)) lh D) (k - (2 * D + 1))).1) = 0) &&& 1#64)) :
    Spec.RsaOaep.writtenDecrypt mo out ml k (r.setWidth 32) (decOut Hs Gs lab o) := by
  generalize hT : srcB V1 (1 + 2 * D) (k - (2 * D + 1)) = T at hout
  have hTl : T.length = k - (2 * D + 1) := by rw [← hT]; simp [srcB]
  have hTg : ∀ i < k - (2 * D + 1), T.getD i 0 = V1 (1 + 2 * D + i) := fun i hi => by
    rw [← hT, srcB, map_range_getD' _ hi]
  generalize hc₀ : accG (V1 0) (fun i => V1 (1 + D + i)) lh D = c₀ at *
  have hsc2 : scanS (fun i => V1 (1 + 2 * D + i)) c₀ (k - (2 * D + 1)) =
      scanS (fun i => T.getD i 0) c₀ T.length := by
    rw [hTl]; exact scanS_congr _ _ fun i hi => (hTg i hi).symm
  rw [hsc2] at hidx hout hml hr
  generalize hsc : scanS (fun i => T.getD i 0) c₀ T.length = sc at *
  obtain ⟨i1, -, -, i4⟩ := scanS_inv (fun i => T.getD i 0) c₀ T.length
  rw [hsc] at i1 i4
  have hacc : sc.2.2 ||| sc.1 = 0 ↔ c₀ = 0 ∧ ¬ bad (fun i => T.getD i 0) T.length ∧
      ¬ lk (fun i => T.getD i 0) T.length := by
    rw [i4, i1, or_eq_zero, or_eq_zero, mk_eq_zero, mk_eq_zero, and_assoc]
  -- A mask of zero: zeros, the length 0, and the result `r = 2 ? 2 : 0`.
  have zero_out : mk (rcOf o = 1 ∧ sc.2.2 ||| sc.1 = 0) = 0 →
      Spec.Rsa.bytesAt mo out k = Spec.RsaOaep.zeros k ∧ mo.readW ml 64 = 0 ∧
      r.setWidth 32 = (if rcOf o = 2 then 2#64 else 0#64).setWidth 32 := fun h0 =>
    ⟨out_zero fun i hi => by rw [hout i hi, h0, andB_zero], by rw [hml, h0]; exact BitVec.and_zero,
      by rw [hr, h0]; split <;> decide⟩
  cases o with
  | fault =>
    obtain ⟨a, b, c⟩ := zero_out (mk_false fun h => by simp [rcOf] at h)
    exact ⟨by rw [c]; decide, a, b⟩
  | invalid =>
    obtain ⟨a, b, c⟩ := zero_out (mk_false fun h => by simp [rcOf] at h)
    exact ⟨by rw [c]; decide, a, b⟩
  | ok em =>
    have em_eq := hem em rfl
    subst em_eq
    have r1 : rcOf (.ok ((List.range k).map V0)) = 1 := rfl
    simp only [r1, true_and, ite_false, show (1 : Nat) ≠ 2 by decide] at hout hml hr zero_out
    rw [BitVec.zero_or] at hr
    simp only [decOut]
    rw [decode_eq hGv _ hk hHl h5, show k - (2 * D + 1) = k - (2 * D + 1) from rfl, hT]
    have hz : sc.2.2 ||| sc.1 ≠ 0 → _ := fun hne => zero_out (mk_false hne)
    by_cases hfd : ¬ lk (fun i => T.getD i 0) T.length ∧ ¬ bad (fun i => T.getD i 0) T.length
    · obtain ⟨j₀, hj₀, hsj, hdw⟩ := scan_found T c₀ hfd.1 hfd.2
      rw [hsc] at hsj
      have hij : idx = j₀ := by
        have := hidx.symm.trans hsj
        have := congrArg BitVec.toNat this
        rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hk2, hidx']),
          Nat.mod_eq_of_lt (by omega_using [hk2, hTl, hj₀])] at this
      subst hij
      rw [hdw, show (1 : Byte) = 1#8 from rfl]
      simp only []
      have hV0 : V1 0 = V0 0 := by
        rw [h5 0 (by omega_using [hk]), mixV, ifn (by omega_using []), mixV, ifn (by omega_using [])]
      have htake : ((List.range k).map V0).take 1 = [V0 0] := by
        rw [show k = (k - 1) + 1 by omega_using [hk], List.range_succ_eq_map]; simp
      by_cases hc : ((List.range k).map V0).take 1 = [0x00] ∧ srcB V1 (1 + D) D = Hs.hash lab
      · rw [ifp hc]
        have hacc0 : sc.2.2 ||| sc.1 = 0 := hacc.mpr ⟨by
          rw [← hc₀]; exact (accG_eq_zero _ _ _ D).mpr ⟨by
            rw [hV0]; rw [htake] at hc; exact List.head_eq_of_cons_eq hc.1, fun i hi => by
            show V1 (1 + D + i) = lh i
            rw [hlh i hi, ← hc.2, srcB, map_range_getD' _ hi]⟩, hfd.2, hfd.1⟩
        rw [mk_true hacc0] at hout hml hr
        refine ⟨by rw [hr]; decide, out_list (by omega_using [hTl]) hj₀ fun i hi => by rw [hout i hi, andB_ones], ?_⟩
        rw [hml, BitVec.and_allOnes, VG.Offset.ofNat_sub_ofNat (by omega_using [hk]), VG.Offset.ofNat_sub_ofNat (by omega_using [hidx']),
          List.length_drop]
        congr 1; omega_using [hTl]
      · rw [ifn hc]
        have hne : sc.2.2 ||| sc.1 ≠ 0 := fun h0 => by
          have e := (accG_eq_zero _ _ _ D).mp (hc₀ ▸ (hacc.mp h0).1)
          obtain ⟨e0, e1⟩ := e
          refine hc ⟨by rw [htake, ← hV0, e0], ?_⟩
          refine srcB_eq (by rw [hHv.2, hHl]) fun i hi => ?_
          rw [← hlh i hi]; exact e1 i hi
        obtain ⟨a, b, c⟩ := hz hne
        exact ⟨by rw [c]; rfl, a, b⟩
    · have hfail := scan_fail T (by
        by_contra hc; exact hfd ⟨fun h => hc (.inl h), fun h => hc (.inr h)⟩)
      have hne : sc.2.2 ||| sc.1 ≠ 0 := fun h0 => hfd ⟨(hacc.mp h0).2.2, (hacc.mp h0).2.1⟩
      obtain ⟨a, b, c⟩ := hz hne
      split
      · rename_i m heq
        split at heq
        · rename_i m' hm; exact absurd hm (hfail m')
        · cases heq
      · exact ⟨by rw [c]; rfl, a, b⟩

end

end VG.Proof.RsaOaep.RISCV64.Dec

end

end

/-!
# RSAES-OAEP decryption on RISC-V: the outputs

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Dc/Out.lean`): `okMask_ok`, `ok`, all ones iff
the private operation's result is 1 and the accumulator zero (`x ≠ 0` from
the top bit of `x ∨ -x`); `outLoop_ok`, the buffer's first `k` bytes ANDed
with it to `out`; `decRet_ok`, the length and the result; `decFail_ok`,
zeros, and the result `r = 2 ? 2 : 0`. From `out` on, `Base` does not hold
(`out` is not ours): the caller's registers in their slots (`Saves`) do.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.RISCV64.Dec

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64 VG.Impl.RsaOaep.RISCV64.Dec VG.WriteBytes
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Impl.Bignum.RISCV64 (countLoop)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo wp_li wp_mov wp_addi wp_subi wp_add wp_sub wp_and wp_or wp_xor
  wp_srl wp_lbu wp_sb wp_sd wp_nil fill_ok ofNat_succ')
open VG.Proof.RsaPkcs1Sig (bytesAt_length writeBytes_out)
open VG.Proof.RsaOaep.RISCV64 (Base Fits Saves view off off_off sc_in sc_inR fr slR slR_sub ne_of_dis)
open VG.Proof.Bignum.RISCV64 (wp_countdown)
open VG.Proof.RsaOaep (mk)
open VG.Proof.Mgf1 (ifp ifn)

/-! ## Bits -/

/-- `(x ∨ -x) >>> 63`: 0 if `x = 0`, 1 if not. -/
theorem nzbit (x : BitVec 64) : ((BitVec.ofNat 64 0 - x) ||| x) >>> 63 = if x = 0 then 0#64 else 1#64 := by
  by_cases hx : x = 0
  · subst hx; decide
  · rw [ifn hx]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_or, Nat.shiftRight_eq_div_pow]
    have h0 : x.toNat ≠ 0 := fun h => hx (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
    have hl := x.isLt
    have hs : (BitVec.ofNat 64 0 - x).toNat = 2 ^ 64 - x.toNat := by
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega_using [h0]
    have h1 : 2 ^ 63 ≤ ((BitVec.ofNat 64 0 - x).toNat ||| x.toNat) := by
      rcases Nat.lt_or_ge x.toNat (2 ^ 63) with h | h
      · exact Nat.le_trans (by rw [hs]; omega_using [h]) Nat.left_le_or
      · exact Nat.le_trans h Nat.right_le_or
    have h2 : ((BitVec.ofNat 64 0 - x).toNat ||| x.toNat) < 2 ^ 64 := Nat.or_lt_two_pow (BitVec.isLt _) hl
    rw [Nat.div_eq_of_lt_le (k := 1) (by omega_using [h1]) (by omega_using [h2])]; rfl

/-- `ok` from the result `rc` and the accumulator `x`. -/
theorem okbits {rc : Nat} (hrc : rc ≤ 2) (x : BitVec 64) :
    BitVec.ofNat 64 0 - ((((BitVec.ofNat 64 rc ^^^ BitVec.ofNat 64 1) - BitVec.ofNat 64 1) >>> 63) &&&
      ((((BitVec.ofNat 64 0 - x) ||| x) >>> 63) ^^^ BitVec.ofNat 64 1)) = mk (rc = 1 ∧ x = 0) := by
  rw [nzbit]
  by_cases hx : x = 0
  · rw [ifp hx, mk]
    rcases (by omega_using [hrc] : rc = 0 ∨ rc = 1 ∨ rc = 2) with rfl | rfl | rfl <;> simp only [hx] <;> decide
  · rw [ifn hx, mk, ifn (fun h => hx h.2)]
    rcases (by omega_using [hrc] : rc = 0 ∨ rc = 1 ∨ rc = 2) with rfl | rfl | rfl <;> decide

/-- The result's fault bit: 2 if `rc = 2`, 0 if not. -/
theorem faultbits {rc : Nat} (hrc : rc ≤ 2) :
    let f := ((BitVec.ofNat 64 rc ^^^ BitVec.ofNat 64 2) - BitVec.ofNat 64 1) >>> 63
    f + f = if rc = 2 then 2#64 else 0#64 := by
  rcases (by omega_using [hrc] : rc = 0 ∨ rc = 1 ∨ rc = 2) with rfl | rfl | rfl <;> decide

/-- `Saves` of the entry state with other memory is `Saves` of the entry state. -/
theorem Saves.ofMem {s t : State} {m : Mem} (h : Saves (withMem s m) t) : Saves s t := ⟨h.sp, h.wr, h.sv⟩

/-- `a6` bytes from `a4` to `a5`, each ANDed with `s7`, for `a6 > 0`. -/
theorem andCopy_ok {u : State} {p q : Addr} {n : Nat} {msk : BitVec 64} (hn : 0 < n) (hn' : n < 2 ^ 64)
    (h4 : u.gpr .a4 = q) (h5 : u.gpr .a5 = p) (h6 : u.gpr .a6 = BitVec.ofNat 64 n) (h7 : u.gpr .s7 = msk)
    (hr : ∀ j < n, InRegions (u.rd ++ u.wr) (q + BitVec.ofNat 64 j) 1)
    (hw : ∀ i < n, InRegions u.wr (p + BitVec.ofNat 64 i) 1)
    (hd : ∀ j < n, ∀ i < n, q + BitVec.ofNat 64 j ≠ p + BitVec.ofNat 64 i) :
    WP isa (countLoop .a6 outBody) u fun t => Kept [.t1, .a4, .a5, .a6] u t ∧
      t.mem = writeBytes u.mem p ((Spec.Rsa.bytesAt u.mem q n).map fun b => andB b msk) := by
  refine WP.mono (wp_countdown (cnt := .a6) hn' hn
    (fun i t => Kept [.t1, .a4, .a5, .a6] u t ∧
      t.mem = writeBytes u.mem p (((Spec.Rsa.bytesAt u.mem q n).map fun b => andB b msk).take i) ∧
      t.gpr .a5 = p + BitVec.ofNat 64 i ∧ t.gpr .a4 = q + BitVec.ofNat 64 i) ?_
    ⟨Kept.refl _ _, by simp [writeBytes_nil], by simp [h5], by simp [h4]⟩ h6) fun t h => ⟨h.1, ?_⟩
  · intro i hi t ⟨hK, hm, h5', h4'⟩ _
    simp only [outBody, List.cons_append, List.nil_append]
    have hR : InRegions (t.rd ++ t.wr) (q + BitVec.ofNat 64 i) 1 := by
      rw [hK.rd, hK.wr]; exact hr _ hi
    have hv : t.mem (q + BitVec.ofNat 64 i) = u.mem (q + BitVec.ofNat 64 i) := by
      rw [hm, writeBytes_out _ _ _ _ n (fun i' hi' => hd i hi i' hi')
        (by simp only [List.length_take, List.length_map, bytesAt_length]; omega_using [])]
    refine wp_lbu (a := q + BitVec.ofNat 64 i) (by rw [h4', BitVec.add_zero]) hR fun s₁ o₁ e₁ =>
      wp_and fun s₂ o₂ e₂ => ?_
    have hA : InRegions s₂.wr (p + BitVec.ofNat 64 i) 1 := by
      rw [o₂.wr, o₁.wr, hK.wr]; exact hw _ hi
    refine wp_sb (a := p + BitVec.ofNat 64 i) (by rw [o₂.get .a5, o₁.get .a5, h5', BitVec.add_zero]) hA
      fun s₃ m₃ => ?_
    refine wp_addi (imm := 1) fun s₄ o₄ e₄ => wp_addi (imm := 1) fun s₅ o₅ e₅ =>
      wp_subi (imm := 1) fun s₆ o₆ e₆ => wp_nil ?_
    have hK' : Kept [.t1, .a4, .a5, .a6] t s₆ :=
      (o₁.keep.trans (o₂.keep.trans (m₃.keep.trans (o₄.keep.trans (o₅.keep.trans o₆.keep))))).mono
    have hlt : (((Spec.Rsa.bytesAt u.mem q n).map fun b => andB b msk).take i).length = i := by
      simp [bytesAt_length]; omega_using [hi]
    have hget : ((Spec.Rsa.bytesAt u.mem q n).map fun b => andB b msk)[i]'(by simp [bytesAt_length]; omega_using [hi]) =
        andB (u.mem (q + BitVec.ofNat 64 i)) msk := by
      simp [Spec.Rsa.bytesAt]
    refine ⟨⟨(hK.trans hK').mono, ?_, ?_, ?_⟩, ?_⟩
    · rw [o₆.mem, o₅.mem, o₄.mem, m₃.mem, o₂.mem, o₁.mem, hm, List.take_succ_eq_append_getElem
        (by simp [bytesAt_length]; omega_using [hi]), writeBytes_snoc _ _ _ _ (by omega_using [hn', hi, hlt]), hlt, hget]
      congr 1
      rw [e₂, e₁, o₁.get .s7, hK.get .s7, h7, hv]; rfl
    · rw [o₆.get .a5, e₅, o₄.get .a5, m₃.gpr, o₂.get .a5, o₁.get .a5, h5', ofNat_succ']
    · rw [o₆.get .a4, o₅.get .a4, e₄, m₃.gpr, o₂.get .a4, o₁.get .a4, h4', ofNat_succ']
    · rw [e₆, o₅.get .a6, o₄.get .a6, m₃.gpr, o₂.get .a6, o₁.get .a6]
  · rw [List.take_of_length_le (by simp [bytesAt_length])] at h
    exact h.2.1

section
variable {pc : Bool} {s : State} (P : PreD pc s) {m : Mem} {rc : Nat}
include P

/-- `ok` (`s7`). -/
theorem okMask_ok {t : State} (h : Base (SD s) (VD s rc) (withMem s m) t) (hrc : rc ≤ 2) :
    WP isa (.block okMask) t fun t' => Base (SD s) (VD s rc) (withMem s m) t' ∧ t'.mem = t.mem ∧
      Only [.a1, .a2, .a3, .s7] t t' ∧ t'.gpr .s7 = mk (rc = 1 ∧ t.gpr .s5 = 0) := by
  have PF : Fits (SD s) (withMem s m) := fits P rfl rfl
  unfold okMask
  refine wp_li (imm := 1) (by decide) fun t₁ o₁ e₁ => wp_xor fun t₂ o₂ e₂ => wp_subi (imm := 1) fun t₃ o₃ e₃ =>
    wp_srl fun t₄ o₄ e₄ => wp_li (imm := 0) (by decide) fun t₅ o₅ e₅ => wp_sub fun t₆ o₆ e₆ =>
    wp_or fun t₇ o₇ e₇ => wp_srl fun t₈ o₈ e₈ => wp_li (imm := 1) (by decide) fun t₉ o₉ e₉ =>
    wp_xor fun t₁₀ o₁₀ e₁₀ => wp_and fun t₁₁ o₁₁ e₁₁ => wp_li (imm := 0) (by decide) fun t₁₂ o₁₂ e₁₂ =>
    wp_sub fun t₁₃ o₁₃ e₁₃ => wp_nil ?_
  have k : Only [.a1, .a2, .a3, .s7] t t₁₃ :=
    (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans (o₇.trans (o₈.trans (o₉.trans (o₁₀.trans
      (o₁₁.trans (o₁₂.trans o₁₃)))))))))))).mono
  refine ⟨h.only PF k, k.mem, k, ?_⟩
  rw [e₁₃, e₁₂, o₁₂.get .a1, e₁₁, o₁₀.get .a1, e₁₀, e₉, o₉.get .a2, o₉.get .a1, e₈, o₈.get .a1, e₇, o₇.get .a1,
    e₆, o₆.get .s5, o₆.get .a1, e₅, o₅.get .s5, o₅.get .a1, e₄, o₄.get .s5, e₃, o₃.get .s5, e₂, o₂.get .s5,
    e₁, o₁.get .s4, o₁.get .s5, Base.drc h]
  exact okbits hrc _

/-- `out` is writable. -/
theorem out_w : ∀ i < kk s, InRegions (fr s :: s.wr) (s.gpr .a0 + BitVec.ofNat 64 i) 1 :=
  fun i hi => by
    rw [P.hwr]
    exact ⟨oR s, by simp, Offset.contains_base _ (by have := P.ok; unfold kk at hi; omega_using [hi, this])
      (by have := P.k2; unfold kk at hi; omega_using [hi])⟩

/-- `*msg_len` is writable. -/
theorem ml_w : InRegions (fr s :: s.wr) (s.gpr .a2 + BitVec.ofNat 64 0) 8 := by
  rw [P.hwr, BitVec.add_zero]
  exact ⟨mlR s, by simp, Region.contains_self _ _⟩

omit P in
/-- The slots and a buffer apart from the stack. -/
theorem slR_dis {R : Region} (h : (kD pc s).Disjoint R) : (slR s).Disjoint R :=
  h.sub_left fun a ha => kR_sub a (slR_sub s a ha)

/-- The buffer's first `k` bytes ANDed with `ok` to `out`. -/
theorem outLoop_ok {t : State} (h : Base (SD s) (VD s rc) (withMem s m) t) :
    WP isa outLoop t fun t' => Saves s t' ∧ t'.rd = s.rd ∧ Kept [.a4, .a5, .a6, .t1] t t' ∧
      t'.mem = writeBytes t.mem (s.gpr .a0)
        ((Spec.Rsa.bytesAt t.mem (off (Sd s) oBuf) (kk s)).map fun b => andB b (t.gpr .s7)) := by
  have PF : Fits (SD s) (withMem s m) := fits P rfl rfl
  have hk1 := P.k1
  have hk2 := P.k2
  have ek : kk s = (s.gpr .a4).toNat := rfl
  have hB : oBuf = 2560 := rfl
  have hR : oRsa = 8192 := rfl
  have hw : t.wr = fr s :: s.wr := h.wr
  unfold outLoop bufBase
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_addi (imm := 2047) fun t₀ o₀ e₀ => wp_addi (imm := 513) fun t₁ o₁ e₁ =>
    wp_mov fun t₂ o₂ e₂ => wp_mov fun t₃ o₃ e₃ => wp_nil ?_)
  have k₃ : Only [.a4, .a5, .a6] t t₃ := (o₀.trans (o₁.trans (o₂.trans o₃))).mono
  have hsep : ∀ j < kk s, ∀ i < kk s, off (Sd s) oBuf + BitVec.ofNat 64 j ≠ s.gpr .a0 + BitVec.ofNat 64 i :=
    fun j hj i hi => ne_of_dis (A := scR s) (B := oR s) P.os.symm (by
      show (scR s).Contains (off (off (Sd s) oBuf) j) 1
      rw [off_off]; exact (sc_sub P) _ (sc_in (n := 1) (by omega_using [hk2, ek, hB, hR, hj]) _ (Region.contains_self _ _)))
      (Offset.contains_base _ (by have := P.ok; omega_using [ek, hi, this]) (by omega_using [ek, hi]))
  refine WP.mono (andCopy_ok (q := off (Sd s) oBuf) (p := s.gpr .a0) (n := kk s) (msk := t.gpr .s7) (by omega_using [hk1, ek])
    (by omega_using [ek]) (by rw [o₃.get .a4, o₂.get .a4, e₁, e₀, h.s0]; exact bufBase_eq _)
    (by rw [o₃.get .a5, e₂, o₁.get .s2, o₀.get .s2, Base.dout h])
    (by rw [e₃, o₂.get .s1, o₁.get .s1, o₀.get .s1, Base.dk h]
        exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm)
    (by rw [k₃.get .s7])
    (fun j hj => by
      rw [k₃.rd, k₃.wr, hw]
      show InRegions _ (off (off (Sd s) oBuf) j) 1
      rw [off_off]; exact sc_inR PF (by omega_using [hk2, ek, hB, hR, hj]) _)
    (by rw [k₃.wr, hw]; exact out_w P) hsep) fun t' ⟨hK, hm⟩ => ?_
  have K : Kept [.a4, .a5, .a6, .t1] t t' := (k₃.keep.trans hK).mono
  have hm' : t'.mem = writeBytes t.mem (s.gpr .a0)
      ((Spec.Rsa.bytesAt t.mem (off (Sd s) oBuf) (kk s)).map fun b => andB b (t.gpr .s7)) := by
    rw [hm, k₃.mem]
  have fr : Frame [oR s] t.mem t'.mem := by
    rw [hm']
    refine writeBytes_frame _ _ _ ?_
    simp only [Region.Contains, BitVec.sub_self, List.length_map, bytesAt_length]
    have := P.ok; unfold kk; simp; omega_using [this]
  exact ⟨Saves.ofMem (h.sv.keep K fr fun r hr => by rw [List.mem_singleton.mp hr]; exact slR_dis P.ko),
    K.rd.trans h.rd, K, hm'⟩

/-- The length and the result. -/
theorem decRet_ok {H : Hash} {D : Nat} (hD : H.D = D) (hD64 : D ≤ 64) {u : State} (sv : Saves s u)
    (h1 : u.gpr .s1 = s.gpr .a4) (h3 : u.gpr .s3 = s.gpr .a2) (h4 : u.gpr .s4 = BitVec.ofNat 64 rc)
    (hrc : rc ≤ 2) {idx : Nat} (h6 : u.gpr .s6 = BitVec.ofNat 64 idx) :
    WP isa (.block (decRet H)) u fun u' => Saves s u' ∧ u'.rd = u.rd ∧
      u'.mem = u.mem.writeW (s.gpr .a2)
        ((s.gpr .a4 - BitVec.ofNat 64 (2 * D + 2) - BitVec.ofNat 64 idx) &&& u.gpr .s7) ∧
      u'.gpr .a0 = (if rc = 2 then 2#64 else 0#64) ||| (u.gpr .s7 &&& 1#64) := by
  subst hD
  unfold decRet faultBit
  simp only [List.cons_append, List.nil_append]
  refine wp_subi (imm := 2 * H.D + 2) (h := by omega_using [hD64]) fun u₁ o₁ e₁ => wp_sub fun u₂ o₂ e₂ =>
    wp_and fun u₃ o₃ e₃ => ?_
  have k₃ : Only [.a1] u u₃ := (o₁.trans (o₂.trans o₃)).mono
  refine wp_sd (a := s.gpr .a2 + BitVec.ofNat 64 0) (by rw [k₃.get .s3, h3])
    (by have := P.alm; rw [BitVec.add_zero]; exact this) (by rw [k₃.wr, sv.wr]; exact ml_w P)
    fun u₄ m₄ => ?_
  refine wp_li (imm := 2) (by decide) fun u₅ o₅ e₅ => wp_xor fun u₆ o₆ e₆ => wp_subi (imm := 1) fun u₇ o₇ e₇ =>
    wp_srl fun u₈ o₈ e₈ => wp_add fun u₉ o₉ e₉ => wp_li (imm := 1) (by decide) fun u₁₀ o₁₀ e₁₀ =>
    wp_and fun u₁₁ o₁₁ e₁₁ => wp_or fun u₁₂ o₁₂ e₁₂ => wp_nil ?_
  have k₁₂ : Only [.a1, .a0] u₄ u₁₂ :=
    (o₅.trans (o₆.trans (o₇.trans (o₈.trans (o₉.trans (o₁₀.trans (o₁₁.trans o₁₂))))))).mono
  have K : Kept [.a1, .a0] u u₁₂ := (k₃.keep.trans (m₄.keep.trans k₁₂.keep)).mono
  have fm : Frame [mlR s] u.mem u₁₂.mem := by
    rw [k₁₂.mem, m₄.mem, k₃.mem, BitVec.add_zero]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨sv.keep K fm fun r hr => by rw [List.mem_singleton.mp hr]; exact slR_dis P.kml, K.rd, ?_, ?_⟩
  · rw [k₁₂.mem, m₄.mem, k₃.mem, BitVec.add_zero, e₃, e₂, e₁, o₁.get .s6, o₂.get .s7, o₁.get .s7, h6, h1]
  · rw [e₁₂, e₁₁, e₁₀, o₁₀.get .s7, o₉.get .s7, o₈.get .s7, o₇.get .s7, o₆.get .s7, o₅.get .s7, m₄.gpr,
      k₃.get .s7, o₁₁.get .a0, o₁₀.get .a0, e₉, e₈, e₇, e₆, e₅, o₅.get .s4, m₄.gpr, k₃.get .s4, h4]
    rw [faultbits hrc]

/-- Zeros to `out` and `*msg_len`, and the result `r = 2 ? 2 : 0`. -/
theorem decFail_ok {t : State} (h : Base (SD s) (VD s rc) (withMem s m) t) (hrc : rc ≤ 2) :
    WP isa decFail t fun u' => Saves s u' ∧ u'.rd = s.rd ∧
      u'.mem = (writeBytes t.mem (s.gpr .a0) (List.replicate (kk s) 0)).writeW (s.gpr .a2) (0#64) ∧
      u'.gpr .a0 = if rc = 2 then 2#64 else 0#64 := by
  have hk1 := P.k1
  have hk2 := P.k2
  have ek : kk s = (s.gpr .a4).toNat := rfl
  have hw : t.wr = fr s :: s.wr := h.wr
  unfold decFail zeroOut faultBit
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (WP.seq (wp_mov fun t₁ o₁ e₁ => wp_mov fun t₂ o₂ e₂ => wp_li (imm := 0) (by decide)
    fun t₃ o₃ e₃ => wp_nil ?_))
  have k₃ : Only [.a1, .t5, .t0] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  refine WP.mono (fill_ok (p := s.gpr .a0) (n := kk s) (b := 0) (by omega_using [hk1, ek]) (by omega_using [ek])
    (by rw [o₃.get .a1, o₂.get .a1, e₁, Base.dout h])
    (by rw [o₃.get .t5, e₂, o₁.get .s1, Base.dk h]
        exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm)
    (by rw [e₃]; rfl)
    (by rw [k₃.wr, hw]; exact out_w P)) fun t₄ ⟨hk, hm⟩ => ?_
  have K₄ : Kept [.a1, .t5, .t0] t t₄ := (k₃.keep.trans hk).mono
  refine wp_li (imm := 0) (by decide) fun t₅ o₅ e₅ => ?_
  refine wp_sd (a := s.gpr .a2 + BitVec.ofNat 64 0) (by rw [o₅.get .s3, K₄.get .s3, Base.dml h])
    (by have := P.alm; rw [BitVec.add_zero]; exact this) (by rw [o₅.wr, K₄.wr, hw]; exact ml_w P)
    fun t₆ m₆ => ?_
  refine wp_li (imm := 2) (by decide) fun u₅ o₅' e₅' => wp_xor fun u₆ o₆ e₆ => wp_subi (imm := 1) fun u₇ o₇ e₇ =>
    wp_srl fun u₈ o₈ e₈ => wp_add fun u₉ o₉ e₉ => wp_nil ?_
  have k₉ : Only [.a1, .a0] t₆ u₉ := (o₅'.trans (o₆.trans (o₇.trans (o₈.trans o₉)))).mono
  have K : Kept [.a1, .t5, .t0, .t1, .a0] t u₉ := (K₄.trans (o₅.keep.trans (m₆.keep.trans k₉.keep))).mono
  have hm' : u₉.mem = (writeBytes t.mem (s.gpr .a0) (List.replicate (kk s) 0)).writeW (s.gpr .a2) (0#64) := by
    rw [k₉.mem, m₆.mem, o₅.mem, hm, k₃.mem, BitVec.add_zero, e₅]
  have fm : Frame [oR s, mlR s] t.mem u₉.mem := by
    rw [hm']
    refine ((writeBytes_frame _ _ _ ?_).mono fun r hr => by simp at hr ⊢; exact .inl hr).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (Region.contains_self _ _)
    simp only [Region.Contains, BitVec.sub_self, List.length_replicate]
    have := P.ok; unfold kk; simp; omega_using [this]
  refine ⟨Saves.ofMem (h.sv.keep K fm fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact slR_dis P.ko
      · exact slR_dis P.kml), K.rd.trans h.rd, hm', ?_⟩
  rw [e₉, e₈, e₇, e₆, e₅', o₅'.get .s4, m₆.gpr, o₅.get .s4, K₄.get .s4, Base.drc h, faultbits hrc]

end

end VG.Proof.RsaOaep.RISCV64.Dec

end

end

/-!
# RSAES-OAEP decryption on RISC-V: correctness

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Dc/Verified.lean`): the entry, the private
operation (`priv_ok`), the check of `k ≥ 2 hLen + 2` (public), then either
zeros and the result `r = 2 ? 2 : 0` (`decFail_ok`, which is what `decOut`
says for a too short `k`) or the decoding (`decMain_ok`), and the restores:
RSAES-OAEP-DECRYPT (RFC 8017 §7.1.2), with the label's hash function and
MGF1's those of the tables, the code for the label's digest length chosen by
`byLen`. `code_correct`: the function against its contract, for the tables
of `vs` (`tab_ofD`: each table is one of them, whose hash function it
names).
-/

@[expose] public section

/-!
## RSAES-OAEP decryption on RISC-V: the decoding

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Dc/Main.lean`): `decMain_ok`, from the private
operation's outcome (`AfterPriv`), the decoding writes what `decOut`
(`Proof/RsaOaep/Decode.lean`) says to `out` and `*msg_len`, and returns its
code, as `writtenDecrypt` takes them.
-/
namespace VG.Proof.RsaOaep.RISCV64.Dec

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64 VG.Impl.RsaOaep.RISCV64.Dec VG.WriteBytes
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaPkcs1Sig (bytesAt_length bytesAt_writeBytes)
open VG.Proof.RsaOaep.RISCV64 (Base Saves view off off_off bytes_entry bytesAt_view TabS)
open VG.Proof.RsaOaep (mixV srcB mk scanS accG zM decOut decode_eq scanS_inv accG_eq_zero or_eq_zero mk_eq_zero
  scan_found scan_fail scan_idx out_list out_zero lk bad srcB_eq scanS_congr map_range_getD')
open VG.Proof.RsaPss.RISCV64 (shV shV_eq)
open VG.Proof.Mgf1 (ifp ifn)

/-- The label, from the entry state. -/
abbrev labB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 10).toNat

theorem writeBytes_at (m : Mem) (q : Addr) (xs : List Byte) {i : Nat} (hi : i < xs.length) (hl : xs.length < 2 ^ 64) :
    writeBytes m q xs (q + BitVec.ofNat 64 i) = xs.getD i 0 := by
  simp only [writeBytes, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hi, hl] : i < 2 ^ 64)]
  rw [ifp hi]

section
variable {pc : Bool} {s : State} (P : PreD pc s)
include P

theorem labB_eq {m : Mem} (hm : Frame [kD pc s, scR s] s.mem m) :
    Spec.Rsa.bytesAt m (stackArg s 9) (stackArg s 10).toNat = labB s :=
  bytes_entry hm P.kl P.ls.symm (by have := (stackArg s 10).isLt; omega_using [])

/-- The decoding, after the private operation's outcome. -/
theorem decMain_ok {H G : Hash} (hH : HashOK H) (hG : HashOK G) (hHF : H.F ≤ 208) (hGF : G.F ≤ 208)
    {Hs Gs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D)
    (hHv : Proof.Mgf1.Valid Hs) (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D)
    (hGv : Proof.Mgf1.Valid Gs) {f : Fns} (T : TabS G f 16 (SD s) s (stackArg s 16))
    (TL : TabS H f 15 (SD s) s (stackArg s 15)) {v : State}
    (A : AfterPriv pc s v) (hsy : v.syms = s.syms) (hk : 2 * H.D + 2 ≤ kk s) :
    WP isa (decMain H f) v fun u => Saves s u ∧ u.rd = s.rd ∧
      Spec.RsaOaep.writtenDecrypt u.mem (s.gpr .a0) (s.gpr .a2) (kk s) ((u.gpr .a0).setWidth 32)
        (decOut Hs Gs (labB s) (privO s)) := by
  have hD0 := hH.hD0
  have hD64 := hH.hD64
  have hk2 := P.k2
  have ek : kk s = (s.gpr .a4).toNat := rfl
  have hrc := rcOf_le (privO s)
  obtain ⟨hE, hSt, hDg, hB, hRs⟩ := offs'
  generalize hD : H.D = D at *
  generalize hO : privO s = o at *
  generalize hRC : rcOf o = rc at *
  have b0 := A.base
  rw [hO, hRC] at b0
  unfold decMain
  -- `EM` unmasked.
  refine unmask_ok P hG hGF (tabS_wm P T A.mem) hGh hGl hGv hD hD0 (by omega_using [hD64]) (by omega_using [hk]) b0 hsy
    fun t₁ b₁ y₁ v₁ => ?_
  -- The label's hash, through its table.
  refine WP.seq (WP.mono (hashLabelT_ok P hH hHF A.mem (tabS_wmL P TL A.mem) b₁ y₁) fun t₂ ⟨⟨b₂, _, s₂, h₂⟩, _⟩ => ?_)
  -- `lHash'` against `lHash`.
  refine WP.seq (WP.mono (accLh_ok P hD hD0 (by omega_using [hD64]) (by omega_using [hk]) b₂) fun t₃ ⟨b₃, m₃, g₃, a₃⟩ => ?_)
  -- The scan.
  refine WP.seq (WP.mono (scan_ok P hD (by omega_using [hD64]) (by omega_using [hk]) b₃) fun t₄ ⟨b₄, m₄, g₄, a₄, i₄⟩ => ?_)
  -- The buffer.
  refine WP.seq (WP.mono (clearBuf_ok P b₄) fun t₅ ⟨b₅, g₅, v₅⟩ => ?_)
  refine WP.seq (WP.mono (copyT_ok P hD (by omega_using [hD64]) (by omega_using [hk]) b₅) fun t₆ ⟨b₆, g₆, v₆⟩ => ?_)
  generalize hsc : scanS (fun i => view t₃.mem (Sd s) (1 + 2 * D + i)) (t₃.gpr .s5) (kk s - (2 * D + 1)) = sc
    at a₄ i₄
  obtain ⟨idx, hidx, hidx'⟩ := scan_idx (fun i => view t₃.mem (Sd s) (1 + 2 * D + i)) (t₃.gpr .s5)
    (kk s - (2 * D + 1))
  rw [hsc] at hidx
  have h6 : t₆.gpr .s6 = BitVec.ofNat 64 idx := by
    rw [g₆.get .s6, g₅.get .s6, i₄, hidx]
  refine WP.seq (WP.mono (shift_ok P b₆ h6 (by omega_using [hk, hidx'])) fun t₇ ⟨b₇, k₇, v₇⟩ => ?_)
  -- `ok`, `out`, the length and the result.
  refine WP.seq (WP.mono (okMask_ok P b₇ (by omega_using [hrc])) fun t₈ ⟨b₈, m₈, g₈, o₈⟩ => ?_)
  refine WP.seq (WP.mono (outLoop_ok P b₈) fun t₉ ⟨sv₉, rd₉, g₉, m₉⟩ => ?_)
  refine WP.mono (decRet_ok P hD (by omega_using [hD64]) (rc := rc) (idx := idx) sv₉
    (by rw [g₉.get .s1, g₈.get .s1, Base.dk b₇]) (by rw [g₉.get .s3, g₈.get .s3, Base.dml b₇])
    (by rw [g₉.get .s4, g₈.get .s4, Base.drc b₇]) (by omega_using [hrc])
    (by rw [g₉.get .s6, g₈.get .s6, k₇.get .s6, h6])) fun u ⟨svu, rdu, mu, ru⟩ =>
    ⟨svu, rdu.trans rd₉, ?_⟩
  -- The views.
  have hS : ∀ {x}, x < oSt → ∀ p ∈ [(oSt, H.S), (oDig, H.D)], x < p.1 ∨ p.1 + p.2 ≤ x :=
    fun hx p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> exact .inl (by simp only; omega_arith)
  have e2 : ∀ x < oSt, view t₂.mem (Sd s) x = view t₁.mem (Sd s) x := fun x hx => s₂ x (by omega_using [hSt, hRs, hx]) (hS hx)
  have hlab : Spec.Rsa.bytesAt v.mem (stackArg s 9) (stackArg s 10).toNat = labB s := labB_eq P A.mem
  rw [hlab] at h₂
  have hlh : ∀ i < D, view t₂.mem (Sd s) (oDig + i) = (Hs.hash (labB s)).getD i 0 := fun i hi => by
    have := congrArg (fun l => l.getD i 0) h₂
    rw [bytesAt_view, srcB, map_range_getD' _ (by omega_using [hD, hi])] at this
    rw [this, hHh]
  -- `lHash'`, `lHash` and the scan, on the view after unmasking.
  have hc0 : t₃.gpr .s5 = accG (view t₁.mem (Sd s) 0) (fun i => view t₁.mem (Sd s) (1 + D + i))
      (fun i => view t₂.mem (Sd s) (oDig + i)) D := by
    rw [a₃, e2 0 (by omega_using [hSt])]
    exact accG_congr _ D (fun i hi => e2 _ (by omega_using [hSt, hD64, hi])) (fun _ _ => rfl)
  have hsc' : sc = scanS (fun i => view t₁.mem (Sd s) (1 + 2 * D + i)) (accG (view t₁.mem (Sd s) 0)
      (fun i => view t₁.mem (Sd s) (1 + D + i)) (fun i => view t₂.mem (Sd s) (oDig + i)) D) (kk s - (2 * D + 1)) := by
    rw [← hsc, hc0, m₃]
    exact scanS_congr _ _ fun i hi => e2 _ (by omega_using [hk2, ek, hSt, hi])
  rw [hsc'] at hidx
  have r5 : t₇.gpr .s5 = sc.2.2 ||| sc.1 := by
    rw [k₇.get .s5, g₆.get .s5, g₅.get .s5, a₄]
  have hok : t₉.gpr .s7 = mk (rcOf o = 1 ∧ (sc.2.2 ||| sc.1) = 0) := by
    rw [g₉.get .s7, o₈, r5, ← hRC]
  rw [hsc'] at hok
  -- The buffer.
  have hT : ∀ y < 2048, view t₆.mem (Sd s) (oBuf + y) =
      (srcB (view t₁.mem (Sd s)) (1 + 2 * D) (kk s - (2 * D + 1))).getD y 0 := by
    intro y hy
    rw [v₆ _ (by omega_using [hB, hRs, hy])]
    by_cases hyt : y < kk s - (2 * D + 1)
    · rw [ifp ⟨by omega_using [], by omega_using [hyt]⟩, show oBuf + y - oBuf = y by omega_using [], v₅ _ (by omega_using [hRs, hD64, hy]), ifn (by omega_using [hB, hD64, hy]), m₄, m₃,
        e2 _ (by omega_using [hk2, ek, hSt, hyt]), srcB, map_range_getD' _ hyt]
    · rw [ifn (by omega_using [hyt]), v₅ _ (by omega_using [hB, hRs, hy]), ifp ⟨by omega_using [], by omega_using [hy]⟩]
      simp [srcB, List.getD_eq_getElem?_getD, hyt]
  have hbuf : ∀ i < kk s, view t₇.mem (Sd s) (oBuf + i) =
      (srcB (view t₁.mem (Sd s)) (1 + 2 * D) (kk s - (2 * D + 1))).getD (i + (idx + 1)) 0 := by
    intro i hi
    rw [v₇ _ (by omega_using [hk2, ek, hB, hRs, hi]), shV_eq _ (by omega_using [hk2, ek, hidx']) (fun x h₁ h₂ => by
      rw [hT x (by omega_using [hk2, ek, h₂])]; simp [srcB, List.getD_eq_getElem?_getD, show ¬ x < kk s - (2 * D + 1) by omega_using [h₁]]) hi]
    by_cases hl : i + (idx + 1) < kk s
    · rw [ifp hl, hT _ (by omega_using [hk2, ek, hidx', hi])]
    · rw [ifn hl]; simp [srcB, List.getD_eq_getElem?_getD, show ¬ i + (idx + 1) < kk s - (2 * D + 1) by omega_using [hl]]
  -- `out`, `*msg_len` and the result.
  have hu : ∀ x, ¬ (mlR s).Contains x 1 → u.mem x = t₉.mem x := fun x hx => by
    rw [mu]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self (mlR s)) _ (Region.contains_self _ _)) x
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact hx)
  have hlen : ((Spec.Rsa.bytesAt t₈.mem (off (Sd s) oBuf) (kk s)).map fun b => andB b (t₈.gpr .s7)).length =
      kk s := by simp [bytesAt_length]
  have hout : ∀ i < kk s, u.mem (s.gpr .a0 + BitVec.ofNat 64 i) =
      andB ((srcB (view t₁.mem (Sd s)) (1 + 2 * D) (kk s - (2 * D + 1))).getD (i + (idx + 1)) 0) (t₉.gpr .s7) := by
    intro i hi
    rw [hu _ (fun hc => P.oml _ (Offset.contains_base _ (by have := P.ok; omega_using [ek, hi, this]) (by omega_using [ek, hi])) hc), m₉]
    rw [writeBytes_at _ _ _ (by rw [hlen]; exact hi) (by rw [hlen]; omega_using [ek]), List.getD_eq_getElem?_getD,
      List.getElem?_map, Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range hi]
    simp only [Option.map_some, Option.getD_some]
    rw [g₉.get .s7]
    congr 1
    rw [m₈, ← hbuf i hi]; show t₇.mem (off (off (Sd s) oBuf) i) = _; rw [off_off]; rfl
  have hml : u.mem.readW (s.gpr .a2) 64 = (BitVec.ofNat 64 (kk s) - BitVec.ofNat 64 (2 * D + 2) -
      BitVec.ofNat 64 idx) &&& t₉.gpr .s7 := by
    rw [mu, Mem.readW_writeW_self64, show s.gpr .a4 = BitVec.ofNat 64 (kk s) from
      (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm]
  rw [hok] at hout hml ru
  exact dec_written hGv hHv hHl (by omega_using [hk]) hk2 v₁ hlh (fun em he => by
      have := A.em; rw [hO, he] at this; exact this.symm)
    hidx (by rcases hidx' with h | h; exact .inl h; exact .inr h) hout hml (by rw [ru, hRC])

end

end VG.Proof.RsaOaep.RISCV64.Dec


namespace VG.Proof.RsaOaep.RISCV64.Dec

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64 VG.Impl.RsaOaep.RISCV64.Dec VG.WriteBytes
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only wp_li wp_sub wp_srl wp_nil eval_nonzero)
open VG.Proof.RsaPkcs1Sig (bytesAt_length bytesAt_writeBytes)
open VG.Proof.RsaOaep.RISCV64 (Saves restore_ok ne_zero_ltBit TabS)
open VG.Proof.MdHashTable.RISCV64 (MVar tables fns3 Coh)
open VG.Proof.RsaOaep (decOut decOut_short)
open VG.Proof.Mgf1 (ifp ifn)

private theorem writtenDecrypt_lost {m m' : Mem} {out len : Addr} {k : Nat} {r r' : BitVec 32}
    {o : Spec.Rsa.Outcome} (hr : r' = r) (hb : Spec.Rsa.bytesAt m' out k = Spec.Rsa.bytesAt m out k)
    (hw : m'.readW len 64 = m.readW len 64) (h : Spec.RsaOaep.writtenDecrypt m out len k r o) :
    Spec.RsaOaep.writtenDecrypt m' out len k r' o := by
  subst hr
  cases o <;> simp only [Spec.RsaOaep.writtenDecrypt, hb, hw] at h ⊢ <;> exact h

/-- The result and the outputs, from the entry state `s`. -/
def Post (Hs Gs : Spec.Mgf1.Hash) (s s' : State) : Prop :=
  abiPreserved s s' ∧ Spec.RsaOaep.writtenDecrypt s'.mem (s.gpr .a0) (s.gpr .a2) (kk s) ((s'.gpr .a0).setWidth 32)
    (decOut Hs Gs (labB s) (privO s))

/-- Before the restores. -/
def Done (Hs Gs : Spec.Mgf1.Hash) (s t : State) : Prop :=
  Saves s t ∧ Spec.RsaOaep.writtenDecrypt t.mem (s.gpr .a0) (s.gpr .a2) (kk s) ((t.gpr .a0).setWidth 32)
    (decOut Hs Gs (labB s) (privO s))

theorem AfterPriv.only {pc : Bool} {s v v' : State} {rs : List Reg} (A : AfterPriv pc s v) (P : PreD pc s) (o : Only rs v v')
    (hrs : ∀ r ∈ rs, r ∉ Proof.RsaOaep.RISCV64.fixed := by decide) : AfterPriv pc s v' := by
  have hm : v'.mem = v.mem := o.mem
  have b := A.base
  rw [← hm] at b
  exact ⟨b.only (fits P rfl rfl) o hrs, hm ▸ A.mem, hm ▸ A.em⟩

/-- The tail for a digest length, which is all it uses of the hash
function's shape. -/
theorem decTail_D {G G' : Hash} (hD : G.D = G'.D) (f : Fns) : decTail G f = decTail G' f := by
  simp only [Dec.decTail, Dec.decMain, chkK, Dec.accLh, Dec.scan, Dec.tArgs, Dec.copyT, Dec.decRet, seedArgs,
    dbArgs, hD]

/-- `EM` too short for the hash: what decryption returns, from the private
operation's result. -/
theorem decOut_short' {Hs Gs : Spec.Mgf1.Hash} {lab : List Byte} {o : Spec.Rsa.Outcome} {k : Nat}
    (hl : ∀ em, o = .ok em → em.length = k) (hk : k < 2 * Hs.len + 2) :
    decOut Hs Gs lab o = if rcOf o = 2 then .fault else .invalid := by
  rw [decOut_short hl hk]
  cases o <;> rfl

section
variable {H G : Hash} (hH : HashOK H) (hG : HashOK G) (fH : H.F ≤ 208) (fG : G.F ≤ 208)
  {Hs Gs : Spec.Mgf1.Hash}
  (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D) (hHv : Proof.Mgf1.Valid Hs)
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs)
  {f : Fns} {pc : Bool} {s : State} (P : PreD pc s) (T : TabS G f 16 (SD s) s (stackArg s 16))
  (TL : TabS H f 15 (SD s) s (stackArg s 15))
include hH hG fH fG hHh hHl hHv hGh hGl hGv P T TL

omit hH hG fH fG hHh hHv hGh hGl hGv T TL in
theorem fail_done {v : State} (A : AfterPriv pc s v) (hk : kk s < 2 * H.D + 2) :
    WP isa decFail v (Done Hs Gs s) := by
  have hrc := rcOf_le (privO s)
  refine WP.mono (decFail_ok P A.base hrc) fun u ⟨sv, _, hm, h3⟩ => ⟨sv, ?_⟩
  have hk2 := P.k2
  have ek : kk s = (s.gpr .a4).toNat := rfl
  have hl : ∀ em, privO s = .ok em → em.length = kk s := fun em he => by
    have := A.em; rw [he] at this; simp only [emOf] at this; rw [← this, bytesAt_length]
  rw [decOut_short' hl (by rw [hHl]; exact hk)]
  have hout : Spec.Rsa.bytesAt u.mem (s.gpr .a0) (kk s) = List.replicate (kk s) 0 := by
    have e := bytesAt_writeBytes v.mem (s.gpr .a0) (List.replicate (kk s) 0)
      (by rw [List.length_replicate]; omega_using [ek])
    rw [List.length_replicate] at e
    rw [← e, hm]
    have f : Frame [mlR s] (writeBytes v.mem (s.gpr .a0) (List.replicate (kk s) 0))
        ((writeBytes v.mem (s.gpr .a0) (List.replicate (kk s) 0)).writeW (s.gpr .a2) (0#64)) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    exact f _ (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact fun hc => P.oml _ (Offset.contains_base _ (by have := P.ok; omega_using [ek, hi, this]) (by omega_using [ek, hi])) hc)
  have hml : u.mem.readW (s.gpr .a2) 64 = 0 := by rw [hm, Mem.readW_writeW_self64]; rfl
  by_cases h2 : rcOf (privO s) = 2
  · rw [ifp h2]; exact ⟨by rw [h3, ifp h2]; decide, hout, hml⟩
  · rw [ifn h2]; exact ⟨by rw [h3, ifn h2]; decide, hout, hml⟩

omit hH hG fH fG hHh hHl hHv hGh hGl hGv T TL in
/-- The check of `k`: in `a0`, whether it is too short. -/
theorem chk_ok (hD64 : H.D ≤ 64) {v : State} (A : AfterPriv pc s v) :
    WP isa (.block (chkK H)) v fun v' => AfterPriv pc s v' ∧ (v'.gpr .a0 != 0) = decide (kk s < 2 * H.D + 2) := by
  have hk2 := P.k2
  have ek : kk s = (s.gpr .a4).toNat := rfl
  refine wp_li (imm := 2 * H.D + 2) (by omega_using [hD64]) fun v₁ o₁ e₁ => wp_sub fun v₂ o₂ e₂ => wp_srl fun v₃ o₃ e₃ =>
    wp_nil ?_
  have k₃ : Only [.a0] v v₃ := (o₁.trans (o₂.trans o₃)).mono
  refine ⟨A.only P k₃, ?_⟩
  rw [e₃, e₂, e₁, o₁.get .s1, Base.dk A.base, show s.gpr .a4 = BitVec.ofNat 64 (s.gpr .a4).toNat by simp]
  exact ne_zero_ltBit (by omega_using [hk2]) (by omega_using [hD64])

/-- The branch on the check of `k`. -/
theorem ite_done {v : State} (A : AfterPriv pc s v) (hsy : v.syms = s.syms)
    (r0 : (v.gpr .a0 != 0) = decide (kk s < 2 * H.D + 2)) :
    WP isa (.ite (.nonzero .a0) decFail (decMain H f)) v (Done Hs Gs s) :=
  WP.ite _ (eval_nonzero _ _) (fun hc => fail_done hHl P A (by rw [r0] at hc; simpa using hc))
    (fun hc => WP.mono (decMain_ok P hH hG fH fG hHh hHl hHv hGh hGl hGv T TL A hsy
      (by rw [r0] at hc; simp at hc; omega_using [hc])) fun u ⟨sv, _, hw⟩ => ⟨sv, hw⟩)

theorem checks_done {v : State} (A : AfterPriv pc s v) (hsy : v.syms = s.syms) :
    WP isa (.block (chkK H)) v fun v' =>
      WP isa (.ite (.nonzero .a0) decFail (decMain H f)) v' (Done Hs Gs s) :=
  WP.mono_syms (chk_ok P hH.hD64 A) fun _ ⟨A', r0⟩ y =>
    ite_done hH hG fH fG hHh hHl hHv hGh hGl hGv P T TL A' (y.trans hsy) r0

theorem code_ok (hl : H.D ∈ lens) : WP isa (decryptG f pc) s (Post Hs Gs s) := by
  have hD64 := hH.hD64
  refine WP.allocLe (by decide) (by have := P.sp1; have := stackBytes_ge pc; unfold frameBytes; omega_arith) ?_
  refine WP.seq (WP.mono_syms (entry_ok P) fun t E y₁ => ?_)
  refine WP.seq (WP.mono_syms (priv_ok P E) fun v A y₂ => ?_)
  -- The label's hash function's digest length to `a0`.
  have TL' := tabS_wmL P TL A.mem
  refine WP.seq (WP.of_syms ?_)
  show WP isa (.block (tword .a0 15 6 ++ [])) v _
  refine wp_tword TL' A.base (k := 6) (by decide) (d := .a0) fun v₁ o₁ e₁ => wp_nil fun y₃ => ?_
  have e0 : v₁.gpr .a0 = BitVec.ofNat 64 H.D := e₁.trans TL'.d
  -- The code for that length.
  refine WP.seq (byLen_ok (D := H.D) (by omega_using [hD64])
    (F := fun u => AfterPriv pc s u ∧ u.syms = s.syms ∧ u.gpr .a0 = BitVec.ofNat 64 H.D)
    (fun _ h => h.2.2) (fun u u' ⟨A', y', r0'⟩ o y => ⟨A'.only P o, y.trans y', by rw [o.get .a0]; exact r0'⟩) ?_
    hl (fun x hx => (lens_certs x hx).1) v₁ ⟨A.only P o₁, y₃.trans (y₂.trans y₁), e0⟩)
  intro u ⟨A', y', _⟩
  rw [decTail_D (G := ofLen H.D) (G' := H) rfl]
  exact WP.seq (WP.mono (checks_done hH hG fH fG hHh hHl hHv hGh hGl hGv P T TL A' y') fun v' h => WP.mono h
    fun t' ⟨sv, res⟩ => WP.mono (restore_ok sv (fb_al8 P)) fun w ⟨habi, h3, hm⟩ m _ fl =>
      ⟨⟨habi.1, habi.2.1, habi.2.2⟩, by
      show Spec.RsaOaep.writtenDecrypt m _ _ _ ((w.gpr .a0).setWidth 32) _
      have fs : Region.Sub ⟨Proof.RsaOaep.RISCV64.fb s + BitVec.ofNat 64 0, frameBytes⟩ (kD pc s) :=
        fun a h => kR_sub a (Proof.RsaOaep.RISCV64.frame_sub s (Nat.le_refl _) a h)
      rw [BitVec.add_zero] at fs
      refine writtenDecrypt_lost (congrArg _ h3) ?_ ?_ res
      · rw [← hm]
        exact List.map_congr_left fun i hi => lost_byte fl (R := ⟨s.gpr .a0, kk s⟩)
          (by rw [show kk s = (s.gpr .a1).toNat from P.ok.symm]; exact (P.ko.sub_left fs).symm) (List.mem_range.mp hi)
      · rw [← hm]
        exact fl.readW (r := mlR s) (by simp only [Region.Contains]; rw [BitVec.sub_self]; decide)
          (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact (P.kml.sub_left fs).symm)
          (by decide)⟩)

end

/-- The label's hash function's table, on entry, if it is `w`'s: what its
calls need of it. -/
theorem tabS_entryDL {vs : List MVar} (hc : Coh vs) {pc : Bool} {s : State} (P : PreD pc s)
    (hpw : (Proof.MdHashTable.RISCV64.names vs).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g) {w : MVar}
    (hw : w ∈ vs)
    (hh : Abi.tableHeld 64 s.mem (stackArg s 15) (FnTable.words isa s (Proof.MdHashTable.RISCV64.tableOf w))) :
    TabS w.w.H (fns3 vs) 15 (SD s) s (stackArg s 15) := by
  refine Proof.MdHashTable.RISCV64.tabS_of (by decide) rfl (arg_al P (by decide)) P.altl P.wtl (A := aR pc s)
    (by rw [P.hrd]; cases pc <;> simp) (in_aR (by decide)) ?_ (P.ka.sub_left kR_sub) (P.sa.sub_left (sc_sub P))
    (by rw [P.hrd]; exact List.mem_append_right _ (List.mem_cons_self ..)) (P.ktl.sub_left kR_sub)
    (P.stl.sub_left (sc_sub P)) hc hpw hw hh
  rw [Proof.RsaOaep.RISCV64.stackArgAddr_eq]
  exact Offset.sub_base _ (by split <;> omega_using [])

/-- MGF1's table, on entry, if it is `w`'s: what MGF1 needs of it. -/
theorem tabS_entryD {vs : List MVar} (hc : Coh vs) {pc : Bool} {s : State} (P : PreD pc s)
    (hpw : (Proof.MdHashTable.RISCV64.names vs).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g) {w : MVar}
    (hw : w ∈ vs)
    (hh : Abi.tableHeld 64 s.mem (stackArg s 16) (FnTable.words isa s (Proof.MdHashTable.RISCV64.tableOf w))) :
    TabS w.w.H (fns3 vs) 16 (SD s) s (stackArg s 16) := by
  refine Proof.MdHashTable.RISCV64.tabS_of (by decide) rfl (arg_al P (by decide)) P.alt P.wt (A := aR pc s)
    (by rw [P.hrd]; cases pc <;> simp) (in_aR (by decide)) ?_ (P.ka.sub_left kR_sub) (P.sa.sub_left (sc_sub P))
    (by rw [P.hrd]; exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    (P.kt.sub_left kR_sub) (P.st.sub_left (sc_sub P)) hc hpw hw hh
  rw [Proof.RsaOaep.RISCV64.stackArgAddr_eq]
  exact Offset.sub_base _ (by split <;> omega_using [])

/-- The tables, on entry: each one of the tables of `vs`, which names its
hash function and holds what the calls through it need. -/
theorem tab_ofG {vs : List MVar} (hc : Coh vs) {pc : Bool} {s : State} (P : PreD pc s)
    (ht : (∃ T ∈ tables vs, Abi.tableHeld 64 s.mem (stackArg s 15) (FnTable.words isa s T)) ∧
      (∃ T ∈ tables vs, Abi.tableHeld 64 s.mem (stackArg s 16) (FnTable.words isa s T)) ∧
      (((tables vs).map (fun T : FnTable => T.fns)).flatten ++
        ((tables vs).map (fun T : FnTable => T.fns)).flatten).Pairwise (fun f g => f ≠ g → s.syms f ≠ s.syms g)) :
    ∃ w₁ ∈ vs, ∃ w ∈ vs, Spec.MdHashTable.hashAt 64 s.mem (stackArg s 15) = some w₁.w.l.G ∧
      Spec.MdHashTable.hashAt 64 s.mem (stackArg s 16) = some w.w.l.G ∧
      TabS w₁.w.H (fns3 vs) 15 (SD s) s (stackArg s 15) ∧ TabS w.w.H (fns3 vs) 16 (SD s) s (stackArg s 16) := by
  obtain ⟨⟨T₁, hT₁, hh₁⟩, ⟨T, hT, hh⟩, hpw⟩ := ht
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  have hpw' := hpw.sublist (List.sublist_append_left _ _)
  exact ⟨w₁, hw₁, w, hw, Proof.MdHashTable.RISCV64.hashAt_tableOf (Proof.MdHashTable.RISCV64.held_tableOf hh₁).2,
    Proof.MdHashTable.RISCV64.hashAt_tableOf (Proof.MdHashTable.RISCV64.held_tableOf hh).2,
    tabS_entryDL hc P hpw' hw₁ hh₁, tabS_entryD hc P hpw' hw hh⟩

theorem tab_ofD {vs : List MVar} (hc : Coh vs) {s : State} (h : (decSpec (tables vs)).pre s) :
    ∃ w₁ ∈ vs, ∃ w ∈ vs, Spec.MdHashTable.hashAt 64 s.mem (stackArg s 15) = some w₁.w.l.G ∧
      Spec.MdHashTable.hashAt 64 s.mem (stackArg s 16) = some w.w.l.G ∧
      TabS w₁.w.H (fns3 vs) 15 (SD s) s (stackArg s 15) ∧ TabS w.w.H (fns3 vs) 16 (SD s) s (stackArg s 16) :=
  tab_ofG hc (preD_of h) (spec_tabD h)

/-- The correctness of `vg_rsa_oaep_decrypt`, against its contract, for the
tables of `vs`. -/
theorem code_correct {vs : List MVar} (hc : Coh vs) (s : State) (h : (decSpec (tables vs)).pre s) :
    ∃ t s', Exec isa (decrypt (fns3 vs)) s t s' ∧ abiPreserved s s' ∧ (decSpec (tables vs)).post s s' := by
  obtain ⟨w₁, -, w, -, hH, hG, TL, T⟩ := tab_ofD hc h
  have P : PreD false s := preD_of h
  obtain ⟨t, s', he, habi, hr⟩ := code_ok w₁.w.l.ok w.w.l.ok w₁.w.l.fits w.w.l.fits w₁.w.l.hash w₁.w.l.len w₁.w.l.valid
    w.w.l.hash w.w.l.len w.w.l.valid P T TL w₁.w.l.lens_mem
  refine ⟨t, s', he, habi, ?_⟩
  have e : stackBytes false = 3471 + 1 := rfl
  unfold decSpec
  rw [e]
  sig_post [Spec.RsaOaep.decryptMdTablesContract, Spec.RsaOaep.decryptMdTablesSig, Spec.RsaOaep.decryptSig,
    Spec.MdHashTable.param, Abi.withTables, abi, argRegs, stackArgs_seventeen, List.append_eq]
  intro H' G' hH' hG'
  rw [hH] at hH'
  rw [hG] at hG'
  cases hH'
  cases hG'
  rw [Proof.RsaOaep.decrypt_eq (by rw [bytesAt_length, bytesAt_length])]
  exact hr

end VG.Proof.RsaOaep.RISCV64.Dec
