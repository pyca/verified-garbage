module

public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Priv
import VerifiedGarbage.Proof.RsaOaep.RISCV64.Main
import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Encode
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Mgf1.Bytes

/-!
# RSAES-OAEP decryption on RISC-V: the buffer

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Dc/Buf.lean`): `clearBuf_ok`, the buffer's 2048
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
variable {s : State} (P : PreD s) {m : Mem} {rc : Nat}
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
    (sc_w PF (by rw [k₅.wr, h.wr]) (by omega))) fun t' ⟨hk, hm⟩ => ?_
  have hK : Kept [.a1, .t5, .t0] t t' := (k₅.keep.trans hk).mono
  have hm' : t'.mem = writeBytes t.mem (off (Sd s) oBuf) (List.replicate 2048 0) := by rw [hm, k₅.mem]
  refine ⟨h.wb PF hK (by rw [List.length_replicate]; omega) hm', hK, fun o ho => ?_⟩
  rw [hm', view_wb _ _ (by rw [List.length_replicate]; omega) ho, List.length_replicate]
  split
  · rename_i hc
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, ifp (by omega)]; rfl
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
  refine WP.seq (wp_addi (imm := oEm + 1 + 2 * H.D) (h := by unfold oEm; omega) fun t₁ o₁ e₁ =>
    wp_addi (imm := 2047) fun t₂ o₂ e₂ => wp_addi (imm := 513) fun t₃ o₃ e₃ =>
    wp_subi (imm := 2 * H.D + 1) (h := by omega) fun t₄ o₄ e₄ => wp_nil ?_)
  have k₄ : Only [.a4, .a1, .a5] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  have hn : t₄.gpr .a5 = BitVec.ofNat 64 (kk s - (2 * H.D + 1)) := by
    rw [e₄, o₃.get .s1, o₂.get .s1, o₁.get .s1, Base.dk h, sub_k (by omega)]
  refine WP.mono (copy_ok (q := off (Sd s) (1 + 2 * H.D)) (p := off (Sd s) oBuf) (n := kk s - (2 * H.D + 1))
    (by omega) (by omega) (by rw [o₄.get .a1, e₃, e₂, o₁.get .s0, h.s0]; exact bufBase_eq _)
    (by rw [o₄.get .a4, o₃.get .a4, o₂.get .a4, e₁, h.s0, hE, Nat.zero_add]) hn
    (fun j hj => by
      rw [k₄.rd, k₄.wr, h.wr]
      show InRegions _ (off (off (Sd s) (1 + 2 * H.D)) j) 1
      rw [off_off]; exact sc_inR PF (by omega) _)
    (sc_w PF (by rw [k₄.wr, h.wr]) (by omega))
    (fun j hj i hi => by
      show off (off (Sd s) (1 + 2 * H.D)) j ≠ off (off (Sd s) oBuf) i
      rw [off_off, off_off]
      exact Offset.add_ofNat_ne _ (by omega) (by omega) (by omega))) fun t' ⟨hk', hm⟩ => ?_
  have hK : Kept [.t0, .a4, .a1, .a5] t t' := (k₄.keep.trans hk').mono
  have hm' : t'.mem = writeBytes t.mem (off (Sd s) oBuf)
      (Spec.Rsa.bytesAt t.mem (off (Sd s) (1 + 2 * H.D)) (kk s - (2 * H.D + 1))) := by rw [hm, k₄.mem]
  refine ⟨h.wb PF hK (by rw [bytesAt_length]; omega) hm', hK, fun o ho => ?_⟩
  rw [hm', view_wb _ _ (by rw [bytesAt_length]; omega) ho, bytesAt_length]
  split
  · rename_i hc
    simp only [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (show o - oBuf < kk s - (2 * H.D + 1) by omega), Option.map_some, Option.getD_some]
    show t.mem (off (off (Sd s) (1 + 2 * H.D)) (o - oBuf)) = _
    rw [off_off]; rfl
  · rfl

end

end VG.Proof.RsaOaep.RISCV64.Dec
