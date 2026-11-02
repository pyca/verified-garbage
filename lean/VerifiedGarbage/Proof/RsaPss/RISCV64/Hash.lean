module

public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Base
public import VerifiedGarbage.Impl.RsaPss.RISCV64
public import VerifiedGarbage.Proof.RsaPss.RISCV64.Pre
import VerifiedGarbage.Proof.RsaPss.RISCV64.Prefix
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSASSA-PSS verification on RISC-V: the hash calls, and `H'` for a given salt length

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPss/PPC64LE/Hash.lean`, `Fixed.lean`): `hInit_ok`, `hUpd_ok`
and `hFin_ok`, the calls of the streaming functions on the state at
`S + oSt` (by `init_ok`, `upd_ok` and `fin_ok`, shared with RSAES-OAEP
encryption), `update`'s data in our part of the working space after the
ranges the calls write (`oY` on); `hashFixedG_ok`, `hashFixed` writes the
digest of the `8 + hLen + salt_len` bytes of `M'` at `oY` to `oDig`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64

open VG VG.RISCV64 VG.Impl.RsaPss.RISCV64
open VG.Impl.RsaOaep.RISCV64 (oEm oSt oDig oCtr oRsa)
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaOaep.RISCV64 (Base Fits SC off off_off view sc_in sc_inR sc_inW sc_cov sdis cR_dis fx
  Same init_ok upd_ok fin_ok hfits offs)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo wp_li wp_addi wp_nil)

theorem pres_of {rs : List Reg} {t t' : State} (o : Only rs t t') (hrs : ∀ r ∈ rs, r ∉ preserved := by decide) :
    ∀ r ∈ preserved, t'.gpr r = t.gpr r := fun r hr => o.gpr r fun h => hrs r h hr

/-- Bytes of our part of the working space outside the ranges a `Same` covers. -/
theorem bytes_same {S : Addr} {t t' : State} {rgs : List (Nat × Nat)} (h : Same S t t' rgs) {d n : Nat}
    (hd : d + n ≤ oRsa) (hr : ∀ p ∈ rgs, d + n ≤ p.1 ∨ p.1 + p.2 ≤ d) :
    Spec.Sha256.bytesAt t'.mem (off S d) n = Spec.Sha256.bytesAt t.mem (off S d) n := by
  simp only [Spec.Sha256.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have := h (d + i) (by omega) fun p hp => by have := hr p hp; omega
  simp only [view] at this
  rw [← off_off] at this
  exact this

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {s : State} (F : Fits S s) {H : Hash} (hH : HashOK H)
  (hF : H.F ≤ 208)
include F hH hF

theorem hInit_ok {t : State} (h : Base S vf s t) :
    WP isa (hInit H) t fun t' => Base S vf s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (S s) t t' [(oSt, H.S)] ∧ hH.SH.Repr t'.mem (off (S s) oSt) [] := by
  refine WP.seq (wp_addi (imm := oSt) (h := by decide) fun t₁ o₁ e₁ => wp_nil ?_)
  refine WP.mono (init_ok F hH hF (h.only F o₁) (by rw [e₁, h.s0])) fun t' ⟨b, g, sm, r⟩ =>
    ⟨b, fun r hr => by rw [g r hr, pres_of o₁ (by decide) r hr], (Same.of_mem o₁.mem _).trans sm, r⟩

theorem hUpd_ok {t : State} (h : Base S vf s t) {m : List Byte} (hr : hH.SH.Repr t.mem (off (S s) oSt) m)
    (h1 : t.gpr .a1 = BitVec.ofNat 64 m.length) {d len : Nat} (h2 : t.gpr .a2 = off (S s) d)
    (h3 : t.gpr .a3 = BitVec.ofNat 64 len) (hd : oY ≤ d) (hl : d + len ≤ oRsa) :
    WP isa (hUpd H) t fun t' => Base S vf s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (S s) t t' [(oSt, H.S)] ∧
      hH.SH.Repr t'.mem (off (S s) oSt) (m ++ Spec.Sha256.bytesAt t.mem (off (S s) d) len) := by
  have Fh := hfits hH
  obtain ⟨_, _, _, _, _⟩ := offs
  have hY : oY = 2048 := rfl
  refine WP.seq (wp_addi (imm := oSt) (h := by decide) fun t₁ o₁ e₁ => wp_nil ?_)
  have b₁ := h.only F o₁
  refine WP.mono (upd_ok F hH hF b₁ (dat := off (S s) d) (len := len) (by rw [e₁, h.s0])
    (by rw [o₁.get .a2, h2]) (by rw [o₁.get .a3, h3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
    (Covers.right (by rw [b₁.wr]; exact sc_cov F hl))
    (sdis (.inr (by omega)) hl (by omega)) (cR_dis F hl))
    fun t' ⟨b, g, sm, r⟩ => ⟨b, fun r hr => by rw [g r hr, pres_of o₁ (by decide) r hr],
      (Same.of_mem o₁.mem _).trans sm, ?_⟩
  have := r m (by rw [o₁.mem]; exact hr) (by rw [o₁.get .a1, h1])
  rwa [o₁.mem] at this

theorem hFin_ok {t : State} (h : Base S vf s t) {m : List Byte} (hr : hH.SH.Repr t.mem (off (S s) oSt) m)
    (h1 : t.gpr .a1 = BitVec.ofNat 64 m.length) (hm : m.length < 2 ^ 64) :
    WP isa (hFin H) t fun t' => Base S vf s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (S s) t t' [(oSt, H.S), (oDig, H.D)] ∧
      Spec.Sha256.bytesAt t'.mem (off (S s) oDig) H.D = hH.SH.H.hash m := by
  refine WP.seq (wp_addi (imm := oSt) (h := by decide) fun t₁ o₁ e₁ =>
    wp_addi (imm := oDig) (h := by decide) fun t₂ o₂ e₂ => wp_nil ?_)
  have k₂ : Only [.a0, .a2] t t₂ := (o₁.trans o₂).mono
  have b₂ := h.only F k₂
  refine WP.mono (fin_ok F hH hF b₂ (by rw [o₂.get .a0, e₁, h.s0]) (by rw [e₂, o₁.get .s0, h.s0]))
    fun t' ⟨b, g, sm, r⟩ =>
    ⟨b, fun r hr => by rw [g r hr, pres_of k₂ (by decide) r hr], (Same.of_mem k₂.mem _).trans sm,
      r m (by rw [k₂.mem]; exact hr) hm (by rw [k₂.get .a1, h1])⟩

/-- `hashFixed`, for a salt length `sl` in `s6`. -/
theorem hashFixedG_ok {D : Nat} (hD : H.D = D) {sl : Nat} {t : State} (h6 : t.gpr .s6 = BitVec.ofNat 64 sl)
    (h : Base S vf s t) (hsl : sl + 8 + D ≤ 2048) :
    WP isa (hashFixed H) t fun t' => Base S vf s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (S s) t t' [(oSt, H.S), (oDig, H.D)] ∧
      Spec.Sha256.bytesAt t'.mem (off (S s) oDig) H.D =
        hH.SH.H.hash (Spec.Sha256.bytesAt t.mem (off (S s) oY) (8 + D + sl)) := by
  have Fh := hfits hH
  have hY : oY = 2048 := rfl
  have hR : oRsa = 8192 := rfl
  have hD64 := hH.hD64
  have g6 : ∀ {u : State}, u.gpr .s6 = t.gpr .s6 → u.gpr .s6 + BitVec.ofNat 64 (8 + H.D) =
      BitVec.ofNat 64 (8 + D + sl) := fun e => by
    rw [e, h6, hD, BitVec.ofNat_add_ofNat]; congr 1; omega
  refine WP.seq (WP.mono (hInit_ok F hH hF h) fun t₁ ⟨b₁, g₁, s₁, r₁⟩ => ?_)
  refine WP.seq (wp_li (imm := 0) (by decide) fun t₂ o₂ e₂ => ?_)
  refine wp_yBase (by rw [o₂.get .s0, b₁.s0]) fun t₃ o₃ e₃ =>
    wp_addi (imm := 8 + H.D) (h := by omega) fun t₄ o₄ e₄ => wp_nil ?_
  have k₄ : Only [.a1, .a2, .a3] t₁ t₄ := (o₂.trans (o₃.trans o₄)).mono
  have b₄ := b₁.only F k₄
  have s6₁ : t₁.gpr .s6 = t.gpr .s6 := g₁ _ (by decide)
  refine WP.seq (WP.mono (hUpd_ok F hH hF b₄ (m := []) (by rw [k₄.mem]; exact r₁)
    (by rw [o₄.get .a1, o₃.get .a1, e₂]; rfl)
    (d := oY) (len := 8 + D + sl) (by rw [o₄.get .a2, e₃])
    (by rw [e₄, o₃.get .s6, o₂.get .s6, g6 s6₁]) (Nat.le_refl _) (by omega)) fun t₅ ⟨b₅, g₅, s₅, r₅⟩ => ?_)
  refine WP.seq (wp_addi (imm := 8 + H.D) (h := by omega) fun t₆ o₆ e₆ => wp_nil ?_)
  have b₆ := b₅.only F o₆
  have s6₅ : t₅.gpr .s6 = t.gpr .s6 := by
    rw [g₅ _ (by decide), k₄.get .s6, s6₁]
  refine WP.mono (hFin_ok F hH hF b₆ (m := [] ++ Spec.Sha256.bytesAt t₄.mem (off (S s) oY) (8 + D + sl))
    (by rw [o₆.mem]; exact r₅) (by rw [e₆, g6 s6₅, List.nil_append, Spec.Sha256.bytesAt]; simp)
    (by simp [Spec.Sha256.bytesAt]; omega)) fun t' ⟨b', g', s', r'⟩ => ⟨b', fun r hr => ?_, ?_, ?_⟩
  · rw [g' r hr, pres_of o₆ (by decide) r hr, g₅ r hr, pres_of k₄ (by decide) r hr, g₁ r hr]
  · exact (((s₁.mono (by simp)).trans ((Same.of_mem k₄.mem _).trans (s₅.mono (by simp)))).trans
      (Same.of_mem o₆.mem _)).trans s'
  · obtain ⟨_, hSt, _, _, _⟩ := offs
    rw [r', List.nil_append, k₄.mem, bytes_same s₁ (by omega) (by simp; omega)]

end

end VG.Proof.RsaPss.RISCV64
