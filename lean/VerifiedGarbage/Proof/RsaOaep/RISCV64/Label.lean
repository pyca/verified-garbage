module

public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Em
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.MgfT
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
public import VerifiedGarbage.Proof.RsaOaep.Encode
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem

/-!
# RSAES-OAEP encryption on RISC-V: the label's hash

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Label.lean`): `hashLabelT_ok`, `hashLabelT` writes
`H` of the label (in `s6` and `s7`) to `S + oDig`, for the hash function `H`
of the table that is our stack argument `j`, each call through the table
running as `H`'s (`initT_ok`, `updT_ok`, `finT_ok`); `copyLh_ok`, `copyLh`
copies its `hLen` bytes, `lHash`, to `EM + 1 + hLen`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.RISCV64

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64 VG.WriteBytes
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo wp_li wp_addi wp_mov wp_nil copy_ok)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Impl.RsaOaep.RISCV64 (Fns hashLabelT labU labF)

/-- An `Only` step keeps the callee-saved registers it does not write. -/
theorem only_pres {rs : List Reg} {t t' : State} (o : Only rs t t') (hrs : ∀ r ∈ rs, r ∉ preserved := by decide) :
    ∀ r ∈ preserved, t'.gpr r = t.gpr r := fun r hr => o.gpr r fun h => hrs r h hr

section
variable {D : Nat} {s : State} (P : PreO D s)
include P

/-- `hashLabelT`, with the hash function `H` of the table that is our stack
argument `j`: `H` of the label, to `S + oDig`. -/
theorem hashLabelT_ok {H : Hash} (hH : HashOK H) (hF : H.F ≤ 208) {f : Fns} {j : Nat} {p : Addr}
    (T : TabS H f j S s p) {t : State} (h : Base S vO s t) (sy : t.syms = s.syms)
    (h6 : t.gpr .s6 = s.gpr .a6) (h7 : t.gpr .s7 = s.gpr .a7) :
    WP isa (hashLabelT f j labU labF) t fun t' => (Base S vO s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (S s) t t' [(oSt, H.S), (oDig, H.D)] ∧
      Spec.Rsa.bytesAt t'.mem (off (S s) oDig) H.D =
        hH.SH.H.hash (Spec.Rsa.bytesAt s.mem (s.gpr .a6) (s.gpr .a7).toNat)) ∧ t'.syms = s.syms := by
  have F := hfits hH
  obtain ⟨_, _, _, _, _⟩ := offs
  refine WP.seq (WP.of_syms (wp_addi (imm := oSt) fun t₁ o₁ e₁ => wp_nil fun y₁ => ?_))
  have b₁ := h.only P.fits o₁
  refine WP.seq (WP.mono (initT_ok P.fits T hH hF b₁ (y₁.trans sy) (by rw [e₁, h.s0]))
    fun t₂ ⟨⟨b₂, g₂, s₂, r₂⟩, y₂⟩ => ?_)
  refine WP.seq (WP.of_syms (wp_addi (imm := oSt) fun t₃ o₃ e₃ => wp_li (imm := 0) (by decide) fun t₄ o₄ e₄ =>
    wp_mov fun t₅ o₅ e₅ => wp_mov fun t₆ o₆ e₆ => wp_nil fun y₆ => ?_))
  have k₆ : Only [.a0, .a1, .a2, .a3] t₂ t₆ := (o₃.trans (o₄.trans (o₅.trans o₆))).mono
  have b₆ := b₂.only P.fits k₆
  have hl : lR s ∈ s.rd := by rw [P.hrd]; simp
  have hb : Spec.Rsa.bytesAt t₆.mem (s.gpr .a6) (s.gpr .a7).toNat =
      Spec.Rsa.bytesAt s.mem (s.gpr .a6) (s.gpr .a7).toNat :=
    bytes_entry b₆.mem P.kl ((P.ls.symm).sub_left (sc_sub P)) (by have := P.wl; omega)
  have p6 : t₂.gpr .s6 = s.gpr .a6 := by rw [g₂ .s6 (by decide), o₁.get .s6, h6]
  have p7 : t₂.gpr .s7 = s.gpr .a7 := by rw [g₂ .s7 (by decide), o₁.get .s7, h7]
  refine WP.seq (WP.mono (updT_ok P.fits T hH hF b₆ (y₆.trans y₂) (dat := s.gpr .a6) (len := (s.gpr .a7).toNat)
    (by rw [o₆.get .a0, o₅.get .a0, o₄.get .a0, e₃, b₂.s0])
    (by rw [o₆.get .a2, e₅, o₄.get .s6, o₃.get .s6, p6])
    (by rw [e₆, o₅.get .s7, o₄.get .s7, o₃.get .s7, p7])
    (Covers.left (by rw [b₆.rd]; exact Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; exact hl))
    ((P.ls.sub_right (sc_sub P)).sub_right (sc_in (by omega)))
    (P.kl.sub_left (cR_sub s))) fun t₇ ⟨⟨b₇, g₇, s₇, r₇⟩, y₇⟩ => ?_)
  refine WP.seq (WP.of_syms (wp_addi (imm := oSt) fun t₈ o₈ e₈ => wp_mov fun t₉ o₉ e₉ =>
    wp_addi (imm := oDig) fun t₁₀ o₁₀ e₁₀ => wp_nil fun y₁₀ => ?_))
  have k₁₀ : Only [.a0, .a1, .a2] t₇ t₁₀ := (o₈.trans (o₉.trans o₁₀)).mono
  have b₁₀ := b₇.only P.fits k₁₀
  have g1 : t₁₀.gpr .a1 = s.gpr .a7 := by
    rw [o₁₀.get .a1, e₉, o₈.get .s7, g₇ .s7 (by decide), k₆.get .s7, p7]
  have hr : hH.SH.Repr t₁₀.mem (off (S s) oSt) (Spec.Rsa.bytesAt s.mem (s.gpr .a6) (s.gpr .a7).toNat) := by
    rw [k₁₀.mem, ← hb]
    have := r₇ [] (by rw [k₆.mem]; exact r₂) (by rw [o₆.get .a1, o₅.get .a1, e₄]; rfl)
    simp only [List.nil_append] at this; exact this
  refine WP.mono (finT_ok P.fits T hH hF b₁₀ (y₁₀.trans y₇) (by rw [o₁₀.get .a0, o₉.get .a0, e₈, b₇.s0])
    (by rw [e₁₀, o₉.get .s0, o₈.get .s0, b₇.s0])) fun t' ⟨⟨b', g', s', r'⟩, y'⟩ => ⟨⟨b', fun r hr' => ?_, ?_, ?_⟩, y'⟩
  · rw [g' r hr', only_pres k₁₀ (by decide) r hr', g₇ r hr', only_pres k₆ (by decide) r hr', g₂ r hr',
      only_pres o₁ (by decide) r hr']
  · have e : ∀ {a b : State}, a.mem = b.mem → ∀ rgs, Same (S s) a b rgs := fun e rgs => Same.of_mem e.symm rgs
    exact ((((((e o₁.mem.symm _).trans (s₂.mono (by simp))).trans (e k₆.mem.symm _)).trans
      (s₇.mono (by simp))).trans (e k₁₀.mem.symm _)).trans s')
  · exact r' _ hr (by rw [bytesAt_length]; have := (s.gpr .a7).isLt; omega)
      (by rw [g1, bytesAt_length, BitVec.ofNat_toNat, BitVec.setWidth_eq])

/-- `copyLh`: the first `hLen` bytes at `S + oDig` to `EM + 1 + hLen`. -/
theorem copyLh_ok {H : Hash} (hH : HashOK H) (hD : H.D = D) {t : State} (h : Base S vO s t) :
    WP isa (copyLh H) t fun t' => Base S vO s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      t'.mem = writeBytes t.mem (off (S s) (1 + D)) (Spec.Rsa.bytesAt t.mem (off (S s) oDig) D) := by
  have F := hfits hH
  obtain ⟨_, _, _, _, _⟩ := offs
  have hD0 := hH.hD0
  have hD64 := hH.hD64
  subst hD
  refine WP.seq (wp_addi (imm := oDig) fun t₁ o₁ e₁ =>
    wp_addi (imm := oEm + 1 + H.D) (h := by unfold oEm; omega) fun t₂ o₂ e₂ =>
    wp_li (imm := H.D) (by omega) fun t₃ o₃ e₃ => wp_nil ?_)
  have k₃ : Only [.a4, .a1, .a5] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  refine WP.mono (copy_ok (q := off (S s) oDig) (p := off (S s) (1 + H.D)) (n := H.D) hD0 (by omega)
    (by rw [o₃.get .a1, e₂, o₁.get .s0, h.s0]; show off (S s) (oEm + 1 + H.D) = _; congr 2)
    (by rw [o₃.get .a4, o₂.get .a4, e₁, h.s0]) (by rw [e₃]) (fun j hj => by
      rw [k₃.rd, k₃.wr, h.wr]
      show InRegions _ (off (off (S s) oDig) j) 1
      rw [off_off]; exact sc_inR P.fits (by omega) _)
    (sc_w P.fits (by rw [k₃.wr, h.wr]) (d := 1 + H.D) (by omega))
    (fun j hj i hi => by
      show off (off (S s) oDig) j ≠ off (off (S s) (1 + H.D)) i
      rw [off_off, off_off]
      exact Offset.add_ofNat_ne _ (by omega) (by omega) (by omega))) fun t' ⟨hk, hm⟩ => ?_
  have hK : Kept [.t0, .a4, .a1, .a5] t t' := (k₃.keep.trans hk).mono
  have hm' : t'.mem = writeBytes t.mem (off (S s) (1 + H.D)) (Spec.Rsa.bytesAt t.mem (off (S s) oDig) H.D) := by
    rw [hm, k₃.mem]
  exact ⟨h.wb P.fits hK (by rw [bytesAt_length]; omega) hm', fun r hr => hK.gpr r (by revert r; decide), hm'⟩

end

/-- `EM` before masking, from its part before `lHash` and `lHash` written
after it. -/
theorem emAt_of {V V' : Nat → Byte} {k D mLen : Nat} {sd lh m : List Byte} (hp : EmPart V k D sd m mLen)
    (hk : 2 * D + 2 + mLen ≤ k) (hk2 : k ≤ 1024)
    (hV : ∀ o < 1024, V' o = if 1 + D ≤ o ∧ o < 1 + D + D then lh.getD (o - (1 + D)) 0 else V o) :
    RsaOaep.EmAt V' k D sd lh m mLen where
  z0 := by rw [hV 0 (by omega), ifn (by omega)]; exact hp.z0
  sd i hi := by rw [hV _ (by omega), ifn (by omega)]; exact hp.sd i hi
  lh i hi := by rw [hV _ (by omega), ifp (by omega), Nat.add_sub_cancel_left]
  ps i h₁ h₂ := by rw [hV _ (by omega), ifn (by omega)]; exact hp.ps i (by omega) h₂
  one := by rw [hV _ (by omega), ifn (by omega)]; exact hp.one
  msg i hi := by rw [hV _ (by omega), ifn (by omega)]; exact hp.msg i hi

end VG.Proof.RsaOaep.RISCV64
