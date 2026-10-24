module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Spec
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Entry
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Checks

/-!
# RSASSA-PSS signing on PPC64LE: MGF1's registers and `clearTop`

Untrusted: everything here is checked by Lean. `dbArgs_ok`: MGF1's registers
for masking `DB` (`dbLen` bytes at `lo`) with `H` (at `k - hLen - 1`);
`clearTop_ok`: `DB`'s first byte ANDed with the mask `c` of the modulus'
first byte, read again.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE.Sg

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE.Sign
open VG.Impl.RsaOaep.PPC64LE (oEm oRsa)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off view view_w8 fx hiRegs kR sc_in sc_inW S_fits)
open VG.Proof.RsaPss.PPC64LE (smB loB cmB)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_addi wp_subi wp_add wp_sub wp_mov wp_lbz wp_lsr
  wp_or wp_and wp_stb wp_nil)

section
variable {D : Nat} {s : State} (P : PreS D s)
include P

omit P in
theorem lo_reg {t : State} (h : Base Ss vS s t) (h0 : s.mem (s.gpr .r5) ≠ 0) :
    t.gpr .r23 = BitVec.ofNat 64 (loN s) := by rw [Base.r23 h, lo_eq h0]

/-- MGF1's registers. -/
theorem dbArgs_ok {H : Impl.Hmac.Stream.PPC64LE.Hash} (hD : H.D = D) (hD64 : D ≤ 64) {t : State}
    (h : Base Ss vS s t) (h0 : s.mem (s.gpr .r5) ≠ 0) (hfit : D + 2 ≤ kk s - loN s) :
    WP isa (.block (dbArgs H)) t fun t' => Base Ss vS s t' ∧ t'.mem = t.mem ∧
      t'.gpr .r24 = off (Ss s) (oEm + (kk s - D - 1)) ∧ t'.gpr .r25 = BitVec.ofNat 64 D ∧
      t'.gpr .r26 = off (Ss s) (oEm + loN s) ∧ t'.gpr .r27 = BitVec.ofNat 64 (kk s - loN s - D - 1) := by
  have F := fits P
  have hk2 : kk s ≤ 1024 := P.k2
  have hl1 := loN_le s
  have hS := S_fits F
  have ek : (s.gpr .r6).toNat = kk s := rfl
  have hE : oEm = 0 := rfl
  refine wp_addi fun t₁ o₁ e₁ => wp_add fun t₂ o₂ e₂ => wp_subi (h := by omega) fun t₃ o₃ e₃ =>
    wp_li (by omega) fun t₄ o₄ e₄ => wp_addi fun t₅ o₅ e₅ => wp_add fun t₆ o₆ e₆ => wp_sub fun t₇ o₇ e₇ =>
    wp_subi (h := by omega) fun t₈ o₈ e₈ => wp_nil ?_
  have k₈ : Only [.r24, .r25, .r26, .r27] t t₈ :=
    (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans (o₇.trans o₈))))))).mono
  have r15 : ∀ u : State, Only [.r24, .r25, .r26, .r27] t u → u.gpr .r15 = s.gpr .r6 := fun u o => by
    rw [o.get .r15, Base.r15 h]
  refine ⟨h.only F k₈, k₈.mem, ?_, ?_, ?_, ?_⟩
  · rw [o₈.get .r24, o₇.get .r24, o₆.get .r24, o₅.get .r24, o₄.get .r24, e₃, e₂, e₁,
      r15 t₁ (o₁.mono), h.r14, hD]
    apply BitVec.eq_of_toNat_eq
    simp only [off, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, ek] at hS ⊢
    unfold oRsa at hS; unfold oEm; omega
  · rw [o₈.get .r25, o₇.get .r25, o₆.get .r25, o₅.get .r25, e₄, hD]
  · rw [o₈.get .r26, o₇.get .r26, e₆, e₅, o₅.get .r23, o₄.get .r23, o₃.get .r23, o₂.get .r23, o₁.get .r23,
      lo_reg h h0, o₄.get .r14, o₃.get .r14, o₂.get .r14, o₁.get .r14, h.r14]
    show _ = off (Ss s) (oEm + loN s)
    rw [← off_off]
  · rw [e₈, e₇, r15 t₆ ((o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans o₆))))).mono),
      o₆.get .r23, o₅.get .r23, o₄.get .r23, o₃.get .r23, o₂.get .r23, o₁.get .r23, lo_reg h h0, hD,
      ← ofNat_toNat (s.gpr .r6), ek, Offset.ofNat_sub_ofNat (by omega), Offset.ofNat_sub_ofNat (by omega)]
    congr 1

omit P in
/-- The mask `c` of the byte `b`, as a byte. -/
theorem and_mask (b : Byte) (x : BitVec 64) : ((b.setWidth 64 &&& x).setWidth 8 : Byte) = b &&& x.setWidth 8 := by
  rw [BitVec.setWidth_and]
  congr 1
  exact BitVec.setWidth_setWidth_of_le _ (by decide)

/-- `clearTop`: `DB`'s first byte ANDed with `c`. -/
theorem clearTop_ok {t : State} (h : Base Ss vS s t) (h0 : s.mem (s.gpr .r5) ≠ 0) :
    WP isa (.block clearTop) t fun t' => Base Ss vS s t' ∧
      t'.mem = t.mem.writeW (off (Ss s) (oEm + loN s)) (view t.mem (Ss s) (oEm + loN s) &&& cS s) := by
  have F := fits P
  have hl1 := loN_le s
  have hn := n_contains P
  have hE : oEm = 0 := rfl
  have hR : oRsa = 8192 := rfl
  simp only [clearTop, List.cons_append, List.nil_append]
  refine wp_lbz (a := s.gpr .r5) (by rw [Base.r20 h, BitVec.add_zero])
    (by rw [h.rd, P.hrd]; exact ⟨nR s, List.mem_append_left _ (by simp), hn⟩) fun t₁ o₁ e₁ => ?_
  have hb : t.mem (s.gpr .r5) = s.mem (s.gpr .r5) := h.mem _ fun r hr hc => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (P.kn.sub_left kR_sub) _ hc hn
    · exact (P.ns.sub_right (sc_sub P)).symm _ hc hn
  refine wp_lsr fun t₂ o₂ e₂ => wp_lsr fun t₃ o₃ e₃ => wp_or fun t₄ o₄ e₄ => wp_lsr fun t₅ o₅ e₅ =>
    wp_or fun t₆ o₆ e₆ => wp_lsr fun t₇ o₇ e₇ => wp_or fun t₈ o₈ e₈ => wp_subi fun t₉ o₉ e₉ =>
    wp_lsr fun t₁₀ o₁₀ e₁₀ => wp_li (by decide) fun t₁₁ o₁₁ e₁₁ => wp_sub fun t₁₂ o₁₂ e₁₂ =>
    wp_li (by decide) fun t₁₃ o₁₃ e₁₃ => wp_and fun t₁₄ o₁₄ e₁₄ => wp_or fun t₁₅ o₁₅ e₁₅ =>
    wp_addi fun t₁₆ o₁₆ e₁₆ => wp_add fun t₁₇ o₁₇ e₁₇ => ?_
  have x8 : t₈.gpr .r10 = smB (s.mem (s.gpr .r5)) := by
    rw [e₈, o₇.get .r10, e₇, e₆, o₅.get .r10, e₅, e₄, o₃.get .r10, e₃, e₂, e₁, hb]; rfl
  have x10 : t₁₀.gpr .r11 = loB (s.mem (s.gpr .r5)) := by rw [e₁₀, e₉, x8]; rfl
  have x15 : t₁₅.gpr .r10 = cmB (s.mem (s.gpr .r5)) := by
    rw [e₁₅, o₁₄.get .r10, o₁₃.get .r10, o₁₂.get .r10, o₁₁.get .r10, o₁₀.get .r10, o₉.get .r10, x8, e₁₄,
      o₁₃.get .r8, e₁₂, e₁₁, o₁₁.get .r11, x10, e₁₃]; rfl
  have K : Only [.r9, .r10, .r11, .r8, .r7] t t₁₅ :=
    (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans (o₇.trans (o₈.trans (o₉.trans (o₁₀.trans
      (o₁₁.trans (o₁₂.trans (o₁₃.trans (o₁₄.trans o₁₅)))))))))))))).mono
  have K₁₇ : Only [.r9, .r10, .r11, .r8, .r7, .r4] t t₁₇ := (K.trans (o₁₆.trans o₁₇)).mono
  have x17 : t₁₇.gpr .r4 = off (Ss s) (oEm + loN s) := by
    rw [e₁₇, e₁₆, o₁₆.get .r23, K.get .r23, K.get .r14, lo_reg h h0, h.r14, ← off_off]
  have hin : InRegions (t₁₇.rd ++ t₁₇.wr) (off (Ss s) (oEm + loN s)) 1 := by
    rw [K₁₇.wr, h.wr]
    have := VG.Proof.RsaOaep.PPC64LE.sc_inR F (o := oEm + loN s) (n := 1) (by omega) t₁₇.rd
    exact this
  refine wp_lbz (a := off (Ss s) (oEm + loN s)) (by rw [x17, BitVec.add_zero]) hin fun t₁₈ o₁₈ e₁₈ =>
    wp_and fun t₁₉ o₁₉ e₁₉ => ?_
  have K₁₉ : Only [.r9, .r10, .r11, .r8, .r7, .r4, .r5] t t₁₉ := (K₁₇.trans (o₁₈.trans o₁₉)).mono
  refine wp_stb (a := off (Ss s) (oEm + loN s)) (by rw [o₁₉.get .r4, o₁₈.get .r4, x17, BitVec.add_zero])
    (by rw [K₁₉.wr, h.wr]; exact sc_inW F (by omega)) fun t' m' => wp_nil ?_
  have hv : (t₁₉.gpr .r5).setWidth 8 = view t.mem (Ss s) (oEm + loN s) &&& cS s := by
    rw [e₁₉, e₁₈, o₁₈.get .r10, o₁₇.get .r10, o₁₆.get .r10, x15, K₁₇.mem, and_mask]; rfl
  have hm : t'.mem = t.mem.writeW (off (Ss s) (oEm + loN s)) (view t.mem (Ss s) (oEm + loN s) &&& cS s) := by
    rw [m'.mem, hv, K₁₉.mem]
  refine ⟨(h.only F K₁₉).keep F m'.keep (R := [⟨off (Ss s) (oEm + loN s), 1⟩])
    (by rw [hm, ← K₁₉.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (sc_in (by omega))), hm⟩

end

end VG.Proof.RsaPss.PPC64LE.Sg
