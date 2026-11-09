module

public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Main
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.VerifyCall
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem

/-!
# RSAES-OAEP encryption on RISC-V: the public-key operation, and failing

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Pub.lean`): `pubArgs_ok`, the arguments of
`vg_rsa_public_precomputed_checked` (`AtCall`): `out`, `pre`, `e`, `EM` at
`S` and the rest of the working space; `call_ok`, the call writes RSAEP of
`EM` to `out` if `pre` holds the modulus' values (`AfterCall`), by its
contract (`Proof/RsaPkcs1Sig/RISCV64/VerifyCall.lean`); `fail_ok`,
`encFail` writes zeros to `out` and returns 0.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.RISCV64

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64 VG.WriteBytes
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo wp_li wp_addi wp_subi wp_add wp_mov wp_sll wp_sd wp_ld wp_addSp
  wp_nil PdOk PdLay pdRd pdWr pdCall fill_ok)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

/-- `pre` holds the values of the modulus. -/
def PreOk (s : State) : Prop :=
  Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 6) (stackArg s 7).toNat)

/-- The working space the public operation gets. -/
abbrev rsaR (s : State) : Region := ⟨off (S s) oRsa, ((stackArg s 5).toNat - 1024) * 8⟩

/-- At the call of `vg_rsa_public_precomputed_checked`, from the entry state
`s`, with `EM` the encoding at `S`. -/
structure AtCall (s : State) (EM : List Byte) (t : State) : Prop where
  sv : Saves s t
  rd : t.rd = s.rd
  mem : Frame [kR s, SC S s] s.mem t.mem
  em : Spec.Rsa.bytesAt t.mem (off (S s) 0) (kk s) = EM
  g0 : t.gpr .a0 = s.gpr .a0
  g1 : t.gpr .a1 = s.gpr .a3
  g2 : t.gpr .a2 = stackArg s 6
  g3 : t.gpr .a3 = stackArg s 7
  g4 : t.gpr .a4 = s.gpr .a4
  g5 : t.gpr .a5 = s.gpr .a5
  g6 : t.gpr .a6 = off (S s) 0
  g7 : t.gpr .a7 = s.gpr .a3
  a0 : stackArg t 0 = off (S s) oRsa
  a1 : stackArg t 1 = BitVec.ofNat 64 ((stackArg s 5).toNat - 1024)

section
variable {D : Nat} {s : State} (P : PreO D s)
include P

theorem scl : 1024 ≤ (stackArg s 5).toNat := by
  have := P.hs; unfold Spec.RsaPss.publicScratchWords at this; omega

theorem rsa_sub : Region.Sub (rsaR s) (scR s) := by
  have := scl P
  exact Offset.sub_base _ (by unfold oRsa; omega)

/-- A load of our stack argument `j` through `t6`, the entry stack pointer,
with memory changed only in the stack and our part of the working space. -/
theorem wp_arg' {t : State} {r : Reg} {j : Nat} {is : List Instr} {Q : State → Prop} (hj : j < 10)
    (h6 : t.gpr .t6 = s.sp) (hrd : t.rd = s.rd) (hm : Frame [kR s, SC S s] s.mem t.mem)
    (k : ∀ t', Only [r] t t' → t'.gpr r = stackArg s j → WP isa (.block is) t' Q)
    (ho : 8 * j < 2048 := by decide) :
    WP isa (.block (.load .d r .t6 (8 * j) :: is)) t Q := by
  refine wp_ld (a := stackArgAddr s j) (by rw [h6]; rfl) (arg_al P hj) ?_ (fun t' o e => k t' o ?_) ho
  · rw [hrd, P.hrd]; exact ⟨aR s, by simp, in_aR hj⟩
  · rw [e, stackArg, hm.readW (in_aR hj) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact P.ka.symm
      · exact (P.sa.sub_left (sc_sub P)).symm) (by decide)]

theorem pubArgs_ok {t : State} {EM : List Byte} (h : Base S vO s t)
    (he : Spec.Rsa.bytesAt t.mem (off (S s) 0) (kk s) = EM) :
    WP isa (.block pubArgs) t (AtCall s EM) := by
  obtain ⟨hE, hSt, hDg, hCt, hRs⟩ := offs
  have hsc := scl P
  have hk2 : kk s ≤ 1024 := P.k2
  have hal := fb_al8 P
  simp only [pubArgs, argBase]
  refine wp_addSp fun t₁ o₁ e₁ => wp_addSp fun t₂ o₂ e₂ => wp_li (imm := 1024) (by decide) fun t₃ o₃ e₃ =>
    wp_sll fun t₄ o₄ e₄ => wp_add fun t₅ o₅ e₅ => ?_
  rw [h.sp, BitVec.add_zero] at e₁
  have k₅ : Only [.t0, .t6, .t1] t t₅ := (o₁.trans (o₂.trans (o₃.trans (o₄.trans o₅)))).mono
  have g0₅ : t₅.gpr .t0 = fb s := by rw [o₅.get .t0, o₄.get .t0, o₃.get .t0, o₂.get .t0, e₁]
  have g6₅ : t₅.gpr .t6 = s.sp := by
    rw [o₅.get .t6, o₄.get .t6, o₃.get .t6, e₂, o₁.sp, h.sp, BitVec.sub_add_cancel]
  refine wp_sd (a := fb s) (by rw [g0₅, BitVec.add_zero]) hal
    (by rw [k₅.wr, h.wr]; have := in_fr s s.wr (d := 0) (n := 8) (by decide); rwa [BitVec.add_zero] at this)
    fun t₆ m₆ => ?_
  have hm₆ : Frame [kR s, SC S s] s.mem t₆.mem := by
    rw [m₆.mem, k₅.mem]
    exact h.mem.writeW (List.mem_cons_self ..) _ (by
      have := frame_contains s (d := 0) (n := 8) (by decide); rwa [BitVec.add_zero] at this)
  refine wp_arg' P (j := 5) (by decide) (by rw [m₆.gpr, g6₅]) (by rw [m₆.rd, k₅.rd, h.rd]) hm₆
    fun t₇ o₇ e₇ => wp_subi (imm := 1024) fun t₈ o₈ e₈ => ?_
  refine wp_sd (a := fb s + BitVec.ofNat 64 8) (by rw [o₈.get .t0, o₇.get .t0, m₆.gpr, g0₅])
    (by have := hal; simp only [fb, BitVec.toNat_add, BitVec.toNat_ofNat] at this ⊢
        have := fb_ge (PreO.fits P); simp only [fb] at this; omega)
    (by rw [o₈.wr, o₇.wr, m₆.wr, k₅.wr, h.wr]; exact in_fr s _ (by decide)) fun t₉ m₉ => ?_
  have hm₉ : Frame [kR s, SC S s] s.mem t₉.mem := by
    rw [m₉.mem, o₈.mem, o₇.mem]
    exact hm₆.writeW (List.mem_cons_self ..) _ (frame_contains s (by decide))
  refine wp_mov fun t₁₀ o₁₀ e₁₀ => wp_mov fun t₁₁ o₁₁ e₁₁ => ?_
  have g6₁₁ : t₁₁.gpr .t6 = s.sp := by
    rw [o₁₁.get .t6, o₁₀.get .t6, m₉.gpr, o₈.get .t6, o₇.get .t6, m₆.gpr, g6₅]
  have r₁₁ : t₁₁.rd = s.rd := by rw [o₁₁.rd, o₁₀.rd, m₉.rd, o₈.rd, o₇.rd, m₆.rd, k₅.rd, h.rd]
  have hm₁₁ : Frame [kR s, SC S s] s.mem t₁₁.mem := by rw [o₁₁.mem, o₁₀.mem]; exact hm₉
  refine wp_arg' P (j := 6) (by decide) g6₁₁ r₁₁ hm₁₁ fun t₁₂ o₁₂ e₁₂ => ?_
  refine wp_arg' P (j := 7) (by decide) (by rw [o₁₂.get .t6, g6₁₁]) (by rw [o₁₂.rd, r₁₁])
    (by rw [o₁₂.mem]; exact hm₁₁) fun t₁₃ o₁₃ e₁₃ => ?_
  refine wp_mov fun t₁₄ o₁₄ e₁₄ => wp_mov fun t₁₅ o₁₅ e₁₅ => wp_addi (imm := oEm) fun t₁₆ o₁₆ e₁₆ =>
    wp_mov fun t₁₇ o₁₇ e₁₇ => wp_nil ?_
  have k₁₇ : Only [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7] t₉ t₁₇ :=
    (o₁₀.trans (o₁₁.trans (o₁₂.trans (o₁₃.trans (o₁₄.trans (o₁₅.trans (o₁₆.trans o₁₇))))))).mono
  have hK : Kept [.t0, .t6, .t1, .a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7] t t₁₇ :=
    (k₅.keep.trans (m₆.keep.trans (o₇.keep.trans (o₈.keep.trans (m₉.keep.trans k₁₇.keep))))).mono
  have c0 : Region.Contains ⟨fb s, 16⟩ (fb s) (64 / 8) := by
    have := Offset.contains (fb s) (d := 0) (e := 0) (n := 8) (k := 16) (by decide) (by decide) (by decide)
    simpa only [BitVec.add_zero] using this
  have c8 : Region.Contains ⟨fb s, 16⟩ (fb s + BitVec.ofNat 64 8) (64 / 8) := by
    have := Offset.contains (fb s) (d := 8) (e := 0) (n := 8) (k := 16) (by decide) (by decide) (by decide)
    simpa only [BitVec.add_zero] using this
  have hfr : Frame [⟨fb s, 16⟩] t.mem t₁₇.mem := by
    rw [k₁₇.mem, m₉.mem, o₈.mem, o₇.mem, m₆.mem, k₅.mem]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _ c8
  have hds : (slR s).Disjoint ⟨fb s, 16⟩ := by
    have := Offset.disjoint (fb s) (d := oSv) (n := frameBytes - oSv) (e := 0) (k := 16) (.inr (by decide))
      (by decide) (by decide)
    rwa [BitVec.add_zero] at this
  have sv : Saves s t₁₇ := h.sv.keep hK hfr (fun r hr => by rw [List.mem_singleton.mp hr]; exact hds)
  have hsp : t₁₇.sp = fb s := sv.sp
  have hfk : Region.Sub ⟨fb s, 16⟩ (kR s) := by
    have := frame_sub s (d := 0) (n := 16) (by decide); rwa [BitVec.add_zero] at this
  refine ⟨sv, hK.rd.trans h.rd, h.mem.trans (hfr.sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨kR s, by simp, hfk⟩), ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [← he]
    exact bytes_entry (A := ⟨fb s, 16⟩) (B := ⟨fb s, 16⟩)
      (hfr.mono fun r hr => by simp at hr ⊢; exact hr)
      ((P.fits.ksc).sub_left hfk |>.sub_right (sc_in (by omega)))
      ((P.fits.ksc).sub_left hfk |>.sub_right (sc_in (by omega))) (by omega)
  · rw [o₁₇.get .a0, o₁₆.get .a0, o₁₅.get .a0, o₁₄.get .a0, o₁₃.get .a0, o₁₂.get .a0, o₁₁.get .a0, e₁₀,
      m₉.gpr, o₈.get .s2, o₇.get .s2, m₆.gpr, k₅.get .s2, h.s2]
  · rw [o₁₇.get .a1, o₁₆.get .a1, o₁₅.get .a1, o₁₄.get .a1, o₁₃.get .a1, o₁₂.get .a1, e₁₁, o₁₀.get .s1,
      m₉.gpr, o₈.get .s1, o₇.get .s1, m₆.gpr, k₅.get .s1, h.s1]
  · rw [o₁₇.get .a2, o₁₆.get .a2, o₁₅.get .a2, o₁₄.get .a2, o₁₃.get .a2, e₁₂]
  · rw [o₁₇.get .a3, o₁₆.get .a3, o₁₅.get .a3, o₁₄.get .a3, e₁₃]
  · rw [o₁₇.get .a4, o₁₆.get .a4, o₁₅.get .a4, e₁₄, o₁₃.get .s3, o₁₂.get .s3, o₁₁.get .s3, o₁₀.get .s3,
      m₉.gpr, o₈.get .s3, o₇.get .s3, m₆.gpr, k₅.get .s3, h.s3]
  · rw [o₁₇.get .a5, o₁₆.get .a5, e₁₅, o₁₄.get .s4, o₁₃.get .s4, o₁₂.get .s4, o₁₁.get .s4, o₁₀.get .s4,
      m₉.gpr, o₈.get .s4, o₇.get .s4, m₆.gpr, k₅.get .s4, h.s4]
  · rw [o₁₇.get .a6, e₁₆, o₁₅.get .s0, o₁₄.get .s0, o₁₃.get .s0, o₁₂.get .s0, o₁₁.get .s0, o₁₀.get .s0,
      m₉.gpr, o₈.get .s0, o₇.get .s0, m₆.gpr, k₅.get .s0, h.s0, hE]
  · rw [e₁₇, o₁₆.get .s1, o₁₅.get .s1, o₁₄.get .s1, o₁₃.get .s1, o₁₂.get .s1, o₁₁.get .s1, o₁₀.get .s1,
      m₉.gpr, o₈.get .s1, o₇.get .s1, m₆.gpr, k₅.get .s1, h.s1]
  · show t₁₇.mem.readW (stackArgAddr t₁₇ 0) 64 = _
    have ea : stackArgAddr t₁₇ 0 = fb s := by rw [stackArgAddr, hsp]; simp
    rw [ea, k₁₇.mem, m₉.mem, Mem.readW_writeW_sep (by
        have := Offset.sep (fb s) (d := 0) (n := 8) (e := 8) (k := 8) (.inl (by decide)) (by decide) (by decide)
        rwa [BitVec.add_zero] at this) (by decide), o₈.mem, o₇.mem, m₆.mem, Mem.readW_writeW_self64, e₅,
      o₄.get .s0, o₃.get .s0, o₂.get .s0, o₁.get .s0, h.s0, e₄, e₃]
    have : (BitVec.ofNat 64 1024 <<< 3 : BitVec 64) = BitVec.ofNat 64 oRsa := by decide
    rw [this]
  · show t₁₇.mem.readW (stackArgAddr t₁₇ 1) 64 = _
    have ea : stackArgAddr t₁₇ 1 = fb s + BitVec.ofNat 64 8 := by rw [stackArgAddr, hsp]
    rw [ea, k₁₇.mem, m₉.mem, Mem.readW_writeW_self64, e₈, e₇, sub_k (by omega)]


theorem oR_eq : oR s = ⟨s.gpr .a0, (s.gpr .a3).toNat⟩ := by rw [oR, P.ok]

theorem pdOk_of {t : State} {EM : List Byte} (ha : AtCall s EM t) : PdOk t := by
  obtain ⟨hE, hSt, hDg, hCt, hRs⟩ := offs
  have hk1 := P.k1; have hk2 := P.k2
  have hsc := scl P
  have hsp : t.sp = fb s := ha.sv.sp
  have hsa : stackArgAddr t 0 = fb s := by rw [stackArgAddr, hsp]; simp
  have hS := (PreO.fits P).wS
  have hwsc := P.wsc
  have eS : (S s).toNat = (stackArg s 4).toNat := rfl
  have hko : (kR s).Disjoint ⟨s.gpr .a0, (s.gpr .a3).toNat⟩ := by rw [← oR_eq P]; exact P.ko
  have hem : Region.Sub ⟨off (S s) 0, (s.gpr .a3).toNat⟩ (scR s) :=
    fun x hx => sc_sub P x (sc_in (by unfold oRsa; omega) x hx)
  have hfa : Region.Sub ⟨fb s, 16⟩ (kR s) := by
    have := frame_sub s (d := 0) (n := 16) (by decide); rwa [BitVec.add_zero] at this
  have h1 : (stackArg t 1).toNat = (stackArg s 5).toNat - 1024 := by
    rw [ha.a1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨?hl, ?spal, ?sp, ?hrd, ?hwr, ?hk, ?h6, ?h10, ?he1, ?he2, ?hs, ?al2, ?al0⟩
  case hl =>
    rw [ha.g0, ha.g1, ha.g2, ha.g3, ha.g4, ha.g5, ha.g6, ha.g7, ha.a0, h1, hsa]
    exact {
      on := by rw [← oR_eq P]; exact P.op
      oe := by rw [← oR_eq P]; exact P.oe
      oi := by rw [← oR_eq P]; exact P.osc.sub_right hem
      os := by rw [← oR_eq P]; exact P.osc.sub_right (rsa_sub P)
      oa := (hko.sub_left hfa).symm
      ns := P.sp.symm.sub_right (rsa_sub P)
      es := P.es.sub_right (rsa_sub P)
      is := Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
      sa := ((P.ksc.sub_left hfa).sub_right (rsa_sub P)).symm
      wo := by have := P.wo; rw [P.ok] at this; exact this
      wn := P.wp
      we := P.we
      wi := by
        show (S s + BitVec.ofNat 64 0).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64
        rw [BitVec.add_zero]; unfold oRsa at hS; omega
      ws := by
        show (S s + BitVec.ofNat 64 oRsa).toNat + ((stackArg s 5).toNat - 1024) * 8 ≤ 2 ^ 64
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; unfold oRsa at *; omega }
  case spal => rw [hsp]; have := fb_al (PreO.fits P); omega
  case sp =>
    rw [hsp]; have := P.sp1
    simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat, frameBytes, stackBytes] at *; omega
  case hrd =>
    simp only [pdRd]
    rw [ha.g2, ha.g3, ha.g4, ha.g5, ha.g6, ha.g7, hsa, ha.rd, ha.sv.wr]
    have hm : ∀ r ∈ s.rd, Covers [r] (s.rd ++ (fr s :: s.wr)) := fun r hr =>
      Covers.left (Covers.of_mem fun x hx => by rw [List.mem_singleton.mp hx]; exact hr)
    have hf16 : InRegions (s.rd ++ (fr s :: s.wr)) (fb s) 16 := by
      have := in_fr' s s.rd s.wr (d := 0) (n := 16) (by decide); rwa [BitVec.add_zero] at this
    refine Covers.cons (hm _ (by rw [P.hrd]; simp)) (Covers.cons (hm _ (by rw [P.hrd]; simp))
      (Covers.cons (Covers.right (sc_cov P.fits (by unfold oRsa; omega)))
        (Covers.one hf16 |>.cons Covers.nil)))
  case hwr =>
    simp only [pdWr]
    rw [ha.g0, ha.g1, ha.a0, h1, ha.sv.wr]
    refine Covers.cons (Covers.of_mem fun x hx => by
      rw [List.mem_singleton.mp hx]; exact List.mem_cons_of_mem _ (by rw [P.hwr, oR_eq P]; simp))
      (Covers.cons ?_ Covers.nil)
    exact Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨scR s, by rw [P.hwr]; simp, oRsa, rfl, by simp only; unfold oRsa; omega⟩
  case hk => rw [ha.g1]; exact ⟨hk1, hk2⟩
  case h6 => rw [ha.g3, ha.g1]; exact P.hp
  case h10 => rw [ha.g7, ha.g1]
  case he1 => rw [ha.g5]; exact P.e1
  case he2 => rw [ha.g5, ha.g1]; exact P.e2
  case hs =>
    rw [ha.g1, h1]; have := P.hs; unfold Spec.RsaPss.publicScratchWords at this; omega
  case al2 => rw [ha.g2]; exact P.al5
  case al0 =>
    rw [ha.a0]; have := P.al3
    show (stackArg s 4 + BitVec.ofNat 64 oRsa).toNat % 8 = 0
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; unfold oRsa at *; omega

/-- After the call: what the restores need, and `out` written with RSAEP of
`EM` if `pre` holds the modulus' values. -/
structure AfterCall (s : State) (EM : List Byte) (t : State) : Prop where
  sv : Saves s t
  res : PreOk s → Spec.Rsa.written t.mem (s.gpr .a0) (kk s) ((t.gpr .a0).setWidth 32)
    (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (kk s))
      (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat) EM)

theorem call_ok {t : State} {EM : List Byte} (ha : AtCall s EM t) :
    WP isa Impl.RsaPkcs1Sig.RISCV64.pubCall t (AfterCall s EM) := by
  have hk2 := P.k2
  refine pdCall (pdOk_of P ha) fun s' hrd' hwr' hsp' hf hpres hpost => ?_
  simp only [pdWr] at hf
  rw [ha.g0, ha.g1, ha.a0, ha.a1, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := (stackArg s 5).isLt; omega)] at hf
  have hko : (kR s).Disjoint ⟨s.gpr .a0, (s.gpr .a3).toNat⟩ := by rw [← oR_eq P]; exact P.ko
  have hd : ∀ r ∈ [(⟨s.gpr .a0, (s.gpr .a3).toNat⟩ : Region), rsaR s], (slR s).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hko.sub_left (slR_sub s)
    · exact (P.ksc.sub_left (slR_sub s)).sub_right (rsa_sub P)
  refine ⟨⟨hsp'.trans ha.sv.sp, hwr'.trans ha.sv.wr,
    ha.sv.sv.frame hf fun _ hp' r hr => (hd r hr).sub_left (slot_sub hp' s)⟩, fun hc => ?_⟩
  have hw : Spec.Rsa.wordsAt t.mem (t.gpr .a2) (t.gpr .a3).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 6) (stackArg s 7).toNat := by
    rw [ha.g2, ha.g3]; exact words_entry ha.mem P.kp ((P.sp).sub_left (sc_sub P)) P.wp
  have := hpost (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
    (by rw [ha.g1, bytesAt_length]) (by rw [hw]; exact hc)
  rw [ha.g0, ha.g1, ha.g4, ha.g5, ha.g6, ha.em,
    bytes_entry ha.mem P.ke ((P.es.symm).sub_left (sc_sub P)) (by have := P.we; omega)] at this
  exact this

/-- `encFail`: zeros to `out`, and 0. -/
theorem fail_ok {t : State} (h : Base S vO s t) :
    WP isa encFail t fun t' => Saves s t' ∧ t'.gpr .a0 = 0 ∧
      Spec.Rsa.bytesAt t'.mem (s.gpr .a0) (kk s) = List.replicate (kk s) 0 := by
  have hk1 := P.k1; have hk2 := P.k2
  have ek : kk s = (s.gpr .a3).toNat := rfl
  refine WP.seq (WP.seq (wp_mov fun t₁ o₁ e₁ => wp_mov fun t₂ o₂ e₂ => wp_li (imm := 0) (by decide)
    fun t₃ o₃ e₃ => wp_nil ?_))
  have k₃ : Only [.a1, .t5, .t0] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  have hout : ∀ i < kk s, InRegions t₃.wr (s.gpr .a0 + BitVec.ofNat 64 i) 1 := fun i hi => by
    rw [k₃.wr, h.wr]
    exact ⟨oR s, List.mem_cons_of_mem _ (by rw [P.hwr]; simp),
      Offset.contains_base _ (by rw [P.ok]; omega) (by have := P.wo; omega)⟩
  refine WP.mono (fill_ok (p := s.gpr .a0) (n := kk s) (b := 0) (by omega) (by omega)
    (by rw [o₃.get .a1, o₂.get .a1, e₁, h.s2]) (by rw [o₃.get .t5, e₂, o₁.get .s1, h.s1]; simp)
    (by rw [e₃]; rfl) hout) fun t₄ ⟨k₄, m₄⟩ => wp_li (imm := 0) (by decide) fun t₅ o₅ e₅ => wp_nil ?_
  have hko : (kR s).Disjoint ⟨s.gpr .a0, (s.gpr .a3).toNat⟩ := by rw [← oR_eq P]; exact P.ko
  have hf : Frame [⟨s.gpr .a0, kk s⟩] t.mem t₅.mem := by
    have := Proof.RsaPkcs1Sig.frame_writeBytes t₃.mem (s.gpr .a0) (List.replicate (kk s) (0 : Byte))
    rw [List.length_replicate] at this
    rw [o₅.mem, m₄, ← k₃.mem] at *; exact this
  refine ⟨h.sv.keep ((k₃.keep.trans (k₄.trans o₅.keep)).mono (rs' := [.a0, .a1, .t5, .t0])) hf
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hko.sub_left (slR_sub s)), by rw [e₅]; rfl, ?_⟩
  have := Proof.RsaPkcs1Sig.bytesAt_writeBytes t₃.mem (s.gpr .a0) (List.replicate (kk s) (0 : Byte))
    (by simp; omega)
  rw [List.length_replicate] at this
  rw [o₅.mem, m₄, this]

end

end VG.Proof.RsaOaep.RISCV64
