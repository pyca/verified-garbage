module

-- separate module: it builds in parallel with the proofs after the call (`Mid` to `Post`), which `Correct`
-- also needs.

public import VerifiedGarbage.Proof.RsaPss.RISCV64.Pre
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.VerifyCall
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem

/-!
# RSASSA-PSS verification on RISC-V: the public-key operation

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPss/PPC64LE/Call.lean`): `pubArgs_ok`, the arguments of
`vg_rsa_public_precomputed_checked` (`AtCall`): `EM`'s place at `scratch`,
`pre`, `e`, the signature and the rest of the working space; `call_ok`, the
call writes RSAVP1 of the signature, or zeros, to `EM`'s place if `pre`
holds the modulus' values, by its contract
(`Proof/RsaPkcs1Sig/RISCV64/VerifyCall.lean`). It also writes the working
space past our part of it, so `Base` holds after it from the entry state with
the memory after the call (`reE`), which has the same registers, stack
pointer, regions, working space, fixed values and digest (`AfterCall`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64

open VG VG.RISCV64 VG.Impl.RsaPss.RISCV64
open VG.Impl.RsaOaep.RISCV64 (frameBytes saved oEm oSt oDig oCtr oRsa)
open VG.Proof.RsaOaep.RISCV64 (Base Fits SC off fx kR fb fr Saves slR slR_sub slot_sub frame_sub frame_contains in_fr
  in_fr' sc_in sc_cov bytes_entry words_entry oSv Saves.keep fb_ge)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo wp_li wp_addi wp_subi wp_add wp_mov wp_sd wp_sll wp_addSp wp_nil
  PdOk PdLay pdRd pdWr pdCall)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

theorem subK {x : BitVec 64} {a : Nat} (h : a ≤ x.toNat) : x - BitVec.ofNat 64 a = BitVec.ofNat 64 (x.toNat - a) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := a) (by omega), Nat.mod_eq_of_lt (a := x.toNat - a) (by omega)]; omega

/-- `k`. -/
abbrev kk (s : State) : Nat := (s.gpr .a1).toNat

/-- `pre` holds the values of the modulus. -/
def PreOk (s : State) : Prop :=
  Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (kk s)) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 3) (stackArg s 4).toNat)

/-- RSAVP1 of the signature, or zeros. -/
def emOf (s : State) : List Byte :=
  (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (kk s))
    (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .a5) (kk s))).getD
    (List.replicate (kk s) 0)

/-- The working space the public operation gets. -/
abbrev rsaR (s : State) : Region := ⟨off (Sp s) oRsa, ((stackArg s 2).toNat - 1024) * 8⟩

/-- The entry state, with the memory `m`. -/
def reE (s : State) (m : Mem) : State := { s with mem := m }

/-- Before the call: `Base`, `Xs`, and `e`, `e_len` and the signature in
`s8`–`s10`. -/
structure Before (D : Nat) (s t : State) : Prop where
  base : Base Sp (vP D) s t
  xs : Xs s t
  s8 : t.gpr .s8 = s.gpr .a2
  s9 : t.gpr .s9 = s.gpr .a3
  s10 : t.gpr .s10 = s.gpr .a5

/-- At the call of `vg_rsa_public_precomputed_checked`, from the entry state
`s`. -/
structure AtCall (D : Nat) (s t : State) : Prop where
  base : Base Sp (vP D) s t
  xs : Xs s t
  g0 : t.gpr .a0 = off (Sp s) 0
  g1 : t.gpr .a1 = s.gpr .a1
  g2 : t.gpr .a2 = stackArg s 3
  g3 : t.gpr .a3 = stackArg s 4
  g4 : t.gpr .a4 = s.gpr .a2
  g5 : t.gpr .a5 = s.gpr .a3
  g6 : t.gpr .a6 = s.gpr .a5
  g7 : t.gpr .a7 = s.gpr .a1
  a0 : stackArg t 0 = off (Sp s) oRsa
  a1 : stackArg t 1 = BitVec.ofNat 64 ((stackArg s 2).toNat - 1024)

section
variable {D : Nat} {s : State} (P : PreP D s)
include P

theorem scl : 1024 ≤ (stackArg s 2).toNat := by
  have := P.hs; unfold Spec.RsaPss.publicScratchWords at this; omega

theorem rsa_sub : Region.Sub (rsaR s) (scR s) := by
  have := scl P
  exact Offset.sub_base _ (by unfold oRsa; omega)

theorem em_sub : Region.Sub ⟨off (Sp s) 0, kk s⟩ (scR s) :=
  fun x hx => sc_sub P x (sc_in (by have := P.k2; have e : kk s = (s.gpr .a1).toNat := rfl; unfold oRsa; omega) x hx)

theorem pubArgs_ok {t : State} (h : Before D s t) : WP isa (.block pubArgs) t (AtCall D s) := by
  have hsc := scl P
  have b := h.base
  have hal := fb_al8 P
  simp only [pubArgs, Impl.RsaOaep.RISCV64.argBase]
  refine wp_addSp fun t₁ o₁ e₁ => wp_addSp fun t₂ o₂ e₂ => wp_li (imm := 1024) (by decide) fun t₃ o₃ e₃ =>
    wp_sll fun t₄ o₄ e₄ => wp_add fun t₅ o₅ e₅ => ?_
  rw [b.sp, BitVec.add_zero] at e₁
  have k₅ : Only [.t0, .t6, .t1] t t₅ := (o₁.trans (o₂.trans (o₃.trans (o₄.trans o₅)))).mono
  have g0₅ : t₅.gpr .t0 = fb s := by rw [o₅.get .t0, o₄.get .t0, o₃.get .t0, o₂.get .t0, e₁]
  have g6₅ : t₅.gpr .t6 = s.sp := by
    rw [o₅.get .t6, o₄.get .t6, o₃.get .t6, e₂, o₁.sp, b.sp, BitVec.sub_add_cancel]
  refine wp_sd (a := fb s) (by rw [g0₅, BitVec.add_zero]) hal
    (by rw [k₅.wr, b.wr]; have := in_fr s s.wr (d := 0) (n := 8) (by decide); rwa [BitVec.add_zero] at this)
    fun t₆ m₆ => ?_
  have hm₆ : Frame [kR s, SC Sp s] s.mem t₆.mem := by
    rw [m₆.mem, k₅.mem]
    exact b.mem.writeW (List.mem_cons_self ..) _ (by
      have := frame_contains s (d := 0) (n := 8) (by decide); rwa [BitVec.add_zero] at this)
  refine wp_arg P (j := 2) (by decide) (by rw [m₆.gpr, g6₅]) (by rw [m₆.rd, k₅.rd, b.rd]) hm₆
    fun t₇ o₇ e₇ => wp_subi (imm := 1024) fun t₈ o₈ e₈ => ?_
  refine wp_sd (a := fb s + BitVec.ofNat 64 8) (by rw [o₈.get .t0, o₇.get .t0, m₆.gpr, g0₅])
    (by have := hal; simp only [fb, BitVec.toNat_add, BitVec.toNat_ofNat] at this ⊢
        have := fb_ge (PreP.fits P); simp only [fb] at this; omega)
    (by rw [o₈.wr, o₇.wr, m₆.wr, k₅.wr, b.wr]; exact in_fr s _ (by decide)) fun t₉ m₉ => ?_
  have hm₉ : Frame [kR s, SC Sp s] s.mem t₉.mem := by
    rw [m₉.mem, o₈.mem, o₇.mem]
    exact hm₆.writeW (List.mem_cons_self ..) _ (frame_contains s (by decide))
  refine wp_addi (imm := oEm) fun t₁₀ o₁₀ e₁₀ => wp_mov fun t₁₁ o₁₁ e₁₁ => ?_
  have g6₁₁ : t₁₁.gpr .t6 = s.sp := by
    rw [o₁₁.get .t6, o₁₀.get .t6, m₉.gpr, o₈.get .t6, o₇.get .t6, m₆.gpr, g6₅]
  have r₁₁ : t₁₁.rd = s.rd := by rw [o₁₁.rd, o₁₀.rd, m₉.rd, o₈.rd, o₇.rd, m₆.rd, k₅.rd, b.rd]
  have hm₁₁ : Frame [kR s, SC Sp s] s.mem t₁₁.mem := by rw [o₁₁.mem, o₁₀.mem]; exact hm₉
  refine wp_arg P (j := 3) (by decide) g6₁₁ r₁₁ hm₁₁ fun t₁₂ o₁₂ e₁₂ => ?_
  refine wp_arg P (j := 4) (by decide) (by rw [o₁₂.get .t6, g6₁₁]) (by rw [o₁₂.rd, r₁₁])
    (by rw [o₁₂.mem]; exact hm₁₁) fun t₁₃ o₁₃ e₁₃ => ?_
  refine wp_mov fun t₁₄ o₁₄ e₁₄ => wp_mov fun t₁₅ o₁₅ e₁₅ => wp_mov fun t₁₆ o₁₆ e₁₆ =>
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
  have hfk : Region.Sub ⟨fb s, 16⟩ (kR s) := by
    have := frame_sub s (d := 0) (n := 16) (by decide); rwa [BitVec.add_zero] at this
  have hmem : Frame [kR s, SC Sp s] s.mem t₁₇.mem :=
    b.mem.trans (hfr.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨kR s, List.mem_cons_self .., hfk⟩)
  have b' : Base Sp (vP D) s t₁₇ :=
    ⟨b.sv.keep hK hfr (fun r hr => by rw [List.mem_singleton.mp hr]; exact hds), hK.rd.trans b.rd,
      (hK.gpr _ (by decide)).trans b.s0, fun r hr => (hK.gpr r (by revert r; decide)).trans (b.vs r hr), hmem⟩
  have hsp : t₁₇.sp = fb s := b'.sp
  refine ⟨b', h.xs.of fun r hr => hK.gpr r (by revert r; decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [o₁₇.get .a0, o₁₆.get .a0, o₁₅.get .a0, o₁₄.get .a0, o₁₃.get .a0, o₁₂.get .a0, o₁₁.get .a0, e₁₀,
      m₉.gpr, o₈.get .s0, o₇.get .s0, m₆.gpr, k₅.get .s0, b.s0]; rfl
  · rw [o₁₇.get .a1, o₁₆.get .a1, o₁₅.get .a1, o₁₄.get .a1, o₁₃.get .a1, o₁₂.get .a1, e₁₁, o₁₀.get .s1,
      m₉.gpr, o₈.get .s1, o₇.get .s1, m₆.gpr, k₅.get .s1, b.pk]
  · rw [o₁₇.get .a2, o₁₆.get .a2, o₁₅.get .a2, o₁₄.get .a2, o₁₃.get .a2, e₁₂]
  · rw [o₁₇.get .a3, o₁₆.get .a3, o₁₅.get .a3, o₁₄.get .a3, e₁₃]
  · rw [o₁₇.get .a4, o₁₆.get .a4, o₁₅.get .a4, e₁₄, o₁₃.get .s8, o₁₂.get .s8, o₁₁.get .s8, o₁₀.get .s8,
      m₉.gpr, o₈.get .s8, o₇.get .s8, m₆.gpr, k₅.get .s8, h.s8]
  · rw [o₁₇.get .a5, o₁₆.get .a5, e₁₅, o₁₄.get .s9, o₁₃.get .s9, o₁₂.get .s9, o₁₁.get .s9, o₁₀.get .s9,
      m₉.gpr, o₈.get .s9, o₇.get .s9, m₆.gpr, k₅.get .s9, h.s9]
  · rw [o₁₇.get .a6, e₁₆, o₁₅.get .s10, o₁₄.get .s10, o₁₃.get .s10, o₁₂.get .s10, o₁₁.get .s10, o₁₀.get .s10,
      m₉.gpr, o₈.get .s10, o₇.get .s10, m₆.gpr, k₅.get .s10, h.s10]
  · rw [e₁₇, o₁₆.get .s1, o₁₅.get .s1, o₁₄.get .s1, o₁₃.get .s1, o₁₂.get .s1, o₁₁.get .s1, o₁₀.get .s1,
      m₉.gpr, o₈.get .s1, o₇.get .s1, m₆.gpr, k₅.get .s1, b.pk]
  · show t₁₇.mem.readW (stackArgAddr t₁₇ 0) 64 = _
    have ea : stackArgAddr t₁₇ 0 = fb s := by rw [stackArgAddr, hsp]; simp
    rw [ea, k₁₇.mem, m₉.mem, Mem.readW_writeW_sep (by
        have := Offset.sep (fb s) (d := 0) (n := 8) (e := 8) (k := 8) (.inl (by decide)) (by decide) (by decide)
        rwa [BitVec.add_zero] at this) (by decide), o₈.mem, o₇.mem, m₆.mem, Mem.readW_writeW_self64, e₅,
      o₄.get .s0, o₃.get .s0, o₂.get .s0, o₁.get .s0, b.s0, e₄, e₃]
    have : (BitVec.ofNat 64 1024 <<< 3 : BitVec 64) = BitVec.ofNat 64 oRsa := by decide
    rw [this]
  · show t₁₇.mem.readW (stackArgAddr t₁₇ 1) 64 = _
    have ea : stackArgAddr t₁₇ 1 = fb s + BitVec.ofNat 64 8 := by rw [stackArgAddr, hsp]
    rw [ea, k₁₇.mem, m₉.mem, Mem.readW_writeW_self64, e₈, e₇, subK (by omega)]

theorem pdOk_of {t : State} (ha : AtCall D s t) : PdOk t := by
  have hk1 := P.k1; have hk2 := P.k2
  have hsc := scl P
  have hsp : t.sp = fb s := ha.base.sp
  have hsa : stackArgAddr t 0 = fb s := by rw [stackArgAddr, hsp]; simp
  have hS := P.fits.wS
  have hwsc := P.wsc
  have eS : (Sp s).toNat = (stackArg s 1).toNat := rfl
  have hem := em_sub P
  have hfa : Region.Sub ⟨fb s, 16⟩ (kR s) := by
    have := frame_sub s (d := 0) (n := 16) (by decide); rwa [BitVec.add_zero] at this
  have h1 : (stackArg t 1).toNat = (stackArg s 2).toNat - 1024 := by
    rw [ha.a1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hgs : (⟨s.gpr .a5, (s.gpr .a1).toNat⟩ : Region).Disjoint (scR s) := by
    have := P.gs; simp only [gR, P.gk] at this; exact this
  have hgr : (⟨s.gpr .a5, (s.gpr .a1).toNat⟩ : Region) ∈ s.rd := by
    have : gR s ∈ s.rd := by rw [P.hrd]; simp
    simpa only [gR, P.gk] using this
  refine ⟨?hl, ?spal, ?sp, ?hrd, ?hwr, ?hk, ?h6, ?h10, ?he1, ?he2, ?hs, ?al2, ?al0⟩
  case hl =>
    rw [ha.g0, ha.g1, ha.g2, ha.g3, ha.g4, ha.g5, ha.g6, ha.g7, ha.a0, h1, hsa]
    exact {
      on := (P.sp.sub_left hem)
      oe := P.es.symm.sub_left hem
      oi := hgs.symm.sub_left hem
      os := Offset.disjoint _ (.inl (by unfold oRsa; omega)) (by omega) (by unfold oRsa; omega)
      oa := ((P.ksc.sub_left hfa).sub_right hem).symm
      ns := P.sp.symm.sub_right (rsa_sub P)
      es := P.es.sub_right (rsa_sub P)
      is := hgs.sub_right (rsa_sub P)
      sa := ((P.ksc.sub_left hfa).sub_right (rsa_sub P)).symm
      wo := by
        show (Sp s + BitVec.ofNat 64 0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64
        rw [BitVec.add_zero]; unfold oRsa at hS; omega
      wn := P.wp
      we := P.we
      wi := by have := P.wg; rw [P.gk] at this; exact this
      ws := by
        show (Sp s + BitVec.ofNat 64 oRsa).toNat + ((stackArg s 2).toNat - 1024) * 8 ≤ 2 ^ 64
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; unfold oRsa at *; omega }
  case spal => rw [hsp]; have := Proof.RsaOaep.RISCV64.fb_al (PreP.fits P); omega
  case sp =>
    rw [hsp]; have := P.sp1
    simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat, frameBytes, Proof.RsaOaep.RISCV64.stackBytes] at *; omega
  case hrd =>
    simp only [pdRd]
    rw [ha.g2, ha.g3, ha.g4, ha.g5, ha.g6, ha.g7, hsa, ha.base.rd, ha.base.wr]
    have hm : ∀ r ∈ s.rd, Covers [r] (s.rd ++ (fr s :: s.wr)) := fun r hr =>
      Covers.left (Covers.of_mem fun x hx => by rw [List.mem_singleton.mp hx]; exact hr)
    have hf16 : InRegions (s.rd ++ (fr s :: s.wr)) (fb s) 16 := by
      have := in_fr' s s.rd s.wr (d := 0) (n := 16) (by decide); rwa [BitVec.add_zero] at this
    refine Covers.cons (hm _ (by rw [P.hrd]; simp)) (Covers.cons (hm _ (by rw [P.hrd]; simp))
      (Covers.cons (hm _ hgr) (Covers.one hf16 |>.cons Covers.nil)))
  case hwr =>
    simp only [pdWr]
    rw [ha.g0, ha.g1, ha.a0, h1, ha.base.wr]
    refine Covers.cons (sc_cov P.fits (by unfold oRsa; omega)) (Covers.cons ?_ Covers.nil)
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
  case al2 => rw [ha.g2]; exact P.al3
  case al0 =>
    rw [ha.a0]; have := P.al1
    show (stackArg s 1 + BitVec.ofNat 64 oRsa).toNat % 8 = 0
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; unfold oRsa at *; omega

end

theorem reE_sp (s : State) (m : Mem) : (reE s m).sp = s.sp := rfl
theorem reE_gpr (s : State) (m : Mem) : (reE s m).gpr = s.gpr := rfl
theorem reE_rd (s : State) (m : Mem) : (reE s m).rd = s.rd := rfl
theorem reE_wr (s : State) (m : Mem) : (reE s m).wr = s.wr := rfl
theorem reE_mem (s : State) (m : Mem) : (reE s m).mem = m := rfl

theorem Saves.reE {s t : State} (h : Saves s t) (m : Mem) : Saves (reE s m) t := ⟨h.sp, h.wr, h.sv⟩

section
variable {D : Nat} {s : State} (P : PreP D s)
include P

/-- Memory that keeps the stack arguments and `n` keeps what `Base` fixes. -/
theorem reE_args {m : Mem} (hf : Frame [kR s, scR s] s.mem m) (j : Nat) (hj : j < 5) :
    stackArg (reE s m) j = stackArg s j := by
  show m.readW (stackArgAddr s j) 64 = s.mem.readW (stackArgAddr s j) 64
  refine hf.readW (in_aR hj) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact P.ka.symm
  · exact P.sa.symm

theorem reE_n0 {m : Mem} (hf : Frame [kR s, scR s] s.mem m) : n0 (reE s m) = n0 s := by
  have hn : (nR s).Contains (s.gpr .a0) 1 := by
    have := Offset.contains_base (s.gpr .a0) (d := 0) (n := 1) (k := (s.gpr .a1).toNat) (by have := P.k1; omega)
      (by have := P.wn; omega)
    simpa only [BitVec.add_zero] using this
  show (m (s.gpr .a0)).setWidth 64 = (s.mem (s.gpr .a0)).setWidth 64
  rw [hf _ fun r hr hc => ?_]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact P.kn _ hc hn
  · exact P.ns _ hn hc

theorem reE_Sp {m : Mem} (hf : Frame [kR s, scR s] s.mem m) : Sp (reE s m) = Sp s := reE_args P hf 1 (by decide)

theorem reE_lo {m : Mem} (hf : Frame [kR s, scR s] s.mem m) : lo (reE s m) = lo s := by
  simp only [lo, smear, reE_n0 P hf]

theorem reE_vP {m : Mem} (hf : Frame [kR s, scR s] s.mem m) : vP D (reE s m) = vP D s := by
  funext r
  cases r <;> simp only [vP, dbLen, reE_lo P hf, reE_gpr]

theorem reE_Xs {m : Mem} (hf : Frame [kR s, scR s] s.mem m) {t : State} (h : Xs s t) : Xs (reE s m) t :=
  ⟨by rw [h.s5]; simp only [cm, smear, lo, reE_n0 P hf], h.s6,
    by rw [h.s7]; simp only [anyL, reE_args P hf 0 (by decide)]⟩

theorem reE_fits {m : Mem} (hf : Frame [kR s, scR s] s.mem m) : Fits Sp (reE s m) := by
  have F := P.fits
  have hS := reE_Sp P hf
  exact ⟨F.sp1, F.sp16, by rw [hS]; exact F.sc, by rw [show SC Sp (reE s m) = SC Sp s by simp only [SC, hS]]; exact F.ksc,
    by rw [hS]; exact F.wS⟩

/-- After the call: `Base` and `Xs` from the entry state with the memory
after it, memory written only in the stack and the working space, and RSAVP1
of the signature at `EM`'s place if `pre` holds the modulus' values. -/
structure AfterCall (D : Nat) (s t : State) : Prop where
  base : Base Sp (vP D) (reE s t.mem) t
  xs : Xs (reE s t.mem) t
  mem : Frame [kR s, scR s] s.mem t.mem
  em : PreOk s → Spec.Rsa.bytesAt t.mem (off (Sp s) 0) (kk s) = emOf s

theorem call_ok {t : State} (ha : AtCall D s t) :
    WP isa Impl.RsaPkcs1Sig.RISCV64.pubCall t (AfterCall D s) := by
  have hk2 := P.k2
  have hsc := scl P
  refine pdCall (pdOk_of P ha) fun s' hrd' hwr' hsp' hf hpres hpost => ?_
  simp only [pdWr] at hf
  rw [ha.g0, ha.g1, ha.a0, ha.a1, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := (stackArg s 2).isLt; omega)] at hf
  have hW : ∀ r ∈ [(⟨off (Sp s) 0, (s.gpr .a1).toNat⟩ : Region), rsaR s], Region.Sub r (scR s) := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact em_sub P
    · exact rsa_sub P
  have hd : ∀ r ∈ [(⟨off (Sp s) 0, (s.gpr .a1).toNat⟩ : Region), rsaR s], (slR s).Disjoint r := fun r hr =>
    (P.ksc.sub_left (slR_sub s)).sub_right (hW r hr)
  have sv : Saves s s' := ⟨hsp'.trans ha.base.sp, hwr'.trans ha.base.wr,
    ha.base.sv.sv.frame hf fun _ hp' r hr => (hd r hr).sub_left (slot_sub hp' s)⟩
  have hmem : Frame [kR s, scR s] s.mem s'.mem := by
    refine (ha.base.mem.sub fun r hr => ?_).trans (hf.sub fun r hr => ⟨scR s, by simp, hW r hr⟩)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨kR s, by simp, fun _ h => h⟩
    · exact ⟨scR s, by simp, sc_sub P⟩
  refine ⟨⟨Saves.reE sv _, hrd'.trans ha.base.rd, ?_, fun r hr => ?_, Frame.refl _ _⟩,
    reE_Xs P hmem (ha.xs.of fun r hr => hpres r (by revert r; decide)), hmem, fun hc => ?_⟩
  · rw [hpres _ (by decide), ha.base.s0, reE_Sp P hmem]
  · rw [hpres r (by revert r; decide), ha.base.vs r hr, reE_vP P hmem]
  have hw : Spec.Rsa.wordsAt t.mem (t.gpr .a2) (t.gpr .a3).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 3) (stackArg s 4).toNat := by
    rw [ha.g2, ha.g3]; exact words_entry ha.base.mem P.kp ((P.sp).sub_left (sc_sub P)) P.wp
  have hgs : (⟨s.gpr .a5, (s.gpr .a1).toNat⟩ : Region).Disjoint (scR s) := by
    have := P.gs; simp only [gR, P.gk] at this; exact this
  have hkg : (kR s).Disjoint ⟨s.gpr .a5, (s.gpr .a1).toNat⟩ := by
    have := P.kg; simp only [gR, P.gk] at this; exact this
  have := hpost (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat)
    (by rw [ha.g1, bytesAt_length]) (by rw [hw]; exact hc)
  rw [ha.g0, ha.g1, ha.g4, ha.g5, ha.g6,
    bytes_entry ha.base.mem P.ke ((P.es.symm).sub_left (sc_sub P)) (by have := P.we; omega),
    bytes_entry ha.base.mem hkg (hgs.symm.sub_left (sc_sub P)) (by have := P.wg; rw [P.gk] at this; omega)] at this
  unfold emOf
  revert this
  cases Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a1).toNat) with
  | none => intro h; exact h.2
  | some y => intro h; exact h.2

end

end VG.Proof.RsaPss.RISCV64
