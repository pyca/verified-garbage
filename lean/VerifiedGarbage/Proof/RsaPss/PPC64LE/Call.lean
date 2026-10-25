module

import VerifiedGarbage.Proof.RsaPss.PPC64LE.Entry
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Callee
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Pre
public import VerifiedGarbage.Impl.RsaPss.PPC64LE
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Pre

/-!
# RSASSA-PSS verification on PPC64LE: the public-key operation

Untrusted: everything here is checked by Lean. `pubArgs_ok`: the arguments
of `vg_rsa_public_precomputed_checked` (`AtCall`): `EM`'s place at
`scratch`, `pre`, `e`, the signature and the rest of the working space;
`call_ok`: the call writes RSAVP1 of the signature, or zeros, to `EM`'s place
if `pre` holds the modulus' values, by its contract
(`Proof/RsaPkcs1Sig/PPC64LE/Callee.lean`). It also writes the working space
past our part of it, so `Base` holds after it from the entry state with the
memory after the call (`reE`), which has the same registers, stack pointer,
regions, working space, fixed values and digest (`AfterCall`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (frameBytes saved oLr arg oEm oSt oDig oW oRsa copyLoop zeroLoop mgfXor save restore)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off fx kR fb fr Saves slR slR_sub frame_sub in_fr in_fr' stackArgAddr_in
  saved_offs sc_in sc_cov bytes_entry words_entry hiRegs)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_addi wp_subi wp_add wp_mov wp_std wp_addSp wp_nil PdOk
  PdLay pdRd pdWr pdCall)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

theorem subK {x : BitVec 64} {a : Nat} (h : a ≤ x.toNat) : x - BitVec.ofNat 64 a = BitVec.ofNat 64 (x.toNat - a) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := a) (by omega_arith), Nat.mod_eq_of_lt (a := x.toNat - a) (by omega_arith)]; omega_arith

/-- `k`. -/
abbrev kk (s : State) : Nat := (s.gpr .r4).toNat

/-- `pre` holds the values of the modulus. -/
def PreOk (s : State) : Prop :=
  Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .r3) (kk s)) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 3) (stackArg s 4).toNat)

/-- RSAVP1 of the signature, or zeros. -/
def emOf (s : State) : List Byte :=
  (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .r3) (kk s))
    (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (kk s))).getD
    (List.replicate (kk s) 0)

/-- The working space the public operation gets. -/
abbrev rsaR (s : State) : Region := ⟨off (Sp s) oRsa, ((stackArg s 2).toNat - 1024) * 8⟩

/-- The entry state, with the memory `m`. -/
def reE (s : State) (m : Mem) : State := { s with mem := m }

/-- Before the call: `Base`, and `e`, `e_len`, the signature and
`scratch_len` in `r24`–`r27`. -/
structure Before (D : Nat) (s t : State) : Prop where
  base : Base Sp (vP D) s t
  r24 : t.gpr .r24 = s.gpr .r5
  r25 : t.gpr .r25 = s.gpr .r6
  r26 : t.gpr .r26 = s.gpr .r8
  r27 : t.gpr .r27 = stackArg s 2

/-- At the call of `vg_rsa_public_precomputed_checked`, from the entry state
`s`. -/
structure AtCall (D : Nat) (s t : State) : Prop where
  base : Base Sp (vP D) s t
  g3 : t.gpr .r3 = off (Sp s) 0
  g4 : t.gpr .r4 = s.gpr .r4
  g5 : t.gpr .r5 = stackArg s 3
  g6 : t.gpr .r6 = stackArg s 4
  g7 : t.gpr .r7 = s.gpr .r5
  g8 : t.gpr .r8 = s.gpr .r6
  g9 : t.gpr .r9 = s.gpr .r8
  g10 : t.gpr .r10 = s.gpr .r4
  a0 : stackArg t 0 = off (Sp s) oRsa
  a1 : stackArg t 1 = BitVec.ofNat 64 ((stackArg s 2).toNat - 1024)

section
variable {D : Nat} {s : State} (P : PreP D s)
include P

theorem scl : 1024 ≤ (stackArg s 2).toNat := by
  have := P.hs; unfold Spec.RsaPss.publicScratchWords at this; omega_arith

theorem rsa_sub : Region.Sub (rsaR s) (scR s) := by
  have := scl P
  exact Offset.sub_base _ (by unfold oRsa; omega_arith)

theorem em_sub : Region.Sub ⟨off (Sp s) 0, kk s⟩ (scR s) :=
  fun x hx => sc_sub P x (sc_in (by have := P.k2; have e : kk s = (s.gpr .r4).toNat := rfl; unfold oRsa; omega_arith) x hx)

theorem pubArgs_ok {t : State} (h : Before D s t) : WP isa (.block pubArgs) t (AtCall D s) := by
  have hsc := scl P
  have b := h.base
  simp only [pubArgs]
  refine wp_addSp fun t₁ o₁ e₁ => wp_li (by decide) fun t₂ o₂ e₂ => wp_add fun t₃ o₃ e₃ => ?_
  rw [b.sp, BitVec.add_zero] at e₁
  have g12₃ : t₃.gpr .r12 = fb s := by rw [o₃.get .r12, o₂.get .r12, e₁]
  refine wp_std (a := fb s + BitVec.ofNat 64 96) (by rw [g12₃])
    (by rw [o₃.wr, o₂.wr, o₁.wr, b.wr]; exact in_fr s _ (by decide) (by decide)) fun t₄ m₄ => ?_
  refine wp_subi (h := by decide) fun t₅ o₅ e₅ => ?_
  refine wp_std (a := fb s + BitVec.ofNat 64 104) (by rw [o₅.get .r12, m₄.gpr, g12₃])
    (by rw [o₅.wr, m₄.wr, o₃.wr, o₂.wr, o₁.wr, b.wr]; exact in_fr s _ (by decide) (by decide)) fun t₆ m₆ => ?_
  refine wp_addi fun t₇ o₇ e₇ => wp_mov fun t₈ o₈ e₈ => wp_mov fun t₉ o₉ e₉ => wp_mov fun t₁₀ o₁₀ e₁₀ =>
    wp_mov fun t₁₁ o₁₁ e₁₁ => wp_mov fun t₁₂ o₁₂ e₁₂ => wp_mov fun t₁₃ o₁₃ e₁₃ => wp_mov fun t₁₄ o₁₄ e₁₄ =>
    wp_nil ?_
  have k₃ : Only [.r12, .r4, .r4] t t₃ := o₁.trans (o₂.trans o₃)
  have k₁₄ : Only [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10] t₆ t₁₄ :=
    (o₇.trans (o₈.trans (o₉.trans (o₁₀.trans (o₁₁.trans (o₁₂.trans (o₁₃.trans o₁₄))))))).mono
  have fr₆ : Frame [⟨fb s + BitVec.ofNat 64 96, 16⟩] t₃.mem t₆.mem := by
    rw [m₆.mem, o₅.mem, m₄.mem]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains (fb s) (d := 96) (e := 96) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (Offset.contains (fb s) (d := 104) (e := 96) (by decide) (by decide) (by decide))
  have hK : Keep [.r12, .r4, .r5, .r3, .r6, .r7, .r8, .r9, .r10] t t₁₄ :=
    (k₃.keep.trans (m₄.keep.trans (o₅.keep.trans (m₆.keep.trans k₁₄.keep)))).mono
  have hfr : Frame [⟨fb s + BitVec.ofNat 64 96, 16⟩] t.mem t₁₄.mem := by
    rw [k₁₄.mem, ← k₃.mem] at *; exact fr₆
  have hds : (slR s).Disjoint ⟨fb s + BitVec.ofNat 64 96, 16⟩ :=
    Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
  have hsub : Region.Sub ⟨fb s + BitVec.ofNat 64 96, 16⟩ (kR s) := frame_sub s (d := 96) (n := 16) (by decide)
  have hmem : Frame [kR s, SC Sp s] s.mem t₁₄.mem := by
    refine b.mem.trans (hfr.sub fun r hr => ?_)
    rw [List.mem_singleton.mp hr]
    exact ⟨kR s, List.mem_cons_self .., hsub⟩
  have b' : Base Sp (vP D) s t₁₄ :=
    ⟨b.sv.keep hK hfr (fun r hr => by rw [List.mem_singleton.mp hr]; exact hds), hK.rd.trans b.rd,
      (hK.gpr _ (by decide)).trans b.r14, fun r hr => (hK.gpr r (by revert r; decide)).trans (b.vs r hr), hmem⟩
  · have hsp : t₁₄.sp = fb s := b'.sp
    refine ⟨b', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [o₁₄.get .r3, o₁₃.get .r3, o₁₂.get .r3, o₁₁.get .r3, o₁₀.get .r3, o₉.get .r3, o₈.get .r3, e₇, m₆.gpr,
        o₅.get .r14, m₄.gpr, k₃.get .r14, b.r14]; rfl
    · rw [o₁₄.get .r4, o₁₃.get .r4, o₁₂.get .r4, o₁₁.get .r4, o₁₀.get .r4, o₉.get .r4, e₈, o₇.get .r15, m₆.gpr,
        o₅.get .r15, m₄.gpr, k₃.get .r15, b.pk]
    · rw [o₁₄.get .r5, o₁₃.get .r5, o₁₂.get .r5, o₁₁.get .r5, o₁₀.get .r5, e₉, o₈.get .r22, o₇.get .r22, m₆.gpr,
        o₅.get .r22, m₄.gpr, k₃.get .r22, b.ppre]
    · rw [o₁₄.get .r6, o₁₃.get .r6, o₁₂.get .r6, o₁₁.get .r6, e₁₀, o₉.get .r23, o₈.get .r23, o₇.get .r23, m₆.gpr,
        o₅.get .r23, m₄.gpr, k₃.get .r23, b.pprel]
    · rw [o₁₄.get .r7, o₁₃.get .r7, o₁₂.get .r7, e₁₁, o₁₀.get .r24, o₉.get .r24, o₈.get .r24, o₇.get .r24, m₆.gpr,
        o₅.get .r24, m₄.gpr, k₃.get .r24, h.r24]
    · rw [o₁₄.get .r8, o₁₃.get .r8, e₁₂, o₁₁.get .r25, o₁₀.get .r25, o₉.get .r25, o₈.get .r25, o₇.get .r25, m₆.gpr,
        o₅.get .r25, m₄.gpr, k₃.get .r25, h.r25]
    · rw [o₁₄.get .r9, e₁₃, o₁₂.get .r26, o₁₁.get .r26, o₁₀.get .r26, o₉.get .r26, o₈.get .r26, o₇.get .r26,
        m₆.gpr, o₅.get .r26, m₄.gpr, k₃.get .r26, h.r26]
    · rw [e₁₄, o₁₃.get .r15, o₁₂.get .r15, o₁₁.get .r15, o₁₀.get .r15, o₉.get .r15, o₈.get .r15, o₇.get .r15,
        m₆.gpr, o₅.get .r15, m₄.gpr, k₃.get .r15, b.pk]
    · show t₁₄.mem.readW (stackArgAddr t₁₄ 0) 64 = _
      rw [stackArgAddr_in, hsp, k₁₄.mem, m₆.mem, Mem.readW_writeW_sep (Offset.sep _ (.inl (by decide)) (by decide)
        (by decide)) (by decide), o₅.mem, m₄.mem, Mem.readW_writeW_self64, e₃, o₂.get .r14, o₁.get .r14, b.r14, e₂]
    · show t₁₄.mem.readW (stackArgAddr t₁₄ 1) 64 = _
      rw [stackArgAddr_in, hsp, k₁₄.mem, m₆.mem, Mem.readW_writeW_self64, e₅, m₄.gpr, k₃.get .r27, h.r27,
        subK (by omega_arith)]

theorem pdOk_of {t : State} (ha : AtCall D s t) : PdOk t := by
  have hk1 := P.k1; have hk2 := P.k2
  have hsc := scl P
  have hsp : t.sp = fb s := ha.base.sp
  have hsa : stackArgAddr t 0 = fb s + BitVec.ofNat 64 96 := by rw [stackArgAddr_in, hsp]
  have hS := P.fits.wS
  have hwsc := P.wsc
  have eS : (Sp s).toNat = (stackArg s 1).toNat := rfl
  have hem := em_sub P
  have hfa : Region.Sub ⟨fb s + BitVec.ofNat 64 96, 16⟩ (kR s) := frame_sub s (d := 96) (n := 16) (by decide)
  have h1 : (stackArg t 1).toNat = (stackArg s 2).toNat - 1024 := by
    rw [ha.a1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  have hgk : (s.gpr .r9).toNat = kk s := P.gk
  have hgs : (⟨s.gpr .r8, (s.gpr .r4).toNat⟩ : Region).Disjoint (scR s) := by
    have := P.gs; simp only [gR, P.gk] at this; exact this
  have hgr : (⟨s.gpr .r8, (s.gpr .r4).toNat⟩ : Region) ∈ s.rd := by
    have : gR s ∈ s.rd := by rw [P.hrd]; simp
    simpa only [gR, P.gk] using this
  refine ⟨?hl, ?sp, ?hrd, ?hwr, ?hk, ?h6, ?h10, ?he1, ?he2, ?hs⟩
  case hl =>
    rw [ha.g3, ha.g4, ha.g5, ha.g6, ha.g7, ha.g8, ha.g9, ha.g10, ha.a0, h1, hsa]
    exact {
      on := (P.sp.sub_left hem)
      oe := P.es.symm.sub_left hem
      oi := hgs.symm.sub_left hem
      os := Offset.disjoint _ (.inl (by unfold oRsa; omega_arith)) (by omega_arith) (by unfold oRsa; omega_arith)
      oa := ((P.ksc.sub_left hfa).sub_right hem).symm
      ns := P.sp.symm.sub_right (rsa_sub P)
      es := P.es.sub_right (rsa_sub P)
      is := hgs.sub_right (rsa_sub P)
      sa := ((P.ksc.sub_left hfa).sub_right (rsa_sub P)).symm
      wo := by
        show (Sp s + BitVec.ofNat 64 0).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64
        rw [BitVec.add_zero]; unfold oRsa at hS; omega_arith
      wn := P.wp
      we := P.we
      wi := by have := P.wg; rw [P.gk] at this; exact this
      ws := by
        show (Sp s + BitVec.ofNat 64 oRsa).toNat + ((stackArg s 2).toNat - 1024) * 8 ≤ 2 ^ 64
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; unfold oRsa at *; omega_arith }
  case sp =>
    rw [hsp]; have := P.sp1
    simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat, frameBytes]; omega_arith
  case hrd =>
    simp only [pdRd]
    rw [ha.g5, ha.g6, ha.g7, ha.g8, ha.g9, ha.g10, hsa, ha.base.rd, ha.base.wr]
    have hm : ∀ r ∈ s.rd, Covers [r] (s.rd ++ (fr s :: s.wr)) := fun r hr =>
      Covers.left (Covers.of_mem fun x hx => by rw [List.mem_singleton.mp hx]; exact hr)
    refine Covers.cons (hm _ (by rw [P.hrd]; simp)) (Covers.cons (hm _ (by rw [P.hrd]; simp))
      (Covers.cons (hm _ hgr)
        (Covers.one (in_fr' s _ _ (by decide) (by decide)) |>.cons Covers.nil)))
  case hwr =>
    simp only [pdWr]
    rw [ha.g3, ha.g4, ha.a0, h1, ha.base.wr]
    refine Covers.cons (sc_cov P.fits (by unfold oRsa; omega_arith)) (Covers.cons ?_ Covers.nil)
    exact Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨scR s, by rw [P.hwr]; simp, oRsa, rfl, by simp only; unfold oRsa; omega_arith⟩
  case hk => rw [ha.g4]; exact ⟨hk1, hk2⟩
  case h6 => rw [ha.g6, ha.g4]; exact P.hp
  case h10 => rw [ha.g10, ha.g4]
  case he1 => rw [ha.g8]; exact P.e1
  case he2 => rw [ha.g8, ha.g4]; exact P.e2
  case hs =>
    rw [ha.g4, h1]; have := P.hs; unfold Spec.RsaPss.publicScratchWords at this; omega_arith

end

theorem reE_sp (s : State) (m : Mem) : (reE s m).sp = s.sp := rfl
theorem reE_gpr (s : State) (m : Mem) : (reE s m).gpr = s.gpr := rfl
theorem reE_rd (s : State) (m : Mem) : (reE s m).rd = s.rd := rfl
theorem reE_wr (s : State) (m : Mem) : (reE s m).wr = s.wr := rfl
theorem reE_mem (s : State) (m : Mem) : (reE s m).mem = m := rfl

theorem Saves.reE {s t : State} (h : Saves s t) (m : Mem) : Saves (reE s m) t :=
  ⟨h.sp, h.wr, h.hi, h.sv, h.ls⟩

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
  have hn : (nR s).Contains (s.gpr .r3) 1 := by
    have := Offset.contains_base (s.gpr .r3) (d := 0) (n := 1) (k := (s.gpr .r4).toNat) (by have := P.k1; omega_arith)
      (by decide)
    rwa [BitVec.add_zero] at this
  show (m (s.gpr .r3)).setWidth 64 = (s.mem (s.gpr .r3)).setWidth 64
  rw [hf _ fun r hr hc => ?_]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact P.kn _ hc hn
  · exact P.ns _ hn hc

theorem reE_Sp {m : Mem} (hf : Frame [kR s, scR s] s.mem m) : Sp (reE s m) = Sp s := reE_args P hf 1 (by decide)

theorem reE_vP {m : Mem} (hf : Frame [kR s, scR s] s.mem m) : vP D (reE s m) = vP D s := by
  have hn := reE_n0 P hf
  have hl : lo (reE s m) = lo s := by simp only [lo, smear, hn]
  funext r
  cases r <;> simp only [vP, cm, dbLen, anyL, hl, hn, smear, reE_gpr, reE_args P hf 0 (by decide),
    reE_args P hf 3 (by decide), reE_args P hf 4 (by decide)]

theorem reE_fits {m : Mem} (hf : Frame [kR s, scR s] s.mem m) : Fits Sp (reE s m) := by
  have F := P.fits
  have hS := reE_Sp P hf
  exact ⟨F.sp1, by rw [hS]; exact F.sc, by rw [show SC Sp (reE s m) = SC Sp s by simp only [SC, hS]]; exact F.ksc,
    by rw [hS]; exact F.wS⟩

/-- After the call: `Base` from the entry state with the memory after it,
memory written only in the stack and the working space, and RSAVP1 of the
signature at `EM`'s place if `pre` holds the modulus' values. -/
structure AfterCall (D : Nat) (s t : State) : Prop where
  base : Base Sp (vP D) (reE s t.mem) t
  mem : Frame [kR s, scR s] s.mem t.mem
  em : PreOk s → Spec.Rsa.bytesAt t.mem (off (Sp s) 0) (kk s) = emOf s

theorem call_ok {t : State} (ha : AtCall D s t) :
    WP isa Impl.RsaPkcs1Sig.PPC64LE.pubCall t (AfterCall D s) := by
  have hk2 := P.k2
  have hsc := scl P
  refine pdCall (pdOk_of P ha) fun s' hrd' hwr' hsp' hf hpres hpost => ?_
  simp only [pdWr] at hf
  rw [ha.g3, ha.g4, ha.a0, ha.a1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (stackArg s 2).isLt; omega_arith)] at hf
  have hW : ∀ r ∈ [(⟨off (Sp s) 0, (s.gpr .r4).toNat⟩ : Region), rsaR s], Region.Sub r (scR s) := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact em_sub P
    · exact rsa_sub P
  have hd : ∀ r ∈ [(⟨off (Sp s) 0, (s.gpr .r4).toNat⟩ : Region), rsaR s], (slR s).Disjoint r := fun r hr =>
    (P.ksc.sub_left (slR_sub s)).sub_right (hW r hr)
  have sv : Saves s s' := ⟨hsp'.trans ha.base.sp, hwr'.trans ha.base.wr,
    fun r hr => (hpres r (by revert r; decide)).trans (ha.base.sv.hi r hr),
    ha.base.sv.sv.frame hf fun p hp' r hr => (hd r hr).sub_left (by
      have := saved_offs p hp'
      exact Offset.sub _ (n := 8) (by omega_arith) (by unfold oLr at *; omega_arith)),
    by
      rw [hf.readW (Region.contains_self _ _) (fun r hr => (hd r hr).sub_left
        (Offset.sub _ (n := 8) (by decide) (by decide))) (by decide)]
      exact ha.base.sv.ls⟩
  have hmem : Frame [kR s, scR s] s.mem s'.mem := by
    refine (ha.base.mem.sub fun r hr => ?_).trans (hf.sub fun r hr => ⟨scR s, by simp, hW r hr⟩)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨kR s, by simp, fun _ h => h⟩
    · exact ⟨scR s, by simp, sc_sub P⟩
  refine ⟨⟨Saves.reE sv _, hrd'.trans ha.base.rd, ?_, fun r hr => ?_, Frame.refl _ _⟩, hmem, fun hc => ?_⟩
  · rw [hpres _ (by decide), ha.base.r14, reE_Sp P hmem]
  · rw [hpres r (by revert r; decide), ha.base.vs r hr, reE_vP P hmem]
  have hw : Spec.Rsa.wordsAt t.mem (t.gpr .r5) (t.gpr .r6).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 3) (stackArg s 4).toNat := by
    rw [ha.g5, ha.g6]; exact words_entry ha.base.mem P.kp ((P.sp).sub_left (sc_sub P)) P.wp
  have hgs : (⟨s.gpr .r8, (s.gpr .r4).toNat⟩ : Region).Disjoint (scR s) := by
    have := P.gs; simp only [gR, P.gk] at this; exact this
  have hkg : (kR s).Disjoint ⟨s.gpr .r8, (s.gpr .r4).toNat⟩ := by
    have := P.kg; simp only [gR, P.gk] at this; exact this
  have := hpost (Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat)
    (by rw [ha.g4, bytesAt_length]) (by rw [hw]; exact hc)
  rw [ha.g3, ha.g4, ha.g7, ha.g8, ha.g9,
    bytes_entry ha.base.mem P.ke ((P.es.symm).sub_left (sc_sub P)) (by have := P.we; omega_arith),
    bytes_entry ha.base.mem hkg (hgs.symm.sub_left (sc_sub P)) (by have := P.wg; rw [P.gk] at this; omega_arith)] at this
  unfold emOf
  revert this
  cases Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r4).toNat) with
  | none => intro h; exact h.2
  | some y => intro h; exact h.2

end

end VG.Proof.RsaPss.PPC64LE
