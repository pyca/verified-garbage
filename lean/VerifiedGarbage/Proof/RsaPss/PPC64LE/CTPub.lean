module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBase
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Pre
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Entry
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Params
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.MgfArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Entry
public import VerifiedGarbage.Impl.RsaPss.PPC64LE
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Pre
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Shift
public import VerifiedGarbage.Proof.RsaPss.VerifyCases
import VerifiedGarbage.Proof.RsaPss.EncBytes
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.MHash
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Select
import VerifiedGarbage.Proof.RsaPss.PPC64LE.ShiftV
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Mid
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.MgfT
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Hash
public import VerifiedGarbage.Proof.RsaOaep.Mask
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Base
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Callee

/-! ### `RsaPss.PPC64LE.Correct`, which this module and modules that import it used -/

section

/-! ### `RsaPss.PPC64LE.Call`, which only this module used -/

section

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
    some (Spec.Rsa.wordsAt s.mem (stackArg s 4) (stackArg s 5).toNat)

/-- RSAVP1 of the signature, or zeros. -/
def emOf (s : State) : List Byte :=
  (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .r3) (kk s))
    (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (kk s))).getD
    (List.replicate (kk s) 0)

/-- The working space the public operation gets. -/
abbrev rsaR (s : State) : Region := ⟨off (Sp s) oRsa, ((stackArg s 3).toNat - 1024) * 8⟩

/-- The entry state, with the memory `m`. -/
def reE (s : State) (m : Mem) : State := { s with mem := m }

/-- Before the call: `Base`, and `e`, `e_len`, the signature and
`scratch_len` in `r24`–`r27`. -/
structure Before (D : Nat) (s t : State) : Prop where
  base : Base Sp (vP D) s t
  r24 : t.gpr .r24 = s.gpr .r5
  r25 : t.gpr .r25 = s.gpr .r6
  r26 : t.gpr .r26 = s.gpr .r9
  r27 : t.gpr .r27 = stackArg s 3

/-- At the call of `vg_rsa_public_precomputed_checked`, from the entry state
`s`. -/
structure AtCall (D : Nat) (s t : State) : Prop where
  base : Base Sp (vP D) s t
  g3 : t.gpr .r3 = off (Sp s) 0
  g4 : t.gpr .r4 = s.gpr .r4
  g5 : t.gpr .r5 = stackArg s 4
  g6 : t.gpr .r6 = stackArg s 5
  g7 : t.gpr .r7 = s.gpr .r5
  g8 : t.gpr .r8 = s.gpr .r6
  g9 : t.gpr .r9 = s.gpr .r9
  g10 : t.gpr .r10 = s.gpr .r4
  a0 : stackArg t 0 = off (Sp s) oRsa
  a1 : stackArg t 1 = BitVec.ofNat 64 ((stackArg s 3).toNat - 1024)

section
variable {D : Nat} {s : State} (P : PreP D s)
include P

theorem scl : 1024 ≤ (stackArg s 3).toNat := by
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
  have eS : (Sp s).toNat = (stackArg s 2).toNat := rfl
  have hem := em_sub P
  have hfa : Region.Sub ⟨fb s + BitVec.ofNat 64 96, 16⟩ (kR s) := frame_sub s (d := 96) (n := 16) (by decide)
  have h1 : (stackArg t 1).toNat = (stackArg s 3).toNat - 1024 := by
    rw [ha.a1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  have hgk : (s.gpr .r10).toNat = kk s := P.gk
  have hgs : (⟨s.gpr .r9, (s.gpr .r4).toNat⟩ : Region).Disjoint (scR s) := by
    have := P.gs; simp only [gR, P.gk] at this; exact this
  have hgr : (⟨s.gpr .r9, (s.gpr .r4).toNat⟩ : Region) ∈ s.rd := by
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
        show (Sp s + BitVec.ofNat 64 oRsa).toNat + ((stackArg s 3).toNat - 1024) * 8 ≤ 2 ^ 64
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
theorem Saves.reE {s t : State} (h : Saves s t) (m : Mem) : Saves (reE s m) t :=
  ⟨h.sp, h.wr, h.hi, h.sv, h.ls⟩

section
variable {D : Nat} {s : State} (P : PreP D s)
include P

/-- Memory that keeps the stack arguments and `n` keeps what `Base` fixes. -/
theorem reE_args {m : Mem} (hf : Frame [kR s, scR s] s.mem m) (j : Nat) (hj : j < 8) :
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

theorem reE_Sp {m : Mem} (hf : Frame [kR s, scR s] s.mem m) : Sp (reE s m) = Sp s := reE_args P hf 2 (by decide)

theorem reE_vP {m : Mem} (hf : Frame [kR s, scR s] s.mem m) : vP D (reE s m) = vP D s := by
  have hn := reE_n0 P hf
  have hl : lo (reE s m) = lo s := by simp only [lo, smear, hn]
  funext r
  cases r <;> simp only [vP, cm, dbLen, anyL, hl, hn, smear, reE_gpr, reE_args P hf 0 (by decide),
    reE_args P hf 1 (by decide), reE_args P hf 4 (by decide), reE_args P hf 5 (by decide)]

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
  rw [ha.g3, ha.g4, ha.a0, ha.a1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (stackArg s 3).isLt; omega_arith)] at hf
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
      Spec.Rsa.wordsAt s.mem (stackArg s 4) (stackArg s 5).toNat := by
    rw [ha.g5, ha.g6]; exact words_entry ha.base.mem P.kp ((P.sp).sub_left (sc_sub P)) P.wp
  have hgs : (⟨s.gpr .r9, (s.gpr .r4).toNat⟩ : Region).Disjoint (scR s) := by
    have := P.gs; simp only [gR, P.gk] at this; exact this
  have hkg : (kR s).Disjoint ⟨s.gpr .r9, (s.gpr .r4).toNat⟩ := by
    have := P.kg; simp only [gR, P.gk] at this; exact this
  have := hpost (Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat)
    (by rw [ha.g4, bytesAt_length]) (by rw [hw]; exact hc)
  rw [ha.g3, ha.g4, ha.g7, ha.g8, ha.g9,
    bytes_entry ha.base.mem P.ke ((P.es.symm).sub_left (sc_sub P)) (by have := P.we; omega_arith),
    bytes_entry ha.base.mem hkg (hgs.symm.sub_left (sc_sub P)) (by have := P.wg; rw [P.gk] at this; omega_arith)] at this
  unfold emOf
  revert this
  cases Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r4).toNat) with
  | none => intro h; exact h.2
  | some y => intro h; exact h.2

end

end VG.Proof.RsaPss.PPC64LE

end

end

/-! ### `RsaPss.PPC64LE.Logic`, which this module and modules that import it used -/

section

/-! ### `RsaPss.PPC64LE.Post`, which this module and modules that import it used -/

section

/-! ### `RsaPss.PPC64LE.Finish`, which only this module used -/

section

/-!
# RSASSA-PSS verification on PPC64LE: `H'` and the result

Untrusted: everything here is checked by Lean. `fixed_ok` and `any_ok`: the
two branches of `finish`, from the state after the checks of `DB`: the
result is 1 exactly when the accumulator is zero and `H` is the hash of
`M' = 0⁸ ‖ mHash ‖ salt` (`mFix`: the last `salt_len` bytes of `DB`;
`mAny`: the `sl` bytes after `pos`), as views of `EM`'s place.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (oEm oSt oDig oW oRsa)
open VG.Impl.MdStream.PPC64LE (Params)
open VG.Proof.MdStream (Md)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off view fx hiRegs Same hfits offs)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_nil)
open VG.Proof.Mgf1 (ifp ifn)

/-- `M'` for a given salt length `sl`: the last `sl` bytes of `DB` (at `lo`,
`dbLen` bytes, in the view `V`). -/
def mFix (V : Nat → Byte) (mh : List Byte) (lN dN sl : Nat) : List Byte :=
  List.replicate 8 0 ++ mh ++ (List.range sl).map fun j => V (lN + dN - sl + j)

/-- `M'` for any salt length: the `sl` bytes of `DB` after `pos`. -/
def mAny (V : Nat → Byte) (mh : List Byte) (lN dN pos sl : Nat) : List Byte :=
  List.replicate 8 0 ++ mh ++ (List.range sl).map fun j => if j + (pos + 1) < dN then V (lN + (j + (pos + 1))) else 0

/-- The `n` bytes of `M'` at `oY`. -/
abbrev mB (m : Mem) (S : Addr) (n : Nat) : List Byte := Spec.Sha256.bytesAt m (off S oY) n

/-- The bytes of `M'` at `oY`, from their view. -/
theorem mB_eq {m : Mem} {S : Addr} {D n : Nat} {mh rest : List Byte} (hmh : mh.length = D)
    (hr : rest.length = n) (h : ∀ i < 8 + D + n, view m S (oY + i) = (List.replicate 8 0 ++ mh ++ rest).getD i 0) :
    mB m S (8 + D + n) = List.replicate 8 0 ++ mh ++ rest := by
  apply List.ext_getElem (by simp [Spec.Sha256.bytesAt, hmh, hr]; omega_arith)
  intro i h₁ h₂
  obtain hi : i < 8 + D + n := by simpa [Spec.Sha256.bytesAt] using h₁
  have := h i hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂, Option.getD_some] at this
  simp only [Spec.Sha256.bytesAt, List.getElem_map, List.getElem_range]
  rw [← this, view, ← off_off]

theorem getD_m3 {mh rest : List Byte} {D : Nat} (hmh : mh.length = D) (i : Nat) :
    (List.replicate 8 0 ++ mh ++ rest).getD i 0 =
      if i < 8 then 0 else if i < 8 + D then mh.getD (i - 8) 0 else rest.getD (i - 8 - D) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.append_assoc]
  by_cases h₁ : i < 8
  · rw [ifp h₁, List.getElem?_append_left (by simp; omega_arith), List.getElem?_replicate, ifp h₁]; rfl
  · rw [ifn h₁, List.getElem?_append_right (by simp; omega_arith), List.length_replicate]
    by_cases h₂ : i < 8 + D
    · rw [ifp h₂, List.getElem?_append_left (by omega_arith)]
    · rw [ifn h₂, List.getElem?_append_right (by omega_arith), hmh, Nat.sub_sub]

section
variable {D lN dN : Nat} {c : Byte} {s : State} (L : Lay D s lN dN c) {H : Hash} (hH : HashOK H)
  {cn dn : String} {cc dc : Prog isa} {f : MdFns} {p : Addr} (T : MdTabS H cn cc dn dc f hArg Sp s p)
include L hH T

theorem fixed_ok (hD : H.D = D) {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hH.SH.H.hash x) {t : State}
    (h : Base Sp (vP D) s t) (sy : t.syms = s.syms) (hsl : (stackArg s 0).toNat + 1 ≤ dN)
    (ha : (t.gpr .r24).toNat < 2 ^ 63) :
    WP isa (.seq (mPrefix H 8) (.seq (copySalt H) (.seq (hashFixed H f hArg) (cmpH H oDig)))) t fun t' =>
      Base Sp (vP D) s t' ∧ t'.gpr .r3 = if t.gpr .r24 = 0#64 ∧ ∀ i < D, view t.mem (Sp s) (lN + dN + i) =
        (Gs.hash (mFix (view t.mem (Sp s)) (mh D s) lN dN (stackArg s 0).toNat)).getD i 0 then 1#64 else 0#64 := by
  have F := L.F
  obtain Fh := hfits hH
  obtain ⟨hE, hSt, hDg, hCt, hW, hRs⟩ := offs
  obtain hk := L.hk; have hk2 := L.k2; have hD0 := L.D0; have hD64 := L.D64
  have hY : oY = 2560 := rfl
  generalize hS : (stackArg s 0).toNat = sl at hsl
  refine WP.seq (WP.mono_syms (prefix_ok L hD (n := 8) (Nat.le_refl _) (by decide) h) fun t₁ ⟨b₁, g₁, v₁⟩ y₁ => ?_)
  refine WP.seq (WP.mono_syms (salt_ok L hD b₁ (by rw [hS]; exact hsl)) fun t₂ ⟨b₂, g₂, v₂⟩ y₂ => ?_)
  rw [hS] at v₂
  refine WP.seq (WP.mono (hashFixed_ok F hH T hD b₂ (y₂.trans (y₁.trans sy)) (by rw [hS]; omega_arith))
    fun t₃ ⟨⟨b₃, g₃, s₃, d₃⟩, _⟩ => ?_)
  rw [hS] at d₃
  obtain g24 : t₃.gpr .r24 = t.gpr .r24 := by
    rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide)]
  refine WP.mono (cmpH_ok L hD (o := oDig) (by omega_arith) b₃ (by rw [g24]; exact ha)) fun t' ⟨b', _, r'⟩ => ⟨b', ?_⟩
  rw [r', g24]
  obtain vH : ∀ i < D, view t₃.mem (Sp s) (lN + dN + i) = view t.mem (Sp s) (lN + dN + i) := fun i hi => by
    rw [s₃ _ (by omega_arith) (fun p hp => by simp at hp; rcases hp with rfl | rfl | rfl <;> simp only <;> omega_arith),
      v₂ _ (by omega_arith), ifn (by omega_arith), v₁ _ (by omega_arith), ifn (by omega_arith), ifn (by omega_arith)]
  obtain hM : mB t₂.mem (Sp s) (8 + D + sl) = mFix (view t.mem (Sp s)) (mh D s) lN dN sl := by
    refine mB_eq (by simp [Spec.Rsa.bytesAt]) (by simp) fun i hi => ?_
    rw [getD_m3 (D := D) (by simp [Spec.Rsa.bytesAt]), v₂ _ (by omega_arith)]
    by_cases h₁ : i < 8
    · rw [ifn (show ¬(oY + 8 + D ≤ oY + i ∧ oY + i < oY + 8 + D + sl) by omega_arith), v₁ _ (by omega_arith),
        ifn (show ¬(oY + 8 ≤ oY + i ∧ oY + i < oY + 8 + D) by omega_arith),
        ifp (show oY ≤ oY + i ∧ oY + i < oY + 8 by omega_arith), ifp h₁]
    · by_cases h₂ : i < 8 + D
      · rw [ifn (show ¬(oY + 8 + D ≤ oY + i ∧ oY + i < oY + 8 + D + sl) by omega_arith), v₁ _ (by omega_arith),
          ifp (show oY + 8 ≤ oY + i ∧ oY + i < oY + 8 + D by omega_arith), ifn h₁, ifp h₂,
          show oY + i - (oY + 8) = i - 8 by omega_arith]
      · rw [ifp (show oY + 8 + D ≤ oY + i ∧ oY + i < oY + 8 + D + sl by omega_arith), v₁ _ (by omega_arith),
          ifn (show ¬(oY + 8 ≤ lN + dN - sl + (oY + i - (oY + 8 + D)) ∧
            lN + dN - sl + (oY + i - (oY + 8 + D)) < oY + 8 + D) by omega_arith),
          ifn (show ¬(oY ≤ lN + dN - sl + (oY + i - (oY + 8 + D)) ∧
            lN + dN - sl + (oY + i - (oY + 8 + D)) < oY + 8) by omega_arith), ifn h₁, ifn h₂]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (show i - 8 - D < sl by omega_arith),
          Option.map_some, Option.getD_some]
        congr 2; omega_arith
  obtain vD : ∀ i < D, view t₃.mem (Sp s) (oDig + i) =
      (Gs.hash (mFix (view t.mem (Sp s)) (mh D s) lN dN sl)).getD i 0 := fun i hi => by
    have d₃' := d₃
    rw [show Spec.Sha256.bytesAt t₂.mem (off (Sp s) oY) (8 + D + sl) = _ from hM] at d₃'
    have := congrArg (·.getD i 0) d₃'
    simp only [Spec.Sha256.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (show i < H.FD by have := hH.hDF; omega_arith), Option.map_some, Option.getD_some] at this
    rw [view, ← off_off, this, hGh, hH.hashTake, List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt (by omega_arith), ← List.getD_eq_getElem?_getD]
  by_cases e : t.gpr .r24 = 0#64 ∧ ∀ i < D, view t.mem (Sp s) (lN + dN + i) =
      (Gs.hash (mFix (view t.mem (Sp s)) (mh D s) lN dN sl)).getD i 0
  · rw [ifp e, ifp ⟨e.1, fun i hi => by rw [vH i hi, vD i hi]; exact e.2 i hi⟩]
  · rw [ifn e, ifn fun h' => e ⟨h'.1, fun i hi => by rw [← vH i hi, ← vD i hi]; exact h'.2 i hi⟩]

theorem any_ok (hD : H.D = D) {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hH.SH.H.hash x)
    {P : Params} {md : Md P.B P.N P.L} (ok : CtOK P md cc dc) {iv : md.HV} (hl : md.Link hH.SH iv D)
    (hN : H.N = P.N) (hB : H.B = P.B) {t : State}
    (h : Base Sp (vP D) s t) (sy : t.syms = s.syms) {pos sl : Nat} (h8 : t.gpr .r8 = BitVec.ofNat 64 pos)
    (hp : pos < dN) (h25 : t.gpr .r25 = BitVec.ofNat 64 sl) (hsl : sl + pos + 1 = dN)
    (ha : (t.gpr .r24).toNat < 2 ^ 63) :
    WP isa (.seq (mPrefix H 2048) (.seq (copyDb H) (.seq (shift H) (.seq (ctHash H P f hArg) (cmpH H oDig))))) t
      fun t' => Base Sp (vP D) s t' ∧ t'.gpr .r3 = if t.gpr .r24 = 0#64 ∧ ∀ i < D, view t.mem (Sp s) (lN + dN + i) =
        (Gs.hash (mAny (view t.mem (Sp s)) (mh D s) lN dN pos sl)).getD i 0 then 1#64 else 0#64 := by
  have F := L.F
  obtain ⟨hE, hSt, hDg, hCt, hW, hRs⟩ := offs
  obtain hk := L.hk; have hk2 := L.k2; have hD0 := L.D0; have hD64 := L.D64
  have hY : oY = 2560 := rfl
  refine WP.seq (WP.mono_syms (prefix_ok L hD (n := 2048) (by decide) (Nat.le_refl _) h) fun t₁ ⟨b₁, g₁, v₁⟩ y₁ => ?_)
  refine WP.seq (WP.mono_syms (copyDb_ok L hD b₁) fun t₂ ⟨b₂, g₂, v₂⟩ y₂ => ?_)
  refine WP.seq (WP.mono_syms (shift_ok L hD b₂ (pos := pos) (by rw [g₂ _ (by decide), g₁ _ (by decide), h8]) hp)
    fun t₃ ⟨b₃, k₃, v₃⟩ y₃ => ?_)
  let b := oY + 8 + D
  let msg := mAny (view t.mem (Sp s)) (mh D s) lN dN pos sl
  obtain hml : msg.length = 8 + D + sl := by simp [msg, mAny, Spec.Rsa.bytesAt]; omega_arith
  obtain w₂ : ∀ o < oRsa, ¬(b ≤ o ∧ o < b + dN) → ¬(oY ≤ o ∧ o < oY + 2048) → view t₂.mem (Sp s) o = view t.mem (Sp s) o :=
    fun o ho h₁ h₂ => by rw [v₂ o ho, ifn h₁, v₁ o ho, ifn (by omega_arith), ifn h₂]
  obtain hz : ∀ x, dN ≤ x → x < dN + 2 ^ 9 → view t₂.mem (Sp s) (b + x) = 0 := fun x h₁ h₂ => by
    have : (2 : Nat) ^ 9 = 512 := rfl
    rw [v₂ _ (by omega_arith), ifn (by omega_arith), v₁ _ (by omega_arith), ifn (by omega_arith), ifp (by omega_arith)]
  obtain hMl : (mh D s).length = D := by simp [Spec.Rsa.bytesAt]
  obtain hYv : ∀ i < 2048, view t₃.mem (Sp s) (oY + i) = msg.getD i 0 := by
    intro i hi
    show _ = (mAny (view t.mem (Sp s)) (mh D s) lN dN pos sl).getD i 0
    unfold mAny
    rw [v₃ _ (by omega_arith)]
    by_cases h₁ : i < 8
    · rw [shV_out _ _ _ _ _ _ (by omega_arith), v₂ _ (by omega_arith), ifn (by omega_arith), v₁ _ (by omega_arith),
        ifn (show ¬(oY + 8 ≤ oY + i ∧ oY + i < oY + 8 + D) by omega_arith),
        ifp (show oY ≤ oY + i ∧ oY + i < oY + 2048 by omega_arith), getD_m3 hMl, ifp h₁]
    · by_cases h₂ : i < 8 + D
      · rw [shV_out _ _ _ _ _ _ (by omega_arith), v₂ _ (by omega_arith), ifn (by omega_arith), v₁ _ (by omega_arith),
          ifp (show oY + 8 ≤ oY + i ∧ oY + i < oY + 8 + D by omega_arith), getD_m3 hMl, ifn h₁, ifp h₂,
          show oY + i - (oY + 8) = i - 8 by omega_arith]
      · rw [getD_m3 hMl, ifn h₁, ifn h₂]
        by_cases h₃ : i < 8 + D + dN
        · rw [show oY + i = b + (i - 8 - D) by omega_arith, shV_eq _ (by omega_arith) hz (by omega_arith)]
          by_cases h₄ : i - 8 - D < sl
          · simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h₄, Option.map_some,
              Option.getD_some]
            by_cases e : i - 8 - D + (pos + 1) < dN
            · rw [ifp e, ifp e, v₂ _ (by omega_arith), ifp (by omega_arith), v₁ _ (by omega_arith), ifn (by omega_arith),
                ifn (by omega_arith)]
              congr 1; omega_arith
            · rw [ifn e, ifn e]
          · rw [ifn (by omega_arith), List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega_arith)]; rfl
        · rw [shV_out _ _ _ _ _ _ (by omega_arith), v₂ _ (by omega_arith), ifn (by omega_arith), v₁ _ (by omega_arith),
            ifn (by omega_arith), ifp (by omega_arith), List.getD_eq_getElem?_getD,
            List.getElem?_eq_none (by simp; omega_arith)]; rfl
  refine WP.seq (WP.mono (ctHash_ok L hH T ok hl hD hN hB b₃ (y₃.trans (y₂.trans (y₁.trans sy))) (sl := sl)
    (by rw [k₃.get .r25, g₂ _ (by decide), g₁ _ (by decide), h25]) (by omega_arith) hml hYv)
    fun t₄ ⟨⟨b₄, g24₄, mem₄, d₄⟩, _⟩ => ?_)
  obtain g24 : t₄.gpr .r24 = t.gpr .r24 := by rw [g24₄, k₃.get .r24, g₂ _ (by decide), g₁ _ (by decide)]
  refine WP.mono (cmpH_ok L hD (o := oDig) (by omega_arith) b₄ (by rw [g24]; exact ha)) fun t' ⟨b', _, r'⟩ => ⟨b', ?_⟩
  rw [r', g24]
  obtain vH : ∀ i < D, view t₄.mem (Sp s) (lN + dN + i) = view t.mem (Sp s) (lN + dN + i) := fun i hi => by
    rw [mem₄ _ (by omega_arith), v₃ _ (by omega_arith), shV_out _ _ _ _ _ _ (by omega_arith),
      w₂ _ (by omega_arith) (by omega_arith) (by omega_arith)]
  obtain vD : ∀ i < D, view t₄.mem (Sp s) (oDig + i) = (Gs.hash msg).getD i 0 := fun i hi => by rw [d₄ i hi, hGh]
  by_cases e : t.gpr .r24 = 0#64 ∧ ∀ i < D, view t.mem (Sp s) (lN + dN + i) = (Gs.hash msg).getD i 0
  · rw [ifp e, ifp ⟨e.1, fun i hi => by rw [vH i hi, vD i hi]; exact e.2 i hi⟩]
  · rw [ifn e, ifn fun h' => e ⟨h'.1, fun i hi => by rw [← vH i hi, ← vD i hi]; exact h'.2 i hi⟩]

end

end VG.Proof.RsaPss.PPC64LE

end

end

/-! ### `RsaPss.PPC64LE.Unmask`, which only this module used -/

section

/-!
# RSASSA-PSS verification on PPC64LE: `DB`

Untrusted: everything here is checked by Lean. `unmask_ok`: `dbArgs` (`dbArgs_ok`), MGF1
through its table (`mgfXorT_ok`, shared with RSAES-OAEP encryption) and `clearTop` (`clearTop_ok`) leave `DB` in
`EM`'s place: `maskedDB` XORed with MGF1 of `H`, its first byte ANDed with
`c` (`dbV`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (oEm oSt oDig oW oRsa Fns mgfXorT)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off view view_w8 sc_in sc_inR sc_inW fx hiRegs MFit TabS mgfXorT_ok)
open VG.Proof.RsaOaep (mixV srcB)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_addi wp_add wp_mov wp_and wp_lbz wp_stb wp_nil)
open VG.Proof.Mgf1 (ifp ifn)

/-- `DB` in `EM`'s place, from its view `V` before unmasking. -/
def dbV (Gs : Spec.Mgf1.Hash) (V : Nat → Byte) (lN dN D : Nat) (c : Byte) (o : Nat) : Byte :=
  let W := mixV V (Spec.Mgf1.mgf1 Gs (srcB V (lN + dN) D) dN) lN dN
  if o = lN then W o &&& c else W o

section
variable {D lN dN : Nat} {c : Byte} {s : State} (L : Lay D s lN dN c)
include L

/-- MGF1's arguments for unmasking `DB`: `H` after it as the seed. -/
theorem dbArgs_ok {H : Hash} (hD : H.D = D) {t : State} (h : Base Sp (vP D) s t) :
    WP isa (.block (dbArgs H)) t fun t' => Base Sp (vP D) s t' ∧ Only [.r26, .r27, .r24, .r25] t t' ∧
      t'.gpr .r24 = off (Sp s) (lN + dN) ∧ t'.gpr .r25 = BitVec.ofNat 64 D ∧ t'.gpr .r26 = off (Sp s) lN ∧
      t'.gpr .r27 = BitVec.ofNat 64 dN := by
  have F := L.F
  have hD64 := L.D64
  subst hD
  refine wp_add fun t₁ o₁ e₁ => wp_mov fun t₂ o₂ e₂ => wp_add fun t₃ o₃ e₃ =>
    wp_li (by omega_arith) fun t₄ o₄ e₄ => wp_nil ?_
  obtain k₄ : Only [.r26, .r27, .r24, .r25] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  obtain a26 : t₁.gpr .r26 = off (Sp s) lN := by rw [e₁, h.r14, h.plo, L.hlo]
  exact ⟨h.only F k₄, k₄,
    by rw [o₄.get .r24, e₃, o₂.get .r26, a26, o₂.get .r21, o₁.get .r21, h.pdb, L.hdb]; exact off_off _ _ _,
    by rw [e₄], by rw [o₄.get .r26, o₃.get .r26, o₂.get .r26, a26],
    by rw [o₄.get .r27, o₃.get .r27, e₂, o₁.get .r21, h.pdb, L.hdb]⟩

/-- `clearTop`: `DB`'s first byte ANDed with `c`. -/
theorem clearTop_ok {t : State} (h : Base Sp (vP D) s t) :
    WP isa (.block clearTop) t fun w => Base Sp (vP D) s w ∧ Keep [.r4, .r5] t w ∧
      ∀ o < oSt, view w.mem (Sp s) o = if o = lN then view t.mem (Sp s) lN &&& c else view t.mem (Sp s) o := by
  have F := L.F
  obtain hk := L.hk; have hk2 := L.k2; have hl := L.l1
  obtain a6 : ∀ {u : State}, Only [.r4] t u → u.gpr .r4 = t.gpr .r14 + t.gpr .r17 → u.gpr .r4 = off (Sp s) lN :=
    fun o e => by rw [e, h.r14, h.plo, L.hlo]
  refine wp_add fun t₆ o₆ e₆ => ?_
  refine wp_lbz (a := off (Sp s) lN) (by rw [a6 o₆ e₆, BitVec.add_zero])
    (by rw [o₆.rd, o₆.wr, h.wr]; exact sc_inR F (by unfold oRsa; omega_arith) _) fun t₇ o₇ e₇ => ?_
  refine wp_and fun t₈ o₈ e₈ => wp_stb (a := off (Sp s) lN) (by rw [o₈.get .r4, o₇.get .r4, a6 o₆ e₆,
    BitVec.add_zero]) (by rw [o₈.wr, o₇.wr, o₆.wr, h.wr]; exact sc_inW F (by unfold oRsa; omega_arith)) fun w mw => ?_
  obtain k₈ : Only [.r4, .r5] t t₈ := (o₆.trans (o₇.trans o₈)).mono
  obtain hK : Keep [.r4, .r5] t w := (k₈.keep.trans mw.keep).mono
  obtain hb : (t₈.gpr .r5).setWidth 8 = view t.mem (Sp s) lN &&& c := by
    rw [e₈, e₇, o₇.get .r18, o₆.get .r18, h.pc, L.hc, o₆.mem]
    simp only [BitVec.setWidth_and, BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide), BitVec.setWidth_eq]
    rfl
  obtain hm : w.mem = t.mem.writeW (off (Sp s) lN) (view t.mem (Sp s) lN &&& c) := by
    rw [mw.mem, hb, k₈.mem]
  refine wp_nil ⟨h.keep F hK (R := [⟨off (Sp s) lN, 1⟩]) (by
      rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (sc_in (by unfold oRsa; omega_arith))), hK, fun o ho => ?_⟩
  rw [hm, view_w8 _ _ (by unfold oRsa; omega_arith) (by unfold oSt oRsa at *; omega_arith)]

theorem unmask_ok {H : Hash} (hD : H.D = D) {G : Hash} (hG : HashOK G) {g : Fns} {pg : Addr}
    (Tg : TabS G g gArg Sp s pg) {Gm : Spec.Mgf1.Hash}
    (hGh : ∀ x, Gm.hash x = hG.SH.H.hash x) (hGl : Gm.len = G.D) (hGv : Proof.Mgf1.Valid Gm) {t : State}
    (h : Base Sp (vP D) s t) (sy : t.syms = s.syms) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ t', Base Sp (vP D) s t' → t'.syms = s.syms →
      (∀ o < oSt, view t'.mem (Sp s) o = dbV Gm (view t.mem (Sp s)) lN dN D c o) → WP isa rest t' Q) :
    WP isa (.seq (.block (dbArgs H)) (.seq (mgfXorT g gArg) (.seq (.block clearTop) rest))) t Q := by
  have F := L.F
  obtain hk := L.hk; have hk2 := L.k2; have hd1 := L.d1; have hD64 := L.D64
  refine WP.seq (WP.mono_syms (dbArgs_ok L hD h) fun t₄ ⟨b₄, k₄, x24, x25, x26, x27⟩ y₄ => ?_)
  refine WP.seq (WP.mono (mgfXorT_ok F hG Tg hGh hGl hGv (src := lN + dN) (srcLen := D) (dst := lN) (dstLen := dN)
    ⟨by omega_arith, by omega_arith, .inr (by omega_arith), by omega_arith⟩ b₄ (y₄.trans sy) x24 x25 x26 x27)
    fun t₅ ⟨⟨b₅, v₅⟩, y₅⟩ => ?_)
  obtain V4 : view t₄.mem (Sp s) = view t.mem (Sp s) := by rw [k₄.mem]
  rw [V4] at v₅
  refine WP.seq (WP.mono_syms (clearTop_ok L b₅) fun w ⟨b, _, v⟩ yw => k w b (yw.trans y₅) fun o ho => ?_)
  rw [v o ho, dbV]
  by_cases e : o = lN
  · subst e; rw [ifp rfl, ifp rfl, v₅ _ ho]
  · rw [ifn e, ifn e, v₅ o ho]

end

end VG.Proof.RsaPss.PPC64LE

end

end

/-! ### `RsaPss.PPC64LE.Scan`, which only this module used -/

section

/-!
# RSASSA-PSS verification on PPC64LE: the first nonzero byte of `DB`

Untrusted: everything here is checked by Lean. `scan_ok`: `scan` finds, in
the `dbLen` bytes of `DB` (`w`), the number `z` of leading zero bytes
(`Proof.RsaPss.lz`) without branching on them: `pos` (`r8`) is `z` and `val`
(`r9`) the byte there if `z < dbLen`, both 0 if not. The invariant after `i`
bytes is that of their leading zeros (`lzr w i`, `lzr_succ`), with `r7` all
ones while it is `i`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (oEm oSt oDig oW oRsa)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off view sc_in sc_inR fx hiRegs)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_addi wp_subi wp_add wp_sub wp_mov wp_and wp_or wp_lsr
  wp_lbz wp_nil wp_countdown)
open VG.Proof.RsaPss (lz)
open VG.Proof.Mgf1 (ifp ifn)

/-- The leading zeros of the first `i` bytes of `w`. -/
def lzr (w : Nat → Byte) (i : Nat) : Nat := lz ((List.range i).map w)

theorem lz_append : ∀ (l : List Byte) (x : Byte),
    lz (l ++ [x]) = if lz l = l.length then (if x = 0 then l.length + 1 else l.length) else lz l
  | [], x => by simp only [List.nil_append, lz, List.length_nil]; split <;> simp
  | b :: bs, x => by
    rw [List.cons_append, lz, lz, lz_append bs x, List.length_cons]
    have := VG.Proof.RsaPss.lz_le bs
    by_cases hb : b = 0 <;> by_cases h : lz bs = bs.length <;> by_cases hx : x = 0 <;>
      simp only [hb, h, hx, ite_true, ite_false, Nat.add_right_cancel_iff] <;> (try split) <;> omega_arith

theorem lzr_succ (w : Nat → Byte) (i : Nat) :
    lzr w (i + 1) = if lzr w i = i then (if w i = 0 then i + 1 else i) else lzr w i := by
  have := lz_append ((List.range i).map w) (w i)
  rw [List.length_map, List.length_range] at this
  rw [lzr, List.range_succ, List.map_append, List.map_singleton, this, lzr]

theorem lzr_le (w : Nat → Byte) (i : Nat) : lzr w i ≤ i := by
  have := VG.Proof.RsaPss.lz_le ((List.range i).map w); simpa [lzr] using this

/-- `(b - 1) >>> 63`: 1 if `b = 0`, 0 if not. -/
theorem isz_eq (b : Byte) : (b.setWidth 64 - BitVec.ofNat 64 1) >>> 63 = if b = 0 then 1#64 else 0#64 := by
  have hb := b.isLt
  obtain e : b = BitVec.ofNat 8 b.toNat := (BitVec.ofNat_toNat _ b).trans (BitVec.setWidth_eq _) |>.symm
  generalize b.toNat = n at hb e
  subst e
  revert n; decide +kernel

/-- What the scan keeps after `i` bytes: `r7` all ones while every byte so
far is zero, `pos` and `val` once one is not. -/
structure ScanI (w : Nat → Byte) (S : Addr) (lN i : Nat) (u : State) : Prop where
  r4 : u.gpr .r4 = off S (lN + i)
  r6 : u.gpr .r6 = BitVec.ofNat 64 i
  r7 : u.gpr .r7 = if lzr w i = i then BitVec.allOnes 64 else 0#64
  r8 : u.gpr .r8 = BitVec.ofNat 64 (if lzr w i < i then lzr w i else 0)
  r9 : u.gpr .r9 = (if lzr w i < i then w (lzr w i) else 0).setWidth 64

theorem scan_step {w : Nat → Byte} {S : Addr} {lN i : Nat} {u u' : State} (I : ScanI w S lN i u)
    (hb : (u'.gpr .r10) = (w i).setWidth 64)
    (h11 : u'.gpr .r11 = (u'.gpr .r10 - BitVec.ofNat 64 1) >>> 63)
    (h12 : u'.gpr .r12 = (u'.gpr .r11 - BitVec.ofNat 64 1) &&& u.gpr .r7)
    (h8 : u'.gpr .r8 = u.gpr .r8 ||| (u.gpr .r6 &&& u'.gpr .r12))
    (h9 : u'.gpr .r9 = u.gpr .r9 ||| (u'.gpr .r10 &&& u'.gpr .r12))
    (h7 : u'.gpr .r7 = u.gpr .r7 &&& (BitVec.ofNat 64 0 - u'.gpr .r11))
    (h4 : u'.gpr .r4 = u.gpr .r4 + BitVec.ofNat 64 1) (h6 : u'.gpr .r6 = u.gpr .r6 + BitVec.ofNat 64 1) :
    ScanI w S lN (i + 1) u' := by
  obtain hz := isz_eq (w i)
  rw [← hb] at hz
  rw [hz] at h11
  obtain hl := lzr_le w i
  obtain r4' : u'.gpr .r4 = off S (lN + (i + 1)) := by rw [h4, I.r4]; exact off_off _ _ _
  obtain r6' : u'.gpr .r6 = BitVec.ofNat 64 (i + 1) := by rw [h6, I.r6, BitVec.ofNat_add]
  by_cases e : lzr w i = i
  · have I7 := I.r7; have I8 := I.r8; have I9 := I.r9
    rw [ifp e] at I7
    rw [ifn (by omega_using [e])] at I8 I9
    by_cases z : w i = 0
    · rw [ifp z] at h11
      obtain h12' : u'.gpr .r12 = 0#64 := by rw [h12, h11, I7]; rfl
      refine ⟨r4', r6', ?_, ?_, ?_⟩ <;> rw [lzr_succ, ifp e, ifp z]
      · rw [ifp rfl, h7, I7, h11]; rfl
      · rw [ifn (by omega_using []), h8, I8, h12', BitVec.and_zero, BitVec.or_zero]
      · rw [ifn (by omega_using []), h9, I9, h12', BitVec.and_zero, BitVec.or_zero]
    · rw [ifn z] at h11
      obtain h12' : u'.gpr .r12 = BitVec.allOnes 64 := by rw [h12, h11, I7]; rfl
      refine ⟨r4', r6', ?_, ?_, ?_⟩ <;> rw [lzr_succ, ifp e, ifn z]
      · rw [ifn (by omega_using []), h7, I7, h11]; rfl
      · rw [ifp (by omega_using []), h8, I8, h12', BitVec.and_allOnes, I.r6]; simp
      · rw [ifp (by omega_using []), h9, I9, h12', BitVec.and_allOnes, hb, ← e]; simp
  · have I7 := I.r7
    rw [ifn e] at I7
    obtain h12' : u'.gpr .r12 = 0#64 := by rw [h12, I7, BitVec.and_zero]
    refine ⟨r4', r6', ?_, ?_, ?_⟩ <;> rw [lzr_succ, ifn e]
    · rw [ifn (by omega_using [hl]), h7, I7, BitVec.zero_and]
    · rw [ifp (by omega_using [hl]), h8, I.r8, ifp (by omega_using [hl, e]), h12', BitVec.and_zero, BitVec.or_zero]
    · rw [ifp (by omega_using [hl]), h9, I.r9, ifp (by omega_using [hl, e]), h12', BitVec.and_zero, BitVec.or_zero]

section
variable {D lN dN : Nat} {c : Byte} {s : State} (L : Lay D s lN dN c)
include L

/-- The scan of `DB`'s `dbLen` bytes, `w`, at `S + lo`. -/
theorem scan_ok {t : State} (h : Base Sp (vP D) s t) {w : Nat → Byte}
    (hw : ∀ j < dN, view t.mem (Sp s) (lN + j) = w j) :
    WP isa scan t fun t' => Base Sp (vP D) s t' ∧ t'.mem = t.mem ∧
      (∀ r ∈ Reg.r14 :: fx ++ hiRegs ++ ([.r24, .r25, .r26, .r27, .r28, .r29] : List Reg), t'.gpr r = t.gpr r) ∧
      t'.gpr .r8 = BitVec.ofNat 64 (if lzr w dN < dN then lzr w dN else 0) ∧
      t'.gpr .r9 = (if lzr w dN < dN then w (lzr w dN) else 0).setWidth 64 := by
  have F := L.F
  obtain hk := L.hk; have hk2 := L.k2; have hl := L.l1; have hd1 := L.d1
  refine WP.seq (wp_add fun t₁ o₁ e₁ => wp_mov fun t₂ o₂ e₂ => wp_li (by decide) fun t₃ o₃ e₃ =>
    wp_li (by decide) fun t₄ o₄ e₄ => wp_subi fun t₅ o₅ e₅ => wp_li (by decide) fun t₆ o₆ e₆ =>
    wp_li (by decide) fun t₇ o₇ e₇ => wp_nil ?_)
  obtain k₇ : Only [.r4, .r5, .r6, .r7, .r8, .r9] t t₇ :=
    (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans o₇)))))).mono
  obtain I0 : ScanI w (Sp s) lN 0 t₇ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [o₇.get .r4, o₆.get .r4, o₅.get .r4, o₄.get .r4, o₃.get .r4, o₂.get .r4, e₁, h.r14, h.plo, L.hlo]; rfl
    · rw [o₇.get .r6, o₆.get .r6, o₅.get .r6, o₄.get .r6, e₃]
    · rw [o₇.get .r7, o₆.get .r7, e₅, e₄]; rfl
    · rw [o₇.get .r8, e₆]; rfl
    · rw [e₇]; rfl
  refine WP.mono (wp_countdown (cnt := .r5) (N := dN) (by omega_using [hk]) (by omega_using [hd1])
    (fun i u => ScanI w (Sp s) lN i u ∧ Only [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12] t₇ u) ?_
    ⟨I0, Only.refl _ _⟩ (by rw [o₇.get .r5, o₆.get .r5, o₅.get .r5, o₄.get .r5, o₃.get .r5, e₂, o₁.get .r21, h.pdb, L.hdb]))
    fun u ⟨I, o⟩ => ?_
  · intro i hi u ⟨I, o⟩ hc
    refine wp_lbz (a := off (Sp s) (lN + i)) (by rw [I.r4, BitVec.add_zero])
      (by rw [o.rd, o.wr, k₇.rd, k₇.wr, h.wr]; exact sc_inR F (by unfold oRsa; omega_using [hk, hk2, hi]) _) fun u₁ p₁ f₁ => ?_
    refine wp_subi fun u₂ p₂ f₂ => wp_lsr fun u₃ p₃ f₃ => wp_subi fun u₄ p₄ f₄ => wp_and fun u₅ p₅ f₅ =>
      wp_and fun u₆ p₆ f₆ => wp_or fun u₇ p₇ f₇ => wp_and fun u₈ p₈ f₈ => wp_or fun u₉ p₉ f₉ =>
      wp_li (by decide) fun u₁₀ p₁₀ f₁₀ => wp_sub fun u₁₁ p₁₁ f₁₁ => wp_and fun u₁₂ p₁₂ f₁₂ =>
      wp_addi fun u₁₃ p₁₃ f₁₃ => wp_addi fun u₁₄ p₁₄ f₁₄ => wp_subi fun u₁₅ p₁₅ f₁₅ => wp_nil ?_
    obtain q : Only [.r10, .r11, .r12, .r3, .r8, .r9, .r7, .r4, .r6, .r5] u u₁₅ :=
      (p₁.trans (p₂.trans (p₃.trans (p₄.trans (p₅.trans (p₆.trans (p₇.trans (p₈.trans (p₉.trans (p₁₀.trans (p₁₁.trans (p₁₂.trans (p₁₃.trans (p₁₄.trans p₁₅)))))))))))))).mono
    obtain v₁ : u₁₅.gpr .r10 = (w i).setWidth 64 := by
      rw [p₁₅.get .r10, p₁₄.get .r10, p₁₃.get .r10, p₁₂.get .r10, p₁₁.get .r10, p₁₀.get .r10,
        p₉.get .r10, p₈.get .r10, p₇.get .r10, p₆.get .r10, p₅.get .r10, p₄.get .r10, p₃.get .r10, p₂.get .r10, f₁,
        o.mem, k₇.mem, ← hw i hi]; rfl
    obtain p₁' : ∀ r ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9], u₁.gpr r = u.gpr r := fun r hr => p₁.get r (by revert r; decide)
    refine ⟨⟨scan_step I v₁ ?_ ?_ ?_ ?_ ?_ ?_ ?_, (o.trans q).mono⟩, ?_⟩ <;>
      simp (disch := decide) only [p₁₅.gpr, p₁₄.gpr, p₁₃.gpr, p₁₂.gpr, p₁₁.gpr, p₁₀.gpr, p₉.gpr, p₈.gpr, p₇.gpr, p₆.gpr, p₅.gpr, p₄.gpr, p₃.gpr, p₂.gpr, f₁₅, f₁₄, f₁₃, f₁₂, f₁₁, f₁₀, f₉, f₈, f₇, f₆, f₅, f₄, f₃, f₂, p₁' _ (by decide : Reg.r4 ∈ _), p₁' _ (by decide : Reg.r5 ∈ _), p₁' _ (by decide : Reg.r6 ∈ _),
        p₁' _ (by decide : Reg.r7 ∈ _), p₁' _ (by decide : Reg.r8 ∈ _), p₁' _ (by decide : Reg.r9 ∈ _)]
  · have kk : Only [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12] t u := (k₇.trans o).mono
    refine ⟨h.only F kk, by rw [o.mem, k₇.mem], fun r hr => ?_, I.r8, I.r9⟩
    exact kk.gpr r (by revert r; decide)

end

end VG.Proof.RsaPss.PPC64LE

end

end

/-! ### `RsaPss.PPC64LE.Check`, which only this module used -/

section

/-!
# RSASSA-PSS verification on PPC64LE: the delimiter and the salt's length

Untrusted: everything here is checked by Lean. `check_ok`: `posCheck` and
`lenCheck` put in `r24` the accumulator, `EM`'s last byte (the first checks)
ORed with `val ⊕ 1` and, for a given salt length, with its difference from
the salt's (`accW`), and in `r25` the salt's length `dbLen - pos - 1`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (oEm oSt oDig oW oRsa)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off view sc_in sc_inR fx hiRegs)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_addi wp_subi wp_add wp_sub wp_xor wp_or wp_lbz wp_nil
  eval_zero)
open VG.Proof.Mgf1 (ifp ifn)

/-- The accumulator after the delimiter's and the salt length's checks. -/
def accW (a : Byte) (val : BitVec 64) (sl : Nat) (any saltLen : BitVec 64) : BitVec 64 :=
  (a.setWidth 64 ||| (val ^^^ 1#64)) ||| if any = 0 then BitVec.ofNat 64 sl ^^^ saltLen else 0#64

section
variable {D lN dN : Nat} {c : Byte} {s : State} (L : Lay D s lN dN c)
include L

/-- `posCheck`: the accumulator with `val ⊕ 1`, and the salt's length. -/
theorem posCheck_ok {t : State} (h : Base Sp (vP D) s t) {a : Byte} {pos : Nat} {val : BitVec 64}
    (ha : view t.mem (Sp s) ((s.gpr .r4).toNat - 1) = a) (h8 : t.gpr .r8 = BitVec.ofNat 64 pos) (hp : pos < dN)
    (h9 : t.gpr .r9 = val) :
    WP isa (.block posCheck) t fun t' => Base Sp (vP D) s t' ∧ Only [.r4, .r24, .r3, .r9, .r25] t t' ∧
      t'.gpr .r24 = a.setWidth 64 ||| (val ^^^ 1#64) ∧ t'.gpr .r25 = BitVec.ofNat 64 (dN - pos - 1) := by
  have F := L.F
  obtain hk := L.hk; have hk2 := L.k2
  generalize hK : (s.gpr .r4).toNat = kN at hk hk2 ha
  refine wp_add fun t₁ o₁ e₁ => wp_subi fun t₂ o₂ e₂ => ?_
  obtain a₂ : t₂.gpr .r4 = off (Sp s) (kN - 1) := by
    rw [e₂, e₁, h.r14, h.pk, ← ofNat_toNat (s.gpr .r4), hK, off_sub _ (by omega_using [hk]) (by omega_using [hK])]
  refine wp_lbz (a := off (Sp s) (kN - 1)) (by rw [a₂, BitVec.add_zero])
    (by rw [o₂.rd, o₁.rd, o₂.wr, o₁.wr, h.wr]; exact sc_inR F (by unfold oRsa; omega_using [hk2]) _) fun t₃ o₃ e₃ => ?_
  refine wp_li (by decide) fun t₄ o₄ e₄ => wp_xor fun t₅ o₅ e₅ => wp_or fun t₆ o₆ e₆ =>
    wp_sub fun t₇ o₇ e₇ => wp_subi fun t₈ o₈ e₈ => wp_nil ?_
  obtain k₈ : Only [.r4, .r24, .r3, .r9, .r25] t t₈ :=
    (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans (o₇.trans o₈))))))).mono
  refine ⟨h.only F k₈, k₈, ?_, ?_⟩
  · rw [o₈.get .r24, o₇.get .r24, e₆, o₅.get .r24, o₄.get .r24, e₃, e₅, o₄.get .r9, o₃.get .r9, o₂.get .r9,
      o₁.get .r9, h9, e₄, o₂.mem, o₁.mem, ← ha]; rfl
  · rw [e₈, e₇, o₆.get .r21, o₅.get .r21, o₄.get .r21, o₃.get .r21, o₂.get .r21, o₁.get .r21, h.pdb, L.hdb,
      o₆.get .r8, o₅.get .r8, o₄.get .r8, o₃.get .r8, o₂.get .r8, o₁.get .r8, h8,
      Offset.ofNat_sub_ofNat (show pos ≤ dN by omega_using [hp]), Offset.ofNat_sub_ofNat (show 1 ≤ dN - pos by omega_using [hp])]

/-- `lenCheck`: for a given salt length, the accumulator with the salt's
length's difference from it. -/
theorem lenCheck_ok {t : State} (h : Base Sp (vP D) s t) {v : BitVec 64} {sl : Nat} (h24 : t.gpr .r24 = v)
    (h25 : t.gpr .r25 = BitVec.ofNat 64 sl) :
    WP isa lenCheck t fun t' => Base Sp (vP D) s t' ∧ Only [.r3, .r24] t t' ∧
      t'.gpr .r24 = v ||| if anyL s = 0 then BitVec.ofNat 64 sl ^^^ stackArg s 0 else 0#64 := by
  have F := L.F
  refine WP.ite _ (eval_zero _ _) (fun hz => ?_) (fun hz => ?_)
  · have ha0 : anyL s = 0 := by rw [← h.pany]; simpa using hz
    refine wp_xor fun w₁ p₁ f₁ => wp_or fun w p f => ?_
    obtain q : Only [.r3, .r24] t w := (p₁.trans p).mono
    refine wp_nil ⟨h.only F q, q, ?_⟩
    rw [f, p₁.get .r24, h24, f₁, h25, h.psl, ifp ha0]
  · have ha0 : anyL s ≠ 0 := by rw [← h.pany]; simpa using hz
    refine wp_nil ⟨h, Only.refl _ t, ?_⟩
    rw [h24, ifn ha0, BitVec.or_zero]

theorem check_ok {t : State} (h : Base Sp (vP D) s t) {a : Byte} {pos : Nat} {val : BitVec 64}
    (ha : view t.mem (Sp s) ((s.gpr .r4).toNat - 1) = a) (h8 : t.gpr .r8 = BitVec.ofNat 64 pos) (hp : pos < dN)
    (h9 : t.gpr .r9 = val) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ t', Base Sp (vP D) s t' → t'.mem = t.mem →
      (∀ r ∈ Reg.r14 :: fx ++ hiRegs ++ ([.r8, .r26, .r27, .r28, .r29] : List Reg), t'.gpr r = t.gpr r) →
      t'.gpr .r24 = accW a val (dN - pos - 1) (anyL s) (stackArg s 0) →
      t'.gpr .r25 = BitVec.ofNat 64 (dN - pos - 1) → t'.syms = t.syms → WP isa rest t' Q) :
    WP isa (.seq (.block posCheck) (.seq lenCheck rest)) t Q :=
  WP.seq (WP.mono_syms (posCheck_ok L h ha h8 hp h9) fun t₈ ⟨b₈, k₈, x24, x25⟩ y₈ =>
    WP.seq (WP.mono_syms (lenCheck_ok L b₈ x24 x25) fun w ⟨b, q, x⟩ yw => k w b (by rw [q.mem, k₈.mem])
      (fun r hr => by rw [q.gpr r (by revert r; decide), k₈.gpr r (by revert r; decide)])
      (by rw [x]; rfl) (by rw [q.get .r25, x25]) (yw.trans y₈)))

end

end VG.Proof.RsaPss.PPC64LE

end

end


/-!
# RSASSA-PSS verification on PPC64LE: after the public operation

Untrusted: everything here is checked by Lean. `post_ok`: from `EM` in its
place (the view `V`), the code after the call returns 1 exactly when `Res`
holds: the accumulator of the checks (`accR`: `0xbc`, the leading byte, the
top bits, the delimiter and, for a given salt length, the salt's length) is
zero and `H` is the hash of `M'` (`mR`), from `DB` unmasked (`dbV`), the first
nonzero byte of `DB` (`lzr`) and the salt's length.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (oEm oSt oDig oW oRsa Fns mgfXorT)
open VG.Impl.MdStream.PPC64LE (Params)
open VG.Proof.MdStream (Md)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off view fx hiRegs Same hfits offs TabS)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_nil eval_zero)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Proof.RsaOaep (mixV srcB)

section
variable (Gm Gs : Spec.Mgf1.Hash) (V : Nat → Byte) (D lN dN : Nat) (c : Byte) (k : Nat) (mh : List Byte)
  (any saltLen : BitVec 64)

/-- `EM` after `acc0`. -/
def v1 : Nat → Byte := fun o => if o = k - 1 then accB V lN c k else V o

/-- `DB`'s bytes, unmasked. -/
def wR (j : Nat) : Byte := dbV Gm (v1 V lN c k) lN dN D c (lN + j)

/-- The position of the first nonzero byte of `DB`, and its value. -/
def posR : Nat := if lzr (wR Gm V D lN dN c k) dN < dN then lzr (wR Gm V D lN dN c k) dN else 0
def valR : Byte := if lzr (wR Gm V D lN dN c k) dN < dN then wR Gm V D lN dN c k (lzr (wR Gm V D lN dN c k) dN) else 0

/-- The salt's length. -/
def slR : Nat := dN - posR Gm V D lN dN c k - 1

/-- The accumulator. -/
def accR : BitVec 64 :=
  accW (accB V lN c k) ((valR Gm V D lN dN c k).setWidth 64) (slR Gm V D lN dN c k) any saltLen

/-- `M'`. -/
def mR : List Byte :=
  if any = 0 then mFix (dbV Gm (v1 V lN c k) lN dN D c) mh lN dN saltLen.toNat
  else mAny (dbV Gm (v1 V lN c k) lN dN D c) mh lN dN (posR Gm V D lN dN c k) (slR Gm V D lN dN c k)

/-- What makes the result 1. -/
def Res : Prop :=
  accR Gm V D lN dN c k any saltLen = 0#64 ∧
    ∀ i < D, V (lN + dN + i) = (Gs.hash (mR Gm V D lN dN c k mh any saltLen)).getD i 0

instance : Decidable (Res Gm Gs V D lN dN c k mh any saltLen) := by unfold Res; infer_instance

end

theorem dbV_congr {Gm : Spec.Mgf1.Hash} {V V' : Nat → Byte} {lN dN D : Nat} {c : Byte} (hf : lN + dN + D ≤ 1024)
    (h : ∀ o < 1024, V o = V' o) {o : Nat} (ho : o < 1024) : dbV Gm V lN dN D c o = dbV Gm V' lN dN D c o := by
  obtain hs : srcB V (lN + dN) D = srcB V' (lN + dN) D :=
    List.map_congr_left fun i hi => h _ (by have := List.mem_range.mp hi; omega_arith)
  simp only [dbV, mixV, hs, h o ho]

theorem xor1_lt (b : Byte) : ((b.setWidth 64) ^^^ 1#64).toNat < 2 ^ 63 := by
  rw [BitVec.toNat_xor]; exact Nat.xor_lt_two_pow (byte_lt b) (by decide)

section
variable {D lN dN : Nat} {c : Byte} {s : State} (L : Lay D s lN dN c) {H : Hash} (hH : HashOK H)
include L hH

theorem post_ok (hD : H.D = D) {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hH.SH.H.hash x)
    {G : Hash} (hG : HashOK G) {g : Fns} {pg : Addr} (Tg : TabS G g gArg Sp s pg) {Gm : Spec.Mgf1.Hash}
    (hGmh : ∀ x, Gm.hash x = hG.SH.H.hash x) (hGml : Gm.len = G.D) (hGmv : Proof.Mgf1.Valid Gm)
    {cn dn : String} {cc dc : Prog isa} {f : MdFns} {p : Addr} (T : MdTabS H cn cc dn dc f hArg Sp s p)
    {P : Params} {md : Md P.B P.N P.L} (ok : CtOK P md cc dc) {iv : md.HV} (hl : md.Link hH.SH iv D)
    (hN : H.N = P.N) (hB : H.B = P.B) {t : State} (h : Base Sp (vP D) s t) (sy : t.syms = s.syms)
    (hfit : anyL s = 0 → (stackArg s 0).toNat + 1 ≤ dN) :
    WP isa (.seq (.block acc0) (.seq (.block (dbArgs H)) (.seq (mgfXorT g gArg) (.seq (.block clearTop) (.seq scan
      (.seq (.block posCheck) (.seq lenCheck (finish H P f)))))))) t fun t' => Base Sp (vP D) s t' ∧
      t'.gpr .r3 = if Res Gm Gs (view t.mem (Sp s)) D lN dN c (s.gpr .r4).toNat (mh D s) (anyL s) (stackArg s 0)
        then 1#64 else 0#64 := by
  have F := L.F
  obtain ⟨hE, hSt, hDg, hCt, hW, hRs⟩ := offs
  obtain hk := L.hk; have hk2 := L.k2; have hD0 := L.D0; have hD64 := L.D64; have hd1 := L.d1
  generalize hK : (s.gpr .r4).toNat = k at hk hk2
  let V := view t.mem (Sp s)
  refine WP.seq (WP.mono_syms (acc0_ok L h) fun t₁ ⟨b₁, g₁, v₁⟩ y₁ => ?_)
  rw [hK] at v₁
  refine unmask_ok L hD hG Tg hGmh hGml hGmv b₁ (y₁.trans sy) fun t₂ b₂ y₂ v₂ => ?_
  obtain e₁ : ∀ o < 1024, view t₁.mem (Sp s) o = v1 V lN c k o := fun o ho => by rw [v₁ o (by omega_arith)]; rfl
  obtain W : ∀ o < 1024, view t₂.mem (Sp s) o = dbV Gm (v1 V lN c k) lN dN D c o := fun o ho => by
    rw [v₂ o (by omega_arith), dbV_congr (by omega_arith) e₁ ho]
  refine WP.seq (WP.mono_syms (scan_ok L b₂ (w := wR Gm V D lN dN c k) fun j hj => by rw [W _ (by omega_arith)]; rfl)
    fun t₃ ⟨b₃, m₃, g₃, x8, x9⟩ y₃ => ?_)
  obtain hpos : posR Gm V D lN dN c k < dN := by
    unfold posR; split <;> omega_arith
  obtain ha : view t₃.mem (Sp s) ((s.gpr .r4).toNat - 1) = accB V lN c k := by
    rw [hK, m₃, W _ (by omega_arith), dbV]
    simp only [mixV]
    rw [ifn (by omega_arith), ifn (by omega_arith), v1, ifp rfl]
  refine check_ok L b₃ (a := accB V lN c k) (pos := posR Gm V D lN dN c k)
    (val := (valR Gm V D lN dN c k).setWidth 64) ha x8 hpos x9 fun t₄ b₄ m₄ g₄ x24 x25 y₄ => ?_
  obtain sy₄ : t₄.syms = s.syms := y₄.trans (y₃.trans y₂)
  obtain W₄ : ∀ o < 1024, view t₄.mem (Sp s) o = dbV Gm (v1 V lN c k) lN dN D c o := fun o ho => by
    rw [m₄, m₃, W o ho]
  obtain vH : ∀ i < D, dbV Gm (v1 V lN c k) lN dN D c (lN + dN + i) = V (lN + dN + i) := fun i hi => by
    simp only [dbV, mixV]; rw [ifn (by omega_arith), ifn (by omega_arith), v1, ifn (by omega_arith)]
  obtain hacc : (t₄.gpr .r24).toNat < 2 ^ 63 := by
    rw [x24, accW]
    refine or_lt (or_lt (byte_lt _) (xor1_lt _)) ?_
    split
    · rename_i h0
      rw [BitVec.toNat_xor, BitVec.toNat_ofNat]
      have := hfit h0
      exact Nat.xor_lt_two_pow (by omega_arith) (by omega_arith)
    · decide
  have x24' : t₄.gpr .r24 = accR Gm V D lN dN c k (anyL s) (stackArg s 0) := x24
  refine WP.ite _ (eval_zero _ _) (fun hz => ?_) (fun hz => ?_)
  all_goals have g20 : t₄.gpr .r20 = anyL s := by rw [g₄ _ (by decide), g₃ _ (by decide), b₂.pany]
  · have h0 : anyL s = 0 := by rw [g20] at hz; simpa using hz
    obtain hM : mFix (view t₄.mem (Sp s)) (mh D s) lN dN (stackArg s 0).toNat =
        mR Gm V D lN dN c k (mh D s) (anyL s) (stackArg s 0) := by
      rw [mR, ifp h0]
      have := hfit h0
      simp only [mFix]
      refine congrArg (_ ++ ·) (List.map_congr_left fun j hj => W₄ _ ?_)
      have := List.mem_range.mp hj; omega_arith
    refine WP.mono (fixed_ok L hH T hD hGh b₄ sy₄ (hfit h0) hacc) fun t' ⟨b', r'⟩ => ⟨b', ?_⟩
    rw [r', hM]
    by_cases e : Res Gm Gs V D lN dN c k (mh D s) (anyL s) (stackArg s 0)
    · rw [ifp e, ifp ⟨by rw [x24']; exact e.1, fun i hi => by rw [W₄ _ (by omega_arith), vH i hi]; exact e.2 i hi⟩]
    · rw [ifn e, ifn fun h' => e ⟨by rw [← x24']; exact h'.1, fun i hi => by
        rw [← vH i hi, ← W₄ _ (by omega_arith)]; exact h'.2 i hi⟩]
  · have h0 : anyL s ≠ 0 := by rw [g20] at hz; simpa using hz
    obtain hM : mAny (view t₄.mem (Sp s)) (mh D s) lN dN (posR Gm V D lN dN c k) (slR Gm V D lN dN c k) =
        mR Gm V D lN dN c k (mh D s) (anyL s) (stackArg s 0) := by
      rw [mR, ifn h0]
      simp only [mAny]
      refine congrArg (List.replicate 8 0 ++ mh D s ++ ·) (List.map_congr_left fun j hj => ?_)
      split
      · rw [W₄ _ (by omega_arith)]
      · rfl
    obtain hsl : slR Gm V D lN dN c k + posR Gm V D lN dN c k + 1 = dN := by unfold slR; omega_arith
    refine WP.mono (any_ok L hH T hD hGh ok hl hN hB b₄ sy₄ (pos := posR Gm V D lN dN c k)
      (sl := slR Gm V D lN dN c k) (by rw [g₄ _ (by decide), x8]; rfl) hpos x25 hsl hacc) fun t' ⟨b', r'⟩ => ⟨b', ?_⟩
    rw [r', hM]
    by_cases e : Res Gm Gs V D lN dN c k (mh D s) (anyL s) (stackArg s 0)
    · rw [ifp e, ifp ⟨by rw [x24']; exact e.1, fun i hi => by rw [W₄ _ (by omega_arith), vH i hi]; exact e.2 i hi⟩]
    · rw [ifn e, ifn fun h' => e ⟨by rw [← x24']; exact h'.1, fun i hi => by
        rw [← vH i hi, ← W₄ _ (by omega_arith)]; exact h'.2 i hi⟩]

end

end VG.Proof.RsaPss.PPC64LE

end

end

/-!
# RSASSA-PSS verification on PPC64LE: the checks are EMSA-PSS-VERIFY's

Untrusted: everything here is checked by Lean. For `EM` of `emLen = E`
bytes after `lo` (`lN`) in the view `V`, `DB` unmasked as the code does
(`wR`) is `Proof.RsaPss.vDb` (`wR_eq`), and `Res` (`Post.lean`) holds
exactly when the leading byte is zero if `lo = 1` and the encoding is
consistent byte by byte (`Proof.RsaPss.EncOk`, `res_iff`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG
open VG.Proof.RsaPss (lz vDb vH EncOk)
open VG.Proof.RsaPss (xorBytes_getD clearTop_getD zeros_getD eq_range_map)
open VG.Proof.RsaOaep (mixV srcB)
open VG.Proof.Mgf1 (ifp ifn Valid mgf1_length xorBytes_length)
open VG.Spec.RsaPss (zeros clearTop)

section
variable {Gs Gm : Spec.Mgf1.Hash} {V : Nat → Byte} {em : List Byte} {lN E : Nat} {c : Byte} {z : Nat}

theorem vH_getD (hfE : Gs.len + 2 ≤ E) (hV : ∀ i < E, V (lN + i) = em.getD i 0) {i : Nat} (hi : i < Gs.len) :
    (vH Gs em (E - Gs.len - 1)).getD i 0 = V (lN + (E - Gs.len - 1) + i) := by
  simp only [vH, List.getD_eq_getElem?_getD, List.getElem?_take, ifp hi, List.getElem?_drop]
  rw [← List.getD_eq_getElem?_getD, Nat.add_assoc, hV _ (by omega_arith)]

theorem vH_length (hE : em.length = E) (hfE : Gs.len + 2 ≤ E) : (vH Gs em (E - Gs.len - 1)).length = Gs.len := by
  simp only [vH, List.length_take, List.length_drop, hE]; omega_arith

theorem srcB_vH (hE : em.length = E) (hfE : Gs.len + 2 ≤ E) (hV : ∀ i < E, V (lN + i) = em.getD i 0) :
    srcB (v1 V lN c (lN + E)) (lN + (E - Gs.len - 1)) Gs.len = vH Gs em (E - Gs.len - 1) := by
  refine (eq_range_map (vH_length hE hfE) fun i hi => ?_).symm
  rw [vH_getD hfE hV hi, v1, ifn (by omega_arith)]

theorem wR_eq (hGv : Valid Gm) (hc : c = (0xFF : Byte) >>> z) (hE : em.length = E) (hfE : Gs.len + 2 ≤ E)
    (hV : ∀ i < E, V (lN + i) = em.getD i 0) {j : Nat} (hj : j < E - Gs.len - 1) :
    wR Gm V Gs.len lN (E - Gs.len - 1) c (lN + E) j = (vDb₂ Gm Gs em (E - Gs.len - 1) z).getD j 0 := by
  have hmk := mgf1_length hGv (vH Gs em (E - Gs.len - 1)) (E - Gs.len - 1)
  have ht : ∀ {i}, i < E - Gs.len - 1 → (em.take (E - Gs.len - 1)).getD i 0 = em.getD i 0 := fun hi => by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, ifp hi]
  let mk := Spec.Mgf1.mgf1 Gm (vH Gs em (E - Gs.len - 1)) (E - Gs.len - 1)
  have hm : mixV (v1 V lN c (lN + E)) (Spec.Mgf1.mgf1 Gm (srcB (v1 V lN c (lN + E)) (lN + (E - Gs.len - 1)) Gs.len)
      (E - Gs.len - 1)) lN (E - Gs.len - 1) (lN + j) = em.getD j 0 ^^^ mk.getD j 0 := by
    rw [srcB_vH hE hfE hV, mixV, ifp ⟨by omega_arith, by omega_arith⟩, v1, ifn (by omega_arith), hV _ (by omega_arith),
      Nat.add_sub_cancel_left]
  have hx : (Spec.Mgf1.xorBytes (em.take (E - Gs.len - 1)) mk).getD j 0 = em.getD j 0 ^^^ mk.getD j 0 := by
    rw [xorBytes_getD (by rw [List.length_take, hE]; omega_arith) (by simp only [mk]; omega_arith), ht hj]
  show (if lN + j = lN then _ &&& c else _) = _
  rw [vDb₂, clearTop_getD]
  by_cases e : j = 0
  · subst e
    rw [ifp (Nat.add_zero lN), ifp rfl, hm, ← hx, hc]
  · rw [ifn (by omega_arith), ifn e, hm, ← hx]

end

section
variable {Gs Gm : Spec.Mgf1.Hash} (hGv : Valid Gm) {V : Nat → Byte} {em mh : List Byte} {lN E : Nat} {c : Byte}
  {z : Nat} (hc : c = (0xFF : Byte) >>> z) (hE : em.length = E) (hfE : Gs.len + 2 ≤ E)
  (hV : ∀ i < E, V (lN + i) = em.getD i 0)

include hGv hc hE hfE hV in
theorem db_eq : vDb₂ Gm Gs em (E - Gs.len - 1) z = (List.range (E - Gs.len - 1)).map (wR Gm V Gs.len lN (E - Gs.len - 1) c (lN + E)) := by
  refine eq_range_map (by simp [vDb₂, VG.Proof.RsaPss.clearTop_length, xorBytes_length, mgf1_length hGv, hE]; omega_arith)
    fun j hj => (wR_eq hGv hc hE hfE hV hj).symm

include hGv hc hE hfE hV in
theorem lzr_eq : lzr (wR Gm V Gs.len lN (E - Gs.len - 1) c (lN + E)) (E - Gs.len - 1) = lz (vDb₂ Gm Gs em (E - Gs.len - 1) z) := by
  rw [db_eq hGv hc hE hfE hV]; rfl

include hGv hc hE hfE hV in
/-- `M'` is the specification's once the delimiter is found and the salt
length is the expected one. -/
theorem mR_eq (hmh : mh.length = Gs.len) {any saltLen : BitVec 64}
    (hlz : lz (vDb₂ Gm Gs em (E - Gs.len - 1) z) < E - Gs.len - 1)
    (hsl : any = 0 → saltLen.toNat = E - Gs.len - 1 - 1 - lz (vDb₂ Gm Gs em (E - Gs.len - 1) z)) :
    mR Gm V Gs.len lN (E - Gs.len - 1) c (lN + E) mh any saltLen =
      zeros 8 ++ mh ++ (vDb₂ Gm Gs em (E - Gs.len - 1) z).drop (lz (vDb₂ Gm Gs em (E - Gs.len - 1) z) + 1) := by
  have hl := lzr_eq hGv hc hE hfE hV
  generalize hdb : vDb₂ Gm Gs em (E - Gs.len - 1) z = db at hl hlz hsl
  have hdl : db.length = E - Gs.len - 1 := by
    rw [← hdb]; simp [vDb₂, VG.Proof.RsaPss.clearTop_length, xorBytes_length, mgf1_length hGv, hE]; omega
  have hp : posR Gm V Gs.len lN (E - Gs.len - 1) c (lN + E) = lz db := by rw [posR, hl, ifp hlz]
  have hw : ∀ j < E - Gs.len - 1, dbV Gm (v1 V lN c (lN + E)) lN (E - Gs.len - 1) Gs.len c (lN + j) = db.getD j 0 :=
    fun j hj => by rw [← hdb, ← wR_eq hGv hc hE hfE hV hj]; rfl
  have hd : ∀ j < E - Gs.len - 1 - lz db - 1, (db.drop (lz db + 1)).getD j 0 =
      dbV Gm (v1 V lN c (lN + E)) lN (E - Gs.len - 1) Gs.len c (lN + (j + (lz db + 1))) := fun j hj => by
    rw [hw _ (by omega_using [hj])]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
    congr 2; omega_using []
  have hdd : (db.drop (lz db + 1)).length = E - Gs.len - 1 - lz db - 1 := by rw [List.length_drop, hdl]; omega_using []
  rw [mR]
  split
  · rename_i h0
    have h1 := hsl h0
    rw [mFix, h1, show E - Gs.len - 1 - 1 - lz db = E - Gs.len - 1 - lz db - 1 by omega_using []]
    refine congrArg (List.replicate 8 0 ++ mh ++ ·) (eq_range_map hdd fun j hj => ?_).symm
    rw [hd j (by omega_using [hj])]; congr 1; omega_using [hlz]
  · rw [mAny, hp, slR, hp]
    refine congrArg (List.replicate 8 0 ++ mh ++ ·) (eq_range_map hdd fun j hj => ?_).symm
    rw [hd j (by omega_using [hj]), ifp (by omega_using [hj])]

end

theorem setWidth64_eq_zero (a : Byte) : a.setWidth 64 = 0#64 ↔ a = 0 := by
  constructor
  · intro h
    have := congrArg (BitVec.setWidth 8) h
    rwa [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq] at this
  · rintro rfl; rfl

theorem setWidth64_xor1 (a : Byte) : (a.setWidth 64 ^^^ 1#64) = 0#64 ↔ a = 1 := by
  rw [BitVec.xor_eq_zero_iff]
  constructor
  · intro h
    have := congrArg (BitVec.setWidth 8) h
    rwa [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq] at this
  · rintro rfl; rfl

section
variable {Gs Gm : Spec.Mgf1.Hash} (hGv : Valid Gm) {V : Nat → Byte} {em mh : List Byte} {lN E : Nat} {c : Byte}
  {z : Nat} (hc : c = (0xFF : Byte) >>> z) (hE : em.length = E) (hfE : Gs.len + 2 ≤ E)
  (hV : ∀ i < E, V (lN + i) = em.getD i 0) (hmh : mh.length = Gs.len) (hHv : Valid Gs)
include hGv hc hE hfE hV hmh hHv

theorem res_iff {any saltLen : BitVec 64} {sLen : Option Nat} (hs : sLen = if any = 0 then some saltLen.toNat else none)
    (hE64 : E < 2 ^ 64) :
    Res Gm Gs V Gs.len lN (E - Gs.len - 1) c (lN + E) mh any saltLen ↔
      (lN = 1 → V 0 = 0) ∧ EncOk₂ Gm Gs mh em E z sLen := by
  have hl := lzr_eq hGv hc hE hfE hV
  have hw : ∀ j < E - Gs.len - 1, wR Gm V Gs.len lN (E - Gs.len - 1) c (lN + E) j =
      (vDb₂ Gm Gs em (E - Gs.len - 1) z).getD j 0 := fun j hj => wR_eq hGv hc hE hfE hV hj
  have hk1 : lN + E - 1 = lN + (E - 1) := by omega_arith
  have hV0 : V lN = em.getD 0 0 := hV 0 (by omega_arith)
  have hVk : V (lN + E - 1) = em.getD (E - 1) 0 := by rw [hk1]; exact hV _ (by omega_arith)
  have hnot : ~~~c = ~~~((0xFF : Byte) >>> z) := by rw [hc]
  -- The hash compared, as lists.
  have hcmp : ∀ M : List Byte, (∀ i < Gs.len, V (lN + (E - Gs.len - 1) + i) = (Gs.hash M).getD i 0) ↔
      Gs.hash M = vH Gs em (E - Gs.len - 1) := fun M => by
    constructor
    · intro h
      refine List.ext_getElem (by rw [hHv.2, vH_length hE hfE]) fun i h₁ h₂ => ?_
      have e := h i (by rw [hHv.2] at h₁; exact h₁)
      rw [← vH_getD hfE hV (by rw [hHv.2] at h₁; exact h₁), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem h₁, List.getElem?_eq_getElem h₂] at e
      exact e.symm
    · intro h i hi; rw [h, vH_getD hfE hV hi]
  have hval : valR Gm V Gs.len lN (E - Gs.len - 1) c (lN + E) = 1 ↔
      lz (vDb₂ Gm Gs em (E - Gs.len - 1) z) < E - Gs.len - 1 ∧
        (vDb₂ Gm Gs em (E - Gs.len - 1) z).getD (lz (vDb₂ Gm Gs em (E - Gs.len - 1) z)) 0 = 1 := by
    unfold valR; rw [hl]
    by_cases h : lz (vDb₂ Gm Gs em (E - Gs.len - 1) z) < E - Gs.len - 1
    · rw [ifp h, hw _ h]; simp [h]
    · rw [ifn h]; simp [h]
  have hsl : lz (vDb₂ Gm Gs em (E - Gs.len - 1) z) < E - Gs.len - 1 →
      slR Gm V Gs.len lN (E - Gs.len - 1) c (lN + E) = E - Gs.len - 1 - 1 - lz (vDb₂ Gm Gs em (E - Gs.len - 1) z) :=
    fun h => by unfold slR posR; rw [hl, ifp h]; omega_arith
  have hsv : (sLen = none ∨ sLen = some (E - Gs.len - 1 - 1 - lz (vDb₂ Gm Gs em (E - Gs.len - 1) z))) ↔
      (any = 0 → saltLen.toNat = E - Gs.len - 1 - 1 - lz (vDb₂ Gm Gs em (E - Gs.len - 1) z)) := by
    rw [hs]; split
    · rename_i h0; simp [h0]
    · rename_i h0; exact ⟨fun _ e => absurd e h0, fun _ => Or.inl rfl⟩
  have hany : lz (vDb₂ Gm Gs em (E - Gs.len - 1) z) < E - Gs.len - 1 →
      ((if any = 0 then BitVec.ofNat 64 (slR Gm V Gs.len lN (E - Gs.len - 1) c (lN + E)) ^^^ saltLen else 0#64) =
        0#64 ↔ (any = 0 → saltLen.toNat = E - Gs.len - 1 - 1 - lz (vDb₂ Gm Gs em (E - Gs.len - 1) z))) := fun h => by
    rw [hsl h]
    split
    · rename_i h0
      rw [BitVec.xor_eq_zero_iff]
      constructor
      · intro e _; rw [← e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
      · intro e; rw [← e h0, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rename_i h0; exact ⟨fun _ e => absurd e h0, fun _ => rfl⟩
  unfold Res accR accW EncOk₂
  rw [BitVec.or_eq_zero_iff, BitVec.or_eq_zero_iff, setWidth64_eq_zero, accB_eq_zero, setWidth64_xor1, hVk, hV0, hnot]
  constructor
  · rintro ⟨⟨⟨⟨ha1, ha2, ha3⟩, hv⟩, hy⟩, hh⟩
    obtain ⟨hlz, h1⟩ := hval.mp hv
    have hy' := (hany hlz).mp hy
    refine ⟨ha3, ha1, ha2, hlz, h1, hsv.mpr hy', ?_⟩
    rw [← mR_eq hGv hc hE hfE hV hmh hlz hy']
    exact (hcmp _).mp hh
  · rintro ⟨ha3, ha1, ha2, hlz, h1, hy, hh⟩
    have hy' := hsv.mp hy
    refine ⟨⟨⟨⟨ha1, ha2, ha3⟩, hval.mpr ⟨hlz, h1⟩⟩, (hany hlz).mpr hy'⟩, ?_⟩
    rw [mR_eq hGv hc hE hfE hV hmh hlz hy']
    exact (hcmp _).mpr hh
end

end VG.Proof.RsaPss.PPC64LE

end

end

/-!
# RSASSA-PSS verification on PPC64LE: correctness

Untrusted: everything here is checked by Lean. The checks (`checks_done`): a
modulus whose first byte is zero (`verify_zero₂`), and an encoding too short
for the digest (`chkEm`) or the salt length expected (`expLen`, `chkSalt`:
`verify_short₂`) return 0; otherwise RSAVP1 of the signature (`call_ok`) and
the checks of `EM` (`post_ok`) return 1 exactly when EMSA-PSS-VERIFY accepts
it (`res_iff`, `verify_bytes₂`), if `pre` holds the modulus' values.
`code_correct`: the function against its shared contract.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (frameBytes restore Fns tword)
open VG.Impl.MdStream.PPC64LE (Params)
open VG.Proof.MdStream (Md)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off view kR fx hiRegs Saves restore_ok freed_gpr ne_zero_ltBit msgBit
  TabS)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only wp_li wp_sub wp_subi wp_lsr wp_or wp_mov wp_nil eval_zero eval_nonzero)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.Mgf1 (ifp ifn)

/-- What the function returns, from its entry state. -/
def vOut (Gs Gm : Spec.Mgf1.Hash) (s : State) : Bool :=
  Spec.RsaPss.verify Gs Gm (Spec.Rsa.bytesAt s.mem (s.gpr .r3) (kk s))
    (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) (mh Gs.len s) (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (kk s))
    (Spec.RsaPss.expectedSaltLen (stackArg s 0) ((stackArg s 1).setWidth 32))

/-- The result, from the entry state `s`. -/
def Post (Gs Gm : Spec.Mgf1.Hash) (s s' : State) : Prop :=
  abiPreserved s s' ∧ (PreOk s → s'.gpr .r3 = if vOut Gs Gm s then 1 else 0)

/-- Before the restores. -/
def Done (Gs Gm : Spec.Mgf1.Hash) (s t : State) : Prop :=
  Saves s t ∧ (PreOk s → t.gpr .r3 = if vOut Gs Gm s then 1 else 0)

/-- `lo` and `c`, from the modulus' first byte. -/
def loN (s : State) : Nat := if (s.mem (s.gpr .r3)).toNat = 1 then 1 else 0
def cB (s : State) : Byte :=
  if (s.mem (s.gpr .r3)).toNat = 1 then 0xFF else BitVec.ofNat 8 (2 ^ Nat.log2 (s.mem (s.gpr .r3)).toNat - 1)

theorem anyL_eq (s : State) : anyL s = 0 ↔ (stackArg s 1).setWidth 32 = 0 := by
  unfold anyL
  rw [BitVec.ushiftRight_zero, ← BitVec.toNat_inj, ← BitVec.toNat_inj (y := 0)]
  simp only [BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (by have := (stackArg s 1).toNat.mod_lt (show 0 < 2 ^ 32 by decide); omega_arith)]
  simp

theorem sLen_eq (s : State) : Spec.RsaPss.expectedSaltLen (stackArg s 0) ((stackArg s 1).setWidth 32) =
    if anyL s = 0 then some (stackArg s 0).toNat else none := by
  unfold Spec.RsaPss.expectedSaltLen
  by_cases h : anyL s = 0
  · rw [ifp h, ifp ((anyL_eq s).mp h)]
  · rw [ifn h, ifn fun h' => h ((anyL_eq s).mpr h')]

theorem bytesAt_cons (m : Mem) (p : Addr) (n : Nat) :
    ∃ rest : List Byte, Spec.Rsa.bytesAt m p (n + 1) = m p :: rest ∧ rest.length = n :=
  ⟨(List.range n).map fun i => m (p + BitVec.ofNat 64 (i + 1)), by
    simp only [Spec.Rsa.bytesAt, List.range_succ_eq_map, List.map_cons, List.map_map]
    rw [show p + BitVec.ofNat 64 0 = p by simp]; rfl, by simp⟩

theorem bytesAt_getD (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (Spec.Rsa.bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, hi]

theorem emOf_length (s : State) : (emOf s).length = kk s := by
  unfold emOf
  cases hp : Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .r3) (kk s))
    (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (kk s)) with
  | none => simp
  | some y => rw [Option.getD_some, Proof.RsaPss.publicOpChecked_length' hp, bytesAt_length]

/-! ## The specification's cases -/

section
variable (Gs Gm : Spec.Mgf1.Hash) {s : State} (hk : 1 ≤ kk s)
include hk

theorem nB_cons : ∃ rest : List Byte, Spec.Rsa.bytesAt s.mem (s.gpr .r3) (kk s) = s.mem (s.gpr .r3) :: rest ∧
    rest.length = kk s - 1 := by
  obtain ⟨rest, h, hl⟩ := bytesAt_cons s.mem (s.gpr .r3) (kk s - 1)
  rw [show kk s - 1 + 1 = kk s by omega_arith] at h
  exact ⟨rest, h, hl⟩

theorem zero_false (h0 : s.mem (s.gpr .r3) = 0) : vOut Gs Gm s = false := by
  obtain ⟨rest, hn, -⟩ := nB_cons hk
  rw [vOut, hn, h0]
  exact Proof.RsaPss.verify_zero₂ Gm Gs _ _ _ _ _

theorem emLen_eq (h0 : s.mem (s.gpr .r3) ≠ 0) {rest : List Byte} (hr : rest.length = kk s - 1) :
    Spec.RsaPss.emLength (Spec.RsaPss.bitLength (Spec.Rsa.os2ip (s.mem (s.gpr .r3) :: rest)) - 1) =
      kk s - loN s := by
  rw [Proof.RsaPss.emLength_eq rest h0, hr, loN]; split <;> omega_arith

theorem short_false (h0 : s.mem (s.gpr .r3) ≠ 0)
    (h : kk s - loN s < Gs.len + (Spec.RsaPss.expectedSaltLen (stackArg s 0) ((stackArg s 1).setWidth 32)).getD 0 + 2) :
    vOut Gs Gm s = false := by
  obtain ⟨rest, hn, hr⟩ := nB_cons hk
  rw [vOut, hn]
  exact Proof.RsaPss.verify_short₂ Gm Gs _ _ _ (by rw [emLen_eq hk h0 hr]; exact h)

end

/-- `Res` is verification, for `EM` in place. -/
theorem res_vOut {Gs Gm : Spec.Mgf1.Hash} (hGv : Proof.Mgf1.Valid Gm) (hHv : Proof.Mgf1.Valid Gs) {s : State}
    (P : PreP Gs.len s)
    (h0 : s.mem (s.gpr .r3) ≠ 0) {m : Mem} (hm : Spec.Rsa.bytesAt m (off (Sp s) 0) (kk s) = emOf s)
    (hem : Gs.len + 2 ≤ kk s - loN s)
    (hfit : anyL s = 0 → (stackArg s 0).toNat + 1 ≤ kk s - loN s - Gs.len - 1) :
    Res Gm Gs (view m (Sp s)) Gs.len (loN s) (kk s - loN s - Gs.len - 1) (cB s) (kk s) (mh Gs.len s) (anyL s)
      (stackArg s 0) ↔ vOut Gs Gm s = true := by
  have hk1 : 64 ≤ kk s := P.k1; have hk2 : kk s ≤ 1024 := P.k2
  have hl1 : loN s ≤ 1 := by unfold loN; split <;> omega_arith
  obtain ⟨rest, hn, hr⟩ := nB_cons (show 1 ≤ kk s by omega_arith)
  have hE := emLen_eq (by omega_arith) h0 hr
  have hM := Proof.RsaPss.mask_eq rest h0
  have hx : (Spec.Rsa.publicOpChecked (s.mem (s.gpr .r3) :: rest) (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (kk s))).getD (Spec.RsaPss.zeros (s.mem (s.gpr .r3) :: rest).length) =
      emOf s := by
    rw [emOf, hn, Spec.RsaPss.zeros, List.length_cons, hr, show kk s - 1 + 1 = kk s by omega_arith]
  generalize hB : Spec.RsaPss.bitLength (Spec.Rsa.os2ip (s.mem (s.gpr .r3) :: rest)) - 1 = eb at hE hM
  generalize hEg : Spec.RsaPss.emLength eb = E at hE hM
  have hc : cB s = (0xFF : Byte) >>> (8 * E - eb) := by rw [hM]; rfl
  have hV : ∀ i < E, view m (Sp s) (loN s + i) = ((emOf s).drop (loN s)).getD i 0 := fun i hi => by
    show m (off (Sp s) (loN s + i)) = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD, ← hm,
      bytesAt_getD _ _ (by omega_arith), show off (Sp s) 0 + BitVec.ofNat 64 (loN s + i) = off (off (Sp s) 0) (loN s + i)
      from rfl, off_off, Nat.zero_add]
  have hV0 : view m (Sp s) 0 = (emOf s).getD 0 0 := by
    rw [← hm, bytesAt_getD _ _ (by omega_arith), BitVec.add_zero]; rfl
  have hEl : ((emOf s).drop (loN s)).length = E := by rw [List.length_drop, emOf_length]; omega_arith
  rw [show kk s - loN s - Gs.len - 1 = E - Gs.len - 1 by omega_arith, show kk s = loN s + E by omega_arith,
    res_iff (E := E) hGv hc hEl (by omega_arith) hV (bytesAt_length _ _ _) hHv (sLen_eq s) (by omega_arith), vOut, hn,
    Proof.RsaPss.verify_bytes₂ Gm Gs hGv (bytesAt_length _ _ _) (by rw [bytesAt_length, List.length_cons, hr]; omega_arith)
      hB hEg (by rw [List.length_cons, hr]; omega_arith) hl1 ?_, hx, hV0]
  rw [sLen_eq]; split
  · rename_i h; have := hfit h; simp only [Option.getD_some]; omega_arith
  · simp only [Option.getD_none]; omega_arith

/-! ## The code -/

section
variable {Gs Gm : Spec.Mgf1.Hash} {s : State} (P : PreP Gs.len s)
include P

theorem fail_ok {t : State} (h : Base Sp (vP Gs.len) s t) (hv : vOut Gs Gm s = false) :
    WP isa Impl.RsaPss.PPC64LE.fail t (Done Gs Gm s) :=
  wp_li (by decide) fun t' o e => wp_nil ⟨(h.only P.fits o).sv, fun _ => by rw [e, hv]; rfl⟩

omit P in
theorem expLen_ok {t : State} (h20 : t.gpr .r20 = anyL s) (h19 : t.gpr .r19 = stackArg s 0) :
    WP isa expLen t fun u => Only [.r4] t u ∧ u.gpr .r4 = if anyL s = 0 then stackArg s 0 else 0 := by
  refine WP.ite _ (eval_zero _ _) (fun hz => wp_mov fun u o e => wp_nil ⟨o, ?_⟩)
    (fun hz => wp_li (by decide) fun u o e => wp_nil ⟨o, ?_⟩)
  · rw [ifp (by rw [← h20]; simpa using hz), e, h19]
  · rw [ifn (by rw [← h20]; simpa using hz), e]; rfl

theorem lo_reE {m : Mem} (hf : Frame [kR s, scR s] s.mem m) : lo (reE s m) = lo s := by
  simp only [lo, smear, reE_n0 P hf]

theorem cm_reE {m : Mem} (hf : Frame [kR s, scR s] s.mem m) : cm (reE s m) = cm s := by
  rw [cm, cm, lo_reE P hf]; simp only [smear, reE_n0 P hf]

theorem lay_reE {H : Hash} (hH : HashOK H) (hGl : Gs.len = H.D) {m : Mem} (hf : Frame [kR s, scR s] s.mem m)
    (h0 : s.mem (s.gpr .r3) ≠ 0) (hem : Gs.len + 2 ≤ kk s - loN s) :
    Lay Gs.len (reE s m) (loN s) (kk s - loN s - Gs.len - 1) (cB s) where
  F := reE_fits P hf
  hlo := by rw [lo_reE P hf, lo_eq h0]; rfl
  hdb := by
    show s.gpr .r4 - lo (reE s m) - BitVec.ofNat 64 (Gs.len + 1) = _
    have e : (s.gpr .r4).toNat = kk s := rfl
    rw [lo_reE P hf, lo_eq h0, show (if (s.mem (s.gpr .r3)).toNat = 1 then 1 else 0) = loN s from rfl,
      ← ofNat_toNat (s.gpr .r4), Offset.ofNat_sub_ofNat (by omega_arith), Offset.ofNat_sub_ofNat (by omega_arith),
      show (s.gpr .r4).toNat - loN s - (Gs.len + 1) = kk s - loN s - Gs.len - 1 by omega_arith]
  hc := by rw [cm_reE P hf, cm_eq h0]; rfl
  l1 := by unfold loN; split <;> omega_arith
  d1 := by omega_arith
  hk := by show _ = kk s; omega_arith
  k2 := P.k2
  D0 := by rw [hGl]; exact hH.hD0
  D64 := by rw [hGl]; exact hH.hD64
  dr := by show dR Gs.len s ∈ s.rd; rw [P.hrd]; simp
  dsc := by
    rw [show SC Sp (reE s m) = SC Sp s by simp only [SC, reE_Sp P hf]]; exact P.ds.sub_right (sc_sub P)
  dk := P.kd
  wd := P.wd

theorem Entered.only {t t' : State} {rs : List Reg} (E : Entered Gs.len s t) (o : Only rs t t')
    (hrs : ∀ r ∈ rs, r ∉ .r14 :: fx ++ hiRegs ++ ([.r9, .r24, .r25, .r26, .r27] : List Reg) := by decide) :
    Entered Gs.len s t' := by
  have g : ∀ r ∈ [Reg.r9, .r24, .r25, .r26, .r27], t'.gpr r = t.gpr r := fun r hr =>
    o.gpr r fun h => hrs r h (List.mem_append_right _ hr)
  exact ⟨E.base.only P.fits o fun r h h' => hrs r h (List.mem_append_left _ h'), (g _ (by decide)).trans E.r24,
    (g _ (by decide)).trans E.r25, (g _ (by decide)).trans E.r26, (g _ (by decide)).trans E.r27,
    (g _ (by decide)).trans E.r9⟩

omit P in
theorem Entered.before {t : State} (E : Entered Gs.len s t) : Before Gs.len s t := ⟨E.base, E.r24, E.r25, E.r26, E.r27⟩

omit P in
theorem n0_eq {t : State} (E : Entered Gs.len s t) (hz : (t.gpr .r9 == 0) = true) : s.mem (s.gpr .r3) = 0 := by
  have : n0 s = 0#64 := by rw [← E.r9]; simpa using hz
  exact (setWidth64_eq_zero _).mp this

omit P in
theorem n0_ne {t : State} (E : Entered Gs.len s t) (hz : (t.gpr .r9 == 0) = false) : s.mem (s.gpr .r3) ≠ 0 :=
  fun h => by rw [E.r9, n0, h] at hz; simp at hz

theorem lo_N (h0 : s.mem (s.gpr .r3) ≠ 0) : s.gpr .r4 - lo s = BitVec.ofNat 64 (kk s - loN s) := by
  have hk1 : 64 ≤ kk s := P.k1
  have ek : (s.gpr .r4).toNat = kk s := rfl
  have hl1 : loN s ≤ 1 := by unfold loN; split <;> omega_arith
  rw [lo_eq h0, show (if (s.mem (s.gpr .r3)).toNat = 1 then 1 else 0) = loN s from rfl, ← ofNat_toNat (s.gpr .r4),
    Offset.ofNat_sub_ofNat (by omega_arith)]

/-- `chkEm`: whether `emLen < hLen + 2`. -/
theorem chkEm_ok {H : Hash} (hGl : Gs.len = H.D) (hD64 : Gs.len ≤ 64) {t : State} (E : Entered Gs.len s t)
    (h0 : s.mem (s.gpr .r3) ≠ 0) :
    WP isa (.block (chkEm H)) t fun t' => Entered Gs.len s t' ∧
      (t'.gpr .r3 != 0) = decide (kk s - loN s < Gs.len + 2) := by
  have hk2 : kk s ≤ 1024 := P.k2
  refine wp_sub fun t₁ o₁ e₁ => wp_subi (h := by omega_arith) fun t₂ o₂ e₂ => wp_lsr fun t₃ o₃ e₃ => wp_nil ?_
  have k₃ : Only [.r3] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  refine ⟨E.only P k₃, ?_⟩
  rw [e₃, e₂, e₁, E.base.pk, E.base.plo, lo_N P h0, ← hGl]
  exact ne_zero_ltBit (by omega_arith) (by omega_arith)

/-- `chkSalt`: whether the salt length expected is more than `emLen - hLen - 2`. -/
theorem chkSalt_ok {H : Hash} (hGl : Gs.len = H.D) (hD64 : Gs.len ≤ 64) {t : State} (E : Entered Gs.len s t)
    (h0 : s.mem (s.gpr .r3) ≠ 0) (hem : Gs.len + 2 ≤ kk s - loN s)
    (h4 : t.gpr .r4 = if anyL s = 0 then stackArg s 0 else 0) :
    WP isa (.block (chkSalt H)) t fun t' => Entered Gs.len s t' ∧
      (t'.gpr .r3 != 0) = decide (kk s - loN s - (Gs.len + 2) < (if anyL s = 0 then stackArg s 0 else 0).toNat) := by
  have hk2 : kk s ≤ 1024 := P.k2
  refine wp_sub fun t₅ o₅ e₅ => wp_subi (h := by omega_arith) fun t₆ o₆ e₆ => wp_sub fun t₇ o₇ e₇ =>
    wp_lsr fun t₈ o₈ e₈ => wp_lsr fun t₉ o₉ e₉ => wp_or fun t₁₀ o₁₀ e₁₀ => wp_nil ?_
  have k₁₀ : Only [.r3, .r5] t t₁₀ := (o₅.trans (o₆.trans (o₇.trans (o₈.trans (o₉.trans o₁₀))))).mono
  refine ⟨E.only P k₁₀, ?_⟩
  rw [e₁₀, o₉.get .r3, e₉, e₈, o₈.get .r4, e₇, o₇.get .r4, e₆, o₆.get .r4, e₅, o₅.get .r4, E.base.pk, E.base.plo,
    lo_N P h0, h4, ← hGl, Offset.ofNat_sub_ofNat hem, BitVec.or_comm]
  have := msgBit (x := kk s - loN s - (Gs.len + 2)) (y := (if anyL s = 0 then stackArg s 0 else 0).toNat)
    (by omega_arith) (BitVec.isLt _)
  rwa [ofNat_toNat] at this

section
variable {H : Hash} (hH : HashOK H) (hGh : ∀ x, Gs.hash x = hH.SH.H.hash x) (hGl : Gs.len = H.D)
  (hHv : Proof.Mgf1.Valid Gs) {G : Hash} (hG : HashOK G) {g : Fns} (Tg : TabS G g gArg Sp s (stackArg s 7))
  (hGmh : ∀ x, Gm.hash x = hG.SH.H.hash x) (hGml : Gm.len = G.D) (hGmv : Proof.Mgf1.Valid Gm)
  {cn dn : String} {cc dc : Prog isa} {f : MdFns} (T : MdTabS H cn cc dn dc f hArg Sp s (stackArg s 6))
  {P' : Params} {md : Md P'.B P'.N P'.L} (ok : CtOK P' md cc dc) {iv : md.HV} (hl : md.Link hH.SH iv Gs.len)
  (hN : H.N = P'.N) (hB : H.B = P'.B)
include hH hGh hGl hHv hG Tg hGmh hGml hGmv T ok hl hN hB

theorem main_done {t : State} (B : Before Gs.len s t) (sy : t.syms = s.syms) (h0 : s.mem (s.gpr .r3) ≠ 0)
    (hem : Gs.len + 2 ≤ kk s - loN s) (hfit : anyL s = 0 → (stackArg s 0).toNat + 1 ≤ kk s - loN s - Gs.len - 1) :
    WP isa (verifyMain H P' f g) t (Done Gs Gm s) := by
  refine WP.seq (WP.mono_syms (pubArgs_ok P B) fun t₁ a₁ y₁ => WP.seq (WP.mono_syms (call_ok P a₁) fun t₂ c₂ y₂ => ?_))
  have L := lay_reE P hH hGl c₂.mem h0 hem
  have hS := reE_Sp P c₂.mem
  have hmh : mh Gs.len (reE s t₂.mem) = mh Gs.len s :=
    VG.Proof.RsaOaep.PPC64LE.bytes_entry c₂.mem P.kd P.ds.symm (by have := hH.hD64; omega_arith)
  have hany : anyL (reE s t₂.mem) = anyL s := by unfold anyL; rw [reE_args P c₂.mem 1 (by decide)]
  have hSC : SC Sp (reE s t₂.mem) = SC Sp s := by simp only [SC, hS]
  have hsl0 : stackArg (reE s t₂.mem) 0 = stackArg s 0 := reE_args P c₂.mem 0 (by decide)
  have hA : ∀ j < 8, ∀ r ∈ [kR s, scR s], Region.Disjoint ⟨stackArgAddr s j, 8⟩ r := fun j hj r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (P.ka.sub_right (in_aR_sub hj)).symm
    · exact (P.sa.sub_right (in_aR_sub hj)).symm
  have Tg' : TabS G g gArg Sp (reE s t₂.mem) (stackArg s 7) := Tg.transfer rfl rfl rfl hSC c₂.mem (hA 7 (by decide))
    fun k hk r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (P.ktg.sub_right (tab_sub (n := 11) (by omega_using [hk]))).symm
      · exact (P.stg.sub_right (tab_sub (n := 11) (by omega_using [hk]))).symm
  have T' : MdTabS H cn cc dn dc f hArg Sp (reE s t₂.mem) (stackArg s 6) := T.transfer rfl rfl rfl hSC c₂.mem
    (hA 6 (by decide)) fun k hk r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (P.kth.sub_right (tab_sub (n := 11) hk)).symm
      · exact (P.sth.sub_right (tab_sub (n := 11) hk)).symm
  refine WP.mono (post_ok L hH hGl.symm hGh hG Tg' hGmh hGml hGmv T' ok hl hN hB c₂.base (y₂.trans (y₁.trans sy))
    (by rw [hany, hsl0]; exact hfit)) fun t' ⟨b', r'⟩ =>
    ⟨⟨b'.sv.sp, b'.sv.wr, b'.sv.hi, b'.sv.sv, b'.sv.ls⟩, fun hc => ?_⟩
  rw [r', hS, hmh, hany, hsl0, reE_gpr]
  have e := res_vOut hGmv hHv P h0 (c₂.em hc) hem hfit
  by_cases hv : vOut Gs Gm s = true
  · rw [ifp (e.mpr hv), ifp hv]; rfl
  · rw [ifn (fun h => hv (e.mp h)), ifn hv]; rfl

theorem checks_done {t : State} (E : Entered Gs.len s t) (sy : t.syms = s.syms) :
    WP isa (checks H P' f g) t (Done Gs Gm s) := by
  have hk1 : 64 ≤ kk s := P.k1
  have hD64 : Gs.len ≤ 64 := hGl ▸ hH.hD64
  refine WP.ite _ (eval_zero _ _) (fun hz => fail_ok P E.base (zero_false Gs Gm (by omega_arith) (n0_eq E hz)))
    (fun hz => ?_)
  have h0 := n0_ne E hz
  -- `emLen < hLen + 2`.
  refine WP.seq (WP.mono_syms (chkEm_ok P hGl hD64 E h0) fun t₃ ⟨E₃, r3⟩ y₃ => ?_)
  refine WP.ite _ (eval_nonzero _ _) (fun hc => fail_ok P E₃.base (short_false Gs Gm (by omega_arith) h0 ?_))
    (fun hc => ?_)
  · rw [r3] at hc; simp at hc; omega_arith
  have hem : Gs.len + 2 ≤ kk s - loN s := by rw [r3] at hc; simp at hc; omega_arith
  -- The salt length expected.
  refine WP.seq (WP.mono_syms (expLen_ok E₃.base.pany E₃.base.psl) fun t₄ ⟨o₄, e₄⟩ y₄ => ?_)
  refine WP.seq (WP.mono_syms (chkSalt_ok P hGl hD64 (E₃.only P o₄) h0 hem e₄) fun t₁₀ ⟨E₁₀, r3'⟩ y₁₀ => ?_)
  refine WP.ite _ (eval_nonzero _ _) (fun hc => fail_ok P E₁₀.base (short_false Gs Gm (by omega_arith) h0 ?_))
    (fun hc => ?_)
  · rw [r3'] at hc
    rw [sLen_eq]
    by_cases ha : anyL s = 0
    · rw [ifp ha] at hc ⊢; simp only [Option.getD_some]; simp at hc; omega_arith
    · rw [ifn ha] at hc; simp at hc
  have hfit : anyL s = 0 → (stackArg s 0).toNat + 1 ≤ kk s - loN s - Gs.len - 1 := fun ha => by
    rw [r3', ifp ha] at hc; simp at hc; omega_arith
  exact main_done P hH hGh hGl hHv hG Tg hGmh hGml hGmv T ok hl hN hB E₁₀.before (y₁₀.trans (y₄.trans (y₃.trans sy)))
    h0 hem hfit

/-- The frame's body for `H`'s sizes, from the state after the frame's push
and the choice of the code, which writes only `r11` and `r12`. -/
theorem body_ok {u : State} (hu : Only [.r11, .r12] (allocated frameBytes s) u) (sy : u.syms = s.syms) :
    WP isa (body H P' f g) u fun w => Post Gs Gm s (freed frameBytes w) := by
  refine WP.seq (WP.mono_syms (entry_ok P hGl.symm (hGl ▸ hH.hD64) hu) fun t E y => WP.seq (WP.mono
    (checks_done P hH hGh hGl hHv hG Tg hGmh hGml hGmv T ok hl hN hB E (y.trans sy)) fun t' ⟨sv, res⟩ =>
      WP.mono (restore_ok sv) fun w ⟨habi, h3, _⟩ => ⟨habi, fun hc => ?_⟩))
  rw [freed_gpr, h3]
  exact res hc

end

end


/-- The frame's body depends on the hash function only through its digest
length. -/
theorem body_D {H H' : Hash} (hD : H.D = H'.D) (P : Params) (f : MdFns) (g : Fns) :
    body H P f g = body H' P f g := by
  simp only [body, checks, verifyMain, finish, prologue, chkEm, chkSalt, dbArgs, mPrefix, copySalt, copyDb, shiftPass,
    shift, hashFixed, ctHash, ctLens, cmpH, hD]

section
variable {Gs Gm : Spec.Mgf1.Hash} {s : State} (P : PreP Gs.len s)
  {H : Hash} (hH : HashOK H) (hGh : ∀ x, Gs.hash x = hH.SH.H.hash x) (hGl : Gs.len = H.D)
  (hHv : Proof.Mgf1.Valid Gs) {G : Hash} (hG : HashOK G) {g : Fns} (Tg : TabS G g gArg Sp s (stackArg s 7))
  (hGmh : ∀ x, Gm.hash x = hG.SH.H.hash x) (hGml : Gm.len = G.D) (hGmv : Proof.Mgf1.Valid Gm)
  {cn dn : String} {cc dc : Prog isa} {f : MdFns} (T : MdTabS H cn cc dn dc f hArg Sp s (stackArg s 6))
  {P' : Params} {md : Md P'.B P'.N P'.L} (ok : CtOK P' md cc dc) {iv : md.HV} (hl : md.Link hH.SH iv Gs.len)
  (hN : H.N = P'.N) (hB : H.B = P'.B)
include P hH hGh hGl hHv hG Tg hGmh hGml hGmv T ok hl hN hB

/-- `vg_rsa_pss_verify_precomputed`, for a hash function's table whose index
`i` is one of `idxs`, whose sizes and parameters `shapeOf i` gives. -/
theorem verify_ok {i : Nat} (hidx : s.mem.readW (stackArg s 6 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 i)
    (hi : i ∈ idxs) (hD : (shapeOf i).1.D = H.D) (hP : (shapeOf i).2 = P') :
    WP isa (verifyPrecomputed f g) s (Post Gs Gm s) := by
  have hi8 : i < 8 := by simp only [idxs, List.mem_cons, List.not_mem_nil, or_false] at hi; omega_using [hi]
  refine WP.allocOf (by decide) (by have := P.sp1; unfold frameBytes; omega_arith) ?_
  show WP isa (.seq (.block (tword .r11 hArg 5 ++ [])) _) _ _
  refine WP.seq (WP.of_syms (twordA_ok (j := 6) (k := 5) (p := stackArg s 6) (by decide) (by decide)
    ⟨aR s, by rw [P.hrd]; simp, in_aR (by decide)⟩ (P.ka.sub_right (in_aR_sub (by decide))).symm rfl
    ⟨tHR s, by rw [P.hrd]; simp, Offset.contains_base _ (by decide) (by decide)⟩
    (P.kth.sub_right (tab_sub (n := 11) (show 5 < 11 by decide))).symm fun u o e => wp_nil fun y => ?_))
  rw [show 8 * 5 = 40 from rfl, hidx] at e
  refine byIdx_ok (D := i) (by omega_using [hi8])
    (F := fun u' => Only [.r11, .r12] (allocated frameBytes s) u' ∧ u'.syms = s.syms ∧
      u'.gpr .r11 = BitVec.ofNat 64 i)
    (fun _ h => h.2.2) (fun u₁ u₂ ⟨o₁, y₁, e₁⟩ o y => ⟨(o₁.trans o).mono, y.trans y₁, by rw [o.get .r11]; exact e₁⟩)
    (fun u' ⟨o', y', _⟩ => ?_) hi (fun x hx => (idxs_certs x hx).1) u ⟨o.mono, y.trans rfl, e⟩
  rw [body_D hD, hP]
  exact body_ok P hH hGh hGl hHv hG Tg hGmh hGml hGmv T ok hl hN hB o' y'

end

end VG.Proof.RsaPss.PPC64LE

end

end

/-!
# RSASSA-PSS verification on PPC64LE: the public data

Untrusted: everything here is checked by Lean. The shared contract's public
data (`PubP`, `pubP_of`): the stack pointer, the pointers and lengths, the
salt-length mode, the modulus, `e` and `pre`. An entry state with the
anchor's public data has its modulus' first byte (`PubP.byte`), so its
`lo`, `c` and `dbLen`, and agrees with it on what `Base` fixes (`PubP.agree`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE
open VG.Proof.RsaOaep.PPC64LE (Base Fits fx Agree Ok)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

/-- The public data of an entry state `s` is the anchor `a`'s. -/
structure PubP (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10], s.gpr r = a.gpr r
  a1 : (stackArg s 1).setWidth 32 = (stackArg a 1).setWidth 32
  args : ∀ i, i < 8 → i ≠ 1 → stackArg s i = stackArg a i
  n : Spec.Rsa.bytesAt s.mem (s.gpr .r3) (kk s) = Spec.Rsa.bytesAt a.mem (a.gpr .r3) (kk a)
  e : Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .r5) (a.gpr .r6).toNat
  w : Spec.Rsa.wordsAt s.mem (stackArg s 4) (stackArg s 5).toNat =
    Spec.Rsa.wordsAt a.mem (stackArg a 4) (stackArg a 5).toNat

theorem pubP_refl (s : State) : PubP s s := ⟨rfl, fun _ _ => rfl, rfl, fun _ _ _ => rfl, rfl, rfl, rfl⟩

theorem leak_eq3 {a b c d : List Byte} {w w' : List (BitVec 64)} (ha : a.length = c.length)
    (hb : b.length = d.length)
    (h : (a ++ b).map (·.toNat) ++ w.map (·.toNat) = (c ++ d).map (·.toNat) ++ w'.map (·.toNat)) :
    a = c ∧ b = d ∧ w = w' := by
  obtain ⟨h₁, h₂⟩ := List.append_inj h (by simp [ha, hb])
  have hi : a ++ b = c ++ d := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h₁
  exact ⟨(List.append_inj hi ha).1, (List.append_inj hi ha).2,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h₂⟩

/-- The contract's public data: `PubP`, the tables' functions at the same
addresses, and the same tables held. -/
theorem pubT_of {hs gs : List FnTable} {s₁ s₂ : State} (h : (verSpec hs gs).pub s₁ s₂) :
    PubP s₁ s₂ ∧
      (∀ f ∈ (hs.map (fun T : FnTable => T.fns)).flatten ++ (gs.map (fun T : FnTable => T.fns)).flatten,
        s₁.syms f = s₂.syms f) ∧
      (∀ T ∈ hs, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 6) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 6) (FnTable.words isa s₂ T))) ∧
      ∀ T ∈ gs, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 7) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 7) (FnTable.words isa s₂ T)) := by
  have e : (304 : Nat) = 303 + 1 := rfl
  unfold verSpec at h
  rw [e] at h
  sig_pub [Spec.RsaPss.verifyPrecomputedMdTableContract, Spec.RsaPss.verifyPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs,
    stackArgs_eight, List.append_eq, List.range, List.range.loop] at h
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at h
  obtain ⟨hsp, hsy, htab, htab', hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3, a4, a5, a6, a7⟩ := h
  obtain ⟨hn, he, hw⟩ := leak_eq3 (by simp [bytesAt_length, h4]) (by simp [bytesAt_length, h6]) hl
  refine ⟨⟨hsp.symm, fun r hr => ?_, a1.symm, fun i hi h1 => ?_, hn.symm, he.symm, hw.symm⟩, hsy,
    fun T hT => htab _ _ rfl rfl T hT, fun T hT => htab' _ _ rfl rfl T hT⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h3.symm, h4.symm, h5.symm, h6.symm, h7.symm, h8.symm, h9.symm, h10.symm]
  · rcases (by omega_using [hi, h1] : i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0.symm, a2.symm, a3.symm, a4.symm, a5.symm, a6.symm, a7.symm]

section
variable {a s : State} (p : PubP a s)
include p

theorem PubP.byte (hk : 1 ≤ kk s) : s.mem (s.gpr .r3) = a.mem (a.gpr .r3) := by
  have e4 : kk s = kk a := by rw [kk, kk, p.g .r4 (by decide)]
  have := congrArg (·.getD 0 0) p.n
  rwa [bytesAt_getD _ _ hk, bytesAt_getD _ _ (by omega), BitVec.add_zero, BitVec.add_zero] at this

theorem PubP.pAny : anyL s = anyL a := by unfold anyL; rw [p.a1]

theorem PubP.pN0 (hk : 1 ≤ kk s) : n0 s = n0 a := by rw [n0, n0, p.byte hk]

theorem PubP.pLo (hk : 1 ≤ kk s) : lo s = lo a := by simp only [lo, smear, p.pN0 hk]

theorem PubP.pCm (hk : 1 ≤ kk s) : cm s = cm a := by rw [cm, cm, p.pLo hk]; simp only [smear, p.pN0 hk]

theorem PubP.pLoN (hk : 1 ≤ kk s) : loN s = loN a := by rw [loN, loN, p.byte hk]

theorem PubP.pKk : kk s = kk a := by rw [kk, kk, p.g .r4 (by decide)]

theorem PubP.pSp : Sp s = Sp a := p.args 2 (by decide) (by decide)

theorem PubP.agree {D : Nat} (hk : 1 ≤ kk s) : Agree Sp (vP D) a s := ⟨p.sp, p.pSp, fun r hr => by
  simp only [fx, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [vP]
  · exact p.g _ (by decide)
  · exact p.g _ (by decide)
  · exact p.pLo hk
  · exact p.pCm hk
  · exact p.args 0 (by decide) (by decide)
  · exact p.pAny
  · rw [dbLen, dbLen, p.pLo hk, p.g .r4 (by decide)]
  · exact p.args 4 (by decide) (by decide)
  · exact p.args 5 (by decide) (by decide)⟩

end

/-- `PubP`, for a nonempty modulus. -/
def PubK (a s : State) : Prop := PubP a s ∧ 1 ≤ kk s

end VG.Proof.RsaPss.PPC64LE
