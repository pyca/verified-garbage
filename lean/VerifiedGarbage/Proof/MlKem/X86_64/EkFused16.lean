module

public import VerifiedGarbage.Proof.MlKem.X86_64.EkFrag16
meta import VerifiedGarbage.Proof.MlKem.X86_64.EkFrag16
meta import VerifiedGarbage.Proof.MlKem.X86_64.EkFrag
public import VerifiedGarbage.Proof.MlKem.X86_64.EkScalar
public import VerifiedGarbage.Proof.MlKem.X86_64.Enc16
meta import VerifiedGarbage.Proof.MlKem.X86_64.EkScalar
import VerifiedGarbage.Proof.MlKem.X86_64.Zero
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
import VerifiedGarbage.Proof.MlKem.X86_64.KgTop
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on x86-64: encapsulation hashing the key in the matrix's fragments, with 16-bit polynomials

As `EkFused.lean`, for `kemEncaps16`: the prologue; `ρ` to `SB` and the
sponge's state zeroed; the fragments (`frags16_ok`, `EkFrag16.lean`); `H(ek)`
to `H`; the remaining entries of `Â` (`MI16`); `m` and `G(m ‖ H(ek))`, which
keep the matrix (`hashesF16_ok`); and, if every `SampleNTT` succeeded, the
rest of K-PKE.Encrypt with 16-bit polynomials (`Enc16.rest_ok`), which
writes the ciphertext straight to `ct`, and `K` to `key`
(`kemEncaps16_correct`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt)

namespace EkF16

open VG.Proof.MlKem.X86_64.Encaps (ecR ecW ecB ecB_bases ecChk eckChk EcWfB hW₃)
open VG.Proof.MlKem.X86_64.Ek (EK ekE ekMs ekG ProOut)
open VG.Proof.MlKem.X86_64.EkF (mov0_ok)
open VG.Impl.MlKem.X86_64.Encaps (nb)
open VG.Impl.MlKem.X86_64.Encaps16 (oHS oHB hzero matH)
open VG.Impl.MlKem.X86_64.Top16 (aP)

variable (K : Kem16)

/-- What the fused encapsulation needs of the layout, besides the fragments'. -/
structure Ek16HWf : Prop extends Ek16FWf K where
  /-- The entries after the fragments are sampled four at a time. -/
  eS : 3 * nb K.L % 4 = 0 ∨ 4 * (K.L.k * K.L.k / 4) ≤ 3 * nb K.L
  noS : K.L.k * K.L.k ≤ 4 * (K.L.k * K.L.k / 4) ∨ K.L.k * K.L.k ≤ 3 * nb K.L
  -- `H(ek)` to `H`
  hC : (copyChk (ecB K.L) (ecW K.L) (sc oH) (sc (oHS K)) 32 && fkeep K [(sc oH, 32)] (3 * nb K.L)) = true
  -- the remaining entries
  qC : ∀ q < K.L.k * K.L.k / 4, 3 * nb K.L ≤ 4 * q →
    (quad16Chk (ecB K.L) (ecW K.L) (K.oA + 512 * (4 * q)) K.oW &&
      fkeep K (quad16W (K.oA + 512 * (4 * q)) K.oW) (4 * q) &&
      keepB (ecB K.L) (quad16W (K.oA + 512 * (4 * q)) K.oW) (sc oH) 32) = true
  -- `m` and `G(m ‖ H(ek))` keep the matrix
  -- K-PKE.Encrypt, and the key
  enc : Enc16.EncChks K (ecB K.L) (ecW K.L) (eckChk K.L) (.r14, 0)
  tl : Enc16.tailChk K (ecB K.L) (ecW K.L) (eckChk K.L) (.r14, 0) (.r13, 0) = true
  o₁T : keepB (ecB K.L) [((.r12, 0), 32)] (.r13, 0) K.L.ctLen = true
  gK : (keepB (ecB K.L) ([(sc oM, 32)] ++ hW₃) (sc oSB) 32 &&
    (List.range (K.L.k * K.L.k)).all (fun e => keepB (ecB K.L) ([(sc oM, 32)] ++ hW₃) (aP K e) 512)) = true

variable {K}

/-- After the fragments and `H(ek)`, with the first `e` entries of `Â`. -/
structure MI16 (K : Kem16) (σ : State) (e : Nat) (s : State) : Prop where
  ec : EK K.L σ s
  sb : bytesAt s.mem (pa s (sc oSB)) 32 = Enc.rhoE K.L (ekE K.L σ)
  mat : MatB16 K.L.k K.oA (Enc.rhoE K.L (ekE K.L σ)) e s
  h : bytesAt s.mem (pa s (sc oH)) 32 = H (ekE K.L σ)

/-- The sponge's state zeroed. -/
theorem hzero16_ok {rbs wbs : List (Reg × Nat)} {s : State} (Lx : Lay rbs wbs s)
    (hin : inB wbs (sc (oHS K)) 200 = true) :
    WP isa (.block (hzero K)) s fun s' => PPost s s' [(sc (oHS K), 200)] ∧
      stateAt s'.mem (pa s (sc (oHS K))) = Spec.Sha3.zero := by
  have hc := Lx.cW hin
  unfold hzero
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (mov0_ok s) fun s₁ ⟨h0, hm1, k1⟩ => ?_
  have e1 : s₁.gpr .rbx = s.gpr .rbx := k1.1 .rbx (by decide)
  refine WP.mono (zeroSt_ok .rbx (oHS K) s₁ h0 fun j hj => ?_) fun s₂ ⟨hz, f2, k2⟩ => ?_
  · rw [k1.2.2, e1]
    exact hc _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩
  · rw [e1] at hz f2
    refine ⟨post_of_keep (k1.trans k2) (by decide) ?_, hz⟩
    show Frame [⟨pa s (sc (oHS K)), 200⟩] s.mem s₂.mem
    rw [← hm1]; exact f2

theorem quadM16_ok {n : String} {c : Prog isa} (v : S16Ok c) (F : Ek16HWf K) {σ : State} (hp : (encK K.L).pre σ) {q : Nat}
    (hq : q < K.L.k * K.L.k / 4) (h3 : 3 * nb K.L ≤ 4 * q) {s : State} (h : MI16 K σ (4 * q) s) :
    WP isa (quad16 (n, c) K.L.k (4 * q) (sc (K.oA + 512 * (4 * q))) (sc K.oW)) s (MI16 K σ (4 * q + 4)) := by
  have W := F.toEcWfB
  have hc := F.qC q hq h3
  simp only [fkeep, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨hqc, ⟨hE, hS⟩, hA⟩, hH⟩ := hc
  have L₀ := h.ec.lay W hp
  have h16 : K.L.k * K.L.k ≤ 16 := Nat.mul_le_mul W.k.2 W.k.2
  refine WP.mono (quad16_ok v L₀ (ecB_bases K.L) (by omega) hqc) fun s' ⟨hP, h15, hres⟩ =>
    ⟨h.ec.step W hp hP hE, by rw [L₀.keepBytes hP hS]; exact h.sb, MatB16.four h.mat h.sb L₀ hP hA h15 hres,
      by rw [L₀.keepBytes hP hH]; exact h.h⟩

/-- After `ρ` to `SB`. -/
structure RI16 (K : Kem16) (σ s : State) : Prop where
  ec : EK K.L σ s
  sb : bytesAt s.mem (pa s (sc oSB)) 32 = Enc.rhoE K.L (ekE K.L σ)
  r15 : s.gpr .r15 = 1

theorem rho16_ok (F : Ek16HWf K) {σ : State} (hp : (encK K.L).pre σ) {s : State} (h : ProOut K.L σ s) :
    WP isa (copy (sc oSB) (.r14, 384 * K.L.k) 32) s (RI16 K σ) := by
  have W := F.toEcWfB
  have L₀ := h.ec.lay W hp
  have hrC := F.rC
  simp only [Bool.and_eq_true] at hrC
  refine WP.mono (copy_okL L₀ (show Reg.r14 ≠ .rdi by decide) hrC.1) fun s₁ ⟨hP₁, hb₁⟩ =>
    ⟨h.ec.step W hp hP₁.b hrC.2, ?_, by rw [hP₁.cs .r15 (by decide), h.r15]⟩
  rw [hP₁.pa rbx_cs, hb₁, ← h.ec.ek]
  show _ = ((bytesAt s.mem (pa s (.r14, 0)) (384 * K.L.k + 32)).drop (384 * K.L.k)).take 32
  rw [bytesAt_slice _ _ (Nat.le_refl _), pa, pa, off_add, Nat.zero_add]

theorem hz16_ok (F : Ek16HWf K) {σ : State} (hp : (encK K.L).pre σ) {s : State} (h : RI16 K σ s) :
    WP isa (.block (hzero K)) s (FI16 K σ 0) := by
  have W := F.toEcWfB
  have L₁ := h.ec.lay W hp
  have hzC := F.zC
  simp only [fkeep, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hzC
  obtain ⟨hzin, ⟨hzE, hzS⟩, -⟩ := hzC
  exact WP.mono (hzero16_ok L₁ hzin) fun s₂ ⟨hP₂, hz⟩ => ⟨h.ec.step W hp hP₂.b hzE,
    by rw [L₁.keepBytes hP₂.b hzS]; exact h.sb, MatB16.zero _ _ _ (by rw [hP₂.cs .r15 (by decide), h.r15]),
    by rw [hP₂.pa rbx_cs, hz, HSponge.hstate_zero]⟩

theorem hcopy16_ok (F : Ek16HWf K) {σ : State} (hp : (encK K.L).pre σ) {s : State} (h : FI16 K σ (nb K.L) s) :
    WP isa (copy (sc oH) (sc (oHS K)) 32) s (MI16 K σ (3 * nb K.L)) := by
  have W := F.toEcWfB
  have hhC := F.hC
  simp only [fkeep, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hhC
  obtain ⟨hcp, ⟨hE, hS⟩, hA⟩ := hhC
  have L₃ := h.ec.lay W hp
  have hn := F.nbE
  have hlen : (ekE K.L σ).length = K.L.ekLen := bytesAt_length _ _ _
  exact WP.mono (copy_okL L₃ (show Reg.rbx ≠ .rdi by decide) hcp) fun s₄ ⟨hP₄, hb₄⟩ =>
    ⟨h.ec.step W hp hP₄.b hE, by rw [L₃.keepBytes hP₄.b hS]; exact h.sb,
      ⟨by rw [hP₄.cs .r15 (by decide)]; exact h.mat.r15,
        fun e he f hf => L₃.keepPoly16 hP₄.b (hA e he) (h.mat.mat e he f hf)⟩,
      by rw [hP₄.pa rbx_cs, hb₄, HSponge.bytesAt_stateAt, h.hs, ← HSponge.H_of_hstate (by rw [hlen]; omega)]⟩

theorem entsM16_ok {n : String} {c : Prog isa} (v : S16Ok c) (F : Ek16HWf K) {σ : State} (hp : (encK K.L).pre σ) {s : State}
    (h : MI16 K σ (3 * nb K.L) s) :
    WP isa (ents16 (n, c) K.L.k K.oA (sc K.oW) (3 * nb K.L) (K.L.k * K.L.k - 3 * nb K.L)) s (MI16 K σ (K.L.k * K.L.k)) := by
  have := ents16_ok (n, c) K.L.k K.oA (sc K.oW) (I := fun e s => 3 * nb K.L ≤ e ∧ MI16 K σ e s)
    (fun e he he' _ hs => absurd F.noS (by omega))
    (fun q hq _ hs => WP.mono (quadM16_ok v F hp hq hs.1 hs.2) fun _ h => ⟨by omega, h⟩)
    (K.L.k * K.L.k - 3 * nb K.L) (3 * nb K.L) (by have := F.nbK; omega) F.eS s ⟨Nat.le_refl _, h⟩
  rw [Nat.add_sub_cancel' F.nbK.2] at this
  exact WP.mono this fun _ h => h.2

/-- `ρ` to `SB`, the fragments, `H(ek)` to `H`, and the remaining entries of `Â`. -/
theorem matH16_ok {n : String} {c : Prog isa} (v : S16Ok c) (F : Ek16HWf K) {b : Prog isa} (hb : BatchHOk16 b)
    {σ : State} (hp : (encK K.L).pre σ) {s : State} (h : ProOut K.L σ s) :
    WP isa (matH K (n, c) b) s (MI16 K σ (K.L.k * K.L.k)) := by
  unfold matH
  exact WP.seq (WP.mono (rho16_ok F hp h) fun _ h₁ => WP.seq (WP.mono (hz16_ok F hp h₁) fun _ h₂ =>
    WP.seq (WP.mono (frags16_ok F.toEk16FWf hb hp h₂) fun _ h₃ => WP.seq (WP.mono (hcopy16_ok F hp h₃) fun _ h₄ =>
      entsM16_ok v F hp h₄))))

/-- `m` to `M` and `G(m ‖ H(ek))`, keeping the matrix. -/
theorem hashesF16_ok (F : Ek16HWf K) {σ : State} (hp : (encK K.L).pre σ) {s : State}
    (h : MI16 K σ (K.L.k * K.L.k) s) :
    WP isa EncapsH.hashes s
      (Enc16.EB16 K (Ek.ekC F.toEcWfB σ) (.r14, 0) (ekE K.L σ) (ekMs σ) (ekG K.L σ).2 (K.L.k * K.L.k)) := by
  have W := F.toEcWfB
  have L₀ := h.ec.lay W hp
  have hg := F.gK
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hg
  refine WP.mono (Ek.hashes_okP W hp h.ec h.h) fun s' ⟨hP, h15, hi⟩ =>
    ⟨hi, by rw [L₀.keepBytes hP hg.1]; exact h.sb, ⟨by rw [h15]; exact h.mat.r15, fun e he f hf => ?_⟩⟩
  have k := hg.2 e he
  have m := h.mat.mat e he f hf
  exact L₀.keepPoly16 hP k m

/-- The end of K-PKE.Encrypt, its ciphertext at `ct`. -/
abbrev EncO16 (F : Ek16HWf K) (σ s : State) : Prop :=
  Enc16.EOut16 K (Ek.ekC F.toEcWfB σ) (.r13, 0) (ekE K.L σ) (ekMs σ) (ekG K.L σ).2 s

/-- The rest of K-PKE.Encrypt, if every `SampleNTT` succeeded. -/
theorem ifRest16_ok (hK : KpkeOk K.L) (v : Sample4Impl) (F : Ek16HWf K) {σ s : State}
    (h : Enc16.EB16 K (Ek.ekC F.toEcWfB σ) (.r14, 0) (ekE K.L σ) (ekMs σ) (ekG K.L σ).2 (K.L.k * K.L.k) s) :
    WP isa (ifOk (Top16.encRest K v.callee (.r14, 0) (.r13, 0))) s (EncO16 F σ) := by
  refine ifOk_ok (fun s₁ hP hne => Enc16.rest_ok hK v (show Reg.r14 ∉ argRegs by decide) (by decide) F.k.2 F.enc F.tl
    (Enc16.ER0.start (h.flag hP F.enc) (KeyGen.r15_ne h.m.r15 hne))) fun s₁ hP he => ?_
  have h₁ := h.flag hP F.enc
  exact ⟨h₁.i.out, h₁.m.r15, fun ho => absurd ho (KeyGen.r15_eq h.m.r15 he)⟩

/-- `K` to `key`. -/
theorem out16_ok (F : Ek16HWf K) {σ : State} {s : State} (h : EncO16 F σ s) :
    WP isa (copy (.r12, 0) (sc oG) 32) s (Ek.EKEnd K.L σ) := by
  have hp := h.out.1
  have L₀ := h.out.2.ec.lay F.toEcWfB hp
  refine WP.mono (copy_okL L₀ (dst := (.r12, 0)) (src := sc oG) (n := 32) (by decide) F.o₁) fun s₁ ⟨hP₁, hb₁⟩ => ?_
  refine ⟨h.out.2.ec.step F.toEcWfB hp hP₁.b F.o₁K, by rw [hP₁.cs .r15 (by decide)]; exact h.r15, ?_, fun ho => ?_⟩
  · rw [hP₁.pa (by decide), hb₁]; exact h.out.2.k
  · rw [L₀.keepBytes hP₁.b F.o₁T]; exact h.ct ho

end EkF16

open EkF16 Ek in
theorem kemEncaps16_correct {K : Kem16} (hK : KpkeOk K.L) (v : Sample4Impl) (F : Ek16HWf K) {n : String}
    {c : Prog isa} (hs : v.callee.s16 = some (n, c)) {b : Prog isa} (hb : v.callee.batchH16 = some b)
    (hctl : ctlOk (kemEncaps16 K v.callee (n, c) b) = true) (σ : State) (hp : (encK K.L).pre σ) :
    ∃ t s', Exec isa (kemEncaps16 K v.callee (n, c) b) σ t s' ∧ abiPreserved σ s' ∧ (encK K.L).post σ s' := by
  have hB := v.batchH16 b hb
  have hS := v.s16 n c hs
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (pro_ok F.toEcWfB hp) fun s₁ h₁ =>
    WP.seq (WP.mono (matH16_ok hS F hB hp h₁) fun s₂ h₂ =>
      WP.seq (WP.mono (hashesF16_ok F hp h₂) fun s₃ h₃ =>
        WP.seq (WP.mono (ifRest16_ok hK v F h₃) fun s₄ h₄ =>
          WP.seq (WP.mono (out16_ok F h₄) fun s₅ h₅ =>
            WP.mono (topEpi_ok h₅.ec.top (h₅.hin F.toEcWfB hp)) fun s₆ ⟨hr, hg, hm⟩ =>
              (⟨hg, post_of F.toEcWfB h₅ hr hm⟩ : gprPreserved σ s₆ ∧ (encK K.L).post σ s₆))))))
  exact ⟨t, s', he, abiPreserved_of_ctl hctl he hF.1, hF.2⟩

end VG.Proof.MlKem.X86_64
