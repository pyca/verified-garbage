module

public import VerifiedGarbage.Proof.MlKem.X86_64.EkFrag
meta import VerifiedGarbage.Proof.MlKem.X86_64.EkFrag
import VerifiedGarbage.Proof.MlKem.X86_64.Zero
import all Init.Data.Nat.Bitwise.Basic
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
meta import Mathlib.Tactic.Conv
meta import VerifiedGarbage.Proof.MlKem.X86_64.YLanes

/-!
# ML-KEM on x86-64: encapsulation hashing the key in the matrix's fragments

`kemEncaps L v.callee` for an implementation `v` with a fragment `b`
(`v.callee.batchH = some b`): the prologue; `ρ` to `SB` and the sponge's
state zeroed (`FI` before the first fragment); the fragments (`frags_ok`,
`EkFrag.lean`); `H(ek)`, the first 32 bytes of the sponge's state, to `H`;
the remaining entries of `Â` (`MI`); `m` and `G(m ‖ H(ek))`, which keep the
matrix (`hashesF_ok`); and `kemEncapsH`'s rest of `K-PKE.Encrypt` and its
outputs, if every `SampleNTT` succeeded (`kemEncapsF_correct`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt)

namespace EkF

open VG.Proof.MlKem.X86_64.Encaps (ecR ecW ecB ecB_bases ecChk EcWf hW₃)
open VG.Proof.MlKem.X86_64.Ek (EK ekE ekMs ekG ProOut)
open VG.Impl.MlKem.X86_64.Encaps (oHS oHB nb hzero matH)

variable (L : Kem)

/-- What the fused encapsulation needs of the layout, besides the fragments'. -/
structure EkHWf : Prop extends EkFWf L where
  /-- The entries after the fragments are sampled four at a time. -/
  eS : 3 * nb L % 4 = 0 ∨ 4 * (L.k * L.k / 4) ≤ 3 * nb L
  noS : L.k * L.k ≤ 4 * (L.k * L.k / 4) ∨ L.k * L.k ≤ 3 * nb L
  -- `H(ek)` to `H`
  hC : (copyChk (ecB L) (ecW L) (sc oH) (sc (oHS L)) 32 && fkeep L [(sc oH, 32)] (3 * nb L)) = true
  -- the remaining entries
  qC : ∀ q < L.k * L.k / 4, 3 * nb L ≤ 4 * q →
    (quadChk (ecB L) (ecW L) (oP (L.pA + 4 * q)) (oP L.pW) &&
      fkeep L (quadW (oP (L.pA + 4 * q)) (oP L.pW)) (4 * q) &&
      keepB (ecB L) (quadW (oP (L.pA + 4 * q)) (oP L.pW)) (sc oH) 32) = true
  -- `m` and `G(m ‖ H(ek))` keep the matrix
  gK : (keepB (ecB L) ([(sc oM, 32)] ++ hW₃) (sc oSB) 32 &&
    (List.range (L.k * L.k)).all (fun e => keepB (ecB L) ([(sc oM, 32)] ++ hW₃) (pS (L.pA + e)) 1024)) = true

variable {L}

/-- After the fragments and `H(ek)`, with the first `e` entries of `Â`. -/
structure MI (L : Kem) (σ : State) (e : Nat) (s : State) : Prop where
  ec : EK L σ s
  sb : bytesAt s.mem (pa s (sc oSB)) 32 = Enc.rhoE L (ekE L σ)
  mat : MatB L (Enc.rhoE L (ekE L σ)) e s
  h : bytesAt s.mem (pa s (sc oH)) 32 = H (ekE L σ)

/-- The sponge's state zeroed. -/
theorem hzero_ok {rbs wbs : List (Reg × Nat)} {s : State} (Lx : Lay rbs wbs s)
    (hin : inB wbs (sc (oHS L)) 200 = true) :
    WP isa (.block (hzero L)) s fun s' => PPost s s' [(sc (oHS L), 200)] ∧
      stateAt s'.mem (pa s (sc (oHS L))) = Spec.Sha3.zero := by
  have hc := Lx.cW hin
  unfold hzero
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (mov0_ok s) fun s₁ ⟨h0, hm1, k1⟩ => ?_
  have e1 : s₁.gpr .rbx = s.gpr .rbx := k1.1 .rbx (by decide)
  refine WP.mono (zeroSt_ok .rbx (oHS L) s₁ h0 fun j hj => ?_) fun s₂ ⟨hz, f2, k2⟩ => ?_
  · rw [k1.2.2, e1]
    exact hc _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩
  · rw [e1] at hz f2
    refine ⟨post_of_keep (k1.trans k2) (by decide) ?_, hz⟩
    show Frame [⟨pa s (sc (oHS L)), 200⟩] s.mem s₂.mem
    rw [← hm1]; exact f2

theorem quadM_ok (v : Sample4Impl) (F : EkHWf L) {σ : State} (hp : (encK L).pre σ) {q : Nat}
    (hq : q < L.k * L.k / 4) (h3 : 3 * nb L ≤ 4 * q) {s : State} (h : MI L σ (4 * q) s) :
    WP isa (quad v.callee L.k (4 * q) (pS (L.pA + 4 * q)) (pS L.pW)) s (MI L σ (4 * q + 4)) := by
  have W := F.toEcWf
  have hc := F.qC q hq h3
  simp only [fkeep, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨hqc, ⟨hE, hS⟩, hA⟩, hH⟩ := hc
  have L₀ := h.ec.lay W hp
  have h16 : L.k * L.k ≤ 16 := Nat.mul_le_mul W.k.2 W.k.2
  refine WP.mono (quad_ok v L₀ (ecB_bases L) (by omega) hqc) fun s' ⟨hP, h15, hres⟩ =>
    ⟨h.ec.step W hp hP hE, by rw [L₀.keepBytes hP hS]; exact h.sb, MatB.four h.mat h.sb L₀ hP hA h15 hres,
      by rw [L₀.keepBytes hP hH]; exact h.h⟩

/-- After `ρ` to `SB`. -/
structure RI (L : Kem) (σ s : State) : Prop where
  ec : EK L σ s
  sb : bytesAt s.mem (pa s (sc oSB)) 32 = Enc.rhoE L (ekE L σ)
  r15 : s.gpr .r15 = 1

theorem rho_ok (F : EkHWf L) {σ : State} (hp : (encK L).pre σ) {s : State} (h : ProOut L σ s) :
    WP isa (copy (sc oSB) (.r14, 384 * L.k) 32) s (RI L σ) := by
  have W := F.toEcWf
  have L₀ := h.ec.lay W hp
  have hrC := F.rC
  simp only [Bool.and_eq_true] at hrC
  refine WP.mono (copy_okL L₀ (show Reg.r14 ≠ .rdi by decide) hrC.1) fun s₁ ⟨hP₁, hb₁⟩ =>
    ⟨h.ec.step W hp hP₁.b hrC.2, ?_, by rw [hP₁.cs .r15 (by decide), h.r15]⟩
  rw [hP₁.pa rbx_cs, hb₁, ← h.ec.ek]
  show _ = ((bytesAt s.mem (pa s (.r14, 0)) (384 * L.k + 32)).drop (384 * L.k)).take 32
  rw [bytesAt_slice _ _ (Nat.le_refl _), pa, pa, off_add, Nat.zero_add]

theorem hz_ok (F : EkHWf L) {σ : State} (hp : (encK L).pre σ) {s : State} (h : RI L σ s) :
    WP isa (.block (hzero L)) s (FI L σ 0) := by
  have W := F.toEcWf
  have L₁ := h.ec.lay W hp
  have hzC := F.zC
  simp only [fkeep, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hzC
  obtain ⟨hzin, ⟨hzE, hzS⟩, -⟩ := hzC
  exact WP.mono (hzero_ok L₁ hzin) fun s₂ ⟨hP₂, hz⟩ => ⟨h.ec.step W hp hP₂.b hzE,
    by rw [L₁.keepBytes hP₂.b hzS]; exact h.sb, MatB.zero L _ (by rw [hP₂.cs .r15 (by decide), h.r15]),
    by rw [hP₂.pa rbx_cs, hz, HSponge.hstate_zero]⟩

theorem hcopy_ok (F : EkHWf L) {σ : State} (hp : (encK L).pre σ) {s : State} (h : FI L σ (nb L) s) :
    WP isa (copy (sc oH) (sc (oHS L)) 32) s (MI L σ (3 * nb L)) := by
  have W := F.toEcWf
  have hhC := F.hC
  simp only [fkeep, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hhC
  obtain ⟨hcp, ⟨hE, hS⟩, hA⟩ := hhC
  have L₃ := h.ec.lay W hp
  have hn := F.nbE
  have hlen : (ekE L σ).length = L.ekLen := bytesAt_length _ _ _
  exact WP.mono (copy_okL L₃ (show Reg.rbx ≠ .rdi by decide) hcp) fun s₄ ⟨hP₄, hb₄⟩ =>
    ⟨h.ec.step W hp hP₄.b hE, by rw [L₃.keepBytes hP₄.b hS]; exact h.sb,
      ⟨by rw [hP₄.cs .r15 (by decide)]; exact h.mat.r15,
        fun e he f hf => L₃.keepPoly hP₄.b (hA e he) (h.mat.mat e he f hf)⟩,
      by rw [hP₄.pa rbx_cs, hb₄, HSponge.bytesAt_stateAt, h.hs, ← HSponge.H_of_hstate (by rw [hlen]; omega)]⟩

theorem entsM_ok (v : Sample4Impl) (F : EkHWf L) {σ : State} (hp : (encK L).pre σ) {s : State}
    (h : MI L σ (3 * nb L) s) :
    WP isa (L.ents v.callee (3 * nb L) (L.k * L.k - 3 * nb L)) s (MI L σ (L.k * L.k)) := by
  have := ents_ok L v.callee (I := fun e s => 3 * nb L ≤ e ∧ MI L σ e s)
    (fun e he he' _ hs => absurd F.noS (by omega))
    (fun q hq _ hs => WP.mono (quadM_ok v F hp hq hs.1 hs.2) fun _ h => ⟨by omega, h⟩)
    (L.k * L.k - 3 * nb L) (3 * nb L) (by have := F.nbK; omega) F.eS s ⟨Nat.le_refl _, h⟩
  rw [Nat.add_sub_cancel' F.nbK.2] at this
  exact WP.mono this fun _ h => h.2

/-- `ρ` to `SB`, the fragments, `H(ek)` to `H`, and the remaining entries of `Â`. -/
theorem matH_ok (v : Sample4Impl) (F : EkHWf L) {b : Prog isa} (hb : BatchHOk b) {σ : State}
    (hp : (encK L).pre σ) {s : State} (h : ProOut L σ s) : WP isa (matH L v.callee b) s (MI L σ (L.k * L.k)) := by
  unfold matH
  exact WP.seq (WP.mono (rho_ok F hp h) fun _ h₁ => WP.seq (WP.mono (hz_ok F hp h₁) fun _ h₂ =>
    WP.seq (WP.mono (frags_ok F.toEkFWf hb hp h₂) fun _ h₃ => WP.seq (WP.mono (hcopy_ok F hp h₃) fun _ h₄ =>
      entsM_ok v F hp h₄))))

/-- `m` to `M` and `G(m ‖ H(ek))`, keeping the matrix. -/
theorem hashesF_ok (F : EkHWf L) {σ : State} (hp : (encK L).pre σ) {s : State} (h : MI L σ (L.k * L.k) s) :
    WP isa EncapsH.hashes s
      (Enc.EB L (Ek.ekC F.toEcWf.toEcWfB σ) (.r14, 0) (ekE L σ) (ekMs σ) (ekG L σ).2 (L.k * L.k)) := by
  have W := F.toEcWf
  have L₀ := h.ec.lay W hp
  have hg := F.gK
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hg
  refine WP.mono (Ek.hashes_okP W.toEcWfB hp h.ec h.h) fun s' ⟨hP, h15, hi⟩ =>
    ⟨hi, by rw [L₀.keepBytes hP hg.1]; exact h.sb, ⟨by rw [h15]; exact h.mat.r15,
      fun e he f hf => L₀.keepPoly hP (hg.2 e he) (h.mat.mat e he f hf)⟩⟩

/-- The rest of `K-PKE.Encrypt`, if every `SampleNTT` succeeded. -/
theorem ifRest_ok (v : Sample4Impl) (F : EkHWf L) {wc wd : List Nat} (K : KemCalls L wc wd) {σ s : State}
    (h : Enc.EB L (Ek.ekC F.toEcWf.toEcWfB σ) (.r14, 0) (ekE L σ) (ekMs σ) (ekG L σ).2 (L.k * L.k) s) :
    WP isa (ifOk (Encrypt.rest L v.callee (.r14, 0))) s (Ek.EncO F.toEcWf σ) := by
  have hc := Enc.encChk_spec F.toEcWf.enc
  refine ifOk_ok (fun s₁ hP hne => Enc.rest_ok v K F.toEcWf.toKemWf hc
    (Enc.ER0.start (h.flag hP hc.inK hc.aK hc.sbK) (KeyGen.r15_ne h.m.r15 hne))) fun s₁ hP he => ?_
  have h₁ := h.flag hP hc.inK hc.aK hc.sbK
  exact ⟨h₁.i.out, h₁.m.r15, fun ho => absurd ho (KeyGen.r15_eq h.m.r15 he)⟩

end EkF

open EkF Ek in
theorem kemEncapsF_correct (v : Sample4Impl) {L : Kem} (F : EkHWf L) {wc wd : List Nat}
    (K : KemCalls L wc wd) {b : Prog isa} (hb : v.callee.batchH = some b)
    (hctl : ctlOk (kemEncaps L v.callee) = true) (σ : State) (hp : (encK L).pre σ) :
    ∃ t s', Exec isa (kemEncaps L v.callee) σ t s' ∧ abiPreserved σ s' ∧ (encK L).post σ s' := by
  have W₀ := F.toEcWf
  have hB := v.batchH b hb
  unfold kemEncaps at hctl ⊢
  rw [hb] at hctl ⊢
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (pro_ok W₀.toEcWfB hp) fun s₁ h₁ =>
    WP.seq (WP.mono (matH_ok v F hB hp h₁) fun s₂ h₂ =>
      WP.seq (WP.mono (hashesF_ok F hp h₂) fun s₃ h₃ =>
        WP.seq (WP.mono (ifRest_ok v F K h₃) fun s₄ h₄ =>
          WP.seq (WP.mono (out_ok W₀ h₄) fun s₅ h₅ =>
            WP.mono (topEpi_ok h₅.ec.top (h₅.hin W₀.toEcWfB hp)) fun s₆ ⟨hr, hg, hm⟩ =>
              (⟨hg, post_of W₀.toEcWfB h₅ hr hm⟩ : gprPreserved σ s₆ ∧ (encK L).post σ s₆))))))
  exact ⟨t, s', he, abiPreserved_of_ctl hctl he hF.1, hF.2⟩

end VG.Proof.MlKem.X86_64
