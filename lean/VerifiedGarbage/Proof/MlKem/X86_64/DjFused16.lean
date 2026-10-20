module

public import VerifiedGarbage.Proof.MlKem.X86_64.DjFrag16
meta import VerifiedGarbage.Proof.MlKem.X86_64.DjFrag16
public import VerifiedGarbage.Proof.MlKem.X86_64.DcTop16
meta import VerifiedGarbage.Proof.MlKem.X86_64.DcTop16
import VerifiedGarbage.Proof.MlKem.X86_64.EkFused16
meta import VerifiedGarbage.Proof.MlKem.X86_64.EkFused16
import all Init.Data.Nat.Bitwise.Basic
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
import VerifiedGarbage.Proof.MlKem.X86_64.KgTop
meta import Mathlib.Tactic.Conv
meta import VerifiedGarbage.Proof.MlKem.X86_64.YLanes

/-!
# ML-KEM on x86-64: decapsulation hashing `z ‖ c` in the matrix's fragments, with 16-bit polynomials

`kemDecapsJ16_correct`: the prologue and `m'` (`Dc16Dec.lean`);
`G(m' ‖ h)` alone, which gives the re-encryption's inputs in the context
before `K̄` (`hashG_ok`, `dcXG`); `ρ` to `SB` and `J`'s sponge zeroed; the
fragments (`fragsJ_ok`, `DjFrag16.lean`); `J(z ‖ c)` to `KB`, which moves
the inputs to the context of the re-encryption after the hashes (`dcX`,
`kbJ_ok`); the remaining entries of `Â` (`entsJ_ok`); and, if every
`SampleNTT` succeeded, the rest of the re-encryption and the choice of the
key.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt)

namespace DjF16

open VG.Proof.MlKem.X86_64.Decaps (DC DCK DM dcDk dcC dcEk dcM' dcG dcKb dcR dcW dcB dcB_bases dcChk dckChk DcWfB
  slice_of dcX)
open VG.Impl.MlKem.X86_64.Encaps (nb)
open VG.Impl.MlKem.X86_64.Encaps16 (oHS oHB hzero)
open VG.Impl.MlKem.X86_64.DecapsJ16 (jLen hashG frag matJ)
open VG.Impl.MlKem.X86_64.Top16 (aP)

variable (K : Kem16)

/-- What decapsulation hashing `z ‖ c` in the fragments needs of the layout, besides the fragments'. -/
structure DjHWf : Prop extends DjFWf K where
  /-- The entries after the fragments are sampled four at a time. -/
  eS : 3 * nb K.L % 4 = 0 ∨ 4 * (K.L.k * K.L.k / 4) ≤ 3 * nb K.L
  noS : K.L.k * K.L.k ≤ 4 * (K.L.k * K.L.k / 4) ∨ K.L.k * K.L.k ≤ 3 * nb K.L
  -- `J(z ‖ c)` to `KB`
  kC : (copyChk (dcB K.L) (dcW K.L) (sc oKB) (sc (oHS K)) 32 && fkeep K [(sc oKB, 32)] (3 * nb K.L)) = true

variable {K}

/-- After `G(m' ‖ h)`: the re-encryption's inputs in the context before `K̄`, and `r15 = 1`. -/
abbrev GI (W : DcWfB K.L oCT16) (σ s : State) : Prop :=
  Enc.EIn K.L (dcXG W σ) (.rbp, 384 * K.L.k) (dcEk K.L σ) (dcM' K.L σ) (dcG K.L σ).2 s ∧ s.gpr .r15 = 1

/-- The re-encryption's inputs in its context, with the first `e` entries of `Â`. -/
abbrev EBX (W : DcWfB K.L oCT16) (σ : State) (e : Nat) (s : State) : Prop :=
  Enc16.EB16 K (dcX W σ) (.rbp, 384 * K.L.k) (dcEk K.L σ) (dcM' K.L σ) (dcG K.L σ).2 e s

theorem hashG_ok (W : DcWfB K.L oCT16) {σ : State} (hp : (decapsK K.L).pre σ) {s : State} (h : DM K.L σ s) :
    WP isa (hashG K) s (GI W σ) := by
  have L₀ := h.dc.lay W hp
  have hdk : 768 * K.L.k + 96 = K.L.dkLen := rfl
  unfold hashG
  refine WP.mono (hash_ok (dcB_bases K.L) (ps := [(sc oM, 32), ((.rbp, 768 * K.L.k + 32), 32)]) (rate := 72)
    (out := sc oG) (len := 64) W.h₁ (show 6 < 256 by decide) L₀) fun s₁ ⟨hP₁, hb₁⟩ => ?_
  have k₁ := h.dc.step W hp hP₁.b W.h₁K
  simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, h.m,
    slice_of h.dc.dk (show 768 * K.L.k + 32 + 32 ≤ K.L.dkLen by omega), KeyGen.sha3Suffix6] at hb₁
  rw [← sha3_512_eq, ← hP₁.pa rbx_cs] at hb₁
  have hK : bytesAt s₁.mem (pa s₁ (sc oG)) 32 = (dcG K.L σ).1 := by
    rw [← bytesAt_take _ _ (show 32 ≤ 64 by decide), hb₁]; rfl
  have hr : bytesAt s₁.mem (pa s₁ sigP) 32 = (dcG K.L σ).2 := by
    have e := bytesAt_drop s₁.mem (pa s₁ (sc oG)) (k := 32) (len := 64) (by decide)
    have e' : (bytesAt s₁.mem (pa s₁ (sc oG)) 64).drop 32 = bytesAt s₁.mem (pa s₁ sigP) 32 := by
      rw [e, pa, pa, off_add]
    rw [← e', hb₁]; rfl
  refine ⟨⟨⟨hp, k₁, hK⟩, slice_of k₁.dk (show 384 * K.L.k + (384 * K.L.k + 32) ≤ K.L.dkLen by omega), ?_, hr⟩, ?_⟩
  · rw [L₀.keepBytes hP₁.b W.h₁M]; exact h.m
  · rw [hP₁.cs .r15 (by decide), h.r15]

theorem rhoJ_ok (F : DjHWf K) {σ : State} {s : State} (h : GI F.toDcWfB σ s) :
    WP isa (copy (sc oSB) (.rbp, 384 * K.L.k + 384 * K.L.k) 32) s (EBG F.toDcWfB σ 0) := by
  have L₀ := (dcXG F.toDcWfB σ).lay h.1.out
  have hrC := F.rC
  simp only [Bool.and_eq_true] at hrC
  refine WP.mono (copy_okL L₀ (show Reg.rbp ≠ .rdi by decide) hrC.1) fun s₁ ⟨hP₁, hb₁⟩ =>
    ⟨h.1.keep hP₁.b hrC.2, ?_, MatB16.zero _ _ _ (by rw [hP₁.cs .r15 (by decide), h.2])⟩
  rw [show pa s₁ (sc oSB) = pa s (sc oSB) from hP₁.pa rbx_cs, hb₁]
  exact h.1.rho

theorem hzJ_ok (F : DjHWf K) {σ : State} {s : State} (h : EBG F.toDcWfB σ 0 s) :
    WP isa (.block (hzero K)) s (FJ F.toDcWfB σ 0) := by
  have L₁ := (dcXG F.toDcWfB σ).lay h.i.out
  have hzC := F.zC
  simp only [fkeep, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hzC
  obtain ⟨hzin, ⟨hzE, hzS⟩, -⟩ := hzC
  exact WP.mono (EkF16.hzero16_ok L₁ hzin) fun s₂ ⟨hP₂, hz⟩ =>
    ⟨⟨h.i.keep hP₂.b hzE, by rw [L₁.keepBytes hP₂.b hzS]; exact h.sb,
      ⟨by rw [hP₂.cs .r15 (by decide)]; exact h.m.r15, fun _ he => absurd he (Nat.not_lt_zero _)⟩⟩,
      by rw [hP₂.pa rbx_cs, hz, HSponge.hstate_zero]⟩

/-- `J(z ‖ c)` to `KB`: the inputs move to the re-encryption's context. -/
theorem kbJ_ok (F : DjHWf K) {σ : State} {s : State} (h : FJ F.toDcWfB σ (nb K.L) s) :
    WP isa (copy (sc oKB) (sc (oHS K)) 32) s (EBX F.toDcWfB σ (3 * nb K.L)) := by
  have L₃ := (dcXG F.toDcWfB σ).lay h.eb.i.out
  have hkC := F.kC
  simp only [fkeep, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hkC
  obtain ⟨hcp, ⟨hE, hS⟩, hA⟩ := hkC
  have hn := F.nbJ
  have hlen := zcE_length K.L σ
  have hjl : jLen K = 32 + K.L.ctLen := rfl
  refine WP.mono (copy_okL L₃ (show Reg.rbx ≠ .rdi by decide) hcp) fun s₄ ⟨hP₄, hb₄⟩ => ?_
  have i₄ := h.eb.i.keep hP₄.b hE
  refine ⟨⟨⟨i₄.out.1, i₄.out.2.dc, i₄.out.2.k, ?_⟩, i₄.ek, i₄.m, i₄.r⟩,
    by rw [L₃.keepBytes hP₄.b hS]; exact h.eb.sb,
    ⟨by rw [hP₄.cs .r15 (by decide)]; exact h.eb.m.r15,
      fun e he f hf => L₃.keepPoly16 hP₄.b (hA e he) (h.eb.m.mat e he f hf)⟩⟩
  rw [hP₄.pa rbx_cs, hb₄, HSponge.bytesAt_stateAt, h.hs,
    ← HSponge.J_of_hstate (by rw [hlen]; omega)]

theorem entsJ_ok {n : String} {c : Prog isa} (v : S16Ok c) (F : DjHWf K) {σ : State} {s : State}
    (h : EBX F.toDcWfB σ (3 * nb K.L) s) :
    WP isa (ents16 (n, c) K.L.k K.oA (sc K.oW) (3 * nb K.L) (K.L.k * K.L.k - 3 * nb K.L)) s
      (EBX F.toDcWfB σ (K.L.k * K.L.k)) := by
  have h16 : K.L.k * K.L.k ≤ 16 := Nat.mul_le_mul F.k.2 F.k.2
  have := ents16_ok (n, c) K.L.k K.oA (sc K.oW) (I := fun e s => 3 * nb K.L ≤ e ∧ EBX F.toDcWfB σ e s)
    (fun e he he' _ hs => absurd F.noS (by omega))
    (fun q hq _ hs => WP.mono (Enc16.quadE_step v (by omega) (F.enc.q q hq) hs.2) fun _ h => ⟨by omega, h.2⟩)
    (K.L.k * K.L.k - 3 * nb K.L) (3 * nb K.L) (by have := F.nbK; omega) F.eS s ⟨Nat.le_refl _, h⟩
  rw [Nat.add_sub_cancel' F.nbK.2] at this
  exact WP.mono this fun _ h => h.2

/-- `ρ` to `SB`, the fragments, `J(z ‖ c)` to `KB`, and the remaining entries of `Â`. -/
theorem matJ_ok {n : String} {c : Prog isa} (v : S16Ok c) (F : DjHWf K) {b : Prog isa} (hb : BatchHOk16 b)
    {σ : State} {s : State} (h : GI F.toDcWfB σ s) :
    WP isa (matJ K (n, c) b) s (EBX F.toDcWfB σ (K.L.k * K.L.k)) := by
  unfold matJ
  exact WP.seq (WP.mono (rhoJ_ok F h) fun _ h₁ => WP.seq (WP.mono (hzJ_ok F h₁) fun _ h₂ =>
    WP.seq (WP.mono (fragsJ_ok F.toDjFWf hb h₂) fun _ h₃ => WP.seq (WP.mono (kbJ_ok F h₃) fun _ h₄ =>
      entsJ_ok v F h₄))))

/-- The rest of the re-encryption, if every `SampleNTT` succeeded. -/
theorem ifRestJ_ok (hK : KpkeOk K.L) (v : Sample4Impl) (F : DjHWf K) {σ s : State}
    (h : EBX F.toDcWfB σ (K.L.k * K.L.k) s) :
    WP isa (ifOk (Top16.encRest K v.callee (.rbp, 384 * K.L.k) (sc oCT16))) s (Decaps16.EncO16 F.toDc16Wf σ) := by
  refine ifOk_ok (fun s₁ hP hne => Enc16.rest_ok hK v (show Reg.rbp ∉ argRegs by decide) (by decide) F.k.2 F.enc F.tl
    (Enc16.ER0.start (h.flag hP F.enc) (KeyGen.r15_ne h.m.r15 hne))) fun s₁ hP he => ?_
  have h₁ := h.flag hP F.enc
  exact ⟨h₁.i.out, h₁.m.r15, fun ho => absurd ho (KeyGen.r15_eq h.m.r15 he)⟩

end DjF16

open Decaps Decaps16 DjF16 in
theorem kemDecapsJ16_correct {K : Kem16} (hK : KpkeOk K.L) (v : Sample4Impl) (F : DjHWf K) {n : String}
    {c : Prog isa} (hs : v.callee.s16 = some (n, c)) {b : Prog isa} (hb : v.callee.batchH16 = some b)
    (hctl : ctlOk (kemDecapsJ16 K v.callee (n, c) b) = true) (σ : State) (hp : (decapsK K.L).pre σ) :
    ∃ t s', Exec isa (kemDecapsJ16 K v.callee (n, c) b) σ t s' ∧ abiPreserved σ s' ∧ (decapsK K.L).post σ s' := by
  have hB := v.batchH16 b hb
  have hS := v.s16 n c hs
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (pro_ok F.toDcWfB hp) fun s₁ ⟨h₁, h15⟩ =>
    WP.seq (WP.mono (dec_ok hK F.toDc16Wf hp h₁ h15) fun s₂ h₂ =>
      WP.seq (WP.mono (hashG_ok F.toDcWfB hp h₂) fun s₃ h₃ =>
        WP.seq (WP.mono (matJ_ok hS F hB h₃) fun s₄ h₄ =>
          WP.seq (WP.mono (ifRestJ_ok hK v F h₄) fun s₅ h₅ =>
            WP.seq (WP.mono (select_okD F.toDcWfB (EncO16.sel (W := F.toDc16Wf) h₅)) fun s₆ h₆ =>
              WP.mono (topEpi_ok h₆.dc.top (h₆.hin F.toDcWfB hp)) fun s₇ ⟨hr, hg, hm⟩ =>
                (⟨hg, post_of F.toDcWfB h₆ hr hm⟩ : gprPreserved σ s₇ ∧ (decapsK K.L).post σ s₇)))))))
  exact ⟨t, s', he, abiPreserved_of_ctl hctl he hF.1, hF.2⟩

end VG.Proof.MlKem.X86_64
