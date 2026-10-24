module

import VerifiedGarbage.Proof.Bignum.X86_64.FoldedMain
public import VerifiedGarbage.Proof.Bignum.X86_64.PdCode
public import VerifiedGarbage.Impl.Rsa.X86_64.Folded
public import VerifiedGarbage.Proof.Bignum.X86_64.PubMain
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.Compare8
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.Octets
public import Mathlib.Logic.Relator
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

@[expose] public section

namespace VG.Proof.Bignum.X86_64.FoldedPublic
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- The code after the check of `e`, for a valid `e`, with any `rest` that
`rest_ok` describes, MXCSR's control bits included. -/
theorem codeWith_correct (rest : Prog isa)
    (hrest : ∀ {t : State} {B : Addr} {Z k : Nat} {op ep ip : Addr} {L : Nat} {eb xb : List Byte} {N R : Nat},
      PdPre t B Z k op ep ip L eb xb N R → WP isa rest t fun t' => ∃ y : Nat,
        (R % N = 2^(64*((k+7)/8)) * 2^(64*((k+7)/8)) % N → y = Spec.Rsa.os2ip xb ^ Spec.Rsa.os2ip eb % N) ∧
        MainPost t t' B Z k op (if Spec.Rsa.os2ip xb < N then y else 0) (decide (Spec.Rsa.os2ip xb < N)) ∧
        t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10)
    (s : State) (h : pdContract.pre s)
    (hev : Spec.Rsa.exponentValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)) = true) :
    ∃ t s', Exec isa (.seq (.block Precomputed.entry) (.seq (seqs (Precomputed.loadWith Compare8.code))
      (.ite .e fail rest))) s t s' ∧ abiPreserved s s' ∧ pdContract.post s s' := by
  have c := pdCtx_of h
  have hZ' := c.hZ
  have hk1 := c.hk1
  have hk2 := c.hk2
  have hn := c.hs.nowrap
  suffices hwp : WP isa (.seq (.block Precomputed.entry) (.seq (seqs (Precomputed.loadWith Compare8.code))
      (.ite .e fail rest))) s fun s' => (gprPreserved s s' ∧ pdContract.post s s') ∧
        s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 by
    obtain ⟨t, s', he, ⟨hg, hp⟩, hx⟩ := hwp
    exact ⟨t, s', he, ⟨hg.1, hg.2, hx⟩, hp⟩
  have hw : ∀ i < 22, InRegions s.wr (off (stackArg s 2) (8 * i)) 8 := fun i hi => c.hs.st (by omega)
  refine WP.seq (WP.mono_mx (by decide +kernel) (pdEntry_ok rfl hw c.ha0 c.ha2 c.hsep) fun t₁ ⟨hdi, h0, h1, h2, h3, h4, h5, hO, hN, hK,
    hE, hL, hIn, ho₁, k₁⟩ mx₁ => ?_)
  have i₁ : InScr (stackArg s 2) ((stackArg s 3).toNat * 8) s.mem t₁.mem := InScr.of_outside ho₁ (by omega)
  have hz : slot (((s.gpr .rsi).toNat + 7) / 8) 8 ≤ (stackArg s 3).toNat * 8 := by unfold slot hdrBytes; omega
  refine WP.seq (WP.mono_mx (by decide +kernel) (pdLoadWith_ok VG.Impl.Rsa.X86_64.Compare8.code @Compare8.code_ok (c.hs.congr k₁.2.2) hdi hz (by omega) (by omega) (by rw [hK, ofNat_toNat64])
    hN (fun i hi => by rw [k₁.2.1, k₁.2.2]; exact c.hpr i hi) c.hps)
    fun t₂ ⟨hN₂, hR₂, hW₂, hb₂, hz₂, f₂, k₂⟩ mx₂ => ?_)
  rw [pre_wv_entry c i₁ (by omega)] at hN₂
  rw [pre_wv_entry c i₁ (by omega)] at hR₂
  have x₂ := Fixed.of_frm f₂ (pdLoadRanges_fixed _)
  have i₂ : InScr (stackArg s 2) ((stackArg s 3).toNat * 8) s.mem t₂.mem :=
    i₁.trans (InScr.of_frm f₂ fun r hr => (pdLoadRanges_le _ r hr).trans hz)
  have kk := k₁.trans k₂
  have hs₂ := c.hs.congr kk.2.2
  have hdi₂ : t₂.gpr .rdi = stackArg s 2 := (k₂.gpr (by decide)).trans hdi
  have hO₂ : word t₂.mem (stackArg s 2) (8 * sOut) = s.gpr .rdi := by rw [x₂ sOut (by decide)]; exact hO
  have hK₂ : word t₂.mem (stackArg s 2) (8 * sK) = BitVec.ofNat 64 (s.gpr .rsi).toNat := by
    rw [x₂ sK (by decide), hK, ofNat_toNat64]
  have hout₂ : ∀ j < (s.gpr .rsi).toNat, InRegions t₂.wr (s.gpr .rdi + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [kk.2.2]; exact c.hout j hj
  -- What either branch leaves.
  have fin : ∀ t r (cb : Bool),
      MainPost t₂ t (stackArg s 2) ((stackArg s 3).toNat * 8) (s.gpr .rsi).toNat (s.gpr .rdi) r cb →
      (∀ nB : List Byte, nB.length = (s.gpr .rsi).toNat →
        Spec.Rsa.modulusValid (Spec.Rsa.os2ip nB) (s.gpr .rsi).toNat = true →
        wv s.mem (s.gpr .rdx) 0 (((s.gpr .rsi).toNat + 7) / 8) = Spec.Rsa.os2ip nB →
        wv s.mem (s.gpr .rdx) (8 * (((s.gpr .rsi).toNat + 7) / 8)) (((s.gpr .rsi).toNat + 7) / 8) =
          2 ^ (128 * (((s.gpr .rsi).toNat + 7) / 8)) % Spec.Rsa.os2ip nB →
        cb = decide (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rsi).toNat) < Spec.Rsa.os2ip nB) ∧
        r = if Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rsi).toNat) < Spec.Rsa.os2ip nB then
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rsi).toNat) ^
            Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) % Spec.Rsa.os2ip nB else 0) →
      gprPreserved s t ∧ pdContract.post s t := by
    intro t r cb hp H
    refine ⟨⟨fun reg hreg => ?_, Mem.readW_congr fun b hb => ?_⟩, fun nB hl hpp => ?_⟩
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hreg
      rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (hp.saved 0 (by decide)).trans ((x₂ 0 (by decide)).trans h0)
      · exact (hp.saved 1 (by decide)).trans ((x₂ 1 (by decide)).trans h1)
      · exact (hp.keep.gpr (by decide)).trans (kk.gpr (by decide))
      · exact (hp.saved 2 (by decide)).trans ((x₂ 2 (by decide)).trans h2)
      · exact (hp.saved 3 (by decide)).trans ((x₂ 3 (by decide)).trans h3)
      · exact (hp.saved 4 (by decide)).trans ((x₂ 4 (by decide)).trans h4)
      · exact (hp.saved 5 (by decide)).trans ((x₂ 5 (by decide)).trans h5)
    · obtain ⟨hZx, hne⟩ := c.hret b hb
      rw [hp.frame _ hZx hne, i₂ _ hZx]
    · rw [c.hpl] at hpp
      obtain ⟨hv, hNv, hRv⟩ := pre_of_some hl hk1 hpp
      exact written_of hl hp.bytes hp.rax (fun _ => H nB hl hv hNv hRv) fun h => absurd h (by rw [hv]; decide)
  generalize hcb : (decide ((word t₂.mem (stackArg s 2) (slot (((s.gpr .rsi).toNat + 7) / 8) aN)).toNat % 2 = 1) &&
      decide (wv t₂.mem (stackArg s 2) (slot (((s.gpr .rsi).toNat + 7) / 8) aR2) (((s.gpr .rsi).toNat + 7) / 8) <
        wv t₂.mem (stackArg s 2) (slot (((s.gpr .rsi).toNat + 7) / 8) aN) (((s.gpr .rsi).toNat + 7) / 8)) &&
      decide (word t₂.mem (stackArg s 2) (slot (((s.gpr .rsi).toNat + 7) / 8) aN + 8 * ((((s.gpr .rsi).toNat + 7) / 8) - 1)) ≠ 0))
    = cb at hz₂
  refine WP.ite (!cb) (by simp [eval, hz₂]) (fun hb => ?_) (fun hb => ?_)
  · -- Values of no modulus.
    have hcf : cb = false := by simpa using hb
    refine WP.mono_mx (by decide +kernel) (fail_ok hs₂ hdi₂ (by omega) (by omega) (by omega) hO₂ hK₂ hout₂ c.houts)
      fun t hp mxt => ⟨fin t 0 false hp fun nB hl hv hNv hRv => ?_, by rw [mxt, mx₂, mx₁]⟩
    obtain ⟨hodd, -, hlo⟩ := valid_facts hv hk1
    have := checks_true (by omega) (hN₂.trans hNv) hodd hlo
      (by rw [hR₂, hRv]; exact Nat.mod_lt _ (by omega))
    rw [hcb, hcf] at this
    exact absurd this (by decide)
  · have hct : cb = true := by simpa using hb
    rw [hct] at hcb
    obtain ⟨hodd, hN1, hRN⟩ := checks_facts (by omega) hcb
    have hpre := pdPre_of c hdi hO hK hE hL hIn ho₁ k₁ hW₂ hb₂ f₂ k₂ hodd hN1 (checks_big (by omega) hcb) hRN hev
    refine WP.mono (hrest hpre) fun t ⟨y, hy, hp, mxt⟩ => ⟨fin t _ _ hp fun nB hl hv hNv hRv => ?_,
      by rw [mxt, mx₂, mx₁]⟩
    rw [hN₂.trans hNv] at hy hp ⊢
    have hyX := hy (by
      rw [hR₂, hRv, Nat.mod_mod, ← Nat.pow_add, show 128 * (((s.gpr .rsi).toNat + 7) / 8) =
        64 * (((s.gpr .rsi).toNat + 7) / 8) + 64 * (((s.gpr .rsi).toNat + 7) / 8) by omega])
    exact ⟨rfl, by rw [hyX]⟩

/-- The code after the check of `e`, for a valid `e`. -/
theorem code_correct (M : Mont)
    (hmx : (Folded.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true) (s : State) (h : pdContract.pre s)
    (hev : Spec.Rsa.exponentValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)) = true) :
    ∃ t s', Exec isa (Folded.code M.mm) s t s' ∧ abiPreserved s s' ∧ pdContract.post s s' := by
  have h' := hmx
  simp only [Folded.code, Code.allInstrs, Bool.and_eq_true] at h'
  have hr := h'.2.2.2
  have hmxp : (seqs (phases M)).allInstrs (fun i => !loadsMxcsr i) = true := by
    have h'' := hr
    rw [rest_eq, allInstrs_seqs_append _ (a := wordIn ++ restStepsWith VG.Impl.Rsa.X86_64.Compare8.code)
        (b := phases M ++ wordOutStepsArr aY) (by simp [wordIn]) (by simp [phases]),
      allInstrs_seqs_append _ (a := phases M) (b := wordOutStepsArr aY) (by simp [phases])
        (by simp [wordOutStepsArr]), Bool.and_eq_true, Bool.and_eq_true] at h''
    exact h''.2.1
  exact codeWith_correct (Folded.rest M.mm) (fun hp => WP.mono_mx hr (rest_ok M hp hmxp)
    fun t ⟨y, hy, hq⟩ mxt => ⟨y, hy, hq, by rw [mxt]⟩) s h hev

end VG.Proof.Bignum.X86_64.FoldedPublic
