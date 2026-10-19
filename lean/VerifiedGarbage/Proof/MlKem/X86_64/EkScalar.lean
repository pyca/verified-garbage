module

public import VerifiedGarbage.Proof.MlKem.X86_64.EkBase
meta import VerifiedGarbage.Proof.MlKem.X86_64.EkBase
import VerifiedGarbage.Proof.MlKem.X86_64.EcTop
meta import VerifiedGarbage.Proof.MlKem.X86_64.EcTop
import all Init.Data.Nat.Bitwise.Basic
import Mathlib.Tactic.Conv
meta import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.MlKem.X86_64.KgCT
meta import VerifiedGarbage.Proof.MlKem.X86_64.KgCT
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.Words
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Proof.MlKem.PolyW
import VerifiedGarbage.Proof.MlKem.X86_64.Cbd16Avx2
import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
import VerifiedGarbage.Proof.MlKem.X86_64.DecMulV
import VerifiedGarbage.Proof.MlKem.X86_64.EncMulV
import VerifiedGarbage.Proof.MlKem.X86_64.FragC
import VerifiedGarbage.Proof.MlKem.X86_64.FragDM
import VerifiedGarbage.Proof.MlKem.X86_64.FragL
import VerifiedGarbage.Proof.MlKem.X86_64.KgMulV
import VerifiedGarbage.Proof.MlKem.X86_64.KgTop
import VerifiedGarbage.Proof.MlKem.X86_64.MulAvx2
import VerifiedGarbage.Proof.MlKem.X86_64.S4Tab
import VerifiedGarbage.Proof.MlKem.X86_64.S4Top
import VerifiedGarbage.Proof.MlKem.X86_64.S4Verified
import VerifiedGarbage.Proof.MlKem.X86_64.VLay42
import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
import VerifiedGarbage.Proof.MlKem.X86_64.VPack
import VerifiedGarbage.Proof.MlKem.X86_64.YNttLay42
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Word
import VerifiedGarbage.Proof.Sha3.X86_64.X4R.Loop
meta import VerifiedGarbage.Proof.Bignum.Layout
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.Words
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
meta import VerifiedGarbage.Proof.Framework.CallLay
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Framework.X86_64.Words
meta import VerifiedGarbage.Proof.MlKem.PolyW
meta import VerifiedGarbage.Proof.MlKem.X86_64.Cbd16Avx2
meta import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
meta import VerifiedGarbage.Proof.MlKem.X86_64.DecMulV
meta import VerifiedGarbage.Proof.MlKem.X86_64.EncMulV
meta import VerifiedGarbage.Proof.MlKem.X86_64.FragC
meta import VerifiedGarbage.Proof.MlKem.X86_64.FragDM
meta import VerifiedGarbage.Proof.MlKem.X86_64.FragL
meta import VerifiedGarbage.Proof.MlKem.X86_64.KgMulV
meta import VerifiedGarbage.Proof.MlKem.X86_64.KgTop
meta import VerifiedGarbage.Proof.MlKem.X86_64.MulAvx2
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Tab
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Top
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Verified
meta import VerifiedGarbage.Proof.MlKem.X86_64.VLay42
meta import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
meta import VerifiedGarbage.Proof.MlKem.X86_64.VPack
meta import VerifiedGarbage.Proof.MlKem.X86_64.YNttLay42
meta import VerifiedGarbage.Proof.Sha3.Arith
meta import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
meta import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Word
meta import VerifiedGarbage.Proof.Sha3.X86_64.X4R.Loop

/-!
# ML-KEM on x86-64: encapsulation hashing the key with the sponge functions

`kemEncaps L v.callee` for any implementation `v` of `vg_mlkem_sample_ntt4`:
the prologue, `H(ek)` to `H` with
the sponge functions (`hashEk_ok`), and `kemEncapsH`'s rest (`EcTop.lean`),
in the context of `encK` (`EkBase.lean`): it returns 1 with
`ML-KEM.Encaps_internal(ek, m)` in `key` and `ct` if every `SampleNTT`
succeeded within 280 iterations, and 0 otherwise (`kemEncaps_correct`); it
leaks only the pointers and `ρ` (`kemEncaps_ct`). The out and the end
(`out_ok`, `post_of`) serve the encapsulation with 16-bit polynomials too.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace Ek

open VG.Proof.MlKem.X86_64.Encaps (ecR ecW ecB ecB_bases ecChk eckChk EcWf EcWfB hW₃ trL)
open VG.Impl.MlKem.X86_64.EncapsH (out)

/-- The writes of `H(ek)`. -/
abbrev hWE : List (Ptr × Nat) := [(sc 0, 200), (sc 200, 640), (sc oH, 32)]

/-- The checks of the layout `H(ek)` with the sponge functions needs. -/
structure EkWf (L : Kem) : Prop extends EcWf L where
  hE : hashChk (ecB L) (ecW L) [((.r14, 0), L.ekLen)] 136 (sc oH) 32 = true
  hEK : ecChk L hWE = true

variable {L : Kem}

/-- `H(ek)` to `H`. -/
theorem hashEk_ok (W : EkWf L) {σ : State} (hp : (encK L).pre σ) {s : State} (h : ProOut L σ s) :
    WP isa (Encaps.hashEk L) s fun s' => EK L σ s' ∧ bytesAt s'.mem (pa s' (sc oH)) 32 = H (ekE L σ) ∧
      s'.gpr .r15 = 1 := by
  have L₀ := h.ec.lay W.toEcWf hp
  unfold Encaps.hashEk
  refine WP.mono (hash_ok (ecB_bases L) (ps := [((.r14, 0), L.ekLen)]) (rate := 136) (out := sc oH) (len := 32)
    W.hE (show 6 < 256 by decide) L₀) fun s' ⟨hP, hb⟩ => ⟨h.ec.step W.toEcWf hp hP.b W.hEK, ?_, ?_⟩
  · simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, h.ec.ek, KeyGen.sha3Suffix6] at hb
    rw [← H_eq] at hb
    rw [hP.pa rbx_cs, hb]
  · rw [hP.cs .r15 (by decide), h.r15]

/-! ## The outputs and the exit -/

variable (W : EcWf L)

/-- The end of `K-PKE.Encrypt`. -/
abbrev EncO (σ s : State) : Prop := Enc.EOut L (ekC W.toEcWfB σ) (.r14, 0) (ekE L σ) (ekMs σ) (ekG L σ).2 s

/-- At the end: `r15` as `allOk`, `K` in `key`, and the ciphertext in `ct` if `r15` is 1. -/
structure EKEnd (L : Kem) (σ s : State) : Prop where
  ec : EK L σ s
  r15 : s.gpr .r15 = if allOk L.k (Enc.rhoE L (ekE L σ)) (L.k * L.k) then 1 else 0
  key : bytesAt s.mem (pa s (.r12, 0)) 32 = (ekG L σ).1
  ct : allOk L.k (Enc.rhoE L (ekE L σ)) (L.k * L.k) →
    bytesAt s.mem (pa s (.r13, 0)) L.ctLen = KPke.ct L.p (aHat (Enc.rhoE L (ekE L σ))) (ekE L σ) (ekMs σ)
      (ekG L σ).2

include W

theorem out_ok {σ : State} {s : State} (h : EncO W σ s) : WP isa (out L) s (EKEnd L σ) := by
  have hp := h.out.1
  have L₀ := h.out.2.ec.lay W hp
  unfold out
  refine WP.seq (WP.mono (copy_okL L₀ (dst := (.r12, 0)) (src := sc oG) (n := 32) (by decide) W.o₁)
    fun s₁ ⟨hP₁, hb₁⟩ => ?_)
  have k₁ := h.out.2.ec.step W hp hP₁.b W.o₁K
  have L₁ := k₁.lay W hp
  refine WP.mono (copy_okL L₁ (dst := (.r13, 0)) (src := sc L.oCT) (n := L.ctLen) (show Reg.rbx ≠ .rdi by decide) W.o₂)
    fun s₂ ⟨hP₂, hb₂⟩ => ?_
  have k₂ := k₁.step W hp hP₂.b W.o₂K
  refine ⟨k₂, ?_, ?_, fun ho => ?_⟩
  · rw [hP₂.cs .r15 (by decide), hP₁.cs .r15 (by decide)]; exact h.r15
  · rw [L₁.keepBytes hP₂.b W.o₂G, hP₁.pa (by decide), hb₁]; exact h.out.2.k
  · rw [hP₂.pa (by decide), hb₂, L₀.keepBytes hP₁.b W.o₁C]; exact h.ct ho

omit W in
theorem EKEnd.hin (W : EcWfB L) {σ s : State} (hp : (encK L).pre σ) (h : EKEnd L σ s) :
    ∀ k < 6, InRegions (s.rd ++ s.wr) (pa s (sc (oSV + 8 * k))) 8 := fun k hk =>
  (h.ec.lay W hp).cR (W.sv k hk) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

omit W in
/-- The postcondition, from the outputs. -/
theorem post_of (W : EcWfB L) {σ s : State} (h : EKEnd L σ s) {s' : State}
    (hr : (s'.gpr .rax).setWidth 32 = (s.gpr .r15).setWidth 32) (hm : s'.mem = s.mem) :
    (encK L).post σ s' := by
  have e12 : pa s (.r12, 0) = σ.gpr .rdx := by
    rw [pa, h.ec.top.regs (.r12, .rdx) (by decide), add_ofNat_zero]
  have e13 : pa s (.r13, 0) = σ.gpr .rcx := by
    rw [pa, h.ec.top.regs (.r13, .rcx) (by decide), add_ofNat_zero]
  show Outcome _ _ _
  by_cases ho : allOk L.k (Enc.rhoE L (ekE L σ)) (L.k * L.k)
  · refine .inl ⟨by rw [hr, h.r15, ifp ho]; rfl, minIterations, ?_⟩
    show encapsInternal L.p minIterations _ _ = _
    rw [KPke.encapsInternal_eq, KPke.kpkeEncrypt_some W.eta (a := aHat (Enc.rhoE L (ekE L σ)))
      fun i hi j hj => aHat_eq ho hi hj, Option.map_some, hm, ← e12, ← e13, h.key, h.ct ho]
  · refine .inr ⟨by rw [hr, h.r15, ifn ho]; rfl, ?_⟩
    obtain ⟨i, hi, j, hj, hn⟩ := not_allOk ho
    show encapsInternal L.p minIterations _ _ = _
    rw [KPke.encapsInternal_eq, KPke.kpkeEncrypt_none hi hj hn]
    rfl

end Ek

open Ek in
theorem kemEncaps_correct (v : Sample4Impl) {L : Kem} (W : EkWf L) {wc wd : List Nat}
    (K : KemCalls L wc wd) (hctl : ctlOk (kemEncaps L v.callee) = true) (σ : State) (hp : (encK L).pre σ) :
    ∃ t s', Exec isa (kemEncaps L v.callee) σ t s' ∧ abiPreserved σ s' ∧ (encK L).post σ s' := by
  have W₀ := W.toEcWf
  unfold kemEncaps at hctl ⊢
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (pro_ok W₀.toEcWfB hp) fun s₁ h₁ =>
    WP.seq (WP.mono (hashEk_ok W hp h₁) fun s₂ ⟨h₂, hH, h15⟩ =>
      WP.seq (WP.mono (hashes_ok W₀.toEcWfB hp h₂ hH h15) fun s₃ h₃ =>
        WP.seq (WP.mono (Enc.encrypt_ok v K W₀.toKemWf (C := ekC W₀.toEcWfB σ) W₀.enc h₃.1 h₃.2) fun s₄ h₄ =>
          WP.seq (WP.mono (out_ok W₀ h₄) fun s₅ h₅ =>
            WP.mono (topEpi_ok h₅.ec.top (h₅.hin W₀.toEcWfB hp)) fun s₆ ⟨hr, hg, hm⟩ =>
              (⟨hg, post_of W₀.toEcWfB h₅ hr hm⟩ : gprPreserved σ s₆ ∧ (encK L).post σ s₆))))))
  exact ⟨t, s', he, abiPreserved_of_ctl hctl he hF.1, hF.2⟩

/-! ## Constant time -/

namespace Ek

open VG.Proof.MlKem.X86_64.Encaps (ecR ecW ecB ecB_bases ecChk eckChk EcWf EcWfB hW₃ trL)
open VG.Impl.MlKem.X86_64.EncapsH (out)

variable {L : Kem} (W : EcWf L)

abbrev R (L : Kem) (I : State → State → Prop) : State → State → Prop := Rel2 (encK L).pre (encK L).pub I

include W

omit W in
theorem ek_lrel (W : EcWfB L) {σ₁ σ₂ x y : State} (p₁ : (encK L).pre σ₁) (p₂ : (encK L).pre σ₂)
    (pub : (encK L).pub σ₁ σ₂) (h₁ : EK L σ₁ x) (h₂ : EK L σ₂ y) : LRel (ecR L) (ecW L) x y := by
  obtain ⟨e1, e2, e3, e4, e5, e6, _⟩ := pub
  refine ⟨h₁.lay W p₁, h₂.lay W p₂, fa5 ?_ ?_ ?_ ?_ ?_, by rw [h₁.top.rsp, h₂.top.rsp, e6]⟩
  · rw [h₁.top.regs (.r14, .rdi) (by decide), h₂.top.regs (.r14, .rdi) (by decide), e1]
  · rw [h₁.top.regs (.rbp, .rsi) (by decide), h₂.top.regs (.rbp, .rsi) (by decide), e2]
  · rw [h₁.top.regs (.rbx, .r8) (by decide), h₂.top.regs (.rbx, .r8) (by decide), e5]
  · rw [h₁.top.regs (.r12, .rdx) (by decide), h₂.top.regs (.r12, .rdx) (by decide), e3]
  · rw [h₁.top.regs (.r13, .rcx) (by decide), h₂.top.regs (.r13, .rcx) (by decide), e4]

omit W in
theorem rho_pub {σ₁ σ₂ : State} (pub : (encK L).pub σ₁ σ₂) :
    Enc.rhoE L (ekE L σ₁) = Enc.rhoE L (ekE L σ₂) :=
  pub.2.2.2.2.2.2

omit W in
theorem pro_tr : RelCT isa (R L fun σ s => s = σ) (.block Encaps.pro) fun _ _ => True :=
  taintRel [.r8, .rsi, .rdx, .rcx, .rdi] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ => by
    subst h₁ h₂
    exact fa5 pub.2.2.2.2.1 pub.2.1 pub.2.2.1 pub.2.2.2.1 pub.1) (by taint_decide)

theorem hashes_tr :
    RelCT isa (R L fun σ s => EK L σ s ∧ bytesAt s.mem (pa s (sc oH)) 32 = H (ekE L σ) ∧ s.gpr .r15 = 1)
      EncapsH.hashes fun _ _ => True :=
  rel2_of (Encaps.hashes_trL W) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ek_lrel W.toEcWfB p₁ p₂ pub h₁.1 h₂.1

omit W in
theorem EIn.any {W : EcWfB L} {σ : State} {E : Ptr} {ek m r : List Byte} {s : State}
    (h : Enc.EIn L (ekC W σ) E ek m r s) : Enc.EIn L (ekCA W) E ek m r s :=
  ⟨⟨σ, h.out⟩, h.ek, h.m, h.r⟩

theorem encrypt_tr (v : Sample4Impl) {wc wd : List Nat} (K : KemCalls L wc wd) :
    RelCT isa (R L (EncI W.toEcWfB)) (encrypt L v.callee (.r14, 0)) fun _ _ => True := by
  obtain ⟨_, rhoT⟩ := W.rhoT
  refine RelCT.mono (RelCT.exists_ (P := fun ρ x y => LRel (ecR L) (ecW L) x y ∧ Enc.EIρ L (ekCA W.toEcWfB) (.r14, 0) ρ x ∧
      Enc.EIρ L (ekCA W.toEcWfB) (.r14, 0) ρ y) (Q := fun _ _ => True) fun ρ =>
      RelCT.mono (Enc.encrypt_tr v K W.toKemWf (C := ekCA W.toEcWfB) W.enc rhoT (ρ := ρ)) (fun _ _ h => h)
        fun _ _ _ => trivial) ?_ fun _ _ _ => trivial
  rintro x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩
  have i₁ : Enc.EIρ L (ekCA W.toEcWfB) (.r14, 0) (Enc.rhoE L (ekE L σ₁)) x := ⟨_, _, _, rfl, EIn.any h₁.1, h₁.2⟩
  have i₂ : Enc.EIρ L (ekCA W.toEcWfB) (.r14, 0) (Enc.rhoE L (ekE L σ₁)) y :=
    ⟨_, _, _, (rho_pub pub).symm, EIn.any h₂.1, h₂.2⟩
  exact ⟨Enc.rhoE L (ekE L σ₁), ek_lrel W.toEcWfB p₁ p₂ pub h₁.1.out.2.ec h₂.1.out.2.ec, i₁, i₂⟩

theorem out_tr : RelCT isa (R L (EncO W)) (out L) fun _ _ => True := by
  refine rel2_of (Q := LRel (ecR L) (ecW L)) ?_ fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
    ek_lrel W.toEcWfB p₁ p₂ pub h₁.out.2.ec h₂.out.2.ec
  unfold out
  obtain ⟨_, oT₁⟩ := W.oT₁
  obtain ⟨_, oT₂⟩ := W.oT₂
  exact RelCT.seq (LRel.step (ecB_bases L) (trL W oT₁) fun x Lx =>
      WP.mono (copy_okL Lx (dst := (.r12, 0)) (src := sc oG) (n := 32) (by decide) W.o₁)
        fun _ h => ⟨_, h.1⟩) (trL W oT₂)

omit W in
theorem epi_tr : RelCT isa (R L (EKEnd L)) (.block topEpi) fun _ _ => True :=
  taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [h₁.ec.top.regs (.rbx, .r8) (by decide), h₂.ec.top.regs (.rbx, .r8) (by decide), pub.2.2.2.2.1])
    (by taint_decide)

omit W in
theorem hashEk_tr (W : EkWf L) :
    RelCT isa (R L (ProOut L)) (Encaps.hashEk L) fun _ _ => True := by
  refine rel2_of (Q := LRel (ecR L) (ecW L)) ?_ fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
    ek_lrel W.toEcWf p₁ p₂ pub h₁.ec h₂.ec
  exact hash_tr (ecB_bases L) (ps := [((.r14, 0), L.ekLen)]) (rate := 136) (out := sc oH) (len := 32) W.hE
    (show 6 < 256 by decide)

end Ek

open Ek in
theorem kemEncaps_ct (v : Sample4Impl) {L : Kem} (W : EkWf L) {wc wd : List Nat}
    (K : KemCalls L wc wd) :
    ConstantTime isa (encK L).pre (encK L).pub (kemEncaps L v.callee) := by
  have W₀ := W.toEcWf
  refine relStart (Q := fun _ _ => True) ?_
  unfold kemEncaps
  refine RelCT.seq (relInv (I' := ProOut L) (fun σ s hp hs => by subst hs; exact pro_ok W₀.toEcWfB hp) pro_tr) ?_
  refine RelCT.seq (relInv (I' := fun σ s => EK L σ s ∧ bytesAt s.mem (pa s (sc oH)) 32 = H (ekE L σ) ∧
    s.gpr .r15 = 1) (fun σ s hp hs => hashEk_ok W hp hs) (hashEk_tr W)) ?_
  refine RelCT.seq (relInv (I' := EncI W₀.toEcWfB) (fun σ s hp hs => hashes_ok W₀.toEcWfB hp hs.1 hs.2.1 hs.2.2)
    (hashes_tr W₀)) ?_
  refine RelCT.seq (relInv (I' := EncO W₀) (fun σ s _ hs => Enc.encrypt_ok v K W₀.toKemWf (C := ekC W₀.toEcWfB σ) W₀.enc hs.1 hs.2)
    (encrypt_tr W₀ v K)) ?_
  refine RelCT.seq (relInv (I' := EKEnd L) (fun σ s _ hs => out_ok W₀ hs) (out_tr W₀)) ?_
  exact RelCT.mono epi_tr (fun _ _ h => h) fun _ _ _ => trivial

end VG.Proof.MlKem.X86_64
