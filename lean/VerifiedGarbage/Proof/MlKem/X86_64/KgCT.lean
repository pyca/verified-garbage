module

public import VerifiedGarbage.Proof.MlKem.X86_64.KgB
meta import VerifiedGarbage.Proof.MlKem.X86_64.KgB
import Mathlib.Tactic.Conv
meta import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.MlKem.X86_64.FragL
meta import VerifiedGarbage.Proof.MlKem.X86_64.FragL
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
import VerifiedGarbage.Proof.MlKem.X86_64.FragEM
import VerifiedGarbage.Proof.MlKem.X86_64.KgMulV
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
meta import VerifiedGarbage.Proof.MlKem.X86_64.FragEM
meta import VerifiedGarbage.Proof.MlKem.X86_64.KgMulV
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
# ML-KEM on x86-64: key generation, constant time of the pieces

Two runs from entry states that agree on the public data (`keyGenK.pub`: the
pointers, the stack pointer and `ρ`), each at the same step with its invariant
(`Rel2`), are in the same layout (`kc_lrel`), and each piece leaks the same in
both (`gRho_tr`, `samples_tr`, `se_tr`, `kgm_tr`, `encT_tr`, `encS_tr`, `fin_tr`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- A piece's constant time in a relation implied by the invariants of two runs. -/
theorem rel2_of {Pre : State → Prop} {Pub : State → State → Prop} {I : State → State → Prop} {c : Prog isa}
    {Q : State → State → Prop} (htr : RelCT isa Q c fun _ _ => True)
    (h : ∀ σ₁ σ₂ x y, Pre σ₁ → Pre σ₂ → Pub σ₁ σ₂ → I σ₁ x → I σ₂ y → Q x y) :
    RelCT isa (Rel2 Pre Pub I) c fun _ _ => True :=
  RelCT.mono htr (fun _ _ ⟨_, _, p₁, p₂, hpub, i₁, i₂⟩ => h _ _ _ _ p₁ p₂ hpub i₁ i₂) fun _ _ h => h

namespace KeyGen

open VG.Impl.MlKem.X86_64.KeyGen

section

variable {L : Kem} (W : KgWfB L)
include W

theorem kc_lrel {σ₁ σ₂ x y : State} (p₁ : (keyGenK L).pre σ₁) (p₂ : (keyGenK L).pre σ₂) (pub : (keyGenK L).pub σ₁ σ₂)
    (h₁ : KC σ₁ x) (h₂ : KC σ₂ y) : LRel kgR (kgW L) x y := by
  obtain ⟨e1, e2, e3, e4, e5, _⟩ := pub
  refine ⟨h₁.lay W p₁, h₂.lay W p₂, fa4 ?_ ?_ ?_ ?_, by rw [h₁.top.rsp, h₂.top.rsp, e5]⟩
  · rw [h₁.top.regs (.rbp, .rdi) (by decide), h₂.top.regs (.rbp, .rdi) (by decide), e1]
  · rw [h₁.top.regs (.rbx, .rcx) (by decide), h₂.top.regs (.rbx, .rcx) (by decide), e4]
  · rw [h₁.top.regs (.r12, .rsi) (by decide), h₂.top.regs (.r12, .rsi) (by decide), e2]
  · rw [h₁.top.regs (.r13, .rdx) (by decide), h₂.top.regs (.r13, .rdx) (by decide), e3]

omit W in
theorem rho_pub {σ₁ σ₂ : State} (pub : (keyGenK L).pub σ₁ σ₂) : rhoK L σ₁ = rhoK L σ₂ := pub.2.2.2.2.2

/-! ## `G` -/

theorem gRho_trL : RelCT isa (LRel kgR (kgW L)) (gRho L) fun _ _ => True := by
  unfold gRho
  refine RelCT.seq (LRel.step (kgB_bases L) (taintRel [.rbx] (fun x y h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.eq (p := sc 0) (l := 1) W.inBs.1) W.nbT)
    fun x Lx => WP.mono (setB_okL Lx (by decide) (by have := W.k; omega) (p := sc oNB) (v := L.k) W.nb)
      fun _ h => ⟨_, h.1⟩) (RelCT.seq (LRel.step (kgB_bases L) (hash_tr (kgB_bases L)
        (ps := [((.rbp, 0), 32), (sc oNB, 1)]) (rate := 72) (out := sc oG) (len := 64) W.gH (show 6 < 256 by decide))
    fun x Lx => WP.mono (hash_ok (kgB_bases L) (ps := [((.rbp, 0), 32), (sc oNB, 1)]) (rate := 72) (out := sc oG)
      (len := 64) W.gH (show 6 < 256 by decide) Lx) fun _ h => ⟨_, h.1⟩)
    (taintRel [.rbx] (fun x y h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.eq (p := sc 0) (l := 1) W.inBs.1) (by taint_decide)))

theorem gRho_tr : RelCT isa (Rel2 (keyGenK L).pre (keyGenK L).pub fun σ s => KC σ s ∧ s.gpr .r15 = 1) (gRho L)
    fun _ _ => True :=
  rel2_of (gRho_trL W) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => kc_lrel W p₁ p₂ pub h₁.1 h₂.1

/-! ## The matrix -/

theorem fin_trL : RelCT isa (LRel kgR (kgW L)) (fin L) fun _ _ => True := by
  unfold fin
  have tr : ∀ {c : Prog isa} {h : VG.Taint.Hint X86_64.Taint.T},
      (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13]) c h).isSome = true →
      RelCT isa (LRel kgR (kgW L)) c fun _ _ => True := fun ht => taintRel [.rbx, .rbp, .r12, .r13] (fun x y h =>
    fa4 (h.eq (p := sc 0) (l := 1) W.inBs.1) (h.eq (p := (.rbp, 0)) (l := 1) rfl)
      (h.eq (p := (.r12, 0)) (l := 1) W.inBs.2.1) (h.eq (p := (.r13, 0)) (l := 1) W.inBs.2.2)) ht
  obtain ⟨_, t₁⟩ := W.finT₁
  obtain ⟨_, t₂⟩ := W.finT₂
  obtain ⟨_, t₄⟩ := W.finT₄
  refine RelCT.seq (LRel.step (kgB_bases L) (tr t₁) fun x Lx =>
      WP.mono (copy_okL Lx (dst := (.r12, 384 * L.k)) (src := sc oG) (n := 32) (by decide) W.f₁)
        fun _ h => ⟨_, h.1⟩)
    (RelCT.seq (LRel.step (kgB_bases L) (tr t₂) fun x Lx =>
      WP.mono (copy_okL Lx (dst := (.r13, 384 * L.k)) (src := (.r12, 0)) (n := L.ekLen) (by decide) W.f₂)
        fun _ h => ⟨_, h.1⟩)
    (RelCT.seq (LRel.step (kgB_bases L) (hash_tr (kgB_bases L) (ps := [((.r12, 0), L.ekLen)]) (rate := 136)
      (out := (.r13, 384 * L.k + L.ekLen)) (len := 32) W.f₃ (show 6 < 256 by decide)) fun x Lx =>
      WP.mono (hash_ok (kgB_bases L) (ps := [((.r12, 0), L.ekLen)]) (rate := 136) (out := (.r13, 384 * L.k + L.ekLen))
        (len := 32) W.f₃ (show 6 < 256 by decide) Lx) fun _ h => ⟨_, h.1⟩)
    (tr t₄)))

theorem fin_tr {I : State → State → Prop} (hI : ∀ {σ s}, I σ s → KC σ s) :
    RelCT isa (Rel2 (keyGenK L).pre (keyGenK L).pub I) (fin L) fun _ _ => True :=
  rel2_of (fin_trL W) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => kc_lrel W p₁ p₂ pub (hI h₁) (hI h₂)

end

section

variable {L : Kem} (W : KgWf L)
include W

theorem sample_tr {e : Nat} (he : e < L.k * L.k) (he' : 4 * (L.k * L.k / 4) ≤ e) :
    RelCT isa (Rel2 (keyGenK L).pre (keyGenK L).pub (KB L e)) (sampleIJ (pS (L.pA + e)) (e / L.k) (e % L.k))
      fun _ _ => True := by
  have hc := W.kb e he he'
  simp only [kbChk, Bool.and_eq_true] at hc
  have hk := W.k
  exact rel2_of (sampleIJ_tr (kgB_bases L) rbx_na (by have := div_lt_k he; omega) (by have := mod_lt_k he; omega)
      hc.1.1.1.1.1 (W.ijT e he))
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨kc_lrel W p₁ p₂ pub h₁.a.kc h₂.a.kc, by rw [h₁.a.sb, h₂.a.sb]; exact rho_pub pub⟩

theorem quad_trK (v : Sample4Impl) {q : Nat} (hq : q < L.k * L.k / 4) :
    RelCT isa (Rel2 (keyGenK L).pre (keyGenK L).pub (KB L (4 * q)))
      (quad v.callee L.k (4 * q) (pS (L.pA + 4 * q)) (pS L.pW)) fun _ _ => True := by
  have hc := W.kq q hq
  simp only [kqChk, Bool.and_eq_true] at hc
  have hk := W.k
  have h16 : L.k * L.k ≤ 16 := Nat.mul_le_mul hk.2 hk.2
  exact rel2_of (RelCT.exists_ fun ρ => quad_tr (ρ := ρ) v (kgB_bases L) (by omega)
      (fun t ht => ⟨by have := div_lt_k (show 4 * q + t < L.k * L.k by omega); omega,
        by have := mod_lt_k (show 4 * q + t < L.k * L.k by omega); omega⟩) hc.1.1.1.1.1)
    fun σ₁ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨KPke.kgRho L.p (kgD σ₁), kc_lrel W p₁ p₂ pub h₁.a.kc h₂.a.kc,
      ⟨h₁.a.sb, fun _ h => absurd h (Nat.not_lt_zero _)⟩,
      ⟨h₂.a.sb.trans (rho_pub pub).symm, fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩

theorem samples_tr (v : Sample4Impl) : RelCT isa (Rel2 (keyGenK L).pre (keyGenK L).pub (KB L 0)) (L.samples v.callee)
    (Rel2 (keyGenK L).pre (keyGenK L).pub (KB L (L.k * L.k))) :=
  samples_tr' L v.callee (R := fun e => Rel2 (keyGenK L).pre (keyGenK L).pub (KB L e))
    (fun _ he he' => relInv (fun _ _ hp hs => sample_step W hp he he' hs) (sample_tr W he he'))
    (fun _ hq => relInv (fun _ _ hp hs => quad_step v W hp hq hs) (quad_trK W v hq))

/-! ## `ŝ` and `ê` -/

theorem prfs_trK (v : Sample4Impl) :
    RelCT isa (Rel2 (keyGenK L).pre (keyGenK L).pub (KRest0 L)) (v.callee.prfs 0 (2 * L.k) L.oPR L.lPW)
      fun _ _ => True := by
  have hc := W.prfs
  simp only [prfsKChk, Bool.and_eq_true] at hc
  exact rel2_of (v.prfs_tr (kgB_bases L) (by have := W.k; omega) hc.1.1.1.1) fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
    kc_lrel W p₁ p₂ pub h₁.kc h₂.kc

theorem se_tr {A : Arith} (hA : ArithOk A) {N : Nat} (hN : N < 2 * L.k) :
    RelCT isa (Rel2 (keyGenK L).pre (keyGenK L).pub (KRest L N 0 0)) (se L A N) fun _ _ => True := by
  have hc := W.se N hN
  simp only [seChk, Bool.and_eq_true] at hc
  unfold se
  exact rel2_of (cbd2At_trL hA rbx_na hc.1) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => kc_lrel W p₁ p₂ pub h₁.kc h₂.kc

/-! ## `ŝ` and `t̂` -/

theorem kgm_tr {A : Arith} (hA : ArithOk A) :
    RelCT isa (Rel2 (keyGenK L).pre (keyGenK L).pub (KRest L (2 * L.k) 0 0))
      (L.kgMulAt A (pS L.pU) (pS 0) (pS L.pA) (pS L.k) (pS L.pZ)) fun _ _ => True := by
  have red : ∀ {σ s : State}, KRest L (2 * L.k) 0 0 σ s → VecReduced s.mem (pa s (pS 0)) L.k ∧
      VecReduced s.mem (pa s (pS L.pA)) (L.k * L.k) ∧ VecReduced s.mem (pa s (pS L.k)) L.k := fun h =>
    ⟨fun j hj => by rw [pS_add, Nat.zero_add]; exact (h.se j (by omega)).1,
      fun e he => by rw [pS_add]; exact (h.mat e he).1,
      fun i hi => by rw [pS_add]; exact (h.se (L.k + i) (by omega)).1⟩
  exact rel2_of (kgMulAt_trL hA W.k34 rbx_na rbx_na rbx_na rbx_na W.km) fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
    ⟨kc_lrel W p₁ p₂ pub h₁.kc h₂.kc, red h₁, red h₂⟩

/-! ## The rows of `ek` -/

theorem encT_tr {A : Arith} (hA : ArithOk A) {i : Nat} (hi : i < L.k) :
    RelCT isa (Rel2 (keyGenK L).pre (keyGenK L).pub (KRestT L i 0)) (encT L A i) fun _ _ => True := by
  have hc := W.encT i hi
  simp only [encTChk, Bool.and_eq_true] at hc
  exact rel2_of (enc12At_trL hA r12_na hc.1) fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
    ⟨kc_lrel W p₁ p₂ pub h₁.kc h₂.kc, (h₁.that i hi).1, (h₂.that i hi).1⟩

/-! ## The rows of `dk` -/

theorem encS_tr {A : Arith} (hA : ArithOk A) {j : Nat} (hj : j < L.k) :
    RelCT isa (Rel2 (keyGenK L).pre (keyGenK L).pub (KRestT L L.k j)) (encS A j) fun _ _ => True := by
  have hc := W.encS j hj
  simp only [encSChk, Bool.and_eq_true] at hc
  exact rel2_of (enc12At_trL hA r13_na hc.1) fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
    ⟨kc_lrel W p₁ p₂ pub h₁.kc h₂.kc, (h₁.shat j hj).1, (h₂.shat j hj).1⟩

/-! ## The rest of the keys -/

end

end KeyGen

end VG.Proof.MlKem.X86_64
