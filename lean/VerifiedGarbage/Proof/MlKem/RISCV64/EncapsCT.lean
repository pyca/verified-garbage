module

public import VerifiedGarbage.Proof.MlKem.RISCV64.Encaps
import VerifiedGarbage.Proof.MlKem.RISCV64.EncryptCT
public import VerifiedGarbage.Proof.MlKem.RISCV64.HashCT

import VerifiedGarbage.Proof.MlKem.RISCV64.RowCT
import VerifiedGarbage.Proof.MlKem.RISCV64.CallsCT
import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.RelBlock
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Encaps
meta import VerifiedGarbage.Proof.MlKem.RISCV64.EncryptCT
meta import VerifiedGarbage.Proof.MlKem.RISCV64.HashCT
meta import VerifiedGarbage.Proof.MlKem.RISCV64.RowCT
meta import VerifiedGarbage.Proof.MlKem.RISCV64.CallsCT
meta import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelBlock
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MlKem.RISCV64.Encrypt

/-!
# ML-KEM on RISC-V: encapsulation, constant time and `Verified`

As on PPC64LE (`Proof/MlKem/PPC64LE/EncapsCT.lean`): two runs from states that
agree on the public data (the pointers, the stack pointer and `ρ` of `ek`,
which the contract lets the function leak) leak the same trace (`all_ct`),
phase by phase: the blocks by the taint analysis, from the pointers, or
because they access no memory; the hashes by `hash_ct`; and K-PKE.Encrypt by
`encrypt_ct`, whose `SampleNTT`s take the seeds of the same `ρ`. What each
run is at each point comes from its correctness (`Encaps.lean`).

All of it holds for any parameter set. Its `outcome` is the contract's,
which ML-KEM-768's `verified` (below) and ML-KEM-1024's use.
-/

@[expose] public section

namespace VG.Proof.MlKem.RISCV64.Encaps

open VG VG.RISCV64 VG.Impl.MlKem.RISCV64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.RISCV64.Enc

/-- Two runs, from states that agree on the public data. -/
structure Two (K : KemLay) (s₁ s₂ : State) : Prop where
  hp₁ : Pre K s₁
  hp₂ : Pre K s₂
  sp : s₁.sp = s₂.sp
  a0 : s₁.gpr .a0 = s₂.gpr .a0
  a1 : s₁.gpr .a1 = s₂.gpr .a1
  a2 : s₁.gpr .a2 = s₂.gpr .a2
  a3 : s₁.gpr .a3 = s₂.gpr .a3
  a4 : s₁.gpr .a4 = s₂.gpr .a4
  rho : ekRho K.p (EK K s₁) = ekRho K.p (EK K s₂)

section
variable {K : KemLay} {s₁ s₂ : State} (two : Two K s₁ s₂)
include two

theorem Two.layEq : lay s₂ K = lay s₁ K := by
  simp only [Encaps.lay, pScr, pEk, pKey, pCt, two.a0, two.a2, two.a3, two.a4, two.sp]

theorem Two.regs {a b : State} (ha : EnEnv K s₁ a) (hb : EnEnv K s₂ b) :
    ∀ r ∈ [Reg.s7, .s8, .s10, .s11], a.gpr r = b.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [ha.s7, hb.s7]; exact two.a3
  · rw [ha.s8, hb.s8]; exact two.a2
  · rw [ha.s10, hb.s10]; exact two.a0
  · rw [ha.ctx.s11, hb.ctx.s11, two.layEq]

theorem Two.sub' {rs : List Reg} {a b : State} (ha : EnEnv K s₁ a) (hb : EnEnv K s₂ b)
    (hs : ∀ r ∈ rs, r ∈ [Reg.s7, .s8, .s10, .s11] := by decide) : ∀ r ∈ rs, a.gpr r = b.gpr r :=
  fun r hr => two.regs ha hb r (hs r hr)

theorem Two.spE {a b : State} (ha : EnEnv K s₁ a) (hb : EnEnv K s₂ b) : a.sp = b.sp := by
  rw [ha.sp, hb.sp, two.sp]

theorem Two.hashOk {ins outs : List Piece} {a b : State} (ha : EnEnv K s₁ a) (hb : EnEnv K s₂ b)
    (hi : ∀ {s₀ s : State}, Pre K s₀ → EnEnv K s₀ s → ∀ p ∈ ins, PieceOk (lay s₀ K) eidx s false p)
    (ho : ∀ {s₀ s : State}, Pre K s₀ → EnEnv K s₀ s → ∀ p ∈ outs, PieceOk (lay s₀ K) eidx s true p) :
    HashOk (lay s₁ K) eidx ins outs a ∧ HashOk (lay s₁ K) eidx ins outs b ∧ a.sp = b.sp :=
  ⟨⟨ha.ctx, hi two.hp₁ ha, ho two.hp₁ ha⟩,
    by rw [← two.layEq]; exact ⟨hb.ctx, hi two.hp₂ hb, ho two.hp₂ hb⟩, two.spE ha hb⟩

theorem all_ct : RelCT isa (fun a b => a = s₁ ∧ b = s₂) K.encaps fun _ _ => True := by
  have hp₁ := two.hp₁
  have hp₂ := two.hp₂
  have hK := hp₁.wf
  -- the setup
  refine RelCT.seq (R := fun (a b : State) =>
      (EnEnv K s₁ a ∧ a.gpr .s9 = pM s₁ ∧ bytesAt a.mem ((layM s₁ K).A 2 0) 32 = M K s₁) ∧
      (EnEnv K s₂ b ∧ b.gpr .s9 = pM s₂ ∧ bytesAt b.mem ((layM s₂ K).A 2 0) 32 = M K s₂))
    (relct_wp (taint_block [.a0, .a1, .a2, .a3, .a4] (fun a b hab => by rw [hab.1, hab.2, two.sp])
      (fun a b hab r hr => by
        rw [hab.1, hab.2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact two.a0
        · exact two.a1
        · exact two.a2
        · exact two.a3
        · exact two.a4) (by taint_decide))
      fun a b hab => ⟨by rw [hab.1]; exact setup_ok hp₁, by rw [hab.2]; exact setup_ok hp₂⟩) ?_
  -- `m` copied
  refine RelCT.seq (R := fun (a b : State) =>
      (EnEnv K s₁ a ∧ bytesAt a.mem ((lay s₁ K).A 0 oMsg) 32 = M K s₁) ∧
      (EnEnv K s₂ b ∧ bytesAt b.mem ((lay s₂ K).A 0 oMsg) 32 = M K s₂))
    (relct_wp (taint_prog [.s9, .s11] (fun a b hab => two.spE hab.1.1 hab.2.1)
      (fun a b hab r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [hab.1.2.1, hab.2.2.1]; exact two.a1
        · exact two.regs hab.1.1 hab.2.1 .s11 (by simp)) (by taint_decide))
      fun a b hab => ⟨copyM_ok hp₁ hab.1.1 hab.1.2.1 hab.1.2.2,
        copyM_ok hp₂ hab.2.1 hab.2.2.1 hab.2.2.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => F4 K s₁ a ∧ F4 K s₂ b)
    (relct_wp (relct_noMem (by rfl)) fun a b hab =>
      ⟨s4_ok hp₁ hab.1.1 hab.1.2, s4_ok hp₂ hab.2.1 hab.2.2⟩) ?_
  -- `H(ek)`
  refine RelCT.seq (R := fun (a b : State) =>
      (F4 K s₁ a ∧ bytesAt a.mem ((lay s₁ K).A 0 oHek) 32 = H (EK K s₁)) ∧
      (F4 K s₂ b ∧ bytesAt b.mem ((lay s₂ K).A 0 oHek) 32 = H (EK K s₂)))
    (relct_wp (hash_ct (L := lay s₁ K) (idx := eidx) VG.Proof.MlKem.rate136 (by decide)
      (List.cons_ne_nil _ _) fun a b hab =>
        two.hashOk (ins := [⟨.s10, 0, K.ekLen⟩]) (outs := [⟨.s11, oHek, 32⟩]) hab.1.1 hab.2.1
        (fun hp h p hp' => by
          have hK := hp.wf
          rw [List.mem_singleton] at hp'; subst hp'
          exact pieceE hp h (.inl rfl) (by simp) (by show 0 < 32768; decide)
            (by show K.ekLen < 2048; have := hK.k4; simp only [KemLay.ekLen]; omega)
            (by show 0 < K.ekLen; simp only [KemLay.ekLen]; omega) (by edecide))
        (fun hp h p hp' => by
          have hK := hp.wf
          rw [List.mem_singleton] at hp'; subst hp'
          exact pieceE hp h (.inr rfl) (fun _ => rfl) (by decide) (by decide) (by decide) (by edecide)))
      fun a b hab => ⟨s5_ok hp₁ hab.1, s5_ok hp₂ hab.2⟩) ?_
  -- `G(m ‖ H(ek))`
  refine RelCT.seq (R := fun (a b : State) =>
      (F4 K s₁ a ∧ bytesAt a.mem ((lay s₁ K).A 0 oG) 32 = KK K s₁ ∧
        bytesAt a.mem ((lay s₁ K).A 0 oSigma) 32 = RR K s₁) ∧
      (F4 K s₂ b ∧ bytesAt b.mem ((lay s₂ K).A 0 oG) 32 = KK K s₂ ∧
        bytesAt b.mem ((lay s₂ K).A 0 oSigma) 32 = RR K s₂))
    (relct_wp (hash_ct (L := lay s₁ K) (idx := eidx) VG.Proof.MlKem.rate72 (by decide)
      (List.cons_ne_nil _ _) fun a b hab =>
        two.hashOk (ins := [⟨.s11, oMsg, 32⟩, ⟨.s11, oHek, 32⟩]) (outs := [⟨.s11, oG, 64⟩])
          hab.1.1.1 hab.2.1.1
        (fun hp h p hp' => by
          have hK := hp.wf
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
          rcases hp' with rfl | rfl
          · exact pieceE hp h (.inr rfl) (by simp) (by decide) (by decide) (by decide) (by edecide)
          · exact pieceE hp h (.inr rfl) (by simp) (by decide) (by decide) (by decide) (by edecide))
        (fun hp h p hp' => by
          have hK := hp.wf
          rw [List.mem_singleton] at hp'; subst hp'
          exact pieceE hp h (.inr rfl) (fun _ => rfl) (by decide) (by decide) (by decide) (by edecide)))
      fun a b hab => ⟨s6_ok hp₁ hab.1, s6_ok hp₂ hab.2⟩) ?_
  -- `K` into `key`
  refine RelCT.seq (R := fun (a b : State) =>
      (F4 K s₁ a ∧ bytesAt a.mem ((lay s₁ K).A 3 0) 32 = KK K s₁ ∧
        bytesAt a.mem ((lay s₁ K).A 0 oSigma) 32 = RR K s₁) ∧
      (F4 K s₂ b ∧ bytesAt b.mem ((lay s₂ K).A 3 0) 32 = KK K s₂ ∧
        bytesAt b.mem ((lay s₂ K).A 0 oSigma) 32 = RR K s₂))
    (relct_wp (taint_prog [.s8, .s11] (fun a b hab => two.spE hab.1.1.1 hab.2.1.1)
      (fun a b hab => two.sub' hab.1.1.1 hab.2.1.1) (by taint_decide))
      fun a b hab => ⟨s7_ok hp₁ hab.1, s7_ok hp₂ hab.2⟩) ?_
  -- K-PKE.Encrypt, and the end
  refine RelCT.seq (R := fun (a b : State) => EnEnv K s₁ a ∧ EnEnv K s₂ b)
    (relct_wp (RelCT.pointwise fun x y hxy => ?_) fun a b hab =>
      ⟨WP.mono (s8_ok hp₁ hab.1) fun _ h => h.1, WP.mono (s8_ok hp₂ hab.2) fun _ h => h.1⟩)
    (taint_block [.s11] (fun a b hab => two.spE hab.1 hab.2)
      (fun a b hab => two.sub' hab.1 hab.2) (by taint_decide))
  have ey : EncPre K (lay s₁ K) eb y := by rw [← two.layEq]; exact encPre hp₂ hxy.2.1.1 hxy.2.1.2.1
  refine encrypt_ct (encPre hp₁ hxy.1.1.1 hxy.1.1.2.1) ey ?_
  show ekRho K.p (bytesAt x.mem ((lay s₁ K).A 2 0) K.ekLen) =
    ekRho K.p (bytesAt y.mem ((lay s₁ K).A 2 0) K.ekLen)
  have e₂ : bytesAt y.mem ((lay s₁ K).A 2 0) K.ekLen = EK K s₂ := by
    rw [← two.layEq]; exact hxy.2.1.1.ek
  rw [hxy.1.1.1.ek, e₂]; exact two.rho

end

/-! ## The outcome -/

theorem outcome {K : KemLay} (hK : K.WF) (s₀ : State) :
    Outcome (fun iters => encapsInternal K.p iters (EK K s₀) (M K s₀))
      (if okEnc K.k (ekRho K.p (EK K s₀)) K.k then 1 else 0)
      (KK K s₀,
        VG.Proof.MlKem.KPke.ct K.p (aEnc (ekRho K.p (EK K s₀)) (RR K s₀)) (EK K s₀) (M K s₀)
          (RR K s₀)) := by
  refine VG.Proof.MlKem.outcome_of_min ?_
  rw [show minIterations = 280 from rfl]
  cases hk : okEnc K.k (ekRho K.p (EK K s₀)) K.k
  · obtain ⟨i, hi, j, hj, hn⟩ := enc_none hk
    refine .inr ⟨rfl, ?_⟩
    rw [VG.Proof.MlKem.KPke.encapsInternal_eq, VG.Proof.MlKem.KPke.kpkeEncrypt_none hi hj hn]; rfl
  · refine .inl ⟨rfl, ?_⟩
    rw [VG.Proof.MlKem.KPke.encapsInternal_eq,
      VG.Proof.MlKem.KPke.kpkeEncrypt_some ⟨hK.η₁, hK.η₂⟩ (enc_some (r := RR K s₀) hk)]
    rfl

theorem EK_eq (K : KemLay) (s₀ : State) : EK K s₀ = bytesAt s₀.mem (s₀.gpr .a0) K.ekLen := by
  simp only [EK, Lay.A, BitVec.add_zero]; rfl

theorem M_eq (K : KemLay) (s₀ : State) : M K s₀ = bytesAt s₀.mem (s₀.gpr .a1) 32 := by
  simp only [M, Lay.A, BitVec.add_zero]; rfl

/-! ## ML-KEM-768 -/

theorem pre_of {s : State} (h : (Spec.MlKem.encapsContract RISCV64.abi 1168).pre s) : Pre kl768 s := by
  sig_pre [Spec.MlKem.encapsContract, Spec.MlKem.encapsSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨al, h0, h1, h2, d1, d2, d3, d4, d5, d6, d7, d8, d9, b1, b2, b3, b4, b5,
    f1, f2, f3, f4, f5, alS⟩ := h
  exact ⟨kl768_wf, kl768_calls, al, h0, h1, h2, d1, d2, d3, d4, d5, d6, d7, d8, d9, b1, b2, b3, b4,
    b5, f1, f2, f3, f4, f5, alS⟩

theorem post_of {s₀ s : State}
    (h3 : s.gpr .a0 = if okEnc kl768.k (ekRho kl768.p (EK kl768 s₀)) kl768.k then 1 else 0)
    (hkey : bytesAt s.mem (pKey s₀) 32 = KK kl768 s₀)
    (hct : bytesAt s.mem (pCt s₀) 1088 = VG.Proof.MlKem.KPke.ct kl768.p
      (aEnc (ekRho kl768.p (EK kl768 s₀)) (RR kl768 s₀)) (EK kl768 s₀) (M kl768 s₀) (RR kl768 s₀)) :
    (Spec.MlKem.encapsContract RISCV64.abi 1168).post s₀ s := by
  sig_post [Spec.MlKem.encapsContract, Spec.MlKem.encapsSig, RISCV64.abi, RISCV64.argRegs]
  have e : BitVec.setWidth 32
      (if okEnc kl768.k (ekRho kl768.p (EK kl768 s₀)) kl768.k then (1 : BitVec 64) else 0) =
      if okEnc kl768.k (ekRho kl768.p (EK kl768 s₀)) kl768.k then 1 else 0 := by
    cases okEnc kl768.k (ekRho kl768.p (EK kl768 s₀)) kl768.k <;> rfl
  have e0 : bytesAt s₀.mem (s₀.gpr .a0) 1184 = EK kl768 s₀ := (EK_eq kl768 s₀).symm
  have e1 : bytesAt s₀.mem (s₀.gpr .a1) 32 = M kl768 s₀ := (M_eq kl768 s₀).symm
  rw [h3, e, hkey, hct, e0, e1]
  exact outcome kl768_wf s₀

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a3 => 0x4000 | .a4 => 0x10000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 1184⟩, ⟨0x2000, 32⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x4000, 1088⟩, ⟨0x10000, 32768⟩]

theorem verified :
    Verified RISCV64.target Impl.MlKem.RISCV64.encaps (Spec.MlKem.encapsContract RISCV64.abi 1168) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hlr, h3, hkey, hct⟩ := correct (pre_of hs)
    exact ⟨t, s', he, ⟨hpres, hsp, hlr⟩, post_of h3 hkey hct⟩
  · have hp₁ := pre_of h₁
    have hp₂ := pre_of h₂
    sig_pub [Spec.MlKem.encapsContract, Spec.MlKem.encapsSig, RISCV64.abi, RISCV64.argRegs] at hpub
    obtain ⟨hsp, hl, g3, g4, g5, g6, g7⟩ := hpub
    have hr : ekRho kl768.p (EK kl768 s₁) = ekRho kl768.p (EK kl768 s₂) := by
      rw [EK_eq, EK_eq]
      unfold leakRho at hl
      exact (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hl
    exact (all_ct ⟨hp₁, hp₂, hsp, g3, g4, g5, g6, g7, hr⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.MlKem.encapsContract, Spec.MlKem.encapsSig, RISCV64.abi, RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | decide +kernel

end VG.Proof.MlKem.RISCV64.Encaps
