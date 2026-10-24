module

public import VerifiedGarbage.Proof.MlKem.PPC64LE.KeyGen
public import VerifiedGarbage.Proof.MlKem.PPC64LE.RowCT

import VerifiedGarbage.Proof.MlKem.PPC64LE.HashCT
import VerifiedGarbage.Proof.MlKem.PPC64LE.PrfCT
import VerifiedGarbage.Proof.MlKem.PPC64LE.CallsCT
import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.KeyGen
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.RowCT
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.HashCT
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.PrfCT
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.CallsCT
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on PPC64LE: key generation in constant time

As on 32-bit ARM (`Proof/MlKem/Arm/KeyGenCT.lean`): two runs from states that
agree on the public data (the pointers, the stack pointer and `ρ`, which the
contract lets the function leak, since `ek` publishes it) leak the same trace
(`all_ct`), phase by phase: the blocks by the taint analysis, from the
pointers, or because they access no memory (`relct_noMem`); the hashes by
`hash_ct`; the `PRF`s by `prfLoop_ct`; the rows of `t̂` by `rowSum_ct`, whose
`SampleNTT`s take the same seeds in both runs; and the calls of the
primitives on the same pointers (`RelCT.callT`). What each run is at each
point comes from its correctness (`KeyGen.lean`).

All of it holds for any parameter set: the taint analyses of the blocks whose
immediates depend on it are facts of `KemLay.CallsOk`, which the parameter set
checks by evaluation.
-/

@[expose] public section

namespace VG.Proof.MlKem.PPC64LE.KeyGen

open VG VG.PPC64LE VG.Impl.MlKem.PPC64LE
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.PPC64LE.Sample (taint_block relct_wp)

/-- Two runs, from states that agree on the public data. -/
structure Two (K : KemLay) (s₁ s₂ : State) : Prop where
  hp₁ : Pre K s₁
  hp₂ : Pre K s₂
  sp : s₁.sp = s₂.sp
  r3 : s₁.gpr .r3 = s₂.gpr .r3
  r4 : s₁.gpr .r4 = s₂.gpr .r4
  r5 : s₁.gpr .r5 = s₂.gpr .r5
  r6 : s₁.gpr .r6 = s₂.gpr .r6
  rho : ρ₀ K s₁ = ρ₀ K s₂

section
variable {K : KemLay} {s₁ s₂ : State} (two : Two K s₁ s₂)
include two

theorem Two.lay : lay s₂ K = lay s₁ K := by
  simp only [KeyGen.lay, pSeed, pEk, pDk, pScr, two.r3, two.r4, two.r5, two.r6, two.sp]

/-- The registers that hold pointers are the same in both runs. -/
theorem Two.regs {a b : State} (ha : KEnv K s₁ a) (hb : KEnv K s₂ b) :
    ∀ r ∈ [Reg.r28, .r29, .r30, .r31], a.gpr r = b.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [ha.r28, hb.r28]; exact two.r5
  · rw [ha.r29, hb.r29]; exact two.r4
  · rw [ha.r30, hb.r30]; exact two.r3
  · rw [ha.ctx.r31, hb.ctx.r31, two.lay]

theorem Two.sub {rs : List Reg} (hs : ∀ r ∈ rs, r ∈ [Reg.r28, .r29, .r30, .r31]) {a b : State}
    (ha : KEnv K s₁ a) (hb : KEnv K s₂ b) : ∀ r ∈ rs, a.gpr r = b.gpr r :=
  fun r hr => two.regs ha hb r (hs r hr)

theorem Two.spE {a b : State} (ha : KEnv K s₁ a) (hb : KEnv K s₂ b) : a.sp = b.sp := by
  rw [ha.sp, hb.sp, two.sp]

/-! ## The rows of `t̂` -/

theorem kgRow_ct {i : Nat} (hi : i < K.k) :
    RelCT isa (fun a b => KRow K s₁ i a ∧ KRow K s₂ i b) K.kgRowBody fun a b =>
      (KRow K s₁ (i + 1) a ∧ (a.gpr .r0 != 0) = decide (i + 1 ≠ K.k)) ∧
      (KRow K s₂ (i + 1) b ∧ (b.gpr .r0 != 0) = decide (i + 1 ≠ K.k)) := by
  refine RelCT.pointwise fun x y ⟨hx, hy⟩ => ?_
  have hp₁ := two.hp₁
  have hp₂ := two.hp₂
  have py : RowPre K (lay s₁ K) (ρ₀ K s₁) (sK K s₂) i (okK K s₂ i) y := by
    have := hy.rowPre hp₂ hi; rwa [two.lay, ← two.rho] at this
  -- `RowSum`
  refine RelCT.seq (R := fun (a b : State) =>
      RowInv K (lay s₁ K) false (ρ₀ K s₁) (sK K s₁) i (okK K s₁ i) x K.k a ∧
      RowInv K (lay s₂ K) false (ρ₀ K s₂) (sK K s₂) i (okK K s₂ i) y K.k b)
    (relct_wp (rowSum_ct hp₁.calls (hx.rowPre hp₁ hi) py) fun a b hab =>
      ⟨by rw [hab.1]; exact rowSum_ok (hx.rowPre hp₁ hi),
        by rw [hab.2]; exact rowSum_ok (hy.rowPre hp₂ hi)⟩) ?_
  -- `t̂[i] += ê[i]`
  refine RelCT.seq (R := fun (a b : State) => KR2 K s₁ i x a ∧ KR2 K s₂ i y b)
    (relct_wp (relct_noMem (by rfl)) fun a b hab => ⟨kr2_ok hp₁ hi hx hab.1, kr2_ok hp₂ hi hy hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => KR3 K s₁ i x a ∧ KR3 K s₂ i y b)
    (relct_wp (RelCT.callT addT (regs2 fun a b hab =>
      ⟨by rw [hab.1.kx.sp, hab.2.kx.sp, hx.env.sp, hy.env.sp, two.sp],
        by rw [hab.1.r3, hab.2.r3, two.lay], by rw [hab.1.r4, hab.2.r4, two.lay]⟩))
      fun a b hab => ⟨kr3_ok hp₁ hi hx hab.1, kr3_ok hp₂ hi hy hab.2⟩) ?_
  -- its encoding
  refine RelCT.seq (R := fun (a b : State) => KR4 K s₁ i x a ∧ KR4 K s₂ i y b)
    (relct_wp (relct_noMem (by rfl)) fun a b hab => ⟨kr4_ok hp₁ hx hab.1, kr4_ok hp₂ hy hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => KR5 K s₁ i x a ∧ KR5 K s₂ i y b)
    (relct_wp (RelCT.callT encode12T (regs2 fun a b hab =>
      ⟨by rw [hab.1.r3.kx.sp, hab.2.r3.kx.sp, hx.env.sp, hy.env.sp, two.sp],
        by rw [hab.1.a3, hab.2.a3, two.lay], by rw [hab.1.a4, hab.2.a4, two.lay]⟩))
      fun a b hab => ⟨kr5_ok hp₁ hi hx hab.1, kr5_ok hp₂ hi hy hab.2⟩) ?_
  exact relct_wp (relct_noMem (by rfl)) fun a b hab => ⟨kr6_ok hp₁ hi hx hab.1, kr6_ok hp₂ hi hy hab.2⟩

/-! ## `ŝ` into `dk` -/

theorem kgS_ct {j : Nat} (hj : j < K.k) :
    RelCT isa (fun a b => KS K s₁ j a ∧ KS K s₂ j b) K.kgSBody fun a b =>
      (KS K s₁ (j + 1) a ∧ (a.gpr .r0 != 0) = decide (j + 1 ≠ K.k)) ∧
      (KS K s₂ (j + 1) b ∧ (b.gpr .r0 != 0) = decide (j + 1 ≠ K.k)) := by
  refine RelCT.pointwise fun x y ⟨hx, hy⟩ => ?_
  have hp₁ := two.hp₁
  have hp₂ := two.hp₂
  refine RelCT.seq (R := fun (a b : State) => KS1 K s₁ j x a ∧ KS1 K s₂ j y b)
    (relct_wp (relct_noMem (by rfl)) fun a b hab => ⟨by rw [hab.1]; exact ks1_ok hp₁ hj hx,
      by rw [hab.2]; exact ks1_ok hp₂ hj hy⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => KS2 K s₁ j x a ∧ KS2 K s₂ j y b)
    (relct_wp (RelCT.callT encode12T (regs2 fun a b hab =>
      ⟨by rw [hab.1.o.sp, hab.2.o.sp, hx.env.sp, hy.env.sp, two.sp],
        by rw [hab.1.a3, hab.2.a3, two.lay], by rw [hab.1.a4, hab.2.a4, two.lay]⟩))
      fun a b hab => ⟨ks2_ok hp₁ hj hx hab.1, ks2_ok hp₂ hj hy hab.2⟩) ?_
  exact relct_wp (relct_noMem (by rfl)) fun a b hab => ⟨ks3_ok hp₁ hj hx hab.1, ks3_ok hp₂ hj hy hab.2⟩

/-! ## The whole function -/

theorem all_ct : RelCT isa (fun a b => a = s₁ ∧ b = s₂) K.keygen fun _ _ => True := by
  have hp₁ := two.hp₁
  have hp₂ := two.hp₂
  have hK := hp₁.wf
  -- the setup
  refine RelCT.seq (R := fun (a b : State) =>
      (KEnv K s₁ a ∧ a.mem ((lay s₁ K).A 0 oK) = BitVec.ofNat 8 K.k) ∧
      (KEnv K s₂ b ∧ b.mem ((lay s₂ K).A 0 oK) = BitVec.ofNat 8 K.k))
    (relct_wp (hp₁.calls.kgSetupT.relct (fun a b hab => by rw [hab.1, hab.2, two.sp])
      (fun a b hab r hr => by
        rw [hab.1, hab.2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact two.r3
        · exact two.r4
        · exact two.r5
        · exact two.r6))
      fun a b hab => ⟨by rw [hab.1]; exact setup_ok hp₁, by rw [hab.2]; exact setup_ok hp₂⟩) ?_
  -- `G(d ‖ k)`
  refine RelCT.seq (R := fun (a b : State) =>
      (KEnv K s₁ a ∧ bytesAt a.mem ((lay s₁ K).A 0 oG) 32 = VG.Proof.MlKem.KPke.kgRho K.p (D s₁) ∧
        bytesAt a.mem ((lay s₁ K).A 0 oSigma) 32 = VG.Proof.MlKem.KPke.kgSigma K.p (D s₁)) ∧
      (KEnv K s₂ b ∧ bytesAt b.mem ((lay s₂ K).A 0 oG) 32 = VG.Proof.MlKem.KPke.kgRho K.p (D s₂) ∧
        bytesAt b.mem ((lay s₂ K).A 0 oSigma) 32 = VG.Proof.MlKem.KPke.kgSigma K.p (D s₂)))
    (relct_wp (hash_ct (L := lay s₁ K) (idx := kidx) VG.Proof.MlKem.rate72 (by decide)
      (List.cons_ne_nil _ _) fun a b hab => ⟨⟨hab.1.1.ctx, g_ins hp₁ hab.1.1, g_outs hp₁ hab.1.1⟩,
        by rw [← two.lay]; exact ⟨hab.2.1.ctx, g_ins hp₂ hab.2.1, g_outs hp₂ hab.2.1⟩,
        two.spE hab.1.1 hab.2.1⟩)
      fun a b hab => ⟨g_ok hp₁ hab.1.1 hab.1.2, g_ok hp₂ hab.2.1 hab.2.2⟩) ?_
  -- `ρ`
  refine RelCT.seq (R := fun (a b : State) =>
      (KEnv K s₁ a ∧ bytesAt a.mem ((lay s₁ K).A 0 oSeed) 32 = VG.Proof.MlKem.KPke.kgRho K.p (D s₁) ∧
        bytesAt a.mem ((lay s₁ K).A 0 oSigma) 32 = VG.Proof.MlKem.KPke.kgSigma K.p (D s₁)) ∧
      (KEnv K s₂ b ∧ bytesAt b.mem ((lay s₂ K).A 0 oSeed) 32 = VG.Proof.MlKem.KPke.kgRho K.p (D s₂) ∧
        bytesAt b.mem ((lay s₂ K).A 0 oSigma) 32 = VG.Proof.MlKem.KPke.kgSigma K.p (D s₂)))
    (relct_wp (taint_prog [.r31] (fun a b hab => two.spE hab.1.1 hab.2.1)
      (fun a b hab => two.sub (by simp) hab.1.1 hab.2.1) (by taint_decide))
      fun a b hab => ⟨rho_ok hp₁ hab.1.1 hab.1.2.1 hab.1.2.2,
        rho_ok hp₂ hab.2.1 hab.2.2.1 hab.2.2.2⟩) ?_
  -- the `PRF`s
  refine RelCT.seq (R := fun (a b : State) =>
      (KEnv K s₁ a ∧ bytesAt a.mem ((lay s₁ K).A 0 oSeed) 32 = VG.Proof.MlKem.KPke.kgRho K.p (D s₁) ∧
        ∀ N < 2 * K.k, PolyIs a.mem ((lay s₁ K).A 0 (oPoly (K.k + N)))
          (ntt (VG.Proof.MlKem.cbd (VG.Proof.MlKem.KPke.kgSigma K.p (D s₁)) N))) ∧
      (KEnv K s₂ b ∧ bytesAt b.mem ((lay s₂ K).A 0 oSeed) 32 = VG.Proof.MlKem.KPke.kgRho K.p (D s₂) ∧
        ∀ N < 2 * K.k, PolyIs b.mem ((lay s₂ K).A 0 (oPoly (K.k + N)))
          (ntt (VG.Proof.MlKem.cbd (VG.Proof.MlKem.KPke.kgSigma K.p (D s₂)) N))))
    (relct_wp (RelCT.pointwise fun x y hxy =>
      prfLoop_ct hK (L := lay s₁ K) true (by have := hK.k1; omega) (by omega) hxy.1.1.ctx
        (by rw [← two.lay]; exact hxy.2.1.ctx) rfl rfl)
      fun a b hab => ⟨prf_phase hp₁ hab.1.1 hab.1.2.1 hab.1.2.2,
        prf_phase hp₂ hab.2.1 hab.2.2.1 hab.2.2.2⟩) ?_
  -- the rows of `t̂`
  refine RelCT.seq (R := fun (a b : State) => KRow K s₁ 0 a ∧ KRow K s₂ 0 b)
    (relct_wp (relct_noMem (by rfl)) fun a b hab =>
      ⟨rows_init hp₁ hab.1.1 hab.1.2.1 hab.1.2.2, rows_init hp₂ hab.2.1 hab.2.2.1 hab.2.2.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => KRow K s₁ K.k a ∧ KRow K s₂ K.k b)
    (relct_loop_nz (N := K.k) hK.k1 fun i hi => kgRow_ct two hi) ?_
  -- `ŝ` into `dk`
  refine RelCT.seq (R := fun (a b : State) => KS K s₁ 0 a ∧ KS K s₂ 0 b)
    (relct_wp (relct_noMem (by rfl)) fun a b hab => ⟨s_init hp₁ hab.1, s_init hp₂ hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => KEnv K s₁ a ∧ KEnv K s₂ b)
    (RelCT.mono (relct_loop_nz (N := K.k) hK.k1 fun j hj => kgS_ct two hj) (fun _ _ h => h)
      fun _ _ h => ⟨h.1.env, h.2.env⟩) ?_
  -- the end
  refine RelCT.seq (R := fun (a b : State) => KEnv K s₁ a ∧ KEnv K s₂ b)
    (relct_wp (hp₁.calls.rhoT.relct (fun a b hab => two.spE hab.1 hab.2)
      (fun a b hab => two.sub (by simp) hab.1 hab.2))
      fun a b hab => ⟨cpRho_env hp₁ hab.1, cpRho_env hp₂ hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => KEnv K s₁ a ∧ KEnv K s₂ b)
    (relct_wp (hp₁.calls.ekT.relct (fun a b hab => two.spE hab.1 hab.2)
      (fun a b hab => two.sub (by simp) hab.1 hab.2))
      fun a b hab => ⟨cpEk_env hp₁ hab.1, cpEk_env hp₂ hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => KEnv K s₁ a ∧ KEnv K s₂ b)
    (relct_wp (hash_ct (L := lay s₁ K) (idx := kidx) VG.Proof.MlKem.rate136 (by decide)
      (List.cons_ne_nil _ _) fun a b hab => ⟨⟨hab.1.ctx, h_ins hp₁ hab.1, h_outs hp₁ hab.1⟩,
        by rw [← two.lay]; exact ⟨hab.2.ctx, h_ins hp₂ hab.2, h_outs hp₂ hab.2⟩,
        two.spE hab.1 hab.2⟩)
      fun a b hab => ⟨hashH_env hp₁ hab.1, hashH_env hp₂ hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => KEnv K s₁ a ∧ KEnv K s₂ b)
    (relct_wp (hp₁.calls.zT.relct (fun a b hab => two.spE hab.1 hab.2)
      (fun a b hab => two.sub (by simp) hab.1 hab.2))
      fun a b hab => ⟨cpZ_env hp₁ hab.1, cpZ_env hp₂ hab.2⟩) ?_
  exact taint_block [.r31] (fun a b hab => two.spE hab.1 hab.2)
    (fun a b hab => two.sub (by simp) hab.1 hab.2) (by taint_decide)

end

/-! ## The outcome -/

/-- The `SampleNTT`s of `Â` all finished, with the entries the rows used. -/
theorem sample_some {K : KemLay} {s₀ : State} (hk : okK K s₀ K.k = true) :
    ∀ i < K.k, ∀ j < K.k,
      sampleNTT 280 (VG.Proof.MlKem.matSeed (VG.Proof.MlKem.KPke.kgRho K.p (D s₀)) i j) =
        some (aK K s₀ i j) := by
  intro i hi j hj
  have h₁ := List.all_eq_true.mp hk i (List.mem_range.mpr hi)
  have h₂ := List.all_eq_true.mp h₁ j (List.mem_range.mpr hj)
  simp only [rowSeed, Bool.false_eq_true, ite_false] at h₂
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h₂
  rw [hv]
  simp only [aK, effA, rowSeed, Bool.false_eq_true, ite_false, hv, Option.getD_some]

/-- A `SampleNTT` of `Â` did not finish. -/
theorem sample_none {K : KemLay} {s₀ : State} (hk : okK K s₀ K.k = false) :
    ∃ i < K.k, ∃ j < K.k,
      sampleNTT 280 (VG.Proof.MlKem.matSeed (VG.Proof.MlKem.KPke.kgRho K.p (D s₀)) i j) = none := by
  rw [okK, List.all_eq_false] at hk
  obtain ⟨i, hi, h₁⟩ := hk
  rw [Bool.not_eq_true, okRow, List.all_eq_false] at h₁
  obtain ⟨j, hj, h₂⟩ := h₁
  simp only [rowSeed, Bool.false_eq_true, ite_false] at h₂
  exact ⟨i, List.mem_range.mp hi, j, List.mem_range.mp hj, Option.not_isSome_iff_eq_none.mp h₂⟩

/-- What key generation returns and writes is the outcome of
`ML-KEM.KeyGen_internal(d, z)`. -/
theorem outcome {K : KemLay} (hK : K.WF) (s₀ : State) :
    Outcome (fun iters => keyGenInternal K.p iters (D s₀) (Z s₀)) (if okK K s₀ K.k then 1 else 0)
      (EK K s₀, DK K s₀) := by
  refine VG.Proof.MlKem.outcome_of_min ?_
  rw [show minIterations = 280 from rfl]
  cases hk : okK K s₀ K.k
  · obtain ⟨i, hi, j, hj, hn⟩ := sample_none hk
    refine .inr ⟨rfl, ?_⟩
    rw [VG.Proof.MlKem.KPke.keyGenInternal_eq, VG.Proof.MlKem.KPke.kpkeKeyGen_none hi hj hn]; rfl
  · refine .inl ⟨rfl, ?_⟩
    rw [VG.Proof.MlKem.KPke.keyGenInternal_eq,
      VG.Proof.MlKem.KPke.kpkeKeyGen_some hK.η₁ (sample_some hk)]
    rfl

/-! ## ML-KEM-768 -/

theorem pre_of {s : State} (h : (Spec.MlKem.keyGenContract PPC64LE.abi 48).pre s) : Pre kl768 s := by
  sig_pre [Spec.MlKem.keyGenContract, Spec.MlKem.keyGenSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h0, h1, h2, d1, d2, d3, d4, d5, d6, b1, b2, b3, b4, f1, f2, f3, f4⟩ := h
  exact ⟨kl768_wf, kl768_calls, h0, h1, h2, d1, d2, d3, d4, d5, d6, b1, b2, b3, b4, f1, f2, f3, f4⟩

theorem post_of {s₀ s : State} (h3 : s.gpr .r3 = if okK kl768 s₀ kl768.k then 1 else 0)
    (hek : bytesAt s.mem (pEk s₀) 1184 = EK kl768 s₀)
    (hdk : bytesAt s.mem (pDk s₀) 2400 = DK kl768 s₀) :
    (Spec.MlKem.keyGenContract PPC64LE.abi 48).post s₀ s := by
  sig_post [Spec.MlKem.keyGenContract, Spec.MlKem.keyGenSig, PPC64LE.abi, PPC64LE.argRegs]
  have e : BitVec.setWidth 32 (if okK kl768 s₀ kl768.k then (1 : BitVec 64) else 0) =
      if okK kl768 s₀ kl768.k then 1 else 0 := by
    cases okK kl768 s₀ kl768.k <;> rfl
  rw [h3, hek, hdk, e]
  exact outcome kl768_wf s₀

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 0x10000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 64⟩]
  wr := [⟨0x2000, 1184⟩, ⟨0x3000, 2400⟩, ⟨0x10000, 32768⟩]

theorem verified :
    Verified PPC64LE.target Impl.MlKem.PPC64LE.keygen (Spec.MlKem.keyGenContract PPC64LE.abi 48) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hlr, h3, hek, hdk⟩ := correct (pre_of hs)
    exact ⟨t, s', he, ⟨hpres, hsp, hlr⟩, post_of h3 hek hdk⟩
  · have hp₁ := pre_of h₁
    have hp₂ := pre_of h₂
    sig_pub [Spec.MlKem.keyGenContract, Spec.MlKem.keyGenSig, PPC64LE.abi, PPC64LE.argRegs] at hpub
    obtain ⟨hsp, hl, g3, g4, g5, g6⟩ := hpub
    have hr : ρ₀ kl768 s₁ = ρ₀ kl768 s₂ :=
      (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hl
    exact (all_ct ⟨hp₁, hp₂, hsp, g3, g4, g5, g6, hr⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.MlKem.keyGenContract, Spec.MlKem.keyGenSig, PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | decide +kernel

end VG.Proof.MlKem.PPC64LE.KeyGen
