module

public import VerifiedGarbage.Proof.MlKem.RISCV64.Decaps
import VerifiedGarbage.Proof.MlKem.RISCV64.EncryptCT
public import VerifiedGarbage.Proof.MlKem.RISCV64.HashCT

import VerifiedGarbage.Proof.MlKem.RISCV64.RowCT
import VerifiedGarbage.Proof.MlKem.RISCV64.CallsCT
import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.RelBlock
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Decaps
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
# ML-KEM on RISC-V: decapsulation, constant time and `Verified`

As on PPC64LE (`Proof/MlKem/PPC64LE/DecapsCT.lean`): two runs from states that
agree on the public data (the pointers, the stack pointer and `ρ` in `dk`,
which the contract lets the function leak) leak the same trace (`all_ct`),
phase by phase: the blocks by the taint analysis, from the pointers, or
because they access no memory; the calls of the primitives on the same
pointers; the hashes by `hash_ct`; and the re-encryption by `encrypt_ct`. The
comparison of `c` and `c'` and the selection of the key branch on nothing but
their counters: the taint analysis proves them constant time from the
pointers, which are the same in both runs. What each run is at each point
comes from its correctness (`Decaps.lean`).

All of it holds for any parameter set: the taint analyses of the blocks whose
immediates depend on it are facts of `KemLay.CallsOk`, which the parameter set
checks by evaluation.
-/

@[expose] public section

namespace VG.Proof.MlKem.RISCV64.Decaps

open VG VG.RISCV64 VG.Impl.MlKem.RISCV64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.RISCV64.Enc

theorem rhoD_eq (K : KemLay) (s : State) : ρD K s = dkRho K.p (DK K s) :=
  VG.Proof.MlKem.KPke.ekRho_dkEk K.p (DK K s)

/-- Two runs, from states that agree on the public data. -/
structure Two (K : KemLay) (s₁ s₂ : State) : Prop where
  hp₁ : Pre K s₁
  hp₂ : Pre K s₂
  sp : s₁.sp = s₂.sp
  a0 : s₁.gpr .a0 = s₂.gpr .a0
  a1 : s₁.gpr .a1 = s₂.gpr .a1
  a2 : s₁.gpr .a2 = s₂.gpr .a2
  a3 : s₁.gpr .a3 = s₂.gpr .a3
  rho : ρD K s₁ = ρD K s₂

section
variable {K : KemLay} {s₁ s₂ : State} (two : Two K s₁ s₂)
include two

theorem Two.layEq : lay s₂ K = lay s₁ K := by
  simp only [Decaps.lay, pScr, pDk, pKey, two.a0, two.a2, two.a3, two.sp]

theorem Two.p0 : (lay s₁ K).ptr 0 = (lay s₂ K).ptr 0 := by rw [two.layEq]

theorem Two.aEq (i o : Nat) : (lay s₁ K).A i o = (lay s₂ K).A i o := by rw [two.layEq]

theorem Two.regs {a b : State} (ha : DEnv K s₁ a) (hb : DEnv K s₂ b) : a.gpr .s11 = b.gpr .s11 := by
  rw [ha.ctx.s11, hb.ctx.s11, two.layEq]

theorem Two.spE {a b : State} (ha : DEnv K s₁ a) (hb : DEnv K s₂ b) : a.sp = b.sp := by
  rw [ha.sp, hb.sp, two.sp]

theorem Two.spD {a b : State} (ha : DD K s₁ a) (hb : DD K s₂ b) : a.sp = b.sp :=
  two.spE ha.env hb.env

theorem Two.spV {f g : Poly} {a b : State} (ha : DV K s₁ f a) (hb : DV K s₂ g b) : a.sp = b.sp :=
  two.spD ha.1 hb.1

theorem Two.hashOk {ins outs : List Piece} {a b : State} (ha : DD K s₁ a) (hb : DD K s₂ b)
    (hi : ∀ {s₀ s : State}, Pre K s₀ → DD K s₀ s → ∀ p ∈ ins, PieceOk (lay s₀ K) didx s false p)
    (ho : ∀ {s₀ s : State}, Pre K s₀ → DD K s₀ s → ∀ p ∈ outs, PieceOk (lay s₀ K) didx s true p) :
    HashOk (lay s₁ K) didx ins outs a ∧ HashOk (lay s₁ K) didx ins outs b ∧ a.sp = b.sp :=
  ⟨⟨ha.env.ctx, hi two.hp₁ ha, ho two.hp₁ ha⟩,
    by rw [← two.layEq]; exact ⟨hb.env.ctx, hi two.hp₂ hb, ho two.hp₂ hb⟩,
    two.spE ha.env hb.env⟩

/-! ## `û` -/

theorem decU_ct {x y : State} (hx : DD K s₁ x) (hy : DD K s₂ y) {j : Nat} (hj : j < K.k) :
    RelCT isa (fun a b => UInv K s₁ x j a ∧ UInv K s₂ y j b) K.decUBody fun a b =>
      (UInv K s₁ x (j + 1) a ∧ (a.gpr .t0 != 0) = decide (j + 1 ≠ K.k)) ∧
      (UInv K s₂ y (j + 1) b ∧ (b.gpr .t0 != 0) = decide (j + 1 ≠ K.k)) := by
  have hp₁ := two.hp₁
  have hp₂ := two.hp₂
  refine relct_wp (RelCT.pointwise fun u w ⟨hu, hw⟩ => ?_) fun a b hab =>
    ⟨decU_step hp₁ hx hj hab.1, decU_step hp₂ hy hj hab.2⟩
  refine RelCT.seq (R := fun (a b : State) =>
      (Only u a ∧ a.gpr .a0 = (lay s₁ K).A 0 (oCin + K.uLen * j) ∧
        a.gpr .a1 = BitVec.ofNat 64 (32 * K.du) ∧ a.gpr .a2 = BitVec.ofNat 64 K.du ∧
        a.gpr .a3 = (lay s₁ K).A 0 (oPoly (K.k + j))) ∧
      (Only w b ∧ b.gpr .a0 = (lay s₂ K).A 0 (oCin + K.uLen * j) ∧
        b.gpr .a1 = BitVec.ofNat 64 (32 * K.du) ∧ b.gpr .a2 = BitVec.ofNat 64 K.du ∧
        b.gpr .a3 = (lay s₂ K).A 0 (oPoly (K.k + j))))
    (relct_wp (relct_noMem (by rw [List.all_append, List.all_append]; rfl)) fun a b hab =>
      ⟨by rw [hab.1]; exact u1_ok hp₁ hx hj hu, by rw [hab.2]; exact u1_ok hp₂ hy hj hw⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => UB K s₁ j u a ∧ UB K s₂ j w b)
    (relct_wp (RelCT.callT hp₁.calls.duT (regs4 fun a b hab =>
      ⟨by rw [hab.1.1.sp, hab.2.1.sp, hu.kx.sp, hw.kx.sp]; exact two.spD hx hy,
        by rw [hab.1.2.1, hab.2.2.1, two.aEq], by rw [hab.1.2.2.1, hab.2.2.2.1],
        by rw [hab.1.2.2.2.1, hab.2.2.2.2.1], by rw [hab.1.2.2.2.2, hab.2.2.2.2.2, two.aEq]⟩))
      fun a b ⟨⟨o₁, a3, a4, a5, a6⟩, ⟨o₂, b3, b4, b5, b6⟩⟩ =>
        ⟨u2_ok hp₁ hx hj hu o₁ a3 a4 a5 a6, u2_ok hp₂ hy hj hw o₂ b3 b4 b5 b6⟩) ?_
  refine RelCT.seq (R := fun (a b : State) =>
      (UB K s₁ j u a ∧ a.gpr .a0 = (lay s₁ K).A 0 (oPoly (K.k + j)) ∧
        a.gpr .a1 = (lay s₁ K).A 0 K.oNtt) ∧
      (UB K s₂ j w b ∧ b.gpr .a0 = (lay s₂ K).A 0 (oPoly (K.k + j)) ∧
        b.gpr .a1 = (lay s₂ K).A 0 K.oNtt))
    (relct_wp (relct_noMem (by rfl)) fun a b hab =>
      ⟨u3_ok hp₁ hx hj hu hab.1, u3_ok hp₂ hy hj hw hab.2⟩) ?_
  exact RelCT.seq (R := fun _ _ => True)
    (RelCT.callT nttT (regs2 fun a b hab =>
      ⟨by rw [hab.1.1.kx.sp, hab.2.1.kx.sp, hu.kx.sp, hw.kx.sp]; exact two.spD hx hy,
        by rw [hab.1.2.1, hab.2.2.1, two.aEq], by rw [hab.1.2.2, hab.2.2.2, two.aEq]⟩))
    (relct_noMem (by rfl))

/-! ## K-PKE.Decrypt -/

theorem decrypt_ct {x y : State} (hx : DD K s₁ x) (hy : DD K s₂ y) :
    RelCT isa (fun a b => a = x ∧ b = y) K.decrypt fun _ _ => True := by
  have hp₁ := two.hp₁
  have hp₂ := two.hp₂
  have hK := hp₁.wf
  -- `û`
  refine RelCT.seq (R := fun (a b : State) => UInv K s₁ x 0 a ∧ UInv K s₂ y 0 b)
    (relct_wp (relct_noMem (by rfl)) fun a b hab =>
      ⟨by rw [hab.1]; exact dU_init, by rw [hab.2]; exact dU_init⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => UInv K s₁ x K.k a ∧ UInv K s₂ y K.k b)
    (relct_loop_nz (N := K.k) hK.k1 fun j hj => decU_ct two hx hy hj) ?_
  refine RelCT.pointwise fun x₃ y₃ ⟨hx₃, hy₃⟩ => ?_
  have d₁ := dU_done hp₁ hx hx₃
  have d₂ := dU_done hp₂ hy hy₃
  obtain ⟨hc₁, g30₁, hs₁, hr₁⟩ := dT_pre hp₁ d₁
  obtain ⟨hc₂, g30₂, hs₂, hr₂⟩ := dT_pre hp₂ d₂
  -- `ŝ`
  refine RelCT.seq (R := fun (a b : State) =>
      DecInv K (lay s₁ K) 2 0 x₃ 0 a ∧ DecInv K (lay s₁ K) 2 0 y₃ 0 b)
    (relct_wp (relct_noMem (by rfl)) fun a b hab =>
      ⟨by rw [hab.1]; exact decT_init, by rw [hab.2]; exact decT_init⟩) ?_
  rw [two.layEq] at hc₂ g30₂ hr₂
  refine RelCT.seq (R := fun (a b : State) =>
      DecInv K (lay s₁ K) 2 0 x₃ K.k a ∧ DecInv K (lay s₁ K) 2 0 y₃ K.k b)
    (relct_loop_nz (N := K.k) hK.k1 fun j hj => decT_ctG hK hc₁ hc₂ g30₁ g30₂ hs₁ hr₁ hr₂ hj) ?_
  refine RelCT.pointwise fun x₅ y₅ ⟨hx₅, hy₅⟩ => ?_
  obtain ⟨e₁, ŝ₁, û₁⟩ := dT_done hp₁ d₁ hx₃.u hx₅
  rw [← two.layEq] at hy₅
  obtain ⟨e₂, ŝ₂, û₂⟩ := dT_done hp₂ d₂ hy₃.u hy₅
  -- `ŝ ∘ û`
  refine RelCT.seq (R := fun (a b : State) =>
      DV K s₁ (VG.Proof.MlKem.KPke.dotK (sHat K s₁) (uHat K s₁) K.k) a ∧
      DV K s₂ (VG.Proof.MlKem.KPke.dotK (sHat K s₂) (uHat K s₂) K.k) b)
    (relct_wp (dot_ct hK (L := lay s₁ K) e₁.env.ctx (by rw [← two.layEq]; exact e₂.env.ctx) ŝ₁ û₁
      (by rw [← two.layEq]; exact ŝ₂) (by rw [← two.layEq]; exact û₂) hp₁.calls) fun a b hab =>
      ⟨by rw [hab.1]; exact dDot_ok hp₁ e₁ ŝ₁ û₁, by rw [hab.2]; exact dDot_ok hp₂ e₂ ŝ₂ û₂⟩) ?_
  -- `NTT⁻¹`
  refine RelCT.seq (R := fun (a b : State) =>
      ((DV K s₁ (VG.Proof.MlKem.KPke.dotK (sHat K s₁) (uHat K s₁) K.k) a ∧ True) ∧
        a.gpr .a0 = (lay s₁ K).A 0 K.oAcc ∧ a.gpr .a1 = (lay s₁ K).A 0 K.oNtt) ∧
      ((DV K s₂ (VG.Proof.MlKem.KPke.dotK (sHat K s₂) (uHat K s₂) K.k) b ∧ True) ∧
        b.gpr .a0 = (lay s₂ K).A 0 K.oAcc ∧ b.gpr .a1 = (lay s₂ K).A 0 K.oNtt))
    (relct_wp (relct_noMem (by rfl)) fun a b hab =>
      ⟨WP.mono (dArgs_ok hp₁ hab.1 (j := K.jAcc) (j' := K.jNtt) (by offs) (by offs))
        fun _ ⟨⟨h, _⟩, g⟩ => ⟨⟨h, trivial⟩, g⟩,
       WP.mono (dArgs_ok hp₂ hab.2 (j := K.jAcc) (j' := K.jNtt) (by offs) (by offs))
        fun _ ⟨⟨h, _⟩, g⟩ => ⟨⟨h, trivial⟩, g⟩⟩) ?_
  refine RelCT.seq (R := fun (a b : State) =>
      DV K s₁ (nttInv (VG.Proof.MlKem.KPke.dotK (sHat K s₁) (uHat K s₁) K.k)) a ∧
      DV K s₂ (nttInv (VG.Proof.MlKem.KPke.dotK (sHat K s₂) (uHat K s₂) K.k)) b)
    (relct_wp (RelCT.callT nttInvT (regs2 fun a b hab =>
      ⟨two.spV hab.1.1.1 hab.2.1.1, by rw [hab.1.2.1, hab.2.2.1, two.aEq],
        by rw [hab.1.2.2, hab.2.2.2, two.aEq]⟩))
      fun a b hab => ⟨dInv_ok hp₁ hab.1.1.1 hab.1.2.1 hab.1.2.2,
        dInv_ok hp₂ hab.2.1.1 hab.2.2.1 hab.2.2.2⟩) ?_
  -- `v'`
  refine RelCT.seq (R := fun (a b : State) =>
      (DV K s₁ (nttInv (VG.Proof.MlKem.KPke.dotK (sHat K s₁) (uHat K s₁) K.k)) a ∧
        a.gpr .a0 = (lay s₁ K).A 0 (oCin + K.uLen * K.k) ∧
        a.gpr .a1 = BitVec.ofNat 64 (32 * K.dv) ∧ a.gpr .a2 = BitVec.ofNat 64 K.dv ∧
        a.gpr .a3 = (lay s₁ K).A 0 (oPoly (3 * K.k))) ∧
      (DV K s₂ (nttInv (VG.Proof.MlKem.KPke.dotK (sHat K s₂) (uHat K s₂) K.k)) b ∧
        b.gpr .a0 = (lay s₂ K).A 0 (oCin + K.uLen * K.k) ∧
        b.gpr .a1 = BitVec.ofNat 64 (32 * K.dv) ∧ b.gpr .a2 = BitVec.ofNat 64 K.dv ∧
        b.gpr .a3 = (lay s₂ K).A 0 (oPoly (3 * K.k))))
    (relct_wp (relct_noMem (by rfl)) fun a b hab => ⟨dV1_ok hp₁ hab.1, dV1_ok hp₂ hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) =>
      (DV K s₁ (nttInv (VG.Proof.MlKem.KPke.dotK (sHat K s₁) (uHat K s₁) K.k)) a ∧
        PolyIs a.mem ((lay s₁ K).A 0 (oPoly (3 * K.k))) (VG.Proof.MlKem.KPke.dcV K.p (CT K s₁))) ∧
      (DV K s₂ (nttInv (VG.Proof.MlKem.KPke.dotK (sHat K s₂) (uHat K s₂) K.k)) b ∧
        PolyIs b.mem ((lay s₂ K).A 0 (oPoly (3 * K.k))) (VG.Proof.MlKem.KPke.dcV K.p (CT K s₂))))
    (relct_wp (RelCT.callT hp₁.calls.duT (regs4 fun a b hab =>
      ⟨two.spV hab.1.1 hab.2.1, by rw [hab.1.2.1, hab.2.2.1, two.aEq],
        by rw [hab.1.2.2.1, hab.2.2.2.1], by rw [hab.1.2.2.2.1, hab.2.2.2.2.1],
        by rw [hab.1.2.2.2.2, hab.2.2.2.2.2, two.aEq]⟩))
      fun a b ⟨⟨h₁, a3, a4, a5, a6⟩, ⟨h₂, b3, b4, b5, b6⟩⟩ =>
        ⟨dV2_ok hp₁ h₁ a3 a4 a5 a6, dV2_ok hp₂ h₂ b3 b4 b5 b6⟩) ?_
  -- `w`
  refine RelCT.seq (R := fun (a b : State) =>
      ((DV K s₁ (nttInv (VG.Proof.MlKem.KPke.dotK (sHat K s₁) (uHat K s₁) K.k)) a ∧
        PolyIs a.mem ((lay s₁ K).A 0 (oPoly (3 * K.k))) (VG.Proof.MlKem.KPke.dcV K.p (CT K s₁))) ∧
        a.gpr .a0 = (lay s₁ K).A 0 (oPoly (3 * K.k)) ∧ a.gpr .a1 = (lay s₁ K).A 0 K.oAcc) ∧
      ((DV K s₂ (nttInv (VG.Proof.MlKem.KPke.dotK (sHat K s₂) (uHat K s₂) K.k)) b ∧
        PolyIs b.mem ((lay s₂ K).A 0 (oPoly (3 * K.k))) (VG.Proof.MlKem.KPke.dcV K.p (CT K s₂))) ∧
        b.gpr .a0 = (lay s₂ K).A 0 (oPoly (3 * K.k)) ∧ b.gpr .a1 = (lay s₂ K).A 0 K.oAcc))
    (relct_wp (relct_noMem (by rfl)) fun a b hab =>
      ⟨WP.mono (dArgs_ok hp₁ hab.1.1 (j := 3 * K.k) (j' := K.jAcc) (by offs) (by offs))
        fun _ ⟨⟨h, m⟩, g⟩ => ⟨⟨h, by rw [m]; exact hab.1.2⟩, g⟩,
       WP.mono (dArgs_ok hp₂ hab.2.1 (j := 3 * K.k) (j' := K.jAcc) (by offs) (by offs))
        fun _ ⟨⟨h, m⟩, g⟩ => ⟨⟨h, by rw [m]; exact hab.2.2⟩, g⟩⟩) ?_
  refine RelCT.seq (R := fun (a b : State) =>
      (DD K s₁ a ∧ PolyIs a.mem ((lay s₁ K).A 0 (oPoly (3 * K.k)))
        (sub (VG.Proof.MlKem.KPke.dcV K.p (CT K s₁))
          (nttInv (VG.Proof.MlKem.KPke.dotK (sHat K s₁) (uHat K s₁) K.k)))) ∧
      (DD K s₂ b ∧ PolyIs b.mem ((lay s₂ K).A 0 (oPoly (3 * K.k)))
        (sub (VG.Proof.MlKem.KPke.dcV K.p (CT K s₂))
          (nttInv (VG.Proof.MlKem.KPke.dotK (sHat K s₂) (uHat K s₂) K.k)))))
    (relct_wp (RelCT.callT subT (regs2 fun a b hab =>
      ⟨two.spV hab.1.1.1 hab.2.1.1, by rw [hab.1.2.1, hab.2.2.1, two.aEq],
        by rw [hab.1.2.2, hab.2.2.2, two.aEq]⟩))
      fun a b hab => ⟨dV4_ok hp₁ hab.1.1.1 hab.1.1.2 hab.1.2.1 hab.1.2.2,
        dV4_ok hp₂ hab.2.1.1 hab.2.1.2 hab.2.2.1 hab.2.2.2⟩) ?_
  -- `m'`
  refine RelCT.seq (R := fun (a b : State) =>
      ((DD K s₁ a ∧ PolyIs a.mem ((lay s₁ K).A 0 (oPoly (3 * K.k)))
          (sub (VG.Proof.MlKem.KPke.dcV K.p (CT K s₁))
            (nttInv (VG.Proof.MlKem.KPke.dotK (sHat K s₁) (uHat K s₁) K.k)))) ∧
        a.gpr .a0 = (lay s₁ K).A 0 (oPoly (3 * K.k)) ∧ a.gpr .a1 = BitVec.ofNat 64 1 ∧
        a.gpr .a2 = (lay s₁ K).A 0 oMsg ∧ a.gpr .a3 = BitVec.ofNat 64 (32 * 1)) ∧
      ((DD K s₂ b ∧ PolyIs b.mem ((lay s₂ K).A 0 (oPoly (3 * K.k)))
          (sub (VG.Proof.MlKem.KPke.dcV K.p (CT K s₂))
            (nttInv (VG.Proof.MlKem.KPke.dotK (sHat K s₂) (uHat K s₂) K.k)))) ∧
        b.gpr .a0 = (lay s₂ K).A 0 (oPoly (3 * K.k)) ∧ b.gpr .a1 = BitVec.ofNat 64 1 ∧
        b.gpr .a2 = (lay s₂ K).A 0 oMsg ∧ b.gpr .a3 = BitVec.ofNat 64 (32 * 1)))
    (relct_wp (relct_noMem (by rfl)) fun a b hab =>
      ⟨dM1_ok hp₁ hab.1.1 hab.1.2, dM1_ok hp₂ hab.2.1 hab.2.2⟩) ?_
  refine RelCT.callT compressT (regs4 ?_)
  intro a b hab
  exact ⟨two.spD hab.1.1.1 hab.2.1.1, by rw [hab.1.2.1, hab.2.2.1, two.aEq],
    by rw [hab.1.2.2.1, hab.2.2.2.1], by rw [hab.1.2.2.2.1, hab.2.2.2.2.1, two.aEq],
    by rw [hab.1.2.2.2.2, hab.2.2.2.2.2]⟩

/-! ## The whole function -/

theorem all_ct : RelCT isa (fun a b => a = s₁ ∧ b = s₂) K.decaps fun _ _ => True := by
  have hp₁ := two.hp₁
  have hp₂ := two.hp₂
  have hK := hp₁.wf
  have hL₁ := lay_ok hp₁
  have hL₂ := lay_ok hp₂
  -- the setup
  refine RelCT.seq (R := fun (a b : State) =>
      (DEnv K s₁ a ∧ a.gpr .s10 = pDk s₁ ∧ a.gpr .s8 = pC s₁ ∧
        bytesAt a.mem ((layC s₁ K).A 2 0) K.ctLen = CT K s₁) ∧
      (DEnv K s₂ b ∧ b.gpr .s10 = pDk s₂ ∧ b.gpr .s8 = pC s₂ ∧
        bytesAt b.mem ((layC s₂ K).A 2 0) K.ctLen = CT K s₂))
    (relct_wp (taint_block [.a0, .a1, .a2, .a3] (fun a b hab => by rw [hab.1, hab.2, two.sp])
      (fun a b hab r hr => by
        rw [hab.1, hab.2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact two.a0
        · exact two.a1
        · exact two.a2
        · exact two.a3) (by taint_decide))
      fun a b hab => ⟨by rw [hab.1]; exact setup_ok hp₁, by rw [hab.2]; exact setup_ok hp₂⟩) ?_
  -- `c` copied
  refine RelCT.seq (R := fun (a b : State) =>
      (DEnv K s₁ a ∧ a.gpr .s10 = pDk s₁ ∧ bytesAt a.mem ((lay s₁ K).A 0 oCin) K.ctLen = CT K s₁) ∧
      (DEnv K s₂ b ∧ b.gpr .s10 = pDk s₂ ∧ bytesAt b.mem ((lay s₂ K).A 0 oCin) K.ctLen = CT K s₂))
    (relct_wp (hp₁.calls.ctT.relct (fun a b hab => two.spE hab.1.1 hab.2.1)
      (fun a b hab r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [hab.1.2.2.1, hab.2.2.2.1]; exact two.a1
        · exact two.regs hab.1.1 hab.2.1))
      fun a b hab =>
        ⟨WP.mono (copyC_ok hp₁ hab.1.1 hab.1.2.2.1 hab.1.2.2.2) fun _ ⟨e, g, c⟩ =>
            ⟨e, by rw [g, hab.1.2.1], c⟩,
          WP.mono (copyC_ok hp₂ hab.2.1 hab.2.2.2.1 hab.2.2.2.2) fun _ ⟨e, g, c⟩ =>
            ⟨e, by rw [g, hab.2.2.1], c⟩⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => DD K s₁ a ∧ DD K s₂ b)
    (relct_wp (relct_noMem (addrOf_noMem _ _ _)) fun a b hab =>
      ⟨WP.mono ptr28_ok fun _ h => dd_of hp₁ hab.1.1 hab.1.2.1 hab.1.2.2 h,
        WP.mono ptr28_ok fun _ h => dd_of hp₂ hab.2.1 hab.2.2.1 hab.2.2.2 h⟩) ?_
  -- K-PKE.Decrypt
  refine RelCT.seq (R := fun (a b : State) =>
      (DD K s₁ a ∧ bytesAt a.mem ((lay s₁ K).A 0 oMsg) 32 = MM K s₁) ∧
      (DD K s₂ b ∧ bytesAt b.mem ((lay s₂ K).A 0 oMsg) 32 = MM K s₂))
    (relct_wp (RelCT.pointwise fun x y hxy => decrypt_ct two hxy.1 hxy.2) fun a b hab =>
      ⟨decrypt_ok hp₁ hab.1, decrypt_ok hp₂ hab.2⟩) ?_
  -- the frames' disjointness from the outputs, for both runs
  have sG : sepAll (dSz K) (0, oMsg, 32) (kRegs ++ [(0, oG, 64)]) = true := by ddecide
  have sJm : sepAll (dSz K) (0, oMsg, 32) (kRegs ++ [(0, oKbar, 32)]) = true := by ddecide
  have sJg : sepAll (dSz K) (0, oG, 32) (kRegs ++ [(0, oKbar, 32)]) = true := by ddecide
  have sJs : sepAll (dSz K) (0, oSigma, 32) (kRegs ++ [(0, oKbar, 32)]) = true := by ddecide
  -- `G(m' ‖ h)`
  refine RelCT.seq (R := fun (a b : State) =>
      (DD K s₁ a ∧ bytesAt a.mem ((lay s₁ K).A 0 oMsg) 32 = MM K s₁ ∧
        bytesAt a.mem ((lay s₁ K).A 0 oG) 32 = K1 K s₁ ∧
        bytesAt a.mem ((lay s₁ K).A 0 oSigma) 32 = R1 K s₁) ∧
      (DD K s₂ b ∧ bytesAt b.mem ((lay s₂ K).A 0 oMsg) 32 = MM K s₂ ∧
        bytesAt b.mem ((lay s₂ K).A 0 oG) 32 = K1 K s₂ ∧
        bytesAt b.mem ((lay s₂ K).A 0 oSigma) 32 = R1 K s₂))
    (relct_wp (hash_ct (L := lay s₁ K) (idx := didx) VG.Proof.MlKem.rate72 (by decide)
      (List.cons_ne_nil _ _) fun a b hab =>
        two.hashOk (ins := [⟨.s11, oMsg, 32⟩, ⟨.s10, 768 * K.k + 32, 32⟩]) (outs := [⟨.s11, oG, 64⟩])
          hab.1.1 hab.2.1
        (fun hp h p hp' => by
          have hK := hp.wf
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
          rcases hp' with rfl | rfl
          · exact pieceD hp h (.inr rfl) (by simp) (by show oMsg < 32768; decide)
              (by show (32 : Nat) < 2048; decide) (by show 0 < 32; decide) (by ddecide)
          · exact pieceD hp h (.inl rfl) (by simp)
              (by show 768 * K.k + 32 < 32768; have := hK.k4; omega)
              (by show (32 : Nat) < 2048; decide) (by show 0 < 32; decide) (by ddecide))
        (fun hp h p hp' => by
          rw [List.mem_singleton] at hp'; subst hp'
          exact pieceD hp h (.inr rfl) (fun _ => rfl) (by show oG < 32768; decide)
            (by show (64 : Nat) < 2048; decide) (by show 0 < 64; decide) (by ddecide)))
      fun a b hab =>
        ⟨WP.mono (hashG_ok hp₁ hab.1.1 hab.1.2) fun _ ⟨d, f, k, r⟩ =>
          ⟨d, (Lay.bytes_keep hL₁ f sG (by decide)).trans hab.1.2, k, r⟩,
         WP.mono (hashG_ok hp₂ hab.2.1 hab.2.2) fun _ ⟨d, f, k, r⟩ =>
          ⟨d, (Lay.bytes_keep hL₂ f sG (by decide)).trans hab.2.2, k, r⟩⟩) ?_
  -- `J(z ‖ c)`
  refine RelCT.seq (R := fun (a b : State) =>
      (DD K s₁ a ∧ bytesAt a.mem ((lay s₁ K).A 0 oMsg) 32 = MM K s₁ ∧
        bytesAt a.mem ((lay s₁ K).A 0 oG) 32 = K1 K s₁ ∧
        bytesAt a.mem ((lay s₁ K).A 0 oSigma) 32 = R1 K s₁ ∧
        bytesAt a.mem ((lay s₁ K).A 0 oKbar) 32 = KB K s₁) ∧
      (DD K s₂ b ∧ bytesAt b.mem ((lay s₂ K).A 0 oMsg) 32 = MM K s₂ ∧
        bytesAt b.mem ((lay s₂ K).A 0 oG) 32 = K1 K s₂ ∧
        bytesAt b.mem ((lay s₂ K).A 0 oSigma) 32 = R1 K s₂ ∧
        bytesAt b.mem ((lay s₂ K).A 0 oKbar) 32 = KB K s₂))
    (relct_wp (hash_ct (L := lay s₁ K) (idx := didx) VG.Proof.MlKem.rate136 (by decide)
      (List.cons_ne_nil _ _) fun a b hab =>
        two.hashOk (ins := [⟨.s10, 768 * K.k + 64, 32⟩, ⟨.s11, oCin, K.ctLen⟩])
          (outs := [⟨.s11, oKbar, 32⟩]) hab.1.1 hab.2.1
        (fun hp h p hp' => by
          have hK := hp.wf
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
          rcases hp' with rfl | rfl
          · exact pieceD hp h (.inl rfl) (by simp)
              (by show 768 * K.k + 64 < 32768; have := hK.k4; omega)
              (by show (32 : Nat) < 2048; decide) (by show 0 < 32; decide) (by ddecide)
          · exact pieceD hp h (.inr rfl) (by simp) (by show oCin < 32768; decide)
              (by show K.ctLen < 2048; exact ct_lt hK) (ct_pos hK) (by ddecide))
        (fun hp h p hp' => by
          rw [List.mem_singleton] at hp'; subst hp'
          exact pieceD hp h (.inr rfl) (fun _ => rfl) (by show oKbar < 32768; decide)
            (by show (32 : Nat) < 2048; decide) (by show 0 < 32; decide) (by ddecide)))
      fun a b hab =>
        ⟨WP.mono (hashJ_ok hp₁ hab.1.1) fun _ ⟨d, f, kb⟩ =>
          ⟨d, (Lay.bytes_keep hL₁ f sJm (by decide)).trans hab.1.2.1,
            (Lay.bytes_keep hL₁ f sJg (by decide)).trans hab.1.2.2.1,
            (Lay.bytes_keep hL₁ f sJs (by decide)).trans hab.1.2.2.2, kb⟩,
         WP.mono (hashJ_ok hp₂ hab.2.1) fun _ ⟨d, f, kb⟩ =>
          ⟨d, (Lay.bytes_keep hL₂ f sJm (by decide)).trans hab.2.2.1,
            (Lay.bytes_keep hL₂ f sJg (by decide)).trans hab.2.2.2.1,
            (Lay.bytes_keep hL₂ f sJs (by decide)).trans hab.2.2.2.2, kb⟩⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => DP K s₁ a ∧ DP K s₂ b)
    (relct_wp (relct_noMem (by rfl)) fun a b ⟨⟨d, m, k, r, kb⟩, ⟨d', m', k', r', kb'⟩⟩ =>
      ⟨ptrs_dp hp₁ d m k r kb, ptrs_dp hp₂ d' m' k' r' kb'⟩) ?_
  -- the re-encryption
  refine RelCT.seq (R := fun (a b : State) => DQ K s₁ a ∧ DQ K s₂ b)
    (relct_wp (RelCT.pointwise fun x y hxy => ?_) fun a b hab =>
      ⟨reenc_ok hp₁ hab.1, reenc_ok hp₂ hab.2⟩) ?_
  · have ey : EncPre K (lay s₁ K) (db K) y := by rw [← two.layEq]; exact encPre hp₂ hxy.2
    refine encrypt_ct (encPre hp₁ hxy.1) ey ?_
    show ekRho K.p (ekB K (lay s₁ K) (db K) x) = ekRho K.p (ekB K (lay s₁ K) (db K) y)
    have e₁ : ekB K (lay s₁ K) (db K) x = eK K s₁ := ek_of hK hxy.1
    have e₂ : ekB K (lay s₁ K) (db K) y = eK K s₂ := by
      rw [← two.layEq]; exact ek_of hK hxy.2
    rw [e₁, e₂]; exact two.rho
  -- the comparison and the selection
  refine RelCT.seq (R := fun (a b : State) => DR K s₁ a ∧ DR K s₂ b)
    (relct_wp (hp₁.calls.cmpT.relct (fun a b hab => two.spE hab.1.env hab.2.env)
      (fun a b hab r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [hab.1.s7, hab.2.s7, two.aEq]
        · rw [hab.1.s8, hab.2.s8, two.aEq]))
      fun a b hab => ⟨cmp_ok hp₁ hab.1, cmp_ok hp₂ hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => DS K s₁ a ∧ DS K s₂ b)
    (relct_wp (taint_block [.s11] (fun a b hab => two.spE hab.1.q.env hab.2.q.env)
      (fun a b hab r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact two.regs hab.1.q.env hab.2.q.env) (by taint_decide))
      fun a b hab => ⟨mask_ok hp₁ hab.1, mask_ok hp₂ hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => DEnv K s₁ a ∧ DEnv K s₂ b)
    (relct_wp (taint_prog [.a0, .a1, .a2, .s6] (fun a b hab => two.spE hab.1.q.env hab.2.q.env)
      (fun a b hab r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [hab.1.a0, hab.2.a0, two.aEq]
        · rw [hab.1.a1, hab.2.a1, two.aEq]
        · rw [hab.1.a2, hab.2.a2]; exact two.a2
        · rw [hab.1.s6, hab.2.s6]) (by taint_decide))
      fun a b hab => ⟨WP.mono (sel_ok hp₁ hab.1) fun _ h => h.1,
        WP.mono (sel_ok hp₂ hab.2) fun _ h => h.1⟩) ?_
  exact taint_block [.s11] (fun a b hab => two.spE hab.1 hab.2)
    (fun a b hab r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact two.regs hab.1 hab.2) (by taint_decide)

end

/-! ## The outcome -/

theorem outcome {K : KemLay} (hK : K.WF) (s₀ : State) :
    Outcome (fun iters => decapsInternal K.p iters (DK K s₀) (CT K s₀))
      (if okEnc K.k (ρD K s₀) K.k then 1 else 0)
      (if CT K s₀ = C2 K s₀ then K1 K s₀ else KB K s₀) := by
  refine VG.Proof.MlKem.outcome_of_min ?_
  rw [show minIterations = 280 from rfl]
  cases hk : okEnc K.k (ρD K s₀) K.k
  · obtain ⟨i, hi, j, hj, hn⟩ := enc_none hk
    refine .inr ⟨rfl, ?_⟩
    rw [VG.Proof.MlKem.KPke.decapsInternal_eq, VG.Proof.MlKem.KPke.kpkeEncrypt_none hi hj hn]; rfl
  · refine .inl ⟨rfl, ?_⟩
    rw [VG.Proof.MlKem.KPke.decapsInternal_eq,
      VG.Proof.MlKem.KPke.kpkeEncrypt_some ⟨hK.η₁, hK.η₂⟩ (enc_some (r := R1 K s₀) hk)]
    rfl

theorem DK_eq (K : KemLay) (s₀ : State) : DK K s₀ = bytesAt s₀.mem (s₀.gpr .a0) K.dkLen := by
  simp only [DK, Lay.A, BitVec.add_zero]; rfl

theorem CT_eq (K : KemLay) (s₀ : State) : CT K s₀ = bytesAt s₀.mem (s₀.gpr .a1) K.ctLen := by
  simp only [CT, Lay.A, BitVec.add_zero]; rfl

/-! ## ML-KEM-768 -/

theorem pre_of {s : State} (h : (Spec.MlKem.decapsContract RISCV64.abi 1168).pre s) : Pre kl768 s := by
  sig_pre [Spec.MlKem.decapsContract, Spec.MlKem.decapsSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨al, h0, h1, h2, d1, d2, d3, d4, d5, b1, b2, b3, b4, f1, f2, f3, f4, alS⟩ := h
  exact ⟨kl768_wf, kl768_calls, al, h0, h1, h2, d1, d2, d3, d4, d5, b1, b2, b3, b4, f1, f2, f3, f4, alS⟩

theorem post_of {s₀ s : State}
    (h3 : s.gpr .a0 = if okEnc kl768.k (ρD kl768 s₀) kl768.k then 1 else 0)
    (hkey : bytesAt s.mem (pKey s₀) 32 =
      if CT kl768 s₀ = C2 kl768 s₀ then K1 kl768 s₀ else KB kl768 s₀) :
    (Spec.MlKem.decapsContract RISCV64.abi 1168).post s₀ s := by
  sig_post [Spec.MlKem.decapsContract, Spec.MlKem.decapsSig, RISCV64.abi, RISCV64.argRegs]
  have e : BitVec.setWidth 32
      (if okEnc kl768.k (ρD kl768 s₀) kl768.k then (1 : BitVec 64) else 0) =
      if okEnc kl768.k (ρD kl768 s₀) kl768.k then 1 else 0 := by
    cases okEnc kl768.k (ρD kl768 s₀) kl768.k <;> rfl
  have e0 : bytesAt s₀.mem (s₀.gpr .a0) 2400 = DK kl768 s₀ := (DK_eq kl768 s₀).symm
  have e1 : bytesAt s₀.mem (s₀.gpr .a1) 1088 = CT kl768 s₀ := (CT_eq kl768 s₀).symm
  rw [h3, e, hkey, e0, e1]
  exact outcome kl768_wf s₀

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a3 => 0x10000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 2400⟩, ⟨0x2000, 1088⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x10000, 32768⟩]

theorem verified :
    Verified RISCV64.target Impl.MlKem.RISCV64.decaps (Spec.MlKem.decapsContract RISCV64.abi 1168) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hlr, h3, hkey⟩ := correct (pre_of hs)
    exact ⟨t, s', he, ⟨hpres, hsp, hlr⟩, post_of h3 hkey⟩
  · have hp₁ := pre_of h₁
    have hp₂ := pre_of h₂
    sig_pub [Spec.MlKem.decapsContract, Spec.MlKem.decapsSig, RISCV64.abi, RISCV64.argRegs] at hpub
    obtain ⟨hsp, hl, g3, g4, g5, g6⟩ := hpub
    have hr : ρD kl768 s₁ = ρD kl768 s₂ := by
      rw [rhoD_eq, rhoD_eq, DK_eq, DK_eq]
      unfold leakRho at hl
      exact (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hl
    exact (all_ct ⟨hp₁, hp₂, hsp, g3, g4, g5, g6, hr⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.MlKem.decapsContract, Spec.MlKem.decapsSig, RISCV64.abi, RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | decide +kernel

end VG.Proof.MlKem.RISCV64.Decaps
