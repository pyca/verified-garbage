module

public import VerifiedGarbage.Impl.MlKem.RISCV64.Top
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.MlKem.RISCV64.Encrypt
public import VerifiedGarbage.Proof.MlKem.RISCV64.Lay
import VerifiedGarbage.Proof.MlKem.RISCV64.HashCT
import VerifiedGarbage.Proof.MlKem.RISCV64.PrfCT
import VerifiedGarbage.Proof.MlKem.RISCV64.RowCT
import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
import VerifiedGarbage.Proof.Framework.RISCV64.RelBlock

/-!
# ML-KEM on RISC-V: K-PKE.Encrypt in constant time

As on PPC64LE (`Proof/MlKem/PPC64LE/EncryptCT.lean`): two runs of `encrypt` on
the same buffers (`EncPre` of the same layout and `EB`) whose encapsulation
keys have the same `ρ` leak the same trace (`encrypt_ct`): the blocks access
no memory (`relct_noMem`), or only memory through the pointers (the taint
analyses of `KemLay.CallsOk`), the calls take the same pointers in both runs,
and the rows' `SampleNTT`s take the same seeds (`rowSum_ct`). What each run is
at each point comes from its correctness (`Encrypt.lean`).
-/

@[expose] public section

namespace VG.Proof.MlKem.RISCV64.Enc

open VG VG.RISCV64 VG.Impl.MlKem.RISCV64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-! ## Decoding `t̂` -/

theorem decT1_ok {K : KemLay} {L : Lay} {i o : Nat} {x s : State} (hc : Ctx L x)
    (g30 : x.gpr .s10 = L.A i o) {j : Nat} (hj : j < 4) (h : DecInv K L i o x j s) :
    WP isa (.block (atMul .a0 .s10 .s6 384 ++ slotAt .a1 .s6 0)) s fun s₁ =>
      Ctx L s₁ ∧ s₁.gpr .a0 = L.A i (o + 384 * j) ∧ s₁.gpr .a1 = L.A 0 (oPoly j) := by
  have hc' := h.kx.ctx (by decide) hc
  have g30' : s.gpr .s10 = L.A i o := by rw [h.kx.cs .s10 (by decide) (by decide), g30]
  refine WP.mono (decTArgs_ok (by omega) hc'.s11 g30' h.s6) fun s₁ ⟨o₁, a3, a4⟩ => ⟨hc'.only o₁, ?_, a4⟩
  rw [a3, ptr_add]

theorem decT_ctG {K : KemLay} (hK : K.WF) {L : Lay} {i o : Nat} {x y : State} (hcx : Ctx L x) (hcy : Ctx L y)
    (g30x : x.gpr .s10 = L.A i o) (g30y : y.gpr .s10 = L.A i o)
    (hs : sepAll L.sizes (i, o, 384 * K.k) [(0, 2048, 1024 * K.k)] = true) (hrx : L.buf i ∈ x.rd ++ x.wr)
    (hry : L.buf i ∈ y.rd ++ y.wr) {j : Nat} (hj : j < K.k) :
    RelCT isa (fun a₁ a₂ => DecInv K L i o x j a₁ ∧ DecInv K L i o y j a₂) K.decTBody fun a₁ a₂ =>
      (DecInv K L i o x (j + 1) a₁ ∧ (a₁.gpr .t0 != 0) = decide (j + 1 ≠ K.k)) ∧
      (DecInv K L i o y (j + 1) a₂ ∧ (a₂.gpr .t0 != 0) = decide (j + 1 ≠ K.k)) := by
  have hj4 : j < 4 := by have := hK.k4; omega
  refine relct_wp (RelCT.pointwise fun u w ⟨hu, hw⟩ => ?_) fun a₁ a₂ hab =>
    ⟨decT_step hK hcx g30x hs hrx hj hab.1, decT_step hK hcy g30y hs hry hj hab.2⟩
  refine RelCT.seq (R := fun (a₁ a₂ : State) =>
      (Ctx L a₁ ∧ a₁.gpr .a0 = L.A i (o + 384 * j) ∧ a₁.gpr .a1 = L.A 0 (oPoly j)) ∧
      (Ctx L a₂ ∧ a₂.gpr .a0 = L.A i (o + 384 * j) ∧ a₂.gpr .a1 = L.A 0 (oPoly j)))
    (relct_wp (relct_noMem (by rfl)) fun a₁ a₂ hab => ⟨by rw [hab.1]; exact decT1_ok hcx g30x hj4 hu,
      by rw [hab.2]; exact decT1_ok hcy g30y hj4 hw⟩) ?_
  exact RelCT.seq (R := fun _ _ => True)
    (RelCT.callT decode12T (regs2 fun a₁ a₂ hab => ⟨hab.1.1.sp_eq hab.2.1,
      by rw [hab.1.2.1, hab.2.2.1], by rw [hab.1.2.2, hab.2.2.2]⟩))
    (relct_noMem (by rfl))

section
variable {K : KemLay} {L : Lay} {b : EB} {s₀₁ s₀₂ : State} (hp₁ : EncPre K L b s₀₁) (hp₂ : EncPre K L b s₀₂)
include hp₁ hp₂

theorem decT_ct {x y : State} (ex : EA K L s₀₁ x) (ey : EA K L s₀₂ y) {j : Nat} (hj : j < K.k) :
    RelCT isa (fun a₁ a₂ => DecInv K L b.iE b.oE x j a₁ ∧ DecInv K L b.iE b.oE y j a₂) K.decTBody
      fun a₁ a₂ => (DecInv K L b.iE b.oE x (j + 1) a₁ ∧ (a₁.gpr .t0 != 0) = decide (j + 1 ≠ K.k)) ∧
        (DecInv K L b.iE b.oE y (j + 1) a₂ ∧ (a₂.gpr .t0 != 0) = decide (j + 1 ≠ K.k)) := by
  obtain ⟨hcx, g30x, hsx, hrx⟩ := dec_pre hp₁ ex
  obtain ⟨hcy, g30y, -, hry⟩ := dec_pre hp₂ ey
  exact decT_ctG hp₁.wf hcx hcy g30x g30y hsx hrx hry hj

/-! ## The rows of `u` -/

theorem encRow_ct (hρ : ρE K L b s₀₁ = ρE K L b s₀₂) {i : Nat} (hi : i < K.k) :
    RelCT isa (fun a b' => ERow K L b s₀₁ i a ∧ ERow K L b s₀₂ i b') K.encRowBody fun a b' =>
      (ERow K L b s₀₁ (i + 1) a ∧ (a.gpr .t0 != 0) = decide (i + 1 ≠ K.k)) ∧
      (ERow K L b s₀₂ (i + 1) b' ∧ (b'.gpr .t0 != 0) = decide (i + 1 ≠ K.k)) := by
  refine relct_wp (RelCT.pointwise fun u w ⟨hu, hw⟩ => ?_) fun a b' hab =>
    ⟨encRow_step hp₁ hi hab.1, encRow_step hp₂ hi hab.2⟩
  have pw : RowPre K L (ρE K L b s₀₁) (VG.Proof.MlKem.encY (rB L s₀₂)) i (okE K L b s₀₂ i) w := by
    have := hw.rowPre hp₂ hi; rwa [← hρ] at this
  -- `RowSum`
  refine RelCT.seq (R := fun (a b' : State) =>
      RowInv K L true (ρE K L b s₀₁) (VG.Proof.MlKem.encY (rB L s₀₁)) i (okE K L b s₀₁ i) u K.k a ∧
      RowInv K L true (ρE K L b s₀₂) (VG.Proof.MlKem.encY (rB L s₀₂)) i (okE K L b s₀₂ i) w K.k b')
    (relct_wp (rowSum_ct hp₁.calls (hu.rowPre hp₁ hi) pw) fun a b' hab =>
      ⟨by rw [hab.1]; exact rowSum_ok (hu.rowPre hp₁ hi),
        by rw [hab.2]; exact rowSum_ok (hw.rowPre hp₂ hi)⟩) ?_
  -- `NTT⁻¹`
  refine RelCT.seq (R := fun (a b' : State) =>
      (RB K L b s₀₁ i u (VG.Proof.MlKem.KPke.dotK (fun j => aE K L b s₀₁ j i)
          (VG.Proof.MlKem.encY (rB L s₀₁)) K.k) a ∧
        a.gpr .a0 = L.A 0 K.oAcc ∧ a.gpr .a1 = L.A 0 K.oNtt) ∧
      (RB K L b s₀₂ i w (VG.Proof.MlKem.KPke.dotK (fun j => aE K L b s₀₂ j i)
          (VG.Proof.MlKem.encY (rB L s₀₂)) K.k) b' ∧
        b'.gpr .a0 = L.A 0 K.oAcc ∧ b'.gpr .a1 = L.A 0 K.oNtt))
    (relct_wp (relct_noMem (by rfl)) fun a b' hab => ⟨er2_ok hp₁ hu hab.1, er2_ok hp₂ hw hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b' : State) =>
      RB K L b s₀₁ i u (nttInv (VG.Proof.MlKem.KPke.dotK (fun j => aE K L b s₀₁ j i)
        (VG.Proof.MlKem.encY (rB L s₀₁)) K.k)) a ∧
      RB K L b s₀₂ i w (nttInv (VG.Proof.MlKem.KPke.dotK (fun j => aE K L b s₀₂ j i)
        (VG.Proof.MlKem.encY (rB L s₀₂)) K.k)) b')
    (relct_wp (RelCT.callT nttInvT (regs2 fun a b' hab =>
      ⟨(hab.1.1.ctx hp₁ hu).sp_eq (hab.2.1.ctx hp₂ hw), by rw [hab.1.2.1, hab.2.2.1],
        by rw [hab.1.2.2, hab.2.2.2]⟩))
      fun a b' hab => ⟨er3_ok hp₁ hu hab.1.1 hab.1.2.1 hab.1.2.2,
        er3_ok hp₂ hw hab.2.1 hab.2.2.1 hab.2.2.2⟩) ?_
  -- `+ e₁[i]`
  refine RelCT.seq (R := fun (a b' : State) =>
      (RB K L b s₀₁ i u (nttInv (VG.Proof.MlKem.KPke.dotK (fun j => aE K L b s₀₁ j i)
          (VG.Proof.MlKem.encY (rB L s₀₁)) K.k)) a ∧
        a.gpr .a0 = L.A 0 K.oAcc ∧ a.gpr .a1 = L.A 0 (oPoly (K.k + (K.k + i)))) ∧
      (RB K L b s₀₂ i w (nttInv (VG.Proof.MlKem.KPke.dotK (fun j => aE K L b s₀₂ j i)
          (VG.Proof.MlKem.encY (rB L s₀₂)) K.k)) b' ∧
        b'.gpr .a0 = L.A 0 K.oAcc ∧ b'.gpr .a1 = L.A 0 (oPoly (K.k + (K.k + i)))))
    (relct_wp (relct_noMem (by rfl)) fun a b' hab =>
      ⟨er4_ok hp₁ hi hu hab.1, er4_ok hp₂ hi hw hab.2⟩) ?_
  refine RelCT.seq (R := fun (a b' : State) =>
      RB K L b s₀₁ i u (VG.Proof.MlKem.KPke.encU K.p (aE K L b s₀₁) (rB L s₀₁) i) a ∧
      RB K L b s₀₂ i w (VG.Proof.MlKem.KPke.encU K.p (aE K L b s₀₂) (rB L s₀₂) i) b')
    (relct_wp (RelCT.callT addT (regs2 fun a b' hab =>
      ⟨(hab.1.1.ctx hp₁ hu).sp_eq (hab.2.1.ctx hp₂ hw), by rw [hab.1.2.1, hab.2.2.1],
        by rw [hab.1.2.2, hab.2.2.2]⟩))
      fun a b' hab => ⟨er5_ok hp₁ hi hu hab.1.1 hab.1.2.1 hab.1.2.2,
        er5_ok hp₂ hi hw hab.2.1 hab.2.2.1 hab.2.2.2⟩) ?_
  -- its encoding
  refine RelCT.seq (R := fun (a b' : State) =>
      (RB K L b s₀₁ i u (VG.Proof.MlKem.KPke.encU K.p (aE K L b s₀₁) (rB L s₀₁) i) a ∧
        a.gpr .a0 = L.A 0 K.oAcc ∧ a.gpr .a1 = BitVec.ofNat 64 K.du ∧
        a.gpr .a2 = L.A b.iC (b.oC + K.uLen * i) ∧ a.gpr .a3 = BitVec.ofNat 64 (32 * K.du)) ∧
      (RB K L b s₀₂ i w (VG.Proof.MlKem.KPke.encU K.p (aE K L b s₀₂) (rB L s₀₂) i) b' ∧
        b'.gpr .a0 = L.A 0 K.oAcc ∧ b'.gpr .a1 = BitVec.ofNat 64 K.du ∧
        b'.gpr .a2 = L.A b.iC (b.oC + K.uLen * i) ∧ b'.gpr .a3 = BitVec.ofNat 64 (32 * K.du)))
    (relct_wp (relct_noMem (by rfl)) fun a b' hab => ⟨er6_ok hp₁ hu hab.1, er6_ok hp₂ hw hab.2⟩) ?_
  exact RelCT.seq (R := fun _ _ => True)
    (RelCT.callT hp₁.calls.cuT (regs4 fun a b' hab =>
      ⟨(hab.1.1.ctx hp₁ hu).sp_eq (hab.2.1.ctx hp₂ hw), by rw [hab.1.2.1, hab.2.2.1],
        by rw [hab.1.2.2.1, hab.2.2.2.1], by rw [hab.1.2.2.2.1, hab.2.2.2.2.1],
        by rw [hab.1.2.2.2.2, hab.2.2.2.2.2]⟩))
    (relct_noMem (by rfl))

/-! ## `v` -/

theorem v_ct {x y : State} (hx : VEnv K L b s₀₁ x) (hy : VEnv K L b s₀₂ y) :
    RelCT isa (fun a b' => a = x ∧ b' = y)
      (.seq K.dot <|
      .seq (.block (polyAddr .a0 K.jAcc ++ polyAddr .a1 K.jNtt)) <|
      .seq callNttInv <|
      .seq (.block (polyAddr .a0 K.jAcc ++ polyAddr .a1 (3 * K.k))) <|
      .seq callAdd <|
      .seq (.block (polyAddr .a0 K.jAcc ++ polyAddr .a1 (3 * K.k + 1))) <|
      .seq callAdd <|
      .seq (.block (polyAddr .a0 K.jAcc ++ [.li .a1 K.dv, .addi .a2 .s7 (K.uLen * K.k), .li .a3 K.vLen]))
        K.callCU)
      fun _ _ => True := by
  have hK := hp₁.wf
  have hcx := hx.kx.ctx (by decide) hp₁.ctx
  have hcy := hy.kx.ctx (by decide) hp₂.ctx
  have va : ∀ {s₀ s : State}, VEnv K L b s₀ s → ∀ j < K.k,
      PolyIs s.mem (L.A 0 (oPoly j)) (VG.Proof.MlKem.ekT (ekB K L b s₀) j) := fun h j hj => by
    have := h.d.v j (by omega); simp only [hj, ↓reduceIte] at this; exact this
  have vv : ∀ {s₀ s : State}, VEnv K L b s₀ s → ∀ j < K.k,
      PolyIs s.mem (L.A 0 (oPoly (K.k + j))) (VG.Proof.MlKem.encY (rB L s₀) j) := fun h j hj => by
    have := h.d.v (K.k + j) (by omega)
    have e : ¬ (K.k + j < K.k) := by omega
    simp only [e, ↓reduceIte, show K.k + j - K.k = j by omega] at this
    exact this
  -- `dot`
  refine RelCT.seq (R := fun (a b' : State) =>
      (VEnv K L b s₀₁ a ∧ PolyIs a.mem (L.A 0 K.oAcc) (VG.Proof.MlKem.KPke.dotK
        (VG.Proof.MlKem.ekT (ekB K L b s₀₁)) (VG.Proof.MlKem.encY (rB L s₀₁)) K.k)) ∧
      (VEnv K L b s₀₂ b' ∧ PolyIs b'.mem (L.A 0 K.oAcc) (VG.Proof.MlKem.KPke.dotK
        (VG.Proof.MlKem.ekT (ekB K L b s₀₂)) (VG.Proof.MlKem.encY (rB L s₀₂)) K.k)))
    (relct_wp (dot_ct hK hcx hcy (va hx) (vv hx) (va hy) (vv hy) hp₁.calls) fun a b' hab =>
      ⟨by rw [hab.1]; exact ev1_ok hp₁ hx, by rw [hab.2]; exact ev1_ok hp₂ hy⟩) ?_
  -- `NTT⁻¹`
  refine RelCT.seq (R := fun (a b' : State) =>
      ((VEnv K L b s₀₁ a ∧ PolyIs a.mem (L.A 0 K.oAcc) (VG.Proof.MlKem.KPke.dotK
          (VG.Proof.MlKem.ekT (ekB K L b s₀₁)) (VG.Proof.MlKem.encY (rB L s₀₁)) K.k)) ∧
        a.gpr .a0 = L.A 0 K.oAcc ∧ a.gpr .a1 = L.A 0 K.oNtt) ∧
      ((VEnv K L b s₀₂ b' ∧ PolyIs b'.mem (L.A 0 K.oAcc) (VG.Proof.MlKem.KPke.dotK
          (VG.Proof.MlKem.ekT (ekB K L b s₀₂)) (VG.Proof.MlKem.encY (rB L s₀₂)) K.k)) ∧
        b'.gpr .a0 = L.A 0 K.oAcc ∧ b'.gpr .a1 = L.A 0 K.oNtt))
    (relct_wp (relct_noMem (by rfl)) fun a b' hab =>
      ⟨evArgs_ok hp₁ hab.1.1 hab.1.2 (by offs), evArgs_ok hp₂ hab.2.1 hab.2.2 (by offs)⟩) ?_
  refine RelCT.seq (R := fun (a b' : State) =>
      (VEnv K L b s₀₁ a ∧ PolyIs a.mem (L.A 0 K.oAcc) (nttInv (VG.Proof.MlKem.KPke.dotK
        (VG.Proof.MlKem.ekT (ekB K L b s₀₁)) (VG.Proof.MlKem.encY (rB L s₀₁)) K.k))) ∧
      (VEnv K L b s₀₂ b' ∧ PolyIs b'.mem (L.A 0 K.oAcc) (nttInv (VG.Proof.MlKem.KPke.dotK
        (VG.Proof.MlKem.ekT (ekB K L b s₀₂)) (VG.Proof.MlKem.encY (rB L s₀₂)) K.k))))
    (relct_wp (RelCT.callT nttInvT (regs2 fun a b' hab =>
      ⟨(hab.1.1.1.kx.ctx (by decide) hp₁.ctx).sp_eq (hab.2.1.1.kx.ctx (by decide) hp₂.ctx),
        by rw [hab.1.2.1, hab.2.2.1], by rw [hab.1.2.2, hab.2.2.2]⟩))
      fun a b' hab => ⟨ev3_ok hp₁ hab.1.1 hab.1.2.1 hab.1.2.2,
        ev3_ok hp₂ hab.2.1 hab.2.2.1 hab.2.2.2⟩) ?_
  -- `+ e₂`
  refine RelCT.seq (R := fun (a b' : State) =>
      ((VEnv K L b s₀₁ a ∧ PolyIs a.mem (L.A 0 K.oAcc) (nttInv (VG.Proof.MlKem.KPke.dotK
          (VG.Proof.MlKem.ekT (ekB K L b s₀₁)) (VG.Proof.MlKem.encY (rB L s₀₁)) K.k))) ∧
        a.gpr .a0 = L.A 0 K.oAcc ∧ a.gpr .a1 = L.A 0 (oPoly (3 * K.k))) ∧
      ((VEnv K L b s₀₂ b' ∧ PolyIs b'.mem (L.A 0 K.oAcc) (nttInv (VG.Proof.MlKem.KPke.dotK
          (VG.Proof.MlKem.ekT (ekB K L b s₀₂)) (VG.Proof.MlKem.encY (rB L s₀₂)) K.k))) ∧
        b'.gpr .a0 = L.A 0 K.oAcc ∧ b'.gpr .a1 = L.A 0 (oPoly (3 * K.k))))
    (relct_wp (relct_noMem (by rfl)) fun a b' hab =>
      ⟨evArgs_ok hp₁ hab.1.1 hab.1.2 (by offs), evArgs_ok hp₂ hab.2.1 hab.2.2 (by offs)⟩) ?_
  have e₂ : ∀ {s₀ s : State}, VEnv K L b s₀ s →
      PolyIs s.mem (L.A 0 (oPoly (3 * K.k))) (VG.Proof.MlKem.cbd (rB L s₀) (2 * K.k)) := fun h => by
    have := h.d.e (2 * K.k) (by omega) (by omega)
    rwa [show K.k + 2 * K.k = 3 * K.k by omega] at this
  refine RelCT.seq (R := fun (a b' : State) =>
      (VEnv K L b s₀₁ a ∧ PolyIs a.mem (L.A 0 K.oAcc)
        (add (nttInv (VG.Proof.MlKem.KPke.dotK (VG.Proof.MlKem.ekT (ekB K L b s₀₁))
          (VG.Proof.MlKem.encY (rB L s₀₁)) K.k)) (VG.Proof.MlKem.cbd (rB L s₀₁) (2 * K.k)))) ∧
      (VEnv K L b s₀₂ b' ∧ PolyIs b'.mem (L.A 0 K.oAcc)
        (add (nttInv (VG.Proof.MlKem.KPke.dotK (VG.Proof.MlKem.ekT (ekB K L b s₀₂))
          (VG.Proof.MlKem.encY (rB L s₀₂)) K.k)) (VG.Proof.MlKem.cbd (rB L s₀₂) (2 * K.k)))))
    (relct_wp (RelCT.callT addT (regs2 fun a b' hab =>
      ⟨(hab.1.1.1.kx.ctx (by decide) hp₁.ctx).sp_eq (hab.2.1.1.kx.ctx (by decide) hp₂.ctx),
        by rw [hab.1.2.1, hab.2.2.1], by rw [hab.1.2.2, hab.2.2.2]⟩))
      fun a b' hab => ⟨evAdd_ok hp₁ (.inl rfl) hab.1.1 (e₂ hab.1.1.1) hab.1.2.1 hab.1.2.2,
        evAdd_ok hp₂ (.inl rfl) hab.2.1 (e₂ hab.2.1.1) hab.2.2.1 hab.2.2.2⟩) ?_
  -- `+ μ`
  refine RelCT.seq (R := fun (a b' : State) =>
      ((VEnv K L b s₀₁ a ∧ PolyIs a.mem (L.A 0 K.oAcc)
          (add (nttInv (VG.Proof.MlKem.KPke.dotK (VG.Proof.MlKem.ekT (ekB K L b s₀₁))
            (VG.Proof.MlKem.encY (rB L s₀₁)) K.k)) (VG.Proof.MlKem.cbd (rB L s₀₁) (2 * K.k)))) ∧
        a.gpr .a0 = L.A 0 K.oAcc ∧ a.gpr .a1 = L.A 0 (oPoly (3 * K.k + 1))) ∧
      ((VEnv K L b s₀₂ b' ∧ PolyIs b'.mem (L.A 0 K.oAcc)
          (add (nttInv (VG.Proof.MlKem.KPke.dotK (VG.Proof.MlKem.ekT (ekB K L b s₀₂))
            (VG.Proof.MlKem.encY (rB L s₀₂)) K.k)) (VG.Proof.MlKem.cbd (rB L s₀₂) (2 * K.k)))) ∧
        b'.gpr .a0 = L.A 0 K.oAcc ∧ b'.gpr .a1 = L.A 0 (oPoly (3 * K.k + 1))))
    (relct_wp (relct_noMem (by rfl)) fun a b' hab =>
      ⟨evArgs_ok hp₁ hab.1.1 hab.1.2 (by offs), evArgs_ok hp₂ hab.2.1 hab.2.2 (by offs)⟩) ?_
  refine RelCT.seq (R := fun (a b' : State) =>
      (VEnv K L b s₀₁ a ∧ PolyIs a.mem (L.A 0 K.oAcc)
        (VG.Proof.MlKem.KPke.encV K.p (ekB K L b s₀₁) (mB L b s₀₁) (rB L s₀₁))) ∧
      (VEnv K L b s₀₂ b' ∧ PolyIs b'.mem (L.A 0 K.oAcc)
        (VG.Proof.MlKem.KPke.encV K.p (ekB K L b s₀₂) (mB L b s₀₂) (rB L s₀₂))))
    (relct_wp (RelCT.callT addT (regs2 fun a b' hab =>
      ⟨(hab.1.1.1.kx.ctx (by decide) hp₁.ctx).sp_eq (hab.2.1.1.kx.ctx (by decide) hp₂.ctx),
        by rw [hab.1.2.1, hab.2.2.1], by rw [hab.1.2.2, hab.2.2.2]⟩))
      fun a b' hab => ⟨evAdd_ok hp₁ (.inr rfl) hab.1.1 hab.1.1.1.d.mu hab.1.2.1 hab.1.2.2,
        evAdd_ok hp₂ (.inr rfl) hab.2.1 hab.2.1.1.d.mu hab.2.2.1 hab.2.2.2⟩) ?_
  -- its encoding
  refine RelCT.seq (R := fun (a b' : State) =>
      (Ctx L a ∧ a.gpr .a0 = L.A 0 K.oAcc ∧ a.gpr .a1 = BitVec.ofNat 64 K.dv ∧
        a.gpr .a2 = L.A b.iC (b.oC + K.uLen * K.k) ∧ a.gpr .a3 = BitVec.ofNat 64 (32 * K.dv)) ∧
      (Ctx L b' ∧ b'.gpr .a0 = L.A 0 K.oAcc ∧ b'.gpr .a1 = BitVec.ofNat 64 K.dv ∧
        b'.gpr .a2 = L.A b.iC (b.oC + K.uLen * K.k) ∧ b'.gpr .a3 = BitVec.ofNat 64 (32 * K.dv)))
    (relct_wp (relct_noMem (by rfl)) fun a b' hab =>
      ⟨WP.mono (ev8_ok hp₁ hab.1) fun _ h =>
          ⟨h.1.1.kx.ctx (by decide) hp₁.ctx, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩,
        WP.mono (ev8_ok hp₂ hab.2) fun _ h =>
          ⟨h.1.1.kx.ctx (by decide) hp₂.ctx, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩⟩) ?_
  exact RelCT.callT hp₁.calls.cuT (regs4 fun a b' hab =>
    ⟨hab.1.1.sp_eq hab.2.1, by rw [hab.1.2.1, hab.2.2.1], by rw [hab.1.2.2.1, hab.2.2.2.1],
      by rw [hab.1.2.2.2.1, hab.2.2.2.2.1], by rw [hab.1.2.2.2.2, hab.2.2.2.2.2]⟩)

/-! ## The whole of K-PKE.Encrypt -/

theorem encrypt_ct (hρ : ρE K L b s₀₁ = ρE K L b s₀₂) :
    RelCT isa (fun a c => a = s₀₁ ∧ c = s₀₂) K.encrypt fun _ _ => True := by
  have hK := hp₁.wf
  -- `ρ`
  refine RelCT.seq (R := fun (a c : State) =>
      (EA K L s₀₁ a ∧ Frame (L.RL [(0, oSeed, 32)]) s₀₁.mem a.mem ∧
        bytesAt a.mem (L.A 0 oSeed) 32 = ρE K L b s₀₁) ∧
      (EA K L s₀₂ c ∧ Frame (L.RL [(0, oSeed, 32)]) s₀₂.mem c.mem ∧
        bytesAt c.mem (L.A 0 oSeed) 32 = ρE K L b s₀₂))
    (relct_wp (hp₁.calls.encSeedT.relct (fun a c hac => by
        rw [hac.1, hac.2, hp₁.ctx.sp_eq hp₂.ctx]) (fun a c hac r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [hac.1, hac.2, hp₁.s10, hp₂.s10]
        · rw [hac.1, hac.2, hp₁.ctx.s11, hp₂.ctx.s11]))
      fun a c hac => ⟨by rw [hac.1]; exact enc1_ok hp₁, by rw [hac.2]; exact enc1_ok hp₂⟩) ?_
  refine RelCT.pointwise fun x y ⟨⟨ex, _, ρx⟩, ⟨ey, _, ρy⟩⟩ => ?_
  -- `t̂`
  refine RelCT.seq (R := fun (a c : State) => DecInv K L b.iE b.oE x 0 a ∧ DecInv K L b.iE b.oE y 0 c)
    (relct_wp (relct_noMem (by rfl)) fun a c hac =>
      ⟨by rw [hac.1]; exact decT_init, by rw [hac.2]; exact decT_init⟩) ?_
  refine RelCT.seq (R := fun (a c : State) => DecInv K L b.iE b.oE x K.k a ∧ DecInv K L b.iE b.oE y K.k c)
    (relct_loop_nz (N := K.k) (by have := hK.k1; omega) fun j hj => decT_ct hp₁ hp₂ ex ey hj) ?_
  -- `ŷ`
  refine RelCT.seq (R := fun (a c : State) =>
      (EA K L s₀₁ a ∧ bytesAt a.mem (L.A 0 oSeed) 32 = ρE K L b s₀₁ ∧
        (∀ k < K.k, PolyIs a.mem (L.A 0 (oPoly k)) (VG.Proof.MlKem.ekT (ekB K L b s₀₁) k)) ∧
        ∀ j < K.k, PolyIs a.mem (L.A 0 (oPoly (K.k + j))) (VG.Proof.MlKem.encY (rB L s₀₁) j)) ∧
      (EA K L s₀₂ c ∧ bytesAt c.mem (L.A 0 oSeed) 32 = ρE K L b s₀₂ ∧
        (∀ k < K.k, PolyIs c.mem (L.A 0 (oPoly k)) (VG.Proof.MlKem.ekT (ekB K L b s₀₂) k)) ∧
        ∀ j < K.k, PolyIs c.mem (L.A 0 (oPoly (K.k + j))) (VG.Proof.MlKem.encY (rB L s₀₂) j)))
    (relct_wp (RelCT.pointwise fun a c hac =>
      prfLoop_ct hK (L := L) true (N₀ := 0) (N₁ := K.k) (by have := hK.k1; omega) (by omega)
        (EA.ctx hp₁ (enc2_ok hp₁ ex ρx hac.1).1) (EA.ctx hp₂ (enc2_ok hp₂ ey ρy hac.2).1) rfl rfl)
      fun a c hac =>
        ⟨let ⟨e, ρ', t⟩ := enc2_ok hp₁ ex ρx hac.1; enc3_ok hp₁ e ρ' t,
          let ⟨e, ρ', t⟩ := enc2_ok hp₂ ey ρy hac.2; enc3_ok hp₂ e ρ' t⟩) ?_
  -- `e₁` and `e₂`
  refine RelCT.seq (R := fun (a c : State) =>
      (EA K L s₀₁ a ∧ bytesAt a.mem (L.A 0 oSeed) 32 = ρE K L b s₀₁ ∧
        (∀ k < 2 * K.k, PolyIs a.mem (L.A 0 (oPoly k)) (if k < K.k then VG.Proof.MlKem.ekT (ekB K L b s₀₁) k
          else VG.Proof.MlKem.encY (rB L s₀₁) (k - K.k))) ∧
        ∀ N, K.k ≤ N → N < 2 * K.k + 1 →
          PolyIs a.mem (L.A 0 (oPoly (K.k + N))) (VG.Proof.MlKem.cbd (rB L s₀₁) N)) ∧
      (EA K L s₀₂ c ∧ bytesAt c.mem (L.A 0 oSeed) 32 = ρE K L b s₀₂ ∧
        (∀ k < 2 * K.k, PolyIs c.mem (L.A 0 (oPoly k)) (if k < K.k then VG.Proof.MlKem.ekT (ekB K L b s₀₂) k
          else VG.Proof.MlKem.encY (rB L s₀₂) (k - K.k))) ∧
        ∀ N, K.k ≤ N → N < 2 * K.k + 1 →
          PolyIs c.mem (L.A 0 (oPoly (K.k + N))) (VG.Proof.MlKem.cbd (rB L s₀₂) N)))
    (relct_wp (RelCT.pointwise fun a c hac =>
      prfLoop_ct hK (L := L) false (N₀ := K.k) (N₁ := 2 * K.k + 1) (by omega) (by omega)
        (EA.ctx hp₁ hac.1.1) (EA.ctx hp₂ hac.2.1) rfl rfl)
      fun a c hac => ⟨enc4_ok hp₁ hac.1.1 hac.1.2.1 (v_of hac.1.2.2.1 hac.1.2.2.2),
        enc4_ok hp₂ hac.2.1 hac.2.2.1 (v_of hac.2.2.2.1 hac.2.2.2.2)⟩) ?_
  -- `μ`
  refine RelCT.pointwise fun x₄ y₄ ⟨⟨e₄, ρ₄, v₄, E₄⟩, ⟨e₄', ρ₄', v₄', E₄'⟩⟩ => ?_
  refine RelCT.seq (R := fun (a c : State) =>
      ((EA K L s₀₁ a ∧ a.mem = x₄.mem) ∧ a.gpr .a0 = L.A b.iM b.oM ∧
        a.gpr .a1 = BitVec.ofNat 64 (32 * 1) ∧ a.gpr .a2 = BitVec.ofNat 64 1 ∧
        a.gpr .a3 = L.A 0 (oPoly (3 * K.k + 1))) ∧
      ((EA K L s₀₂ c ∧ c.mem = y₄.mem) ∧ c.gpr .a0 = L.A b.iM b.oM ∧
        c.gpr .a1 = BitVec.ofNat 64 (32 * 1) ∧ c.gpr .a2 = BitVec.ofNat 64 1 ∧
        c.gpr .a3 = L.A 0 (oPoly (3 * K.k + 1))))
    (relct_wp (relct_noMem (by rfl)) fun a c hac =>
      ⟨by rw [hac.1]; exact enc5a_ok hp₁ e₄, by rw [hac.2]; exact enc5a_ok hp₂ e₄'⟩) ?_
  refine RelCT.seq (R := fun (a c : State) =>
      (EA K L s₀₁ a ∧ Frame (L.RL [(0, oPoly (3 * K.k + 1), 1024)]) x₄.mem a.mem ∧
        PolyIs a.mem (L.A 0 (oPoly (3 * K.k + 1))) (decodeDecompress 1 (mB L b s₀₁))) ∧
      (EA K L s₀₂ c ∧ Frame (L.RL [(0, oPoly (3 * K.k + 1), 1024)]) y₄.mem c.mem ∧
        PolyIs c.mem (L.A 0 (oPoly (3 * K.k + 1))) (decodeDecompress 1 (mB L b s₀₂))))
    (relct_wp (RelCT.callT decompressT (regs4 fun a c hac =>
      ⟨(EA.ctx hp₁ hac.1.1.1).sp_eq (EA.ctx hp₂ hac.2.1.1), by rw [hac.1.2.1, hac.2.2.1],
        by rw [hac.1.2.2.1, hac.2.2.2.1], by rw [hac.1.2.2.2.1, hac.2.2.2.2.1],
        by rw [hac.1.2.2.2.2, hac.2.2.2.2.2]⟩))
      fun a c hac => ⟨enc5b_ok hp₁ e₄ hac.1.1 hac.1.2.1 hac.1.2.2.1 hac.1.2.2.2.1 hac.1.2.2.2.2,
        enc5b_ok hp₂ e₄' hac.2.1 hac.2.2.1 hac.2.2.2.1 hac.2.2.2.2.1 hac.2.2.2.2.2⟩) ?_
  -- the rows of `u`
  refine RelCT.seq (R := fun (a c : State) => ERow K L b s₀₁ 0 a ∧ ERow K L b s₀₂ 0 c)
    (relct_wp (relct_noMem (by rfl)) fun a c hac =>
      ⟨rows_init hp₁ hac.1.1 (data5 hp₁ ρ₄ v₄ E₄ hac.1.2.1 hac.1.2.2),
        rows_init hp₂ hac.2.1 (data5 hp₂ ρ₄' v₄' E₄' hac.2.2.1 hac.2.2.2)⟩) ?_
  refine RelCT.seq (R := fun (a c : State) => ERow K L b s₀₁ K.k a ∧ ERow K L b s₀₂ K.k c)
    (relct_loop_nz (N := K.k) (by have := hK.k1; omega) fun i hi => encRow_ct hp₁ hp₂ hρ hi) ?_
  -- `v`
  exact RelCT.pointwise fun x₇ y₇ ⟨h₇, h₇'⟩ => v_ct hp₁ hp₂ h₇.venv h₇'.venv

end

end VG.Proof.MlKem.RISCV64.Enc
