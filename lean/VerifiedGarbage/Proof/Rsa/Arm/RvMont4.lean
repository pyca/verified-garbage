module

public import VerifiedGarbage.Proof.Rsa.Arm.RvMont3
public import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeState
public import VerifiedGarbage.Proof.Rsa.Arm.RvMont
public import VerifiedGarbage.Proof.Rsa.Arm.RvStage
import VerifiedGarbage.Proof.Bignum.Arm.SetupCT
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeCT
import VerifiedGarbage.Proof.Rsa.Arm.CvFail
import VerifiedGarbage.Proof.Bignum.Arm.Precompute
import VerifiedGarbage.Proof.Bignum.Arm.Setup
import VerifiedGarbage.Proof.Framework.Offset

/-! # `vg_rsa_recover_primes` on ARMv7: Montgomery multiplication's working space set up

`setup`, then `n` and `R² mod n` by `precompute` (`montB_vp`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt wOf Layout)

/-- `R² mod n`. -/
abbrev R2v (P : RP) : Nat := 2 ^ (128 * P.w6) % P.n

/-- The stage `K01` but for `r8`. -/
abbrev R01 (P : RP) (σ : State) (s : State) (keepHalves : Bool := true) : Prop :=
  KR P σ (A01 P σ) live01 (AWh P σ P.c) (montWide keepHalves) (Vh P σ P.c) (montSlots keepHalves) s

section
variable {P : RP}

theorem In.r0F_rM {σ : State} (pre : In P σ) : P.r0F.Disjoint P.rM :=
  (pre.sF.symm.sub_left (Offset.sub_base (State.addr P.sp) (d := 0) (n := 4) (k := 88) (by decide) |>
    fun h => by simpa using h)).sub_right (rM_sub pre.sizes pre.fS)

theorem In.workspaceM {σ s : State} (pre : In P σ) (wr : s.wr = σ.wr) : Workspace s P.M0 (8 * P.lenM) := by
  have sz := pre.sizes
  have hf := pre.fS
  refine ⟨?_, by rw [wr, pre.wr]; simp⟩
  rw [M0_toNat sz hf, Nat.add_assoc, sz.endM]
  have := Nat.le_trans (arr_mono (w := P.w) (show mBase + 8 ≤ nArr by decide)) sz.fits
  simp only [RP.Z] at hf this ⊢; omega

theorem Bs.nB {σ s : State} (h : Bs P σ s) : Spec.Rsa.bytesAt s.mem (State.addr P.nP) P.K = P.nB := by
  have pre := h.pre
  rw [VG.Proof.Rsa.Arm.CrtValues.bytes_frame h.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact pre.sN.symm
    · exact pre.nF.sub_right (Offset.sub_base (State.addr P.sp) (d := 0) (n := 4) (k := 56) (by decide) |>
        fun d => by simpa using d)) (by have := pre.k2; omega), pre.nB]

theorem fitsM : arrAt P.w6 8 ≤ 8 * P.lenM := by
  simp only [arrAt, Proof.Rsa.Mont.hdrBytes, RP.lenM]; omega

/-- `setup`. -/
theorem setup_vp {E : State → Prop} (keepHalves : Bool := true) :
    VP (fun σ s => E σ ∧ K01 P σ s keepHalves ∧ s.gpr .r0 = P.M0 ∧ s.gpr .r7 = BitVec.ofNat 32 P.w6 ∧ s.gpr .r3 = 0 ∧
        s.mem.readW (State.addr P.sp) 32 = P.M0) VG.Impl.Bignum.Arm.setup
      (fun σ s => E σ ∧ R01 P σ s keepHalves ∧ Layout s.mem (State.addr P.M0) P.lenM ∧ wOf s.mem (State.addr P.M0) = P.w6 ∧
        s.gpr .r0 = P.M0 ∧ s.mem.readW (State.addr P.sp) 32 = P.M0) := by
  refine VP.of_ct (fun σ₁ σ₂ s t tr1 tr2 u v h e1 e2 =>
    ⟨setup_ct s t tr1 tr2 u v trivial trivial (h.1.2.2.1.trans h.2.2.2.1.symm) e1 e2, trivial⟩)
    fun σ s ⟨e, h, r0, r7, r3, sv⟩ => ?_
  have pre := h.bs.pre
  have sz := pre.sizes
  have hf := pre.fS
  refine WP.mono (setup_ok s (pre.workspaceM h.bs.wr) (by have := sz.w6a; omega) (by have := sz.w6b; omega)
    fitsM r0 r7 r3) fun t ⟨lay, wd, t0, outs, rest⟩ => ⟨e, ?_, lay, wd, t0, ?_⟩
  · have f := frameM_of_outs outs (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;>
      simp only [RP.lenM] <;> omega)
    exact h.toR.keep (keepM sz hf f) (by decide) (by decide) (by cases keepHalves <;> decide) rest.sp rest.rd rest.wr
  · have f := frameM_of_outs outs (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;>
      simp only [RP.lenM] <;> omega)
    rw [← sv]
    exact f.readW (r := P.r0F) (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact pre.r0F_rM) (by decide)

/-- The stage before `precompute`. -/
abbrev PreP (P : RP) (σ s : State) (keepHalves : Bool := true) : Prop :=
  R01 P σ s keepHalves ∧ Layout s.mem (State.addr P.M0) P.lenM ∧ wOf s.mem (State.addr P.M0) = P.w6 ∧
    s.gpr .r0 = P.M0 ∧ s.mem.readW (State.addr P.sp) 32 = P.M0 ∧ s.gpr .r4 = P.nP ∧
    s.gpr .r6 = BitVec.ofNat 32 P.K

theorem preP_input {keepHalves : Bool} {σ s : State} (hn : P.n % 2 = 1 ∧ 1 < P.n) (h : PreP P σ s keepHalves) :
    PrecomputeInput P.M0 P.nP P.lenM P.w6 P.K s := by
  obtain ⟨k, lay, wd, r0, sv, r4, r6⟩ := h
  have hb := k.bs
  have pre := hb.pre
  have sp : s.sp = P.sp := hb.sp.trans pre.sp
  have nb := hb.nB
  have k1 := pre.k1
  refine ⟨⟨pre.workspaceM hb.wr, lay, wd, r0, ⟨⟨State.addr P.sp, 56⟩, by rw [hb.rd, hb.wr, pre.wr]; simp, ?_⟩,
    by rw [sp]; exact pre.r0F_rM, by rw [sp]; exact sv⟩, by omega, by simp only [RP.w6]; omega, pre.fN,
    by rw [hb.rd, hb.wr]; exact pre.rdN, pre.sN.symm.sub_right (rM_sub pre.sizes pre.fS) |> fun d => d,
    r4, r6, by rw [nb]; exact hn.2, by rw [nb]; exact hn.1⟩
  rw [sp]; simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide

theorem countFits (sz : Sizes P) : 128 * P.w6 < 2 ^ 32 := by have := sz.w6b; omega

/-- `n` and `R² mod n`. -/
theorem precompute_vp (hn : P.n % 2 = 1 ∧ 1 < P.n) (hs : Sizes P) {E : State → Prop} (keepHalves : Bool := true) :
    VP (fun σ s => E σ ∧ PreP P σ s keepHalves) VG.Impl.Bignum.Arm.precompute
      (fun σ s => E σ ∧ R01 P σ s keepHalves ∧ MR P s ∧ numAt s.mem (State.addr P.M0) P.w6 0 = P.n ∧
        numAt s.mem (State.addr P.M0) P.w6 4 = R2v P) := by
  refine VP.of_ct (fun σ₁ σ₂ => ((precompute_ct (base := P.M0) (src := P.nP) (len := P.lenM) (w := P.w6) (k := P.K)
    (countFits hs)).mono (fun s t h => ⟨preP_input hn h.1.2, preP_input hn h.2.2, ?_⟩) fun _ _ _ => trivial))
    fun σ s ⟨e, h⟩ => ?_
  · rw [h.1.2.1.bs.sp, h.1.2.1.bs.pre.sp, h.2.2.1.bs.sp, h.2.2.1.bs.pre.sp]
  have i := preP_input hn h
  have nb := h.1.bs.nB
  have sz := h.1.bs.pre.sizes
  have hf := h.1.bs.pre.fS
  refine WP.mono (precompute_ok s i.workspace i.layout i.width i.positive i.fits i.sourceFits i.readable i.separate
    i.ptr i.source i.count i.stackRead i.stackSep i.saved i.large i.odd (countFits hs))
    fun t ⟨d, n0, r2, f, rest⟩ => ⟨e, ?_, ?_, by rw [n0, nb], by rw [r2, nb]⟩
  · exact h.1.keep (keepM sz hf f) (by decide) (by decide) (by cases keepHalves <;> decide) rest.sp rest.rd rest.wr
  · exact ⟨d.workspace, d.layout, d.width, d.inverse, by rw [n0, nb]; exact hn.2, d.stackRead, d.stackSep, d.saved⟩

end

end VG.Proof.Rsa.Arm.Recover
