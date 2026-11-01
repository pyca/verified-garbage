module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contract
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTAbsorb
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTCrypt
import VerifiedGarbage.Proof.AesGcm.RISCV64.Absorb
import VerifiedGarbage.Proof.AesGcm.RISCV64.FinTag
import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamFinish
import VerifiedGarbage.Proof.AesGcm.RISCV64.Tag
import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Contract
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTAbsorb
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTCrypt
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Absorb
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.FinTag
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamFinish
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Tag
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Env
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Impl.AesGcm.RISCV64

/-!
# AES-GCM on RISC-V: `tag`, `finTag` and `vg_aes_gcm_stream_finish` are constant time

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcm/Arm/CTFin.lean`): the invariants fix the context, the state,
`W`, the stack pointer, the number of rounds (`s3`), the lengths of the
additional data (`s10`) and of the text (`s11`), and the tag's address
(`s9`), all held in registers the environment pins.
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- An environment with `R` rounds in `s3`. -/
def EnvR (c st w sp : Addr) (R : Nat) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ V .s3 = BitVec.ofNat 64 R ∧ Env V sp s

/-- Before `finTag`: also `aad_len` (`A`) and `text_len` (`T`) in `s10` and `s11`. -/
def FTI (c st w sp : Addr) (R : Nat) (A T : BitVec 64) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ V .s3 = BitVec.ofNat 64 R ∧ V .s10 = A ∧
    V .s11 = T ∧ Env V sp s

theorem FTI.r {c st w sp : Addr} {R : Nat} {A T : BitVec 64} {s : State} (h : FTI c st w sp R A T s) :
    EnvR c st w sp R s :=
  let ⟨V, a, b, d, e, _, _, he⟩ := h
  ⟨V, a, b, d, e, he⟩

section
variable {c st w sp : Addr} (L : Lay c st w)
include L

theorem tag_ct {o R : Nat} (ho : o = 0 ∨ o = 112) (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    CT (EnvR c st w sp R) (tag o) := by
  refine CT.seq (J := EnvR c st w sp R)
    ((lens_ct L (yo := 16) (.inr rfl)).mono fun s ⟨V, a, b, d, _, he⟩ => ⟨V, a, b, d, he⟩)
    (fun s ⟨V, a, b, d, e, he⟩ => WP.mono (lens_ok (L.v a b d) (.inr rfl) he rfl) fun s' h =>
      ⟨V, a, b, d, e, h.1⟩) ?_
  let J : State → Prop := fun s => ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧
    Env V sp s ∧ s.gpr .a0 = V .s2 ∧ s.gpr .a1 = BitVec.ofNat 64 R ∧ s.gpr .a2 = V .s1 ∧
    s.gpr .a3 = V .s0 + BitVec.ofNat 64 o ∧ s.gpr .a4 = BitVec.ofNat 64 1 ∧
    s.gpr .a5 = V .s0 + BitVec.ofNat 64 512
  refine CT.seq (J := J) ?_ (fun s ⟨V, a, b, d, e, he⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s3, .s2, .s1, .s0])
        (.block (tagArgs o)) h).isSome = true := by rcases ho with rfl | rfl <;> exact ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, a₁, b₁, d₁, e₁, h₁⟩ ⟨_, a₂, b₂, d₂, e₂, h₂⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => pinK h₁ h₂ (e₁.trans e₂.symm) (a₁.trans a₂.symm)
        (b₁.trans b₂.symm) (d₁.trans d₂.symm) hr⟩) hc
  · refine WP.mono (tagArgs_ok (L.v a b d) (o := o) ho he)
      fun s' ⟨_, a3, a4, a5, a6, a7, a8, hg, hk⟩ => ⟨V, a, b, d, he.keep (fun r hr => hg r (by revert r; decide)
        (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
        (by revert r; decide) (by revert r; decide)) hk.sp hk.rd hk.wr, a3, by rw [a4, e], a5, a6, a7, a8⟩
  · exact CT.ctr fun s₁ s₂ ⟨V₁, a₁, b₁, d₁, e₁, a3, a4, a5, a6, a7, a8⟩
      ⟨V₂, a₂, b₂, d₂, e₂, b3, b4, b5, b6, b7, b8⟩ => by
      have g₁ := ctrTag_mk (L.v a₁ b₁ d₁) ho e₁ a3 a4 a5 a6 a7 a8 hR
      have g₂ := ctrTag_mk (L.v a₂ b₂ d₂) ho e₂ b3 b4 b5 b6 b7 b8 hR
      rw [a₁, b₁, d₁] at g₁
      rw [a₂, b₂, d₂] at g₂
      exact ⟨_, _, _, _, _, _, g₁, g₂, e₁.sp.trans e₂.sp.symm⟩

/-- The number of buffered bytes `finTag` pads: of the text if there is any,
else of the additional data. -/
abbrev finQ (A T : BitVec 64) : Nat := if T.toNat = 0 then A.toNat % 16 else T.toNat % 16

theorem finTag_ct {o R : Nat} (ho : o = 0 ∨ o = 112) (hR : R = 10 ∨ R = 12 ∨ R = 14) {A T : BitVec 64} :
    CT (FTI c st w sp R A T) (finTag o) := by
  have hq : finQ A T < 16 := by simp only [finQ]; split <;> exact Nat.mod_lt _ (by decide)
  let J : State → Prop := fun s => FTI c st w sp R A T s ∧ s.gpr .s6 = BitVec.ofNat 64 (finQ A T)
  refine CT.seq (J := J) ?_ (fun s ⟨V, a, b, d, e, f, g, he⟩ => ?_) ?_
  · refine CT.ite (decide (T.toNat = 0)) (fun s ⟨_, _, _, _, _, _, g, he⟩ =>
      eval_zero (by rw [he.ofNat (r := .s11) (by decide), g]) T.isLt) (fun _ => ?_) (fun _ => ?_)
    · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s10])
          (.block [.logicImm .and .s6 .s10 15]) h).isSome = true := ⟨_, by taint_decide⟩
      refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, f₁, _, h₁⟩ ⟨_, _, _, _, _, f₂, _, h₂⟩ =>
        ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
      simp only [List.mem_singleton] at hr; subst hr
      rw [h₁.fr _ (by decide), h₂.fr _ (by decide), f₁, f₂]
    · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s11])
          (.block [.logicImm .and .s6 .s11 15]) h).isSome = true := ⟨_, by taint_decide⟩
      refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, g₁, h₁⟩ ⟨_, _, _, _, _, _, g₂, h₂⟩ =>
        ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
      simp only [List.mem_singleton] at hr; subst hr
      rw [h₁.fr _ (by decide), h₂.fr _ (by decide), g₁, g₂]
  · have h22 := he.fr .s10 (by decide)
    have h23 := he.fr .s11 (by decide)
    refine WP.ite (decide (T.toNat = 0)) (eval_zero (by rw [he.ofNat (r := .s11) (by decide), g]) T.isLt)
      (fun ht => ?_) (fun hf => ?_)
    · have hand := and15 (V .s10)
      have hQ : finQ A T = (V .s10).toNat % 16 := by simp only [finQ, f]; simp at ht; simp [ht]
      have h₃ : WP isa (.block [.logicImm .and .s6 .s10 15]) s fun s₃ =>
          s₃.gpr .s6 = BitVec.ofNat 64 ((V .s10).toNat % 16) ∧
            (∀ r, r ≠ .s6 → s₃.gpr r = s.gpr r) ∧ Keeps s s₃ := by
        crun [Int.reduceNatCast', h22, hand]
        exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl⟩⟩
      exact WP.mono h₃ fun s₃ ⟨h26, hg, hk⟩ => ⟨⟨V, a, b, d, e, f, g, he.keep (fun r hr => hg r
        (by revert r; decide)) hk.sp hk.rd hk.wr⟩, by rw [h26, hQ]⟩
    · have hand := and15 (V .s11)
      have hQ : finQ A T = (V .s11).toNat % 16 := by simp only [finQ, g]; simp at hf; simp [hf]
      have h₃ : WP isa (.block [.logicImm .and .s6 .s11 15]) s fun s₃ =>
          s₃.gpr .s6 = BitVec.ofNat 64 ((V .s11).toNat % 16) ∧
            (∀ r, r ≠ .s6 → s₃.gpr r = s.gpr r) ∧ Keeps s s₃ := by
        crun [Int.reduceNatCast', h23, hand]
        exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl⟩⟩
      exact WP.mono h₃ fun s₃ ⟨h26, hg, hk⟩ => ⟨⟨V, a, b, d, e, f, g, he.keep (fun r hr => hg r
        (by revert r; decide)) hk.sp hk.rd hk.wr⟩, by rw [h26, hQ]⟩
  refine CT.seq (J := FTI c st w sp R A T)
    ((flush_ct L (yo := 16) (.inr rfl) hq).mono fun s ⟨⟨V, a, b, d, _, _, _, he⟩, h26⟩ => ⟨⟨V, a, b, d, he⟩, h26⟩)
    (fun s ⟨⟨V, a, b, d, e, f, g, he⟩, h26⟩ => WP.mono (flush_ok (L.v a b d) (yo := 16) (.inr rfl)
      (x := List.replicate (finQ A T) 0) ⟨he, rfl⟩ (by simp [h26, Nat.mod_eq_of_lt hq])) fun s' fl =>
        ⟨V, a, b, d, e, f, g, fl.env⟩) ?_
  refine CT.seq (J := EnvR c st w sp R) ?_ (fun s ⟨V, a, b, d, e, f, g, he⟩ => ?_)
    ((tag_ct L ho hR).mono fun _ h => h)
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s10, .s11])
        (.block [mov .s4 .s10, mov .s6 .s11]) h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, f₁, g₁, h₁⟩ ⟨_, _, _, _, _, f₂, g₂, h₂⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), f₁, f₂]
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), g₁, g₂]
  · have h₅ : WP isa (.block [mov .s4 .s10, mov .s6 .s11]) s fun s₅ =>
        (∀ r, r ≠ .s4 → r ≠ .s6 → s₅.gpr r = s.gpr r) ∧ Keeps s s₅ := by
      crun [Int.reduceNatCast', mov]
      exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl⟩⟩
    exact WP.mono h₅ fun s₅ ⟨hg, hk⟩ => ⟨V, a, b, d, e, he.keep (fun r hr => hg r (by revert r; decide)
      (by revert r; decide)) hk.sp hk.rd hk.wr⟩

end

/-- In `finish`, after the entry: also the tag's address `Tp` in `s9`, which
the state may write. -/
def FinI (c st w sp : Addr) (R : Nat) (A T Tp : BitVec 64) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ V .s3 = BitVec.ofNat 64 R ∧ V .s10 = A ∧
    V .s11 = T ∧ V .s9 = Tp ∧ Env V sp s ∧ Covers [⟨Tp, 16⟩] s.wr

theorem finEntry_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6]) (.block finEntry) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem tagOut_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s9, .s0]) (.block tagOut)
    h).isSome = true := ⟨_, by taint_decide⟩

theorem streamFinish_ct : ConstantTime isa streamFinishRISCV64.pre streamFinishRISCV64.pub streamFinish := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q3, q4, q5, q6, q7, q8, q9, qsp⟩ := hq
  have h₁' : finPre σ₁ := h₁
  have L := finLay h₁'
  have hR := fin_R h₁'
  have dtw : (⟨σ₁.gpr .a5, 16⟩ : Region).Disjoint ⟨σ₁.gpr .a6, 16⟩ := by
    obtain ⟨-, -, -, -, -, -, -, dtw, -⟩ := h₁'
    exact dtw.sub_right (Region.sub_prefix (by decide))
  let I₀ : State → Prop := fun s => finPre s ∧ s.gpr .a0 = σ₁.gpr .a0 ∧ s.gpr .a1 = σ₁.gpr .a1 ∧
    s.gpr .a2 = σ₁.gpr .a2 ∧ s.gpr .a3 = σ₁.gpr .a3 ∧ s.gpr .a4 = σ₁.gpr .a4 ∧ s.gpr .a5 = σ₁.gpr .a5 ∧
    s.gpr .a6 = σ₁.gpr .a6 ∧ s.sp = σ₁.sp
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm, q4.symm, q5.symm, q6.symm, q7.symm,
    q8.symm, q9.symm, qsp.symm⟩, ?_⟩
  let FI := FinI (σ₁.gpr .a0) (σ₁.gpr .a2) (σ₁.gpr .a6) σ₁.sp (σ₁.gpr .a1).toNat (σ₁.gpr .a3) (σ₁.gpr .a4)
    (σ₁.gpr .a5)
  refine CT.seq (J := FI) ?_ (fun s ⟨hs, e3, e4, e5, e6, e7, e8, e9, esp⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := finEntry_taint
    exact CT.taintEq (I := I₀) _ σ₁.gpr σ₁.sp (fun s ⟨_, e3, e4, e5, e6, e7, e8, e9, esp⟩ =>
      ⟨esp, by simp [e3, e4, e5, e6, e7, e8, e9]⟩) hc
  · refine WP.mono (fin1_wp (fin_W hs) (fin_al hs)) fun s₁ h1 => ?_
    have hT : Covers [⟨s.gpr .a5, 16⟩] s₁.wr := by
      rw [h1.en.keeps.wr, hs.2.1]; exact covers_mem (by simp)
    refine ⟨s₁.gpr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h1.s2, e3]
    · rw [h1.s1, e5]
    · rw [h1.s0, e9]
    · rw [h1.s3, e4, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [h1.s10, e6]
    · rw [h1.s11, e7]
    · rw [h1.s9, e8]
    · rw [← esp]; exact fin_env hs h1
    · rw [← e8]; exact hT
  refine CT.seq (J := FI)
    ((finTag_ct L (o := 0) (.inl rfl) hR).mono fun s ⟨V, a, b, d, e, f, g, _, he, _⟩ => ⟨V, a, b, d, e, f, g, he⟩)
    (fun s ⟨V, a, b, d, e, f, g, i, he, hT⟩ => WP.mono (WP.with_rdwr (finTag_ok (L.v a b d) (o := 0) (.inl rfl)
      (a := List.replicate ((σ₁.gpr .a3).toNat % 16) 0) (ct := List.replicate (σ₁.gpr .a4).toNat 0) he e hR rfl
      (by simp [f]) (by simp [g]))) fun s' ⟨fo, _, wr, _⟩ =>
        ⟨V, a, b, d, e, f, g, i, fo.env, by rw [wr]; exact hT⟩) ?_
  refine CT.seq (J := fun s => s.gpr .s0 = σ₁.gpr .a6 ∧ s.sp = σ₁.sp) ?_
    (fun s ⟨V, a, b, d, e, f, g, i, he, hT⟩ => WP.mono (tagOut_ok he (by rw [i]; exact hT)
      (by rw [i, d]; exact dtw)) fun s' ⟨_, _, hg, hk⟩ =>
        ⟨by rw [hg _ (by decide), he.s0, d], by rw [hk.sp, he.sp]⟩) ?_
  · obtain ⟨_, hc⟩ := tagOut_taint
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, d₁, _, _, _, i₁, h₁, _⟩ ⟨_, _, _, d₂, _, _, _, i₂, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), i₁, i₂]
    · rw [h₁.s0, h₂.s0, d₁, d₂]
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => σ₁.gpr .a6) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

end VG.Proof.AesGcm.RISCV64
