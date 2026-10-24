module

public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Contract
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.FinTag
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.CTCrypt
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTBase
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Tag
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.StreamFinish
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.InitCT
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTAbsorb
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTFin
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Flush
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamFinish
import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.Framework.PPC64LE.Run
meta import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Contract
meta import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.FinTag
meta import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.CTCrypt
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTBase
meta import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Tag
meta import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.StreamFinish
meta import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.InitCT
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTAbsorb
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Flush
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Env
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamFinish
public import VerifiedGarbage.Impl.Sm4Gcm.PPC64LE
public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Crypt
public import VerifiedGarbage.Spec.TripleDes
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Ghash1
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Ghash1

/-!
# SM4-GCM on PPC64LE: `tag`, `finTag` and `vg_sm4_gcm_stream_finish` are constant time

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/PPC64LE/CTFin.lean`): the invariants fix the context, the
state, `W`, the stack pointer, the lengths of the additional data (`r22`)
and of the text (`r23`), and the tag's address (`r20`), all held in
registers the environment pins, and the permission to write SM4's working
space.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4Gcm.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov lens flush tagOut)
open VG.Proof.AesGcm.PPC64LE (CT ct_of CT.taintEq Env Lay Keeps covers_mem eval_zero and15 lens_ct lens_ok
  flush_ct flush_ok tagOut_ok finQ WP.with_rdwr)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- An environment that may write SM4's working space. -/
def EnvX (c st w x sp : Addr) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ V .r28 = x ∧ Env V sp s ∧ Covers [xR x] s.wr

/-- Before `finTag`: also `aad_len` (`A`) and `text_len` (`T`) in `r22` and `r23`. -/
def FTI (c st w x sp : Addr) (A T : BitVec 64) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ V .r28 = x ∧ V .r22 = A ∧
    V .r23 = T ∧ Env V sp s ∧ Covers [xR x] s.wr

theorem FTI.r {c st w x sp : Addr} {A T : BitVec 64} {s : State} (h : FTI c st w x sp A T s) :
    EnvX c st w x sp s :=
  let ⟨V, a, b, d, e, _, _, he, hx⟩ := h
  ⟨V, a, b, d, e, he, hx⟩

section
variable {c st w x sp : Addr} (L : Lay c st w) (X : XOk c st w x)
include L X

theorem tag_ct {o : Nat} (ho : o = 0 ∨ o = 112) :
    CT (EnvX c st w x sp) (tag o) := by
  refine CT.seq (J := EnvX c st w x sp)
    ((lens_ct L (yo := 16) (.inr rfl)).mono fun s ⟨V, a, b, d, _, he, _⟩ => ⟨V, a, b, d, he⟩)
    (fun s ⟨V, a, b, d, e, he, hx⟩ => WP.mono (WP.with_rdwr (lens_ok (L.v a b d) (.inr rfl) he rfl))
      fun s' ⟨h, _, wr, _⟩ => ⟨V, a, b, d, e, h.1, by rw [wr]; exact hx⟩) ?_
  let J : State → Prop := fun s => ∃ V : Reg → BitVec 64, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧
    V .r28 = x ∧ Env V sp s ∧ Covers [xR x] s.wr ∧ s.gpr .r3 = V .r29 ∧ s.gpr .r4 = V .r30 ∧
    s.gpr .r5 = V .r31 + BitVec.ofNat 64 o ∧ s.gpr .r6 = BitVec.ofNat 64 1 ∧
    s.gpr .r7 = V .r28
  refine CT.seq (J := J) ?_ (fun s ⟨V, a, b, d, e, he, hx⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r28, .r29, .r30, .r31])
        (.block (tagArgs o)) h).isSome = true := by rcases ho with rfl | rfl <;> exact ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, a₁, b₁, d₁, c₁, h₁, _⟩ ⟨_, a₂, b₂, d₂, c₂, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => pinK h₁ h₂ (a₁.trans a₂.symm)
        (b₁.trans b₂.symm) (d₁.trans d₂.symm) (c₁.trans c₂.symm) hr⟩) hc
  · refine WP.mono (tagArgs_ok (o := o) (by omega) (by omega) he)
      fun s' ⟨_, a3, a4, a5, a6, a7, hg, hk⟩ => ⟨V, a, b, d, e, he.keep (fun r hr => hg r (by revert r; decide)
        (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)) hk.sp hk.rd
        hk.wr, by rw [hk.wr]; exact hx, a3, a4, a5, a6, a7⟩
  · exact CT.ctr fun s₁ s₂ ⟨V₁, a₁, b₁, d₁, c₁, e₁, x₁, a3, a4, a5, a6, a7⟩
      ⟨V₂, a₂, b₂, d₂, c₂, e₂, x₂, b3, b4, b5, b6, b7⟩ => by
      have g₁ := ctrTag_mk (L.v a₁ b₁ d₁) (by rw [a₁, b₁, d₁, c₁]; exact X) ho e₁ a3 a4 a5 a6 a7
        (by rw [c₁]; exact x₁)
      have g₂ := ctrTag_mk (L.v a₂ b₂ d₂) (by rw [a₂, b₂, d₂, c₂]; exact X) ho e₂ b3 b4 b5 b6 b7
        (by rw [c₂]; exact x₂)
      rw [a₁, b₁, d₁, c₁] at g₁
      rw [a₂, b₂, d₂, c₂] at g₂
      exact ⟨_, _, _, _, _, g₁, g₂, e₁.sp.trans e₂.sp.symm⟩

theorem finTag_ct {o : Nat} (ho : o = 0 ∨ o = 112) {A T : BitVec 64} :
    CT (FTI c st w x sp A T) (finTag o) := by
  have hq : finQ A T < 16 := by simp only [finQ]; split <;> exact Nat.mod_lt _ (by decide)
  let J : State → Prop := fun s => FTI c st w x sp A T s ∧ s.gpr .r26 = BitVec.ofNat 64 (finQ A T)
  refine CT.seq (J := J) ?_ (fun s ⟨V, a, b, d, e, f, g, he, hx⟩ => ?_) ?_
  · refine CT.ite (decide (T.toNat = 0)) (fun s ⟨_, _, _, _, _, _, g, he, _⟩ =>
      eval_zero (by rw [he.ofNat (r := .r23) (by decide), g]) T.isLt) (fun _ => ?_) (fun _ => ?_)
    · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r22])
          (.block [.li .r0 15, .logic .and .r26 .r22 .r0]) h).isSome = true := ⟨_, by taint_decide⟩
      refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, f₁, _, h₁, _⟩ ⟨_, _, _, _, _, f₂, _, h₂, _⟩ =>
        ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
      simp only [List.mem_singleton] at hr; subst hr
      rw [h₁.fr _ (by decide), h₂.fr _ (by decide), f₁, f₂]
    · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r23])
          (.block [.li .r0 15, .logic .and .r26 .r23 .r0]) h).isSome = true := ⟨_, by taint_decide⟩
      refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, g₁, h₁, _⟩ ⟨_, _, _, _, _, _, g₂, h₂, _⟩ =>
        ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
      simp only [List.mem_singleton] at hr; subst hr
      rw [h₁.fr _ (by decide), h₂.fr _ (by decide), g₁, g₂]
  · have h22 := he.fr .r22 (by decide)
    have h23 := he.fr .r23 (by decide)
    refine WP.ite (decide (T.toNat = 0)) (eval_zero (by rw [he.ofNat (r := .r23) (by decide), g]) T.isLt)
      (fun ht => ?_) (fun hf => ?_)
    · have hand := and15 (V .r22)
      have hQ : finQ A T = (V .r22).toNat % 16 := by simp only [finQ, f]; simp at ht; simp [ht]
      have h₃ : WP isa (.block [.li .r0 15, .logic .and .r26 .r22 .r0]) s fun s₃ =>
          s₃.gpr .r26 = BitVec.ofNat 64 ((V .r22).toNat % 16) ∧
            (∀ r, r ≠ .r0 → r ≠ .r26 → s₃.gpr r = s.gpr r) ∧ Keeps s s₃ := by
        crun [h22, hand]
        exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
      exact WP.mono h₃ fun s₃ ⟨h26, hg, hk⟩ => ⟨⟨V, a, b, d, e, f, g, he.keep (fun r hr => hg r
        (by revert r; decide) (by revert r; decide)) hk.sp hk.rd hk.wr, by rw [hk.wr]; exact hx⟩, by rw [h26, hQ]⟩
    · have hand := and15 (V .r23)
      have hQ : finQ A T = (V .r23).toNat % 16 := by simp only [finQ, g]; simp at hf; simp [hf]
      have h₃ : WP isa (.block [.li .r0 15, .logic .and .r26 .r23 .r0]) s fun s₃ =>
          s₃.gpr .r26 = BitVec.ofNat 64 ((V .r23).toNat % 16) ∧
            (∀ r, r ≠ .r0 → r ≠ .r26 → s₃.gpr r = s.gpr r) ∧ Keeps s s₃ := by
        crun [h23, hand]
        exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
      exact WP.mono h₃ fun s₃ ⟨h26, hg, hk⟩ => ⟨⟨V, a, b, d, e, f, g, he.keep (fun r hr => hg r
        (by revert r; decide) (by revert r; decide)) hk.sp hk.rd hk.wr, by rw [hk.wr]; exact hx⟩, by rw [h26, hQ]⟩
  refine CT.seq (J := FTI c st w x sp A T)
    ((flush_ct L (yo := 16) (.inr rfl) hq).mono fun s ⟨⟨V, a, b, d, _, _, _, he, _⟩, h26⟩ => ⟨⟨V, a, b, d, he⟩, h26⟩)
    (fun s ⟨⟨V, a, b, d, e, f, g, he, hx⟩, h26⟩ => WP.mono (WP.with_rdwr (flush_ok (L.v a b d) (yo := 16) (.inr rfl)
      (x := List.replicate (finQ A T) 0) ⟨he, rfl⟩ (by simp [h26, Nat.mod_eq_of_lt hq]))) fun s' ⟨fl, _, wr, _⟩ =>
        ⟨V, a, b, d, e, f, g, fl.env, by rw [wr]; exact hx⟩) ?_
  refine CT.seq (J := EnvX c st w x sp) ?_ (fun s ⟨V, a, b, d, e, f, g, he, hx⟩ => ?_)
    ((tag_ct L X ho).mono fun _ h => h)
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r22, .r23])
        (.block [mov .r24 .r22, mov .r26 .r23]) h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, f₁, g₁, h₁, _⟩ ⟨_, _, _, _, _, f₂, g₂, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), f₁, f₂]
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), g₁, g₂]
  · have h₅ : WP isa (.block [mov .r24 .r22, mov .r26 .r23]) s fun s₅ =>
        (∀ r, r ≠ .r24 → r ≠ .r26 → s₅.gpr r = s.gpr r) ∧ Keeps s s₅ := by
      crun [mov, BitVec.or_self]
      exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
    exact WP.mono h₅ fun s₅ ⟨hg, hk⟩ => ⟨V, a, b, d, e, he.keep (fun r hr => hg r (by revert r; decide)
      (by revert r; decide)) hk.sp hk.rd hk.wr, by rw [hk.wr]; exact hx⟩

end

/-- In `finish`, after the entry: also the tag's address `Tp` in `r20`, which
the state may write. -/
def FinI (c st w x sp : Addr) (A T Tp : BitVec 64) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ V .r28 = x ∧ V .r22 = A ∧
    V .r23 = T ∧ V .r20 = Tp ∧ Env V sp s ∧ Covers [⟨Tp, 16⟩] s.wr ∧ Covers [xR x] s.wr

theorem finEntry_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint
    (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8, .r9]) (.block finEntry) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem tagOut_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r20, .r31]) (.block tagOut)
    h).isSome = true := ⟨_, by taint_decide⟩

theorem streamFinish_ct : ConstantTime isa streamFinishPPC64LE.pre streamFinishPPC64LE.pub streamFinish := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q3, q4, q5, q6, q7, q8, q9, qsp⟩ := hq
  have h₁' : finPre σ₁ := h₁
  have L := finLay h₁'
  have X := finX h₁'
  have dtw : (⟨σ₁.gpr .r7, 16⟩ : Region).Disjoint ⟨σ₁.gpr .r8, 16⟩ :=
    h₁'.2.2.2.2.2.2.2.1.sub_right (Region.sub_prefix (by decide))
  let I₀ : State → Prop := fun s => finPre s ∧ s.gpr .r3 = σ₁.gpr .r3 ∧ s.gpr .r4 = σ₁.gpr .r4 ∧
    s.gpr .r5 = σ₁.gpr .r5 ∧ s.gpr .r6 = σ₁.gpr .r6 ∧ s.gpr .r7 = σ₁.gpr .r7 ∧ s.gpr .r8 = σ₁.gpr .r8 ∧
    s.gpr .r9 = σ₁.gpr .r9 ∧ s.sp = σ₁.sp
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm, q4.symm, q5.symm, q6.symm, q7.symm,
    q8.symm, q9.symm, qsp.symm⟩, ?_⟩
  let FI := FinI (σ₁.gpr .r3) (σ₁.gpr .r4) (σ₁.gpr .r8) (σ₁.gpr .r9) σ₁.sp (σ₁.gpr .r5) (σ₁.gpr .r6)
    (σ₁.gpr .r7)
  refine CT.seq (J := FI) ?_ (fun s ⟨hs, e3, e4, e5, e6, e7, e8, e9, esp⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := finEntry_taint
    exact CT.taintEq (I := I₀) _ σ₁.gpr σ₁.sp (fun s ⟨_, e3, e4, e5, e6, e7, e8, e9, esp⟩ =>
      ⟨esp, by simp [e3, e4, e5, e6, e7, e8, e9]⟩) hc
  · refine WP.mono (fin1_wp (fin_W hs)) fun s₁ h1 => ?_
    have hT : Covers [⟨s.gpr .r7, 16⟩] s₁.wr := by
      rw [h1.en.keeps.wr, hs.2.1]; exact covers_mem (by simp)
    refine ⟨s₁.gpr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h1.r29, e3]
    · rw [h1.r30, e4]
    · rw [h1.r31, e8]
    · rw [h1.r28, e9]
    · rw [h1.r22, e5]
    · rw [h1.r23, e6]
    · rw [h1.r20, e7]
    · rw [← esp]; exact fin_env hs h1
    · rw [← e7]; exact hT
    · rw [← e9, h1.en.keeps.wr]; exact fin_X hs
  refine CT.seq (J := FI)
    ((finTag_ct L X (o := 0) (.inl rfl)).mono fun s ⟨V, a, b, d, e, f, g, _, he, _, hx⟩ =>
      ⟨V, a, b, d, e, f, g, he, hx⟩)
    (fun s ⟨V, a, b, d, e, f, g, i, he, hT, hx⟩ => WP.mono (WP.with_rdwr (finTag_ok (L.v a b d)
      (by rw [a, b, d, e]; exact X) (o := 0) (.inl rfl)
      (a := List.replicate ((σ₁.gpr .r5).toNat % 16) 0) (ct := List.replicate (σ₁.gpr .r6).toNat 0) he
      (by rw [e]; exact hx) rfl (by simp [f]) (by simp [g]))) fun s' ⟨fo, _, wr, _⟩ =>
        ⟨V, a, b, d, e, f, g, i, fo.env, by rw [wr]; exact hT, by rw [wr]; exact hx⟩) ?_
  refine CT.seq (J := fun s => s.gpr .r31 = σ₁.gpr .r8 ∧ s.sp = σ₁.sp) ?_
    (fun s ⟨V, a, b, d, _, f, g, i, he, hT, _⟩ => WP.mono (tagOut_ok he (by rw [i]; exact hT)
      (by rw [i, d]; exact dtw)) fun s' ⟨_, _, hg, hk⟩ =>
        ⟨by rw [hg _ (by decide), he.r31, d], by rw [hk.sp, he.sp]⟩) ?_
  · obtain ⟨_, hc⟩ := tagOut_taint
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, d₁, _, _, _, i₁, h₁, _⟩ ⟨_, _, _, d₂, _, _, _, i₂, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), i₁, i₂]
    · rw [h₁.r31, h₂.r31, d₁, d₂]
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => σ₁.gpr .r8) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

end VG.Proof.Sm4Gcm.PPC64LE
