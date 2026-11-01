module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contract
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTFin
import VerifiedGarbage.Proof.AesGcm.RISCV64.Absorb
import VerifiedGarbage.Proof.AesGcm.RISCV64.Compare
import VerifiedGarbage.Proof.AesGcm.RISCV64.FinTag
import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamVerify
import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Contract
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTFin
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Absorb
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Compare
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.FinTag
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamVerify
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Env
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Spec.TripleDes
public import VerifiedGarbage.Impl.AesGcm.RISCV64

/-!
# AES-GCM on RISCV64: `vg_aes_gcm_stream_verify` is constant time

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcm/Arm/CTVerify.lean`): the invariant fixes what `finish`'s
does (`FinI`), and the received tag's address and length (`r20`, `r19`);
the branch on the tag length is on that public length, and the comparison
does not branch.
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- In `verify`, after the entry: the received tag's `tl` bytes at `Tp`,
apart from `W`, which the state may read. -/
def VerI (c st w sp : Addr) (R : Nat) (A T Tp : BitVec 64) (tl : Nat) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ V .s3 = BitVec.ofNat 64 R ∧ V .s10 = A ∧
    V .s11 = T ∧ V .s9 = Tp ∧ V .s8 = BitVec.ofNat 64 tl ∧ Env V sp s ∧ Covers [⟨Tp, tl⟩] (s.rd ++ s.wr) ∧
    (⟨Tp, tl⟩ : Region).Disjoint ⟨w, 2560⟩

theorem verEntry_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7]) (.block verEntry) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem tagLenOk_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s8]) tagLenOk h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem recv_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s8, .s9, .s0]) recv h).isSome =
    true := ⟨_, by taint_decide⟩

theorem cmp_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s8, .s0]) (cmp 0) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem li3_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs []) (.block [.li .a0 0]) h).isSome =
    true := ⟨_, by taint_decide⟩

section
variable {c st w sp : Addr} (L : Lay c st w) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) {A T Tp : BitVec 64}
  {tl : Nat}
include L hR

/-- `verify` after the tag length is known to be allowed. -/
theorem verOk_ct (t1 : 1 ≤ tl) (t16 : tl ≤ 16) :
    CT (VerI c st w sp R A T Tp tl) (.seq recv (.seq (finTag 0) (cmp 0))) := by
  refine CT.seq (J := VerI c st w sp R A T Tp tl) ?_ (fun s ⟨V, a, b, d, e, f, g, i, j, he, hT, hTd⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := recv_taint
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, d₁, _, _, _, i₁, j₁, h₁, _⟩ ⟨_, _, _, d₂, _, _, _, i₂, j₂, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), j₁, j₂]
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), i₁, i₂]
    · rw [h₁.s0, h₂.s0, d₁, d₂]
  · refine WP.mono (recv_ok he j t1 t16 (by rw [i]; exact hT) (by rw [i, d]; exact hTd.sub_right (Lay.wSub
      (by decide)))) fun s' ⟨_, _, hg, hk⟩ => ⟨V, a, b, d, e, f, g, i, j, he.keep (fun r hr => hg r
        (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
        (by revert r; decide)) hk.sp hk.rd hk.wr, by rw [hk.rd, hk.wr]; exact hT, hTd⟩
  refine CT.seq (J := VerI c st w sp R A T Tp tl)
    ((finTag_ct L (o := 0) (.inl rfl) hR).mono fun s ⟨V, a, b, d, e, f, g, _, _, he, _⟩ =>
      ⟨V, a, b, d, e, f, g, he⟩)
    (fun s ⟨V, a, b, d, e, f, g, i, j, he, hT, hTd⟩ => WP.mono (WP.with_rdwr (finTag_ok (L.v a b d) (o := 0)
      (.inl rfl) (a := List.replicate (A.toNat % 16) 0) (ct := List.replicate T.toNat 0) he e hR rfl
      (by simp [f]) (by simp [g]))) fun s' ⟨fo, rd, wr, _⟩ =>
        ⟨V, a, b, d, e, f, g, i, j, fo.env, by rw [rd, wr]; exact hT, hTd⟩) ?_
  obtain ⟨_, hc⟩ := cmp_taint
  refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, d₁, _, _, _, _, j₁, h₁, _⟩ ⟨_, _, _, d₂, _, _, _, _, j₂, h₂, _⟩ =>
    ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), j₁, j₂]
  · rw [h₁.s0, h₂.s0, d₁, d₂]

/-- The same, for correctness: `W` is kept in `r31`. -/
theorem verOk_wp (t1 : 1 ≤ tl) (t16 : tl ≤ 16) {s : State} (h : VerI c st w sp R A T Tp tl s) :
    WP isa (.seq recv (.seq (finTag 0) (cmp 0))) s fun s' => s'.gpr .s0 = w ∧ s'.sp = sp := by
  obtain ⟨V, a, b, d, e, f, g, i, j, he, hT, hTd⟩ := h
  refine WP.seq (WP.mono (recv_ok he j t1 t16 (by rw [i]; exact hT) (by rw [i, d]; exact hTd.sub_right (Lay.wSub
    (by decide)))) fun s₁ ⟨_, _, hg, hk⟩ => ?_)
  have he₁ := he.keep (fun r hr => hg r (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide)) hk.sp hk.rd hk.wr
  refine WP.seq (WP.mono (finTag_ok (L.v a b d) (o := 0) (.inl rfl) (a := List.replicate (A.toNat % 16) 0)
    (ct := List.replicate T.toNat 0) he₁ e hR rfl (by simp [f]) (by simp [g])) fun s₂ fo => ?_)
  refine WP.mono (cmp_ok fo.env (o := 0) (.inl rfl) j t1 t16) fun s' ⟨_, _, hg', hk'⟩ =>
    ⟨by rw [hg' _ (by decide) (by decide) (by decide) (by decide) (by decide), fo.env.s0, d],
      by rw [hk'.sp, fo.env.sp]⟩

end

theorem streamVerify_ct : ConstantTime isa streamVerifyRISCV64.pre streamVerifyRISCV64.pub streamVerify := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp⟩ := hq
  have h₁' : verPre σ₁ := h₁
  have L := verLay h₁'
  have hR : (σ₁.gpr .a1).toNat = 10 ∨ (σ₁.gpr .a1).toNat = 12 ∨ (σ₁.gpr .a1).toNat = 14 :=
    h₁'.2.2.2.2.2.2.2.2.2.2.2
  let I₀ : State → Prop := fun s => verPre s ∧ s.gpr .a0 = σ₁.gpr .a0 ∧ s.gpr .a1 = σ₁.gpr .a1 ∧
    s.gpr .a2 = σ₁.gpr .a2 ∧ s.gpr .a3 = σ₁.gpr .a3 ∧ s.gpr .a4 = σ₁.gpr .a4 ∧ s.gpr .a5 = σ₁.gpr .a5 ∧
    s.gpr .a6 = σ₁.gpr .a6 ∧ s.gpr .a7 = σ₁.gpr .a7 ∧ s.sp = σ₁.sp
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm, q4.symm, q5.symm, q6.symm, q7.symm,
    q8.symm, q9.symm, q10.symm, qsp.symm⟩, ?_⟩
  let tl := (σ₁.gpr .a6).toNat
  let VI := VerI (σ₁.gpr .a0) (σ₁.gpr .a2) (σ₁.gpr .a7) σ₁.sp (σ₁.gpr .a1).toNat (σ₁.gpr .a3) (σ₁.gpr .a4)
    (σ₁.gpr .a5) tl
  refine CT.seq (J := VI) ?_ (fun s ⟨hs, e3, e4, e5, e6, e7, e8, e9, e10, esp⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := verEntry_taint
    exact CT.taintEq (I := I₀) _ σ₁.gpr σ₁.sp (fun s ⟨_, e3, e4, e5, e6, e7, e8, e9, e10, esp⟩ =>
      ⟨esp, by simp [e3, e4, e5, e6, e7, e8, e9, e10]⟩) hc
  · refine WP.mono (ver1_wp (ver_W hs)) fun s₁ h1 => ?_
    have hT : Covers [⟨s.gpr .a5, (s.gpr .a6).toNat⟩] (s₁.rd ++ s₁.wr) := by
      rw [h1.en.keeps.rd, h1.en.keeps.wr, hs.1]; exact covers_mem (List.mem_append_left _ (by simp))
    have hTd : (⟨s.gpr .a5, (s.gpr .a6).toNat⟩ : Region).Disjoint ⟨s.gpr .a7, 2560⟩ := hs.2.2.2.2.2.2.1
    refine ⟨s₁.gpr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h1.s2, e3]
    · rw [h1.s1, e5]
    · rw [h1.s0, e10]
    · rw [h1.s3, e4, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [h1.s10, e6]
    · rw [h1.s11, e7]
    · rw [h1.s9, e8]
    · rw [h1.s8, e9, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [← esp]; exact ver_env hs h1
    · simp only [tl]; rw [← e8, ← e9]; exact hT
    · simp only [tl]; rw [← e8, ← e9, ← e10]; exact hTd
  -- the tag length
  let ok := Spec.Gcm.tagLenOk tl
  let J : State → Prop := fun s => VI s ∧ s.gpr .s5 = BitVec.ofNat 64 (if ok then 1 else 0)
  refine CT.seq (J := J) ?_ (fun s ⟨V, a, b, d, e, f, g, i, j, he, hT, hTd⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := tagLenOk_taint
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, _, _, j₁, h₁, _⟩ ⟨_, _, _, _, _, _, _, _, j₂, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_singleton] at hr; subst hr
    rw [h₁.fr _ (by decide), h₂.fr _ (by decide), j₁, j₂]
  · refine WP.mono (tagLenOk_ok (by rw [he.fr _ (by decide), j]) (σ₁.gpr .a6).isLt) fun s' ⟨h25, hg, hk⟩ =>
      ⟨⟨V, a, b, d, e, f, g, i, j, he.keep (fun r hr => hg r (by revert r; decide) (by revert r; decide))
        hk.sp hk.rd hk.wr, by rw [hk.rd, hk.wr]; exact hT, hTd⟩, h25⟩
  have ev : ∀ s, J s → isa.eval (.zero .s5) s = some (decide ((if ok then 1 else 0) = 0)) :=
    fun s h => eval_zero h.2 (by split <;> decide)
  refine CT.seq (J := fun s => s.gpr .s0 = σ₁.gpr .a7 ∧ s.sp = σ₁.sp) ?_ (fun s hs => ?_) ?_
  · refine CT.ite _ ev (fun hb => ?_) (fun hb => ?_)
    · obtain ⟨_, hc⟩ := li3_taint
      exact CT.taint _ (fun s₁ s₂ ⟨⟨_, _, _, _, _, _, _, _, _, h₁, _⟩, _⟩ ⟨⟨_, _, _, _, _, _, _, _, _, h₂, _⟩, _⟩ =>
        ⟨h₁.sp.trans h₂.sp.symm, fun r hr => by simp at hr⟩) hc
    · have hok : ok = true := by cases e : ok <;> simp_all
      obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
      exact (verOk_ct L hR t1 t16).mono fun s h => h.1
  · refine WP.ite _ (ev s hs) (fun hb => ?_) (fun hb => ?_)
    · obtain ⟨⟨V, _, _, d, _, _, _, _, _, he, _⟩, _⟩ := hs
      have h₀ : WP isa (.block [.li .a0 0]) s fun s' => (∀ r, r ≠ .a0 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
        crun [Int.reduceNatCast', ]
        exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl⟩⟩
      exact WP.mono h₀ fun s' ⟨hg, hk⟩ => ⟨by rw [hg _ (by decide), he.s0, d], by rw [hk.sp, he.sp]⟩
    · have hok : ok = true := by cases e : ok <;> simp_all
      obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
      exact verOk_wp L hR t1 t16 hs.1
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => σ₁.gpr .a7) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

end VG.Proof.AesGcm.RISCV64
