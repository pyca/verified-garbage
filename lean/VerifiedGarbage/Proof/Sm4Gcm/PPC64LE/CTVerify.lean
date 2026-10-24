module

public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Contract
public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.CTFin
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTBase
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.FinTag
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.StreamVerify
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.InitCT
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTVerify
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Compare
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamVerify
import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.Framework.PPC64LE.Run
meta import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Contract
meta import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.CTFin
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTBase
meta import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.FinTag
meta import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.StreamVerify
meta import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.InitCT
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTVerify
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Compare
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Env
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-!
# SM4-GCM on PPC64LE: `vg_sm4_gcm_stream_verify` is constant time

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/PPC64LE/CTVerify.lean`): the invariant fixes what `finish`'s
does (`FinI`), and the received tag's address and length (`r20`, `r19`);
the branch on the tag length is on that public length, and the comparison
does not branch.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4Gcm.PPC64LE
open VG.Impl.AesGcm.PPC64LE (recv cmp tagLenOk)
open VG.Proof.AesGcm.PPC64LE (CT ct_of CT.taintEq Env Lay Keeps covers_mem eval_zero recv_ok cmp_ok
  tagLenOk_ok tagLenOk_bounds tagLenOk_taint recv_taint cmp_taint li3_taint WP.with_rdwr)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- In `verify`, after the entry: the received tag's `tl` bytes at `Tp`,
apart from `W`, which the state may read. -/
def VerI (c st w sp : Addr) (A T Tp : BitVec 64) (tl : Nat) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ V .r22 = A ∧
    V .r23 = T ∧ V .r20 = Tp ∧ V .r19 = BitVec.ofNat 64 tl ∧ Env V sp s ∧ Covers [⟨Tp, tl⟩] (s.rd ++ s.wr) ∧
    (⟨Tp, tl⟩ : Region).Disjoint ⟨w, 2560⟩ ∧ Covers [xR x] s.wr

theorem verEntry_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint
    (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8, .r9]) (.block verEntry) h).isSome = true :=
  ⟨_, by taint_decide⟩

section
variable {c st w x sp : Addr} (L : Lay c st w) (X : XOk c st w x) {A T Tp : BitVec 64}
  {tl : Nat}
include L X

/-- `verify` after the tag length is known to be allowed. -/
theorem verOk_ct (t1 : 1 ≤ tl) (t16 : tl ≤ 16) :
    CT (VerI c st w sp A T Tp tl) (.seq recv (.seq (finTag 0) (cmp 0))) := by
  refine CT.seq (J := VerI c st w sp A T Tp tl) ?_ (fun s ⟨V, a, b, d, f, g, i, j, he, hT, hTd, hx⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := recv_taint
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, d₁, _, _, i₁, j₁, h₁, _⟩ ⟨_, _, _, d₂, _, _, i₂, j₂, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), j₁, j₂]
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), i₁, i₂]
    · rw [h₁.r31, h₂.r31, d₁, d₂]
  · refine WP.mono (recv_ok he j t1 t16 (by rw [i]; exact hT) (by rw [i, d]; exact hTd.sub_right (Lay.wSub
      (by decide)))) fun s' ⟨_, _, hg, hk⟩ => ⟨V, a, b, d, f, g, i, j, he.keep (fun r hr => hg r
        (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
        (by revert r; decide)) hk.sp hk.rd hk.wr, by rw [hk.rd, hk.wr]; exact hT, hTd, by rw [hk.wr]; exact hx⟩
  refine CT.seq (J := VerI c st w sp A T Tp tl)
    ((finTag_ct L X (o := 0) (.inl rfl)).mono fun s ⟨V, a, b, d, f, g, _, _, he, _, _, hx⟩ =>
      ⟨V, a, b, d, f, g, he, hx⟩)
    (fun s ⟨V, a, b, d, f, g, i, j, he, hT, hTd, hx⟩ => WP.mono (WP.with_rdwr (finTag_ok (L.v a b d)
      (by rw [a, b, d]; exact X) (o := 0)
      (.inl rfl) (a := List.replicate (A.toNat % 16) 0) (ct := List.replicate T.toNat 0) he (by rw [d]; exact hx) rfl
      (by simp [f]) (by simp [g]))) fun s' ⟨fo, rd, wr, _⟩ =>
        ⟨V, a, b, d, f, g, i, j, fo.env, by rw [rd, wr]; exact hT, hTd, by rw [wr]; exact hx⟩) ?_
  obtain ⟨_, hc⟩ := cmp_taint
  refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, d₁, _, _, _, j₁, h₁, _⟩ ⟨_, _, _, d₂, _, _, _, j₂, h₂, _⟩ =>
    ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), j₁, j₂]
  · rw [h₁.r31, h₂.r31, d₁, d₂]

/-- The same, for correctness: `W` is kept in `r31`. -/
theorem verOk_wp (t1 : 1 ≤ tl) (t16 : tl ≤ 16) {s : State} (h : VerI c st w sp A T Tp tl s) :
    WP isa (.seq recv (.seq (finTag 0) (cmp 0))) s fun s' => s'.gpr .r31 = w ∧ s'.sp = sp := by
  obtain ⟨V, a, b, d, f, g, i, j, he, hT, hTd, hx⟩ := h
  refine WP.seq (WP.mono (recv_ok he j t1 t16 (by rw [i]; exact hT) (by rw [i, d]; exact hTd.sub_right (Lay.wSub
    (by decide)))) fun s₁ ⟨_, _, hg, hk⟩ => ?_)
  have he₁ := he.keep (fun r hr => hg r (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide)) hk.sp hk.rd hk.wr
  refine WP.seq (WP.mono (finTag_ok (L.v a b d) (by rw [a, b, d]; exact X) (o := 0) (.inl rfl)
    (a := List.replicate (A.toNat % 16) 0)
    (ct := List.replicate T.toNat 0) he₁ (by rw [d, hk.wr]; exact hx) rfl (by simp [f]) (by simp [g])) fun s₂ fo => ?_)
  refine WP.mono (cmp_ok fo.env (o := 0) (.inl rfl) j t1 t16) fun s' ⟨_, _, hg', hk'⟩ =>
    ⟨by rw [hg' _ (by decide) (by decide) (by decide) (by decide) (by decide), fo.env.r31, d],
      by rw [hk'.sp, fo.env.sp]⟩

end

theorem streamVerify_ct : ConstantTime isa streamVerifyPPC64LE.pre streamVerifyPPC64LE.pub streamVerify := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q3, q4, q5, q6, q7, q8, q9, qsp⟩ := hq
  have h₁' : verPre σ₁ := h₁
  have L := verLay h₁'
  have X := verX h₁'
  let I₀ : State → Prop := fun s => verPre s ∧ s.gpr .r3 = σ₁.gpr .r3 ∧ s.gpr .r4 = σ₁.gpr .r4 ∧
    s.gpr .r5 = σ₁.gpr .r5 ∧ s.gpr .r6 = σ₁.gpr .r6 ∧ s.gpr .r7 = σ₁.gpr .r7 ∧ s.gpr .r8 = σ₁.gpr .r8 ∧
    s.gpr .r9 = σ₁.gpr .r9 ∧ s.sp = σ₁.sp
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm, q4.symm, q5.symm, q6.symm, q7.symm,
    q8.symm, q9.symm, qsp.symm⟩, ?_⟩
  let tl := (σ₁.gpr .r8).toNat
  let VI := VerI (σ₁.gpr .r3) (σ₁.gpr .r4) (σ₁.gpr .r9) σ₁.sp (σ₁.gpr .r5) (σ₁.gpr .r6)
    (σ₁.gpr .r7) tl
  refine CT.seq (J := VI) ?_ (fun s ⟨hs, e3, e4, e5, e6, e7, e8, e9, esp⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := verEntry_taint
    exact CT.taintEq (I := I₀) _ σ₁.gpr σ₁.sp (fun s ⟨_, e3, e4, e5, e6, e7, e8, e9, esp⟩ =>
      ⟨esp, by simp [e3, e4, e5, e6, e7, e8, e9]⟩) hc
  · refine WP.mono (ver1_wp (ver_W hs)) fun s₁ h1 => ?_
    have hT : Covers [⟨s.gpr .r7, (s.gpr .r8).toNat⟩] (s₁.rd ++ s₁.wr) := by
      rw [h1.en.keeps.rd, h1.en.keeps.wr, hs.1]; exact covers_mem (List.mem_append_left _ (by simp))
    have hTd : (⟨s.gpr .r7, (s.gpr .r8).toNat⟩ : Region).Disjoint ⟨s.gpr .r9, 2560⟩ :=
      hs.2.2.2.2.2.2.1.sub_right (Region.sub_prefix (by decide))
    refine ⟨s₁.gpr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h1.r29, e3]
    · rw [h1.r30, e4]
    · rw [h1.r31, e9]
    · rw [h1.r22, e5]
    · rw [h1.r23, e6]
    · rw [h1.r20, e7]
    · rw [h1.r19, e8, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [← esp]; exact ver_env hs h1
    · simp only [tl]; rw [← e7, ← e8]; exact hT
    · simp only [tl]; rw [← e7, ← e8, ← e9]; exact hTd
    · rw [← e9, h1.en.keeps.wr]; exact ver_X hs
  -- the tag length
  let ok := Spec.Gcm.tagLenOk tl
  let J : State → Prop := fun s => VI s ∧ s.gpr .r25 = BitVec.ofNat 64 (if ok then 1 else 0)
  refine CT.seq (J := J) ?_ (fun s ⟨V, a, b, d, f, g, i, j, he, hT, hTd, hx⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := tagLenOk_taint
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, _, j₁, h₁, _⟩ ⟨_, _, _, _, _, _, _, j₂, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_singleton] at hr; subst hr
    rw [h₁.fr _ (by decide), h₂.fr _ (by decide), j₁, j₂]
  · refine WP.mono (tagLenOk_ok (by rw [he.fr _ (by decide), j]) (σ₁.gpr .r8).isLt) fun s' ⟨h25, hg, hk⟩ =>
      ⟨⟨V, a, b, d, f, g, i, j, he.keep (fun r hr => hg r (by revert r; decide) (by revert r; decide))
        hk.sp hk.rd hk.wr, by rw [hk.rd, hk.wr]; exact hT, hTd, by rw [hk.wr]; exact hx⟩, h25⟩
  have ev : ∀ s, J s → isa.eval (.zero .d .r25) s = some (decide ((if ok then 1 else 0) = 0)) :=
    fun s h => eval_zero h.2 (by split <;> decide)
  refine CT.seq (J := fun s => s.gpr .r31 = σ₁.gpr .r9 ∧ s.sp = σ₁.sp) ?_ (fun s hs => ?_) ?_
  · refine CT.ite _ ev (fun hb => ?_) (fun hb => ?_)
    · obtain ⟨_, hc⟩ := li3_taint
      exact CT.taint _ (fun s₁ s₂ ⟨⟨_, _, _, _, _, _, _, _, h₁, _⟩, _⟩ ⟨⟨_, _, _, _, _, _, _, _, h₂, _⟩, _⟩ =>
        ⟨h₁.sp.trans h₂.sp.symm, fun r hr => by simp at hr⟩) hc
    · have hok : ok = true := by cases e : ok <;> simp_all
      obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
      exact (verOk_ct L X t1 t16).mono fun s h => h.1
  · refine WP.ite _ (ev s hs) (fun hb => ?_) (fun hb => ?_)
    · obtain ⟨⟨V, _, _, d, _, _, _, _, he, _⟩, _⟩ := hs
      have h₀ : WP isa (.block [.li .r3 0]) s fun s' => (∀ r, r ≠ .r3 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
        crun []
        exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
      exact WP.mono h₀ fun s' ⟨hg, hk⟩ => ⟨by rw [hg _ (by decide), he.r31, d], by rw [hk.sp, he.sp]⟩
    · have hok : ok = true := by cases e : ok <;> simp_all
      obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
      exact verOk_wp L X t1 t16 hs.1
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => σ₁.gpr .r9) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

end VG.Proof.Sm4Gcm.PPC64LE
