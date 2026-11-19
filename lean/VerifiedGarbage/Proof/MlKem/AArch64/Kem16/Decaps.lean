module

public import VerifiedGarbage.Impl.MlKem.AArch64.Kem16
public import VerifiedGarbage.Proof.MlKem.AArch64.Decaps
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Table
public import VerifiedGarbage.Proof.MlKem.AArch64.KemB
public import VerifiedGarbage.Proof.MlKem.AArch64.KemEnc
public import VerifiedGarbage.Proof.MlKem.AArch64.KemOps
public import VerifiedGarbage.Proof.MlKem.AArch64.Lay
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.PrfUsing
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Interface
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Tables
import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.VRest
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TableApart
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.EncapsTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Correct
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemMatrixCall
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Matrix
public import VerifiedGarbage.Proof.MlKem.AArch64.DecapsA
import VerifiedGarbage.Proof.MlKem.AArch64.Shared
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Framework.Range
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import VerifiedGarbage.Proof.Framework.GetElem
meta import VerifiedGarbage.Proof.MlKem.AArch64.DecapsA
public import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.MlKem.AArch64.KemCommon
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
public import VerifiedGarbage.Impl.MlKem.AArch64.FixedHashDecaps
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TransformTables
public import VerifiedGarbage.Impl.MlKem.AArch64.Optimized

/-! ### `MlKem.AArch64.Optimized.DecryptStart`, which this module and modules that import it used -/

section

/-! ### `MlKem.AArch64.Optimized.DecryptSeed`, which only this module used -/

section

/-! # Decapsulation seed derivation after the fused decryption path -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Decaps
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
variable {P : KemLay}
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

theorem a_tail_using (hash : FixedHash.HashFn)
    (hash_ok : FixedHash.HashCorrect hash .x28 ST WK 72 6
      [⟨.x28,MB,32⟩,⟨.x25,768*P.k+32,32⟩] [⟨.x28,KP,32⟩,⟨.x28,RB,32⟩])
    {s₀ s₂ : State} (hp : Pre P (deL P) s₀)
    (kb₂ : KB P (deL P) s₀ s₂) (x₂ : s₂.gpr .x24=1) (m₂ : bytesAt s₂.mem (sA (deL P) s₀ MB) 32=mD P s₀) :
    WP isa (seqs [hash .x28 ST WK 72 6
      [⟨.x28,MB,32⟩,⟨.x25,768*P.k+32,32⟩] [⟨.x28,KP,32⟩,⟨.x28,RB,32⟩],
      .block (copy32 .x25 (768*P.k) .x28 SB)]) s₂ (AfterA P s₀) := by
  have hw := hp.wf
  -- `G(m' ‖ h)`
  refine WP.seq (WP.mono (hash_ok (hsetup hp kb₂ (by decide : 72 ∈ Spec.Sha3.rates)) (by decide) (by simp)
    (fun p hp' => by
      rcases mem2' hp' with rfl | rfl
      · exact pieceOk (k := 3) hp kb₂ (by decide) (by dek) (.inr (by decide)) (by decide) (by dek)
      · exact pieceOk (k := 0) hp kb₂ (by decide) (by dek) (.inl (by dek)) (by decide) (by dek))
    (fun p hp' => by
      rcases mem2' hp' with rfl | rfl
      · exact pieceOk (k := 3) hp kb₂ (by decide) (by dek) (.inr (by decide)) (by decide) (by dek)
      · exact pieceOk (k := 3) hp kb₂ (by decide) (by dek) (.inr (by decide)) (by decide) (by dek))
    (by
      refine List.pairwise_pair.mpr ?_
      simp only [preg, e28 kb₂]
      exact sdisj hp (by kom) (by kom) (by decide)))
    fun s₃ ⟨k₃, o₃⟩ => ?_)
  obtain kb₃ := kb₂.hash hp k₃ fun p hp' => by
    rcases mem2' hp' with rfl | rfl
    · exact ⟨3, KP, 32, rfl, by decide, by dek, by dek, .inr (.inr (by kom))⟩
    · exact ⟨3, RB, 32, rfl, by decide, by dek, by dek, .inr (.inr (by kom))⟩
  obtain msg : (List.map (pbytes s₂) [⟨.x28, MB, 32⟩, ⟨.x25, 768 * P.k + 32, 32⟩]).flatten =
      mD P s₀ ++ KPke.dkH P.params (dkD P s₀) := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, pbytes,
      e28 kb₂, kb₂.x25]
    rw [m₂, slice_eq kb₂ (b := 0) (by decide) (by dek)]
    rfl
  obtain ⟨o₁, o₂, -⟩ := o₃
  rw [msg] at o₁ o₂
  obtain hG := G_eq (mD P s₀ ++ KPke.dkH P.params (dkD P s₀))
  obtain kp₃ : bytesAt s₃.mem (sA (deL P) s₀ KP) 32 = (gD P s₀).1 := by
    rw [← e28 kb₂, o₁]; show _ = (G (mD P s₀ ++ KPke.dkH P.params (dkD P s₀))).1; rw [hG]; rfl
  obtain r₃ : bytesAt s₃.mem (sA (deL P) s₀ RB) 32 = (gD P s₀).2 := by
    rw [← e28 kb₂, o₂]; show _ = (G (mD P s₀ ++ KPke.dkH P.params (dkD P s₀))).2; rw [hG]; rfl
  have k₃' := k₃
  simp only [VG.Proof.MlKem.AArch64.STr, VG.Proof.MlKem.AArch64.WKr, preg, List.map_cons, List.map_nil,
    kb₂.x28, kb₂.sp] at k₃'
  obtain m₃ : bytesAt s₃.mem (sA (deL P) s₀ MB) 32 = mD P s₀ := by
    rw [bytesAt_frame k₃'.frame (fun r hr => by
      rcases mem5 hr with rfl | rfl | rfl | rfl | rfl
      · exact sdisj hp (by kom) (by kom) (by decide)
      · exact sdisj hp (by kom) (by kom) (by decide)
      · exact below_R hp hp.scb (hp.fs (by kom))
      · exact sdisj hp (by kom) (by kom) (by decide)
      · exact sdisj hp (by kom) (by kom) (by decide)) (by decide)]
    exact m₂
  -- `ρ`
  refine WP.mono (KeyGen.copy_ok (S := kA s₀ 0) (D := kA s₀ 3) (so := 768 * P.k) (dO := SB) (by decide)
    (by decide) (by kom) (by decide) (hp.args.rdisj (by dek) (by dek) (by dek) (hp.fs (by kom)) (by dek)
      (by dek)) kb₃.x25 kb₃.x28 (cov_r hp kb₃ (b := 0) (by dek) (by dek)) (cov_s hp kb₃ (by kom)))
    fun s₄ ⟨k₄, f₄, b₄⟩ => ?_
  obtain kb₄ := kb₃.frame k₄ f₄ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact safe_scr hp (by kom)
  obtain far₄ : ∀ {o l : Nat}, o + l ≤ SV P + 48 → (o + l ≤ SB ∨ SB + 32 ≤ o) →
      bytesAt s₄.mem (sA (deL P) s₀ o) l = bytesAt s₃.mem (sA (deL P) s₀ o) l := fun f h => by
    refine bytesAt_frame f₄ (fun r hr => ?_) (by kom)
    rw [List.mem_singleton.mp hr]
    exact sdisj hp f (by kom) h
  refine ⟨kb₄, by rw [k₄.get .x24, k₃.cs _ (by decide) (by decide), x₂],
    by rw [far₄ (o := MB) (l := 32) (by kom) (by decide)]; exact m₃,
    by rw [far₄ (o := KP) (l := 32) (by kom) (by decide)]; exact kp₃,
    by rw [far₄ (o := RB) (l := 32) (by kom) (by decide)]; exact r₃, ?_⟩
  rw [show sA (deL P) s₀ SB = kA s₀ 3 + BitVec.ofNat 64 SB from rfl, b₄,
    show kA s₀ 0 = kA s₀ ((deL P).slot 0) from rfl, slice_eq kb₃ (b := 0) (by decide) (by dek)]
  rfl

end VG.Proof.MlKem.AArch64.Decaps

end

end

/-! ### `MlKem.AArch64.Optimized.DecryptM`, which only this module used -/

section

/-! ### `MlKem.AArch64.Optimized.DecryptW`, which only this module used -/

section

/-! # Decryption with 16-bit coefficients: `û'` and the tail

`uW_all`: each row of `u` decoded and decompressed into `PP`, narrowed to 16 bits at `yOff i`
and transformed by `vg_mlkem16_ntt`. `m_tailW`: after the 16-bit dot product `ŝᵀ ∘ û'`, its
inverse transform, widened into `PP`, subtracted from the decompressed `v` and compressed into
`m'`. -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Decaps
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
variable {P : KemLay}

/-- After `û'[i]` for `i < n`, stored with 16 bits. -/
structure DInvW (P : KemLay) (s₀ : State) (n : Nat) (s : State) : Prop where
  kb : KB P (deL P) s₀ s
  x24 : s.gpr .x24 = 1
  u : ∀ i < n, PolyIsW 16 s.mem (sA (deL P) s₀ (yOff P i)) (ntt (KPke.dcU P.params (cD P s₀) i))

theorem DInvW.frame {s₀ : State} {n : Nat} {s s' : State} (h : DInvW P s₀ n s) (hk : KB P (deL P) s₀ s')
    (hx : s'.gpr .x24 = s.gpr .x24) {W : List Region} (hf : Frame W s.mem s'.mem)
    (hW : ∀ r ∈ W, (R (kA s₀) (deL P).sc (YH P) (1024 * n)).Disjoint r) : DInvW P s₀ n s' :=
  ⟨hk, by rw [hx, h.x24], fun i hi => polyIsW_frame_poly (w16 := true) hf (fun r hr => (hW r hr).sub_left
    (R.sub2 (by simp only [yOff]; omega_using []) (by simp only [yOff]; omega_using [hi]))) (h.u i hi)⟩

theorem uW_step {s₀ : State} (hp : Pre P (deL P) s₀) (hc : Calls P) {i : Nat} (hi : i < P.k) {s : State}
    (ht : Optimized.TransformTables s) (h : DInvW P s₀ i s) :
    WP isa (Impl.MlKem.AArch64.Optimized.deU P i) s fun t => DInvW P s₀ (i + 1) t ∧
      Frame [R (kA s₀) (deL P).sc (PP P) 1024,R (kA s₀) (deL P).sc (yOff P i) 1024,
        R (kA s₀) (deL P).sc NS 1024] s.mem t.mem ∧ Optimized.TransformTables t := by
  have hw := hp.wf
  obtain hpo := po_y hw hi
  obtain hu := du_le hi
  obtain fu : 32 * P.du * i + 32 * P.du ≤ (deL P).len 1 := by dek
  apply WPs.seqs (by simp)
  refine WPs.cons (WP.mono_syms (ddL_ok hp hc (k := 1) (o := 32 * P.du * i) (d := P.du) (off := PP P)
    (by decide) fu (.inl rfl) (po_PP hw) (.inl (by dek)) h.kb) fun s₁ ⟨kb₁, f₁, p₁, x₁⟩ sy₁ => ?_)
  obtain e₁ := h.frame kb₁ x₁ f₁ fun r hr => by
    rw [List.mem_singleton.mp hr]; exact dfar hp (by omega_using [hi]) (po_PP hw).le (by lom)
  rw [slice_eq h.kb (b := 1) (by decide) fu] at p₁
  obtain ht₁ := ht.frame sy₁ (kb₁.rd.trans h.kb.rd.symm) (kb₁.wr.trans h.kb.wr.symm) (kb₁.sp.trans h.kb.sp.symm)
    f₁ (cov_w hp h.kb ⟨hp.scw,hp.scb⟩ (o:=PP P) (l:=1024) (hp.fs (po_PP hw).le))
  refine WPs.cons (WP.mono_syms (narrowW_ok hp (po_PP hw) hpo (by lom) kb₁ p₁)
    fun s₂ ⟨kb₂, f₂, p₂, x₂⟩ sy₂ => ?_)
  obtain e₂ := e₁.frame kb₂ x₂ f₂ fun r hr => by
    rw [List.mem_singleton.mp hr]; exact dfar hp (by omega_using [hi]) hpo.le (.inr (by simp only [yOff]; omega_using []))
  obtain ht₂ := ht₁.frame sy₂ (kb₂.rd.trans kb₁.rd.symm) (kb₂.wr.trans kb₁.wr.symm) (kb₂.sp.trans kb₁.sp.symm)
    f₂ (cov_w hp kb₁ ⟨hp.scw,hp.scb⟩ (o:=yOff P i) (l:=1024) (hp.fs hpo.le))
  refine WPs.single (WP.mono_syms (nttW_ok hp hpo kb₂ p₂ ht₂) fun s₃ ⟨kb₃, f₃, p₃, x₃⟩ sy₃ => ?_)
  obtain e₃ := e₂.frame kb₃ x₃ f₃ fun r hr => by
    rcases mem2' hr with rfl | rfl
    · exact dfar hp (by omega_using [hi]) hpo.le (.inr (by simp only [yOff]; omega_using []))
    · exact dfar hp (by omega_using [hi]) (by kom) (.inl (by kom))
  obtain ht₃ := ht₂.frame sy₃ (kb₃.rd.trans kb₂.rd.symm) (kb₃.wr.trans kb₂.wr.symm) (kb₃.sp.trans kb₂.sp.symm)
    f₃ (covers_cons (cov_s hp kb₂ hpo.le) (cov_s hp kb₂ (o:=NS) (l:=1024) (by kom)))
  refine ⟨⟨e₃.kb,e₃.x24,fun i' hi' => ?_⟩,
    ((f₁.mono (by simp)).trans (f₂.mono (by simp))).trans (f₃.mono (by simp)),ht₃⟩
  rcases (by omega_using [hi'] : i' < i ∨ i' = i) with hi' | rfl
  · exact e₃.u i' hi'
  · refine (congrArg (fun x => PolyIsW 16 s₃.mem (sA (deL P) s₀ (yOff P i')) (ntt x)) ?_).mp p₃
    simp only [KPke.dcU, cD, deL, List.getD_cons_zero, List.getD_cons_succ, KemLay.params]

/-- What decoding `û'` writes. -/
def uWritesW (P : KemLay) (s₀ : State) : List Region :=
  [R (kA s₀) (deL P).sc (YH P) (1024*P.k),R (kA s₀) (deL P).sc NS 1024,R (kA s₀) (deL P).sc (PP P) 1024]

theorem uW_all {s₀ s : State} (hp : Pre P (deL P) s₀) (hc : Calls P)
    (ht : Optimized.TransformTables s) (h : DInvW P s₀ 0 s) :
    WPs ((List.range P.k).map (Impl.MlKem.AArch64.Optimized.deU P)) s fun t =>
      DInvW P s₀ P.k t ∧ Frame (uWritesW P s₀) s.mem t.mem ∧ Optimized.TransformTables t := by
  apply WPs.range (I := fun i t => DInvW P s₀ i t ∧ Frame (uWritesW P s₀) s.mem t.mem ∧
    Optimized.TransformTables t)
  · intro i hi t ⟨di,fi,ti⟩
    refine WP.mono (uW_step hp hc hi ti di) fun u ⟨du,fu,tu⟩ => ⟨du,fi.trans (fu.sub (fun r hh => ?_)),tu⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl | rfl
    · exact ⟨_,by simp [uWritesW],fun _ hh => hh⟩
    · exact ⟨R (kA s₀) (deL P).sc (YH P) (1024*P.k),by simp [uWritesW],
        R.sub2 (by simp [yOff]) (by simp only [yOff]; omega_using [hi])⟩
    · exact ⟨_,by simp [uWritesW],fun _ hh => hh⟩
  · exact ⟨h,Frame.refl _ _,ht⟩

theorem m_tailW {s₀ s : State} (hp : Pre P (deL P) s₀) (hc : Calls P)
    (ht : Optimized.TransformTables s)
    (hk : KB P (deL P) s₀ s) (hx : s.gpr .x24=1)
    (t₄ : PolyIsW 16 s.mem (sA (deL P) s₀ (TP P))
      (KPke.dotK (dcS (KPke.dkPke P.params (dkD P s₀)))
        (fun j => ntt (KPke.dcU P.params (cD P s₀) j)) P.k)) :
    WPs [Ntt16.Readonly.nttInvAtWithW (TP P) NS,Kem16.widenAt (TP P) (PP P),
      P.ddLAt .x26 (32*P.du*P.k) P.dv (EP P),subAt (EP P) (PP P),ceAt (EP P) 1 .x28 MB] s
      fun t => KB P (deL P) s₀ t ∧ t.gpr .x24=1 ∧ bytesAt t.mem (sA (deL P) s₀ MB) 32=mD P s₀ := by
  have hw := hp.wf
  refine WPs.cons (WP.mono (invW_ok hp (po_TP hw) hk t₄.1 ht) fun s₅ ⟨kb₅, f₅, t₅, x₅⟩ => ?_)
  rw [t₄.2] at t₅
  refine WPs.cons (WP.mono (widenW_ok hp (po_TP hw) (po_PP hw) (by lom) kb₅ t₅)
    fun s₆ ⟨kb₆, f₆, t₆, x₆⟩ => ?_)
  obtain fv : 32 * P.du * P.k + 32 * P.dv ≤ (deL P).len 1 := by
    simp only [deL, List.getD_cons_zero, List.getD_cons_succ, KemLay.ctLen]
    rw [Nat.mul_add, Nat.mul_assoc]
  refine WPs.cons (WP.mono (ddL_ok hp hc (k := 1) (o := 32 * P.du * P.k) (d := P.dv) (off := EP P) (by decide)
    fv (.inr rfl) (po_EP hw) (.inl (by dek)) kb₆) fun s₇ ⟨kb₇, f₇, p₇, x₇⟩ => ?_)
  rw [slice_eq kb₆ (b := 1) (by decide) fv] at p₇
  obtain t₇ := polyIs_frame f₇ (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact papart hp (po_PP hw) (po_EP hw) (by lom)) t₆
  refine WPs.cons (WP.mono (sub_ok hp (po_EP hw) (po_PP hw) (by lom) kb₇ p₇.1 t₇.1)
    fun s₈ ⟨kb₈, f₈, p₈, x₈⟩ => ?_)
  rw [p₇.2, t₇.2] at p₈
  refine WPs.single (WP.mono (ce_ok hp (off := EP P) (d := 1) (k := 3) (o := MB) (po_EP hw) (by decide)
    (by decide) (by dek) (by dek) (.inr ⟨by kom, .inl (by kom)⟩) kb₈ p₈.1) fun s₉ ⟨kb₉, f₉, b₉, x₉⟩ => ?_)
  refine ⟨kb₉, by rw [x₉, x₈, x₇, x₆, x₅, hx], ?_⟩
  rw [show sA (deL P) s₀ MB = kA s₀ ((deL P).slot 3) + BitVec.ofNat 64 MB from rfl, b₉, p₈.2, mD, KPke.decM,
    KPke.kpkeDecrypt_eq]
  rfl

end VG.Proof.MlKem.AArch64.Decaps

end

end


/-! # Complete decryption with 16-bit coefficients and a single fused secret-vector dot product -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Decaps
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
variable {P : KemLay}

theorem fused_m_ok {s₀ s : State} (hp : Pre P (deL P) s₀) (hc : Calls P) (htr : Optimized.TransformTables s) (h : DInv P s₀ 0 s)
    (ht : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA"))
    (hcT : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr))
    (ha : (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint ⟨kA s₀ (deL P).sc,P.scl⟩) :
    WP isa (Impl.MlKem.AArch64.Optimized.decryptM P) s fun t => KB P (deL P) s₀ t ∧ t.gpr .x24=1 ∧
      bytesAt t.mem (sA (deL P) s₀ MB) 32=mD P s₀ := by
  have hw := hp.wf
  obtain far : ∀o l, o+l≤P.scl → (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint
      (R (kA s₀) (deL P).sc o l) := by
    intro o l hf
    obtain hd : (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint (R (kA s₀) (deL P).sc 0 P.scl) := by
      simpa only [R,ptr_zero] using ha
    exact hd.sub_right (R.sub2 (by omega_using []) (by omega_using [hf]))
  apply WPs.seqs (by simp)
  rw [List.append_assoc]
  apply WPs.append
  refine WPs.mono_syms (uW_all hp hc htr ⟨h.kb,h.x24,fun _ hj => by omega⟩) fun t ⟨dt,ft,trt⟩ hs => ?_
  obtain gt : Dot.GammaArtifact t.mem (t.syms "VG_MLKEM_GAMMA") := by
    rw [hs]; apply gamma_frame ht ft
    intro r hh
    simp only [uWritesW, List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl | rfl <;> exact far _ _ (by lom)
  obtain hT : ∀j<P.k, decode12 (bytesAt s₀.mem (kA s₀ ((deL P).slot 0)+BitVec.ofNat 64 (0+384*j)) 384)=
      dcS (KPke.dkPke P.params (dkD P s₀)) j := by
    intro j hj
    simp only [deL,Nat.zero_add]
    rw [←bytesAt_slice s₀.mem (kA s₀ 0) (show 384*j+384≤(deL P).len 0 by dek),dcS_eq s₀ hj]
    rfl
  obtain d0 : DecodeInvW P (deL P) s₀ t.mem (dcS (KPke.dkPke P.params (dkD P s₀)))
      (fun j => ntt (KPke.dcU P.params (cD P s₀) j)) 1 0 t :=
    ⟨dt.kb,dt.x24,fun _ hj => by omega,dt.u,Frame.refl _ _⟩
  apply WPs.append
  obtain dec := WPs.range (fun _ hj _ h => decode_stepW hp (kE := 0) (eo := 0) (by decide) (by change 0<2; decide)
    (by dek) hj hT h) d0
  simp only [Nat.zero_add] at dec
  refine WPs.mono_syms dec fun u du hsu => ?_
  obtain gu : Dot.GammaArtifact u.mem (u.syms "VG_MLKEM_GAMMA") := by
    rw [hsu]
    apply gamma_frame gt du.frame
    intro r hh
    rw [List.mem_singleton.mp hh,hs]
    obtain hkk := Nat.mul_le_mul_right P.k hw.facts.1
    simp only [Nat.one_mul] at hkk
    exact far _ _ (by lom)
  obtain cu : Covers [⟨u.syms "VG_MLKEM_GAMMA",512⟩] (u.rd++u.wr) := by
    simpa only [hsu,hs,du.kb.rd,du.kb.wr,←h.kb.rd,←h.kb.wr] using hcT
  obtain au : (polyRegion (sA (deL P) s₀ (TP P))).Disjoint ⟨u.syms "VG_MLKEM_GAMMA",512⟩ := by
    rw [hsu,hs]; exact (far _ _ (by lom)).symm
  obtain tru := trt.frame hsu (du.kb.rd.trans dt.kb.rd.symm) (du.kb.wr.trans dt.kb.wr.symm)
    (du.kb.sp.trans dt.kb.sp.symm) du.frame (cov_w hp dt.kb ⟨hp.scw,hp.scb⟩ (hp.fs (by lom)))
  refine WPs.cons (WP.mono_syms (fusedW_ok hp (po_TP hw) du.kb (decodedTerms P)
    (decoded_readyW hp du gu cu au).data) fun w ⟨kw,fw,pw,xw⟩ hus => ?_)
  rw [decoded_sum] at pw
  obtain trw := tru.frame hus (kw.rd.trans du.kb.rd.symm) (kw.wr.trans du.kb.wr.symm)
    (kw.sp.trans du.kb.sp.symm) fw (cov_w hp du.kb ⟨hp.scw,hp.scb⟩ (hp.fs (by lom)))
  exact m_tailW hp hc trw kw (xw.trans du.x24) pw

end VG.Proof.MlKem.AArch64.Decaps

end

end


/-! # Decapsulation prologue and seed derivation with fused decryption -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Decaps
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
variable {P : KemLay}
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

theorem start_using_ok (hash : FixedHash.HashFn)
    (hash_ok : FixedHash.HashCorrect hash .x28 ST WK 72 6
      [⟨.x28,MB,32⟩,⟨.x25,768*P.k+32,32⟩] [⟨.x28,KP,32⟩,⟨.x28,RB,32⟩])
    {s₀ : State} (hp : Pre P (deL P) s₀) (hc : Calls P) (htr : Optimized.TransformTables s₀)
    (ht : Dot.GammaArtifact s₀.mem (s₀.syms "VG_MLKEM_GAMMA"))
    (hcT : Covers [⟨s₀.syms "VG_MLKEM_GAMMA",512⟩] (s₀.rd++s₀.wr))
    (ha : (⟨s₀.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint ⟨kA s₀ (deL P).sc,P.scl⟩) :
    WP isa (Impl.MlKem.AArch64.FixedHashDecaps.deStartUsing hash P) s₀ (AfterA P s₀) := by
  have hw := hp.wf
  refine WP.seq (WP.mono_syms (prologue_ok hp) fun s₁ h₁ hs => ?_)
  obtain gt : Dot.GammaArtifact s₁.mem (s₁.syms "VG_MLKEM_GAMMA") := by
    rw [hs]
    rcases h₁.mem with hm | hf
    · rwa [hm]
    · apply gamma_frame ht hf
      intro r hh
      rw [List.mem_singleton.mp hh]
      exact ha.sub_right (R.sub (by lom))
  obtain ct : Covers [⟨s₁.syms "VG_MLKEM_GAMMA",512⟩] (s₁.rd++s₁.wr) := by
    simpa only [hs,h₁.keep.rd,h₁.keep.wr] using hcT
  obtain tr₁ : Optimized.TransformTables s₁ := by
    apply htr.frame hs h₁.keep.rd h₁.keep.wr h₁.keep.sp
    · rcases h₁.mem with hm | hf
      · simpa only [hm] using Frame.refl [R (kA s₀) (deL P).sc (SV P) 48] s₀.mem
      · exact hf
    · exact cov_w₀ hp ⟨hp.scw,hp.scb⟩ (hp.fs (by omega_using []))
  refine WP.seq (WP.mono (fused_m_ok hp hc tr₁ ⟨h₁.kb,h₁.x24,fun _ hj => by omega⟩ gt ct
    (by simpa only [hs] using ha)) fun s₂ ⟨kb₂,x₂,m₂⟩ => ?_)
  exact a_tail_using hash hash_ok hp kb₂ x₂ m₂

end VG.Proof.MlKem.AArch64.Decaps

end

end

/-! ### `MlKem.AArch64.Hybrid.DecapsStart`, which this module and modules that import it used -/

section

/-! ### `MlKem.AArch64.Hybrid.CopyN`, which only this module used -/

section

/-! # Copying `n` words through `x9` (`Kem16.copyN`), as `KeyGen.copy_ok` copies 32 bytes -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.Sha3 (bytesAt)

/-- The `n` words at `S + so` copied to `D + dO`, through `x9`. -/
theorem copyN_ok {n : Nat} {S D : Addr} {sb db : Reg} {so dO : Nat} (hn : 8 * n < 2 ^ 64) (hs9 : sb ≠ .x9) (hd9 : db ≠ .x9)
    (hso : so % 8 = 0 ∧ so + 8 * n ≤ 32768) (hdo : dO % 8 = 0 ∧ dO + 8 * n ≤ 32768)
    (hsep : Region.Disjoint ⟨S + BitVec.ofNat 64 so, 8 * n⟩ ⟨D + BitVec.ofNat 64 dO, 8 * n⟩)
    {s : State} (hS : s.gpr sb = S) (hD : s.gpr db = D)
    (hin : Covers [⟨S + BitVec.ofNat 64 so, 8 * n⟩] (s.rd ++ s.wr))
    (hout : Covers [⟨D + BitVec.ofNat 64 dO, 8 * n⟩] s.wr) :
    WP isa (.block (Impl.MlKem.AArch64.Kem16.copyN n sb so db dO)) s fun s' => Keep [.x9] s s' ∧
      Frame [⟨D + BitVec.ofNat 64 dO, 8 * n⟩] s.mem s'.mem ∧
      bytesAt s'.mem (D + BitVec.ofNat 64 dO) (8 * n) = bytesAt s.mem (S + BitVec.ofNat 64 so) (8 * n) := by
  obtain n9s : sb ∉ [Reg.x9] := by simpa using hs9
  obtain n9d : db ∉ [Reg.x9] := by simpa using hd9
  refine WP.mono (wp_range_flatMap (M := isa) (N := n) (fun k (s' : State) => Keep [.x9] s s' ∧
      Frame [⟨D + BitVec.ofNat 64 dO, 8 * n⟩] s.mem s'.mem ∧
      ∀ i < 8 * k, s'.mem (D + BitVec.ofNat 64 (dO + i)) = s.mem (S + BitVec.ofNat 64 (so + i)))
    (fun k s₁ hk ⟨k₁, f₁, b₁⟩ => ?_) n (Nat.le_refl _) s
    ⟨Keep.refl _ _, Frame.refl _ _, fun i hi => absurd hi (by omega_using [])⟩) fun s' ⟨k', f', b'⟩ =>
      ⟨k', f', ?_⟩
  · refine wp_ldrx (a := S + BitVec.ofNat 64 (so + 8 * k)) ⟨by omega_using [hso], by omega_using [hso, hk]⟩ (by rw [k₁.get sb n9s, hS])
      (by rw [k₁.rd, k₁.wr]; exact in_R (A := fun _ => S) (b := 0) hin (k := 8 * k) (by omega_using [hk]) hn)
      fun s₂ h₂ e₂ => wp_strx (a := D + BitVec.ofNat 64 (dO + 8 * k)) ⟨by omega_using [hdo], by omega_using [hdo, hk]⟩
      (by rw [h₂.get db n9d, k₁.get db n9d, hD])
      (by rw [h₂.wr, k₁.wr]; exact in_R (A := fun _ => D) (b := 0) hout (k := 8 * k) (by omega_using [hk]) hn)
      fun s₃ h₃ => wp_nil ?_
    obtain m₃ : s₃.mem = s₁.mem.writeW (D + BitVec.ofNat 64 (dO + 8 * k))
        (s₁.mem.readW (S + BitVec.ofNat 64 (so + 8 * k)) 64) := by
      rw [h₃.mem, e₂, h₂.mem]
    refine ⟨((k₁.trans h₂.keep).trans h₃.keep).mono, ?_, fun i hi => ?_⟩
    · rw [m₃]
      exact f₁.writeW (List.mem_singleton_self _) _ (by
        rw [← ptr_add]; exact contains_off (by omega_using [hk]) hn)
    · rw [m₃]
      rcases (by omega_using [] : i < 8 * k ∨ 8 * k ≤ i) with hi' | hi'
      · rw [writeW64_off _ _ _ _ (sep_off D (a := dO + i) (n := 1) (b := dO + 8 * k) (k := 8) (by omega_using [hi'])
          (by omega_using [hdo, hk, hi]) (by omega_using [hdo, hk]) _ (by rw [BitVec.sub_self]; decide))]
        exact b₁ i hi'
      · rw [show D + BitVec.ofNat 64 (dO + i) = D + BitVec.ofNat 64 (dO + 8 * k) + BitVec.ofNat 64 (i - 8 * k) by
          rw [ptr_add, show dO + 8 * k + (i - 8 * k) = dO + i by omega_using [hi']], writeW64_byte _ _ _ (by omega_using [hi]),
          readW64_byte _ _ (by omega_using [hi]), ptr_add, show so + 8 * k + (i - 8 * k) = so + i by omega_using [hi']]
        refine f₁ _ fun r hr hc => ?_
        rw [List.mem_singleton.mp hr] at hc
        exact hsep _ (R.contains (A := fun _ => S) (b := 0) (k := i) (n := 1) (by omega_using [hk, hi]) hn) hc
  · refine List.ext_getElem (by simp only [bytesAt_length]) fun i h₁ _ => ?_
    rw [bytesAt_length] at h₁
    rw [bytesAt_getElem, bytesAt_getElem, ptr_add, ptr_add]
    exact b' i (by omega_using [h₁])


end VG.Proof.MlKem.AArch64.KeyGen

end

end


/-!
# The hashing decapsulation's message

`J(z ‖ c)` is absorbed by the matrix's first pairs (`Hybrid.pair3`) from a
copy of `z ‖ c` in `scratch`, just below `c'`'s buffer (`jM`, `Kem16.jSrc`):
`jM_ok`, where it lies. `startJ_ok`: the all-zero third state and the copy
(`Kem16.startJ`), after `m'`, `G(m' ‖ h)` and `ρ` (`AfterA`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Hybrid

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Proof.MlKem.AArch64.Decaps
open VG.Spec.Sha3 (stateAt bytesAt)
open VG.Spec.MlKem
open VG.Proof.MlKem

variable {P : KemLay}

/-- `z ‖ c`, copied to `scratch` (argument 3 of decapsulation) from `CB - 32`. -/
def jM (P : KemLay) : Msg := ⟨Impl.MlKem.AArch64.Kem16.jSrc P, 3, CB P - 32⟩

/-- `J`'s message. -/
abbrev jE (P : KemLay) (s₀ : State) : List Byte := KPke.dkZ P.params (dkD P s₀) ++ cD P s₀

theorem jM_base (s₀ : State) : ((jM P).reg s₀).base = sA (deL P) s₀ (CB P - 32) := rfl

theorem jM_ok {s₀ : State} (hp : Pre P (deL P) s₀) (hk : Stk128 P (deL P) s₀)
    (hs : SrcOk (Impl.MlKem.AArch64.Kem16.jSrc P)) : MsgOk P (deL P) (jM P) s₀ := by
  have hw := hp.wf
  obtain f : CB P - 32 + (32 + P.ctLen) ≤ SV P + 48 := by lom
  have e : (jM P).reg s₀ = R (kA s₀) (deL P).sc (CB P - 32) (32 + P.ctLen) := rfl
  refine ⟨hs, fun s h => ?_, fun s h => ?_, ?_, fun r hr => ?_, ?_, fun e' he => ?_, ?_⟩
  · show s.gpr .x28 + BitVec.ofNat 64 (CB P - 32) = _
    rw [jM_base, e28 h]
  · rw [e]; exact cov_sr hp h f
  · rw [e]; exact sdisj hp (by lom) f (.inl (by lom))
  · rw [e]
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · exact sdisj hp f (by lom) (.inr (by lom))
    · exact sdisj hp f (by lom) (.inr (by lom))
    · exact sdisj hp f (by lom) (.inr (by lom))
    · exact below_R hp hp.scb (hp.fs f)
  · rw [e]; exact sdisj hp f (by lom) (.inr (by lom))
  · rw [e]; exact sdisj hp f (by lom) (.inr (by lom))
  · rw [e]; exact hk.R hp.scb (hp.fs f)

/-- After the first phase and `Kem16.startJ`. -/
structure AfterJ (P : KemLay) (s₀ s : State) : Prop where
  a : AfterA P s₀ s
  zero : stateAt s.mem (kA s₀ (deL P).sc) = Spec.Sha3.zero
  msg : bytesAt s.mem ((jM P).reg s₀).base (jM P).S.len = jE P s₀

theorem startJ_ok {s₀ sQ : State} (hp : Pre P (deL P) s₀) (h8 : 8 * (P.ctLen / 8) = P.ctLen)
    (hA : AfterA P s₀ sQ) :
    WP isa (.block (Impl.MlKem.AArch64.Kem16.startJ P)) sQ (AfterJ P s₀) := by
  have hw := hp.wf
  have kbA := hA.kb
  unfold Impl.MlKem.AArch64.Kem16.startJ
  rw [WP.block_append_iff, WP.block_append_iff]
  -- the third state
  obtain hS := hsetup hp kbA (by decide : 136 ∈ Spec.Sha3.rates)
  refine WP.mono (zeroState_ok hS (s := sQ) ⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩) fun s₁ ⟨k₁, z₁⟩ => ?_
  obtain e28' : ∀ o l, (⟨sQ.gpr .x28 + BitVec.ofNat 64 o, l⟩ : Region) = R (kA s₀) (deL P).sc o l :=
    fun o l => by rw [kbA.x28]
  obtain kb₁ := kbA.call k₁ fun r hr => by
    rw [List.mem_singleton.mp hr, VG.Proof.MlKem.AArch64.STr, e28']; exact safe_scr hp (by lom)
  obtain far₁ : ∀ {o l : Nat}, o + l ≤ SV P + 48 → 200 ≤ o →
      bytesAt s₁.mem (sA (deL P) s₀ o) l = bytesAt sQ.mem (sA (deL P) s₀ o) l := fun f h => by
    refine bytesAt_frame k₁.frame (fun r hr => ?_) (by lom)
    rw [List.mem_singleton.mp hr, VG.Proof.MlKem.AArch64.STr, e28']
    exact sdisj hp f (by lom) (.inr (by simp only [KEM.ST]; omega_using [h]))
  obtain z₁' : stateAt s₁.mem (kA s₀ (deL P).sc) = Spec.Sha3.zero := by
    rw [kbA.x28, show KEM.ST = 0 from rfl, ptr_zero] at z₁; exact z₁
  obtain x24₁ : s₁.gpr .x24 = 1 := by rw [k₁.cs _ (by decide) (by decide), hA.x24]
  -- `z`
  refine WP.mono (KeyGen.copy_ok (S := kA s₀ 0) (D := kA s₀ 3) (so := 768 * P.k + 64) (dO := CB P - 32)
    (by decide) (by decide) (by lom) (by lom)
    (hp.args.rdisj (by dek) (by dek) (by dek) (hp.fs (by lom)) (by dek) (by dek))
    kb₁.x25 kb₁.x28 (cov_r hp kb₁ (b := 0) (by dek) (by dek)) (cov_s hp kb₁ (by lom)))
    fun s₂ ⟨k₂, f₂, b₂⟩ => ?_
  obtain kb₂ := kb₁.frame k₂ f₂ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact safe_scr hp (by lom)
  obtain far₂ : ∀ {o l : Nat}, o + l ≤ SV P + 48 → (o + l ≤ CB P - 32 ∨ CB P ≤ o) →
      bytesAt s₂.mem (sA (deL P) s₀ o) l = bytesAt s₁.mem (sA (deL P) s₀ o) l := fun f h => by
    refine bytesAt_frame f₂ (fun r hr => ?_) (by lom)
    rw [List.mem_singleton.mp hr]
    exact sdisj hp f (by lom) (by lom)
  obtain st₂ : stateAt s₂.mem (kA s₀ (deL P).sc) = Spec.Sha3.zero := by
    rw [VG.Proof.Sha3.AArch64.Hybrid.X3.stateAt_frame f₂ (fun r hr => by
      rw [List.mem_singleton.mp hr, stR_sc]; exact sdisj hp (by lom) (by lom) (.inl (by lom)))]
    exact z₁'
  obtain x24₂ : s₂.gpr .x24 = 1 := by rw [k₂.get .x24, x24₁]
  -- `c`
  refine WP.mono (KeyGen.copyN_ok (n := P.ctLen / 8) (S := kA s₀ 1) (D := kA s₀ 3) (so := 0) (dO := CB P)
    (by lom) (by decide) (by decide) ⟨by decide, by lom⟩ ⟨by lom, by lom⟩
    (by rw [h8]; exact hp.args.rdisj (by dek) (by dek) (by dek) (hp.fs (by lom)) (by dek) (by dek))
    kb₂.x26 kb₂.x28 (by rw [h8]; exact cov_r hp kb₂ (b := 1) (by dek) (by dek))
    (by rw [h8]; exact cov_s hp kb₂ (by lom)))
    fun s₃ ⟨k₃, f₃, b₃⟩ => ?_
  rw [h8] at f₃ b₃
  obtain kb₃ := kb₂.frame k₃ f₃ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact safe_scr hp (by lom)
  obtain far₃ : ∀ {o l : Nat}, o + l ≤ SV P + 48 → (o + l ≤ CB P ∨ CB P + P.ctLen ≤ o) →
      bytesAt s₃.mem (sA (deL P) s₀ o) l = bytesAt s₂.mem (sA (deL P) s₀ o) l := fun f h => by
    refine bytesAt_frame f₃ (fun r hr => ?_) (by lom)
    rw [List.mem_singleton.mp hr]
    exact sdisj hp f (by lom) h
  obtain keep : ∀ {o l : Nat}, o + l ≤ CB P - 32 → 200 ≤ o →
      bytesAt s₃.mem (sA (deL P) s₀ o) l = bytesAt sQ.mem (sA (deL P) s₀ o) l := fun h h' => by
    rw [far₃ (by lom) (.inl (by lom)), far₂ (by lom) (.inl h), far₁ (by lom) h']
  refine ⟨⟨kb₃, by rw [k₃.get .x24, x24₂], ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [keep (by lom) (by decide)]; exact hA.m
  · rw [keep (by lom) (by decide)]; exact hA.kp
  · rw [keep (by lom) (by decide)]; exact hA.r
  · rw [keep (by lom) (by decide)]; exact hA.rho
  · rw [VG.Proof.Sha3.AArch64.Hybrid.X3.stateAt_frame f₃ (fun r hr => by
      rw [List.mem_singleton.mp hr, stR_sc]; exact sdisj hp (by lom) (by lom) (.inl (by lom)))]
    exact st₂
  · -- `z ‖ c`
    show bytesAt s₃.mem (kA s₀ 3 + BitVec.ofNat 64 (CB P - 32)) (32 + P.ctLen) = _
    rw [bytesAt_add, ptr_add, show CB P - 32 + 32 = CB P by lom, b₃,
      show bytesAt s₃.mem (kA s₀ 3 + BitVec.ofNat 64 (CB P - 32)) 32 =
        bytesAt s₂.mem (kA s₀ 3 + BitVec.ofNat 64 (CB P - 32)) 32 from far₃ (by lom) (.inl (by lom)), b₂,
      kb₂.ro_bytes (b := 1) (by dek) (by dek), ptr_zero]
    obtain hz := slice_eq kb₁ (b := 0) (o := 768 * P.k + 64) (n := 32) (by decide) (by dek)
    rw [show (deL P).slot 0 = 0 from rfl] at hz
    rw [hz]
    rfl

/-- `decapsAArch64 P`, with 128 bytes of stack. -/
def decapsAArch64S (P : KemLay) : Contract AArch64.isa where
  pre s :=
    let dk : Region := ⟨s.gpr .x0, P.dkLen⟩
    let ct : Region := ⟨s.gpr .x1, P.ctLen⟩
    let key : Region := ⟨s.gpr .x2, 32⟩
    let scratch : Region := ⟨s.gpr .x3, P.scl⟩
    let stack : Region := ⟨s.sp - 128, 128⟩
    s.rd = [dk, ct] ∧ s.wr = [key, scratch] ∧ dk.Disjoint key ∧ dk.Disjoint scratch ∧ ct.Disjoint key ∧
    ct.Disjoint scratch ∧ key.Disjoint scratch ∧ 128 ≤ s.sp.toNat ∧ stack.Disjoint dk ∧ stack.Disjoint ct ∧
    stack.Disjoint key ∧ stack.Disjoint scratch
  post := (decapsAArch64 P).post
  pub := (decapsAArch64 P).pub

theorem preSD {s : State} (h : (decapsAArch64S P).pre s) : (decapsAArch64 P).pre s ∧ Stk128 P (deL P) s := by
  obtain ⟨rd, wr, d02, d03, d12, d13, d23, sp128, k0, k1, k2, k3⟩ := h
  obtain sub : Region.Sub ⟨s.sp - 16, 16⟩ (frame s.sp) := below_sub (by decide) (by decide)
  refine ⟨⟨rd, wr, d02, d03, d12, d13, d23, by omega_using [sp128],
    k0.sub_left sub, k1.sub_left sub, k2.sub_left sub, k3.sub_left sub⟩, sp128, ?_⟩
  intro b hb
  have hb : b < 4 := hb
  rcases (by omega_using [hb] : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl
  · exact k0
  · exact k1
  · exact k2
  · exact k3

end VG.Proof.MlKem.AArch64.Hybrid

end

end

/-! # The 16-bit decapsulation's postcondition and `J(z ‖ c)`

`DoneW` and `post_ofW`: what the re-encryption, the comparison and the
selection leave, and the decapsulation's postcondition from it; `tailJ_ok`:
`J(z ‖ c)` from the third state to `JB` (`Kem16.tailJ`), for
`Kem16P/Decaps.lean`. -/

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Optimized/KemMatrix.lean`, which only this module imported.

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Decaps
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
variable {P : KemLay}
variable {prf : Nat→Nat→Prog isa}

/-- `c'`, with `Â` stored with 16 bits. -/
abbrev cprW (P : KemLay) (s₀ : State) (mB : Mem) : List Byte :=
  KPke.ct P.params (aMW true P (deL P) s₀ mB) (KPke.dkEk P.params (dkD P s₀)) (mD P s₀) (gD P s₀).2

/-- What the function leaves, with `Â` stored with 16 bits. -/
structure DoneW (P : KemLay) (s₀ : State) (mB : Mem) (v : BitVec 64) (s : State) : Prop where
  abi : abiPreserved s₀ s
  x0 : s.gpr .x0 = v
  key : bytesAt s.mem (kA s₀ 2) 32 = if cD P s₀ = cprW P s₀ mB then (gD P s₀).1 else jD P s₀

theorem post_ofW {s₀ sB s' : State} {mA : Mem} (hB : BInvW true P (deL P) s₀ mA (rhoD P s₀) (P.k * P.k) sB)
    (hD : DoneW P s₀ sB.mem (sB.gpr .x24) s') : (decapsAArch64 P).post s₀ s' := by
  show Outcome (fun iters => decapsInternal P.params iters (bytesAt s₀.mem (s₀.gpr .x0) P.dkLen)
    (bytesAt s₀.mem (s₀.gpr .x1) P.ctLen)) ((s'.gpr .x0).setWidth 32) (bytesAt s'.mem (s₀.gpr .x2) 32)
  have key : bytesAt s'.mem (s₀.gpr .x2) 32 =
      if cD P s₀ = cprW P s₀ sB.mem then (gD P s₀).1 else jD P s₀ := hD.key
  rw [key, hD.x0]
  rcases hB.outcome with ⟨h1, hs⟩ | ⟨h0, i, hi, j, hj, hn⟩
  · rw [h1]
    refine .inl ⟨rfl, 280, ?_⟩
    show decapsInternal P.params 280 (dkD P s₀) (cD P s₀) = _
    rw [KPke.decapsInternal_eq, KPke.kpkeEncrypt_some (p := P.params) ⟨rfl, rfl⟩
      (a := aMW true P (deL P) s₀ sB.mem) fun i hi j hj => by rw [KPke.ekRho_dkEk]; exact hs i hi j hj]
    rfl
  · rw [h0]
    refine .inr ⟨rfl, ?_⟩
    show decapsInternal P.params 280 (dkD P s₀) (cD P s₀) = none
    rw [KPke.decapsInternal_eq, KPke.kpkeEncrypt_none (p := P.params) hi hj (by rw [KPke.ekRho_dkEk]; exact hn)]
    rfl

/-- `BInvW` carried over writes apart from `ρ` and `Â`, from the memory written. -/
theorem binv_move {w16 : Bool} {L : Layout} {s₀ s t : State} {mA : Mem} {ρ : List Byte} {n : Nat}
    (h : BInvW w16 P L s₀ mA ρ n s) (hk : KB P L s₀ t) (h24 : t.gpr .x24 = s.gpr .x24) {rs : List Region}
    (hf : Frame rs s.mem t.mem) (hρ : ∀ r ∈ rs, (R (kA s₀) L.sc SB 32).Disjoint r)
    (hA : ∀ e < n, ∀ r ∈ rs, (polyRegion (aP L s₀ e)).Disjoint r) : BInvW w16 P L s₀ t.mem ρ n t := by
  refine ⟨hk, Frame.refl _ _, ?_, by rw [h24]; exact h.acc, fun e he => reducedW_frame hf (hA e he) (h.red e he),
    fun e he => ?_⟩
  · rw [bytesAt_frame hf hρ (by decide)]; exact h.rho
  · rw [polyAtW_frame hf (hA e he)]; exact h.res e he

/-- `J(z ‖ c)`, the first 32 bytes of the third state, to `JB` (`Kem16.tailJ`). -/
theorem tailJ_ok {s₀ sB : State} (hp : Pre P (deL P) s₀) {ρ : List Byte} {n : Nat} (hn : n ≤ P.k * P.k)
    (hB : BInvW true P (deL P) s₀ sB.mem ρ n sB)
    (hst : Spec.Sha3.stateAt sB.mem (kA s₀ (deL P).sc) =
      Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 (BitVec.ofNat 8 0x1f) (Hybrid.jE P s₀))) :
    WP isa (.block Impl.MlKem.AArch64.Kem16.tailJ) sB fun t =>
      BInvW true P (deL P) s₀ t.mem ρ n t ∧ t.gpr .x24 = sB.gpr .x24 ∧
      bytesAt t.mem (sA (deL P) s₀ JB) 32 = jD P s₀ ∧
      (∀ {o l : Nat}, o + l ≤ SV P + 48 → (o + l ≤ JB ∨ JB + 32 ≤ o) →
        bytesAt t.mem (sA (deL P) s₀ o) l = bytesAt sB.mem (sA (deL P) s₀ o) l) ∧
      Frame [R (kA s₀) (deL P).sc JB 32] sB.mem t.mem := by
  have hw := hp.wf
  refine WP.mono (KeyGen.copy_ok (S := kA s₀ 3) (D := kA s₀ 3) (so := KEM.ST) (dO := JB)
    (by decide) (by decide) (by decide) (by decide) (sdisj hp (by lom) (by lom) (by lom))
    hB.kb.x28 hB.kb.x28 (cov_sr hp hB.kb (by lom)) (cov_s hp hB.kb (by lom))) fun t ⟨k, f, b⟩ => ?_
  have kb := hB.kb.frame k f (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact safe_scr hp (by lom)
  have far : ∀ {o l : Nat}, o + l ≤ SV P + 48 → (o + l ≤ JB ∨ JB + 32 ≤ o) →
      bytesAt t.mem (sA (deL P) s₀ o) l = bytesAt sB.mem (sA (deL P) s₀ o) l := fun hf h => by
    refine bytesAt_frame f (fun r hr => ?_) (by lom)
    rw [List.mem_singleton.mp hr]; exact sdisj hp hf (by lom) h
  refine ⟨binv_move hB kb (k.get .x24) f (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact sdisj hp (by lom) (by lom) (by lom))
    (fun e he r hr => by
      rw [List.mem_singleton.mp hr]
      exact sdisj hp (o₁ := AH + 1024 * e) (l₁ := 1024) (by lom) (by lom) (.inr (by lom))),
    k.get .x24, ?_, far, f⟩
  rw [show sA (deL P) s₀ JB = kA s₀ 3 + BitVec.ofNat 64 JB from rfl, b,
    show KEM.ST = 0 from rfl, ptr_zero]
  show _ = J (Hybrid.jE P s₀)
  rw [J_eq, Hybrid.bytesAt_squeeze]
  show Spec.Sha3.squeezeFrom 136 (Spec.Sha3.stateAt sB.mem (kA s₀ (deL P).sc)) 0 32 = _
  rw [hst]; rfl

end VG.Proof.MlKem.AArch64.Decaps
