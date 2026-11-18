module

public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Fn
public import VerifiedGarbage.Proof.AesGcm.Scratch
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.AesGcm.PPC64LE
public import VerifiedGarbage.Impl.AesGcm.PPC64LE.SealFused
public import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Groups
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Init
import VerifiedGarbage.Proof.AesGcm.PPC64LE.InitCT
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamInit
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamFinish
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamVerify
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTFin
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTVerify
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Seal
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTSeal
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Open
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTOpen
import VerifiedGarbage.Proof.Framework.SigEval
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.Impl.StackScratch.PPC64LE.Args
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchArgs
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTBase
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTCrypt
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTText
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CryptOk
import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTBase
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Fn
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTCrypt
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTText
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CryptOk
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.InitCT
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamCrypt
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Env
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTJ0
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTJ0
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamInit
public import VerifiedGarbage.Proof.Aes.SboxSpec
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.PPC64LE.StraightK
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.Gcm.Ctr
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
meta import VerifiedGarbage.Proof.Gcm.Compose
meta import VerifiedGarbage.Proof.Gcm.Ctr
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Impl.AesGcm.PPC64LE

/-! ### `AesGcm.PPC64LE.StreamCT`, which only this module used -/

section

/-! ### `AesGcm.PPC64LE.StreamAad`, which this module and modules that import it used -/

section

/-!
# AES-GCM on PPC64LE: `vg_aes_gcm_stream_aad`

Untrusted: everything here is checked by Lean. The entry saves our caller's
registers and sets up `absorb`'s arguments (`aadEntry_ok`); `absorb 16`
absorbs the data into the accumulator (`aad_run`), which keeps the rest of
the state (`streamAad_wp`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom StreamRepr)
open VG.Proof.Gcm (Absorbed Ctr)

/-- The entry: `absorb`'s arguments. -/
theorem aadEntry_ok {s : State} (hW : Covers [⟨s.gpr .r8, 2560⟩] s.wr) :
    WP isa (.block streamAadPre) s fun s' => Entered s (s.gpr .r8) s' ∧
      s'.gpr .r31 = s.gpr .r8 ∧ s'.gpr .r30 = s.gpr .r4 ∧ s'.gpr .r29 = s.gpr .r3 ∧
      s'.gpr .r24 = s.gpr .r6 ∧ s'.gpr .r25 = s.gpr .r7 ∧
      s'.gpr .r26 = BitVec.ofNat 64 ((s.gpr .r5).toNat % 16) := by
  refine WP.block_append (WP.mono (save_ok (b := .r8) (by decide) hW) fun s₁ ⟨hg, h31, hk, hsv, hf⟩ => ?_)
  have e3 : s₁.gpr .r3 = s.gpr .r3 := hg _ (by decide) (by decide)
  have e4 : s₁.gpr .r4 = s.gpr .r4 := hg _ (by decide) (by decide)
  have e5 : s₁.gpr .r5 = s.gpr .r5 := hg _ (by decide) (by decide)
  have e6 : s₁.gpr .r6 = s.gpr .r6 := hg _ (by decide) (by decide)
  have e7 : s₁.gpr .r7 = s.gpr .r7 := hg _ (by decide) (by decide)
  crun [mov, BitVec.or_self, e3, e4, e5, e6, e7, h31, and15]
  exact ⟨fun r hr => by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [hg],
    ⟨hk.rd, hk.wr, hk.sp, hk.lr⟩, hsv, hf⟩

/-- The regions `stream_aad` writes. -/
abbrev aadFrame (St W : Addr) : List Region := savedR W :: absFrame St W 16

/-- After the entry: `absorb`'s precondition, for additional data `x` so far
of `aad_len` bytes modulo 16. -/
theorem aad_entry {s : State} (hs : streamAadPPC64LE.pre s) {x : List Byte}
    (hx : x.length % 16 = (s.gpr .r5).toNat % 16) :
    WP isa (.block streamAadPre) s fun s₁ => Entered s (s.gpr .r8) s₁ ∧ s₁.gpr .r29 = s.gpr .r3 ∧
      s₁.gpr .r30 = s.gpr .r4 ∧ s₁.gpr .r31 = s.gpr .r8 ∧
      AbsIn s₁.gpr s.sp 16 (Spec.Gcm.ctxH s.mem (s.gpr .r3)) x (s.gpr .r6) (s.gpr .r7).toNat s₁ ∧
      bytesAt s₁.mem (s.gpr .r6) (s.gpr .r7).toNat = bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat := by
  simp only [streamAadPPC64LE] at hs
  obtain ⟨hrd, hwr, dcs, dcw, dds, ddw, dsw, wc, wd, ws, ww⟩ := hs
  generalize hCtx : s.gpr .r3 = Ctx at *
  generalize hSt : s.gpr .r4 = St at *
  generalize hD : s.gpr .r6 = D at *
  generalize hn : (s.gpr .r7).toNat = n at *
  generalize hW : s.gpr .r8 = W at *
  have hlt : n < 2 ^ 64 := hn ▸ (s.gpr .r7).isLt
  have hn' : s.gpr .r7 = BitVec.ofNat 64 n := by rw [← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hWc : Covers [⟨W, 2560⟩] s.wr := by rw [hwr]; exact covers_mem (by simp)
  refine WP.mono (aadEntry_ok (by rw [hW]; exact hWc)) fun s₁ ⟨en, h31, h30, h29, h24, h25, h26⟩ => ?_
  rw [hW] at en h31
  rw [hSt] at h30
  rw [hCtx] at h29
  rw [hD] at h24
  rw [hn'] at h25
  have perm : Perm Ctx St W s₁ :=
    (⟨covers_mem (by rw [hrd, hwr]; simp), covers_mem (by rw [hwr]; simp), hWc⟩ : Perm Ctx St W s).of_eq
      en.keeps.rd en.keeps.wr
  have he : Env s₁.gpr s.sp s₁ := ⟨fun _ _ => rfl, en.keeps.sp, by rw [h29, h30, h31]; exact perm⟩
  have sW : Region.Sub (savedR W) ⟨W, 2560⟩ := Offset.sub_base _ (by decide)
  have hdat : bytesAt s₁.mem D n = bytesAt s.mem D n :=
    bytesAt_frame en.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ddw.sub_right sW) (by omega_using [hn])
  have hH : blockAt s₁.mem (s₁.gpr .r29 + BitVec.ofNat 64 240) = Spec.Gcm.ctxH s.mem Ctx := by
    rw [h29, ctxH_eq]
    exact blockAt_frame en.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (dcw.sub_left (Offset.sub_base _ (by decide))).sub_right sW)
  refine ⟨en, h29, h30, h31, ⟨he, h24, h25, by rw [h26, hx], ?_, hH⟩, hdat⟩
  rw [h30, h31]
  exact ⟨by rw [en.keeps.rd, en.keeps.wr, hrd]; exact covers_mem (by simp), hlt, wd, dds, ddw⟩

/-- One run of `stream_aad`, for additional data `x` so far of `aad_len` bytes
modulo 16. -/
theorem aad_run [VG.Proof.Gcm.PPC64LE.GhashLaw] {s : State} (hs : streamAadPPC64LE.pre s) {x : List Byte}
    (hx : x.length % 16 = (s.gpr .r5).toNat % 16) :
    WP isa streamAad s fun s' => abiPreserved s s' ∧
      (Absorbed s.mem (s.gpr .r4 + BitVec.ofNat 64 16) (s.gpr .r4 + BitVec.ofNat 64 32)
          (Spec.Gcm.ctxH s.mem (s.gpr .r3)) x →
        Absorbed s'.mem (s.gpr .r4 + BitVec.ofNat 64 16) (s.gpr .r4 + BitVec.ofNat 64 32)
          (Spec.Gcm.ctxH s.mem (s.gpr .r3)) (x ++ bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat)) ∧
      Frame (aadFrame (s.gpr .r4) (s.gpr .r8)) s.mem s'.mem := by
  have hs' := hs
  obtain ⟨-, -, dcs, dcw, -, -, dsw, wc, -, ws, ww⟩ := hs'
  have L₀ : Lay (s.gpr .r3) (s.gpr .r4) (s.gpr .r8) := Lay.of wc ws ww dcs dcw dsw
  refine WP.seq (WP.mono (aad_entry hs hx) fun s₁ ⟨en, h29, h30, h31, hIn, hdat⟩ => ?_)
  have dS : ∀ (d k : Nat), d + k ≤ 80 →
      (⟨s.gpr .r4 + BitVec.ofNat 64 d, k⟩ : Region).Disjoint (savedR (s.gpr .r8)) :=
    fun d k h => L₀.st_w h (.inr ⟨by decide, by decide⟩)
  have hA : ∀ (m : Mem), Frame [savedR (s.gpr .r8)] s.mem m →
      Absorbed s.mem (s.gpr .r4 + BitVec.ofNat 64 16) (s.gpr .r4 + BitVec.ofNat 64 32)
        (Spec.Gcm.ctxH s.mem (s.gpr .r3)) x →
      Absorbed m (s.gpr .r4 + BitVec.ofNat 64 16) (s.gpr .r4 + BitVec.ofNat 64 32)
        (Spec.Gcm.ctxH s.mem (s.gpr .r3)) x :=
    fun m hf ha => ha.congr (blockAt_frame hf fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dS 16 16 (by decide))
      (bytesAt_frame hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (dS 32 16 (by decide)).sub_left (Region.sub_prefix (Nat.le_of_lt (Nat.mod_lt _ (by decide)))))
        (by omega_using []))
  refine WP.seq (WP.mono (absorb_ok (L₀.v h29 h30 h31) (.inr rfl) hIn) fun s₂ h₂ => ?_)
  have f₂ := h₂.frame
  rw [h30, h31] at f₂
  have hsv : SavedAt s₂.mem (s.gpr .r8) s := en.saved.frame f₂ (saved_absFrame L₀ (.inr rfl))
  have e31 : s₂.gpr .r31 = s.gpr .r8 := (h₂.env.fr _ (by decide)).trans h31
  refine WP.mono (restore_ok e31 (by
      have := h₂.env.perm.w; rw [h31] at this; exact Covers.right this) hsv h₂.env.sp
    (fun r hr => by
      rw [h₂.env.fr r (by revert hr; revert r; decide)]; exact en.low r hr))
    fun s' ⟨ga, hm, _⟩ => ⟨ga, fun ha => ?_, ?_⟩
  · have := h₂.abs
    rw [h30, hdat] at this
    rw [hm]; exact this (hA _ en.frame ha)
  · rw [hm]
    exact (en.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩).trans
      (f₂.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)

theorem streamAad_wp [VG.Proof.Gcm.PPC64LE.GhashLaw] {s : State} (hs : streamAadPPC64LE.pre s) :
    WP isa streamAad s fun s' => abiPreserved s s' ∧ streamAadPPC64LE.post s s' := by
  have hz : (Spec.Gcm.zeros ((s.gpr .r5).toNat % 16)).length % 16 = (s.gpr .r5).toNat % 16 := by
    rw [Proof.Gcm.length_zeros, Nat.mod_mod]
  refine WP.mono (WP.forall_det (P := fun (i : (Block → Block) × List Byte × List Byte) =>
      StreamRepr s.mem (s.gpr .r4) i.1 (Spec.Gcm.ctxH s.mem (s.gpr .r3)) i.2.1 i.2.2 [] ∧
        s.gpr .r5 = BitVec.ofNat 64 i.2.2.length)
    (Q := fun i s' => StreamRepr s'.mem (s.gpr .r4) i.1 (Spec.Gcm.ctxH s.mem (s.gpr .r3)) i.2.1
      (i.2.2 ++ bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat) [])
    (aad_run hs hz) fun ⟨ciph, iv, a⟩ ⟨hr, hl⟩ => ?_) fun s' ⟨⟨ga, _, _⟩, h⟩ =>
      ⟨ga, fun ciph iv a hr hl => h ⟨ciph, iv, a⟩ ⟨hr, hl⟩⟩
  have hx : a.length % 16 = (s.gpr .r5).toNat % 16 := by rw [hl, toNat_mod16]
  obtain ⟨hj, ha, hc⟩ := Proof.Gcm.streamRepr_iff.mp hr
  have hs' := hs
  simp only [streamAadPPC64LE] at hs'
  obtain ⟨-, -, -, -, -, -, dsw, -, -, ws, ww⟩ := hs'
  have dSt : ∀ r ∈ aadFrame (s.gpr .r4) (s.gpr .r8), ∀ d, d + 16 ≤ 80 → (d + 16 ≤ 16 ∨ 48 ≤ d) →
      (⟨s.gpr .r4 + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := by
    intro r hr d hd hd'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have st_off : ∀ e k, e + k ≤ 80 → (d + 16 ≤ e ∨ e + k ≤ d) →
        (⟨s.gpr .r4 + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint ⟨s.gpr .r4 + BitVec.ofNat 64 e, k⟩ :=
      fun e k he h => Offset.disjoint _ h (by omega_using [hd]) (by omega_using [he])
    rcases hr with rfl | rfl | rfl | rfl
    · exact (dsw.sub_left (Offset.sub_base _ (by omega_using [hd]))).sub_right (Offset.sub_base _ (by decide))
    · exact st_off 16 16 (by decide) (by omega_using [hd'])
    · exact st_off 32 16 (by decide) (by omega_using [hd'])
    · exact (dsw.sub_left (Offset.sub_base _ (by omega_using [hd]))).sub_right (Offset.sub_base _ (by decide))
  refine WP.mono (aad_run hs hx) fun s' ⟨_, habs, hf⟩ => ?_
  refine Proof.Gcm.streamRepr_iff.mpr ⟨?_, ?_, ?_⟩
  · rw [← hj]
    have := blockAt_frame hf fun r hr => by simpa using dSt r hr 0 (by decide) (.inl (by decide))
    simpa using this
  · exact habs ha
  · refine hc.congr ?_ ?_
    · exact blockAt_frame hf fun r hr => dSt r hr 48 (by decide) (.inr (by decide))
    · exact blockAt_frame hf fun r hr => dSt r hr 64 (by decide) (.inr (by decide))

end VG.Proof.AesGcm.PPC64LE

end

end

/-!
# AES-GCM on PPC64LE: `vg_aes_gcm_stream_init` and `vg_aes_gcm_stream_aad` are constant time

Untrusted: everything here is checked by Lean. The entry by the taint
analysis from the public arguments; then `j0` (`j0_ct`) or `absorb 16`
(`absorb_ct`) from the invariants the entry's correctness gives; then the
exit from `W`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE

theorem streamInitPre_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint
    (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) (.block streamInitPre) h).isSome = true := ⟨_, by taint_decide⟩

theorem streamAadPre_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint
    (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8]) (.block streamAadPre) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem streamInit_ct [VG.Proof.Gcm.PPC64LE.GhashLaw] : ConstantTime isa streamInitPPC64LE.pre streamInitPPC64LE.pub streamInit := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q3, q4, q5, q6, q7, qsp⟩ := hq
  have L : Lay (σ₁.gpr .r3) (σ₁.gpr .r6) (σ₁.gpr .r7) := by
    obtain ⟨-, -, dcs, dcw, -, -, dsw, wc, -, ws, ww⟩ := h₁
    exact Lay.of wc ws ww dcs dcw dsw
  let I₀ : State → Prop := fun s => streamInitPPC64LE.pre s ∧ s.gpr .r3 = σ₁.gpr .r3 ∧
    s.gpr .r4 = σ₁.gpr .r4 ∧ s.gpr .r5 = σ₁.gpr .r5 ∧ s.gpr .r6 = σ₁.gpr .r6 ∧ s.gpr .r7 = σ₁.gpr .r7 ∧
    s.sp = σ₁.sp
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm, q4.symm, q5.symm, q6.symm, q7.symm,
    qsp.symm⟩, ?_⟩
  refine CT.seq (J := J0I (σ₁.gpr .r3) (σ₁.gpr .r6) (σ₁.gpr .r7) σ₁.sp (σ₁.gpr .r4) (σ₁.gpr .r5).toNat) ?_
    (fun s ⟨hs, e3, e4, e5, e6, e7, esp⟩ => WP.mono (si_entry hs) fun s₁ ⟨_, h29, h30, h31, hJ, _⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := streamInitPre_taint
    exact CT.taintEq (I := I₀) _ σ₁.gpr σ₁.sp (fun s ⟨_, e3, e4, e5, e6, e7, esp⟩ =>
      ⟨esp, by simp [e3, e4, e5, e6, e7]⟩) hc
  · rw [e3] at h29
    rw [e6] at h30
    rw [e7] at h31
    rw [e3, e4, e5, esp] at hJ
    exact ⟨s₁.gpr, _, h29, h30, h31, hJ⟩
  refine CT.seq (J := fun s => s.gpr .r31 = σ₁.gpr .r7 ∧ s.sp = σ₁.sp) (j0_ct L)
    (fun s ⟨V, H, h29, h30, h31, hJ⟩ => WP.mono (j0_ok (L.v h29 h30 h31) hJ) fun s₂ h₂ =>
      ⟨(h₂.env.fr _ (by decide)).trans h31, h₂.env.sp⟩) ?_
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => σ₁.gpr .r7) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

theorem streamAad_ct [VG.Proof.Gcm.PPC64LE.GhashLaw] : ConstantTime isa streamAadPPC64LE.pre streamAadPPC64LE.pub streamAad := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q3, q4, q5, q6, q7, q8, qsp⟩ := hq
  have L : Lay (σ₁.gpr .r3) (σ₁.gpr .r4) (σ₁.gpr .r8) := by
    obtain ⟨-, -, dcs, dcw, -, -, dsw, wc, -, ws, ww⟩ := h₁
    exact Lay.of wc ws ww dcs dcw dsw
  let q := (σ₁.gpr .r5).toNat % 16
  have hq16 : q < 16 := Nat.mod_lt _ (by decide)
  let I₀ : State → Prop := fun s => streamAadPPC64LE.pre s ∧ s.gpr .r3 = σ₁.gpr .r3 ∧
    s.gpr .r4 = σ₁.gpr .r4 ∧ s.gpr .r5 = σ₁.gpr .r5 ∧ s.gpr .r6 = σ₁.gpr .r6 ∧ s.gpr .r7 = σ₁.gpr .r7 ∧
    s.gpr .r8 = σ₁.gpr .r8 ∧ s.sp = σ₁.sp
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm, q4.symm, q5.symm, q6.symm, q7.symm,
    q8.symm, qsp.symm⟩, ?_⟩
  refine CT.seq (J := AbsI (σ₁.gpr .r3) (σ₁.gpr .r4) (σ₁.gpr .r8) σ₁.sp 16 (σ₁.gpr .r6) (σ₁.gpr .r7).toNat q)
    ?_ (fun s ⟨hs, e3, e4, e5, e6, e7, e8, esp⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := streamAadPre_taint
    exact CT.taintEq (I := I₀) _ σ₁.gpr σ₁.sp (fun s ⟨_, e3, e4, e5, e6, e7, e8, esp⟩ =>
      ⟨esp, by simp [e3, e4, e5, e6, e7, e8]⟩) hc
  · have hx : (List.replicate q (0 : Byte)).length % 16 = (s.gpr .r5).toNat % 16 := by
      rw [List.length_replicate, e5, Nat.mod_mod]
    refine WP.mono (aad_entry hs hx) fun s₁ ⟨_, h29, h30, h31, hIn, _⟩ => ?_
    rw [e3] at h29 hIn
    rw [e4] at h30
    rw [e8] at h31
    rw [e6, e7, esp] at hIn
    exact ⟨s₁.gpr, _, _, h29, h30, h31, by rw [List.length_replicate, Nat.mod_mod], hIn⟩
  refine CT.seq (J := fun s => s.gpr .r31 = σ₁.gpr .r8 ∧ s.sp = σ₁.sp) (absorb_ct L (.inr rfl) hq16)
    (fun s ⟨V, H, x, h29, h30, h31, _, hs⟩ => WP.mono (absorb_ok (L.v h29 h30 h31) (.inr rfl) hs)
      fun s₂ h₂ => ⟨(h₂.env.fr _ (by decide)).trans h31, h₂.env.sp⟩) ?_
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => σ₁.gpr .r8) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

end VG.Proof.AesGcm.PPC64LE

end

end

/-! ### `AesGcm.PPC64LE.CTCryptFn`, which only this module used -/

section

/-!
# AES-GCM on PPC64LE: `vg_aes_gcm_stream_encrypt` and `vg_aes_gcm_stream_decrypt` are constant time

Untrusted: everything here is checked by Lean. The entry by the taint
analysis from the public arguments, which it keeps in registers the pieces
preserve (`DI`); then `crypt` (`crypt_ct`) and `textAbsorb`
(`textAbsorb_ct`), in either order, from the invariants their correctness
gives; then the exit from `W`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE

/-- After the entry: the arguments kept, `len` (`N`) bytes at `data` (`D`),
after `aad_len` (`A`) bytes of additional data and `text_len` (`T`) of
text, and `R` rounds. -/
def DI (c st w sp D : Addr) (R : Nat) (N A T : BitVec 64) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ V .r20 = D ∧ V .r19 = N ∧ V .r22 = A ∧
    V .r23 = T ∧ V .r28 = BitVec.ofNat 64 R ∧ (R = 10 ∨ R = 12 ∨ R = 14) ∧ Env V sp s ∧ DataW c st w s D N.toNat

/-- Before `crypt`, with the arguments kept. -/
def CI (c st w sp D : Addr) (R : Nat) (N A T : BitVec 64) (s : State) : Prop :=
  ∃ V icb P, V .r29 = c ∧ V .r30 = st ∧ V .r31 = w ∧ V .r20 = D ∧ V .r19 = N ∧ V .r22 = A ∧ V .r23 = T ∧
    P % 16 = T.toNat % 16 ∧ CrIn V sp R icb P D N.toNat s

theorem cryptEntry_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint
    (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10]) (.block cryptEntry) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem cryptEntryArgs_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint
    (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10]) (.block (cryptEntry ++ textArgs)) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem textArgs_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r19, .r20, .r23])
    (.block textArgs) h).isSome = true := ⟨_, by taint_decide⟩

/-- The entry. -/
theorem sc_DI {s₀ : State} (h : streamCryptPre s₀) :
    WP isa (.block cryptEntry) s₀ (DI (s₀.gpr .r3) (s₀.gpr .r5) (s₀.gpr .r10) s₀.sp (s₀.gpr .r8)
      (s₀.gpr .r4).toNat (s₀.gpr .r9) (s₀.gpr .r6) (s₀.gpr .r7)) :=
  WP.mono (sc1_wp (sc_W h)) fun s₁ h1 => ⟨s₁.gpr, h1.r29, h1.r30, h1.r31, h1.r20, h1.r19, h1.r22, h1.r23,
    by rw [h1.r28, BitVec.ofNat_toNat, BitVec.setWidth_eq], h.2.2.2.2.2.2.2.2.2.2.2.2, sc_env h h1,
    sc_dataW h h1.en.keeps.wr⟩

section
variable {c st w sp D : Addr} {R : Nat} {N A T : BitVec 64}

theorem di_ta {s : State} (h : DI c st w sp D R N A T s) : TA c st w sp D N A T s :=
  let ⟨V, h29, h30, h31, h20, h19, h22, h23, _, _, he, hd⟩ := h
  ⟨V, h29, h30, h31, h20, h19, h22, h23, he, hd.ok⟩

theorem ci_cr {s : State} (h : CI c st w sp D R N A T s) : CrI c st w sp R D N.toNat (T.toNat % 16) s :=
  let ⟨V, icb, P, h29, h30, h31, _, _, _, _, hP, ci⟩ := h
  ⟨V, icb, P, h29, h30, h31, hP, ci⟩

theorem ta_exit {s : State} (h : TA c st w sp D N A T s) : s.gpr .r31 = w ∧ s.sp = sp :=
  let ⟨_, _, _, h31, _, _, _, _, he, _⟩ := h
  ⟨(he.fr _ (by decide)).trans h31, he.sp⟩

/-- The arguments of `crypt`. -/
theorem di_textArgs {s : State} (h : DI c st w sp D R N A T s) :
    WP isa (.block textArgs) s (CI c st w sp D R N A T) := by
  obtain ⟨V, h29, h30, h31, h20, h19, h22, h23, h28, hR, he, hd⟩ := h
  refine WP.mono textArgs_ok fun s₂ ⟨h24, h25, h26, hg, hk⟩ => ?_
  have he₂ := he.keep (fun r hr => hg r (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide)) hk.sp hk.rd hk.wr
  exact ⟨V, 0, T.toNat, h29, h30, h31, h20, h19, h22, h23, rfl, he₂, by rw [h24, he.fr _ (by decide), h20],
    by rw [h25, he.fr _ (by decide), h19, BitVec.ofNat_toNat, BitVec.setWidth_eq],
    by rw [h26, he.fr _ (by decide), h23], h28, hR, by rw [h29, h30, h31]; exact hd.of_eq hk.rd hk.wr⟩

variable (L : Lay c st w)
include L

theorem ci_crypt {s : State} (h : CI c st w sp D R N A T s) : WP isa crypt s (TA c st w sp D N A T) := by
  obtain ⟨V, icb, P, h29, h30, h31, h20, h19, h22, h23, _, ci⟩ := h
  refine WP.mono (WP.with_rdwr (crypt_ok (L.v h29 h30 h31) ci)) fun s' ⟨co, rd, wr, _⟩ =>
    ⟨V, h29, h30, h31, h20, h19, h22, h23, co.env, ?_⟩
  have := ci.data.ok.of_eq rd wr
  rw [h30, h31] at this
  exact this

theorem di_textAbsorb [VG.Proof.Gcm.PPC64LE.GhashLaw] {s : State} (h : DI c st w sp D R N A T s) :
    WP isa textAbsorb s (DI c st w sp D R N A T) := by
  obtain ⟨V, h29, h30, h31, h20, h19, h22, h23, h28, hR, he, hd⟩ := h
  refine WP.mono (WP.with_rdwr (textAbsorb_ok (L.v h29 h30 h31) (a := List.replicate (A.toNat % 16) 0)
    (ct := List.replicate T.toNat 0) he rfl (by rw [h20, h19, h30, h31]; exact hd.ok) (by simp [h22])
    (by simp [h23]))) fun s' ⟨ta, rd, wr, _⟩ => ⟨V, h29, h30, h31, h20, h19, h22, h23, h28, hR, ta.env,
      hd.of_eq rd wr⟩

theorem ta_textAbsorb [VG.Proof.Gcm.PPC64LE.GhashLaw] {s : State} (h : TA c st w sp D N A T s) :
    WP isa textAbsorb s fun s' => s'.gpr .r31 = w ∧ s'.sp = sp := by
  obtain ⟨V, h29, h30, h31, h20, h19, h22, h23, he, hd⟩ := h
  exact WP.mono (textAbsorb_ok (L.v h29 h30 h31) (a := List.replicate (A.toNat % 16) 0)
    (ct := List.replicate T.toNat 0) he rfl (by rw [h20, h19, h30, h31]; exact hd) (by simp [h22])
    (by simp [h23])) fun s' ta => ⟨(ta.env.fr _ (by decide)).trans h31, ta.env.sp⟩

end

/-- The invariant of the entry, from the public arguments of `σ`. -/
abbrev SCI (σ : State) (s : State) : Prop :=
  streamCryptPre s ∧ s.gpr .r3 = σ.gpr .r3 ∧ s.gpr .r4 = σ.gpr .r4 ∧ s.gpr .r5 = σ.gpr .r5 ∧
    s.gpr .r6 = σ.gpr .r6 ∧ s.gpr .r7 = σ.gpr .r7 ∧ s.gpr .r8 = σ.gpr .r8 ∧ s.gpr .r9 = σ.gpr .r9 ∧
    s.gpr .r10 = σ.gpr .r10 ∧ s.sp = σ.sp

theorem sci_of {σ₁ σ₂ : State} (h₁ : streamCryptPre σ₁) (h₂ : streamCryptPre σ₂) (hq : streamCryptPub σ₁ σ₂) :
    SCI σ₁ σ₁ ∧ SCI σ₁ σ₂ := by
  obtain ⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp⟩ := hq
  exact ⟨⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨h₂, q3.symm, q4.symm, q5.symm, q6.symm, q7.symm, q8.symm, q9.symm, q10.symm, qsp.symm⟩⟩

theorem sci_DI {σ s : State} (h : SCI σ s) :
    WP isa (.block cryptEntry) s (DI (σ.gpr .r3) (σ.gpr .r5) (σ.gpr .r10) σ.sp (σ.gpr .r8)
      (σ.gpr .r4).toNat (σ.gpr .r9) (σ.gpr .r6) (σ.gpr .r7)) := by
  obtain ⟨hs, e3, e4, e5, e6, e7, e8, e9, e10, esp⟩ := h
  have := sc_DI hs
  rw [e3, e4, e5, e6, e7, e8, e9, e10, esp] at this
  exact this

theorem streamEncrypt_ct [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    ConstantTime isa streamEncryptPPC64LE.pre streamEncryptPPC64LE.pub streamEncrypt := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  have h₁' : streamCryptPre σ₁ := h₁
  have L := scLay h₁'
  obtain ⟨i₁, i₂⟩ := sci_of h₁' h₂ hq
  refine ⟨SCI σ₁, i₁, i₂, ?_⟩
  refine CT.seq (J := CI (σ₁.gpr .r3) (σ₁.gpr .r5) (σ₁.gpr .r10) σ₁.sp (σ₁.gpr .r8) (σ₁.gpr .r4).toNat
    (σ₁.gpr .r9) (σ₁.gpr .r6) (σ₁.gpr .r7)) ?_
    (fun s h => WP.block_append (WP.mono (sci_DI h) fun _ h' => di_textArgs h')) ?_
  · obtain ⟨_, hc⟩ := cryptEntryArgs_taint
    exact CT.taintEq _ σ₁.gpr σ₁.sp (fun s ⟨_, e3, e4, e5, e6, e7, e8, e9, e10, esp⟩ =>
      ⟨esp, by simp [e3, e4, e5, e6, e7, e8, e9, e10]⟩) hc
  refine CT.seq ((crypt_ct L).mono fun _ h => ci_cr h) (fun _ h => ci_crypt L h) ?_
  refine CT.seq (J := fun s => s.gpr .r31 = σ₁.gpr .r10 ∧ s.sp = σ₁.sp) (textAbsorb_ct L)
    (fun _ h => ta_textAbsorb L h) ?_
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => σ₁.gpr .r10) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

theorem streamDecrypt_ct [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    ConstantTime isa streamDecryptPPC64LE.pre streamDecryptPPC64LE.pub streamDecrypt := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  have h₁' : streamCryptPre σ₁ := h₁
  have L := scLay h₁'
  obtain ⟨i₁, i₂⟩ := sci_of h₁' h₂ hq
  refine ⟨SCI σ₁, i₁, i₂, ?_⟩
  refine CT.seq (J := DI (σ₁.gpr .r3) (σ₁.gpr .r5) (σ₁.gpr .r10) σ₁.sp (σ₁.gpr .r8) (σ₁.gpr .r4).toNat
    (σ₁.gpr .r9) (σ₁.gpr .r6) (σ₁.gpr .r7)) ?_ (fun s h => sci_DI h) ?_
  · obtain ⟨_, hc⟩ := cryptEntry_taint
    exact CT.taintEq _ σ₁.gpr σ₁.sp (fun s ⟨_, e3, e4, e5, e6, e7, e8, e9, e10, esp⟩ =>
      ⟨esp, by simp [e3, e4, e5, e6, e7, e8, e9, e10]⟩) hc
  refine CT.seq ((textAbsorb_ct L).mono fun _ h => di_ta h) (fun _ h => di_textAbsorb L h) ?_
  refine CT.seq ?_ (fun _ h => di_textArgs h) ?_
  · obtain ⟨_, hc⟩ := textArgs_taint
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, a20, a19, _, a23, _, _, e₁, _⟩
      ⟨_, _, _, _, b20, b19, _, b23, _, _, e₂, _⟩ => ⟨e₁.sp.trans e₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [e₁.fr _ (by decide), e₂.fr _ (by decide), a19, b19]
    · rw [e₁.fr _ (by decide), e₂.fr _ (by decide), a20, b20]
    · rw [e₁.fr _ (by decide), e₂.fr _ (by decide), a23, b23]
  refine CT.seq ((crypt_ct L).mono fun _ h => ci_cr h) (fun _ h => ci_crypt L h) ?_
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => σ₁.gpr .r10) σ₁.sp (fun s h => ⟨(ta_exit h).2, by simp [(ta_exit h).1]⟩) hc

end VG.Proof.AesGcm.PPC64LE

end

end

/-! ### `AesGcm.PPC64LE.Verified`, which only this module used -/

section

/-!
# AES-GCM on PPC64LE: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time,
a state satisfying each precondition, and the shared contracts of
`Spec/Gcm/Contract.lean` with the working space as a last argument
(`Proof/AesGcm/Scratch.lean`; with no stack: a call keeps the return address
in the link register, which each function saves in the working space).
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE

theorem init_correct (s : State) (hs : initPPC64LE.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initPPC64LE.post s s' :=
  init_wp hs

theorem streamInit_correct [VG.Proof.Gcm.PPC64LE.GhashLaw] (s : State) (hs : streamInitPPC64LE.pre s) :
    ∃ t s', Exec isa streamInit s t s' ∧ abiPreserved s s' ∧ streamInitPPC64LE.post s s' :=
  streamInit_wp hs

theorem streamAad_correct [VG.Proof.Gcm.PPC64LE.GhashLaw] (s : State) (hs : streamAadPPC64LE.pre s) :
    ∃ t s', Exec isa streamAad s t s' ∧ abiPreserved s s' ∧ streamAadPPC64LE.post s s' :=
  streamAad_wp hs

theorem streamEncrypt_correct [VG.Proof.Gcm.PPC64LE.GhashLaw] (s : State) (hs : streamEncryptPPC64LE.pre s) :
    ∃ t s', Exec isa streamEncrypt s t s' ∧ abiPreserved s s' ∧ streamEncryptPPC64LE.post s s' :=
  streamEncrypt_wp hs

theorem streamDecrypt_correct [VG.Proof.Gcm.PPC64LE.GhashLaw] (s : State) (hs : streamDecryptPPC64LE.pre s) :
    ∃ t s', Exec isa streamDecrypt s t s' ∧ abiPreserved s s' ∧ streamDecryptPPC64LE.post s s' :=
  streamDecrypt_wp hs

theorem streamFinish_correct [VG.Proof.Gcm.PPC64LE.GhashLaw] (s : State) (hs : streamFinishPPC64LE.pre s) :
    ∃ t s', Exec isa streamFinish s t s' ∧ abiPreserved s s' ∧ streamFinishPPC64LE.post s s' :=
  streamFinish_wp hs

theorem streamVerify_correct [VG.Proof.Gcm.PPC64LE.GhashLaw] (s : State) (hs : streamVerifyPPC64LE.pre s) :
    ∃ t s', Exec isa streamVerify s t s' ∧ abiPreserved s s' ∧ streamVerifyPPC64LE.post s s' :=
  streamVerify_wp hs

theorem sealFused_correct [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    (s : State) (hs : sealPPC64LE.pre s) :
    ∃ t s', Exec isa Impl.AesGcm.PPC64LE.SealFused.seal s t s' ∧
      abiPreserved s s' ∧ sealPPC64LE.post s s' :=
  sealFused_wp hs

theorem open_correct [VG.Proof.Gcm.PPC64LE.GhashLaw] (s : State) (hs : openPPC64LE.pre s) :
    ∃ t s', Exec isa «open» s t s' ∧ abiPreserved s s' ∧ openPPC64LE.post s s' :=
  open_wp hs

/-! ## States satisfying the preconditions (with empty buffers) -/

def initSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 16 | .r5 => 0x2000 | .r6 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 256⟩, ⟨0x4000, 2560⟩]

def streamInitSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r6 => 0x3000 | .r7 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩]

def streamAadSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x3000 | .r6 => 0x2000 | .r8 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩]

def streamCryptSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 10 | .r5 => 0x3000 | .r8 => 0x2000 | .r10 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩, ⟨0x4000, 2560⟩]

def finSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 10 | .r5 => 0x3000 | .r8 => 0x5000 | .r9 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩, ⟨0x4000, 2560⟩]

def verSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 10 | .r5 => 0x3000 | .r8 => 0x5000 | .r10 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x5000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩]

/-! ## The shared contracts -/

theorem init_verified :
    Verified PPC64LE.target init (Proof.AesGcm.initScratchContract PPC64LE.abi) :=
  Verified.of_correct init_correct init_ct (by
    sig_implies [Proof.AesGcm.initScratchContract, Proof.AesGcm.initScratchSig, Spec.Gcm.initPre,
      Spec.Gcm.initPost, initPPC64LE, PPC64LE.abi, PPC64LE.argRegs] [initSat] using initSat)

theorem streamInit_verified [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target streamInit (Proof.AesGcm.streamInitScratchContract PPC64LE.abi) :=
  Verified.of_correct streamInit_correct streamInit_ct (by
    sig_implies [Proof.AesGcm.streamInitScratchContract, Proof.AesGcm.streamInitScratchSig,
      Spec.Gcm.streamInitPost, streamInitPPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      [streamInitSat] using streamInitSat)

theorem streamAad_verified [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target streamAad (Proof.AesGcm.streamAadScratchContract PPC64LE.abi) :=
  Verified.of_correct streamAad_correct streamAad_ct (by
    sig_implies [Proof.AesGcm.streamAadScratchContract, Proof.AesGcm.streamAadScratchSig,
      Spec.Gcm.streamAadPost, streamAadPPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      [streamAadSat] using streamAadSat)

theorem streamEncrypt_verified [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target streamEncrypt (Proof.AesGcm.streamEncryptScratchContract PPC64LE.abi) :=
  Verified.of_correct streamEncrypt_correct streamEncrypt_ct (by
    sig_implies [Proof.AesGcm.streamEncryptScratchContract, Proof.AesGcm.streamCryptScratchSig,
      Spec.Gcm.streamTextPre, Proof.AesGcm.streamEncryptRoundsPost, streamEncryptPPC64LE, streamCryptPre,
      streamCryptPub, rounds, PPC64LE.abi, PPC64LE.argRegs] [streamCryptSat] using streamCryptSat)

theorem streamDecrypt_verified [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target streamDecrypt (Proof.AesGcm.streamDecryptScratchContract PPC64LE.abi) :=
  Verified.of_correct streamDecrypt_correct streamDecrypt_ct (by
    sig_implies [Proof.AesGcm.streamDecryptScratchContract, Proof.AesGcm.streamCryptScratchSig,
      Spec.Gcm.streamTextPre, Proof.AesGcm.streamDecryptRoundsPost, streamDecryptPPC64LE, streamCryptPre,
      streamCryptPub, rounds, PPC64LE.abi, PPC64LE.argRegs] [streamCryptSat] using streamCryptSat)

theorem streamFinish_verified [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target streamFinish (Proof.AesGcm.streamFinishScratchContract PPC64LE.abi) :=
  Verified.of_correct streamFinish_correct streamFinish_ct (by
    sig_implies [Proof.AesGcm.streamFinishScratchContract, Proof.AesGcm.streamFinishScratchSig,
      Spec.Gcm.streamFinishPre, Proof.AesGcm.streamFinishRoundsPost, streamFinishPPC64LE, finPre, rounds, PPC64LE.abi,
      PPC64LE.argRegs] [finSat] using finSat)

theorem streamVerify_verified [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target streamVerify (Proof.AesGcm.streamVerifyScratchContract PPC64LE.abi) :=
  Verified.of_correct streamVerify_correct streamVerify_ct (by
    sig_implies [Proof.AesGcm.streamVerifyScratchContract, Proof.AesGcm.streamVerifyScratchSig,
      Spec.Gcm.streamVerifyPre, Proof.AesGcm.streamVerifyRoundsPost, streamVerifyPPC64LE, verPre, rounds, PPC64LE.abi,
      PPC64LE.argRegs] [verSat] using verSat)

/-- `tag` at `0x5000` and the working space at `0x6000`, the stack arguments. -/
def sealSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 10 | .r5 => 0x2000 | .r7 => 0x3000 | .r9 => 0x4000 | _ => 0
  lr := 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9061 then 0x50 else bif Nat.beq a.toNat 0x9069 then 0x60 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x9060, 16⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x5000, 16⟩, ⟨0x6000, 2560⟩]

theorem sealFused_verified [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] :
    Verified PPC64LE.target Impl.AesGcm.PPC64LE.SealFused.seal
      (Proof.AesGcm.sealScratchContract PPC64LE.abi) :=
  Verified.of_correct sealFused_correct sealFused_ct (by
    sig_implies [Proof.AesGcm.sealScratchContract, Proof.AesGcm.sealScratchSig, Spec.Gcm.sealPre,
      Proof.AesGcm.sealRoundsPost, sealPPC64LE, sealPre, onePub, args, rounds, PPC64LE.abi, PPC64LE.argRegs,
      stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
      [sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealSat)

/-- `tag` at `0x5000`, `tag_len` 0 and the working space at `0x6000`, the stack arguments. -/
def openSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 10 | .r5 => 0x2000 | .r7 => 0x3000 | .r9 => 0x4000 | _ => 0
  lr := 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9061 then 0x50 else bif Nat.beq a.toNat 0x9071 then 0x60 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x5000, 0⟩, ⟨0x9060, 24⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x6000, 2560⟩]

/-- The leak `open` may have: whether it succeeds. -/
theorem leak_bool {a b : Bool} (h : [if a = true then 1 else 0] = [if b = true then 1 else 0]) : a = b := by
  cases a <;> cases b <;> simp_all

/-- The postconditions match on `openResult`; the result is the low 32 bits
of `r3`; and `open`'s public data include its leak, whether it succeeds (for
`rounds` of 10, 12 or 14). -/
theorem open_verified [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target «open» (Proof.AesGcm.openScratchContract PPC64LE.abi) :=
  Verified.of_correct open_correct open_ct
    { pre := by
        sig_implies_pre [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPre,
          openPPC64LE, openPre, onePub, args, rounds, PPC64LE.abi, PPC64LE.argRegs,
          stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
      post := by
        intro s s' _ h
        sig_eval [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Proof.AesGcm.openRoundsPost, PPC64LE.abi,
          PPC64LE.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
        simp only [openPPC64LE] at h
        intro _
        exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openLeak, openPPC64LE,
          openPre, onePub, args, rounds, PPC64LE.abi, PPC64LE.argRegs, stackArg, stackArgAddr, List.getD,
          List.range, List.range.loop] at h
        obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2⟩ := h
        refine ⟨⟨h3, h4, h5, h6, h7, h8, h9, h10, hsp, fun i hi => ?_⟩, fun hr => leak_bool ?_⟩
        · rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega_using [hi]) with rfl | rfl | rfl
          · exact a0
          · exact a1
          · exact a2
        · have e₁ : ¬((s₁.gpr .r4).toNat = 10 ∨ (s₁.gpr .r4).toNat = 12 ∨ (s₁.gpr .r4).toNat = 14) ↔ False :=
            ⟨fun x => x hr, False.elim⟩
          have e₂ : ¬((s₂.gpr .r4).toNat = 10 ∨ (s₂.gpr .r4).toNat = 12 ∨ (s₂.gpr .r4).toNat = 14) ↔ False :=
            ⟨fun x => x (h4 ▸ hr), False.elim⟩
          simp only [e₁, e₂, ↓reduceIte] at hl
          exact hl
      sat := by
        sig_implies_sat [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPre,
          openPPC64LE, openPre, onePub, args, rounds, PPC64LE.abi, PPC64LE.argRegs,
          stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
          [openSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openSat }

end VG.Proof.AesGcm.PPC64LE

end

end


/-!
# AES-GCM on PPC64LE, with its working space on the stack

Each function runs its code, proved with the working space as an argument
(`Verified.lean`), in a frame of 2592 bytes that allocates it
(`Verified.stackScratch`): its arguments all arrive in registers, the
working space in the next one.
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE

/-- A state satisfying `vg_aes_gcm_init`'s precondition, without the working
space. -/
def initFrameSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 16 | .r5 => 0x2000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 256⟩]

theorem initFrameSat_pre : ∃ s, (Spec.Gcm.initContract PPC64LE.abi 2592).pre s := by
  implies_sat [Spec.Gcm.initContract, Spec.Gcm.initSig, Spec.Gcm.initPre, Spec.Gcm.initPost,
    PPC64LE.abi, PPC64LE.argRegs] [initFrameSat] using initFrameSat

theorem init_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2592 .r6 init)
      (Spec.Gcm.initContract PPC64LE.abi 2592) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Gcm.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Gcm.initPre PPC64LE.abi.ptrBits) (post := Spec.Gcm.initPost PPC64LE.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2592) init_verified (by decide) (by decide)
    (Proof.AesGcm.initPre_local _) (Proof.AesGcm.initPost_local _)
    (Proof.AesGcm.initPostOut_local _) initFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_init`'s precondition, without the
working space. -/
def streamInitFrameSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r6 => 0x3000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 80⟩]

theorem streamInitFrameSat_pre : ∃ s, (Spec.Gcm.streamInitContract PPC64LE.abi 2592).pre s := by
  implies_sat [Spec.Gcm.streamInitContract, Spec.Gcm.streamInitSig, Spec.Gcm.streamInitPost,
    PPC64LE.abi, PPC64LE.argRegs] [streamInitFrameSat] using streamInitFrameSat

theorem streamInit_framed [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2592 .r7 streamInit)
      (Spec.Gcm.streamInitContract PPC64LE.abi 2592) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Gcm.streamInitSig) (nm := "scratch") (e := .u64)
    (n := 320) (post := Spec.Gcm.streamInitPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 2592) streamInit_verified (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.AesGcm.streamInitPost_local _)
    (fun vs m m₁ m₂ r hl _ => Proof.AesGcm.streamInitPostOut_local _ vs m m₁ m₂ r hl)
    streamInitFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_aad`'s precondition, without the
working space. -/
def streamAadFrameSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x3000 | .r6 => 0x2000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 80⟩]

theorem streamAadFrameSat_pre : ∃ s, (Spec.Gcm.streamAadContract PPC64LE.abi 2592).pre s := by
  implies_sat [Spec.Gcm.streamAadContract, Spec.Gcm.streamAadSig, Spec.Gcm.streamAadPost,
    PPC64LE.abi, PPC64LE.argRegs] [streamAadFrameSat] using streamAadFrameSat

theorem streamAad_framed [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2592 .r8 streamAad)
      (Spec.Gcm.streamAadContract PPC64LE.abi 2592) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Gcm.streamAadSig) (nm := "scratch") (e := .u64)
    (n := 320) (post := Spec.Gcm.streamAadPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 2592) streamAad_verified (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.AesGcm.streamAadPost_local _)
    (fun vs m m₁ m₂ r hl _ => Proof.AesGcm.streamAadPostOut_local _ vs m m₁ m₂ r hl)
    streamAadFrameSat_pre

/-- A state satisfying the preconditions of `vg_aes_gcm_stream_encrypt` and
`vg_aes_gcm_stream_decrypt`, without the working space. -/
def streamCryptFrameSat : State := { streamCryptSat with wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩] }

theorem streamEncryptFrameSat_pre : ∃ s, (Proof.AesGcm.streamEncryptRoundsContract PPC64LE.abi 2592).pre s := by
  implies_sat [Proof.AesGcm.streamEncryptRoundsContract, Spec.Gcm.streamCryptSig, Spec.Gcm.streamTextPre,
    Proof.AesGcm.streamEncryptRoundsPost, PPC64LE.abi, PPC64LE.argRegs] [streamCryptFrameSat, streamCryptSat]
    using streamCryptFrameSat

theorem streamEncrypt_framed [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2592 .r10 streamEncrypt)
      (Proof.AesGcm.streamEncryptRoundsContract PPC64LE.abi 2592) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamTextPre PPC64LE.abi.ptrBits)
    (post := Proof.AesGcm.streamEncryptRoundsPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 2592) streamEncrypt_verified (by decide) (by decide)
    (Proof.AesGcm.streamTextPre_local _) (Proof.AesGcm.streamEncryptPost_local _)
    (fun vs m m₁ m₂ r hl _ => Proof.AesGcm.streamEncryptPostOut_local _ vs m m₁ m₂ r hl) streamEncryptFrameSat_pre

theorem streamDecryptFrameSat_pre : ∃ s, (Proof.AesGcm.streamDecryptRoundsContract PPC64LE.abi 2592).pre s := by
  implies_sat [Proof.AesGcm.streamDecryptRoundsContract, Spec.Gcm.streamCryptSig, Spec.Gcm.streamTextPre,
    Proof.AesGcm.streamDecryptRoundsPost, PPC64LE.abi, PPC64LE.argRegs] [streamCryptFrameSat, streamCryptSat]
    using streamCryptFrameSat

theorem streamDecrypt_framed [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2592 .r10 streamDecrypt)
      (Proof.AesGcm.streamDecryptRoundsContract PPC64LE.abi 2592) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamTextPre PPC64LE.abi.ptrBits)
    (post := Proof.AesGcm.streamDecryptRoundsPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 2592) streamDecrypt_verified (by decide) (by decide)
    (Proof.AesGcm.streamTextPre_local _) (Proof.AesGcm.streamDecryptPost_local _)
    (fun vs m m₁ m₂ r hl _ => Proof.AesGcm.streamDecryptPostOut_local _ vs m m₁ m₂ r hl) streamDecryptFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_finish`'s precondition, without
the working space. -/
def finFrameSat : State := { finSat with wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩] }

theorem finFrameSat_pre : ∃ s, (Proof.AesGcm.streamFinishRoundsContract PPC64LE.abi 2592).pre s := by
  implies_sat [Proof.AesGcm.streamFinishRoundsContract, Spec.Gcm.streamFinishSig, Spec.Gcm.streamFinishPre,
    Proof.AesGcm.streamFinishRoundsPost, PPC64LE.abi, PPC64LE.argRegs] [finFrameSat, finSat] using finFrameSat

theorem streamFinish_framed [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2592 .r9 streamFinish)
      (Proof.AesGcm.streamFinishRoundsContract PPC64LE.abi 2592) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Gcm.streamFinishSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamFinishPre PPC64LE.abi.ptrBits)
    (post := Proof.AesGcm.streamFinishRoundsPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 2592) streamFinish_verified (by decide) (by decide)
    (Proof.AesGcm.streamFinishPre_local _) (Proof.AesGcm.streamFinishPost_local _)
    (fun vs m m₁ m₂ r hl _ => Proof.AesGcm.streamFinishPostOut_local _ vs m m₁ m₂ r hl) finFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_verify`'s precondition, without
the working space. -/
def verFrameSat : State := { verSat with wr := [⟨0x3000, 80⟩] }

theorem verFrameSat_pre : ∃ s, (Proof.AesGcm.streamVerifyRoundsContract PPC64LE.abi 2592).pre s := by
  implies_sat [Proof.AesGcm.streamVerifyRoundsContract, Spec.Gcm.streamVerifySig, Spec.Gcm.streamVerifyPre,
    Proof.AesGcm.streamVerifyRoundsPost, PPC64LE.abi, PPC64LE.argRegs] [verFrameSat, verSat] using verFrameSat

theorem streamVerify_framed [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2592 .r10 streamVerify)
      (Proof.AesGcm.streamVerifyRoundsContract PPC64LE.abi 2592) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Gcm.streamVerifySig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamVerifyPre PPC64LE.abi.ptrBits)
    (post := Proof.AesGcm.streamVerifyRoundsPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 2592) streamVerify_verified (by decide) (by decide)
    (Proof.AesGcm.streamVerifyPre_local _) (Proof.AesGcm.streamVerifyPost_local _)
    (fun vs m m₁ m₂ r hl _ => Proof.AesGcm.streamVerifyPostOut_local _ vs m m₁ m₂ r hl) verFrameSat_pre

/-- A state satisfying `vg_aes_gcm_seal`'s precondition, without the working
space: `tag` alone on the stack. -/
def sealFrameSat : State where
  gpr := sealSat.gpr
  lr := 0
  sp := 0x9000
  mem := sealSat.mem
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x9060, 8⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x5000, 16⟩]

theorem sealFrameSat_pre : ∃ s, (Proof.AesGcm.sealRoundsContract PPC64LE.abi 2672).pre s := by
  implies_sat [Proof.AesGcm.sealRoundsContract, Spec.Gcm.sealSig, Spec.Gcm.sealPre, Proof.AesGcm.sealRoundsPost, PPC64LE.abi,
    PPC64LE.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
    [sealFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealFrameSat

/-- `seal`, whose `tag` arrives on the stack: the frame copies it, then the
working space's address, above its stack pointer (`Verified.stackScratchArgs`). -/
theorem seal_framed [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchArgs 2672 1 Impl.AesGcm.PPC64LE.SealFused.seal)
      (Proof.AesGcm.sealRoundsContract PPC64LE.abi 2672) :=
  PPC64LE.Verified.stackScratchArgs (sig := Spec.Gcm.sealSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Gcm.sealPre PPC64LE.abi.ptrBits) (post := Proof.AesGcm.sealRoundsPost PPC64LE.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2672) (m := 1) sealFused_verified (by decide) (by decide)
    (Proof.AesGcm.sealPre_local _) (Proof.AesGcm.sealPost_local _)
    (fun vs m m₁ m₂ r hl _ => Proof.AesGcm.sealPostOut_local _ vs m m₁ m₂ r hl) sealFrameSat_pre

/-- A state satisfying `vg_aes_gcm_open`'s precondition, without the working
space: `tag` and `tag_len` alone on the stack. -/
def openFrameSat : State where
  gpr := openSat.gpr
  lr := 0
  sp := 0x9000
  mem := openSat.mem
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x5000, 0⟩, ⟨0x9060, 16⟩]
  wr := [⟨0x4000, 0⟩]

theorem openFrameSat_pre : ∃ s, (Proof.AesGcm.openRoundsContract PPC64LE.abi 2688).pre s := by
  implies_sat [Proof.AesGcm.openRoundsContract, Spec.Gcm.openSig, Spec.Gcm.openPre, Proof.AesGcm.openRoundsPost, Spec.Gcm.openLeak,
    PPC64LE.abi, PPC64LE.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
    [openFrameSat, openSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openFrameSat

/-- `open`, whose `tag` and `tag_len` arrive on the stack, as `seal`'s `tag` does. -/
theorem open_framed [VG.Proof.Gcm.PPC64LE.GhashLaw] :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchArgs 2688 2 «open»)
      (Proof.AesGcm.openRoundsContract PPC64LE.abi 2688) :=
  PPC64LE.Verified.stackScratchArgs (sig := Spec.Gcm.openSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Gcm.openPre PPC64LE.abi.ptrBits) (post := Proof.AesGcm.openRoundsPost PPC64LE.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2688) (m := 2) (leak := some (Spec.Gcm.openLeak PPC64LE.abi.ptrBits))
    open_verified (by decide) (by decide) (Proof.AesGcm.openPre_local _) (Proof.AesGcm.openPost_local _)
    (fun vs m m₁ m₂ r hl _ => Proof.AesGcm.openPostOut_local _ vs m m₁ m₂ r hl)
    openFrameSat_pre (hleak := Proof.AesGcm.openLeak_local _)

end VG.Proof.AesGcm.PPC64LE
