module

public import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contract
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Fn
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamInit
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.Gcm.Ctr
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.AesGcm.PPC64LE

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
      simp only [List.mem_singleton] at hr; subst hr; exact ddw.sub_right sW) (by omega)
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
        (by omega))
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
      fun e k he h => Offset.disjoint _ h (by omega) (by omega)
    rcases hr with rfl | rfl | rfl | rfl
    · exact (dsw.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by decide))
    · exact st_off 16 16 (by decide) (by omega)
    · exact st_off 32 16 (by decide) (by omega)
    · exact (dsw.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by decide))
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
