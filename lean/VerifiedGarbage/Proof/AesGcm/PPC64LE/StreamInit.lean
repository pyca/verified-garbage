module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contract
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Fn
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.Gcm.Ctr
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Offset

/-!
# AES-GCM on PPC64LE: `vg_aes_gcm_stream_init`

Untrusted: everything here is checked by Lean. The entry saves our caller's
registers and sets up `j0`'s arguments (`siEntry_ok`); `j0` writes `J₀`, a
zero accumulator and the first counter block, which is a state for the
nonce, no additional data and no text (`streamInit_wp`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom StreamRepr)

/-- After an entry that saved our caller's registers in `W`, from `s₀`. -/
structure Entered (s₀ : State) (W : Addr) (s : State) : Prop where
  low : ∀ r ∈ [Reg.r2, .r14, .r15, .r16, .r17], s.gpr r = s₀.gpr r
  keeps : Keeps' s₀ s
  saved : SavedAt s.mem W s₀
  frame : Frame [savedR W] s₀.mem s.mem

/-- The entry: `j0`'s arguments. -/
theorem siEntry_ok {s : State} (hW : Covers [⟨s.gpr .r7, 2560⟩] s.wr) :
    WP isa (.block streamInitPre) s fun s' => Entered s (s.gpr .r7) s' ∧
      s'.gpr .r31 = s.gpr .r7 ∧ s'.gpr .r30 = s.gpr .r6 ∧ s'.gpr .r29 = s.gpr .r3 ∧
      s'.gpr .r24 = s.gpr .r4 ∧ s'.gpr .r25 = s.gpr .r5 ∧ s'.gpr .r18 = s.gpr .r5 := by
  refine WP.block_append (WP.mono (save_ok (b := .r7) (by decide) hW) fun s₁ ⟨hg, h31, hk, hsv, hf⟩ => ?_)
  have e3 : s₁.gpr .r3 = s.gpr .r3 := hg _ (by decide) (by decide)
  have e4 : s₁.gpr .r4 = s.gpr .r4 := hg _ (by decide) (by decide)
  have e5 : s₁.gpr .r5 = s.gpr .r5 := hg _ (by decide) (by decide)
  have e6 : s₁.gpr .r6 = s.gpr .r6 := hg _ (by decide) (by decide)
  crun [mov, BitVec.or_self, e3, e4, e5, e6, h31]
  exact ⟨fun r hr => by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [hg],
    ⟨hk.rd, hk.wr, hk.sp, hk.lr⟩, hsv, hf⟩

/-- After the entry: `j0`'s precondition, for the nonce and the hash subkey on entry. -/
theorem si_entry {s : State} (hs : streamInitPPC64LE.pre s) :
    WP isa (.block streamInitPre) s fun s₁ => Entered s (s.gpr .r7) s₁ ∧ s₁.gpr .r29 = s.gpr .r3 ∧
      s₁.gpr .r30 = s.gpr .r6 ∧ s₁.gpr .r31 = s.gpr .r7 ∧
      J0In s₁.gpr s.sp (Spec.Gcm.ctxH s.mem (s.gpr .r3)) (s.gpr .r4) (s.gpr .r5).toNat s₁ ∧
      bytesAt s₁.mem (s.gpr .r4) (s.gpr .r5).toNat = bytesAt s.mem (s.gpr .r4) (s.gpr .r5).toNat := by
  simp only [streamInitPPC64LE] at hs
  obtain ⟨hrd, hwr, dcs, dcw, dns, dnw, dsw, wc, wn, ws, ww⟩ := hs
  generalize hCtx : s.gpr .r3 = Ctx at *
  generalize hNp : s.gpr .r4 = Np at *
  generalize hn : (s.gpr .r5).toNat = n at *
  generalize hSt : s.gpr .r6 = St at *
  generalize hW : s.gpr .r7 = W at *
  have hlt : n < 2 ^ 64 := hn ▸ (s.gpr .r5).isLt
  have hn' : s.gpr .r5 = BitVec.ofNat 64 n := by rw [← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hWc : Covers [⟨W, 2560⟩] s.wr := by rw [hwr]; exact covers_mem (by simp)
  refine WP.mono (siEntry_ok (by rw [hW]; exact hWc)) fun s₁ ⟨en, h31, h30, h29, h24, h25, h18⟩ => ?_
  rw [hW] at en h31
  rw [hSt] at h30
  rw [hCtx] at h29
  rw [hNp] at h24
  rw [hn'] at h25 h18
  have perm : Perm Ctx St W s₁ :=
    (⟨covers_mem (by rw [hrd, hwr]; simp), covers_mem (by rw [hwr]; simp), hWc⟩ : Perm Ctx St W s).of_eq
      en.keeps.rd en.keeps.wr
  have he : Env s₁.gpr s.sp s₁ := ⟨fun _ _ => rfl, en.keeps.sp, by rw [h29, h30, h31]; exact perm⟩
  have sW : Region.Sub (savedR W) ⟨W, 2560⟩ := Offset.sub_base _ (by decide)
  have hiv : bytesAt s₁.mem Np n = bytesAt s.mem Np n :=
    bytesAt_frame en.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dnw.sub_right sW) (by omega)
  have hH : blockAt s₁.mem (s₁.gpr .r29 + BitVec.ofNat 64 240) = Spec.Gcm.ctxH s.mem Ctx := by
    rw [h29, ctxH_eq]
    exact blockAt_frame en.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (dcw.sub_left (Offset.sub_base _ (by decide))).sub_right sW)
  refine ⟨en, h29, h30, h31, ⟨he, hH, h24, h25, h18, ?_⟩, hiv⟩
  rw [h30, h31]
  exact ⟨by rw [en.keeps.rd, en.keeps.wr, hrd]; exact covers_mem (by simp), hlt, wn, dns, dnw⟩

theorem streamInit_wp {s : State} (hs : streamInitPPC64LE.pre s) :
    WP isa streamInit s fun s' => abiPreserved s s' ∧ streamInitPPC64LE.post s s' := by
  have L₀ : Lay (s.gpr .r3) (s.gpr .r6) (s.gpr .r7) := by
    obtain ⟨-, -, dcs, dcw, -, -, dsw, wc, -, ws, ww⟩ := hs
    exact Lay.of wc ws ww dcs dcw dsw
  refine WP.seq (WP.mono (si_entry hs) fun s₁ ⟨en, h29, h30, h31, hJ, hiv⟩ => ?_)
  refine WP.seq (WP.mono (j0_ok (L₀.v h29 h30 h31) hJ) fun s₂ h₂ => ?_)
  have hsv : SavedAt s₂.mem (s.gpr .r7) s := by
    have := h₂.frame
    rw [h30, h31] at this
    exact en.saved.frame this (saved_j0Frame L₀)
  have e31 : s₂.gpr .r31 = s.gpr .r7 := (h₂.env.fr _ (by decide)).trans h31
  refine WP.mono (restore_ok e31 (by
      have := h₂.env.perm.w; rw [h31] at this; exact Covers.right this) hsv h₂.env.sp
    (fun r hr => by
      rw [h₂.env.fr r (by revert hr; revert r; decide)]; exact en.low r hr))
    fun s' ⟨ga, hm, _⟩ => ⟨ga, fun ciph => ?_⟩
  have hj := h₂.j0
  have hy := h₂.y
  have hcb := h₂.cb
  rw [h30, hiv] at hj hcb
  rw [h30] at hy
  rw [hm]
  exact Proof.Gcm.streamRepr_iff.mpr ⟨hj, Proof.Gcm.absorbed_nil _ hy, Proof.Gcm.ctr_zero _ _ _ _ hcb⟩

end VG.Proof.AesGcm.PPC64LE
