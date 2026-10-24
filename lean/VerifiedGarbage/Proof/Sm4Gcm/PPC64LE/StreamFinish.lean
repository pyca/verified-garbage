module

public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Contract
public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.FinTag
import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.StreamCrypt
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Fn
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamInit
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamFinish
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Sm4Gcm.PPC64LE
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Env
public import VerifiedGarbage.Proof.Sm4Gcm.PPC64LE.Crypt
public import VerifiedGarbage.Spec.Gcm
public import VerifiedGarbage.Spec.Sm4.Gcm.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# SM4-GCM on PPC64LE: `vg_sm4_gcm_stream_finish`

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/PPC64LE/StreamFinish.lean`), with SM4's tag: the entry saves our caller's
registers and keeps the arguments in `r20`–`r30` (`fin1_wp`); `finTag 0`
puts the tag into `W` (`fin_tag`, `fin_out`), and `tagOut` copies it to
`tag` (`streamFinish_wp`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4Gcm.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov tagOut)
open VG.Proof.AesGcm.PPC64LE (Env Lay Perm Entered SavedAt savedR save_ok restore_ok covers_mem
  covers_prefix covers_off bytesAt_frame blockAt_frame ctx_saved ctxH_keep saved_w toNat_mod16 WP.forall_det
  WP.with_rdwr Lay.saved_st tagOut_ok lensBlock_mod toNat_of_eq)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ghashInput fullTag)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Proof.Gcm (Absorbed)

section
variable {s₀ : State} (h : finPre s₀)
include h

theorem finLay : Lay (s₀.gpr .r3) (s₀.gpr .r4) (s₀.gpr .r8) := by
  obtain ⟨-, -, dcs, -, dcw, -, dsw, -, fc, fs, -, fw, -⟩ := h
  have fw' : (s₀.gpr .r8).toNat + 2560 ≤ 2 ^ 64 := fw
  exact Lay.of fc fs (by omega) dcs (dcw.sub_right (Region.sub_prefix (by decide)))
    (dsw.sub_right (Region.sub_prefix (by decide)))

theorem finX : XOk (s₀.gpr .r3) (s₀.gpr .r4) (s₀.gpr .r8) (s₀.gpr .r9) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, dcx, dsx, -, dwx, fx⟩ := h
  exact ⟨fx, dcx, dsx, dwx⟩

theorem fin_W' : Covers [⟨s₀.gpr .r8, scrBytes⟩] s₀.wr := by
  rw [h.2.1]; exact covers_mem (by simp)

theorem fin_W : Covers [⟨s₀.gpr .r8, 2560⟩] s₀.wr := covers_prefix (fin_W' h) (by decide)

theorem fin_X : Covers [xR (s₀.gpr .r9)] s₀.wr := by
  rw [h.2.1]; exact covers_mem (by simp)

end

/-- After the entry of `finish`, from `s₀`. -/
structure SF1 (s₀ s₁ : State) : Prop where
  en : Entered s₀ (s₀.gpr .r8) s₁
  r31 : s₁.gpr .r31 = s₀.gpr .r8
  r30 : s₁.gpr .r30 = s₀.gpr .r4
  r29 : s₁.gpr .r29 = s₀.gpr .r3
  r22 : s₁.gpr .r22 = s₀.gpr .r5
  r23 : s₁.gpr .r23 = s₀.gpr .r6
  r20 : s₁.gpr .r20 = s₀.gpr .r7
  r28 : s₁.gpr .r28 = s₀.gpr .r9

theorem fin1_wp {s₀ : State} (hW : Covers [⟨s₀.gpr .r8, 2560⟩] s₀.wr) :
    WP isa (.block finEntry) s₀ (SF1 s₀) := by
  refine WP.block_append (WP.mono (save_ok (b := .r8) (by decide) hW) fun s₁ ⟨hg, h31, hk, hsv, hf⟩ => ?_)
  have e3 : s₁.gpr .r3 = s₀.gpr .r3 := hg _ (by decide) (by decide)
  have e4 : s₁.gpr .r4 = s₀.gpr .r4 := hg _ (by decide) (by decide)
  have e5 : s₁.gpr .r5 = s₀.gpr .r5 := hg _ (by decide) (by decide)
  have e6 : s₁.gpr .r6 = s₀.gpr .r6 := hg _ (by decide) (by decide)
  have e7 : s₁.gpr .r7 = s₀.gpr .r7 := hg _ (by decide) (by decide)
  have e9 : s₁.gpr .r9 = s₀.gpr .r9 := hg _ (by decide) (by decide)
  crun [mov, BitVec.or_self, e3, e4, e5, e6, e7, e9, h31]
  refine ⟨⟨fun r hr => by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [hg],
    ⟨hk.rd, hk.wr, hk.sp, hk.lr⟩, hsv, hf⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [h31]

/-- The environment after the entry. -/
theorem fin_env {s₀ s₁ : State} (h : finPre s₀) (h1 : SF1 s₀ s₁) : Env s₁.gpr s₀.sp s₁ := by
  obtain ⟨hrd, hwr, -⟩ := h
  have perm : Perm (s₀.gpr .r3) (s₀.gpr .r4) (s₀.gpr .r8) s₁ :=
    (⟨covers_mem (by rw [hrd]; simp), covers_mem (by rw [hwr]; simp),
      covers_prefix (covers_mem (r := ⟨s₀.gpr .r8, scrBytes⟩) (by rw [hwr]; simp)) (by decide)⟩ :
      Perm (s₀.gpr .r3) (s₀.gpr .r4) (s₀.gpr .r8) s₀).of_eq h1.en.keeps.rd h1.en.keeps.wr
  exact ⟨fun _ _ => rfl, h1.en.keeps.sp, by rw [h1.r29, h1.r30, h1.r31]; exact perm⟩

section
variable {c st w x : Addr} (L : Lay c st w) (X : XOk c st w x)
include L X

theorem saved_tagFrame {o : Nat} (ho : o = 0 ∨ o = 112) : ∀ r ∈ tagFrame st w x o, (savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using L.saved_st (d := 0) (k := 32) (by decide)
  · exact saved_w (by decide) (.inl (by decide))
  · exact saved_w (by omega) (.inl (by omega))
  · exact saved_w (by decide) (.inr (by decide))
  · exact X.wx.sub_left (Lay.wSub (by decide))

end

/-- The tag, for a state that represents `a` and `ct`, from a memory `m₀`
that differs from the entry's only apart from the context and the state. -/
theorem fin_out {s₀ s : State} {m₀ : Mem} {rs : List Region} (hf₀ : Frame rs s₀.mem m₀)
    (hdc : ∀ r ∈ rs, (⟨s₀.gpr .r3, 256⟩ : Region).Disjoint r)
    (hds : ∀ r ∈ rs, (⟨s₀.gpr .r4, 80⟩ : Region).Disjoint r)
    {V : Reg → BitVec 64} {sp : Addr} (h29 : V .r29 = s₀.gpr .r3) (h30 : V .r30 = s₀.gpr .r4)
    (h22 : V .r22 = s₀.gpr .r5) {o : Nat} {iv a ct : List Byte}
    (hf : FinOut V sp o (ctxH s₀.mem (s₀.gpr .r3)) a ct m₀ s)
    (hs : StreamRepr s₀.mem (s₀.gpr .r4) (ctxCiph s₀.mem (s₀.gpr .r3))
      (ctxH s₀.mem (s₀.gpr .r3)) iv a ct) (hl : s₀.gpr .r5 = BitVec.ofNat 64 a.length) :
    bytesAt s.mem (V .r31 + BitVec.ofNat 64 o) 16 =
      fullTag (ctxCiph s₀.mem (s₀.gpr .r3)) (ctxH s₀.mem (s₀.gpr .r3)) iv a ct := by
  rw [Proof.Gcm.streamRepr_iff] at hs
  obtain ⟨hj, hab, -⟩ := hs
  have hb := Nat.mod_lt (ghashInput a ct).length (show 16 > 0 by decide)
  have dS : ∀ {d k : Nat}, d + k ≤ 80 → ∀ r ∈ rs, (⟨s₀.gpr .r4 + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r :=
    fun hd r hr => (hds r hr).sub_left (Lay.stSub hd)
  have hab₀ : Absorbed m₀ (V .r30 + BitVec.ofNat 64 16) (V .r30 + BitVec.ofNat 64 32)
      (ctxH s₀.mem (s₀.gpr .r3)) (ghashInput a ct) := by
    rw [h30]
    exact hab.congr (blockAt_frame hf₀ (dS (d := 16) (by decide)))
      (bytesAt_frame hf₀ (dS (d := 32) (k := (ghashInput a ct).length % 16) (by omega)) (by omega))
  rw [hf.out hab₀,
    h29, ciph_keep hf₀ hdc, h30,
    blockAt_frame hf₀ (by simpa using dS (d := 0) (k := 16) (by decide)), hj,
    h22, toNat_of_eq hl, lensBlock_mod, Proof.Gcm.fullTag_eq]

theorem streamFinish_wp {s₀ : State} (h : streamFinishPPC64LE.pre s₀) :
    WP isa streamFinish s₀ fun s' => abiPreserved s₀ s' ∧ streamFinishPPC64LE.post s₀ s' := by
  have h' : finPre s₀ := h
  have L₀ := finLay h'
  have X₀ := finX h'
  have hh := h'
  obtain ⟨-, hwr, -, -, -, -, -, dtw, -, -, -, -, -⟩ := hh
  have hTw : Covers [⟨s₀.gpr .r7, 16⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  have run : ∀ {a ct : List Byte}, a.length % 16 = (s₀.gpr .r5).toNat % 16 → (s₀.gpr .r6).toNat = ct.length →
      WP isa streamFinish s₀ fun s' => abiPreserved s₀ s' ∧ ∀ iv,
        StreamRepr s₀.mem (s₀.gpr .r4) (ctxCiph s₀.mem (s₀.gpr .r3))
          (ctxH s₀.mem (s₀.gpr .r3)) iv a ct → s₀.gpr .r5 = BitVec.ofNat 64 a.length →
        bytesAt s'.mem (s₀.gpr .r7) 16 =
          fullTag (ctxCiph s₀.mem (s₀.gpr .r3)) (ctxH s₀.mem (s₀.gpr .r3)) iv a ct := by
    intro a ct ha hP
    refine WP.seq (WP.mono (fin1_wp (fin_W h')) fun s₁ h1 => ?_)
    have he₁ := fin_env h' h1
    have L := L₀.v h1.r29 h1.r30 h1.r31
    have hH₁ : blockAt s₁.mem (s₁.gpr .r29 + BitVec.ofNat 64 240) = ctxH s₀.mem (s₀.gpr .r3) := by
      rw [h1.r29]; exact ctxH_keep h1.en.frame (ctx_saved L₀)
    have X : XOk (s₁.gpr .r29) (s₁.gpr .r30) (s₁.gpr .r31) (s₁.gpr .r28) := by rw [h1.r29, h1.r30, h1.r31, h1.r28]; exact X₀
    refine WP.seq (WP.mono (WP.with_rdwr (finTag_ok L X (o := 0) (.inl rfl) (a := a) (ct := ct) he₁
      (by rw [h1.r28, h1.en.keeps.wr]; exact fin_X h') hH₁ (by rw [h1.r22]; exact ha)
      (by rw [h1.r23]; exact hP))) fun s₂ ⟨hf, rd₂, wr₂, _⟩ => ?_)
    have hTw₂ : Covers [⟨s₁.gpr .r20, 16⟩] s₂.wr := by
      rw [wr₂, h1.en.keeps.wr, h1.r20]; exact hTw
    have hTd : (⟨s₁.gpr .r20, 16⟩ : Region).Disjoint ⟨s₁.gpr .r31, 16⟩ := by
      rw [h1.r20, h1.r31]; exact dtw.sub_right (Region.sub_prefix (by decide))
    refine WP.seq (WP.mono (tagOut_ok hf.env hTw₂ hTd) fun s₃ ⟨hb₃, hf₃, g₃, hk₃⟩ => ?_)
    have he₃ := hf.env.keep (fun r hr => g₃ r (by revert r; decide)) hk₃.sp hk₃.rd hk₃.wr
    have sv₂ : SavedAt s₂.mem (s₀.gpr .r8) s₀ := by
      have := hf.frame; rw [h1.r30, h1.r31, h1.r28] at this
      exact h1.en.saved.frame this (saved_tagFrame L₀ X₀ (.inl rfl))
    have sv₃ : SavedAt s₃.mem (s₀.gpr .r8) s₀ := sv₂.frame hf₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h1.r20]
      exact (dtw.sub_right (VG.Offset.sub_base _ (show 128 + 120 ≤ scrBytes by decide))).symm)
    have e31 : s₃.gpr .r31 = s₀.gpr .r8 := (he₃.fr _ (by decide)).trans h1.r31
    refine WP.mono (restore_ok e31 (by have := he₃.perm.w; rw [h1.r31] at this; exact Covers.right this) sv₃
      he₃.sp (fun r hr => by rw [he₃.fr r (by revert hr; revert r; decide)]; exact h1.en.low r hr))
      fun s' ⟨ga, hm, _⟩ => ⟨ga, fun iv hs hl => ?_⟩
    have := fin_out (s := s₂) h1.en.frame (ctx_saved L₀) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simpa using (L₀.saved_st (d := 0) (k := 80) (by decide)).symm) h1.r29 h1.r30
      h1.r22 hf hs hl
    rw [BitVec.add_zero] at this
    rw [hm, ← h1.r20, hb₃, this]
  have h₀ := run (a := List.replicate ((s₀.gpr .r5).toNat % 16) 0) (ct := List.replicate (s₀.gpr .r6).toNat 0)
    (by simp) (by simp)
  refine WP.mono (WP.forall_det (WP.mono h₀ fun _ hh => hh.1)
    (P := fun i : List Byte × List Byte × List Byte =>
      StreamRepr s₀.mem (s₀.gpr .r4) (ctxCiph s₀.mem (s₀.gpr .r3))
          (ctxH s₀.mem (s₀.gpr .r3)) i.1 i.2.1 i.2.2 ∧
        s₀.gpr .r5 = BitVec.ofNat 64 i.2.1.length ∧ (s₀.gpr .r6).toNat = i.2.2.length)
    fun i hi => WP.mono (run (a := i.2.1) (ct := i.2.2) (by rw [hi.2.1, toNat_mod16]) hi.2.2)
      fun s' hh => hh.2 i.1 hi.1 hi.2.1)
    fun s' hh => ⟨hh.1, fun iv a c hs hl hp => hh.2 ⟨iv, a, c⟩ ⟨hs, hl, hp⟩⟩

end VG.Proof.Sm4Gcm.PPC64LE
