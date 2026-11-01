module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contract
public import VerifiedGarbage.Proof.AesGcm.RISCV64.FinTag
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Fn
public import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamInit
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
import VerifiedGarbage.Proof.Gcm.Be64
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.AesGcm.RISCV64

/-!
# AES-GCM on RISCV64: `vg_aes_gcm_stream_finish`

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcm/Arm/StreamFinish.lean`): the entry saves our caller's
registers and keeps the arguments in `s1`–`s3` and `s9`–`s11` (`fin1_wp`); `finTag 0`
puts the tag into `W` (`fin_tag`, `fin_out`), and `tagOut` copies it to
`tag` (`streamFinish_wp`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput fullTag)
open VG.Proof.Gcm (Absorbed)

theorem lensBlock_mod (L c : Nat) : Proof.Gcm.lensBlock (L % 2 ^ 64) c = Proof.Gcm.lensBlock L c := by
  simp only [Proof.Gcm.lensBlock]
  rw [← Proof.Gcm.be64_mod (8 * (L % 2 ^ 64)), ← Proof.Gcm.be64_mod (8 * L)]
  congr 2; omega

theorem toNat_of_eq {x : BitVec 64} {L : Nat} (h : x = BitVec.ofNat 64 L) : x.toNat = L % 2 ^ 64 := by
  rw [h, BitVec.toNat_ofNat]

/-- The tag at `W` copied to `tag` (`s9`). -/
theorem tagOut_ok {V : Reg → BitVec 64} {sp : Addr} {s : State} (he : Env V sp s)
    (hTw : Covers [⟨V .s9, 16⟩] s.wr) (hTd : (⟨V .s9, 16⟩ : Region).Disjoint ⟨V .s0, 16⟩) :
    WP isa (.block tagOut) s fun s' =>
      bytesAt s'.mem (V .s9) 16 = bytesAt s.mem (V .s0) 16 ∧ Frame [⟨V .s9, 16⟩] s.mem s'.mem ∧
        (∀ r, r ≠ .t0 → s'.gpr r = s.gpr r) ∧ Keeps' s s' := by
  have h20 := he.fr .s9 (by decide); have h31 := he.s0
  refine WP.mono (Bytes.copyBytes_ok (tmp := .t0) (src := .s0) (dst := .s9) (soff := 0) (doff := 0) (n := 16)
    (by decide) (by decide) (by decide) (by decide) (fun i hi => ?_) (fun i hi => ?_) (fun i hi hc => ?_))
    fun s' c => ⟨?_, ?_, c.gpr, ⟨c.rd, c.wr, c.sp⟩⟩
  · rw [h31, Nat.zero_add]; exact he.perm.wR (d := i) (n := 1) (by omega)
  · rw [h20, Nat.zero_add]; exact in_off hTw (d := i) (n := 1) (by omega) (by decide)
  · rw [h20, h31, Nat.zero_add, add_ofNat_zero] at hc
    exact hTd.symm _ (Offset.contains_base _ (by omega) (by omega)) hc
  · simp only [bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have := c.copied i (List.mem_range.mp hi)
    simp only [h20, h31, Nat.zero_add] at this; exact this
  · have := c.frame; rwa [h20, add_ofNat_zero] at this

section
variable {s₀ : State} (h : finPre s₀)
include h

theorem finLay : Lay (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a6) := by
  obtain ⟨-, -, dcs, -, dcw, -, dsw, -, fc, fs, -, fw, -, -, a0, a2, a6⟩ := h
  exact Lay.of fc fs fw dcs dcw dsw a0 a2 a6

theorem fin_R : (s₀.gpr .a1).toNat = 10 ∨ (s₀.gpr .a1).toNat = 12 ∨ (s₀.gpr .a1).toNat = 14 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hR, -⟩ := h
  exact hR

theorem fin_al : (s₀.gpr .a6).toNat % 8 = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, a6⟩ := h
  exact a6

theorem fin_stk : StkOk (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a6) s₀.sp := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hk, -⟩ := h
  exact hk.stk (by simp) (by simp) (by simp)

theorem fin_W : Covers [⟨s₀.gpr .a6, 2560⟩] s₀.wr := by
  rw [h.2.1]; exact covers_mem (by simp)

end

/-- After the entry of `finish`, from `s₀`. -/
structure SF1 (s₀ s₁ : State) : Prop where
  en : Entered s₀ (s₀.gpr .a6) s₁
  s0 : s₁.gpr .s0 = s₀.gpr .a6
  s1 : s₁.gpr .s1 = s₀.gpr .a2
  s2 : s₁.gpr .s2 = s₀.gpr .a0
  s3 : s₁.gpr .s3 = s₀.gpr .a1
  s10 : s₁.gpr .s10 = s₀.gpr .a3
  s11 : s₁.gpr .s11 = s₀.gpr .a4
  s9 : s₁.gpr .s9 = s₀.gpr .a5

theorem fin1_wp {s₀ : State} (hW : Covers [⟨s₀.gpr .a6, 2560⟩] s₀.wr) (hal : (s₀.gpr .a6).toNat % 8 = 0) :
    WP isa (.block finEntry) s₀ (SF1 s₀) := by
  refine WP.block_append (WP.mono (save_ok (b := .a6) hW hal) fun s₁ ⟨hg, h31, hk, hsv, hf⟩ => ?_)
  have e3 : s₁.gpr .a0 = s₀.gpr .a0 := hg _ (by decide)
  have e4 : s₁.gpr .a1 = s₀.gpr .a1 := hg _ (by decide)
  have e5 : s₁.gpr .a2 = s₀.gpr .a2 := hg _ (by decide)
  have e6 : s₁.gpr .a3 = s₀.gpr .a3 := hg _ (by decide)
  have e7 : s₁.gpr .a4 = s₀.gpr .a4 := hg _ (by decide)
  have e8 : s₁.gpr .a5 = s₀.gpr .a5 := hg _ (by decide)
  crun [Int.reduceNatCast', mov, e3, e4, e5, e6, e7, e8, h31]
  refine ⟨⟨⟨hk.rd, hk.wr, hk.sp⟩, hsv, hf⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [h31]

/-- The environment after the entry. -/
theorem fin_env {s₀ s₁ : State} (h : finPre s₀) (h1 : SF1 s₀ s₁) : Env s₁.gpr s₀.sp s₁ := by
  have hk := fin_stk h
  obtain ⟨hrd, hwr, -⟩ := h
  have perm : Perm (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a6) s₁ :=
    (⟨covers_mem (by rw [hrd]; simp), covers_mem (by rw [hwr]; simp), covers_mem (by rw [hwr]; simp)⟩ :
      Perm (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a6) s₀).of_eq h1.en.keeps.rd h1.en.keeps.wr
  exact ⟨fun _ _ => rfl, h1.en.keeps.sp, by rw [h1.s2, h1.s1, h1.s0]; exact perm,
    by rw [h1.s2, h1.s1, h1.s0, h1.en.keeps.sp]; exact hk⟩

section
variable {c st w : Addr} (L : Lay c st w)
include L

theorem saved_tagFrame {sp : Addr} (hk : StkOk c st w sp) {o : Nat} (ho : o = 0 ∨ o = 112) :
    ∀ r ∈ tagFrame st w o sp, (savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using L.saved_st (d := 0) (k := 32) (by decide)
  · exact saved_w (by decide) (.inl (by decide))
  · exact saved_w (by omega) (.inl (by omega))
  · exact saved_w (by decide) (.inr (by decide))
  · exact saved_below hk

end

/-- The tag, for a state that represents `a` and `ct`, from a memory `m₀`
that differs from the entry's only apart from the context and the state. -/
theorem fin_out {s₀ s : State} {m₀ : Mem} {rs : List Region} (hf₀ : Frame rs s₀.mem m₀)
    (hdc : ∀ r ∈ rs, (⟨s₀.gpr .a0, 256⟩ : Region).Disjoint r)
    (hds : ∀ r ∈ rs, (⟨s₀.gpr .a2, 80⟩ : Region).Disjoint r)
    (hR : (s₀.gpr .a1).toNat = 10 ∨ (s₀.gpr .a1).toNat = 12 ∨ (s₀.gpr .a1).toNat = 14)
    {V : Reg → BitVec 64} {sp : Addr} (h29 : V .s2 = s₀.gpr .a0) (h30 : V .s1 = s₀.gpr .a2)
    (h22 : V .s10 = s₀.gpr .a3) {o : Nat} {iv a ct : List Byte}
    (hf : FinOut V sp o (s₀.gpr .a1).toNat (ctxH s₀.mem (s₀.gpr .a0)) a ct m₀ s)
    (hs : StreamRepr s₀.mem (s₀.gpr .a2) (ctxCiph s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat)
      (ctxH s₀.mem (s₀.gpr .a0)) iv a ct) (hl : s₀.gpr .a3 = BitVec.ofNat 64 a.length) :
    bytesAt s.mem (V .s0 + BitVec.ofNat 64 o) 16 =
      fullTag (ctxCiph s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat) (ctxH s₀.mem (s₀.gpr .a0)) iv a ct := by
  rw [Proof.Gcm.streamRepr_iff] at hs
  obtain ⟨hj, hab, -⟩ := hs
  have hb := Nat.mod_lt (ghashInput a ct).length (show 16 > 0 by decide)
  have dS : ∀ {d k : Nat}, d + k ≤ 80 → ∀ r ∈ rs, (⟨s₀.gpr .a2 + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r :=
    fun hd r hr => (hds r hr).sub_left (Lay.stSub hd)
  have hab₀ : Absorbed m₀ (V .s1 + BitVec.ofNat 64 16) (V .s1 + BitVec.ofNat 64 32)
      (ctxH s₀.mem (s₀.gpr .a0)) (ghashInput a ct) := by
    rw [h30]
    exact hab.congr (blockAt_frame hf₀ (dS (d := 16) (by decide)))
      (bytesAt_frame hf₀ (dS (d := 32) (k := (ghashInput a ct).length % 16) (by omega)) (by omega))
  rw [hf.out hab₀,
    h29, ciph_keep hf₀ hdc hR, h30,
    blockAt_frame hf₀ (by simpa using dS (d := 0) (k := 16) (by decide)), hj,
    h22, toNat_of_eq hl, lensBlock_mod, Proof.Gcm.fullTag_eq]

theorem streamFinish_wp {s₀ : State} (h : streamFinishRISCV64.pre s₀) :
    WP isa streamFinish s₀ fun s' => abiPreserved s₀ s' ∧ streamFinishRISCV64.post s₀ s' := by
  have h' : finPre s₀ := h
  have L₀ := finLay h'
  have hR := fin_R h'
  have hk₀ := fin_stk h'
  have hh := h'
  obtain ⟨-, hwr, -, -, -, -, -, dtw, -⟩ := hh
  have hTw : Covers [⟨s₀.gpr .a5, 16⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  have run : ∀ {a ct : List Byte}, a.length % 16 = (s₀.gpr .a3).toNat % 16 → (s₀.gpr .a4).toNat = ct.length →
      WP isa streamFinish s₀ fun s' => abiPreserved s₀ s' ∧ ∀ iv,
        StreamRepr s₀.mem (s₀.gpr .a2) (ctxCiph s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat)
          (ctxH s₀.mem (s₀.gpr .a0)) iv a ct → s₀.gpr .a3 = BitVec.ofNat 64 a.length →
        bytesAt s'.mem (s₀.gpr .a5) 16 =
          fullTag (ctxCiph s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat) (ctxH s₀.mem (s₀.gpr .a0)) iv a ct := by
    intro a ct ha hP
    refine WP.seq (WP.mono (fin1_wp (fin_W h') (fin_al h')) fun s₁ h1 => ?_)
    have he₁ := fin_env h' h1
    have L := L₀.v h1.s2 h1.s1 h1.s0
    have hH₁ : blockAt s₁.mem (s₁.gpr .s2 + BitVec.ofNat 64 240) = ctxH s₀.mem (s₀.gpr .a0) := by
      rw [h1.s2]; exact ctxH_keep h1.en.frame (ctx_saved L₀)
    refine WP.seq (WP.mono (WP.with_rdwr (finTag_ok L (o := 0) (.inl rfl) (a := a) (ct := ct) he₁
      (by rw [h1.s3, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hR hH₁ (by rw [h1.s10]; exact ha)
      (by rw [h1.s11]; exact hP))) fun s₂ ⟨hf, rd₂, wr₂, _⟩ => ?_)
    have hTw₂ : Covers [⟨s₁.gpr .s9, 16⟩] s₂.wr := by
      rw [wr₂, h1.en.keeps.wr, h1.s9]; exact hTw
    have hTd : (⟨s₁.gpr .s9, 16⟩ : Region).Disjoint ⟨s₁.gpr .s0, 16⟩ := by
      rw [h1.s9, h1.s0]; exact dtw.sub_right (Region.sub_prefix (by decide))
    refine WP.seq (WP.mono (tagOut_ok hf.env hTw₂ hTd) fun s₃ ⟨hb₃, hf₃, g₃, hk₃⟩ => ?_)
    have he₃ := hf.env.keep (fun r hr => g₃ r (by revert r; decide)) hk₃.sp hk₃.rd hk₃.wr
    have sv₂ : SavedAt s₂.mem (s₀.gpr .a6) s₀ := by
      have := hf.frame; rw [h1.s1, h1.s0] at this
      exact h1.en.saved.frame this (saved_tagFrame L₀ hk₀ (.inl rfl))
    have sv₃ : SavedAt s₃.mem (s₀.gpr .a6) s₀ := sv₂.frame hf₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h1.s9]
      exact (dtw.sub_right (Lay.wSub (by decide))).symm)
    have e31 : s₃.gpr .s0 = s₀.gpr .a6 := (he₃.fr _ (by decide)).trans h1.s0
    refine WP.mono (restore_ok e31 (fin_al h') (by have := he₃.perm.w; rw [h1.s0] at this; exact Covers.right this)
      sv₃ he₃.sp)
      fun s' ⟨ga, hm, _⟩ => ⟨ga, fun iv hs hl => ?_⟩
    have := fin_out (s := s₂) h1.en.frame (ctx_saved L₀) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simpa using (L₀.saved_st (d := 0) (k := 80) (by decide)).symm) hR h1.s2 h1.s1
      h1.s10 hf hs hl
    rw [BitVec.add_zero] at this
    rw [hm, ← h1.s9, hb₃, this]
  have h₀ := run (a := List.replicate ((s₀.gpr .a3).toNat % 16) 0) (ct := List.replicate (s₀.gpr .a4).toNat 0)
    (by simp) (by simp)
  refine WP.mono (WP.forall_det (WP.mono h₀ fun _ hh => hh.1)
    (P := fun i : List Byte × List Byte × List Byte =>
      StreamRepr s₀.mem (s₀.gpr .a2) (ctxCiph s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat)
          (ctxH s₀.mem (s₀.gpr .a0)) i.1 i.2.1 i.2.2 ∧
        s₀.gpr .a3 = BitVec.ofNat 64 i.2.1.length ∧ (s₀.gpr .a4).toNat = i.2.2.length)
    fun i hi => WP.mono (run (a := i.2.1) (ct := i.2.2) (by rw [hi.2.1, toNat_mod16]) hi.2.2)
      fun s' hh => hh.2 i.1 hi.1 hi.2.1)
    fun s' hh => ⟨hh.1, fun iv a c hs hl hp => hh.2 ⟨iv, a, c⟩ ⟨hs, hl, hp⟩⟩

end VG.Proof.AesGcm.RISCV64
