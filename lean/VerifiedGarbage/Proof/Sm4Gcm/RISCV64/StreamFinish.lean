module

public import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Contract
public import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.FinTag
public import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.StreamCrypt
public import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamFinish
import VerifiedGarbage.Proof.AesGcm.RISCV64.Absorb
import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
import VerifiedGarbage.Proof.Gcm.Be64
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.Offset

/-!
# SM4-GCM on RISC-V: `vg_sm4_gcm_stream_finish`

Untrusted: everything here is checked by Lean. AES-GCM's
(`Proof/AesGcm/RISCV64/StreamFinish.lean`) with SM4's `finTag 0`: the entry
saves our caller's registers and keeps the arguments in `s1`, `s2` and
`s9`–`s11` (`fin1_wp`); `finTag 0` puts the tag into `W` (`fin_out`), and
`tagOut` copies it to `tag` (`streamFinish_wp`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.RISCV64

open VG VG.RISCV64 VG.Impl.Sm4Gcm.RISCV64
open VG.Impl.AesGcm.RISCV64 (mov tagOut)
open VG.Proof.AesGcm.RISCV64 hiding CrIn CrMid CrOut crFrame ciphOf TailKs ctx_crFrame ciph_frame
  CtrCall CtrPost ctr_call ctr_rel stp_crFrame saved_crFrame ciph_keep tagFrame TagOut TagMid tagLens_ok
  tagArgs_ok ctrTag_mk tagCall_ok tag_ok tFrame_sub t_tagFrame FinOut finTag_ok finLay fin_R fin_al fin_stk
  fin_W SF1 fin1_wp fin_env saved_tagFrame fin_out streamFinish_wp finPre streamFinishRISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ghashInput fullTag)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Proof.Gcm (Absorbed)

section
variable {s₀ : State} (h : finPre s₀)
include h

theorem finLay : Lay (s₀.gpr .a0) (s₀.gpr .a1) (s₀.gpr .a5) := by
  obtain ⟨-, -, dcs, -, dcw, -, dsw, -, fc, fs, -, fw, -, a0, a1, a5⟩ := h
  exact Lay.of fc fs fw dcs dcw dsw a0 a1 a5

theorem fin_al : (s₀.gpr .a5).toNat % 8 = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, a5⟩ := h
  exact a5

theorem fin_stk : StkOk (s₀.gpr .a0) (s₀.gpr .a1) (s₀.gpr .a5) s₀.sp := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hk, -⟩ := h
  exact hk.stk (by simp) (by simp) (by simp)

theorem fin_big {V : Reg → BitVec 64} (h2 : V .s2 = s₀.gpr .a0) (h1 : V .s1 = s₀.gpr .a1)
    (h0 : V .s0 = s₀.gpr .a5) : Big V s₀.sp := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hk, -⟩ := h
  exact hk.big (by rw [h2]; simp) (by rw [h1]; simp) (by rw [h0]; simp)

theorem fin_bw : (below s₀.sp 3232).Disjoint ⟨s₀.gpr .a5, 2560⟩ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hk, -⟩ := h
  exact hk.buf3 (by simp)

theorem fin_W : Covers [⟨s₀.gpr .a5, 2560⟩] s₀.wr := by
  rw [h.2.1]; exact covers_mem (by simp)

end

/-- After the entry of `finish`, from `s₀`. -/
structure SF1 (s₀ s₁ : State) : Prop where
  en : Entered s₀ (s₀.gpr .a5) s₁
  s0 : s₁.gpr .s0 = s₀.gpr .a5
  s1 : s₁.gpr .s1 = s₀.gpr .a1
  s2 : s₁.gpr .s2 = s₀.gpr .a0
  s10 : s₁.gpr .s10 = s₀.gpr .a2
  s11 : s₁.gpr .s11 = s₀.gpr .a3
  s9 : s₁.gpr .s9 = s₀.gpr .a4

theorem fin1_wp {s₀ : State} (hW : Covers [⟨s₀.gpr .a5, 2560⟩] s₀.wr) (hal : (s₀.gpr .a5).toNat % 8 = 0) :
    WP isa (.block finEntry) s₀ (SF1 s₀) := by
  refine WP.block_append (WP.mono (save_ok (b := .a5) hW hal) fun s₁ ⟨hg, h31, hk, hsv, hf⟩ => ?_)
  have e3 : s₁.gpr .a0 = s₀.gpr .a0 := hg _ (by decide)
  have e4 : s₁.gpr .a1 = s₀.gpr .a1 := hg _ (by decide)
  have e5 : s₁.gpr .a2 = s₀.gpr .a2 := hg _ (by decide)
  have e6 : s₁.gpr .a3 = s₀.gpr .a3 := hg _ (by decide)
  have e7 : s₁.gpr .a4 = s₀.gpr .a4 := hg _ (by decide)
  crun [Int.reduceNatCast', mov, e3, e4, e5, e6, e7, h31]
  refine ⟨⟨⟨hk.rd, hk.wr, hk.sp⟩, hsv, hf⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [h31]

/-- The environment after the entry. -/
theorem fin_env {s₀ s₁ : State} (h : finPre s₀) (h1 : SF1 s₀ s₁) : Env s₁.gpr s₀.sp s₁ := by
  have hk := fin_stk h
  obtain ⟨hrd, hwr, -⟩ := h
  have perm : Perm (s₀.gpr .a0) (s₀.gpr .a1) (s₀.gpr .a5) s₁ :=
    (⟨covers_mem (by rw [hrd]; simp), covers_mem (by rw [hwr]; simp), covers_mem (by rw [hwr]; simp)⟩ :
      Perm (s₀.gpr .a0) (s₀.gpr .a1) (s₀.gpr .a5) s₀).of_eq h1.en.keeps.rd h1.en.keeps.wr
  exact ⟨fun _ _ => rfl, h1.en.keeps.sp, by rw [h1.s2, h1.s1, h1.s0]; exact perm,
    by rw [h1.s2, h1.s1, h1.s0, h1.en.keeps.sp]; exact hk⟩

section
variable {c st w : Addr} (L : Lay c st w)
include L

theorem saved_tagFrame {sp : Addr} (hbw : (below sp 3232).Disjoint ⟨w, 2560⟩) {o : Nat} (ho : o = 0 ∨ o = 112) :
    ∀ r ∈ tagFrame st w o sp, (savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using L.saved_st (d := 0) (k := 32) (by decide)
  · exact saved_w (by decide) (.inl (by decide))
  · exact saved_w (by omega) (.inl (by omega))
  · exact saved_w (by decide) (.inr (by decide))
  · exact (hbw.sub_right (Lay.wSub (by decide))).symm

end

/-- The tag, for a state that represents `a` and `ct`, from a memory `m₀`
that differs from the entry's only apart from the context and the state. -/
theorem fin_out {s₀ s : State} {m₀ : Mem} {rs : List Region} (hf₀ : Frame rs s₀.mem m₀)
    (hdc : ∀ r ∈ rs, (⟨s₀.gpr .a0, 256⟩ : Region).Disjoint r)
    (hds : ∀ r ∈ rs, (⟨s₀.gpr .a1, 80⟩ : Region).Disjoint r)
    {V : Reg → BitVec 64} {sp : Addr} (h29 : V .s2 = s₀.gpr .a0) (h30 : V .s1 = s₀.gpr .a1)
    (h22 : V .s10 = s₀.gpr .a2) {o : Nat} {iv a ct : List Byte}
    (hf : FinOut V sp o (ctxH s₀.mem (s₀.gpr .a0)) a ct m₀ s)
    (hs : StreamRepr s₀.mem (s₀.gpr .a1) (ctxCiph s₀.mem (s₀.gpr .a0))
      (ctxH s₀.mem (s₀.gpr .a0)) iv a ct) (hl : s₀.gpr .a2 = BitVec.ofNat 64 a.length) :
    bytesAt s.mem (V .s0 + BitVec.ofNat 64 o) 16 =
      fullTag (ctxCiph s₀.mem (s₀.gpr .a0)) (ctxH s₀.mem (s₀.gpr .a0)) iv a ct := by
  rw [Proof.Gcm.streamRepr_iff] at hs
  obtain ⟨hj, hab, -⟩ := hs
  have hb := Nat.mod_lt (ghashInput a ct).length (show 16 > 0 by decide)
  have dS : ∀ {d k : Nat}, d + k ≤ 80 → ∀ r ∈ rs, (⟨s₀.gpr .a1 + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r :=
    fun hd r hr => (hds r hr).sub_left (Lay.stSub hd)
  have hab₀ : Absorbed m₀ (V .s1 + BitVec.ofNat 64 16) (V .s1 + BitVec.ofNat 64 32)
      (ctxH s₀.mem (s₀.gpr .a0)) (ghashInput a ct) := by
    rw [h30]
    exact hab.congr (blockAt_frame hf₀ (dS (d := 16) (by decide)))
      (bytesAt_frame hf₀ (dS (d := 32) (k := (ghashInput a ct).length % 16) (by omega)) (by omega))
  rw [hf.out hab₀,
    h29, ciph_keep hf₀ hdc, h30,
    blockAt_frame hf₀ (by simpa using dS (d := 0) (k := 16) (by decide)), hj,
    h22, toNat_of_eq hl, lensBlock_mod, Proof.Gcm.fullTag_eq]

theorem streamFinish_wp {s₀ : State} (h : streamFinishRISCV64.pre s₀) :
    WP isa streamFinish s₀ fun s' => abiPreserved s₀ s' ∧ streamFinishRISCV64.post s₀ s' := by
  have h' : finPre s₀ := h
  have L₀ := finLay h'
  have hk₀ := fin_stk h'
  have hh := h'
  obtain ⟨-, hwr, -, -, -, -, -, dtw, -⟩ := hh
  have hbw := fin_bw h'

  have hTw : Covers [⟨s₀.gpr .a4, 16⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  have run : ∀ {a ct : List Byte}, a.length % 16 = (s₀.gpr .a2).toNat % 16 → (s₀.gpr .a3).toNat = ct.length →
      WP isa streamFinish s₀ fun s' => abiPreserved s₀ s' ∧ ∀ iv,
        StreamRepr s₀.mem (s₀.gpr .a1) (ctxCiph s₀.mem (s₀.gpr .a0))
          (ctxH s₀.mem (s₀.gpr .a0)) iv a ct → s₀.gpr .a2 = BitVec.ofNat 64 a.length →
        bytesAt s'.mem (s₀.gpr .a4) 16 =
          fullTag (ctxCiph s₀.mem (s₀.gpr .a0)) (ctxH s₀.mem (s₀.gpr .a0)) iv a ct := by
    intro a ct ha hP
    refine WP.seq (WP.mono (fin1_wp (fin_W h') (fin_al h')) fun s₁ h1 => ?_)
    have he₁ := fin_env h' h1
    have L := L₀.v h1.s2 h1.s1 h1.s0
    have hH₁ : blockAt s₁.mem (s₁.gpr .s2 + BitVec.ofNat 64 240) = ctxH s₀.mem (s₀.gpr .a0) := by
      rw [h1.s2]; exact ctxH_keep h1.en.frame (ctx_saved L₀)
    refine WP.seq (WP.mono (WP.with_rdwr (finTag_ok L (fin_big h' h1.s2 h1.s1 h1.s0) (o := 0) (.inl rfl)
      (a := a) (ct := ct) he₁ hH₁ (by rw [h1.s10]; exact ha)
      (by rw [h1.s11]; exact hP))) fun s₂ ⟨hf, rd₂, wr₂, _⟩ => ?_)
    have hTw₂ : Covers [⟨s₁.gpr .s9, 16⟩] s₂.wr := by
      rw [wr₂, h1.en.keeps.wr, h1.s9]; exact hTw
    have hTd : (⟨s₁.gpr .s9, 16⟩ : Region).Disjoint ⟨s₁.gpr .s0, 16⟩ := by
      rw [h1.s9, h1.s0]; exact dtw.sub_right (Region.sub_prefix (by decide))
    refine WP.seq (WP.mono (tagOut_ok hf.env hTw₂ hTd) fun s₃ ⟨hb₃, hf₃, g₃, hk₃⟩ => ?_)
    have he₃ := hf.env.keep (fun r hr => g₃ r (by revert r; decide)) hk₃.sp hk₃.rd hk₃.wr
    have sv₂ : SavedAt s₂.mem (s₀.gpr .a5) s₀ := by
      have := hf.frame; rw [h1.s1, h1.s0] at this
      exact h1.en.saved.frame this (saved_tagFrame L₀ hbw (.inl rfl))
    have sv₃ : SavedAt s₃.mem (s₀.gpr .a5) s₀ := sv₂.frame hf₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h1.s9]
      exact (dtw.sub_right (Lay.wSub (by decide))).symm)
    have e31 : s₃.gpr .s0 = s₀.gpr .a5 := (he₃.fr _ (by decide)).trans h1.s0
    refine WP.mono (restore_ok e31 (fin_al h') (by have := he₃.perm.w; rw [h1.s0] at this; exact Covers.right this)
      sv₃ he₃.sp)
      fun s' ⟨ga, hm, _⟩ => ⟨ga, fun iv hs hl => ?_⟩
    have := fin_out (s := s₂) h1.en.frame (ctx_saved L₀) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simpa using (L₀.saved_st (d := 0) (k := 80) (by decide)).symm) h1.s2 h1.s1
      h1.s10 hf hs hl
    rw [BitVec.add_zero] at this
    rw [hm, ← h1.s9, hb₃, this]
  have h₀ := run (a := List.replicate ((s₀.gpr .a2).toNat % 16) 0) (ct := List.replicate (s₀.gpr .a3).toNat 0)
    (by simp) (by simp)
  refine WP.mono (WP.forall_det (WP.mono h₀ fun _ hh => hh.1)
    (P := fun i : List Byte × List Byte × List Byte =>
      StreamRepr s₀.mem (s₀.gpr .a1) (ctxCiph s₀.mem (s₀.gpr .a0))
          (ctxH s₀.mem (s₀.gpr .a0)) i.1 i.2.1 i.2.2 ∧
        s₀.gpr .a2 = BitVec.ofNat 64 i.2.1.length ∧ (s₀.gpr .a3).toNat = i.2.2.length)
    fun i hi => WP.mono (run (a := i.2.1) (ct := i.2.2) (by rw [hi.2.1, toNat_mod16]) hi.2.2)
      fun s' hh => hh.2 i.1 hi.1 hi.2.1)
    fun s' hh => ⟨hh.1, fun iv a c hs hl hp => hh.2 ⟨iv, a, c⟩ ⟨hs, hl, hp⟩⟩

end VG.Proof.Sm4Gcm.RISCV64
