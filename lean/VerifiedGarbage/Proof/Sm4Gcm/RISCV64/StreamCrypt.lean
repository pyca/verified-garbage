module

public import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Contract
public import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Crypt
public import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.RISCV64.Absorb
import VerifiedGarbage.Proof.AesGcm.RISCV64.Ghash1
import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset

/-!
# SM4-GCM on RISC-V: `vg_sm4_gcm_stream_encrypt` and `vg_sm4_gcm_stream_decrypt`

Untrusted: everything here is checked by Lean. AES-GCM's
(`Proof/AesGcm/RISCV64/StreamCrypt.lean`) with SM4's `crypt`: the entry
saves our caller's registers and keeps the arguments in `s1`–`s11`
(`sc1_wp`); `encrypt` runs `crypt` on the data and then absorbs what it
wrote (`textAbsorb`), `decrypt` absorbs the data first; both keep `J₀`
(`enc_run`, `dec_run`) (`streamEncrypt_wp`, `streamDecrypt_wp`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.RISCV64

open VG VG.RISCV64 VG.Impl.Sm4Gcm.RISCV64
open VG.Impl.AesGcm.RISCV64 (mov textArgs textAbsorb)
open VG.Proof.AesGcm.RISCV64 hiding CrIn CrMid CrOut crFrame ciphOf TailKs ctx_crFrame ciph_frame
  CtrCall CtrPost ctr_call ctr_rel cryptHead_ok ctrArgs_ok ctrWhole_mk cryptWhole_ok tailArgs_ok ctrTail_mk
  tailKs_ok tailXor_ok cryptTail_ok cryptFill_ok crypt_ok SC1 sc1_wp scLay sc_R sc_al sc_stk sc_W sc_env
  sc_dataW stp_crFrame saved_crFrame ciph_keep scR EncOut enc_run dec_run streamEncrypt_wp streamDecrypt_wp
  streamCryptPre streamCryptPub streamEncryptRISCV64 streamDecryptRISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ghashInput gctr inc32 j0)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

/-- After the entry, from `s₀`. -/
structure SC1 (s₀ s₁ : State) : Prop where
  en : Entered s₀ (s₀.gpr .a6) s₁
  s0 : s₁.gpr .s0 = s₀.gpr .a6
  s1 : s₁.gpr .s1 = s₀.gpr .a1
  s2 : s₁.gpr .s2 = s₀.gpr .a0
  s11 : s₁.gpr .s11 = s₀.gpr .a3
  s10 : s₁.gpr .s10 = s₀.gpr .a2
  s9 : s₁.gpr .s9 = s₀.gpr .a4
  s8 : s₁.gpr .s8 = s₀.gpr .a5

theorem sc1_wp {s₀ : State} (hW : Covers [⟨s₀.gpr .a6, 2560⟩] s₀.wr) (hal : (s₀.gpr .a6).toNat % 8 = 0) :
    WP isa (.block cryptEntry) s₀ (SC1 s₀) := by
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

section
variable {s₀ : State} (h : streamCryptPre s₀)
include h

theorem scLay : Lay (s₀.gpr .a0) (s₀.gpr .a1) (s₀.gpr .a6) := by
  obtain ⟨-, -, dcs, -, dcw, -, dsw, -, fc, fs, -, fw, -, a0, a1, a6⟩ := h
  exact Lay.of fc fs fw dcs dcw dsw a0 a1 a6

theorem sc_al : (s₀.gpr .a6).toNat % 8 = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, a6⟩ := h
  exact a6

theorem sc_stk : StkOk (s₀.gpr .a0) (s₀.gpr .a1) (s₀.gpr .a6) s₀.sp := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hk, -⟩ := h
  exact hk.stk (by simp) (by simp) (by simp)

theorem sc_big {V : Reg → BitVec 64} (h2 : V .s2 = s₀.gpr .a0) (h1 : V .s1 = s₀.gpr .a1)
    (h0 : V .s0 = s₀.gpr .a6) : Big V s₀.sp := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hk, -⟩ := h
  exact hk.big (by rw [h2]; simp) (by rw [h1]; simp) (by rw [h0]; simp)

/-- The context, the state and `W` are apart from the 3232 bytes below the stack pointer. -/
theorem sc_b3 : (below s₀.sp 3232).Disjoint ⟨s₀.gpr .a0, 256⟩ ∧ (below s₀.sp 3232).Disjoint ⟨s₀.gpr .a1, 80⟩ ∧
    (below s₀.sp 3232).Disjoint ⟨s₀.gpr .a6, 2560⟩ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hk, -⟩ := h
  exact ⟨hk.buf3 (by simp), hk.buf3 (by simp), hk.buf3 (by simp)⟩

/-- The data are apart from the 3232 bytes below the stack pointer. -/
theorem sc_bd : (below s₀.sp 3232).Disjoint ⟨s₀.gpr .a4, (s₀.gpr .a5).toNat⟩ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hk, -⟩ := h
  exact hk.buf3 (by simp)

theorem sc_W : Covers [⟨s₀.gpr .a6, 2560⟩] s₀.wr := by
  rw [h.2.1]; exact covers_mem (by simp)

/-- The environment after the entry. -/
theorem sc_env {s₁ : State} (h1 : SC1 s₀ s₁) : Env s₁.gpr s₀.sp s₁ := by
  have hk := sc_stk h
  obtain ⟨hrd, hwr, -⟩ := h
  have perm : Perm (s₀.gpr .a0) (s₀.gpr .a1) (s₀.gpr .a6) s₁ :=
    (⟨covers_mem (by rw [hrd]; simp), covers_mem (by rw [hwr]; simp), covers_mem (by rw [hwr]; simp)⟩ :
      Perm (s₀.gpr .a0) (s₀.gpr .a1) (s₀.gpr .a6) s₀).of_eq h1.en.keeps.rd h1.en.keeps.wr
  exact ⟨fun _ _ => rfl, h1.en.keeps.sp, by rw [h1.s2, h1.s1, h1.s0]; exact perm,
    by rw [h1.s2, h1.s1, h1.s0, h1.en.keeps.sp]; exact hk⟩

/-- The data, as `crypt` needs it. -/
theorem sc_dataW {s : State} (hwr' : s.wr = s₀.wr) (hsp : s.sp = s₀.sp) :
    DataW (s₀.gpr .a0) (s₀.gpr .a1) (s₀.gpr .a6) s (s₀.gpr .a4) (s₀.gpr .a5).toNat := by
  obtain ⟨-, hwr, -, dcd, -, dsd, -, ddw, -, -, fd, -, hk, -⟩ := h
  have hD : Covers [⟨s₀.gpr .a4, (s₀.gpr .a5).toNat⟩] s.wr := by rw [hwr', hwr]; exact covers_mem (by simp)
  exact ⟨⟨covers_left hD, (s₀.gpr .a5).isLt, fd, dsd.symm, ddw, by rw [hsp]; exact hk.buf (by simp)⟩, hD, dcd⟩

end

section
variable {c st w : Addr} (L : Lay c st w)
include L

omit L in
theorem stp_crFrame {sp : Addr} (hbs : (below sp 3232).Disjoint ⟨st, 80⟩) {s : State} {D : Addr} {n : Nat}
    (hd : DataW c st w s D n) {d k : Nat} (h1 : d + k ≤ 48) :
    ∀ r ∈ crFrame st sp D n, (⟨st + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hd.ok.st.sub_right (Lay.stSub (by omega_arith))).symm
  · exact Lay.st_st (.inl h1) (by omega_arith) (by decide)
  · exact (hbs.sub_right (Lay.stSub (by omega_arith))).symm

theorem saved_crFrame {sp : Addr} (hbw : (below sp 3232).Disjoint ⟨w, 2560⟩) {s : State} {D : Addr} {n : Nat}
    (hd : DataW c st w s D n) : ∀ r ∈ crFrame st sp D n, (savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hd.ok.w.sub_right (Lay.wSub (by decide))).symm
  · exact L.saved_st (by decide)
  · exact (hbw.sub_right (Lay.wSub (by decide))).symm

theorem ctx_crFrame' {sp : Addr} (hbc : (below sp 3232).Disjoint ⟨c, 256⟩) {s : State} {D : Addr} {n : Nat}
    (hd : DataW c st w s D n) : ∀ r ∈ crFrame st sp D n, (⟨c, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hd.ctx
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact hbc.symm

omit L in
/-- `ciphOf` is `ctxCiph`, and a frame apart from the context keeps it. -/
theorem ciph_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨c, 256⟩ : Region).Disjoint r) : ciphOf m' c = ctxCiph m c := ciph_frame hf hd

end

/-- What `encrypt` (or `decrypt`) does, for the counter block `icb`, the
additional data `a` and the text `ct` so far (only their lengths matter to
the code). -/
structure EncOut (s₀ : State) (icb : Block) (a ct : List Byte) (dec : Bool) (s : State) : Prop where
  ctr : Ctr s₀.mem (s₀.gpr .a1 + BitVec.ofNat 64 48) (s₀.gpr .a1 + BitVec.ofNat 64 64)
      (ctxCiph s₀.mem (s₀.gpr .a0)) icb ct.length →
    Ctr s.mem (s₀.gpr .a1 + BitVec.ofNat 64 48) (s₀.gpr .a1 + BitVec.ofNat 64 64)
      (ctxCiph s₀.mem (s₀.gpr .a0)) icb (ct.length + (s₀.gpr .a5).toNat)
  out : Ctr s₀.mem (s₀.gpr .a1 + BitVec.ofNat 64 48) (s₀.gpr .a1 + BitVec.ofNat 64 64)
      (ctxCiph s₀.mem (s₀.gpr .a0)) icb ct.length →
    bytesAt s.mem (s₀.gpr .a4) (s₀.gpr .a5).toNat =
      xorKs (ctxCiph s₀.mem (s₀.gpr .a0)) icb ct.length (bytesAt s₀.mem (s₀.gpr .a4) (s₀.gpr .a5).toNat)
  abs : Ctr s₀.mem (s₀.gpr .a1 + BitVec.ofNat 64 48) (s₀.gpr .a1 + BitVec.ofNat 64 64)
      (ctxCiph s₀.mem (s₀.gpr .a0)) icb ct.length →
    Absorbed s₀.mem (s₀.gpr .a1 + BitVec.ofNat 64 16) (s₀.gpr .a1 + BitVec.ofNat 64 32)
      (ctxH s₀.mem (s₀.gpr .a0)) (ghashInput a ct) →
    Absorbed s.mem (s₀.gpr .a1 + BitVec.ofNat 64 16) (s₀.gpr .a1 + BitVec.ofNat 64 32)
      (ctxH s₀.mem (s₀.gpr .a0))
      (ghashInput a (ct ++ if dec then bytesAt s₀.mem (s₀.gpr .a4) (s₀.gpr .a5).toNat else
        xorKs (ctxCiph s₀.mem (s₀.gpr .a0)) icb ct.length (bytesAt s₀.mem (s₀.gpr .a4) (s₀.gpr .a5).toNat)))
  j : blockAt s.mem (s₀.gpr .a1) = blockAt s₀.mem (s₀.gpr .a1)

theorem enc_run {s₀ : State} (h : streamCryptPre s₀) (icb : Block) {a ct : List Byte}
    (ha : a.length % 16 = (s₀.gpr .a2).toNat % 16) (hP : (s₀.gpr .a3).toNat = ct.length) :
    WP isa streamEncrypt s₀ fun s' => abiPreserved s₀ s' ∧ EncOut s₀ icb a ct false s' := by
  have L₀ := scLay h
  have hk₀ := sc_stk h
  obtain ⟨bc₀, bs₀, bw₀⟩ := sc_b3 h
  refine WP.seq (WP.block_append (WP.mono (sc1_wp (sc_W h) (sc_al h)) fun s₁ h1 => ?_))
  have he₁ := sc_env h h1
  have L := L₀.v h1.s2 h1.s1 h1.s0
  refine WP.mono textArgs_ok fun s₂ ⟨h24, h25, h26, hg₂, hk₂⟩ => ?_
  have he₂ : Env s₁.gpr s₀.sp s₂ := he₁.keep (fun r hr => hg₂ r (by revert r; decide) (by revert r; decide)
    (by revert r; decide)) hk₂.sp hk₂.rd hk₂.wr
  have hd₂₀ := sc_dataW h (s := s₂) (hk₂.wr.trans h1.en.keeps.wr) (hk₂.sp.trans h1.en.keeps.sp)
  have hd₂ : DataW (s₁.gpr .s2) (s₁.gpr .s1) (s₁.gpr .s0) s₂ (s₁.gpr .s9) (s₁.gpr .s8).toNat := by
    rw [h1.s2, h1.s1, h1.s0, h1.s9, h1.s8]; exact hd₂₀
  have ci : CrIn s₁.gpr s₀.sp icb ct.length (s₁.gpr .s9) (s₁.gpr .s8).toNat s₂ :=
    ⟨he₂, h24, by rw [h25, BitVec.ofNat_toNat, BitVec.setWidth_eq], by rw [h26, h1.s11, hP],
      sc_big h h1.s2 h1.s1 h1.s0, by rw [h1.s9, h1.s8]; exact sc_bd h, hd₂⟩
  refine WP.seq (WP.mono (WP.with_rdwr (crypt_ok L ci)) fun s₃ ⟨co, rd₃, wr₃, sp₃⟩ => ?_)
  have hd₃ := hd₂.ok.of_eq rd₃ wr₃ sp₃
  have f₂ : Frame [savedR (s₀.gpr .a6)] s₀.mem s₂.mem := by rw [hk₂.mem]; exact h1.en.frame
  have cf := co.frame
  rw [h1.s1, h1.s9, h1.s8] at cf
  have hH₃ : blockAt s₃.mem (s₁.gpr .s2 + BitVec.ofNat 64 240) = ctxH s₀.mem (s₀.gpr .a0) := by
    rw [h1.s2, blockAt_frame cf (fun r hr => (ctx_crFrame' L₀ bc₀ hd₂₀ r hr).sub_left (Lay.ctxSub (by decide))),
      ctxH_keep f₂ (ctx_saved L₀)]
  refine WP.seq (WP.mono (WP.with_rdwr (textAbsorb_ok L (a := a) (ct := ct) co.env hH₃ hd₃ (by rw [h1.s10]; exact ha)
    (by rw [h1.s11]; exact hP))) fun s₄ ⟨ta, rd₄, wr₄, _⟩ => ?_)
  have tf := ta.frame
  rw [h1.s1, h1.s0] at tf
  have sv₄ : SavedAt s₄.mem (s₀.gpr .a6) s₀ :=
    (((hk₂.mem ▸ h1.en.saved : SavedAt s₂.mem (s₀.gpr .a6) s₀)).frame cf (saved_crFrame L₀ bw₀ hd₂₀)).frame tf
      (saved_taFrame L₀ hk₀)
  have e31 : s₄.gpr .s0 = s₀.gpr .a6 := (ta.env.fr _ (by decide)).trans h1.s0
  refine WP.mono (restore_ok e31 (sc_al h) (by have := ta.env.perm.w; rw [h1.s0] at this; exact Covers.right this)
    sv₄ ta.env.sp)
    fun s' ⟨ga, hm, _⟩ => ⟨ga, ?_⟩
  have hc : ciphOf s₂.mem (s₁.gpr .s2) = ctxCiph s₀.mem (s₀.gpr .a0)  := by
    rw [h1.s2]; exact ciph_keep f₂ (ctx_saved L₀)
  have ctr₂ : ∀ {P : Nat}, Ctr s₀.mem (s₀.gpr .a1 + BitVec.ofNat 64 48) (s₀.gpr .a1 + BitVec.ofNat 64 64)
      (ctxCiph s₀.mem (s₀.gpr .a0)) icb P →
      Ctr s₂.mem (s₁.gpr .s1 + BitVec.ofNat 64 48) (s₁.gpr .s1 + BitVec.ofNat 64 64)
        (ciphOf s₂.mem (s₁.gpr .s2)) icb P := fun hc₀ => by
    rw [hc, h1.s1]
    exact hc₀.congr (blockAt_frame f₂ (stp_saved L₀ (by decide))) (blockAt_frame f₂ (stp_saved L₀ (by decide)))
  have dat₂ : bytesAt s₂.mem (s₀.gpr .a4) (s₀.gpr .a5).toNat = bytesAt s₀.mem (s₀.gpr .a4) (s₀.gpr .a5).toNat :=
    bytesAt_frame f₂ (data_saved hd₂₀.ok) (by have := hd₂₀.ok.lt; omega_arith)
  have out₃ : Ctr s₀.mem (s₀.gpr .a1 + BitVec.ofNat 64 48) (s₀.gpr .a1 + BitVec.ofNat 64 64)
      (ctxCiph s₀.mem (s₀.gpr .a0)) icb ct.length →
      bytesAt s₃.mem (s₀.gpr .a4) (s₀.gpr .a5).toNat =
        xorKs (ctxCiph s₀.mem (s₀.gpr .a0)) icb ct.length (bytesAt s₀.mem (s₀.gpr .a4) (s₀.gpr .a5).toNat) :=
    fun hc₀ => by
      have := co.out (ctr₂ hc₀)
      rw [hc, h1.s9, h1.s8, dat₂] at this
      exact this
  have hd₃₀ : DataOk (s₀.gpr .a1) (s₀.gpr .a6) s₃ (s₀.gpr .a4) (s₀.gpr .a5).toNat := hd₂₀.ok.of_eq rd₃ wr₃ sp₃
  refine ⟨fun hc₀ => ?_, fun hc₀ => ?_, fun hc₀ hab => ?_, ?_⟩
  · rw [hm]
    have := co.ctr (ctr₂ hc₀)
    rw [hc, h1.s1, h1.s8] at this
    exact this.congr (blockAt_frame tf (stp_taFrame L₀ hk₀ (.inr ⟨by decide, by decide⟩)))
      (blockAt_frame tf (stp_taFrame L₀ hk₀ (.inr ⟨by decide, by decide⟩)))
  · rw [hm, bytesAt_frame tf (data_taFrame hd₃₀ (sp₃.trans (hk₂.sp.trans h1.en.keeps.sp))) (by have := hd₃₀.lt; omega_arith)]
    exact out₃ hc₀
  · rw [hm]
    have hb := Nat.mod_lt (ghashInput a ct).length (show 16 > 0 by decide)
    have hab₃ : Absorbed s₃.mem (s₀.gpr .a1 + BitVec.ofNat 64 16) (s₀.gpr .a1 + BitVec.ofNat 64 32)
        (ctxH s₀.mem (s₀.gpr .a0)) (ghashInput a ct) :=
      (hab.congr (blockAt_frame f₂ (stp_saved L₀ (by decide)))
        (bytesAt_frame f₂ (stp_saved L₀ (by omega_arith)) (by omega_arith))).congr
        (blockAt_frame cf (stp_crFrame bs₀ hd₂₀ (by decide)))
        (bytesAt_frame cf (stp_crFrame bs₀ hd₂₀ (by omega_arith)) (by omega_arith))
    have := ta.abs (by rw [h1.s1]; exact hab₃)
    rw [h1.s1, h1.s9, h1.s8, out₃ hc₀] at this
    exact this
  · rw [hm, blockAt_frame tf (by simpa using stp_taFrame L₀ hk₀ (d := 0) (k := 16) (.inl (by decide))),
      blockAt_frame cf (by simpa using stp_crFrame bs₀ hd₂₀ (d := 0) (k := 16) (by decide)),
      blockAt_frame f₂ (by simpa using stp_saved L₀ (d := 0) (k := 16) (by decide))]

theorem dec_run {s₀ : State} (h : streamCryptPre s₀) (icb : Block) {a ct : List Byte}
    (ha : a.length % 16 = (s₀.gpr .a2).toNat % 16) (hP : (s₀.gpr .a3).toNat = ct.length) :
    WP isa streamDecrypt s₀ fun s' => abiPreserved s₀ s' ∧ EncOut s₀ icb a ct true s' := by
  have L₀ := scLay h
  have hk₀ := sc_stk h
  obtain ⟨-, bs₀, bw₀⟩ := sc_b3 h
  refine WP.seq (WP.mono (sc1_wp (sc_W h) (sc_al h)) fun s₁ h1 => ?_)
  have he₁ := sc_env h h1
  have L := L₀.v h1.s2 h1.s1 h1.s0
  have f₁ : Frame [savedR (s₀.gpr .a6)] s₀.mem s₁.mem := h1.en.frame
  have hd₁₀ := sc_dataW h (s := s₁) h1.en.keeps.wr h1.en.keeps.sp
  have hd₁ : DataOk (s₁.gpr .s1) (s₁.gpr .s0) s₁ (s₁.gpr .s9) (s₁.gpr .s8).toNat := by
    rw [h1.s1, h1.s0, h1.s9, h1.s8]; exact hd₁₀.ok
  have hH₁ : blockAt s₁.mem (s₁.gpr .s2 + BitVec.ofNat 64 240) = ctxH s₀.mem (s₀.gpr .a0) := by
    rw [h1.s2]; exact ctxH_keep f₁ (ctx_saved L₀)
  refine WP.seq (WP.mono (WP.with_rdwr (textAbsorb_ok L (a := a) (ct := ct) he₁ hH₁ hd₁
    (by rw [h1.s10]; exact ha) (by rw [h1.s11]; exact hP))) fun s₄ ⟨ta, rd₄, wr₄, sp₄⟩ => ?_)
  have tf := ta.frame
  rw [h1.s1, h1.s0] at tf
  refine WP.seq (WP.mono textArgs_ok fun s₅ ⟨h24, h25, h26, hg₅, hk₅⟩ => ?_)
  have he₅ : Env s₁.gpr s₀.sp s₅ := ta.env.keep (fun r hr => hg₅ r (by revert r; decide) (by revert r; decide)
    (by revert r; decide)) hk₅.sp hk₅.rd hk₅.wr
  have hd₅₀ := sc_dataW h (s := s₅) (hk₅.wr.trans (wr₄.trans h1.en.keeps.wr))
    (hk₅.sp.trans (sp₄.trans h1.en.keeps.sp))
  have hd₅ : DataW (s₁.gpr .s2) (s₁.gpr .s1) (s₁.gpr .s0) s₅ (s₁.gpr .s9) (s₁.gpr .s8).toNat := by
    rw [h1.s2, h1.s1, h1.s0, h1.s9, h1.s8]; exact hd₅₀
  have e20 := ta.env.fr .s9 (by decide)
  have e19 := ta.env.fr .s8 (by decide)
  have e23 := ta.env.fr .s11 (by decide)
  have ci : CrIn s₁.gpr s₀.sp icb ct.length (s₁.gpr .s9) (s₁.gpr .s8).toNat s₅ :=
    ⟨he₅, by rw [h24, e20], by rw [h25, e19, BitVec.ofNat_toNat, BitVec.setWidth_eq],
      by rw [h26, e23, h1.s11, hP], sc_big h h1.s2 h1.s1 h1.s0, by rw [h1.s9, h1.s8]; exact sc_bd h, hd₅⟩
  refine WP.seq (WP.mono (WP.with_rdwr (crypt_ok L ci)) fun s₆ ⟨co, rd₆, wr₆, _⟩ => ?_)
  have cf := co.frame
  rw [h1.s1, h1.s9, h1.s8] at cf
  have sv₆ : SavedAt s₆.mem (s₀.gpr .a6) s₀ :=
    ((h1.en.saved.frame tf (saved_taFrame L₀ hk₀)) : SavedAt s₄.mem (s₀.gpr .a6) s₀) |>.frame
      (hk₅.mem ▸ cf) (saved_crFrame L₀ bw₀ hd₅₀)
  have e31 : s₆.gpr .s0 = s₀.gpr .a6 := (co.env.fr _ (by decide)).trans h1.s0
  refine WP.mono (restore_ok e31 (sc_al h) (by have := co.env.perm.w; rw [h1.s0] at this; exact Covers.right this)
    sv₆ co.env.sp)
    fun s' ⟨ga, hm, _⟩ => ⟨ga, ?_⟩
  have hc : ciphOf s₅.mem (s₁.gpr .s2) = ctxCiph s₀.mem (s₀.gpr .a0)  := by
    rw [h1.s2, hk₅.mem, ciph_frame tf (ctx_taFrame L₀ hk₀)]; exact ciph_keep f₁ (ctx_saved L₀)
  have blk₅ : ∀ {d : Nat}, (d + 16 ≤ 16 ∨ 48 ≤ d ∧ d + 16 ≤ 80) →
      blockAt s₅.mem (s₀.gpr .a1 + BitVec.ofNat 64 d) = blockAt s₀.mem (s₀.gpr .a1 + BitVec.ofNat 64 d) :=
    fun hd => by
      rw [hk₅.mem, blockAt_frame tf (stp_taFrame L₀ hk₀ hd), blockAt_frame f₁ (stp_saved L₀ (by omega_arith))]
  have ctr₅ : ∀ {P : Nat}, Ctr s₀.mem (s₀.gpr .a1 + BitVec.ofNat 64 48) (s₀.gpr .a1 + BitVec.ofNat 64 64)
      (ctxCiph s₀.mem (s₀.gpr .a0)) icb P →
      Ctr s₅.mem (s₁.gpr .s1 + BitVec.ofNat 64 48) (s₁.gpr .s1 + BitVec.ofNat 64 64)
        (ciphOf s₅.mem (s₁.gpr .s2)) icb P := fun hc₀ => by
    rw [hc, h1.s1]
    exact hc₀.congr (blk₅ (d := 48) (.inr ⟨by decide, by decide⟩)) (blk₅ (d := 64) (.inr ⟨by decide, by decide⟩))
  have dat₅ : bytesAt s₅.mem (s₀.gpr .a4) (s₀.gpr .a5).toNat = bytesAt s₀.mem (s₀.gpr .a4) (s₀.gpr .a5).toNat := by
    have hlt := hd₁₀.ok.lt
    rw [hk₅.mem, bytesAt_frame tf (data_taFrame hd₁₀.ok h1.en.keeps.sp) (by omega_arith), bytesAt_frame f₁ (data_saved hd₁₀.ok) (by omega_arith)]
  have dat₁ : bytesAt s₁.mem (s₀.gpr .a4) (s₀.gpr .a5).toNat = bytesAt s₀.mem (s₀.gpr .a4) (s₀.gpr .a5).toNat :=
    bytesAt_frame f₁ (data_saved hd₁₀.ok) (by have := hd₁₀.ok.lt; omega_arith)
  refine ⟨fun hc₀ => ?_, fun hc₀ => ?_, fun hc₀ hab => ?_, ?_⟩
  · rw [hm]
    have := co.ctr (ctr₅ hc₀)
    rw [hc, h1.s1, h1.s8] at this
    exact this
  · rw [hm]
    have := co.out (ctr₅ hc₀)
    rw [hc, h1.s9, h1.s8, dat₅] at this
    exact this
  · simp only [hm, ↓reduceIte]
    have hab₁ : Absorbed s₁.mem (s₀.gpr .a1 + BitVec.ofNat 64 16) (s₀.gpr .a1 + BitVec.ofNat 64 32)
        (ctxH s₀.mem (s₀.gpr .a0)) (ghashInput a ct) :=
      hab.congr (blockAt_frame f₁ (stp_saved L₀ (by decide)))
        (bytesAt_frame f₁ (stp_saved L₀ (by omega_arith)) (by omega_arith))
    have := ta.abs (by rw [h1.s1]; exact hab₁)
    rw [h1.s1, h1.s9, h1.s8, dat₁] at this
    rw [← hk₅.mem] at this
    exact this.congr (blockAt_frame cf (stp_crFrame bs₀ hd₅₀ (by decide)))
      (bytesAt_frame cf (stp_crFrame bs₀ hd₅₀ (by omega_arith)) (by omega_arith))
  · rw [hm, blockAt_frame cf (by simpa using stp_crFrame bs₀ hd₅₀ (d := 0) (k := 16) (by decide))]
    simpa using blk₅ (d := 0) (.inl (by decide))

theorem streamEncrypt_wp {s₀ : State} (h : streamEncryptRISCV64.pre s₀) :
    WP isa streamEncrypt s₀ fun s' => abiPreserved s₀ s' ∧ streamEncryptRISCV64.post s₀ s' := by
  have h' : streamCryptPre s₀ := h
  have h₀ := enc_run h' 0 (a := List.replicate ((s₀.gpr .a2).toNat % 16) 0)
    (ct := List.replicate (s₀.gpr .a3).toNat 0) (by simp) (by simp)
  refine WP.mono (WP.forall_det (WP.mono h₀ fun _ hh => hh.1)
    (P := fun i : List Byte × List Byte × List Byte =>
      let ciph := ctxCiph s₀.mem (s₀.gpr .a0)
      let hh := ctxH s₀.mem (s₀.gpr .a0)
      StreamRepr s₀.mem (s₀.gpr .a1) ciph hh i.1 i.2.1 (gctr ciph (inc32 (j0 hh i.1)) i.2.2) ∧
        s₀.gpr .a2 = BitVec.ofNat 64 i.2.1.length ∧ (s₀.gpr .a3).toNat = i.2.2.length)
    fun i hi => enc_run h' (inc32 (j0 (ctxH s₀.mem (s₀.gpr .a0)) i.1)) (a := i.2.1)
      (ct := gctr (ctxCiph s₀.mem (s₀.gpr .a0)) (inc32 (j0 (ctxH s₀.mem (s₀.gpr .a0)) i.1)) i.2.2)
      (by rw [hi.2.1, toNat_mod16]) (by rw [Proof.Gcm.length_gctr]; exact hi.2.2))
    fun s' hh => ⟨hh.1, fun iv a p hs hl hp => ?_⟩
  obtain ⟨-, eo⟩ := hh.2 ⟨iv, a, p⟩ ⟨hs, hl, hp⟩
  rw [Proof.Gcm.streamRepr_iff] at hs
  obtain ⟨hj, hab, hct⟩ := hs
  have hl' : (gctr (ctxCiph s₀.mem (s₀.gpr .a0))
      (inc32 (j0 (ctxH s₀.mem (s₀.gpr .a0)) iv)) p).length = p.length := Proof.Gcm.length_gctr _ _ _
  have eo₁ := eo.ctr hct
  have eo₂ := eo.out hct
  have eo₃ := eo.abs hct hab
  simp only [Bool.false_eq_true, ite_false] at eo₃
  rw [hl'] at eo₁ eo₂ eo₃
  rw [← Proof.Gcm.gctr_append] at eo₃
  refine ⟨?_, ?_⟩
  · rw [Proof.Gcm.streamRepr_iff]
    refine ⟨eo.j.trans hj, eo₃, ?_⟩
    rw [Proof.Gcm.length_gctr, List.length_append, length_bytesAt]; exact eo₁
  · rw [eo₂, Proof.Gcm.gctr_append, List.drop_left' hl']

theorem streamDecrypt_wp {s₀ : State} (h : streamDecryptRISCV64.pre s₀) :
    WP isa streamDecrypt s₀ fun s' => abiPreserved s₀ s' ∧ streamDecryptRISCV64.post s₀ s' := by
  have h' : streamCryptPre s₀ := h
  have h₀ := dec_run h' 0 (a := List.replicate ((s₀.gpr .a2).toNat % 16) 0)
    (ct := List.replicate (s₀.gpr .a3).toNat 0) (by simp) (by simp)
  refine WP.mono (WP.forall_det (WP.mono h₀ fun _ hh => hh.1)
    (P := fun i : List Byte × List Byte × List Byte =>
      let ciph := ctxCiph s₀.mem (s₀.gpr .a0)
      let hh := ctxH s₀.mem (s₀.gpr .a0)
      StreamRepr s₀.mem (s₀.gpr .a1) ciph hh i.1 i.2.1 i.2.2 ∧
        s₀.gpr .a2 = BitVec.ofNat 64 i.2.1.length ∧ (s₀.gpr .a3).toNat = i.2.2.length)
    fun i hi => dec_run h' (inc32 (j0 (ctxH s₀.mem (s₀.gpr .a0)) i.1)) (a := i.2.1) (ct := i.2.2)
      (by rw [hi.2.1, toNat_mod16]) hi.2.2)
    fun s' hh => ⟨hh.1, fun iv a c hs hl hp => ?_⟩
  obtain ⟨-, eo⟩ := hh.2 ⟨iv, a, c⟩ ⟨hs, hl, hp⟩
  rw [Proof.Gcm.streamRepr_iff] at hs
  obtain ⟨hj, hab, hct⟩ := hs
  have eo₁ := eo.ctr hct
  have eo₂ := eo.out hct
  have eo₃ := eo.abs hct hab
  simp only [ite_true] at eo₃
  refine ⟨?_, ?_⟩
  · rw [Proof.Gcm.streamRepr_iff]
    refine ⟨eo.j.trans hj, eo₃, ?_⟩
    rw [List.length_append, length_bytesAt]; exact eo₁
  · rw [eo₂, Proof.Gcm.gctr_append, List.drop_left' (Proof.Gcm.length_gctr _ _ _)]

end VG.Proof.Sm4Gcm.RISCV64
