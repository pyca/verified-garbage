module

public import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Crypt
public import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamFinish
import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
import VerifiedGarbage.Proof.Gcm.Be64
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.Framework.RISCV64.Run
public import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamCrypt
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Tag
import VerifiedGarbage.Proof.AesGcm.RISCV64.Init
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps

/-! ### `Sm4Gcm.RISCV64.Tag`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on RISC-V: the tag (`tag o`)

Untrusted: everything here is checked by Lean. AES-GCM's `tag o`
(`Proof/AesGcm/RISCV64/Tag.lean`) with `vg_sm4_ctr32`: it absorbs the
lengths block of `s4` and `s6` bytes, copies the accumulator `S` to `W + o`
and XORs `CIPH_K(J₀)` into it, from the counter block `J₀` at the state
(`tag_ok`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.RISCV64

open VG VG.RISCV64 VG.Impl.Sm4Gcm.RISCV64
open VG.Impl.AesGcm.RISCV64 (mov lens scrO)
open VG.Proof.AesGcm.RISCV64 hiding CrIn CrMid CrOut crFrame ciphOf TailKs ctx_crFrame ciph_frame
  CtrCall CtrPost ctr_call ctr_rel tagFrame TagOut TagMid tagLens_ok tagArgs_ok ctrTag_mk tagCall_ok
  tag_ok
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom toBytes ofBytes)
open VG.Proof.Gcm (lensBlock)

/-- The regions `tag o` writes. -/
abbrev tagFrame (st w : Addr) (o : Nat) (sp : Addr) : List Region :=
  [⟨st, 32⟩, ⟨w + BitVec.ofNat 64 96, 16⟩, ⟨w + BitVec.ofNat 64 o, 16⟩, ⟨w + BitVec.ofNat 64 512, 256⟩,
    below sp 3248]

/-- After `tag o`, from `m₀`: the tag of the accumulator `Y` (before the
lengths block) and the counter block `J`. -/
structure TagOut (V : Reg → BitVec 64) (sp : Addr) (o : Nat) (H Y J : Block) (aLen cLen : Nat) (m₀ : Mem)
    (s : State) : Prop where
  env : Env V sp s
  out : bytesAt s.mem (V .s0 + BitVec.ofNat 64 o) 16 =
    toBytes (ghashFrom H Y [ofBytes (lensBlock aLen cLen)] ^^^ ciphOf m₀ (V .s2) J)
  frame : Frame (tagFrame (V .s1) (V .s0) o sp) m₀ s.mem

/-- After the lengths block: what the arguments of the call need. -/
structure TagMid (V : Reg → BitVec 64) (sp : Addr) (H Y J : Block) (aLen cLen : Nat) (m₀ : Mem)
    (s : State) : Prop where
  env : Env V sp s
  hY : blockAt s.mem (V .s1 + BitVec.ofNat 64 16) = ghashFrom H Y [ofBytes (lensBlock aLen cLen)]
  hJ : blockAt s.mem (V .s1) = J
  hc : ciphOf s.mem (V .s2) = ciphOf m₀ (V .s2)
  frame : Frame (tFrame (V .s1) (V .s0) 16 sp) m₀ s.mem

section
variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s1) (V .s0))
include L

/-- The lengths block absorbed, before the copy. -/
theorem tagLens_ok [VG.Proof.Gcm.RISCV64.GhashLaw] {H J : Block} {s : State} (he : Env V sp s)
    (hH : blockAt s.mem (V .s2 + BitVec.ofNat 64 240) = H) (hJ : blockAt s.mem (V .s1) = J) :
    WP isa (lens 16) s (TagMid V sp H (blockAt s.mem (V .s1 + BitVec.ofNat 64 16)) J
      (s.gpr .s4).toNat (s.gpr .s6).toNat s.mem) := by
  refine WP.mono (lens_ok L (.inr rfl) he hH) fun s₁ ⟨he₁, _, hY₁, _, f₁⟩ => ?_
  exact ⟨he₁, hY₁, by rw [blockAt_frame f₁ (j_tFrame L he.stk'), hJ], ciph_frame f₁ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.cs.sub_right (Lay.stSub (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact he.stk'.c), f₁⟩

/-- The accumulator copied to `W + o`, and the arguments of `vg_sm4_ctr32`. -/
theorem tagArgs_ok {o : Nat} (ho : o = 0 ∨ o = 112) {s : State} (he : Env V sp s) :
    WP isa (.block (tagArgs o)) s fun s' =>
      s'.mem = (s.mem.writeW (V .s0 + BitVec.ofNat 64 o) (s.mem.readW (V .s1 + BitVec.ofNat 64 16) 64)).writeW
        (V .s0 + BitVec.ofNat 64 (o + 8))
        ((s.mem.writeW (V .s0 + BitVec.ofNat 64 o) (s.mem.readW (V .s1 + BitVec.ofNat 64 16) 64)).readW
          (V .s1 + BitVec.ofNat 64 24) 64) ∧
      s'.gpr .a0 = V .s2 ∧ s'.gpr .a1 = V .s1 ∧ s'.gpr .a2 = V .s0 + BitVec.ofNat 64 o ∧
      s'.gpr .a3 = BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .t0 → r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → s'.gpr r = s.gpr r) ∧
      Keeps' s s' := by
  have h29 := he.s2; have h30 := he.s1; have h31 := he.s0
  have ho8 : o % 8 = 0 := by omega_using [ho]
  have hob : o + 16 ≤ 128 := by omega_using [ho]
  simp only [tagArgs]
  refine Steps.wp_ld (off := 16) (a := V .s1 + BitVec.ofNat 64 16) (by decide) (by rw [h30])
    (L.stal (by decide) (by decide)) (he.perm.stR (by decide)) fun s₁ u₁ => ?_
  refine Steps.wp_sd (off := o) (a := V .s0 + BitVec.ofNat 64 o) (by omega_using [ho])
    (by rw [u₁.other _ (by decide), h31]) (L.wal8 ho8 (by omega_using [ho]))
    (by rw [u₁.wr]; exact he.perm.wW (by omega_using [ho])) fun s₂ u₂ => ?_
  refine Steps.wp_ld (off := 24) (a := V .s1 + BitVec.ofNat 64 24) (by decide)
    (by rw [u₂.gpr, u₁.other _ (by decide), h30]) (L.stal (by decide) (by decide))
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact he.perm.stR (by decide)) fun s₃ u₃ => ?_
  refine Steps.wp_sd (off := o + 8) (a := V .s0 + BitVec.ofNat 64 (o + 8)) (by omega_using [ho])
    (by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h31]) (L.wal8 (by omega_using [ho]) (by omega_using [ho]))
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact he.perm.wW (by omega_using [ho])) fun s₄ u₄ => ?_
  have g : ∀ r, r ≠ .t0 → s₄.gpr r = s.gpr r := fun r hr => by
    rw [u₄.gpr, u₃.other _ hr, u₂.gpr, u₁.other _ hr]
  refine Steps.wp_mv fun s₅ u₅ => Steps.wp_mv fun s₆ u₆ =>
    Steps.wp_addi (imm := o) (by omega_using [ho]) fun s₇ u₇ => Steps.wp_li (imm := 1) (by decide) fun s₈ u₈ =>
    WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r h0 h1 h2 h3 h4 => by
      rw [u₈.other _ h4, u₇.other _ h3, u₆.other _ h2, u₅.other _ h1, g _ h0], ⟨?_, ?_, ?_⟩⟩
  · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.gpr, u₃.mem, u₂.mem, u₁.gpr, u₁.mem]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, g _ (by decide), h29]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), g _ (by decide), h30]
  · rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), g _ (by decide), h31]
  · rw [u₈.gpr]
  · rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]

/-- The arguments of `vg_sm4_ctr32` on the tag at `W + o`, with the counter block `J₀` at the state. -/
theorem ctrTag_mk (hb : Big V sp) {o : Nat} (ho : o = 0 ∨ o = 112) {s : State} (he : Env V sp s)
    (h3 : s.gpr .a0 = V .s2) (h5 : s.gpr .a1 = V .s1)
    (h6 : s.gpr .a2 = V .s0 + BitVec.ofNat 64 o) (h7 : s.gpr .a3 = BitVec.ofNat 64 1) :
    CtrCall s (V .s2) (V .s1) (V .s0 + BitVec.ofNat 64 o) 1 := by
  have hoW : o + 16 ≤ 16 ∨ (96 ≤ o ∧ o + 16 ≤ 2560) := by omega_using [ho]
  have hsp := he.sp
  refine ⟨h3, h5, h6, h7, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
  · exact (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by omega_using [ho]))
  · simpa using L.st_w (a := 0) (n := 16) (d := o) (k := 16) (by decide) hoW
  · have := L.cw; omega_using [this]
  · have := L.sw; omega_using [this]
  · have := L.ww
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_using [ho]),
      Nat.mod_eq_of_lt (by omega_using [ho, this])]; omega_using [ho, this]
  · rw [hsp]; exact he.stk'.al
  · rw [hsp]; exact hb.ge
  · rw [hsp]; exact hb.c.sub_right (Region.sub_prefix (by decide))
  · rw [hsp]; exact hb.st.sub_right (Region.sub_prefix (by decide))
  · rw [hsp]; exact hb.w.sub_right (Lay.wSub (by omega_using [ho]))
  · exact Covers.cons (covers_prefix he.perm.ctx (by decide)) (Covers.cons
      (covers_left (covers_prefix he.perm.st (by decide))) (Covers.cons (covers_left (he.perm.wC (by omega_using [ho])))
        Covers.nil))
  · exact Covers.cons (covers_prefix he.perm.st (by decide)) (Covers.cons (he.perm.wC (by omega_using [ho])) Covers.nil)

/-- The copy and the call of `vg_sm4_ctr32` on it. -/
theorem tagCall_ok (hb : Big V sp) {o : Nat} (ho : o = 0 ∨ o = 112) {H Y J : Block} {aLen cLen : Nat}
    {m₀ : Mem} {s : State} (h : TagMid V sp H Y J aLen cLen m₀ s) :
    WP isa (.seq (.block (tagArgs o)) ctrCall) s (TagOut V sp o H Y J aLen cLen m₀) := by
  have he := h.env
  have hoW : o + 16 ≤ 16 ∨ (96 ≤ o ∧ o + 16 ≤ 2560) := by omega_using [ho]
  refine WP.seq (WP.mono (tagArgs_ok L ho he) fun s₂ ⟨hm₂, a3, a4, a5, a6, hg₂, hk₂⟩ => ?_)
  rw [show V .s0 + BitVec.ofNat 64 (o + 8) = V .s0 + BitVec.ofNat 64 o + BitVec.ofNat 64 8 from
      (add_ofNat_assoc _ _ _).symm,
    show V .s1 + BitVec.ofNat 64 24 = V .s1 + BitVec.ofNat 64 16 + BitVec.ofNat 64 8 by
      rw [BitVec.add_assoc]; rfl] at hm₂
  have he₂ : Env V sp s₂ := he.keep (fun r hr => hg₂ r (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide) (by revert r; decide)) hk₂.sp hk₂.rd hk₂.wr
  have f₂ : Frame [⟨V .s0 + BitVec.ofNat 64 o, 16⟩] s.mem s₂.mem := by
    rw [hm₂]; exact Proof.Cmac.frame_store2 _ _ _
  have hT : bytesAt s₂.mem (V .s0 + BitVec.ofNat 64 o) 16 = bytesAt s.mem (V .s1 + BitVec.ofNat 64 16) 16 := by
    rw [hm₂, bytesAt_copy2 _ (by
      rw [add_ofNat_assoc]; exact (L.st_w (a := 24) (n := 8) (d := o) (k := 8) (by decide) (by omega_using [ho])).symm)]
  have dJo : (⟨V .s1, 16⟩ : Region).Disjoint ⟨V .s0 + BitVec.ofNat 64 o, 16⟩ := by
    simpa using L.st_w (a := 0) (n := 16) (d := o) (k := 16) (by decide) hoW
  have hJ₂ : blockAt s₂.mem (V .s1) = J := by
    rw [blockAt_frame f₂ fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dJo, h.hJ]
  have hc₂ : ciphOf s₂.mem (V .s2) = ciphOf m₀ (V .s2) := by
    rw [ciph_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.cw'.sub_right (Lay.wSub (by omega_using [ho]))), h.hc]
  have hcall := ctrTag_mk L hb ho he₂ a3 a4 a5 a6
  refine WP.mono (ctr_call hcall) fun s₃ g => ?_
  have gout := g.out; have gframe := g.frame
  rw [blocksAt_one, blocksAt_one, ctr32_single, List.cons.injEq] at gout
  rw [he₂.sp] at gframe
  refine ⟨he₂.of_saved g.saved g.sp g.rd g.wr, ?_, ?_⟩
  · rw [Proof.Cmac.bytesAt_blockAt, gout.1, hJ₂,
      show Spec.Sm4.gcmCipher (Spec.Sm4.scheduleAt s₂.mem (V .s2)) = ciphOf s₂.mem (V .s2) from rfl,
      hc₂, show blockAt s₂.mem (V .s0 + BitVec.ofNat 64 o) = blockAt s.mem (V .s1 + BitVec.ofNat 64 16)
        by rw [blockAt, blockAt, hT], h.hY]
  · have fA : Frame (tagFrame (V .s1) (V .s0) o sp) m₀ s.mem := h.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., by simpa using Offset.sub_base (V .s1) (show 16 + 16 ≤ 32 by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
      · exact ⟨⟨V .s0 + BitVec.ofNat 64 512, 256⟩, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, below_sub⟩
    refine (fA.trans (f₂.sub fun r hr => ?_)).trans (gframe.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩

/-- `tag o`, for `o` of 0 or 112. -/
theorem tag_ok [VG.Proof.Gcm.RISCV64.GhashLaw] (hb : Big V sp) {o : Nat} (ho : o = 0 ∨ o = 112) {H J : Block} {s : State} (he : Env V sp s)
    (hH : blockAt s.mem (V .s2 + BitVec.ofNat 64 240) = H) (hJ : blockAt s.mem (V .s1) = J) :
    WP isa (tag o) s (TagOut V sp o H (blockAt s.mem (V .s1 + BitVec.ofNat 64 16)) J
      (s.gpr .s4).toNat (s.gpr .s6).toNat s.mem) :=
  WP.seq (WP.mono (tagLens_ok L he hH hJ) fun _ hm => tagCall_ok L hb ho hm)

end

end VG.Proof.Sm4Gcm.RISCV64

end

end

/-! ### `Sm4Gcm.RISCV64.StreamCrypt`, which this module and modules that import it used -/

section

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
  obtain e3 : s₁.gpr .a0 = s₀.gpr .a0 := hg _ (by decide)
  obtain e4 : s₁.gpr .a1 = s₀.gpr .a1 := hg _ (by decide)
  obtain e5 : s₁.gpr .a2 = s₀.gpr .a2 := hg _ (by decide)
  obtain e6 : s₁.gpr .a3 = s₀.gpr .a3 := hg _ (by decide)
  obtain e7 : s₁.gpr .a4 = s₀.gpr .a4 := hg _ (by decide)
  obtain e8 : s₁.gpr .a5 = s₀.gpr .a5 := hg _ (by decide)
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

/-- The context, the state and `W` are apart from the 3248 bytes below the stack pointer. -/
theorem sc_b3 : (below s₀.sp 3248).Disjoint ⟨s₀.gpr .a0, 256⟩ ∧ (below s₀.sp 3248).Disjoint ⟨s₀.gpr .a1, 80⟩ ∧
    (below s₀.sp 3248).Disjoint ⟨s₀.gpr .a6, 2560⟩ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hk, -⟩ := h
  exact ⟨hk.buf3 (by simp), hk.buf3 (by simp), hk.buf3 (by simp)⟩

/-- The data are apart from the 3248 bytes below the stack pointer. -/
theorem sc_bd : (below s₀.sp 3248).Disjoint ⟨s₀.gpr .a4, (s₀.gpr .a5).toNat⟩ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hk, -⟩ := h
  exact hk.buf3 (by simp)

theorem sc_W : Covers [⟨s₀.gpr .a6, 2560⟩] s₀.wr := by
  rw [h.2.1]; exact covers_mem (by simp)

/-- The environment after the entry. -/
theorem sc_env {s₁ : State} (h1 : SC1 s₀ s₁) : Env s₁.gpr s₀.sp s₁ := by
  obtain hk := sc_stk h
  obtain ⟨hrd, hwr, -⟩ := h
  obtain perm : Perm (s₀.gpr .a0) (s₀.gpr .a1) (s₀.gpr .a6) s₁ :=
    (⟨covers_mem (by rw [hrd]; simp), covers_mem (by rw [hwr]; simp), covers_mem (by rw [hwr]; simp)⟩ :
      Perm (s₀.gpr .a0) (s₀.gpr .a1) (s₀.gpr .a6) s₀).of_eq h1.en.keeps.rd h1.en.keeps.wr
  exact ⟨fun _ _ => rfl, h1.en.keeps.sp, by rw [h1.s2, h1.s1, h1.s0]; exact perm,
    by rw [h1.s2, h1.s1, h1.s0, h1.en.keeps.sp]; exact hk⟩

/-- The data, as `crypt` needs it. -/
theorem sc_dataW {s : State} (hwr' : s.wr = s₀.wr) (hsp : s.sp = s₀.sp) :
    DataW (s₀.gpr .a0) (s₀.gpr .a1) (s₀.gpr .a6) s (s₀.gpr .a4) (s₀.gpr .a5).toNat := by
  obtain ⟨-, hwr, -, dcd, -, dsd, -, ddw, -, -, fd, -, hk, -⟩ := h
  obtain hD : Covers [⟨s₀.gpr .a4, (s₀.gpr .a5).toNat⟩] s.wr := by rw [hwr', hwr]; exact covers_mem (by simp)
  exact ⟨⟨covers_left hD, (s₀.gpr .a5).isLt, fd, dsd.symm, ddw, by rw [hsp]; exact hk.buf (by simp)⟩, hD, dcd⟩

end

section
variable {c st w : Addr} (L : Lay c st w)
include L

omit L in
theorem stp_crFrame {sp : Addr} (hbs : (below sp 3248).Disjoint ⟨st, 80⟩) {s : State} {D : Addr} {n : Nat}
    (hd : DataW c st w s D n) {d k : Nat} (h1 : d + k ≤ 48) :
    ∀ r ∈ crFrame st sp D n, (⟨st + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hd.ok.st.sub_right (Lay.stSub (by omega_arith))).symm
  · exact Lay.st_st (.inl h1) (by omega_arith) (by decide)
  · exact (hbs.sub_right (Lay.stSub (by omega_arith))).symm

theorem saved_crFrame {sp : Addr} (hbw : (below sp 3248).Disjoint ⟨w, 2560⟩) {s : State} {D : Addr} {n : Nat}
    (hd : DataW c st w s D n) : ∀ r ∈ crFrame st sp D n, (savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hd.ok.w.sub_right (Lay.wSub (by decide))).symm
  · exact L.saved_st (by decide)
  · exact (hbw.sub_right (Lay.wSub (by decide))).symm

theorem ctx_crFrame' {sp : Addr} (hbc : (below sp 3248).Disjoint ⟨c, 256⟩) {s : State} {D : Addr} {n : Nat}
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

theorem enc_run [VG.Proof.Gcm.RISCV64.GhashLaw] {s₀ : State} (h : streamCryptPre s₀) (icb : Block) {a ct : List Byte}
    (ha : a.length % 16 = (s₀.gpr .a2).toNat % 16) (hP : (s₀.gpr .a3).toNat = ct.length) :
    WP isa streamEncrypt s₀ fun s' => abiPreserved s₀ s' ∧ EncOut s₀ icb a ct false s' := by
  obtain L₀ := scLay h
  obtain hk₀ := sc_stk h
  obtain ⟨bc₀, bs₀, bw₀⟩ := sc_b3 h
  refine WP.seq (WP.block_append (WP.mono (sc1_wp (sc_W h) (sc_al h)) fun s₁ h1 => ?_))
  obtain he₁ := sc_env h h1
  obtain L := L₀.v h1.s2 h1.s1 h1.s0
  refine WP.mono textArgs_ok fun s₂ ⟨h24, h25, h26, hg₂, hk₂⟩ => ?_
  obtain he₂ : Env s₁.gpr s₀.sp s₂ := he₁.keep (fun r hr => hg₂ r (by revert r; decide) (by revert r; decide)
    (by revert r; decide)) hk₂.sp hk₂.rd hk₂.wr
  obtain hd₂₀ := sc_dataW h (s := s₂) (hk₂.wr.trans h1.en.keeps.wr) (hk₂.sp.trans h1.en.keeps.sp)
  obtain hd₂ : DataW (s₁.gpr .s2) (s₁.gpr .s1) (s₁.gpr .s0) s₂ (s₁.gpr .s9) (s₁.gpr .s8).toNat := by
    rw [h1.s2, h1.s1, h1.s0, h1.s9, h1.s8]; exact hd₂₀
  obtain ci : CrIn s₁.gpr s₀.sp icb ct.length (s₁.gpr .s9) (s₁.gpr .s8).toNat s₂ :=
    ⟨he₂, h24, by rw [h25, BitVec.ofNat_toNat, BitVec.setWidth_eq], by rw [h26, h1.s11, hP],
      sc_big h h1.s2 h1.s1 h1.s0, by rw [h1.s9, h1.s8]; exact sc_bd h, hd₂⟩
  refine WP.seq (WP.mono (WP.with_rdwr (crypt_ok L ci)) fun s₃ ⟨co, rd₃, wr₃, sp₃⟩ => ?_)
  obtain hd₃ := hd₂.ok.of_eq rd₃ wr₃ sp₃
  obtain f₂ : Frame [savedR (s₀.gpr .a6)] s₀.mem s₂.mem := by rw [hk₂.mem]; exact h1.en.frame
  have cf := co.frame
  rw [h1.s1, h1.s9, h1.s8] at cf
  obtain hH₃ : blockAt s₃.mem (s₁.gpr .s2 + BitVec.ofNat 64 240) = ctxH s₀.mem (s₀.gpr .a0) := by
    rw [h1.s2, blockAt_frame cf (fun r hr => (ctx_crFrame' L₀ bc₀ hd₂₀ r hr).sub_left (Lay.ctxSub (by decide))),
      ctxH_keep f₂ (ctx_saved L₀)]
  refine WP.seq (WP.mono (WP.with_rdwr (textAbsorb_ok L (a := a) (ct := ct) co.env hH₃ hd₃ (by rw [h1.s10]; exact ha)
    (by rw [h1.s11]; exact hP))) fun s₄ ⟨ta, rd₄, wr₄, _⟩ => ?_)
  have tf := ta.frame
  rw [h1.s1, h1.s0] at tf
  obtain sv₄ : SavedAt s₄.mem (s₀.gpr .a6) s₀ :=
    (((hk₂.mem ▸ h1.en.saved : SavedAt s₂.mem (s₀.gpr .a6) s₀)).frame cf (saved_crFrame L₀ bw₀ hd₂₀)).frame tf
      (saved_taFrame L₀ hk₀)
  obtain e31 : s₄.gpr .s0 = s₀.gpr .a6 := (ta.env.fr _ (by decide)).trans h1.s0
  refine WP.mono (restore_ok e31 (sc_al h) (by have := ta.env.perm.w; rw [h1.s0] at this; exact Covers.right this)
    sv₄ ta.env.sp)
    fun s' ⟨ga, hm, _⟩ => ⟨ga, ?_⟩
  obtain hc : ciphOf s₂.mem (s₁.gpr .s2) = ctxCiph s₀.mem (s₀.gpr .a0)  := by
    rw [h1.s2]; exact ciph_keep f₂ (ctx_saved L₀)
  obtain ctr₂ : ∀ {P : Nat}, Ctr s₀.mem (s₀.gpr .a1 + BitVec.ofNat 64 48) (s₀.gpr .a1 + BitVec.ofNat 64 64)
      (ctxCiph s₀.mem (s₀.gpr .a0)) icb P →
      Ctr s₂.mem (s₁.gpr .s1 + BitVec.ofNat 64 48) (s₁.gpr .s1 + BitVec.ofNat 64 64)
        (ciphOf s₂.mem (s₁.gpr .s2)) icb P := fun hc₀ => by
    rw [hc, h1.s1]
    exact hc₀.congr (blockAt_frame f₂ (stp_saved L₀ (by decide))) (blockAt_frame f₂ (stp_saved L₀ (by decide)))
  obtain dat₂ : bytesAt s₂.mem (s₀.gpr .a4) (s₀.gpr .a5).toNat = bytesAt s₀.mem (s₀.gpr .a4) (s₀.gpr .a5).toNat :=
    bytesAt_frame f₂ (data_saved hd₂₀.ok) (by have := hd₂₀.ok.lt; omega_arith)
  obtain out₃ : Ctr s₀.mem (s₀.gpr .a1 + BitVec.ofNat 64 48) (s₀.gpr .a1 + BitVec.ofNat 64 64)
      (ctxCiph s₀.mem (s₀.gpr .a0)) icb ct.length →
      bytesAt s₃.mem (s₀.gpr .a4) (s₀.gpr .a5).toNat =
        xorKs (ctxCiph s₀.mem (s₀.gpr .a0)) icb ct.length (bytesAt s₀.mem (s₀.gpr .a4) (s₀.gpr .a5).toNat) :=
    fun hc₀ => by
      have := co.out (ctr₂ hc₀)
      rw [hc, h1.s9, h1.s8, dat₂] at this
      exact this
  obtain hd₃₀ : DataOk (s₀.gpr .a1) (s₀.gpr .a6) s₃ (s₀.gpr .a4) (s₀.gpr .a5).toNat := hd₂₀.ok.of_eq rd₃ wr₃ sp₃
  refine ⟨fun hc₀ => ?_, fun hc₀ => ?_, fun hc₀ hab => ?_, ?_⟩
  · rw [hm]
    have := co.ctr (ctr₂ hc₀)
    rw [hc, h1.s1, h1.s8] at this
    exact this.congr (blockAt_frame tf (stp_taFrame L₀ hk₀ (.inr ⟨by decide, by decide⟩)))
      (blockAt_frame tf (stp_taFrame L₀ hk₀ (.inr ⟨by decide, by decide⟩)))
  · rw [hm, bytesAt_frame tf (data_taFrame hd₃₀ (sp₃.trans (hk₂.sp.trans h1.en.keeps.sp))) (by have := hd₃₀.lt; omega_arith)]
    exact out₃ hc₀
  · rw [hm]
    obtain hb := Nat.mod_lt (ghashInput a ct).length (show 16 > 0 by decide)
    obtain hab₃ : Absorbed s₃.mem (s₀.gpr .a1 + BitVec.ofNat 64 16) (s₀.gpr .a1 + BitVec.ofNat 64 32)
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

theorem dec_run [VG.Proof.Gcm.RISCV64.GhashLaw] {s₀ : State} (h : streamCryptPre s₀) (icb : Block) {a ct : List Byte}
    (ha : a.length % 16 = (s₀.gpr .a2).toNat % 16) (hP : (s₀.gpr .a3).toNat = ct.length) :
    WP isa streamDecrypt s₀ fun s' => abiPreserved s₀ s' ∧ EncOut s₀ icb a ct true s' := by
  obtain L₀ := scLay h
  obtain hk₀ := sc_stk h
  obtain ⟨-, bs₀, bw₀⟩ := sc_b3 h
  refine WP.seq (WP.mono (sc1_wp (sc_W h) (sc_al h)) fun s₁ h1 => ?_)
  obtain he₁ := sc_env h h1
  obtain L := L₀.v h1.s2 h1.s1 h1.s0
  have f₁ : Frame [savedR (s₀.gpr .a6)] s₀.mem s₁.mem := h1.en.frame
  obtain hd₁₀ := sc_dataW h (s := s₁) h1.en.keeps.wr h1.en.keeps.sp
  obtain hd₁ : DataOk (s₁.gpr .s1) (s₁.gpr .s0) s₁ (s₁.gpr .s9) (s₁.gpr .s8).toNat := by
    rw [h1.s1, h1.s0, h1.s9, h1.s8]; exact hd₁₀.ok
  obtain hH₁ : blockAt s₁.mem (s₁.gpr .s2 + BitVec.ofNat 64 240) = ctxH s₀.mem (s₀.gpr .a0) := by
    rw [h1.s2]; exact ctxH_keep f₁ (ctx_saved L₀)
  refine WP.seq (WP.mono (WP.with_rdwr (textAbsorb_ok L (a := a) (ct := ct) he₁ hH₁ hd₁
    (by rw [h1.s10]; exact ha) (by rw [h1.s11]; exact hP))) fun s₄ ⟨ta, rd₄, wr₄, sp₄⟩ => ?_)
  have tf := ta.frame
  rw [h1.s1, h1.s0] at tf
  refine WP.seq (WP.mono textArgs_ok fun s₅ ⟨h24, h25, h26, hg₅, hk₅⟩ => ?_)
  obtain he₅ : Env s₁.gpr s₀.sp s₅ := ta.env.keep (fun r hr => hg₅ r (by revert r; decide) (by revert r; decide)
    (by revert r; decide)) hk₅.sp hk₅.rd hk₅.wr
  obtain hd₅₀ := sc_dataW h (s := s₅) (hk₅.wr.trans (wr₄.trans h1.en.keeps.wr))
    (hk₅.sp.trans (sp₄.trans h1.en.keeps.sp))
  obtain hd₅ : DataW (s₁.gpr .s2) (s₁.gpr .s1) (s₁.gpr .s0) s₅ (s₁.gpr .s9) (s₁.gpr .s8).toNat := by
    rw [h1.s2, h1.s1, h1.s0, h1.s9, h1.s8]; exact hd₅₀
  obtain e20 := ta.env.fr .s9 (by decide)
  obtain e19 := ta.env.fr .s8 (by decide)
  obtain e23 := ta.env.fr .s11 (by decide)
  obtain ci : CrIn s₁.gpr s₀.sp icb ct.length (s₁.gpr .s9) (s₁.gpr .s8).toNat s₅ :=
    ⟨he₅, by rw [h24, e20], by rw [h25, e19, BitVec.ofNat_toNat, BitVec.setWidth_eq],
      by rw [h26, e23, h1.s11, hP], sc_big h h1.s2 h1.s1 h1.s0, by rw [h1.s9, h1.s8]; exact sc_bd h, hd₅⟩
  refine WP.seq (WP.mono (WP.with_rdwr (crypt_ok L ci)) fun s₆ ⟨co, rd₆, wr₆, _⟩ => ?_)
  have cf := co.frame
  rw [h1.s1, h1.s9, h1.s8] at cf
  obtain sv₆ : SavedAt s₆.mem (s₀.gpr .a6) s₀ :=
    ((h1.en.saved.frame tf (saved_taFrame L₀ hk₀)) : SavedAt s₄.mem (s₀.gpr .a6) s₀) |>.frame
      (hk₅.mem ▸ cf) (saved_crFrame L₀ bw₀ hd₅₀)
  obtain e31 : s₆.gpr .s0 = s₀.gpr .a6 := (co.env.fr _ (by decide)).trans h1.s0
  refine WP.mono (restore_ok e31 (sc_al h) (by have := co.env.perm.w; rw [h1.s0] at this; exact Covers.right this)
    sv₆ co.env.sp)
    fun s' ⟨ga, hm, _⟩ => ⟨ga, ?_⟩
  obtain hc : ciphOf s₅.mem (s₁.gpr .s2) = ctxCiph s₀.mem (s₀.gpr .a0)  := by
    rw [h1.s2, hk₅.mem, ciph_frame tf (ctx_taFrame L₀ hk₀)]; exact ciph_keep f₁ (ctx_saved L₀)
  obtain blk₅ : ∀ {d : Nat}, (d + 16 ≤ 16 ∨ 48 ≤ d ∧ d + 16 ≤ 80) →
      blockAt s₅.mem (s₀.gpr .a1 + BitVec.ofNat 64 d) = blockAt s₀.mem (s₀.gpr .a1 + BitVec.ofNat 64 d) :=
    fun hd => by
      rw [hk₅.mem, blockAt_frame tf (stp_taFrame L₀ hk₀ hd), blockAt_frame f₁ (stp_saved L₀ (by omega_arith))]
  obtain ctr₅ : ∀ {P : Nat}, Ctr s₀.mem (s₀.gpr .a1 + BitVec.ofNat 64 48) (s₀.gpr .a1 + BitVec.ofNat 64 64)
      (ctxCiph s₀.mem (s₀.gpr .a0)) icb P →
      Ctr s₅.mem (s₁.gpr .s1 + BitVec.ofNat 64 48) (s₁.gpr .s1 + BitVec.ofNat 64 64)
        (ciphOf s₅.mem (s₁.gpr .s2)) icb P := fun hc₀ => by
    rw [hc, h1.s1]
    exact hc₀.congr (blk₅ (d := 48) (.inr ⟨by decide, by decide⟩)) (blk₅ (d := 64) (.inr ⟨by decide, by decide⟩))
  obtain dat₅ : bytesAt s₅.mem (s₀.gpr .a4) (s₀.gpr .a5).toNat = bytesAt s₀.mem (s₀.gpr .a4) (s₀.gpr .a5).toNat := by
    have hlt := hd₁₀.ok.lt
    rw [hk₅.mem, bytesAt_frame tf (data_taFrame hd₁₀.ok h1.en.keeps.sp) (by omega_arith), bytesAt_frame f₁ (data_saved hd₁₀.ok) (by omega_arith)]
  obtain dat₁ : bytesAt s₁.mem (s₀.gpr .a4) (s₀.gpr .a5).toNat = bytesAt s₀.mem (s₀.gpr .a4) (s₀.gpr .a5).toNat :=
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
    obtain hab₁ : Absorbed s₁.mem (s₀.gpr .a1 + BitVec.ofNat 64 16) (s₀.gpr .a1 + BitVec.ofNat 64 32)
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

theorem streamEncrypt_wp [VG.Proof.Gcm.RISCV64.GhashLaw] {s₀ : State} (h : streamEncryptRISCV64.pre s₀) :
    WP isa streamEncrypt s₀ fun s' => abiPreserved s₀ s' ∧ streamEncryptRISCV64.post s₀ s' := by
  have h' : streamCryptPre s₀ := h
  obtain h₀ := enc_run h' 0 (a := List.replicate ((s₀.gpr .a2).toNat % 16) 0)
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
  obtain hl' : (gctr (ctxCiph s₀.mem (s₀.gpr .a0))
      (inc32 (j0 (ctxH s₀.mem (s₀.gpr .a0)) iv)) p).length = p.length := Proof.Gcm.length_gctr _ _ _
  obtain eo₁ := eo.ctr hct
  obtain eo₂ := eo.out hct
  obtain eo₃ := eo.abs hct hab
  simp only [Bool.false_eq_true, ite_false] at eo₃
  rw [hl'] at eo₁ eo₂ eo₃
  rw [← Proof.Gcm.gctr_append] at eo₃
  refine ⟨?_, ?_⟩
  · rw [Proof.Gcm.streamRepr_iff]
    refine ⟨eo.j.trans hj, eo₃, ?_⟩
    rw [Proof.Gcm.length_gctr, List.length_append, length_bytesAt]; exact eo₁
  · rw [eo₂, Proof.Gcm.gctr_append, List.drop_left' hl']

theorem streamDecrypt_wp [VG.Proof.Gcm.RISCV64.GhashLaw] {s₀ : State} (h : streamDecryptRISCV64.pre s₀) :
    WP isa streamDecrypt s₀ fun s' => abiPreserved s₀ s' ∧ streamDecryptRISCV64.post s₀ s' := by
  have h' : streamCryptPre s₀ := h
  obtain h₀ := dec_run h' 0 (a := List.replicate ((s₀.gpr .a2).toNat % 16) 0)
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
  obtain eo₁ := eo.ctr hct
  obtain eo₂ := eo.out hct
  obtain eo₃ := eo.abs hct hab
  simp only [ite_true] at eo₃
  refine ⟨?_, ?_⟩
  · rw [Proof.Gcm.streamRepr_iff]
    refine ⟨eo.j.trans hj, eo₃, ?_⟩
    rw [List.length_append, length_bytesAt]; exact eo₁
  · rw [eo₂, Proof.Gcm.gctr_append, List.drop_left' (Proof.Gcm.length_gctr _ _ _)]

end VG.Proof.Sm4Gcm.RISCV64

end

end

/-! ### `Sm4Gcm.RISCV64.FinTag`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on RISC-V: the tag after the last piece (`finTag o`)

Untrusted: everything here is checked by Lean. AES-GCM's `finTag o`
(`Proof/AesGcm/RISCV64/StreamFinish.lean`) with SM4's `tag o`: it pads and absorbs
the buffered bytes (`flush`), then puts the tag into `W + o` (`finTag_ok`).
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.RISCV64

open VG VG.RISCV64 VG.Impl.Sm4Gcm.RISCV64
open VG.Impl.AesGcm.RISCV64 (mov flush)
open VG.Proof.AesGcm.RISCV64 hiding CrIn CrMid CrOut crFrame ciphOf TailKs ctx_crFrame ciph_frame
  CtrCall CtrPost ctr_call ctr_rel tagFrame TagOut TagMid tagLens_ok tagArgs_ok ctrTag_mk tagCall_ok
  tag_ok tFrame_sub t_tagFrame FinOut finTag_ok
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput ghash ghashFrom blocks zeros padLen toBytes ofBytes)
open VG.Proof.Gcm (Absorbed lensBlock padded)

/-- `tFrame` is within `tagFrame`. -/
theorem tFrame_sub {st w sp : Addr} {o : Nat} :
    ∀ r ∈ tFrame st w 16 sp, ∃ r' ∈ tagFrame st w o sp, Region.Sub r r' := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., by simpa using Offset.sub_base st (show 16 + 16 ≤ 32 by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
  · exact ⟨⟨w + BitVec.ofNat 64 512, 256⟩, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, below_sub⟩

theorem t_tagFrame {st w sp : Addr} {o : Nat} {m m' : Mem} (h : Frame (tFrame st w 16 sp) m m') :
    Frame (tagFrame st w o sp) m m' := h.sub tFrame_sub

/-- After `finTag o`, from `m₀`. -/
structure FinOut (V : Reg → BitVec 64) (sp : Addr) (o : Nat) (H : Block) (a ct : List Byte) (m₀ : Mem)
    (s : State) : Prop where
  env : Env V sp s
  out : Absorbed m₀ (V .s1 + BitVec.ofNat 64 16) (V .s1 + BitVec.ofNat 64 32) H (ghashInput a ct) →
    bytesAt s.mem (V .s0 + BitVec.ofNat 64 o) 16 =
      toBytes (ghashFrom H (ghash H (blocks (padded a ct))) [ofBytes (lensBlock (V .s10).toNat ct.length)]
        ^^^ ciphOf m₀ (V .s2) (blockAt m₀ (V .s1)))
  frame : Frame (tagFrame (V .s1) (V .s0) o sp) m₀ s.mem

section
variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s1) (V .s0))
include L

theorem finTag_ok [VG.Proof.Gcm.RISCV64.GhashLaw] (hb : Big V sp) {o : Nat} (ho : o = 0 ∨ o = 112) {H : Block} {a ct : List Byte}
    {s : State} (he : Env V sp s)
    (hH : blockAt s.mem (V .s2 + BitVec.ofNat 64 240) = H)
    (ha : a.length % 16 = (V .s10).toNat % 16) (hP : (V .s11).toNat = ct.length) :
    WP isa (finTag o) s (FinOut V sp o H a ct s.mem) := by
  have h22 := he.fr .s10 (by decide)
  have h23 := he.fr .s11 (by decide)
  -- `s6`: the length of the buffered bytes, modulo 16
  have mid : WP isa (.ite (.zero .s11) (.block [.logicImm .and .s6 .s10 15])
      (.block [.logicImm .and .s6 .s11 15])) s fun s₂ =>
      s₂.gpr .s6 = BitVec.ofNat 64 ((ghashInput a ct).length % 16) ∧
        (∀ r, r ≠ .s6 → s₂.gpr r = s.gpr r) ∧ Keeps s s₂ := by
    refine WP.ite _ (eval_zero (he.ofNat (r := .s11) (by decide)) (V .s11).isLt) (fun ht => ?_) (fun hf => ?_)
    · have hc : ct = [] := List.eq_nil_of_length_eq_zero (by rw [← hP]; simpa using ht)
      have e : (ghashInput a ct).length % 16 = (V .s10).toNat % 16 := by
        rw [hc, Proof.Gcm.ghashInput_nil, ha]
      have hand := and15 (V .s10)
      rw [e]
      crun [Int.reduceNatCast', h22, hand]
      exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl⟩⟩
    · have hc : ct ≠ [] := fun e => by subst e; simp only [List.length_nil] at hP; simp [hP] at hf
      have e : (ghashInput a ct).length % 16 = (V .s11).toNat % 16 := by
        rw [Proof.Gcm.ghashInput_of_ne hc, List.length_append, List.length_append, Proof.Gcm.length_zeros, hP]
        have := Proof.Gcm.length_pad_mod a.length; omega_using [this]
      have hand := and15 (V .s11)
      rw [e]
      crun [Int.reduceNatCast', h23, hand]
      exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.mono mid fun s₂ ⟨h26₂, hg₂, hk₂⟩ => ?_)
  have he₂ := he.keep (fun r hr => hg₂ r (by revert r; decide)) hk₂.sp hk₂.rd hk₂.wr
  refine WP.seq (WP.mono (flush_ok L (yo := 16) (.inr rfl) (x := ghashInput a ct) (H := H)
    ⟨he₂, by rw [hk₂.mem]; exact hH⟩ h26₂) fun s₄ hfl => ?_)
  have hf₄ := hfl.frame
  rw [hk₂.mem] at hf₄
  -- the lengths
  have h₅ : WP isa (.block [mov .s4 .s10, mov .s6 .s11]) s₄ fun s₅ =>
      s₅.gpr .s4 = V .s10 ∧ s₅.gpr .s6 = V .s11 ∧ (∀ r, r ≠ .s4 → r ≠ .s6 → s₅.gpr r = s₄.gpr r) ∧
        Keeps s₄ s₅ := by
    have e22 := hfl.env.fr .s10 (by decide)
    have e23 := hfl.env.fr .s11 (by decide)
    crun [Int.reduceNatCast', mov, e22, e23]
    exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.mono h₅ fun s₅ ⟨h24₅, h26₅, hg₅, hk₅⟩ => ?_)
  have he₅ := hfl.env.keep (fun r hr => hg₅ r (by revert r; decide) (by revert r; decide)) hk₅.sp hk₅.rd hk₅.wr
  refine WP.mono (tag_ok L hb ho he₅ (H := H) (by rw [hk₅.mem]; exact hfl.hH) rfl) fun s₆ tg => ?_
  rw [h24₅, h26₅, hP, hk₅.mem] at tg
  refine ⟨tg.env, fun hab => ?_, (t_tagFrame hf₄).trans tg.frame⟩
  rw [tg.out]
  have hw := (hfl.abs (by rw [hk₂.mem]; exact hab)).whole_eq (by
    simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _)
  rw [show ghashInput a ct ++ zeros (padLen (ghashInput a ct).length) = padded a ct from rfl] at hw
  rw [hw, ciph_frame hf₄ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.cs.sub_right (Lay.stSub (by decide))
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact he.stk'.c),
    blockAt_frame hf₄ (j_tFrame L he.stk')]

end

end VG.Proof.Sm4Gcm.RISCV64

end

end

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

theorem fin_bw : (below s₀.sp 3248).Disjoint ⟨s₀.gpr .a5, 2560⟩ := by
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

theorem saved_tagFrame {sp : Addr} (hbw : (below sp 3248).Disjoint ⟨w, 2560⟩) {o : Nat} (ho : o = 0 ∨ o = 112) :
    ∀ r ∈ tagFrame st w o sp, (savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using L.saved_st (d := 0) (k := 32) (by decide)
  · exact saved_w (by decide) (.inl (by decide))
  · exact saved_w (by omega_using [ho]) (.inl (by omega_using [ho]))
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
      (bytesAt_frame hf₀ (dS (d := 32) (k := (ghashInput a ct).length % 16) (by omega_using [])) (by omega_using []))
  rw [hf.out hab₀,
    h29, ciph_keep hf₀ hdc, h30,
    blockAt_frame hf₀ (by simpa using dS (d := 0) (k := 16) (by decide)), hj,
    h22, toNat_of_eq hl, lensBlock_mod, Proof.Gcm.fullTag_eq]

theorem streamFinish_wp [VG.Proof.Gcm.RISCV64.GhashLaw] {s₀ : State} (h : streamFinishRISCV64.pre s₀) :
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
