module
public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Crypt
public import VerifiedGarbage.Proof.AesGcm.X86_64.StreamText
import VerifiedGarbage.Proof.Gcm.Compose

import VerifiedGarbage.Proof.Sm4Gcm.X86_64.CryptOk
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Fn
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
import VerifiedGarbage.Proof.AesGcm.X86_64.Flush
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Fn
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Gcm.Ctr
public import VerifiedGarbage.Proof.Gcm.Stream

/-!
# SM4-GCM on x86-64: the text of `stream_encrypt` and `stream_decrypt`

Untrusted: everything here is checked by Lean. `streamText enc` pads the
additional data first if there is no text yet (AES-GCM's `firstFlush`), then
encrypts the data and absorbs the ciphertext (`enc`), or absorbs the
ciphertext and decrypts it, with `crypt` and AES-GCM's `absorb`, as AES-GCM's
does for fewer than 256 bytes (`Proof/AesGcm/X86_64/StreamText.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Sm4Gcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm tlenO alenO streamLoad partWith firstFlush absorb)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt zeros padLen ghashInput)
open VG.Proof.Gcm (Absorbed Ctr xorKs)
open VG.Proof.AesGcm.X86_64 (GcmImpl Lay Env DataOk absFrame tFrame AbsIn AbsOut FlOut absorb_ok flush_ok
  load_ok load_env ctext ctext_append length_ctext ctext_nil bytesAt_zero abs_frame ctr_frame test_ok eval_e
  bytesAt_frame blockAt_frame and15 imm_eq and_self_beq toNat_mod16 data_absFrame length_bytesAt bytesAt_add
  WP.with_rdwr)

/-- What `streamText` writes. -/
abbrev stFrame (St W SP D : Addr) (n : Nat) : List Region :=
  [⟨St + BitVec.ofNat 64 16, 64⟩, ⟨D, n⟩, ⟨W + BitVec.ofNat 64 96, 16⟩, ⟨W + BitVec.ofNat 64 512, 256⟩,
    below SP stkN]

theorem crFrame_st {St W SP D : Addr} {n : Nat} {m m' : Mem} (hf : Frame (crFrame St SP D n) m m') :
    Frame (stFrame St W SP D n) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨D, n⟩, by simp, fun _ h => h⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨below SP stkN, by simp, fun _ h => h⟩

theorem absFrame_st {St W SP D : Addr} {n : Nat} {m m' : Mem} (hf : Frame (absFrame St W SP 16) m m') :
    Frame (stFrame St W SP D n) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨W + BitVec.ofNat 64 512, 256⟩, by simp, fun _ h => h⟩
    · exact ⟨below SP stkN, by simp, below8_stk SP⟩

theorem tFrame_st {St W SP D : Addr} {n : Nat} {m m' : Mem} (hf : Frame (tFrame St W SP 16) m m') :
    Frame (stFrame St W SP D n) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨W + BitVec.ofNat 64 96, 16⟩, by simp, fun _ h => h⟩
    · exact ⟨⟨W + BitVec.ofNat 64 512, 256⟩, by simp, fun _ h => h⟩
    · exact ⟨below SP stkN, by simp, below8_stk SP⟩

section
variable {Ctx St W SP : Addr} (L : Lay4 Ctx St W SP)
include L

theorem ctx_tFrame16 : ∀ r ∈ tFrame St W SP 16, (⟨Ctx, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.lay.cs.sub_right (Lay.stSub (by decide))
  · exact L.lay.cw'.sub_right (Lay.wSub (by decide))
  · exact L.lay.cw'.sub_right (Lay.wSub (by decide))
  · exact L.lay.kc.symm

theorem ctx_absFrame16 : ∀ r ∈ absFrame St W SP 16, (⟨Ctx, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.lay.cs.sub_right (Lay.stSub (by decide))
  · exact L.lay.cs.sub_right (Lay.stSub (by decide))
  · exact L.lay.cw'.sub_right (Lay.wSub (by decide))
  · exact L.lay.kc.symm

theorem ctr_absFrame16 : ∀ r ∈ absFrame St W SP 16, (⟨St + BitVec.ofNat 64 48, 32⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.lay.st_st (.inr (by decide)) (by decide) (by decide)
  · exact L.lay.st_st (.inr (by decide)) (by decide) (by decide)
  · exact L.lay.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact (L.lay.stk_st (by decide)).symm

theorem ctr_tFrame16 : ∀ r ∈ tFrame St W SP 16, (⟨St + BitVec.ofNat 64 48, 32⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.lay.st_st (.inr (by decide)) (by decide) (by decide)
  · exact L.lay.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact L.lay.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact (L.lay.stk_st (by decide)).symm

theorem abs_crFrame {s : State} {D : Addr} {n : Nat} (hd : DataW4 Ctx St W SP s D n) :
    ∀ r ∈ crFrame St SP D n, (⟨St + BitVec.ofNat 64 16, 32⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hd.dw.ok.st.sub_right (Lay.stSub (by decide))).symm
  · exact L.lay.st_st (.inl (by decide)) (by decide) (by decide)
  · exact (L.ks.sub_right (Lay.stSub (by decide))).symm

/-- The slots of `W` from 176 are outside the regions the pieces write. -/
theorem slot_tFrame {d : Nat} (h₁ : 176 ≤ d) (h₂ : d + 8 ≤ 512) :
    ∀ r ∈ tFrame St W SP 16, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (L.lay.st_w (by decide) (.inr ⟨by omega, by omega⟩)).symm
  · exact L.lay.w_w (.inr (by omega)) (by omega) (by decide)
  · exact L.lay.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.lay.stk_w (by omega)).symm

theorem slot_absFrame {d : Nat} (h₁ : 176 ≤ d) (h₂ : d + 8 ≤ 512) :
    ∀ r ∈ absFrame St W SP 16, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (L.lay.st_w (by decide) (.inr ⟨by omega, by omega⟩)).symm
  · exact (L.lay.st_w (by decide) (.inr ⟨by omega, by omega⟩)).symm
  · exact L.lay.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.lay.stk_w (by omega)).symm

theorem slot_crFrame {s : State} {D : Addr} {n d : Nat} (hd : DataW4 Ctx St W SP s D n) (h₁ : 176 ≤ d)
    (h₂ : d + 8 ≤ 512) : ∀ r ∈ crFrame St SP D n, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hd.dw.ok.w.sub_right (Lay.wSub (by omega))).symm
  · exact (L.lay.st_w (by decide) (.inr ⟨by omega, by omega⟩)).symm
  · exact (L.kw.sub_right (Lay.wSub (by omega))).symm

omit L in
theorem data_tFrame {s : State} {D : Addr} {n : Nat} (hd : DataW4 Ctx St W SP s D n) :
    ∀ r ∈ tFrame St W SP 16, (⟨D, n⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hd.dw.ok.st.sub_right (Lay.stSub (by decide))
  · exact hd.dw.ok.w.sub_right (Lay.wSub (by decide))
  · exact hd.dw.ok.w.sub_right (Lay.wSub (by decide))
  · exact hd.dw.ok.stk.symm

end

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay4 Ctx St W SP)
include L

/-- Before the text: the additional data padded if there is no text yet. -/
theorem start_ok {Hyp : Prop} {H : Block} {m₀ : Mem} {s : State} (he : Env Ctx St W SP s) (hm : s.mem = m₀)
    {a c₀ : List Byte} (hP : c₀.length < 2 ^ 64) (hH : blockAt m₀ (Ctx + BitVec.ofNat 64 240) = H)
    (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 a.length)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 c₀.length)
    (hyA : Hyp → Absorbed m₀ (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c₀)) :
    WP isa (.seq (.block [.mov .rax (.mem (at_ .r15 tlenO)), .alu .test .rax (.reg .rax)])
      (.ite .e (firstFlush v.callees) (.block []))) s fun s' => Env Ctx St W SP s' ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ Frame (tFrame St W SP 16) m₀ s'.mem ∧
      (Hyp → Absorbed s'.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (a ++ zeros (padLen a.length) ++ c₀)) := by
  have r₂ := he.perm.wR (show 192 + 8 ≤ 2560 by decide)
  obtain ⟨s₂, run₂, hz₂, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa [.mov .rax (.mem (at_ .r15 tlenO)),
      .alu .test .rax (.reg .rax)] s = some s₂ ∧ s₂.zf = some (decide (c₀.length = 0)) ∧
      (∀ r, r ≠ .rax → s₂.gpr r = s.gpr r) ∧ s₂.mem = s.mem ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    refine ⟨_, by xrun [he.r15, r₂], ?_, ?_, ?_⟩
    · simp only [zf_arithFlags, gpr_setReg, ite_true, htl, and_self_beq hP]
    · intro r a; simp [gpr_setReg, gpr_arithFlags, a]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have he₂ : Env Ctx St W SP s₂ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide)) hrd₂ hwr₂
  have hm₂' : s₂.mem = m₀ := hm₂.trans hm
  refine WP.ite (decide (c₀.length = 0)) (eval_e hz₂) (fun ht => ?_) (fun hf => ?_)
  · have hc : c₀ = [] := List.eq_nil_of_length_eq_zero (by simpa using ht)
    subst hc
    have r₃ := he₂.perm.wR (show 184 + 8 ≤ 2560 by decide)
    obtain ⟨s₃, run₃, hbx₃, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa [.mov .rbx (.mem (at_ .r15 alenO)),
        .alu .and .rbx (imm 15)] s₂ = some s₃ ∧ s₃.gpr .rbx = BitVec.ofNat 64 (a.length % 16) ∧
        (∀ r, r ≠ .rbx → s₃.gpr r = s₂.gpr r) ∧ s₃.mem = s₂.mem ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
      have hand := and15 (BitVec.ofNat 64 a.length)
      rw [imm_eq (by decide), toNat_mod16] at hand
      refine ⟨_, by xrun [he₂.r15, r₃], ?_, ?_, ?_⟩
      · simp only [gpr_setReg, gpr_arithFlags, ite_true, hm₂, hal, hand]
      · intro r a; simp [gpr_setReg, gpr_arithFlags, a]
      all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
    unfold firstFlush
    refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
    have he₃ : Env Ctx St W SP s₃ := he₂.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide)) hrd₃ hwr₃
    have hm₃' : s₃.mem = m₀ := hm₃.trans hm₂'
    refine WP.mono (WP.with_rdwr (flush_ok v L.lay (yo := 16) (.inr rfl) (H := H) (x := a)
      ⟨he₃, by rw [hm₃']; exact hH⟩ hbx₃)) fun s₄ ⟨fo, rd₄, wr₄⟩ =>
        ⟨fo.env, by rw [rd₄, hrd₃, hrd₂], by rw [wr₄, hwr₃, hwr₂], hm₃' ▸ fo.frame, fun hy => ?_⟩
    rw [List.append_nil]
    exact fo.abs (by rw [hm₃']; exact hyA hy)
  · have hc : c₀ ≠ [] := fun e => by subst e; simp_all
    refine WP.block_nil ⟨he₂, hrd₂, hwr₂, by rw [hm₂']; exact Frame.refl _ _, fun hy => ?_⟩
    rw [hm₂', ← Proof.Gcm.ghashInput_of_ne hc]
    exact hyA hy

/-- `streamText enc`: the `n` bytes at `D` encrypted (`enc`) or decrypted,
and their ciphertext absorbed, after additional data `a` and text `c₀`. -/
theorem streamText_ok (enc : Bool) {Hyp : Prop} {H icb : Block} {D : Addr} {n : Nat} {m₀ : Mem} {s : State}
    (he : Env Ctx St W SP s) (hm : s.mem = m₀) (hd : DataW4 Ctx St W SP s D n)
    (hbp : s.gpr .rbp = BitVec.ofNat 64 n) {a c₀ : List Byte} (hP : c₀.length < 2 ^ 64)
    (hH : blockAt m₀ (Ctx + BitVec.ofNat 64 240) = H)
    (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 a.length)
    (htl : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 c₀.length)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n)
    (hyA : Hyp → Absorbed m₀ (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H (ghashInput a c₀))
    (hyC : Hyp → Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx) icb c₀.length) :
    WP isa (streamText v.callees enc) s fun s' => Env Ctx St W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame (stFrame St W SP D n) m₀ s'.mem ∧
      (Hyp → Absorbed s'.mem (St + BitVec.ofNat 64 16) (St + BitVec.ofNat 64 32) H
          (ghashInput a (c₀ ++ ctext enc (ciphOf m₀ Ctx) icb c₀.length (bytesAt m₀ D n))) ∧
        Ctr s'.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx) icb (c₀.length + n) ∧
        bytesAt s'.mem D n = xorKs (ciphOf m₀ Ctx) icb c₀.length (bytesAt m₀ D n)) := by
  have hlt := hd.dw.ok.lt
  have hx : (a ++ zeros (padLen a.length) ++ c₀).length % 16 = c₀.length % 16 := by
    have := Proof.Gcm.length_pad_mod a.length
    simp only [List.length_append, Proof.Gcm.length_zeros]; omega
  simp only [streamText]
  obtain ⟨s₁, run₁, hz₁, hg₁, hm₁, hrd₁, hwr₁⟩ := test_ok s .rbp hbp hlt
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env Ctx St W SP s₁ := he.keep (fun r _ => by rw [hg₁]) hrd₁ hwr₁
  refine WP.ite (decide (n = 0)) (eval_e hz₁) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    refine WP.block_nil ⟨he₁, hrd₁, hwr₁, by rw [hm₁, hm]; exact Frame.refl _ _, fun hy => ⟨?_, ?_, rfl⟩⟩
    · rw [bytesAt_zero, ctext_nil, List.append_nil, hm₁, hm]; exact hyA hy
    · rw [hm₁, hm]; exact hyC hy
  have h0 : n ≠ 0 := by simpa using hf
  refine WP.assoc (WP.seq (WP.mono (start_ok v L he₁ (hm₁.trans hm) hP hH (by rw [hm₁]; exact hal)
    (by rw [hm₁]; exact htl) hyA) fun s₂ ⟨he₂, rd₂, wr₂, f₂, ha₂⟩ => ?_))
  -- The slots of `W`, the hash subkey, the cipher, the counter and the data, through the padding.
  have sl₂ : ∀ d, 176 ≤ d → d + 8 ≤ 512 →
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
    rw [f₂.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (slot_tFrame L h₁ h₂) (by decide), hm]
  have hd₂ : DataW4 Ctx St W SP s₂ D n := hd.of_eq (rd₂.trans hrd₁) (wr₂.trans hwr₁)
  have hc₂ : ciphOf s₂.mem Ctx = ciphOf m₀ Ctx := ciph_frame f₂ (ctx_tFrame16 L)
  have hH₂ : blockAt s₂.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame f₂ fun r hr => (ctx_tFrame16 L r hr).sub_left (Lay.ctxSub (by decide)), hH]
  have hD₂ : bytesAt s₂.mem D n = bytesAt m₀ D n := bytesAt_frame f₂ (data_tFrame hd) (by omega)
  have hC₂ : Hyp → Ctr s₂.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx) icb c₀.length :=
    fun hy => ctr_frame f₂ (ctr_tFrame16 L) (hyC hy)
  -- The data, its length and the text so far modulo 16.
  obtain ⟨s₃, run₃, h12₃, hbp₃, hbx₃, hg₃, hm₃, hrd₃, hwr₃⟩ := load_ok he₂
    ((sl₂ 200 (by decide) (by decide)).trans hdat) ((sl₂ 208 (by decide) (by decide)).trans hlen)
    ((sl₂ 192 (by decide) (by decide)).trans htl)
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  rw [toNat_mod16] at hbx₃
  have he₃ := he₂.keep (load_env hg₃) hrd₃ hwr₃
  have hd₃ : DataW4 Ctx St W SP s₃ D n := hd₂.of_eq hrd₃ hwr₃
  have sl₃ : ∀ d, 176 ≤ d → d + 8 ≤ 512 →
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
    rw [hm₃]; exact sl₂ d h₁ h₂
  have hne : ∀ y : List Byte, y.length = n → c₀ ++ y ≠ [] := fun y hy e => h0 (by
    have := congrArg List.length e
    rw [List.length_append, hy, List.length_nil] at this
    omega)
  cases enc
  · -- Decrypting: the ciphertext absorbed, then decrypted.
    simp only [partWith, Bool.false_eq_true, ↓reduceIte]
    have hai : AbsIn Ctx St W SP 16 H (a ++ zeros (padLen a.length) ++ c₀) D n s₃ :=
      ⟨he₃, h12₃, hbp₃, by rw [hbx₃, hx], hd₃.dw.ok, by rw [hm₃]; exact hH₂⟩
    refine WP.seq (WP.mono (WP.with_rdwr (absorb_ok v L.lay (.inr rfl) hai)) fun s₄ ⟨ao, rd₄, wr₄⟩ => ?_)
    have sl₄ : ∀ d, 176 ≤ d → d + 8 ≤ 512 →
        s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
      rw [ao.frame.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (slot_absFrame L h₁ h₂)
        (by decide), sl₃ d h₁ h₂]
    obtain ⟨s₅, run₅, h12₅, hbp₅, hbx₅, hg₅, hm₅, hrd₅, hwr₅⟩ := load_ok ao.env
      ((sl₄ 200 (by decide) (by decide)).trans hdat) ((sl₄ 208 (by decide) (by decide)).trans hlen)
      ((sl₄ 192 (by decide) (by decide)).trans htl)
    refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
    rw [toNat_mod16] at hbx₅
    have he₅ := ao.env.keep (load_env hg₅) hrd₅ hwr₅
    have hd₅ : DataW4 Ctx St W SP s₅ D n := hd₃.of_eq (by rw [hrd₅, rd₄]) (by rw [hwr₅, wr₄])
    have hc₅ : ciphOf s₅.mem Ctx = ciphOf m₀ Ctx := by
      rw [hm₅, ciph_frame ao.frame (ctx_absFrame16 L), hm₃, hc₂]
    have hD₅ : bytesAt s₅.mem D n = bytesAt m₀ D n := by
      rw [hm₅, bytesAt_frame ao.frame (data_absFrame (yo := 16) (.inr rfl) hd₃.dw.ok) (by omega), hm₃, hD₂]
    refine WP.mono (WP.with_rdwr (crypt_ok L (icb := icb) (P := c₀.length) ⟨he₅, h12₅, hbp₅, hbx₅, hd₅⟩))
      fun s₆ ⟨co, rd₆, wr₆⟩ => ⟨co.env, by rw [rd₆, hrd₅, rd₄, hrd₃, rd₂, hrd₁], by rw [wr₆, hwr₅, wr₄, hwr₃, wr₂, hwr₁],
        (tFrame_st f₂).trans ((hm₃ ▸ absFrame_st ao.frame).trans (hm₅ ▸ crFrame_st co.frame)), fun hy => ⟨?_, ?_, ?_⟩⟩
    · have A := abs_frame co.frame (abs_crFrame L hd₅) (hm₅ ▸ ao.abs (hm₃ ▸ ha₂ hy))
      rw [hm₃, hD₂] at A
      simp only [ctext, Bool.false_eq_true, ↓reduceIte]
      rw [Proof.Gcm.ghashInput_of_ne (hne _ (length_bytesAt _ _ _)), ← List.append_assoc]
      exact A
    · have C := co.ctr
      rw [hc₅] at C
      exact C (hm₅ ▸ ctr_frame ao.frame (ctr_absFrame16 L) (hm₃ ▸ hC₂ hy))
    · have C := co.out
      rw [hc₅, hD₅] at C
      exact C (hm₅ ▸ ctr_frame ao.frame (ctr_absFrame16 L) (hm₃ ▸ hC₂ hy))
  · -- Encrypting: the plaintext encrypted, then the ciphertext absorbed.
    simp only [partWith, ↓reduceIte]
    have hc₃ : ciphOf s₃.mem Ctx = ciphOf m₀ Ctx := by rw [hm₃, hc₂]
    refine WP.seq (WP.mono (WP.with_rdwr (crypt_ok L (icb := icb) (P := c₀.length) ⟨he₃, h12₃, hbp₃, hbx₃, hd₃⟩))
      fun s₄ ⟨co, rd₄, wr₄⟩ => ?_)
    have sl₄ : ∀ d, 176 ≤ d → d + 8 ≤ 512 →
        s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
      rw [co.frame.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (slot_crFrame L hd₃ h₁ h₂)
        (by decide), sl₃ d h₁ h₂]
    obtain ⟨s₅, run₅, h12₅, hbp₅, hbx₅, hg₅, hm₅, hrd₅, hwr₅⟩ := load_ok co.env
      ((sl₄ 200 (by decide) (by decide)).trans hdat) ((sl₄ 208 (by decide) (by decide)).trans hlen)
      ((sl₄ 192 (by decide) (by decide)).trans htl)
    refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
    rw [toNat_mod16] at hbx₅
    have he₅ := co.env.keep (load_env hg₅) hrd₅ hwr₅
    have hd₅ : DataW4 Ctx St W SP s₅ D n := hd₃.of_eq (by rw [hrd₅, rd₄]) (by rw [hwr₅, wr₄])
    have hH₅ : blockAt s₅.mem (Ctx + BitVec.ofNat 64 240) = H := by
      rw [hm₅, blockAt_frame co.frame (fun r hr => (ctx_crFrame L hd₃ r hr).sub_left (Lay.ctxSub (by decide))),
        hm₃, hH₂]
    have hai : AbsIn Ctx St W SP 16 H (a ++ zeros (padLen a.length) ++ c₀) D n s₅ :=
      ⟨he₅, h12₅, hbp₅, by rw [hbx₅, hx], hd₅.dw.ok, hH₅⟩
    refine WP.mono (WP.with_rdwr (absorb_ok v L.lay (.inr rfl) hai))
      fun s₆ ⟨ao, rd₆, wr₆⟩ => ⟨ao.env, by rw [rd₆, hrd₅, rd₄, hrd₃, rd₂, hrd₁], by rw [wr₆, hwr₅, wr₄, hwr₃, wr₂, hwr₁],
        (tFrame_st f₂).trans ((hm₃ ▸ crFrame_st co.frame).trans (hm₅ ▸ absFrame_st ao.frame)), fun hy => ⟨?_, ?_, ?_⟩⟩
    · have C := co.out
      rw [hc₃, hm₃, hD₂] at C
      have o := C (hm₃ ▸ hC₂ hy)
      have A := ao.abs (hm₅ ▸ abs_frame co.frame (abs_crFrame L hd₃) (hm₃ ▸ ha₂ hy))
      rw [hm₅, o] at A
      simp only [ctext, ↓reduceIte]
      rw [Proof.Gcm.ghashInput_of_ne (hne _ (Proof.Gcm.length_xorKs _ _ _ _ |>.trans (length_bytesAt _ _ _))),
        ← List.append_assoc]
      exact A
    · have C := co.ctr
      rw [hc₃, hm₃] at C
      exact ctr_frame ao.frame (ctr_absFrame16 L) (hm₅ ▸ C (hC₂ hy))
    · have C := co.out
      rw [hc₃, hm₃, hD₂] at C
      rw [bytesAt_frame ao.frame (data_absFrame (yo := 16) (.inr rfl) hd₅.dw.ok) (by omega), hm₅]
      exact C (hC₂ hy)

end

end VG.Proof.Sm4Gcm.X86_64
