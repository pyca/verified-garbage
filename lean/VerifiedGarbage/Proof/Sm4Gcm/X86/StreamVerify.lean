module

import VerifiedGarbage.Proof.AesGcm.X86.Cmp
meta import VerifiedGarbage.Proof.AesGcm.X86.Cmp
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.AesGcm.X86.Top
public import VerifiedGarbage.Proof.Sm4Gcm.X86.Contract
meta import VerifiedGarbage.Proof.AesGcm.X86.Top
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
meta import VerifiedGarbage.Impl.Sm4Gcm.X86
meta import VerifiedGarbage.Proof.Framework.X86.Call
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
meta import VerifiedGarbage.TCB.X86.Isa
meta import VerifiedGarbage.TCB.X86.State
meta import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Sm4Gcm.X86.Tag
import VerifiedGarbage.Proof.Gcm.Be64
meta import VerifiedGarbage.Proof.Sm4Gcm.X86.Tag
meta import VerifiedGarbage.Proof.Gcm.Be64
meta import VerifiedGarbage.Proof.Sm4Gcm.X86.Contract

/-! ### `Sm4Gcm.X86.StreamFinish`, which only this module used -/

section

/-! ### `Sm4Gcm.X86.FinTag`, which only this module used -/

section

/-!
# SM4-GCM on x86: the tag of a streaming state (`finTag`)

Untrusted: everything here is checked by Lean. `finTag o` pads what GHASH
buffered (`text_len mod 16` bytes, or `aad_len mod 16` if there is no text)
and absorbs it (`flush 16`), then writes the tag to `W + o` (`tag`): the
full tag of the message the state represents (`finTag_pc`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86

variable {vg : VG.Proof.AesGcm.X86.GcmImpl}

open VG VG.X86 VG.X86.RegUpd VG.Impl.Sm4Gcm.X86 VG.WriteBytes VG.Proof.AesGcm.X86
open VG.Impl.AesGcm.X86 hiding ctrCall keyCall ctrArgs cryptWhole cryptTail crypt tag init cryptEntry
  streamEncrypt streamDecrypt finEntry finTag streamFinish streamVerify oneEntry oneTag oneCrypt «seal» «open»
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks zeros padLen ofBytes toBytes StreamRepr fullTag ghashInput)
open VG.Proof.Gcm (Absorbed lensBlock padded)

theorem lensBlock_mod (a t : Nat) : lensBlock (a % 2 ^ 64) t = lensBlock a t := by
  simp only [lensBlock]
  rw [← Proof.Gcm.be64_mod (8 * (a % 2 ^ 64)), ← Proof.Gcm.be64_mod (8 * a)]
  congr 2
  omega_using []

theorem val64_eq (lo hi : BitVec 32) : val64 lo hi = (hi ++ lo).toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt lo.isLt, Nat.shiftLeft_eq]

/-- The length of what GHASH buffered, modulo 16. -/
theorem ghashInput_mod {a c : List Byte} :
    (ghashInput a c).length % 16 = (if c = [] then a.length else c.length) % 16 := by
  by_cases hc : c = []
  · simp [ghashInput, hc]
  · rw [Proof.Gcm.ghashInput_of_ne hc]
    simp only [hc, ↓reduceIte, List.length_append, Proof.Gcm.length_zeros]
    have := Proof.Gcm.length_pad_mod a.length
    omega_using [this]

theorem or_eq_zero32 (a b : BitVec 32) : (a ||| b = 0) ↔ (a = 0 ∧ b = 0) := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_or] at this
    have := Nat.or_eq_zero_iff.mp this
    exact ⟨BitVec.eq_of_toNat_eq (by simpa using this.1), BitVec.eq_of_toNat_eq (by simpa using this.2)⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- Which length's remainder GHASH buffered: `text_len`'s, or `aad_len`'s if there is no text. -/
theorem buffered_mod {al ah xl xh : BitVec 32} {a c : List Byte} (hl : ah ++ al = BitVec.ofNat 64 a.length)
    (ht : (xh ++ xl).toNat = c.length) :
    (ghashInput a c).length % 16 = (if (xl ||| xh == 0) = true then al else xl).toNat % 16 := by
  rw [ghashInput_mod]
  obtain e := val64_eq xl xh
  simp only [val64] at e
  by_cases hc : c = []
  · subst hc
    obtain h0 : xl = 0 ∧ xh = 0 := by
      simp only [List.length_nil] at ht
      exact ⟨BitVec.eq_of_toNat_eq (by simp; omega_using [e, ht]), BitVec.eq_of_toNat_eq (by simp; omega_using [e, ht])⟩
    obtain ⟨rfl, rfl⟩ := h0
    simp only [↓reduceIte, BitVec.or_self, beq_self_eq_true]
    exact (lo_mod16 hl).symm
  · have hne : (xl ||| xh == 0) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq, or_eq_zero32]
      rintro ⟨rfl, rfl⟩
      exact hc (List.eq_nil_of_length_eq_zero (by simp at ht; omega_using [ht]))
    simp only [hc, ↓reduceIte, hne, Bool.false_eq_true]
    omega_using [ht, e]

/-- The kept lengths `finTag` reads. -/
structure FinIn (Ctx St W SP : BitVec 32) (al ah xl xh : BitVec 32) (s : State) : Prop where
  env : Env Ctx St W SP s
  al : slotv s.mem W alO = al
  ah : slotv s.mem W ahO = ah
  xl : slotv s.mem W xlO = xl
  xh : slotv s.mem W xhO = xh

/-- After `finTag o`: the tag of what the state represented, from `m₀`. -/
structure FinOut (Ctx St W SP : BitVec 32) (o : Nat) (al ah xl xh : BitVec 32) (m₀ : Mem) (s : State) : Prop where
  env : Env Ctx St W SP s
  frame : Frame (tagFrame St W SP o) m₀ s.mem
  tag : ∀ iv a c, StreamRepr m₀ (w64 St) (ciphOf m₀ Ctx) (Hk m₀ Ctx) iv a c → ah ++ al = BitVec.ofNat 64 a.length →
    (xh ++ xl).toNat = c.length → bytesAt s.mem (w64 W + BitVec.ofNat 64 o) 16 = fullTag (ciphOf m₀ Ctx) (Hk m₀ Ctx) iv a c

theorem FinIn.keep {Ctx St W SP : BitVec 32} {al ah xl xh : BitVec 32} {s s' : State}
    (h : FinIn Ctx St W SP al ah xl xh s) (hbp : s'.gpr .ebp = s.gpr .ebp) (hsi : s'.gpr .esi = s.gpr .esi)
    (hsp : s'.gpr .esp = s.gpr .esp) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    FinIn Ctx St W SP al ah xl xh s' :=
  ⟨h.env.keep hbp hsi hsp hrd hwr (by rw [hm]), by rw [hm]; exact h.al, by rw [hm]; exact h.ah, by rw [hm]; exact h.xl,
    by rw [hm]; exact h.xh⟩

section
variable {Ctx St W SP : BitVec 32} (L : Lay4 Ctx St W SP 1536)
include L

theorem finTag_pc {o : Nat} (ho : o = 0 ∨ o = 112) {al ah xl xh : BitVec 32} :
    Pc (fun (m₀ : Mem) s => FinIn Ctx St W SP al ah xl xh s ∧ s.mem = m₀) (finTag vg.callees o)
      (FinOut Ctx St W SP o al ah xl xh ·) := by
  generalize hv : (if (xl ||| xh == 0) = true then al else xl) = v
  refine Pc.seq (Q := fun m₀ s => (FinIn Ctx St W SP al ah xl xh s ∧ s.mem = m₀) ∧ s.gpr .eax = xl ∧
      s.gpr .ecx = al ∧ s.zf = some (xl ||| xh == 0))
    (Pc.taint [.ebp] (fun m₀ s ⟨h, hm⟩ => ?_) (fun _ _ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.env.ebp, h₂.1.env.ebp]) (by taint_decide)) ?_
  · have he := h.env
    obtain h1 := h.xl; have h2 := h.al; have h3 := h.xh
    rw [slotv_eq] at h1 h2 h3
    refine WP.of_runBlock ⟨_, by xrun [he.ebp, L.aW, he.wIn', h1, h2, h3], ⟨h.keep (by regs []) (by regs [])
      (by regs []) (by mems []) (by mems []) (by mems []), by mems []; exact hm⟩, by regs [], by regs [], by mems []⟩
  refine Pc.seq (Q := fun m₀ s => (FinIn Ctx St W SP al ah xl xh s ∧ s.mem = m₀) ∧ s.gpr .eax = v) ?_ ?_
  · refine Pc.ite (xl ||| xh == 0) (fun _ _ h => h.2.2.2) (fun ht => ?_) (fun hf => ?_)
    · refine Pc.taint [] (fun m₀ s ⟨⟨h, hm⟩, _, hc, _⟩ => WP.of_runBlock ⟨_, by xrun [], ⟨h.keep (by regs [])
        (by regs []) (by regs []) (by mems []) (by mems []) (by mems []), by mems []; exact hm⟩, by
          rw [← hv, ht]; regs [hc]; rfl⟩) (fun _ _ _ _ _ _ _ h => by simp at h) (by taint_decide)
    · exact Pc.mono Pc.nil (fun _ _ h => h) fun _ _ ⟨h, ha, _, _⟩ => ⟨h, by rw [← hv, hf]; exact ha⟩
  refine Pc.seq (Q := fun m₀ s => FinIn Ctx St W SP al ah xl xh s ∧
      slotv s.mem W bO = BitVec.ofNat 32 (v.toNat % 16) ∧ Frame [⟨w64 W + BitVec.ofNat 64 bO, 4⟩] m₀ s.mem)
    (Pc.taint [.ebp] (fun m₀ s ⟨⟨h, hm⟩, ha⟩ => ?_) (fun _ _ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.1.env.ebp, h₂.1.1.env.ebp]) (by taint_decide)) ?_
  · have he := h.env
    obtain hand := and15 v
    refine WP.of_runBlock ⟨_, by xrun [he.ebp, L.aW, he.wIn, ha], ?_⟩
    obtain fb : Frame [⟨w64 W + BitVec.ofNat 64 bO, 4⟩] s.mem
        (s.mem.writeW (w64 W + BitVec.ofNat 64 bO) (v &&& BitVec.ofNat 32 15)) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    obtain sK : ∀ {q}, 128 ≤ q → q + 4 ≤ 240 → slotv (s.mem.writeW (w64 W + BitVec.ofNat 64 bO)
        (v &&& BitVec.ofNat 32 15)) W q = slotv s.mem W q := fun h₁ h₂ =>
      slot_frame fb fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by simp only [bO]; omega_using [h₂])) (by omega_using [h₂]) (by decide)
    refine ⟨⟨he.keep (by regs []) (by regs []) (by regs []) (by mems []) (by mems []) (by
        simp only [mem_setMem, mem_setReg, mem_arithFlags]; exact sK (by decide) (by decide)),
      by simp only [mem_setMem, mem_setReg, mem_arithFlags]; rw [sK (by decide) (by decide)]; exact h.al,
      by simp only [mem_setMem, mem_setReg, mem_arithFlags]; rw [sK (by decide) (by decide)]; exact h.ah,
      by simp only [mem_setMem, mem_setReg, mem_arithFlags]; rw [sK (by decide) (by decide)]; exact h.xl,
      by simp only [mem_setMem, mem_setReg, mem_arithFlags]; rw [sK (by decide) (by decide)]; exact h.xh⟩, ?_, ?_⟩
    · simp only [mem_setMem, mem_setReg, mem_arithFlags, slotv_eq, Mem.readW_writeW_self32]; exact hand
    · simp only [mem_setMem, mem_setReg, mem_arithFlags]; rw [← hm]; exact fb
  refine Pc.seq (Pc.lift (flush_pc L.lay (yo := 16) (.inr rfl) (b := v.toNat % 16) (Nat.mod_lt _ (by decide)))
    (fun _ s => s.mem) fun m₀ s h => ⟨⟨h.1.env, h.2.1⟩, rfl⟩) ?_
  refine Pc.mono (Pc.lift (tag_pc L (al := alO) (ah := ahO) (tl := xlO) (th := xhO) ho
      (.inr (.inl ⟨rfl, rfl, rfl, rfl, rfl⟩)) (alo := al) (ahi := ah) (tlo := xl) (thi := xh))
    (fun _ s => s.mem) fun m₀ s' ⟨s, ⟨h, _, _⟩, fo, _, _⟩ => ⟨⟨fo.env, ?_⟩, rfl⟩) (fun _ _ h => h) fun m₀ s'' ⟨s', ⟨s, ⟨h, hb, fb⟩, fo, _, _⟩, tg, _, _⟩ => ?_
  · refine ⟨tg.env, ?_, fun iv a c hr hl ht => ?_⟩
    · refine (fb.sub fun r hr => ?_).trans ((t_tagFrame L fo.frame).trans tg.frame)
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨wsR W, by simp, Offset.sub _ (by decide) (by decide)⟩
    rw [Proof.Gcm.streamRepr_iff, ofNat_lit, ofNat_lit] at hr
    obtain ⟨hj, ha, -⟩ := hr
    obtain dS : ∀ {d k : Nat}, d + k ≤ 80 → ∀ r ∈ [(⟨w64 W + BitVec.ofNat 64 bO, 4⟩ : Region)],
        (⟨w64 St + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun hk r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_w hk (.inr ⟨by decide, by decide⟩)
    obtain hHs : Hk s.mem Ctx = Hk m₀ Ctx := blockAt_frame fb fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide)
    obtain hx := buffered_mod hl ht
    rw [hv] at hx
    obtain ha₁ : Absorbed s.mem (w64 St + BitVec.ofNat 64 16) (w64 St + BitVec.ofNat 64 32) (Hk s.mem Ctx)
        (ghashInput a c) := by
      rw [hHs]
      exact ha.congr (blockAt_frame fb (dS (by decide))) (bytesAt_frame fb (dS (d := 32)
        (k := (ghashInput a c).length % 16) (by omega_using [])) (by omega_using []))
    obtain hab := fo.abs _ hx ha₁
    have acc := hab.1
    rw [show ghashInput a c ++ zeros (padLen (ghashInput a c).length) = padded a c from rfl,
      Proof.Gcm.whole_of_mod (Proof.Gcm.length_padded a c), List.take_of_length_le (Nat.le_refl _)] at acc
    obtain hH' : Hk s'.mem Ctx = Hk s.mem Ctx := blockAt_frame fo.frame (ctx_tFrame L.lay (.inr rfl))
    obtain hC : ciphOf s'.mem Ctx = ciphOf m₀ Ctx := by
      rw [ciph_frame fo.frame (ctx_tFrame' L), ciph_frame fb (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.cw.sub_right (Lay.wSub (by decide)))]
    obtain hJ : blockAt s'.mem (w64 St) = blockAt m₀ (w64 St) := by
      obtain e₁ := blockAt_frame fo.frame (p := w64 St + BitVec.ofNat 64 0) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact Lay.st_st (.inl (by decide)) (by decide) (by decide)
        · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
        · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
        · exact (L.lay.stk_st (by decide)).symm
      obtain e₂ := blockAt_frame fb (dS (d := 0) (k := 16) (by decide))
      simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at e₁ e₂
      rw [e₁, e₂]
    obtain hva : val64 al ah = a.length % 2 ^ 64 := by rw [val64_eq, hl, BitVec.toNat_ofNat]
    obtain hvx : val64 xl xh = c.length := by rw [val64_eq, ht]
    rw [tg.out, hH', hHs, acc, hC, hJ, hj, hva, hvx, lensBlock_mod, hHs, Proof.Gcm.fullTag_eq]
  · have sl : ∀ {q}, 112 ≤ q → q + 4 ≤ 240 → slotv s'.mem W q = slotv s.mem W q := fun h₁ h₂ =>
      slot_frame fo.frame (slot_tFrame L.lay (.inr rfl) h₁ h₂)
    exact ⟨by rw [sl (by decide) (by decide)]; exact h.al, by rw [sl (by decide) (by decide)]; exact h.ah,
      by rw [sl (by decide) (by decide)]; exact h.xl, by rw [sl (by decide) (by decide)]; exact h.xh⟩

end

end VG.Proof.Sm4Gcm.X86

end

end

/-!
# SM4-GCM on x86: `vg_aes_gcm_stream_finish`

Untrusted: everything here is checked by Lean. The entry, the tag
(`finTag 0`), its copy to `tag` (`tagOut 0`) and the exit, as one `Pc`
(`streamFinish_pc`): correct (`streamFinish_correct`) and constant time
(`streamFinish_ct`). The entry is shared with `vg_aes_gcm_stream_verify`
(`finEntry_pc`), whose `W` is its last argument too: the pieces find it at 7
in the public data (`pubSw`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86

variable {vg : VG.Proof.AesGcm.X86.GcmImpl}

open VG VG.X86 VG.X86.RegUpd VG.Impl.Sm4Gcm.X86 VG.WriteBytes VG.Proof.AesGcm.X86
open VG.Impl.AesGcm.X86 hiding ctrCall keyCall ctrArgs cryptWhole cryptTail crypt tag init cryptEntry
  streamEncrypt streamDecrypt finEntry finTag streamFinish streamVerify oneEntry oneTag oneCrypt «seal» «open»
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr)
open VG.Spec.Gcm (ctxH)
open VG.Spec.Sm4.Gcm (ctxCiph)

abbrev finKeeps : List (Nat × Nat) := [(0, ctxO), (2, alO), (3, ahO), (4, xlO), (5, xhO)]

theorem streamFinish_eq : (streamFinish vg.callees) = .seq (entry 7 (([.mov .esi (argOp 1)] : List Instr) ++
    ((finKeeps ++ [(6, tpO)]).flatMap (fun (p : Nat × Nat) => keep p.1 p.2) ++ [])))
    (.seq (finTag vg.callees 0) (.seq (tagOut 0) (.block restore))) := rfl

/-- What the precondition of `finish` and `verify` (with `nA` arguments, `W`
the last, `w`) gives. -/
structure FinPre (nA w : Nat) (s : State) : Prop where
  cR : Covers [⟨w64 (arg s 0), 256⟩] (s.rd ++ s.wr)
  sW : Covers [⟨w64 (arg s 1), 80⟩] s.wr
  wW : Covers [⟨w64 (arg s w), 2560⟩] s.wr
  aR : Covers [⟨argAddr s 0, 4 * nA⟩] (s.rd ++ s.wr)
  cs : (⟨w64 (arg s 0), 256⟩ : Region).Disjoint ⟨w64 (arg s 1), 80⟩
  cw : (⟨w64 (arg s 0), 256⟩ : Region).Disjoint ⟨w64 (arg s w), 2560⟩
  sw : (⟨w64 (arg s 1), 80⟩ : Region).Disjoint ⟨w64 (arg s w), 2560⟩
  wa : (⟨w64 (arg s w), 2560⟩ : Region).Disjoint ⟨argAddr s 0, 4 * nA⟩
  r_s : (⟨w64 (s.gpr .esp), 4⟩ : Region).Disjoint ⟨w64 (arg s 1), 80⟩
  r_w : (⟨w64 (s.gpr .esp), 4⟩ : Region).Disjoint ⟨w64 (arg s w), 2560⟩
  k_c : (below (s.gpr .esp) 1536).Disjoint ⟨w64 (arg s 0), 256⟩
  k_s : (below (s.gpr .esp) 1536).Disjoint ⟨w64 (arg s 1), 80⟩
  k_w : (below (s.gpr .esp) 1536).Disjoint ⟨w64 (arg s w), 2560⟩
  fc : (arg s 0).toNat + 256 ≤ 2 ^ 32
  fs : (arg s 1).toNat + 80 ≤ 2 ^ 32
  fw : (arg s w).toNat + 2560 ≤ 2 ^ 32
  sp : 1536 ≤ (s.gpr .esp).toNat
  fa : (s.gpr .esp).toNat + 4 + 4 * nA ≤ 2 ^ 32

theorem finPre_of {s : State} (h : finPre s) : FinPre 8 7 s := by
  simp only [finPre] at h
  sig_split h
  rename_i hrd hwr d_cs hdrop3 d_cw hdrop5 hdrop6 d_sw hdrop8 hdrop9 hdrop10 d_wa hdrop12 r_s hdrop14 r_w
    hdrop16 k_c k_s hdrop19 k_w hdrop21 fc fs hdrop24 fw sp
  clear hdrop3 hdrop5 hdrop6 hdrop8 hdrop9 hdrop10 hdrop12 hdrop14 hdrop16 hdrop19 hdrop21 hdrop24
  have fa := h
  clear h
  rw [ofNat_lit, below_eq sp] at k_c k_s k_w
  exact ⟨by rw [hrd, hwr]; exact covers_of_mem (by simp), by rw [hwr]; exact covers_of_mem (by simp),
    by rw [hwr]; exact covers_of_mem (by simp), by rw [hrd, hwr]; exact covers_of_mem (by simp), d_cs, d_cw, d_sw,
    d_wa, r_s, r_w, k_c, k_s, k_w, fc, fs, fw, sp, by omega_using [fa]⟩

/-- The tag `finish` writes. -/
theorem finPre_tag {s : State} (h : finPre s) : Covers [⟨w64 (arg s 6), 16⟩] s.wr ∧
    (arg s 6).toNat + 16 ≤ 2 ^ 32 ∧ (⟨w64 (arg s 6), 16⟩ : Region).Disjoint ⟨w64 (arg s 7), 2560⟩ ∧
    (⟨w64 (s.gpr .esp), 4⟩ : Region).Disjoint ⟨w64 (arg s 6), 16⟩ := by
  simp only [finPre] at h
  sig_split h
  rename_i hdrop0 hwr hdrop2 hdrop3 hdrop4 hdrop5 hdrop6 hdrop7 hdrop8 d_tw hdrop10 hdrop11 hdrop12 hdrop13
    r_t hdrop15 hdrop16 hdrop17 hdrop18 hdrop19 hdrop20 hdrop21 hdrop22 hdrop23 ft hdrop25 hdrop26
  clear hdrop0 hdrop2 hdrop3 hdrop4 hdrop5 hdrop6 hdrop7 hdrop8 hdrop10 hdrop11 hdrop12 hdrop13 hdrop15
    hdrop16 hdrop17 hdrop18 hdrop19 hdrop20 hdrop21 hdrop22 hdrop23 hdrop25 hdrop26
  clear h
  exact ⟨by rw [hwr]; exact covers_of_mem (by simp), ft, d_tw, r_t⟩

theorem verifyPre_of {s : State} (h : verifyPre s) : FinPre 9 8 s := by
  simp only [verifyPre] at h
  sig_split h
  rename_i hrd hwr d_cs d_cw hdrop4 hdrop5 hdrop6 hdrop7 d_sw hdrop9 d_wa hdrop11 r_s hdrop13 r_w hdrop15 k_c
    k_s hdrop18 k_w hdrop20 fc fs hdrop23 fw sp
  clear hdrop4 hdrop5 hdrop6 hdrop7 hdrop9 hdrop11 hdrop13 hdrop15 hdrop18 hdrop20 hdrop23
  have fa := h
  clear h
  rw [ofNat_lit, below_eq sp] at k_c k_s k_w
  exact ⟨by rw [hrd, hwr]; exact covers_of_mem (by simp), by rw [hwr]; exact covers_of_mem (by simp),
    by rw [hwr]; exact covers_of_mem (by simp), by rw [hrd, hwr]; exact covers_of_mem (by simp), d_cs, d_cw, d_sw,
    d_wa, r_s, r_w, k_c, k_s, k_w, fc, fs, fw, sp, by omega_using [fa]⟩

/-- The tag `verify` reads. -/
theorem verifyPre_tag {s : State} (h : verifyPre s) :
    Covers [⟨w64 (arg s 6), (arg s 7).toNat⟩] (s.rd ++ s.wr) ∧ (arg s 6).toNat + (arg s 7).toNat ≤ 2 ^ 32 ∧
      (⟨w64 (arg s 6), (arg s 7).toNat⟩ : Region).Disjoint ⟨w64 (arg s 8), 2560⟩ := by
  simp only [verifyPre] at h
  sig_split h
  rename_i hrd hwr hdrop2 hdrop3 hdrop4 hdrop5 d_tw hdrop7 hdrop8 hdrop9 hdrop10 hdrop11 hdrop12 hdrop13
    hdrop14 hdrop15 hdrop16 hdrop17 hdrop18 hdrop19 hdrop20 hdrop21 hdrop22 ft hdrop24 hdrop25
  clear hdrop2 hdrop3 hdrop4 hdrop5 hdrop7 hdrop8 hdrop9 hdrop10 hdrop11 hdrop12 hdrop13 hdrop14 hdrop15
    hdrop16 hdrop17 hdrop18 hdrop19 hdrop20 hdrop21 hdrop22 hdrop24 hdrop25
  clear h
  exact ⟨by rw [hrd, hwr]; exact covers_of_mem (by simp), ft, d_tw⟩

theorem FinPre.lay {nA w : Nat} {s : State} (h : FinPre nA w s) :
    Lay4 (arg s 0) (arg s 1) (arg s w) (s.gpr .esp) 1536 :=
  Lay4.of h.fc h.fs h.fw (by decide) h.sp h.cs h.cw (h.sw.sub_right (Region.sub_prefix (by decide)))
    (h.sw.sub_right (Lay.wSub (by decide))) h.k_c h.k_s h.k_w

/-- The layout of `finish` and `verify`, for the public data `p` (`W` at 6). -/
structure FinL (p : BitVec 32 × (Nat → BitVec 32)) : Prop where
  L : Lay4 (p.2 0) (p.2 1) (p.2 6) p.1 1536
  r_s : (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 1), 80⟩
  r_w : (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 6), 2560⟩

theorem FinPre.fl {nA w : Nat} {s : State} (h : FinPre nA w s) (hw : nA = w + 1) (h7 : 7 ≤ w)
    {p : BitVec 32 × (Nat → BitVec 32)} (hp : pubSw nA 6 s = p) : FinL p := by
  have a : ∀ i, i < 6 → arg s i = p.2 i := fun i hi => pubSw_arg hp (by omega_using [hw, h7, hi]) (by omega_using [hi]) (by omega_using [hw, h7, hi])
  have aW : arg s w = p.2 6 := pubSw_W hp (by omega_using [hw, h7]) hw
  have esp := pubSw_esp hp
  have L := h.lay
  have r_s := h.r_s
  have r_w := h.r_w
  rw [a 0 (by decide), a 1 (by decide), aW, esp] at L
  rw [esp, a 1 (by decide)] at r_s
  rw [esp, aW] at r_w
  exact ⟨L, r_s, r_w⟩

/-- After the entry of `finish` or `verify`. -/
structure FinEnt (nA w : Nat) (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  pre : FinPre nA w s₀
  pub : pubSw nA 6 s₀ = p
  fin : FinIn (p.2 0) (p.2 1) (p.2 6) p.1 (p.2 2) (p.2 3) (p.2 4) (p.2 5) s
  saved : SavedAt s.mem (p.2 6) s₀
  frame : Frame [⟨w64 (p.2 6) + BitVec.ofNat 64 128, 2432⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The entry of `finish` and `verify`, copying also the arguments `ex`. -/
theorem finEntry_pc (nA w : Nat) (hw : nA = w + 1) (h7 : 7 ≤ w) (ex : List (Nat × Nat))
    (hex : ∀ q ∈ finKeeps ++ ex, q.1 < nA ∧ 144 ≤ q.2 ∧ q.2 + 4 ≤ 2560 ∧ q.2 % 4 = 0)
    (hnd : ((finKeeps ++ ex).map (·.2)).Nodup) (Pre : State → Prop) (hPre : ∀ s, Pre s → FinPre nA w s)
    (p : BitVec 32 × (Nat → BitVec 32)) {hh₀ hh : Taint.Hint VG.X86.taint.T}
    (ht₀ : (VG.X86.taint.check (τr [.esp]) (.block [.mov .eax (argOp w)]) hh₀).isSome = true)
    (ht : (VG.X86.taint.check (τr [.eax, .esp]) (.block (saveAt ++ (([.mov .esi (argOp 1)] : List Instr) ++
      ((finKeeps ++ ex).flatMap (fun p => keep p.1 p.2) ++ [])))) hh).isSome = true) :
    Pc (fun (s₀ : State) s => Pre s₀ ∧ pubSw nA 6 s₀ = p ∧ s = s₀)
      (entry w (([.mov .esi (argOp 1)] : List Instr) ++ ((finKeeps ++ ex).flatMap (fun p => keep p.1 p.2) ++ [])))
      (fun s₀ s => FinEnt nA w p s₀ s ∧ (∀ q ∈ ex, slotv s.mem (p.2 6) q.2 = arg s₀ q.1) ∧ Pre s₀) := by
  refine ⟨fun s₀ s ⟨hpre, hpub, hs⟩ => ?_, ?_⟩
  · subst s
    have h := hPre _ hpre
    have L := h.lay
    have a : ∀ i, i < 6 → arg s₀ i = p.2 i := fun i hi => pubSw_arg hpub (by omega_using [hw, h7, hi]) (by omega_using [hi]) (by omega_using [hw, h7, hi])
    have aW : arg s₀ w = p.2 6 := pubSw_W hpub (by omega_using [hw, h7]) hw
    have esp := pubSw_esp hpub
    have rA : Covers [argsR (s₀.gpr .esp) nA] (s₀.rd ++ s₀.wr) := by rw [argsR_eq]; exact h.aR
    have aw : (argsR (s₀.gpr .esp) nA).Disjoint ⟨w64 (arg s₀ w), 2560⟩ := by rw [argsR_eq]; exact h.wa.symm
    refine entry_ok (finKeeps ++ ex) [] (by omega_using [hw]) (by omega_using [hw, h7]) hex hnd rfl rfl h.wW rA aw h.fa h.fw fun s₂ e => ?_
    have he : Env (arg s₀ 0) (arg s₀ 1) (arg s₀ w) (s₀.gpr .esp) s₂ :=
      ⟨e.ebp, e.esi, e.esp, by rw [e.rd, e.wr]; exact h.cR, by rw [e.wr]; exact h.sW, by rw [e.wr]; exact h.wW,
        e.slots (0, ctxO) (by simp)⟩
    refine ⟨s₂, rfl, ⟨h, hpub, ?_, ?_, ?_, e.rd, e.wr⟩, fun q hq => by rw [← aW]; exact e.slots q (by simp [hq]),
      hpre⟩
    · rw [← a 0 (by omega_using []), ← a 1 (by omega_using []), ← a 2 (by omega_using []), ← a 3 (by omega_using []), ← a 4 (by omega_using []),
        ← a 5 (by omega_using []), ← aW, ← esp]
      exact ⟨he, e.slots (2, alO) (by simp), e.slots (3, ahO) (by simp), e.slots (4, xlO) (by simp),
        e.slots (5, xhO) (by simp)⟩
    · rw [← aW]; exact e.saved
    · rw [← aW]; exact e.frame
  · refine CT.seq (J := fun s => s.gpr .eax = p.2 6 ∧ s.gpr .esp = p.1)
      (CT.taint [.esp] (fun s₁ s₂ ⟨a₁, _, h₁, e₁⟩ ⟨a₂, _, h₂, e₂⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; subst e₁; subst e₂
        rw [pubSw_esp h₁, pubSw_esp h₂]) ht₀) (fun s ⟨s₀, hpre, hpub, hs⟩ => ?_)
      (CT.taint [.eax, .esp] (fun s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2, h₂.2]) ht)
    subst s
    have h := hPre _ hpre
    have rA : Covers [argsR (s₀.gpr .esp) nA] (s₀.rd ++ s₀.wr) := by rw [argsR_eq]; exact h.aR
    exact WP.mono (arg0_ok (argIn_of rA h.fa (by omega_using [hw]))) fun s' ⟨ax, sp⟩ =>
      ⟨by rw [ax]; exact pubSw_W hpub (by omega_using [hw, h7]) hw, by rw [sp]; exact pubSw_esp hpub⟩

/-- Our caller's registers, outside the regions the tag is computed in. -/
theorem saved_tagFrame {Ctx St W SP : BitVec 32} (L : Lay4 Ctx St W SP 1536) :
    ∀ r ∈ tagFrame St W SP 0, (savedR W).Disjoint r := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using (L.st_w (a := 0) (n := 32) (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

/-- The return address, outside the regions the tag is computed in. -/
theorem ret_tagFrame {p : BitVec 32 × (Nat → BitVec 32)} (FL : FinL p) :
    ∀ r ∈ tagFrame (p.2 1) (p.2 6) p.1 0, (⟨w64 p.1, 4⟩ : Region).Disjoint r := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact FL.r_s.sub_right (Region.sub_prefix (by decide))
  · exact FL.r_w.sub_right (Lay.wSub (by decide))
  · exact FL.r_w.sub_right (Lay.wSub (by decide))
  · exact FL.r_w.sub_right (Lay.wSub (by decide))
  · exact ret_below FL.L.sp

/-- The exit of `finish` and `verify`, after the pieces wrote within `rs`,
apart from our caller's registers and the return address. -/
theorem fin_exit {nA w : Nat} {p : BitVec 32 × (Nat → BitVec 32)} {s₀ s₁ s : State} (h₁ : FinEnt nA w p s₀ s₁)
    (FL : FinL p) (he : Env (p.2 0) (p.2 1) (p.2 6) p.1 s) {rs : List Region} (hf : Frame rs s₁.mem s.mem)
    (hS : ∀ r ∈ rs, (savedR (p.2 6)).Disjoint r) (hR : ∀ r ∈ rs, (⟨w64 p.1, 4⟩ : Region).Disjoint r) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ s'.mem = s.mem ∧ s'.gpr .eax = s.gpr .eax := by
  have esp := pubSw_esp h₁.pub
  have hsv : SavedAt s.mem (p.2 6) s₀ := h₁.saved.frame hf hS
  have rE : ∀ r ∈ [(⟨w64 (p.2 6) + BitVec.ofNat 64 128, 2432⟩ : Region)], (⟨w64 p.1, 4⟩ : Region).Disjoint r :=
    fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact FL.r_w.sub_right (Lay.wSub (by decide))
  have hret : s.mem.readW (w64 (s₀.gpr .esp)) 32 = s₀.mem.readW (w64 (s₀.gpr .esp)) 32 := by
    rw [esp, ret_kept hf hR, ret_kept h₁.frame rE]
  exact WP.mono (exit_ok he.ebp (by rw [he.esp, esp]) (covers_left he.wW) FL.L.fw hsv hret)
    fun s' ⟨abi, m', ax, _, _⟩ => ⟨abi, m', ax⟩

/-- The streaming state and the key context, as the pieces see them after the entry. -/
theorem fin_repr {nA w : Nat} {p : BitVec 32 × (Nat → BitVec 32)} {s₀ s₁ : State} (h₁ : FinEnt nA w p s₀ s₁)
    (L : Lay4 (p.2 0) (p.2 1) (p.2 6) p.1 1536) {iv a c : List Byte}
    (hr : StreamRepr s₀.mem (w64 (p.2 1)) (ctxCiph s₀.mem (w64 (p.2 0))) (ctxH s₀.mem (w64 (p.2 0))) iv a c) :
    StreamRepr s₁.mem (w64 (p.2 1)) (ciphOf s₁.mem (p.2 0)) (Hk s₁.mem (p.2 0)) iv a c ∧
      ciphOf s₁.mem (p.2 0) = ctxCiph s₀.mem (w64 (p.2 0)) ∧ Hk s₁.mem (p.2 0) = ctxH s₀.mem (w64 (p.2 0)) := by
  have hC : ciphOf s₁.mem (p.2 0) = ctxCiph s₀.mem (w64 (p.2 0)) :=
    ciph_frame h₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.cw.sub_right (Lay.wSub (by decide)))
  have hH : Hk s₁.mem (p.2 0) = ctxH s₀.mem (w64 (p.2 0)) := by
    rw [ctxH_eq]
    exact blockAt_frame h₁.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide)
  refine ⟨?_, hC, hH⟩
  rw [hC, hH]
  exact streamRepr_frame h₁.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    simpa using L.st_w (a := 0) (n := 80) (d := 128) (k := 2432) (by decide) (.inr ⟨by decide, by decide⟩)) hr

/-- A word of `W` outside the regions the tag is computed in. -/
theorem slot_tagFrame {Ctx St W SP : BitVec 32} (L : Lay4 Ctx St W SP 1536) {m m' : Mem}
    (hf : Frame (tagFrame St W SP 0) m m') {o : Nat} (h₁ : 128 ≤ o) (h₂ : o + 4 ≤ 240) :
    slotv m' W o = slotv m W o := by
  rw [slotv_eq, slotv_eq]
  refine slot_frame hf fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · have := (L.st_w (a := 0) (n := 32) (d := o) (k := 4) (by decide) (.inr ⟨by omega_using [h₁], by omega_using [h₂]⟩)).symm
    rwa [BitVec.add_zero] at this
  · exact Lay.w_w (d := 96) (k := 16) (.inr (by omega_using [h₁])) (by omega_using [h₂]) (by decide)
  · exact Lay.w_w (d := 0) (k := 16) (.inr (by omega_using [h₁])) (by omega_using [h₂]) (by decide)
  · exact Lay.w_w (d := 240) (k := 2320) (.inl (by omega_using [h₂])) (by omega_using [h₂]) (by decide)
  · exact (L.stk_w (by omega_using [h₂])).symm

theorem streamFinish_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun (s₀ : State) s => finPre s₀ ∧ pubSw 8 6 s₀ = p ∧ s = s₀) (streamFinish vg.callees)
      (fun s₀ s' => abiPreserved s₀ s' ∧ streamFinishX86.post s₀ s') := by
  by_cases hex : ∃ s₀, finPre s₀ ∧ pubSw 8 6 s₀ = p
  swap
  · exact Pc.vacuous fun a s ⟨h₁, h₂, _⟩ => hex ⟨a, h₁, h₂⟩
  obtain ⟨z, hz, hzp⟩ := hex
  have FL : FinL p := (finPre_of hz).fl rfl (by decide) hzp
  have L := FL.L
  obtain ⟨-, fT, tw, rt⟩ := finPre_tag hz
  rw [pubSw_last hzp (m := 7) (by decide) rfl] at fT
  rw [pubSw_last hzp (m := 7) (by decide) rfl, pubSw_W hzp (m := 7) (by decide) rfl] at tw
  rw [pubSw_last hzp (m := 7) (by decide) rfl, pubSw_esp hzp] at rt
  rw [streamFinish_eq]
  refine Pc.seq (finEntry_pc 8 7 rfl (by decide) [(6, tpO)] (by decide) (by decide) finPre (fun _ h => finPre_of h) p
    (by taint_decide) (by taint_decide)) (Pc.seq (Pc.lift (finTag_pc L (o := 0) (.inl rfl)) (fun _ s => s.mem)
      fun s₀ s h => ⟨h.1.fin, rfl⟩) ?_)
  -- The tag copied to `tag`.
  refine Pc.seq (Pc.of (I := fun s => WEnv (p.2 6) s ∧ slotv s.mem (p.2 6) tpO = p.2 7 ∧
      Covers [⟨w64 (p.2 7), 16⟩] s.wr)
    (R := fun s s' => bytesAt s'.mem (w64 (p.2 7)) 16 = bytesAt s.mem (w64 (p.2 6) + BitVec.ofNat 64 0) 16 ∧
      Frame [⟨w64 (p.2 7), 16⟩] s.mem s'.mem ∧ s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esi = s.gpr .esi ∧
      s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr)
    (fun s hs => tagOut_ok hs.1 (by decide) hs.2.1 hs.2.2 fT) (tagOut_ct rfl fun s hs => ⟨hs.1, hs.2.1⟩) _
    (fun s₀ s' ⟨s, ⟨h₁, hv, hpre⟩, fo, rd, wr⟩ => ⟨⟨fo.env.ebp, fo.env.wW, L.fw⟩, by
      rw [slot_tagFrame L fo.frame (by decide) (by decide), hv (6, tpO) (by simp),
        pubSw_last h₁.pub (m := 7) (by decide) rfl], by
      rw [wr, h₁.wr, ← pubSw_last h₁.pub (m := 7) (by decide) rfl]; exact (finPre_tag hpre).1⟩)) ?_
  -- The exit.
  refine Pc.taint [.ebp] (fun s₀ s'' ⟨s', ⟨s, ⟨h₁, _, _⟩, fo, _, _⟩, b, f, bp, si, sp, rd, wr⟩ => ?_)
    (fun _ _ s₁ s₂ ⟨_, ⟨_, _, h₁, _⟩, _, _, e₁, _⟩ ⟨_, ⟨_, _, h₂, _⟩, _, _, e₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [e₁, e₂, h₁.env.ebp, h₂.env.ebp]) (by taint_decide)
  have tS : ∀ r ∈ [(⟨w64 (p.2 7), 16⟩ : Region)], (⟨w64 (p.2 6) + BitVec.ofNat 64 ctxO, 4⟩ : Region).Disjoint r :=
    fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (tw.sub_right (Lay.wSub (by decide))).symm
  have he : Env (p.2 0) (p.2 1) (p.2 6) p.1 s'' := fo.env.keep bp si sp rd wr (slot_frame f tS)
  have hf : Frame (tagFrame (p.2 1) (p.2 6) p.1 0 ++ [⟨w64 (p.2 7), 16⟩]) s.mem s''.mem :=
    (fo.frame.mono fun r hr => List.mem_append_left _ hr).trans (f.mono fun r hr => List.mem_append_right _ hr)
  refine WP.mono (fin_exit h₁ FL he hf (fun r hr => ?_) (fun r hr => ?_)) fun s₃ ⟨abi, m', _⟩ =>
    ⟨abi, fun iv a c hr hl ht => ?_⟩
  · rcases List.mem_append.mp hr with hr | hr
    · exact saved_tagFrame L r hr
    · simp only [List.mem_singleton] at hr; subst hr; exact (tw.sub_right (Lay.wSub (by decide))).symm
  · rcases List.mem_append.mp hr with hr | hr
    · exact ret_tagFrame FL r hr
    · simp only [List.mem_singleton] at hr; subst hr; exact rt
  have hA : ∀ i, i < 6 → arg s₀ i = p.2 i := fun i hi => pubSw_arg h₁.pub (by omega_using [hi]) (by omega_using [hi]) (by omega_using [hi])
  rw [hA 0 (by decide), hA 1 (by decide)] at hr
  rw [hA 2 (by decide), hA 3 (by decide)] at hl
  rw [hA 4 (by decide), hA 5 (by decide)] at ht
  rw [hA 0 (by decide), pubSw_last h₁.pub (m := 7) (by decide) rfl, m', b]
  obtain ⟨hr₁, hC, hH⟩ := fin_repr h₁ L hr
  have := fo.tag iv a c hr₁ hl ht
  rw [hC, hH] at this
  exact this

theorem streamFinish_correct (s : State) (hs : streamFinishX86.pre s) :
    ∃ t s', Exec isa (streamFinish vg.callees) s t s' ∧ abiPreserved s s' ∧ streamFinishX86.post s s' :=
  (streamFinish_pc (pubSw 8 6 s)).wp s s ⟨hs, rfl, rfl⟩

theorem streamFinish_ct : ConstantTime isa streamFinishX86.pre streamFinishX86.pub (streamFinish vg.callees) :=
  Pc.constantTime (pubSw 8 6) (fun _ _ _ _ h => pubSw_eq (by decide) h) streamFinish_pc fun _ hs => ⟨hs, rfl, rfl⟩

end VG.Proof.Sm4Gcm.X86

end

end

/-!
# SM4-GCM on x86: `vg_aes_gcm_stream_verify`

Untrusted: everything here is checked by Lean. The entry (`finEntry_pc`,
keeping `tag` and `tag_len` too), the tag length checked (`tagLenOk_pc`),
and then either 0, or the received tag copied from `tag` (`recv_ok`), the
tag computed (`finTag_pc`) and compared (`cmp_ok`), as one `Pc`
(`streamVerify_pc`): correct (`streamVerify_correct`) and constant time
(`streamVerify_ct`). Only the lengths and the pointers affect the
branches: the comparison has none.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86

variable {vg : VG.Proof.AesGcm.X86.GcmImpl}

open VG VG.X86 VG.X86.RegUpd VG.Impl.Sm4Gcm.X86 VG.WriteBytes VG.Proof.AesGcm.X86
open VG.Impl.AesGcm.X86 hiding ctrCall keyCall ctrArgs cryptWhole cryptTail crypt tag init cryptEntry
  streamEncrypt streamDecrypt finEntry finTag streamFinish streamVerify oneEntry oneTag oneCrypt «seal» «open»
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr fullTag zeros)
open VG.Spec.Gcm (ctxH)
open VG.Spec.Sm4.Gcm (ctxCiph)

theorem streamVerify_eq : (streamVerify vg.callees) = .seq (entry 8 (([.mov .esi (argOp 1)] : List Instr) ++
    ((finKeeps ++ [(6, tpO), (7, tglO)]).flatMap (fun (p : Nat × Nat) => keep p.1 p.2) ++ [])))
    (.seq tagLenOk (.seq (.ite .e (.block [.mov .eax (imm 0)])
      (.seq recv (.seq (finTag vg.callees 0) (cmp 0)))) (.block restore))) := rfl

/-- Where the received tag is copied. -/
abbrev rR (W : BitVec 32) : Region := ⟨w64 W + BitVec.ofNat 64 rO, 16⟩

/-- The kept values, after the received tag is copied. -/
theorem FinIn.frameR {Ctx St W SP : BitVec 32} {al ah xl xh : BitVec 32} {s s' : State}
    (h : FinIn Ctx St W SP al ah xl xh s) (hf : Frame [rR W] s.mem s'.mem) (hbp : s'.gpr .ebp = s.gpr .ebp)
    (hsi : s'.gpr .esi = s.gpr .esi) (hsp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    FinIn Ctx St W SP al ah xl xh s' := by
  obtain sl : ∀ o, o + 4 ≤ rO → slotv s'.mem W o = slotv s.mem W o := fun o ho => by
    have ho' : o + 4 ≤ 196 := ho
    rw [slotv_eq, slotv_eq]
    exact slot_frame hf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl ho') (by omega_using [ho']) (by decide)
  obtain hc := sl ctxO (by decide)
  rw [slotv_eq, slotv_eq] at hc
  exact ⟨h.env.keep hbp hsi hsp hrd hwr hc, by rw [sl _ (by decide)]; exact h.al, by rw [sl _ (by decide)]; exact h.ah,
    by rw [sl _ (by decide)]; exact h.xl, by rw [sl _ (by decide)]; exact h.xh⟩

/-- The received tag, outside the regions the tag is computed in. -/
theorem rR_tagFrame {Ctx St W SP : BitVec 32} (L : Lay4 Ctx St W SP 1536) :
    ∀ r ∈ tagFrame St W SP 0, (rR W).Disjoint r := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · have := (L.st_w (a := 0) (n := 32) (d := 196) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm
    rwa [BitVec.add_zero] at this
  · exact Lay.w_w (d := 96) (k := 16) (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (d := 0) (k := 16) (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (d := 240) (k := 2320) (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

/-- After the entry and the tag length checked. -/
structure VT (p : BitVec 32 × (Nat → BitVec 32)) (ok : Bool) (s₀ s₁ s : State) : Prop where
  ent : FinEnt 9 8 p s₀ s₁
  vp : verifyPre s₀
  fin : FinIn (p.2 0) (p.2 1) (p.2 6) p.1 (p.2 2) (p.2 3) (p.2 4) (p.2 5) s
  mem : s.mem = s₁.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  tgl : slotv s.mem (p.2 6) tglO = BitVec.ofNat 32 (p.2 7).toNat
  tp : slotv s.mem (p.2 6) tpO = p.2 8
  zf : s.zf = some (!ok)

/-- What `verify` ends with, before restoring our caller's registers. -/
def VOut (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop :=
  ∃ s₁, FinEnt 9 8 p s₀ s₁ ∧ Env (p.2 0) (p.2 1) (p.2 6) p.1 s ∧
    Frame (rR (p.2 6) :: tagFrame (p.2 1) (p.2 6) p.1 0) s₁.mem s.mem ∧ streamVerifyX86.post s₀ s

theorem streamVerify_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun (s₀ : State) s => verifyPre s₀ ∧ pubSw 9 6 s₀ = p ∧ s = s₀) (streamVerify vg.callees)
      (fun s₀ s' => abiPreserved s₀ s' ∧ streamVerifyX86.post s₀ s') := by
  by_cases hex : ∃ s₀, verifyPre s₀ ∧ pubSw 9 6 s₀ = p
  swap
  · exact Pc.vacuous fun a s ⟨h₁, h₂, _⟩ => hex ⟨a, h₁, h₂⟩
  obtain ⟨z, hz, hzp⟩ := hex
  obtain FL : FinL p := (verifyPre_of hz).fl rfl (by decide) hzp
  have L := FL.L
  obtain a8 : ∀ {s₀ : State}, pubSw 9 6 s₀ = p → arg s₀ 7 = p.2 7 := fun h =>
    pubSw_arg h (by decide) (by decide) (by decide)
  obtain a7 : ∀ {s₀ : State}, pubSw 9 6 s₀ = p → arg s₀ 6 = p.2 8 := fun h => pubSw_last h (by decide) rfl
  obtain ⟨-, fT, tw⟩ := verifyPre_tag hz
  rw [a7 hzp, a8 hzp] at fT
  rw [a7 hzp, a8 hzp, pubSw_W hzp (m := 8) (by decide) rfl] at tw
  generalize hok : Spec.Gcm.tagLenOk (p.2 7).toNat = ok
  obtain ht32 : (p.2 7).toNat < 2 ^ 32 := (p.2 7).isLt
  rw [streamVerify_eq]
  -- The entry, then the tag length.
  refine Pc.seq (finEntry_pc 9 8 rfl (by decide) [(6, tpO), (7, tglO)] (by decide) (by decide) verifyPre
    (fun _ h => verifyPre_of h) p (by taint_decide) (by taint_decide)) ?_
  refine Pc.seq (Q := fun s₀ s => ∃ s₁, VT p ok s₀ s₁ s) (Pc.mono (Pc.lift (tagLenOk_pc (W := p.2 6) ht32)
    (fun _ s => s) fun s₀ s ⟨h, hv, _⟩ => ⟨rfl, h.fin.env.ebp, L.aW (by decide), h.fin.env.wIn' (by decide), by
      rw [hv (7, tglO) (by simp), a8 h.pub, ofNat_toNat32]⟩) (fun _ _ h => h)
    fun s₀ s ⟨s₁, ⟨h₁, hv, hpre⟩, ⟨tl, hz⟩, _, _⟩ => ⟨s₁, h₁, hpre, h₁.fin.keep
      (by rw [tl.other _ (by decide) (by decide)]) (by rw [tl.other _ (by decide) (by decide)])
      (by rw [tl.other _ (by decide) (by decide)]) tl.mem tl.rd tl.wr,
      tl.mem, by rw [tl.rd, h₁.rd], by rw [tl.wr, h₁.wr], by rw [tl.mem, hv (7, tglO) (by simp), a8 h₁.pub, ofNat_toNat32],
      by rw [tl.mem, hv (6, tpO) (by simp), a7 h₁.pub], by rw [hz, hok]⟩) ?_
  refine Pc.seq (Q := VOut p) (Pc.ite (!ok) (fun _ _ ⟨_, h⟩ => h.zf) (fun hb => ?_) (fun hb => ?_)) ?_
  -- A tag length `tagLenOk` does not allow.
  · have hf : ok = false := by simpa using hb
    refine Pc.taint [] (fun s₀ s ⟨s₁, h⟩ => ?_) (fun _ _ _ _ _ _ _ h => by simp at h) (by taint_decide)
    have he := h.fin.env
    refine WP.of_runBlock ⟨_, by xrun [], ?_⟩
    refine ⟨s₁, h.ent, he.keep (by regs []) (by regs []) (by regs []) (by mems []) (by mems []) (by mems []), ?_, ?_⟩
    · mems []; rw [h.mem]; exact Frame.refl _ _
    · simp only [streamVerifyX86, ret32_eq]
      intro iv a c _ _ _
      obtain e : Spec.Gcm.tagLenOk (arg s₀ 7).toNat = false := by rw [a8 h.ent.pub, hok, hf]
      simp only [e, Bool.false_eq_true, false_and, ↓reduceIte]
      regs []; rfl
  -- An allowed one: the tags compared.
  · have hT : ok = true := by simpa using hb
    have ht := hok
    rw [hT] at ht
    obtain ht' : 1 ≤ (p.2 7).toNat ∧ (p.2 7).toNat ≤ 16 := by
      simp only [Spec.Gcm.tagLenOk, Bool.and_eq_true, decide_eq_true_eq] at ht
      omega_using [ht]
    obtain ⟨t1, t16⟩ := ht'
    -- The received tag copied.
    refine Pc.seq (Pc.of (I := fun s => WEnv (p.2 6) s ∧ slotv s.mem (p.2 6) tglO = BitVec.ofNat 32 (p.2 7).toNat ∧
        slotv s.mem (p.2 6) tpO = p.2 8 ∧ Covers [⟨w64 (p.2 8), (p.2 7).toNat⟩] (s.rd ++ s.wr))
      (R := fun s s' => bytesAt s'.mem (w64 (p.2 6) + BitVec.ofNat 64 rO) 16 =
          bytesAt s.mem (w64 (p.2 8)) (p.2 7).toNat ++ zeros (16 - (p.2 7).toNat) ∧
        Frame [⟨w64 (p.2 6) + BitVec.ofNat 64 rO, 16⟩] s.mem s'.mem ∧ s'.gpr .ebp = s.gpr .ebp ∧
        s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr)
      (fun s hs => recv_ok hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 fT tw t1 t16)
      (recv_ct fun s hs => ⟨hs.1, hs.2.1, hs.2.2.1⟩) _
      (fun s₀ s ⟨s₁, h⟩ => ⟨⟨h.fin.env.ebp, h.fin.env.wW, L.fw⟩, h.tgl, h.tp, by
        rw [h.rd, h.wr, ← a7 h.ent.pub, ← a8 h.ent.pub]; exact (verifyPre_tag h.vp).1⟩)) ?_
    -- The tag computed.
    refine Pc.seq (Pc.lift (finTag_pc L (o := 0) (.inl rfl) (al := p.2 2) (ah := p.2 3)
      (xl := p.2 4) (xh := p.2 5)) (fun _ s => s.mem)
      fun s₀ s' ⟨s, ⟨s₁, h⟩, _, f, g1, g2, g3, rd, wr⟩ => ⟨h.fin.frameR f g1 g2 g3 rd wr, rfl⟩) ?_
    -- Compared.
    refine Pc.mono (Pc.of (I := fun s => WEnv (p.2 6) s ∧ slotv s.mem (p.2 6) tglO = BitVec.ofNat 32 (p.2 7).toNat)
      (R := fun s s' => s'.gpr .eax = BitVec.ofNat 32
          (if bytesAt s.mem (w64 (p.2 6) + BitVec.ofNat 64 0) (p.2 7).toNat ++ zeros (16 - (p.2 7).toNat) =
              bytesAt s.mem (w64 (p.2 6) + BitVec.ofNat 64 rO) 16 then 1 else 0) ∧
        Frame [⟨w64 (p.2 6) + BitVec.ofNat 64 vO, 16⟩] s.mem s'.mem ∧ s'.gpr .ebp = s.gpr .ebp ∧
        s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr)
      (fun s hs => cmp_ok hs.1 hs.2 t1 t16 (by decide)) (cmp_ct (.inl rfl) fun s hs => hs) _
      (fun s₀ s'' ⟨s', ⟨s, ⟨s₁, h⟩, _, f, _⟩, fo, _, _⟩ => ⟨⟨fo.env.ebp, fo.env.wW, L.fw⟩, by
        rw [slot_tagFrame L fo.frame (by decide) (by decide), slotv_eq,
          slot_frame f fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Lay.w_w (a := 180) (n := 4) (d := 196) (k := 16) (.inl (by decide)) (by decide) (by decide),
          ← slotv_eq]
        exact h.tgl⟩)) (fun _ _ h => h) ?_
    intro s₀ s₃ ⟨s₂, ⟨s', ⟨s, ⟨s₁, h⟩, b, f, g1, g2, g3, rd, wr⟩, fo, rd₂, wr₂⟩, a₃, f₃, e1, e2, e3, rd₃, wr₃⟩
    obtain f₁ : Frame [rR (p.2 6)] s₁.mem s'.mem := by rw [← h.mem]; exact f
    refine ⟨s₁, h.ent, fo.env.keep e1 e2 e3 rd₃ wr₃ ?_, ?_, ?_⟩
    · exact slot_frame f₃ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Lay.w_w (a := 144) (n := 4) (d := 240) (k := 16) (.inl (by decide)) (by decide) (by decide)
    · refine f₁.mono (fun r hr => by simp at hr; subst hr; simp) |>.trans
        (fo.frame.mono (fun r hr => List.mem_cons_of_mem _ hr) |>.trans
        (f₃.sub (fun r hr => ⟨wsR (p.2 6), by simp, by
          simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by decide) (by decide)⟩)))
    · have hA : ∀ i, i < 6 → arg s₀ i = p.2 i := fun i hi => pubSw_arg h.ent.pub (by omega_using [hi]) (by omega_using [hi]) (by omega_using [hi])
      simp only [streamVerifyX86, ret32_eq]
      intro iv a c hr hl hc
      rw [hA 0 (by decide), hA 1 (by decide)] at hr
      rw [hA 2 (by decide), hA 3 (by decide)] at hl
      rw [hA 4 (by decide), hA 5 (by decide)] at hc
      rw [hA 0 (by decide), a7 h.ent.pub, a8 h.ent.pub]
      obtain ⟨hr₁, hC, hH⟩ := fin_repr h.ent L hr
      obtain hC' : ciphOf s'.mem (p.2 0) = ciphOf s₁.mem (p.2 0) :=
        ciph_frame f₁ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact L.cw.sub_right (Lay.wSub (by decide)))
      obtain hH' : Hk s'.mem (p.2 0) = Hk s₁.mem (p.2 0) :=
        blockAt_frame f₁ fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide)
      obtain hr₂ : StreamRepr s'.mem (w64 (p.2 1)) (ciphOf s'.mem (p.2 0)) (Hk s'.mem (p.2 0)) iv a c := by
        rw [hC', hH']
        exact streamRepr_frame f₁ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          simpa using L.st_w (a := 0) (n := 80) (d := 196) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)) hr₁
      obtain tag := fo.tag iv a c hr₂ hl hc
      rw [hC', hH', hC, hH] at tag
      generalize fullTag (ctxCiph s₀.mem (w64 (p.2 0))) (ctxH s₀.mem (w64 (p.2 0))) iv a c = T at tag ⊢
      obtain bW : bytesAt s₂.mem (w64 (p.2 6) + BitVec.ofNat 64 0) (p.2 7).toNat = T.take (p.2 7).toNat := by
        rw [← tag, bytesAt_take _ _ t16]
      obtain bR : bytesAt s₂.mem (w64 (p.2 6) + BitVec.ofNat 64 rO) 16 =
          bytesAt s₀.mem (w64 (p.2 8)) (p.2 7).toNat ++ zeros (16 - (p.2 7).toNat) := by
        rw [bytesAt_frame fo.frame (rR_tagFrame L) (by decide), b, h.mem,
          bytesAt_frame h.ent.frame (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact tw.sub_right (Lay.wSub (by decide))) (by omega_using [])]
      simp only [bW, bR, List.append_left_inj] at a₃
      simp only [hok, hT, true_and]
      by_cases hX : T.take (p.2 7).toNat = bytesAt s₀.mem (w64 (p.2 8)) (p.2 7).toNat
      · simp only [hX, ↓reduceIte] at a₃ ⊢
        rw [a₃]; rfl
      · simp only [hX, ↓reduceIte] at a₃ ⊢
        rw [a₃]; rfl
  -- The exit.
  refine Pc.taint [.ebp] (fun s₀ s ⟨s₁, h₁, he, hf, hpost⟩ => ?_) (fun _ _ s₁ s₂ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ebp, h₂.ebp]) (by taint_decide)
  refine WP.mono (fin_exit h₁ FL he hf (fun r hr => ?_) (fun r hr => ?_)) fun s' ⟨abi, _, ax⟩ => ⟨abi, ?_⟩
  · rcases List.mem_cons.mp hr with rfl | hr
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact saved_tagFrame L r hr
  · rcases List.mem_cons.mp hr with rfl | hr
    · exact FL.r_w.sub_right (Lay.wSub (by decide))
    · exact ret_tagFrame FL r hr
  simp only [streamVerifyX86, ret32_eq] at hpost ⊢
  rw [ax]
  exact hpost

theorem streamVerify_correct (s : State) (hs : streamVerifyX86.pre s) :
    ∃ t s', Exec isa (streamVerify vg.callees) s t s' ∧ abiPreserved s s' ∧ streamVerifyX86.post s s' :=
  (streamVerify_pc (pubSw 9 6 s)).wp s s ⟨hs, rfl, rfl⟩

theorem streamVerify_ct : ConstantTime isa streamVerifyX86.pre streamVerifyX86.pub (streamVerify vg.callees) :=
  Pc.constantTime (pubSw 9 6) (fun _ _ _ _ h => pubSw_eq (by decide) h) streamVerify_pc fun _ hs => ⟨hs, rfl, rfl⟩

end VG.Proof.Sm4Gcm.X86
