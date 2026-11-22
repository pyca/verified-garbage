module

import VerifiedGarbage.Proof.Sm4Gcm.X86.Open
public import VerifiedGarbage.Proof.Sm4Gcm.Scratch
public import VerifiedGarbage.Proof.Sm4Gcm.X86.CtrCall
public import VerifiedGarbage.Proof.Sm4Gcm.X86.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sm4.X86.Lit
import VerifiedGarbage.Proof.Sm4.X86.Ctr32Lit
import VerifiedGarbage.Proof.Sm4.X86.LayersLit
public import VerifiedGarbage.Proof.AesGcm.X86.Frame
public import VerifiedGarbage.Impl.StackScratch.X86
import VerifiedGarbage.Proof.Framework.X86.StackScratch
public import VerifiedGarbage.Proof.AesGcm.X86.Top
meta import VerifiedGarbage.Proof.AesGcm.X86.Top
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Impl.Sm4Gcm.X86
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Framework.X86.Call
meta import VerifiedGarbage.TCB.X86.Isa
meta import VerifiedGarbage.TCB.X86.State
meta import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.AesGcm.X86.Loops
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.AesGcm.X86.Absorb
meta import VerifiedGarbage.Proof.AesGcm.X86.Loops
meta import VerifiedGarbage.Proof.Cmac.Block32
meta import VerifiedGarbage.Proof.Cmac.Mem32
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesGcm.X86.Flush
meta import VerifiedGarbage.Proof.AesGcm.X86.Flush
meta import VerifiedGarbage.Proof.Gcm.Ctr
public import VerifiedGarbage.Proof.Sm4Gcm.X86.CryptTail
meta import VerifiedGarbage.Proof.Sm4Gcm.X86.CryptTail
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
meta import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
public import VerifiedGarbage.Proof.AesGcm.X86.TextAbsorb
meta import VerifiedGarbage.Proof.AesGcm.X86.TextAbsorb
meta import VerifiedGarbage.Proof.Sm4Gcm.X86.Contract
meta import VerifiedGarbage.Proof.Sm4Gcm.X86.CtrCall
import VerifiedGarbage.Proof.AesGcm.X86.Cmp
meta import VerifiedGarbage.Proof.AesGcm.X86.Cmp
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Gcm.Be64
meta import VerifiedGarbage.Proof.Gcm.Be64

/-! ### `Sm4Gcm.X86.StreamVerify`, which only this module used -/

section

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

end

end

/-! ### `Sm4Gcm.X86.StreamDecrypt`, which only this module used -/

section

/-! ### `Sm4Gcm.X86.StreamEncrypt`, which this module and modules that import it used -/

section

/-! ### `Sm4Gcm.X86.StreamCrypt`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on x86: the entry of `stream_encrypt` and `stream_decrypt`

Untrusted: everything here is checked by Lean. What the precondition
gives (`CrPure`), the entry (`crEntry_pc`), the text as `crypt` takes it
(`setText_ok`) and as `textAbsorb` takes it.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Sm4Gcm.X86 VG.WriteBytes VG.Proof.AesGcm.X86
open VG.Impl.AesGcm.X86 hiding ctrCall keyCall ctrArgs cryptWhole cryptTail crypt tag init cryptEntry
  streamEncrypt streamDecrypt finEntry finTag streamFinish streamVerify oneEntry oneTag oneCrypt «seal» «open»
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr)
open VG.Spec.Gcm (ctxH)
open VG.Spec.Sm4.Gcm (ctxCiph)

abbrev crKeeps : List (Nat × Nat) :=
  [(0, ctxO), (2, alO), (3, ahO), (4, xlO), (5, xhO), (6, dataO), (7, lenO)]

/-- The facts of the precondition about the public data `p` alone. -/
structure CrPure (p : BitVec 32 × (Nat → BitVec 32)) : Prop where
  lay : Lay4 (p.2 0) (p.2 1) (p.2 8) p.1 1536
  fd : (p.2 6).toNat + (p.2 7).toNat ≤ 2 ^ 32
  dctx : (⟨w64 (p.2 0), 256⟩ : Region).Disjoint ⟨w64 (p.2 6), (p.2 7).toNat⟩
  dst : (⟨w64 (p.2 6), (p.2 7).toNat⟩ : Region).Disjoint ⟨w64 (p.2 1), 80⟩
  dw : (⟨w64 (p.2 6), (p.2 7).toNat⟩ : Region).Disjoint ⟨w64 (p.2 8), 2560⟩
  dstk : (below p.1 1536).Disjoint ⟨w64 (p.2 6), (p.2 7).toNat⟩
  r_s : (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 1), 80⟩
  r_d : (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 6), (p.2 7).toNat⟩
  r_w : (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 8), 2560⟩
  sp : 1536 ≤ p.1.toNat

theorem crPure_of {p : BitVec 32 × (Nat → BitVec 32)} {s : State} (h : streamCryptPre s) (hp : pubOf 9 s = p) :
    CrPure p := by
  simp only [streamCryptPre] at h
  sig_split h
  rename_i hdrop0 hdrop1 d_cs d_cd d_cw hdrop5 d_sd d_sw hdrop8 d_dw hdrop10 hdrop11 hdrop12 r_s r_d r_w
    hdrop16 k_c k_s k_d k_w hdrop21 fc fs fd fw sp
  clear hdrop0 hdrop1 hdrop5 hdrop8 hdrop10 hdrop11 hdrop12 hdrop16 hdrop21 h
  rw [ofNat_lit, below_eq sp] at k_c k_s k_d k_w
  have a0 := pubOf_arg hp (i := 0) (by decide); have a1 := pubOf_arg hp (i := 1) (by decide)
  have a6 := pubOf_arg hp (i := 6) (by decide); have a7 := pubOf_arg hp (i := 7) (by decide)
  have a8 := pubOf_arg hp (i := 8) (by decide)
  have e := pubOf_esp hp
  simp only [a0, a1, a6, a7, a8, e] at d_cs d_cd d_cw d_sd d_sw d_dw r_s r_d r_w k_c k_s k_d k_w fc fs fd fw sp
  exact ⟨Lay4.of fc fs fw (by decide) sp d_cs d_cw (d_sw.sub_right (Region.sub_prefix (by decide)))
    (d_sw.sub_right (Lay.wSub (by decide))) k_c k_s k_w, fd, d_cd, d_sd.symm, d_dw, k_d, r_s, r_d, r_w, sp⟩

/-- After the entry of `stream_encrypt` or `stream_decrypt`. -/
structure CEnt (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  pre : streamCryptPre s₀
  pub : pubOf 9 s₀ = p
  env : Env (p.2 0) (p.2 1) (p.2 8) p.1 s
  ta : TaSl (p.2 8) (p.2 6) (p.2 7).toNat (p.2 2) (p.2 4) (p.2 5) s.mem
  ah : slotv s.mem (p.2 8) ahO = p.2 3
  saved : SavedAt s.mem (p.2 8) s₀
  frame : Frame [⟨w64 (p.2 8) + BitVec.ofNat 64 128, 2432⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem crEntry_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun (s₀ : State) s => streamCryptPre s₀ ∧ pubOf 9 s₀ = p ∧ s = s₀)
      (entry 8 (([.mov .esi (argOp 1)] : List Instr) ++ (crKeeps.flatMap (fun p => keep p.1 p.2) ++ []))) (CEnt p) := by
  refine ⟨fun s₀ s ⟨hpre, hpub, hs⟩ => ?_, ?_⟩
  · subst s
    have hp := hpre
    simp only [streamCryptPre] at hp
    sig_split hp
    rename_i hrd hwr hdrop2 hdrop3 hdrop4 hdrop5 hdrop6 hdrop7 hdrop8 hdrop9 hdrop10 d_wa hdrop12 hdrop13
      hdrop14 hdrop15 hdrop16 hdrop17 hdrop18 hdrop19 hdrop20 hdrop21 hdrop22 hdrop23 hdrop24 fw hdrop26
    clear hdrop2 hdrop3 hdrop4 hdrop5 hdrop6 hdrop7 hdrop8 hdrop9 hdrop10 hdrop12 hdrop13 hdrop14 hdrop15
      hdrop16 hdrop17 hdrop18 hdrop19 hdrop20 hdrop21 hdrop22 hdrop23 hdrop24 hdrop26
    have fa := hp
    clear hp
    have a : ∀ i, i < 9 → arg s₀ i = p.2 i := fun i hi => pubOf_arg hpub hi
    have esp := pubOf_esp hpub
    have wW : Covers [⟨w64 (arg s₀ 8), 2560⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
    have rA : Covers [argsR (s₀.gpr .esp) 9] (s₀.rd ++ s₀.wr) := by
      rw [argsR_eq, hrd, hwr]; exact covers_of_mem (by simp)
    have aw : (argsR (s₀.gpr .esp) 9).Disjoint ⟨w64 (arg s₀ 8), 2560⟩ := by rw [argsR_eq]; exact d_wa.symm
    refine entry_ok crKeeps [] (by decide) (by decide) (by decide) (by decide) rfl rfl wW rA aw (by omega_using [fa]) fw
      fun s₂ e => ?_
    have he : Env (arg s₀ 0) (arg s₀ 1) (arg s₀ 8) (s₀.gpr .esp) s₂ :=
      ⟨e.ebp, e.esi, e.esp, by rw [e.rd, e.wr, hrd]; exact covers_of_mem (by simp),
        by rw [e.wr, hwr]; exact covers_of_mem (by simp), by rw [e.wr]; exact wW,
        e.slots (0, ctxO) (by simp)⟩
    refine ⟨s₂, rfl, hpre, hpub, ?_, ?_, ?_, ?_, ?_, e.rd, e.wr⟩
    · rw [← a 0 (by decide), ← a 1 (by decide), ← a 8 (by decide), ← esp]; exact he
    · rw [← a 2 (by decide), ← a 4 (by decide), ← a 5 (by decide), ← a 6 (by decide), ← a 7 (by decide),
        ← a 8 (by decide)]
      exact ⟨e.slots (6, dataO) (by simp), by rw [e.slots (7, lenO) (by simp), ofNat_toNat32],
        e.slots (2, alO) (by simp), e.slots (4, xlO) (by simp), e.slots (5, xhO) (by simp)⟩
    · rw [← a 3 (by decide), ← a 8 (by decide)]; exact e.slots (3, ahO) (by simp)
    · rw [← a 8 (by decide)]; exact e.saved
    · rw [← a 8 (by decide)]; exact e.frame
  · refine CT.seq (J := fun s => s.gpr .eax = p.2 8 ∧ s.gpr .esp = p.1)
      (CT.taint [.esp] (fun s₁ s₂ ⟨a₁, _, h₁, e₁⟩ ⟨a₂, _, h₂, e₂⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; subst e₁; subst e₂
        rw [pubOf_esp h₁, pubOf_esp h₂]) (by taint_decide)) (fun s ⟨s₀, hpre, hpub, hs⟩ => ?_)
      (CT.taint [.eax, .esp] (fun s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2, h₂.2]) (by taint_decide))
    subst s
    have hp := hpre
    simp only [streamCryptPre] at hp
    sig_split hp
    rename_i hrd hwr hdrop2 hdrop3 hdrop4 hdrop5 hdrop6 hdrop7 hdrop8 hdrop9 hdrop10 hdrop11 hdrop12 hdrop13
      hdrop14 hdrop15 hdrop16 hdrop17 hdrop18 hdrop19 hdrop20 hdrop21 hdrop22 hdrop23 hdrop24 hdrop25 hdrop26
    have fa := hp
    clear hdrop2 hdrop3 hdrop4 hdrop5 hdrop6 hdrop7 hdrop8 hdrop9 hdrop10 hdrop11 hdrop12 hdrop13 hdrop14
      hdrop15 hdrop16 hdrop17 hdrop18 hdrop19 hdrop20 hdrop21 hdrop22 hdrop23 hdrop24 hdrop25 hdrop26
    clear hp
    have rA : Covers [argsR (s₀.gpr .esp) 9] (s₀.rd ++ s₀.wr) := by
      rw [argsR_eq, hrd, hwr]; exact covers_of_mem (by simp)
    exact WP.mono (arg0_ok (argIn_of rA (by omega_using [fa]) (by decide))) fun s' ⟨ax, sp⟩ =>
      ⟨by rw [ax]; exact pubOf_arg hpub (by decide), by rw [sp]; exact pubOf_esp hpub⟩

/-- `setText`: the text as the pieces take it. -/
theorem setText_ok {Ctx St W SP : BitVec 32} {K : Nat} (L : Lay4 Ctx St W SP K) {D : BitVec 32} {n : Nat}
    {al xl xh : BitVec 32} {s : State} (he : Env Ctx St W SP s) (hs : TaSl W D n al xl xh s.mem) :
    ∃ s', runBlock isa setText s = some s' ∧ slotv s'.mem W dO = D ∧ slotv s'.mem W nO = BitVec.ofNat 32 n ∧
      slotv s'.mem W bO = BitVec.ofNat 32 (xl.toNat % 16) ∧ Frame [pslotR W] s.mem s'.mem ∧
      s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have h1 := hs.data; have h2 := hs.len; have h3 := hs.xl
  rw [slotv_eq] at h1 h2 h3
  simp only [dataO, lenO, xlO] at h1 h2 h3
  have hand := and15 xl
  refine ⟨_, by xrun [setText, he.ebp, L.aW, he.wIn, he.wIn', h1, h2, h3], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · mems [slotv_eq]
  · mems [slotv_eq, h2]
  · mems [slotv_eq, h3]; rw [hand]
  · simp only [mem_setMem, mem_setReg, mem_arithFlags]
    exact pslot_write (pslot_write (pslot_write (Frame.refl _ _) (by decide) (by decide) _) (by decide)
      (by decide) _) (by decide) (by decide) _
  · regs []
  · regs []
  · regs []
  all_goals rfl

end VG.Proof.Sm4Gcm.X86

end

end

/-!
# SM4-GCM on x86: `vg_aes_gcm_stream_encrypt`

Untrusted: everything here is checked by Lean. The entry, the text
encrypted (`crypt`), the ciphertext absorbed (`textAbsorb`) and the exit,
as one `Pc` (`streamEncrypt_pc`): correct (`streamEncrypt_correct`) and
constant time (`streamEncrypt_ct`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86

variable {vg : VG.Proof.AesGcm.X86.GcmImpl}

open VG VG.X86 VG.X86.RegUpd VG.Impl.Sm4Gcm.X86 VG.WriteBytes VG.Proof.AesGcm.X86
open VG.Impl.AesGcm.X86 hiding ctrCall keyCall ctrArgs cryptWhole cryptTail crypt tag init cryptEntry
  streamEncrypt streamDecrypt finEntry finTag streamFinish streamVerify oneEntry oneTag oneCrypt «seal» «open»
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr gctr inc32 j0)
open VG.Spec.Gcm (ctxH)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

theorem streamEncrypt_eq : (streamEncrypt vg.callees) = .seq (entry 8 (([.mov .esi (argOp 1)] : List Instr) ++
    (crKeeps.flatMap (fun p => keep p.1 p.2) ++ [])))
    (.seq (.block setText) (.seq crypt (.seq (textAbsorb vg.callees) (.block restore)))) := rfl

/-- After `setText`: the text ready for `crypt`. -/
structure CSet (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  ent : ∃ s₁, CEnt p s₀ s₁ ∧ Frame [pslotR (p.2 8)] s₁.mem s.mem ∧ s.rd = s₁.rd ∧ s.wr = s₁.wr
  cr : CrIn (p.2 0) (p.2 1) (p.2 8) p.1 1536 (p.2 6) (p.2 7).toNat (p.2 5 ++ p.2 4).toNat s

theorem cr_dataW {p : BitVec 32 × (Nat → BitVec 32)} (hc : CrPure p) {s₀ s : State} (hpre : streamCryptPre s₀)
    (hpub : pubOf 9 s₀ = p) (hwr : s.wr = s₀.wr) :
    DataW (p.2 0) (p.2 1) (p.2 8) p.1 1536 s (p.2 6) (p.2 7).toNat := by
  have hp := hpre
  simp only [streamCryptPre] at hp
  have hw : Covers [⟨w64 (p.2 6), (p.2 7).toNat⟩] s.wr := by
    rw [hwr, hp.2.1, ← pubOf_arg hpub (i := 6) (by decide), ← pubOf_arg hpub (i := 7) (by decide)]
    exact covers_of_mem (by simp)
  exact ⟨⟨covers_left hw, hc.fd, hc.dst, hc.dw, hc.dstk⟩, hw, hc.dctx⟩

theorem setText_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (CEnt p) (.block setText) (CSet p) := by
  refine Pc.taint [.ebp] (fun s₀ s h => ?_) (fun _ _ s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.env.ebp, h₂.env.ebp]) (by taint_decide)
  have hc := crPure_of h.pre h.pub
  have L := hc.lay
  obtain ⟨s', run, d, n, b, fr, bp, si, sp, rd, wr⟩ := setText_ok L h.env h.ta
  refine WP.of_runBlock ⟨s', run, ⟨s, h, fr, rd, wr⟩, ?_⟩
  have kP : ∀ r ∈ [pslotR (p.2 8)], (keptR (p.2 8)).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  refine ⟨h.env.keep bp si sp rd wr (slot_frame fr fun r hr => (kP r hr).sub_left (Offset.sub _ (by decide)
    (by decide))), d, n, by rw [b, append_toNat32]; congr 1; omega_using [], (p.2 7).isLt,
    cr_dataW hc h.pre h.pub (by rw [wr, h.wr])⟩

/-- The streaming state's regions are apart from what `crypt` and `textAbsorb` write, but their own. -/
theorem st_crFrame {p : BitVec 32 × (Nat → BitVec 32)} (hc : CrPure p) {d k : Nat} (hk : d + k ≤ 48) :
    ∀ r ∈ crFrame (p.2 1) (p.2 8) p.1 1536 (p.2 6) (p.2 7).toNat,
      (⟨w64 (p.2 1) + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  have L := hc.lay
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hc.dst.sub_right (Lay.stSub (by omega_using [hk]))).symm
  · exact Lay.st_st (.inl (by omega_using [hk])) (by omega_using [hk]) (by decide)
  · exact L.st_w (by omega_using [hk]) (.inr ⟨by decide, by decide⟩)
  · exact (L.stk_st (by omega_using [hk])).symm

theorem st_taFrame {p : BitVec 32 × (Nat → BitVec 32)} (hc : CrPure p) {d k : Nat}
    (hk : d + k ≤ 16 ∨ (48 ≤ d ∧ d + k ≤ 80)) :
    ∀ r ∈ taFrame (p.2 1) (p.2 8) p.1 28, (⟨w64 (p.2 1) + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  have L := hc.lay
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Lay.st_st (by omega_using [hk]) (by omega_using [hk]) (by decide)
  · exact L.st_w (by omega_using [hk]) (.inr ⟨by decide, by decide⟩)
  · exact L.st_w (by omega_using [hk]) (.inr ⟨by decide, by decide⟩)
  · exact (L.lay.stk_st (by omega_using [hk])).symm

theorem ret_crFrame {p : BitVec 32 × (Nat → BitVec 32)} (hc : CrPure p) :
    ∀ r ∈ crFrame (p.2 1) (p.2 8) p.1 1536 (p.2 6) (p.2 7).toNat, (⟨w64 p.1, 4⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hc.r_d
  · exact hc.r_s.sub_right (Lay.stSub (by decide))
  · exact hc.r_w.sub_right (Lay.wSub (by decide))
  · exact ret_below hc.sp

theorem ret_taFrame {p : BitVec 32 × (Nat → BitVec 32)} (hc : CrPure p) :
    ∀ r ∈ taFrame (p.2 1) (p.2 8) p.1 28, (⟨w64 p.1, 4⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hc.r_s.sub_right (Lay.stSub (by decide))
  · exact hc.r_w.sub_right (Lay.wSub (by decide))
  · exact hc.r_w.sub_right (Lay.wSub (by decide))
  · exact ret_below (by have := hc.sp; omega_using [this])

/-- The entry's and `setText`'s writes, within `W`. -/
theorem cset_frame {p : BitVec 32 × (Nat → BitVec 32)} {s₀ s₁ s : State} (h₁ : CEnt p s₀ s₁)
    (fr : Frame [pslotR (p.2 8)] s₁.mem s.mem) : Frame [⟨w64 (p.2 8) + BitVec.ofNat 64 96, 2464⟩] s₀.mem s.mem :=
  (h₁.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩).trans (fr.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩)

/-- The exit of `encrypt` and `decrypt`, after `crypt` and `textAbsorb` in either order. -/
theorem cr_exit {p : BitVec 32 × (Nat → BitVec 32)} (hc : CrPure p) {s₀ s₁ s : State} (h₁ : CEnt p s₀ s₁)
    (he : Env (p.2 0) (p.2 1) (p.2 8) p.1 s)
    (hf : Frame (pslotR (p.2 8) :: crFrame (p.2 1) (p.2 8) p.1 1536 (p.2 6) (p.2 7).toNat ++
      taFrame (p.2 1) (p.2 8) p.1 28) s₁.mem s.mem) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ s'.mem = s.mem := by
  have L := hc.lay
  have esp := pubOf_esp h₁.pub
  have hsv : SavedAt s.mem (p.2 8) s₀ := h₁.saved.frameK hf fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact Lay.w_w (a := 128) (n := 112) (d := 272) (k := 12) (.inl (by decide)) (by decide) (by decide)
    rcases List.mem_append.mp hr with hr | hr
    · exact kept_crFrame L (cr_dataW hc h₁.pre h₁.pub h₁.wr) r hr
    · exact kept_taFrame L.lay r hr
  have rT : ∀ r ∈ pslotR (p.2 8) :: crFrame (p.2 1) (p.2 8) p.1 1536 (p.2 6) (p.2 7).toNat ++
      taFrame (p.2 1) (p.2 8) p.1 28, (⟨w64 p.1, 4⟩ : Region).Disjoint r := fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hc.r_w.sub_right (Lay.wSub (d := 272) (n := 12) (by decide))
    rcases List.mem_append.mp hr with hr | hr
    · exact ret_crFrame hc r hr
    · exact ret_taFrame hc r hr
  have rE : ∀ r ∈ [(⟨w64 (p.2 8) + BitVec.ofNat 64 128, 2432⟩ : Region)], (⟨w64 p.1, 4⟩ : Region).Disjoint r :=
    fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hc.r_w.sub_right (Lay.wSub (by decide))
  have hret : s.mem.readW (w64 (s₀.gpr .esp)) 32 = s₀.mem.readW (w64 (s₀.gpr .esp)) 32 := by
    rw [esp, ret_kept hf rT, ret_kept h₁.frame rE]
  exact WP.mono (exit_ok he.ebp (by rw [he.esp, esp]) (covers_left he.wW) L.fw hsv hret)
    fun s' ⟨abi, m', _, _, _⟩ => ⟨abi, m'⟩

theorem streamEncrypt_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun (s₀ : State) s => streamCryptPre s₀ ∧ pubOf 9 s₀ = p ∧ s = s₀) (streamEncrypt vg.callees)
      (fun s₀ s' => abiPreserved s₀ s' ∧ streamEncryptX86.post s₀ s') := by
  by_cases hex : ∃ s₀, streamCryptPre s₀ ∧ pubOf 9 s₀ = p
  swap
  · exact Pc.vacuous fun a s ⟨h₁, h₂, _⟩ => hex ⟨a, h₁, h₂⟩
  obtain ⟨z, hz, hzp⟩ := hex
  have hc := crPure_of hz hzp
  have L := hc.lay
  rw [streamEncrypt_eq]
  refine Pc.seq (crEntry_pc p) (Pc.seq (setText_pc p) ?_)
  refine Pc.seq (Pc.lift (Pc.forall fun icb => crypt_pc L rfl (icb := icb) (D := p.2 6)
    (n := (p.2 7).toNat) (P := (p.2 5 ++ p.2 4).toNat)) (fun _ s => s.mem) fun s₀ s h => ⟨h.cr, rfl⟩) ?_
  refine Pc.seq (Pc.lift (textAbsorb_pc L.lay (D := p.2 6) (n := (p.2 7).toNat) (al := p.2 2) (ah := p.2 3)
    (xl := p.2 4) (xh := p.2 5)) (fun _ s => s.mem) fun s₀ s' ⟨s, h, co, rd, wr⟩ => ⟨?_, rfl⟩) ?_
  · obtain ⟨s₁, h₁, fr, rd₁, wr₁⟩ := h.ent
    have dw := cr_dataW hc h₁.pre h₁.pub (s := s') (by rw [wr, wr₁, h₁.wr])
    refine ⟨(co default).env, (h₁.ta.frame fr fun r hr => ?_).frame (co default).frame
      (kept_crFrame L h.cr.data), (p.2 7).isLt, DataOk.mono dw.ok (by decide) L.sp⟩
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  refine Pc.taint [.ebp] (fun s₀ s₄ ⟨s₃, ⟨s₂, h₂, co, rd₃, wr₃⟩, ta, rd₄, wr₄⟩ => ?_)
    (fun _ _ s₁ s₂ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.env.ebp, h₂.env.ebp]) (by taint_decide)
  obtain ⟨s₁, h₁, fr, rd₁, wr₁⟩ := h₂.ent
  have hf : Frame (pslotR (p.2 8) :: crFrame (p.2 1) (p.2 8) p.1 1536 (p.2 6) (p.2 7).toNat ++
      taFrame (p.2 1) (p.2 8) p.1 28) s₁.mem s₄.mem :=
    ((fr.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..).trans
      ((co default).frame.mono fun r hr => List.mem_cons_of_mem _ (List.mem_append_left _ hr))).trans
      (ta.frame.mono fun r hr => List.mem_cons_of_mem _ (List.mem_append_right _ hr))
  refine WP.mono (cr_exit hc h₁ ta.env hf) fun s' ⟨abi, m'⟩ => ⟨abi, fun iv a pt hr hl hpt => ?_⟩
  have hA : ∀ i, i < 9 → arg s₀ i = p.2 i := fun i hi => pubOf_arg h₁.pub hi
  dsimp only
  rw [hA 0 (by decide), hA 1 (by decide)] at hr
  rw [hA 2 (by decide), hA 3 (by decide)] at hl
  rw [hA 4 (by decide), hA 5 (by decide)] at hpt
  rw [hA 0 (by decide), hA 1 (by decide), hA 6 (by decide), hA 7 (by decide), m']
  generalize hci : ctxCiph s₀.mem (w64 (p.2 0)) = ciph at hr ⊢
  generalize hH : ctxH s₀.mem (w64 (p.2 0)) = H at hr ⊢
  have fW := cset_frame h₁ fr
  have hC2 : ciphOf s₂.mem (p.2 0) = ciph := by
    rw [← hci]; exact ciph_frame fW (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.cw.sub_right (Lay.wSub (by decide)))
  have hH2 : Hk s₂.mem (p.2 0) = H := by
    rw [← hH, ctxH_eq]; exact blockAt_frame fW fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide)
  have hr₂ := streamRepr_frame fW (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.sb) hr
  rw [← hC2, ← hH2] at hr₂
  rw [Proof.Gcm.streamRepr_iff, ofNat_lit, ofNat_lit, ofNat_lit, ofNat_lit] at hr₂
  obtain ⟨hj, ha, hct⟩ := hr₂
  rw [hH2] at hj
  rw [hC2, hH2] at ha hct
  have hP : (gctr ciph (inc32 (j0 H iv)) pt).length = (p.2 5 ++ p.2 4).toNat := by
    rw [Proof.Gcm.length_gctr, hpt]
  rw [hP] at hct
  have hco := co (inc32 (j0 H iv))
  have hct' : CtrS s₂.mem (p.2 1) (ciphOf s₂.mem (p.2 0)) (inc32 (j0 H iv))
      (p.2 5 ++ p.2 4).toNat := by rw [hC2]; exact hct
  have hct₃ := hco.ctr hct'
  have hout := hco.out hct'
  rw [hC2] at hct₃ hout
  have hd := h₂.cr.data
  have hfit := hd.ok.fit
  have hD2 : bytesAt s₂.mem (w64 (p.2 6)) (p.2 7).toNat = bytesAt s₀.mem (w64 (p.2 6)) (p.2 7).toNat :=
    bytesAt_frame fW (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hc.dw.sub_right (Lay.wSub (by decide))) (by omega_using [])
  rw [hD2] at hout
  have hH3 : Hk s₃.mem (p.2 0) = H := by
    rw [← hH2]; exact blockAt_frame hco.frame fun r hr =>
      (ctx_crFrame L hd r hr).sub_left (Lay.ctxSub (by decide))
  have ha₃ : Absorbed s₃.mem (w64 (p.2 1) + BitVec.ofNat 64 16) (w64 (p.2 1) + BitVec.ofNat 64 32)
      (Hk s₃.mem (p.2 0)) (Spec.Gcm.ghashInput a (gctr ciph (inc32 (j0 H iv)) pt)) := by
    rw [hH3]
    exact ha.congr (blockAt_frame hco.frame (st_crFrame hc (by decide)))
      (bytesAt_frame hco.frame (st_crFrame hc (d := 32) (k := (Spec.Gcm.ghashInput a _).length % 16) (by omega_using []))
        (by omega_using []))
  have hab := ta.abs a (gctr ciph (inc32 (j0 H iv)) pt) ⟨hl, by rw [Proof.Gcm.length_gctr, hpt]⟩ ha₃
  rw [hout, hH3] at hab
  have hcnew : gctr ciph (inc32 (j0 H iv)) (pt ++ bytesAt s₀.mem (w64 (p.2 6)) (p.2 7).toNat) =
      gctr ciph (inc32 (j0 H iv)) pt ++
        xorKs ciph (inc32 (j0 H iv)) (p.2 5 ++ p.2 4).toNat (bytesAt s₀.mem (w64 (p.2 6)) (p.2 7).toNat) := by
    rw [Proof.Gcm.gctr_append, hpt]
  have dT := data_taFrame (D := p.2 6) (n := (p.2 7).toNat) (DataOk.mono hd.ok (k := 28) (by decide) L.sp)
  refine ⟨?_, ?_⟩
  · rw [Proof.Gcm.streamRepr_iff, ofNat_lit, ofNat_lit, ofNat_lit, ofNat_lit, hcnew]
    refine ⟨?_, hab, ?_⟩
    · have e₁ := blockAt_frame ta.frame (st_taFrame hc (d := 0) (k := 16) (.inl (by decide)))
      have e₂ := blockAt_frame hco.frame (st_crFrame hc (d := 0) (k := 16) (by decide))
      simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at e₁ e₂
      rw [e₁, e₂, hj]
    · rw [List.length_append, Proof.Gcm.length_gctr, Proof.Gcm.length_xorKs, length_bytesAt, ← hpt]
      exact hct₃.congr (blockAt_frame ta.frame (st_taFrame hc (.inr ⟨by decide, by decide⟩)))
        (blockAt_frame ta.frame (st_taFrame hc (.inr ⟨by decide, by decide⟩)))
  · rw [bytesAt_frame ta.frame dT (by omega_using []), hout, hcnew,
      List.drop_left' (by rw [Proof.Gcm.length_gctr])]

theorem streamEncrypt_correct (s : State) (hs : streamEncryptX86.pre s) :
    ∃ t s', Exec isa (streamEncrypt vg.callees) s t s' ∧ abiPreserved s s' ∧ streamEncryptX86.post s s' :=
  (streamEncrypt_pc (pubOf 9 s)).wp s s ⟨hs, rfl, rfl⟩

theorem streamEncrypt_ct : ConstantTime isa streamEncryptX86.pre streamEncryptX86.pub (streamEncrypt vg.callees) :=
  Pc.constantTime (pubOf 9) (fun _ _ _ _ h => pubOf_eq h) streamEncrypt_pc fun _ hs => ⟨hs, rfl, rfl⟩

end VG.Proof.Sm4Gcm.X86

end

end

/-!
# SM4-GCM on x86: `vg_aes_gcm_stream_decrypt`

Untrusted: everything here is checked by Lean. The entry, the ciphertext
absorbed (`textAbsorb`), the text decrypted (`crypt`) and the exit, as one
`Pc` (`streamDecrypt_pc`): correct (`streamDecrypt_correct`) and constant
time (`streamDecrypt_ct`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86

variable {vg : VG.Proof.AesGcm.X86.GcmImpl}

open VG VG.X86 VG.X86.RegUpd VG.Impl.Sm4Gcm.X86 VG.WriteBytes VG.Proof.AesGcm.X86
open VG.Impl.AesGcm.X86 hiding ctrCall keyCall ctrArgs cryptWhole cryptTail crypt tag init cryptEntry
  streamEncrypt streamDecrypt finEntry finTag streamFinish streamVerify oneEntry oneTag oneCrypt «seal» «open»
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr gctr inc32 j0)
open VG.Spec.Gcm (ctxH)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

theorem streamDecrypt_eq : (streamDecrypt vg.callees) = .seq (entry 8 (([.mov .esi (argOp 1)] : List Instr) ++
    (crKeeps.flatMap (fun p => keep p.1 p.2) ++ [])))
    (.seq (textAbsorb vg.callees) (.seq (.block setText) (.seq crypt (.block restore)))) := rfl

theorem streamDecrypt_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun (s₀ : State) s => streamCryptPre s₀ ∧ pubOf 9 s₀ = p ∧ s = s₀) (streamDecrypt vg.callees)
      (fun s₀ s' => abiPreserved s₀ s' ∧ streamDecryptX86.post s₀ s') := by
  by_cases hex : ∃ s₀, streamCryptPre s₀ ∧ pubOf 9 s₀ = p
  swap
  · exact Pc.vacuous fun a s ⟨h₁, h₂, _⟩ => hex ⟨a, h₁, h₂⟩
  obtain ⟨z, hz, hzp⟩ := hex
  obtain hc := crPure_of hz hzp
  have L := hc.lay
  rw [streamDecrypt_eq]
  refine Pc.seq (crEntry_pc p) ?_
  refine Pc.seq (Pc.lift (textAbsorb_pc L.lay (D := p.2 6) (n := (p.2 7).toNat) (al := p.2 2) (ah := p.2 3)
    (xl := p.2 4) (xh := p.2 5)) (fun _ s => s.mem) fun s₀ s h =>
      ⟨⟨h.env, h.ta, (p.2 7).isLt, DataOk.mono (cr_dataW hc h.pre h.pub h.wr).ok (k := 28) (by decide) hc.lay.sp⟩, rfl⟩) ?_
  -- The text, as `crypt` takes it.
  refine Pc.seq (Q := fun s₀ s₃ => ∃ s₂, (∃ s₁, CEnt p s₀ s₁ ∧
      TaOut (p.2 0) (p.2 1) (p.2 8) p.1 28 (p.2 6) (p.2 7).toNat (p.2 2) (p.2 3) (p.2 4) (p.2 5) s₁.mem s₂ ∧
      s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr) ∧
      CrIn (p.2 0) (p.2 1) (p.2 8) p.1 1536 (p.2 6) (p.2 7).toNat (p.2 5 ++ p.2 4).toNat s₃ ∧
      Frame [pslotR (p.2 8)] s₂.mem s₃.mem ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr)
    (Pc.taint [.ebp] (fun s₀ s₂ h => ?_) (fun _ _ s₁ s₂ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.env.ebp, h₂.env.ebp]) (by taint_decide)) ?_
  · obtain ⟨s₁, h₁, ta, rd₂, wr₂⟩ := h
    obtain sl := h₁.ta.frame ta.frame (kept_taFrame L.lay)
    obtain ⟨s₃, run, d, n, b, fr, bp, si, sp, rd, wr⟩ := setText_ok L ta.env sl
    refine WP.of_runBlock ⟨s₃, run, s₂, ⟨s₁, h₁, ta, rd₂, wr₂⟩, ?_, fr, rd, wr⟩
    obtain kP : ∀ r ∈ [pslotR (p.2 8)], (keptR (p.2 8)).Disjoint r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    refine ⟨ta.env.keep bp si sp rd wr (slot_frame fr fun r hr => (kP r hr).sub_left (Offset.sub _ (by decide)
      (by decide))), d, n, by rw [b, append_toNat32]; congr 1; omega_using [], (p.2 7).isLt,
      cr_dataW hc h₁.pre h₁.pub (by rw [wr, wr₂, h₁.wr])⟩
  refine Pc.seq (Pc.lift (Pc.forall fun icb => crypt_pc L rfl (icb := icb) (D := p.2 6)
    (n := (p.2 7).toNat) (P := (p.2 5 ++ p.2 4).toNat)) (fun _ s => s.mem) fun s₀ s ⟨_, _, hin, _⟩ => ⟨hin, rfl⟩) ?_
  refine Pc.taint [.ebp] (fun s₀ s₄ ⟨s₃, ⟨s₂, ⟨s₁, h₁, ta, rd₂, wr₂⟩, hin, fr, rd₃, wr₃⟩, co, rd₄, wr₄⟩ => ?_)
    (fun _ _ s₁ s₂ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [(h₁ default).env.ebp, (h₂ default).env.ebp])
    (by taint_decide)
  obtain hf : Frame (pslotR (p.2 8) :: crFrame (p.2 1) (p.2 8) p.1 1536 (p.2 6) (p.2 7).toNat ++
      taFrame (p.2 1) (p.2 8) p.1 28) s₁.mem s₄.mem :=
    ((ta.frame.mono fun r hr => List.mem_cons_of_mem _ (List.mem_append_right _ hr)).trans
      (fr.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..)).trans
      ((co default).frame.mono fun r hr => List.mem_cons_of_mem _ (List.mem_append_left _ hr))
  refine WP.mono (cr_exit hc h₁ (co default).env hf) fun s' ⟨abi, m'⟩ => ⟨abi, fun iv a c hr hl hct => ?_⟩
  obtain hA : ∀ i, i < 9 → arg s₀ i = p.2 i := fun i hi => pubOf_arg h₁.pub hi
  dsimp only
  rw [hA 0 (by decide), hA 1 (by decide)] at hr
  rw [hA 2 (by decide), hA 3 (by decide)] at hl
  rw [hA 4 (by decide), hA 5 (by decide)] at hct
  rw [hA 0 (by decide), hA 1 (by decide), hA 6 (by decide), hA 7 (by decide), m']
  generalize hci : ctxCiph s₀.mem (w64 (p.2 0)) = ciph at hr ⊢
  generalize hH : ctxH s₀.mem (w64 (p.2 0)) = H at hr ⊢
  obtain fE : Frame [⟨w64 (p.2 8) + BitVec.ofNat 64 96, 2464⟩] s₀.mem s₁.mem :=
    h₁.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
  have hd := hin.data
  have hfit := hd.ok.fit
  obtain dP : ∀ r ∈ [pslotR (p.2 8)], (⟨w64 (p.2 6), (p.2 7).toNat⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hc.dw.sub_right (Lay.wSub (by decide))
  obtain hC1 : ciphOf s₁.mem (p.2 0) = ciph := by
    rw [← hci]; exact ciph_frame fE (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.cw.sub_right (Lay.wSub (by decide)))
  obtain hC3 : ciphOf s₃.mem (p.2 0) = ciph := by
    rw [← hC1, ciph_frame fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.cw.sub_right (Lay.wSub (by decide))),
      ciph_frame ta.frame (ctx_taFrame L.lay)]
  obtain hH1 : Hk s₁.mem (p.2 0) = H := by
    rw [← hH, ctxH_eq]; exact blockAt_frame fE fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide)
  obtain hr₁ := streamRepr_frame fE (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.sb) hr
  rw [Proof.Gcm.streamRepr_iff, ofNat_lit, ofNat_lit, ofNat_lit, ofNat_lit] at hr₁
  obtain ⟨hj, ha, hcr⟩ := hr₁
  obtain hD1 : bytesAt s₁.mem (w64 (p.2 6)) (p.2 7).toNat = bytesAt s₀.mem (w64 (p.2 6)) (p.2 7).toNat :=
    bytesAt_frame fE (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hc.dw.sub_right (Lay.wSub (by decide))) (by omega_using [])
  obtain hab := ta.abs a c ⟨hl, hct⟩ (by rw [hH1]; exact ha)
  rw [hD1, hH1] at hab
  -- The counter blocks, as `crypt` takes them.
  obtain hct3 : CtrS s₃.mem (p.2 1) (ciphOf s₃.mem (p.2 0)) (inc32 (j0 H iv)) (p.2 5 ++ p.2 4).toNat := by
    rw [hC3, hct]
    obtain dP' : ∀ {d k : Nat}, d + k ≤ 80 → ∀ r ∈ [pslotR (p.2 8)],
        (⟨w64 (p.2 1) + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun hk r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_w hk (.inr ⟨by decide, by decide⟩)
    exact (hcr.congr (blockAt_frame ta.frame (st_taFrame hc (.inr ⟨by decide, by decide⟩)))
      (blockAt_frame ta.frame (st_taFrame hc (.inr ⟨by decide, by decide⟩)))).congr
      (blockAt_frame fr (dP' (by decide))) (blockAt_frame fr (dP' (by decide)))
  obtain hco := co (inc32 (j0 H iv))
  obtain hct₄ := hco.ctr hct3
  obtain hout := hco.out hct3
  rw [hC3] at hct₄ hout
  obtain hD3 : bytesAt s₃.mem (w64 (p.2 6)) (p.2 7).toNat = bytesAt s₀.mem (w64 (p.2 6)) (p.2 7).toNat := by
    rw [bytesAt_frame fr dP (by omega_using []), bytesAt_frame ta.frame (data_taFrame (DataOk.mono hd.ok (k := 28) (by decide) hc.lay.sp)) (by omega_using []), hD1]
  rw [hD3] at hout
  obtain hdrop : (gctr ciph (inc32 (j0 H iv)) (c ++ bytesAt s₀.mem (w64 (p.2 6)) (p.2 7).toNat)).drop c.length =
      xorKs ciph (inc32 (j0 H iv)) c.length (bytesAt s₀.mem (w64 (p.2 6)) (p.2 7).toNat) := by
    rw [Proof.Gcm.gctr_append, List.drop_left' (Proof.Gcm.length_gctr _ _ _)]
  refine ⟨?_, by rw [hout, hdrop, hct]⟩
  rw [Proof.Gcm.streamRepr_iff, ofNat_lit, ofNat_lit, ofNat_lit, ofNat_lit]
  obtain dP' : ∀ {d k : Nat}, d + k ≤ 80 → ∀ r ∈ [pslotR (p.2 8)],
      (⟨w64 (p.2 1) + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun hk r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.st_w hk (.inr ⟨by decide, by decide⟩)
  refine ⟨?_, ?_, ?_⟩
  · have e₁ := blockAt_frame hco.frame (st_crFrame hc (d := 0) (k := 16) (by decide))
    obtain e₂ := blockAt_frame fr (dP' (d := 0) (k := 16) (by decide))
    obtain e₃ := blockAt_frame ta.frame (st_taFrame hc (d := 0) (k := 16) (.inl (by decide)))
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at e₁ e₂ e₃
    rw [e₁, e₂, e₃, hj]
  · exact (hab.congr (blockAt_frame fr (dP' (by decide)))
      (bytesAt_frame fr (dP' (d := 32) (k := (Spec.Gcm.ghashInput a _).length % 16) (by omega_using [])) (by omega_using []))).congr
      (blockAt_frame hco.frame (st_crFrame hc (by decide)))
      (bytesAt_frame hco.frame (st_crFrame hc (d := 32) (k := (Spec.Gcm.ghashInput a _).length % 16) (by omega_using []))
        (by omega_using []))
  · rw [List.length_append, length_bytesAt, ← hct]; exact hct₄

theorem streamDecrypt_correct (s : State) (hs : streamDecryptX86.pre s) :
    ∃ t s', Exec isa (streamDecrypt vg.callees) s t s' ∧ abiPreserved s s' ∧ streamDecryptX86.post s s' :=
  (streamDecrypt_pc (pubOf 9 s)).wp s s ⟨hs, rfl, rfl⟩

theorem streamDecrypt_ct : ConstantTime isa streamDecryptX86.pre streamDecryptX86.pub (streamDecrypt vg.callees) :=
  Pc.constantTime (pubOf 9) (fun _ _ _ _ h => pubOf_eq h) streamDecrypt_pc fun _ hs => ⟨hs, rfl, rfl⟩

end VG.Proof.Sm4Gcm.X86

end

end

/-! ### `Sm4Gcm.X86.Init`, which only this module used -/

section

/-!
# SM4-GCM on x86: `vg_sm4_gcm_init`

Untrusted: everything here is checked by Lean. The key schedule
(`vg_sm4_expand_key`, any implementation `ki` of it: `KeyImpl`), then the
hash subkey `CIPH_K(0¹²⁸)` (`vg_sm4_ctr32` on a zero block, with a zero
counter block at `T`), as one `Pc` (`init_pc`): correct (`init_correct`)
and constant time (`init_ct`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86


open VG VG.X86 VG.X86.RegUpd VG.Impl.Sm4Gcm.X86 VG.WriteBytes VG.Proof.AesGcm.X86
open VG.Impl.AesGcm.X86 hiding ctrCall keyCall ctrArgs cryptWhole cryptTail crypt tag init cryptEntry
  streamEncrypt streamDecrypt finEntry finTag streamFinish streamVerify oneEntry oneTag oneCrypt «seal» «open»
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt)
open VG.Spec.Sm4.Gcm (KeyRepr)

/-- The facts of `init`'s precondition about the public data `p` alone. -/
structure InitPure (p : BitVec 32 × (Nat → BitVec 32)) : Prop where
  kc : (⟨w64 (p.2 0), 16⟩ : Region).Disjoint ⟨w64 (p.2 1), 256⟩
  kw : (⟨w64 (p.2 0), 16⟩ : Region).Disjoint ⟨w64 (p.2 2), 2560⟩
  cw : (⟨w64 (p.2 1), 256⟩ : Region).Disjoint ⟨w64 (p.2 2), 2560⟩
  r_c : (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 1), 256⟩
  r_w : (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 2), 2560⟩
  k_k : (below p.1 1536).Disjoint ⟨w64 (p.2 0), 16⟩
  k_c : (below p.1 1536).Disjoint ⟨w64 (p.2 1), 256⟩
  k_w : (below p.1 1536).Disjoint ⟨w64 (p.2 2), 2560⟩
  fk : (p.2 0).toNat + 16 ≤ 2 ^ 32
  fc : (p.2 1).toNat + 256 ≤ 2 ^ 32
  fw : (p.2 2).toNat + 2560 ≤ 2 ^ 32
  sp : 1536 ≤ p.1.toNat

theorem initPure_of {p : BitVec 32 × (Nat → BitVec 32)} {s : State} (h : initPre s) (hp : pubOf 3 s = p) :
    InitPure p := by
  simp only [initPre] at h
  sig_split h
  rename_i hdrop0 hdrop1 d_kc d_kw hdrop4 d_cw hdrop6 hdrop7 hdrop8 r_c r_w hdrop11 k_k k_c k_w hdrop15 fk fc
    fw sp
  clear hdrop0 hdrop1 hdrop4 hdrop6 hdrop7 hdrop8 hdrop11 hdrop15 h
  rw [ofNat_lit, below_eq sp] at k_k k_c k_w
  obtain a0 := pubOf_arg hp (i := 0) (by decide); have a1 := pubOf_arg hp (i := 1) (by decide)
  obtain a2 := pubOf_arg hp (i := 2) (by decide)
  obtain e := pubOf_esp hp
  simp only [a0, a1, a2, e] at d_kc d_kw d_cw r_c r_w k_k k_c k_w fk fc fw sp
  exact ⟨d_kc, d_kw, d_cw, r_c, r_w, k_k, k_c, k_w, fk, fc, fw, sp⟩

/-- `ctx` and `W` and the stack apart, at offsets. -/
theorem InitPure.cw' {p : BitVec 32 × (Nat → BitVec 32)} (h : InitPure p) {a n d k : Nat} (ha : a + n ≤ 256)
    (hd : d + k ≤ 2560) :
    (⟨w64 (p.2 1) + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 (p.2 2) + BitVec.ofNat 64 d, k⟩ :=
  (h.cw.sub_left (Lay.ctxSub ha)).sub_right (Lay.wSub hd)

abbrev initTail : List Instr := [.mov .eax (argOp 0), .mov .edx (.reg .esi)]

abbrev initMid : List Instr :=
  ([.mov .eax (imm 0), .store (at_ .esi 240) .eax, .store (at_ .esi 244) .eax,
      .store (at_ .esi 248) .eax, .store (at_ .esi 252) .eax] : List Instr) ++ zero4 tO ++
      ([.mov .eax (.reg .esi), .mov .edx (.reg .ebp), .alu .add .edx (imm tO),
        .mov .ebx (.reg .esi), .alu .add .ebx (imm 240), .mov .edi (imm 1)] : List Instr)

theorem init_eq (k : Fn) : init k = .seq (entry 2 (([.mov .esi (argOp 1)] : List Instr) ++
    (([] : List (Nat × Nat)).flatMap (fun p => keep p.1 p.2) ++ initTail)))
    (.seq (keyCall k) (.seq (.block initMid) (.seq ctrCall (.block restore)))) := rfl

/-- After the entry: the arguments of `vg_sm4_expand_key`. -/
structure IEnt (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  pre : initPre s₀
  pub : pubOf 3 s₀ = p
  call : KeyCall s (p.2 0) (p.2 1)
  esi : s.gpr .esi = p.2 1
  ebp : s.gpr .ebp = p.2 2
  esp : s.gpr .esp = p.1
  saved : SavedAt s.mem (p.2 2) s₀
  frame : Frame [⟨w64 (p.2 2) + BitVec.ofNat 64 128, 2432⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem iEntry_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun (s₀ : State) s => initPre s₀ ∧ pubOf 3 s₀ = p ∧ s = s₀)
      (entry 2 (([.mov .esi (argOp 1)] : List Instr) ++ (([] : List (Nat × Nat)).flatMap (fun p => keep p.1 p.2) ++ initTail)))
      (IEnt p) := by
  refine ⟨fun s₀ s ⟨hpre, hpub, hs⟩ => ?_, ?_⟩
  · subst s
    obtain hc := initPure_of hpre hpub
    have hp := hpre
    simp only [initPre] at hp
    sig_split hp
    rename_i hrd hwr hdrop2 hdrop3 hdrop4 hdrop5 hdrop6 d_wa hdrop8 hdrop9 hdrop10 hdrop11 hdrop12 hdrop13
      hdrop14 hdrop15 hdrop16 hdrop17 hdrop18 hdrop19
    clear hdrop2 hdrop3 hdrop4 hdrop5 hdrop6 hdrop8 hdrop9 hdrop10 hdrop11 hdrop12 hdrop13 hdrop14 hdrop15
      hdrop16 hdrop17 hdrop18 hdrop19
    have fa := hp
    clear hp
    obtain a : ∀ i, i < 3 → arg s₀ i = p.2 i := fun i hi => pubOf_arg hpub hi
    obtain esp := pubOf_esp hpub
    obtain wW : Covers [⟨w64 (arg s₀ 2), 2560⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
    obtain rA : Covers [argsR (s₀.gpr .esp) 3] (s₀.rd ++ s₀.wr) := by
      rw [argsR_eq, hrd, hwr]; exact covers_of_mem (by simp)
    obtain aw : (argsR (s₀.gpr .esp) 3).Disjoint ⟨w64 (arg s₀ 2), 2560⟩ := by rw [argsR_eq]; exact d_wa.symm
    refine entry_ok [] initTail (by decide) (by decide) (by decide) (by decide) rfl rfl wW rA aw (by omega_arith)
      (by rw [a 2 (by decide)]; exact hc.fw) fun s₂ e => ?_
    obtain i₀ : InRegions (s₂.rd ++ s₂.wr) (argA (s₀.gpr .esp) 0) 4 := by
      rw [e.rd, e.wr]; exact argIn_of rA (by omega_arith) (by decide)
    obtain v₀ := e.args 0 (by decide)
    refine ⟨_, by xrun [e.esp, i₀, v₀, e.esi], ?_⟩
    obtain bsub : Region.Sub (below p.1 1460) (below p.1 1536) := VG.X86.below_sub (by decide) hc.sp
    obtain hrd' : s₀.rd = [⟨w64 (p.2 0), 16⟩] := by rw [hrd, a 0 (by decide)]
    obtain hwr' : s₀.wr = [⟨w64 (p.2 1), 256⟩, ⟨w64 (p.2 2), 2560⟩, ⟨argAddr s₀ 0, 12⟩] := by
      rw [hwr, a 1 (by decide), a 2 (by decide)]
    refine ⟨hpre, hpub, ⟨by regs [v₀]; exact a 0 (by decide), by regs [e.esi]; exact a 1 (by decide),
      by regs [e.esp, esp]; have := hc.sp; omega_arith, hc.kc.sub_right (Region.sub_prefix (by decide)),
      by regs [e.esp, esp]; exact hc.k_k.sub_left bsub,
      by regs [e.esp, esp]; exact (hc.k_c.sub_left bsub).sub_right (Region.sub_prefix (by decide)),
      hc.fk, by have := hc.fc; omega_arith,
      by mems [e.rd, e.wr, hrd']; exact covers_of_mem (by simp), ?_⟩, by regs [e.esi]; exact a 1 (by decide),
      by regs [e.ebp]; rw [a 2 (by decide)], by regs [e.esp, esp], by mems []; rw [← a 2 (by decide)]; exact e.saved,
      by mems []; rw [← a 2 (by decide)]; exact e.frame, by mems [e.rd], by mems [e.wr]⟩
    mems [e.wr, hwr']
    have := covers_off (p := w64 (p.2 1)) (k := 256) (d := 0) (n := 128)
      (rs := [⟨w64 (p.2 1), 256⟩, ⟨w64 (p.2 2), 2560⟩, ⟨argAddr s₀ 0, 12⟩]) (covers_of_mem (by simp)) (by decide)
      (by decide)
    simpa using this
  · refine CT.seq (J := fun s => s.gpr .eax = p.2 2 ∧ s.gpr .esp = p.1)
      (CT.taint [.esp] (fun s₁ s₂ ⟨a₁, _, h₁, e₁⟩ ⟨a₂, _, h₂, e₂⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; subst e₁; subst e₂
        rw [pubOf_esp h₁, pubOf_esp h₂]) (by taint_decide)) (fun s ⟨s₀, hpre, hpub, hs⟩ => ?_)
      (CT.taint [.eax, .esp] (fun s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2, h₂.2]) (by taint_decide))
    subst s
    have hp := hpre
    simp only [initPre] at hp
    sig_split hp
    rename_i hrd hwr hdrop2 hdrop3 hdrop4 hdrop5 hdrop6 hdrop7 hdrop8 hdrop9 hdrop10 hdrop11 hdrop12 hdrop13
      hdrop14 hdrop15 hdrop16 hdrop17 hdrop18 hdrop19
    clear hdrop2 hdrop3 hdrop4 hdrop5 hdrop6 hdrop7 hdrop8 hdrop9 hdrop10 hdrop11 hdrop12 hdrop13 hdrop14
      hdrop15 hdrop16 hdrop17 hdrop18 hdrop19
    have fa := hp
    clear hp
    obtain rA : Covers [argsR (s₀.gpr .esp) 3] (s₀.rd ++ s₀.wr) := by
      rw [argsR_eq, hrd, hwr]; exact covers_of_mem (by simp)
    exact WP.mono (arg0_ok (argIn_of rA (by omega_arith) (by decide))) fun s' ⟨ax, sp⟩ =>
      ⟨by rw [ax]; exact pubOf_arg hpub (by decide), by rw [sp]; exact pubOf_esp hpub⟩

/-- After the key schedule and `initMid`: the arguments of `vg_sm4_ctr32` for `H`. -/
structure IMid (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  ent : ∃ s₁, IEnt p s₀ s₁ ∧ Frame [⟨w64 (p.2 1), 256⟩, ⟨w64 (p.2 2), 2560⟩, below p.1 1536] s₁.mem s.mem
  call : CtrCall s (p.2 1) (p.2 2 + BitVec.ofNat 32 96) (p.2 1 + BitVec.ofNat 32 240) 1
  esp : s.gpr .esp = p.1
  ebp : s.gpr .ebp = p.2 2
  sched : Spec.Sm4.scheduleAt s.mem (w64 (p.2 1)) = Spec.Sm4.expandKey (Spec.Sm4.blockAt s₀.mem (w64 (p.2 0)))
  zt : blockAt s.mem (w64 (p.2 2) + BitVec.ofNat 64 96) = 0
  zh : blockAt s.mem (w64 (p.2 1) + BitVec.ofNat 64 240) = 0
  saved : SavedAt s.mem (p.2 2) s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem iMid_ok {p : BitVec 32 × (Nat → BitVec 32)} (hc : InitPure p) {s₀ s₁ s : State} (h : IEnt p s₀ s₁)
    (g : KeyPost s₁ (p.2 0) (p.2 1) s) :
    WP isa (.block initMid) s (IMid p s₀) := by
  obtain eT := w64_add (x := p.2 2) (k := 96) (by have := hc.fw; omega_arith)
  obtain eH := w64_add (x := p.2 1) (k := 240) (by have := hc.fc; omega_arith)
  obtain bp : s.gpr .ebp = p.2 2 := by rw [g.saved .ebp (by decide), h.ebp]
  obtain si : s.gpr .esi = p.2 1 := by rw [g.saved .esi (by decide), h.esi]
  obtain sp : s.gpr .esp = p.1 := by rw [g.saved .esp (by decide), h.esp]
  obtain hwr : s.wr = s₀.wr := by rw [g.wr, h.wr]
  have hp := h.pre
  simp only [initPre] at hp
  obtain hwr₀ : s₀.wr = [⟨w64 (p.2 1), 256⟩, ⟨w64 (p.2 2), 2560⟩, ⟨argAddr s₀ 0, 12⟩] := by
    rw [hp.2.1, pubOf_arg h.pub (i := 1) (by decide), pubOf_arg h.pub (i := 2) (by decide)]
  obtain wC : Covers [⟨w64 (p.2 1), 256⟩] s.wr := by rw [hwr, hwr₀]; exact covers_of_mem (by simp)
  obtain wW : Covers [⟨w64 (p.2 2), 2560⟩] s.wr := by rw [hwr, hwr₀]; exact covers_of_mem (by simp)
  obtain aC : ∀ {o}, o < 256 → w64 (p.2 1 + BitVec.ofNat 32 o) = w64 (p.2 1) + BitVec.ofNat 64 o :=
    fun ho => w64_add (by have := hc.fc; omega_arith)
  obtain aW : ∀ {o}, o < 2560 → w64 (p.2 2 + BitVec.ofNat 32 o) = w64 (p.2 2) + BitVec.ofNat 64 o :=
    fun ho => w64_add (by have := hc.fw; omega_arith)
  obtain cIn : ∀ {d}, d + 4 ≤ 256 → InRegions s.wr (w64 (p.2 1) + BitVec.ofNat 64 d) 4 :=
    fun hd => in_off wC hd (by decide)
  obtain wIn : ∀ {d}, d + 4 ≤ 2560 → InRegions s.wr (w64 (p.2 2) + BitVec.ofNat 64 d) 4 :=
    fun hd => in_off wW hd (by decide)
  obtain hzC : ∀ m : Mem, Cmac.zero4 m (w64 (p.2 1) + BitVec.ofNat 64 240) =
      (((m.writeW (w64 (p.2 1) + BitVec.ofNat 64 240) (BitVec.ofNat 32 0)).writeW (w64 (p.2 1) + BitVec.ofNat 64 244)
      (BitVec.ofNat 32 0)).writeW (w64 (p.2 1) + BitVec.ofNat 64 248) (BitVec.ofNat 32 0)).writeW
      (w64 (p.2 1) + BitVec.ofNat 64 252) (BitVec.ofNat 32 0) := fun m => by
    simp only [Cmac.zero4, Cmac.store4, add_ofNat_assoc]; rfl
  obtain hzW : ∀ m : Mem, Cmac.zero4 m (w64 (p.2 2) + BitVec.ofNat 64 96) =
      (((m.writeW (w64 (p.2 2) + BitVec.ofNat 64 96) (BitVec.ofNat 32 0)).writeW (w64 (p.2 2) + BitVec.ofNat 64 100)
      (BitVec.ofNat 32 0)).writeW (w64 (p.2 2) + BitVec.ofNat 64 104) (BitVec.ofNat 32 0)).writeW
      (w64 (p.2 2) + BitVec.ofNat 64 108) (BitVec.ofNat 32 0) := fun m => by
    simp only [Cmac.zero4, Cmac.store4, add_ofNat_assoc]; rfl
  refine WP.of_runBlock ⟨_, by xrun [initMid, bp, si, aC, aW, cIn, wIn, zero4, ← hzC, ← hzW], ?_⟩
  generalize hZ₁ : Cmac.zero4 s.mem (w64 (p.2 1) + BitVec.ofNat 64 240) = Z₁
  generalize hZ₂ : Cmac.zero4 Z₁ (w64 (p.2 2) + BitVec.ofNat 64 96) = Z₂
  obtain f₁ : Frame [⟨w64 (p.2 1) + BitVec.ofNat 64 240, 16⟩] s.mem Z₁ := by
    rw [← hZ₁]; exact Cmac.frame_store4 _ _ _ _ _
  obtain f₂ : Frame [⟨w64 (p.2 2) + BitVec.ofNat 64 96, 16⟩] Z₁ Z₂ := by rw [← hZ₂]; exact Cmac.frame_store4 _ _ _ _ _
  have hfit := hc.fc
  have hfw := hc.fw
  have hsp := hc.sp
  obtain bsub : Region.Sub (below p.1 1460) (below p.1 1536) := VG.X86.below_sub (by decide) hsp
  have gf := g.frame
  rw [h.esp] at gf
  have go := g.out
  obtain dK : ∀ r ∈ [(⟨w64 (p.2 2) + BitVec.ofNat 64 128, 2432⟩ : Region)],
      (⟨w64 (p.2 0), 16⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hc.kw.sub_right (Lay.wSub (by decide))
  rw [sm4BlockAt_frame h.frame dK] at go
  obtain dZ : ∀ r ∈ [(⟨w64 (p.2 1) + BitVec.ofNat 64 240, 16⟩ : Region)],
      (⟨w64 (p.2 1), 128⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.base_disjoint _ (by decide) (by omega_arith)
  obtain dZ₂ : ∀ r ∈ [(⟨w64 (p.2 2) + BitVec.ofNat 64 96, 16⟩ : Region)],
      (⟨w64 (p.2 1), 128⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hc.cw.sub_left (Region.sub_prefix (by omega_arith))).sub_right (Lay.wSub (by decide))
  obtain hsv : SavedAt Z₂ (p.2 2) s₀ := by
    refine ((h.saved.frame gf fun r hr => ?_).frame f₁ fun r hr => ?_).frame f₂ fun r hr => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ((hc.cw.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))).symm
      · exact ((hc.k_w.sub_left bsub).sub_right (Lay.wSub (by decide))).symm
    · simp only [List.mem_singleton] at hr; subst hr; exact (hc.cw' (by decide) (by decide)).symm
    · simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  obtain kc := hc.cw' (a := 0) (n := 128) (d := 96) (k := 16) (by decide) (by decide)
  obtain cd := hc.cw' (a := 240) (n := 16) (d := 96) (k := 16) (by decide) (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at kc
  obtain rC : Covers [⟨w64 (p.2 1), 128⟩] (s.rd ++ s.wr) := by
    have := covers_off (p := w64 (p.2 1)) (k := 256) (d := 0) (n := 128) (rs := s.wr) wC (by decide) (by decide)
    exact covers_left (by simpa using this)
  refine ⟨⟨s₁, h, ?_⟩, ⟨by regs [si], by regs [bp], by regs [si], by regs [], by regs [sp]; omega_arith,
    by rw [eT]; exact kc, ?_, by rw [eT, eH]; exact cd.symm,
    by regs [sp]; exact hc.k_c.sub_right (Region.sub_prefix (by decide)),
    by regs [sp]; rw [eT]; exact hc.k_w.sub_right (Lay.wSub (by decide)),
    by regs [sp]; rw [eH]; exact hc.k_c.sub_right (Lay.ctxSub (by decide)),
    by omega_arith, by rw [toNat_add32 (by omega_arith)]; omega_arith, by rw [toNat_add32 (by omega_arith)]; omega_arith,
    by mems []; exact rC, ?_⟩, by regs [sp], by regs [bp], ?_, ?_, ?_, ?_, by mems [g.rd, h.rd],
    by mems [g.wr, h.wr]⟩
  · simp only [mem_setMem, mem_setReg, mem_arithFlags]
    refine (gf.sub fun r hr => ?_).trans ((f₁.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
      · exact ⟨_, by simp, bsub⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Lay.ctxSub (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Lay.wSub (by decide)⟩
  · rw [eH]
    have := Offset.disjoint (w64 (p.2 1)) (d := 0) (n := 128) (e := 240) (k := 16 * 1) (.inl (by omega_arith))
      (by omega_arith) (by omega_arith)
    simpa using this
  · mems []
    rw [eT, eH]
    exact covers_cons (covers_off wW (by decide) (by decide)) (covers_cons (covers_off wC (by decide) (by decide))
      covers_nil)
  · simp only [mem_setMem, mem_setReg, mem_arithFlags]
    rw [scheduleAt_frame f₂ dZ₂, scheduleAt_frame f₁ dZ]
    exact go
  · simp only [mem_setMem, mem_setReg, mem_arithFlags]
    rw [← hZ₂, blockAt, zero4_bytes', ofBytes_zeros]
  · simp only [mem_setMem, mem_setReg, mem_arithFlags]
    rw [blockAt_frame f₂ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact cd, ← hZ₁, blockAt, zero4_bytes', ofBytes_zeros]
  · simp only [mem_setMem, mem_setReg, mem_arithFlags]; exact hsv

theorem init_pc (ki : KeyImpl) (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun (s₀ : State) s => initPre s₀ ∧ pubOf 3 s₀ = p ∧ s = s₀) (init ki.fn)
      (fun s₀ s' => abiPreserved s₀ s' ∧ initX86.post s₀ s') := by
  by_cases hex : ∃ s₀, initPre s₀ ∧ pubOf 3 s₀ = p
  swap
  · exact Pc.vacuous fun a s ⟨h₁, h₂, _⟩ => hex ⟨a, h₁, h₂⟩
  obtain ⟨z, hz, hzp⟩ := hex
  obtain hc := initPure_of hz hzp
  rw [init_eq]
  refine Pc.seq (iEntry_pc p) ?_
  refine Pc.seq (Pc.of (I := fun s => KeyCall s (p.2 0) (p.2 1) ∧ s.gpr .esp = p.1) (fun s h => key_call ki h.1)
    (key_ct ki fun s h => h) _ fun _ _ h => ⟨h.call, h.esp⟩) ?_
  refine Pc.seq (Q := IMid p) (Pc.taint [.esi, .ebp] (fun s₀ s ⟨s₁, h, g⟩ => iMid_ok hc h g)
    (fun _ _ s₁ s₂ ⟨t₁, h₁, g₁⟩ ⟨t₂, h₂, g₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [g₁.saved .esi (by decide), g₂.saved .esi (by decide), h₁.esi, h₂.esi]
      · rw [g₁.saved .ebp (by decide), g₂.saved .ebp (by decide), h₁.ebp, h₂.ebp]) (by taint_decide)) ?_
  refine Pc.seq (Pc.of (I := fun s => CtrCall s (p.2 1) (p.2 2 + BitVec.ofNat 32 96)
    (p.2 1 + BitVec.ofNat 32 240) 1 ∧ s.gpr .esp = p.1) (fun s h => ctr_call h.1)
    (ctr_ct fun s h => h) _ fun _ _ h => ⟨h.call, h.esp⟩) ?_
  refine Pc.taint [.ebp] (fun s₀ s' ⟨s, hm, g⟩ => ?_) (fun _ _ s₁ s₂ ⟨_, h₁, g₁⟩ ⟨_, h₂, g₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [g₁.saved .ebp (by decide), g₂.saved .ebp (by decide), h₁.ebp, h₂.ebp]) (by taint_decide)
  obtain ⟨s₁, h₁, fE⟩ := hm.ent
  obtain eT := w64_add (x := p.2 2) (k := 96) (by have := hc.fw; omega_arith)
  obtain eH := w64_add (x := p.2 1) (k := 240) (by have := hc.fc; omega_arith)
  obtain bp : s'.gpr .ebp = p.2 2 := by rw [g.saved .ebp (by decide), hm.ebp]
  have gf := g.frame
  rw [hm.esp, eT, eH] at gf
  have hsp := hc.sp
  obtain dC : ∀ r ∈ [(⟨w64 (p.2 2) + BitVec.ofNat 64 96, 16⟩ : Region),
      ⟨w64 (p.2 1) + BitVec.ofNat 64 240, 16 * 1⟩, below p.1 1536],
      (⟨w64 (p.2 1), 128⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hc.cw.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))
    · exact Offset.base_disjoint _ (by decide) (by omega_arith)
    · exact (hc.k_c.sub_right (Region.sub_prefix (by decide))).symm
  obtain hsv : SavedAt s'.mem (p.2 2) s₀ := hm.saved.frame gf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact (hc.cw' (by decide) (by decide)).symm
    · exact ((hc.k_w.sub_right (Lay.wSub (by decide)))).symm
  obtain rG : ∀ r ∈ [(⟨w64 (p.2 2) + BitVec.ofNat 64 96, 16⟩ : Region),
      ⟨w64 (p.2 1) + BitVec.ofNat 64 240, 16 * 1⟩, below p.1 1536],
      (⟨w64 p.1, 4⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hc.r_w.sub_right (Lay.wSub (by decide))
    · exact hc.r_c.sub_right (Lay.ctxSub (by decide))
    · exact ret_below hsp
  obtain rF : ∀ r ∈ [(⟨w64 (p.2 1), 256⟩ : Region), ⟨w64 (p.2 2), 2560⟩, below p.1 1536],
      (⟨w64 p.1, 4⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hc.r_c
    · exact hc.r_w
    · exact ret_below hsp
  obtain rE : ∀ r ∈ [(⟨w64 (p.2 2) + BitVec.ofNat 64 128, 2432⟩ : Region)], (⟨w64 p.1, 4⟩ : Region).Disjoint r :=
    fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hc.r_w.sub_right (Lay.wSub (by decide))
  obtain hret : s'.mem.readW (w64 (s₀.gpr .esp)) 32 = s₀.mem.readW (w64 (s₀.gpr .esp)) 32 := by
    rw [pubOf_esp h₁.pub, ret_kept gf rG, ret_kept fE rF, ret_kept h₁.frame rE]
  obtain hwr₀ : s'.wr = s₀.wr := by rw [g.wr, hm.wr]
  have hp := h₁.pre
  simp only [initPre] at hp
  obtain wW : Covers [⟨w64 (p.2 2), 2560⟩] s'.wr := by
    rw [hwr₀, hp.2.1, pubOf_arg h₁.pub (i := 2) (by decide)]; exact covers_of_mem (by simp)
  refine WP.mono (exit_ok (W := p.2 2) bp (by rw [g.saved .esp (by decide), hm.esp, pubOf_esp h₁.pub])
    (covers_left wW) hc.fw hsv hret)
    fun s'' ⟨abi, m'', _, _, _⟩ => ⟨abi, ?_⟩
  obtain hA : ∀ i, i < 3 → arg s₀ i = p.2 i := fun i hi => pubOf_arg h₁.pub hi
  show KeyRepr s''.mem _ _
  rw [hA 0 (by decide), hA 1 (by decide), m'']
  obtain hkey : (Vector.ofFn fun i : Fin 16 => (bytesAt s₀.mem (w64 (p.2 0)) 16).getD i.val 0) =
      Spec.Sm4.blockAt s₀.mem (w64 (p.2 0)) := by
    rw [Proof.Sm4.bytesAt_eq_blockAt]; exact Proof.Sm4.ofFn_toList _
  obtain hs : Spec.Sm4.scheduleAt s'.mem (w64 (p.2 1)) =
      Spec.Sm4.expandKey (Spec.Sm4.blockAt s₀.mem (w64 (p.2 0))) := by
    rw [scheduleAt_frame gf dC]; exact hm.sched
  refine ⟨by rw [hkey]; exact hs, ?_⟩
  have go := g.out
  rw [eH, eT, blocksAt_one, blocksAt_one, hm.zh, hm.zt, hm.sched] at go
  obtain hb := congrArg (fun l => List.getD l 0 0) go
  simp only [List.getD_cons_zero] at hb
  rw [Proof.Gcm.ctr32_getD _ _ _ (by simp)] at hb
  simp only [List.getD_cons_zero, Nat.repeat, BitVec.zero_xor] at hb
  rw [ctxH_eq, hb]
  simp only [Spec.Sm4.gcmCipherOfKey, hkey]
  exact BitVec.zero_xor

theorem init_correct (ki : KeyImpl) (s : State) (hs : initX86.pre s) :
    ∃ t s', Exec isa (init ki.fn) s t s' ∧ abiPreserved s s' ∧ initX86.post s s' :=
  (init_pc ki (pubOf 3 s)).wp s s ⟨hs, rfl, rfl⟩

theorem init_ct (ki : KeyImpl) : ConstantTime isa initX86.pre initX86.pub (init ki.fn) :=
  Pc.constantTime (pubOf 3) (fun _ _ _ _ h => pubOf_eq h) (init_pc ki) fun _ hs => ⟨hs, rfl, rfl⟩

end VG.Proof.Sm4Gcm.X86

end

end

/-! ### `Sm4Gcm.X86.Verified`, which only this module used -/

section

/-!
# SM4-GCM on x86: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant
time, a state satisfying each precondition, and the shared contracts of
`Spec/Sm4/Gcm/Contract.lean` with the working space as an argument
(`Proof/Sm4Gcm/Scratch.lean`): with 1536 bytes of stack for the functions
that call `vg_sm4_ctr32` (which pushes four arguments and the return
address, and keeps its working space below them). `stream_init` and
`stream_aad` are AES-GCM's (`Proof/AesGcm/X86/Verified.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86

variable {vg : VG.Proof.AesGcm.X86.GcmImpl}

open VG VG.X86 VG.Impl.Sm4Gcm.X86 VG.Proof.AesGcm.X86
open VG.Impl.AesGcm.X86 hiding ctrCall keyCall ctrArgs cryptWhole cryptTail crypt tag init cryptEntry
  streamEncrypt streamDecrypt finEntry finTag streamFinish streamVerify oneEntry oneTag oneCrypt «seal» «open»

/-- A state satisfying the precondition of `vg_sm4_gcm_stream_encrypt` and
`_decrypt` (with no data): the context at `0x1000`, the state at `0x3000`,
the data at `0x2000` and `scratch` at `0x4000`. -/
def crSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x30
    else if a = 0x801d then 0x20 else if a = 0x8025 then 0x40 else 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩, ⟨0x4000, 2560⟩, ⟨0x8004, 36⟩]

theorem streamEncrypt_verified : Verified X86.target (streamEncrypt vg.callees) (Proof.Sm4Gcm.streamEncryptScratchContract X86.abi 1536) :=
  Verified.of_correct streamEncrypt_correct streamEncrypt_ct (by
    have a0 : arg crSat 0 = 0x1000 := by decide
    have a1 : arg crSat 1 = 0x3000 := by decide
    have a2 : arg crSat 2 = 0 := by decide
    have a3 : arg crSat 3 = 0 := by decide
    have a4 : arg crSat 4 = 0 := by decide
    have a5 : arg crSat 5 = 0 := by decide
    have a6 : arg crSat 6 = 0x2000 := by decide
    have a7 : arg crSat 7 = 0 := by decide
    have a8 : arg crSat 8 = 0x4000 := by decide
    have e : argAddr crSat 0 = 0x8004 := by decide
    have esp : crSat.gpr .esp = 0x8000 := rfl
    sig_implies [Proof.Sm4Gcm.streamEncryptScratchContract, Proof.Sm4Gcm.streamCryptScratchSig, Spec.Sm4.Gcm.streamEncryptPost, Spec.Sm4.Gcm.streamDecryptPost, streamEncryptX86, streamCryptPre, pubN,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, e, esp] using crSat)

theorem streamDecrypt_verified : Verified X86.target (streamDecrypt vg.callees) (Proof.Sm4Gcm.streamDecryptScratchContract X86.abi 1536) :=
  Verified.of_correct streamDecrypt_correct streamDecrypt_ct (by
    have a0 : arg crSat 0 = 0x1000 := by decide
    have a1 : arg crSat 1 = 0x3000 := by decide
    have a2 : arg crSat 2 = 0 := by decide
    have a3 : arg crSat 3 = 0 := by decide
    have a4 : arg crSat 4 = 0 := by decide
    have a5 : arg crSat 5 = 0 := by decide
    have a6 : arg crSat 6 = 0x2000 := by decide
    have a7 : arg crSat 7 = 0 := by decide
    have a8 : arg crSat 8 = 0x4000 := by decide
    have e : argAddr crSat 0 = 0x8004 := by decide
    have esp : crSat.gpr .esp = 0x8000 := rfl
    sig_implies [Proof.Sm4Gcm.streamDecryptScratchContract, Proof.Sm4Gcm.streamCryptScratchSig, Spec.Sm4.Gcm.streamEncryptPost, Spec.Sm4.Gcm.streamDecryptPost, streamDecryptX86, streamCryptPre, pubN,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, e, esp] using crSat)

/-- A state satisfying `vg_sm4_gcm_stream_finish`'s precondition: the
context at `0x1000`, the state at `0x3000`, the tag at `0x5000` and `work`
at `0x4000`. -/
def finSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x30
    else if a = 0x801d then 0x50 else if a = 0x8021 then 0x40 else 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩, ⟨0x4000, 2560⟩, ⟨0x8004, 32⟩]

theorem streamFinish_verified :
    Verified X86.target (streamFinish vg.callees) (Proof.Sm4Gcm.streamFinishScratchContract X86.abi 1536) :=
  Verified.of_correct streamFinish_correct streamFinish_ct (by
    have a0 : arg finSat 0 = 0x1000 := by decide
    have a1 : arg finSat 1 = 0x3000 := by decide
    have a2 : arg finSat 2 = 0 := by decide
    have a3 : arg finSat 3 = 0 := by decide
    have a4 : arg finSat 4 = 0 := by decide
    have a5 : arg finSat 5 = 0 := by decide
    have a6 : arg finSat 6 = 0x5000 := by decide
    have a7 : arg finSat 7 = 0x4000 := by decide
    have e : argAddr finSat 0 = 0x8004 := by decide
    have esp : finSat.gpr .esp = 0x8000 := rfl
    sig_implies [Proof.Sm4Gcm.streamFinishScratchContract, Proof.Sm4Gcm.streamFinishScratchSig,
      Spec.Sm4.Gcm.streamFinishPost, streamFinishX86, finPre, pubN,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, a3, a4, a5, a6, a7, e, esp] using finSat)

/-- A state satisfying `vg_sm4_gcm_stream_verify`'s precondition: as
`finSat`, with a received tag of no bytes at `0x5000`. -/
def verSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x30
    else if a = 0x801d then 0x50 else if a = 0x8025 then 0x40 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x5000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩, ⟨0x8004, 36⟩]

theorem streamVerify_verified :
    Verified X86.target (streamVerify vg.callees) (Proof.Sm4Gcm.streamVerifyScratchContract X86.abi 1536) :=
  Verified.of_correct streamVerify_correct streamVerify_ct (by
    have a0 : arg verSat 0 = 0x1000 := by decide
    have a1 : arg verSat 1 = 0x3000 := by decide
    have a2 : arg verSat 2 = 0 := by decide
    have a3 : arg verSat 3 = 0 := by decide
    have a4 : arg verSat 4 = 0 := by decide
    have a5 : arg verSat 5 = 0 := by decide
    have a6 : arg verSat 6 = 0x5000 := by decide
    have a7 : arg verSat 7 = 0 := by decide
    have a8 : arg verSat 8 = 0x4000 := by decide
    have e : argAddr verSat 0 = 0x8004 := by decide
    have esp : verSat.gpr .esp = 0x8000 := rfl
    sig_implies [Proof.Sm4Gcm.streamVerifyScratchContract, Proof.Sm4Gcm.streamVerifyScratchSig,
      Spec.Sm4.Gcm.streamVerifyPost, streamVerifyX86, verifyPre, pubN,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, e, esp] using verSat)

/-- A state satisfying `vg_sm4_gcm_seal`'s precondition (with no nonce,
additional data or data): the context at `0x1000`, the nonce at `0x2000`,
the additional data at `0x2100`, the data at `0x3000`, the tag at `0x5000`
and `work` at `0x4000`. -/
def sealSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20
    else if a = 0x8011 then 0x21 else if a = 0x8019 then 0x30 else if a = 0x8021 then 0x50
    else if a = 0x8025 then 0x40 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x5000, 16⟩, ⟨0x4000, 2560⟩, ⟨0x8004, 36⟩]

theorem seal_verified : Verified X86.target («seal» vg.callees) (Proof.Sm4Gcm.sealScratchContract X86.abi 1536) :=
  Verified.of_correct seal_correct seal_ct (by
    have a0 : arg sealSat 0 = 0x1000 := by decide
    have a1 : arg sealSat 1 = 0x2000 := by decide
    have a2 : arg sealSat 2 = 0 := by decide
    have a3 : arg sealSat 3 = 0x2100 := by decide
    have a4 : arg sealSat 4 = 0 := by decide
    have a5 : arg sealSat 5 = 0x3000 := by decide
    have a6 : arg sealSat 6 = 0 := by decide
    have a7 : arg sealSat 7 = 0x5000 := by decide
    have a8 : arg sealSat 8 = 0x4000 := by decide
    have e : argAddr sealSat 0 = 0x8004 := by decide
    have esp : sealSat.gpr .esp = 0x8000 := rfl
    sig_implies [Proof.Sm4Gcm.sealScratchContract, Proof.Sm4Gcm.sealScratchSig,
      Spec.Sm4.Gcm.sealPost, sealX86, sealPre, pubN,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, e, esp] using sealSat)

/-- A state satisfying `vg_sm4_gcm_open`'s precondition: as `sealSat`, with
a received tag of no bytes at `0x5000`. -/
def openSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20
    else if a = 0x8011 then 0x21 else if a = 0x8019 then 0x30 else if a = 0x8021 then 0x50
    else if a = 0x8029 then 0x40 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0x5000, 0⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 2560⟩, ⟨0x8004, 40⟩]

/-- The leak `open` may have: whether it succeeds. -/
theorem leak_bool {a b : Bool} (h : ([if a = true then 1 else 0] : List Nat) = [if b = true then 1 else 0]) :
    a = b := by
  cases a <;> cases b <;> simp_all

theorem open_pre : ∀ s, (Proof.Sm4Gcm.openScratchContract X86.abi 1536).pre s → openX86.pre s := by
  sig_implies_pre [Proof.Sm4Gcm.openScratchContract, Proof.Sm4Gcm.openScratchSig,
    Spec.Sm4.Gcm.openPost, Spec.Sm4.Gcm.openLeak, openX86, openPre, pubN,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]

/-- `open`'s public data include its leak, whether it succeeds. -/
theorem open_verified : Verified X86.target («open» vg.callees) (Proof.Sm4Gcm.openScratchContract X86.abi 1536) :=
  Verified.of_correct open_correct open_ct
    { pre := open_pre
      post := by sig_implies_post [Proof.Sm4Gcm.openScratchContract, Proof.Sm4Gcm.openScratchSig,
        Spec.Sm4.Gcm.openPost, Spec.Sm4.Gcm.openLeak, openX86, openPre, pubN,
        X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      pub := by
        intro s₁ s₂ h₁ h₂ h
        sig_pub [Proof.Sm4Gcm.openScratchContract, Proof.Sm4Gcm.openScratchSig,
          Spec.Sm4.Gcm.openPost, Spec.Sm4.Gcm.openLeak, openX86, openPre, pubN,
          X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
        sig_split h
        sig_reduce [Proof.Sm4Gcm.openScratchContract, Proof.Sm4Gcm.openScratchSig,
          Spec.Sm4.Gcm.openPost, Spec.Sm4.Gcm.openLeak, openX86, openPre, pubN,
          X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
        sig_simp [Proof.Sm4Gcm.openScratchContract, Proof.Sm4Gcm.openScratchSig,
          Spec.Sm4.Gcm.openPost, Spec.Sm4.Gcm.openLeak, openX86, openPre, pubN,
          X86.abi, X86.argSlots, X86.argVal, X86.argBytes] [Nat.forall_lt_succ_right, Nat.not_lt_zero,
          false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals first
          | with_reducible assumption
          | (apply leak_bool; with_reducible assumption)
      sat := by
        have a0 : arg openSat 0 = 0x1000 := by decide
        have a1 : arg openSat 1 = 0x2000 := by decide
        have a2 : arg openSat 2 = 0 := by decide
        have a3 : arg openSat 3 = 0x2100 := by decide
        have a4 : arg openSat 4 = 0 := by decide
        have a5 : arg openSat 5 = 0x3000 := by decide
        have a6 : arg openSat 6 = 0 := by decide
        have a7 : arg openSat 7 = 0x5000 := by decide
        have a8 : arg openSat 8 = 0 := by decide
        have a9 : arg openSat 9 = 0x4000 := by decide
        have e : argAddr openSat 0 = 0x8004 := by decide
        have esp : openSat.gpr .esp = 0x8000 := rfl
        sig_implies_sat [Proof.Sm4Gcm.openScratchContract, Proof.Sm4Gcm.openScratchSig,
          Spec.Sm4.Gcm.openPost, Spec.Sm4.Gcm.openLeak, openX86, openPre, pubN,
          X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
          [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, e, esp] using openSat }

/-- A state satisfying `vg_sm4_gcm_init`'s precondition: the key at
`0x1000`, the context at `0x2000` and `scratch` at `0x4000`. -/
def initSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800d then 0x40 else 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 256⟩, ⟨0x4000, 2560⟩, ⟨0x8004, 12⟩]

theorem init_verified (ki : KeyImpl) :
    Verified X86.target (init ki.fn) (Proof.Sm4Gcm.initScratchContract X86.abi 1536) :=
  Verified.of_correct (init_correct ki) (init_ct ki) (by
    have a0 : arg initSat 0 = 0x1000 := by decide
    have a1 : arg initSat 1 = 0x2000 := by decide
    have a2 : arg initSat 2 = 0x4000 := by decide
    have e : argAddr initSat 0 = 0x8004 := by decide
    have esp : initSat.gpr .esp = 0x8000 := rfl
    sig_implies [Proof.Sm4Gcm.initScratchContract, Proof.Sm4Gcm.initScratchSig, Spec.Sm4.Gcm.initPost, initX86, initPre, pubN,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes] [a0, a1, a2, e, esp] using initSat)

/-! ## The stack pointer -/

section
variable (vg : GcmImpl)

theorem init_spSafe (ki : KeyImpl) : (init ki.fn).all (fun i => !X86.isa.writesSp i) = true := by
  simp only [init, keyCall, ctrCall, entry, Code.all, ctr_spSafe, ki.spSafe,
    Bool.true_and, Bool.and_true]
  lit_decide

theorem streamEncrypt_spSafe : (streamEncrypt vg.callees).all (fun i => !X86.isa.writesSp i) = true := by
  simp only [absorb, absorbHead, absorbWhole, crypt, cryptTail, cryptWhole, ctrCall, firstFlush, flush, ghCall,
    ghash1, textAbsorb, streamEncrypt, Code.all, GcmImpl.callees, ctr_spSafe, vg.gh.spSafe, Bool.true_and,
    Bool.and_true]
  lit_decide

theorem streamDecrypt_spSafe : (streamDecrypt vg.callees).all (fun i => !X86.isa.writesSp i) = true := by
  simp only [absorb, absorbHead, absorbWhole, crypt, cryptTail, cryptWhole, ctrCall, firstFlush, flush, ghCall,
    ghash1, textAbsorb, streamDecrypt, Code.all, GcmImpl.callees, ctr_spSafe, vg.gh.spSafe, Bool.true_and,
    Bool.and_true]
  lit_decide

theorem streamFinish_spSafe : (streamFinish vg.callees).all (fun i => !X86.isa.writesSp i) = true := by
  simp only [ctrCall, finTag, flush, ghCall, ghash1, lens, tag, tagOut, streamFinish, Code.all, GcmImpl.callees,
    ctr_spSafe, vg.gh.spSafe, Bool.true_and, Bool.and_true]
  lit_decide

theorem streamVerify_spSafe : (streamVerify vg.callees).all (fun i => !X86.isa.writesSp i) = true := by
  simp only [ctrCall, finTag, flush, ghCall, ghash1, lens, tag, streamVerify, Code.all, GcmImpl.callees,
    ctr_spSafe, vg.gh.spSafe, Bool.true_and, Bool.and_true]
  lit_decide

theorem seal_spSafe : («seal» vg.callees).all (fun i => !X86.isa.writesSp i) = true := by
  simp only [absorb, absorbHead, absorbWhole, crypt, cryptTail, cryptWhole, ctrCall, flush, ghCall, ghash1, j0,
    j0hash, lens, oneAad, oneCrypt, oneTag, tag, tagOut, «seal», Code.all, GcmImpl.callees, ctr_spSafe,
    vg.gh.spSafe, Bool.true_and, Bool.and_true]
  lit_decide

theorem open_spSafe : («open» vg.callees).all (fun i => !X86.isa.writesSp i) = true := by
  simp only [absorb, absorbHead, absorbWhole, crypt, cryptTail, cryptWhole, ctrCall, flush, ghCall, ghash1, j0,
    j0hash, lens, oneAad, oneCrypt, oneTag, tag, «open», Code.all, GcmImpl.callees, ctr_spSafe, vg.gh.spSafe,
    Bool.true_and, Bool.and_true]
  lit_decide

end

end VG.Proof.Sm4Gcm.X86

end

end


/-!
# SM4-GCM's functions on x86, with their working space on the stack

Every function runs its code, proved with the working space as an argument
(`Verified.lean`), in a frame that allocates it and copies the arguments
passed on the stack (`Verified.stackScratch`): the return address, the
copied argument slots (two for `init`, seven for `stream_finish`, eight for
`stream_encrypt`, `stream_decrypt`, `stream_verify` and `seal`, nine for
`open`) and the 2560 bytes of working space. The copies are read only where
the postconditions read the buffers (`Proof/Sm4Gcm/Scratch.lean`).
`stream_init` and `stream_aad` are AES-GCM's (`Proof/AesGcm/X86/Frame.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86

open VG VG.X86 VG.Impl.Sm4Gcm.X86 VG.Proof.AesGcm.X86
open VG.Impl.AesGcm.X86 hiding ctrCall keyCall ctrArgs cryptWhole cryptTail crypt tag init cryptEntry
  streamEncrypt streamDecrypt finEntry finTag streamFinish streamVerify oneEntry oneTag oneCrypt «seal» «open»

private theorem noEsp_of {c : Prog isa} (h : NoSp c) :
    c.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq]
  exact List.all_eq_true.mpr fun i hi => by simp [h i hi]

variable (vg : GcmImpl)

theorem init_noEsp (ki : KeyImpl) : (init ki.fn).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [init, keyCall, ctrCall, entry, Code.allInstrs, noEsp_of ctr_nosp,
    noEsp_of ki.nosp, Bool.true_and, Bool.and_true]
  decide +kernel

theorem init_stackUse (ki : KeyImpl) : stackUse (init ki.fn) ≤ 1536 := by
  have hk := ki.stack
  simp only [init, keyCall, ctrCall, entry, stackUse, ctrFn, ctr_stack', Nat.max_le, X86.frameBytes,
    List.length_cons, List.length_nil]
  omega_using [hk]

theorem streamEncrypt_noEsp :
    (streamEncrypt vg.callees).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [absorb, absorbHead, absorbWhole, crypt, cryptTail, cryptWhole, ctrCall, firstFlush, flush, ghCall,
    ghash1, textAbsorb, streamEncrypt, Code.allInstrs, GcmImpl.callees, noEsp_of ctr_nosp,
    noEsp_of vg.gh.nosp, Bool.true_and, Bool.and_true]
  decide +kernel

theorem streamEncrypt_stackUse : stackUse (streamEncrypt vg.callees) ≤ 1536 := by
  simp only [absorb, absorbHead, absorbWhole, crypt, cryptTail, cryptWhole, ctrCall, firstFlush, flush, ghCall,
    ghash1, textAbsorb, streamEncrypt, stackUse, GcmImpl.callees, ctrFn, ctr_stack', vg.gh.stack, Nat.max_le]
  decide +kernel

theorem streamDecrypt_noEsp :
    (streamDecrypt vg.callees).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [absorb, absorbHead, absorbWhole, crypt, cryptTail, cryptWhole, ctrCall, firstFlush, flush, ghCall,
    ghash1, textAbsorb, streamDecrypt, Code.allInstrs, GcmImpl.callees, noEsp_of ctr_nosp,
    noEsp_of vg.gh.nosp, Bool.true_and, Bool.and_true]
  decide +kernel

theorem streamDecrypt_stackUse : stackUse (streamDecrypt vg.callees) ≤ 1536 := by
  simp only [absorb, absorbHead, absorbWhole, crypt, cryptTail, cryptWhole, ctrCall, firstFlush, flush, ghCall,
    ghash1, textAbsorb, streamDecrypt, stackUse, GcmImpl.callees, ctrFn, ctr_stack', vg.gh.stack, Nat.max_le]
  decide +kernel

theorem streamFinish_noEsp :
    (streamFinish vg.callees).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [ctrCall, finTag, flush, ghCall, ghash1, lens, tag, streamFinish, Code.allInstrs, GcmImpl.callees,
    noEsp_of ctr_nosp, noEsp_of vg.gh.nosp, Bool.true_and, Bool.and_true]
  decide +kernel

theorem streamFinish_stackUse : stackUse (streamFinish vg.callees) ≤ 1536 := by
  simp only [ctrCall, finTag, flush, ghCall, ghash1, lens, tag, streamFinish, stackUse, GcmImpl.callees, ctrFn,
    ctr_stack', vg.gh.stack, Nat.max_le]
  decide +kernel

theorem streamVerify_noEsp :
    (streamVerify vg.callees).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [ctrCall, finTag, flush, ghCall, ghash1, lens, tag, streamVerify, Code.allInstrs, GcmImpl.callees,
    noEsp_of ctr_nosp, noEsp_of vg.gh.nosp, Bool.true_and, Bool.and_true]
  decide +kernel

theorem streamVerify_stackUse : stackUse (streamVerify vg.callees) ≤ 1536 := by
  simp only [ctrCall, finTag, flush, ghCall, ghash1, lens, tag, streamVerify, stackUse, GcmImpl.callees, ctrFn,
    ctr_stack', vg.gh.stack, Nat.max_le]
  decide +kernel

theorem seal_noEsp : («seal» vg.callees).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [absorb, absorbHead, absorbWhole, crypt, cryptTail, cryptWhole, ctrCall, flush, ghCall, ghash1, j0,
    j0hash, lens, oneAad, oneCrypt, oneTag, tag, «seal», Code.allInstrs, GcmImpl.callees, noEsp_of ctr_nosp,
    noEsp_of vg.gh.nosp, Bool.true_and, Bool.and_true]
  decide +kernel

theorem seal_stackUse : stackUse («seal» vg.callees) ≤ 1536 := by
  simp only [absorb, absorbHead, absorbWhole, crypt, cryptTail, cryptWhole, ctrCall, flush, ghCall, ghash1, j0,
    j0hash, lens, oneAad, oneCrypt, oneTag, tag, «seal», stackUse, GcmImpl.callees, ctrFn, ctr_stack',
    vg.gh.stack, Nat.max_le, X86.frameBytes, List.length_cons, List.length_nil, Nat.zero_le, true_and, and_true]
  decide +kernel

theorem open_noEsp : («open» vg.callees).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [absorb, absorbHead, absorbWhole, crypt, cryptTail, cryptWhole, ctrCall, flush, ghCall, ghash1, j0,
    j0hash, lens, oneAad, oneCrypt, oneTag, tag, «open», Code.allInstrs, GcmImpl.callees, noEsp_of ctr_nosp,
    noEsp_of vg.gh.nosp, Bool.true_and, Bool.and_true]
  decide +kernel

theorem open_stackUse : stackUse («open» vg.callees) ≤ 1536 := by
  simp only [absorb, absorbHead, absorbWhole, crypt, cryptTail, cryptWhole, ctrCall, flush, ghCall, ghash1, j0,
    j0hash, lens, oneAad, oneCrypt, oneTag, tag, «open», stackUse, GcmImpl.callees, ctrFn, ctr_stack',
    vg.gh.stack, Nat.max_le, X86.frameBytes, List.length_cons, List.length_nil, Nat.zero_le, true_and, and_true]
  decide +kernel

/-- A state satisfying `vg_sm4_gcm_init`'s precondition, without the working
space: a 16-byte key at `0x1000` and the context at `0x2000`, as stack
arguments at `0x8004`. -/
def initFrameSat : State :=
  { initSat with rd := [⟨0x1000, 16⟩], wr := [⟨0x2000, 256⟩, ⟨0x8004, 8⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.initContract X86.abi 4112).pre s := by
  implies_sat [Spec.Sm4.Gcm.initContract, Spec.Sm4.Gcm.initSig, Spec.Sm4.Gcm.initPost,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [initFrameSat, initSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using initFrameSat

theorem init_framed (ki : KeyImpl) :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2576 2 (init ki.fn))
      (Spec.Sm4.Gcm.initContract X86.abi 4112) :=
  X86.Verified.stackScratch (sig := Spec.Sm4.Gcm.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (post := Spec.Sm4.Gcm.initPost X86.abi.ptrBits) (wa := true) (stack := 1536) (bytes := 2576)
    (init_verified ki) (by decide) (init_noEsp ki) (init_stackUse ki)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (initPost_local _) (fun vs m m₁ m₂ r hl _ => initPostOut_local _ vs m m₁ m₂ r hl) initFrameSat_pre

/-- A state satisfying the preconditions of `vg_sm4_gcm_stream_encrypt` and
`vg_sm4_gcm_stream_decrypt`, without the working space: their eight argument
slots at `0x8004`. -/
def crFrameSat : State :=
  { crSat with rd := [⟨0x1000, 256⟩], wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩, ⟨0x8004, 32⟩] }

theorem streamEncryptFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamEncryptContract X86.abi 4136).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamEncryptContract, Spec.Sm4.Gcm.streamCryptSig,
    Spec.Sm4.Gcm.streamEncryptPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [crFrameSat, crSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using crFrameSat

theorem streamEncrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2600 8 (streamEncrypt vg.callees))
      (Spec.Sm4.Gcm.streamEncryptContract X86.abi 4136) :=
  X86.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (post := Spec.Sm4.Gcm.streamEncryptPost X86.abi.ptrBits) (wa := true) (stack := 1536)
    (bytes := 2600) (streamEncrypt_verified (vg := vg)) (by decide) (streamEncrypt_noEsp vg)
    (streamEncrypt_stackUse vg) (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (streamEncryptPost_local _) (fun vs m m₁ m₂ r hl _ => streamEncryptPostOut_local _ vs m m₁ m₂ r hl) streamEncryptFrameSat_pre

theorem streamDecryptFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamDecryptContract X86.abi 4136).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamDecryptContract, Spec.Sm4.Gcm.streamCryptSig,
    Spec.Sm4.Gcm.streamDecryptPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [crFrameSat, crSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using crFrameSat

theorem streamDecrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2600 8 (streamDecrypt vg.callees))
      (Spec.Sm4.Gcm.streamDecryptContract X86.abi 4136) :=
  X86.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (post := Spec.Sm4.Gcm.streamDecryptPost X86.abi.ptrBits) (wa := true) (stack := 1536)
    (bytes := 2600) (streamDecrypt_verified (vg := vg)) (by decide) (streamDecrypt_noEsp vg)
    (streamDecrypt_stackUse vg) (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (streamDecryptPost_local _) (fun vs m m₁ m₂ r hl _ => streamDecryptPostOut_local _ vs m m₁ m₂ r hl) streamDecryptFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_stream_finish`'s precondition, without
the working space: its seven argument slots at `0x8004`. -/
def finFrameSat : State :=
  { finSat with wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩, ⟨0x8004, 28⟩] }

theorem finFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamFinishContract X86.abi 4132).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamFinishContract, Spec.Sm4.Gcm.streamFinishSig,
    Spec.Sm4.Gcm.streamFinishPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [finFrameSat, finSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using finFrameSat

theorem streamFinish_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2596 7 (streamFinish vg.callees))
      (Spec.Sm4.Gcm.streamFinishContract X86.abi 4132) :=
  X86.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamFinishSig) (nm := "work") (e := .u64)
    (n := 320) (post := Spec.Sm4.Gcm.streamFinishPost X86.abi.ptrBits) (wa := true) (stack := 1536)
    (bytes := 2596) (streamFinish_verified (vg := vg)) (by decide) (streamFinish_noEsp vg)
    (streamFinish_stackUse vg) (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (streamFinishPost_local _) (fun vs m m₁ m₂ r hl _ => streamFinishPostOut_local _ vs m m₁ m₂ r hl) finFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_stream_verify`'s precondition, without
the working space: its eight argument slots at `0x8004`. -/
def verFrameSat : State :=
  { verSat with wr := [⟨0x3000, 80⟩, ⟨0x8004, 32⟩] }

theorem verFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.streamVerifyContract X86.abi 4136).pre s := by
  implies_sat [Spec.Sm4.Gcm.streamVerifyContract, Spec.Sm4.Gcm.streamVerifySig,
    Spec.Sm4.Gcm.streamVerifyPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [verFrameSat, verSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using verFrameSat

theorem streamVerify_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2600 8 (streamVerify vg.callees))
      (Spec.Sm4.Gcm.streamVerifyContract X86.abi 4136) :=
  X86.Verified.stackScratch (sig := Spec.Sm4.Gcm.streamVerifySig) (nm := "work") (e := .u64)
    (n := 320) (post := Spec.Sm4.Gcm.streamVerifyPost X86.abi.ptrBits) (wa := true) (stack := 1536)
    (bytes := 2600) (streamVerify_verified (vg := vg)) (by decide) (streamVerify_noEsp vg)
    (streamVerify_stackUse vg) (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (streamVerifyPost_local _) (fun vs m m₁ m₂ r hl _ => streamVerifyPostOut_local _ vs m m₁ m₂ r hl) verFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_seal`'s precondition, without the working
space: its eight argument slots at `0x8004`. -/
def sealFrameSat : State :=
  { sealSat with wr := [⟨0x3000, 0⟩, ⟨0x5000, 16⟩, ⟨0x8004, 32⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.sealContract X86.abi 4136).pre s := by
  implies_sat [Spec.Sm4.Gcm.sealContract, Spec.Sm4.Gcm.sealSig, Spec.Sm4.Gcm.sealPost,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [sealFrameSat, sealSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using sealFrameSat

theorem seal_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2600 8 («seal» vg.callees))
      (Spec.Sm4.Gcm.sealContract X86.abi 4136) :=
  X86.Verified.stackScratch (sig := Spec.Sm4.Gcm.sealSig) (nm := "work") (e := .u64)
    (n := 320) (post := Spec.Sm4.Gcm.sealPost X86.abi.ptrBits) (wa := true) (stack := 1536)
    (bytes := 2600) (seal_verified (vg := vg)) (by decide) (seal_noEsp vg)
    (seal_stackUse vg) (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (sealPost_local _) (fun vs m m₁ m₂ r hl _ => sealPostOut_local _ vs m m₁ m₂ r hl)
    sealFrameSat_pre

/-- A state satisfying `vg_sm4_gcm_open`'s precondition, without the working
space: its nine argument slots at `0x8004`. -/
def openFrameSat : State :=
  { openSat with wr := [⟨0x3000, 0⟩, ⟨0x8004, 36⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.Sm4.Gcm.openContract X86.abi 4140).pre s := by
  implies_sat [Spec.Sm4.Gcm.openContract, Spec.Sm4.Gcm.openSig, Spec.Sm4.Gcm.openPost,
    Spec.Sm4.Gcm.openLeak, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [openFrameSat, openSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using openFrameSat

theorem open_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2604 9 («open» vg.callees))
      (Spec.Sm4.Gcm.openContract X86.abi 4140) :=
  X86.Verified.stackScratch (sig := Spec.Sm4.Gcm.openSig) (nm := "work") (e := .u64)
    (n := 320) (post := Spec.Sm4.Gcm.openPost X86.abi.ptrBits) (wa := true) (stack := 1536)
    (leak := some (Spec.Sm4.Gcm.openLeak X86.abi.ptrBits))
    (bytes := 2604) (open_verified (vg := vg)) (by decide) (open_noEsp vg)
    (open_stackUse vg) (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (openPost_local _) (fun vs m m₁ m₂ r hl _ => openPostOut_local _ vs m m₁ m₂ r hl)
    openFrameSat_pre (hleak := openLeak_local _)

end VG.Proof.Sm4Gcm.X86
