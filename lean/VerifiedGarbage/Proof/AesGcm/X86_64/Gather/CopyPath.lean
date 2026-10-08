import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Steps
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Calls
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.CopyLoop

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86-64: the blocks of a short text

Untrusted: everything here is checked by Lean. What each block of the path
of a text shorter than `t` bytes does, from the arguments kept in `work`:
the test of the length (`shortTest_ok`), the nonce kept in the streaming
state's slots and the gathering's registers (`copyEntry_ok`), what the
gathering needs (`copyGatherPre`) and leaves (`gathered_eq`), and the
arguments of `vg_aes_gcm_seal` (`sealArgs_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Gather

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.SealGather
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.ChaCha20Poly1305.X86_64.Gather (GatherPre GKeeps gatherRegs frame_of)
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes
open VG.Spec.Gcm (gathered gatheredLen)

/-- What holds after the copy: the frame, the slots kept, and the nonce and
its length in the streaming state's slots. -/
structure CBase (s : State) (st : State) : Prop extends Base s (AL s) 0 st where
  nonce : st.mem.readW (St s) 64 = Nn s
  nonceLen : st.mem.readW (St s + BitVec.ofNat 64 8) 64 = s.gpr .rcx

/-- `CBase`, with the text gathered in the output. -/
structure SBase (s : State) (st : State) : Prop extends CBase s st where
  out : bytesAt st.mem (Dst s) (L s) = pt s (Cnt s)

section
variable {M : CtxMode} {s : State} (hp : SG M s)
include hp

/-- The length of the text, `CF` if it is shorter than `t` bytes. -/
theorem shortTest_ok {t : Nat} (ht : t < 2 ^ 31) {ap : BitVec 64} {i : Nat} {st : State} (h : Base s ap i st) :
    WP isa (.block (shortTest t)) st fun st' =>
      st'.gpr .r11 = W s ∧ st'.cf = some (decide (L s < t)) ∧
      (∀ r, r ≠ .rax → r ≠ .r11 → st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  obtain ⟨a₅, e₅⟩ := h.w hp
  have r₅ := h.slot hp (d := 40) (by decide)
  have hL : L s < 2 ^ 64 := (stackArg s 3).isLt
  have hlen : st.mem.readW (W s + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 (L s) := by
    rw [h.kept.len, ofNat_toNat]
  have it := imm_eq ht
  apply WP.of_runBlock
  refine ⟨_, by simp only [shortTest, gLen]; xrun [a₅, e₅, r₅, hlen, it], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags]
  · rw [cf_arithFlags]; simp only [gpr_setReg, ite_true, reduceCtorEq, ↓reduceIte, hlen,
      toNat_ofNat_of_lt hL, toNat_ofNat_of_lt (show t < 2 ^ 64 by omega)]
  · intro r a b; simp [gpr_setReg, gpr_arithFlags, a, b]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

/-- The nonce and its length kept, and the gathering's registers: all the
slices left, `dst`, and the first descriptor. -/
theorem copyEntry_ok {st : State} (h : Base s (AL s) 0 st) (h11 : st.gpr .r11 = W s) (hsi : st.gpr .rsi = Nn s)
    (hdx : st.gpr .rdx = s.gpr .rcx) :
    WP isa (.block copyEntry) st fun st' =>
      st'.gpr .r9 = BitVec.ofNat 64 (Cnt s) ∧ st'.gpr .rdi = Dst s ∧ st'.gpr .r11 = Src s ∧
      (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ CBase s st' := by
  have hw := hp.w_w
  have r₈ := h.slot hp (d := 64) (by decide)
  have r₄ := h.slot hp (d := 32) (by decide)
  have r₇ := h.slot hp (d := 56) (by decide)
  have w : ∀ d, d + 8 ≤ 184 → InRegions st.wr (W s + BitVec.ofNat 64 d) (64 / 8) := fun d hd => by
    rw [h.wr]; exact w_in hp (by omega)
  have hleft : st.mem.readW (W s + BitVec.ofNat 64 64) 64 = BitVec.ofNat 64 (Cnt s) := by
    rw [h.kept.left, Nat.sub_zero]
  have hdesc : st.mem.readW (W s + BitVec.ofNat 64 56) 64 = Src s := by
    rw [h.kept.desc]; simp
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [copyEntry, gState, gLeft, gDst, gDesc]
    xrun [h11, hsi, hdx, w 104 (by decide), w 112 (by decide), r₈, r₄, r₇, h.kept.dst, hleft, hdesc,
      readW_writeW_off], ?_⟩
  have c : ∀ d, d + 8 ≤ 184 → (wkR s).Contains (W s + BitVec.ofNat 64 d) (64 / 8) :=
    fun d h₂ => Offset.contains_base _ h₂ (by omega)
  have cs : ∀ d, 104 ≤ d → d + 8 ≤ 184 → (stR s).Contains (W s + BitVec.ofNat 64 d) (64 / 8) := fun d h₁ h₂ => by
    have e : W s + BitVec.ofNat 64 d = St s + BitVec.ofNat 64 (d - 104) := by
      rw [St, BitVec.add_assoc, ofNat_add_ofNat]; congr 2; omega
    rw [e]; exact Offset.contains_base _ (by omega) (by omega)
  have fS : Frame [stR s] st.mem
      ((st.mem.writeW (W s + BitVec.ofNat 64 104) (Nn s)).writeW (W s + BitVec.ofNat 64 112) (s.gpr .rcx)) :=
    ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cs 104 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cs 112 (by decide) (by decide))
  refine ⟨by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg], fun r hr => ?_,
    ⟨⟨?_, fun r hr => ?_, by simp [rd_setReg, h.rd], by simp [wr_setReg, h.wr], ?_, ?_⟩, ?_, ?_⟩⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
  · simp [gpr_setReg, h.rsp]
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg] <;> exact h.saved _ (by decide)
  · simp only [mem_setReg]
    exact h.kept.frame fS fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact kpR_stR
  · simp only [mem_setReg]
    exact h.frame.trans (fS.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨wkR s, by simp, stR_sub⟩)
  · simp (disch := decide) only [mem_setReg, St, readW_writeW_off, Mem.readW_writeW_self64]
  · simp (disch := decide) only [mem_setReg, St, Offset.add_add, readW_writeW_off, Mem.readW_writeW_self64]

/-- The descriptors, byte by byte, through a frame of the regions written and
the stack. -/
theorem desc_byte {m : Mem} (hf : Frame (wR s ++ [tR s]) s.mem m) :
    ∀ a, (Sig.descRegion 64 (Src s) (Cnt s)).Contains a 1 → m a = s.mem a := fun a ha =>
  hf a fun r hr hc => ds_apart hp r hr a (by simpa [Sig.descRegion] using ha) hc

/-- The slices, through a frame of the regions written and the stack. -/
theorem listed_eq {m : Mem} (hf : Frame (wR s ++ [tR s]) s.mem m) :
    Sig.listed 64 m .u8 (Src s) (Cnt s) = lsR s :=
  Sig.listed_congr 64 .u8 _ _ (desc_byte hp hf)

/-- The bytes of the first `i` slices, through a frame of the regions written
and the stack. -/
theorem pt_eq {m : Mem} (hf : Frame (wR s ++ [tR s]) s.mem m) {i : Nat} (hi : i ≤ Cnt s) :
    gathered 64 m (Src s) i = pt s i := by
  induction i with
  | zero => simp [pt, gathered, Sig.listed]
  | succ i ih =>
    rw [Proof.Gcm.gathered_succ, desc_off, BitVec.setWidth_eq, ih (by omega), pt_succ,
      sb_eq hp hf (by omega), sl_eq hp hf (by omega), toNat_ofNat_of_lt (by
        have := gl_succ_le hp (show i < Cnt s by omega); have : L s < 2 ^ 64 := (stackArg s 3).isLt; omega),
      slice_eq hp hf (by omega)]

/-- What the gathering needs, after `copyEntry`. -/
theorem copyGatherPre {st : State} (hL : L s < 2 ^ 63) (h : Base s (AL s) 0 st)
    (h9 : st.gpr .r9 = BitVec.ofNat 64 (Cnt s)) (hdi : st.gpr .rdi = Dst s) (h11 : st.gpr .r11 = Src s) :
    GatherPre st (Src s) (Dst s) (Cnt s) (L s) := by
  have hl := listed_eq hp h.frame
  refine ⟨h11, h9, hdi, (stackArg s 1).isLt, hp.w_ds, hL, ?_, ?_, ?_, ?_, hp.ds_d, ?_⟩
  · rw [← hp.glen, gl, gatheredLen, gatheredLen, hl]
  · rw [h.rd, h.wr]; exact covers_left' (covers_of_mem (by rw [hp.rd]; simp))
  · rw [hl, h.rd, h.wr]
    intro r hr
    exact covers_left' (covers_of_mem (by rw [hp.rd]; simp [hr]))
  · rw [h.wr, hp.wr]; exact covers_of_mem (by simp)
  · rw [hl]; exact fun r hr => (hp.ls r hr).1

/-- After the gathering: the text in the output, and the rest as it was. -/
theorem gathered_after {st st' : State} (h : CBase s st)
    (hm : st'.mem = WriteBytes.writeBytes st.mem (Dst s) (gathered 64 st.mem (Src s) (Cnt s))) (hk : GKeeps st st') :
    SBase s st' := by
  have hL : L s < 2 ^ 64 := (stackArg s 3).isLt
  have hpt : gathered 64 st.mem (Src s) (Cnt s) = pt s (Cnt s) := pt_eq hp h.frame (Nat.le_refl _)
  have hlen : (pt s (Cnt s)).length = L s := by rw [length_pt, hp.glen]
  rw [hpt] at hm
  have fD : Frame [dR s] st.mem st'.mem := frame_of hm (by rw [hlen])
  have ns : ∀ r ∉ gatherRegs, st'.gpr r = st.gpr r := hk.gpr
  have sd : (stR s).Disjoint (dR s) := (hp.d_w.symm.sub_left stR_sub)
  have hcs : ∀ r ∈ calleeSaved, r ∉ gatherRegs := by decide
  have cS : (stR s).Contains (St s) (64 / 8) := by
    have := Offset.contains_base (St s) (d := 0) (n := 8) (k := 80) (by decide) (by decide)
    rwa [show St s + BitVec.ofNat 64 0 = St s from BitVec.add_zero _] at this
  have cS8 : (stR s).Contains (St s + BitVec.ofNat 64 8) (64 / 8) :=
    Offset.contains_base (St s) (d := 8) (n := 8) (k := 80) (by decide) (by decide)
  have dS : ∀ r ∈ [dR s], (stR s).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact sd
  have e1 : st'.gpr .rsp = SP s := by rw [ns .rsp (by decide), h.rsp]
  have e2 : ∀ r ∈ calleeSaved, st'.gpr r = s.gpr r := fun r hr => by rw [ns r (hcs r hr), h.saved r hr]
  have e5 : Kept s (AL s) 0 st'.mem := h.kept.frame fD fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.d_w.symm.sub_left kpR_sub
  have e6 : Frame (wR s ++ [tR s]) s.mem st'.mem := h.frame.trans (fD.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨dR s, by simp, fun _ h => h⟩)
  have e7 : st'.mem.readW (St s) 64 = Nn s := by rw [fD.readW cS dS (by decide)]; exact h.nonce
  have e8 : st'.mem.readW (St s + BitVec.ofNat 64 8) 64 = s.gpr .rcx := by
    rw [fD.readW cS8 dS (by decide)]; exact h.nonceLen
  have e9 : bytesAt st'.mem (Dst s) (L s) = pt s (Cnt s) := by
    rw [hm, ← hlen]; exact bytesAt_writeBytes_self _ _ _ (by omega)
  exact ⟨⟨⟨e1, e2, hk.rd.trans h.rd, hk.wr.trans h.wr, e5, e6⟩, e7, e8⟩, e9⟩

/-- The arguments of `vg_aes_gcm_seal(ctx, rounds, nonce, nonce_len, aad,
aad_len, dst, len, tag)`, with `tag`, `len` and `dst` to push. -/
theorem sealArgs_ok {st : State} (h : SBase s st) :
    WP isa (.block sealArgs) st fun st' =>
      st'.gpr .rdi = K s ∧ st'.gpr .rsi = s.gpr .rsi ∧ st'.gpr .rdx = Nn s ∧ st'.gpr .rcx = s.gpr .rcx ∧
      st'.gpr .r8 = Ad s ∧ st'.gpr .r9 = AL s ∧ st'.gpr .rax = Tg s ∧ st'.gpr .r10 = stackArg s 3 ∧
      st'.gpr .r11 = Dst s ∧ (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧
      st'.rd = st.rd ∧ st'.wr = st.wr := by
  have B := h.toBase
  obtain ⟨a₅, e₅⟩ := B.w hp
  have r₀ := B.slot hp (d := 0) (by decide)
  have r₁ := B.slot hp (d := 8) (by decide)
  have r₂ := B.slot hp (d := 16) (by decide)
  have r₃ := B.slot hp (d := 24) (by decide)
  have r₄ := B.slot hp (d := 32) (by decide)
  have r₅ := B.slot hp (d := 40) (by decide)
  have r₆ := B.slot hp (d := 48) (by decide)
  have r₁₃ := B.slot hp (d := 104) (by decide)
  have r₁₄ := B.slot hp (d := 112) (by decide)
  have n₀ : st.mem.readW (W s + BitVec.ofNat 64 104) 64 = Nn s := h.nonce
  have n₁ : st.mem.readW (W s + BitVec.ofNat 64 112) 64 = s.gpr .rcx := by
    rw [← h.nonceLen, St, Offset.add_add]
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [sealArgs, gCtx, gRounds, gState, gAad, gAlen, gTag, gLen, gDst]
    xrun [a₅, e₅, r₀, r₁, r₂, r₃, r₄, r₅, r₆, r₁₃, r₁₄, n₀, n₁, B.kept.ctx, B.kept.rounds, B.kept.aad,
      B.kept.alen, B.kept.tag, B.kept.len, B.kept.dst], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (simp [gpr_setReg]; done)
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
  all_goals simp [mem_setReg, rd_setReg, wr_setReg]

end

end VG.Proof.AesGcm.X86_64.Gather
