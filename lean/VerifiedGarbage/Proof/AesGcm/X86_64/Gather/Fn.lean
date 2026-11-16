module

import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.CallTo
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Loop
public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Mid
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Calls
import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
public import VerifiedGarbage.Proof.Gcm.SealGather
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.SealCallee
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.BlkCall
import VerifiedGarbage.Proof.Framework.X86_64.CallSp
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.CopyLoop
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Steps
import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Steps
import VerifiedGarbage.Proof.Gcm.Ctr
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Cmac.Spec

/-! ### `AesGcm.X86_64.Gather.SealCall`, which only this module used -/

section

/-! ### `AesGcm.X86_64.Gather.CopyPath`, which only this module used -/

section

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86-64: the blocks of a short text

Untrusted: everything here is checked by Lean. What each block of the path
of a text copied whole does, from the arguments kept in `work`: the nonce
kept in the streaming state's slots and the gathering's registers (`copyEntry_ok`), what the
gathering needs (`copyGatherPre`) and leaves (`gathered_eq`), and the
arguments of `vg_aes_gcm_seal` (`sealArgs_ok`).
-/

@[expose] public section

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
    rw [h.wr]; exact w_in hp (by omega_using [hd])
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
    fun d h₂ => Offset.contains_base _ h₂ (by omega_using [h₂])
  have cs : ∀ d, 104 ≤ d → d + 8 ≤ 184 → (stR s).Contains (W s + BitVec.ofNat 64 d) (64 / 8) := fun d h₁ h₂ => by
    have e : W s + BitVec.ofNat 64 d = St s + BitVec.ofNat 64 (d - 104) := by
      rw [St, BitVec.add_assoc, ofNat_add_ofNat]; congr 2; omega_using [h₁]
    rw [e]; exact Offset.contains_base _ (by omega_using [h₂]) (by omega_using [h₂])
  have fS : Frame [stR s] st.mem
      ((st.mem.writeW (W s + BitVec.ofNat 64 104) (Nn s)).writeW (W s + BitVec.ofNat 64 112) (s.gpr .rcx)) :=
    ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cs 104 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cs 112 (by decide) (by decide))
  refine ⟨by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg], fun r hr => ?_,
    ⟨⟨?_, fun r hr => ?_, by simp [rd_setReg, h.rd], by simp [wr_setReg, h.wr], ?_, ?_, h.mx⟩, ?_, ?_⟩⟩
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
    rw [Proof.Gcm.gathered_succ, desc_off, BitVec.setWidth_eq, ih (by omega_using [hi]), pt_succ,
      sb_eq hp hf (by omega_using [hi]), sl_eq hp hf (by omega_using [hi]), toNat_ofNat_of_lt (by
        have := gl_succ_le hp (show i < Cnt s by omega_using [hi]); have : L s < 2 ^ 64 := (stackArg s 3).isLt; omega_arith),
      slice_eq hp hf (by omega_using [hi])]

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
    (hm : st'.mem = WriteBytes.writeBytes st.mem (Dst s) (gathered 64 st.mem (Src s) (Cnt s))) (hk : GKeeps st st')
    (hmx : st'.mxcsr = st.mxcsr) : SBase s st' := by
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
    rw [hm, ← hlen]; exact bytesAt_writeBytes_self _ _ _ (by omega_using [hL, hlen])
  exact ⟨⟨⟨e1, e2, hk.rd.trans h.rd, hk.wr.trans h.wr, e5, e6, hmx.trans h.mx⟩, e7, e8⟩, e9⟩

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

end

end


/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86-64: the call of `vg_aes_gcm_seal`

Untrusted: everything here is checked by Lean. The call of
`vg_aes_gcm_seal` on the text gathered in the output, with `dst`, `len` and
`tag` pushed for it (`sealCall_ok`): what it needs, from the layout of the
entry state `s` (`sealEntry`), and that what it leaves is what
`vg_aes_gcm_seal_gather` must (`Done`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Gather

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (gathered)
open VG.Proof.AesGcm.X86_64.StreamTo (covers_cons' covers_nil' sub_add_ofNat stackArg_entry)

/-- What the function returns with. -/
def Done (s s' : State) : Prop := gprPreserved s s' ∧ Proof.AesGcm.sealGatherPostG s s'

section
variable (s : State)

/-- What the call reads and writes. -/
abbrev sealRd (M : CtxMode) : List Region := [kR M s, nR s, aR s, ⟨SP s - BitVec.ofNat 64 24, 24⟩]
abbrev sealWr : List Region := [dR s, tgR s]

end

section
variable {M : CtxMode} {s : State} (hp : SG M s)
include hp

/-- What the call of `vg_aes_gcm_seal` needs. -/
theorem sealPre_of {u : State}
    (hrsp : u.gpr .rsp = SP s - BitVec.ofNat 64 32) (hrd : u.rd = sealRd s M) (hwr : u.wr = sealWr s)
    (h_di : u.gpr .rdi = K s) (h_si : u.gpr .rsi = s.gpr .rsi) (h_dx : u.gpr .rdx = Nn s)
    (h_cx : u.gpr .rcx = s.gpr .rcx) (h_8 : u.gpr .r8 = Ad s) (h_9 : u.gpr .r9 = AL s)
    (a0 : stackArg u 0 = Dst s) (a1 : stackArg u 1 = stackArg s 3) (a2 : stackArg u 2 = Tg s)
    (hok : M.ok u.mem (K s)) :
    (sealK M).pre u := by
  have wsp := hp.w_sp
  have wsp' := hp.w_sp'
  have hargs : (Proof.AesGcm.args u 3) = ⟨SP s - BitVec.ofNat 64 24, 24⟩ := by
    simp only [Proof.AesGcm.args, stackArgAddr, hrsp]
    rw [sub_add_ofNat _ (by decide)]
  have hret : (Proof.AesGcm.ret u) = ⟨SP s - BitVec.ofNat 64 32, 8⟩ := by simp only [Proof.AesGcm.ret, hrsp]
  have hstk : below (SP s - BitVec.ofNat 64 32) 2624 = ⟨SP s - BitVec.ofNat 64 2656, 2624⟩ := by
    simp only [below]
    rw [← Offset.sub_add_eq, ← BitVec.ofNat_add]
  have tA : Region.Sub ⟨SP s - BitVec.ofNat 64 24, 24⟩ (tR s) := stk_sub (s := s) (by decide) (by decide)
  have tR' : Region.Sub ⟨SP s - BitVec.ofNat 64 32, 8⟩ (tR s) := stk_sub (s := s) (by decide) (by decide)
  have tS : Region.Sub ⟨SP s - BitVec.ofNat 64 2656, 2624⟩ (tR s) := stk_sub (s := s) (by decide) (by decide)
  have hsp32 : (SP s - BitVec.ofNat 64 32).toNat = (SP s).toNat - 32 := toNat_sub_ofNat (by omega_arith)
  have hsp24 : (SP s - BitVec.ofNat 64 24).toNat = (SP s).toNat - 24 := toNat_sub_ofNat (by omega_arith)
  have hsp2656 : (SP s - BitVec.ofNat 64 2656).toNat = (SP s).toNat - 2656 := toNat_sub_ofNat (by omega_arith)
  have d₁ : (⟨SP s - BitVec.ofNat 64 32, 8⟩ : Region).Disjoint ⟨SP s - BitVec.ofNat 64 24, 24⟩ :=
    Offset.disjoint_of_le (by simp only [hsp32, hsp24]; omega_arith) (by simp only [hsp24]; omega_arith)
  have d₂ : (⟨SP s - BitVec.ofNat 64 2656, 2624⟩ : Region).Disjoint ⟨SP s - BitVec.ofNat 64 24, 24⟩ :=
    Offset.disjoint_of_le (by simp only [hsp2656, hsp24]; omega_arith) (by simp only [hsp24]; omega_arith)
  simp only [sealK, sealPreK, Proof.AesGcm.arg, hargs, hret, hrd, hwr, h_di, h_si, h_dx, h_cx, h_8, h_9, a0, a1,
    a2, hrsp, Proof.AesGcm.rounds, hstk]
  exact ⟨trivial, trivial, hp.k_d, hp.k_t, hp.n_d, hp.n_t, hp.a_d, hp.a_t, hp.d_t, hp.b_d.symm.sub_right tA,
    hp.b_t.symm.sub_right tA, hp.b_k.sub_left tR', hp.b_n.sub_left tR', hp.b_a.sub_left tR', hp.b_d.sub_left tR',
    hp.b_t.sub_left tR', d₁, hp.b_k.sub_left tS, hp.b_n.sub_left tS, hp.b_a.sub_left tS, hp.b_d.sub_left tS,
    hp.b_t.sub_left tS, d₂, hp.w_k, hp.w_n, hp.w_ad, hp.w_d, hp.w_t, by rw [hsp32]; omega_arith, by rw [hsp32]; omega_arith,
    hp.rounds, hok⟩

/-- The registers the call of `vg_aes_gcm_seal` is entered with. -/
structure SealRegs (s st : State) : Prop where
  rdi : st.gpr .rdi = K s
  rsi : st.gpr .rsi = s.gpr .rsi
  rdx : st.gpr .rdx = Nn s
  rcx : st.gpr .rcx = s.gpr .rcx
  r8 : st.gpr .r8 = Ad s
  r9 : st.gpr .r9 = AL s
  rax : st.gpr .rax = Tg s
  r10 : st.gpr .r10 = stackArg s 3
  r11 : st.gpr .r11 = Dst s

/-- What the call of `vg_aes_gcm_seal` needs, after the push. -/
theorem sealEntry {st : State} (h : SBase s st) (g : SealRegs s st) :
    (sealK M).pre ((pushed [.rax, .r10, .r11] st).callEntry.withRegions (sealRd s M) (sealWr s)) ∧
      Covers (sealRd s M ++ sealWr s) ((pushed [.rax, .r10, .r11] st).rd ++ (pushed [.rax, .r10, .r11] st).wr) ∧
      Covers (sealWr s) (pushed [.rax, .r10, .r11] st).wr ∧
      stackArg ((pushed [.rax, .r10, .r11] st).callEntry.withRegions (sealRd s M) (sealWr s)) 0 = Dst s ∧
      stackArg ((pushed [.rax, .r10, .r11] st).callEntry.withRegions (sealRd s M) (sealWr s)) 1 = stackArg s 3 ∧
      stackArg ((pushed [.rax, .r10, .r11] st).callEntry.withRegions (sealRd s M) (sealWr s)) 2 = Tg s := by
  have wsp := hp.w_sp
  have wsp' := hp.w_sp'
  have hsp := h.rsp
  have hn8 : 8 * [Reg.rax, .r10, .r11].length ≤ (st.gpr .rsp).toNat := by rw [hsp]; simp; omega_arith
  obtain ⟨hpf, hpj⟩ := pushRegs_mem st [.rax, .r10, .r11] (by decide) hn8
  have hpj' : ∀ j (hj : j < 3), (pushed [.rax, .r10, .r11] st).mem.readW (SP s - BitVec.ofNat 64 (8 * (j + 1))) 64 =
      st.gpr ([Reg.rax, .r10, .r11][j]'hj) := fun j hj => by rw [← hsp]; exact hpj j hj
  have hP : (pushed [.rax, .r10, .r11] st).gpr .rsp = SP s - BitVec.ofNat 64 24 := by rw [pushed_rsp, hsp]; rfl
  have hpf' : Frame [⟨SP s - BitVec.ofNat 64 24, 24⟩] st.mem (pushed [.rax, .r10, .r11] st).mem := by
    rw [hsp] at hpf; exact hpf
  have hE : Frame [⟨SP s - BitVec.ofNat 64 32, 8⟩] (pushed [.rax, .r10, .r11] st).mem
      (pushed [.rax, .r10, .r11] st).callEntry.mem := by
    have := callEntry_frame (pushed [.rax, .r10, .r11] st)
    rw [hP] at this
    simpa only [below, ← Offset.sub_add_eq, ← BitVec.ofNat_add] using this
  have fU : Frame (wR s ++ [tR s]) s.mem (pushed [.rax, .r10, .r11] st).callEntry.mem :=
    (h.frame.trans (frame_stk (s := s) (by decide) (by decide) hpf')).trans
      (frame_stk (s := s) (by decide) (by decide) hE)
  have hPsp8 : 8 ≤ (SP s - BitVec.ofNat 64 24).toNat := by rw [toNat_sub_ofNat (by omega_arith)]; omega_arith
  have hPt : (SP s - BitVec.ofNat 64 24).toNat = (SP s).toNat - 24 := toNat_sub_ofNat (by omega_arith)
  have ea : ∀ j, j < 3 →
      stackArg ((pushed [.rax, .r10, .r11] st).callEntry.withRegions (sealRd s M) (sealWr s)) j =
        (pushed [.rax, .r10, .r11] st).mem.readW (SP s - BitVec.ofNat 64 24 + BitVec.ofNat 64 (8 * j)) 64 :=
    fun j hj => stackArg_entry hP hPsp8 _ _ (by rw [hPt]; omega_arith)
  have a0 := ea 0 (by decide)
  have a1 := ea 1 (by decide)
  have a2 := ea 2 (by decide)
  rw [show SP s - BitVec.ofNat 64 24 + BitVec.ofNat 64 (8 * 0) = SP s - BitVec.ofNat 64 (8 * (2 + 1)) from
    by simp, hpj' 2 (by decide)] at a0
  rw [show SP s - BitVec.ofNat 64 24 + BitVec.ofNat 64 (8 * 1) = SP s - BitVec.ofNat 64 (8 * (1 + 1)) from
    sub_add_ofNat _ (by decide), hpj' 1 (by decide)] at a1
  rw [show SP s - BitVec.ofNat 64 24 + BitVec.ofNat 64 (8 * 2) = SP s - BitVec.ofNat 64 (8 * (0 + 1)) from
    sub_add_ofNat _ (by decide), hpj' 0 (by decide)] at a2
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at a0 a1 a2
  have gU : ∀ r, r ≠ .rsp →
      ((pushed [.rax, .r10, .r11] st).callEntry.withRegions (sealRd s M) (sealWr s)).gpr r = st.gpr r :=
    fun r hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr _ _ hr]
  have hU : ((pushed [.rax, .r10, .r11] st).callEntry.withRegions (sealRd s M) (sealWr s)).gpr .rsp =
      SP s - BitVec.ofNat 64 32 := by
    rw [State.withRegions_gpr, State.callEntry_rsp, hP, ← Offset.sub_add_eq]; rfl
  have hok : M.ok ((pushed [.rax, .r10, .r11] st).callEntry.withRegions (sealRd s M) (sealWr s)).mem (K s) := by
    rw [State.withRegions_mem]
    exact M.frame fU (k_apart hp) hp.w_k hp.ok
  have hpre := sealPre_of hp hU rfl rfl (by rw [gU _ (by decide)]; exact g.rdi)
    (by rw [gU _ (by decide)]; exact g.rsi) (by rw [gU _ (by decide)]; exact g.rdx)
    (by rw [gU _ (by decide)]; exact g.rcx) (by rw [gU _ (by decide)]; exact g.r8)
    (by rw [gU _ (by decide)]; exact g.r9) (by rw [a0, g.r11]) (by rw [a1, g.r10]) (by rw [a2, g.rax]) hok
  have hPw : (pushed [.rax, .r10, .r11] st).wr = ⟨SP s - BitVec.ofNat 64 24, 24⟩ :: wR s := by
    rw [pushed_wr, hsp, h.wr, hp.wr]; rfl
  have hPr : (pushed [.rax, .r10, .r11] st).rd = [kR M s, nR s, aR s, dsR s] ++ lsR s ++ [argR s] := by
    rw [pushed_rd, h.rd, hp.rd]
  have cw : Covers (sealWr s) (pushed [.rax, .r10, .r11] st).wr := by
    rw [hPw]
    exact covers_cons' (covers_of_mem (by simp)) (covers_cons' (covers_of_mem (by simp)) covers_nil')
  have cr : Covers (sealRd s M ++ sealWr s)
      ((pushed [.rax, .r10, .r11] st).rd ++ (pushed [.rax, .r10, .r11] st).wr) := by
    rw [hPr, hPw]
    exact covers_cons' (covers_of_mem (by simp)) (covers_cons' (covers_of_mem (by simp))
      (covers_cons' (covers_of_mem (by simp)) (covers_cons' (covers_of_mem (by simp))
        (covers_cons' (covers_of_mem (by simp)) (covers_cons' (covers_of_mem (by simp)) covers_nil')))))
  exact ⟨hpre, cr, cw, by rw [a0, g.r11], by rw [a1, g.r10], by rw [a2, g.rax]⟩

/-- The call of `vg_aes_gcm_seal` on the text gathered in the output, with
`dst`, `len` and `tag` pushed for it: what `vg_aes_gcm_seal_gather` must leave. -/
theorem sealCall_ok (S : SealFn M) {st : State} (h : SBase s st) (g : SealRegs s st) :
    WP isa (.frame (.push [.rax, .r10, .r11]) (.call S.fn.name S.fn.code) (.pop .rax 3)) st (Done s) := by
  have hL : L s < 2 ^ 64 := (stackArg s 3).isLt
  have wsp := hp.w_sp
  have wsp' := hp.w_sp'
  have hsp := h.rsp
  have hn8 : 8 * [Reg.rax, .r10, .r11].length ≤ (st.gpr .rsp).toNat := by rw [hsp]; simp; omega_arith
  obtain ⟨hpf, -⟩ := pushRegs_mem st [.rax, .r10, .r11] (by decide) hn8
  have hP : (pushed [.rax, .r10, .r11] st).gpr .rsp = SP s - BitVec.ofNat 64 24 := by rw [pushed_rsp, hsp]; rfl
  have hpf' : Frame [⟨SP s - BitVec.ofNat 64 24, 24⟩] st.mem (pushed [.rax, .r10, .r11] st).mem := by
    rw [hsp] at hpf; exact hpf
  have hE : Frame [⟨SP s - BitVec.ofNat 64 32, 8⟩] (pushed [.rax, .r10, .r11] st).mem
      (pushed [.rax, .r10, .r11] st).callEntry.mem := by
    have := callEntry_frame (pushed [.rax, .r10, .r11] st)
    rw [hP] at this
    simpa only [below, ← Offset.sub_add_eq, ← BitVec.ofNat_add] using this
  have fS : Frame (wR s ++ [tR s]) st.mem (pushed [.rax, .r10, .r11] st).callEntry.mem :=
    (frame_stk (s := s) (by decide) (by decide) hpf').trans (frame_stk (s := s) (by decide) (by decide) hE)
  have fU : Frame (wR s ++ [tR s]) s.mem (pushed [.rax, .r10, .r11] st).callEntry.mem := h.frame.trans fS
  have gU : ∀ r, r ≠ .rsp →
      ((pushed [.rax, .r10, .r11] st).callEntry.withRegions (sealRd s M) (sealWr s)).gpr r = st.gpr r :=
    fun r hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr _ _ hr]
  obtain ⟨hpre, cr, cw, a0, a1, a2⟩ := sealEntry hp h g
  -- The text gathered, which the push and the return address leave as it was.
  have fS2 : Frame [⟨SP s - BitVec.ofNat 64 24, 24⟩, ⟨SP s - BitVec.ofNat 64 32, 8⟩] st.mem
      (pushed [.rax, .r10, .r11] st).callEntry.mem :=
    (hpf'.sub fun r hr => ⟨r, by simp at hr ⊢; exact Or.inl hr, fun _ h => h⟩).trans
      (hE.sub fun r hr => ⟨r, by simp at hr ⊢; exact Or.inr hr, fun _ h => h⟩)
  have eD : bytesAt (pushed [.rax, .r10, .r11] st).callEntry.mem (Dst s) (L s) = pt s (Cnt s) := by
    rw [← h.out]
    refine bytesAt_frame fS2 (fun r hr => ?_) (Nat.le_of_lt hL)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.b_d.symm.sub_right (stk_sub (s := s) (by decide) (by decide))
    · exact hp.b_d.symm.sub_right (stk_sub (s := s) (by decide) (by decide))
  refine WP.frame (by simp) (by decide) (by decide) hn8 (WP.call_sp_mx (k := sealK M)
    S.ok S.sp (by have := S.xd; omega_arith) hpre cr cw fun s' hrd' hwr' hcs hfr _ ⟨s₂, hm₂, _, hpost⟩ _ => ?_)
  have r₃ := hcs _ (by decide : Reg.rsp ∈ calleeSaved)
  simp only [sealK, Proof.AesGcm.sealX86_64, Proof.AesGcm.arg, a0, a1, a2, State.withRegions_mem,
    gU _ (by decide : Reg.rdi ≠ .rsp), gU _ (by decide : Reg.rsi ≠ .rsp), gU _ (by decide : Reg.rdx ≠ .rsp),
    gU _ (by decide : Reg.rcx ≠ .rsp), gU _ (by decide : Reg.r8 ≠ .rsp), gU _ (by decide : Reg.r9 ≠ .rsp),
    g.rdi, g.rsi, g.rdx, g.rcx, g.r8, g.r9, hm₂, ciph_eq hp fU, hk_eq hp fU, iv_eq hp fU, ad_eq hp fU, eD]
    at hpost
  have b4888 : Region.Sub (below ((pushed [.rax, .r10, .r11] st).gpr .rsp) (S.fn.code.x86_64Depth + 8)) (tR s) := by
    have h₁ := below_sub (sp := (pushed [.rax, .r10, .r11] st).gpr .rsp) (a := S.fn.code.x86_64Depth + 8)
      (b := 4864) (by have := S.xd; omega_arith) (by decide)
    have e : below (SP s - BitVec.ofNat 64 24) 4864 = ⟨SP s - BitVec.ofNat 64 4888, 4864⟩ := by
      simp only [below, ← Offset.sub_add_eq, ← BitVec.ofNat_add]
    rw [hP] at h₁ ⊢
    rw [e] at h₁
    exact fun a h => stk_sub (s := s) (by decide) (by decide) a (h₁ a h)
  have fC : Frame (wR s ++ [tR s]) st.mem s'.mem := by
    refine (hpf'.sub fun r hr => ?_).trans (hfr.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨tR s, by simp, stk_sub (s := s) (by decide) (by decide)⟩
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl) | rfl
      · exact ⟨dR s, by simp, fun _ h => h⟩
      · exact ⟨tgR s, by simp, fun _ h => h⟩
      · exact ⟨tR s, by simp, b4888⟩
  refine ⟨r₃, hwr', ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · by_cases hr' : r = .rsp
    · subst hr'; rw [popped_rsp, r₃, hP]
      show SP s - BitVec.ofNat 64 24 + BitVec.ofNat 64 24 = SP s
      exact BitVec.sub_add_cancel _ _
    · rw [popped_gpr _ _ _ hr' (fun e => by subst e; simp [calleeSaved] at hr), hcs r hr, pushed_gpr _ _ hr',
        h.saved r hr]
  · rw [popped_mem]
    exact (h.frame.trans fC).readW (Region.contains_self _ _) (ret_disj hp) (by decide)
  · show Spec.Gcm.encryptWith (ciph s) (hk s) 16 (iv s) (pt s (Cnt s)) (ad s) = _
    rw [popped_mem]
    exact hpost

end

/-- `SBase` through code that changes no memory, `rsp` or callee-saved register. -/
theorem SBase.regs {s st st' : State} (h : SBase s st) (hm : st'.mem = st.mem)
    (hcs : ∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) (hrd : st'.rd = st.rd) (hwr : st'.wr = st.wr)
    (hmx : st'.mxcsr = st.mxcsr) : SBase s st' :=
  ⟨⟨h.toBase.regs hm hcs hrd hwr hmx, hm ▸ h.nonce, hm ▸ h.nonceLen⟩, hm ▸ h.out⟩

section
variable {M : CtxMode} {s : State} (hp : SG M s)
include hp

/-- The path of a short text, after the test: the slices copied to the
output, and encrypted there by `vg_aes_gcm_seal`. -/
theorem copySeal_wp (S : SealFn M) (hL : L s < 2 ^ 63) {st : State} (h : Base s (AL s) 0 st)
    (h11 : st.gpr .r11 = W s) (hsi : st.gpr .rsi = Nn s) (hdx : st.gpr .rdx = s.gpr .rcx) :
    WP isa (Impl.AesGcm.X86_64.SealGather.copySeal S.fn) st (Done s) := by
  unfold Impl.AesGcm.X86_64.SealGather.copySeal
  refine WP.seq (WP.mono (copyEntry_ok hp h h11 hsi hdx) fun s₁ ⟨r9₁, rdi₁, r11₁, _, C₁⟩ => ?_)
  refine WP.seq (WP.mono_mx (by decide) (gatherCopy_wp s₁ (copyGatherPre hp hL C₁.toBase r9₁ rdi₁ r11₁))
    fun s₂ ⟨m₂, k₂⟩ mx₂ => ?_)
  have B₂ := gathered_after hp C₁ m₂ k₂ mx₂
  refine WP.seq (WP.mono_mx (by decide) (sealArgs_ok hp B₂) fun s₃ ⟨di, si, dx, cx, r8, r9, ax, r10, r11, cs, m, rd, wr⟩ mxw => ?_)
  exact sealCall_ok hp S (B₂.regs m cs rd wr mxw) ⟨di, si, dx, cx, r8, r9, ax, r10, r11⟩

end

end VG.Proof.AesGcm.X86_64.Gather

end

end


/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86-64: correctness

Untrusted: everything here is checked by Lean. Each piece of the code, from
what holds before it to what holds after it (`w_entry2` … `w_fin`), which
the proof of constant time follows too; the slices, one call of
`vg_aes_gcm_stream_encrypt_to` each (`slices_ok`); the text, after the
additional data padded to a whole block (`text_ok`); and the whole function
(`sealGather_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Gather

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.SealGather
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block StreamRepr ctxCiph ctxH gctr inc32 j0 fullTag)
open VG.Proof.Gcm (padA)

/-! ## What holds between the pieces -/

/-- After the first entry block. -/
def E1 (s : State) (s₁ : State) : Prop :=
  (s₁.gpr .r11 = W s ∧ (∀ r, r ≠ .r11 → r ≠ .rax → r ≠ .r10 → s₁.gpr r = s.gpr r) ∧
    s₁.mem.readW (W s + BitVec.ofNat 64 0) 64 = K s ∧
    s₁.mem.readW (W s + BitVec.ofNat 64 8) 64 = s.gpr .rsi ∧
    s₁.mem.readW (W s + BitVec.ofNat 64 16) 64 = Ad s ∧
    s₁.mem.readW (W s + BitVec.ofNat 64 24) 64 = AL s ∧
    s₁.mem.readW (W s + BitVec.ofNat 64 56) 64 = Src s ∧
    s₁.mem.readW (W s + BitVec.ofNat 64 64) 64 = stackArg s 1 ∧
    s₁.mem.readW (W s + BitVec.ofNat 64 80) 64 = AL s ∧
    Frame [kpR s] s.mem s₁.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr) ∧ s₁.mxcsr = s.mxcsr

/-- Before the call of `vg_aes_gcm_stream_init`. -/
def E2 (s : State) (st : State) : Prop :=
  Base s (AL s) 0 st ∧ st.gpr .rdi = K s ∧ st.gpr .rsi = Nn s ∧ st.gpr .rdx = s.gpr .rcx ∧ st.gpr .rcx = St s

/-- Before the call of `vg_aes_gcm_stream_aad` on the additional data. -/
def P4 (s : State) (st : State) : Prop :=
  Mid s (AL s) 0 [] st ∧ st.gpr .rdi = K s ∧ st.gpr .rsi = St s ∧ st.gpr .rdx = BitVec.ofNat 64 0 ∧
    st.gpr .rcx = Ad s ∧ st.gpr .r8 = AL s

/-- After the length of the text. -/
def T1 (s : State) (st : State) : Prop :=
  Mid s (AL s) 0 (ad s) st ∧ st.gpr .r11 = W s ∧ st.zf = some (decide (L s = 0))

/-- After the remainder of the length of the additional data. -/
def T2 (s : State) (st : State) : Prop :=
  Mid s (AL s) 0 (ad s) st ∧ st.gpr .r11 = W s ∧ st.gpr .rcx = AL s ∧
    st.gpr .r8 = BitVec.ofNat 64 ((AL s).toNat % 16) ∧ st.zf = some (decide ((AL s).toNat % 16 = 0))

/-- The length of the padding. -/
abbrev pl (s : State) : Nat := 16 - (AL s).toNat % 16

/-- The length of the additional data, padded. -/
abbrev apP (s : State) : BitVec 64 := BitVec.ofNat 64 (padA (ad s)).length

/-- Before the call of `vg_aes_gcm_stream_aad` on the padding. -/
def T3 (s : State) (st : State) : Prop :=
  Mid s (AL s + BitVec.ofNat 64 (pl s)) 0 (ad s) st ∧ st.gpr .rdi = K s ∧ st.gpr .rsi = St s ∧
    st.gpr .rdx = AL s ∧ st.gpr .rcx = W s + BitVec.ofNat 64 88 ∧ st.gpr .r8 = BitVec.ofNat 64 (pl s)

/-- Before the call of `vg_aes_gcm_stream_encrypt_to` on slice `i`. -/
def S1 (s : State) (ap : BitVec 64) (i : Nat) (A : List Byte) (st : State) : Prop :=
  Mid s ap i A st ∧ st.gpr .rdi = K s ∧ st.gpr .rsi = s.gpr .rsi ∧ st.gpr .rdx = St s ∧ st.gpr .rcx = ap ∧
    st.gpr .r8 = BitVec.ofNat 64 (gl s i) ∧ st.gpr .r9 = sb s i ∧
    st.gpr .r10 = Dst s + BitVec.ofNat 64 (gl s i) ∧ st.gpr .rax = BitVec.ofNat 64 (sl s i)

/-- After the call on slice `i`: its encryption done, the slots not yet past it. -/
def S2 (s : State) (ap : BitVec 64) (i : Nat) (A : List Byte) (st : State) : Prop :=
  Base s ap i st ∧ StreamRepr st.mem (St s) (ciph s) (hk s) (iv s) A (ct s (i + 1)) ∧
    bytesAt st.mem (Dst s) (gl s (i + 1)) = ct s (i + 1)

/-- Before the call of `vg_aes_gcm_stream_finish`: the streaming state
represents the message with the additional data and the whole ciphertext,
which the output holds. -/
def Fin (s : State) (st : State) : Prop :=
  ∃ ap i, Base s ap i st ∧ StreamRepr st.mem (St s) (ciph s) (hk s) (iv s) (ad s) (ct s (Cnt s)) ∧
    bytesAt st.mem (Dst s) (L s) = ct s (Cnt s)

/-- `Fin`, with the arguments of `vg_aes_gcm_stream_finish`. -/
def P7 (s : State) (st : State) : Prop :=
  Fin s st ∧ st.gpr .rdi = K s ∧ st.gpr .rsi = s.gpr .rsi ∧ st.gpr .rdx = St s ∧ st.gpr .rcx = AL s ∧
    st.gpr .r8 = stackArg s 3 ∧ st.gpr .r9 = Tg s

theorem length_ad (s : State) : (ad s).length = (AL s).toNat := Cmac.bytesAt_length _ _ _

theorem al_eq (s : State) : AL s = BitVec.ofNat 64 (ad s).length := by rw [length_ad, ofNat_toNat]

/-- The encryption of a text in two pieces: that of the first, then the rest. -/
theorem gctr_split (ciph : Block → Block) (icb : Block) (x y : List Byte) :
    gctr ciph icb x ++ (gctr ciph icb (x ++ y)).drop x.length = gctr ciph icb (x ++ y) := by
  rw [Proof.Gcm.gctr_append, List.drop_left' (Proof.Gcm.length_gctr _ _ _)]

theorem one_kpR {s : State} {r : Region} (hd : (kpR s).Disjoint r) : ∀ r' ∈ [kpR s], r.Disjoint r' := fun r' hr => by
  simp only [List.mem_singleton] at hr; subst hr; exact hd.symm

section
variable {M : CtxMode} {s : State} (hp : SG M s)
include hp

/-! ## The pieces -/

theorem w_entry2 {st : State} (h : E1 s st) : WP isa (.block entry2) st (E2 s) := by
  obtain ⟨⟨h11, hg, c₀, c₁, c₂, c₃, c₇, c₈, c₁₀, f₁, rd₁, wr₁⟩, mx₁⟩ := h
  exact WP.mono_mx (by decide) (entry2_ok hp h11 hg c₀ c₁ c₂ c₃ c₇ c₈ c₁₀ f₁ rd₁ wr₁)
    fun _ ⟨k, f₂, di, si, dx, cx, _, sp, cs, rd₂, wr₂⟩ mx₂ =>
      ⟨⟨sp, cs, rd₂, wr₂, k, frame_kpR f₂, mx₂.trans mx₁⟩, di, si, dx, cx⟩

theorem w_init (inl : Bool) (I : InitFn) {st : State} (h : E2 s st) :
    WP isa (callOr inl I.fn) st (Mid s (AL s) 0 []) :=
  initCall_ok hp inl I h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

theorem w_aadArgs {st : State} (h : Mid s (AL s) 0 [] st) : WP isa (.block aadArgs) st (P4 s) :=
  WP.mono_mx (by decide) (aadArgs_ok hp h.toBase) fun _ ⟨di, si, dx, cx, r8, cs, m, rd, wr⟩ mxw =>
    ⟨h.regs m cs rd wr mxw, di, si, dx, cx, r8⟩

theorem w_aad (inl : Bool) (A : AadFn) {st : State} (h : P4 s st) :
    WP isa (callOr inl A.fn) st (Mid s (AL s) 0 (ad s)) := by
  obtain ⟨M₄, di, si, dx, cx, r8⟩ := h
  refine WP.mono (aadCall_ok hp inl A M₄ (hp.a_w.symm.sub_left stR_sub) hp.b_a
    (covers_of_mem (by rw [hp.rd]; simp)) hp.w_ad (AL s).isLt di si dx cx (by rw [r8, ofNat_toNat]))
    fun _ M₅ => ?_
  rwa [List.nil_append, ad_eq hp M₄.frame] at M₅

theorem w_textLen {st : State} (h : Mid s (AL s) 0 (ad s) st) : WP isa (.block textLen) st (T1 s) :=
  WP.mono_mx (by decide) (textLen_ok hp h.toBase) fun _ ⟨r11, z, cs, m, rd, wr⟩ mxw => ⟨h.regs m cs rd wr mxw, r11, z⟩

theorem w_padLen {st : State} (h : T1 s st) : WP isa (.block padLen) st (T2 s) :=
  WP.mono_mx (by decide) (padLen_ok hp h.1.toBase h.2.1) fun _ ⟨r11, cx, r8, z, cs, m, rd, wr⟩ mxw =>
    ⟨h.1.regs m cs rd wr mxw, r11, cx, r8, z⟩

omit hp in
/-- The additional data, already a whole number of blocks. -/
theorem pad_none {st : State} (h : T2 s st) (hr : (AL s).toNat % 16 = 0) : Mid s (apP s) 0 (padA (ad s)) st := by
  have hpad : padA (ad s) = ad s := by
    simp [padA, Proof.Gcm.padLen_of_mod (show (ad s).length % 16 = 0 by rw [length_ad]; exact hr),
      Spec.Gcm.zeros]
  rw [apP, hpad, ← al_eq]
  exact h.1

theorem w_padArgs {st : State} (h : T2 s st) : WP isa (.block padArgs) st (T3 s) := by
  obtain ⟨M₂, r11, cx, r8, -⟩ := h
  exact WP.mono_mx (by decide) (padArgs_ok hp M₂.toBase r11 cx r8)
    fun s₃ ⟨di, si, dx, cx, r8, k, f, cs₃, rd₃, wr₃⟩ mx₃ =>
    ⟨⟨⟨by rw [cs₃ _ (by decide), M₂.rsp], fun r hr => by rw [cs₃ r hr, M₂.saved r hr], rd₃.trans M₂.rd,
      wr₃.trans M₂.wr, k, M₂.frame.trans (frame_kpR f), mx₃.trans M₂.mx⟩, Nat.zero_le _,
      StreamTo.streamRepr_frame f (one_kpR kpR_stR) M₂.sr, by rw [gl_zero, ct_zero]; rfl⟩, di, si, dx, cx, r8⟩

theorem w_padCall (inl : Bool) (A : AadFn) {st : State} (h : T3 s st) (hr : (AL s).toNat % 16 ≠ 0) :
    WP isa (callOr inl A.fn) st (Mid s (apP s) 0 (padA (ad s))) := by
  obtain ⟨M₃, di, si, dx, cx, r8⟩ := h
  have hw := hp.w_w
  have hpl : pl s = 16 - (AL s).toNat % 16 := rfl
  have hn : pl s ≤ 16 := by omega_using [hpl]
  have wd : (W s + BitVec.ofNat 64 88).toNat = (W s).toNat + 88 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 88) (by decide)]; omega_using [hw]
  refine WP.mono (aadCall_ok hp inl A M₃ (Offset.disjoint _ (.inr (by omega_using [hpl])) (by decide) (by omega_using [hpl]))
    (hp.b_w.sub_right (Offset.sub_base _ (by omega_using [hpl])))
    (covers_left (by rw [hp.wr]; exact StreamTo.covers_off (k := 184) (d := 88) (by simp) (by omega_using [hpl]) (by decide)))
    (by rw [wd]; omega_using [hw, hpl]) (by omega_using [hpl]) di si (by rw [dx, al_eq]) cx r8) fun s₄ M₄ => ?_
  have hpad : padA (ad s) = ad s ++ bytesAt st.mem (W s + BitVec.ofNat 64 88) (pl s) := by
    rw [M₃.kept.zeros hn]
    simp only [padA, Spec.Gcm.padLen, length_ad]
    congr 2; omega_using [hr, hpl]
  have hap : AL s + BitVec.ofNat 64 (pl s) = apP s := by
    rw [apP, hpad, List.length_append, length_ad, Cmac.bytesAt_length, ← ofNat_add_ofNat, ofNat_toNat]
  rw [← hap, hpad]
  exact M₄

theorem w_leftTest {ap : BitVec 64} {A : List Byte} {st : State} (h : Mid s ap 0 A st) :
    WP isa (.block leftTest) st fun st' => Mid s ap 0 A st' ∧ st'.zf = some (decide (Cnt s - 0 = 0)) :=
  WP.mono_mx (by decide) (leftTest_ok hp h.toBase) fun _ ⟨_, z, cs, m, rd, wr⟩ mxw => ⟨h.regs m cs rd wr mxw, z⟩

theorem w_sliceArgs {ap : BitVec 64} {A : List Byte} {i : Nat} (hi : i < Cnt s) {st : State}
    (h : Mid s ap i A st) : WP isa (.block sliceArgs) st (S1 s ap i A) :=
  WP.mono_mx (by decide) (sliceArgs_ok hp hi h.toBase) fun _ ⟨di, si, dx, cx, r8, r9, r10, ax, cs, m, rd, wr⟩ mxw =>
    ⟨h.regs m cs rd wr mxw, di, si, dx, cx, r8, r9, r10, ax⟩

theorem w_sliceCall (T : ToFn M) {ap : BitVec 64} {A : List Byte} (hap : ap = BitVec.ofNat 64 A.length)
    {i : Nat} (hi : i < Cnt s) {st : State} (h : S1 s ap i A st) :
    WP isa (.frame (.push [.rax, .r10, .rax]) (.call T.fn.name T.fn.code) (.pop .rax 3)) st (S2 s ap i A) := by
  have hL : L s < 2 ^ 64 := (stackArg s 3).isLt
  have gsl := gl_succ_le hp hi
  obtain ⟨M₁, di, si, dx, cx, r8, r9, r10, ax⟩ := h
  refine WP.mono_mx (by simp only [Code.allInstrs, T.mx, Bool.and_true]; rfl)
    (toCall_ok hp T hi M₁.toBase di si dx cx r8 r9 r10 ax) fun s₂ ⟨cs₂, rd₂, wr₂, f₂, post⟩ mx₂ => ?_
  have B₂ := M₁.toBase.after hp cs₂ rd₂ wr₂ mx₂ f₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨wkR s, by simp, stR_sub⟩
      · exact ⟨dR s, by simp, dq_sub hp hi⟩)
    fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact kpR_stR
      · exact (hp.d_w.symm.sub_left kpR_sub).sub_right (dq_sub hp hi)
  obtain ⟨sr₂, dd₂⟩ := post (iv s) A (pt s i) M₁.sr hap (length_pt s i).symm
  -- The output before slice `i`, which the call leaves as it was.
  have hD : bytesAt s₂.mem (Dst s) (gl s i) = ct s i := by
    rw [← M₁.out]
    refine bytesAt_frame f₂ (fun r hr => ?_) (by omega_using [hL, gsl])
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact hp.d_w.sub_left (Region.sub_prefix (gl_le hp (Nat.le_of_lt hi))) |>.sub_right stR_sub
    · exact Offset.base_disjoint _ (Nat.le_refl _) (by have := hp.w_d; omega_using [hL, gsl])
    · exact hp.b_d.symm.sub_left (Region.sub_prefix (gl_le hp (Nat.le_of_lt hi)))
  refine ⟨B₂, by rw [← pt_succ] at sr₂; exact sr₂, ?_⟩
  rw [gl_succ, bytesAt_add, hD, dd₂]
  show _ = gctr (ciph s) (icb s) (pt s (i + 1))
  rw [pt_succ]
  exact gctr_split _ _ _ _

theorem w_sliceNext {ap : BitVec 64} {A : List Byte} {i : Nat} (hi : i < Cnt s) {st : State}
    (h : S2 s ap i A st) :
    WP isa (.block sliceNext) st fun st' => Mid s ap (i + 1) A st' ∧ st'.zf = some (decide (Cnt s - (i + 1) = 0)) := by
  have hL : L s < 2 ^ 64 := (stackArg s 3).isLt
  have gsl := gl_succ_le hp hi
  obtain ⟨B₂, sr₂, out₂⟩ := h
  refine WP.mono_mx (by decide) (sliceNext_ok hp hi B₂) fun s₃ ⟨_, z, k, f₃, cs₃, rd₃, wr₃⟩ mx₃ =>
    ⟨⟨⟨by rw [cs₃ _ (by decide), B₂.rsp], fun r hr => by rw [cs₃ r hr, B₂.saved r hr], rd₃.trans B₂.rd,
      wr₃.trans B₂.wr, k, B₂.frame.trans (frame_kpR f₃), mx₃.trans B₂.mx⟩, by omega_using [hi],
      StreamTo.streamRepr_frame f₃ (one_kpR kpR_stR) sr₂, ?_⟩, z⟩
  rw [← out₂]
  exact bytesAt_frame f₃ (one_kpR ((hp.d_w.symm.sub_left kpR_sub).sub_right
    (Region.sub_prefix (gl_succ s i ▸ gsl)))) (by rw [gl_succ]; omega_using [hL, gsl])

/-- Slice `i`, from `Mid s ap i`: `Mid s ap (i + 1)`, and `ZF` if it was the last. -/
theorem slice_ok (T : ToFn M) {ap : BitVec 64} {A : List Byte} (hap : ap = BitVec.ofNat 64 A.length)
    {i : Nat} (hi : i < Cnt s) {st : State} (h : Mid s ap i A st) :
    WP isa (.seq (.block sliceArgs) (.seq (.frame (.push [.rax, .r10, .rax]) (.call T.fn.name T.fn.code)
      (.pop .rax 3)) (.block sliceNext))) st fun st' =>
      Mid s ap (i + 1) A st' ∧ st'.zf = some (decide (Cnt s - (i + 1) = 0)) :=
  WP.seq (WP.mono (w_sliceArgs hp hi h) fun _ h₁ => WP.seq (WP.mono (w_sliceCall hp T hap hi h₁)
    fun _ h₂ => w_sliceNext hp hi h₂))

/-- The slices, from `Mid s ap 0`: `Mid s ap (Cnt s)`. -/
theorem slices_ok (T : ToFn M) {ap : BitVec 64} {A : List Byte} (hap : ap = BitVec.ofNat 64 A.length) {st : State}
    (h : Mid s ap 0 A st) : WP isa (slices T.fn) st (Mid s ap (Cnt s) A) := by
  unfold slices
  refine WP.seq (WP.mono (w_leftTest hp h) fun s₁ ⟨M₁, z⟩ => ?_)
  refine WP.ite (decide (Cnt s - 0 = 0)) (by simp only [eval, z]) (fun e => ?_) (fun e => ?_)
  · have hC : Cnt s = 0 := by simpa using e
    exact WP.block_nil (hC ▸ M₁)
  have hC : 0 < Cnt s := by simp at e; omega_using [e]
  refine WP.loop (fun n st => ∃ i, i < Cnt s ∧ n = Cnt s - i ∧ Mid s ap i A st)
    (fun n st ⟨i, hi, hn, hM⟩ => WP.mono (slice_ok hp T hap hi hM) fun st' ⟨hM', z'⟩ => ?_) (Cnt s) s₁
    ⟨0, hC, rfl, M₁⟩
  by_cases e' : Cnt s - (i + 1) = 0
  · exact .inl ⟨by simp [eval, z', e'], (show i + 1 = Cnt s by omega_using [hi, e']) ▸ hM'⟩
  · exact .inr ⟨by simp [eval, z', e'], Cnt s - (i + 1), by omega_using [hi, hn], i + 1, by omega_using [e'], rfl, hM'⟩

/-- The encryption of all the slices, with no text. -/
theorem ct_cnt_nil (hL : L s = 0) : ct s (Cnt s) = [] :=
  List.eq_nil_of_length_eq_zero (by rw [length_ct, hp.glen, hL])

/-- No text: `Fin`. -/
theorem fin_none {st : State} (h : T1 s st) (hL : L s = 0) : Fin s st := by
  refine ⟨AL s, 0, h.1.toBase, ?_, ?_⟩
  · rw [ct_cnt_nil hp hL]; have := h.1.sr; rwa [ct_zero] at this
  · rw [ct_cnt_nil hp hL, hL]; rfl

/-- All the slices, after some text: `Fin`. -/
theorem fin_slices {st : State} (h : Mid s (apP s) (Cnt s) (padA (ad s)) st) (hL : L s ≠ 0) : Fin s st :=
  ⟨_, _, h.toBase, Proof.Gcm.streamRepr_padded (fun hc => hL (by
    rw [← hp.glen, ← length_ct, hc]; rfl)) h.sr, by rw [← hp.glen]; exact h.out⟩

/-- The text: none, or the additional data padded to a whole block, then the
slices. -/
theorem text_ok (inl : Bool) (A : AadFn) (T : ToFn M) {st : State} (h : Mid s (AL s) 0 (ad s) st) :
    WP isa (text A.fn T.fn inl) st (Fin s) := by
  unfold text
  refine WP.seq (WP.mono (w_textLen hp h) fun s₁ h₁ => ?_)
  refine WP.ite (decide (L s = 0)) (by simp only [eval, h₁.2.2]) (fun e => ?_) (fun e => ?_)
  · exact WP.block_nil (fin_none hp h₁ (by simpa using e))
  have hL : L s ≠ 0 := by simpa using e
  refine WP.seq (WP.mono (w_padLen hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (Q := Mid s (apP s) 0 (padA (ad s))) ?_ fun s₃ M₃ =>
    WP.mono (slices_ok hp T rfl M₃) fun _ M₄ => fin_slices hp M₄ hL)
  refine WP.ite (decide ((AL s).toNat % 16 = 0)) (by simp only [eval, h₂.2.2.2.2]) (fun e₂ => ?_) (fun e₂ => ?_)
  · exact WP.block_nil (pad_none h₂ (by simpa using e₂))
  have hr : (AL s).toNat % 16 ≠ 0 := by simpa using e₂
  exact WP.seq (WP.mono (w_padArgs hp h₂) fun _ h₃ => w_padCall hp inl A h₃ hr)

theorem w_finArgs {st : State} (h : Fin s st) : WP isa (.block finArgs) st (P7 s) := by
  obtain ⟨ap, i, B, sr, out⟩ := h
  exact WP.mono_mx (by decide) (finArgs_ok hp B) fun _ ⟨di, si, dx, cx, r8, r9, cs, m, rd, wr⟩ mxw =>
    ⟨⟨ap, i, B.regs m cs rd wr mxw, m ▸ sr, m ▸ out⟩, di, si, dx, cx, r8, r9⟩

theorem w_fin (inl : Bool) (F : FinFn) {st : State} (h : P7 s st) : WP isa (callOr inl F.fn) st (Done s) := by
  obtain ⟨⟨ap, i, B₇, sr₆, out₆⟩, di, si, dx, cx, r8, r9⟩ := h
  have hC : (ct s (Cnt s)).length = L s := by rw [length_ct, hp.glen]
  refine WP.mono (finCall_ok hp inl F B₇ sr₆ hC di si dx cx r8 r9) fun s₈ ⟨B₈, f₈, tag⟩ => ?_
  have hL : L s < 2 ^ 64 := (stackArg s 3).isLt
  have hdst : bytesAt s₈.mem (Dst s) (L s) = ct s (Cnt s) := by
    rw [← out₆]
    refine bytesAt_frame f₈ (fun r hr => ?_) (Nat.le_of_lt hL)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.d_w.sub_right stR_sub
    · exact hp.d_t
    · exact hp.b_d.symm
  refine ⟨⟨B₈.saved, B₈.frame.readW (Region.contains_self _ _) (ret_disj hp) (by decide)⟩, ?_⟩
  show Spec.Gcm.encryptWith (ciph s) (hk s) 16 (iv s) (pt s (Cnt s)) (ad s) =
    (bytesAt s₈.mem (Dst s) (L s), bytesAt s₈.mem (Tg s) 16)
  rw [Proof.Gcm.encryptWith_eq, hdst, tag]

/-- The streaming path, from the call of `vg_aes_gcm_stream_init` on. -/
theorem stream_wp (inl : Bool) (I : InitFn) (A : AadFn) (T : ToFn M) (F : FinFn) {st : State} (h₂ : E2 s st) :
    WP isa (stream I.fn A.fn T.fn F.fn inl) st (Done s) := by
  unfold stream
  exact WP.seq (WP.mono (w_init hp inl I h₂) fun _ h₃ => WP.seq (WP.mono (w_aadArgs hp h₃) fun _ h₄ =>
    WP.seq (WP.mono (w_aad hp inl A h₄) fun _ h₅ => WP.seq (WP.mono (text_ok hp inl A T h₅) fun _ h₆ =>
      WP.seq (WP.mono (w_finArgs hp h₆) fun _ h₇ => w_fin hp inl F h₇)))))

/-- `vg_aes_gcm_seal_gather`: `fast` for a text shorter than `q` bytes (as
`quick` sets `CF`), and otherwise `short` when
`test` sets `CF` (to `go`), and otherwise `I`, `A`, `T` and `F`. -/
theorem sealGatherG_wp {q : Nat} {quick fast test short : Prog isa} {go : Bool}
    (hquick : ∀ st, E2 s st → WP isa quick st fun st' =>
      E2 s st' ∧ st'.gpr .r11 = W s ∧ st'.cf = some (decide (L s < q)))
    (hfast : L s < q → ∀ st, E2 s st → st.gpr .r11 = W s → WP isa fast st (Done s))
    (htest : ∀ st, E2 s st → WP isa test st fun st' => E2 s st' ∧ st'.gpr .r11 = W s ∧ st'.cf = some go)
    (hshort : go = true → ∀ st, E2 s st → st.gpr .r11 = W s → WP isa short st (Done s))
    (inl : Bool) (I : InitFn) (A : AadFn) (T : ToFn M) (F : FinFn) {st : State} (hs : Same s st) :
    WP isa (sealGather quick fast test short I.fn A.fn T.fn F.fn inl) st (Done s) := by
  unfold sealGather gatherRest
  refine WP.seq (WP.mono_mx (by decide) (entry1_ok hp hs) fun _ h₁ hm =>
    WP.seq (WP.mono (w_entry2 hp ⟨h₁, hm.trans hs.mx⟩) fun _ h₂ =>
    WP.seq (WP.mono (hquick _ h₂) fun σ ⟨E₀, r₀, c₀⟩ => ?_)))
  refine WP.ite (decide (L s < q)) (by simp only [eval, c₀]) (fun e => hfast (by simpa using e) σ E₀ r₀)
    (fun _ => WP.seq (WP.mono (htest _ E₀) fun st ⟨E, r11, cf⟩ => ?_))
  exact WP.ite go (by simp only [eval, cf]) (fun e => hshort e st E r11) (fun _ => stream_wp hp inl I A T F E)

/-- The short path of `copySeal S` below `t` bytes. -/
theorem sealShort_wp (S : SealFn M) {t : Nat} (ht : t < 2 ^ 31) :
    decide (L s < t) = true → ∀ st, E2 s st → st.gpr .r11 = W s → WP isa (copySeal S.fn) st (Done s) :=
  fun e st E r11 => by
    have : L s < t := by simpa using e
    exact copySeal_wp hp S (by omega_using [ht, this]) E.1 r11 E.2.2.1 E.2.2.2.1

end

end VG.Proof.AesGcm.X86_64.Gather
