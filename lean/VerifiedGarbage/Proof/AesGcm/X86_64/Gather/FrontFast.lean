module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Front
public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.SplitCall
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Copy
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86-64: a TLS record's text from the entry

Untrusted: everything here is checked by Lean. The path `frontFast` of a
text `frontTest` passes (a 12-byte nonce, one or two slices, at most 16
bytes after the first: `front_facts`), from a state `Same` as the entry:
`ctx` and `rounds` kept in `work` (`fastEntry_ok`), the second slice, if
any, copied to the output after the first, one byte at a time
(`fastCopy_wp`), and the call of `vg_aes_gcm_seal_split` from the first
slice where it is (`frontFast_wp`), by the proofs of `copySplit`'s
(`splitCall_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Gather

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.SealGather VG.WriteBytes
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (gathered)
open VG.Proof.AesGcm.X86_64 (length_bytesAt bytesAt_frame sub_beq imm_eq)
open VG.Proof.AesGcm.X86_64.Short (CopyPre)
open VG.Proof.ChaCha20Poly1305.X86_64.Gather (ofNat_beq_zero)

/-- The fast path's state between its blocks: the stack, the callee-saved
registers, the regions and the arguments of `vg_aes_gcm_seal_split` in
registers as on entry, the memory as on entry but where the code writes, and
`ctx` and `rounds` in `work`. -/
structure FBase (s st : State) : Prop where
  rsp : st.gpr .rsp = SP s
  saved : ∀ r ∈ calleeSaved, st.gpr r = s.gpr r
  rd : st.rd = s.rd
  wr : st.wr = s.wr
  frame : Frame (wR s ++ [tR s]) s.mem st.mem
  ctx : st.mem.readW (W s + BitVec.ofNat 64 0) 64 = K s
  rounds : st.mem.readW (W s + BitVec.ofNat 64 8) 64 = s.gpr .rsi
  rdx : st.gpr .rdx = Nn s
  r8 : st.gpr .r8 = Ad s
  r9 : st.gpr .r9 = AL s

/-- `FBase` through code that changes no memory and writes none of its
registers. -/
theorem FBase.regs {s st st' : State} (h : FBase s st) (hm : st'.mem = st.mem)
    (g : ∀ r, r ∈ calleeSaved ∨ r = .rdx ∨ r = .r8 ∨ r = .r9 → st'.gpr r = st.gpr r) (hrd : st'.rd = st.rd)
    (hwr : st'.wr = st.wr) : FBase s st' :=
  ⟨by rw [g _ (Or.inl (by decide)), h.rsp], fun r hr => by rw [g r (Or.inl hr), h.saved r hr], hrd.trans h.rd,
    hwr.trans h.wr, hm ▸ h.frame, hm ▸ h.ctx, hm ▸ h.rounds, by rw [g _ (by simp), h.rdx],
    by rw [g _ (by simp), h.r8], by rw [g _ (by simp), h.r9]⟩

section
variable {M : CtxMode} {s : State} (hp : SG M s)
include hp

/-- `ctx` and `rounds` kept, the first descriptor in `r10`, and `ZF` if there
is one slice. -/
theorem fastEntry_ok {st : State} (hs : Same s st) :
    WP isa (.block fastEntry) st fun s₁ => FBase s s₁ ∧ s₁.gpr .r10 = Src s ∧
      s₁.zf = some (decide (Cnt s = 1)) := by
  have sp := same_rsp hs
  obtain ⟨a₀, e₀⟩ := same_a hp hs (i := 0) (by decide)
  obtain ⟨a₁, e₁⟩ := same_a hp hs (i := 1) (by decide)
  obtain ⟨a₅, e₅⟩ := same_a hp hs (i := 5) (by decide)
  have w : ∀ d, d + 8 ≤ 104 → InRegions st.wr (W s + BitVec.ofNat 64 d) (64 / 8) := fun d h => by
    rw [hs.wr]; exact w_in hp (by omega)
  have gdi : st.gpr .rdi = K s := hs.gpr _ (by decide) (by decide) (by decide)
  have gsi : st.gpr .rsi = s.gpr .rsi := hs.gpr _ (by decide) (by decide) (by decide)
  have hC : Cnt s < 2 ^ 64 := (stackArg s 1).isLt
  have hz : ((stackArg s 1 - BitVec.ofNat 64 1) == 0) = decide (Cnt s = 1) := by
    rw [← ofNat_toNat (stackArg s 1)]
    exact sub_beq (by omega) (by decide)
  have i1 := imm_eq (n := 1) (by decide)
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [fastEntry, gCtx, gRounds]
    xrun [a₀, e₀, a₁, e₁, a₅, e₅, w 0 (by decide), w 8 (by decide), gdi, gsi, i1], ?_, ?_, ?_⟩
  · refine ⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, gpr_arithFlags, sp]
    · have a : r ≠ .rax := by intro e; subst e; simp [calleeSaved] at hr
      have b : r ≠ .r10 := by intro e; subst e; simp [calleeSaved] at hr
      have c : r ≠ .r11 := by intro e; subst e; simp [calleeSaved] at hr
      simp [gpr_setReg, gpr_arithFlags, a, b, c]; exact hs.gpr r a b c
    · simp [rd_setReg, rd_arithFlags, hs.rd]
    · simp [wr_setReg, wr_arithFlags, hs.wr]
    · have c : ∀ d, d + 8 ≤ 104 → (kpR s).Contains (W s + BitVec.ofNat 64 d) (64 / 8) :=
        fun d h₂ => Offset.contains_base _ h₂ (by omega)
      simp only [mem_setReg, mem_arithFlags]
      rw [← hs.mem]
      exact frame_kpR (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 0 (by decide))).writeW
        (List.mem_singleton_self _) _ (c 8 (by decide)))
    all_goals simp (disch := decide) only [mem_setReg, mem_arithFlags, gpr_setReg, gpr_arithFlags, reduceCtorEq,
      ↓reduceIte, Mem.readW_writeW_self64, readW_writeW_off]
    · exact hs.gpr _ (by decide) (by decide) (by decide)
    · exact hs.gpr _ (by decide) (by decide) (by decide)
    · exact hs.gpr _ (by decide) (by decide) (by decide)
  · simp [gpr_setReg, gpr_arithFlags]
  · simp only [zf_arithFlags]
    rw [hz]

/-- The descriptors' bytes from `j` to `j + 8`, in a state of the path. -/
theorem desc_in' {st : State} (h : FBase s st) {j : Nat} (hj : j + 8 ≤ Cnt s * 16) :
    InRegions (st.rd ++ st.wr) (Src s + BitVec.ofNat 64 j) 8 := by
  rw [h.rd, h.wr, hp.rd]
  exact ⟨dsR s, by simp, Offset.contains_base _ hj (by have := hp.w_ds; omega)⟩

/-- Stack argument `i`, in a state of the path. -/
theorem fa_in {st : State} (h : FBase s st) {i : Nat} (hi : i < 6) :
    InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 (8 * (i + 1))) 8 ∧
      st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 (8 * (i + 1))) 64 = stackArg s i := by
  rw [h.rd, h.wr, h.rsp]; exact ⟨a_in hp hi, keep_a hp h.frame hi⟩

/-- The second slice's length into `rcx`, `ZF` if it is empty. -/
theorem fastLen2_ok (hc : Cnt s = 2) {st : State} (h : FBase s st) (h10 : st.gpr .r10 = Src s) :
    WP isa (.block fastLen2) st fun s₂ => FBase s s₂ ∧ s₂.gpr .r10 = Src s ∧
      s₂.gpr .rcx = BitVec.ofNat 64 (sl s 1) ∧ s₂.zf = some (decide (sl s 1 = 0)) := by
  have d₂₄ := desc_in' hp h (j := 24) (by omega)
  have v₂₄ : st.mem.readW (Src s + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (sl s 1) := by
    rw [← sl_eq hp h.frame (i := 1) (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
  have hl : sl s 1 < 2 ^ 64 := BitVec.isLt _
  apply WP.of_runBlock
  refine ⟨_, by simp only [fastLen2]; xrun [h10, d₂₄, v₂₄], ?_, ?_, ?_, ?_⟩
  · exact h.regs (by simp [mem_setReg, mem_arithFlags]) (fun r hr => by
      have : r ≠ .rcx := by rcases hr with hr | rfl | rfl | rfl <;> [(intro e; subst e; simp [calleeSaved] at hr); decide; decide; decide]
      simp [gpr_setReg, gpr_arithFlags, this]) (by simp [rd_setReg, rd_arithFlags]) (by simp [wr_setReg, wr_arithFlags])
  · simp [gpr_setReg, gpr_arithFlags, h10]
  · simp [gpr_setReg, gpr_arithFlags]
  · simp only [zf_arithFlags, gpr_setReg, ↓reduceIte, BitVec.and_self]
    rw [ofNat_beq_zero hl]

/-- The copy's registers: the second slice, the output after the first, and
an index of 0. -/
theorem fastCopy_ok (hc : Cnt s = 2) (hlt : sl s 1 < 2 ^ 63) {st : State} (h : FBase s st)
    (h10 : st.gpr .r10 = Src s) (hcx : st.gpr .rcx = BitVec.ofNat 64 (sl s 1)) :
    WP isa (.block fastCopy) st fun s₃ => FBase s s₃ ∧
      CopyPre s₃ (sb s 1) (Dst s + BitVec.ofNat 64 (fl s)) (sl s 1) ∧ s₃.gpr .r10 = BitVec.ofNat 64 0 := by
  have hfl := fl_le hp
  have hL : L s < 2 ^ 64 := (stackArg s 3).isLt
  obtain ⟨a₂, e₂⟩ := fa_in hp h (i := 2) (by decide)
  have d₁₆ := desc_in' hp h (j := 16) (by omega)
  have d₈ := desc_in' hp h (j := 8) (by omega)
  have v₁₆ : st.mem.readW (Src s + BitVec.ofNat 64 16) 64 = sb s 1 := sb_eq hp h.frame (i := 1) (by omega)
  have v₈ : st.mem.readW (Src s + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 (fl s) := by
    have := sl_eq hp h.frame (i := 0) (by omega)
    rw [show Src s + BitVec.ofNat 64 (16 * 0) = Src s by simp] at this
    rw [this, fl_eq]; simp [hc]
  have hgl : fl s + sl s 1 = L s := by
    have := hp.glen
    rw [hc, show (2 : Nat) = 0 + 1 + 1 from rfl, gl_succ, gl_succ, gl_zero] at this
    rw [fl_eq]; simp [hc]; omega
  have hsl : (⟨sb s 1, sl s 1⟩ : Region) ∈ lsR s := slice_mem s (i := 1) (by omega)
  apply WP.of_runBlock
  refine ⟨_, by simp only [fastCopy]; xrun [h10, a₂, e₂, d₁₆, v₁₆, d₈, v₈], ?_, ?_, ?_⟩
  · exact h.regs (by simp [mem_setReg, mem_arithFlags]) (fun r hr => by
      have a : r ≠ .rsi := by rcases hr with hr | rfl | rfl | rfl <;> [(intro e; subst e; simp [calleeSaved] at hr); decide; decide; decide]
      have b : r ≠ .rdi := by rcases hr with hr | rfl | rfl | rfl <;> [(intro e; subst e; simp [calleeSaved] at hr); decide; decide; decide]
      have c : r ≠ .r10 := by rcases hr with hr | rfl | rfl | rfl <;> [(intro e; subst e; simp [calleeSaved] at hr); decide; decide; decide]
      simp [gpr_setReg, gpr_arithFlags, a, b, c]) (by simp [rd_setReg, rd_arithFlags]) (by simp [wr_setReg, wr_arithFlags])
  · refine ⟨by simp [gpr_setReg, gpr_arithFlags], by simp [gpr_setReg, gpr_arithFlags],
      by simp [gpr_setReg, gpr_arithFlags, hcx], hlt, ?_, ?_, ?_⟩
    · simp only [rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, h.rd, h.wr]
      exact Covers.left (Covers.of_mem fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hp.rd]; simp [hsl])
    · simp only [wr_setReg, wr_arithFlags, h.wr, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨dR s, by simp, fl s, rfl, by simp only; omega⟩
    · have := (hp.ls _ hsl).1
      exact this.sub_right (by have := dK_sub hp (s := s); rw [← hgl, Nat.add_sub_cancel_left] at this; exact this)
  · simp [gpr_setReg, gpr_arithFlags]

end

/-- The slices after the first, in the output after it. -/
def FOut (s st : State) : Prop :=
  bytesAt st.mem (Dst s + BitVec.ofNat 64 (fl s)) (L s - fl s) =
    gathered 64 s.mem (Src s + BitVec.ofNat 64 (16 * k0 s)) (Cnt s - k0 s)

section
variable {M : CtxMode} {s : State} (hp : SG M s)
include hp

/-- With two slices, the text is the first and the second. -/
theorem gl_two (hc : Cnt s = 2) : fl s + sl s 1 = L s := by
  have := hp.glen
  rw [hc, show (2 : Nat) = 0 + 1 + 1 from rfl, gl_succ, gl_succ, gl_zero] at this
  rw [fl_eq]; simp [hc]; omega

omit hp in
/-- With two slices, those after the first are the second. -/
theorem gathered_two (hc : Cnt s = 2) :
    gathered 64 s.mem (Src s + BitVec.ofNat 64 (16 * k0 s)) (Cnt s - k0 s) = bytesAt s.mem (sb s 1) (sl s 1) := by
  have hk : k0 s = 1 := by simp [k0, hc]
  rw [hk, hc, show 2 - 1 = 0 + 1 from rfl, gathered_zero]
  simp [gathered, Sig.listed, sb, sl]

/-- The second slice copied to the output after the first, one byte at a time. -/
theorem fastLoop_wp (hc : Cnt s = 2) (hn : sl s 1 ≠ 0) {st : State} (h : FBase s st)
    (hcp : CopyPre st (sb s 1) (Dst s + BitVec.ofNat 64 (fl s)) (sl s 1)) (h10 : st.gpr .r10 = BitVec.ofNat 64 0) :
    WP isa (.loop (.block copy1Body) .ne) st fun t => FBase s t ∧ FOut s t := by
  have hgl := gl_two hp hc
  have hfl := fl_le hp
  have hL : L s < 2 ^ 64 := (stackArg s 3).isLt
  have hsl : (⟨sb s 1, sl s 1⟩ : Region) ∈ lsR s := slice_mem s (i := 1) (by omega)
  have c0 : CInv st (sb s 1) (Dst s + BitVec.ofNat 64 (fl s)) 0 st :=
    ⟨h10, by simp [bytesAt]; rfl, fun _ _ _ _ => rfl, rfl, rfl⟩
  refine WP.mono (chunks_wp (P := fun j t => CInv st (sb s 1) (Dst s + BitVec.ofNat 64 (fl s)) j t ∧
      t.gpr .r8 = st.gpr .r8)
    (fun j t ⟨c, r8⟩ hj => let ⟨t', e, c', z, r8'⟩ := copy1Step_ok8 hcp c hj; ⟨t', e, ⟨c', r8'.trans r8⟩, z⟩)
    (by decide) (⟨c0, rfl⟩ : _ ∧ _) (by omega) (Nat.mod_one _)) fun t ⟨c, r8⟩ => ?_
  have hsub : Region.Sub ⟨Dst s + BitVec.ofNat 64 (fl s), sl s 1⟩ (dR s) := by
    have := dK_sub hp (s := s); rw [← hgl, Nat.add_sub_cancel_left] at this; exact this
  have hlen : (bytesAt st.mem (sb s 1) (sl s 1)).length = sl s 1 := length_bytesAt _ _ _
  have fD : Frame [⟨Dst s + BitVec.ofNat 64 (fl s), sl s 1⟩] st.mem t.mem :=
    ChaCha20Poly1305.X86_64.Gather.frame_of c.mem (by rw [hlen])
  have kd : ∀ r ∈ [(⟨Dst s + BitVec.ofNat 64 (fl s), sl s 1⟩ : Region)], (kpR s).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (hp.d_w.symm.sub_left kpR_sub).sub_right hsub
  have k : ∀ d, d + 8 ≤ 104 → t.mem.readW (W s + BitVec.ofNat 64 d) 64 = st.mem.readW (W s + BitVec.ofNat 64 d) 64 :=
    fun d hd' => fD.readW (Offset.contains_base _ hd' (by omega)) kd (by decide)
  have keep : ∀ r, r ∈ calleeSaved ∨ r = .rdx ∨ r = .r8 ∨ r = .r9 → t.gpr r = st.gpr r := fun r hr => by
    rcases hr with hr | rfl | rfl | rfl
    · exact c.keep r (by intro e; subst e; simp [calleeSaved] at hr) (by intro e; subst e; simp [calleeSaved] at hr)
        (by intro e; subst e; simp [calleeSaved] at hr)
    · exact c.keep _ (by decide) (by decide) (by decide)
    · exact r8
    · exact c.keep _ (by decide) (by decide) (by decide)
  refine ⟨⟨by rw [keep _ (Or.inl (by decide)), h.rsp], fun r hr => by rw [keep r (Or.inl hr), h.saved r hr],
    c.rd.trans h.rd, c.wr.trans h.wr, h.frame.trans (fD.sub fun r hr => ?_), by rw [k 0 (by decide)]; exact h.ctx,
    by rw [k 8 (by decide)]; exact h.rounds, by rw [keep _ (by simp), h.rdx], by rw [keep _ (by simp), h.r8],
    by rw [keep _ (by simp), h.r9]⟩, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨dR s, by simp, hsub⟩
  · unfold FOut
    have e := bytesAt_writeBytes_self st.mem (Dst s + BitVec.ofNat 64 (fl s)) (bytesAt st.mem (sb s 1) (sl s 1))
      (by rw [hlen]; omega)
    rw [hlen] at e
    rw [gathered_two hc, show L s - fl s = sl s 1 by omega, c.mem, e]
    exact bytesAt_frame h.frame (ls_apart hp hsl) (by have := hp.w_ls _ hsl; simp at this; omega)

end

section
variable {M : CtxMode} {s : State} (hp : SG M s)
include hp

/-- With one slice, or an empty second one, nothing follows the first. -/
theorem fout_nil {st : State} (h : Cnt s = 1 ∨ (Cnt s = 2 ∧ sl s 1 = 0)) : FOut s st := by
  have hfl := fl_le hp
  have hk : k0 s = 1 := by rcases h with h | ⟨h, -⟩ <;> simp [k0, h]
  unfold FOut
  rcases h with h | ⟨h, h0⟩
  · have hL : L s = fl s := by
      have := hp.glen
      rw [h, show (1 : Nat) = 0 + 1 from rfl, gl_succ, gl_zero] at this
      rw [fl_eq]; simp [h]; omega
    rw [hL, Nat.sub_self, hk, h]
    simp [bytesAt, gathered, Sig.listed]
  · rw [show L s - fl s = 0 by have := gl_two hp h; omega, gathered_two h, h0]
    simp [bytesAt]

/-- The second slice, if there is one, copied to the output after the first. -/
theorem fastTail_wp (hcnt : Cnt s = 1 ∨ Cnt s = 2) (hsub : L s - fl s ≤ 16) {st : State} (h : FBase s st)
    (h10 : st.gpr .r10 = Src s) (hz : st.zf = some (decide (Cnt s = 1))) :
    WP isa (.ite .e (.block [])
        (.seq (.block fastLen2) (.ite .e (.block []) (.seq (.block fastCopy) (.loop (.block copy1Body) .ne))))) st
      fun t => FBase s t ∧ FOut s t := by
  refine WP.ite (decide (Cnt s = 1)) (by simp only [eval, hz]) (fun e => WP.block_nil ⟨h, fout_nil hp (Or.inl (by simpa using e))⟩)
    (fun e => ?_)
  have hc : Cnt s = 2 := by have : Cnt s ≠ 1 := by simpa using e
                            omega
  have hgl := gl_two hp hc
  refine WP.seq (WP.mono (fastLen2_ok hp hc h h10) fun s₂ ⟨F₂, r10₂, cx₂, zf₂⟩ => ?_)
  refine WP.ite (decide (sl s 1 = 0)) (by simp only [eval, zf₂]) (fun e => WP.block_nil ⟨F₂, fout_nil hp (Or.inr ⟨hc, by simpa using e⟩)⟩)
    (fun e => ?_)
  have hn : sl s 1 ≠ 0 := by simpa using e
  exact WP.seq (WP.mono (fastCopy_ok hp hc (by omega) F₂ r10₂ cx₂) fun s₃ ⟨F₃, P₃, r10₃⟩ =>
    fastLoop_wp hp hc hn F₃ P₃ r10₃)

/-- The arguments of `vg_aes_gcm_seal_split` from the first slice. -/
theorem fastArgs_ok (hn : s.gpr .rcx = 12#64) (hc : Cnt s ≠ 0) {st : State} (h : FBase s st) (o : FOut s st) :
    WP isa (.block fastArgs) st fun t => SCBase s t ∧ SplitRegs s t := by
  obtain ⟨a₀, e₀⟩ := fa_in hp h (i := 0) (by decide)
  obtain ⟨a₂, e₂⟩ := fa_in hp h (i := 2) (by decide)
  obtain ⟨a₃, e₃⟩ := fa_in hp h (i := 3) (by decide)
  obtain ⟨a₄, e₄⟩ := fa_in hp h (i := 4) (by decide)
  have d₀ := desc_in' hp h (j := 0) (by omega)
  have d₈ := desc_in' hp h (j := 8) (by omega)
  have v₀ : st.mem.readW (Src s + BitVec.ofNat 64 0) 64 = fb s := by
    have := sb_eq hp h.frame (i := 0) (by omega)
    rw [show (16 * 0 : Nat) = 0 from rfl] at this
    rw [this]; simp [fb, hc]
  have v₈ : st.mem.readW (Src s + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 (fl s) := by
    have := sl_eq hp h.frame (i := 0) (by omega)
    rw [show Src s + BitVec.ofNat 64 (16 * 0) = Src s by simp] at this
    rw [this, fl_eq]; simp [hc]
  apply WP.of_runBlock
  refine ⟨_, by simp only [fastArgs]; xrun [a₀, e₀, a₂, e₂, a₃, e₃, a₄, e₄, d₀, v₀, d₈, v₈], ?_, ?_⟩
  · have g : ∀ r, r ∈ calleeSaved → _ := fun r (hr : r ∈ calleeSaved) => by
      have : r ≠ .rcx ∧ r ≠ .r10 ∧ r ≠ .rsi ∧ r ≠ .rdi ∧ r ≠ .rax ∧ r ≠ .r11 := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro e; subst e; simp [calleeSaved] at hr)
      exact this
    refine ⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h.rsp]
    · obtain ⟨a, b, c, d, e, f⟩ := g r hr
      simp [gpr_setReg, a, b, c, d, e, f, h.saved r hr]
    · simp [rd_setReg, h.rd]
    · simp [wr_setReg, h.wr]
    · simp only [mem_setReg]; exact h.frame
    · simp only [mem_setReg]; exact h.ctx
    · simp only [mem_setReg]; exact h.rounds
    · simp only [FOut] at o; simp only [mem_setReg]; exact o
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h.rdx]
    · simp [gpr_setReg, hn]
    · simp [gpr_setReg, h.r8]
    · simp [gpr_setReg, h.r9]
    all_goals simp [gpr_setReg]

/-- The path of a TLS record's text, from a state `Same` as the entry. -/
theorem frontFast_wp (S : SplitFn M) {long : Bool} (hg : frontGo long s = true) {st : State}
    (hs : Same s st) : WP isa (frontFast S.fn) st (Done s) := by
  obtain ⟨hn, hcnt, hsub⟩ := front_facts hp hg
  have hc0 : Cnt s ≠ 0 := by omega
  unfold frontFast
  refine WP.seq (WP.mono (fastEntry_ok hp hs) fun s₁ ⟨F₁, r10₁, zf₁⟩ => ?_)
  refine WP.seq (WP.mono (fastTail_wp hp hcnt hsub F₁ r10₁ zf₁) fun s₂ ⟨F₂, O₂⟩ => ?_)
  exact WP.seq (WP.mono (fastArgs_ok hp hn hc0 F₂ O₂) fun s₃ ⟨B₃, G₃⟩ => splitCall_ok hp S B₃ G₃)

end

end VG.Proof.AesGcm.X86_64.Gather
