import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl

/-!
# `vg_rsa_private_checked` on x86-64: the call of the CRT

The CRT runs with the stack arguments the frame holds at `rsp`, writing
`M` at `oM` (`crt_pre`), and returns with `M` written and the frame's
slots kept (`crt_call`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.PrivChecked
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64

/-- The base of the stack the function uses. -/
abbrev kb (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 stackBytes

theorem fb_sub8 (s : State) : fb s - 8 = kb s := by
  rw [fb_eq]; exact BitVec.add_sub_cancel _ _

theorem kb_toNat {s : State} (hp : PreF s) : (kb s).toNat + stackBytes + 8 + 112 ≤ 2 ^ 64 ∧
    (kb s).toNat + stackBytes = (s.gpr .rsp).toNat := by
  have := hp.sp1; have := hp.sp2
  simp only [kb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold stackBytes at *; omega

theorem toNat_off {p : Addr} {d : Nat} (h : p.toNat + d < 2 ^ 64) : (off p d).toNat = p.toNat + d := by
  simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- The stack argument `i` of a function called from the frame is the
frame's word `8 i`. -/
theorem stackArg_entry {s t : State} (hsp : t.gpr .rsp = fb s) (rd wr : List Region) {i : Nat} (hi : i < 400) :
    stackArg (t.callEntry.withRegions rd wr) i = word t.mem (fb s) (8 * i) := by
  have hsep := Offset.sep (kb s) (d := 8 * (i + 1)) (n := 8) (e := 0) (k := 8) (by omega) (by omega) (by omega)
  rw [show kb s + BitVec.ofNat 64 0 = kb s from BitVec.add_zero _] at hsep
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_mem, hsp, fb_sub8]
  rw [Mem.readW_writeW_sep hsep (by decide)]
  show _ = t.mem.readW (off (fb s) (8 * i)) 64
  rw [fb_eq, off_off, show 8 + 8 * i = 8 * (i + 1) by omega]

theorem stackArgAddr_entry {s t : State} (hsp : t.gpr .rsp = fb s) (rd wr : List Region) :
    stackArgAddr (t.callEntry.withRegions rd wr) 0 = fb s := by
  simp only [stackArgAddr, State.withRegions_gpr, State.callEntry_rsp, hsp, fb_sub8]
  rw [fb_eq]

/-- What the CRT reads. -/
def crtRd (s : State) : List Region :=
  [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨stackArg s 0, (s.gpr .rcx).toNat⟩, ⟨stackArg s 2, (stackArg s 3).toNat⟩,
    ⟨stackArg s 4, (stackArg s 5).toNat⟩, ⟨stackArg s 6, (stackArg s 7).toNat⟩,
    ⟨stackArg s 8, (stackArg s 9).toNat⟩, ⟨stackArg s 10, (stackArg s 11).toNat⟩, ⟨fb s, 96⟩]

/-- What the CRT writes: `M` and the working space. -/
def crtWr (s : State) : List Region :=
  [⟨off (fb s) oM, (s.gpr .rcx).toNat⟩, ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩]

theorem crt_pre {s t : State} (hp : PreF s) (he : Env s t)
    (hargs : ∀ i < 12, word t.mem (fb s) (8 * i) = stackArg s (i + 2)) (hdi : t.gpr .rdi = off (fb s) oM)
    (hsi : t.gpr .rsi = s.gpr .rcx) (hdx : t.gpr .rdx = s.gpr .rdx) (hcx : t.gpr .rcx = s.gpr .rcx)
    (h8 : t.gpr .r8 = stackArg s 0) (h9 : t.gpr .r9 = s.gpr .rcx) :
    crtContract.pre (t.callEntry.withRegions (crtRd s) (crtWr s)) := by
  have hE : ∀ i < 12, stackArg (t.callEntry.withRegions (crtRd s) (crtWr s)) i = stackArg s (i + 2) :=
    fun i hi => (stackArg_entry he.rsp _ _ (by omega)).trans (hargs i hi)
  simp only [crtContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.callEntry_rsp,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
    hdi, hsi, hdx, hcx, h8, h9, he.rsp, stackArgAddr_entry he.rsp, hE 0 (by decide), hE 1 (by decide),
    hE 2 (by decide), hE 3 (by decide), hE 4 (by decide), hE 5 (by decide), hE 6 (by decide), hE 7 (by decide),
    hE 8 (by decide), hE 9 (by decide), hE 10 (by decide), hE 11 (by decide), Nat.reduceAdd, fb_sub8]
  have ⟨hK1, hK2⟩ := kb_toNat hp
  have e1 : stackBytes = 3248 := rfl
  have e2 : oM = 160 := rfl
  have e3 : frameBytes = 3240 := rfl
  have hk1 := hp.k1
  have hk2 := hp.k2
  have sM : Region.Sub ⟨off (fb s) oM, (s.gpr .rcx).toNat⟩ (stkR s) := frame_sub s (by unfold oM frameBytes; omega)
  have sA : Region.Sub ⟨fb s, 96⟩ (stkR s) := by
    have := frame_sub s (d := 0) (n := 96) (by decide); simpa only [off, BitVec.add_zero] using this
  have sR : Region.Sub ⟨kb s, 8⟩ (stkR s) := Region.sub_prefix (by decide)
  have dMA : (⟨off (fb s) oM, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨fb s, 96⟩ :=
    Offset.disjoint_base _ (by decide) (by omega)
  have hfb : fb s = kb s + BitVec.ofNat 64 8 := fb_eq s
  have dRM : (⟨kb s, 8⟩ : Region).Disjoint ⟨off (fb s) oM, (s.gpr .rcx).toNat⟩ := by
    rw [hfb, off, BitVec.add_assoc, ← BitVec.ofNat_add]; exact Offset.base_disjoint _ (by decide) (by omega)
  have dRA : (⟨kb s, 8⟩ : Region).Disjoint ⟨fb s, 96⟩ := by
    rw [hfb]; exact Offset.base_disjoint _ (by decide) (by omega)
  have wM : (off (fb s) oM).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 := by
    rw [toNat_off (by rw [hfb, ← off, toNat_off (by omega)]; unfold oM; omega), hfb, ← off,
      toNat_off (by omega)]; unfold oM; omega
  have hil := hp.hil
  have dKi : (stkR s).Disjoint ⟨stackArg s 0, (s.gpr .rcx).toNat⟩ := by rw [← hil]; exact hp.dKi
  have dis : (⟨stackArg s 0, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩ := by
    rw [← hil]; exact hp.dis
  have wI : (stackArg s 0).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 := by rw [← hil]; exact hp.wI
  refine ⟨by omega, rfl, rfl, hp.dKn.sub_left sM, dKi.sub_left sM, hp.dKp.sub_left sM, hp.dKq.sub_left sM,
    hp.dKdp.sub_left sM, hp.dKdq.sub_left sM, hp.dKqi.sub_left sM, hp.dKs.sub_left sM, dMA, hp.dns, dis,
    hp.dps, hp.dqs, hp.ddps, hp.ddqs, hp.dqis, (hp.dKs.sub_left sA).symm, dRM, hp.dKn.sub_left sR, dKi.sub_left sR,
    hp.dKp.sub_left sR, hp.dKq.sub_left sR, hp.dKdp.sub_left sR, hp.dKdq.sub_left sR, hp.dKqi.sub_left sR,
    hp.dKs.sub_left sR, dRA, wM, hp.wN, wI, hp.wP, hp.wQ, hp.wDp, hp.wDq, hp.wQi, hp.wS, ⟨hk1, hk2⟩, trivial, trivial,
    hp.pl1, hp.pl2, hp.ql1, hp.ql2, hp.hdpl, hp.hqil, hp.hdql, hp.hsl⟩

/-! ## Memory across a call from the frame -/

/-- The return address a call from the frame stores. -/
theorem callEntry_frame {s t : State} (hsp : t.gpr .rsp = fb s) : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
  rw [State.callEntry_mem, hsp]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))

/-- A buffer of the caller that the function does not write, from memory
changed only where it may write. -/
theorem bytes_of_frame {s : State} {m : Mem} (hf : Frame [stkR s, outR s, scrR s] s.mem m) {p : Addr} {len : Nat}
    (hk : (stkR s).Disjoint ⟨p, len⟩) (ho : (outR s).Disjoint ⟨p, len⟩) (hs : (scrR s).Disjoint ⟨p, len⟩)
    (hl : len ≤ 2 ^ 64) : Spec.Rsa.bytesAt m p len = Spec.Rsa.bytesAt s.mem p len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => hf.bytes (R := ⟨p, len⟩) (fun r hr => ?_) hl (List.mem_range.mp hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hk.symm
  · exact ho.symm
  · exact hs.symm

/-- The return address's bytes are in the stack the function uses. -/
theorem below_sub (s : State) : Region.Sub (below (fb s) 8) (stkR s) := ret_sub s

/-- Memory changed by a call from the frame, within regions in the stack
the function uses, `out` or the working space. -/
theorem frame_call {s : State} {m₁ m₂ m₃ : Mem} (h₁ : Frame [stkR s, outR s, scrR s] m₁ m₂) {rs : List Region}
    (h₂ : Frame rs m₂ m₃) (hs : ∀ r ∈ rs, Region.Sub r (stkR s) ∨ Region.Sub r (outR s) ∨ Region.Sub r (scrR s)) :
    Frame [stkR s, outR s, scrR s] m₁ m₃ :=
  h₁.trans (h₂.sub fun r hr => by
    rcases hs r hr with h | h | h
    · exact ⟨_, List.mem_cons_self .., h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), h⟩)

theorem sub_refl (r : Region) : Region.Sub r r := fun _ h => h

/-- A slot kept by a call that writes regions apart from it. -/
theorem slot_keep {s : State} {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {d : Nat}
    (hd : ∀ r ∈ rs, (⟨off (fb s) d, 8⟩ : Region).Disjoint r) : word m' (fb s) d = word m (fb s) d :=
  hf.readW (Region.contains_self _ _) hd (by decide)

/-! ## The call -/

/-- The slots are apart from `M`, the working space and the return address. -/
theorem slot_apart {s : State} (hp : PreF s) {d : Nat} (hd : 96 ≤ d) (hd' : d + 8 ≤ oM) :
    ∀ r ∈ crtWr s ++ [below (fb s) 8], (⟨off (fb s) d, 8⟩ : Region).Disjoint r := by
  have ⟨hK1, _⟩ := kb_toNat hp
  have e1 : stackBytes = 3248 := rfl
  have e2 : oM = 160 := rfl
  have hk2 := hp.k2
  intro r hr
  simp only [crtWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  · exact (hp.dKs.sub_left (frame_sub s (by unfold frameBytes; omega)))
  · rw [show below (fb s) 8 = ⟨kb s, 8⟩ by simp only [below]; rw [← fb_sub8]; rfl, fb_eq, off_off]
    exact Offset.disjoint_base _ (by omega) (by omega)

theorem crt_covers {s t : State} (hp : PreF s) (he : Env s t) :
    Covers (crtRd s ++ crtWr s) (t.rd ++ t.wr) ∧ Covers (crtWr s) t.wr := by
  have hk2 := hp.k2
  have hil := hp.hil
  have e2 : oM = 160 := rfl
  have e3 : frameBytes = 3240 := rfl
  have hfr : (⟨fb s, frameBytes⟩ : Region) ∈ t.wr := by rw [he.wr]; exact List.mem_cons_self ..
  have hscr : (⟨stackArg s 12, (stackArg s 13).toNat * 8⟩ : Region) ∈ t.wr := by
    rw [he.wr, hp.hwr]; simp
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have cw : Covers (crtWr s) t.wr := Covers.of_sub fun r hr => by
    simp only [crtWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hfr, oM, rfl, by dsimp only; omega⟩
    · exact ⟨_, hscr, 0, z _, by dsimp only; omega⟩
  refine ⟨Covers.append_left (Covers.of_sub fun r hr => ?_) cw.right, cw⟩
  · have hrd : ∀ x, x ∈ s.rd → x ∈ t.rd ++ t.wr := fun x hx => List.mem_append_left _ (by rw [he.rd]; exact hx)
    simp only [crtRd, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, hrd ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ (by rw [hp.hrd]; simp), 0, z _,
        by dsimp only; omega⟩
    · exact ⟨⟨stackArg s 0, (stackArg s 1).toNat⟩, hrd ⟨stackArg s 0, (stackArg s 1).toNat⟩ (by rw [hp.hrd]; simp), 0,
        z _, by dsimp only; omega⟩
    · exact ⟨⟨stackArg s 2, (stackArg s 3).toNat⟩, hrd ⟨stackArg s 2, (stackArg s 3).toNat⟩ (by rw [hp.hrd]; simp), 0,
        z _, by dsimp only; omega⟩
    · exact ⟨⟨stackArg s 4, (stackArg s 5).toNat⟩, hrd ⟨stackArg s 4, (stackArg s 5).toNat⟩ (by rw [hp.hrd]; simp), 0,
        z _, by dsimp only; omega⟩
    · exact ⟨⟨stackArg s 6, (stackArg s 7).toNat⟩, hrd ⟨stackArg s 6, (stackArg s 7).toNat⟩ (by rw [hp.hrd]; simp), 0,
        z _, by dsimp only; omega⟩
    · exact ⟨⟨stackArg s 8, (stackArg s 9).toNat⟩, hrd ⟨stackArg s 8, (stackArg s 9).toNat⟩ (by rw [hp.hrd]; simp), 0,
        z _, by dsimp only; omega⟩
    · exact ⟨⟨stackArg s 10, (stackArg s 11).toNat⟩, hrd ⟨stackArg s 10, (stackArg s 11).toNat⟩ (by rw [hp.hrd]; simp), 0,
        z _, by dsimp only; omega⟩
    · exact ⟨_, List.mem_append_right _ hfr, 0, z _, by dsimp only; omega⟩

/-- The call of the CRT: `M` holds its result, which it returns. -/
theorem crt_call (v : CrtImpl) {s t : State} (hp : PreF s) (he : Env s t)
    (hargs : ∀ i < 12, word t.mem (fb s) (8 * i) = stackArg s (i + 2)) (hdi : t.gpr .rdi = off (fb s) oM)
    (hsi : t.gpr .rsi = s.gpr .rcx) (hdx : t.gpr .rdx = s.gpr .rdx) (hcx : t.gpr .rcx = s.gpr .rcx)
    (h8 : t.gpr .r8 = stackArg s 0) (h9 : t.gpr .r9 = s.gpr .rcx) :
    WP isa (.call v.name v.code) t fun t' => Env s t' ∧
      Spec.Rsa.written t'.mem (off (fb s) oM) (s.gpr .rcx).toNat ((t'.gpr .rax).setWidth 32)
        (Spec.Rsa.privateCrt (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 5).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 5).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 10) (stackArg s 3).toNat)) ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 := by
  obtain ⟨hc, hw⟩ := crt_covers hp he
  refine WP.call_mx (k := crtContract) v.ok v.nosp (by rw [v.depth]; decide)
    (crt_pre hp he hargs hdi hsi hdx hcx h8 h9) hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ hmx
  rw [v.depth, he.rsp] at hf
  have hE : ∀ i < 12, stackArg (t.callEntry.withRegions (crtRd s) (crtWr s)) i = stackArg s (i + 2) :=
    fun i hi => (stackArg_entry he.rsp _ _ (by omega)).trans (hargs i hi)
  have hfE : Frame [stkR s, outR s, scrR s] s.mem t.callEntry.mem :=
    frame_call he.mem (callEntry_frame he.rsp) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inl (below_sub s)
  have hk2 := hp.k2
  have hil := hp.hil
  have b : ∀ {p : Addr} {len : Nat}, (stkR s).Disjoint ⟨p, len⟩ → (outR s).Disjoint ⟨p, len⟩ →
      (scrR s).Disjoint ⟨p, len⟩ → len ≤ 2 ^ 64 →
      Spec.Rsa.bytesAt t.callEntry.mem p len = Spec.Rsa.bytesAt s.mem p len := fun hk ho hs hl =>
    bytes_of_frame hfE hk ho hs hl
  simp only [crtContract, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    hdi, hdx, hcx, h8, hE 0 (by decide), hE 1 (by decide), hE 2 (by decide), hE 3 (by decide), hE 4 (by decide),
    hE 6 (by decide), hE 8 (by decide), Nat.reduceAdd, hm₂, hg₂ .rax (by decide)] at hpost
  rw [b hp.dKn hp.dOn hp.dns.symm (by have := hp.wN; omega),
    b (by rw [← hil]; exact hp.dKi) (by rw [← hil]; exact hp.dOi) (by rw [← hil]; exact hp.dis.symm)
      (by omega),
    b hp.dKp hp.dOp hp.dps.symm (by have := hp.wP; omega),
    b hp.dKq hp.dOq hp.dqs.symm (by have := hp.wQ; omega),
    b (by rw [← hp.hdpl]; exact hp.dKdp) (by rw [← hp.hdpl]; exact hp.dOdp)
      (by rw [← hp.hdpl]; exact hp.ddps.symm) (by have := hp.wDp; have := hp.hdpl; omega),
    b (by rw [← hp.hdql]; exact hp.dKdq) (by rw [← hp.hdql]; exact hp.dOdq)
      (by rw [← hp.hdql]; exact hp.ddqs.symm) (by have := hp.wDq; have := hp.hdql; omega),
    b (by rw [← hp.hqil]; exact hp.dKqi) (by rw [← hp.hqil]; exact hp.dOqi)
      (by rw [← hp.hqil]; exact hp.dqis.symm) (by have := hp.wQi; have := hp.hqil; omega)] at hpost
  refine ⟨⟨(hcs .rsp (by decide)).trans he.rsp, hrd.trans he.rd, hwr.trans he.wr,
    frame_call he.mem hf fun r hr => ?_, ?_, ?_, ?_, ?_, ?_⟩, hpost, hcs, hmx⟩
  · simp only [crtWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (frame_sub s (by unfold oM frameBytes; omega))
    · exact .inr (.inr (sub_refl _))
    · exact .inl (below_sub s)
  · rw [slot_keep hf (slot_apart hp (by decide) (by decide))]; exact he.sOut
  · rw [slot_keep hf (slot_apart hp (by decide) (by decide))]; exact he.sN
  · rw [slot_keep hf (slot_apart hp (by decide) (by decide))]; exact he.sK
  · rw [slot_keep hf (slot_apart hp (by decide) (by decide))]; exact he.sE
  · rw [slot_keep hf (slot_apart hp (by decide) (by decide))]; exact he.sEl

end VG.Proof.Rsa.X86_64
