import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl
import VerifiedGarbage.Proof.Rsa.X86_64.PubChecked
import VerifiedGarbage.Proof.Rsa.Octets

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.PrivCrt`. -/
section

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

theorem fb_sub8 (s : State) : VG.Proof.Rsa.X86_64.fb s - 8 = VG.Proof.Rsa.X86_64.kb s := by
  rw [fb_eq]; exact BitVec.add_sub_cancel _ _

theorem kb_toNat {s : State} (hp : PreF s) : (VG.Proof.Rsa.X86_64.kb s).toNat + stackBytes + 8 + 112 ≤ 2 ^ 64 ∧
    (VG.Proof.Rsa.X86_64.kb s).toNat + stackBytes = (s.gpr .rsp).toNat := by
  have := hp.sp1; have := hp.sp2
  simp only [VG.Proof.Rsa.X86_64.kb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold stackBytes at *; omega

theorem toNat_off {p : Addr} {d : Nat} (h : p.toNat + d < 2 ^ 64) : (VG.Proof.Bignum.X86_64.off p d).toNat = p.toNat + d := by
  simp only [VG.Proof.Bignum.X86_64.off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- The stack argument `i` of a function called from the frame is the
frame's word `8 i`. -/
theorem stackArg_entry {s t : State} (hsp : t.gpr .rsp = VG.Proof.Rsa.X86_64.fb s) (rd wr : List Region) {i : Nat} (hi : i < 400) :
    stackArg (t.callEntry.withRegions rd wr) i = VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) (8 * i) := by
  have hsep := Offset.sep (VG.Proof.Rsa.X86_64.kb s) (d := 8 * (i + 1)) (n := 8) (e := 0) (k := 8) (by omega) (by omega) (by omega)
  rw [show VG.Proof.Rsa.X86_64.kb s + BitVec.ofNat 64 0 = VG.Proof.Rsa.X86_64.kb s from BitVec.add_zero _] at hsep
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_mem, hsp, VG.Proof.Rsa.X86_64.fb_sub8]
  rw [Mem.readW_writeW_sep hsep (by decide)]
  show _ = t.mem.readW (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) (8 * i)) 64
  rw [fb_eq, off_off, show 8 + 8 * i = 8 * (i + 1) by omega]

theorem stackArgAddr_entry {s t : State} (hsp : t.gpr .rsp = VG.Proof.Rsa.X86_64.fb s) (rd wr : List Region) :
    stackArgAddr (t.callEntry.withRegions rd wr) 0 = VG.Proof.Rsa.X86_64.fb s := by
  simp only [stackArgAddr, State.withRegions_gpr, State.callEntry_rsp, hsp, VG.Proof.Rsa.X86_64.fb_sub8]
  rw [fb_eq]

/-- What the CRT reads. -/
def crtRd (s : State) : List Region :=
  [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨stackArg s 0, (s.gpr .rcx).toNat⟩, ⟨stackArg s 2, (stackArg s 3).toNat⟩,
    ⟨stackArg s 4, (stackArg s 5).toNat⟩, ⟨stackArg s 6, (stackArg s 7).toNat⟩,
    ⟨stackArg s 8, (stackArg s 9).toNat⟩, ⟨stackArg s 10, (stackArg s 11).toNat⟩, ⟨VG.Proof.Rsa.X86_64.fb s, 96⟩]

/-- What the CRT writes: `M` and the working space. -/
def crtWr (s : State) : List Region :=
  [⟨VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) VG.Impl.Rsa.X86_64.PrivChecked.oM, (s.gpr .rcx).toNat⟩, ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩]

theorem crt_pre {s t : State} (hp : PreF s) (he : VG.Proof.Rsa.X86_64.Env s t)
    (hargs : ∀ i < 12, VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) (8 * i) = stackArg s (i + 2)) (hdi : t.gpr .rdi = VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) VG.Impl.Rsa.X86_64.PrivChecked.oM)
    (hsi : t.gpr .rsi = s.gpr .rcx) (hdx : t.gpr .rdx = s.gpr .rdx) (hcx : t.gpr .rcx = s.gpr .rcx)
    (h8 : t.gpr .r8 = stackArg s 0) (h9 : t.gpr .r9 = s.gpr .rcx) :
    crtContract.pre (t.callEntry.withRegions (VG.Proof.Rsa.X86_64.crtRd s) (VG.Proof.Rsa.X86_64.crtWr s)) := by
  have hE : ∀ i < 12, stackArg (t.callEntry.withRegions (VG.Proof.Rsa.X86_64.crtRd s) (VG.Proof.Rsa.X86_64.crtWr s)) i = stackArg s (i + 2) :=
    fun i hi => (VG.Proof.Rsa.X86_64.stackArg_entry he.rsp _ _ (by omega)).trans (hargs i hi)
  simp only [crtContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.callEntry_rsp,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
    hdi, hsi, hdx, hcx, h8, h9, he.rsp, VG.Proof.Rsa.X86_64.stackArgAddr_entry he.rsp, hE 0 (by decide), hE 1 (by decide),
    hE 2 (by decide), hE 3 (by decide), hE 4 (by decide), hE 5 (by decide), hE 6 (by decide), hE 7 (by decide),
    hE 8 (by decide), hE 9 (by decide), hE 10 (by decide), hE 11 (by decide), Nat.reduceAdd, VG.Proof.Rsa.X86_64.fb_sub8]
  have ⟨hK1, hK2⟩ := VG.Proof.Rsa.X86_64.kb_toNat hp
  have e1 : stackBytes = 3248 := rfl
  have e2 : VG.Impl.Rsa.X86_64.PrivChecked.oM = 160 := rfl
  have e3 : frameBytes = 3240 := rfl
  have hk1 := hp.k1
  have hk2 := hp.k2
  have sM : Region.Sub ⟨VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) VG.Impl.Rsa.X86_64.PrivChecked.oM, (s.gpr .rcx).toNat⟩ (stkR s) := frame_sub s (by unfold VG.Impl.Rsa.X86_64.PrivChecked.oM frameBytes; omega)
  have sA : Region.Sub ⟨VG.Proof.Rsa.X86_64.fb s, 96⟩ (stkR s) := by
    have := frame_sub s (d := 0) (n := 96) (by decide); simpa only [VG.Proof.Bignum.X86_64.off, BitVec.add_zero] using this
  have sR : Region.Sub ⟨VG.Proof.Rsa.X86_64.kb s, 8⟩ (stkR s) := Region.sub_prefix (by decide)
  have dMA : (⟨VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) VG.Impl.Rsa.X86_64.PrivChecked.oM, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨VG.Proof.Rsa.X86_64.fb s, 96⟩ :=
    Offset.disjoint_base _ (by decide) (by omega)
  have hfb : VG.Proof.Rsa.X86_64.fb s = VG.Proof.Rsa.X86_64.kb s + BitVec.ofNat 64 8 := fb_eq s
  have dRM : (⟨VG.Proof.Rsa.X86_64.kb s, 8⟩ : Region).Disjoint ⟨VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) VG.Impl.Rsa.X86_64.PrivChecked.oM, (s.gpr .rcx).toNat⟩ := by
    rw [hfb, VG.Proof.Bignum.X86_64.off, BitVec.add_assoc, ← BitVec.ofNat_add]; exact Offset.base_disjoint _ (by decide) (by omega)
  have dRA : (⟨VG.Proof.Rsa.X86_64.kb s, 8⟩ : Region).Disjoint ⟨VG.Proof.Rsa.X86_64.fb s, 96⟩ := by
    rw [hfb]; exact Offset.base_disjoint _ (by decide) (by omega)
  have wM : (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) VG.Impl.Rsa.X86_64.PrivChecked.oM).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 := by
    rw [VG.Proof.Rsa.X86_64.toNat_off (by rw [hfb, ← VG.Proof.Bignum.X86_64.off, VG.Proof.Rsa.X86_64.toNat_off (by omega)]; unfold VG.Impl.Rsa.X86_64.PrivChecked.oM; omega), hfb, ← VG.Proof.Bignum.X86_64.off,
      VG.Proof.Rsa.X86_64.toNat_off (by omega)]; unfold VG.Impl.Rsa.X86_64.PrivChecked.oM; omega
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
theorem callEntry_frame {s t : State} (hsp : t.gpr .rsp = VG.Proof.Rsa.X86_64.fb s) : Frame [below (VG.Proof.Rsa.X86_64.fb s) 8] t.mem t.callEntry.mem := by
  rw [State.callEntry_mem, hsp]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))

/-- A buffer of the caller that the function does not write, from memory
changed only where it may write. -/
theorem bytes_of_frame {s : State} {m : Mem} (hf : Frame [stkR s, VG.Proof.Rsa.X86_64.outR s, scrR s] s.mem m) {p : Addr} {len : Nat}
    (hk : (stkR s).Disjoint ⟨p, len⟩) (ho : (VG.Proof.Rsa.X86_64.outR s).Disjoint ⟨p, len⟩) (hs : (scrR s).Disjoint ⟨p, len⟩)
    (hl : len ≤ 2 ^ 64) : Spec.Rsa.bytesAt m p len = Spec.Rsa.bytesAt s.mem p len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => hf.bytes (R := ⟨p, len⟩) (fun r hr => ?_) hl (List.mem_range.mp hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hk.symm
  · exact ho.symm
  · exact hs.symm

/-- The return address's bytes are in the stack the function uses. -/
theorem below_sub (s : State) : Region.Sub (below (VG.Proof.Rsa.X86_64.fb s) 8) (stkR s) := ret_sub s

/-- Memory changed by a call from the frame, within regions in the stack
the function uses, `out` or the working space. -/
theorem frame_call {s : State} {m₁ m₂ m₃ : Mem} (h₁ : Frame [stkR s, VG.Proof.Rsa.X86_64.outR s, scrR s] m₁ m₂) {rs : List Region}
    (h₂ : Frame rs m₂ m₃) (hs : ∀ r ∈ rs, Region.Sub r (stkR s) ∨ Region.Sub r (VG.Proof.Rsa.X86_64.outR s) ∨ Region.Sub r (scrR s)) :
    Frame [stkR s, VG.Proof.Rsa.X86_64.outR s, scrR s] m₁ m₃ :=
  h₁.trans (h₂.sub fun r hr => by
    rcases hs r hr with h | h | h
    · exact ⟨_, List.mem_cons_self .., h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), h⟩)

theorem sub_refl (r : Region) : Region.Sub r r := fun _ h => h

/-- A slot kept by a call that writes regions apart from it. -/
theorem slot_keep {s : State} {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {d : Nat}
    (hd : ∀ r ∈ rs, (⟨VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) d, 8⟩ : Region).Disjoint r) : VG.Proof.Bignum.X86_64.word m' (VG.Proof.Rsa.X86_64.fb s) d = VG.Proof.Bignum.X86_64.word m (VG.Proof.Rsa.X86_64.fb s) d :=
  hf.readW (Region.contains_self _ _) hd (by decide)

/-! ## The call -/

/-- The slots are apart from `M`, the working space and the return address. -/
theorem slot_apart {s : State} (hp : PreF s) {d : Nat} (hd : 96 ≤ d) (hd' : d + 8 ≤ VG.Impl.Rsa.X86_64.PrivChecked.oM) :
    ∀ r ∈ VG.Proof.Rsa.X86_64.crtWr s ++ [below (VG.Proof.Rsa.X86_64.fb s) 8], (⟨VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) d, 8⟩ : Region).Disjoint r := by
  have ⟨hK1, _⟩ := VG.Proof.Rsa.X86_64.kb_toNat hp
  have e1 : stackBytes = 3248 := rfl
  have e2 : VG.Impl.Rsa.X86_64.PrivChecked.oM = 160 := rfl
  have hk2 := hp.k2
  intro r hr
  simp only [VG.Proof.Rsa.X86_64.crtWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  · exact (hp.dKs.sub_left (frame_sub s (by unfold frameBytes; omega)))
  · rw [show below (VG.Proof.Rsa.X86_64.fb s) 8 = ⟨VG.Proof.Rsa.X86_64.kb s, 8⟩ by simp only [below]; rw [← VG.Proof.Rsa.X86_64.fb_sub8]; rfl, fb_eq, off_off]
    exact Offset.disjoint_base _ (by omega) (by omega)

theorem crt_covers {s t : State} (hp : PreF s) (he : VG.Proof.Rsa.X86_64.Env s t) :
    Covers (VG.Proof.Rsa.X86_64.crtRd s ++ VG.Proof.Rsa.X86_64.crtWr s) (t.rd ++ t.wr) ∧ Covers (VG.Proof.Rsa.X86_64.crtWr s) t.wr := by
  have hk2 := hp.k2
  have hil := hp.hil
  have e2 : VG.Impl.Rsa.X86_64.PrivChecked.oM = 160 := rfl
  have e3 : frameBytes = 3240 := rfl
  have hfr : (⟨VG.Proof.Rsa.X86_64.fb s, frameBytes⟩ : Region) ∈ t.wr := by rw [he.wr]; exact List.mem_cons_self ..
  have hscr : (⟨stackArg s 12, (stackArg s 13).toNat * 8⟩ : Region) ∈ t.wr := by
    rw [he.wr, hp.hwr]; simp
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have cw : Covers (VG.Proof.Rsa.X86_64.crtWr s) t.wr := Covers.of_sub fun r hr => by
    simp only [VG.Proof.Rsa.X86_64.crtWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hfr, VG.Impl.Rsa.X86_64.PrivChecked.oM, rfl, by dsimp only; omega⟩
    · exact ⟨_, hscr, 0, z _, by dsimp only; omega⟩
  refine ⟨Covers.append_left (Covers.of_sub fun r hr => ?_) cw.right, cw⟩
  · have hrd : ∀ x, x ∈ s.rd → x ∈ t.rd ++ t.wr := fun x hx => List.mem_append_left _ (by rw [he.rd]; exact hx)
    simp only [VG.Proof.Rsa.X86_64.crtRd, List.mem_cons, List.not_mem_nil, or_false] at hr
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
theorem crt_call (v : CrtImpl) {s t : State} (hp : PreF s) (he : VG.Proof.Rsa.X86_64.Env s t)
    (hargs : ∀ i < 12, VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) (8 * i) = stackArg s (i + 2)) (hdi : t.gpr .rdi = VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) VG.Impl.Rsa.X86_64.PrivChecked.oM)
    (hsi : t.gpr .rsi = s.gpr .rcx) (hdx : t.gpr .rdx = s.gpr .rdx) (hcx : t.gpr .rcx = s.gpr .rcx)
    (h8 : t.gpr .r8 = stackArg s 0) (h9 : t.gpr .r9 = s.gpr .rcx) :
    WP isa (.call v.name v.code) t fun t' => VG.Proof.Rsa.X86_64.Env s t' ∧
      Spec.Rsa.written t'.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) VG.Impl.Rsa.X86_64.PrivChecked.oM) (s.gpr .rcx).toNat ((t'.gpr .rax).setWidth 32)
        (Spec.Rsa.privateCrt (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 5).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 5).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 10) (stackArg s 3).toNat)) ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 := by
  obtain ⟨hc, hw⟩ := VG.Proof.Rsa.X86_64.crt_covers hp he
  refine WP.call_mx (k := crtContract) v.ok v.nosp (by rw [v.depth]; decide)
    (VG.Proof.Rsa.X86_64.crt_pre hp he hargs hdi hsi hdx hcx h8 h9) hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ hmx
  rw [v.depth, he.rsp] at hf
  have hE : ∀ i < 12, stackArg (t.callEntry.withRegions (VG.Proof.Rsa.X86_64.crtRd s) (VG.Proof.Rsa.X86_64.crtWr s)) i = stackArg s (i + 2) :=
    fun i hi => (VG.Proof.Rsa.X86_64.stackArg_entry he.rsp _ _ (by omega)).trans (hargs i hi)
  have hfE : Frame [stkR s, VG.Proof.Rsa.X86_64.outR s, scrR s] s.mem t.callEntry.mem :=
    VG.Proof.Rsa.X86_64.frame_call he.mem (VG.Proof.Rsa.X86_64.callEntry_frame he.rsp) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inl (VG.Proof.Rsa.X86_64.below_sub s)
  have hk2 := hp.k2
  have hil := hp.hil
  have b : ∀ {p : Addr} {len : Nat}, (stkR s).Disjoint ⟨p, len⟩ → (VG.Proof.Rsa.X86_64.outR s).Disjoint ⟨p, len⟩ →
      (scrR s).Disjoint ⟨p, len⟩ → len ≤ 2 ^ 64 →
      Spec.Rsa.bytesAt t.callEntry.mem p len = Spec.Rsa.bytesAt s.mem p len := fun hk ho hs hl =>
    VG.Proof.Rsa.X86_64.bytes_of_frame hfE hk ho hs hl
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
    VG.Proof.Rsa.X86_64.frame_call he.mem hf fun r hr => ?_, ?_, ?_, ?_, ?_, ?_⟩, hpost, hcs, hmx⟩
  · simp only [VG.Proof.Rsa.X86_64.crtWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (frame_sub s (by unfold VG.Impl.Rsa.X86_64.PrivChecked.oM frameBytes; omega))
    · exact .inr (.inr (VG.Proof.Rsa.X86_64.sub_refl _))
    · exact .inl (VG.Proof.Rsa.X86_64.below_sub s)
  · rw [VG.Proof.Rsa.X86_64.slot_keep hf (VG.Proof.Rsa.X86_64.slot_apart hp (by decide) (by decide))]; exact he.sOut
  · rw [VG.Proof.Rsa.X86_64.slot_keep hf (VG.Proof.Rsa.X86_64.slot_apart hp (by decide) (by decide))]; exact he.sN
  · rw [VG.Proof.Rsa.X86_64.slot_keep hf (VG.Proof.Rsa.X86_64.slot_apart hp (by decide) (by decide))]; exact he.sK
  · rw [VG.Proof.Rsa.X86_64.slot_keep hf (VG.Proof.Rsa.X86_64.slot_apart hp (by decide) (by decide))]; exact he.sE
  · rw [VG.Proof.Rsa.X86_64.slot_keep hf (VG.Proof.Rsa.X86_64.slot_apart hp (by decide) (by decide))]; exact he.sEl

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.PrivPc`. -/
section

/-!
# `vg_rsa_private_checked` on x86-64: the call of `vg_rsa_public_precompute`

`r₁` kept in its slot, and `n`'s values written to the frame at `oPre`
(`pc_stage`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.PrivChecked
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64

/-- A stack argument past a store to the frame. -/
theorem arg_wo {s : State} (m : Mem) {d : Nat} (v : BitVec 64) (hd : d + 8 ≤ frameBytes) {j : Nat} (hj : j < 14) :
    (m.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) d) v).readW (stackArgAddr s j) 64 = m.readW (stackArgAddr s j) 64 := by
  rw [stackArgAddr_fb]
  exact word_wo m (VG.Proof.Rsa.X86_64.fb s) v (by unfold frameBytes at *; omega) (by unfold frameBytes at *; omega)
    (by unfold frameBytes; omega)

/-- `2 ⌈k / 8⌉` from `k`. -/
theorem preWords_val {x : BitVec 64} (hx : x.toNat ≤ 1024) :
    (x + BitVec.signExtend 64 (7 : BitVec 32)) >>> 3 + (x + BitVec.signExtend 64 (7 : BitVec 32)) >>> 3 =
      BitVec.ofNat 64 (Spec.Rsa.precomputedWords x.toNat) := by
  rw [sx7]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords, show (7 : BitVec 64).toNat = 7 from rfl]
  omega

/-- `r₁` kept, and the arguments of `vg_rsa_public_precompute`. -/
theorem pcArgs_ok {s t : State} (hp : PreF s) (he : VG.Proof.Rsa.X86_64.Env s t) :
    WP isa (.block pcArgs) t fun t' => VG.Proof.Rsa.X86_64.Env s t' ∧
      t'.mem = t.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) oR1) (t.gpr .rax) ∧ t'.gpr .rdi = VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) oPre ∧
      t'.gpr .rsi = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) ∧
      t'.gpr .rdx = s.gpr .rdx ∧ t'.gpr .rcx = s.gpr .rcx ∧ t'.gpr .r8 = stackArg s 12 ∧
      t'.gpr .r9 = stackArg s 13 := by
  have hs := he.scr hp
  have hk2 := hp.k2
  have harg : ∀ j < 14, InRegions (t.rd ++ t.wr) (stackArgAddr s j) 8 := fun j hj =>
    ⟨⟨stackArgAddr s 0, 112⟩, List.mem_append_left _ (by
      rw [he.rd, hp.hrd]; simp only [List.mem_cons]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl trivial))))))))),
      by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8, .r9] (Q := fun t' =>
      t'.mem = t.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) oR1) (t.gpr .rax) ∧ t'.gpr .rdi = VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) oPre ∧
      t'.gpr .rsi = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) ∧
      t'.gpr .rdx = s.gpr .rdx ∧ t'.gpr .rcx = s.gpr .rcx ∧ t'.gpr .r8 = stackArg s 12 ∧
      t'.gpr .r9 = stackArg s 13) (by
    xrun [pcArgs, lea, preWords, List.cons_append, List.nil_append, ea_sp, he.rsp, VG.Impl.Rsa.X86_64.PrivChecked.arg,
      show VG.Proof.Rsa.X86_64.fb s + BitVec.ofNat 64 (frameBytes + 8 + 8 * 12) = stackArgAddr s 12 from (stackArgAddr_fb s 12).symm,
      show VG.Proof.Rsa.X86_64.fb s + BitVec.ofNat 64 (frameBytes + 8 + 8 * 13) = stackArgAddr s 13 from (stackArgAddr_fb s 13).symm,
      hs.st (d := oR1) (by decide), hs.ld (d := oK) (by decide), hs.ld (d := oN) (by decide),
      harg 12 (by decide), harg 13 (by decide), sx_ofNat (show oPre < 2 ^ 31 by decide),
      word_wo t.mem (VG.Proof.Rsa.X86_64.fb s) (t.gpr .rax) (show oR1 + 8 ≤ oK ∨ oK + 8 ≤ oR1 by decide) (by decide) (by decide),
      word_wo t.mem (VG.Proof.Rsa.X86_64.fb s) (t.gpr .rax) (show oR1 + 8 ≤ oN ∨ oN + 8 ≤ oR1 by decide) (by decide) (by decide),
      he.sK, he.sN, VG.Proof.Rsa.X86_64.arg_wo (s := s) t.mem (t.gpr .rax) (show oR1 + 8 ≤ frameBytes by decide) (show 12 < 14 by decide),
      VG.Proof.Rsa.X86_64.arg_wo (s := s) t.mem (t.gpr .rax) (show oR1 + 8 ≤ frameBytes by decide) (show 13 < 14 by decide),
      he.arg hp (show 12 < 14 by decide), he.arg hp (show 13 < 14 by decide), VG.Proof.Rsa.X86_64.preWords_val (show
        (s.gpr .rcx).toNat ≤ 1024 by omega)]) rfl) fun t' ⟨⟨hm, hdi, hsi, hdx, hcx, h8, h9⟩, k⟩ => ⟨⟨?_, k.2.1.trans he.rd, k.2.2.trans he.wr, ?_,
      ?_, ?_, ?_, ?_, ?_⟩, hm, hdi, hsi, hdx, hcx, h8, h9⟩
  · rw [k.gpr (by decide)]; exact he.rsp
  · rw [hm]
    refine VG.Proof.Rsa.X86_64.frame_call he.mem (rs := [⟨VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) oR1, 8⟩]) ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Region.contains_self _ _)) fun r hr => ?_
    rw [List.mem_singleton.mp hr]; exact .inl (frame_sub s (by decide))
  all_goals rw [hm, word_wo _ _ _ (by decide) (by decide) (by decide)]
  · exact he.sOut
  · exact he.sN
  · exact he.sK
  · exact he.sE
  · exact he.sEl

/-! ## The call -/

/-- `n`'s values in the frame, `2 ⌈k / 8⌉` words. -/
def preR (s : State) : Region :=
  ⟨VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) oPre, Spec.Rsa.precomputedWords (s.gpr .rcx).toNat * 8⟩

theorem preWords_le {s : State} (hp : PreF s) : Spec.Rsa.precomputedWords (s.gpr .rcx).toNat ≤ 256 := by
  have := hp.k2; unfold Spec.Rsa.precomputedWords Spec.Rsa.modulusWords; omega

theorem preR_sub {s : State} (hp : PreF s) : Region.Sub (VG.Proof.Rsa.X86_64.preR s) (stkR s) :=
  frame_sub s (by have := VG.Proof.Rsa.X86_64.preWords_le hp; unfold oPre frameBytes; omega)

/-- A region of the frame at `d`, apart from the return address of a call. -/
theorem ret_disjoint (s : State) {d n : Nat} (h : d + n ≤ frameBytes) :
    (below (VG.Proof.Rsa.X86_64.fb s) 8).Disjoint ⟨VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) d, n⟩ := by
  rw [show below (VG.Proof.Rsa.X86_64.fb s) 8 = ⟨VG.Proof.Rsa.X86_64.kb s, 8⟩ by simp only [below]; rw [← VG.Proof.Rsa.X86_64.fb_sub8]; rfl, fb_eq, off_off]
  exact Offset.base_disjoint _ (by omega) (by unfold frameBytes at h; omega)

theorem pc_pre {s t : State} (hp : PreF s) (he : VG.Proof.Rsa.X86_64.Env s t) (hdi : t.gpr .rdi = VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) oPre)
    (hsi : t.gpr .rsi = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat))
    (hdx : t.gpr .rdx = s.gpr .rdx) (hcx : t.gpr .rcx = s.gpr .rcx) (h8 : t.gpr .r8 = stackArg s 12)
    (h9 : t.gpr .r9 = stackArg s 13) :
    pcContract.pre (t.callEntry.withRegions [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩] [VG.Proof.Rsa.X86_64.preR s, scrR s]) := by
  have hpw := VG.Proof.Rsa.X86_64.preWords_le hp
  have hsiN : (BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat)).toNat =
      Spec.Rsa.precomputedWords (s.gpr .rcx).toNat := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  simp only [pcContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.callEntry_rsp,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
    hdi, hsi, hdx, hcx, h8, h9, he.rsp, hsiN, VG.Proof.Rsa.X86_64.fb_sub8]
  have ⟨hK1, _⟩ := VG.Proof.Rsa.X86_64.kb_toNat hp
  have e1 : stackBytes = 3248 := rfl
  have e2 : oPre = 1184 := rfl
  have hfb : VG.Proof.Rsa.X86_64.fb s = VG.Proof.Rsa.X86_64.kb s + BitVec.ofNat 64 8 := fb_eq s
  have sP := VG.Proof.Rsa.X86_64.preR_sub hp
  have sR : Region.Sub ⟨VG.Proof.Rsa.X86_64.kb s, 8⟩ (stkR s) := Region.sub_prefix (by decide)
  have dRP : (⟨VG.Proof.Rsa.X86_64.kb s, 8⟩ : Region).Disjoint (VG.Proof.Rsa.X86_64.preR s) := by
    have := VG.Proof.Rsa.X86_64.ret_disjoint s (d := oPre) (n := Spec.Rsa.precomputedWords (s.gpr .rcx).toNat * 8)
      (by unfold oPre frameBytes; omega)
    rwa [show below (VG.Proof.Rsa.X86_64.fb s) 8 = ⟨VG.Proof.Rsa.X86_64.kb s, 8⟩ by simp only [below]; rw [← VG.Proof.Rsa.X86_64.fb_sub8]; rfl] at this
  have wP : (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) oPre).toNat + Spec.Rsa.precomputedWords (s.gpr .rcx).toNat * 8 ≤ 2 ^ 64 := by
    rw [VG.Proof.Rsa.X86_64.toNat_off (by rw [hfb, ← VG.Proof.Bignum.X86_64.off, VG.Proof.Rsa.X86_64.toNat_off (by omega)]; omega), hfb, ← VG.Proof.Bignum.X86_64.off, VG.Proof.Rsa.X86_64.toNat_off (by omega)]; omega
  exact ⟨trivial, rfl, hp.dKn.sub_left sP, hp.dKs.sub_left sP, hp.dns, dRP, hp.dKn.sub_left sR,
    hp.dKs.sub_left sR, wP, hp.wN, hp.wS, ⟨hp.k1, hp.k2⟩, trivial, hp.hsl⟩

/-- The regions `vg_rsa_public_precompute` is given: `n`, and the precomputed
values and the working space. -/
theorem pc_covers {s t : State} (hp : PreF s) (he : VG.Proof.Rsa.X86_64.Env s t) :
    Covers ([⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩] ++ [VG.Proof.Rsa.X86_64.preR s, scrR s]) (t.rd ++ t.wr) ∧
      Covers [VG.Proof.Rsa.X86_64.preR s, scrR s] t.wr := by
  have hpw := VG.Proof.Rsa.X86_64.preWords_le hp
  have hk2 := hp.k2
  have hfr : (⟨VG.Proof.Rsa.X86_64.fb s, frameBytes⟩ : Region) ∈ t.wr := by rw [he.wr]; exact List.mem_cons_self ..
  have hscr : scrR s ∈ t.wr := by rw [he.wr, hp.hwr]; simp [scrR]
  have hn : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region) ∈ t.rd := by rw [he.rd, hp.hrd]; simp
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have cw : Covers [VG.Proof.Rsa.X86_64.preR s, scrR s] t.wr := Covers.of_sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hfr, oPre, rfl, by simp only [VG.Proof.Rsa.X86_64.preR]; unfold oPre frameBytes; omega⟩
    · exact ⟨_, hscr, 0, z _, Nat.le_refl _ |>.trans (by simp)⟩
  exact ⟨Covers.append (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; exact hn) cw, cw⟩

/-- The call of `vg_rsa_public_precompute`: `n`'s values in the frame (zeros
if `n` is not valid), and whether it is returned. `M` and `r₁`'s slot are
kept. -/
theorem pc_call (M : Mont) (name : String) (hmx : (Precompute.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (hsp : NoSp (Precompute.code M.mm)) (hd : (Precompute.code M.mm).depth = 0) {s t : State} (hp : PreF s)
    (he : VG.Proof.Rsa.X86_64.Env s t) (hdi : t.gpr .rdi = VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) oPre)
    (hsi : t.gpr .rsi = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat))
    (hdx : t.gpr .rdx = s.gpr .rdx) (hcx : t.gpr .rcx = s.gpr .rcx) (h8 : t.gpr .r8 = stackArg s 12)
    (h9 : t.gpr .r9 = stackArg s 13) :
    WP isa (.call name (Precompute.code M.mm)) t fun t' => VG.Proof.Rsa.X86_64.Env s t' ∧
      (match Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) with
        | some ws => (t'.gpr .rax).setWidth 32 = 1 ∧
          Spec.Rsa.wordsAt t'.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) oPre) (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) = ws
        | none => (t'.gpr .rax).setWidth 32 = 0 ∧
          Spec.Rsa.wordsAt t'.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) oPre) (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) =
            List.replicate (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) 0) ∧
      Spec.Rsa.bytesAt t'.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) VG.Impl.Rsa.X86_64.PrivChecked.oM) (s.gpr .rcx).toNat =
        Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) VG.Impl.Rsa.X86_64.PrivChecked.oM) (s.gpr .rcx).toNat ∧
      VG.Proof.Bignum.X86_64.word t'.mem (VG.Proof.Rsa.X86_64.fb s) oR1 = VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) oR1 ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 := by
  have hpw := VG.Proof.Rsa.X86_64.preWords_le hp
  have hk2 := hp.k2
  obtain ⟨hcov, cw⟩ := VG.Proof.Rsa.X86_64.pc_covers hp he
  refine WP.call_mx (k := pcContract) (pcCode_correct M hmx) hsp (by rw [hd]; decide)
    (VG.Proof.Rsa.X86_64.pc_pre hp he hdi hsi hdx hcx h8 h9) hcov cw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ hmx
  rw [hd, he.rsp] at hf
  have hfE : Frame [stkR s, VG.Proof.Rsa.X86_64.outR s, scrR s] s.mem t.callEntry.mem :=
    VG.Proof.Rsa.X86_64.frame_call he.mem (VG.Proof.Rsa.X86_64.callEntry_frame he.rsp) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inl (VG.Proof.Rsa.X86_64.below_sub s)
  have hpwN : (BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat)).toNat =
      Spec.Rsa.precomputedWords (s.gpr .rcx).toNat := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  simp only [pcContract, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
    hdi, hsi, hdx, hcx, hpwN, hm₂, hg₂ .rax (by decide),
    VG.Proof.Rsa.X86_64.bytes_of_frame hfE hp.dKn hp.dOn hp.dns.symm (by have := hp.wN; omega)] at hpost
  have hapart : ∀ {d n : Nat}, d + n ≤ oPre → ∀ r ∈ [VG.Proof.Rsa.X86_64.preR s, scrR s] ++ [below (VG.Proof.Rsa.X86_64.fb s) 8],
      (⟨VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) d, n⟩ : Region).Disjoint r := fun {d n} hdn r hr => by
    have := (show oPre = 1184 from rfl)
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint _ (.inl hdn) (by omega) (by unfold oPre at *; omega)
    · exact hp.dKs.sub_left (frame_sub s (by unfold frameBytes; omega))
    · exact (VG.Proof.Rsa.X86_64.ret_disjoint s (by unfold frameBytes; omega)).symm
  refine ⟨⟨(hcs .rsp (by decide)).trans he.rsp, hrd.trans he.rd, hwr.trans he.wr,
    VG.Proof.Rsa.X86_64.frame_call he.mem hf fun r hr => ?_, ?_, ?_, ?_, ?_, ?_⟩, hpost, ?_, ?_, hcs, hmx⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (VG.Proof.Rsa.X86_64.preR_sub hp)
    · exact .inr (.inr (VG.Proof.Rsa.X86_64.sub_refl _))
    · exact .inl (VG.Proof.Rsa.X86_64.below_sub s)
  · rw [VG.Proof.Rsa.X86_64.slot_keep hf (hapart (by decide))]; exact he.sOut
  · rw [VG.Proof.Rsa.X86_64.slot_keep hf (hapart (by decide))]; exact he.sN
  · rw [VG.Proof.Rsa.X86_64.slot_keep hf (hapart (by decide))]; exact he.sK
  · rw [VG.Proof.Rsa.X86_64.slot_keep hf (hapart (by decide))]; exact he.sE
  · rw [VG.Proof.Rsa.X86_64.slot_keep hf (hapart (by decide))]; exact he.sEl
  · simp only [Spec.Rsa.bytesAt]
    exact List.map_congr_left fun i hi => hf.bytes (R := ⟨VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) VG.Impl.Rsa.X86_64.PrivChecked.oM, (s.gpr .rcx).toNat⟩)
      (fun r hr => hapart (by unfold VG.Impl.Rsa.X86_64.PrivChecked.oM oPre; omega) r hr) (by dsimp only; omega) (List.mem_range.mp hi)
  · exact VG.Proof.Rsa.X86_64.slot_keep hf (hapart (by decide))

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.PrivPd`. -/
section

/-!
# `vg_rsa_private_checked` on x86-64: the call of `vg_rsa_public_precomputed_checked`

`r₃` kept in its slot, and `M^e mod n` written to `out` (`pd_stage`), for
whatever `M` holds.
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.PrivChecked
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64

theorem arg_in {s t : State} (hp : PreF s) (he : VG.Proof.Rsa.X86_64.Env s t) {j : Nat} (hj : j < 14) :
    InRegions (t.rd ++ t.wr) (stackArgAddr s j) 8 :=
  ⟨⟨stackArgAddr s 0, 112⟩, List.mem_append_left _ (by
    rw [he.rd, hp.hrd]; simp only [List.mem_cons]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl trivial))))))))),
    by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)⟩

theorem word_wo0 (m : Mem) (base : Addr) (v : BitVec 64) {d' : Nat} (h : 8 ≤ d') (hd' : d' + 8 ≤ 4096) :
    (m.writeW base v).readW (VG.Proof.Bignum.X86_64.off base d') 64 = m.readW (VG.Proof.Bignum.X86_64.off base d') 64 := by
  have := word_wo m base v (d := 0) (d' := d') (.inl (by omega)) (by decide) hd'
  simpa only [Bignum.X86_64.word, VG.Proof.Bignum.X86_64.off, BitVec.add_zero] using this

theorem arg_wo0 {s : State} (m : Mem) (v : BitVec 64) {j : Nat} (hj : j < 14) :
    (m.writeW (VG.Proof.Rsa.X86_64.fb s) v).readW (stackArgAddr s j) 64 = m.readW (stackArgAddr s j) 64 := by
  have := VG.Proof.Rsa.X86_64.arg_wo (s := s) m v (d := 0) (by decide) hj
  simpa only [VG.Proof.Bignum.X86_64.off, BitVec.add_zero] using this

/-- `r₃` kept, and the arguments of `vg_rsa_public_precomputed_checked`. -/
theorem pdArgs_ok {s t : State} (hp : PreF s) (he : VG.Proof.Rsa.X86_64.Env s t) :
    WP isa (.block pdArgs) t fun t' => VG.Proof.Rsa.X86_64.Env s t' ∧
      t'.mem = (((((t.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) oR3) (t.gpr .rax)).writeW (VG.Proof.Rsa.X86_64.fb s) (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) VG.Impl.Rsa.X86_64.PrivChecked.oM)).writeW
        (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) 8) (s.gpr .rcx)).writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) 16) (stackArg s 12)).writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) 24) (stackArg s 13)) ∧
      t'.gpr .rdi = s.gpr .rdi ∧ t'.gpr .rsi = s.gpr .rcx ∧ t'.gpr .rdx = VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) oPre ∧
      t'.gpr .rcx = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) ∧
      t'.gpr .r8 = s.gpr .r8 ∧ t'.gpr .r9 = s.gpr .r9 := by
  have hs := he.scr hp
  have hk2 := hp.k2
  have h0 : InRegions t.wr (VG.Proof.Rsa.X86_64.fb s) 8 := by simpa only [VG.Proof.Bignum.X86_64.off, BitVec.add_zero] using hs.st (d := 0) (by decide)
  refine WP.mono (WP.keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] (Q := fun t' =>
      t'.mem = (((((t.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) oR3) (t.gpr .rax)).writeW (VG.Proof.Rsa.X86_64.fb s) (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) VG.Impl.Rsa.X86_64.PrivChecked.oM)).writeW
        (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) 8) (s.gpr .rcx)).writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) 16) (stackArg s 12)).writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) 24) (stackArg s 13)) ∧
      t'.gpr .rdi = s.gpr .rdi ∧ t'.gpr .rsi = s.gpr .rcx ∧ t'.gpr .rdx = VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) oPre ∧
      t'.gpr .rcx = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) ∧
      t'.gpr .r8 = s.gpr .r8 ∧ t'.gpr .r9 = s.gpr .r9) (by
    xrun [pdArgs, lea, preWords, List.cons_append, List.nil_append, ea_sp, he.rsp, VG.Impl.Rsa.X86_64.PrivChecked.arg,
      show VG.Proof.Rsa.X86_64.fb s + BitVec.ofNat 64 (frameBytes + 8 + 8 * 12) = stackArgAddr s 12 from (stackArgAddr_fb s 12).symm,
      show VG.Proof.Rsa.X86_64.fb s + BitVec.ofNat 64 (frameBytes + 8 + 8 * 13) = stackArgAddr s 13 from (stackArgAddr_fb s 13).symm,
      hs.st (d := oR3) (by decide), h0, hs.st (d := 8) (by decide),
      hs.st (d := 16) (by decide), hs.st (d := 24) (by decide), hs.ld (d := oK) (by decide),
      hs.ld (d := oOut) (by decide), hs.ld (d := VG.Impl.Rsa.X86_64.PrivChecked.oE) (by decide), hs.ld (d := oEl) (by decide),
      VG.Proof.Rsa.X86_64.arg_in hp he (show 12 < 14 by decide), VG.Proof.Rsa.X86_64.arg_in hp he (show 13 < 14 by decide),
      sx_ofNat (show oPre < 2 ^ 31 by decide), sx_ofNat (show VG.Impl.Rsa.X86_64.PrivChecked.oM < 2 ^ 31 by decide), word_wo, VG.Proof.Rsa.X86_64.arg_wo, VG.Proof.Rsa.X86_64.word_wo0, VG.Proof.Rsa.X86_64.arg_wo0,
      he.sK, he.sOut, he.sE, he.sEl, he.arg hp (show 12 < 14 by decide), he.arg hp (show 13 < 14 by decide),
      VG.Proof.Rsa.X86_64.preWords_val (show (s.gpr .rcx).toNat ≤ 1024 by omega)]) rfl)
    fun t' ⟨⟨hm, hdi, hsi, hdx, hcx, h8, h9⟩, k⟩ => ⟨⟨?_, k.2.1.trans he.rd, k.2.2.trans he.wr, ?_, ?_, ?_, ?_, ?_, ?_⟩,
      hm, hdi, hsi, hdx, hcx, h8, h9⟩
  · rw [k.gpr (by decide)]; exact he.rsp
  · have h0' : (⟨VG.Proof.Rsa.X86_64.fb s, frameBytes⟩ : Region).Contains (VG.Proof.Rsa.X86_64.fb s) 8 := by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
    have fr : ∀ {d : Nat}, d + 8 ≤ frameBytes → (⟨VG.Proof.Rsa.X86_64.fb s, frameBytes⟩ : Region).Contains (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) d) 8 :=
      fun hd => Offset.contains_base _ hd (by unfold frameBytes at hd; omega)
    rw [hm]
    refine VG.Proof.Rsa.X86_64.frame_call he.mem (rs := [⟨VG.Proof.Rsa.X86_64.fb s, frameBytes⟩]) ?_ fun r hr => ?_
    · exact ((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (fr (d := oR3) (by decide))).writeW
        (List.mem_singleton_self _) _ h0').writeW (List.mem_singleton_self _) _ (fr (d := 8) (by decide))).writeW
        (List.mem_singleton_self _) _ (fr (d := 16) (by decide))).writeW (List.mem_singleton_self _) _
        (fr (d := 24) (by decide)))
    · rw [List.mem_singleton.mp hr]
      have := frame_sub s (d := 0) (n := frameBytes) (by decide)
      exact .inl (by simpa only [VG.Proof.Bignum.X86_64.off, BitVec.add_zero] using this)
  all_goals rw [hm]; simp (disch := decide) only [Bignum.X86_64.word, word_wo, VG.Proof.Rsa.X86_64.word_wo0]
  · exact he.sOut
  · exact he.sN
  · exact he.sK
  · exact he.sE
  · exact he.sEl

/-! ## The call -/

/-- `M` in the frame, `k` bytes. -/
def mR (s : State) : Region := ⟨VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) VG.Impl.Rsa.X86_64.PrivChecked.oM, (s.gpr .rcx).toNat⟩

theorem mR_sub {s : State} (hp : PreF s) : Region.Sub (VG.Proof.Rsa.X86_64.mR s) (stkR s) :=
  frame_sub s (by have := hp.k2; unfold VG.Impl.Rsa.X86_64.PrivChecked.oM frameBytes; omega)

/-- What the call reads: `n`'s values, `e`, `M` and its stack arguments. -/
def pdRd (s : State) : List Region :=
  [VG.Proof.Rsa.X86_64.preR s, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩, VG.Proof.Rsa.X86_64.mR s, ⟨VG.Proof.Rsa.X86_64.fb s, 32⟩]

/-- What it writes: `out` and the working space. -/
def pdWr (s : State) : List Region := [⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩, scrR s]

theorem word_self0 (m : Mem) (base : Addr) (v : BitVec 64) : VG.Proof.Bignum.X86_64.word (m.writeW base v) base 0 = v := by
  have := VG.Proof.Bignum.X86_64.word_writeW_self m base 0 v
  simpa only [VG.Proof.Bignum.X86_64.off, BitVec.add_zero] using this

theorem pd_pre {s t : State} (hp : PreF s) (he : VG.Proof.Rsa.X86_64.Env s t)
    (hw0 : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) 0 = VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) VG.Impl.Rsa.X86_64.PrivChecked.oM) (hw1 : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) 8 = s.gpr .rcx)
    (hw2 : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) 16 = stackArg s 12) (hw3 : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) 24 = stackArg s 13)
    (hdi : t.gpr .rdi = s.gpr .rdi) (hsi : t.gpr .rsi = s.gpr .rcx) (hdx : t.gpr .rdx = VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) oPre)
    (hcx : t.gpr .rcx = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat))
    (h8 : t.gpr .r8 = s.gpr .r8) (h9 : t.gpr .r9 = s.gpr .r9) :
    pdContract.pre (t.callEntry.withRegions (VG.Proof.Rsa.X86_64.pdRd s) (VG.Proof.Rsa.X86_64.pdWr s)) := by
  have hpw := VG.Proof.Rsa.X86_64.preWords_le hp
  have hcxN : (BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat)).toNat =
      Spec.Rsa.precomputedWords (s.gpr .rcx).toNat := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hE : ∀ i, i < 4 → stackArg (t.callEntry.withRegions (VG.Proof.Rsa.X86_64.pdRd s) (VG.Proof.Rsa.X86_64.pdWr s)) i = VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) (8 * i) :=
    fun i hi => VG.Proof.Rsa.X86_64.stackArg_entry he.rsp _ _ (by omega)
  simp only [pdContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.callEntry_rsp,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
    hdi, hsi, hdx, hcx, h8, h9, he.rsp, hcxN, VG.Proof.Rsa.X86_64.stackArgAddr_entry he.rsp, hE 0 (by decide), hE 1 (by decide),
    hE 2 (by decide), hE 3 (by decide), Nat.reduceMul, hw0, hw1, hw2, hw3, VG.Proof.Rsa.X86_64.fb_sub8]
  have ⟨hK1, _⟩ := VG.Proof.Rsa.X86_64.kb_toNat hp
  have e1 : stackBytes = 3248 := rfl
  have e2 : oPre = 1184 := rfl
  have e3 : VG.Impl.Rsa.X86_64.PrivChecked.oM = 160 := rfl
  have hk2 := hp.k2
  have hsi' := hp.hsi
  have hfb : VG.Proof.Rsa.X86_64.fb s = VG.Proof.Rsa.X86_64.kb s + BitVec.ofNat 64 8 := fb_eq s
  have sP := VG.Proof.Rsa.X86_64.preR_sub hp
  have sM := VG.Proof.Rsa.X86_64.mR_sub hp
  have sA : Region.Sub ⟨VG.Proof.Rsa.X86_64.fb s, 32⟩ (stkR s) := by
    have := frame_sub s (d := 0) (n := 32) (by decide); simpa only [VG.Proof.Bignum.X86_64.off, BitVec.add_zero] using this
  have sR : Region.Sub ⟨VG.Proof.Rsa.X86_64.kb s, 8⟩ (stkR s) := Region.sub_prefix (by decide)
  have rb : below (VG.Proof.Rsa.X86_64.fb s) 8 = ⟨VG.Proof.Rsa.X86_64.kb s, 8⟩ := by simp only [below]; rw [← VG.Proof.Rsa.X86_64.fb_sub8]; rfl
  have dRP : (⟨VG.Proof.Rsa.X86_64.kb s, 8⟩ : Region).Disjoint (VG.Proof.Rsa.X86_64.preR s) := by
    rw [← rb]; exact VG.Proof.Rsa.X86_64.ret_disjoint s (by unfold oPre frameBytes; omega)
  have dRM : (⟨VG.Proof.Rsa.X86_64.kb s, 8⟩ : Region).Disjoint (VG.Proof.Rsa.X86_64.mR s) := by
    rw [← rb]; exact VG.Proof.Rsa.X86_64.ret_disjoint s (by unfold VG.Impl.Rsa.X86_64.PrivChecked.oM frameBytes; omega)
  have dRA : (⟨VG.Proof.Rsa.X86_64.kb s, 8⟩ : Region).Disjoint ⟨VG.Proof.Rsa.X86_64.fb s, 32⟩ := by
    rw [hfb]; exact Offset.base_disjoint _ (by decide) (by omega)
  have dOut : ∀ {r : Region}, Region.Sub r (stkR s) →
      (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region).Disjoint r := fun h => by
    rw [← hsi']; exact (hp.dKo.sub_left h).symm
  have wFr : ∀ {d n : Nat}, d + n ≤ frameBytes → (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) d).toNat + n ≤ 2 ^ 64 := fun {d n} h => by
    unfold frameBytes at h
    rw [VG.Proof.Rsa.X86_64.toNat_off (by rw [hfb, ← VG.Proof.Bignum.X86_64.off, VG.Proof.Rsa.X86_64.toNat_off (by omega)]; omega), hfb, ← VG.Proof.Bignum.X86_64.off, VG.Proof.Rsa.X86_64.toNat_off (by omega)]; omega
  refine ⟨by omega, rfl, rfl, dOut sP, ?_, dOut sM, ?_, dOut sA, hp.dKs.sub_left sP, hp.des,
    hp.dKs.sub_left sM, (hp.dKs.sub_left sA).symm, ?_, dRP, hp.dKe.sub_left sR, dRM, hp.dKs.sub_left sR, dRA,
    ?_, wFr (by unfold oPre frameBytes; omega), hp.wE, wFr (by unfold VG.Impl.Rsa.X86_64.PrivChecked.oM frameBytes; omega), hp.wS,
    ⟨hp.k1, hp.k2⟩, trivial, trivial, hp.L1, hp.L2, hp.hsl⟩
  · rw [← hsi']; exact hp.dOe
  · rw [← hsi']; exact hp.dOs
  · rw [← hsi']; exact (hp.dKo.sub_left sR)
  · rw [← hsi']; exact hp.wO

/-- Bytes of the frame at `d`, kept by a call's return address. -/
theorem entry_bytes {s t : State} (hsp : t.gpr .rsp = VG.Proof.Rsa.X86_64.fb s) {d n : Nat} (h : d + n ≤ frameBytes) :
    Spec.Rsa.bytesAt t.callEntry.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) d) n = Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) d) n := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => (VG.Proof.Rsa.X86_64.callEntry_frame hsp).bytes (R := ⟨VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) d, n⟩)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact (VG.Proof.Rsa.X86_64.ret_disjoint s h).symm)
    (by dsimp only; unfold frameBytes at h; omega) (List.mem_range.mp hi)

/-- Words of the frame at `d`, kept by a call's return address. -/
theorem entry_words {s t : State} (hsp : t.gpr .rsp = VG.Proof.Rsa.X86_64.fb s) {d n : Nat} (h : d + 8 * n ≤ frameBytes) :
    Spec.Rsa.wordsAt t.callEntry.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) d) n = Spec.Rsa.wordsAt t.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) d) n := by
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  show t.callEntry.mem.readW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) d) (8 * i)) 64 = t.mem.readW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) d) (8 * i)) 64
  rw [off_off]
  exact (VG.Proof.Rsa.X86_64.callEntry_frame hsp).readW (Region.contains_self _ _) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact (VG.Proof.Rsa.X86_64.ret_disjoint s (by unfold frameBytes at *; omega)).symm) (by decide)

/-- The regions `vg_rsa_public_precomputed_checked` is given. -/
theorem pd_covers {s t : State} (hp : PreF s) (he : VG.Proof.Rsa.X86_64.Env s t) :
    Covers (VG.Proof.Rsa.X86_64.pdRd s) (t.rd ++ t.wr) ∧ Covers (VG.Proof.Rsa.X86_64.pdWr s) t.wr := by
  have hpw := VG.Proof.Rsa.X86_64.preWords_le hp
  have hk2 := hp.k2
  have hsi' := hp.hsi
  have hfr : (⟨VG.Proof.Rsa.X86_64.fb s, frameBytes⟩ : Region) ∈ t.wr := by rw [he.wr]; exact List.mem_cons_self ..
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have cw : Covers (VG.Proof.Rsa.X86_64.pdWr s) t.wr := Covers.of_mem fun r hr => by
    simp only [VG.Proof.Rsa.X86_64.pdWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [he.wr, hp.hwr]
    rcases hr with rfl | rfl
    · rw [← hsi']; simp
    · simp [scrR]
  have cr : Covers (VG.Proof.Rsa.X86_64.pdRd s) (t.rd ++ t.wr) := Covers.of_sub fun r hr => by
    simp only [VG.Proof.Rsa.X86_64.pdRd, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_append_right _ hfr, oPre, rfl, by simp only [VG.Proof.Rsa.X86_64.preR]; unfold oPre frameBytes; omega⟩
    · exact ⟨⟨s.gpr .r8, (s.gpr .r9).toNat⟩, List.mem_append_left _ (by rw [he.rd, hp.hrd]; simp), 0, z _,
        by dsimp only; omega⟩
    · exact ⟨_, List.mem_append_right _ hfr, VG.Impl.Rsa.X86_64.PrivChecked.oM, rfl, by simp only [VG.Proof.Rsa.X86_64.mR]; unfold VG.Impl.Rsa.X86_64.PrivChecked.oM frameBytes; omega⟩
    · exact ⟨_, List.mem_append_right _ hfr, 0, z _, by dsimp only; unfold frameBytes; omega⟩
  exact ⟨cr, cw⟩

/-- The call of `vg_rsa_public_precomputed_checked`: `M^e mod n` to `out`,
for whatever modulus `n`'s values in the frame are of. `M` and the slots of
`r₁` and `r₃` are kept. -/
theorem pd_call (M : Mont) (name : String) (hmx : (Precomputed.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (hsp : NoSp (Checked.precomputedChecked M.mm)) (hd : (Checked.precomputedChecked M.mm).depth = 0)
    {s t : State} (hp : PreF s) (he : VG.Proof.Rsa.X86_64.Env s t)
    (hw0 : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) 0 = VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) VG.Impl.Rsa.X86_64.PrivChecked.oM) (hw1 : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) 8 = s.gpr .rcx)
    (hw2 : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) 16 = stackArg s 12) (hw3 : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) 24 = stackArg s 13)
    (hdi : t.gpr .rdi = s.gpr .rdi) (hsi : t.gpr .rsi = s.gpr .rcx) (hdx : t.gpr .rdx = VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) oPre)
    (hcx : t.gpr .rcx = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat))
    (h8 : t.gpr .r8 = s.gpr .r8) (h9 : t.gpr .r9 = s.gpr .r9) :
    WP isa (.call name (Checked.precomputedChecked M.mm)) t fun t' => VG.Proof.Rsa.X86_64.Env s t' ∧
      (∀ nB : List Byte, nB.length = (s.gpr .rcx).toNat →
        Spec.Rsa.publicPrecompute nB =
          some (Spec.Rsa.wordsAt t.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) oPre) (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat)) →
        Spec.Rsa.written t'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((t'.gpr .rax).setWidth 32)
          (Spec.Rsa.publicOpChecked nB (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
            (Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) VG.Impl.Rsa.X86_64.PrivChecked.oM) (s.gpr .rcx).toNat))) ∧
      Spec.Rsa.bytesAt t'.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) VG.Impl.Rsa.X86_64.PrivChecked.oM) (s.gpr .rcx).toNat =
        Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) VG.Impl.Rsa.X86_64.PrivChecked.oM) (s.gpr .rcx).toNat ∧
      VG.Proof.Bignum.X86_64.word t'.mem (VG.Proof.Rsa.X86_64.fb s) oR1 = VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) oR1 ∧ VG.Proof.Bignum.X86_64.word t'.mem (VG.Proof.Rsa.X86_64.fb s) oR3 = VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) oR3 ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 := by
  have hpw := VG.Proof.Rsa.X86_64.preWords_le hp
  have hk2 := hp.k2
  have hsi' := hp.hsi
  obtain ⟨cr, cw⟩ := VG.Proof.Rsa.X86_64.pd_covers hp he
  have hv := Proof.Rsa.X86_64.precomputedChecked_correct M hmx
  have hpre := VG.Proof.Rsa.X86_64.pd_pre hp he hw0 hw1 hw2 hw3 hdi hsi hdx hcx h8 h9
  have hdd : 8 * (Checked.precomputedChecked M.mm).depth + 16 < 2 ^ 64 := by rw [hd]; decide
  have hpre' : (⟨pdContract.pre, pdChkContract.post, pdContract.pub⟩ : Contract isa).pre
      (t.callEntry.withRegions (VG.Proof.Rsa.X86_64.pdRd s) (VG.Proof.Rsa.X86_64.pdWr s)) := hpre
  have hcov := Covers.append_left cr cw.right
  refine WP.call_mx (k := ⟨pdContract.pre, pdChkContract.post, pdContract.pub⟩) (rd := VG.Proof.Rsa.X86_64.pdRd s) (wr := VG.Proof.Rsa.X86_64.pdWr s)
    hv hsp hdd
    hpre' hcov cw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ hmx
  rw [hd, he.rsp] at hf
  have hfE : Frame [stkR s, VG.Proof.Rsa.X86_64.outR s, scrR s] s.mem t.callEntry.mem :=
    VG.Proof.Rsa.X86_64.frame_call he.mem (VG.Proof.Rsa.X86_64.callEntry_frame he.rsp) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inl (VG.Proof.Rsa.X86_64.below_sub s)
  have hcxN : (BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat)).toNat =
      Spec.Rsa.precomputedWords (s.gpr .rcx).toNat := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  simp only [pdChkContract, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
    hdi, hsi, hdx, hcx, h8, h9, hcxN, hm₂, hg₂ .rax (by decide), VG.Proof.Rsa.X86_64.stackArg_entry he.rsp _ _ (show 0 < 400 by decide),
    Nat.mul_zero, hw0, VG.Proof.Rsa.X86_64.entry_bytes he.rsp (show VG.Impl.Rsa.X86_64.PrivChecked.oM + (s.gpr .rcx).toNat ≤ frameBytes by unfold VG.Impl.Rsa.X86_64.PrivChecked.oM frameBytes; omega),
    VG.Proof.Rsa.X86_64.entry_words he.rsp (show oPre + 8 * Spec.Rsa.precomputedWords (s.gpr .rcx).toNat ≤ frameBytes by
      unfold oPre frameBytes; omega),
    VG.Proof.Rsa.X86_64.bytes_of_frame hfE hp.dKe hp.dOe (hp.des.symm) (by have := hp.wE; omega)] at hpost
  have hapart : ∀ {d n : Nat}, d + n ≤ frameBytes → 32 ≤ d → ∀ r ∈ VG.Proof.Rsa.X86_64.pdWr s ++ [below (VG.Proof.Rsa.X86_64.fb s) 8],
      (⟨VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) d, n⟩ : Region).Disjoint r := fun {d n} hdn h32 r hr => by
    simp only [VG.Proof.Rsa.X86_64.pdWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [← hsi']; exact (hp.dKo.sub_left (frame_sub s hdn))
    · exact hp.dKs.sub_left (frame_sub s hdn)
    · exact (VG.Proof.Rsa.X86_64.ret_disjoint s hdn).symm
  refine ⟨⟨(hcs .rsp (by decide)).trans he.rsp, hrd.trans he.rd, hwr.trans he.wr,
    VG.Proof.Rsa.X86_64.frame_call he.mem hf fun r hr => ?_, ?_, ?_, ?_, ?_, ?_⟩, hpost, ?_, ?_, ?_, hcs, hmx⟩
  · simp only [VG.Proof.Rsa.X86_64.pdWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr (.inl (by rw [← hsi']; exact VG.Proof.Rsa.X86_64.sub_refl _))
    · exact .inr (.inr (VG.Proof.Rsa.X86_64.sub_refl _))
    · exact .inl (VG.Proof.Rsa.X86_64.below_sub s)
  · rw [VG.Proof.Rsa.X86_64.slot_keep hf (hapart (by decide) (by decide))]; exact he.sOut
  · rw [VG.Proof.Rsa.X86_64.slot_keep hf (hapart (by decide) (by decide))]; exact he.sN
  · rw [VG.Proof.Rsa.X86_64.slot_keep hf (hapart (by decide) (by decide))]; exact he.sK
  · rw [VG.Proof.Rsa.X86_64.slot_keep hf (hapart (by decide) (by decide))]; exact he.sE
  · rw [VG.Proof.Rsa.X86_64.slot_keep hf (hapart (by decide) (by decide))]; exact he.sEl
  · simp only [Spec.Rsa.bytesAt]
    exact List.map_congr_left fun i hi => hf.bytes (R := ⟨VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) VG.Impl.Rsa.X86_64.PrivChecked.oM, (s.gpr .rcx).toNat⟩)
      (fun r hr => hapart (by unfold VG.Impl.Rsa.X86_64.PrivChecked.oM frameBytes; omega) (by decide) r hr) (by dsimp only; omega)
      (List.mem_range.mp hi)
  · exact VG.Proof.Rsa.X86_64.slot_keep hf (hapart (by decide) (by decide))
  · exact VG.Proof.Rsa.X86_64.slot_keep hf (hapart (by decide) (by decide))

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.PrivTail`. -/
section

/-!
# `vg_rsa_private_checked` on x86-64: the check and the release

After the calls, `out` (which `vg_rsa_public_precomputed_checked` wrote) is
compared with the input without branches (`cmpLoop_ok`), and `M` is
released to `out` under the mask of `r₁ = r₂ = r₃ = 1` and their equality,
and zeroed (`releaseLoop_ok`), whatever `M` and `out` hold (`tail_ok`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.PrivChecked
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.WriteBytes (writeW8_apply)

theorem ea_at10 (t : State) {b : Reg} {p : Addr} {j : Nat} (hb : t.gpr b = p)
    (hi : t.gpr .r10 = BitVec.ofNat 64 j) : t.ea (at10 b) = p + BitVec.ofNat 64 j := by
  simp only [State.ea, at10, hb, hi, BitVec.mul_one, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]

theorem ea_mByte (t : State) {S : Addr} {j : Nat} (hb : t.gpr .rsp = S) (hi : t.gpr .r10 = BitVec.ofNat 64 j) :
    t.ea mByte = VG.Proof.Bignum.X86_64.off S VG.Impl.Rsa.X86_64.PrivChecked.oM + BitVec.ofNat 64 j := by
  simp only [State.ea, mByte, hb, hi, BitVec.mul_one, BitVec.ofInt_natCast, VG.Proof.Bignum.X86_64.off]
  rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 j)]

/-- `r₂ & r₁ & r₃ & 1`. -/
def gOf (r₂ r₁ r₃ : BitVec 64) : BitVec 64 := r₂ &&& r₁ &&& r₃ &&& 1

theorem gOf_cases (r₂ r₁ r₃ : BitVec 64) : VG.Proof.Rsa.X86_64.gOf r₂ r₁ r₃ = 0 ∨ VG.Proof.Rsa.X86_64.gOf r₂ r₁ r₃ = 1 := by
  unfold VG.Proof.Rsa.X86_64.gOf
  generalize r₂ &&& r₁ &&& r₃ = x
  have h : (x &&& 1).toNat = x.toNat % 2 := by
    rw [BitVec.toNat_and, show (1 : BitVec 64).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h0 | h1
  · exact .inl (BitVec.eq_of_toNat_eq (by rw [h, h0]; rfl))
  · exact .inr (BitVec.eq_of_toNat_eq (by rw [h, h1]; rfl))

/-- The comparison's registers. -/
theorem cmpArgs_ok {s t : State} (hp : PreF s) (he : VG.Proof.Rsa.X86_64.Env s t) :
    WP isa (.block cmpArgs) t fun t' => t'.mem = t.mem ∧
      t'.gpr .r11 = VG.Proof.Rsa.X86_64.gOf (t.gpr .rax) (VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) oR1) (VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) oR3) ∧
      t'.gpr .rdi = s.gpr .rdi ∧ t'.gpr .rsi = stackArg s 0 ∧ t'.gpr .rcx = s.gpr .rcx ∧
      t'.gpr .r10 = BitVec.ofNat 64 0 ∧ t'.gpr .rdx = 0 ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .r11, .rdi, .rsi, .rcx, .r10, .rdx] t t' := by
  have hs := he.scr hp
  refine WP.mono (WP.keep [.rax, .r11, .rdi, .rsi, .rcx, .r10, .rdx] (c := .block cmpArgs) (Q := fun t' =>
      t'.mem = t.mem ∧ t'.gpr .r11 = VG.Proof.Rsa.X86_64.gOf (t.gpr .rax) (VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) oR1) (VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) oR3) ∧
      t'.gpr .rdi = s.gpr .rdi ∧ t'.gpr .rsi = stackArg s 0 ∧ t'.gpr .rcx = s.gpr .rcx ∧
      t'.gpr .r10 = BitVec.ofNat 64 0 ∧ t'.gpr .rdx = 0) (by
    xrun [cmpArgs, VG.Proof.Rsa.X86_64.gOf, ea_sp, he.rsp, VG.Impl.Rsa.X86_64.PrivChecked.arg, hs.ld (d := oR1) (by decide), hs.ld (d := oR3) (by decide),
      hs.ld (d := oOut) (by decide), hs.ld (d := oK) (by decide), VG.Proof.Rsa.X86_64.arg_in hp he (show 0 < 14 by decide),
      show VG.Proof.Rsa.X86_64.fb s + BitVec.ofNat 64 (frameBytes + 8 + 8 * 0) = stackArgAddr s 0 from (stackArgAddr_fb s 0).symm,
      he.sOut, he.sK, he.arg hp (show 0 < 14 by decide)]) rfl) fun t' ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, k⟩ => ⟨h1, h2, h3, h4, h5, h6, h7, k⟩

theorem zext_xor_eq_zero (a b : Byte) : (BitVec.setWidth 64 a ^^^ BitVec.setWidth 64 b = 0) ↔ a = b := by
  rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.xor_eq_zero_iff]
  constructor
  · intro h
    have := congrArg (BitVec.setWidth 8) h
    simpa using this
  · rintro rfl; rfl

/-- After `j` bytes of the comparison. -/
structure CmpInv (t₀ : State) (op ip : Addr) (j : Nat) (t : State) : Prop where
  keep : VG.Proof.MlKem.X86_64.Keep [.rax, .r9, .r10, .rdx] t₀ t
  mem : t.mem = t₀.mem
  r10 : t.gpr .r10 = BitVec.ofNat 64 j
  rdx : t.gpr .rdx = 0 ↔ ∀ i < j, t₀.mem (op + BitVec.ofNat 64 i) = t₀.mem (ip + BitVec.ofNat 64 i)

/-- The comparison of the `k` bytes at `op` and `ip`: `rdx` is zero exactly
when they are equal. -/
theorem cmpLoop_ok {t : State} {op ip : Addr} {k : Nat} (hk1 : 1 ≤ k) (hk : k < 2 ^ 63)
    (hdi : t.gpr .rdi = op) (hsi : t.gpr .rsi = ip) (hcx : t.gpr .rcx = BitVec.ofNat 64 k)
    (h10 : t.gpr .r10 = BitVec.ofNat 64 0) (hdx : t.gpr .rdx = 0)
    (ho : ∀ i < k, InRegions (t.rd ++ t.wr) (op + BitVec.ofNat 64 i) 1)
    (hi : ∀ i < k, InRegions (t.rd ++ t.wr) (ip + BitVec.ofNat 64 i) 1) :
    WP isa cmpLoop t fun t' => VG.Proof.Rsa.X86_64.CmpInv t op ip k t' := by
  refine wp_upto (a := 0) (N := k) (by omega) (VG.Proof.Rsa.X86_64.CmpInv t op ip) ?_ (fun _ h => h)
    ⟨Keep.refl _ _, rfl, h10, ⟨fun _ _ h => absurd h (by omega), fun _ => hdx⟩⟩
  intro j _ hj u hI
  have hdi' : u.gpr .rdi = op := (hI.keep.gpr (by decide)).trans hdi
  have hsi' : u.gpr .rsi = ip := (hI.keep.gpr (by decide)).trans hsi
  have hcx' : u.gpr .rcx = BitVec.ofNat 64 k := (hI.keep.gpr (by decide)).trans hcx
  have hoj : InRegions (u.rd ++ u.wr) (op + BitVec.ofNat 64 j) 1 := by
    rw [hI.keep.2.1, hI.keep.2.2]; exact ho j hj
  have hij : InRegions (u.rd ++ u.wr) (ip + BitVec.ofNat 64 j) 1 := by
    rw [hI.keep.2.1, hI.keep.2.2]; exact hi j hj
  refine WP.mono (WP.keep [.rax, .r9, .r10, .rdx] (Q := fun u' => u'.mem = u.mem ∧
      u'.gpr .r10 = BitVec.ofNat 64 (j + 1) ∧ u'.zf = some (decide (j + 1 = k)) ∧
      u'.gpr .rdx = u.gpr .rdx ||| (BitVec.setWidth 64 (u.mem (op + BitVec.ofNat 64 j)) ^^^
        BitVec.setWidth 64 (u.mem (ip + BitVec.ofNat 64 j)))) (by
    xrun [cmpLoop, State.ea, at10, hdi', hsi', BitVec.mul_one, show BitVec.ofInt 64 0 = 0#64 from rfl,
      BitVec.add_zero, hoj, hij, hI.r10, hcx', ofNat_add_one,
      ofNat_sub_beq (show j + 1 < 2 ^ 64 by omega) (show k < 2 ^ 64 by omega)]) rfl) fun u' ⟨⟨hm, h10', hz, hdx'⟩, k'⟩ => ⟨hz, (hI.keep.trans k').mono (by decide), hm.trans hI.mem, h10', ?_⟩
  rw [hdx', show (0 : BitVec 64) = 0#64 from rfl, BitVec.or_eq_zero_iff, ← show (0 : BitVec 64) = 0#64 from rfl,
    VG.Proof.Rsa.X86_64.zext_xor_eq_zero, hI.rdx, hI.mem]
  constructor
  · rintro ⟨h1, h2⟩ i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact h1 i hi
    · exact h2
  · intro h
    exact ⟨fun i hi => h i (by omega), h j (by omega)⟩

/-- The release mask and the result. -/
def relMask (g : BitVec 64) (eq : Bool) : BitVec 64 := if g = 1 ∧ eq = true then BitVec.allOnes 64 else 0
def result (g : BitVec 64) (eq : Bool) : BitVec 64 := if g = 1 then (if eq then 1 else 2) else 0

theorem masks_ok {t : State} {g : BitVec 64} {eq : Bool} (h11 : t.gpr .r11 = g) (hg : g = 0 ∨ g = 1)
    (hdx : t.gpr .rdx = 0 ↔ eq = true) :
    WP isa (.block masks) t fun t' => t'.mem = t.mem ∧ t'.gpr .r9 = VG.Proof.Rsa.X86_64.relMask g eq ∧ t'.gpr .r11 = VG.Proof.Rsa.X86_64.result g eq ∧
      t'.gpr .r10 = BitVec.ofNat 64 0 ∧ VG.Proof.MlKem.X86_64.Keep [.rdx, .r9, .rax, .r8, .r11, .r10] t t' := by
  have hcf : decide ((t.gpr .rdx).toNat < BitVec.toNat (1 : BitVec 64)) = eq := by
    rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]
    cases eq
    · have : t.gpr .rdx ≠ 0 := fun h => by simpa using hdx.mp h
      simp only [decide_eq_false_iff_not, Nat.lt_one_iff]
      intro h; exact this (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
    · simp only [decide_eq_true_eq, Nat.lt_one_iff, hdx.mpr rfl]; rfl
  refine WP.mono (WP.keep [.rdx, .r9, .rax, .r8, .r11, .r10] (Q := fun t' => t'.mem = t.mem ∧
      t'.gpr .r9 = VG.Proof.Rsa.X86_64.relMask g eq ∧ t'.gpr .r11 = VG.Proof.Rsa.X86_64.result g eq ∧ t'.gpr .r10 = BitVec.ofNat 64 0) (by
    xrun [masks, h11, hcf]
    rcases hg with rfl | rfl <;> cases eq <;> decide) rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, k⟩

theorem low_and_mask (b : Byte) (g : BitVec 64) (eq : Bool) :
    (BitVec.setWidth 64 b &&& VG.Proof.Rsa.X86_64.relMask g eq).setWidth 8 = if g = 1 ∧ eq = true then b else 0 := by
  unfold VG.Proof.Rsa.X86_64.relMask
  split
  · rw [BitVec.and_allOnes]; simp
  · rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.and_zero]; rfl

/-- After `j` bytes of the release. -/
structure RelInv (t₀ : State) (op Mb : Addr) (g : BitVec 64) (eq : Bool) (j : Nat) (t : State) : Prop where
  keep : VG.Proof.MlKem.X86_64.Keep [.rax, .r10] t₀ t
  r10 : t.gpr .r10 = BitVec.ofNat 64 j
  out : ∀ i < j, t.mem (op + BitVec.ofNat 64 i) = if g = 1 ∧ eq = true then t₀.mem (Mb + BitVec.ofNat 64 i) else 0
  m : ∀ i < j, t.mem (Mb + BitVec.ofNat 64 i) = 0
  frame : ∀ x, (∀ i < j, x ≠ op + BitVec.ofNat 64 i) → (∀ i < j, x ≠ Mb + BitVec.ofNat 64 i) → t.mem x = t₀.mem x

/-- The release: `out := M & mask`, `M := 0`, byte by byte. -/
theorem releaseLoop_ok {t : State} {S op : Addr} {k : Nat} {g : BitVec 64} {eq : Bool} (hk1 : 1 ≤ k)
    (hk : k < 2 ^ 63) (hsp : t.gpr .rsp = S) (hdi : t.gpr .rdi = op) (h9 : t.gpr .r9 = VG.Proof.Rsa.X86_64.relMask g eq)
    (hcx : t.gpr .rcx = BitVec.ofNat 64 k) (h10 : t.gpr .r10 = BitVec.ofNat 64 0)
    (hwo : ∀ i < k, InRegions t.wr (op + BitVec.ofNat 64 i) 1)
    (hwm : ∀ i < k, InRegions t.wr (VG.Proof.Bignum.X86_64.off S VG.Impl.Rsa.X86_64.PrivChecked.oM + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < k, ∀ i' < k, op + BitVec.ofNat 64 i ≠ VG.Proof.Bignum.X86_64.off S VG.Impl.Rsa.X86_64.PrivChecked.oM + BitVec.ofNat 64 i') :
    WP isa releaseLoop t fun t' => VG.Proof.Rsa.X86_64.RelInv t op (VG.Proof.Bignum.X86_64.off S VG.Impl.Rsa.X86_64.PrivChecked.oM) g eq k t' := by
  refine wp_upto (a := 0) (N := k) (by omega) (VG.Proof.Rsa.X86_64.RelInv t op (VG.Proof.Bignum.X86_64.off S VG.Impl.Rsa.X86_64.PrivChecked.oM) g eq) ?_ (fun _ h => h)
    ⟨Keep.refl _ _, h10, fun _ h => absurd h (by omega), fun _ h => absurd h (by omega), fun _ _ _ => rfl⟩
  intro j _ hj u hI
  have hsp' : u.gpr .rsp = S := (hI.keep.gpr (by decide)).trans hsp
  have hdi' : u.gpr .rdi = op := (hI.keep.gpr (by decide)).trans hdi
  have h9' : u.gpr .r9 = VG.Proof.Rsa.X86_64.relMask g eq := (hI.keep.gpr (by decide)).trans h9
  have hcx' : u.gpr .rcx = BitVec.ofNat 64 k := (hI.keep.gpr (by decide)).trans hcx
  have hoj : InRegions u.wr (op + BitVec.ofNat 64 j) 1 := by rw [hI.keep.2.2]; exact hwo j hj
  have hmj : InRegions u.wr (VG.Proof.Bignum.X86_64.off S VG.Impl.Rsa.X86_64.PrivChecked.oM + BitVec.ofNat 64 j) 1 := by rw [hI.keep.2.2]; exact hwm j hj
  have hmj' : InRegions (u.rd ++ u.wr) (VG.Proof.Bignum.X86_64.off S VG.Impl.Rsa.X86_64.PrivChecked.oM + BitVec.ofNat 64 j) 1 :=
    let ⟨r, hr, hc⟩ := hmj; ⟨r, List.mem_append_right _ hr, hc⟩
  have hb : u.mem (VG.Proof.Bignum.X86_64.off S VG.Impl.Rsa.X86_64.PrivChecked.oM + BitVec.ofNat 64 j) = t.mem (VG.Proof.Bignum.X86_64.off S VG.Impl.Rsa.X86_64.PrivChecked.oM + BitVec.ofNat 64 j) :=
    hI.frame _ (fun i hi h => hsep i (by omega) j hj h.symm) fun i hi h => out_ne (by omega) (by omega)
      (show j ≠ i by omega) h
  refine WP.mono (WP.keep [.rax, .r10] (Q := fun u' =>
      u'.mem = (u.mem.writeW (op + BitVec.ofNat 64 j)
        (if g = 1 ∧ eq = true then t.mem (VG.Proof.Bignum.X86_64.off S VG.Impl.Rsa.X86_64.PrivChecked.oM + BitVec.ofNat 64 j) else 0)).writeW
          (VG.Proof.Bignum.X86_64.off S VG.Impl.Rsa.X86_64.PrivChecked.oM + BitVec.ofNat 64 j) (0 : Byte) ∧
      u'.gpr .r10 = BitVec.ofNat 64 (j + 1) ∧ u'.zf = some (decide (j + 1 = k))) (by
    xrun [releaseLoop, State.ea, at10, mByte, hsp', hdi', hI.r10, h9', hcx', BitVec.mul_one,
      show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, BitVec.ofInt_natCast,
      show S + BitVec.ofNat 64 j + BitVec.ofNat 64 VG.Impl.Rsa.X86_64.PrivChecked.oM = VG.Proof.Bignum.X86_64.off S VG.Impl.Rsa.X86_64.PrivChecked.oM + BitVec.ofNat 64 j by
        rw [VG.Proof.Bignum.X86_64.off, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 j)],
      hoj, hmj, hmj', hb, VG.Proof.Rsa.X86_64.low_and_mask, ofNat_add_one,
      ofNat_sub_beq (show j + 1 < 2 ^ 64 by omega) (show k < 2 ^ 64 by omega)]
    rfl) rfl) fun u' ⟨⟨hm, h10', hz⟩, k'⟩ => ⟨hz, (hI.keep.trans k').mono (by decide), h10', ?_, ?_, ?_⟩
  · intro i hi
    rw [hm, VG.WriteBytes.writeW8_apply, VG.WriteBytes.writeW8_apply]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (hsep i (by omega) j hj)),
        ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega) (by omega) (show i ≠ j by omega)))]
      exact hI.out i hi
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (hsep i (by omega) i (by omega)))]; simp only [↓reduceIte]
  · intro i hi
    rw [hm, VG.WriteBytes.writeW8_apply]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega) (by omega) (show i ≠ j by omega))),
        VG.WriteBytes.writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false fun h => hsep j hj i (by omega) h.symm)]
      exact hI.m i hi
    · simp only [↓reduceIte]
  · intro x hx hx'
    rw [hm, VG.WriteBytes.writeW8_apply, VG.WriteBytes.writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx' j (by omega))),
      ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega)))]
    exact hI.frame x (fun i hi => hx i (by omega)) fun i hi => hx' i (by omega)

theorem bytesAt_eq_iff (m : Mem) (a b : Addr) (k : Nat) :
    Spec.Rsa.bytesAt m a k = Spec.Rsa.bytesAt m b k ↔
      ∀ i < k, m (a + BitVec.ofNat 64 i) = m (b + BitVec.ofNat 64 i) := by
  simp only [Spec.Rsa.bytesAt]
  constructor
  · intro h i hi
    have := congrArg (fun l => l[i]?) h
    simpa [hi] using this
  · intro h
    exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

theorem contains_of_byte {r : Region} {p : Addr} {n : Nat} (h : r = ⟨p, n⟩) (hn : n ≤ 2 ^ 64) {i : Nat}
    (hi : i < n) : r.Contains (p + BitVec.ofNat 64 i) 1 := by
  subst h; exact Offset.contains_base _ (by omega) (by omega)

/-- The check and the release, after the calls, from `t`: whatever `M`,
`out` and the values returned hold. -/
theorem tail_ok {s t : State} (hp : PreF s) (he : VG.Proof.Rsa.X86_64.Env s t) :
    WP isa (seqs PrivChecked.tail) t fun t' =>
      t'.gpr .rax = VG.Proof.Rsa.X86_64.result (VG.Proof.Rsa.X86_64.gOf (t.gpr .rax) (VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) oR1) (VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) oR3))
        (decide (Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rcx).toNat =
          Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat)) ∧
      Spec.Rsa.bytesAt t'.mem (s.gpr .rdi) (s.gpr .rcx).toNat =
        (if VG.Proof.Rsa.X86_64.gOf (t.gpr .rax) (VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) oR1) (VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) oR3) = 1 ∧
            Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rcx).toNat =
              Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat
          then Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) VG.Impl.Rsa.X86_64.PrivChecked.oM) (s.gpr .rcx).toNat
          else List.replicate (s.gpr .rcx).toNat 0) ∧
      Spec.Rsa.bytesAt t'.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) VG.Impl.Rsa.X86_64.PrivChecked.oM) (s.gpr .rcx).toNat = List.replicate (s.gpr .rcx).toNat 0 ∧
      VG.Proof.Rsa.X86_64.Env s t' := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hsi := hp.hsi
  have hil := hp.hil
  -- The input, unchanged.
  have hin : Spec.Rsa.bytesAt t.mem (stackArg s 0) (s.gpr .rcx).toNat =
      Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat :=
    VG.Proof.Rsa.X86_64.bytes_of_frame he.mem (by rw [← hil]; exact hp.dKi) (by rw [← hil]; exact hp.dOi) (by rw [← hil]; exact hp.dis.symm)
      (by omega)
  have hout : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region) ∈ t.wr := by
    rw [he.wr, hp.hwr, ← hsi]; simp
  have hinp : (⟨stackArg s 0, (s.gpr .rcx).toNat⟩ : Region) ∈ t.rd := by
    rw [he.rd, hp.hrd, ← hil]; simp
  have hfr : (⟨VG.Proof.Rsa.X86_64.fb s, frameBytes⟩ : Region) ∈ t.wr := by rw [he.wr]; exact List.mem_cons_self ..
  have wO : (s.gpr .rcx).toNat ≤ 2 ^ 64 := by omega
  unfold PrivChecked.tail
  simp only [seqs]
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.cmpArgs_ok hp he) fun t₁ ⟨hm₁, h11, hdi, hsi₁, hcx, h10, hdx, k₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.cmpLoop_ok (k := (s.gpr .rcx).toNat) (op := s.gpr .rdi) (ip := stackArg s 0) (by omega)
    (by omega) hdi hsi₁ (by rw [hcx]; exact (VG.Proof.Rsa.X86_64.ofNat_toNat _).symm) h10 hdx
    (fun i hi => ⟨_, List.mem_append_right _ (by rw [k₁.2.2]; exact hout), VG.Proof.Rsa.X86_64.contains_of_byte rfl wO hi⟩)
    (fun i hi => ⟨_, List.mem_append_left _ (by rw [k₁.2.1]; exact hinp), VG.Proof.Rsa.X86_64.contains_of_byte rfl wO hi⟩))
    fun t₂ hI => ?_)
  have k12 := k₁.trans hI.keep
  have hrdx : t₂.gpr .rdx = 0 ↔ decide (Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rcx).toNat =
      Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat) = true := by
    rw [hI.rdx, decide_eq_true_iff, ← hin, VG.Proof.Rsa.X86_64.bytesAt_eq_iff, hm₁]
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.masks_ok (h11 ▸ (hI.keep.gpr (by decide))) (VG.Proof.Rsa.X86_64.gOf_cases _ _ _) hrdx)
    fun t₃ ⟨hm₃, h9, h11', h10', k₃⟩ => ?_)
  have k13 := k12.trans k₃
  have hsep : ∀ i < (s.gpr .rcx).toNat, ∀ i' < (s.gpr .rcx).toNat,
      s.gpr .rdi + BitVec.ofNat 64 i ≠ VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) VG.Impl.Rsa.X86_64.PrivChecked.oM + BitVec.ofNat 64 i' := fun i hi i' hi' h => by
    have hc := VG.Proof.Rsa.X86_64.contains_of_byte (r := VG.Proof.Rsa.X86_64.mR s) rfl wO hi'
    rw [← h] at hc
    exact (hp.dKo.sub_left (VG.Proof.Rsa.X86_64.mR_sub hp)) _ hc
      (VG.Proof.Rsa.X86_64.contains_of_byte (r := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩) rfl (by omega) (show i < (s.gpr .rsi).toNat by omega))
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.releaseLoop_ok (k := (s.gpr .rcx).toNat) (S := VG.Proof.Rsa.X86_64.fb s) (by omega) (by omega)
    ((k13.gpr (by decide)).trans he.rsp) (((hI.keep.trans k₃).gpr (by decide)).trans hdi) h9 ?_ h10'
    (fun i hi => ⟨_, by rw [k13.2.2]; exact hout, VG.Proof.Rsa.X86_64.contains_of_byte rfl wO hi⟩)
    (fun i hi => ⟨_, by rw [k13.2.2]; exact hfr, by
      rw [VG.Proof.Bignum.X86_64.off, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact Offset.contains_base _ (by unfold VG.Impl.Rsa.X86_64.PrivChecked.oM frameBytes; omega) (by unfold VG.Impl.Rsa.X86_64.PrivChecked.oM; omega)⟩)
    hsep) fun t₄ hR => ?_)
  · rw [((hI.keep.trans k₃).gpr (by decide)).trans hcx]; exact (VG.Proof.Rsa.X86_64.ofNat_toNat _).symm
  have hm₃ : t₃.mem = t.mem := hm₃.trans (hI.mem.trans hm₁)
  have k14 := k13.trans hR.keep
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.gpr .rax = t₄.gpr .r11 ∧ t'.mem = t₄.mem) (by xrun) rfl)
    fun t' ⟨⟨hax, hm⟩, k'⟩ => ?_
  have k15 := k14.trans k'
  have hfr4 : Frame [VG.Proof.Rsa.X86_64.outR s, VG.Proof.Rsa.X86_64.mR s] t.mem t'.mem := fun x hx => by
    rw [hm, hR.frame x (fun i hi h => hx _ (List.mem_cons_self ..) (by
        rw [h]; exact VG.Proof.Rsa.X86_64.contains_of_byte (r := VG.Proof.Rsa.X86_64.outR s) rfl (by omega) (show i < (s.gpr .rsi).toNat by omega)))
      (fun i hi h => hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (by
        rw [h]; exact VG.Proof.Rsa.X86_64.contains_of_byte rfl wO hi)), hm₃]
  have hslot : ∀ {d : Nat}, 96 ≤ d → d + 8 ≤ VG.Impl.Rsa.X86_64.PrivChecked.oM → VG.Proof.Bignum.X86_64.word t'.mem (VG.Proof.Rsa.X86_64.fb s) d = VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) d := fun hd hd' =>
    VG.Proof.Rsa.X86_64.slot_keep hfr4 fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.dKo.sub_left (frame_sub s (by unfold VG.Impl.Rsa.X86_64.PrivChecked.oM frameBytes at *; omega))
      · exact Offset.disjoint _ (.inl hd') (by unfold VG.Impl.Rsa.X86_64.PrivChecked.oM at hd'; omega) (by unfold VG.Impl.Rsa.X86_64.PrivChecked.oM; omega)
  refine ⟨hax.trans ((hR.keep.gpr (by decide)).trans h11'), ?_, ?_, ⟨(k15.gpr (by decide)).trans he.rsp,
    k15.2.1.trans he.rd, k15.2.2.trans he.wr, VG.Proof.Rsa.X86_64.frame_call he.mem hfr4 fun r hr => ?_,
    (hslot (by decide) (by decide)).trans he.sOut, (hslot (by decide) (by decide)).trans he.sN,
    (hslot (by decide) (by decide)).trans he.sK, (hslot (by decide) (by decide)).trans he.sE,
    (hslot (by decide) (by decide)).trans he.sEl⟩⟩
  · by_cases hc : VG.Proof.Rsa.X86_64.gOf (t.gpr .rax) (VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) oR1) (VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) oR3) = 1 ∧
        Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rcx).toNat =
          Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat
    · have hc' : VG.Proof.Rsa.X86_64.gOf (t.gpr .rax) (VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) oR1) (VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) oR3) = 1 ∧
          decide (Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rcx).toNat =
            Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat) = true := ⟨hc.1, decide_eq_true hc.2⟩
      simp only [hc, and_self, ↓reduceIte]
      simp only [Spec.Rsa.bytesAt, hm]
      exact List.map_congr_left fun i hi => by
        rw [hR.out i (List.mem_range.mp hi), hm₃]; simp only [hc', and_self, ↓reduceIte]
    · have hc' : ¬ (VG.Proof.Rsa.X86_64.gOf (t.gpr .rax) (VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) oR1) (VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) oR3) = 1 ∧
          decide (Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rcx).toNat =
            Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat) = true) :=
        fun h => hc ⟨h.1, of_decide_eq_true h.2⟩
      simp only [hc, ↓reduceIte]
      simp only [Spec.Rsa.bytesAt, hm]
      refine List.ext_getElem (by simp) fun i h₁ _ => ?_
      simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
      rw [hR.out i (by simpa using h₁)]; simp only [hc', ↓reduceIte]
  · simp only [Spec.Rsa.bytesAt, hm]
    refine List.ext_getElem (by simp) fun i h₁ _ => ?_
    simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
    exact hR.m i (by simpa using h₁)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr (.inl (VG.Proof.Rsa.X86_64.sub_refl _))
    · exact .inl (VG.Proof.Rsa.X86_64.mR_sub hp)

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.PrivCheck`. -/
section

/-!
# `vg_rsa_private_checked` on x86-64: what follows the CRT

`check_ok` runs everything after the call of the CRT, from any state the
frame allows: whatever `M` holds and whatever the CRT returned (`r₁`), it
releases `M` to `out` (and returns 1) only if `r₁` is odd, `n` is a valid
modulus and the public operation of `M` with `e`, within BoringSSL's
limits, is the input; otherwise `out` is zeros. This is the fault tolerance
of the check: a faulted exponentiation releases nothing that fails it.
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.PrivChecked
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64

theorem bytes_wo (m : Mem) (base : Addr) {d a n : Nat} (v : BitVec 64) (h : d + 8 ≤ a ∨ a + n ≤ d)
    (ha : a + n ≤ 4096) (hd : d + 8 ≤ 4096) :
    Spec.Rsa.bytesAt (m.writeW (VG.Proof.Bignum.X86_64.off base d) v) (VG.Proof.Bignum.X86_64.off base a) n = Spec.Rsa.bytesAt m (VG.Proof.Bignum.X86_64.off base a) n := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  exact VG.Proof.Bignum.X86_64.writeW_outside m base v (by omega) _ (by rw [VG.Proof.Bignum.X86_64.ofs_off base (by omega)]; omega)

theorem words_wo (m : Mem) (base : Addr) {d a n : Nat} (v : BitVec 64) (h : d + 8 ≤ a ∨ a + 8 * n ≤ d)
    (ha : a + 8 * n ≤ 4096) (hd : d + 8 ≤ 4096) :
    Spec.Rsa.wordsAt (m.writeW (VG.Proof.Bignum.X86_64.off base d) v) (VG.Proof.Bignum.X86_64.off base a) n = Spec.Rsa.wordsAt m (VG.Proof.Bignum.X86_64.off base a) n := by
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  show (m.writeW (VG.Proof.Bignum.X86_64.off base d) v).readW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off base a) (8 * i)) 64 = m.readW (VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off base a) (8 * i)) 64
  rw [off_off]
  exact (VG.Proof.Bignum.X86_64.writeW_outside m base v (by omega)).word (by omega) (by omega)

theorem bytes_wo0 (m : Mem) (base : Addr) {a n : Nat} (v : BitVec 64) (h : 8 ≤ a) (ha : a + n ≤ 4096) :
    Spec.Rsa.bytesAt (m.writeW base v) (VG.Proof.Bignum.X86_64.off base a) n = Spec.Rsa.bytesAt m (VG.Proof.Bignum.X86_64.off base a) n := by
  have := VG.Proof.Rsa.X86_64.bytes_wo m base (d := 0) v (.inl h) ha (by decide)
  simpa only [VG.Proof.Bignum.X86_64.off, BitVec.add_zero] using this

theorem words_wo0 (m : Mem) (base : Addr) {a n : Nat} (v : BitVec 64) (h : 8 ≤ a) (ha : a + 8 * n ≤ 4096) :
    Spec.Rsa.wordsAt (m.writeW base v) (VG.Proof.Bignum.X86_64.off base a) n = Spec.Rsa.wordsAt m (VG.Proof.Bignum.X86_64.off base a) n := by
  have := VG.Proof.Rsa.X86_64.words_wo m base (d := 0) v (.inl h) ha (by decide)
  simpa only [VG.Proof.Bignum.X86_64.off, BitVec.add_zero] using this

/-! ## Bits -/

theorem and1_toNat (x : BitVec 64) : (x &&& 1).toNat = x.toNat % 2 := by
  rw [BitVec.toNat_and, show (1 : BitVec 64).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem and1_eq_one (x : BitVec 64) : x &&& 1 = 1 ↔ x.toNat % 2 = 1 := by
  rw [← BitVec.toNat_inj, VG.Proof.Rsa.X86_64.and1_toNat]; rfl

theorem gOf_eq_one (a b c : BitVec 64) : VG.Proof.Rsa.X86_64.gOf a b c = 1 ↔ a &&& 1 = 1 ∧ b &&& 1 = 1 ∧ c &&& 1 = 1 := by
  have key : ∀ x : Nat, x % 2 = 1 ↔ x.testBit 0 = true := fun x => by
    rw [Nat.testBit_zero]; simp
  simp only [VG.Proof.Rsa.X86_64.gOf, VG.Proof.Rsa.X86_64.and1_eq_one, BitVec.toNat_and, key, Nat.testBit_and, Bool.and_eq_true, and_assoc]

theorem and1_of_setWidth_one {x : BitVec 64} (h : x.setWidth 32 = 1) : x &&& 1 = 1 := by
  rw [VG.Proof.Rsa.X86_64.and1_eq_one]
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_setWidth] at this
  have h2 : x.toNat % 2 = x.toNat % 2 ^ 32 % 2 := (Nat.mod_mod_of_dvd _ (by decide)).symm
  rw [h2, this]; rfl

theorem and1_of_setWidth_zero {x : BitVec 64} (h : x.setWidth 32 = 0) : x &&& 1 ≠ 1 := by
  rw [Ne, VG.Proof.Rsa.X86_64.and1_eq_one]
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_setWidth] at this
  have h2 : x.toNat % 2 = x.toNat % 2 ^ 32 % 2 := (Nat.mod_mod_of_dvd _ (by decide)).symm
  rw [h2, this]; decide

/-! ## The check -/

/-- Whether `M` is released: `r₁` odd, `n` a valid modulus, and the public
operation of `M` (within BoringSSL's limits on `e`) the input. -/
def released (r₁ : BitVec 64) (nB eB xB mB : List Byte) : Prop :=
  r₁ &&& 1 = 1 ∧ Spec.Rsa.modulusValid (Spec.Rsa.os2ip nB) nB.length ∧ Spec.Rsa.publicOpChecked nB eB mB = some xB

instance (r₁ : BitVec 64) (nB eB xB mB : List Byte) : Decidable (VG.Proof.Rsa.X86_64.released r₁ nB eB xB mB) := by
  unfold VG.Proof.Rsa.X86_64.released; infer_instance

/-- What the check returns: 1 if it releases `M`, 2 if `r₁` is odd, `n`
valid and the public operation of `M` succeeds but is not the input, 0
otherwise. -/
def checkResult (r₁ : BitVec 64) (nB eB xB mB : List Byte) : BitVec 64 :=
  if r₁ &&& 1 = 1 ∧ Spec.Rsa.modulusValid (Spec.Rsa.os2ip nB) nB.length = true ∧
      (Spec.Rsa.publicOpChecked nB eB mB).isSome = true then
    (if Spec.Rsa.publicOpChecked nB eB mB = some xB then 1 else 2)
  else 0

theorem check_eq (pcName : String) (pc : Prog isa) (pdName : String) (pd : Prog isa) :
    seqs (VG.Impl.Rsa.X86_64.PrivChecked.check pcName pc pdName pd) =
      .seq (.block pcArgs) (.seq (.call pcName pc) (.seq (.block pdArgs) (.seq (.call pdName pd)
        (seqs PrivChecked.tail)))) := rfl

theorem bytesAt_length' (m : Mem) (p : Addr) (n : Nat) : (Spec.Rsa.bytesAt m p n).length = n := by
  simp [Spec.Rsa.bytesAt]

theorem precompute_isSome (nB : List Byte) :
    (Spec.Rsa.publicPrecompute nB).isSome = Spec.Rsa.modulusValid (Spec.Rsa.os2ip nB) nB.length := by
  simp only [Spec.Rsa.publicPrecompute]
  split <;> simp_all

/-- The check's logic: what it returns and whether it releases `M`, from
what the calls returned (`r₂` and `r₃`) and wrote (`outB`). -/
theorem check_logic {r₁ r₂ r₃ : BitVec 64} {nB eB xB mB outB : List Byte}
    (h3 : match Spec.Rsa.publicPrecompute nB with
      | some _ => r₃.setWidth 32 = 1
      | none => r₃.setWidth 32 = 0)
    (h2 : (Spec.Rsa.publicPrecompute nB).isSome = true →
      match Spec.Rsa.publicOpChecked nB eB mB with
      | some y => r₂.setWidth 32 = 1 ∧ outB = y
      | none => r₂.setWidth 32 = 0) :
    VG.Proof.Rsa.X86_64.result (VG.Proof.Rsa.X86_64.gOf r₂ r₁ r₃) (decide (outB = xB)) = VG.Proof.Rsa.X86_64.checkResult r₁ nB eB xB mB ∧
      ((VG.Proof.Rsa.X86_64.gOf r₂ r₁ r₃ = 1 ∧ outB = xB) ↔ VG.Proof.Rsa.X86_64.released r₁ nB eB xB mB) := by
  unfold VG.Proof.Rsa.X86_64.checkResult VG.Proof.Rsa.X86_64.released VG.Proof.Rsa.X86_64.result
  rw [← VG.Proof.Rsa.X86_64.precompute_isSome]
  cases hpc : Spec.Rsa.publicPrecompute nB with
  | none =>
    simp only [hpc] at h3
    have hg : VG.Proof.Rsa.X86_64.gOf r₂ r₁ r₃ ≠ 1 := fun h => VG.Proof.Rsa.X86_64.and1_of_setWidth_zero h3 ((VG.Proof.Rsa.X86_64.gOf_eq_one _ _ _).mp h).2.2
    have hg' : ¬ VG.Proof.Rsa.X86_64.gOf r₂ r₁ r₃ = 1#64 := hg
    simp [hg']
  | some ws =>
    simp only [hpc] at h3
    have h2 := h2 (by simp [hpc])
    cases hpo : Spec.Rsa.publicOpChecked nB eB mB with
    | none =>
      simp only [hpo] at h2
      have hg : VG.Proof.Rsa.X86_64.gOf r₂ r₁ r₃ ≠ 1 := fun h => VG.Proof.Rsa.X86_64.and1_of_setWidth_zero h2 ((VG.Proof.Rsa.X86_64.gOf_eq_one _ _ _).mp h).1
      have hg' : ¬ VG.Proof.Rsa.X86_64.gOf r₂ r₁ r₃ = 1#64 := hg
      simp [hg']
    | some y =>
      simp only [hpo] at h2
      obtain ⟨h2, rfl⟩ := h2
      have hg : VG.Proof.Rsa.X86_64.gOf r₂ r₁ r₃ = 1 ↔ r₁ &&& 1 = 1 := by
        rw [VG.Proof.Rsa.X86_64.gOf_eq_one]; exact ⟨fun h => h.2.1, fun h => ⟨VG.Proof.Rsa.X86_64.and1_of_setWidth_one h2, h, VG.Proof.Rsa.X86_64.and1_of_setWidth_one h3⟩⟩
      by_cases h1 : r₁ &&& 1 = 1
      · have hg1 : VG.Proof.Rsa.X86_64.gOf r₂ r₁ r₃ = 1#64 := hg.mpr h1
        have h1' : r₁ &&& 1#64 = 1#64 := h1
        simp [hg1, h1']
      · have hg1 : ¬ VG.Proof.Rsa.X86_64.gOf r₂ r₁ r₃ = 1#64 := fun h => h1 (hg.mp h)
        have h1' : ¬ r₁ &&& 1#64 = 1#64 := h1
        simp [hg1, h1']

/-- Everything after the CRT, from any state the frame allows: whatever `M`
holds and the CRT returned. -/
theorem check_ok (M : Mont) (pcName pdName : String)
    (pcMx : (Precompute.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (pdMx : (Precomputed.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (pcNosp : NoSp (Precompute.code M.mm)) (pdNosp : NoSp (Checked.precomputedChecked M.mm))
    (pcDepth : (Precompute.code M.mm).depth = 0) (pdDepth : (Checked.precomputedChecked M.mm).depth = 0)
    {s t : State} (hp : PreF s) (he : VG.Proof.Rsa.X86_64.Env s t) :
    WP isa (seqs (VG.Impl.Rsa.X86_64.PrivChecked.check pcName (Precompute.code M.mm) pdName (Checked.precomputedChecked M.mm))) t fun t' =>
      VG.Proof.Rsa.X86_64.Env s t' ∧
      t'.gpr .rax = VG.Proof.Rsa.X86_64.checkResult (t.gpr .rax) (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) VG.Impl.Rsa.X86_64.PrivChecked.oM) (s.gpr .rcx).toNat) ∧
      Spec.Rsa.bytesAt t'.mem (s.gpr .rdi) (s.gpr .rcx).toNat =
        (if VG.Proof.Rsa.X86_64.released (t.gpr .rax) (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
            (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
            (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat)
            (Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) VG.Impl.Rsa.X86_64.PrivChecked.oM) (s.gpr .rcx).toNat)
          then Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) VG.Impl.Rsa.X86_64.PrivChecked.oM) (s.gpr .rcx).toNat
          else List.replicate (s.gpr .rcx).toNat 0) ∧
      Spec.Rsa.bytesAt t'.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) VG.Impl.Rsa.X86_64.PrivChecked.oM) (s.gpr .rcx).toNat = List.replicate (s.gpr .rcx).toNat 0 ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 := by
  have hk2 := hp.k2
  have hpw := VG.Proof.Rsa.X86_64.preWords_le hp
  have csk : ∀ {rs : List Reg} {a b : State}, VG.Proof.MlKem.X86_64.Keep rs a b → (∀ r ∈ calleeSaved, r ∉ rs) →
      ∀ r ∈ calleeSaved, b.gpr r = a.gpr r := fun k h r hr => k.gpr (h r hr)
  rw [VG.Proof.Rsa.X86_64.check_eq]
  refine WP.seq (WP.mono_mx (by decide +kernel) (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8, .r9] (VG.Proof.Rsa.X86_64.pcArgs_ok hp he) rfl)
    fun t₁ ⟨⟨he₁, hm₁, hdi, hsi, hdx, hcx, h8, h9⟩, k₁⟩ hmx₁ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.pc_call M pcName pcMx pcNosp pcDepth hp he₁ hdi hsi hdx hcx h8 h9)
    fun t₂ ⟨he₂, hpc, hM₂, hR1₂, hcs₂, hmx₂⟩ => ?_)
  refine WP.seq (WP.mono_mx (by decide +kernel)
    (WP.keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] (VG.Proof.Rsa.X86_64.pdArgs_ok hp he₂) rfl)
    fun t₃ ⟨⟨he₃, hm₃, hdi₃, hsi₃, hdx₃, hcx₃, h8₃, h9₃⟩, k₃⟩ hmx₃ => ?_)
  have hw : ∀ {d : Nat}, d < 4 → VG.Proof.Bignum.X86_64.word t₃.mem (VG.Proof.Rsa.X86_64.fb s) (8 * d) =
      [VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) VG.Impl.Rsa.X86_64.PrivChecked.oM, s.gpr .rcx, stackArg s 12, stackArg s 13].getD d 0 := fun {d} hd => by
    rw [hm₃]
    rcases (show d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 by omega) with rfl | rfl | rfl | rfl
    · simp (disch := decide) only [word_wo, VG.Proof.Rsa.X86_64.word_self0, Nat.mul_zero]
      rfl
    · simp (disch := decide) only [word_wo, VG.Proof.Bignum.X86_64.word_writeW_self, Nat.mul_one]; rfl
    · simp (disch := decide) only [word_wo, VG.Proof.Bignum.X86_64.word_writeW_self]; rfl
    · simp (disch := decide) only [VG.Proof.Bignum.X86_64.word_writeW_self]; rfl
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.pd_call M pdName pdMx pdNosp pdDepth hp he₃ (hw (d := 0) (by decide))
    (hw (d := 1) (by decide)) (hw (d := 2) (by decide)) (hw (d := 3) (by decide)) hdi₃ hsi₃ hdx₃ hcx₃ h8₃ h9₃)
    fun t₄ ⟨he₄, hpd, hM₄, hR1₄, hR3₄, hcs₄, hmx₄⟩ => ?_)
  refine WP.mono_mx (by decide +kernel)
    (WP.keep [.rax, .r11, .rdi, .rsi, .rcx, .r10, .rdx, .r9, .r8] (VG.Proof.Rsa.X86_64.tail_ok hp he₄) (by decide +kernel))
    fun t' ⟨⟨hax, hout, hM', he'⟩, k₅⟩ hmx₅ => ⟨he', ?_, ?_, hM',
      fun r hr => by rw [csk k₅ (by decide) r hr, hcs₄ r hr, csk k₃ (by decide) r hr, hcs₂ r hr,
        csk k₁ (by decide) r hr],
      by rw [hmx₅, hmx₄, hmx₃, hmx₂, hmx₁]⟩ <;> clear hM'
  all_goals
    -- The values the tail reads.
    have hr1 : VG.Proof.Bignum.X86_64.word t₄.mem (VG.Proof.Rsa.X86_64.fb s) oR1 = t.gpr .rax := by
      rw [hR1₄, hm₃]
      simp (disch := decide) only [word_wo, VG.Proof.Rsa.X86_64.word_wo0]
      rw [hR1₂, hm₁, VG.Proof.Bignum.X86_64.word_writeW_self]
    have hr3 : VG.Proof.Bignum.X86_64.word t₄.mem (VG.Proof.Rsa.X86_64.fb s) oR3 = t₂.gpr .rax := by
      rw [hR3₄, hm₃]
      simp (disch := decide) only [word_wo, VG.Proof.Rsa.X86_64.word_wo0, VG.Proof.Bignum.X86_64.word_writeW_self]
    have hmb : Spec.Rsa.bytesAt t₃.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) VG.Impl.Rsa.X86_64.PrivChecked.oM) (s.gpr .rcx).toNat =
        Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) VG.Impl.Rsa.X86_64.PrivChecked.oM) (s.gpr .rcx).toNat := by
      rw [hm₃]
      simp (disch := first | decide | (simp only [oM, oR3, oR1]; omega)) only [VG.Proof.Rsa.X86_64.bytes_wo, VG.Proof.Rsa.X86_64.bytes_wo0]
      rw [hM₂, hm₁, VG.Proof.Rsa.X86_64.bytes_wo _ _ _ (.inl (by decide)) (by unfold VG.Impl.Rsa.X86_64.PrivChecked.oM; omega) (by decide)]
    have hpre : Spec.Rsa.wordsAt t₃.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) oPre) (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) =
        Spec.Rsa.wordsAt t₂.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) oPre) (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) := by
      rw [hm₃]
      simp (disch := first | decide | (simp only [oPre, oR3]; omega)) only [VG.Proof.Rsa.X86_64.words_wo, VG.Proof.Rsa.X86_64.words_wo0]
    rw [hr1, hr3] at hax hout
    rw [hM₄, hmb] at hout
    simp only [hmb] at hpd
    have h3 : match Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) with
        | some _ => (t₂.gpr .rax).setWidth 32 = 1
        | none => (t₂.gpr .rax).setWidth 32 = 0 := by
      cases hc : Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) <;>
        simp only [hc] at hpc ⊢ <;> exact hpc.1
    have hl := VG.Proof.Rsa.X86_64.check_logic (r₁ := t.gpr .rax) (r₂ := t₄.gpr .rax) (r₃ := t₂.gpr .rax)
      (eB := Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
      (mB := Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) VG.Impl.Rsa.X86_64.PrivChecked.oM) (s.gpr .rcx).toNat)
      (outB := Spec.Rsa.bytesAt t₄.mem (s.gpr .rdi) (s.gpr .rcx).toNat)
      (xB := Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat) h3 (fun hs => by
        obtain ⟨ws, hws⟩ := Option.isSome_iff_exists.mp hs
        rw [hws] at hpc
        have := hpd _ (VG.Proof.Rsa.X86_64.bytesAt_length' _ _ _) (by rw [hws, hpre, hpc.2])
        cases hpo : Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
            (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
            (Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) VG.Impl.Rsa.X86_64.PrivChecked.oM) (s.gpr .rcx).toNat) <;>
          simp only [hpo, Spec.Rsa.written] at this ⊢
        · exact this.1
        · exact this)
    first | (rw [hax]; exact hl.1) | (rw [hout]; exact if_congr hl.2 rfl rfl)

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.PrivOutcome`. -/
section

/-!
# `vg_rsa_private_checked` on x86-64: the outcome

What the CRT returns and writes, followed by what the check returns and
releases (`check_ok`), is `privateChecked`'s outcome (`outcome_eq`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64

/-- The CRT's result `mB` (returning `rc`), and the check's of it (returning
`r` and writing `outB`), are the checked private operation's. -/
theorem outcome_eq {m m' : Mem} {M out : Addr} {k : Nat} {rc r : BitVec 64}
    {nB eB xB pB qB dPB dQB qInvB : List Byte} (hn : nB.length = k) (hx : xB.length = k)
    (hcrt : Spec.Rsa.written m M k (rc.setWidth 32) (Spec.Rsa.privateCrt nB xB pB qB dPB dQB qInvB))
    (hr : r = VG.Proof.Rsa.X86_64.checkResult rc nB eB xB (Spec.Rsa.bytesAt m M k))
    (hout : Spec.Rsa.bytesAt m' out k =
      if VG.Proof.Rsa.X86_64.released rc nB eB xB (Spec.Rsa.bytesAt m M k) then Spec.Rsa.bytesAt m M k else List.replicate k 0) :
    Spec.Rsa.writtenOutcome m' out k (r.setWidth 32) (Spec.Rsa.privateChecked nB eB xB pB qB dPB dQB qInvB) := by
  rw [Proof.Rsa.privateChecked_of_crt (hx.trans hn.symm)]
  cases hc : Spec.Rsa.privateCrt nB xB pB qB dPB dQB qInvB with
  | none =>
    rw [hc] at hcrt
    have h1 := VG.Proof.Rsa.X86_64.and1_of_setWidth_zero hcrt.1
    have hrel : ¬ VG.Proof.Rsa.X86_64.released rc nB eB xB (Spec.Rsa.bytesAt m M k) := fun h => h1 h.1
    simp only [VG.Proof.Rsa.X86_64.checkResult, h1, false_and, ↓reduceIte] at hr
    simp only [hrel, ↓reduceIte] at hout
    exact ⟨by rw [hr]; rfl, hout⟩
  | some y =>
    rw [hc] at hcrt
    obtain ⟨hr1, hy⟩ := hcrt
    obtain ⟨hm, hs⟩ := Proof.Rsa.privateCrt_some hc
    have h1 := VG.Proof.Rsa.X86_64.and1_of_setWidth_one hr1
    rw [hy] at hr hout
    by_cases he : Spec.Rsa.exponentValid (Spec.Rsa.os2ip eB) = true
    · have hsome := hs eB he
      by_cases hp : Spec.Rsa.publicOpChecked nB eB y = some xB
      · have hrel : VG.Proof.Rsa.X86_64.released rc nB eB xB y := ⟨h1, hm, hp⟩
        simp only [VG.Proof.Rsa.X86_64.checkResult, h1, hm, hp, ↓reduceIte] at hr
        simp only [hrel, ↓reduceIte] at hout
        simp only [he, hp, ↓reduceIte]
        exact ⟨by rw [hr]; rfl, hout⟩
      · have hrel : ¬ VG.Proof.Rsa.X86_64.released rc nB eB xB y := fun h => hp h.2.2
        simp only [VG.Proof.Rsa.X86_64.checkResult, h1, hm, hsome, hp, and_self, ↓reduceIte] at hr
        simp only [hrel, ↓reduceIte] at hout
        simp only [he, hp, ↓reduceIte]
        exact ⟨by rw [hr]; rfl, hout⟩
    · have hnone : Spec.Rsa.publicOpChecked nB eB y = none := by
        simp only [Spec.Rsa.publicOpChecked, he]; rfl
      have hrel : ¬ VG.Proof.Rsa.X86_64.released rc nB eB xB y := fun h => by
        have := h.2.2; rw [hnone] at this; cases this
      simp only [VG.Proof.Rsa.X86_64.checkResult, hnone, Option.isSome_none, Bool.false_eq_true, and_false, ↓reduceIte] at hr
      simp only [hrel, ↓reduceIte] at hout
      simp only [he, Bool.false_eq_true, ↓reduceIte]
      exact ⟨by rw [hr]; rfl, hout⟩

/-! ## Fault tolerance -/

/-- What the check releases passes it: a result 1 means `mB` (of `k` octets)
is below `n` and `mB^e mod n` is the input. -/
theorem checkResult_sound {r₁ : BitVec 64} {nB eB xB mB : List Byte} (hx : xB.length = nB.length)
    (h : VG.Proof.Rsa.X86_64.checkResult r₁ nB eB xB mB = 1) :
    VG.Proof.Rsa.X86_64.released r₁ nB eB xB mB ∧ Spec.Rsa.os2ip mB < Spec.Rsa.os2ip nB ∧
      Spec.Rsa.os2ip mB ^ Spec.Rsa.os2ip eB % Spec.Rsa.os2ip nB = Spec.Rsa.os2ip xB := by
  simp only [VG.Proof.Rsa.X86_64.checkResult] at h
  split at h
  · rename_i hc
    split at h
    · rename_i hp
      exact ⟨⟨hc.1, hc.2.1, hp⟩, Proof.Rsa.publicOpChecked_sound hx hp⟩
    · cases h
  · cases h

/-- The check and the release are correct whatever the CRT left in `M` and
returned: they release `M` (returning 1) only if `M` is below `n` and
`M^e mod n` is the input, and write zeros otherwise; `M` is zeroed either
way. A fault in the CRT's computation (of the result, of its return value,
or of both) is never released. -/
theorem check_faultTolerant (M : Mont) (pcName pdName : String)
    (pcMx : (Precompute.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (pdMx : (Precomputed.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (pcNosp : NoSp (Precompute.code M.mm)) (pdNosp : NoSp (Checked.precomputedChecked M.mm))
    (pcDepth : (Precompute.code M.mm).depth = 0) (pdDepth : (Checked.precomputedChecked M.mm).depth = 0)
    {s t : State} (hp : PreF s) (he : VG.Proof.Rsa.X86_64.Env s t) :
    WP isa (seqs (PrivChecked.check pcName (Precompute.code M.mm) pdName
        (Checked.precomputedChecked M.mm))) t fun t' =>
      (t'.gpr .rax = 1 →
        Spec.Rsa.bytesAt t'.mem (s.gpr .rdi) (s.gpr .rcx).toNat =
            Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) PrivChecked.oM) (s.gpr .rcx).toNat ∧
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) PrivChecked.oM) (s.gpr .rcx).toNat) <
            Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) ∧
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) PrivChecked.oM) (s.gpr .rcx).toNat) ^
              Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) %
              Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) =
            Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat)) ∧
      (t'.gpr .rax ≠ 1 → Spec.Rsa.bytesAt t'.mem (s.gpr .rdi) (s.gpr .rcx).toNat =
        List.replicate (s.gpr .rcx).toNat 0) ∧
      Spec.Rsa.bytesAt t'.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) PrivChecked.oM) (s.gpr .rcx).toNat =
        List.replicate (s.gpr .rcx).toNat 0 :=
  WP.mono (VG.Proof.Rsa.X86_64.check_ok M pcName pdName pcMx pdMx pcNosp pdNosp pcDepth pdDepth hp he)
    fun t' ⟨_, hax, hout, hM, _⟩ => by
      have hx : (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat).length =
          (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat).length := by
        rw [VG.Proof.Rsa.X86_64.bytesAt_length', VG.Proof.Rsa.X86_64.bytesAt_length']
      refine ⟨fun h1 => ?_, fun h1 => ?_, hM⟩
      · obtain ⟨hrel, hs⟩ := VG.Proof.Rsa.X86_64.checkResult_sound hx (hax ▸ h1)
        simp only [hrel, ↓reduceIte] at hout
        exact ⟨hout, hs⟩
      · have hrel : ¬ VG.Proof.Rsa.X86_64.released (t.gpr .rax) (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
            (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
            (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat)
            (Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) PrivChecked.oM) (s.gpr .rcx).toNat) := fun h => by
          apply h1
          rw [hax]
          simp only [VG.Proof.Rsa.X86_64.checkResult, h.1, h.2.1, h.2.2, Option.isSome_some, and_self, ↓reduceIte]
        simp only [hrel, ↓reduceIte] at hout
        exact hout

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.PrivCorrect`. -/
section

/-!
# `vg_rsa_private_checked` on x86-64: correctness

The frame's push, the CRT's arguments and call (`crtArgs_ok`, `crt_call`),
the check (`check_ok`) and the pop: `code_correct`, for every implementation
of the CRT.
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.PrivChecked
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64

/-- The state after the frame's pop, from the state `s₂` its body ends in. -/
def freed (bytes : Nat) (s₂ : State) : State :=
  { s₂.setReg .rsp (s₂.gpr .rsp + BitVec.ofNat 64 bytes) with wr := s₂.wr.tail }

/-- The frame: its body runs from `allocState frameBytes s` and ends with
`rsp` and the writable regions as the push left them. -/
theorem wp_alloc {body : Prog isa} {s : State} {Q : State → Prop} (hsp : frameBytes ≤ (s.gpr .rsp).toNat)
    (hb : WP isa body (allocState frameBytes s) fun s₂ => s₂.gpr .rsp = VG.Proof.Rsa.X86_64.fb s ∧
      s₂.wr = (allocState frameBytes s).wr ∧ Q (VG.Proof.Rsa.X86_64.freed frameBytes s₂)) :
    WP isa (.frame (.alloc frameBytes) body (.free frameBytes)) s Q := by
  obtain ⟨t, s₂, he, hsp₂, hw, hq⟩ := hb
  have ha : isa.push (.alloc frameBytes) s = some (allocState frameBytes s) := by
    simp only [isa, push, allocState]
    exact ite_eq_left ⟨by decide, by decide, by decide, hsp⟩
  have hf : isa.pop (.free frameBytes) (allocState frameBytes s) s₂ = some (VG.Proof.Rsa.X86_64.freed frameBytes s₂) := by
    simp only [isa, pop]
    exact ite_eq_left ⟨by decide, by decide, by decide, hsp₂, hw, rfl⟩
  exact ⟨_, _, Exec.frame ha he hf, hq⟩

theorem body_eq (crtName : String) (crt : Prog isa) (pcName : String) (pc : Prog isa) (pdName : String)
    (pd : Prog isa) :
    VG.Impl.Rsa.X86_64.PrivChecked.body crtName crt pcName pc pdName pd =
      .seq (.block crtArgs) (.seq (.call crtName crt) (seqs (VG.Impl.Rsa.X86_64.PrivChecked.check pcName pc pdName pd))) := rfl

/-- The return address is outside everything the function writes. -/
theorem ret_frame {s : State} (hp : PreF s) {m : Mem} (h : Frame [stkR s, VG.Proof.Rsa.X86_64.outR s, scrR s] s.mem m) :
    m.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
  have hsp2 := hp.sp2
  refine h.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · have := Offset.disjoint_below (s.gpr .rsp) (n := stackBytes) (d := 0) (k := 8)
      (by unfold stackBytes; omega)
    simpa only [stkR, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  · exact hp.dRo
  · exact hp.dRs

theorem code_correct (v : CrtImpl) (pcName pdName : String) (s : State) (h : chkContract.pre s) :
    ∃ t s', Exec isa (VG.Impl.Rsa.X86_64.PrivChecked.code v.name v.code pcName (Precompute.code v.mont.mm) pdName
        (Checked.precomputedChecked v.mont.mm)) s t s' ∧ abiPreserved s s' ∧ chkContract.post s s' := by
  have hp := preF_of h
  have hk2 := hp.k2
  suffices hw : WP isa (VG.Impl.Rsa.X86_64.PrivChecked.code v.name v.code pcName (Precompute.code v.mont.mm) pdName
      (Checked.precomputedChecked v.mont.mm)) s fun s' => abiPreserved s s' ∧ chkContract.post s s' by
    obtain ⟨t, s', he, hq⟩ := hw
    exact ⟨t, s', he, hq⟩
  refine VG.Proof.Rsa.X86_64.wp_alloc (by have := hp.sp1; unfold stackBytes at this; unfold frameBytes; omega) ?_
  rw [VG.Proof.Rsa.X86_64.body_eq]
  refine WP.seq (WP.mono_mx (by decide +kernel)
    (WP.keep [.rax, .rdi, .rsi, .r8, .r9] (crtArgs_ok hp) (by decide +kernel))
    fun t₁ ⟨⟨he₁, _, hargs, hdi, hsi, hdx, hcx, h8, h9⟩, k₁⟩ hmx₁ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86_64.crt_call v hp he₁ hargs hdi hsi hdx hcx h8 h9) fun t₂ ⟨he₂, hcrt, hcs₂, hmx₂⟩ => ?_)
  refine WP.mono (VG.Proof.Rsa.X86_64.check_ok v.mont pcName pdName v.pcMx v.pdMx v.pcNosp v.pdNosp v.pcDepth v.pdDepth hp he₂)
    fun t₃ ⟨he₃, hrax, hout, _, hcs₃, hmx₃⟩ => ?_
  refine ⟨he₃.rsp, by rw [he₃.wr]; rfl, ⟨fun r hr => ?_, VG.Proof.Rsa.X86_64.ret_frame hp he₃.mem, ?_⟩, ?_⟩
  · by_cases hr' : r = .rsp
    · subst hr'
      show t₃.gpr .rsp + BitVec.ofNat 64 frameBytes = s.gpr .rsp
      rw [he₃.rsp, BitVec.sub_add_cancel]
    · show (if r = .rsp then _ else t₃.gpr r) = s.gpr r
      simp only [hr', ↓reduceIte]
      rw [hcs₃ r hr, hcs₂ r hr, k₁.gpr (by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all)]
      simp only [allocState_gpr, hr', ↓reduceIte]
  · show t₃.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10
    rw [hmx₃, hmx₂, hmx₁]; rfl
  · have hfr : (VG.Proof.Rsa.X86_64.freed frameBytes t₃).gpr .rax = t₃.gpr .rax := rfl
    have hfm : (VG.Proof.Rsa.X86_64.freed frameBytes t₃).mem = t₃.mem := rfl
    simp only [chkContract, hfr, hfm]
    exact VG.Proof.Rsa.X86_64.outcome_eq (VG.Proof.Rsa.X86_64.bytesAt_length' _ _ _) (by rw [VG.Proof.Rsa.X86_64.bytesAt_length']) hcrt hrax hout

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.PrivCT`. -/
section

/-!
# `vg_rsa_private_checked` on x86-64: constant time

Two runs from entry states that agree on the public data (`chkContract.pub`:
the pointers and lengths, `n` and `e`) leak the same trace. Each point of
the code is described, in each run, by what correctness says of it from that
run's entry state, which agrees with an anchor `a` on the public data
(`At`): the blocks between the calls are checked by the taint analysis
from the registers this fixes, and each call is constant time for its
callee's contract, whose public data it fixes too (`body_ct`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.PrivChecked
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64

/-! ## Entry states and the anchor -/

/-- An entry state meeting the precondition with the anchor's public data. -/
def Sib (a s : State) : Prop := chkContract.pre s ∧ chkContract.pub a s

theorem pub_refl (s : State) : chkContract.pub s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Sib.gpr {a s : State} (h : VG.Proof.Rsa.X86_64.Sib a s) {r : Reg} (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) :
    s.gpr r = a.gpr r := (h.2.1 r hr).symm

theorem Sib.arg {a s : State} (h : VG.Proof.Rsa.X86_64.Sib a s) {i : Nat} (hi : i < 14) : stackArg s i = stackArg a i :=
  ((List.map_inj_left.mp h.2.2.1) i (List.mem_range.mpr hi)).symm

theorem Sib.n {a s : State} (h : VG.Proof.Rsa.X86_64.Sib a s) :
    Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat :=
  h.2.2.2.1.symm

theorem Sib.e {a s : State} (h : VG.Proof.Rsa.X86_64.Sib a s) :
    Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .r8) (a.gpr .r9).toNat :=
  h.2.2.2.2.symm

theorem Sib.fb {a s : State} (h : VG.Proof.Rsa.X86_64.Sib a s) : VG.Proof.Rsa.X86_64.fb s = VG.Proof.Rsa.X86_64.fb a := by
  show s.gpr .rsp - _ = a.gpr .rsp - _
  rw [h.gpr (r := .rsp) (by decide)]

/-- A point of a run, described by `J` from the run's entry state. -/
def At (J : State → State → Prop) (a t : State) : Prop := ∃ s, VG.Proof.Rsa.X86_64.Sib a s ∧ J s t

/-- A register `J` gives as a function of the public data. -/
theorem pin {J : State → State → Prop} {r : Reg} (f : State → BitVec 64) (hf : ∀ s t, J s t → t.gpr r = f s)
    (hs : ∀ a s, VG.Proof.Rsa.X86_64.Sib a s → f s = f a) {a t₁ t₂ : State} (h₁ : VG.Proof.Rsa.X86_64.At J a t₁) (h₂ : VG.Proof.Rsa.X86_64.At J a t₂) :
    t₁.gpr r = t₂.gpr r := by
  obtain ⟨s₁, S₁, j₁⟩ := h₁
  obtain ⟨s₂, S₂, j₂⟩ := h₂
  rw [hf _ _ j₁, hf _ _ j₂, hs _ _ S₁, hs _ _ S₂]

/-- In the frame, `rsp` is public. -/
theorem pins_rsp {J : State → State → Prop} (hJ : ∀ s t, J s t → VG.Proof.Rsa.X86_64.Env s t) : Pins (VG.Proof.Rsa.X86_64.At J) [.rsp] :=
  fun _ _ _ h₁ h₂ r hr => by
    rw [List.mem_singleton.mp hr]
    exact VG.Proof.Rsa.X86_64.pin VG.Proof.Rsa.X86_64.fb (fun s t h => (hJ s t h).rsp) (fun _ _ h => h.fb) h₁ h₂

theorem Env.congr {s t t' : State} (he : VG.Proof.Rsa.X86_64.Env s t) (hm : t'.mem = t.mem) (hk : VG.Proof.MlKem.X86_64.Keep [.rax, .r11, .rdi, .rsi, .rcx, .r10, .rdx] t t') :
    VG.Proof.Rsa.X86_64.Env s t' :=
  ⟨(hk.gpr (by decide)).trans he.rsp, hk.2.1.trans he.rd, hk.2.2.trans he.wr, hm ▸ he.mem, hm ▸ he.sOut,
    hm ▸ he.sN, hm ▸ he.sK, hm ▸ he.sE, hm ▸ he.sEl⟩

/-- A caller's buffer, read by a callee: the same as at the entry. -/
theorem Env.entryBytes {s t : State} (he : VG.Proof.Rsa.X86_64.Env s t) (rd wr : List Region) {p : Addr} {len : Nat}
    (hk : (stkR s).Disjoint ⟨p, len⟩) (ho : (VG.Proof.Rsa.X86_64.outR s).Disjoint ⟨p, len⟩) (hs : (scrR s).Disjoint ⟨p, len⟩)
    (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt (t.callEntry.withRegions rd wr).mem p len = Spec.Rsa.bytesAt s.mem p len := by
  rw [State.withRegions_mem]
  exact VG.Proof.Rsa.X86_64.bytes_of_frame (VG.Proof.Rsa.X86_64.frame_call he.mem (VG.Proof.Rsa.X86_64.callEntry_frame he.rsp) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact .inl (VG.Proof.Rsa.X86_64.below_sub s)) hk ho hs hl

/-! ## The points of the code -/

def J0 (s t : State) : Prop := t = allocState frameBytes s

def J1 (s t : State) : Prop :=
  VG.Proof.Rsa.X86_64.Env s t ∧ (∀ i < 12, VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) (8 * i) = stackArg s (i + 2)) ∧ t.gpr .rdi = VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) VG.Impl.Rsa.X86_64.PrivChecked.oM ∧
    t.gpr .rsi = s.gpr .rcx ∧ t.gpr .rdx = s.gpr .rdx ∧ t.gpr .rcx = s.gpr .rcx ∧ t.gpr .r8 = stackArg s 0 ∧
    t.gpr .r9 = s.gpr .rcx

def J2 (s t : State) : Prop := VG.Proof.Rsa.X86_64.Env s t

def J3 (s t : State) : Prop :=
  VG.Proof.Rsa.X86_64.Env s t ∧ t.gpr .rdi = VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) oPre ∧
    t.gpr .rsi = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) ∧
    t.gpr .rdx = s.gpr .rdx ∧ t.gpr .rcx = s.gpr .rcx ∧ t.gpr .r8 = stackArg s 12 ∧ t.gpr .r9 = stackArg s 13

/-- The precomputed values of `n`, or zeros. -/
def preVal (nB : List Byte) (w : Nat) : List (BitVec 64) :=
  match Spec.Rsa.publicPrecompute nB with
  | some ws => ws
  | none => List.replicate w 0

def J4 (s t : State) : Prop :=
  VG.Proof.Rsa.X86_64.Env s t ∧ Spec.Rsa.wordsAt t.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) oPre) (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) =
    VG.Proof.Rsa.X86_64.preVal (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat)

def J5 (s t : State) : Prop :=
  VG.Proof.Rsa.X86_64.J4 s t ∧ VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) 0 = VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) VG.Impl.Rsa.X86_64.PrivChecked.oM ∧ VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) 8 = s.gpr .rcx ∧
    VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) 16 = stackArg s 12 ∧ VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) 24 = stackArg s 13 ∧
    t.gpr .rdi = s.gpr .rdi ∧ t.gpr .rsi = s.gpr .rcx ∧ t.gpr .rdx = VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) oPre ∧
    t.gpr .rcx = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) ∧
    t.gpr .r8 = s.gpr .r8 ∧ t.gpr .r9 = s.gpr .r9

def J7 (s t : State) : Prop :=
  t.gpr .rsp = VG.Proof.Rsa.X86_64.fb s ∧ t.gpr .rdi = s.gpr .rdi ∧ t.gpr .rsi = stackArg s 0 ∧ t.gpr .rcx = s.gpr .rcx ∧
    t.gpr .r10 = BitVec.ofNat 64 0

/-! ## The calls -/

/-- The registers a callee sees, from the caller's. -/
theorem entry_regs (t : State) (rd wr : List Region) :
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map (t.callEntry.withRegions rd wr).gpr =
      [t.gpr .rdi, t.gpr .rsi, t.gpr .rdx, t.gpr .rcx, t.gpr .r8, t.gpr .r9, t.gpr .rsp - 8] := by
  simp only [List.map_cons, List.map_nil, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide)]

theorem regs_eq {s₁ s₂ : State}
    (h : [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map s₁.gpr = [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map s₂.gpr) :
    ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r :=
  List.map_inj_left.mp h

/-- What the CRT's contract makes public, from the entry state. -/
theorem crt_view {a s t : State} (S : VG.Proof.Rsa.X86_64.Sib a s) (h : VG.Proof.Rsa.X86_64.J1 s t) :
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map (t.callEntry.withRegions (VG.Proof.Rsa.X86_64.crtRd s) (VG.Proof.Rsa.X86_64.crtWr s)).gpr =
      [VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb a) VG.Impl.Rsa.X86_64.PrivChecked.oM, a.gpr .rcx, a.gpr .rdx, a.gpr .rcx, stackArg a 0, a.gpr .rcx, VG.Proof.Rsa.X86_64.fb a - 8] ∧
    (∀ i < 12, stackArg (t.callEntry.withRegions (VG.Proof.Rsa.X86_64.crtRd s) (VG.Proof.Rsa.X86_64.crtWr s)) i = stackArg a (i + 2)) ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions (VG.Proof.Rsa.X86_64.crtRd s) (VG.Proof.Rsa.X86_64.crtWr s)).mem
      ((t.callEntry.withRegions (VG.Proof.Rsa.X86_64.crtRd s) (VG.Proof.Rsa.X86_64.crtWr s)).gpr .rdx)
      ((t.callEntry.withRegions (VG.Proof.Rsa.X86_64.crtRd s) (VG.Proof.Rsa.X86_64.crtWr s)).gpr .rcx).toNat =
      Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat := by
  obtain ⟨he, hargs, hdi, hsi, hdx, hcx, h8, h9⟩ := h
  have hp := preF_of S.1
  refine ⟨?_, fun i hi => ?_, ?_⟩
  · rw [VG.Proof.Rsa.X86_64.entry_regs, hdi, hsi, hdx, hcx, h8, h9, he.rsp, S.fb, S.gpr (r := .rcx) (by decide),
      S.gpr (r := .rdx) (by decide), S.arg (by decide)]
  · rw [VG.Proof.Rsa.X86_64.stackArg_entry he.rsp _ _ (by omega), hargs i hi, S.arg (by omega)]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), hdx, hcx]
    rw [he.entryBytes _ _ hp.dKn hp.dOn hp.dns.symm (by have := hp.wN; omega), S.n]

theorem crt_ct (v : CrtImpl) : RelCT isa (Two (VG.Proof.Rsa.X86_64.At VG.Proof.Rsa.X86_64.J1)) (.call v.name v.code) fun _ _ => True := by
  refine RelCT.callEx (k := crtContract) v.ok v.ct fun t₁ t₂ ⟨a, ⟨s₁, S₁, j₁⟩, ⟨s₂, S₂, j₂⟩⟩ => ?_
  obtain ⟨r₁, g₁, n₁⟩ := VG.Proof.Rsa.X86_64.crt_view S₁ j₁
  obtain ⟨r₂, g₂, n₂⟩ := VG.Proof.Rsa.X86_64.crt_view S₂ j₂
  obtain ⟨c₁, w₁⟩ := VG.Proof.Rsa.X86_64.crt_covers (preF_of S₁.1) j₁.1
  obtain ⟨c₂, w₂⟩ := VG.Proof.Rsa.X86_64.crt_covers (preF_of S₂.1) j₂.1
  obtain ⟨he₁, hargs₁, hdi₁, hsi₁, hdx₁, hcx₁, h8₁, h9₁⟩ := j₁
  obtain ⟨he₂, hargs₂, hdi₂, hsi₂, hdx₂, hcx₂, h8₂, h9₂⟩ := j₂
  have p₁ : crtContract.pre ((t₁.callEntry).withRegions (VG.Proof.Rsa.X86_64.crtRd s₁) (VG.Proof.Rsa.X86_64.crtWr s₁)) :=
    VG.Proof.Rsa.X86_64.crt_pre (preF_of S₁.1) he₁ hargs₁ hdi₁ hsi₁ hdx₁ hcx₁ h8₁ h9₁
  have p₂ : crtContract.pre ((t₂.callEntry).withRegions (VG.Proof.Rsa.X86_64.crtRd s₂) (VG.Proof.Rsa.X86_64.crtWr s₂)) :=
    VG.Proof.Rsa.X86_64.crt_pre (preF_of S₂.1) he₂ hargs₂ hdi₂ hsi₂ hdx₂ hcx₂ h8₂ h9₂
  have ga : ∀ i < 12, stackArg ((t₁.callEntry).withRegions (VG.Proof.Rsa.X86_64.crtRd s₁) (VG.Proof.Rsa.X86_64.crtWr s₁)) i =
      stackArg ((t₂.callEntry).withRegions (VG.Proof.Rsa.X86_64.crtRd s₂) (VG.Proof.Rsa.X86_64.crtWr s₂)) i := fun i hi => (g₁ i hi).trans (g₂ i hi).symm
  have hpub : crtContract.pub ((t₁.callEntry).withRegions (VG.Proof.Rsa.X86_64.crtRd s₁) (VG.Proof.Rsa.X86_64.crtWr s₁))
      ((t₂.callEntry).withRegions (VG.Proof.Rsa.X86_64.crtRd s₂) (VG.Proof.Rsa.X86_64.crtWr s₂)) :=
    ⟨VG.Proof.Rsa.X86_64.regs_eq (r₁.trans r₂.symm), ga 0 (by decide), ga 1 (by decide), ga 2 (by decide), ga 3 (by decide),
      ga 4 (by decide), ga 5 (by decide), ga 6 (by decide), ga 7 (by decide), ga 8 (by decide), ga 9 (by decide),
      ga 10 (by decide), ga 11 (by decide), n₁.trans n₂.symm⟩
  exact ⟨VG.Proof.Rsa.X86_64.crtRd s₁, VG.Proof.Rsa.X86_64.crtWr s₁, VG.Proof.Rsa.X86_64.crtRd s₂, VG.Proof.Rsa.X86_64.crtWr s₂, p₁, p₂, hpub, c₁, w₁, c₂, w₂,
    by rw [he₁.rsp, he₂.rsp, S₁.fb, S₂.fb]⟩

/-- What `vg_rsa_public_precompute`'s contract makes public. -/
theorem pc_view {a s t : State} (S : VG.Proof.Rsa.X86_64.Sib a s) (h : VG.Proof.Rsa.X86_64.J3 s t) :
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map
        (t.callEntry.withRegions [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩] [VG.Proof.Rsa.X86_64.preR s, scrR s]).gpr =
      [VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb a) oPre, BitVec.ofNat 64 (Spec.Rsa.precomputedWords (a.gpr .rcx).toNat), a.gpr .rdx, a.gpr .rcx,
        stackArg a 12, stackArg a 13, VG.Proof.Rsa.X86_64.fb a - 8] ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩] [VG.Proof.Rsa.X86_64.preR s, scrR s]).mem
      ((t.callEntry.withRegions [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩] [VG.Proof.Rsa.X86_64.preR s, scrR s]).gpr .rdx)
      ((t.callEntry.withRegions [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩] [VG.Proof.Rsa.X86_64.preR s, scrR s]).gpr .rcx).toNat =
      Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat := by
  obtain ⟨he, hdi, hsi, hdx, hcx, h8, h9⟩ := h
  have hp := preF_of S.1
  refine ⟨?_, ?_⟩
  · rw [VG.Proof.Rsa.X86_64.entry_regs, hdi, hsi, hdx, hcx, h8, h9, he.rsp, S.fb, S.gpr (r := .rcx) (by decide),
      S.gpr (r := .rdx) (by decide), S.arg (by decide), S.arg (by decide)]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), hdx, hcx]
    rw [he.entryBytes _ _ hp.dKn hp.dOn hp.dns.symm (by have := hp.wN; omega), S.n]

theorem pc_ct (M : Mont) (name : String) (hmx : (Precompute.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    RelCT isa (Two (VG.Proof.Rsa.X86_64.At VG.Proof.Rsa.X86_64.J3)) (.call name (Precompute.code M.mm)) fun _ _ => True := by
  refine RelCT.callEx (k := pcContract) (pcCode_correct M hmx) (pcCode_constantTime M)
    fun t₁ t₂ ⟨a, ⟨s₁, S₁, j₁⟩, ⟨s₂, S₂, j₂⟩⟩ => ?_
  obtain ⟨r₁, n₁⟩ := VG.Proof.Rsa.X86_64.pc_view S₁ j₁
  obtain ⟨r₂, n₂⟩ := VG.Proof.Rsa.X86_64.pc_view S₂ j₂
  obtain ⟨c₁, w₁⟩ := VG.Proof.Rsa.X86_64.pc_covers (preF_of S₁.1) j₁.1
  obtain ⟨c₂, w₂⟩ := VG.Proof.Rsa.X86_64.pc_covers (preF_of S₂.1) j₂.1
  obtain ⟨he₁, hdi₁, hsi₁, hdx₁, hcx₁, h8₁, h9₁⟩ := j₁
  obtain ⟨he₂, hdi₂, hsi₂, hdx₂, hcx₂, h8₂, h9₂⟩ := j₂
  exact ⟨_, _, _, _, VG.Proof.Rsa.X86_64.pc_pre (preF_of S₁.1) he₁ hdi₁ hsi₁ hdx₁ hcx₁ h8₁ h9₁,
    VG.Proof.Rsa.X86_64.pc_pre (preF_of S₂.1) he₂ hdi₂ hsi₂ hdx₂ hcx₂ h8₂ h9₂, ⟨VG.Proof.Rsa.X86_64.regs_eq (r₁.trans r₂.symm), n₁.trans n₂.symm⟩,
    c₁, w₁, c₂, w₂, by rw [he₁.rsp, he₂.rsp, S₁.fb, S₂.fb]⟩

/-- What `vg_rsa_public_precomputed_checked`'s contract makes public. -/
theorem pd_view {a s t : State} (S : VG.Proof.Rsa.X86_64.Sib a s) (h : VG.Proof.Rsa.X86_64.J5 s t) :
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map (t.callEntry.withRegions (VG.Proof.Rsa.X86_64.pdRd s) (VG.Proof.Rsa.X86_64.pdWr s)).gpr =
      [a.gpr .rdi, a.gpr .rcx, VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb a) oPre, BitVec.ofNat 64 (Spec.Rsa.precomputedWords (a.gpr .rcx).toNat),
        a.gpr .r8, a.gpr .r9, VG.Proof.Rsa.X86_64.fb a - 8] ∧
    stackArg (t.callEntry.withRegions (VG.Proof.Rsa.X86_64.pdRd s) (VG.Proof.Rsa.X86_64.pdWr s)) 0 = VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb a) VG.Impl.Rsa.X86_64.PrivChecked.oM ∧
    stackArg (t.callEntry.withRegions (VG.Proof.Rsa.X86_64.pdRd s) (VG.Proof.Rsa.X86_64.pdWr s)) 1 = a.gpr .rcx ∧
    stackArg (t.callEntry.withRegions (VG.Proof.Rsa.X86_64.pdRd s) (VG.Proof.Rsa.X86_64.pdWr s)) 2 = stackArg a 12 ∧
    stackArg (t.callEntry.withRegions (VG.Proof.Rsa.X86_64.pdRd s) (VG.Proof.Rsa.X86_64.pdWr s)) 3 = stackArg a 13 ∧
    Spec.Rsa.wordsAt (t.callEntry.withRegions (VG.Proof.Rsa.X86_64.pdRd s) (VG.Proof.Rsa.X86_64.pdWr s)).mem
      ((t.callEntry.withRegions (VG.Proof.Rsa.X86_64.pdRd s) (VG.Proof.Rsa.X86_64.pdWr s)).gpr .rdx)
      ((t.callEntry.withRegions (VG.Proof.Rsa.X86_64.pdRd s) (VG.Proof.Rsa.X86_64.pdWr s)).gpr .rcx).toNat =
      VG.Proof.Rsa.X86_64.preVal (Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat)
        (Spec.Rsa.precomputedWords (a.gpr .rcx).toNat) ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions (VG.Proof.Rsa.X86_64.pdRd s) (VG.Proof.Rsa.X86_64.pdWr s)).mem
      ((t.callEntry.withRegions (VG.Proof.Rsa.X86_64.pdRd s) (VG.Proof.Rsa.X86_64.pdWr s)).gpr .r8)
      ((t.callEntry.withRegions (VG.Proof.Rsa.X86_64.pdRd s) (VG.Proof.Rsa.X86_64.pdWr s)).gpr .r9).toNat =
      Spec.Rsa.bytesAt a.mem (a.gpr .r8) (a.gpr .r9).toNat := by
  obtain ⟨⟨he, hpw⟩, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9⟩ := h
  have hp := preF_of S.1
  have hk2 := hp.k2
  have hpwl := VG.Proof.Rsa.X86_64.preWords_le hp
  have hcxN : (BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat)).toNat =
      Spec.Rsa.precomputedWords (s.gpr .rcx).toNat := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have rcx := S.gpr (r := .rcx) (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [VG.Proof.Rsa.X86_64.entry_regs, hdi, hsi, hdx, hcx, h8, h9, he.rsp, S.fb, rcx, S.gpr (r := .rdi) (by decide),
      S.gpr (r := .r8) (by decide), S.gpr (r := .r9) (by decide)]
  · rw [VG.Proof.Rsa.X86_64.stackArg_entry he.rsp _ _ (by decide), ← S.fb]; exact hw0
  · rw [VG.Proof.Rsa.X86_64.stackArg_entry he.rsp _ _ (by decide), ← rcx]; exact hw1
  · rw [VG.Proof.Rsa.X86_64.stackArg_entry he.rsp _ _ (by decide), ← S.arg (by decide)]; exact hw2
  · rw [VG.Proof.Rsa.X86_64.stackArg_entry he.rsp _ _ (by decide), ← S.arg (by decide)]; exact hw3
  · simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), hdx, hcx, hcxN]
    rw [VG.Proof.Rsa.X86_64.entry_words he.rsp (show oPre + 8 * Spec.Rsa.precomputedWords (s.gpr .rcx).toNat ≤ frameBytes by
      unfold oPre frameBytes; omega), hpw, S.n, rcx]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), h8, h9]
    rw [he.entryBytes _ _ hp.dKe hp.dOe hp.des.symm (by have := hp.wE; omega), S.e]

theorem pd_ct (M : Mont) (name : String) (hmx : (Precomputed.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    RelCT isa (Two (VG.Proof.Rsa.X86_64.At VG.Proof.Rsa.X86_64.J5)) (.call name (Checked.precomputedChecked M.mm)) fun _ _ => True := by
  have hct : ConstantTime isa (⟨pdContract.pre, pdChkContract.post, pdContract.pub⟩ : Contract isa).pre
      (⟨pdContract.pre, pdChkContract.post, pdContract.pub⟩ : Contract isa).pub (Checked.precomputedChecked M.mm) :=
    precomputedChecked_constantTime M
  refine RelCT.callEx (k := ⟨pdContract.pre, pdChkContract.post, pdContract.pub⟩)
    (precomputedChecked_correct M hmx) hct fun t₁ t₂ ⟨a, ⟨s₁, S₁, j₁⟩, ⟨s₂, S₂, j₂⟩⟩ => ?_
  obtain ⟨r₁, a0₁, a1₁, a2₁, a3₁, w₁', e₁⟩ := VG.Proof.Rsa.X86_64.pd_view S₁ j₁
  obtain ⟨r₂, a0₂, a1₂, a2₂, a3₂, w₂', e₂⟩ := VG.Proof.Rsa.X86_64.pd_view S₂ j₂
  obtain ⟨c₁, w₁⟩ := VG.Proof.Rsa.X86_64.pd_covers (preF_of S₁.1) j₁.1.1
  obtain ⟨c₂, w₂⟩ := VG.Proof.Rsa.X86_64.pd_covers (preF_of S₂.1) j₂.1.1
  obtain ⟨⟨he₁, -⟩, hw0₁, hw1₁, hw2₁, hw3₁, hdi₁, hsi₁, hdx₁, hcx₁, h8₁, h9₁⟩ := j₁
  obtain ⟨⟨he₂, -⟩, hw0₂, hw1₂, hw2₂, hw3₂, hdi₂, hsi₂, hdx₂, hcx₂, h8₂, h9₂⟩ := j₂
  have p₁ : pdContract.pre (t₁.callEntry.withRegions (VG.Proof.Rsa.X86_64.pdRd s₁) (VG.Proof.Rsa.X86_64.pdWr s₁)) :=
    VG.Proof.Rsa.X86_64.pd_pre (preF_of S₁.1) he₁ hw0₁ hw1₁ hw2₁ hw3₁ hdi₁ hsi₁ hdx₁ hcx₁ h8₁ h9₁
  have p₂ : pdContract.pre (t₂.callEntry.withRegions (VG.Proof.Rsa.X86_64.pdRd s₂) (VG.Proof.Rsa.X86_64.pdWr s₂)) :=
    VG.Proof.Rsa.X86_64.pd_pre (preF_of S₂.1) he₂ hw0₂ hw1₂ hw2₂ hw3₂ hdi₂ hsi₂ hdx₂ hcx₂ h8₂ h9₂
  have hpub : pdContract.pub (t₁.callEntry.withRegions (VG.Proof.Rsa.X86_64.pdRd s₁) (VG.Proof.Rsa.X86_64.pdWr s₁))
      (t₂.callEntry.withRegions (VG.Proof.Rsa.X86_64.pdRd s₂) (VG.Proof.Rsa.X86_64.pdWr s₂)) :=
    ⟨VG.Proof.Rsa.X86_64.regs_eq (r₁.trans r₂.symm), a0₁.trans a0₂.symm, a1₁.trans a1₂.symm, a2₁.trans a2₂.symm,
      a3₁.trans a3₂.symm, w₁'.trans w₂'.symm, e₁.trans e₂.symm⟩
  exact ⟨VG.Proof.Rsa.X86_64.pdRd s₁, VG.Proof.Rsa.X86_64.pdWr s₁, VG.Proof.Rsa.X86_64.pdRd s₂, VG.Proof.Rsa.X86_64.pdWr s₂, p₁, p₂, hpub, Covers.append_left c₁ w₁.right, w₁,
    Covers.append_left c₂ w₂.right, w₂, by rw [he₁.rsp, he₂.rsp, S₁.fb, S₂.fb]⟩

/-! ## The pieces -/

theorem crtArgs_two : RelCT isa (Two (VG.Proof.Rsa.X86_64.At VG.Proof.Rsa.X86_64.J0)) (.block crtArgs) (Two (VG.Proof.Rsa.X86_64.At VG.Proof.Rsa.X86_64.J1)) :=
  two_piece [.rsp] (fun _ _ _ h₁ h₂ r hr => by
      rw [List.mem_singleton.mp hr]
      exact VG.Proof.Rsa.X86_64.pin VG.Proof.Rsa.X86_64.fb (fun s t h => by rw [h]; rfl) (fun _ _ h => h.fb) h₁ h₂) (by taint_decide)
    fun _ t ⟨s, S, ht⟩ => by
      subst ht
      exact WP.mono (crtArgs_ok (preF_of S.1)) fun _ ⟨he, _, hargs, hdi, hsi, hdx, hcx, h8, h9⟩ =>
        ⟨s, S, he, hargs, hdi, hsi, hdx, hcx, h8, h9⟩

theorem crtCall_two (v : CrtImpl) : RelCT isa (Two (VG.Proof.Rsa.X86_64.At VG.Proof.Rsa.X86_64.J1)) (.call v.name v.code) (Two (VG.Proof.Rsa.X86_64.At VG.Proof.Rsa.X86_64.J2)) :=
  two_post (VG.Proof.Rsa.X86_64.crt_ct v) fun _ _ ⟨s, S, he, hargs, hdi, hsi, hdx, hcx, h8, h9⟩ =>
    WP.mono (VG.Proof.Rsa.X86_64.crt_call v (preF_of S.1) he hargs hdi hsi hdx hcx h8 h9) fun _ h => ⟨s, S, h.1⟩

theorem pcArgs_two : RelCT isa (Two (VG.Proof.Rsa.X86_64.At VG.Proof.Rsa.X86_64.J2)) (.block pcArgs) (Two (VG.Proof.Rsa.X86_64.At VG.Proof.Rsa.X86_64.J3)) :=
  two_piece [.rsp] (VG.Proof.Rsa.X86_64.pins_rsp fun _ _ h => h) (by taint_decide)
    fun _ _ ⟨s, S, he⟩ => WP.mono (VG.Proof.Rsa.X86_64.pcArgs_ok (preF_of S.1) he) fun _ ⟨he', _, hdi, hsi, hdx, hcx, h8, h9⟩ =>
      ⟨s, S, he', hdi, hsi, hdx, hcx, h8, h9⟩

theorem pcCall_two (M : Mont) (name : String) (hmx : (Precompute.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (hsp : NoSp (Precompute.code M.mm)) (hd : (Precompute.code M.mm).depth = 0) :
    RelCT isa (Two (VG.Proof.Rsa.X86_64.At VG.Proof.Rsa.X86_64.J3)) (.call name (Precompute.code M.mm)) (Two (VG.Proof.Rsa.X86_64.At VG.Proof.Rsa.X86_64.J4)) :=
  two_post (VG.Proof.Rsa.X86_64.pc_ct M name hmx) fun _ _ ⟨s, S, he, hdi, hsi, hdx, hcx, h8, h9⟩ =>
    WP.mono (VG.Proof.Rsa.X86_64.pc_call M name hmx hsp hd (preF_of S.1) he hdi hsi hdx hcx h8 h9) fun _ ⟨he', hpc, _⟩ =>
      ⟨s, S, he', by
        cases hq : Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) <;>
          simp only [hq] at hpc <;> simp only [VG.Proof.Rsa.X86_64.preVal, hq] <;> exact hpc.2⟩

theorem pdArgs_two : RelCT isa (Two (VG.Proof.Rsa.X86_64.At VG.Proof.Rsa.X86_64.J4)) (.block pdArgs) (Two (VG.Proof.Rsa.X86_64.At VG.Proof.Rsa.X86_64.J5)) :=
  two_piece [.rsp] (VG.Proof.Rsa.X86_64.pins_rsp fun _ _ h => h.1) (by taint_decide)
    fun _ t ⟨s, S, he, hpw⟩ => by
      have hp := preF_of S.1
      have hpwl := VG.Proof.Rsa.X86_64.preWords_le hp
      refine WP.mono (VG.Proof.Rsa.X86_64.pdArgs_ok hp he) fun t₃ ⟨he₃, hm₃, hdi₃, hsi₃, hdx₃, hcx₃, h8₃, h9₃⟩ => ?_
      have hw : ∀ {d : Nat}, d < 4 → VG.Proof.Bignum.X86_64.word t₃.mem (VG.Proof.Rsa.X86_64.fb s) (8 * d) =
          [VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) VG.Impl.Rsa.X86_64.PrivChecked.oM, s.gpr .rcx, stackArg s 12, stackArg s 13].getD d 0 := fun {d} hd => by
        rw [hm₃]
        rcases (show d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 by omega) with rfl | rfl | rfl | rfl
        · simp (disch := decide) only [word_wo, VG.Proof.Rsa.X86_64.word_self0, Nat.mul_zero]
          rfl
        · simp (disch := decide) only [word_wo, VG.Proof.Bignum.X86_64.word_writeW_self, Nat.mul_one]; rfl
        · simp (disch := decide) only [word_wo, VG.Proof.Bignum.X86_64.word_writeW_self]; rfl
        · simp (disch := decide) only [VG.Proof.Bignum.X86_64.word_writeW_self]; rfl
      have hpre : Spec.Rsa.wordsAt t₃.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) oPre) (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) =
          Spec.Rsa.wordsAt t.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) oPre) (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) := by
        rw [hm₃]
        simp (disch := first | decide | (simp only [oPre, oR3]; omega)) only [VG.Proof.Rsa.X86_64.words_wo, VG.Proof.Rsa.X86_64.words_wo0]
      exact ⟨s, S, ⟨he₃, hpre.trans hpw⟩, hw (d := 0) (by decide), hw (d := 1) (by decide),
        hw (d := 2) (by decide), hw (d := 3) (by decide), hdi₃, hsi₃, hdx₃, hcx₃, h8₃, h9₃⟩

theorem pdCall_two (M : Mont) (name : String) (hmx : (Precomputed.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (hsp : NoSp (Checked.precomputedChecked M.mm)) (hd : (Checked.precomputedChecked M.mm).depth = 0) :
    RelCT isa (Two (VG.Proof.Rsa.X86_64.At VG.Proof.Rsa.X86_64.J5)) (.call name (Checked.precomputedChecked M.mm)) (Two (VG.Proof.Rsa.X86_64.At VG.Proof.Rsa.X86_64.J2)) :=
  two_post (VG.Proof.Rsa.X86_64.pd_ct M name hmx) fun _ _ ⟨s, S, ⟨he, _⟩, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9⟩ =>
    WP.mono (VG.Proof.Rsa.X86_64.pd_call M name hmx hsp hd (preF_of S.1) he hw0 hw1 hw2 hw3 hdi hsi hdx hcx h8 h9) fun _ h => ⟨s, S, h.1⟩

theorem cmpArgs_two : RelCT isa (Two (VG.Proof.Rsa.X86_64.At VG.Proof.Rsa.X86_64.J2)) (.block cmpArgs) (Two (VG.Proof.Rsa.X86_64.At VG.Proof.Rsa.X86_64.J7)) :=
  two_piece [.rsp] (VG.Proof.Rsa.X86_64.pins_rsp fun _ _ h => h) (by taint_decide)
    fun _ _ ⟨s, S, he⟩ => WP.mono (VG.Proof.Rsa.X86_64.cmpArgs_ok (preF_of S.1) he) fun _ ⟨_, _, hdi, hsi, hcx, h10, _, k⟩ =>
      ⟨s, S, (k.gpr (by decide)).trans he.rsp, hdi, hsi, hcx, h10⟩

theorem tail_eq : seqs PrivChecked.tail =
    .seq (.block cmpArgs) (.seq cmpLoop (.seq (.block masks) (.seq releaseLoop (.block [.mov .rax (.reg .r11)])))) :=
  rfl

/-- The comparison and the release, from the registers `cmpArgs` sets. -/
theorem rest_ct : RelCT isa (Two (VG.Proof.Rsa.X86_64.At VG.Proof.Rsa.X86_64.J7))
    (.seq cmpLoop (.seq (.block masks) (.seq releaseLoop (.block [.mov .rax (.reg .r11)])))) fun _ _ => True :=
  two_taint [.rdi, .rsi, .rcx, .r10, .rsp] (fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact VG.Proof.Rsa.X86_64.pin (fun s => s.gpr .rdi) (fun _ _ h => h.2.1) (fun _ _ S => S.gpr (by decide)) h₁ h₂
    · exact VG.Proof.Rsa.X86_64.pin (fun s => stackArg s 0) (fun _ _ h => h.2.2.1) (fun _ _ S => S.arg (by decide)) h₁ h₂
    · exact VG.Proof.Rsa.X86_64.pin (fun s => s.gpr .rcx) (fun _ _ h => h.2.2.2.1) (fun _ _ S => S.gpr (by decide)) h₁ h₂
    · exact VG.Proof.Rsa.X86_64.pin (fun _ => BitVec.ofNat 64 0) (fun _ _ h => h.2.2.2.2) (fun _ _ _ => rfl) h₁ h₂
    · exact VG.Proof.Rsa.X86_64.pin VG.Proof.Rsa.X86_64.fb (fun _ _ h => h.1) (fun _ _ S => S.fb) h₁ h₂) (by taint_decide)

theorem body_ct (v : CrtImpl) (pcName pdName : String) :
    RelCT isa (Two (VG.Proof.Rsa.X86_64.At VG.Proof.Rsa.X86_64.J0)) (VG.Impl.Rsa.X86_64.PrivChecked.body v.name v.code pcName (Precompute.code v.mont.mm) pdName
      (Checked.precomputedChecked v.mont.mm)) fun _ _ => True := by
  rw [VG.Proof.Rsa.X86_64.body_eq, VG.Proof.Rsa.X86_64.check_eq, VG.Proof.Rsa.X86_64.tail_eq]
  exact RelCT.seq VG.Proof.Rsa.X86_64.crtArgs_two (RelCT.seq (VG.Proof.Rsa.X86_64.crtCall_two v) (RelCT.seq VG.Proof.Rsa.X86_64.pcArgs_two
    (RelCT.seq (VG.Proof.Rsa.X86_64.pcCall_two v.mont pcName v.pcMx v.pcNosp v.pcDepth) (RelCT.seq VG.Proof.Rsa.X86_64.pdArgs_two
      (RelCT.seq (VG.Proof.Rsa.X86_64.pdCall_two v.mont pdName v.pdMx v.pdNosp v.pdDepth) (RelCT.seq VG.Proof.Rsa.X86_64.cmpArgs_two VG.Proof.Rsa.X86_64.rest_ct))))))

/-! ## The frame -/

theorem alloc_push {s s₁ : State} (h : isa.push (.alloc frameBytes) s = some s₁) : s₁ = allocState frameBytes s := by
  simp only [isa, push] at h
  split at h
  · cases h; rfl
  · cases h

/-- A frame of `frameBytes` bytes leaks what its body does. -/
theorem relCT_alloc {body : Prog isa} {P R : State → State → Prop}
    (hb : RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = allocState frameBytes s₁ ∧ b = allocState frameBytes s₂)
      body R) :
    RelCT isa P (.frame (.alloc frameBytes) body (.free frameBytes)) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | frame p₁ b₁ q₁ =>
    cases e₂ with
    | frame p₂ b₂ q₂ =>
      obtain rfl := VG.Proof.Rsa.X86_64.alloc_push p₁
      obtain rfl := VG.Proof.Rsa.X86_64.alloc_push p₂
      obtain ⟨rfl, -⟩ := hb _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ b₁ b₂
      exact ⟨rfl, trivial⟩

theorem code_constantTime (v : CrtImpl) (pcName pdName : String) :
    ConstantTime isa chkContract.pre chkContract.pub (VG.Impl.Rsa.X86_64.PrivChecked.code v.name v.code pcName (Precompute.code v.mont.mm) pdName
      (Checked.precomputedChecked v.mont.mm)) :=
  RelCT.constantTime (VG.Proof.Rsa.X86_64.relCT_alloc ((VG.Proof.Rsa.X86_64.body_ct v pcName pdName).mono
    (fun _ _ ⟨s₁, s₂, ⟨h₁, h₂, hpub⟩, e₁, e₂⟩ => ⟨s₁, ⟨s₁, ⟨h₁, VG.Proof.Rsa.X86_64.pub_refl s₁⟩, e₁⟩, ⟨s₂, ⟨h₂, hpub⟩, e₂⟩⟩)
    fun _ _ h => h))

/-! ## `Verified` -/

/-- `vg_rsa_private_checked`, calling the implementation `v` of the CRT and
the public operation of the same Montgomery multiplication, meets the shared
contract. -/
theorem code_verified (v : CrtImpl) (pcName pdName : String) :
    Verified target (VG.Impl.Rsa.X86_64.PrivChecked.code v.name v.code pcName (Precompute.code v.mont.mm) pdName
      (Checked.precomputedChecked v.mont.mm)) (Spec.Rsa.privateCheckedContract abi stackBytes) :=
  have hct : ConstantTime isa chkContract.pre chkContract.pub (VG.Impl.Rsa.X86_64.PrivChecked.code v.name v.code pcName
      (Precompute.code v.mont.mm) pdName (Checked.precomputedChecked v.mont.mm)) := VG.Proof.Rsa.X86_64.code_constantTime v pcName pdName
  Verified.of_correct (k := chkContract) (VG.Proof.Rsa.X86_64.code_correct v pcName pdName) hct private_checked_implies

/-- It writes `rsp` only in its frame's push and pop. -/
theorem code_spSafe (v : CrtImpl) (pcName pdName : String) :
    (VG.Impl.Rsa.X86_64.PrivChecked.code v.name v.code pcName (Precompute.code v.mont.mm) pdName (Checked.precomputedChecked v.mont.mm)).all
      (fun i => !isa.writesSp i) = true := by
  simp only [VG.Impl.Rsa.X86_64.PrivChecked.code, VG.Proof.Rsa.X86_64.body_eq, VG.Proof.Rsa.X86_64.check_eq, VG.Proof.Rsa.X86_64.tail_eq, Code.all, v.spSafe, v.pcSpSafe, v.pdSpSafe,
    Bool.true_and]
  decide +kernel

end VG.Proof.Rsa.X86_64

end
