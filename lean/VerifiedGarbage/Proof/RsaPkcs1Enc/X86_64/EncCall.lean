import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncPre

/-!
# RSAES-PKCS1-v1_5 encryption on x86-64: the call of `vg_rsa_public_checked`

The call's arguments from the slots (`callArgs_run`), its precondition
with the stack arguments in the frame (`pub_pre`), and what it leaves
(`pub_call`): `out` holds `vg_rsa_public_checked`'s result for `EM`, and the
frame its slots and `EM`.
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Encrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-! ## The arguments -/

theorem callArgs_run {s t : State} (hp : EPre s) (h : PreCall s t) :
    WP isa (.block callArgs) t fun t' => t'.mem = t.mem ∧ t'.gpr .rdi = s.gpr .rdi ∧ t'.gpr .rsi = s.gpr .rcx ∧
      t'.gpr .rdx = s.gpr .rdx ∧ t'.gpr .rcx = s.gpr .rcx ∧ t'.gpr .r8 = s.gpr .r8 ∧ t'.gpr .r9 = s.gpr .r9 ∧
      Keep [.rdi, .rsi, .rdx, .rcx, .r8, .r9] t t' := by
  have hF := fb_toNat hp
  have hs : Scr t (fb s) frameBytes := Scr.of_mem (by rw [h.wr]; exact List.mem_cons_self ..)
    (by have := hF.1; omega)
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8, .r9] (c := .block callArgs) (Q := fun t' =>
      t'.mem = t.mem ∧ t'.gpr .rdi = s.gpr .rdi ∧ t'.gpr .rsi = s.gpr .rcx ∧ t'.gpr .rdx = s.gpr .rdx ∧
      t'.gpr .rcx = s.gpr .rcx ∧ t'.gpr .r8 = s.gpr .r8 ∧ t'.gpr .r9 = s.gpr .r9) ?_ rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2, k⟩
  xrun [callArgs, ea_sp, h.rsp, hs.ld (d := oOut) (by decide), hs.ld (d := oK) (by decide),
    hs.ld (d := oN) (by decide), hs.ld (d := oE) (by decide), hs.ld (d := oEl) (by decide), h.slots.sOut,
    h.slots.sK, h.slots.sN, h.slots.sE, h.slots.sEl]
  done

/-! ## The callee's view -/

/-- The base of the stack the function uses. -/
abbrev kb (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 encStack

theorem fb_sub8 (s : State) : fb s - 8 = kb s := by
  rw [fb_eq]; exact BitVec.add_sub_cancel _ _

theorem kb_toNat {s : State} (hp : EPre s) : (kb s).toNat + encStack + 56 ≤ 2 ^ 64 ∧
    (kb s).toNat + encStack = (s.gpr .rsp).toNat := by
  have := hp.sp1; have := hp.sp2
  simp only [kb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold encStack frameBytes at *; omega

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

/-- What `vg_rsa_public_checked` reads: `n`, `e`, `EM` and its stack
arguments. -/
def pubRd (s : State) : List Region :=
  [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨off (fb s) oEM, (s.gpr .rcx).toNat⟩, ⟨fb s, 32⟩]

/-- What it writes: `out` and the working space. -/
def pubWr (s : State) : List Region :=
  [⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩, ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩]

theorem pub_pre {s t : State} (hp : EPre s) (h : PreCall s t) (hdi : t.gpr .rdi = s.gpr .rdi)
    (hsi : t.gpr .rsi = s.gpr .rcx) (hdx : t.gpr .rdx = s.gpr .rdx) (hcx : t.gpr .rcx = s.gpr .rcx)
    (h8 : t.gpr .r8 = s.gpr .r8) (h9 : t.gpr .r9 = s.gpr .r9) :
    pubChkK.pre (t.callEntry.withRegions (pubRd s) (pubWr s)) := by
  have e0 : stackArg (t.callEntry.withRegions (pubRd s) (pubWr s)) 0 = off (fb s) oEM := by
    rw [stackArg_entry h.rsp _ _ (by decide)]
    have := h.slots.a0; simp only [Bignum.word, off_zero, Nat.mul_zero]; exact this
  have e1 : stackArg (t.callEntry.withRegions (pubRd s) (pubWr s)) 1 = s.gpr .rcx := by
    rw [stackArg_entry h.rsp _ _ (by decide)]; exact h.slots.a1
  have e2 : stackArg (t.callEntry.withRegions (pubRd s) (pubWr s)) 2 = stackArg s 4 := by
    rw [stackArg_entry h.rsp _ _ (by decide)]; exact h.slots.a2
  have e3 : stackArg (t.callEntry.withRegions (pubRd s) (pubWr s)) 3 = stackArg s 5 := by
    rw [stackArg_entry h.rsp _ _ (by decide)]; exact h.slots.a3
  simp only [pubChkK, pubContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_rsp, State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), hdi, hsi, hdx, hcx, h8, h9, h.rsp,
    stackArgAddr_entry h.rsp, e0, e1, e2, e3, fb_sub8]
  have ⟨hK1, hK2⟩ := kb_toNat hp
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hsi' := hp.hsi
  have e5 : encStack = 1120 := rfl
  have e6 : oEM = 80 := rfl
  have e7 : frameBytes = 1112 := rfl
  have hfb : fb s = off (kb s) 8 := fb_eq s
  have sM : Region.Sub ⟨off (fb s) oEM, (s.gpr .rcx).toNat⟩ (stkR s) := frame_sub s (by omega)
  have sA : Region.Sub ⟨fb s, 32⟩ (stkR s) := by
    have := frame_sub s (d := 0) (n := 32) (by decide); simpa only [off, BitVec.add_zero] using this
  have sR : Region.Sub ⟨kb s, 8⟩ (stkR s) := Region.sub_prefix (by decide)
  have dMA : (⟨off (fb s) oEM, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨fb s, 32⟩ :=
    Offset.disjoint_base _ (by decide) (by omega)
  have dRM : (⟨kb s, 8⟩ : Region).Disjoint ⟨off (fb s) oEM, (s.gpr .rcx).toNat⟩ := by
    rw [hfb, off_off]; exact Offset.base_disjoint _ (by decide) (by omega)
  have dRA : (⟨kb s, 8⟩ : Region).Disjoint ⟨fb s, 32⟩ := by
    rw [hfb]; exact Offset.base_disjoint _ (by decide) (by omega)
  have wM : (off (fb s) oEM).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 := by
    rw [hfb, off_off]; simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have dKo : (stkR s).Disjoint ⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ := by have := hp.dKo; rwa [hsi'] at this
  have dOn : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ := by
    have := hp.dOn; rwa [hsi'] at this
  have dOe : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩ := by
    have := hp.dOe; rwa [hsi'] at this
  have dOs : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩ := by
    have := hp.dOs; rwa [hsi'] at this
  have wO : (s.gpr .rdi).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 := by have := hp.wO; omega
  refine ⟨by omega, rfl, rfl, dOn, dOe, (dKo.sub_left sM).symm, dOs, (dKo.sub_left sA).symm, hp.dns, hp.des,
    (hp.dKs.sub_left sM), (hp.dKs.sub_left sA).symm, dKo.sub_left sR, hp.dKn.sub_left sR, hp.dKe.sub_left sR,
    dRM, hp.dKs.sub_left sR, dRA, wO, hp.wN, hp.wE, wM, hp.wS, ⟨hk1, hk2⟩, trivial, trivial, hp.L1, hp.L2,
    hp.hsl⟩

theorem pub_covers {s t : State} (hp : EPre s) (h : PreCall s t) :
    Covers (pubRd s ++ pubWr s) (t.rd ++ t.wr) ∧ Covers (pubWr s) t.wr := by
  have hk2 := hp.k2
  have hsi := hp.hsi
  have e2 : oEM = 80 := rfl
  have e3 : frameBytes = 1112 := rfl
  have hfr : (⟨fb s, frameBytes⟩ : Region) ∈ t.wr := by rw [h.wr]; exact List.mem_cons_self ..
  have hscr : (⟨stackArg s 4, (stackArg s 5).toNat * 8⟩ : Region) ∈ t.wr := by rw [h.wr, hp.hwr]; simp
  have hout : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region) ∈ t.wr := by rw [h.wr, hp.hwr]; simp
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have cw : Covers (pubWr s) t.wr := Covers.of_sub fun r hr => by
    simp only [pubWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hout, 0, z _, by dsimp only; omega⟩
    · exact ⟨_, hscr, 0, z _, by dsimp only; omega⟩
  refine ⟨Covers.append_left (Covers.of_sub fun r hr => ?_) cw.right, cw⟩
  have hrd : ∀ x, x ∈ s.rd → x ∈ t.rd ++ t.wr := fun x hx => List.mem_append_left _ (by rw [h.rd]; exact hx)
  simp only [pubRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, hrd ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hrd ⟨s.gpr .r8, (s.gpr .r9).toNat⟩ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, List.mem_append_right _ hfr, oEM, rfl, by dsimp only; omega⟩
  · exact ⟨_, List.mem_append_right _ hfr, 0, z _, by dsimp only; omega⟩

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

/-- The modulus and the exponent of an entry state. -/
abbrev nB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat
abbrev eB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat

/-- After the call. -/
structure PostCall (s t : State) : Prop where
  rsp : t.gpr .rsp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  mem : Frame [stkR s, outR s, scrR s] s.mem t.mem
  slots : Slots s t.mem
  sZ : word t.mem (fb s) oZ = zmask (psB s)
  res : Spec.Rsa.written t.mem (s.gpr .rdi) (kOf s) ((t.gpr .rax).setWidth 32)
    (Spec.Rsa.publicOpChecked (nB s) (eB s) (Spec.RsaPkcs1Enc.encode (msgB s) (psB s)))

/-- The return address a call from the frame stores. -/
theorem callEntry_frame {s t : State} (hsp : t.gpr .rsp = fb s) : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
  rw [State.callEntry_mem, hsp]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))

theorem below_eq (s : State) : below (fb s) 8 = ⟨kb s, 8⟩ := by
  simp only [below]; rw [← fb_sub8]; rfl

/-- Words of the frame below `EM` are apart from what the call writes. -/
theorem slot_apart {s : State} (hp : EPre s) {d n : Nat} (hd : d + n ≤ frameBytes) :
    ∀ r ∈ pubWr s ++ [below (fb s) 8], (⟨off (fb s) d, n⟩ : Region).Disjoint r := by
  have ⟨hK1, _⟩ := kb_toNat hp
  have e1 : encStack = 1120 := rfl
  have e3 : frameBytes = 1112 := rfl
  have hsi := hp.hsi
  intro r hr
  simp only [pubWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · have := hp.dKo; rw [hsi] at this; exact this.sub_left (frame_sub s hd)
  · exact hp.dKs.sub_left (frame_sub s hd)
  · rw [below_eq, fb_eq, off_off]
    exact Offset.disjoint_base _ (by omega) (by omega)

theorem pub_call (v : PubImpl) {s t : State} (hp : EPre s) (h : PreCall s t) (hdi : t.gpr .rdi = s.gpr .rdi)
    (hsi : t.gpr .rsi = s.gpr .rcx) (hdx : t.gpr .rdx = s.gpr .rdx) (hcx : t.gpr .rcx = s.gpr .rcx)
    (h8 : t.gpr .r8 = s.gpr .r8) (h9 : t.gpr .r9 = s.gpr .r9) :
    WP isa (.call v.name v.code) t fun t' => PostCall s t' ∧ (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧
      t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 := by
  obtain ⟨hc, hw⟩ := pub_covers hp h
  refine WP.call_mx (k := pubChkK) v.ok v.nosp (by rw [v.depth]; decide)
    (pub_pre hp h hdi hsi hdx hcx h8 h9) hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ hmx
  rw [v.depth, h.rsp] at hf
  have hk2 := hp.k2
  have hsi' := hp.hsi
  have e6 : oEM = 80 := rfl
  have e7 : frameBytes = 1112 := rfl
  have hfE : Frame [stkR s, outR s, scrR s] s.mem t.callEntry.mem :=
    frame_call (frame_of_outside h.out) (callEntry_frame h.rsp) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inl (ret_sub s)
  have hE0 : stackArg (t.callEntry.withRegions (pubRd s) (pubWr s)) 0 = off (fb s) oEM := by
    rw [stackArg_entry h.rsp _ _ (by decide)]
    have := h.slots.a0; simp only [Bignum.word, off_zero, Nat.mul_zero]; exact this
  have hem : Spec.Rsa.bytesAt t.callEntry.mem (off (fb s) oEM) (s.gpr .rcx).toNat =
      Spec.RsaPkcs1Enc.encode (msgB s) (psB s) := by
    rw [← h.em]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => (callEntry_frame h.rsp).bytes (R := ⟨off (fb s) oEM, (s.gpr .rcx).toNat⟩)
      (fun r hr => ?_) (by show (s.gpr .rcx).toNat ≤ 2 ^ 64; omega) (List.mem_range.mp hi)
    rw [List.mem_singleton.mp hr]
    exact slot_apart hp (d := oEM) (n := (s.gpr .rcx).toNat) (by omega) _
      (List.mem_append_right _ (List.mem_singleton_self _))
  simp only [pubChkK, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), hdi, hdx, hcx, h8, h9, hE0, hem, hm₂,
    hg₂ .rax (by decide)] at hpost
  rw [bytes_of_frame hfE hp.dKn (by have := hp.dOn; rw [outR]; exact this) hp.dns.symm (by have := hp.wN; omega),
    bytes_of_frame hfE hp.dKe (by have := hp.dOe; rw [outR]; exact this) hp.des.symm (by have := hp.wE; omega)]
    at hpost
  have hkeep : ∀ {d : Nat}, d + 8 ≤ oEM → word s'.mem (fb s) d = word t.mem (fb s) d := fun hd =>
    hf.readW (Region.contains_self _ _) (slot_apart hp (by omega)) (by decide)
  have hkeep0 : s'.mem.readW (fb s) 64 = t.mem.readW (fb s) 64 := by
    have := hkeep (d := 0) (by decide); simp only [Bignum.word, off_zero] at this; exact this
  refine ⟨⟨(hcs .rsp (by decide)).trans h.rsp, hrd.trans h.rd, hwr.trans h.wr,
    frame_call (frame_of_outside h.out) hf fun r hr => ?_,
    ⟨(hkeep (by decide)).trans h.slots.sOut, (hkeep (by decide)).trans h.slots.sN,
      (hkeep (by decide)).trans h.slots.sK, (hkeep (by decide)).trans h.slots.sE,
      (hkeep (by decide)).trans h.slots.sEl, hkeep0.trans h.slots.a0, (hkeep (by decide)).trans h.slots.a1,
      (hkeep (by decide)).trans h.slots.a2, (hkeep (by decide)).trans h.slots.a3⟩,
    (hkeep (by decide)).trans h.sZ, hpost⟩, hcs, hmx⟩
  simp only [pubWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact .inr (.inl (by rw [outR, hsi']; exact sub_refl _))
  · exact .inr (.inr (sub_refl _))
  · exact .inl (ret_sub s)

end VG.Proof.RsaPkcs1Enc.X86_64
