module

public import VerifiedGarbage.Proof.Rsa.X86_64.PrivCrt
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivPcFrame
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCode

/-!
# `vg_rsa_private_checked_precomputed` on x86-64: the call of the CRT

`vg_rsa_private_crt_precomputed` runs with the stack arguments the frame
holds at `rsp`, `pre` among them, writing `M` at `oM` (`crtPc_pre`), and
returns with `M` written, if `pre` holds the key's values, and the frame's
slots kept (`crtPc_call`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.PrivCheckedPc
open VG.Impl.Rsa.X86_64.PrivChecked (sp lea oM)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- The return address of a call from the frame. -/
abbrev kbP (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 (frameBytes + 8)

theorem fbP_sub8 (s : State) : fbP s - 8 = kbP s := by
  simp only [fbP, kbP, BitVec.sub_sub]; rfl

theorem fbP_kbP (s : State) : fbP s = kbP s + BitVec.ofNat 64 8 := by
  rw [← fbP_sub8]; exact (BitVec.sub_add_cancel _ _).symm

theorem fbP_off (s : State) (d : Nat) : off (fbP s) d = kbP s + BitVec.ofNat 64 (8 + d) := by
  rw [fbP_kbP, off, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem kbP_toNat {s : State} (hp : PreFPc s) : (kbP s).toNat + (frameBytes + 8) + 8 + 128 ≤ 2 ^ 64 ∧
    (kbP s).toNat + (frameBytes + 8) = (s.gpr .rsp).toNat ∧ 8 ≤ (kbP s).toNat := by
  have := hp.sp1; have := hp.sp2
  simp only [kbP, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold stackBytesPc frameBytes at *; omega

/-- The stack argument `i` of a function called from the frame is the
frame's word `8 i`. -/
theorem stackArgP_entry {s t : State} (hsp : t.gpr .rsp = fbP s) (rd wr : List Region) {i : Nat} (hi : i < 400) :
    stackArg (t.callEntry.withRegions rd wr) i = word t.mem (fbP s) (8 * i) := by
  have hsep := Offset.sep (kbP s) (d := 8 * (i + 1)) (n := 8) (e := 0) (k := 8) (by omega) (by omega) (by omega)
  rw [show kbP s + BitVec.ofNat 64 0 = kbP s from BitVec.add_zero _] at hsep
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_mem, hsp, fbP_sub8]
  rw [Mem.readW_writeW_sep hsep (by decide)]
  show _ = t.mem.readW (off (fbP s) (8 * i)) 64
  rw [fbP_kbP, ← off, off_off, show 8 + 8 * i = 8 * (i + 1) by omega]

theorem stackArgAddrP_entry {s t : State} (hsp : t.gpr .rsp = fbP s) (rd wr : List Region) :
    stackArgAddr (t.callEntry.withRegions rd wr) 0 = fbP s := by
  simp only [stackArgAddr, State.withRegions_gpr, State.callEntry_rsp, hsp, fbP_sub8]
  rw [fbP_kbP]

/-- What the CRT reads. -/
def crtPcRd (s : State) : List Region :=
  [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨stackArg s 0, (s.gpr .rcx).toNat⟩, ⟨stackArg s 2, (stackArg s 3).toNat⟩,
    ⟨stackArg s 4, (stackArg s 5).toNat⟩, ⟨stackArg s 6, (stackArg s 7).toNat⟩,
    ⟨stackArg s 8, (stackArg s 9).toNat⟩, ⟨stackArg s 10, (stackArg s 11).toNat⟩,
    ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩, ⟨fbP s, 112⟩]

/-- What the CRT writes: `M` and the working space. -/
def crtPcWr (s : State) : List Region :=
  [⟨off (fbP s) oM, (s.gpr .rcx).toNat⟩, ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩]

theorem crtPc_pre {s t : State} (hp : PreFPc s) (he : EnvP s t)
    (hargs : ∀ i < 14, word t.mem (fbP s) (8 * i) = stackArg s (i + 2)) (hdi : t.gpr .rdi = off (fbP s) oM)
    (hsi : t.gpr .rsi = s.gpr .rcx) (hdx : t.gpr .rdx = s.gpr .rdx) (hcx : t.gpr .rcx = s.gpr .rcx)
    (h8 : t.gpr .r8 = stackArg s 0) (h9 : t.gpr .r9 = s.gpr .rcx) :
    crtPcContract.pre (t.callEntry.withRegions (crtPcRd s) (crtPcWr s)) := by
  have hE : ∀ i < 14, stackArg (t.callEntry.withRegions (crtPcRd s) (crtPcWr s)) i = stackArg s (i + 2) :=
    fun i hi => (stackArgP_entry he.rsp _ _ (by omega)).trans (hargs i hi)
  simp only [crtPcContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.callEntry_rsp,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
    hdi, hsi, hdx, hcx, h8, h9, he.rsp, stackArgAddrP_entry he.rsp, hE 0 (by decide), hE 1 (by decide),
    hE 2 (by decide), hE 3 (by decide), hE 4 (by decide), hE 5 (by decide), hE 6 (by decide), hE 7 (by decide),
    hE 8 (by decide), hE 9 (by decide), hE 10 (by decide), hE 11 (by decide), hE 12 (by decide),
    hE 13 (by decide), Nat.reduceAdd, fbP_sub8]
  have ⟨hK1, hK2, _⟩ := kbP_toNat hp
  have e1 : stackBytesPc = 1208 := rfl
  have e2 : oM = 160 := rfl
  have e3 : frameBytes = 1192 := rfl
  have hk1 := hp.k1
  have hk2 := hp.k2
  have sM : Region.Sub ⟨off (fbP s) oM, (s.gpr .rcx).toNat⟩ (stkRP s) := frameP_sub s (by unfold oM frameBytes; omega)
  have sA : Region.Sub ⟨fbP s, 112⟩ (stkRP s) := by
    have := frameP_sub s (d := 0) (n := 112) (by decide); simpa only [off, BitVec.add_zero] using this
  have sR : Region.Sub ⟨kbP s, 8⟩ (stkRP s) := by
    have := retP_sub s; rwa [show below (fbP s) 8 = ⟨kbP s, 8⟩ by simp only [below]; rw [← fbP_sub8]; rfl] at this
  have dMA : (⟨off (fbP s) oM, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨fbP s, 112⟩ :=
    Offset.disjoint_base _ (by decide) (by omega)
  have hfb : fbP s = kbP s + BitVec.ofNat 64 8 := fbP_kbP s
  have dRM : (⟨kbP s, 8⟩ : Region).Disjoint ⟨off (fbP s) oM, (s.gpr .rcx).toNat⟩ := by
    rw [hfb, off, BitVec.add_assoc, ← BitVec.ofNat_add]; exact Offset.base_disjoint _ (by decide) (by omega)
  have dRA : (⟨kbP s, 8⟩ : Region).Disjoint ⟨fbP s, 112⟩ := by
    rw [hfb]; exact Offset.base_disjoint _ (by decide) (by omega)
  have wM : (off (fbP s) oM).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 := by
    rw [toNat_off (by rw [hfb, ← off, toNat_off (by omega)]; unfold oM; omega), hfb, ← off,
      toNat_off (by omega)]; unfold oM; omega
  have hil := hp.hil
  have dKi : (stkRP s).Disjoint ⟨stackArg s 0, (s.gpr .rcx).toNat⟩ := by rw [← hil]; exact hp.dKi
  have dis : (⟨stackArg s 0, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩ := by
    rw [← hil]; exact hp.dis
  have wI : (stackArg s 0).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 := by rw [← hil]; exact hp.wI
  refine ⟨by omega, rfl, rfl, hp.dKn.sub_left sM, dKi.sub_left sM, hp.dKp.sub_left sM, hp.dKq.sub_left sM,
    hp.dKdp.sub_left sM, hp.dKdq.sub_left sM, hp.dKqi.sub_left sM, hp.dKpre.sub_left sM, hp.dKs.sub_left sM, dMA,
    hp.dns, dis, hp.dps, hp.dqs, hp.ddps, hp.ddqs, hp.dqis, hp.dpres, (hp.dKs.sub_left sA).symm, dRM,
    hp.dKn.sub_left sR, dKi.sub_left sR, hp.dKp.sub_left sR, hp.dKq.sub_left sR, hp.dKdp.sub_left sR,
    hp.dKdq.sub_left sR, hp.dKqi.sub_left sR, hp.dKpre.sub_left sR, hp.dKs.sub_left sR, dRA, wM, hp.wN, wI, hp.wP,
    hp.wQ, hp.wDp, hp.wDq, hp.wQi, hp.wS, hp.wPre, ⟨hk1, hk2⟩, trivial, trivial, hp.pl1, hp.pl2, hp.ql1, hp.ql2,
    hp.hdpl, hp.hqil, hp.hdql, hp.hsl, hp.hprl⟩

/-- The return address of the CRT's calls is in the stack the function
uses, below its own. -/
theorem holeP_sub (s : State) : Region.Sub (hole (kbP s)) (stkRP s) := by
  rw [show hole (kbP s) = ⟨s.gpr .rsp - BitVec.ofNat 64 stackBytesPc, 8⟩ by
    simp only [hole, kbP, BitVec.sub_sub]; rfl]
  exact Region.sub_prefix (by decide)

/-- Frame bytes at `d` are apart from the return address of the CRT's calls. -/
theorem frameP_hole {s : State} (hp : PreFPc s) {d n : Nat} (h : d + n ≤ frameBytes) :
    Region.Disjoint ⟨kbP s + BitVec.ofNat 64 (8 + d), n⟩ (hole (kbP s)) := by
  have ⟨hK1, _, _⟩ := kbP_toNat hp
  exact Offset.disjoint_below (kbP s) (n := 8) (by unfold frameBytes at h hK1; omega)

/-- The CRT's buffers are apart from the return address of its calls. -/
theorem crtPc_clear {s t : State} (hp : PreFPc s) (he : EnvP s t) :
    Clear (hole ((t.callEntry.withRegions (crtPcRd s) (crtPcWr s)).gpr .rsp))
      (t.callEntry.withRegions (crtPcRd s) (crtPcWr s)) := by
  simp only [State.withRegions_gpr, State.callEntry_rsp, he.rsp, fbP_sub8]
  have sH := holeP_sub s
  have hil := hp.hil
  have hk2 := hp.k2
  have e2 : oM = 160 := rfl
  intro r hr
  simp only [State.withRegions_rd, State.withRegions_wr, crtPcRd, crtPcWr, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hp.dKn.sub_left sH).symm
  · exact ((show (stkRP s).Disjoint ⟨stackArg s 0, (s.gpr .rcx).toNat⟩ by rw [← hil]; exact hp.dKi).sub_left sH).symm
  · exact (hp.dKp.sub_left sH).symm
  · exact (hp.dKq.sub_left sH).symm
  · exact (hp.dKdp.sub_left sH).symm
  · exact (hp.dKdq.sub_left sH).symm
  · exact (hp.dKqi.sub_left sH).symm
  · exact (hp.dKpre.sub_left sH).symm
  · rw [fbP_kbP]; exact frameP_hole hp (d := 0) (by decide)
  · rw [fbP_kbP, off, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact frameP_hole hp (by unfold frameBytes; omega)
  · exact (hp.dKs.sub_left sH).symm

/-! ## Memory across a call from the frame -/

/-- The return address a call from the frame stores. -/
theorem callEntryP_frame {s t : State} (hsp : t.gpr .rsp = fbP s) : Frame [below (fbP s) 8] t.mem t.callEntry.mem := by
  rw [State.callEntry_mem, hsp]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))

/-- A buffer of the caller that the function does not write, from memory
changed only where it may write. -/
theorem bytesP_of_frame {s : State} {m : Mem} (hf : Frame [stkRP s, outR s, scrR s] s.mem m) {p : Addr} {len : Nat}
    (hk : (stkRP s).Disjoint ⟨p, len⟩) (ho : (outR s).Disjoint ⟨p, len⟩) (hs : (scrR s).Disjoint ⟨p, len⟩)
    (hl : len ≤ 2 ^ 64) : Spec.Rsa.bytesAt m p len = Spec.Rsa.bytesAt s.mem p len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => hf.bytes (R := ⟨p, len⟩) (fun r hr => ?_) hl (List.mem_range.mp hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hk.symm
  · exact ho.symm
  · exact hs.symm

/-- `pre`'s words, from memory changed only where the function may write. -/
theorem wordsP_of_frame {s : State} {m : Mem} (hf : Frame [stkRP s, outR s, scrR s] s.mem m) {p : Addr} {n : Nat}
    (hk : (stkRP s).Disjoint ⟨p, n * 8⟩) (ho : (outR s).Disjoint ⟨p, n * 8⟩) (hs : (scrR s).Disjoint ⟨p, n * 8⟩)
    (hl : p.toNat + n * 8 ≤ 2 ^ 64) : Spec.Rsa.wordsAt m p n = Spec.Rsa.wordsAt s.mem p n := by
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => hf.readW (r := ⟨p, n * 8⟩) ?_ (fun r hr => ?_) (by decide)
  · have := List.mem_range.mp hi
    exact Offset.contains_base _ (by omega) (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hk.symm
    · exact ho.symm
    · exact hs.symm

/-- The return address's bytes are in the stack the function uses. -/
theorem belowP_sub (s : State) : Region.Sub (below (fbP s) 8) (stkRP s) := retP_sub s

/-- Memory changed by a call from the frame, within regions in the stack
the function uses, `out` or the working space. -/
theorem frameP_call {s : State} {m₁ m₂ m₃ : Mem} (h₁ : Frame [stkRP s, outR s, scrR s] m₁ m₂) {rs : List Region}
    (h₂ : Frame rs m₂ m₃) (hs : ∀ r ∈ rs, Region.Sub r (stkRP s) ∨ Region.Sub r (outR s) ∨ Region.Sub r (scrR s)) :
    Frame [stkRP s, outR s, scrR s] m₁ m₃ :=
  h₁.trans (h₂.sub fun r hr => by
    rcases hs r hr with h | h | h
    · exact ⟨_, List.mem_cons_self .., h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), h⟩)

/-- A slot kept by a call that writes regions apart from it. -/
theorem slotP_keep {s : State} {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {d : Nat}
    (hd : ∀ r ∈ rs, (⟨off (fbP s) d, 8⟩ : Region).Disjoint r) : word m' (fbP s) d = word m (fbP s) d :=
  hf.readW (Region.contains_self _ _) hd (by decide)

/-! ## The call -/

/-- The slots are apart from `M`, the working space and the return address. -/
theorem slotP_apart {s : State} (hp : PreFPc s) {d : Nat} (hd' : d + 8 ≤ oM) :
    ∀ r ∈ crtPcWr s ++ [below (fbP s) 16], (⟨off (fbP s) d, 8⟩ : Region).Disjoint r := by
  have e2 : oM = 160 := rfl
  have hk2 := hp.k2
  intro r hr
  simp only [crtPcWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  · exact (hp.dKs.sub_left (frameP_sub s (by unfold frameBytes; omega)))
  · exact Offset.disjoint_below (fbP s) (n := 16) (by omega)

theorem crtPc_covers {s t : State} (hp : PreFPc s) (he : EnvP s t) :
    Covers (crtPcRd s ++ crtPcWr s) (t.rd ++ t.wr) ∧ Covers (crtPcWr s) t.wr := by
  have hk2 := hp.k2
  have hil := hp.hil
  have e2 : oM = 160 := rfl
  have e3 : frameBytes = 1192 := rfl
  have hfr : (⟨fbP s, frameBytes⟩ : Region) ∈ t.wr := by rw [he.wr]; exact List.mem_cons_self ..
  have hscr : (⟨stackArg s 12, (stackArg s 13).toNat * 8⟩ : Region) ∈ t.wr := by
    rw [he.wr, hp.hwr]; simp
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have cw : Covers (crtPcWr s) t.wr := Covers.of_sub fun r hr => by
    simp only [crtPcWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hfr, oM, rfl, by dsimp only; omega⟩
    · exact ⟨_, hscr, 0, z _, by dsimp only; omega⟩
  refine ⟨Covers.append_left (Covers.of_sub fun r hr => ?_) cw.right, cw⟩
  · have hrd : ∀ x, x ∈ s.rd → x ∈ t.rd ++ t.wr := fun x hx => List.mem_append_left _ (by rw [he.rd]; exact hx)
    simp only [crtPcRd, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact ⟨⟨stackArg s 14, (stackArg s 15).toNat * 8⟩,
        hrd ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
    · exact ⟨_, List.mem_append_right _ hfr, 0, z _, by dsimp only; omega⟩

/-- The call of the CRT: `M` holds its result, which it returns. -/
theorem crtPc_call (v : CrtImpl) {s t : State} (hp : PreFPc s) (he : EnvP s t)
    (hargs : ∀ i < 14, word t.mem (fbP s) (8 * i) = stackArg s (i + 2)) (hdi : t.gpr .rdi = off (fbP s) oM)
    (hsi : t.gpr .rsi = s.gpr .rcx) (hdx : t.gpr .rdx = s.gpr .rdx) (hcx : t.gpr .rcx = s.gpr .rcx)
    (h8 : t.gpr .r8 = stackArg s 0) (h9 : t.gpr .r9 = s.gpr .rcx) :
    WP isa (.call v.pcrtName v.pcrt) t fun t' => EnvP s t' ∧
      (Spec.Rsa.privatePreOk s.mem (s.gpr .rdx) (s.gpr .rcx).toNat (stackArg s 2) (stackArg s 3).toNat
        (stackArg s 4) (stackArg s 5).toNat (stackArg s 14) (stackArg s 15).toNat →
      Spec.Rsa.written t'.mem (off (fbP s) oM) (s.gpr .rcx).toNat ((t'.gpr .rax).setWidth 32)
        (Spec.Rsa.privateCrt (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 5).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 5).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 10) (stackArg s 3).toNat))) ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 := by
  obtain ⟨hc, hw⟩ := crtPc_covers hp he
  refine WP.call_mx (k := crtPcContract.clear) v.pcrtOk v.pcrtNosp (by rw [v.pcrtDepth]; decide)
    ⟨crtPc_pre hp he hargs hdi hsi hdx hcx h8 h9, crtPc_clear hp he⟩ hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ hmx
  rw [v.pcrtDepth, he.rsp] at hf
  simp only [Nat.reduceAdd, Nat.reduceMul] at hf
  have hE : ∀ i < 14, stackArg (t.callEntry.withRegions (crtPcRd s) (crtPcWr s)) i = stackArg s (i + 2) :=
    fun i hi => (stackArgP_entry he.rsp _ _ (by omega)).trans (hargs i hi)
  have hfE : Frame [stkRP s, outR s, scrR s] s.mem t.callEntry.mem :=
    frameP_call he.mem (callEntryP_frame he.rsp) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inl (belowP_sub s)
  have hk2 := hp.k2
  have hil := hp.hil
  have b : ∀ {p : Addr} {len : Nat}, (stkRP s).Disjoint ⟨p, len⟩ → (outR s).Disjoint ⟨p, len⟩ →
      (scrR s).Disjoint ⟨p, len⟩ → len ≤ 2 ^ 64 →
      Spec.Rsa.bytesAt t.callEntry.mem p len = Spec.Rsa.bytesAt s.mem p len := fun hk ho hs hl =>
    bytesP_of_frame hfE hk ho hs hl
  simp only [Contract.clear, crtPcContract, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    hdi, hdx, hcx, h8, hE 0 (by decide), hE 1 (by decide), hE 2 (by decide), hE 3 (by decide), hE 4 (by decide),
    hE 6 (by decide), hE 8 (by decide), hE 12 (by decide), hE 13 (by decide), Nat.reduceAdd, hm₂, hg₂ .rax (by decide),
    Spec.Rsa.privatePreOk] at hpost
  rw [b hp.dKn hp.dOn hp.dns.symm (by have := hp.wN; omega),
    b (p := stackArg s 2) (len := (stackArg s 3).toNat) hp.dKp hp.dOp hp.dps.symm (by have := hp.wP; omega),
    b (p := stackArg s 4) (len := (stackArg s 5).toNat) hp.dKq hp.dOq hp.dqs.symm (by have := hp.wQ; omega),
    b (p := stackArg s 0) (len := (s.gpr .rcx).toNat) (by rw [← hil]; exact hp.dKi) (by rw [← hil]; exact hp.dOi)
      (by rw [← hil]; exact hp.dis.symm) (by omega),
    b (p := stackArg s 6) (len := (stackArg s 3).toNat) (by rw [← hp.hdpl]; exact hp.dKdp)
      (by rw [← hp.hdpl]; exact hp.dOdp)
      (by rw [← hp.hdpl]; exact hp.ddps.symm) (by have := hp.wDp; have := hp.hdpl; omega),
    b (p := stackArg s 8) (len := (stackArg s 5).toNat) (by rw [← hp.hdql]; exact hp.dKdq)
      (by rw [← hp.hdql]; exact hp.dOdq)
      (by rw [← hp.hdql]; exact hp.ddqs.symm) (by have := hp.wDq; have := hp.hdql; omega),
    b (p := stackArg s 10) (len := (stackArg s 3).toNat) (by rw [← hp.hqil]; exact hp.dKqi)
      (by rw [← hp.hqil]; exact hp.dOqi)
      (by rw [← hp.hqil]; exact hp.dqis.symm) (by have := hp.wQi; have := hp.hqil; omega),
    wordsP_of_frame hfE hp.dKpre hp.dOpre hp.dpres.symm hp.wPre] at hpost
  refine ⟨⟨(hcs .rsp (by decide)).trans he.rsp, hrd.trans he.rd, hwr.trans he.wr,
    frameP_call he.mem hf fun r hr => ?_, ?_, ?_, ?_, ?_, ?_⟩, fun h => hpost h, hcs, hmx⟩
  · simp only [crtPcWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (frameP_sub s (by unfold oM frameBytes; omega))
    · exact .inr (.inr (sub_refl _))
    · exact .inl (ret2P_sub s)
  · rw [slotP_keep hf (slotP_apart hp (by decide))]; exact he.sOut
  · rw [slotP_keep hf (slotP_apart hp (by decide))]; exact he.sN
  · rw [slotP_keep hf (slotP_apart hp (by decide))]; exact he.sK
  · rw [slotP_keep hf (slotP_apart hp (by decide))]; exact he.sE
  · rw [slotP_keep hf (slotP_apart hp (by decide))]; exact he.sEl

end VG.Proof.Rsa.X86_64
