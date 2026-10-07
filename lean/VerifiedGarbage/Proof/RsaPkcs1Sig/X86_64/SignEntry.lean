import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.SignBlocks
import VerifiedGarbage.Proof.Rsa.X86_64.PrivCtx

/-!
# `vg_rsa_pkcs1_sign` on x86-64: the entry of `vg_rsa_private_checked`

Everything the call uses is in the function's stack, at offsets of its
base `kb`: the callee's stack (`stackBytes` bytes at `kb`), the return
address (at `kb + stackBytes`), and the frame above (at
`kb + stackBytes + 8`), which holds the call's stack arguments and `EM`. Its
precondition at the call (`priv_pre`).
-/

namespace VG.Proof.RsaPkcs1Sig.X86_64.Sgn

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Sign
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (sp lea)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64
open VG.Proof.Rsa.X86_64 (chkContract stackBytes)

theorem fb_kb (s : State) : fb s = off (kb s) 3264 := fb_eq s

/-- The callee's stack pointer. -/
theorem fb_sub8 (s : State) : fb s - 8 = off (kb s) 3256 := by
  rw [fb_kb, off, off, show (3264 : Nat) = 3256 + 8 from rfl, BitVec.ofNat_add, ← BitVec.add_assoc]
  exact BitVec.add_sub_cancel _ _

theorem ksub (s : State) {d n : Nat} (h : d + n ≤ sigStack) : Region.Sub ⟨off (kb s) d, n⟩ (stkR s) :=
  Offset.sub_base _ h

theorem stackArg_entry {s t : State} (hsp : t.gpr .rsp = fb s) (rd wr : List Region) {i : Nat} (hi : i < 100) :
    stackArg (t.callEntry.withRegions rd wr) i = word t.mem (fb s) (8 * i) := by
  have hsep := Offset.sep (kb s) (d := 3256 + 8 * (i + 1)) (n := 8) (e := 3256) (k := 8) (by omega) (by omega)
    (by omega)
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_mem, hsp, fb_sub8]
  rw [off, BitVec.add_assoc, ← BitVec.ofNat_add, Mem.readW_writeW_sep hsep (by decide)]
  show _ = t.mem.readW (off (fb s) (8 * i)) 64
  rw [fb_kb, off_off, show 3256 + 8 * (i + 1) = 3264 + 8 * i by omega]

theorem stackArgAddr_entry {s t : State} (hsp : t.gpr .rsp = fb s) (rd wr : List Region) :
    stackArgAddr (t.callEntry.withRegions rd wr) 0 = fb s := by
  simp only [stackArgAddr, State.withRegions_gpr, State.callEntry_rsp, hsp, fb_sub8]
  rw [fb_kb, off, off, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- `EM`, as the call's input. -/
def emR (s : State) : Region := ⟨off (fb s) oEM, (s.gpr .rcx).toNat⟩

/-- What the call reads: `n`, `e`, `EM`, the key's parts and its stack
arguments. -/
def privRd (s : State) : List Region :=
  [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩, emR s,
    ⟨stackArg s 3, (stackArg s 4).toNat⟩, ⟨stackArg s 5, (stackArg s 6).toNat⟩,
    ⟨stackArg s 7, (stackArg s 8).toNat⟩, ⟨stackArg s 9, (stackArg s 10).toNat⟩,
    ⟨stackArg s 11, (stackArg s 12).toNat⟩, ⟨fb s, 112⟩]

/-- What it writes: `out` and the working space. -/
def privWr (s : State) : List Region := [outR s, scrR s]

theorem priv_pre {s t : State} (hp : PreS s) (hsp : t.gpr .rsp = fb s)
    (hw : ∀ i < 14, word t.mem (fb s) (8 * i) = callArg s i)
    (hdi : t.gpr .rdi = s.gpr .rdi) (hsi : t.gpr .rsi = s.gpr .rsi) (hdx : t.gpr .rdx = s.gpr .rdx)
    (hcx : t.gpr .rcx = s.gpr .rcx) (h8 : t.gpr .r8 = s.gpr .r8) (h9 : t.gpr .r9 = s.gpr .r9) :
    chkContract.pre (t.callEntry.withRegions (privRd s) (privWr s)) := by
  have hE : ∀ i, i < 14 → stackArg (t.callEntry.withRegions (privRd s) (privWr s)) i = callArg s i :=
    fun i hi => (stackArg_entry hsp _ _ (by omega)).trans (hw i hi)
  have hE2 : ∀ j, j < 12 → stackArg (t.callEntry.withRegions (privRd s) (privWr s)) (j + 2) = stackArg s (j + 3) :=
    fun j hj => hE (j + 2) (by omega)
  simp only [chkContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_rsp, State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), hdi, hsi, hdx, hcx, h8, h9, hsp,
    stackArgAddr_entry hsp, hE 0 (by decide), hE 1 (by decide), callArg,
    (hE2 0 (by decide) : stackArg _ 2 = _), (hE2 1 (by decide) : stackArg _ 3 = _),
    (hE2 2 (by decide) : stackArg _ 4 = _), (hE2 3 (by decide) : stackArg _ 5 = _),
    (hE2 4 (by decide) : stackArg _ 6 = _), (hE2 5 (by decide) : stackArg _ 7 = _),
    (hE2 6 (by decide) : stackArg _ 8 = _), (hE2 7 (by decide) : stackArg _ 9 = _),
    (hE2 8 (by decide) : stackArg _ 10 = _), (hE2 9 (by decide) : stackArg _ 11 = _),
    (hE2 10 (by decide) : stackArg _ 12 = _), (hE2 11 (by decide) : stackArg _ 13 = _), fb_sub8]
  have ⟨hK1, hK2⟩ := kb_toNat hp
  have e1 : sigStack = 4456 := rfl
  have e2 : oEM = 160 := rfl
  have e3 : stackBytes = 3256 := rfl
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hfb : fb s = off (kb s) 3264 := fb_kb s
  have hem : off (fb s) oEM = off (kb s) 3424 := by rw [hfb, off_off]; rfl
  have sM : Region.Sub (emR s) (stkR s) := by simp only [emR]; rw [hem]; exact ksub s (by omega)
  have sA : Region.Sub ⟨fb s, 112⟩ (stkR s) := by rw [hfb]; exact ksub s (by decide)
  have sR : Region.Sub ⟨off (kb s) 3256, 8⟩ (stkR s) := ksub s (by decide)
  have sK : Region.Sub ⟨off (kb s) 3256 - BitVec.ofNat 64 3256, 3256⟩ (stkR s) := by
    rw [show off (kb s) 3256 - BitVec.ofNat 64 3256 = kb s from BitVec.add_sub_cancel _ _]
    exact Region.sub_prefix (by decide)
  have hkk : off (kb s) 3256 - BitVec.ofNat 64 3256 = kb s := BitVec.add_sub_cancel _ _
  have dMA : (emR s).Disjoint ⟨fb s, 112⟩ := by
    simp only [emR]; rw [hem, hfb]; exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  have dRM : (⟨off (kb s) 3256, 8⟩ : Region).Disjoint (emR s) := by
    simp only [emR]; rw [hem]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  have dRA : (⟨off (kb s) 3256, 8⟩ : Region).Disjoint ⟨fb s, 112⟩ := by
    rw [hfb]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  have dKM : (⟨off (kb s) 3256 - BitVec.ofNat 64 3256, 3256⟩ : Region).Disjoint (emR s) := by
    simp only [emR]; rw [hkk, hem]; exact Offset.base_disjoint _ (by omega) (by omega)
  have dKA : (⟨off (kb s) 3256 - BitVec.ofNat 64 3256, 3256⟩ : Region).Disjoint ⟨fb s, 112⟩ := by
    rw [hkk, hfb]; exact Offset.base_disjoint _ (by omega) (by omega)
  have wM : (off (fb s) oEM).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 := by
    rw [hem, toNat_off (by omega)]; omega
  have hR : (off (kb s) 3256).toNat = (kb s).toNat + 3256 := toNat_off (by omega)
  have dK := hp.dKo; have dKn := hp.dKn; have dKe := hp.dKe; have dKp := hp.dKp; have dKq := hp.dKq
  have dKdp := hp.dKdp; have dKdq := hp.dKdq; have dKqi := hp.dKqi; have dKs := hp.dKs
  refine ⟨by omega, by omega, rfl, rfl, hp.dOn, hp.dOe, (dK.sub_left sM).symm, hp.dOp, hp.dOq, hp.dOdp, hp.dOdq,
    hp.dOqi, hp.dOs, (dK.sub_left sA).symm,
    hp.dns, hp.des, dKs.sub_left sM, hp.dps, hp.dqs, hp.ddps, hp.ddqs, hp.dqis, (dKs.sub_left sA).symm,
    dK.sub_left sR, dKn.sub_left sR, dKe.sub_left sR, dRM, dKp.sub_left sR, dKq.sub_left sR, dKdp.sub_left sR,
    dKdq.sub_left sR, dKqi.sub_left sR, dKs.sub_left sR, dRA,
    dK.sub_left sK, dKn.sub_left sK, dKe.sub_left sK, dKM, dKp.sub_left sK, dKq.sub_left sK, dKdp.sub_left sK,
    dKdq.sub_left sK, dKqi.sub_left sK, dKs.sub_left sK, dKA,
    hp.wO, hp.wN, hp.wE, wM, hp.wP, hp.wQ, hp.wDp, hp.wDq, hp.wQi, hp.wS, ⟨hk1, hk2⟩, hp.hsi, trivial, hp.L1,
    hp.L2, hp.pl1, hp.pl2, hp.ql1, hp.ql2, hp.hdpl, hp.hqil, hp.hdql, by simp only [Spec.Rsa.scratchWords]; exact hp.hsl⟩

/-! ## Memory across the call -/

theorem priv_covers {s t : State} (hp : PreS s) (he : Env s t) :
    Covers (privRd s ++ privWr s) (t.rd ++ t.wr) ∧ Covers (privWr s) t.wr := by
  have hk2 := hp.k2
  have hfr : (⟨fb s, frameBytes⟩ : Region) ∈ t.wr := by rw [he.wr]; exact List.mem_cons_self ..
  have hout : outR s ∈ t.wr := by rw [he.wr, hp.hwr]; simp [outR]
  have hscr : scrR s ∈ t.wr := by rw [he.wr, hp.hwr]; simp [scrR]
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have cw : Covers (privWr s) t.wr := Covers.of_sub fun r hr => by
    simp only [privWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hout, 0, z _, by simp only [outR]; omega⟩
    · exact ⟨_, hscr, 0, z _, by simp only [scrR]; omega⟩
  refine ⟨Covers.append_left (Covers.of_sub fun r hr => ?_) cw.right, cw⟩
  have hrd : ∀ x, x ∈ s.rd → x ∈ t.rd ++ t.wr := fun x hx => List.mem_append_left _ (by rw [he.rd]; exact hx)
  simp only [privRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, hrd ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hrd ⟨s.gpr .r8, (s.gpr .r9).toNat⟩ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, List.mem_append_right _ hfr, oEM, rfl, by dsimp only [emR]; unfold oEM frameBytes; omega⟩
  · exact ⟨_, hrd ⟨stackArg s 3, (stackArg s 4).toNat⟩ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hrd ⟨stackArg s 5, (stackArg s 6).toNat⟩ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hrd ⟨stackArg s 7, (stackArg s 8).toNat⟩ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hrd ⟨stackArg s 9, (stackArg s 10).toNat⟩ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hrd ⟨stackArg s 11, (stackArg s 12).toNat⟩ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, List.mem_append_right _ hfr, 0, z _, by dsimp only; unfold frameBytes; omega⟩

/-- The callee's stack and the return address, below the frame. -/
theorem below_kb (s : State) : below (fb s) (3256 + 8) = ⟨kb s, 3264⟩ := by
  simp only [below]; rw [fb_kb]; exact congrArg (Region.mk · 3264) (BitVec.add_sub_cancel _ _)

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

/-- What the call writes is apart from the frame. -/
theorem frame_apart {s : State} (hp : PreS s) {d n : Nat} (hd : d + n ≤ frameBytes) :
    ∀ r ∈ privWr s ++ [below (fb s) (3256 + 8)], (⟨off (fb s) d, n⟩ : Region).Disjoint r := by
  intro r hr
  simp only [privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hp.dKo.sub_left (frame_sub s hd))
  · exact (hp.dKs.sub_left (frame_sub s hd))
  · rw [below_kb, fb_kb, off_off]
    exact (Offset.base_disjoint (kb s) (e := 3264 + d) (n := n) (k := 3264) (by omega)
      (by have := (kb_toNat hp).1; unfold frameBytes at hd; unfold sigStack at this; omega)).symm

theorem callEntry_frame {s t : State} (hsp : t.gpr .rsp = fb s) :
    Frame [below (fb s) (3256 + 8)] t.mem t.callEntry.mem := by
  rw [State.callEntry_mem, hsp]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))

/-- A slot kept by a call that writes regions apart from it. -/
theorem slot_keep {p : Addr} {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {d : Nat}
    (hd : ∀ r ∈ rs, (⟨off p d, 8⟩ : Region).Disjoint r) : word m' p d = word m p d :=
  hf.readW (Region.contains_self _ _) hd (by decide)

end VG.Proof.RsaPkcs1Sig.X86_64.Sgn
