module

public import VerifiedGarbage.Proof.AesXts.X86_64.To.Contract
public import VerifiedGarbage.Impl.AesXts.X86_64To
public import VerifiedGarbage.Proof.AesXts.X86_64.Unit.Call
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Copy
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Copy
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.LoopCT
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.AesXts.Unit
import VerifiedGarbage.Proof.AesCbc.X86_64.Block
import VerifiedGarbage.Proof.AesCbc.X86_64.Loop
import VerifiedGarbage.Proof.AesXts.X86_64.CT
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.AesXts.X86_64.To.Contract
meta import VerifiedGarbage.Impl.AesXts.X86_64To
meta import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.SealGather
meta import VerifiedGarbage.Proof.AesXts.X86_64.Unit.Call
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Copy
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.LoopCT
meta import VerifiedGarbage.Proof.AesCcm.BytesAt
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Run
meta import VerifiedGarbage.Proof.AesXts.Unit
meta import VerifiedGarbage.Proof.AesCbc.X86_64.Block
meta import VerifiedGarbage.Proof.AesCbc.X86_64.Loop
meta import VerifiedGarbage.Proof.AesXts.X86_64.CT
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# XTS-AES of whole blocks on x86-64, out of place, by a copy: the proof

`copyThen_correct`: for an implementation `f` of `vg_aes_xts_encrypt` or
`vg_aes_xts_decrypt` (`modeX86_64 (xtsMode enc)`), `copyThen f`
(`Impl/AesXts/X86_64To.lean`) meets the out-of-place contract
`xtsToX86_64 enc`: the stash (`stash_ok`) writes the first 24 bytes of the
scratch buffer, the copy (`copyBytes_ok`) writes `dst` with the blocks at
`src`, the arguments come back from the scratch buffer (`unstash_ok`), and
the call (`Unit.xts_call`) transforms the blocks at `dst` in place.
`copyThen_ct`: the pieces are constant time from the public arguments, and
the call by its callee's proof.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.To

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesXts.X86_64To
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.X86_64 (modeX86_64 in_rw offset_nat)
open VG.Spec.Aes (bytesAt)

section
variable (s : State)

abbrev W : Addr := s.gpr .rdi
abbrev R : Nat := (s.gpr .rsi).toNat
abbrev T : Addr := s.gpr .rdx
abbrev Sr : Addr := s.gpr .rcx
abbrev N : Nat := (s.gpr .r8).toNat
abbrev S : Addr := s.gpr .r9
abbrev Dd : Addr := s.gpr .r10

abbrev schR : Region := ⟨W s, 240⟩
abbrev srcR : Region := ⟨Sr s, 16 * N s⟩
abbrev ivR : Region := ⟨T s, 16⟩
abbrev dstR : Region := ⟨Dd s, 16 * N s⟩
abbrev scrR : Region := ⟨S s, 2176⟩
abbrev retR : Region := ⟨s.gpr .rsp, 8⟩
abbrev stkR : Region := below (s.gpr .rsp) 16

/-- Offset `d` of the scratch buffer. -/
abbrev Sd (d : Nat) : Addr := S s + BitVec.ofNat 64 d

end

/-- The precondition, by name. -/
structure TPre (s : State) : Prop where
  rd : s.rd = [schR s, srcR s]
  wr : s.wr = [ivR s, dstR s, scrR s]
  sch_iv : (schR s).Disjoint (ivR s)
  sch_dst : (schR s).Disjoint (dstR s)
  sch_scr : (schR s).Disjoint (scrR s)
  src_iv : (srcR s).Disjoint (ivR s)
  src_dst : (srcR s).Disjoint (dstR s)
  src_scr : (srcR s).Disjoint (scrR s)
  iv_dst : (ivR s).Disjoint (dstR s)
  iv_scr : (ivR s).Disjoint (scrR s)
  dst_scr : (dstR s).Disjoint (scrR s)
  ret_iv : (retR s).Disjoint (ivR s)
  ret_dst : (retR s).Disjoint (dstR s)
  ret_scr : (retR s).Disjoint (scrR s)
  stk_sch : (stkR s).Disjoint (schR s)
  stk_src : (stkR s).Disjoint (srcR s)
  stk_iv : (stkR s).Disjoint (ivR s)
  stk_dst : (stkR s).Disjoint (dstR s)
  stk_scr : (stkR s).Disjoint (scrR s)
  iv_wrap : (T s).toNat + 16 ≤ 2 ^ 64
  src_wrap : (Sr s).toNat + 16 * N s ≤ 2 ^ 64
  dst_wrap : (Dd s).toNat + 16 * N s ≤ 2 ^ 64
  scr_wrap : (S s).toNat + 2176 ≤ 2 ^ 64
  rsp_lo : 16 ≤ (s.gpr .rsp).toNat
  rsp_hi : (s.gpr .rsp).toNat + 8 ≤ 2 ^ 64
  n_lt : N s < 2 ^ 59
  rounds : R s = 10 ∨ R s = 12 ∨ R s = 14

theorem TPre.of {enc : Bool} {s : State} (h : (xtsToX86_64 enc).pre s) : TPre s :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v, w, x, y, z, a', b'⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v, w, x, y, z, a', b'⟩

theorem ofNat_toNat (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The memory after the stash. -/
def stashMem (s : State) : Mem :=
  ((s.mem.writeW (Sd s 0) (s.gpr .rdi)).writeW (Sd s 8) (s.gpr .rsi)).writeW (Sd s 16) (s.gpr .r8)

section
variable {s₀ : State} (hp : TPre s₀)
include hp

theorem TPre.cS {d n : Nat} (h : d + n ≤ 2176) : (scrR s₀).Contains (Sd s₀ d) n :=
  Offset.contains_base _ h (by have := hp.scr_wrap; omega)

theorem TPre.wS {d n : Nat} (h : d + n ≤ 2176) : InRegions s₀.wr (Sd s₀ d) n :=
  in_rw (r := scrR s₀) (by rw [hp.wr]; simp) (hp.cS h)

theorem TPre.shl16 : BitVec.ofNat 64 (N s₀) <<< 4 = BitVec.ofNat 64 (16 * N s₀) := by
  apply BitVec.eq_of_toNat_eq
  have := hp.n_lt
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (a := N s₀) (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- The stash: `schedule`, `rounds` and `n` in the scratch buffer, and the
copy's arguments. -/
theorem stash_ok :
    ∃ s', runBlock isa stash s₀ = some s' ∧ s'.mem = stashMem s₀ ∧
      s'.gpr .rsi = Sr s₀ ∧ s'.gpr .rdi = Dd s₀ ∧ s'.gpr .rcx = BitVec.ofNat 64 (16 * N s₀) ∧
      (∀ r, r ≠ .rsi → r ≠ .rdi → r ≠ .rcx → s'.gpr r = s₀.gpr r) ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr := by
  have w0 := hp.wS (d := 0) (n := 8) (by decide)
  have w8 := hp.wS (d := 8) (n := 8) (by decide)
  have w16 := hp.wS (d := 16) (n := 8) (by decide)
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, stash, runBlock_cons, runStep_some, Impl.AesCbc.X86_64.at_,
      exec, readSrc, State.store64, State.ea, execShift, offset_nat, Option.map_some,
      gpr_setReg, w0, w8, w16, show 1 ≤ 4 ∧ 4 ≤ 63 from by decide]
    rfl, ?_⟩
  refine ⟨rfl, ?_, ?_, ?_, fun r h₁ h₂ h₃ => ?_, rfl, rfl⟩
  · simp [gpr_setReg, gpr_setFlags]
  · simp [gpr_setReg, gpr_setFlags]
  · simp only [gpr_setReg, ↓reduceIte]
    rw [← hp.shl16, ofNat_toNat]
  · simp [gpr_setReg, gpr_setFlags, h₁, h₂, h₃]

/-- What the stash keeps outside the first 24 bytes of the scratch buffer. -/
theorem stash_frame : Frame [scrR s₀] s₀.mem (stashMem s₀) := by
  refine (((Frame.refl _ _).writeW List.mem_cons_self _ (hp.cS (by decide))).writeW List.mem_cons_self _
    (hp.cS (by decide))).writeW List.mem_cons_self _ (hp.cS (by decide))

theorem stash_read0 : (stashMem s₀).readW (Sd s₀ 0) 64 = s₀.gpr .rdi := by
  have hw := hp.scr_wrap
  rw [stashMem, Mem.readW_writeW_sep (Offset.sep (S s₀) (d := 0) (n := 8) (e := 16) (k := 8) (by omega)
      (by omega) (by omega)) (by decide),
    Mem.readW_writeW_sep (Offset.sep (S s₀) (d := 0) (n := 8) (e := 8) (k := 8) (by omega)
      (by omega) (by omega)) (by decide),
    Mem.readW_writeW_self64]

theorem stash_read8 : (stashMem s₀).readW (Sd s₀ 8) 64 = s₀.gpr .rsi := by
  have hw := hp.scr_wrap
  rw [stashMem, Mem.readW_writeW_sep (Offset.sep (S s₀) (d := 8) (n := 8) (e := 16) (k := 8) (by omega)
      (by omega) (by omega)) (by decide), Mem.readW_writeW_self64]

omit hp in
theorem stash_read16 : (stashMem s₀).readW (Sd s₀ 16) 64 = s₀.gpr .r8 := Mem.readW_writeW_self64 _ _ _

/-- After the stash. -/
structure P1 (s₀ s : State) : Prop where
  mem : s.mem = stashMem s₀
  rsi : s.gpr .rsi = Sr s₀
  rdi : s.gpr .rdi = Dd s₀
  rcx : s.gpr .rcx = BitVec.ofNat 64 (16 * N s₀)
  keep : ∀ r, r ≠ .rsi → r ≠ .rdi → r ≠ .rcx → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem stash_wp : WP isa (.block stash) s₀ (P1 s₀) := by
  obtain ⟨s₁, run₁, m, a, b, c, d, e, f⟩ := stash_ok hp
  exact WP.of_runBlock ⟨s₁, run₁, m, a, b, c, d, e, f⟩

/-- After the copy: `dst` holds the blocks at `src`. -/
structure P2 (s₀ s : State) : Prop where
  mem : s.mem = WriteBytes.writeBytes (stashMem s₀) (Dd s₀) (bytesAt s₀.mem (Sr s₀) (16 * N s₀))
  rdi : s.gpr .rdi = Dd s₀
  keep : ∀ r, r ≠ .rsi → r ≠ .rdi → r ≠ .rcx → r ≠ .rax → r ≠ .r8 → r ≠ .r10 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem P1.copyPre {s : State} (h : P1 s₀ s) :
    Proof.AesGcm.X86_64.Short.CopyPre s (Sr s₀) (Dd s₀) (16 * N s₀) where
  rsi := h.rsi
  rdi := h.rdi
  rcx := h.rcx
  lt := by have := hp.n_lt; omega
  rd := by
    rw [h.rd, h.wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨srcR s₀, by simp, 0, by simp, by simp⟩
  wr := by
    rw [h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨dstR s₀, by simp, 0, by simp, by simp⟩
  disj := hp.src_dst

theorem src_stash : bytesAt (stashMem s₀) (Sr s₀) (16 * N s₀) = bytesAt s₀.mem (Sr s₀) (16 * N s₀) :=
  Proof.Cmac.bytesAt_frame (stash_frame hp) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.src_scr) (by have := hp.n_lt; omega)

theorem copy_wp {s : State} (h : P1 s₀ s) :
    WP isa (Impl.ChaCha20Poly1305.X86_64.SealGather.copyBytes .x16) s (P2 s₀) :=
  WP.mono (Proof.ChaCha20Poly1305.X86_64.Gather.copyBytes_ok (h.copyPre hp) .x16) fun s' ⟨m, g, rd, wr⟩ =>
    { mem := by rw [m, h.mem, src_stash hp]
      rdi := by rw [g _ (by decide) (by decide) (by decide), h.rdi]
      keep := fun r a b c d e f => by rw [g r d e f, h.keep r a b c]
      rd := by rw [rd, h.rd]
      wr := by rw [wr, h.wr] }

/-- The memory before the call: the stash, and `dst` holding the blocks at
`src`. -/
def CopiedMem (s₀ : State) (m : Mem) : Prop :=
  Frame [scrR s₀, dstR s₀] s₀.mem m ∧
    Spec.Cbc.blocksAt m (Dd s₀) (N s₀) = Spec.Cbc.blocksAt s₀.mem (Sr s₀) (N s₀)

/-- Before the call. -/
structure Ready (s₀ s : State) : Prop where
  pre : Unit.XPre s (W s₀) (T s₀) (Dd s₀) (S s₀) (N s₀) (R s₀)
  cs : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r
  mem : CopiedMem s₀ s.mem

theorem P2.copied {s : State} (h : P2 s₀ s) : CopiedMem s₀ s.mem := by
  have hn := hp.n_lt
  have hl : (bytesAt s₀.mem (Sr s₀) (16 * N s₀)).length = 16 * N s₀ := Proof.AesXts.Unit.length_bytesAt _ _ _
  refine ⟨?_, ?_⟩
  · rw [h.mem]
    exact ((stash_frame hp).mono (by simp)).trans ((Proof.AesGcm.X86_64.writeBytes_frame' _ hl).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dstR s₀, by simp, fun _ h => h⟩)
  · rw [← Proof.AesXts.Unit.blocks_bytesAt, ← Proof.AesXts.Unit.blocks_bytesAt, h.mem,
      Proof.AesCcm.bytesAt_writeBytes_base _ _ _ (by rw [hl]) (by omega), hl, List.drop_eq_nil_of_le (by
        rw [Proof.AesXts.Unit.length_bytesAt]), List.append_nil]

theorem P2.read {s : State} (h : P2 s₀ s) {d : Nat} (hd : d + 8 ≤ 2176) :
    s.mem.readW (Sd s₀ d) 64 = (stashMem s₀).readW (Sd s₀ d) 64 := by
  rw [h.mem]
  exact (Proof.AesGcm.X86_64.writeBytes_frame' _ (Proof.AesXts.Unit.length_bytesAt _ _ _)).readW
    (r := ⟨Sd s₀ d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.dst_scr.symm.sub_left (Offset.sub_base _ hd))) (by decide)

theorem rdwr_eq {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    s.rd ++ s.wr = [schR s₀, srcR s₀, ivR s₀, dstR s₀, scrR s₀] := by
  rw [hrd, hwr, hp.rd, hp.wr]; rfl

omit hp in
theorem TPre.reads : Covers ([⟨W s₀, 240⟩] ++ [⟨T s₀, 16⟩, ⟨Dd s₀, 16 * N s₀⟩, ⟨S s₀, 2176⟩])
    [schR s₀, srcR s₀, ivR s₀, dstR s₀, scrR s₀] := by
  refine Covers.of_sub fun r hr => ?_
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
  · exact ⟨ivR s₀, by simp, 0, by simp, by simp⟩
  · exact ⟨dstR s₀, by simp, 0, by simp, by simp⟩
  · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

omit hp in
theorem TPre.writes : Covers [⟨T s₀, 16⟩, ⟨Dd s₀, 16 * N s₀⟩, ⟨S s₀, 2176⟩] [ivR s₀, dstR s₀, scrR s₀] := by
  refine Covers.of_sub fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨ivR s₀, by simp, 0, by simp, by simp⟩
  · exact ⟨dstR s₀, by simp, 0, by simp, by simp⟩
  · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

/-- The arguments of the in-place call, back from the scratch buffer. -/
theorem unstash_wp {s : State} (h : P2 s₀ s) : WP isa (.block unstash) s (Ready s₀) := by
  have hr9 : s.gpr .r9 = S s₀ :=
    h.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have rw' := rdwr_eq hp h.rd h.wr
  have i0 : InRegions (s.rd ++ s.wr) (Sd s₀ 0) 8 := by
    rw [rw']; exact in_rw (r := scrR s₀) (by simp) (hp.cS (by decide))
  have i8 : InRegions (s.rd ++ s.wr) (Sd s₀ 8) 8 := by
    rw [rw']; exact in_rw (r := scrR s₀) (by simp) (hp.cS (by decide))
  have i16 : InRegions (s.rd ++ s.wr) (Sd s₀ 16) 8 := by
    rw [rw']; exact in_rw (r := scrR s₀) (by simp) (hp.cS (by decide))
  have e0 : s.gpr .r9 + BitVec.ofNat 64 0 = Sd s₀ 0 := by rw [hr9]
  have e8 : s.gpr .r9 + BitVec.ofNat 64 8 = Sd s₀ 8 := by rw [hr9]
  have e16 : s.gpr .r9 + BitVec.ofNat 64 16 = Sd s₀ 16 := by rw [hr9]
  have v0 := (h.read hp (d := 0) (by decide)).trans (stash_read0 hp)
  have v8 := (h.read hp (d := 8) (by decide)).trans (stash_read8 hp)
  have v16 := (h.read hp (d := 16) (by decide)).trans (stash_read16 (s₀ := s₀))
  refine WP.of_runBlock ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, unstash, runBlock_cons, runStep_some, runBlock_nil,
      Impl.AesCbc.X86_64.at_, exec, readSrc, State.load64, State.ea, offset_nat, Option.map_some, gpr_setReg,
      mem_setReg, rd_setReg, wr_setReg, e0, e8, e16, i0, i8, i16]
    rfl, ?_⟩
  have k (r : Reg) (h₁ : r ≠ .rsi) (h₂ : r ≠ .rdi) (h₃ : r ≠ .rcx) (h₄ : r ≠ .rax) (h₅ : r ≠ .r8)
      (h₆ : r ≠ .r10) : s.gpr r = s₀.gpr r := h.keep r h₁ h₂ h₃ h₄ h₅ h₆
  have krsp : s.gpr .rsp = s₀.gpr .rsp := k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have v0' : s.mem.readW (S s₀) 64 = W s₀ := by simpa using v0
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, hp.rounds, by have := hp.n_lt; omega, hp.sch_iv, hp.sch_dst, hp.sch_scr,
    hp.iv_dst, hp.iv_scr, hp.dst_scr, ?_, ?_, ?_, ?_, hp.iv_wrap, hp.dst_wrap, hp.scr_wrap, ?_, ?_⟩, ?_, ?_⟩
  · simp [gpr_setReg, v0']
  · simp [gpr_setReg, v8]
  · simp [gpr_setReg, k .rdx (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  · simp [gpr_setReg, h.rdi]
  · simp [gpr_setReg, v16]
  · simp [gpr_setReg, hr9]
  · show (below _ 16).Disjoint _; simp only [gpr_setReg, reduceCtorEq, ↓reduceIte, krsp]; exact hp.stk_sch
  · show (below _ 16).Disjoint _; simp only [gpr_setReg, reduceCtorEq, ↓reduceIte, krsp]; exact hp.stk_iv
  · show (below _ 16).Disjoint _; simp only [gpr_setReg, reduceCtorEq, ↓reduceIte, krsp]; exact hp.stk_dst
  · show (below _ 16).Disjoint _; simp only [gpr_setReg, reduceCtorEq, ↓reduceIte, krsp]; exact hp.stk_scr
  · simp only [rd_setReg, wr_setReg]; rw [rw']; exact TPre.reads (s₀ := s₀)
  · simp only [wr_setReg]; rw [h.wr, hp.wr]; exact TPre.writes (s₀ := s₀)
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (simp only [gpr_setReg, reduceCtorEq, ↓reduceIte]
       exact k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  · simp only [mem_setReg]; exact h.copied hp

/-- The in-place call, and the contract. -/
theorem call_wp (enc : Bool) {f : Impl.Aes.X86_64.Blocks}
    (ok : ∀ s, (modeX86_64 (AesXts.xtsMode enc)).pre s →
      ∃ t s', Exec isa f.code s t s' ∧ abiPreserved s s' ∧ (modeX86_64 (AesXts.xtsMode enc)).post s s')
    (nosp : NoSp f.code) (depth : f.code.depth ≤ 1) {s : State} (h : Ready s₀ s) :
    WP isa (.call f.name f.code) s fun s' => gprPreserved s₀ s' ∧ (xtsToX86_64 enc).post s₀ s' := by
  refine WP.mono (Unit.xts_call enc ok nosp depth h.pre) fun s' x => ?_
  have hsp : s.gpr .rsp = s₀.gpr .rsp := h.cs .rsp (by simp [calleeSaved])
  have hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  have eW : bytesAt s.mem (W s₀) (16 * (R s₀ + 1)) = bytesAt s₀.mem (W s₀) (16 * (R s₀ + 1)) :=
    Proof.Cmac.bytesAt_frame h.mem.1 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.sch_scr.sub_left (Region.sub_prefix hRb)
      · exact hp.sch_dst.sub_left (Region.sub_prefix hRb)) (by omega)
  have eT : bytesAt s.mem (T s₀) 16 = bytesAt s₀.mem (T s₀) 16 :=
    Proof.Cmac.bytesAt_frame h.mem.1 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.iv_scr
      · exact hp.iv_dst) (by decide)
  refine ⟨⟨fun r hr => by rw [x.saved r hr, h.cs r hr], ?_⟩, ?_, ?_⟩
  · rw [x.frame.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hp.ret_iv
        · exact hp.ret_dst
        · exact hp.ret_scr
        · rw [Unit.stk, hsp]; exact Offset.base_disjoint_below _ (by decide)) (by decide)]
    exact h.mem.1.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.ret_scr
        · exact hp.ret_dst) (by decide)
  · show Spec.Cbc.blocksAt s'.mem (Dd s₀) (N s₀) = _
    rw [x.out, eW, eT, h.mem.2]
  · show bytesAt s'.mem (T s₀) 16 = _
    rw [x.tw, eT]

theorem copyThen_wp (enc : Bool) {f : Impl.Aes.X86_64.Blocks}
    (ok : ∀ s, (modeX86_64 (AesXts.xtsMode enc)).pre s →
      ∃ t s', Exec isa f.code s t s' ∧ abiPreserved s s' ∧ (modeX86_64 (AesXts.xtsMode enc)).post s s')
    (nosp : NoSp f.code) (depth : f.code.depth ≤ 1) :
    WP isa (copyThen f) s₀ fun s' => gprPreserved s₀ s' ∧ (xtsToX86_64 enc).post s₀ s' :=
  WP.seq (WP.mono (stash_wp hp) fun _ h₁ =>
    WP.seq (WP.mono (copy_wp hp h₁) fun _ h₂ =>
      WP.seq (WP.mono (unstash_wp hp h₂) fun _ h₃ => call_wp hp enc ok nosp depth h₃)))

end

/-! ## The code -/

theorem copyThen_mx {f : Impl.Aes.X86_64.Blocks} (hf : f.code.allInstrs (fun i => !loadsMxcsr i) = true) :
    (copyThen f).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [copyThen, Code.allInstrs, hf, Bool.and_true]; decide +kernel

theorem copyThen_spSafe {f : Impl.Aes.X86_64.Blocks} (hf : f.code.all (fun i => !X86_64.isa.writesSp i) = true) :
    (copyThen f).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [copyThen, Code.all, hf, Bool.and_true]; decide +kernel

theorem copyThen_nosp {f : Impl.Aes.X86_64.Blocks} (hf : NoSp f.code) : NoSp (copyThen f) := by
  have hv : f.code.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by
    rw [Code.allInstrs_eq, List.all_eq_true]
    exact fun i hi => by simp [hf i hi]
  have h : (copyThen f).allInstrs (fun i => !Taint.clobbers i .rsp) = true := by
    simp only [copyThen, Code.allInstrs, hv, Bool.and_true]
    decide +kernel
  rw [Code.allInstrs_eq] at h
  exact fun i hi => by simpa using List.all_eq_true.mp h i hi

theorem copyThen_depth {f : Impl.Aes.X86_64.Blocks} (hf : f.code.depth ≤ 1) : (copyThen f).depth ≤ 2 := by
  have : (Impl.ChaCha20Poly1305.X86_64.SealGather.copyBytes .x16 : Prog isa).depth = 0 := by decide +kernel
  simp only [copyThen, Code.depth, Nat.max_le, this]
  omega

theorem copyThen_correct (enc : Bool) {f : Impl.Aes.X86_64.Blocks}
    (ok : ∀ s, (modeX86_64 (AesXts.xtsMode enc)).pre s →
      ∃ t s', Exec isa f.code s t s' ∧ abiPreserved s s' ∧ (modeX86_64 (AesXts.xtsMode enc)).post s s')
    (nosp : NoSp f.code) (depth : f.code.depth ≤ 1) (mx : f.code.allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (hs : (xtsToX86_64 enc).pre s) :
    ∃ t s', Exec isa (copyThen f) s t s' ∧ abiPreserved s s' ∧ (xtsToX86_64 enc).post s s' := by
  obtain ⟨t, s', he, hg, hpo⟩ := copyThen_wp (TPre.of hs) enc ok nosp depth
  exact ⟨t, s', he, abiPreserved_of_exec (copyThen_mx mx) he hg, hpo⟩

/-! ## Constant time -/

theorem stash_taint :
    ∃ h, (taint.check (Taint.ofRegs [.rdi, .rsi, .rcx, .r8, .r9, .r10]) (.block stash) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem copy_taint : ∃ h, (taint.check (Taint.ofRegs [.rsi, .rdi, .rcx])
    (Impl.ChaCha20Poly1305.X86_64.SealGather.copyBytes .x16) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem unstash_taint : ∃ h, (taint.check (Taint.ofRegs [.rdi, .r9]) (.block unstash) h).isSome = true :=
  ⟨_, by taint_decide⟩

section
variable {enc : Bool} {s₀ s₀' : State} (hp : TPre s₀) (hp' : TPre s₀') (hq : (xtsToX86_64 enc).pub s₀ s₀')
include hp hp' hq

theorem copyThen_rel {f : Impl.Aes.X86_64.Blocks}
    (ok : ∀ s, (modeX86_64 (AesXts.xtsMode enc)).pre s →
      ∃ t s', Exec isa f.code s t s' ∧ abiPreserved s s' ∧ (modeX86_64 (AesXts.xtsMode enc)).post s s')
    (ct : ConstantTime isa (modeX86_64 (AesXts.xtsMode enc)).pre (modeX86_64 (AesXts.xtsMode enc)).pub f.code) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (copyThen f) fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := hq
  have t1 := taint_rel [.rdi, .rsi, .rcx, .r8, .r9, .r10] stash_taint (P := fun a b => a = s₀ ∧ b = s₀')
    (fun a b h r hr => by
      obtain ⟨rfl, rfl⟩ := h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact q1
      · exact q2
      · exact q4
      · exact q5
      · exact q6
      · exact q7)
    (F₁ := P1 s₀) (F₂ := P1 s₀') fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨stash_wp hp, stash_wp hp'⟩
  have t2 := taint_rel [.rsi, .rdi, .rcx] copy_taint (P := fun a b => P1 s₀ a ∧ P1 s₀' b)
    (fun a b h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.1.rsi, h.2.rsi, Sr, Sr, q4]
      · rw [h.1.rdi, h.2.rdi, Dd, Dd, q7]
      · rw [h.1.rcx, h.2.rcx, N, N, q5])
    (F₁ := P2 s₀) (F₂ := P2 s₀') fun a b h => ⟨copy_wp hp h.1, copy_wp hp' h.2⟩
  have t3 := taint_rel [.rdi, .r9] unstash_taint (P := fun a b => P2 s₀ a ∧ P2 s₀' b)
    (fun a b h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.rdi, h.2.rdi, Dd, Dd, q7]
      · rw [h.1.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          h.2.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), q6])
    (F₁ := Ready s₀) (F₂ := Ready s₀') fun a b h => ⟨unstash_wp hp h.1, unstash_wp hp' h.2⟩
  have c := Unit.xts_rel enc ok ct (n := f.name) (P := fun a b => Ready s₀ a ∧ Ready s₀' b)
    (fun a b h => ⟨_, _, _, _, _, _, h.1.pre, by
      have := h.2.pre
      simp only [W, T, Dd, S, N, R, ← q1, ← q2, ← q3, ← q5, ← q6, ← q7] at this
      exact this,
      by rw [h.1.cs .rsp (by simp [calleeSaved]), h.2.cs .rsp (by simp [calleeSaved]), q8]⟩)
  exact t1.seq (t2.seq (t3.seq c))

end

theorem copyThen_ct (enc : Bool) {f : Impl.Aes.X86_64.Blocks}
    (ok : ∀ s, (modeX86_64 (AesXts.xtsMode enc)).pre s →
      ∃ t s', Exec isa f.code s t s' ∧ abiPreserved s s' ∧ (modeX86_64 (AesXts.xtsMode enc)).post s s')
    (ct : ConstantTime isa (modeX86_64 (AesXts.xtsMode enc)).pre (modeX86_64 (AesXts.xtsMode enc)).pub f.code) :
    ConstantTime isa (xtsToX86_64 enc).pre (xtsToX86_64 enc).pub (copyThen f) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (copyThen_rel (TPre.of h₁) (TPre.of h₂) hq ok ct _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- The out-of-place functions that copy the blocks from `src` to `dst` and
transform them there by the in-place ones `enc` and `dec` (`copyThen`):
`vg_aes_xts_encrypt_to` and `vg_aes_xts_decrypt_to` with the suffix `suffix`. -/
def ToImpl.ofCopy (suffix : String) (enc : Impl.Aes.X86_64.Blocks) (encDepth : enc.code.depth ≤ 1)
    (encOk : ∀ s, (modeX86_64 (AesXts.xtsMode true)).pre s →
      ∃ t s', Exec isa enc.code s t s' ∧ abiPreserved s s' ∧ (modeX86_64 (AesXts.xtsMode true)).post s s')
    (encCt : ConstantTime isa (modeX86_64 (AesXts.xtsMode true)).pre (modeX86_64 (AesXts.xtsMode true)).pub enc.code)
    (encNosp : NoSp enc.code) (encMxcsr : enc.code.allInstrs (fun i => !loadsMxcsr i) = true)
    (encSpSafe : enc.code.all (fun i => !isa.writesSp i) = true)
    (dec : Impl.Aes.X86_64.Blocks) (decDepth : dec.code.depth ≤ 1)
    (decOk : ∀ s, (modeX86_64 (AesXts.xtsMode false)).pre s →
      ∃ t s', Exec isa dec.code s t s' ∧ abiPreserved s s' ∧ (modeX86_64 (AesXts.xtsMode false)).post s s')
    (decCt : ConstantTime isa (modeX86_64 (AesXts.xtsMode false)).pre (modeX86_64 (AesXts.xtsMode false)).pub
      dec.code)
    (decNosp : NoSp dec.code) (decMxcsr : dec.code.allInstrs (fun i => !loadsMxcsr i) = true)
    (decSpSafe : dec.code.all (fun i => !isa.writesSp i) = true) : ToImpl where
  enc := ⟨"vg_aes_xts_encrypt_to" ++ suffix, copyThen enc⟩
  encDepth := copyThen_depth encDepth
  encOk := copyThen_correct true encOk encNosp encDepth encMxcsr
  encCt := copyThen_ct true encOk encCt
  encNosp := copyThen_nosp encNosp
  encMxcsr := copyThen_mx encMxcsr
  encSpSafe := copyThen_spSafe encSpSafe
  dec := ⟨"vg_aes_xts_decrypt_to" ++ suffix, copyThen dec⟩
  decDepth := copyThen_depth decDepth
  decOk := copyThen_correct false decOk decNosp decDepth decMxcsr
  decCt := copyThen_ct false decOk decCt
  decNosp := copyThen_nosp decNosp
  decMxcsr := copyThen_mx decMxcsr
  decSpSafe := copyThen_spSafe decSpSafe

end VG.Proof.AesXts.X86_64.To
