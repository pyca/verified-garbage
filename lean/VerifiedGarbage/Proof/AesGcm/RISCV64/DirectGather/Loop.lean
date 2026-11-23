module

public import VerifiedGarbage.Impl.AesGcm.RISCV64.DirectGather
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Env
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.AesGcm.RISCV64.CryptOk
public import VerifiedGarbage.Proof.Gather.RISCV64.Loop
import VerifiedGarbage.Proof.Gcm.SealGather
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Loops

/-! # Reading one public descriptor and advancing the gather cursors -/

public section

namespace VG.Proof.AesGcm.RISCV64.DirectGather

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesGcm.RISCV64
open VG.Impl.AesGcm.RISCV64.DirectGather (pieceArgs)

structure ArgsOut (s z : State) (W D S n p cursor : Addr) : Prop where
  source : z.gpr .s4 = S
  size : z.gpr .s5 = n
  offset : z.gpr .s6 = BitVec.ofNat 64 (p.toNat % 16)
  cursorNext : z.gpr .s8 = cursor + 16
  delta : z.gpr .s9 = D + p - S
  other : ∀ r, r ∉ [Reg.s4, .s5, .s6, .s8, .s9, .t0, .t3, .t4] → z.gpr r = s.gpr r
  mem : z.mem = s.mem.writeW (W + 248) (p + n)
  keep : Keeps' s z

theorem pieceArgs_wp {s : State} {W D S n p cursor : Addr}
    (work : s.gpr .s0 = W) (atCursor : s.gpr .s8 = cursor)
    (wa : W.toNat % 8 = 0)
    (writable : Covers [⟨W, 2560⟩] s.wr)
    (readable : Covers [⟨cursor, 16⟩] (s.rd ++ s.wr))
    (ptr : s.mem.readW cursor 64 = S) (len : s.mem.readW (cursor + 8) 64 = n)
    (dest : s.mem.readW (W + 240) 64 = D) (prior : s.mem.readW (W + 248) 64 = p) :
    WP isa (.block pieceArgs) s fun z => ArgsOut s z W D S n p cursor := by
  unfold pieceArgs
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (Bytes.loadLE64_ok (d := .s4) (tmp := .t3) (hi := .t4) (n := .s8) (off := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [atCursor]; exact in_off readable (by decide) (by decide))
    (by rw [atCursor]; exact in_off readable (by decide) (by decide)))
    fun a ⟨ga, oa, ma, ra, wa', sa⟩ => ?_
  have curA := oa .s8 (by decide) (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (Bytes.loadLE64_ok (d := .s5) (tmp := .t3) (hi := .t4) (n := .s8) (off := 8)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [curA, atCursor, ra, wa']; exact in_off readable (by decide) (by decide))
    (by rw [curA, atCursor, ra, wa']; exact in_off readable (by decide) (by decide)))
    fun b ⟨gb, ob, mb, rb, wb, sb⟩ => ?_
  have ga' : a.gpr .s4 = S := by simpa only [atCursor, BitVec.add_zero, ptr] using ga
  have gb' : b.gpr .s5 = n := by rw [gb, curA, atCursor, ma]; exact len
  refine wp_addi (imm := 16) (by decide) fun c hc => ?_
  refine wp_ld (a := W + 248) (off := dstO) (by decide)
    (by rw [hc.other _ (by decide), ob _ (by decide) (by decide) (by decide), oa _ (by decide) (by decide) (by decide), work]; rfl)
    (Spill.al8 (d := 248) wa (by decide))
    (by rw [hc.rd, hc.wr, rb, wb, ra, wa']; exact in_left (in_off writable (by decide) (by decide)))
    fun d hd => ?_
  have pd : d.gpr .t0 = p := by rw [hd.gpr, hc.mem, mb, ma, prior]
  refine wp_andi (by decide) fun e he => ?_
  refine wp_ld (a := W + 240) (off := dataO) (by decide)
    (by rw [he.other _ (by decide), hd.other _ (by decide), hc.other _ (by decide),
      ob _ (by decide) (by decide) (by decide), oa _ (by decide) (by decide) (by decide), work]; rfl)
    (Spill.al8 (d := 240) wa (by decide))
    (by rw [he.rd, he.wr, hd.rd, hd.wr, hc.rd, hc.wr, rb, wb, ra, wa'];
        exact in_left (in_off writable (by decide) (by decide)))
    fun f hf => ?_
  have df : f.gpr .s9 = D := by rw [hf.gpr, he.mem, hd.mem, hc.mem, mb, ma, dest]
  refine wp_add fun g hg => ?_
  refine wp_sub fun h hh => ?_
  refine wp_add fun i hi => ?_
  refine wp_sd (a := W + 248) (off := dstO) (by decide)
    (by rw [hi.other _ (by decide), hh.other _ (by decide), hg.other _ (by decide), hf.other _ (by decide),
      he.other _ (by decide), hd.other _ (by decide), hc.other _ (by decide),
      ob _ (by decide) (by decide) (by decide), oa _ (by decide) (by decide) (by decide), work]; rfl)
    (Spill.al8 (d := 248) wa (by decide))
    (by rw [hi.wr, hh.wr, hg.wr, hf.wr, he.wr, hd.wr, hc.wr, wb, wa'];
        exact in_off writable (by decide) (by decide)) fun z hz => WP.block_nil ?_
  have sg : g.gpr .s4 = S := by rw [hg.other _ (by decide), hf.other _ (by decide),
    he.other _ (by decide), hd.other _ (by decide), hc.other _ (by decide), ob _ (by decide) (by decide) (by decide), ga']
  have nh : h.gpr .s5 = n := by rw [hh.other _ (by decide), hg.other _ (by decide), hf.other _ (by decide),
    he.other _ (by decide), hd.other _ (by decide), hc.other _ (by decide), gb']
  have pf : f.gpr .t0 = p := by rw [hf.other _ (by decide), he.other _ (by decide), pd]
  have ph : h.gpr .t0 = p := by rw [hh.other _ (by decide), hg.other _ (by decide), pf]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hz.gpr, hi.other _ (by decide), hh.other _ (by decide), sg]
  · rw [hz.gpr, hi.other _ (by decide), nh]
  · rw [hz.gpr, hi.other _ (by decide), hh.other _ (by decide), hg.other _ (by decide),
      hf.other _ (by decide), he.gpr, pd]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (BitVec.ofInt 64 15).toNat = 2 ^ 4 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat]
    omega
  · rw [hz.gpr, hi.other _ (by decide), hh.other _ (by decide), hg.other _ (by decide),
      hf.other _ (by decide), he.other _ (by decide), hd.other _ (by decide), hc.gpr,
      ob _ (by decide) (by decide) (by decide), oa _ (by decide) (by decide) (by decide), atCursor]; rfl
  · rw [hz.gpr, hi.other _ (by decide), hh.gpr, hg.gpr, df, pf, sg]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [hz.gpr, hi.other _ hr.2.2.2.2.2.1, hh.other _ hr.2.2.2.2.1, hg.other _ hr.2.2.2.2.1,
      hf.other _ hr.2.2.2.2.1, he.other _ hr.2.2.1, hd.other _ hr.2.2.2.2.2.1, hc.other _ hr.2.2.2.1,
      ob _ hr.2.1 hr.2.2.2.2.2.2.1 hr.2.2.2.2.2.2.2, oa _ hr.1 hr.2.2.2.2.2.2.1 hr.2.2.2.2.2.2.2]
  · rw [hz.mem, hi.gpr, ph, nh, hi.mem, hh.mem, hg.mem, hf.mem, he.mem, hd.mem, hc.mem, mb, ma]
  · exact ⟨by rw [hz.rd, hi.rd, hh.rd, hg.rd, hf.rd, he.rd, hd.rd, hc.rd, rb, ra],
      by rw [hz.wr, hi.wr, hh.wr, hg.wr, hf.wr, he.wr, hd.wr, hc.wr, wb, wa'],
      by rw [hz.sp, hi.sp, hh.sp, hg.sp, hf.sp, he.sp, hd.sp, hc.sp, sb, sa]⟩

end VG.Proof.AesGcm.RISCV64.DirectGather

end

/-! # Appending an out-of-place CTR piece to the gathered ciphertext

All descriptor reads and all plaintext refer to the caller's original
memory. Only the current destination slice and the CTR workspace may change.
-/

public section

namespace VG.Proof.AesGcm.RISCV64.DirectGather

open VG VG.RISCV64 VG.Spec.Gcm VG.Proof.Gcm VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gather.RISCV64 (sb sl pt_succ gl_succ)

theorem cryptPiece_wp {V : Reg → BitVec 64} {sp src dst : Addr} {R i : Nat}
    {icb : Block} {original : Mem} {s : State}
    (L : Lay (V .s2) (V .s1) (V .s0))
    {p n : Nat}
    (h : CrIn true V sp R icb p (sb original src i) (dst + BitVec.ofNat 64 p) n s)
    (hb : BkIn (V .s7) (V .s2) (V .s1) (V .s0) sp R s.mem
      (sb original src i) (dst + BitVec.ofNat 64 p) n s)
    (hp : p = gatheredLen 64 original src i) (hn : n = sl original src i)
    (prior : bytesAt s.mem dst p = gctr (ciphOf s.mem (V .s2) R) icb (gathered 64 original src i))
    (source : bytesAt s.mem (sb original src i) n = bytesAt original (sb original src i) n)
    (apart : ∀ r ∈ crFrame (V .s1) (V .s0) (dst + BitVec.ofNat 64 p) n,
      (⟨dst, p⟩ : Region).Disjoint r)
    (bound : p ≤ 2^64)
    (ctr : Ctr s.mem (V .s1 + 48) (V .s1 + 64) (ciphOf s.mem (V .s2) R) icb p) :
    WP isa (cryptB true true) s fun z =>
      CrOut true V sp R icb p (sb original src i) (dst + BitVec.ofNat 64 p) n s.mem z ∧
      bytesAt z.mem dst (gatheredLen 64 original src (i + 1)) =
        gctr (ciphOf s.mem (V .s2) R) icb (gathered 64 original src (i + 1)) := by
  subst p
  subst n
  refine WP.mono (cryptB_ok L h (fun _ => hb)) fun z hz => ⟨hz, ?_⟩
  rw [gl_succ, Cmac.Stream.bytesAt_append, bytesAt_frame hz.frame apart bound, prior,
    hz.out ctr, source, pt_succ, gctr_append, length_gathered]

end VG.Proof.AesGcm.RISCV64.DirectGather

end

/-! # The public descriptor countdown in direct gather seal -/

public section
namespace VG.Proof.AesGcm.RISCV64.DirectGather

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesGcm.RISCV64

/-- Decrement the scratch slot and leave exactly the new value in t1 for
the back edge. All other registers and all other memory are preserved. -/
theorem decrement_wp {s : State} {p : Addr} {v : BitVec 64}
    (addr : s.gpr .s0 + BitVec.ofNat 64 rO = p)
    (aligned : p.toNat % 8 = 0) (wr : InRegions s.wr p 8)
    (before : s.mem.readW p 64 = v) :
    WP isa (.block [.load .d .t1 .s0 rO, .addi .t1 .t1 (-1), .store .d .t1 .s0 rO]) s fun z =>
      z.gpr .t1 = v - 1 ∧ (∀ r, r ≠ .t1 → z.gpr r = s.gpr r) ∧
      z.mem = s.mem.writeW p (v - 1) ∧ z.rd = s.rd ∧ z.wr = s.wr ∧ z.sp = s.sp := by
  refine wp_ld (by decide) addr aligned (in_left wr) fun a ha => ?_
  refine wp_subi (imm := 1) (by decide) fun b hb => ?_
  have count : b.gpr .t1 = v - 1 := by rw [hb.gpr, ha.gpr, before]; rfl
  refine wp_sd (by decide) (by rw [hb.other _ (by decide), ha.other _ (by decide)]; exact addr)
    aligned (by rw [hb.wr, ha.wr]; exact wr) fun z hz => WP.block_nil ?_
  exact ⟨by rw [hz.gpr, count], fun r hr => by rw [hz.gpr, hb.other r hr, ha.other r hr],
    by rw [hz.mem, count, hb.mem, ha.mem], hz.rd.trans (hb.rd.trans ha.rd),
    hz.wr.trans (hb.wr.trans ha.wr), hz.sp.trans (hb.sp.trans ha.sp)⟩

end VG.Proof.AesGcm.RISCV64.DirectGather

end

/-! # The direct gather loop, one CTR call per caller-supplied descriptor -/

@[expose] public section
namespace VG.Proof.AesGcm.RISCV64.DirectGather

open VG VG.RISCV64 VG.Spec.Gcm VG.Proof.Gcm VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gather.RISCV64 (sb sl gl_succ gl_mono)
open VG.Impl.AesGcm.RISCV64.DirectGather (pieceArgs pieces)

structure LoopArgs where
  original : Mem
  src : Addr
  dst : Addr
  count : Nat
  rounds : Nat
  icb : Block
  V : Reg → Addr
  sp : Addr

namespace LoopArgs

abbrev cursor (a : LoopArgs) (i : Nat) := a.src + BitVec.ofNat 64 (16*i)
abbrev doneBytes (a : LoopArgs) (i : Nat) := gatheredLen 64 a.original a.src i
abbrev total (a : LoopArgs) := a.doneBytes a.count
abbrev S (a : LoopArgs) (i : Nat) := sb a.original a.src i
abbrev n (a : LoopArgs) (i : Nat) := sl a.original a.src i
abbrev out (a : LoopArgs) (i : Nat) := a.dst + BitVec.ofNat 64 (a.doneBytes i)
abbrev w (a : LoopArgs) := a.V .s0
abbrev st (a : LoopArgs) := a.V .s1
abbrev c (a : LoopArgs) := a.V .s2
abbrev b (a : LoopArgs) := a.V .s7
abbrev frame (a : LoopArgs) : List Region :=
  [⟨a.dst, a.total⟩, ⟨a.st + 48, 32⟩, ⟨a.w + 512, 2048⟩, ⟨a.w + 248, 8⟩, ⟨a.w + 256, 8⟩]
def regs (a : LoopArgs) (i : Nat) (delta : Addr) : Reg → Addr :=
  fun r => if r = .s8 then a.cursor i else if r = .s9 then delta else a.V r

end LoopArgs

/-- Fixed bounds, permissions and disjointness from the gather contract. The
original memory supplies all descriptors and plaintext even after setup. -/
structure LoopInput (a : LoopArgs) (entry : State) : Prop where
  L : Lay a.c a.st a.w
  rounds : a.rounds = 10 ∨ a.rounds = 12 ∨ a.rounds = 14
  s3 : a.V .s3 = BitVec.ofNat 64 a.rounds
  countLt : a.count < 2^64
  descFit : a.src.toNat + 16 * a.count ≤ 2^64
  descRd : Covers [⟨a.src, 16 * a.count⟩] (entry.rd ++ entry.wr)
  descApart : ∀ r ∈ a.frame, (⟨a.src, 16 * a.count⟩ : Region).Disjoint r
  descWords : ∀ i < a.count, entry.mem.readW (a.cursor i) 64 = a.S i ∧
    entry.mem.readW (a.cursor i + 8) 64 = BitVec.ofNat 64 (a.n i)
  sources : ∀ i < a.count, DataOk a.st a.w entry (a.S i) (a.n i)
  srcApart : ∀ i < a.count, ∀ r ∈ a.frame, (⟨a.S i, a.n i⟩ : Region).Disjoint r
  sourceBytes : ∀ i < a.count,
    bytesAt entry.mem (a.S i) (a.n i) = bytesAt a.original (a.S i) (a.n i)
  data : DataW a.c a.st a.w entry a.dst a.total
  bk : BkIn a.b a.c a.st a.w a.sp a.rounds entry.mem a.dst a.dst a.total entry

/-- The live descriptor and byte cursors, ciphertext already written, and
all changed memory since the first descriptor. -/
structure LoopAt (a : LoopArgs) (entry : State) (i : Nat) (s : State) : Prop where
  env : ∃ d, Env (a.regs i d) a.sp s
  rd : s.rd = entry.rd
  wr : s.wr = entry.wr
  sp : s.sp = entry.sp
  dest : s.mem.readW (a.w + 240) 64 = a.dst
  offset : s.mem.readW (a.w + 248) 64 = BitVec.ofNat 64 (a.doneBytes i)
  remaining : s.mem.readW (a.w + 256) 64 = BitVec.ofNat 64 (a.count - i)
  ctr : Ctr s.mem (a.st + 48) (a.st + 64) (ciphOf entry.mem a.c a.rounds) a.icb (a.doneBytes i)
  output : bytesAt s.mem a.dst (a.doneBytes i) =
    gctr (ciphOf entry.mem a.c a.rounds) a.icb (gathered 64 a.original a.src i)
  frame : Frame a.frame entry.mem s.mem


namespace LoopInput
variable {a : LoopArgs} {e : State} (h : LoopInput a e)

include h

omit h in
theorem bound {i : Nat} (hi : i < a.count) : a.doneBytes i + a.n i ≤ a.total :=
  gl_succ a.original a.src i ▸ gl_mono a.original a.src (Nat.succ_le_of_lt hi)

theorem sliceData {i : Nat} (hi : i < a.count) : DataW a.c a.st a.w e (a.out i) (a.n i) := by
  have hk := bound (a := a) hi
  by_cases hn : 0 < a.n i
  · exact h.data.sub hk hn
  · have hz : a.n i = 0 := Nat.eq_zero_of_not_pos hn
    have sub := Offset.sub_base a.dst hk
    have A := h.data.ok
    exact ⟨⟨covers_off A.rd hk A.lt, (h.sources i hi).lt, by rw [hz, Nat.add_zero]; exact Nat.le_of_lt (BitVec.isLt _),
      A.st.sub_left sub, A.w.sub_left sub, A.sk.sub_left sub⟩,
      covers_off h.data.wr hk A.lt, h.data.ctx.sub_right sub⟩

omit h in
theorem apartFrame {q : Region} (dst : q.Disjoint ⟨a.dst, a.total⟩)
    (st : q.Disjoint ⟨a.st,80⟩) (w : q.Disjoint ⟨a.w,2560⟩) :
    ∀ r ∈ a.frame, q.Disjoint r := by
  intro r hr
  simp only [LoopArgs.frame, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact dst
  · exact st.sub_right (Lay.stSub (d := 48) (by decide))
  · exact w.sub_right (Lay.wSub (d := 512) (by decide))
  · exact w.sub_right (Lay.wSub (d := 248) (by decide))
  · exact w.sub_right (Lay.wSub (d := 256) (by decide))

theorem ctxApart : ∀ r ∈ a.frame, (⟨a.c,256⟩ : Region).Disjoint r :=
  apartFrame h.data.ctx h.L.cs h.L.cw'

theorem bkApart : ∀ r ∈ a.frame, (⟨a.b,960⟩ : Region).Disjoint r :=
  apartFrame h.bk.d h.bk.st h.bk.w

theorem slotCr {i d : Nat} (hi : i < a.count) (lo : 96 ≤ d) (top : d+8 ≤ 512) :
    ∀ r ∈ crFrame a.st a.w (a.out i) (a.n i), (⟨a.w + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ((h.sliceData hi).ok.w.symm).sub_left (Lay.wSub (by omega))
  · exact (h.L.sb.symm.sub_left (Lay.bSub lo (by omega))).sub_right (Lay.stSub (by decide))
  · exact Offset.disjoint _ (Or.inl top) (by omega) (by decide)

theorem priorApart {i : Nat} (hi : i < a.count) :
    ∀ r ∈ crFrame a.st a.w (a.out i) (a.n i), (⟨a.dst,a.doneBytes i⟩ : Region).Disjoint r := by
  intro r hr
  have hj := bound (a := a) hi
  have hn := h.data.ok.lt
  have A := h.data.ok.take (k := a.doneBytes i) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.base_disjoint _ (Nat.le_refl _) (by omega)
  · exact A.st.sub_right (Lay.stSub (by decide))
  · exact A.w.sub_right (Lay.wSub (by decide))

omit h in
theorem frameCr {i : Nat} (hi : i < a.count) {m t : Mem}
    (f : Frame (crFrame a.st a.w (a.out i) (a.n i)) m t) : Frame a.frame m t := by
  apply f.sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, .head _, Offset.sub_base _ (bound (a := a) hi)⟩
  · exact ⟨_, .tail _ (.head _), fun _ h => h⟩
  · exact ⟨_, .tail _ (.tail _ (.head _)), fun _ h => h⟩

theorem bkSlice {i : Nat} (hi : i < a.count) {s : State} (hf : Frame a.frame e.mem s.mem)
    (rd : s.rd = e.rd) (wr : s.wr = e.wr) :
    BkIn a.b a.c a.st a.w a.sp a.rounds s.mem (a.S i) (a.out i) (a.n i) s := by
  have b := h.bk.frame h.rounds hf h.bkApart h.ctxApart rd wr
  exact ⟨b.rd,b.al,b.st,b.w,b.sk,b.d.sub_right (Offset.sub_base _ (bound (a := a) hi)), b.keys⟩

theorem ctrSlot {d i : Nat} (lo : 96 ≤ d) (top : d+8 ≤ 2560) {s t : Mem}
    {ciph : Block → Block} (f : Frame [⟨a.w + BitVec.ofNat 64 d, 8⟩] s t)
    (ctr : Ctr s (a.st+48) (a.st+64) ciph a.icb i) : Ctr t (a.st+48) (a.st+64) ciph a.icb i := by
  have eq (off : Nat) (within : off + 16 ≤ 80) :
      blockAt t (a.st + BitVec.ofNat 64 off) = blockAt s (a.st + BitVec.ofNat 64 off) := by
    apply blockAt_frame f
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact (h.L.sb.sub_left (Lay.stSub within)).sub_right (Lay.bSub lo top)
  exact ctr.congr (eq 48 (by decide)) (eq 64 (by decide))

end LoopInput

variable {a : LoopArgs} {e s z : State} {i : Nat}

theorem args_wp (h : LoopInput a e) (hi : i < a.count) (u : LoopAt a e i s) :
    WP isa (.block pieceArgs) s fun z =>
      ArgsOut s z a.w a.dst (a.S i) (BitVec.ofNat 64 (a.n i))
        (BitVec.ofNat 64 (a.doneBytes i)) (a.cursor i) := by
  obtain ⟨d, env⟩ := u.env
  have fit := h.descFit
  have cov : Covers [⟨a.cursor i,16⟩] (s.rd ++ s.wr) := by
    rw [u.rd,u.wr]
    intro x n hx
    obtain ⟨r,hr,hx⟩ := hx
    obtain rfl := List.mem_singleton.mp hr
    refine h.descRd x n ⟨_, .head _, ?_⟩
    change (x - a.cursor i).toNat + n ≤ 16 at hx
    change (x - a.src).toNat + n ≤ 16*a.count
    have ex : x - a.src = (x - a.cursor i) + BitVec.ofNat 64 (16*i) := by
      unfold LoopArgs.cursor; rw [Offset.sub_add_eq]; exact (BitVec.sub_add_cancel _ _).symm
    rw [ex, BitVec.toNat_add]
    have hdiv := Nat.mod_le ((x - a.cursor i).toNat + (BitVec.ofNat 64 (16*i)).toNat) (2^64)
    have hib : 16*i < 2^64 := by omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hib] at *
    omega
  have w₀ := u.frame.readW (w := 64) (Offset.contains_base a.src (d := 16*i) (by omega) (by omega))
    h.descApart (by decide)
  have w₈ := u.frame.readW (w := 64) (Offset.contains_base a.src (d := 16*i+8) (by omega) (by omega))
    h.descApart (by decide)
  have cursor₈ : a.cursor i + 8 = a.src + BitVec.ofNat 64 (16*i+8) := add_ofNat_assoc _ _ _
  exact pieceArgs_wp env.s0 (env.fr _ (by decide)) h.L.wal env.perm.w cov
    (w₀.trans (h.descWords i hi).1)
    ((by rw [cursor₈]; exact w₈ : s.mem.readW (a.cursor i+8) 64 = e.mem.readW (a.cursor i+8) 64).trans
      (h.descWords i hi).2) u.dest u.offset

abbrev stepRegs (a : LoopArgs) (i : Nat) := a.regs (i+1) (a.out i - a.S i)
abbrev ArgsAfter (a : LoopArgs) (i : Nat) (s z : State) :=
  ArgsOut s z a.w a.dst (a.S i) (BitVec.ofNat 64 (a.n i)) (BitVec.ofNat 64 (a.doneBytes i)) (a.cursor i)

theorem argsFrame (v : ArgsAfter a i s z) : Frame [⟨a.w+248,8⟩] s.mem z.mem := by
  rw [v.mem]
  exact (Frame.refl _ _).writeW (.head _) _ (Region.contains_self _ _)

theorem argsFullFrame (u : LoopAt a e i s) (v : ArgsAfter a i s z) : Frame a.frame e.mem z.mem :=
  u.frame.trans ((argsFrame v).mono (by simp [LoopArgs.frame]))

theorem cryptReady (h : LoopInput a e) (hi : i < a.count) (u : LoopAt a e i s) (v : ArgsAfter a i s z) :
    CrIn true (stepRegs a i) a.sp a.rounds a.icb (a.doneBytes i) (a.S i) (a.out i) (a.n i) z := by
  obtain ⟨d, env⟩ := u.env
  have regs : Env (stepRegs a i) a.sp z := by
    refine ⟨?_, v.keep.sp.trans env.sp, env.perm.of_eq v.keep.rd v.keep.wr, v.keep.sp ▸ env.stk⟩
    intro r hr
    by_cases r8 : r = .s8
    · subst r
      change z.gpr .s8 = a.cursor (i+1)
      rw [v.cursorNext]; exact (add_ofNat_assoc _ _ 16).trans (by simp only [LoopArgs.cursor, Nat.mul_succ])
    by_cases r9 : r = .s9
    · subst r; exact v.delta
    have other : r ∉ [Reg.s4,.s5,.s6,.s8,.s9,.t0,.t3,.t4] := by
      revert hr r8 r9
      cases r <;> decide
    rw [v.other r other,env.fr r hr]
    simp [stepRegs,LoopArgs.regs,r8,r9]
  have data := h.sliceData hi
  have less : a.doneBytes i < 2^64 := Nat.lt_of_le_of_lt (gl_mono _ _ (Nat.le_of_lt hi)) h.data.ok.lt
  refine ⟨regs,v.source,v.size,?_,h.s3,h.rounds,
    data.of_eq (v.keep.rd.trans u.rd) (v.keep.wr.trans u.wr) (v.keep.sp.trans u.sp),
    (h.sources i hi).of_eq (v.keep.rd.trans u.rd) (v.keep.wr.trans u.wr) (v.keep.sp.trans u.sp),
    (h.srcApart i hi _ (.head _)).sub_right (Offset.sub_base _ (LoopInput.bound hi)),fun _ => rfl⟩
  rw [v.offset,BitVec.toNat_ofNat,Nat.mod_eq_of_lt less]

theorem cryptCtr (h : LoopInput a e) (u : LoopAt a e i s) (v : ArgsAfter a i s z) :
    Ctr z.mem (a.st+48) (a.st+64) (ciphOf z.mem a.c a.rounds) a.icb (a.doneBytes i) := by
  rw [ciph_frame (argsFullFrame u v) h.ctxApart h.rounds]
  exact h.ctrSlot (d := 248) (by decide) (by decide) (argsFrame v) u.ctr

theorem crypt_wp (h : LoopInput a e) (hi : i < a.count) (u : LoopAt a e i s) (v : ArgsAfter a i s z) :
    WP isa (cryptB true true) z fun t =>
      CrOut true (stepRegs a i) a.sp a.rounds a.icb (a.doneBytes i) (a.S i) (a.out i) (a.n i) z.mem t ∧
      bytesAt t.mem a.dst (a.doneBytes (i+1)) =
        gctr (ciphOf e.mem a.c a.rounds) a.icb (gathered 64 a.original a.src (i+1)) := by
  have fr := argsFullFrame u v
  have ciph := ciph_frame fr h.ctxApart h.rounds
  have cp := gl_mono a.original a.src (Nat.le_of_lt hi)
  have less := h.data.ok.lt
  have bound : a.doneBytes i ≤ 2^64 := Nat.le_trans cp (Nat.le_of_lt less)
  have bk := h.bkSlice hi fr (v.keep.rd.trans u.rd) (v.keep.wr.trans u.wr)
  rw [← ciph]
  refine cryptPiece_wp (V := stepRegs a i) h.L (cryptReady h hi u v) bk rfl rfl ?_ ?_ (h.priorApart hi) bound
    (cryptCtr h u v)
  · change bytesAt z.mem a.dst (a.doneBytes i) = gctr (ciphOf z.mem a.c a.rounds) a.icb _
    rw [bytesAt_frame (argsFrame v) _ bound, ciph]
    · exact u.output
    · intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact (h.data.ok.w.sub_left (Region.sub_prefix cp)).sub_right (Lay.wSub (d := 248) (by decide))
  · exact (bytesAt_frame fr (h.srcApart i hi) (Nat.le_of_lt (h.sources i hi).lt)).trans (h.sourceBytes i hi)

abbrev stepCode : Prog isa :=
  .seq (.block pieceArgs) (.seq (cryptB true true)
    (.block [.load .d .t1 .s0 rO,.addi .t1 .t1 (-1),.store .d .t1 .s0 rO]))

theorem step_wp (h : LoopInput a e) (hi : i < a.count) (u : LoopAt a e i s) :
    WP isa stepCode s fun t => LoopAt a e (i+1) t ∧ t.gpr .t1 = BitVec.ofNat 64 (a.count-(i+1)) := by
  refine WP.seq (WP.mono (args_wp h hi u) fun z v => WP.seq (WP.mono
    (WP.with_rdwr' (crypt_wp h hi u v)) fun t ⟨⟨cr,cout⟩,rd,wr⟩ => ?_))
  have slot (j : Nat) (lo : 96 ≤ j) (top : j+8 ≤ 512) :
      t.mem.readW (a.w + BitVec.ofNat 64 j) 64 = z.mem.readW (a.w + BitVec.ofNat 64 j) 64 :=
    cr.frame.readW (Region.contains_self _ _) (h.slotCr hi lo top) (by decide)
  have pre : t.mem.readW (a.w+256) 64 = BitVec.ofNat 64 (a.count-i) := by
    erw [slot 256 (by decide) (by decide), v.mem,
      Mem.readW_writeW_sep (w := 64) (w' := 64) (Offset.sep a.w (d := 256) (e := 248) (by decide) (by decide) (by decide)) (by decide)]
    exact u.remaining
  have small : a.count-i ≥ 1 := by omega
  have sub : BitVec.ofNat 64 (a.count-i) - 1 = BitVec.ofNat 64 (a.count-(i+1)) := by
    change BitVec.ofNat 64 (a.count-i) - BitVec.ofNat 64 1 = _
    rw [Offset.ofNat_sub_ofNat small,Nat.sub_sub]
  refine WP.mono (decrement_wp (p := a.w+256) (by rw [cr.env.s0]; rfl)
    (Spill.al8 (d := 256) h.L.wal (by decide)) (in_off (d := 256) cr.env.perm.w (by decide) (by decide)) pre)
    fun y ⟨t1,keep,mem,yrd,ywr,ysp⟩ => ?_
  have yf : Frame [⟨a.w+256,8⟩] t.mem y.mem := by
    rw [mem]; exact (Frame.refl _ _).writeW (.head _) _ (Region.contains_self _ _)
  have tf := (argsFullFrame u v).trans (LoopInput.frameCr hi cr.frame)
  have ep := u.env.choose_spec.sp
  have nsp : t.sp = e.sp := cr.env.sp.trans (ep.symm.trans u.sp)
  have pr := gl_succ a.original a.src i
  have ciph := ciph_frame (argsFullFrame u v) h.ctxApart h.rounds
  refine ⟨⟨⟨_, cr.env.keep (fun r hr => keep r fun he => by subst he; exact (by decide : Reg.t1 ∉ frozen) hr)
    ysp yrd ywr⟩,yrd.trans (rd.trans (v.keep.rd.trans u.rd)),ywr.trans (wr.trans (v.keep.wr.trans u.wr)),
    ysp.trans nsp,?_,?_,?_,?_,?_,tf.trans (yf.mono (by simp [LoopArgs.frame]))⟩,t1.trans sub⟩
  · erw [mem, Mem.readW_writeW_sep (w := 64) (w' := 64) (Offset.sep a.w (d := 240) (e := 256) (by decide) (by decide) (by decide)) (by decide),
      slot 240 (by decide) (by decide),v.mem,
      Mem.readW_writeW_sep (w := 64) (w' := 64) (Offset.sep a.w (d := 240) (e := 248) (by decide) (by decide) (by decide)) (by decide)]
    exact u.dest
  · erw [mem, Mem.readW_writeW_sep (w := 64) (w' := 64) (Offset.sep a.w (d := 248) (e := 256) (by decide) (by decide) (by decide)) (by decide),
      slot 248 (by decide) (by decide),v.mem,Mem.readW_writeW_self64, ← BitVec.ofNat_add]
    exact congrArg (BitVec.ofNat 64) pr.symm
  · rw [mem,Mem.readW_writeW_self64,sub]
  · apply h.ctrSlot (d := 256) (by decide) (by decide) yf
    have ct := cr.ctr (cryptCtr h u v)
    change Ctr t.mem (a.st+48) (a.st+64) (ciphOf z.mem a.c a.rounds) a.icb (a.doneBytes i+a.n i) at ct
    rwa [ciph,← pr] at ct
  · rw [bytesAt_frame yf]
    · exact cout
    · intro r hr; obtain rfl := List.mem_singleton.mp hr
      exact (h.data.ok.w.sub_left (Region.sub_prefix (gl_mono _ _ (Nat.succ_le_of_lt hi)))).sub_right
        (Lay.wSub (d := 256) (by decide))
    · exact Nat.le_trans (gl_mono _ _ (Nat.succ_le_of_lt hi)) (Nat.le_of_lt h.data.ok.lt)

theorem countLoad_wp (h : LoopInput a e) (u : LoopAt a e 0 s) :
    WP isa (.block [.load .d .t1 .s0 rO]) s fun z =>
      LoopAt a e 0 z ∧ z.gpr .t1 = BitVec.ofNat 64 a.count := by
  obtain ⟨d,env⟩ := u.env
  refine Steps.wp_ld (a := a.w+256) (by decide) (by rw [env.s0]; rfl)
    (Spill.al8 (d := 256) h.L.wal (by decide)) (in_left (in_off (d := 256) env.perm.w (by decide) (by decide)))
    fun z vz => WP.block_nil ?_
  refine ⟨⟨⟨d,env.keep (fun r hr => vz.other r fun he => by subst he; exact (by decide : Reg.t1 ∉ frozen) hr)
    vz.sp vz.rd vz.wr⟩,vz.rd.trans u.rd,vz.wr.trans u.wr,vz.sp.trans u.sp,?_,?_,?_,?_,?_,?_⟩,?_⟩
  · rw [vz.mem]; exact u.dest
  · rw [vz.mem]; exact u.offset
  · rw [vz.mem]; exact u.remaining
  · rw [vz.mem]; exact u.ctr
  · rw [vz.mem]; exact u.output
  · rw [vz.mem]; exact u.frame
  · rw [vz.gpr]; exact u.remaining

theorem pieces_wp (h : LoopInput a e) (u : LoopAt a e 0 s) :
    WP isa pieces s (LoopAt a e a.count) := by
  refine WP.seq (WP.mono (countLoad_wp h u) fun t ⟨v,t1⟩ =>
    WP.ite (decide (a.count=0)) (Steps.eval_zero_ofNat _ _ h.countLt t1) (fun yes => ?_) (fun no => ?_))
  · have eq : a.count=0 := by simpa using yes
    rw [eq]; exact WP.block_nil v
  · have ne : a.count≠0 := by simpa using no
    refine WP.loop (M := isa) (c := .nonzero .t1)
      (fun k z => ∃ j, k=a.count-j ∧ j<a.count ∧ LoopAt a e j z) ?_ (a.count-0) _
      ⟨0,rfl,by omega,v⟩
    rintro k z ⟨j,rfl,hj,hz⟩
    refine WP.mono (step_wp h hj hz) fun t ⟨ht,h1⟩ => ?_
    have lim := h.countLt
    have ev := Steps.eval_nonzero_ofNat t .t1 (by omega : a.count-(j+1)<2^64) h1
    by_cases last : j+1=a.count
    · exact Or.inl ⟨by rw [ev]; simp [last], last ▸ ht⟩
    · exact Or.inr ⟨by rw [ev]; simp; omega, a.count-(j+1), by omega,j+1,rfl,by omega,ht⟩

end VG.Proof.AesGcm.RISCV64.DirectGather

end
