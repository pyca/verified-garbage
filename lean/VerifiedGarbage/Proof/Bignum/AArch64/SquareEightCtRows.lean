module

import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightRows
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightHead
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtContext
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightRows
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightHead
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtContext
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCtContext
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightRowMath
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightSetup
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightInternal
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCtContext
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightRowMath
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightSetup
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightInternal

/-! ### `Bignum.AArch64.SquareEightCtHead`, which this module and modules that import it used -/

section

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareEight
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.BlockedRedc (FastW blocks)
open VG.Proof.Bignum.AArch64.ProductEight (productBase fast_width input_separation)

structure BasicCtx (a : Nat) (p : Ws × Nat) (s : State) : Prop where
  fast : FastW p.1 s
  index : p.2 < blocks p.1
  ptr : s.gpr .x8 = off p.1.B (slot (8*blocks p.1) a+64*p.2)
  count : s.gpr .x12 = BitVec.ofNat 64 (blocks p.1-p.2)
  zero : s.gpr .x7 = 0

structure PtrCtx (a : Nat) (twice : Bool) (p : Ws × Nat) (s : State) : Prop where
  basic : BasicCtx a p s
  tptr : s.gpr .x16 = off p.1.B (productBase (blocks p.1)+(if twice then 128*p.2 else 64*p.2))
  nptr : s.gpr .x17 = off p.1.B (slot (8*blocks p.1) a)

structure InternalCtx (a : Nat) (p : Ws × Nat) (s : State) : Prop where
  ptrs : PtrCtx a true p s
  bound : wv s.mem p.1.B (productBase (blocks p.1)) (16*blocks p.1+2) < 2 ^ (64*(16*p.2))

structure HeadCtx (a : Nat) (p : Ws × Nat) (s : State) : Prop where
  ptrs : PtrCtx a false p s
  iterations : s.gpr .x15 = BitVec.ofNat 64 p.2
  pending : s.gpr .x10 = 0

theorem output_ctx_mem {a : Nat} (ha : a < 8) (twice : Bool)
    (p : Ws × Nat) (s : State) (h : BasicCtx a p s) :
    WP isa (.block (VG.Impl.Bignum.AArch64.ProductEight.outputPtr twice a)) s (fun t => PtrCtx a twice p t ∧ t.mem = s.mem) := by
  obtain ⟨he, _, hk⟩ := fast_width h.fast
  obtain ⟨mi, hg, hz⟩ := h.fast.1
  have hh : Hdr s.mem p.1.B (8*blocks p.1) mi := he.symm ▸ hg.hdr
  have hsize : slot (8*blocks p.1) 8 ≤ p.1.Z := he.symm ▸ hz
  refine WP.mono (outputPtr_ok hg.scr hg.x0 hh hsize ha (by have := h.index; omega_using [hk, this]) h.ptr twice)
    fun t ⟨⟨ht16, ht17, htm⟩, kt⟩ => ?_
  exact ⟨⟨⟨⟨⟨mi, ⟨hg.scr.congr kt.wr, (kt.gpr _ (by decide)).trans hg.x0, htm ▸ hg.hdr⟩, hz⟩, h.fast.2⟩,
    h.index, (kt.gpr _ (by decide)).trans h.ptr, (kt.gpr _ (by decide)).trans h.count,
    (kt.gpr _ (by decide)).trans h.zero⟩, ht16, ht17⟩, htm⟩

theorem initial_ptr_ctx {a : Nat} (ha : a < 8) (p : Ws × Nat) (s : State)
    (h : p.2 < blocks p.1 ∧ LoopCtx a p.1 p.2 s) :
    WP isa (.block (VG.Impl.Bignum.AArch64.ProductEight.outputPtr true a)) s (InternalCtx a p) := by
  have hb : BasicCtx a p s := ⟨h.2.fast, h.1, h.2.ptr, h.2.count, h.2.zero⟩
  refine WP.mono (output_ctx_mem ha true p s hb) fun t ⟨ht, hm⟩ => ?_
  refine ⟨ht, ?_⟩
  rw [hm, h.2.value]
  simpa only [show 128*(8*p.2) = 64*(16*p.2) by omega_using []] using
    cross_words_lt_full s.mem p.1.B (slot (8*blocks p.1) a) (8*p.2)

abbrev AfterInternal (a : Nat) (p : Ws × Nat) (s : State) := BasicCtx a p s ∧ s.gpr .x10 = 0

def headInternal : List Instr := VG.Impl.Bignum.AArch64.SquareEight.code ++ [movi .x10 0]
def headSuffix (a : Nat) : List Instr := VG.Impl.Bignum.AArch64.ProductEight.outputPtr false a ++
  [ldh .x15 sW, .lsr .x .x15 .x15 3, .sub .x .x15 .x15 .x12]

theorem internal_ctx {a : Nat} (ha : a < 8) (p : Ws × Nat) (s : State) (h : InternalCtx a p s) :
    WP isa (.block headInternal) s (AfterInternal a p) := by
  have hb := h.ptrs.basic
  obtain ⟨he, _, _⟩ := fast_width hb.fast
  obtain ⟨mi, hg, hz⟩ := hb.fast.1
  have hsize : slot (8*blocks p.1) 8 ≤ p.1.Z := he.symm ▸ hz
  have hA : slot (8*blocks p.1) a+64*blocks p.1 ≤ p.1.Z := by
    have := slot_le (w := 8*blocks p.1) ha
    omega_using [hsize, this]
  have hP : productBase (blocks p.1)+8*(16*blocks p.1+2) ≤ p.1.Z := by
    unfold productBase slot Public.aAcc at *
    omega_using [he, hz]
  have hj := hb.index
  apply WP.block_append
  refine WP.mono (internal_ok hg.scr hb.ptr h.ptrs.tptr hb.zero (by omega_using [hA, hj]) hP (by omega_using [hj]) h.bound)
    fun t ⟨_, hto, kt⟩ => ?_
  have hout := hto.mono (o' := productBase (blocks p.1)) (n' := 8*(16*blocks p.1+2)) (by omega_using []) (by omega_using [hj])
  have hHt : Hdr t.mem p.1.B p.1.w mi := he ▸ frame_header hout (he.symm ▸ hg.hdr)
  refine WP.mono (clearPending_ok t) fun u ⟨⟨hu10, hum⟩, ku⟩ => ?_
  have kk := kt.trans ku
  exact ⟨⟨⟨⟨mi, ⟨hg.scr.congr kk.wr, (kk.gpr _ (by decide)).trans hg.x0, hum ▸ hHt⟩, hz⟩, hb.fast.2⟩,
    hj, (kk.gpr _ (by decide)).trans hb.ptr, (kk.gpr _ (by decide)).trans hb.count,
    (kk.gpr _ (by decide)).trans hb.zero⟩, hu10⟩

theorem head_suffix_ctx {a : Nat} (ha : a < 8) (p : Ws × Nat) (s : State) (h : AfterInternal a p s) :
    WP isa (.block (headSuffix a)) s (HeadCtx a p) := by
  apply WP.block_append
  refine WP.mono (WP.keep [.x13, .x16, .x17] (output_ctx_mem ha false p s h.1) rfl rfl rfl)
    fun t ⟨⟨ht, _⟩, kt⟩ => ?_
  obtain ⟨he, _, hk⟩ := fast_width ht.basic.fast
  obtain ⟨mi, hg, hz⟩ := ht.basic.fast.1
  refine WP.mono (rowCount_ok hg.scr hg.x0 (he.symm ▸ hg.hdr) (he.symm ▸ hz) hk
    (Nat.le_of_lt ht.basic.index) ht.basic.count) fun u ⟨⟨hu15, hum⟩, ku⟩ => ?_
  refine ⟨⟨⟨⟨⟨mi, ⟨hg.scr.congr ku.wr, (ku.gpr _ (by decide)).trans hg.x0, hum ▸ hg.hdr⟩, hz⟩,
    ht.basic.fast.2⟩, ht.basic.index, (ku.gpr _ (by decide)).trans ht.basic.ptr,
    (ku.gpr _ (by decide)).trans ht.basic.count, (ku.gpr _ (by decide)).trans ht.basic.zero⟩,
    (ku.gpr _ (by decide)).trans ht.tptr, (ku.gpr _ (by decide)).trans ht.nptr⟩,
    hu15, (ku.gpr _ (by decide)).trans ((kt.gpr _ (by decide)).trans h.2)⟩

end VG.Proof.Bignum.AArch64.SquareEight

end

end

/-! ### `Bignum.AArch64.SquareEightCtOff`, which only this module used -/

section

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareEight
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.BlockedRedc (FastW blocks)
open VG.Proof.Bignum.AArch64.ProductEight (productBase fast_width input_separation)

def offCode : Prog isa := .ite (.nonzero .x .x15)
  (countLoop .x15 VG.Impl.Bignum.AArch64.ProductEight.offBlock) (.block [])
def tailFinish : List Instr := SquareEightRaw.finishCarry ++
  [.addImm .x .x8 .x8 64, .subImm .x .x12 .x12 1]

theorem off_ctx {a : Nat} (ha : a < 8) (ha1 : a ≠ Public.aAcc) (ha2 : a ≠ Public.aTmp)
    (p : Ws × Nat) (s : State) (h : HeadCtx a p s) : WP isa offCode s (BasicCtx a p) := by
  have hb := h.ptrs.basic
  obtain ⟨he, _, hk⟩ := fast_width hb.fast
  obtain ⟨mi, hg, hz⟩ := hb.fast.1
  have hsize : slot (8*blocks p.1) 8 ≤ p.1.Z := he.symm ▸ hz
  have hA := input_separation hb.fast ha1 ha2
  have hAZ : slot (8*blocks p.1) a+64*blocks p.1 ≤ p.1.Z := by
    have := slot_le (w := 8*blocks p.1) ha
    omega_using [hsize, this]
  have hP : productBase (blocks p.1)+8*(16*blocks p.1+2) ≤ p.1.Z := by
    unfold productBase slot Public.aAcc at *
    omega_using [he, hz]
  have hj := hb.index
  refine WP.mono (offDiagonal_full hg.scr hb.ptr hb.zero h.pending h.ptrs.tptr h.ptrs.nptr h.iterations
    (by omega_using [hAZ, hj]) hP (by omega_using [hAZ, hj]) (by omega_using [hA, hj]) (by omega_using [hA, hj]) (by omega_using [hk, hj]) (by omega_using [hj])) fun t ⟨_, hto, kt⟩ => ?_
  have hout := hto.mono (o' := productBase (blocks p.1)) (n' := 8*(16*blocks p.1+2)) (by omega_using []) (by omega_using [hj])
  have hHt : Hdr t.mem p.1.B p.1.w mi := he ▸ frame_header hout (he.symm ▸ hg.hdr)
  exact ⟨⟨⟨mi, ⟨hg.scr.congr kt.wr, (kt.gpr _ (by decide)).trans hg.x0, hHt⟩, hz⟩, hb.fast.2⟩,
    hj, (kt.gpr _ (by decide)).trans hb.ptr, (kt.gpr _ (by decide)).trans hb.count,
    (kt.gpr _ (by decide)).trans hb.zero⟩

end VG.Proof.Bignum.AArch64.SquareEight

end

end

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareEight
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.Bignum.AArch64.BlockedRedc (FastW blocks)

abbrev RowPre (a : Nat) (p : Ws × Nat) (s : State) := p.2 < blocks p.1 ∧ LoopCtx a p.1 p.2 s

theorem pins_row (a : Nat) : Pins (RowPre a) [.x0] :=
  fun p s t hs ht => pins_goodW p.1 s t hs.2.fast.1 ht.2.fast.1

theorem pins_basic (a : Nat) : Pins (BasicCtx a) [.x0] :=
  fun p s t hs ht => pins_goodW p.1 s t hs.fast.1 ht.fast.1

theorem pins_internal (a : Nat) : Pins (InternalCtx a) [.x8, .x16] := by
  intro p s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hs.ptrs.basic.ptr.trans ht.ptrs.basic.ptr.symm
  · exact hs.ptrs.tptr.trans ht.ptrs.tptr.symm

theorem pins_after_internal (a : Nat) : Pins (AfterInternal a) [.x0] :=
  fun p s t hs ht => pins_basic a p s t hs.1 ht.1

theorem pins_head (a : Nat) : Pins (HeadCtx a) [.x8, .x16, .x17, .x15] := by
  intro p s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hs.ptrs.basic.ptr.trans ht.ptrs.basic.ptr.symm
  · exact hs.ptrs.tptr.trans ht.ptrs.tptr.symm
  · exact hs.ptrs.nptr.trans ht.ptrs.nptr.symm
  · exact hs.iterations.trans ht.iterations.symm

theorem pins_tail (a : Nat) : Pins (PtrCtx a true) [.x8, .x12, .x16] := by
  intro p s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hs.basic.ptr.trans ht.basic.ptr.symm
  · exact hs.basic.count.trans ht.basic.count.symm
  · exact hs.tptr.trans ht.tptr.symm

theorem head_ct {a : Nat} (ha : a < 8)
    {ho hh : VG.Taint.Hint VG.AArch64.Taint.T}
    (hO : (taint.check (Taint.ofRegs [.x0])
      (.block (VG.Impl.Bignum.AArch64.ProductEight.outputPtr true a)) ho).isSome = true)
    (hH : (taint.check (Taint.ofRegs [.x0]) (.block (headSuffix a)) hh).isSome = true) :
    RelCT isa (Two (RowPre a)) (.block (SquareEightRaw.rowHead a)) (Two (HeadCtx a)) := by
  have heq : SquareEightRaw.rowHead a =
      (VG.Impl.Bignum.AArch64.ProductEight.outputPtr true a ++ headInternal) ++ headSuffix a := by
    simp only [SquareEightRaw.rowHead, headInternal, headSuffix, List.append_assoc]
  rw [heq]
  apply RelCT.block_append
  refine RelCT.seq ?_ (two_piece _ (pins_after_internal a) hH (head_suffix_ctx ha))
  apply RelCT.block_append
  exact RelCT.seq (two_piece _ (pins_row a) hO (initial_ptr_ctx ha))
    (two_piece _ (pins_internal a) (by taint_decide) (internal_ctx ha))

theorem tail_ct {a : Nat} (ha : a < 8)
    {ho : VG.Taint.Hint VG.AArch64.Taint.T}
    (hO : (taint.check (Taint.ofRegs [.x0])
      (.block (VG.Impl.Bignum.AArch64.ProductEight.outputPtr true a)) ho).isSome = true) :
    RelCT isa (Two (BasicCtx a)) (.block (SquareEightRaw.rowTail a)) (fun _ _ => True) := by
  have heq : SquareEightRaw.rowTail a =
      VG.Impl.Bignum.AArch64.ProductEight.outputPtr true a ++ tailFinish := by
    simp only [SquareEightRaw.rowTail, tailFinish, List.append_assoc]
  rw [heq]
  apply RelCT.block_append
  exact RelCT.seq (two_piece _ (pins_basic a) hO
    (fun p s h => WP.mono (output_ctx_mem ha true p s h) fun _ ht => ht.1))
    (two_taint _ (pins_tail a) (by taint_decide))

theorem row_ct {a : Nat} (ha : a < 8) (ha1 : a ≠ Public.aAcc) (ha2 : a ≠ Public.aTmp)
    {ho hh : VG.Taint.Hint VG.AArch64.Taint.T}
    (hO : (taint.check (Taint.ofRegs [.x0])
      (.block (VG.Impl.Bignum.AArch64.ProductEight.outputPtr true a)) ho).isSome = true)
    (hH : (taint.check (Taint.ofRegs [.x0]) (.block (headSuffix a)) hh).isSome = true) :
    RelCT isa (Two (RowPre a)) (rowBody a) (fun _ _ => True) := by
  unfold rowBody
  exact RelCT.seq (head_ct ha hO hH)
    (RelCT.seq (two_post (two_taint _ (pins_head a) (by taint_decide)) (off_ctx ha ha1 ha2))
      (tail_ct ha hO))

theorem rows_ct {a : Nat} (ha : a < 8) (ha1 : a ≠ Public.aAcc) (ha2 : a ≠ Public.aTmp)
    {ho hh : VG.Taint.Hint VG.AArch64.Taint.T}
    (hO : (taint.check (Taint.ofRegs [.x0])
      (.block (VG.Impl.Bignum.AArch64.ProductEight.outputPtr true a)) ho).isSome = true)
    (hH : (taint.check (Taint.ofRegs [.x0]) (.block (headSuffix a)) hh).isSome = true) :
    RelCT isa (Two fun L s => 0 < blocks L ∧ LoopCtx a L 0 s)
      (SquareEightRaw.rows a) (Two fun L s => LoopCtx a L (blocks L) s) := by
  apply two_loop blocks (row_ct ha ha1 ha2 hO hH)
  intro L j s hj h
  refine WP.mono (row_ctx_next ha ha1 ha2 hj h) fun t ⟨ht, he⟩ => ⟨he, fun _ => ht, ?_⟩
  intro hlast
  exact hlast ▸ ht

end VG.Proof.Bignum.AArch64.SquareEight
