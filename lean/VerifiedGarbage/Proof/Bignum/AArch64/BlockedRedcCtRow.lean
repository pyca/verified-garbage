module

import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcBody
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcBody
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad

/-! ### `Bignum.AArch64.BlockedRedcCtContext`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.Bignum.AArch64.BlockedRedc
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)

abbrev rawBase (L : Ws) := slot L.w aAcc + 16
abbrev modBase (L : Ws) := slot L.w aN
abbrev rowBase (L : Ws) (j : Nat) := rawBase L + 64 * j
abbrev blocks (L : Ws) := L.w / 8

def FastW (L : Ws) (s : State) : Prop := GoodW L s ∧ 16 ≤ L.w ∧ L.w % 8 = 0

structure LoopCtx (L : Ws) (j : Nat) (s : State) : Prop where
  fast : FastW L s
  ptr : s.gpr .x8 = off L.B (rowBase L j)
  count : s.gpr .x12 = BitVec.ofNat 64 (blocks L - j)
  zero : s.gpr .x7 = 0
  carry : (s.gpr .x10).toNat ≤ 1

structure HeadCtx (p : Ws × Nat) (s : State) : Prop where
  loop : LoopCtx p.1 p.2 s
  modulus : s.gpr .x17 = off p.1.B (modBase p.1)

structure BodyCtx (p : Ws × Nat) (s : State) : Prop where
  loop : LoopCtx p.1 p.2 s
  tptr : s.gpr .x16 = off p.1.B (rowBase p.1 p.2 + 64)
  nptr : s.gpr .x17 = off p.1.B (modBase p.1 + 64)
  count : s.gpr .x15 = BitVec.ofNat 64 (blocks p.1 - 1)

theorem row_bounds {L : Ws} {s : State} {j : Nat} (h : FastW L s) (hj : j < blocks L) :
    2 ≤ blocks L ∧ 8 * blocks L < 2 ^ 64 ∧ 256 ≤ rowBase L j ∧
      rowBase L j + 64 * (blocks L + 1) ≤ L.Z ∧ modBase L + 64 * blocks L ≤ rowBase L j := by
  have hw := Square.goodW_width h.1
  obtain ⟨mi, hg, hz⟩ := h.1
  have h16 := h.2.1
  have hm := h.2.2
  have he : 8 * blocks L = L.w := by dsimp [blocks]; omega_using [hm]
  dsimp [rowBase, rawBase, modBase, slot, hdrBytes, aAcc, aN] at hz ⊢
  dsimp [blocks] at *
  omega_using [hj, hw, hz, h16]

def rowPrefix : List Instr := VG.Impl.Bignum.AArch64.BlockedRedc.asLoad ++
  [ldh .x17 (sArr aN), ldh .x15 sMinv]

def rowMiddle : List Instr := VG.Impl.Bignum.AArch64.BlockedRedc.nsLoad ++
  (List.range 8).flatMap VG.Impl.Bignum.AArch64.BlockedRedc.cancel ++ columnSetup

def rowTail : Prog isa := .seq
  (countLoop .x15 (tailBlock ++ [.addImm .x .x17 .x17 64]))
  (.block (VG.Impl.Bignum.AArch64.BlockedRedc.addMemory true ++ [.adc .x .x10 .x7 .x7] ++
    VG.Impl.Bignum.AArch64.BlockedRedc.asStore ++ [.addImm .x .x8 .x8 64, .subImm .x .x12 .x12 1]))

theorem row_split : rowBody = .seq (.block (rowPrefix ++ rowMiddle)) rowTail := by
  simp only [rowBody, rowPrefix, rowMiddle, rowTail, startBlock, List.append_assoc]

theorem prefix_ctx (p : Ws × Nat) (s : State) (h : p.2 < blocks p.1 ∧ LoopCtx p.1 p.2 s) :
    WP isa (.block rowPrefix) s (HeadCtx p) := by
  obtain ⟨mi, hg, hz⟩ := h.2.fast.1
  obtain ⟨hk, _, hHdr, hSize, _⟩ := row_bounds h.2.fast h.1
  unfold rowPrefix
  apply WP.block_append
  refine WP.mono (asLoad_ok hg.scr h.2.ptr (by omega_using [hSize])) fun a ⟨⟨_, ham, _⟩, ka⟩ => ?_
  refine WP.mono (startHeader_ok (hg.scr.congr ka.wr) ((ka.gpr .x0 (by decide)).trans hg.x0)
    (by omega_using [hHdr, hSize])) fun t ⟨⟨ht17, _, htm⟩, kt⟩ => ?_
  have km := ka.trans kt
  have hm := htm.trans ham
  have hG : GoodW p.1 t := ⟨mi, ⟨hg.scr.congr km.wr, (km.gpr .x0 (by decide)).trans hg.x0,
    hm ▸ hg.hdr⟩, hz⟩
  refine ⟨⟨⟨hG, h.2.fast.2⟩, (km.gpr .x8 (by decide)).trans h.2.ptr,
    (km.gpr .x12 (by decide)).trans h.2.count, (km.gpr .x7 (by decide)).trans h.2.zero,
    ?_⟩, ?_⟩
  · exact Nat.le_trans (Nat.le_of_eq (congrArg BitVec.toNat (km.gpr .x10 (by decide)))) h.2.carry
  · exact ht17.trans ((congrArg (fun m : Mem => word m p.1.B (8 * sArr aN)) ham).trans
      (hg.hdr.harr aN (by decide)))

theorem firstBlock_ctx (p : Ws × Nat) (s : State) (h : p.2 < blocks p.1 ∧ LoopCtx p.1 p.2 s) :
    WP isa (.block (rowPrefix ++ rowMiddle)) s (BodyCtx p) := by
  obtain ⟨mi, hg, hz⟩ := h.2.fast.1
  obtain ⟨hk, hkw, hHdr, hSize, hNQ⟩ := row_bounds h.2.fast h.1
  have hn := hg.scr.nowrap
  have he : 8 * blocks p.1 = p.1.w := by have := h.2.fast.2.2; dsimp [blocks]; omega_using [this]
  have heCode : rowPrefix ++ rowMiddle = startBlock ++ columnSetup := by
    simp only [rowPrefix, rowMiddle, startBlock, List.append_assoc]
  rewrite [heCode]
  apply WP.block_append
  refine WP.mono (startBlock_ok (eN := modBase p.1) hg.scr hg.x0 h.2.ptr h.2.zero (by omega_using [hHdr, hSize])
    (by omega_using [hSize]) (by omega_using [hSize, hNQ]) (by omega_using [hk, hNQ]) (hg.hdr.harr aN (by decide)) hg.hdr.hminv)
    fun a ⟨_, hao, ha17, ka⟩ => ?_
  have hHA := (Square.scratch_arrays (hao.mono (o' := rawBase p.1)
    (n' := 8 * (2 * p.1.w + 2)) (by dsimp [rowBase]; omega_using [])
    (by dsimp [rowBase]; omega))).hdr hg.hdr
  have hW := hHA.hw.trans (congrArg (BitVec.ofNat 64) he.symm)
  refine WP.mono (columnSetup_ok (hg.scr.congr ka.wr) ((ka.gpr .x0 (by decide)).trans hg.x0)
    ((ka.gpr .x8 (by decide)).trans h.2.ptr) ha17 (by omega_using [hHdr, hSize]) hW hk hkw)
    fun t ⟨⟨ht16, ht17, ht15, htm⟩, kt⟩ => ?_
  have km := ka.trans kt
  have hG : GoodW p.1 t := ⟨mi, ⟨hg.scr.congr km.wr, (km.gpr .x0 (by decide)).trans hg.x0,
    htm ▸ hHA⟩, hz⟩
  refine ⟨⟨⟨hG, h.2.fast.2⟩, (km.gpr .x8 (by decide)).trans h.2.ptr,
    (km.gpr .x12 (by decide)).trans h.2.count, (km.gpr .x7 (by decide)).trans h.2.zero,
    ?_⟩, ht16, ht17, ht15⟩
  exact Nat.le_trans (Nat.le_of_eq (congrArg BitVec.toNat (km.gpr .x10 (by decide)))) h.2.carry

end VG.Proof.Bignum.AArch64.BlockedRedc

end

end

@[expose] public section

namespace VG.Proof.Bignum.AArch64.BlockedRedc
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64

abbrev RowPre (p : Ws × Nat) (s : State) := p.2 < blocks p.1 ∧ LoopCtx p.1 p.2 s

theorem pins_loop : Pins RowPre [.x0, .x8, .x12, .x7] := by
  intro p s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact pins_goodW p.1 s t hs.2.fast.1 ht.2.fast.1 .x0 (by simp)
  · exact hs.2.ptr.trans ht.2.ptr.symm
  · exact hs.2.count.trans ht.2.count.symm
  · exact hs.2.zero.trans ht.2.zero.symm

theorem pins_head : Pins HeadCtx [.x0, .x8, .x12, .x7, .x17] := by
  intro p s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact pins_goodW p.1 s t hs.loop.fast.1 ht.loop.fast.1 .x0 (by simp)
  · exact hs.loop.ptr.trans ht.loop.ptr.symm
  · exact hs.loop.count.trans ht.loop.count.symm
  · exact hs.loop.zero.trans ht.loop.zero.symm
  · exact hs.modulus.trans ht.modulus.symm

theorem pins_body : Pins BodyCtx [.x8, .x12, .x16, .x17, .x15] := by
  intro p s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hs.loop.ptr.trans ht.loop.ptr.symm
  · exact hs.loop.count.trans ht.loop.count.symm
  · exact hs.tptr.trans ht.tptr.symm
  · exact hs.nptr.trans ht.nptr.symm
  · exact hs.count.trans ht.count.symm

/-- Header loads are recaptured through their proven public values before
using them as addresses or loop bounds. Arithmetic values stay secret. -/
theorem firstBlock_ct : RelCT isa (Two RowPre) (.block (rowPrefix ++ rowMiddle)) (fun _ _ => True) := by
  apply RelCT.block_append
  exact RelCT.seq (two_piece [.x0, .x8, .x12, .x7] pins_loop (by taint_decide) prefix_ctx)
    (two_taint [.x0, .x8, .x12, .x7, .x17] pins_head (by taint_decide))

theorem rowBody_ct : RelCT isa (Two RowPre) rowBody (fun _ _ => True) := by
  rewrite [row_split]
  exact RelCT.seq (two_post firstBlock_ct firstBlock_ctx)
    (two_taint [.x8, .x12, .x16, .x17, .x15] pins_body (by taint_decide))

end VG.Proof.Bignum.AArch64.BlockedRedc
