module
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcBody
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
import VerifiedGarbage.Proof.Bignum.AArch64.MulAdd

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
  have he : 8 * blocks L = L.w := by dsimp [blocks]; omega
  dsimp [rowBase, rawBase, modBase, slot, hdrBytes, aAcc, aN] at hz ⊢
  dsimp [blocks] at *
  omega

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
  refine WP.mono (asLoad_ok hg.scr h.2.ptr (by omega)) fun a ⟨⟨_, ham, _⟩, ka⟩ => ?_
  refine WP.mono (startHeader_ok (hg.scr.congr ka.wr) ((ka.gpr .x0 (by decide)).trans hg.x0)
    (by omega)) fun t ⟨⟨ht17, _, htm⟩, kt⟩ => ?_
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
  have he : 8 * blocks p.1 = p.1.w := by have := h.2.fast.2.2; dsimp [blocks]; omega
  have heCode : rowPrefix ++ rowMiddle = startBlock ++ columnSetup := by
    simp only [rowPrefix, rowMiddle, startBlock, List.append_assoc]
  rewrite [heCode]
  apply WP.block_append
  refine WP.mono (startBlock_ok (eN := modBase p.1) hg.scr hg.x0 h.2.ptr h.2.zero (by omega)
    (by omega) (by omega) (by omega) (hg.hdr.harr aN (by decide)) hg.hdr.hminv)
    fun a ⟨_, hao, ha17, ka⟩ => ?_
  have hHA := (Square.scratch_arrays (hao.mono (o' := rawBase p.1)
    (n' := 8 * (2 * p.1.w + 2)) (by dsimp [rowBase]; omega)
    (by dsimp [rowBase]; omega))).hdr hg.hdr
  have hW := hHA.hw.trans (congrArg (BitVec.ofNat 64) he.symm)
  refine WP.mono (columnSetup_ok (hg.scr.congr ka.wr) ((ka.gpr .x0 (by decide)).trans hg.x0)
    ((ka.gpr .x8 (by decide)).trans h.2.ptr) ha17 (by omega) hW hk hkw)
    fun t ⟨⟨ht16, ht17, ht15, htm⟩, kt⟩ => ?_
  have km := ka.trans kt
  have hG : GoodW p.1 t := ⟨mi, ⟨hg.scr.congr km.wr, (km.gpr .x0 (by decide)).trans hg.x0,
    htm ▸ hHA⟩, hz⟩
  refine ⟨⟨⟨hG, h.2.fast.2⟩, (km.gpr .x8 (by decide)).trans h.2.ptr,
    (km.gpr .x12 (by decide)).trans h.2.count, (km.gpr .x7 (by decide)).trans h.2.zero,
    ?_⟩, ht16, ht17, ht15⟩
  exact Nat.le_trans (Nat.le_of_eq (congrArg BitVec.toNat (km.gpr .x10 (by decide)))) h.2.carry

end VG.Proof.Bignum.AArch64.BlockedRedc
