module
public import Mathlib.Data.Int.GCD
public import VerifiedGarbage.Impl.Ffdh.AArch64.Domain
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Framework.Contract

import VerifiedGarbage.Proof.Ffdh.AArch64.Checks
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Checks
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Ffdh.AArch64.Ws
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Ws
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
import VerifiedGarbage.Proof.Bignum.AArch64.CrtBuild
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChk
import VerifiedGarbage.Proof.Bignum.AArch64.CrtExp
import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtP
import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.Double
import VerifiedGarbage.Proof.Bignum.AArch64.Mont
import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
import VerifiedGarbage.Proof.Bignum.AArch64.PdExp
import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.AArch64.Setup
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import VerifiedGarbage.Proof.Bignum.AArch64.Store
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
meta import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
meta import VerifiedGarbage.Proof.Bignum.AArch64.Copy
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtBuild
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtExp
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtP
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.AArch64.Csub
meta import VerifiedGarbage.Proof.Bignum.AArch64.Double
meta import VerifiedGarbage.Proof.Bignum.AArch64.Mont
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdExp
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
meta import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
meta import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
meta import VerifiedGarbage.Proof.Bignum.AArch64.Row
meta import VerifiedGarbage.Proof.Bignum.AArch64.Setup
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
meta import VerifiedGarbage.Proof.Bignum.AArch64.Store
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Poly1305.Limbs64

/-!
# FFDH on AArch64: the comparisons in constant time

In runs on workspaces of the same layout (`Two GoodW`), whatever the
numbers in them: the header loads are checked by the taint analysis from
`x0`, the loops from the registers the header gave (`w` and the bases).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64.Crt
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- A workspace is one after code that keeps its memory, `x0` and the
permissions. -/
theorem GoodW.keep {L : Ws} {s t : State} (h : GoodW L s) (hm : t.mem = s.mem) (h0 : t.gpr .x0 = s.gpr .x0)
    (hwr : t.wr = s.wr) : GoodW L t := by
  obtain ⟨mi, hg, hZ⟩ := h
  exact ⟨mi, ⟨hg.scr.congr hwr, h0.trans hg.x0, by rw [hm]; exact hg.hdr⟩, hZ⟩

/-- The registers the comparison loops need, from the header. -/
def CmpRegs (a b : Nat) (L : Ws) (t : State) : Prop :=
  t.gpr .x14 = BitVec.ofNat 64 L.w ∧ t.gpr .x16 = off L.B (slot L.w a) ∧ t.gpr .x17 = off L.B (slot L.w b)

theorem pins_cmpRegs (a b : Nat) : Pins (CmpRegs a b) [.x14, .x16, .x17] :=
  pins_of (fun L r => if r = .x14 then BitVec.ofNat 64 L.w else
      if r = .x16 then off L.B (slot L.w a) else off L.B (slot L.w b))
    fun L s h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.1
      · exact h.2.1
      · exact h.2.2

/-- A comparison: its first block (checked by the taint analysis from `x0`),
then code checked from the registers it loads. -/
theorem cmp_ct {a b : Nat} {l : List Instr} {c : Prog isa}
    {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (hl : ∀ (L : Ws) s, GoodW L s → WP isa (.block (ptrs a b ++ l)) s (CmpRegs a b L))
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block (ptrs a b ++ l)) hc₁).isSome = true)
    (hT' : (taint.check (Taint.ofRegs [.x14, .x16, .x17]) c hc₂).isSome = true) :
    RelCT isa (Two GoodW) (.seq (.block (ptrs a b ++ l)) c) fun _ _ => True :=
  RelCT.seq (two_piece [.x0] pins_goodW hT hl) (two_taint [.x14, .x16, .x17] (pins_cmpRegs a b) hT')

theorem ptrsCmp_ok {a b : Nat} (ha : a < 8) (hb : b < 8) (L : Ws) (s : State) (h : GoodW L s) :
    WP isa (.block (ptrs a b ++ [movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7])) s (CmpRegs a b L) := by
  obtain ⟨_, hg, hZ⟩ := h
  exact WP.mono (cmpHead_ok hg hZ ha hb) fun _ h => ⟨h.2.2.1, h.1, h.2.1⟩

theorem ptrsEq_ok {a b : Nat} (ha : a < 8) (hb : b < 8) (L : Ws) (s : State) (h : GoodW L s) :
    WP isa (.block (ptrs a b ++ [movi .x9 0, mov .x14 .x12])) s (CmpRegs a b L) := by
  obtain ⟨_, hg, hZ⟩ := h
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off L.B (8 * i)) 8 := fun i hi => hg.ld hZ hi
  exact WP.mono (WP.keep [.x9, .x12, .x14, .x16, .x17] (Q := CmpRegs a b L)
    (by unfold ptrs CmpRegs; brun [hg.x0, hdr_enc (sArr_lt ha), hdr_enc (sArr_lt hb), hdr_enc (show sW < 32 by decide),
      hl (sArr a) (sArr_lt ha), hl (sArr b) (sArr_lt hb), hl sW (by decide), hg.hdr.harr a ha,
      hg.hdr.harr b hb, hg.hdr.hw]) rfl rfl rfl) fun _ h => h.1

/-- `ltArr a b`, given the taint analysis's check of its first block. -/
theorem ltArr_ct {a b : Nat} (ha : a < 8) (hb : b < 8) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block (ptrs a b ++ [movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7]))
      hc).isSome = true) :
    RelCT isa (Two GoodW) (seqs (ltArr a b)) fun _ _ => True :=
  cmp_ct (ptrsCmp_ok ha hb) hT (by taint_decide)

/-- `geArr a b`. -/
theorem geArr_ct {a b : Nat} (ha : a < 8) (hb : b < 8) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block (ptrs a b ++ [movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7]))
      hc).isSome = true) :
    RelCT isa (Two GoodW) (seqs (geArr a b)) fun _ _ => True :=
  cmp_ct (ptrsCmp_ok ha hb) hT (by taint_decide)

/-- `eqArr a b`. -/
theorem eqArr_ct {a b : Nat} (ha : a < 8) (hb : b < 8) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block (ptrs a b ++ [movi .x9 0, mov .x14 .x12]))
      hc).isSome = true) :
    RelCT isa (Two GoodW) (seqs (eqArr a b)) fun _ _ => True :=
  cmp_ct (ptrsEq_ok ha hb) hT (by taint_decide)

/-- Layouts of at least one word and fewer than `2^31`. -/
def GoodW1 (L : Ws) (s : State) : Prop := GoodW L s ∧ 1 ≤ L.w ∧ L.w < 2 ^ 31

theorem two_goodW1 {s₁ s₂ : State} (h : Two GoodW1 s₁ s₂) : Two GoodW s₁ s₂ := two_mono (fun _ _ h => h.1) h

/-- The workspace, with `x16` the temporary array's base. -/
def TmpReg (L : Ws) (t : State) : Prop := GoodW L t ∧ t.gpr .x16 = off L.B (slot L.w aTmp)

theorem tmpPtr_ok (L : Ws) (s : State) (h : GoodW1 L s) :
    WP isa (.block [ldh .x16 (sArr aTmp)]) s fun t => GoodW1 L t ∧ t.gpr .x16 = off L.B (slot L.w aTmp) := by
  obtain ⟨⟨mi, hg, hZ⟩, hw⟩ := h
  exact WP.mono (WP.keep [.x16] (Q := fun t => t.gpr .x16 = off L.B (slot L.w aTmp) ∧ t.mem = s.mem)
    (by brun [hg.x0, hdr_enc (sArr_lt (show aTmp < 8 by decide)), hg.ld hZ (sArr_lt (show aTmp < 8 by decide)),
      hg.hdr.harr aTmp (by decide)]) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h16, hm⟩, k⟩ => ⟨⟨GoodW.keep ⟨mi, hg, hZ⟩ hm (k.gpr .x0 (by decide)) k.wr, hw⟩, h16⟩

theorem or1_ok (L : Ws) (s : State) (h : GoodW1 L s ∧ s.gpr .x16 = off L.B (slot L.w aTmp)) :
    WP isa (.block [ld .x3 .x16, movi .x4 1, .logic .orr .x .x3 .x3 .x4, st .x3 .x16]) s (GoodW1 L) := by
  obtain ⟨⟨⟨mi, hg, hZ⟩, hw⟩, h16⟩ := h
  have hn := hg.scr.nowrap
  have sT := Nat.le_trans (slot_le (w := L.w) (show aTmp < 8 by decide)) hZ
  have hT0 := hdr_lt_slot L.w aTmp (show 31 < 32 by decide)
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun t' => t'.mem = s.mem.writeW (off L.B (slot L.w aTmp))
      (word s.mem L.B (slot L.w aTmp) ||| 1))
    (by brun [h16, hg.scr.ld (show slot L.w aTmp + 8 ≤ L.Z by omega), hg.scr.st (show slot L.w aTmp + 8 ≤ L.Z by omega)]; rfl)
    (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k⟩ => ?_
  have o := writeW_outside s.mem L.B (d := slot L.w aTmp) (word s.mem L.B (slot L.w aTmp) ||| 1) (by omega)
  rw [← hm] at o
  exact ⟨⟨mi, hg.of_outside (by omega) o k.wr (k.gpr .x0 (by decide)), hZ⟩, hw⟩

theorem ltP_eq : seqs (([.block [ldh .x16 (sArr aTmp)], .block [ld .x3 .x16, movi .x4 1,
    .logic .orr .x .x3 .x3 .x4, st .x3 .x16]] : List (Prog isa)) ++ ltArr aTmp aN) = .seq (.block [ldh .x16 (sArr aTmp)])
    (.seq (.block [ld .x3 .x16, movi .x4 1, .logic .orr .x .x3 .x3 .x4, st .x3 .x16]) (seqs (ltArr aTmp aN))) := rfl

/-- `ltP a` (`a ≠ aTmp`). -/
theorem ltP_ct {a : Nat} (ha : a < 8) (haT : a ≠ aTmp) {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT₁ : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x12 sW, ldh .x16 (sArr a), ldh .x17 (sArr aTmp)])
      hc₁).isSome = true)
    (hT₂ : (taint.check (Taint.ofRegs [.x0]) (.block (ptrs aTmp aN ++ [movi .x7 0, mov .x14 .x12,
      .subs .x .x3 .x7 .x7])) hc₂).isSome = true) :
    RelCT isa (Two GoodW1) (seqs (ltP a)) fun _ _ => True := by
  unfold ltP
  rw [List.append_assoc]
  refine RelCT.seqs_append (by simp [copyArr]) (by simp) ?_
  rw [ltP_eq]
  refine RelCT.seq (R := Two GoodW1) (two_post ((copyArr_ct (show aTmp < 8 by decide) ha hT₁).mono
      (fun _ _ h => two_goodW1 h) fun _ _ h => h) fun L s h => ?_)
    (RelCT.seq (two_piece [.x0] (fun L s₁ s₂ h₁ h₂ => pins_goodW L s₁ s₂ h₁.1 h₂.1) (by taint_decide) tmpPtr_ok)
      (RelCT.seq (two_piece [.x16] (pins_of (fun L _ => off L.B (slot L.w aTmp)) fun L s h r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact h.2) (by taint_decide) or1_ok)
        ((ltArr_ct (show aTmp < 8 by decide) (show aN < 8 by decide) hT₂).mono (fun _ _ h => two_goodW1 h)
          fun _ _ h => h)))
  obtain ⟨⟨mi, hg, hZ⟩, hw, hw'⟩ := h
  have hT0 := hdr_lt_slot L.w aTmp (show 31 < 32 by decide)
  exact WP.mono (copyArr_ok hg hZ hw hw' (show aTmp < 8 by decide) ha (Ne.symm haT)) fun t ⟨_, ho, k⟩ =>
    ⟨⟨mi, hg.of_outside (by omega) ho k.wr (k.gpr .x0 (by decide)), hZ⟩, hw, hw'⟩

/-- `isOdd a`. -/
theorem isOdd_ct {a : Nat} (ha : a < 8) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x16 (sArr a)]) hc).isSome = true) :
    RelCT isa (Two GoodW) (seqs (isOdd a)) fun _ _ => True := by
  unfold isOdd
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := fun L t => t.gpr .x16 = off L.B (slot L.w a)) [.x0] pins_goodW hT
    fun L s ⟨mi, hg, hZ⟩ => ?_) (two_taint [.x16] (pins_of (fun L _ => off L.B (slot L.w a)) fun L s h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h) (by taint_decide))
  exact WP.mono (WP.keep [.x16] (Q := fun t => t.gpr .x16 = off L.B (slot L.w a))
    (by brun [hg.x0, hdr_enc (sArr_lt ha), hg.ld hZ (sArr_lt ha), hg.hdr.harr a ha]) rfl rfl rfl) fun t h => h.1

/-- `GoodW1` after a change of memory at offsets `o ≥ 128`. -/
theorem GoodW1.of_outside {L : Ws} {s t : State} (h : GoodW1 L s) {o n : Nat} (ho : 8 * 16 ≤ o)
    (hout : Outside L.B o n s.mem t.mem) (hwr : t.wr = s.wr) (h0 : t.gpr .x0 = s.gpr .x0) : GoodW1 L t :=
  let ⟨⟨mi, hg, hZ⟩, hw⟩ := h
  ⟨⟨mi, hg.of_outside ho hout hwr h0, hZ⟩, hw⟩

theorem GoodW1.keep {L : Ws} {s t : State} (h : GoodW1 L s) (hm : t.mem = s.mem) (h0 : t.gpr .x0 = s.gpr .x0)
    (hwr : t.wr = s.wr) : GoodW1 L t := ⟨GoodW.keep h.1 hm h0 hwr, h.2⟩

theorem pins_goodW1 : Pins GoodW1 [.x0] := fun L s₁ s₂ h₁ h₂ => pins_goodW L s₁ s₂ h₁.1 h₂.1

/-- A store of `x9` into the header slot `sl ≥ 16`. -/
theorem stF_ok {sl : Nat} (hsl : 16 ≤ sl) (hsl' : sl < 32) (L : Ws) (s : State) (h : GoodW1 L s) :
    WP isa (.block [sth .x9 sl]) s (GoodW1 L) := by
  obtain ⟨⟨mi, hg, hZ⟩, hw⟩ := h
  have hn := hg.scr.nowrap
  have h8 := hdr_lt_slot L.w 0 hsl'
  have h8' := hdr_lt_slot L.w 8 hsl'
  refine WP.mono (WP.keep [] (Q := fun t' => t'.mem = s.mem.writeW (off L.B (8 * sl)) (s.gpr .x9))
    (by brun [hg.x0, hdr_enc hsl', hg.scr.st (show 8 * sl + 8 ≤ L.Z by omega)]) rfl rfl rfl) fun t ⟨hm, k⟩ => ?_
  have o := writeW_outside s.mem L.B (d := 8 * sl) (s.gpr .x9) (by omega)
  rw [← hm] at o
  exact GoodW1.of_outside ⟨⟨mi, hg, hZ⟩, hw⟩ (by omega) o k.wr (k.gpr .x0 (by decide))

/-- `andF`. -/
theorem andF_ok (L : Ws) (s : State) (h : GoodW1 L s) : WP isa (.block andF) s (GoodW1 L) := by
  obtain ⟨⟨mi, hg, hZ⟩, hw⟩ := h
  have hn := hg.scr.nowrap
  have h8 := hdr_lt_slot L.w 0 (show sF < 32 by decide)
  have h8' := hdr_lt_slot L.w 8 (show sF < 32 by decide)
  have eF : sF = 30 := rfl
  refine WP.mono (WP.keep [.x3, .x9] (Q := fun t' => ∃ v : BitVec 64, t'.mem = s.mem.writeW (off L.B (8 * sF)) v)
    (by unfold andF; brun [hg.x0, hdr_enc (show sF < 32 by decide), hg.scr.ld (show 8 * sF + 8 ≤ L.Z by omega),
      hg.scr.st (show 8 * sF + 8 ≤ L.Z by omega)]; exact ⟨_, rfl⟩) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨v, hm⟩, k⟩ => ?_
  have o := writeW_outside s.mem L.B (d := 8 * sF) v (by omega)
  rw [← hm] at o
  exact GoodW1.of_outside ⟨⟨mi, hg, hZ⟩, hw⟩ (by omega) o k.wr (k.gpr .x0 (by decide))

/-- `range a` (`a ≠ aTmp`). -/
theorem range_ct {a : Nat} (ha : a < 8) (haT : a ≠ aTmp) {hc₁ hc₂ hc₃ : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT₁ : (taint.check (Taint.ofRegs [.x0]) (.block (ptrs aOne a ++ [movi .x7 0, mov .x14 .x12,
      .subs .x .x3 .x7 .x7])) hc₁).isSome = true)
    (hT₂ : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x12 sW, ldh .x16 (sArr a), ldh .x17 (sArr aTmp)])
      hc₂).isSome = true)
    (hT₃ : (taint.check (Taint.ofRegs [.x0]) (.block (ptrs aTmp aN ++ [movi .x7 0, mov .x14 .x12,
      .subs .x .x3 .x7 .x7])) hc₃).isSome = true) :
    RelCT isa (Two GoodW1) (seqs (range a)) fun _ _ => True := by
  rw [show range a = ltArr aOne a ++ (.block [sth .x9 sF] :: (ltP a ++ [.block andF])) by simp [range, gt1]]
  refine RelCT.seqs_append (by simp [ltArr, cmpArr]) (by simp) (RelCT.seq (R := Two GoodW1)
    (two_post ((ltArr_ct (show aOne < 8 by decide) ha hT₁).mono (fun _ _ h => two_goodW1 h) fun _ _ h => h)
      fun L s h => ?_) ?_)
  · obtain ⟨⟨mi, hg, hZ⟩, hw, hw'⟩ := h
    exact WP.mono (ltArr_ok hg hZ hw hw' (show aOne < 8 by decide) ha) fun t ⟨_, hm, k⟩ =>
      GoodW1.keep ⟨⟨mi, hg, hZ⟩, hw, hw'⟩ hm (k.gpr .x0 (by decide)) k.wr
  refine seqs_cons_ct (by simp [ltP, copyArr]) (RelCT.seq (R := Two GoodW1)
    (two_piece [.x0] pins_goodW1 (by taint_decide) (stF_ok (by decide) (by decide))) ?_)
  refine RelCT.seqs_append (by simp [ltP, copyArr]) (by simp) (RelCT.seq (R := Two GoodW1)
    (two_post (ltP_ct ha haT hT₂ hT₃) fun L s h => ?_) ?_)
  · obtain ⟨⟨mi, hg, hZ⟩, hw, hw'⟩ := h
    have hT0 := hdr_lt_slot L.w aTmp (show 31 < 32 by decide)
    exact WP.mono (ltP_ok hg hZ hw hw' ha haT) fun t ⟨_, ho, k⟩ =>
      GoodW1.of_outside ⟨⟨mi, hg, hZ⟩, hw, hw'⟩ (by omega) ho k.wr (k.gpr .x0 (by decide))
  exact two_taint [.x0] pins_goodW1 (by taint_decide)

end VG.Proof.Ffdh.AArch64
