module
public import VerifiedGarbage.Proof.Rsa.AArch64.CkCT
public import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyCode

import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyCT
meta import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyCT
import VerifiedGarbage.Proof.Rsa.AArch64.ExpCheck
meta import VerifiedGarbage.Proof.Rsa.AArch64.ExpCheck
import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.Octets
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
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.Double
import VerifiedGarbage.Proof.Bignum.AArch64.Mont
import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
import VerifiedGarbage.Proof.Bignum.AArch64.PdCTRest
import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
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
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
import VerifiedGarbage.Proof.Rsa.AArch64.CkCTPieces
import VerifiedGarbage.Proof.Rsa.AArch64.CkCode
import VerifiedGarbage.Proof.Rsa.AArch64.CkPhase
import VerifiedGarbage.Proof.Rsa.AArch64.CkPieces
import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyCTReduce
import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyHead
import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyMain
import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyPhase
import VerifiedGarbage.Proof.Rsa.AArch64.CvCTMain
import VerifiedGarbage.Proof.Rsa.AArch64.CvCode
import VerifiedGarbage.Proof.Rsa.AArch64.Guarded
import VerifiedGarbage.Proof.Rsa.AArch64.Inv
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
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
meta import VerifiedGarbage.Proof.Bignum.AArch64.Csub
meta import VerifiedGarbage.Proof.Bignum.AArch64.Double
meta import VerifiedGarbage.Proof.Bignum.AArch64.Mont
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdCTRest
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
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
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
meta import VerifiedGarbage.Proof.Rsa.AArch64.CkCTPieces
meta import VerifiedGarbage.Proof.Rsa.AArch64.CkCode
meta import VerifiedGarbage.Proof.Rsa.AArch64.CkPhase
meta import VerifiedGarbage.Proof.Rsa.AArch64.CkPieces
meta import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyCTReduce
meta import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyCode
meta import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyHead
meta import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyMain
meta import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyPhase
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvCTMain
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvCode
meta import VerifiedGarbage.Proof.Rsa.AArch64.Guarded
meta import VerifiedGarbage.Proof.Rsa.AArch64.Inv
meta import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops

/-!
# `vg_rsa_check_crt_key` on AArch64: constant time but for `n` and `e`

`entry`, the checks of `e` and `n`, `fail` and `main` (`ckcMain_ct`) leak
the same in runs that agree on the public data (`ckcCode_ct`): the
contract's `ConstantTime` (`ckcCode_constantTime`).
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.CheckKey (sE sElen sD sDlen sP sPlen sQ sQlen sDP sDQ sQI fail)
open VG.Impl.Rsa.AArch64.CheckCrtKey (entry)
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

/-- A state the contract allows, with the public data `p`. -/
def CkcRel (p : CkP) (s : State) : Prop := ckcA.pre s ∧ (ckcIn s).pub = p

theorem ckcEntry_split : entry = ([.ldrSp .x8 48] : List Instr) ++ entry.drop 1 := rfl

/-- After `entry`'s first instruction. -/
def Ckc1 (p : CkP) (t : State) : Prop :=
  ∃ s, CkcRel p s ∧ t.gpr .x8 = p.B ∧ t.gpr .x2 = p.pE ∧ t.gpr .x3 = BitVec.ofNat 64 p.el ∧
    WP isa (.block (entry.drop 1)) t (CkcHeadPost s)

/-- After `entry`. -/
def Ckc2 (p : CkP) (t : State) : Prop := ∃ s, CkcRel p s ∧ CkcHeadPost s t

/-- After the check of `e`. -/
def Ckc3 (p : CkP) (t : State) : Prop :=
  ∃ s t₁, CkcRel p s ∧ CkcHeadPost s t₁ ∧ t.mem = t₁.mem ∧
    Keep [.x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] t₁ t ∧
    t.gpr .x9 = BitVec.ofNat 64 (Spec.Rsa.exponentValid (Spec.Rsa.os2ip p.eb)).toNat

/-- After the loads of `n`'s pointer and length. -/
def Ckc3b (p : CkP) (t : State) : Prop :=
  ∃ s t₁, CkcRel p s ∧ CkcHeadPost s t₁ ∧ t.mem = t₁.mem ∧
    Keep [.x2, .x3, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] t₁ t ∧
    t.gpr .x2 = p.pN ∧ t.gpr .x3 = BitVec.ofNat 64 p.k ∧ Spec.Rsa.exponentValid (Spec.Rsa.os2ip p.eb) = true

/-- After the check of `n`. -/
def Ckc4 (p : CkP) (t : State) : Prop :=
  ∃ s t₁, CkcRel p s ∧ CkcHeadPost s t₁ ∧ t.mem = t₁.mem ∧
    Keep [.x2, .x3, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] t₁ t ∧
    t.gpr .x9 = BitVec.ofNat 64 (Spec.Rsa.modulusValid (Spec.Rsa.os2ip p.nb) p.k).toNat ∧
    Spec.Rsa.exponentValid (Spec.Rsa.os2ip p.eb) = true

theorem ckcRel_x {p : CkP} {s : State} (h : CkcRel p s) :
    s.gpr .x0 = p.pN ∧ s.gpr .x1 = BitVec.ofNat 64 p.k ∧ s.gpr .x2 = p.pE ∧ s.gpr .x3 = BitVec.ofNat 64 p.el := by
  obtain ⟨-, rfl⟩ := h
  exact ⟨rfl, (ofNat_toNat64 _).symm, rfl, (ofNat_toNat64 _).symm⟩

/-- `fail` leaks nothing. -/
theorem ckcFail_ct {α : Type} {Φ : α → State → Prop} : RelCT isa (Two Φ) (.block fail) fun _ _ => True :=
  two_taint [] (fun _ _ _ _ _ _ hr => absurd hr (List.not_mem_nil)) (by taint_decide)

/-- `entry` leaks the same in runs with the same public data. -/
theorem ckcEntry_ct : RelCT isa (Two CkcRel) (.block entry) (Two Ckc2) := by
  rw [ckcEntry_split]
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := Ckc1) [.x2, .x3] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [(ckcRel_x h₁).2.2.1, (ckcRel_x h₂).2.2.1]
    · rw [(ckcRel_x h₁).2.2.2, (ckcRel_x h₂).2.2.2]) (by taint_decide) ?_)
    (two_piece [.x8, .x2, .x3] (fun p s₁ s₂ ⟨_, _, a₁, b₁, c₁, _⟩ ⟨_, _, a₂, b₂, c₂, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [a₁, a₂]
      · rw [b₁, b₂]
      · rw [c₁, c₂]) (by taint_decide) fun p t ⟨s, hs, _, _, _, hw⟩ => WP.mono hw fun t' h => ⟨s, hs, h⟩))
  intro p s hs
  have c := ckcCtx_of hs.1
  have hh : WP isa (.block (([.ldrSp .x8 48] : List Instr) ++ entry.drop 1)) s (CkcHeadPost s) := by
    rw [← ckcEntry_split]; exact ckcHead_ok' c
  have hB' : s.mem.readW (s.sp + BitVec.ofNat 64 48) 64 = stackArg s 6 := rfl
  have ha8 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 48) 8 := c.ha 6 (by decide)
  have ho : 48 % 8 = 0 ∧ 48 < 32768 := ⟨rfl, by decide⟩
  obtain ⟨-, -, h2, h3⟩ := ckcRel_x hs
  refine WP.mono (WP.and (WP.block_append_iff.mp hh) (WP.keep [.x8] (Q := fun t => t.gpr .x8 = stackArg s 6)
    (by brun [exec_ldrSp ho ha8, hB']) (by decide) (by decide) (by decide +kernel))) fun t ⟨hw, h8, k⟩ =>
      ⟨s, hs, h8.trans (congrArg CkP.B hs.2), (k.gpr .x2 (by decide)).trans h2, (k.gpr .x3 (by decide)).trans h3, hw⟩

/-- `vg_rsa_check_crt_key` leaks the same in runs that agree on the public
data. -/
theorem ckcCode_ct : RelCT isa (Two CkcRel) CheckCrtKey.code fun _ _ => True := by
  unfold CheckCrtKey.code
  refine RelCT.seq ckcEntry_ct (RelCT.seq (R := Two Ckc3) ?_ ?_)
  -- The check of `e`.
  · refine two_piece [.x4, .x5] (fun p s₁ s₂ ⟨σ₁, c₁, h₁⟩ ⟨σ₂, c₂, h₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.x4, h₂.x4, (ckcRel_x c₁).2.2.1, (ckcRel_x c₂).2.2.1]
      · rw [h₁.x5, h₂.x5, ofNat_toNat64, ofNat_toNat64, (ckcRel_x c₁).2.2.2, (ckcRel_x c₂).2.2.2])
      (by taint_decide) ?_
    rintro p t ⟨s, hs, h⟩
    have c := ckcCtx_of hs.1
    have heb := c.e.congrK h.inScr h.keep
    have hel : (ckcIn s).eb.length = (s.gpr .x3).toNat := bytesAt_length _ _ _
    have hel1 : 1 ≤ (s.gpr .x3).toNat := c.L.el1
    have hel2 : (s.gpr .x3).toNat ≤ (s.gpr .x1).toNat := c.L.el2
    have hk2 : (s.gpr .x1).toNat ≤ 1024 := c.L.k2
    refine WP.mono (expCheck_ok (eb := (ckcIn s).eb) h.x4 h.x5 hel1 (by omega)
      (fun i hi => heb.rd i (by rw [hel]; exact hi)) ?_) fun t' ⟨hz, hm, k⟩ => ⟨s, t, hs, h, hm, k, ?_⟩
    · rw [← hel]
      refine List.ext_getElem (by simp [Spec.Rsa.bytesAt]) fun i h1 h2 => ?_
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
      exact (heb.val i h1).symm
    · rw [hz, ← hs.2]; rfl
  -- `fail` or the check of `n`.
  refine two_ite (fun p s₁ s₂ ⟨_, _, _, _, _, _, z₁⟩ ⟨_, _, _, _, _, _, z₂⟩ => by
    rw [eval_zero, eval_zero, z₁, z₂]) (ckcFail_ct.mono (fun _ _ h => h) fun _ _ h => h) ?_
  refine RelCT.seq (R := Two Ckc4) (RelCT.block_append (RelCT.seq (R := Two Ckc3b) ?_ ?_)) ?_
  · refine two_piece [.x0] (fun p s₁ s₂ ⟨⟨σ₁, t₁, c₁, h₁, _, k₁, _⟩, _⟩ ⟨⟨σ₂, t₂, c₂, h₂, _, k₂, _⟩, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [k₁.gpr .x0 (by decide), k₂.gpr .x0 (by decide), h₁.x0, h₂.x0]
      exact (congrArg CkP.B c₁.2).trans (congrArg CkP.B c₂.2).symm) (by taint_decide) ?_
    rintro p t ⟨⟨s, t₁, hs, h, hm, k, hz⟩, he⟩
    have hev : Spec.Rsa.exponentValid (Spec.Rsa.os2ip p.eb) = true := by
      rw [eval_zero, hz] at he
      cases hv : Spec.Rsa.exponentValid (Spec.Rsa.os2ip p.eb)
      · rw [hv] at he; exact absurd he (by decide)
      · rfl
    have c := ckcCtx_of hs.1
    have hs₂ := h.scr.congr k.wr
    have hn := hs₂.nowrap
    have hZ : 128 * (s.gpr .x1).toNat ≤ (stackArg s 7).toNat * 8 := c.L.z
    have hk1 : 64 ≤ (s.gpr .x1).toNat := c.L.k1
    have h0 : t.gpr .x0 = stackArg s 6 := (k.gpr .x0 (by decide)).trans h.x0
    have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off (stackArg s 6) (8 * i)) 8 := fun i hi => hs₂.ld (by omega)
    have aN : word t.mem (stackArg s 6) (8 * Public.sN) = s.gpr .x0 := by rw [hm]; exact h.args.n
    have aK : word t.mem (stackArg s 6) (8 * Public.sK) = BitVec.ofNat 64 (s.gpr .x1).toNat := by
      rw [hm]; exact h.args.k
    refine WP.mono (WP.keep [.x2, .x3] (Q := fun t' => t'.gpr .x2 = s.gpr .x0 ∧
        t'.gpr .x3 = BitVec.ofNat 64 (s.gpr .x1).toNat ∧ t'.mem = t.mem) (by
      brun [h0, hdr_enc (show Public.sN < 32 by decide), hdr_enc (show Public.sK < 32 by decide),
        hl Public.sN (by decide), hl Public.sK (by decide), aN, aK])
      (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨h2, h3, hm'⟩, k'⟩ =>
        ⟨s, t₁, hs, h, by rw [hm', hm], (k.trans k').mono (by decide), by rw [h2, ← hs.2]; rfl,
          by rw [h3, ← hs.2]; rfl, hev⟩
  · refine two_piece [.x2, .x3] (fun p s₁ s₂ ⟨_, _, _, _, _, _, a₁, b₁, _⟩ ⟨_, _, _, _, _, _, a₂, b₂, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [a₁, a₂]
      · rw [b₁, b₂]) (by taint_decide) ?_
    rintro p t ⟨s, t₁, hs, h, hm, k, h2, h3, hev⟩
    have c := ckcCtx_of hs.1
    have hnb := c.n.congrK (by rw [hm]; exact h.inScr) (h.keep.trans k)
    have hnl : (ckcIn s).nb.length = (s.gpr .x1).toNat := bytesAt_length _ _ _
    have hk1 : 64 ≤ (s.gpr .x1).toNat := c.L.k1
    have hk2 : (s.gpr .x1).toNat ≤ 1024 := c.L.k2
    rw [← hs.2] at h2 h3
    refine WP.mono (WP.keep [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] (invalid_ok h2 h3 hk1 hk2 hnl
      (fun i hi => hnb.rd i (by rw [hnl]; exact hi)) (fun i hi => hnb.val i _))
      (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨hz, hm', _⟩, k'⟩ =>
        ⟨s, t₁, hs, h, by rw [hm', hm], (k.trans k').mono (by decide), by rw [hz, ← hs.2]; rfl, hev⟩
  -- `fail` or `main`.
  refine two_ite (fun p s₁ s₂ ⟨_, _, _, _, _, _, z₁, _⟩ ⟨_, _, _, _, _, _, z₂, _⟩ => by
    rw [eval_zero, eval_zero, z₁, z₂]) (ckcFail_ct.mono (fun _ _ h => h) fun _ _ h => h) ?_
  exact ckcMain_ct.mono (fun _ _ h => two_mono (fun p t ⟨⟨s, t₁, hs, h, hm, k, _⟩, _⟩ =>
    ⟨ckcIn s, hs.2, ckcPre_of (ckcCtx_of hs.1) h hm k, rfl⟩) h) fun _ _ h => h

/-- `vg_rsa_check_crt_key` is constant time but for `n` and `e`. -/
theorem ckcCode_constantTime : ConstantTime isa ckcA.pre ckcA.pub CheckCrtKey.code := by
  refine RelCT.constantTime (ckcCode_ct.mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨(ckcIn s₁).pub, ⟨h₁, rfl⟩, ⟨h₂, ?_⟩,
    hp.2.1⟩) fun _ _ h => h)
  obtain ⟨hr, hsp, ha, hn, he⟩ := hp
  have r : ∀ r ∈ argRegs, s₂.gpr r = s₁.gpr r := fun r h => (hr r h).symm
  have a : ∀ j < 8, stackArg s₂ j = stackArg s₁ j := fun j hj => by
    have := congrArg (fun l => l[j]?) ha
    simp only [List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.some.injEq] at this
    exact this.symm
  have w₁ := h₁.2.2.1
  have w₂ := h₂.2.2.1
  simp only [CkIn.pub, ckcIn, CkP.mk.injEq]
  refine ⟨a 6 (by decide), by rw [a 7 (by decide)], by rw [r .x1 (by decide)], by rw [r .x1 (by decide), r .x5 (by decide), r .x7 (by decide)], by rw [r .x3 (by decide)],
    by rw [r .x5 (by decide)], by rw [r .x5 (by decide)], by rw [r .x7 (by decide)], r .x0 (by decide),
    r .x2 (by decide), r .x4 (by decide), r .x4 (by decide), r .x6 (by decide), a 0 (by decide), a 2 (by decide),
    a 4 (by decide), hn.symm, he.symm, ?_⟩
  rw [w₁, w₂, a 6 (by decide), a 7 (by decide)]

end VG.Proof.Rsa.AArch64
