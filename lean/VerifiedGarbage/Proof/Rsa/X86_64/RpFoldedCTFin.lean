module

public import VerifiedGarbage.Proof.Rsa.X86_64.RpCT7
public import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedCTCands
import VerifiedGarbage.Proof.Rsa.X86_64.RpCT4
import VerifiedGarbage.Proof.Rsa.X86_64.RpMont
import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpCT6
meta import VerifiedGarbage.Proof.Bignum.CrtFrame
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpCT4
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpFin
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpMont
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.Inv
meta import VerifiedGarbage.Proof.Rsa.X86_64.Loops
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Rsa.X86_64.RpCT5

/-! # Factor extraction following the folded candidate search -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.RecoveryFolded

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt sMask)

open VG.Impl.Rsa.X86_64.Keys.Recover.Folded
open Rp

theorem finA_ct (M : Mont) : RelCT isa (Two GR3) (seqs [.block [.mov .rax (.mem (hdr sC3)), .store (hdr sMask) .rax],
    M.mm aY aY aOne, zeroA fU, .block (ws ++ base aY .r8 ++ base aOne .r10 ++ base fU .rsi ++ ([.mov32 .rbp (.imm 0)] : List Instr)),
    wordLoop 0 subBody]) (Two (FX XT)) := by
  simp only [seqs]
  refine RelCT.seq (R := Two (FX XC)) (blk_gct RpP.B RpP.Z (fun p => wk p.k)
    (fun _ _ ⟨_, _, _, _, _, e, S, _⟩ => e ▸ S.ws) (by taint_decide) fun p s h => ?_) ?_
  · obtain ⟨I, m₀, minv, res, cnt, rfl, S, L, O, hv, hc, hgo, hc3, hy⟩ := h
    dsimp only [RpIn.pub]
    have h256 := hc.ws.h256
    refine WP.mono (WP.keep [.rax] (Q := fun u => u.mem = s.mem.writeW (off I.B (8 * sMask))
        (mask res.isSome)) (by
      xrun [State.ea, hdr, hc.ws.rdi, hdrOff, hc.ws.scr.ld (d := 8 * sC3) (by simp only [sC3, sFn]; omega_arith),
        hc.ws.scr.st (d := 8 * sMask) (by simp only [sMask, sFn]; omega_arith), hc3]) rfl) fun u ⟨m₁, k₁⟩ => ?_
    have hf₁ : Frm I.B (rg (wk I.k) [] [sMask]) s.mem u.mem := by
      rw [m₁]; exact Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sMask, sFn]; omega_arith)) _ _
        (List.mem_singleton_self _)
    exact ⟨I, m₀, res.isSome, rfl, S.step hf₁ (by decide) (by decide) k₁ (by decide), L, O,
      by rw [m₁, word_writeW_self], minv, _, _, hc.congr hf₁ (by decide) (by decide) k₁ (by decide)⟩
  refine RelCT.seq (R := Two (FX fun _ _ => True)) (mm_gct RpP.B RpP.Z (fun p => wk p.k) (fun _ _ h => h.ws) M
    (o := aY) (a := aY) (b := aOne) (by unfold MmUse; decide) fun p s h => ?_) ?_
  · have h' := h
    obtain ⟨I, m₀, c, rfl, S, L, O, hmk, minv, r, t, hc⟩ := h'
    have hg := hc.good
    have hw2 := hc.ws.w2
    exact WP.mono (M.mm_ok hg.1 hg.2 hc.ws.w1 (by omega_arith) (o := aY) (a := aY) (b := aOne) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.hinv
      (by rw [hc.hone, hc.hn]; have := hc.n1; omega_arith)) fun u ⟨_, _, _, ha, k⟩ =>
      h.step (Frm.rg_of_arrays ha [aAcc, aTmp, aY] [] (by decide)) (by decide) (by simp) (by simp) k (by decide)
        fun _ _ _ => trivial
  refine RelCT.seq (R := Two (FX XU)) (zeroA_gct RpP.B RpP.Z (fun p => wk p.k) (fun _ _ h => h.ws)
    (by taint_decide) fun p s h => WP.mono (zeroA_ok h.ws (j := fU) (by decide)) fun u ⟨z, o, k⟩ =>
      h.step (Frm.rg_of_out o (Nat.le_refl _) [fU] [] (by decide)) (by decide) (by simp) (by simp) k (by decide)
        fun I e _ => by subst e; exact z) ?_
  have e : (.seq (.block (ws ++ base aY .r8 ++ base aOne .r10 ++ base fU .rsi ++ [.mov32 .rbp (.imm 0)]))
      (wordLoop 0 subBody) : Prog isa) = .seq (.block (ws ++ (base aY .r8 ++ (base aOne .r10 ++
        (base fU .rsi ++ ([.mov32 .rbp (.imm 0)] : List Instr)))))) (wordLoop 0 subBody) := by
    simp only [List.append_assoc]
  rw [e]
  refine ws_ct RpP.B RpP.Z (fun p => wk p.k) (fun _ _ h => h.ws) (by taint_decide) fun p s h => ?_
  rw [← e]
  have hw := h.ws
  have hn0 := hw.scr.nowrap
  have hZ := hw.hZ
  have hw1 := hw.w1
  have hw2 := hw.w2
  refine WP.seq (WP.mono (subSet_ok hw aY aOne fU) fun t ⟨h12, h8, h10, hsi, hbp, m₄, k₄⟩ => ?_)
  have sY := hw.sl (j := aY) (by decide)
  have sO := hw.sl (j := aOne) (by decide)
  have sU := hw.sl (j := fU) (by decide)
  refine WP.mono (sub_ok (hw.scr.congr k₄.2.2) h8 h10 hsi h12 hbp (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by have := slot_far (w := wk p.k) (show fU ≠ aY by decide); omega_arith)
    (by have := slot_far (w := wk p.k) (show fU ≠ aOne by decide); omega_arith)) fun u ⟨_, _, _, o₅, k₅⟩ => ?_
  rw [m₄] at o₅
  have hf : Frm p.B (rg (wk p.k) [fU] []) s.mem u.mem := Frm.rg_of_out o₅ (by omega_arith) _ _ (by decide)
  refine h.step hf (by decide) (by simp) (by simp) (k₄.trans k₅) (by decide) fun I e z => ?_
  subst e
  dsimp only [RpIn.pub] at *
  show word u.mem I.B (slot (wk I.k) fU + 8 * wk I.k) = 0
  rw [o₅.word (Or.inr (by omega_arith)) (by omega_arith)]
  exact word_above_zero (n := wk I.k) (L := wk I.k + 2) (by omega_arith) (by rw [z]; exact Nat.two_pow_pos _)

theorem fin_ct [InvLaw] (M : Mont) : RelCT isa (Two GR3) (seqs (fin M.mm)) fun _ _ => True := by
  rw [show fin M.mm = [.block [.mov .rax (.mem (hdr sC3)), .store (hdr sMask) .rax], M.mm aY aY aOne, zeroA fU,
      .block (ws ++ base aY .r8 ++ base aOne .r10 ++ base fU .rsi ++ [.mov32 .rbp (.imm 0)]),
      wordLoop 0 subBody] ++ ([inverse fU fV fX₂ aN, zeroA fQ, copyA fQ aN, divmod fQ fR fV fT] ++
      ([.block (ws ++ base fV .rbx ++ base fQ .r10 ++ [.mov32 .rbp (.imm 0)]), wordLoop 0 ltBody,
        .block [.mov .r15 (.reg .rbp)], wordLoop 0 cswapBody] ++
      (storeA fV sP Impl.Bignum.X86_64.Public.sK sMask ++ (storeA fQ sQ Impl.Bignum.X86_64.Public.sK sMask ++
        ([.block retMask] : List (Prog isa)))))) by simp only [fin, List.append_assoc, List.cons_append,
          List.nil_append]]
  refine (ct_app (by simp) (by simp) (finA_ct M) (ct_app (by simp) (by simp) finB_ct (ct_app (by simp)
    (by simp [storeA]) finC_ct (?_ : RelCT isa (Two (FX fun _ _ => True)) _ (Two fun (_ : RpP) (_ : State) => True))))).mono
      (fun _ _ h => h) fun _ _ _ => trivial
  refine RelCT.seqs_append (by simp [storeA]) (by simp [storeA]) (RelCT.seq (R := Two GSr) ?_ ?_)
  · refine (storeR_ct (by decide) (by decide) RpP.pP (fun p s h => ?_) (by taint_decide)).mono
      (fun _ _ h => two_mono (fun p s ⟨I, m₀, c, e, S, L, O, hm, _⟩ => ⟨I, c, e, S.ws, S.args, S.wr, L, O, hm⟩) h)
      fun _ _ h => h
    obtain ⟨I, c, rfl, -, ha, -, L, O, -⟩ := h
    exact ⟨ha.p, O.p, O.sp⟩
  refine RelCT.seqs_append (by simp [storeA]) (by simp) (RelCT.seq (R := Two GSr)
    (storeR_ct (by decide) (by decide) RpP.pQ (fun p s h => ?_) (by taint_decide)) ?_)
  · obtain ⟨I, c, rfl, -, ha, -, L, O, -⟩ := h
    exact ⟨ha.q, O.q, O.sq⟩
  exact (two_taint [.rdi] pins_GSr (by taint_decide)).mono (fun _ _ h => h) fun _ _ _ => ⟨default, trivial, trivial⟩

/-- Preparation, candidates and output preserve the original leakage policy. -/
theorem rest_ct [InvLaw] (M : Mont) : RelCT isa (Two GR0) (Folded.rest M.mm) fun _ _ => True := by
  rw [show Folded.rest M.mm = seqs ([prepare] ++ (mont M.mm ++ ([Folded.candLoop M.mm] ++ fin M.mm))) by
    simp only [Folded.rest, List.append_assoc]]
  exact (ct_app (Ξ := fun (_ : RpP) (_ : State) => True) (by simp) (by simp [mont]) (ct_one prepare_ct)
    (ct_app (by simp [mont]) (by simp [fin]) (mont_ct M)
      (ct_app (by simp) (by simp [fin]) (ct_one (candLoop_ct M)) ((fin_ct M).mono (fun _ _ h => h)
        (fun _ _ _ => ⟨default, trivial, trivial⟩))))).mono (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Rsa.X86_64.RecoveryFolded
