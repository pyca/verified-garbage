module
public import VerifiedGarbage.Proof.Dsa.AArch64.Run
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Table
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Arguments
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateFromFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.WorkspaceBase
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.FrameWord
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Workspace

/-! # Reduce the shaped candidate from an uninitialized arithmetic workspace -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Rsa.AArch64 VG.Proof.RsaOaep.AArch64
open VG.Impl.Bignum.AArch64 VG.Impl.Dsa.Generation.Layout

theorem reduceFromFrame_ok {s : State} {B F S : Addr} {Z w pLen qLen : Nat}
    {V : Nat → Byte} {W : Nat → BitVec 64} {xb qb : List Byte}
    (L : Lay s F S) (R : Rep s.mem F S V W) (hS : Scr s B Z)
    (hB : W 5 + BitVec.ofNat 64 arithmetic = B)
    (hZ : slot w 16 ≤ Z) (hw1 : 2 ≤ w) (hw48 : w ≤ 48)
    (hpLen : pLen = 8 * w) (hqLen : qLen ≤ pLen)
    (hsep : ∀ k < 34, ∀ j < 32, Mem.Sep (VG.Proof.Bignum.off F (8 * k)) 8 (VG.Proof.Bignum.off B (8 * j)) 8)
    (hframe : ∀ k < 34, ∀ i < 8, Z ≤ ofs B (VG.Proof.Bignum.off (VG.Proof.Bignum.off F (8 * k)) i))
    (sx : Src s B Z (VG.Proof.Bignum.off (W 5) shaped) xb) (sq : Src s B Z (VG.Proof.Bignum.off (W 5) q) qb)
    (hx : xb.length = pLen) (hq : qb.length = qLen) (hqposlen : 1 ≤ qLen)
    (hqpos : 0 < Spec.Rsa.os2ip qb) (hqfit : 2 * Spec.Rsa.os2ip qb < 2 ^ (64 * w))
    (hpw : ∀ i < pLen, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) p) i) 1)
    (hew : ∀ i < pLen, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) exponent) i) 1)
    (hpo : ∀ i < pLen, Z ≤ ofs B (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) p) i))
    (heo : ∀ i < pLen, Z ≤ ofs B (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) exponent) i))
    (hpe : ∀ i < pLen, ∀ j < pLen, VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) p) i ≠ VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) exponent) j) :
    WP isa (seqs [.block Impl.Dsa.AArch64.Generation.workspaceBase,
      Impl.Dsa.AArch64.Generation.workspace w, Impl.Dsa.AArch64.Generation.candidateFromFrame pLen qLen]) s fun t =>
      let value := Spec.Rsa.os2ip xb + 1 - Spec.Rsa.os2ip xb % (2 * Spec.Rsa.os2ip qb)
      Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off (W 5) p) pLen = Spec.Dsa.encodeBE pLen value ∧
      Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off (W 5) exponent) pLen =
        Spec.Dsa.encodeBE pLen ((value - 1) / Spec.Rsa.os2ip qb) ∧
      Ws t B Z w ∧ VG.Proof.Bignum.word t.mem B 160 = VG.Proof.Bignum.off (W 5) p ∧
      Frame [⟨B, Z⟩, ⟨VG.Proof.Bignum.off (W 5) p, pLen⟩, ⟨VG.Proof.Bignum.off (W 5) exponent, pLen⟩] s.mem t.mem ∧
      Keep (.x0 :: mmRegs) s t := by
  simp only [seqs]
  refine WP.seq (WP.mono (workspaceBase_ok L R hB) fun u ⟨hdi, hm, ku⟩ => ?_)
  have sxu := sx.congrK (fun a _ => by rw [hm]) ku
  have squ := sq.congrK (fun a _ => by rw [hm]) ku
  refine WP.seq (WP.mono (workspace_ok (hS.congr ku.wr) hdi hZ hw1 hw48)
    fun v ⟨hv, _, fv, kv⟩ => ?_)
  have hz : 256 ≤ Z := Nat.le_trans (Nat.le_add_right 256 _) hZ
  have hb : ∀ r ∈ workspaceRanges, r.1 + r.2 ≤ Z := by
    simp only [workspaceRanges, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only <;> omega
  refine WP.mono (candidateFromFrame_ok hv hpLen hqLen (by omega)
    (kv.sp.trans (ku.sp.trans L.sp))
    (fun k hk => by rw [kv.rd, kv.wr, ku.rd, ku.wr]; exact L.ld (d := 8 * k) (n := 8) (by unfold VG.Impl.RsaOaep.AArch64.frameBytes; omega))
    (fun k hk => (frame_word_of_workspace fv hb (hframe k hk)).trans (by rw [hm]; exact R.fr k hk))
    hsep (sxu.congrK (InScr.of_frm fv hb) kv) (squ.congrK (InScr.of_frm fv hb) kv)
    hx hq hqposlen hqpos hqfit
    (fun i hi => by rw [kv.wr, ku.wr]; exact hpw i hi)
    (fun i hi => by rw [kv.wr, ku.wr]; exact hew i hi) hpo heo hpe)
    fun t ⟨tp, te, ht, hp, ft, kt⟩ => ?_
  refine ⟨tp, te, ht, hp, ?_, ((ku.trans kv).trans kt).mono (by decide)⟩
  have fs : Frame [⟨B, Z⟩, ⟨VG.Proof.Bignum.off (W 5) p, pLen⟩, ⟨VG.Proof.Bignum.off (W 5) exponent, pLen⟩] s.mem v.mem := by
    intro a ha
    rw [fv a (fun r hr => Or.inr (Nat.le_trans (hb r hr) (by
      have hn := ha ⟨B, Z⟩ (by simp)
      change ¬ ofs B a < Z at hn
      omega))), hm]
  exact fs.trans ft

end VG.Proof.Dsa.AArch64.Generation
