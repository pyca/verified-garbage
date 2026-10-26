module
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Slots
import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
public import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Arguments
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateFromFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CheckPrime
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.WorkspaceBase
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Workspace
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp

/-! # Reduce the shaped candidate from an uninitialized arithmetic workspace -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Rsa.X86_64 VG.Proof.RsaOaep.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Dsa.Generation.Layout

theorem reduceFromFrame_ok {s : State} {B F S : Addr} {Z w pLen qLen : Nat}
    {V : Nat → Byte} {W : Nat → BitVec 64} {xb qb : List Byte}
    (L : Lay s F S) (R : Rep s.mem F S V W) (hS : Scr s B Z)
    (hB : W 5 + BitVec.ofNat 64 arithmetic = B)
    (hZ : slot w 16 ≤ Z) (hw1 : 2 ≤ w) (hw2 : w < 2 ^ 24)
    (hpLen : pLen = 8 * w) (hqLen : qLen ≤ pLen)
    (hsep : ∀ k < 37, ∀ j < 32, Mem.Sep (off F (8 * k)) 8 (off B (8 * j)) 8)
    (hframe : ∀ k < 37, ∀ i < 8, Z ≤ ofs B (off (off F (8 * k)) i))
    (sx : Src s B Z (off (W 5) shaped) xb) (sq : Src s B Z (off (W 5) q) qb)
    (hx : xb.length = pLen) (hq : qb.length = qLen) (hqposlen : 1 ≤ qLen)
    (hqpos : 0 < Spec.Rsa.os2ip qb) (hqfit : 2 * Spec.Rsa.os2ip qb < 2 ^ (64 * w))
    (hpw : ∀ i < pLen, InRegions s.wr (off (off (W 5) p) i) 1)
    (hew : ∀ i < pLen, InRegions s.wr (off (off (W 5) exponent) i) 1)
    (hpo : ∀ i < pLen, Z ≤ ofs B (off (off (W 5) p) i))
    (heo : ∀ i < pLen, Z ≤ ofs B (off (off (W 5) exponent) i))
    (hpe : ∀ i < pLen, ∀ j < pLen, off (off (W 5) p) i ≠ off (off (W 5) exponent) j) :
    WP isa (seqs [.block Impl.Dsa.X86_64.Generation.workspaceBase,
      Impl.Dsa.X86_64.Generation.workspace w, Impl.Dsa.X86_64.Generation.candidateFromFrame pLen qLen]) s fun t =>
      let value := Spec.Rsa.os2ip xb + 1 - Spec.Rsa.os2ip xb % (2 * Spec.Rsa.os2ip qb)
      Spec.Rsa.bytesAt t.mem (off (W 5) p) pLen = Spec.Dsa.encodeBE pLen value ∧
      Spec.Rsa.bytesAt t.mem (off (W 5) exponent) pLen =
        Spec.Dsa.encodeBE pLen ((value - 1) / Spec.Rsa.os2ip qb) ∧
      Ws t B Z w ∧ word t.mem B 160 = off (W 5) p ∧
      Frame [⟨B, Z⟩, ⟨off (W 5) p, pLen⟩, ⟨off (W 5) exponent, pLen⟩] s.mem t.mem ∧
      Keep (.rdi :: mmRegs) s t := by
  simp only [seqs]
  refine WP.seq (WP.mono (workspaceBase_ok L R hB) fun u ⟨hdi, hm, ku⟩ => ?_)
  have sxu := sx.congrK (fun a _ => by rw [hm]) ku
  have squ := sq.congrK (fun a _ => by rw [hm]) ku
  refine WP.seq (WP.mono (workspace_ok (hS.congr ku.2.2) hdi hZ hw1 hw2)
    fun v ⟨hv, _, fv, kv⟩ => ?_)
  have hz : 256 ≤ Z := Nat.le_trans (Nat.le_add_right 256 _) hZ
  have hb : ∀ r ∈ [(48, 80), (224, 8)], r.1 + r.2 ≤ Z := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only <;> omega
  refine WP.mono (candidateFromFrame_ok hv hpLen hqLen
    ((kv.gpr (by decide)).trans ((ku.gpr (by decide)).trans L.rsp))
    (fun k hk => by rw [kv.2.1, kv.2.2, ku.2.1, ku.2.2]; exact L.ld (by unfold VG.Impl.RsaOaep.X86_64.frameBytes; omega))
    (fun k hk => by rw [frame_word_of_workspace fv hb (hframe k hk), hm]; exact R.fr k hk)
    hsep (sxu.congrK (InScr.of_frm fv hb) kv) (squ.congrK (InScr.of_frm fv hb) kv)
    hx hq hqposlen hqpos hqfit
    (fun i hi => by rw [kv.2.2, ku.2.2]; exact hpw i hi)
    (fun i hi => by rw [kv.2.2, ku.2.2]; exact hew i hi) hpo heo hpe)
    fun t ⟨tp, te, ht, hp, ft, kt⟩ => ?_
  refine ⟨tp, te, ht, hp, ?_, ((ku.trans kv).trans kt).mono (by decide)⟩
  have fs : Frame [⟨B, Z⟩, ⟨off (W 5) p, pLen⟩, ⟨off (W 5) exponent, pLen⟩] s.mem v.mem := by
    intro a ha
    rw [fv a (fun r hr => Or.inr (Nat.le_trans (hb r hr) (by
      have hn := ha ⟨B, Z⟩ (by simp)
      change ¬ ofs B a < Z at hn
      omega))), hm]
  exact fs.trans ft

end VG.Proof.Dsa.X86_64.Generation
