module
public import VerifiedGarbage.Impl.MillerRabin.AArch64.Caller
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Base
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Impl.MillerRabin.AArch64.Caller
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Base
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import Mathlib.Tactic.Push
meta import Mathlib.Tactic.Attr.Core
meta import Aesop.BuiltinRules
meta import Mathlib.Tactic.ToDual
meta import Mathlib.Tactic.ToAdditive
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # The caller's save and restore addresses are fixed by its workspace -/

@[expose] public section

namespace VG.Proof.MillerRabin.AArch64.Caller

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.MillerRabin.AArch64.Caller

private def Loaded (L : VG.Proof.Bignum.AArch64.Ws) (s : State) : Prop :=
  s.gpr .x0 = L.B ∧ s.gpr .x2 = off L.B (slot L.w aOne) ∧ s.gpr .x3 = BitVec.ofNat 64 L.w

private theorem load_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
    (h : Good s B Z w mi) (hZ : slot w 8 ≤ Z) :
    WP isa (.block saveLoad) s (Loaded ⟨B, Z, w⟩) := by
  have hl : ∀ j < 16, InRegions (s.rd ++ s.wr) (off B (8 * j)) 8 :=
    fun j hj => h.scr.ld (by have := hdr_lt_slot w 8 (by omega_arith : j < 32); omega_arith)
  unfold saveLoad Loaded
  brun [h.x0, hdr_enc (show sArr aOne < 32 by decide), hdr_enc (show sW < 32 by decide),
    hl (sArr aOne) (by decide), hl sW (by decide), h.hdr.harr aOne (by decide), h.hdr.hw]

theorem save_ct : RelCT isa (Two GoodW) (.block save) fun _ _ => True := by
  unfold save
  apply RelCT.block_append
  refine RelCT.seq (two_post (Ψ := Loaded) ?_ ?_) ?_
  · exact two_taint [.x0] (fun L s t hs ht r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact hs.choose_spec.1.x0.trans ht.choose_spec.1.x0.symm) (by taint_decide)
  · intro L s h
    obtain ⟨mi, hg, hz⟩ := h
    exact load_ok hg hz
  · exact two_taint [.x0, .x2, .x3] (fun L s t hs ht r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hs.1.trans ht.1.symm
      · exact hs.2.1.trans ht.2.1.symm
      · exact hs.2.2.trans ht.2.2.symm) (by taint_decide)

def RestorePre (L : VG.Proof.Bignum.AArch64.Ws) (s : State) : Prop :=
  Scr s L.B L.Z ∧ slot L.w 8 ≤ L.Z ∧ s.gpr .x19 = L.B ∧
    word s.mem L.B (8 * sW) = BitVec.ofNat 64 L.w ∧
    word s.mem L.B (8 * sArr aOne) = off L.B (slot L.w aOne)

private theorem restore_head_ok {s : State} {L : VG.Proof.Bignum.AArch64.Ws}
    (h : RestorePre L s) : WP isa (.block restoreHead) s (Loaded L) := by
  obtain ⟨hs, hz, h19, hW, hA⟩ := h
  have hl : ∀ j < 16, InRegions (s.rd ++ s.wr) (off L.B (8 * j)) 8 :=
    fun j hj => hs.ld (by have := hdr_lt_slot L.w 8 (by omega_arith : j < 32); omega_arith)
  have ht : InRegions s.wr (off L.B (8 * kFlag)) 8 :=
    hs.st (by have := hdr_lt_slot L.w 8 (show kFlag < 32 by decide); omega_arith)
  have hStoreW (v : BitVec 64) :
      word (s.mem.writeW (off L.B (8 * kFlag)) v) L.B (8 * sW) = BitVec.ofNat 64 L.w :=
    (hdrStore_hdr s.mem L.B v (by decide) (by decide) (by decide)).trans hW
  have hStoreA (v : BitVec 64) :
      word (s.mem.writeW (off L.B (8 * kFlag)) v) L.B (8 * sArr aOne) = off L.B (slot L.w aOne) :=
    (hdrStore_hdr s.mem L.B v (by decide) (by decide) (by decide)).trans hA
  unfold restoreHead Loaded
  brun [VG.Proof.RsaKeyGen.AArch64.exec_addImm_w, BitVec.add_zero, h19,
    hdr_enc (show kFlag < 32 by decide), hdr_enc (show sW < 32 by decide),
    hdr_enc (show sArr aOne < 32 by decide), ht, hl sW (by decide),
    hl (sArr aOne) (by decide), hStoreW, hStoreA]

theorem restore_ct : RelCT isa (Two RestorePre) (.block restore) fun _ _ => True := by
  unfold restore
  apply RelCT.block_append
  refine RelCT.seq (two_post (Ψ := Loaded) ?_ (fun _ _ h => restore_head_ok h)) ?_
  · exact two_taint [.x19] (fun L s t hs ht r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact hs.2.2.1.trans ht.2.2.1.symm) (by taint_decide)
  · exact two_taint [.x0, .x2, .x3] (fun L s t hs ht r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hs.1.trans ht.1.symm
      · exact hs.2.1.trans ht.2.1.symm
      · exact hs.2.2.trans ht.2.2.symm) (by taint_decide)

end VG.Proof.MillerRabin.AArch64.Caller
