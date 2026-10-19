module
public import Mathlib.Tactic.Conv
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Pack
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PackInto
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # Pack all three generated parameters into p || q || g -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem pack_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    {pb qb gb : List Byte} {pLen qLen : Nat}
    (L : Lay s F S) (R : Rep s.mem F S V W)
    (hp : pb.length = pLen) (hq : qb.length = qLen) (hg : gb.length = pLen)
    (hl : 2 ≤ pLen ∧ 2 ≤ qLen ∧ 2 * pLen + qLen ≤ 1024)
    (sp : Src s (off (W 5) packed) (2 * pLen + qLen) (off (W 5) Impl.Dsa.Generation.Layout.p) pb)
    (sq : Src s (off (W 5) packed) (2 * pLen + qLen) (off (W 5) q) qb)
    (sg : Src s (off (W 5) packed) (2 * pLen + qLen) (off (W 5) g) gb)
    (hwr : ∀ i < 2 * pLen + qLen, InRegions s.wr (off (off (W 5) packed) i) 1)
    (hF : (⟨F, frameBytes⟩ : Region).Disjoint ⟨off (W 5) packed, 2 * pLen + qLen⟩)
    (hS : (⟨S, oRsa⟩ : Region).Disjoint ⟨off (W 5) packed, 2 * pLen + qLen⟩) :
    WP isa (Impl.Dsa.X86_64.Generation.pack pLen qLen) s fun t =>
      Spec.Rsa.bytesAt t.mem (off (W 5) packed) (2 * pLen + qLen) = pb ++ qb ++ gb ∧
      Lay t F S ∧ Rep t.mem F S V W ∧
      Frame [⟨off (W 5) packed, 2 * pLen + qLen⟩] s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t := by
  unfold Impl.Dsa.X86_64.Generation.pack
  change WP isa (.seq _ (.seq _ _)) s _
  have first := packInto_ok (d := 0) L R (by decide : Impl.Dsa.Generation.Layout.p < 2 ^ 31)
    (by omega) hl.2.2 (by omega) sp hwr hF hS
  simp only [Nat.add_zero, hp] at first
  refine WP.seq (WP.mono first fun u ⟨bu, Lu, Ru, _, fu, ku⟩ => ?_)
  have second := packInto_ok (d := pLen) Lu Ru (by decide : q < 2 ^ 31)
    (by omega) hl.2.2 (by omega) (sq.congrK fu ku)
    (fun i hi => by rw [ku.2.2]; exact hwr i hi) hF hS
  simp only [hq] at second
  refine WP.seq (WP.mono second fun v ⟨bv, Lv, Rv, fv, iv, kv⟩ => ?_)
  have third := packInto_ok (d := pLen + qLen) Lv Rv (by decide : g < 2 ^ 31)
    (by omega) hl.2.2 (by omega) (sg.congrK (fu.trans iv) (ku.trans kv))
    (fun i hi => by rw [kv.2.2, ku.2.2]; exact hwr i hi) hF hS
  simp only [hg] at third
  simp only [Impl.Bignum.X86_64.seqs, Nat.add_assoc]
  refine WP.mono third fun t ⟨bt, Lt, Rt, ft, it, kt⟩ => ?_
  have keep := (ku.trans kv).trans kt
  have inside := (fu.trans iv).trans it
  refine ⟨?_, Lt, Rt, ?_, keep.mono (by decide)⟩
  · have preserveP : Spec.Rsa.bytesAt t.mem (off (W 5) packed) pLen = pb := by
      rw [VG.Proof.Dsa.Generation.frame_bytesAt ft (by
        intro r hr; rcases List.mem_singleton.mp hr with rfl
        exact Offset.base_disjoint _ (by omega) (by omega)) (by omega),
        VG.Proof.Dsa.Generation.frame_bytesAt fv (by
          intro r hr; rcases List.mem_singleton.mp hr with rfl
          exact Offset.base_disjoint _ (by omega) (by omega)) (by omega)]
      simpa [off] using bu
    have preserveQ : Spec.Rsa.bytesAt t.mem (off (off (W 5) packed) pLen) qLen = qb := by
      rw [VG.Proof.Dsa.Generation.frame_bytesAt ft (by
        intro r hr; rcases List.mem_singleton.mp hr with rfl
        exact Offset.disjoint _ (Or.inl (by omega)) (by omega) (by omega)) (by omega)]
      exact bv
    rw [show 2 * pLen + qLen = (pLen + qLen) + pLen by omega,
      VG.Proof.Dsa.Generation.bytesAt_append, VG.Proof.Dsa.Generation.bytesAt_append,
      preserveP, preserveQ, bt]
  · intro a ha
    apply inside a
    have hn := ha ⟨off (W 5) packed, 2 * pLen + qLen⟩ (by simp)
    change ¬ ofs (off (W 5) packed) a < 2 * pLen + qLen at hn
    omega

end VG.Proof.Dsa.X86_64.Generation
