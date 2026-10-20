module
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Proof.Dsa.X86_64.Finish
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.GeneratorStep
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorPowerFresh
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorInput
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
import VerifiedGarbage.Proof.Framework.Omega

/-! # Evaluate h^((p−1)/q) while retaining the persistent generation frame -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Layout

theorem generatorEvaluate_ok (M : Mont) (Sq : MontS) {s : State} {B F S hp : Addr}
    {len : Nat} {pb hb eb : List Byte} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) (hB : W 5 = B) (hhp : W 21 = hp)
    (hs : Scr s B activeBytes) (hl : len = 128 ∨ len = 256 ∨ len = 384)
    (hpl : pb.length = len) (hhl : hb.length = len) (hel : eb.length = len)
    (hm : 1 < Spec.Dsa.decodeBE pb) (hodd : Spec.Dsa.decodeBE pb % 2 = 1)
    (sp : Src s B activeBytes (off B VG.Impl.Dsa.Generation.Layout.p) pb)
    (sh : Src s B activeBytes hp hb)
    (se : Src s B activeBytes (off B VG.Impl.Dsa.Generation.Layout.exponent) eb)
    (hout : ∀ i < len, InRegions s.wr (off (off B VG.Impl.Dsa.Generation.Layout.g) i) 1)
    (houtside : ∀ i < len, activeBytes ≤ ofs B (off (off B VG.Impl.Dsa.Generation.Layout.g) i))
    (hF : ∀ r ∈ [⟨B, activeBytes⟩, ⟨off B VG.Impl.Dsa.Generation.Layout.g, len⟩], (⟨F, frameBytes⟩ : Region).Disjoint r)
    (hS : ∀ r ∈ [⟨B, activeBytes⟩, ⟨off B VG.Impl.Dsa.Generation.Layout.g, len⟩], (⟨S, oRsa⟩ : Region).Disjoint r) :
    WP isa (Impl.Dsa.X86_64.Generation.generatorEvaluate Sq.mm M.mm len) s fun t =>
      Spec.Rsa.bytesAt t.mem (off B VG.Impl.Dsa.Generation.Layout.g) len =
        Spec.Dsa.encodeBE len (Spec.Dsa.powMod (Spec.Dsa.decodeBE hb) (Spec.Dsa.decodeBE eb) (Spec.Dsa.decodeBE pb)) ∧
      Lay t F S ∧ Rep t.mem F S V W ∧
      Frame [⟨B, activeBytes⟩, ⟨off B VG.Impl.Dsa.Generation.Layout.g, len⟩] s.mem t.mem ∧
      Keep (.rdi :: coreRegs) s t := by
  unfold Impl.Dsa.X86_64.Generation.generatorEvaluate
  refine WP.seq (WP.mono (generatorInput_ok L R hB hhp (hs.st (by decide)))
    fun u ⟨hdi, hptr, fu, ku⟩ => ?_)
  have ff : Frm B [(272, 8)] s.mem u.mem := Frm.of_outside fu (by simp)
  have bounds : ∀ r ∈ [(272, 8)], r.1 + r.2 ≤ activeBytes := by
    intro r hr; rcases List.mem_singleton.mp hr with rfl; decide
  refine WP.mono (generatorPowerFresh_ok M Sq (hs.congr ku.2.2) hdi hl hpl hhl hel hm hodd hptr
    (sp.congrK (InScr.of_frm ff bounds) ku) (sh.congrK (InScr.of_frm ff bounds) ku)
    (se.congrK (InScr.of_frm ff bounds) ku)
    (fun i hi => by rw [ku.2.2]; exact hout i hi) houtside) fun t ⟨result, ft, kt⟩ => ?_
  have fg : Frame [⟨B, activeBytes⟩, ⟨off B VG.Impl.Dsa.Generation.Layout.g, len⟩] s.mem u.mem := by
    intro a ha
    apply fu a
    right
    have hn := ha ⟨B, activeBytes⟩ (by simp)
    change ¬ ofs B a < activeBytes at hn
    unfold activeBytes at hn
    omega
  have frame := fg.trans ft
  have Rt := rep_of_disjoint_frame R frame hF hS
  have keep := ku.trans kt
  exact ⟨result, lay_of_rep L R Rt rfl (keep.gpr (by decide)) keep.2.2, Rt, frame, keep.mono (by decide)⟩

end VG.Proof.Dsa.X86_64.Generation
