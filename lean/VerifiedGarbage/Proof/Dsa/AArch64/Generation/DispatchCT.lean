module
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.NativeParametersCT
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Entry

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GenerateCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Dispatch
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextSuccess
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.NativeParametersCT
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Entry
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GenerateCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Dispatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextSuccess
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Public parameter lengths select one of the three verified generators -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Proof.MillerRabin.AArch64 VG.Impl.Dsa.AArch64.Generation

def DispatchBefore (p : ParameterPublic) : State → Prop :=
  ParameterStart p.context.geo.pLen p.context.geo.qLen p

def DispatchChecked (len : Nat) (p : ParameterPublic) (s : State) : Prop :=
  DispatchBefore p s ∧ s.gpr .x3 = BitVec.ofNat 64 p.context.geo.pLen ∧
    isa.eval (.zero .x .x4) s = some (BitVec.ofNat 64 p.context.geo.pLen == BitVec.ofNat 64 len)

theorem dispatchBefore_congr {p : ParameterPublic} {s t : State}
    (h : DispatchBefore p s) (hm : t.mem = s.mem) (hk : Keep [.x3, .x4] s t) : DispatchBefore p t := by
  obtain ⟨⟨W, hW, h16⟩, hp, hq⟩ := h
  exact ⟨⟨W, hW.congr hm hk, h16⟩, hp, hq⟩

theorem dispatch_check :
    RelCT isa (Two (DispatchBefore)) (.block [.ldrSp .x3 136, .subImm .x .x4 .x3 128])
      (Two (DispatchChecked 128)) := by
  refine two_post (two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)) ?_
  intro p s h
  obtain ⟨W, hm, _⟩ := h.1
  obtain ⟨V, R⟩ := hm.rep
  have h17 := (hm.slots 17 (by simp [generationSlots])).trans p.context.pLenSlot
  refine WP.mono (lengthTest_ok hm.layout R) fun t ⟨ha, hz, he, hk⟩ => ?_
  exact ⟨dispatchBefore_congr h he hk, ha.trans h17, by simpa only [h17] using hz⟩

def DispatchLarge (p : ParameterPublic) (s : State) : Prop :=
  DispatchBefore p s ∧ s.gpr .x3 = BitVec.ofNat 64 p.context.geo.pLen ∧ p.context.geo.pLen ≠ 128

def DispatchLargeChecked (p : ParameterPublic) (s : State) : Prop :=
  DispatchBefore p s ∧ p.context.geo.pLen ≠ 128 ∧
    isa.eval (.zero .x .x4) s = some (BitVec.ofNat 64 p.context.geo.pLen == (256#64))

theorem dispatch_check256 :
    RelCT isa (Two (DispatchLarge)) (.block [.subImm .x .x4 .x3 256])
      (Two (DispatchLargeChecked)) := by
  refine two_piece [.x3] ?_ (by taint_decide) ?_
  · intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hs.2.1.trans ht.2.1.symm
  · intro p s ⟨h, ha, hn⟩
    refine WP.mono lengthTest256_ok fun t ⟨hz, he, hk⟩ => ?_
    exact ⟨dispatchBefore_congr h he hk, hn, by simpa only [ha] using hz⟩

theorem dispatch_ct (H : GenerationHashes) (M : Mont)  (K : Kernel)
     :
    RelCT isa (Two (DispatchBefore)) (dispatch H.sha1 H.sha256 M.mm K.run) (fun _ _ => True) := by
  unfold dispatch
  refine RelCT.seq (dispatch_check) (two_ite (fun _ _ _ hs ht => hs.2.2.trans ht.2.2.symm) ?_ ?_)
  · apply two_map (fun p : ParameterPublic => p) ?_ (generate_ct H M K 128 20 (Or.inl ⟨rfl, rfl⟩))
    intro p s h
    have hb := Option.some.inj (h.1.2.2.symm.trans h.2)
    rcases p.context.geo.lengths with ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩
    · simpa only [DispatchBefore, hp, hq] using h.1.1
    all_goals simp [hp] at hb
  · have tail : RelCT isa (Two (DispatchLarge))
        (.seq (.block [.subImm .x .x4 .x3 256])
          (.ite (.zero .x .x4) (generate H.sha1 H.sha256 M.mm K.run 256 32)
            (generate H.sha1 H.sha256 M.mm K.run 384 32))) (fun _ _ => True) := by
      refine RelCT.seq (dispatch_check256) (two_ite (fun _ _ _ hs ht => hs.2.2.trans ht.2.2.symm) ?_ ?_)
      · apply two_map (fun p : ParameterPublic => p) ?_ (generate_ct H M K 256 32 (Or.inr (Or.inl ⟨rfl, rfl⟩)))
        intro p s h
        have hb := Option.some.inj (h.1.2.2.symm.trans h.2)
        rcases p.context.geo.lengths with ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩
        · exact False.elim (h.1.2.1 hp)
        · simpa only [DispatchBefore, hp, hq] using h.1.1
        · simp [hp] at hb
      · apply two_map (fun p : ParameterPublic => p) ?_ (generate_ct H M K 384 32 (Or.inr (Or.inr ⟨rfl, rfl⟩)))
        intro p s h
        have hb := Option.some.inj (h.1.2.2.symm.trans h.2)
        rcases p.context.geo.lengths with ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩
        · exact False.elim (h.1.2.1 hp)
        · simp [hp] at hb
        · simpa only [DispatchBefore, hp, hq] using h.1.1
    apply two_map (fun p : ParameterPublic => p) ?_ tail
    intro p s h
    refine ⟨h.1.1, h.1.2.1, fun hp => ?_⟩
    have hb := Option.some.inj (h.1.2.2.symm.trans h.2)
    simp [hp] at hb

end VG.Proof.Dsa.AArch64.Generation
