module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorPlan
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.GeneratorStep
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Dsa.X86_64.Finish

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorFromFrame
import VerifiedGarbage.Impl.Dsa.Generation.Layout
import VerifiedGarbage.Proof.Dsa.X86_64.Call
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Impl.Dsa.X86_64.Generation.GeneratorPower
import VerifiedGarbage.Proof.Dsa.X86_64.PublicCalls
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorModulus
import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorInput
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
/-! # Generator range and power stages preserve their common memory invariant -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/GeneratorFootprint.lean`, which only this module imported.
section

/-! # Global memory footprint of the reused generator exponentiation -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.Proof.Bignum VG.Proof.Dsa.X86_64 VG.Impl.Dsa.Layout
open VG.Impl.Bignum.X86_64

theorem generator_power_frame {B : Addr} {len : Nat} {m m' : Mem}
    (hl : len = 128 ∨ len = 256 ∨ len = 384)
    (hf : CallFrame B pWorkspace (len / 8) (off B VG.Impl.Dsa.Generation.Layout.g) len m m') :
    Frame [⟨B, activeBytes⟩, ⟨off B VG.Impl.Dsa.Generation.Layout.g, len⟩] m m' := by
  have hsize : pWorkspace + slot (len / 8) 8 + tabBytes (len / 8) ≤ activeBytes := by
    rcases hl with hh | hh | hh <;> rw [hh] <;> decide
  have sub : Region.Sub ⟨off B pWorkspace, slot (len / 8) 8 + tabBytes (len / 8)⟩ ⟨B, activeBytes⟩ :=
    Offset.sub_base B (by omega)
  intro a ha
  have hn := ha ⟨B, activeBytes⟩ (by simp)
  have hn' : ¬ (⟨off B pWorkspace, slot (len / 8) 8 + tabBytes (len / 8)⟩ : Region).Contains a 1 :=
    fun hc => hn (sub a hc)
  apply hf a
  · right
    change ¬ ofs B a < activeBytes at hn
    unfold activeBytes at hn
    omega
  · intro r hr
    right
    have hb := (workRanges_ok (len / 8) r hr).2
    change ¬ ofs (off B pWorkspace) a < slot (len / 8) 8 + tabBytes (len / 8) at hn'
    omega
  · intro i hi he
    apply ha ⟨off B VG.Impl.Dsa.Generation.Layout.g, len⟩ (by simp)
    rw [he]
    exact Offset.contains_base _ (by omega) (by rcases hl with hh | hh | hh <;> omega)

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/GeneratorPower.lean`, which only this module imported.
section

/-! # Generator construction uses the existing verified public exponentiation -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64

theorem generatorPower_ok (M : Mont) (Sq : MontS) {s : State} {B : Addr}
    {len modulus : Nat} {mi : BitVec 64} {hb eb : List Byte}
    (h : Good s B activeBytes outerWords 0)
    (child : ChildReady s.mem B pWorkspace (len / 8) modulus mi)
    (hl : len = 128 ∨ len = 256 ∨ len = 384)
    (hm : 1 < modulus) (hodd : modulus % 2 = 1)
    (has : OperandBytes s B activeBytes ⟨.input .g, .pLen⟩ hb)
    (hes : OperandBytes s B activeBytes ⟨.input .x, .pLen⟩ eb)
    (hhl : hb.length = len) (hel : eb.length = len)
    (hout : ∀ i < len, InRegions s.wr (off (off B VG.Impl.Dsa.Generation.Layout.g) i) 1)
    (houtside : ∀ i < len, activeBytes ≤ ofs B (off (off B VG.Impl.Dsa.Generation.Layout.g) i)) :
    WP isa (Impl.Dsa.X86_64.Generation.generatorPower Sq.mm M.mm) s fun t =>
      Good t B activeBytes outerWords 0 ∧ ChildReady t.mem B pWorkspace (len / 8) modulus mi ∧
      Spec.Rsa.bytesAt t.mem (off B VG.Impl.Dsa.Generation.Layout.g) len =
        Spec.Dsa.encodeBE len (Spec.Dsa.powMod (Spec.Dsa.decodeBE hb) (Spec.Dsa.decodeBE eb) modulus) ∧
      CallFrame B pWorkspace (len / 8) (off B VG.Impl.Dsa.Generation.Layout.g) len s.mem t.mem ∧
      Keep coreRegs s t := by
  have hlen : 1 ≤ len ∧ len ≤ 1024 ∧ 2 ≤ len / 8 ∧ len / 8 ≤ 48 ∧
      len / 8 = (len + 7) / 8 ∧ pWorkspace + slot (len / 8) 8 + tabBytes (len / 8) ≤ activeBytes := by
    rcases hl with hh | hh | hh <;> rw [hh] <;> decide
  exact corePublicPow_ok M Sq h child (by decide) (by decide) hlen.2.2.2.2.2 (by decide)
    hlen.2.2.1 hlen.2.2.2.1 hlen.2.2.2.1 (by decide) hm hodd
    ⟨.input .g, .pLen⟩ ⟨.input .x, .pLen⟩ ⟨.local VG.Impl.Dsa.Generation.Layout.g, .pLen⟩
    (by trivial) (by trivial) (by change VG.Impl.Dsa.Generation.Layout.g < 2 ^ 31; decide)
    has hes (by omega) (by rw [hhl, ← hlen.2.2.2.2.1]) (by omega) (by omega)
    (by simpa only [hhl] using has.length) hlen.1 (by omega) hlen.2.2.2.2.1 hout houtside

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/GeneratorPowerFresh.lean`, which only this module imported.
section

/-! # Initialize and evaluate one generator power from arbitrary scratch -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64

theorem generatorPowerFresh_ok (M : Mont) (Sq : MontS) {s : State} {B hp : Addr}
    {len : Nat} {pb hb eb : List Byte}
    (hs : Scr s B activeBytes) (hdi : s.gpr .rdi = B)
    (hl : len = 128 ∨ len = 256 ∨ len = 384)
    (hpl : pb.length = len) (hhl : hb.length = len) (hel : eb.length = len)
    (hm : 1 < Spec.Dsa.decodeBE pb) (hodd : Spec.Dsa.decodeBE pb % 2 = 1)
    (hptr : word s.mem B 272 = hp)
    (sp : Src s B activeBytes (off B VG.Impl.Dsa.Generation.Layout.p) pb)
    (sh : Src s B activeBytes hp hb)
    (se : Src s B activeBytes (off B VG.Impl.Dsa.Generation.Layout.exponent) eb)
    (hout : ∀ i < len, InRegions s.wr (off (off B VG.Impl.Dsa.Generation.Layout.g) i) 1)
    (houtside : ∀ i < len, activeBytes ≤ ofs B (off (off B VG.Impl.Dsa.Generation.Layout.g) i)) :
    WP isa (Impl.Dsa.X86_64.Generation.generatorPowerFresh Sq.mm M.mm len) s fun t =>
      Spec.Rsa.bytesAt t.mem (off B VG.Impl.Dsa.Generation.Layout.g) len =
        Spec.Dsa.encodeBE len (Spec.Dsa.powMod (Spec.Dsa.decodeBE hb) (Spec.Dsa.decodeBE eb) (Spec.Dsa.decodeBE pb)) ∧
      Frame [⟨B, activeBytes⟩, ⟨off B VG.Impl.Dsa.Generation.Layout.g, len⟩] s.mem t.mem ∧
      Keep coreRegs s t := by
  unfold Impl.Dsa.X86_64.Generation.generatorPowerFresh
  refine WP.seq (WP.mono (generatorModulus_ok hs hdi hl hpl sp hodd)
    fun u ⟨mi, gu, child, _, ep, plen, gh, fu, ku⟩ => ?_)
  have bounds : ∀ r ∈ [(48, 80), (256, 80)] ++ initRanges pWorkspace (len / 8), r.1 + r.2 ≤ activeBytes := by
    intro r hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, initRanges] at hr
    rcases hr with (rfl | rfl) | (rfl | rfl)
    · decide
    · decide
    · decide
    · rcases hl with hh | hh | hh <;> rw [hh] <;> decide
  have shu := sh.congrK (InScr.of_frm fu bounds) ku
  have seu := se.congrK (InScr.of_frm fu bounds) ku
  have has : OperandBytes u B activeBytes ⟨.input .g, .pLen⟩ hb := by
    refine ⟨?_, ?_⟩
    · change word u.mem B 328 = _
      rw [hhl]; exact plen
    · change Src u B activeBytes (word u.mem B 272) hb
      rw [gh, hptr]; exact shu
  have hes : OperandBytes u B activeBytes ⟨.input .x, .pLen⟩ eb := by
    refine ⟨?_, ?_⟩
    · change word u.mem B 328 = _
      rw [hel]; exact plen
    · change Src u B activeBytes (word u.mem B 288) eb
      rw [ep]; exact seu
  refine WP.mono (generatorPower_ok M Sq gu child hl hm hodd has hes hhl hel
    (fun i hi => by rw [ku.2.2]; exact hout i hi) houtside)
    fun t ⟨_, _, result, ft, kt⟩ => ?_
  have ff : Frame [⟨B, activeBytes⟩, ⟨off B VG.Impl.Dsa.Generation.Layout.g, len⟩] s.mem u.mem := by
    intro a ha
    apply fu a
    intro r hr
    right
    have hn := ha ⟨B, activeBytes⟩ (by simp)
    change ¬ ofs B a < activeBytes at hn
    exact Nat.le_trans (bounds r hr) (by omega)
  exact ⟨result, ff.trans (generator_power_frame hl ft), (ku.trans kt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/GeneratorEvaluate.lean`, which only this module imported.
section

/-! # Evaluate h^((p−1)/q) while retaining the persistent generation frame -/

section
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
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem generatorInputRange_ok {p : GeneratorPlan} {W : Nat → BitVec 64} {s : State}
    (h : GeneratorMemory p W s) :
    WP isa (Impl.Dsa.X86_64.Generation.generatorRangeFromFrame p.len false) s fun t =>
      t.gpr .rax = mask (decide (1 < Spec.Dsa.decodeBE p.hb ∧
        Spec.Dsa.decodeBE p.hb < Spec.Dsa.decodeBE p.pb - 1)) ∧
      GeneratorMemory p W t ∧ Frame p.changed s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t := by
  obtain ⟨V, R⟩ := h.rep
  refine WP.mono (generatorFromFrame_ok false h.layout R h.arithmetic
    (by rw [h.base]; exact p.arithmeticBase) p.width p.workspaceRoom p.frameHeaders p.frameOutside
    (p.frameSeparate _ (by simp)) (p.hashSeparate _ (by simp))
    (by simpa only [h.base] using h.pArithmetic) (by simpa only [Bool.false_eq_true, ↓reduceIte, h.input] using h.hArithmetic)
    p.pLength p.hLength (fun _ => p.pOdd) (fun he => Bool.noConfusion he))
    fun t ⟨hr, Lt, Rt, _, ft, kt⟩ => ?_
  have frame : Frame p.changed s.mem t.mem := ft.mono (by intro r hr; rcases List.mem_singleton.mp hr with rfl; simp [GeneratorPlan.changed])
  exact ⟨hr, h.frame Lt ⟨V, Rt⟩ h.base h.input frame kt.2.1 kt.2.2, frame, kt⟩

theorem generatorEvaluateStage_ok (M : Mont) (Sq : MontS)
    {p : GeneratorPlan} {W : Nat → BitVec 64} {s : State} (h : GeneratorMemory p W s) :
    WP isa (Impl.Dsa.X86_64.Generation.generatorEvaluate Sq.mm M.mm p.len) s fun t =>
      Spec.Rsa.bytesAt t.mem (off p.B g) p.len = Spec.Dsa.encodeBE p.len p.value ∧
      GeneratorMemory p W t ∧ Frame p.changed s.mem t.mem ∧ Keep (.rdi :: coreRegs) s t := by
  obtain ⟨V, R⟩ := h.rep
  refine WP.mono (generatorEvaluate_ok M Sq h.layout R h.base h.input h.parent
    p.width p.pLength p.hLength p.eLength p.pPositive p.pOdd
    h.pParent h.hParent h.eParent h.gWrite p.gParentOutside
    (by intro r hr; exact p.frameSeparate r (by simp only [List.mem_cons] at hr ⊢; exact Or.inr hr))
    (by intro r hr; exact p.hashSeparate r (by simp only [List.mem_cons] at hr ⊢; exact Or.inr hr)))
    fun t ⟨result, Lt, Rt, ft, kt⟩ => ?_
  have frame : Frame p.changed s.mem t.mem := ft.mono (by
    intro r hr; simp only [GeneratorPlan.changed, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h <;> simp [h])
  exact ⟨result, h.frame Lt ⟨V, Rt⟩ h.base h.input frame kt.2.1 kt.2.2, frame, kt⟩

end VG.Proof.Dsa.X86_64.Generation
