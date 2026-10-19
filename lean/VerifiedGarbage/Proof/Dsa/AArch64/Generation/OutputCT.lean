module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.NativeParametersCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.FinishOutput
public import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
meta import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.FinishOutput
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch

/-! Output copying and failure zeroing use public frame inputs. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Proof.Rsa.AArch64

private theorem ct_assoc_left {P Q : State → State → Prop} {a b c : Prog isa}
    (h : RelCT isa P (.seq a (.seq b c)) Q) : RelCT isa P (.seq (.seq a b) c) Q := by
  intro s t xs ys u v hp es et
  cases es with
  | seq eab ec =>
    cases eab with
    | seq ea eb =>
      cases et with
      | seq fab fc =>
        cases fab with
        | seq fa fb =>
          obtain ⟨tr, post⟩ := h _ _ _ _ _ _ hp (.seq ea (.seq eb ec)) (.seq fa (.seq fb fc))
          exact ⟨by simpa only [List.append_assoc] using tr, post⟩

structure OutputPublic where
  context : GenerationContext
  accepted : Bool

def OutputBefore (p : OutputPublic) (s : State) : Prop :=
  ∃ W, GenerationMemory p.context W s ∧ (W 19 == (1#64)) = p.accepted

def OutputCopyReady (p : OutputPublic) (s : State) : Prop :=
  s.gpr .x12 = VG.Proof.Bignum.off (p.context.saved 5) Impl.Dsa.Generation.Layout.packed ∧
  s.gpr .x2 = p.context.saved 6 ∧ s.gpr .x9 = p.context.saved 7

theorem outputCopy_ct : RelCT isa (Two OutputBefore) Impl.Dsa.AArch64.Generation.outputCopy
    (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.outputCopy
  refine RelCT.seq (two_post (Ψ := OutputCopyReady) (two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)) ?_)
    (two_taint [.x12, .x2, .x9] ?_ (by taint_decide))
  · intro p s ⟨W, h, _⟩
    obtain ⟨V, R⟩ := h.rep
    have h7 : W 7 = BitVec.ofNat 64 (p.context.saved 7).toNat := by
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using h.slots 7 (by simp [generationSlots])
    exact WP.mono (outputArgs_ok h.layout R h7) fun t ⟨a, b, c, _, _⟩ =>
      show OutputCopyReady p t from ⟨by simpa only [h.slots 5 (by simp [generationSlots])] using a,
        b.trans (h.slots 6 (by simp [generationSlots])), by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using c⟩
  · intro p s t hs ht r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hs.1.trans ht.1.symm
    · exact hs.2.1.trans ht.2.1.symm
    · exact hs.2.2.trans ht.2.2.symm

def OutputZeroReady (p : OutputPublic) (s : State) : Prop :=
  Lay s p.context.geo.F p.context.geo.hash ∧ ∃ V W,
    Rep s.mem p.context.geo.F p.context.geo.hash V W ∧ W 19 = p.context.saved 6 ∧ W 21 = p.context.saved 7

theorem outputZero_ct : RelCT isa (Two OutputBefore) Impl.Dsa.AArch64.Generation.outputZero
    (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.outputZero zeroOut
  refine RelCT.seq (two_post (Ψ := OutputZeroReady) (two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)) ?_)
    (ct_assoc_left (RelCT.seq (two_post (Ψ := fun (p : OutputPublic) s =>
      s.gpr .x11 = p.context.saved 6 ∧ s.gpr .x12 = p.context.saved 7)
      (two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)) ?_)
      (two_taint [.x11, .x12] ?_ (by taint_decide))))
  · intro p s ⟨W, h, _⟩
    obtain ⟨V, R⟩ := h.rep
    exact WP.mono (zeroArgs_ok h.layout R) fun t ⟨L, R', _, _⟩ =>
      show OutputZeroReady p t from ⟨L, V, _, R', by simpa [upd] using h.slots 6 (by simp [generationSlots]),
        by simpa [upd] using h.slots 7 (by simp [generationSlots])⟩
  · intro p s ⟨L, V, W, R, h19, h21⟩
    have ho : s.mem.readW (p.context.geo.F + BitVec.ofNat 64 sOut) 64 = p.context.saved 6 :=
      (R.fr 19 (by decide)).trans h19
    have hk : s.mem.readW (p.context.geo.F + BitVec.ofNat 64 sK) 64 = p.context.saved 7 :=
      (R.fr 21 (by decide)).trans h21
    brun [exec_ldrSp (off := sOut) (by decide), exec_ldrSp (off := sK) (by decide), L.sp,
      L.ld (d := sOut) (n := 8) (by decide), L.ld (d := sK) (n := 8) (by decide), ho, hk]
  · intro p s t hs ht r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.1.trans ht.1.symm
    · exact hs.2.trans ht.2.symm

theorem output_check {p : OutputPublic} {s : State} (h : OutputBefore p s) :
    WP isa (.block Impl.Dsa.AArch64.Generation.successStatus) s
      (fun t => OutputBefore p t ∧ isa.eval (.zero .x .x3) t = some p.accepted) := by
  obtain ⟨W, hm, hs⟩ := h
  obtain ⟨V, R⟩ := hm.rep
  exact WP.mono (successStatus_ok hm.layout R) fun t ⟨hz, he, hk⟩ =>
    ⟨⟨W, hm.congr he hk, hs⟩, hz.trans (congrArg some hs)⟩

theorem finishOutput_ct : RelCT isa (Two OutputBefore) Impl.Dsa.AArch64.Generation.finishOutput
    (fun _ _ => True) := by
  refine RelCT.seq (two_post (two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide))
    (fun _ _ h => output_check h)) ?_
  refine two_ite (fun _ _ _ hs ht => hs.2.trans ht.2.symm) ?_ ?_
  · exact two_map (fun p : OutputPublic => p) (fun _ _ h => h.1.1) outputCopy_ct
  · exact two_map (fun p : OutputPublic => p) (fun _ _ h => h.1.1) outputZero_ct

end VG.Proof.Dsa.AArch64.Generation
