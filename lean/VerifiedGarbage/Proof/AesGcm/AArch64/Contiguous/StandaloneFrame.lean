module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.StandalonePowers
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.LeafContract
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.PreparedVectors
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.Calls
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.LeafCT
import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! The public standalone entry needs two stack arguments. Both buffer layouts
share its allocation, ABI preservation, timing and residue proofs. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Standalone
open VG VG.AArch64 VG.Impl.AesGcm.AArch64 VG.Impl.StackScratch.AArch64
open VG.Impl.AesGcm.AArch64.Contiguous.Standalone
open DirectGather (genBase)

abbrev frame (v : Calls) := withStackArgScratch (v.pwWn+32) 2 (body v)
abbrev BodyOk (v : GcmImpl) := ∀ {s W P}, Inner v.calls.pwWn W s →
  BatchPowers v.calls.pwWn (s.gpr .x0) W P s →
  WP isa (body v.calls) s fun t => GprAbi s t ∧ result s t
abbrev BodyRel (v : GcmImpl) := ∀ {a b W P}, Inner v.calls.pwWn W a → Inner v.calls.pwWn W b →
  BatchPowers v.calls.pwWn (a.gpr .x0) W P a → BatchPowers v.calls.pwWn (b.gpr .x0) W P b →
  onePub 2 a b → RelCT isa (Eq2 a b) (body v.calls) TT
abbrev FrameVectors (v : Calls) := ∀ {s t : State} {tr : List Leak}, Exec isa (frame v) s tr t →
  ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

theorem frame_ok (v : GcmImpl) {o : State} (c : Caller o) (pow : Prepared.Powers o) (run : BodyOk v)
    (sz : 768 ≤ v.calls.pwWn ∧ v.calls.pwWn ≤ 2560 ∧ v.calls.pwWn%16=0)
    (vectors : FrameVectors v.calls) : WP isa (frame v.calls) o fun t => abiPreserved o t ∧ result o t := by
  suffices raw : WP isa (frame v.calls) o (fun t => GprAbi o t ∧ result o t) by
    obtain ⟨tr,t,ex,⟨hg,hs⟩,post⟩ := raw
    exact ⟨tr,t,ex,⟨hg,hs,vectors ex⟩,post⟩
  obtain ⟨first,e⟩ := pushed c sz.2.1 sz.2.2
  have en := inner c e sz.1
  apply WP.alloc ⟨by omega,by omega,by omega⟩ (by have := c.room; omega)
  refine WP.seq ⟨_,_,Exec.block first,?_⟩
  refine (run en (originalPowers c pow e sz.2.2)).mono ?_
  intro z ⟨abi,post⟩ m u fr
  have hold : ∀ r ∈ preserved, r ≠ .x16 ∧ r ≠ .x17 := by decide
  exact ⟨⟨fun r hr => (abi.1 r hr).trans (e.regs r (hold r hr).1 (hold r hr).2),
    by change z.sp+BitVec.ofNat 64 (v.calls.pwWn+32) = o.sp
       rw [abi.2,e.sp,genBase,BitVec.sub_add_cancel]⟩,
    result_frame c (by omega) (entryResult e c post) fr⟩


theorem frame_rel (v : GcmImpl) {a b : State} (ca : Caller a) (cb : Caller b)
    (pa : Prepared.Powers a) (pb : Prepared.Powers b) (run : BodyRel v)
    (sz : 768 ≤ v.calls.pwWn ∧ v.calls.pwWn ≤ 2560 ∧ v.calls.pwWn%16=0) (pub : onePub 3 a b) :
    RelCT isa (Eq2 a b) (frame v.calls) TT := by
  let wn := v.calls.pwWn
  let u := setArgsState (wn+32) 2 (allocated (wn+32) a)
  let z := setArgsState (wn+32) 2 (allocated (wn+32) b)
  obtain ⟨ra,e⟩ := pushed ca sz.2.1 sz.2.2
  obtain ⟨rb,f⟩ := pushed cb sz.2.1 sz.2.2
  obtain ⟨q0,q1,q2,q3,q4,q5,q6,q7,sp,stk⟩ := pub
  have base : DirectGather.genWork a wn = DirectGather.genWork b wn := by simp only [DirectGather.genWork,DirectGather.genBase,sp]
  have sp' : u.sp = z.sp := by rw [e.sp,f.sp,DirectGather.genBase,DirectGather.genBase,sp]
  have eq (r : Reg) (h16 : r ≠ .x16) (h17 : r ≠ .x17) (h : a.gpr r = b.gpr r) : u.gpr r = z.gpr r :=
    (e.regs _ h16 h17).trans (h.trans (f.regs _ h16 h17).symm)
  have pub' : onePub 2 u z :=
    ⟨eq _ (by decide) (by decide) q0,eq _ (by decide) (by decide) q1,eq _ (by decide) (by decide) q2,
      eq _ (by decide) (by decide) q3,eq _ (by decide) (by decide) q4,eq _ (by decide) (by decide) q5,
      eq _ (by decide) (by decide) q6,eq _ (by decide) (by decide) q7,sp',
      fun i hi => (e.args i hi).trans ((stk i (by omega)).trans (f.args i hi).symm)⟩
  apply RelCT.alloc (P := Eq2 a b) (R := TT)
  apply RelCT.seq (R := Eq2 u z)
  · rintro x y tx ty x' y' ⟨_,_,⟨rfl,rfl⟩,rfl,rfl⟩ ex ey
    obtain ⟨rfl,rfl⟩ := Exec.det ex (.block ra)
    obtain ⟨rfl,rfl⟩ := Exec.det ey (.block rb)
    exact ⟨by simp only [allocated,sp],rfl,rfl⟩
  · have p := inner ca e sz.1
    have q := inner cb f sz.1
    have left := originalPowers ca pa e sz.2.2
    have right := originalPowers cb pb f sz.2.2
    rw [←stk 2 (by decide)] at right
    exact run p (base ▸ q) left (base ▸ right) pub'

theorem standaloneLeaf (v : GcmImpl) (run : BodyOk v) (rel : BodyRel v)
    (sz : 768 ≤ v.calls.pwWn ∧ v.calls.pwWn ≤ 2560 ∧ v.calls.pwWn%16=0)
    (check : (withStackArgScratch (v.calls.pwWn+32) 2 (bodyWith v.calls false)).allInstrs keepsV = true)
    (side : VG.AArch64.Scrub.scrubSide (frame v.calls) (v.calls.pwWn+32) 0 (clear v.calls) [] = true)
    (sat : ∃ s, (leafContract (fun _ => True)).pre s) :
    VerifiedScrubbed target (prog v.calls) (leafContract (fun _ => True)) 0 := by
  apply scrubLeaf (by omega) side
  exact ⟨fun _ h => frame_ok v h.1 h.2.1 run sz (frameVectors v.calls check),ct_of (fun _ _ pa pb pub => frame_rel v pa.1 pb.1 pa.2.1 pb.2.1 rel sz pub.1),sat⟩

end VG.Proof.AesGcm.AArch64.Contiguous.Standalone
