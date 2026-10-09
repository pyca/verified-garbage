import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowStep
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCallFrame

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase (vr)
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep)

abbrev LowIndex := Fin 2 × Fin 4
def lowRaw0 (i : LowIndex) : VReg := vr (8*i.1.val+2*i.2.val)
def lowRaw1 (i : LowIndex) : VReg := vr (8*i.1.val+2*i.2.val+1)
def lowValue0 (v : Values) (i : LowIndex) : BitVec 128 := (v i.1)[2*i.2.val]
def lowValue1 (v : Values) (i : LowIndex) : BitVec 128 := (v i.1)[2*i.2.val+1]
def lowOff (i : LowIndex) : Nat := 1024*i.1.val+256*i.2.val

def LowPending (s : State) (v : Values) (is : List LowIndex) : Prop :=
  ∀i∈is,s.v (lowRaw0 i)=lowValue0 v i ∧ s.v (lowRaw1 i)=lowValue1 v i

theorem Banks.lowPending {s : State} {v : Values} (h : Banks s v) (is : List LowIndex) : LowPending s v is := by
  intro i hi
  constructor
  · simpa only [bankRegs,Vector.getElem_ofFn,lowRaw0,lowValue0] using h i.1 ⟨2*i.2.val,by omega⟩
  · simpa only [bankRegs,Vector.getElem_ofFn,lowRaw1,lowValue1,Nat.add_assoc] using h i.1 ⟨2*i.2.val+1,by omega⟩

theorem low_raw_keep (i j : LowIndex) (hne : i≠j) :
    lowRaw0 j∉lowPairClobs (lowRaw0 i) (lowRaw1 i) ∧
    lowRaw1 j∉lowPairClobs (lowRaw0 i) (lowRaw1 i) := by
  rcases i with ⟨p,i⟩
  rcases j with ⟨q,j⟩
  revert p i q j
  decide

theorem LowPending.next {s t : State} {v : Values} {i : LowIndex} {is : List LowIndex}
    (h : LowPending s v (i::is)) (hn : i∉is)
    (hf : StepKeep (lowPairClobs (lowRaw0 i) (lowRaw1 i)) s t) : LowPending t v is := by
  intro j hj
  have hne : i≠j := by intro he; exact hn (he ▸ hj)
  have hk := low_raw_keep i j hne
  rw [hf.vec _ hk.1,hf.vec _ hk.2]
  exact h j (List.mem_cons_of_mem _ hj)

end VG.Proof.MlDsa.AArch64.Optimized.Paired
