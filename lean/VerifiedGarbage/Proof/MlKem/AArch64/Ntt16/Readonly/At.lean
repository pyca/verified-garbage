module
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.Call
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
public import VerifiedGarbage.TCB.AArch64.Isa
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Ntt16.Readonly
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem.AArch64

theorem TableReady.frame {s t : State} {symbol : String} {H : List Nat} {f w : Addr} {rs : List Region}
 (ht : TableReady s symbol H f w) (hs : t.syms=s.syms) (hr : t.rd=s.rd) (hw : t.wr=s.wr)
 (hf : Frame rs s.mem t.mem) (hd : ∀r∈rs,(Region.mk (s.syms symbol) 512).Disjoint r) :
 TableReady t symbol H f w := by
 refine ⟨?_,by simpa only [hs,hr,hw] using ht.readable,
   by simpa only [hs] using ht.output,by simpa only [hs] using ht.scratch⟩
 intro i hi
 rw [hs,hf.readW (Offset.contains_base _ (by omega) (by omega)) hd (by decide)]
 exact ht.table i hi

end VG.Proof.MlKem.AArch64.Ntt16.Readonly
