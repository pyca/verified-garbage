import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedReturn
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCheckModel

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Paired
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.MlDsa.AArch64.Optimized.Response (finishValue hintFinishValue)

def dataReturn (kind : Kind) (d : CheckData) : BitVec 64 :=
  if kind==.h then hintFinishValue d.count d.flags else finishValue d.flags

theorem returnValue_data (kind : Kind) (s : State) : returnValue kind s=dataReturn kind (dataAt s) := rfl

/-- The response loop's writes are framed away from saved registers. Restoring
those registers closes the ABI independently of the loop's vector clobbers. -/
theorem loop_finish_ok (kind : Kind) {s₀ s : State} {work : Addr}
    {gr gs : List Reg} {vr vs : List VReg} {body : Prog isa} {d : CheckData} {writes : List Region}
    (hf : CallFrame gr vr s₀ s) (hs : Saved s.mem work s₀.v)
    (hd : ∀r∈writes,(⟨work+BitVec.ofNat 64 2048,128⟩:Region).Disjoint r)
    (hr : ∀p∈extraSlots 1920,InRegions (s.rd++s.wr)
      ((work+BitVec.ofNat 64 128)+BitVec.ofNat 64 p.2) 16)
    (hb : WP isa body s fun u => CallFrame gs vs s u ∧ u.gpr .x2=work+BitVec.ofNat 64 128 ∧
      dataAt u=d ∧ Frame writes s.mem u.mem) :
    WP isa (.seq body (.block (finish kind))) s fun t =>
      Keep ((gr++gs)++([.x0,.x9,.x10] : List Reg)) s₀ t ∧
      t.mem=d.mem ∧ t.gpr .x0=dataReturn kind d := by
  refine WP.seq (WP.mono hb fun u ⟨hu,hx,hdata,hm⟩ => ?_)
  have hs' : Saved u.mem work s₀.v := hs.frame hm hd
  have hr' : ∀p∈extraSlots 1920,InRegions (u.rd++u.wr) (u.gpr .x2+BitVec.ofNat 64 p.2) 16 := by
    intro p hp
    rw [hu.rd,hu.wr,hx]
    exact hr p hp
  refine WP.mono (finish_saved_ok kind (hf.trans hu) hx hs' hr') fun t ⟨ht,htm,htv⟩ => ?_
  refine ⟨ht,htm.trans (congrArg CheckData.mem hdata),?_⟩
  rw [htv,returnValue_data,hdata]

end VG.Proof.MlDsa.AArch64.Optimized.Paired
