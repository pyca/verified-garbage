import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MatrixMaskMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourMaskInit
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Blocks

namespace VG.Proof.MlDsa.AArch64.Optimized.MatrixMask
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Call (Ptr lea)
open VG.Proof.MlDsa.AArch64.Optimized.BoundedFour (InitKeep)

abbrev scalar : List Instr := [.movz .x .x8 0 0,.sub .w .x8 .x8 .x0]
def footer (a : Ptr) (N : Nat) : List Instr := lea .x1 a.1 a.2 ++ [.movz .x .x2 (BitVec.ofNat 16 N) 0]
def setup (a : Ptr) (N : Nat) : List Instr := scalar ++ [.vop (.dup .s4 .v0 .x8)] ++ footer a N

def resultMask (s : State) : BitVec 128 :=
  if (s.gpr .x0).setWidth 32=1 then ~~~0#128 else 0#128

theorem scalar_ok (s : State) : WP isa (.block scalar) s fun t =>
    ((t.gpr .x8=((0#32-(s.gpr .x0).setWidth 32).setWidth 64) ∧ t.mem=s.mem) ∧
      Keep [.x8] s t) ∧ t.v=s.v := by
  apply WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold scalar
  arun
  rfl

theorem footer_ok {s : State} {a : Ptr} (ha : a.1∈VG.Proof.MlDsa.AArch64.keptRegs)
    {N : Nat} (hN : N<65536) : WP isa (.block (footer a N)) s fun t =>
    ((t.gpr .x1=pa s a ∧ t.gpr .x2=BitVec.ofNat 64 N ∧ t.mem=s.mem) ∧
      Keep [.x1,.x2,.x9] s t) ∧ t.v=s.v := by
  apply WP.keepV (by
    unfold footer lea
    split
    · rfl
    · unfold Impl.MlDsa.AArch64.Call.movV
      split <;> rfl)
  unfold footer
  have h1 : a.1≠.x1 := by intro h; rw [h] at ha; revert ha; decide
  refine VG.Proof.MlDsa.AArch64.lea_ok h1.symm a.2 fun b hb hp => ?_
  refine wp_movz fun t ht hc => wp_nil ?_
  refine ⟨⟨by rw [ht.get .x1,hp],?_,ht.mem.trans hb.mem⟩,(hb.keep.trans ht.keep).mono (by simp)⟩
  rw [hc]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat]
  omega

theorem setup_ok {s : State} {a : Ptr} (ha : a.1∈VG.Proof.MlDsa.AArch64.keptRegs)
    {N : Nat} (hN : N<65536) (hr : (s.gpr .x0).setWidth 32=0 ∨ (s.gpr .x0).setWidth 32=1) :
    WP isa (.block (setup a N)) s fun t =>
      InitKeep [.x1,.x2,.x8,.x9] [.v0] s t ∧ t.gpr .x1=pa s a ∧
      t.gpr .x2=BitVec.ofNat 64 N ∧ t.v .v0=resultMask s := by
  unfold setup
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (scalar_ok s) fun b ⟨⟨⟨h8,hm⟩,hb⟩,hv⟩ => ?_
  simp only [List.cons_append,List.nil_append]
  refine wp_vop (d := .v0) rfl fun c hc => ?_
  refine WP.mono (footer_ok ha hN) fun t ⟨⟨⟨hp,h2,htm⟩,ht⟩,htv⟩ => ?_
  refine ⟨⟨((hb.trans (hc.keep (by decide))).trans ht).mono (by decide),?_,?_⟩,?_,h2,?_⟩
  · rw [htm,hc.mem,hm]
  · intro r hr
    rw [htv,hc.other r (by simpa using hr),hv]
  · have h8 : a.1∉[Reg.x8] := by
      intro h; rw [List.mem_singleton.mp h] at ha; revert ha; decide
    rw [hp,pa,hc.gpr,hb.get a.1 h8]
  · rw [htv,hc.v,h8]
    unfold resultMask
    rcases hr with h | h <;> rw [h] <;> rfl

end VG.Proof.MlDsa.AArch64.Optimized.MatrixMask
