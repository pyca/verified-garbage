module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

structure ZeroReady (L : List Zq) (slot : Nat) (aP : Addr) (s : State) : Prop where
  len : L.length≤256
  coeffs : Rej8.Scalar.Coeffs s.mem aP L
  saved : checkpoint (s.gpr .x19+BitVec.ofNat 64 slot) aP L s.mem
  read0 : InRegions (s.rd++s.wr) (s.gpr .x19+BitVec.ofNat 64 slot) 8
  read1 : InRegions (s.rd++s.wr) (s.gpr .x19+BitVec.ofNat 64 (slot+8)) 8
  writable : ∀i<256,InRegions s.wr (coeffAddr aP i) 4

theorem zeroExtra_relCT {s u : State} {slot : Nat} (ho : slot+8<32768) (ha : slot%8=0)
    {L : List Zq} {aP : Addr} (ps : ZeroReady L slot aP s) (pu : ZeroReady L slot aP u)
    (hsp : s.sp=u.sp) (h19 : s.gpr .x19=u.gpr .x19) :
    RelCT isa (fun a b=>a=s ∧ b=u) (Impl.MlKem.AArch64.Paired.zeroExtra slot)
      (fun a b=>s.sp=a.sp ∧ u.sp=b.sp) := by
  have start : RelCT isa (fun a b=>a=s ∧ b=u)
      (.block [.ldr .x .x3 .x19 slot,.ldr .x .x4 .x19 (slot+8)])
      (VG.AArch64.Taint.Agree (Taint.ofRegs [.x3,.x4])) := by
    intro a b tr ur a' b' h ea eb
    rcases h with ⟨ha',hb'⟩
    subst a; subst b
    obtain ⟨ka,_,a3,a4⟩ := exec_post (load_checkpoint s ho ha ps.read0 ps.read1) ea
    obtain ⟨kb,_,b3,b4⟩ := exec_post (load_checkpoint u ho ha pu.read0 pu.read1) eb
    refine ⟨loadCheckpoint_ct slot s u tr ur a' b' trivial trivial
      (agree_of hsp (by intro r hr; rw [List.mem_singleton.mp hr]; exact h19)) ea eb,
      agree_of (ka.sp.trans (hsp.trans kb.sp.symm)) ?_⟩
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact (a3.trans ps.saved.1).trans (b3.trans pu.saved.1).symm
    · apply BitVec.eq_of_toNat_eq
      rw [a4,b4]
      have es : s.gpr .x19+BitVec.ofNat 64 (slot+8)=s.gpr .x19+BitVec.ofNat 64 slot+8 := by
        rw [BitVec.ofNat_add,BitVec.add_assoc]; rfl
      have eu : u.gpr .x19+BitVec.ofNat 64 (slot+8)=u.gpr .x19+BitVec.ofNat 64 slot+8 := by
        rw [BitVec.ofNat_add,BitVec.add_assoc]; rfl
      rw [es,eu,ps.saved.2,pu.saved.2]
  have trace : RelCT isa (fun a b=>a=s ∧ b=u) (Impl.MlKem.AArch64.Paired.zeroExtra slot)
      (fun _ _=>True) := by
    refine RelCT.seq start ?_
    intro a b tr ur a' b' h ea eb
    exact ⟨zeroSuffix_ct a b tr ur a' b' trivial trivial h ea eb,trivial⟩
  intro a b tr ur a' b' h ea eb
  rcases h with ⟨ha',hb'⟩
  subst a; subst b
  have hs := exec_post (zeroExtra_ok s ho ha ps.len ps.coeffs ps.saved ps.read0 ps.read1 ps.writable) ea
  have hu := exec_post (zeroExtra_ok u ho ha pu.len pu.coeffs pu.saved pu.read0 pu.read1 pu.writable) eb
  exact ⟨(trace s u tr ur a' b' ⟨rfl,rfl⟩ ea eb).1,hs.1.sp.symm,hu.1.sp.symm⟩

end VG.Proof.MlKem.AArch64.Paired
