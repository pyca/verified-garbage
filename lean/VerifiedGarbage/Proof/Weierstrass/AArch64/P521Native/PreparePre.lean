module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.PrepareArgs
import VerifiedGarbage.Proof.Framework.Offset

/-! Prefix input regions permit the public table's active stack frames. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Ecdsa.AArch64
open VG.Impl.Weierstrass.AArch64.P521Native (config outerBlock001)
open VG.Proof.Ed25519.AArch64 (Keeps)

/-- Region membership rather than an exact region list: the native function
has already opened two stack frames when its argument preparation runs. -/
structure PrepareApiPre (s : State) : Prop where
  privateRegion : (⟨s.gpr .x1,66⟩ : Region)∈s.rd++s.wr
  peer : (⟨s.gpr .x2,133⟩ : Region)∈s.rd++s.wr
  scratch : (⟨s.gpr .x3,8192⟩ : Region)∈s.wr
  private_apart : Region.Disjoint ⟨s.gpr .x1,66⟩ ⟨s.gpr .x3,8192⟩
  peer_apart : Region.Disjoint ⟨s.gpr .x2,133⟩ ⟨s.gpr .x3,8192⟩
  scratch_fit : (s.gpr .x3).toNat+8192≤2^64

theorem prepare_api_args_ok {s : State} (pre : PrepareApiPre s) :
    WP isa (.block (outerBlock001.take 5)) s fun t =>
      SetupPre config t ∧ t.gpr .x26=s.sp ∧ t.gpr .x4=s.gpr .x3 ∧ t.gpr .x6=s.gpr .x2 ∧
      t.gpr .x3=s.gpr .x1 ∧ t.gpr .x2=s.gpr .x2+BitVec.ofNat 64 1 ∧
      Keeps [.x2,.x3,.x4,.x6,.x26] s t := by
  refine WP.mono (prepare_args_ok s) fun t ⟨table,workspace,peer,secretArg,peerPlus,keep,_⟩ => ?_
  have len : config.C.len=66 := rfl
  have oldPrivate : t.gpr .x1=s.gpr .x1 := keep.gpr .x1 (by decide)
  have regions : t.rd++t.wr=s.rd++s.wr := by rw [keep.rd,keep.wr]
  refine ⟨?_,table,workspace,peer,secretArg,peerPlus,keep⟩
  constructor
  · rw [workspace,keep.wr]
    exact pre.scratch
  · intro e he
    rw [secretArg,regions]
    exact ⟨_,pre.privateRegion,Offset.contains_base _ (by rw [len] at he; exact he) (by rw [len] at he; omega_arith)⟩
  · intro e he
    rw [oldPrivate,regions]
    exact ⟨_,pre.privateRegion,Offset.contains_base _ (by rw [len] at he; exact he) (by rw [len] at he; omega_arith)⟩
  · intro e he
    rw [peerPlus,regions,BitVec.add_assoc,BitVec.ofNat_add_ofNat]
    exact ⟨_,pre.peer,Offset.contains_base _ (by rw [len] at he; omega_arith) (by rw [len] at he; omega_arith)⟩
  · rw [oldPrivate,workspace,len]
    exact pre.private_apart
  · rw [peerPlus,workspace,len]
    exact pre.peer_apart.sub_left (Offset.sub_base _ (by decide))
  · rw [secretArg,workspace,len]
    exact pre.private_apart
  · rw [workspace]
    exact pre.scratch_fit

end VG.Proof.Weierstrass.AArch64.P521Native
