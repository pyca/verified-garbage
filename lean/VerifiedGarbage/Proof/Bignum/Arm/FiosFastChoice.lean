module

public import VerifiedGarbage.Impl.Bignum.Arm.FiosFast
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Selection changes only flags and compares the public packed-word count. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.FiosFast
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_cmp op2_imm)

def Post (s : State) (base : BitVec 32) (acc b mod n : Nat) (t : State) : Prop :=
  (∃ q<2^32, 2^32*val32 t.mem (State.addr base) acc (n+1)=
    val32 s.mem (State.addr base) acc (n+2)+
    (s.gpr .r1).toNat*val32 s.mem (State.addr base) b n+
    q*val32 s.mem (State.addr base) mod n) ∧
  t.gpr .r0=base+BitVec.ofNat 32 (acc+4*(n+1)) ∧
  Outside (State.addr base) acc (4*(n+1)) s.mem t.mem ∧
  Rest roundClobbers s t

theorem Post.prefix {s u t : State} {base : BitVec 32} {acc b mod n : Nat}
    (h : Post u base acc b mod n t) (mem : u.mem=s.mem) (rest : Rest [] s u) :
    Post s base acc b mod n t := by
  obtain ⟨value,ptr,outside,rt⟩ := h
  refine ⟨?_,ptr,?_,(rest.mono (by simp)).trans rt⟩
  · simpa only [mem,rest.gpr .r1 (by simp)] using value
  · simpa only [mem] using outside

theorem choose_ok (s : State) (n k : Nat) (hn : n<2^32) (hk : k<2^32)
    (enc : encodable (BitVec.ofNat 32 k)=true) (count : s.gpr .lr=BitVec.ofNat 32 n) :
    WP isa (.block (VG.Impl.Bignum.Arm.FiosFast.choose (BitVec.ofNat 32 k))) s fun t =>
      t.z=decide (n=k) ∧ t.mem=s.mem ∧ Rest [] s t := by
  unfold VG.Impl.Bignum.Arm.FiosFast.choose
  refine wp_cmp (op2_imm enc) fun t ht zero => WP.block_nil ?_
  refine ⟨?_,ht.mem,ht.rest []⟩
  rw [zero,count]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq,decide_eq_true_eq]
  constructor
  · intro eq
    have same : BitVec.ofNat 32 n=BitVec.ofNat 32 k := by
      calc
        _ = (BitVec.ofNat 32 n-BitVec.ofNat 32 k)+BitVec.ofNat 32 k := (BitVec.sub_add_cancel _ _).symm
        _ = _ := by
          rw [eq]
          change 0#32+BitVec.ofNat 32 k=BitVec.ofNat 32 k
          exact BitVec.zero_add _
    have e := congrArg BitVec.toNat same
    simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn,Nat.mod_eq_of_lt hk] using e
  · intro eq
    rw [eq,BitVec.sub_self]
    rfl

end VG.Proof.Bignum.Arm.FiosFast
