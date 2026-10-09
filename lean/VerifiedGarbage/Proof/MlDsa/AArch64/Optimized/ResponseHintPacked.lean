import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintFlags

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64

theorem packedWords_nat (lo hi : BitVec 32) :
    (lo.setWidth 64 ||| (hi.setWidth 64 <<< 32)).toNat=lo.toNat+hi.toNat*4294967296 := by
  rw [BitVec.or_comm,←BitVec.setWidth_append_eq_shiftLeft_setWidth_or,BitVec.setWidth_eq,
    BitVec.toNat_append,←Nat.shiftLeft_add_eq_or_of_lt lo.isLt,Nat.shiftLeft_eq]
  omega

def hintFailure (m : Mem) (B : BitVec 32) (p a h : Addr) (j : Nat) : Bool :=
  hintLaneFailure m B p a h 0 j || hintLaneFailure m B p a h 1 j ||
    hintLaneFailure m B p a h 2 j || hintLaneFailure m B p a h 3 j

def hintCount (m : Mem) (B : BitVec 32) (p a h : Addr) (j : Nat) : Nat :=
  hintLaneCount m B p a h 0 j+hintLaneCount m B p a h 1 j+
    hintLaneCount m B p a h 2 j+hintLaneCount m B p a h 3 j

theorem hintRun_packed_value (m : Mem) (B : BitVec 32) (p a h : Addr) {j : Nat} (hj : j≤64) :
    (hintFinishValue (hintRun m B p a h j).counts (hintRun m B p a h j).flags).toNat=
      hintCount m B p a h j+(if hintFailure m B p a h j then 0 else 4294967296) := by
  have h0 := hintRun_count_bound m B p a h hj (e:=0) (by decide)
  have h1 := hintRun_count_bound m B p a h hj (e:=1) (by decide)
  have h2 := hintRun_count_bound m B p a h hj (e:=2) (by decide)
  have h3 := hintRun_count_bound m B p a h hj (e:=3) (by decide)
  have hsum : (vword (hintRun m B p a h j).counts 0+vword (hintRun m B p a h j).counts 1+
      vword (hintRun m B p a h j).counts 2+vword (hintRun m B p a h j).counts 3).toNat=
      hintCount m B p a h j := by
    simp only [BitVec.toNat_add]
    rw [Nat.mod_eq_of_lt (by change _<4294967296; omega),
      Nat.mod_eq_of_lt (by change _<4294967296; omega),
      Nat.mod_eq_of_lt (by change _<4294967296; omega)]
    rw [hintRun_count_value _ _ _ _ _ hj (by decide),hintRun_count_value _ _ _ _ _ hj (by decide),
      hintRun_count_value _ _ _ _ _ hj (by decide),hintRun_count_value _ _ _ _ _ hj (by decide)]
    rfl
  unfold hintFinishValue
  rw [hintRun_finish_flag]
  change (_ ||| ((if hintFailure m B p a h j then (0:BitVec 64) else 1) <<< 32)).toNat=_
  cases hf : hintFailure m B p a h j
  · change (_ ||| ((1#32).setWidth 64 <<< 32)).toNat=hintCount m B p a h j+4294967296
    rw [packedWords_nat,hsum]
    rfl
  · change (_ ||| ((0#32).setWidth 64 <<< 32)).toNat=hintCount m B p a h j+0
    rw [packedWords_nat,hsum]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.Response
