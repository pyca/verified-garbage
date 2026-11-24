module

public import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.Tail
public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.GenericStream
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Run
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Tail
open VG VG.WriteBytes

/-- Read both XOR operands from the original memory. The two stores may overlap
inside the destination and assign the same value to every byte in their intersection. -/
theorem ends_mem (m : Mem) (S K D : Addr) {w n : Nat} (lo : w ≤ n) (hi : n ≤ 2*w) (bound : n < 2^64) :
    let atOff := fun (p : Addr) => p + BitVec.ofNat 64 (n-w)
    (m.write D w (m.read S w ^^^ m.read K w)).write (atOff D) w
      (m.read (atOff S) w ^^^ m.read (atOff K) w) =
      writeBytes m D (xorBytes m S K n) := by
  dsimp only
  funext p
  let i := (p-D).toNat
  let j := (p-(D+BitVec.ofNat 64 (n-w))).toNat
  have il : i < 2^64 := (p-D).isLt
  have off : j = (2^64-(n-w)+i) % 2^64 := by
    dsimp only [i,j]
    rw [← BitVec.sub_sub,BitVec.toNat_sub,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (a := n-w) (by omega_using [bound])]
  simp only [Mem.write,writeBytes,length_xorBytes]
  change (if j < w then _ else if i < w then _ else _) = (if i < n then _ else _)
  split
  · rename_i endByte
    have ij : n-w+j=i := by omega_using [off,endByte,il,bound,lo]
    have inside : i<n := by omega_using [ij,lo,endByte]
    rw [ite_eq_left inside, VG.Proof.AesGcm.AArch64.Tail.xorBytes_getD _ _ _ inside,BitVec.extractLsb'_xor,
      Mem.extractLsb'_read _ _ endByte,Mem.extractLsb'_read _ _ endByte]
    simp only [BitVec.add_assoc,← BitVec.ofNat_add,ij]
  · rename_i outside
    split
    · rename_i front
      have inside : i<n := by omega_using [front,lo]
      rw [ite_eq_left inside,VG.Proof.AesGcm.AArch64.Tail.xorBytes_getD _ _ _ inside,BitVec.extractLsb'_xor,
        Mem.extractLsb'_read _ _ front,Mem.extractLsb'_read _ _ front]
    · rename_i past
      rw [ite_eq_right (by omega_using [past,outside,off,hi,lo,bound,il])]

end VG.Proof.AesGcm.AArch64.Contiguous.Tail

namespace VG.Proof.AesGcm.AArch64.Contiguous.Tail
open VG VG.AArch64 VG.AArch64.RegUpd VG.WriteBytes
open VG.Impl.AesGcm.AArch64.Contiguous.Tail
open DirectGather.Generic (SourcePre)
open VG.Impl.AesGcm.AArch64 (imm)

open DirectGather.Generic (TailDone)

theorem wide_ok (wide : Bool) {s : State} {S K D : Addr} {n : Nat}
    (src : s.gpr .x23 = S) (key : s.gpr .x11 = K) (dst : s.gpr .x26 = D) (len : s.gpr .x24 = BitVec.ofNat 64 n)
    (data : SourcePre s S D n) (ks : LoopPre s K D n)
    (lo : (if wide then 8 else 4) ≤ n) (hi : n ≤ 2*(if wide then 8 else 4)) :
    WP isa (.block (wideEnds (if wide then .x else .w) (if wide then 8 else 4))) s (TailDone s S K D n) := by
  let w := if wide then 8 else 4
  have small : n < 2^64 := by have := data.lt; omega
  have readAt (p : Addr) (h : Covers [⟨p,n⟩] (s.rd++s.wr)) :
      InRegions (s.rd++s.wr) p w ∧ InRegions (s.rd++s.wr) (p+BitVec.ofNat 64 (n-w)) w := by
    refine ⟨?_,in_off h (by dsimp [w]; omega) small⟩
    simpa using (in_off (d := 0) h (by dsimp [w]; omega) small : InRegions _ (p+0#64) w)
  obtain ⟨rS,tS⟩ := readAt S data.rd
  obtain ⟨rK,tK⟩ := readAt K ks.rd
  have wD := in_off (d := 0) (n := w) data.wr (by dsimp [w]; omega) small
  have tD := in_off (d := n-w) (n := w) data.wr (by dsimp [w]; omega) small
  rw [BitVec.add_zero] at wD
  have trunc (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by simp
  cases wide <;> simp only [w,Bool.false_eq_true,ite_true,ite_false] at lo hi rS tS rK tK wD tD ⊢
  all_goals
    apply WP.of_runBlock
    refine ⟨_,by arun [wideEnds,src,key,dst,len,BitVec.add_zero,Offset.ofNat_sub_ofNat lo,rS,rK,tS,tK,wD,tD],?_⟩
    refine ⟨?_,?_,?_,rfl,?_,rfl,rfl,rfl⟩
    · simpa only [gpr_write,mem_write,reduceCtorEq,ite_true,ite_false,Size.bits,State.read,
        BitVec.setWidth_eq,trunc,BitVec.add_zero,src,key,dst,len,Offset.ofNat_sub_ofNat lo,
        Mem.readW,Mem.writeW] using ends_mem s.mem S K D lo hi small
    · simp [gpr_write]
    · simp [gpr_write]
    · intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

private theorem scratch_done {s t : State} {S K D : Addr} {n : Nat} {v : Addr}
    (h : TailDone (s.write .x .x12 v) S K D n t) : TailDone s S K D n t := by
  refine { h with gpr := fun r hr => (h.gpr r hr).trans (gpr_write_of_ne _ _ _ ?_) }
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

private theorem shiftCount {s : State} {n k : Nat} (h : s.gpr .x24 = BitVec.ofNat 64 n) (hn : n < 2^64) :
    (s.write .x .x12 (s.gpr .x24 >>> k)).gpr .x12 = BitVec.ofNat 64 (n / 2^k) := by
  simp only [gpr_write_self,Size.bits,BitVec.setWidth_eq,h]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn,Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self ..) hn)]

theorem words_ok {s : State} {S K D : Addr} {n : Nat}
    (src : s.gpr .x23 = S) (key : s.gpr .x11 = K) (dst : s.gpr .x26 = D) (len : s.gpr .x24 = BitVec.ofNat 64 n)
    (count : s.gpr .x10 = BitVec.ofNat 64 n) (data : SourcePre s S D n) (ks : LoopPre s K D n) (hn : n < 16) :
    WP isa wordTail s (TailDone s S K D n) := by
  let u := s.write .x .x12 (s.gpr .x24 >>> 3)
  have sw := shiftCount (k := 3) len (by omega)
  refine WP.seq (WP.of_runBlock ⟨u,rfl,?_⟩)
  refine WP.ite (decide (n/8 ≠ 0)) (eval_nonzero sw (by omega)) (fun e => ?_) (fun _ => ?_)
  · have h := of_decide_eq_true e
    exact (wide_ok true (s := u) src key dst len ⟨data.lt,data.rd,data.wr,data.layout⟩ ⟨ks.lt,ks.rd,ks.wr,ks.disj⟩ (by dsimp; omega) (by dsimp; omega)).mono
      fun _ q => scratch_done q
  · let a := u.write .x .x12 (u.gpr .x24 >>> 2)
    have v := shiftCount (s := u) (k := 2) len (by omega)
    refine WP.seq (WP.of_runBlock ⟨a,rfl,?_⟩)
    refine WP.ite (decide (n/4 ≠ 0)) (eval_nonzero v (by omega)) (fun f => ?_) (fun _ => ?_)
    · have h := of_decide_eq_true f
      have lt : n < 8 := by simp_all
      exact (wide_ok false (s := a) src key dst len ⟨data.lt,data.rd,data.wr,data.layout⟩ ⟨ks.lt,ks.rd,ks.wr,ks.disj⟩ (by dsimp; omega) (by dsimp; omega)).mono
        fun _ q => scratch_done (scratch_done q)
    · exact (DirectGather.Generic.byteTail_law (s := a) src key dst len count ⟨data.lt,data.rd,data.wr,data.layout⟩ ⟨ks.lt,ks.rd,ks.wr,ks.disj⟩ hn).mono fun _ q =>
        scratch_done (scratch_done q)

end VG.Proof.AesGcm.AArch64.Contiguous.Tail
