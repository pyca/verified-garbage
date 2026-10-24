module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SelectRow
public import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! Read-only packed table geometry and the two public header cells used by the scan. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure SelectEnv (B table dst : Addr) (w : Nat) (s : State) : Prop where
 base : s.gpr .x0=B
 destination : word s.mem B (8*sArr 5)=dst
 width : word s.mem B (8*sW)=BitVec.ofNat 64 w
 readDestinationHeader : InRegions (s.rd++s.wr) (off B (8*sArr 5)) 8
 readWidthHeader : InRegions (s.rd++s.wr) (off B (8*sW)) 8
 readSource : ∀ j<32, ∀ i<w, InRegions (s.rd++s.wr) (off table (8*w*j+8*i)) 8
 readOutput : ∀ i<w, InRegions (s.rd++s.wr) (off dst (8*i)) 8
 writeOutput : ∀ i<w, InRegions s.wr (off dst (8*i)) 8
 separate : ∀ j<32, ∀ i<w, ∀ b<8, 8*w≤ofs dst (off table (8*w*j+8*i)+BitVec.ofNat 64 b)
 separateDestinationHeader : ∀ b<8, 8*w≤ofs dst (off B (8*sArr 5)+BitVec.ofNat 64 b)
 separateWidthHeader : ∀ b<8, 8*w≤ofs dst (off B (8*sW)+BitVec.ofNat 64 b)

theorem SelectEnv.after_frame {B table dst : Addr} {w : Nat} {s t : State} {rs : List Reg}
 (h : SelectEnv B table dst w s) (frame : Outside dst 0 (8*w) s.mem t.mem)
 (rest : Keep rs s t) (base : t.gpr .x0=B) : SelectEnv B table dst w t := by
 refine ⟨base,?_,?_,?_,?_,?_,?_,?_,h.separate,h.separateDestinationHeader,h.separateWidthHeader⟩
 · have same : word t.mem B (8*sArr 5)=word s.mem B (8*sArr 5) :=
    Mem.readW_congr fun b hb => frame (off B (8*sArr 5)+BitVec.ofNat 64 b)
     (Or.inr (by simpa only [Nat.zero_add] using h.separateDestinationHeader b hb))
   exact same.trans h.destination
 · have same : word t.mem B (8*sW)=word s.mem B (8*sW) :=
    Mem.readW_congr fun b hb => frame (off B (8*sW)+BitVec.ofNat 64 b)
     (Or.inr (by simpa only [Nat.zero_add] using h.separateWidthHeader b hb))
   exact same.trans h.width
 · rw [rest.rd,rest.wr];exact h.readDestinationHeader
 · rw [rest.rd,rest.wr];exact h.readWidthHeader
 · intro j hj i hi;rw [rest.rd,rest.wr];exact h.readSource j hj i hi
 · intro i hi;rw [rest.rd,rest.wr];exact h.readOutput i hi
 · intro i hi;rw [rest.wr];exact h.writeOutput i hi

theorem SelectEnv.source_word {B table dst : Addr} {w : Nat} {s t : State}
 (h : SelectEnv B table dst w s) (frame : Outside dst 0 (8*w) s.mem t.mem) {j i : Nat}
 (hj : j<32) (hi : i<w) : word t.mem table (8*w*j+8*i)=word s.mem table (8*w*j+8*i) :=
 Mem.readW_congr fun b hb => frame _ (Or.inr (by simpa only [Nat.zero_add] using h.separate j hj i hi b hb))

private theorem exec_cselc_x (s : State) (d n m : Reg) (cond : CondCode) :
 exec (.cselc .x d n m cond) s =
 some (s.write .x d (if cond.holds s then s.gpr n else s.gpr m)) := rfl

private theorem zeroFlag (s : State) (d : Reg) (a b : BitVec 64) (c : Bool) :
 (s.addWithCarry .x d a b c).zf=decide (a+b+BitVec.ofNat 64 c.toNat=0#64) := rfl

private theorem matching_mask : ∀ v<32, ∀ j<32,
 (if decide ((BitVec.ofNat 64 v ^^^ BitVec.ofNat 64 j) + ~~~0#64 + 1#64 = 0#64) then 0#64-1#64 else 0#64) =
 (if v=j then BitVec.allOnes 64 else 0#64) := by
 decide +kernel

theorem selectHead_ok {s : State} {B table dst : Addr} {w v j : Nat}
 (env : SelectEnv B table dst w s) (hv : v<32) (hj : j<32)
 (digit : s.gpr .x10=BitVec.ofNat 64 v) (candidate : s.gpr .x11=BitVec.ofNat 64 j) :
 WP isa (.block VG.Impl.Ffdh.AArch64.Cached.Comb.selectHead) s fun t =>
 (t.gpr .x8=dst ∧ t.gpr .x12=BitVec.ofNat 64 w ∧
 t.gpr .x6=(if v=j then BitVec.allOnes 64 else 0#64) ∧ t.mem=s.mem) ∧
 Keep [.x3,.x6,.x7,.x8,.x12] s t := by
 unfold VG.Impl.Ffdh.AArch64.Cached.Comb.selectHead
 refine WP.keep [.x3,.x6,.x7,.x8,.x12] ?_ rfl rfl rfl
 brun [env.base,hdr_enc (show sArr 5<32 by decide),hdr_enc (show sW<32 by decide),
 env.readDestinationHeader,env.readWidthHeader,env.destination,env.width,digit,candidate,exec_cselc_x,CondCode.holds,RegUpd.zf_write,zeroFlag,Bool.toNat_true]
 exact matching_mask v hv j hj

end VG.Proof.Ffdh.AArch64.Cached
