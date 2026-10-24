module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SelectEnv
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! One of exactly 32 table rows, preserving the context and public cursor. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem off_off (B : Addr) (a b : Nat) : off (off B a) b=off B (a+b) := by
 simp only [off,BitVec.add_assoc,BitVec.ofNat_add]

private theorem next_ok (s : State) {j : Nat} (candidate : s.gpr .x11=BitVec.ofNat 64 j) :
 WP isa (.block [.addImm .x .x11 .x11 1,.subImm .x .x3 .x11 32]) s fun t =>
 (t.gpr .x11=BitVec.ofNat 64 (j+1) ∧ t.gpr .x3=BitVec.ofNat 64 (j+1)-32#64 ∧ t.mem=s.mem) ∧
 Keep [.x3,.x11] s t := by
 refine WP.keep [.x3,.x11] ?_ rfl rfl rfl
 brun [candidate,←BitVec.ofNat_add]

def selectClobbers : List Reg := [.x3,.x4,.x6,.x7,.x8,.x9,.x11,.x12]

theorem selectStep_ok {s : State} {B table dst : Addr} {w v j : Nat}
 (env : SelectEnv B table dst w s) (positive : 0<w) (fit : 8*w≤2^64)
 (hv : v<32) (hj : j<32)
 (digit : s.gpr .x10=BitVec.ofNat 64 v) (candidate : s.gpr .x11=BitVec.ofNat 64 j)
 (pointer : s.gpr .x9=off table (8*w*j)) :
 WP isa VG.Impl.Ffdh.AArch64.Cached.Comb.selectStep s fun t =>
 SelectEnv B table dst w t ∧
 (∀ i<w, word t.mem dst (8*i)=word s.mem dst (8*i) |||
  (word s.mem table (8*w*j+8*i) &&& (if v=j then BitVec.allOnes 64 else 0#64))) ∧
 Outside dst 0 (8*w) s.mem t.mem ∧
 t.gpr .x9=off table (8*w*(j+1)) ∧ t.gpr .x10=BitVec.ofNat 64 v ∧
 t.gpr .x11=BitVec.ofNat 64 (j+1) ∧ t.gpr .x3=BitVec.ofNat 64 (j+1)-32#64 ∧
 Keep selectClobbers s t := by
 unfold VG.Impl.Ffdh.AArch64.Cached.Comb.selectStep
 rw [WP.seq_iff]
 refine WP.mono (selectHead_ok env hv hj digit candidate) ?_
 rintro u ⟨⟨dstU,countU,maskU,memU⟩,restU⟩
 rw [WP.seq_iff]
 refine WP.mono (selectRow_ok u positive fit ((restU.gpr .x9 (by decide)).trans pointer)
  dstU maskU countU ?_ ?_ ?_ ?_) ?_
 · intro i hi
   rw [off_off,restU.rd,restU.wr]
   exact env.readSource j hj i hi
 · intro i hi;rw [restU.rd,restU.wr];exact env.readOutput i hi
 · intro i hi;rw [restU.wr];exact env.writeOutput i hi
 · intro i hi b hb
   rw [off_off]
   exact env.separate j hj i hi b hb
 · rintro z ⟨words,frame,srcZ,_,restZ⟩
   refine WP.mono (next_ok z ((restZ.gpr .x11 (by decide)).trans
    ((restU.gpr .x11 (by decide)).trans candidate))) ?_
   rintro t ⟨⟨next,counter,memT⟩,restT⟩
   have keep : Keep selectClobbers s t := ((restU.trans restZ).trans restT).mono (by decide)
   have totalFrame : Outside dst 0 (8*w) s.mem t.mem := by rw [memT,←memU];exact frame
   refine ⟨env.after_frame totalFrame keep ((keep.gpr .x0 (by simp [selectClobbers])).trans env.base),
    ?_,totalFrame,?_,(keep.gpr .x10 (by simp [selectClobbers])).trans digit,next,counter,keep⟩
   · intro i hi
     rw [memT,words i hi,memU]
     simp only [word,off_off]
   · rw [restT.gpr .x9 (by decide),srcZ,off_off]
     congr 1

end VG.Proof.Ffdh.AArch64.Cached
