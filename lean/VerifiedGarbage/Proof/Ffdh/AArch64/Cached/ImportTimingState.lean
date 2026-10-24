module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ImportData
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ImportFrame
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Framework.Omega

/-! Public geometry for importing canonical context limbs into fresh scratch. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure ImportPublic where
 workspace : Ws
 k : Nat
 ctx : Addr
 room : slot workspace.w 8≤workspace.Z
 words : workspace.w=(k+7)/8
 positive : 0<k
 size : k<2^31

structure ImportReady (q : ImportPublic) (s : State) : Prop where
 scratch : Scr s q.workspace.B q.workspace.Z
 base : s.gpr .x0=q.workspace.B
 length : word s.mem q.workspace.B (8*sLen)=BitVec.ofNat 64 q.k
 context : word s.mem q.workspace.B (8*sCtx)=q.ctx
 readable : ∀ i<2*q.workspace.w,InRegions (s.rd++s.wr) (off q.ctx (24+8*i)) 8
 outside : ∀ i<16*q.workspace.w,q.workspace.Z≤ofs q.workspace.B (off q.ctx 24+BitVec.ofNat 64 i)

structure ImportDataReady (q : ImportPublic) (s : State) : Prop where
 good : GoodW q.workspace s
 context : word s.mem q.workspace.B (8*sCtx)=q.ctx
 readable : ∀ i<2*q.workspace.w,InRegions (s.rd++s.wr) (off q.ctx (24+8*i)) 8
 outside : ∀ i<16*q.workspace.w,q.workspace.Z≤ofs q.workspace.B (off q.ctx 24+BitVec.ofNat 64 i)

theorem ImportDataReady.after_arrays {q : ImportPublic} {s t : State} {js : List Nat} {mi : BitVec 64} {rs : List Reg}
 (h : ImportDataReady q s) (good : Good t q.workspace.B q.workspace.Z q.workspace.w mi)
 (frame : Arrays q.workspace.B q.workspace.w js s.mem t.mem) (rest : Keep rs s t) : ImportDataReady q t :=
 ⟨⟨mi,good,q.room⟩,(arrays_header frame (by decide)).trans h.context,
  fun i hi =>by rw [rest.rd,rest.wr];exact h.readable i hi,h.outside⟩

def PrefixCopyReady (q : ImportPublic) (i a : Nat) (s : State) : Prop :=
 ImportDataReady q s ∧ s.gpr .x16=off q.ctx (24+8*q.workspace.w*i) ∧
 s.gpr .x17=off q.workspace.B (slot q.workspace.w a) ∧ s.gpr .x12=BitVec.ofNat 64 q.workspace.w

theorem prefixCopy_ok {q : ImportPublic} {s : State} {a i : Nat}
 (h : PrefixCopyReady q i a s) (array : a<8) (index : i<2) :
 WP isa copyWords s fun t =>ImportDataReady q t ∧ s.gpr .x0=t.gpr .x0 ∧
 t.gpr .x16=off q.ctx (24+8*q.workspace.w*i+8*q.workspace.w) := by
 have mulBound : q.workspace.w*i≤q.workspace.w := by simpa using Nat.mul_le_mul_left q.workspace.w (by omega : i≤1)
 have bytesBound : 8*q.workspace.w*i≤8*q.workspace.w := by simpa using Nat.mul_le_mul_left (8*q.workspace.w) (by omega : i≤1)
 obtain ⟨ready,ptr,dst,count⟩:=h
 obtain ⟨mi,good,_⟩:=ready.good
 refine WP.mono (copyFromContext_ok good q.room (by rw [q.words];have :=q.positive;omega)
  (by rw [q.words];have :=q.size;omega) array ptr dst count
  (fun j hj =>by
   have rd :=ready.readable (q.workspace.w*i+j) (by omega)
   simpa only [Nat.mul_add,Nat.add_assoc,Nat.mul_assoc] using rd)
  (fun j hj =>by
   have out :=ready.outside (8*q.workspace.w*i+j) (by omega)
   simpa only [off,BitVec.ofNat_add,BitVec.add_assoc] using out)) ?_
 rintro t ⟨goodT,_,frame,ptrT,rest⟩
 exact ⟨ready.after_arrays goodT frame rest,(rest.gpr .x0 (by simp [mmRegs])).symm,ptrT⟩

end VG.Proof.Ffdh.AArch64.Cached
