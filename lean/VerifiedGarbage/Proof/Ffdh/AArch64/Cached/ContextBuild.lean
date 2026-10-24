module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PowerState
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.EntryPointer
import VerifiedGarbage.Proof.Framework.Omega

/-! Writable canonical context geometry and the initialized table prefix. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure ContextSpace (p : Parameters) (s : State) : Prop where
 writable : ∀ i<3+34*p.w,InRegions s.wr (off p.ctx (8*i)) 8
 outside : ∀ i<8*(3+34*p.w),p.Z≤ofs p.B (p.ctx+BitVec.ofNat 64 i)

theorem ContextSpace.after {p : Parameters} {s t : State} {rs : List Reg}
 (h : ContextSpace p s) (rest : Keep rs s t) : ContextSpace p t :=
 ⟨fun i hi => by rw [rest.wr];exact h.writable i hi,h.outside⟩

theorem entry_index (w j i : Nat) : entryOffset w j+8*i=8*(3+(2+j)*w+i) := by
 unfold entryOffset
 simp only [Nat.mul_add,Nat.add_mul,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] <;>omega

theorem ContextSpace.entry_write {p : Parameters} {s : State} (h : ContextSpace p s)
 {j i : Nat} (hj : j<32) (hi : i<p.w) :
 InRegions s.wr (off p.ctx (entryOffset p.w j+8*i)) 8 := by
 rw [entry_index]
 apply h.writable
 have multiple := Nat.mul_le_mul_right p.w (show 2+j≤33 by omega)
 omega

theorem ContextSpace.entry_read {p : Parameters} {s : State} (h : ContextSpace p s)
 {j i : Nat} (hj : j<32) (hi : i<p.w) :
 InRegions (s.rd++s.wr) (off p.ctx (entryOffset p.w j+8*i)) 8 :=
 let ⟨r,hr,contains⟩ := h.entry_write hj hi
 ⟨r,List.mem_append_right _ hr,contains⟩

theorem ContextSpace.entry_outside {p : Parameters} {s : State} (h : ContextSpace p s)
 {j i : Nat} (hj : j<32) (hi : i<8*p.w) :
 p.Z≤ofs p.B (off p.ctx (entryOffset p.w j)+BitVec.ofNat 64 i) := by
 have multiple := Nat.mul_le_mul_left (8*p.w) (show 2+j≤33 by omega)
 have bound : entryOffset p.w j+i<8*(3+34*p.w) := by unfold entryOffset;omega
 have outside := h.outside (entryOffset p.w j+i) bound
 simpa only [off,BitVec.ofNat_add,BitVec.add_assoc] using outside

theorem entry_within (p : Parameters) {j : Nat} (hj : j<32) :
 entryOffset p.w j+8*p.w≤8*(3+34*p.w) := by
 have multiple := Nat.mul_le_mul_left (8*p.w) (show 2+j≤33 by omega)
 unfold entryOffset
 omega

theorem entry_fit (p : Parameters) {j : Nat} (hj : j<32) : entryOffset p.w j+8*p.w≤2^64 := by
 have multiple := Nat.mul_le_mul_left (8*p.w) (show 2+j≤33 by omega)
 have := p.width
 unfold entryOffset
 omega

def entryValue (p : Parameters) (j : Nat) : Nat :=
 Spec.Rsa.powMod p.G (Spec.Rsa.FixedBaseComb.exponent p.N j) p.P*2^(64*p.w)%p.P

def TablePrefix (p : Parameters) (n : Nat) (s : State) : Prop :=
 ∀ j<n,wv s.mem p.ctx (entryOffset p.w j) p.w=entryValue p j

theorem TablePrefix.after_inscr {p : Parameters} {n : Nat} {s t : State}
 (h : TablePrefix p n s) (space : ContextSpace p s) (limit : n≤32)
 (frame : InScr p.B p.Z s.mem t.mem) : TablePrefix p n t := by
 intro j hj
 apply Eq.trans (wv_congr fun i hi => Mem.readW_congr fun b hb => frame _ ?_) (h j hj)
 have outside := space.entry_outside (j:=j) (i:=8*i+b) (by omega) (by omega)
 have same : off p.ctx (entryOffset p.w j+8*i)+BitVec.ofNat 64 b=
  off p.ctx (entryOffset p.w j)+BitVec.ofNat 64 (8*i+b) := by simp only [off,BitVec.ofNat_add,BitVec.add_assoc]
 rw [same]
 exact outside

theorem TablePrefix.extend {p : Parameters} {n : Nat} {s t : State}
 (h : TablePrefix p n s) (limit : n<32) (frame : Outside p.ctx (entryOffset p.w n) (8*p.w) s.mem t.mem)
 (value : wv t.mem p.ctx (entryOffset p.w n) p.w=entryValue p n) : TablePrefix p (n+1) t := by
 intro j hj
 by_cases same : j=n
 · simpa only [same] using value
 · have old : j<n := by omega
   have multiple := Nat.mul_le_mul_left (8*p.w) (show j+1≤n by omega)
   have leftEq : entryOffset p.w j+8*p.w=24+16*p.w+(8*p.w)*(j+1) := by unfold entryOffset;simp only [Nat.mul_add,Nat.add_mul,Nat.mul_comm,Nat.mul_left_comm] <;>omega
   have rightEq : entryOffset p.w n=24+16*p.w+(8*p.w)*n := by unfold entryOffset;simp only [Nat.mul_add,Nat.add_mul,Nat.mul_comm,Nat.mul_left_comm] <;>omega
   have separate : entryOffset p.w j+8*p.w≤entryOffset p.w n := by rw [leftEq,rightEq];omega
   exact (frame.wv (Or.inl separate) (by have := entry_fit p limit;omega)).trans (h j old)

end VG.Proof.Ffdh.AArch64.Cached
