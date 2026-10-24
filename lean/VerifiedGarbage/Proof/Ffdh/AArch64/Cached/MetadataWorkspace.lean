module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.MetadataMemory
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.WorkspaceState
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! Context metadata stores cannot overwrite the separate scratch controls. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

private theorem contextStore_workspace {p : Parameters} {s : State} (space : ContextSpace p s)
 (m : Mem) {d : Nat} (inside : d+8≤8*(3+34*p.w)) (value : Addr) :
 ∀ x,ofs p.B x<p.Z→(m.writeW (off p.ctx d) value) x=m x := by
 intro x hx
 have fit : d+8≤2^64 := by have := p.width;omega
 have outside (i : Nat) (hi : i<8) : p.Z≤ofs p.B (off p.ctx d+BitVec.ofNat 64 i) := by
  simpa only [off,BitVec.ofNat_add,BitVec.add_assoc] using space.outside (d+i) (by omega)
 apply writeW_outside m p.ctx value fit x
 exact (outside_shift_iff p.ctx x (by omega) fit).mpr (le_ofs_of_sep outside hx)

theorem metadataMemory_workspace {p : Parameters} {s : State} (space : ContextSpace p s) (N : Nat) :
 ∀ x,ofs p.B x<p.Z→metadataMemory s.mem p.B p.ctx N x=
 ((s.mem.writeW (off p.B (8*sBytes)) (BitVec.ofNat 64 ((N+7)/8))).writeW
  (off p.B (8*sRows)) (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows N))) x := by
 intro x hx
 unfold metadataMemory
 rw [contextStore_workspace space _ (d:=16) (by omega) _ x hx,
  contextStore_workspace space _ (d:=8) (by omega) _ x hx]
 simpa only [off,BitVec.add_zero] using contextStore_workspace space _ (d:=0) (by omega) _ x hx

theorem metadataMemory_controls {p : Parameters} {s : State} (space : ContextSpace p s)
 (scratch : Scr s p.B p.Z) (N : Nat) :
 word (metadataMemory s.mem p.B p.ctx N) p.B (8*sBytes)=BitVec.ofNat 64 ((N+7)/8) ∧
 word (metadataMemory s.mem p.B p.ctx N) p.B (8*sRows)=BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows N) ∧
 (∀ i<32,i≠sBytes→i≠sRows→word (metadataMemory s.mem p.B p.ctx N) p.B (8*i)=word s.mem p.B (8*i)) := by
 let m := (s.mem.writeW (off p.B (8*sBytes)) (BitVec.ofNat 64 ((N+7)/8))).writeW
  (off p.B (8*sRows)) (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows N))
 have same (i : Nat) (hi : i<32) : word (metadataMemory s.mem p.B p.ctx N) p.B (8*i)=word m p.B (8*i) :=
  workspace_word (by have := scratch.nowrap;omega) (metadataMemory_workspace space N)
   (by have := hdr_lt_slot p.w 8 hi;have := p.room;omega)
 constructor
 · rw [same sBytes (by decide)]
   exact ((writeW_outside _ _ _ (by decide : 8*sRows+8≤2^64)).word
    (Or.inl (by decide : 8*sBytes+8≤8*sRows)) (by decide)).trans (word_writeW_self _ _ _ _)
 constructor
 · rw [same sRows (by decide)]
   exact word_writeW_self _ _ _ _
 · intro i hi notBytes notRows
   rw [same i hi]
   have separate {j : Nat} (hj : j<32) (different : i≠j) (m : Mem) (v : Addr) :
    word (m.writeW (off p.B (8*j)) v) p.B (8*i)=word m p.B (8*i) :=
    (writeW_outside _ _ _ (by omega)).word (by omega) (by omega)
   exact (separate (by decide) notRows _ _).trans (separate (by decide) notBytes _ _)

end VG.Proof.Ffdh.AArch64.Cached
