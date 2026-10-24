module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ContextBuild
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.Ring

/-! Table construction changes the workspace and table entries, preserving the canonical prefix. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

def tableStart (w : Nat) : Nat := 24+16*w

def buildWrites (p : Parameters) : List Region :=
 [⟨p.B,p.Z⟩,⟨off p.ctx (tableStart p.w),256*p.w⟩]

abbrev BuildFrame (p : Parameters) := Frame (buildWrites p)

theorem entryOffset_table (w j : Nat) : entryOffset w j=tableStart w+8*w*j := by
 unfold entryOffset tableStart
 ring

theorem buildTable_fit (p : Parameters) : tableStart p.w+256*p.w≤2^64 := by
 have := p.width
 unfold tableStart
 omega

theorem BuildFrame.of_inscr {p : Parameters} {m m' : Mem} (h : InScr p.B p.Z m m') : BuildFrame p m m' := by
 intro x hx
 apply h
 have no := hx ⟨p.B,p.Z⟩ (by simp [buildWrites])
 change ¬ofs p.B x+1≤p.Z at no
 omega

theorem BuildFrame.of_entry {p : Parameters} {m m' : Mem} {j : Nat} (inside : j<32)
 (h : Outside p.ctx (entryOffset p.w j) (8*p.w) m m') : BuildFrame p m m' := by
 have fit := entry_fit p inside
 have localFrame := outside_to_array (by have := p.positive;omega) fit h
 intro x hx
 apply localFrame x
 right
 have no := hx ⟨off p.ctx (tableStart p.w),256*p.w⟩ (by simp [buildWrites])
 have sub : (⟨off p.ctx (entryOffset p.w j),8*p.w⟩ : Region).Sub
   ⟨off p.ctx (tableStart p.w),256*p.w⟩ := by
  have span : 8*p.w*j+8*p.w≤256*p.w := by
   have le := Nat.mul_le_mul_left (8*p.w) (show j+1≤32 by omega)
   have eq : 8*p.w*(j+1)=8*p.w*j+8*p.w := by ring
   rw [eq] at le
   omega
  have hsub := Offset.sub_base (off p.ctx (tableStart p.w)) (d:=8*p.w*j) (n:=8*p.w) (k:=256*p.w) span
  simpa only [entryOffset_table,off,BitVec.ofNat_add,BitVec.add_assoc] using hsub
 have noEntry : ¬(⟨off p.ctx (entryOffset p.w j),8*p.w⟩ : Region).Contains x 1 := fun hi => no (sub x hi)
 change ¬ofs (off p.ctx (entryOffset p.w j)) x+1≤8*p.w at noEntry
 omega

theorem BuildFrame.prefix {p : Parameters} {s t : State} (space : ContextSpace p s)
 (frame : BuildFrame p s.mem t.mem) {i : Nat} (inside : i<tableStart p.w) :
 t.mem (p.ctx+BitVec.ofNat 64 i)=s.mem (p.ctx+BitVec.ofNat 64 i) := by
 apply frame
 intro r hr
 simp only [buildWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
 rcases hr with rfl | rfl
 · have outside := space.outside i (by unfold tableStart at inside;omega)
   change ¬ofs p.B (p.ctx+BitVec.ofNat 64 i)+1≤p.Z
   omega
 · have fit := buildTable_fit p
   have shifted := (outside_shift_iff p.ctx (p.ctx+BitVec.ofNat 64 i)
    (by have := p.positive;omega) fit).mp (Or.inl (by
     rw [show ofs p.ctx (p.ctx+BitVec.ofNat 64 i)=i from Mem.sub_ofNat_toNat p.ctx (by omega)]
     exact inside))
   change ¬ofs (off p.ctx (tableStart p.w)) (p.ctx+BitVec.ofNat 64 i)+1≤256*p.w
   omega

end VG.Proof.Ffdh.AArch64.Cached
