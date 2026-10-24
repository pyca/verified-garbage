module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Precompute
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! The native entry saves only public arguments in the scratch header. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def entryMemory (m : Mem) (B ctx dom dl k : Addr) : Mem :=
 (((m.writeW (off B (8*sCtx)) ctx).writeW (off B (8*sDom)) dom).writeW
 (off B (8*sDL)) dl).writeW (off B (8*sLen)) k

theorem precomputeEntry_ok {s : State} {B : Addr} {Z : Nat}
 (scratch : Scr s B Z) (room : 256≤Z) (base : s.gpr .x5=B) :
 WP isa (.block Precompute.entry) s fun t =>
 (t.gpr .x0=B ∧ t.mem=entryMemory s.mem B (s.gpr .x0) (s.gpr .x2) (s.gpr .x3) (s.gpr .x4)) ∧
 Keep [.x0] s t := by
 refine WP.keep [.x0] (Q:=fun t => t.gpr .x0=B ∧ t.mem=entryMemory s.mem B (s.gpr .x0) (s.gpr .x2) (s.gpr .x3) (s.gpr .x4)) ?_ rfl rfl rfl
 unfold Precompute.entry entryMemory
 brun [base,st,hdr_enc (show sCtx<32 by decide),hdr_enc (show sDom<32 by decide),
  hdr_enc (show sDL<32 by decide),hdr_enc (show sLen<32 by decide),
  scratch.st (d:=8*sCtx) (by unfold sCtx;omega),
  scratch.st (d:=8*sDom) (by unfold sDom;omega),
  scratch.st (d:=8*sDL) (by unfold sDL;omega),
  scratch.st (d:=8*sLen) (by unfold sLen;omega)]

theorem entryMemory_header (m : Mem) (B ctx dom dl k : Addr) :
 word (entryMemory m B ctx dom dl k) B (8*sCtx)=ctx ∧
 word (entryMemory m B ctx dom dl k) B (8*sDom)=dom ∧
 word (entryMemory m B ctx dom dl k) B (8*sDL)=dl ∧
 word (entryMemory m B ctx dom dl k) B (8*sLen)=k := by
 have separate (m : Mem) (i j : Nat) (hi : i<32) (hj : j<32) (different : i≠j) (v : Addr) :
  word (m.writeW (off B (8*i)) v) B (8*j)=word m B (8*j) :=
  Mem.readW_writeW_sep (Offset.sep B (by omega) (by omega) (by omega)) (by decide)
 unfold entryMemory
 rw [separate _ sLen sCtx (by decide) (by decide) (by decide) _,
  separate _ sDL sCtx (by decide) (by decide) (by decide) _,
  separate _ sDom sCtx (by decide) (by decide) (by decide) _,word_writeW_self,
  separate _ sLen sDom (by decide) (by decide) (by decide) _,
  separate _ sDL sDom (by decide) (by decide) (by decide) _,word_writeW_self,
  separate _ sLen sDL (by decide) (by decide) (by decide) _,word_writeW_self,word_writeW_self]
 exact ⟨rfl,rfl,rfl,rfl⟩

theorem entryMemory_range (m : Mem) (B ctx dom dl k : Addr) :
 Outside B 128 32 m (entryMemory m B ctx dom dl k) := by
 intro x hx
 have store (m : Mem) (i : Nat) (low : 16≤i) (high : i<20) (v : Addr) :
  (m.writeW (off B (8*i)) v) x=m x :=
  writeW_outside m B v (by omega) x (by omega)
 unfold entryMemory
 rw [store _ sLen (by decide) (by decide),store _ sDL (by decide) (by decide),
  store _ sDom (by decide) (by decide),store _ sCtx (by decide) (by decide)]

theorem entryMemory_frame (m : Mem) (B ctx dom dl k : Addr) (Z : Nat) (room : 256≤Z) :
 InScr B Z m (entryMemory m B ctx dom dl k) := by
 have frame := (Frame.refl [⟨B,Z⟩] m).writeW (r:=⟨B,Z⟩) (b:=off B (8*sCtx)) (by simp) ctx
  (Offset.contains_base _ (by unfold sCtx;omega) (by decide))
 have frame := frame.writeW (r:=⟨B,Z⟩) (b:=off B (8*sDom)) (by simp) dom
  (Offset.contains_base _ (by unfold sDom;omega) (by decide))
 have frame := frame.writeW (r:=⟨B,Z⟩) (b:=off B (8*sDL)) (by simp) dl
  (Offset.contains_base _ (by unfold sDL;omega) (by decide))
 have frame := frame.writeW (r:=⟨B,Z⟩) (b:=off B (8*sLen)) (by simp) k
  (Offset.contains_base _ (by unfold sLen;omega) (by decide))
 intro x hx
 exact frame x (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr;subst r;change ¬ofs B x+1≤Z;omega)

end VG.Proof.Ffdh.AArch64.Cached
