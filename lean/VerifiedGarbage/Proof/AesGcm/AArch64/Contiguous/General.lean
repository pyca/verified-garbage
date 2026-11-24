module

public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.LeafCT
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Offset

/-! Caller-owned buffers, available stack and the result of contiguous authenticated encryption. -/
@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous
open VG VG.AArch64

abbrev srcR (s : State) : Region := ⟨s.gpr .x6,(stackArg s 0).toNat⟩
abbrev dstR (s : State) : Region := ⟨s.gpr .x7,(stackArg s 0).toNat⟩
abbrev tagR (s : State) : Region := ⟨stackArg s 1,16⟩
abbrev callerArgs (s : State) : Region := ⟨stackArgAddr s 0,24⟩
abbrev externalRegions (s : State) : List Region :=
  [Gather.kR .plain s,Gather.nR s,Gather.aR s,srcR s,dstR s,tagR s]

/-- The same facts are established for both cases of the paired-buffer API. -/
structure Caller (s : State) : Prop where
  read : Covers [Gather.kR .plain s,Gather.nR s,Gather.aR s,srcR s,callerArgs s] (s.rd ++ s.wr)
  write : Covers [dstR s,tagR s] s.wr
  kd : (Gather.kR .plain s).Disjoint (dstR s)
  kt : (Gather.kR .plain s).Disjoint (tagR s)
  nd : (Gather.nR s).Disjoint (dstR s)
  nt : (Gather.nR s).Disjoint (tagR s)
  ad : (Gather.aR s).Disjoint (dstR s)
  atag : (Gather.aR s).Disjoint (tagR s)
  sd : (srcR s).Disjoint (dstR s) ∨ s.gpr .x6 = s.gpr .x7
  st : (srcR s).Disjoint (tagR s)
  dt : (dstR s).Disjoint (tagR s)
  dstArgs : (dstR s).Disjoint (callerArgs s)
  stack : ∀ r ∈ externalRegions s, (below s.sp 2640).Disjoint r
  nowrap : ∀ r ∈ externalRegions s, r.base.toNat + r.len ≤ 2^64
  room : 2640 ≤ s.sp.toNat
  top : s.sp.toNat+24 ≤ 2^64
  rounds : VG.Proof.AesGcm.AArch64.rounds (s.gpr .x1)

/-! The caller’s three stack arguments remain readable across either bounded frame. -/
namespace BoundedArgs
open DirectGather.Compact (base scratch LocalMem scratchArg)

theorem scratchApart (size : Fin 753) (o : State) (c : Caller o) (r : Region) (hr : r ∈ externalRegions o) :
    (scratch size o).Disjoint r :=
  (c.stack r hr).sub_left (Offset.sub_below _ (by have := size.isLt; omega) (by have := size.isLt; omega))

theorem argsApart (size : Fin 753) (o : State) : (callerArgs o).Disjoint (scratch size o) := by
  simpa only [callerArgs,stackArgAddr,scratch,base,Nat.mul_zero,BitVec.add_zero] using
    Offset.base_disjoint_below o.sp (by have := size.isLt; omega : size.val+24 ≤ 2^64)

theorem argRead {size : Fin 753} {o t : State} (c : Caller o) (m : LocalMem size o t) (i : Nat) (hi : i < 3) :
    InRegions (t.rd ++ t.wr) (base size o + BitVec.ofNat 64 (size.val+8*i)) 8 := by
  rw [scratchArg]
  exact m.read _ _ (c.read _ _ ⟨callerArgs o,by simp,DirectGather.stackArg_contains o i hi⟩)

theorem argVal {size : Fin 753} {o t : State} (m : LocalMem size o t) (i : Nat) (hi : i < 3) :
    t.mem.readW (base size o + BitVec.ofNat 64 (size.val+8*i)) 64 = stackArg o i := by
  rw [scratchArg]
  exact m.frame.read (DirectGather.stackArg_contains o i hi)
    (by simpa only [List.mem_singleton,forall_eq] using argsApart size o) (by decide)

end BoundedArgs

namespace Prepared

abbrev powerR (s : State) : Region := ⟨stackArg s 2,128⟩
structure Powers (o : State) : Prop where
  read : Covers [powerR o] (o.rd++o.wr)
  dst : (powerR o).Disjoint (dstR o)
  stack : (powerR o).Disjoint (below o.sp 2640)
  repr : Spec.Gcm.Powers8Repr o.mem (stackArg o 2) (Spec.Gcm.ctxH o.mem (o.gpr .x0))

end Prepared

/-- Authenticate precisely the bytes at the source in the caller's original memory. -/
def result (s t : State) : Prop :=
  Spec.Gcm.encryptWith (Spec.Gcm.ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat)
      (Spec.Gcm.ctxH s.mem (s.gpr .x0)) 16
      (Spec.Aes.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
      (Spec.Aes.bytesAt s.mem (s.gpr .x6) (stackArg s 0).toNat)
      (Spec.Aes.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) =
    (Spec.Aes.bytesAt t.mem (s.gpr .x7) (stackArg s 0).toNat,Spec.Aes.bytesAt t.mem (stackArg s 1) 16)

theorem result_frame {o u v : State} (c : Caller o) {k : Nat} (le : k ≤ 2640)
    (p : result o u) (f : Frame [below o.sp k] u.mem v.mem) : result o v := by
  have sub : (below o.sp k).Sub (below o.sp 2640) := Offset.sub_below _ le (by omega)
  have apart {r : Region} (mem : r ∈ externalRegions o) : ∀ w ∈ [below o.sp k], r.Disjoint w := by
    simpa only [List.mem_singleton,forall_eq] using ((c.stack _ mem).sub_left sub).symm
  unfold result at *
  rw [bytesAt_frame f (apart (r := dstR o) (by simp [externalRegions])) (Nat.le_of_lt (stackArg o 0).isLt),
    bytesAt_frame f (apart (r := tagR o) (by simp [externalRegions])) (by decide)]
  exact p

end VG.Proof.AesGcm.AArch64.Contiguous
