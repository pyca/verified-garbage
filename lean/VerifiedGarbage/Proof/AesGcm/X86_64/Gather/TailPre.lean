module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Finish

public section
namespace VG.Proof.AesGcm.X86_64.Gather.DirectTail
open VG VG.X86_64 VG.Proof.AesGcm.X86_64.Short
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Spec.Gcm (Block blockAt)
open VG.Spec.Aes (bytesAt)

structure TailArgs where
  ctx : Addr
  work : Addr
  sp : Addr
  descriptors : Addr
  first : Addr
  second : Addr
  dst : Addr
  firstLen : Nat
  len : Nat
  aadLen : Nat

namespace TailArgs
abbrev consumed (a : TailArgs) := 16*(a.firstLen/16)
abbrev remaining (a : TailArgs) := a.len-a.consumed
abbrev secondLen (a : TailArgs) := a.len-a.firstLen
abbrev output (a : TailArgs) := a.dst+BitVec.ofNat 64 a.consumed
abbrev tail1 (a : TailArgs) := a.first+BitVec.ofNat 64 a.consumed
abbrev wR (a : TailArgs) : Region := ⟨a.work,2560⟩
abbrev outR (a : TailArgs) : Region := ⟨a.output,a.remaining⟩
abbrev firstR (a : TailArgs) : Region := ⟨a.tail1,a.firstLen%16⟩
abbrev secondR (a : TailArgs) : Region := ⟨a.second,a.secondLen⟩
abbrev secondSlot (a : TailArgs) : Region := ⟨a.descriptors+16#64,8⟩
abbrev textBytes (a : TailArgs) (m : Mem) :=
  bytesAt m a.tail1 (a.firstLen%16) ++ bytesAt m a.second a.secondLen
abbrev cipherBytes (a : TailArgs) (m : Mem) :=
  List.zipWith (· ^^^ ·) (a.textBytes m) (bytesAt m (a.work+1040#64) a.remaining)
end TailArgs

/-- Machine state after hashing the whole blocks of the first fragment and
generating the final keystream. An empty second fragment needs no address. -/
structure TailPre (a : TailArgs) (H : Block) (s : State) : Prop where
  env : Env a.ctx (a.work+16#64) a.work a.sp s
  x0 : s.xmm .xmm0=revMask
  x1 : s.xmm .xmm1=poly
  h1 : IsH1 H (s.xmm .xmm3)
  h2 : IsH2 H (s.xmm .xmm3) (s.xmm .xmm6)
  desc : s.mem.readW (a.sp+8#64) 64=a.descriptors
  first : s.mem.readW a.descriptors 64=a.first
  firstLen : s.mem.readW (a.descriptors+8#64) 64=BitVec.ofNat 64 a.firstLen
  second : 0<a.secondLen → s.mem.readW a.secondSlot.base 64=a.second
  data : s.mem.readW (a.work+200#64) 64=a.dst
  len : s.mem.readW (a.work+192#64) 64=BitVec.ofNat 64 a.len
  aad : s.mem.readW (a.work+184#64) 64=BitVec.ofNat 64 a.aadLen
  lenLt : a.len<2^64
  firstLe : a.firstLen≤a.len
  bounded : a.remaining≤16
  stackR : InRegions (s.rd++s.wr) (a.sp+8#64) 8
  descR : Covers [⟨a.descriptors,16⟩] (s.rd++s.wr)
  secondSlotR : 0<a.secondLen → InRegions (s.rd++s.wr) a.secondSlot.base 8
  firstRead : Covers [a.firstR] (s.rd++s.wr)
  secondRead : 0<a.secondLen → Covers [a.secondR] (s.rd++s.wr)
  write : Covers [a.outR] s.wr
  outWork : a.outR.Disjoint a.wR
  firstWork : a.firstR.Disjoint a.wR
  firstOut : a.firstR.Disjoint a.outR
  secondWork : 0<a.secondLen → a.secondR.Disjoint a.wR
  secondOut : 0<a.secondLen → a.secondR.Disjoint a.outR
  slotWork : 0<a.secondLen → a.secondSlot.Disjoint a.wR
  slotOut : 0<a.secondLen → a.secondSlot.Disjoint a.outR

end VG.Proof.AesGcm.X86_64.Gather.DirectTail
end
