module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Generate
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! Copy the three canonical public metadata words into native controls. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def generationMetadataMemory (m : Mem) (B N bytes rows : Addr) : Mem :=
 ((m.writeW (off B (8*sBits)) N).writeW (off B (8*sBytes)) bytes).writeW (off B (8*sRows)) rows

theorem generationMetadata_range (m : Mem) (B N bytes rows : Addr) :
 Outside B 128 80 m (generationMetadataMemory m B N bytes rows) := by
 intro q hq
 have store (m : Mem) (i : Nat) (low : 16≤i) (high : i<26) (v : Addr) :
  (m.writeW (off B (8*i)) v) q=m q := writeW_outside m B v (by omega) q (by omega)
 unfold generationMetadataMemory
 rw [store _ sRows (by decide) (by decide),store _ sBytes (by decide) (by decide),store _ sBits (by decide) (by decide)]

theorem generateEntryMetadata_ok {s : State} {B ctx N bytes rows : Addr} {Z : Nat}
 (scratch : Scr s B Z) (room : 256≤Z) (base : s.gpr .x0=B) (context : s.gpr .x9=ctx)
 (read0 : InRegions (s.rd++s.wr) ctx 8) (read8 : InRegions (s.rd++s.wr) (off ctx 8) 8)
 (read16 : InRegions (s.rd++s.wr) (off ctx 16) 8)
 (value0 : word s.mem ctx 0=N) (value8 : word s.mem ctx 8=bytes) (value16 : word s.mem ctx 16=rows) :
 WP isa (.block (Generate.entry.drop 10)) s fun t =>
 t.mem=generationMetadataMemory s.mem B N bytes rows ∧ Keep [.x10,.x11,.x12] s t := by
 refine WP.keep [.x10,.x11,.x12] ?_ rfl rfl rfl
 unfold Generate.entry generationMetadataMemory
 dsimp only [List.drop]
 have v0 : s.mem.readW ctx 64=N := by simpa only [word,off,BitVec.add_zero] using value0
 brun [base,context,read0,read8,read16,v0,value8,value16,
  hdr_enc (show sBits<32 by decide),hdr_enc (show sBytes<32 by decide),hdr_enc (show sRows<32 by decide),
  scratch.st (d:=8*sBits) (by unfold sBits;omega),scratch.st (d:=8*sBytes) (by unfold sBytes;omega),
  scratch.st (d:=8*sRows) (by unfold sRows;omega)]

end VG.Proof.Ffdh.AArch64.Cached
