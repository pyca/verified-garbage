module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.MetadataHead
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.MetadataRows
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.MetadataTail
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Exact serialization of the reviewed sampling width and comb row count. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def metadataMemory (m : Mem) (B ctx : Addr) (N : Nat) : Mem :=
 let m1 := m.writeW (off B (8*sBytes)) (BitVec.ofNat 64 ((N+7)/8))
 let m2 := m1.writeW (off B (8*sRows)) (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows N))
 ((m2.writeW ctx (BitVec.ofNat 64 N)).writeW (off ctx 8) (BitVec.ofNat 64 ((N+7)/8))).writeW
  (off ctx 16) (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows N))

theorem metadata_ok {s : State} {B ctx : Addr} {Z N : Nat}
 (scratch : Scr s B Z) (room : 256≤Z) (output : Scr s ctx 24)
 (base : s.gpr .x0=B) (context : word s.mem B (8*sCtx)=ctx)
 (bits : word s.mem B (8*sBits)=BitVec.ofNat 64 N) (positive : 0<N) (bound : N≤8192) :
 WP isa Policy.metadata s fun t => t.mem=metadataMemory s.mem B ctx N ∧
 Keep [.x8,.x10,.x11,.x12,.x13,.x14] s t := by
 unfold Policy.metadata
 rw [WP.seq_iff]
 refine WP.mono (metadataHead_ok scratch room base bound bits) ?_
 rintro u ⟨⟨bitsU,widthU,leftU,countU,memU⟩,restU⟩
 rw [WP.seq_iff]
 refine WP.mono (metadataRows_ok u positive bound leftU countU) ?_
 rintro v ⟨countV,memV,restV⟩
 have rest := restU.trans restV
 have frame : Outside B (8*sBytes) 8 s.mem u.mem := by
  rw [memU];exact writeW_outside _ _ _ (by decide)
 have ctxV : word v.mem B (8*sCtx)=ctx := by
  rw [memV]
  exact (frame.word (Or.inl (by decide : 8*sCtx+8≤8*sBytes)) (by decide)).trans context
 refine WP.mono (metadataTail_ok (scratch.congr rest.wr) room (output.congr rest.wr)
  ((rest.gpr .x0 (by decide)).trans base) ctxV
  ((restV.gpr .x10 (by decide)).trans bitsU) ((restV.gpr .x11 (by decide)).trans widthU) countV) ?_
 rintro t ⟨memT,restT⟩
 refine ⟨?_,(rest.trans restT).mono (by decide)⟩
 rw [memV,memU] at memT
 exact memT

end VG.Proof.Ffdh.AArch64.Cached
