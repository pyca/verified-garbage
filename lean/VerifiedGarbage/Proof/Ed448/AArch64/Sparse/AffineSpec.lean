module

public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Save
public import VerifiedGarbage.Proof.X448.AArch64.Base.AddDefs
public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Joint

/-! Untrusted interface for inline affine addition. The implementation proof is
passed by the registration, keeping NEON arithmetic algebra out of its callers. -/

@[expose] public section
namespace VG.Proof.Ed448.AArch64.Sparse
open VG VG.AArch64
open VG.Impl.X448.AArch64 (slot ACC)
open VG.Proof.X448.AArch64 (Scr Keeps ofs)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd Same fclob)
open VG.Proof.Curve448.AArch64.Fast (Mb)
open VG.Proof.X448.AArch64.Base (affEnv)
local notation "EV" => VG.Proof.X448.AArch64.Weak.E

structure AffineKeep (base:Addr) (s t:State) : Prop where
  regs : Keeps fclob s t
  saved : ∀ i<8,t.gpr (VG.Impl.X448.AArch64.Fast.saved i)=s.gpr (VG.Impl.X448.AArch64.Fast.saved i)
  mem : ∀ a,(ofs base a<64 ∨ 2880≤ofs base a) →
    (ofs base a<ACC ∨ ACC+1152≤ofs base a) →
    (ofs base a<GSAVE ∨ GSAVE+64≤ofs base a) → t.mem a=s.mem a

structure AffineOk : Prop where
  ok : ∀ {s:State} {base:Addr} (_hs:Scr s base) (_hb:BEnv s.mem base)
    (_hz:Bnd Mb s.mem base (slot 19)),
    WP isa VG.Impl.Ed448.AArch64.Sparse.addAffine s fun t =>
      AffineKeep base s t ∧ BEnv t.mem base ∧
      Same base (VG.Proof.X448.AArch64.Base.temps++[5,3,4]) s.mem t.mem ∧
      Bnd Mb t.mem base (slot 3) ∧ Bnd Mb t.mem base (slot 4) ∧ Bnd Mb t.mem base (slot 5) ∧
      EV t.mem base=affEnv 3 4 5 6 7 (EV s.mem base)

end VG.Proof.Ed448.AArch64.Sparse
