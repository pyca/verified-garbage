module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PowerState

/-! Register-only phases preserve arithmetic state when memory is unchanged. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem good_after_mem {s t : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {rs : List Reg}
 (good : Good s B Z w mi) (mem : t.mem=s.mem) (rest : Keep rs s t) (base : t.gpr .x0=B) : Good t B Z w mi :=
 ⟨good.scr.congr rest.wr,base,mem ▸ good.hdr⟩

theorem ModState.after_mem {p : Parameters} {s t : State} {rs : List Reg}
 (state : ModState p s) (mem : t.mem=s.mem) (rest : Keep rs s t) (base : t.gpr .x0=p.B) : ModState p t :=
 ⟨good_after_mem state.good mem rest base,mem ▸ state.modulus,mem ▸ state.inverse,mem ▸ state.one,mem ▸ state.r2⟩

end VG.Proof.Ffdh.AArch64.Cached
