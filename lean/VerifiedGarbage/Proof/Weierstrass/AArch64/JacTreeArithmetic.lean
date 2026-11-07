module
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Fprog
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLayout
public import VerifiedGarbage.Proof.Weierstrass.Jac

import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Production
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd
import VerifiedGarbage.Proof.Weierstrass.Comb
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract

/-! Tree precomputation: even multiples double a previous table entry;
odd multiples add the original public point to the accumulator. -/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

theorem keeps_prog {M : Mod} {base : Addr} {W : List Nat} {s t : State} {rs : List Reg}
    (h : Keeps rs s t) (hr : ∀ r ∈ rs, r ∈ clob M.n) : ProgKeep M base W s t :=
  ⟨fun r hn => h.gpr r (fun hh => hn (hr r hh)),h.rd,h.wr,h.sp,fun _ _ _ => congrFun h.mem _⟩

end VG.Proof.Weierstrass.AArch64
