module
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.ReadonlyCalls
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.Call
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.FastTable
public import VerifiedGarbage.Spec.MlKem.Kpke16
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.CallF
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.CallFI

import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MlKem.AArch64.KeccakCall
public import VerifiedGarbage.Spec.MlKem

/-!
# ML-KEM on AArch64: the 16-bit NTT and its inverse of polynomials stored with 16 bits, at offsets

`vg_mlkem16_ntt` and `vg_mlkem16_inv_ntt` called on the polynomial at an offset of `x28`
(`nttAtWithW_ok`, `nttInvAtWithW_ok`). The polynomial and the working space are 512 bytes
each.
-/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Ntt16.W
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Ntt16
open VG.Proof.MlKem.AArch64.Ntt16.Readonly (TableReady)
open VG.Impl.MlKem.AArch64.Ntt16

theorem nttAtWithW_ok {s : State} {off ns : Nat} {f w : Addr} {F : Poly}
    (hoff : off<65536) (hns : ns<65536)
    (hf : s.gpr .x28+BitVec.ofNat 64 off=f) (hw : s.gpr .x28+BitVec.ofNat 64 ns=w)
    (_hd : (Region.mk f 512).Disjoint ⟨w,512⟩) (hp : PolyIsW 16 s.mem f F)
    (hc : Covers [⟨f,512⟩,⟨w,512⟩] s.wr) (ht : NttR.FastReady s f w) :
    WP isa (Impl.MlKem.AArch64.Ntt16.Readonly.nttAtWithW off ns) s fun t=>
      Kept [⟨f,512⟩,⟨w,512⟩] s t ∧ PolyIsW 16 t.mem f (ntt F) := by
  have prep : WP isa (.block (Impl.MlKem.AArch64.ptrTo .x0 .x28 off ++ Impl.MlKem.AArch64.ptrTo .x1 .x28 ns)) s
      fun z=>Only [.x0,.x1] s z ∧ z.gpr .x0=f ∧ z.gpr .x1=w := by
    refine wp_ptrTo (by decide) hoff fun a ha ea=>wp_ptrTo' (by decide) hns fun z hz ez=>?_
    exact ⟨(ha.trans hz).mono (by simp),by rw [hz.get .x0 (by decide),ea]; exact hf,
      by rw [ez,ha.get .x28 (by decide)]; exact hw⟩
  refine WP.seq (WP.mono_syms prep fun z ⟨oz,z0,_⟩ zs=>?_)
  have table : NttR.FastReady z f w :=
    ⟨by simpa only [zs,oz.mem] using ht.table,
      by simpa only [NttR.sRegion,zs,oz.rd,oz.wr] using ht.readable,
      by simpa only [NttR.sRegion,zs] using ht.output,by simpa only [NttR.sRegion,zs] using ht.scratch⟩
  exact NttR.ntt16_call z0 (by rw [oz.mem]; exact hp.1) (by rw [oz.wr]; exact Covers.head hc) table
    fun t kt pt=>⟨(Kept.of_keep oz.keep oz.mem (by decide)).trans
      (kt.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self),
      by simpa only [oz.mem,hp.2] using pt⟩

theorem nttInvAtWithW_ok {s : State} {off ns : Nat} {f w : Addr} {F : Poly}
    (hoff : off<65536) (hns : ns<65536)
    (hf : s.gpr .x28+BitVec.ofNat 64 off=f) (hw : s.gpr .x28+BitVec.ofNat 64 ns=w)
    (_hd : (Region.mk f 512).Disjoint ⟨w,512⟩) (hp : PolyIsW 16 s.mem f F)
    (hc : Covers [⟨f,512⟩,⟨w,512⟩] s.wr) (ht : NttR.FastInvReady s f w) :
    WP isa (Impl.MlKem.AArch64.Ntt16.Readonly.nttInvAtWithW off ns) s fun t=>
      Kept [⟨f,512⟩,⟨w,512⟩] s t ∧ PolyIsW 16 t.mem f (nttInv F) := by
  have prep : WP isa (.block (Impl.MlKem.AArch64.ptrTo .x0 .x28 off ++ Impl.MlKem.AArch64.ptrTo .x1 .x28 ns)) s
      fun z=>Only [.x0,.x1] s z ∧ z.gpr .x0=f ∧ z.gpr .x1=w := by
    refine wp_ptrTo (by decide) hoff fun a ha ea=>wp_ptrTo' (by decide) hns fun z hz ez=>?_
    exact ⟨(ha.trans hz).mono (by simp),by rw [hz.get .x0 (by decide),ea]; exact hf,
      by rw [ez,ha.get .x28 (by decide)]; exact hw⟩
  refine WP.seq (WP.mono_syms prep fun z ⟨oz,z0,_⟩ zs=>?_)
  have table : NttR.FastInvReady z f w :=
    ⟨by simpa only [zs,oz.mem] using ht.table,
      by simpa only [NttR.sRegion,zs,oz.rd,oz.wr] using ht.readable,
      by simpa only [NttR.sRegion,zs] using ht.output,by simpa only [NttR.sRegion,zs] using ht.scratch⟩
  exact NttR.nttInv16_call z0 (by rw [oz.mem]; exact hp.1) (by rw [oz.wr]; exact Covers.head hc) table
    fun t kt pt=>⟨(Kept.of_keep oz.keep oz.mem (by decide)).trans
      (kt.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self),
      by simpa only [oz.mem,hp.2] using pt⟩

end VG.Proof.MlKem.AArch64.Ntt16.W
