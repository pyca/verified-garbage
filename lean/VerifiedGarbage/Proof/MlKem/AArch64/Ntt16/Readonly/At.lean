module
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.Call
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.ReadonlyCalls
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Ntt16.Readonly
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem.AArch64

theorem TableReady.frame {s t : State} {symbol : String} {H : List Nat} {f w : Addr} {rs : List Region}
 (ht : TableReady s symbol H f w) (hs : t.syms=s.syms) (hr : t.rd=s.rd) (hw : t.wr=s.wr)
 (hf : Frame rs s.mem t.mem) (hd : ∀r∈rs,(Region.mk (s.syms symbol) 512).Disjoint r) :
 TableReady t symbol H f w := by
 refine ⟨?_,by simpa only [hs,hr,hw] using ht.readable,
   by simpa only [hs] using ht.output,by simpa only [hs] using ht.scratch⟩
 intro i hi
 rw [hs,hf.readW (Offset.contains_base _ (by omega) (by omega)) hd (by decide)]
 exact ht.table i hi

theorem nttAtWith_ok {s : State} {off ns : Nat} {f w : Addr} {F : Poly}
 (hoff : off<65536) (hns : ns<65536)
 (hf : s.gpr .x28+BitVec.ofNat 64 off=f) (hw : s.gpr .x28+BitVec.ofNat 64 ns=w)
 (hd : (polyRegion f).Disjoint (polyRegion w)) (hp : PolyIs s.mem f F)
 (hc : Covers [polyRegion f,polyRegion w] s.wr)
 (ht : TableReady s "VG_MLKEM_NTT16_ZETAS" Impl.MlKem.AArch64.Ntt16.tableHalves f w) :
 WP isa (Impl.MlKem.AArch64.Ntt16.Readonly.nttAtWith off ns) s fun t=>
 Kept [polyRegion f,polyRegion w] s t ∧ PolyIs t.mem f (ntt F) := by
 have prep : WP isa (.block (Impl.MlKem.AArch64.ptrTo .x0 .x28 off ++ Impl.MlKem.AArch64.ptrTo .x1 .x28 ns)) s
     fun z=>Only [.x0,.x1] s z ∧ z.gpr .x0=f ∧ z.gpr .x1=w := by
  refine wp_ptrTo (by decide) hoff fun a ha ea=>wp_ptrTo' (by decide) hns fun z hz ez=>?_
  exact ⟨(ha.trans hz).mono (by simp),by rw [hz.get .x0 (by decide),ea]; exact hf,
    by rw [ez,ha.get .x28 (by decide)]; exact hw⟩
 refine WP.seq (WP.mono_syms prep fun z ⟨oz,z0,z1⟩ zs=>?_)
 have table : TableReady z "VG_MLKEM_NTT16_ZETAS" Impl.MlKem.AArch64.Ntt16.tableHalves f w := by
  exact ⟨by simpa only [zs,oz.mem] using ht.table,
    by simpa only [zs,oz.rd,oz.wr] using ht.readable,
    by simpa only [zs] using ht.output,by simpa only [zs] using ht.scratch⟩
 exact fwd_call z0 z1 hd (by rw [oz.mem]; exact hp.1)
   (by rw [oz.wr]; exact hc) table fun t kt pt=>
   ⟨(Kept.of_keep oz.keep oz.mem (by decide)).trans kt,by simpa only [oz.mem,hp.2] using pt⟩
theorem nttInvAtWith_ok {s : State} {off ns : Nat} {f w : Addr} {F : Poly}
 (hoff : off<65536) (hns : ns<65536)
 (hf : s.gpr .x28+BitVec.ofNat 64 off=f) (hw : s.gpr .x28+BitVec.ofNat 64 ns=w)
 (hd : (polyRegion f).Disjoint (polyRegion w)) (hp : PolyIs s.mem f F)
 (hc : Covers [polyRegion f,polyRegion w] s.wr)
 (ht : TableReady s "VG_MLKEM_INTT16_ZETAS" Impl.MlKem.AArch64.Ntt16.invTableHalves f w) :
 WP isa (Impl.MlKem.AArch64.Ntt16.Readonly.nttInvAtWith off ns) s fun t=>
 Kept [polyRegion f,polyRegion w] s t ∧ PolyIs t.mem f (nttInv F) := by
 have prep : WP isa (.block (Impl.MlKem.AArch64.ptrTo .x0 .x28 off ++ Impl.MlKem.AArch64.ptrTo .x1 .x28 ns)) s
     fun z=>Only [.x0,.x1] s z ∧ z.gpr .x0=f ∧ z.gpr .x1=w := by
  refine wp_ptrTo (by decide) hoff fun a ha ea=>wp_ptrTo' (by decide) hns fun z hz ez=>?_
  exact ⟨(ha.trans hz).mono (by simp),by rw [hz.get .x0 (by decide),ea]; exact hf,
    by rw [ez,ha.get .x28 (by decide)]; exact hw⟩
 refine WP.seq (WP.mono_syms prep fun z ⟨oz,z0,z1⟩ zs=>?_)
 have table : TableReady z "VG_MLKEM_INTT16_ZETAS" Impl.MlKem.AArch64.Ntt16.invTableHalves f w := by
  exact ⟨by simpa only [zs,oz.mem] using ht.table,
    by simpa only [zs,oz.rd,oz.wr] using ht.readable,
    by simpa only [zs] using ht.output,by simpa only [zs] using ht.scratch⟩
 exact inv_call z0 z1 hd (by rw [oz.mem]; exact hp.1)
   (by rw [oz.wr]; exact hc) table fun t kt pt=>
   ⟨(Kept.of_keep oz.keep oz.mem (by decide)).trans kt,by simpa only [oz.mem,hp.2] using pt⟩
end VG.Proof.MlKem.AArch64.Ntt16.Readonly
