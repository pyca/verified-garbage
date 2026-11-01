module

public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.ReadonlyCalls
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.FastTable
public import VerifiedGarbage.Proof.MlKem.Kpke16Contract
public import VerifiedGarbage.Proof.MlKem.AArch64.KeccakCall
public import VerifiedGarbage.Spec.MlKem

import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.Call
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.FwdF
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.AbiF
import VerifiedGarbage.Proof.MlKem.AArch64.PrimCall
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.InvFI
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.AbiFI
/-!
# ML-KEM on AArch64: the 16-bit NTT and its inverse of polynomials stored with 16 bits, at offsets

`vg_mlkem16_ntt` and `vg_mlkem16_inv_ntt` called on the polynomial at an offset of `x28`
(`nttAtWithW_ok`, `nttInvAtWithW_ok`). The polynomial and the working space are 512 bytes
each.
-/

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/NttR/CallF.lean`, which only this module imported.
section

/-!
# ML-KEM on AArch64: calling `vg_mlkem16_ntt`

`fwdFast` as a callee: correct under its own contract (`fastC`), and its
call on the polynomial at `f` (`ntt16_call`), with the table as `FastReady`
says.
-/

section

namespace VG.Proof.MlKem.AArch64.NttR

open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Impl.MlKem.AArch64.Ntt16.Fast (fwdFast name)

/-- `fwdFast`'s contract as the code sees it. -/
def fastC : Contract isa where
  pre s := InF s
  post s t := PolyIsW 16 t.mem (s.gpr .x0) (ntt (polyAtW 16 s.mem (s.gpr .x0)))
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.syms name = t.syms name

theorem fastC_correct (s : State) (h : fastC.pre s) :
    ∃ tr t, Exec isa fwdFast s tr t ∧ abiPreserved s t ∧ fastC.post s t := by
  obtain ⟨tr, t, he, -, hp⟩ := fwdF_run s h
  exact ⟨tr, t, he, fwdFast_abi he, hp⟩

/-- `vg_mlkem16_ntt(f, _)`: `NTT` of the polynomial with 16-bit coefficients at `f`. -/
theorem ntt16_call {s : State} {f : Addr} (h0 : s.gpr .x0 = f) (hr : ReducedW 16 s.mem f)
    (hw : Covers [⟨f, 512⟩] s.wr) {w : Addr} (ht : FastReady s f w) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨f, 512⟩] s s' → PolyIsW 16 s'.mem f (ntt (polyAtW 16 s.mem f)) → Q s') :
    WP isa (.call "vg_mlkem16_ntt" fwdFast) s Q := by
  have c0 : s.callEntry.gpr .x0 = f := (entry s).trans h0
  refine WP.callV (k := fastC) fastC_correct (rd := [fastRegion s]) (wr := [⟨f, 512⟩]) ?_
    (ht.readable.append_left hw.right) hw ?_
  · have hsy : (s.callEntry.withRegions [fastRegion s] [⟨f, 512⟩]).syms = s.syms := rfl
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [State.withRegions_wr, State.withRegions_gpr, c0]; exact List.mem_singleton_self _
    · simpa only [State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr, c0] using hr
    · simpa only [State.withRegions_mem, State.callEntry_mem, hsy] using ht.table
    · simp only [State.withRegions_rd, State.withRegions_wr, hsy]
      exact Covers.of_mem (fun r h => List.mem_append_left _ h)
    · simpa only [State.withRegions_gpr, hsy, c0] using ht.output.sub_left (Region.sub_prefix (by decide : 512 ≤ 1024))
  · intro s' hrd hwr hsp hf hcs _ hvec hpost
    simp only [fastC, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0] at hpost
    exact hQ s' ⟨hcs, hsp, hrd, hwr, hf, hvec⟩ hpost

end VG.Proof.MlKem.AArch64.NttR
end

end

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/NttR/CallFI.lean`, which only this module imported.
section

/-!
# ML-KEM on AArch64: calling `vg_mlkem16_inv_ntt`

`invFast` as a callee: correct under its own contract (`fastInvC`), and its
call on the polynomial at `f` (`nttInv16_call`), with the table as
`FastInvReady` says.
-/

section

namespace VG.Proof.MlKem.AArch64.NttR

open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Impl.MlKem.AArch64.Ntt16.FastInv (invFast name)

/-- `invFast`'s contract as the code sees it. -/
def fastInvC : Contract isa where
  pre s := InFI s
  post s t := PolyIsW 16 t.mem (s.gpr .x0) (nttInv (polyAtW 16 s.mem (s.gpr .x0)))
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.syms name = t.syms name

theorem fastInvC_correct (s : State) (h : fastInvC.pre s) :
    ∃ tr t, Exec isa invFast s tr t ∧ abiPreserved s t ∧ fastInvC.post s t := by
  obtain ⟨tr, t, he, -, hp⟩ := invFI_run s h
  exact ⟨tr, t, he, invFast_abi he, hp⟩

/-- `vg_mlkem16_inv_ntt(f, _)`: `NTT⁻¹` of the polynomial with 16-bit coefficients at `f`. -/
theorem nttInv16_call {s : State} {f : Addr} (h0 : s.gpr .x0 = f) (hr : ReducedW 16 s.mem f)
    (hw : Covers [⟨f, 512⟩] s.wr) {w : Addr} (ht : FastInvReady s f w) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨f, 512⟩] s s' → PolyIsW 16 s'.mem f (nttInv (polyAtW 16 s.mem f)) → Q s') :
    WP isa (.call "vg_mlkem16_inv_ntt" invFast) s Q := by
  have c0 : s.callEntry.gpr .x0 = f := (entry s).trans h0
  refine WP.callV (k := fastInvC) fastInvC_correct (rd := [fastInvRegion s]) (wr := [⟨f, 512⟩]) ?_
    (ht.readable.append_left hw.right) hw ?_
  · have hsy : (s.callEntry.withRegions [fastInvRegion s] [⟨f, 512⟩]).syms = s.syms := rfl
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [State.withRegions_wr, State.withRegions_gpr, c0]; exact List.mem_singleton_self _
    · simpa only [State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr, c0] using hr
    · simpa only [State.withRegions_mem, State.callEntry_mem, hsy] using ht.table
    · simp only [State.withRegions_rd, State.withRegions_wr, hsy]
      exact Covers.of_mem (fun r h => List.mem_append_left _ h)
    · simpa only [State.withRegions_gpr, hsy, c0] using ht.output.sub_left (Region.sub_prefix (by decide : 512 ≤ 1024))
  · intro s' hrd hwr hsp hf hcs _ hvec hpost
    simp only [fastInvC, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0] at hpost
    exact hQ s' ⟨hcs, hsp, hrd, hwr, hf, hvec⟩ hpost

end VG.Proof.MlKem.AArch64.NttR
end

end

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
