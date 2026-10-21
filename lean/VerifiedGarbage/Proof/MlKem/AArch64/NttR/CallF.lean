module

public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.FwdF
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.FastTable
public import VerifiedGarbage.Proof.MlKem.AArch64.KeccakCall
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.AbiF
import VerifiedGarbage.Proof.MlKem.AArch64.PrimCall
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-KEM on AArch64: calling `vg_mlkem16_ntt`

`fwdFast` as a callee: correct under its own contract (`fastC`), and its
call on the polynomial at `f` (`ntt16_call`), with the table as `FastReady`
says.
-/

@[expose] public section

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
