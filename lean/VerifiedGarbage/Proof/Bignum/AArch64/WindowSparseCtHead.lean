module

public import VerifiedGarbage.Proof.Bignum.AArch64.WindowSparseCtContext
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCtHead
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSparseTile
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightSetup
import VerifiedGarbage.Proof.Bignum.AArch64.WindowSparseRows
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtContext
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightRows

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowSparse
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.BlockedRedc (FastW blocks)
open VG.Proof.Bignum.AArch64.ProductEight (productBase fast_width input_separation)

open VG.Proof.Bignum.AArch64.SquareEight (BasicCtx PtrCtx HeadCtx AfterInternal output_ctx_mem clearPending_ok frame_header)

theorem initial_ptr_ctx {a : Nat} (ha : a < 8) (p : Ws × Nat) (s : State)
    (h : p.2 < blocks p.1 ∧ LoopCtx a p.1 p.2 s) :
    WP isa (.block (VG.Impl.Bignum.AArch64.ProductEight.outputPtr true a)) s (PtrCtx a true p) := by
  have hb : BasicCtx a p s := ⟨h.2.fast, h.1, h.2.ptr, h.2.count, h.2.zero⟩
  exact WP.mono (output_ctx_mem ha true p s hb) fun _ ht => ht.1

def headInternal : List Instr := (VG.Impl.Bignum.AArch64.WindowSparse.holes ++ VG.Impl.Bignum.AArch64.SquareEight.code) ++ [movi .x10 0]
def headSuffix (a : Nat) : List Instr := VG.Impl.Bignum.AArch64.ProductEight.outputPtr false a ++
  [ldh .x15 sW, .lsr .x .x15 .x15 3, .sub .x .x15 .x15 .x12]

theorem internal_ctx {a : Nat} (ha : a < 8) (ha1 : a ≠ Public.aAcc) (ha2 : a ≠ Public.aTmp) (p : Ws × Nat) (s : State) (h : PtrCtx a true p s) :
    WP isa (.block headInternal) s (AfterInternal a p) := by
  have hb := h.basic
  obtain ⟨he, _, _⟩ := fast_width hb.fast
  obtain ⟨mi, hg, hz⟩ := hb.fast.1
  have hsize : slot (8*blocks p.1) 8 ≤ p.1.Z := he.symm ▸ hz
  have hA : slot (8*blocks p.1) a+64*blocks p.1 ≤ p.1.Z := by
    have := slot_le (w := 8*blocks p.1) ha
    omega
  have hP : productBase (blocks p.1)+8*(16*blocks p.1+2) ≤ p.1.Z := by
    unfold productBase slot Public.aAcc at *
    omega
  have hj := hb.index
  apply WP.block_append
  have hsep := input_separation hb.fast ha1 ha2
  refine WP.mono (tile_ok (eA := slot (8*blocks p.1) a+64*p.2)
    (eT := productBase (blocks p.1)+128*p.2) hg.scr hb.ptr h.tptr hb.zero (by omega) (by omega) (by omega))
    fun t ⟨_, hto, kt⟩ => ?_
  have hout := hto.mono (o' := productBase (blocks p.1)) (n' := 8*(16*blocks p.1+2)) (by omega) (by omega)
  have hHt : Hdr t.mem p.1.B p.1.w mi := he ▸ frame_header hout (he.symm ▸ hg.hdr)
  refine WP.mono (clearPending_ok t) fun u ⟨⟨hu10, hum⟩, ku⟩ => ?_
  have kk := kt.trans ku
  exact ⟨⟨⟨⟨mi, ⟨hg.scr.congr kk.wr, (kk.gpr _ (by decide)).trans hg.x0, hum ▸ hHt⟩, hz⟩, hb.fast.2⟩,
    hj, (kk.gpr _ (by decide)).trans hb.ptr, (kk.gpr _ (by decide)).trans hb.count,
    (kk.gpr _ (by decide)).trans hb.zero⟩, hu10⟩

end VG.Proof.Bignum.AArch64.WindowSparse
