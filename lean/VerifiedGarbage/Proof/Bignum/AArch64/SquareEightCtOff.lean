module

public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCtHead
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightRows
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightOffDiagonal
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtContext

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareEight
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.BlockedRedc (FastW blocks)
open VG.Proof.Bignum.AArch64.ProductEight (productBase fast_width input_separation)

def offCode : Prog isa := .ite (.nonzero .x .x15)
  (countLoop .x15 VG.Impl.Bignum.AArch64.ProductEight.offBlock) (.block [])
def tailFinish : List Instr := SquareEightRaw.finishCarry ++
  [.addImm .x .x8 .x8 64, .subImm .x .x12 .x12 1]

theorem off_ctx {a : Nat} (ha : a < 8) (ha1 : a ≠ Public.aAcc) (ha2 : a ≠ Public.aTmp)
    (p : Ws × Nat) (s : State) (h : HeadCtx a p s) : WP isa offCode s (BasicCtx a p) := by
  have hb := h.ptrs.basic
  obtain ⟨he, _, hk⟩ := fast_width hb.fast
  obtain ⟨mi, hg, hz⟩ := hb.fast.1
  have hsize : slot (8*blocks p.1) 8 ≤ p.1.Z := he.symm ▸ hz
  have hA := input_separation hb.fast ha1 ha2
  have hAZ : slot (8*blocks p.1) a+64*blocks p.1 ≤ p.1.Z := by
    have := slot_le (w := 8*blocks p.1) ha
    omega
  have hP : productBase (blocks p.1)+8*(16*blocks p.1+2) ≤ p.1.Z := by
    unfold productBase slot Public.aAcc at *
    omega
  have hj := hb.index
  refine WP.mono (offDiagonal_full hg.scr hb.ptr hb.zero h.pending h.ptrs.tptr h.ptrs.nptr h.iterations
    (by omega) hP (by omega) (by omega) (by omega) (by omega) (by omega)) fun t ⟨_, hto, kt⟩ => ?_
  have hout := hto.mono (o' := productBase (blocks p.1)) (n' := 8*(16*blocks p.1+2)) (by omega) (by omega)
  have hHt : Hdr t.mem p.1.B p.1.w mi := he ▸ frame_header hout (he.symm ▸ hg.hdr)
  exact ⟨⟨⟨mi, ⟨hg.scr.congr kt.wr, (kt.gpr _ (by decide)).trans hg.x0, hHt⟩, hz⟩, hb.fast.2⟩,
    hj, (kt.gpr _ (by decide)).trans hb.ptr, (kt.gpr _ (by decide)).trans hb.count,
    (kt.gpr _ (by decide)).trans hb.zero⟩

end VG.Proof.Bignum.AArch64.SquareEight
