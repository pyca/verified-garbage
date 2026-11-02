module

public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtPinsB
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Bignum.RISCV64.CrtPinsB
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint

/-!
# The RSA private-key operation on RISC-V: constant time

The code's list of programs (`crtF`) is cut after each block that loads
words of the header (`Reach.lean`): there the registers the taint analysis
needs public have values that the public data fixes (`CrtPins*.lean`).
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Crt

open VG VG.RISCV64 VG.RISCV64.Taint VG.Impl.Bignum.RISCV64 VG.Impl.Bignum.RISCV64.Crt
open VG.Proof.Bignum.RISCV64.Pre (Two two_taint)
open VG.Proof.Bignum.RISCV64 (At chain_cons chain_start at_zero_inv)

theorem fn_rel : RelCT isa (Two C0) crt fun _ _ => True := by
  refine chain_start (chain_cons crt_run (m := 1) (by decide) ?_ ?_)
  · refine RelCT.mono (P := Two C0)
      (VG.Proof.Bignum.RISCV64.RelCT.seqL_single (front_rel.mono (fun _ _ h => h) fun _ _ _ => trivial))
      (fun _ _ ⟨a, h₁, h₂, hsp⟩ => ⟨a, at_zero_inv h₁, at_zero_inv h₂, hsp⟩) fun _ _ h => h
  refine chain_cons crt_run (m := 5) (by decide) (two_taint _ pins1 (by taint_decide)) ?_
  refine chain_cons crt_run (m := 13) (by decide) (two_taint _ pins5 (by taint_decide)) ?_
  refine chain_cons crt_run (m := 21) (by decide) (two_taint _ pins13 (by taint_decide)) ?_
  refine chain_cons crt_run (m := 29) (by decide) (two_taint _ pins21 (by taint_decide)) ?_
  refine chain_cons crt_run (m := 37) (by decide) (two_taint _ pins29 (by taint_decide)) ?_
  refine chain_cons crt_run (m := 45) (by decide) (two_taint _ pins37 (by taint_decide)) ?_
  refine chain_cons crt_run (m := 46) (by decide) (two_taint _ pins45 (by taint_decide)) ?_
  refine chain_cons crt_run (m := 98) (by decide) (two_taint _ pins46 (by taint_decide)) ?_
  refine chain_cons crt_run (m := 106) (by decide) (two_taint _ pins98 (by taint_decide)) ?_
  refine chain_cons crt_run (m := 134) (by decide) (two_taint _ pins106 (by taint_decide)) ?_
  refine chain_cons crt_run (m := 136) (by decide) (two_taint _ pins134 (by taint_decide)) ?_
  refine chain_cons crt_run (m := 177) (by decide) (two_taint _ pins136 (by taint_decide)) ?_
  refine chain_cons crt_run (m := 205) (by decide) (two_taint _ pins177 (by taint_decide)) ?_
  refine chain_cons crt_run (m := 207) (by decide) (two_taint _ pins205 (by taint_decide)) ?_
  refine chain_cons crt_run (m := 248) (by decide) (two_taint _ pins207 (by taint_decide)) ?_
  refine chain_cons crt_run (m := 250) (by decide) (two_taint _ pins248 (by taint_decide)) ?_
  refine chain_cons crt_run (m := 251) (by decide) (two_taint _ pins250 (by taint_decide)) ?_
  refine chain_cons crt_run (m := 297) (by decide) (two_taint _ pins251 (by taint_decide)) ?_
  refine chain_cons crt_run (m := 303) (by decide) (two_taint _ pins297 (by taint_decide)) ?_
  refine chain_cons crt_run (m := 322) (by decide) (two_taint _ pins303 (by taint_decide)) ?_
  exact two_taint _ pins322 (by taint_decide)

theorem fn_ct : ConstantTime isa fnContract.pre fnContract.pub crt :=
  RelCT.constantTime (fn_rel.mono (fun s t ⟨hs, ht, ⟨hr, hsp, ha, hn⟩⟩ =>
    ⟨dataOf s, ⟨hs, rfl⟩, ⟨ht, by
      simp only [dataOf]
      rw [List.map_congr_left fun r h => (hr r h).symm, ha, hn]⟩, hsp⟩) fun _ _ h => h)

end VG.Proof.Bignum.RISCV64.Crt
