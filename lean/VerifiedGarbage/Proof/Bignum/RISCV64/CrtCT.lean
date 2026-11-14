module

public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtPinsB
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Bignum.RISCV64.CrtPinsB
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint

/-!
# The RSA private-key operation on RISC-V: constant time

`crt` and `crtP`: the code's list of programs (`crtF`) is cut after each block that loads
words of the header (`Reach.lean`): there the registers the taint analysis
needs public have values that the public data fixes (`CrtPins*.lean`).
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Crt

open VG VG.RISCV64 VG.RISCV64.Taint VG.Impl.Bignum.RISCV64 VG.Impl.Bignum.RISCV64.Crt
open VG.Proof.Bignum.RISCV64.Pre (Two two_taint)
open VG.Proof.Bignum.RISCV64 (At chain_cons chain_start at_zero_inv)

theorem fn_rel : RelCT isa (Two (C0 false)) crt fun _ _ => True := by
  refine chain_start (chain_cons (crt_run false) (m := 1) (by decide) ?_ ?_)
  · refine RelCT.mono (P := Two (C0 false))
      (VG.Proof.Bignum.RISCV64.RelCT.seqL_single (front_rel.mono (fun _ _ h => h) fun _ _ _ => trivial))
      (fun _ _ ⟨a, h₁, h₂, hsp⟩ => ⟨a, at_zero_inv h₁, at_zero_inv h₂, hsp⟩) fun _ _ h => h
  refine chain_cons (crt_run false) (m := 5) (by decide) (two_taint _ pins1 (by taint_decide)) ?_
  refine chain_cons (crt_run false) (m := 13) (by decide) (two_taint _ pins5 (by taint_decide)) ?_
  refine chain_cons (crt_run false) (m := 21) (by decide) (two_taint _ pins13 (by taint_decide)) ?_
  refine chain_cons (crt_run false) (m := 29) (by decide) (two_taint _ pins21 (by taint_decide)) ?_
  refine chain_cons (crt_run false) (m := 37) (by decide) (two_taint _ pins29 (by taint_decide)) ?_
  refine chain_cons (crt_run false) (m := 45) (by decide) (two_taint _ pins37 (by taint_decide)) ?_
  refine chain_cons (crt_run false) (m := 46) (by decide) (two_taint _ pins45 (by taint_decide)) ?_
  refine chain_cons (crt_run false) (m := 98) (by decide) (two_taint _ pins46 (by taint_decide)) ?_
  refine chain_cons (crt_run false) (m := 106) (by decide) (two_taint _ pins98 (by taint_decide)) ?_
  refine chain_cons (crt_run false) (m := 134) (by decide) (two_taint _ pins106 (by taint_decide)) ?_
  refine chain_cons (crt_run false) (m := 136) (by decide) (two_taint _ pins134 (by taint_decide)) ?_
  refine chain_cons (crt_run false) (m := 177) (by decide) (two_taint _ pins136 (by taint_decide)) ?_
  refine chain_cons (crt_run false) (m := 205) (by decide) (two_taint _ pins177 (by taint_decide)) ?_
  refine chain_cons (crt_run false) (m := 207) (by decide) (two_taint _ pins205 (by taint_decide)) ?_
  refine chain_cons (crt_run false) (m := 248) (by decide) (two_taint _ pins207 (by taint_decide)) ?_
  refine chain_cons (crt_run false) (m := 254) (by decide) (two_taint _ pins248 (by taint_decide)) ?_
  refine chain_cons (crt_run false) (m := 275) (by decide) (two_taint _ pins254 (by taint_decide)) ?_
  refine chain_cons (crt_run false) (m := 305) (by decide) (two_taint _ pins275 (by taint_decide)) ?_
  refine chain_cons (crt_run false) (m := 311) (by decide) (two_taint _ pins305 (by taint_decide)) ?_
  refine chain_cons (crt_run false) (m := 330) (by decide) (two_taint _ pins311 (by taint_decide)) ?_
  exact two_taint _ pins330 (by taint_decide)

theorem fn_relP : RelCT isa (Two (C0 true)) crtP fun _ _ => True := by
  refine chain_start (chain_cons (crt_run true) (m := 1) (by decide) ?_ ?_)
  · refine RelCT.mono (P := Two (C0 true))
      (VG.Proof.Bignum.RISCV64.RelCT.seqL_single (front_rel.mono (fun _ _ h => h) fun _ _ _ => trivial))
      (fun _ _ ⟨a, h₁, h₂, hsp⟩ => ⟨a, at_zero_inv h₁, at_zero_inv h₂, hsp⟩) fun _ _ h => h
  refine chain_cons (crt_run true) (m := 5) (by decide) (two_taint _ pins1 (by taint_decide)) ?_
  refine chain_cons (crt_run true) (m := 13) (by decide) (two_taint _ pins5 (by taint_decide)) ?_
  refine chain_cons (crt_run true) (m := 21) (by decide) (two_taint _ pins13 (by taint_decide)) ?_
  refine chain_cons (crt_run true) (m := 29) (by decide) (two_taint _ pins21 (by taint_decide)) ?_
  refine chain_cons (crt_run true) (m := 37) (by decide) (two_taint _ pins29 (by taint_decide)) ?_
  refine chain_cons (crt_run true) (m := 45) (by decide) (two_taint _ pins37 (by taint_decide)) ?_
  refine chain_cons (crt_run true) (m := 46) (by decide) (two_taint _ pins45 (by taint_decide)) ?_
  refine chain_cons (crt_run true) (m := 75) (by decide) (two_taint _ pins46 (by taint_decide)) ?_
  refine chain_cons (crt_run true) (m := 83) (by decide) (two_taint _ pins98 (by taint_decide)) ?_
  refine chain_cons (crt_run true) (m := 106) (by decide) (two_taint _ pins106 (by taint_decide)) ?_
  refine chain_cons (crt_run true) (m := 108) (by decide) (two_taint _ pins134 (by taint_decide)) ?_
  refine chain_cons (crt_run true) (m := 149) (by decide) (two_taint _ pins136 (by taint_decide)) ?_
  refine chain_cons (crt_run true) (m := 172) (by decide) (two_taint _ pins177 (by taint_decide)) ?_
  refine chain_cons (crt_run true) (m := 174) (by decide) (two_taint _ pins205 (by taint_decide)) ?_
  refine chain_cons (crt_run true) (m := 215) (by decide) (two_taint _ pins207 (by taint_decide)) ?_
  refine chain_cons (crt_run true) (m := 221) (by decide) (two_taint _ pins248 (by taint_decide)) ?_
  refine chain_cons (crt_run true) (m := 242) (by decide) (two_taint _ pins254 (by taint_decide)) ?_
  refine chain_cons (crt_run true) (m := 272) (by decide) (two_taint _ pins275 (by taint_decide)) ?_
  refine chain_cons (crt_run true) (m := 278) (by decide) (two_taint _ pins305 (by taint_decide)) ?_
  refine chain_cons (crt_run true) (m := 297) (by decide) (two_taint _ pins311 (by taint_decide)) ?_
  exact two_taint _ pins330 (by taint_decide)

theorem fn_ct : ConstantTime isa fnContract.pre fnContract.pub crt :=
  RelCT.constantTime (fn_rel.mono (fun s t ⟨hs, ht, ⟨hr, hsp, ha, hn⟩⟩ =>
    ⟨dataOf false s, ⟨hs, rfl⟩, ⟨ht, by
      simp only [dataOf, argRegsG, Bool.false_eq_true, ↓reduceIte]
      rw [List.map_congr_left fun r h => (hr r h).symm, ha, hn]⟩, hsp⟩) fun _ _ h => h)

theorem fn_ctP : ConstantTime isa fnContractP.pre fnContractP.pub crtP :=
  RelCT.constantTime (fn_relP.mono (fun s t ⟨hs, ht, ⟨⟨hr, hsp, ha, hn⟩, h1⟩⟩ =>
    ⟨dataOf true s, ⟨hs, rfl⟩, ⟨ht, by
      simp only [dataOf, argRegsG, ↓reduceIte, List.map_append, List.map_cons, List.map_nil, h1]
      rw [List.map_congr_left fun r h => (hr r h).symm, ha, hn]⟩, hsp⟩) fun _ _ h => h)

end VG.Proof.Bignum.RISCV64.Crt
