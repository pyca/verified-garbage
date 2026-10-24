module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCTBase
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Reach
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPinsB
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPinsB
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCTBase
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.Reach
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCorrect

/-!
# The RSA private-key operation on PPC64LE: constant time

The code's list of programs (`crtF`) is cut after each block that loads
words of the header (`Reach.lean`): there the registers the taint analysis
needs public have values that the public data fixes (`CrtPins*.lean`).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE (Two Pins two_post two_taint At seg chain_cons chain_start at_zero_inv)

theorem crt_run (d : List (BitVec 64) × List (BitVec 64) × List Byte) (s : State) (h : C0 d s) :
    WP isa (Code.seqL crtF) s fun _ => True :=
  let ⟨tr, t, e, _⟩ := fn_correct s h.1
  ⟨tr, t, exec_flat.mp e, trivial⟩


theorem fn_rel : RelCT isa (Two C0) crt fun _ _ => True := by
  refine chain_start (chain_cons crt_run (m := 1) (by decide) ?_ ?_)
  · refine RelCT.mono (P := Two C0) (RelCT.seqL_single (front_rel.mono (fun _ _ h => h) fun _ _ _ => trivial))
      (fun _ _ ⟨a, h₁, h₂, hsp⟩ => ⟨a, at_zero_inv h₁, at_zero_inv h₂, hsp⟩) fun _ _ h => h
  refine chain_cons crt_run (m := 5) (by decide) (two_taint _ pins1 (by taint_decide)) ?_
  refine chain_cons crt_run (m := 13) (by decide) (two_taint _ pins5 (by taint_decide)) ?_
  refine chain_cons crt_run (m := 21) (by decide) (two_taint _ pins13 (by taint_decide)) ?_
  refine chain_cons crt_run (m := 29) (by decide) (two_taint _ pins21 (by taint_decide)) ?_
  refine chain_cons crt_run (m := 37) (by decide) (two_taint _ pins29 (by taint_decide)) ?_
  refine chain_cons crt_run (m := 45) (by decide) (two_taint _ pins37 (by taint_decide)) ?_
  refine chain_cons crt_run (m := 46) (by decide) (two_taint _ pins45 (by taint_decide)) ?_
  refine chain_cons crt_run (m := 98) (by decide) (two_taint _ pins46 (by taint_decide)) ?_
  refine chain_cons crt_run (m := 150) (by decide) (two_taint _ pins98 (by taint_decide)) ?_
  refine chain_cons crt_run (m := 201) (by decide) (two_taint _ pins150 (by taint_decide)) ?_
  refine chain_cons crt_run (m := 204) (by decide) (two_taint _ pins201 (by taint_decide)) ?_
  refine chain_cons crt_run (m := 249) (by decide) (two_taint _ pins204 (by taint_decide)) ?_
  refine chain_cons crt_run (m := 255) (by decide) (two_taint _ pins249 (by taint_decide)) ?_
  refine chain_cons crt_run (m := 274) (by decide) (two_taint _ pins255 (by taint_decide)) ?_
  exact two_taint _ pins274 (by taint_decide)

theorem fn_ct : ConstantTime isa fnContract.pre fnContract.pub crt :=
  RelCT.constantTime (fn_rel.mono (fun s t ⟨hs, ht, ⟨hr, hsp, ha, hn⟩⟩ =>
    ⟨dataOf s, ⟨hs, rfl⟩, ⟨ht, by
      simp only [dataOf]
      rw [List.map_congr_left fun r h => (hr r h).symm, ha, hn]⟩, hsp⟩) fun _ _ h => h)

end VG.Proof.Bignum.PPC64LE.Crt
