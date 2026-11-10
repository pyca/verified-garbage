module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCTBase
import VerifiedGarbage.Proof.Bignum.PPC64LE.Reach
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPinsB
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPinsB
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCTBase
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.Reach
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCorrect
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPinsA
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
public import VerifiedGarbage.Proof.Framework.Flat

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

theorem crt_run (pc : Bool) (d : List (BitVec 64) × List (BitVec 64) × List Byte) (s : State) (h : C0 pc d s) :
    WP isa (Code.seqL (crtF pc)) s fun _ => True := by
  cases pc
  · let ⟨tr, t, e, _⟩ := fn_correct s h.1
    exact ⟨tr, t, exec_flat.mp e, trivial⟩
  · let ⟨tr, t, e, _⟩ := fn_correctP s h.1
    exact ⟨tr, t, exec_flat.mp e, trivial⟩

theorem fn_rel : RelCT isa (Two (C0 false)) crt fun _ _ => True := by
  refine chain_start (chain_cons (crt_run false) (m := 1) (by decide) ?_ ?_)
  · refine RelCT.mono (P := Two (C0 false)) (RelCT.seqL_single (front_rel.mono (fun _ _ h => h) fun _ _ _ => trivial))
      (fun _ _ ⟨a, h₁, h₂, hsp⟩ => ⟨a, at_zero_inv h₁, at_zero_inv h₂, hsp⟩) fun _ _ h => h
  refine chain_cons (crt_run false) (m := 5) (by decide) (two_taint _ pins1 (by taint_decide)) ?_
  refine chain_cons (crt_run false) (m := 13) (by decide) (two_taint _ pins5 (by taint_decide)) ?_
  refine chain_cons (crt_run false) (m := 21) (by decide) (two_taint _ pins13 (by taint_decide)) ?_
  refine chain_cons (crt_run false) (m := 29) (by decide) (two_taint _ pins21 (by taint_decide)) ?_
  refine chain_cons (crt_run false) (m := 37) (by decide) (two_taint _ pins29 (by taint_decide)) ?_
  refine chain_cons (crt_run false) (m := 45) (by decide) (two_taint _ pins37 (by taint_decide)) ?_
  refine chain_cons (crt_run false) (m := 46) (by decide) (two_taint _ pins45 (by taint_decide)) ?_
  refine chain_cons (crt_run false) (m := 91) (by decide) (two_taintR _ pins46 (by taint_decide_rel)) ?_
  refine chain_cons (crt_run false) (m := 100) (by decide) (two_taint _ pins91 (by taint_decide)) ?_
  refine chain_cons (crt_run false) (m := 124) (by decide) (two_taintR _ pins100 (by taint_decide_rel)) ?_
  refine chain_cons (crt_run false) (m := 148) (by decide) (two_taintR _ pins124 (by taint_decide_rel)) ?_
  refine chain_cons (crt_run false) (m := 172) (by decide) (two_taintR _ pins148 (by taint_decide_rel)) ?_
  refine chain_cons (crt_run false) (m := 195) (by decide) (two_taintR _ pins172 (by taint_decide_rel)) ?_
  refine chain_cons (crt_run false) (m := 202) (by decide) (two_taint _ pins195 (by taint_decide)) ?_
  refine chain_cons (crt_run false) (m := 252) (by decide) (two_taintR _ pins202 (by taint_decide_rel)) ?_
  refine chain_cons (crt_run false) (m := 258) (by decide) (two_taint _ pins252 (by taint_decide)) ?_
  refine chain_cons (crt_run false) (m := 271) (by decide) (two_taintR _ pins258 (by taint_decide_rel)) ?_
  exact two_taint _ pins271 (by taint_decide)

theorem fn_relP : RelCT isa (Two (C0 true)) crtP fun _ _ => True := by
  refine chain_start (chain_cons (crt_run true) (m := 1) (by decide) ?_ ?_)
  · refine RelCT.mono (P := Two (C0 true)) (RelCT.seqL_single (front_rel.mono (fun _ _ h => h) fun _ _ _ => trivial))
      (fun _ _ ⟨a, h₁, h₂, hsp⟩ => ⟨a, at_zero_inv h₁, at_zero_inv h₂, hsp⟩) fun _ _ h => h
  refine chain_cons (crt_run true) (m := 5) (by decide) (two_taint _ pins1 (by taint_decide)) ?_
  refine chain_cons (crt_run true) (m := 13) (by decide) (two_taint _ pins5 (by taint_decide)) ?_
  refine chain_cons (crt_run true) (m := 21) (by decide) (two_taint _ pins13 (by taint_decide)) ?_
  refine chain_cons (crt_run true) (m := 29) (by decide) (two_taint _ pins21 (by taint_decide)) ?_
  refine chain_cons (crt_run true) (m := 37) (by decide) (two_taint _ pins29 (by taint_decide)) ?_
  refine chain_cons (crt_run true) (m := 45) (by decide) (two_taint _ pins37 (by taint_decide)) ?_
  refine chain_cons (crt_run true) (m := 46) (by decide) (two_taint _ pins45 (by taint_decide)) ?_
  refine chain_cons (crt_run true) (m := 91) (by decide) (two_taintR _ pins46 (by taint_decide_rel)) ?_
  refine chain_cons (crt_run true) (m := 100) (by decide) (two_taint _ pins91 (by taint_decide)) ?_
  refine chain_cons (crt_run true) (m := 118) (by decide) (two_taintR _ pins100 (by taint_decide_rel)) ?_
  refine chain_cons (crt_run true) (m := 142) (by decide) (two_taintR _ pins124 (by taint_decide_rel)) ?_
  refine chain_cons (crt_run true) (m := 160) (by decide) (two_taintR _ pins148 (by taint_decide_rel)) ?_
  refine chain_cons (crt_run true) (m := 183) (by decide) (two_taintR _ pins172 (by taint_decide_rel)) ?_
  refine chain_cons (crt_run true) (m := 190) (by decide) (two_taint _ pins195 (by taint_decide)) ?_
  refine chain_cons (crt_run true) (m := 234) (by decide) (two_taintR _ pins202 (by taint_decide_rel)) ?_
  refine chain_cons (crt_run true) (m := 240) (by decide) (two_taint _ pins252 (by taint_decide)) ?_
  refine chain_cons (crt_run true) (m := 253) (by decide) (two_taintR _ pins258 (by taint_decide_rel)) ?_
  exact two_taint _ pins271 (by taint_decide)

theorem fn_ct : ConstantTime isa fnContract.pre fnContract.pub crt :=
  RelCT.constantTime (fn_rel.mono (fun s t ⟨hs, ht, ⟨hr, hsp, ha, hn⟩⟩ =>
    ⟨dataOf false s, ⟨hs, rfl⟩, ⟨ht, by
      simp only [dataOf, argRegsG, Bool.false_eq_true, ↓reduceIte]
      rw [List.map_congr_left fun r h => (hr r h).symm, ha, hn]⟩, hsp⟩) fun _ _ h => h)

theorem fn_ctP : ConstantTime isa fnContractP.pre fnContractP.pub crtP :=
  RelCT.constantTime (fn_relP.mono (fun s t ⟨hs, ht, ⟨⟨hr, hsp, ha, hn⟩, h12⟩⟩ =>
    ⟨dataOf true s, ⟨hs, rfl⟩, ⟨ht, by
      simp only [dataOf, argRegsG, ↓reduceIte, List.map_append, List.map_cons, List.map_nil, h12]
      rw [List.map_congr_left fun r h => (hr r h).symm, ha, hn]⟩, hsp⟩) fun _ _ h => h)

end VG.Proof.Bignum.PPC64LE.Crt
