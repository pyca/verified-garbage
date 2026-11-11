module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.PrivPreCTB
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.Flat
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.PrivPreCTB
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.Flat
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# An RSA private key's precomputed values on PPC64LE: constant time

The code's list of programs (`privF`) is cut after each block that loads
values of the header (`PrivPreCTA.lean`, `PrivPreCTB.lean`): there the
registers the taint analysis needs public have values that the public data
fixes. `Precompute.core`, whose branches are on `n`, is
`vg_rsa_public_precompute`'s (`Pre.core_rel`), from `Pre.C1` for data the
public data fixes.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.PrivPre

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE (Two Pins two_post two_taint two_taintR At seg chain_cons chain_start
  at_zero_inv)

/-- The first block, the registers saved and the arguments stored, by the
taint analysis from the stack's first argument once loaded. -/
theorem front_rel : RelCT isa (Two C0) (.block (PrivPre.save ++ PrivPre.args)) fun _ _ => True := by
  unfold PrivPre.save
  simp only [List.append_assoc]
  exact RelCT.block_append (RelCT.seq (two_post (two_taint _ pins_C0 (by taint_decide)) fun _ _ h => loadS_L1 h)
    (two_taint _ pins_L1 (by taint_decide)))

theorem priv_run (d : PDat) (s : State) (h : C0 d s) : WP isa (Code.seqL privF) s fun _ => True :=
  let ⟨tr, t, e, _⟩ := fn_correct s h.1
  ⟨tr, t, exec_flat.mp e, trivial⟩

theorem relCT_to_flat {P Q : State → State → Prop} {c : Prog isa} (h : RelCT isa P c Q) :
    RelCT isa P (Code.seqL c.flat) Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ _ _ _ _ hp (exec_flat.mpr e₁) (exec_flat.mpr e₂)

/-- `Precompute.core`, as `vg_rsa_public_precompute`'s. -/
theorem core_seg : RelCT isa (Two (At C0 privF 96)) (seg privF 96 106) fun _ _ => True := by
  rw [show seg privF 96 106 = Code.seqL (Code.flat Precompute.core) from rfl]
  refine RelCT.mono (relCT_to_flat Pre.core_rel) (fun s₁ s₂ ⟨d, h₁, h₂, hsp⟩ => ?_) fun _ _ _ => trivial
  obtain ⟨s₀, c0, c1⟩ := at_C1 h₁
  obtain ⟨s₀', c0', c1'⟩ := at_C1 h₂
  exact ⟨pdOf s₀, c1, by rw [pdOf_eq c0 c0']; exact c1', hsp⟩

theorem fn_rel : RelCT isa (Two C0) PrivPre.code fun _ _ => True := by
  refine chain_start (chain_cons priv_run (m := 1) (by decide) ?_ ?_)
  · exact RelCT.mono (P := Two C0) (RelCT.seqL_single front_rel)
      (fun _ _ ⟨a, h₁, h₂, hsp⟩ => ⟨a, at_zero_inv h₁, at_zero_inv h₂, hsp⟩) fun _ _ h => h
  refine chain_cons priv_run (m := 5) (by decide) (two_taint _ pins1 (by taint_decide)) ?_
  refine chain_cons priv_run (m := 9) (by decide) (two_taint _ pins5 (by taint_decide)) ?_
  refine chain_cons priv_run (m := 17) (by decide) (two_taint _ pins9 (by taint_decide)) ?_
  refine chain_cons priv_run (m := 25) (by decide) (two_taint _ pins17 (by taint_decide)) ?_
  refine chain_cons priv_run (m := 33) (by decide) (two_taint _ pins25 (by taint_decide)) ?_
  refine chain_cons priv_run (m := 41) (by decide) (two_taint _ pins33 (by taint_decide)) ?_
  refine chain_cons priv_run (m := 50) (by decide) (two_taint _ pins41 (by taint_decide)) ?_
  refine chain_cons priv_run (m := 51) (by decide) (two_taint _ pins50 (by taint_decide)) ?_
  refine chain_cons priv_run (m := 96) (by decide) (two_taintR _ pins51 (by taint_decide_rel)) ?_
  refine chain_cons priv_run (m := 106) (by decide) core_seg ?_
  refine chain_cons priv_run (m := 113) (by decide) (two_taint _ pins106 (by taint_decide)) ?_
  refine chain_cons priv_run (m := 152) (by decide) (two_taintR _ pins113 (by taint_decide_rel)) ?_
  refine chain_cons priv_run (m := 191) (by decide) (two_taintR _ pins152 (by taint_decide_rel)) ?_
  exact two_taint _ pins191 (by taint_decide)

theorem fn_ct : ConstantTime isa fnContract.pre fnContract.pub PrivPre.code :=
  RelCT.constantTime (fn_rel.mono (fun s t ⟨hs, ht, ⟨hr, hsp, ha, hn⟩⟩ =>
    ⟨dataOf s, ⟨hs, rfl⟩, ⟨ht, by
      simp only [dataOf]
      rw [List.map_congr_left fun r h => (hr r h).symm, ha, hn]⟩, hsp⟩) fun _ _ h => h)

end VG.Proof.Bignum.PPC64LE.PrivPre
