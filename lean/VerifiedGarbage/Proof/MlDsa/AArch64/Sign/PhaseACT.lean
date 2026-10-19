module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Rel
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Rel
import Mathlib.Tactic.Conv
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.Conv
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Ball
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejBounded
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
import VerifiedGarbage.Proof.MlDsa.Round.Decompose
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
import VerifiedGarbage.Proof.MlKem.AArch64.Shared
import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Proof.MlKem.Compress
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.MlKem.KPke
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Squeeze
import VerifiedGarbage.Proof.Sha3.Arith
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Ball
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejBounded
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
meta import VerifiedGarbage.Proof.MlDsa.Round.Decompose
meta import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
meta import VerifiedGarbage.Proof.MlDsa.Verify.Mem
meta import VerifiedGarbage.Proof.MlKem.AArch64.Common
meta import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
meta import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
meta import VerifiedGarbage.Proof.MlKem.AArch64.Shared
meta import VerifiedGarbage.Proof.MlKem.AArch64.Vec
meta import VerifiedGarbage.Proof.MlKem.Compress
meta import VerifiedGarbage.Proof.MlKem.Encode
meta import VerifiedGarbage.Proof.MlKem.KPke
meta import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Absorb
meta import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
meta import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Squeeze
meta import VerifiedGarbage.Proof.Sha3.Arith

/-!
# ML-DSA signing on AArch64: `ExpandA` leaks only `ρ`

Two runs of `ExpandA` with the same `ρ` compute the same results of
`vg_mldsa_rej_ntt_poly`, so they agree on `x24` (`RA`), and leak the same
(`expandA_tr`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- Two runs of `ExpandA` after `e` entries, with the same `x24`. -/
abbrev RA (p : Params) (D e : Nat) : State → State → Prop :=
  RR p D (fun σ s => IA p D σ e s) fun x y => x.gpr .x24 = y.gpr .x24

theorem callE_ok' {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {σ : State} {e : Nat}
    (he : eChk p e = true) {s : State} (h : IA p D σ e s) (hs : bytesAt s.mem (pa s (sc oRS)) 34 = seedE p σ e) :
    WP isa (rejCallAt P (pS (aBase p + e))) s fun s' => JE p D e σ s' ∧ s'.gpr .x24 = s.gpr .x24 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hc, _, _⟩ := eChk_spec he
  refine WP.mono (rejCall_ok hP h.st.lay hc) fun s' ⟨hP3, hcs3, hred, hout, hmax⟩ =>
    ⟨⟨s, h, hP3, hcs3, hred, ?_, ?_⟩, hcs3⟩
  · rw [← hs]; exact hout
  · rw [← hs]; exact hmax

theorem blkE_taint (p : Params) (e : Nat) :
    (taint.check (AArch64.Taint.ofRegs bases) (.block (blkE p e)) (.block [])).isSome = true := by
  dsimp only [blkE, setB]; rfl

theorem sampleE_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {e : Nat} (he : eChk p e = true) :
    RelCT isa (RA p D e) (sampleE P p e) (RA p D (e + 1)) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hc, _, _⟩ := eChk_spec he
  rw [sampleE_eq]
  refine RelCT.seq (R := RR p D (fun σ s => IA p D σ e s ∧ bytesAt s.mem (pa s (sc oRS)) 34 = seedE p σ e)
    fun x y => x.gpr .x24 = y.gpr .x24) ?_ (RelCT.seq (R := RR p D (JE p D e)
      fun x y => x.gpr .x24 = y.gpr .x24 ∧ (x.gpr .x0).setWidth 32 = (y.gpr .x0).setWidth 32) ?_ ?_)
  · exact stepRR (F := fun s s' => s'.gpr .x24 = s.gpr .x24) (fun σ s _ h => blkE_ok he h)
      (lrel_tr (fun x y h => h.lrel fun _ _ h => h.st) (blkE_taint p e)) fun x y x' y' h fx fy _ => by rw [fx, fy, h.2]
  · refine stepRR (F := fun s s' => s'.gpr .x24 = s.gpr .x24) (fun σ s _ h => callE_ok' hP he h.1 h.2)
      ((rejCall_tr hP hc).mono (fun x y h => ⟨h.lrel fun _ _ h => h.1.st, ?_⟩) fun _ _ h => h)
      fun x y x' y' h fx fy q => ⟨by rw [fx, fy, h.2], q⟩
    obtain ⟨⟨σ₁, σ₂, _, _, hpub, ⟨_, s₁⟩, ⟨_, s₂⟩⟩, _⟩ := h
    rw [s₁, s₂, seedE, seedE, pub_rho hpub]
  · refine stepRR (F := fun s s' => s'.gpr .x24 =
        BitVec.setWidth 64 ((s.gpr .x24).setWidth 32 &&& (s.gpr .x0).setWidth 32))
      (fun σ s _ h => WP.conj (andE_ok he h) (WP.mono (and24_ok s) fun _ h => h.2))
      (lrel_tr (fun x y h => h.lrel fun _ σ h => ?_) (by taint_decide)) fun x y x' y' h fx fy _ => by rw [fx, fy, h.2.1, h.2.2]
    obtain ⟨s₀, h₀, hP₀, -⟩ := h
    exact h₀.st.step hP₀ (eChk_spec he).2.2.1



end VG.Proof.MlDsa.AArch64.Sign
