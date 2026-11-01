module

public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.CTMain
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Code
import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Ffdh.Contract
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.CTMain
meta import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Code
meta import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Ffdh.Contract

/-!
# An FFDH parameter candidate on AArch64: constant time, and `Verified`

Every value of the candidate is public (`pcPub` fixes the arguments and the
octets of `rand`), so runs that agree on them agree on `ppOf`, and leak the
same (`code_constantTime`): the entry, the zeros to `out` and the length
check from the arguments, then `main` (`main_ct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MillerRabin.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

/-- A state the contract allows, with the public data `p`. -/
def P0 (p : PP) (s : State) : Prop := pcPre s ∧ ppOf s = p

/-- After the entry. -/
def P2 (p : PP) (t : State) : Prop := ∃ s, P0 p s ∧ EntryPost s t

/-- After the zeros to `out`. -/
def P2' (p : PP) (t : State) : Prop := ∃ s t₁, P0 p s ∧ EntryPost s t₁ ∧ Zeroed s t₁ t

/-- After the length check. -/
def P3 (p : PP) (t : State) : Prop := ∃ s, P0 p s ∧ Front s t

/-- The registers `zeroOut`'s loop needs pinned. -/
def zoVal' (ptr : Addr) (len : Nat) : Reg → BitVec 64
  | .x1 => ptr
  | .x2 => BitVec.ofNat 64 len
  | _ => 0

theorem entry_ct : RelCT isa (Two P0) (.block entry) (Two P2) :=
  two_piece [.x7] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (congrArg PP.B h₁.2).trans (congrArg PP.B h₂.2).symm)
    (by taint_decide) fun p s h => WP.mono (entry_ok (pctx_of h.1)) fun t he => ⟨s, h, he⟩

theorem zeros_ct : RelCT isa (Two P2) (zeroOut kOut kLen) (Two P2') :=
  pin_ct [.x0] [.x1, .x2] (fun p => zoVal' p.op p.L)
    (fun p s₁ s₂ ⟨σ₁, c₁, h₁⟩ ⟨σ₂, c₂, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h₁.x0, h₂.x0, show σ₁.gpr .x7 = p.B from congrArg PP.B c₁.2, show σ₂.gpr .x7 = p.B from congrArg PP.B c₂.2])
    (by taint_decide)
    (fun p t ⟨s, c, he⟩ => by
      have k := pctx_of c.1
      have hs := k.hs.congr he.keep.wr
      have hn := hs.nowrap
      have hZ : 128 * (((s.gpr .x3).toNat + 7) / 8) + 256 ≤ (stackArg s 0).toNat * 8 := k.dims.z
      have hL : (s.gpr .x1).toNat = ((s.gpr .x3).toNat + 7) / 8 := k.len
      have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off (s.gpr .x7) (8 * i)) 8 := fun i hi => hs.ld (by omega)
      have hop : s.gpr .x0 = p.op := congrArg PP.op c.2
      have hpL : BitVec.ofNat 64 p.L = s.gpr .x1 := by
        rw [← c.2]; show BitVec.ofNat 64 (((s.gpr .x3).toNat + 7) / 8) = _; rw [← hL, ofNat_toNat64]
      refine WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun t' => t'.gpr .x1 = p.op ∧
          t'.gpr .x2 = BitVec.ofNat 64 p.L) (by
        brun [he.x0, hdr_enc (show kOut < 32 by decide), hdr_enc (show kLen < 32 by decide), hl kOut (by decide),
          hl kLen (by decide), he.args.out, he.args.len, hop, hpL]) (by decide) (by decide) (by decide +kernel))
        fun t' ⟨⟨h1, h2⟩, _⟩ r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h1
      · exact h2)
    (by taint_decide) fun p t ⟨s, c, he⟩ => WP.mono (zeros_ok (pctx_of c.1) he) fun t' hz => ⟨s, t, c, he, hz⟩

theorem lenCheck_ct : RelCT isa (Two P2') (.block ([ldh .x3 kRandLen, ldh .x4 kLen] ++ geFlag)) (Two P3) :=
  two_piece [.x0] (fun p s₁ s₂ ⟨σ₁, _, c₁, e₁, z₁⟩ ⟨σ₂, _, c₂, e₂, z₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [(z₁.keep.gpr .x0 (by decide)).trans e₁.x0, (z₂.keep.gpr .x0 (by decide)).trans e₂.x0,
      show σ₁.gpr .x7 = p.B from congrArg PP.B c₁.2, show σ₂.gpr .x7 = p.B from congrArg PP.B c₂.2])
    (by taint_decide) fun p t ⟨s, t₁, c, he, hz⟩ => WP.mono (lenCheck_ok (pctx_of c.1) he hz) fun t' hf => ⟨s, c, hf⟩

theorem P3.x5 {p : PP} {t : State} (h : P3 p t) :
    t.gpr .x5 = BitVec.ofNat 64 (decide (p.L ≤ p.r.length)).toNat := by
  obtain ⟨s, c, hf⟩ := h
  rw [hf.x5, ← c.2]
  have hL := (pctx_of c.1).len
  show _ = BitVec.ofNat 64 (decide ((ppOf s).L ≤ (pcRand s).length)).toNat
  rw [← hL, pcRand_length]

theorem P3.m0 {p : PP} {t : State} (h : P3 p t) (hb : isa.eval (.zero .x .x5) t = some false) : M0 p t := by
  have hx := h.x5
  obtain ⟨s, c, hf⟩ := h
  have k := pctx_of c.1
  rw [eval_zero, hx] at hb
  have hle : p.L ≤ p.r.length := by
    revert hb; cases hd : decide (p.L ≤ p.r.length)
    · intro hb; cases hb
    · intro _; simpa using hd
  have hL : (s.gpr .x1).toNat = (ppOf s).L := k.len
  rw [← c.2] at hle ⊢
  exact ⟨ph_of k hf, by show word t.mem (s.gpr .x7) _ = _; rw [hf.args.used, ← hL, ofNat_toNat64], hle⟩

/-- `vg_ffdh_parameter_candidate` leaks the same in runs with the same
public data. -/
theorem code_ct (M : Mont) (R : Kernel) :
    RelCT isa (Two P0) (VG.Impl.Ffdh.AArch64.ParameterCandidate.code M.mm R.run) fun _ _ => True := by
  unfold VG.Impl.Ffdh.AArch64.ParameterCandidate.code
  simp only [seqs]
  refine RelCT.seq entry_ct (RelCT.seq zeros_ct (RelCT.seq lenCheck_ct ?_))
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.x5, h₂.x5]) ?_ ?_
  · have e : finNone = .block (([movi .x3 0, ldh .x2 kUsedP] : List Instr) ++ [st .x3 .x2, movi .x0 0]) := rfl
    rw [e]
    refine (RelCT.block_append (pin_ct (Ψ := fun _ _ => True) [.x0] [.x2] (fun p _ => p.up)
      (fun p s₁ s₂ ⟨⟨σ₁, c₁, f₁⟩, _⟩ ⟨⟨σ₂, c₂, f₂⟩, _⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [f₁.x0, f₂.x0]; exact (congrArg PP.B c₁.2).trans (congrArg PP.B c₂.2).symm)
      (by taint_decide) ?_ (by taint_decide) ?_)).mono (fun _ _ h => h) fun _ _ _ => trivial
    · rintro p t ⟨⟨s, c, hf⟩, _⟩
      have k := pctx_of c.1
      have hph := ph_of k hf
      rw [c.2] at hph
      have hs := hph.scr
      have hn := hs.nowrap
      have hZ := hph.dims.z
      have hl : InRegions (t.rd ++ t.wr) (off p.B (8 * kUsedP)) 8 := hs.ld (by simp only [kUsedP, sFn, PP.L] at *; omega)
      refine WP.mono (WP.keep [.x2, .x3] (Q := fun t' => t'.gpr .x2 = p.up) (by
        brun [hph.x0, hdr_enc (show kUsedP < 32 by decide), hl, hph.args.usedP]) (by decide) (by decide)
        (by decide +kernel)) fun t' h2 r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr; exact h2.1
    · rintro p t ⟨⟨s, c, hf⟩, hb⟩
      have k := pctx_of c.1
      have hlt : (pcRand s).length < (s.gpr .x1).toNat := by
        have hx := (show P3 p t from ⟨s, c, hf⟩).x5
        rw [eval_zero, hx] at hb
        have hL := k.len
        rw [← c.2] at hb
        revert hb
        cases hd : decide ((ppOf s).L ≤ (ppOf s).r.length)
        · intro _; simp only [decide_eq_false_iff_not, Nat.not_le] at hd; rw [hL]; exact hd
        · intro hb; cases hb
      have hZ : 128 * (((s.gpr .x3).toNat + 7) / 8) + 256 ≤ (stackArg s 0).toNat * 8 := k.dims.z
      exact WP.seq_iff.mpr (WP.block_append_iff.mp (WP.mono (finNone_ok (up := s.gpr .x2) (k.hs.congr hf.keep.wr)
        hf.x0 (show 8 * 32 ≤ (stackArg s 0).toNat * 8 by omega) hf.args.usedP (k.ou.congr hf.keep.wr).upw)
        fun _ _ => trivial))
  · exact two_map id (fun p t h => h.1.m0 h.2) (main_ct M R)

theorem P0.self {s : State} (h : pcPre s) : P0 (ppOf s) s := ⟨h, rfl⟩

/-- Runs that agree on the public data agree on `ppOf`. -/
theorem ppOf_eq {s₁ s₂ : State} (hp : pcPub s₁ s₂) : ppOf s₂ = ppOf s₁ := by
  obtain ⟨_, hr, h0, h1, h2, h3, h4, h5, h6, h7, ha⟩ := hp
  have hrr : pcRand s₁ = pcRand s₂ := VG.Proof.RsaKeyGen.map_toNat_inj hr
  simp only [ppOf, ← h0, ← h2, ← h3, ← h4, ← h5, ← h7, ← ha, ← hrr]

/-- `vg_ffdh_parameter_candidate` is constant time: its leak depends only
on the public data. -/
theorem code_constantTime (M : Mont) (R : Kernel) :
    ConstantTime isa pcPre pcPub (VG.Impl.Ffdh.AArch64.ParameterCandidate.code M.mm R.run) :=
  RelCT.constantTime ((code_ct M R).mono (fun s₁ _ ⟨h₁, h₂, hp⟩ =>
    ⟨ppOf s₁, P0.self h₁, ⟨h₂, ppOf_eq hp⟩, hp.1⟩) fun _ _ h => h)

/-- `vg_ffdh_parameter_candidate`, against its contract. -/
theorem pc_verified (M : Mont) (R : Kernel) :
    Verified target (VG.Impl.Ffdh.AArch64.ParameterCandidate.code M.mm R.run)
      (Proof.Ffdh.parameterCandidateContract abi) :=
  Verified.of_correct (code_correct M R) (code_constantTime M R) pc_implies

end VG.Proof.Ffdh.AArch64.ParameterCandidate
