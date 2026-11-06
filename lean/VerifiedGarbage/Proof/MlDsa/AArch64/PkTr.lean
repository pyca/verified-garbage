module

public import VerifiedGarbage.Impl.MlDsa.AArch64.PkTr
public import VerifiedGarbage.Spec.MlDsa.PkTr
public import VerifiedGarbage.Proof.Sha3.AArch64.Variant
public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Hash
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Top
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Lay
import VerifiedGarbage.Proof.Sha3.AArch64.Callers.Sums
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.TaintSumGeneric
public import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Impl.MlDsa.AArch64.PkTr
meta import VerifiedGarbage.Proof.Sha3.AArch64.Callers.Sums
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.RegSet

/-!
# ML-DSA on AArch64: `vg_mldsa*_pk_tr`

Untrusted: everything here is checked by Lean. `pkTrWith v.callee p` meets
`pkTrContract p AArch64.abi 16` for any Keccak backend `v` (`pkTr_verified`):
after `enter` (`x3 ← scratch`), key generation's prologue keeps `pk`, `tr` and
`scratch` in `x25`, `x26` and `x28` (`KeyGen.pro_ok`), where the contract's
precondition gives the layout of the buffers (`trLay`); the sponge writes
`H(pk, 64)` to `tr` (`shake_ok`), and key generation's epilogue restores the
caller's registers (`KeyGen.epi_ok`). It is constant time for every backend,
from the summaries of the sponge's calls (`pkTr_taint`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.PkTr

open VG VG.AArch64 VG.Proof.MlDsa.AArch64
open VG.Impl.MlDsa.AArch64.PkTr
open VG.Spec.MlDsa (Params scratchWords mlDsa44 mlDsa65 mlDsa87)
open VG.Spec.Sha3 (bytesAt)

/-- Constant time, for any Keccak backend `c` with the summaries of its calls. -/
theorem pkTr_taint (c : Impl.Sha3.AArch64.Callee) (hS : Taint.AllOk VectorTaint.taint (Proof.Sha3.AArch64.Callers.sums c)) :
    ∀ p : Params, (p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) →
      ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2]) (pkTrWith c p) h).isSome = true := by
  intro p hp
  rcases hp with rfl | rfl | rfl <;>
    taint_decide_generic c := Impl.Sha3.AArch64.Callee.scalar using hS

/-! ## The layout -/

/-- `pk` (read), in `x25`. -/
abbrev trR (p : Params) : List (Reg × Nat) := [(.x25, p.pkLen)]
/-- `scratch` and `tr` (written), in `x28` and `x26`. -/
abbrev trW (p : Params) : List (Reg × Nat) := [(.x28, scratchWords p * 8), (.x26, 64)]

theorem below_of_resv3 {S : Nat} {sp : Addr} {a b c : Region}
    (h : Sig.conj ((stackBelow sp S).map fun r => [r.Disjoint a, r.Disjoint b, r.Disjoint c]).flatten) :
    (below sp S).Disjoint a ∧ (below sp S).Disjoint b ∧ (below sp S).Disjoint c := by
  rcases S with _ | S
  · refine ⟨?_, ?_, ?_⟩ <;> exact fun x h _ => by simp [Region.Contains] at h
  · simp only [stackBelow, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
      Sig.conj_cons] at h
    exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem small {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    p.pkLen < 2 ^ 32 ∧ scratchWords p * 8 < 2 ^ 32 := by
  rcases hp with rfl | rfl | rfl <;> decide

/-- After the prologue, the contract's precondition (on the state `σ` before
`enter`, which is `σ₁` but for `x3`) gives the layout. -/
theorem trLay {p : Params} (hp' : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) {S : Nat} {σ σ₁ s : State}
    (hpre : (Spec.MlDsa.pkTrContract p AArch64.abi S).pre σ) (o : Proof.MlKem.AArch64.Only [.x3] σ σ₁)
    (h : KeyGen.Top σ₁ s) (e3 : σ₁.gpr .x3 = σ.gpr .x2) : Lay S (trR p) (trW p) s := by
  sig_pre [Spec.MlDsa.pkTrContract, Spec.MlDsa.pkTrSig, AArch64.abi, VG.AArch64.argRegs] at hpre
  obtain ⟨hwf, hrd, hwr, d01, d02, d12, hres, n0, n1, n2⟩ := hpre
  obtain ⟨k0, k1, k2⟩ := below_of_resv3 hres
  have hS : S ≤ σ.sp.toNat := KeyGen.le_of_wfP hwf
  have hsm := small hp'
  have e25 : s.gpr .x25 = σ.gpr .x0 := by rw [h.x25, o.gpr _ (by decide)]
  have e26 : s.gpr .x26 = σ.gpr .x1 := by rw [h.x26, o.gpr _ (by decide)]
  have e28 : s.gpr .x28 = σ.gpr .x2 := by rw [h.x28, e3]
  have esp : s.sp = σ.sp := by rw [h.sp, o.sp]
  have erd : s.rd = σ.rd := by rw [h.rd, o.rd]
  have ewr : s.wr = σ.wr := by rw [h.wr, o.wr]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, by rw [esp]; exact hS⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl)
    exacts [hsm.1, hsm.2, by decide]
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl) b' (rfl | rfl | rfl) hne hw <;>
      first
        | exact absurd rfl hne
        | simp only [e25, e26, e28]
          first
            | with_reducible assumption
            | exact Region.Disjoint.symm (by assumption)
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl) <;> simp only [e25, e26, e28, esp] <;> with_reducible assumption
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl) <;> simp only [e25, e26, e28] <;> with_reducible assumption
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl) <;> simp only [e25, e26, e28, erd, ewr]
    · exact KeyGen.inR_self (r := ⟨σ.gpr .x0, p.pkLen⟩) (by rw [hrd]; simp)
    · exact KeyGen.inR_self (r := ⟨σ.gpr .x2, scratchWords p * 8⟩) (by rw [hwr]; simp)
    · exact KeyGen.inR_self (r := ⟨σ.gpr .x1, 64⟩) (by rw [hwr]; simp)
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl) <;> simp only [e26, e28, ewr]
    · exact KeyGen.inR_self (r := ⟨σ.gpr .x2, scratchWords p * 8⟩) (by rw [hwr]; simp)
    · exact KeyGen.inR_self (r := ⟨σ.gpr .x1, 64⟩) (by rw [hwr]; simp)
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl) <;> simp

/-! ## Correctness -/

theorem hchk {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    hashChk (trR p) (trW p) [⟨.x25, 0, p.pkLen⟩] ⟨.x26, 0, 64⟩ = true := by
  rcases hp with rfl | rfl | rfl <;> decide

theorem keepSv {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    keepB (trR p) (trW p) [(Impl.MlDsa.AArch64.Call.sc 0, 200), (Impl.MlDsa.AArch64.Call.sc 200, 640), pieceP ⟨.x26, 0, 64⟩] KeyGen.svP 48 = true := by
  rcases hp with rfl | rfl | rfl <;> decide

theorem scr_big {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    Impl.MlDsa.AArch64.KeyGen.SV + 48 ≤ scratchWords p * 8 := by
  rcases hp with rfl | rfl | rfl <;> decide

theorem pkTr_ok (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87)
    {S : Nat} (h16 : 16 ≤ S) (hS : S < 2 ^ 64) {σ : State} (hpre : (Spec.MlDsa.pkTrContract p AArch64.abi S).pre σ) :
    WP isa (pkTrWith v.callee p) σ fun s' => abiPreserved σ s' ∧
      bytesAt s'.mem (σ.gpr .x1) 64 = Spec.MlDsa.pkTr (bytesAt σ.mem (σ.gpr .x0) p.pkLen) := by
  have hpre' := hpre
  sig_pre [Spec.MlDsa.pkTrContract, Spec.MlDsa.pkTrSig, AArch64.abi, VG.AArch64.argRegs] at hpre'
  obtain ⟨_, hrd, hwr, _, d02, _, _, _, _, n2⟩ := hpre'
  have hsm := small hp
  have hbig := scr_big hp
  have hscr : InRegions σ.wr (σ.gpr .x2) (scratchWords p * 8) :=
    KeyGen.inR_self (r := ⟨σ.gpr .x2, scratchWords p * 8⟩) (by rw [hwr]; simp)
  unfold pkTrWith enter
  refine WP.seq (Proof.MlKem.AArch64.wp_addImm (by decide) fun σ₁ o e => Proof.MlKem.AArch64.wp_nil ?_)
  have e3 : σ₁.gpr .x3 = σ.gpr .x2 := by rw [e, BitVec.add_zero]
  have hin : ∀ k < 6, InRegions σ₁.wr (σ₁.gpr .x3 + BitVec.ofNat 64 (Impl.MlDsa.AArch64.KeyGen.SV + 8 * k)) 8 :=
    fun k hk => by
      rw [e3, o.wr]
      exact inRegions_sub hscr (by omega) (by omega)
  refine WP.seq (WP.mono (KeyGen.pro_ok hin) fun s ⟨ht, _, hf⟩ => ?_)
  have L := trLay hp hpre o ht e3
  refine WP.seq (WP.mono (shake_ok (keccak := v) h16 hS L (by simp) (hchk hp)) fun s' ⟨hP, _, ho⟩ => ?_)
  have ht' := ht.step L hP (keepSv hp)
  have hin' : InRegions (s'.rd ++ s'.wr) (σ₁.gpr .x3 + BitVec.ofNat 64 Impl.MlDsa.AArch64.KeyGen.SV) 48 := by
    obtain ⟨r, hr, hc⟩ := inRegions_sub (off := Impl.MlDsa.AArch64.KeyGen.SV) (l := 48) hscr (by omega) (by omega)
    refine ⟨r, List.mem_append_right _ ?_, by rw [e3]; exact hc⟩
    rw [hP.wr, ht.wr, o.wr]; exact hr
  refine WP.mono (KeyGen.epi_ok ht' hin') fun s'' ⟨ha, _, hm⟩ => ⟨?_, ?_⟩
  · refine ⟨fun r hr => ?_, by rw [ha.2.1, o.sp], fun r hr => (ha.2.2 r hr).trans (o.vcs r hr)⟩
    rw [ha.1 r hr, o.gpr r (by revert r; decide)]
  · have e26 : pa s (.x26, 0) = σ.gpr .x1 := by
      rw [pa, ht.x26, o.gpr _ (by decide), BitVec.add_zero]
    have e25 : s.gpr .x25 + BitVec.ofNat 64 0 = σ.gpr .x0 := by
      rw [ht.x25, o.gpr _ (by decide), BitVec.add_zero]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
      Proof.MlKem.AArch64.pbytes, e25] at ho
    rw [hm, ← e26, ho, Spec.MlDsa.pkTr]
    refine congrArg (Spec.MlDsa.H · 64) ?_
    rw [Proof.MlKem.bytesAt_frame hf (fun r hr => ?_) (by omega), o.mem]
    simp only [List.mem_singleton] at hr
    subst hr
    rw [e3]
    exact d02.sub_right (VG.Offset.sub_base _ (by omega))

/-! ## The contract -/

/-- A state satisfying the precondition. -/
def pkTrSat (p : Params) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x4000 | .x2 => 0x10000 | _ => 0
  sp := 0x80000
  mem := fun _ => 0
  syms := fun _ => 0
  rd := [⟨0x1000, p.pkLen⟩]
  wr := [⟨0x4000, 64⟩, ⟨0x10000, scratchWords p * 8⟩]

theorem pkTrSat_pre {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    (Spec.MlDsa.pkTrContract p AArch64.abi 16).pre (pkTrSat p) := by
  rcases hp with rfl | rfl | rfl
  all_goals sig_pre [Spec.MlDsa.pkTrContract, Spec.MlDsa.pkTrSig, AArch64.abi, VG.AArch64.argRegs, pkTrSat]
  all_goals sig_and_intros
  all_goals first | rfl | exact Region.disjoint_of_sep (by decide) | decide

theorem pkTr_verified (v : Proof.Sha3.AArch64.Permutation) (p : Params)
    (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    Verified AArch64.target (pkTrWith v.callee p) (Spec.MlDsa.pkTrContract p AArch64.abi 16) := by
  obtain ⟨hint, hh⟩ := pkTr_taint v.callee v.callerSums p hp
  refine ⟨fun σ hσ => ?_, RelCT.constantTime (VectorTaint.relRegs [.x0, .x1, .x2] (fun x y ⟨_, _, h⟩ => ?_) hh),
    ⟨pkTrSat p, pkTrSat_pre hp⟩⟩
  · obtain ⟨t, s', he, ha, hb⟩ := pkTr_ok v hp (by decide) (by decide) hσ
    refine ⟨t, s', he, ha, ?_⟩
    sig_post [Spec.MlDsa.pkTrContract, Spec.MlDsa.pkTrSig, AArch64.abi, VG.AArch64.argRegs]
    exact hb
  · sig_pub [Spec.MlDsa.pkTrContract, Spec.MlDsa.pkTrSig, AArch64.abi, VG.AArch64.argRegs] at h
    obtain ⟨e₁, e₂, e₃, e₄⟩ := h
    refine ⟨e₁, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [e₂, e₃, e₄]

end VG.Proof.MlDsa.AArch64.PkTr
