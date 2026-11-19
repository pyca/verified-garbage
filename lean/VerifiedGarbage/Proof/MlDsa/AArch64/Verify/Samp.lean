module

public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Samp
meta import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Samp
public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Sample
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Sample
import VerifiedGarbage.Proof.MlKem.AArch64.Shared
import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
meta import VerifiedGarbage.Proof.MlKem.AArch64.Shared
meta import VerifiedGarbage.Proof.MlKem.AArch64.Vec
meta import VerifiedGarbage.Proof.MlKem.AArch64.Common
meta import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
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
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Arith
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Blocks
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Hash
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Inline
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Round
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Blocks
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.CallRound
import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.Proof.MlDsa.KeyGen.Leak
import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
import VerifiedGarbage.Proof.MlDsa.Verify.Bounds
import VerifiedGarbage.Proof.MlDsa.Verify.Final
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import VerifiedGarbage.Proof.MlKem.Compress
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.MlKem.KPke
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Squeeze
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Call
import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.Frag
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Base
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
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Arith
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Blocks
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Hash
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Inline
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Round
meta import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Blocks
meta import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.CallRound
meta import VerifiedGarbage.Proof.MlDsa.DecideAt
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Leak
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
meta import VerifiedGarbage.Proof.MlDsa.Verify.Bounds
meta import VerifiedGarbage.Proof.MlDsa.Verify.Final
meta import VerifiedGarbage.Proof.MlDsa.Verify.Mem
meta import VerifiedGarbage.Proof.MlKem.Compress
meta import VerifiedGarbage.Proof.MlKem.Encode
meta import VerifiedGarbage.Proof.MlKem.KPke
meta import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Absorb
meta import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
meta import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Squeeze
meta import VerifiedGarbage.Proof.Sha3.Arith
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Call
meta import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.Frag
meta import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Base
import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.MlKem.Arith
meta import VerifiedGarbage.Proof.MlKem.AArch64.Wp
meta import VerifiedGarbage.Proof.MlKem.Arith
public import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Lay
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.TaintSumGeneric
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Lay
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.Framework.TaintSumGeneric
import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono

/-! ### `MlDsa.AArch64.Verify.Z`, which only this module used -/

section

/-!
# ML-DSA verification on AArch64: the prologue, the hint and `z`

The prologue (`pro_vpiece`); the hint of the signature, with `x24` whether it
is well formed (`hint_vpiece`); then, if it is, `z[i]` (polynomial `k + i`
after `Â`) and `x24` whether each norm so far is small (`zOne_vpiece`). The
results in `x24` are functions of the signature, so they are the same in two
runs.
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Verify

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq normRq hintBitUnpack bitUnpack)
open VG.Proof.MlDsa (polyAt coeffAt Reduced PolyIs HintIs)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.KeyGen (ifp ifn)

/-! ## The inputs -/

/-- `h`, `z[i]`, and whether the norms of `z[0], …, z[j - 1]` are small, of a run from `σ`. -/
abbrev hintOf (p : Params) (σ : State) : Option (List (Vector Bool Spec.MlDsa.n)) :=
  Proof.MlDsa.Verify.vHint p (vSig p σ)
abbrev zOf (p : Params) (σ : State) (i : Nat) : IPoly := Proof.MlDsa.Verify.vZ p (vSig p σ) i
abbrev normOk (p : Params) (σ : State) (j : Nat) : Prop := ∀ i < j, normRq [toRq (zOf p σ i)] < p.γ₁ - p.β

/-- The result in `x24`. -/
abbrev flag (P : Prop) [Decidable P] : BitVec 64 := if P then 1 else 0

theorem flag_congr {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) : flag P = flag Q := by
  by_cases hp : P
  · simp only [flag, hp, h.mp hp, ↓reduceIte]
  · simp only [flag, hp, mt h.mpr hp, ↓reduceIte]

/-- `and24` of a flag and a callee's result. -/
theorem and_flag {P Q : Prop} [Decidable P] [Decidable Q] (r : BitVec 64)
    (hr : r.setWidth 32 = if Q then 1 else 0) :
    ((flag P).setWidth 32 &&& r.setWidth 32).setWidth 64 = flag (P ∧ Q) := by
  rw [hr]
  by_cases hp : P <;> by_cases hq : Q <;> simp only [flag, hp, hq, ↓reduceIte, and_self, and_false, false_and] <;>
    decide

theorem vpa0 (s : State) (r : Reg) : pa s (r, 0) = s.gpr r := BitVec.add_zero _

theorem VC.slice {p : Params} {σ s : State} (h : VC p σ s) {o len : Nat} (hl : o + len ≤ p.sigLen) :
    bytesAt s.mem (pa s (.x27, o)) len = ((vSig p σ).drop o).take len := by
  rw [← h.sig, vpa0, Proof.MlKem.bytesAt_slice _ _ hl]

theorem VC.pkSlice {p : Params} {σ s : State} (h : VC p σ s) {o len : Nat} (hl : o + len ≤ p.pkLen) :
    bytesAt s.mem (pa s (.x25, o)) len = ((vPk p σ).drop o).take len := by
  rw [← h.pk, vpa0, Proof.MlKem.bytesAt_slice _ _ hl]

theorem sc_ge {p : Params} (hF : VFacts p) : 4096 + 1024 * (p.k * p.ℓ + p.k + p.ℓ + 6) ≤ scrLen p := by
  rw [scr_eq]; have := hF.k; have := hF.l; omega_arith

/-- The block `and24`: only `x24`, and memory kept. -/
theorem and24_post {S : Nat} (s : State) :
    WP isa (.block and24) s fun s' => PPostB S s s' [] ∧ (∀ r, r ≠ .x24 → s'.gpr r = s.gpr r) ∧
      s'.gpr .x24 = ((s.gpr .x24).setWidth 32 &&& (s.gpr .x0).setWidth 32).setWidth 64 ∧ s'.mem = s.mem :=
  WP.mono (and24_ok s) fun _ ⟨o, e⟩ => ⟨postB_of_keep o.keep (by decide) (by rw [o.mem]; exact Frame.refl _ _),
    fun r hr => o.get r (by simpa using hr), e, o.mem⟩

theorem and24_nomem : ∀ i ∈ and24, ∀ s, isa.addrs i s = [] := fun i hi _ => by
  simp only [and24, List.mem_singleton] at hi; subst hi; rfl

/-! ## The prologue -/

theorem pro_vpiece {p : Params} (hF : VFacts p) {S : Nat} :
    VPiece p S (fun σ s => s = σ) (fun σ s => VC p σ s ∧ s.gpr .x24 = 1) (.block pro) := by
  refine ⟨fun σ s hp hs => ?_, taintRel [.x0, .x1, .x2, .x3] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ => ?_)
    (by taint_decide)⟩
  · subst hs
    have hp' := hp
    have hp' := hp'.1
    sig_pre [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig, AArch64.abi, VG.AArch64.argRegs,vInputs] at hp'
    obtain ⟨_, hwr, d03, d13, d23, _, _, _, _, _⟩ := hp'
    have hsc : 4096 + 1024 * (p.k * p.ℓ + p.k + p.ℓ + 6) ≤ Spec.MlDsa.scratchWords p * 8 := sc_ge hF
    have hsm := hF.small
    have hsv : SV + 48 ≤ Spec.MlDsa.scratchWords p * 8 := Nat.le_trans (by decide) (Nat.le_trans (Nat.le_add_right 4096 _) hsc)
    have hin : ∀ k < 6, InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 (SV + 8 * k)) 8 := fun k hk =>
      ⟨⟨s.gpr .x3, Spec.MlDsa.scratchWords p * 8⟩, by rw [hwr]; simp,
        Offset.contains_base _ (by simp only [SV]; omega_arith) (by simp only [SV]; omega_arith)⟩
    refine WP.mono (pro_ok hin) fun s' ⟨ht, h24, hf⟩ => ⟨⟨ht, ?_, ?_, ?_⟩, h24⟩
    · rw [vpa0, ht.x25]
      exact Proof.MlKem.bytesAt_frame hf (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact d03.sub_right (Offset.sub_base _ hsv)) (Nat.le_of_lt (Nat.lt_trans hsm.2.1 (by decide)))
    · rw [vpa0, ht.x26]
      exact Proof.MlKem.bytesAt_frame hf (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact d13.sub_right (Offset.sub_base _ hsv)) (by decide)
    · rw [vpa0, ht.x27]
      exact Proof.MlKem.bytesAt_frame hf (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact d23.sub_right (Offset.sub_base _ hsv)) (Nat.le_of_lt (Nat.lt_trans hsm.2.2 (by decide)))
  · subst h₁ h₂
    obtain ⟨esp, _, _, _, e0, e1, e2, e3⟩ := vPub_eq pub
    refine ⟨esp, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

/-! ## The hint -/

/-- After the hint: `x24` whether it is well formed, and the hint. -/
def V1 (p : Params) (σ s : State) : Prop :=
  VC p σ s ∧ s.gpr .x24 = flag ((hintOf p σ).isSome = true) ∧
    ∀ h, hintOf p σ = some h → HintIs s.mem (pa s (hP p 0)) p.k h

theorem hint_chk {p : Params} (hF : VFacts p) :
    rwChk (vR p) (vW p) (.x27, oHint p) (p.ω + p.k) (hP p 0) (256 * p.k * 4) = true := by
  have := hF.k; have := hF.l; have := hF.kl; have := scr_eq p; have := hF.sig; have := hF.small
  unfold rwChk; vlayd

theorem hint_eq (p : Params) (σ : State) :
    hintOf p σ = hintBitUnpack p.ω p.k (((vSig p σ).drop (oHint p)).take (p.ω + p.k)) := rfl

theorem hint_vpiece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p) :
    VPiece p S (fun σ s => VC p σ s ∧ s.gpr .x24 = 1) (V1 p) (hint P p) := by
  have hc := hint_chk hF
  refine ⟨fun σ s hp h => ?_, ?_⟩
  · have L := h.1.lay hF hp
    unfold hint
    refine WP.seq (WP.mono (huAt_ok hP.s64 hP.hintUnpack L hc hF.hu) fun s₁ ⟨hP₁, x₁, hq⟩ => ?_)
    have h₁ := h.1.step hF hp hP₁ (by
      have := hF.k; have := hF.l; have := hF.kl; have := scr_eq p; have := hF.small
      unfold vcChk; vlayd)
    refine WP.mono (and24_post (S := S) s₁) fun s₂ ⟨hP₂, g₂, x₂, hm⟩ => ?_
    have h₂ := h₁.step hF hp hP₂ (by
      have := hF.k; have := hF.l; have := scr_eq p; have := hF.small
      unfold vcChk; vlayd)
    rw [h.1.slice (by rw [hF.sig, oHint]; omega_arith), show p.ω + p.k - p.ω = p.k by omega_arith, ← hint_eq] at hq
    refine ⟨h₂, ?_, fun hh e => ?_⟩
    · rw [x₂, x₁, h.2]
      revert hq; cases hintOf p σ with
      | some hh => intro ⟨hr, _⟩; rw [hr]; rfl
      | none => intro hr; rw [hr]; rfl
    · rw [e] at hq
      rw [hP₂.pa (show Reg.x28 ∈ keptRegs by decide), hm, hP₁.pa (show Reg.x28 ∈ keptRegs by decide)]
      exact hq.2
  · refine vrel_of (Q := fun x y => VTwo p S x y ∧ bytesAt x.mem (pa x (.x27, oHint p)) (p.ω + p.k) =
      bytesAt y.mem (pa y (.x27, oHint p)) (p.ω + p.k)) ?_ fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
        ⟨vc_two hF p₁ p₂ pub h₁.1 h₂.1, by
          have hl : oHint p + (p.ω + p.k) ≤ p.sigLen := by rw [hF.sig, oHint]; omega_arith
          rw [h₁.1.slice hl, h₂.1.slice hl, (vPub_eq pub).2.2.2.1]⟩
    unfold hint
    exact RelCT.seq (huAt_tr hP.hintUnpack (vOk p) hc hF.hu fun x y h => ⟨h.1.lx, h.1.ly, h.2, h.1.same⟩)
      (block_nomem_tr and24_nomem)

/-! ## `z` -/

/-- After `z[0], …, z[j - 1]`, with the hint well formed. -/
structure VZ (p : Params) (σ : State) (j : Nat) (s : State) : Prop where
  vc : VC p σ s
  hint : ∃ h, hintOf p σ = some h ∧ HintIs s.mem (pa s (hP p 0)) p.k h
  z : ∀ i < j, PolyIs s.mem (pa s (zP p i)) (toRq (zOf p σ i))

/-- A piece that writes `ws` keeps `VZ`. -/
structure VZChk (p : Params) (j : Nat) (ws : List (Ptr × Nat)) : Prop where
  vc : vcChk p ws = true
  hint : keepB (vR p) (vW p) ws (hP p 0) (1024 * p.k) = true
  z : ∀ i < j, keepB (vR p) (vW p) ws (zP p i) 1024 = true

theorem VZ.keep {p : Params} (hF : VFacts p) {S : Nat} {σ : State} (hp : vPre p S σ) {j : Nat} {s s' : State}
    (h : VZ p σ j s) {ws : List (Ptr × Nat)} (hP : PPostB S s s' ws) (hc : VZChk p j ws) : VZ p σ j s' := by
  have L := h.vc.lay hF hp
  obtain ⟨hh, e, hH⟩ := h.hint
  exact ⟨h.vc.step hF hp hP hc.vc, ⟨hh, e, L.keepHint hP hc.hint hH⟩,
    fun i hi => L.keepPoly hP (hc.z i hi) (h.z i hi)⟩

theorem VFacts.scr {p : Params} (_ : VFacts p) : scrLen p = 1024 * (p.k * p.ℓ + 4 * p.k + 3 * p.ℓ + 32) :=
  scr_eq p

/-- Proves a `VZChk`: each check decided for each parameter set if it can be (`vlayd`). -/
tactic_template "vzchk " hF:term:max : tactic => `(tactic| (
      have := ($hF).k; have := ($hF).l; have := ($hF).kl; have := ($hF).scr; have := ($hF).small
      refine ⟨?_, ?_, ?_⟩ <;> intros <;> (try unfold VG.Proof.MlDsa.AArch64.Verify.vcChk) <;> first | vlayd | vlay))

theorem zl_le {p : Params} {j : Nat} (hj : j < p.ℓ) : lenZ p * j + lenZ p ≤ lenZ p * p.ℓ := by
  rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj

/-- `x24` whether the norms so far are small, and then `z[j]`, and whether its norm is. -/
abbrev Z0 (p : Params) (j : Nat) (σ s : State) : Prop := VZ p σ j s ∧ s.gpr .x24 = flag (normOk p σ j)
abbrev Z1 (p : Params) (j : Nat) (σ s : State) : Prop :=
  Z0 p j σ s ∧ PolyIs s.mem (pa s (zP p j)) (toRq (zOf p σ j))
abbrev Z2 (p : Params) (j : Nat) (σ s : State) : Prop :=
  Z1 p j σ s ∧ (s.gpr .x0).setWidth 32 = if normRq [toRq (zOf p σ j)] < p.γ₁ - p.β then 1 else 0

theorem zOf_eq (p : Params) (σ : State) (j : Nat) :
    zOf p σ j = bitUnpack (((vSig p σ).drop (p.ctildeLen + lenZ p * j)).take (lenZ p)) (p.γ₁ - 1) p.γ₁ := rfl

section
variable {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p) {j : Nat} (hj : j < p.ℓ)
include hP hF hj

omit hP in
theorem bu_chk : rwChk (vR p) (vW p) (.x27, p.ctildeLen + lenZ p * j) (lenZ p) (zP p j) 1024 = true := by
  have := hF.k; have := hF.l; have := hF.kl; have := scr_eq p; have := hF.sig; have := hF.small
  have := zl_le hj
  unfold rwChk; vlayd

theorem bu_vpiece : VPiece p S (Z0 p j) (Z1 p j)
    (bitUnpackAt P (.x27, p.ctildeLen + lenZ p * j) (lenZ p) (p.γ₁ - 1) p.γ₁ (zP p j)) := by
  have hc := bu_chk hF hj
  refine ⟨fun σ s hp h => ?_, vrel_of (Q := VTwo p S) (buAt_tr hP.bitUnpack (vOk p) hc hF.bp
    fun x y h => ⟨h.lx, h.ly, h.same⟩) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => vc_two hF p₁ p₂ pub h₁.1.vc h₂.1.vc⟩
  have L := h.1.vc.lay hF hp
  refine WP.mono (buAt_ok hP.s64 hP.bitUnpack L hc hF.bp) fun s' ⟨hP', x', hq⟩ => ?_
  have := zl_le hj
  refine ⟨⟨h.1.keep hF hp hP' (by vzchk hF), by rw [x', h.2]⟩, ?_⟩
  rw [h.1.vc.slice (by rw [hF.sig]; omega_arith), ← zOf_eq] at hq
  rw [hP'.pa (show Reg.x28 ∈ keptRegs by decide)]
  exact hq

theorem norm_vpiece : VPiece p S (Z1 p j) (Z2 p j) (normLtAt P (zP p j) (p.γ₁ - p.β)) := by
  have hc : inB (vR p ++ vW p) (zP p j) 1024 = true := by
    have := hF.k; have := hF.l; have := hF.kl; have := scr_eq p; vlayd
  refine ⟨fun σ s hp h => ?_, vrel_of (Q := fun x y => VTwo p S x y ∧ Reduced x.mem (pa x (zP p j)) ∧
    Reduced y.mem (pa y (zP p j))) (normAt_tr hP.normLt (vOk p) hc fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2,
      h.1.same⟩) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨vc_two hF p₁ p₂ pub h₁.1.1.vc h₂.1.1.vc, h₁.2.1, h₂.2.1⟩⟩
  have L := h.1.1.vc.lay hF hp
  refine WP.mono (normAt_ok hP.s64 hP.normLt L hc hF.g1.2.2 h.2.1) fun s' ⟨hP', x', hq⟩ => ?_
  have hz := L.keepPoly hP' (by
    have := hF.k; have := hF.l; have := hF.kl; have := scr_eq p; vlayd) h.2
  refine ⟨⟨⟨h.1.1.keep hF hp hP' (by vzchk hF), by rw [x', h.1.2]⟩, hz⟩, ?_⟩
  rw [hq, h.2.2]

omit hP in
theorem and_vpiece : VPiece p S (Z2 p j) (Z0 p (j + 1)) (.block and24) := by
  refine ⟨fun σ s hp h => ?_, block_nomem_tr and24_nomem⟩
  refine WP.mono (and24_post (S := S) s) fun s' ⟨hP', _, x', _⟩ => ?_
  have L := h.1.1.1.vc.lay hF hp
  have hz := L.keepPoly hP' (by
    have := hF.k; have := hF.l; have := hF.kl; have := scr_eq p; vlayd) h.1.2
  obtain ⟨⟨⟨hv, hn⟩, _⟩, hr⟩ := h
  have hv' := hv.keep hF hp hP' (by vzchk hF)
  refine ⟨⟨hv'.vc, hv'.hint, fun i hi => ?_⟩, ?_⟩
  · rcases (by omega_arith : i < j ∨ i = j) with hi | rfl
    · exact hv'.z i hi
    · exact hz
  · rw [x', hn, and_flag _ hr]
    exact flag_congr ⟨fun ⟨h1, h2⟩ i hi => by
      rcases (by omega_arith : i < j ∨ i = j) with hi | rfl
      exacts [h1 i hi, h2], fun h1 => ⟨fun i hi => h1 i (by omega_arith), h1 j (by omega_arith)⟩⟩

theorem zOne_vpiece : VPiece p S (Z0 p j) (Z0 p (j + 1)) (zOne P p j) :=
  (bu_vpiece hP hF hj).seq ((norm_vpiece hP hF hj).seq (and_vpiece hF hj))

end

end VG.Proof.MlDsa.AArch64.Verify

end

end

/-!
# ML-DSA verification on AArch64: the samplers

`ρ` to the seed (`copyRho_vpiece`); each entry `Â[r, s]` sampled from `ρ ‖ s ‖
r` (`expA_vpiece`), and `c` (`ball_vpiece`), each reduced, and `x24` 1 only if
every sampler succeeded, with their outputs (`VA`, `VB`). Each sampler's
output is masked with its result, without a branch; the seeds are functions of
the public key and the signature, the same in two runs.
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Verify

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq Bounds minBounds rejNTTPoly sampleInBall Outcome)
open VG.Proof.MlDsa (polyAt coeffAt Reduced PolyIs)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.KeyGen (ifp ifn)
open VG.Impl.MlKem.AArch64 (copy32)
open VG.Proof.MlKem.AArch64 (Keep)

/-- The seed of entry `e = rℓ + s` of `Â`. -/
abbrev seedOf (p : Params) (σ : State) (e : Nat) : List Byte :=
  Proof.MlDsa.Verify.aSeed (vPk p σ) (e / p.ℓ) (e % p.ℓ)
/-- `c̃`. -/
abbrev ctOf (p : Params) (σ : State) : List Byte := Proof.MlDsa.Verify.vCt p (vSig p σ)

/-- After the first `e` entries of `Â`. -/
structure VA (p : Params) (σ : State) (e : Nat) (s : State) : Prop where
  vz : VZ p σ p.ℓ s
  nok : normOk p σ p.ℓ
  rho : bytesAt s.mem (pa s (sc oSA)) 32 = (vPk p σ).take 32
  red : ∀ e' < e, Reduced s.mem (pa s (aP e'))
  ok : ∃ q : Bool, s.gpr .x24 = flag (q = true) ∧
    (q = true → ∀ e' < e, ∃ b : Bounds, rejNTTPoly b.rejNTT (seedOf p σ e') = some (polyAt s.mem (pa s (aP e')))) ∧
    (q = false → ∃ e' < e, rejNTTPoly minBounds.rejNTT (seedOf p σ e') = none)

/-- A piece that writes `ws` keeps `VA`. -/
structure VAChk (p : Params) (e : Nat) (ws : List (Ptr × Nat)) : Prop where
  vz : VZChk p p.ℓ ws
  rho : keepB (vR p) (vW p) ws (sc oSA) 32 = true
  a : ∀ e' < e, keepB (vR p) (vW p) ws (aP e') 1024 = true

/-- Proves a `VAChk`: each check decided for each parameter set if it can be (`vlayd`). -/
syntax "vachk " term:max : tactic
macro_rules
  | `(tactic| vachk $hF) => `(tactic| (
      have := ($hF).k; have := ($hF).l; have := ($hF).kl; have := ($hF).scr; have := ($hF).small
      refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;> intros <;> (try unfold VG.Proof.MlDsa.AArch64.Verify.vcChk) <;> first | vlayd | vlay))

theorem VA.keep {p : Params} (hF : VFacts p) {S : Nat} {σ : State} (hp : vPre p S σ) {e : Nat} {s s' : State}
    (h : VA p σ e s) {ws : List (Ptr × Nat)} (hP : PPostB S s s' ws) (hc : VAChk p e ws)
    (h24 : s'.gpr .x24 = s.gpr .x24) : VA p σ e s' := by
  have L := h.vz.vc.lay hF hp
  obtain ⟨q, hq, h1, h0⟩ := h.ok
  refine ⟨h.vz.keep hF hp hP hc.vz, h.nok, by rw [L.keepBytes hP hc.rho]; exact h.rho,
    fun e' he' => L.keepRed hP (hc.a e' he') (h.red e' he'), q, by rw [h24]; exact hq, fun hq' e' he' => ?_, h0⟩
  obtain ⟨b, hb⟩ := h1 hq' e' he'
  exact ⟨b, by rw [hb, L.keepPolyAt hP (hc.a e' he')]⟩

/-! ## `ρ` -/

theorem copyRho_vpiece {p : Params} (hF : VFacts p) {S : Nat} :
    VPiece p S (fun σ s => Z0 p p.ℓ σ s ∧ normOk p σ p.ℓ) (VA p · 0) (.block (copy32 .x25 0 .x28 oSA)) := by
  have hc : copyPChk (vR p) (vW p) (sc oSA) (.x25, 0) = true := by
    have := hF.k; have := hF.l; have := hF.scr; have := hF.pk; unfold copyPChk; vlayd
  refine ⟨fun σ s hp h => ?_, taintRel [.x25, .x28] (fun x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ?_)
    (by taint_decide)⟩
  · have L := h.1.1.vc.lay hF hp
    refine WP.mono (copyP_ok L hc) fun s' ⟨hP', k', hb⟩ => ?_
    refine ⟨h.1.1.keep hF hp hP' (by vzchk hF), h.2, ?_, fun _ h => absurd h (Nat.not_lt_zero _), true, ?_,
      fun _ _ h => absurd h (Nat.not_lt_zero _), fun h => absurd h (by decide)⟩
    · rw [hP'.pa (show Reg.x28 ∈ keptRegs by decide), hb, h.1.1.vc.pkSlice (by rw [hF.pk]; omega_using []), List.drop_zero]
    · rw [k'.get .x24, h.1.2]; exact flag_congr (iff_of_true h.2 rfl)
  · have T := vc_two hF p₁ p₂ pub h₁.1.1.vc h₂.1.1.vc
    refine ⟨T.same.2, fun r hr => T.same.1 r ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide

/-! ## An entry of `Â` -/

/-- The seed of `RejNTTPoly` set. -/
abbrev VA1 (p : Params) (e : Nat) (σ s : State) : Prop :=
  VA p σ e s ∧ bytesAt s.mem (pa s (sc oSA)) 34 = seedOf p σ e

/-- After `RejNTTPoly`. -/
abbrev VA2 (p : Params) (e : Nat) (σ s : State) : Prop :=
  VA p σ e s ∧ ((s.gpr .x0).setWidth 32 = 1 → Reduced s.mem (pa s (aP e))) ∧
    Outcome (fun b => rejNTTPoly b.rejNTT (seedOf p σ e)) ((s.gpr .x0).setWidth 32) (polyAt s.mem (pa s (aP e)))

theorem integerToBytes_one (x : Nat) : Spec.MlDsa.integerToBytes x 1 = [BitVec.ofNat 8 x] := by
  simp [Spec.MlDsa.integerToBytes]

theorem vsetTwo_ok {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {o a b : Nat}
    (ho : o + 1 < 4096) (h1 : inB wbs (sc o) 1 = true) (h2 : inB wbs (sc (o + 1)) 1 = true) :
    WP isa (.block (setB (sc o) a ++ setB (sc (o + 1)) b)) s fun s' =>
      PPostB S s s' [(sc o, 1), (sc (o + 1), 1)] ∧ Keep [.x9] s s' ∧
      bytesAt s'.mem (pa s (sc o)) 2 = [BitVec.ofNat 8 a, BitVec.ofNat 8 b] := by
  rw [WP.block_append_iff]
  refine WP.mono (setB_ok L (p := sc o) (v := a) (by simp only; omega_using [ho]) h1 (show Reg.x28 ∈ keptRegs by decide))
    fun s₁ ⟨hP₁, k₁, m₁⟩ => WP.mono (setB_ok (L.post hP₁) (p := sc (o + 1)) (v := b) ho h2
      (show Reg.x28 ∈ keptRegs by decide))
      fun s₂ ⟨hP₂, k₂, m₂⟩ => ⟨PPostB.app hP₁ hP₂ (sc_bases _ (by simp)), (k₁.trans k₂).mono (by simp), ?_⟩
  have e : pa s₁ (sc (o + 1)) = pa s (sc o) + BitVec.ofNat 64 1 := by
    rw [hP₁.pa (show Reg.x28 ∈ keptRegs by decide), pa, pa, BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [m₂, m₁, e]
  exact bytesAt_two _ _ _ _

/-- The AND of a sampler's result and the mask of its output, from the registers `x28`. -/
theorem vtail_taint : ∀ j < 80, (taint.check (AArch64.Taint.ofRegs [.x28]) (.seq (.block and24) (mask (sc (oP j))))
    (VG.Taint.hintOf taint (AArch64.Taint.ofRegs [.x28]) (.seq (.block and24) (mask (sc 0))))).isSome = true := by
  decide +kernel

section
variable {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p) {e : Nat} (he : e < p.k * p.ℓ)
include hP hF he

omit hP in
theorem seed_vpiece : VPiece p S (VA p · e) (VA1 p e)
    (.block (setB (sc (oSA + 32)) (e % p.ℓ) ++ setB (sc (oSA + 33)) (e / p.ℓ))) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := hF.scr
  have hq : e / p.ℓ < p.k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he)
  have hr : e % p.ℓ < p.ℓ := Nat.mod_lt _ (by omega_using [hl])
  refine ⟨fun σ s hp h => ?_, taintRel [.x28] (fun x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ =>
    (vc_two hF p₁ p₂ pub h₁.vz.vc h₂.vz.vc).x28) (setIJ_taint _ (by omega_using [hl, hr]) _ (by omega_using [hk, hq]))⟩
  have L := h.vz.vc.lay hF hp
  refine WP.mono (vsetTwo_ok L (o := oSA + 32) (a := e % p.ℓ) (b := e / p.ℓ) (by decide) (by vlayd) (by vlayd))
    fun s' ⟨hP', k', hb⟩ => ⟨h.keep hF hp hP' (by vachk hF) (k'.get .x24), ?_⟩
  rw [bytes34, L.keepBytes hP' (by vlayd), h.rho, sc_add, sc_pa hP', hb, seedOf, Proof.MlDsa.Verify.aSeed,
    integerToBytes_one, integerToBytes_one, List.append_assoc]
  rfl

omit hP in
theorem rej_chk : rejNttChk (vR p) (vW p) (sc oSA) (aP e) (sc oSS) = true := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := hF.scr
  unfold rejNttChk; vlayd

theorem rej_vpiece : VPiece p S (VA1 p e) (VA2 p e) (rejNttAt P (sc oSS) (sc oSA) (aP e)) := by
  have hc := rej_chk hF he
  refine ⟨fun σ s hp h => ?_, vrel_of (Q := fun x y => VTwo p S x y ∧
    bytesAt x.mem (pa x (sc oSA)) 34 = bytesAt y.mem (pa y (sc oSA)) 34)
    (rejNttInline_tr hP.rejNtt (vOk p) hc fun x y h => ⟨h.1.lx, h.1.ly, h.2, h.1.same⟩)
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨vc_two hF p₁ p₂ pub h₁.1.vz.vc h₂.1.vz.vc, by
      rw [h₁.2, h₂.2, seedOf, seedOf, (vPub_eq pub).2.1]⟩⟩
  have L := h.1.vz.vc.lay hF hp
  refine WP.mono (rejNttInline_ok hP.s64 hP.rejNtt L hc) fun s' ⟨hP', x', hred, hout⟩ => ?_
  rw [h.2] at hout
  have e' : pa s' (aP e) = pa s (aP e) := sc_pa hP' _
  refine ⟨h.1.keep hF hp hP' (by vachk hF) x', fun h1 => by rw [e']; exact hred h1, by rw [e']; exact hout⟩

omit hP in
theorem tail_vpiece : VPiece p S (VA2 p e) (VA p · (e + 1)) (.seq (.block and24) (mask (aP e))) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := hF.scr
  refine ⟨fun σ s hp h => ?_, taintRel [.x28] (fun x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ =>
    (vc_two hF p₁ p₂ pub h₁.1.vz.vc h₂.1.vz.vc).x28) (vtail_taint e (by omega_using [he, hkl]))⟩
  have L := h.1.vz.vc.lay hF hp
  obtain ⟨hv, hred, hout⟩ := h
  have hr01 := Proof.MlDsa.KeyGen.outcome_01 hout
  refine WP.mono (tail_ok L (a := aP e) (by vlayd) (by vlayd) hr01) fun s' ⟨hP', x', hco⟩ => ?_
  have hvz := hv.vz.keep hF hp hP' (by vzchk hF)
  have e' : pa s' (aP e) = pa s (aP e) := sc_pa hP' _
  obtain ⟨q, hq, h1, h0⟩ := hv.ok
  rw [hq] at x'
  have hA : ∀ e' < e, polyAt s'.mem (pa s' (aP e')) = polyAt s.mem (pa s (aP e')) := fun e' he' =>
    L.keepPolyAt hP' (by vlay)
  refine ⟨hvz, hv.nok, by rw [L.keepBytes hP' (by vlayd)]; exact hv.rho, fun e'' he'' => ?_, q && ((s.gpr .x0).setWidth 32 == 1), ?_, fun hq' e'' he'' => ?_,
    fun hq' => ?_⟩
  · rcases (by omega_using [he''] : e'' < e ∨ e'' = e) with he'' | rfl
    · exact L.keepRed hP' (by vlay) (hv.red e'' he'')
    · rw [e']
      by_cases h1 : (s.gpr .x0).setWidth 32 = 1
      · exact (Proof.MlDsa.KeyGen.masked_one h1 hco).2 (hred h1)
      · exact (Proof.MlDsa.KeyGen.masked_zero h1 hco).1
  · rw [x', and_flag _ (Q := (s.gpr .x0).setWidth 32 = 1) (by rcases hr01 with h | h <;> rw [h] <;> decide)]
    exact flag_congr (by simp)
  · simp only [Bool.and_eq_true, beq_iff_eq] at hq'
    rcases (by omega_using [he''] : e'' < e ∨ e'' = e) with he'' | rfl
    · obtain ⟨b, hb⟩ := h1 hq'.1 e'' he''
      exact ⟨b, by rw [hb, hA e'' he'']⟩
    · rcases hout with ⟨_, b, hb⟩ | ⟨h0', _⟩
      · exact ⟨b, by rw [e', (Proof.MlDsa.KeyGen.masked_one hq'.2 hco).1]; exact hb⟩
      · rw [hq'.2] at h0'; exact absurd h0' (by decide)
  · cases hqq : q
    · obtain ⟨e'', he'', hn⟩ := h0 hqq
      exact ⟨e'', by omega_using [he''], hn⟩
    · rw [hqq] at hq'
      simp only [Bool.true_and, beq_eq_false_iff_ne, ne_eq] at hq'
      rcases hout with ⟨h1', _⟩ | ⟨_, hn⟩
      · exact absurd h1' hq'
      · exact ⟨e, by omega_using [], hn⟩

theorem expA_vpiece : VPiece p S (VA p · e) (VA p · (e + 1)) (expA P p e) := by
  unfold expA sampled
  exact (seed_vpiece hF he).seq ((rej_vpiece hP hF he).seq (tail_vpiece hF he))

end

/-! ## `c` -/

/-- After the samplers. -/
structure VB (p : Params) (σ : State) (s : State) : Prop where
  vz : VZ p σ p.ℓ s
  nok : normOk p σ p.ℓ
  red : ∀ e < p.k * p.ℓ, Reduced s.mem (pa s (aP e))
  redC : Reduced s.mem (pa s (cP p))
  ok : ∃ q : Bool, s.gpr .x24 = flag (q = true) ∧
    (q = true → (∀ e < p.k * p.ℓ, ∃ b : Bounds, rejNTTPoly b.rejNTT (seedOf p σ e) = some (polyAt s.mem (pa s (aP e)))) ∧
      ∃ b : Bounds, (sampleInBall p.τ b.ball (ctOf p σ)).map toRq = some (polyAt s.mem (pa s (cP p)))) ∧
    (q = false → (∃ e < p.k * p.ℓ, rejNTTPoly minBounds.rejNTT (seedOf p σ e) = none) ∨
      (sampleInBall p.τ minBounds.ball (ctOf p σ)).map toRq = none)

/-- After `SampleInBall`. -/
abbrev VB1 (p : Params) (σ s : State) : Prop :=
  VA p σ (p.k * p.ℓ) s ∧ ((s.gpr .x0).setWidth 32 = 1 → Reduced s.mem (pa s (cP p))) ∧
    Outcome (fun b => (sampleInBall p.τ b.ball (ctOf p σ)).map toRq) ((s.gpr .x0).setWidth 32)
      (polyAt s.mem (pa s (cP p)))

section
variable {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p)
include hP hF

omit hP in
theorem ball_chk : ballChk (vR p) (vW p) (.x27, 0) p.ctildeLen (cP p) (sc oSS) = true := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := hF.scr; have := hF.ct; have := hF.sig
  unfold ballChk; vlayd

omit hP in
theorem ctOf_eq {σ s : State} (h : VC p σ s) : bytesAt s.mem (pa s (.x27, 0)) p.ctildeLen = ctOf p σ := by
  have := hF.sig
  rw [h.slice (by omega_using [this]), List.drop_zero]; rfl

theorem ballCall_vpiece : VPiece p S (VA p · (p.k * p.ℓ)) (VB1 p)
    (ballAt P (sc oSS) (.x27, 0) p.ctildeLen p.τ (cP p)) := by
  have hc := ball_chk hF
  refine ⟨fun σ s hp h => ?_, vrel_of (Q := fun x y => VTwo p S x y ∧
    bytesAt x.mem (pa x (.x27, 0)) p.ctildeLen = bytesAt y.mem (pa y (.x27, 0)) p.ctildeLen)
    (ballAt_tr hP.ball (vOk p) hc hF.ct.1 fun x y h => ⟨h.1.lx, h.1.ly, h.2, h.1.same⟩)
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨vc_two hF p₁ p₂ pub h₁.vz.vc h₂.vz.vc, by
      rw [ctOf_eq hF h₁.vz.vc, ctOf_eq hF h₂.vz.vc, ctOf, ctOf, (vPub_eq pub).2.2.2.1]⟩⟩
  have L := h.vz.vc.lay hF hp
  refine WP.mono (ballAt_ok hP.s64 hP.ball L hc hF.ct.1) fun s' ⟨hP', x', hred, hout⟩ => ?_
  rw [ctOf_eq hF h.vz.vc] at hout
  have e' : pa s' (cP p) = pa s (cP p) := sc_pa hP' _
  refine ⟨h.keep hF hp hP' (by vachk hF) x', fun h1 => by rw [e']; exact hred h1, by rw [e']; exact hout⟩

omit hP in
theorem ballTail_vpiece : VPiece p S (VB1 p) (VB p) (.seq (.block and24) (mask (cP p))) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := hF.scr
  refine ⟨fun σ s hp h => ?_, taintRel [.x28] (fun x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ =>
    (vc_two hF p₁ p₂ pub h₁.1.vz.vc h₂.1.vz.vc).x28) (vtail_taint _ (by omega_using [hkl, hl, hk]))⟩
  have L := h.1.vz.vc.lay hF hp
  obtain ⟨hv, hred, hout⟩ := h
  have hr01 := Proof.MlDsa.KeyGen.outcome_01 hout
  refine WP.mono (tail_ok L (a := cP p) (by vlayd) (by vlayd) hr01) fun s' ⟨hP', x', hco⟩ => ?_
  have hvz := hv.vz.keep hF hp hP' (by vzchk hF)
  have e' : pa s' (cP p) = pa s (cP p) := sc_pa hP' _
  obtain ⟨q, hq, h1, h0⟩ := hv.ok
  rw [hq] at x'
  refine ⟨hvz, hv.nok, fun e he => L.keepRed hP' (by vlayd) (hv.red e he), ?_, q && ((s.gpr .x0).setWidth 32 == 1), ?_, fun hq' => ⟨fun e he => ?_, ?_⟩,
    fun hq' => ?_⟩
  · rw [e']
    by_cases h1 : (s.gpr .x0).setWidth 32 = 1
    · exact (Proof.MlDsa.KeyGen.masked_one h1 hco).2 (hred h1)
    · exact (Proof.MlDsa.KeyGen.masked_zero h1 hco).1
  · rw [x', and_flag _ (Q := (s.gpr .x0).setWidth 32 = 1) (by rcases hr01 with h | h <;> rw [h] <;> decide)]
    exact flag_congr (by simp)
  · simp only [Bool.and_eq_true, beq_iff_eq] at hq'
    obtain ⟨b, hb⟩ := h1 hq'.1 e he
    exact ⟨b, by rw [hb, L.keepPolyAt hP' (by vlayd)]⟩
  · simp only [Bool.and_eq_true, beq_iff_eq] at hq'
    rcases hout with ⟨_, b, hb⟩ | ⟨h0', _⟩
    · exact ⟨b, by rw [e', (Proof.MlDsa.KeyGen.masked_one hq'.2 hco).1]; exact hb⟩
    · rw [hq'.2] at h0'; exact absurd h0' (by decide)
  · cases hqq : q
    · exact .inl (h0 hqq)
    · rw [hqq] at hq'
      simp only [Bool.true_and, beq_eq_false_iff_ne, ne_eq] at hq'
      rcases hout with ⟨h1'', _⟩ | ⟨_, hn⟩
      · exact absurd h1'' hq'
      · exact .inr hn

end

end VG.Proof.MlDsa.AArch64.Verify
