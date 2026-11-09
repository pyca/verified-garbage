module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseA
public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Hash
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA signing on AArch64: the private key and `ρ″`

Once `Â` is sampled (`IM`): `ŝ₁[r]`, `ŝ₂[i]` and `t̂₀[i]`, each the `NTT` of
the `BitUnpack` of its piece of `sk` (`S1v`, `S2v`, `T0v`), and
`ρ″ = H(K ‖ rnd ‖ μ, 64)` (`rppOf`); and the layout checks of decoding
(`idChk`, `decChk`, `dChk`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable (p : Params)

/-- The slots of `ŝ₁`, `ŝ₂` and `t̂₀`. -/
abbrev s1Base : Nat := 5 + 2 * p.k + 2 * p.ℓ
abbrev s2Base : Nat := 5 + 2 * p.k + 3 * p.ℓ
abbrev t0Base : Nat := 5 + 3 * p.k + 3 * p.ℓ

/-- `ŝ₁[r]`, `ŝ₂[i]` and `t̂₀[i]` of the function entered in `σ`. -/
abbrev S1v (σ : State) (r : Nat) : Poly := s1F p (skOf p σ) r
abbrev S2v (σ : State) (i : Nat) : Poly := s2F p (skOf p σ) i
abbrev T0v (σ : State) (i : Nat) : Poly := t0F p (skOf p σ) i

/-- `ρ″ = H(K ‖ rnd ‖ μ, 64)`. -/
abbrev rppOf (σ : State) : List Byte := H (((skOf p σ).drop 32).take 32 ++ rndOf σ ++ muOf σ) 64

end

/-! ## `Â` -/

/-- `Â` sampled within `maxBounds`, in its slots. -/
structure IM (p : Params) (D : Nat) (σ s : State) : Prop where
  st : St p D σ s
  ok : ∀ e < p.k * p.ℓ, (rejNTTPoly maxBounds.rejNTT (seedE p σ e)).isSome
  A : Fam s (aBase p) (p.k * p.ℓ) (aVal p σ)

def imChk (p : Params) (ws : List (Ptr × Nat)) : Bool := stChk p ws && famChk (sgR p) (sgW p) ws (aBase p) (p.k * p.ℓ)

theorem IM.step {p : Params} {D : Nat} {σ s s' : State} (h : IM p D σ s) {ws : List (Ptr × Nat)}
    (hP : PPostB D s s' ws) (hc : imChk p ws = true) : IM p D σ s' := by
  simp only [imChk, Bool.and_eq_true] at hc
  exact ⟨h.st.step hP hc.1, h.ok, Fam.keep h.st.lay hP hc.2 h.A⟩

/-! ## The private key -/

def idChk (p : Params) (ws : List (Ptr × Nat)) (a b c : Nat) : Bool :=
  imChk p ws && famChk (sgR p) (sgW p) ws (s1Base p) a && famChk (sgR p) (sgW p) ws (s2Base p) b && famChk (sgR p) (sgW p) ws (t0Base p) c

theorem pS_bases (j : Nat) : (pS j).1 ∈ keptRegs := by simp

theorem sc_bases (o : Nat) : (sc o).1 ∈ keptRegs := by simp

theorem pa_add (s : State) (r : Reg) (a b : Nat) : pa s (r, a) + BitVec.ofNat 64 b = pa s (r, a + b) := by
  rw [pa, pa, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem sk_slice {p : Params} {D : Nat} {σ s : State} (h : St p D σ s) {o len : Nat} (hk : o + len ≤ p.skLen) :
    bytesAt s.mem (pa s (.x25, o)) len = ((skOf p σ).drop o).take len := by
  rw [← h.sk, VG.Proof.MlKem.bytesAt_slice _ _ hk, pa_add, Nat.zero_add]

/-- What decoding a polynomial of `len` bytes at `src` to slot `j` needs of the layout. -/
def decChk (p : Params) (a b c : Nat) (src : Ptr) (len j : Nat) : Bool :=
  rwChk (sgR p) (sgW p) src len (pS j) 1024 && ipChkS (sgR p) (sgW p) (pS j) &&
    idChk p [(pS j, 1024)] a b c && idChk p [(pS j, 1024), (sc oPS, 1024)] a b c

/-- What `decode` needs of the layout. -/
def dChk (p : Params) : Bool :=
  (List.range p.ℓ).all (fun r => decChk p r 0 0 (.x25, skS1 p r) (sLen p) (s1Base p + r) &&
      decide (skS1 p r + sLen p ≤ p.skLen)) &&
    (List.range p.k).all (fun i => decChk p p.ℓ i 0 (.x25, skS2 p i) (sLen p) (s2Base p + i) &&
      decide (skS2 p i + sLen p ≤ p.skLen)) &&
    (List.range p.k).all (fun i => decChk p p.ℓ p.k i (.x25, skT0 p i) 416 (t0Base p + i) &&
      decide (skT0 p i + 416 ≤ p.skLen)) &&
    hashChk (sgR p) (sgW p) [⟨.x25, 32, 32⟩, ⟨.x27, 0, 32⟩, ⟨.x26, 0, 64⟩] ⟨.x28, oMS, 64⟩ &&
    idChk p [(sc 0, 200), (sc 200, 640), (sc oMS, 64)] p.ℓ p.k p.k && inB (sgB p) (sc oMS) 64 &&
    decide ((p.η, p.η) ∈ bitPackParams) && decide (64 ≤ p.skLen)

theorem dChk_ok {p : Params} (h : Ok3 p) : dChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide +kernel

theorem dChk_spec {p : Params} (hc : dChk p = true) :
    (∀ r < p.ℓ, decChk p r 0 0 (.x25, skS1 p r) (sLen p) (s1Base p + r) = true ∧ skS1 p r + sLen p ≤ p.skLen) ∧
    (∀ i < p.k, decChk p p.ℓ i 0 (.x25, skS2 p i) (sLen p) (s2Base p + i) = true ∧ skS2 p i + sLen p ≤ p.skLen) ∧
    (∀ i < p.k, decChk p p.ℓ p.k i (.x25, skT0 p i) 416 (t0Base p + i) = true ∧ skT0 p i + 416 ≤ p.skLen) ∧
    hashChk (sgR p) (sgW p) [⟨.x25, 32, 32⟩, ⟨.x27, 0, 32⟩, ⟨.x26, 0, 64⟩] ⟨.x28, oMS, 64⟩ = true ∧
    idChk p [(sc 0, 200), (sc 200, 640), (sc oMS, 64)] p.ℓ p.k p.k = true ∧ inB (sgB p) (sc oMS) 64 = true ∧
    (p.η, p.η) ∈ bitPackParams ∧ 64 ≤ p.skLen := by
  simp only [dChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, hη⟩, hsk⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6, hη, hsk⟩

theorem sLen_eq (p : Params) : sLen p = 32 * bitlen (p.η + p.η) := by rw [← Nat.two_mul]

end VG.Proof.MlDsa.AArch64.Sign
