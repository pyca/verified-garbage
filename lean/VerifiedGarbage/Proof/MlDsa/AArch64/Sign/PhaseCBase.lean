module

import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackCall
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseD
import VerifiedGarbage.Proof.MlDsa.Sign.Mem
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Blocks
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA signing on AArch64: the commitment of an iteration

The values of iteration `t` of the loop: `Â`, `y`, `ŷ`, `w` and `c̃` (`Am`,
`Yv`, `YHv`, `Wv`, `CTv`), with `y[r]` from `ExpandMask(ρ″, κ + r)` for
`κ = ℓt`, `ŷ[r] = NTT(y[r])`, `w[i] = NTT⁻¹(∑_j Â[i, j] ŷ[j])` and
`c̃ = H(μ ‖ w1Encode(w₁), λ/4)`; that the `t` iterations before were rejected
(within `maxBounds`, `RejT`); the two bytes of `κ` (`setKappa_okB`); and the
layout checks of the commitment's pieces (`ikChk`, `ilChk`, `mChk`, `wChk`,
`hChk`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlKem.AArch64 (Only Keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable (p : Params)

/-- `Â[i, j]`, within `maxBounds`. -/
abbrev Am (σ : State) (i j : Nat) : Poly := aF maxBounds.rejNTT (rhoOf p σ) i j

/-- The slots of `h`, `y`, `ŷ` and `w`. -/
abbrev yBase : Nat := 5 + p.k
abbrev yhBase : Nat := 5 + p.k + p.ℓ
abbrev wBase : Nat := 5 + p.k + 2 * p.ℓ

/-- `y[r]`, `ŷ[r]`, `w[i]` and `c̃` of the iteration with counter `κ`. -/
abbrev Yv (σ : State) (κ r : Nat) : Poly := toRq (yF p (rppOf p σ) κ r)
abbrev YHv (σ : State) (κ r : Nat) : Poly := yhF p (rppOf p σ) κ r
abbrev Wv (σ : State) (κ i : Nat) : Poly := wF p (Am p σ) (rppOf p σ) κ i
abbrev CTv (σ : State) (κ : Nat) : List Byte := ctF p (Am p σ) (muOf σ) (rppOf p σ) κ

/-- The iterations before `t` were rejected, within `maxBounds`. -/
abbrev RejT (σ : State) (t : Nat) : Prop :=
  Rej p (amat p (Am p σ)) ((List.range p.ℓ).map (S1v p σ)) ((List.range p.k).map (S2v p σ))
    ((List.range p.k).map (T0v p σ)) (muOf σ) (rppOf p σ) maxBounds 0 t

end

theorem aVal_ij {p : Params} {σ : State} {i j : Nat} (hj : j < p.ℓ) : aVal p σ (p.ℓ * i + j) = Am p σ i j := by
  have hl : 0 < p.ℓ := by omega_arith
  have e1 : (p.ℓ * i + j) / p.ℓ = i := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hl, Nat.div_eq_of_lt hj, Nat.zero_add]
  have e2 : (p.ℓ * i + j) % p.ℓ = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  simp only [aVal, e1, e2]

/-! ## The head of an iteration -/

/-- A piece that writes `ws` keeps what decoding left (but `KAP` and `CNT`). -/
def ikChk (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  idChk p ws p.ℓ p.k p.k && keepB (sgR p) (sgW p) ws (sc oMS) 64

/-- A piece that writes `ws` keeps what decoding left, `KAP` and `CNT`. -/
def ilChk (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  ikChk p ws && keepB (sgR p) (sgW p) ws (sc oKAP) 8 && keepB (sgR p) (sgW p) ws (sc oCNT) 8

/-! ## `κ + r` -/

theorem integerToBytes_two (x : Nat) : integerToBytes x 2 = [BitVec.ofNat 8 x, BitVec.ofNat 8 (x / 256)] := by
  simp [integerToBytes, List.range_succ]

theorem kappa_bytes {x : Nat} (hx : x < 2 ^ 16) :
    [(BitVec.ofNat 64 x).setWidth 8, (BitVec.ofNat 64 x >>> 8).setWidth 8] = integerToBytes x 2 := by
  rw [integerToBytes_two]
  congr 1
  · apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega_arith
  · congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
    omega_arith

theorem add_one_ne (a : Addr) : a ≠ a + 1 := by
  intro h
  have := congrArg BitVec.toNat h
  have ha := a.isLt
  rw [BitVec.toNat_add] at this
  have e1 : (1 : BitVec 64).toNat = 1 := rfl
  rw [e1] at this
  omega_arith

theorem bytes2_write (m : Mem) (a : Addr) (v w : Byte) :
    bytesAt ((m.writeW a v).writeW (a + 1) w) a 2 = [v, w] := by
  show [((m.writeW a v).writeW (a + 1) w) (a + BitVec.ofNat 64 0),
    ((m.writeW a v).writeW (a + 1) w) (a + BitVec.ofNat 64 1)] = _
  have e0 : a + BitVec.ofNat 64 0 = a := BitVec.add_zero a
  have e1 : a + BitVec.ofNat 64 1 = a + 1 := rfl
  rw [e0, e1, VG.Proof.MlKem.writeW8_apply, VG.Proof.MlKem.writeW8_apply, ifn (add_one_ne a), ifp rfl,
    VG.Proof.MlKem.writeW8_apply, ifp rfl]

/-- `κ + r` to `MS + 64`, as the two bytes of `ExpandMask`'s seed. -/
theorem setKappa_okB {D : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay D rbs wbs s) {r x : Nat}
    (hr : r < 4096) (hx : x + r < 2 ^ 16) (h1 : inB (rbs ++ wbs) (sc oKAP) 8 = true)
    (h2 : inB wbs (sc (oMS + 64)) 2 = true) (hk : s.mem.readW (pa s (sc oKAP)) 64 = BitVec.ofNat 64 x) :
    WP isa (.block (setKappa r)) s fun s' => PPostB D s s' [(sc (oMS + 64), 2)] ∧
      s'.gpr .x24 = s.gpr .x24 ∧
      bytesAt s'.mem (pa s (sc (oMS + 64))) 2 = integerToBytes (x + r) 2 := by
  have e65 : pa s (sc (oMS + 65)) = pa s (sc (oMS + 64)) + 1 := (pa_sc_add s (oMS + 64) 1).symm
  have w2 := L.inW h2
  have c0 : (⟨pa s (sc (oMS + 64)), 2⟩ : Region).Contains (pa s (sc (oMS + 64))) 1 := by
    have := Offset.contains_base (pa s (sc (oMS + 64))) (d := 0) (n := 1) (k := 2) (by omega_arith) (by decide)
    rwa [BitVec.add_zero] at this
  have c1 : (⟨pa s (sc (oMS + 64)), 2⟩ : Region).Contains (pa s (sc (oMS + 65))) 1 := by
    rw [e65]; exact Offset.contains_base _ (d := 1) (by omega_arith) (by decide)
  have i0 : InRegions s.wr (pa s (sc (oMS + 64))) 1 := by
    have := inRegions_sub (off := 0) (l := 1) w2 (by omega_arith) (by decide)
    rwa [BitVec.add_zero] at this
  have i1 : InRegions s.wr (pa s (sc (oMS + 65))) 1 := by
    rw [e65]; exact inRegions_sub (off := 1) (l := 1) w2 (by omega_arith) (by decide)
  refine WP.mono (setKappa_run r hr s (L.inR h1) i0 i1) fun s' ⟨hm, k⟩ => ?_
  have hf : Frame [⟨pa s (sc (oMS + 64)), 2⟩] s.mem s'.mem := by
    rw [hm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _ c1
  refine ⟨postB_of_keep k (by decide) hf, k.get .x24, ?_⟩
  rw [hm, e65, bytes2_write, hk, ofNat64_add, kappa_bytes hx]

/-! ## `y` and `ŷ` -/

def icmChk (p : Params) (ws : List (Ptr × Nat)) (r : Nat) : Bool :=
  ilChk p ws && famChk (sgR p) (sgW p) ws (yBase p) r && famChk (sgR p) (sgW p) ws (yhBase p) r

/-- What `y[r]` and `ŷ[r]` need of the layout. -/
def mChk (p : Params) (r : Nat) : Bool :=
  let y := pS (yBase p + r)
  let yh := pS (yhBase p + r)
  let w1 : List (Ptr × Nat) := [(sc (oMS + 64), 2)]
  let w2 : List (Ptr × Nat) := [(y, 1024), (sc oPS, 2048)]
  let w3 : List (Ptr × Nat) := [(yh, 1024)]
  let w4 : List (Ptr × Nat) := [(yh, 1024), (sc oPS, 1024)]
  icmChk p w1 r && inB (sgB p) (sc oKAP) 8 && inB (sgW p) (sc (oMS + 64)) 2 && maskChkS (sgR p) (sgW p) y &&
    icmChk p w2 r && copyChk (sgR p) (sgW p) yh y 1024 && icmChk p w3 r && famChk (sgR p) (sgW p) w3 (yBase p) (r + 1) &&
    ipChkS (sgR p) (sgW p) yh && icmChk p w4 r && famChk (sgR p) (sgW p) w4 (yBase p) (r + 1) &&
    decide (p.ℓ * 813 + r < 2 ^ 16) && decide (r < 4096) && decide (p.γ₁ = 2 ^ 17 ∨ p.γ₁ = 2 ^ 19)

/-! ## `w` -/

def icwChk (p : Params) (ws : List (Ptr × Nat)) (i : Nat) : Bool :=
  icmChk p ws p.ℓ && famChk (sgR p) (sgW p) ws (wBase p) i

/-- What `w[i]` needs of the layout. -/
def wChk (p : Params) (i : Nat) : Bool :=
  let w := pS (wBase p + i)
  (List.range p.ℓ).all (fun j => mulChk (sgR p) (sgW p) w (aP p i j) (yhP p j)) && ipChkS (sgR p) (sgW p) w &&
    icwChk p [(w, 1024)] i && icwChk p [(w, 1024), (sc oPS, 1024)] i && decide (0 < p.ℓ)

/-! ## `w₁` and `c̃` -/

/-- The encodings of the first `i` polynomials of `w₁`. -/
abbrev w1Enc (p : Params) (σ : State) (κ i : Nat) : List Byte :=
  (List.range i).flatMap fun j => simpleBitPack (w1F p (Am p σ) (rppOf p σ) κ j) (w1Max p)

/-- What `w1Encode(w₁[i])` needs of the layout. -/
def hChk (p : Params) (i : Nat) : Bool :=
  let o := sc (oW1+w1Len p*i)
  rwChk (sgR p) (sgW p) (wP p i) 1024 o (w1Len p) &&
    icwChk p [(o,w1Len p)] p.k &&
    keepB (sgR p) (sgW p) [(o,w1Len p)] (sc oW1) (w1Len p*i) && decide (p.γ₂∈gamma2s)


end VG.Proof.MlDsa.AArch64.Sign
