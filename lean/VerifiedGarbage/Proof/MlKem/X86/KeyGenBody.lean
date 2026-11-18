module

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MlKem.X86.TopKem
public import VerifiedGarbage.Impl.MlKem.X86.KeyGen
import VerifiedGarbage.Proof.MlKem.X86.TopLocal
import VerifiedGarbage.Proof.MlKem.X86.TopSeq
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.X86.TopKem
meta import VerifiedGarbage.Proof.MlKem.X86.TopLocal
meta import VerifiedGarbage.Proof.MlKem.X86.TopSeq
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.MlKem.X86.Extra
public import VerifiedGarbage.Proof.MlKem.X86.TopKeep
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.MlKem.KPke
public import VerifiedGarbage.Proof.Sha256.X86.Lit
public import VerifiedGarbage.Proof.Sha3.X86.Lit
public import VerifiedGarbage.Proof.MlKem.X86.Top
public import VerifiedGarbage.Impl.MlKem.X86.Kem
meta import VerifiedGarbage.Impl.MlKem.X86.KeyGen
meta import VerifiedGarbage.Proof.MlKem.X86.Extra
meta import VerifiedGarbage.Proof.MlKem.X86.TopKeep
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.MlKem.KPke
meta import VerifiedGarbage.Proof.Sha256.X86.Lit
meta import VerifiedGarbage.Proof.Sha3.X86.Lit
meta import VerifiedGarbage.Proof.MlKem.X86.Top
meta import VerifiedGarbage.Impl.MlKem.X86.Kem

/-! ### `MlKem.X86.KeyGenFin`, which this module and modules that import it used -/

section

/-! ### `MlKem.X86.KeyGenRow`, which this module and modules that import it used -/

section

/-! ### `MlKem.X86.KeyGenPre`, which only this module used -/

section

/-!
# ML-KEM on x86 (32-bit): the setting of key generation

The layout of the arguments (`Y L`: `seed`, `ek`, `dk`, `scratch`, and the
88 bytes of stack), which each parameter set's contract implies; the public
data, which includes `ρ`; and `d`, `z` and the values the body computes from
them.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- `seed` (64 bytes, read), `ek`, `dk` and `scratch` (written); 88 bytes of stack. -/
def Y (L : KemLay) : Lay := ⟨[(64, false), (L.p.ekLen, true), (L.p.dkLen, true), (L.scratch, true)], 3, 88⟩

section
variable (s₀ : State)
/-- `d`. -/
abbrev d : List Byte := bytesAt s₀.mem (Buf.addr s₀ ⟨0, 0, 32⟩) 32
/-- `z`. -/
abbrev z : List Byte := bytesAt s₀.mem (Buf.addr s₀ ⟨0, 32, 32⟩) 32
end

/-- What keygen may leak: `ρ`. -/
abbrev lk (L : KemLay) (s₀ : State) : List Byte := KPke.kgRho L.p (d s₀)

theorem addr0 (s₀ : State) (i : Nat) : Buf.addr s₀ ⟨i, 0, 32⟩ = (arg s₀ i).setWidth 64 := by
  simp only [Buf.addr, Buf.ptr, BitVec.add_zero]

/-- A taint check of code with `scratch` at `(Y L).sc`, through `esi`. -/
tactic_template "yk_taint" : tactic => `(tactic| ((try simp only [show ∀ L, (Y L).sc = 3 from fun _ => rfl]); (try simp only
                   [ptrTo, reduceIte, Nat.reduceEqDiff, List.cons_append, List.nil_append]); taint_rfl))

end VG.Proof.MlKem.X86.KeyGen

end

end

/-! ### `MlKem.X86.KeyGenG`, which this module and modules that import it used -/

section

/-!
# ML-KEM on x86 (32-bit): the start of key generation

`esi = scratch`, the word `kgACC` set to 1, and `ρ ‖ σ = G(d ‖ k)` at `kgRS`
(`start_piece`), which is `P 0`: the state of the loop over `N` that computes
`ŝ` and `ê`.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt Repr stateAt squeezeFrom absorb pad sha3_512 sha3Suffix shakeSuffix)

/-! ## Buffers -/

abbrev bSE (j : Nat) : Buf := ⟨3, 1024 * j, 1024⟩

section
variable (L : KemLay)
abbrev bT : Buf := ⟨3, L.kgT, 1024⟩
abbrev bA : Buf := ⟨3, L.kgA, 1024⟩
abbrev bP : Buf := ⟨3, L.kgP, 1024⟩
abbrev bNS : Buf := ⟨3, L.kgNS, 1024⟩
abbrev bSS : Buf := ⟨3, L.kgSS, 2048⟩
abbrev bRS : Buf := ⟨3, L.kgRS, 64⟩
abbrev bRho : Buf := ⟨3, L.kgRS, 32⟩
abbrev bSig : Buf := ⟨3, L.kgRS + 32, 32⟩
abbrev bNB : Buf := ⟨3, L.kgRS + 64, 1⟩
abbrev bPRF : Buf := ⟨3, L.kgPRF, 128⟩
abbrev bACC : Buf := ⟨3, L.kgACC, 4⟩

/-- `σ ‖ N`, `PRF`'s input. -/
abbrev bSigN : Buf := ⟨3, L.kgRS + 32, 33⟩
end

section
variable (L : KemLay) (s₀ : State)
/-- `ŝ[j]` (`j < k`) or `ê[j - k]`. -/
abbrev seP (j : Nat) : Poly := ntt (cbd (KPke.kgSigma L.p (d s₀)) j)
end

/-- The facts of the layout that the start of key generation uses. -/
class GOK (L : KemLay) : Prop where
  rs : (Y L).ok (bSig L) = true ∧ (Y L).ok (bRS L) = true ∧ (Y L).okW (bACC L) = true ∧
    (Y L).okW (bNB L) = true ∧ (Y L).apart (bACC L) [⟨3, L.kgRS + 64, 1⟩] = true
  g : ((Y L).okW ⟨3, L.kgST, 200⟩ && (Y L).okW ⟨3, L.kgWK, 640⟩ && (Y L).ok ⟨0, 0, 32⟩ &&
    (Y L).ok ⟨3, L.kgRS + 64, 1⟩ && (Y L).okW ⟨3, L.kgRS, 64⟩ && (Y L).sep ⟨3, L.kgST, 200⟩ ⟨3, L.kgWK, 640⟩ &&
    (Y L).sep ⟨0, 0, 32⟩ ⟨3, L.kgST, 200⟩ && (Y L).sep ⟨0, 0, 32⟩ ⟨3, L.kgWK, 640⟩ &&
    (Y L).sep ⟨3, L.kgRS + 64, 1⟩ ⟨3, L.kgST, 200⟩ && (Y L).sep ⟨3, L.kgRS + 64, 1⟩ ⟨3, L.kgWK, 640⟩ &&
    (Y L).sep ⟨3, L.kgST, 200⟩ ⟨3, L.kgRS, 64⟩ && (Y L).sep ⟨3, L.kgRS, 64⟩ ⟨3, L.kgWK, 640⟩) = true ∧
    (Y L).apart (bACC L) [⟨3, L.kgST, 200⟩, ⟨3, L.kgWK, 640⟩, ⟨3, L.kgRS, 64⟩] = true
variable {L : KemLay}

/-- While `ŝ` and `ê` are computed: `ŝ[j]` or `ê[j - k]` for `j < N`. -/
structure P (L : KemLay) (N : Nat) (s₀ s : State) : Prop where
  ctx : Ctx (Y L) s₀ s
  acc : s.mem.readW (Buf.addr s₀ (bACC L)) 32 = 1
  rho : bytesAt s.mem (Buf.addr s₀ (bRho L)) 32 = KPke.kgRho L.p (d s₀)
  sig : bytesAt s.mem (Buf.addr s₀ (bSig L)) 32 = KPke.kgSigma L.p (d s₀)
  se : ∀ j < N, PolyIs s.mem (Buf.addr s₀ (bSE j)) (seP L s₀ j)

/-- After `kgACC` is set. -/
structure I1 (L : KemLay) (s₀ s : State) : Prop where
  ctx : Ctx (Y L) s₀ s
  acc : s.mem.readW (Buf.addr s₀ (bACC L)) 32 = 1

/-- After the `k` of `G`'s input is stored. -/
structure I2 (L : KemLay) (s₀ s : State) : Prop extends I1 L s₀ s where
  nb : bytesAt s.mem (Buf.addr s₀ (bNB L)) 1 = [BitVec.ofNat 8 L.p.k]

theorem rs_split [GOK L] {s₀ : State} (hp : TPre (Y L) s₀) {m : Mem} {o : List Byte}
    (h : bytesAt m (Buf.addr s₀ (bRS L)) 64 = o) :
    bytesAt m (Buf.addr s₀ (bRho L)) 32 = o.take 32 ∧ bytesAt m (Buf.addr s₀ (bSig L)) 32 = o.drop 32 := by
  have e₁ : Buf.addr s₀ (bRho L) = Buf.addr s₀ (bRS L) := rfl
  have e₂ : Buf.addr s₀ (bSig L) = Buf.addr s₀ (bRS L) + BitVec.ofNat 64 32 := by
    rw [Buf.addr_eq hp (b := bSig L) GOK.rs.1, Buf.addr_eq hp (b := bRS L) GOK.rs.2.1, BitVec.add_assoc,
      ← BitVec.ofNat_add]
  refine ⟨by rw [e₁, ← bytesAt_take _ _ (show 32 ≤ 64 by decide), h], ?_⟩
  rw [e₂, ← h, bytesAt_drop _ _ (show 32 ≤ 64 by decide)]

/-- The start, then `c`. -/
theorem start_piece [GOK L] {Q : State → State → Prop} {c : Prog isa}
    (hc : Piece (TPre (Y L)) (TPub (Y L) (lk L)) (P L 0) Q c) :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (fun s₀ s => s = P0 s₀) Q
      (.seq (.block [.mov .esi (.mem (at_ .esp 32))]) <|
        .seq (.block [.mov .eax (.imm 1), .store (at_ .esi L.kgACC) .eax]) <|
        .seq (.block (st8 (L.kgRS + 64) L.p.k)) <|
        .seq (hash2 3 L.kgST L.kgWK 72 6 ⟨0, 0, 32⟩ ⟨3, L.kgRS + 64, 1⟩ ⟨3, L.kgRS, 64⟩) c) := by
  obtain ⟨-, -, o₃, o₄, a₁⟩ := GOK.rs (L := L)
  obtain ⟨g₁, g₂⟩ := GOK.g (L := L)
  refine Piece.seq (ldsc_piece (Y := Y L) (by yk_taint)) ?_
  refine Piece.seq (B := I1 L) (st32_piece (Y := Y L) L.kgACC 1 o₃ (by taint_rfl) (fun _ _ _ h => h)
    fun s₀ s s' hp _ h' m' => ⟨h', by rw [m']; exact Mem.readW_writeW_self32 _ _ _⟩) ?_
  refine Piece.seq (B := I2 L) (st8_piece (Y := Y L) (L.kgRS + 64) L.p.k o₄ (by taint_rfl)
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' m' => ⟨⟨h', ?_⟩, ?_⟩) ?_
  · rw [← h.acc, m']; exact keepW hp (N := 0) (by rdecide) a₁ (frW8 (Y := Y L))
  · rw [m']
    refine bytesAt_eq (L := [BitVec.ofNat 8 L.p.k]) rfl fun i hi => ?_
    obtain rfl : i = 0 := by omega_using [hi]
    simp only [BitVec.add_zero, writeW8_apply, List.getElem_cons_zero]
    exact (ite_eq_left (rfl : Buf.addr s₀ (bNB L) = Buf.addr s₀ ⟨(Y L).sc, L.kgRS + 64, 1⟩)).trans
      (by rw [BitVec.setWidth_ofNat_of_le (by decide)])
  refine Piece.seq (hash2_piece (Y := Y L) L.kgST L.kgWK 72 6 ⟨0, 0, 32⟩ ⟨3, L.kgRS + 64, 1⟩ ⟨3, L.kgRS, 64⟩
    rate72 g₁ (by rdecide) (by rdecide) (by rdecide) (by rdecide) (by taint_rfl) (by yk_taint) (by yk_taint)
    (by yk_taint) (by yk_taint) (fun _ _ _ h => h.ctx)
    fun s₀ s s' hp h h' fr out => ?_) hc
  have hd : bytesAt s.mem (Buf.addr s₀ ⟨0, 0, 32⟩) 32 = d s₀ :=
    h.ctx.roBytes hp (b := ⟨0, 0, 32⟩) (by rdecide) rfl
  rw [hd, h.nb, show (BitVec.ofNat 32 6).setWidth 8 = sha3Suffix from sha3Suffix32, ← padded, ← sha3_512_eq] at out
  obtain ⟨r₁, r₂⟩ := rs_split hp out
  refine ⟨h', ?_, r₁, r₂, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  rw [← h.acc]; exact keepW hp (by rdecide) g₂ fr

end VG.Proof.MlKem.X86.KeyGen

end

end

/-!
# ML-KEM on x86 (32-bit): `t̂` in key generation

Row `i` of `Â` (`kgRow L i`): each entry `Â[i, j]` is sampled from `ρ ‖ j ‖ i`,
masked by the value `vg_mlkem_sample_ntt` returned, which is ANDed into
`kgACC` (`entry0_piece`, `entry_piece`), and multiplied by `ŝ[j]` into
`t̂[i]`; then `ê[i]` is added and `t̂[i]` encoded into `ek` (`row_piece`).

`B k e` is what holds after `k` entries and `e` rows: `kgACC` is 0 or 1; if
1, the first `k` samples succeeded, and the first `e` rows of `ek` are those
of `ek_PKE` for the matrix `aM` they sampled; if 0, one of the `k²` samples
failed within `minIterations` iterations.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- Row `i` of `ek`. -/
abbrev bEK (i : Nat) : Buf := ⟨1, 384 * i, 384⟩

section
variable (L : KemLay) (s₀ : State)
/-- The seed of the `k`th entry of `Â`, `Â[k / k, k % k]`. -/
abbrev mS (k : Nat) : List Byte := matSeed (KPke.kgRho L.p (d s₀)) (k / L.p.k) (k % L.p.k)
/-- `Â[i, j]`, if sampled. -/
noncomputable abbrev aM (i j : Nat) : Poly := sv (matSeed (KPke.kgRho L.p (d s₀)) i j)

/-- `Â[i, 0] ×_T ŝ[0] + … + Â[i, j - 1] ×_T ŝ[j - 1]`. -/
noncomputable abbrev part (i j : Nat) : Poly := KPke.dotK (aM L s₀ i) (seP L s₀) j
end

/-- `kgACC`. -/
abbrev accV (L : KemLay) (s₀ s : State) : BitVec 32 := s.mem.readW (Buf.addr s₀ (bACC L)) 32

/-- See the module documentation. -/
structure B (L : KemLay) (k e : Nat) (s₀ s : State) : Prop where
  ctx : Ctx (Y L) s₀ s
  rho : bytesAt s.mem (Buf.addr s₀ (bRho L)) 32 = KPke.kgRho L.p (d s₀)
  se : ∀ j < 2 * L.p.k, PolyIs s.mem (Buf.addr s₀ (bSE j)) (seP L s₀ j)
  acc : accV L s₀ s = 0 ∨ accV L s₀ s = 1
  ok : accV L s₀ s = 1 → ∀ k' < k, ∃ a, Samp (mS L s₀ k') a
  fail : accV L s₀ s = 0 → ∃ k' < L.p.k * L.p.k, sampleNTT minIterations (mS L s₀ k') = none
  ek : accV L s₀ s = 1 → ∀ i < e,
    bytesAt s.mem (Buf.addr s₀ (bEK i)) 384 = encode12 (KPke.kgT L.p (aM L s₀) (d s₀) i)

/-- Whether `bs` is apart from `ρ`, `ŝ` and `ê`. -/
def safeS (L : KemLay) (bs : List Buf) : Bool :=
  (Y L).apart (bRho L) bs && (List.range (2 * L.p.k)).all fun j => (Y L).apart (bSE j) bs

/-- Whether `bs` is also apart from `kgACC` and `ek`. -/
def safe (L : KemLay) (bs : List Buf) : Bool :=
  (Y L).apart (bACC L) bs && safeS L bs && (List.range L.p.k).all fun i => (Y L).apart (bEK i) bs

variable {L : KemLay}

/-- What `B` states of `ρ`, `ŝ` and `ê`, kept. -/
theorem keepS {s₀ : State} {m m' : Mem} (hp : TPre (Y L) s₀) {bs : List Buf} {M : Nat} (hM : M + 16 ≤ (Y L).stk)
    (hs : safeS L bs = true) (fr : Frame (FR s₀ bs M) m m')
    (h₁ : bytesAt m (Buf.addr s₀ (bRho L)) 32 = KPke.kgRho L.p (d s₀))
    (h₂ : ∀ j < 2 * L.p.k, PolyIs m (Buf.addr s₀ (bSE j)) (seP L s₀ j)) :
    bytesAt m' (Buf.addr s₀ (bRho L)) 32 = KPke.kgRho L.p (d s₀) ∧
      ∀ j < 2 * L.p.k, PolyIs m' (Buf.addr s₀ (bSE j)) (seP L s₀ j) := by
  simp only [safeS, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hs
  exact ⟨by rw [keepBytes hp hM hs.1 fr]; exact h₁, fun j hj => keepPoly hp hM (hs.2 j hj) fr (h₂ j hj)⟩

theorem B.keep {k e : Nat} {s₀ s s' : State} (hp : TPre (Y L) s₀) {bs : List Buf} {M : Nat}
    (hM : M + 16 ≤ (Y L).stk) (hs : safe L bs = true) (he : e ≤ L.p.k)
    (fr : Frame (FR s₀ bs M) s.mem s'.mem) (h : B L k e s₀ s) (c : Ctx (Y L) s₀ s') : B L k e s₀ s' := by
  simp only [safe, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hs
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hs
  have ea : accV L s₀ s' = accV L s₀ s := keepW hp hM h₁ fr
  obtain ⟨k₁, k₂⟩ := keepS hp hM h₂ fr h.rho h.se
  refine ⟨c, k₁, k₂, ea ▸ h.acc, fun e₁ => h.ok (ea ▸ e₁), fun e₁ => h.fail (ea ▸ e₁), fun e₁ i hi => ?_⟩
  rw [keepBytes hp hM (h₃ i (by omega_using [he, hi])) fr]
  exact h.ek (ea ▸ e₁) i hi

/-- Before entry `(i, j)`: and `t̂[i]` so far, if `0 < j`. -/
structure R (L : KemLay) (i j : Nat) (s₀ s : State) : Prop extends B L (L.p.k * i + j) i s₀ s where
  t : 0 < j → Reduced s.mem (Buf.addr s₀ (bT L)) ∧
    (accV L s₀ s = 1 → polyAt s.mem (Buf.addr s₀ (bT L)) = part L s₀ i j)

theorem R.keep {i j : Nat} (hi : i < L.p.k) {s₀ s s' : State} (hp : TPre (Y L) s₀) {bs : List Buf} {M : Nat}
    (hM : M + 16 ≤ (Y L).stk) (hs : safe L bs = true) (hT : (Y L).apart (bT L) bs = true)
    (fr : Frame (FR s₀ bs M) s.mem s'.mem) (h : R L i j s₀ s) (c : Ctx (Y L) s₀ s') : R L i j s₀ s' := by
  have k := h.toB.keep hp hM hs (by omega_using [hi]) fr c
  have ea : accV L s₀ s' = accV L s₀ s :=
    keepW hp hM (by simp only [safe, Bool.and_eq_true] at hs; exact hs.1.1) fr
  refine ⟨k, fun hj => ⟨keepRed hp hM hT fr (h.t hj).1, fun e₁ => ?_⟩⟩
  rw [polyAt_congr (Top.keep hp hM hT fr)]
  exact (h.t hj).2 (ea ▸ e₁)

/-! ## Bytes -/

theorem st8_byte {s₀ : State} (m : Mem) (o v : Nat) :
    bytesAt (m.writeW (Buf.addr s₀ ⟨(Y L).sc, o, 1⟩) ((BitVec.ofNat 32 v).setWidth 8)) (Buf.addr s₀ ⟨3, o, 1⟩) 1 =
      [BitVec.ofNat 8 v] := by
  refine bytesAt_eq (L := [BitVec.ofNat 8 v]) rfl fun i hi => ?_
  obtain rfl : i = 0 := by omega_using [hi]
  simp only [BitVec.add_zero, writeW8_apply, List.getElem_cons_zero]
  refine (ite_eq_left (rfl : Buf.addr s₀ ⟨3, o, 1⟩ = Buf.addr s₀ ⟨(Y L).sc, o, 1⟩)).trans ?_
  rw [BitVec.setWidth_ofNat_of_le (by decide)]

section
variable (L : KemLay)
/-- `ρ ‖ j ‖ i`, the seed of `Â[i, j]`. -/
abbrev bSeed : Buf := ⟨3, L.kgRS, 34⟩
abbrev bJ : Buf := ⟨3, L.kgRS + 32, 1⟩
abbrev bI : Buf := ⟨3, L.kgRS + 33, 1⟩
end

/-- The facts of the layout that the rows use. -/
class KgRowOK (L : KemLay) : Prop where
  seed : (Y L).ok (bJ L) = true ∧ (Y L).ok (bI L) = true ∧ (Y L).ok (bRho L) = true ∧
    (Y L).okW (bJ L) = true ∧ (Y L).okW (bI L) = true
  nb : safe L [⟨3, L.kgRS + 32, 1⟩] = true ∧ safe L [⟨3, L.kgRS + 33, 1⟩] = true ∧
    (Y L).apart (bT L) [⟨3, L.kgRS + 32, 1⟩] = true ∧ (Y L).apart (bT L) [⟨3, L.kgRS + 33, 1⟩] = true ∧
    (Y L).apart (bJ L) [⟨3, L.kgRS + 33, 1⟩] = true
  samp : safe L [bA L, bSS L] = true ∧ (Y L).apart (bT L) [bA L, bSS L] = true ∧
    ((Y L).ok ⟨3, L.kgRS, 34⟩ && (Y L).okW ⟨3, L.kgA, 1024⟩ && (Y L).okW ⟨3, L.kgSS, 2048⟩ &&
      (Y L).sep ⟨3, L.kgRS, 34⟩ ⟨3, L.kgA, 1024⟩ && (Y L).sep ⟨3, L.kgRS, 34⟩ ⟨3, L.kgSS, 2048⟩ &&
      (Y L).sep ⟨3, L.kgA, 1024⟩ ⟨3, L.kgSS, 2048⟩) = true
  mask : safeS L [bACC L, bA L] = true ∧ (∀ i < L.p.k, (Y L).apart (bEK i) [bACC L, bA L] = true) ∧
    (Y L).apart (bT L) [bACC L, bA L] = true ∧
    ((Y L).okW ⟨(Y L).sc, L.kgACC, 4⟩ && (Y L).okW ⟨(Y L).sc, L.kgA, 1024⟩ &&
      (Y L).sep ⟨(Y L).sc, L.kgACC, 4⟩ ⟨(Y L).sc, L.kgA, 1024⟩) = true
  mul : safe L [bT L, bNS L] = true ∧ safe L [bP L, bNS L] = true ∧ safe L [bT L] = true ∧
    (Y L).apart (bT L) [bP L, bNS L] = true ∧ (Y L).apart (bA L) [bP L, bNS L] = true ∧
    (Y L).apart (bACC L) [bT L, bNS L] = true ∧ (Y L).apart (bACC L) [bP L, bNS L] = true ∧
    ((Y L).okW (bT L) && (Y L).ok (bP L) && (Y L).sep (bT L) (bP L)) = true
  mul0 : ((Y L).okW (bT L) && (Y L).ok (bA L) && (Y L).ok (bSE 0) && (Y L).okW (bNS L) &&
    (Y L).sep (bT L) (bA L) && (Y L).sep (bT L) (bSE 0) && (Y L).sep (bT L) (bNS L) && (Y L).sep (bA L) (bNS L) &&
    (Y L).sep (bSE 0) (bNS L)) = true
  mulJ : ∀ j < L.p.k, ((Y L).okW (bP L) && (Y L).ok (bA L) && (Y L).ok (bSE j) && (Y L).okW (bNS L) &&
    (Y L).sep (bP L) (bA L) && (Y L).sep (bP L) (bSE j) && (Y L).sep (bP L) (bNS L) && (Y L).sep (bA L) (bNS L) &&
    (Y L).sep (bSE j) (bNS L)) = true
  row : ∀ i < L.p.k, ((Y L).okW (bT L) && (Y L).ok (bSE (L.p.k + i)) && (Y L).sep (bT L) (bSE (L.p.k + i))) = true ∧
    ((Y L).ok (bT L) && (Y L).okW (bEK i) && (Y L).sep (bT L) (bEK i)) = true ∧ safeS L [bEK i] = true ∧
    (Y L).apart (bACC L) [bEK i] = true ∧ ∀ i' < i, (Y L).apart (bEK i') [bEK i] = true

theorem seed_split [KgRowOK L] {s₀ : State} (hp : TPre (Y L) s₀) (m : Mem) :
    bytesAt m (Buf.addr s₀ (bSeed L)) 34 =
      bytesAt m (Buf.addr s₀ (bRho L)) 32 ++ (bytesAt m (Buf.addr s₀ (bJ L)) 1 ++ bytesAt m (Buf.addr s₀ (bI L)) 1) := by
  obtain ⟨o₁, o₂, o₃, -⟩ := KgRowOK.seed (L := L)
  have e₁ : Buf.addr s₀ (bJ L) = Buf.addr s₀ (bRho L) + BitVec.ofNat 64 32 := by
    rw [Buf.addr_eq hp (b := bJ L) o₁, Buf.addr_eq hp (b := bRho L) o₃, BitVec.add_assoc, ← BitVec.ofNat_add]
  have e₂ : Buf.addr s₀ (bI L) = Buf.addr s₀ (bJ L) + BitVec.ofNat 64 1 := by
    rw [Buf.addr_eq hp (b := bJ L) o₁, Buf.addr_eq hp (b := bI L) o₂, BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [e₂, e₁, ← bytesAt_add, show Buf.addr s₀ (bSeed L) = Buf.addr s₀ (bRho L) from rfl]
  exact bytesAt_add m _ 32 2

/-! ## The value returned by `SampleNTT`, and `kgACC` -/

theorem mS_eq (s₀ : State) {i j : Nat} (hj : j < L.p.k) : mS L s₀ (L.p.k * i + j) = matSeed (KPke.kgRho L.p (d s₀)) i j := by
  simp only [mS]
  rw [idx_div hj, idx_mod hj]

/-! ## An entry -/

/-- After `ρ ‖ j` is stored. -/
structure S1 (L : KemLay) (i j : Nat) (s₀ s : State) : Prop extends R L i j s₀ s where
  bj : bytesAt s.mem (Buf.addr s₀ (bJ L)) 1 = [BitVec.ofNat 8 j]

/-- After `ρ ‖ j ‖ i` is stored. -/
structure S2 (L : KemLay) (i j : Nat) (s₀ s : State) : Prop extends R L i j s₀ s where
  seed : bytesAt s.mem (Buf.addr s₀ (bSeed L)) 34 = matSeed (KPke.kgRho L.p (d s₀)) i j

/-- After `Â[i, j]` is sampled, `r` returned. -/
structure S3 (L : KemLay) (i j : Nat) (s₀ s : State) : Prop extends R L i j s₀ s where
  red : s.gpr .eax = 1 → Reduced s.mem (Buf.addr s₀ (bA L))
  out : Outcome (fun iters => sampleNTT iters (matSeed (KPke.kgRho L.p (d s₀)) i j)) (s.gpr .eax)
    (polyAt s.mem (Buf.addr s₀ (bA L)))

/-- After it is masked, and `kgACC` updated. -/
structure S4 (L : KemLay) (i j : Nat) (s₀ s : State) : Prop extends B L (L.p.k * i + j + 1) i s₀ s where
  t : 0 < j → Reduced s.mem (Buf.addr s₀ (bT L)) ∧
    (accV L s₀ s = 1 → polyAt s.mem (Buf.addr s₀ (bT L)) = part L s₀ i j)
  red : Reduced s.mem (Buf.addr s₀ (bA L))
  a : accV L s₀ s = 1 → polyAt s.mem (Buf.addr s₀ (bA L)) = aM L s₀ i j

variable [KgRowOK L]

/-- `ρ ‖ j ‖ i`, `Â[i, j]` sampled and masked, then `c`. -/
theorem sample_piece (i j : Nat) (hi : i < L.p.k) (hj : j < L.p.k) {Q : State → State → Prop} {c : Prog isa}
    (hc : Piece (TPre (Y L)) (TPub (Y L) (lk L)) (S4 L i j) Q c) :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (R L i j) Q
      (.seq (.block (st8 (L.kgRS + 32) j)) <| .seq (.block (st8 (L.kgRS + 33) i)) <|
        .seq (sampleC 3 ⟨3, L.kgRS, 34⟩ ⟨3, L.kgA, 1024⟩ ⟨3, L.kgSS, 2048⟩) (.seq (maskA L.kgACC L.kgA) c)) := by
  obtain ⟨n₁, n₂, n₃, n₄, n₅⟩ := KgRowOK.nb (L := L)
  obtain ⟨-, -, -, w₁, w₂⟩ := KgRowOK.seed (L := L)
  refine Piece.seq (B := S1 L i j) (st8_piece (Y := Y L) (L.kgRS + 32) j w₁ (by taint_rfl)
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' m' =>
      ⟨h.keep hi hp (M := 0) (by rdecide) n₁ n₃ (m' ▸ frW8 (Y := Y L)) h', by rw [m']; exact st8_byte _ _ _⟩) ?_
  refine Piece.seq (B := S2 L i j) (st8_piece (Y := Y L) (L.kgRS + 33) i w₂ (by taint_rfl)
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' m' => ?_) ?_
  · have k := h.keep hi hp (M := 0) (by rdecide) n₂ n₄ (m' ▸ frW8 (Y := Y L)) h'
    refine ⟨k, ?_⟩
    rw [seed_split hp, k.rho, keepBytes hp (N := 0) (by rdecide) n₅ (m' ▸ frW8 (Y := Y L)), h.bj, m', st8_byte]
    rfl
  obtain ⟨p₁, p₂, p₃⟩ := KgRowOK.samp (L := L)
  refine Piece.seq (B := S3 L i j) (sampleC_piece (Y := Y L) 3 L.kgRS 3 L.kgA 3 L.kgSS p₃ (by rdecide)
    (by yk_taint) (fun _ _ _ h => h.ctx) (fun s₀ s₀' s s' _ _ hq h h' => ?_)
    fun s₀ s s' hp h h' fr red out => ⟨h.keep hi hp (by rdecide) p₁ p₂ fr h', red, ?_⟩) ?_
  · rw [h.seed, h'.seed]; exact congrArg (matSeed · i j) hq.2.2
  · rw [h.seed] at out; exact out
  obtain ⟨q₁, q₂, q₃, q₄⟩ := KgRowOK.mask (L := L)
  refine Piece.seq (maskA_piece (Y := Y L) L.kgACC L.kgA q₄ (by taint_rfl) (fun _ _ _ h => h.ctx)
    fun s₀ s s' hp h h' fr ha hc => ?_) hc
  have fr' := fr2 fr
  have hr := outcome_01 h.out
  obtain ⟨s₁, s₂, s₃⟩ := acc_step h.acc hr
  have ea : accV L s₀ s' = accV L s₀ s &&& s.gpr .eax := ha
  rw [← ea] at s₁ s₂ s₃
  obtain ⟨k₁, k₂⟩ := keepS hp (M := 0) (by rdecide) q₁ fr' h.rho h.se
  obtain ⟨mr, ma⟩ := mask_poly hr hc h.red
  refine ⟨⟨h', k₁, k₂, s₁, fun e₁ k' hk' => ?_, fun e₁ => ?_, fun e₁ i' hi' => ?_⟩,
    fun hj => ⟨keepRed hp (by rdecide) q₃ fr' (h.t hj).1, fun e₁ => ?_⟩, mr, fun e₁ => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with hk' | rfl
    · exact h.ok (s₂ e₁).1 k' hk'
    · rw [mS_eq s₀ hj]
      rcases h.out with ⟨_, it, e⟩ | ⟨e, _⟩
      · exact ⟨_, it, e⟩
      · exact absurd ((s₂ e₁).2) (by rw [e]; decide)
  · rcases s₃ e₁ with e₂ | e₂
    · exact h.fail e₂
    · refine ⟨L.p.k * i + j, idx_lt hi hj, ?_⟩
      rw [mS_eq s₀ hj]
      rcases h.out with ⟨e, _⟩ | ⟨_, e⟩
      · exact absurd e (by rw [e₂]; decide)
      · exact e
  · rw [keepBytes hp (N := 0) (by rdecide) (q₂ i' (by omega_using [hi, hi'])) fr']
    exact h.ek (s₂ e₁).1 i' hi'
  · rw [polyAt_congr (Top.keep hp (by rdecide) q₃ fr')]
    exact (h.t hj).2 (s₂ e₁).1
  · refine (ma (s₂ e₁).2).trans ?_
    rcases h.out with ⟨_, it, e⟩ | ⟨e, _⟩
    · exact (sv_eq ⟨it, e⟩).symm
    · exact absurd ((s₂ e₁).2) (by rw [e]; decide)

/-- After `Â[i, j] ×_T ŝ[j]` is computed, for `0 < j`. -/
structure S5 (L : KemLay) (i j : Nat) (s₀ s : State) : Prop extends S4 L i j s₀ s where
  p : Reduced s.mem (Buf.addr s₀ (bP L)) ∧
    (accV L s₀ s = 1 → polyAt s.mem (Buf.addr s₀ (bP L)) = multiplyNTTs (aM L s₀ i j) (seP L s₀ j))

/-- Entry `(i, 0)`: `t̂[i] ← Â[i, 0] ×_T ŝ[0]`. -/
theorem entry0_piece (i : Nat) (hi : i < L.p.k) :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (R L i 0) (R L i 1) (kgEntry L i 0) := by
  obtain ⟨m₁, -, -, -, -, a₁, -, -⟩ := KgRowOK.mul (L := L)
  have hk : 0 < L.p.k := by omega_using [hi]
  refine sample_piece i 0 hi hk (mulC_piece (Y := Y L) 3 L.kgT 3 L.kgA 3 0 3 L.kgNS KgRowOK.mul0
    (by rdecide) (by yk_taint) (fun _ _ _ h => ⟨h.ctx, h.red, (h.se 0 (by omega_using [hi])).1⟩)
    fun s₀ s s' hp h h' fr post => ?_)
  have k := h.toB.keep hp (by rdecide) m₁ (by omega_using [hi]) fr h'
  have ea : accV L s₀ s' = accV L s₀ s := keepW hp (by rdecide) a₁ fr
  refine ⟨k, fun _ => ⟨post.1, fun e₁ => ?_⟩⟩
  rw [post.2, h.a (ea ▸ e₁), (h.se 0 (by omega_using [hi])).2]
  rfl

/-- Entry `(i, j + 1)`: `t̂[i] ← t̂[i] + Â[i, j + 1] ×_T ŝ[j + 1]`. -/
theorem entry_piece (i j : Nat) (hi : i < L.p.k) (hj : j + 1 < L.p.k) :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (R L i (j + 1)) (R L i (j + 2)) (kgEntry L i (j + 1)) := by
  obtain ⟨-, m₂, m₃, m₄, m₅, -, a₂, o₃⟩ := KgRowOK.mul (L := L)
  have a₃ : (Y L).apart (bACC L) [bT L] = true := by
    have := (KgRowOK.mul (L := L)).2.2.1; simp only [safe, Bool.and_eq_true] at this; exact this.1.1
  refine sample_piece i (j + 1) hi hj (.seq (B := S5 L i (j + 1))
    (mulC_piece (Y := Y L) 3 L.kgP 3 L.kgA 3 (1024 * (j + 1)) 3 L.kgNS (KgRowOK.mulJ (j + 1) hj) (by rdecide)
      (by yk_taint) (fun _ _ _ h => ⟨h.ctx, h.red, (h.se (j + 1) (by omega_using [hj])).1⟩)
      fun s₀ s s' hp h h' fr post => ?_) ?_)
  · have k := h.toB.keep hp (by rdecide) m₂ (by omega_using [hi]) fr h'
    have ea : accV L s₀ s' = accV L s₀ s := keepW hp (by rdecide) a₂ fr
    refine ⟨⟨k, fun hj' => ⟨keepRed hp (by rdecide) m₄ fr (h.t hj').1, fun e₁ => ?_⟩,
      keepRed hp (by rdecide) m₅ fr h.red, fun e₁ => ?_⟩, post.1, fun e₁ => ?_⟩
    · rw [polyAt_congr (Top.keep hp (by rdecide) m₄ fr)]; exact (h.t hj').2 (ea ▸ e₁)
    · rw [polyAt_congr (Top.keep hp (by rdecide) m₅ fr)]; exact h.a (ea ▸ e₁)
    · rw [post.2, h.a (ea ▸ e₁), (h.se (j + 1) (by omega_using [hj])).2]
  refine accC_piece add_verified add_nosp add_stack 3 L.kgT 3 L.kgP o₃ (by rdecide) (by yk_taint)
    (fun _ _ _ h => ⟨h.ctx, (h.t (Nat.succ_pos _)).1, h.p.1⟩) fun s₀ s s' hp h h' fr post => ?_
  have k := h.toB.keep hp (by rdecide) m₃ (by omega_using [hi]) fr h'
  have ea : accV L s₀ s' = accV L s₀ s := keepW hp (by rdecide) a₃ fr
  refine ⟨k, fun _ => ⟨post.1, fun e₁ => ?_⟩⟩
  rw [post.2, (h.t (Nat.succ_pos _)).2 (ea ▸ e₁), h.p.2 (ea ▸ e₁)]
  rfl

/-! ## A row -/

/-- `t̂[i]` is computed. -/
structure S6 (L : KemLay) (i : Nat) (s₀ s : State) : Prop extends B L (L.p.k * i + L.p.k) i s₀ s where
  t : Reduced s.mem (Buf.addr s₀ (bT L)) ∧
    (accV L s₀ s = 1 → polyAt s.mem (Buf.addr s₀ (bT L)) = KPke.kgT L.p (aM L s₀) (d s₀) i)

/-- Row `i`: `t̂[i] = Â[i] ∘ ŝ + ê[i]`, encoded into `ek`. -/
theorem row_piece (i : Nat) (hi : i < L.p.k) :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (B L (L.p.k * i) i) (B L (L.p.k * (i + 1)) (i + 1)) (kgRow L i) := by
  obtain ⟨o₁, o₂, o₃, o₄, o₅⟩ := KgRowOK.row i hi
  obtain ⟨-, -, m₃, -, -, -, -, -⟩ := KgRowOK.mul (L := L)
  have a₃ : (Y L).apart (bACC L) [bT L] = true := by
    simp only [safe, Bool.and_eq_true] at m₃; exact m₃.1.1
  refine (Piece.seqs0 (P := R L i) L.p.k (fun j hj => match j, hj with
    | 0, _ => entry0_piece i hi
    | j + 1, hj => entry_piece i j hi hj) ?_).mono (fun _ _ _ h => ⟨h, fun h => absurd h (Nat.lt_irrefl _)⟩)
    fun _ _ _ h => h
  refine Piece.seq (B := S6 L i) (accC_piece add_verified add_nosp add_stack 3 L.kgT 3 (1024 * (L.p.k + i))
    o₁ (by rdecide) (by yk_taint) (fun _ _ _ h => ⟨h.ctx, (h.t (by omega_using [hi])).1, (h.se (L.p.k + i) (by omega_using [hi])).1⟩)
    fun s₀ s s' hp h h' fr post => ?_) ?_
  · have k := h.toB.keep hp (by rdecide) m₃ (by omega_using [hi]) fr h'
    have ea : accV L s₀ s' = accV L s₀ s := keepW hp (by rdecide) a₃ fr
    refine ⟨k, post.1, fun e₁ => ?_⟩
    rw [post.2, (h.t (by omega_using [hi])).2 (ea ▸ e₁), (h.se (L.p.k + i) (by omega_using [hi])).2]
    rfl
  refine enc12C_piece (Y := Y L) 3 L.kgT 1 (384 * i) o₂ (by rdecide) (by yk_taint)
    (fun _ _ _ h => ⟨h.ctx, h.t.1⟩) fun s₀ s s' hp h h' fr post => ?_
  obtain ⟨k₁, k₂⟩ := keepS hp (by rdecide) o₃ fr h.rho h.se
  have ea : accV L s₀ s' = accV L s₀ s := keepW hp (by rdecide) o₄ fr
  refine ⟨h', k₁, k₂, ea ▸ h.acc, fun e₁ => h.ok (ea ▸ e₁), fun e₁ => h.fail (ea ▸ e₁), fun e₁ i' hi' => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hi' | rfl
  · rw [keepBytes hp (by rdecide) (o₅ i' hi') fr]; exact h.ek (ea ▸ e₁) i' hi'
  · rw [post, h.t.2 (ea ▸ e₁)]

/-- The `k` rows, then `c`. -/
theorem rows_piece {Q : State → State → Prop} {c : Prog isa}
    (h : Piece (TPre (Y L)) (TPub (Y L) (lk L)) (B L (L.p.k * L.p.k) L.p.k) Q c) :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (B L 0 0) Q (seqs ((List.range L.p.k).map (kgRow L)) c) :=
  Piece.seqs0 (P := fun i => B L (L.p.k * i) i) L.p.k row_piece h

end VG.Proof.MlKem.X86.KeyGen

end

end

/-!
# ML-KEM on x86 (32-bit): the keys in key generation

After the rows: `ρ` copied into `ek` (which completes `ek_PKE`), `ŝ` encoded
into `dk` (`dk_PKE`, `enc_piece`), `ek` copied into `dk`, `H(ek)` hashed into
`dk`, `z` copied into `dk`, and `kgACC` loaded to be returned (`fin_piece`).
`F n` is what holds after `n` of these steps.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt squeezeFrom absorb pad sha3Suffix)

section
variable (L : KemLay)
/-- `ρ` in `ek`. -/
abbrev bEKr : Buf := ⟨1, 384 * L.p.k, 32⟩
/-- `ByteEncode₁₂(ŝ[j])` in `dk`. -/
abbrev bDK (j : Nat) : Buf := ⟨2, 384 * j, 384⟩
/-- `ek` in `dk`. -/
abbrev bDKE : Buf := ⟨2, 384 * L.p.k, L.p.ekLen⟩
/-- `H(ek)` in `dk`. -/
abbrev bDKH : Buf := ⟨2, 768 * L.p.k + 32, 32⟩
/-- `z` in `dk`. -/
abbrev bDKZ : Buf := ⟨2, 768 * L.p.k + 64, 32⟩
end

/-- After `n` of the steps that write the keys. -/
structure F (L : KemLay) (n : Nat) (s₀ s : State) : Prop extends B L (L.p.k * L.p.k) L.p.k s₀ s where
  rhoE : 1 ≤ n → bytesAt s.mem (Buf.addr s₀ (bEKr L)) 32 = KPke.kgRho L.p (d s₀)
  dk : ∀ j < L.p.k, j + 2 ≤ n → bytesAt s.mem (Buf.addr s₀ (bDK j)) 384 = encode12 (seP L s₀ j)
  cp : L.p.k + 2 ≤ n → accV L s₀ s = 1 →
    bytesAt s.mem (Buf.addr s₀ (bDKE L)) L.p.ekLen = KPke.ekPKE L.p (aM L s₀) (d s₀)
  hh : L.p.k + 3 ≤ n → accV L s₀ s = 1 →
    bytesAt s.mem (Buf.addr s₀ (bDKH L)) 32 = H (KPke.ekPKE L.p (aM L s₀) (d s₀))
  zk : L.p.k + 4 ≤ n → bytesAt s.mem (Buf.addr s₀ (bDKZ L)) 32 = z s₀

/-- Whether `bs` is apart from what `B` and the first `n` steps state. -/
def safeF (L : KemLay) (bs : List Buf) (n : Nat) : Bool :=
  safe L bs && (n < 1 || (Y L).apart (bEKr L) bs) &&
    ((List.range L.p.k).all fun j => n < j + 2 || (Y L).apart (bDK j) bs) &&
    (n < L.p.k + 2 || (Y L).apart (bDKE L) bs) && (n < L.p.k + 3 || (Y L).apart (bDKH L) bs) &&
    (n < L.p.k + 4 || (Y L).apart (bDKZ L) bs)

variable {L : KemLay}

theorem F.keep {n : Nat} {s₀ s s' : State} (hp : TPre (Y L) s₀) {bs : List Buf} {M : Nat}
    (hM : M + 16 ≤ (Y L).stk) (hs : safeF L bs n = true) (fr : Frame (FR s₀ bs M) s.mem s'.mem) (h : F L n s₀ s)
    (c : Ctx (Y L) s₀ s') : F L n s₀ s' := by
  simp only [safeF, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hs
  obtain ⟨⟨⟨⟨⟨h₀, h₁⟩, h₂⟩, h₃⟩, h₄⟩, h₅⟩ := hs
  have k := h.toB.keep hp hM h₀ (Nat.le_refl _) fr c
  have ea : accV L s₀ s' = accV L s₀ s := keepW hp hM (by simp only [safe, Bool.and_eq_true] at h₀; exact h₀.1.1) fr
  refine ⟨k, fun hn => ?_, fun j hj hn => ?_, fun hn e₁ => ?_, fun hn e₁ => ?_, fun hn => ?_⟩
  · rcases h₁ with h₁ | h₁
    · omega_using [hn, h₁]
    · rw [keepBytes hp hM h₁ fr]; exact h.rhoE hn
  · rcases h₂ j hj with h₂ | h₂
    · omega
    · rw [keepBytes hp hM h₂ fr]; exact h.dk j hj hn
  · rcases h₃ with h₃ | h₃
    · omega_using [hn, h₃]
    · rw [keepBytes hp hM h₃ fr]; exact h.cp hn (ea ▸ e₁)
  · rcases h₄ with h₄ | h₄
    · omega_using [hn, h₄]
    · rw [keepBytes hp hM h₄ fr]; exact h.hh hn (ea ▸ e₁)
  · rcases h₅ with h₅ | h₅
    · omega_using [hn, h₅]
    · rw [keepBytes hp hM h₅ fr]; exact h.zk hn

/-- The facts of the layout that writing the keys uses. -/
class FinOK (L : KemLay) : Prop where
  fin : safeF L [bEKr L] 0 = true ∧ (∀ j < L.p.k, safeF L [bDK j] (j + 1) = true) ∧
    safeF L [bDKE L] (L.p.k + 1) = true ∧
    safeF L [⟨(Y L).sc, L.kgST, 200⟩, ⟨(Y L).sc, L.kgWK, 640⟩, bDKH L] (L.p.k + 2) = true ∧
    safeF L [bDKZ L] (L.p.k + 3) = true ∧ safeF L [] (L.p.k + 4) = true ∧ (Y L).apart (bACC L) [bDKE L] = true ∧
    (Y L).apart (bACC L) [⟨(Y L).sc, L.kgST, 200⟩, ⟨(Y L).sc, L.kgWK, 640⟩, bDKH L] = true
  enc : ∀ j < L.p.k, ((Y L).ok (bSE j) && (Y L).okW (bDK j) && (Y L).sep (bSE j) (bDK j)) = true
  ek : (Y L).ok ⟨1, 0, 384 * L.p.k⟩ = true ∧ (Y L).ok (bEKr L) = true ∧ (Y L).ok ⟨2, 0, 384 * L.p.k⟩ = true ∧
    (Y L).ok (bDKE L) = true ∧ (Y L).ok (bDKH L) = true ∧ (Y L).ok (bDKZ L) = true ∧
    (Y L).ok ⟨2, 0, 384 * L.p.k + L.p.ekLen⟩ = true ∧ (Y L).ok ⟨2, 0, 768 * L.p.k + 64⟩ = true
  rho : ((Y L).ok ⟨3, L.kgRS, 4 * 8⟩ && (Y L).okW ⟨1, 384 * L.p.k, 4 * 8⟩ &&
    (Y L).sep ⟨3, L.kgRS, 4 * 8⟩ ⟨1, 384 * L.p.k, 4 * 8⟩) = true
  cp : ((Y L).ok ⟨1, 0, L.p.ekLen⟩ && (Y L).okW (bDKE L) && (Y L).sep ⟨1, 0, L.p.ekLen⟩ (bDKE L)) = true ∧
    4 * (L.p.ekLen / 4) = L.p.ekLen ∧ 0 < L.p.ekLen / 4 ∧ L.p.ekLen / 4 < 2 ^ 30 ∧ L.p.ekLen < 2 ^ 32
  hh : ((Y L).okW ⟨3, L.kgST, 200⟩ && (Y L).okW ⟨3, L.kgWK, 640⟩ && (Y L).ok ⟨1, 0, L.p.ekLen⟩ &&
    (Y L).okW (bDKH L) && (Y L).sep ⟨3, L.kgST, 200⟩ ⟨3, L.kgWK, 640⟩ && (Y L).sep ⟨1, 0, L.p.ekLen⟩ ⟨3, L.kgST, 200⟩ &&
    (Y L).sep ⟨1, 0, L.p.ekLen⟩ ⟨3, L.kgWK, 640⟩ && (Y L).sep ⟨3, L.kgST, 200⟩ (bDKH L) &&
    (Y L).sep (bDKH L) ⟨3, L.kgWK, 640⟩) = true
  zk : ((Y L).ok ⟨0, 32, 4 * 8⟩ && (Y L).okW ⟨2, 768 * L.p.k + 64, 4 * 8⟩ &&
    (Y L).sep ⟨0, 32, 4 * 8⟩ ⟨2, 768 * L.p.k + 64, 4 * 8⟩) = true
  acc : (Y L).ok ⟨3, L.kgACC, 4⟩ = true

/-- `ek`, if every sample succeeded. -/
theorem ek_full [FinOK L] {n : Nat} {s₀ s : State} (hp : TPre (Y L) s₀) (h : F L n s₀ s) (hn : 1 ≤ n)
    (e : accV L s₀ s = 1) :
    bytesAt s.mem (Buf.addr s₀ ⟨1, 0, L.p.ekLen⟩) L.p.ekLen = KPke.ekPKE L.p (aM L s₀) (d s₀) := by
  obtain ⟨o₁, o₂, -⟩ := FinOK.ek (L := L)
  rw [bytes_split hp _ (o' := 384 * L.p.k) (l₁ := 384 * L.p.k) (l₂ := 32) (L := L.p.ekLen) (Nat.zero_add _) rfl o₁ o₂,
    bytes_catK hp _ o₁, h.rhoE hn, KPke.ekPKE]
  exact congrArg (· ++ _) (catK_congr fun i hi => by rw [Nat.zero_add]; exact h.ek e i hi)

/-- `dk`, if every sample succeeded. -/
theorem dk_full [FinOK L] {s₀ s : State} (hp : TPre (Y L) s₀) (h : F L (L.p.k + 4) s₀ s) (e : accV L s₀ s = 1) :
    bytesAt s.mem (Buf.addr s₀ ⟨2, 0, L.p.dkLen⟩) L.p.dkLen =
      KPke.dkPKE L.p (d s₀) ++ KPke.ekPKE L.p (aM L s₀) (d s₀) ++ H (KPke.ekPKE L.p (aM L s₀) (d s₀)) ++ z s₀ := by
  obtain ⟨-, -, o₃, o₄, o₅, o₆, o₇, o₈⟩ := FinOK.ek (L := L)
  rw [bytes_split hp _ (o' := 768 * L.p.k + 64) (l₁ := 768 * L.p.k + 64) (l₂ := 32) (Nat.zero_add _)
      (by unfold Params.dkLen; omega_using []) o₈ o₆,
    bytes_split hp _ (o' := 768 * L.p.k + 32) (l₁ := 768 * L.p.k + 32) (l₂ := 32) (Nat.zero_add _) rfl
      (by unfold Params.ekLen at o₇; rw [show 768 * L.p.k + 32 = 384 * L.p.k + (384 * L.p.k + 32) by omega_using []]; exact o₇) o₅,
    bytes_split hp _ (o' := 384 * L.p.k) (l₁ := 384 * L.p.k) (l₂ := L.p.ekLen) (Nat.zero_add _)
      (by unfold Params.ekLen; omega_using []) o₃ o₄,
    bytes_catK hp _ o₃, h.cp (by omega_using []) e, h.hh (by omega_using []) e, h.zk (by omega_using []), KPke.dkPKE]
  refine congrArg (fun x => x ++ _ ++ _ ++ _) (catK_congr fun j hj => ?_)
  rw [Nat.zero_add]; exact h.dk j hj (by omega_using [hj])

variable [FinOK L]

/-- `dk[384j : 384j + 384] ← ByteEncode₁₂(ŝ[j])`. -/
theorem enc_piece (j : Nat) (hj : j < L.p.k) :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (F L (j + 1)) (F L (j + 2)) (kgEnc j) := by
  refine enc12C_piece (Y := Y L) 3 (1024 * j) 2 (384 * j) (FinOK.enc j hj) (by rdecide) (by yk_taint)
    (fun _ _ _ h => ⟨h.ctx, (h.se j (by omega_using [hj])).1⟩) fun s₀ s s' hp h h' fr post => ?_
  have k := h.keep hp (by rdecide) ((FinOK.fin (L := L)).2.1 j hj) fr h'
  refine ⟨k.toB, fun hn => k.rhoE (by omega_using []), fun j' hj' hn => ?_, fun hn => by omega_using [hj, hn], fun hn => by omega_using [hj, hn],
    fun hn => by omega_using [hj, hn]⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hn | e
  · exact k.dk j' hj' (by omega_using [hn])
  · obtain rfl : j' = j := by omega_using [e]
    rw [post, (h.se j' (by omega_using [hj])).2]

/-- After the keys are written: `kgACC` returned. -/
structure Done (L : KemLay) (s₀ s : State) : Prop extends F L (L.p.k + 4) s₀ s where
  eax : s.gpr .eax = accV L s₀ s

/-- The keys, from the rows. -/
theorem fin_piece [GOK L] :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (B L (L.p.k * L.p.k) L.p.k) (Done L)
      (.seq (copyW 3 ⟨3, L.kgRS, 32⟩ ⟨1, 384 * L.p.k, 32⟩ 8) <|
        seqs ((List.range L.p.k).map kgEnc) <|
        .seq (copyW 3 ⟨1, 0, L.p.ekLen⟩ ⟨2, 384 * L.p.k, L.p.ekLen⟩ (L.p.ekLen / 4)) <|
        .seq (hash1 3 L.kgST L.kgWK 136 6 ⟨1, 0, L.p.ekLen⟩ ⟨2, 768 * L.p.k + 32, 32⟩) <|
        .seq (copyW 3 ⟨0, 32, 32⟩ ⟨2, 768 * L.p.k + 64, 32⟩ 8) (.block [.mov .eax (.mem (at_ .esi L.kgACC))])) := by
  obtain ⟨f₁, -, f₄, f₅, f₆, f₇, f₈, f₉⟩ := FinOK.fin (L := L)
  obtain ⟨c₁, c₂, c₃, c₄, c₅⟩ := FinOK.cp (L := L)
  refine Piece.seq (B := F L 1) (copyW_piece (Y := Y L) 3 L.kgRS 1 (384 * L.p.k) 8 (by decide) (by decide)
    FinOK.rho (by yk_taint) (by taint_decide) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr post => ?_) ?_
  · have k := h.keep hp (M := 0) (by rdecide)
      (by simp only [safeF, Bool.and_eq_true] at f₁; exact f₁.1.1.1.1.1) (Nat.le_refl _) (fr1 fr) h'
    refine ⟨k, fun _ => ?_, fun _ _ hn => by omega_using [hn], fun hn => by omega_using [hn], fun hn => by omega_using [hn], fun hn => by omega_using [hn]⟩
    rw [show Buf.addr s₀ (bEKr L) = Buf.addr s₀ ⟨1, 384 * L.p.k, 4 * 8⟩ from rfl, post]
    exact h.rho
  refine Piece.seqs0 (P := fun i => F L (i + 1)) L.p.k (fun j hj => enc_piece j hj) ?_
  refine Piece.seq (B := F L (L.p.k + 2)) (copyW_piece' (Y := Y L) 1 0 2 (384 * L.p.k) (L.p.ekLen / 4) L.p.ekLen
    c₂ c₃ c₄ c₁ (by yk_taint) (by taint_decide) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr post => ?_) ?_
  · have k := h.keep hp (by rdecide) f₄ (fr1 fr) h'
    have ea : accV L s₀ s' = accV L s₀ s := keepW hp (N := 0) (by rdecide) f₈ (fr1 fr)
    refine ⟨k.toB, fun _ => k.rhoE (by omega_using []), fun j hj _ => k.dk j hj (by omega_using [hj]), fun _ e₁ => ?_,
      fun hn => by omega_using [hn], fun hn => by omega_using [hn]⟩
    rw [post]
    exact ek_full hp h (by omega_using []) (ea ▸ e₁)
  refine Piece.seq (B := F L (L.p.k + 3)) (hash1_piece (Y := Y L) L.kgST L.kgWK 136 6 ⟨1, 0, L.p.ekLen⟩
    ⟨2, 768 * L.p.k + 32, 32⟩ rate136 FinOK.hh (by rdecide) c₅ (by rdecide) (by taint_rfl) (by yk_taint) (by yk_taint)
    (by yk_taint) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr out => ?_) ?_
  · have k := h.keep hp (by rdecide) f₅ fr h'
    have ea : accV L s₀ s' = accV L s₀ s := keepW hp (by rdecide) f₉ fr
    refine ⟨k.toB, fun _ => k.rhoE (by omega_using []), fun j hj _ => k.dk j hj (by omega_using [hj]), fun _ => k.cp (by omega_using []),
      fun _ e₁ => ?_, fun hn => by omega_using [hn]⟩
    rw [out, ek_full hp h (by omega_using []) (ea ▸ e₁), show (BitVec.ofNat 32 6).setWidth 8 = sha3Suffix from sha3Suffix32,
      ← padded, ← H_eq]
  refine Piece.seq (B := F L (L.p.k + 4)) (copyW_piece (Y := Y L) 0 32 2 (768 * L.p.k + 64) 8 (by decide)
    (by decide) FinOK.zk (by yk_taint) (by taint_decide) (fun _ _ _ h => h.ctx)
    fun s₀ s s' hp h h' fr post => ?_) ?_
  · have k := h.keep hp (by rdecide) f₆ (fr1 fr) h'
    refine ⟨k.toB, fun _ => k.rhoE (by omega_using []), fun j hj _ => k.dk j hj (by omega_using [hj]), fun _ => k.cp (by omega_using []),
      fun _ => k.hh (by omega_using []), fun _ => ?_⟩
    rw [show Buf.addr s₀ (bDKZ L) = Buf.addr s₀ ⟨2, 768 * L.p.k + 64, 4 * 8⟩ from rfl, post]
    exact h.ctx.roBytes hp (b := ⟨0, 32, 32⟩) (by rdecide) rfl
  exact ld32_piece (Y := Y L) L.kgACC FinOK.acc (by yk_taint) (fun _ _ _ h => h.ctx)
    fun s₀ s s' hp h h' m' e => ⟨h.keep hp (bs := []) (M := 0) (by rdecide) f₇
      (m' ▸ Frame.refl _ _) h',
      by rw [e]; show _ = s'.mem.readW _ 32; rw [m']; rfl⟩

end VG.Proof.MlKem.X86.KeyGen

end

end

/-! ### `MlKem.X86.KeyGenPrf`, which this module and modules that import it used -/

section

/-!
# ML-KEM on x86 (32-bit): `ŝ` and `ê` in key generation

`kgPrf L N` computes `NTT(SamplePolyCBD₂(PRF₂(σ, N)))` into `scratch[1024N]`
(`prf_piece`), and the `2k` of them take `P 0` to `P (2k)` (`prfs_piece`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt squeezeFrom absorb pad shakeSuffix)

variable {L : KemLay}

/-- `P N` holds after a block or call whose frame is apart from what it states. -/
theorem P.keep {N : Nat} {s₀ s s' : State} (hp : TPre (Y L) s₀) {bs : List Buf} {M : Nat}
    (hM : M + 16 ≤ (Y L).stk) (h₁ : (Y L).apart (bACC L) bs = true) (h₂ : (Y L).apart (bRho L) bs = true)
    (h₃ : (Y L).apart (bSig L) bs = true) (h₄ : ∀ j < N, (Y L).apart (bSE j) bs = true)
    (fr : Frame (FR s₀ bs M) s.mem s'.mem) (h : P L N s₀ s) (c : Ctx (Y L) s₀ s') : P L N s₀ s' :=
  ⟨c, by rw [keepW hp hM h₁ fr]; exact h.acc, by rw [keepBytes hp hM h₂ fr]; exact h.rho,
    by rw [keepBytes hp hM h₃ fr]; exact h.sig, fun j hj => keepPoly hp hM (h₄ j hj) fr (h.se j hj)⟩

/-- `σ ‖ N` is stored. -/
structure Q1 (L : KemLay) (N : Nat) (s₀ s : State) : Prop extends P L N s₀ s where
  nb : bytesAt s.mem (Buf.addr s₀ (bNB L)) 1 = [BitVec.ofNat 8 N]

/-- `PRF₂(σ, N)` is computed. -/
structure Q2 (L : KemLay) (N : Nat) (s₀ s : State) : Prop extends P L N s₀ s where
  prf : bytesAt s.mem (Buf.addr s₀ (bPRF L)) 128 = prf 2 (KPke.kgSigma L.p (d s₀)) (BitVec.ofNat 8 N)

/-- `SamplePolyCBD₂(PRF₂(σ, N))` is computed. -/
structure Q3 (L : KemLay) (N : Nat) (s₀ s : State) : Prop extends P L N s₀ s where
  cbd : PolyIs s.mem (Buf.addr s₀ (bSE N)) (cbd (KPke.kgSigma L.p (d s₀)) N)

/-- The facts of the layout that `ŝ` and `ê` use. -/
class PrfOK (L : KemLay) : Prop where
  sig : (Y L).ok (bNB L) = true ∧ (Y L).ok (bSig L) = true
  nb : (Y L).apart (bACC L) [⟨3, L.kgRS + 64, 1⟩] = true ∧ (Y L).apart (bRho L) [⟨3, L.kgRS + 64, 1⟩] = true ∧
    (Y L).apart (bSig L) [⟨3, L.kgRS + 64, 1⟩] = true
  hash : ((Y L).okW ⟨3, L.kgST, 200⟩ && (Y L).okW ⟨3, L.kgWK, 640⟩ && (Y L).ok (bSigN L) && (Y L).okW (bPRF L) &&
    (Y L).sep ⟨3, L.kgST, 200⟩ ⟨3, L.kgWK, 640⟩ && (Y L).sep (bSigN L) ⟨3, L.kgST, 200⟩ &&
    (Y L).sep (bSigN L) ⟨3, L.kgWK, 640⟩ && (Y L).sep ⟨3, L.kgST, 200⟩ (bPRF L) &&
    (Y L).sep (bPRF L) ⟨3, L.kgWK, 640⟩) = true ∧
    (Y L).apart (bACC L) [⟨3, L.kgST, 200⟩, ⟨3, L.kgWK, 640⟩, bPRF L] = true ∧
    (Y L).apart (bRho L) [⟨3, L.kgST, 200⟩, ⟨3, L.kgWK, 640⟩, bPRF L] = true ∧
    (Y L).apart (bSig L) [⟨3, L.kgST, 200⟩, ⟨3, L.kgWK, 640⟩, bPRF L] = true
  prf : ∀ N < 2 * L.p.k,
    (∀ j < N, (Y L).apart (bSE j) [⟨3, L.kgST, 200⟩, ⟨3, L.kgWK, 640⟩, bPRF L] = true) ∧
    (∀ j < N, (Y L).apart (bSE j) [⟨3, L.kgRS + 64, 1⟩] = true) ∧
    (∀ j < N, (Y L).apart (bSE j) [bSE N] = true) ∧
    (∀ j < N, (Y L).apart (bSE j) [bSE N, bNS L] = true) ∧
    ((Y L).apart (bACC L) [bSE N] && (Y L).apart (bRho L) [bSE N] && (Y L).apart (bSig L) [bSE N]) = true ∧
    ((Y L).apart (bACC L) [bSE N, bNS L] && (Y L).apart (bRho L) [bSE N, bNS L] &&
      (Y L).apart (bSig L) [bSE N, bNS L]) = true ∧
    ((Y L).ok (bPRF L) && (Y L).okW (bSE N) && (Y L).sep (bPRF L) (bSE N)) = true ∧
    ((Y L).okW (bSE N) && (Y L).okW (bNS L) && (Y L).sep (bSE N) (bNS L)) = true

theorem sigN_split [PrfOK L] {s₀ : State} (hp : TPre (Y L) s₀) (m : Mem) :
    bytesAt m (Buf.addr s₀ (bSigN L)) 33 =
      bytesAt m (Buf.addr s₀ (bSig L)) 32 ++ bytesAt m (Buf.addr s₀ (bNB L)) 1 := by
  have e : Buf.addr s₀ (bNB L) = Buf.addr s₀ (bSig L) + BitVec.ofNat 64 32 := by
    rw [Buf.addr_eq hp (b := bNB L) PrfOK.sig.1, Buf.addr_eq hp (b := bSig L) PrfOK.sig.2, BitVec.add_assoc,
      ← BitVec.ofNat_add]
  rw [e]
  exact bytesAt_add m (Buf.addr s₀ (bSig L)) 32 1

variable [GOK L] [PrfOK L]

/-- `ŝ[N]` or `ê[N - k]`. -/
theorem prf_piece (N : Nat) (hN : N < 2 * L.p.k) :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (P L N) (P L (N + 1)) (kgPrf L N) := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈⟩ := PrfOK.prf N hN
  obtain ⟨b₁, b₂, b₃⟩ := PrfOK.nb (L := L)
  obtain ⟨c₁, c₂, c₃, c₄⟩ := PrfOK.hash (L := L)
  refine Piece.seq (B := Q1 L N) (st8_piece (Y := Y L) (L.kgRS + 64) N (GOK.rs (L := L)).2.2.2.1 (by taint_rfl)
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' m' => ⟨?_, ?_⟩) ?_
  · exact h.keep hp (M := 0) (by rdecide) b₁ b₂ b₃ (fun j hj => a₂ j hj) (m' ▸ frW8 (Y := Y L)) h'
  · rw [m']
    refine bytesAt_eq (L := [BitVec.ofNat 8 N]) rfl fun i hi => ?_
    obtain rfl : i = 0 := by omega_using [hi]
    simp only [BitVec.add_zero, writeW8_apply, List.getElem_cons_zero]
    refine (ite_eq_left (rfl : Buf.addr s₀ (bNB L) = Buf.addr s₀ ⟨(Y L).sc, L.kgRS + 64, 1⟩)).trans ?_
    rw [BitVec.setWidth_ofNat_of_le (by decide)]
  refine Piece.seq (B := Q2 L N) (hash1_piece (Y := Y L) L.kgST L.kgWK 136 0x1f (bSigN L) (bPRF L) rate136 c₁
    (by rdecide) (by rdecide) (by rdecide) (by taint_rfl) (by yk_taint) (by yk_taint) (by yk_taint)
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr out => ⟨?_, ?_⟩) ?_
  · exact h.keep hp (by rdecide) c₂ c₃ c₄ (fun j hj => a₁ j hj) fr h'
  · rw [out, sigN_split hp, h.sig, h.nb, show (BitVec.ofNat 32 0x1f).setWidth 8 = shakeSuffix from shakeSuffix32,
      prf_eq]
  refine Piece.seq (B := Q3 L N) (cbd2C_piece (Y := Y L) 3 L.kgPRF 3 (1024 * N) a₇ (by rdecide) (by yk_taint)
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr post => ⟨?_, ?_⟩) ?_
  · simp only [Bool.and_eq_true] at a₅
    exact h.keep hp (by rdecide) a₅.1.1 a₅.1.2 a₅.2 a₃ fr h'
  · rw [h.prf] at post; exact post
  refine inPlaceC_piece NttFwd.verified ntt_nosp ntt_stack 3 (1024 * N) 3 L.kgNS a₈ (by rdecide) (by yk_taint)
    (fun _ _ _ h => ⟨h.ctx, h.cbd.1⟩) fun s₀ s s' hp h h' fr post => ?_
  simp only [Bool.and_eq_true] at a₆
  have k := h.keep hp (by rdecide) a₆.1.1 a₆.1.2 a₆.2 a₄ fr h'
  refine ⟨h', k.acc, k.rho, k.sig, fun j hj => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
  · exact k.se j hj
  · rw [h.cbd.2] at post; exact post

/-- The `2k` of them, then `c`. -/
theorem prfs_piece {B : State → State → Prop} {c : Prog isa}
    (h : Piece (TPre (Y L)) (TPub (Y L) (lk L)) (P L (2 * L.p.k)) B c) :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (P L 0) B (seqs ((List.range (2 * L.p.k)).map (kgPrf L)) c) :=
  Piece.seqs0 (P := P L) (2 * L.p.k) prf_piece h

end VG.Proof.MlKem.X86.KeyGen

end

end

/-!
# ML-KEM on x86 (32-bit): the body of key generation

The body is the start (`KeyGenG.lean`), `ŝ` and `ê` (`KeyGenPrf.lean`), the
rows of `t̂` (`KeyGenRow.lean`) and the keys (`KeyGenFin.lean`). If every
`SampleNTT` succeeded (`kgACC` is 1), `samp_bound` gives one bound on their
iterations, within which K-PKE.KeyGen succeeds with the matrix sampled
(`KPke.kpkeKeyGen_some`); if one failed within `minIterations`, K-PKE.KeyGen
fails with that bound (`KPke.kpkeKeyGen_none`) (`post`). Two runs with the
same pointers and `ρ` leak the same: the contract lets the function leak `ρ`.
Each parameter set's contract implies `TPre (Y L)` and its public data
(`Proof/MlKem/X86/KeyGen.lean` for ML-KEM-768).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

variable {L : KemLay}

theorem body_piece [GOK L] [PrfOK L] [KgRowOK L] [FinOK L] :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (fun s₀ s => s = P0 s₀) (Done L) (kgBody L) :=
  start_piece <| prfs_piece <| rows_piece fin_piece |>.mono (fun _ _ _ h =>
    ⟨h.ctx, h.rho, h.se, .inr h.acc, fun _ _ h => absurd h (Nat.not_lt_zero _),
      fun e => absurd (h.acc.symm.trans e) (by decide), fun _ _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun _ _ _ h => h

theorem piece [GOK L] [PrfOK L] [KgRowOK L] [FinOK L] (hsp : NoSp (kgBody L)) :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (Done L s₀) s₀ s')
      (leaf (kgBody L)) :=
  topLeaf hsp (body_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨h.ctx, h⟩)

/-- Every sample, within one bound. -/
theorem samples {s₀ s : State} (h : Done L s₀ s) (e : accV L s₀ s = 1) :
    ∃ M, ∀ i < L.p.k, ∀ j < L.p.k, sampleNTT M (matSeed (KPke.kgRho L.p (d s₀)) i j) = some (aM L s₀ i j) := by
  obtain ⟨M, hM⟩ := samp_bound ((List.range (L.p.k * L.p.k)).map fun k =>
      (mS L s₀ k, aM L s₀ (k / L.p.k) (k % L.p.k))) (by
    intro p hp
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    obtain ⟨a, ha⟩ := h.ok e k (List.mem_range.mp hk)
    show Samp (mS L s₀ k) (sv (mS L s₀ k))
    rw [sv_eq ha]; exact ha)
  refine ⟨M, fun i hi j hj => ?_⟩
  have r := hM (mS L s₀ (L.p.k * i + j), aM L s₀ ((L.p.k * i + j) / L.p.k) ((L.p.k * i + j) % L.p.k))
    (List.mem_map.mpr ⟨L.p.k * i + j, List.mem_range.mpr (idx_lt hi hj), rfl⟩)
  rw [mS_eq s₀ hj, idx_div hj, idx_mod hj] at r
  exact r

/-- The postcondition, from the final state of the body. -/
theorem post [FinOK L] (hη : L.p.η₁ = 2) {s₀ s : State} (hp : TPre (Y L) s₀) (h : Done L s₀ s) :
    Outcome (fun iters => keyGenInternal L.p iters (d s₀) (z s₀)) (accV L s₀ s)
      (bytesAt s.mem (Buf.addr s₀ ⟨1, 0, L.p.ekLen⟩) L.p.ekLen,
        bytesAt s.mem (Buf.addr s₀ ⟨2, 0, L.p.dkLen⟩) L.p.dkLen) := by
  rcases h.acc with e | e
  · obtain ⟨k, hk, hn⟩ := h.fail e
    have hk0 : 0 < L.p.k := Nat.pos_of_ne_zero fun h0 => by rw [h0] at hk; omega_using [hk]
    refine .inr ⟨e, ?_⟩
    show keyGenInternal L.p minIterations (d s₀) (z s₀) = none
    rw [KPke.keyGenInternal_eq, KPke.kpkeKeyGen_none (i := k / L.p.k) (j := k % L.p.k)
      (Nat.div_lt_of_lt_mul hk) (Nat.mod_lt _ hk0) hn]
    rfl
  · obtain ⟨M, hM⟩ := samples h e
    refine .inl ⟨e, M, ?_⟩
    show keyGenInternal L.p M (d s₀) (z s₀) = _
    rw [KPke.keyGenInternal_eq, KPke.kpkeKeyGen_some hη hM, ek_full hp h.toF (by omega_using []) e, dk_full hp h.toF e]
    rfl

end VG.Proof.MlKem.X86.KeyGen
