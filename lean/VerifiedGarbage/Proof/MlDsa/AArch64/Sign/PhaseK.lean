module
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseCBase

import VerifiedGarbage.Proof.MlDsa.Sign.Mem
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA signing on AArch64: the checks of an iteration

The values the checks of an iteration compute: `c = SampleInBall(c̃)`
(`cV`), `z[r]`, `r₀[i]`, `ct₀[i]` and the hints `h[i]` (`Zv`, `R0v`, `CT0v`,
`Hv`), whether the iteration passes (`PassV`, `passV_iff`), and the number
of 1s of the hints (`onesSum`, against `ω`); and the layout checks of the
checks' pieces (`bChk`, `zChk`, `rChk`, `hChk2`, `ksChk`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlKem.AArch64 (Only Keep wp_movz wp_nil)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable (p : Params)

/-- `c = SampleInBall(c̃)` of the iteration with counter `κ`, within `maxBounds`. -/
abbrev cV (σ : State) (κ : Nat) : IPoly :=
  (sampleInBall p.τ maxBounds.ball (CTv p σ κ)).getD (Vector.replicate n 0)

/-- `z[r]`, `r₀[i]`, `ct₀[i]`, `w[i] - cs₂[i]`, `w[i] - cs₂[i] + ct₀[i]` and `h[i]`. -/
abbrev Zv (σ : State) (κ r : Nat) : Poly := zF p (S1v p σ) (rppOf p σ) κ (cV p σ κ) r
abbrev R0v (σ : State) (κ i : Nat) : Poly := r0F p (Am p σ) (S2v p σ) (rppOf p σ) κ (cV p σ κ) i
abbrev CT0v (σ : State) (κ i : Nat) : Poly := ct0F (T0v p σ) (cV p σ κ) i
abbrev W'v (σ : State) (κ i : Nat) : Poly := w'F p (Am p σ) (S2v p σ) (rppOf p σ) κ (cV p σ κ) i
abbrev Hv (σ : State) (κ i : Nat) : Vector Bool n := hF p (Am p σ) (S2v p σ) (T0v p σ) (rppOf p σ) κ (cV p σ κ) i

/-- Whether the iteration with counter `κ` passes, once `SampleInBall` succeeded. -/
abbrev PassV (σ : State) (κ : Nat) : Prop :=
  passF p (Am p σ) (S1v p σ) (S2v p σ) (T0v p σ) (rppOf p σ) κ (cV p σ κ)

end

/-! ## `SampleInBall` -/

def bChk (p : Params) : Bool :=
  ballChkS (sgR p) (sgW p) (cLen p) cP && icwChk p [(cP, 1024), (sc oPS, 2048)] p.k &&
    keepB (sgR p) (sgW p) [(cP, 1024), (sc oPS, 2048)] (sc oCT) (cLen p) && decide ((cLen p, p.τ) ∈ ballParams)

theorem ball_val {τ : Nat} {x : List Byte} {r : BitVec 32} {out : Poly}
    (h : Outcome (fun b => (sampleInBall τ b.ball x).map toRq) r out) (h1 : r = 1)
    (hm : (sampleInBall τ maxBounds.ball x).isSome) :
    out = toRq ((sampleInBall τ maxBounds.ball x).getD (Vector.replicate n 0)) := by
  rcases h with ⟨_, b, hb⟩ | ⟨h0, _⟩
  · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hm
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hb
    have e1 := sampleInBall_mono (Nat.le_max_left b.ball maxBounds.ball) hc
    have e2 := sampleInBall_mono (Nat.le_max_right b.ball maxBounds.ball) hy
    rw [e1] at e2
    rw [hy, Option.some.inj e2]; rfl
  · rw [h1] at h0; cases h0

/-! ## Norms, into `x24` -/

theorem bit_congr {a b : Prop} [Decidable a] [Decidable b] (h : a ↔ b) : bit a = bit b := by
  by_cases ha : a
  · rw [show bit a = 1 from ifp ha _ _, show bit b = 1 from ifp (h.mp ha) _ _]
  · rw [show bit a = 0 from ifn ha _ _, show bit b = 0 from ifn (fun hb => ha (h.mpr hb)) _ _]

theorem bit_one {a : Prop} [Decidable a] : bit a = 1 ↔ a := by
  by_cases ha : a
  · exact ⟨fun _ => ha, fun _ => ifp ha _ _⟩
  · exact ⟨fun h => absurd (h.symm.trans (ifn ha 1 0)) (by decide), fun h => absurd h ha⟩

theorem bit_zero {a : Prop} [Decidable a] : bit a = 0 ↔ ¬ a := by
  by_cases ha : a
  · exact ⟨fun h => absurd (h.symm.trans (ifp ha 1 0)) (by decide), fun h => absurd ha h⟩
  · exact ⟨fun _ => ha, fun _ => ifn ha _ _⟩

theorem forall_lt_succ {P : Nat → Prop} {r : Nat} : ((∀ j < r, P j) ∧ P r) ↔ ∀ j < r + 1, P j :=
  ⟨fun ⟨h1, h2⟩ j hj => by
    rcases (by omega_arith : j < r ∨ j = r) with hj | rfl
    exacts [h1 j hj, h2], fun h => ⟨fun j hj => h j (by omega_arith), h r (by omega_arith)⟩⟩

theorem Fam.shift {s : State} {b m r : Nat} {f : Nat → Poly} (h : Fam s (b + r) (m - r) fun j => f (r + j))
    (hr : r < m) : Fam s (b + (r + 1)) (m - (r + 1)) fun j => f (r + 1 + j) := fun j hj => by
  have := h (j + 1) (by omega_arith)
  show Pl s (b + (r + 1) + j) (f (r + 1 + j))
  rw [show b + (r + 1) + j = b + r + (j + 1) by omega_arith, show r + 1 + j = r + (j + 1) by omega_arith]
  exact this

theorem Fam.zero {s : State} {b m : Nat} {f : Nat → Poly} (h : Fam s b m f) :
    Fam s (b + 0) (m - 0) fun j => f (0 + j) := fun j hj => by
  show Pl s (b + 0 + j) (f (0 + j))
  rw [Nat.add_zero, Nat.zero_add]
  exact h j hj

/-! ## The checks' state -/

def kbChk (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  ilChk p ws && keepB (sgR p) (sgW p) ws (sc oCT) (cLen p) && keepB (sgR p) (sgW p) ws cP 1024

/-! ## `z` -/

def zfam (p : Params) (ws : List (Ptr × Nat)) (r : Nat) : Bool :=
  kbChk p ws && famChk (sgR p) (sgW p) ws (yBase p) r && famChk (sgR p) (sgW p) ws (wBase p) p.k && keepB (sgR p) (sgW p) ws (sc oONES) 8

/-- What `z[r]` needs of the layout. -/
def zChk (p : Params) (r : Nat) : Bool :=
  let w1 : List (Ptr × Nat) := [(t1P, 1024)]
  let w2 : List (Ptr × Nat) := [(t1P, 1024), (sc oPS, 1024)]
  let w3 : List (Ptr × Nat) := [(yP p r, 1024)]
  mulChk (sgR p) (sgW p) t1P cP (s1P p r) && ipChkS (sgR p) (sgW p) t1P && accChk (sgR p) (sgW p) (yP p r) t1P &&
    normChk (sgB p) (yP p r) && zfam p w1 r && zfam p w2 r && zfam p w3 r && zfam p [] (r + 1) &&
    famChk (sgR p) (sgW p) w1 (yBase p + r) (p.ℓ - r) && famChk (sgR p) (sgW p) w2 (yBase p + r) (p.ℓ - r) &&
    famChk (sgR p) (sgW p) w3 (yBase p + (r + 1)) (p.ℓ - (r + 1)) && famChk (sgR p) (sgW p) [] (yBase p + (r + 1)) (p.ℓ - (r + 1)) &&
    famChk (sgR p) (sgW p) w3 (yBase p) r && keepB (sgR p) (sgW p) w1 (s1P p r) 1024 && decide (p.γ₁ - p.β < 2 ^ 32) &&
    decide (r < p.ℓ)

/-! ## `r₀` -/

/-- `z` passed. -/
abbrev ZOk (p : Params) (σ : State) (κ : Nat) : Prop := ∀ j < p.ℓ, normRq [Zv p σ κ j] < p.γ₁ - p.β

def rfam (p : Params) (ws : List (Ptr × Nat)) (i : Nat) : Bool :=
  kbChk p ws && famChk (sgR p) (sgW p) ws (yBase p) p.ℓ && famChk (sgR p) (sgW p) ws (wBase p) i && keepB (sgR p) (sgW p) ws (sc oONES) 8

/-- What `r₀[i]` needs of the layout. -/
def rChk (p : Params) (i : Nat) : Bool :=
  let w1 : List (Ptr × Nat) := [(t1P, 1024)]
  let w2 : List (Ptr × Nat) := [(t1P, 1024), (sc oPS, 1024)]
  let w3 : List (Ptr × Nat) := [(wP p i, 1024)]
  let w4 : List (Ptr × Nat) := [(t2P, 1024)]
  mulChk (sgR p) (sgW p) t1P cP (s2P p i) && ipChkS (sgR p) (sgW p) t1P && accChk (sgR p) (sgW p) (wP p i) t1P &&
    rwChk (sgR p) (sgW p) (wP p i) 1024 t2P 1024 && normChk (sgB p) t2P && rfam p w1 i && rfam p w2 i &&
    rfam p w3 i && rfam p w4 (i + 1) && rfam p [] (i + 1) &&
    famChk (sgR p) (sgW p) w1 (wBase p + i) (p.k - i) && famChk (sgR p) (sgW p) w2 (wBase p + i) (p.k - i) &&
    famChk (sgR p) (sgW p) w3 (wBase p + (i + 1)) (p.k - (i + 1)) && famChk (sgR p) (sgW p) w4 (wBase p + (i + 1)) (p.k - (i + 1)) &&
    famChk (sgR p) (sgW p) [] (wBase p + (i + 1)) (p.k - (i + 1)) && keepB (sgR p) (sgW p) w4 (wP p i) 1024 &&
    decide (p.γ₂ - p.β < 2 ^ 32) && decide (p.γ₂ ∈ gamma2s) && decide (i < p.k)

/-! ## Hints and their 1s -/

theorem hintIs_congr {m m' : Mem} {a : Addr} {h : List (Vector Bool n)}
    (hb : ∀ k < 1024, m' (a + BitVec.ofNat 64 k) = m (a + BitVec.ofNat 64 k)) (H : HintIs m a 1 h) :
    HintIs m' a 1 h :=
  ⟨H.1, fun i hi j hj => by
    have hn : n = 256 := rfl
    rw [coeffAt_congr₂ hb (show 256 * i + j < 256 by omega_arith)]; exact H.2 i hi j hj⟩

/-- The hints of the first `m` slots from `b`. -/
def HFam (s : State) (b m : Nat) (f : Nat → Vector Bool n) : Prop :=
  ∀ j < m, HintIs s.mem (pa s (pS (b + j))) 1 [f j]

theorem HFam.keep {D : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State} (L : Lay D rbs wbs s)
    {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws) {b m : Nat} {f : Nat → Vector Bool n}
    (hc : famChk rbs wbs ws b m = true) (h : HFam s b m f) : HFam s' b m f := fun j hj => by
  have hk := famChk_one hc hj
  rw [hP.pa (L.keepBs hk)]
  exact hintIs_congr (VG.Proof.MlKem.bytes_frame hP.frame (L.fdisj hk) (by decide)) (h j hj)

theorem HFam.snoc {s : State} {b m : Nat} {f : Nat → Vector Bool n} (h : HFam s b m f)
    (h' : HintIs s.mem (pa s (pS (b + m))) 1 [f m]) : HFam s b (m + 1) f := fun j hj => by
  rcases (by omega_arith : j < m ∨ j = m) with hj | rfl
  exacts [h j hj, h']

theorem hintOnes_le (h : Vector Bool n) : hintOnes [h] ≤ 256 := by
  rw [hintOnes_single]
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

/-- The sum of the 1s of the first `i` hints. -/
abbrev onesSum (f : Nat → Vector Bool n) (i : Nat) : Nat := ((List.range i).map fun j => hintOnes [f j]).sum

theorem onesSum_le (f : Nat → Vector Bool n) : ∀ i, onesSum f i ≤ 256 * i
  | 0 => by simp [onesSum]
  | i + 1 => by
    simp only [onesSum, List.range_succ, List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    have := onesSum_le f i; have := hintOnes_le (f i)
    simp only [onesSum] at *
    omega_arith

theorem onesSum_succ (f : Nat → Vector Bool n) (i : Nat) : onesSum f (i + 1) = onesSum f i + hintOnes [f i] := by
  simp only [onesSum, List.range_succ, List.map_append, List.map_cons, List.map_nil, List.sum_append,
    List.sum_cons, List.sum_nil, Nat.add_zero]

/-! ## `ct₀` and the hint -/

/-- `r₀` passed. -/
abbrev R0Ok (p : Params) (σ : State) (κ : Nat) : Prop := ∀ j < p.k, normRq [R0v p σ κ j] < p.γ₂ - p.β

def hfam (p : Params) (ws : List (Ptr × Nat)) (a c : Nat) : Bool :=
  kbChk p ws && famChk (sgR p) (sgW p) ws (yBase p) p.ℓ && famChk (sgR p) (sgW p) ws (wBase p) a &&
    famChk (sgR p) (sgW p) ws (wBase p + a) (p.k - a) && famChk (sgR p) (sgW p) ws 5 c

theorem ones32 {m : Mem} {a : Addr} {x : Nat} (h : m.readW a 64 = BitVec.ofNat 64 x) :
    (m.readW a 64).setWidth 32 = BitVec.ofNat 32 x := by
  rw [h]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_arith

theorem sw_ofNat {n : Nat} (h : n < 2 ^ 32) : BitVec.setWidth 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega_arith)]

/-- What `h[i]` needs of the layout. -/
def hChk2 (p : Params) (i : Nat) : Bool :=
  let w1 : List (Ptr × Nat) := [(t3P, 1024)]
  let w2 : List (Ptr × Nat) := [(t3P, 1024), (sc oPS, 1024)]
  let w4 : List (Ptr × Nat) := [(t4P, 1024)]
  let w5 : List (Ptr × Nat) := [(wP p i, 1024)]
  let w7 : List (Ptr × Nat) := [(hP i, 1024)]
  let w8 : List (Ptr × Nat) := [(sc oONES, 8)]
  mulChk (sgR p) (sgW p) t3P cP (t0P p i) && ipChkS (sgR p) (sgW p) t3P && normChk (sgB p) t3P &&
    copyChk (sgR p) (sgW p) t4P (wP p i) 1024 && accChk (sgR p) (sgW p) (wP p i) t3P &&
    accChk (sgR p) (sgW p) t4P (wP p i) && hintChk (sgR p) (sgW p) t4P (wP p i) (hP i) &&
    hfam p w1 i i && hfam p w2 i i && hfam p [] i i && hfam p w4 i i &&
    (kbChk p w5 && famChk (sgR p) (sgW p) w5 (yBase p) p.ℓ && famChk (sgR p) (sgW p) w5 5 i) &&
    hfam p w4 (i + 1) i && hfam p w7 (i + 1) i && hfam p w8 (i + 1) (i + 1) &&
    famChk (sgR p) (sgW p) w5 (wBase p) i && famChk (sgR p) (sgW p) w5 (wBase p + (i + 1)) (p.k - (i + 1)) &&
    keepB (sgR p) (sgW p) w1 (sc oONES) 8 && keepB (sgR p) (sgW p) w2 (sc oONES) 8 && keepB (sgR p) (sgW p) [] (sc oONES) 8 &&
    keepB (sgR p) (sgW p) w4 (sc oONES) 8 && keepB (sgR p) (sgW p) w5 (sc oONES) 8 && keepB (sgR p) (sgW p) w7 (sc oONES) 8 &&
    keepB (sgR p) (sgW p) [] t3P 1024 && keepB (sgR p) (sgW p) w4 t3P 1024 &&
    keepB (sgR p) (sgW p) w5 t4P 1024 && keepB (sgR p) (sgW p) w1 (t0P p i) 1024 &&
    inB (sgB p) (sc oONES) 8 && inB (sgW p) (sc oONES) 8 &&
    decide (p.γ₂ < 2 ^ 32) && decide (p.γ₂ ∈ gamma2s) && decide (i < p.k) && decide (256 * p.k < 2 ^ 32)

/-! ## `ω` -/

theorem sign_bit {S w : Nat} (hS : S < 2 ^ 32) (hw : w < 2 ^ 31) :
    ((BitVec.ofNat 64 S - BitVec.ofNat 64 w) >>> 63).setWidth 32 = if S < w then 1 else 0 := by
  by_cases h : S < w
  · rw [ifp h]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    rw [Nat.shiftRight_eq_div_pow, show (1 : BitVec 32).toNat = 1 from rfl]
    omega_arith
  · rw [ifn h]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    rw [Nat.shiftRight_eq_div_pow, show (0 : BitVec 32).toNat = 0 from rfl]
    omega_arith

/-! ## The checks -/

/-- What the checks need of the layout. -/
def ksChk (p : Params) : Bool :=
  ipChkS (sgR p) (sgW p) cP && icwChk p [(cP, 1024), (sc oPS, 1024)] p.k &&
    keepB (sgR p) (sgW p) [(cP, 1024), (sc oPS, 1024)] (sc oCT) (cLen p) && inB (sgW p) (sc oONES) 8 &&
    kbChk p [(sc oONES, 8)] && famChk (sgR p) (sgW p) [(sc oONES, 8)] (yBase p) p.ℓ &&
    famChk (sgR p) (sgW p) [(sc oONES, 8)] (wBase p) p.k &&
    (List.range p.ℓ).all (zChk p) && (List.range p.k).all (rChk p) && (List.range p.k).all (hChk2 p) &&
    inB (sgB p) (sc oONES) 8 && inB (sgW p) (sc oCNT) 8 && inB (sgW p) (sc oKAP) 8 &&
    kbChk p [] &&
    famChk (sgR p) (sgW p) [(sc oCNT, 8)] (yBase p) p.ℓ && famChk (sgR p) (sgW p) [(sc oCNT, 8)] 5 p.k &&
    famChk (sgR p) (sgW p) [] (yBase p) p.ℓ && famChk (sgR p) (sgW p) [] 5 p.k &&
    ikChk p [(sc oCNT, 8)] && ikChk p [(sc oKAP, 8)] && keepB (sgR p) (sgW p) [(sc oKAP, 8)] (sc oCNT) 8 &&
    keepB (sgR p) (sgW p) [(sc oCNT, 8)] (sc oCT) (cLen p) && decide (p.ω + 1 < 4096) && decide (p.ℓ < 4096) &&
    decide (256 * p.k < 2 ^ 32) && decide (0 < p.ℓ) && famChk (sgR p) (sgW p) [] (wBase p) p.k && inB (sgB p) (sc oKAP) 8

theorem bit_ne {a : Prop} [Decidable a] : (bit a).setWidth 32 ≠ 0 ↔ a := by
  by_cases ha : a
  · rw [show bit a = 1 from ifp ha _ _]; exact ⟨fun _ => ha, fun _ => by decide⟩
  · rw [show bit a = 0 from ifn ha _ _]; exact ⟨fun h => absurd rfl h, fun h => absurd h ha⟩

theorem bit_and' {a b : Prop} [Decidable a] [Decidable b] :
    BitVec.setWidth 64 ((bit a).setWidth 32 &&& (if b then (1 : BitVec 32) else 0)) = bit (a ∧ b) := by
  by_cases ha : a <;> by_cases hb : b <;> simp [bit, ha, hb]

theorem passV_iff {p : Params} {σ : State} {κ : Nat} :
    (((ZOk p σ κ ∧ R0Ok p σ κ) ∧ ∀ j < p.k, normRq [CT0v p σ κ j] < p.γ₂) ∧ onesSum (Hv p σ κ) p.k < p.ω + 1) ↔
      PassV p σ κ :=
  ⟨fun ⟨⟨⟨a, b⟩, c⟩, d⟩ => ⟨a, b, c, Nat.le_of_lt_succ d⟩, fun ⟨a, b, c, d⟩ => ⟨⟨⟨a, b⟩, c⟩, Nat.lt_succ_of_le d⟩⟩

theorem ksChk_spec {p : Params} (hc : ksChk p = true) : ∀ {Q : Prop}, (ipChkS (sgR p) (sgW p) cP = true →
    icwChk p [(cP, 1024), (sc oPS, 1024)] p.k = true →
    keepB (sgR p) (sgW p) [(cP, 1024), (sc oPS, 1024)] (sc oCT) (cLen p) = true → inB (sgW p) (sc oONES) 8 = true →
    kbChk p [(sc oONES, 8)] = true → famChk (sgR p) (sgW p) [(sc oONES, 8)] (yBase p) p.ℓ = true →
    famChk (sgR p) (sgW p) [(sc oONES, 8)] (wBase p) p.k = true →
    (∀ r < p.ℓ, zChk p r = true) → (∀ i < p.k, rChk p i = true) → (∀ i < p.k, hChk2 p i = true) →
    inB (sgB p) (sc oONES) 8 = true → inB (sgW p) (sc oCNT) 8 = true → inB (sgW p) (sc oKAP) 8 = true →
    kbChk p [] = true → famChk (sgR p) (sgW p) [(sc oCNT, 8)] (yBase p) p.ℓ = true →
    famChk (sgR p) (sgW p) [(sc oCNT, 8)] 5 p.k = true → famChk (sgR p) (sgW p) [] (yBase p) p.ℓ = true →
    famChk (sgR p) (sgW p) [] 5 p.k = true → ikChk p [(sc oCNT, 8)] = true → ikChk p [(sc oKAP, 8)] = true →
    keepB (sgR p) (sgW p) [(sc oKAP, 8)] (sc oCNT) 8 = true → keepB (sgR p) (sgW p) [(sc oCNT, 8)] (sc oCT) (cLen p) = true →
    p.ω + 1 < 4096 → p.ℓ < 4096 → 256 * p.k < 2 ^ 32 → 0 < p.ℓ → famChk (sgR p) (sgW p) [] (wBase p) p.k = true →
    inB (sgB p) (sc oKAP) 8 = true → Q) → Q := by
  intro Q k
  simp only [ksChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, hz⟩, hr⟩, hh⟩, c8⟩, c9⟩, c10⟩, c13⟩, c14⟩, c15⟩, c16⟩, c17⟩, c18⟩, c19⟩, c20⟩, c21⟩, hω⟩, hl⟩, hk⟩, hl0⟩, c22⟩, c23⟩ := hc
  exact k c1 c2 c3 c4 c5 c6 c7 hz hr hh c8 c9 c10 c13 c14 c15 c16 c17 c18 c19 c20 c21 hω hl hk hl0 c22 c23

/-- `x24 ← 1`, `ONES ← 0`. -/
abbrev kInit : List Instr := [.movz .x .x24 1 0] ++ setQ (sc oONES) 0

theorem ksChk_ok {p : Params} (h : Ok3 p) : ksChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide +kernel

theorem bChk_ok {p : Params} (h : Ok3 p) : bChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide +kernel

end VG.Proof.MlDsa.AArch64.Sign
