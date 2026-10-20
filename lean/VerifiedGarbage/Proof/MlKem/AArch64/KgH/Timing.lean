module

import VerifiedGarbage.Proof.MlKem.AArch64.KgH.Matrix
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TopTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.PairTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.LastTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.PairTiming
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixPair
public import VerifiedGarbage.Impl.MlKem.AArch64.Hybrid
public import VerifiedGarbage.Proof.MlKem.AArch64.Lay
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.State
public import VerifiedGarbage.Proof.MlKem.AArch64.KgH.Inv
import VerifiedGarbage.Proof.MlKem.AArch64.KgH.Pair
import VerifiedGarbage.Proof.MlKem.AArch64.KgH.Row

/-! # The matrix with the rows of `t̂` between its pairs leaks only public data

`matrixRows_relCT`: two runs with the same pointers, stack pointer, `ρ` and
constant tables, through `Kem16.kgMatrixRows`, leak the same: each hashing pair
by `Hybrid.pairMCode_relCT` (its timing depends on `ρ` alone; the blocks of
`ek` it absorbs by the taint analysis, `habs`), the final entry by
`Paired.lastCode_relCT`, and each row of `t̂` by the taint analysis, from the
pointers and the symbols (`hrow`). -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Optimized
open VG.Impl.MlKem.AArch64.Kem16 (rowsBy hashedBy kgRows kgPair kgMatrixRows)
open VG.Spec.Sha3 (bytesAt stateAt)

variable {P : KemLay}

/-- What both runs share: pointers, the stack pointer and `ρ`. -/
structure SameK (P : KemLay) (σ τ : State) : Prop where
  ptr : ∀ i, kA σ i = kA τ i
  sp : σ.sp = τ.sp
  rho : rhoK P σ = rhoK P τ

/-- Both runs after `n` entries, `r` rows and `h` blocks, with the same symbols. -/
def KR (P : KemLay) (σ τ : State) (n r h : Nat) (s u : State) : Prop :=
  IL P σ n r h s ∧ IL P τ n r h u ∧ s.syms "VG_MLKEM_REJ_SHUFFLE" = u.syms "VG_MLKEM_REJ_SHUFFLE" ∧
    ∀ name ∈ restSymbols, s.syms name = u.syms name

theorem KR.syms {σ τ s u t v : State} {n r h n' r' h' : Nat} (H : KR P σ τ n r h s u)
    {tr ur : List Leak} {c : Prog isa} (et : Exec isa c s tr t) (eu : Exec isa c u ur v)
    (ht : IL P σ n' r' h' t) (hv : IL P τ n' r' h' v) : KR P σ τ n' r' h' t v :=
  ⟨ht, hv, by rw [Exec.syms et, Exec.syms eu]; exact H.2.2.1,
    fun name hn => by rw [Exec.syms et, Exec.syms eu]; exact H.2.2.2 name hn⟩

/-- **A row of `t̂`** leaks only the pointers. -/
theorem row_relCT {σ τ : State} (hp : Pre P σ) (hq : Pre P τ) (hr : Noise.Room P) (sm : SameK P σ τ)
    {n r h : Nat} (hrk : r < P.k) (hn : P.k * (r + 1) ≤ n)
    (hrow : ∃ h, ((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28])
      (Kem16.kgRow P r) h).isSome = true) :
    RelCT isa (KR P σ τ n r h) (Kem16.kgRow P r) (KR P σ τ n (r + 1) h) := by
  intro s u tr ur t v H et eu
  have ks := H.1.b.kb
  have ku := H.2.1.b.kb
  refine ⟨symbol_taint [.x25,.x26,.x27,.x28] (by rw [ks.sp, ku.sp, sm.sp]) (fun q hq => ?_) H.2.2.2 hrow et eu,
    H.syms et eu (Paired.exec_post (row_step hp hr hrk hn H.1) et)
      (Paired.exec_post (row_step hq hr hrk hn H.2.1) eu)⟩
  rcases mem4 hq with rfl | rfl | rfl | rfl
  · rw [ks.x25, ku.x25, sm.ptr 0]
  · rw [ks.x26, ku.x26, sm.ptr 1]
  · rw [ks.x27, ku.x27, sm.ptr 2]
  · rw [ks.x28, ku.x28, sm.ptr 3]

theorem seeds_eq {σ τ s u : State} (hw : P.Wf) (sm : SameK P σ τ) {n r h n' r' h' : Nat}
    (hs : IL P σ n r h s) (hu : IL P τ n' r' h' u) (i : Nat) :
    Paired.seedState s.mem (kA σ 3+BitVec.ofNat 64 SB) i P.k =
      Paired.seedState u.mem (kA σ 3+BitVec.ofNat 64 SB) i P.k := by
  rw [Paired.seedState_eq _ _ (by lom) (by lom), Paired.seedState_eq _ _ (by lom) (by lom)]
  unfold Paired.seedBytes
  rw [hs.b.rho, sm.ptr 3, hu.b.rho, sm.rho]

/-- **A hashing pair** leaks only the pointers and `ρ`. -/
theorem pairH_relCT {σ τ : State} (hp : Pre P σ) (hq : Pre P τ) (hk : Stk128K P σ) (hk' : Stk128K P τ)
    (hr : Noise.Room P) (sm : SameK P σ τ) {p r h m : Nat}
    (he : 2*p+1 < P.k*P.k) (hm : m ≤ 3) (hb : ∀ k < m, 136*(h+k) < P.ekLen) (hhr : 136*(h+m) ≤ 384*r)
    (habs : ∀ blk, 136 * blk < (Kem16.kgSrc P).len → ∃ h, (taint.check (Taint.ofRegs [(Kem16.kgSrc P).r, .x28])
      (.block (Hybrid.absorbBlock (Kem16.kgSrc P) blk)) h).isSome = true) :
    RelCT isa (KR P σ τ (2*p) r h) (Hybrid.pairM SB SS AH P (Kem16.kgSrc P) (2*p) h m true)
      (KR P σ τ (2*p+2) r (h+m)) := by
  intro s u tr ur t v H et eu
  have hw := hp.wf
  have hf := hw.facts
  have hkk : P.k * P.k ≤ 16 := hf.2.2.1
  have hoa : AH+1024*(2*p)<65536 := by simp only [KG.AH]; omega
  have hob : AH+1024*(2*p+1)<65536 := by simp only [KG.AH]; omega
  have ks := H.1.b.kb
  have ku := H.2.1.b.kb
  have ms := matrixTable_of hp ks H.1.tables
  have mu := matrixTable_of hq ku H.2.1.tables
  have ps := pair_input hp he ks ms
  have pu := pair_input hq he ku mu
  have hs := hash_inputK hp hk he ks H.1.tstk ms
  have hu := hash_inputK hq hk' he ku H.2.1.tstk mu
  rw [← sm.ptr 3, ← H.2.2.1] at pu
  rw [← sm.ptr 3, ← sm.ptr 1, ← H.2.2.1] at hu
  have hash₂ := H.2.1.hash
  rw [← sm.ptr 3, ← sm.ptr 1] at hash₂
  have ct := Hybrid.pairMCode_relCT (w16 := true) (a := 2*p) (j := h) (m := m) P (Kem16.kgSrc P) (srcOkK hw)
    (by decide) (by decide) (by decide) hoa hob ps hs pu hu (fun k hk _ => hb k hk) H.1.hash rfl hash₂ rfl
    (by rw [ks.sp, ku.sp, sm.sp]) (seeds_eq hw sm H.1 H.2.1 (2*p)) (seeds_eq hw sm H.1 H.2.1 (2*p+1)) habs
  exact ⟨(ct _ _ _ _ _ _ ⟨rfl, rfl⟩ (Hybrid.pairM_exec et) (Hybrid.pairM_exec eu)).1,
    H.syms et eu (Paired.exec_post (pair_step hp hk hr he hm hb hhr H.1) et)
      (Paired.exec_post (pair_step hq hk' hr he hm hb hhr H.2.1) eu)⟩

/-- **The final entry** of an odd matrix leaks only the pointers and `ρ`. -/
theorem lastH_relCT {σ τ : State} (hp : Pre P σ) (hq : Pre P τ) (hr : Noise.Room P) (sm : SameK P σ τ)
    {r h : Nat} (hodd : P.k * P.k % 2 = 1) :
    RelCT isa (KR P σ τ (P.k*P.k-1) r h) (Paired.lastSample P true true) (KR P σ τ (P.k*P.k) r h) := by
  intro s u tr ur t v H et eu
  have hw := hp.wf
  have he : P.k * P.k - 1 < P.k * P.k := by omega
  have ks := H.1.b.kb
  have ku := H.2.1.b.kb
  have ps := last_input hp he ks (matrixTable_of hp ks H.1.tables)
  have pu := last_input hq he ku (matrixTable_of hq ku H.2.1.tables)
  rw [← sm.ptr 3, ← H.2.2.1] at pu
  have seed : Paired.seedBytes s.mem (kA σ 3+BitVec.ofNat 64 SB) (P.k*P.k-1) P.k =
      Paired.seedBytes u.mem (kA σ 3+BitVec.ofNat 64 SB) (P.k*P.k-1) P.k := by
    unfold Paired.seedBytes
    rw [H.1.b.rho, sm.ptr 3, H.2.1.b.rho, sm.rho]
  have ct := Paired.lastCode_relCT (w16 := true) (by decide) (by decide) (by decide) (by lom) (by lom) (by lom)
    ps pu (hp.args.rdisj (b₁:=3) (b₂:=3) (o₁:=SB) (l₁:=32) (o₂:=AH+1024*(P.k*P.k-1)) (l₂:=1024)
      (by decide) (by decide) (by kl) (matrixEntry_fit hw he) (by lom))
    (by rw [ks.sp, ku.sp, sm.sp]) (by rw [ks.x28, ku.x28, sm.ptr 3]) seed
  have ht := Paired.exec_post (last_step hp hr hodd H.1) et
  have hv := Paired.exec_post (last_step hq hr hodd H.2.1) eu
  have hsy := H.syms et eu ht hv
  rw [Paired.lastSample_eq] at et eu
  simp only [ite_true] at et eu
  exact ⟨(ct _ _ _ _ _ _ ⟨rfl, rfl⟩ et eu).1, hsy⟩

/-- `n` steps, each a list of programs, by a relational invariant `I i` before step `i`. -/
theorem relcts_flatMap_range {f : Nat → List (Prog isa)} {I : Nat → State → State → Prop} :
    ∀ {n : Nat}, (∀ i < n, RelCTs (I i) (f i) (I (i + 1))) → RelCTs (I 0) ((List.range n).flatMap f) (I n)
  | 0, _ => fun _ _ h => h
  | n + 1, hf => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact RelCTs.append (relcts_flatMap_range fun i hi => hf i (by omega)) (hf n (by omega))

/-- Rows `a` to `b - 1` of `t̂` leak only the pointers. -/
theorem rows_relCT {σ τ : State} (hp : Pre P σ) (hq : Pre P τ) (hr : Noise.Room P) (sm : SameK P σ τ)
    (hrow : ∀ i < P.k, ∃ h, ((VectorSymbols.analysis restSymbols).check
      (VectorTaint.ofRegs [.x25,.x26,.x27,.x28]) (Kem16.kgRow P i) h).isSome = true) {n h : Nat} :
    ∀ (d a b : Nat), b - a = d → a ≤ b → b ≤ P.k → P.k * b ≤ n →
      RelCTs (KR P σ τ n a h) (kgRows P a b) (KR P σ τ n b h)
  | 0, a, b, hd, hab, _, _ => by
    have e : b = a := by omega
    subst e
    simp only [kgRows, Nat.sub_self, List.range'_zero, List.map_nil, RelCTs]
    exact fun _ _ h => h
  | d + 1, a, b, hd, hab, hbk, hn => by
    have e : kgRows P a b = Kem16.kgRow P a :: kgRows P (a + 1) b := by
      simp only [kgRows, hd, show b - (a + 1) = d by omega, List.range'_succ, List.map_cons]
    rw [e]
    exact ⟨_, row_relCT hp hq hr sm (r := a) (by omega)
      (Nat.le_trans (Nat.mul_le_mul_left _ (by omega)) hn) (hrow a (by omega)),
      rows_relCT hp hq hr sm hrow d (a + 1) b (by omega) (by omega) hbk hn⟩

/-- **The matrix and the rows of `t̂`** leak only the pointers and `ρ`. -/
theorem matrixRows_relCT {σ τ : State} (hp : Pre P σ) (hq : Pre P τ) (hk : Stk128K P σ) (hk' : Stk128K P τ)
    (hr : Noise.Room P) (sm : SameK P σ τ)
    (habs : ∀ blk, 136 * blk < (Kem16.kgSrc P).len → ∃ h, (taint.check (Taint.ofRegs [(Kem16.kgSrc P).r, .x28])
      (.block (Hybrid.absorbBlock (Kem16.kgSrc P) blk)) h).isSome = true)
    (hrow : ∀ i < P.k, ∃ h, ((VectorSymbols.analysis restSymbols).check
      (VectorTaint.ofRegs [.x25,.x26,.x27,.x28]) (Kem16.kgRow P i) h).isSome = true) :
    RelCTs (KR P σ τ 0 0 0) (kgMatrixRows P) (KR P σ τ (P.k * P.k) P.k (hashedBy P (P.k * P.k / 2))) := by
  have hw := hp.wf
  have hf := hw.facts
  have hek : 384 * P.k < P.ekLen := by simp only [KemLay.ekLen]; omega
  have pairs := relcts_flatMap_range (n := P.k * P.k / 2)
    (I := fun p => KR P σ τ (2 * p) (rowsBy P p) (hashedBy P p))
    (f := fun p => kgPair P p :: kgRows P (rowsBy P p) (rowsBy P (p + 1)))
    (fun p hp' => by
      have hmono := rowsBy_mono P p
      have hle := rowsBy_le P (p + 1)
      have hrk := rowsBy_le P p
      have pc := pairH_relCT hp hq hk hk' hr sm (p := p) (r := rowsBy P p) (h := hashedBy P p)
        (m := hashedBy P (p + 1) - hashedBy P p) (by omega)
        (by simp only [hashedBy]; omega) (fun k hk' => by
          have := Nat.mul_le_mul_left 384 hrk
          have h3 := hashed_le P (p + 1)
          simp only [hashedBy] at h3 hk' ⊢
          have : 136 * (384 * rowsBy P p / 136) ≤ 384 * rowsBy P p := Nat.mul_div_le _ _
          omega) (by
          rw [← hashed_succ]
          have hA : hashedBy P p ≤ 384 * rowsBy P p / 136 :=
            (Nat.le_div_iff_mul_le (by decide)).2 (by have := hashed_le P p; omega)
          have hB : 136 * (384 * rowsBy P p / 136) ≤ 384 * rowsBy P p := Nat.mul_div_le _ _
          simp only [hashedBy]
          have := Nat.min_le_right 3 (384 * rowsBy P p / 136 - hashedBy P p)
          omega) habs
      rw [← hashed_succ] at pc
      exact ⟨_, pc, rows_relCT hp hq hr sm hrow (rowsBy P (p + 1) - rowsBy P p) (rowsBy P p) (rowsBy P (p + 1))
        rfl hmono hle (Nat.le_trans (rowsBy_mul P (p + 1)) (by omega))⟩)
  rw [show rowsBy P 0 = 0 by simp [rowsBy], show hashedBy P 0 = 0 from rfl, Nat.mul_zero] at pairs
  rw [kgMatrixRows]
  refine RelCTs.append pairs ?_
  have hle := rowsBy_le P (P.k * P.k / 2)
  by_cases ho : P.k * P.k % 2 = 1
  · rw [ite_eq_left ho]
    have e : 2 * (P.k * P.k / 2) = P.k * P.k - 1 := by omega
    refine ⟨KR P σ τ (P.k * P.k) (rowsBy P (P.k * P.k / 2)) (hashedBy P (P.k * P.k / 2)), ?_,
      rows_relCT hp hq hr sm hrow _ _ P.k rfl hle (Nat.le_refl _) (Nat.le_refl _)⟩
    rw [e]
    exact lastH_relCT hp hq hr sm ho
  · rw [ite_eq_right ho]
    have e : 2 * (P.k * P.k / 2) = P.k * P.k := by omega
    have er : rowsBy P (P.k * P.k / 2) = P.k := by
      simp only [rowsBy, e, Nat.mul_div_cancel_left _ (show 0 < P.k by omega), Nat.min_self]
    intro s u h
    rwa [e, er] at h

end VG.Proof.MlKem.AArch64.KeyGen
