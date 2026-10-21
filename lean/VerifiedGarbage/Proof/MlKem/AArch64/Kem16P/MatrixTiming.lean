module

public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Matrix
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.MatrixTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.PairTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.LastTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemMatrixTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.PairTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-!
# The matrix computing PRF outputs leaks only public pointers and `ρ`

The pairs hashing the message by `Hybrid.hashPair_relCT`, `G` by a relation the caller proves, then, with each
run's invariant after `G` (`PRel`), the pairs computing PRF outputs
(`pairPCode_relCT`), the others (`Paired.pair_relCT`) and the singleton
(`lastCodeP_relCT` or `Paired.lastCode_relCT`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Kem16P

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Proof.MlKem.AArch64.Hybrid (Stk128 MT3 HRel Same hashPair_relCT)
open VG.Proof.MlKem.AArch64.Paired (exec_post)
open VG.Spec.MlKem
open VG.Proof.MlKem

variable {P : KemLay} {L : Layout}

/-- Both runs after `G`, `e` entries and the first `c` PRF outputs. -/
def PRel (P : KemLay) (L : Layout) (σ τ : State) (ρ : List Byte) (e c : Nat) (s u : State) : Prop :=
  (∃ m, PInvW true P L σ m ρ e c s) ∧ (∃ n, PInvW true P L τ n ρ e c u) ∧
  MT3 P L σ s ∧ MT3 P L τ u ∧ s.syms "VG_MLKEM_REJ_SHUFFLE" = u.syms "VG_MLKEM_REJ_SHUFFLE"

/-- The singleton's memory. -/
theorem layB_of {s₀ s : State} (hp : Pre P L s₀) {N₀ : Nat} (hN : N₀ + 3 ≤ 12) (h : KB P L s₀ s) :
    LayB (sA L s₀ SS) (sA L s₀ RB) (sA L s₀ (Impl.MlKem.AArch64.Kem16P.bufOff (TP P) N₀)) s := by
  have hw := hp.wf
  have bR := bufR_eq (L := L) (P := P) s₀ N₀
  exact ⟨cov_s hp h (o := SS) (l := 2048) (by lom), cov_sr hp h (o := RB) (l := 32) (by lom),
    sdisj hp (by lom) (by lom) (by lom), by rw [bR]; exact cov_s hp h (by lom),
    by rw [bR]; exact sdisj hp (by lom) (by lom) (by lom),
    by rw [bR]; exact sdisj hp (by lom) (by lom) (by lom)⟩

/-- The singleton's buffers, apart from the rest of its memory. -/
theorem apart_of {s₀ s : State} (hp : Pre P L s₀) {N₀ : Nat} (hN : N₀ + 3 ≤ 12) (tb : MT3 P L s₀ s) :
    BufApart (sA L s₀ SS) (sA L s₀ SB) (aP L s₀ (P.k * P.k - 1)) (s.syms "VG_MLKEM_REJ_SHUFFLE")
      (sA L s₀ RB) (sA L s₀ (Impl.MlKem.AArch64.Kem16P.bufOff (TP P) N₀)) := by
  have hw := hp.wf
  have hf := hw.facts
  have hkk : P.k * P.k ≤ 16 := hf.2.2.1
  have hk1 : 0 < P.k := hf.1
  have hn : 0 < P.k * P.k := Nat.mul_pos hk1 hk1
  have bR := bufR_eq (L := L) (P := P) s₀ N₀
  exact ⟨by rw [bR]; exact sdisj hp (by lom) (by lom) (by lom), by rw [bR]; exact sdisj hp (by lom) (by lom) (by lom),
    by rw [bR]; exact sdisj hp (o₂ := AH + 1024 * (P.k * P.k - 1)) (l₂ := 1024) (by lom) (by lom) (by lom),
    by rw [bR]; exact tb.t.apart.sub_right (scratch_sub hp (by lom))⟩

/-- A pair computing PRF outputs `N₀`, …, `N₀ + m - 1`. -/
theorem prfPair_relCT {M : Hybrid.Msg} {σ τ : State} (hp : Pre P L σ) (hq : Pre P L τ)
    (hk : Stk128 P L σ) (hk' : Stk128 P L τ) (sm : Same L M σ τ) {ρ : List Byte} {i N₀ m : Nat}
    (he : 2 * i + 1 < P.k * P.k) (hN : N₀ + 3 ≤ 12) (hm : m ≤ 3) :
    RelCT isa (PRel P L σ τ ρ (2 * i) N₀) (Impl.MlKem.AArch64.Kem16P.pairP SB SS AH RB (TP P) P (2 * i) N₀ m)
      (PRel P L σ τ ρ (2 * i + 2) (N₀ + m)) := by
  intro s u tr ur t v h et eu
  obtain ⟨⟨mσ, h₁⟩, ⟨mτ, h₂⟩, t₁, t₂, sh⟩ := h
  have hw := hp.wf
  have hbo : Impl.MlKem.AArch64.Kem16P.bufOff (TP P) (N₀ + 2) < 65536 := by
    simp only [Impl.MlKem.AArch64.Kem16P.bufOff]; lom
  have h4 : 4096 ≤ Impl.MlKem.AArch64.Kem16P.bufOff (TP P) N₀ := by
    simp only [Impl.MlKem.AArch64.Kem16P.bufOff]; lom
  have hf := hw.facts
  have hkk : P.k * P.k ≤ 16 := hf.2.2.1
  have hoa : AH + 1024 * (2 * i) < 65536 := by simp only [KEM.AH]; omega_using [he, hkk]
  have hob : AH + 1024 * (2 * i + 1) < 65536 := by simp only [KEM.AH]; omega_using [he, hkk]
  have ps := pair_input hp he h₁.b.kb t₁.t
  have hs := prf_input hp hk he hN h₁.b.kb t₁
  have pu := pair_input hq he h₂.b.kb t₂.t
  have hu := prf_input hq hk' he hN h₂.b.kb t₂
  have ba : ∀ o, sA L σ o = sA L τ o := fun o => congrArg (fun b => b + BitVec.ofNat 64 o) sm.base
  have aa : ∀ i, aP L σ i = aP L τ i := fun i => ba _
  rw [← ba SS, ← ba SB, ← aa (2 * i), ← aa (2 * i + 1), ← sh] at pu
  rw [← aa (2 * i), ← aa (2 * i + 1), ← ba SS, ← ba RB, ← ba (Impl.MlKem.AArch64.Kem16P.bufOff (TP P) N₀), ← sh,
    ← sm.base] at hu
  have seeds : ∀ j, Paired.seedState s.mem (sA L σ SB) j P.k = Paired.seedState u.mem (sA L σ SB) j P.k := by
    intro j
    rw [Paired.seedState_eq _ _ (by lom) (by lom), Paired.seedState_eq _ _ (by lom) (by lom)]
    unfold Paired.seedBytes
    rw [h₁.b.rho, ba SB, h₂.b.rho]
  have ct := pairPCode_relCT (w16 := true) P RB (TP P) (a := 2 * i) (m := m) (by omega) hbo h4 (by decide) (by decide)
    (by decide) hoa hob ps hs pu hu rfl (by decide) (by decide) rfl (by rw [h₁.b.kb.sp, h₂.b.kb.sp, sm.sp]) (seeds _) (seeds _)
  have ht := exec_post (paired_stepP hp hk he hN hm h₁ t₁) et
  have hv := exec_post (paired_stepP hq hk' he hN hm h₂ t₂) eu
  exact ⟨(ct _ _ _ _ _ _ ⟨rfl, rfl⟩ (pairP_exec et) (pairP_exec eu)).1, ⟨_, ht.1⟩, ⟨_, hv.1⟩, ht.2, hv.2,
    by rw [Exec.syms et, Exec.syms eu]; exact sh⟩

/-- A pair computing no PRF output after `G`. -/
theorem plainPairP_relCT {M : Hybrid.Msg} {σ τ : State} (hp : Pre P L σ) (hq : Pre P L τ)
    (sm : Same L M σ τ) {ρ : List Byte} {e c : Nat} (he : e + 1 < P.k * P.k) (hc : c ≤ 12) :
    RelCT isa (PRel P L σ τ ρ e c) (Impl.MlKem.AArch64.Paired.pair P false e true) (PRel P L σ τ ρ (e + 2) c) := by
  intro s u tr ur t v h et eu
  obtain ⟨⟨mσ, h₁⟩, ⟨mτ, h₂⟩, t₁, t₂, sh⟩ := h
  have hw := hp.wf
  have ps := pair_input hp he h₁.b.kb t₁.t
  have pu := pair_input hq he h₂.b.kb t₂.t
  have ba : ∀ o, sA L σ o = sA L τ o := fun o => congrArg (fun b => b + BitVec.ofNat 64 o) sm.base
  have aa : ∀ i, aP L σ i = aP L τ i := fun i => ba _
  rw [← ba SS, ← ba SB, ← aa e, ← aa (e + 1), ← sh] at pu
  have seeds : ∀ i, Paired.seedState s.mem (sA L σ SB) i P.k = Paired.seedState u.mem (sA L σ SB) i P.k := by
    intro i
    rw [Paired.seedState_eq _ _ (by lom) (by lom), Paired.seedState_eq _ _ (by lom) (by lom)]
    unfold Paired.seedBytes
    rw [h₁.b.rho, ba SB, h₂.b.rho]
  have ct := Paired.pair_relCT (w16 := true) (L := P) (kg := false) (a := e) (by decide) (by decide) (by decide)
    (by change AH + 1024 * e < 65536; lom) (by change AH + 1024 * (e + 1) < 65536; lom) ps pu
    (by rw [h₁.b.kb.sp, h₂.b.kb.sp, sm.sp]) (by rw [h₁.b.kb.x28, h₂.b.kb.x28, sm.base]) (seeds e) (seeds (e + 1))
  have ht := exec_post (paired_stepQ hp he hc h₁ t₁) et
  have hv := exec_post (paired_stepQ hq he hc h₂ t₂) eu
  exact ⟨(ct _ _ _ _ _ _ ⟨rfl, rfl⟩ et eu).1, ⟨_, ht.1⟩, ⟨_, hv.1⟩, ht.2, hv.2,
    by rw [Exec.syms et, Exec.syms eu]; exact sh⟩

/-- The singleton computing no PRF output after `G`. -/
theorem lastQ_relCT {M : Hybrid.Msg} {σ τ : State} (hp : Pre P L σ) (hq : Pre P L τ)
    (sm : Same L M σ τ) {ρ : List Byte} {e c : Nat} (he : e < P.k * P.k) (hc : c ≤ 12) :
    RelCT isa (PRel P L σ τ ρ e c) (Paired.lastCode SB SS e P.k (AH + 1024 * e) true)
      (PRel P L σ τ ρ (e + 1) c) := by
  intro s u tr ur t v h et eu
  obtain ⟨⟨mσ, h₁⟩, ⟨mτ, h₂⟩, t₁, t₂, sh⟩ := h
  have hw := hp.wf
  have ps := last_input hp he h₁.b.kb t₁.t
  have pu := last_input hq he h₂.b.kb t₂.t
  have ba : ∀ o, sA L σ o = sA L τ o := fun o => congrArg (fun b => b + BitVec.ofNat 64 o) sm.base
  have aa : ∀ i, aP L σ i = aP L τ i := fun i => ba _
  rw [← ba SS, ← ba SB, ← aa e, ← sh] at pu
  have seed : Paired.seedBytes s.mem (sA L σ SB) e P.k = Paired.seedBytes u.mem (sA L σ SB) e P.k := by
    unfold Paired.seedBytes
    rw [h₁.b.rho, ba SB, h₂.b.rho]
  have ct := Paired.lastCode_relCT (w16 := true) (by decide) (by decide) (by decide) (by lom) (by lom) (by lom)
    ps pu (sdisj hp (by lom) (by lom) (by lom))
    (by rw [h₁.b.kb.sp, h₂.b.kb.sp, sm.sp]) (by rw [h₁.b.kb.x28, h₂.b.kb.x28, sm.base]) seed
  have ht := exec_post (singleton_stepQ hp he hc h₁ t₁) et
  have hv := exec_post (singleton_stepQ hq he hc h₂ t₂) eu
  exact ⟨(ct _ _ _ _ _ _ ⟨rfl, rfl⟩ et eu).1, ⟨_, ht.1⟩, ⟨_, hv.1⟩, ht.2, hv.2,
    by rw [Exec.syms et, Exec.syms eu]; exact sh⟩

/-- The singleton computing PRF outputs `N₀`, `N₀ + 1`, `N₀ + 2` after `G`. -/
theorem lastPP_relCT {M : Hybrid.Msg} {σ τ : State} (hp : Pre P L σ) (hq : Pre P L τ)
    (hk : Stk128 P L σ) (hk' : Stk128 P L τ) (sm : Same L M σ τ) {ρ : List Byte} {N₀ : Nat}
    (hN : N₀ + 3 ≤ 12) :
    RelCT isa (PRel P L σ τ ρ (P.k * P.k - 1) N₀) (Impl.MlKem.AArch64.Kem16P.lastP P N₀)
      (PRel P L σ τ ρ (P.k * P.k - 1 + 1) (N₀ + 3)) := by
  intro s u tr ur t v h et eu
  obtain ⟨⟨mσ, h₁⟩, ⟨mτ, h₂⟩, t₁, t₂, sh⟩ := h
  have ht := exec_post (singleton_stepP hp hk hN h₁ t₁) et
  have hv := exec_post (singleton_stepP hq hk' hN h₂ t₂) eu
  have hw := hp.wf
  have hf := hw.facts
  have hkk : P.k * P.k ≤ 16 := hf.2.2.1
  have hk1 : 0 < P.k := hf.1
  have hn : 0 < P.k * P.k := Nat.mul_pos hk1 hk1
  have he : P.k * P.k - 1 < P.k * P.k := by omega
  have hoff : AH + 1024 * (P.k * P.k - 1) < 65536 := by simp only [KEM.AH]; omega_using [hkk]
  have hbo : Impl.MlKem.AArch64.Kem16P.bufOff (TP P) N₀ < 65536 := by
    simp only [Impl.MlKem.AArch64.Kem16P.bufOff]; lom
  have h4 : 4096 ≤ Impl.MlKem.AArch64.Kem16P.bufOff (TP P) N₀ := by
    simp only [Impl.MlKem.AArch64.Kem16P.bufOff]; lom
  have ps := last_input hp he h₁.b.kb t₁.t
  have pu := last_input hq he h₂.b.kb t₂.t
  have ls := layB_of hp hN h₁.b.kb
  have lu := layB_of hq hN h₂.b.kb
  have ba : ∀ o, sA L σ o = sA L τ o := fun o => congrArg (fun b => b + BitVec.ofNat 64 o) sm.base
  have aa : ∀ i, aP L σ i = aP L τ i := fun i => ba _
  rw [← ba SS, ← ba SB, ← aa (P.k * P.k - 1), ← sh] at pu
  rw [← ba SS, ← ba RB, ← ba (Impl.MlKem.AArch64.Kem16P.bufOff (TP P) N₀)] at lu
  have seed : Paired.seedBytes s.mem (sA L σ SB) (P.k * P.k - 1) P.k =
      Paired.seedBytes u.mem (sA L σ SB) (P.k * P.k - 1) P.k := by
    unfold Paired.seedBytes
    rw [h₁.b.rho, ba SB, h₂.b.rho]
  have ct := lastCodeP_relCT P (w16 := true) (a := P.k * P.k - 1) (by omega) hbo h4 (by decide) (by decide)
    (by decide) hoff hk1 (by omega) ps pu (sdisj hp (o₂ := AH + 1024 * (P.k * P.k - 1)) (l₂ := 1024)
      (by lom) (by lom) (by lom))
    ls lu (apart_of hp hN t₁) (e28 h₁.b.kb RB) (e28 h₁.b.kb _)
    (by rw [h₁.b.kb.sp, h₂.b.kb.sp, sm.sp]) (by rw [h₁.b.kb.x28, h₂.b.kb.x28, sm.base]) seed
  rw [lastP_eq] at et eu
  exact ⟨(ct _ _ _ _ _ _ ⟨rfl, rfl⟩ et eu).1, ⟨_, ht.1⟩, ⟨_, hv.1⟩, ht.2, hv.2,
    by rw [Exec.syms et, Exec.syms eu]; exact sh⟩

/-- A relation that also keeps each run's symbols. -/
theorem relCT_syms {c : Prog isa} {Pr Q : State → State → Prop} {s₀ u₀ : State} (h : RelCT isa Pr c Q) :
    RelCT isa (fun s u => Pr s u ∧ s.syms = s₀.syms ∧ u.syms = u₀.syms) c
      (fun s u => Q s u ∧ s.syms = s₀.syms ∧ u.syms = u₀.syms) := by
  intro s u tr ur t v hh et eu
  have r := h s u tr ur t v hh.1 et eu
  exact ⟨r.1, r.2, by rw [Exec.syms et]; exact hh.2.1, by rw [Exec.syms eu]; exact hh.2.2⟩

/-- **The matrix computing PRF outputs** leaks only public pointers and `ρ`, given that `G`
(`between`) takes the hashing pairs' relation to `PRel`. -/
theorem matrixP_relCT {M : Hybrid.Msg} {σ τ : State} (hp : Pre P L σ) (hq : Pre P L τ)
    (hk : Stk128 P L σ) (hk' : Stk128 P L τ) (hM : Hybrid.MsgOk P L M σ) (hM' : Hybrid.MsgOk P L M τ)
    (sm : Same L M σ τ) (ho : Hybrid.HashOk P M.S) {m n : Mem} {ρ Eσ Eτ : List Byte} {s₀ u₀ : State}
    (habs : ∀ blk, 136 * blk < M.S.len → ∃ h, (taint.check (Taint.ofRegs [M.S.r, .x28])
      (.block (Impl.MlKem.AArch64.Hybrid.absorbBlock M.S blk)) h).isSome = true)
    {between : Prog isa}
    (hb : RelCT isa (fun s u => HRel true P L M σ τ m n ρ Eσ Eτ (2 * Impl.MlKem.AArch64.Hybrid.hashPairs M.S)
        (Impl.MlKem.AArch64.Hybrid.hashPairs M.S) s u ∧ s.syms = s₀.syms ∧ u.syms = u₀.syms) between
      (PRel P L σ τ ρ (2 * Impl.MlKem.AArch64.Hybrid.hashPairs M.S) 0)) :
    RelCT isa (fun s u => HRel true P L M σ τ m n ρ Eσ Eτ 0 0 s u ∧ s.syms = s₀.syms ∧ u.syms = u₀.syms)
      (Impl.MlKem.AArch64.Kem16P.matrixP P M.S between)
      (PRel P L σ τ ρ (P.k * P.k) (finalCount P (Impl.MlKem.AArch64.Hybrid.hashPairs M.S))) := by
  have hw := hp.wf
  have hk1 : 0 < P.k := hw.facts.1
  have hn : 0 < P.k * P.k := Nat.mul_pos hk1 hk1
  have hP := ho.pairs
  have h9 := placed_le (P := P) (hp := Impl.MlKem.AArch64.Hybrid.hashPairs M.S) hw
  have hlen : ∀ i < Impl.MlKem.AArch64.Hybrid.hashPairs M.S, 136 * (3 * i + 2) < M.S.len := by
    intro i hi
    have := ho.part; have := ho.three
    simp only [Impl.MlKem.AArch64.Hybrid.hashPairs, Impl.MlKem.AArch64.Hybrid.blocks] at hi
    omega
  generalize hH : Impl.MlKem.AArch64.Hybrid.hashPairs M.S = H at hP h9 hb hlen ⊢
  have hpairs : Impl.MlKem.AArch64.Kem16P.pairs P = P.k * P.k / 2 := rfl
  unfold Impl.MlKem.AArch64.Kem16P.matrixP
  simp only [hH, filter_lt_range, filter_ge_range, List.map_map]
  rw [show min H (Impl.MlKem.AArch64.Kem16P.pairs P) = H by omega]
  apply RelCTs.seqs (by simp)
  refine RelCTs.append (R := PRel P L σ τ ρ (2 * (Impl.MlKem.AArch64.Kem16P.pairs P - H + H))
      (min (Impl.MlKem.AArch64.Kem16P.placed P H) (3 * (Impl.MlKem.AArch64.Kem16P.pairs P - H))))
    (RelCTs.append (R := PRel P L σ τ ρ (2 * H) 0) (RelCTs.append ?_ ⟨_, hb, fun _ _ h => h⟩) ?_) ?_
  -- The pairs hashing the message.
  · have r := RelCTs.range (n := H) (f := fun i => Impl.MlKem.AArch64.Hybrid.pair3 P M.S (2 * i) i true)
      (I := fun i s u => HRel true P L M σ τ m n ρ Eσ Eτ (2 * i) i s u ∧ s.syms = s₀.syms ∧ u.syms = u₀.syms)
      fun i hi => by
        rw [show 2 * (i + 1) = 2 * i + 2 by omega]
        exact relCT_syms (hashPair_relCT hp hq hk hk' hM hM' sm (by omega) (hlen i hi) habs)
    simpa only [Nat.mul_zero] using r
  -- The pairs computing PRF outputs.
  · have r := RelCTs.range (n := Impl.MlKem.AArch64.Kem16P.pairs P - H)
      (I := fun j => PRel P L σ τ ρ (2 * (j + H)) (min (Impl.MlKem.AArch64.Kem16P.placed P H) (3 * j)))
      (f := (fun i => if Impl.MlKem.AArch64.Kem16P.pairCount P H i = 0 then Paired.pair P false (2 * i) true
        else Impl.MlKem.AArch64.Kem16P.pairP SB SS AH RB (TP P) P (2 * i) (3 * (i - H)) (Impl.MlKem.AArch64.Kem16P.pairCount P H i)) ∘
          (· + H))
      fun j hj => by
        have he : 2 * (j + H) + 1 < P.k * P.k := by omega
        simp only [Function.comp]
        rw [show 2 * (j + 1 + H) = 2 * (j + H) + 2 by omega]
        by_cases hc : Impl.MlKem.AArch64.Kem16P.pairCount P H (j + H) = 0
        · rw [ite_eq_left hc]
          have hc' : Impl.MlKem.AArch64.Kem16P.placed P H ≤ 3 * j := by
            simp only [Impl.MlKem.AArch64.Kem16P.pairCount] at hc; omega
          rw [show min (Impl.MlKem.AArch64.Kem16P.placed P H) (3 * (j + 1)) =
            min (Impl.MlKem.AArch64.Kem16P.placed P H) (3 * j) by omega]
          exact plainPairP_relCT hp hq sm he (by omega)
        · rw [ite_eq_right hc]
          have hc' : 3 * j < Impl.MlKem.AArch64.Kem16P.placed P H := by
            simp only [Impl.MlKem.AArch64.Kem16P.pairCount] at hc; omega
          rw [show min (Impl.MlKem.AArch64.Kem16P.placed P H) (3 * j) = 3 * (j + H - H) by omega,
            show min (Impl.MlKem.AArch64.Kem16P.placed P H) (3 * (j + 1)) =
              3 * (j + H - H) + Impl.MlKem.AArch64.Kem16P.pairCount P H (j + H) by
              simp only [Impl.MlKem.AArch64.Kem16P.pairCount]; omega]
          exact prfPair_relCT hp hq hk hk' sm he (by omega)
            (by simp only [Impl.MlKem.AArch64.Kem16P.pairCount]; omega)
    simpa only [Nat.zero_add, Nat.mul_zero, Nat.min_zero] using r
  -- The singleton.
  · rw [show Impl.MlKem.AArch64.Kem16P.pairs P - H + H = P.k * P.k / 2 by omega]
    by_cases hodd : Impl.MlKem.AArch64.Kem16P.single P = true
    · rw [ite_eq_left hodd]
      have hodd' : P.k * P.k % 2 = 1 := by
        simpa [Impl.MlKem.AArch64.Kem16P.single] using hodd
      rw [show 2 * (P.k * P.k / 2) = P.k * P.k - 1 by omega]
      by_cases hl : Impl.MlKem.AArch64.Kem16P.placed P H ≥ 3 * (Impl.MlKem.AArch64.Kem16P.pairs P - H) + 3
      · rw [ite_eq_left hl, show min (Impl.MlKem.AArch64.Kem16P.placed P H)
          (3 * (Impl.MlKem.AArch64.Kem16P.pairs P - H)) = 3 * (Impl.MlKem.AArch64.Kem16P.pairs P - H) by omega]
        refine ⟨_, lastPP_relCT hp hq hk hk' sm (by omega), fun s u h => ?_⟩
        rw [Nat.sub_add_cancel hn] at h
        simpa only [finalCount, hodd, hl, and_self, ite_true] using h
      · rw [ite_eq_right hl, Paired.lastSample_eq]
        refine ⟨_, lastQ_relCT hp hq sm (by omega : P.k * P.k - 1 < P.k * P.k) (by omega), fun s u h => ?_⟩
        rw [Nat.sub_add_cancel hn] at h
        simpa only [finalCount, hodd, hl, and_false, ite_false, Bool.false_eq_true] using h
    · rw [ite_eq_right hodd]
      have hev : P.k * P.k % 2 = 0 := by
        simp only [Impl.MlKem.AArch64.Kem16P.single, decide_eq_true_eq] at hodd; omega
      rw [show 2 * (P.k * P.k / 2) = P.k * P.k by omega]
      intro s u h
      simpa only [finalCount, hodd, Bool.false_eq_true, false_and, ite_false] using h

end VG.Proof.MlKem.AArch64.Kem16P
