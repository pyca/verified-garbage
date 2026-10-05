import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Steps
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Core
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Reduce
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Search

/-!
# Deterministic ECDSA on AArch64: the candidates

The values of a run, as RFC 6979 computes them from the private key and the
digest on entry (`kvI`, `candI`, `sigI`); the loop's invariant before
candidate `i` (`LoopInv`): `K` and `V` are those before it, the count is
`8 - i`, and every earlier candidate was unsuitable. One iteration either
moves to candidate `i + 1`, branching back, or leaves the loop with the
signature of candidate `i`, which is suitable or the last (`tryOne_ok`,
`loop_ok`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64
open VG.Proof.Ecdsa.Rfc6979 (kvAt candAt step)

variable {P : RfcHash} {L : Lay P.I.hashLen} {g : Reg → BitVec 64} {m₀ : Mem}

/-! ## The run's values -/

/-- The private key, the digest and its integer. -/
abbrev xOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m₀ : Mem) : Nat :=
  Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.d (8 * P.w))
abbrev hBOf (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte := Spec.Sha256.bytesAt m₀ L.dg P.H.D
abbrev eOf (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : Nat := Spec.Ecdsa.hashToInt P.R.E.C (hBOf P L m₀)

/-- `K` and `V` after steps b–g. -/
abbrev kv0 (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte × List Byte :=
  Spec.Ecdsa.Rfc6979.init P.R.E.C P.ok.SH.H P.H.D (xOf P L m₀) (hBOf P L m₀)

/-- `K` and `V` before candidate `i`, candidate `i`'s `V`, and its signature, with
`k` the leftmost `8 w` bytes of `V`. -/
abbrev kvI (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) : List Byte × List Byte :=
  kvAt P.ok.SH.H (kv0 P L m₀).1 (kv0 P L m₀).2 i
abbrev candI (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) : List Byte :=
  candAt P.ok.SH.H (kv0 P L m₀).1 (kv0 P L m₀).2 i
abbrev sigI (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) : Option (Nat × Nat) :=
  Spec.Ecdsa.signWith P.R.E.C (xOf P L m₀) (eOf P L m₀) (Spec.Weierstrass.ofBytes ((candI P L m₀ i).take (8 * P.w)))

/-- What the function's result is, for the signature `r` of the last candidate. -/
def ResultIs (P : RfcHash) {dn : Nat} (L : Lay dn) (r : Option (Nat × Nat)) (t : State) : Prop :=
  match r with
  | some rs => (t.gpr .x0).setWidth 32 = 1 ∧
      Spec.Sha256.bytesAt t.mem L.out (16 * P.w) = Spec.Ecdsa.encode P.R.E.C rs
  | none => (t.gpr .x0).setWidth 32 = 0 ∧
      Spec.Sha256.bytesAt t.mem L.out (16 * P.w) = List.replicate (16 * P.w) 0

/-- Before candidate `i`. -/
structure LoopInv (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  lt : i < 8
  k : kOf P L t.mem = (kvI P L m₀ i).1
  v : vOf P L t.mem = (kvI P L m₀ i).2
  cnt : cnt L t.mem = BitVec.ofNat 64 (8 - i)
  fails : ∀ j < i, sigI P L m₀ j = none

/-- After the loop, at candidate `i`: suitable or the last. -/
structure Exit (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  lt : i < 8
  fails : ∀ j < i, sigI P L m₀ j = none
  last : sigI P L m₀ i ≠ none ∨ i = 7
  res : ResultIs P L (sigI P L m₀ i) t

/-! ## Facts kept -/

theorem Ctx.dBytes (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {n : Nat} (hn : n ≤ L.q) :
    Spec.Sha256.bytesAt t.mem L.d n = Spec.Sha256.bytesAt m₀ L.d n := by
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi => hc.d_byte hL (by have := List.mem_range.mp hi; omega)

theorem Ctx.dgBytes (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {n : Nat} (hn : n ≤ P.I.hashLen) :
    Spec.Sha256.bytesAt t.mem L.dg n = Spec.Sha256.bytesAt m₀ L.dg n := by
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi => hc.dg_byte hL (by have := List.mem_range.mp hi; omega)

/-- The count, kept by memory that changed elsewhere. -/
theorem cnt_frame {ws : List Region} {m m' : Mem} (hf : Frame ws m m')
    (hd : ∀ r ∈ ws, Region.Disjoint ⟨L.B + BitVec.ofNat 64 192, 8⟩ r) : cnt L m' = cnt L m :=
  hf.readW (Region.contains_self _ _) hd (by decide)

theorem kvw_cnt (hL : L.Ok) : ∀ r ∈ KVW L, Region.Disjoint ⟨L.B + BitVec.ofNat 64 192, 8⟩ r := by
  simp only [KVW, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact hL.stk_SCR (by anums)
  · exact Offset.disjoint_base _ (by anums) (by anums)

/-- What `core` changes: `out` and `scratch`. -/
abbrev CoreW {dn : Nat} (L : Lay dn) : List Region := [L.OUT, L.SCR]

theorem corew_disj (hL : L.Ok) {d n : Nat} (h₂ : d + n ≤ 256) :
    ∀ r ∈ CoreW L, Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := by
  simp only [CoreW, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact hL.stk_OUT h₂
  · exact hL.stk_SCR h₂

theorem cnt_sub {i : Nat} (hi : i < 8) : BitVec.ofNat 64 (8 - i) - 1 = BitVec.ofNat 64 (8 - (i + 1)) := by
  have : ∀ i < 8, BitVec.ofNat 64 (8 - i) - 1 = BitVec.ofNat 64 (8 - (i + 1)) := by decide
  exact this i hi

theorem cnt_ne {i : Nat} (hi : i < 8) : BitVec.ofNat 64 (8 - (i + 1)) ≠ 0 ↔ i + 1 < 8 := by
  have : ∀ i < 8, (BitVec.ofNat 64 (8 - (i + 1)) ≠ 0 ↔ i + 1 < 8) := by decide
  exact this i hi

theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (Spec.Sha256.bytesAt m p n).length = n := by
  simp [Spec.Sha256.bytesAt]

/-- `core`'s signature is the candidate's: it reads the leftmost `8 w` bytes
of `V` and of the digest. -/
theorem coreSig_eq (hL : L.Ok) (hq : L.q = 8 * P.w) {t : State} (hc : Ctx L g m₀ t) {i : Nat}
    (hv : vOf P L t.mem = candI P L m₀ i) : coreSig P L t.mem = sigI P L m₀ i := by
  have hQ := P.lenQ
  have hw : P.w = P.R.E.n := rfl
  have hD : 8 * P.w ≤ P.H.D := by rw [← P.len]; exact hQ
  have hB : Spec.Ecdsa.nBits P.R.E.C = 8 * (8 * P.w) := by rw [P.R.nBits]; omega
  have hv' : Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 80) P.H.D = candI P L m₀ i := hv
  have e₁ : Spec.Ecdsa.hashToInt P.R.E.C (Spec.Sha256.bytesAt t.mem L.dg (8 * P.w)) =
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg (8 * P.w)) := by
    rw [hashToInt_takeQ hB (by rw [length_bytesAt]), List.take_of_length_le (by rw [length_bytesAt]),
      hc.dgBytes hL hQ]
  have e₂ : Spec.Ecdsa.hashToInt P.R.E.C (Spec.Sha256.bytesAt m₀ L.dg P.H.D) =
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg (8 * P.w)) := by
    rw [hashToInt_takeQ hB (by rw [length_bytesAt]; exact hD), ← bytesAt_take m₀ L.dg hD]
  have e₃ : Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 80) (8 * P.w) = (candI P L m₀ i).take (8 * P.w) := by
    rw [bytesAt_take _ (L.B + BitVec.ofNat 64 80) hD, hv']
  have e₄ : Spec.Sha256.bytesAt t.mem L.d (8 * P.w) = Spec.Sha256.bytesAt m₀ L.d (8 * P.w) :=
    hc.dBytes hL (by omega)
  simp only [coreSig, coreSigOf, ecdsa_bytesAt, sigI, eOf, hBOf, xOf]
  rw [← hw, e₁, e₂, e₃, e₄]

theorem ResultIs.eax_zero {r : Option (Nat × Nat)} {t : State} (h : ResultIs P L r t) :
    (t.gpr .x0).setWidth 32 = 0 ↔ r = none := by
  cases r with
  | none => exact ⟨fun _ => rfl, fun _ => h.1⟩
  | some rs => exact ⟨fun h' => by rw [h.1] at h'; exact absurd h' (by decide), fun h' => by cases h'⟩

/-- The result, kept by code that keeps `rax` and changes memory elsewhere. -/
theorem ResultIs.keep {r : Option (Nat × Nat)} {t t' : State} (h : ResultIs P L r t) (ha : t'.gpr .x0 = t.gpr .x0)
    (hm : Spec.Sha256.bytesAt t'.mem L.out (16 * P.w) = Spec.Sha256.bytesAt t.mem L.out (16 * P.w)) :
    ResultIs P L r t' := by
  cases r with
  | none => exact ⟨by rw [ha]; exact h.1, by rw [hm]; exact h.2⟩
  | some rs => exact ⟨by rw [ha]; exact h.1, by rw [hm]; exact h.2⟩

/-! ## One candidate -/

/-- After `V = HMAC_K(V)`: candidate `i`'s `V`. -/
structure P₁ (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (u : State) : Prop where
  lt : i < 8
  k : kOf P L u.mem = (kvI P L m₀ i).1
  v : vOf P L u.mem = candI P L m₀ i
  cnt : cnt L u.mem = BitVec.ofNat 64 (8 - i)
  fails : ∀ j < i, sigI P L m₀ j = none

/-- `core`'s arguments. -/
structure Args {dn : Nat} (L : Lay dn) (u : State) : Prop where
  x0 : u.gpr .x0 = L.out
  x1 : u.gpr .x1 = L.d
  x2 : u.gpr .x2 = L.dg
  x3 : u.gpr .x3 = L.B + BitVec.ofNat 64 80
  x4 : u.gpr .x4 = L.scr

/-- After `core`: its result. -/
structure P₃ (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (u : State) : Prop where
  lt : i < 8
  k : kOf P L u.mem = (kvI P L m₀ i).1
  v : vOf P L u.mem = candI P L m₀ i
  cnt : cnt L u.mem = BitVec.ofNat 64 (8 - i)
  fails : ∀ j < i, sigI P L m₀ j = none
  res : ResultIs P L (sigI P L m₀ i) u

/-- After the decision: whether to go on. -/
structure Mid (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (i : Nat) (u : State) : Prop where
  lt : i < 8
  k : kOf P L u.mem = (kvI P L m₀ i).1
  v : vOf P L u.mem = candI P L m₀ i
  cnt : cnt L u.mem = BitVec.ofNat 64 (8 - (i + 1))
  fails : ∀ j < i, sigI P L m₀ j = none
  res : ResultIs P L (sigI P L m₀ i) u
  dec : isa.eval (.nonzero .x .x12) u = some (decide (sigI P L m₀ i = none ∧ i + 1 < 8))

theorem try₁_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : LoopInv P L m₀ i t) :
    WP isa (cfgOf P).hmacV t fun u => Ctx L g m₀ u ∧ P₁ P L m₀ i u :=
  WP.mono (hmacV_ok hL hc) fun u₁ ⟨hc₁, hf₁, hk₁, hv₁⟩ => ⟨hc₁, hi.lt, hk₁.trans hi.k,
    by rw [hv₁, hi.k, hi.v]; rfl, (cnt_frame hf₁ (kvw_cnt hL)).trans hi.cnt, hi.fails⟩

theorem try₂_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : P₁ P L m₀ i t) :
    WP isa (.block Cfg.coreArgs) t fun u => Ctx L g m₀ u ∧ P₁ P L m₀ i u ∧ Args L u :=
  WP.mono (coreArgs_ok hL hc) fun _ ⟨hc₂, hm₂, hdi, hsi, hdx, hcx, h8⟩ =>
    ⟨hc₂, ⟨hi.lt, hm₂ ▸ hi.k, hm₂ ▸ hi.v, hm₂ ▸ hi.cnt, hi.fails⟩, hdi, hsi, hdx, hcx, h8⟩

theorem try₃_ok (hL : L.Ok) (hq : L.q = 8 * P.w) {t : State} (hc : Ctx L g m₀ t) {i : Nat}
    (hi : P₁ P L m₀ i t) (ha : Args L t) :
    WP isa (.call (cfgOf P).coreN (cfgOf P).coreC) t fun u => Ctx L g m₀ u ∧ P₃ P L m₀ i u := by
  refine WP.mono (core_ok (P := P) hL hq P.lenQ hc ha.x0 ha.x1 ha.x2 ha.x3 ha.x4) fun u₃ ⟨hc₃, hf₃, hr₃⟩ => ?_
  rw [coreSig_eq hL hq hc hi.v] at hr₃
  exact ⟨hc₃, hi.lt, (bytesAt_frame hf₃ (corew_disj hL (by anums)) (by anums)).trans hi.k,
    (bytesAt_frame hf₃ (corew_disj hL (by anums)) (by anums)).trans hi.v,
    (cnt_frame hf₃ (corew_disj hL (by anums))).trans hi.cnt, hi.fails, hr₃⟩

theorem try₄_ok (hL : L.Ok) (hq : L.q = 8 * P.w) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : P₃ P L m₀ i t) :
    WP isa (.block Cfg.goOn) t fun u => Ctx L g m₀ u ∧ Mid P L m₀ i u := by
  refine WP.mono (goOn_ok hL hc) fun u₄ ⟨hc₄, hf₄, hn₄, ha₄, hz₄⟩ => ⟨hc₄, hi.lt, ?_, ?_, ?_, hi.fails, ?_, ?_⟩
  · exact (bytesAt_frame hf₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by anums) (by anums) (by anums))
      (by anums)).trans hi.k
  · exact (bytesAt_frame hf₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by anums) (by anums) (by anums))
      (by anums)).trans hi.v
  · rw [hn₄, hi.cnt, cnt_sub hi.lt]
  · exact hi.res.keep ha₄ (bytesAt_frame hf₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hL.stk_OUT (by anums)).symm.sub_left (Region.sub_prefix (by rw [hq]; anums))) (by anums))
  · rw [hz₄, hi.cnt, cnt_sub hi.lt]
    simp only [hi.res.eax_zero, cnt_ne hi.lt]

/-- The branch: step h.3 and the next candidate, or the end. -/
theorem branch_ok (hL : L.Ok) (hq : L.q = 8 * P.w) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : Mid P L m₀ i t) :
    WP isa (.ite (.nonzero .x .x12) (.seq (cfgOf P).rekey (.block Cfg.again)) (.block Cfg.stop)) t fun t' => Ctx L g m₀ t' ∧
      ((isa.eval (.nonzero .x .x12) t' = some false ∧ Exit P L m₀ i t') ∨
        (isa.eval (.nonzero .x .x12) t' = some true ∧ LoopInv P L m₀ (i + 1) t')) := by
  by_cases hgo : sigI P L m₀ i = none ∧ i + 1 < 8
  · refine WP.ite true (by rw [hi.dec, decide_eq_true hgo]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine WP.seq (WP.mono (rekey_ok hL (by rw [hq]) hc) fun u₅ ⟨hc₅, hf₅, hk₅, hv₅⟩ => ?_)
    refine WP.mono (again_ok hL hc₅) fun u₆ ⟨hc₆, hm₆, hz₆⟩ => ⟨hc₆, .inr ⟨hz₆, ?_⟩⟩
    have hkv : kvI P L m₀ (i + 1) = step P.ok.SH.H (kvI P L m₀ i).1 (kvI P L m₀ i).2 := rfl
    refine ⟨hgo.2, ?_, ?_, ?_, fun j hj => ?_⟩
    · rw [hm₆, hk₅, hi.k, hi.v, hkv]; rfl
    · rw [hm₆, hv₅, hk₅, hi.k, hi.v, hkv]; rfl
    · rw [hm₆, cnt_frame hf₅ (kvw_cnt hL), hi.cnt]
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact hi.fails j hj
      · exact hgo.1
  · refine WP.ite false (by rw [hi.dec, decide_eq_false hgo]) (fun h => absurd h (by decide)) (fun _ => ?_)
    refine WP.mono (stop_ok hL hc) fun u₅ ⟨hc₅, hm₅, hz₅, ha₅⟩ => ⟨hc₅, .inl ⟨hz₅,
      ⟨hi.lt, hi.fails, ?_, hi.res.keep ha₅ (by rw [hm₅])⟩⟩⟩
    by_cases hs : sigI P L m₀ i = none
    · exact .inr (by have := hi.lt; have : ¬ i + 1 < 8 := fun h => hgo ⟨hs, h⟩; omega)
    · exact .inl hs

theorem tryOne_ok (hL : L.Ok) (hq : L.q = 8 * P.w) {t : State} (hc : Ctx L g m₀ t) {i : Nat}
    (hi : LoopInv P L m₀ i t) :
    WP isa (cfgOf P).tryOne t fun t' => Ctx L g m₀ t' ∧
      ((isa.eval (.nonzero .x .x12) t' = some false ∧ Exit P L m₀ i t') ∨
        (isa.eval (.nonzero .x .x12) t' = some true ∧ LoopInv P L m₀ (i + 1) t')) :=
  WP.seq (WP.mono (try₁_ok hL hc hi) fun _ ⟨h₁, p₁⟩ =>
    WP.seq (WP.mono (try₂_ok hL h₁ p₁) fun _ ⟨h₂, p₂, a₂⟩ =>
      WP.seq (WP.mono (try₃_ok hL hq h₂ p₂ a₂) fun _ ⟨h₃, p₃⟩ =>
        WP.seq (WP.mono (try₄_ok hL hq h₃ p₃) fun _ ⟨h₄, p₄⟩ => branch_ok hL hq h₄ p₄))))

end VG.Proof.Ecdsa.Rfc6979.AArch64
