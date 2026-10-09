import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Samp

/-!
# ML-DSA key generation on x86 (32-bit): after the samplers

Once the samplers are done, with `Â` and `s₁ ‖ s₂` in memory as `A` and `S`
(`Good`), the rest of the function computes the keys from them, whatever they
are (`KR`): after the copies of `ρ` and `K` (`copies_piece`), the first `np`
entries of `s₁ ‖ s₂` packed to `sk`, the first `nj` of `s₁` in the NTT domain,
and the first `nr` rows of `t` packed to `pk` and `sk`.
-/

namespace VG.Proof.MlDsa.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top
open VG.Impl.MlDsa.X86.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt polyAt coeffAt Reduced PolyIs bitPack simpleBitPack keyGenSeeds)
open VG.Proof.MlDsa.KeyGen (t1K t0K)
open VG.Spec.Sha3 (bytesAt)

/-- After the samplers: the keys from `A` and `S`, so far. -/
structure KR (p : Params) (A : Nat → Poly) (S : Nat → IPoly) (np nj nr : Nat) (s₀ s : State) : Prop where
  ctx : Ctx (YK p) s₀ s
  good : Good p s₀ (p.k * p.ℓ) (p.ℓ + p.k) A S (accV s₀ s)
  small : ∀ r < p.ℓ + p.k, Small p.η (S r)
  aS : ∀ e < p.k * p.ℓ, PolyIs s.mem (Buf.addr s₀ (aB e)) (A e)
  s2 : ∀ i < p.k, PolyIs s.mem (Buf.addr s₀ (sB p (p.ℓ + i))) (toRq (S (p.ℓ + i)))
  s1 : ∀ j < p.ℓ, PolyIs s.mem (Buf.addr s₀ (sB p j)) (if j < nj then ntt (toRq (S j)) else toRq (S j))
  pk0 : bytesAt s.mem (Buf.addr s₀ ⟨1, 0, 32⟩) 32 = rhoOf p s₀
  sk0 : bytesAt s.mem (Buf.addr s₀ ⟨2, 0, 32⟩) 32 = rhoOf p s₀
  sk1 : bytesAt s.mem (Buf.addr s₀ ⟨2, 32, 32⟩) 32 = kOf p s₀
  packs : ∀ r < np, bytesAt s.mem (Buf.addr s₀ ⟨2, 128 + lenS p * r, lenS p⟩) (lenS p) = bitPack (S r) p.η p.η
  rows : ∀ i < nr, bytesAt s.mem (Buf.addr s₀ ⟨1, 32 + 320 * i, 320⟩) 320 = simpleBitPack (t1K p A S i) 1023 ∧
    bytesAt s.mem (Buf.addr s₀ ⟨2, oT0 p + 416 * i, 416⟩) 416 = bitPack (t0K p A S i) 4095 4096

/-- The buffers of `KR` but the polynomials of `s₁` apart from `bs`. -/
structure SafeR (p : Params) (np nr : Nat) (bs : List Buf) : Prop where
  acc : (YK p).apart (sb oACC 4) bs = true
  aS : ∀ e < p.k * p.ℓ, (YK p).apart (aB e) bs = true
  s2 : ∀ i < p.k, (YK p).apart (sB p (p.ℓ + i)) bs = true
  pk0 : (YK p).apart ⟨1, 0, 32⟩ bs = true
  sk0 : (YK p).apart ⟨2, 0, 32⟩ bs = true
  sk1 : (YK p).apart ⟨2, 32, 32⟩ bs = true
  packs : ∀ r < np, (YK p).apart ⟨2, 128 + lenS p * r, lenS p⟩ bs = true
  rows : ∀ i < nr, (YK p).apart ⟨1, 32 + 320 * i, 320⟩ bs = true ∧ (YK p).apart ⟨2, oT0 p + 416 * i, 416⟩ bs = true

/-- Proves a `SafeR`, with the facts of the parameter set `hF`: each check decided for each
parameter set if it can be (`layd`). -/
macro "safeR " hF:term:max : tactic => `(tactic| (
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> (try refine ⟨?_, ?_⟩) <;> first | layd | layp $hF))

theorem apart_append {Y : Lay} {b : Buf} {bs₁ bs₂ : List Buf} (h₁ : Y.apart b bs₁ = true)
    (h₂ : Y.apart b bs₂ = true) : Y.apart b (bs₁ ++ bs₂) = true := by
  simp only [Lay.apart, List.all_append, Bool.and_eq_true] at *
  exact ⟨h₁.1, h₁.2, h₂.2⟩

/-- `SafeR` of two lists of buffers, for both. -/
theorem SafeR.append {p : Params} {np nr : Nat} {bs₁ bs₂ : List Buf} (h₁ : SafeR p np nr bs₁)
    (h₂ : SafeR p np nr bs₂) : SafeR p np nr (bs₁ ++ bs₂) :=
  ⟨apart_append h₁.acc h₂.acc, fun e he => apart_append (h₁.aS e he) (h₂.aS e he),
    fun i hi => apart_append (h₁.s2 i hi) (h₂.s2 i hi), apart_append h₁.pk0 h₂.pk0, apart_append h₁.sk0 h₂.sk0,
    apart_append h₁.sk1 h₂.sk1, fun r hr => apart_append (h₁.packs r hr) (h₂.packs r hr),
    fun i hi => ⟨apart_append (h₁.rows i hi).1 (h₂.rows i hi).1, apart_append (h₁.rows i hi).2 (h₂.rows i hi).2⟩⟩

/-! `SafeR` of one buffer, proved once for any buffer: each check is about the
buffer and one other, apart from it or in another argument. -/

theorem apart_one_same {Y : Lay} {b c : Buf} (hb : Y.ok b = true) (hc : Y.ok c = true) (ha : b.arg = c.arg)
    (h : b.off + b.len ≤ c.off ∨ c.off + c.len ≤ b.off) : Y.apart b [c] = true := by
  simp only [Lay.apart, Lay.sep, List.all_cons, List.all_nil, hb, hc, ha, ↓reduceIte, Bool.true_and,
    Bool.and_true, Bool.or_eq_true, decide_eq_true_eq]
  exact h

theorem apart_one_diff {Y : Lay} {b c : Buf} (hb : Y.ok b = true) (hc : Y.ok c = true) (ha : b.arg ≠ c.arg)
    (hw : Y.awr c.arg = true) : Y.apart b [c] = true := by
  simp only [Lay.apart, Lay.sep, List.all_cons, List.all_nil, hb, hc, ha, ↓reduceIte, hw, Bool.or_true,
    Bool.and_true]

theorem ykOk {p : Params} {a o l : Nat} (ha : a < 4) (hl : 0 < l) (h : o + l ≤ (YK p).alen a) :
    (YK p).ok ⟨a, o, l⟩ = true := by
  simp only [Lay.ok, YK_n, ha, hl, h, decide_true, Bool.and_self]

/-- Closes the arithmetic of a check of one buffer, in each case of `η` if it needs it. -/
macro "safe1 " hF:term:max : tactic => `(tactic| (
  try simp only [VG.Impl.MlDsa.X86.KeyGen.oACC, VG.Impl.MlDsa.X86.KeyGen.oP, VG.Impl.MlDsa.X86.KeyGen.oT0]
  first
    | omega_arith
    | rcases ($hF).eta with ⟨_, e⟩ | ⟨_, e⟩ <;> simp only [e] at * <;> omega_arith))

/-- A buffer of `scratch` apart from the accumulator, `Â` and `s₂`. -/
theorem SafeR.sc {p : Params} (hF : PFacts p) {np nr : Nat} (hnp : np ≤ p.ℓ + p.k) (hnr : nr ≤ p.k) {o l : Nat}
    (h0 : 0 < l) (h1 : o + l ≤ oACC ∨ oACC + 4 ≤ o)
    (h2 : o + l ≤ oP 0 ∨ (oP (p.k * p.ℓ) ≤ o ∧ o + l ≤ oP (p.k * p.ℓ + p.ℓ)) ∨ oP (p.k * p.ℓ + p.ℓ + p.k) ≤ o)
    (h3 : o + l ≤ scrLen p) : SafeR p np nr [sb o l] := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hs : scrLen p = 1024 * (p.k * p.ℓ + 4 * p.k + 3 * p.ℓ + 32) := by simp only [scrLen, hF.sw]; omega
  have hpk := hF.pk; have hsk := hF.sk
  simp only [oT0] at hsk
  simp only [oACC, oP] at h1 h2
  have hc : (YK p).ok (sb o l) = true := ykOk (by decide) h0 h3
  have same : ∀ {o' l' : Nat}, 0 < l' → o' + l' ≤ scrLen p → (o' + l' ≤ o ∨ o + l ≤ o') →
      (YK p).apart (sb o' l') [sb o l] = true :=
    fun hl' h hs => apart_one_same (ykOk (by decide) hl' h) hc rfl hs
  have d1 : ∀ {o' l' : Nat}, 0 < l' → o' + l' ≤ p.pkLen → (YK p).apart ⟨1, o', l'⟩ [sb o l] = true :=
    fun hl' h => apart_one_diff (ykOk (by decide) hl' h) hc (by dsimp only; decide) rfl
  have d2 : ∀ {o' l' : Nat}, 0 < l' → o' + l' ≤ p.skLen → (YK p).apart ⟨2, o', l'⟩ [sb o l] = true :=
    fun hl' h => apart_one_diff (ykOk (by decide) hl' h) hc (by dsimp only; decide) rfl
  refine ⟨same (by decide) ?_ ?_, fun e he => same (by decide) ?_ ?_, fun i hi => same (by decide) ?_ ?_,
    d1 (by decide) ?_, d2 (by decide) ?_, d2 (by decide) ?_, fun r hr => d2 ?_ ?_,
    fun i hi => ⟨d1 (by decide) ?_, d2 (by decide) ?_⟩⟩
  all_goals try rw [hs]
  all_goals safe1 hF

/-- A buffer of `pk` after the rows so far. -/
theorem SafeR.pk {p : Params} (hF : PFacts p) {np nr : Nat} (hnp : np ≤ p.ℓ + p.k) (hnr : nr ≤ p.k) {o l : Nat}
    (h0 : 0 < l) (h1 : 32 + 320 * nr ≤ o) (h2 : o + l ≤ p.pkLen) : SafeR p np nr [⟨1, o, l⟩] := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hs : scrLen p = 1024 * (p.k * p.ℓ + 4 * p.k + 3 * p.ℓ + 32) := by simp only [scrLen, hF.sw]; omega
  have hpk := hF.pk; have hsk := hF.sk
  simp only [oT0] at hsk
  have hc : (YK p).ok ⟨1, o, l⟩ = true := ykOk (by decide) h0 h2
  have sc : ∀ {o' l' : Nat}, 0 < l' → o' + l' ≤ scrLen p → (YK p).apart (sb o' l') [⟨1, o, l⟩] = true :=
    fun hl' h => apart_one_diff (ykOk (by decide) hl' h) hc (by dsimp only; decide) rfl
  have same : ∀ {o' l' : Nat}, 0 < l' → o' + l' ≤ p.pkLen → (o' + l' ≤ o ∨ o + l ≤ o') →
      (YK p).apart ⟨1, o', l'⟩ [⟨1, o, l⟩] = true :=
    fun hl' h hs => apart_one_same (ykOk (by decide) hl' h) hc rfl hs
  have d2 : ∀ {o' l' : Nat}, 0 < l' → o' + l' ≤ p.skLen → (YK p).apart ⟨2, o', l'⟩ [⟨1, o, l⟩] = true :=
    fun hl' h => apart_one_diff (ykOk (by decide) hl' h) hc (by dsimp only; decide) rfl
  refine ⟨sc (by decide) ?_, fun e he => sc (by decide) ?_, fun i hi => sc (by decide) ?_,
    same (by decide) ?_ ?_, d2 (by decide) ?_, d2 (by decide) ?_, fun r hr => d2 ?_ ?_,
    fun i hi => ⟨same (by decide) ?_ ?_, d2 (by decide) ?_⟩⟩
  all_goals try rw [hs]
  all_goals safe1 hF

/-- A buffer of `sk` after `ρ` and `K`, apart from the entries packed and the rows so far. -/
theorem SafeR.sk {p : Params} (hF : PFacts p) {np nr : Nat} (hnp : np ≤ p.ℓ + p.k) (hnr : nr ≤ p.k) {o l : Nat}
    (h0 : 0 < l) (h1 : 64 ≤ o) (hp : o + l ≤ 128 ∨ 128 + lenS p * np ≤ o) (hr : o + l ≤ oT0 p ∨ oT0 p + 416 * nr ≤ o)
    (h2 : o + l ≤ p.skLen) : SafeR p np nr [⟨2, o, l⟩] := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hs : scrLen p = 1024 * (p.k * p.ℓ + 4 * p.k + 3 * p.ℓ + 32) := by simp only [scrLen, hF.sw]; omega
  have hpk := hF.pk; have hsk := hF.sk
  have hc : (YK p).ok ⟨2, o, l⟩ = true := ykOk (by decide) h0 h2
  simp only [oT0] at hsk hr
  have sc : ∀ {o' l' : Nat}, 0 < l' → o' + l' ≤ scrLen p → (YK p).apart (sb o' l') [⟨2, o, l⟩] = true :=
    fun hl' h => apart_one_diff (ykOk (by decide) hl' h) hc (by dsimp only; decide) rfl
  have d1 : ∀ {o' l' : Nat}, 0 < l' → o' + l' ≤ p.pkLen → (YK p).apart ⟨1, o', l'⟩ [⟨2, o, l⟩] = true :=
    fun hl' h => apart_one_diff (ykOk (by decide) hl' h) hc (by dsimp only; decide) rfl
  have same : ∀ {o' l' : Nat}, 0 < l' → o' + l' ≤ p.skLen → (o' + l' ≤ o ∨ o + l ≤ o') →
      (YK p).apart ⟨2, o', l'⟩ [⟨2, o, l⟩] = true :=
    fun hl' h hs => apart_one_same (ykOk (by decide) hl' h) hc rfl hs
  refine ⟨sc (by decide) ?_, fun e he => sc (by decide) ?_, fun i hi => sc (by decide) ?_,
    d1 (by decide) ?_, same (by decide) ?_ ?_, same (by decide) ?_ ?_, fun r hr => same ?_ ?_ ?_,
    fun i hi => ⟨d1 (by decide) ?_, same (by decide) ?_ ?_⟩⟩
  all_goals try rw [hs]
  all_goals safe1 hF

theorem KR.keep {p : Params} {A : Nat → Poly} {S : Nat → IPoly} {np nj nr : Nat} {s₀ s s' : State}
    (h : KR p A S np nj nr s₀ s) (hp : TPre (YK p) s₀) {bs : List Buf} {N : Nat} (hN : N + 16 ≤ 96)
    (hs : SafeR p np nr bs) (hs1 : ∀ j < p.ℓ, (YK p).apart (sB p j) bs = true) (fr : Frame (FR s₀ bs N) s.mem s'.mem)
    (h' : Ctx (YK p) s₀ s') : KR p A S np nj nr s₀ s' where
  ctx := h'
  good := by rw [acc_keep hp hN hs.acc fr]; exact h.good
  small := h.small
  aS e he := keepPolyD hp hN (hs.aS e he) fr (h.aS e he)
  s2 i hi := keepPolyD hp hN (hs.s2 i hi) fr (h.s2 i hi)
  s1 j hj := keepPolyD hp hN (hs1 j hj) fr (h.s1 j hj)
  pk0 := by rw [keepBytes hp hN hs.pk0 fr]; exact h.pk0
  sk0 := by rw [keepBytes hp hN hs.sk0 fr]; exact h.sk0
  sk1 := by rw [keepBytes hp hN hs.sk1 fr]; exact h.sk1
  packs r hr := by rw [keepBytes hp hN (hs.packs r hr) fr]; exact h.packs r hr
  rows i hi := ⟨by rw [keepBytes hp hN (hs.rows i hi).1 fr]; exact (h.rows i hi).1,
    by rw [keepBytes hp hN (hs.rows i hi).2 fr]; exact (h.rows i hi).2⟩

/-- The states after the copies, and the first `np` entries packed, `nj` in the NTT domain and `nr` rows. -/
abbrev KRx (p : Params) (np nj nr : Nat) (s₀ s : State) : Prop := ∃ A S, KR p A S np nj nr s₀ s

/-! ## `ρ` and `K` to the keys -/

theorem KB.rho {p : Params} {s₀ s : State} (h : KB p s₀ s) :
    bytesAt s.mem (Buf.addr s₀ (sb oHX 32)) 32 = rhoOf p s₀ := by
  show _ = (keyGenSeeds p (xiOf s₀)).1
  rw [seeds_eq]
  show _ = (hxOf p s₀).take 32
  rw [← h.hx, Proof.MlKem.bytesAt_take _ _ (by decide)]

theorem KB.kk {p : Params} (hF : PFacts p) {s₀ s : State} (hp : TPre (YK p) s₀) (h : KB p s₀ s) :
    bytesAt s.mem (Buf.addr s₀ (sb (oHX + 96) 32)) 32 = kOf p s₀ := by
  show _ = (keyGenSeeds p (xiOf s₀)).2.2
  rw [seeds_eq]
  show _ = ((hxOf p s₀).drop 96).take 32
  rw [← h.hx, bytes_sub hp _ (k := 96) (c := 32) (L := 128) (by decide) (by layd) (by layd)]

theorem copies_piece {p : Params} (hF : PFacts p) :
    KP p (KSamp p (p.k * p.ℓ) (p.ℓ + p.k)) (KRx p 0 0 0) copies := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  unfold copies
  refine Piece.seq (B := fun s₀ s => KSamp p (p.k * p.ℓ) (p.ℓ + p.k) s₀ s ∧
      bytesAt s.mem (Buf.addr s₀ ⟨1, 0, 32⟩) 32 = rhoOf p s₀)
    (copyW_piece (Y := YK p) kS oHX 1 0 8 (by decide) (by decide) (by layd) (h₁ := .block []) (by kernel_rfl)
      (by taint_decide) (fun _ _ _ h => h.kb.ctx) fun s₀ s s' hp h h' fr cp => ⟨h.keep hp (N := 0) (by omega)
        ⟨by layd, by layd, fun _ _ => by layd, fun _ _ => by layd⟩ (fr1 fr) h', ?_⟩) ?_
  · show bytesAt s'.mem _ 32 = _
    rw [cp]; exact h.kb.rho
  refine Piece.seq (B := fun s₀ s => KSamp p (p.k * p.ℓ) (p.ℓ + p.k) s₀ s ∧
      bytesAt s.mem (Buf.addr s₀ ⟨1, 0, 32⟩) 32 = rhoOf p s₀ ∧ bytesAt s.mem (Buf.addr s₀ ⟨2, 0, 32⟩) 32 = rhoOf p s₀)
    (copyW_piece (Y := YK p) kS oHX 2 0 8 (by decide) (by decide) (by layd) (h₁ := .block []) (by kernel_rfl)
      (by taint_decide) (fun _ _ _ h => h.1.kb.ctx) fun s₀ s s' hp h h' fr cp => ⟨h.1.keep hp (N := 0) (by omega)
        ⟨by layd, by layd, fun _ _ => by layd, fun _ _ => by layd⟩ (fr1 fr) h',
        by rw [keepBytes hp (N := 0) (stkN (by omega)) (b := ⟨1, 0, 32⟩) (by layd) (fr1 fr)]; exact h.2, ?_⟩) ?_
  · show bytesAt s'.mem _ 32 = _
    rw [cp]; exact h.1.kb.rho
  refine copyW_piece (Y := YK p) kS (oHX + 96) 2 32 8 (by decide) (by decide) (by layd) (h₁ := .block [])
    (by kernel_rfl) (by taint_decide) (fun _ _ _ h => h.1.kb.ctx) fun s₀ s s' hp h h' fr cp => ?_
  obtain ⟨⟨kb, A, S, hA, hS, hG⟩, e1, e2⟩ := h
  have k : ∀ b : Buf, (YK p).apart b [⟨2, 32, 32⟩] = true →
      bytesAt s'.mem (Buf.addr s₀ b) b.len = bytesAt s.mem (Buf.addr s₀ b) b.len :=
    fun b hb => keepBytes hp (N := 0) (stkN (by omega)) hb (fr1 fr)
  refine ⟨A, S, h', ?_, fun r hr => (hS r hr).2, fun e he => keepPolyD hp (stkN (by omega)) (by layd) (fr1 fr)
    (hA e he), fun i hi => keepPolyD hp (stkN (by omega)) (by layd) (fr1 fr) (hS _ (by omega)).1,
    fun j hj => ?_, by rw [k _ (by layd)]; exact e1, by rw [k _ (by layd)]; exact e2, ?_,
    fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  · rw [acc_keep hp (N := 0) (by omega) (by layd) (fr1 fr)]; exact hG
  · rw [ifn (Nat.not_lt_zero j)]
    exact keepPolyD hp (stkN (by omega)) (by layd) (fr1 fr) (hS _ (by omega)).1
  · show bytesAt s'.mem _ 32 = _
    rw [cp]; exact kb.kk hF hp

end VG.Proof.MlDsa.X86.KeyGen
