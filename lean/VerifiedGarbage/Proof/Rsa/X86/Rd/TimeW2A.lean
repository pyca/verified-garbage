module

public import VerifiedGarbage.Proof.Rsa.X86.Rd.TimeW2Q
public import VerifiedGarbage.Proof.Rsa.X86.Rd.DivAW
import VerifiedGarbage.Proof.Rsa.X86.Rd.Loops
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Half
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Mont.X86.Rt.Step
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Impl.Rsa.X86.RecoverDetRt
meta import VerifiedGarbage.Proof.Rsa.X86.Rd.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Rsa.X86.Rd.TimeW2Q

/-! # `divA`'s timing on i686

`RecoverDetRt.divA` (`Rd/DivAW.lean` has its run): `normA` and `unnormA` loop `z` times, `z` the
leading zeros of `n`'s word `W' - 1` (`zN`), the same in both runs since `n` is; their bodies are
leaves, at `sZ`, between the stage before them and the code still to run (`Cn`). `wordDivQ` is
`relWordDivQ`; the rest are leaves.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot aM sB
open VG.Impl.Rsa.X86.RecoverRt (nar wid)
open VG.Impl.Rsa.X86.RecoverDetRt hiding aN aP aQ
open VG.Impl.Rsa.X86.Recover (aN)
open VG.Proof.Rsa.X86.Keys
open VG.Impl.Mont.X86 (sc at_)
open VG.Proof.Mont.X86.Rt (PtrAt readSrc_ptr ptr_add)
open VG.Proof.Rsa.X86.WordRt (MLen wq)
open VG.Proof.Rsa.X86.InvBatchRt.Time (view)

/-! ## The count -/

/-- `n`'s leading zeros in `W'` words: how many times `normA` doubles it. -/
def zN (n a : Nat) : Nat := 32 * wq a - 1 - Nat.log2 n

section
variable {n a : Nat}

theorem zN_lt (n0 : n ≠ 0) (hn' : n < 2 ^ (32 * wq a)) (k : Nat) :
    n * 2 ^ k < 2 ^ (32 * wq a - 1) ↔ k < zN n a := by
  have hl : Nat.log2 n < 32 * wq a := (Nat.log2_lt n0).2 hn'
  unfold zN
  constructor
  · intro h
    refine Nat.lt_of_not_le fun c => ?_
    have c' : 32 * wq a - 1 ≤ Nat.log2 n + k := by omega_using [c]
    have h1 := Nat.mul_le_mul_right (2 ^ k) (Nat.log2_self_le n0)
    rw [← Nat.pow_add] at h1
    have h2 := Nat.pow_le_pow_right (n := 2) (by decide) c'
    omega_using [h, h1, h2]
  · intro h
    have h1 := Nat.mul_lt_mul_of_pos_right (Nat.lt_log2_self (n := n)) (Nat.two_pow_pos k)
    rw [← Nat.pow_add] at h1
    have h2 := Nat.pow_le_pow_right (n := 2) (by decide) (show Nat.log2 n + 1 + k ≤ 32 * wq a - 1 by omega_using [h])
    omega_using [h1, h2]

theorem zN_le (hw1 : 1 ≤ wq a) (hn0 : 2 ^ (32 * (wq a - 1)) ≤ n) : zN n a ≤ 31 := by
  have n0 : n ≠ 0 := by have := Nat.two_pow_pos (32 * (wq a - 1)); omega
  have := (Nat.le_log2 n0).2 hn0
  unfold zN; omega

theorem zN_top (n0 : n ≠ 0) (hn' : n < 2 ^ (32 * wq a)) : 2 ^ (32 * wq a - 1) ≤ n * 2 ^ zN n a :=
  Nat.le_of_not_lt fun h => Nat.lt_irrefl _ ((zN_lt n0 hn' _).1 h)

theorem zN_lt' (n0 : n ≠ 0) (hn' : n < 2 ^ (32 * wq a)) : n * 2 ^ zN n a < 2 ^ (32 * wq a) := by
  have hl : Nat.log2 n < 32 * wq a := (Nat.log2_lt n0).2 hn'
  have h1 := Nat.mul_lt_mul_of_pos_right (Nat.lt_log2_self (n := n)) (Nat.two_pow_pos (zN n a))
  rw [← Nat.pow_add, show Nat.log2 n + 1 + zN n a = 32 * wq a by unfold zN; omega_using [hl]] at h1
  exact h1

end

/-! ## `divA`'s stages -/

/-- A state of `divA`: zero and `n` (narrow), the wide arrays `liveW` and the header words `ls`, the
public ones as `H` says. -/
def KA (g : Geo) (n a : Nat) (liveW ls : List Nat) (H : (Nat → Nat) → (Nat → Nat) → Prop) (s : State) : Prop :=
  GA g a ∧ ∃ s0 A AW V, KS g s0 A [aZero, aN] AW liveW V ls s ∧ H AW V ∧ A aZero = 0 ∧ A aN = n

/-- `normA`'s state after `k` doublings. -/
def NK (g : Geo) (n a k : Nat) (s : State) : Prop :=
  GA g a ∧ ∃ s0 A ok x, NS g s0 A ok n x k s ∧ A aZero = 0 ∧ A aN = n ∧ x < 2 ^ (32 * g.W)

section
variable {g : Geo} {s : State} {n a : Nat} {liveW ls : List Nat} {H : (Nat → Nat) → (Nat → Nat) → Prop}

theorem KA.onView (h : KA g n a liveW ls H s) : KA g.vw n a liveW ls H (view s g.B g.Z) :=
  let ⟨ga, _, _, _, _, k, r⟩ := h
  ⟨ga, _, _, _, _, k.onView, r⟩

theorem KA.p0 (pg : PubG g) (h : KA g n a liveW ls H s) : P0 g s :=
  let ⟨_, _, _, _, _, k, _⟩ := h
  k.pre0 pg

theorem KA.slot {d v : Nat} (h : KA g n a liveW ls H s) (hd : d ∈ ls) (hv : ∀ AW V, H AW V → V d = v) :
    w32 s.mem g.B d = v :=
  let ⟨_, _, _, _, _, k, hH, _⟩ := h
  (k.sl d hd).trans (hv _ _ hH)

theorem NS.onView {s0 : State} {A : Nat → Nat} {ok x z : Nat} (h : NS g s0 A ok n x z s) :
    NS g.vw (view s0 g.B g.Z) A ok n x z (view s g.B g.Z) :=
  let ⟨_, _, k, r⟩ := h
  ⟨_, _, k.onView, r⟩

theorem NK.onView {k : Nat} (h : NK g n a k s) : NK g.vw n a k (view s g.B g.Z) :=
  let ⟨ga, _, _, _, _, P, r⟩ := h
  ⟨ga, _, _, _, _, P.onView, r⟩

theorem NK.p0 (pg : PubG g) {k : Nat} (h : NK g n a k s) : P0 g s :=
  let ⟨_, _, _, _, _, ⟨_, _, h, _⟩, _⟩ := h
  h.pre0 pg

end

/-! ## `normA` -/

/-- `divA` after `wideN`: `n` wide, the dividend's extra word zero. -/
def NA1 (g : Geo) (n a : Nat) (s : State) : Prop :=
  KA g n a [wN, wA] [sOkDE] (fun AW _ => AW wN = n) s ∧ w32 s.mem g.B (arr g.W wA + 4 * g.W) = 0

/-- `normA`'s first block: `sZ := 0`, `n`'s top bit tested. -/
abbrev nBlk0 : Prog isa := .block ([.mov .eax (.imm 0), .store (sc sZ) .eax] ++ topBit)

/-- `normA`'s doubling. -/
abbrev nBody : Prog isa := seqs [VG.Impl.Rsa.X86.KeyRt.chain wid .adc wN wN wN false,
  VG.Impl.Rsa.X86.KeyRt.chain wid .adc wA wA wA true,
  .block (([.mov .eax (.mem (sc sZ)), .alu .add .eax (.imm 1), .store (sc sZ) .eax] : List Instr) ++ topBit)]

/-- `normA`'s loop after `k` doublings, and whether another follows. -/
def NL (g : Geo) (n a k : Nat) (s : State) : Prop :=
  NK g n a k s ∧ (0 < k → isa.eval .e s = some (decide (k < zN n a)))

section
variable {g : Geo} {t : State} {n a : Nat}

theorem nBlk0_ok (h : NA1 g n a t) (ha1 : a ≤ 1024) (hw1 : 1 ≤ wq a) (hn' : n < 2 ^ (32 * wq a)) :
    WP isa nBlk0 t fun u => NK g n a 0 u ∧ u.zf = some (decide (n < 2 ^ (32 * wq a - 1))) := by
  obtain ⟨⟨⟨ha, hw⟩, s0, A, AW, V, h, hN, hz, hnA⟩, hxt⟩ := h
  have fA := h.wsW.fit64 (j := wA) (by decide)
  have hx : AW wA < 2 ^ (32 * g.W) := by rw [← h.arrsW wA (by simp)]; exact val32_lt _ _ _ _
  refine wp_movS (v := 0) rfl fun u₁ U₁ _ => ?_
  have h₁ := h.of_rest U₁.keeps (by decide) U₁.mem
  refine storeHdr h₁.ws (d := sZ) (by decide) .eax fun u₂ K₂ e₂ k₂ _ _ => ?_
  have h₂ := h₁.slot1 K₂ (by decide) (k₂.mono (by decide)) e₂
  rw [show topBit = topBit ++ [] from (List.append_nil _).symm]
  refine KS.topBit_ok h₂ (h₂.mlen ha ha1) (by simp) hw1 hw fun u₃ h₃ m₃ zf₃ => WP.block_nil ?_
  have X₃ : val32 u₃.mem g.B (arr g.W wA) (g.W + 1) = AW wA := by
    rw [m₃, val32_succ]
    have k₂W := K₂.toW
    rw [U₁.mem] at k₂W
    have e := k₂W.word (j := wA) (i := g.W) (by show 4 * g.W + 4 ≤ 4 * (g.W + 2); omega_using []) (by simp) (by decide) fA
    change w32 u₂.mem g.B (arr g.W wA + 4 * g.W) = w32 t.mem g.B (arr g.W wA + 4 * g.W) at e
    rw [e, hxt]
    change val32 u₂.mem g.B (arr g.W wA) g.W + 0 = AW wA
    rw [Nat.add_zero, ← h₂.arrsW wA (by simp)]
  simp only [hN, top_lt_iff hn' hw1] at zf₃
  exact ⟨⟨⟨ha, hw⟩, s0, A, V sOkDE, AW wA, ⟨_, _, h₃, by rw [upd_self, U₁.gpr]; rfl,
    by rw [upd_ne _ _ (by decide)], by rw [hN, Nat.pow_zero, Nat.mul_one],
    by rw [Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hx], by rw [X₃, Nat.pow_zero, Nat.mul_one]⟩, hz, hnA, hx⟩,
    zf₃⟩

theorem nBody_ok {k : Nat} (h : NK g n a k t) (ha1 : a ≤ 1024) (hw1 : 1 ≤ wq a)
    (hn0 : 2 ^ (32 * (wq a - 1)) ≤ n) (hn' : n < 2 ^ (32 * wq a)) (hk : k < zN n a) :
    WP isa nBody t (NL g n a (k + 1)) := by
  obtain ⟨⟨ha, hw⟩, s0, A, ok, x, P, hz, hnA, hx⟩ := h
  have n0 : n ≠ 0 := by have := Nat.two_pow_pos (32 * (wq a - 1)); omega
  have z31 := zN_le hw1 hn0
  have hn2 : n * 2 ^ (k + 1) < 2 ^ (32 * wq a) :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hk)) (zN_lt' n0 hn')
  refine WP.mono (normStep_ok P ha ha1 hw1 hw hx (by omega_using [hk, z31]) hn2) fun u ⟨P', zf⟩ => ?_
  refine ⟨⟨⟨ha, hw⟩, s0, A, ok, x, P', hz, hnA, hx⟩, fun _ => ?_⟩
  show u.zf = _
  rw [zf, decide_eq_decide.mpr (zN_lt n0 hn' (k + 1))]

end

theorem c_nBlk0 : OkK [] nBlk0 := ⟨_, by taint_decide⟩
theorem c_chN : OkK [sZ] (VG.Impl.Rsa.X86.KeyRt.chain wid .adc wN wN wN false) := ⟨_, by taint_decide⟩
theorem c_chA : OkK [sZ] (VG.Impl.Rsa.X86.KeyRt.chain wid .adc wA wA wA true) := ⟨_, by taint_decide⟩
theorem c_nZ : OkK [sZ] (.block (([.mov .eax (.mem (sc sZ)), .alu .add .eax (.imm 1), .store (sc sZ) .eax] :
    List Instr) ++ topBit)) := ⟨_, by taint_decide⟩

/-- A chain's frame: the leaf's start kept, `sZ` too. -/
theorem chain_frame {g : Geo} {s : State} {o x y v : Nat} {extra : Bool} (h : P0 g s)
    (ho : o < 22) (hx : x < 22) (hy : y < 22) (hv : w32 s.mem g.B sZ = v) :
    WP isa (VG.Impl.Rsa.X86.KeyRt.chain wid .adc o x y extra) s fun w =>
      P0 g w ∧ ∀ d ∈ [sZ], w32 w.mem g.B d = (fun _ => v) d := by
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.chainAdd_ok h.1 ho hx hy extra) fun w ⟨_, k, _, K⟩ => ?_
  refine ⟨h.keepK k (by simpa using ho) (by simp) K (by decide) (by decide), fun d hd => ?_⟩
  simp only [List.mem_singleton] at hd; subst hd
  have e : slot w.mem g.B sZ = slot s.mem g.B sZ := k.slot (e := sZ) (by decide) (by simp)
  exact e.trans hv

/-- `normA`, related: `n` and the dividend doubled `zN n a` times. -/
theorem normA_rel {g : Geo} (pg : PubG g) {n a : Nat} (ha1 : a ≤ 1024) (hw1 : 1 ≤ wq a)
    (hn0 : 2 ^ (32 * (wq a - 1)) ≤ n) (hn' : n < 2 ^ (32 * wq a)) :
    RelCT isa (Both (NA1 g n a)) normA (Both (NK g n a (zN n a))) := by
  have n0 : n ≠ 0 := by have := Nat.two_pow_pos (32 * (wq a - 1)); omega
  unfold normA
  simp only [seqs]
  refine VG.RelCT.seq (R := Both fun u => NK g n a 0 u ∧ u.zf = some (decide (n < 2 ^ (32 * wq a - 1))))
    (leafP (P := fun g' => NA1 g' n a) (Q := fun g' u => NK g' n a 0 u ∧ u.zf = some (decide (n < 2 ^ (32 * wq a - 1))))
      (fun _ => 0) (by simp) (fun _ h => h.1.p0 pg) (fun _ h => ⟨h.1.onView, h.2⟩) (by simp)
      (fun _ _ h => nBlk0_ok h ha1 hw1 hn') c_nBlk0)
    (VG.RelCT.ite (fun s t ⟨hs, ht⟩ => by show s.zf.map _ = t.zf.map _; rw [hs.2, ht.2]) ?_ ?_)
  · refine VG.RelCT.block_nil fun s t ⟨⟨hs, ht⟩, e⟩ => ?_
    have : zN n a = 0 := by
      have e' : isa.eval .ne s = s.zf.map (!·) := rfl
      rw [e', hs.2] at e
      simp only [Option.map_some, Option.some.injEq, Bool.not_eq_true', decide_eq_false_iff_not] at e
      have := (zN_lt n0 hn' 0).not.mp (by simpa using e)
      omega_using [this]
    rw [this]
    exact ⟨hs.1, ht.1⟩
  · by_cases pos : 0 < zN n a
    · have cn : ∀ k, k < zN n a → ∀ s, NL g n a k s →
          Cn g [sZ] (fun _ => k) nBody (NL g n a (k + 1)) s := fun k hk s h => by
        refine ⟨h.1.p0 pg, fun d hd => ?_, nBody_ok h.1 ha1 hw1 hn0 hn' hk,
          run_of (nBody_ok h.1.onView ha1 hw1 hn0 hn' hk)⟩
        simp only [List.mem_singleton] at hd; subst hd
        obtain ⟨_, _, _, _, _, ⟨_, _, hK, hzV, _⟩, _⟩ := h.1
        exact (hK.sl sZ (by simp)).trans hzV
      refine (relLoopB (NL g n a) (K := zN n a) pos (fun k hk => ?_) (fun k s hk _ h => h.2 hk)).mono
        (fun s t ⟨⟨hs, ht⟩, _⟩ => ⟨⟨hs.1, fun h => absurd h (Nat.lt_irrefl 0)⟩,
          ⟨ht.1, fun h => absurd h (Nat.lt_irrefl 0)⟩⟩) (fun s t ⟨hs, ht⟩ => ⟨hs.1, ht.1⟩)
      refine VG.RelCT.mono (P := Both (Cn g [sZ] (fun _ => k) nBody (NL g n a (k + 1)))) ?_
        (fun s t ⟨hs, ht⟩ => ⟨cn k hk s hs, cn k hk t ht⟩) (fun _ _ h => h)
      exact VG.RelCT.seq
        (contSeq (by decide) (fun s h => chain_frame h.1 (by decide) (by decide) (by decide) (h.2.1 sZ (by simp)))
          c_chN)
        (VG.RelCT.seq
          (contSeq (by decide) (fun s h => chain_frame h.1 (by decide) (by decide) (by decide) (h.2.1 sZ (by simp)))
            c_chA)
          (contLast (by decide) c_nZ))
    · intro s _ _ _ _ _ ⟨⟨hs, _⟩, e⟩ _ _
      have e' : isa.eval .ne s = s.zf.map (!·) := rfl
      rw [e', hs.2] at e
      simp only [Option.map_some, Option.some.injEq, Bool.not_eq_false', decide_eq_true_eq] at e
      exact absurd ((zN_lt n0 hn' 0).1 (by simpa using e)) pos

/-! ## `wideN`, the division and `clearQTop` -/

/-- After the division: `sZ = zN`. -/
abbrev DA3 (g : Geo) (n a : Nat) : State → Prop := KA g n a [wA, wR] [sZ, sOkDE] fun _ V => V sZ = zN n a

/-- After `clearQTop`. -/
abbrev DA4 (g : Geo) (n a : Nat) : State → Prop := KA g n a [wA, wA, wR] [sZ, sOkDE] fun _ V => V sZ = zN n a

/-- After `unnormA`. -/
abbrev DA5 (g : Geo) (n a : Nat) : State → Prop := KA g n a [wA, wR] [sZ, sOkDE] fun _ _ => True

section
variable {g : Geo} {s : State} {n a : Nat}

theorem wideNA_ok (h : GA g a ∧ PA1 g n s) : WP isa wideN s (NA1 g n a) := by
  obtain ⟨ga, s0, A, AW, V, h, hz, hn, hxt⟩ := h
  refine WP.mono (h.wideN_ok (by simp [VG.Impl.Rsa.X86.RecoverDetRt.aN]) (by decide) (by decide))
    fun t ⟨h₁, _, ex₁⟩ => ?_
  exact ⟨⟨ga, s0, A, _, V, h₁, by show upd (upd AW wN 0) wN (A aN) wN = n; rw [upd_self]; exact hn, hz, hn⟩,
    ex₁.trans hxt⟩

theorem wdqA_ok (h : NK g n a (zN n a) s) (ha1 : a ≤ 1024) (h4 : 4 ≤ wq a) (hwW : wq a ≤ g.W) :
    WP isa (wordDivQ nl wA wR wN wDt true) s (DA3 g n a) := by
  obtain ⟨⟨ha, hw⟩, s0, A, ok, x, ⟨AW₂, V₂, h₂, hz₂, _⟩, hzA, hnA, _⟩ := h
  have kwW : VG.Proof.Rsa.X86.KeyRt.kw (16 * g.n + 24) = g.W := kw_wid _
  refine WP.mono (wordDivQ_ok h₂.rtW (h₂.mlen ha ha1) (x := wA) (r := wR) (m := wN) (t := wDt)
    (extra := true) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) h4 (by rw [kwW]; exact hwW))
    fun t₃ ⟨_, k₃, _, _, _, _, _, K₃⟩ => ?_
  rw [kwW] at k₃
  have h₂m := h₂.mono (AW' := AW₂) (liveW' := []) (fun j hj => ⟨hj, rfl⟩) (fun j hj => by simp at hj)
    (fun d hd => ⟨hd, rfl⟩)
  have h₃ : KS g s0 A [aZero, aN] (upd (upd AW₂ wA (num t₃.mem g.B g.W wA)) wR (num t₃.mem g.B g.W wR))
      [wA, wR] V₂ [sZ, sOkDE] t₃ :=
    h₂m.core k₃ (fun j hj => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl <;> exact h₂m.wsW.arr_fit (by decide)) (by decide)
      (K₃.mono (by decide)) (h₂m.arrs_W k₃ (by decide) (by decide)) (by decide)
      (fun j hj => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl
        · rw [upd_ne _ _ (by decide), upd_self]
        · rw [upd_self])
      (by decide) (h₂m.sl_keep k₃ (by decide)) h₂m.ls_ok
  exact ⟨⟨ha, hw⟩, s0, A, _, V₂, h₃, hz₂, hzA, hnA⟩

theorem cqtA_ok (h : DA3 g n a s) (ha1 : a ≤ 1024) (hw2 : 2 ≤ wq a) : WP isa clearQTop s (DA4 g n a) := by
  obtain ⟨⟨ha, hw⟩, s0, A, AW, V, h, hz, hzA, hnA⟩ := h
  exact WP.mono (h.clearQTop_ok (h.mlen ha ha1) (by decide) hw2 hw) fun t ht =>
    ⟨⟨ha, hw⟩, s0, A, _, V, ht, hz, hzA, hnA⟩

end

theorem c_wideN : OkK [] wideN := ⟨_, by taint_decide⟩
theorem c_cqt : OkK [] clearQTop := ⟨_, by taint_decide⟩
theorem c_wdqPreA : OkK [] (seqs (wdqPre nl wA wR wN true)) := ⟨_, by taint_decide⟩
theorem c_dqAA : OkK [VG.Impl.Rsa.X86.WordModRt.oSteps] (seqs (dqA nl wA wR wN wDt)) := ⟨_, by taint_decide⟩
theorem c_dq3A : OkK [VG.Impl.Rsa.X86.WordModRt.oSteps] (dq3 wA) := ⟨_, by taint_decide⟩
theorem c_dq4A : OkK [VG.Impl.Rsa.X86.WordModRt.oSteps] dq4 := ⟨_, by taint_decide⟩

/-! ## `unnormA` -/

/-- `unnormA`'s test of `sZ`. -/
abbrev uBlk0 : Prog isa := .block [.mov .eax (.mem (sc sZ)), .alu .test .eax (.reg .eax)]

/-- `unnormA`'s halving, before its count down. -/
abbrev uHalf : List (Prog isa) := [.block [.mov .ebx (.imm 0)], VG.Impl.Rsa.X86.KeyRt.half wid wR]

/-- `unnormA`'s count down. -/
abbrev uDown : Prog isa := .block [.mov .eax (.mem (sc sZ)), .alu .sub .eax (.imm 1), .store (sc sZ) .eax]

/-- `unnormA`'s loop after `i` halvings, and whether another follows. -/
def UL (g : Geo) (n a i : Nat) (s : State) : Prop :=
  KA g n a [wA, wA, wR] [sZ, sOkDE] (fun _ V => V sZ = zN n a - i) s ∧
    (0 < i → isa.eval .ne s = some (decide (i < zN n a)))

section
variable {g : Geo} {s : State} {n a : Nat}

theorem uBlk0_ok (h : DA4 g n a s) (z32 : zN n a < 2 ^ 32) :
    WP isa uBlk0 s fun u => DA4 g n a u ∧ u.zf = some (decide (zN n a = 0)) := by
  obtain ⟨ga, s0, A, AW, V, h, hz, hzA, hnA⟩ := h
  refine wp_movS (h.readSlot (d := sZ) (by simp)) fun u₁ U₁ _ => VG.X86.Wp.wp_test fun u₂ F₂ z₂ => WP.block_nil ?_
  have h₂ := h.of_rest (rs := opRegs) ((U₁.keeps.mono (by decide)).trans ⟨fun r _ => by rw [F₂.gpr], F₂.rd, F₂.wr⟩)
    (fun x hx => hx) (by rw [F₂.mem, U₁.mem])
  rw [U₁.gpr, BitVec.and_self, hz, ofNat_beq_zero z32] at z₂
  exact ⟨⟨ga, s0, A, AW, V, h₂, hz, hzA, hnA⟩, z₂⟩

theorem uBody_ok {i : Nat} (h : KA g n a [wA, wA, wR] [sZ, sOkDE] (fun _ V => V sZ = zN n a - i) s)
    (hi : i < zN n a) (z32 : zN n a < 2 ^ 32) :
    WP isa (seqs (uHalf ++ [uDown])) s (UL g n a (i + 1)) := by
  obtain ⟨ga, s0, A, AW, V, P, hS, hzA, hnA⟩ := h
  simp only [seqs, List.cons_append, List.nil_append]
  refine WP.seq (wp_movS rfl fun u₁ U₁' _ => WP.block_nil ?_)
  have P₁ := P.of_rest U₁'.keeps (by decide) U₁'.mem
  refine WP.seq (WP.mono (P₁.half_W (j := wR) (by simp) (by rw [U₁'.gpr]; rfl) (by decide)) fun u₂ ⟨P₂, _⟩ => ?_)
  refine wp_movS (P₂.readSlot (d := sZ) (by simp)) fun u₃ U₃ _ =>
    VG.Proof.Mont.X86.Rt.wp_subZ (v := 1) rfl fun u₄ U₄ z₄ => ?_
  have P₄ := P₂.of_rest (rs := opRegs) ((U₃.keeps.mono (by decide)).trans (U₄.keeps.mono (by decide)))
    (fun x hx => hx) (by rw [U₄.mem, U₃.mem])
  refine WP.mono (P₄.storeSlot (d := sZ) (by decide) .eax) fun t ⟨P₅, zf₅, _⟩ => ?_
  have ev : (u₄.gpr .eax).toNat = zN n a - (i + 1) := by
    rw [U₄.gpr, U₃.gpr, hS, BitVec.toNat_sub, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show zN n a - i < 2 ^ 32 by omega_using [z32]), show (1 : BitVec 32).toNat = 1 from rfl]
    omega_using [hi, z32]
  have zz : (u₃.gpr .eax - 1 == 0) = decide (i + 1 = zN n a) := by
    rw [U₃.gpr, hS]
    by_cases e : i + 1 = zN n a
    · simp only [e, decide_true, beq_iff_eq]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show zN n a - i < 2 ^ 32 by omega_using [z32])]; simp; omega_using [e]
    · simp only [e, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro c; have := congrArg BitVec.toNat c
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show zN n a - i < 2 ^ 32 by omega_using [z32])] at this
      simp at this; omega_using [z32, e, this]
  rw [zz] at z₄
  refine ⟨⟨ga, s0, A, _, _, P₅.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨List.mem_cons_of_mem _ hj, rfl⟩)
    (fun d hd => ⟨List.mem_cons_of_mem _ hd, rfl⟩),
    by show upd V sZ (u₄.gpr .eax).toNat sZ = _; rw [upd_self, ev], hzA, hnA⟩, fun _ => ?_⟩
  show t.zf.map (!·) = _
  rw [zf₅, z₄]
  by_cases e : i + 1 = zN n a
  · simp [e]
  · simp only [e, decide_false, Option.map_some, Bool.not_false]
    exact congrArg some (decide_eq_true (by omega_using [hi, e])).symm

end

theorem c_uBlk0 : OkK [sZ] uBlk0 := ⟨_, by taint_decide⟩
theorem c_uHalf : OkK [sZ] (seqs uHalf) := ⟨_, by taint_decide⟩
theorem c_uDown : OkK [sZ] uDown := ⟨_, by taint_decide⟩

/-- The halving's frame: the leaf's start kept, `sZ` too. -/
theorem uHalf_frame {g : Geo} {s : State} {v : Nat} (h : P0 g s) (hv : w32 s.mem g.B sZ = v) :
    WP isa (seqs uHalf) s fun w => P0 g w ∧ ∀ d ∈ [sZ], w32 w.mem g.B d = (fun _ => v) d := by
  simp only [seqs]
  refine WP.seq (wp_movS rfl fun u₁ U₁ _ => WP.block_nil ?_)
  have p₁ : P0 g u₁ := h.keep U₁.keeps (by decide) (by decide) (by rw [U₁.mem]; exact Outside.refl _ _ _ _)
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.half_ok p₁.1 (j := wR) (by decide) (by rw [U₁.gpr]; decide))
    fun w ⟨_, k, _, K⟩ => ⟨p₁.keepK k (by simp; decide) (by simp) K (by decide) (by decide), fun d hd => ?_⟩
  simp only [List.mem_singleton] at hd; subst hd
  have e : slot w.mem g.B sZ = slot u₁.mem g.B sZ := k.slot (e := sZ) (by decide) (by simp)
  rw [U₁.mem] at e
  exact e.trans hv

/-- `unnormA`, related: the remainder halved `zN n a` times. -/
theorem unnormA_rel {g : Geo} (pg : PubG g) {n a : Nat} (z32 : zN n a < 2 ^ 32) :
    RelCT isa (Both (DA4 g n a)) unnormA (Both (DA5 g n a)) := by
  unfold unnormA
  simp only [seqs]
  refine VG.RelCT.seq (R := Both fun u => DA4 g n a u ∧ u.zf = some (decide (zN n a = 0)))
    (leafP (P := fun g' => DA4 g' n a) (Q := fun g' u => DA4 g' n a u ∧ u.zf = some (decide (zN n a = 0)))
      (fun _ => zN n a) (by decide) (fun _ h => h.p0 pg) (fun _ h => h.onView)
      (fun _ h d hd => by simp only [List.mem_singleton] at hd; subst hd; exact h.slot (by simp) fun _ _ h => h)
      (fun _ _ h => uBlk0_ok h z32) c_uBlk0)
    (VG.RelCT.ite (fun s t ⟨hs, ht⟩ => by show s.zf = t.zf; rw [hs.2, ht.2]) ?_ ?_)
  · refine VG.RelCT.block_nil fun s t ⟨⟨hs, ht⟩, e⟩ => ?_
    have e' : isa.eval .e s = s.zf := rfl
    rw [e', hs.2] at e
    simp only [Option.some.injEq, decide_eq_true_eq] at e
    have mk : ∀ u, DA4 g n a u → DA5 g n a u := fun u ⟨ga, s0, A, AW, V, h, _, hzA, hnA⟩ =>
      ⟨ga, s0, A, AW, V, h.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨by simp at hj ⊢; omega_using [hj], rfl⟩)
        (fun d hd => ⟨hd, rfl⟩), trivial, hzA, hnA⟩
    exact ⟨mk s hs.1, mk t ht.1⟩
  · by_cases pos : 0 < zN n a
    · have cn : ∀ i, i < zN n a → ∀ s, UL g n a i s →
          Cn g [sZ] (fun _ => zN n a - i) (seqs (uHalf ++ [uDown])) (UL g n a (i + 1)) s := fun i hi s h => by
        refine ⟨h.1.p0 pg, fun d hd => ?_, uBody_ok h.1 hi z32, run_of (uBody_ok h.1.onView hi z32)⟩
        simp only [List.mem_singleton] at hd; subst hd
        exact h.1.slot (by simp) fun _ _ h => h
      refine (relLoopB (UL g n a) (K := zN n a) pos (fun i hi => ?_) (fun i s hi _ h => h.2 hi)).mono
        (fun s t ⟨⟨hs, ht⟩, _⟩ => ⟨⟨by rw [Nat.sub_zero]; exact hs.1, fun h => absurd h (Nat.lt_irrefl 0)⟩,
          ⟨by rw [Nat.sub_zero]; exact ht.1, fun h => absurd h (Nat.lt_irrefl 0)⟩⟩)
        (fun s t ⟨hs, ht⟩ => ?_)
      · refine VG.RelCT.mono (P := Both (Cn g [sZ] (fun _ => zN n a - i) (seqs (uHalf ++ [uDown]))
          (UL g n a (i + 1)))) ?_ (fun s t ⟨hs, ht⟩ => ⟨cn i hi s hs, cn i hi t ht⟩) (fun _ _ h => h)
        exact relSeqs (contApp (by decide) (fun s h => uHalf_frame h.1 (h.2.1 sZ (by simp))) c_uHalf)
          (contLast (c := seqs [uDown]) (by decide) c_uDown)
      · have mk : ∀ u, UL g n a (zN n a) u → DA5 g n a u := fun u ⟨⟨ga, s0, A, AW, V, h, _, hzA, hnA⟩, _⟩ =>
          ⟨ga, s0, A, AW, V, h.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨by simp at hj ⊢; omega_using [hj], rfl⟩)
            (fun d hd => ⟨hd, rfl⟩), trivial, hzA, hnA⟩
        exact ⟨mk s hs, mk t ht⟩
    · intro s _ _ _ _ _ ⟨⟨hs, _⟩, e⟩ _ _
      have e' : isa.eval .e s = s.zf := rfl
      rw [e', hs.2] at e
      simp only [Option.some.injEq, decide_eq_false_iff_not] at e
      exact absurd (Nat.pos_of_ne_zero e) pos

/-! ## `divA` -/

/-- `divA`'s end: `n` wide again, and whether `m < n`. -/
abbrev divATail : List (Prog isa) := [wideN, VG.Impl.Rsa.X86.KeyRt.sub3 wid wT wA wN, .block [.store (sc sLt) .ebx]]

theorem tailA_ok {g : Geo} {s : State} {n a : Nat} (h : DA5 g n a s) : WP isa (seqs divATail) s (DA1 g n) := by
  obtain ⟨_, s0, A, AW, V, h₅, _, hzA, hnA⟩ := h
  simp only [seqs]
  refine WP.seq (WP.mono (h₅.wideN_ok (by simp) (by decide) (by decide)) fun t₆ ⟨h₆, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h₆.subWrap_W (o := wT) (a := wA) (b := wN) (by decide) (by simp) (by simp)
    (by decide) (by decide) (by decide)) fun t₇ ⟨h₇, _⟩ => ?_)
  refine WP.mono (h₇.storeSlot (d := sLt) (by decide) .ebx) fun t ⟨h₈, _, _⟩ => ?_
  refine ⟨s0, A, _, _, h₈.mono (fun j hj => ⟨by simpa [VG.Impl.Rsa.X86.RecoverDetRt.aN] using hj, rfl⟩)
    (fun j hj => ⟨by simp at hj ⊢; omega_using [hj], rfl⟩) (fun d hd => ⟨by simp at hd ⊢; omega_using [hd], rfl⟩), hzA, hnA, ?_⟩
  rw [upd_ne _ _ (show wN ≠ wT by decide), upd_self]
  exact hnA

theorem c_tailA : OkK [] (seqs divATail) := ⟨_, by taint_decide⟩

theorem divA_eq : divA = .seq wideN (.seq normA (.seq (wordDivQ nl wA wR wN wDt true) (.seq clearQTop
    (.seq unnormA (seqs divATail))))) := rfl

/-- `divA`, related, from its start to its end. -/
theorem divA_both {g : Geo} (pg : PubG g) {n a : Nat} (ha0 : 64 ≤ a) (ha1 : a ≤ 1024) (haw : wq a ≤ g.w)
    (hn0 : 2 ^ (32 * (wq a - 1)) ≤ n) (hn' : n < 2 ^ (32 * wq a)) :
    RelCT isa (Both fun s => GA g a ∧ PA1 g n s) divA (Both (DA1 g n)) := by
  have h16 : 16 ≤ wq a := by simp only [wq]; omega_using [ha0]
  have hwW : wq a ≤ g.W := by simp only [Geo.W, VG.Impl.Rsa.X86.Recover.wide]; simp only [Geo.w] at haw; omega_using [haw]
  have z32 : zN n a < 2 ^ 32 := by have := zN_le (by omega_using [h16]) hn0; omega_using [this]
  rw [divA_eq]
  refine VG.RelCT.seq (leafP (P := fun g' s => GA g' a ∧ PA1 g' n s) (Q := fun g' => NA1 g' n a) (fun _ => 0)
    (by simp) (fun s h => let ⟨_, _, _, _, k, _⟩ := h.2; k.pre0 pg)
    (fun s h => let ⟨ga, _, _, _, _, k, r⟩ := h; ⟨ga, _, _, _, _, k.onView, r⟩) (by simp)
    (fun _ _ h => wideNA_ok h) c_wideN)
    (VG.RelCT.seq (normA_rel pg ha1 (by omega_using [h16]) hn0 hn') (VG.RelCT.seq ?_ (VG.RelCT.seq
      (leafP (P := fun g' => DA3 g' n a) (Q := fun g' => DA4 g' n a) (fun _ => 0) (by simp)
        (fun _ h => h.p0 pg) (fun _ h => h.onView) (by simp) (fun _ _ h => cqtA_ok h ha1 (by omega_using [h16])) c_cqt)
      (VG.RelCT.seq (unnormA_rel pg z32)
        (leafP (P := fun g' => DA5 g' n a) (Q := fun g' => DA1 g' n) (fun _ => 0) (by simp)
          (fun _ h => h.p0 pg) (fun _ h => h.onView) (by simp) (fun _ _ h => tailA_ok h) c_tailA)))))
  exact relWordDivQ (a := a) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by omega_using [h16]) (by rw [kw_wid]; exact hwW) (fun _ h => h.p0 pg)
    (fun s h => let ⟨⟨ha, _⟩, _, _, _, _, ⟨_, _, k, _⟩, _⟩ := h; k.mlen ha ha1)
    (fun s h => wdqA_ok h ha1 (by omega_using [h16]) hwW) (fun s h => run_of (wdqA_ok h.onView ha1 (by omega_using [h16]) hwW))
    c_wdqPreA c_dqAA c_dq3A c_dq4A

/-- `divA`'s timing (`PLAN.md`, P7c). -/
theorem divA_relCT {g : Geo} (pg : PubG g) (n a : Nat)
    (ha : g.args VG.Impl.Rsa.X86.RecoverDetRt.nl = BitVec.ofNat 32 a) (ha0 : 64 ≤ a) (ha1 : a ≤ 1024)
    (haw : VG.Proof.Rsa.X86.WordRt.wq a ≤ g.w)
    (hn0 : 2 ^ (32 * (VG.Proof.Rsa.X86.WordRt.wq a - 1)) ≤ n)
    (hn' : n < 2 ^ (32 * VG.Proof.Rsa.X86.WordRt.wq a)) :
    RelCT isa (RA (PA1 g n) (PA1 g n)) VG.Impl.Rsa.X86.RecoverDetRt.divA (RA (DA1 g n) (DA1 g n)) :=
  (divA_both pg ha0 ha1 haw hn0 hn').mono (fun _ _ ⟨_, hs, ht⟩ => ⟨⟨⟨ha, haw⟩, hs⟩, ⟨⟨ha, haw⟩, ht⟩⟩)
    fun _ _ ⟨hs, ht⟩ => RA.of pg (fun _ h => let ⟨_, _, _, _, k, _⟩ := h; k.stage) hs ht

end VG.Proof.Rsa.X86.Recover
