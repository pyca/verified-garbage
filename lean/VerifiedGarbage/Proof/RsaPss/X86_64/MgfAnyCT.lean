module

public import VerifiedGarbage.Proof.RsaPss.X86_64.MgfAny
meta import VerifiedGarbage.Proof.RsaPss.X86_64.MgfAny
public import VerifiedGarbage.Proof.RsaPss.X86_64.MgfCT
meta import VerifiedGarbage.Proof.RsaPss.X86_64.MgfCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS on x86-64 with the hash functions as arguments: MGF1 is constant time

Two runs of `mgfXorAny hs` with the same frame, working space, writable
regions, place and length of `DB`, seed length `D` and MGF1's hash function
`g` (`MA`, `MEA`) leak the same trace (`mgfXorAny_ct`). The pieces that do
not depend on the hash function are checked by the taint analysis once
(`AnyMgfChecks`), with `D`, `g` and the message's length `D + 4` public
words of the frame; those of the hash function `hs[g]` are its
`HashChecks`; the dispatch goes the same way in both runs
(`dispatch_relCT`), and so does the branch on the number of blocks, which
`D` fixes.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Any

open VG VG.X86_64 VG.Impl.RsaPss.X86_64 VG.Impl.RsaPss.X86_64.AnyHash
open VG.Proof.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum (off)
open VG.Proof.Bignum.X86_64 (Two two_post two_map two_mono two_loop two_ite)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Dispatch.X86_64 (FlagsOnly)
open VG.Proof.RsaPss (lastBlk)

/-- The taint checks of MGF1's pieces that do not depend on the hash
functions, with `n` writable regions after the frame. -/
structure AnyMgfChecks (n : Nat) : Prop where
  clearCopy : ∃ hc, (taint.check (pT n [15, 21, 23, 24] []) (.seq clearSeedBlocks copySeed) hc).isSome = true
  counter : ∃ hc, (taint.check (pT n [15, 31] [.rcx]) (.block counterAny) hc).isSome = true
  selM : ∃ hc, (taint.check (pT n [48] []) (.block [.mov .rax (.mem (sp sMsel))]) hc).isSome = true
  pad : ∃ hc, (taint.check (pT n [21, 27] []) slotPad80 hc).isSome = true
  testFb : ∃ hc, (taint.check (pT n [30] [])
    (.block [.mov .rax (.mem (sp sFb)), .alu .test .rax (.reg .rax)]) hc).isSome = true

theorem anyMgfChecks {n : Nat} (hn : n = 1 ∨ n = 2) : AnyMgfChecks n := by
  rcases hn with rfl | rfl
  · exact ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩⟩
  · exact ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
      ⟨_, by taint_decide⟩⟩

-- A pair in a list of public words.
set_option hygiene false in
macro "mem_ws" : tactic => `(tactic| simp only [hws, List.mem_append, List.mem_cons,
  List.mem_singleton, List.not_mem_nil, true_or, or_true, or_false])

theorem Pub.flags {F S : Addr} {rest : List Region} {ws : List (Nat × BitVec 64)} {rs : List (Reg × BitVec 64)}
    {X : (Nat → Byte) → (Nat → BitVec 64) → Prop} {t t' : State} (h : Pub F S rest ws rs X t)
    (hf : FlagsOnly t t') : Pub F S rest ws rs X t' := by
  obtain ⟨V, W, R, hw, hx⟩ := h.W
  exact ⟨h.L.congr (hf.gpr _) hf.wr (by rw [hf.mem]), hf.wr.trans h.wr, ⟨V, W, hf.mem ▸ R, hw, hx⟩,
    fun p hp => (hf.gpr p.1).trans (h.regs p hp)⟩

/-- A public word, read. -/
theorem Pub.word {F S : Addr} {rest : List Region} {ws : List (Nat × BitVec 64)} {rs : List (Reg × BitVec 64)}
    {X : (Nat → Byte) → (Nat → BitVec 64) → Prop} {t : State} (h : Pub F S rest ws rs X t) :
    ∃ V W, Rep t.mem F S V W ∧ (∀ p ∈ ws, W p.1 = p.2) ∧ X V W := h.W

/-! ## MGF1's hash -/

section Hash

variable {G : Hash} (hG : HashOK G) (K : Callees G) (n : Nat) (ℓ : Nat)

variable (G) in
/-- At the start of the hash: the message's length `ℓ`, public here. -/
def HEL (a : HA) (t : State) : Prop :=
  HOk (H := G) n a ∧ Pub a.F a.S a.rest (hws a ++ [(27, BitVec.ofNat 64 ℓ)]) []
    (fun _ _ => ℓ + 1 + G.P.L ≤ a.nbm * G.P.B) t

variable (G) in
/-- After the length field: the index of the last block, public here. -/
def HFL (a : HA) (t : State) : Prop :=
  HOk (H := G) n a ∧ lastBlk G.P.B G.P.L ℓ < a.nbm ∧
    Pub a.F a.S a.rest (hws a ++ [(30, BitVec.ofNat 64 (lastBlk G.P.B G.P.L ℓ))]) [] (fun _ _ => True) t

theorem hel_he {a : HA} {t : State} (h : HEL G n ℓ a t) : HE G n a t := by
  obtain ⟨V, W, R, hw, hx⟩ := h.2.W
  exact ⟨h.1, ⟨h.2.L, h.2.wr, ⟨V, W, R, fun p hp => hw p (List.mem_append_left _ hp),
    ⟨ℓ, hw (27, BitVec.ofNat 64 ℓ) (by mem_ws), hx⟩⟩, fun _ hp => by cases hp⟩⟩

theorem hfl_hf {a : HA} {t : State} (h : HFL G n ℓ a t) : HF G n a t := by
  obtain ⟨V, W, R, hw, -⟩ := h.2.2.W
  exact ⟨h.1, ⟨h.2.2.L, h.2.2.wr, ⟨V, W, R, fun p hp => hw p (List.mem_append_left _ hp),
    ⟨_, hw (30, BitVec.ofNat 64 (lastBlk G.P.B G.P.L ℓ)) (by mem_ws), h.2.1⟩⟩, fun _ hp => by cases hp⟩⟩

include hG K in
theorem anyInit_ct (hfx : FixedChecks n) :
    RelCT isa (Two (HEL G n ℓ)) (ctInit G) (Two (HEL G n ℓ)) := by
  refine two_post ((ctInit_ct hG K n hfx).mono (fun _ _ ⟨a, h1, h2⟩ =>
    ⟨a, hel_he n ℓ h1, hel_he n ℓ h2⟩) (fun _ _ _ => trivial)) fun a t h => ?_
  obtain ⟨V, W, R, hw, hx⟩ := h.2.W
  exact WP.mono (ctInit_ok hG K h.2.L R) fun u ⟨L', _, hwr, _, R', _⟩ =>
    ⟨h.1, h.2.next L' hwr R' hw hx⟩

theorem anyPad_ct (ha : AnyMgfChecks n) :
    RelCT isa (Two (HEL G n ℓ)) slotPad80 (Two (HEL G n ℓ)) := by
  obtain ⟨_, hp⟩ := ha.pad
  refine two_post (two_pub n [21, 27] [] HA.F HA.S HA.rest (fun a => [(21, a.S), (27, BitVec.ofNat 64 ℓ)])
    (fun _ => []) (fun a t h => ⟨_, h.2.sub (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> mem_ws) (fun _ h => h) fun _ _ x => x⟩)
    (fun a t h => h.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp) fun a t h => ?_
  obtain ⟨V, W, R, hw, hfit⟩ := h.2.W
  obtain ⟨_, _, hnb⟩ := h.1
  refine WP.mono (slotPad80_ok h.2.L R (N := a.nbm * G.P.B) (hw (27, BitVec.ofNat 64 ℓ) (by mem_ws)) (by omega) hnb) fun u P =>
    ⟨h.1, h.2.next P.L P.keep.2.2 P.R hw hfit⟩

include hG in
theorem anyLen_ct (hc : HashChecks G.P G.D n) :
    RelCT isa (Two (HEL G n ℓ)) (.block (lenField G)) (Two (HFL G n ℓ)) := by
  refine two_post ((lenField_ct hG n hc).mono (fun _ _ ⟨a, h1, h2⟩ =>
    ⟨a, hel_he n ℓ h1, hel_he n ℓ h2⟩) (fun _ _ _ => trivial)) fun a t h => ?_
  obtain ⟨V, W, R, hw, hfit⟩ := h.2.W
  have hB0 := hG.B_pos
  refine WP.mono (lenField_ok hG h.2.L R (hw (27, BitVec.ofNat 64 ℓ) (by mem_ws)) (by obtain ⟨_, _, hnb⟩ := h.1; omega))
    fun u ⟨L', hk, R'⟩ => ⟨h.1, (Nat.div_lt_iff_lt_mul hB0).mpr (by omega), h.2.next L' hk.2.2 R' (fun q hq => ?_) trivial⟩
  rcases List.mem_append.mp hq with hq | hq
  · exact ws_upd (fun q hq' => hw q (List.mem_append_left _ hq')) (by simp [hws]) _ q hq
  · rw [List.mem_singleton.mp hq]; simp [upd]

theorem anyTest_ct (ha : AnyMgfChecks n) (hB0 : 0 < G.P.B) :
    RelCT isa (Two (HFL G n ℓ)) (.block [.mov .rax (.mem (sp sFb)), .alu .test .rax (.reg .rax)])
      (Two fun a t => HFL G n ℓ a t ∧ t.zf = some (decide (lastBlk G.P.B G.P.L ℓ = 0))) := by
  obtain ⟨_, hp⟩ := ha.testFb
  refine two_post (two_pub n [30] [] HA.F HA.S HA.rest
    (fun _ => [(30, BitVec.ofNat 64 (lastBlk G.P.B G.P.L ℓ))])
    (fun _ => []) (fun a t h => ⟨_, h.2.2.sub (fun q hq => by rw [List.mem_singleton.mp hq]; mem_ws)
      (fun _ h => h) fun _ _ x => x⟩)
    (fun a t h => h.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp) fun a t h => ?_
  obtain ⟨V, W, R, hw, -⟩ := h.2.2.W
  have L := h.2.2.L
  refine WP.mono (testFb_ok L R (hw (30, BitVec.ofNat 64 (lastBlk G.P.B G.P.L ℓ)) (by mem_ws)) (by
    have := h.2.1; obtain ⟨_, _, hnb⟩ := h.1
    have : a.nbm ≤ a.nbm * G.P.B := Nat.le_mul_of_pos_right _ hB0
    omega))
    fun u ⟨hz, hm, hk⟩ => ⟨⟨h.1, h.2.1, h.2.2.next (L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm])) hk.2.2
      (hm ▸ R) hw trivial⟩, hz⟩

include hG K in
/-- The digest of a message of the public length `ℓ`. -/
theorem mgfHashAny_ct (hc : HashChecks G.P G.D n) (hfx : FixedChecks n) (ha : AnyMgfChecks n) :
    RelCT isa (Two (HEL G n ℓ)) (mgfHashAny G) fun _ _ => True := by
  unfold mgfHashAny seqs seqs seqs seqs
  refine (anyInit_ct hG K n ℓ hfx).seq ((anyPad_ct n ℓ ha).seq ((anyLen_ct hG n ℓ hc).seq
    ((anyTest_ct n ℓ ha hG.B_pos).seq (two_ite (fun a s₁ s₂ h₁ h₂ => by
      rw [show isa.eval .e s₁ = s₁.zf from rfl, show isa.eval .e s₂ = s₂.zf from rfl, h₁.2, h₂.2]) ?_ ?_))))
  · unfold directRest seqs seqs seqs
    refine ((directLen_ct hG n hc).mono (fun _ _ ⟨a, h1, h2⟩ => ⟨a, hfl_hf n ℓ h1.1.1, hfl_hf n ℓ h2.1.1⟩)
      (fun _ _ h => h)).seq ((startB_ct n hfx).seq ?_)
    exact two_map (fun a : HA => (a, 0)) (fun _ _ h => h) ((compA_ct hG n hc).seq (digestState_ct n hc))
  · unfold genericRest seqs seqs
    exact ((lenLoop_ct hG n hc).mono (fun _ _ ⟨a, h1, h2⟩ => ⟨a, hfl_hf n ℓ h1.1.1, hfl_hf n ℓ h2.1.1⟩)
      (fun _ _ h => h)).seq ((compLoop_ct hG n hc hfx).seq (digestOut_ct n hc))

end Hash

/-! ## The loop -/

section Loop

variable (n D g gd : Nat) (Gs : Spec.Mgf1.Hash)

/-- The anchor fits `mgfXorAny`. -/
def MOkA (a : MA) : Prop := RestOk n a.F a.rest ∧ DbAt D a.e a.db ∧ 0 < D ∧ D ≤ 64

/-- The public words of the entry. -/
def mwsE (a : MA) : List (Nat × BitVec 64) :=
  [(15, BitVec.ofNat 64 D), (21, a.S), (23, off a.S a.e), (24, BitVec.ofNat 64 a.db), (48, BitVec.ofNat 64 g)]

/-- The public words in round `j`. -/
def mwsA (a : MA) (j : Nat) : List (Nat × BitVec 64) :=
  [(15, BitVec.ofNat 64 D), (21, a.S), (23, off a.S a.e), (24, BitVec.ofNat 64 a.db), (31, BitVec.ofNat 64 j),
    (32, BitVec.ofNat 64 (j * gd)), (48, BitVec.ofNat 64 g)]

-- A pair in a list of public words of MGF1's loop.
set_option hygiene false in
macro "mem_wsA" : tactic => `(tactic| simp only [mwsA, mwsE, hws, List.mem_append, List.mem_cons,
  List.mem_singleton, List.not_mem_nil, true_or, or_true, or_false])

theorem mwsA_keys {a : MA} {j : Nat} {q : Nat × BitVec 64} (hq : q ∈ mwsA D g gd a j) :
    q.1 = 15 ∨ q.1 = 21 ∨ q.1 = 23 ∨ q.1 = 24 ∨ q.1 = 31 ∨ q.1 = 32 ∨ q.1 = 48 := by
  simp only [mwsA, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- At the start. -/
def MEA (a : MA) (t : State) : Prop :=
  MOkA n D a ∧ Pub a.F a.S a.rest (mwsE D g a) [] (fun _ _ => True) t

/-- Before round `j`: the correctness proof's invariant. -/
def MIA (a : MA) (j : Nat) (t : State) : Prop :=
  MOkA n D a ∧ j * gd < a.db ∧ ∃ (u₀ : State) (V : Nat → Byte) (W : Nat → BitVec 64),
    u₀.wr = ⟨a.F, frameBytes⟩ :: a.rest ∧ W 15 = BitVec.ofNat 64 D ∧ W 21 = a.S ∧ W 23 = off a.S a.e ∧
    W 24 = BitVec.ofNat 64 a.db ∧ W 48 = BitVec.ofNat 64 g ∧
    MgfI u₀ a.F a.S V W (Spec.Mgf1.mgf1 Gs ((List.range D).map fun i => V (a.e + a.db + i)) a.db)
      a.e a.db gd j t

theorem mia_rep {a : MA} {j : Nat} {t : State} (h : MIA n D g gd Gs a j t) :
    ∃ V W, Rep t.mem a.F a.S V W ∧ ∀ q ∈ mwsA D g gd a j, W q.1 = q.2 := by
  obtain ⟨-, -, u₀, V, W, -, h15, h21, h23, h24, h48, I⟩ := h
  obtain ⟨V', W', R', h31, h32, hW, -⟩ := I.rep
  refine ⟨V', W', R', fun q hq => ?_⟩
  simp only [mwsA, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hW 15 (by decide) (.inl (by decide))).trans h15
  · exact (hW 21 (by decide) (.inl (by decide))).trans h21
  · exact (hW 23 (by decide) (.inl (by decide))).trans h23
  · exact (hW 24 (by decide) (.inl (by decide))).trans h24
  · exact h31
  · exact h32
  · exact (hW 48 (by decide) (.inr (by decide))).trans h48

theorem mia_pub {a : MA} {j : Nat} {t : State} (h : MIA n D g gd Gs a j t) :
    Pub a.F a.S a.rest (mwsA D g gd a j) [] (fun _ _ => True) t := by
  obtain ⟨V, W, R, hw⟩ := mia_rep n D g gd Gs h
  obtain ⟨-, -, u₀, _, _, hwr, -, -, -, -, -, I⟩ := h
  exact ⟨I.L, I.wr.trans hwr, ⟨V, W, R, hw, trivial⟩, fun _ hp => by cases hp⟩

/-- Round `j`, as the loop sees it. -/
abbrev MBA (p : MA × Nat) (t : State) : Prop := p.2 < mN gd p.1 ∧ MIA n D g gd Gs p.1 p.2 t

/-- After `H` is copied to `Y`, cleared after it, and `rcx` is `Y`. -/
def M1A (p : MA × Nat) (t : State) : Prop :=
  MOkA n D p.1 ∧ p.2 * gd < p.1.db ∧ Pub p.1.F p.1.S p.1.rest (mwsA D g gd p.1 p.2) [(.rcx, off p.1.S oY)]
    (fun V _ => ∀ i, D ≤ i → i < 256 → V (oY + i) = 0) t

/-- After the counter: `H ‖ C` in `Y`, cleared after it. -/
def M2A (p : MA × Nat) (t : State) : Prop :=
  MOkA n D p.1 ∧ p.2 * gd < p.1.db ∧
    Pub p.1.F p.1.S p.1.rest (mwsA D g gd p.1 p.2 ++ [(27, BitVec.ofNat 64 (D + 4)), (28, BitVec.ofNat 64 2)]) []
      (fun V _ => ∀ i, D + 4 ≤ i → i < 256 → V (oY + i) = 0) t

/-- After the hash. -/
def M3A (p : MA × Nat) (t : State) : Prop :=
  MOkA n D p.1 ∧ p.2 * gd < p.1.db ∧ Pub p.1.F p.1.S p.1.rest (mwsA D g gd p.1 p.2) [] (fun _ _ => True) t

/-- After the digest is XORed into `DB`. -/
def M4A (p : MA × Nat) (t : State) : Prop :=
  MOkA n D p.1 ∧ Pub p.1.F p.1.S p.1.rest (mwsA D g gd p.1 p.2) [] (fun _ _ => True) t

theorem anyClearCopy_ct (ha : AnyMgfChecks n) :
    RelCT isa (Two (MBA n D g gd Gs)) (.seq clearSeedBlocks copySeed) (Two (M1A n D g gd)) := by
  obtain ⟨_, hp⟩ := ha.clearCopy
  refine two_post (two_pub n [15, 21, 23, 24] [] (fun p => p.1.F) (fun p => p.1.S) (fun p => p.1.rest)
    (fun p => [(15, BitVec.ofNat 64 D), (21, p.1.S), (23, off p.1.S p.1.e), (24, BitVec.ofNat 64 p.1.db)])
    (fun _ => [])
    (fun p t h => ⟨_, (mia_pub n D g gd Gs h.2).sub (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> mem_wsA) (fun _ h => h) fun _ _ x => x⟩)
    (fun p t h => h.2.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp) fun p t h => ?_
  obtain ⟨V1, W1, R1, hw⟩ := mia_rep n D g gd Gs h.2
  obtain ⟨hm, hj, u₀, _, _, hwr, -, -, -, -, -, I⟩ := h.2
  have w15 : W1 15 = BitVec.ofNat 64 D := hw (15, BitVec.ofNat 64 D) (by mem_wsA)
  have w23 : W1 23 = off p.1.S p.1.e := hw (23, off p.1.S p.1.e) (by mem_wsA)
  have w24 : W1 24 = BitVec.ofNat 64 p.1.db := hw (24, BitVec.ofNat 64 p.1.db) (by mem_wsA)
  refine WP.seq (WP.mono (clearSeedBlocks_ok I.L R1) fun u1 ⟨L1, k1, hcx1, R1'⟩ => ?_)
  refine WP.mono (copySeed_ok L1 R1' hm.2.1 w23 w24 w15 hm.2.2.1 hcx1) fun u2 ⟨L2, k2, R2⟩ =>
    ⟨hm, hj, L2, k2.2.2.trans (k1.2.2.trans (I.wr.trans hwr)), ⟨_, _, R2, hw, fun i h1 h2 => ?_⟩, fun q hq => ?_⟩
  · simp only [cpV, clrV]
    rw [ifn (by omega), ifp (by omega)]
  · rw [List.mem_singleton.mp hq]
    show u2.gpr .rcx = off p.1.S oY
    exact (k2.gpr (by decide)).trans hcx1

theorem anyCounter_ct (ha : AnyMgfChecks n) (hgd : 0 < gd) :
    RelCT isa (Two (M1A n D g gd)) (.block counterAny) (Two (M2A n D g gd)) := by
  obtain ⟨_, hp⟩ := ha.counter
  refine two_post (two_pub n [15, 31] [.rcx] (fun p => p.1.F) (fun p => p.1.S) (fun p => p.1.rest)
    (fun p => [(15, BitVec.ofNat 64 D), (31, BitVec.ofNat 64 p.2)]) (fun p => [(.rcx, off p.1.S oY)])
    (fun p t h => ⟨_, h.2.2.sub (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> mem_wsA) (fun _ h => h) fun _ _ x => x⟩)
    (fun p t h => h.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp) fun p t h => ?_
  obtain ⟨hm, hj, P⟩ := h
  obtain ⟨V, W, R, hw, hz⟩ := P.W
  have hfit := hm.2.1.fit
  have c1 : oEm = 2560 := rfl
  have hjD : p.2 ≤ p.2 * gd := Nat.le_mul_of_pos_right _ hgd
  refine WP.mono (counterAny_ok P.L R (hw (31, BitVec.ofNat 64 p.2) (by mem_wsA)) (by omega)
    (hw (15, BitVec.ofNat 64 D) (by mem_wsA)) hm.2.2.2 (P.regs (.rcx, _) (by mem_wsA)))
    fun u ⟨L', k, R'⟩ => ⟨hm, hj, P.next L' k.2.2 R' (fun q hq => ?_) fun i h1 h2 => ?_⟩
  · rcases List.mem_append.mp hq with hq | hq
    · have := mwsA_keys D g gd hq
      simp only [upd]
      rw [ifn (by omega), ifn (by omega)]
      exact hw q hq
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> simp [upd]
  · simp only [ctrV]
    rw [ifn (by omega)]
    exact hz i (by omega) h2

section Case

variable {hs : List Hash} {g : Nat} (hg : g < hs.length) (hG : HashOK hs[g]) (K : Callees hs[g])

include hG K in
theorem anyHash_ct (hc : HashChecks hs[g].P hs[g].D n) (hfx : FixedChecks n) (ha : AnyMgfChecks n) :
    RelCT isa (Two (M2A n D g hs[g].D)) (mgfHashAny hs[g]) (Two (M3A n D g hs[g].D)) := by
  have hB := hG.dims.B
  have hL := hG.dims.L
  refine two_post (two_map (fun p : MA × Nat => (⟨p.1.F, p.1.S, p.1.rest, 2⟩ : HA))
    (fun p t h => by
      obtain ⟨hm, hj, P⟩ := h
      have := hm.2.2.2
      refine ⟨⟨hm.1, by show 1 ≤ 2; decide, by show 2 * hs[g].P.B ≤ 2048; omega⟩,
        P.sub (fun q hq => ?_) (fun _ h => h) fun _ _ _ => by show D + 4 + 1 + hs[g].P.L ≤ 2 * hs[g].P.B; omega⟩
      simp only [hws, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with (rfl | rfl) | rfl <;> mem_wsA) (mgfHashAny_ct hG K n (D + 4) hc hfx ha)) fun p t h => ?_
  obtain ⟨hm, hj, P⟩ := h
  obtain ⟨V, W, R, hw, hz⟩ := P.W
  refine WP.mono (mgfHashAny_gen hG K P.L R (hw (27, BitVec.ofNat 64 (D + 4)) (by mem_wsA)) (hw (28, BitVec.ofNat 64 2) (by mem_wsA))
    (by have := hm.2.2.2; rcases hB with h | h <;> rw [h] <;> omega))
    fun u ⟨L', _, hwr, _, V', W', R', _, hW', _⟩ => ⟨hm, hj, P.next L' hwr R' (fun q hq => ?_) trivial⟩
  have := mwsA_keys D g hs[g].D hq
  rw [hW' q.1 (by unfold nW frameBytes; omega) (by omega) (by omega)]
  exact hw q (List.mem_append_left _ hq)

include hG in
theorem anyXorOut_ct (hc : HashChecks hs[g].P hs[g].D n) :
    RelCT isa (Two (M3A n D g hs[g].D)) (xorOut hs[g]) (Two (M4A n D g hs[g].D)) := by
  obtain ⟨_, hp⟩ := hc.xorOut
  refine two_post (two_pub n [21, 23, 24, 32] [] (fun p => p.1.F) (fun p => p.1.S) (fun p => p.1.rest)
    (fun p => [(21, p.1.S), (23, off p.1.S p.1.e), (24, BitVec.ofNat 64 p.1.db),
      (32, BitVec.ofNat 64 (p.2 * hs[g].D))])
    (fun _ => [])
    (fun p t h => ⟨_, h.2.2.sub (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> mem_wsA) (fun _ h => h) fun _ _ x => x⟩)
    (fun p t h => h.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp) fun p t h => ?_
  obtain ⟨hm, hj, P⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := P.W
  exact WP.mono (xorOut_ok hG P.L R hm.2.1.zero (hw (23, off p.1.S p.1.e) (by mem_wsA))
    (hw (24, BitVec.ofNat 64 p.1.db) (by mem_wsA)) (hw (32, BitVec.ofNat 64 (p.2 * hs[g].D)) (by mem_wsA)) hj)
    fun u ⟨L', k, R'⟩ => ⟨hm, P.next L' k.2.2 R' hw trivial⟩

theorem anyNextCtr_ct (hc : HashChecks hs[g].P hs[g].D n) :
    RelCT isa (Two (M4A n D g hs[g].D)) (.block (nextCtr hs[g])) fun _ _ => True := by
  obtain ⟨_, hp⟩ := hc.nextCtr
  exact two_pub n [24, 31, 32] [] (fun p => p.1.F) (fun p => p.1.S) (fun p => p.1.rest)
    (fun p => [(24, BitVec.ofNat 64 p.1.db), (31, BitVec.ofNat 64 p.2), (32, BitVec.ofNat 64 (p.2 * hs[g].D))])
    (fun _ => [])
    (fun p t h => ⟨_, h.2.sub (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> mem_wsA) (fun _ h => h) fun _ _ x => x⟩)
    (fun p t h => h.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp

include hG K in
theorem anyRound_ct (hl : hs.length ≤ 2 ^ 31) (hc : HashChecks hs[g].P hs[g].D n) (hfx : FixedChecks n)
    (ha : AnyMgfChecks n) :
    RelCT isa (Two (MBA n D g hs[g].D Gs)) (.seq seedPart (dispatch sMsel gPart hs)) fun _ _ => True := by
  have hgd := hG.hD0
  have h1 : RelCT isa (Two (MBA n D g hs[g].D Gs)) seedPart (Two (M2A n D g hs[g].D)) := by
    unfold seedPart; simp only [seqs]
    exact RelCT.assoc ((anyClearCopy_ct n D g hs[g].D Gs ha).seq (anyCounter_ct n D g hs[g].D ha hgd))
  refine RelCT.seq h1 ?_
  obtain ⟨_, hsel⟩ := ha.selM
  refine dispatch_relCT (Ψ := M2A n D g hs[g].D) hg hl (two_pub n [48] [] (fun p => p.1.F) (fun p => p.1.S)
    (fun p => p.1.rest) (fun _ => [(48, BitVec.ofNat 64 g)]) (fun _ => [])
    (fun p t h => ⟨_, h.2.2.sub (fun q hq => by rw [List.mem_singleton.mp hq]; mem_wsA) (fun _ h => h)
      fun _ _ x => x⟩) (fun p t h => h.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hsel) (fun p t h => ?_) ?_
  · obtain ⟨hm, hj, P⟩ := h
    obtain ⟨V, W, R, hw, hz⟩ := P.W
    have L := P.L
    have h48 : t.mem.readW (off p.1.F sMsel) 64 = BitVec.ofNat 64 g := by
      rw [R.rd (d := sMsel) 48 rfl (by decide), hw (48, BitVec.ofNat 64 g) (by mem_wsA)]
    refine WP.mono (WP.keep [.rax] (Q := fun u => u.gpr .rax = BitVec.ofNat 64 g ∧ u.mem = t.mem) ?_ rfl)
      fun u ⟨⟨hax, hm'⟩, k⟩ => ⟨⟨hm, hj, P.next (L.congr (k.gpr (by decide)) k.2.2 (by rw [hm'])) k.2.2
        (hm' ▸ R) hw hz⟩, hax⟩
    xrun [ea_sp, L.rsp, L.ld (d := sMsel) (by decide), h48]
  · unfold gPart seqs seqs
    refine RelCT.seq ((anyHash_ct n D hg hG K hc hfx ha).mono (fun _ _ ⟨p, ⟨s₁, h₁, f₁⟩, ⟨s₂, h₂, f₂⟩⟩ =>
      ⟨p, ⟨h₁.1, h₁.2.1, Pub.flags h₁.2.2 f₁⟩, ⟨h₂.1, h₂.2.1, Pub.flags h₂.2.2 f₂⟩⟩) (fun _ _ h => h))
      ((anyXorOut_ct n D hg hG hc).seq (anyNextCtr_ct n D hg hc))

include hG in
theorem anyInit_mgf_ct (hfx : FixedChecks n) :
    RelCT isa (Two (MEA n D g)) (.block [.mov32 .rax (.imm 0), .store (sp sCtr) .rax, .store (sp sDone) .rax])
      (Two fun a t => 0 < mN hs[g].D a ∧ MIA n D g hs[g].D Gs a 0 t) := by
  obtain ⟨_, hp⟩ := hfx.mgfInit
  refine two_post (two_pub n [21, 23, 24] [] MA.F MA.S MA.rest
    (fun a => [(21, a.S), (23, off a.S a.e), (24, BitVec.ofNat 64 a.db)]) (fun _ => [])
    (fun a t h => ⟨_, h.2.sub (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> mem_wsA) (fun _ h => h) fun _ _ x => x⟩)
    (fun a t h => h.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp) fun a t h => ?_
  obtain ⟨V, W, R, hw, -⟩ := h.2.W
  have L := h.2.L
  have hD := hG.hD0
  have hdb1 := h.1.2.1.db1
  have G' := L.geo
  have R2 := (R.wf G' (k := 31) (by decide) 0#64).wf G' (k := 32) (by decide) 0#64
  rw [show off a.F (8 * 31) = off a.F sCtr from rfl, show off a.F (8 * 32) = off a.F sDone from rfl] at R2
  refine WP.mono (WP.keep [.rax] (Q := fun v => v.mem =
      (t.mem.writeW (off a.F sCtr) 0#64).writeW (off a.F sDone) 0#64) ?_ rfl) fun v ⟨hm, hk⟩ => ?_
  · xrun [ea_sp, L.rsp, L.st (d := sCtr) (by decide), L.st (d := sDone) (by decide),
      show BitVec.setWidth 64 (0 : BitVec 32) = 0#64 from rfl]
  have R2' : Rep v.mem a.F a.S V (upd (upd W 31 0#64) 32 0#64) := hm ▸ R2
  have Lv : Lay v a.F a.S := L.congr (hk.gpr (by decide)) hk.2.2 (by
    rw [slot_eq sScr 21 rfl, slot_eq sScr 21 rfl, R2'.fr 21 (by decide), R.fr 21 (by decide)]; simp [upd])
  refine ⟨(cnt_iff hD).mpr (by rw [Nat.zero_mul]; omega), h.1, by rw [Nat.zero_mul]; omega, t, V, W, h.2.wr,
    hw (15, BitVec.ofNat 64 D) (by mem_wsA), hw (21, a.S) (by mem_wsA), hw (23, off a.S a.e) (by mem_wsA),
    hw (24, BitVec.ofNat 64 a.db) (by mem_wsA), hw (48, BitVec.ofNat 64 g) (by mem_wsA),
    Lv, hk.2.1, hk.2.2, keep_cs hk (by decide), _, _, R2', by simp [upd], by simp [upd],
    fun k _ h => by simp only [upd, ifn (show k ≠ 32 by omega), ifn (show k ≠ 31 by omega)],
    fun o _ _ => by simp only [mixV, Nat.zero_mul, Nat.zero_min, Nat.add_zero]; rw [ifn (by omega)]⟩

include hG K in
theorem anyRound_wp (hl : hs.length ≤ 2 ^ 31) (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = hs[g].D)
    (hGv : Proof.Mgf1.Valid Gs) {a : MA} {j : Nat} {t : State} (h : MIA n D g hs[g].D Gs a j t) :
    WP isa (.seq seedPart (dispatch sMsel gPart hs)) t fun t' =>
      isa.eval .b t' = some (decide (j + 1 < mN hs[g].D a)) ∧ (j + 1 < mN hs[g].D a → MIA n D g hs[g].D Gs a (j + 1) t') ∧
      (j + 1 = mN hs[g].D a → True) := by
  have hD := hG.hD0
  obtain ⟨hm, hjD, u₀, V, W, hwr, h15, h21, h23, h24, h48, I⟩ := h
  refine WP.mono (roundAny_ok hg hl hG K hGh hGl hGv hm.2.1 hm.2.2.1 hm.2.2.2 h23 h24 h15 h48 I hjD)
    fun t' ⟨hcf, I'⟩ => ⟨?_, fun h' => ⟨hm, (cnt_iff hD).mp h', u₀, V, W, hwr, h15, h21, h23, h24, h48, I'⟩,
      fun _ => trivial⟩
  simp only [eval, hcf, Option.some.injEq, decide_eq_decide]
  exact (cnt_iff hD).symm

include hG K in
/-- `mgfXorAny` is constant time. -/
theorem mgfXorAny_ct (hl : hs.length ≤ 2 ^ 31) (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = hs[g].D)
    (hGv : Proof.Mgf1.Valid Gs) (hc : HashChecks hs[g].P hs[g].D n) (hfx : FixedChecks n) (ha : AnyMgfChecks n) :
    RelCT isa (Two (MEA n D g)) (mgfXorAny hs) fun _ _ => True :=
  (anyInit_mgf_ct n D Gs hg hG hfx).seq ((two_loop (Φ := MIA n D g hs[g].D Gs) (Ψ := fun _ _ => True)
    (mN hs[g].D) (anyRound_ct n D Gs hg hG K hl hc hfx ha)
    fun _ _ _ _ h => anyRound_wp n D Gs hg hG K hl hGh hGl hGv h).mono (fun _ _ h => h) fun _ _ _ => trivial)

end Case

end Loop

end VG.Proof.RsaPss.X86_64.Any
