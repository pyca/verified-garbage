module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.TailRounds
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.Rounds3

/-!
# ChaCha20 and Poly1305 together (x86-64): the rounds of three sets

`Stitch.troundsG3`: `Avx2Tail`'s double rounds on three sets of two blocks
(`last3`'s, the masks in `ymm14`, `ymm15`), absorbing the blocks of a
schedule at `rsi` between their halves, as `troundsG` does on one set or
two (`TailRounds.lean`): a double round is six parts (`trH3`), each a list
of `Avx2Tail`'s instructions of three sets (`ymmOf3`), which together are
the double round on the words (`Avx2Tail.block3_ok`, `dr3_words`); the
blocks of Poly1305 between them write only Poly1305's registers and no
vector register or memory, and the parts write only vector registers.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Proof.ChaCha20.X86_64.Avx2Tail (HY3 YM3 HB ymmOf3 hiOk3 block3_ok hy3_wordsOf hb_of3 blk_wordsOf
  wordsOf half3H cols3H diags3H dr3_words)
open VG.Proof.ChaCha20.X86_64.Avx512Tail (HI W hstep rotH)
open VG.Proof.Poly1305.X86_64 (Keeps absorbRegs)
open VG.Proof.ChaCha20 (CState)
open VG.Spec.ChaCha20 (innerBlock)
open VG.Spec.Poly1305 (bytesAt)
open VG.Proof.Poly1305 (absorbAll)

/-- The six parts of a double round on three sets. -/
def trH3 : Nat → List HI
  | 0 => half3H 16 12
  | 1 => half3H 8 7
  | 2 => rotH .xmm1 .xmm2 .xmm3 0x39 0x4e 0x93 ++ rotH .xmm5 .xmm6 .xmm7 0x39 0x4e 0x93 ++
    rotH .xmm9 .xmm10 .xmm11 0x39 0x4e 0x93
  | 3 => half3H 16 12
  | 4 => half3H 8 7
  | _ => rotH .xmm1 .xmm2 .xmm3 0x93 0x4e 0x39 ++ rotH .xmm5 .xmm6 .xmm7 0x93 0x4e 0x39 ++
    rotH .xmm9 .xmm10 .xmm11 0x93 0x4e 0x39

theorem drH3_eq : cols3H ++ diags3H = trH3 0 ++ trH3 1 ++ trH3 2 ++ trH3 3 ++ trH3 4 ++ trH3 5 := by
  simp only [cols3H, diags3H, trH3, List.append_assoc]

theorem trH3_ok (i : Nat) : (trH3 i).all hiOk3 = true := by
  unfold trH3; split <;> decide

theorem half3_eq :
    Impl.ChaCha20.X86_64.Avx2Tail.half3 .xmm14 12 = (trH3 0).flatMap ymmOf3 ∧
    Impl.ChaCha20.X86_64.Avx2Tail.half3 .xmm15 7 = (trH3 1).flatMap ymmOf3 ∧
    Impl.ChaCha20.X86_64.Avx2Tail.rot3 0x39 0x4e 0x93 = (trH3 2).flatMap ymmOf3 ∧
    Impl.ChaCha20.X86_64.Avx2Tail.rot3 0x93 0x4e 0x39 = (trH3 5).flatMap ymmOf3 := by
  decide +kernel

/-- A double round of three sets with the blocks between its parts. -/
theorem troundG3_eq (bl fb : Nat → Nat) (n : Nat) (h0 : bl n ≠ 0) :
    troundG3 bl fb n = (trH3 0).flatMap ymmOf3 ++
      ((if bl n = 4 then piece (fb n + bl n - 4) else []) ++
      ((trH3 1).flatMap ymmOf3 ++ (piece (fb n + bl n - 4 + 1) ++
      ((trH3 2).flatMap ymmOf3 ++ ((trH3 3).flatMap ymmOf3 ++ (piece (fb n + bl n - 4 + 2) ++
      ((trH3 4).flatMap ymmOf3 ++ (piece (fb n + bl n - 4 + 3) ++
      (trH3 5).flatMap ymmOf3)))))))) := by
  obtain ⟨e0, e1, e2, e5⟩ := half3_eq
  simp only [troundG3, h0, ite_false, e0, e1, e2, e5, show trH3 3 = trH3 0 from rfl,
    show trH3 4 = trH3 1 from rfl, List.append_assoc]

/-- A double round of three sets absorbing nothing. -/
theorem troundG3_eq0 (bl fb : Nat → Nat) (n : Nat) (h0 : bl n = 0) :
    troundG3 bl fb n = (trH3 0).flatMap ymmOf3 ++ ((trH3 1).flatMap ymmOf3 ++
      ((trH3 2).flatMap ymmOf3 ++ ((trH3 3).flatMap ymmOf3 ++ ((trH3 4).flatMap ymmOf3 ++
      (trH3 5).flatMap ymmOf3)))) := by
  obtain ⟨e0, e1, e2, e5⟩ := half3_eq
  simp only [troundG3, h0, ite_true, e0, e1, e2, e5, show trH3 3 = trH3 0 from rfl,
    show trH3 4 = trH3 1 from rfl, List.append_assoc]

/-- During the rounds of three sets: their states `vs` in the vector
registers, the masks, the memory, the permissions and the registers but
Poly1305's as in `s₁`, and Poly1305's satisfying `Q`. -/
structure TB3 (s₁ : State) (vs : Nat → CState) (Q : State → Prop) (s : State) : Prop where
  hb : HB 3 vs s
  ym : YM3 s
  mem : s.mem = s₁.mem
  gpr : ∀ r, r ∉ absorbRegs → s.gpr r = s₁.gpr r
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  poly : Q s

/-- As `TB3`, with the words of the vector registers `ws`. -/
structure TW3 (s₁ : State) (ws : Nat → W) (Q : State → Prop) (s : State) : Prop where
  hy : HY3 ws s
  ym : YM3 s
  mem : s.mem = s₁.mem
  gpr : ∀ r, r ∉ absorbRegs → s.gpr r = s₁.gpr r
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  poly : Q s

section
variable {s₁ : State}

/-- A part of the double round. -/
theorem seg_tw3 {is : List HI} (hok : is.all hiOk3 = true) {ws : Nat → W} {Q : State → Prop}
    (hQ : ∀ s s' : State, s'.gpr = s.gpr → Q s → Q s') {s : State} (h : TW3 s₁ ws Q s) :
    WP isa (.block (is.flatMap ymmOf3)) s (TW3 s₁ (fun l => is.foldl hstep (ws l)) Q) :=
  WP.mono (block3_ok is hok h.hy h.ym) fun s' ⟨hy, ym, f⟩ =>
    ⟨hy, ym, f.mem.trans h.mem, fun r hr => by rw [f.gpr, h.gpr r hr], f.rd.trans h.rd, f.wr.trans h.wr,
      hQ s s' f.gpr h.poly⟩

/-- Code that keeps the vector registers and Poly1305's frame keeps `TW3`. -/
theorem TW3.piece {ws : Nat → W} {Q Q' : State → Prop} {s s' : State} (h : TW3 s₁ ws Q s) (hq : Q' s')
    (k : Keeps absorbRegs s s') (hx : s'.xmm = s.xmm) (hy : s'.ymmHi = s.ymmHi) : TW3 s₁ ws Q' s' :=
  ⟨fun r l q hr hl hq' => by simpa only [State.lane, hx, hy] using h.hy r l q hr hl hq',
    fun l => by simpa only [State.lane, hx, hy] using h.ym l, by rw [k.2.1, h.mem],
    fun r hr => by rw [k.1 r hr, h.gpr r hr], by rw [k.2.2.1, h.rd], by rw [k.2.2.2, h.wr], hq⟩

variable {q : Addr} {N : Nat} {R0 R1 : BitVec 64} {X : Nat} (hk : Key R0 R1) (hrsi : s₁.gpr .rsi = q)
  (hin : ∀ off n, off + n ≤ N → InRegions (s₁.rd ++ s₁.wr) (q + BitVec.ofNat 64 off) n)
include hk hrsi hin

/-- Block `j` of the `N` bytes at `q`. -/
theorem piece_tw3 {j : Nat} (hj : 16 * j + 16 ≤ N) {ws : Nat → W} {s : State}
    (h : TW3 s₁ ws (AccTo q R0 R1 X s₁ j) s) :
    WP isa (.block (piece j)) s (TW3 s₁ ws (AccTo q R0 R1 X s₁ (j + 1))) := by
  unfold piece
  refine WP.block_append (WP.mono (addProd_ok hk h.poly (p := q) (by rw [h.gpr _ (by decide), hrsi]) (j := j)
    fun e he => by rw [h.rd, h.wr]; exact hin _ _ (by omega)) fun s' ⟨a, k, x, y⟩ => ?_)
  have a' : HalfTo q R0 R1 X s₁ j s' := by
    show Half R0 R1 (absorbAll (rN R0 R1) X (bytesAt s₁.mem q (16 * (j + 1)))) s'
    rw [h.mem] at a
    rw [Nat.mul_add, Nat.mul_one, VG.Proof.Poly1305.bytesAt_add,
      VG.Proof.Poly1305.absorbAll_append (by rw [VG.Proof.Poly1305.length_bytesAt]; omega)]
    exact a
  exact WP.mono (carry1_ok hk a') fun s'' ⟨a₂, k₂, x₂, y₂⟩ =>
    (h.piece a' k x y).piece a₂ k₂ x₂ y₂

/-- A double round on three sets, absorbing its blocks. -/
theorem troundG3_ok {bl fb : Nat → Nat} {tot : Nat} (sc : SchedOk bl fb tot)
    (hN : 16 * tot ≤ N) {n : Nat} (hn : n < 10)
    {vs : Nat → CState} {s : State} (h : TB3 s₁ vs (AccTo q R0 R1 X s₁ (fb n)) s) :
    WP isa (.block (troundG3 bl fb n)) s
      (TB3 s₁ (fun j => innerBlock (vs j)) (AccTo q R0 R1 X s₁ (fb (n + 1)))) := by
  have hb32 : fb n + bl n ≤ tot := by
    rw [← sc.succ n hn]; exact sc.le _ (by omega)
  have hfb : bl n ≠ 0 → 4 ≤ fb n + bl n := sc.four n hn
  -- The parts, as steps of `TW3`.
  have tw : TW3 s₁ (wordsOf s) (AccTo q R0 R1 X s₁ (fb n)) s :=
    ⟨hy3_wordsOf s, h.ym, h.mem, h.gpr, h.rd, h.wr, h.poly⟩
  have hwords : ∀ {s' : State}, TW3 s₁ (fun l => (cols3H ++ diags3H).foldl hstep (wordsOf s l))
      (AccTo q R0 R1 X s₁ (fb (n + 1))) s' →
      TB3 s₁ (fun j => innerBlock (vs j)) (AccTo q R0 R1 X s₁ (fb (n + 1))) s' := fun h' =>
    ⟨hb_of3 h'.hy (fun k hk l hl => by rw [dr3_words _ hk, blk_wordsOf h.hb hk hl]) (by decide), h'.ym,
      h'.mem, h'.gpr, h'.rd, h'.wr, h'.poly⟩
  by_cases e0 : bl n = 0
  · -- No blocks.
    have ef : fb (n + 1) = fb n := by rw [sc.succ n hn, e0, Nat.add_zero]
    rw [troundG3_eq0 bl fb n e0]
    simp only [drH3_eq, List.foldl_append] at hwords
    refine WP.block_append (WP.mono (seg_tw3 (trH3_ok 0) acc_gpr tw) fun t₁ h₁ => ?_)
    refine WP.block_append (WP.mono (seg_tw3 (trH3_ok 1) acc_gpr h₁) fun t₂ h₂ => ?_)
    refine WP.block_append (WP.mono (seg_tw3 (trH3_ok 2) acc_gpr h₂) fun t₃ h₃ => ?_)
    refine WP.block_append (WP.mono (seg_tw3 (trH3_ok 3) acc_gpr h₃) fun t₄ h₄ => ?_)
    refine WP.block_append (WP.mono (seg_tw3 (trH3_ok 4) acc_gpr h₄) fun t₅ h₅ => ?_)
    exact WP.mono (seg_tw3 (trH3_ok 5) acc_gpr h₅) fun _ h' => hwords (by rw [ef]; exact h')
  have hfb' := hfb e0
  obtain ⟨j, hj⟩ : ∃ j, j = fb n + bl n - 4 := ⟨_, rfl⟩
  have hfin : ∀ {s' : State}, TW3 s₁ (fun l => (cols3H ++ diags3H).foldl hstep (wordsOf s l))
      (AccTo q R0 R1 X s₁ (j + 3 + 1)) s' →
      TB3 s₁ (fun j => innerBlock (vs j)) (AccTo q R0 R1 X s₁ (fb (n + 1))) s' := fun h' =>
    hwords (by rw [sc.succ n hn, show fb n + bl n = j + 3 + 1 by omega]; exact h')
  rw [troundG3_eq bl fb n e0, ← hj]
  simp only [drH3_eq, List.foldl_append] at hfin
  rcases sc.cases n hn with e4 | e3 | e0'
  rotate_left 2
  · exact absurd e0' e0
  · -- Four blocks: one after each half.
    have ej : fb n = j := by omega
    rw [ite_eq_left e4]
    refine WP.block_append (WP.mono (seg_tw3 (trH3_ok 0) acc_gpr tw) fun t₁ h₁ => ?_)
    rw [ej] at h₁
    refine WP.block_append (WP.mono (piece_tw3 hk hrsi hin (by omega) h₁) fun t₂ h₂ => ?_)
    refine WP.block_append (WP.mono (seg_tw3 (trH3_ok 1) acc_gpr h₂) fun t₃ h₃ => ?_)
    refine WP.block_append (WP.mono (piece_tw3 hk hrsi hin (by omega) h₃) fun t₄ h₄ => ?_)
    refine WP.block_append (WP.mono (seg_tw3 (trH3_ok 2) acc_gpr h₄) fun t₅ h₅ => ?_)
    refine WP.block_append (WP.mono (seg_tw3 (trH3_ok 3) acc_gpr h₅) fun t₆ h₆ => ?_)
    refine WP.block_append (WP.mono (piece_tw3 hk hrsi hin (by omega) h₆) fun t₇ h₇ => ?_)
    refine WP.block_append (WP.mono (seg_tw3 (trH3_ok 4) acc_gpr h₇) fun t₈ h₈ => ?_)
    refine WP.block_append (WP.mono (piece_tw3 hk hrsi hin (by omega) h₈) fun t₉ h₉ => ?_)
    exact WP.mono (seg_tw3 (trH3_ok 5) acc_gpr h₉) fun _ h' => hfin h'
  · -- Three blocks: none after the first half.
    have ej : fb n = j + 1 := by omega
    rw [ite_eq_right (by omega), List.nil_append]
    refine WP.block_append (WP.mono (seg_tw3 (trH3_ok 0) acc_gpr tw) fun t₁ h₁ => ?_)
    rw [ej] at h₁
    refine WP.block_append (WP.mono (seg_tw3 (trH3_ok 1) acc_gpr h₁) fun t₃ h₃ => ?_)
    refine WP.block_append (WP.mono (piece_tw3 hk hrsi hin (by omega) h₃) fun t₄ h₄ => ?_)
    refine WP.block_append (WP.mono (seg_tw3 (trH3_ok 2) acc_gpr h₄) fun t₅ h₅ => ?_)
    refine WP.block_append (WP.mono (seg_tw3 (trH3_ok 3) acc_gpr h₅) fun t₆ h₆ => ?_)
    refine WP.block_append (WP.mono (piece_tw3 hk hrsi hin (by omega) h₆) fun t₇ h₇ => ?_)
    refine WP.block_append (WP.mono (seg_tw3 (trH3_ok 4) acc_gpr h₇) fun t₈ h₈ => ?_)
    refine WP.block_append (WP.mono (piece_tw3 hk hrsi hin (by omega) h₈) fun t₉ h₉ => ?_)
    exact WP.mono (seg_tw3 (trH3_ok 5) acc_gpr h₉) fun _ h' => hfin h'

end

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch
