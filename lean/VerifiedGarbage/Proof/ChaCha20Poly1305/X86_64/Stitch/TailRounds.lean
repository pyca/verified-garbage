import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Chunk
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.Rounds

/-!
# ChaCha20 and Poly1305 together (x86-64): the tail's rounds

`Stitch.trounds`: `Avx2Tail`'s double rounds on one or two sets of two
blocks, absorbing the 32 blocks at `rsi` between their halves. A double
round is six parts (`trH`), each a list of `Avx2Tail`'s instructions of the
rounds (`HI`), which together are the double round on the words
(`Avx2Tail.block_ok`); the blocks of Poly1305 between them write only
Poly1305's registers (`absorbRegs`) and no vector register or memory, and
the parts write only vector registers, so they compose under an invariant
of both (`TB`), as in `Chunk.lean`.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Proof.ChaCha20.X86_64.Avx2Tail (HY YM HB ymmOf hiOk block_ok hy_wordsOf hb_of blk_wordsOf wordsOf)
open VG.Proof.ChaCha20.X86_64.Avx512Tail (HI W hstep halfH rotH half2H colsH diagsH cols2H diags2H
  dr1_words dr2_words)
open VG.Proof.Poly1305.X86_64 (Keeps absorbRegs)
open VG.Proof.ChaCha20 (CState)
open VG.Spec.ChaCha20 (innerBlock)
open VG.Spec.Poly1305 (bytesAt)
open VG.Proof.Poly1305 (absorbAll)

/-- The six parts of a double round on one set or two: the halves of the
column round, the rotations of the rows, the halves of the diagonal round
and the rotations back. -/
def trH (two : Bool) : Nat → List HI
  | 0 => if two then half2H 16 12 else halfH .xmm0 .xmm1 .xmm2 .xmm3 16 12
  | 1 => if two then half2H 8 7 else halfH .xmm0 .xmm1 .xmm2 .xmm3 8 7
  | 2 => if two then rotH .xmm1 .xmm2 .xmm3 0x39 0x4e 0x93 ++ rotH .xmm5 .xmm6 .xmm7 0x39 0x4e 0x93
    else rotH .xmm1 .xmm2 .xmm3 0x39 0x4e 0x93
  | 3 => if two then half2H 16 12 else halfH .xmm0 .xmm1 .xmm2 .xmm3 16 12
  | 4 => if two then half2H 8 7 else halfH .xmm0 .xmm1 .xmm2 .xmm3 8 7
  | _ => if two then rotH .xmm1 .xmm2 .xmm3 0x93 0x4e 0x39 ++ rotH .xmm5 .xmm6 .xmm7 0x93 0x4e 0x39
    else rotH .xmm1 .xmm2 .xmm3 0x93 0x4e 0x39

/-- A double round on one set or two. -/
def drH (two : Bool) : List HI := if two then cols2H ++ diags2H else colsH ++ diagsH

theorem drH_eq (two : Bool) :
    drH two = trH two 0 ++ trH two 1 ++ trH two 2 ++ trH two 3 ++ trH two 4 ++ trH two 5 := by
  cases two <;> simp only [drH, trH, colsH, diagsH, cols2H, diags2H, Bool.false_eq_true, ite_false, ite_true,
    List.append_assoc]

theorem trH_ok (two : Bool) (i : Nat) : (trH two i).all hiOk = true := by
  unfold trH; cases two <;> split <;> decide

theorem half_eq (two : Bool) :
    (if two then Impl.ChaCha20.X86_64.Avx2Tail.half2 else Impl.ChaCha20.X86_64.Avx2Tail.half1) .xmm8 12 =
      (trH two 0).flatMap ymmOf ∧
    (if two then Impl.ChaCha20.X86_64.Avx2Tail.half2 else Impl.ChaCha20.X86_64.Avx2Tail.half1) .xmm9 7 =
      (trH two 1).flatMap ymmOf ∧
    (if two then Impl.ChaCha20.X86_64.Avx2Tail.rot2 else Impl.ChaCha20.X86_64.Avx2Tail.rot1) 0x39 0x4e 0x93 =
      (trH two 2).flatMap ymmOf ∧
    (if two then Impl.ChaCha20.X86_64.Avx2Tail.rot2 else Impl.ChaCha20.X86_64.Avx2Tail.rot1) 0x93 0x4e 0x39 =
      (trH two 5).flatMap ymmOf := by
  cases two <;> decide +kernel

/-- A double round with the blocks between its parts. -/
theorem tround_eq (two : Bool) (n : Nat) :
    tround two n = (trH two 0).flatMap ymmOf ++
      ((if blocks n = 4 then piece (firstBlock n + blocks n - 4) else []) ++
      ((trH two 1).flatMap ymmOf ++ (piece (firstBlock n + blocks n - 4 + 1) ++
      ((trH two 2).flatMap ymmOf ++ ((trH two 3).flatMap ymmOf ++ (piece (firstBlock n + blocks n - 4 + 2) ++
      ((trH two 4).flatMap ymmOf ++ (piece (firstBlock n + blocks n - 4 + 3) ++
      (trH two 5).flatMap ymmOf)))))))) := by
  obtain ⟨e0, e1, e2, e5⟩ := half_eq two
  have e3 : trH two 3 = trH two 0 := by cases two <;> rfl
  have e4 : trH two 4 = trH two 1 := by cases two <;> rfl
  simp only [tround, e0, e1, e2, e5, e3, e4, List.append_assoc]

/-- During the tail's rounds: the states `vs` of the `S` sets in the vector
registers, the masks, the memory, the permissions and the registers but
Poly1305's as in `s₁`, and Poly1305's satisfying `Q`. -/
structure TB (s₁ : State) (S : Nat) (vs : Nat → CState) (Q : State → Prop) (s : State) : Prop where
  hb : HB S vs s
  ym : YM s
  mem : s.mem = s₁.mem
  gpr : ∀ r, r ∉ absorbRegs → s.gpr r = s₁.gpr r
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  poly : Q s

/-- As `TB`, with the words of the vector registers `ws`. -/
structure TW (s₁ : State) (ws : Nat → W) (Q : State → Prop) (s : State) : Prop where
  hy : HY ws s
  ym : YM s
  mem : s.mem = s₁.mem
  gpr : ∀ r, r ∉ absorbRegs → s.gpr r = s₁.gpr r
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  poly : Q s

section
variable {s₁ : State}

/-- A part of the double round. -/
theorem seg_tw {is : List HI} (hok : is.all hiOk = true) {ws : Nat → W} {Q : State → Prop}
    (hQ : ∀ s s' : State, s'.gpr = s.gpr → Q s → Q s') {s : State} (h : TW s₁ ws Q s) :
    WP isa (.block (is.flatMap ymmOf)) s (TW s₁ (fun l => is.foldl hstep (ws l)) Q) :=
  WP.mono (block_ok is hok h.hy h.ym) fun s' ⟨hy, ym, f⟩ =>
    ⟨hy, ym, f.mem.trans h.mem, fun r hr => by rw [f.gpr, h.gpr r hr], f.rd.trans h.rd, f.wr.trans h.wr,
      hQ s s' f.gpr h.poly⟩

/-- Code that keeps the vector registers and Poly1305's frame keeps `TW`. -/
theorem TW.piece {ws : Nat → W} {Q Q' : State → Prop} {s s' : State} (h : TW s₁ ws Q s) (hq : Q' s')
    (k : Keeps absorbRegs s s') (hx : s'.xmm = s.xmm) (hy : s'.ymmHi = s.ymmHi) : TW s₁ ws Q' s' :=
  ⟨fun r l q hr hl hq' => by simpa only [State.lane, hx, hy] using h.hy r l q hr hl hq',
    fun l => by simpa only [State.lane, hx, hy] using h.ym l, by rw [k.2.1, h.mem],
    fun r hr => by rw [k.1 r hr, h.gpr r hr], by rw [k.2.2.1, h.rd], by rw [k.2.2.2, h.wr], hq⟩

variable {q : Addr} {R0 R1 : BitVec 64} {X : Nat} (hk : Key R0 R1) (hrsi : s₁.gpr .rsi = q)
  (hin : ∀ off n, off + n ≤ 512 → InRegions (s₁.rd ++ s₁.wr) (q + BitVec.ofNat 64 off) n)
include hk hrsi hin

/-- Block `j` of the 512 bytes at `q`. -/
theorem piece_tw {j : Nat} (hj : j < 32) {ws : Nat → W} {s : State} (h : TW s₁ ws (AccTo q R0 R1 X s₁ j) s) :
    WP isa (.block (piece j)) s (TW s₁ ws (AccTo q R0 R1 X s₁ (j + 1))) := by
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

/-- A double round on `S` sets (`S` 1 or 2, `two` whether 2), absorbing its
blocks. -/
theorem tround_ok {two : Bool} {S : Nat} (hS : S = if two then 2 else 1) {n : Nat} (hn : n < 10)
    {vs : Nat → CState} {s : State} (h : TB s₁ S vs (AccTo q R0 R1 X s₁ (firstBlock n)) s) :
    WP isa (.block (tround two n)) s
      (TB s₁ S (fun j => innerBlock (vs j)) (AccTo q R0 R1 X s₁ (firstBlock (n + 1)))) := by
  have hb32 : firstBlock n + blocks n ≤ 32 := by rw [← firstBlock_succ]; unfold firstBlock; split <;> omega
  have hb34 : blocks n = 4 ∨ blocks n = 3 := by unfold blocks; split <;> simp
  have hfb : 4 ≤ firstBlock n + blocks n := by unfold firstBlock blocks; split <;> omega
  -- The parts, as steps of `TW`.
  have tw : TW s₁ (wordsOf s) (AccTo q R0 R1 X s₁ (firstBlock n)) s :=
    ⟨hy_wordsOf s, h.ym, h.mem, h.gpr, h.rd, h.wr, h.poly⟩
  obtain ⟨j, hj⟩ : ∃ j, j = firstBlock n + blocks n - 4 := ⟨_, rfl⟩
  have hfin : ∀ {s' : State}, TW s₁ (fun l => (drH two).foldl hstep (wordsOf s l))
      (AccTo q R0 R1 X s₁ (j + 3 + 1)) s' →
      TB s₁ S (fun j => innerBlock (vs j)) (AccTo q R0 R1 X s₁ (firstBlock (n + 1))) s' := by
    intro s' h'
    refine ⟨hb_of h'.hy (fun k hk l hl => ?_) (by cases two <;> simp_all), h'.ym, h'.mem, h'.gpr, h'.rd, h'.wr,
      by rw [firstBlock_succ, show firstBlock n + blocks n = j + 3 + 1 by omega]; exact h'.poly⟩
    cases two
    · simp only [Bool.false_eq_true, ite_false] at hS; subst hS
      obtain rfl : k = 0 := by omega
      simp only [drH, Bool.false_eq_true, ite_false]
      rw [dr1_words, blk_wordsOf h.hb hk hl]
    · simp only [ite_true] at hS; subst hS
      simp only [drH, ite_true]
      rw [dr2_words _ hk, blk_wordsOf h.hb hk hl]
  rw [tround_eq, ← hj]
  simp only [drH_eq, List.foldl_append] at hfin
  rcases hb34 with e4 | e3
  · -- Four blocks: one after each half.
    have ej : firstBlock n = j := by omega
    rw [ite_eq_left e4]
    refine WP.block_append (WP.mono (seg_tw (trH_ok two 0) acc_gpr tw) fun t₁ h₁ => ?_)
    rw [ej] at h₁
    refine WP.block_append (WP.mono (piece_tw hk hrsi hin (by omega) h₁) fun t₂ h₂ => ?_)
    refine WP.block_append (WP.mono (seg_tw (trH_ok two 1) acc_gpr h₂) fun t₃ h₃ => ?_)
    refine WP.block_append (WP.mono (piece_tw hk hrsi hin (by omega) h₃) fun t₄ h₄ => ?_)
    refine WP.block_append (WP.mono (seg_tw (trH_ok two 2) acc_gpr h₄) fun t₅ h₅ => ?_)
    refine WP.block_append (WP.mono (seg_tw (trH_ok two 3) acc_gpr h₅) fun t₆ h₆ => ?_)
    refine WP.block_append (WP.mono (piece_tw hk hrsi hin (by omega) h₆) fun t₇ h₇ => ?_)
    refine WP.block_append (WP.mono (seg_tw (trH_ok two 4) acc_gpr h₇) fun t₈ h₈ => ?_)
    refine WP.block_append (WP.mono (piece_tw hk hrsi hin (by omega) h₈) fun t₉ h₉ => ?_)
    exact WP.mono (seg_tw (trH_ok two 5) acc_gpr h₉) fun _ h' => hfin h'
  · -- Three blocks: none after the first half.
    have ej : firstBlock n = j + 1 := by omega
    rw [ite_eq_right (by omega), List.nil_append]
    refine WP.block_append (WP.mono (seg_tw (trH_ok two 0) acc_gpr tw) fun t₁ h₁ => ?_)
    rw [ej] at h₁
    refine WP.block_append (WP.mono (seg_tw (trH_ok two 1) acc_gpr h₁) fun t₃ h₃ => ?_)
    refine WP.block_append (WP.mono (piece_tw hk hrsi hin (by omega) h₃) fun t₄ h₄ => ?_)
    refine WP.block_append (WP.mono (seg_tw (trH_ok two 2) acc_gpr h₄) fun t₅ h₅ => ?_)
    refine WP.block_append (WP.mono (seg_tw (trH_ok two 3) acc_gpr h₅) fun t₆ h₆ => ?_)
    refine WP.block_append (WP.mono (piece_tw hk hrsi hin (by omega) h₆) fun t₇ h₇ => ?_)
    refine WP.block_append (WP.mono (seg_tw (trH_ok two 4) acc_gpr h₇) fun t₈ h₈ => ?_)
    refine WP.block_append (WP.mono (piece_tw hk hrsi hin (by omega) h₈) fun t₉ h₉ => ?_)
    exact WP.mono (seg_tw (trH_ok two 5) acc_gpr h₉) fun _ h' => hfin h'

/-- The ten double rounds, absorbing the 32 blocks. -/
theorem trounds_ok {two : Bool} {S : Nat} (hS : S = if two then 2 else 1) {vs : Nat → CState}
    (h : TB s₁ S vs (AccTo q R0 R1 X s₁ 0) s₁) :
    ∀ n, n ≤ 10 → WP isa (trounds two n) s₁
      (TB s₁ S (fun j => Nat.repeat innerBlock n (vs j)) (AccTo q R0 R1 X s₁ (firstBlock n)))
  | 0, _ => WP.block_nil h
  | n + 1, hn => WP.seq (WP.mono (trounds_ok hS h n (by omega)) fun _ h' => tround_ok hk hrsi hin hS (by omega) h')

end

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch
