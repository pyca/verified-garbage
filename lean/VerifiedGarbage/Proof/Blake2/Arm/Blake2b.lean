import VerifiedGarbage.Proof.Sha512.Arm.Compress
import VerifiedGarbage.Proof.Blake2.Scratch
import VerifiedGarbage.Impl.Blake2.Arm.CompressB
import VerifiedGarbage.Proof.Blake2.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Blake2.Contract
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Blake2.Arm.Stream.Verified
import VerifiedGarbage.Impl.Blake2.Arm.Stream
import VerifiedGarbage.Proof.Framework.Arm.StackScratch

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.Arm.BlockB`. -/
section

section

/-!
# BLAKE2b on ARMv7: the rounds

Weakest-precondition rules for the 64-bit operations `G` uses on pairs of
32-bit registers (exclusive or and rotations; loads, stores and additions are
SHA-512's, `Proof/Sha512/Arm/Rounds.lean`), in continuation-passing style;
`G`, executed once for any offsets of its words and message words (`wp_g`);
and the rounds on the work vector in `scratch[0, 128)`.
-/

namespace VG.Proof.Blake2.ArmB

open VG VG.Arm
open VG.Impl.Sha512.Arm (lo hi ld st add64)
open VG.Impl.Blake2.Arm.B (xor64 rotr rotr' g gAt round rounds)
open VG.Proof.Sha512.Arm (Only Pair rd64 write64 A Reg64 Wrote wp_st wp_add64 wp_eor mem_rd lo_xor hi_xor
  lo_rotr hi_rotr lo_rotr' hi_rotr' lo_rd64 hi_rd64 eq_of_lo_hi rd64_write64_self rd64_write64_ne
  frame_write64 rd64_frame)
open VG.Proof.MdStream.Arm (Upd Mupd wp_mov wp_ldr op2_reg op2_lsr op2_lsl)
open VG.Spec.Blake2 (Work Block)

/-! ## Rotations by 32 -/

theorem lo_rotr32 (x : BitVec 64) : lo (x.rotateRight 32) = hi x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [lo, Impl.Sha512.Arm.hi, BitVec.getLsbD_extractLsb', BitVec.getLsbD_rotateRight,
    Nat.zero_add, show 32 % 64 = 32 from rfl, show 64 - 32 = 32 from rfl, hi, decide_true,
    Bool.true_and, ite_true]

theorem hi_rotr32 (x : BitVec 64) : hi (x.rotateRight 32) = lo x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [lo, Impl.Sha512.Arm.hi, BitVec.getLsbD_extractLsb', BitVec.getLsbD_rotateRight,
    Nat.zero_add, show 32 % 64 = 32 from rfl, show 64 - 32 = 32 from rfl, hi, decide_true,
    Bool.true_and, show ¬ 32 + i < 32 by omega, show 32 + i < 64 by omega, ite_false,
    Nat.add_sub_cancel_left]

/-- A word rotated by 32 is its halves swapped. -/
theorem pair_swap {s : VG.Arm.State} {l h : Reg} {x : BitVec 64} (p : Pair s l h x) :
    Pair s h l (x.rotateRight 32) :=
  ⟨by rw [VG.Proof.Blake2.ArmB.lo_rotr32]; exact p.2, by rw [VG.Proof.Blake2.ArmB.hi_rotr32]; exact p.1⟩

/-! ## The 64-bit operations -/

/-- The registers a region of 64-bit words can be read through. -/
def Rd64 (rs : List Region) (B : BitVec 32) (N : Nat) : Prop :=
  ∀ o, o + 8 ≤ N → InRegions rs (A B o) 4 ∧ InRegions rs (A B (o + 4)) 4

theorem Reg64.rd {wr : List Region} {B : BitVec 32} {N : Nat} (rd : List Region) (h : Reg64 wr B N) :
    VG.Proof.Blake2.ArmB.Rd64 (rd ++ wr) B N :=
  fun o ho => ⟨mem_rd' (h o ho).1, mem_rd' (h o ho).2⟩
where
  mem_rd' {a : Addr} {n : Nat} : InRegions wr a n → InRegions (rd ++ wr) a n :=
    fun ⟨r, hr, hc⟩ => ⟨r, List.mem_append_right _ hr, hc⟩

section
variable {rest : List Instr} {s : VG.Arm.State} {Q : VG.Arm.State → Prop}

/-- A load of a 64-bit word from readable memory, whose contents are `m`. -/
theorem wp_ld64 {l h b : Reg} {B : BitVec 32} {off : Nat} {m : Mem} (hlb : l ≠ b) (hlh : l ≠ h)
    (ho : off + 4 < 4096) (hb : s.gpr b = B) (hm : s.mem = m)
    (hi : InRegions (s.rd ++ s.wr) (A B off) 4) (hi' : InRegions (s.rd ++ s.wr) (A B (off + 4)) 4)
    (k : ∀ s', Only [l, h] s s' → Pair s' l h (rd64 m B off) → WP isa (.block rest) s' Q) :
    WP isa (.block (ld l h b off ++ rest)) s Q := by
  subst hm
  simp only [ld, List.cons_append, List.nil_append]
  refine wp_ldr (by omega) (by rw [hb]) hi fun s₁ u₁ => ?_
  refine wp_ldr ho (by rw [u₁.other b (Ne.symm hlb), hb]) (by rw [u₁.rd, u₁.wr]; exact hi')
    fun s₂ u₂ => k s₂ ((Only.of_upd u₁).trans (Only.of_upd u₂)) ⟨?_, ?_⟩
  · rw [u₂.other l hlh, u₁.gpr, lo_rd64]
  · rw [u₂.gpr, u₁.mem, hi_rd64]

theorem wp_xor64 {dl dh l h : Reg} {x y : BitVec 64} (h₁ : dl ≠ dh) (h₂ : dl ≠ h)
    (px : Pair s dl dh x) (py : Pair s l h y)
    (k : ∀ s', Only [dl, dh] s s' → Pair s' dl dh (x ^^^ y) → WP isa (.block rest) s' Q) :
    WP isa (.block (xor64 dl dh l h ++ rest)) s Q := by
  simp only [xor64, List.cons_append, List.nil_append]
  refine VG.Proof.Sha512.Arm.wp_eor (op2_reg _ _) fun s₁ u₁ => ?_
  refine VG.Proof.Sha512.Arm.wp_eor (op2_reg _ _) fun s₂ u₂ => k s₂ ((Only.of_upd u₁).trans (Only.of_upd u₂)) ⟨?_, ?_⟩
  · rw [u₂.other dl h₁, u₁.gpr, px.1, py.1, lo_xor]
  · rw [u₂.gpr, u₁.other dh (Ne.symm h₁), u₁.other h (Ne.symm h₂), px.2, py.2, hi_xor]

theorem wp_rotr {n : Nat} {t l h : Reg} {x : BitVec 64} (h0 : 0 < n) (hn : n < 32)
    (htl : t ≠ l) (hth : t ≠ h) (hlh : l ≠ h) (px : Pair s l h x)
    (k : ∀ s', Only [t, h] s s' → Pair s' t h (x.rotateRight n) → WP isa (.block rest) s' Q) :
    WP isa (.block (rotr n t l h ++ rest)) s Q := by
  simp only [rotr, List.cons_append, List.nil_append]
  refine wp_mov (op2_lsr ⟨h0, by omega⟩) fun s₁ u₁ => ?_
  refine VG.Proof.Sha512.Arm.wp_eor (op2_lsl ⟨by omega, by omega⟩) fun s₂ u₂ => ?_
  refine wp_mov (op2_lsr ⟨h0, by omega⟩) fun s₃ u₃ => ?_
  refine VG.Proof.Sha512.Arm.wp_eor (op2_lsl ⟨by omega, by omega⟩) fun s₄ u₄ =>
    k s₄ (((((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans
      (Only.of_upd u₄)).mono (by simp)) ⟨?_, ?_⟩
  · rw [u₄.other t hth, u₃.other t hth, u₂.gpr, u₁.gpr, u₁.other h (Ne.symm hth), px.1, px.2,
      lo_rotr x h0 hn]
  · rw [u₄.gpr, u₃.gpr, u₃.other l hlh, u₂.other h (Ne.symm hth), u₂.other l (Ne.symm htl),
      u₁.other h (Ne.symm hth), u₁.other l (Ne.symm htl), px.1, px.2, hi_rotr x h0 hn]

theorem wp_rotr' {n : Nat} {t l h : Reg} {x : BitVec 64} (h0 : 32 < n) (hn : n < 64)
    (htl : t ≠ l) (hth : t ≠ h) (hlh : l ≠ h) (px : Pair s l h x)
    (k : ∀ s', Only [t, h] s s' → Pair s' t h (x.rotateRight n) → WP isa (.block rest) s' Q) :
    WP isa (.block (rotr' n t l h ++ rest)) s Q := by
  simp only [rotr', List.cons_append, List.nil_append]
  refine wp_mov (op2_lsr ⟨by omega, by omega⟩) fun s₁ u₁ => ?_
  refine VG.Proof.Sha512.Arm.wp_eor (op2_lsl ⟨by omega, by omega⟩) fun s₂ u₂ => ?_
  refine wp_mov (op2_lsl ⟨by omega, by omega⟩) fun s₃ u₃ => ?_
  refine VG.Proof.Sha512.Arm.wp_eor (op2_lsr ⟨by omega, by omega⟩) fun s₄ u₄ =>
    k s₄ (((((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans
      (Only.of_upd u₄)).mono (by simp)) ⟨?_, ?_⟩
  · rw [u₄.other t hth, u₃.other t hth, u₂.gpr, u₁.gpr, u₁.other l (Ne.symm htl), px.1, px.2,
      lo_rotr' x h0 hn]
  · rw [u₄.gpr, u₃.gpr, u₃.other l hlh, u₂.other h (Ne.symm hth), u₂.other l (Ne.symm htl),
      u₁.other h (Ne.symm hth), u₁.other l (Ne.symm htl), px.1, px.2, hi_rotr' x h0 hn,
      BitVec.xor_comm]

end

/-! ## One `G` -/

/-- The registers `G` writes. -/
def gRegs : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]

/-- The memory after `G` on the words at `V + a`, …, `V + d`, with the message
words at `Bk + x` and `Bk + y`. -/
def gMem (m : Mem) (V Bk : BitVec 32) (a b c d x y : Nat) : Mem :=
  let r := VG.Proof.Blake2.mix Spec.Blake2.b (rd64 m V a) (rd64 m V b) (rd64 m V c) (rd64 m V d) (rd64 m Bk x)
    (rd64 m Bk y)
  write64 (write64 (write64 (write64 m V a r.1) V b r.2.1) V c r.2.2.1) V d r.2.2.2

section
variable {rest : List Instr} {s : VG.Arm.State} {Q : VG.Arm.State → Prop}

theorem wp_g {a b c d x y : Nat} {V Bk : BitVec 32}
    (ha : a + 8 ≤ 128) (hb : b + 8 ≤ 128) (hc : c + 8 ≤ 128) (hd : d + 8 ≤ 128)
    (hx : x + 8 ≤ 128) (hy : y + 8 ≤ 128)
    (hRV : Reg64 s.wr V 128) (hRB : VG.Proof.Blake2.ArmB.Rd64 (s.rd ++ s.wr) Bk 128) (h3 : s.gpr .r3 = V)
    (h1 : s.gpr .r1 = Bk)
    (K : ∀ s', Wrote VG.Proof.Blake2.ArmB.gRegs s s' (VG.Proof.Blake2.ArmB.gMem s.mem V Bk a b c d x y) → WP isa (.block rest) s' Q) :
    WP isa (.block (g a b c d x y ++ rest)) s Q := by
  unfold g
  simp only [List.append_assoc]
  have iV : ∀ o, o + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (A V o) 4 ∧
      InRegions (s.rd ++ s.wr) (A V (o + 4)) 4 := Reg64.rd s.rd hRV
  -- Load the four words.
  refine VG.Proof.Blake2.ArmB.wp_ld64 (by decide) (by decide) (by omega) h3 rfl (iV a ha).1 (iV a ha).2
    fun s₁ o₁ pa => ?_
  refine VG.Proof.Blake2.ArmB.wp_ld64 (by decide) (by decide) (by omega) (by rw [o₁.gpr _ (by decide), h3]) o₁.mem
    (by rw [o₁.rd, o₁.wr]; exact (iV b hb).1) (by rw [o₁.rd, o₁.wr]; exact (iV b hb).2)
    fun s₂ o₂ pb => ?_
  have O₂ := o₁.trans o₂
  refine VG.Proof.Blake2.ArmB.wp_ld64 (by decide) (by decide) (by omega) (by rw [O₂.gpr _ (by decide), h3]) O₂.mem
    (by rw [O₂.rd, O₂.wr]; exact (iV c hc).1) (by rw [O₂.rd, O₂.wr]; exact (iV c hc).2)
    fun s₃ o₃ pc => ?_
  have O₃ := O₂.trans o₃
  refine VG.Proof.Blake2.ArmB.wp_ld64 (by decide) (by decide) (by omega) (by rw [O₃.gpr _ (by decide), h3]) O₃.mem
    (by rw [O₃.rd, O₃.wr]; exact (iV d hd).1) (by rw [O₃.rd, O₃.wr]; exact (iV d hd).2)
    fun s₄ o₄ pd => ?_
  have O₄ := O₃.trans o₄
  -- a := a + b + m[x]
  refine wp_add64 (by decide) (by decide)
    (pa.of_only ((o₂.trans o₃).trans o₄) (by decide) (by decide))
    (pb.of_only (o₃.trans o₄) (by decide) (by decide)) fun s₅ o₅ p₅ => ?_
  have O₅ := O₄.trans o₅
  refine VG.Proof.Blake2.ArmB.wp_ld64 (by decide) (by decide) (by omega) (by rw [O₅.gpr _ (by decide), h1]) O₅.mem
    (by rw [O₅.rd, O₅.wr]; exact (hRB x hx).1) (by rw [O₅.rd, O₅.wr]; exact (hRB x hx).2)
    fun s₆ o₆ pX => ?_
  refine wp_add64 (by decide) (by decide) (p₅.of_only o₆ (by decide) (by decide)) pX
    fun s₇ o₇ p₇ => ?_
  -- d := (d ⊕ a) >>> 32
  refine VG.Proof.Blake2.ArmB.wp_xor64 (by decide) (by decide)
    (pd.of_only (((o₅.trans o₆).trans o₇)) (by decide) (by decide)) p₇ fun s₈ o₈ p₈ => ?_
  have pd₁ := VG.Proof.Blake2.ArmB.pair_swap p₈
  -- c := c + d
  refine wp_add64 (by decide) (by decide)
    (pc.of_only ((((o₄.trans o₅).trans o₆).trans o₇).trans o₈) (by decide) (by decide)) pd₁
    fun s₉ o₉ pc₁ => ?_
  -- b := (b ⊕ c) >>> 24
  refine VG.Proof.Blake2.ArmB.wp_xor64 (by decide) (by decide)
    (pb.of_only ((((((o₃.trans o₄).trans o₅).trans o₆).trans o₇).trans o₈).trans o₉) (by decide)
      (by decide)) pc₁ fun s₁₀ o₁₀ p₁₀ => ?_
  refine VG.Proof.Blake2.ArmB.wp_rotr (n := 24) (by decide) (by decide) (by decide) (by decide) (by decide) p₁₀
    fun s₁₁ o₁₁ pb₁ => ?_
  have O₁₁ := (((((((O₅.trans o₆).trans o₇).trans o₈).trans o₉).trans o₁₀).trans o₁₁))
  -- a := a + b + m[y]
  refine VG.Proof.Blake2.ArmB.wp_ld64 (by decide) (by decide) (by omega) (by rw [O₁₁.gpr _ (by decide), h1]) O₁₁.mem
    (by rw [O₁₁.rd, O₁₁.wr]; exact (hRB y hy).1) (by rw [O₁₁.rd, O₁₁.wr]; exact (hRB y hy).2)
    fun s₁₂ o₁₂ pY => ?_
  refine wp_add64 (by decide) (by decide)
    (p₇.of_only ((((o₈.trans o₉).trans o₁₀).trans o₁₁).trans o₁₂) (by decide) (by decide))
    (pb₁.of_only o₁₂ (by decide) (by decide)) fun s₁₃ o₁₃ p₁₃ => ?_
  refine wp_add64 (by decide) (by decide) p₁₃ (pY.of_only o₁₃ (by decide) (by decide))
    fun s₁₄ o₁₄ pa₂ => ?_
  -- d := (d ⊕ a) >>> 16
  refine VG.Proof.Blake2.ArmB.wp_xor64 (by decide) (by decide)
    (pd₁.of_only (((((o₉.trans o₁₀).trans o₁₁).trans o₁₂).trans o₁₃).trans o₁₄) (by decide)
      (by decide)) pa₂ fun s₁₅ o₁₅ p₁₅ => ?_
  refine VG.Proof.Blake2.ArmB.wp_rotr (n := 16) (by decide) (by decide) (by decide) (by decide) (by decide) p₁₅
    fun s₁₆ o₁₆ pd₂ => ?_
  -- c := c + d
  refine wp_add64 (by decide) (by decide)
    (pc₁.of_only ((((((o₁₀.trans o₁₁).trans o₁₂).trans o₁₃).trans o₁₄).trans o₁₅).trans o₁₆)
      (by decide) (by decide)) pd₂ fun s₁₇ o₁₇ pc₂ => ?_
  -- b := (b ⊕ c) >>> 63
  refine VG.Proof.Blake2.ArmB.wp_xor64 (by decide) (by decide)
    (pb₁.of_only ((((((o₁₂.trans o₁₃).trans o₁₄).trans o₁₅).trans o₁₆).trans o₁₇)) (by decide)
      (by decide)) pc₂ fun s₁₈ o₁₈ p₁₈ => ?_
  refine VG.Proof.Blake2.ArmB.wp_rotr' (n := 63) (by decide) (by decide) (by decide) (by decide) (by decide) p₁₈
    fun s₁₉ o₁₉ pb₂ => ?_
  have O₁₉ := (((((((((O₁₁.trans o₁₂).trans o₁₃).trans o₁₄).trans o₁₅).trans o₁₆).trans o₁₇).trans
    o₁₈).trans o₁₉))
  have pa₂' := pa₂.of_only ((((o₁₅.trans o₁₆).trans o₁₇).trans o₁₈).trans o₁₉) (by decide) (by decide)
  have pc₂' := pc₂.of_only (o₁₈.trans o₁₉) (by decide) (by decide)
  have pd₂' := pd₂.of_only ((o₁₇.trans o₁₈).trans o₁₉) (by decide) (by decide)
  -- Store them.
  have w : Reg64 s₁₉.wr V 128 := by rw [O₁₉.wr]; exact hRV
  have r3 : s₁₉.gpr .r3 = V := by rw [O₁₉.gpr _ (by decide), h3]
  refine wp_st (by omega) r3 pa₂' (w a ha).1 (w a ha).2 fun s₂₀ u₂₀ => ?_
  refine wp_st (by omega) (by rw [u₂₀.gpr, r3]) (by rw [Pair, u₂₀.gpr]; exact pb₂)
    (by rw [u₂₀.wr]; exact (w b hb).1) (by rw [u₂₀.wr]; exact (w b hb).2) fun s₂₁ u₂₁ => ?_
  refine wp_st (by omega) (by rw [u₂₁.gpr, u₂₀.gpr, r3]) (by rw [Pair, u₂₁.gpr, u₂₀.gpr]; exact pc₂')
    (by rw [u₂₁.wr, u₂₀.wr]; exact (w c hc).1) (by rw [u₂₁.wr, u₂₀.wr]; exact (w c hc).2)
    fun s₂₂ u₂₂ => ?_
  refine wp_st (by omega) (by rw [u₂₂.gpr, u₂₁.gpr, u₂₀.gpr, r3])
    (by rw [Pair, u₂₂.gpr, u₂₁.gpr, u₂₀.gpr]; exact pd₂')
    (by rw [u₂₂.wr, u₂₁.wr, u₂₀.wr]; exact (w d hd).1)
    (by rw [u₂₂.wr, u₂₁.wr, u₂₀.wr]; exact (w d hd).2) fun s₂₃ u₂₃ => K s₂₃ ⟨fun r hr => ?_, ?_,
      by rw [u₂₃.rd, u₂₂.rd, u₂₁.rd, u₂₀.rd, O₁₉.rd], by rw [u₂₃.wr, u₂₂.wr, u₂₁.wr, u₂₀.wr, O₁₉.wr],
      by rw [u₂₃.sp, u₂₂.sp, u₂₁.sp, u₂₀.sp, O₁₉.sp]⟩
  · rw [u₂₃.gpr, u₂₂.gpr, u₂₁.gpr, u₂₀.gpr]
    exact (O₁₉.mono (by decide)).gpr r hr
  · rw [u₂₃.mem, u₂₂.mem, u₂₁.mem, u₂₀.mem, O₁₉.mem]
    rfl

end

/-! ## The work vector in `scratch` -/

theorem rd64_write64 (m : Mem) {V : BitVec 32} (fit : V.toNat + 128 ≤ 2 ^ 32) {o o' : Nat}
    (x : BitVec 64) (ho : o + 8 ≤ 128) (ho' : o' + 8 ≤ 128) (h8 : o % 8 = 0) (h8' : o' % 8 = 0) :
    rd64 (write64 m V o x) V o' = if o = o' then x else rd64 m V o' := by
  by_cases e : o = o'
  · subst e; simp only [ite_true]; exact rd64_write64_self _ _ (by omega)
  · simp only [e, ite_false]; exact rd64_write64_ne _ _ (by omega) (by omega) (by omega)

/-- What the rounds need of the state `s₀` at their start: the scratch space
at `V` (in `r3`), and the message block `M` at `Bk` (in `r1`). -/
structure RCtx (V Bk : BitVec 32) (M : VG.Spec.Blake2.Block 64) (s₀ : VG.Arm.State) : Prop where
  r3 : s₀.gpr .r3 = V
  r1 : s₀.gpr .r1 = Bk
  fitV : V.toNat + 128 ≤ 2 ^ 32
  fitB : Bk.toNat + 128 ≤ 2 ^ 32
  wV : Reg64 s₀.wr V 128
  rB : VG.Proof.Blake2.ArmB.Rd64 (s₀.rd ++ s₀.wr) Bk 128
  disj : Region.Disjoint ⟨State.addr Bk, 128⟩ ⟨State.addr V, 128⟩
  msg : ∀ j (hj : j < 16), rd64 s₀.mem Bk (8 * j) = M ⟨j, hj⟩

/-- The rounds invariant, relative to the state `s₀` at their start: the work
vector `v` is in `scratch[0, 128)`, and nothing else has changed but the
registers of `G`. -/
structure RI (V : BitVec 32) (s₀ : VG.Arm.State) (v : Work 64) (s : VG.Arm.State) : Prop where
  vars : ∀ k (hk : k < 16), rd64 s.mem V (8 * k) = v[k]
  gpr : ∀ r, r ∉ VG.Proof.Blake2.ArmB.gRegs → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨State.addr V, 128⟩] s₀.mem s.mem

theorem eq_mul8 (p q : Nat) : (8 * p = 8 * q) = (p = q) := propext ⟨fun h => by omega, fun h => by rw [h]⟩

theorem gAt_ok {x y z u : Nat} (hx : x < 16) (hy : y < 16) (hz : z < 16) (hu : u < 16)
    (hq : [x, y, z, u].Nodup) (r i : Nat) {V Bk : BitVec 32} {M : VG.Spec.Blake2.Block 64} {s₀ s : VG.Arm.State}
    {v : Work 64} (c : VG.Proof.Blake2.ArmB.RCtx V Bk M s₀) (h : VG.Proof.Blake2.ArmB.RI V s₀ v s) :
    WP isa (gAt r i x y z u) s (VG.Proof.Blake2.ArmB.RI V s₀ (Spec.Blake2.G Spec.Blake2.b v ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩
      ⟨u, hu⟩ (M (Spec.Blake2.sigmaAt r (2 * i))) (M (Spec.Blake2.sigmaAt r (2 * i + 1))))) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hq
  obtain ⟨⟨nxy, nxz, nxu⟩, ⟨nyz, nyu⟩, nzu, -⟩ := hq
  have sj := (Spec.Blake2.sigmaAt r (2 * i)).isLt
  have sk := (Spec.Blake2.sigmaAt r (2 * i + 1)).isLt
  have fitV := c.fitV
  unfold gAt
  rw [← List.append_nil (g _ _ _ _ _ _)]
  refine VG.Proof.Blake2.ArmB.wp_g (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [h.wr]; exact c.wV) (by rw [h.rd, h.wr]; exact c.rB) (by rw [h.gpr _ (by decide), c.r3])
    (by rw [h.gpr _ (by decide), c.r1]) fun s' w => WP.block_nil ?_
  have hm : ∀ j (hj : j < 16), rd64 s.mem Bk (8 * j) = M ⟨j, hj⟩ := fun j hj => by
    rw [rd64_frame h.frame (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact c.disj)
      c.fitB (by omega)]
    exact c.msg j hj
  refine ⟨fun k hk => ?_, fun q hq => by rw [w.gpr q hq, h.gpr q hq], by rw [w.rd, h.rd],
    by rw [w.wr, h.wr], by rw [w.sp, h.sp], ?_⟩
  · have m8 : ∀ p, (8 * p) % 8 = 0 := fun p => Nat.mul_mod_right 8 p
    rw [w.mem, VG.Proof.Blake2.ArmB.gMem]
    rw [VG.Proof.Blake2.ArmB.rd64_write64 _ fitV _ (by omega) (by omega) (m8 _) (m8 _),
      VG.Proof.Blake2.ArmB.rd64_write64 _ fitV _ (by omega) (by omega) (m8 _) (m8 _),
      VG.Proof.Blake2.ArmB.rd64_write64 _ fitV _ (by omega) (by omega) (m8 _) (m8 _),
      VG.Proof.Blake2.ArmB.rd64_write64 _ fitV _ (by omega) (by omega) (m8 _) (m8 _),
      h.vars x hx, h.vars y hy, h.vars z hz, h.vars u hu, h.vars k hk, hm _ sj, hm _ sk,
      Proof.Blake2.G_get _ v (a := ⟨x, hx⟩) (b := ⟨y, hy⟩) (c := ⟨z, hz⟩) (d := ⟨u, hu⟩) nxy nxz nxu
        nyz nyu nzu _ _ k hk]
    simp only [VG.Proof.Blake2.ArmB.eq_mul8, Fin.getElem_fin]
    by_cases ey : y = k
    · subst ey; simp only [Ne.symm nyu, Ne.symm nyz, ite_true, ite_false]
    by_cases ez : z = k
    · subst ez; simp only [ey, Ne.symm nzu, ite_true, ite_false]
    by_cases eu : u = k
    · subst eu; simp only [ey, ez, ite_true, ite_false]
    by_cases ex : x = k
    · subst ex; simp only [ey, ez, eu, ite_true, ite_false]
    simp only [ey, ez, eu, ex, ite_false]
  · rw [w.mem, VG.Proof.Blake2.ArmB.gMem]
    have m := List.mem_singleton_self (⟨State.addr V, 128⟩ : Region)
    exact frame_write64 (frame_write64 (frame_write64 (frame_write64 h.frame m fitV (by omega) _) m fitV
      (by omega) _) m fitV (by omega) _) m fitV (by omega) _

theorem round_ok (r : Nat) {V Bk : BitVec 32} {M : VG.Spec.Blake2.Block 64} {s₀ s : VG.Arm.State} {v : Work 64}
    (c : VG.Proof.Blake2.ArmB.RCtx V Bk M s₀) (h : VG.Proof.Blake2.ArmB.RI V s₀ v s) :
    WP isa (round r) s (VG.Proof.Blake2.ArmB.RI V s₀ (Spec.Blake2.round Spec.Blake2.b M v r)) := by
  unfold round
  refine WP.seq (WP.mono (VG.Proof.Blake2.ArmB.gAt_ok (x := 0) (y := 4) (z := 8) (u := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) r 0 c h) fun s h => ?_)
  refine WP.seq (WP.mono (VG.Proof.Blake2.ArmB.gAt_ok (x := 1) (y := 5) (z := 9) (u := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) r 1 c h) fun s h => ?_)
  refine WP.seq (WP.mono (VG.Proof.Blake2.ArmB.gAt_ok (x := 2) (y := 6) (z := 10) (u := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) r 2 c h) fun s h => ?_)
  refine WP.seq (WP.mono (VG.Proof.Blake2.ArmB.gAt_ok (x := 3) (y := 7) (z := 11) (u := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) r 3 c h) fun s h => ?_)
  refine WP.seq (WP.mono (VG.Proof.Blake2.ArmB.gAt_ok (x := 0) (y := 5) (z := 10) (u := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) r 4 c h) fun s h => ?_)
  refine WP.seq (WP.mono (VG.Proof.Blake2.ArmB.gAt_ok (x := 1) (y := 6) (z := 11) (u := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) r 5 c h) fun s h => ?_)
  refine WP.seq (WP.mono (VG.Proof.Blake2.ArmB.gAt_ok (x := 2) (y := 7) (z := 8) (u := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) r 6 c h) fun s h => ?_)
  refine WP.mono (VG.Proof.Blake2.ArmB.gAt_ok (x := 3) (y := 4) (z := 9) (u := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) r 7 c h) fun s h => ?_
  exact h

theorem rounds_ok {V Bk : BitVec 32} {M : VG.Spec.Blake2.Block 64} {s₀ : VG.Arm.State} {v : Work 64} (c : VG.Proof.Blake2.ArmB.RCtx V Bk M s₀)
    (hv : ∀ k (hk : k < 16), rd64 s₀.mem V (8 * k) = v[k]) (n : Nat) :
    WP isa (rounds n) s₀ (VG.Proof.Blake2.ArmB.RI V s₀ ((List.range n).foldl (Spec.Blake2.round Spec.Blake2.b M) v)) := by
  induction n with
  | zero => exact WP.block_nil ⟨hv, fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | succ n ih =>
    refine WP.seq (WP.mono ih fun s hs => ?_)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact VG.Proof.Blake2.ArmB.round_ok n c hs

end VG.Proof.Blake2.ArmB

end

/-!
# BLAKE2b on ARMv7: one block

Initializing the work vector in `scratch` (`init_ok`), XORing it into the
state (`fin_ok`), and advancing the counter, the block pointer and the count
(`advance_ok`).
-/

namespace VG.Proof.Blake2.ArmB

open VG VG.Arm
open VG.Impl.Sha512.Arm (lo hi ld st add64 const64)
open VG.Impl.Blake2.Arm.B (xor64 ldH ldIV finH tweak ctrLo ctrHi flagOff zeroOff)
open VG.Proof.Sha512.Arm (Only Pair rd64 write64 A A_eq Reg64 Wrote wp_ld wp_st wp_const64
  rd64_write64_self rd64_write64_ne rd64_write64_disj frame_write64 rd64_frame lo_append hi_append
  hi_append_lo eq_of_lo_hi)
open VG.Spec.Blake2 (Work Block HashValue Params)

/-! ## The work vector of `F` -/

section InitV
variable {w : Nat} (P : VG.Spec.Blake2.Params w)

/-- The work vector at the start of the rounds of `F` (RFC 7693 §3.2). -/
def initV (h : HashValue w) (t : Nat) (f : Bool) : Work w :=
  let v : Work w := h ++ P.IV
  let v := v.set 12 (v[12] ^^^ BitVec.ofNat w t)
  let v := v.set 13 (v[13] ^^^ BitVec.ofNat w (t / 2 ^ w))
  if f then v.set 14 (v[14] ^^^ BitVec.allOnes w) else v

theorem F_eq (h : HashValue w) (m : VG.Spec.Blake2.Block w) (t : Nat) (f : Bool) :
    Spec.Blake2.F P h m t f =
      Vector.ofFn fun i => h[i] ^^^ ((List.range P.r).foldl (Spec.Blake2.round P m) (VG.Proof.Blake2.ArmB.initV P h t f))[i] ^^^
        ((List.range P.r).foldl (Spec.Blake2.round P m) (VG.Proof.Blake2.ArmB.initV P h t f))[i.val + 8] := rfl

/-- The flag word. -/
def flagW (w : Nat) (f : Bool) : BitVec w := if f then BitVec.allOnes w else 0

/-- The word XORed into IV word `k` (`k < 8`): the counter's words and the flag word. -/
def tweakV (t : Nat) (f : Bool) (k : Nat) : BitVec w :=
  if k = 4 then BitVec.ofNat w t else if k = 5 then BitVec.ofNat w (t / 2 ^ w)
  else if k = 6 then VG.Proof.Blake2.ArmB.flagW w f else 0

theorem initV_get (h : HashValue w) (t : Nat) (f : Bool) (k : Nat) (hk : k < 16) :
    (VG.Proof.Blake2.ArmB.initV P h t f)[k] =
      if hk8 : k < 8 then h[k] else P.IV[k - 8] ^^^ VG.Proof.Blake2.ArmB.tweakV t f (k - 8) := by
  unfold VG.Proof.Blake2.ArmB.initV VG.Proof.Blake2.ArmB.tweakV VG.Proof.Blake2.ArmB.flagW
  have ha : ∀ j (hj : j < 16), (h ++ P.IV)[j] = if h8 : j < 8 then h[j] else P.IV[j - 8] :=
    fun j hj => Vector.getElem_append hj
  by_cases e12 : k = 12
  · subst e12; cases f <;> simp [ha]
  by_cases e13 : k = 13
  · subst e13; cases f <;> simp [ha]
  by_cases e14 : k = 14
  · subst e14; cases f <;> simp [ha]
  have e4 : k - 8 ≠ 4 := by omega
  have e5 : k - 8 ≠ 5 := by omega
  have e6 : k - 8 ≠ 6 := by omega
  cases f <;> simp [Ne.symm e12, Ne.symm e13, Ne.symm e14, e4, e5, e6, ha k hk]

end InitV

/-! ## Regions -/

/-- The state's region, the scratch region, and the work vector's part of it. -/
abbrev stR (st : BitVec 32) : Region := ⟨State.addr st, 64⟩
abbrev scrR (scr : BitVec 32) : Region := ⟨State.addr scr, 512⟩
abbrev workR (scr : BitVec 32) : Region := ⟨State.addr scr, 128⟩

/-- What a block needs of its state `s`, with `state = st` (in `r0`) and
`scratch = scr` (in `r3`). -/
structure Ctx (st scr : BitVec 32) (s : VG.Arm.State) : Prop where
  r0 : s.gpr .r0 = st
  r3 : s.gpr .r3 = scr
  fitS : st.toNat + 64 ≤ 2 ^ 32
  fitV : scr.toNat + 512 ≤ 2 ^ 32
  disj : (VG.Proof.Blake2.ArmB.stR st).Disjoint (VG.Proof.Blake2.ArmB.scrR scr)
  wS : Reg64 s.wr st 64
  wV : Reg64 s.wr scr 512

theorem Ctx.of_eq {st scr : BitVec 32} {s s' : VG.Arm.State} (c : VG.Proof.Blake2.ArmB.Ctx st scr s) (h0 : s'.gpr .r0 = s.gpr .r0)
    (h3 : s'.gpr .r3 = s.gpr .r3) (hwr : s'.wr = s.wr) : VG.Proof.Blake2.ArmB.Ctx st scr s' :=
  ⟨h0.trans c.r0, h3.trans c.r3, c.fitS, c.fitV, c.disj, hwr ▸ c.wS, hwr ▸ c.wV⟩

theorem Ctx.disjW {st scr : BitVec 32} {s : VG.Arm.State} (c : VG.Proof.Blake2.ArmB.Ctx st scr s) : (VG.Proof.Blake2.ArmB.stR st).Disjoint (VG.Proof.Blake2.ArmB.workR scr) :=
  c.disj.sub_right (Region.sub_prefix (by omega))

/-- A word of `scratch` above the work vector is unchanged by writes to it. -/
theorem rd64_frame_hi {m m' : Mem} {scr : BitVec 32} (fit : scr.toNat + 512 ≤ 2 ^ 32)
    (hf : Frame [VG.Proof.Blake2.ArmB.workR scr] m m') {o : Nat} (h1 : 128 ≤ o) (h2 : o + 8 ≤ 512) :
    rd64 m' scr o = rd64 m scr o := by
  have hd : ∀ r ∈ [VG.Proof.Blake2.ArmB.workR scr], Region.Disjoint ⟨State.addr scr + BitVec.ofNat 64 128, 384⟩ r := by
    simp only [List.mem_singleton, forall_eq]; exact Offset.disjoint_base _ (by omega) (by omega)
  have c : ∀ d, 128 ≤ d → d + 4 ≤ 512 →
      Region.Contains ⟨State.addr scr + BitVec.ofNat 64 128, 384⟩ (A scr d) (32 / 8) := fun d h h' => by
    rw [A_eq (by omega)]; exact Offset.contains _ h (by omega) (by omega)
  simp only [rd64]
  rw [hf.readW (c o h1 (by omega)) hd (by decide), hf.readW (c (o + 4) (by omega) (by omega)) hd (by decide)]

/-! ## Initializing the work vector -/

structure LdInv (st scr : BitVec 32) (s : VG.Arm.State) (n : Nat) (s' : VG.Arm.State) : Prop where
  gpr : ∀ r, r ∉ [Reg.r4, .r5, .r6, .r7] → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  vars : ∀ k < n, rd64 s'.mem scr (8 * k) = rd64 s.mem st (8 * k)
  frame : Frame [VG.Proof.Blake2.ArmB.workR scr] s.mem s'.mem

theorem ldH_ok {st scr : BitVec 32} {s : VG.Arm.State} (c : VG.Proof.Blake2.ArmB.Ctx st scr s) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap ldH)) s (VG.Proof.Blake2.ArmB.LdInv st scr s n) := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ h => absurd h (by omega),
      Frame.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s₁ h₁ => ?_
    have c₁ := c.of_eq (h₁.gpr _ (by decide)) (h₁.gpr _ (by decide)) h₁.wr
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [ldH, ← List.append_nil (Impl.Sha512.Arm.st .r4 .r5 .r3 (8 * n))]
    refine wp_ld (by decide) (by decide) (by omega) c₁.r0 (c₁.wS _ (by omega)).1
      (c₁.wS _ (by omega)).2 fun s₂ o₂ p₂ => ?_
    refine wp_st (by omega) (by rw [o₂.gpr _ (by decide), c₁.r3]) p₂
      (by rw [o₂.wr]; exact (c₁.wV _ (by omega)).1) (by rw [o₂.wr]; exact (c₁.wV _ (by omega)).2)
      fun s₃ u₃ => WP.block_nil ⟨fun r hr => ?_, by rw [u₃.rd, o₂.rd, h₁.rd],
        by rw [u₃.wr, o₂.wr, h₁.wr], by rw [u₃.sp, o₂.sp, h₁.sp], fun k hk => ?_, ?_⟩
    · rw [u₃.gpr, (o₂.mono (es := [Reg.r4, .r5, .r6, .r7]) (by decide)).gpr r hr, h₁.gpr r hr]
    · have fitV := c.fitV
      rw [u₃.mem]
      by_cases hkn : k = n
      · subst hkn
        rw [rd64_write64_self _ _ (by omega),
          rd64_frame h₁.frame (fun r hr => by simp at hr; subst hr; exact c.disjW) c.fitS (by omega)]
      · rw [rd64_write64_ne (b := scr) (o := 8 * n) (o' := 8 * k) _ _ (by omega) (by omega)
          (by omega), o₂.mem]
        exact h₁.vars k (by omega)
    · rw [u₃.mem, o₂.mem]
      exact frame_write64 (N := 128) (o := 8 * n) h₁.frame (by simp) (by have := c.fitV; omega)
        (by omega) _

theorem tweak_ok (k : Nat) : 128 ≤ tweak k ∧ tweak k + 8 ≤ 512 := by
  unfold tweak ctrLo ctrHi flagOff zeroOff; split_ifs <;> omega

theorem iv_getD {k : Nat} (hk : k < 8) :
    Spec.Blake2.b.IV.toList.getD k 0 = Spec.Blake2.b.IV[k] := by
  simp [List.getD_eq_getElem?_getD, hk]

structure IvInv (scr : BitVec 32) (T : Nat → BitVec 64) (s : VG.Arm.State) (n : Nat) (s' : VG.Arm.State) :
    Prop where
  gpr : ∀ r, r ∉ [Reg.r4, .r5, .r6, .r7] → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  vars : ∀ k < 8, rd64 s'.mem scr (8 * k) = rd64 s.mem scr (8 * k)
  ivs : ∀ k, k < n → ∀ h8 : k < 8, rd64 s'.mem scr (64 + 8 * k) = Spec.Blake2.b.IV[k] ^^^ T k
  frame : Frame [VG.Proof.Blake2.ArmB.workR scr] s.mem s'.mem

theorem ldIV_ok {st scr : BitVec 32} {s : VG.Arm.State} (c : VG.Proof.Blake2.ArmB.Ctx st scr s) (T : Nat → BitVec 64)
    (hT : ∀ k < 8, rd64 s.mem scr (tweak k) = T k) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap ldIV)) s (VG.Proof.Blake2.ArmB.IvInv scr T s n) := by
  intro n hn
  have fitV := c.fitV
  induction n with
  | zero => exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl,
      fun _ h _ => absurd h (by omega), Frame.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s₁ h₁ => ?_
    have c₁ := c.of_eq (h₁.gpr _ (by decide)) (h₁.gpr _ (by decide)) h₁.wr
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [ldIV, ← List.append_nil (Impl.Sha512.Arm.st .r4 .r5 .r3 (64 + 8 * n))]
    have tw := VG.Proof.Blake2.ArmB.tweak_ok n
    refine wp_const64 (by decide) fun s₂ o₂ p₂ => ?_
    refine wp_ld (by decide) (by decide) (by omega) (by rw [o₂.gpr _ (by decide), c₁.r3])
      (by rw [o₂.wr]; exact (c₁.wV _ tw.2).1) (by rw [o₂.wr]; exact (c₁.wV _ tw.2).2)
      fun s₃ o₃ p₃ => ?_
    refine VG.Proof.Blake2.ArmB.wp_xor64 (by decide) (by decide) (p₂.of_only o₃ (by decide) (by decide)) p₃
      fun s₄ o₄ p₄ => ?_
    have O := (o₂.trans o₃).trans o₄
    refine wp_st (by omega) (by rw [O.gpr _ (by decide), c₁.r3]) p₄
      (by rw [O.wr]; exact (c₁.wV _ (by omega)).1) (by rw [O.wr]; exact (c₁.wV _ (by omega)).2)
      fun s₅ u₅ => WP.block_nil ⟨fun r hr => ?_, by rw [u₅.rd, O.rd, h₁.rd],
        by rw [u₅.wr, O.wr, h₁.wr], by rw [u₅.sp, O.sp, h₁.sp], fun k hk => ?_, fun k hk h8 => ?_, ?_⟩
    · rw [u₅.gpr, (O.mono (by decide)).gpr r hr, h₁.gpr r hr]
    · rw [u₅.mem, rd64_write64_ne (b := scr) (o := 64 + 8 * n) (o' := 8 * k) _ _ (by omega)
        (by omega) (by omega), O.mem]
      exact h₁.vars k hk
    · rw [u₅.mem]
      by_cases hkn : k = n
      · subst hkn
        rw [rd64_write64_self _ _ (by omega), o₂.mem,
          VG.Proof.Blake2.ArmB.rd64_frame_hi fitV h₁.frame tw.1 tw.2, hT k (by omega), VG.Proof.Blake2.ArmB.iv_getD (by omega)]
      · rw [rd64_write64_ne (b := scr) (o := 64 + 8 * n) (o' := 64 + 8 * k) _ _ (by omega)
          (by omega) (by omega), O.mem]
        exact h₁.ivs k (by omega) h8
    · rw [u₅.mem, O.mem]
      exact frame_write64 (N := 128) (o := 64 + 8 * n) h₁.frame (by simp) (by omega) (by omega) _

/-- `init` makes the work vector of `F` for the state `H` (at `st`) and the
tweaks `T` (in `scratch`). -/
theorem init_ok {st scr : BitVec 32} {s : VG.Arm.State} (c : VG.Proof.Blake2.ArmB.Ctx st scr s) (T : Nat → BitVec 64)
    (hT : ∀ k < 8, rd64 s.mem scr (tweak k) = T k) :
    WP isa (.block Impl.Blake2.Arm.B.init) s fun s' =>
      (∀ r, r ∉ [Reg.r4, .r5, .r6, .r7] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ Frame [VG.Proof.Blake2.ArmB.workR scr] s.mem s'.mem ∧
      ∀ k (hk : k < 16), rd64 s'.mem scr (8 * k) =
        if k < 8 then rd64 s.mem st (8 * k) else Spec.Blake2.b.IV[k - 8]'(by omega) ^^^ T (k - 8) := by
  unfold Impl.Blake2.Arm.B.init
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Blake2.ArmB.ldH_ok c 8 (Nat.le_refl _)) fun s₁ h₁ => ?_
  have c₁ := c.of_eq (h₁.gpr _ (by decide)) (h₁.gpr _ (by decide)) h₁.wr
  have hT₁ : ∀ k < 8, rd64 s₁.mem scr (tweak k) = T k := fun k hk => by
    rw [VG.Proof.Blake2.ArmB.rd64_frame_hi c.fitV h₁.frame (VG.Proof.Blake2.ArmB.tweak_ok k).1 (VG.Proof.Blake2.ArmB.tweak_ok k).2]; exact hT k hk
  refine WP.mono (VG.Proof.Blake2.ArmB.ldIV_ok c₁ T hT₁ 8 (Nat.le_refl _)) fun s₂ h₂ => ?_
  refine ⟨fun r hr => by rw [h₂.gpr r hr, h₁.gpr r hr], by rw [h₂.rd, h₁.rd], by rw [h₂.wr, h₁.wr],
    by rw [h₂.sp, h₁.sp], h₁.frame.trans h₂.frame, fun k hk => ?_⟩
  by_cases h8 : k < 8
  · simp only [h8, ↓reduceIte]; rw [h₂.vars k h8, h₁.vars k h8]
  · simp only [h8, ↓reduceIte]
    rw [show 8 * k = 64 + 8 * (k - 8) by omega, h₂.ivs (k - 8) (by omega) (by omega)]

/-! ## XORing the work vector into the state -/

structure UInv (st scr : BitVec 32) (s : VG.Arm.State) (n : Nat) (s' : VG.Arm.State) : Prop where
  gpr : ∀ r, r ∉ [Reg.r4, .r5, .r6, .r7, .r8, .r9] → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  done : ∀ k < n, rd64 s'.mem st (8 * k) =
    rd64 s.mem st (8 * k) ^^^ rd64 s.mem scr (8 * k) ^^^ rd64 s.mem scr (64 + 8 * k)
  todo : ∀ k, n ≤ k → k < 8 → rd64 s'.mem st (8 * k) = rd64 s.mem st (8 * k)
  frame : Frame [VG.Proof.Blake2.ArmB.stR st] s.mem s'.mem

theorem fin_ok {st scr : BitVec 32} {s : VG.Arm.State} (c : VG.Proof.Blake2.ArmB.Ctx st scr s) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap finH)) s (VG.Proof.Blake2.ArmB.UInv st scr s n) := by
  intro n hn
  have fitS := c.fitS
  have fitV := c.fitV
  induction n with
  | zero => exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ h => absurd h (by omega),
      fun _ _ _ => rfl, Frame.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s₁ h₁ => ?_
    have c₁ := c.of_eq (h₁.gpr _ (by decide)) (h₁.gpr _ (by decide)) h₁.wr
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [finH, ← List.append_nil (Impl.Sha512.Arm.st .r4 .r5 .r0 (8 * n))]
    refine wp_ld (by decide) (by decide) (by omega) c₁.r0 (c₁.wS _ (by omega)).1
      (c₁.wS _ (by omega)).2 fun s₂ o₂ p₂ => ?_
    refine wp_ld (by decide) (by decide) (by omega) (by rw [o₂.gpr _ (by decide), c₁.r3])
      (by rw [o₂.wr]; exact (c₁.wV _ (by omega)).1) (by rw [o₂.wr]; exact (c₁.wV _ (by omega)).2)
      fun s₃ o₃ p₃ => ?_
    have O₃ := o₂.trans o₃
    refine wp_ld (by decide) (by decide) (by omega) (by rw [O₃.gpr _ (by decide), c₁.r3])
      (by rw [O₃.wr]; exact (c₁.wV _ (by omega)).1) (by rw [O₃.wr]; exact (c₁.wV _ (by omega)).2)
      fun s₄ o₄ p₄ => ?_
    refine VG.Proof.Blake2.ArmB.wp_xor64 (by decide) (by decide) (p₂.of_only (o₃.trans o₄) (by decide) (by decide))
      (p₃.of_only o₄ (by decide) (by decide)) fun s₅ o₅ p₅ => ?_
    refine VG.Proof.Blake2.ArmB.wp_xor64 (by decide) (by decide) p₅ (p₄.of_only o₅ (by decide) (by decide))
      fun s₆ o₆ p₆ => ?_
    have O := ((O₃.trans o₄).trans o₅).trans o₆
    refine wp_st (by omega) (by rw [O.gpr _ (by decide), c₁.r0]) p₆
      (by rw [O.wr]; exact (c₁.wS _ (by omega)).1) (by rw [O.wr]; exact (c₁.wS _ (by omega)).2)
      fun s₇ u₇ => WP.block_nil ⟨fun r hr => ?_, by rw [u₇.rd, O.rd, h₁.rd],
        by rw [u₇.wr, O.wr, h₁.wr], by rw [u₇.sp, O.sp, h₁.sp], fun k hk => ?_, fun k hk hk' => ?_, ?_⟩
    · rw [u₇.gpr, (O.mono (by decide)).gpr r hr, h₁.gpr r hr]
    · have hd : ∀ r ∈ [VG.Proof.Blake2.ArmB.stR st], Region.Disjoint (VG.Proof.Blake2.ArmB.scrR scr) r := fun r hr => by
        simp at hr; subst hr; exact c.disj.symm
      rw [u₇.mem, O.mem, o₃.mem, o₂.mem]
      by_cases hkn : k = n
      · subst hkn
        rw [rd64_write64_self _ _ (by omega), h₁.todo k (by omega) (by omega),
          rd64_frame h₁.frame hd fitV (by omega), rd64_frame h₁.frame hd fitV (by omega)]
      · rw [rd64_write64_ne (b := st) (o := 8 * n) (o' := 8 * k) _ _ (by omega) (by omega)
          (by omega)]
        exact h₁.done k (by omega)
    · rw [u₇.mem, rd64_write64_ne (b := st) (o := 8 * n) (o' := 8 * k) _ _ (by omega)
        (by omega) (by omega), O.mem]
      exact h₁.todo k (by omega) hk'
    · rw [u₇.mem, O.mem]
      exact frame_write64 (N := 64) (o := 8 * n) h₁.frame (by simp) fitS (by omega) _

end VG.Proof.Blake2.ArmB

end

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.Arm.CompressB`. -/
section

section

/-!
# BLAKE2b on ARMv7: the code as a literal

The code of the compression function as a literal (`materialize_code`,
`Proof/Framework/Lit.lean`).
-/

namespace VG

materialize_code Impl.Blake2.Arm.B.compress

end VG

end

/-!
# BLAKE2b compression function on ARMv7: the whole function

The loop is proven against `Proof.Blake2.compressArm Spec.Blake2.b`
(`compress_verified'`), which the streaming functions use for their calls;
`compress_verified` moves it to the shared contract of
`Spec/Blake2/Contract.lean`. Constant time is the taint analysis on the
literal code (`LitB.lean`).
-/

namespace VG.Proof.Blake2.ArmB

open VG VG.Arm
open VG.Impl.Sha512.Arm (lo hi)
open VG.Impl.Blake2.Arm.B (advance body save restore setup saved tweak ctrLo ctrHi flagOff zeroOff)
open VG.Proof.Sha512.Arm (Only Pair rd64 write64 A A_eq Reg64 lo_append hi_append hi_append_lo
  eq_of_lo_hi lo_add hi_add lo_toNat hi_toNat readW64 rd64_frame lo_rd64 hi_rd64)
open VG.Proof.MdStream.Arm (eval_ne contains_offset sub_offset)
open VG.Spec.Blake2 (Work Block HashValue Params)

/-! ## Memory -/

theorem stateAt_get {st : BitVec 32} (hfit : st.toNat + 64 ≤ 2 ^ 32) (m : Mem) {k : Nat} (hk : k < 8) :
    (Spec.Blake2.stateAt 64 m (State.addr st))[k] = rd64 m st (8 * k) := by
  simp only [Spec.Blake2.stateAt, Vector.getElem_ofFn, rd64]
  rw [readW64, A_eq (by omega), A_eq (by omega),
    show State.addr st + BitVec.ofNat 64 (8 * k) + 4 = State.addr st + BitVec.ofNat 64 (8 * k + 4) from
      Offset.add_ofNat_add_ofNat _ _ 4]

theorem stateAt_ext {st : BitVec 32} (hfit : st.toNat + 64 ≤ 2 ^ 32) {m : Mem} {H : HashValue 64}
    (h : ∀ k (hk : k < 8), rd64 m st (8 * k) = (H[k]'(by omega))) : Spec.Blake2.stateAt 64 m (State.addr st) = H := by
  ext k hk
  rw [VG.Proof.Blake2.ArmB.stateAt_get hfit m hk, h k hk]

theorem blockAt_get {bk : BitVec 32} (hfit : bk.toNat + 128 ≤ 2 ^ 32) (m : Mem) {j : Nat} (hj : j < 16) :
    Spec.Blake2.blockAt 64 m (State.addr bk) ⟨j, hj⟩ = rd64 m bk (8 * j) := by
  rw [Proof.Blake2.blockAt_word, readW64, rd64, A_eq (by omega), A_eq (by omega),
    show State.addr bk + BitVec.ofNat 64 (64 / 8 * j) + 4 = State.addr bk + BitVec.ofNat 64 (8 * j + 4) from
      Offset.add_ofNat_add_ofNat _ _ 4]

/-- A 32-bit word outside the regions a frame allows to change. -/
theorem readW_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {a : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨a, 4⟩ r) : m'.readW a 32 = m.readW a 32 :=
  hf.readW (Region.contains_self _ _) hd (by decide)

/-! ## The precondition -/

section
variable (s₀ : VG.Arm.State)

abbrev stp : BitVec 32 := s₀.gpr .r0
abbrev bp : BitVec 32 := s₀.gpr .r1
abbrev nb : Nat := (s₀.gpr .r2).toNat
abbrev scp : BitVec 32 := stackArg s₀ 3
abbrev t₀ : Nat := (tArm s₀).toNat
abbrev fl : Bool := stackArg s₀ 2 != 0
abbrev blR : Region := ⟨State.addr (VG.Proof.Blake2.ArmB.bp s₀), 128 * VG.Proof.Blake2.ArmB.nb s₀⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 16⟩
abbrev H₀ : HashValue 64 := Spec.Blake2.stateAt 64 s₀.mem (State.addr (VG.Proof.Blake2.ArmB.stp s₀))

/-- Where block `i` starts. -/
abbrev blkAddr (i : Nat) : BitVec 32 := VG.Proof.Blake2.ArmB.bp s₀ + BitVec.ofNat 32 (128 * i)

/-- The counter's region in `scratch`. -/
abbrev ctrR : Region := ⟨State.addr (VG.Proof.Blake2.ArmB.scp s₀) + BitVec.ofNat 64 ctrLo, 12⟩

end

structure Pre (s₀ : VG.Arm.State) : Prop where
  rd : s₀.rd = [VG.Proof.Blake2.ArmB.blR s₀, VG.Proof.Blake2.ArmB.argR s₀]
  wr : s₀.wr = [VG.Proof.Blake2.ArmB.stR (VG.Proof.Blake2.ArmB.stp s₀), VG.Proof.Blake2.ArmB.scrR (VG.Proof.Blake2.ArmB.scp s₀)]
  st_scr : (VG.Proof.Blake2.ArmB.stR (VG.Proof.Blake2.ArmB.stp s₀)).Disjoint (VG.Proof.Blake2.ArmB.scrR (VG.Proof.Blake2.ArmB.scp s₀))
  blk_st : (VG.Proof.Blake2.ArmB.blR s₀).Disjoint (VG.Proof.Blake2.ArmB.stR (VG.Proof.Blake2.ArmB.stp s₀))
  blk_scr : (VG.Proof.Blake2.ArmB.blR s₀).Disjoint (VG.Proof.Blake2.ArmB.scrR (VG.Proof.Blake2.ArmB.scp s₀))
  a_st : (VG.Proof.Blake2.ArmB.argR s₀).Disjoint (VG.Proof.Blake2.ArmB.stR (VG.Proof.Blake2.ArmB.stp s₀))
  a_scr : (VG.Proof.Blake2.ArmB.argR s₀).Disjoint (VG.Proof.Blake2.ArmB.scrR (VG.Proof.Blake2.ArmB.scp s₀))
  st_fits : (VG.Proof.Blake2.ArmB.stp s₀).toNat + 64 ≤ 2 ^ 32
  blk_fits : (VG.Proof.Blake2.ArmB.bp s₀).toNat + 128 * VG.Proof.Blake2.ArmB.nb s₀ ≤ 2 ^ 32
  scr_fits : (VG.Proof.Blake2.ArmB.scp s₀).toNat + 512 ≤ 2 ^ 32
  sp_fits : s₀.sp.toNat + 16 ≤ 2 ^ 32

theorem pre_of (s₀ : VG.Arm.State) (h : (VG.Proof.Blake2.compressArm Spec.Blake2.b).pre s₀) : VG.Proof.Blake2.ArmB.Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

namespace Pre
variable {s₀ : VG.Arm.State} (h : VG.Proof.Blake2.ArmB.Pre s₀)
include h

theorem ctx {s : VG.Arm.State} (h0 : s.gpr .r0 = VG.Proof.Blake2.ArmB.stp s₀) (h3 : s.gpr .r3 = VG.Proof.Blake2.ArmB.scp s₀) (hw : s.wr = s₀.wr) :
    VG.Proof.Blake2.ArmB.Ctx (VG.Proof.Blake2.ArmB.stp s₀) (VG.Proof.Blake2.ArmB.scp s₀) s :=
  ⟨h0, h3, h.st_fits, h.scr_fits, h.st_scr,
    Reg64.of_mem (by rw [hw, h.wr]; simp) h.st_fits, Reg64.of_mem (by rw [hw, h.wr]; simp) h.scr_fits⟩

theorem blk_toNat {i : Nat} (hi : i < VG.Proof.Blake2.ArmB.nb s₀) : (VG.Proof.Blake2.ArmB.blkAddr s₀ i).toNat = (VG.Proof.Blake2.ArmB.bp s₀).toNat + 128 * i := by
  have := h.blk_fits
  simp only [VG.Proof.Blake2.ArmB.blkAddr, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := 128 * i) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem blk_fit {i : Nat} (hi : i < VG.Proof.Blake2.ArmB.nb s₀) : (VG.Proof.Blake2.ArmB.blkAddr s₀ i).toNat + 128 ≤ 2 ^ 32 := by
  have := h.blk_fits; rw [h.blk_toNat hi]; omega

theorem blk_addr {i : Nat} (hi : i < VG.Proof.Blake2.ArmB.nb s₀) :
    State.addr (VG.Proof.Blake2.ArmB.blkAddr s₀ i) = State.addr (VG.Proof.Blake2.ArmB.bp s₀) + BitVec.ofNat 64 (128 * i) :=
  addr_add (by have := h.blk_fits; omega)

theorem blk_sub {i : Nat} (hi : i < VG.Proof.Blake2.ArmB.nb s₀) : Region.Sub ⟨State.addr (VG.Proof.Blake2.ArmB.blkAddr s₀ i), 128⟩ (VG.Proof.Blake2.ArmB.blR s₀) := by
  have := h.blk_fits
  rw [h.blk_addr hi]; exact sub_offset (by omega) (by omega)

theorem blk_rd {i : Nat} (hi : i < VG.Proof.Blake2.ArmB.nb s₀) : VG.Proof.Blake2.ArmB.Rd64 (s₀.rd ++ s₀.wr) (VG.Proof.Blake2.ArmB.blkAddr s₀ i) 128 := by
  have := h.blk_fit hi
  have := h.blk_fits
  have hc : ∀ o, o + 4 ≤ 128 → InRegions (s₀.rd ++ s₀.wr) (A (VG.Proof.Blake2.ArmB.blkAddr s₀ i) o) 4 := fun o ho => by
    refine ⟨VG.Proof.Blake2.ArmB.blR s₀, by simp [h.rd], ?_⟩
    rw [A_eq (by omega), h.blk_addr hi, Offset.add_ofNat_add_ofNat]
    exact contains_offset (by omega) (by omega)
  exact fun o ho => ⟨hc o (by omega), hc (o + 4) (by omega)⟩

/-- The address of a word of `scratch`. -/
theorem scr_addr {d : Nat} (hd : d < 512) :
    A (VG.Proof.Blake2.ArmB.scp s₀) d = State.addr (VG.Proof.Blake2.ArmB.scp s₀) + BitVec.ofNat 64 d := A_eq (by have := h.scr_fits; omega)

theorem in_scr {d : Nat} (hd : d + 4 ≤ 512) : InRegions (s₀.rd ++ s₀.wr) (A (VG.Proof.Blake2.ArmB.scp s₀) d) 4 := by
  rw [h.scr_addr (by omega)]
  exact ⟨VG.Proof.Blake2.ArmB.scrR (VG.Proof.Blake2.ArmB.scp s₀), by simp [h.wr], contains_offset hd (by omega)⟩

theorem out_scr {d : Nat} (hd : d + 4 ≤ 512) : InRegions s₀.wr (A (VG.Proof.Blake2.ArmB.scp s₀) d) 4 := by
  rw [h.scr_addr (by omega)]
  exact ⟨VG.Proof.Blake2.ArmB.scrR (VG.Proof.Blake2.ArmB.scp s₀), by simp [h.wr], contains_offset hd (by omega)⟩

/-- A scratch word apart from the work vector, the state and the counter. -/
theorem scr_frame {d : Nat} (hd : 128 ≤ d) (hd' : d + 4 ≤ 512) (hc : d + 4 ≤ ctrLo ∨ ctrLo + 12 ≤ d)
    {m m' : Mem}
    (hf : Frame [VG.Proof.Blake2.ArmB.workR (VG.Proof.Blake2.ArmB.scp s₀)] m m' ∨ Frame [VG.Proof.Blake2.ArmB.stR (VG.Proof.Blake2.ArmB.stp s₀)] m m' ∨ Frame [VG.Proof.Blake2.ArmB.ctrR s₀] m m') :
    m'.readW (A (VG.Proof.Blake2.ArmB.scp s₀) d) 32 = m.readW (A (VG.Proof.Blake2.ArmB.scp s₀) d) 32 := by
  have := h.scr_fits
  rw [h.scr_addr (by omega)]
  rcases hf with hf | hf | hf <;> refine VG.Proof.Blake2.ArmB.readW_frame hf ?_ <;>
    simp only [List.mem_singleton, forall_eq]
  · exact Offset.disjoint_base _ hd (by omega)
  · exact Region.Disjoint.sub_left h.st_scr.symm (Offset.sub_base _ (by omega))
  · exact Offset.disjoint _ hc (by omega) (by simp only [ctrLo]; omega)

theorem scr_frame64 {d : Nat} (hd : 128 ≤ d) (hd' : d + 8 ≤ 512) (hc : d + 8 ≤ ctrLo ∨ ctrLo + 12 ≤ d)
    {m m' : Mem}
    (hf : Frame [VG.Proof.Blake2.ArmB.workR (VG.Proof.Blake2.ArmB.scp s₀)] m m' ∨ Frame [VG.Proof.Blake2.ArmB.stR (VG.Proof.Blake2.ArmB.stp s₀)] m m' ∨ Frame [VG.Proof.Blake2.ArmB.ctrR s₀] m m') :
    rd64 m' (VG.Proof.Blake2.ArmB.scp s₀) d = rd64 m (VG.Proof.Blake2.ArmB.scp s₀) d := by
  simp only [rd64]
  rw [h.scr_frame (by omega) (by omega) (by omega) hf, h.scr_frame (by omega) (by omega) (by omega) hf]

/-- A state word apart from the scratch space. -/
theorem st_frame {m m' : Mem} (hf : Frame [VG.Proof.Blake2.ArmB.scrR (VG.Proof.Blake2.ArmB.scp s₀)] m m') {k : Nat} (hk : k < 8) :
    rd64 m' (VG.Proof.Blake2.ArmB.stp s₀) (8 * k) = rd64 m (VG.Proof.Blake2.ArmB.stp s₀) (8 * k) :=
  rd64_frame hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.st_scr)
    h.st_fits (by omega)

/-- A block word apart from the state and the scratch space. -/
theorem blk_frame {m m' : Mem} (hf : Frame [VG.Proof.Blake2.ArmB.stR (VG.Proof.Blake2.ArmB.stp s₀), VG.Proof.Blake2.ArmB.scrR (VG.Proof.Blake2.ArmB.scp s₀)] m m') {i : Nat}
    (hi : i < VG.Proof.Blake2.ArmB.nb s₀) {o : Nat} (ho : o + 8 ≤ 128) :
    rd64 m' (VG.Proof.Blake2.ArmB.blkAddr s₀ i) o = rd64 m (VG.Proof.Blake2.ArmB.blkAddr s₀ i) o :=
  rd64_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.blk_st.sub_left (h.blk_sub hi)
    · exact h.blk_scr.sub_left (h.blk_sub hi)) (h.blk_fit hi) ho

end Pre

/-! ## Advancing the counter -/

/-- The counter's three words after advancing by 128. -/
def ctrMem (m : Mem) (scr : BitVec 32) (N : Nat) : Mem :=
  ((m.writeW (A scr ctrLo) (lo (BitVec.ofNat 64 (N + 128)))).writeW (A scr (ctrLo + 4))
    (hi (BitVec.ofNat 64 (N + 128)))).writeW (A scr ctrHi) (BitVec.ofNat 32 ((N + 128) / 2 ^ 64))

theorem carry_lo (N : Nat) : lo (BitVec.ofNat 64 N) + 128 = lo (BitVec.ofNat 64 (N + 128)) := by
  rw [← BitVec.ofNat_add_ofNat, lo_add]; rfl

theorem carry_hi (N : Nat) :
    hi (BitVec.ofNat 64 N) + (0 + 0 + if 2 ^ 32 ≤ (lo (BitVec.ofNat 64 N)).toNat + 128 then 1 else 0) =
      hi (BitVec.ofNat 64 (N + 128)) := by
  rw [← BitVec.ofNat_add_ofNat, hi_add]
  simp only [show lo (BitVec.ofNat 64 128) = 128 from rfl, show hi (BitVec.ofNat 64 128) = 0 from rfl,
    show (128 : BitVec 32).toNat = 128 from rfl]
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.zero_add]

theorem carry_top (N : Nat) :
    BitVec.ofNat 32 (N / 2 ^ 64) + 0 +
      (if 2 ^ 32 ≤ (hi (BitVec.ofNat 64 N)).toNat +
        (0 + 0 + if 2 ^ 32 ≤ (lo (BitVec.ofNat 64 N)).toNat + 128 then (1 : BitVec 32) else 0).toNat
        then 1 else 0) = BitVec.ofNat 32 ((N + 128) / 2 ^ 64) := by
  have hl := lo_toNat (BitVec.ofNat 64 N)
  have hh := hi_toNat (BitVec.ofNat 64 N)
  rw [BitVec.toNat_ofNat] at hl hh
  generalize (lo (BitVec.ofNat 64 N)).toNat = L at hl
  generalize (hi (BitVec.ofNat 64 N)).toNat = H at hh
  apply BitVec.eq_of_toNat_eq
  by_cases c0 : 2 ^ 32 ≤ L + 128
  · simp only [c0, ite_true, show ((0 : BitVec 32) + 0 + 1).toNat = 1 from rfl]
    by_cases c1 : 2 ^ 32 ≤ H + 1
    · simp only [c1, ite_true, BitVec.toNat_add, BitVec.toNat_ofNat, show (0 : BitVec 32).toNat = 0 from rfl,
        show (1 : BitVec 32).toNat = 1 from rfl]
      omega
    · simp only [c1, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, show (0 : BitVec 32).toNat = 0 from rfl]
      omega
  · simp only [c0, ite_false, show ((0 : BitVec 32) + 0 + 0).toNat = 0 from rfl, Nat.add_zero]
    have c1 : ¬ 2 ^ 32 ≤ H := by omega
    simp only [c1, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, show (0 : BitVec 32).toNat = 0 from rfl]
    omega

set_option simprocs false in
theorem advance_ok {s : VG.Arm.State} {scr : BitVec 32} {N : Nat} (h3 : s.gpr .r3 = scr) (hw : Reg64 s.wr scr 512)
    (hlo : rd64 s.mem scr ctrLo = BitVec.ofNat 64 N)
    (hhi : s.mem.readW (A scr ctrHi) 32 = BitVec.ofNat 32 (N / 2 ^ 64)) :
    WP isa (.block advance) s fun s' =>
      s'.gpr .r1 = s.gpr .r1 + 128 ∧ s'.gpr .r2 = s.gpr .r2 - 1 ∧ s'.z = (s.gpr .r2 - 1 == 0) ∧
      (∀ r, r ∉ [Reg.r1, .r2, .r4, .r5, .r6, .r7] → s'.gpr r = s.gpr r) ∧
      s'.mem = VG.Proof.Blake2.ArmB.ctrMem s.mem scr N ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have o168 := hw ctrLo (by decide)
  have o176 := hw ctrHi (by decide)
  have i168 := Reg64.rd s.rd hw ctrLo (by decide)
  have i176 := Reg64.rd s.rd hw ctrHi (by decide)
  have hl := lo_rd64 s.mem scr ctrLo
  have hh := hi_rd64 s.mem scr ctrLo
  rw [hlo] at hl hh
  simp only [A, ctrLo, ctrHi, show 168 + 4 = 172 from rfl] at o168 o176 i168 i176 hhi hl hh
  apply WP.of_runBlock
  simp (config := {decide := true}) only [advance, ctrLo, ctrHi, show 168 + 4 = 172 from rfl,
    runBlock_cons, runStep_some,
    runBlock_nil, exec, isa, Op2.eval, State.load32, State.store32, addFlags, subFlags,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.c_setReg,
    RegUpd.z_setReg, RegUpd.sp_setReg, h3, i168.1, i168.2, i176.1, o168.1, o168.2, o176.1,
    ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  simp only [← hl, ← hh, hhi]
  simp only [decide_eq_true_eq, show (128 : BitVec 32).toNat = 128 from rfl]
  refine ⟨trivial, trivial, trivial, fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h4, h5, h6, h7⟩ := hr
    simp only [h1, h2, h4, h5, h6, h7, ite_false]
  · refine ⟨?_, trivial⟩
    rw [VG.Proof.Blake2.ArmB.carry_lo, VG.Proof.Blake2.ArmB.carry_hi, VG.Proof.Blake2.ArmB.carry_top N]
    rfl

/-! ## The prologue -/

/-- The address of word `d` of `scratch`. -/
abbrev SA (s₀ : VG.Arm.State) (d : Nat) : Addr := State.addr (VG.Proof.Blake2.ArmB.scp s₀ + BitVec.ofNat 32 d)

/-- The flag word of `last`. -/
def flag32 (l : BitVec 32) : BitVec 32 := 0 - ((0 - l ||| l) >>> 31)

/-- The words the prologue stores in `scratch`, in order. -/
def setupWrites (s₀ : VG.Arm.State) : List (Nat × BitVec 32) :=
  [(168, stackArg s₀ 0), (172, stackArg s₀ 1), (128, s₀.gpr .r4), (132, s₀.gpr .r5),
   (136, s₀.gpr .r6), (140, s₀.gpr .r7), (144, s₀.gpr .r8), (148, s₀.gpr .r9), (152, s₀.gpr .r10),
   (156, s₀.gpr .r11), (160, s₀.gpr .lr), (176, 0), (180, 0), (192, 0), (196, 0),
   (184, VG.Proof.Blake2.ArmB.flag32 (stackArg s₀ 2)), (188, VG.Proof.Blake2.ArmB.flag32 (stackArg s₀ 2))]

/-- The memory after the prologue. -/
def setupMem (s₀ : VG.Arm.State) : Mem :=
  (VG.Proof.Blake2.ArmB.setupWrites s₀).foldl (fun m p => m.writeW (VG.Proof.Blake2.ArmB.SA s₀ p.1) p.2) s₀.mem

theorem SA_eq {s₀ : VG.Arm.State} (hp : VG.Proof.Blake2.ArmB.Pre s₀) {d : Nat} (hd : d < 512) :
    VG.Proof.Blake2.ArmB.SA s₀ d = State.addr (VG.Proof.Blake2.ArmB.scp s₀) + BitVec.ofNat 64 d := hp.scr_addr hd

theorem SA_sep {s₀ : VG.Arm.State} (hp : VG.Proof.Blake2.ArmB.Pre s₀) {d e : Nat} (hd : d + 4 ≤ 512) (he : e + 4 ≤ 512)
    (h : d + 4 ≤ e ∨ e + 4 ≤ d) : Mem.Sep (VG.Proof.Blake2.ArmB.SA s₀ d) 4 (VG.Proof.Blake2.ArmB.SA s₀ e) 4 := by
  rw [VG.Proof.Blake2.ArmB.SA_eq hp (by omega), VG.Proof.Blake2.ArmB.SA_eq hp (by omega)]
  exact Offset.sep _ h (by omega) (by omega)

theorem readW_writeW_SA {s₀ : VG.Arm.State} (hp : VG.Proof.Blake2.ArmB.Pre s₀) (m : Mem) (v : BitVec 32) {d e : Nat}
    (hd : d + 4 ≤ 512) (he : e + 4 ≤ 512) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (VG.Proof.Blake2.ArmB.SA s₀ e) v).readW (VG.Proof.Blake2.ArmB.SA s₀ d) 32 = m.readW (VG.Proof.Blake2.ArmB.SA s₀ d) 32 :=
  Mem.readW_writeW_sep (VG.Proof.Blake2.ArmB.SA_sep hp hd he h) (by decide)

/-- A stack argument is unchanged by a write to `scratch`. -/
theorem readW_writeW_arg {s₀ : VG.Arm.State} (hp : VG.Proof.Blake2.ArmB.Pre s₀) (m : Mem) (v : BitVec 32) {i e : Nat} (hi : i < 4)
    (he : e + 4 ≤ 512) :
    (m.writeW (VG.Proof.Blake2.ArmB.SA s₀ e) v).readW (State.addr (s₀.sp + BitVec.ofNat 32 (4 * i))) 32 =
      m.readW (State.addr (s₀.sp + BitVec.ofNat 32 (4 * i))) 32 := by
  have := hp.sp_fits
  refine Mem.readW_writeW_sep (hp.a_scr.sep ?_ ?_) (by decide)
  · show (⟨State.addr (s₀.sp + BitVec.ofNat 32 (4 * 0)), 16⟩ : Region).Contains _ 4
    rw [addr_add (by omega), addr_add (by omega)]
    exact Offset.contains _ (by omega) (by omega) (by omega)
  · rw [VG.Proof.Blake2.ArmB.SA_eq hp (by omega)]; exact contains_offset he (by omega)

set_option simprocs false in
theorem setup_ok {s₀ : VG.Arm.State} (hp : VG.Proof.Blake2.ArmB.Pre s₀) :
    WP isa (.block setup) s₀ fun s₁ =>
      s₁.mem = VG.Proof.Blake2.ArmB.setupMem s₀ ∧ (∀ r ∈ [Reg.r0, .r1, .r2], s₁.gpr r = s₀.gpr r) ∧
      s₁.gpr .r3 = VG.Proof.Blake2.ArmB.scp s₀ ∧ s₁.z = (s₀.gpr .r2 - 0 == 0) ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧
      s₁.sp = s₀.sp := by
  have hs := hp.sp_fits
  have ia : ∀ i, i < 4 → InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.sp + BitVec.ofNat 32 (4 * i))) 4 :=
    fun i hi => ⟨VG.Proof.Blake2.ArmB.argR s₀, by simp [hp.rd], by
      show (⟨State.addr (s₀.sp + BitVec.ofNat 32 (4 * 0)), 16⟩ : Region).Contains _ 4
      rw [addr_add (by omega), addr_add (by omega)]
      exact Offset.contains _ (by omega) (by omega) (by omega)⟩
  have a0 := ia 0 (by decide); have a1 := ia 1 (by decide); have a2 := ia 2 (by decide)
  have a3 := ia 3 (by decide)
  simp only [show 4 * 0 = 0 from rfl, show 4 * 1 = 4 from rfl, show 4 * 2 = 8 from rfl,
    show 4 * 3 = 12 from rfl] at a0 a1 a2 a3
  have e3 : s₀.mem.readW (State.addr (s₀.sp + BitVec.ofNat 32 12)) 32 = stackArg s₀ 3 := rfl
  have e0 : s₀.mem.readW (State.addr (s₀.sp + BitVec.ofNat 32 0)) 32 = stackArg s₀ 0 := rfl
  have e1 : ∀ v, (s₀.mem.writeW (State.addr (stackArg s₀ 3 + BitVec.ofNat 32 168)) v).readW
      (State.addr (s₀.sp + BitVec.ofNat 32 4)) 32 = stackArg s₀ 1 := fun v =>
    VG.Proof.Blake2.ArmB.readW_writeW_arg hp _ v (i := 1) (by decide) (by decide)
  have e2 : ∀ v v', ((s₀.mem.writeW (State.addr (stackArg s₀ 3 + BitVec.ofNat 32 168)) v).writeW
      (State.addr (stackArg s₀ 3 + BitVec.ofNat 32 172)) v').readW
      (State.addr (s₀.sp + BitVec.ofNat 32 8)) 32 = stackArg s₀ 2 := fun v v' => by
    rw [VG.Proof.Blake2.ArmB.readW_writeW_arg hp _ v' (i := 2) (by decide) (by decide),
      VG.Proof.Blake2.ArmB.readW_writeW_arg hp _ v (i := 2) (by decide) (by decide)]; rfl
  have w : ∀ d, d + 4 ≤ 512 → InRegions s₀.wr (State.addr (stackArg s₀ 3 + BitVec.ofNat 32 d)) 4 :=
    fun d hd => hp.out_scr hd
  have w168 := w 168 (by decide); have w172 := w 172 (by decide); have w128 := w 128 (by decide)
  have w132 := w 132 (by decide); have w136 := w 136 (by decide); have w140 := w 140 (by decide)
  have w144 := w 144 (by decide); have w148 := w 148 (by decide); have w152 := w 152 (by decide)
  have w156 := w 156 (by decide); have w160 := w 160 (by decide); have w176 := w 176 (by decide)
  have w180 := w 180 (by decide); have w192 := w 192 (by decide); have w196 := w 196 (by decide)
  have w184 := w 184 (by decide); have w188 := w 188 (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [setup, VG.Impl.Blake2.Arm.B.save, VG.Impl.Blake2.Arm.B.saved, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, ctrLo, ctrHi, zeroOff, flagOff,
    show 168 + 4 = 172 from rfl, show 176 + 4 = 180 from rfl, show 192 + 4 = 196 from rfl,
    show 184 + 4 = 188 from rfl, runBlock_cons, runStep_some,
    runBlock_nil, exec, isa, Op2.eval, State.load32, State.store32, subFlags,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.sp_setReg, a0, a1, a2, a3, e3, e0, e1, e2, w168, w172, w128, w132, w136, w140, w144, w148,
    w152, w156, w160, w176, w180, w192, w196, w184, w188,
    ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, fun r hr => ?_, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> rfl

/-! ## The loop invariant -/

/-- The callee-saved registers are saved in the scratch space. -/
def Saved (s₀ : VG.Arm.State) (m : Mem) : Prop := ∀ p ∈ VG.Impl.Blake2.Arm.B.saved, m.readW (A (VG.Proof.Blake2.ArmB.scp s₀) p.2) 32 = s₀.gpr p.1

theorem saved_off : ∀ p ∈ VG.Impl.Blake2.Arm.B.saved, 128 ≤ p.2 ∧ p.2 + 4 ≤ 164 := by decide

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : VG.Arm.State) (i : Nat) (s : VG.Arm.State) : Prop where
  r0 : s.gpr .r0 = VG.Proof.Blake2.ArmB.stp s₀
  r3 : s.gpr .r3 = VG.Proof.Blake2.ArmB.scp s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [VG.Proof.Blake2.ArmB.stR (VG.Proof.Blake2.ArmB.stp s₀), VG.Proof.Blake2.ArmB.scrR (VG.Proof.Blake2.ArmB.scp s₀)] s₀.mem s.mem
  state : Spec.Blake2.stateAt 64 s.mem (State.addr (VG.Proof.Blake2.ArmB.stp s₀)) =
    Spec.Blake2.compressBlocks Spec.Blake2.b (VG.Proof.Blake2.ArmB.H₀ s₀) s₀.mem (State.addr (VG.Proof.Blake2.ArmB.bp s₀)) i (VG.Proof.Blake2.ArmB.t₀ s₀) (VG.Proof.Blake2.ArmB.fl s₀)
  saved : VG.Proof.Blake2.ArmB.Saved s₀ s.mem
  lo : rd64 s.mem (VG.Proof.Blake2.ArmB.scp s₀) ctrLo = BitVec.ofNat 64 (VG.Proof.Blake2.ArmB.t₀ s₀ + i * 128)
  hi : s.mem.readW (A (VG.Proof.Blake2.ArmB.scp s₀) ctrHi) 32 = BitVec.ofNat 32 ((VG.Proof.Blake2.ArmB.t₀ s₀ + i * 128) / 2 ^ 64)
  hi' : s.mem.readW (A (VG.Proof.Blake2.ArmB.scp s₀) (ctrHi + 4)) 32 = 0
  f : rd64 s.mem (VG.Proof.Blake2.ArmB.scp s₀) flagOff = VG.Proof.Blake2.ArmB.flagW 64 (VG.Proof.Blake2.ArmB.fl s₀)
  z : rd64 s.mem (VG.Proof.Blake2.ArmB.scp s₀) zeroOff = 0

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : VG.Arm.State) (i : Nat) (s : VG.Arm.State) : Prop extends VG.Proof.Blake2.ArmB.Common s₀ i s where
  r1 : s.gpr .r1 = VG.Proof.Blake2.ArmB.blkAddr s₀ i
  r2 : s.gpr .r2 = BitVec.ofNat 32 (VG.Proof.Blake2.ArmB.nb s₀ - i)

/-- The high 64 bits of the counter, from its two words. -/
theorem hi64 {H : Nat} (h : H < 2 ^ 32) : ((0 : BitVec 32) ++ BitVec.ofNat 32 H : BitVec 64) = BitVec.ofNat 64 H := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append]
  simp only [BitVec.toNat_ofNat, show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_shiftLeft,
    Nat.zero_or]
  omega

theorem ctr_bound {s₀ : VG.Arm.State} {i : Nat} (hi : i ≤ VG.Proof.Blake2.ArmB.nb s₀) : (VG.Proof.Blake2.ArmB.t₀ s₀ + i * 128) / 2 ^ 64 < 2 ^ 32 := by
  have h1 : VG.Proof.Blake2.ArmB.t₀ s₀ < 2 ^ 64 := (tArm s₀).isLt
  have h2 : VG.Proof.Blake2.ArmB.nb s₀ < 2 ^ 32 := (s₀.gpr .r2).isLt
  omega

theorem compressBlocks_succ' (H : HashValue 64) (m : Mem) (p : Addr) (i t : Nat) (f : Bool) :
    Spec.Blake2.compressBlocks Spec.Blake2.b H m p (i + 1) t f =
      Spec.Blake2.F Spec.Blake2.b (Spec.Blake2.compressBlocks Spec.Blake2.b H m p i t f)
        (Spec.Blake2.blockAt 64 m (p + BitVec.ofNat 64 (128 * i))) (t + i * 128) f :=
  Proof.Blake2.compressBlocks_succ _ _ _ _ _ _ _

theorem ctrMem_frame {s₀ : VG.Arm.State} (hp : VG.Proof.Blake2.ArmB.Pre s₀) (m : Mem) (N : Nat) :
    Frame [VG.Proof.Blake2.ArmB.ctrR s₀] m (VG.Proof.Blake2.ArmB.ctrMem m (VG.Proof.Blake2.ArmB.scp s₀) N) := by
  have := hp.scr_fits
  have c : ∀ d, ctrLo ≤ d → d + 4 ≤ ctrLo + 12 → (VG.Proof.Blake2.ArmB.ctrR s₀).Contains (A (VG.Proof.Blake2.ArmB.scp s₀) d) (32 / 8) :=
    fun d h1 h2 => by
      rw [hp.scr_addr (by simp only [ctrLo] at h2; omega)]
      exact Offset.contains _ h1 (by omega) (by simp only [ctrLo]; omega)
  have m' := List.mem_singleton_self (VG.Proof.Blake2.ArmB.ctrR s₀)
  exact (((Frame.refl _ _).writeW m' _ (c _ (by decide) (by decide))).writeW m' _
    (c _ (by decide) (by decide))).writeW m' _ (c _ (by decide) (by decide))

theorem ctrMem_lo {s₀ : VG.Arm.State} (hp : VG.Proof.Blake2.ArmB.Pre s₀) (m : Mem) (N : Nat) :
    rd64 (VG.Proof.Blake2.ArmB.ctrMem m (VG.Proof.Blake2.ArmB.scp s₀) N) (VG.Proof.Blake2.ArmB.scp s₀) ctrLo = BitVec.ofNat 64 (N + 128) := by
  simp only [rd64, VG.Proof.Blake2.ArmB.ctrMem, ctrLo, ctrHi, A]
  rw [VG.Proof.Blake2.ArmB.readW_writeW_SA hp _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32,
    VG.Proof.Blake2.ArmB.readW_writeW_SA hp _ _ (by decide) (by decide) (by decide),
    VG.Proof.Blake2.ArmB.readW_writeW_SA hp _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32, hi_append_lo]

theorem ctrMem_hi {s₀ : VG.Arm.State} (m : Mem) (N : Nat) :
    (VG.Proof.Blake2.ArmB.ctrMem m (VG.Proof.Blake2.ArmB.scp s₀) N).readW (A (VG.Proof.Blake2.ArmB.scp s₀) ctrHi) 32 = BitVec.ofNat 32 ((N + 128) / 2 ^ 64) := by
  simp only [VG.Proof.Blake2.ArmB.ctrMem, Mem.readW_writeW_self32]

/-! ## One block -/

theorem body_ok {s₀ : VG.Arm.State} (hp : VG.Proof.Blake2.ArmB.Pre s₀) {i : Nat} (hi : i < VG.Proof.Blake2.ArmB.nb s₀) {s : VG.Arm.State}
    (hL : VG.Proof.Blake2.ArmB.LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ VG.Proof.Blake2.ArmB.Common s₀ (VG.Proof.Blake2.ArmB.nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < VG.Proof.Blake2.ArmB.nb s₀ ∧ VG.Proof.Blake2.ArmB.LInv s₀ (i + 1) s') := by
  have c := hp.ctx hL.r0 hL.r3 hL.wr
  have fitS := hp.st_fits
  have fitV := hp.scr_fits
  have fitB := hp.blk_fit hi
  set N := VG.Proof.Blake2.ArmB.t₀ s₀ + i * 128 with hN
  set H := Spec.Blake2.compressBlocks Spec.Blake2.b (VG.Proof.Blake2.ArmB.H₀ s₀) s₀.mem (State.addr (VG.Proof.Blake2.ArmB.bp s₀)) i (VG.Proof.Blake2.ArmB.t₀ s₀) (VG.Proof.Blake2.ArmB.fl s₀)
    with hH
  set M := Spec.Blake2.blockAt 64 s₀.mem (State.addr (VG.Proof.Blake2.ArmB.blkAddr s₀ i)) with hM
  have hb := VG.Proof.Blake2.ArmB.ctr_bound (s₀ := s₀) (Nat.le_of_lt hi)
  have hHk : ∀ k (hk : k < 8), rd64 s.mem (VG.Proof.Blake2.ArmB.stp s₀) (8 * k) = (H[k]'(by omega)) := fun k hk => by
    rw [← VG.Proof.Blake2.ArmB.stateAt_get fitS _ hk, hL.state]
  -- Initialize the work vector.
  have hT : ∀ k < 8, rd64 s.mem (VG.Proof.Blake2.ArmB.scp s₀) (tweak k) = VG.Proof.Blake2.ArmB.tweakV N (VG.Proof.Blake2.ArmB.fl s₀) k := fun k hk => by
    unfold tweak VG.Proof.Blake2.ArmB.tweakV
    by_cases h4 : k = 4
    · simp only [h4, ite_true]; exact hL.lo
    by_cases h5 : k = 5
    · simp only [h5, ite_true, show (5 : Nat) ≠ 4 by decide, ite_false]
      have e1 := hL.hi
      have e2 := hL.hi'
      simp only [rd64, ctrHi, A] at e1 e2 ⊢
      rw [e1, e2, VG.Proof.Blake2.ArmB.hi64 hb]
    by_cases h6 : k = 6
    · simp only [h6, ite_true, show (6 : Nat) ≠ 4 by decide, show (6 : Nat) ≠ 5 by decide, ite_false]
      exact hL.f
    simp only [h4, h5, h6, ite_false]; exact hL.z
  refine WP.seq (WP.mono (VG.Proof.Blake2.ArmB.init_ok c _ hT) fun s₁ ⟨g₁, rd₁, wr₁, sp₁, f₁, v₁⟩ => ?_)
  have hv : ∀ k (hk : k < 16), rd64 s₁.mem (VG.Proof.Blake2.ArmB.scp s₀) (8 * k) = (VG.Proof.Blake2.ArmB.initV Spec.Blake2.b H N (VG.Proof.Blake2.ArmB.fl s₀))[k] :=
    fun k hk => by
      rw [v₁ k hk, VG.Proof.Blake2.ArmB.initV_get]
      by_cases h8 : k < 8
      · simp only [h8, ↓reduceIte, ↓reduceDIte]; exact hHk k h8
      · simp only [h8, ↓reduceIte, ↓reduceDIte]
  -- The rounds.
  have fr₁ : Frame [VG.Proof.Blake2.ArmB.stR (VG.Proof.Blake2.ArmB.stp s₀), VG.Proof.Blake2.ArmB.scrR (VG.Proof.Blake2.ArmB.scp s₀)] s₀.mem s₁.mem :=
    hL.frame.trans (f₁.sub fun r hr => ⟨VG.Proof.Blake2.ArmB.scrR (VG.Proof.Blake2.ArmB.scp s₀), by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)⟩)
  have rc : VG.Proof.Blake2.ArmB.RCtx (VG.Proof.Blake2.ArmB.scp s₀) (VG.Proof.Blake2.ArmB.blkAddr s₀ i) M s₁ :=
    ⟨by rw [g₁ _ (by decide), hL.r3], by rw [g₁ _ (by decide), hL.r1], by omega, fitB,
      fun o ho => by rw [wr₁]; exact c.wV o (by omega),
      by rw [rd₁, wr₁, hL.rd, hL.wr]; exact hp.blk_rd hi,
      (hp.blk_scr.sub_left (hp.blk_sub hi)).sub_right (Region.sub_prefix (by omega)),
      fun j hj => by rw [hp.blk_frame fr₁ hi (by omega), hM, VG.Proof.Blake2.ArmB.blockAt_get fitB _ hj]⟩
  refine WP.seq (WP.mono (VG.Proof.Blake2.ArmB.rounds_ok rc hv 12) fun s₂ h₂ => ?_)
  -- XOR into the state.
  have c₂ : VG.Proof.Blake2.ArmB.Ctx (VG.Proof.Blake2.ArmB.stp s₀) (VG.Proof.Blake2.ArmB.scp s₀) s₂ :=
    c.of_eq ((h₂.gpr _ (by decide)).trans (g₁ _ (by decide)))
      ((h₂.gpr _ (by decide)).trans (g₁ _ (by decide))) (h₂.wr.trans wr₁)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Blake2.ArmB.fin_ok c₂ 8 (Nat.le_refl _)) fun s₃ h₃ => ?_
  have f₁₂ : Frame [VG.Proof.Blake2.ArmB.workR (VG.Proof.Blake2.ArmB.scp s₀)] s.mem s₂.mem := f₁.trans h₂.frame
  have hctr : ∀ {m m' : Mem}, Frame [VG.Proof.Blake2.ArmB.workR (VG.Proof.Blake2.ArmB.scp s₀)] m m' ∨ Frame [VG.Proof.Blake2.ArmB.stR (VG.Proof.Blake2.ArmB.stp s₀)] m m' ∨
      Frame [VG.Proof.Blake2.ArmB.ctrR s₀] m m' → ∀ d, 128 ≤ d → d + 4 ≤ 512 → (d + 4 ≤ ctrLo ∨ ctrLo + 12 ≤ d) →
      m'.readW (A (VG.Proof.Blake2.ArmB.scp s₀) d) 32 = m.readW (A (VG.Proof.Blake2.ArmB.scp s₀) d) 32 :=
    fun hf d h1 h2 h3 => hp.scr_frame h1 h2 h3 hf
  have hctr3 : ∀ d, 128 ≤ d → d + 4 ≤ 512 →
      s₃.mem.readW (A (VG.Proof.Blake2.ArmB.scp s₀) d) 32 = s.mem.readW (A (VG.Proof.Blake2.ArmB.scp s₀) d) 32 := fun d h1 h2 => by
    have e₁ : s₂.mem.readW (A (VG.Proof.Blake2.ArmB.scp s₀) d) 32 = s.mem.readW (A (VG.Proof.Blake2.ArmB.scp s₀) d) 32 := by
      rw [hp.scr_addr (by omega)]
      exact VG.Proof.Blake2.ArmB.readW_frame f₁₂ (by
        simp only [List.mem_singleton, forall_eq]; exact Offset.disjoint_base _ h1 (by omega))
    rw [← e₁, hp.scr_addr (by omega)]
    exact VG.Proof.Blake2.ArmB.readW_frame h₃.frame (by
      simp only [List.mem_singleton, forall_eq]
      exact Region.Disjoint.sub_left hp.st_scr.symm (Offset.sub_base _ (by omega)))
  have hlo₃ : rd64 s₃.mem (VG.Proof.Blake2.ArmB.scp s₀) ctrLo = BitVec.ofNat 64 N := by
    simp only [rd64]; rw [hctr3 _ (by decide) (by decide), hctr3 _ (by decide) (by decide)]
    exact hL.lo
  have hhi₃ : s₃.mem.readW (A (VG.Proof.Blake2.ArmB.scp s₀) ctrHi) 32 = BitVec.ofNat 32 (N / 2 ^ 64) := by
    rw [hctr3 _ (by decide) (by decide)]; exact hL.hi
  have c₃ : VG.Proof.Blake2.ArmB.Ctx (VG.Proof.Blake2.ArmB.stp s₀) (VG.Proof.Blake2.ArmB.scp s₀) s₃ := c₂.of_eq (h₃.gpr _ (by decide)) (h₃.gpr _ (by decide)) h₃.wr
  refine VG.Proof.Blake2.ArmB.advance_ok c₃.r3 c₃.wV hlo₃ hhi₃ |>.mono fun s₄ ⟨r1₄, r2₄, z₄, g₄, m₄, rd₄, wr₄, sp₄⟩ => ?_
  -- Registers
  have g₃ : ∀ r, r ∉ [Reg.r1, .r2, .r4, .r5, .r6, .r7] → r ∉ VG.Proof.Blake2.ArmB.gRegs → s₄.gpr r = s.gpr r :=
    fun r ha hb => by
      have e₃ : r ∉ [Reg.r4, .r5, .r6, .r7, .r8, .r9] := fun h => hb
        ((by decide : ∀ r ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9], r ∈ gRegs) r h)
      have e₁ : r ∉ [Reg.r4, .r5, .r6, .r7] := fun h => hb
        ((by decide : ∀ r ∈ [Reg.r4, .r5, .r6, .r7], r ∈ gRegs) r h)
      rw [g₄ r ha, h₃.gpr r e₃, h₂.gpr r hb, g₁ r e₁]
  have hrd : s₄.rd = s₀.rd := by rw [rd₄, h₃.rd, h₂.rd, rd₁, hL.rd]
  have hwr : s₄.wr = s₀.wr := by rw [wr₄, h₃.wr, h₂.wr, wr₁, hL.wr]
  have hsp : s₄.sp = s₀.sp := by rw [sp₄, h₃.sp, h₂.sp, sp₁, hL.sp]
  -- Memory
  have hsub : ∀ r ∈ [VG.Proof.Blake2.ArmB.workR (VG.Proof.Blake2.ArmB.scp s₀)], ∃ r' ∈ [VG.Proof.Blake2.ArmB.stR (VG.Proof.Blake2.ArmB.stp s₀), VG.Proof.Blake2.ArmB.scrR (VG.Proof.Blake2.ArmB.scp s₀)], Region.Sub r r' :=
    fun r hr => ⟨VG.Proof.Blake2.ArmB.scrR (VG.Proof.Blake2.ArmB.scp s₀), by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)⟩
  have hsubC : ∀ r ∈ [VG.Proof.Blake2.ArmB.ctrR s₀], ∃ r' ∈ [VG.Proof.Blake2.ArmB.stR (VG.Proof.Blake2.ArmB.stp s₀), VG.Proof.Blake2.ArmB.scrR (VG.Proof.Blake2.ArmB.scp s₀)], Region.Sub r r' :=
    fun r hr => ⟨VG.Proof.Blake2.ArmB.scrR (VG.Proof.Blake2.ArmB.scp s₀), by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by simp only [ctrLo]; omega)⟩
  have hframe : Frame [VG.Proof.Blake2.ArmB.stR (VG.Proof.Blake2.ArmB.stp s₀), VG.Proof.Blake2.ArmB.scrR (VG.Proof.Blake2.ArmB.scp s₀)] s₀.mem s₄.mem := by
    rw [m₄]
    exact ((fr₁.trans (h₂.frame.sub hsub)).trans (h₃.frame.mono (by simp))).trans
      ((VG.Proof.Blake2.ArmB.ctrMem_frame hp _ N).sub hsubC)
  have hc4 : ∀ d, 128 ≤ d → d + 4 ≤ 512 → (d + 4 ≤ ctrLo ∨ ctrLo + 12 ≤ d) →
      s₄.mem.readW (A (VG.Proof.Blake2.ArmB.scp s₀) d) 32 = s.mem.readW (A (VG.Proof.Blake2.ArmB.scp s₀) d) 32 := fun d h1 h2 h3 => by
    rw [m₄, hp.scr_frame h1 h2 h3 (.inr (.inr (VG.Proof.Blake2.ArmB.ctrMem_frame hp _ N))), hctr3 d h1 h2]
  have hstate : Spec.Blake2.stateAt 64 s₄.mem (State.addr (VG.Proof.Blake2.ArmB.stp s₀)) =
      Spec.Blake2.F Spec.Blake2.b H M N (VG.Proof.Blake2.ArmB.fl s₀) := by
    rw [m₄]
    refine VG.Proof.Blake2.ArmB.stateAt_ext fitS fun k hk => ?_
    have hcs : Frame [VG.Proof.Blake2.ArmB.scrR (VG.Proof.Blake2.ArmB.scp s₀)] s₃.mem (VG.Proof.Blake2.ArmB.ctrMem s₃.mem (VG.Proof.Blake2.ArmB.scp s₀) N) :=
      (VG.Proof.Blake2.ArmB.ctrMem_frame hp _ N).sub fun r hr => ⟨VG.Proof.Blake2.ArmB.scrR (VG.Proof.Blake2.ArmB.scp s₀), by simp, by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by simp only [ctrLo]; omega)⟩
    have hws : Frame [VG.Proof.Blake2.ArmB.scrR (VG.Proof.Blake2.ArmB.scp s₀)] s.mem s₂.mem := f₁₂.sub fun r hr => ⟨VG.Proof.Blake2.ArmB.scrR (VG.Proof.Blake2.ArmB.scp s₀), by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)⟩
    rw [hp.st_frame hcs hk, h₃.done k hk, hp.st_frame hws hk, hHk k hk, h₂.vars k (by omega),
      show 64 + 8 * k = 8 * (k + 8) by omega, h₂.vars (k + 8) (by omega), VG.Proof.Blake2.ArmB.F_eq, Vector.getElem_ofFn]
    rfl
  have hcommon : VG.Proof.Blake2.ArmB.Common s₀ (i + 1) s₄ := by
    refine ⟨by rw [g₃ _ (by decide) (by decide), hL.r0], by rw [g₃ _ (by decide) (by decide), hL.r3],
      hrd, hwr, hsp, hframe, ?_, fun p hp' => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hstate, VG.Proof.Blake2.ArmB.compressBlocks_succ', ← hH, hM, hp.blk_addr hi]
    · have := VG.Proof.Blake2.ArmB.saved_off p hp'
      rw [hc4 _ this.1 (by omega) (by simp only [ctrLo]; omega)]; exact hL.saved p hp'
    · rw [m₄, VG.Proof.Blake2.ArmB.ctrMem_lo hp, show N + 128 = VG.Proof.Blake2.ArmB.t₀ s₀ + (i + 1) * 128 by rw [hN, Nat.add_mul, Nat.one_mul, Nat.add_assoc]]
    · rw [m₄, VG.Proof.Blake2.ArmB.ctrMem_hi, show N + 128 = VG.Proof.Blake2.ArmB.t₀ s₀ + (i + 1) * 128 by rw [hN, Nat.add_mul, Nat.one_mul, Nat.add_assoc]]
    · rw [hc4 _ (by decide) (by decide) (by decide)]; exact hL.hi'
    · simp only [rd64]; rw [hc4 _ (by decide) (by decide) (by decide), hc4 _ (by decide) (by decide) (by decide)]
      exact hL.f
    · simp only [rd64]; rw [hc4 _ (by decide) (by decide) (by decide), hc4 _ (by decide) (by decide) (by decide)]
      exact hL.z
  have hnb : VG.Proof.Blake2.ArmB.nb s₀ < 2 ^ 32 := (s₀.gpr .r2).isLt
  have hr2 : s₃.gpr .r2 - 1 = BitVec.ofNat 32 (VG.Proof.Blake2.ArmB.nb s₀ - (i + 1)) := by
    rw [h₃.gpr _ (by decide), h₂.gpr _ (by decide), g₁ _ (by decide), hL.r2,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  have hev : eval .ne s₄ = some (!(BitVec.ofNat 32 (VG.Proof.Blake2.ArmB.nb s₀ - (i + 1)) == 0)) := by
    rw [eval_ne, z₄, hr2]
  by_cases hlast : i + 1 = VG.Proof.Blake2.ArmB.nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon⟩
  · right
    have hne : VG.Proof.Blake2.ArmB.nb s₀ - (i + 1) ≠ 0 := by omega
    have h0 : BitVec.ofNat 32 (VG.Proof.Blake2.ArmB.nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
      exact hne h'
    refine ⟨by rw [hev]; simpa using h0, by omega, { hcommon with r1 := ?_, r2 := ?_ }⟩
    · rw [r1₄, h₃.gpr _ (by decide), h₂.gpr _ (by decide), g₁ _ (by decide), hL.r1]
      simp only [VG.Proof.Blake2.ArmB.blkAddr]
      rw [BitVec.add_assoc, show (128 : BitVec _) = BitVec.ofNat _ 128 from rfl, BitVec.ofNat_add_ofNat]
      rfl
    · rw [r2₄, hr2]

/-! ## The prologue's memory -/

theorem flag_eq (l : BitVec 32) : (VG.Proof.Blake2.ArmB.flag32 l ++ VG.Proof.Blake2.ArmB.flag32 l : BitVec 64) = VG.Proof.Blake2.ArmB.flagW 64 (l != 0) := by
  by_cases h : l = 0
  · subst h; decide
  · have h0 : l.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
    have hm : (0 - l ||| l).msb = true := by
      rw [BitVec.msb_or, BitVec.msb_eq_decide, BitVec.msb_eq_decide, BitVec.toNat_sub]
      have := l.isLt
      simp only [show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero, Bool.or_eq_true,
        decide_eq_true_eq]
      omega
    have e1 : (0 - l ||| l) >>> 31 = 1 := by
      rw [BitVec.msb_eq_decide] at hm
      simp only [decide_eq_true_eq] at hm
      apply BitVec.eq_of_toNat_eq
      have := (0 - l ||| l).isLt
      simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, show (1 : BitVec 32).toNat = 1 from rfl]
      omega
    have ht : (l != 0) = true := by simpa using h
    simp only [VG.Proof.Blake2.ArmB.flag32, e1, VG.Proof.Blake2.ArmB.flagW, ht, ite_true]
    decide

theorem setupMem_frame {s₀ : VG.Arm.State} (hp : VG.Proof.Blake2.ArmB.Pre s₀) : Frame [VG.Proof.Blake2.ArmB.scrR (VG.Proof.Blake2.ArmB.scp s₀)] s₀.mem (VG.Proof.Blake2.ArmB.setupMem s₀) := by
  have c : ∀ d : Nat, d + 4 ≤ 512 → (VG.Proof.Blake2.ArmB.scrR (VG.Proof.Blake2.ArmB.scp s₀)).Contains (VG.Proof.Blake2.ArmB.SA s₀ d) (32 / 8) :=
    fun d hd => by rw [VG.Proof.Blake2.ArmB.SA_eq hp (by omega)]; exact contains_offset hd (by have := hp.scr_fits; omega)
  have m := List.mem_singleton_self (VG.Proof.Blake2.ArmB.scrR (VG.Proof.Blake2.ArmB.scp s₀))
  have key : ∀ (l : List (Nat × BitVec 32)), (∀ p ∈ l, p.1 + 4 ≤ 512) → ∀ m₀ : Mem,
      Frame [VG.Proof.Blake2.ArmB.scrR (VG.Proof.Blake2.ArmB.scp s₀)] s₀.mem m₀ →
      Frame [VG.Proof.Blake2.ArmB.scrR (VG.Proof.Blake2.ArmB.scp s₀)] s₀.mem (l.foldl (fun m p => m.writeW (VG.Proof.Blake2.ArmB.SA s₀ p.1) p.2) m₀) := by
    intro l
    induction l with
    | nil => intro _ m₀ h; exact h
    | cons p ps ih =>
      intro hl m₀ h
      exact ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) _
        (h.writeW m _ (c p.1 (hl p (List.mem_cons_self))))
  have hl : ∀ p ∈ VG.Proof.Blake2.ArmB.setupWrites s₀, p.1 + 4 ≤ 512 := by
    intro p hp
    simp only [VG.Proof.Blake2.ArmB.setupWrites, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> exact Nat.le_of_ble_eq_true rfl
  exact key _ hl _ (Frame.refl _ _)

theorem common_zero {s₀ : VG.Arm.State} (hp : VG.Proof.Blake2.ArmB.Pre s₀) {s₁ : VG.Arm.State} (hm : s₁.mem = VG.Proof.Blake2.ArmB.setupMem s₀)
    (h0 : s₁.gpr .r0 = s₀.gpr .r0) (h3 : s₁.gpr .r3 = VG.Proof.Blake2.ArmB.scp s₀) (hrd : s₁.rd = s₀.rd)
    (hwr : s₁.wr = s₀.wr) (hsp : s₁.sp = s₀.sp) : VG.Proof.Blake2.ArmB.Common s₀ 0 s₁ := by
  have hf := VG.Proof.Blake2.ArmB.setupMem_frame hp
  have ht := (tArm s₀).isLt
  refine ⟨h0, h3, hrd, hwr, hsp, by rw [hm]; exact hf.mono (by simp), ?_, fun p hp' => ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · refine VG.Proof.Blake2.ArmB.stateAt_ext hp.st_fits fun k hk => ?_
    rw [hm, hp.st_frame hf hk, ← VG.Proof.Blake2.ArmB.stateAt_get hp.st_fits _ hk]
    rfl
  all_goals simp only [hm, rd64, A, ctrLo, ctrHi, flagOff, zeroOff]
  · simp only [VG.Impl.Blake2.Arm.B.saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) only [VG.Proof.Blake2.ArmB.setupMem, VG.Proof.Blake2.ArmB.setupWrites, List.foldl, Mem.readW_writeW_self32,
      VG.Proof.Blake2.ArmB.readW_writeW_SA hp]
  · simp (config := {decide := true}) only [VG.Proof.Blake2.ArmB.setupMem, VG.Proof.Blake2.ArmB.setupWrites, List.foldl, Mem.readW_writeW_self32,
      VG.Proof.Blake2.ArmB.readW_writeW_SA hp]
    show tArm s₀ = _
    rw [Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp (config := {decide := true}) only [VG.Proof.Blake2.ArmB.setupMem, VG.Proof.Blake2.ArmB.setupWrites, List.foldl, Mem.readW_writeW_self32,
      VG.Proof.Blake2.ArmB.readW_writeW_SA hp]
    rw [Nat.zero_mul, Nat.add_zero, Nat.div_eq_of_lt ht]; rfl
  · simp (config := {decide := true}) only [VG.Proof.Blake2.ArmB.setupMem, VG.Proof.Blake2.ArmB.setupWrites, List.foldl, Mem.readW_writeW_self32,
      VG.Proof.Blake2.ArmB.readW_writeW_SA hp]
  · simp (config := {decide := true}) only [VG.Proof.Blake2.ArmB.setupMem, VG.Proof.Blake2.ArmB.setupWrites, List.foldl, Mem.readW_writeW_self32,
      VG.Proof.Blake2.ArmB.readW_writeW_SA hp]
    exact VG.Proof.Blake2.ArmB.flag_eq _
  · simp (config := {decide := true}) only [VG.Proof.Blake2.ArmB.setupMem, VG.Proof.Blake2.ArmB.setupWrites, List.foldl, Mem.readW_writeW_self32,
      VG.Proof.Blake2.ArmB.readW_writeW_SA hp]

/-! ## The epilogue -/

set_option simprocs false in
theorem restore_ok {s₀ : VG.Arm.State} (hp : VG.Proof.Blake2.ArmB.Pre s₀) {s : VG.Arm.State} (hc : VG.Proof.Blake2.ArmB.Common s₀ (VG.Proof.Blake2.ArmB.nb s₀) s) :
    WP isa (.block VG.Impl.Blake2.Arm.B.restore) s fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ (VG.Proof.Blake2.compressArm Spec.Blake2.b).post s₀ s' := by
  have i : ∀ d, d + 4 ≤ 512 → InRegions (s.rd ++ s.wr) (State.addr (stackArg s₀ 3 + BitVec.ofNat 32 d)) 4 :=
    fun d hd => by rw [hc.rd, hc.wr]; exact hp.in_scr hd
  have i0 := i 128 (by decide); have i1 := i 132 (by decide); have i2 := i 136 (by decide)
  have i3 := i 140 (by decide); have i4 := i 144 (by decide); have i5 := i 148 (by decide)
  have i6 := i 152 (by decide); have i7 := i 156 (by decide); have i8 := i 160 (by decide)
  have g : ∀ p ∈ VG.Impl.Blake2.Arm.B.saved, s.mem.readW (State.addr (stackArg s₀ 3 + BitVec.ofNat 32 p.2)) 32 = s₀.gpr p.1 :=
    hc.saved
  simp only [VG.Impl.Blake2.Arm.B.saved, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at g
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩ := g
  have hstate := hc.state
  have hr3 := hc.r3
  apply WP.of_runBlock
  simp (config := {decide := true}) only [VG.Impl.Blake2.Arm.B.restore, VG.Impl.Blake2.Arm.B.saved, List.map_cons, List.map_nil, runBlock_cons,
    runStep_some, runBlock_nil, exec, isa, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, State.load32, hr3, i0, i1, i2, i3, i4, i5, i6, i7, i8, ite_true, ite_false,
    g0, g1, g2, g3, g4, g5, g6, g7, g8, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun r hr => ?_, hstate⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-! ## The whole function -/

theorem correct {s₀ : VG.Arm.State} (hp : VG.Proof.Blake2.ArmB.Pre s₀) :
    WP isa Impl.Blake2.Arm.B.compress s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ (VG.Proof.Blake2.compressArm Spec.Blake2.b).post s₀ s' := by
  unfold Impl.Blake2.Arm.B.compress
  refine WP.seq (WP.mono (VG.Proof.Blake2.ArmB.setup_ok hp) fun s₁ ⟨m₁, g₁, r3₁, z₁, rd₁, wr₁, sp₁⟩ => ?_)
  have hc₀ := VG.Proof.Blake2.ArmB.common_zero hp m₁ (g₁ _ (by decide)) r3₁ rd₁ wr₁ sp₁
  refine WP.seq (WP.mono (Q := VG.Proof.Blake2.ArmB.Common s₀ (VG.Proof.Blake2.ArmB.nb s₀)) ?_ fun s₂ hc => VG.Proof.Blake2.ArmB.restore_ok hp hc)
  refine WP.ite (s₀.gpr .r2 - 0 == 0) (by rw [← z₁]; rfl) (fun h => ?_) (fun h => ?_)
  · have h0 : VG.Proof.Blake2.ArmB.nb s₀ = 0 := by simp at h; simp [VG.Proof.Blake2.ArmB.nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < VG.Proof.Blake2.ArmB.nb s₀ := by
      simp only [beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → VG.Arm.State → Prop := fun m s => ∃ i, m = VG.Proof.Blake2.ArmB.nb s₀ - i ∧ i < VG.Proof.Blake2.ArmB.nb s₀ ∧ VG.Proof.Blake2.ArmB.LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval .ne s' = some false ∧ VG.Proof.Blake2.ArmB.Common s₀ (VG.Proof.Blake2.ArmB.nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (VG.Proof.Blake2.ArmB.body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, VG.Proof.Blake2.ArmB.nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩
    have hL₀ : VG.Proof.Blake2.ArmB.LInv s₀ 0 s₁ :=
      { hc₀ with
        r1 := by rw [g₁ _ (by decide)]; simp [VG.Proof.Blake2.ArmB.blkAddr]
        r2 := by rw [g₁ _ (by decide)]; simp [VG.Proof.Blake2.ArmB.nb] }
    exact WP.loop (M := isa) Inv hstep (VG.Proof.Blake2.ArmB.nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

/-! ## Verified -/

/-- The initial taint: `r0`–`r2` are public, and so are the 16 bytes of stack
arguments. -/
def τ₀ : VG.Arm.Taint.T := { regs := .ofList [.r0, .r1, .r2], flags := false, argLen := 16 }

theorem argByte_eq {s : VG.Arm.State} (hsp : s.sp.toNat + 16 ≤ 2 ^ 32) {k : Nat} (hk : k < 16) :
    VG.Arm.Taint.argByte s k = stackArgAddr s (k / 4) + BitVec.ofNat 64 (k % 4) := by
  simp only [VG.Arm.Taint.argByte, stackArgAddr]
  rw [addr_add (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2; omega

theorem agree₀ {s₁ s₂ : VG.Arm.State} (h₁ : (VG.Proof.Blake2.compressArm Spec.Blake2.b).pre s₁)
    (h₂ : (VG.Proof.Blake2.compressArm Spec.Blake2.b).pre s₂) (hpub : (VG.Proof.Blake2.compressArm Spec.Blake2.b).pub s₁ s₂) :
    VG.Arm.Taint.Agree VG.Proof.Blake2.ArmB.τ₀ s₁ s₂ := by
  obtain ⟨psp, p0, p1, p2, a0, a1, a2, a3⟩ := hpub
  have hp₁ := VG.Proof.Blake2.ArmB.pre_of _ h₁; have hp₂ := VG.Proof.Blake2.ArmB.pre_of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => (h rfl).elim, ⟨fun h => (h rfl).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨hp₁.sp_fits, ?_⟩, fun _ h => (List.not_mem_nil h).elim⟩,
    ⟨fun h => (h rfl).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨hp₂.sp_fits, ?_⟩,
      fun _ h => (List.not_mem_nil h).elim⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp,
    fun k hk => ?_⟩
  · simp only [VG.Proof.Blake2.ArmB.τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> assumption
  · have e : (⟨State.addr s₁.sp, 16⟩ : Region) = VG.Proof.Blake2.ArmB.argR s₁ := by simp [stackArgAddr]
    simp only [VG.Proof.Blake2.ArmB.τ₀, e, hp₁.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp₁.a_st
    · exact hp₁.a_scr
  · have e : (⟨State.addr s₂.sp, 16⟩ : Region) = VG.Proof.Blake2.ArmB.argR s₂ := by simp [stackArgAddr]
    simp only [VG.Proof.Blake2.ArmB.τ₀, e, hp₂.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp₂.a_st
    · exact hp₂.a_scr
  · simp only [VG.Proof.Blake2.ArmB.τ₀] at hk
    rw [VG.Proof.Blake2.ArmB.argByte_eq hp₁.sp_fits hk, VG.Proof.Blake2.ArmB.argByte_eq hp₂.sp_fits hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    have : k / 4 = 0 ∨ k / 4 = 1 ∨ k / 4 = 2 ∨ k / 4 = 3 := by omega
    rcases this with h | h | h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1
    · exact congrArg _ a2
    · exact congrArg _ a3

/-- A state satisfying the precondition (with no blocks, and the scratch space at 0). -/
def sat : VG.Arm.State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 0⟩, ⟨0x4000, 16⟩]
  wr := [⟨0x1000, 64⟩, ⟨0, 512⟩]

/-- The proof, against the ARMv7 contract the streaming functions use. -/
theorem compress_verified' :
    Verified Arm.target Impl.Blake2.Arm.B.compress (VG.Proof.Blake2.compressArm Spec.Blake2.b) := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h₁, h₂⟩ := VG.Proof.Blake2.ArmB.correct (VG.Proof.Blake2.ArmB.pre_of s hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he⟩, h₂⟩
  · exact VG.Taint.constantTime (A := VG.Arm.taint) VG.Proof.Blake2.ArmB.τ₀ (fun _ _ h₁ h₂ hpub => VG.Proof.Blake2.ArmB.agree₀ h₁ h₂ hpub)
      (by taint_decide)
  · refine ⟨VG.Proof.Blake2.ArmB.sat, rfl, rfl, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide⟩ <;>
    exact Region.disjoint_of_sep (by decide)

theorem compress_implies :
    (VG.Proof.Blake2.compressArm Spec.Blake2.b).Implies (Spec.Blake2.compressBContract Arm.abi) := by
  sig_implies [Spec.Blake2.compressBContract, Spec.Blake2.compressBSig, VG.Proof.Blake2.compressArm, tArm, Arm.abi,
    Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Spec.Blake2.blockBytes]
    [sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using VG.Proof.Blake2.ArmB.sat

/-- The proof, against the shared contract of `Spec/Blake2/Contract.lean`. -/
theorem compress_verified :
    Verified Arm.target Impl.Blake2.Arm.B.compress (Spec.Blake2.compressBContract Arm.abi) :=
  compress_verified'.of_implies VG.Proof.Blake2.ArmB.compress_implies

end VG.Proof.Blake2.ArmB

end

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.Arm.Blake2b`. -/
section

/-!
# BLAKE2b on ARMv7: the streaming functions

The generic ARMv7 streaming layer (`Proof/Blake2/Arm/Stream/`) instantiated
with BLAKE2b's parameters and its compression function (`compress_verified'`).
-/

namespace VG.Proof.Blake2.ArmB

open VG VG.Arm
open VG.Proof.Blake2.Arm.Stream (CalleeOk okB init_check_b init_verified update_verified
  finalize_verified initB_implies updateB_implies finalizeB_implies)

theorem calleeB : CalleeOk Spec.Blake2.b Impl.Blake2.Arm.B.compress :=
  ⟨VG.Proof.Blake2.ArmB.compress_verified', by lit_decide⟩

theorem initB_verified :
    Verified Arm.target (Impl.Blake2.Arm.Stream.init Spec.Blake2.b) (Spec.Blake2.initBContract Arm.abi) :=
  init_verified okB init_check_b initB_implies

theorem updateB_verified :
    Verified Arm.target
      (Impl.Blake2.Arm.Stream.update (w := 64) "vg_blake2b_compress" Impl.Blake2.Arm.B.compress)
      (Spec.Blake2.updateBScratchContract Arm.abi 16) :=
  update_verified okB VG.Proof.Blake2.ArmB.calleeB updateB_implies

theorem finalizeB_verified :
    Verified Arm.target
      (Impl.Blake2.Arm.Stream.finalize (w := 64) "vg_blake2b_compress" Impl.Blake2.Arm.B.compress)
      (Spec.Blake2.finalizeBScratchContract Arm.abi 16) :=
  finalize_verified okB VG.Proof.Blake2.ArmB.calleeB finalizeB_implies

/-! ## `update` and `finalize` with their working space in a frame of their own

The theorems above are of the streaming functions with their working space
as an argument (`update_scratch`, `finalize_scratch`); `update` and
`finalize` run them in a frame that allocates it (`Verified.stackScratch`).
-/

/-- A state satisfying `update`'s precondition. -/
def updateFrameSat : Arm.State :=
  { Proof.Blake2.Arm.Stream.updateSat 64 with rd := [⟨0x2000, 0⟩, ⟨0x5000, 8⟩], wr := [⟨0x1000, 192⟩] }

theorem updateB_framed : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratch 592 2 (Impl.Blake2.Arm.Stream.update (w := 64) "vg_blake2b_compress" Impl.Blake2.Arm.B.compress))
    (Spec.Blake2.updateBContract Arm.abi (16 + 592)) :=
  Arm.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 72) (stack := 16) (bytes := 592) (m := 2)
    VG.Proof.Blake2.ArmB.updateB_verified (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Blake2.updateBPost_local _)
    (by implies_sat [Spec.Blake2.updateBContract, Spec.Blake2.updateBSig, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [updateFrameSat, Proof.Blake2.Arm.Stream.updateSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
        Mem.read] using VG.Proof.Blake2.ArmB.updateFrameSat)

/-- A state satisfying `finalize`'s precondition. -/
def finalizeFrameSat : Arm.State :=
  { Proof.Blake2.Arm.Stream.finalizeSat 64 with rd := [⟨0x5000, 4⟩], wr := [⟨0x1000, 192⟩, ⟨0x2000, 64⟩] }

theorem finalizeB_framed : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratch 592 1 (Impl.Blake2.Arm.Stream.finalize (w := 64) "vg_blake2b_compress" Impl.Blake2.Arm.B.compress))
    (Spec.Blake2.finalizeBContract Arm.abi (16 + 592)) :=
  Arm.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 72) (stack := 16) (bytes := 592) (m := 1)
    VG.Proof.Blake2.ArmB.finalizeB_verified (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Blake2.finalizeBPost_local _)
    (by implies_sat [Spec.Blake2.finalizeBContract, Spec.Blake2.finalizeBSig, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [finalizeFrameSat, Proof.Blake2.Arm.Stream.finalizeSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
        Mem.read] using VG.Proof.Blake2.ArmB.finalizeFrameSat)

end VG.Proof.Blake2.ArmB

end
