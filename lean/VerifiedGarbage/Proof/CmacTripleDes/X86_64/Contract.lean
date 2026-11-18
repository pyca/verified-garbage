module

public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.TCB.X86_64.Isa
public import VerifiedGarbage.Spec.Cmac
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.Framework.X86_64.Spill
public import VerifiedGarbage.Impl.CmacTripleDes.X86_64
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.RoundLit
public import VerifiedGarbage.Proof.TripleDes.SboxTables
public import VerifiedGarbage.Proof.CmacTripleDes.Block
import VerifiedGarbage.Proof.CmacTripleDes.IndexLit
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.CmacTripleDes.Des
public import VerifiedGarbage.Proof.CmacTripleDes.Rows
public import VerifiedGarbage.Proof.Framework.X86_64.Linear
public import VerifiedGarbage.Proof.Framework.Bitslice.Rows
public import VerifiedGarbage.Impl.CmacTripleDes.X86_64.Round
import VerifiedGarbage.Proof.Framework.Taint

/-! ### `CmacTripleDes.X86_64.Block`, which the modules that import this one used -/

section

/-! ### `CmacTripleDes.X86_64.Round`, which only this module used -/

section

/-!
# A DES round on x86-64

The round's three parts are checked by evaluation (`Straight.check`): the
broadcast inputs (`inputs`) and the output (`output`), which only move,
mask and XOR bits, over the lane domain; the S-boxes (`sboxes`), which
combine words bitwise with constants that differ by position, over the row
domain (`Bitslice.rows`), on all 64 values of a box's input at once.
`round_ok` composes them: `R` and `L ⊕ f(R, K)`.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.CmacTripleDes VG.Impl.CmacTripleDes.X86_64

/-- The round's memory: the broadcast inputs in slots 0–5 at `r15`, and the
round key at `r14`. -/
def rCfg : Cfg := { base := .r15, slots := 6, ext := .r14, exts := 1 }

/-- Slot `k` of the scratch buffer. -/
abbrev slotW (s : State) (k : Nat) : BitVec 64 := s.mem.readW (wordAddr (s.gpr .r15) k) 64

/-- The round key's word. -/
abbrev keyW (s : State) : BitVec 64 := s.mem.readW (wordAddr (s.gpr .r14) 0) 64

/-! ## The inputs -/

/-- Bit `p` of slot `t`: in lane `p / 6`, below its fifth bit, bit `t` of
the box's input, `R`'s bit (atom `0 … 63`) XOR the key's (atom `64 …`). -/
def inG (t p : Nat) : List Nat :=
  if p < 48 ∧ p % 6 < 4 then [expSrc (6 * (p / 6) + t), 64 + 6 * (p / 6) + t] else []

def inPost (e : Env (Nat × Nat)) : Bool :=
  (List.range 6).all fun t => e.slot t == some (outWord (inG t))

theorem inputs_check :
    check (lanes 64 7) rCfg (linExt 1) inputs (linEnv [(.r13, 0)]) inPost = true := by
  lit_decide

theorem inG_lt : ∀ t < 6, ∀ p < 64, ∀ a ∈ inG t p, a < 2 ^ 7 := by lit_decide

/-- The registers the round keeps. -/
def kept : List Reg := [.rbx, .rbp, .rsp, .r10, .r11, .r14, .r15]

theorem inputs_kept :
    (.r12 :: .r13 :: kept).all (fun r => inputs.all fun i => i.dst != some r) = true := by
  lit_decide

/-- The inputs of `inputs`: `R` and the round key. -/
def inW (s : State) (i : Nat) : BitVec 64 := if i = 0 then s.gpr .r13 else keyW s

theorem inputs_ok {s : State} (hok : Ok rCfg s) :
    ∃ s', runBlock isa inputs s = some s' ∧
      (∀ t < 6, ∀ p < 64, (slotW s' t).getLsbD p = xorBits (inW s) (inG t p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ .r12 :: .r13 :: kept, s'.gpr r = s.gpr r) ∧
      Frame [slotRegion rCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ inputs_check
  have hrel : Rel (LaneRel 7 (assign (inW s) (2 ^ 7))) rCfg (linExt 1) (linEnv [(.r13, 0)]) s := by
    refine ⟨fun r a h => ?_, (fun _ _ _ h => by cases h), fun j a hj h => ?_⟩
    · simp only [linEnv, List.find?, Option.map_eq_some_iff] at h
      split at h
      · rename_i hr
        simp only [beq_iff_eq] at hr; subst hr
        simp only [Option.some.injEq, exists_eq_left'] at h; subst h
        exact inWord_rel (inW s) (i := 0) (by decide)
      · simp at h
    · simp only [rCfg] at hj
      obtain rfl : j = 0 := by omega_using [hj]
      simp only [linExt, Option.some.injEq] at h; subst h
      exact inWord_rel (inW s) (i := 1) (by decide)
  obtain ⟨s', hs', p⟩ := run lanes_sound hok hrel he
  refine ⟨s', hs', fun t ht q hq => ?_, p.rd, p.wr, fun r hr => p.other r ?_, p.frame⟩
  · have h := List.all_eq_true.mp hpost t (List.mem_range.mpr ht)
    simp only [beq_iff_eq] at h
    exact outWord_rel (inG_lt t ht) (p.rel.slot t _ (by simp only [rCfg]; omega_using [ht]) h) q hq
  · rw [List.all_eq_true.mp inputs_kept r hr]; decide

/-! ## The S-boxes -/

/-- Slot `t` on row `c`, at every position: bit `t` of `c`. -/
def rowIn (t : Nat) : Nat := rowsOf 64 (fun c => c.testBit t) 64

def sbEnv : Env Nat := { reg := fun _ => none, slot := fun t => if t < 6 then some (rowIn t) else none }

/-- At bit `6 (7 - i) + off i b`, output bit `b` of box `i`, on every row. -/
def sbPost (e : Env Nat) : Bool :=
  match e.reg .rax with
  | some F => (List.range 8).all fun i => (List.range 4).all fun b => (List.range 64).all fun c =>
      F.testBit (64 * c + (6 * (7 - i) + off i b)) == (Proof.TripleDes.outputTable i b).testBit c
  | none => false

theorem sboxes_check : check (rows 64 6) rCfg (fun _ => none) sboxes sbEnv sbPost = true := by
  lit_decide

theorem sboxes_kept :
    (.r12 :: .r13 :: kept).all (fun r => sboxes.all fun i => i.dst != some r) = true := by
  lit_decide

/-- The input of the box whose lane holds bit `p`, from bit `p` of the slots. -/
def boxIn (s : State) (p : Nat) : BitVec 6 := ofBits 6 fun t => (slotW s t).getLsbD p

theorem sboxes_ok {s : State} (hok : Ok rCfg s) :
    ∃ s', runBlock isa sboxes s = some s' ∧
      (∀ i < 8, ∀ b < 4, (s'.gpr .rax).getLsbD (6 * (7 - i) + off i b) =
        (Spec.TripleDes.sBox i (boxIn s (6 * (7 - i) + off i b))).getLsbD b) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ .r12 :: .r13 :: kept, s'.gpr r = s.gpr r) ∧
      Frame [slotRegion rCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ sboxes_check
  obtain ⟨F, hF, hout⟩ : ∃ F, e'.reg .rax = some F ∧ ∀ i < 8, ∀ b < 4, ∀ c < 64,
      F.testBit (64 * c + (6 * (7 - i) + off i b)) = (Spec.TripleDes.sBox i (BitVec.ofNat 6 c)).getLsbD b := by
    simp only [sbPost] at hpost
    split at hpost
    · rename_i F hF
      refine ⟨F, hF, fun i hi b hb c hc => ?_⟩
      have := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hpost i
        (List.mem_range.mpr hi)) b (List.mem_range.mpr hb)) c (List.mem_range.mpr hc)
      rw [← Proof.TripleDes.testBit_outputTable hc]
      simpa using this
    · cases hpost
  have key : ∀ p < 64, ∃ s', runBlock isa sboxes s = some s' ∧
      Post (RowRel p (boxIn s p).toNat) rCfg (fun _ => none) e' s s'
        (fun r => (sboxes.all fun i => i.dst != some r) = false) := by
    intro p hp
    refine run (rows_sound hp (boxIn s p).isLt) hok
      ⟨fun r a h => by simp [sbEnv] at h, fun t a ht h => ?_, fun _ _ _ h => by cases h⟩ he
    simp only [sbEnv] at h
    split at h
    · rename_i ht6
      cases h
      show (rowIn t).testBit (64 * (boxIn s p).toNat + p) = (slotW s t).getLsbD p
      have hc := (boxIn s p).isLt
      rw [rowIn, testBit_rowsOf, decide_eq_true (by omega_using [hp] : 64 * (boxIn s p).toNat + p < 64 * 64),
        Bool.true_and, show (64 * (boxIn s p).toNat + p) / 64 = (boxIn s p).toNat by omega_using [hp],
        BitVec.testBit_toNat, boxIn, getLsbD_ofBits, decide_eq_true ht6, Bool.true_and]
    · cases h
  obtain ⟨s', hs', p₀⟩ := key 0 (by omega_using [])
  refine ⟨s', hs', fun i hi b hb => ?_, p₀.rd, p₀.wr, fun r hr => p₀.other r ?_, p₀.frame⟩
  · have hp : 6 * (7 - i) + off i b < 64 := by revert i b; decide
    obtain ⟨s'', hs'', p₁⟩ := key _ hp
    obtain rfl := run_unique hs'' hs'
    have h := p₁.rel.reg .rax F hF
    simp only [RowRel] at h
    rw [← h, hout i hi b hb _ (boxIn s _).isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [List.all_eq_true.mp sboxes_kept r hr]; decide

/-! ## The output -/

/-- No memory. -/
def oCfg : Cfg := { base := .r15, slots := 0, ext := .r14, exts := 0 }

/-- `r12`: `R` (input word 2). -/
def oG12 (p : Nat) : List Nat := [128 + p]

/-- `r13`: bit `j` of `L` (input word 1) XOR, for `j < 32`, the S-boxes' bit
`pSrc j` (in `rax`, input word 0). -/
def oG13 (p : Nat) : List Nat := if p < 32 then [outPos (pSrc p), 64 + p] else [64 + p]

def oIns : List (Reg × Nat) := [(.rax, 0), (.r12, 1), (.r13, 2)]

theorem output_check :
    check (lanes 64 8) oCfg (linExt 3) output (linEnv oIns) (linPost 8 [(.r12, oG12), (.r13, oG13)]) = true := by
  lit_decide

theorem output_kept : kept.all (fun r => output.all fun i => i.dst != some r) = true := by
  lit_decide

/-- The inputs of `output`. -/
def oW (s : State) (i : Nat) : BitVec 64 :=
  if i = 0 then s.gpr .rax else if i = 1 then s.gpr .r12 else s.gpr .r13

theorem oCfg_ok (s : State) : Ok oCfg s :=
  ⟨fun k hk => absurd hk (by simp [oCfg]), fun k hk => absurd hk (by simp [oCfg]), by decide,
    fun k hk => absurd hk (by simp [oCfg])⟩

theorem output_ok (s : State) :
    ∃ s', runBlock isa output s = some s' ∧
      (∀ p < 64, (s'.gpr .r12).getLsbD p = xorBits (oW s) (oG12 p)) ∧
      (∀ p < 64, (s'.gpr .r13).getLsbD p = xorBits (oW s) (oG13 p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem := by
  obtain ⟨s', hs', hout, hrd, hwr, hoth, hfr⟩ := linear_ok output_check (oCfg_ok s) (oW s)
    (fun r i hri => by
      simp only [oIns, List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hri
      rcases hri with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, rfl⟩)
    (fun j hj => absurd hj (by simp [oCfg]))
  refine ⟨s', hs', hout .r12 oG12 (by simp), hout .r13 oG13 (by simp), hrd, hwr,
    fun r hr => hoth r (List.all_eq_true.mp output_kept r hr), ?_⟩
  funext a
  exact hfr a fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [slotRegion, oCfg, Region.Contains]

/-! ## The round -/

theorem runBlock_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil]; rfl
  | cons i is ih =>
    rw [List.cons_append, runBlock_cons, runBlock_cons]
    cases exec i s with
    | none => rfl
    | some s' => rw [runStep_some, runStep_some, ih]

theorem expSrc_lt : ∀ q < 48, expSrc q < 32 := by lit_decide

/-- The box inputs that `inputs` broadcasts. -/
theorem boxIn_eq {s s₁ : State}
    (h : ∀ t < 6, ∀ p < 64, (slotW s₁ t).getLsbD p = xorBits (inW s) (inG t p))
    {i o : Nat} (hi : i < 8) (ho : o < 4) :
    boxIn s₁ (6 * (7 - i) + o) = chunk ((s.gpr .r13).setWidth 32) ((keyW s).setWidth 48) i := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  have hE := expSrc_lt (6 * (7 - i) + t) (by omega_using [ht])
  rw [boxIn, getLsbD_ofBits, decide_eq_true ht, Bool.true_and, h t ht _ (by omega_using [ho]),
    getLsbD_chunk _ _ hi ht, inG, ite_eq_left (by omega_using [ho]), show (6 * (7 - i) + o) / 6 = 7 - i by omega_using [ho]]
  simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, inW, BitVec.getLsbD_setWidth,
    Nat.div_eq_of_lt (show expSrc (6 * (7 - i) + t) < 64 by omega_using [hE]),
    Nat.mod_eq_of_lt (show expSrc (6 * (7 - i) + t) < 64 by omega_using [hE]),
    show (64 + 6 * (7 - i) + t) / 64 = 1 by omega_using [ht], show (64 + 6 * (7 - i) + t) % 64 = 6 * (7 - i) + t by omega_using [ht],
    hE, show 6 * (7 - i) + t < 48 by omega_using [ht], decide_true, Bool.true_and, ite_true]
  rfl

theorem off_lt : ∀ i < 8, ∀ b < 4, off i b < 4 := by decide

theorem pSrc_lt : ∀ j < 32, pSrc j < 32 := by lit_decide

/-- One round: `(L, R) := (R, L ⊕ f(R, K))` on the low 32 bits of `r12` and
`r13`, with the round key the low 48 bits of `[r14]`. -/
theorem round_ok {s : State} (hok : Ok rCfg s) :
    ∃ s', runBlock isa round s = some s' ∧
      s'.gpr .r12 = s.gpr .r13 ∧
      (s'.gpr .r13).setWidth 32 = (s.gpr .r12).setWidth 32 ^^^
        Spec.TripleDes.roundFunction ((s.gpr .r13).setWidth 32) ((keyW s).setWidth 48) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Frame [slotRegion rCfg s] s.mem s'.mem := by
  obtain ⟨s₁, h₁, hx, rd₁, wr₁, k₁, f₁⟩ := inputs_ok hok
  have hok₁ : Ok rCfg s₁ := hok.congr (k₁ .r15 (by simp [kept])) (k₁ .r14 (by simp [kept])) rd₁ wr₁
  obtain ⟨s₂, h₂, hy, rd₂, wr₂, k₂, f₂⟩ := sboxes_ok hok₁
  obtain ⟨s₃, h₃, o12, o13, rd₃, wr₃, k₃, m₃⟩ := output_ok s₂
  have r12₂ : s₂.gpr .r12 = s.gpr .r12 := (k₂ .r12 (by simp)).trans (k₁ .r12 (by simp))
  have r13₂ : s₂.gpr .r13 = s.gpr .r13 := (k₂ .r13 (by simp)).trans (k₁ .r13 (by simp))
  refine ⟨s₃, ?_, ?_, ?_, rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁),
    fun r hr => (k₃ r hr).trans ((k₂ r (by simp [hr])).trans (k₁ r (by simp [hr]))), ?_⟩
  · rw [round, runBlock_append, runBlock_append, h₁, Option.bind_some, h₂, Option.bind_some, h₃]
  · apply BitVec.eq_of_getLsbD_eq
    intro p hp
    rw [o12 p hp, oG12]
    simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, oW,
      show (128 + p) / 64 = 2 by omega_using [hp], show (128 + p) % 64 = p by omega_using [hp]]
    rw [ite_eq_right (by decide), ite_eq_right (by decide), r13₂]
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have hu := pSrc_lt j hj
    have hi : 7 - pSrc j / 4 < 8 := by omega_using []
    have hb : pSrc j % 4 < 4 := by omega_using []
    have ho := off_lt _ hi _ hb
    have hpos : outPos (pSrc j) = 6 * (7 - (7 - pSrc j / 4)) + off (7 - pSrc j / 4) (pSrc j % 4) := by
      rw [outPos, show 7 - (7 - pSrc j / 4) = pSrc j / 4 by omega_using [hu]]
    rw [BitVec.getLsbD_setWidth, decide_eq_true hj, Bool.true_and, o13 j (by omega_using [hj]), oG13, ite_eq_left hj,
      BitVec.getLsbD_xor, BitVec.getLsbD_setWidth, decide_eq_true hj, Bool.true_and,
      getLsbD_roundFunction _ _ hj]
    simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, oW]
    rw [Nat.div_eq_of_lt (show outPos (pSrc j) < 64 by omega_using [ho, hpos]), Nat.mod_eq_of_lt (show outPos (pSrc j) < 64 by omega_using [ho, hpos]),
      show (64 + j) / 64 = 1 by omega_using [hj], show (64 + j) % 64 = j by omega_using [hj], ite_eq_left rfl, ite_eq_right (by decide),
      ite_eq_left rfl, r12₂, hpos, hy _ hi _ hb, boxIn_eq hx hi ho, Bool.xor_comm]
  · have hr : slotRegion rCfg s₁ = slotRegion rCfg s := by
      simp only [slotRegion]; rw [show rCfg.base = .r15 from rfl, k₁ .r15 (by simp [kept])]
    rw [hr] at f₂
    rw [m₃]; exact f₁.trans f₂

end VG.Proof.CmacTripleDes.X86_64

end

end

/-!
# TDEA on x86-64: the passes and the block

`block` encrypts the 64-bit block in `rax` with the key schedule at `r14`
(`block_ok`): `IP` into `r12` and `r13`, three passes of sixteen rounds
(`pass_ok`, the round keys `rbx` bytes apart, the halves exchanged after
each pass), and `IP⁻¹`. During the block, `r14` points to slot
`kpos p j` of the key schedule before round `j` of pass `p`.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.X86_64.Straight VG.Bitslice VG.Impl.CmacTripleDes
  VG.Impl.CmacTripleDes.X86_64 VG.Proof.CmacTripleDes

/-- What the block needs: the key schedule at `r14` readable, and the slots
0–5 of the scratch buffer at `r15` writable, apart from it. -/
structure BlockPre (s : State) : Prop where
  sched : ∃ R ∈ s.rd ++ s.wr, R.base = s.gpr .r14 ∧ 384 ≤ R.len ∧ R.len < 2 ^ 64
  scr : ∃ R ∈ s.wr, R.base = s.gpr .r15 ∧ 48 ≤ R.len ∧ R.len < 2 ^ 64
  disj : Region.Disjoint ⟨s.gpr .r15, 48⟩ ⟨s.gpr .r14, 384⟩

/-- The slots of the broadcast inputs. -/
abbrev xR (s₀ : State) : Region := ⟨s₀.gpr .r15, 48⟩

/-- What the block keeps. -/
structure Same (s₀ s : State) : Prop where
  r15 : s.gpr .r15 = s₀.gpr .r15
  rbp : s.gpr .rbp = s₀.gpr .rbp
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [xR s₀] s₀.mem s.mem

/-- The key schedule. -/
abbrev sch (s₀ : State) : Spec.TripleDes.Schedule := Spec.TripleDes.scheduleAt s₀.mem (s₀.gpr .r14)

theorem wordAddr_zero (a : Addr) : wordAddr a 0 = a := by simp [wordAddr]

theorem ok_at {s₀ s : State} (hp : BlockPre s₀) (h : Same s₀ s) {n : Nat} (hn : n < 48)
    (hk : s.gpr .r14 = s₀.gpr .r14 + BitVec.ofNat 64 (8 * n)) : Ok rCfg s := by
  obtain ⟨R, hR, hRb, hRl, hRw⟩ := hp.sched
  obtain ⟨X, hX, hXb, hXl, hXw⟩ := hp.scr
  refine ⟨fun k hk' => ?_, fun k hk' => ?_, by decide, fun k hk' j hj => ?_⟩
  · rw [h.wr]
    exact ⟨X, hX, contains_word (off := 0) (by show s.gpr .r15 = _; rw [h.r15, ← hXb]; simp)
      (by simp only [rCfg] at hk'; omega_arith) hXl hXw⟩
  · simp only [rCfg] at hk'
    obtain rfl : k = 0 := by omega_arith
    rw [h.rd, h.wr]
    exact ⟨R, hR, contains_word (off := 8 * n) (by show s.gpr .r14 = _; rw [hk, hRb]) (by omega_arith) hRl hRw⟩
  · simp only [rCfg] at hk' hj
    obtain rfl : j = 0 := by omega_arith
    rw [show rCfg.base = .r15 from rfl, show rCfg.ext = .r14 from rfl, h.r15, hk, wordAddr_zero]
    exact hp.disj.sep (slot_contains _ hk' (by decide)) (Offset.contains_base _ (by omega_arith) (by omega_arith))

theorem key_at {s₀ s : State} (hp : BlockPre s₀) (h : Same s₀ s) {n : Nat} (hn : n < 48)
    (hk : s.gpr .r14 = s₀.gpr .r14 + BitVec.ofNat 64 (8 * n)) : keyW s = (sch s₀).getD n 0 := by
  rw [scheduleAt_getD _ _ hn, keyW, wordAddr_zero, hk]
  refine h.frame.readW (r := ⟨s₀.gpr .r14 + BitVec.ofNat 64 (8 * n), 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact (hp.disj.sub_right (Offset.sub_base _ (by omega_arith))).symm

/-! ## The rounds of a pass -/

theorem roundTail_ok (s : State) :
    ∃ s', runBlock isa roundTail s = some s' ∧
      s'.gpr .r14 = s.gpr .r14 + s.gpr .rbx ∧ s'.gpr .r11 = s.gpr .r11 - 1 ∧
      s'.zf = some ((s.gpr .r11 - 1) == 0) ∧ (∀ r, r ≠ .r14 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, BitVec.reduceSignExtend, roundTail, runBlock_cons, runStep_some, runBlock_nil, exec,
      execAlu, readSrc, Option.bind_some, gpr_setReg, gpr_arithFlags]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg]
  · exact gpr_setReg_self _ _ _
  · rw [zf_setReg, zf_arithFlags]; simp
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]

theorem ofNat_sub_one {k : Nat} (hk : 1 ≤ k) (hk' : k < 2 ^ 64) :
    BitVec.ofNat 64 k - 1 = BitVec.ofNat 64 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_arith

theorem ofNat_beq_zero {k : Nat} (hk : k < 2 ^ 64) : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
    show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]

/-- The key schedule's slot before round `j` of pass `p`. -/
def kpos (p j : Nat) : Nat := if p % 2 = 1 then 16 * p + 15 - j else 16 * p + j

/-- The distance from one round key to the next in pass `p`. -/
def stride (p : Nat) : BitVec 64 := if p % 2 = 1 then BitVec.ofNat 64 (2 ^ 64 - 8) else BitVec.ofNat 64 8

theorem kpos_succ_addr (a : Addr) {p j : Nat} (hp : p < 3) (hj : j < 16) :
    a + BitVec.ofNat 64 (8 * kpos p j) + stride p = a + BitVec.ofNat 64 (8 * kpos p (j + 1)) := by
  rw [BitVec.add_assoc, stride, kpos, kpos]
  congr 1
  split
  · rename_i hodd
    rw [← BitVec.ofNat_add]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_arith
  · rw [← BitVec.ofNat_add]
    congr 1

/-- After `j` rounds of pass `p`, from the halves `lr`. -/
structure PInv (s₀ : State) (p : Nat) (lr : BitVec 32 × BitVec 32) (j : Nat) (s : State) : Prop where
  same : Same s₀ s
  r14 : s.gpr .r14 = s₀.gpr .r14 + BitVec.ofNat 64 (8 * kpos p j)
  rbx : s.gpr .rbx = stride p
  r10 : s.gpr .r10 = BitVec.ofNat 64 (3 - p)
  r11 : s.gpr .r11 = BitVec.ofNat 64 (16 - j)
  halves : ((s.gpr .r12).setWidth 32, (s.gpr .r13).setWidth 32) = rounds (passKeys (sch s₀) p) j lr

theorem kpos_lt {p j : Nat} (hp : p < 3) (hj : j < 16) : kpos p j < 48 := by
  simp only [kpos]; split <;> omega_arith

theorem passKeys_at (s₀ : State) {p j : Nat} (hj : j < 16) :
    passKeys (sch s₀) p j = ((sch s₀).getD (kpos p j) 0).setWidth 48 := by
  rw [passKeys_eq _ hj, kpos]
  by_cases h : p % 2 = 1
  · rw [ite_eq_left h, ite_eq_left h, show 16 * p + (15 - j) = 16 * p + 15 - j by omega_arith]
  · rw [ite_eq_right h, ite_eq_right h]

/-- One round of pass `p`. -/
theorem roundStep_ok {s₀ : State} (hp : BlockPre s₀) {p : Nat} (hp3 : p < 3) {lr : BitVec 32 × BitVec 32}
    {j : Nat} (hj : j < 16) {s : State} (h : PInv s₀ p lr j s) :
    WP isa (.block (round ++ roundTail)) s fun s' =>
      s'.zf = some (decide (j + 1 = 16)) ∧ PInv s₀ p lr (j + 1) s' := by
  rw [WP.block_append_iff]
  obtain ⟨s₁, h₁, e12, e13, rd₁, wr₁, k₁, f₁⟩ := round_ok (ok_at hp h.same (kpos_lt hp3 hj) h.r14)
  refine WP.of_runBlock ⟨s₁, h₁, WP.of_runBlock ?_⟩
  obtain ⟨s₂, h₂, t14, t11, tzf, tk, tm, trd, twr⟩ := roundTail_ok s₁
  have kk : ∀ r ∈ kept, s₁.gpr r = s.gpr r := k₁
  refine ⟨s₂, h₂, ?_, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [tzf, kk .r11 (by simp [kept]), h.r11, ofNat_sub_one (by omega_arith) (by omega_arith),
      ofNat_beq_zero (by omega_arith)]
    congr 1
    exact decide_eq_decide.mpr (by omega_arith)
  · rw [tk .r15 (by decide) (by decide), kk .r15 (by simp [kept]), h.same.r15]
  · rw [tk .rbp (by decide) (by decide), kk .rbp (by simp [kept]), h.same.rbp]
  · rw [tk .rsp (by decide) (by decide), kk .rsp (by simp [kept]), h.same.rsp]
  · rw [trd, rd₁, h.same.rd]
  · rw [twr, wr₁, h.same.wr]
  · rw [tm]
    have hr : slotRegion rCfg s = xR s₀ := by
      simp only [slotRegion, xR]; rw [show rCfg.base = .r15 from rfl, h.same.r15]; rfl
    rw [hr] at f₁
    exact h.same.frame.trans f₁
  · rw [t14, kk .r14 (by simp [kept]), kk .rbx (by simp [kept]), h.r14, h.rbx, kpos_succ_addr _ hp3 hj]
  · rw [tk .rbx (by decide) (by decide), kk .rbx (by simp [kept]), h.rbx]
  · rw [tk .r10 (by decide) (by decide), kk .r10 (by simp [kept]), h.r10]
  · rw [t11, kk .r11 (by simp [kept]), h.r11, ofNat_sub_one (by omega_arith) (by omega_arith)]
    congr 1
  · rw [rounds_succ, ← h.halves, tk .r12 (by decide) (by decide), tk .r13 (by decide) (by decide), e12, e13,
      key_at hp h.same (kpos_lt hp3 hj) h.r14, passKeys_at s₀ hj]

/-- Pass `p`: sixteen rounds from the halves `lr`. -/
theorem pass_ok {s₀ : State} (hp : BlockPre s₀) {p : Nat} (hp3 : p < 3) {lr : BitVec 32 × BitVec 32}
    {s : State} (h : Same s₀ s) (h14 : s.gpr .r14 = s₀.gpr .r14 + BitVec.ofNat 64 (8 * kpos p 0))
    (hbx : s.gpr .rbx = stride p) (h10 : s.gpr .r10 = BitVec.ofNat 64 (3 - p))
    (hlr : ((s.gpr .r12).setWidth 32, (s.gpr .r13).setWidth 32) = lr) :
    WP isa pass s (PInv s₀ p lr 16) := by
  refine WP.seq (WP.of_runBlock ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some]; rfl, ?_⟩)
  have g : ∀ r, r ≠ .r11 → (s.setReg32 .r11 (16 : BitVec 32)).gpr r = s.gpr r := fun r hr => by
    simp [State.setReg32, gpr_setReg, hr]
  have h0 : PInv s₀ p lr 0 (s.setReg32 .r11 (16 : BitVec 32)) :=
    ⟨⟨by rw [g _ (by decide), h.r15], by rw [g _ (by decide), h.rbp], by rw [g _ (by decide), h.rsp],
      h.rd, h.wr, h.frame⟩, by rw [g _ (by decide), h14], by rw [g _ (by decide), hbx],
      by rw [g _ (by decide), h10], by simp [State.setReg32, gpr_setReg],
      by rw [g _ (by decide), g _ (by decide), hlr]; rfl⟩
  refine WP.loop (M := isa) (body := .block (round ++ roundTail)) (c := .ne) (Q := PInv s₀ p lr 16)
    (fun (n : Nat) (t : State) => ∃ j, n = 16 - j ∧ j < 16 ∧ PInv s₀ p lr j t) ?_ 16 _ ⟨0, rfl, by decide, h0⟩
  rintro n t ⟨j, rfl, hj, ht⟩
  refine WP.mono (roundStep_ok hp hp3 hj ht) fun t' ⟨zf', h'⟩ => ?_
  by_cases hz : j + 1 = 16
  · left
    refine ⟨by simp [X86_64.eval, zf', hz], ?_⟩
    rwa [hz] at h'
  · right
    exact ⟨by simp [X86_64.eval, zf', hz], 16 - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, h'⟩

/-! ## The passes -/

theorem passTail_ok (s : State) :
    ∃ s', runBlock isa passTail s = some s' ∧
      s'.gpr .r14 = s.gpr .r14 + (BitVec.ofNat 64 128 - s.gpr .rbx) ∧ s'.gpr .rbx = 0 - s.gpr .rbx ∧
      s'.gpr .r12 = s.gpr .r13 ∧ s'.gpr .r13 = s.gpr .r12 ∧ s'.gpr .r10 = s.gpr .r10 - 1 ∧
      s'.zf = some ((s.gpr .r10 - 1) == 0) ∧
      (∀ r, r ∉ [Reg.rax, .rbx, .r10, .r12, .r13, .r14] → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, BitVec.reduceSignExtend, passTail, runBlock_cons, runStep_some, runBlock_nil, exec,
      execAlu, readSrc, readSrc32, Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags,
      State.setReg32]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · rw [zf_setReg, zf_arithFlags]; simp
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]

/-- After `p` passes, from the block `x`. -/
structure OInv (s₀ : State) (x : BitVec 64) (p : Nat) (s : State) : Prop where
  same : Same s₀ s
  r14 : s.gpr .r14 = s₀.gpr .r14 + BitVec.ofNat 64 (8 * kpos p 0)
  rbx : s.gpr .rbx = stride p
  r10 : s.gpr .r10 = BitVec.ofNat 64 (3 - p)
  halves : ((s.gpr .r12).setWidth 32, (s.gpr .r13).setWidth 32) = passes (sch s₀) p (split (Spec.TripleDes.permute Spec.TripleDes.ip x))

theorem kpos_tail_addr (a : Addr) {p : Nat} (hp : p < 3) :
    a + BitVec.ofNat 64 (8 * kpos p 16) + (BitVec.ofNat 64 128 - stride p) =
      a + BitVec.ofNat 64 (8 * kpos (p + 1) 0) := by
  rw [BitVec.add_assoc]
  congr 1
  rcases (by omega_arith : p = 0 ∨ p = 1 ∨ p = 2) with rfl | rfl | rfl <;> decide

theorem stride_succ {p : Nat} (hp : p < 3) : 0 - stride p = stride (p + 1) := by
  rcases (by omega_arith : p = 0 ∨ p = 1 ∨ p = 2) with rfl | rfl | rfl <;> decide

/-- One pass and the exchange after it. -/
theorem passBody_ok {s₀ : State} (hp : BlockPre s₀) {x : BitVec 64} {p : Nat} (hp3 : p < 3) {s : State}
    (h : OInv s₀ x p s) :
    WP isa (.seq pass (.block passTail)) s fun s' =>
      s'.zf = some (decide (p + 1 = 3)) ∧ OInv s₀ x (p + 1) s' := by
  refine WP.seq (WP.mono (pass_ok hp hp3 h.same h.r14 h.rbx h.r10 h.halves) fun s₁ h₁ => ?_)
  obtain ⟨s₂, h₂, t14, tbx, t12, t13, t10, tzf, tk, tm, trd, twr⟩ := passTail_ok s₁
  refine WP.of_runBlock ⟨s₂, h₂, ?_, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩⟩
  · rw [tzf, h₁.r10, ofNat_sub_one (by omega_arith) (by omega_arith), ofNat_beq_zero (by omega_arith)]
    congr 1
    exact decide_eq_decide.mpr (by omega_arith)
  · rw [tk .r15 (by decide), h₁.same.r15]
  · rw [tk .rbp (by decide), h₁.same.rbp]
  · rw [tk .rsp (by decide), h₁.same.rsp]
  · rw [trd, h₁.same.rd]
  · rw [twr, h₁.same.wr]
  · rw [tm]; exact h₁.same.frame
  · rw [t14, h₁.r14, h₁.rbx, kpos_tail_addr _ hp3]
  · rw [tbx, h₁.rbx, stride_succ hp3]
  · rw [t10, h₁.r10, ofNat_sub_one (by omega_arith) (by omega_arith)]
    congr 1
  · rw [t12, t13, passes, ← h₁.halves]
    rfl

/-- The three passes. -/
theorem passes_ok {s₀ : State} (hp : BlockPre s₀) {x : BitVec 64} {s : State} (h : OInv s₀ x 0 s) :
    WP isa (.loop (.seq pass (.block passTail)) .ne) s (OInv s₀ x 3) := by
  refine WP.loop (M := isa) (body := .seq pass (.block passTail)) (c := .ne) (Q := OInv s₀ x 3)
    (fun (n : Nat) (t : State) => ∃ p, n = 3 - p ∧ p < 3 ∧ OInv s₀ x p t) ?_ 3 _ ⟨0, rfl, by decide, h⟩
  rintro n t ⟨p, rfl, hp3, ht⟩
  refine WP.mono (passBody_ok hp hp3 ht) fun t' ⟨zf', h'⟩ => ?_
  by_cases hz : p + 1 = 3
  · left
    refine ⟨by simp [X86_64.eval, zf', hz], ?_⟩
    rwa [hz] at h'
  · right
    exact ⟨by simp [X86_64.eval, zf', hz], 3 - (p + 1), by omega_arith, p + 1, rfl, by omega_arith, h'⟩

/-! ## `IP` and `IP⁻¹` -/

/-- `IP`'s high half into `r12`, its low half into `r13`, from `rax` (input word 0). -/
def ipG12 (t : Nat) : List Nat := if t < 32 then [ipSrc (32 + t)] else []
def ipG13 (t : Nat) : List Nat := if t < 32 then [ipSrc t] else []

theorem ip_check :
    check (lanes 64 6) oCfg (linExt 1) ipCode (linEnv [(.rax, 0)])
      (linPost 6 [(.r12, ipG12), (.r13, ipG13)]) = true := by
  lit_decide

/-- `IP⁻¹(R ‖ L)` into `rax`, from `R` in `r12` (input word 0) and `L` in `r13` (input word 1). -/
def fpG (j : Nat) : List Nat := if 32 ≤ fpSrc j then [fpSrc j - 32] else [64 + fpSrc j]

theorem fp_check :
    check (lanes 64 7) oCfg (linExt 2) fpCode (linEnv [(.r12, 0), (.r13, 1)]) (linPost 7 [(.rax, fpG)]) = true := by
  lit_decide

def blockKept : List Reg := [.rbp, .rsp, .r14, .r15]

theorem ip_kept : blockKept.all (fun r => ipCode.all fun i => i.dst != some r) = true := by lit_decide

theorem fp_kept : blockKept.all (fun r => fpCode.all fun i => i.dst != some r) = true := by lit_decide

theorem ipSrc_lt : ∀ j < 64, ipSrc j < 64 := by lit_decide

theorem fpSrc_lt : ∀ j < 64, fpSrc j < 64 := by lit_decide

theorem frame_oCfg {s : State} {m m' : Mem} (h : Frame [slotRegion oCfg s] m m') : m' = m := by
  funext a
  exact h a fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [slotRegion, oCfg, Region.Contains]

theorem ip_ok (s : State) :
    ∃ s', runBlock isa ipCode s = some s' ∧
      ((s'.gpr .r12).setWidth 32, (s'.gpr .r13).setWidth 32) =
        split (Spec.TripleDes.permute Spec.TripleDes.ip (s.gpr .rax)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ blockKept, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem := by
  obtain ⟨s', hs', hout, hrd, hwr, hoth, hfr⟩ := linear_ok ip_check (oCfg_ok s) (fun _ => s.gpr .rax)
    (fun r i hri => by
      simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hri
      obtain ⟨rfl, rfl⟩ := hri; exact ⟨by decide, rfl⟩)
    (fun j hj => absurd hj (by simp [oCfg]))
  refine ⟨s', hs', ?_, hrd, hwr, fun r hr => hoth r (List.all_eq_true.mp ip_kept r hr), frame_oCfg hfr⟩
  have h12 := hout .r12 ipG12 (by simp)
  have h13 := hout .r13 ipG13 (by simp)
  simp only [split, Prod.mk.injEq]
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro t ht
  · have hs := ipSrc_lt (32 + t) (by omega_arith)
    rw [BitVec.getLsbD_setWidth, decide_eq_true ht, Bool.true_and, h12 t (by omega_arith), ipG12, ite_eq_left ht,
      BitVec.getLsbD_setWidth, decide_eq_true ht, Bool.true_and, BitVec.getLsbD_ushiftRight,
      Spec.TripleDes.permute, ← Spec.TripleDes.permute,
      getLsbD_permute _ _ (by decide) (show 32 + t < 64 by omega_arith)]
    simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, Nat.mod_eq_of_lt hs]
    rfl
  · have hs := ipSrc_lt t (by omega_arith)
    rw [BitVec.getLsbD_setWidth, decide_eq_true ht, Bool.true_and, h13 t (by omega_arith), ipG13, ite_eq_left ht,
      BitVec.getLsbD_setWidth, decide_eq_true ht, Bool.true_and,
      getLsbD_permute _ _ (by decide) (show t < 64 by omega_arith)]
    simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, Nat.mod_eq_of_lt hs]
    rfl

theorem fp_ok (s : State) :
    ∃ s', runBlock isa fpCode s = some s' ∧
      s'.gpr .rax = Spec.TripleDes.permute Spec.TripleDes.fp ((s.gpr .r12).setWidth 32 ++ (s.gpr .r13).setWidth 32) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ blockKept, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem := by
  let W : Nat → BitVec 64 := fun i => if i = 0 then s.gpr .r12 else s.gpr .r13
  obtain ⟨s', hs', hout, hrd, hwr, hoth, hfr⟩ := linear_ok fp_check (oCfg_ok s) W
    (fun r i hri => by
      simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hri
      rcases hri with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, rfl⟩)
    (fun j hj => absurd hj (by simp [oCfg]))
  refine ⟨s', hs', ?_, hrd, hwr, fun r hr => hoth r (List.all_eq_true.mp fp_kept r hr), frame_oCfg hfr⟩
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hs := fpSrc_lt j hj
  rw [hout .rax fpG (by simp) j hj, getLsbD_permute _ _ (by decide) hj, BitVec.getLsbD_append,
    show 64 - Spec.TripleDes.fp.getD (64 - 1 - j) 1 = fpSrc j from rfl, fpG]
  by_cases h32 : 32 ≤ fpSrc j
  · rw [ite_eq_left h32, ite_eq_right (by omega_arith)]
    simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf,
      Nat.div_eq_of_lt (show fpSrc j - 32 < 64 by omega_arith), Nat.mod_eq_of_lt (show fpSrc j - 32 < 64 by omega_arith),
      BitVec.getLsbD_setWidth, show fpSrc j - 32 < 32 by omega_arith, decide_true, Bool.true_and]
    rfl
  · rw [ite_eq_right h32, ite_eq_left (by omega_arith)]
    simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf,
      show (64 + fpSrc j) / 64 = 1 by omega_arith, show (64 + fpSrc j) % 64 = fpSrc j by omega_arith,
      BitVec.getLsbD_setWidth, show fpSrc j < 32 by omega_arith, decide_true, Bool.true_and]
    rfl

theorem sub504_ok (s : State) :
    ∃ s', runBlock isa [.alu .sub .r14 (.imm 504)] s = some s' ∧
      s'.gpr .r14 = s.gpr .r14 - BitVec.ofNat 64 504 ∧ (∀ r, r ≠ .r14 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some]
    rfl, ?_⟩
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [gpr_setReg_self]; rfl
  · simp [gpr_setReg, hr]

/-- TDEA encryption of the block in `rax` (as a 64-bit integer) with the key
schedule at `r14`, into `rax`. -/
theorem block_ok {s₀ : State} (hp : BlockPre s₀) :
    WP isa block s₀ fun s =>
      Same s₀ s ∧ s.gpr .r14 = s₀.gpr .r14 ∧ s.gpr .rax = tdes (sch s₀) (s₀.gpr .rax) := by
  obtain ⟨s₁, h₁, hal₁, rd₁, wr₁, k₁, m₁⟩ := ip_ok s₀
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, h₁, WP.of_runBlock ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some]; rfl, ?_⟩⟩
  have g : ∀ r, r ≠ .r10 → r ≠ .rbx →
      ((s₁.setReg32 .r10 (3 : BitVec 32)).setReg32 .rbx (8 : BitVec 32)).gpr r = s₁.gpr r := fun r h1 h2 => by
    simp [State.setReg32, gpr_setReg, h1, h2]
  have hO : OInv s₀ (s₀.gpr .rax) 0 ((s₁.setReg32 .r10 (3 : BitVec 32)).setReg32 .rbx (8 : BitVec 32)) :=
    ⟨⟨by rw [g _ (by decide) (by decide), k₁ _ (by decide)], by rw [g _ (by decide) (by decide), k₁ _ (by decide)],
      by rw [g _ (by decide) (by decide), k₁ _ (by decide)], rd₁, wr₁,
      by show Frame [xR s₀] s₀.mem s₁.mem; rw [m₁]; exact Frame.refl _ _⟩,
      by rw [g _ (by decide) (by decide), k₁ _ (by decide)]; simp [kpos],
      by simp [State.setReg32, gpr_setReg, stride],
      by simp [State.setReg32, gpr_setReg],
      by rw [g _ (by decide) (by decide), g _ (by decide) (by decide), hal₁]; rfl⟩
  refine WP.seq (WP.mono (passes_ok hp hO) fun s₃ h₃ => ?_)
  rw [WP.block_append_iff]
  obtain ⟨s₄, h₄, r14₄, g4, m₄, rd₄, wr₄⟩ := sub504_ok s₃
  obtain ⟨s₅, h₅, ax₅, rd₅, wr₅, k₅, m₅⟩ := fp_ok s₄
  refine WP.of_runBlock ⟨s₄, h₄, WP.of_runBlock ⟨s₅, h₅, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩⟩
  · rw [k₅ _ (by decide), g4 _ (by decide), h₃.same.r15]
  · rw [k₅ _ (by decide), g4 _ (by decide), h₃.same.rbp]
  · rw [k₅ _ (by decide), g4 _ (by decide), h₃.same.rsp]
  · rw [rd₅, rd₄, h₃.same.rd]
  · rw [wr₅, wr₄, h₃.same.wr]
  · rw [m₅, m₄]; exact h₃.same.frame
  · rw [k₅ _ (by decide), r14₄, h₃.r14, show 8 * kpos 3 0 = 504 from rfl, BitVec.add_sub_cancel]
  · rw [ax₅, g4 _ (by decide), g4 _ (by decide), tdes_eq, ← h₃.halves]

end VG.Proof.CmacTripleDes.X86_64

end

end

/-! ### `CmacTripleDes.X86_64.Save`, which the modules that import this one used -/

section

/-!
# TDEA-CMAC on x86-64: saving and restoring the registers

Each function saves our caller's callee-saved registers to bytes `[48, 96)` of
the scratch buffer (`save`), and restores them from there, through `r15`
(`restore`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacTripleDes.X86_64

theorem offset_nat (i : Nat) : BitVec.ofInt 64 (i : Int) = BitVec.ofNat 64 i := rfl

/-- The memory after saving the registers to the scratch buffer at `S`. -/
abbrev savedMem (s : State) (S : Addr) : Mem := Spill.saveMem s.mem S s.gpr saved

theorem saved_bound : ∀ p ∈ saved, 48 ≤ p.2 ∧ p.2 + 8 ≤ 96 := by decide

theorem save_ok (s : State) (sc : Reg)
    (hw : ∀ d, 48 ≤ d → d + 8 ≤ 96 → InRegions s.wr (s.gpr sc + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa (save sc) s = some s' ∧ s'.gpr = s.gpr ∧ s'.mem = savedMem s (s.gpr sc) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨_, Spill.save_run sc saved s fun p hp => hw p.2 (saved_bound p hp).1 (saved_bound p hp).2, rfl, rfl,
    rfl, rfl⟩

theorem readW_writeW_other (m : Mem) (b : Addr) {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
    (m.writeW (b + BitVec.ofNat 64 e) v).readW (b + BitVec.ofNat 64 d) 64 = m.readW (b + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep b h hd he) (by decide)

/-- The saved registers, read back. -/
theorem savedMem_read (s : State) (S : Addr) :
    (savedMem s S).readW (S + BitVec.ofNat 64 48) 64 = s.gpr .rbx ∧
    (savedMem s S).readW (S + BitVec.ofNat 64 56) 64 = s.gpr .rbp ∧
    (savedMem s S).readW (S + BitVec.ofNat 64 64) 64 = s.gpr .r12 ∧
    (savedMem s S).readW (S + BitVec.ofNat 64 72) 64 = s.gpr .r13 ∧
    (savedMem s S).readW (S + BitVec.ofNat 64 80) 64 = s.gpr .r14 ∧
    (savedMem s S).readW (S + BitVec.ofNat 64 88) 64 = s.gpr .r15 :=
  have h := Spill.saveMem_saved s.mem S s.gpr saved (by decide)
  ⟨h (.rbx, 48) (by decide), h (.rbp, 56) (by decide), h (.r12, 64) (by decide), h (.r13, 72) (by decide),
    h (.r14, 80) (by decide), h (.r15, 88) (by decide)⟩

theorem slot_contains (b : Addr) {d : Nat} (h₁ : 48 ≤ d) (h₂ : d + 8 ≤ 96) :
    (⟨b + BitVec.ofNat 64 48, 48⟩ : Region).Contains (b + BitVec.ofNat 64 d) 8 := by
  rw [show b + BitVec.ofNat 64 d = (b + BitVec.ofNat 64 48) + BitVec.ofNat 64 (d - 48) from
    (Offset.add_add_eq b (by omega_using [h₁])).symm]
  exact Offset.contains_base _ (by omega_using [h₂]) (by omega_using [h₂])

/-- Saving the registers changes only their slots. -/
theorem savedMem_frame (s : State) (S : Addr) : Frame [⟨S + BitVec.ofNat 64 48, 48⟩] s.mem (savedMem s S) :=
  Spill.saveMem_frame _ _ _ _ fun p hp => slot_contains _ (saved_bound p hp).1 (saved_bound p hp).2

theorem restore_ok (s : State) {B : Addr} (hb : s.gpr .r15 = B)
    (hr : ∀ d, 48 ≤ d → d + 8 ≤ 96 → InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa restore s = some s' ∧
      s'.gpr .rbx = s.mem.readW (B + BitVec.ofNat 64 48) 64 ∧
      s'.gpr .rbp = s.mem.readW (B + BitVec.ofNat 64 56) 64 ∧
      s'.gpr .r12 = s.mem.readW (B + BitVec.ofNat 64 64) 64 ∧
      s'.gpr .r13 = s.mem.readW (B + BitVec.ofNat 64 72) 64 ∧
      s'.gpr .r14 = s.mem.readW (B + BitVec.ofNat 64 80) 64 ∧
      s'.gpr .r15 = s.mem.readW (B + BitVec.ofNat 64 88) 64 ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.mem = s.mem := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, restore, saved, List.map, runBlock_cons, runStep_some,
      runBlock_nil, at_, exec, readSrc, State.load64, State.ea, offset_nat, gpr_setReg, mem_setReg,
      rd_setReg, wr_setReg, Option.map_some, hb,
      hr 48 (by decide) (by decide), hr 56 (by decide) (by decide), hr 64 (by decide) (by decide),
      hr 72 (by decide) (by decide), hr 80 (by decide) (by decide), hr 88 (by decide) (by decide)]
    rfl, ?_⟩
  simp only [reduceCtorEq, ↓reduceIte, and_self, gpr_setReg, mem_setReg]

/-- The registers restored from slots that have not changed since they
were saved, the stack pointer kept: `gprPreserved`. -/
theorem restored {s₀ s s' : State} {S : Addr} (hm : ∀ d, 48 ≤ d → d + 8 ≤ 96 →
      s.mem.readW (S + BitVec.ofNat 64 d) 64 = (savedMem s₀ S).readW (S + BitVec.ofNat 64 d) 64)
    (h : s'.gpr .rbx = s.mem.readW (S + BitVec.ofNat 64 48) 64 ∧
      s'.gpr .rbp = s.mem.readW (S + BitVec.ofNat 64 56) 64 ∧
      s'.gpr .r12 = s.mem.readW (S + BitVec.ofNat 64 64) 64 ∧
      s'.gpr .r13 = s.mem.readW (S + BitVec.ofNat 64 72) 64 ∧
      s'.gpr .r14 = s.mem.readW (S + BitVec.ofNat 64 80) 64 ∧
      s'.gpr .r15 = s.mem.readW (S + BitVec.ofNat 64 88) 64)
    (hsp : s'.gpr .rsp = s₀.gpr .rsp) : ∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r := by
  obtain ⟨a, b, c, d, e, f⟩ := savedMem_read s₀ S
  obtain ⟨ha, hb, hc, hd, he, hf⟩ := h
  intro r hr
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [ha, hm 48 (by decide) (by decide), a]
  · rw [hb, hm 56 (by decide) (by decide), b]
  · exact hsp
  · rw [hc, hm 64 (by decide) (by decide), c]
  · rw [hd, hm 72 (by decide) (by decide), d]
  · rw [he, hm 80 (by decide) (by decide), e]
  · rw [hf, hm 88 (by decide) (by decide), f]

end VG.Proof.CmacTripleDes.X86_64

end

end

/-!
# TDEA-CMAC on x86-64: the contracts the proofs are written against

The artifacts' contracts are the shared ones of
`Spec/Cmac/TripleDesContract.lean`, which imply these (`Verified.lean`). The
functions call nothing and use no stack.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.X86_64

open VG VG.X86_64

/-- `CIPH_K` for TDEA with the key schedule at `w`, in `m`. -/
abbrev ciphAt (m : Mem) (w : Addr) : Spec.Cmac.Cipher := Spec.Cmac.tdesWith (Spec.TripleDes.scheduleAt m w)

/-- `vg_cmac_triple_des_init(key = rdi, key_len = rsi, out = rdx, scratch = rcx)`. -/
def initX86_64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let out : Region := ⟨s.gpr .rdx, 400⟩
    let scr : Region := ⟨s.gpr .rcx, 120⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [key] ∧ s.wr = [out, scr] ∧ key.Disjoint out ∧ key.Disjoint scr ∧ out.Disjoint scr ∧
      ret.Disjoint out ∧ ret.Disjoint scr ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 400 ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat + 120 ≤ 2 ^ 64 ∧ Spec.TripleDes.validKey (s.gpr .rsi).toNat
  post s s' :=
    let k := Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
    let ks := Spec.Cmac.subkeys (Spec.Cmac.tdesWith k) 8
    Spec.TripleDes.scheduleAt s'.mem (s.gpr .rdx) = k ∧
      Spec.Aes.bytesAt s'.mem (s.gpr .rdx + 384) 16 = ks.1 ++ ks.2
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `vg_cmac_triple_des_update(schedule = rdi, state = rsi, data = rdx, n = rcx, scratch = r8)`. -/
def updateX86_64 : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 384⟩
    let state : Region := ⟨s.gpr .rsi, 8⟩
    let data : Region := ⟨s.gpr .rdx, 8 * (s.gpr .rcx).toNat⟩
    let scr : Region := ⟨s.gpr .r8, 120⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [sched, data] ∧ s.wr = [state, scr] ∧
      sched.Disjoint state ∧ sched.Disjoint scr ∧ data.Disjoint state ∧ data.Disjoint scr ∧
      state.Disjoint scr ∧ ret.Disjoint state ∧ ret.Disjoint scr ∧
      (s.gpr .rsi).toNat + 8 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 8 * (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + 120 ≤ 2 ^ 64
  post s s' :=
    Spec.Aes.bytesAt s'.mem (s.gpr .rsi) 8 =
      Spec.Cmac.chain (ciphAt s.mem (s.gpr .rdi)) (Spec.Aes.bytesAt s.mem (s.gpr .rsi) 8)
        (Spec.Cmac.blocksAt s.mem (s.gpr .rdx) 8 (s.gpr .rcx).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `vg_cmac_triple_des_finalize(key = rdi, state = rsi, last = rdx, last_len = rcx, scratch = r8)`. -/
def finalizeX86_64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, 400⟩
    let state : Region := ⟨s.gpr .rsi, 8⟩
    let last : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let scr : Region := ⟨s.gpr .r8, 120⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [key, last] ∧ s.wr = [state, scr] ∧
      key.Disjoint state ∧ key.Disjoint scr ∧ last.Disjoint state ∧ last.Disjoint scr ∧
      state.Disjoint scr ∧ ret.Disjoint state ∧ ret.Disjoint scr ∧
      (s.gpr .rdi).toNat + 400 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 8 ≤ 2 ^ 64 ∧
      (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 120 ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat ≤ 8
  post s s' :=
    let ciph := ciphAt s.mem (s.gpr .rdi)
    let ks := Spec.Cmac.subkeys ciph 8
    Spec.Aes.bytesAt s.mem (s.gpr .rdi + 384) 16 = ks.1 ++ ks.2 →
    ∀ msg : List Byte, msg.length % 8 = 0 → (msg = [] ∨ 0 < (s.gpr .rcx).toNat) →
      Spec.Aes.bytesAt s.mem (s.gpr .rsi) 8 = Spec.Cmac.chain ciph (Spec.Cmac.zeros 8) (Spec.Cmac.blocks 8 msg) →
      Spec.Aes.bytesAt s'.mem (s.gpr .rsi) 8 =
        Spec.Cmac.macFull ciph 8 (msg ++ Spec.Aes.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.CmacTripleDes.X86_64
