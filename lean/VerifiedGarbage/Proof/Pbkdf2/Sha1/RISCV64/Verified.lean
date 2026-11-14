module

public import VerifiedGarbage.Proof.Pbkdf2.Sha1.RISCV64.Cmp
public import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Correct
public import VerifiedGarbage.Proof.Sha1.Md
public import VerifiedGarbage.Impl.Sha1.RISCV64
public import VerifiedGarbage.Impl.Sha1.RISCV64.Stream
import VerifiedGarbage.Proof.Sha1.RISCV64.Stream
import VerifiedGarbage.Proof.Hmac.Generic.Common
public import VerifiedGarbage.Spec.Pbkdf2.Generic
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Align
public import VerifiedGarbage.Impl.Pbkdf2.Sha1.RISCV64
public import VerifiedGarbage.Proof.Pbkdf2.Sha1Words
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Pbkdf2.Sha1.RISCV64.Round
public import VerifiedGarbage.Proof.Pbkdf2.RISCV64.IterateMain
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Sha1.StateMem
public import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Calls
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Hmac.Common
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Impl.Pbkdf2.Sha1.RISCV64

/-! ### `Pbkdf2.Sha1.RISCV64.Fin`, which only this module used -/

section

/-! ### `Pbkdf2.Sha1.RISCV64.Pro`, which only this module used -/

section

/-! ### `Pbkdf2.Sha1.RISCV64.Loop`, which only this module used -/

section

/-! ### `Pbkdf2.Sha1.RISCV64.Frame`, which only this module used -/

section

/-! ### `Pbkdf2.RISCV64.Sha1`, which only this module used -/

section

/-!
# PBKDF2-HMAC-SHA-1 on RISC-V: `iterate`

The iteration over a Merkle–Damgård hash function (`Impl/Pbkdf2/RISCV64.lean`)
for SHA-1's sizes, compression function and digest code (`it`), and what its
proof needs of SHA-1 (`hashOkW`): the sizes and the precondition that
SHA-1's own iteration (`Proof/Pbkdf2/Sha1/RISCV64/`) shares with it.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.RISCV64.Sha1

open VG.RISCV64
open VG.Impl.Pbkdf2.RISCV64 (It padBE)

/-- SHA-1's parameters of the iteration. -/
def it : It where
  N := 20
  B := 64
  D := 20
  CW := 80
  cmpN := "vg_sha1_compress"
  cmpC := Impl.Sha1.RISCV64.compress
  out := Impl.Sha1.RISCV64.Stream.params.out
  pad := padBE 64 20 8

/-- What the proof needs of SHA-1, with `Wi` bytes of working space. -/
theorem hashOkW (Wi : Nat) (h₁ : 227 ≤ Wi) (h₂ : Wi ≤ 8192) :
    HashOk it Wi Spec.Hmac.sha1S Proof.Sha1.md Spec.Sha1.H0 where
  sizes := ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by simp only [it]; omega_using [h₁], h₂⟩
  pad := by decide
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha1.md, Spec.Sha1.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 20) h (by omega_using [hj])
  out := fun s h₁ h₂ h₃ => (Proof.Sha1.RISCV64.Stream.shape.out s h₁ h₂ h₃).mono fun _ ⟨g, a, b, c, d⟩ =>
    ⟨fun r x y _ => g r x y, a, b, c, d⟩
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun m => by
    show Spec.Sha1.hash m = _
    rw [Proof.Sha1.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Sha1.md.digest_length _))).symm,
    by decide, by decide⟩

end VG.Proof.Pbkdf2.RISCV64.Sha1

end

end


/-!
# PBKDF2-HMAC-SHA-1's iteration on RISC-V: the frame

Untrusted: everything here is checked by Lean. The precondition is the one
of every Merkle–Damgård hash function's iteration (`Pre`,
`Proof/Pbkdf2/RISCV64/Iterate.lean`), for SHA-1's sizes (`Sha1.it`), and so
are the parts of the scratch space (`sc`, `sc_contains`, …): the frame is
`scratch` rounded up to a multiple of 8, of which the code uses 164 bytes.
`Hs` says the frame holds the key's two hash values; `LI` is the loop's
invariant, with `m` steps left, `U`'s words in `A` and `T`'s in the frame.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Sha1.RISCV64

open VG VG.RISCV64 VG.Impl.Pbkdf2.Sha1.RISCV64
open VG.Proof.Pbkdf2.RISCV64 (Pre Sizes key up tp scr nn sc scR keyR uR tR sc_contains sc_al sc_add pad_le)
open VG.Proof.Pbkdf2.RISCV64.Sha1 (it)
open VG.Spec.Sha1 (HashValue Word)
open VG.Proof.Pbkdf2.Sha1Words (wstep wIter)

section
variable (s₀ : State)

/-- The key's inner and outer hash values. -/
abbrev Hi : HashValue := Spec.Sha1.stateAt s₀.mem (key s₀)
abbrev Ho : HashValue := Spec.Sha1.stateAt s₀.mem (key s₀ + BitVec.ofNat 64 84)

/-- The word at offset `d` of the frame. -/
abbrev fw (m : Mem) (d : Nat) : Word := m.readW (sc s₀ + BitVec.ofNat 64 d) 32

end

/-- The frame holds the key's two hash values. -/
structure Hs (s₀ : State) (m : Mem) : Prop where
  hi : ∀ k < 5, fw s₀ m (hiO + 4 * k) = (Hi s₀)[k]!
  ho : ∀ k < 5, fw s₀ m (hoO + 4 * k) = (Ho s₀)[k]!

/-- The loop's invariant, with `m` steps left before the final `T`, `R`. -/
structure LI (Wi : Nat) (s₀ : State) (R : HashValue) (m : Nat) (s : State) : Prop where
  b : s.gpr B = sc s₀
  n : s.gpr N = BitVec.ofNat 64 m
  tp : s.gpr TP = tp s₀
  xy : ∃ x y : HashValue, (∀ k < 5, (s.gpr (A.getD k .t0)).setWidth 32 = x[k]!) ∧
    (∀ k < 5, fw s₀ s.mem (tO + 4 * k) = y[k]!) ∧ wIter (Hi s₀) (Ho s₀) m x y = R
  hs : Hs s₀ s.mem
  saved : Spill.Saved (sc s₀) s₀.gpr saved s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [scR Wi s₀] s₀.mem s.mem

section
variable {Wi : Nat} {s₀ : State} (hp : Pre it Wi s₀) (hz : Sizes it Wi)
include hp hz

omit hp in
theorem fc {d n : Nat} (h : d + n ≤ 164) : (scR Wi s₀).Contains (sc s₀ + BitVec.ofNat 64 d) n :=
  sc_contains hz (by have := hz.fits; simp only [it] at this; omega_using [h, this])

theorem fin {s : State} (hwr : s.wr = s₀.wr) {d n : Nat} (h : d + n ≤ 164) :
    InRegions s.wr (sc s₀ + BitVec.ofNat 64 d) n :=
  ⟨scR Wi s₀, by rw [hwr, hp.wr]; simp, fc hz h⟩

theorem frd {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {d n : Nat} (h : d + n ≤ 164) :
    InRegions (s.rd ++ s.wr) (sc s₀ + BitVec.ofNat 64 d) n :=
  ⟨scR Wi s₀, by rw [hrd, hwr, hp.rd, hp.wr]; simp, fc hz h⟩

end

theorem fal (s₀ : State) {d : Nat} (h : d % 4 = 0) : (sc s₀ + BitVec.ofNat 64 d).toNat % 4 = 0 :=
  Align.al_add sc_al (by decide) h

theorem fsep (s₀ : State) {a b : Nat} (h : a + 4 ≤ b ∨ b + 4 ≤ a) (ha : a + 4 ≤ 164) (hb : b + 4 ≤ 164) :
    Mem.Sep (sc s₀ + BitVec.ofNat 64 a) 4 (sc s₀ + BitVec.ofNat 64 b) 4 :=
  Offset.sep _ h (by omega_using [ha]) (by omega_using [hb])

/-- A word of the frame after a word written elsewhere in it. -/
theorem fw_write (s₀ : State) (m : Mem) {a b : Nat} (v : Word) (h : a + 4 ≤ b ∨ b + 4 ≤ a) (ha : a + 4 ≤ 164)
    (hb : b + 4 ≤ 164) : fw s₀ (m.writeW (sc s₀ + BitVec.ofNat 64 b) v) a = fw s₀ m a :=
  Mem.readW_writeW_sep (fsep s₀ h ha hb) (by decide)

/-- The saved registers' slots, apart from the words. -/
theorem slot_word (s₀ : State) {d a : Nat} (hd : d + 8 ≤ 104) (ha : 104 ≤ a) (ha' : a + 4 ≤ 164) :
    Region.Disjoint ⟨sc s₀ + BitVec.ofNat 64 d, 8⟩ ⟨sc s₀ + BitVec.ofNat 64 a, 4⟩ :=
  Offset.disjoint _ (by omega_using [hd, ha]) (by omega_using [hd]) (by omega_using [ha'])

theorem saved_bound : ∀ p ∈ saved, p.2 % 8 = 0 ∧ p.2 + 8 ≤ 104 := by decide

/-- A word written in the frame keeps the saved registers. -/
theorem saved_write {s₀ : State} {m : Mem} (h : Spill.Saved (sc s₀) s₀.gpr saved m) {a : Nat} (v : Word)
    (ha : 104 ≤ a) (ha' : a + 4 ≤ 164) :
    Spill.Saved (sc s₀) s₀.gpr saved (m.writeW (sc s₀ + BitVec.ofNat 64 a) v) :=
  h.frame (rs := [⟨sc s₀ + BitVec.ofNat 64 a, 4⟩])
    ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
    fun p hp r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact slot_word s₀ (saved_bound p hp).2 ha ha'

end VG.Proof.Pbkdf2.Sha1.RISCV64

end

end


/-!
# PBKDF2-HMAC-SHA-1's iteration on RISC-V: the loop

Untrusted: everything here is checked by Lean. One step (`body_ok`): the
inner compression of `U`'s block into `V`, the outer one of that into `A`
(`cmp_ok`), which is `U`'s next value, `T ← T ⊕ U` in the frame (`xorT_ok`),
and one step fewer left; the loop (`loop_ok`) runs them all, from the
invariant `LI`.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Sha1.RISCV64

open VG VG.RISCV64 VG.Impl.Pbkdf2.Sha1.RISCV64
open VG.RISCV64.Steps (Upd Mupd wp_xor wp_subi eval_zero eval_nonzero ofNat_beq_zero)
open VG.Proof.Pbkdf2.RISCV64 (Pre Sizes tp sc scR sc_al sc_sub)
open VG.Proof.Pbkdf2.RISCV64.Sha1 (it)
open VG.Spec.Sha1 (HashValue Word compress)
open VG.Proof.Pbkdf2.Sha1Words (blk wstep wIter)

/-! ## Word loads and stores -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_lw {t n : Reg} {off : Nat} {a : Addr} (ho : off < 2048) (ha : s.gpr n + BitVec.ofNat 64 off = a)
    (hal : a.toNat % 4 = 0) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' t ((s.mem.readW a 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.load .w t n off :: is)) s Q := by
  refine Steps.WP.cons (s' := s.write t ((s.mem.readW a 32).setWidth 64)) ?_ (k _ (Upd.write _ _ _))
  rw [exec_load_w ho (by rw [ha]; exact hal) (by rw [ha]; exact hin), ha]

theorem wp_sw {t n : Reg} {off : Nat} {a : Addr} (ho : off < 2048) (ha : s.gpr n + BitVec.ofNat 64 off = a)
    (hal : a.toNat % 4 = 0) (hout : InRegions s.wr a 4)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 32)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store .w t n off :: is)) s Q := by
  refine Steps.WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 32) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  rw [exec_store_w ho (by rw [ha]; exact hal) (by rw [ha]; exact hout), ha]

end

/-! ## Registers of the two layouts -/

theorem inner_wr : ∀ k < 5, inner.wr k = A.getD k .t0 := by decide
theorem inner_var : ∀ k < 5, inner.var 0 k = V.getD k .t0 := by decide
theorem outer_wr : ∀ k < 5, outer.wr k = V.getD k .t0 := by decide
theorem outer_var : ∀ k < 5, outer.var 0 k = A.getD k .t0 := by decide

theorem inner_keep : ¬ Clob inner B ∧ ¬ Clob inner N ∧ ¬ Clob inner TP := by simp only [Clob]; decide
theorem outer_keep : ¬ Clob outer B ∧ ¬ Clob outer N ∧ ¬ Clob outer TP := by simp only [Clob]; decide

theorem A_ne : ∀ k < 5, A.getD k .t0 ≠ T1 ∧ A.getD k .t0 ≠ B ∧ A.getD k .t0 ≠ N := by decide

/-! ## `T ← T ⊕ U` -/

/-- The first `k` words of `T` updated, from the state `s₁` before. -/
structure XI (s₀ s₁ : State) (x y : HashValue) (k : Nat) (s : State) : Prop where
  done : ∀ j < k, fw s₀ s.mem (tO + 4 * j) = y[j]! ^^^ x[j]!
  todo : ∀ j, k ≤ j → j < 5 → fw s₀ s.mem (tO + 4 * j) = y[j]!
  gpr : ∀ r, r ≠ T1 → s.gpr r = s₁.gpr r
  other : ∀ d, d + 4 ≤ tO → fw s₀ s.mem d = fw s₀ s₁.mem d
  saved : Spill.Saved (sc s₀) s₀.gpr saved s₁.mem → Spill.Saved (sc s₀) s₀.gpr saved s.mem
  frame : Frame [⟨sc s₀ + BitVec.ofNat 64 tO, 20⟩] s₁.mem s.mem
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  sp : s.sp = s₁.sp


section
variable {Wi : Nat} {s₀ : State} (hp : Pre it Wi s₀) (hz : Sizes it Wi)
include hp hz

theorem xorT_ok (s₁ : State) (x y : HashValue) (hb : s₁.gpr B = sc s₀)
    (hx : ∀ k < 5, (s₁.gpr (A.getD k .t0)).setWidth 32 = x[k]!) (hy : ∀ k < 5, fw s₀ s₁.mem (tO + 4 * k) = y[k]!)
    (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) :
    WP isa (.block xorT) s₁ (XI s₀ s₁ x y 5) := by
  refine wp_range_flatMap (M := isa) (XI s₀ s₁ x y) (fun k s hk h => ?_) 5 (Nat.le_refl _) s₁
    ⟨fun _ h => absurd h (by omega_using []), fun j _ hj => hy j hj, fun _ _ => rfl, fun _ _ => rfl, id, Frame.refl _ _,
      rfl, rfl, rfl⟩
  have an := A_ne k hk
  have hb' : s.gpr B = sc s₀ := by rw [h.gpr _ (by decide), hb]
  have rd' : s.rd = s₀.rd := h.rd.trans hrd
  have wr' : s.wr = s₀.wr := h.wr.trans hwr
  refine wp_lw (a := sc s₀ + BitVec.ofNat 64 (tO + 4 * k)) (by simp only [tO]; omega_using [hk]) (by rw [hb'])
    (fal s₀ (by simp only [tO]; omega_using [])) (frd hp hz rd' wr' (by simp only [tO]; omega_using [hk])) fun s₂ u₂ => ?_
  refine wp_xor fun s₃ u₃ => ?_
  refine wp_sw (a := sc s₀ + BitVec.ofNat 64 (tO + 4 * k)) (by simp only [tO]; omega_using [hk])
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), hb']) (fal s₀ (by simp only [tO]; omega_using []))
    (by rw [u₃.wr, u₂.wr]; exact fin hp hz wr' (by simp only [tO]; omega_using [hk])) fun s₄ u₄ => WP.block_nil ?_
  have hv : (s₃.gpr T1).setWidth 32 = y[k]! ^^^ x[k]! := by
    rw [u₃.gpr, u₂.gpr, lo32_xor, lo32_ext, u₂.other _ an.1, h.gpr _ an.1, hx k hk]
    have := h.todo k (Nat.le_refl _) hk
    simp only [fw] at this
    rw [this]
  have m₄ : s₄.mem = s.mem.writeW (sc s₀ + BitVec.ofNat 64 (tO + 4 * k)) (y[k]! ^^^ x[k]!) := by
    rw [u₄.mem, hv, u₃.mem, u₂.mem]
  refine ⟨fun j hj => ?_, fun j hj hj' => ?_, fun r hr => ?_, fun d hd => ?_, fun hsv => ?_, ?_,
    by rw [u₄.rd, u₃.rd, u₂.rd, h.rd], by rw [u₄.wr, u₃.wr, u₂.wr, h.wr], by rw [u₄.sp, u₃.sp, u₂.sp, h.sp]⟩
  · rw [m₄]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [fw_write s₀ _ _ (by omega_using [hj]) (by simp only [tO]; omega_arith) (by simp only [tO]; omega_using [hk])]; exact h.done j hj
    · exact Mem.readW_writeW_self32 _ _ _
  · rw [m₄, fw_write s₀ _ _ (by omega_using [hj]) (by simp only [tO]; omega_using [hj']) (by simp only [tO]; omega_using [hk])]
    exact h.todo j (by omega_using [hj]) hj'
  · rw [u₄.gpr, u₃.other _ hr, u₂.other _ hr, h.gpr _ hr]
  · rw [m₄, fw_write s₀ _ _ (by omega_using [hd]) (by simp only [tO] at hd ⊢; omega_using [hd]) (by simp only [tO]; omega_using [hk])]
    exact h.other d hd
  · rw [m₄]; exact saved_write (h.saved hsv) _ (by simp only [tO]; omega_using []) (by simp only [tO]; omega_using [hk])
  · rw [m₄]
    exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by simp only [tO]; omega_using [])
      (by simp only [tO]; omega_using [hk]) (by simp only [tO]; omega_using []))

/-! ## One step -/

theorem body_ok {R : HashValue} {m : Nat} {s : State} (h : LI Wi s₀ R (m + 1) s) (hm : m + 1 < 2 ^ 64) :
    WP isa (.block body) s (LI Wi s₀ R m) := by
  obtain ⟨x, y, hx, hy, hR⟩ := h.xy
  have rdwr : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  unfold body
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  -- The inner compression.
  refine WP.mono (cmp_ok inner_ok s x (Hi s₀) h.b sc_al
    (fun k hk => frd hp hz h.rd h.wr (by simp only [inner, hiO]; omega)) (fun k hk => h.hs.hi k hk)
    (fun k hk => by rw [inner_wr k hk]; exact hx k hk)) fun s₁ ⟨v₁, k₁, m₁, rd₁, wr₁, sp₁⟩ => ?_
  rw [WP.block_append_iff]
  have b₁ : s₁.gpr B = sc s₀ := by rw [k₁ _ inner_keep.1, h.b]
  -- The outer compression.
  refine WP.mono (cmp_ok outer_ok s₁ (compress (Hi s₀) (blk x)) (Ho s₀) b₁ sc_al
    (fun k hk => frd hp hz (rd₁.trans h.rd) (wr₁.trans h.wr) (by simp only [outer, hoO]; omega))
    (fun k hk => by rw [m₁]; exact h.hs.ho k hk)
    (fun k hk => by rw [outer_wr k hk, ← inner_var k hk]; exact v₁ k hk)) fun s₂ ⟨v₂, k₂, m₂, rd₂, wr₂, sp₂⟩ => ?_
  rw [WP.block_append_iff]
  have b₂ : s₂.gpr B = sc s₀ := by rw [k₂ _ outer_keep.1, b₁]
  have hx₂ : ∀ k < 5, (s₂.gpr (A.getD k .t0)).setWidth 32 = (wstep (Hi s₀) (Ho s₀) x)[k]! := fun k hk => by
    rw [← outer_var k hk]; exact v₂ k hk
  -- `T ← T ⊕ U`.
  refine WP.mono (xorT_ok hp hz s₂ _ y b₂ hx₂ (fun k hk => by rw [m₂, m₁]; exact hy k hk)
    (rd₂.trans (rd₁.trans h.rd)) (wr₂.trans (wr₁.trans h.wr))) fun s₃ h₃ => ?_
  refine wp_subi (imm := 1) (by decide) fun s₄ u₄ => WP.block_nil ?_
  have g₃ : ∀ r, r ≠ T1 → ¬ Clob outer r → ¬ Clob inner r → s₃.gpr r = s.gpr r := fun r h1 ho hi => by
    rw [h₃.gpr r h1, k₂ r ho, k₁ r hi]
  refine ⟨?_, ?_, ?_, ⟨wstep (Hi s₀) (Ho s₀) x, Vector.zipWith (· ^^^ ·) y (wstep (Hi s₀) (Ho s₀) x), fun k hk => ?_,
    fun k hk => ?_, ?_⟩, ⟨fun k hk => ?_, fun k hk => ?_⟩, ?_, by rw [u₄.rd, h₃.rd, rd₂, rd₁, h.rd],
    by rw [u₄.wr, h₃.wr, wr₂, wr₁, h.wr], by rw [u₄.sp, h₃.sp, sp₂, sp₁, h.sp], ?_⟩
  · rw [u₄.other _ (by decide), g₃ _ (by decide) outer_keep.1 inner_keep.1, h.b]
  · rw [u₄.gpr, g₃ _ (by decide) outer_keep.2.1 inner_keep.2.1, h.n]
    rw [Offset.ofNat_sub_ofNat (show 1 ≤ m + 1 by omega), Nat.add_sub_cancel]
  · rw [u₄.other _ (by decide), g₃ _ (by decide) outer_keep.2.2 inner_keep.2.2, h.tp]
  · rw [u₄.other _ (A_ne k hk).2.2, h₃.gpr _ (A_ne k hk).1]; exact hx₂ k hk
  · rw [u₄.mem, h₃.done k hk, getElem!_pos _ k hk, getElem!_pos _ k hk, getElem!_pos _ k hk,
      Vector.getElem_zipWith]
  · rw [← hR]; rfl
  · rw [u₄.mem, h₃.other _ (by simp only [hiO, tO]; omega), m₂, m₁]; exact h.hs.hi k hk
  · rw [u₄.mem, h₃.other _ (by simp only [hoO, tO]; omega), m₂, m₁]; exact h.hs.ho k hk
  · rw [u₄.mem]; exact h₃.saved (by rw [m₂, m₁]; exact h.saved)
  · rw [u₄.mem]
    refine h.frame.trans ?_
    rw [← m₁, ← m₂]
    exact h₃.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR Wi s₀, by simp, sc_sub (by have := hz.fits; simp only [it, tO] at this ⊢; omega)⟩

/-! ## The loop -/

theorem loop_ok {R : HashValue} {n : Nat} (hn : n < 2 ^ 32) {s : State} (h : LI Wi s₀ R n s) :
    WP isa (.ite (.zero N) (.block []) (.loop (.block body) (.nonzero N))) s (LI Wi s₀ R 0) := by
  have hlt : n < 2 ^ 64 := by omega_using [hn]
  refine WP.ite (decide (n = 0)) (by rw [eval_zero, h.n, ofNat_beq_zero hlt]) (fun hb => ?_) (fun hb => ?_)
  · obtain rfl : n = 0 := by simpa using hb
    exact WP.block_nil h
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hb; omega_using [hb]⟩
    refine WP.loop (M := isa) (fun m s => m + 1 < 2 ^ 32 ∧ LI Wi s₀ R (m + 1) s)
      (fun m s ⟨hm, hs'⟩ => WP.mono (body_ok hp hz hs' (by omega_using [hm])) fun s' hi => ?_) m s ⟨hn, h⟩
    have hz' : isa.eval (.nonzero N) s' = some (decide (m ≠ 0)) := by
      rw [eval_nonzero, hi.n, bne, ofNat_beq_zero (by omega_using [hm])]; simp
    cases m with
    | zero => exact .inl ⟨by rw [hz']; rfl, hi⟩
    | succ m => exact .inr ⟨by rw [hz']; simp, m, by omega_using [], by omega_using [hm], hi⟩

end

end VG.Proof.Pbkdf2.Sha1.RISCV64

end

end


/-!
# PBKDF2-HMAC-SHA-1's iteration on RISC-V: the prologue

Untrusted: everything here is checked by Lean. After the entry block, which
zero-extends `n` (`Proof/Pbkdf2/RISCV64/IterateMain.lean`): the frame
aligned and our caller's registers saved there; the key's inner and outer
hash values copied to the frame as words (`cpLE_ok`); `T`'s words to the
frame (`cpT_ok`) and `U`'s to `A` (`ldU_ok`), big-endian. That is the loop's
invariant with `n` steps left (`pro_ok`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Sha1.RISCV64

open VG VG.RISCV64 VG.Impl.Pbkdf2.Sha1.RISCV64
open VG.RISCV64.ByteLoad (beWord loadBE32_ok loadLE32_ok contains_byte)
open VG.Proof.Pbkdf2.RISCV64 (Pre Sizes Entry key up tp scr nn sc scR keyR uR tR sc_al sc_sub)
open VG.Proof.Pbkdf2.RISCV64.Sha1 (it)
open VG.Spec.Sha1 (HashValue Word)
open VG.Proof.Pbkdf2.Sha1Words (beWords wIter)

/-- A big-endian word in a region a frame keeps. -/
theorem beWord_frame {rs : List Region} {m m' : Mem} {R : Region} {p : Addr} {off : Nat}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, R.Disjoint r) (hc : R.Contains (p + BitVec.ofNat 64 off) 4) :
    beWord m' p off = beWord m p off := by
  have e (k : Nat) (hk : k < 4) : m' (p + BitVec.ofNat 64 (off + k)) = m (p + BitVec.ofNat 64 (off + k)) :=
    hf _ fun r hr hx => hd r hr _ (contains_byte hc (k := k) hk) hx
  have e0 := e 0 (by decide)
  rw [Nat.add_zero] at e0
  simp only [beWord, e0, e 1 (by decide), e 2 (by decide), e 3 (by decide)]

/-- What the prologue keeps. -/
structure PS (Wi : Nat) (s₀ s : State) : Prop where
  a0 : s.gpr .a0 = key s₀
  a1 : s.gpr .a1 = up s₀
  b : s.gpr B = sc s₀
  tp : s.gpr TP = tp s₀
  frame : Frame [scR Wi s₀] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem PS.keep {Wi : Nat} {s₀ s s' : State} (h : PS Wi s₀ s) (hg : ∀ r, r ≠ T1 → r ≠ KR → s'.gpr r = s.gpr r)
    (hf : Frame [scR Wi s₀] s.mem s'.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    PS Wi s₀ s' :=
  ⟨by rw [hg _ (by decide) (by decide), h.a0], by rw [hg _ (by decide) (by decide), h.a1],
    by rw [hg _ (by decide) (by decide), h.b], by rw [hg _ (by decide) (by decide), h.tp], h.frame.trans hf,
    hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp⟩

section
variable {Wi : Nat} {s₀ : State} (hp : Pre it Wi s₀) (hz : Sizes it Wi)
include hp hz

omit hp in
/-- A word stored in the frame, within `scR`. -/
theorem frame_word {m : Mem} {d : Nat} (hd : d + 4 ≤ 164) (v : Word) :
    Frame [scR Wi s₀] m (m.writeW (sc s₀ + BitVec.ofNat 64 d) v) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (fc hz hd)

/-- The first `k` words of the hash value at `so(key)` copied to `fo` in the frame. -/
structure CI (so fo : Nat) (s₁ : State) (k : Nat) (s : State) : Prop where
  ps : PS Wi s₀ s
  done : ∀ j < k, fw s₀ s.mem (fo + 4 * j) = s₀.mem.readW (key s₀ + BitVec.ofNat 64 (so + 4 * j)) 32
  other : ∀ d, d + 4 ≤ fo ∨ fo + 20 ≤ d → d + 4 ≤ 164 → fw s₀ s.mem d = fw s₀ s₁.mem d
  saved : Spill.Saved (sc s₀) s₀.gpr saved s₁.mem → Spill.Saved (sc s₀) s₀.gpr saved s.mem
  gpr : ∀ r, r ≠ T1 → r ≠ KR → s.gpr r = s₁.gpr r

theorem cpLE_ok (so fo : Nat) (hso : so + 20 ≤ 168) (hso4 : so % 4 = 0) (hfo : 104 ≤ fo) (hfo' : fo + 20 ≤ 164)
    (hfa : fo % 4 = 0) (s₁ : State) (h₁ : PS Wi s₀ s₁) :
    WP isa (.block (cpLE so fo)) s₁ (CI (Wi := Wi) (s₀ := s₀) so fo s₁ 5) := by
  refine wp_range_flatMap (M := isa) (CI (Wi := Wi) (s₀ := s₀) so fo s₁) (fun k s hk h => ?_) 5 (Nat.le_refl _) s₁
    ⟨h₁, fun _ h => absurd h (by omega), fun _ _ _ => rfl, id, fun _ _ _ => rfl⟩
  rw [WP.block_append_iff]
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .a0 + BitVec.ofNat 64 (so + 4 * k)) 4 :=
    ⟨keyR it s₀, by rw [h.ps.rd, h.ps.wr, hp.rd, hp.wr]; simp,
      by rw [h.ps.a0]; exact Offset.contains_base _ (by simp only [it, Impl.Pbkdf2.RISCV64.It.S]; omega) (by omega)⟩
  refine WP.mono (loadLE32_ok (s := s) (d := T1) (tmp := KR) (n := .a0) (by decide) (by decide) (by decide)
    (by omega) hin) fun s₂ e₂ => ?_
  subst e₂
  refine wp_sw (a := sc s₀ + BitVec.ofNat 64 (fo + 4 * k)) (by omega)
    (by rw [RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide), h.ps.b])
    (fal s₀ (by omega)) (by exact fin hp hz h.ps.wr (by omega)) fun s₃ u₃ => WP.block_nil ?_
  have val : s.mem.readW (key s₀ + BitVec.ofNat 64 (so + 4 * k)) 32 =
      s₀.mem.readW (key s₀ + BitVec.ofNat 64 (so + 4 * k)) 32 :=
    h.ps.frame.readW (r := keyR it s₀) (Offset.contains_base _ (by simp only [it, Impl.Pbkdf2.RISCV64.It.S]; omega) (by omega))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.k_s) (by decide)
  have m₃ : s₃.mem = s.mem.writeW (sc s₀ + BitVec.ofNat 64 (fo + 4 * k))
      (s₀.mem.readW (key s₀ + BitVec.ofNat 64 (so + 4 * k)) 32) := by
    rw [u₃.mem, RegUpd.gpr_write_self, lo32_ext, RegUpd.mem_write, RegUpd.mem_write, h.ps.a0, val]
  have g₃ : ∀ r, r ≠ T1 → r ≠ KR → s₃.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₃.gpr, RegUpd.gpr_write_of_ne _ _ h1, RegUpd.gpr_write_of_ne _ _ h2]
  refine ⟨h.ps.keep g₃ (by rw [m₃]; exact frame_word hz (by omega) _) u₃.rd u₃.wr u₃.sp, fun j hj => ?_,
    fun d hd hd' => ?_, fun hsv => ?_, fun r h1 h2 => by rw [g₃ r h1 h2, h.gpr r h1 h2]⟩
  · rw [m₃]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [fw_write s₀ _ _ (by omega) (by omega) (by omega)]; exact h.done j hj
    · exact Mem.readW_writeW_self32 _ _ _
  · rw [m₃, fw_write s₀ _ _ (by omega) hd' (by omega)]; exact h.other d hd hd'
  · rw [m₃]; exact saved_write (h.saved hsv) _ (by omega) (by omega)

/-- The first `k` words of `T` copied to the frame. -/
structure TI (s₁ : State) (k : Nat) (s : State) : Prop where
  ps : PS Wi s₀ s
  done : ∀ j < k, fw s₀ s.mem (tO + 4 * j) = (beWords s₀.mem (tp s₀))[j]!
  other : ∀ d, d + 4 ≤ tO → fw s₀ s.mem d = fw s₀ s₁.mem d
  saved : Spill.Saved (sc s₀) s₀.gpr saved s₁.mem → Spill.Saved (sc s₀) s₀.gpr saved s.mem
  gpr : ∀ r, r ≠ T1 → r ≠ KR → s.gpr r = s₁.gpr r

omit hp hz in
theorem beWords_get (m : Mem) (p : Addr) {k : Nat} (hk : k < 5) : (beWords m p)[k]! = beWord m p (4 * k) := by
  rw [getElem!_pos _ k hk]; simp only [beWords, Vector.getElem_ofFn]; rfl

theorem cpT_ok (s₁ : State) (h₁ : PS Wi s₀ s₁) : WP isa (.block cpT) s₁ (TI (Wi := Wi) (s₀ := s₀) s₁ 5) := by
  refine wp_range_flatMap (M := isa) (TI (Wi := Wi) (s₀ := s₀) s₁) (fun k s hk h => ?_) 5 (Nat.le_refl _) s₁
    ⟨h₁, fun _ h => absurd h (by omega_using []), fun _ _ => rfl, id, fun _ _ _ => rfl⟩
  rw [WP.block_append_iff]
  have hc : (tR it s₀).Contains (tp s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
    Offset.contains_base _ (by simp only [it]; omega_using [hk]) (by omega_using [hk])
  have hin : InRegions (s.rd ++ s.wr) (s.gpr TP + BitVec.ofNat 64 (4 * k)) 4 :=
    ⟨tR it s₀, by rw [h.ps.rd, h.ps.wr, hp.rd, hp.wr]; simp, by rw [h.ps.tp]; exact hc⟩
  refine WP.mono (loadBE32_ok (s := s) (d := T1) (tmp := KR) (n := TP) (by decide) (by decide) (by decide)
    (by omega_using [hk]) hin) fun s₂ e₂ => ?_
  subst e₂
  refine wp_sw (a := sc s₀ + BitVec.ofNat 64 (tO + 4 * k)) (by simp only [tO]; omega_using [hk])
    (by rw [RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide), h.ps.b])
    (fal s₀ (by simp only [tO]; omega_using [])) (by exact fin hp hz h.ps.wr (by simp only [tO]; omega_using [hk]))
    fun s₃ u₃ => WP.block_nil ?_
  have val : beWord s.mem (s.gpr TP) (4 * k) = (beWords s₀.mem (tp s₀))[k]! := by
    rw [h.ps.tp, beWord_frame h.ps.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.t_s) hc, beWords_get _ _ hk]
  have m₃ : s₃.mem = s.mem.writeW (sc s₀ + BitVec.ofNat 64 (tO + 4 * k)) (beWords s₀.mem (tp s₀))[k]! := by
    rw [u₃.mem, RegUpd.gpr_write_self, lo32_ext, RegUpd.mem_write, RegUpd.mem_write, val]
  have g₃ : ∀ r, r ≠ T1 → r ≠ KR → s₃.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₃.gpr, RegUpd.gpr_write_of_ne _ _ h1, RegUpd.gpr_write_of_ne _ _ h2]
  refine ⟨h.ps.keep g₃ (by rw [m₃]; exact frame_word hz (by simp only [tO]; omega_using [hk]) _) u₃.rd u₃.wr u₃.sp,
    fun j hj => ?_, fun d hd => ?_, fun hsv => ?_, fun r h1 h2 => by rw [g₃ r h1 h2, h.gpr r h1 h2]⟩
  · rw [m₃]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [fw_write s₀ _ _ (by omega_using [hj]) (by simp only [tO]; omega_arith) (by simp only [tO]; omega_using [hk])]; exact h.done j hj
    · exact Mem.readW_writeW_self32 _ _ _
  · rw [m₃, fw_write s₀ _ _ (by omega_using [hd]) (by simp only [tO] at hd ⊢; omega_using [hd]) (by simp only [tO]; omega_using [hk])]
    exact h.other d hd
  · rw [m₃]; exact saved_write (h.saved hsv) _ (by simp only [tO]; omega_using []) (by simp only [tO]; omega_using [hk])

omit hp hz in
theorem A_nodup : ∀ i < 5, ∀ j < 5, i ≠ j → A.getD i .t0 ≠ A.getD j .t0 := by decide
omit hp hz in
theorem A_sp : ∀ k < 5, A.getD k .t0 ≠ .a0 ∧ A.getD k .t0 ≠ .a1 ∧ A.getD k .t0 ≠ B ∧ A.getD k .t0 ≠ TP ∧
    A.getD k .t0 ≠ KR ∧ A.getD k .t0 ≠ N := by decide

/-- The first `k` words of `U` loaded into `A`. -/
structure UI (s₁ : State) (k : Nat) (s : State) : Prop where
  done : ∀ j < k, (s.gpr (A.getD j .t0)).setWidth 32 = (beWords s₀.mem (up s₀))[j]!
  gpr : ∀ r, (∀ j < 5, r ≠ A.getD j .t0) → r ≠ KR → s.gpr r = s₁.gpr r
  mem : s.mem = s₁.mem
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  sp : s.sp = s₁.sp

omit hz in
theorem ldU_ok (s₁ : State) (h₁ : PS Wi s₀ s₁) : WP isa (.block ldU) s₁ (UI (s₀ := s₀) s₁ 5) := by
  refine wp_range_flatMap (M := isa) (UI (s₀ := s₀) s₁) (fun k s hk h => ?_) 5 (Nat.le_refl _) s₁
    ⟨fun _ h => absurd h (by omega_using []), fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
  have an := A_sp k hk
  have a1 : s.gpr .a1 = up s₀ := by
    rw [h.gpr _ (fun j hj => (A_sp j hj).2.1.symm) (by decide), h₁.a1]
  have hc : (uR it s₀).Contains (up s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
    Offset.contains_base _ (by simp only [it]; omega_using [hk]) (by omega_using [hk])
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .a1 + BitVec.ofNat 64 (4 * k)) 4 :=
    ⟨uR it s₀, by rw [h.rd, h.wr, h₁.rd, h₁.wr, hp.rd, hp.wr]; simp, by rw [a1]; exact hc⟩
  refine WP.mono (loadBE32_ok (s := s) (d := A.getD k .t0) (tmp := KR) (n := .a1) an.2.1 (by decide) an.2.2.2.2.1
    (by omega_using [hk]) hin) fun s₂ e₂ => ?_
  subst e₂
  have val : beWord s.mem (s.gpr .a1) (4 * k) = (beWords s₀.mem (up s₀))[k]! := by
    rw [a1, h.mem, beWord_frame h₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.u_s) hc, beWords_get _ _ hk]
  refine ⟨fun j hj => ?_, fun r hr h2 => ?_, by rw [RegUpd.mem_write, RegUpd.mem_write, h.mem],
    by rw [RegUpd.rd_write, RegUpd.rd_write, h.rd], by rw [RegUpd.wr_write, RegUpd.wr_write, h.wr],
    by rw [RegUpd.sp_write, RegUpd.sp_write, h.sp]⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [RegUpd.gpr_write_of_ne _ _ (A_nodup j (by omega_arith) k hk (by omega_using [hj])),
        RegUpd.gpr_write_of_ne _ _ (A_sp j (by omega_arith)).2.2.2.2.1]
      exact h.done j hj
    · rw [RegUpd.gpr_write_self, lo32_ext, val]
  · rw [RegUpd.gpr_write_of_ne _ _ (hr k hk), RegUpd.gpr_write_of_ne _ _ h2]; exact h.gpr r hr h2

end

/-! ## The whole prologue -/

/-- The final `T`, from the arguments. -/
abbrev Rf (s₀ : State) : HashValue :=
  wIter (Hi s₀) (Ho s₀) (nn s₀) (beWords s₀.mem (up s₀)) (beWords s₀.mem (tp s₀))

theorem save_eq : save = ([.addi B B 7, .logicImm .and B B (-8)] : List Instr) ++ Spill.saveCode B saved := rfl

theorem saved_fits : Spill.Fits saved := by decide

section
variable {Wi : Nat} {s₀ : State} (hp : Pre it Wi s₀) (hz : Sizes it Wi)
include hp hz

theorem pro_ok {e : State} (he : Entry s₀ e) : WP isa (.block (save ++ setup)) e (LI Wi s₀ (Rf s₀) (nn s₀)) := by
  rw [save_eq, List.append_assoc, WP.block_append_iff]
  refine WP.mono (Q := fun (e₁ : State) => e₁ = e.write B (sc s₀)) ?_ fun e₁ he₁ => ?_
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addi (show imm12 7 by decide),
      exec_logicImm (show imm12 (-8) by decide), RegUpd.gpr_write_self, RegUpd.write_write, Align.align_eq,
      Option.some.injEq, exists_eq_left']
    rw [he.other _ (by decide)]; rfl
  subst he₁
  have b₁ : (e.write B (sc s₀)).gpr B = sc s₀ := RegUpd.gpr_write_self _ _ _
  have g₁ (r : Reg) (hr : r ≠ B) : (e.write B (sc s₀)).gpr r = e.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine Spill.save_ok (b := B) (l := saved) (by rw [b₁]; exact sc_al) (by decide) (fun q hq => ?_) ?_
  · rw [b₁]; exact fin hp hz (by rw [RegUpd.wr_write, he.wr]) (by have := saved_bound q hq; omega_using [this])
  generalize hs₂ : ({ (e.write B (sc s₀)) with
    mem := Spill.saveMem (e.write B (sc s₀)).mem ((e.write B (sc s₀)).gpr B) (e.write B (sc s₀)).gpr saved } :
      State) = s₂
  have gpr₂ (r : Reg) (hr : r ≠ B) : s₂.gpr r = e.gpr r := by rw [← hs₂]; exact g₁ r hr
  have b₂ : s₂.gpr B = sc s₀ := by rw [← hs₂]; exact b₁
  have mem₂ : s₂.mem = Spill.saveMem s₀.mem (sc s₀) (e.write B (sc s₀)).gpr saved := by
    rw [← hs₂]; show Spill.saveMem _ _ _ _ = _; rw [b₁, RegUpd.mem_write, he.mem]
  have ps₂ : PS Wi s₀ s₂ := by
    refine ⟨by rw [gpr₂ _ (by decide), he.other _ (by decide)], by rw [gpr₂ _ (by decide), he.other _ (by decide)],
      b₂, by rw [gpr₂ _ (by decide), he.other _ (by decide)]; rfl, ?_, by rw [← hs₂]; exact he.rd,
      by rw [← hs₂]; exact he.wr, by rw [← hs₂]; exact he.sp⟩
    rw [mem₂]
    refine (Spill.saveMem_frame_base (n := 104) (fun q hq => (saved_bound q hq).2) (by decide) _ _ _).sub
      fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨scR Wi s₀, by simp, ?_⟩
    have := sc_sub (Wi := Wi) (s₀ := s₀) (a := 0) (n := 104) (by have := hz.fits; simp only [it] at this; omega_using [this])
    rwa [Proof.Pbkdf2.RISCV64.sc0] at this
  have sv₂ : Spill.Saved (sc s₀) s₀.gpr saved s₂.mem := by
    rw [mem₂]
    intro q hq
    rw [Spill.saveMem_saved saved_fits _ _ _ q hq]
    have : q.1 ≠ B ∧ q.1 ≠ .a2 := by revert q; decide
    rw [g₁ _ this.1, he.other _ this.2]
  -- The four parts of the setup.
  unfold setup
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (cpLE_ok hp hz 0 hiO (by decide) (by decide) (by decide) (by decide) (by decide) s₂ ps₂)
    fun s₃ h₃ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cpLE_ok hp hz 84 hoO (by decide) (by decide) (by decide) (by decide) (by decide) s₃ h₃.ps)
    fun s₄ h₄ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cpT_ok hp hz s₄ h₄.ps) fun s₅ h₅ => ?_
  refine WP.mono (ldU_ok hp s₅ h₅.ps) fun s₆ h₆ => ?_
  have m₆ : s₆.mem = s₅.mem := h₆.mem
  have keepA (r : Reg) (hA : ∀ j < 5, r ≠ A.getD j .t0) (h1 : r ≠ T1) (h2 : r ≠ KR) : s₆.gpr r = s₂.gpr r := by
    rw [h₆.gpr r hA h2, h₅.gpr r h1 h2, h₄.gpr r h1 h2, h₃.gpr r h1 h2]
  have notA (r : Reg) (h : r = B ∨ r = N ∨ r = TP) : ∀ j < 5, r ≠ A.getD j .t0 := fun j hj e => by
    rcases h with rfl | rfl | rfl
    · exact (A_sp j hj).2.2.1 e.symm
    · exact (A_sp j hj).2.2.2.2.2 e.symm
    · exact (A_sp j hj).2.2.2.1 e.symm
  refine ⟨?_, ?_, ?_, ⟨beWords s₀.mem (up s₀), beWords s₀.mem (tp s₀), h₆.done, fun k hk => by
      rw [m₆]; exact h₅.done k hk, rfl⟩, ⟨fun k hk => ?_, fun k hk => ?_⟩, ?_, by rw [h₆.rd]; exact h₅.ps.rd,
    by rw [h₆.wr]; exact h₅.ps.wr, by rw [h₆.sp]; exact h₅.ps.sp, by rw [m₆]; exact h₅.ps.frame⟩
  · rw [keepA _ (notA _ (.inl rfl)) (by decide) (by decide), b₂]
  · rw [keepA _ (notA _ (.inr (.inl rfl))) (by decide) (by decide), gpr₂ _ (by decide)]; exact he.a2
  · rw [keepA _ (notA _ (.inr (.inr rfl))) (by decide) (by decide), gpr₂ _ (by decide), he.other _ (by decide)]; rfl
  · rw [m₆, h₅.other _ (by simp only [hiO, tO]; omega_using [hk]), h₄.other _ (.inl (by simp only [hiO, hoO]; omega_using [hk]))
      (by simp only [hiO]; omega_using [hk]), h₃.done k hk, Nat.zero_add, getElem!_pos _ k hk, Proof.Sha1.StateMem.stateAt_get _ _ hk]
  · rw [m₆, h₅.other _ (by simp only [hoO, tO]; omega_using [hk]), h₄.done k hk, getElem!_pos _ k hk,
      Proof.Sha1.StateMem.stateAt_get _ _ hk, Offset.add_add]
  · rw [m₆]; exact h₅.saved (h₄.saved (h₃.saved sv₂))

end

end VG.Proof.Pbkdf2.Sha1.RISCV64

end

end


/-!
# PBKDF2-HMAC-SHA-1's iteration on RISC-V: the epilogue, and correctness

Untrusted: everything here is checked by Lean. The epilogue writes `T`'s
words to `t`, big-endian, which is the digest of the final `T`
(`out_ok`), and restores our caller's registers (`fin_ok`). `correct`: the
entry block, the prologue, the loop and the epilogue meet the iteration's
contract (`iterK`), since the digest of the final `T` on words is PBKDF2's
(`Sha1Words.iterate_digest`, `Md.iterate_hmac`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Sha1.RISCV64

open VG VG.RISCV64 VG.Impl.Pbkdf2.Sha1.RISCV64
open VG.RISCV64.ByteLoad (beBytes storeBE_ok)
open VG.WriteBytes (writeBytes)
open VG.Impl.Words.RISCV64 (storeBE)
open VG.Proof.Hmac.Common (writeBytes_at writeBytes_other)
open VG.Proof.Pbkdf2.RISCV64 (Pre Sizes Entry key up tp scr nn sc scR keyR uR tR sc_al sc_sub iterK)
open VG.Proof.Pbkdf2.RISCV64.Sha1 (it)
open VG.Spec.Sha1 (HashValue Word wordBytes)
open VG.Proof.Sha1 (md)
open VG.Proof.Pbkdf2.Sha1Words (beWords wIter digest_eq digest_beWords iterate_digest)

theorem shr_byte (x : BitVec 64) (s : Nat) : (x >>> s).setWidth 8 = x.extractLsb' s 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_ushiftRight, hi]

theorem setWidth_byte (w : Word) {s : Nat} (h : s + 8 ≤ 32) :
    (w.setWidth 64).extractLsb' s 8 = w.extractLsb' s 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi, show s + i < 32 by omega_using [h, hi], show s + i < 64 by omega_using [h, hi]]

/-- A word, as `storeBE 4` stores it. -/
theorem beBytes_word (w : Word) : beBytes 4 (w.setWidth 64) = wordBytes w := by
  simp only [beBytes, shr_byte]
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  simp (disch := decide) only [List.map_cons, List.map_nil, Nat.reduceMul, Nat.reduceSub, setWidth_byte,
    wordBytes]

/-- Byte `4k + i` of a digest. -/
theorem digest_getD (x : HashValue) {k i : Nat} (hk : k < 5) (hi : i < 4) :
    (md.digest x).getD (4 * k + i) 0 = (wordBytes x[k]!).getD i 0 := by
  rw [digest_eq, getElem!_pos x k hk]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 by omega_using [hk]) with rfl | rfl | rfl | rfl | rfl <;>
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_using [hi]) with rfl | rfl | rfl | rfl <;>
  simp [wordBytes]

theorem digest_length (x : HashValue) : (md.digest x).length = 20 := md.digest_length x

/-! ## `T` to `t` -/

/-- The first `k` words of `T` written to `t`, from the state `s₁` before. -/
structure OI (s₀ s₁ : State) (y : HashValue) (k : Nat) (s : State) : Prop where
  bytes : ∀ j < 20, s.mem (tp s₀ + BitVec.ofNat 64 j) =
    if j < 4 * k then (md.digest y).getD j 0 else s₁.mem (tp s₀ + BitVec.ofNat 64 j)
  frame : Frame [tR it s₀] s₁.mem s.mem
  gpr : ∀ r, r ≠ T1 → r ≠ KR → s.gpr r = s₁.gpr r
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  sp : s.sp = s₁.sp

section
variable {Wi : Nat} {s₀ : State} (hp : Pre it Wi s₀) (hz : Sizes it Wi)
include hp hz

/-- The frame's words, which the writes to `t` keep. -/
theorem fw_tR {m m' : Mem} (hf : Frame [tR it s₀] m m') {d : Nat} (hd : d + 4 ≤ 164) : fw s₀ m' d = fw s₀ m d :=
  hf.readW (r := scR Wi s₀) (fc hz hd) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.t_s.symm) (by decide)

theorem out_ok (s₁ : State) (y : HashValue) (hb : s₁.gpr B = sc s₀) (htp : s₁.gpr TP = tp s₀)
    (hy : ∀ k < 5, fw s₀ s₁.mem (tO + 4 * k) = y[k]!) (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) :
    WP isa (.block ((List.range 5).flatMap fun k => ([.load .w T1 B (tO + 4 * k)] : List Instr) ++ storeBE 4 T1 KR TP (4 * k)))
      s₁ (OI s₀ s₁ y 5) := by
  refine wp_range_flatMap (M := isa) (OI s₀ s₁ y) (fun k s hk h => ?_) 5 (Nat.le_refl _) s₁
    ⟨fun j _ => by simp, Frame.refl _ _, fun _ _ _ => rfl, rfl, rfl, rfl⟩
  have hb' : s.gpr B = sc s₀ := by rw [h.gpr _ (by decide) (by decide), hb]
  have htp' : s.gpr TP = tp s₀ := by rw [h.gpr _ (by decide) (by decide), htp]
  have rd' : s.rd = s₀.rd := h.rd.trans hrd
  have wr' : s.wr = s₀.wr := h.wr.trans hwr
  rw [List.singleton_append]
  refine wp_lw (a := sc s₀ + BitVec.ofNat 64 (tO + 4 * k)) (by simp only [tO]; omega_using [hk]) (by rw [hb'])
    (fal s₀ (by simp only [tO]; omega_using [])) (frd hp hz rd' wr' (by simp only [tO]; omega_using [hk])) fun s₂ u₂ => ?_
  have hv : s₂.gpr T1 = (y[k]!).setWidth 64 := by
    have e := fw_tR hp hz h.frame (d := tO + 4 * k) (by simp only [tO]; omega_using [hk])
    have e' := hy k hk
    simp only [fw] at e e'
    rw [u₂.gpr, e, e']
  have tp₂ : s₂.gpr TP = tp s₀ := by rw [u₂.other _ (by decide), htp']
  refine WP.mono (storeBE_ok (s := s₂) (v := T1) (tmp := KR) (n := TP) (off := 4 * k) (w := 4) (by decide)
    (by decide) (by decide) (by decide) (by omega_using [hk]) fun j hj => ?_) fun s₃ e₃ => ?_
  · rw [u₂.wr, wr', hp.wr, tp₂]
    exact ⟨tR it s₀, by simp, Offset.contains_base _ (by simp only [it]; omega_using [hk, hj]) (by omega_using [hk, hj])⟩
  subst e₃
  have m₃ : (({ s₂ with mem := writeBytes s₂.mem (s₂.gpr TP + BitVec.ofNat 64 (4 * k)) (beBytes 4 (s₂.gpr T1)) } :
      State).write KR (s₂.gpr T1)).mem = writeBytes s.mem (tp s₀ + BitVec.ofNat 64 (4 * k)) (wordBytes y[k]!) := by
    rw [RegUpd.mem_write]; show writeBytes _ _ _ = _; rw [u₂.mem, tp₂, hv, beBytes_word]
  have wl : (wordBytes y[k]!).length = 4 := rfl
  refine ⟨fun j hj => ?_, ?_, fun r h1 h2 => ?_, ?_, ?_, ?_⟩
  · rw [m₃]
    by_cases hin : 4 * k ≤ j ∧ j < 4 * k + 4
    · obtain ⟨i, rfl⟩ : ∃ i, j = 4 * k + i := ⟨j - 4 * k, by omega_using [hin]⟩
      rw [← Offset.add_add, writeBytes_at _ _ _ (by rw [wl]; omega_using [hin]) (by rw [wl]; decide),
        digest_getD y hk (by omega_using [hin])]
      simp only [show 4 * k + i < 4 * (k + 1) by omega_using [hin], ↓reduceIte]
    · rw [writeBytes_other _ _ _ (by
        rw [wl, Offset.lt_iff _ _ (by omega_using [hk]), Mem.sub_ofNat_toNat _ (by omega_using [hj])]; exact hin), h.bytes j hj]
      by_cases hjk : j < 4 * k
      · simp only [hjk, show j < 4 * (k + 1) by omega_using [hjk], ↓reduceIte]
      · simp only [hjk, show ¬ j < 4 * (k + 1) by omega_using [hin, hjk], ↓reduceIte]
  · rw [m₃]
    exact h.frame.trans (VG.WriteBytes.writeBytes_frame _ _ _ (by
      rw [wl]; exact Offset.contains_base _ (by simp only [it]; omega_using [hk]) (by omega_using [hk])))
  · rw [RegUpd.gpr_write_of_ne _ _ h2]
    show s₂.gpr r = _
    rw [u₂.other _ h1, h.gpr r h1 h2]
  · rw [RegUpd.rd_write]; show s₂.rd = _; rw [u₂.rd, h.rd]
  · rw [RegUpd.wr_write]; show s₂.wr = _; rw [u₂.wr, h.wr]
  · rw [RegUpd.sp_write]; show s₂.sp = _; rw [u₂.sp, h.sp]

omit hp hz in
theorem finish_eq : finish = ((List.range 5).flatMap fun k => ([.load .w T1 B (tO + 4 * k)] : List Instr) ++
    storeBE 4 T1 KR TP (4 * k)) ++ Spill.restoreCode B saved := rfl

theorem fin_ok {R : HashValue} {s : State} (h : LI Wi s₀ R 0 s) :
    WP isa (.block finish) s fun s' => abiPreserved s₀ s' ∧ Spec.Sha256.bytesAt s'.mem (tp s₀) 20 = md.digest R := by
  obtain ⟨x, y, hx, hy, hR⟩ := h.xy
  have hyR : y = R := hR
  subst hyR
  rw [finish_eq, WP.block_append_iff]
  refine WP.mono (out_ok hp hz s y h.b h.tp hy h.rd h.wr) fun s₁ h₁ => ?_
  have b₁ : s₁.gpr B = sc s₀ := by rw [h₁.gpr _ (by decide) (by decide), h.b]
  have sv₁ : Spill.Saved (sc s₀) s₀.gpr saved s₁.mem :=
    h.saved.frame h₁.frame fun q hq r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.t_s.symm.sub_left (sc_sub (by have := hz.fits; have := saved_bound q hq; simp only [it] at *; omega_arith))
  refine WP.mono (Spill.restore_wp (b := B) (l := saved) (B := sc s₀) sc_al b₁ (by decide) (by decide)
    (fun q hq => frd hp hz (h₁.rd.trans h.rd) (h₁.wr.trans h.wr) (by have := saved_bound q hq; omega_using [this])) sv₁)
    fun s₂ r₂ => ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · exact r₂.gpr_of (.inl (by revert r; decide))
  · rw [r₂.sp, h₁.sp, h.sp]
  · exact r₂.gpr_of (.inl (by decide))
  · rw [r₂.mem]
    apply List.ext_getElem (by simp [Spec.Sha256.bytesAt, digest_length])
    intro j h₁' h₂'
    simp only [Spec.Sha256.bytesAt, List.length_map, List.length_range] at h₁'
    simp only [Spec.Sha256.bytesAt, List.getElem_map, List.getElem_range]
    rw [h₁.bytes j h₁']
    simp only [show j < 4 * 5 by omega_using [h₁'], ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂',
      Option.getD_some]

end

theorem entry_eq : entry = Impl.Pbkdf2.RISCV64.It.entry := rfl

/-- `iterate` meets the iteration's contract, for SHA-1's link to the specification. -/
theorem correct {Wi : Nat} {s₀ : State} (hp : Pre it Wi s₀) (hz : Sizes it Wi)
    (hl : md.Link Spec.Hmac.sha1S Spec.Sha1.H0 20) :
    WP isa iterate s₀ fun s' => abiPreserved s₀ s' ∧ (iterK Spec.Hmac.sha1S Wi).post s₀ s' := by
  unfold iterate main
  refine WP.seq (WP.mono (by rw [entry_eq]; exact Proof.Pbkdf2.RISCV64.entry_ok s₀) fun e he => ?_)
  refine WP.seq (WP.mono (pro_ok hp hz he) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (loop_ok hp hz (Proof.Pbkdf2.RISCV64.nn_lt s₀) h₁) fun s₂ h₂ => ?_)
  refine WP.mono (fin_ok hp hz h₂) fun s' ⟨ha, hb⟩ => ⟨ha, ?_⟩
  intro k0 hk hi ho
  have hD : Spec.Hmac.sha1S.digestBytes = 20 := rfl
  rw [hD]
  rw [MdStream.Md.iterate_hmac hl hk hi ho _ (by simp [Spec.Sha256.bytesAt]),
    ← digest_beWords s₀.mem (s₀.gpr .a1), ← digest_beWords s₀.mem (s₀.gpr .a3),
    iterate_digest (md.stateAt s₀.mem (s₀.gpr .a0))
      (md.stateAt s₀.mem (s₀.gpr .a0 + BitVec.ofNat 64 Spec.Hmac.sha1S.stateBytes))]
  exact hb

end VG.Proof.Pbkdf2.Sha1.RISCV64

end

end


/-!
# PBKDF2-HMAC-SHA-1's iteration on RISC-V: `Verified`

Untrusted: everything here is checked by Lean. Constant time (`ct`), as for
every Merkle–Damgård hash function's iteration
(`Proof/Pbkdf2/RISCV64/Correct.lean`): the taint analysis of `main` after the
entry block, which zero-extends `n`, the one input public only in its low
32 bits (`RelCT.wpDep`). `verifiedW`: `correct` meets the iteration's
contract with `Wi` bytes of scratch space (`iterK`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Sha1.RISCV64

open VG VG.RISCV64 VG.Impl.Pbkdf2.Sha1.RISCV64
open VG.Proof.Pbkdf2.RISCV64 (Entry entry_ok nn iterK pre_of iterImp iterSat)
open VG.Proof.Pbkdf2.RISCV64.Sha1 (it hashOkW)

/-- The taint analysis of `main`, which the kernel checks. -/
theorem main_ck : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) main hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- `iterate` is constant time, for any precondition whose public data are `iterK`'s. -/
theorem ct {pre : State → Prop} {pub : State → State → Prop}
    (hpub : ∀ s₁ s₂, pub s₁ s₂ → s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
      (s₁.gpr .a2).setWidth 32 = (s₂.gpr .a2).setWidth 32 ∧ s₁.gpr .a3 = s₂.gpr .a3 ∧
      s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.sp = s₂.sp) :
    ConstantTime isa pre pub iterate := by
  obtain ⟨_, hb⟩ := main_ck
  refine RelCT.constantTime (Q := fun _ _ => True) (RelCT.seq ?_ (RelCT.taint (A := taint)
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) (fun _ _ h => h) hb))
  have ag4 : ∀ s₁ s₂ : State, pre s₁ ∧ pre s₂ ∧ pub s₁ s₂ →
      taint.Agree (Taint.ofRegs [.a0, .a1, .a3, .a4]) s₁ s₂ := by
    rintro s₁ s₂ ⟨_, _, hq⟩
    obtain ⟨h0, h1, _, h3, h4, hsp⟩ := hpub s₁ s₂ hq
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [h0, h1, h3, h4]
  refine RelCT.mono (RelCT.wpDep (F := Entry) (RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a3, .a4])
    ag4 (by rw [entry_eq]; taint_decide)) fun s₁ s₂ _ => ⟨by rw [entry_eq]; exact entry_ok s₁,
      by rw [entry_eq]; exact entry_ok s₂⟩) (fun _ _ h => h) ?_
  rintro s₁' s₂' ⟨-, σ₁, σ₂, ⟨_, _, hq⟩, a, b⟩
  obtain ⟨h0, h1, h2, h3, h4, hsp⟩ := hpub σ₁ σ₂ hq
  refine ⟨by rw [a.sp, b.sp, hsp], fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [a.other _ (by decide), b.other _ (by decide), h0]
  · rw [a.other _ (by decide), b.other _ (by decide), h1]
  · rw [a.a2, b.a2, nn, nn, h2]
  · rw [a.other _ (by decide), b.other _ (by decide), h3]
  · rw [a.other _ (by decide), b.other _ (by decide), h4]

theorem noFrames : iterate.noFrames = true := by decide

/-- `iterate` meets the iteration's contract, with `Wi` bytes of working space. -/
theorem verifiedW (Wi : Nat) (h₁ : 227 ≤ Wi) (h₂ : Wi ≤ 8192) :
    ∀ s, (iterK Spec.Hmac.sha1S Wi).pre s →
      ∃ t s', Exec isa iterate s t s' ∧ abiPreserved s s' ∧ (iterK Spec.Hmac.sha1S Wi).post s s' := by
  intro s hs
  have ho := hashOkW Wi h₁ h₂
  obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of (P := it) rfl rfl hs) ho.sizes ho.link
  exact ⟨t, s', he, h₁, h₂⟩

end VG.Proof.Pbkdf2.Sha1.RISCV64
