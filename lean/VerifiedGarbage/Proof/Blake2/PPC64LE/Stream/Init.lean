module

public import VerifiedGarbage.Proof.Blake2.PPC64LE.Stream.Common
public import VerifiedGarbage.Proof.MdStream.PPC64LE.Common
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Blake2.PPC64LE.Compress

/-!
# Streaming BLAKE2 on PPC64LE: `init`

`initState` stores the initial hash value (`initState_ok`); for a key,
`keyBlock` zeroes the buffer (`zero_ok`) and copies the key into it
(`keyLoop_ok`). `init` is a leaf function writing only `r5`, `r6` and
`r9`–`r12`.
-/

@[expose] public section

namespace VG.Proof.Blake2.PPC64LE.Stream.Init

open VG VG.PPC64LE VG.Spec.Blake2
open VG.Impl.Blake2.PPC64LE.Stream (N B initState)
open VG.Impl.Blake2.PPC64LE (sz ws movImm)
open VG.Proof.Blake2 (initPPC64LE bufOff repr_keyBlock stateAt_congr)
open VG.Proof.MdStream.PPC64LE (Upd Mupd WP.cons toNat_ofNat_lt wp_li wp_addi wp_subi wp_lbz wp_stb
  wp_std wp_stw wp_lsl ofNat_succ)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_snoc writeBytes_frame writeBytes_append
  write_eq_writeBytes)

/-! ## Instructions at the word size

A word of BLAKE2s is the low 32 bits of a register: `movImm` leaves only
those right, and the stores of words read only those. -/

section
variable {w : Nat} {is : List Instr} {s : State} {Q : State → Prop}

/-- `s'` is `s` with register `d` set to a value whose low `w` bits are `x`. -/
def UpdW (w : Nat) (s s' : State) (d : Reg) (x : BitVec w) : Prop :=
  ∃ v : BitVec 64, v.setWidth w = x ∧ Upd s s' d v

theorem wp_movImm (hw : w = 64 ∨ w = 32) {d : Reg} {x : BitVec w} {rest : List Instr}
    (k : ∀ s', UpdW w s s' d x → WP isa (.block rest) s' Q) :
    WP isa (.block (movImm w d (x.setWidth 64) ++ rest)) s Q := by
  rcases hw with rfl | rfl
  · simp only [movImm, ite_true, List.cons_append, List.nil_append]
    refine WP.cons exec_lis (WP.cons exec_ori (WP.cons (exec_lsl (by decide)) (WP.cons exec_oris
      (WP.cons exec_ori (k _ ⟨x, BitVec.setWidth_eq _, ⟨?_, fun r h => ?_, rfl, rfl, rfl, rfl⟩⟩)))))
    · simp only [State.write, ite_true, BitVec.setWidth_eq]
      exact Proof.Blake2.PPC64LE.movImm64_eq x
    · simp [State.write, h]
  · simp only [movImm, show (32 : Nat) ≠ 64 by decide, ite_false, List.cons_append, List.nil_append]
    refine WP.cons exec_lis (WP.cons exec_ori (k _ ⟨_, Proof.Blake2.PPC64LE.movImm32_eq x,
      ⟨by simp [State.write], fun r h => by simp [State.write, h], rfl, rfl, rfl, rfl⟩⟩))

theorem wp_storew (hw : w = 64 ∨ w = 32) {t n : Reg} {off : Nat} {a : Addr}
    (ho : off < 2 ^ 15 ∧ off % 4 = 0)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a (w / 8))
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth w)) → WP isa (.block is) s' Q)
    (hn : n ≠ .r0 := by decide) :
    WP isa (.block (.store (sz w) t n off :: is)) s Q := by
  rcases hw with rfl | rfl
  · exact wp_std ho ha hout (fun s' h => k s' (by rwa [BitVec.setWidth_eq])) hn
  · exact wp_stw ho.1 ha hout k hn

theorem wp_xor {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .xor d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

end

/-! ## Sizes -/

section
variable {w : Nat} (hw : w = 64 ∨ w = 32)
include hw

theorem w_le : w ≤ 64 := by omega

theorem word_in {j : Nat} (hj : j < 8) : w / 8 * j + w / 8 ≤ bufOff w := by
  rcases hw with rfl | rfl <;> simp only [bufOff] <;> omega

theorem word_sep {j k : Nat} (h : j ≠ k) :
    w / 8 * j + w / 8 ≤ w / 8 * k ∨ w / 8 * k + w / 8 ≤ w / 8 * j := by
  rcases hw with rfl | rfl <;> omega

theorem sizes : bufOff w + blockBytes w < 2 ^ 32 ∧ 16 ≤ blockBytes w ∧ blockBytes w % 8 = 0 ∧
    blockBytes w < 2 ^ (w - 8) ∧ w / 8 < 2 ^ 64 ∧ bufOff w ≤ 64 ∧ 0 < w / 8 ∧ w / 8 ≤ 8 := by
  rcases hw with rfl | rfl <;> decide

theorem readW_writeW_self_w (m : Mem) (a : Addr) (v : BitVec w) : (m.writeW a v).readW a w = v := by
  rcases hw with rfl | rfl
  · exact Mem.readW_writeW_self64 m a v
  · exact Mem.readW_writeW_self32 m a v

theorem setWidth_back (x : BitVec w) : (x.setWidth 64).setWidth w = x := by
  rw [BitVec.setWidth_setWidth_of_le _ (w_le hw), BitVec.setWidth_eq]

/-- A shift left keeps the low bits of the shifted low bits. -/
theorem setWidth_shl (x : BitVec 64) : (x <<< 8).setWidth w = x.setWidth w <<< 8 := by
  have := w_le hw
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft]
  by_cases h : i < 8 <;> simp [h, hi, show i - 8 < w by omega, show i < 64 by omega]

omit hw in
/-- The low bits of a register holding `n`. -/
theorem ofNat_toNat_w (x : BitVec 64) : x.setWidth w = BitVec.ofNat w x.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp

end

/-! ## The initial hash value -/

section
variable {w : Nat} (P : Params w)

/-- `IV[k]`, for any `k`. -/
def ivAt (k : Nat) : BitVec w := if h : k < 8 then P.IV[k] else 0

/-- The store of `IV[k + 1]`. -/
def ivStep (k : Nat) : List Instr :=
  movImm w .r9 ((ivAt P (k + 1)).setWidth 64) ++ [.store (sz w) .r9 .r3 (ws w * (k + 1))]

theorem initState_eq : initState P = (List.range 7).flatMap (ivStep P) ++
    (movImm w .r9 ((P.IV[0] ^^^ 0x01010000).setWidth 64) ++
    ([.lsl .r10 .r6 8, .logic .xor .r9 .r9 .r10, .logic .xor .r9 .r9 .r4,
      .store (sz w) .r9 .r3 0] : List Instr)) := by
  rw [initState, List.append_assoc]
  rfl

/-- After storing `IV[1..k]`. -/
structure IvInv (s₀ : State) (k : Nat) (s : State) : Prop where
  gpr : ∀ r, r ≠ .r9 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨s₀.gpr .r3, bufOff w⟩] s₀.mem s.mem
  words : ∀ j < k, s.mem.readW (s₀.gpr .r3 + BitVec.ofNat 64 (w / 8 * (j + 1))) w = ivAt P (j + 1)

variable {P}

theorem iv_step (hw : w = 64 ∨ w = 32) {s₀ : State}
    (hwr : ∀ a n, InRegions [⟨s₀.gpr .r3, bufOff w⟩] a n → InRegions s₀.wr a n)
    (k : Nat) (s : State) (hk : k < 7) (h : IvInv P s₀ k s) :
    WP isa (.block (ivStep P k)) s (IvInv P s₀ (k + 1)) := by
  have hs := sizes hw
  have hin : (⟨s₀.gpr .r3, bufOff w⟩ : Region).Contains
      (s₀.gpr .r3 + BitVec.ofNat 64 (w / 8 * (k + 1))) (w / 8) :=
    Offset.contains_base _ (word_in hw (by omega)) (by have := word_in hw (j := k + 1) (by omega); omega)
  refine wp_movImm hw fun s₁ ⟨v₁, hv₁, u₁⟩ => wp_storew hw (a := s₀.gpr .r3 + BitVec.ofNat 64 (w / 8 * (k + 1)))
    ⟨by unfold ws; have := word_in hw (j := k + 1) (by omega); omega,
      by unfold ws; rcases hw with rfl | rfl <;> omega⟩ ?_ ?_
    fun s₂ g₂ => WP.block_nil ?_
  · rw [u₁.other _ (by decide), h.gpr _ (by decide)]; rfl
  · rw [u₁.wr, h.wr]; exact hwr _ _ ⟨_, List.mem_singleton_self _, hin⟩
  have hv : (s₁.gpr .r9).setWidth w = ivAt P (k + 1) := by rw [u₁.gpr, hv₁]
  refine ⟨fun r hr => by rw [g₂.gpr, u₁.other r hr, h.gpr r hr], by rw [g₂.rd, u₁.rd, h.rd],
    by rw [g₂.wr, u₁.wr, h.wr], by rw [g₂.sp, u₁.sp, h.sp], ?_, fun j hj => ?_⟩
  · rw [g₂.mem, u₁.mem]; exact h.frame.writeW (List.mem_singleton_self _) _ hin
  · rw [g₂.mem, hv, u₁.mem]
    by_cases e : j = k
    · subst e; exact readW_writeW_self_w hw _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep _ (word_sep hw (fun h => e (by omega)))
        (by have := word_in hw (j := j + 1) (by omega); omega)
        (by have := word_in hw (j := k + 1) (by omega); omega)) hs.2.2.2.2.1]
      exact h.words j (by omega)

/-- The state after `initState`. -/
structure StateOk (s₀ : State) (s : State) : Prop where
  gpr : ∀ r, r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨s₀.gpr .r3, bufOff w⟩] s₀.mem s.mem
  state : stateAt w s.mem (s₀.gpr .r3) = Spec.Blake2.init P (s₀.gpr .r4).toNat (s₀.gpr .r6).toNat

theorem initState_ok (hw : w = 64 ∨ w = 32) {s₀ : State}
    (hwr : ∀ a n, InRegions [⟨s₀.gpr .r3, bufOff w⟩] a n → InRegions s₀.wr a n) :
    WP isa (.block (initState P)) s₀ (StateOk (P := P) s₀) := by
  have hs := sizes hw
  have hle := w_le hw
  rw [initState_eq, WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (IvInv P s₀) (iv_step hw hwr) 7 (Nat.le_refl _) s₀
    ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega)⟩) fun s₇ h₇ => ?_
  have hin : (⟨s₀.gpr .r3, bufOff w⟩ : Region).Contains (s₀.gpr .r3 + BitVec.ofNat 64 0) (w / 8) :=
    Offset.contains_base _ (by have := word_in hw (j := 0) (by omega); omega) (by omega)
  refine wp_movImm hw fun s₁ ⟨v₁, hv₁, u₁⟩ => wp_lsl (by decide) fun s₂ u₂ => wp_xor fun s₃ u₃ =>
    wp_xor fun s₄ u₄ =>
    wp_storew hw (a := s₀.gpr .r3 + BitVec.ofNat 64 0) ⟨by decide, by decide⟩ ?_ ?_
    fun s₅ g₅ => WP.block_nil ?_
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      h₇.gpr _ (by decide)]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h₇.wr]; exact hwr _ _ ⟨_, List.mem_singleton_self _, hin⟩
  have g : ∀ r, r ≠ .r9 → r ≠ .r10 → s₅.gpr r = s₀.gpr r := fun r h1 h2 => by
    rw [g₅.gpr, u₄.other r h1, u₃.other r h1, u₂.other r h2, u₁.other r h1, h₇.gpr r h1]
  -- The word stored.
  have hv : (s₄.gpr .r9).setWidth w = P.IV[0] ^^^ 0x01010000 ^^^
      (BitVec.ofNat w (s₀.gpr .r6).toNat <<< 8) ^^^ BitVec.ofNat w (s₀.gpr .r4).toNat := by
    rw [u₄.gpr, u₃.other .r4 (by decide), u₃.gpr, u₂.other .r9 (by decide), u₂.gpr, u₁.gpr,
      u₂.other .r4 (by decide), u₁.other .r4 (by decide), u₁.other .r6 (by decide),
      h₇.gpr .r4 (by decide), h₇.gpr .r6 (by decide), BitVec.setWidth_xor, BitVec.setWidth_xor, hv₁,
      setWidth_shl hw, ofNat_toNat_w, ofNat_toNat_w]
    rfl
  have hm : s₅.mem = s₇.mem.writeW (s₀.gpr .r3 + BitVec.ofNat 64 0) ((s₄.gpr .r9).setWidth w) := by
    rw [g₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨g, by rw [g₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h₇.rd],
    by rw [g₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h₇.wr], by rw [g₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h₇.sp],
    ?_, ?_⟩
  · rw [hm]; exact h₇.frame.writeW (List.mem_singleton_self _) _ hin
  · apply Vector.ext
    intro j hj
    rw [stateAt, Vector.getElem_ofFn, Spec.Blake2.init, Vector.getElem_set, hm]
    simp only
    split
    · rename_i e; subst e
      rw [Nat.mul_zero, readW_writeW_self_w hw, hv]
    · obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hsep : Mem.Sep (s₀.gpr .r3 + BitVec.ofNat 64 (w / 8 * (j + 1))) (w / 8)
          (s₀.gpr .r3 + BitVec.ofNat 64 0) (w / 8) :=
        Offset.sep _ (.inr (by rw [Nat.mul_succ]; omega))
          (by have := word_in hw (j := j + 1) hj; omega) (by have := word_in hw (j := 0) (by omega); omega)
      rw [Mem.readW_writeW_sep hsep hs.2.2.2.2.1, h₇.words j (by omega)]
      simp only [ivAt, hj, ↓reduceDIte]

end

/-! ## The key block -/

section
variable {w : Nat}

theorem writeW_zero (m : Mem) (a : Addr) :
    m.writeW a (0 : BitVec 64) = writeBytes m a (List.replicate 8 0) := by
  rw [Mem.writeW, write_eq_writeBytes]; rfl

theorem writeBytes_at (m : Mem) (q : Addr) (xs : List Byte) {i : Nat} (hi : i < 2 ^ 64) :
    writeBytes m q xs (q + BitVec.ofNat 64 i) =
      if i < xs.length then xs.getD i 0 else m (q + BitVec.ofNat 64 i) := by
  simp only [writeBytes, Mem.sub_ofNat_toNat q hi]

theorem bytesAt_writeBytes {m : Mem} {q : Addr} {xs : List Byte} {n : Nat} (hn : n < 2 ^ 64)
    (hx : xs.length ≤ n) (hz : ∀ i < n, m (q + BitVec.ofNat 64 i) = 0) :
    bytesAt (writeBytes m q xs) q n = xs ++ List.replicate (n - xs.length) 0 := by
  apply List.ext_getElem (by simp [bytesAt]; omega)
  intro i h1 _
  simp only [bytesAt, List.length_map, List.length_range] at h1
  simp only [bytesAt, List.getElem_map, List.getElem_range, writeBytes_at m q xs (by omega : i < 2 ^ 64)]
  by_cases hi : i < xs.length
  · simp only [hi, ↓reduceIte]
    rw [List.getElem_append_left hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some]
  · simp only [hi, ↓reduceIte]
    rw [hz i h1, List.getElem_append_right (by omega), List.getElem_replicate]

/-- After zeroing `8 · j` bytes of the buffer, from `σ`. -/
structure ZInv (σ : State) (j : Nat) (s : State) : Prop where
  gpr : s.gpr = σ.gpr
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  sp : s.sp = σ.sp
  mem : s.mem = writeBytes σ.mem (σ.gpr .r3 + BitVec.ofNat 64 (bufOff w)) (List.replicate (8 * j) 0)

theorem zero_ok (hw : w = 64 ∨ w = 32) {σ : State} (hr9 : σ.gpr .r9 = 0)
    (hwr : ∀ a n, InRegions [⟨σ.gpr .r3, bufOff w + blockBytes w⟩] a n → InRegions σ.wr a n) :
    WP isa (.block ((List.range (B w / 8)).flatMap fun j => [.store .d .r9 .r3 (N w + 8 * j)])) σ
      (ZInv (w := w) σ (blockBytes w / 8)) := by
  have hs := sizes hw
  refine wp_range_flatMap (M := isa) (ZInv (w := w) σ) (fun j s hj h => ?_) _ (Nat.le_refl _) σ
    ⟨rfl, rfl, rfl, rfl, by rw [Nat.mul_zero, List.replicate_zero, writeBytes_nil]⟩
  rw [B_eq] at hj
  refine wp_std (a := σ.gpr .r3 + BitVec.ofNat 64 (bufOff w + 8 * j)) ⟨?_, ?_⟩ (by rw [h.gpr, N_eq])
    ?_ fun s' g' => WP.block_nil ⟨g'.gpr.trans h.gpr, g'.rd.trans h.rd, g'.wr.trans h.wr, g'.sp.trans h.sp, ?_⟩
  · rw [N_eq]; rcases hw with rfl | rfl <;> simp only [bufOff, blockBytes] at hj ⊢ <;> omega
  · rw [N_eq]; rcases hw with rfl | rfl <;> simp only [bufOff] <;> omega
  · rw [h.wr]; exact hwr _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩
  · have e := writeBytes_append σ.mem (σ.gpr .r3 + BitVec.ofNat 64 (bufOff w))
      (List.replicate (8 * j) 0) (List.replicate 8 0) (by simp; omega)
    rw [List.length_replicate] at e
    rw [g'.mem, h.mem, h.gpr, hr9, writeW_zero, ← Offset.add_ofNat_add_ofNat, e,
      List.replicate_append_replicate, Nat.mul_succ]

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .r3
abbrev kp : Addr := s₀.gpr .r5
abbrev kk : Nat := (s₀.gpr .r6).toNat
abbrev buf (w : Nat) : Addr := st s₀ + BitVec.ofNat 64 (bufOff w)
abbrev stR (w : Nat) : Region := ⟨st s₀, bufOff w + blockBytes w⟩
abbrev kR : Region := ⟨kp s₀, kk s₀⟩
/-- The key. -/
abbrev key : List Byte := bytesAt s₀.mem (kp s₀) (kk s₀)

end

/-- After copying `j` bytes of the key over the zeroed buffer `Z`. -/
structure KInv (s₀ : State) (Z : Mem) (j : Nat) (s : State) : Prop where
  j_le : j ≤ kk s₀
  r5 : s.gpr .r5 = kp s₀ + BitVec.ofNat 64 j
  r12 : s.gpr .r12 = buf s₀ w + BitVec.ofNat 64 j
  r6 : s.gpr .r6 = BitVec.ofNat 64 (kk s₀ - j)
  other : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r5 → r ≠ .r6 → r ≠ .r12 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mem : s.mem = writeBytes Z (buf s₀ w) ((key s₀).take j)

theorem keyLoop_ok (hw : w = 64 ∨ w = 32) {s₀ : State} {Z : Mem} {σ : State}
    (hrd : s₀.rd = [kR s₀]) (hwr : s₀.wr = [stR s₀ w]) (hd : (kR s₀).Disjoint (stR s₀ w))
    (hk : 1 ≤ kk s₀) (hkb : kk s₀ ≤ blockBytes w) (hZ : Frame [stR s₀ w] s₀.mem Z)
    (hσ : KInv (w := w) s₀ Z 0 σ) :
    WP isa (.loop (.block [.lbz .r9 .r5 0, .stb .r9 .r12 0, .addi .r5 .r5 1,
        .addi .r12 .r12 1, .subi .r6 .r6 1]) (.nonzero .d .r6)) σ
      (KInv (w := w) s₀ Z (kk s₀)) := by
  have hs := sizes hw
  have hkl : kk s₀ < 2 ^ 64 := (s₀.gpr .r6).isLt
  refine WP.loop (M := isa) (fun n (s : State) => ∃ j, n = kk s₀ - j ∧ j < kk s₀ ∧ KInv (w := w) s₀ Z j s)
    ?_ (kk s₀) σ ⟨0, by omega, by omega, hσ⟩
  rintro n s ⟨j, rfl, hj, h⟩
  -- The key byte read is unchanged.
  have hbyte : s.mem (kp s₀ + BitVec.ofNat 64 j) = s₀.mem (kp s₀ + BitVec.ofNat 64 j) := by
    rw [h.mem]
    have hf : Frame [stR s₀ w] s₀.mem (writeBytes Z (buf s₀ w) ((key s₀).take j)) :=
      hZ.trans (writeBytes_frame Z _ _ (Offset.contains_base _ (by simp; omega) (by omega)))
    exact hf.bytes (R := kR s₀) (by simpa using hd) (by simp; omega) hj
  have hin : InRegions (s.rd ++ s.wr) (kp s₀ + BitVec.ofNat 64 j) 1 := by
    rw [h.rd, hrd]; exact ⟨_, List.mem_cons_self .., Offset.contains_base _ (by omega) (by omega)⟩
  have hout : InRegions s.wr (buf s₀ w + BitVec.ofNat 64 j) 1 := by
    rw [h.wr, hwr, Offset.add_ofNat_add_ofNat]
    exact ⟨_, List.mem_cons_self .., Offset.contains_base _ (by omega) (by omega)⟩
  refine wp_lbz (a := kp s₀ + BitVec.ofNat 64 j) (by decide) (by rw [h.r5]; simp) hin fun s₁ u₁ => ?_
  refine wp_stb (a := buf s₀ w + BitVec.ofNat 64 j) (by decide) (by rw [u₁.other _ (by decide), h.r12]; simp)
    (by rw [u₁.wr]; exact hout) fun s₂ g₂ => ?_
  refine wp_addi (by decide) fun s₃ u₃ => wp_addi (by decide) fun s₄ u₄ =>
    wp_subi (by decide) fun s₅ u₅ => WP.block_nil ?_
  have hr6 : s₅.gpr .r6 = BitVec.ofNat 64 (kk s₀ - (j + 1)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.r6,
      sub_ofNat (by omega), Nat.sub_sub]
  have hI : KInv (w := w) s₀ Z (j + 1) s₅ := by
    refine ⟨by omega, ?_, ?_, hr6, fun r h1 h2 h3 h4 h5 => ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂.gpr, u₁.other _ (by decide), h.r5,
        BitVec.add_assoc, ← BitVec.ofNat_add]
    · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.r12,
        BitVec.add_assoc, ← BitVec.ofNat_add]
    · rw [u₅.other r h4, u₄.other r h5, u₃.other r h3, g₂.gpr, u₁.other r h1, h.other r h1 h2 h3 h4 h5]
    · rw [u₅.rd, u₄.rd, u₃.rd, g₂.rd, u₁.rd, h.rd]
    · rw [u₅.wr, u₄.wr, u₃.wr, g₂.wr, u₁.wr, h.wr]
    · rw [u₅.sp, u₄.sp, u₃.sp, g₂.sp, u₁.sp, h.sp]
    · have hj' : j < (key s₀).length := by simp [bytesAt]; omega
      have hl : (List.take j (key s₀)).length = j := by
        rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
      rw [u₅.mem, u₄.mem, u₃.mem, g₂.mem, u₁.mem, u₁.gpr, hbyte, h.mem, List.take_add_one,
        List.getElem?_eq_getElem hj', Option.toList_some,
        writeBytes_snoc _ _ _ _ (by rw [hl]; omega), hl, setWidth_byte]
      congr 1
      simp [bytesAt]
  by_cases hjk : j + 1 = kk s₀
  · refine .inl ⟨?_, hjk ▸ hI⟩
    show VG.PPC64LE.eval (.nonzero .d .r6) s₅ = _
    rw [MdStream.PPC64LE.eval_nonzero, hr6, bne, MdStream.PPC64LE.ofNat_beq_zero (by omega)]
    simp; omega
  · refine .inr ⟨?_, kk s₀ - (j + 1), by omega, j + 1, rfl, by omega, hI⟩
    show VG.PPC64LE.eval (.nonzero .d .r6) s₅ = _
    rw [MdStream.PPC64LE.eval_nonzero, hr6, bne, MdStream.PPC64LE.ofNat_beq_zero (by omega)]
    simp; omega

end

section
variable {w : Nat} {P : Params w}

theorem keyBlock_eq : Impl.Blake2.PPC64LE.Stream.keyBlock (w := w) =
    .seq (.block ((.li .r9 0 :: (List.range (B w / 8)).flatMap fun j =>
        ([.store .d .r9 .r3 (N w + 8 * j)] : List Instr)) ++ ([.addi .r12 .r3 (N w)] : List Instr)))
      (.loop (.block [.lbz .r9 .r5 0, .stb .r9 .r12 0, .addi .r5 .r5 1, .addi .r12 .r12 1,
        .subi .r6 .r6 1]) (.nonzero .d .r6)) := by
  rw [Impl.Blake2.PPC64LE.Stream.keyBlock, List.map_eq_flatMap]

theorem keyBlock_ok (hw : w = 64 ∨ w = 32) {s₀ σ : State}
    (hrd : s₀.rd = [kR s₀]) (hwr : s₀.wr = [stR s₀ w]) (hd : (kR s₀).Disjoint (stR s₀ w))
    (hk : 1 ≤ kk s₀) (hkb : kk s₀ ≤ blockBytes w) (hσ : StateOk (P := P) s₀ σ) :
    WP isa (Impl.Blake2.PPC64LE.Stream.keyBlock (w := w)) σ fun s =>
      (∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r5 → r ≠ .r6 → r ≠ .r12 → s.gpr r = s₀.gpr r) ∧
      s.sp = s₀.sp ∧ Frame [⟨buf s₀ w, blockBytes w⟩] σ.mem s.mem ∧
      bytesAt s.mem (buf s₀ w) (blockBytes w) = key s₀ ++ List.replicate (blockBytes w - kk s₀) 0 := by
  have hs := sizes hw
  have hxs : (key s₀).length = kk s₀ := by simp [bytesAt]
  have hbuf : ∀ n, n ≤ blockBytes w → (stR s₀ w).Contains (buf s₀ w) n := fun n hn =>
    Offset.contains_base _ (by omega) (by omega)
  have hσ0 : σ.gpr .r3 = st s₀ := hσ.gpr _ (by decide) (by decide)
  rw [keyBlock_eq]
  refine WP.seq (wp_li (by decide) fun σ₁ u₁ => ?_)
  rw [List.append_eq, WP.block_append_iff]
  refine WP.mono (zero_ok hw (σ := σ₁) (by rw [u₁.gpr]; rfl) ?_) fun s₂ h₂ => ?_
  · rw [u₁.wr, hσ.wr, hwr, u₁.other _ (by decide), hσ0]; exact fun _ _ h => h
  have hZ : s₂.mem = writeBytes σ.mem (buf s₀ w) (List.replicate (blockBytes w) 0) := by
    rw [h₂.mem, u₁.other _ (by decide), hσ0, u₁.mem, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hs.2.2.1)]
  have hfZ : Frame [stR s₀ w] s₀.mem s₂.mem := by
    rw [hZ]
    exact (hσ.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨stR s₀ w, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩).trans
      (writeBytes_frame _ _ _ (by simpa using hbuf _ (Nat.le_refl _)))
  refine wp_addi (by rw [N_eq]; omega) fun s₃ u₃ => WP.block_nil ?_
  refine WP.mono (keyLoop_ok hw hrd hwr hd hk hkb hfZ ⟨Nat.zero_le _, ?_, ?_, ?_, ?_,
    by rw [u₃.rd, h₂.rd, u₁.rd, hσ.rd], by rw [u₃.wr, h₂.wr, u₁.wr, hσ.wr],
    by rw [u₃.sp, h₂.sp, u₁.sp, hσ.sp], ?_⟩) fun s h => ?_
  · rw [u₃.other _ (by decide), h₂.gpr, u₁.other _ (by decide), hσ.gpr _ (by decide) (by decide)]; simp
  · rw [u₃.gpr, h₂.gpr, u₁.other _ (by decide), hσ0, N_eq]; simp
  · rw [u₃.other _ (by decide), h₂.gpr, u₁.other _ (by decide), hσ.gpr _ (by decide) (by decide),
      Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · intro r h1 h2 h3 h4 h5
    rw [u₃.other r h5, h₂.gpr, u₁.other r h1, hσ.gpr r h1 h2]
  · rw [u₃.mem, List.take_zero, writeBytes_nil]
  have hm : s.mem = writeBytes (writeBytes σ.mem (buf s₀ w) (List.replicate (blockBytes w) 0))
      (buf s₀ w) (key s₀) := by
    rw [h.mem, List.take_of_length_le (by omega), hZ]
  refine ⟨h.other, h.sp, ?_, ?_⟩
  · rw [hm]
    exact (writeBytes_frame _ _ _ (contains_prefix _ (by simp))).trans
      (writeBytes_frame _ _ _ (contains_prefix _ (by omega)))
  · rw [hm, bytesAt_writeBytes (by omega) (by omega) fun i hi => ?_, hxs]
    rw [writeBytes_at _ _ _ (by omega)]
    simp [hi]

end

/-! ## The whole function -/

/-- `init` stores the initial hash value and, for a key, the key block. -/
theorem correct {w : Nat} {P : Params w} {s₀ : State} (hP : Ok P) (hp : (initPPC64LE P).pre s₀) :
    WP isa (Impl.Blake2.PPC64LE.Stream.init P) s₀ fun s' =>
      GprAbi s₀ s' ∧ (initPPC64LE P).post s₀ s' := by
  obtain ⟨hrd, hwr, hd, -, -, hkk⟩ := hp
  have hw := hP.w
  have hs := sizes hw
  have hkb : kk s₀ ≤ blockBytes w := Nat.le_trans hkk hP.max
  have hxs : (key s₀).length = kk s₀ := by simp [bytesAt]
  have hsub : ∀ r ∈ [(⟨st s₀, bufOff w⟩ : Region)], ∃ r' ∈ [stR s₀ w], Region.Sub r r' := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨stR s₀ w, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
  have hcs : ∀ r ∈ preserved, r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r12 := by decide
  unfold Impl.Blake2.PPC64LE.Stream.init
  refine WP.seq (WP.mono (initState_ok (P := P) hw (fun a n h => ?_)) fun σ hσ => ?_)
  · rw [hwr]
    obtain ⟨r, hr, hc⟩ := h
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩
  have hr6 : σ.gpr .r6 = BitVec.ofNat 64 (kk s₀) := by
    rw [hσ.gpr _ (by decide) (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.ite _ (zero_iff σ hr6 (s₀.gpr .r6).isLt) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine ⟨⟨fun r hr => hσ.gpr r (hcs r hr).1 (hcs r hr).2.1, hσ.sp⟩, ?_⟩
    exact repr_keyBlock P hP.pos (hxs ▸ hkb) hσ.state fun h => absurd (hxs ▸ hb) h
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.mono (keyBlock_ok hw hrd hwr hd (by omega) hkb hσ) fun s ⟨hg, hsp, hf, hb'⟩ => ?_
    refine ⟨⟨fun r hr => hg r (hcs r hr).1 (hcs r hr).2.1 (hcs r hr).2.2.1 (hcs r hr).2.2.2.1
      (hcs r hr).2.2.2.2, hsp⟩, ?_⟩
    refine repr_keyBlock P hP.pos (hxs ▸ hkb) ?_ fun _ => by rw [hxs]; exact hb'
    rw [← hσ.state]
    exact stateAt_congr fun i hi => hf.bytes (R := ⟨st s₀, bufOff w⟩)
      (by simpa using Offset.base_disjoint (st s₀) (Nat.le_refl (bufOff w)) (n := blockBytes w) (by omega))
      (by simp only; omega) hi

end VG.Proof.Blake2.PPC64LE.Stream.Init
