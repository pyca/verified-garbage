module

public import VerifiedGarbage.Impl.Scrypt.X86_64.Salsa
public import VerifiedGarbage.Proof.Scrypt.Spec
import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Framework.X86_64.Spill
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Scrypt.X86_64.Salsa
meta import VerifiedGarbage.Proof.Scrypt.Spec
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.X86_64.Spill
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# The Salsa20/8 Core on x86-64: the rounds
-/

@[expose] public section

namespace VG.Proof.Scrypt.X86_64

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Spec.Scrypt (Word)
open VG.Proof.Scrypt

/-! ## Addresses -/

/-- An address `p + d` as the code computes it. -/
abbrev bufAt (p : Addr) (d : Nat) : Addr := p + BitVec.ofInt 64 (d : Int)

theorem ofInt_natCast (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = s.gpr b + BitVec.ofInt 64 (d : Int) := rfl

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem contains_off {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (bufAt base off) n := by
  simp only [bufAt, ofInt_natCast]; exact Offset.contains_base base h ho

theorem off_sep (p : Addr) {d e n k : Nat} (hd : d < 2 ^ 32) (he : e < 2 ^ 32) (hn : n ≤ 8)
    (hk : k ≤ 8) (h : d + n ≤ e ∨ e + k ≤ d) :
    Mem.Sep (bufAt p d) n (bufAt p e) k := by
  simp only [bufAt, ofInt_natCast]; exact Offset.sep p h (by omega_arith) (by omega_arith)

/-- Reading a 32-bit word after writing a (32- or 64-bit) value elsewhere near `p`. -/
theorem readW_writeW_off (m : Mem) (p : Addr) {w' : Nat} (v : BitVec w') {d e : Nat}
    (hw' : w' = 32 ∨ w' = 64) (hd : d < 2 ^ 32) (he : e < 2 ^ 32) (h : d + 4 ≤ e ∨ e + w' / 8 ≤ d) :
    (m.writeW (bufAt p e) v).readW (bufAt p d) 32 = m.readW (bufAt p d) 32 :=
  Mem.readW_writeW_sep (off_sep p hd he (by omega_arith) (by omega_arith) h) (by decide)

/-- `scratch`. -/
abbrev scR (p : Addr) : Region := ⟨p, 64⟩
/-- The home slots of words 12–15, at the start of `scratch`. -/
abbrev slotR (p : Addr) : Region := ⟨p, 16⟩

theorem in_sc {rs ws : List Region} {p : Addr} (hw : scR p ∈ ws) {d n : Nat} (h : d + n ≤ 64) :
    InRegions (rs ++ ws) (bufAt p d) n :=
  ⟨scR p, List.mem_append_right _ hw, contains_off h (by omega_arith)⟩

theorem out_sc {ws : List Region} {p : Addr} (hw : scR p ∈ ws) {d n : Nat} (h : d + n ≤ 64) :
    InRegions ws (bufAt p d) n :=
  ⟨scR p, hw, contains_off h (by omega_arith)⟩

/-! ## Registers -/

theorem wreg_ne : ∀ k < 12, wreg k ≠ .rax ∧ wreg k ≠ .rsi ∧ wreg k ≠ .rdi ∧ wreg k ≠ .rsp := by
  decide

theorem wreg_inj : ∀ a < 12, ∀ b < 12, wreg a = wreg b → a = b := by decide

/-! ## One instruction -/

/-- `s'` is `s` with register `d` set to `x` (and possibly the flags changed). -/
structure Upd (d : Reg) (x : BitVec 64) (s s' : State) : Prop where
  gpr : s'.gpr d = x
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem mov32_upd {s : State} {d : Reg} {src : Src} {x : Word} (hr : readSrc32 s src = some x) :
    ∃ s', exec (.mov32 d src) s = some s' ∧ Upd d (x.setWidth 64) s s' := by
  simp only [exec, hr, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨by simp [State.setReg32, State.setReg], fun r hr => by simp [State.setReg32, State.setReg, hr],
    rfl, rfl, rfl⟩

theorem add32_upd {s : State} {d : Reg} {src : Src} {x : Word} (hr : readSrc32 s src = some x) :
    ∃ s', exec (.alu32 .add d src) s = some s' ∧
      Upd d (((s.gpr d).setWidth 32 + x).setWidth 64) s s' := by
  simp only [exec, execAlu32, hr, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨by simp [State.setReg32, State.setReg],
    fun r hr => by simp [State.setReg32, State.setReg, arithFlags, State.setFlags, hr], rfl, rfl, rfl⟩

theorem xor32_upd {s : State} {d : Reg} {src : Src} {x : Word} (hr : readSrc32 s src = some x) :
    ∃ s', exec (.alu32 .xor d src) s = some s' ∧
      Upd d (((s.gpr d).setWidth 32 ^^^ x).setWidth 64) s s' := by
  simp only [exec, execAlu32, hr, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨by simp only [State.setReg32, State.setReg, ite_true],
    fun r hr => by simp [State.setReg32, State.setReg, arithFlags, State.setFlags, hr], rfl, rfl, rfl⟩

theorem ror32_upd {s : State} {d : Reg} {n : Nat} (h1 : 1 ≤ n) (h2 : n ≤ 31) :
    ∃ s', exec (.shift32 .ror d n) s = some s' ∧
      Upd d ((((s.gpr d).setWidth 32).rotateRight n).setWidth 64) s s' := by
  simp only [exec, execShift32, h1, h2, and_self, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨by simp only [State.setReg32, State.setReg, ite_true],
    fun r hr => by simp [State.setReg32, State.setReg, State.setFlags, hr], rfl, rfl, rfl⟩

theorem store32_exec {s : State} {m : MemOp} {r : Reg} (h : InRegions s.wr (s.ea m) 4) :
    exec (.store32 m r) s = some { s with mem := s.mem.writeW (s.ea m) ((s.gpr r).setWidth 32) } := by
  simp only [exec, State.store32, h, ite_true]

/-- Running one instruction, then the rest of the block. -/
theorem wp_cons {i : Instr} {is : List Instr} {s : State} {Q : State → Prop} {P : State → Prop}
    (he : ∃ s', exec i s = some s' ∧ P s') (hk : ∀ s', P s' → WP isa (.block is) s' Q) :
    WP isa (.block (i :: is)) s Q := by
  obtain ⟨s', h, hp⟩ := he
  exact WP.block_cons_iff.mpr ⟨s', h, hk s' hp⟩

/-! ## Where the words are -/

/-- The rounds invariant, relative to the state `s₀` at the start of the
rounds: words 0–11 of `v` in their registers, words 12–15 in their slots. -/
structure RI (p : Addr) (v : Vector Word 16) (s₀ s : State) : Prop where
  regs : ∀ k (hk : k < 12), s.gpr (wreg k) = (v[k]'(by omega_arith)).setWidth 64
  slots : ∀ k (hk : k < 16), 12 ≤ k → s.mem.readW (bufAt p (slotOff k)) 32 = (v[k]'(by omega_arith))
  frame : Frame [slotR p] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsi : s.gpr .rsi = p
  rdi : s.gpr .rdi = s₀.gpr .rdi
  rsp : s.gpr .rsp = s₀.gpr .rsp

theorem RI.upd_rax {p : Addr} {v : Vector Word 16} {s₀ s s' : State} (h : RI p v s₀ s)
    {x : BitVec 64} (hu : Upd .rax x s s') : RI p v s₀ s' where
  regs k hk := (hu.other _ (wreg_ne k hk).1).trans (h.regs k hk)
  slots k hk h12 := hu.mem ▸ h.slots k hk h12
  frame := hu.mem ▸ h.frame
  rd := hu.rd.trans h.rd
  wr := hu.wr.trans h.wr
  rsi := (hu.other _ (by decide)).trans h.rsi
  rdi := (hu.other _ (by decide)).trans h.rdi
  rsp := (hu.other _ (by decide)).trans h.rsp

theorem src_read {p : Addr} {v : Vector Word 16} {s₀ s : State} (h : RI p v s₀ s)
    (hw : scR p ∈ s₀.wr) {k : Nat} (hk : k < 16) : readSrc32 s (src k) = some (v[k]'(by omega_arith)) := by
  unfold src
  split
  · rename_i hk12
    simp [readSrc32, h.regs k hk12]
  · rename_i hk12
    have hin : InRegions (s.rd ++ s.wr) (bufAt p (slotOff k)) 4 :=
      in_sc (h.wr ▸ hw) (by simp only [slotOff]; omega_arith)
    simp only [readSrc32, ea_at, h.rsi, State.load32, hin, ite_true]
    rw [h.slots k hk (by omega_arith)]

/-! ## One line -/

theorem ite_pos' {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

theorem ite_neg' {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬c) :
    (if c then a else b) = b := by simp [h]

/-- The side conditions of `line_ok`, decidable for concrete arguments. -/
def LSide (i j k n : Nat) : Bool :=
  decide (i < 16 ∧ j < 16 ∧ k < 16 ∧ 1 ≤ n ∧ n ≤ 31)

/-- The first three instructions of a line: `eax = R((x[j]'(by omega)) + (x[k]'(by omega)), n)`. -/
theorem sum_ok {p : Addr} {v : Vector Word 16} {s₀ s : State} (h : RI p v s₀ s)
    (hw : scR p ∈ s₀.wr) {i j k n : Nat} (hj : j < 16) (hk : k < 16) (h1 : 1 ≤ n) (h2 : n ≤ 31)
    {Q : State → Prop}
    (hQ : ∀ s', RI p v s₀ s' → s'.gpr .rax = (((v[j]'(by omega_arith)) + (v[k]'(by omega_arith))).rotateLeft n).setWidth 64 →
      WP isa (.block (if i < 12 then [.alu32 .xor (wreg i) (.reg .rax)]
        else [.alu32 .xor .rax (.mem (at_ .rsi (slotOff i))),
          .store32 (at_ .rsi (slotOff i)) .rax])) s' Q) :
    WP isa (.block (line i j k n)) s Q := by
  rw [line, List.cons_append, List.cons_append, List.cons_append, List.nil_append]
  refine wp_cons (mov32_upd (d := .rax) (src_read h hw hj)) fun s₁ u₁ => ?_
  have h₁ := h.upd_rax u₁
  refine wp_cons (add32_upd (d := .rax) (src_read h₁ hw hk)) fun s₂ u₂ => ?_
  have h₂ := h₁.upd_rax u₂
  refine wp_cons (ror32_upd (d := .rax) (s := s₂) (n := 32 - n) (by omega_arith) (by omega_arith))
    fun s₃ u₃ => ?_
  refine hQ s₃ (h₂.upd_rax u₃) ?_
  rw [u₃.gpr, u₂.gpr, u₁.gpr, rotateLeft_eq _ (by omega_arith) (by omega_arith)]
  simp

theorem line_ok {i j k n : Nat} (hs : LSide i j k n = true) {p : Addr} {v : Vector Word 16}
    {s₀ s : State} (h : RI p v s₀ s) (hw : scR p ∈ s₀.wr) :
    WP isa (.block (line i j k n)) s (RI p (stepN v i j k n) s₀) := by
  simp only [LSide, decide_eq_true_eq] at hs
  obtain ⟨hi, hj, hk, h1, h2⟩ := hs
  refine sum_ok h hw hj hk h1 h2 fun s₃ h₃ hrax => ?_
  have get := stepN_get v n hi hj hk
  split
  · rename_i hi12
    refine wp_cons (xor32_upd (d := wreg i) (s := s₃) (src := .reg .rax) rfl) fun s₄ u₄ => ?_
    refine WP.block_nil ⟨fun m hm => ?_, fun m hm h12 => ?_, u₄.mem ▸ h₃.frame, u₄.rd.trans h₃.rd,
      u₄.wr.trans h₃.wr, (u₄.other _ (wreg_ne i hi12).2.1.symm).trans h₃.rsi,
      (u₄.other _ (wreg_ne i hi12).2.2.1.symm).trans h₃.rdi,
      (u₄.other _ (wreg_ne i hi12).2.2.2.symm).trans h₃.rsp⟩
    · rw [get m (by omega_arith)]
      by_cases e : i = m
      · subst e
        rw [ite_pos' rfl, u₄.gpr, h₃.regs i hi12, hrax]
        simp
      · rw [ite_neg' e, u₄.other _ fun h' => e (wreg_inj i hi12 m hm h'.symm), h₃.regs m hm]
    · rw [get m hm, u₄.mem, ite_neg' (by omega_arith)]
      exact h₃.slots m hm h12
  · rename_i hi12
    have hin : InRegions (s₃.rd ++ s₃.wr) (bufAt p (slotOff i)) 4 :=
      in_sc (h₃.wr ▸ hw) (by simp only [slotOff]; omega_arith)
    have hr : readSrc32 s₃ (.mem (at_ .rsi (slotOff i))) = some (v[i]'(by omega_arith)) := by
      simp only [readSrc32, ea_at, h₃.rsi, State.load32, hin, ite_true]
      rw [h₃.slots i hi (by omega_arith)]
    refine wp_cons (xor32_upd (d := .rax) hr) fun s₄ u₄ => ?_
    have h₄ := h₃.upd_rax u₄
    have hout : InRegions s₄.wr (s₄.ea (at_ .rsi (slotOff i))) 4 := by
      rw [ea_at, h₄.rsi]; exact out_sc (h₄.wr ▸ hw) (by simp only [slotOff]; omega_arith)
    refine WP.block_cons_iff.mpr ⟨_, store32_exec hout, WP.block_nil ?_⟩
    have hval : (s₄.gpr .rax).setWidth 32 = (stepN v i j k n)[i] := by
      rw [get i hi, ite_pos' rfl, u₄.gpr, hrax]
      simp [BitVec.xor_comm]
    rw [ea_at, h₄.rsi, hval]
    refine ⟨fun m hm => ?_, fun m hm h12 => ?_, ?_, h₄.rd, h₄.wr, h₄.rsi, h₄.rdi, h₄.rsp⟩
    · rw [get m (by omega_arith), ite_neg' (by omega_arith)]
      exact h₄.regs m hm
    · by_cases e : i = m
      · subst e; exact Mem.readW_writeW_self32 _ _ _
      · rw [readW_writeW_off _ _ _ (by omega_arith) (by simp only [slotOff]; omega_arith)
          (by simp only [slotOff]; omega_arith) (by simp only [slotOff]; omega_arith), get m hm, ite_neg' e]
        exact h₄.slots m hm h12
    · exact h₄.frame.writeW (List.mem_singleton_self _) _
        (contains_off (by simp only [slotOff]; omega_arith) (by simp only [slotOff]; omega_arith))

/-! ## Double rounds -/

theorem lines_ok {p : Addr} {s₀ : State} (hw : scR p ∈ s₀.wr) :
    ∀ (l : List (Nat × Nat × Nat × Nat)), (l.all fun (i, j, k, n) => LSide i j k n) = true →
      ∀ (v : Vector Word 16) (s : State), RI p v s₀ s →
      WP isa (.block (l.flatMap fun (i, j, k, n) => line i j k n)) s
        (RI p (l.foldl (fun x (i, j, k, n) => stepN x i j k n) v) s₀)
  | [], _, _, _, h => WP.block_nil h
  | (i, j, k, n) :: l, hl, v, s, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hl
    rw [List.flatMap_cons, WP.block_append_iff, List.foldl_cons]
    exact WP.mono (line_ok hl.1 h hw) fun s' h' => lines_ok hw l hl.2 _ s' h'

private def sequentialLines : List (Nat × Nat × Nat × Nat) := [
  (4, 0, 12, 7), (8, 4, 0, 9), (12, 8, 4, 13), (0, 12, 8, 18),
  (9, 5, 1, 7), (13, 9, 5, 9), (1, 13, 9, 13), (5, 1, 13, 18),
  (14, 10, 6, 7), (2, 14, 10, 9), (6, 2, 14, 13), (10, 6, 2, 18),
  (3, 15, 11, 7), (7, 3, 15, 9), (11, 7, 3, 13), (15, 11, 7, 18),
  (1, 0, 3, 7), (2, 1, 0, 9), (3, 2, 1, 13), (0, 3, 2, 18),
  (6, 5, 4, 7), (7, 6, 5, 9), (4, 7, 6, 13), (5, 4, 7, 18),
  (11, 10, 9, 7), (8, 11, 10, 9), (9, 8, 11, 13), (10, 9, 8, 18),
  (12, 15, 14, 7), (13, 12, 15, 9), (14, 13, 12, 13), (15, 14, 13, 18)]

private theorem doubleRound_sequential (v : Vector Word 16) : Spec.Scrypt.doubleRound v =
    sequentialLines.foldl (fun x (i, j, k, n) => stepN x i j k n) v := rfl

/-! The code's lines are the specification's, reordered: each line moves
before lines that neither write a word it reads or writes nor read the word it
writes (`pull`), checked by `decide` on the indices. -/

/-- A line as a function of a tuple. -/
private def stepL (x : Vector Word 16) (a : Nat × Nat × Nat × Nat) : Vector Word 16 :=
  stepN x a.1 a.2.1 a.2.2.1 a.2.2.2

/-- Lines `a` and `b` commute: neither writes a word the other reads or writes. -/
private def indep (a b : Nat × Nat × Nat × Nat) : Bool :=
  a.1 % 16 != b.1 % 16 && a.1 % 16 != b.2.1 % 16 && a.1 % 16 != b.2.2.1 % 16 &&
    b.1 % 16 != a.2.1 % 16 && b.1 % 16 != a.2.2.1 % 16

private theorem stepL_comm {a b : Nat × Nat × Nat × Nat} (h : indep a b = true)
    (x : Vector Word 16) : stepL (stepL x a) b = stepL (stepL x b) a := by
  obtain ⟨i, j, k, n⟩ := a
  obtain ⟨i', j', k', n'⟩ := b
  simp only [indep, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨e₁, e₂⟩, e₃⟩, e₄⟩, e₅⟩ := h
  apply Vector.ext
  intro m hm
  simp only [stepL, stepN, Spec.Scrypt.step, fin, Fin.getElem_fin, Vector.getElem_set, e₁, e₂, e₃, e₄, e₅,
    Ne.symm e₁, ite_false]
  by_cases a : i % 16 = m <;> by_cases b : i' % 16 = m <;> simp only [a, b, ite_true, ite_false]
  exact absurd (a.trans b.symm) e₁

/-- `l` with `b` removed, if every line before `b` commutes with it. -/
private def pull (b : Nat × Nat × Nat × Nat) : List (Nat × Nat × Nat × Nat) →
    Option (List (Nat × Nat × Nat × Nat))
  | [] => none
  | a :: l => if a = b then some l else if indep a b then (pull b l).map (a :: ·) else none

/-- `r` is `l` reordered by moving lines over lines they commute with. -/
private def reorder : List (Nat × Nat × Nat × Nat) → List (Nat × Nat × Nat × Nat) → Bool
  | l, [] => l.isEmpty
  | l, b :: r => match pull b l with
    | some l' => reorder l' r
    | none => false

private theorem pull_foldl {b : Nat × Nat × Nat × Nat} :
    ∀ {l l' : List (Nat × Nat × Nat × Nat)}, pull b l = some l' → ∀ x : Vector Word 16,
      l.foldl stepL x = l'.foldl stepL (stepL x b)
  | [], _, h, _ => nomatch h
  | a :: l, l', h, x => by
    simp only [pull] at h
    by_cases e : a = b
    · rw [ite_eq_left e] at h
      cases h; subst e; rfl
    · rw [ite_eq_right e] at h
      by_cases hi : indep a b = true
      · rw [ite_eq_left hi] at h
        cases hp : pull b l with
        | none => rw [hp] at h; nomatch h
        | some l₀ =>
          rw [hp] at h
          cases h
          rw [List.foldl_cons, pull_foldl hp, stepL_comm hi, List.foldl_cons]
      · rw [ite_eq_right hi] at h; nomatch h

private theorem reorder_foldl :
    ∀ {l r : List (Nat × Nat × Nat × Nat)}, reorder l r = true → ∀ x : Vector Word 16,
      l.foldl stepL x = r.foldl stepL x
  | l, [], h, x => by
    simp only [reorder, List.isEmpty_iff] at h; subst h; rfl
  | l, b :: r, h, x => by
    simp only [reorder] at h
    split at h
    · next l' hp => rw [pull_foldl hp, reorder_foldl h, List.foldl_cons]
    · nomatch h

theorem doubleRound_eq (v : Vector Word 16) : Spec.Scrypt.doubleRound v =
    lines.foldl (fun x (i, j, k, n) => stepN x i j k n) v := by
  rw [doubleRound_sequential]
  exact reorder_foldl (l := sequentialLines) (r := lines) (by decide +kernel) v

theorem doubleRound_ok {p : Addr} {v : Vector Word 16} {s₀ s : State} (h : RI p v s₀ s)
    (hw : scR p ∈ s₀.wr) : WP isa doubleRound s (RI p (Spec.Scrypt.doubleRound v) s₀) := by
  rw [doubleRound_eq]
  exact lines_ok hw lines (by decide) v s h

theorem rounds_ok {p : Addr} {v : Vector Word 16} {s₀ : State} (h : RI p v s₀ s₀)
    (hw : scR p ∈ s₀.wr) :
    ∀ n, WP isa (rounds n) s₀ (RI p (Nat.repeat Spec.Scrypt.doubleRound n v) s₀)
  | 0 => WP.block_nil h
  | n + 1 => WP.seq (WP.mono (rounds_ok h hw n) fun _ h' => doubleRound_ok h' hw)

end VG.Proof.Scrypt.X86_64

/-!
# The Salsa20/8 Core on x86-64: loading, finishing, saving and restoring
-/

namespace VG.Proof.Scrypt.X86_64

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Spec.Scrypt (Word)
open VG.Proof.Scrypt

/-! ## The precondition -/

section
variable (s₀ : State)
/-- `b`. -/
abbrev bp : Addr := s₀.gpr .rdi
/-- `scratch`. -/
abbrev sp : Addr := s₀.gpr .rsi
/-- The input words. -/
def V : Vector Word 16 := Vector.ofFn fun j => s₀.mem.readW (bufAt (bp s₀) (4 * j.1)) 32
end

abbrev bR (p : Addr) : Region := ⟨p, 64⟩

theorem V_get (s₀ : State) {k : Nat} (hk : k < 16) :
    (V s₀)[k] = s₀.mem.readW (bufAt (bp s₀) (4 * k)) 32 := by
  simp only [V, Vector.getElem_ofFn]

theorem out_b {ws : List Region} {p : Addr} (hw : bR p ∈ ws) {d n : Nat} (h : d + n ≤ 64) :
    InRegions ws (bufAt p d) n :=
  ⟨bR p, hw, contains_off h (by omega_arith)⟩

theorem mem_read {s : State} {r : Reg} {d : Nat}
    (hin : InRegions (s.rd ++ s.wr) (bufAt (s.gpr r) d) 4) :
    readSrc32 s (.mem (at_ r d)) = some (s.mem.readW (bufAt (s.gpr r) d) 32) := by
  simp only [readSrc32, ea_at, State.load32, hin, ite_true]

/-! ## Loading the words -/

/-- The load invariant after `n` words, relative to the state `s₁` after the
prologue's stores. -/
structure LI (s₀ s₁ : State) (n : Nat) (s : State) : Prop where
  regs : ∀ k (hk : k < 12), k < n → s.gpr (wreg k) = ((V s₀)[k]'(by omega_arith)).setWidth 64
  slots : ∀ k (hk : k < 16), 12 ≤ k → k < n → s.mem.readW (bufAt (sp s₀) (slotOff k)) 32 = (V s₀)[k]
  frame : Frame [slotR (sp s₀)] s₁.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsi : s.gpr .rsi = sp s₀
  rdi : s.gpr .rdi = bp s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp

theorem sub_slot_sc (p : Addr) : ∀ r ∈ [slotR p], ∃ r' ∈ [scR p], Region.Sub r r' := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨scR p, List.mem_singleton_self _, Region.sub_prefix (by omega_arith)⟩

end VG.Proof.Scrypt.X86_64
