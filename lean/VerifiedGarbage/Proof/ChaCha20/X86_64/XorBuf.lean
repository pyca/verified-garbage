module

public import VerifiedGarbage.Impl.ChaCha20.X86_64.XorBuf
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.X86_64.Avx

/-!
# XORing keystream from a buffer into the data, eight bytes at a time

`XorBuf.xorBufTo d s b` writes the `n` bytes at `S` (in `s`) XORed with the
`n` bytes at `B` (in `b`) to the `n` bytes at `D` (in `d`), `n` being in
`rdx`: byte `k` of the destination becomes byte `k` of the source XORed with
byte `k` of the buffer, and nothing else in memory changes. The destination
is the source or apart from it (`Sep`): either way the source bytes not yet
done are intact (`Inv.src`). Only `rax`, `r8`, `rcx` and the flags are
written among the registers. `xorBuf_ok` is the case `S = D` (`xorBuf`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.XorBuf

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.XorBuf

/-! ## The destination of the vector implementations -/

/-- `[rsi + ix + d]`. -/
theorem ea_atDst (s : State) (ix : Reg) (d : Nat) :
    s.ea (atDst (some ix) d) = s.gpr .rsi + s.gpr ix + BitVec.ofNat 64 d := by
  simp only [State.ea, atDst, BitVec.mul_one]
  congr 1

/-- `[rsi + ix + d]`, `ix` holding the destination's distance from the
source `S`, and `rsi` at `S + p`: the destination's byte `p + d`. -/
theorem ea_atDst_eq (s : State) {ix : Reg} {S D : Addr} {p : Nat} (hs : s.gpr .rsi = S + BitVec.ofNat 64 p)
    (hx : s.gpr ix = D - S) (d : Nat) :
    s.ea (atDst (some ix) d) = D + BitVec.ofNat 64 (p + d) := by
  rw [ea_atDst, hs, hx, BitVec.ofNat_add, ← BitVec.add_assoc D]
  congr 1
  rw [BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 p), ← BitVec.add_assoc, BitVec.add_comm S, BitVec.sub_add_cancel]

/-- The destination's distance from the source, added to the source's byte
`x`: the destination's. -/
theorem sub_add_add (D S x : Addr) : D - S + (S + x) = D + x := by
  rw [← BitVec.add_assoc, BitVec.sub_add_cancel]

/-- `[rsi + d]` in place. -/
theorem ea_atDst_none (s : State) (d : Nat) :
    s.ea (atDst none d) = s.gpr .rsi + BitVec.ofNat 64 d := by
  simp only [State.ea, atDst]
  congr 1

/-- `atDst (if to then some .r11 else none)` addresses the destination `b`
of the source `a`: `r11` holds their distance (`to`), or they are the same
(in place). -/
def DstAt (to : Bool) (g : Reg → BitVec 64) (a b : Addr) : Prop :=
  (to = true → g .r11 = b - a) ∧ (to = false → b = a)

theorem DstAt.ea {to : Bool} {s : State} {a b : Addr} (hs : s.gpr .rsi = a) (h : DstAt to s.gpr a b) (d : Nat) :
    s.ea (atDst (if to then some .r11 else none) d) = b + BitVec.ofNat 64 d := by
  cases to
  · rw [h.2 rfl]; simp only [Bool.false_eq_true, ite_false, ea_atDst_none, hs]
  · simp only [ite_true, ea_atDst, hs, h.1 rfl]
    rw [BitVec.add_comm a, BitVec.sub_add_cancel]

theorem DstAt.congr {to : Bool} {g g' : Reg → BitVec 64} {a b : Addr} (h : DstAt to g a b) (e : g' = g) :
    DstAt to g' a b := e ▸ h

/-- Both moved on by the same offset. -/
theorem DstAt.add {to : Bool} {g : Reg → BitVec 64} {a b : Addr} (h : DstAt to g a b) (x : Addr) :
    DstAt to g (a + x) (b + x) :=
  ⟨fun e => by rw [h.1 e, BitVec.eq_sub_iff_add_eq, ← BitVec.add_assoc, BitVec.sub_add_cancel],
    fun e => by rw [h.2 e]⟩

/-! ## Bytes of quadwords -/

/-- Byte `t` of a quadword read. -/
theorem readW64_byte (m : Mem) (a : Addr) {t : Nat} (ht : t < 8) :
    (m.readW a 64).extractLsb' (8 * t) 8 = m (a + BitVec.ofNat 64 t) := by
  change ((m.read a 8).setWidth 64).extractLsb' (8 * t) 8 = _
  rw [BitVec.setWidth_eq, Mem.extractLsb'_read _ _ ht]

/-- A byte store. -/
theorem writeW8_apply (m : Mem) (a x : Addr) (v : Byte) :
    (m.writeW a v) x = if x = a then v else m x := by
  simp only [Mem.writeW, Mem.write]
  by_cases h : x = a
  · subst h; simp
  · have : ¬ (x - a).toNat < 8 / 8 := by
      intro h'
      apply h
      have h0 : (x - a).toNat = 0 := by omega_arith
      have := BitVec.eq_of_toNat_eq (x := x - a) (y := 0) (by rw [h0]; rfl)
      rw [← BitVec.sub_add_cancel x a, this]; exact BitVec.zero_add a
    simp only [this, h, ↓reduceIte]

theorem xor_setWidth (a b : Byte) : (a.setWidth 64 ^^^ b.setWidth 64).setWidth 8 = a ^^^ b := by
  ext i hi; simp

/-! ## Regions -/

/-- A sub-range of a permitted range is permitted. -/
theorem inRegions_offset {rs : List Region} {a : Addr} {n : Nat} (h : InRegions rs a n)
    {i m : Nat} (him : i + m ≤ n) : InRegions rs (a + BitVec.ofNat 64 i) m := by
  obtain ⟨r, hr, hc⟩ := h
  refine ⟨r, hr, ?_⟩
  simp only [Region.Contains] at *
  have e : a + BitVec.ofNat 64 i - r.base = (a - r.base) + BitVec.ofNat 64 i := by
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm
      (BitVec.ofNat 64 i), ← BitVec.add_assoc]
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := (a - r.base).isLt
  rcases Nat.lt_or_ge ((a - r.base).toNat + i % 2 ^ 64) (2 ^ 64) with h' | h'
  · rw [Nat.mod_eq_of_lt h']
    have : i % 2 ^ 64 ≤ i := Nat.mod_le _ _
    omega_arith
  · have : ((a - r.base).toNat + i % 2 ^ 64) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
    have : i % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
    rw [Nat.mod_eq_sub_mod h', Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith

/-- Byte `k` of a range at `p` is in it. -/
theorem contains_byte (p : Addr) {k n : Nat} (hk : k < n) (hn : n ≤ 2 ^ 64) :
    (⟨p, n⟩ : Region).Contains (p + BitVec.ofNat 64 k) 1 := by
  simp only [Region.Contains]
  rw [Mem.sub_ofNat_toNat p (by omega_arith)]; omega_arith

/-- A byte of the buffer is not in the data. -/
theorem buf_not_data {D B : Addr} {n : Nat} (hd : (⟨D, n⟩ : Region).Disjoint ⟨B, n⟩)
    (hn : n ≤ 2 ^ 64) {k : Nat} (hk : k < n) : ¬ (⟨D, n⟩ : Region).Contains (B + BitVec.ofNat 64 k) 1 :=
  fun h => hd _ h (contains_byte B hk hn)

/-! ## The invariant -/

section
variable (D S B : Addr) (n : Nat) (s₀ : State)

/-- `i` bytes done, of `n` from `S` and `B` to `D`. -/
structure Inv (i : Nat) (s : State) : Prop where
  data : ∀ k < n, s.mem (D + BitVec.ofNat 64 k) =
    if k < i then s₀.mem (S + BitVec.ofNat 64 k) ^^^ s₀.mem (B + BitVec.ofNat 64 k)
    else s₀.mem (D + BitVec.ofNat 64 k)
  frame : Frame [⟨D, n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The destination apart from the buffer, and the source itself or apart
from it. -/
structure Sep : Prop where
  db : (⟨D, n⟩ : Region).Disjoint ⟨B, n⟩
  alias : D = S ∨ (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩
  hn : n < 2 ^ 64

end

theorem Sep.self {D B : Addr} {n : Nat} (hd : (⟨D, n⟩ : Region).Disjoint ⟨B, n⟩) (hn : n < 2 ^ 64) :
    Sep D D B n := ⟨hd, .inl rfl, hn⟩

theorem Inv.zero (D S B : Addr) (n : Nat) (s₀ : State) : Inv D S B n s₀ 0 s₀ :=
  ⟨fun k hk => by simp, Frame.refl _ _, rfl, rfl⟩

/-- The buffer is unchanged. -/
theorem Inv.buf {D S B : Addr} {n : Nat} {s₀ s : State} {i : Nat} (h : Inv D S B n s₀ i s)
    (hs : Sep D S B n) {k : Nat} (hk : k < n) :
    s.mem (B + BitVec.ofNat 64 k) = s₀.mem (B + BitVec.ofNat 64 k) := by
  refine h.frame (B + BitVec.ofNat 64 k) ?_
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact buf_not_data hs.db (by have := hs.hn; omega_arith) hk

/-- The source bytes not yet done are intact. -/
theorem Inv.src {D S B : Addr} {n : Nat} {s₀ s : State} {i : Nat} (h : Inv D S B n s₀ i s)
    (hs : Sep D S B n) {k : Nat} (hik : i ≤ k) (hk : k < n) :
    s.mem (S + BitVec.ofNat 64 k) = s₀.mem (S + BitVec.ofNat 64 k) := by
  rcases hs.alias with rfl | hdis
  · rw [h.data k hk, ite_eq_right (by omega_arith)]
  · refine h.frame (S + BitVec.ofNat 64 k) ?_
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact fun hc => hdis _ (contains_byte S hk (by have := hs.hn; omega_arith)) hc

/-- Memory after the `N` bytes at offset `i`. -/
abbrev wMem (N : Nat) (m : Mem) (D S B : Addr) (i : Nat) : Mem :=
  m.writeW (D + BitVec.ofNat 64 i) (m.readW (S + BitVec.ofNat 64 i) (8 * N) ^^^ m.readW (B + BitVec.ofNat 64 i) (8 * N))

/-- After the `N` bytes at offset `i` (each loaded from the source before the
destination's are stored). -/
theorem Inv.wstep {N : Nat} (hN : N ≤ 64) {D S B : Addr} {n : Nat} {s₀ s : State} {i : Nat}
    (h : Inv D S B n s₀ i s) (hs : Sep D S B n) (hi : i + N ≤ n)
    {s' : State} (hm : s'.mem = wMem N s.mem D S B i) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Inv D S B n s₀ (i + N) s' := by
  have hn := hs.hn
  refine ⟨fun k hk => ?_, ?_, hrd.trans h.rd, hwr.trans h.wr⟩
  · simp only [hm, wMem]
    by_cases hin : i ≤ k ∧ k < i + N
    · have e : ∀ {P : Addr}, P + BitVec.ofNat 64 k = P + BitVec.ofNat 64 i + BitVec.ofNat 64 (k - i) := by
        intro P; rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' hin.1]
      rw [e, writeW_byte _ _ _ (by omega_arith) (by omega_arith), BitVec.extractLsb'_xor, byte_readW _ _ (by omega_arith),
        byte_readW _ _ (by omega_arith), ← e (P := S), ← e (P := B), h.buf hs hk, h.src hs hin.1 hk,
        ite_eq_left (by omega_arith)]
    · rw [writeW_byte_off _ _ _ _ ?_, h.data k hk]
      · by_cases hik : k < i
        · rw [ite_eq_left hik, ite_eq_left (by omega_arith)]
        · rw [ite_eq_right hik, ite_eq_right (by omega_arith)]
      · rw [Offset.sub_toNat' D (by omega_arith) (by omega_arith)]
        split <;> omega_arith
  · rw [hm]
    refine h.frame.writeW (List.mem_singleton_self _) _ ?_
    simp only [Region.Contains]
    rw [Mem.sub_ofNat_toNat D (by omega_arith)]; omega_arith

/-- Memory after the quadword at offset `i`. -/
abbrev qMem (m : Mem) (D S B : Addr) (i : Nat) : Mem :=
  m.writeW (D + BitVec.ofNat 64 i) (m.readW (S + BitVec.ofNat 64 i) 64 ^^^ m.readW (B + BitVec.ofNat 64 i) 64)

/-- Memory after the byte at offset `i`. -/
abbrev bMem (m : Mem) (D S B : Addr) (i : Nat) : Mem :=
  m.writeW (D + BitVec.ofNat 64 i) (m (S + BitVec.ofNat 64 i) ^^^ m (B + BitVec.ofNat 64 i))

/-- After the byte at offset `i`. -/
theorem Inv.bstep {D S B : Addr} {n : Nat} {s₀ s : State} {i : Nat} (h : Inv D S B n s₀ i s)
    (hs : Sep D S B n) (hi : i < n) {s' : State}
    (hm : s'.mem = bMem s.mem D S B i) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Inv D S B n s₀ (i + 1) s' := by
  have hn := hs.hn
  refine ⟨fun k hk => ?_, ?_, hrd.trans h.rd, hwr.trans h.wr⟩
  · simp only [hm, bMem]
    rw [writeW8_apply]
    by_cases he : k = i
    · subst he
      rw [ite_eq_left rfl, h.buf hs hk, h.src hs (Nat.le_refl _) hk, ite_eq_left (by omega_arith)]
    · rw [ite_eq_right (Offset.add_ofNat_ne D (by omega_arith) (by omega_arith) he), h.data k hk]
      by_cases h₁ : k < i
      · rw [ite_eq_left h₁, ite_eq_left (by omega_arith)]
      · rw [ite_eq_right h₁, ite_eq_right (by omega_arith)]
  · rw [hm]
    refine h.frame.writeW (List.mem_singleton_self _) _ ?_
    simp only [Region.Contains]
    rw [Mem.sub_ofNat_toNat D (by omega_arith)]; omega_arith

/-! ## The loops -/

section
variable {d sr b : Reg} (hdx : d ≠ .rax ∧ d ≠ .r8 ∧ d ≠ .rcx) (hsx : sr ≠ .rax ∧ sr ≠ .r8 ∧ sr ≠ .rcx)
  (hbx : b ≠ .rax ∧ b ≠ .r8 ∧ b ≠ .rcx) {D S B : Addr} {n : Nat} {s₀ : State}

/-- The registers while the loops run: `i` bytes done, of the `n` at `S`. -/
structure Regs (d sr b : Reg) (D S B : Addr) (n : Nat) (s₀ : State) (i : Nat) (s : State) : Prop where
  rd : s.gpr d = D
  rs : s.gpr sr = S
  rb : s.gpr b = B
  rdx : s.gpr .rdx = BitVec.ofNat 64 n
  rcx : s.gpr .rcx = BitVec.ofNat 64 i
  keep : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .rcx → s.gpr r = s₀.gpr r

theorem se8 : BitVec.signExtend 64 (8 : BitVec 32) = 8 := by decide
theorem se1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide

include hdx hsx hbx in
theorem q_step (hs : Sep D S B n)
    (hw : InRegions s₀.wr D n) (hrs : InRegions (s₀.rd ++ s₀.wr) S n) (hr : InRegions (s₀.rd ++ s₀.wr) B n)
    {j : Nat} (hj : j < n / 8)
    {s : State} (hI : Inv D S B n s₀ (8 * j) s) (hR : Regs d sr b D S B n s₀ (8 * j) s)
    (hax : s.gpr .rax = BitVec.ofNat 64 (n / 8 - j)) :
    WP isa (.block (qBody d sr b)) s fun s' =>
      Inv D S B n s₀ (8 * (j + 1)) s' ∧ Regs d sr b D S B n s₀ (8 * (j + 1)) s' ∧
        s'.gpr .rax = BitVec.ofNat 64 (n / 8 - (j + 1)) ∧
        s'.zf = some (decide (n / 8 - (j + 1) = 0)) ∧
        s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi ∧ s'.zmmHi = s.zmmHi := by
  have hn := hs.hn
  have hi : 8 * j + 8 ≤ n := by omega_arith
  have ea₁ : D + BitVec.ofNat 64 (8 * j) * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 =
      D + BitVec.ofNat 64 (8 * j) := by simp
  have ea₂ : B + BitVec.ofNat 64 (8 * j) * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 =
      B + BitVec.ofNat 64 (8 * j) := by simp
  have ea₃ : S + BitVec.ofNat 64 (8 * j) * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 =
      S + BitVec.ofNat 64 (8 * j) := by simp
  have o₁ : InRegions s.wr (D + BitVec.ofNat 64 (8 * j)) 8 := by rw [hI.wr]; exact inRegions_offset hw hi
  have i₃ : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 (8 * j)) 8 := by
    rw [hI.rd, hI.wr]; exact inRegions_offset hrs hi
  have i₂ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (8 * j)) 8 := by
    rw [hI.rd, hI.wr]; exact inRegions_offset hr hi
  have e8 : 8 * (j + 1) = 8 * j + 8 := by omega_arith
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, qBody, idx, runBlock_cons, runStep_some, runBlock_nil, reduceExec,
    State.ea, readSrc, execAlu, arithFlags, State.load64, State.store64, State.setReg,
    State.setFlags, hR.rd, hR.rs, hR.rb, hR.rcx, hbx.2.1, hdx.2.1, ea₁, ea₂, ea₃,
    i₂, i₃, o₁, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', se8, se1]
  refine ⟨by rw [e8]; exact hI.wstep (N := 8) (by decide) hs hi rfl rfl rfl,
    ⟨by simp [hdx.1, hdx.2.1, hdx.2.2, hR.rd], by simp [hsx.1, hsx.2.1, hsx.2.2, hR.rs],
    by simp [hbx.1, hbx.2.1, hbx.2.2, hR.rb],
    by simp [hR.rdx], by simp [e8, BitVec.ofNat_add],
    fun r h₁ h₂ h₃ => by simp [h₁, h₂, h₃, hR.keep r h₁ h₂ h₃]⟩, ?_, ?_, by simp⟩
  · simp only [hax]
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega_arith), Nat.sub_sub]
  · rw [hax, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat_beq (by omega_arith) (by omega_arith)]
    simp only [decide_eq_decide]; omega_arith

include hdx hsx hbx in
theorem b_step (hs : Sep D S B n)
    (hw : InRegions s₀.wr D n) (hrs : InRegions (s₀.rd ++ s₀.wr) S n) (hr : InRegions (s₀.rd ++ s₀.wr) B n)
    {i : Nat} (hi : i < n)
    {s : State} (hI : Inv D S B n s₀ i s) (hR : Regs d sr b D S B n s₀ i s) :
    WP isa (.block (bBody d sr b)) s fun s' =>
      Inv D S B n s₀ (i + 1) s' ∧ Regs d sr b D S B n s₀ (i + 1) s' ∧
        s'.zf = some (decide (i + 1 = n)) ∧
        s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi ∧ s'.zmmHi = s.zmmHi := by
  have hn := hs.hn
  have ea₁ : D + BitVec.ofNat 64 i * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = D + BitVec.ofNat 64 i := by
    simp
  have ea₂ : B + BitVec.ofNat 64 i * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = B + BitVec.ofNat 64 i := by
    simp
  have ea₃ : S + BitVec.ofNat 64 i * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = S + BitVec.ofNat 64 i := by
    simp
  have o₁ : InRegions s.wr (D + BitVec.ofNat 64 i) 1 := by rw [hI.wr]; exact inRegions_offset hw hi
  have i₃ : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 i) 1 := by
    rw [hI.rd, hI.wr]; exact inRegions_offset hrs hi
  have i₂ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 i) 1 := by
    rw [hI.rd, hI.wr]; exact inRegions_offset hr hi
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, bBody, idx, runBlock_cons, runStep_some, runBlock_nil, reduceExec,
    State.ea, readSrc, execAlu, arithFlags, State.load8, State.store8, State.setReg,
    State.setFlags, hR.rd, hR.rs, hR.rb, hR.rcx, hbx.1, hdx.1, hdx.2.1, ea₁, ea₂, ea₃,
    i₂, i₃, o₁, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', se1]
  rw [xor_setWidth]
  refine ⟨hI.bstep hs hi rfl rfl rfl, ⟨by simp [hdx.1, hdx.2.1, hdx.2.2, hR.rd],
    by simp [hsx.1, hsx.2.1, hsx.2.2, hR.rs], by simp [hbx.1, hbx.2.1, hbx.2.2, hR.rb],
    by simp [hR.rdx], by simp [BitVec.ofNat_add],
    fun r h₁ h₂ h₃ => by simp [h₁, h₂, h₃, hR.keep r h₁ h₂ h₃]⟩, ?_, by simp⟩
  rw [hR.rdx, ← Offset.ofNat_sub_ofNat_beq (x := i + 1) (y := n) (by omega_arith) (by omega_arith),
    BitVec.ofNat_add]
  rfl

end

/-! ## The whole -/

/-- What `xorBufTo` does: byte `k < n` of the destination the XOR of byte
`k` of the source and of the buffer, the rest of memory and the registers
but `rax`, `r8` and `rcx` unchanged. -/
structure PostTo (D S B : Addr) (n : Nat) (s₀ s : State) : Prop where
  data : ∀ k < n, s.mem (D + BitVec.ofNat 64 k) =
    s₀.mem (S + BitVec.ofNat 64 k) ^^^ s₀.mem (B + BitVec.ofNat 64 k)
  frame : Frame [⟨D, n⟩] s₀.mem s.mem
  keep : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .rcx → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  xmm : s.xmm = s₀.xmm
  ymmHi : s.ymmHi = s₀.ymmHi
  zmmHi : s.zmmHi = s₀.zmmHi

/-- What `xorBuf` does: `PostTo` in place. -/
abbrev Post (_d _b : Reg) (D B : Addr) (n : Nat) (s₀ s : State) : Prop := PostTo D D B n s₀ s

theorem xorBufTo_ok {d sr b : Reg} (hdx : d ≠ .rax ∧ d ≠ .r8 ∧ d ≠ .rcx) (hsx : sr ≠ .rax ∧ sr ≠ .r8 ∧ sr ≠ .rcx)
    (hbx : b ≠ .rax ∧ b ≠ .r8 ∧ b ≠ .rcx) {D S B : Addr} {n : Nat} {s₀ : State}
    (hD : s₀.gpr d = D) (hS : s₀.gpr sr = S) (hB : s₀.gpr b = B) (hrdx : s₀.gpr .rdx = BitVec.ofNat 64 n)
    (hs : Sep D S B n) (hw : InRegions s₀.wr D n) (hrs : InRegions (s₀.rd ++ s₀.wr) S n)
    (hr : InRegions (s₀.rd ++ s₀.wr) B n) :
    WP isa (xorBufTo d sr b) s₀ (PostTo D S B n s₀) := by
  have hn := hs.hn
  -- The registers and vector state at each point.
  let V : State → Prop := fun s => s.xmm = s₀.xmm ∧ s.ymmHi = s₀.ymmHi ∧ s.zmmHi = s₀.zmmHi
  have hI0 := Inv.zero D S B n s₀
  -- The prologue.
  have h₁ : WP isa (.block [.mov32 .rcx (.imm 0), .mov .rax (.reg .rdx), .shift .shr .rax 3]) s₀
      fun s => Inv D S B n s₀ 0 s ∧ Regs d sr b D S B n s₀ 0 s ∧ s.gpr .rax = BitVec.ofNat 64 (n / 8) ∧
        s.zf = some (decide (n / 8 = 0)) ∧ V s := by
    apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, and_self, runBlock_cons, runStep_some,
      runBlock_nil, reduceExec, readSrc, readSrc32, execShift, State.setReg, State.setReg32, State.setFlags,
      Option.map_some, Option.some.injEq, exists_eq_left', hrdx]
    have hs : BitVec.ofNat 64 n >>> 3 = BitVec.ofNat 64 (n / 8) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
        Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega_arith)]
    refine ⟨⟨hI0.data, hI0.frame, rfl, rfl⟩, ⟨by simp [hdx.1, hdx.2.2, hD], by simp [hsx.1, hsx.2.2, hS],
      by simp [hbx.1, hbx.2.2, hB], by simp [hrdx],
      by simp, fun r h₁ _ h₃ => by simp [h₁, h₃]⟩,
      by simp [hs], ?_, rfl, rfl, rfl⟩
    have hz : (BitVec.ofNat 64 (n / 8) == 0) = decide (n / 8 = 0) := by
      rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
      constructor
      · intro h
        have := congrArg BitVec.toNat h
        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this
      · intro h; rw [h]; rfl
    rw [hs, hz]
  -- After the quadwords.
  let Q : State → Prop := fun s => Inv D S B n s₀ (8 * (n / 8)) s ∧ Regs d sr b D S B n s₀ (8 * (n / 8)) s ∧ V s
  have h₂ : ∀ s, (Inv D S B n s₀ 0 s ∧ Regs d sr b D S B n s₀ 0 s ∧ s.gpr .rax = BitVec.ofNat 64 (n / 8) ∧
      s.zf = some (decide (n / 8 = 0)) ∧ V s) →
      WP isa (.ite .e (.block []) (.loop (.block (qBody d sr b)) .ne)) s Q := by
    rintro s ⟨hI, hR, hax, hz, hV⟩
    refine WP.ite (decide (n / 8 = 0)) (by simp [eval, hz]) (fun h => ?_) (fun h => ?_)
    · simp only [decide_eq_true_eq] at h
      exact WP.block_nil (M := isa) ⟨cast (congrArg (fun i => Inv D S B n s₀ (8 * i) s) h.symm) hI,
        cast (congrArg (fun i => Regs d sr b D S B n s₀ (8 * i) s) h.symm) hR, hV⟩
    · simp only [decide_eq_false_iff_not] at h
      let Inv' : Nat → State → Prop := fun c s => ∃ j, c = n / 8 - j ∧ j < n / 8 ∧
        Inv D S B n s₀ (8 * j) s ∧ Regs d sr b D S B n s₀ (8 * j) s ∧ s.gpr .rax = BitVec.ofNat 64 (n / 8 - j) ∧ V s
      have hstep : ∀ c s, Inv' c s → WP isa (.block (qBody d sr b)) s (fun s' =>
          (eval .ne s' = some false ∧ Q s') ∨ (eval .ne s' = some true ∧ ∃ c' < c, Inv' c' s')) := by
        rintro c s ⟨j, rfl, hj, hI, hR, hax, hV⟩
        refine WP.mono (q_step hdx hsx hbx hs hw hrs hr hj hI hR hax)
          fun s' ⟨hI', hR', hax', hz', x₁, x₂, x₃⟩ => ?_
        have hV' : V s' := ⟨x₁.trans hV.1, x₂.trans hV.2.1, x₃.trans hV.2.2⟩
        by_cases hl : n / 8 - (j + 1) = 0
        · have e : j + 1 = n / 8 := by omega_arith
          exact .inl ⟨by simp [eval, hz', hl], cast (congrArg (fun i => Inv D S B n s₀ (8 * i) s') e) hI',
            cast (congrArg (fun i => Regs d sr b D S B n s₀ (8 * i) s') e) hR', hV'⟩
        · exact .inr ⟨by simp [eval, hz', hl], n / 8 - (j + 1), by omega_arith, j + 1, rfl, by omega_arith,
            hI', hR', hax', hV'⟩
      exact WP.loop (M := isa) Inv' hstep (n / 8 - 0) s ⟨0, rfl, by omega_arith, hI, hR, by simpa using hax, hV⟩
  -- The bytes.
  let F : State → Prop := fun s => Inv D S B n s₀ n s ∧ Regs d sr b D S B n s₀ n s ∧ V s
  have h₃ : ∀ s, Q s → WP isa (.seq (.block [.alu .cmp .rcx (.reg .rdx)])
      (.ite .e (.block []) (.loop (.block (bBody d sr b)) .ne))) s F := by
    rintro s ⟨hI, hR, hV⟩
    have hle : 8 * (n / 8) ≤ n := by omega_arith
    have hc : WP isa (.block [.alu .cmp .rcx (.reg .rdx)]) s fun s' =>
        Inv D S B n s₀ (8 * (n / 8)) s' ∧ Regs d sr b D S B n s₀ (8 * (n / 8)) s' ∧ V s' ∧
          s'.zf = some (decide (8 * (n / 8) = n)) := by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, readSrc, execAlu, arithFlags,
        State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left']
      refine ⟨⟨hI.data, hI.frame, hI.rd, hI.wr⟩, ⟨hR.rd, hR.rs, hR.rb, hR.rdx, hR.rcx, hR.keep⟩, hV, ?_⟩
      rw [hR.rcx, hR.rdx, Offset.ofNat_sub_ofNat_beq (by omega_arith) hn]
    refine WP.seq (WP.mono hc fun s₁ ⟨hI₁, hR₁, hV₁, hz₁⟩ => ?_)
    refine WP.ite (decide (8 * (n / 8) = n)) (by simp [eval, hz₁]) (fun h => ?_) (fun h => ?_)
    · simp only [decide_eq_true_eq] at h
      exact WP.block_nil (M := isa) ⟨cast (congrArg (fun i => Inv D S B n s₀ i s₁) h) hI₁,
        cast (congrArg (fun i => Regs d sr b D S B n s₀ i s₁) h) hR₁, hV₁⟩
    · simp only [decide_eq_false_iff_not] at h
      let Inv' : Nat → State → Prop := fun c s => ∃ i, c = n - i ∧ i < n ∧
        Inv D S B n s₀ i s ∧ Regs d sr b D S B n s₀ i s ∧ V s
      have hstep : ∀ c s, Inv' c s → WP isa (.block (bBody d sr b)) s (fun s' =>
          (eval .ne s' = some false ∧ F s') ∨ (eval .ne s' = some true ∧ ∃ c' < c, Inv' c' s')) := by
        rintro c s ⟨i, rfl, hi, hI, hR, hV⟩
        refine WP.mono (b_step hdx hsx hbx hs hw hrs hr hi hI hR)
          fun s' ⟨hI', hR', hz', x₁, x₂, x₃⟩ => ?_
        have hV' : V s' := ⟨x₁.trans hV.1, x₂.trans hV.2.1, x₃.trans hV.2.2⟩
        by_cases hl : i + 1 = n
        · exact .inl ⟨by simp [eval, hz', hl], cast (congrArg (fun i => Inv D S B n s₀ i s') hl) hI',
            cast (congrArg (fun i => Regs d sr b D S B n s₀ i s') hl) hR', hV'⟩
        · exact .inr ⟨by simp [eval, hz', hl], n - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, hI', hR', hV'⟩
      exact WP.loop (M := isa) Inv' hstep (n - 8 * (n / 8)) s₁ ⟨8 * (n / 8), rfl, by omega_arith, hI₁, hR₁, hV₁⟩
  refine WP.seq (WP.mono h₁ fun s h => WP.seq (WP.mono (h₂ s h) fun s' hq =>
    WP.mono (h₃ s' hq) fun s'' hf => ?_))
  obtain ⟨hI, hR, hV⟩ := hf
  exact ⟨fun k hk => by rw [hI.data k hk, ite_eq_left hk], hI.frame, hR.keep, hI.rd, hI.wr,
    hV.1, hV.2.1, hV.2.2⟩

/-- `xorBufTo_ok` in place. -/
theorem xorBuf_ok {d b : Reg} (hdx : d ≠ .rax ∧ d ≠ .r8 ∧ d ≠ .rcx)
    (hbx : b ≠ .rax ∧ b ≠ .r8 ∧ b ≠ .rcx) {D B : Addr} {n : Nat} {s₀ : State}
    (hD : s₀.gpr d = D) (hB : s₀.gpr b = B) (hrdx : s₀.gpr .rdx = BitVec.ofNat 64 n)
    (hn : n < 2 ^ 64) (hd : (⟨D, n⟩ : Region).Disjoint ⟨B, n⟩)
    (hw : InRegions s₀.wr D n) (hr : InRegions (s₀.rd ++ s₀.wr) B n) :
    WP isa (xorBuf d b) s₀ (Post d b D B n s₀) :=
  xorBufTo_ok hdx hdx hbx hD hD hB hrdx (Sep.self hd hn) hw
    (let ⟨r, hr', hc⟩ := hw; ⟨r, List.mem_append_right _ hr', hc⟩) hr

end VG.Proof.ChaCha20.X86_64.XorBuf
