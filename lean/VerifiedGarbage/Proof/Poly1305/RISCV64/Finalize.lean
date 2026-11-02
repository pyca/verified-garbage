module

public import VerifiedGarbage.Proof.Poly1305.RISCV64.Buffer
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Poly1305.RISCV64.Lit
import VerifiedGarbage.Proof.Poly1305.Stream
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Poly1305.RISCV64.Buffer
meta import VerifiedGarbage.Proof.Poly1305.RISCV64.Lit
meta import VerifiedGarbage.Proof.Poly1305.Stream
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Poly1305.Spec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Keep
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Poly1305.RISCV64.Contract
meta import VerifiedGarbage.Proof.Poly1305.RISCV64.Blocks
import VerifiedGarbage.Proof.Poly1305.RISCV64.Reduce
meta import VerifiedGarbage.Proof.Poly1305.RISCV64.Reduce

/-!
# Poly1305 on RISC-V: `finalize`

As on PPC64LE (`Proof/Poly1305/PPC64LE/Finalize.lean`): a non-empty buffer
is padded in place with `0x01` and zeros and absorbed without `pad`; then the
accumulator is reduced, `s` is added modulo `2¹²⁸`, and the sum stored is the
tag. The proof is for any writable regions holding the state and the tag,
so it serves both `vg_poly1305_finalize` and `vg_poly1305_finalize_scratch`,
whose `scratch` the code does not use.
-/

@[expose] public section

namespace VG.Proof.Poly1305.RISCV64

open VG VG.RISCV64 VG.RISCV64.Wide VG.RISCV64.Steps VG.Impl.Poly1305.RISCV64
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr Buffered leBytes mac)

/-! ## The buffer, a byte at a time -/

/-- Byte `k` of the buffer. -/
abbrev bufB (st : Addr) (k : Nat) : Addr := st + BitVec.ofNat 64 (56 + k)

theorem bufB_eq (st : Addr) (k : Nat) : bufB st k = off st 56 + BitVec.ofNat 64 k := by
  rw [off, Offset.add_add]

theorem bufB_ne {st : Addr} {j k : Nat} (hj : j < 16) (hk : k < 16) (h : j ≠ k) :
    bufB st j ≠ bufB st k :=
  Offset.add_ofNat_ne st (by omega) (by omega) (by omega)

theorem bufB_in {s : State} {st : Addr} (hw : sR st ∈ s.wr) {k : Nat} (hk : k < 16) :
    InRegions s.wr (bufB st k) 1 :=
  in_st hw (by omega)

theorem bfR_bufB (st : Addr) {k : Nat} (hk : k < 16) : (bfR st).Contains (bufB st k) 1 := by
  rw [bufB_eq]; exact Offset.contains_base _ (by omega) (by omega)

/-- The buffer's bytes are `f k`. -/
def BufHas (m : Mem) (st : Addr) (f : Nat → Byte) : Prop := ∀ k < 16, m (bufB st k) = f k

theorem bytesAt_buf {m : Mem} {st : Addr} {f : Nat → Byte} (h : BufHas m st f) :
    bytesAt m (off st 56) 16 = (List.range 16).map f := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro k hk
  rw [← h k (List.mem_range.mp hk), bufB_eq]

/-! ## The precondition -/

section
variable (s₀ : State)
/-- The number of bytes buffered. -/
abbrev kf : Nat := (s₀.gpr .a1).toNat % 16
abbrev op : Addr := s₀.gpr .a2
abbrev oR' : Region := ⟨op s₀, 16⟩
/-- The bytes buffered. -/
abbrev tail : List Byte := bytesAt s₀.mem (off (st s₀) 56) (kf s₀)
end

structure FPre (s₀ : State) : Prop where
  st_in : sR (st s₀) ∈ s₀.wr
  o_in : oR' s₀ ∈ s₀.wr
  st_o : (sR (st s₀)).Disjoint (oR' s₀)
  st_al : (st s₀).toNat % 8 = 0

theorem kf_lt (s₀ : State) : kf s₀ < 16 := Nat.mod_lt _ (by decide)

/-! ## Prologue -/

/-- The state after the prologue. -/
structure F0 (s₀ : State) (s : State) : Prop where
  a0 : s.gpr .a0 = st s₀
  y1 : s.gpr Y1 = BitVec.ofNat 64 (kf s₀)
  a2 : s.gpr .a2 = op s₀
  keys : Keys (Rn s₀) s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = s₀.mem
  acc : A0 s₀ < P → hv s = A0 s₀ ∧ Bounds s

theorem fprologue_ok {s₀ : State} (hp : FPre s₀) :
    WP isa (.block (.logicImm .and Y1 .a1 15 :: setup)) s₀ (F0 s₀) := by
  refine wp_andi (by decide) fun s₁ u₁ => WP.mono (setup_ok s₁ (by
    rw [u₁.other _ (by decide), u₁.rd, u₁.wr]
    exact List.mem_append_right _ hp.st_in) (by rw [u₁.other _ (by decide)]; exact hp.st_al))
    fun s₂ ⟨hk, ha, k⟩ => ?_
  have m₁ : s₁.mem = s₀.mem := u₁.mem
  have a0₁ : s₁.gpr .a0 = s₀.gpr .a0 := u₁.other _ (by decide)
  have hR : Rk s₁.mem (s₁.gpr .a0) = Rn s₀ := by rw [m₁, a0₁]
  have hA : A0 s₁ = A0 s₀ := by simp only [A0, st, m₁, a0₁]
  rw [hR] at hk
  rw [hA] at ha
  exact ⟨by rw [k.gpr' (r := .a0), a0₁], by rw [k.gpr' (r := Y1), u₁.gpr, and15],
    by rw [k.gpr' (r := .a2), u₁.other _ (by decide)], hk, by rw [k.2.2.1, u₁.rd],
    by rw [k.2.2.2.1, u₁.wr], by rw [k.2.1, m₁], ha⟩

/-! ## Padding the buffer in place -/

/-- The padded block: the buffered bytes, `0x01`, zeros. -/
def padded (s₀ : State) (k : Nat) : Byte :=
  if k < kf s₀ then (tail s₀).getD k 0 else if k = kf s₀ then 1 else 0

theorem tail_byte (s₀ : State) {k : Nat} (hk : k < kf s₀) :
    s₀.mem (bufB (st s₀) k) = (tail s₀).getD k 0 := by
  simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
    Option.map_some, Option.getD_some]
  rw [← bufB_eq]

/-- The zero loop's invariant, before byte `j`, from the state `s₁` after the
prologue. -/
structure ZInv (s₀ : State) (s₁ : State) (j : Nat) (s : State) : Prop where
  j_le : kf s₀ ≤ j ∧ j ≤ 16
  x1 : s.gpr X1 = bufB (st s₀) j
  x0 : s.gpr X0 = BitVec.ofNat 64 (16 - j)
  y0 : s.gpr Y0 = 0
  keep : ∀ r, r ≠ X1 → r ≠ X0 → r ≠ Y0 → s.gpr r = s₁.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [bfR (st s₀)] s₀.mem s.mem
  buf : BufHas s.mem (st s₀) fun k =>
    if k < kf s₀ then (tail s₀).getD k 0 else if k < j then 0 else s₀.mem (bufB (st s₀) k)

theorem zinit_ok {s₀ : State} {s₁ : State} (h₁ : F0 s₀ s₁) :
    WP isa (.block [.li Y0 0, .addi X1 .a0 56, .add X1 X1 Y1, .li X0 16, .sub X0 X0 Y1]) s₁
      (ZInv s₀ s₁ (kf s₀)) := by
  have hk := kf_lt s₀
  refine wp_li (imm := 0) (by decide) fun s₂ u₂ => wp_addi (imm := 56) (by decide) fun s₃ u₃ =>
    wp_add fun s₄ u₄ => wp_li (imm := 16) (by decide) fun s₅ u₅ => wp_sub fun s₆ u₆ =>
    WP.block_nil ?_
  have hm : s₆.mem = s₁.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  refine ⟨⟨Nat.le_refl _, Nat.le_of_lt hk⟩, ?_, ?_, ?_, fun r h1 h2 h3 => ?_,
    by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, h₁.rd], by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, h₁.wr],
    by rw [hm, h₁.mem]; exact Frame.refl _ _, fun k hk' => ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₂.other _ (by decide), h₁.a0, h₁.y1, Offset.add_add]
  · rw [u₆.gpr, u₅.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), h₁.y1, Poly1305.sub_ofNat (by omega_using [hk])]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr]; rfl
  · rw [u₆.other r h2, u₅.other r h2, u₄.other r h1, u₃.other r h1, u₂.other r h3]
  · rw [hm, h₁.mem]
    by_cases hkf : k < kf s₀
    · simp only [hkf, ite_true]; exact tail_byte s₀ hkf
    · simp only [hkf, ite_false]

theorem zero_step {s₀ : State} (hp : FPre s₀) {s₁ : State} {j : Nat}
    (hj : j < 16) {s : State} (h : ZInv s₀ s₁ j s) :
    WP isa (.block zeroBody) s fun s' => ZInv s₀ s₁ (j + 1) s' := by
  refine wp_sb (t := Y0) (a := bufB (st s₀) j) (by decide) (by rw [h.x1, add_ofNat_zero])
    (by rw [h.wr]; exact bufB_in hp.st_in hj) fun s₂ m₂ => ?_
  refine wp_addi (imm := 1) (by decide) fun s₃ u₃ => wp_subi (imm := 1) (by decide) fun s₄ u₄ =>
    WP.block_nil ?_
  refine ⟨⟨Nat.le_trans h.j_le.1 (Nat.le_succ _), by omega_using [hj]⟩, ?_, ?_, ?_,
    fun r h1 h2 h3 => ?_, by rw [u₄.rd, u₃.rd, m₂.rd, h.rd], by rw [u₄.wr, u₃.wr, m₂.wr, h.wr], ?_,
    fun k hk => ?_⟩
  · rw [u₄.other _ (by decide), u₃.gpr, m₂.gpr, h.x1, bufB, Offset.add_add, Nat.add_assoc]
  · rw [u₄.gpr, u₃.other _ (by decide), m₂.gpr, h.x0, Poly1305.sub_ofNat (by omega_using [hj]),
      Nat.sub_sub]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), m₂.gpr, h.y0]
  · rw [u₄.other r h2, u₃.other r h1, m₂.gpr, h.keep r h1 h2 h3]
  · rw [u₄.mem, u₃.mem, m₂.mem]
    exact h.frame.writeW (List.mem_singleton_self _) _ (bfR_bufB _ hj)
  · rw [u₄.mem, u₃.mem, m₂.mem, WriteBytes.writeW8_apply]
    by_cases hkj : k = j
    · subst hkj
      simp only [ite_true, h.y0, show ¬ k < kf s₀ by have := h.j_le.1; omega_using [this],
        show k < k + 1 by omega_using [], ite_false]
      rfl
    · simp only [bufB_ne hk hj hkj, ite_false]
      rw [h.buf k hk]
      by_cases h1 : k < kf s₀
      · simp only [h1, ite_true]
      · simp only [h1, ite_false]
        by_cases h2 : k < j
        · simp only [h2, ite_true, show k < j + 1 by omega_using [h2]]
        · simp only [h2, ite_false, show ¬ k < j + 1 by omega_using [hkj, h2]]

theorem zeroLoop_ok {s₀ : State} (hp : FPre s₀) {s₁ : State} {s : State}
    (h : ZInv s₀ s₁ (kf s₀) s) :
    WP isa (.loop (.block zeroBody) (.nonzero X0)) s (ZInv s₀ s₁ 16) := by
  have hk := kf_lt s₀
  refine WP.loop (M := isa) (fun n s => ∃ j, n = 16 - j ∧ j < 16 ∧ ZInv s₀ s₁ j s) ?_ _ s
    ⟨kf s₀, rfl, hk, h⟩
  rintro n s ⟨j, rfl, hj, hz⟩
  refine WP.mono (zero_step hp hj hz) fun s' h' => ?_
  have hev := eval_nonzero_ofNat s' X0 (k := 16 - (j + 1)) (by omega_using [hj]) h'.x0
  by_cases hl : j + 1 = 16
  · exact .inl ⟨by rw [hev, decide_eq_false (show ¬ 16 - (j + 1) ≠ 0 by omega_using [hl])],
      hl ▸ h'⟩
  · exact .inr ⟨by rw [hev, decide_eq_true (show 16 - (j + 1) ≠ 0 by omega_using [hj, hl])],
      _, by omega_using [hj], j + 1, rfl, by omega_using [hj, hl], h'⟩

/-- After the `0x01` byte. -/
structure PInv (s₀ : State) (s₁ : State) (s : State) : Prop where
  keep : ∀ r, r ≠ X1 → r ≠ X0 → r ≠ Y0 → s.gpr r = s₁.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [bfR (st s₀)] s₀.mem s.mem
  buf : BufHas s.mem (st s₀) (padded s₀)

theorem one_byte : ((BitVec.ofNat 64 1).setWidth 8 : Byte) = 1 := by decide

theorem pad1_ok {s₀ : State} (hp : FPre s₀) {s₁ : State} (h₁ : F0 s₀ s₁) {s : State}
    (h : ZInv s₀ s₁ 16 s) :
    WP isa (.block [.li Y0 1, .addi X1 .a0 56, .add X1 X1 Y1, .store .b Y0 X1 0]) s (PInv s₀ s₁) := by
  have hk := kf_lt s₀
  refine wp_li (imm := 1) (by decide) fun s₂ u₂ => wp_addi (imm := 56) (by decide) fun s₃ u₃ =>
    wp_add fun s₄ u₄ => ?_
  have hx1 : s₄.gpr X1 = bufB (st s₀) (kf s₀) := by
    rw [u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₂.other _ (by decide),
      h.keep _ (by decide) (by decide) (by decide), h.keep _ (by decide) (by decide) (by decide),
      h₁.a0, h₁.y1, Offset.add_add]
  refine wp_sb (t := Y0) (a := bufB (st s₀) (kf s₀)) (by decide) (by rw [hx1, add_ofNat_zero])
    (by rw [u₄.wr, u₃.wr, u₂.wr, h.wr]; exact bufB_in hp.st_in hk) fun s₅ m₅ => WP.block_nil ?_
  refine ⟨fun r h1 h2 h3 => ?_, by rw [m₅.rd, u₄.rd, u₃.rd, u₂.rd, h.rd],
    by rw [m₅.wr, u₄.wr, u₃.wr, u₂.wr, h.wr], ?_, fun k hk' => ?_⟩
  · rw [m₅.gpr, u₄.other r h1, u₃.other r h1, u₂.other r h3, h.keep r h1 h2 h3]
  · rw [m₅.mem, u₄.mem, u₃.mem, u₂.mem]
    exact h.frame.writeW (List.mem_singleton_self _) _ (bfR_bufB _ hk)
  · rw [m₅.mem, u₄.mem, u₃.mem, u₂.mem, WriteBytes.writeW8_apply, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, one_byte]
    by_cases hkj : k = kf s₀
    · subst hkj
      simp only [ite_true, padded, Nat.lt_irrefl, ite_false]
    · simp only [bufB_ne hk' hk hkj, ite_false]
      rw [h.buf k hk']
      by_cases h1 : k < kf s₀
      · simp only [h1, ite_true, padded]
      · simp only [h1, ite_false, hk', ite_true, padded, hkj]

/-- The padded block as a number: the buffered bytes with `0x01` appended. -/
theorem padded_value {s₀ : State} {m : Mem} (h : BufHas m (st s₀) (padded s₀)) :
    leNum (bytesAt m (off (st s₀) 56) 16) + 2 ^ 128 * false.toNat = leNum (tail s₀ ++ [0x01]) := by
  have hk := kf_lt s₀
  have hlen : (tail s₀).length = kf s₀ := Poly1305.length_bytesAt _ _ _
  have hl : (List.range 16).map (padded s₀) = (tail s₀ ++ [0x01]) ++ List.replicate (15 - kf s₀) 0 := by
    apply List.ext_getElem
    · simp [hlen]; omega_using [hk, hlen]
    · intro k h₁ h₂
      simp only [List.getElem_map, List.getElem_range]
      rcases Nat.lt_trichotomy k (kf s₀) with hk' | rfl | hk'
      · rw [List.getElem_append_left (by simp [hlen]; omega_using [hlen, hk']),
          List.getElem_append_left (by omega_using [hlen, hk'])]
        simp only [padded, hk', ite_true]
        simp [List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (show k < (tail s₀).length by omega_using [hlen, hk'])]
      · rw [List.getElem_append_left (by simp [hlen]), List.getElem_append_right (by omega_using [hlen])]
        simp [padded, hlen]
      · rw [List.getElem_append_right (by simp [hlen]; omega_using [hlen, hk'])]
        simp [padded, show ¬ k < kf s₀ by omega_using [hlen, hk'],
          show k ≠ kf s₀ by omega_using [hlen, hk']]
  rw [Bool.toNat_false, Nat.mul_zero, Nat.add_zero, bytesAt_buf h, hl,
    Poly1305.leNum_append _ (List.replicate _ _), Poly1305.leNum_replicate_zero, Nat.mul_zero,
    Nat.add_zero]

/-- After the buffered bytes (if any) are absorbed. -/
structure Tail (s₀ : State) (s₁ : State) (s : State) : Prop where
  keep : ∀ r ∈ [Reg.a0, .a2], s.gpr r = s₁.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [bfR (st s₀)] s₀.mem s.mem
  acc : A0 s₀ < P → hv s % P = Poly1305.absorbAll (Rn s₀) (A0 s₀) (tail s₀) % P ∧ Bounds s

theorem tail_nil {s₀ : State} (h : kf s₀ = 0) : tail s₀ = [] := by
  simp [tail, bytesAt, h]

theorem lastBlock_eq : lastBlock =
    .seq (.block [.li Y0 0, .addi X1 .a0 56, .add X1 X1 Y1, .li X0 16, .sub X0 X0 Y1])
      (.seq (.loop (.block zeroBody) (.nonzero X0))
        (.block (([.li Y0 1, .addi X1 .a0 56, .add X1 X1 Y1, .store .b Y0 X1 0] : List Instr) ++
          absorb .a0 56 false))) := rfl

theorem lastBlock_ok {s₀ : State} (hp : FPre s₀) {s₁ : State} (h₁ : F0 s₀ s₁)
    (hpos : 0 < kf s₀) : WP isa lastBlock s₁ (Tail s₀ s₁) := by
  have hk := kf_lt s₀
  rw [lastBlock_eq]
  refine WP.seq (WP.mono (zinit_ok h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (zeroLoop_ok hp h₂) fun s₃ h₃ => ?_)
  refine WP.block_append (WP.mono (pad1_ok hp h₁ h₃) fun s₄ h₄ => ?_)
  have g : ∀ r, r ≠ X1 → r ≠ X0 → r ≠ Y0 → s₄.gpr r = s₁.gpr r := h₄.keep
  have x0₄ : s₄.gpr .a0 = st s₀ := by rw [g .a0 (by decide) (by decide) (by decide), h₁.a0]
  have hk₄ : Keys (Rn s₀) s₄ := h₁.keys.of_regs fun r hr => g r (by revert r; decide)
    (by revert r; decide) (by revert r; decide)
  refine WP.mono (absorbBuf_ok s₄ false hk₄ (by rw [h₄.wr, x0₄]; exact hp.st_in))
    fun s₅ ⟨ha, k₅⟩ => ?_
  refine ⟨fun r hr => ?_, by rw [k₅.2.2.1, h₄.rd], by rw [k₅.2.2.2.1, h₄.wr],
    by rw [k₅.2.1]; exact h₄.frame, fun hA => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rw [k₅.gpr', g _ (by decide) (by decide) (by decide)]
  · have hv₄ : hv s₄ = hv s₁ := by
      simp only [hv, val3, g H0 (by decide) (by decide) (by decide),
        g H1 (by decide) (by decide) (by decide), g H2 (by decide) (by decide) (by decide)]
    have hb₄ : Bounds s₁ → Bounds s₄ := by
      simp only [Bounds, g H2 (by decide) (by decide) (by decide)]; exact id
    obtain ⟨hv₁, hb₁⟩ := h₁.acc hA
    obtain ⟨hv, hb⟩ := ha (hb₄ hb₁)
    refine ⟨?_, hb⟩
    have hlen : (tail s₀).length = kf s₀ := Poly1305.length_bytesAt _ _ _
    rw [hv, hv₄, hv₁, x0₄, padded_value h₄.buf,
      Poly1305.absorbAll_block (by omega_using [hpos, hk, hlen]) (by omega_using [hpos, hk, hlen]),
      Nat.mod_mod, Nat.mul_comm]

/-! ## Epilogue -/

theorem fepilogue_ok {s₀ : State} (hp : FPre s₀) {s₁ : State} (h₁ : F0 s₀ s₁) {s : State}
    (ht : Tail s₀ s₁ s) :
    WP isa (.block (reduce ++ addS ++ storeTag)) s fun s' => Proof.Poly1305.finalizeRISCV64.post s₀ s' := by
  have x0 : s.gpr .a0 = st s₀ := by rw [ht.keep .a0 (by simp), h₁.a0]
  have x2 : s.gpr .a2 = op s₀ := by rw [ht.keep .a2 (by simp), h₁.a2]
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (reduce_ok s) fun s₂ ⟨hr, k₂⟩ => ?_)
  have x0₂ : s₂.gpr .a0 = st s₀ := by rw [k₂.gpr', x0]
  refine WP.block_append (WP.mono (addS_ok s₂ (by
    rw [k₂.2.2.1, k₂.2.2.2.1, ht.wr, x0₂]; exact List.mem_append_right _ hp.st_in)
    (by rw [x0₂]; exact hp.st_al))
    fun s₃ ⟨ha, k₃⟩ => ?_)
  have x2₃ : s₃.gpr .a2 = op s₀ := by rw [k₃.gpr', k₂.gpr', x2]
  refine WP.mono (storeTag_ok s₃ (by rw [k₃.2.2.2.1, k₂.2.2.2.1, ht.wr, x2₃]; exact hp.o_in))
    fun s₄ hm₄ => ?_
  intro key msg hbuf hcnt
  obtain ⟨W, B, rfl, hrep, hBl, hBb⟩ := Buffered.split hbuf
  have hk : kf s₀ = (W ++ B).length % 16 := hcnt
  have htail : tail s₀ = B := by rw [tail, hk, off_56]; exact hBb
  rw [← htail]
  have hA := A0_lt hrep
  obtain ⟨hv₀, hb⟩ := ht.acc hA
  have hN := hr hb
  rw [hv₀, Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hA _)] at hN
  -- The key's `s`, unchanged since entry.
  have hf : Frame [hR (st s₀), wR (st s₀)] s₀.mem s₂.mem := by
    rw [k₂.2.1]
    exact ht.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨wR (st s₀), by simp, bfR_sub_wR _⟩
  have hS : word s₂.mem (s₂.gpr .a0) 40 + 2 ^ 64 * word s₂.mem (s₂.gpr .a0) 48 =
      leNum (((bytesAt s₀.mem (off (st s₀) 24) 32).drop 16).take 16) := by
    rw [key_drop, leNum_key, x0₂, word, word, word, word, add_ofNat_zero, off, Offset.add_add,
      key_word hf (d := 40) (by decide) (by decide), key_word hf (d := 48) (by decide) (by decide)]
  rw [hS] at ha
  have hH : (s₂.gpr H0).toNat + 2 ^ 64 * (s₂.gpr H1).toNat + 2 ^ 128 * (s₂.gpr H2).toNat =
      accumulate (clamp (leNum ((bytesAt s₀.mem (off (st s₀) 24) 32).take 16))) (W ++ tail s₀) := by
    rw [clamp_key, Poly1305.accumulate_append hrep.1, repr_acc hrep]
    exact hN
  simp only [mac]
  rw [repr_key hrep] at hH ha
  rw [hm₄, x2₃]
  refine tag_bytes _ _ _ _ _ ?_
  rw [ha, ← hH]
  omega_using []

/-! ## The whole function -/

theorem finalize_correct {s₀ : State} (hp : FPre s₀) :
    WP isa finalize s₀ (Proof.Poly1305.finalizeRISCV64.post s₀) := by
  refine WP.seq (WP.mono (fprologue_ok hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (Q := Tail s₀ s₁) ?_ fun s₃ h₃ => fepilogue_ok hp h₁ h₃)
  refine WP.ite (decide (kf s₀ = 0))
    (by rw [eval_zero, h₁.y1, ofNat_beq_zero (by have := kf_lt s₀; omega_using [this])])
    (fun h => ?_) (fun h => ?_)
  · simp only [decide_eq_true_eq] at h
    refine WP.block_nil (M := isa) ⟨fun r _ => rfl, h₁.rd, h₁.wr, by rw [h₁.mem]; exact Frame.refl _ _,
      fun hA => ?_⟩
    obtain ⟨e, b⟩ := h₁.acc hA
    refine ⟨?_, b⟩
    rw [tail_nil h, Poly1305.absorbAll_nil, e]
  · simp only [decide_eq_false_iff_not] at h
    exact lastBlock_ok hp h₁ (Nat.pos_of_ne_zero h)

theorem finalize_ok (s : State) (hp : FPre s) :
    ∃ t s', Exec isa finalize s t s' ∧ abiPreserved s s' ∧ Proof.Poly1305.finalizeRISCV64.post s s' := by
  obtain ⟨tr, t, he, hpost, hkeep⟩ :=
    WP.keep written (finalize_correct hp) (by lit_decide) (by lit_decide)
  exact ⟨tr, t, he, abiPreserved_of_keep he hkeep (by decide) (by decide), hpost⟩

theorem finalize_ct {pre : State → Prop} {pub : State → State → Prop}
    (hpub : ∀ s₁ s₂, pub s₁ s₂ → s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
      s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.sp = s₂.sp) :
    ConstantTime isa pre pub finalize := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  obtain ⟨h0, h1, h2, hsp⟩ := hpub s₁ s₂ h
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2

/-- A state satisfying the precondition. -/
def finalizeSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a2 => 0x2000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 128⟩, ⟨0x2000, 16⟩]

theorem finalize_verified : Verified RISCV64.target finalize Proof.Poly1305.finalizeRISCV64 :=
  ⟨fun s hs => finalize_ok s ⟨by rw [hs.2.1]; exact List.mem_cons_self,
      by rw [hs.2.1]; exact List.mem_cons_of_mem _ List.mem_cons_self, hs.2.2.1, hs.2.2.2⟩,
    finalize_ct fun _ _ h => h,
    ⟨finalizeSat, rfl, rfl, Region.disjoint_of_sep (by decide), by decide⟩⟩

/-- A state satisfying the precondition, with a working space. -/
def finalizeScratchSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a2 => 0x2000 | .a3 => 0x3000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 128⟩, ⟨0x2000, 16⟩, ⟨0x3000, 128⟩]

theorem finalizeScratch_verified :
    Verified RISCV64.target finalize Proof.Poly1305.finalizeScratchRISCV64 :=
  ⟨fun s hs => finalize_ok s ⟨by rw [hs.2.1]; exact List.mem_cons_self,
      by rw [hs.2.1]; exact List.mem_cons_of_mem _ List.mem_cons_self, hs.2.2.1, hs.2.2.2.2.2⟩,
    finalize_ct fun _ _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2⟩,
    ⟨finalizeScratchSat, rfl, rfl, Region.disjoint_of_sep (by decide),
      Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), by decide⟩⟩

end VG.Proof.Poly1305.RISCV64
