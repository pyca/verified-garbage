import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Blake2.X86.CompressS.Dword
import VerifiedGarbage.Proof.Blake2.Spec
import VerifiedGarbage.Impl.Blake2.X86.CompressS

/-!
# BLAKE2s on x86 (32-bit), with SSE2: the rounds

Doubleword `i` of `xmm r` holds word `4 r + i` of the work vector (`Rows`).
`vg_ok` executes `G` on each doubleword of the four rows once, for any
values; `gather_ok` the gathering of four message words, for any words of
the block (`Msg`); `round_ok` and `rounds_ok` compose them into the rounds of
`F`: `G` on each doubleword is the column step, and with the rows rotated
(`diag`), the diagonal step.
-/

namespace VG.Proof.Blake2.X86.CompressS

open VG VG.X86
open VG.Spec.Blake2 (Work Block G sigmaAt)
open VG.Proof.Blake2 (mix G_get)
open VG.Impl.Blake2.X86 (at_)
open VG.Impl.Blake2.X86.CompressS

/-- The block `M` is at `K`: word `j` at `[K + 4j]`. -/
def Msg (K : BitVec 32) (M : Block 32) (m : Mem) : Prop :=
  ∀ j : Fin 16, m.readW (addr K (4 * j.val)) 32 = M j

/-- Doubleword `l` of register `r`. -/
abbrev dw (s : State) (r : XReg) (l : Nat) : BitVec 32 := dword (s.xmm r) l

/-! ## `G` on each doubleword -/

theorem rotr12 (x : BitVec 32) : x >>> 12 ||| x <<< 20 = x.rotateRight 12 := shr_or_shl x (by decide)
theorem rotr8 (x : BitVec 32) : x >>> 8 ||| x <<< 24 = x.rotateRight 8 := shr_or_shl x (by decide)
theorem rotr7 (x : BitVec 32) : x >>> 7 ||| x <<< 25 = x.rotateRight 7 := shr_or_shl x (by decide)

theorem psrld_12 (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .psrld x (BitVec.ofNat 8 12)) i = dword x i >>> 12 := dword_psrld x _ (by decide) hi
theorem pslld_20 (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .pslld x (BitVec.ofNat 8 20)) i = dword x i <<< 20 := dword_pslld x _ (by decide) hi
theorem psrld_8 (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .psrld x (BitVec.ofNat 8 8)) i = dword x i >>> 8 := dword_psrld x _ (by decide) hi
theorem pslld_24 (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .pslld x (BitVec.ofNat 8 24)) i = dword x i <<< 24 := dword_pslld x _ (by decide) hi
theorem psrld_7 (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .psrld x (BitVec.ofNat 8 7)) i = dword x i >>> 7 := dword_psrld x _ (by decide) hi
theorem pslld_25 (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .pslld x (BitVec.ofNat 8 25)) i = dword x i <<< 25 := dword_pslld x _ (by decide) hi

theorem vg_eq : vg =
    [xb .paddd .xmm0 .xmm5, xb .paddd .xmm0 .xmm1, xb .pxor .xmm3 .xmm0,
     .xop (.pshuflw .xmm3 .xmm3 0xb1), .xop (.pshufhw .xmm3 .xmm3 0xb1),
     xb .paddd .xmm2 .xmm3, xb .pxor .xmm1 .xmm2,
     xb .movdqa .xmm4 .xmm1, .xop (.shift .psrld .xmm1 (BitVec.ofNat 8 12)),
     .xop (.shift .pslld .xmm4 (BitVec.ofNat 8 20)), xb .por .xmm1 .xmm4,
     xb .paddd .xmm0 .xmm6, xb .paddd .xmm0 .xmm1, xb .pxor .xmm3 .xmm0,
     xb .movdqa .xmm4 .xmm3, .xop (.shift .psrld .xmm3 (BitVec.ofNat 8 8)),
     .xop (.shift .pslld .xmm4 (BitVec.ofNat 8 24)), xb .por .xmm3 .xmm4,
     xb .paddd .xmm2 .xmm3, xb .pxor .xmm1 .xmm2,
     xb .movdqa .xmm4 .xmm1, .xop (.shift .psrld .xmm1 (BitVec.ofNat 8 7)),
     .xop (.shift .pslld .xmm4 (BitVec.ofNat 8 25)), xb .por .xmm1 .xmm4] := rfl

theorem add_swap (a x b : BitVec 32) : a + x + b = a + b + x := by
  rw [BitVec.add_assoc, BitVec.add_comm x b, ← BitVec.add_assoc]

/-- `G`'s four words of doubleword `l`, from the rows and the message words
in `xmm5` and `xmm6`. -/
abbrev laneMix (s : State) (l : Nat) : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 :=
  mix Spec.Blake2.s (dw s .xmm0 l) (dw s .xmm1 l) (dw s .xmm2 l) (dw s .xmm3 l) (dw s .xmm5 l)
    (dw s .xmm6 l)

theorem vg_ok (s : State) :
    WP isa (.block vg) s fun s' =>
      (∀ l, l < 4 → dw s' .xmm0 l = (laneMix s l).1 ∧ dw s' .xmm1 l = (laneMix s l).2.1 ∧
        dw s' .xmm2 l = (laneMix s l).2.2.1 ∧ dw s' .xmm3 l = (laneMix s l).2.2.2) ∧
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm3 → r ≠ .xmm4 → s'.xmm r = s.xmm r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [vg_eq]
  apply WP.of_runBlock
  simp only [xb, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    RegUpd.gpr_setXmm, RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm,
    Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl => ?_, fun r h0 h1 h2 h3 h4 => ?_, trivial, trivial, trivial, trivial⟩
  · simp only [dw, RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true,
      eval_movdqa]
    simp only [dword_paddd _ _ hl, dword_pxor, dword_por, dword_rot16 _ hl, psrld_12 _ hl,
      pslld_20 _ hl, psrld_8 _ hl, pslld_24 _ hl, psrld_7 _ hl, pslld_25 _ hl, rotr12, rotr8, rotr7,
      rotateLeft_16, laneMix, mix, Spec.Blake2.s, add_swap, and_self]
  · simp only [RegUpd.xmm_setXmm_of_ne, h0, h1, h2, h3, h4, not_false_eq_true]

/-! ## Gathering message words -/

theorem gather_eq (x : XReg) (f : Nat → Nat) : gather x f =
    [.mov .ecx (.mem ⟨.edi, 4 * f 0⟩), .mov .edx (.mem ⟨.edi, 4 * f 1⟩),
     .xop (.movd x .ecx), .xop (.movd .xmm7 .edx), .xop (.bin .punpckldq x .xmm7),
     .mov .ecx (.mem ⟨.edi, 4 * f 2⟩), .mov .edx (.mem ⟨.edi, 4 * f 3⟩),
     .xop (.movd .xmm4 .ecx), .xop (.movd .xmm7 .edx), .xop (.bin .punpckldq .xmm4 .xmm7),
     .xop (.bin .punpcklqdq x .xmm4)] := rfl

theorem gathered (a b c d : BitVec 32) :
    XBinOp.eval .punpcklqdq (XBinOp.eval .punpckldq ((0 : BitVec 96) ++ a) ((0 : BitVec 96) ++ b))
      (XBinOp.eval .punpckldq ((0 : BitVec 96) ++ c) ((0 : BitVec 96) ++ d)) = ofDwords a b c d := by
  simp only [punpcklqdq_eq, punpckldq_eq, dword_ofDwords_0, dword_ofDwords_1, dword_movd_0]

theorem dword_gathered (f : Nat → BitVec 32) {i : Nat} (hi : i < 4) :
    dword (ofDwords (f 0) (f 1) (f 2) (f 3)) i = f i := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;> simp only [dword_ofDwords_0, dword_ofDwords_1,
    dword_ofDwords_2, dword_ofDwords_3]

theorem xmm_setReg_app (s : State) (r : Reg) (v : BitVec 32) (x : XReg) :
    (s.setReg r v).xmm x = s.xmm x := rfl

theorem gather_ok {K : BitVec 32} {M : Block 32} {s : State} (hk : s.gpr .edi = K)
    (hm : Msg K M s.mem) (hrd : ∀ j < 16, InRegions (s.rd ++ s.wr) (addr K (4 * j)) 4)
    {x : XReg} (hx4 : x ≠ .xmm4) (hx7 : x ≠ .xmm7) {f : Nat → Nat} (hf : ∀ i < 4, f i < 16) :
    WP isa (.block (gather x f)) s fun s' =>
      (∀ i (hi : i < 4), dw s' x i = M ⟨f i, hf i hi⟩) ∧
      (∀ y, y ≠ x → y ≠ .xmm4 → y ≠ .xmm7 → s'.xmm y = s.xmm y) ∧
      (∀ r, r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have r0 := hrd _ (hf 0 (by decide))
  have r1 := hrd _ (hf 1 (by decide))
  have r2 := hrd _ (hf 2 (by decide))
  have r3 := hrd _ (hf 3 (by decide))
  rw [gather_eq]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, readSrc, ea_mk,
    State.load32, RegUpd.gpr_setReg_self, RegUpd.gpr_setXmm, RegUpd.mem_setXmm, RegUpd.rd_setXmm,
    RegUpd.wr_setXmm, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.gpr_setReg_of_ne, hk, r0, r1, r2, r3, reduceCtorEq, not_false_eq_true, ↓reduceIte,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun i hi => ?_, fun y h1 h2 h3 => ?_, fun r h1 h2 => ?_, trivial, trivial, trivial⟩
  · simp only [dw, xmm_setReg_app, RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne _ _ hx4, RegUpd.xmm_setXmm_of_ne _ _ hx7,
      RegUpd.xmm_setXmm_of_ne _ _ (show (XReg.xmm4) ≠ .xmm7 by decide), gathered]
    rw [dword_gathered (fun i => s.mem.readW (addr K (4 * f i)) 32) hi, hm ⟨f i, hf i hi⟩]
  · simp only [xmm_setReg_app, RegUpd.xmm_setXmm_of_ne _ _ h1, RegUpd.xmm_setXmm_of_ne _ _ h2,
      RegUpd.xmm_setXmm_of_ne _ _ h3]
  · simp only [RegUpd.gpr_setXmm, RegUpd.gpr_setReg_of_ne _ _ h1, RegUpd.gpr_setReg_of_ne _ _ h2]

/-! ## The rows -/

/-- The work vector `v` is in `xmm0, …, xmm3`: word `4 r + i` in doubleword
`i` of `xmm r`. -/
structure Rows (v : Work 32) (s : State) : Prop where
  r0 : ∀ i (hi : i < 4), dw s .xmm0 i = v[i]
  r1 : ∀ i (hi : i < 4), dw s .xmm1 i = v[4 + i]
  r2 : ∀ i (hi : i < 4), dw s .xmm2 i = v[8 + i]
  r3 : ∀ i (hi : i < 4), dw s .xmm3 i = v[12 + i]

theorem fin16_val (n : Nat) : ((no_index (OfNat.ofNat n) : Fin 16) : Nat) = n % 16 := rfl

/-- The four `G`s on the columns, with message words `X i` and `Y i`. -/
abbrev colStep (v : Work 32) (X Y : Nat → BitVec 32) : Work 32 :=
  G Spec.Blake2.s (G Spec.Blake2.s (G Spec.Blake2.s (G Spec.Blake2.s v 0 4 8 12 (X 0) (Y 0))
    1 5 9 13 (X 1) (Y 1)) 2 6 10 14 (X 2) (Y 2)) 3 7 11 15 (X 3) (Y 3)

/-- The four `G`s on the diagonals, with message words `X i` and `Y i`. -/
abbrev diagStep (v : Work 32) (X Y : Nat → BitVec 32) : Work 32 :=
  G Spec.Blake2.s (G Spec.Blake2.s (G Spec.Blake2.s (G Spec.Blake2.s v 0 5 10 15 (X 0) (Y 0))
    1 6 11 12 (X 1) (Y 1)) 2 7 8 13 (X 2) (Y 2)) 3 4 9 14 (X 3) (Y 3)

/-- Message word `j` of half `k` of round `r`. -/
abbrev msgW (M : Block 32) (r k j : Nat) : BitVec 32 := M (sigmaAt r (8 * k + j))

theorem round_eq (M : Block 32) (v : Work 32) (r : Nat) :
    Spec.Blake2.round Spec.Blake2.s M v r =
      diagStep (colStep v (fun i => msgW M r 0 (2 * i)) (fun i => msgW M r 0 (2 * i + 1)))
        (fun i => msgW M r 1 (2 * i)) (fun i => msgW M r 1 (2 * i + 1)) := rfl

/-! Bounds of the indices of the work vector, which `get_elem_tactic` would
prove by `omega` over every hypothesis of a long proof. -/

theorem ix0 {i : Nat} (hi : i < 4) : i < 16 := by omega
theorem ix4 {i : Nat} (hi : i < 4) : 4 + i < 16 := by omega
theorem ix8 {i : Nat} (hi : i < 4) : 8 + i < 16 := by omega
theorem ix12 {i : Nat} (hi : i < 4) : 12 + i < 16 := by omega
theorem dx0 (i : Nat) : (i + 3) % 4 < 16 := by omega
theorem dx4 (i : Nat) : 4 + (i + 1) % 4 < 16 := by omega
theorem dx8 (i : Nat) : 8 + (i + 2) % 4 < 16 := by omega
theorem dx12 (i : Nat) : 12 + (i + 3) % 4 < 16 := by omega

/-- Column `i` after the column step is `G` on column `i`. -/
theorem col_get (v : Work 32) (X Y : Nat → BitVec 32) {i : Nat} (hi : i < 4) :
    (colStep v X Y)[i]'(ix0 hi) =
      (mix Spec.Blake2.s (v[i]'(ix0 hi)) (v[4 + i]'(ix4 hi)) (v[8 + i]'(ix8 hi)) (v[12 + i]'(ix12 hi))
        (X i) (Y i)).1 ∧
    (colStep v X Y)[4 + i]'(ix4 hi) =
      (mix Spec.Blake2.s (v[i]'(ix0 hi)) (v[4 + i]'(ix4 hi)) (v[8 + i]'(ix8 hi)) (v[12 + i]'(ix12 hi))
        (X i) (Y i)).2.1 ∧
    (colStep v X Y)[8 + i]'(ix8 hi) =
      (mix Spec.Blake2.s (v[i]'(ix0 hi)) (v[4 + i]'(ix4 hi)) (v[8 + i]'(ix8 hi)) (v[12 + i]'(ix12 hi))
        (X i) (Y i)).2.2.1 ∧
    (colStep v X Y)[12 + i]'(ix12 hi) =
      (mix Spec.Blake2.s (v[i]'(ix0 hi)) (v[4 + i]'(ix4 hi)) (v[8 + i]'(ix8 hi)) (v[12 + i]'(ix12 hi))
        (X i) (Y i)).2.2.2 := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [G_get, Fin.getElem_fin, fin16_val, Nat.reduceMod, Nat.reduceAdd,
      Nat.reduceEqDiff, ↓reduceIte, and_self]

/-- Diagonal `i` after the diagonal step is `G` on diagonal `i`. -/
theorem diag_get (v : Work 32) (X Y : Nat → BitVec 32) {i : Nat} (hi : i < 4) :
    (diagStep v X Y)[i]'(ix0 hi) =
      (mix Spec.Blake2.s (v[i]'(ix0 hi)) (v[4 + (i + 1) % 4]'(dx4 i))
      (v[8 + (i + 2) % 4]'(dx8 i)) (v[12 + (i + 3) % 4]'(dx12 i)) (X i) (Y i)).1 ∧
    (diagStep v X Y)[4 + (i + 1) % 4]'(dx4 i) =
      (mix Spec.Blake2.s (v[i]'(ix0 hi)) (v[4 + (i + 1) % 4]'(dx4 i))
      (v[8 + (i + 2) % 4]'(dx8 i)) (v[12 + (i + 3) % 4]'(dx12 i)) (X i) (Y i)).2.1 ∧
    (diagStep v X Y)[8 + (i + 2) % 4]'(dx8 i) =
      (mix Spec.Blake2.s (v[i]'(ix0 hi)) (v[4 + (i + 1) % 4]'(dx4 i))
      (v[8 + (i + 2) % 4]'(dx8 i)) (v[12 + (i + 3) % 4]'(dx12 i)) (X i) (Y i)).2.2.1 ∧
    (diagStep v X Y)[12 + (i + 3) % 4]'(dx12 i) =
      (mix Spec.Blake2.s (v[i]'(ix0 hi)) (v[4 + (i + 1) % 4]'(dx4 i))
      (v[8 + (i + 2) % 4]'(dx8 i)) (v[12 + (i + 3) % 4]'(dx12 i)) (X i) (Y i)).2.2.2 := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [G_get, Fin.getElem_fin, fin16_val, Nat.reduceMod, Nat.reduceAdd,
      Nat.reduceEqDiff, ↓reduceIte, and_self]

/-! ## Rotating the rows -/

theorem shuf39 (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (shufDwords x 0x39) i = dword x ((i + 1) % 4) := by
  rw [dword_shufDwords _ _ hi]; rcases cases4 hi with rfl | rfl | rfl | rfl <;> rfl
theorem shuf4e (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (shufDwords x 0x4e) i = dword x ((i + 2) % 4) := by
  rw [dword_shufDwords _ _ hi]; rcases cases4 hi with rfl | rfl | rfl | rfl <;> rfl
theorem shuf93 (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (shufDwords x 0x93) i = dword x ((i + 3) % 4) := by
  rw [dword_shufDwords _ _ hi]; rcases cases4 hi with rfl | rfl | rfl | rfl <;> rfl

/-- `xmm0, xmm2, xmm3` rotated by `a, b, c` doublewords by three `pshufd`. -/
theorem shufs_ok (o₁ o₂ o₃ : BitVec 8) {a b c : Nat}
    (h₁ : ∀ x i, i < 4 → dword (shufDwords x o₁) i = dword x ((i + a) % 4))
    (h₂ : ∀ x i, i < 4 → dword (shufDwords x o₂) i = dword x ((i + b) % 4))
    (h₃ : ∀ x i, i < 4 → dword (shufDwords x o₃) i = dword x ((i + c) % 4)) (s : State) :
    WP isa (.block [.xop (.pshufd .xmm0 .xmm0 o₁), .xop (.pshufd .xmm2 .xmm2 o₂),
      .xop (.pshufd .xmm3 .xmm3 o₃)]) s fun s' =>
      (∀ i, i < 4 → dw s' .xmm0 i = dw s .xmm0 ((i + a) % 4)) ∧
      (∀ i, i < 4 → dw s' .xmm1 i = dw s .xmm1 i) ∧
      (∀ i, i < 4 → dw s' .xmm2 i = dw s .xmm2 ((i + b) % 4)) ∧
      (∀ i, i < 4 → dw s' .xmm3 i = dw s .xmm3 ((i + c) % 4)) ∧
      (∀ r, r ≠ .xmm0 → r ≠ .xmm2 → r ≠ .xmm3 → s'.xmm r = s.xmm r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, RegUpd.gpr_setXmm,
    RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm, Option.some.injEq, exists_eq_left']
  refine ⟨fun i hi => ?_, fun i _ => ?_, fun i hi => ?_, fun i hi => ?_, fun r h1 h2 h3 => ?_, trivial,
    trivial, trivial, trivial⟩ <;>
    simp only [dw, RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true]
  · exact h₁ _ i hi
  · exact h₂ _ i hi
  · exact h₃ _ i hi
  · simp only [RegUpd.xmm_setXmm_of_ne _ _ h1, RegUpd.xmm_setXmm_of_ne _ _ h2,
      RegUpd.xmm_setXmm_of_ne _ _ h3]

theorem diag_eq : diag = [.xop (.pshufd .xmm0 .xmm0 0x93), .xop (.pshufd .xmm2 .xmm2 0x39),
    .xop (.pshufd .xmm3 .xmm3 0x4e)] := rfl
theorem undiag_eq : undiag = [.xop (.pshufd .xmm0 .xmm0 0x39), .xop (.pshufd .xmm2 .xmm2 0x93),
    .xop (.pshufd .xmm3 .xmm3 0x4e)] := rfl

theorem lane_0 (i : Nat) : lane 0 i = i := rfl
theorem lane_1 (i : Nat) : lane 1 i = (i + 3) % 4 := rfl
theorem lane_lt (k : Nat) {i : Nat} (hi : i < 4) : lane k i < 4 := by
  unfold lane; split <;> omega

/-! ## The rounds -/

/-- During the rounds of a block, from `s₀`: the work vector is `v`, and
only the XMM registers, `ecx` and `edx` (and the flags) have changed. -/
structure RS (s₀ : State) (v : Work 32) (s : State) : Prop where
  rows : Rows v s
  gpr : ∀ r, r ≠ .ecx → r ≠ .edx → s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

section
variable {K : BitVec 32} {M : Block 32} {s₀ : State} (hk : s₀.gpr .edi = K) (hm : Msg K M s₀.mem)
  (hrd : ∀ j < 16, InRegions (s₀.rd ++ s₀.wr) (addr K (4 * j)) 4)
include hk hm hrd

/-- The message words of half `k` of round `r` into `xmm5` and `xmm6`. -/
theorem msgs_ok {s : State} (hs : ∀ r, r ≠ .ecx → r ≠ .edx → s.gpr r = s₀.gpr r)
    (hsm : s.mem = s₀.mem) (hsr : s.rd = s₀.rd) (hsw : s.wr = s₀.wr) (r k : Nat) :
    WP isa (.block (msgs r k)) s fun s' =>
      (∀ i, i < 4 → dw s' .xmm5 i = msgW M r k (2 * lane k i)) ∧
      (∀ i, i < 4 → dw s' .xmm6 i = msgW M r k (2 * lane k i + 1)) ∧
      (∀ y, y ≠ .xmm4 → y ≠ .xmm5 → y ≠ .xmm6 → y ≠ .xmm7 → s'.xmm y = s.xmm y) ∧
      (∀ g, g ≠ .ecx → g ≠ .edx → s'.gpr g = s₀.gpr g) ∧ s'.mem = s₀.mem ∧ s'.rd = s₀.rd ∧
      s'.wr = s₀.wr := by
  have hk' : s.gpr .edi = K := by rw [hs _ (by decide) (by decide), hk]
  have hm' : Msg K M s.mem := by rw [hsm]; exact hm
  have hrd' : ∀ j < 16, InRegions (s.rd ++ s.wr) (addr K (4 * j)) 4 := by rw [hsr, hsw]; exact hrd
  unfold msgs
  rw [WP.block_append_iff]
  refine WP.mono (gather_ok hk' hm' hrd' (x := .xmm5) (by decide) (by decide)
    (fun i _ => (sigmaAt r (8 * k + 2 * lane k i)).isLt)) fun s₁ ⟨x₁, o₁, g₁, m₁, r₁, w₁⟩ => ?_
  refine WP.mono (gather_ok (M := M) (by rw [g₁ _ (by decide) (by decide), hk']) (by rw [m₁]; exact hm')
    (by rw [r₁, w₁]; exact hrd') (x := .xmm6) (by decide) (by decide)
    (fun i _ => (sigmaAt r (8 * k + 2 * lane k i + 1)).isLt)) fun s₂ ⟨x₂, o₂, g₂, m₂, r₂, w₂⟩ => ?_
  refine ⟨fun i hi => ?_, fun i hi => x₂ i hi, fun y h4 h5 h6 h7 => ?_, fun g h1 h2 => ?_,
    by rw [m₂, m₁, hsm], by rw [r₂, r₁, hsr], by rw [w₂, w₁, hsw]⟩
  · rw [dw, o₂ _ (by decide) (by decide) (by decide)]; exact x₁ i hi
  · rw [o₂ _ h6 h4 h7, o₁ _ h5 h4 h7]
  · rw [g₂ g h1 h2, g₁ g h1 h2, hs g h1 h2]

omit hk hm hrd in
/-- `G` on each doubleword of the rows `v`, with message words `X` and `Y`. -/
theorem vg_rows {v : Work 32} {s : State} (h : Rows v s) {X Y : Nat → BitVec 32}
    (hX : ∀ i, i < 4 → dw s .xmm5 i = X i) (hY : ∀ i, i < 4 → dw s .xmm6 i = Y i) :
    WP isa (.block vg) s fun s' => Rows (colStep v X Y) s' ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  WP.mono (vg_ok s) fun _ ⟨q, _, g, m, r, w⟩ => by
    refine ⟨⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩, g, m, r, w⟩ <;>
    obtain ⟨a, b, c, d⟩ := q i hi <;>
    simp only [laneMix, h.r0 i hi, h.r1 i hi, h.r2 i hi, h.r3 i hi, hX i hi, hY i hi] at a b c d
    · rw [a, (col_get v X Y hi).1]
    · rw [b, (col_get v X Y hi).2.1]
    · rw [c, (col_get v X Y hi).2.2.1]
    · rw [d, (col_get v X Y hi).2.2.2]

theorem round_ok {v : Work 32} {s : State} (h : RS s₀ v s) (r : Nat) :
    WP isa (round r) s (RS s₀ (Spec.Blake2.round Spec.Blake2.s M v r)) := by
  -- The column step.
  refine WP.seq (WP.mono (msgs_ok hk hm hrd h.gpr h.mem h.rd h.wr r 0)
    fun s₁ ⟨x₁, y₁, o₁, g₁, m₁, r₁, w₁⟩ => ?_)
  simp only [lane_0] at x₁ y₁
  have h₁ : Rows v s₁ := by
    have e : ∀ q : XReg, q = .xmm0 ∨ q = .xmm1 ∨ q = .xmm2 ∨ q = .xmm3 → s₁.xmm q = s.xmm q :=
      fun q hq => o₁ q (by rcases hq with rfl | rfl | rfl | rfl <;> decide)
        (by rcases hq with rfl | rfl | rfl | rfl <;> decide)
        (by rcases hq with rfl | rfl | rfl | rfl <;> decide)
        (by rcases hq with rfl | rfl | rfl | rfl <;> decide)
    exact ⟨fun i hi => by rw [dw, e _ (by simp)]; exact h.rows.r0 i hi,
      fun i hi => by rw [dw, e _ (by simp)]; exact h.rows.r1 i hi,
      fun i hi => by rw [dw, e _ (by simp)]; exact h.rows.r2 i hi,
      fun i hi => by rw [dw, e _ (by simp)]; exact h.rows.r3 i hi⟩
  refine WP.seq (WP.mono (vg_rows h₁ x₁ y₁) fun s₂ ⟨h₂, g₂, m₂, r₂, w₂⟩ => ?_)
  -- The rows rotated.
  refine WP.seq ?_
  rw [diag_eq]
  refine WP.mono (shufs_ok 0x93 0x39 0x4e (a := 3) (b := 1) (c := 2) (fun x i hi => shuf93 x hi)
    (fun x i hi => shuf39 x hi) (fun x i hi => shuf4e x hi) s₂)
    fun s₃ ⟨d0, d1, d2, d3, _, g₃, m₃, r₃, w₃⟩ => ?_
  obtain ⟨w, hw⟩ : ∃ w, w = colStep v (fun i => msgW M r 0 (2 * i)) (fun i => msgW M r 0 (2 * i + 1)) :=
    ⟨_, rfl⟩
  rw [← hw] at h₂
  -- The diagonal step.
  have gs : ∀ g, g ≠ .ecx → g ≠ .edx → s₃.gpr g = s₀.gpr g := fun g h1 h2 => by
    rw [g₃, g₂, g₁ g h1 h2]
  refine WP.seq (WP.mono (msgs_ok hk hm hrd gs (by rw [m₃, m₂, m₁]) (by rw [r₃, r₂, r₁])
    (by rw [w₃, w₂, w₁]) r 1) fun s₄ ⟨x₄, y₄, o₄, g₄, m₄, r₄, w₄⟩ => ?_)
  simp only [lane_1] at x₄ y₄
  have e₄ : ∀ q : XReg, q = .xmm0 ∨ q = .xmm1 ∨ q = .xmm2 ∨ q = .xmm3 → s₄.xmm q = s₃.xmm q :=
    fun q hq => o₄ q (by rcases hq with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hq with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hq with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hq with rfl | rfl | rfl | rfl <;> decide)
  -- Doubleword `i` holds diagonal `j = i - 1` of `w`.
  have dg : ∀ i (hi : i < 4),
      dw s₄ .xmm0 i = w[(i + 3) % 4]'(dx0 i) ∧ dw s₄ .xmm1 i = w[4 + ((i + 3) % 4 + 1) % 4]'(dx4 _) ∧
      dw s₄ .xmm2 i = w[8 + ((i + 3) % 4 + 2) % 4]'(dx8 _) ∧
      dw s₄ .xmm3 i = w[12 + ((i + 3) % 4 + 3) % 4]'(dx12 _) :=
    fun i hi => ⟨by rw [dw, e₄ _ (by simp)]; exact (d0 i hi).trans (h₂.r0 _ (Nat.mod_lt _ (by decide))),
      by rw [dw, e₄ _ (by simp)]; exact (d1 i hi).trans ((h₂.r1 i hi).trans (getElem_congr_idx (by omega))),
      by rw [dw, e₄ _ (by simp)]
         exact (d2 i hi).trans ((h₂.r2 _ (Nat.mod_lt _ (by decide))).trans (getElem_congr_idx (by omega))),
      by rw [dw, e₄ _ (by simp)]
         exact (d3 i hi).trans ((h₂.r3 _ (Nat.mod_lt _ (by decide))).trans (getElem_congr_idx (by omega)))⟩
  refine WP.seq (WP.mono (vg_ok s₄) fun s₅ ⟨q, _, g₅, m₅, r₅, w₅⟩ => ?_)
  rw [undiag_eq]
  refine WP.mono (shufs_ok 0x39 0x93 0x4e (a := 1) (b := 3) (c := 2) (fun x i hi => shuf39 x hi)
    (fun x i hi => shuf93 x hi) (fun x i hi => shuf4e x hi) s₅)
    fun s₆ ⟨u0, u1, u2, u3, _, g₆, m₆, r₆, w₆⟩ => ?_
  rw [round_eq, ← hw]
  have hq : ∀ i (hi : i < 4),
      dw s₅ .xmm0 i = (diagStep w (fun i => msgW M r 1 (2 * i)) (fun i => msgW M r 1 (2 * i + 1)))[(i + 3) % 4]'(dx0 i) ∧
      dw s₅ .xmm1 i = (diagStep w (fun i => msgW M r 1 (2 * i)) (fun i => msgW M r 1 (2 * i + 1)))[4 + ((i + 3) % 4 + 1) % 4]'(dx4 _) ∧
      dw s₅ .xmm2 i = (diagStep w (fun i => msgW M r 1 (2 * i)) (fun i => msgW M r 1 (2 * i + 1)))[8 + ((i + 3) % 4 + 2) % 4]'(dx8 _) ∧
      dw s₅ .xmm3 i = (diagStep w (fun i => msgW M r 1 (2 * i)) (fun i => msgW M r 1 (2 * i + 1)))[12 + ((i + 3) % 4 + 3) % 4]'(dx12 _) := fun i hi => by
    obtain ⟨a, b, c, d⟩ := q i hi
    obtain ⟨l0, l1, l2, l3⟩ := dg i hi
    obtain ⟨e0, e1, e2, e3⟩ := diag_get w (fun i => msgW M r 1 (2 * i)) (fun i => msgW M r 1 (2 * i + 1))
      (Nat.mod_lt (i + 3) (show 0 < 4 by decide))
    simp only [laneMix, l0, l1, l2, l3, x₄ i hi, y₄ i hi] at a b c d
    exact ⟨a.trans e0.symm, b.trans e1.symm, c.trans e2.symm, d.trans e3.symm⟩
  refine ⟨⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩,
    fun g h1 h2 => by rw [g₆, g₅, g₄ g h1 h2], by rw [m₆, m₅, m₄], by rw [r₆, r₅, r₄],
    by rw [w₆, w₅, w₄]⟩
  · rw [u0 i hi, (hq _ (Nat.mod_lt _ (by decide))).1]
    exact getElem_congr_idx (by omega)
  · rw [u1 i hi, (hq i hi).2.1]
    exact getElem_congr_idx (by omega)
  · rw [u2 i hi, (hq _ (Nat.mod_lt _ (by decide))).2.2.1]
    exact getElem_congr_idx (by omega)
  · rw [u3 i hi, (hq _ (Nat.mod_lt _ (by decide))).2.2.2]
    exact getElem_congr_idx (by omega)

theorem rounds_ok {v : Work 32} {s : State} (h : RS s₀ v s) (n : Nat) :
    WP isa (rounds n) s (RS s₀ ((List.range n).foldl (Spec.Blake2.round Spec.Blake2.s M) v)) := by
  induction n with
  | zero => exact WP.block_nil h
  | succ n ih =>
    refine WP.seq (WP.mono ih fun s' h' => ?_)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact round_ok hk hm hrd h' n

end

end VG.Proof.Blake2.X86.CompressS
