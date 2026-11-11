module

public import VerifiedGarbage.Proof.MlKem.X86_64.RowEY
public import VerifiedGarbage.Proof.MlKem.PolyW
import VerifiedGarbage.Proof.MlKem.X86_64.YNtt
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on x86-64: a row of products of polynomials of `u16`s (`rowEY16`)

`rowLdY16` loads the 32 coefficients of a block of a polynomial of `u16`s
(`PolyIsW 16`) as `rowLdY` loads those of `u32`s, as pairs: two loads, and
`vpermq` with `0xD8`, which brings quadwords `0, 2` of the block to lane 0
and `1, 3` to lane 1 (`word_permD8`), each doubleword a pair of
coefficients already. So `rowEY16` is `rowEg` of `FRep.u16` (`rowEY16_wo`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Proof.MlKem VG.Spec.MlKem

/-- Word `i` of lane `l` after `vpermq` with `0xD8` of the 32 bytes at `a`:
word `8 (i / 4) + 4 l + i % 4` of them. -/
theorem word_permD8 (m : Mem) (a : Addr) {l i : Nat} (hl : l < 2) (hi : i < 8) :
    word (if l = 0 then XBinOp.eval .punpcklqdq (m.readW (a + BitVec.ofNat 64 (16 * 0)) 128)
        (m.readW (a + BitVec.ofNat 64 (16 * 1)) 128)
      else XBinOp.eval .punpckhqdq (m.readW (a + BitVec.ofNat 64 (16 * 0)) 128)
        (m.readW (a + BitVec.ofNat 64 (16 * 1)) 128)) i =
      m.readW (a + BitVec.ofNat 64 (2 * (8 * (i / 4) + 4 * l + i % 4))) 16 := by
  have e : ∀ t k, k < 8 → word (m.readW (a + BitVec.ofNat 64 (16 * t)) 128) k =
      m.readW (a + BitVec.ofNat 64 (2 * (8 * t + k))) 16 := fun t k hk => by
    rw [word_readW _ _ hk, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact congrArg (fun x => m.readW (a + BitVec.ofNat 64 x) 16) (by omega)
  rcases lane01 hl with rfl | rfl
  · rw [ite_eq_left rfl, word_punpcklqdq (hi := hi)]
    split
    · rw [e 0 i (by omega)]; exact congrArg (fun x => m.readW (a + BitVec.ofNat 64 x) 16) (by omega)
    · rw [e 1 (i - 4) (by omega)]; exact congrArg (fun x => m.readW (a + BitVec.ofNat 64 x) 16) (by omega)
  · rw [ite_eq_right (by decide), word_punpckhqdq (hi := hi)]
    split
    · rw [e 0 (4 + i) (by omega)]; exact congrArg (fun x => m.readW (a + BitVec.ofNat 64 x) 16) (by omega)
    · rw [e 1 i hi]; exact congrArg (fun x => m.readW (a + BitVec.ofNat 64 x) 16) (by omega)

/-- `rowLdY16`: the coefficients of block `b` of `F` (`u16`s at `fB + o j`),
as pairs in `vbase`'s order. -/
theorem ld16_ok {o : Nat} {fB : Addr} {F : Poly} {b j : Nat} {s : State} (hb : b < 8)
    (hrsi : s.gpr .rsi = fB + BitVec.ofNat 64 (64 * b)) (hF : PolyIsW 16 s.mem (fB + BitVec.ofNat 64 (o * j)) F)
    (rF : InRegions (s.rd ++ s.wr) (fB + BitVec.ofNat 64 (o * j)) 512) :
    WP isa (.block (rowLdY16 o j)) s fun s' =>
      (∀ l < 2, PLanes (s'.lane .xmm0 l) (fun i => F[2 * pairY b l i]!) (fun i => F[2 * pairY b l i + 1]!) ∧
        PLanes (s'.lane .xmm1 l) (fun i => F[2 * pairY b l (4 + i)]!) (fun i => F[2 * pairY b l (4 + i) + 1]!)) ∧
      YOnly [.xmm0, .xmm1, .xmm8, .xmm9] s s' := by
  have ad : ∀ t, s.gpr .rsi + BitVec.ofNat 64 (o * j + 32 * t) =
      fB + BitVec.ofNat 64 (o * j) + BitVec.ofNat 64 (64 * b + 32 * t) := fun t => by
    rw [hrsi]; simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact congrArg (fB + ·) (congrArg _ (by omega))
  have r : ∀ t < 2, InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 (o * j + 32 * t)) 32 := fun t ht => by
    rw [ad]; exact CallLay.inRegions_sub rF (by omega) (by omega)
  simp only [rowLdY16]
  rw [show ∀ (a b c d : Instr), [a, b, c, d] = [a] ++ ([b] ++ ([c] ++ [d])) from fun _ _ _ _ => rfl]
  rw [WP.block_append_iff]
  refine WP.mono (yld_ok (p := .rsi) (off := o * j) (d := .xmm0) (by simpa using r 0 (by decide)))
    fun s1 ⟨L1, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (yld_ok (p := .rsi) (off := o * j + 32) (d := .xmm1)
    (by rw [o1.rd, o1.wr, o1.gpr]; simpa using r 1 (by decide))) fun s2 ⟨L2, o2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ypermq_ok (d := .xmm0) (r := .xmm0) s2) fun s3 ⟨P3a, P3b, o3⟩ => ?_
  refine WP.mono (ypermq_ok (d := .xmm1) (r := .xmm1) s3) fun s4 ⟨P4a, P4b, o4⟩ =>
    ⟨fun l hl => ?_, ((((o1.trans o2).trans o3).trans o4)).mono (by simp)⟩
  -- the bytes of the block, in the memory the loads read
  have m1 : s1.mem = s.mem := o1.mem
  have lane0 : ∀ l' < 2, s2.lane .xmm0 l' =
      s.mem.readW (fB + BitVec.ofNat 64 (o * j) + BitVec.ofNat 64 (64 * b + 32 * 0) + BitVec.ofNat 64 (16 * l')) 128 :=
    fun l' hl' => by rw [o2.lane _ (by decide) l' hl', L1 l' hl', ← ad 0, Nat.mul_zero, Nat.add_zero]
  have lane1 : ∀ l' < 2, s2.lane .xmm1 l' =
      s.mem.readW (fB + BitVec.ofNat 64 (o * j) + BitVec.ofNat 64 (64 * b + 32 * 1) + BitVec.ofNat 64 (16 * l')) 128 :=
    fun l' hl' => by rw [L2 l' hl', o1.gpr, m1, ← ad]
  have X : s4.lane .xmm0 l = if l = 0 then XBinOp.eval .punpcklqdq (s2.lane .xmm0 0) (s2.lane .xmm0 1)
      else XBinOp.eval .punpckhqdq (s2.lane .xmm0 0) (s2.lane .xmm0 1) := by
    rw [o4.lane _ (by decide) l hl]
    rcases lane01 hl with rfl | rfl
    · rw [P3a, ite_eq_left rfl]
    · rw [P3b, ite_eq_right (by decide)]
  have Y : s4.lane .xmm1 l = if l = 0 then XBinOp.eval .punpcklqdq (s2.lane .xmm1 0) (s2.lane .xmm1 1)
      else XBinOp.eval .punpckhqdq (s2.lane .xmm1 0) (s2.lane .xmm1 1) := by
    rcases lane01 hl with rfl | rfl
    · rw [P4a, ite_eq_left rfl, o3.lane _ (by decide) 0 (by decide), o3.lane _ (by decide) 1 (by decide)]
    · rw [P4b, ite_eq_right (by decide), o3.lane _ (by decide) 0 (by decide), o3.lane _ (by decide) 1 (by decide)]
  -- the coefficients of the words
  have cw : ∀ t < 2, ∀ i < 8, (word (if l = 0 then
        XBinOp.eval .punpcklqdq
          (s.mem.readW (fB + BitVec.ofNat 64 (o * j) + BitVec.ofNat 64 (64 * b + 32 * t) + BitVec.ofNat 64 (16 * 0)) 128)
          (s.mem.readW (fB + BitVec.ofNat 64 (o * j) + BitVec.ofNat 64 (64 * b + 32 * t) + BitVec.ofNat 64 (16 * 1)) 128)
      else XBinOp.eval .punpckhqdq
          (s.mem.readW (fB + BitVec.ofNat 64 (o * j) + BitVec.ofNat 64 (64 * b + 32 * t) + BitVec.ofNat 64 (16 * 0)) 128)
          (s.mem.readW (fB + BitVec.ofNat 64 (o * j) + BitVec.ofNat 64 (64 * b + 32 * t) + BitVec.ofNat 64 (16 * 1)) 128))
        i).toNat = (F[32 * b + 8 * ((8 * t + i) / 4) + 4 * l + (8 * t + i) % 4]!).val := fun t ht i hi => by
    rw [word_permD8 _ _ hl hi, BitVec.add_assoc, ← BitVec.ofNat_add,
      show 64 * b + 32 * t + 2 * (8 * (i / 4) + 4 * l + i % 4) =
        2 * (32 * b + 8 * ((8 * t + i) / 4) + 4 * l + (8 * t + i) % 4) by omega,
      ← coeffAtW16_eq, polyIsW_toNat hF (by rw [n_eq]; omega)]
  rw [X, Y, lane0 0 (by decide), lane0 1 (by decide), lane1 0 (by decide), lane1 1 (by decide)]
  refine ⟨fun i hi => ⟨?_, ?_⟩, fun i hi => ⟨?_, ?_⟩⟩
  · refine (cw 0 (by decide) (2 * i) (by omega)).trans (congrArg (fun k : Nat => (F[k]!).val) ?_)
    unfold pairY; omega
  · refine (cw 0 (by decide) (2 * i + 1) (by omega)).trans (congrArg (fun k : Nat => (F[k]!).val) ?_)
    unfold pairY; omega
  · refine (cw 1 (by decide) (2 * i) (by omega)).trans (congrArg (fun k : Nat => (F[k]!).val) ?_)
    unfold pairY; omega
  · refine (cw 1 (by decide) (2 * i + 1) (by omega)).trans (congrArg (fun k : Nat => (F[k]!).val) ?_)
    unfold pairY; omega

/-- The polynomials of `u16`s (`PolyIsW 16`), `o` bytes apart. -/
def FRep.u16 (o : Nat) : FRep o where
  ld := rowLdY16 o
  stv := 64
  st := 64
  sz := 512
  Is := PolyIsW 16
  hst := by decide
  frame := fun hf _ _ hd h => polyIsW16_frame hf hd h
  ok := fun hb hrsi hF rF => ld16_ok hb hrsi hF rF

/-- What `rowEY16` may write: `rax` (the constants), `rcx` (the count) and the
pointers. -/
theorem rowEY16_wo {k : Nat} (hk : k = 3 ∨ k = 4) :
    writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8] (rowEY16 (512 * k) k) = true := by
  rcases hk with rfl | rfl <;> decide +kernel

end VG.Proof.MlKem.X86_64
