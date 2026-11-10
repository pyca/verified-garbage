module

public import VerifiedGarbage.Proof.Bignum.X86.PrivPre.Body
public import VerifiedGarbage.Proof.Bignum.X86.PrivPre.Prime
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeRt.Copy
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Top
public import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # `vg_rsa_private_precompute` on x86: the factors' values to `pre`

`copyPrime j i skip`: the `8 w_p` bytes of the working space's wide slot `j`,
for the factor of argument `i`, to `pre` at `dstOff s skip`, after `n`'s
values and, for `q`, `p`'s (`copyPrime_ok`).
-/

@[expose] public section
namespace VG.Proof.Bignum.X86.PrivPre
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Bignum.X86.PrivPre (shl primeWords dstAt slotSrc copyPrime copyLoop incoming)
open VG.Impl.Bignum.X86.PublicRt (argAt)

section
variable {s t : State} {is : List Instr} {Q : State → Prop}

/-- `j` additions of `r'` to `r`. -/
theorem addRep_ok {r r' : Reg} (hne : r ≠ r') : ∀ (j : Nat) {t : State},
    (∀ u, Keeps [r] t u → u.mem = t.mem →
      (u.gpr r).toNat = ((t.gpr r).toNat + j * (t.gpr r').toNat) % 2 ^ 32 → WP isa (.block is) u Q) →
    WP isa (.block (List.replicate j (.alu .add r (.reg r')) ++ is)) t Q
  | 0, t, k => by
    simpa using k t (Keeps.refl _ _) rfl (by simp [Nat.mod_eq_of_lt (t.gpr r).isLt])
  | j + 1, t, k => by
    rw [List.replicate_succ, List.cons_append]
    refine wp_add fun u₁ U₁ _ => addRep_ok hne j fun u K m e =>
      k u (U₁.keeps.trans K) (by rw [m, U₁.mem]) ?_
    rw [e, U₁.gpr, U₁.other r' (Ne.symm hne), BitVec.toNat_add, Nat.mod_add_mod, Nat.succ_mul]
    congr 1; omega

theorem argAt_incoming (i : Nat) :
    argAt (Impl.Bignum.X86.PrivPre.frameBytes / 4) i = incoming i := by
  simp only [argAt, incoming, Impl.Bignum.X86.PrivPre.stackAt, Impl.Mont.X86.at_,
    Impl.Bignum.X86.PrivPre.frameBytes, MemOp.mk.injEq, true_and]
  omega

/-- `primeWords`, at the wrapper's frame: `r = w_p` for the length of argument `i`. -/
theorem primeWordsF_ok (A : PPABI s) (B : Body s t) {i : Nat} (hi : i < 10) (h1 : 1 ≤ (arg s i).toNat)
    (h2 : (arg s i).toNat < 2 ^ 32 - 8) {r r₂ : Reg} (hr : r ≠ r₂)
    (k : ∀ u, Keeps [r, r₂] t u → u.mem = t.mem → (u.gpr r).toNat = Spec.Rsa.primeWords (arg s i).toNat →
      WP isa (.block is) u Q) :
    WP isa (.block (primeWords (Impl.Bignum.X86.PrivPre.frameBytes / 4) i r r₂ ++ is)) t Q := by
  simp only [primeWords, List.cons_append, List.nil_append]
  rw [argAt_incoming]
  refine wp_movS (B.readArg A hi) fun u₁ a₁ _ => ?_
  refine wp_addS rfl fun u₂ a₂ _ => wp_shr (by decide) fun u₃ a₃ _ => wp_movS rfl fun u₄ a₄ _ => ?_
  refine wp_subS rfl fun u₅ a₅ _ => wp_shr (by decide) fun u₆ a₆ _ => wp_addS rfl fun u₇ a₇ _ => ?_
  refine k u₇ ?_ ?_ ?_
  · exact ((((((a₁.keeps.mono (by simp)).trans (a₂.keeps.mono (by simp))).trans (a₃.keeps.mono (by simp))).trans
      (a₄.keeps.mono (by simp))).trans (a₅.keeps.mono (by simp))).trans (a₆.keeps.mono (by simp))).trans
      (a₇.keeps.mono (by simp))
  · rw [a₇.mem, a₆.mem, a₅.mem, a₄.mem, a₃.mem, a₂.mem, a₁.mem]
  · have r₁ : u₁.gpr r = BitVec.ofNat 32 (arg s i).toNat := by rw [a₁.gpr, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have r₃ : u₃.gpr r = (BitVec.ofNat 32 (arg s i).toNat + 7) >>> 3 := by rw [a₃.gpr, a₂.gpr, r₁]
    have e₇ : u₇.gpr r = u₃.gpr r + (u₃.gpr r - 2) >>> 31 := by
      rw [a₇.gpr, a₆.other _ hr, a₅.other _ hr, a₄.other _ hr, a₆.gpr, a₅.gpr, a₄.gpr]
    rw [e₇, r₃]
    exact primeWords_val _ h1 h2

/-- `pre`'s offset of a factor's values: after `n`'s, and the factor of
argument `i`'s if `some i`. -/
def dstOff (s : State) : Option Nat → Nat
  | none => 16 * Spec.Rsa.modulusWords (arg s 3).toNat
  | some i => 16 * Spec.Rsa.modulusWords (arg s 3).toNat + 8 * Spec.Rsa.primeWords (arg s i).toNat

/-- `16 ⌈n_len / 8⌉`, as `r := n_len; r += 7; r >>= 3; shl r 4` computes it. -/
theorem width16_ok (A : PPABI s) (B : Body s t) {r : Reg}
    (k : ∀ u, Keeps [r] t u → u.mem = t.mem → (u.gpr r).toNat = 16 * Spec.Rsa.modulusWords (arg s 3).toNat →
      WP isa (.block is) u Q) :
    WP isa (.block ([.mov r (.mem (incoming 3)), .alu .add r (.imm 7), .shift .shr r 3] ++ shl r 4 ++ is)) t Q := by
  have l := A.lengths
  simp only [Spec.Rsa.lenValid] at l
  simp only [List.cons_append, List.nil_append]
  refine wp_movS (B.readArg A (by decide)) fun u₁ a₁ _ => wp_addi fun u₂ a₂ => wp_shr (by decide)
    fun u₃ a₃ _ => shl_ok 4 fun u₄ K₄ m₄ e₄ => k u₄ ?_ ?_ ?_
  · exact (((a₁.keeps.trans a₂.keeps).trans a₃.keeps).trans K₄)
  · rw [m₄, a₃.mem, a₂.mem, a₁.mem]
  · rw [e₄, a₃.gpr, a₂.gpr, a₁.gpr]
    simp only [Spec.Rsa.modulusWords, BitVec.toNat_ushiftRight, BitVec.toNat_add, Nat.shiftRight_eq_div_pow]
    rw [show (7 : BitVec 32).toNat = 7 from rfl, Nat.mod_eq_of_lt (a := (arg s 3).toNat + 7) (by omega)]
    omega

theorem dstAt_ok (A : PPABI s) (B : Body s t) {skip : Option Nat} (hs : skip = none ∨ skip = some 5)
    (k : ∀ u, Body s u → Keeps [.eax, .ecx, .ebp] t u → u.mem = t.mem →
      PtrAt u (argumentPointer s 0) .ebp (dstOff s skip) → WP isa (.block is) u Q) :
    WP isa (.block (dstAt skip ++ is)) t Q := by
  have l := A.lengths
  simp only [Spec.Rsa.lenValid] at l
  have p0 : (argumentPointer s 0).toNat = (arg s 0).toNat := by
    simp only [argumentPointer, BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := (arg s 0).isLt; omega)
  simp only [dstAt, List.append_assoc]
  refine width16_ok A B fun u₁ K₁ m₁ e₁ => ?_
  have B₁ : Body s u₁ := B.next (K₁.1 _ (by decide)) K₁.2.1 K₁.2.2 (by rw [m₁]; exact Frame.refl _ _)
  simp only [List.cons_append]
  refine wp_addS (B₁.readArg A (by decide)) fun u₂ a₂ _ => ?_
  have B₂ : Body s u₂ := B₁.next (a₂.other _ (by decide)) a₂.rd a₂.wr (by rw [a₂.mem]; exact Frame.refl _ _)
  have e₂ : (u₂.gpr .ebp).toNat = ((arg s 0).toNat + 16 * Spec.Rsa.modulusWords (arg s 3).toNat) % 2 ^ 32 := by
    rw [a₂.gpr, BitVec.toNat_add, e₁]; omega
  have K₂ : Keeps [.eax, .ecx, .ebp] t u₂ := ((K₁.mono (by simp)).trans (a₂.keeps.mono (by simp)))
  rcases hs with rfl | rfl
  · exact k u₂ B₂ K₂ (by rw [a₂.mem, m₁]) (by rw [PtrAt, e₂, p0]; rfl)
  · have h1 := A.pPositive
    have h2 := A.pLength
    refine primeWordsF_ok A B₂ (by decide) h1 (by omega) (r := .eax) (r₂ := .ecx) (by decide)
      fun u₃ K₃ m₃ e₃ => shl_ok 3 fun u₄ K₄ m₄ e₄ => wp_add fun u₅ a₅ _ => k u₅ ?_ ?_ ?_ ?_
    · exact B₂.next ((a₅.other _ (by decide)).trans ((K₄.1 _ (by decide)).trans (K₃.1 _ (by decide))))
        (by rw [a₅.rd, K₄.2.1, K₃.2.1]) (by rw [a₅.wr, K₄.2.2, K₃.2.2])
        (by rw [a₅.mem, m₄, m₃]; exact Frame.refl _ _)
    · exact ((K₂.trans (K₃.mono (by simp))).trans (K₄.mono (by simp))).trans (a₅.keeps.mono (by simp))
    · rw [a₅.mem, m₄, m₃, a₂.mem, m₁]
    · have pw : Spec.Rsa.primeWords (arg s 5).toNat ≤ 128 := by
        simp only [Spec.Rsa.primeWords, Spec.Rsa.modulusWords]; omega
      rw [PtrAt, a₅.gpr, BitVec.toNat_add, K₄.1 _ (by decide), K₃.1 _ (by decide), e₂, e₄, e₃, p0]
      simp only [dstOff]
      omega

theorem p8_toNat : (argumentPointer s 8).toNat = (arg s 8).toNat := by
  simp only [argumentPointer, BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := (arg s 8).isLt; omega)

theorem p0_toNat : (argumentPointer s 0).toNat = (arg s 0).toNat := by
  simp only [argumentPointer, BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := (arg s 0).isLt; omega)

theorem slotSrc_ok (A : PPABI s) (B : Body s t) {j : Nat}
    (k : ∀ u, Keeps [.ecx, .esi] t u → u.mem = t.mem →
      PtrAt u (argumentPointer s 8) .esi (CrtRt.lo (arg s 3).toNat (.slot .wide j)) → WP isa (.block is) u Q) :
    WP isa (.block (slotSrc j ++ is)) t Q := by
  have l := A.lengths
  simp only [Spec.Rsa.lenValid] at l
  simp only [slotSrc, List.append_assoc]
  refine width16_ok A B (r := .ecx) fun u₁ K₁ m₁ e₁ => ?_
  have B₁ : Body s u₁ := B.next (K₁.1 _ (by decide)) K₁.2.1 K₁.2.2 (by rw [m₁]; exact Frame.refl _ _)
  simp only [List.cons_append]
  refine wp_addi fun u₂ a₂ => ?_
  have B₂ : Body s u₂ := B₁.next (a₂.other _ (by decide)) a₂.rd a₂.wr (by rw [a₂.mem]; exact Frame.refl _ _)
  refine wp_movS (B₂.readArg A (by decide)) fun u₃ a₃ _ => wp_addi fun u₄ a₄ =>
    addRep_ok (r := .esi) (r' := .ecx) (by decide) j fun u₅ K₅ m₅ e₅ => k u₅ ?_ ?_ ?_
  · exact ((((K₁.mono (by simp)).trans (a₂.keeps.mono (by simp))).trans (a₃.keeps.mono (by simp))).trans
      (a₄.keeps.mono (by simp))).trans (K₅.mono (by simp))
  · rw [m₅, a₄.mem, a₃.mem, a₂.mem, m₁]
  · have ecx : (u₄.gpr .ecx).toNat = CrtRt.st (arg s 3).toNat .wide := by
      rw [a₄.other _ (by decide), a₃.other _ (by decide), a₂.gpr, BitVec.toNat_add, e₁]
      simp only [CrtRt.st, CrtRt.bc, CrtRt.mw, Spec.Rsa.modulusWords]
      rw [show (32 : BitVec 32).toNat = 32 from rfl]
      omega
    have esi : (u₄.gpr .esi).toNat = ((arg s 8).toNat + Impl.Bignum.X86.CrtRt.numBase) % 2 ^ 32 := by
      rw [a₄.gpr, a₃.gpr, BitVec.toNat_add, BitVec.toNat_ofNat]
      simp only [Impl.Bignum.X86.CrtRt.numBase, Nat.reducePow, Nat.reduceMod]
    rw [PtrAt, e₅, ecx, esi, p8_toNat]
    simp only [CrtRt.lo]
    omega

theorem copyPrime_ok (A : PPABI s) (B : Body s t) {j i : Nat} {skip : Option Nat} (hj : j ≤ 17)
    (hi : i = 5 ∨ i = 7) (hs : skip = none ∨ skip = some 5)
    (hfit : dstOff s skip + 8 * Spec.Rsa.primeWords (arg s i).toNat ≤ (arg s 1).toNat * 8) :
    WP isa (copyPrime j i skip) t fun u => Body s u ∧ Keeps [.eax, .ecx, .ebp, .esi] t u ∧
      Outside (argumentPointer s 0) (dstOff s skip) (4 * (2 * Spec.Rsa.primeWords (arg s i).toNat)) t.mem u.mem ∧
      val32 u.mem (argumentPointer s 0) (dstOff s skip) (2 * Spec.Rsa.primeWords (arg s i).toNat) =
        val32 t.mem (argumentPointer s 8) (CrtRt.lo (arg s 3).toNat (.slot .wide j))
          (2 * Spec.Rsa.primeWords (arg s i).toNat) := by
  have l := A.lengths
  simp only [Spec.Rsa.lenValid] at l
  have hL : 1 ≤ (arg s i).toNat ∧ (arg s i).toNat < (arg s 3).toNat := by
    rcases hi with rfl | rfl
    · exact ⟨A.pPositive, A.pLength⟩
    · exact ⟨A.qPositive, A.qLength⟩
  have pw : Spec.Rsa.primeWords (arg s i).toNat ≤ Spec.Rsa.modulusWords (arg s 3).toNat := by
    simp only [Spec.Rsa.primeWords, Spec.Rsa.modulusWords]; omega
  have nd := CrtRt.need_le l.1 A.scratchLength
  unfold copyPrime
  rw [show dstAt skip ++ slotSrc j ++ primeWords (Impl.Bignum.X86.PrivPre.frameBytes / 4) i .ecx .eax ++ shl .ecx 3 =
    dstAt skip ++ (slotSrc j ++ (primeWords (Impl.Bignum.X86.PrivPre.frameBytes / 4) i .ecx .eax ++
      (shl .ecx 3 ++ []))) by simp]
  refine WP.seq (dstAt_ok A B hs fun u₁ B₁ K₁ m₁ P₁ => slotSrc_ok A B₁ fun u₂ K₂ m₂ P₂ => ?_)
  have B₂ : Body s u₂ := B₁.next (K₂.1 _ (by decide)) K₂.2.1 K₂.2.2 (by rw [m₂]; exact Frame.refl _ _)
  refine primeWordsF_ok A B₂ (by rcases hi with rfl | rfl <;> decide) hL.1 (by omega) (r := .ecx) (r₂ := .eax)
    (by decide) fun u₃ K₃ m₃ e₃ => shl_ok 3 fun u₄ K₄ m₄ e₄ => WP.block_nil ?_
  have K : Keeps [.eax, .ecx, .ebp, .esi] t u₄ :=
    (((K₁.mono (by simp)).trans (K₂.mono (by simp))).trans (K₃.mono (by simp))).trans (K₄.mono (by simp))
  have M : u₄.mem = t.mem := by rw [m₄, m₃, m₂, m₁]
  have hw : Ws u₄ (argumentPointer s 8) ((arg s 9).toNat * 8) :=
    ⟨by rw [K.2.2, B.wr, A.wr]; simp, by rw [p8_toNat]; exact A.wsBound⟩
  have hpw : InRegions u₄.wr (argumentPointer s 0) ((arg s 1).toNat * 8) :=
    ⟨preR s, by rw [K.2.2, B.wr, A.wr]; simp, Region.contains_self _ _⟩
  have hesi : PtrAt u₄ (argumentPointer s 8) .esi (CrtRt.lo (arg s 3).toNat (.slot .wide j)) := by
    rw [PtrAt, K₄.1 _ (by decide), K₃.1 _ (by decide)]; exact P₂
  have hebp : PtrAt u₄ (argumentPointer s 0) .ebp (dstOff s skip) := by
    rw [PtrAt, K₄.1 _ (by decide), K₃.1 _ (by decide), K₂.1 _ (by decide)]; exact P₁
  have hecx : (u₄.gpr .ecx).toNat = 4 * (2 * Spec.Rsa.primeWords (arg s i).toNat) := by
    rw [e₄, e₃]; simp only [Spec.Rsa.modulusWords] at pw; omega
  refine WP.mono (PrecomputeRt.copyOutLoop_ok hw hpw (by rw [p0_toNat]; exact A.preBound) A.preWs
    (by simp only [Spec.Rsa.primeWords]; omega) ?_ (by omega) hesi hebp hecx) fun u ⟨O, V, Ku⟩ => ?_
  · simp only [CrtRt.need, CrtRt.lo, CrtRt.st, CrtRt.bc, CrtRt.mw, Impl.Bignum.X86.CrtRt.numBase] at nd ⊢
    simp only [Spec.Rsa.modulusWords] at pw nd ⊢
    have : j * (2 * (8 * (((arg s 3).toNat + 7) / 8)) + 32) ≤ 17 * (2 * (8 * (((arg s 3).toNat + 7) / 8)) + 32) :=
      Nat.mul_le_mul_right _ hj
    omega
  · rw [M] at O V
    refine ⟨B.next ((Ku.1 _ (by decide)).trans (K.1 _ (by decide))) (Ku.2.1.trans K.2.1) (Ku.2.2.trans K.2.2)
      ((VG.Proof.Bignum.outside_frame O (by omega)).sub fun r hr => ?_), K.trans Ku, O, V⟩
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨preR s, by simp, Offset.sub_base _ (by omega)⟩

end
end VG.Proof.Bignum.X86.PrivPre
