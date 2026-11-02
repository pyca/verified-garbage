module

public import VerifiedGarbage.Proof.Dsa.X86.PowOuts
public import VerifiedGarbage.Impl.Dsa.X86.Pow
import VerifiedGarbage.Proof.Dsa.X86.PowMul
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Mont.X86.ExponentMask
import VerifiedGarbage.Proof.Mont.X86.PowerInit
import VerifiedGarbage.Proof.Mont.X86.ShiftDown
import VerifiedGarbage.Proof.Dsa.Arithmetic
public import VerifiedGarbage.Proof.Rsa.MontMulContract

/-! # The pieces of DSA's exponentiation, between calls

`St s₀ t`: from the exponentiation's start `s₀`, `t` has the context, the
registers but `powerClob` of `s₀` (`esp` and `edi` among them), and changes
only the context's own bytes (`coreRanges`) and the 96 bytes of stack below
`esp`, which lie apart from the working space. Each piece keeps it, and says
what it writes: a multiplication by a call (`mulSt_ok`), one in a slot
(`oneSt_ok`), the exponent's low bit as a mask (`maskSt_ok`), the masked
selection (`selectSt_ok`) and the exponent's shift (`shiftSt_ok`).
-/

@[expose] public section

namespace VG.Proof.Dsa.X86.Pow

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Dynamic VG.Impl.Dsa.X86.Pow
open VG.Proof.Rsa.MontMul (scratchBytes)

/-- The bytes the exponentiation's core may change: the inverse and the mask
in the header, and every slot but the modulus's. -/
def coreRanges (n : Nat) : List (Nat × Nat) := [(0, 8), (slot n 1, contextBytes n - slot n 1)]

structure St (n m size : Nat) (base : Addr) (s₀ t : State) : Prop where
  ctx : Context n m base size t
  room : CallRoom (s₀.gpr .esp) base size
  keeps : Keeps powerClob s₀ t
  mem : OutsS base (s₀.gpr .esp) (coreRanges n) s₀.mem t.mem

section
variable {n m size : Nat} {base : Addr} {s₀ : State}

theorem St.esp {t : State} (S : St n m size base s₀ t) : t.gpr .esp = s₀.gpr .esp := S.keeps.1 _ (by decide)

theorem St.room' {t : State} (S : St n m size base s₀ t) : CallRoom (t.gpr .esp) base size := by
  rw [S.esp]; exact S.room

/-- Ranges within the core's. -/
theorem OutsS.core {sp : BitVec 32} {rs : List (Nat × Nat)} {m₁ m₂ : Mem}
    (h : OutsS base sp rs m₁ m₂) (hr : ∀ r ∈ rs, ∃ c ∈ coreRanges n, c.1 ≤ r.1 ∧ r.1 + r.2 ≤ c.1 + c.2) :
    OutsS base sp (coreRanges n) m₁ m₂ :=
  h.widen fun y hy r hr' => by
    obtain ⟨c, hc, h₁, h₂⟩ := hr r hr'
    have := hy c hc
    omega

/-- A state after a piece that keeps the context and changes only ranges within the core's. -/
theorem St.next {t u : State} (S : St n m size base s₀ t) (C : Context n m base size u)
    (K : Keeps powerClob t u) {rs : List (Nat × Nat)} (O : OutsS base (s₀.gpr .esp) rs t.mem u.mem)
    (hr : ∀ r ∈ rs, ∃ c ∈ coreRanges n, c.1 ≤ r.1 ∧ r.1 + r.2 ≤ c.1 + c.2) : St n m size base s₀ u :=
  ⟨C, S.room, S.keeps.trans K, S.mem.trans (O.core hr)⟩

theorem slot_lin (n i : Nat) : slot n i = 64 + i * (16 * n + 8) := rfl

/-- Slot `i` (4 to 8) keeps its value when a call writes slot `o` (4 to 7). -/
theorem mul_slot_keep {sp : BitVec 32} {m₁ m₂ : Mem} {o i k : Nat}
    (O : OutsS base sp [(slot n o, 8 * n), (calleeScratch n, scratchBytes n)] m₁ m₂)
    (R : CallRoom sp base size) (nw : base.toNat + size ≤ 2 ^ 32) (cb : contextBytes n ≤ size) (hn : 2 ≤ n)
    (hi4 : 4 ≤ i) (hi : i < 9) (hio : i ≠ o) (hk : k ≤ 2 * n) :
    val32 m₂ base (slot n i) k = val32 m₁ base (slot n i) k := by
  have sep := slot_sep (n := n) hio
  have b := slot_bound (n := n) hi
  have l4 := Nat.mul_le_mul_right (16 * n + 8) hi4
  simp only [stride] at sep b
  refine O.val32 R nw (fun r hr => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · dsimp only; omega
  · simp only [calleeScratch, scratchBytes, slot_lin] at b ⊢; omega

theorem mulSt_ok {t : State} {o a b : Nat} (S : St n m size base s₀ t) (hn : 2 ≤ n)
    (ho : 4 ≤ o) (ho7 : o ≤ 7) (ha : 4 ≤ a) (ha7 : a ≤ 7) (hb : 4 ≤ b) (hb7 : b ≤ 7)
    (hB : wordsVal t.mem base (slot n b) n < m) :
    WP isa (VG.Impl.Dsa.X86.Pow.mul n o a b) t fun u => St n m size base s₀ u ∧ u.gpr .esi = t.gpr .esi ∧
      wordsVal u.mem base (slot n o) n < m ∧
      wordsVal u.mem base (slot n o) n * 2 ^ (64 * n) % m =
        wordsVal t.mem base (slot n a) n * wordsVal t.mem base (slot n b) n % m ∧
      (∀ i, 4 ≤ i → i < 9 → i ≠ o → ∀ k ≤ 2 * n, val32 u.mem base (slot n i) k = val32 t.mem base (slot n i) k) ∧
      u.mem.readW (off base 4) 32 = t.mem.readW (off base 4) 32 := by
  have h := S.ctx
  have cb := h.size_le
  have nw := h.scr.nowrap
  refine WP.mono (mul_ok h S.room' hn ho ho7 ha ha7 hb hb7 hB) fun u ⟨cs, rd, wr, O, L, V⟩ => ?_
  have K : Keeps powerClob t u :=
    ⟨fun r hr => cs r (by revert hr; cases r <;> simp [powerClob, calleeSaved]), rd, wr⟩
  have lo := Nat.mul_le_mul_right (16 * n + 8) ho
  have hi := Nat.mul_le_mul_right (16 * n + 8) ho7
  have C : Context n m base size u := Context.outsS_keep h S.room' K (by decide) (by decide) O
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [calleeScratch, slot_lin] <;> omega)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [calleeScratch, slot_lin] <;> omega)
  rw [S.esp] at O
  refine ⟨S.next C K O fun r hr => ⟨(slot n 1, contextBytes n - slot n 1), List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_⟩,
    cs .esi (by decide), L, V, fun i hi4 hi hio k hk => mul_slot_keep O S.room nw cb hn hi4 hi hio hk,
    O.readW32 S.room nw (fun r hr => ?_) (by simp only [contextBytes, slot_lin] at cb; omega)⟩
  rotate_left
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [calleeScratch, slot_lin] <;> omega
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  have b8 := slot_bound (n := n) (i := 8) (by decide)
  simp only [stride] at b8
  rcases hr with rfl | rfl <;> simp only [contextBytes, calleeScratch, scratchBytes, slot_lin] at b8 ⊢ <;> omega

/-- The core's second range holds slots 1 to 8. -/
theorem in_core {i k : Nat} (hi : 1 ≤ i) (hk : slot n i + k ≤ contextBytes n) :
    ∃ c ∈ coreRanges n, c.1 ≤ slot n i ∧ slot n i + k ≤ c.1 + c.2 := by
  have := Nat.mul_le_mul_right (16 * n + 8) hi
  refine ⟨(slot n 1, contextBytes n - slot n 1), List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_, ?_⟩ <;>
    simp only [slot_lin, contextBytes] at * <;> omega

/-- Slot `j` keeps its value outside a write of slot `i`. -/
theorem outside_slot {m₁ m₂ : Mem} {i j k len : Nat} (O : Outside base (slot n i) len m₁ m₂)
    (hlen : len ≤ 16 * n + 8) (hij : j ≠ i) (hj : j < 9) (hk : k ≤ 2 * n) (nw : contextBytes n ≤ 2 ^ 64) :
    val32 m₂ base (slot n j) k = val32 m₁ base (slot n j) k := by
  have sep := slot_sep (n := n) hij
  have b := slot_bound (n := n) hj
  simp only [stride] at sep b
  exact O.val32 (by omega) (by omega)

theorem oneSt_ok {t : State} {i : Nat} (S : St n m size base s₀ t) (hi1 : 1 ≤ i) (hi : i < 9) :
    WP isa (VG.Impl.Mont.X86.Dynamic.one n (slot n i)) t fun u => St n m size base s₀ u ∧ u.gpr .esi = t.gpr .esi ∧
      wordsVal u.mem base (slot n i) n = 1 ∧
      ∀ j, j < 9 → j ≠ i → ∀ k ≤ 2 * n, val32 u.mem base (slot n j) k = val32 t.mem base (slot n j) k := by
  have h := S.ctx
  have cb := h.size_le
  have nw := h.scr.nowrap
  have b := slot_bound (n := n) hi
  have n0 : 0 < n := h.modulus.n0
  have s0 := slot_le (n := n) (i := 0) (j := i) (by omega)
  simp only [stride] at b s0
  refine WP.mono (one_ok h.scr n0 (by omega)) fun u ⟨O, V, K⟩ => ?_
  have C := h.outside_keep K (by decide) (by decide) O (.inl (by omega)) (by have := slot_header n i; omega)
  refine ⟨S.next C (K.mono (by decide)) (rs := [(slot n i, 8 * n)]) (OutsS.of_outs (Outs.of_outside O (by simp)))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact in_core hi1 (by omega)), K.1 _ (by decide), V,
    fun j hj hji k hk => outside_slot O (by omega) hji hj hk (by omega)⟩

theorem maskSt_ok {t : State} (S : St n m size base s₀ t) :
    WP isa (.block (exponentMask (slot n 8) 4)) t fun u => St n m size base s₀ u ∧ u.gpr .esi = t.gpr .esi ∧
      u.mem.readW (off base 4) 32 = (if w32 t.mem base (slot n 8) % 2 = 1 then BitVec.allOnes 32 else 0) ∧
      ∀ j, j < 9 → ∀ k ≤ 2 * n, val32 u.mem base (slot n j) k = val32 t.mem base (slot n j) k := by
  have h := S.ctx
  have cb := h.size_le
  have nw := h.scr.nowrap
  have b := slot_bound (n := n) (i := 8) (by decide)
  simp only [stride] at b
  refine WP.mono (exponentMask_ok h.scr (by omega) (by simp only [contextBytes, slot_lin] at cb; omega))
    fun u ⟨O, V, K⟩ => ?_
  have C := h.outside_keep K (by decide) (by decide) O (.inr (by simp only [slot_lin]; omega)) (by decide)
  refine ⟨S.next C (K.mono (by decide)) (rs := [(4, 4)]) (OutsS.of_outs (Outs.of_outside O (by simp)))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨(0, 8), List.mem_cons_self .., by decide, by decide⟩),
    K.1 _ (by decide), V, fun j hj k hk => ?_⟩
  have := slot_header n j
  have bj := slot_bound (n := n) hj
  simp only [stride] at bj
  exact O.val32 (.inr (by omega)) (by omega)

theorem selectSt_ok {t : State} {bit : Bool} (S : St n m size base s₀ t)
    (hmask : t.mem.readW (off base 4) 32 = if bit then BitVec.allOnes 32 else 0) :
    WP isa (selectProduct (contextMod n) (slot n 6) (slot n 7) 4) t fun u => St n m size base s₀ u ∧ u.gpr .esi = t.gpr .esi ∧
      wordsVal u.mem base (slot n 6) n = wordsVal t.mem base (slot n (if bit then 7 else 6)) n ∧
      ∀ j, j < 9 → j ≠ 6 → ∀ k ≤ 2 * n, val32 u.mem base (slot n j) k = val32 t.mem base (slot n j) k := by
  have h := S.ctx
  have cb := h.size_le
  have nw := h.scr.nowrap
  have n0 : 0 < n := h.modulus.n0
  have b6 := slot_bound (n := n) (i := 6) (by decide)
  have b7 := slot_bound (n := n) (i := 7) (by decide)
  have s67 := slot_le (n := n) (i := 6) (j := 7) (by decide)
  have s06 := slot_le (n := n) (i := 0) (j := 6) (by decide)
  simp only [stride] at b6 b7 s67 s06
  refine WP.mono (selectProduct_ok (M := contextMod n) h.scr
    (by change slot n 6 + 8 * n ≤ size; omega) (by change slot n 7 + 8 * n ≤ size; omega)
    (by simp only [contextBytes, slot_lin] at cb; omega) (.inr (.inl (by change slot n 6 + 8 * n ≤ slot n 7; omega)))
    bit hmask n0) fun u ⟨O, V, K⟩ => ?_
  change Outside base (slot n 6) (8 * n) t.mem u.mem at O
  have C := h.outside_keep K (by decide) (by decide) O (.inl (by omega)) (by have := slot_header n 6; omega)
  refine ⟨S.next C (K.mono (by decide)) (rs := [(slot n 6, 8 * n)]) (OutsS.of_outs (Outs.of_outside O (by simp)))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact in_core (by decide) (by omega)), K.1 _ (by decide), ?_,
    fun j hj hji k hk => outside_slot O (by omega) hji hj hk (by omega)⟩
  change wordsVal u.mem base (slot n 6) n = _ at V
  rw [V]; cases bit <;> rfl

theorem shiftSt_ok {t : State} {e : Nat} (S : St n m size base s₀ t) (he : 2 ≤ e) (hen : e ≤ 2 * n) :
    WP isa (shiftDown e (slot n 8)) t fun u => St n m size base s₀ u ∧ u.gpr .esi = t.gpr .esi ∧
      val32 u.mem base (slot n 8) e = val32 t.mem base (slot n 8) e / 2 ∧
      ∀ j, j < 9 → j ≠ 8 → ∀ k ≤ 2 * n, val32 u.mem base (slot n j) k = val32 t.mem base (slot n j) k := by
  have h := S.ctx
  have cb := h.size_le
  have nw := h.scr.nowrap
  have b8 := slot_bound (n := n) (i := 8) (by decide)
  have s08 := slot_le (n := n) (i := 0) (j := 8) (by decide)
  simp only [stride] at b8 s08
  refine WP.mono (shiftDown_ok h.scr he (by omega)) fun u ⟨O, V, K⟩ => ?_
  have C := h.outside_keep K (by decide) (by decide) O (.inl (by omega)) (by have := slot_header n 8; omega)
  refine ⟨S.next C (K.mono (by decide)) (rs := [(slot n 8, 4 * e)]) (OutsS.of_outs (Outs.of_outside O (by simp)))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact in_core (by decide) (by omega)), K.1 _ (by decide), V,
    fun j hj hji k hk => outside_slot O (by omega) hji hj hk (by omega)⟩

end

end VG.Proof.Dsa.X86.Pow
