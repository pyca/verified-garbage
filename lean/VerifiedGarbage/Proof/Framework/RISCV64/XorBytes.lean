module

public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.Words.RISCV64.XorBytes
public import VerifiedGarbage.TCB.RISCV64.Isa
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes
import all Init.Data.Nat.Bitwise.Basic

/-!
# RISC-V: XORing bytes of argument buffers

Untrusted: everything here is checked by Lean. The effect of `xorBytes`,
byte by byte (`xorBytes_ok`): each byte of the destination is XORed with the
source's (which the writes must not overlap), and memory changes only
there.
-/

@[expose] public section

namespace VG.RISCV64.Bytes

open VG.Impl.Words.RISCV64 VG.RISCV64.Steps

variable {s : State}

/-- The byte stored by `xor t, t, u; sb t, …` after two `lbu`s. -/
theorem xor_setWidth (a b : Byte) : ((a.setWidth 64 ^^^ b.setWidth 64).setWidth 8) = a ^^^ b := by
  ext i hi; simp

/-- What `xorBytes` keeps: the registers but `t` and `u`. -/
structure Keep2 (t u : Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ≠ t → r ≠ u → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

/-- Bytes `0 … k - 1` XORed, the rest of the destination as it was. -/
structure XorI (t u dst src : Reg) (n : Nat) (s : State) (k : Nat) (s' : State) : Prop
    extends Keep2 t u s s' where
  xored : ∀ j < k, s'.mem (s.gpr dst + BitVec.ofNat 64 j) =
    s.mem (s.gpr dst + BitVec.ofNat 64 j) ^^^ s.mem (s.gpr src + BitVec.ofNat 64 j)
  rest : ∀ j, k ≤ j → j < n → s'.mem (s.gpr dst + BitVec.ofNat 64 j) = s.mem (s.gpr dst + BitVec.ofNat 64 j)
  frame : Frame [⟨s.gpr dst, n⟩] s.mem s'.mem

theorem xorBytes_ok {t u dst src : Reg} {n : Nat} (htd : t ≠ dst) (hts : t ≠ src) (hud : u ≠ dst)
    (hus : u ≠ src) (htu : t ≠ u) (hn : n ≤ 2048)
    (hr : ∀ i < n, InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < n, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < n, ¬ (⟨s.gpr dst, n⟩ : Region).Contains (s.gpr src + BitVec.ofNat 64 i) 1) :
    WP isa (.block (xorBytes t u dst src n)) s (XorI t u dst src n s n) := by
  refine wp_range_flatMap (M := isa) (XorI t u dst src n s) (fun k s₁ hk h => ?_) n
    (Nat.le_refl _) s ⟨⟨fun _ _ _ => rfl, rfl, rfl, rfl⟩, fun _ h => absurd h (by omega),
      fun _ _ _ => rfl, Frame.refl _ _⟩
  have hdst : s₁.gpr dst = s.gpr dst := h.gpr _ (Ne.symm htd) (Ne.symm hud)
  have hsrc : s₁.gpr src = s.gpr src := h.gpr _ (Ne.symm hts) (Ne.symm hus)
  have hwk := hw k hk
  have hrk : InRegions (s.rd ++ s.wr) (s.gpr dst + BitVec.ofNat 64 k) 1 := by
    obtain ⟨r, hr, hc⟩ := hwk; exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine wp_lbu (a := s.gpr dst + BitVec.ofNat 64 k) (by omega) (by rw [hdst])
    (by rw [h.rd, h.wr]; exact hrk) fun s₂ u₂ => ?_
  refine wp_lbu (a := s.gpr src + BitVec.ofNat 64 k) (by omega)
    (by rw [u₂.other _ (Ne.symm hts), hsrc]) (by rw [u₂.rd, u₂.wr, h.rd, h.wr]; exact hr k hk)
    fun s₃ u₃ => ?_
  refine wp_xor fun s₄ u₄ => ?_
  refine wp_sb (a := s.gpr dst + BitVec.ofNat 64 k) (by omega)
    (by rw [u₄.other _ (Ne.symm htd), u₃.other _ (Ne.symm hud), u₂.other _ (Ne.symm htd), hdst])
    (by rw [u₄.wr, u₃.wr, u₂.wr, h.wr]; exact hwk) fun s₅ g₅ => WP.block_nil ?_
  -- The bytes read: the destination's, not yet written, and the source's.
  have vd : s₁.mem (s.gpr dst + BitVec.ofNat 64 k) = s.mem (s.gpr dst + BitVec.ofNat 64 k) :=
    h.rest k (Nat.le_refl _) hk
  have vs : s₁.mem (s.gpr src + BitVec.ofNat 64 k) = s.mem (s.gpr src + BitVec.ofNat 64 k) :=
    h.frame _ fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep k hk
  have hv : (s₄.gpr t).setWidth 8 =
      s.mem (s.gpr dst + BitVec.ofNat 64 k) ^^^ s.mem (s.gpr src + BitVec.ofNat 64 k) := by
    rw [u₄.gpr, u₃.other _ htu, u₂.gpr, u₃.gpr, u₂.mem, vd, vs, xor_setWidth]
  have hm : s₅.mem = s₁.mem.writeW (s.gpr dst + BitVec.ofNat 64 k)
      (s.mem (s.gpr dst + BitVec.ofNat 64 k) ^^^ s.mem (s.gpr src + BitVec.ofNat 64 k)) := by
    rw [g₅.mem, hv, u₄.mem, u₃.mem, u₂.mem]
  refine ⟨⟨fun r h1 h2 => by rw [g₅.gpr, u₄.other r h1, u₃.other r h2, u₂.other r h1, h.gpr r h1 h2],
    by rw [g₅.rd, u₄.rd, u₃.rd, u₂.rd, h.rd], by rw [g₅.wr, u₄.wr, u₃.wr, u₂.wr, h.wr],
    by rw [g₅.sp, u₄.sp, u₃.sp, u₂.sp, h.sp]⟩, fun j hj => ?_, fun j hj hjn => ?_, ?_⟩
  · rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [byte_writeW_ne _ _ _ (by omega) (by omega) (by omega)]; exact h.xored j hj
    · simp only [WriteBytes.writeW8_apply, ite_true]
  · rw [hm, byte_writeW_ne _ _ _ (by omega) (by omega) (by omega)]
    exact h.rest j (by omega) hjn
  · rw [hm]
    exact h.frame.writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega) (by omega))

end VG.RISCV64.Bytes
