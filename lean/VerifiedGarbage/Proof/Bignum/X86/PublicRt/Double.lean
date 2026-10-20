module

public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Output
public import VerifiedGarbage.Proof.Mont.X86.Rt.Body
import VerifiedGarbage.Proof.Framework.Omega

/-! # `R² mod M` by doublings, in public RSA at a run-time width

`double`: the sum `2 T` of number 4 at `256 + 5 B`, and its carry after it
(`double_ok`); `reduce`: number 4 set to the sum minus `M`, and the mask
`ecx`, all ones if the sum is below `M` (`reduce_ok`); `select x d`: number
`d` set to number `x` under a mask (`select_ok`); so `doubleStep` doubles
number 4 modulo `M` (`doubleStep_ok`), and `powerTwo` leaves `2^(16 B) mod M`
in it, `R² mod M` for `R = 2^(8 B)` (`powerTwo_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86

theorem numAt_succ (len j : Nat) : numAt len (j + 1) = numAt len j + wb len := by
  simp only [numAt, Nat.succ_mul]; omega

/-- Number `x` and number `d` lie apart. -/
theorem numAt_apart (len : Nat) {x d : Nat} (h : x ≠ d) :
    numAt len d + wb len ≤ numAt len x ∨ numAt len x + wb len ≤ numAt len d := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · right; have := Nat.mul_le_mul_right (wb len) (Nat.succ_le_of_lt h)
    simp only [numAt, Nat.succ_mul] at *; omega
  · left; have := Nat.mul_le_mul_right (wb len) (Nat.succ_le_of_lt h)
    simp only [numAt, Nat.succ_mul] at *; omega

theorem _root_.VG.Proof.Bignum.X86.PublicInputs.edi_eq {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PublicInputs base bytes len args s) (hbase : (args 8).toNat = base.toNat) : args 8 = s.gpr .edi :=
  BitVec.eq_of_toNat_eq (hbase.trans h.edi.symm)

theorem double_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PublicInputs base bytes len args s) :
    WP isa double s fun u => Outside base (numAt len 5) (wb len + 4) s.mem u.mem ∧
      (∃ c : Bool, w32 u.mem base (numAt len 5 + wb len) = c.toNat ∧
        val32 u.mem base (numAt len 5) (nw len) + 2 ^ (32 * nw len) * c.toNat =
          val32 s.mem base (numAt len 4) (nw len) + val32 s.mem base (numAt len 4) (nw len)) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  have f5 := (h.fits (j := 5) (by decide)).2
  have f4 := (h.fits (j := 4) (by decide)).1
  have dims := h.dimensions
  have wbe := wb_eq len
  have wbl := wb_le h.upper
  have nw' := h.scratch.nowrap
  have sep := numAt_apart len (x := 4) (d := 5) (by decide)
  unfold double
  refine WP.seq (slotPtr_ok (r := .ebp) (t := .edx) (j := 5) (by decide) (by decide) h.edi h.width h.upper
    (by decide) fun u K m p _ => ?_)
  have hu := h.keep K (by decide) (by decide) (by rw [m]; exact Outside.refl _ _ _ _)
  refine slotPtr_ok (r := .ebx) (t := .edx) (j := 4) (by decide) (by decide) hu.edi hu.width h.upper (by decide)
    fun v Kv mv pv cv => wp_movS rfl fun w uw _ => WP.block_nil ?_
  have Kw : Keeps [.ebx, .ecx, .edx, .ebp] s w :=
    ((K.mono (by decide)).trans (Kv.mono (by decide))).trans (uw.keeps.mono (by decide))
  have mw : w.mem = s.mem := by rw [uw.mem, mv, m]
  have hw := h.ws.of_keeps Kw
  refine WP.seq (WP.mono (doubleLoop_ok hw (x := numAt len 4) (a := numAt len 5) (N := nw len)
    (by simp only [nw]; omega) (by omega) (by omega) (by omega)
    (by rw [PtrAt, uw.other _ (by decide)]; exact pv)
    (by rw [PtrAt, uw.other _ (by decide), Kv.1 _ (by decide)]; exact p)
    (by rw [uw.other _ (by decide), cv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact wbe)
    uw.gpr) fun t ⟨O, ebp, ⟨c, ec, V⟩, Kt⟩ => ?_)
  have ht := hw.of_keeps Kt
  refine wp_movS rfl fun t₁ e₁ _ => wp_subS rfl fun t₂ e₂ _ => ?_
  have K₂ : Keeps [.eax] t t₂ := e₁.keeps.trans e₂.keeps
  have ebp₂ : PtrAt t₂ base .ebp (numAt len 5 + 4 * nw len) := by rw [PtrAt, K₂.1 _ (by decide)]; exact ebp
  refine wp_storeS (ea_ptr (ht.of_keeps K₂) ebp₂ (d := 0) (by omega))
    (ws_write (ht.of_keeps K₂) (y := numAt len 5 + 4 * nw len + 0) (n := 4) (by omega)) fun t₃ m₃ => WP.block_nil ?_
  have eax : (t₂.gpr .eax).toNat = c.toNat := by
    rw [e₂.gpr, e₁.gpr, e₁.other _ (by decide), ec]; cases c <;> rfl
  have mt₂ : t₂.mem = t.mem := by rw [e₂.mem, e₁.mem]
  refine ⟨?_, ⟨c, ?_, ?_⟩, (Kw.mono (by decide)).trans ((Kt.trans (K₂.mono (by decide))).trans (m₃.keeps _))⟩
  · rw [m₃.mem, mt₂, Nat.add_zero, ← mw]
    have O' : Outside base (numAt len 5) (wb len + 4) w.mem t.mem := O.mono (Nat.le_refl _) (by omega)
    exact O'.trans ((writeW32_outside _ _ _ (by omega)).mono (by omega) (by omega))
  · rw [m₃.mem, mt₂, Nat.add_zero, ← wbe, w32_write_self, eax]
  · rw [m₃.mem, mt₂, Nat.add_zero, ← mw,
      (writeW32_outside t.mem base (t₂.gpr .eax) (by omega)).val32 (by omega) (by omega)]
    exact V

end VG.Proof.Bignum.X86.PublicRt
