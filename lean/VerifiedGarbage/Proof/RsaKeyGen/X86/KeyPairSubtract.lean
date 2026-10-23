module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Paired native subtraction for the private-exponent complement -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.Key

theorem subtractPair_ok {s : State} {B : Addr} {Z out a b : Nat} (h : Scr s B Z)
    (fa : a + 8 ≤ Z) (fb : b + 8 ≤ Z) (fo : out + 8 ≤ Z) :
    WP isa (.block (subtractPair out a b)) s fun t =>
      Outside B out 8 s.mem t.mem ∧
      (∃ borrow : Bool, val32 t.mem B out 2 + val32 s.mem B b 2 =
        val32 s.mem B a 2 + 2 ^ 64 * borrow.toNat) ∧ Keeps [.eax, .edx] s t := by
  have hn := h.nowrap
  unfold subtractPair
  refine wp_movS (readSrc_sc h (by omega_arith)) fun u U _ => ?_
  have hu := h.of_keeps U.keeps (by decide)
  refine wp_movS (readSrc_sc hu (by omega_arith)) fun v V _ => ?_
  have Kv : Keeps [.eax, .edx] s v := (U.keeps.mono (by decide)).widen V.keeps
  have hv := h.of_keeps Kv (by decide)
  have loRead := readSrc_sc hv (d := b) (by omega_arith)
  rw [V.mem, U.mem] at loRead
  refine wp_subS loRead fun w W cfW => ?_
  have Kw : Keeps [.eax, .edx] s w := Kv.widen W.keeps
  have hw := h.of_keeps Kw (by decide)
  have hiRead := readSrc_sc hw (d := b + 4) (by omega_arith)
  rw [W.mem, V.mem, U.mem] at hiRead
  refine wp_sbbS hiRead cfW fun x X _ => ?_
  have Kx : Keeps [.eax, .edx] s x := Kw.widen X.keeps
  have hx := h.of_keeps Kx (by decide)
  refine wp_storeS (hx.ea (by omega_arith)) (hx.write (by omega_arith)) fun y Y => ?_
  have hy := hx.of_keeps (Y.keeps []) (by decide)
  refine wp_storeS (hy.ea (by omega_arith)) (hy.write (by omega_arith)) fun t T => WP.block_nil ?_
  let lowBorrow := decide ((v.gpr .eax).toNat < (s.mem.readW (off B b) 32).toNat)
  let highBorrow := decide ((w.gpr .edx).toNat < (s.mem.readW (off B (b + 4)) 32).toNat + lowBorrow.toNat)
  have low : (w.gpr .eax).toNat + w32 s.mem B b = (v.gpr .eax).toNat + 2 ^ 32 * lowBorrow.toNat := by
    rw [W.gpr]
    have H := sbb_rel (v.gpr .eax) (s.mem.readW (off B b) 32) false
    simpa only [show (BitVec.ofBool false).setWidth 32 = 0#32 from rfl, BitVec.sub_zero,
      Bool.toNat_false, Nat.add_zero] using H
  have high : (x.gpr .edx).toNat + w32 s.mem B (b + 4) + lowBorrow.toNat =
      (w.gpr .edx).toNat + 2 ^ 32 * highBorrow.toNat := by rw [X.gpr]; exact sbb_rel ..
  rw [V.other _ (by decide), U.gpr] at low
  rw [W.other _ (by decide), V.gpr, U.mem] at high
  change (w.gpr .eax).toNat + w32 s.mem B b = w32 s.mem B a + 2 ^ 32 * lowBorrow.toNat at low
  change (x.gpr .edx).toNat + w32 s.mem B (b + 4) + lowBorrow.toNat =
    w32 s.mem B (a + 4) + 2 ^ 32 * highBorrow.toNat at high
  have oldMem : x.mem = s.mem := X.mem.trans (W.mem.trans (V.mem.trans U.mem))
  have Oy : Outside B out 4 s.mem y.mem := by
    rw [Y.mem, oldMem]
    exact writeW32_outside _ _ _ (by omega_arith)
  have Ot : Outside B (out + 4) 4 y.mem t.mem := by
    rw [T.mem]
    exact writeW32_outside _ _ _ (by omega_arith)
  have lowT : w32 t.mem B out = (x.gpr .eax).toNat := by
    rw [Ot.w32 (Or.inl (Nat.le_refl _)) (by omega_arith), Y.mem, w32_write_self]
  have highT : w32 t.mem B (out + 4) = (x.gpr .edx).toNat := by
    rw [T.mem, w32_write_self, Y.gpr]
  refine ⟨(Oy.mono (Nat.le_refl _) (by omega_arith)).trans (Ot.mono (by omega_arith) (by omega_arith)),
    ⟨highBorrow, ?_⟩, Kx.trans ((Y.keeps _).trans (T.keeps _))⟩
  simp only [val32, Nat.mul_zero, Nat.add_zero]
  rw [lowT, highT, X.other _ (by decide)]
  omega_arith

end VG.Proof.RsaKeyGen.X86.Key
