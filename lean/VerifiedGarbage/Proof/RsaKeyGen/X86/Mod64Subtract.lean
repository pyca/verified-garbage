module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64Shift
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Native subtraction supplies the 64-bit borrow and combined selection mask -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Mod64

theorem sub_rel (a b : BitVec 32) :
    (a - b).toNat + b.toNat = a.toNat + 2 ^ 32 * (decide (a.toNat < b.toNat)).toNat := by
  have H := sbb_rel a b false
  simpa only [show (BitVec.ofBool false).setWidth 32 = 0#32 from rfl, BitVec.sub_zero,
    Bool.toNat_false, Nat.add_zero] using H

theorem subtract_ok {s : State} {base : Addr} {size exponent : Nat}
    (scratch : Scr s base size) (fit : exponent + 8 ≤ size) :
    WP isa (.block (subtract exponent)) s fun t =>
      (∃ borrow : Bool,
        t.gpr .ebp = (s.gpr .ebp + 0#32 + (BitVec.ofBool borrow).setWidth 32) - 1 ∧
        pair (t.gpr .eax) (t.gpr .edx) + pair (s.mem.readW (off base exponent) 32)
          (s.mem.readW (off base (exponent + 4)) 32) =
          pair (s.gpr .ecx) (s.gpr .ebx) + 2 ^ 64 * borrow.toNat) ∧
      t.mem = s.mem ∧ Keeps [.eax, .edx, .ebp] s t := by
  unfold subtract
  refine wp_movS rfl fun a A _ => wp_movS rfl fun b B _ => ?_
  have Kb : Keeps [.eax, .edx] s b := (A.keeps.mono (by decide)).widen B.keeps
  have readLo := readSrc_sc (scratch.of_keeps Kb (by decide)) (d := exponent) (by omega)
  rw [B.mem, A.mem] at readLo
  refine wp_subS readLo fun c C cfC => ?_
  have Kc : Keeps [.eax, .edx] s c := Kb.widen C.keeps
  have readHi := readSrc_sc (scratch.of_keeps Kc (by decide)) (d := exponent + 4) (by omega)
  rw [C.mem, B.mem, A.mem] at readHi
  refine wp_sbbS readHi cfC fun d D cfD => wp_adcS rfl cfD fun e E _ => wp_subS rfl fun t T _ => WP.block_nil ?_
  let lowBorrow := decide ((b.gpr .eax).toNat < (s.mem.readW (off base exponent) 32).toNat)
  let highBorrow := decide ((c.gpr .edx).toNat <
    (s.mem.readW (off base (exponent + 4)) 32).toNat + lowBorrow.toNat)
  have lo : (c.gpr .eax).toNat + (s.mem.readW (off base exponent) 32).toNat =
      (b.gpr .eax).toNat + 2 ^ 32 * lowBorrow.toNat := by
    rw [C.gpr]
    exact sub_rel ..
  have hi : (d.gpr .edx).toNat + (s.mem.readW (off base (exponent + 4)) 32).toNat + lowBorrow.toNat =
      (c.gpr .edx).toNat + 2 ^ 32 * highBorrow.toNat := by
    rw [D.gpr]
    exact sbb_rel ..
  rw [B.other .eax (by decide), A.gpr] at lo
  rw [C.other .edx (by decide), B.gpr, A.other .ebx (by decide)] at hi
  refine ⟨⟨highBorrow, ?_, ?_⟩, T.mem.trans (E.mem.trans (D.mem.trans (C.mem.trans (B.mem.trans A.mem)))),
    (((((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps).widen D.keeps).widen E.keeps).widen T.keeps⟩
  · rw [T.gpr, E.gpr, D.other .ebp (by decide), C.other .ebp (by decide),
      B.other .ebp (by decide), A.other .ebp (by decide)]
    rfl
  · rw [T.other .eax (by decide), E.other .eax (by decide), D.other .eax (by decide),
      T.other .edx (by decide), E.other .edx (by decide)]
    unfold pair
    omega

end VG.Proof.RsaKeyGen.X86.Mod64
