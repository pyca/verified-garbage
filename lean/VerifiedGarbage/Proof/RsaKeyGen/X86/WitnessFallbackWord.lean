module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessFallback
public import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Masked native updates select the fallback bits and retain uniform witnesses -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessFallback
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.WitnessFallback

theorem low_value (old : BitVec 32) (uniform : Bool) :
    ((((cmask uniform ^^^ BitVec.allOnes 32) &&& 2#32) ||| old).toNat) =
      if uniform then old.toNat else old.toNat ||| 2 := by
  cases uniform
  · change (2#32 ||| old).toNat = old.toNat ||| 2
    rw [BitVec.toNat_or, Nat.or_comm]
    rfl
  · change (0#32 ||| old).toNat = old.toNat
    rw [BitVec.zero_or]

theorem high_value (old : BitVec 32) (uniform : Bool) :
    ((((cmask uniform ^^^ BitVec.allOnes 32) &&& 0x80000000#32) ^^^ BitVec.allOnes 32) &&& old).toNat =
      if uniform then old.toNat else old.toNat % 2 ^ 31 := by
  cases uniform
  · change (0x7fffffff#32 &&& old).toNat = old.toNat % 2 ^ 31
    rw [BitVec.toNat_and, Nat.and_comm]
    change old.toNat &&& (2 ^ 31 - 1) = old.toNat % 2 ^ 31
    exact Nat.and_two_pow_sub_one_eq_mod _ _
  · change (BitVec.allOnes 32 &&& old).toNat = old.toNat
    rw [BitVec.allOnes_and]

theorem low_ok {s : State} {base : Addr} {size src : Nat} (scratch : Scr s base size)
    (fit : src + 4 ≤ size) {uniform : Bool} (mask : s.gpr .eax = cmask uniform) :
    WP isa (.block (low src)) s fun t =>
      w32 t.mem base src = (if uniform then w32 s.mem base src else w32 s.mem base src ||| 2) ∧
      Outside base src 4 s.mem t.mem ∧ Keeps [.ecx] s t := by
  unfold low
  refine wp_movS rfl fun a A _ => wp_logicS (.inr rfl) rfl fun b B => wp_logicS (.inl rfl) rfl fun c C => ?_
  have Kc : Keeps [.ecx] s c := (A.keeps.widen B.keeps).widen C.keeps
  have load := readSrc_sc (scratch.of_keeps Kc (by decide)) fit
  rw [C.mem, B.mem, A.mem] at load
  refine wp_orS load fun d D => ?_
  have Kd : Keeps [.ecx] s d := Kc.widen D.keeps
  have Sd := scratch.of_keeps Kd (by decide)
  refine wp_storeS (Sd.ea (by omega)) (Sd.write fit) fun t T => WP.block_nil ?_
  have V : d.gpr .ecx = (((cmask uniform ^^^ BitVec.allOnes 32) &&& 2#32) ||| s.mem.readW (off base src) 32) := by
    rw [D.gpr, C.gpr, B.gpr, A.gpr, mask]
    rfl
  refine ⟨?_, ?_, Kd.widen (T.keeps [])⟩
  · rw [T.mem, w32_write_self, V]
    exact low_value _ _
  · rw [T.mem, D.mem, C.mem, B.mem, A.mem]
    exact writeW32_outside _ _ _ (by have := scratch.nowrap; omega)

theorem high_ok {s : State} {base : Addr} {size offset : Nat} (scratch : Scr s base size)
    (fit : offset + 4 ≤ size) {uniform : Bool} (mask : s.gpr .eax = cmask uniform) :
    WP isa (.block (high offset)) s fun t =>
      w32 t.mem base offset = (if uniform then w32 s.mem base offset else w32 s.mem base offset % 2 ^ 31) ∧
      Outside base offset 4 s.mem t.mem ∧ Keeps [.ecx] s t := by
  unfold high
  refine wp_movS rfl fun a A _ => wp_logicS (.inr rfl) rfl fun b B =>
    wp_logicS (.inl rfl) rfl fun c C => wp_logicS (.inr rfl) rfl fun d D => ?_
  have Kd : Keeps [.ecx] s d := ((A.keeps.widen B.keeps).widen C.keeps).widen D.keeps
  have load := readSrc_sc (scratch.of_keeps Kd (by decide)) fit
  rw [D.mem, C.mem, B.mem, A.mem] at load
  refine wp_logicS (.inl rfl) load fun e E => ?_
  have Ke : Keeps [.ecx] s e := Kd.widen E.keeps
  have Se := scratch.of_keeps Ke (by decide)
  refine wp_storeS (Se.ea (by omega)) (Se.write fit) fun t T => WP.block_nil ?_
  have V : e.gpr .ecx = ((((cmask uniform ^^^ BitVec.allOnes 32) &&& 0x80000000#32) ^^^
      BitVec.allOnes 32) &&& s.mem.readW (off base offset) 32) := by
    rw [E.gpr, D.gpr, C.gpr, B.gpr, A.gpr, mask]
    rfl
  refine ⟨?_, ?_, Ke.widen (T.keeps [])⟩
  · rw [T.mem, w32_write_self, V]
    exact high_value _ _
  · rw [T.mem, E.mem, D.mem, C.mem, B.mem, A.mem]
    exact writeW32_outside _ _ _ (by have := scratch.nowrap; omega)

end VG.Proof.RsaKeyGen.X86.WitnessFallback
