module

import VerifiedGarbage.Impl.MillerRabin.X86.Ops
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Impl.MillerRabin.X86.Layout

/-! # Branch-free conversion of a word comparison into a stored bit -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem equalFinish_ok {s : State} {W : Addr} {L result : Nat} (hw : Ws s W L)
    (base : PtrAt s W .edi 0) (fit : result + 4 ≤ L) :
    WP isa (.block [.mov .eax (.imm 0), .alu .sub .ebx (.imm 1),
      .alu .adc .eax (.imm 0), .store (slot result) .eax]) s fun t =>
      w32 t.mem W result = (decide (s.gpr .ebx = 0#32)).toNat ∧
      Outside W result 4 s.mem t.mem ∧ Keeps [.eax, .ebx] s t := by
  refine wp_movS rfl fun a A _ => wp_subS rfl fun b B cf => wp_adcS rfl cf fun c C _ => ?_
  have K : Keeps [.eax, .ebx] s c := ((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps
  have hc := hw.of_keeps K
  have baseC : PtrAt c W .edi 0 := by rw [PtrAt, K.1 .edi (by decide)]; exact base
  refine wp_storeS (ea_ptr hc baseC (d := result) (by omega))
    (ws_write hc (y := 0 + result) (n := 4) (by omega)) fun t T => WP.block_nil ?_
  have M : c.mem = s.mem := C.mem.trans (B.mem.trans A.mem)
  have value : c.gpr .eax = BitVec.ofNat 32 (decide (s.gpr .ebx = 0#32)).toNat := by
    rw [C.gpr, B.other .eax (by decide), A.gpr, A.other .ebx (by decide)]
    have test : decide ((s.gpr .ebx).toNat < (1 : BitVec 32).toNat) = decide (s.gpr .ebx = 0#32) := by
      have iffZero : (s.gpr .ebx).toNat < (1 : BitVec 32).toNat ↔ s.gpr .ebx = 0#32 := by
        rw [← BitVec.toNat_inj]
        change (s.gpr .ebx).toNat < 1 ↔ (s.gpr .ebx).toNat = 0
        omega
      simp only [iffZero]
    rw [test]
    cases decide (s.gpr .ebx = 0#32) <;> rfl
  refine ⟨?_, ?_, K.widen (T.keeps [])⟩
  · rw [T.mem, Nat.zero_add, w32_write_self, value, BitVec.toNat_ofNat]
    cases decide (s.gpr .ebx = 0#32) <;> rfl
  · rw [T.mem, Nat.zero_add, M]
    exact writeW32_outside _ _ _ (by have := hw.nowrap; omega)

end VG.Proof.MillerRabin.X86
