module

import VerifiedGarbage.Impl.MillerRabin.X86.Ops
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
public import VerifiedGarbage.Impl.MillerRabin.X86.Layout

/-! # Masked native-word table selection with an in-place destination -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Bignum.X86.PublicRt (countLoop count1_zf ptr4)

def selectBody : List Instr :=
  [.mov .eax (.mem (at_ .ebp 0)), .alu .xor .eax (.mem (at_ .ebx 0)),
    .alu .and .eax (.reg .ecx), .alu .xor .eax (.mem (at_ .ebx 0)), .store (at_ .ebx 0) .eax,
    .alu .add .ebp (.imm 4), .alu .add .ebx (.imm 4), .alu .sub .esi (.imm 1)]

theorem selectLoop_ok {s : State} {W : Addr} {L x y N : Nat} (hw : Ws s W L)
    (positive : 0 < N) (dstFit : x + 4 * N ≤ L) (srcFit : y + 4 * N ≤ L)
    (apart : x + 4 * N ≤ y ∨ y + 4 * N ≤ x)
    (dst : PtrAt s W .ebx x) (src : PtrAt s W .ebp y) (count : (s.gpr .esi).toNat = N)
    (k : Bool) (mask : s.gpr .ecx = if k then BitVec.allOnes 32 else 0#32) :
    WP isa (.loop (.block selectBody) .ne) s fun t =>
      Outside W x (4 * N) s.mem t.mem ∧
      val32 t.mem W x N = val32 s.mem W (if k then y else x) N ∧
      Keeps [.eax, .ebx, .ebp, .esi] s t := by
  have nowrap := hw.nowrap
  refine WP.mono (countLoop positive (fun i t => Keeps [.eax, .ebx, .ebp, .esi] s t ∧
    PtrAt t W .ebx (x + 4 * i) ∧ PtrAt t W .ebp (y + 4 * i) ∧ (t.gpr .esi).toNat = N - i ∧
    Outside W x (4 * i) s.mem t.mem ∧ val32 t.mem W x i = val32 s.mem W (if k then y else x) i) ?_
    ⟨Keeps.refl _ _, by simpa using dst, by simpa using src, by simpa using count, Outside.refl _ _ _ _, rfl⟩)
    fun t ⟨K, _, _, _, O, V⟩ => ⟨O, V, K⟩
  rintro i t index ⟨K, bx, bp, countI, O, V⟩
  have ht := hw.of_keeps K
  unfold selectBody
  refine wp_movS (readSrc_ptr ht bp (d := 0) (by omega)) fun a A _ => ?_
  have bxA : PtrAt a W .ebx (x + 4 * i) := by rw [PtrAt, A.other .ebx (by decide)]; exact bx
  have readA := readSrc_ptr (ht.of_keeps A.keeps) bxA (d := 0) (by omega : x + 4 * i + 0 + 4 ≤ L)
  refine wp_logicS (.inr rfl) readA fun b B => wp_logicS (.inl rfl) rfl fun c C => ?_
  have bxC : PtrAt c W .ebx (x + 4 * i) := by
    rw [PtrAt, C.other .ebx (by decide), B.other .ebx (by decide), A.other .ebx (by decide)]; exact bx
  have Kc : Keeps [.eax] t c := (A.keeps.trans B.keeps).trans C.keeps
  refine wp_logicS (.inr rfl) (readSrc_ptr (ht.of_keeps Kc) bxC (d := 0) (by omega)) fun d D => ?_
  have Kd := Kc.trans D.keeps
  have bxD : PtrAt d W .ebx (x + 4 * i) := by rw [PtrAt, Kd.1 .ebx (by decide)]; exact bx
  refine wp_storeS (ea_ptr (ht.of_keeps Kd) bxD (d := 0) (by omega))
    (ws_write (ht.of_keeps Kd) (y := x + 4 * i + 0) (n := 4) (by omega)) fun e E => ?_
  refine wp_addS rfl fun f F _ => wp_addS rfl fun h H _ => wp_subZ rfl fun u U Z => WP.block_nil ?_
  have esiH : h.gpr .esi = t.gpr .esi := by
    rw [H.other .esi (by decide), F.other .esi (by decide), E.gpr, Kd.1 .esi (by decide)]
  obtain ⟨nextCount, last⟩ := count1_zf countI index
  have value : d.gpr .eax = if k then t.mem.readW (off W (y + 4 * i)) 32
      else t.mem.readW (off W (x + 4 * i)) 32 := by
    rw [D.gpr, C.gpr, B.gpr, A.gpr, A.mem, C.mem, B.mem, A.mem,
      B.other .ecx (by decide), A.other .ecx (by decide),
      K.1 .ecx (by decide), mask, Nat.add_zero, Nat.add_zero]
    simp only [show AluOp.xor ≠ AluOp.and by decide, ↓reduceIte]
    cases k
    · simp only [Bool.false_eq_true, ↓reduceIte, BitVec.and_zero, BitVec.zero_xor]
    · simp only [↓reduceIte, BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  refine ⟨⟨(((((K.widen Kd).widen (E.keeps [])).widen F.keeps).widen H.keeps).widen U.keeps),
    ?_, ?_, by rw [U.gpr, esiH]; exact nextCount, ?_, ?_⟩, by rw [Z, esiH, last]⟩
  · rw [PtrAt, U.other .ebx (by decide), H.gpr, F.other .ebx (by decide), E.gpr, Kd.1 .ebx (by decide)]
    exact ptr4 bx
  · rw [PtrAt, U.other .ebp (by decide), H.other .ebp (by decide), F.gpr, E.gpr, Kd.1 .ebp (by decide)]
    exact ptr4 bp
  · rw [U.mem, H.mem, F.mem, E.mem, D.mem, C.mem, B.mem, A.mem, Nat.add_zero]
    exact (O.mono (by omega) (by omega)).trans
      ((writeW32_outside _ _ _ (by omega)).mono (by omega) (by omega))
  · rw [U.mem, H.mem, F.mem, E.mem, D.mem, C.mem, B.mem, A.mem, Nat.add_zero,
      val32_store nowrap (by omega), V, value, val32_succ]
    cases k <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · change _ + _ * w32 t.mem W (x + 4 * i) = _
      rw [O.w32 (by omega) (by omega)]
    · change _ + _ * w32 t.mem W (y + 4 * i) = _
      rw [O.w32 (by omega) (by omega)]

end VG.Proof.MillerRabin.X86
