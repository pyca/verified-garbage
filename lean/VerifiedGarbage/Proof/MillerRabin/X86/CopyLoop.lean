module

import VerifiedGarbage.Impl.MillerRabin.X86.Ops
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
public import VerifiedGarbage.Impl.MillerRabin.X86.Layout

/-! # A runtime native-word copy preserves its source and every other byte -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Bignum.X86.PublicRt (countLoop count1_zf ptr4)

def copyBody : List Instr :=
  [.mov .eax (.mem (at_ .ebx 0)), .store (at_ .ebp 0) .eax,
    .alu .add .ebx (.imm 4), .alu .add .ebp (.imm 4), .alu .sub .esi (.imm 1)]

theorem copyLoop_ok {s : State} {W : Addr} {L x y N : Nat} (hw : Ws s W L)
    (positive : 0 < N) (dstFit : x + 4 * N ≤ L) (srcFit : y + 4 * N ≤ L)
    (apart : x = y ∨ x + 4 * N ≤ y ∨ y + 4 * N ≤ x)
    (dst : PtrAt s W .ebp x) (src : PtrAt s W .ebx y) (count : (s.gpr .esi).toNat = N) :
    WP isa (.loop (.block copyBody) .ne) s fun t =>
      Outside W x (4 * N) s.mem t.mem ∧ val32 t.mem W x N = val32 s.mem W y N ∧
      Keeps [.eax, .ebx, .ebp, .esi] s t := by
  have nowrap := hw.nowrap
  refine WP.mono (countLoop positive (fun i t => Keeps [.eax, .ebx, .ebp, .esi] s t ∧
    PtrAt t W .ebp (x + 4 * i) ∧ PtrAt t W .ebx (y + 4 * i) ∧ (t.gpr .esi).toNat = N - i ∧
    Outside W x (4 * i) s.mem t.mem ∧ val32 t.mem W x i = val32 s.mem W y i) ?_
    ⟨Keeps.refl _ _, by simpa using dst, by simpa using src, by simpa using count, Outside.refl _ _ _ _, rfl⟩)
    fun t ⟨K, _, _, _, O, V⟩ => ⟨O, V, K⟩
  rintro i t index ⟨K, bp, bx, countI, O, V⟩
  have ht := hw.of_keeps K
  unfold copyBody
  refine wp_movS (readSrc_ptr ht bx (d := 0) (by omega)) fun a A _ => ?_
  have bpA : PtrAt a W .ebp (x + 4 * i) := by rw [PtrAt, A.other .ebp (by decide)]; exact bp
  refine wp_storeS (ea_ptr (ht.of_keeps A.keeps) bpA (d := 0) (by omega))
    (ws_write (ht.of_keeps A.keeps) (y := x + 4 * i + 0) (n := 4) (by omega)) fun b B => ?_
  refine wp_addS rfl fun c C _ => wp_addS rfl fun d D _ => wp_subZ rfl fun u U Z => WP.block_nil ?_
  have esiD : d.gpr .esi = t.gpr .esi := by
    rw [D.other .esi (by decide), C.other .esi (by decide), B.gpr, A.other .esi (by decide)]
  obtain ⟨nextCount, last⟩ := count1_zf countI index
  have word : w32 t.mem W (y + 4 * i) = w32 s.mem W (y + 4 * i) :=
    O.w32 (by rcases apart with apart | apart <;> omega) (by omega)
  refine ⟨⟨((((K.widen A.keeps).widen (B.keeps [])).widen C.keeps).widen D.keeps).widen U.keeps,
    ?_, ?_, by rw [U.gpr, esiD]; exact nextCount, ?_, ?_⟩, by rw [Z, esiD, last]⟩
  · rw [PtrAt, U.other .ebp (by decide), D.gpr, C.other .ebp (by decide), B.gpr, A.other .ebp (by decide)]
    exact ptr4 bp
  · rw [PtrAt, U.other .ebx (by decide), D.other .ebx (by decide), C.gpr, B.gpr, A.other .ebx (by decide)]
    exact ptr4 bx
  · rw [U.mem, D.mem, C.mem, B.mem, A.mem, Nat.add_zero]
    exact (O.mono (by omega) (by omega)).trans
      ((writeW32_outside _ _ _ (by omega)).mono (by omega) (by omega))
  · rw [U.mem, D.mem, C.mem, B.mem, A.mem, Nat.add_zero, val32_store nowrap (by omega),
      V, A.gpr, Nat.add_zero, val32_succ s.mem W y]
    change _ + _ * w32 t.mem W (y + 4 * i) = _
    rw [word]

end VG.Proof.MillerRabin.X86
