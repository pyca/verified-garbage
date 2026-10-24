module

public import VerifiedGarbage.Proof.Mont.X86.Compact.Args
public import VerifiedGarbage.Proof.Mont.Words

/-! # Loading a multiplier from a prepared operand -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

/-- Load a native word from the selected operand into the row's multiplier slot. -/
theorem loadA_ok {s : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32}
    (hw : Ws s W L) (ha : Args s W L A) (base : (A 0).toNat = W.toNat)
    {S a i : Nat} (headerFit : 64 + 8 * (A 3).toNat + 4 ≤ L)
    (operand : s.mem.readW (off W (64 + 8 * (A 3).toNat)) 32 = BitVec.ofNat 32 (W.toNat + a))
    (hedi : PtrAt s W .edi S) (hebp : PtrAt s W .ebp (S + Compact.accOff + 4 * i))
    (operandFit : a + 4 * i + 4 ≤ L) (accFit : S + Compact.accOff + 4 * i < L) :
    WP isa (.block Compact.loadA) s fun u =>
      u.mem = s.mem.writeW (off W (S + Rt.multOff)) (s.mem.readW (off W (a + 4 * i)) 32) ∧
      Keeps [.eax, .ecx, .edx] s u := by
  have nowrap := hw.nowrap
  have acc : Compact.accOff = 24 := rfl
  have mult : Rt.multOff = 20 := rfl
  unfold Compact.loadA
  refine WP.block_append (WP.mono (operandPtr_ok hw ha base (r := .ecx) (t := .edx)
    (i := 3) (by decide) (by decide) (by decide) headerFit) fun a₀ ⟨ptr, M, K⟩ => ?_)
  refine wp_movS rfl fun a₁ B _ => ?_
  refine wp_subS rfl fun a₂ C _ => ?_
  refine wp_subS rfl fun a₃ D _ => ?_
  refine wp_addS rfl fun a₄ E _ => ?_
  have K₄ : Keeps [.eax, .ecx, .edx] s a₄ :=
    ((((K.mono (by decide)).widen B.keeps).widen C.keeps).widen D.keeps).widen E.keeps
  have offset : (a₃.gpr .eax).toNat = 4 * i := by
    rw [D.gpr, C.gpr, B.gpr, B.other .edi (by decide), K.1 .ebp (by decide), K.1 .edi (by decide)]
    simp only [BitVec.toNat_sub, hebp, hedi, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := W.toNat + (S + Compact.accOff + 4 * i)) (by omega_arith),
      Nat.mod_eq_of_lt (a := W.toNat + S) (by omega_arith)]
    omega_arith
  have address : PtrAt a₄ W .eax (a + 4 * i) := by
    rw [PtrAt, E.gpr, BitVec.toNat_add, offset, D.other .ecx (by decide),
      C.other .ecx (by decide), B.other .ecx (by decide), ptr, operand, BitVec.toNat_ofNat]
    omega_arith
  refine wp_movS (readSrc_ptr (hw.of_keeps K₄) address (d := 0) (by omega_arith)) fun a₅ F _ => ?_
  have K₅ : Keeps [.eax, .ecx, .edx] s a₅ := K₄.widen F.keeps
  have edi : PtrAt a₅ W .edi S := by rw [PtrAt, K₅.1 .edi (by decide)]; exact hedi
  refine wp_storeS (ea_ptr (hw.of_keeps K₅) edi (d := Rt.multOff) (by omega_arith))
    (ws_write (hw.of_keeps K₅) (y := S + Rt.multOff) (n := 4) (by omega_arith)) fun u G => WP.block_nil ?_
  refine ⟨?_, K₅.widen (G.keeps [])⟩
  rw [G.mem, F.gpr, F.mem, E.mem, D.mem, C.mem, B.mem, M, Nat.add_zero]

end VG.Proof.Mont.X86.Compact
