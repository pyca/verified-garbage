module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashGeometry
public import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Seed pointers and lengths survive calls of the existing SHA code -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86

structure HashRegisters (st data scratch : BitVec 32) (len : Nat) (s : State) : Prop where
  state : s.gpr .ebx = st
  data : s.gpr .esi = data
  length : s.gpr .edi = BitVec.ofNat 32 len
  scratch : s.gpr .ebp = scratch

theorem HashRegisters.of_keeps {st data scratch : BitVec 32} {len : Nat} {s t : State} {rs : List Reg}
    (h : HashRegisters st data scratch len s) (K : Keeps rs s t)
    (preserved : ∀ r ∈ [.ebx, .esi, .edi, .ebp], r ∉ rs) : HashRegisters st data scratch len t :=
  ⟨(K.1 _ (preserved _ (by simp))).trans h.state, (K.1 _ (preserved _ (by simp))).trans h.data,
   (K.1 _ (preserved _ (by simp))).trans h.length, (K.1 _ (preserved _ (by simp))).trans h.scratch⟩

theorem HashRegisters.after {st data scratch : BitVec 32} {len : Nat} {s t : State} {ws : List Region}
    (h : HashRegisters st data scratch len s) (A : After s ws t) : HashRegisters st data scratch len t :=
  ⟨(A.cs _ (by decide)).trans h.state, (A.cs _ (by decide)).trans h.data,
   (A.cs _ (by decide)).trans h.length, (A.cs _ (by decide)).trans h.scratch⟩

theorem hash_update_setup {s : State} {st data scratch : BitVec 32} {len : Nat}
    (R : HashRegisters st data scratch len s) :
    WP isa (.block [.mov .edx (.reg .esi), .mov .ecx (.reg .edi), .mov .eax (.imm 0)]) s fun t =>
      HashRegisters st data scratch len t ∧ t.gpr .edx = data ∧ t.gpr .ecx = BitVec.ofNat 32 len ∧
      t.gpr .eax = 0 ∧ t.mem = s.mem ∧ Keeps [.edx, .ecx, .eax] s t := by
  refine wp_movS rfl fun u U _ => wp_movS rfl fun v V _ => wp_movS rfl fun t T _ => WP.block_nil ?_
  have K : Keeps [.edx, .ecx, .eax] s t :=
    ((U.keeps.mono (by decide)).trans (V.keeps.mono (by decide))).trans (T.keeps.mono (by decide))
  exact ⟨R.of_keeps K (by decide), by rw [T.other .edx (by decide), V.other .edx (by decide), U.gpr, R.data],
    by rw [T.other .ecx (by decide), V.gpr, U.other .edi (by decide), R.length], T.gpr,
    by rw [T.mem, V.mem, U.mem], K⟩

end VG.Proof.Dsa.X86.Generation
