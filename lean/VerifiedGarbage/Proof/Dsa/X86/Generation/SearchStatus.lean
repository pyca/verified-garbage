module
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Search
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # The search controller's public words and status transitions -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86 VG.Impl.Dsa.X86.Generation

structure SearchControl (base : Addr) (counter stride : Nat) (s : State) : Prop where
  scr : Scr s base 12
  count : s.mem.readW (off base 0) 32 = BitVec.ofNat 32 counter
  offset : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 (1 + counter * stride)

theorem SearchControl.unchanged {s t : State} {base : Addr} {counter stride : Nat} {rs : List Reg}
    (C : SearchControl base counter stride s) (mem : t.mem = s.mem) (K : Keeps rs s t)
    (di : .edi ∉ rs) (sp : .esp ∉ rs) : SearchControl base counter stride t :=
  ⟨C.scr.of_keeps K di sp, by rw [mem]; exact C.count, by rw [mem]; exact C.offset⟩

theorem pSearchStatus_ok {s : State} {base : Addr} {counter stride : Nat}
    (C : SearchControl base counter stride s) (status : Nat) :
    WP isa (.block (pSearchStatus status)) s fun t => SearchControl base counter stride t ∧
      t.mem.readW (off base 8) 32 = BitVec.ofNat 32 status ∧
      Outside base 0 12 s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold pSearchStatus
  refine wp_movS rfl fun a sa _ => ?_
  have Sa := C.scr.of_keeps sa.keeps (by decide)
  refine wp_storeS (Sa.ea (d := 8) (by decide)) (Sa.write (d := 8) (by decide)) fun t at' => WP.block_nil ?_
  have mem : t.mem = s.mem.writeW (off base 8) (BitVec.ofNat 32 status) := by rw [at'.mem, sa.gpr, sa.mem]
  have O : Outside base 8 4 s.mem t.mem := by rw [mem]; exact writeW32_outside _ _ _ (by decide)
  have K := sa.keeps.trans (at'.keeps [.eax])
  have fixed (d : Nat) (hd : d + 4 ≤ 8) : t.mem.readW (off base d) 32 = s.mem.readW (off base d) 32 := by
    apply BitVec.eq_of_toNat_eq; exact O.w32 (.inl hd) (by omega)
  exact ⟨⟨C.scr.of_keeps K (by decide), (fixed 0 (by decide)).trans C.count,
    (fixed 4 (by decide)).trans C.offset⟩, by rw [mem, Mem.readW_writeW_self32],
    O.mono (by omega) (by omega), K⟩

theorem pSearchStatusCmp_ok {s : State} {base : Addr} {counter stride status : Nat}
    (C : SearchControl base counter stride s) (bound : status ≤ 3)
    (saved : s.mem.readW (off base 8) 32 = BitVec.ofNat 32 status) :
    WP isa (.block pSearchStatusCmp) s fun t => t.zf = some (decide (status = 3)) ∧
      t.mem = s.mem ∧ Keeps [.eax] s t := by
  unfold pSearchStatusCmp
  refine wp_movS (v := BitVec.ofNat 32 status) (by rw [readSrc_sc C.scr (d := 8) (by decide), saved])
    fun a sa _ => wp_cmpi fun t at' _ zt => WP.block_nil ?_
  refine ⟨?_, at'.mem.trans sa.mem, sa.keeps.trans (at'.keeps _)⟩
  rw [zt, sa.gpr]
  change some (BitVec.ofNat 32 status - BitVec.ofNat 32 3 == (0 : BitVec 32)) = _
  rw [sub_beq (by omega) (by decide)]
end VG.Proof.Dsa.X86.Generation
