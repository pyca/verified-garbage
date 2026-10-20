module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeReady
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PrimeControl
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeControl
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeEffects
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Prime-test status operations leave tape consumption and arithmetic intact -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

theorem primeMarkReady_ok {G : PrimeConfig} {s : State} (R : PrimeReady G s) (status : Nat) :
    WP isa (.block (primeMark status)) s fun t => PrimeReady G t ∧
      t.mem.readW (off G.base primeStatus) 32 = BitVec.ofNat 32 status ∧
      t.mem.readW (off G.base primeUniform) 32 = s.mem.readW (off G.base primeUniform) 32 ∧
      t.mem.readW (off G.base primeUsed) 32 = s.mem.readW (off G.base primeUsed) 32 ∧
      PrimeFrame G.base G.n (G.witness.setWidth 64) G.len s.mem t.mem ∧ Keeps powerClob s t := by
  have room : primeStatus + 4 ≤ G.size := by have := G.flagRoom; unfold primeStatus primeIsUniform at *; omega
  refine WP.mono (primeMark_ok R.context.scr room) fun t ⟨mem, O, K⟩ => ?_
  have F : PrimeFrame G.base G.n (G.witness.setWidth 64) G.len s.mem t.mem :=
    primeFrame_local (rs := [(primeStatus, 4)]) (Outs.of_outside O (by simp))
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; simp [primeWrites])
      G.width G.flagRoom (by have := R.context.scr.nowrap; omega)
  refine ⟨R.keep F K (by decide) (by decide), by rw [mem, Mem.readW_writeW_self32], ?_, ?_, F, K.mono (by decide)⟩
  · apply BitVec.eq_of_toNat_eq; exact O.w32 (by decide) (by decide)
  · apply BitVec.eq_of_toNat_eq; exact O.w32 (by decide) (by decide)

theorem primeStatusTest_ok {G : PrimeConfig} {s : State} {status : Nat} (R : PrimeReady G s)
    (bound : status < 2 ^ 32)
    (saved : s.mem.readW (off G.base primeStatus) 32 = BitVec.ofNat 32 status) :
    WP isa (.block [.mov .eax (.mem (sc primeStatus)), .alu .cmp .eax (.imm 4)]) s fun t =>
      t.zf = some (decide (status = 4)) ∧ t.mem = s.mem ∧ Keeps powerClob s t := by
  have room : primeStatus + 4 ≤ G.size := by have := G.flagRoom; unfold primeStatus primeIsUniform at *; omega
  refine wp_movS (v := BitVec.ofNat 32 status) (by rw [readSrc_sc R.context.scr room, saved])
    fun a sa _ => wp_cmpi fun t at' _ zt => WP.block_nil ?_
  refine ⟨?_, at'.mem.trans sa.mem, (sa.keeps.mono (by decide)).trans (at'.keeps _)⟩
  rw [zt, sa.gpr]
  change some (BitVec.ofNat 32 status - BitVec.ofNat 32 4 == (0 : BitVec 32)) = _
  rw [sub_beq bound (by decide)]
end VG.Proof.Dsa.X86.Generation
