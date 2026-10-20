module
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeRun
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeEffects
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeLoop
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeStatus

/-! # Start a fresh candidate's uniform-witness count -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Dsa.X86.Generation

theorem primeInit_ok {G : PrimeConfig} {s : State} (R : PrimeReady G s) :
    WP isa (.block primeInit) s fun t => PrimeReady G t ∧
      t.mem.readW (off G.base primeUniform) 32 = 0 ∧
      t.mem.readW (off G.base primeUsed) 32 = s.mem.readW (off G.base primeUsed) 32 ∧
      PrimeFrame G.base G.n (G.witness.setWidth 64) G.len s.mem t.mem ∧ Keeps powerClob s t := by
  have room : primeUniform + 4 ≤ G.size := by have := G.flagRoom; unfold primeUniform primeIsUniform at *; omega
  unfold primeInit
  apply WP.block_append
  refine wp_movS rfl fun a sa _ => ?_
  have Sa := R.context.scr.of_keeps sa.keeps (by decide)
  refine wp_storeS (Sa.ea (by omega)) (Sa.write room) fun b ab => WP.block_nil ?_
  have Kb : Keeps powerClob s b := (sa.keeps.mono (by decide)).trans (ab.keeps _)
  have Ob : Outside G.base primeUniform 4 s.mem b.mem := by
    rw [ab.mem, sa.mem]
    exact writeW32_outside _ _ _ (by have := R.context.scr.nowrap; omega)
  have Fb : PrimeFrame G.base G.n (G.witness.setWidth 64) G.len s.mem b.mem :=
    primeFrame_local (rs := [(primeUniform, 4)]) (Outs.of_outside Ob (by simp))
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; simp [primeWrites])
      G.width G.flagRoom (by have := R.context.scr.nowrap; omega)
  have cb : b.mem.readW (off G.base primeUniform) 32 = 0 := by rw [ab.mem, Mem.readW_writeW_self32, sa.gpr]
  have usedb : b.mem.readW (off G.base primeUsed) 32 = s.mem.readW (off G.base primeUsed) 32 := by
    apply BitVec.eq_of_toNat_eq; exact Ob.w32 (by decide) (by decide)
  refine WP.mono (primeMarkReady_ok (R.keep Fb Kb (by decide) (by decide)) 4)
    fun t ⟨Rt, _, count, used, F, K⟩ => ?_
  exact ⟨Rt, count.trans cb, used.trans usedb, Fb.trans F, Kb.trans K⟩

theorem primeLoop_ok {G : PrimeConfig} {s : State} {used : Nat} (R : PrimeReady G s)
    (used_le : used ≤ G.tapeLen)
    (consumed : s.mem.readW (off G.base primeUsed) 32 = BitVec.ofNat 32 used) :
    WP isa (primeLoop G.len G.draw G.checks) s fun t =>
      let result := primeRun G s.mem used 0
      PrimeReady G t ∧ result.status ≠ 4 ∧
      t.mem.readW (off G.base primeStatus) 32 = BitVec.ofNat 32 result.status ∧
      t.mem.readW (off G.base primeUniform) 32 = BitVec.ofNat 32 result.uniform ∧
      t.mem.readW (off G.base primeUsed) 32 = BitVec.ofNat 32 result.used ∧
      PrimeFrame G.base G.n (G.witness.setWidth 64) G.len s.mem t.mem ∧ Keeps powerClob s t := by
  unfold primeLoop
  refine WP.seq (WP.mono (primeInit_ok R) fun a ⟨Ra, count, useda, Fa, Ka⟩ => ?_)
  have positive : 0 < G.checks := by unfold PrimeConfig.checks Spec.Dsa.primeChecks; split <;> decide
  refine WP.mono (primeLoopBody_ok Ra used_le positive (useda.trans consumed) count)
    fun t ⟨Rt, terminal, status, uniform, usedt, Ft, Kt⟩ => ?_
  rw [primeRun_frame Fa] at terminal status uniform usedt
  exact ⟨Rt, terminal, status, uniform, usedt, Fa.trans Ft, Ka.trans Kt⟩
end VG.Proof.Dsa.X86.Generation
