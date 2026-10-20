module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Round
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
public import VerifiedGarbage.Proof.Mont.X86.ContextFrame
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Ecdsa.X86.Flags
import VerifiedGarbage.Proof.Dsa.X86.Checks

/-! # Terminal comparisons retain the minus-one result for the squaring loop -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation
open VG.Proof.Ecdsa.X86

theorem roundCompare_ok {s : State} {base : Addr} {size n m z : Nat}
    (h : Context n m base size s) (hn : n ≤ 48) (room : roundStatus + 4 ≤ size)
    (one : wordsVal s.mem base (slot n 3) n = 1)
    (minus : wordsVal s.mem base (slot n 8) n = m - 1)
    (value : wordsVal s.mem base (slot n 6) n = z) :
    WP isa (roundCompare n) s fun t =>
      t.zf = some (decide (¬ (z = 1 ∨ z = m - 1))) ∧
      t.mem.readW (off base roundStatus) 32 = mask32 (z = m - 1) ∧
      Outside base roundStatus 4 s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have nz := h.modulus.n0
  have bounds (j : Nat) (hj : j < 9) : slot n j + 8 * n ≤ size := by
    have := slot_bound (n := n) hj
    have := h.size_le
    simp only [stride] at *
    omega
  have far (j : Nat) (hj : j < 9) : slot n j + 8 * n ≤ roundStatus := by
    have := slot_bound (n := n) hj
    simp only [contextBytes, slot, stride, roundStatus] at *
    omega
  unfold roundCompare
  refine WP.seq (WP.mono (equal_ok n h.scr nz (bounds 6 (by decide)) (bounds 8 (by decide)))
    fun a ⟨ax, ka, ma⟩ => ?_)
  have sa := h.scr.of_keeps ka (by decide)
  refine WP.seq (wp_storeS (sa.ea (by omega)) (sa.write room) fun b ab => WP.block_nil ?_)
  have kb := ka.trans (ab.keeps _)
  have sb := h.scr.of_keeps kb (by decide)
  have ob : Outside base roundStatus 4 s.mem b.mem := by
    rw [ab.mem, ma]
    exact writeW32_outside _ _ _ (by have := h.scr.nowrap; omega)
  have vals (j : Nat) (hj : j < 9) : wordsVal b.mem base (slot n j) n = wordsVal s.mem base (slot n j) n := by
    rw [wordsVal_eq_val32, wordsVal_eq_val32]
    exact ob.val32 (by have := far j hj; omega) (by have := h.scr.nowrap; have := bounds j hj; omega)
  refine WP.seq (WP.mono (equal_ok n sb nz (bounds 6 (by decide)) (bounds 3 (by decide)))
    fun c ⟨cx, kc, mc⟩ => ?_)
  have sc := sb.of_keeps kc (by decide)
  refine wp_orS (readSrc_sc sc room) fun d cd => wp_cmpi fun t dt _ zt => WP.block_nil ?_
  have status : b.mem.readW (off base roundStatus) 32 = mask32 (z = m - 1) := by
    rw [ab.mem, Mem.readW_writeW_self32, ax, value, minus]
  have eq : d.gpr .edx = mask32 (z = 1) ||| mask32 (z = m - 1) := by
    rw [cd.gpr, cx, mc, status, vals 6 (by decide), vals 3 (by decide), value, one]
  refine ⟨?_, by rw [dt.mem, cd.mem, mc, status], ?_, ?_⟩
  · rw [zt, eq]
    by_cases h1 : z = 1 <;> by_cases hm : z = m - 1 <;> simp [mask32, h1, hm]
  · rw [dt.mem, cd.mem, mc]; exact ob
  · exact ((kb.trans kc).widen cd.keeps).trans (dt.keeps _)
end VG.Proof.Dsa.X86.Generation
