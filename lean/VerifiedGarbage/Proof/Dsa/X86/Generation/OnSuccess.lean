module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameWords
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Framework.Semantics

/-! # Continue a parameter-search phase only after its public success status -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem frameSuccess_ok {s : State} {base : Addr} {words : Nat → BitVec 32}
    (F : SearchFrame s base) (R : FrameWords s.mem base words) :
    WP isa (.block frameSuccess) s fun t => t.zf = some (decide (words 19 = 1)) ∧
      t.mem = s.mem ∧ Keeps [.eax] s t := by
  unfold frameSuccess
  refine wp_movS (F.readWord R (by decide : 19 < 37)) fun a sa _ =>
    wp_cmpi fun t at' _ zt => WP.block_nil ?_
  refine ⟨?_, at'.mem.trans sa.mem, sa.keeps.trans (at'.keeps _)⟩
  rw [zt, sa.gpr]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    have := congrArg (fun x : BitVec 32 => x + 1) h
    rw [BitVec.sub_add_cancel] at this
    exact this.trans (by rfl)
  · intro h; rw [h]; rfl

theorem onSuccess_ok {s : State} {base : Addr} {words : Nat → BitVec 32}
    {next : Prog isa} {Q : State → Prop}
    (F : SearchFrame s base) (R : FrameWords s.mem base words)
    (yes : ∀ t, t.mem = s.mem → Keeps [.eax] s t → words 19 = 1 → WP isa next t Q)
    (no : ∀ t, t.mem = s.mem → Keeps [.eax] s t → words 19 ≠ 1 → Q t) :
    WP isa (onSuccess next) s Q := by
  unfold onSuccess
  refine WP.seq (WP.mono (frameSuccess_ok F R) fun t ⟨zf, mem, K⟩ => ?_)
  by_cases good : words 19 = 1
  · exact WP.ite true (by change t.zf = some true; rw [zf]; simp only [good, decide_true]) (fun _ => yes t mem K good) (fun h => Bool.noConfusion h)
  · exact WP.ite false (by change t.zf = some false; rw [zf]; congr 1; exact decide_eq_false good) (fun h => Bool.noConfusion h) (fun _ => WP.block_nil (no t mem K good))
end VG.Proof.Dsa.X86.Generation
