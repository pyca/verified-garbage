module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Entry
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameWords
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Framework.Semantics

/-! # Select the SHA family and width using only the public modulus length -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86.Generation
open VG.Impl.Pbkdf2.Stream.X86 (Hash)

theorem dispatch_ok {H1 H256 : Hash} {name : String} {check : Prog isa}
    {s : State} {base : Addr} {W : Nat → BitVec 32} {Q : State → Prop}
    (F : SearchFrame s base) (R : FrameWords s.mem base W)
    (one : ∀ t, t.mem = s.mem → Keeps [.eax] s t → W 17 = 128 → WP isa (generate H1 name check 128 20) t Q)
    (two : ∀ t, t.mem = s.mem → Keeps [.eax] s t → W 17 = 256 → WP isa (generate H256 name check 256 32) t Q)
    (three : ∀ t, t.mem = s.mem → Keeps [.eax] s t → W 17 ≠ 128 → W 17 ≠ 256 →
      WP isa (generate H256 name check 384 32) t Q) :
    WP isa (dispatch H1 H256 name check) s Q := by
  unfold dispatch
  refine WP.seq (wp_movS (F.readWord R (by decide : 17 < 37)) fun a sa _ =>
    wp_cmpi fun b ab _ zb => WP.block_nil ?_)
  have Kb : Keeps [.eax] s b := sa.keeps.trans (ab.keeps _)
  have mb : b.mem = s.mem := ab.mem.trans sa.mem
  have first : b.zf = some (decide (W 17 = 128)) := by
    rw [zb, sa.gpr]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro h
      have h' := congrArg (fun x : BitVec 32 => x + 128) h
      rw [BitVec.sub_add_cancel] at h'
      exact h'.trans (by rfl)
    · intro h; rw [h]; rfl
  by_cases h1 : W 17 = 128
  · exact WP.ite true (by change b.zf = some true; rw [first]; simp only [h1, decide_true])
      (fun _ => one b mb Kb h1) (fun h => Bool.noConfusion h)
  · refine WP.ite false (by change b.zf = some false; rw [first]; congr 1; exact decide_eq_false h1)
      (fun h => Bool.noConfusion h) (fun _ => ?_)
    refine WP.seq (wp_cmpi fun c bc _ zc => WP.block_nil ?_)
    have Kc := Kb.trans (bc.keeps [.eax])
    have mc := bc.mem.trans mb
    have second : c.zf = some (decide (W 17 = 256)) := by
      rw [zc, ab.gpr, sa.gpr]
      congr 1
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, decide_eq_true_eq]
      constructor
      · intro h
        have h' := congrArg (fun x : BitVec 32 => x + 256) h
        rw [BitVec.sub_add_cancel] at h'
        exact h'.trans (by rfl)
      · intro h; rw [h]; rfl
    by_cases h2 : W 17 = 256
    · exact WP.ite true (by change c.zf = some true; rw [second]; simp only [h2, decide_true])
        (fun _ => two c mc Kc h2) (fun h => Bool.noConfusion h)
    · exact WP.ite false (by change c.zf = some false; rw [second]; congr 1; exact decide_eq_false h2)
        (fun h => Bool.noConfusion h) (fun _ => three c mc Kc h1 h2)
end VG.Proof.Dsa.X86.Generation
