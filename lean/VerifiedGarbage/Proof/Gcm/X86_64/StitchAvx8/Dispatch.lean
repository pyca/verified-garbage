import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Cursor
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Spec

/-! # Selecting a fixed schedule from the public round count -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch

private theorem cmpRound_ok (s : State) (n : Nat) (hn : n = 10 ∨ n = 12) :
    WP isa (.block [.alu .cmp .rsi (.imm (BitVec.ofNat 32 n))]) s fun t =>
      t.zf = some (decide (nr s = n)) ∧ YFrame [] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some, isa, Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩
  change some ((s.gpr .rsi - (BitVec.ofNat 32 n).signExtend 64) == 0) = _
  congr 1
  unfold nr
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq, decide_eq_true_eq]
  rcases hn with rfl | rfl
  · change s.gpr .rsi - (10 : BitVec 64) = 0 ↔ _
    bv_omega
  · change s.gpr .rsi - (12 : BitVec 64) = 0 ↔ _
    bv_omega

theorem pre_same {s t : State} (h : SPre s) (hf : YFrame [] s t) : SPre t := by
  rcases hf with ⟨hg, hm, hr, hw, _⟩
  cases s; cases t
  dsimp at hg hm hr hw
  cases hg; cases hm; cases hr; cases hw
  cases h
  constructor <;> with_reducible assumption

theorem epost_same {s t u : State} (hf : YFrame [] s t) (h : EPost t u) : EPost s u := by
  rcases hf with ⟨hg, hm, hr, hw, _⟩
  cases s; cases t
  dsimp at hg hm hr hw
  cases hg; cases hm; cases hr; cases hw
  cases h
  constructor <;> with_reducible assumption

theorem dpost_same {s t u : State} (hf : YFrame [] s t) (h : DPost t u) : DPost s u := by
  rcases hf with ⟨hg, hm, hr, hw, _⟩
  cases s; cases t
  dsimp at hg hm hr hw
  cases hg; cases hm; cases hr; cases hw
  cases h
  constructor <;> with_reducible assumption

theorem dispatch_ok {s : State} {a b c : Prog isa} {Q : State → Prop} (hp : SPre s)
    (ha : ∀ t, YFrame [] s t → nr s = 10 → WP isa a t Q)
    (hb : ∀ t, YFrame [] s t → nr s = 12 → WP isa b t Q)
    (hc : ∀ t, YFrame [] s t → nr s = 14 → WP isa c t Q) :
    WP isa (Impl.Gcm.X86_64.StitchAvx8.dispatch a b c) s Q := by
  refine WP.seq (WP.mono (cmpRound_ok s 10 (by decide)) fun t ⟨hz, hf⟩ => ?_)
  refine WP.ite (decide (nr s = 10)) (by simp only [eval, hz])
    (fun he => ha t hf (by simpa using he)) (fun he => ?_)
  have h10 : nr s ≠ 10 := by simpa using he
  refine WP.seq (WP.mono (cmpRound_ok t 12 (by decide)) fun u ⟨hz', hf'⟩ => ?_)
  have ht : nr t = nr s := by simp only [nr, hf.gpr]
  rw [ht] at hz'
  refine WP.ite (decide (nr s = 12)) (by simp only [eval, hz'])
    (fun he => hb u (hf.trans hf') (by simpa using he)) (fun he => ?_)
  have h12 : nr s ≠ 12 := by simpa using he
  exact hc u (hf.trans hf') (by rcases hp.rounds with he | he | he <;> omega)

end VG.Proof.Gcm.X86_64.StitchAvx8
