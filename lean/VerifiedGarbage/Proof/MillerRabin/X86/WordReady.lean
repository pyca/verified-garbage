module

public import VerifiedGarbage.Proof.MillerRabin.X86.TimingReady
public import VerifiedGarbage.Proof.MillerRabin.X86.WordLoad

/-! # Public exponent-word loads and loop tests preserve arithmetic readiness -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Mont.X86 VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt numAt)

theorem load_word_ready {σ s : State} {base : Addr} {bytes w i : Nat}
    (facts : RoundFacts σ base bytes w) (hi : i < 2 * w)
    (h : WindowReady σ base bytes w (8 * (i + 1)) s) :
    WP isa (.block wordLoad) s (WindowReady σ base bytes w (8 * (i + 1))) := by
  refine WP.mono (word_load facts h.stage hi
    (readW_of_w32 (by have := facts.upper; omega) h.count)) ?_
  rintro t ⟨stage, _, frame⟩
  have arrays (a : Nat) (ha : a < 28) := header_frame_num h.stage.context.ws.nowrap facts.fit ha
    (by decide : sV + 4 ≤ 256) frame
  have hdrFit : 256 ≤ bytes := Nat.le_trans (Nat.le_add_right _ _) facts.fit
  have headers (d : Nat) (hd : d + 4 ≤ 256) (sep : d + 4 ≤ sV ∨ sV + 4 ≤ d) :=
    workspace_frame_word h.stage.context.ws.nowrap (Nat.le_trans hd hdrFit)
      (Nat.le_trans (by decide : sV + 4 ≤ 256) hdrFit) sep frame
  refine ⟨⟨stage, by rw [arrays 6 (by decide)]; exact h.reduced, ?_⟩, ?_, ?_⟩
  · simpa only [w32, headers sF (by decide) (by decide)] using h.flag
  · simpa only [w32, headers sK (by decide) (by decide)] using h.count
  · intro j hj
    rw [arrays (11 + j) (by omega)]
    exact h.table j hj

theorem test_word_ready {σ s : State} {base : Addr} {bytes w k : Nat}
    (facts : RoundFacts σ base bytes w) (h : WindowReady σ base bytes w k s) (hk : k < 2 ^ 32) :
    WP isa (.block [.mov .eax (.mem (sc sK)), .alu .cmp .eax (.imm 0)]) s fun t =>
      WindowReady σ base bytes w k t ∧ t.zf = some (decide (k = 0)) := by
  refine wp_movS (by rw [h.stage.read_header facts.fit (by decide), readW_of_w32 hk h.count]) fun u U _ =>
    wp_cmpS rfl fun t Ut zt => WP.block_nil ?_
  have stage := (h.stage.of_registers U.keeps U.mem).of_registers
    (rs := []) ⟨fun r _ => congrFun Ut.gpr r, Ut.rd, Ut.wr⟩ Ut.mem
  have mem : t.mem = s.mem := Ut.mem.trans U.mem
  refine ⟨⟨⟨stage, by rw [mem]; exact h.reduced, by rw [mem]; exact h.flag⟩,
    by rw [mem]; exact h.count, by rw [mem]; exact h.table⟩, ?_⟩
  rw [zt, U.gpr, show BitVec.ofNat 32 k - 0 = BitVec.ofNat 32 k from BitVec.sub_zero _]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
  rfl

end VG.Proof.MillerRabin.X86
