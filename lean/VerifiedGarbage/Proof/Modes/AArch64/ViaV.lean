module

public import VerifiedGarbage.Proof.Modes.AArch64.FbLoop
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# A register kept in a vector register around a core's code, on AArch64

`c.viaV r v` (`Impl/Modes/AArch64/Fb.lean`) copies `r` to the vector
register `v` before the core's `prepare` and `crypt` and back after. If no
instruction of the core writes `v` (`vSafe`, checked by evaluation, the
code of the functions it calls included), each
keeps `r` (`keepsReg_viaV`), whatever it does to `r` in between; and
`BlockSpec.viaV` is the core's `BlockSpec` for the wrapped core, if `r` is
none of the registers the core keeps for the modes and its key being ready
does not depend on `r`.
-/

@[expose] public section

namespace VG.Proof.Modes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Modes.AArch64
open VG.Impl.Aes.AArch64 (sb)

/-- Whether no instruction of `c` writes the vector register `v`, with no
calls or frames. -/
def vSafe (v : VReg) : Prog isa → Bool
  | .block is => is.all fun i => vdstOf i != some v
  | .seq a b => vSafe v a && vSafe v b
  | .ite _ a b => vSafe v a && vSafe v b
  | .loop b _ => vSafe v b
  | .call _ b => vSafe v b
  | _ => false

theorem vSafe_instrs {v : VReg} : ∀ {c : Prog isa}, vSafe v c = true → ∀ i ∈ instrs c, vdstOf i ≠ some v
  | .block is, hc, i, hi => by
    simp only [vSafe, List.all_eq_true] at hc; simpa using hc i hi
  | .seq a b, hc, i, hi => by
    simp only [vSafe, Bool.and_eq_true] at hc
    rcases List.mem_append.mp hi with hi | hi
    · exact vSafe_instrs hc.1 i hi
    · exact vSafe_instrs hc.2 i hi
  | .ite _ a b, hc, i, hi => by
    simp only [vSafe, Bool.and_eq_true] at hc
    rcases List.mem_append.mp hi with hi | hi
    · exact vSafe_instrs hc.1 i hi
    · exact vSafe_instrs hc.2 i hi
  | .loop b _, hc, i, hi => vSafe_instrs (c := b) hc i hi
  | .call _ b, hc, i, hi => vSafe_instrs (c := b) hc i hi
  | .frame _ _ _, hc, _, _ => by simp only [vSafe, Bool.false_eq_true] at hc
  | .icall .., hc, _, _ => by simp only [vSafe, Bool.false_eq_true] at hc

theorem keepsV_of_vSafe {v : VReg} {c : Prog isa} (hc : vSafe v c = true) :
    ∀ s t s', Exec isa c s t s' → s'.v v = s.v v :=
  fun _ _ _ h => Exec.vec (vSafe_instrs hc) h

/-- `dup v.2d, r`. -/
theorem dup_ok (s : State) (v : VReg) (r : Reg) :
    runBlock isa [.vop (.dup .d2 v r)] s = some (s.setV v (ofVDwords (s.gpr r) (s.gpr r))) := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VOp.eval, Option.map_some]

/-- `umov r, v.d[0]`. -/
theorem umov_ok (s : State) (r : Reg) (v : VReg) :
    runBlock isa [.umov .x r v 0] s = some (s.write .x r ((s.v v).extractLsb' 0 64)) := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits, Nat.zero_mul, Nat.mul_zero,
    show (0 : Nat) < 128 by decide, ite_true]

theorem extract_ofVDwords (x : BitVec 64) : (ofVDwords x x).extractLsb' 0 64 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [ofVDwords, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and,
    Nat.zero_add, ite_true]

/-- A one-instruction block's run. -/
theorem exec_of_single {i : Instr} {s s' : State} {t : List Leak} (b : execBlock isa [i] s = some (s', t)) :
    exec i s = some s' := by
  obtain ⟨s₁, e, w⟩ := WP.block_cons_iff.mp (⟨t, s', Exec.block b, rfl⟩ : WP isa (.block [i]) s (· = s'))
  rw [WP.block_nil_iff] at w
  subst w
  exact e

/-- The wrapped code keeps `r`, if the code between does not write `v`. -/
theorem keepsReg_wrap {r : Reg} {v : VReg} {p : Prog isa} (hp : vSafe v p = true) :
    KeepsReg r (.seq (.block [.vop (.dup .d2 v r)]) (.seq p (.block [.umov .x r v 0]))) := by
  intro s t s' h
  cases h with
  | seq e₁ e₂ =>
    cases e₁ with
    | block b₁ =>
      cases e₂ with
      | seq e₃ e₄ =>
        cases e₄ with
        | block b₄ =>
          have h₁ := exec_of_single b₁
          simp only [exec, VOp.eval, Option.map_some] at h₁
          obtain rfl := (Option.some.inj h₁)
          have h₄ := exec_of_single b₄
          simp only [exec, Size.bits, Nat.zero_mul, Nat.mul_zero, show (0 : Nat) < 128 by decide, ite_true] at h₄
          obtain rfl := (Option.some.inj h₄)
          rw [(write_ok _ _ _).1, keepsV_of_vSafe hp _ _ _ e₃, RegUpd.v_setV_self, extract_ofVDwords]

/-- The wrapped core's `prepare` and `crypt` keep `r`. -/
theorem keepsReg_viaV {c : Core} {r : Reg} {v : VReg} (hp : vSafe v c.prepare = true)
    (hc : vSafe v c.crypt = true) : KeepsReg r (c.viaV r v).prepare ∧ KeepsReg r (c.viaV r v).crypt :=
  ⟨keepsReg_wrap hp, keepsReg_wrap hc⟩

/-- What the wrapped code does: what the code between does, with `r` and `v`
changed. -/
theorem WP.wrap {r : Reg} {v : VReg} {p : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa p (s.setV v (ofVDwords (s.gpr r) (s.gpr r))) Q) :
    WP isa (.seq (.block [.vop (.dup .d2 v r)]) (.seq p (.block [.umov .x r v 0]))) s fun s' =>
      ∃ s₁, Q s₁ ∧ s' = s₁.write .x r ((s₁.v v).extractLsb' 0 64) :=
  WP.seq (WP.of_runBlock ⟨_, dup_ok s v r, WP.seq (WP.mono h fun s₁ q =>
    WP.of_runBlock ⟨_, umov_ok s₁ r v, s₁, q, rfl⟩)⟩)

variable {c : Core}

/-- The wrapped core meets the core's `BlockSpec`. -/
def BlockSpec.viaV (cs : BlockSpec c) {r : Reg} (v : VReg) (hsb : r ≠ sb) (hd : r ≠ c.dataReg)
    (hl : r ≠ c.leftReg)
    (hready : ∀ {s : State} {B : Addr} {k : cs.Key} (x : BitVec 64), cs.Ready s B k →
      cs.Ready (s.write .x r x) B k) :
    BlockSpec (c.viaV r v) where
  Key := cs.Key
  cipher := cs.cipher
  KeyArgs := cs.KeyArgs
  Ready := cs.Ready
  cipher_len := cs.cipher_len
  layout := let h := cs.layout; ⟨h.lgG_lt, h.bw_pos, h.bw_le, h.buf_le, h.room, h.small, h.bufImm⟩
  keyRegs_ok := cs.keyRegs_ok
  regs_ok := cs.regs_ok
  keyArgs_congr := cs.keyArgs_congr
  ready_frame := cs.ready_frame
  prepare_wp {s B rs k} hB hs hrs hk := by
    have hk₁ : cs.KeyArgs (s.setV v (ofVDwords (s.gpr r) (s.gpr r))) rs k :=
      cs.keyArgs_congr hk (fun _ _ => rfl) rfl rfl rfl (Frame.refl _ _)
    refine WP.mono (WP.wrap (cs.prepare_wp hB ⟨hs.wr, hs.fit⟩ hrs hk₁)) fun s' ⟨s₁, ⟨ready, b, dr, lr, f, rd, wr⟩, e⟩ => ?_
    subst e
    exact ⟨hready _ ready, by rw [(write_ok _ _ _).2.1 _ (Ne.symm hsb), b],
      by rw [(write_ok _ _ _).2.1 _ (Ne.symm hd), dr]; rfl, by rw [(write_ok _ _ _).2.1 _ (Ne.symm hl), lr]; rfl,
      f, rd, wr⟩
  crypt_wp {s B k} hB hs hr := by
    have hr₁ : cs.Ready (s.setV v (ofVDwords (s.gpr r) (s.gpr r))) B k :=
      cs.ready_frame hr (Frame.refl [] _) (fun _ h => by simp at h) ⟨fun _ h => by simp at h, rfl, rfl, rfl⟩ fun _ _ => rfl
    refine WP.mono (WP.wrap (cs.crypt_wp hB ⟨hs.wr, hs.fit⟩ hr₁)) fun s' ⟨s₁, ⟨b, dr, lr, ready, f, e, rd, wr⟩, he⟩ => ?_
    subst he
    exact ⟨by rw [(write_ok _ _ _).2.1 _ (Ne.symm hsb), b], by rw [(write_ok _ _ _).2.1 _ (Ne.symm hd), dr]; rfl,
      by rw [(write_ok _ _ _).2.1 _ (Ne.symm hl), lr]; rfl, hready _ ready, f, e, rd, wr⟩

end VG.Proof.Modes.AArch64
