module

public import VerifiedGarbage.Proof.MlKem.X86.Common
public import VerifiedGarbage.Proof.MlKem.X86.Top
import VerifiedGarbage.Proof.MlKem.X86.TopSeq
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlKem.KPke
import VerifiedGarbage.Proof.MlKem.X86.SampleSetup
import VerifiedGarbage.Proof.MlKem.X86.TopCall

/-! ### `MlKem.X86.TopHash`, which this module and modules that import it used -/

section

/-!
# ML-KEM on x86 (32-bit): SHA-3 and SHAKE in the top-level functions

The Keccak state set to zero (`zeroTop_piece`), the Keccak calls with their
arguments (`absorbC_piece`, `padC_piece`, `squeezeC_piece`), and a SHA-3 or
SHAKE function of one or two buffers (`hash1_piece`, `hash2_piece`): the
output is `squeezeFrom` of the padded state (`Proof/MlKem/KPke.lean`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86.Top

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem
open VG.Proof.Sha3.X86 (reg32)
open VG.Spec.Sha3 (Repr bytesAt stateAt squeezeFrom absorb pad rates)

variable {Y : Lay} {lk : State → List Byte} {A B : State → State → Prop}

/-- A loop of `N ≥ 1` iterations of a block, counting down with `sub ecx, 1`. -/
theorem wp_count {body : List Instr} {N : Nat} (hN : 0 < N) (I : Nat → State → Prop) {s : State}
    (h0 : I 0 s)
    (hs : ∀ k < N, ∀ s, I k s → WP isa (.block body) s fun s' => I (k + 1) s' ∧
      isa.eval .ne s' = some (decide (k + 1 < N))) :
    WP isa (.loop (.block body) .ne) s (I N) := by
  refine WP.loop (M := isa) (fun n (s : State) => ∃ k, n = N - k ∧ k < N ∧ I k s)
    (fun n s hi => ?_) N s ⟨0, (Nat.sub_zero N).symm, hN, h0⟩
  obtain ⟨k, hn, hk, hi⟩ := hi
  refine (hs k hk _ hi).mono fun s' ⟨hi', hc⟩ => ?_
  by_cases h : k + 1 < N
  · exact .inr ⟨by rw [hc, decide_eq_true h], N - (k + 1), by omega_using [hn, hk], k + 1, rfl, h, hi'⟩
  · exact .inl ⟨by rw [hc, decide_eq_false h], by rw [show N = k + 1 by omega_using [hk, h]]; exact hi'⟩

theorem wp_subi_last {d : Reg} {v : BitVec 32} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr d - v → s'.zf = some (s.gpr d - v == 0) → Q s') :
    WP isa (.block [.alu .sub d (.imm v)]) s Q := by
  refine wp_cons (s' := (arithFlags s (s.gpr d - v) (decide ((s.gpr d).toNat < v.toNat))
      (subOverflow (s.gpr d) v (s.gpr d - v))).setReg d (s.gpr d - v))
    (by simp only [exec, execAlu, readSrc, Option.bind_some]) (WP.block_nil_iff.mpr ?_)
  exact k _ (Only.flags s d _ _ _) (by simp [State.setReg]) rfl

/-! ## The Keccak state set to zero -/

theorem zeroTop_piece (st : Nat) (hc : Y.okW ⟨Y.sc, st, 200⟩ = true) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esi]) (zeroTop st) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame ([⟨Y.sc, st, 200⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 0]) s.mem s'.mem →
      stateAt s'.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩) = Spec.Sha3.zero → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (zeroTop st) := by
  obtain ⟨hc₁, hc₂⟩ := Lay.okW_iff.mp hc
  refine Piece.taint [.esi] (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp _ hq ha ha' r hr => ?_) tt
  · have h := hA s₀ s hp ha
    have fit : (Buf.ptr s₀ ⟨Y.sc, st, 200⟩).toNat + 200 ≤ 2 ^ 32 := Buf.fit hp hc₁
    refine WP.seq (wp_movr' fun s₁ o₁ v₁ => wp_addi fun s₂ o₂ v₂ => wp_movi fun s₃ o₃ v₃ =>
      wp_movi fun s₄ o₄ v₄ => WP.block_nil_iff.mpr ?_)
    have o := (((o₁.trans o₂).trans o₃).trans o₄).mono (es := [.edx, .eax, .ecx]) (by simp)
    have c₄ := h.only o (by decide) (by decide)
    let I : Nat → State → Prop := fun k u => Ctx Y s₀ u ∧
      u.gpr .edx = Buf.ptr s₀ ⟨Y.sc, st, 200⟩ + BitVec.ofNat 32 (4 * k) ∧ u.gpr .ecx = BitVec.ofNat 32 (50 - k) ∧
      u.gpr .eax = 0 ∧ Frame [Buf.rgn s₀ ⟨Y.sc, st, 200⟩] s.mem u.mem ∧
      ∀ j < 4 * k, u.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩ + BitVec.ofNat 64 j) = 0
    have i0 : I 0 s₄ := ⟨c₄, by rw [o₄.gpr _ (by decide), o₃.gpr _ (by decide), v₂, v₁, h.esi]; simp,
      v₄, by rw [o₄.gpr _ (by decide), v₃], by rw [o.mem]; exact Frame.refl _ _,
      fun j hj => absurd hj (by omega_using [])⟩
    refine (wp_count (N := 50) (by decide) I i0 fun k hk u hu => ?_).mono fun u hu => ?_
    · obtain ⟨cu, eu, ecu, eau, fu, zu⟩ := hu
      have ea : u.ea (at_ .edx 0) = Buf.addr s₀ ⟨Y.sc, st, 200⟩ + BitVec.ofNat 64 (4 * k) := by
        simp only [State.ea, at_, eu]
        rw [ea_add (by omega_using [fit, hk])]
        rfl
      have hin : InRegions u.wr (u.ea (at_ .edx 0)) 4 := by
        rw [ea]; exact Buf.inRegW hp hc₁ hc₂ cu.wr (by show 4 * k + 4 ≤ 200; omega_using [hk])
      obtain ⟨r, hr, hcr⟩ := Buf.contains hp hc₁ hc₂ (o := 4 * k) (n := 4) (by show 4 * k + 4 ≤ 200; omega_using [hk])
      have cm : Ctx Y s₀ { u with mem := u.mem.writeW (u.ea (at_ .edx 0)) (u.gpr .eax) } :=
        ⟨cu.esp, cu.rd, cu.wr, cu.esi, by rw [ea]; exact cu.frame.writeW hr _ hcr⟩
      refine wp_store hin (wp_addi fun u₁ o₁ v₁ => wp_subi_last fun u₂ o₂ v₂ z₂ => ?_)
      have cm₂ := (cm.only o₁ (by decide) (by decide)).only o₂ (by decide) (by decide)
      have m₂ : u₂.mem = u.mem.writeW (Buf.addr s₀ ⟨Y.sc, st, 200⟩ + BitVec.ofNat 64 (4 * k)) (0 : BitVec 32) := by
        rw [o₂.mem, o₁.mem, ← eau, ← ea]
      have x₂ : u₂.gpr .ecx = BitVec.ofNat 32 (50 - (k + 1)) := by
        rw [v₂, o₁.gpr _ (by decide)]; exact (congrArg (· - 1) ecu).trans (cnt_next hk)
      refine ⟨⟨cm₂, ?_, x₂, by rw [o₂.gpr _ (by decide), o₁.gpr _ (by decide)]; exact eau, ?_, ?_⟩, ?_⟩
      · rw [o₂.gpr _ (by decide), v₁, eu]
        show _ + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 4 = _
        rw [add_ofNat_add, show 4 * (k + 1) = 4 * k + 4 by omega_using []]
      · rw [m₂]
        exact fu.writeW (List.mem_singleton_self _) _ (by
          show (⟨Buf.addr s₀ ⟨Y.sc, st, 200⟩, 200⟩ : Region).Contains _ 4
          simp only [Region.Contains]; rw [Mem.sub_ofNat_toNat _ (by omega_using [hk])]; omega_using [hk])
      · rw [m₂]; exact Sample.zero_write zu
      · show u₂.zf.map (!·) = _
        have e₁ : u₁.gpr .ecx = BitVec.ofNat 32 (50 - k) := (o₁.gpr _ (by decide)).trans ecu
        rw [z₂, e₁]; exact cnt_ne hk (by decide)
    · obtain ⟨cu, -, -, -, fu, zu⟩ := hu
      exact hQ s₀ s u hp ha cu (fu.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inl hr, fun _ h => h⟩)
        (Sample.stateAt_zero fun j hj => zu j (by omega_using [hj]))
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [(hA _ _ hp ha).esi, (hA _ _ ‹_› ha').esi, hq.sc hp]

/-! ## The Keccak calls, with their arguments -/

theorem absorbC_piece (st wk rate pos : Nat) (b : Buf) (hr : rate ∈ rates) (hpos : pos < rate)
    (hc : (Y.okW ⟨Y.sc, st, 200⟩ && Y.okW ⟨Y.sc, wk, 640⟩ && Y.ok b && Y.sep ⟨Y.sc, st, 200⟩ ⟨Y.sc, wk, 640⟩ &&
      Y.sep b ⟨Y.sc, st, 200⟩ && Y.sep b ⟨Y.sc, wk, 640⟩) = true) (hN : 56 ≤ Y.stk) (hlen : b.len < 2 ^ 32)
    {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨Y.sc, st, 200⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 rate)), .mov .edx (.imm (BitVec.ofNat 32 pos))] : List Instr) ++
      ptrTo Y.sc .ebx b ++ ([.mov .ebp (.imm (BitVec.ofNat 32 b.len))] : List Instr) ++
      ptrTo Y.sc .edi ⟨Y.sc, wk, 640⟩)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame ([⟨Y.sc, st, 200⟩, ⟨Y.sc, wk, 640⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 40]) s.mem s'.mem →
      (∀ msg, Repr s.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩) rate msg → pos = msg.length % rate →
        Repr s'.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩) rate (msg ++ bytesAt s.mem (b.addr s₀) b.len)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (absorbC Y.sc st wk rate pos b) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, -⟩, -⟩, -⟩ := hc'
  refine Piece.seq (setup_piece (fun s₀ s₁ => AbsArgs s₁ (Buf.ptr s₀ ⟨Y.sc, st, 200⟩) (b.ptr s₀)
      (Buf.ptr s₀ ⟨Y.sc, wk, 640⟩) rate pos b.len) (fun s₀ s hp h => ?_) hA tt)
    (absorb_call Y.sc st Y.sc wk b rate pos hr hpos hc hN hlen (fun s₀ s₁ hp ⟨_, _, h₁, _, a₁⟩ => ⟨h₁, a₁⟩)
      fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr post => ?_)
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    refine ptrTo_ok hp h (Lay.okW_iff.mp h0).1 fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by decide) (by decide)
    refine wp_movi fun s₂ o₂ v₂ => wp_movi fun s₃ o₃ v₃ => ?_
    have c₃ := (c₁.only o₂ (by decide) (by decide)).only o₃ (by decide) (by decide)
    refine ptrTo_ok hp c₃ h2 fun s₄ o₄ v₄ => ?_
    have c₄ := c₃.only o₄ (by decide) (by decide)
    refine wp_movi fun s₅ o₅ v₅ => ?_
    have c₅ := c₄.only o₅ (by decide) (by decide)
    rw [← List.append_nil (ptrTo Y.sc .edi _)]
    refine ptrTo_ok hp c₅ (Lay.okW_iff.mp h1).1 fun s₆ o₆ v₆ => WP.block_nil_iff.mpr ?_
    refine ⟨c₅.only o₆ (by decide) (by decide),
      o₆.mem.trans (o₅.mem.trans (o₄.mem.trans (o₃.mem.trans (o₂.mem.trans o₁.mem)))), ⟨?_, ?_, ?_, ?_, ?_, v₆⟩⟩
    · rw [o₆.gpr _ (by decide), o₅.gpr _ (by decide), o₄.gpr _ (by decide), o₃.gpr _ (by decide),
        o₂.gpr _ (by decide), v₁]
    · rw [o₆.gpr _ (by decide), o₅.gpr _ (by decide), o₄.gpr _ (by decide), o₃.gpr _ (by decide), v₂]
    · rw [o₆.gpr _ (by decide), o₅.gpr _ (by decide), o₄.gpr _ (by decide), v₃]
    · rw [o₆.gpr _ (by decide), o₅.gpr _ (by decide), v₄]
    · rw [o₆.gpr _ (by decide), v₅]
  · rw [m₁] at fr post
    exact hQ s₀ s s' hp ha h' fr post

theorem padC_piece (st wk rate pos sfx : Nat) (hr : rate ∈ rates) (hpos : pos < rate)
    (hc : (Y.okW ⟨Y.sc, st, 200⟩ && Y.okW ⟨Y.sc, wk, 640⟩ && Y.sep ⟨Y.sc, st, 200⟩ ⟨Y.sc, wk, 640⟩) = true)
    (hN : 56 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨Y.sc, st, 200⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 rate)), .mov .edx (.imm (BitVec.ofNat 32 pos)),
        .mov .ebx (.imm (BitVec.ofNat 32 sfx))] : List Instr) ++ ptrTo Y.sc .edi ⟨Y.sc, wk, 640⟩)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame ([⟨Y.sc, st, 200⟩, ⟨Y.sc, wk, 640⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 40]) s.mem s'.mem →
      (∀ msg, Repr s.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩) rate msg → pos = msg.length % rate →
        stateAt s'.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩) =
          absorb rate (pad rate ((BitVec.ofNat 32 sfx).setWidth 8) msg)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (padC Y.sc st wk rate pos sfx) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨h0, h1⟩, -⟩ := hc'
  refine Piece.seq (setup_piece (fun s₀ s₁ => PadArgs s₁ (Buf.ptr s₀ ⟨Y.sc, st, 200⟩)
      (Buf.ptr s₀ ⟨Y.sc, wk, 640⟩) rate pos sfx) (fun s₀ s hp h => ?_) hA tt)
    (pad_call Y.sc st Y.sc wk rate pos sfx hr hpos hc hN (fun s₀ s₁ hp ⟨_, _, h₁, _, a₁⟩ => ⟨h₁, a₁⟩)
      fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr post => ?_)
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    refine ptrTo_ok hp h (Lay.okW_iff.mp h0).1 fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by decide) (by decide)
    refine wp_movi fun s₂ o₂ v₂ => wp_movi fun s₃ o₃ v₃ => wp_movi fun s₄ o₄ v₄ => ?_
    have c₄ := ((c₁.only o₂ (by decide) (by decide)).only o₃ (by decide) (by decide)).only o₄ (by decide)
      (by decide)
    rw [← List.append_nil (ptrTo Y.sc .edi _)]
    refine ptrTo_ok hp c₄ (Lay.okW_iff.mp h1).1 fun s₅ o₅ v₅ => WP.block_nil_iff.mpr ?_
    refine ⟨c₄.only o₅ (by decide) (by decide),
      o₅.mem.trans (o₄.mem.trans (o₃.mem.trans (o₂.mem.trans o₁.mem))), ⟨?_, ?_, ?_, ?_, v₅⟩⟩
    · rw [o₅.gpr _ (by decide), o₄.gpr _ (by decide), o₃.gpr _ (by decide), o₂.gpr _ (by decide), v₁]
    · rw [o₅.gpr _ (by decide), o₄.gpr _ (by decide), o₃.gpr _ (by decide), v₂]
    · rw [o₅.gpr _ (by decide), o₄.gpr _ (by decide), v₃]
    · rw [o₅.gpr _ (by decide), v₄]
  · rw [m₁] at fr post
    exact hQ s₀ s s' hp ha h' fr post

theorem squeezeC_piece (st wk rate : Nat) (o : Buf) (hr : rate ∈ rates)
    (hc : (Y.okW ⟨Y.sc, st, 200⟩ && Y.okW ⟨Y.sc, wk, 640⟩ && Y.okW o && Y.sep ⟨Y.sc, st, 200⟩ ⟨Y.sc, wk, 640⟩ &&
      Y.sep ⟨Y.sc, st, 200⟩ o && Y.sep o ⟨Y.sc, wk, 640⟩) = true) (hN : 56 ≤ Y.stk) (hlen : o.len < 2 ^ 32)
    {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨Y.sc, st, 200⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 rate)), .mov .edx (.imm 0)] : List Instr) ++
      ptrTo Y.sc .ebx o ++ ([.mov .ebp (.imm (BitVec.ofNat 32 o.len))] : List Instr) ++
      ptrTo Y.sc .edi ⟨Y.sc, wk, 640⟩)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame ([⟨Y.sc, st, 200⟩, o, ⟨Y.sc, wk, 640⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 40]) s.mem s'.mem →
      bytesAt s'.mem (o.addr s₀) o.len =
        squeezeFrom rate (stateAt s.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩)) 0 o.len → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (squeezeC Y.sc st wk rate o) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, -⟩, -⟩, -⟩ := hc'
  refine Piece.seq (setup_piece (fun s₀ s₁ => AbsArgs s₁ (Buf.ptr s₀ ⟨Y.sc, st, 200⟩) (o.ptr s₀)
      (Buf.ptr s₀ ⟨Y.sc, wk, 640⟩) rate 0 o.len) (fun s₀ s hp h => ?_) hA tt)
    (squeeze_call Y.sc st Y.sc wk o rate 0 hr (Nat.zero_le _) hc hN hlen
      (fun s₀ s₁ hp ⟨_, _, h₁, _, a₁⟩ => ⟨h₁, a₁⟩)
      fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr r₁ _ => ?_)
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    refine ptrTo_ok hp h (Lay.okW_iff.mp h0).1 fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by decide) (by decide)
    refine wp_movi fun s₂ o₂ v₂ => wp_movi fun s₃ o₃ v₃ => ?_
    have c₃ := (c₁.only o₂ (by decide) (by decide)).only o₃ (by decide) (by decide)
    refine ptrTo_ok hp c₃ (Lay.okW_iff.mp h2).1 fun s₄ o₄ v₄ => ?_
    have c₄ := c₃.only o₄ (by decide) (by decide)
    refine wp_movi fun s₅ o₅ v₅ => ?_
    have c₅ := c₄.only o₅ (by decide) (by decide)
    rw [← List.append_nil (ptrTo Y.sc .edi _)]
    refine ptrTo_ok hp c₅ (Lay.okW_iff.mp h1).1 fun s₆ o₆ v₆ => WP.block_nil_iff.mpr ?_
    refine ⟨c₅.only o₆ (by decide) (by decide),
      o₆.mem.trans (o₅.mem.trans (o₄.mem.trans (o₃.mem.trans (o₂.mem.trans o₁.mem)))), ⟨?_, ?_, ?_, ?_, ?_, v₆⟩⟩
    · rw [o₆.gpr _ (by decide), o₅.gpr _ (by decide), o₄.gpr _ (by decide), o₃.gpr _ (by decide),
        o₂.gpr _ (by decide), v₁]
    · rw [o₆.gpr _ (by decide), o₅.gpr _ (by decide), o₄.gpr _ (by decide), o₃.gpr _ (by decide), v₂]
    · rw [o₆.gpr _ (by decide), o₅.gpr _ (by decide), o₄.gpr _ (by decide), v₃]; rfl
    · rw [o₆.gpr _ (by decide), o₅.gpr _ (by decide), v₄]
    · rw [o₆.gpr _ (by decide), v₅]
  · rw [m₁] at fr r₁
    exact hQ s₀ s s' hp ha h' fr r₁

/-! ## Hashes -/

/-- The frame of the Keccak calls: the state, the working space and their stack. -/
abbrev kF (st wk : Nat) (Y : Lay) (s₀ : State) : List Region :=
  [⟨Y.sc, st, 200⟩, ⟨Y.sc, wk, 640⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 40]

theorem kF_zero {s₀ : State} (hp : TPre Y s₀) {st wk : Nat} (hN : 56 ≤ Y.stk) {m m' : Mem}
    (fr : Frame ([⟨Y.sc, st, 200⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 0]) m m') : Frame (kF st wk Y s₀) m m' :=
  fr.sub fun r hr => by
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨below (E1 s₀) 40, by simp, stk_sub hp (by omega_using []) (by omega_using [hN])⟩

theorem kF_bytes {s₀ : State} (hp : TPre Y s₀) {st wk : Nat} (hN : 56 ≤ Y.stk) {b : Buf} (hb : Y.ok b = true)
    (hs : (Y.okW ⟨Y.sc, st, 200⟩ && Y.okW ⟨Y.sc, wk, 640⟩ && Y.sep b ⟨Y.sc, st, 200⟩ && Y.sep b ⟨Y.sc, wk, 640⟩) = true)
    {m m' : Mem} (fr : Frame (kF st wk Y s₀) m m') : bytesAt m' (b.addr s₀) b.len = bytesAt m (b.addr s₀) b.len := by
  simp only [Bool.and_eq_true] at hs
  obtain ⟨⟨⟨h₁, h₂⟩, d₁⟩, d₂⟩ := hs
  exact bytesAt_frame fr (Buf.frD hp hb (bs := [⟨Y.sc, st, 200⟩, ⟨Y.sc, wk, 640⟩])
    (by simp [(Lay.okW_iff.mp h₁).1, (Lay.okW_iff.mp h₂).1, d₁, d₂]) (by omega_using [hN]))
    (by show b.len ≤ 2 ^ 64; have := Buf.fit hp hb; omega_using [this])

/-- The SHA-3 or SHAKE function (`rate`, suffix `sfx`) of the bytes of `b₁` and `b₂`, into `o`. -/
theorem hash2_piece (st wk rate sfx : Nat) (b₁ b₂ o : Buf) (hr : rate ∈ rates)
    (hc : (Y.okW ⟨Y.sc, st, 200⟩ && Y.okW ⟨Y.sc, wk, 640⟩ && Y.ok b₁ && Y.ok b₂ && Y.okW o &&
      Y.sep ⟨Y.sc, st, 200⟩ ⟨Y.sc, wk, 640⟩ && Y.sep b₁ ⟨Y.sc, st, 200⟩ && Y.sep b₁ ⟨Y.sc, wk, 640⟩ &&
      Y.sep b₂ ⟨Y.sc, st, 200⟩ && Y.sep b₂ ⟨Y.sc, wk, 640⟩ && Y.sep ⟨Y.sc, st, 200⟩ o &&
      Y.sep o ⟨Y.sc, wk, 640⟩) = true) (hN : 56 ≤ Y.stk)
    (hl₁ : b₁.len < 2 ^ 32) (hl₂ : b₂.len < 2 ^ 32) (hlo : o.len < 2 ^ 32)
    {h₀ h₁ h₂ h₃ h₄ : Taint.Hint VG.X86.Taint.T}
    (t₀ : (VG.X86.taint.check (τr [.esi]) (zeroTop st) h₀).isSome = true)
    (t₁ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨Y.sc, st, 200⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 rate)), .mov .edx (.imm (BitVec.ofNat 32 0))] : List Instr) ++
      ptrTo Y.sc .ebx b₁ ++ ([.mov .ebp (.imm (BitVec.ofNat 32 b₁.len))] : List Instr) ++
      ptrTo Y.sc .edi ⟨Y.sc, wk, 640⟩)) h₁).isSome = true)
    (t₂ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨Y.sc, st, 200⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 rate)), .mov .edx (.imm (BitVec.ofNat 32 (b₁.len % rate)))] : List Instr) ++
      ptrTo Y.sc .ebx b₂ ++ ([.mov .ebp (.imm (BitVec.ofNat 32 b₂.len))] : List Instr) ++
      ptrTo Y.sc .edi ⟨Y.sc, wk, 640⟩)) h₂).isSome = true)
    (t₃ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨Y.sc, st, 200⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 rate)), .mov .edx (.imm (BitVec.ofNat 32 ((b₁.len + b₂.len) % rate))),
        .mov .ebx (.imm (BitVec.ofNat 32 sfx))] : List Instr) ++ ptrTo Y.sc .edi ⟨Y.sc, wk, 640⟩)) h₃).isSome = true)
    (t₄ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨Y.sc, st, 200⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 rate)), .mov .edx (.imm 0)] : List Instr) ++
      ptrTo Y.sc .ebx o ++ ([.mov .ebp (.imm (BitVec.ofNat 32 o.len))] : List Instr) ++
      ptrTo Y.sc .edi ⟨Y.sc, wk, 640⟩)) h₄).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame ([⟨Y.sc, st, 200⟩, ⟨Y.sc, wk, 640⟩, o].map (Buf.rgn s₀) ++ [below (E1 s₀) 40]) s.mem s'.mem →
      bytesAt s'.mem (o.addr s₀) o.len = squeezeFrom rate (absorb rate (pad rate ((BitVec.ofNat 32 sfx).setWidth 8)
        (bytesAt s.mem (b₁.addr s₀) b₁.len ++ bytesAt s.mem (b₂.addr s₀) b₂.len))) 0 o.len → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (hash2 Y.sc st wk rate sfx b₁ b₂ o) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hS, hW⟩, hb₁⟩, hb₂⟩, hO⟩, dSW⟩, d₁S⟩, d₁W⟩, d₂S⟩, d₂W⟩, dSO⟩, dOW⟩ := hc'
  have hrate := (rate_lt hr)
  have hr0 : 0 < rate := by simp [rates] at hr; omega_using [hr]
  -- after zeroing, absorbing `b₁`, absorbing `b₂`, padding
  let P : Nat → State → State → Prop := fun i s₀ u => ∃ s, A s₀ s ∧ Ctx Y s₀ u ∧ Frame (kF st wk Y s₀) s.mem u.mem ∧
    (i = 0 → stateAt u.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩) = Spec.Sha3.zero) ∧
    (i = 1 → Repr u.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩) rate (bytesAt s.mem (b₁.addr s₀) b₁.len)) ∧
    (i = 2 → Repr u.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩) rate
      (bytesAt s.mem (b₁.addr s₀) b₁.len ++ bytesAt s.mem (b₂.addr s₀) b₂.len)) ∧
    (i = 3 → stateAt u.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩) = absorb rate (pad rate ((BitVec.ofNat 32 sfx).setWidth 8)
      (bytesAt s.mem (b₁.addr s₀) b₁.len ++ bytesAt s.mem (b₂.addr s₀) b₂.len)))
  have cS : (Y.okW ⟨Y.sc, st, 200⟩ && Y.okW ⟨Y.sc, wk, 640⟩ && Y.sep ⟨Y.sc, st, 200⟩ ⟨Y.sc, wk, 640⟩) = true := by
    simp [hS, hW, dSW]
  refine Piece.seq (B := P 0) (zeroTop_piece st hS t₀ hA fun s₀ s s' hp ha h' fr z =>
    ⟨s, ha, h', kF_zero hp hN fr, fun _ => z, by simp, by simp, by simp⟩) ?_
  refine Piece.seq (B := P 1) (absorbC_piece st wk rate 0 b₁ hr hr0 (by simp [hS, hW, hb₁, dSW, d₁S, d₁W])
    hN hl₁ t₁ (fun s₀ u _ ⟨_, _, h, _⟩ => h) fun s₀ u u' hp ⟨s, ha, _, fu, z, _⟩ h' fr post => ?_) ?_
  · have r := post [] (repr_nil (z rfl)) (by simp)
    rw [List.nil_append, kF_bytes hp hN hb₁ (by simp [hS, hW, d₁S, d₁W]) fu] at r
    exact ⟨s, ha, h', fu.trans fr, by simp, fun _ => r, by simp, by simp⟩
  refine Piece.seq (B := P 2) (absorbC_piece st wk rate (b₁.len % rate) b₂ hr (Nat.mod_lt _ hr0)
    (by simp [hS, hW, hb₂, dSW, d₂S, d₂W]) hN hl₂ t₂ (fun s₀ u _ ⟨_, _, h, _⟩ => h)
    fun s₀ u u' hp ⟨s, ha, _, fu, _, r, _⟩ h' fr post => ?_) ?_
  · have r' := post _ (r rfl) (by rw [bytesAt_length])
    rw [kF_bytes hp hN hb₂ (by simp [hS, hW, d₂S, d₂W]) fu] at r'
    exact ⟨s, ha, h', fu.trans fr, by simp, by simp, fun _ => r', by simp⟩
  refine Piece.seq (B := P 3) (padC_piece st wk rate ((b₁.len + b₂.len) % rate) sfx hr (Nat.mod_lt _ hr0) cS hN t₃
    (fun s₀ u _ ⟨_, _, h, _⟩ => h) fun s₀ u u' hp ⟨s, ha, _, fu, _, _, r, _⟩ h' fr post => ?_) ?_
  · exact ⟨s, ha, h', fu.trans fr, by simp, by simp, by simp,
      fun _ => post _ (r rfl) (by rw [List.length_append, bytesAt_length, bytesAt_length])⟩
  refine squeezeC_piece st wk rate o hr (by simp [hS, hW, hO, dSW, dSO, dOW]) hN hlo t₄
    (fun s₀ u _ ⟨_, _, h, _⟩ => h) fun s₀ u u' hp ⟨s, ha, _, fu, _, _, _, z⟩ h' fr r₁ => ?_
  rw [z rfl] at r₁
  refine hQ s₀ s u' hp ha h' ((fu.sub fun r hr => ?_).trans (fr.sub fun r hr => ?_)) r₁
  · simp only [kF, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  · simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩

/-- The SHA-3 or SHAKE function (`rate`, suffix `sfx`) of the bytes of `b`, into `o`. -/
theorem hash1_piece (st wk rate sfx : Nat) (b o : Buf) (hr : rate ∈ rates)
    (hc : (Y.okW ⟨Y.sc, st, 200⟩ && Y.okW ⟨Y.sc, wk, 640⟩ && Y.ok b && Y.okW o &&
      Y.sep ⟨Y.sc, st, 200⟩ ⟨Y.sc, wk, 640⟩ && Y.sep b ⟨Y.sc, st, 200⟩ && Y.sep b ⟨Y.sc, wk, 640⟩ &&
      Y.sep ⟨Y.sc, st, 200⟩ o && Y.sep o ⟨Y.sc, wk, 640⟩) = true) (hN : 56 ≤ Y.stk)
    (hl : b.len < 2 ^ 32) (hlo : o.len < 2 ^ 32)
    {h₀ h₁ h₃ h₄ : Taint.Hint VG.X86.Taint.T}
    (t₀ : (VG.X86.taint.check (τr [.esi]) (zeroTop st) h₀).isSome = true)
    (t₁ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨Y.sc, st, 200⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 rate)), .mov .edx (.imm (BitVec.ofNat 32 0))] : List Instr) ++
      ptrTo Y.sc .ebx b ++ ([.mov .ebp (.imm (BitVec.ofNat 32 b.len))] : List Instr) ++
      ptrTo Y.sc .edi ⟨Y.sc, wk, 640⟩)) h₁).isSome = true)
    (t₃ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨Y.sc, st, 200⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 rate)), .mov .edx (.imm (BitVec.ofNat 32 (b.len % rate))),
        .mov .ebx (.imm (BitVec.ofNat 32 sfx))] : List Instr) ++ ptrTo Y.sc .edi ⟨Y.sc, wk, 640⟩)) h₃).isSome = true)
    (t₄ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨Y.sc, st, 200⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 rate)), .mov .edx (.imm 0)] : List Instr) ++
      ptrTo Y.sc .ebx o ++ ([.mov .ebp (.imm (BitVec.ofNat 32 o.len))] : List Instr) ++
      ptrTo Y.sc .edi ⟨Y.sc, wk, 640⟩)) h₄).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame ([⟨Y.sc, st, 200⟩, ⟨Y.sc, wk, 640⟩, o].map (Buf.rgn s₀) ++ [below (E1 s₀) 40]) s.mem s'.mem →
      bytesAt s'.mem (o.addr s₀) o.len = squeezeFrom rate (absorb rate (pad rate ((BitVec.ofNat 32 sfx).setWidth 8)
        (bytesAt s.mem (b.addr s₀) b.len))) 0 o.len → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (hash1 Y.sc st wk rate sfx b o) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hS, hW⟩, hb⟩, hO⟩, dSW⟩, dbS⟩, dbW⟩, dSO⟩, dOW⟩ := hc'
  have hr0 : 0 < rate := by simp [rates] at hr; omega_using [hr]
  let P : Nat → State → State → Prop := fun i s₀ u => ∃ s, A s₀ s ∧ Ctx Y s₀ u ∧ Frame (kF st wk Y s₀) s.mem u.mem ∧
    (i = 0 → stateAt u.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩) = Spec.Sha3.zero) ∧
    (i = 1 → Repr u.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩) rate (bytesAt s.mem (b.addr s₀) b.len)) ∧
    (i = 3 → stateAt u.mem (Buf.addr s₀ ⟨Y.sc, st, 200⟩) = absorb rate (pad rate ((BitVec.ofNat 32 sfx).setWidth 8)
      (bytesAt s.mem (b.addr s₀) b.len)))
  have cS : (Y.okW ⟨Y.sc, st, 200⟩ && Y.okW ⟨Y.sc, wk, 640⟩ && Y.sep ⟨Y.sc, st, 200⟩ ⟨Y.sc, wk, 640⟩) = true := by
    simp [hS, hW, dSW]
  refine Piece.seq (B := P 0) (zeroTop_piece st hS t₀ hA fun s₀ s s' hp ha h' fr z =>
    ⟨s, ha, h', kF_zero hp hN fr, fun _ => z, by simp, by simp⟩) ?_
  refine Piece.seq (B := P 1) (absorbC_piece st wk rate 0 b hr hr0 (by simp [hS, hW, hb, dSW, dbS, dbW])
    hN hl t₁ (fun s₀ u _ ⟨_, _, h, _⟩ => h) fun s₀ u u' hp ⟨s, ha, _, fu, z, _⟩ h' fr post => ?_) ?_
  · have r := post [] (repr_nil (z rfl)) (by simp)
    rw [List.nil_append, kF_bytes hp hN hb (by simp [hS, hW, dbS, dbW]) fu] at r
    exact ⟨s, ha, h', fu.trans fr, by simp, fun _ => r, by simp⟩
  refine Piece.seq (B := P 3) (padC_piece st wk rate (b.len % rate) sfx hr (Nat.mod_lt _ hr0) cS hN t₃
    (fun s₀ u _ ⟨_, _, h, _⟩ => h) fun s₀ u u' hp ⟨s, ha, _, fu, _, r, _⟩ h' fr post => ?_) ?_
  · exact ⟨s, ha, h', fu.trans fr, by simp, by simp, fun _ => post _ (r rfl) (by rw [bytesAt_length])⟩
  refine squeezeC_piece st wk rate o hr (by simp [hS, hW, hO, dSW, dSO, dOW]) hN hlo t₄
    (fun s₀ u _ ⟨_, _, h, _⟩ => h) fun s₀ u u' hp ⟨s, ha, _, fu, _, _, z⟩ h' fr r₁ => ?_
  rw [z rfl] at r₁
  refine hQ s₀ s u' hp ha h' ((fu.sub fun r hr => ?_).trans (fr.sub fun r hr => ?_)) r₁
  · simp only [kF, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  · simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩

end VG.Proof.MlKem.X86.Top

end

end

/-!
# ML-KEM on x86 (32-bit): the code of the top-level functions between calls

Storing a byte in `scratch` (`st8_piece`), copying words (`copyW_piece`), and,
after a call of `vg_mlkem_sample_ntt`, keeping the AND of the values it
returned and masking the polynomial it sampled (`maskA_piece`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86.Top

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem
open VG.Proof.Sha3.X86 (reg32)
open VG.Spec.Sha3 (bytesAt)

variable {Y : Lay} {lk : State → List Byte} {A B : State → State → Prop}

theorem wp_andr {d r : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr d &&& s.gpr r → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.reg r) :: is)) s Q :=
  wp_cons (s' := (arithFlags s (s.gpr d &&& s.gpr r) false false).setReg d (s.gpr d &&& s.gpr r))
    (by simp only [exec, execAlu, readSrc, Option.bind_some])
    (k _ (Only.flags s d _ _ _) (by simp [State.setReg]))

theorem wp_subr {d r : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr d - s.gpr r → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.reg r) :: is)) s Q :=
  wp_cons (s' := (arithFlags s (s.gpr d - s.gpr r) (decide ((s.gpr d).toNat < (s.gpr r).toNat))
      (subOverflow (s.gpr d) (s.gpr r) (s.gpr d - s.gpr r))).setReg d (s.gpr d - s.gpr r))
    (by simp only [exec, execAlu, readSrc, Option.bind_some])
    (k _ (Only.flags s d _ _ _) (by simp [State.setReg]))

theorem wp_store' {b r : Reg} {disp : Nat} {is : List Instr} {s : State} {Q : State → Prop}
    (hin : InRegions s.wr (s.ea (at_ b disp)) 4)
    (k : ∀ s', (∀ x, s'.gpr x = s.gpr x) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = s.mem.writeW (s.ea (at_ b disp)) (s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.store (at_ b disp) r :: is)) s Q :=
  wp_store hin (k _ (fun _ => rfl) rfl rfl rfl)

theorem wp_store8 {b : Reg} {r : Reg8} {disp : Nat} {is : List Instr} {s : State} {Q : State → Prop}
    (hin : InRegions s.wr (s.ea (at_ b disp)) 1)
    (k : WP isa (.block is) { s with mem := s.mem.writeW (s.ea (at_ b disp)) ((s.gpr r.reg).setWidth 8) } Q) :
    WP isa (.block (.store8 (at_ b disp) r :: is)) s Q :=
  wp_cons (by simp only [exec, State.store8, hin, ite_true]) k

/-! ## A byte -/

theorem st8_piece (o v : Nat) (hc : Y.okW ⟨Y.sc, o, 1⟩ = true) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esi]) (.block (st8 o v)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      s'.mem = s.mem.writeW (Buf.addr s₀ ⟨Y.sc, o, 1⟩) ((BitVec.ofNat 32 v).setWidth 8) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (.block (st8 o v)) := by
  obtain ⟨hc₁, hc₂⟩ := Lay.okW_iff.mp hc
  refine Piece.taint [.esi] (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp _ hq ha ha' r hr => ?_) tt
  · have h := hA s₀ s hp ha
    obtain ea : (s.gpr .esi + BitVec.ofNat 32 o).setWidth 64 = Buf.addr s₀ ⟨Y.sc, o, 1⟩ := by rw [h.esi]
    obtain ⟨r, hr, hcr⟩ := Buf.contains hp hc₁ hc₂ (o := 0) (n := 1) (Nat.le_refl _)
    simp only [BitVec.add_zero] at hcr
    obtain hin : InRegions s.wr (Buf.addr s₀ ⟨Y.sc, o, 1⟩) 1 := by
      have := Buf.inRegW hp hc₁ hc₂ h.wr (o := 0) (n := 1) (Nat.le_refl _)
      simpa using this
    refine wp_movi fun s₁ o₁ v₁ => ?_
    obtain h₁ := h.only o₁ (by decide) (by decide)
    obtain ea₁ : s₁.ea (at_ .esi o) = Buf.addr s₀ ⟨Y.sc, o, 1⟩ := by
      simp only [State.ea, at_]; rw [o₁.gpr _ (by decide)]; exact ea
    refine wp_store8 (by rw [ea₁, h₁.wr, ← h.wr]; exact hin) (WP.block_nil_iff.mpr ?_)
    refine hQ s₀ s _ hp ha ⟨h₁.esp, h₁.rd, h₁.wr, h₁.esi, ?_⟩ ?_
    · show Frame _ _ (s₁.mem.writeW _ _)
      rw [ea₁]; exact h₁.frame.writeW (w := 8) hr _ hcr
    · show s₁.mem.writeW _ _ = _
      rw [ea₁, o₁.mem, show s₁.gpr Reg8.al.reg = BitVec.ofNat 32 v from v₁]
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [(hA _ _ hp ha).esi, (hA _ _ ‹_› ha').esi, hq.sc hp]

/-! ## Copying words -/

/-- The bytes after a word is written at offset `4k`. -/
theorem wordw_bytes {m : Mem} {d : Addr} {w : BitVec 32} {k j : Nat} (hk : 4 * k + 4 < 2 ^ 64)
    (hj : j < 4 * k + 4) :
    (m.writeW (d + BitVec.ofNat 64 (4 * k)) w) (d + BitVec.ofNat 64 j) =
      if 4 * k ≤ j then w.extractLsb' (8 * (j - 4 * k)) 8 else m (d + BitVec.ofNat 64 j) := by
  simp only [Mem.writeW, Mem.write]
  by_cases e : 4 * k ≤ j
  · have t : (d + BitVec.ofNat 64 j - (d + BitVec.ofNat 64 (4 * k))).toNat = j - 4 * k := by
      rw [show d + BitVec.ofNat 64 j - (d + BitVec.ofNat 64 (4 * k)) = BitVec.ofNat 64 (j - 4 * k) by
        rw [show j = 4 * k + (j - 4 * k) by omega_using [e], BitVec.ofNat_add]; bv_omega]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hj])]
    rw [ite_eq_left e, t, ite_eq_left (by omega_using [hj])]
    rfl
  · rw [ite_eq_right e, ite_eq_right fun h => ?_]
    obtain t : (d + BitVec.ofNat 64 j - (d + BitVec.ofNat 64 (4 * k))).toNat = 2 ^ 64 - (4 * k - j) := by
      have : d + BitVec.ofNat 64 j - (d + BitVec.ofNat 64 (4 * k)) = BitVec.ofNat 64 j - BitVec.ofNat 64 (4 * k) := by
        bv_omega
      rw [this, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j) (by omega_using [hk, e]),
        Nat.mod_eq_of_lt (a := 4 * k) (by omega_using [hk])]
      omega_using [hk, e]
    rw [t] at h
    omega_using [hk, h]

theorem copyW_piece (sa so da dO n : Nat) (hn : 0 < n) (_hn' : n < 2 ^ 30)
    (hc : (Y.ok ⟨sa, so, 4 * n⟩ && Y.okW ⟨da, dO, 4 * n⟩ && Y.sep ⟨sa, so, 4 * n⟩ ⟨da, dO, 4 * n⟩) = true)
    {h₁ h₂ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .edi ⟨sa, so, 4 * n⟩ ++
      ptrTo Y.sc .ebp ⟨da, dO, 4 * n⟩ ++ ([.mov .ecx (.imm (BitVec.ofNat 32 n))] : List Instr))) h₁).isSome = true)
    (t₂ : (VG.X86.taint.check (τr [.edi, .ebp, .ecx]) (.loop (.block [.mov .eax (.mem (at_ .edi 0)),
      .store (at_ .ebp 0) .eax, .alu .add .edi (.imm 4), .alu .add .ebp (.imm 4), .alu .sub .ecx (.imm 1)]) .ne)
      h₂).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame [Buf.rgn s₀ ⟨da, dO, 4 * n⟩] s.mem s'.mem →
      bytesAt s'.mem (Buf.addr s₀ ⟨da, dO, 4 * n⟩) (4 * n) = bytesAt s.mem (Buf.addr s₀ ⟨sa, so, 4 * n⟩) (4 * n) →
      B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (copyW Y.sc ⟨sa, so, 4 * n⟩ ⟨da, dO, 4 * n⟩ n) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨hS, hD⟩, dSD⟩ := hc'
  obtain hD₁ := (Lay.okW_iff.mp hD).1
  let S : Buf := ⟨sa, so, 4 * n⟩
  let D : Buf := ⟨da, dO, 4 * n⟩
  refine Piece.seq (setup_piece (fun s₀ s₁ => s₁.gpr .edi = S.ptr s₀ ∧ s₁.gpr .ebp = D.ptr s₀ ∧
      s₁.gpr .ecx = BitVec.ofNat 32 n) (fun s₀ s hp h => ?_) hA t₁) ?_
  · simp only [List.append_assoc]
    refine ptrTo_ok hp h hS fun s₁ o₁ v₁ => ?_
    obtain c₁ := h.only o₁ (by decide) (by decide)
    refine ptrTo_ok hp c₁ hD₁ fun s₂ o₂ v₂ => ?_
    obtain c₂ := c₁.only o₂ (by decide) (by decide)
    refine wp_movi fun s₃ o₃ v₃ => WP.block_nil_iff.mpr ?_
    exact ⟨c₂.only o₃ (by decide) (by decide), o₃.mem.trans (o₂.mem.trans o₁.mem),
      by rw [o₃.gpr _ (by decide), o₂.gpr _ (by decide), v₁], by rw [o₃.gpr _ (by decide), v₂], v₃⟩
  refine Piece.taint [.edi, .ebp, .ecx] (fun s₀ s₁ hp ⟨s, ha, h₁, m₁, e₁, e₂, e₃⟩ => ?_)
    (fun s₀ s₀' s s' hp hp' hq ⟨_, _, _, _, e₁, e₂, e₃⟩ ⟨_, _, _, _, e₁', e₂', e₃'⟩ r hr => ?_) t₂
  · have fS : (S.ptr s₀).toNat + 4 * n ≤ 2 ^ 32 := Buf.fit hp hS
    obtain fD : (D.ptr s₀).toNat + 4 * n ≤ 2 ^ 32 := Buf.fit hp hD₁
    obtain dd := Buf.disj hp hS hD₁ dSD
    let I : Nat → State → Prop := fun k u => Ctx Y s₀ u ∧ u.gpr .edi = S.ptr s₀ + BitVec.ofNat 32 (4 * k) ∧
      u.gpr .ebp = D.ptr s₀ + BitVec.ofNat 32 (4 * k) ∧ u.gpr .ecx = BitVec.ofNat 32 (n - k) ∧
      Frame [D.rgn s₀] s.mem u.mem ∧ ∀ j < 4 * k, u.mem (D.addr s₀ + BitVec.ofNat 64 j) = s.mem (S.addr s₀ + BitVec.ofNat 64 j)
    obtain i0 : I 0 s₁ := ⟨h₁, by rw [e₁]; simp, by rw [e₂]; simp, e₃, by rw [m₁]; exact Frame.refl _ _,
      fun j hj => absurd hj (by omega_using [])⟩
    refine (wp_count hn I i0 fun k hk u ⟨cu, du, bu, xu, fu, cpu⟩ => ?_).mono fun u ⟨cu, _, _, _, fu, cpu⟩ => ?_
    · have eS : u.ea (at_ .edi 0) = S.addr s₀ + BitVec.ofNat 64 (4 * k) := by
        simp only [State.ea, at_, du]; rw [ea_add (by omega_using [fS, hk])]; rfl
      obtain eD : u.ea (at_ .ebp 0) = D.addr s₀ + BitVec.ofNat 64 (4 * k) := by
        simp only [State.ea, at_, bu]; rw [ea_add (by omega_using [fD, hk])]; rfl
      obtain hinS : InRegions (u.rd ++ u.wr) (S.addr s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
        Buf.inRegR hp hS cu.rd cu.wr (show 4 * k + 4 ≤ 4 * n by omega_using [hk])
      refine wp_movm' (by rw [eS]; exact hinS) fun u₁ o₁ v₁ => ?_
      obtain c₁ := cu.only o₁ (by decide) (by decide)
      obtain eD₁ : u₁.ea (at_ .ebp 0) = D.addr s₀ + BitVec.ofNat 64 (4 * k) := by
        rw [← eD]; simp only [State.ea, at_, o₁.gpr _ (by decide : Reg.ebp ∉ [Reg.eax])]
      obtain hinD : InRegions u₁.wr (D.addr s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
        Buf.inRegW hp hD₁ (Lay.okW_iff.mp hD).2 c₁.wr (show 4 * k + 4 ≤ 4 * n by omega_using [hk])
      refine wp_store' (by rw [eD₁]; exact hinD) fun u₂ g₂ r₂ w₂ m₂ => ?_
      obtain ⟨r, hr, hcr⟩ := Buf.contains hp hD₁ (Lay.okW_iff.mp hD).2 (o := 4 * k) (n := 4)
        (show 4 * k + 4 ≤ 4 * n by omega_using [hk])
      obtain c₂ : Ctx Y s₀ u₂ := ⟨by rw [g₂]; exact c₁.esp, by rw [r₂]; exact c₁.rd, by rw [w₂]; exact c₁.wr,
        by rw [g₂]; exact c₁.esi, by rw [m₂, eD₁]; exact c₁.frame.writeW hr _ hcr⟩
      refine wp_addi fun u₃ o₃ v₃ => wp_addi fun u₄ o₄ v₄ => wp_subi_last fun u₅ o₅ v₅ z₅ => ?_
      obtain c₅ := ((c₂.only o₃ (by decide) (by decide)).only o₄ (by decide) (by decide)).only o₅ (by decide)
        (by decide)
      obtain m₅ : u₅.mem = u₁.mem.writeW (D.addr s₀ + BitVec.ofNat 64 (4 * k)) (u.mem.readW (S.addr s₀ +
          BitVec.ofNat 64 (4 * k)) 32) := by
        rw [o₅.mem, o₄.mem, o₃.mem, m₂, eD₁, v₁, eS]
      obtain ex : u₄.gpr .ecx = BitVec.ofNat 32 (n - k) := by
        rw [o₄.gpr _ (by decide), o₃.gpr _ (by decide), g₂, o₁.gpr _ (by decide), xu]
      refine ⟨⟨c₅, ?_, ?_, by rw [v₅, ex]; exact cnt_next hk, ?_, ?_⟩, ?_⟩
      · rw [o₅.gpr _ (by decide), o₄.gpr _ (by decide), v₃, g₂, o₁.gpr _ (by decide), du]
        show _ + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 4 = _
        rw [add_ofNat_add, show 4 * (k + 1) = 4 * k + 4 by omega_using []]
      · rw [o₅.gpr _ (by decide), v₄, o₃.gpr _ (by decide), g₂, o₁.gpr _ (by decide), bu]
        show _ + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 4 = _
        rw [add_ofNat_add, show 4 * (k + 1) = 4 * k + 4 by omega_using []]
      · rw [m₅, o₁.mem]
        exact fu.writeW (List.mem_singleton_self _) _ (by
          show (⟨D.addr s₀, 4 * n⟩ : Region).Contains _ 4
          simp only [Region.Contains]; rw [Mem.sub_ofNat_toNat _ (by omega_using [fD, hk])]; omega_using [hk])
      · intro j hj
        rw [m₅, o₁.mem, wordw_bytes (by omega_using [fD, hk]) hj]
        split
        · rename_i e
          rw [← Mem.readW_byte _ _ (by omega_using [hj]), BitVec.add_assoc, ← BitVec.ofNat_add,
            show 4 * k + (j - 4 * k) = j by omega_using [e]]
          exact fu.bytes (R := S.rgn s₀) (fun r hr => by
            rw [List.mem_singleton] at hr; subst hr; exact dd) (by show 4 * n ≤ 2 ^ 64; omega_using [fD])
            (show j < 4 * n by omega_using [hk, hj])
        · exact cpu j (by omega_arith)
      · show u₅.zf.map (!·) = _
        rw [z₅, ex]; exact cnt_ne hk (by omega_using [fD])
    · refine hQ s₀ s u hp ha cu fu ?_
      exact List.map_congr_left fun j hj => cpu j (List.mem_range.mp hj)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [e₁, e₁', hq.ptr hS]
    · rw [e₂, e₂', hq.ptr hD₁]
    · rw [e₃, e₃']

/-! ## After `SampleNTT` -/

theorem maskA_piece (ao po : Nat)
    (hc : (Y.okW ⟨Y.sc, ao, 4⟩ && Y.okW ⟨Y.sc, po, 1024⟩ && Y.sep ⟨Y.sc, ao, 4⟩ ⟨Y.sc, po, 1024⟩) = true)
    {ht : Taint.Hint VG.X86.Taint.T} (tt : (VG.X86.taint.check (τr [.esi]) (maskA ao po) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame [Buf.rgn s₀ ⟨Y.sc, ao, 4⟩, Buf.rgn s₀ ⟨Y.sc, po, 1024⟩] s.mem s'.mem →
      s'.mem.readW (Buf.addr s₀ ⟨Y.sc, ao, 4⟩) 32 = s.mem.readW (Buf.addr s₀ ⟨Y.sc, ao, 4⟩) 32 &&& s.gpr .eax →
      (∀ i < 256, coeffAt s'.mem (Buf.addr s₀ ⟨Y.sc, po, 1024⟩) i =
        coeffAt s.mem (Buf.addr s₀ ⟨Y.sc, po, 1024⟩) i &&& (0 - s.gpr .eax)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (maskA ao po) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨hC, hP⟩, dCP⟩ := hc'
  obtain hC₁ := (Lay.okW_iff.mp hC).1
  obtain hP₁ := (Lay.okW_iff.mp hP).1
  let C : Buf := ⟨Y.sc, ao, 4⟩
  let P : Buf := ⟨Y.sc, po, 1024⟩
  refine Piece.taint [.esi] (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp _ hq ha ha' r hr => ?_) tt
  · have h := hA s₀ s hp ha
    obtain dd := Buf.disj hp hC₁ hP₁ dCP
    obtain fP : (P.ptr s₀).toNat + 1024 ≤ 2 ^ 32 := Buf.fit hp hP₁
    obtain eC : ∀ u : State, u.gpr .esi = arg s₀ Y.sc → u.ea (at_ .esi ao) = C.addr s₀ := fun u e => by
      simp only [State.ea, at_, e]; rfl
    obtain ⟨rC, hrC, hcC⟩ := Buf.contains hp hC₁ (Lay.okW_iff.mp hC).2 (o := 0) (n := 4) (Nat.le_refl _)
    simp only [BitVec.add_zero] at hcC
    obtain inC : InRegions (s.rd ++ s.wr) (C.addr s₀) 4 := by
      have := Buf.inRegR hp hC₁ h.rd h.wr (o := 0) (n := 4) (Nat.le_refl _)
      simpa using this
    obtain inCw : InRegions s.wr (C.addr s₀) 4 := by
      have := Buf.inRegW hp hC₁ (Lay.okW_iff.mp hC).2 h.wr (o := 0) (n := 4) (Nat.le_refl _)
      simpa using this
    refine WP.seq (wp_movi fun s₁ o₁ v₁ => wp_subr fun s₂ o₂ v₂ => ?_)
    obtain c₂ := (h.only o₁ (by decide) (by decide)).only o₂ (by decide) (by decide)
    obtain inC₂ : InRegions (s₂.rd ++ s₂.wr) (C.addr s₀) 4 := by
      have := Buf.inRegR hp hC₁ c₂.rd c₂.wr (o := 0) (n := 4) (Nat.le_refl _)
      simpa using this
    refine wp_movm' (by rw [eC s₂ c₂.esi]; exact inC₂) fun s₃ o₃ v₃ => ?_
    obtain c₃ := c₂.only o₃ (by decide) (by decide)
    refine wp_andr fun s₄ o₄ v₄ => ?_
    obtain c₄ := c₃.only o₄ (by decide) (by decide)
    refine wp_store' (by rw [eC s₄ c₄.esi, c₄.wr, ← h.wr]; exact inCw) fun s₅ g₅ r₅ w₅ m₅ => ?_
    obtain c₅ : Ctx Y s₀ s₅ := ⟨by rw [g₅]; exact c₄.esp, by rw [r₅]; exact c₄.rd, by rw [w₅]; exact c₄.wr,
      by rw [g₅]; exact c₄.esi, by rw [m₅, eC s₄ c₄.esi]; exact c₄.frame.writeW hrC _ hcC⟩
    refine wp_movr' fun s₆ o₆ v₆ => wp_addi fun s₇ o₇ v₇ => wp_movi fun s₈ o₈ v₈ => WP.block_nil_iff.mpr ?_
    obtain c₈ := ((c₅.only o₆ (by decide) (by decide)).only o₇ (by decide) (by decide)).only o₈ (by decide)
      (by decide)
    -- the state after the first block
    obtain rE : s₈.gpr .edx = 0 - s.gpr .eax := by
      rw [o₈.gpr _ (by decide), o₇.gpr _ (by decide), o₆.gpr _ (by decide), g₅, o₄.gpr _ (by decide),
        o₃.gpr _ (by decide), v₂, v₁, o₁.gpr _ (by decide)]
    obtain m₈ : s₈.mem = s.mem.writeW (C.addr s₀) (s.mem.readW (C.addr s₀) 32 &&& s.gpr .eax) := by
      rw [o₈.mem, o₇.mem, o₆.mem, m₅, eC s₄ c₄.esi, v₄, v₃, eC s₂ c₂.esi, o₃.gpr _ (by decide),
        o₂.gpr _ (by decide), o₁.gpr _ (by decide), o₄.mem, o₃.mem, o₂.mem, o₁.mem]
    obtain fC : Frame [C.rgn s₀] s.mem s₈.mem := by
      rw [m₈]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    obtain cP : ∀ i < 256, coeffAt s₈.mem (P.addr s₀) i = coeffAt s.mem (P.addr s₀) i := fun i hi =>
      Frame.readW fC (coeff_contains _ (show i < n by rw [n_eq]; exact hi)) (fun r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact dd.symm) (by decide)
    obtain aC : s₈.mem.readW (C.addr s₀) 32 = s.mem.readW (C.addr s₀) 32 &&& s.gpr .eax := by
      rw [m₈]; exact Mem.readW_writeW_self32 _ _ _
    let I : Nat → State → Prop := fun k u => Ctx Y s₀ u ∧ u.gpr .edi = P.ptr s₀ + BitVec.ofNat 32 (4 * k) ∧
      u.gpr .ecx = BitVec.ofNat 32 (256 - k) ∧ u.gpr .edx = 0 - s.gpr .eax ∧
      Frame [C.rgn s₀, P.rgn s₀] s.mem u.mem ∧ u.mem.readW (C.addr s₀) 32 = s.mem.readW (C.addr s₀) 32 &&& s.gpr .eax ∧
      (∀ i < k, coeffAt u.mem (P.addr s₀) i = coeffAt s.mem (P.addr s₀) i &&& (0 - s.gpr .eax)) ∧
      (∀ i, k ≤ i → i < 256 → coeffAt u.mem (P.addr s₀) i = coeffAt s.mem (P.addr s₀) i)
    obtain i0 : I 0 s₈ := ⟨c₈, by rw [o₈.gpr _ (by decide), v₇, v₆, g₅, c₄.esi]; simp; rfl,
      v₈, rE, fC.mono (by simp), aC, fun i hi => absurd hi (by omega_using []), fun i _ hi => cP i hi⟩
    refine (wp_count (N := 256) (by decide) I i0 fun k hk u ⟨cu, du, xu, eu, fu, au, lo, hi⟩ => ?_).mono
      fun u ⟨cu, _, _, _, fu, au, lo, _⟩ => hQ s₀ s u hp ha cu fu au lo
    obtain eP : u.ea (at_ .edi 0) = coeffAddr (P.addr s₀) k := by
      simp only [State.ea, at_, du]; rw [ea_add (by omega_using [fP, hk])]; rfl
    obtain hk' : k < n := by rw [n_eq]; exact hk
    obtain inP : InRegions u.wr (coeffAddr (P.addr s₀) k) 4 :=
      Buf.inRegW hp hP₁ (Lay.okW_iff.mp hP).2 cu.wr (show 4 * k + 4 ≤ 1024 by omega_using [hk])
    obtain ⟨rP, hrP, hcP⟩ := Buf.contains hp hP₁ (Lay.okW_iff.mp hP).2 (o := 4 * k) (n := 4)
      (show 4 * k + 4 ≤ 1024 by omega_using [hk])
    obtain inP' : InRegions (u.rd ++ u.wr) (coeffAddr (P.addr s₀) k) 4 :=
      Buf.inRegR hp hP₁ cu.rd cu.wr (show 4 * k + 4 ≤ 1024 by omega_using [hk])
    refine wp_movm' (by rw [eP]; exact inP') fun u₁ o₁ v₁ => ?_
    obtain c₁ := cu.only o₁ (by decide) (by decide)
    refine wp_andr fun u₂ o₂ v₂ => ?_
    obtain c₂ := c₁.only o₂ (by decide) (by decide)
    obtain eP₂ : u₂.ea (at_ .edi 0) = coeffAddr (P.addr s₀) k := by
      rw [← eP]; simp only [State.ea, at_]; rw [o₂.gpr _ (by decide), o₁.gpr _ (by decide)]
    refine wp_store' (by rw [eP₂, c₂.wr, ← cu.wr]; exact inP) fun u₃ g₃ r₃ w₃ m₃ => ?_
    obtain c₃ : Ctx Y s₀ u₃ := ⟨by rw [g₃]; exact c₂.esp, by rw [r₃]; exact c₂.rd, by rw [w₃]; exact c₂.wr,
      by rw [g₃]; exact c₂.esi, by rw [m₃, eP₂]; exact c₂.frame.writeW hrP _ hcP⟩
    refine wp_addi fun u₄ o₄ v₄ => wp_subi_last fun u₅ o₅ v₅ z₅ => ?_
    obtain c₅ := (c₃.only o₄ (by decide) (by decide)).only o₅ (by decide) (by decide)
    obtain val : u₂.gpr .eax = coeffAt s.mem (P.addr s₀) k &&& (0 - s.gpr .eax) := by
      rw [v₂, v₁, o₁.gpr _ (by decide), eu, eP, ← coeffAt_eq, hi k (Nat.le_refl _) hk]
    obtain m₅ : u₅.mem = u.mem.writeW (coeffAddr (P.addr s₀) k) (coeffAt s.mem (P.addr s₀) k &&& (0 - s.gpr .eax)) := by
      rw [o₅.mem, o₄.mem, m₃, eP₂, val, o₂.mem, o₁.mem]
    obtain ex : u₄.gpr .ecx = BitVec.ofNat 32 (256 - k) := by
      rw [o₄.gpr _ (by decide), g₃, o₂.gpr _ (by decide), o₁.gpr _ (by decide), xu]
    refine ⟨⟨c₅, ?_, by rw [v₅, ex]; exact cnt_next hk, ?_, ?_, ?_, fun i hi' => ?_, fun i hi₁ hi₂ => ?_⟩, ?_⟩
    · rw [o₅.gpr _ (by decide), v₄, g₃, o₂.gpr _ (by decide), o₁.gpr _ (by decide), du]
      show _ + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 4 = _
      rw [add_ofNat_add, show 4 * (k + 1) = 4 * k + 4 by omega_using []]
    · rw [o₅.gpr _ (by decide), o₄.gpr _ (by decide), g₃, o₂.gpr _ (by decide), o₁.gpr _ (by decide), eu]
    · rw [m₅]; exact fu.writeW (r := P.rgn s₀) (by simp) _ (coeff_contains _ hk')
    · rw [m₅, Mem.readW_writeW_sep (dd.sep (Region.contains_self _ _) (coeff_contains _ hk')) (by decide)]
      exact au
    · rw [m₅, coeffAt_writeW _ _ (by rw [n_eq]; omega_using [hk, hi']) hk']
      split
      · rename_i e; subst e; rfl
      · exact lo i (by omega_arith)
    · rw [m₅, coeffAt_writeW_ne _ _ (by rw [n_eq]; omega_using [hi₂]) hk' (by omega_using [hi₁])]
      exact hi i (by omega_using [hi₁]) hi₂
    · show u₅.zf.map (!·) = _
      rw [z₅, ex]; exact cnt_ne hk (by decide)
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [(hA _ _ hp ha).esi, (hA _ _ ‹_› ha').esi, hq.sc hp]

/-! ## `esi`, a word, and the value returned -/

/-- `esi ← scratch`, at the start of the body. -/
theorem ldsc_piece {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp]) (.block [.mov .esi (.mem (at_ .esp (20 + 4 * Y.sc)))]) ht).isSome = true) :
    Piece (TPre Y) (TPub Y lk) (fun s₀ s => s = P0 s₀) (Ctx Y) (.block [.mov .esi (.mem (at_ .esp (20 + 4 * Y.sc)))]) := by
  refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_) tt
  · subst e
    obtain ea : (P0 s₀).ea (at_ .esp (20 + 4 * Y.sc)) = argAddr s₀ Y.sc := P0_argAddr s₀ Y.sc
    refine wp_movm' (by rw [ea]; exact P0_argIn hp.sc_lt hp.sp' hp.gwr) fun s₁ o₁ v₁ => WP.block_nil_iff.mpr ?_
    refine ⟨by rw [o₁.gpr _ (by decide)], o₁.rd, o₁.wr, ?_, by rw [o₁.mem]; exact Frame.refl _ _⟩
    rw [v₁, ea]
    exact P0_arg hp.E0_big hp.sc_lt hp.sp' (by rw [hp.fr16]; exact hp.stk_g.sub_left hp.frame_sub)
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', P0_esp, P0_esp, hq.1]

/-- A word of `scratch` set to `v`. -/
theorem st32_piece (o v : Nat) (hc : Y.okW ⟨Y.sc, o, 4⟩ = true) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esi]) (.block [.mov .eax (.imm (BitVec.ofNat 32 v)), .store (at_ .esi o) .eax])
      ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      s'.mem = s.mem.writeW (Buf.addr s₀ ⟨Y.sc, o, 4⟩) (BitVec.ofNat 32 v) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (.block [.mov .eax (.imm (BitVec.ofNat 32 v)), .store (at_ .esi o) .eax]) := by
  obtain ⟨hc₁, hc₂⟩ := Lay.okW_iff.mp hc
  refine Piece.taint [.esi] (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp _ hq ha ha' r hr => ?_) tt
  · have h := hA s₀ s hp ha
    obtain ⟨r, hr, hcr⟩ := Buf.contains hp hc₁ hc₂ (o := 0) (n := 4) (Nat.le_refl _)
    simp only [BitVec.add_zero] at hcr
    obtain hin : InRegions s.wr (Buf.addr s₀ ⟨Y.sc, o, 4⟩) 4 := by
      have := Buf.inRegW hp hc₁ hc₂ h.wr (o := 0) (n := 4) (Nat.le_refl _)
      simpa using this
    refine wp_movi fun s₁ o₁ v₁ => ?_
    obtain h₁ := h.only o₁ (by decide) (by decide)
    obtain ea₁ : s₁.ea (at_ .esi o) = Buf.addr s₀ ⟨Y.sc, o, 4⟩ := by
      simp only [State.ea, at_]; rw [h₁.esi]
    refine wp_store' (by rw [ea₁, h₁.wr, ← h.wr]; exact hin) fun s₂ g₂ r₂ w₂ m₂ => WP.block_nil_iff.mpr ?_
    refine hQ s₀ s _ hp ha ⟨by rw [g₂]; exact h₁.esp, by rw [r₂]; exact h₁.rd, by rw [w₂]; exact h₁.wr,
      by rw [g₂]; exact h₁.esi, ?_⟩ ?_
    · rw [m₂, ea₁]; exact h₁.frame.writeW hr _ hcr
    · rw [m₂, ea₁, o₁.mem, v₁]
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [(hA _ _ hp ha).esi, (hA _ _ ‹_› ha').esi, hq.sc hp]

/-- `eax ←` a word of `scratch`. -/
theorem ld32_piece (o : Nat) (hc : Y.ok ⟨Y.sc, o, 4⟩ = true) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esi]) (.block [.mov .eax (.mem (at_ .esi o))]) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → s'.mem = s.mem →
      s'.gpr .eax = s.mem.readW (Buf.addr s₀ ⟨Y.sc, o, 4⟩) 32 → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (.block [.mov .eax (.mem (at_ .esi o))]) := by
  refine Piece.taint [.esi] (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp _ hq ha ha' r hr => ?_) tt
  · have h := hA s₀ s hp ha
    obtain hin : InRegions (s.rd ++ s.wr) (Buf.addr s₀ ⟨Y.sc, o, 4⟩) 4 := by
      have := Buf.inRegR hp hc h.rd h.wr (o := 0) (n := 4) (Nat.le_refl _)
      simpa using this
    obtain ea : s.ea (at_ .esi o) = Buf.addr s₀ ⟨Y.sc, o, 4⟩ := by simp only [State.ea, at_]; rw [h.esi]
    refine wp_movm' (by rw [ea]; exact hin) fun s₁ o₁ v₁ => WP.block_nil_iff.mpr ?_
    exact hQ s₀ s s₁ hp ha (h.only o₁ (by decide) (by decide)) o₁.mem (by rw [v₁, ea])
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [(hA _ _ hp ha).esi, (hA _ _ ‹_› ha').esi, hq.sc hp]

end VG.Proof.MlKem.X86.Top
