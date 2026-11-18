module

public import VerifiedGarbage.Proof.MlDsa.X86.Sign.Pre
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values
import VerifiedGarbage.Proof.MlDsa.X86.Sign.Words
public import VerifiedGarbage.Proof.MlDsa.X86.Sign.Inst
import VerifiedGarbage.Proof.MlKem.X86.TopLocal
import VerifiedGarbage.Proof.MlKem.X86.TopSeq
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.Proof.MlDsa.Sign.Mem
import VerifiedGarbage.Proof.MlKem.X86.AddSub
import VerifiedGarbage.Proof.MlKem.X86.Leaf
meta import VerifiedGarbage.Proof.MlDsa.X86.Sign.Words
meta import VerifiedGarbage.Proof.MlKem.X86.TopLocal
meta import VerifiedGarbage.Proof.MlKem.X86.TopSeq
meta import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlDsa.DecideAt
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
public import VerifiedGarbage.Proof.MlDsa.X86.Sign.PhaseK
import VerifiedGarbage.Proof.MlDsa.Round.Decompose
import VerifiedGarbage.Proof.MlDsa.X86.Sign.PrimD
import VerifiedGarbage.Proof.MlDsa.X86.Sign.Local
meta import VerifiedGarbage.Proof.MlDsa.X86.Sign.PhaseK
meta import VerifiedGarbage.Proof.MlDsa.Round.Decompose
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.MlDsa.X86.Sign.PrimD
meta import VerifiedGarbage.Proof.MlDsa.X86.Sign.Local
meta import VerifiedGarbage.Proof.MlKem.X86.AddSub

/-! ### `MlDsa.X86.Sign.Final`, which only this module used -/

section

/-! ### `MlDsa.X86.Sign.PhaseL`, which only this module used -/

section

/-!
# ML-DSA signing on x86 (32-bit): the rejection sampling loop

Iteration `t` runs the commitment, `SampleInBall`, and the checks if it
succeeded, and ends with `CNT ← CNT - 1` (`iter_piece`). The loop runs `NI`
iterations (`loop_piece`): after `t < NI` of them, iteration `t` is next
(`IT`); after all of them, the last one's outcome is in `OK`, with `c̃`, `z`
and the hint if it succeeded (`Fin`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf at_)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece Only)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params} {P : Prims}

/-- The outcome of the last iteration, `u`. -/
structure Fin' (p : Params) (F : PrimsOk P) (u : Nat) (s₀ s : State) : Prop where
  ctx : Ctx (Y p) s₀ s
  run : Run p F u s₀
  ok : scw s₀ s oOK = if (F.ballF p.τ (CTv p s₀ (p.ℓ * u)) && decide (passS p u s₀)) then 1 else 0
  out : F.ballF p.τ (CTv p s₀ (p.ℓ * u)) = true → passS p u s₀ →
    Fam s₀ s.mem (yB p) p.ℓ (Zv p s₀ (p.ℓ * u)) ∧ HF s₀ s.mem p.k (Hv p s₀ (p.ℓ * u)) ∧
      bytesAt s.mem (Buf.addr s₀ (sc oCT (cLen p))) (cLen p) = CTv p s₀ (p.ℓ * u)
  none : F.ballF p.τ (CTv p s₀ (p.ℓ * u)) = false → sampleInBall p.τ minBounds.ball (CTv p s₀ (p.ℓ * u)) = none

/-- After `t` iterations. -/
structure LI (p : Params) (F : PrimsOk P) (t : Nat) (s₀ s : State) : Prop where
  good : Good p F s₀
  le : t ≤ NI p F s₀
  it : t < NI p F s₀ → IT p t s₀ s
  fin : t = NI p F s₀ → Fin' p F (NI p F s₀ - 1) s₀ s

/-- A store to the word at `o`, which keeps the flags. -/
theorem wp_stscZ {s₀ s : State} (hp : TPre (Y p) s₀) (h : Ctx (Y p) s₀ s) {o : Nat} (hc : (Y p).okW (sc o 4) = true)
    {r : Reg} {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Ctx (Y p) s₀ s' → (∀ x, s'.gpr x = s.gpr x) → s'.zf = s.zf →
      s'.mem = s.mem.writeW (Buf.addr s₀ (sc o 4)) (s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.store (at_ .esi o) r :: is)) s Q := by
  obtain ⟨hc₁, hc₂⟩ := Lay.okW_iff.mp hc
  have hin : InRegions s.wr (Buf.addr s₀ (sc o 4)) 4 := by
    have := Buf.inRegW hp hc₁ hc₂ h.wr (o := 0) (n := 4) (Nat.le_refl _)
    simpa using this
  refine VG.Proof.MlKem.X86.wp_store (by rw [ea_sc h o 4]; exact hin) ?_
  have c := ctx_write hp h hc (w := 32) (by decide) (s.gpr r)
  refine k _ ?_ (fun _ => rfl) rfl (by rw [ea_sc h o 4])
  rw [ea_sc h o 4]; exact c

theorem ofNat_sub_one {x : Nat} (h1 : 1 ≤ x) (h2 : x < 2 ^ 32) : BitVec.ofNat 32 x - 1 = BitVec.ofNat 32 (x - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have : (1 : BitVec 32).toNat = 1 := rfl
  rw [this]
  omega_arith

/-- `CNT ← CNT - 1`, which sets `ZF` when the loop ends. -/
theorem tail_piece (F : PrimsOk P) (ps : PS p) (t : Nat) :
    SP p (ED p F t) (fun s₀ s => LI p F (t + 1) s₀ s ∧ isa.eval .ne s = some (decide (t + 1 < NI p F s₀)))
      (.block [.mov .eax (.mem (at_ .esi oCNT)), .alu .sub .eax (.imm 1), .store (at_ .esi oCNT) .eax]) := by
  refine blk_piece (fun _ _ _ h => h.kd.ctx) (fun s₀ s hp h => ?_) rfl
  refine wp_ldsc hp h.kd.ctx (sc_ok' ps (by decide) (by decide)) fun s₁ o₁ v₁ => wp_subi fun s₂ o₂ v₂ z₂ => ?_
  have o := o₁.trans o₂
  have c₂ := h.kd.ctx.only o (by simp) (by simp)
  refine wp_stscZ hp c₂ (sc_ok ps (by decide) (by decide)) fun s' c' g' z' m' => WP.block_nil_iff.mpr ?_
  have fr : Frame (FR s₀ [sc oCNT 4] 80) s.mem s'.mem := fr0 hp (by decide) (by
    rw [m', o.mem]; exact frW32 (Y := Y p))
  have hrun := h.run
  have hNI := NI_good hrun.1
  have ht := hrun.2
  have hlt := hrun.lt
  have hnext : t + 1 < NI p F s₀ ↔ contS p F t s₀ = true ∧ t + 1 < 814 := by
    rw [hNI]; exact nIt_next _ (by have := ht; rw [hNI] at this; exact this)
  have hcnt : scw s₀ s' oCNT = scw s₀ s oCNT - 1 := by
    rw [scw, m', Mem.readW_writeW_self32, v₂, v₁]
  have hz : isa.eval .ne s' = some (decide (t + 1 < NI p F s₀)) := by
    show s'.zf.map (!·) = _
    rw [z', z₂, v₁, h.cnt]
    cases e : contS p F t s₀
    · simp only [e, Bool.false_eq_true, false_and, iff_false] at hnext
      rw [decide_eq_false hnext]; simp
    · simp only [e, true_and] at hnext
      simp only [↓reduceIte]
      rw [show decide (t + 1 < NI p F s₀) = decide (t + 1 < 814) from decide_eq_decide.mpr hnext]
      by_cases e' : t + 1 < 814
      · rw [decide_eq_true e']
        rw [ofNat_sub_one (by omega_arith) (by omega_arith)]
        have : (BitVec.ofNat 32 (814 - t - 1) == 0) = false := by
          apply beq_eq_false_iff_ne.mpr
          intro h0
          have := congrArg BitVec.toNat h0
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this
          exact absurd this (by show ¬ (814 - t - 1 = 0); omega_arith)
        rw [this]; rfl
      · rw [decide_eq_false e', show 814 - t = 1 by omega_arith]; rfl
  refine ⟨⟨hrun.1, ht, fun ht' => ?_, fun ht' => ?_⟩, hz⟩
  · have hc : contS p F t s₀ = true := (hnext.mp ht').1
    refine ⟨h.kd.keep hp ps c' (by decide) fr (by ofsd), ?_, ?_, (hnext.mp ht').2⟩
    · rw [scw, keepW' hp (by decide) fr (sc_ok' ps (by decide) (by decide)) (by ofsd)]; exact h.kap hc
    · rw [hcnt, h.cnt, hc]
      simp only [↓reduceIte]
      rw [ofNat_sub_one (by omega_arith) (by omega_arith), Nat.sub_sub]
  · rw [← ht', Nat.add_sub_cancel]
    refine ⟨c', hrun, ?_, fun hb hq => ?_, h.none⟩
    · rw [scw, keepW' hp (by decide) fr (sc_ok' ps (by decide) (by decide)) (by ofsd)]; exact h.ok
    · obtain ⟨f1, f2, f3⟩ := h.out hb hq
      have := ps.hcLen
      exact ⟨f1.keep hp ps (by decide) fr (by simp only [nS, yB]; omega_arith) (by ofsd),
        f2.keep hp ps (by decide) fr (by simp only [nS]; omega_arith) (by ofsd),
        by rw [keepB hp (by decide) fr (by ofsd) (by ofsd), f3]⟩

/-- `OK ← 0` and `CNT ← 1`, when `SampleInBall` failed. -/
theorem ballFail_piece (F : PrimsOk P) (ps : PS p) (t : Nat) :
    SP p (fun s₀ s => (∃ s', IB p F t s₀ s' ∧ Ctx (Y p) s₀ s ∧ s.mem = s'.mem ∧ s.zf = some (!ballB p F t s₀)) ∧
      ballB p F t s₀ = false) (ED p F t) (.block (st32 oOK 0 ++ st32 oCNT 1)) := by
  refine blk_piece (fun _ _ _ h => h.1.choose_spec.2.1) (fun s₀ s hp h => ?_) rfl
  obtain ⟨⟨s', ib, c, m, _⟩, hb⟩ := h
  have hf : F.ballF p.τ (CTv p s₀ (p.ℓ * t)) = false := by rw [← ballB_of ib.run]; exact hb
  have kd := ib.cc.cw.cm.it.kd.keep hp ps c (N := 0) (bs := []) (by decide) (by rw [m]; exact Frame.refl _ _)
    (by simp)
  refine wp_st32 hp c (sc_ok ps (by decide) (by decide)) 0 fun s₁ c₁ f₁ v₁ => ?_
  rw [← List.append_nil (st32 oCNT 1)]
  refine wp_st32 hp c₁ (sc_ok ps (by decide) (by decide)) 1 fun s₂ c₂ f₂ v₂ => WP.block_nil_iff.mpr ?_
  have kd₁ := kd.keep hp ps c₁ (N := 80) (by decide) (fr0 hp (by decide) f₁) (by ofsd)
  have hc : contS p F t s₀ = false := by simp only [contS, contV, hf, Bool.false_and]
  refine ⟨kd₁.keep hp ps c₂ (N := 80) (by decide) (fr0 hp (by decide) f₂) (by ofsd), ib.run, by rw [hc, v₂]; rfl,
    (fun e => by rw [hc] at e; cases e), ?_, (fun e => by rw [hf] at e; cases e), fun _ => ib.no hf⟩
  rw [scw, keepW' hp (N := 80) (by decide) (fr0 hp (by decide) f₂) (sc_ok' ps (by decide) (by decide)) (by ofsd), ← scw,
    v₁, hf, Bool.false_and]; rfl

/-- Iteration `t`. -/
theorem iter_piece (F : PrimsOk P) (ps : PS p) (t : Nat) :
    SP p (fun s₀ s => LI p F t s₀ s ∧ t < NI p F s₀)
      (fun s₀ s => LI p F (t + 1) s₀ s ∧ isa.eval .ne s = some (decide (t + 1 < NI p F s₀))) (iter P p) := by
  unfold iter
  refine Piece.seq (B := fun s₀ s => CC p t s₀ s ∧ Run p F t s₀)
    ((sp_pure (Run p F t) (commit_piece F ps t)).mono (fun s₀ s _ h =>
      ⟨⟨h.1.it h.2, fun j hj => absurd hj (Nat.not_lt_zero _), fun j hj => absurd hj (Nat.not_lt_zero _)⟩,
        h.1.good, h.2⟩) fun _ _ _ h => h) ?_
  refine Piece.seq (ballCall_piece F ps t) ?_
  refine Piece.seq (ballTest_piece F t) ?_
  refine Piece.seq (Piece.ite (ballB p F t) (fun s₀ s _ h => ?_) (fun s₀ s₀' _ _ hq => ballB_eq ps hq)
    ((checks_piece F ps t).mono (fun s₀ s hp h => ?_) fun _ _ _ h => h) (ballFail_piece F ps t)) (tail_piece F ps t)
  · show s.zf.map (!·) = _
    rw [h.choose_spec.2.2.2]; cases ballB p F t s₀ <;> rfl
  · obtain ⟨⟨s', ib, c, m, _⟩, hb⟩ := h
    have hs : F.ballF p.τ (CTv p s₀ (p.ℓ * t)) = true := by rw [← ballB_of ib.run]; exact hb
    exact ⟨⟨ib.cc.ofMem hp ps c m, ib.run, hs⟩, by rw [m]; exact ib.yes hs⟩

/-- `κ ← 0`, `CNT ← 814`, and the loop. -/
theorem signLoop_piece (F : PrimsOk P) (ps : PS p) :
    SP p (fun s₀ s => KD p s₀ s ∧ Good p F s₀) (fun s₀ s => Fin' p F (NI p F s₀ - 1) s₀ s) (Impl.MlDsa.X86.Sign.signLoop P p) := by
  unfold Impl.MlDsa.X86.Sign.signLoop
  refine Piece.seq (B := LI p F 0) ?_ ((loopN (NI p F) (LI p F) (fun s₀ _ => NI_pos (p := p) F s₀)
    (fun s₀ s₀' _ _ hq => NI_eq ps hq) fun t => iter_piece F ps t).mono (fun _ _ _ h => h)
      fun s₀ s _ h => h.fin rfl)
  refine blk_piece (fun _ _ _ h => h.1.ctx) (fun s₀ s hp h => ?_) rfl
  refine wp_st32 hp h.1.ctx (sc_ok ps (by decide) (by decide)) 0 fun s₁ c₁ f₁ v₁ => ?_
  rw [← List.append_nil (st32 oCNT 814)]
  refine wp_st32 hp c₁ (sc_ok ps (by decide) (by decide)) 814 fun s₂ c₂ f₂ v₂ => WP.block_nil_iff.mpr ?_
  have kd₁ := h.1.keep hp ps c₁ (N := 80) (by decide) (fr0 hp (by decide) f₁) (by ofsd)
  have hpos := NI_pos (p := p) F s₀
  refine ⟨h.2, Nat.zero_le _, fun _ => ⟨kd₁.keep hp ps c₂ (N := 80) (by decide) (fr0 hp (by decide) f₂) (by ofsd),
    ?_, v₂, by decide⟩, fun e => absurd e (by omega_arith)⟩
  rw [scw, keepW' hp (N := 80) (by decide) (fr0 hp (by decide) f₂) (sc_ok' ps (by decide) (by decide)) (by ofsd), ← scw,
    v₁]; rfl

end VG.Proof.MlDsa.X86.Sign

end

end

/-! ### `MlDsa.X86.Sign.PhaseO`, which only this module used -/

section

/-!
# ML-DSA signing on x86 (32-bit): the signature

Once an iteration passed, `sig` is `c̃` (`outCopy_piece`), the `BitPack` of
`z` (`packZ_piece`), in range by the check of its norm (`inRange_of_norm`),
and `HintBitPack(h)` (`hpack_piece`), whose 1s are at most `ω` by the check of
their number, and whose leakage, the hint, two runs whose checks pass agree on
(`hint_list`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf at_ copyW)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece Only)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params} {P : Prims}

/-! ## `z` in range -/

theorem coeff_val {m : Mem} {a : Addr} {f : Poly} (h : PolyIs m a f) {i : Nat} (hi : i < 256) :
    (coeffAt m a i).toNat = f[i].val := by
  have e := congrArg (·[i]) h.2
  simp only [polyAt, Vector.getElem_ofFn] at e
  rw [← e, Fin.val_ofNat, Nat.mod_eq_of_lt (h.1 i hi)]

theorem inRange_of_norm {m : Mem} {a : Addr} {f : Poly} (h : PolyIs m a f) {B γ : Nat}
    (hn : normRq [f] < B) (hB : B ≤ γ) :
    ∀ i < n, -((γ - 1 : Nat) : Int) ≤ modPm (coeffAt m a i).toNat q ∧ modPm (coeffAt m a i).toNat q ≤ γ := by
  intro i hi
  have := (VG.Proof.MlDsa.Round.normRq_lt f B).mp hn i hi
  rw [getElem!_pos f i hi] at this
  rw [coeff_val h hi]
  simp only [normZq] at this
  omega_using [hB, this]

/-! ## The hint -/

theorem coeff_slot {m : Mem} {s₀ : State} (hp : TPre (Y p) s₀) (ps : PS p) {i j : Nat} (hi : i < p.k) :
    coeffAt m (Buf.addr s₀ (sc (oP 5) (1024 * p.k))) (256 * i + j) = coeffAt m (Buf.addr s₀ (pS (5 + i))) j := by
  have e : Buf.addr s₀ (pS (5 + i)) = Buf.addr s₀ (sc (oP 5) (1024 * p.k)) + BitVec.ofNat 64 (1024 * i) := by
    show Buf.addr s₀ (sc (oP (5 + i)) 1024) = _
    rw [show oP (5 + i) = oP 5 + 1024 * i by simp only [oP]; omega_using []]
    exact addr_off hp (by ofsd) (by ofsd)
  simp only [coeffAt]
  rw [e, BitVec.add_assoc, ← BitVec.ofNat_add, show 1024 * i + 4 * j = 4 * (256 * i + j) by omega_using []]

theorem hintAt_of {m : Mem} {s₀ : State} (hp : TPre (Y p) s₀) (ps : PS p) {f : Nat → Vector Bool n}
    (h : HF s₀ m p.k f) : hintAt m (Buf.addr s₀ (sc (oP 5) (1024 * p.k))) p.k = (List.range p.k).map f := by
  unfold hintAt
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  apply Vector.ext
  intro j hj
  have e := (h i hi).2 0 (by decide) j hj
  simp only [Nat.mul_zero, Nat.zero_add, List.getD_cons_zero] at e
  rw [Vector.getElem_ofFn, coeff_slot hp ps hi, e, getElem!_pos (f i) j hj]
  cases (f i)[j] <;> decide

theorem hintOnes_map (k : Nat) (f : Nat → Vector Bool n) :
    hintOnes ((List.range k).map f) = ((List.range k).map fun j => hintOnes [f j]).sum := by
  simp only [hintOnes, List.map_map, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  rfl

/-- The coefficients of the hint, as the list `hbitsV` of its bits. -/
theorem hint_list {m : Mem} {s₀ : State} (hp : TPre (Y p) s₀) (ps : PS p) {f : Nat → Vector Bool n}
    (h : HF s₀ m p.k f) :
    (List.range (256 * p.k)).map (fun i => (coeffAt m (Buf.addr s₀ (sc (oP 5) (1024 * p.k))) i).toNat) =
      ((List.range p.k).map f).flatMap fun hi => hi.toList.map Bool.toNat := by
  suffices ∀ k ≤ p.k, (List.range (256 * k)).map (fun i => (coeffAt m (Buf.addr s₀ (sc (oP 5) (1024 * p.k))) i).toNat) =
      ((List.range k).map f).flatMap fun hi => hi.toList.map Bool.toNat from this p.k (Nat.le_refl _)
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 256 * (k + 1) = 256 * k + 256 by omega_using [], List.range_add, List.map_append, ih (by omega_using [hk]),
      List.range_succ (n := k), List.map_append, List.flatMap_append]
    congr 1
    simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map]
    refine List.ext_getElem (by simp) fun j h₁ h₂ => ?_
    simp only [List.length_map, List.length_range] at h₁
    have e := (h k (by omega_using [hk])).2 0 (by decide) j h₁
    simp only [Nat.mul_zero, Nat.zero_add, List.getD_cons_zero] at e
    simp only [List.getElem_map, List.getElem_range, Function.comp, Vector.getElem_toList, coeff_slot hp ps (by omega_using [hk] : k < p.k),
      e, getElem!_pos (f k) j h₁]
    cases (f k)[j] <;> rfl

/-! ## The signature -/

/-- The `BitPack` of the first `r` polynomials of `z`. -/
abbrev zEnc (p : Params) (s₀ : State) (κ r : Nat) : List Byte :=
  (List.range r).flatMap fun j => bitPack ((Zv p s₀ κ j).map fun c => modPm c.val q) (p.γ₁ - 1) p.γ₁

/-- Before the signature, the last iteration `U s₀` having passed; with the
first `r` polynomials of `z` packed after `c̃` in `sig`. -/
structure OS (p : Params) (F : PrimsOk P) (U : State → Nat) (r : Nat) (s₀ s : State) : Prop where
  ctx : Ctx (Y p) s₀ s
  fy : Fam s₀ s.mem (yB p) p.ℓ (Zv p s₀ (p.ℓ * U s₀))
  fh : HF s₀ s.mem p.k (Hv p s₀ (p.ℓ * U s₀))
  run : Run p F (U s₀) s₀
  ball : F.ballF p.τ (CTv p s₀ (p.ℓ * U s₀)) = true
  pass : passS p (U s₀) s₀
  ok1 : scw s₀ s oOK = 1
  sig : bytesAt s.mem (Buf.addr s₀ (bSig 0 (cLen p + zLen p * r))) (cLen p + zLen p * r) =
    CTv p s₀ (p.ℓ * U s₀) ++ zEnc p s₀ (p.ℓ * U s₀) r

/-- A write of `sig` keeps `z` and the hint. -/
theorem sigKeep {s₀ : State} (hp : TPre (Y p) s₀) (ps : PS p) {m m' : Mem} {fz : Nat → Poly} {fh : Nat → Vector Bool n}
    (hz : Fam s₀ m (yB p) p.ℓ fz) (hh : HF s₀ m p.k fh) {bs : List Buf} {N : Nat} (hN : N ≤ 80)
    (fr : Frame (FR s₀ bs N) m m') (hb : ∀ c ∈ bs, (Y p).ok c = true ∧ c.arg = 3) :
    Fam s₀ m' (yB p) p.ℓ fz ∧ HF s₀ m' p.k fh ∧
      m'.readW (Buf.addr s₀ (sc oOK 4)) 32 = m.readW (Buf.addr s₀ (sc oOK 4)) 32 :=
  ⟨hz.keep hp ps hN fr (by simp only [nS, yB]; omega_using []) fun c hc => ⟨(hb c hc).1, fun e => by
      rw [(hb c hc).2] at e; cases e⟩,
    hh.keep hp ps hN fr (by simp only [nS]; omega_using []) fun c hc => ⟨(hb c hc).1, fun e => by
      rw [(hb c hc).2] at e; cases e⟩,
    keepW' hp hN fr (sc_ok' ps (by decide) (by decide)) fun c hc => ⟨(hb c hc).1, fun e => by
      rw [(hb c hc).2] at e; cases e⟩⟩

/-- Before the signature, the last iteration `U s₀` having passed. -/
structure OI (p : Params) (F : PrimsOk P) (U : State → Nat) (s₀ s : State) : Prop where
  ctx : Ctx (Y p) s₀ s
  fy : Fam s₀ s.mem (yB p) p.ℓ (Zv p s₀ (p.ℓ * U s₀))
  fh : HF s₀ s.mem p.k (Hv p s₀ (p.ℓ * U s₀))
  run : Run p F (U s₀) s₀
  ball : F.ballF p.τ (CTv p s₀ (p.ℓ * U s₀)) = true
  pass : passS p (U s₀) s₀
  ok1 : scw s₀ s oOK = 1
  ct : bytesAt s.mem (Buf.addr s₀ (sc oCT (cLen p))) (cLen p) = CTv p s₀ (p.ℓ * U s₀)

/-- `c̃` to `sig`. -/
theorem outCopy_piece (F : PrimsOk P) (ps : PS p) (U : State → Nat) :
    SP p (OI p F U) (OS p F U 0) (copyW SC (sc oCT (cLen p)) (bSig 0 (cLen p)) (cLen p / 4)) := by
  have hc := ps.hcLen
  have e4 : 4 * (cLen p / 4) = cLen p := by omega_using [hc]
  have e : copyW SC (sc oCT (cLen p)) (bSig 0 (cLen p)) (cLen p / 4) =
      copyW SC ⟨SC, oCT, 4 * (cLen p / 4)⟩ ⟨3, 0, 4 * (cLen p / 4)⟩ (cLen p / 4) := rfl
  rw [e]
  refine copy_piece SC oCT 3 0 (cLen p / 4) (by omega_using [hc]) (by omega_using [hc]) (by ofsd) (fun _ _ _ h => h.ctx)
    fun s₀ s s' hp h c' fr hb => ?_
  have fr' : Frame (FR s₀ [⟨3, 0, 4 * (cLen p / 4)⟩] 80) s.mem s'.mem := fr.mono (by simp)
  have hk := sigKeep hp ps h.fy h.fh (by decide) fr' fun c hc => by
    rw [List.mem_singleton] at hc; subst hc; exact ⟨by ofsd, rfl⟩
  refine ⟨c', hk.1, hk.2.1, h.run, h.ball, h.pass, by rw [scw, hk.2.2]; exact h.ok1, ?_⟩
  rw [e4] at hb
  simp only [Nat.mul_zero, Nat.add_zero]
  rw [show zEnc p s₀ (p.ℓ * U s₀) 0 = [] from rfl, List.append_nil]
  exact hb.trans h.ct

/-- `BitPack(z[r], γ₁ - 1, γ₁)` to `sig`. -/
theorem packZ_piece (F : PrimsOk P) (ps : PS p) (U : State → Nat) (r : Nat) (hr : r < p.ℓ) :
    SP p (OS p F U r) (OS p F U (r + 1)) (packZ P p r) := by
  have hz := ps.hzLen
  have hβ := ps.hβ
  have hm : zLen p * r + zLen p ≤ zLen p * p.ℓ := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hr
  have hc := ps.hcLen
  refine bp_piece F.bitPack (F.ok _ (by simp)) (p.γ₁ - 1) p.γ₁ (zLen p) ps.hz.1 ps.hz.2 ⟨by omega_arith, by omega_arith, by omega_using [hz]⟩
    SC (oP (yB p + r)) 3 (sigZ p r) (by ofsd) (fun s₀ s _ h => ⟨h.ctx, (fam_at h.fy hr).1,
      inRange_of_norm (fam_at h.fy hr) (h.pass.1 r hr) (by omega_using [])⟩) fun s₀ s s' hp h c' fr hb => ?_
  have hk := sigKeep hp ps h.fy h.fh (by decide) fr fun c hc => by
    rw [List.mem_singleton] at hc; subst hc; exact ⟨by ofsd, rfl⟩
  refine ⟨c', hk.1, hk.2.1, h.run, h.ball, h.pass, by rw [scw, hk.2.2]; exact h.ok1, ?_⟩
  rw [bytes_split hp s'.mem (o' := sigZ p r) (l₁ := cLen p + zLen p * r) (l₂ := zLen p) (by simp only [sigZ]; omega_using []) (by rw [Nat.mul_succ]; omega_using [])
    (by ofsd) (by ofsd), keepBytes hp (N := 80) (by show 80 + 16 ≤ 96; decide) (b := ⟨3, 0, cLen p + zLen p * r⟩) (by ofsd) fr, h.sig, hb,
    (fam_at h.fy hr).2, List.append_assoc]
  simp only [zEnc, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The signature, of the last iteration `U s₀`. -/
abbrev sigV (p : Params) (s₀ : State) (κ : Nat) : List Byte :=
  CTv p s₀ κ ++ zEnc p s₀ κ p.ℓ ++ hintBitPack p.ω p.k ((List.range p.k).map (Hv p s₀ κ))

/-- `HintBitPack(h)` to `sig`. -/
theorem hpack_piece (F : PrimsOk P) (ps : PS p) (U : State → Nat)
    (hU : ∀ s₀ s₀', TPre (Y p) s₀ → TPre (Y p) s₀' → SPub p s₀ s₀' → U s₀ = U s₀') :
    SP p (OS p F U p.ℓ) (fun s₀ s => Ctx (Y p) s₀ s ∧ scw s₀ s oOK = 1 ∧
      bytesAt s.mem (Buf.addr s₀ (bSig 0 p.sigLen)) p.sigLen = sigV p s₀ (p.ℓ * U s₀))
      (hintBitPackAt P (sc (oP 5) (1024 * p.k)) p.ω (bSig (sigH p) (p.ω + p.k))) := by
  have hz := ps.hzLen
  have hc := ps.hcLen
  have hsl := ps.hsigLen
  unfold hintBitPackAt
  rw [show (sc (oP 5) (1024 * p.k)).len / 4 = 256 * p.k by show 1024 * p.k / 4 = _; omega_using []]
  refine hbp_piece F.hintBitPack (F.ok _ (by simp)) p.ω p.k ps.hhint SC (oP 5) 3 (sigH p) (by ofsd)
    (fun s₀ s hp h => ⟨h.ctx, ?_⟩) (fun s₀ s₀' s s' hp hp' hq h h' => ?_) fun s₀ s s' hp h c' fr hb =>
      ⟨c', by rw [scw, (sigKeep hp ps h.fy h.fh (by decide) fr fun c hc => by
        rw [List.mem_singleton] at hc; subst hc; exact ⟨by ofsd, rfl⟩).2.2]; exact h.ok1, ?_⟩
  · rw [hintAt_of hp ps h.fh, hintOnes_map]; exact h.pass.2.2.2
  · rw [hint_list hp ps h.fh, hint_list hp' ps h'.fh, ← hU s₀ s₀' hp hp' hq]
    exact (((run_at ps hq h.run).2 h.ball).2 h.pass)
  · rw [bytes_split hp s'.mem (o' := sigH p) (l₁ := cLen p + zLen p * p.ℓ) (l₂ := p.ω + p.k) (by simp only [sigH]; omega_using [])
      (by omega_using [hsl]) (by ofsd) (by ofsd), keepBytes hp (N := 80) (by show 80 + 16 ≤ 96; decide)
      (b := ⟨3, 0, cLen p + zLen p * p.ℓ⟩) (by ofsd) fr, h.sig, hb, hintAt_of hp ps h.fh]

/-- The signature. -/
theorem output_piece (F : PrimsOk P) (ps : PS p) (U : State → Nat)
    (hU : ∀ s₀ s₀', TPre (Y p) s₀ → TPre (Y p) s₀' → SPub p s₀ s₀' → U s₀ = U s₀') :
    SP p (OI p F U) (fun s₀ s => Ctx (Y p) s₀ s ∧ scw s₀ s oOK = 1 ∧
      bytesAt s.mem (Buf.addr s₀ (bSig 0 p.sigLen)) p.sigLen = sigV p s₀ (p.ℓ * U s₀)) (output P p) := by
  unfold output
  refine (outCopy_piece F ps U).seq (Piece.seq ?_ (hpack_piece F ps U hU))
  have := seqR_piece (p := p) (I := OS p F U) 0 p.ℓ fun r _ hr => packZ_piece F ps U r (by omega_using [hr])
  simpa using this

end VG.Proof.MlDsa.X86.Sign

end

end

/-!
# ML-DSA signing on x86 (32-bit): the body

After `ExpandA`, the rest (`rest_piece`: the private key, the loop, and the
signature if the last iteration passed) leaves `OK`, and `sig` if it is 1, as
`Sign_internal` says (`Outcome`, `rest_outcome`): 1 with the signature within
`maxBounds` if the last iteration passed, and 0 with `Sign_internal` failing
within `minBounds` if `SampleInBall` failed or the 814 iterations were
rejected; and 0 at once if an entry of `Â` failed (`body_piece`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf at_)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece Only P0)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params} {P : Prims}

/-! ## `Sign_internal` -/

section
variable {s₀ : State}

theorem signMu_min_A (h : ∃ e < p.k * p.ℓ, rejNTTPoly minBounds.rejNTT (seedE p s₀ e) = none) :
    signMu p minBounds (skOf p s₀) (muOf s₀) (rndOf s₀) = none := by
  obtain ⟨e, he, hn⟩ := h
  have hl : 0 < p.ℓ := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.mul_zero] at he; omega_using [he]
  exact signMu_none_A (expandA_none ⟨e / p.ℓ, (Nat.div_lt_iff_lt_mul hl).mpr he, e % p.ℓ, Nat.mod_lt _ hl, hn⟩)

theorem signMu_min_L (hA : expandA p maxBounds (rhoV (skOf p s₀)) = some (amat p (Av (skOf p s₀))))
    (hL : loopV p (skOf p s₀) (muOf s₀) (rndOf s₀) minBounds minBounds.sign 0 = none) :
    signMu p minBounds (skOf p s₀) (muOf s₀) (rndOf s₀) = none := by
  cases e : expandA p minBounds (rhoV (skOf p s₀)) with
  | none => exact signMu_none_A e
  | some A' =>
    have := expandA_mono (show minBounds.rejNTT ≤ maxBounds.rejNTT by decide) e
    rw [hA] at this
    obtain rfl := (Option.some.inj this).symm
    exact signMu_none_L e hL

theorem sigOf_eq (κ : Nat) :
    sigOf p (CTv p s₀ κ, (List.range p.ℓ).map (Zv p s₀ κ), (List.range p.k).map (Hv p s₀ κ)) = sigV p s₀ κ := by
  simp only [sigOf, sigEncode, sigV, zEnc, List.flatMap_map, List.map_map]
  rfl

end

/-! ## The rest -/

/-- After the rest, the last iteration being `NI - 1`. -/
structure RD (p : Params) (F : PrimsOk P) (s₀ s : State) : Prop where
  ctx : Ctx (Y p) s₀ s
  run : Run p F (NI p F s₀ - 1) s₀
  ok : scw s₀ s oOK = if (F.ballF p.τ (CTv p s₀ (p.ℓ * (NI p F s₀ - 1))) && decide (passS p (NI p F s₀ - 1) s₀))
    then 1 else 0
  sig : F.ballF p.τ (CTv p s₀ (p.ℓ * (NI p F s₀ - 1))) = true → passS p (NI p F s₀ - 1) s₀ →
    bytesAt s.mem (Buf.addr s₀ (bSig 0 p.sigLen)) p.sigLen = sigV p s₀ (p.ℓ * (NI p F s₀ - 1))
  none : F.ballF p.τ (CTv p s₀ (p.ℓ * (NI p F s₀ - 1))) = false →
    sampleInBall p.τ minBounds.ball (CTv p s₀ (p.ℓ * (NI p F s₀ - 1))) = none

/-- Whether the last iteration passed, in a run whose `Â` was sampled. -/
def lastB (p : Params) (F : PrimsOk P) (s₀ : State) : Bool :=
  decide (Good p F s₀) && F.ballF p.τ (CTv p s₀ (p.ℓ * (NI p F s₀ - 1))) &&
    decide (passS p (NI p F s₀ - 1) s₀)

theorem lastB_eq {F : PrimsOk P} {s₀ s₀' : State} (ps : PS p) (hq : SPub p s₀ s₀') : lastB p F s₀ = lastB p F s₀' := by
  unfold lastB
  by_cases h : Good p F s₀
  · have h' := (good_iff ps hq).mp h
    have hr : Run p F (NI p F s₀ - 1) s₀ := ⟨h, by have := NI_pos (p := p) F s₀; omega_using [this]⟩
    obtain ⟨ect, hb⟩ := run_at ps hq hr
    rw [← NI_eq ps hq, ← ect, decide_eq_true h, decide_eq_true h']
    cases e : F.ballF p.τ (CTv p s₀ (p.ℓ * (NI p F s₀ - 1)))
    · simp only [Bool.true_and, Bool.false_and]
    · simp only [Bool.true_and]
      exact decide_eq_decide.mpr (hb e).1
  · have h' : ¬ Good p F s₀' := fun h' => h ((good_iff ps hq).mpr h')
    rw [decide_eq_false h, decide_eq_false h', Bool.false_and, Bool.false_and, Bool.false_and, Bool.false_and]

/-- The private key, the loop, and the signature if the last iteration passed. -/
theorem rest_piece (F : PrimsOk P) (ps : PS p) :
    SP p (fun s₀ s => (∃ s', IA p F.rejF (p.k * p.ℓ) s₀ s' ∧ Ctx (Y p) s₀ s ∧ s.mem = s'.mem) ∧
      okE p F.rejF s₀ (p.k * p.ℓ) = true) (RD p F) (rest P p) := by
  unfold rest
  refine Piece.seq (B := fun s₀ s => KD p s₀ s ∧ Good p F s₀) ((sp_pure (Good p F) (rpp_piece ps)).mono
    (fun s₀ s _ h => ?_) fun _ _ _ h => h) ?_
  · obtain ⟨⟨s', ia, c, m⟩, hg⟩ := h
    exact ⟨⟨c, ⟨by rw [m]; exact ia.fam hg, by rw [m]; exact ia.dk.f1, by rw [m]; exact ia.dk.f2,
      by rw [m]; exact ia.dk.f0⟩⟩, hg⟩
  refine Piece.seq (signLoop_piece F ps) ?_
  refine okIte_piece (sc_ok' ps (by decide) (by decide)) (lastB p F) (fun s₀ s _ h => ⟨h.ctx, ?_⟩)
    (fun s₀ s₀' _ _ hq => lastB_eq ps hq) ?_ ?_
  · rw [h.ok]; simp only [lastB, decide_eq_true h.run.1, Bool.true_and]
  · let U : State → Nat := fun s₀ => NI p F s₀ - 1
    let φ : State → Prop := fun s₀ => Run p F (U s₀) s₀ ∧ F.ballF p.τ (CTv p s₀ (p.ℓ * U s₀)) = true ∧
      passS p (U s₀) s₀
    refine ((sp_pure φ (output_piece F ps U fun s₀ s₀' _ _ hq => by
      simp only [U, NI_eq ps hq])).mono (fun s₀ s hp h => ?_) fun s₀ s _ h => ?_)
    · obtain ⟨⟨s', fn, c, m⟩, hb⟩ := h
      simp only [lastB, Bool.and_eq_true, decide_eq_true_eq] at hb
      obtain ⟨⟨_, hs⟩, hq⟩ := hb
      obtain ⟨f1, f2, f3⟩ := fn.out hs hq
      refine ⟨⟨c, by rw [m]; exact f1, by rw [m]; exact f2, fn.run, hs, hq, ?_, by rw [m]; exact f3⟩, fn.run, hs, hq⟩
      rw [scw, m, ← scw, fn.ok, hs, decide_eq_true hq]; rfl
    · obtain ⟨⟨c, ok1, sg⟩, hr, hs, hq⟩ := h
      refine ⟨c, hr, by rw [ok1, hs, decide_eq_true hq]; rfl, fun _ _ => sg, fun e => by rw [hs] at e; cases e⟩
  · refine nil_piece fun s₀ s _ h => ?_
    obtain ⟨⟨s', fn, c, m⟩, hb⟩ := h
    refine ⟨c, fn.run, by rw [scw, m, ← scw]; exact fn.ok, fun hs hq => ?_, fn.none⟩
    simp only [lastB, decide_eq_true fn.run.1, hs, decide_eq_true hq] at hb
    cases hb

/-- What the rest leaves is `Sign_internal`'s outcome. -/
theorem rest_outcome {F : PrimsOk P} (ps : PS p) {s₀ s : State} (h : RD p F s₀ s) :
    Outcome (fun b => signMu p b (skOf p s₀) (muOf s₀) (rndOf s₀)) (scw s₀ s oOK)
      (bytesAt s.mem (Buf.addr s₀ (bSig 0 p.sigLen)) p.sigLen) := by
  have hg := h.run.1
  have hA := expandA_good hg
  have hNI := NI_good hg
  have hpos := NI_pos (p := p) F s₀
  have hlt := h.run.lt
  have hc := h.run.cont
  cases hs : F.ballF p.τ (CTv p s₀ (p.ℓ * (NI p F s₀ - 1)))
  · refine .inr ⟨by rw [h.ok, hs, Bool.false_and]; rfl, signMu_min_L hA ?_⟩
    exact loopV_none_ball ps.hok F.ballMax hc (h.none hs)
  · by_cases hq : passS p (NI p F s₀ - 1) s₀
    · refine .inl ⟨by rw [h.ok, hs, decide_eq_true hq]; rfl, maxBounds, ?_⟩
      rw [h.sig hs hq, ← sigOf_eq]
      exact signMu_some hA (loopV_pass ps.hok F.ballMax (by show _ < 1000; omega_using [hlt]) hc hs hq)
    · refine .inr ⟨by rw [h.ok, hs, decide_eq_false hq]; rfl, signMu_min_L hA ?_⟩
      have hcu : contS p F (NI p F s₀ - 1) s₀ = true := by
        simp only [contS, contV, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
        exact ⟨hs, hq⟩
      have hn : NI p F s₀ - 1 + 1 < NI p F s₀ ↔ contS p F (NI p F s₀ - 1) s₀ = true ∧ NI p F s₀ - 1 + 1 < 814 := by
        rw [hNI]; exact nIt_next _ (by have : NI p F s₀ - 1 < NI p F s₀ := by omega_using [hpos]
                                       rw [hNI] at this; exact this)
      have hu : NI p F s₀ - 1 = 813 := by
        by_contra hne
        exact absurd (hn.mpr ⟨hcu, by omega_using [hlt, hne]⟩) (by omega_using [])
      refine loopV_none_exh ps.hok F.ballMax fun j hj => ?_
      rcases (by omega_using [hu, hj] : j < NI p F s₀ - 1 ∨ j = NI p F s₀ - 1) with hj' | rfl
      · exact hc j hj'
      · exact hcu

/-! ## The body -/

/-- What signing returns, and leaves in `sig`, from the initial state `s₀`. -/
def Done (p : Params) (s₀ s : State) : Prop :=
  Outcome (fun b => signMu p b (skOf p s₀) (muOf s₀) (rndOf s₀)) (s.gpr .eax)
    (bytesAt s.mem (Buf.addr s₀ (bSig 0 p.sigLen)) p.sigLen)

theorem ldsc_tt : (VG.X86.taint.check (τr [.esp]) (.block [.mov .esi (.mem (at_ .esp (20 + 4 * SC)))])
    (VG.X86.taint.hintOf (τr [.esp]) (.block [.mov .esi (.mem (at_ .esp (20 + 4 * SC)))]))).isSome = true := by
  native_taint_decide

/-- `esi ← scratch`, which leaves memory as the leaf's push did. -/
theorem ldscM_piece :
    SP p (fun s₀ s => s = P0 s₀) (fun s₀ s => Ctx (Y p) s₀ s ∧ s.mem = (P0 s₀).mem)
      (.block [.mov .esi (.mem (at_ .esp (20 + 4 * SC)))]) where
  wp s₀ s hp e := by
    subst e
    have ea : (P0 s₀).ea (at_ .esp (20 + 4 * SC)) = argAddr s₀ SC := VG.Proof.MlKem.X86.P0_argAddr s₀ SC
    refine wp_movm' (by rw [ea]; exact VG.Proof.MlKem.X86.P0_argIn hp.sc_lt hp.sp' hp.gwr) fun s₁ o₁ v₁ => WP.block_nil_iff.mpr ?_
    refine ⟨⟨by rw [o₁.gpr _ (by decide)], o₁.rd, o₁.wr, ?_, by rw [o₁.mem]; exact Frame.refl _ _⟩, o₁.mem⟩
    rw [v₁, ea]
    exact VG.Proof.MlKem.X86.P0_arg hp.E0_big hp.sc_lt hp.sp' (by rw [hp.fr16]; exact hp.stk_g.sub_left hp.frame_sub)
  ct := (lift (p := p) (ldsc_piece (Y := Y p) (lk := lk0) ldsc_tt)).ct

/-- The bytes of a buffer, after the leaf's push, as on entry. -/
theorem p0_keep {s₀ : State} (hp : TPre (Y p) s₀) {b : Buf} (hb : (Y p).ok b = true) :
    ∀ i < b.len, (P0 s₀).mem (b.addr s₀ + BitVec.ofNat 64 i) = s₀.mem (b.addr s₀ + BitVec.ofNat 64 i) := by
  obtain ⟨h₁, -, -⟩ := Lay.ok_iff.mp hb
  exact VG.Proof.MlKem.bytes_frame (VG.Proof.MlKem.X86.P0_mem hp.E0_big) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact (((hp.stk_a _ h₁).sub_left hp.frame_sub).sub_right (Buf.sub hp hb)).symm)
    (by have := Buf.fit hp hb; omega_using [this])

/-- `KEYS` is 0, or `scratch` holds the private key's polynomials on entry. -/
def KeysPre (p : Params) (s₀ : State) : Prop := keysW s₀ = 0 ∨ DKs p p.ℓ p.k p.k s₀ s₀.mem

theorem dks_p0 {s₀ : State} (hp : TPre (Y p) s₀) (ps : PS p) (h : DKs p p.ℓ p.k p.k s₀ s₀.mem) :
    DKs p p.ℓ p.k p.k s₀ (P0 s₀).mem := by
  have fam : ∀ {b n : Nat} {f : Nat → Poly}, b + n ≤ nS p → Fam s₀ s₀.mem b n f → Fam s₀ (P0 s₀).mem b n f :=
    fun hb hf j hj => VG.Proof.MlDsa.Sign.polyIs_congr (p0_keep hp (slot_ok' ps (by omega_using [hb, hj]))) (hf j hj)
  exact ⟨fam (by simp only [nS, s1B]; omega_arith) h.f1, fam (by simp only [nS, s2B]; omega_arith) h.f2,
    fam (by simp only [nS, t0B]; omega_arith) h.f0⟩

/-- The branch on `KEYS`, which is nonzero as on entry. -/
theorem keysIte_piece {A B : State → State → Prop} (ps : PS p) {t e : Prog isa}
    (hA : ∀ s₀ s, TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s ∧ scw s₀ s oKEYS = keysW s₀)
    (ht : SP p (fun s₀ s₁ => (∃ s, A s₀ s ∧ Ctx (Y p) s₀ s₁ ∧ s₁.mem = s.mem) ∧ (keysW s₀ != 0) = true) B t)
    (he : SP p (fun s₀ s₁ => (∃ s, A s₀ s ∧ Ctx (Y p) s₀ s₁ ∧ s₁.mem = s.mem) ∧ (keysW s₀ != 0) = false) B e) :
    SP p A B (ifKeysElse t e) := by
  refine Piece.seq (B := fun s₀ s₁ => (∃ s, A s₀ s ∧ Ctx (Y p) s₀ s₁ ∧ s₁.mem = s.mem) ∧
    s₁.zf = some (!(keysW s₀ != 0))) (blk_piece (fun s₀ s hp ha => (hA s₀ s hp ha).1) (fun s₀ s hp ha => ?_) rfl) ?_
  · obtain ⟨h, hk⟩ := hA s₀ s hp ha
    refine wp_ldsc hp h (sc_ok' ps (by decide) (by decide)) fun s₁ o₁ v₁ => wp_test fun s₂ o₂ z₂ =>
      WP.block_nil_iff.mpr ?_
    have o := o₁.trans o₂
    refine ⟨⟨s, ha, h.only o (by simp) (by simp), o.mem⟩, ?_⟩
    rw [z₂, v₁, hk, BitVec.and_self]
    simp [bne]
  · refine Piece.ite (fun s₀ => keysW s₀ != 0) (fun s₀ s₁ hp ha => ?_) (fun s₀ s₀' _ _ hq => ?_)
      (ht.mono (fun _ _ _ h => ⟨h.1.1, h.2⟩) fun _ _ _ h => h)
      (he.mono (fun _ _ _ h => ⟨h.1.1, h.2⟩) fun _ _ _ h => h)
    · show s₁.zf.map (!·) = _
      rw [ha.2]; cases (keysW s₀ != 0) <;> rfl
    · have e := hq.1.2.2
      simp only [keysOf, List.cons.injEq, and_true] at e
      by_cases h₁ : keysW s₀ = 0 <;> by_cases h₂ : keysW s₀' = 0 <;> simp only [h₁, h₂, ↓reduceIte] at e ⊢
      · cases e
      · cases e
      · rw [bne_iff_ne.mpr h₁, bne_iff_ne.mpr h₂]

/-- The private key's polynomials: decoded, or as `scratch` holds them on entry. -/
theorem keysOpt_piece (F : PrimsOk P) (ps : PS p) :
    SP p (fun s₀ s => (Ctx (Y p) s₀ s ∧ s.mem = (P0 s₀).mem) ∧ KeysPre p s₀)
      (fun s₀ s => Ctx (Y p) s₀ s ∧ DKs p p.ℓ p.k p.k s₀ s.mem) (keysOpt P p) := by
  unfold keysOpt
  refine keysIte_piece ps (fun s₀ s hp h => ⟨h.1.1, ?_⟩) (nil_piece fun s₀ s hp h => ?_)
    ((keys_piece F ps).mono (fun s₀ s _ h => ⟨h.1.choose_spec.2.1, ?_⟩) fun _ _ _ h => h)
  · rw [scw, h.1.2]
    exact Mem.readW_congr fun i hi => p0_keep hp (sc_ok' ps (by decide) (by decide)) i hi
  · obtain ⟨⟨s', ⟨⟨_, m⟩, kp⟩, c', m'⟩, hb⟩ := h
    refine ⟨c', ?_⟩
    rw [m', m]
    rcases kp with kp | kp
    · rw [kp] at hb; cases hb
    · exact dks_p0 hp ps kp
  · exact ⟨fun j hj => absurd hj (Nat.not_lt_zero _), fun j hj => absurd hj (Nat.not_lt_zero _),
      fun j hj => absurd hj (Nat.not_lt_zero _)⟩

/-- The body of `vg_mldsa*_sign`. -/
theorem body_piece (F : PrimsOk P) (ps : PS p) :
    SP p (fun s₀ s => s = P0 s₀ ∧ KeysPre p s₀) (fun s₀ s => Ctx (Y p) s₀ s ∧ Done p s₀ s) (body P p) := by
  unfold body
  refine Piece.seq (sp_pure (KeysPre p) ldscM_piece) ?_
  refine Piece.seq (keysOpt_piece F ps) ?_
  refine Piece.seq (B := fun s₀ s => Ctx (Y p) s₀ s ∧ scw s₀ s oOK = 1 ∧ DKs p p.ℓ p.k p.k s₀ s.mem)
    (blk_piece (fun _ _ _ h => h.1) (fun s₀ s hp h => ?_) rfl) ?_
  · rw [← List.append_nil (st32 oOK 1)]
    exact wp_st32 hp h.1 (sc_ok ps (by decide) (by decide)) 1 fun s' c' fr v => WP.block_nil_iff.mpr
      ⟨c', v, h.2.keep hp ps (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (by decide) fr (by ofsd)⟩
  refine Piece.seq (expandA_piece F ps) ?_
  refine Piece.seq (B := fun s₀ s => Ctx (Y p) s₀ s ∧ Outcome (fun b => signMu p b (skOf p s₀) (muOf s₀) (rndOf s₀))
      (scw s₀ s oOK) (bytesAt s.mem (Buf.addr s₀ (bSig 0 p.sigLen)) p.sigLen))
    (okIte_piece (sc_ok' ps (by decide) (by decide)) (fun s₀ => okE p F.rejF s₀ (p.k * p.ℓ))
      (fun _ _ _ h => ⟨h.ctx, h.ok⟩) (fun _ _ _ _ hq => okE_eq ps hq _)
      ((rest_piece F ps).mono (fun _ _ _ h => h) fun _ _ _ h => ⟨h.ctx, rest_outcome ps h⟩)
      (nil_piece fun s₀ s _ h => ?_)) ?_
  · obtain ⟨⟨s', ia, c, m⟩, hb⟩ := h
    refine ⟨c, .inr ⟨by rw [scw, m, ← scw, ia.ok, hb]; rfl, signMu_min_A (ia.bad hb)⟩⟩
  refine blk_piece (fun _ _ _ h => h.1) (fun s₀ s hp h => wp_ldsc hp h.1 (sc_ok' ps (by decide) (by decide))
    fun s' o' v' => WP.block_nil_iff.mpr ⟨h.1.only o' (by simp) (by simp), ?_⟩) rfl
  unfold Done
  rw [v', o'.mem]
  exact h.2

end VG.Proof.MlDsa.X86.Sign

end

end

/-! ### `MlDsa.X86.Sign.Top`, which only this module used -/

section

/-!
# ML-DSA signing on x86 (32-bit): `vg_mldsa{44,65,87}_sign`

The body in the leaf's frame (`piece`), and `Verified` against `signContract`
(`verified`), for any implementations of the primitives that `PrimsOk` says
are verified, and any of the three parameter sets.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece P0 LeafPost satState)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params} {P : Prims}

/-- A piece whose precondition on the initial state is part of `Pre`. -/
theorem pre_pure {Pre : State → Prop} {Pub : State → State → Prop} {A B : State → State → Prop} {c : Prog isa}
    (φ : State → Prop) (h : Piece Pre Pub (fun s₀ s => A s₀ s ∧ φ s₀) B c) :
    Piece (fun s => Pre s ∧ φ s) Pub A B c where
  wp s₀ s h₀ ha := h.wp s₀ s h₀.1 ⟨ha, h₀.2⟩
  ct s₀ s₀' h₀ h₀' hq := (h.ct s₀ s₀' h₀.1 h₀'.1 hq).mono (fun _ _ ⟨a, a'⟩ => ⟨⟨a, h₀.2⟩, ⟨a', h₀'.2⟩⟩)
    fun _ _ h => h

/-- The runs' precondition: the layout, and `KEYS`. -/
abbrev KPre (p : Params) (s₀ : State) : Prop := TPre (Y p) s₀ ∧ KeysPre p s₀

/-- `vg_mldsa*_sign_core`, a leaf around `body`. -/
theorem piece (F : PrimsOk P) (ps : PS p) (hsp : NoSp (body P p)) :
    Piece (KPre p) (SPub p) (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (Done p s₀) s₀ s') (sign P p) := by
  have hb := pre_pure (KeysPre p) (body_piece F ps)
  exact Piece.leaf (W (Y p)) hsp (fun _ hp => ⟨hp.1.E0_big, by have := hp.1.sp'; omega_using [this]⟩) (fun _ hp => hp.1.hW)
    (fun _ _ _ _ hq => hq.1.1) (hb.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨⟨h.1.frame, h.1.esp, h.1.rd, h.1.wr⟩, h.2⟩)

/-- `KEYS` as the contract says it. -/
theorem keysW_eq (ps : PS p) {s₀ : State} (hp : TPre (Y p) s₀) :
    keysW s₀ = keysWord s₀.mem ((arg s₀ 4).setWidth 64) := by
  unfold keysW keysWord
  rw [Buf.addr_eq hp (sc_ok' ps (by decide) (by decide))]

theorem slot_addr (ps : PS p) {s₀ : State} (hp : TPre (Y p) s₀) {j : Nat} (hj : j < nS p) :
    Buf.addr s₀ (pS j) = (arg s₀ 4).setWidth 64 + BitVec.ofNat 64 (oP j) :=
  Buf.addr_eq hp (slot_ok' ps hj)

/-- The contract's precondition on `KEYS`, as the proof's. -/
theorem keysPre_of (ps : PS p) {s₀ : State} (hp : TPre (Y p) s₀)
    (h : keysWord s₀.mem ((arg s₀ 4).setWidth 64) = 0 ∨
      KeysIn p s₀.mem ((arg s₀ 4).setWidth 64) (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.skLen)) :
    KeysPre p s₀ := by
  have hk := ps.hk
  have hl := ps.hl
  rcases h with h | h
  · exact .inl (by rw [keysW_eq ps hp]; exact h)
  have sk : skOf p s₀ = bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.skLen := by
    simp only [skOf, bSk, addr0]
  refine .inr ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · have e := h j (by omega_using [hj])
    rw [PreparedKey.secret_s1 p _ hj, ← sk] at e
    rw [slot_addr ps hp (by simp only [nS, s1B]; omega_using [hj])]
    exact e
  · have e := h (p.ℓ + j) (by omega_using [hj])
    rw [PreparedKey.secret_s2 p _ hj, ← sk,
      show 5 + 2 * p.k + 2 * p.ℓ + (p.ℓ + j) = s2B p + j by simp only [s2B]; omega_using []] at e
    rw [slot_addr ps hp (by simp only [nS, s2B]; omega_using [hj])]
    exact e
  · have e := h (p.ℓ + p.k + j) (by omega_using [hj])
    rw [PreparedKey.secret_t0 p _ hj, ← sk,
      show 5 + 2 * p.k + 2 * p.ℓ + (p.ℓ + p.k + j) = t0B p + j by simp only [t0B]; omega_using []] at e
    rw [slot_addr ps hp (by simp only [nS, t0B]; omega_using [hj])]
    exact e

theorem core_pub_of (ps : PS p) {s₀ s₀' : State} (hp : TPre (Y p) s₀) (hp' : TPre (Y p) s₀')
    (h : (signCoreContract p X86.abi 96).pub s₀ s₀') : SPub p s₀ s₀' := by
  sig_pub [signCoreContract, signSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, a0, a1, a2, a3, a4⟩ := h
  simp only [List.cons.injEq] at e₂
  refine ⟨⟨e₁, fun i hi => ?_, ?_⟩, ?_⟩
  · rw [Y_n] at hi
    obtain rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega_using [hi]
    exacts [a0, a1, a2, a3, a4]
  · have e := e₂.1
    simp only [keysOf, keysW_eq ps hp, keysW_eq ps hp']
    by_cases h₁ : keysWord s₀.mem ((arg s₀ 4).setWidth 64) = 0 <;>
      by_cases h₂ : keysWord s₀'.mem ((arg s₀' 4).setWidth 64) = 0 <;>
      simp only [h₁, h₂, ↓reduceIte] at e ⊢ <;> cases e
  · simp only [skOf, muOf, rndOf, bSk, bMu, bRnd, addr0]
    exact e₂.2

/-- Memory with the arguments `0`, `0x2000`, `0x3000`, `0x8000` and `0x10000` at `0x5004`. -/
def satMem : Mem := fun a =>
  if a = 0x5009 then 0x20 else if a = 0x500d then 0x30 else if a = 0x5011 then 0x80 else if a = 0x5016 then 1 else 0

theorem sat (h3 : Ok3 p) : ∃ s, (signCoreContract p X86.abi 96).pre s := by
  rcases h3 with rfl | rfl | rfl
  · refine ⟨satState satMem [⟨0, 2560⟩, ⟨0x2000, 64⟩, ⟨0x3000, 32⟩] [⟨0x8000, 2420⟩, ⟨0x10000, 77824⟩, ⟨0x5004, 20⟩], ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [signCoreContract, signSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      sig_and_intros
      all_goals first
        | trivial
        | exact Or.inl (by decide +kernel)
        | decide +kernel
  · refine ⟨satState satMem [⟨0, 4032⟩, ⟨0x2000, 64⟩, ⟨0x3000, 32⟩] [⟨0x8000, 3309⟩, ⟨0x10000, 103424⟩, ⟨0x5004, 20⟩], ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [signCoreContract, signSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      sig_and_intros
      all_goals first
        | trivial
        | exact Or.inl (by decide +kernel)
        | decide +kernel
  · refine ⟨satState satMem [⟨0, 4896⟩, ⟨0x2000, 64⟩, ⟨0x3000, 32⟩] [⟨0x8000, 4627⟩, ⟨0x10000, 144384⟩, ⟨0x5004, 20⟩], ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [signCoreContract, signSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      sig_and_intros
      all_goals first
        | trivial
        | exact Or.inl (by decide +kernel)
        | decide +kernel

/-- `vg_mldsa{44,65,87}_sign_core`, with the primitives `P`, is verified against `signCoreContract`. -/
theorem verified (F : PrimsOk P) (h3 : Ok3 p) (hsp : NoSp (body P p)) :
    Verified X86.target (sign P p) (signCoreContract p X86.abi 96) := by
  have ps := PS.of h3
  refine Piece.verified (((piece F ps hsp).pre_mono
    (fun _ h => ⟨(core_pre_of h).1, keysPre_of ps (core_pre_of h).1 (core_pre_of h).2⟩)
    fun _ _ h h' hq => core_pub_of ps (core_pre_of h).1 (core_pre_of h').1 hq).mono
    (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) (sat h3)
  obtain ⟨habi, -, -, s, hd, hm, hax⟩ := hq
  refine ⟨habi, ?_⟩
  sig_post [signCoreContract, signSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  obtain hok : (Y p).ok ⟨3, 0, p.sigLen⟩ = true := by ofs
  rw [sw32, hax, argKeep (core_pre_of h₀).1 hm (k := 3) (l := p.sigLen) hok]
  unfold Done at hd
  simp only [skOf, muOf, rndOf, bSk, bMu, bRnd, bSig, addr0] at hd
  exact hd

end VG.Proof.MlDsa.X86.Sign

end

end


/-!
# ML-DSA signing on x86 (32-bit): verified

`vg_mldsa{44,65,87}_sign_core` (`sign prims p`) with the x86 primitives, verified
against `signCoreContract` (`verified`, with `prims_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlDsa.X86.Sign
open VG.Spec.MlDsa

/-- The body of `vg_mldsa44_sign_core` never writes `esp`: the one evaluation
of its code, which its callers take (`NoSp.leaf`, `SignEntry.signEntry_nosp`). -/
theorem body44_nosp : NoSp (body prims mlDsa44) := NoSp.of_all (by lit_decide)

theorem signCore44_verified : Verified X86.target (sign prims mlDsa44) (signCoreContract mlDsa44 X86.abi 96) :=
  verified prims_ok (.inl rfl) body44_nosp

/-- The body of `vg_mldsa65_sign_core` never writes `esp`: the one evaluation
of its code, which its callers take (`NoSp.leaf`, `SignEntry.signEntry_nosp`). -/
theorem body65_nosp : NoSp (body prims mlDsa65) := NoSp.of_all (by lit_decide)

theorem signCore65_verified : Verified X86.target (sign prims mlDsa65) (signCoreContract mlDsa65 X86.abi 96) :=
  verified prims_ok (.inr (.inl rfl)) body65_nosp

/-- The body of `vg_mldsa87_sign_core` never writes `esp`: the one evaluation
of its code, which its callers take (`NoSp.leaf`, `SignEntry.signEntry_nosp`). -/
theorem body87_nosp : NoSp (body prims mlDsa87) := NoSp.of_all (by lit_decide)

theorem signCore87_verified : Verified X86.target (sign prims mlDsa87) (signCoreContract mlDsa87 X86.abi 96) :=
  verified prims_ok (.inr (.inr rfl)) body87_nosp

end VG.Proof.MlDsa.X86.Sign
