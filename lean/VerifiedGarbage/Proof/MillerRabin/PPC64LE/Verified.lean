module

public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFn
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Last
public import VerifiedGarbage.Proof.MillerRabin.Contract
import VerifiedGarbage.Proof.Ffdh.MillerRabin
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Eq
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.MillerRabin.PPC64LE.Round
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.MillerRabin.Representation
import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Last
meta import VerifiedGarbage.Proof.MillerRabin.Contract
meta import VerifiedGarbage.Proof.Ffdh.MillerRabin
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Eq
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
meta import VerifiedGarbage.Impl.MillerRabin.PPC64LE.Round
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFn
meta import VerifiedGarbage.Proof.MillerRabin.Representation
meta import VerifiedGarbage.Proof.Bignum.Math

/-! ### `Bignum.PPC64LE.MontVerified`, which only this module used -/

section

/-!
# Montgomery multiplication on PPC64LE: reading the working space

Two states that agree on the working space read the same words from it
(`agree_read`, `agree_readW`).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum.PPC64LE VG.Impl.Bignum
open VG.Proof.Rsa.Mont (numAt wOf wordAt Layout Operand Keeps arrAt aM minvWord)

/-! ## Reading memory within the working space -/

theorem agree_read {m₁ m₂ : Mem} {ws : Addr} {L d k : Nat}
    (h : ∀ a, (⟨ws, L⟩ : Region).Contains a 1 → m₁ a = m₂ a) (hk : d + k ≤ L) (hk' : d + k < 2 ^ 64) :
    m₁.read (ws + BitVec.ofNat 64 d) k = m₂.read (ws + BitVec.ofNat 64 d) k :=
  Mem.read_congr fun i hi => h _ (by
    simp only [Region.Contains]
    rw [Offset.add_add, Mem.sub_ofNat_toNat _ (by omega_arith)]
    omega_arith)

theorem agree_readW {m₁ m₂ : Mem} {ws : Addr} {L d : Nat}
    (h : ∀ a, (⟨ws, L⟩ : Region).Contains a 1 → m₁ a = m₂ a) (hk : d + 8 ≤ L) (hk' : d + 8 < 2 ^ 64) :
    m₁.readW (ws + BitVec.ofNat 64 d) 64 = m₂.readW (ws + BitVec.ofNat 64 d) 64 := by
  simp only [Mem.readW, agree_read h hk hk']

end VG.Proof.Bignum.PPC64LE

end

end

/-! ### `MillerRabin.PPC64LE.CT`, which only this module used -/

section

/-! ### `MillerRabin.PPC64LE.Fn`, which this module and modules that import it used -/

section

/-! ### `MillerRabin.PPC64LE.Core`, which only this module used -/

section

/-!
# The Miller–Rabin round on PPC64LE: the round

`core_ok`: the table, the windows and the three squarings leave the mask of
`Proof.MillerRabin.Round.round c b` in `r23` (`Proof.Ffdh.window_round_eq`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.MillerRabin.PPC64LE
open VG.Proof.Bignum (slot slot_sep)
open VG.Proof.RsaKeyGen (wRun wEnd mrE)

/-- The registers the round's core writes. -/
abbrev coreRegs : List Reg := expRegs

theorem core_ok {s : State} {B : Addr} {Z w c b : Nat} (h : MCtx s B Z w) (hc : Consts s.mem B w c)
    (hc3 : 3 ≤ c) (hodd : c % 2 = 1) (h5 : arr s.mem B w 5 = b % c * 2 ^ (64 * w) % c) :
    WP isa core s fun t => MCtx t B Z w ∧ t.gpr .r23 = mask (Proof.MillerRabin.Round.round c b) ∧
      Mut B w s.mem t.mem ∧ Keep coreRegs s t := by
  have hcw : c < 16 ^ (16 * w) := by
    rw [← hc.cand, show (16 : Nat) ^ (16 * w) = 2 ^ (32 * (2 * w)) by
      rw [show (16 : Nat) = 2 ^ 4 from rfl, ← Nat.pow_mul]; congr 1; omega_using []]
    exact val32_lt _ _ _ _
  have hE : mrE c < 16 ^ (16 * w) :=
    Nat.lt_of_le_of_lt (Nat.le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _)) hcw
  unfold core
  refine WP.seq (WP.mono (table_ok h hc hc3 hodd h5) fun t₁ ⟨f1, _, tab, y1⟩ => ?_)
  have w1 : WSt expRegs t₁ t₁ B Z w c b :=
    ⟨f1.ctx, f1.consts, tab, Outs.refl _ _ _, Keep.refl _ _, by decide, by decide⟩
  refine WP.seq (WP.mono (windows_ok w1 hc3 hodd y1) fun t₂ e2 => ?_)
  refine WP.seq (WP.mono (last_ok e2.ws hc3 hodd e2.y e2.p (j := 1) (by simp)) fun t₃ ⟨w3, y3, _, p3⟩ => ?_)
  refine WP.seq (WP.mono (last_ok w3 hc3 hodd y3 p3 (j := 2) (by simp)) fun t₄ ⟨w4, y4, _, p4⟩ => ?_)
  refine WP.mono (last_ok w4 hc3 hodd y4 p4 (j := 3) (by simp)) fun t ⟨w5, _, _, p5⟩ =>
    ⟨w5.ctx, ?_, Outs.trans f1.muts (winRanges_mut w5.outs), (f1.keep.trans w5.keep).mono (by decide)⟩
  rw [p5]
  congr 1
  show (wEnd c (wRun c b (mrE c) (16 * w) (16 * w))).2 = _
  rw [VG.Proof.Ffdh.window_round_eq (W := 16 * w) b hc3 hodd hE, ← VG.Proof.Ffdh.rsa_round_eq b hc3 hodd]
  rfl

end VG.Proof.MillerRabin.PPC64LE

end

end

/-! ### `MillerRabin.PPC64LE.Save`, which only this module used -/

section

/-!
# The Miller–Rabin round on PPC64LE: saving and restoring the nonvolatile registers

As `Proof/Bignum/PPC64LE/MontSave.lean`: `save` stores `r14`–`r31` in the
144-byte scratch buffer at `r5`, and copies its address into `r21`;
`restore` loads them back through `r21`, `r21` last.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.PPC64LE.Save

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Impl.MillerRabin.PPC64LE

/-- The scratch buffer, 144 bytes. -/
abbrev savR (w : Addr) : Region := ⟨w, 144⟩

theorem saved_inj : ∀ i < 18, ∀ j < 18, saved i = saved j → i = j := by decide

theorem saved_ne : ∀ i < 17, saved i ≠ .r21 := by decide

theorem saved_17 : saved 17 = .r21 := rfl

theorem sav_contains (w : Addr) {i : Nat} (hi : i < 18) : (savR w).Contains (off w (8 * i)) 8 :=
  Offset.contains_base w (by omega_using [hi]) (by omega_using [hi])

theorem sav_sep (w : Addr) {i j : Nat} (hi : i < 18) (hj : j < 18) (h : i ≠ j) :
    Mem.Sep (off w (8 * i)) 8 (off w (8 * j)) 8 :=
  Offset.sep w (by omega_using [hi, hj, h]) (by omega_using [hi]) (by omega_using [hj])

/-- The first `n` registers are saved. -/
structure SI (s₀ : State) (n : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.lr = s₀.lr
  frame : Frame [savR (s₀.gpr .r5)] s₀.mem s.mem
  saved : ∀ i < n, s.mem.readW (off (s₀.gpr .r5) (8 * i)) 64 = s₀.gpr (saved i)

theorem save_step (s₀ : State) (hin : savR (s₀.gpr .r5) ∈ s₀.wr) {n : Nat} (hn : n < 18) {s : State}
    (h : SI s₀ n s) : WP isa (.block [.store .d (saved n) .r5 (8 * n)]) s (SI s₀ (n + 1)) := by
  have hw : s.gpr .r5 = s₀.gpr .r5 := by rw [h.gpr]
  have hout : InRegions s.wr (s.gpr .r5 + BitVec.ofNat 64 (8 * n)) 8 := by
    rw [h.wr, hw]; exact ⟨_, hin, sav_contains _ hn⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_store_d (show Reg.r5 ≠ .r0 by decide) (show 8 * n < 2 ^ 15 ∧ (8 * n) % 4 = 0 by omega_using [hn])
      hout, Option.some.injEq, exists_eq_left', hw]
  refine ⟨h.gpr, h.rd, h.wr, h.sp, h.lr,
    h.frame.writeW (List.mem_singleton_self _) _ (sav_contains _ hn), fun i hi => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · rw [Mem.readW_writeW_sep (sav_sep _ (by omega_using [hi, hn]) hn (by omega_using [hi])) (by decide)]
    exact h.saved i hi
  · rw [Mem.readW_writeW_self64, h.gpr]

/-- The state after `save`. -/
structure Saved (s₀ : State) (s : State) : Prop where
  keep : Keep [.r21] s₀ s
  r21 : s.gpr .r21 = s₀.gpr .r5
  frame : Frame [savR (s₀.gpr .r5)] s₀.mem s.mem
  saved : ∀ i < 18, s.mem.readW (off (s₀.gpr .r5) (8 * i)) 64 = s₀.gpr (saved i)

theorem save_ok (s₀ : State) (hin : savR (s₀.gpr .r5) ∈ s₀.wr) : WP isa (.block save) s₀ (Saved s₀) := by
  rw [save]
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (SI s₀)
    (fun k s hk h => save_step s₀ hin hk h) 18 (Nat.le_refl _) s₀
    ⟨rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s h => ?_)
  have hw : s.gpr .r5 = s₀.gpr .r5 := by rw [h.gpr]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addi (show Reg.r5 ≠ .r0 by decide)
    (show 0 < 2 ^ 15 by decide), BitVec.add_zero, Option.some.injEq, exists_eq_left', hw]
  refine ⟨⟨fun r hr => ?_, h.rd, h.wr, h.sp, h.lr⟩, ?_, h.frame, h.saved⟩
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e fun e => hr (by simp [e]), h.gpr]
  · rw [gpr_write, ite_eq_left_iff.mpr fun e => absurd rfl e]

/-- The first `n` registers are restored to `v`, from the state `sB` the
restoring starts in. -/
structure RI (sB : State) (w : Addr) (v : Nat → BitVec 64) (n : Nat) (s : State) : Prop where
  r21 : s.gpr .r21 = w
  restored : ∀ i < n, s.gpr (saved i) = v i
  others : ∀ r, (∀ i < 18, r ≠ saved i) → s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  sp : s.sp = sB.sp
  lr : s.lr = sB.lr

theorem restore_step (sB : State) {w : Addr} {v : Nat → BitVec 64} (hsin : savR w ∈ sB.wr)
    (hsav : ∀ i < 18, sB.mem.readW (off w (8 * i)) 64 = v i)
    {n : Nat} (hn : n < 17) {s : State} (h : RI sB w v n s) :
    WP isa (.block [.load .d (saved n) .r21 (8 * n)]) s (RI sB w v (n + 1)) := by
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r21 + BitVec.ofNat 64 (8 * n)) 8 := by
    rw [h.rd, h.wr, h.r21]; exact ⟨_, List.mem_append_right _ hsin, sav_contains _ (by omega_using [hn])⟩
  have hv : s.mem.readW (w + BitVec.ofNat 64 (8 * n)) 64 = v n := by
    rw [h.mem]; exact hsav n (by omega_using [hn])
  have hn21 := saved_ne n hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show Reg.r21 ≠ .r0 by decide) (show 8 * n < 2 ^ 15 ∧ (8 * n) % 4 = 0 by
      omega_using [hn]) hin, Option.some.injEq, exists_eq_left', h.r21, hv]
  refine ⟨?_, fun i hi => ?_, fun r hr => ?_, h.mem, h.rd, h.wr, h.sp, h.lr⟩
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (Ne.symm hn21)]; exact h.r21
  · rw [gpr_write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have e : saved i ≠ saved n := fun e =>
        absurd (saved_inj i (by omega_using [hi, hn]) n (by omega_using [hn]) e) (by omega_using [hi])
      rw [ite_eq_right_iff.mpr fun e' => absurd e' e]; exact h.restored i hi
    · rw [ite_eq_left_iff.mpr fun e => absurd rfl e]
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (hr n (by omega_using [hn]))]
    exact h.others r hr

/-- `restore`, from a state whose scratch buffer, at `r21`, holds `v`. -/
theorem restore_ok (sB : State) {w : Addr} {v : Nat → BitVec 64} (hw : sB.gpr .r21 = w)
    (hsin : savR w ∈ sB.wr) (hsav : ∀ i < 18, sB.mem.readW (off w (8 * i)) 64 = v i) :
    WP isa (.block restore) sB fun s =>
      (∀ i < 18, s.gpr (saved i) = v i) ∧ (∀ r, (∀ i < 18, r ≠ saved i) → s.gpr r = sB.gpr r) ∧
      s.mem = sB.mem ∧ s.rd = sB.rd ∧ s.wr = sB.wr ∧ s.sp = sB.sp ∧ s.lr = sB.lr := by
  rw [restore]
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (RI sB w v)
    (fun k s hk h => restore_step sB hsin hsav hk h) 17 (Nat.le_refl _) sB
    ⟨hw, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩) fun s h => ?_)
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r21 + BitVec.ofNat 64 136) 8 := by
    rw [h.rd, h.wr, h.r21]; exact ⟨_, List.mem_append_right _ hsin, sav_contains _ (i := 17) (by decide)⟩
  have hv : s.mem.readW (w + BitVec.ofNat 64 136) 64 = v 17 := by
    rw [h.mem]; exact hsav 17 (by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show Reg.r21 ≠ .r0 by decide) (show 136 < 2 ^ 15 ∧ 136 % 4 = 0 by decide) hin,
    Option.some.injEq, exists_eq_left', h.r21, hv]
  refine ⟨fun i hi => ?_, fun r hr => ?_, h.mem, h.rd, h.wr, h.sp, h.lr⟩
  · rw [gpr_write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [ite_eq_right_iff.mpr fun e => absurd e (saved_ne i hi)]; exact h.restored i hi
    · rw [saved_17, ite_eq_left_iff.mpr fun e => absurd rfl e]
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (saved_17 ▸ hr 17 (by decide))]
    exact h.others r hr

end VG.Proof.MillerRabin.PPC64LE.Save

end

end


/-!
# The Miller–Rabin round on PPC64LE: the function

`vg_miller_rabin_round(ws = r3, ws_len = r4, scratch = r5)` (`fnContract`):
`round` saves the nonvolatile registers in the scratch buffer, sets up the
working space's registers (`setup_ok`), runs the round (`core_ok`), and
restores them (`fn_correct`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.MillerRabin.PPC64LE
open VG.Proof.Bignum (slot slot_sep)
open VG.Proof.RsaKeyGen (mrE mrA)
open VG.Proof.Rsa.Mont (numAt wOf wordAt arrAt)

/-- The working space: `ws_len` words at `r3`. -/
abbrev wsR (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat * 8⟩

/-- `vg_miller_rabin_round(ws = r3, ws_len = r4, scratch = r5)`, the scratch
buffer 144 bytes. -/
def fnContract : Contract isa where
  pre s :=
    let ws := s.gpr .r3
    let n := (s.gpr .r4).toNat
    s.rd = [] ∧ s.wr = [wsR s, Save.savR (s.gpr .r5)] ∧ (wsR s).Disjoint (Save.savR (s.gpr .r5)) ∧
      ws.toNat + n * 8 ≤ 2 ^ 64 ∧ Proof.MillerRabin.Round.Layout Proof.MillerRabin.Round.compact s.mem ws n ∧
      Proof.MillerRabin.Round.Prepared Proof.MillerRabin.Round.compact s.mem ws
  post s t :=
    let ws := s.gpr .r3
    let w := wOf s.mem ws
    let c := numAt s.mem ws w 0
    (∀ b, numAt s.mem ws w 5 = b % c * 2 ^ (64 * w) % c →
      ((t.gpr .r3).setWidth 32).toNat = if Proof.MillerRabin.Round.round c b then 1 else 0) ∧
      Proof.MillerRabin.Round.Keeps Proof.MillerRabin.Round.compact ws (s.gpr .r4).toNat w s.mem t.mem
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      wOf s₁.mem (s₁.gpr .r3) = wOf s₂.mem (s₂.gpr .r3)

/-- A store to the scratch buffer leaves the working space. -/
theorem frame_outside {m m' : Mem} {B S : Addr} {Z : Nat} (hf : Frame [Save.savR S] m m')
    (hd : (⟨B, Z⟩ : Region).Disjoint (Save.savR S)) : Mont.Outside B Z (2 ^ 64) m m' := by
  intro x hx
  simp only [Mont.ofs] at hx
  refine hf x fun r hr hc => ?_
  simp only [List.mem_singleton] at hr
  subst hr
  have := (x - B).isLt
  exact hd x (by simp only [Region.Contains]; omega_arith) hc

/-- The round leaves the scratch buffer. -/
theorem outs_scratch {m m' : Mem} {B S : Addr} {Z : Nat} {rs : List (Nat × Nat)} (h : Outs B rs m m')
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ Z) (hd : (⟨B, Z⟩ : Region).Disjoint (Save.savR S)) {x : Addr}
    (hx : (Save.savR S).Contains x 1) : m' x = m x := by
  refine h x fun r hm => .inr ?_
  show r.1 + r.2 ≤ (x - B).toNat
  have := hr r hm
  by_contra hc
  exact hd x (by simp only [Region.Contains]; omega) hx

theorem roundRanges_le {w Z : Nat} (hZ : slot w 28 ≤ Z) : ∀ r ∈ roundRanges w, r.1 + r.2 ≤ Z := by
  have e : slot w 11 + 16 * (8 * (w + 2)) = slot w 27 := by simp only [slot]; omega_arith
  have h27 := slot_lt (w := w) (show 27 < 28 by decide)
  have l : ∀ j < 28, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_lt hj) hZ
  intro r hr
  simp only [roundRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h <;> rw [h]
  · exact l 2 (by decide)
  · exact l 3 (by decide)
  · exact l 5 (by decide)
  · exact l 6 (by decide)
  · show slot w 11 + 16 * (8 * (w + 2)) ≤ Z
    omega_arith

theorem shl1_ofNat (w : Nat) : BitVec.ofNat 64 w <<< 1 = BitVec.ofNat 64 (2 * w) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.pow_one,
    Nat.mod_mul_mod, Nat.mul_comm]

theorem stride_ofNat (w : Nat) :
    BitVec.ofNat 64 w <<< 3 + BitVec.ofNat 64 16 = BitVec.ofNat 64 (8 * (w + 2)) := by
  rw [shl3_ofNat, ← BitVec.ofNat_add]
  congr 1

/-- The registers `setup` writes. -/
def setupRegs : List Reg := [.r10, .r11, .r12, .r29, .r31]

/-- `setup`: the working space's registers. -/
theorem setup_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z) (h3 : s.gpr .r3 = B)
    (hw : s.mem.readW (off B 48) 64 = BitVec.ofNat 64 w) (hw4 : 4 ≤ w) (hw' : w ≤ 128) (hZ : slot w 28 ≤ Z)
    (hinv : (w32 s.mem B (slot w 0) * w32 s.mem B 56 + 1) % 2 ^ 32 = 0) :
    WP isa (.block setup) s fun t => (MCtx t B Z w ∧ t.mem = s.mem) ∧ Keep setupRegs s t := by
  have h0 : slot w 0 = 256 := by simp [slot, Impl.Bignum.hdrBytes]
  have h28 : 256 ≤ slot w 28 := by simp only [slot, Impl.Bignum.hdrBytes]; omega_arith
  have hb : WP isa (.block setup) s fun t =>
      (t.gpr .r31 = B ∧ t.gpr .r10 = off B 256 ∧ t.gpr .r11 = BitVec.ofNat 64 (2 * w) ∧
        t.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)) ∧
        t.gpr .r12 = (s.mem.readW (off B 56) 32).setWidth 64 ∧ t.mem = s.mem) ∧ Keep setupRegs s t := by
    refine WP.keep _ ?_ (by decide)
    unfold setup
    prun [h3, hs.ld (show 48 + 8 ≤ Z by omega_arith), hs.ld (show 56 + 4 ≤ Z by omega_arith), sW, sMinv, hw,
      stride_ofNat, shl1_ofNat, Impl.Bignum.hdrBytes, BitVec.add_zero]
  refine WP.mono hb fun t ⟨⟨t31, t10, t11, t29, t12, tm⟩, k⟩ => ⟨⟨⟨⟨hs.congr k.wr, by rw [t10, h0], t29, t11, t31,
    hw4, hw', hZ⟩, ?_, ?_⟩, tm⟩, k⟩
  · rw [t12, BitVec.toNat_setWidth]; exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (BitVec.isLt _)
  · rw [t12, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide)), tm]
    exact hinv

theorem ret_val (x : Bool) : ((BitVec.ofNat 64 1 &&& mask x).setWidth 32).toNat = if x then 1 else 0 := by
  cases x <;> decide

theorem pres_not_written : ∀ r ∈ preserved, (∀ i < 18, r ≠ Impl.MillerRabin.PPC64LE.saved i) →
    r ∉ setupRegs ++ coreRegs ++ ([.r3] : List Reg) ∧ r ≠ .r21 := by
  decide

theorem fn_correct (s : State) (h : fnContract.pre s) :
    ∃ tr t, Exec isa Impl.MillerRabin.PPC64LE.round s tr t ∧ abiPreserved s t ∧ fnContract.post s t := by
  obtain ⟨-, hwr, hdis, hnw, hL, hp⟩ := h
  have hsin : Save.savR (s.gpr .r5) ∈ s.wr := by rw [hwr]; simp
  show WP isa Impl.MillerRabin.PPC64LE.round s fun t => abiPreserved s t ∧ fnContract.post s t
  -- the layout and the prepared values
  dsimp only [Proof.MillerRabin.Round.Layout, Proof.MillerRabin.Round.compact] at hL
  obtain ⟨-, ⟨-, -, -, -⟩, h4, h128, hspace, -⟩ := hL
  dsimp only [Proof.MillerRabin.Round.Prepared, Proof.MillerRabin.Round.compact] at hp
  obtain ⟨h3, hodd, hinv, hx5, h9, h10, he, hl⟩ := hp
  simp only [wsR] at hdis
  generalize hBd : s.gpr .r3 = B at hdis hnw hspace h4 h128 h3 hodd hinv hx5 h9 h10 he hl
  generalize hZd : (s.gpr .r4).toNat * 8 = Z at hdis hnw
  generalize hwd : wOf s.mem B = w at hspace h4 h128 h3 hodd hinv hx5 h9 h10 he hl
  generalize hcd : numAt s.mem B w 0 = c at h3 hodd hx5 h9 h10 he hl
  have hZ : slot w 28 ≤ Z := by
    rw [← hZd]; change slot w 28 ≤ 8 * (s.gpr .r4).toNat at hspace; omega_arith
  have hs : Scr s B Z := Scr.of_mem (by rw [hwr, ← hBd, ← hZd]; simp) hnw
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  obtain ⟨b, -, hb⟩ := VG.Proof.MillerRabin.witness_exists hR hx5
  have sl : ∀ j < 28, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_lt hj) hZ
  unfold Impl.MillerRabin.PPC64LE.round
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Save.save_ok s hsin) fun s₁ hS => ?_
  have hout₁ := frame_outside (B := B) (Z := Z) hS.frame hdis
  have v₁ : ∀ {j}, j < 28 → val32 s₁.mem B (slot w j) (2 * w) = val32 s.mem B (slot w j) (2 * w) :=
    fun hj => hout₁.val32 (by have := sl _ hj; omega_arith) (by have := sl _ hj; omega_arith)
  have wd₁ : ∀ {d}, d + 8 ≤ Z → s₁.mem.readW (off B d) 64 = s.mem.readW (off B d) 64 :=
    fun hd => hout₁.word (by omega_arith) (by omega_arith)
  have h0 := slot_lt (w := w) (show 0 < 28 by decide)
  have h0' : slot w 0 = 256 := by simp [slot, Impl.Bignum.hdrBytes]
  refine WP.mono (setup_ok (hs.congr hS.keep.wr) (by rw [hS.keep.gpr .r3 (by decide), hBd])
    (by rw [wd₁ (by omega_arith), ← hwd]; simp [wOf, wordAt, Proof.Rsa.Mont.wWord])
    h4 h128 hZ (by
      rw [w32_eq_mod, w32_eq_mod]
      simp only [VG.Proof.Bignum.word]
      rw [wd₁ (by omega_arith), wd₁ (by omega_arith)]
      exact VG.Proof.Bignum.Minv32.minv_low hinv)) fun s₂ ⟨⟨hm2, m2⟩, k2⟩ => ?_
  have hc2 : Consts s₂.mem B w c := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [m2, show arr s₁.mem B w 0 = val32 s₁.mem B (slot w 0) (2 * w) from rfl, v₁ (by decide), ← numAt_eq,
        hcd]
    · rw [m2, show arr s₁.mem B w aOne = val32 s₁.mem B (slot w 9) (2 * w) from rfl, v₁ (by decide), ← numAt_eq]
      exact h9
    · rw [m2, show arr s₁.mem B w aMinus = val32 s₁.mem B (slot w 10) (2 * w) from rfl, v₁ (by decide),
        ← numAt_eq]
      exact h10
    · rw [m2, show arr s₁.mem B w aE = val32 s₁.mem B (slot w 27) (2 * w) from rfl, v₁ (by decide), ← numAt_eq]
      exact he
    · rw [m2]
      have := sl 27 (by decide)
      exact (wd₁ (d := slot w 27 + 8 * w) (by omega_arith)).trans hl
  have h52 : arr s₂.mem B w 5 = b % c * 2 ^ (64 * w) % c := by
    rw [m2, show arr s₁.mem B w 5 = val32 s₁.mem B (slot w 5) (2 * w) from rfl, v₁ (by decide), ← numAt_eq]
    exact hb
  refine WP.seq (WP.mono (core_ok hm2 hc2 h3 hodd h52) fun t ⟨_, t23, tmut, kt⟩ => ?_)
  rw [WP.block_append_iff]
  have hret : WP isa (.block [.li .r3 1, .logic .and .r3 .r3 .r23]) t fun t' =>
      (t'.gpr .r3 = BitVec.ofNat 64 1 &&& mask (Proof.MillerRabin.Round.round c b) ∧ t'.mem = t.mem) ∧ Keep [.r3] t t' := by
    refine WP.keep _ ?_ (by decide)
    prun [t23]
  refine WP.mono hret fun t₃ ⟨⟨r3v, m3⟩, k3⟩ => ?_
  have kall := ((hS.keep.trans k2).trans kt).trans k3
  -- the registers back
  have hsav : ∀ i < 18, t₃.mem.readW (off (s.gpr .r5) (8 * i)) 64 = s.gpr (Impl.MillerRabin.PPC64LE.saved i) :=
      fun i hi => by
    rw [← hS.saved i hi, m3]
    exact Mem.readW_congr fun k hk => (outs_scratch tmut (roundRanges_le hZ) hdis
      (Region.Contains.byte (Save.sav_contains _ hi) (by
        rw [Mem.sub_ofNat_toNat _ (by omega_arith)]; omega_arith))).trans (by rw [m2])
  have k23 := (k2.trans kt).trans k3
  refine WP.mono (Save.restore_ok t₃ ((k23.gpr .r21 (by decide)).trans hS.r21)
    (by rw [kall.wr]; exact hsin) hsav) fun u ⟨urs, uot, um, _, _, usp, ulr⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [usp, kall.sp], by rw [ulr, kall.lr]⟩, ?_, ?_⟩
  · by_cases hs' : ∃ i < 18, r = Impl.MillerRabin.PPC64LE.saved i
    · obtain ⟨i, hi, rfl⟩ := hs'
      exact urs i hi
    · have hn : ∀ i < 18, r ≠ Impl.MillerRabin.PPC64LE.saved i := fun i hi e => hs' ⟨i, hi, e⟩
      obtain ⟨h1, h2⟩ := pres_not_written r hr hn
      rw [uot r hn, k23.gpr r h1, hS.keep.gpr r (by simpa using h2)]
  · intro b' hb'
    rw [uot .r3 (by decide), r3v, ret_val]
    rw [hBd, hwd, hcd] at hb'
    rw [hBd, hwd, hcd, VG.Proof.MillerRabin.round_eq_of_mont (b' := b') (by omega_arith) hR (hb.symm.trans hb')]
  · intro i hi hh ha ht
    simp only [hBd, hwd] at ha ht ⊢
    have hi' : i < Z := by rw [← hZd]; omega_arith
    have hofs : Mont.ofs B (B + BitVec.ofNat 64 i) = i := by
      show (B + BitVec.ofNat 64 i - B).toNat = i
      rw [Mem.sub_ofNat_toNat _ (by omega_arith)]
    rw [um, m3, tmut _ fun r hr => ?_, m2, hout₁ _ (by rw [hofs]; omega_arith)]
    simp only [roundRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hofs]
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ha 2 (by simp)
    · exact ha 3 (by simp)
    · exact ha 5 (by simp)
    · exact ha 6 (by simp)
    · have e : slot w 11 + 16 * (8 * (w + 2)) = arrAt w (11 + 16) := by
        simp only [slot, arrAt, Impl.Bignum.hdrBytes, Proof.Rsa.Mont.hdrBytes]; omega_arith
      rw [e]; exact ht

end VG.Proof.MillerRabin.PPC64LE

end

end

/-!
# The Miller–Rabin round on PPC64LE: constant time

As `Proof/Bignum/PPC64LE/PubCT.lean`: two runs are related by `Two` at each
step. The taint analysis checks the saving of the registers and `setup` from
the working space's address and the scratch buffer's, and, after `setup`,
everything else from the registers it fixes, which depend only on the public
data (`FD`): array 0's base, `2 w`, the arrays' size, the working space and
the scratch buffer. Nothing branches on memory: the loops count `w`, the
16 windows of a word and the 16 entries of the table.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.MillerRabin.PPC64LE
open VG.Proof.Bignum (slot)
open VG.Proof.Rsa.Mont (wOf)
open VG.Proof.Bignum.PPC64LE (Two Pins two_post two_taint)

/-- The public data of a run. -/
structure FD where
  B : Addr
  n : BitVec 64
  S : Addr
  w : Nat

def fdOf (s : State) : FD := ⟨s.gpr .r3, s.gpr .r4, s.gpr .r5, wOf s.mem (s.gpr .r3)⟩

def C0 (d : FD) (s : State) : Prop := fnContract.pre s ∧ fdOf s = d

/-- After `setup`. -/
def C1 (d : FD) (s : State) : Prop :=
  s.gpr .r10 = off d.B (slot d.w 0) ∧ s.gpr .r11 = BitVec.ofNat 64 (2 * d.w) ∧
    s.gpr .r29 = BitVec.ofNat 64 (8 * (d.w + 2)) ∧ s.gpr .r31 = d.B ∧ s.gpr .r21 = d.S

theorem pins_C0 : Pins C0 [.r3, .r5] := by
  rintro d s₁ s₂ ⟨-, h₁⟩ ⟨-, h₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (congrArg FD.B h₁).trans (congrArg FD.B h₂).symm
  · exact (congrArg FD.S h₁).trans (congrArg FD.S h₂).symm

theorem pins_C1 : Pins C1 [.r10, .r11, .r21, .r29, .r31] := by
  rintro d s₁ s₂ ⟨a10, a11, a29, a31, a21⟩ ⟨b10, b11, b29, b31, b21⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [a10, b10]
  · rw [a11, b11]
  · rw [a21, b21]
  · rw [a29, b29]
  · rw [a31, b31]

theorem front_C1 {d : FD} {s : State} (h : C0 d s) : WP isa (.block (Impl.MillerRabin.PPC64LE.save ++ setup)) s (C1 d) := by
  obtain ⟨⟨-, hwr, hdis, hnw, hL, hp⟩, rfl⟩ := h
  have hsin : Save.savR (s.gpr .r5) ∈ s.wr := by rw [hwr]; simp
  dsimp only [Proof.MillerRabin.Round.Layout, Proof.MillerRabin.Round.compact] at hL
  obtain ⟨-, ⟨-, -, -, -⟩, h4, h128, hspace, -⟩ := hL
  dsimp only [Proof.MillerRabin.Round.Prepared, Proof.MillerRabin.Round.compact] at hp
  obtain ⟨-, -, hinv, -⟩ := hp
  simp only [wsR] at hdis
  simp only [fdOf]
  generalize hBd : s.gpr .r3 = B at hdis hnw hspace h4 h128 hinv
  generalize hZd : (s.gpr .r4).toNat * 8 = Z at hdis hnw
  generalize hwd : wOf s.mem B = w at hspace h4 h128 hinv
  have hZ : slot w 28 ≤ Z := by
    rw [← hZd]; change slot w 28 ≤ 8 * (s.gpr .r4).toNat at hspace; omega_using [hspace]
  have hs : Scr s B Z := Scr.of_mem (by rw [hwr, ← hBd, ← hZd]; simp) hnw
  have h0 := slot_lt (w := w) (show 0 < 28 by decide)
  have h0' : slot w 0 = 256 := by simp [slot, Impl.Bignum.hdrBytes]
  rw [WP.block_append_iff]
  refine WP.mono (Save.save_ok s hsin) fun s₁ hS => ?_
  have hout₁ := frame_outside (B := B) (Z := Z) hS.frame hdis
  have wd₁ : ∀ {d}, d + 8 ≤ Z → s₁.mem.readW (off B d) 64 = s.mem.readW (off B d) 64 :=
    fun hd => hout₁.word (by omega_using [hd]) (by omega_using [hnw, hd])
  refine WP.mono (setup_ok (hs.congr hS.keep.wr) (by rw [hS.keep.gpr .r3 (by decide), hBd])
    (by rw [wd₁ (by omega_using [hZ, h0, h0']), ← hwd]; simp [wOf, VG.Proof.Rsa.Mont.wordAt, Proof.Rsa.Mont.wWord])
    h4 h128 hZ (by
      rw [w32_eq_mod, w32_eq_mod]
      simp only [VG.Proof.Bignum.word]
      rw [wd₁ (by omega_using [hZ, h0]), wd₁ (by omega_using [hZ, h0, h0'])]
      exact VG.Proof.Bignum.Minv32.minv_low hinv)) fun s₂ ⟨⟨hm2, _⟩, k2⟩ => ?_
  exact ⟨hm2.h10, hm2.h11, hm2.h29, hm2.h31, (k2.gpr .r21 (by decide)).trans hS.r21⟩

theorem fn_rel : RelCT isa (Two C0) Impl.MillerRabin.PPC64LE.round fun _ _ => True := by
  unfold Impl.MillerRabin.PPC64LE.round
  exact RelCT.seq (two_post (two_taint _ pins_C0 (by taint_decide)) fun _ _ h => front_C1 h)
    (two_taintR _ pins_C1 (by taint_decide_rel))

theorem fn_ct : ConstantTime isa fnContract.pre fnContract.pub Impl.MillerRabin.PPC64LE.round :=
  RelCT.constantTime (fn_rel.mono (fun s t ⟨hs, ht, hsp, h3, h4, h5, hw⟩ =>
    ⟨fdOf s, ⟨hs, rfl⟩, ⟨ht, by simp only [fdOf]; rw [h3, h4, h5, ← h3, hw, h3]⟩, hsp⟩) fun _ _ h => h)

end VG.Proof.MillerRabin.PPC64LE

end

end

/-!
# The Miller–Rabin round on PPC64LE: the shared contract

As `Proof/MillerRabin/PPC64LE/Verified.lean`: `round` is proven against
`fnContract`, with the scratch buffer where it saves the nonvolatile
registers as a third argument; that is `roundContract` with the buffer
appended (`scratch_verified`), and `withStackScratch` allocates the buffer
in a frame of its own (`round_verified`), as the contract's precondition,
postcondition and leak read memory only within the working space when the
precondition holds.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.PPC64LE

open VG VG.PPC64LE
open VG.Proof.Rsa.Mont (numAt wOf wordAt arrAt)
open VG.Proof.MillerRabin.Round (compact Layout Prepared Keeps)

/-- `roundContract`'s precondition. -/
def rPre : Curry (Proof.MillerRabin.Round.roundSig.words abi.ptrBits) (Mem → Prop) := fun ws wsLen m =>
  Layout compact m ws wsLen.toNat ∧ Prepared compact m ws

/-- `roundContract`'s postcondition. -/
def rPost : Proof.MillerRabin.Round.roundSig.Post abi.ptrBits := fun ws wsLen m m' r =>
  let w := wOf m ws
  let c := numAt m ws w 0
  (∀ b, numAt m ws w 5 = b % c * 2 ^ (64 * w) % c → r.toNat = if Proof.MillerRabin.Round.round c b then 1 else 0) ∧
    Keeps compact ws wsLen.toNat w m m'

/-- `roundContract`'s leak. -/
def rLeak : Curry (Proof.MillerRabin.Round.roundSig.words abi.ptrBits) (Mem → List Nat) := fun ws _ m => [wOf m ws]

/-- `roundContract` with the 144-byte scratch buffer as a third argument. -/
abbrev scratchContract : Contract isa :=
  Sig.scratchContract abi Proof.MillerRabin.Round.roundSig "scratch" .u64 18 rPre rPost false 0 (some rLeak)

/-! ## Satisfiability -/

/-- A four-limb prepared workspace for the candidate 3 at `0x1000`, as on
AArch64. -/
def satWord (i : Nat) : BitVec 64 :=
  if i = 6 then 4 else if i = 7 then 0x5555555555555555 else
    if 8 ≤ i ∧ i < 16 then BitVec.ofNat 64 (0x1100 + 48 * (i - 8)) else
    if i = 28 then 48 else if i = 32 then 3 else if i = 62 then 2 else
    if i = 86 then 1 else if i = 92 then 2 else if i = 194 then 1 else if i = 198 then 2 else 0

def satMem : Mem := fun x =>
  let i := (x - 0x1000).toNat
  if i < 2048 then (satWord (i / 8)).extractLsb' (8 * (i % 8)) 8 else 0

theorem sat_layout : Layout compact satMem 0x1000 256 := by
  simp only [Layout, compact, Proof.Rsa.Mont.Layout, Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff,
    forall_const, true_and]
  decide +kernel

theorem sat_prepared : Prepared compact satMem 0x1000 := by
  have hw : wOf satMem 0x1000 = 4 := by decide +kernel
  have hc : numAt satMem 0x1000 4 0 = 3 := by
    rw [VG.Proof.Bignum.PPC64LE.numAt_eq]; decide +kernel
  have h5 : numAt satMem 0x1000 4 5 = 2 := by
    rw [VG.Proof.Bignum.PPC64LE.numAt_eq]; decide +kernel
  have h9 : numAt satMem 0x1000 4 9 = 1 := by
    rw [VG.Proof.Bignum.PPC64LE.numAt_eq]; decide +kernel
  have h10 : numAt satMem 0x1000 4 10 = 2 := by
    rw [VG.Proof.Bignum.PPC64LE.numAt_eq]; decide +kernel
  have h27 : numAt satMem 0x1000 4 27 = 1 := by
    rw [VG.Proof.Bignum.PPC64LE.numAt_eq]; decide +kernel
  simp only [Prepared, compact, hw, hc, h5, h9, h10, h27]
  decide +kernel

/-- A state meeting `scratchContract`: the scratch buffer at `0x2000`. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 256 | .r5 => 0x2000 | _ => 0
  lr := 0
  sp := 0x8000
  mem := satMem
  rd := []
  wr := [⟨0x1000, 2048⟩, ⟨0x2000, 144⟩]

/-- `satState` without the scratch buffer: a state meeting `roundContract`. -/
def satState₀ : State := { satState with wr := [⟨0x1000, 2048⟩] }

theorem fn_implies : fnContract.Implies scratchContract where
  pre := by
    intro s h
    sig_pre [scratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Proof.MillerRabin.Round.roundSig, rPre, rPost, rLeak, fnContract, abi, argRegs] at h
    sig_split h
    sig_reduce [scratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Proof.MillerRabin.Round.roundSig, rPre, rPost, rLeak, fnContract, abi, argRegs]
    simp only [Prepared]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> with_reducible assumption
  post := by
    sig_implies_post [scratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Proof.MillerRabin.Round.roundSig, rPre, rPost, rLeak, fnContract, abi, argRegs]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [scratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Proof.MillerRabin.Round.roundSig, rPre, rPost, rLeak, fnContract, abi, argRegs] at h
    obtain ⟨hsp, hw, h3, h4, h5⟩ := h
    exact ⟨hsp, h3, h4, h5, List.singleton_inj.mp hw⟩
  sat := by
    refine ⟨satState, ?_⟩
    sig_pre [scratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Proof.MillerRabin.Round.roundSig, rPre, rPost, rLeak, abi, argRegs]
    sig_and_intros
    · rfl
    · exact Region.disjoint_of_sep (by decide)
    · decide
    · decide
    · show Layout compact satMem 4096 (BitVec.toNat (256 : BitVec 64)) ∧ Prepared compact satMem 4096
      exact ⟨sat_layout, sat_prepared⟩

theorem scratch_verified : Verified target Impl.MillerRabin.PPC64LE.round scratchContract :=
  Verified.of_correct fn_correct fn_ct fn_implies

/-! ## Reading memory within the working space -/

theorem arrAt_le {w j k : Nat} (h : j ≤ k) : arrAt w j ≤ arrAt w k := by
  unfold arrAt; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

/-- What the contract reads of `m₂` agrees with `m₁`, whose layout bounds it. -/
structure Same (ws : Addr) (m₁ m₂ : Mem) : Prop where
  w : wOf m₂ ws = wOf m₁ ws
  rd : ∀ d, d + 8 ≤ arrAt (wOf m₁ ws) 28 → m₂.readW (ws + BitVec.ofNat 64 d) 64 = m₁.readW (ws + BitVec.ofNat 64 d) 64
  num : ∀ j < 28, numAt m₂ ws (wOf m₁ ws) j = numAt m₁ ws (wOf m₁ ws) j

theorem same_of {m₁ m₂ : Mem} {ws : Addr} {n : Nat}
    (h : ∀ a, (⟨ws, n * 8⟩ : Region).Contains a 1 → m₂ a = m₁ a) (hl : Layout compact m₁ ws n) :
    Same ws m₁ m₂ := by
  dsimp only [Layout, compact] at hl
  obtain ⟨-, -, -, h128, hsp, -⟩ := hl
  have hsp' : arrAt (wOf m₁ ws) 28 ≤ n * 8 := by
    change arrAt (wOf m₁ ws) 28 ≤ 8 * n at hsp; omega_arith
  have hz : arrAt (wOf m₁ ws) 28 < 2 ^ 64 := by unfold arrAt Proof.Rsa.Mont.hdrBytes; omega_arith
  have rd : ∀ d, d + 8 ≤ arrAt (wOf m₁ ws) 28 →
      m₂.readW (ws + BitVec.ofNat 64 d) 64 = m₁.readW (ws + BitVec.ofNat 64 d) 64 :=
    fun d hd => VG.Proof.Bignum.PPC64LE.agree_readW h (by omega_arith) (by omega_arith)
  have h48 : 8 * 6 + 8 ≤ arrAt (wOf m₁ ws) 28 := by unfold arrAt Proof.Rsa.Mont.hdrBytes; omega_arith
  refine ⟨?_, rd, fun j hj => ?_⟩
  · simp only [wOf, wordAt, Proof.Rsa.Mont.wWord]
    rw [rd _ h48]
  · have hj' := arrAt_le (w := wOf m₁ ws) (show j + 1 ≤ 28 by omega_arith)
    have e : arrAt (wOf m₁ ws) (j + 1) = arrAt (wOf m₁ ws) j + 8 * (wOf m₁ ws + 2) := by
      unfold arrAt; rw [Nat.add_mul, Nat.one_mul]; omega_arith
    simp only [numAt]
    rw [VG.Proof.Bignum.PPC64LE.agree_read h (by omega_arith) (by omega_arith)]

theorem layout_congr {m₁ m₂ : Mem} {ws : Addr} {n : Nat} (hS : Same ws m₁ m₂) (hl : Layout compact m₁ ws n) :
    Layout compact m₂ ws n := by
  have hl' := hl
  dsimp only [Layout, compact, Proof.Rsa.Mont.Layout] at hl' ⊢
  obtain ⟨h0, ⟨h2, h31, h8, harr⟩, h4, h128, hsp, hst⟩ := hl'
  rw [hS.w]
  have hz : 8 * 28 + 8 ≤ arrAt (wOf m₁ ws) 28 := by unfold arrAt Proof.Rsa.Mont.hdrBytes; omega_arith
  refine ⟨h0, ⟨h2, h31, h8, fun j hj => ?_⟩, h4, h128, hsp, ?_⟩
  · simp only [wordAt, Proof.Rsa.Mont.arrWord] at harr ⊢
    rw [hS.rd _ (by omega_arith)]; exact harr j hj
  · simp only [wordAt] at hst ⊢
    rw [hS.rd _ (by omega_arith)]; exact hst

theorem prepared_congr {m₁ m₂ : Mem} {ws : Addr} {n : Nat} (hS : Same ws m₁ m₂) (hl : Layout compact m₁ ws n)
    (hp : Prepared compact m₁ ws) : Prepared compact m₂ ws := by
  dsimp only [Layout, compact] at hl
  obtain ⟨-, -, -, h128, -, -⟩ := hl
  dsimp only [Prepared, compact] at hp ⊢
  rw [hS.w, hS.num 0 (by decide), hS.num 5 (by decide), hS.num 9 (by decide), hS.num 10 (by decide),
    hS.num 27 (by decide)]
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hp
  have hz0 : arrAt (wOf m₁ ws) 0 + 8 ≤ arrAt (wOf m₁ ws) 28 := by unfold arrAt Proof.Rsa.Mont.hdrBytes; omega_arith
  have hz7 : 8 * 7 + 8 ≤ arrAt (wOf m₁ ws) 28 := by unfold arrAt Proof.Rsa.Mont.hdrBytes; omega_arith
  have hz27 : arrAt (wOf m₁ ws) 27 + 8 * wOf m₁ ws + 8 ≤ arrAt (wOf m₁ ws) 28 := by
    unfold arrAt Proof.Rsa.Mont.hdrBytes; omega_arith
  refine ⟨a1, a2, ?_, a4, a5, a6, a7, ?_⟩
  · simp only [wordAt, Proof.Rsa.Mont.minvWord] at a3 ⊢
    rw [hS.rd _ hz0, hS.rd _ hz7]; exact a3
  · rw [hS.rd _ hz27]; exact a8

/-- The contract's arguments, as `Curry.apply` passes them. -/
theorem words_eq : Proof.MillerRabin.Round.roundSig.words abi.ptrBits = [.addr, .int 64] := rfl

theorem pre_local : ∀ vs m₁ m₂, vs.length = (Proof.MillerRabin.Round.roundSig.words abi.ptrBits).length →
    (∀ b ∈ Sig.bufs Proof.MillerRabin.Round.roundSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Proof.MillerRabin.Round.roundSig.words abi.ptrBits) rPre vs m₁ →
      Curry.apply (Proof.MillerRabin.Round.roundSig.words abi.ptrBits) rPre vs m₂ := by
  intro vs m₁ m₂ hlen hb h
  rw [words_eq] at hlen
  match vs, hlen with
  | [ws, l], _ =>
  simp only [Proof.MillerRabin.Round.roundSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
    Elem.size] at hb
  change Curry.apply [ArgWord.addr, .int 64] rPre _ m₁ at h
  change Curry.apply [ArgWord.addr, .int 64] rPre _ m₂
  dsimp only [Curry.apply, rPre, ArgWord.ofRaw] at h ⊢
  simp only [BitVec.setWidth_eq] at h ⊢
  obtain ⟨hl, hp⟩ := h
  have hS := same_of (m₁ := m₁) (m₂ := m₂) (n := l.toNat) (fun x hx => (hb x hx).symm) hl
  exact ⟨layout_congr hS hl, prepared_congr hS hl hp⟩

theorem post_local : ∀ vs m₁ m₂ m' r, vs.length = (Proof.MillerRabin.Round.roundSig.words abi.ptrBits).length →
    Curry.apply (Proof.MillerRabin.Round.roundSig.words abi.ptrBits) rPre vs m₂ →
    (∀ b ∈ Sig.bufs Proof.MillerRabin.Round.roundSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Proof.MillerRabin.Round.roundSig.words abi.ptrBits) rPost vs m₁ m' r →
      Curry.apply (Proof.MillerRabin.Round.roundSig.words abi.ptrBits) rPost vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hp hb h
  rw [words_eq] at hlen
  match vs, hlen with
  | [ws, l], _ =>
  simp only [Proof.MillerRabin.Round.roundSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
    Elem.size] at hb
  change Curry.apply [ArgWord.addr, .int 64] rPre _ m₂ at hp
  change Curry.apply [ArgWord.addr, .int 64] rPost _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, .int 64] rPost _ m₂ m' r
  dsimp only [Curry.apply, rPre, rPost, ArgWord.ofRaw] at hp h ⊢
  simp only [BitVec.setWidth_eq] at hp h ⊢
  obtain ⟨hl, -⟩ := hp
  have hS := same_of (m₁ := m₂) (m₂ := m₁) (n := l.toNat) hb hl
  obtain ⟨hr, hk⟩ := h
  simp only [hS.w, hS.num 0 (by decide), hS.num 5 (by decide)] at hr hk
  refine ⟨hr, fun i hi hh ha ht => ?_⟩
  rw [hk i hi hh ha ht]
  refine hb _ ?_
  show (ws + BitVec.ofNat 64 i - ws).toNat + 1 ≤ l.toNat * 8
  rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  have := Nat.mod_le i (2 ^ 64)
  have hi' : i < 8 * (l : BitVec 64).toNat := hi
  omega_arith


/-- `rPost` reads the memory on return only within the working space. -/
theorem post_out : ∀ vs m m₁ m₂ r, vs.length = (Proof.MillerRabin.Round.roundSig.words abi.ptrBits).length →
    (∀ b ∈ Sig.bufs Proof.MillerRabin.Round.roundSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Proof.MillerRabin.Round.roundSig.words abi.ptrBits) rPost vs m m₁ r →
      Curry.apply (Proof.MillerRabin.Round.roundSig.words abi.ptrBits) rPost vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  rw [words_eq] at hlen
  match vs, hlen with
  | [ws, l], _ =>
  simp only [Proof.MillerRabin.Round.roundSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
    Elem.size] at hb
  change Curry.apply [ArgWord.addr, .int 64] rPost _ m m₁ r at h
  change Curry.apply [ArgWord.addr, .int 64] rPost _ m m₂ r
  dsimp only [Curry.apply, rPost, ArgWord.ofRaw] at h ⊢
  simp only [BitVec.setWidth_eq] at h ⊢
  obtain ⟨hr, hk⟩ := h
  refine ⟨hr, fun i hi hh ha ht => ?_⟩
  rw [← hk i hi hh ha ht]
  refine (hb _ ?_).symm
  show (ws + BitVec.ofNat 64 i - ws).toNat + 1 ≤ l.toNat * 8
  rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  have := Nat.mod_le i (2 ^ 64)
  have hi' : i < 8 * (l : BitVec 64).toNat := hi
  omega_arith

theorem leak_local : ∀ f, some rLeak = some f → ∀ vs m₁ m₂,
    vs.length = (Proof.MillerRabin.Round.roundSig.words abi.ptrBits).length →
    Curry.apply (Proof.MillerRabin.Round.roundSig.words abi.ptrBits) rPre vs m₂ →
    (∀ b ∈ Sig.bufs Proof.MillerRabin.Round.roundSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply _ f vs m₁ = Curry.apply _ f vs m₂ := by
  intro f hf vs m₁ m₂ hlen hp hb
  cases hf
  rw [words_eq] at hlen
  match vs, hlen with
  | [ws, l], _ =>
  simp only [Proof.MillerRabin.Round.roundSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
    Elem.size] at hb
  change Curry.apply [ArgWord.addr, .int 64] rPre _ m₂ at hp
  change Curry.apply [ArgWord.addr, .int 64] rLeak _ m₁ = Curry.apply [ArgWord.addr, .int 64] rLeak _ m₂
  dsimp only [Curry.apply, rPre, rLeak, ArgWord.ofRaw] at hp ⊢
  simp only [BitVec.setWidth_eq] at hp
  rw [(same_of (m₁ := m₂) (m₂ := m₁) (n := l.toNat) hb hp.1).w]

/-- `vg_miller_rabin_round` with its scratch buffer in a frame of 176 bytes. -/
theorem round_verified : Verified target
    (Impl.StackScratch.PPC64LE.withStackScratch 176 .r5 Impl.MillerRabin.PPC64LE.round)
    (Proof.MillerRabin.Round.roundContract abi compact 176) :=
  Verified.stackScratchL (sig := Proof.MillerRabin.Round.roundSig) (nm := "scratch") (e := .u64) (n := 18)
    (post := rPost) (wa := false) (stack := 0) (bytes := 176) scratch_verified (by decide)
    (by decide) pre_local post_local (fun vs m m₁ m₂ r hl _ => post_out vs m m₁ m₂ r hl) leak_local
    ⟨satState₀, by
      sig_pre [Proof.MillerRabin.Round.roundSig, rPre, rPost, rLeak, abi, argRegs]
      sig_and_intros
      · decide
      · decide
      · exact Region.disjoint_of_sep (by decide)
      · decide
      · exact sat_layout
      · exact sat_prepared⟩

end VG.Proof.MillerRabin.PPC64LE
