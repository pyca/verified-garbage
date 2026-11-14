module

public import VerifiedGarbage.Proof.Rsa.X86.Rd.TimeW2Q
public import VerifiedGarbage.Proof.Rsa.X86.Rd.DivBW
import VerifiedGarbage.Proof.Rsa.X86.Rd.Loops
import VerifiedGarbage.Proof.Rsa.X86.Rd.Move
import VerifiedGarbage.Proof.Rsa.X86.Rd.TwosW
import VerifiedGarbage.Proof.Rsa.X86.Rd.DivQ
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Impl.Rsa.X86.RecoverDetRt
meta import VerifiedGarbage.Proof.Rsa.X86.Rd.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Rsa.X86.Rd.TimeW2Q

/-! # `divB`'s timing on i686

`RecoverDetRt.divB` (`Rd/DivBW.lean` has its run): the start and the end are leaves, the stages of
`D`'s leading zeros (`stageDWH`, `stageDBH`) are leaves between the stage loops' header words, and
`wordDivQ` is related on its own.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot aM sB
open VG.Impl.Rsa.X86.RecoverRt (nar wid)
open VG.Impl.Rsa.X86.RecoverDetRt hiding aN aP aQ
open VG.Impl.Rsa.X86.Recover (aN)
open VG.Proof.Rsa.X86.Keys
open VG.Impl.Mont.X86 (sc at_)
open VG.Proof.Mont.X86.Rt (PtrAt readSrc_ptr ptr_add)
open VG.Proof.Rsa.X86.WordRt (MLen wq)
open VG.Proof.Rsa.X86.InvBatchRt.Time (view)
open VG.Impl.Rsa.X86.KeyRt (arrPtr copy sel chain zeroWide eqSFast)

/-! ## `divB`'s stages -/

/-- A state of `divB`: one, zero and `n` (narrow), the wide arrays `liveW` (with `n` in `wN`), and
the header words `ls`, the public ones as `H` says. -/
def DK (g : Geo) (n a : Nat) (liveW ls : List Nat) (H : (Nat → Nat) → Prop) (s : State) : Prop :=
  GA g a ∧ ∃ s0 A AW V, KS g s0 A [aOne1, aZero, aN] AW liveW V ls s ∧ H V ∧ A aOne1 = 1 ∧ A aZero = 0 ∧
    A aN = n ∧ AW wN = n

/-- `DvS`, its values forgotten, its loop size `vd` in `d`. -/
abbrev DX (g : Geo) (n a d vd : Nat) : State → Prop := DK g n a [wDD, wNN, wN] [d, sLt, sOkDE] (· d = vd)

/-- `DvS` at `sOkDE`, its values forgotten. -/
abbrev D0 (g : Geo) (n a : Nat) : State → Prop := DK g n a [wDD, wNN, wN] [sOkDE, sLt, sOkDE] fun _ => True

section
variable {g : Geo} {s0 s : State} {n a : Nat} {liveW ls : List Nat} {H : (Nat → Nat) → Prop}

theorem DK.onView (h : DK g n a liveW ls H s) : DK g.vw n a liveW ls H (view s g.B g.Z) :=
  let ⟨ga, _, _, _, _, k, r⟩ := h
  ⟨ga, _, _, _, _, k.onView, r⟩

theorem DK.p0 (pg : PubG g) (h : DK g n a liveW ls H s) : P0 g s :=
  let ⟨_, _, _, _, _, k, _⟩ := h
  k.pre0 pg

theorem DK.slot {d v : Nat} (h : DK g n a liveW ls H s) (hd : d ∈ ls) (hv : ∀ V, H V → V d = v) :
    w32 s.mem g.B d = v :=
  let ⟨_, _, _, _, _, k, hH, _⟩ := h
  (k.sl d hd).trans (hv _ hH)

theorem DX.dvs {d vd : Nat} (h : DX g n a d vd s) : GA g a ∧ ∃ s0 ok lt v, DvS g s0 ok lt n v d vd s :=
  let ⟨ga, s0, A, AW, V, k, hd, h1, hz, hn, hnw⟩ := h
  ⟨ga, s0, V sOkDE, V sLt, (AW wDD, AW wNN), A, AW, V, k, hd, rfl, rfl, h1, hz, hn, rfl, rfl, hnw⟩

theorem D0.dvs (h : D0 g n a s) : GA g a ∧ ∃ s0 ok lt v, DvS g s0 ok lt n v sOkDE ok s :=
  let ⟨ga, s0, A, AW, V, k, _, h1, hz, hn, hnw⟩ := h
  ⟨ga, s0, V sOkDE, V sLt, (AW wDD, AW wNN), A, AW, V, k, rfl, rfl, rfl, h1, hz, hn, rfl, rfl, hnw⟩

theorem DvS.dx {ok lt d vd : Nat} {v : Nat × Nat} (ga : GA g a) (h : DvS g s0 ok lt n v d vd s) :
    DX g n a d vd s :=
  let ⟨A, AW, V, k, hd, _, _, h1, hz, hn, _, _, hnw⟩ := h
  ⟨ga, s0, A, AW, V, k, hd, h1, hz, hn, hnw⟩

theorem DvS.d0 {ok lt : Nat} {v : Nat × Nat} (ga : GA g a) (h : DvS g s0 ok lt n v sOkDE ok s) : D0 g n a s :=
  let ⟨A, AW, V, k, _, _, _, h1, hz, hn, _, _, hnw⟩ := h
  ⟨ga, s0, A, AW, V, k, trivial, h1, hz, hn, hnw⟩

end

/-- A leaf from a state of `divB`. -/
theorem leafDK {g : Geo} (pg : PubG g) {n a : Nat} {liveW ls : List Nat} {H : (Nat → Nat) → Prop}
    {Q : Geo → State → Prop} {c : Prog isa} {ds : List Nat} (vals : Nat → Nat)
    (hds : ∀ d ∈ ds, d ∈ ls ∧ d + 4 ≤ 160) (hv : ∀ V, H V → ∀ d ∈ ds, V d = vals d)
    (hf : ∀ g' s, DK g' n a liveW ls H s → WP isa c s (Q g')) (h : OkK ds c) :
    RelCT isa (Both (DK g n a liveW ls H)) c (Both (Q g)) :=
  leafP (P := fun g' => DK g' n a liveW ls H) vals (fun d hd => (hds d hd).2) (fun _ h => h.p0 pg)
    (fun _ h => h.onView) (fun _ h d hd => h.slot (hds d hd).1 fun V hV => hv V hV d hd) hf h

/-! ### The word stages -/

/-- `stageDWH`'s first part: the OR of `D`'s top words, the flag, `D` shifted up by them. -/
abbrev dw1 : List (Prog isa) :=
  [.seq (.block (arrPtr wid .esi wDD .edx ++ VG.Impl.Rsa.X86.WordModRt.width4 nl .edx ++
      [.alu .add .esi (.reg .edx), .mov .edx (.mem (sc sC4)), .alu .sub .esi (.reg .edx), .mov .ecx (.imm 0)]))
    (.loop (.block [.alu .or .ecx (.mem (at_ .esi 0)), .alu .add .esi (.imm 4), .alu .sub .edx (.imm 4)]) .ne),
  .block flagZero, moveH wid wDD wT false true, sel wid wDD wDD wT sStg]

/-- `stageDWH`'s second part: `N` shifted up. -/
abbrev dw2 : List (Prog isa) := [moveH wid wNN wT false true, sel wid wNN wNN wT sStg]

/-- Between `stageDWH`'s parts. -/
abbrev DWM (g : Geo) (n a c : Nat) : State → Prop :=
  DK g n a [wDD, wT, wDD, wNN, wN] [sStg, sC4, sLt, sOkDE] fun V => V sStg ≤ 1 ∧ V sC4 = 4 * c

section
variable {g : Geo} {s : State} {n a c : Nat}

theorem dw1_ok (h : DX g n a sC4 (4 * c) s) (ha1 : a ≤ 1024) (hc0 : 0 < c) (hc : c < wq a) :
    WP isa (seqs dw1) s (DWM g n a c) := by
  obtain ⟨⟨ha, hw⟩, s0, A, AW, V, h, hd, h1, hz, hn, hNW⟩ := h
  have cW : c < g.W := by simp only [Geo.W, VG.Impl.Rsa.X86.Recover.wide]; simp only [Geo.w] at hw; omega_using [hc, hw]
  simp only [seqs]
  refine WP.seq (WP.mono (h.orTopD (h.mlen ha ha1) (by simp) (by simp) hd hc0 (Nat.le_of_lt hc) hw)
    fun t₁ ⟨h₁, _⟩ => ?_)
  refine WP.seq (WP.mono h₁.flagZero fun t₂ ⟨h₂, _⟩ => ?_)
  have hV₂ : upd V sStg (if t₁.gpr .ecx = 0 then 1 else 0) sC4 = 4 * c := by
    rw [upd_ne _ _ (by decide)]; exact hd
  refine WP.seq (WP.mono (h₂.moveUp_W (o := wT) (a := wDD) (c := c) (by decide) (by simp) (by decide) cW
    (by simp) hV₂ (by decide)) fun t₃ ⟨h₃, _, _⟩ => ?_)
  refine WP.mono (h₃.sel_W (o := wDD) (a := wDD) (b := wT) (sl := sStg) (by decide) (by simp)
    (by simp) (by simp) (by rw [upd_self]; split <;> decide) (.inr (by decide)) (by decide)) fun t₄ ⟨h₄, _⟩ => ?_
  refine ⟨⟨ha, hw⟩, s0, A, _, _, h₄, ⟨by rw [upd_self]; split <;> decide, hV₂⟩, h1, hz, hn, ?_⟩
  simp only [upd_ne _ _ (show wN ≠ wDD by decide), upd_ne _ _ (show wN ≠ wT by decide), hNW]

theorem dw2_ok (h : DWM g n a c s) (hc : c < wq a) : WP isa (seqs dw2) s (DX g n a sC4 (4 * c)) := by
  obtain ⟨⟨ha, hw⟩, s0, A, AW, V, h, ⟨hb, hd⟩, h1, hz, hn, hNW⟩ := h
  have cW : c < g.W := by simp only [Geo.W, VG.Impl.Rsa.X86.Recover.wide]; simp only [Geo.w] at hw; omega_using [hc, hw]
  simp only [seqs]
  refine WP.seq (WP.mono (h.moveUp_W (o := wT) (a := wNN) (c := c) (by decide) (by simp) (by decide) cW
    (by simp) hd (by decide)) fun t₅ ⟨h₅, _, _⟩ => ?_)
  refine WP.mono (h₅.sel_W (o := wNN) (a := wNN) (b := wT) (sl := sStg) (by decide) (by simp)
    (by simp) (by simp) hb (.inr (by decide)) (by decide)) fun t ⟨h₆, _⟩ => ?_
  refine ⟨⟨ha, hw⟩, s0, A, _, _, h₆.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨by simp at hj ⊢; omega_using [hj], rfl⟩)
    (fun d hd => ⟨by simp at hd ⊢; omega_using [hd], rfl⟩), hd, h1, hz, hn, ?_⟩
  simp only [upd_ne _ _ (show wN ≠ wNN by decide), upd_ne _ _ (show wN ≠ wT by decide), hNW]

end

theorem c_dw1 : OkK [sC4] (seqs dw1) := ⟨_, by taint_decide⟩
theorem c_dw2 : OkK [sC4] (seqs dw2) := ⟨_, by taint_decide⟩

/-- A word stage, related. -/
theorem stageDW_rel {g : Geo} (pg : PubG g) {n a c : Nat} (ha1 : a ≤ 1024) (hc0 : 0 < c) (hc : c < wq a) :
    RelCT isa (Both (DX g n a sC4 (4 * c))) stageDWH (Both (DX g n a sC4 (4 * c))) := by
  have e : stageDWH = seqs (dw1 ++ dw2) := rfl
  rw [e]
  exact relSeqs (leafDK pg (fun _ => 4 * c) (by decide) (fun V hV d hd => by simp at hd; subst hd; exact hV)
      (fun g' s h => dw1_ok h ha1 hc0 hc) c_dw1)
    (leafDK pg (fun _ => 4 * c) (by decide) (fun V hV d hd => by simp at hd; subst hd; exact hV.2)
      (fun g' s h => dw2_ok h hc) c_dw2)

theorem c_wInit : OkK [] (.block [.mov .eax (.imm (BitVec.ofNat 32 (4 * 2 ^ 7))), .store (sc sC4) .eax]) :=
  ⟨_, by taint_decide⟩
theorem c_wLim : OkK [sC4] (.block (VG.Impl.Rsa.X86.WordModRt.width4 nl .eax ++
    ([.mov .ecx (.mem (sc sC4)), .alu .cmp .ecx (.reg .eax)] : List Instr))) := ⟨_, by taint_decide⟩
theorem c_wHalf : OkK [sC4] (.block halfC4) := ⟨_, by taint_decide⟩

/-- The word stages of `D`'s leading zeros, related. -/
theorem wordStagesD_rel {g : Geo} (pg : PubG g) {n a : Nat} (ha1 : a ≤ 1024) :
    RelCT isa (Both (D0 g n a))
      (wordStagesL 128 (VG.Impl.Rsa.X86.WordModRt.width4 nl .eax) stageDWH) (Both (D0 g n a)) := by
  have w4 : 4 * wq a < 2 ^ 32 := by simp only [wq]; omega_using [ha1]
  have e : wordStagesL 128 (VG.Impl.Rsa.X86.WordModRt.width4 nl .eax) stageDWH =
    wordStagesL (2 ^ 7) (VG.Impl.Rsa.X86.WordModRt.width4 nl .eax) stageDWH := rfl
  rw [e]
  refine relWordStagesL (lim := 4 * wq a) (S := fun g' => D0 g' n a)
    (Fin := fun g' => D0 g' n a)
    (fun g' j => DX g' n a sC4 (4 * 2 ^ j)) (fun g' j => DX g' n a sC4 (4 * 2 ^ j)) (by decide)
    (fun _ h => h.p0 pg) (fun _ _ h => h.p0 pg) (fun _ _ h => h.p0 pg)
    (fun _ h => h.onView) (fun _ _ h => h.onView) (fun _ _ h => h.onView)
    (fun g' s h => let ⟨_, _, _, _, _, P⟩ := h.dvs; P.ws)
    (fun g' s t h k e r => ?_) (fun g' j t _ h => ?_) (fun g' j t _ h is Q k => ?_)
    (fun g' j t u _ h r m => ?_) (fun _ _ _ _ h _ => h) (fun g' j t _ h => ?_)
    (fun g' j t u hj h k e r => ?_) (fun j _ hl => stageDW_rel pg ha1 (Nat.two_pow_pos j) (by omega_using [hl]))
    c_wInit c_wLim c_wHalf
  · obtain ⟨ga, _, _, _, _, P⟩ := h.dvs
    exact DvS.dx ga (P.reslot k (by decide) (by decide) (by decide) e (r.mono (by decide)))
  · obtain ⟨_, _, _, _, _, P⟩ := h.dvs
    exact ⟨P.ws, P.slotEq⟩
  · obtain ⟨⟨ha, _⟩, _, _, _, _, P⟩ := h.dvs
    obtain ⟨A, AW, V, hK⟩ := P.ks
    exact VG.Proof.Rsa.X86.WordRt.width4_ok (hK.mlen ha ha1) (r := .eax)
      fun u' K m e => k u' (K.mono (by decide)) m (by rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt w4])
  · obtain ⟨ga, _, _, _, _, P⟩ := h.dvs
    exact DvS.dx ga (P.of_rest r m)
  · obtain ⟨_, _, _, _, _, P⟩ := h.dvs
    exact ⟨P.ws, P.slotEq⟩
  · obtain ⟨ga, _, _, _, _, P⟩ := h.dvs
    refine ⟨fun hj0 => ?_, fun hj0 => ?_⟩
    · have p := pow_pred hj0
      exact DvS.dx ga (P.reslot k (by decide) (by decide) (by decide) (by rw [e]; omega) r)
    · subst hj0
      exact DvS.d0 ga (P.reslot k (by decide) (by decide) (by decide) e r).forget

/-! ### The bit stages -/

/-- `stageDBH`'s first part: `D`'s top `b` bits tested, the flag. -/
abbrev db1 : List (Prog isa) :=
  [.block (VG.Impl.Rsa.X86.WordModRt.topPtr wid nl .esi wDD 1 .edx ++ [.mov .eax (.mem (at_ .esi 0))]),
    topTest, .block flagZero]

/-- A bit stage of `b` bits, its flag set. -/
abbrev DBM (g : Geo) (n a b : Nat) : State → Prop :=
  DK g n a [wDD, wNN, wN] [sStg, sB, sLt, sOkDE] fun V => V sStg ≤ 1 ∧ V sB = b

/-- `upBitsSelH`'s copy into `wT` made. -/
abbrev DBC (g : Geo) (n a b : Nat) : State → Prop :=
  DK g n a [wT, wDD, wNN, wN] [sStg, sB, sLt, sOkDE] fun V => V sStg ≤ 1 ∧ V sB = b

/-- `upBitsSelH`'s doublings, `i` made. -/
abbrev DBT (g : Geo) (n a b : Nat) (i : Nat) : State → Prop :=
  DK g n a [wT, wDD, wNN, wN] [sBc, sStg, sB, sLt, sOkDE] fun V => V sStg ≤ 1 ∧ V sB = b ∧ V sBc = b - i

section
variable {g : Geo} {s : State} {n a b : Nat}

theorem db1_ok (h : DX g n a sB b s) (ha1 : a ≤ 1024) (hb : 0 < b) (hb32 : b < 32) (hw1 : 1 ≤ wq a) :
    WP isa (seqs db1) s (DBM g n a b) := by
  obtain ⟨⟨ha, hw⟩, s0, A, AW, V, h, hd, h1, hz, hn, hNW⟩ := h
  have hW := h.rtW
  have nw := hW.ws.workspace.nowrap
  have fa := h.wsW.arr_fit (j := wDD) (by decide)
  have wW : g.W = 2 * g.w + 2 := rfl
  simp only [S] at fa
  simp only [seqs]
  refine WP.seq (VG.Proof.Rsa.X86.WordRt.topPtr_ok hW (h.mlen ha ha1) (j := wDD) (i := 1) (r := .esi) (t := .edx)
    (by decide) (by decide) (by decide) (by decide) (by decide) hw1 (by rw [kw_wid]; change wq a ≤ g.W + 2; omega_using [hw, wW])
    fun u₁ U₁ m₁ p₁ _ => ?_)
  rw [kw_wid] at p₁
  change PtrAt u₁ g.B .esi (arr g.W wDD + 4 * wq a - 4 * 1) at p₁
  refine wp_movS (readSrc_ptr (h.rt.rt.of_wr U₁.2.2) p₁ (d := 0) (by omega_using [hw, fa, wW])) fun u₂ U₂ _ => WP.block_nil ?_
  have h₂ := h.of_rest (rs := opRegs) ((U₁.mono (by decide)).trans (U₂.keeps.mono (by decide)))
    (fun x hx => hx) (by rw [U₂.mem, m₁])
  refine WP.seq (WP.mono (topTest_ok h₂.ws (b := b) (by rw [h₂.sl _ (by simp), hd]) hb hb32)
    fun t₃ ⟨K₃, m₃, _⟩ => ?_)
  have h₃ := h₂.of_rest K₃ (by decide) m₃
  refine WP.mono h₃.flagZero fun t₄ ⟨h₄, _⟩ => ?_
  exact ⟨⟨ha, hw⟩, s0, A, AW, _, h₄, ⟨by rw [upd_self]; split <;> decide, by rw [upd_ne _ _ (by decide)]; exact hd⟩,
    h1, hz, hn, hNW⟩

end

theorem c_db1 : OkK [sB] (seqs db1) := ⟨_, by taint_decide⟩
theorem c_copyT (j : Nat) (hj : j = wDD ∨ j = wNN) : OkK [] (copy wid wT j) := by
  rcases hj with rfl | rfl
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩
theorem c_selT (j : Nat) (hj : j = wDD ∨ j = wNN) : OkK [] (sel wid j j wT sStg) := by
  rcases hj with rfl | rfl
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩
theorem c_dblT : OkK [] (chain wid .adc wT wT wT false) := ⟨_, by taint_decide⟩
theorem c_bcInit : OkK [sB] (.block [.mov .eax (.mem (sc sB)), .store (sc sBc) .eax]) := ⟨_, by taint_decide⟩
theorem c_bcDown : OkK [sBc] (.block downBc) := ⟨_, by taint_decide⟩

/-- `upBitsSelH j`, related. -/
theorem upBitsSel_rel {g : Geo} (pg : PubG g) {n a b j : Nat} (hj : j = wDD ∨ j = wNN) (hb : 0 < b)
    (hb32 : b < 32) :
    RelCT isa (Both (DBM g n a b)) (upBitsSelH j) (Both (DBM g n a b)) := by
  have hjW : j ∈ [wDD, wNN, wN] := by rcases hj with rfl | rfl <;> simp
  have hjT : j ≠ wT := by rcases hj with rfl | rfl <;> decide
  have hjN : wN ≠ j := by rcases hj with rfl | rfl <;> decide
  have hl : ∀ i ∈ [aOne1, aZero, aN], i / 2 ≠ j := by rcases hj with rfl | rfl <;> decide
  unfold upBitsSelH
  simp only [seqs]
  refine VG.RelCT.seq (R := Both (DBC g n a b))
    (leafDK (n := n) (a := a) (liveW := [wDD, wNN, wN]) (ls := [sStg, sB, sLt, sOkDE])
      (H := fun V => V sStg ≤ 1 ∧ V sB = b) (Q := fun g' => DBC g' n a b) pg (fun _ => 0)
      (by simp) (by simp) (fun g' s h => ?_) (c_copyT j hj))
    (VG.RelCT.seq (R := Both (DBT g n a b b))
      (relTimesH (S := fun g' => DBC g' n a b) (Fin := fun g' => DBT g' n a b b)
        (fun g' i => DBT g' n a b i) (fun g' i => DBT g' n a b i) hb (by omega_using [hb32])
        (fun _ h => h.p0 pg) (fun _ _ h => h.p0 pg) (fun _ h => h.onView) (fun _ _ h => h.onView)
        (fun g' s h => ?_) (fun g' s t h k e r => ?_) (fun g' i t _ h => ?_) (fun g' i t u _ h k e r => ?_)
        (fun i _ => leafDK (n := n) (a := a) (liveW := [wT, wDD, wNN, wN]) (ls := [sBc, sStg, sB, sLt, sOkDE])
          (H := fun V => V sStg ≤ 1 ∧ V sB = b ∧ V sBc = b - i) (Q := fun g' => DBT g' n a b i) pg (fun _ => 0)
          (by simp) (by simp) (fun g' s h => ?_) c_dblT)
        c_bcInit c_bcDown)
      (leafDK (n := n) (a := a) (liveW := [wT, wDD, wNN, wN]) (ls := [sBc, sStg, sB, sLt, sOkDE])
        (H := fun V => V sStg ≤ 1 ∧ V sB = b ∧ V sBc = b - b) (Q := fun g' => DBM g' n a b) pg (fun _ => 0)
        (by simp) (by simp) (fun g' s h => ?_) (c_selT j hj)))
  · obtain ⟨ga, s0, A, AW, V, k, hH, h1, hz, hn, hNW⟩ := h
    refine WP.mono (k.copy_W (o := wT) (a := j) (by decide) hjW (Ne.symm hjT) (by decide)) fun t ⟨kt, _⟩ => ?_
    exact ⟨ga, s0, A, _, V, kt, hH, h1, hz, hn, by rw [upd_ne _ _ (by decide)]; exact hNW⟩
  · obtain ⟨_, _, _, _, V, k, ⟨_, hB⟩, _⟩ := h
    exact ⟨k.ws, by rw [k.sl _ (by simp), hB]⟩
  · obtain ⟨ga, s0, A, AW, V, hK, ⟨hS, hB⟩, h1, hz, hn, hNW⟩ := h
    exact ⟨ga, s0, A, AW, _, hK.slot1 k (by decide) (r.mono (by decide)) e,
      ⟨by rw [upd_ne _ _ (by decide)]; exact hS, by rw [upd_ne _ _ (by decide)]; exact hB, by rw [upd_self]; omega_using []⟩,
      h1, hz, hn, hNW⟩
  · obtain ⟨_, _, _, _, V, k, ⟨_, _, hc⟩, _⟩ := h
    exact ⟨k.ws, by rw [k.sl _ (by simp), hc]⟩
  · obtain ⟨ga, s0, A, AW, V, k', ⟨hS, hB, _⟩, h1, hz, hn, hNW⟩ := h
    have P := (k'.slot1 k (by decide) r e).mono (A' := A) (live' := [aOne1, aZero, aN]) (AW' := AW)
      (liveW' := [wT, wDD, wNN, wN]) (ls' := [sBc, sStg, sB, sLt, sOkDE]) (fun j hj => ⟨hj, rfl⟩)
      (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨List.mem_cons_of_mem _ hd, rfl⟩)
    have hH : upd V sBc (b - (i + 1)) sStg ≤ 1 ∧ upd V sBc (b - (i + 1)) sB = b ∧
        upd V sBc (b - (i + 1)) sBc = b - (i + 1) :=
      ⟨by rw [upd_ne _ _ (by decide)]; exact hS, by rw [upd_ne _ _ (by decide)]; exact hB, upd_self ..⟩
    refine ⟨fun _ => ⟨ga, s0, A, AW, _, P, hH, h1, hz, hn, hNW⟩, fun hi => ?_⟩
    exact ⟨ga, s0, A, AW, _, P, ⟨hH.1, hH.2.1, by rw [hH.2.2, hi]⟩, h1, hz, hn, hNW⟩
  · obtain ⟨ga, s0, A, AW, V, k, hH, h1, hz, hn, hNW⟩ := h
    refine WP.mono (k.add_W (o := wT) (a := wT) (b := wT) (by decide) (by simp) (by simp) (by decide))
      fun t ⟨kt, _⟩ => ?_
    exact ⟨ga, s0, A, _, V, kt.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨by simp at hj ⊢; omega_using [hj], rfl⟩)
      (fun d hd => ⟨hd, rfl⟩), hH, h1, hz, hn, by rw [upd_ne _ _ (by decide)]; exact hNW⟩
  · obtain ⟨ga, s0, A, AW, V, k, ⟨hS, hB, _⟩, h1, hz, hn, hNW⟩ := h
    refine WP.mono (k.sel_W (o := j) (a := j) (b := wT) (sl := sStg) (by rcases hj with rfl | rfl <;> decide)
      (by simp [hjW]) (by simp) (by simp) hS (.inr hjT) hl) fun t ⟨kt, _⟩ => ?_
    exact ⟨ga, s0, A, _, V, kt.mono (fun j hj => ⟨hj, rfl⟩) (fun i hi => ⟨by simp at hi ⊢; omega_using [hi], rfl⟩)
      (fun d hd => ⟨by simp at hd ⊢; omega_using [hd], rfl⟩), ⟨hS, hB⟩, h1, hz, hn, by rw [upd_ne _ _ hjN]; exact hNW⟩

/-- A bit stage, related. -/
theorem stageDB_rel {g : Geo} (pg : PubG g) {n a b : Nat} (ha1 : a ≤ 1024) (hb : 0 < b) (hb32 : b < 32)
    (hw1 : 1 ≤ wq a) :
    RelCT isa (Both (DX g n a sB b)) stageDBH (Both (DBM g n a b)) := by
  have e : stageDBH = seqs (db1 ++ [upBitsSelH wDD, upBitsSelH wNN]) := rfl
  rw [e]
  exact relSeqs (leafDK pg (fun _ => b) (by decide) (fun V hV d hd => by simp at hd; subst hd; exact hV)
      (fun g' s h => db1_ok h ha1 hb hb32 hw1) c_db1)
    (VG.RelCT.seq (upBitsSel_rel pg (.inl rfl) hb hb32) (upBitsSel_rel pg (.inr rfl) hb hb32))

theorem c_bInit : OkK [] (.block [.mov .eax (.imm (BitVec.ofNat 32 (2 ^ 4))), .store (sc sB) .eax]) :=
  ⟨_, by taint_decide⟩
theorem c_bHalf : OkK [sB] (.block (halfB 0)) := ⟨_, by taint_decide⟩

/-- The bit stages of `D`'s leading zeros, related. -/
theorem bitStagesD_rel {g : Geo} (pg : PubG g) {n a : Nat} (ha1 : a ≤ 1024) (hw1 : 1 ≤ wq a) :
    RelCT isa (Both (D0 g n a)) (bitStagesL 16 1 stageDBH) (Both (D0 g n a)) := by
  have e : bitStagesL 16 1 stageDBH = bitStagesL (2 ^ 4) (2 ^ 0) stageDBH := rfl
  rw [e]
  refine relBitStagesL (S := fun g' => D0 g' n a) (Fin := fun g' => D0 g' n a)
    (fun g' j => DX g' n a sB (2 ^ j)) (fun g' j => DBM g' n a (2 ^ j)) (by decide) (by decide)
    (fun _ h => h.p0 pg) (fun _ _ h => h.p0 pg) (fun _ h => h.onView) (fun _ _ h => h.onView)
    (fun g' s h => let ⟨_, _, _, _, _, P⟩ := h.dvs; P.ws)
    (fun g' s t h k e r => ?_) (fun g' j t _ _ h => ?_) (fun g' j t u _ hj h k e r => ?_)
    (fun j _ hj => stageDB_rel pg ha1 (Nat.two_pow_pos j) ?_ hw1) c_bInit c_bHalf
  · obtain ⟨ga, _, _, _, _, P⟩ := h.dvs
    exact DvS.dx ga (P.reslot k (by decide) (by decide) (by decide) e (r.mono (by decide)))
  · obtain ⟨_, _, _, _, _, hK, ⟨_, hB⟩, _⟩ := h
    exact ⟨hK.ws, by rw [hK.sl _ (by simp), hB]⟩
  · obtain ⟨ga, s0, A, AW, V, hK, _, h1, hz, hn, hNW⟩ := h
    have P := hK.slot1 k (by decide) r e
    refine ⟨fun hj0 => ⟨ga, s0, A, AW, _, P.mono (fun i hi => ⟨hi, rfl⟩) (fun i hi => ⟨hi, rfl⟩)
      (fun d hd => ⟨by simp at hd ⊢; omega_using [hd], rfl⟩), ?_, h1, hz, hn, hNW⟩, fun hj0 => ⟨ga, s0, A, AW, _,
      P.mono (fun i hi => ⟨hi, rfl⟩) (fun i hi => ⟨hi, rfl⟩) (fun d hd => ⟨by simp at hd ⊢; omega_using [hd], rfl⟩),
      trivial, h1, hz, hn, hNW⟩⟩
    show upd V sB (2 ^ j / 2) sB = 2 ^ (j - 1)
    rw [upd_self, pow_pred hj0, Nat.mul_div_cancel_left _ (by decide)]
  · have : 2 ^ j ≤ 2 ^ 4 := Nat.pow_le_pow_right (by decide) hj
    simp only [Nat.reducePow] at this
    omega_using [this]

/-! ### The start, the division and the end -/

/-- `divB`'s start: one, `n - r` and `m + 1`, narrow and wide. -/
abbrev divBPre : List (Prog isa) :=
  [copy nar aOne1 aZero, .block (VG.Impl.Rsa.X86.KeyRt.setOne nar aOne1),
    VG.Impl.Rsa.X86.KeyRt.sub3 nar aD aN aRlo, chain nar .adc aM1 aM aOne1 false,
    zeroWide wid wDD, copy nar (2 * wDD) aM1, zeroWide wid wNN, copy nar (2 * wNN) aD]

/-- `divB`'s end: the quotient narrow, and whether the remainder is zero. -/
abbrev divBEnd : List (Prog isa) := [copy nar aD (2 * wNN), eqSFast nar sExact (2 * wRB) aZero]

/-- After `divB`'s division. -/
abbrev DQ (g : Geo) (n a : Nat) : State → Prop := DK g n a [wNN, wRB, wN] [sLt, sOkDE] fun _ => True

theorem divB_eq : divB = seqs (divBPre ++ [wordStagesL 128 (VG.Impl.Rsa.X86.WordModRt.width4 nl .eax) stageDWH,
    bitStagesL 16 1 stageDBH, wordDivQ nl wNN wRB wDD wDt false, seqs divBEnd]) := rfl

section
variable {g : Geo} {s : State} {n a : Nat}

theorem preB_ok (h : GA g a ∧ DA1 g n s) : WP isa (seqs divBPre) s (D0 g n a) := by
  obtain ⟨ga, s0, A, AW, V, h, hz, hn, hnW⟩ := h
  exact WP.mono (divB_pre h hz hn rfl rfl hnW) fun _ P => DvS.d0 ga P

theorem wdqB_ok (h : D0 g n a s) (ha1 : a ≤ 1024) (h4 : 4 ≤ wq a) (hw1 : wq a ≤ g.W) :
    WP isa (wordDivQ nl wNN wRB wDD wDt false) s (DQ g n a) := by
  obtain ⟨⟨ha, hw⟩, s0, A₃, AW₃, V₃, h₃, _, h1₃, hz₃, hn₃, hNW₃⟩ := h
  have kwW : VG.Proof.Rsa.X86.KeyRt.kw (16 * g.n + 24) = g.W := kw_wid _
  have h₃m := h₃.mono (ls' := [sLt, sOkDE]) (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, rfl⟩)
    (fun d hd => ⟨List.mem_cons_of_mem _ hd, rfl⟩)
  refine WP.mono (wordDivQ_ok h₃m.rtW (h₃m.mlen ha ha1) (x := wNN) (r := wRB) (m := wDD) (t := wDt)
    (extra := false) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) h4 (by rw [kwW]; exact hw1))
    fun t₄ ⟨_, k₄, _, _, _, _, _, K₄⟩ => ?_
  rw [kwW] at k₄
  have h₃n := h₃m.mono (liveW' := [wN]) (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨by simp at hj ⊢; omega_using [hj], rfl⟩)
    (fun d hd => ⟨hd, rfl⟩)
  have h₄ : KS g s0 A₃ [aOne1, aZero, aN] (upd (upd AW₃ wNN (num t₄.mem g.B g.W wNN)) wRB
      (num t₄.mem g.B g.W wRB)) [wNN, wRB, wN] V₃ [sLt, sOkDE] t₄ :=
    h₃n.core k₄ (fun j hj => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl <;> exact h₃n.wsW.arr_fit (by decide)) (by decide) (K₄.mono (by decide))
      (h₃n.arrs_W k₄ (by decide) (by decide)) (by decide)
      (fun j hj => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl
        · rw [upd_ne _ _ (by decide), upd_self]
        · rw [upd_self]
        · rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]
          exact (h₃n.arrsW_W k₄ (by decide) (by decide)) wN (by simp))
      (by decide) (h₃n.sl_keep k₄ (by decide)) h₃n.ls_ok
  exact ⟨⟨ha, hw⟩, s0, A₃, _, V₃, h₄, trivial, h1₃, hz₃, hn₃,
    by rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]; exact hNW₃⟩

theorem endB_ok (h : DQ g n a s) : WP isa (seqs divBEnd) s (DB1 g n) := by
  obtain ⟨_, s0, A, AW, V, h₄, _, h1, hz, hn, hNW⟩ := h
  have h1' : A 26 = 1 := h1
  have hz' : A 10 = 0 := hz
  have hn' : A 32 = n := hn
  have h₅ := (h₄.view (j := wNN) (by simp)).view (j := wRB) (by simp)
  simp only [seqs]
  refine WP.seq (WP.mono (h₅.copy_w (o := aD) (a := 2 * wNN) (by decide) (by simp) (by decide) (by decide))
    fun t₆ ⟨h₆, _, _⟩ => ?_)
  refine WP.mono (h₆.eq_w (d := sExact) (a := 2 * wRB) (b := aZero) (by simp) (by simp) (by decide)) fun t h₇ => ?_
  refine ⟨s0, _, _, _, h₇.mono (fun j hj => ⟨?_, rfl⟩) (fun j hj => ⟨?_, rfl⟩) (fun d hd => ⟨?_, rfl⟩),
      ?_, ?_, ?_, hNW⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢
    rcases hj with h | h | h | h <;> simp [h, VG.Impl.Rsa.X86.RecoverDetRt.aN]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢
    simp [hj]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
    rcases hd with h | h | h <;> simp [h]
  · simp [upd, aD, wNN, wRB, aOne1, h1']
  · simp [upd, aD, wNN, wRB, aZero, hz']
  · simp [upd, aD, wNN, wRB, VG.Impl.Rsa.X86.RecoverDetRt.aN, aN, hn']

end

theorem c_preB : OkK [] (seqs divBPre) := ⟨_, by taint_decide⟩
theorem c_endB : OkK [] (seqs divBEnd) := ⟨_, by taint_decide⟩
theorem c_wdqPreB : OkK [] (seqs (wdqPre nl wNN wRB wDD false)) := ⟨_, by taint_decide⟩
theorem c_dqAB : OkK [VG.Impl.Rsa.X86.WordModRt.oSteps] (seqs (dqA nl wNN wRB wDD wDt)) := ⟨_, by taint_decide⟩
theorem c_dq3B : OkK [VG.Impl.Rsa.X86.WordModRt.oSteps] (dq3 wNN) := ⟨_, by taint_decide⟩
theorem c_dq4 : OkK [VG.Impl.Rsa.X86.WordModRt.oSteps] dq4 := ⟨_, by taint_decide⟩

/-- `divB`, related, from its start to its end. -/
theorem divB_both {g : Geo} (pg : PubG g) {n a : Nat} (ha0 : 64 ≤ a) (ha1 : a ≤ 1024) (haw : wq a ≤ g.w) :
    RelCT isa (Both fun s => GA g a ∧ DA1 g n s) divB (Both (DB1 g n)) := by
  have h4 : 16 ≤ wq a := by simp only [wq]; omega_using [ha0]
  have hwW : wq a ≤ g.W := by simp only [Geo.W, VG.Impl.Rsa.X86.Recover.wide]; simp only [Geo.w] at haw; omega_using [haw]
  rw [divB_eq]
  refine relSeqs (leafP (P := fun g' s => GA g' a ∧ DA1 g' n s) (Q := fun g' => D0 g' n a) (fun _ => 0) (by simp)
    (fun s h => let ⟨_, _, _, _, k, _⟩ := h.2; k.pre0 pg)
    (fun s h => let ⟨ga, _, _, _, _, k, r⟩ := h; ⟨ga, _, _, _, _, k.onView, r⟩) (by simp)
    (fun _ _ h => preB_ok h) c_preB) ?_
  refine VG.RelCT.seq (wordStagesD_rel pg ha1) (VG.RelCT.seq (bitStagesD_rel pg ha1 (by omega_using [h4]))
    (VG.RelCT.seq ?_ (leafDK (n := n) (a := a) (liveW := [wNN, wRB, wN]) (ls := [sLt, sOkDE])
      (H := fun _ => True) (Q := fun g' => DB1 g' n) pg (fun _ => 0) (by simp) (by simp)
      (fun _ _ h => endB_ok h) c_endB)))
  refine relWordDivQ (a := a) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by omega_using [h4]) (by rw [kw_wid]; exact hwW) (fun _ h => h.p0 pg)
    (fun s h => let ⟨⟨ha, _⟩, _, _, _, _, k, _⟩ := h; k.mlen ha ha1)
    (fun s h => wdqB_ok h ha1 (by omega_using [h4]) hwW) (fun s h => run_of (wdqB_ok h.onView ha1 (by omega_using [h4]) hwW))
    c_wdqPreB c_dqAB c_dq3B c_dq4

/-- `divB`'s timing (`PLAN.md`, P7c). `n`'s bound is not needed: the stages and steps run their counts
whatever `n` is. -/
theorem divB_relCT {g : Geo} (pg : PubG g) (n a : Nat)
    (ha : g.args VG.Impl.Rsa.X86.RecoverDetRt.nl = BitVec.ofNat 32 a) (ha0 : 64 ≤ a) (ha1 : a ≤ 1024)
    (haw : VG.Proof.Rsa.X86.WordRt.wq a ≤ g.w) (_hn' : n < 2 ^ (32 * VG.Proof.Rsa.X86.WordRt.wq a)) :
    RelCT isa (RA (DA1 g n) (DA1 g n)) VG.Impl.Rsa.X86.RecoverDetRt.divB (RA (DB1 g n) (DB1 g n)) :=
  (divB_both pg ha0 ha1 haw).mono (fun _ _ ⟨_, hs, ht⟩ => ⟨⟨⟨ha, haw⟩, hs⟩, ⟨⟨ha, haw⟩, ht⟩⟩)
    fun _ _ ⟨hs, ht⟩ => RA.of pg (fun _ h => let ⟨_, _, _, _, k, _⟩ := h; k.stage) hs ht

end VG.Proof.Rsa.X86.Recover
