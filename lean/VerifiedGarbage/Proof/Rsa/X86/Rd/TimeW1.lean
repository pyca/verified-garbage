module

public import VerifiedGarbage.Proof.Rsa.X86.Rd.TimeW2
public import VerifiedGarbage.Proof.Rsa.X86.Rd.TimeBaseW
public import VerifiedGarbage.Proof.Bignum.ShiftStages
import VerifiedGarbage.Proof.Rsa.X86.Rd.DetPartsW
import VerifiedGarbage.Proof.Rsa.X86.Rd.ProdW
import VerifiedGarbage.Proof.Rsa.X86.Rd.TwosW
import VerifiedGarbage.Proof.Rsa.X86.Rd.Ops
import VerifiedGarbage.Proof.Rsa.X86.Rd.Loops
import VerifiedGarbage.Proof.Rsa.X86.WordRt.Mul
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.Rsa.X86.RecoverDetRt
meta import VerifiedGarbage.Proof.Rsa.X86.Rd.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Rsa.X86.Rd.TimeBaseW
meta import VerifiedGarbage.Proof.Rsa.X86.Rd.TimeW2

/-! # `det`'s timing on i686 by words: `twos`, `gcdSet`, the products and `minus4n`

`gcdSet` and `minus4n` are checked whole by the taint analysis (`PubA`). The others count their
loops in header words (`sC4`, `sB`, `sBc`, `oJ`) that both runs hold equal, so their leaves are
checked on the views (`OkK`), between frames that state those words, and their loops related by
`relWordStagesL`, `relBitStagesL`, `relTimesH` and `relLoopB`. `twos` is related on its stages'
sizes alone (`twos_rel`); its result, `u` odd, is each run's own (`twos_ok`).
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.RecoverRt (nar wid)
open VG.Impl.Rsa.X86.RecoverDetRt hiding aN aP aQ
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa.X86.InvBatchRt.Time (view)
open VG.Impl.Rsa.X86.Keys (seqs)
open VG.Impl.Rsa.X86.KeyRt (arrPtr bytesB copy chain zeroWide sel half)
open VG.Impl.Rsa.X86.WordModRt (oJ)
open VG.Impl.Mont.X86 (sc at_)

/-! ## `gcdSet` and `minus4n` -/

theorem gcdSet_pub : PubA gcdSet := ⟨_, by taint_decide⟩

theorem minus4n_pub : PubA minus4n := ⟨_, by taint_decide⟩

theorem gcdSet_tw1 {g : Geo} {n : Nat} {s : State} (hs : TW1 g n s) : WP isa gcdSet s (GW0 g n) := by
  obtain ⟨s0, A, AW, V, h, hu, hn⟩ := hs
  exact WP.mono (gcdSetW_ok h rfl rfl) fun t ⟨A', h', m, _, n'⟩ =>
    ⟨s0, A', AW, V, h', by rw [m]; exact hu, n'.trans hn⟩

theorem gcdSet_relCT {g : Geo} (_pg : PubG g) (n : Nat) :
    RelCT isa (RA (TW1 g n) (TW1 g n)) VG.Impl.Rsa.X86.RecoverDetRt.gcdSet (RA (GW0 g n) (GW0 g n)) :=
  gcdSet_pub.relCT (fun _ hs => gcdSet_tw1 hs) (fun _ hs => gcdSet_tw1 hs)

theorem minus4n_sq1 {g : Geo} {s : State} (hs : SQ1 g s) : WP isa minus4n s (M41 g) := by
  obtain ⟨s0, A, AW, V, h, hz⟩ := hs
  exact WP.mono (minus4n_ok h rfl rfl) fun t ⟨AW', V', h', _⟩ => ⟨s0, A, AW', V', h', hz⟩

theorem minus4n_relCT {g : Geo} (_pg : PubG g) :
    RelCT isa (RA (SQ1 g) (SQ1 g)) VG.Impl.Rsa.X86.RecoverDetRt.minus4n (RA (M41 g) (M41 g)) :=
  minus4n_pub.relCT (fun _ hs => minus4n_sq1 hs) (fun _ hs => minus4n_sq1 hs)

/-! ## `aProduct` -/

/-- `aProduct`'s rows: before row `k`, the count `k` in `oJ`. -/
def ARows (n : Nat) (g : Geo) (k : Nat) (s : State) : Prop :=
  St g [VG.Impl.Rsa.X86.Keys.aZero, VG.Impl.Rsa.X86.RecoverDetRt.aN] [] [oJ, sOkDE]
      (fun A _ V => V oJ = k ∧ A VG.Impl.Rsa.X86.Keys.aZero = 0 ∧ A VG.Impl.Rsa.X86.RecoverDetRt.aN = n) s ∧
    k ≤ g.w ∧ (0 < k → isa.eval .ne s = some (decide (k < g.w)))

theorem ARows.onView {n : Nat} {g : Geo} {k : Nat} {s : State} (h : ARows n g k s) :
    ARows n g.vw k (view s g.B g.Z) :=
  ⟨h.1.onView, h.2.1, fun hk => by rw [eval_view]; exact h.2.2 hk⟩

/-- The `oJ` count's flag: whether another row follows. -/
theorem ne_of_zf {v : State} {k w : Nat} (hk : k + 1 ≤ w) (zv : v.zf = some (decide (k + 1 = w))) :
    isa.eval .ne v = some (decide (k + 1 < w)) := by
  show v.zf.map (!·) = _
  rw [zv]
  by_cases e : k + 1 = w
  · simp [e]
  · simp only [e, decide_false, Option.map_some, Bool.not_false]
    exact congrArg some (decide_eq_true (by omega)).symm

theorem rowW_step {n : Nat} {g : Geo} {k : Nat} {s : State} (hs : ARows n g k s) (hk : k < g.w) :
    WP isa (rowW wA wX3 wT) s (ARows n g (k + 1)) := by
  obtain ⟨⟨s0, A, AW, V, h, hj, hz, hn⟩, -, -⟩ := hs
  have kwW : VG.Proof.Rsa.X86.KeyRt.kw (16 * g.n + 24) = g.W := kw_wid _
  have kwN : VG.Proof.Rsa.X86.KeyRt.kw (8 * g.n + 8) = g.w := kw_nar _
  have wW : g.W = 2 * g.w + 2 := rfl
  refine WP.mono (rowWRow_ok h.rtW h.rt (o := wA) (a := wX3) (b := wT) (j := k) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [h.sl oJ (by simp), hj]) (by rw [kwW]; omega))
    fun v ⟨_, _, kp, _, _, cv, zv, Kv⟩ => ?_
  rw [kwW] at kp
  rw [kwN] at zv
  have ds : ∀ d ∈ [oJ], SlotOk d := by decide
  refine ⟨⟨s0, A, AW, upd V oJ (k + 1), h.core kp (fun j hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact h.wsW.arr_fit (by decide)
      · exact h.wsW.arr_fit (by decide)) ds (Kv.mono (by decide)) (h.arrs_W kp (by decide) ds) h.live_lt
      (fun _ hj => nomatch hj) (fun _ hj => nomatch hj) (fun d hd => ?_) h.ls_ok, upd_self .., hz, hn⟩,
    by omega, fun _ => ne_of_zf hk zv⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · rw [cv, upd_self]
  · rw [upd_ne _ _ (by decide), kp.slot (h.ls_ok sOkDE (by simp)).2.1 (fun e he => by simp at he; subst he; decide)]
    exact h.sl sOkDE (by simp)

/-- `aProduct`'s start: `wT` the GCD widened, `wA` and its high half zero, the count zero. -/
abbrev aStart : List (Prog isa) := [zeroWide wid wT, copy nar (2 * wT) aG,
  zeroWide wid wA, zeroWide wid (wA + 1), .block [.mov .eax (.imm 0), .store (sc oJ) .eax]]

/-- `aProduct`'s end: `wA`'s high half and extra words zero. -/
abbrev aEnd : List (Prog isa) := [zeroWide wid (wA + 1),
  .block (arrPtr wid .eax wA .edx ++ bytesB wid .ecx ++ ([.alu .add .eax (.reg .ecx), .mov .ecx (.imm 0),
    .store (at_ .eax 0) .ecx, .store (at_ .eax 4) .ecx] : List Instr))]

theorem aStart_pub : PubA (seqs aStart) := ⟨_, by taint_decide⟩
theorem aEnd_pub : PubA (seqs aEnd) := ⟨_, by taint_decide⟩
theorem rowW_ok : OkK [oJ] (rowW wA wX3 wT) := ⟨_, by taint_decide⟩

theorem aProduct_split : aProduct = seqs (zeroWide wid wT :: aStart.tail ++ .loop (rowW wA wX3 wT) .ne :: aEnd) :=
  rfl

theorem aStart_ok {n : Nat} {g : Geo} {s : State} (hs : GW1 g n s) : WP isa (seqs aStart) s (ARows n g 0) := by
  obtain ⟨s0, A, AW, V, h, hz, hn⟩ := hs
  simp only [seqs]
  refine WP.seq (WP.mono (h.zeroWide_W (j := wT) (by decide) (by decide)) fun u₁ ⟨h₁, z₁⟩ => ?_)
  have h₁' : KS g s0 A [aG, VG.Impl.Rsa.X86.Keys.aZero, VG.Impl.Rsa.X86.RecoverDetRt.aN] (upd AW wT 0) [wX3] V
      [sOkDE] u₁ :=
    h₁.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨List.mem_cons_of_mem _ hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
  refine WP.seq (WP.mono (h₁'.widen (k := wT) (a := aG) (by decide) (by simp) (by decide) z₁ (by decide)
    (by decide)) fun u₂ ⟨h₂, _⟩ => ?_)
  refine WP.seq (WP.mono (h₂.zeroWide_W (j := wA) (by decide) (by decide)) fun u₃ ⟨h₃, _⟩ => ?_)
  refine WP.seq (WP.mono (h₃.zeroWide_W (j := wA + 1) (by decide) (by decide)) fun u₄ ⟨h₄, _⟩ => ?_)
  refine wp_movS (v := 0) rfl fun u₅ U₅ _ => ?_
  have h₅ := h₄.of_rest U₅.keeps (by decide) U₅.mem
  refine WP.mono (h₅.storeSlot (d := oJ) (by decide) .eax) fun u₆ ⟨h₆, _, _⟩ => ?_
  rw [U₅.gpr] at h₆
  refine ⟨⟨s0, A, AW, _, h₆.mono (live' := [VG.Impl.Rsa.X86.Keys.aZero, VG.Impl.Rsa.X86.RecoverDetRt.aN])
    (liveW' := []) (ls' := [oJ, sOkDE]) (fun j hj => ⟨by simp at hj ⊢; omega, rfl⟩) (fun _ hj => nomatch hj)
    (fun d hd => ⟨by simp at hd ⊢; omega, rfl⟩), ?_, hz, hn⟩, Nat.zero_le _, fun h => absurd h (Nat.lt_irrefl 0)⟩
  rw [upd_self]; rfl

theorem aEnd_ok {n : Nat} {g : Geo} {s : State} (hs : ARows n g g.w s) : WP isa (seqs aEnd) s (PA1 g n) := by
  obtain ⟨⟨s0, A, AW, V, h, -, hz, hn⟩, -, -⟩ := hs
  have h' : KS g s0 A [VG.Impl.Rsa.X86.Keys.aZero, VG.Impl.Rsa.X86.RecoverDetRt.aN]
      (upd AW wA (num s.mem g.B g.W wA)) [wA] V [oJ, sOkDE] s :=
    h.core (Keep.refl g.B g.W [] [] s.mem) (fun _ hj => nomatch hj) (fun _ hj => nomatch hj)
      (Keeps.refl _ _) h.arrs h.live_lt (fun j hj => by simp at hj; subst hj; rw [upd_self])
      (by decide) h.sl h.ls_ok
  simp only [seqs]
  refine WP.seq (WP.mono (h'.zeroWide_W (j := wA + 1) (by decide) (by decide)) fun u₁ ⟨h₁, _⟩ => ?_)
  refine WP.mono (h₁.clearTop (by simp) (by decide)) fun t ⟨h₂, top⟩ => ?_
  exact ⟨s0, A, _, _, h₂.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨by simp at hj ⊢; omega, rfl⟩)
    (fun d hd => ⟨by simp at hd ⊢; omega, rfl⟩), hz, hn, top⟩

theorem aProduct_relCT {g : Geo} (pg : PubG g) (n : Nat) :
    RelCT isa (RA (GW1 g n) (GW1 g n)) VG.Impl.Rsa.X86.RecoverDetRt.aProduct (RA (PA1 g n) (PA1 g n)) := by
  have w1 : 1 ≤ g.w := by
    simp only [Geo.w, VG.Impl.Rsa.X86.Recover.width]; omega
  rw [aProduct_split]
  refine relSeqs (R := Both (ARows n g 0)) ((aStart_pub.relCT (fun _ hs => aStart_ok hs) (fun _ hs => aStart_ok hs)).mono
    (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2⟩)) ?_
  refine VG.RelCT.seq (R := Both (ARows n g g.w)) (relLoopB (ARows n g) (K := g.w) (by omega) (fun k hk => ?_)
    (fun k s hk hkK hs => hs.2.2 hk)) ?_
  · exact (leafG (P := fun g' s => ARows n g' k s ∧ k < g'.w) (Q := fun g' => ARows n g' (k + 1)) pg (fun _ => k)
      (by decide) (fun _ h => h.1.1.mul) (fun _ h => ⟨h.1.onView, h.2⟩)
      (fun _ h => h.1.1.slots (fun d hd => by simp at hd; subst hd; simp)
        (fun _ _ _ f d hd => by simp at hd; subst hd; exact f.1))
      (fun _ _ h => rowW_step h.1 h.2) rowW_ok).mono (fun _ _ h => ⟨⟨h.1, hk⟩, h.2, hk⟩) fun _ _ h => h
  · exact (aEnd_pub.relCT (fun _ hs => aEnd_ok hs) (fun _ hs => aEnd_ok hs)).mono
      (fun s t h => RA.of pg (fun _ h => h.1.mul) h.1 h.2) fun _ _ h => h

/-! ## `square` -/

/-- `square`'s rows: before row `k`, the count `k` in `oJ`. -/
def SqRows (g : Geo) (k : Nat) (s : State) : Prop :=
  St g [aD, VG.Impl.Rsa.X86.Keys.aZero] [wN] [oJ, sExact, sLt, sOkDE]
      (fun A _ V => V oJ = k ∧ A VG.Impl.Rsa.X86.Keys.aZero = 0) s ∧
    k ≤ g.w ∧ (0 < k → isa.eval .ne s = some (decide (k < g.w)))

theorem SqRows.onView {g : Geo} {k : Nat} {s : State} (h : SqRows g k s) : SqRows g.vw k (view s g.B g.Z) :=
  ⟨h.1.onView, h.2.1, fun hk => by rw [eval_view]; exact h.2.2 hk⟩

/-- `square`'s row: `mulRow` of `aD` by itself into narrow 34 and 35 (wide `wA`). -/
abbrev sqRow : Prog isa := VG.Impl.Rsa.X86.WordModRt.mulRow nar (2 * wA) aD aD

theorem sqRow_step {g : Geo} {k : Nat} {s : State} (hs : SqRows g k s) (hk : k < g.w) :
    WP isa sqRow s (SqRows g (k + 1)) := by
  obtain ⟨⟨s0, A, AW, V, h, hj, hz⟩, -, -⟩ := hs
  have kwN : VG.Proof.Rsa.X86.KeyRt.kw (8 * g.n + 8) = g.w := kw_nar _
  refine WP.mono (VG.Proof.Rsa.X86.WordRt.mulRow_ok h.rt (o := 2 * wA) (a := aD) (b := aD) (j := k)
    (rows := none) (half := false) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [h.sl oJ (by simp), hj]) (by rw [kwN]; omega) (by simp))
    fun v ⟨_, kp, _, _, cv, zv, Kv⟩ => ?_
  rw [kwN] at kp
  simp only [VG.Proof.Rsa.X86.WordRt.rowsN, VG.Proof.Rsa.X86.WordRt.rowW, kwN] at zv
  have kp' : Keep g.B g.w [34, 35] [oJ] s.mem v.mem := kp
  have ds : ∀ d ∈ [oJ], SlotOk d := by decide
  refine ⟨⟨s0, A, AW, upd V oJ (k + 1), h.core kp' (fun j hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact h.ws.arr_fit (by decide)
      · exact h.ws.arr_fit (by decide)) ds (Kv.mono (by decide)) (h.arrs_w kp' (by decide) ds) h.live_lt
      (h.arrsW_w kp' (by decide) ds) h.liveW_lt (fun d hd => ?_) h.ls_ok, upd_self .., hz⟩,
    by omega, fun _ => ne_of_zf hk zv⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl
  · rw [cv, upd_self]
  all_goals
    rw [upd_ne _ _ (by decide), kp'.slot (h.ls_ok _ (by simp)).2.1 (fun e he => by simp at he; subst he; decide)]
    exact h.sl _ (by simp)

/-- `square`'s start: `b = q + 1`, then `mulWide`'s clearing and count, grouped to the left. -/
abbrev sqStart : Prog isa := .seq (.seq (.seq (chain nar .adc aD aD aOne1 false) (zeroWide nar (2 * wA)))
  (zeroWide nar (2 * wA + 1))) (.block [.mov .eax (.imm 0), .store (sc oJ) .eax])

theorem sqStart_pub : PubA sqStart := ⟨_, by taint_decide⟩
theorem sqRow_ok : OkK [oJ] sqRow := ⟨_, by taint_decide⟩

theorem square_split : square = .seq (chain nar .adc aD aD aOne1 false) (.seq (zeroWide nar (2 * wA))
    (.seq (zeroWide nar (2 * wA + 1)) (.seq (.block [.mov .eax (.imm 0), .store (sc oJ) .eax])
      (.loop sqRow .ne)))) :=
  rfl

theorem sqStart_ok {n : Nat} {g : Geo} {s : State} (hs : DB1 g n s) : WP isa sqStart s (SqRows g 0) := by
  obtain ⟨s0, A, AW, V, h, one, hz, -, -⟩ := hs
  refine WP.assoc' (WP.assoc' (WP.seq (WP.mono (h.add_w (o := aD) (a := aD) (b := aOne1) (by decide) (by simp)
    (by simp) (by decide)) fun u ⟨h₁, _⟩ => ?_)))
  refine WP.mono (VG.Proof.Rsa.X86.WordRt.rowsInit_ok h₁.rt (o := 2 * wA) (a := aD) (b := aD) (by decide))
    fun v I => ?_
  have kwN : VG.Proof.Rsa.X86.KeyRt.kw (8 * g.n + 8) = g.w := kw_nar _
  have kp := I.keep
  rw [kwN] at kp
  have kp' : Keep g.B g.w [34, 35] [oJ] u.mem v.mem := kp
  have ds : ∀ d ∈ [oJ], SlotOk d := by decide
  have h₂ := h₁.core kp' (fun j hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact h₁.ws.arr_fit (by decide)
      · exact h₁.ws.arr_fit (by decide)) ds (I.rest.mono (by decide)) (h₁.arrs_w kp' (by decide) ds)
      h₁.live_lt (h₁.arrsW_w kp' (by decide) ds) h₁.liveW_lt (ls' := [oJ, sExact, sLt, sOkDE])
      (V' := upd V oJ 0) (fun d hd => ?_) (by decide)
  · refine ⟨⟨s0, _, AW, _, h₂.mono (live' := [aD, VG.Impl.Rsa.X86.Keys.aZero]) (fun j hj => ⟨by simp at hj ⊢; omega, rfl⟩)
      (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩), upd_self .., ?_⟩, Nat.zero_le _,
      fun h => absurd h (Nat.lt_irrefl 0)⟩
    rw [upd_ne _ _ (by decide)]; exact hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl
  · rw [I.cnt, upd_self]
  all_goals
    rw [upd_ne _ _ (by decide), kp'.slot (h₁.ls_ok _ (by simp)).2.1 (fun e he => by simp at he; subst he; decide)]
    exact h₁.sl _ (by simp)

theorem SqRows.sq1 {g : Geo} {s : State} (hs : SqRows g g.w s) : SQ1 g s := by
  obtain ⟨⟨s0, A, AW, V, h, -, hz⟩, -, -⟩ := hs
  refine ⟨s0, A, _, V, (h.core (Keep.refl g.B g.W [] [] s.mem) (fun _ hj => nomatch hj) (fun _ hj => nomatch hj)
      (Keeps.refl _ _) h.arrs h.live_lt (liveW' := wA :: [wN]) (AW' := upd AW wA (num s.mem g.B g.W wA))
      (fun j hj => ?_) (by decide) h.sl h.ls_ok).mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, rfl⟩)
      (fun d hd => ⟨by simp at hd ⊢; omega, rfl⟩), hz⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl
  · rw [upd_self]
  · rw [upd_ne _ _ (by decide)]; exact h.arrsW _ (by simp)

theorem square_relCT {g : Geo} (pg : PubG g) (n : Nat) :
    RelCT isa (RA (DB1 g n) (DB1 g n)) VG.Impl.Rsa.X86.RecoverDetRt.square (RA (SQ1 g) (SQ1 g)) := by
  have w1 : 1 ≤ g.w := by
    simp only [Geo.w, VG.Impl.Rsa.X86.Recover.width]; omega
  rw [square_split]
  refine VG.RelCT.assoc (VG.RelCT.assoc (VG.RelCT.assoc ?_))
  refine VG.RelCT.seq (R := Both (SqRows g 0)) ((sqStart_pub.relCT (fun _ hs => sqStart_ok hs)
    (fun _ hs => sqStart_ok hs)).mono (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2⟩)) ?_
  refine (relLoopB (SqRows g) (K := g.w) (by omega) (fun k hk => ?_) (fun k s hk hkK hs => hs.2.2 hk)).mono
    (fun _ _ h => h) fun s t h => RA.of pg (P := SQ1 g)
    (fun _ h => let ⟨_, _, _, _, k, _⟩ := h; ⟨_, _, _, _, _, _, _, k⟩) (SqRows.sq1 h.1) (SqRows.sq1 h.2)
  exact (leafG (P := fun g' s => SqRows g' k s ∧ k < g'.w) (Q := fun g' => SqRows g' (k + 1)) pg (fun _ => k)
    (by decide) (fun _ h => h.1.1.mul) (fun _ h => ⟨h.1.onView, h.2⟩)
    (fun _ h => h.1.1.slots (fun d hd => by simp at hd; subst hd; simp)
      (fun _ _ _ f d hd => by simp at hd; subst hd; exact f.1))
    (fun _ _ h => sqRow_step h.1 h.2) sqRow_ok).mono (fun _ _ h => ⟨⟨h.1, hk⟩, h.2, hk⟩) fun _ _ h => h

/-! ## The halvings' frame -/

/-- The halvings' frame at a geometry of `w0` narrow words: the arrays `live`, `liveW` and the header
words `ls`, their values `F`. -/
def TwF (w0 : Nat) (live liveW ls : List Nat) (F : (Nat → Nat) → Prop) (g : Geo) (s : State) : Prop :=
  St g live liveW ls (fun _ _ V => F V) s ∧ g.w = w0

section
variable {w0 : Nat} {live liveW ls : List Nat} {F : (Nat → Nat) → Prop} {g : Geo} {s : State}

theorem TwF.onView (h : TwF w0 live liveW ls F g s) : TwF w0 live liveW ls F g.vw (view s g.B g.Z) :=
  ⟨h.1.onView, h.2⟩

theorem TwF.p0 (pg : PubG g) (h : TwF w0 live liveW ls F g s) : P0 g s :=
  let ⟨_, _, _, _, k, _⟩ := h.1
  k.pre0 pg

theorem TwF.mul (h : TwF w0 live liveW ls F g s) : MulPost g s := h.1.mul

end

/-- A leaf from a halvings' frame. -/
theorem twLeaf {w0 : Nat} {g : Geo} (pg : PubG g) {live liveW ls : List Nat} {F : (Nat → Nat) → Prop}
    {Q : Geo → State → Prop} {c : Prog isa} {ds : List Nat} (vals : Nat → Nat)
    (hds : ∀ d ∈ ds, d ∈ ls ∧ d + 4 ≤ 160) (hv : ∀ V, F V → ∀ d ∈ ds, V d = vals d)
    (hf : ∀ g' s, TwF w0 live liveW ls F g' s → WP isa c s (Q g')) (h : OkK ds c) :
    RelCT isa (Both (TwF w0 live liveW ls F g)) c (Both (Q g)) :=
  leafP vals (fun d hd => (hds d hd).2) (fun _ h => h.p0 pg) (fun _ h => h.onView)
    (fun _ h => h.1.slots (fun d hd => (hds d hd).1) (fun _ _ V f => hv V f)) hf h

/-- A header word set, in place of its old value. -/
theorem KS.setSlot {g : Geo} {s0 t u : State} {A AW V : Nat → Nat} {live liveW ls : List Nat} {d x v : Nat}
    (h : KS g s0 A live AW liveW V ls t) (k : Keep g.B v [] [d] t.mem u.mem) (hd : SlotOk d)
    (r : Keeps opRegs t u) (e : slot u.mem g.B d = x) :
    KS g s0 A live AW liveW (upd V d x) ls u :=
  (h.slot1 k hd r e).mono (fun _ hj => ⟨hj, rfl⟩) (fun _ hj => ⟨hj, rfl⟩)
    (fun _ he => ⟨List.mem_cons_of_mem _ he, rfl⟩)

/-- The stages' frames. -/
abbrev twL : List Nat := [aU, aX2, VG.Impl.Rsa.X86.RecoverDetRt.aN]

/-- Between the stages. -/
abbrev TS0 (w0 : Nat) : Geo → State → Prop := TwF w0 twL [wX3] [sOkDE] fun _ => True

/-- Before and after a word stage of `2^j` words. -/
abbrev TPW (w0 j : Nat) : Geo → State → Prop := TwF w0 twL [wX3] [sC4, sOkDE] fun V => V sC4 = 4 * 2 ^ j

/-- Before and after a bit stage of `2^j` bits. -/
abbrev TPB (w0 j : Nat) : Geo → State → Prop := TwF w0 twL [wX3] [sB, sOkDE] fun V => V sB = 2 ^ j

/-- Inside a word stage, its flag set. -/
abbrev TMW (w0 j : Nat) : Geo → State → Prop :=
  TwF w0 twL [wX3] [sStg, sC4, sOkDE] fun V => V sStg ≤ 1 ∧ V sC4 = 4 * 2 ^ j

/-- Inside a bit stage of `b` bits, its flag set. -/
abbrev TMB (w0 b : Nat) (live liveW : List Nat) : Geo → State → Prop :=
  TwF w0 live liveW [sStg, sB, sOkDE] fun V => V sStg ≤ 1 ∧ V sB = b

/-- Inside a bit stage's `timesH`, before run `i` (or, `Post`, before its count down). -/
abbrev TMT (w0 b : Nat) (live liveW : List Nat) (i : Nat) : Geo → State → Prop :=
  TwF w0 live liveW [sBc, sStg, sB, sOkDE] fun V => V sBc = b - i ∧ V sStg ≤ 1 ∧ V sB = b

/-- Membership in a literal list, by `decide`. -/
theorem memOf {l l' : List Nat} (h : ∀ i ∈ l, i ∈ l') {i : Nat} (hi : i ∈ l) : i ∈ l' := h i hi

/-! ## The steps, for any geometry -/

section
variable {w0 j b : Nat} {g : Geo} {s : State}

theorem twInit_step {n : Nat} (three : 3 ≤ n) (hs : TW0 g n s) : WP isa twosInit s (TS0 g.w g) := by
  obtain ⟨s0, A, AW, V, h, z, hn⟩ := hs
  exact WP.mono (twosInit_ok h z hn rfl rfl three) fun _ ⟨A', AW', V', h', _⟩ =>
    ⟨⟨s0, A', AW', V', h'.mono (fun _ hj => ⟨hj, rfl⟩) (fun _ hj => ⟨hj, rfl⟩)
      (fun _ hd => ⟨List.mem_cons_of_mem _ hd, rfl⟩), trivial⟩, rfl⟩

theorem twWF_step (hj : 2 ^ j < w0) (hs : TPW w0 j g s) : WP isa (stageWH false) s (TPW w0 j g) := by
  obtain ⟨⟨s0, A, AW, V, h, hd⟩, hw⟩ := hs
  exact WP.mono (stageW_ok false (s0 := s0) (ok := V sOkDE) (n := A VG.Impl.Rsa.X86.RecoverDetRt.aN)
    (v := (A aU, A aX2, AW wX3)) ⟨A, AW, V, h, hd, rfl, rfl, rfl, rfl, rfl⟩ (Nat.two_pow_pos j) (by omega))
    fun _ ⟨A', AW', V', h', hd', _⟩ => ⟨⟨s0, A', AW', V', h', hd'⟩, hw⟩

theorem twWT1_step (hj : 2 ^ j < w0) (hs : TPW w0 j g s) :
    WP isa (seqs [orLowH aU aX2, .block flagZero, moveH nar aU aTmp true false, sel nar aU aU aTmp sStg]) s
      (TMW w0 j g) := by
  obtain ⟨⟨s0, A, AW, V, h, hd⟩, hw⟩ := hs
  exact WP.mono (stageW_pre true h hd (Nat.two_pow_pos j) (by omega))
    fun _ ⟨A', V', h', f, e1, _⟩ => ⟨⟨s0, A', AW, V', h'.mono (fun _ hj => ⟨memOf (by decide) hj, rfl⟩)
      (fun _ hj => ⟨hj, rfl⟩) (fun _ hd => ⟨hd, rfl⟩), by rw [f]; split <;> decide, e1⟩, hw⟩

theorem twWT2_step (hj : 2 ^ j < w0) (hs : TMW w0 j g s) :
    WP isa (seqs [moveH nar aX2 aTmp true false, sel nar aX2 aX2 aTmp sStg]) s (TMW w0 j g) := by
  obtain ⟨⟨s0, A, AW, V, h, f, e1⟩, hw⟩ := hs
  simp only [seqs]
  refine WP.seq (WP.mono (h.moveDown_w (o := aTmp) (a := aX2) (c := 2 ^ j) (by decide) (by simp) (by decide)
    (by omega) (by simp) e1 (by decide)) fun t₁ ⟨h₁, _, _⟩ => ?_)
  refine WP.mono (h₁.sel_w (o := aX2) (a := aX2) (b := aTmp) (sl := sStg) (by decide) (by simp)
    (by simp) (by simp) f (.inr (by decide)) (by decide)) fun _ ⟨h₂, _⟩ => ?_
  exact ⟨⟨s0, _, AW, V, h₂.mono (fun _ hj => ⟨memOf (by decide) hj, rfl⟩) (fun _ hj => ⟨hj, rfl⟩)
    (fun _ hd => ⟨hd, rfl⟩), f, e1⟩, hw⟩

theorem twWT3_step (hj : 2 ^ j < w0) (hs : TMW w0 j g s) :
    WP isa (seqs [moveH wid wX3 wT false true, sel wid wX3 wX3 wT sStg]) s (TPW w0 j g) := by
  obtain ⟨⟨s0, A, AW, V, h, f, e1⟩, hw⟩ := hs
  simp only [seqs]
  refine WP.seq (WP.mono (h.moveUp_W (o := wT) (a := wX3) (c := 2 ^ j) (by decide) (by simp) (by decide)
    (by simp only [Geo.W, VG.Impl.Rsa.X86.Recover.wide]; simp only [Geo.w] at hw; omega) (by simp) e1
    (by decide)) fun t₁ ⟨h₁, _, _⟩ => ?_)
  refine WP.mono (h₁.sel_W (o := wX3) (a := wX3) (b := wT) (sl := sStg) (by decide) (by simp)
    (by simp) (by simp) f (.inr (by decide)) (by decide)) fun _ ⟨h₂, _⟩ => ?_
  exact ⟨⟨s0, A, _, V, h₂.mono (fun _ hj => ⟨hj, rfl⟩) (fun _ hj => ⟨memOf (by decide) hj, rfl⟩)
    (fun _ hd => ⟨memOf (by decide) hd, rfl⟩), e1⟩, hw⟩

/-- A bit stage's test of the low words' OR. -/
abbrev twLow (joint : Bool) : Prog isa :=
  .block (arrPtr nar .esi aU .edx ++ arrPtr nar .ebp (if joint then aX2 else aU) .edx ++
    ([.mov .eax (.mem (at_ .esi 0)), .alu .or .eax (.mem (at_ .ebp 0))] : List Instr))

theorem twB0_step (joint : Bool) (hj : 2 ^ j < 32) (hs : TPB w0 j g s) :
    WP isa (.seq (.seq (twLow joint) lowTest) (.block flagZero)) s (TMB w0 (2 ^ j) twL [wX3] g) := by
  obtain ⟨⟨s0, A, AW, V, h, hd⟩, hw⟩ := hs
  refine WP.seq (WP.seq (WP.mono (h.lowOr_ok (a := aU) (b := if joint then aX2 else aU) (by simp)
    (by cases joint <;> simp)) fun t₁ ⟨h₁, _⟩ => WP.mono (lowTest_ok h₁.ws (b := 2 ^ j)
      (by rw [h₁.sl _ (by simp), hd]) (Nat.two_pow_pos j) hj) fun t₂ ⟨K₂, m₂, _⟩ => ?_))
  have h₂ := h₁.of_rest K₂ (by decide) m₂
  refine WP.mono h₂.flagZero fun _ ⟨h₃, _⟩ => ?_
  exact ⟨⟨s0, A, AW, _, h₃, by rw [upd_self]; split <;> decide, by rw [upd_ne _ _ (by decide)]; exact hd⟩, hw⟩

theorem twCopy_step {src : Nat} (hsrc : src ∈ twL) (hne : aTmp ≠ src) (hs : TMB w0 b twL [wX3] g s) :
    WP isa (copy nar aTmp src) s (TMB w0 b (aTmp :: twL) [wX3] g) := by
  obtain ⟨⟨s0, A, AW, V, h, f⟩, hw⟩ := hs
  exact WP.mono (h.copy_w (o := aTmp) (a := src) (by decide) hsrc hne (by decide))
    fun _ ⟨h₁, _, _⟩ => ⟨⟨s0, _, AW, V, h₁, f⟩, hw⟩

theorem twSel_step {o : Nat} (ho : o ∈ twL) (hne : o ≠ aTmp) (ho44 : o < 44) (hs : TMB w0 b (aTmp :: twL) [wX3] g s) :
    WP isa (sel nar o o aTmp sStg) s (TMB w0 b twL [wX3] g) := by
  obtain ⟨⟨s0, A, AW, V, h, f⟩, hw⟩ := hs
  exact WP.mono (h.sel_w (o := o) (a := o) (b := aTmp) (sl := sStg) ho44 (List.mem_cons_of_mem _ ho) (by simp)
    (by simp) f.1 (.inr hne) (fun i hi => (show ∀ o ∈ twL, ∀ i ∈ [wX3], o / 2 ≠ i by decide) o ho i hi))
    fun _ ⟨h₁, _⟩ => ⟨⟨s0, _, AW, V, h₁.mono (fun _ hj => ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj), rfl⟩)
      (fun _ hj => ⟨hj, rfl⟩) (fun _ hd => ⟨hd, rfl⟩), f⟩, hw⟩

theorem twCopyW_step (hs : TMB w0 b twL [wX3] g s) :
    WP isa (copy wid wT wX3) s (TMB w0 b twL [wT, wX3] g) := by
  obtain ⟨⟨s0, A, AW, V, h, f⟩, hw⟩ := hs
  exact WP.mono (h.copy_W (o := wT) (a := wX3) (by decide) (by simp) (by decide) (by decide))
    fun _ ⟨h₁, _⟩ => ⟨⟨s0, A, _, V, h₁, f⟩, hw⟩

theorem twSelW_step (hs : TMB w0 b twL [wT, wX3] g s) :
    WP isa (sel wid wX3 wX3 wT sStg) s (TMB w0 b twL [wX3] g) := by
  obtain ⟨⟨s0, A, AW, V, h, f⟩, hw⟩ := hs
  exact WP.mono (h.sel_W (o := wX3) (a := wX3) (b := wT) (sl := sStg) (by decide) (by simp) (by simp)
    (by simp) f.1 (.inr (by decide)) (by decide))
    fun _ ⟨h₁, _⟩ => ⟨⟨s0, A, _, V, h₁.mono (fun _ hj => ⟨hj, rfl⟩) (fun _ hj => ⟨memOf (by decide) hj, rfl⟩)
      (fun _ hd => ⟨hd, rfl⟩), f⟩, hw⟩

theorem TMB.tpb (hs : TMB w0 (2 ^ j) twL [wX3] g s) : TPB w0 j g s := by
  obtain ⟨⟨s0, A, AW, V, h, f⟩, hw⟩ := hs
  exact ⟨⟨s0, A, AW, V, h.mono (fun _ hj => ⟨hj, rfl⟩) (fun _ hj => ⟨hj, rfl⟩)
    (fun _ hd => ⟨memOf (by decide) hd, rfl⟩), f.2⟩, hw⟩

end

/-! ## The leaves' certificates -/

theorem twC_init : OkK [] twosInit := ⟨_, by taint_decide⟩
theorem twC_wf : OkK [sC4] (stageWH false) := ⟨_, by taint_decide⟩
theorem twC_w1 : OkK [sC4]
    (seqs [orLowH aU aX2, .block flagZero, moveH nar aU aTmp true false, sel nar aU aU aTmp sStg]) :=
  ⟨_, by taint_decide⟩
theorem twC_w2 : OkK [sC4] (seqs [moveH nar aX2 aTmp true false, sel nar aX2 aX2 aTmp sStg]) := ⟨_, by taint_decide⟩
theorem twC_w3 : OkK [sC4] (seqs [moveH wid wX3 wT false true, sel wid wX3 wX3 wT sStg]) := ⟨_, by taint_decide⟩
theorem twC_b0f : OkK [sB] (.seq (.seq (twLow false) lowTest) (.block flagZero)) := ⟨_, by taint_decide⟩
theorem twC_b0t : OkK [sB] (.seq (.seq (twLow true) lowTest) (.block flagZero)) := ⟨_, by taint_decide⟩
theorem twC_cu : OkK [] (copy nar aTmp aU) := ⟨_, by taint_decide⟩
theorem twC_cx : OkK [] (copy nar aTmp aX2) := ⟨_, by taint_decide⟩
theorem twC_cw : OkK [] (copy wid wT wX3) := ⟨_, by taint_decide⟩
theorem twC_su : OkK [] (sel nar aU aU aTmp sStg) := ⟨_, by taint_decide⟩
theorem twC_sx : OkK [] (sel nar aX2 aX2 aTmp sStg) := ⟨_, by taint_decide⟩
theorem twC_sw : OkK [] (sel wid wX3 wX3 wT sStg) := ⟨_, by taint_decide⟩
theorem twC_half : OkK [] (.seq (.block [.mov .ebx (.imm 0)]) (half nar aTmp)) := ⟨_, by taint_decide⟩
theorem twC_dbl : OkK [] (chain wid .adc wT wT wT false) := ⟨_, by taint_decide⟩
theorem twC_bc0 : OkK [sB] (.block [.mov .eax (.mem (sc sB)), .store (sc sBc) .eax]) := ⟨_, by taint_decide⟩
theorem twC_bcd : OkK [sBc] (.block downBc) := ⟨_, by taint_decide⟩
theorem twC_c4i : OkK [] (.block [.mov .eax (.imm (BitVec.ofNat 32 (4 * 2 ^ 7))), .store (sc sC4) .eax]) :=
  ⟨_, by taint_decide⟩
theorem twC_lim : OkK [sC4]
    (.block (bytesB nar .eax ++ ([.mov .ecx (.mem (sc sC4)), .alu .cmp .ecx (.reg .eax)] : List Instr))) :=
  ⟨_, by taint_decide⟩
theorem twC_c4h : OkK [sC4] (.block halfC4) := ⟨_, by taint_decide⟩
theorem twC_bi : OkK [] (.block [.mov .eax (.imm (BitVec.ofNat 32 (2 ^ 4))), .store (sc sB) .eax]) :=
  ⟨_, by taint_decide⟩
theorem twC_bh : OkK [sB] (.block (halfB 0)) := ⟨_, by taint_decide⟩

/-! ## The stages, related -/

/-- `timesH body` on a bit stage's frame, `body` keeping it. -/
theorem twTimes {w0 b : Nat} {g : Geo} (pg : PubG g) {live liveW : List Nat} {body : Prog isa}
    (hb : 0 < b) (hb32 : b < 2 ^ 32) (cb : OkK [] body)
    (hstep : ∀ g' s0 A AW V s, KS g' s0 A live AW liveW V [sBc, sStg, sB, sOkDE] s →
      WP isa body s fun t => ∃ A' AW', KS g' s0 A' live AW' liveW V [sBc, sStg, sB, sOkDE] t) :
    RelCT isa (Both (TMB w0 b live liveW g)) (timesH body) (Both (TMB w0 b live liveW g)) :=
  relTimesH (fun g' i => TMT w0 b live liveW i g') (fun g' i => TMT w0 b live liveW i g') hb hb32 (fun _ h => h.p0 pg) (fun _ _ h => h.p0 pg)
    (fun _ h => h.onView) (fun _ _ h => h.onView)
    (fun _ _ ⟨⟨_, _, _, _, h, f⟩, _⟩ => ⟨h.ws, by rw [h.sl sB (by simp), f.2]⟩)
    (fun _ _ _ ⟨⟨s0, A, AW, _, h, f⟩, hw⟩ k e r =>
      ⟨⟨s0, A, AW, _, h.slot1 k (by decide) (r.mono (by decide)) e, by rw [upd_self, Nat.sub_zero],
        by rw [upd_ne _ _ (by decide)]; exact f.1, by rw [upd_ne _ _ (by decide)]; exact f.2⟩, hw⟩)
    (fun _ _ _ _ ⟨⟨_, _, _, _, h, f⟩, _⟩ => ⟨h.ws, by rw [h.sl sBc (by simp), f.1]⟩)
    (fun _ _ _ _ _ ⟨⟨s0, A, AW, _, h, f⟩, hw⟩ k e r =>
      have h' := h.setSlot k (by decide) r e
      ⟨fun _ => ⟨⟨s0, A, AW, _, h', by rw [upd_self], by rw [upd_ne _ _ (by decide)]; exact f.2.1,
          by rw [upd_ne _ _ (by decide)]; exact f.2.2⟩, hw⟩,
        fun _ => ⟨⟨s0, A, AW, _, h'.mono (fun _ hj => ⟨hj, rfl⟩) (fun _ hj => ⟨hj, rfl⟩)
          (fun _ hd => ⟨List.mem_cons_of_mem _ hd, rfl⟩),
          by rw [upd_ne _ _ (by decide)]; exact f.2.1, by rw [upd_ne _ _ (by decide)]; exact f.2.2⟩, hw⟩⟩)
    (fun _ _ => twLeaf pg (fun _ => 0) (ds := []) (by simp) (by simp)
      (fun g' s ⟨⟨s0, A, AW, V, h, f⟩, hw⟩ =>
        WP.mono (hstep g' s0 A AW V s h) fun _ ⟨A', AW', h'⟩ => ⟨⟨s0, A', AW', V, h', f⟩, hw⟩) cb)
    twC_bc0 twC_bcd

/-- A word stage of `2^j` words, related. -/
theorem twWordBody (joint : Bool) {w0 j : Nat} {g : Geo} (pg : PubG g) (hj : 2 ^ j < w0) :
    RelCT isa (Both (TPW w0 j g)) (stageWH joint) (Both (TPW w0 j g)) := by
  have hv : ∀ V : Nat → Nat, V sC4 = 4 * 2 ^ j → ∀ d ∈ [sC4], V d = (fun _ => 4 * 2 ^ j) d := fun V f d hd => by
    simp only [List.mem_singleton] at hd; subst hd; exact f
  have hv' : ∀ V : Nat → Nat, (V sStg ≤ 1 ∧ V sC4 = 4 * 2 ^ j) → ∀ d ∈ [sC4], V d = (fun _ => 4 * 2 ^ j) d :=
    fun V f => hv V f.2
  cases joint
  · exact twLeaf pg _ (by decide) hv (fun _ _ h => twWF_step hj h) twC_wf
  · rw [show stageWH true = seqs (orLowH aU aX2 :: [.block flagZero, moveH nar aU aTmp true false,
        sel nar aU aU aTmp sStg] ++ moveH nar aX2 aTmp true false :: ([sel nar aX2 aX2 aTmp sStg] ++
          moveH wid wX3 wT false true :: [sel wid wX3 wX3 wT sStg])) from rfl]
    refine relSeqs (R := Both (TMW w0 j g)) (twLeaf pg _ (by decide) hv (fun _ _ h => twWT1_step hj h) twC_w1) ?_
    exact relSeqs (R := Both (TMW w0 j g)) (twLeaf pg _ (by decide) hv' (fun _ _ h => twWT2_step hj h) twC_w2)
      (twLeaf pg _ (by decide) hv' (fun _ _ h => twWT3_step hj h) twC_w3)

/-- A bit stage of `2^j` bits, related. -/
theorem twBitBody (joint : Bool) {w0 j : Nat} {g : Geo} (pg : PubG g) (hj : 2 ^ j < 32) :
    RelCT isa (Both (TPB w0 j g)) (stageBH joint) (Both (TPB w0 j g)) := by
  have hb : 0 < 2 ^ j := Nat.two_pow_pos j
  have hb32 : 2 ^ j < 2 ^ 32 := by omega
  have hv : ∀ V : Nat → Nat, V sB = 2 ^ j → ∀ d ∈ [sB], V d = (fun _ => 2 ^ j) d := fun V f d hd => by
    simp only [List.mem_singleton] at hd; subst hd; exact f
  have T1 := twTimes (w0 := w0) (live := aTmp :: twL) (liveW := [wX3]) pg hb hb32 twC_half
    fun g' s0 A AW V s h => by
      refine WP.seq (wp_movS rfl fun t₁ U _ => WP.block_nil ?_)
      have P₁ := h.of_rest U.keeps (by decide) U.mem
      exact WP.mono (P₁.half_w (j := aTmp) (by simp) (by rw [U.gpr]; rfl) (by decide)) fun _ ⟨hv, _⟩ =>
        ⟨_, AW, hv.mono (fun _ hj => ⟨List.mem_cons_of_mem _ hj, rfl⟩) (fun _ hj => ⟨hj, rfl⟩)
          (fun _ hd => ⟨hd, rfl⟩)⟩
  have L0 := fun joint => twLeaf (Q := TMB w0 (2 ^ j) twL [wX3]) pg _ (by decide) hv
    (fun _ _ h => twB0_step joint hj h)
  have LCu := twLeaf (Q := TMB w0 (2 ^ j) (aTmp :: twL) [wX3]) (ds := []) pg (fun _ => 0) (by simp) (by simp)
    (fun _ _ h => twCopy_step (src := aU) (by simp) (by decide) h) twC_cu
  have LSu := twLeaf (Q := TMB w0 (2 ^ j) twL [wX3]) (ds := []) pg (fun _ => 0) (by simp) (by simp)
    (fun _ _ h => twSel_step (o := aU) (by simp) (by decide) (by decide) h) twC_su
  cases joint
  · rw [show stageBH false = .seq (twLow false) (.seq lowTest (.seq (.block flagZero)
      (.seq (.seq (copy nar aTmp aU) (timesH (.seq (.block [.mov .ebx (.imm 0)]) (half nar aTmp))))
        (sel nar aU aU aTmp sStg)))) from rfl]
    refine VG.RelCT.assoc (VG.RelCT.assoc ?_)
    refine VG.RelCT.seq (L0 false twC_b0f) (VG.RelCT.seq (VG.RelCT.seq LCu T1) ?_)
    exact LSu.mono (fun _ _ h => h) fun _ _ h => ⟨h.1.tpb, h.2.tpb⟩
  · have T2 := twTimes (w0 := w0) (live := twL) (liveW := [wT, wX3]) pg hb hb32 twC_dbl
      fun g' s0 A AW V s h =>
        WP.mono (h.add_W (o := wT) (a := wT) (b := wT) (by decide) (by simp) (by simp) (by decide))
          fun _ ⟨hv, _⟩ => ⟨A, _, hv.mono (fun _ hj => ⟨hj, rfl⟩) (fun _ hj => ⟨List.mem_cons_of_mem _ hj, rfl⟩)
            (fun _ hd => ⟨hd, rfl⟩)⟩
    have LCx := twLeaf (Q := TMB w0 (2 ^ j) (aTmp :: twL) [wX3]) (ds := []) pg (fun _ => 0) (by simp) (by simp)
      (fun _ _ h => twCopy_step (src := aX2) (by simp) (by decide) h) twC_cx
    have LSx := twLeaf (Q := TMB w0 (2 ^ j) twL [wX3]) (ds := []) pg (fun _ => 0) (by simp) (by simp)
      (fun _ _ h => twSel_step (o := aX2) (by simp) (by decide) (by decide) h) twC_sx
    have LCw := twLeaf (Q := TMB w0 (2 ^ j) twL [wT, wX3]) (ds := []) pg (fun _ => 0) (by simp) (by simp)
      (fun _ _ h => twCopyW_step h) twC_cw
    have LSw := twLeaf (Q := TMB w0 (2 ^ j) twL [wX3]) (ds := []) pg (fun _ => 0) (by simp) (by simp)
      (fun _ _ h => twSelW_step h) twC_sw
    rw [show stageBH true = .seq (twLow true) (.seq lowTest (.seq (.block flagZero)
      (.seq (.seq (copy nar aTmp aU) (timesH (.seq (.block [.mov .ebx (.imm 0)]) (half nar aTmp))))
        (.seq (sel nar aU aU aTmp sStg)
          (.seq (.seq (copy nar aTmp aX2) (timesH (.seq (.block [.mov .ebx (.imm 0)]) (half nar aTmp))))
            (.seq (sel nar aX2 aX2 aTmp sStg)
              (.seq (.seq (copy wid wT wX3) (timesH (chain wid .adc wT wT wT false)))
                (sel wid wX3 wX3 wT sStg)))))))) from rfl]
    refine VG.RelCT.assoc (VG.RelCT.assoc ?_)
    refine VG.RelCT.seq (L0 true twC_b0t) (VG.RelCT.seq (VG.RelCT.seq LCu T1) (VG.RelCT.seq LSu
      (VG.RelCT.seq (VG.RelCT.seq LCx T1) (VG.RelCT.seq LSx (VG.RelCT.seq (VG.RelCT.seq LCw T2) ?_)))))
    exact LSw.mono (fun _ _ h => h) fun _ _ h => ⟨h.1.tpb, h.2.tpb⟩

/-- A phase's word stages, related. -/
theorem twWords (joint : Bool) {g : Geo} (pg : PubG g) :
    RelCT isa (Both (TS0 g.w g)) (wordStagesL (2 ^ 7) (bytesB nar .eax) (stageWH joint)) (Both (TS0 g.w g)) :=
  relWordStagesL (k := 7) (lim := 4 * g.w) (S := TS0 g.w) (Fin := TS0 g.w) (fun g' j => TPW g.w j g') (fun g' j => TPW g.w j g') (by decide)
    (fun _ h => h.p0 pg) (fun _ _ h => h.p0 pg) (fun _ _ h => h.p0 pg) (fun _ h => h.onView)
    (fun _ _ h => h.onView) (fun _ _ h => h.onView)
    (fun _ _ ⟨⟨_, _, _, _, h, _⟩, _⟩ => h.ws)
    (fun _ _ _ ⟨⟨s0, A, AW, _, h, _⟩, hw⟩ k e r =>
      ⟨⟨s0, A, AW, _, h.slot1 k (by decide) (r.mono (by decide)) e, upd_self ..⟩, hw⟩)
    (fun _ _ _ _ ⟨⟨_, _, _, _, h, f⟩, _⟩ => ⟨h.ws, by rw [h.sl sC4 (by simp), f]⟩)
    (fun _ _ _ _ ⟨⟨_, _, _, _, h, _⟩, hw⟩ _ _ k =>
      VG.Proof.Rsa.X86.KeyRt.bytesB_ok (VG.Proof.Rsa.X86.KeyRt.lenSrc h.rt) h.rt.lenLe
        fun u K m e => k u (K.mono (by decide)) m (by rw [e, kw_nar]; exact congrArg (4 * ·) hw))
    (fun _ _ _ _ _ ⟨⟨s0, A, AW, V, h, f⟩, hw⟩ r m => ⟨⟨s0, A, AW, V, h.of_rest r (fun _ hx => hx) m, f⟩, hw⟩)
    (fun _ _ _ _ h _ => h)
    (fun _ _ _ _ ⟨⟨_, _, _, _, h, f⟩, _⟩ => ⟨h.ws, by rw [h.sl sC4 (by simp), f]⟩)
    (fun _ j _ _ _ ⟨⟨s0, A, AW, _, h, _⟩, hw⟩ k e r =>
      ⟨fun hj => ⟨⟨s0, A, AW, _, h.setSlot k (by decide) r e, (upd_self ..).trans (by
          have := pow_pred hj; omega)⟩, hw⟩,
        fun _ => ⟨⟨s0, A, AW, _, (h.setSlot k (by decide) r e).mono (fun _ hj => ⟨hj, rfl⟩)
          (fun _ hj => ⟨hj, rfl⟩) (fun _ hd => ⟨memOf (by decide) hd, rfl⟩), trivial⟩, hw⟩⟩)
    (fun j _ hl => twWordBody (w0 := g.w) (j := j) joint pg (by omega))
    twC_c4i twC_lim twC_c4h

/-- A phase's bit stages, related. -/
theorem twBits (joint : Bool) {g : Geo} (pg : PubG g) :
    RelCT isa (Both (TS0 g.w g)) (bitStagesL (2 ^ 4) (2 ^ 0) (stageBH joint)) (Both (TS0 g.w g)) :=
  relBitStagesL (k := 4) (m := 0) (S := TS0 g.w) (Fin := TS0 g.w) (fun g' j => TPB g.w j g') (fun g' j => TPB g.w j g') (by decide) (by decide)
    (fun _ h => h.p0 pg) (fun _ _ h => h.p0 pg) (fun _ h => h.onView) (fun _ _ h => h.onView)
    (fun _ _ ⟨⟨_, _, _, _, h, _⟩, _⟩ => h.ws)
    (fun _ _ _ ⟨⟨s0, A, AW, _, h, _⟩, hw⟩ k e r =>
      ⟨⟨s0, A, AW, _, h.slot1 k (by decide) (r.mono (by decide)) e, upd_self ..⟩, hw⟩)
    (fun _ _ _ _ _ ⟨⟨_, _, _, _, h, f⟩, _⟩ => ⟨h.ws, by rw [h.sl sB (by simp), f]⟩)
    (fun _ j _ _ _ _ ⟨⟨s0, A, AW, _, h, _⟩, hw⟩ k e r =>
      ⟨fun hj => ⟨⟨s0, A, AW, _, h.setSlot k (by decide) r e, (upd_self ..).trans (by
          rw [pow_pred hj, Nat.mul_div_cancel_left _ (by decide)])⟩, hw⟩,
        fun _ => ⟨⟨s0, A, AW, _, (h.setSlot k (by decide) r e).mono (fun _ hj => ⟨hj, rfl⟩)
          (fun _ hj => ⟨hj, rfl⟩) (fun _ hd => ⟨memOf (by decide) hd, rfl⟩), trivial⟩, hw⟩⟩)
    (fun j _ hj => twBitBody (w0 := g.w) (j := j) joint pg (by
      have := Nat.pow_le_pow_right (n := 2) (by decide) hj; simp at this; omega))
    twC_bi twC_bh

theorem twos_split : twos = .seq twosInit (.seq (wordStagesL (2 ^ 7) (bytesB nar .eax) (stageWH true))
    (.seq (bitStagesL (2 ^ 4) (2 ^ 0) (stageBH true)) (.seq (wordStagesL (2 ^ 7) (bytesB nar .eax) (stageWH false))
      (bitStagesL (2 ^ 4) (2 ^ 0) (stageBH false))))) :=
  rfl

/-- The halvings, related: the stages' sizes only. -/
theorem twos_rel {g : Geo} (pg : PubG g) {n : Nat} (three : 3 ≤ n) :
    RelCT isa (Both (TW0 g n)) twos (Both (TS0 g.w g)) := by
  rw [twos_split]
  refine VG.RelCT.seq ?_ (VG.RelCT.seq (twWords true pg) (VG.RelCT.seq (twBits true pg)
    (VG.RelCT.seq (twWords false pg) (twBits false pg))))
  exact (leafSt (live := [aZ0, aX2, VG.Impl.Rsa.X86.RecoverDetRt.aN]) (liveW := [wX]) (ls := [sOkDE])
    (F := fun A _ _ => A aZ0 = 0 ∧ A VG.Impl.Rsa.X86.RecoverDetRt.aN = n) (Q := fun g' => TS0 g'.w g')
    (ds := []) pg (fun _ => 0) (by simp) (by simp) (fun _ _ h => twInit_step three h) twC_init).mono
    (fun _ _ h => h) fun _ _ h => h

theorem twos_tw1 {g : Geo} {n : Nat} {s : State} (three : 3 ≤ n) (small : n < 2 ^ (32 * g.w))
    (t13 : VG.Proof.Bignum.ShiftStages.tz (n - 1) < 2 ^ 13) (hs : TW0 g n s) : WP isa twos s (TW1 g n) := by
  obtain ⟨s0, A, AW, V, h, z, hn⟩ := hs
  exact WP.mono (twos_ok h z hn rfl rfl three small t13) fun _ ⟨A', AW', V', h', eU, _, _, eN, _⟩ =>
    ⟨s0, A', AW', V', h', by rw [eU]; exact (VG.Proof.Bignum.ShiftStages.tz_spec _ (by omega)).2, eN⟩

theorem twos_relCT {g : Geo} (pg : PubG g) (n : Nat) (three : 3 ≤ n) (small : n < 2 ^ (32 * g.w))
    (t13 : VG.Proof.Bignum.ShiftStages.tz (n - 1) < 2 ^ 13) :
    RelCT isa (RA (TW0 g n) (TW0 g n)) VG.Impl.Rsa.X86.RecoverDetRt.twos (RA (TW1 g n) (TW1 g n)) :=
  (VG.RelCT.wp (F₁ := TW1 g n) (F₂ := TW1 g n) (twos_rel pg three)
    fun _ _ ⟨hs, ht⟩ => ⟨twos_tw1 three small t13 hs, twos_tw1 three small t13 ht⟩).mono
    (fun _ _ h => ⟨h.2.1, h.2.2⟩)
    fun _ _ h => RA.of pg (fun _ h => let ⟨_, _, _, _, k, _⟩ := h; ⟨_, _, _, _, _, _, _, k⟩) h.2.1 h.2.2

end VG.Proof.Rsa.X86.Recover
