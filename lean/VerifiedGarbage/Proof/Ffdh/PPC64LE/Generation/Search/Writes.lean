module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Live
public import VerifiedGarbage.Impl.Ffdh.PPC64LE.Generation.Search
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset

/-! # The parameter search's writes of its own words, and zeros at `out` (PPC64LE)

The terminal statuses and the exit for an exhausted bound
(`search_exhausted`); the zeroing of `out`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Generation

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE VG.Spec.Ffdh
open VG.Proof.Ffdh.Control (writeController writeController_word writeController_frame
  controllerValue controllerValue_unchanged)
open VG.Impl.Ffdh.PPC64LE.Generation.Search
open VG.Impl.Bignum.PPC64LE (countLoop)

private theorem not_self_disjoint {r : Region} (h : r.Disjoint r) (hl : 0 < r.len) : False :=
  h r.base (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)
    (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)

namespace SInput

variable {p : SPub} {original : State}

theorem out_mem (h : SInput p original) : (⟨p.op, p.len⟩ : Region) ∈ inWrites original := by
  rw [← h.out_eq]; simp [inWrites]

theorem out_ctl (h : SInput p original) : (⟨p.op, p.len⟩ : Region).Disjoint ⟨p.control, 128⟩ := by
  have := h.writes_pairwise
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at this
  rw [← h.out_eq, ← h.ctl_eq]
  exact this.1.2.2

theorem out_ne_ctl (h : SInput p original) : (⟨p.op, p.len⟩ : Region) ≠ inCtl original := by
  intro he
  have d := h.out_ctl
  rw [he, h.ctl_eq] at d
  exact not_self_disjoint d (by show 0 < 128; decide)

end SInput

/-- The controller's word-only writes keep `out`. -/
theorem out_frame {p : SPub} {original : State} (hi : SInput p original) {m m' : Mem}
    (hf : Frame [⟨p.control, 128⟩] m m') :
    Spec.Rsa.bytesAt m' p.op p.len = Spec.Rsa.bytesAt m p.op p.len := by
  have hk := hi.len_bounds
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi' => ?_
  exact hf.bytes (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hi.out_ctl)
    (show p.len ≤ 2 ^ 64 by omega) (List.mem_range.mp hi')

/-! ## Terminal statuses -/

def terminalValues (status : Nat) : List (Nat × BitVec 64) :=
  [(0, 0), (3, 0), (14, BitVec.ofNat 64 status)]

theorem terminalValues_bound (status : Nat) : ∀ e ∈ terminalValues status, e.1 < 16 := by
  simp only [terminalValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide

theorem terminal_ok {s : State} {B : Addr} (a : CtlAccess s B) (hb : s.gpr .r31 = B)
    {status : Nat} (hst : status = 1 ∨ status = 3) :
    WP isa (.block (terminal status)) s fun t =>
      t.mem = writeController s.mem B (terminalValues status) ∧ Keep [.r10, .r11] s t := by
  rcases hst with rfl | rfl <;>
  refine WP.keep [.r10, .r11] ?_ (by decide) <;>
  unfold terminal writeController terminalValues <;>
  simp only [List.foldl_cons, List.foldl_nil]
  all_goals
    prun [ldf, stf, hb, a.st0, a.st 0 (by decide), a.st 24 (by decide), a.st 112 (by decide), BitVec.add_zero]
    rfl

/-- A terminal status written over a loop state, with no attempts left. -/
theorem terminal_live {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) {status : Nat} (hst : status = 1 ∨ status = 3) :
    WP isa (.block (terminal status)) s fun t =>
      SLive p original used 0 t ∧ t.mem = writeController s.mem p.control (terminalValues status) := by
  refine WP.mono (terminal_ok h.access h.r31 hst) fun t ⟨hm, k⟩ => ?_
  have hh : Slots t.mem p.control (p.headers used 0) := by
    refine headers_after _ (terminalValues_bound status) hm ?_
    intro e he
    simp only [SPub.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [controllerValue, terminalValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
        ite_true, ite_false] <;>
      first | rfl | exact h.header (by simp [SPub.headers])
  refine ⟨h.update (u := used) (k' := 0) h.used_le (Nat.zero_le _) _
    (terminalValues_bound status) (by
      simp only [terminalValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide) hm k.mono hh, hm⟩

/-- The words of a terminal status written over a loop state. -/
theorem terminal_words {p : SPub} {original s t : State} {used k : Nat}
    (h : SLive p original used k s) {status : Nat}
    (hm : (j : Nat) → j < 16 → word t.mem p.control (8 * j) =
      controllerValue (terminalValues status) j (word s.mem p.control (8 * j))) :
    word t.mem p.control 112 = BitVec.ofNat 64 status ∧
      Spec.Rsa.wordsAt t.mem p.control 4 = [0, BitVec.ofNat 64 p.len,
        BitVec.ofNat 64 (parameterEntropy p.bits), 0] := by
  refine ⟨?_, ?_⟩
  · rw [show (112 : Nat) = 8 * 14 from rfl, hm 14 (by decide)]
    simp only [controllerValue, terminalValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
      ite_true, ite_false]
  · change [word t.mem p.control (8 * 0), word t.mem p.control (8 * 1), word t.mem p.control (8 * 2),
      word t.mem p.control (8 * 3)] = _
    rw [hm 0 (by decide), hm 1 (by decide), hm 2 (by decide), hm 3 (by decide)]
    simp only [controllerValue, terminalValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
      ite_true, ite_false]
    rw [h.header (j := 1) (v := BitVec.ofNat 64 p.len) (by simp [SPub.headers]),
      h.header (j := 2) (v := BitVec.ofNat 64 (parameterEntropy p.bits)) (by simp [SPub.headers])]

/-! ## Zeros at `out` -/

/-- A zeroing of `out` changes memory only there. -/
theorem zero_frame {p : SPub} {original : State} (hinput : SInput p original) {m m' : Mem}
    (hf : ∀ x, (∀ j < p.len, x ≠ p.op + BitVec.ofNat 64 j) → m' x = m x) :
    Frame (SInput.callChanges original) m m' := by
  intro a ha
  apply hf
  intro i hi he
  have hk := hinput.len_bounds
  have hin : (⟨p.op, p.len⟩ : Region) ∈ SInput.callChanges original := by
    rw [← hinput.out_eq]; simp [SInput.callChanges]
  apply ha _ hin
  rw [he]
  exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, hk])

/-- `out_len` zeros at `out`, from its address in `r3`, its length in `r4`,
and zero in `r5`. -/
theorem zeroLoop_ok {s : State} {O : Addr} {k : Nat} (ho : ∀ i < k, InRegions s.wr (off O i) 1)
    (hk : 1 ≤ k) (hk' : k < 2 ^ 63)
    (h3 : s.gpr .r3 = O) (h4 : s.gpr .r4 = BitVec.ofNat 64 k) (h5 : s.gpr .r5 = BitVec.ofNat 64 0) :
    WP isa (countLoop .r4 [.stb .r5 .r3 0, .addi .r3 .r3 1]) s fun t =>
      ((∀ i < k, t.mem (off O i) = 0) ∧ Outside O 0 k s.mem t.mem) ∧ Keep [.r3, .r4, .r5] s t := by
  let Inv : Nat → State → Prop := fun j t =>
    t.gpr .r3 = off O j ∧ t.gpr .r5 = BitVec.ofNat 64 0 ∧ Outside O 0 j s.mem t.mem ∧
      (∀ i < j, t.mem (off O i) = 0) ∧ Keep [.r3, .r4, .r5] s t
  refine WP.mono (wp_countdown (body := .block ([.stb .r5 .r3 0, .addi .r3 .r3 1] ++
      ([.subi .r4 .r4 1] : List Instr)))
    (cnt := .r4) (N := k) (by omega) (by omega) Inv (fun j hj t ⟨t3, t5, tout, tb, tk⟩ hc => ?_)
    ⟨by rw [h3]; simp [off], h5, Outside.refl _ _ _ _, fun _ h => absurd h (by omega),
      Keep.refl _ _⟩ h4) fun t ⟨_, _, tout, tb, tk⟩ => ⟨⟨tb, tout⟩, tk⟩
  have hst : WP isa (.block [.stb .r5 .r3 0, .addi .r3 .r3 1, .subi .r4 .r4 1]) t fun t' =>
      t' = (({ t with mem := t.mem.write (off O j) 1 ((BitVec.ofNat 64 0).setWidth 8) } :
          State).write .r3 (off O (j + 1))).write .r4 (t.gpr .r4 - BitVec.ofNat 64 1) := by
    have hs : InRegions t.wr (off O j) 1 := by rw [tk.wr]; exact ho j hj
    prun [t3, t5, exec_stb (show Reg.r3 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide), hs]
  refine WP.mono hst fun t' e => ?_
  subst e
  have hw1 := write1_outside t.mem O (d := j) ((BitVec.ofNat 64 0).setWidth 8) (by omega)
  refine ⟨⟨by gsimp, by gsimp; exact t5, ?_, ?_, ?_⟩, by gsimp⟩
  · gsimp; exact (tout.mono (Nat.le_refl _) (by omega)).trans (hw1.mono (by omega) (by omega))
  · intro i hi
    gsimp
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [hw1 _ (by rw [ofs_off0 O (by omega)]; omega)]; exact tb i hi
    · rw [write1_self]; rfl
  · exact tk.trans' (((Keep.mem _ _).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono

theorem search_zero_out {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) :
    WP isa zeroOut s fun t =>
      SLive p original used k t ∧ Spec.Rsa.bytesAt t.mem p.op p.len = List.replicate p.len 0 ∧
      (∀ j < 16, word t.mem p.control (8 * j) = word s.mem p.control (8 * j)) := by
  have hk := h.input.len_bounds
  have scr := h.input.control_scr (t := s) h.wr
  have hv := h.header (j := 5) (v := p.op) (by simp [SPub.headers])
  have hv6 := h.header (j := 6) (v := BitVec.ofNat 64 p.len) (by simp [SPub.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv hv6
  have hl : InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 40) 8 := scr.ld (by decide)
  have hl6 : InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 48) 8 := scr.ld (by decide)
  have hno : p.op.toNat + p.len ≤ 2 ^ 64 := by
    have := h.input.nowrap (r := inOut original) (by simp [inWrites])
    rw [h.input.out_eq] at this; exact this
  have hout : ∀ i < p.len, InRegions s.wr (off p.op i) 1 := fun i hi =>
    ⟨⟨p.op, p.len⟩, by rw [h.wr, h.input.1.2.2.2.1]; exact h.input.out_mem,
      Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, hk])⟩
  unfold zeroOut
  refine WP.seq (WP.mono (WP.keep [.r3, .r4, .r5] (Q := fun t => t.gpr .r3 = p.op ∧
      t.gpr .r4 = BitVec.ofNat 64 p.len ∧ t.gpr .r5 = BitVec.ofNat 64 0 ∧ t.mem = s.mem) (by
    prun [ldf, h.r31, hl, hl6, hv, hv6]) (by decide)) fun s₁ ⟨⟨h3, h4, h5, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (zeroLoop_ok (fun i hi => by rw [k₁.wr]; exact hout i hi) (by omega) (by omega) h3 h4 h5)
    fun t ⟨⟨tb, tout⟩, kt⟩ => ?_
  have hf : ∀ x, (∀ i < p.len, x ≠ p.op + BitVec.ofNat 64 i) → t.mem x = s.mem x := by
    intro x hx
    rw [tout x (Or.inr ?_), hm₁]
    by_contra hc
    exact hx (x - p.op).toNat (by simp only [ofs] at hc; omega)
      (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel])
  have kk := k₁.trans kt
  have hfr := zero_frame h.input hf
  refine ⟨h.restore kk.rd kk.wr kk.sp (fun r hr => kk.gpr r (by revert r hr; decide)) hfr, ?_,
    fun j hj => h.input.control_frame hfr j hj⟩
  refine List.eq_replicate_iff.mpr ⟨by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range], ?_⟩
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  exact tb i (List.mem_range.mp hi)

theorem search_exhausted {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) :
    WP isa exhausted s (SDone p original (.exhausted used)) := by
  unfold exhausted
  refine WP.seq (WP.mono (terminal_live h (status := 3) (.inr rfl)) fun t ⟨ht, hm⟩ => ?_)
  refine WP.mono (search_zero_out ht) fun u ⟨hu, hz, hc⟩ => ?_
  have hw (j : Nat) (hj : j < 16) : word u.mem p.control (8 * j) =
      controllerValue (terminalValues 3) j (word s.mem p.control (8 * j)) := by
    rw [hc j hj, hm, writeController_word _ _ _ (terminalValues_bound 3) j hj]
  obtain ⟨hs, hp⟩ := terminal_words h hw
  exact hu.done rfl hs hp hz

end VG.Proof.Ffdh.PPC64LE.Generation
