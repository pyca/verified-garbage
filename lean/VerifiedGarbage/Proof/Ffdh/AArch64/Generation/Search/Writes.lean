module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Search.Live
public import VerifiedGarbage.Impl.Ffdh.AArch64.Generation.Search
import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Init
import VerifiedGarbage.Proof.Bignum.AArch64.PubFail
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! # The parameter search's writes of its own words, and zeros at `out` (AArch64)

The terminal statuses and the exit for an exhausted bound
(`search_exhausted`); the zeroing of `out`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Generation

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Spec.Ffdh
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh.AArch64 (Slots)
open VG.Proof.Ffdh.Control (writeController writeController_word writeController_frame
  controllerValue controllerValue_unchanged)
open VG.Impl.Ffdh.AArch64.Generation.Search
open VG.Impl.Bignum.AArch64 (movi)

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

theorem terminal_ok {s : State} {B : Addr} (a : CtlAccess s B) (hb : s.gpr .x19 = B)
    {status : Nat} (hst : status = 1 ∨ status = 3) :
    WP isa (.block (terminal status)) s fun t =>
      t.mem = writeController s.mem B (terminalValues status) ∧ Keep [.x10, .x11] s t := by
  rcases hst with rfl | rfl <;>
  refine WP.keep [.x10, .x11] ?_ (by decide) (by decide) (by decide +kernel) <;>
  unfold terminal writeController terminalValues <;>
  simp only [List.foldl_cons, List.foldl_nil]
  all_goals
    brun [ldf, stf, hb, imm64 (show 0 < 65536 by decide), imm64 (show 1 < 65536 by decide),
      imm64 (show 3 < 65536 by decide), a.st0, a.st 0 (by decide), a.st 24 (by decide),
      a.st 112 (by decide)]
    rfl

/-- A terminal status written over a loop state, with no attempts left. -/
theorem terminal_live {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) {status : Nat} (hst : status = 1 ∨ status = 3) :
    WP isa (.block (terminal status)) s fun t =>
      SLive p original used 0 t ∧ t.mem = writeController s.mem p.control (terminalValues status) := by
  refine WP.mono (terminal_ok h.access h.x19 hst) fun t ⟨hm, k⟩ => ?_
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
  have hout : ∀ i < p.len, InRegions s.wr (p.op + BitVec.ofNat 64 i) 1 := fun i hi =>
    ⟨⟨p.op, p.len⟩, by rw [h.wr, h.input.1.2.2.2.1]; exact h.input.out_mem,
      Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, hk])⟩
  unfold zeroOut
  refine WP.seq (WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun t => t.gpr .x1 = p.op + BitVec.ofNat 64 0 ∧
      t.gpr .x2 = BitVec.ofNat 64 p.len ∧ t.gpr .x3 = 0 ∧ t.mem = s.mem) (by
    brun [ldf, h.x19, imm64 (show 0 < 65536 by decide), hl, hl6, hv, hv6]) (by decide) (by decide)
      (by decide +kernel)) fun s₁ ⟨⟨h1, h2, h3, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (wp_countdown (N := p.len) (by omega) (by omega) (BInv s₁ p.op)
    (fun i hi t hI _ => bStep_ok (by omega) h3 (fun i hi => by rw [k₁.wr]; exact hout i hi) hi hI)
    ⟨Keep.refl _ _, h1, fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ => rfl⟩ h2) fun t hI => ?_
  have hf : ∀ x, (∀ i < p.len, x ≠ p.op + BitVec.ofNat 64 i) → t.mem x = s.mem x :=
    fun x hx => by rw [hI.frame x hx, hm₁]
  have kk := k₁.trans hI.keep
  have hfr := zero_frame h.input hf
  refine ⟨h.restore kk.rd kk.wr kk.sp (fun r hr _ => kk.gpr r (by revert r hr; decide)) kk.vcs hfr, ?_,
    fun j hj => h.input.control_frame hfr j hj⟩
  refine List.eq_replicate_iff.mpr ⟨by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range], ?_⟩
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  exact hI.bytes i (List.mem_range.mp hi)

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

end VG.Proof.Ffdh.AArch64.Generation
