module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.Data
public import VerifiedGarbage.Impl.RsaKeyGen.AArch64.Search
import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Init
import VerifiedGarbage.Proof.Bignum.AArch64.PubFail
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! # The RSA prime search's writes of its own words, and zeros at `out` (AArch64)

The terminal statuses and the exit for an exhausted search
(`search_exhausted`); the zeroing of `out`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Search

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh.AArch64 (Slots)
open VG.Proof.Ffdh.Control (writeController controllerValue controllerValue_unchanged)
open VG.Proof.Ffdh.AArch64.Generation (imm64)
open VG.Impl.RsaKeyGen.AArch64.Search
open VG.Spec.RsaKeyGen (primeEntropy PrimeSearchResult)
open VG.Impl.Bignum.AArch64 (movi)

namespace SInput

variable {p : SPub} {original : State}

theorem out_mem (h : SInput p original) : (⟨p.op, p.len⟩ : Region) ∈ inWrites original := by
  rw [← h.out_eq]; simp [inWrites]

theorem len_bounds (h : SInput p original) : 32 ≤ p.len ∧ p.len ≤ 512 := by
  rw [← h.2]; have := h.1.2.2.2.2.2.2.2.2.1; unfold Spec.RsaKeyGen.primeLenValid at this
  exact ⟨this.1, this.2.1⟩

theorem out_frame (h : SInput p original) : (⟨p.op, p.len⟩ : Region).Disjoint p.frame := by
  have hd := h.frame_disjoint (r := inOut original) (by simp [SInput.callChanges])
  rw [h.out_eq] at hd
  exact hd.symm

end SInput

/-- The search's word-only writes keep `out`. -/
theorem out_frame {p : SPub} {original : State} (hi : SInput p original) {m m' : Mem}
    (hf : Frame [p.frame] m m') :
    Spec.Rsa.bytesAt m' p.op p.len = Spec.Rsa.bytesAt m p.op p.len := by
  have hk := hi.len_bounds
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi' => ?_
  exact hf.bytes (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hi.out_frame)
    (show p.len ≤ 2 ^ 64 by omega) (List.mem_range.mp hi')

/-- A finished search from a loop state whose words agree. -/
theorem SLive.done {p : SPub} {original s : State} {used k : Nat} {result : PrimeSearchResult}
    (h : SLive p original used k s)
    (h0 : word s.mem p.F (8 * 0) = BitVec.ofNat 64 result.remaining)
    (h3 : word s.mem p.F (8 * 3) = BitVec.ofNat 64 result.requested)
    (h12 : word s.mem p.F (8 * 12) = BitVec.ofNat 64 result.used)
    (h14 : word s.mem p.F (8 * 14) = BitVec.ofNat 64 result.status)
    (hout : Spec.Rsa.bytesAt s.mem p.op p.len =
      match result.outcome with
      | .accepted c => Spec.Rsa.i2osp c p.len
      | _ => List.replicate p.len 0) :
    SDone p original result s :=
  ⟨h.input, h.rd, h.wr, h.x19, h.saved, h.vcs, h.savedX19,
    h.header (by simp [SPub.headers]), h.header (by simp [SPub.headers]),
    h.header (by simp [SPub.headers]), h.header (by simp [SPub.headers]),
    h0, h3, h12, h14, hout⟩

/-! ## Terminal statuses -/

def terminalValues (status : Nat) : List (Nat × BitVec 64) :=
  [(0, 0), (3, 0), (14, BitVec.ofNat 64 status)]

theorem terminalValues_bound (status : Nat) : ∀ e ∈ terminalValues status, e.1 < 20 := by
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

/-- A terminal status written over a loop state, with no counted candidates left. -/
theorem terminal_live {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) {status : Nat} (hst : status = 1 ∨ status = 3) :
    WP isa (.block (terminal status)) s fun t =>
      SLive p original used 0 t ∧ t.mem = writeController s.mem p.F (terminalValues status) := by
  refine WP.mono (terminal_ok h.access h.x19 hst) fun t ⟨hm, k⟩ => ?_
  have hh : Slots t.mem p.F (p.headers used 0) := by
    refine headers_after _ (terminalValues_bound status) hm ?_
    intro e he
    simp only [SPub.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [controllerValue, terminalValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
        ite_true, ite_false] <;>
      first | rfl | exact h.header (by simp [SPub.headers])
  refine ⟨h.update (u := used) (k' := 0) h.used_le (Nat.zero_le _) _
    (terminalValues_bound status) (by
      simp only [terminalValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide) hm k.mono hh, hm⟩

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
      (∀ j < 20, word t.mem p.F (8 * j) = word s.mem p.F (8 * j)) := by
  have hk := h.input.len_bounds
  have a := h.access
  have hv := h.header (j := 5) (v := p.op) (by simp [SPub.headers])
  have hv6 := h.header (j := 6) (v := BitVec.ofNat 64 p.len) (by simp [SPub.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv hv6
  have hout : ∀ i < p.len, InRegions s.wr (p.op + BitVec.ofNat 64 i) 1 := fun i hi =>
    ⟨⟨p.op, p.len⟩, by rw [h.wr, h.input.1.2.2.2.1]; exact List.mem_cons_of_mem _ h.input.out_mem,
      Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, hk])⟩
  unfold zeroOut
  refine WP.seq (WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun t => t.gpr .x1 = p.op + BitVec.ofNat 64 0 ∧
      t.gpr .x2 = BitVec.ofNat 64 p.len ∧ t.gpr .x3 = 0 ∧ t.mem = s.mem) (by
    brun [ldf, h.x19, imm64 (show 0 < 65536 by decide), a.ld 40 (by decide), a.ld 48 (by decide), hv, hv6])
      (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨⟨h1, h2, h3, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (wp_countdown (N := p.len) (by omega) (by omega) (BInv s₁ p.op)
    (fun i hi t hI _ => bStep_ok (by omega) h3 (fun i hi => by rw [k₁.wr]; exact hout i hi) hi hI)
    ⟨Keep.refl _ _, h1, fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ => rfl⟩ h2) fun t hI => ?_
  have hf : ∀ x, (∀ i < p.len, x ≠ p.op + BitVec.ofNat 64 i) → t.mem x = s.mem x :=
    fun x hx => by rw [hI.frame x hx, hm₁]
  have kk := k₁.trans hI.keep
  have hfr := zero_frame h.input hf
  refine ⟨h.restore kk.rd kk.wr kk.sp (fun r hr _ => kk.gpr r (by revert r hr; decide)) kk.vcs hfr, ?_,
    fun j hj => h.input.frame_words hfr j hj⟩
  refine List.eq_replicate_iff.mpr ⟨by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range], ?_⟩
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  exact hI.bytes i (List.mem_range.mp hi)

theorem search_exhausted {p : SPub} {original s : State} {used k : Nat}
    {result : PrimeSearchResult} (h : SLive p original used k s)
    (hr : result = ⟨.exhausted, used, result.trace⟩) :
    WP isa exhausted s (SDone p original result) := by
  unfold exhausted
  refine WP.seq (WP.mono (terminal_live h (status := 3) (.inr rfl)) fun t ⟨ht, hm⟩ => ?_)
  refine WP.mono (search_zero_out ht) fun u ⟨hu, hz, hc⟩ => ?_
  have hb := terminalValues_bound 3
  have hw (j : Nat) (hj : j < 20) : word u.mem p.F (8 * j) =
      controllerValue (terminalValues 3) j (word s.mem p.F (8 * j)) := by
    rw [hc j hj, hm, frame_word _ _ _ hb j hj]
  rw [hr]
  refine hu.done ?_ ?_ ?_ ?_ (by simpa only using hz)
  · rw [hw 0 (by decide)]; rfl
  · rw [hw 3 (by decide)]; rfl
  · rw [hw 12 (by decide)]; exact h.header (by simp [SPub.headers])
  · rw [hw 14 (by decide)]; rfl

end VG.Proof.RsaKeyGen.AArch64.Search
