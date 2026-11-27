module

public import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Sieved
public import VerifiedGarbage.Proof.Ffdh.RISCV64.ParameterCandidate.Base
public import VerifiedGarbage.Proof.Ffdh.RISCV64.ParameterCandidate.Shape
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Backend
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.CTBase
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.RoundCall
public import VerifiedGarbage.Proof.RsaKeyGen.MrWindow
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCore
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Ffdh.MillerRabin
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.WitnessStreamStep
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.WordCut
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.Loop
import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.Witness
import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.MontPrep
import VerifiedGarbage.Proof.MillerRabin.RISCV64.Verified
import VerifiedGarbage.Proof.Mont.RangeCover
import VerifiedGarbage.Proof.RsaKeyGen.WitnessBits
meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run

-- separate module: the tests, whose symbolic executions the constant-time proof need not re-check

/-!
# An FFDH parameter candidate on RISC-V: the tests

The tests of p and q, over the prime search's prepared working space
(`Prep`) and its round's call (`roundCall_ok`,
`Proof/MillerRabin/RISCV64/Search/RoundCall.lean`):

* `MSt`: between the witnesses of a modulus `N` of `mb` bits, `St`, the
  modulus's header (`Ph`) and `Prep`. `MSt.frm`: it survives a change of
  `Free` ranges; `MSt.round`: and the round (`roundCount_ok`).
* `draw_ok`: a witness's octets from the tape, its cut, its range
  (`atLeast2_ok`, `ltN_ok`) and its round.

## The witnesses and the results

`millerRabin_ok`, witnesses drawn while `hStat` is 4, against
`checkWitnesses`, for a count of witnesses `C` in `hChecks`; `montPrep_mst`,
a modulus's Montgomery constants; `testQ_ok`, the test of q (halved in place
from p, `halveQ_from`); `testP1_ok` and `testPR_ok`, the tests of p's first
witness (`firstCheck`) and of its others (`restChecks`), p loaded again;
`pResult_ok` and `qResult_ok`, their results; `tests_ok`, against
`sievedTests`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.ParameterCandidate

variable {C : Nat}

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Ffdh.RISCV64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.RISCV64
open VG.RISCV64.Steps (eval_zero eval_zero_ofNat)
open VG.Impl.MillerRabin.RISCV64 VG.Impl.MillerRabin.RISCV64.Search
open VG.Proof.MillerRabin.RISCV64 (A RoundImpl)
open VG.Proof.MillerRabin.RISCV64.Search (geFlag_ok Prep RcPost RcD RC Kept keeps_word roundCall_ok)
open VG.Proof.RsaKeyGen (mrE mrA)
open VG.Proof.Bignum.RISCV64.Pre (Two)

/-! ## The tests' state -/

structure MSt (p : PP) (mb N C : Nat) (s : State) : Prop where
  st : St p s
  ph : Ph p mb C s
  prep : Prep s p.B p.n (wOf mb) N
  mb1 : 511 ≤ mb
  mb2 : mb ≤ p.bits

/-- The words `Ph` and `Prep` read. -/
def Read (w d : Nat) : Prop :=
  d = 0 ∨ d = 48 ∨ d = 56 ∨ d = 168 ∨ d = 192 ∨ d = 216 ∨ d = 224 ∨ d = 248 ∨ (∃ j < 8, d = 8 * (8 + j)) ∨
    d = slot w 0 ∨ d = slot w 27 + 8 * w

theorem Read.arr {w j : Nat} (hj : j < 8) : Read w (8 * (8 + j)) := by
  unfold Read; right; right; right; right; right; right; right; right; left; exact ⟨j, hj, rfl⟩

theorem Ph.keep {p : PP} {mb : Nat} {s t : State} (h : Ph p mb C s)
    (r7 : t.gpr .a7 = s.gpr .a7) (r0 : t.gpr .t0 = s.gpr .t0) (r5 : t.gpr .s5 = s.gpr .s5)
    (hw : ∀ d, Read (wOf mb) d → word t.mem p.B d = word s.mem p.B d) : Ph p mb C t :=
  ⟨r7.trans h.a7, r0.trans h.t0, r5.trans h.s5, (hw 248 (by simp [Read])).trans h.mbW,
    (hw 216 (by simp [Read])).trans h.kW, (hw 48 (by simp [Read])).trans h.wW,
    (hw 224 (by simp [Read])).trans h.strideW,
    fun j hj => (hw _ (Read.arr hj)).trans (h.arrW j hj),
    (hw 168 (by simp [Read])).trans h.checksW, h.k1, h.k2, (hw 192 (by simp [Read])).trans h.topW⟩

/-- A range the draw or the round's bookkeeping changes: the header words
`hUsed`, `hStat`, `hIdx` and `hBad`, or arrays 2 to 6. -/
def Free (w : Nat) (r : Nat × Nat) : Prop :=
  ((r.1 = 152 ∨ r.1 = 160 ∨ r.1 = 176 ∨ r.1 = 200) ∧ r.2 = 8) ∨
    (∃ j, 2 ≤ j ∧ j ≤ 6 ∧ r.1 = slot w j ∧ r.2 ≤ 8 * (w + 2))

theorem Free.word {w d : Nat} {r : Nat × Nat} (h : Free w r) (hd : Read w d) :
    d + 8 ≤ r.1 ∨ r.1 + r.2 ≤ d := by
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  unfold Read at hd
  rcases h with ⟨h1, h2⟩ | ⟨j, hj1, hj2, h1, h2⟩
  · rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨k, hk, rfl⟩ | rfl | rfl <;>
      (try rw [es]) <;> omega_arith
  · rw [h1]
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨k, hk, rfl⟩ | rfl | rfl <;>
      simp only [es] <;> (try have := Nat.mul_le_mul_right (8 * (w + 2)) hj2) <;>
      (try have := Nat.mul_le_mul_right (8 * (w + 2)) hj1) <;> omega_arith

theorem Free.arr {w j : Nat} {r : Nat × Nat} (h : Free w r) (hj : j = 0 ∨ j = 1 ∨ j = 9 ∨ j = 10 ∨ j = 27) :
    slot w j + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w j := by
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  rcases h with ⟨h1, h2⟩ | ⟨k, hk1, hk2, h1, h2⟩
  · right; rcases hj with rfl | rfl | rfl | rfl | rfl <;> rw [es] <;> omega_arith
  · rw [h1]
    have a := Nat.mul_le_mul_right (8 * (w + 2)) hk2
    have b := Nat.mul_le_mul_right (8 * (w + 2)) hk1
    rcases hj with rfl | rfl | rfl | rfl | rfl <;> simp only [es] <;> omega_arith

theorem MSt.w {p : PP} {mb N : Nat} {s : State} (h : MSt p mb N C s) :
    2 ≤ wOf mb ∧ wOf mb ≤ 128 ∧ slot (wOf mb) 28 + saveBytes ≤ p.Z := by
  have hn := h.st.dims.n
  have hb := h.st.dims.b2
  have := h.mb1; have := h.mb2
  simp only [wOf, slot, hdrBytes, saveBytes, PP.Z, PP.L] at hn ⊢
  omega_arith

theorem Free.mut {p : PP} {mb N : Nat} {s : State} (h : MSt p mb N C s) {r : Nat × Nat} (hr : Free (wOf mb) r) :
    InMut p.n r := by
  obtain ⟨hw2, -, hZ⟩ := h.w
  have es : ∀ j, slot (wOf mb) j = 256 + j * (8 * (wOf mb + 2)) := fun _ => rfl
  rcases hr with ⟨h1, h2⟩ | ⟨j, hj1, hj2, h1, h2⟩
  · refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), ?_, ?_⟩ <;> dsimp only <;>
      omega_arith
  · refine InMut.arrays (by rw [h1, es]; omega_arith) ?_
    simp only [es, PP.Z] at hZ h1 ⊢
    have := Nat.mul_le_mul_right (8 * (wOf mb + 2)) hj2
    rw [h1]; omega_arith

theorem Read.le {w d : Nat} (hd : Read w d) : d + 8 ≤ slot w 28 := by
  have e0 : slot w 0 = 256 := by simp [slot, hdrBytes]
  have e27 : slot w 27 = 256 + 27 * (8 * (w + 2)) := rfl
  have e28 : slot w 28 = 256 + 28 * (8 * (w + 2)) := rfl
  unfold Read at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨k, hk, rfl⟩ | rfl | rfl <;> omega_arith

theorem MSt.frm {p : PP} {mb N : Nat} {s t : State} (h : MSt p mb N C s) {rs : List (Nat × Nat)}
    (hf : Frm p.B rs s.mem t.mem) (hr : ∀ r ∈ rs, Free (wOf mb) r) {regs : List Reg} (k : Keep regs s t)
    (hsp : t.sp = s.sp) (h6 : Reg.s6 ∉ regs) (r7 : t.gpr .a7 = s.gpr .a7) (r0 : t.gpr .t0 = s.gpr .t0)
    (r5 : t.gpr .s5 = s.gpr .s5) (r1 : t.gpr .t1 = s.gpr .t1) : MSt p mb N C t := by
  obtain ⟨hw2, hw128, hZ⟩ := h.w
  have hnw := h.st.scr.nowrap
  have es : ∀ j, slot (wOf mb) j = 256 + j * (8 * (wOf mb + 2)) := fun _ => rfl
  have hZ' : 256 + 28 * (8 * (wOf mb + 2)) + saveBytes ≤ p.Z := by rw [← es]; exact hZ
  have hw : ∀ d, Read (wOf mb) d → word t.mem p.B d = word s.mem p.B d := fun d hd =>
    hf.word_eq (fun r hr' => (hr r hr').word hd) (by have := hd.le; omega_arith)
  refine ⟨h.st.step (Frm.toMut hf fun r hr' => Free.mut h (hr r hr')) k hsp h6,
    h.ph.keep r7 r0 r5 hw, h.prep.keep ⟨h.prep.env.hs.congr k.2.2, r7.trans h.prep.env.a7, r5.trans h.prep.env.s5,
      r0.trans h.prep.env.t0, (k.gpr h6).trans h.prep.env.s6, h.prep.env.hw, h.prep.env.hw', h.prep.env.hZ⟩
      (h.prep.t1_of r1) (fun d hd => hw d ?_) (fun j hj => ?_), h.mb1, h.mb2⟩
  · rcases hd with rfl | rfl | rfl | rfl | ⟨j, hj, rfl⟩ | rfl | rfl
    case inr.inr.inr.inr.inl => exact Read.arr hj
    all_goals simp [Read]
  simp only [A, Pre.wordsVal_eq_wv]
  exact hf.wv_eq (fun r hr' => (hr r hr').arr hj) (by
    have := es 0; have := es 1; have := es 9; have := es 10; have := es 27
    rcases hj with rfl | rfl | rfl | rfl | rfl <;> simp only [saveBytes] at hZ' <;> omega_arith)

theorem Read.kept {w d : Nat} (hd : Read w d) : ∀ i, d ≤ i → i < d + 8 → Kept w i := by
  intro i h1 h2
  have e0 : slot w 0 = 256 := by simp [slot, hdrBytes]
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have := es 2; have := es 3; have := es 5; have := es 6; have := es 8; have := es 11; have := es 27
  unfold Read at hd
  refine ⟨fun k hk => ?_, fun j hj => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨k, hk, rfl⟩ | rfl | rfl <;> omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨k, hk, rfl⟩ | rfl | rfl <;> omega_arith
  · rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨k, hk, rfl⟩ | rfl | rfl <;> omega_arith

/-! ## Across a round -/

/-- A header word the round keeps. -/
theorem keeps_hdr {m m' : Mem} {B : Addr} {n w i : Nat}
    (h : Proof.MillerRabin.Round.Keeps Proof.MillerRabin.Round.compact B n w m m') (hi : i < 32)
    (hk : i ≠ 1 ∧ i ≠ 23 ∧ i ≠ 26 ∧ i ≠ 29 ∧ i ≠ 30) (hn : 256 ≤ 8 * n) :
    word m' B (8 * i) = word m B (8 * i) :=
  keeps_word h (by omega_arith) fun j h1 h2 => by
    simp only [Kept, slot, hdrBytes, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    and_intros <;> omega_arith

/-- `St` survives the round, which changes the working space only where its
`Keeps` allows (none of the argument words, nor the save area) and memory
outside it only on the stack below `sp`, apart from the buffers. -/
theorem St.call {p : PP} {s t : State} {w : Nat} (h : St p s)
    (hk : Proof.MillerRabin.Round.Keeps Proof.MillerRabin.Round.compact p.B p.n w s.mem t.mem)
    (hf : Frame [⟨p.B, p.Z⟩, stk p.sp] s.mem t.mem) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hsp : t.sp = s.sp) (h6 : t.gpr .s6 = p.B) (hw : slot w 28 + saveBytes ≤ p.Z) : St p t := by
  have hn := h.dims.n
  have e : ∀ {i : Nat}, i < 32 → i ≠ 1 ∧ i ≠ 23 ∧ i ≠ 26 ∧ i ≠ 29 ∧ i ≠ 30 →
      word t.mem p.B (8 * i) = word s.mem p.B (8 * i) := fun hi hk' =>
    keeps_hdr hk hi hk' (by simp only [PP.L] at hn; omega_arith)
  have ha := h.args
  refine ⟨h.scr.congr hwr, h6, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, h.bufs.sepR, ?_, ?_, by rw [hwr]; exact h.bufs.oW,
    h.bufs.oNW, h.bufs.sepO, h.bufs.scrU.congr hwr, h.bufs.sepU, h.bufs.stkR, h.bufs.stkO, h.bufs.stkU, h.bufs.dOU⟩,
    h.dims, by rw [hwr]; exact h.ws, hsp.trans h.sp, h.sp96, h.sp16, h.stkB, fun i hi => ?_⟩
  · rw [e (by decide) (by decide)]; exact ha.wsLen
  · rw [e (by decide) (by decide)]; exact ha.out
  · rw [e (by decide) (by decide)]; exact ha.len
  · rw [e (by decide) (by decide)]; exact ha.usedP
  · rw [e (by decide) (by decide)]; exact ha.bits
  · rw [e (by decide) (by decide)]; exact ha.gen
  · rw [e (by decide) (by decide)]; exact ha.rand
  · rw [e (by decide) (by decide)]; exact ha.rlen
  · rw [hrd, hwr]; exact h.bufs.rdR
  · refine Eq.trans ?_ h.bufs.bR
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => hf _ fun r hr => ?_
    have hi' : i < p.r.length := List.mem_range.mp hi
    have hc : (⟨p.rp, p.r.length⟩ : Region).Contains (p.rp + BitVec.ofNat 64 i) 1 := by
      have := h.dims.rl
      have e0 := VG.Proof.Mont.ofs_off0 p.rp (d := i) (by omega_arith)
      simp only [VG.Proof.Mont.ofs, VG.Proof.Mont.off] at e0
      simp only [Region.Contains]; omega_arith
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · intro hc'
      have := h.bufs.sepR i hi' (p.rp + BitVec.ofNat 64 i) (by
        simp only [Region.Contains] at hc'; simp only [ofs]; omega_arith)
      exact this rfl
    · exact fun hc' => h.bufs.stkR _ hc' hc
  · refine Eq.trans ?_ h.bufs.bO
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => hf _ fun r hr => ?_
    have hi' : i < p.L := List.mem_range.mp hi
    have hnw := h.bufs.oNW
    have ho : ofs p.op (p.op + BitVec.ofNat 64 i) = i := by simp only [ofs]; rw [Mem.sub_ofNat_toNat _ (by omega_arith)]
    have hc : (⟨p.op, p.L⟩ : Region).Contains (p.op + BitVec.ofNat 64 i) 1 := by
      simp only [Region.Contains]; simp only [ofs] at ho; omega_arith
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · intro hc'
      have := h.bufs.sepO _ (by rw [ho]; exact hi')
      simp only [Region.Contains, ofs] at hc' this; omega_arith
    · exact fun hc' => h.bufs.stkO _ hc' hc
  · have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
    have := es 2; have := es 3; have := es 5; have := es 6; have := es 8; have := es 11; have := es 27
    have := es 28
    simp only [PP.Z, saveBytes] at hw
    refine (keeps_word hk (by simp only [saveBytes]; omega_arith) fun j h1 h2 => ?_).trans (h.save i hi)
    simp only [Kept, saveBytes, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h1 ⊢
    and_intros <;> omega_arith

/-- What `round` leaves: the round's state `u` (`RcPost`), and the status
and count stored over it. -/
def RdPost (s : State) (B : Addr) (L w c a i K : Nat) (t : State) : Prop :=
  ∃ u, RcPost s B L w c a u ∧ (t.mem = if Proof.MillerRabin.Round.round c a then
      (u.mem.writeW (B + BitVec.ofNat 64 176) (BitVec.ofNat 64 (i + 1))).writeW (B + BitVec.ofNat 64 160)
        (BitVec.ofNat 64 (if i + 1 < K then 4 else 1))
    else u.mem.writeW (B + BitVec.ofNat 64 160) (BitVec.ofNat 64 2)) ∧ Keep [.t2, .t3, .t4] u t ∧ t.sp = u.sp

/-- `MSt` survives a witness's round. -/
theorem MSt.round {p : PP} {mb N a i K : Nat} {s t : State} (h : MSt p mb N C s)
    (hRd : RdPost s p.B p.n (wOf mb) N a i K t) : MSt p mb N C t := by
  obtain ⟨u, hu, tm, kt, tsp⟩ := hRd
  obtain ⟨hw2, -, hZ⟩ := h.w
  have stu : St p u := h.st.call hu.keeps (by have := hu.frame; rw [h.st.sp] at this; exact this) hu.rd hu.wr
    hu.sp hu.prep.env.s6 hZ
  have phu : Ph p mb C u := h.ph.keep (hu.prep.env.a7.trans h.ph.a7.symm) (hu.prep.env.t0.trans h.ph.t0.symm)
    (hu.prep.env.s5.trans h.ph.s5.symm) fun d hd => keeps_word hu.keeps (by
      have := hd.le; simp only [PP.Z, saveBytes] at hZ; omega_arith) hd.kept
  have mu : MSt p mb N C u := ⟨stu, phu, hu.prep, h.mb1, h.mb2⟩
  have hf : Frm p.B [(176, 8), (160, 8)] u.mem t.mem := by
    rw [tm]
    split
    · exact frm_writeW (a := 160) (frm_writeW (a := 176) (Frm.refl _ _ _) _
        ⟨_, List.mem_cons_self, by decide, by decide⟩ (by decide)) _
        ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by decide, by decide⟩ (by decide)
    · exact frm_writeW (a := 160) (Frm.refl _ _ _) _
        ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by decide, by decide⟩ (by decide)
  exact mu.frm hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Or.inl ⟨by simp, rfl⟩) kt tsp (by decide) (kt.gpr (by decide))
    (kt.gpr (by decide)) (kt.gpr (by decide)) (kt.gpr (by decide))

theorem stat_eq {i K : Nat} :
    BitVec.ofNat 64 4 - BitVec.ofNat 64 (if K ≤ i + 1 then 1 else 0) * BitVec.ofNat 64 3 =
      BitVec.ofNat 64 (if i + 1 < K then 4 else 1) := by
  by_cases h : K ≤ i + 1
  · rw [ite_eq_left h, ite_eq_right (show ¬ i + 1 < K by omega_arith)]; decide
  · rw [ite_eq_right h, ite_eq_left (show i + 1 < K by omega_arith)]; decide

/-- The round of a witness `a` (`roundCall_ok`), then `hStat` 2 if it
failed, else the passing witnesses `hIdx` counted and `hStat` 1 once there
are `hChecks` of them, 4 before. -/
theorem roundCount_ok {R : RoundImpl} {s : State} {B : Addr} {L w c a i K : Nat}
    (h : RC ⟨B, L, w, c, a⟩ s)
    (hI : word s.mem B 176 = BitVec.ofNat 64 i) (hK : word s.mem B 168 = BitVec.ofNat 64 K)
    (hi : i < 2 ^ 62) (hK' : K < 2 ^ 62) :
    WP isa (VG.Impl.MillerRabin.RISCV64.Search.round R.name R.code) s (RdPost s B L w c a i K) := by
  have hp : Prep s B L w c := h.1
  have hZ := hp.env.hZ
  have hnw := hp.env.hs.nowrap
  have es : ∀ j, VG.Proof.Bignum.slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have hZ' : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := by rw [← es]; exact hZ
  unfold VG.Impl.MillerRabin.RISCV64.Search.round
  refine WP.seq (WP.mono (roundCall_ok R h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2) fun u (hu : RcPost s B L w c a u) => ?_)
  have hs : Scr u B (8 * L) := hu.prep.env.hs
  have h6 : u.gpr .s6 = B := hu.prep.env.s6
  have l160 : InRegions u.wr (B + BitVec.ofNat 64 160) 8 := hs.st (d := 160) (by omega_arith)
  have a160 : (B + BitVec.ofNat 64 160).toNat % 8 = 0 := hs.al8 (d := 160) (by omega_arith) (by decide)
  refine WP.ite (decide ((if Proof.MillerRabin.Round.round c a then 1 else 0) = 0))
    (eval_zero_ofNat u .a0 (by split <;> decide) hu.a0) (fun hb => ?_) (fun hb => ?_)
  · have hf : Proof.MillerRabin.Round.round c a = false := by
      cases hr : Proof.MillerRabin.Round.round c a <;> simp_all
    refine WP.mono (WP.rdwr (WP.keep [.t2] (Q := fun t => t.mem = u.mem.writeW (B + BitVec.ofNat 64 160)
      (BitVec.ofNat 64 2)) ?_ (by rfl) (by rfl))) fun t ⟨⟨tm, kt⟩, _, _, tsp⟩ =>
        ⟨u, hu, by rw [tm, hf]; rfl, kt.mono (by decide), tsp⟩
    simp only [sth, hStat]
    brun [h6, l160, a160, exec_li (show imm12 2 by decide)]
  · have ht : Proof.MillerRabin.Round.round c a = true := by
      cases hr : Proof.MillerRabin.Round.round c a <;> simp_all
    have rI : u.mem.readW (B + BitVec.ofNat 64 176) 64 = BitVec.ofNat 64 i :=
      (keeps_word hu.keeps (d := 176) (by omega_arith) (fun j h1 h2 => by
        simp only [Kept, slot, hdrBytes, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        and_intros <;> omega_arith)).trans hI
    have rK : u.mem.readW (B + BitVec.ofNat 64 168) 64 = BitVec.ofNat 64 K :=
      (keeps_word hu.keeps (d := 168) (by omega_arith) (fun j h1 h2 => by
        simp only [Kept, slot, hdrBytes, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        and_intros <;> omega_arith)).trans hK
    have l176 : InRegions (u.rd ++ u.wr) (B + BitVec.ofNat 64 176) 8 := hs.ld (d := 176) (by omega_arith)
    have l168 : InRegions (u.rd ++ u.wr) (B + BitVec.ofNat 64 168) 8 := hs.ld (d := 168) (by omega_arith)
    have s176 : InRegions u.wr (B + BitVec.ofNat 64 176) 8 := hs.st (d := 176) (by omega_arith)
    have a176 : (B + BitVec.ofNat 64 176).toNat % 8 = 0 := hs.al8 (d := 176) (by omega_arith) (by decide)
    have a168 : (B + BitVec.ofNat 64 168).toNat % 8 = 0 := hs.al8 (d := 168) (by omega_arith) (by decide)
    simp only [List.append_assoc]
    rw [WP.block_append_iff]
    refine WP.mono (WP.rdwr (WP.keep [.t2, .t3] (Q := fun v => v.gpr .t2 = BitVec.ofNat 64 (i + 1) ∧
        v.gpr .t3 = BitVec.ofNat 64 K ∧ v.mem = u.mem.writeW (B + BitVec.ofNat 64 176) (BitVec.ofNat 64 (i + 1)))
      ?_ (by rfl) (by rfl))) fun v ⟨⟨⟨v2, v3, vm⟩, kv⟩, _, _, vsp⟩ => ?_
    · simp only [ldh, sth, hIdx, hChecks]
      brun [h6, l176, l168, s176, a176, a168, rI, rK, BitVec.ofNat_add_ofNat]
    rw [WP.block_append_iff]
    refine WP.mono (WP.rdwr (geFlag_ok (d := .t3) v2 v3 (by omega_arith) (by omega_arith)))
      fun v' ⟨⟨⟨g3, gm⟩, kg⟩, _, _, gsp⟩ => ?_
    have h6' : v'.gpr .s6 = B := (kg.gpr (by decide)).trans ((kv.gpr (by decide)).trans h6)
    have l160' : InRegions v'.wr (B + BitVec.ofNat 64 160) 8 := by rw [kg.2.2, kv.2.2]; exact l160
    refine WP.mono (WP.rdwr (WP.keep [.t3, .t4] (Q := fun t => t.mem = v'.mem.writeW (B + BitVec.ofNat 64 160)
        (BitVec.ofNat 64 (if i + 1 < K then 4 else 1))) ?_ (by rfl) (by rfl)))
      fun t ⟨⟨tm, kt⟩, _, _, tsp⟩ => ⟨u, hu, by rw [tm, gm, vm, ht]; rfl,
        ((kv.trans kg).trans kt).mono (by decide), by rw [tsp, gsp, vsp]⟩
    simp only [sth, hStat]
    brun [h6', l160', a160, g3, exec_li (show imm12 3 by decide), exec_li (show imm12 4 by decide), stat_eq]

/-! ## Drawing a witness -/

open VG.Impl.Bignum.RISCV64.PublicChecked (base)
open VG.Impl.Bignum.RISCV64.Precompute (loadN copyWords)

/-- Before a draw of a witness for the modulus `N` of `mb` bits, `u`
octets of the tape read. -/
structure DPre (p : PP) (mb N u C : Nat) (s : State) : Prop where
  m : MSt p mb N C s
  used : word s.mem p.B (8 * hUsed) = BitVec.ofNat 64 u
  room : u + (mb + 7) / 8 ≤ p.r.length

/-- The head of a draw. -/
abbrev dHeadB : List Instr :=
  [ldh .s7 hRand, ldh .t2 hUsed, .add .s7 .s7 .t2, ldh .s8 hK, .add .t2 .t2 .s8, sth .t2 hUsed] ++ base .a7 4

/-- After the head of a draw: the octets' address in `s7`, their count in
`s8`, array 4's in `a7`, and `used` advanced. -/
def DHead (p : PP) (mb u : Nat) (s t : State) : Prop :=
  (t.gpr .s7 = p.rp + BitVec.ofNat 64 u ∧ t.gpr .s8 = BitVec.ofNat 64 ((mb + 7) / 8) ∧
    t.gpr .a7 = off p.B (slot (wOf mb) 4) ∧
    t.mem = s.mem.writeW (p.B + BitVec.ofNat 64 152) (BitVec.ofNat 64 (u + (mb + 7) / 8))) ∧
  Keep [.s7, .t2, .s8, .a7] s t ∧ t.sp = s.sp

theorem dHead_ok {p : PP} {mb N u : Nat} {s : State} (h : DPre p mb N u C s) :
    WP isa (.block dHeadB) s (DHead p mb u s) := by
  rw [WP.block_append_iff]
  have hk := h.m.ph.kW
  have hu := h.used
  have st := h.m.st
  simp only [word, off, hK, hUsed, Nat.reduceMul] at hk hu
  refine WP.mono (WP.rdwr (WP.keep [.s7, .t2, .s8] (Q := fun u' => u'.gpr .s7 = p.rp + BitVec.ofNat 64 u ∧
      u'.gpr .s8 = BitVec.ofNat 64 ((mb + 7) / 8) ∧
      u'.mem = s.mem.writeW (p.B + BitVec.ofNat 64 152) (BitVec.ofNat 64 (u + (mb + 7) / 8))) ?_ (by rfl) (by rfl)))
    fun t₁ ⟨⟨⟨a7, a8, am⟩, k₁⟩, _, _, sp₁⟩ => ?_
  · simp only [ldh, sth, hRand, hUsed, hK]
    brun [st.s6, st.ld (d := 136) (by decide), st.ld (d := 152) (by decide), st.ld (d := 216) (by decide),
      st.st (d := 152) (by decide), st.al (d := 136) (by decide) (by decide), st.al (d := 152) (by decide) (by decide),
      st.al (d := 216) (by decide) (by decide), st.args.rand', hk, hu, BitVec.ofNat_add_ofNat]
  refine WP.mono (WP.rdwr (Pub.base_ok (rd := .a7) (by decide) ((k₁.gpr (by decide)).trans h.m.ph.a7)
    ((k₁.gpr (by decide)).trans h.m.ph.s5) 4))
    fun t ⟨⟨⟨b7, m⟩, k⟩, _, _, sp⟩ => ⟨⟨(k.gpr (by decide)).trans a7, (k.gpr (by decide)).trans a8, b7,
      m.trans am⟩, (k₁.trans k).mono (by decide), sp.trans sp₁⟩

/-- The load, after the head: the witness's octets in array 4. -/
theorem dLoadN_ok {p : PP} {mb N u : Nat} {s t : State} (h : DPre p mb N u C s) (ht : DHead p mb u s t) :
    WP isa loadN t fun t₂ =>
      ((wv t₂.mem p.B (slot (wOf mb) 4) (wOf mb) = Spec.Rsa.os2ip ((p.r.drop u).take ((mb + 7) / 8)) ∧
        t₂.gpr .a7 = off p.B (slot (wOf mb) 4) ∧
        Frm p.B [(152, 8), (slot (wOf mb) 4, 8 * wOf mb)] s.mem t₂.mem ∧
        t₂.mem.readW (p.B + BitVec.ofNat 64 152) 64 = BitVec.ofNat 64 (u + (mb + 7) / 8)) ∧
      Keep (([.s7, .t2, .s8, .a7] : List Reg) ++ ([.a0, .s0, .t3, .t4, .t5] : List Reg)) s t₂) ∧ t₂.sp = s.sp := by
  obtain ⟨⟨a7, a8, a77, am⟩, k₁, sp₁⟩ := ht
  have st := h.m.st
  have hb1 := st.dims.b1
  have hb2 := st.dims.b2
  have hn := st.dims.n
  have hnw := st.scr.nowrap
  have hm1 := h.m.mb1
  have hm2 := h.m.mb2
  have hroom := h.room
  have h0 := h.m.ph.t0
  generalize hwd : wOf mb = w at *
  have hw8 : 8 ≤ w := by simp only [wOf] at hwd; omega_arith
  have hw128 : w ≤ 128 := by simp only [wOf] at hwd; omega_arith
  have hKw : (mb + 7) / 8 ≤ 8 * w := by simp only [wOf] at hwd; omega_arith
  have hZ : slot w 4 + 8 * w ≤ p.Z := by simp only [slot, hdrBytes, PP.Z, PP.L] at hn ⊢; omega_arith
  generalize hKd : (mb + 7) / 8 = K at *
  have hK1 : 1 ≤ K := by omega_arith
  have ho : Outside p.B 152 8 s.mem t.mem := by rw [am]; exact writeW_outside _ _ _ (by omega_arith)
  have hbr : Spec.Rsa.bytesAt t.mem p.rp p.r.length = p.r := by
    rw [bytes_frm (Frm.of_outside (rs := [(152, 8)]) ho (List.mem_singleton_self _)) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; simp only [PP.Z]; omega_arith) st.bufs.sepR]
    exact st.bufs.bR
  have e : ∀ i, VG.Proof.Mont.off (p.rp + BitVec.ofNat 64 u) i = off p.rp (u + i) := fun i => off_off p.rp u i
  refine WP.mono (WP.rdwr (loadN_ok (N := p.rp + BitVec.ofNat 64 u) (st.scr.congr k₁.2.2) a77
    (by rw [a7]; simp only [VG.Proof.Mont.off, BitVec.add_zero]) a8 ((k₁.gpr (by decide)).trans h0) hK1 hKw
    (by omega_arith) (by simp only [slot, hdrBytes]; omega_arith) (by simp only [slot, hdrBytes]; omega_arith) hZ
    (fun i hi => by
      rw [k₁.2.1, k₁.2.2, e]
      exact st.bufs.rdR _ (by omega_arith))
    (fun i hi x hx => by
      rw [e]
      exact st.bufs.sepR _ (by omega_arith) x hx))) fun t₂ ⟨⟨v₂, o₂, k₂⟩, _, _, sp₂⟩ => ?_
  refine ⟨⟨⟨?_, (k₂.gpr (by decide)).trans a77, ?_, ?_⟩, k₁.trans k₂⟩, sp₂.trans sp₁⟩
  · rw [← Pre.wordsVal_eq_wv, v₂, ← VG.Proof.Dsa.bytesAt_slice t.mem p.rp (total := p.r.length) (by omega_arith), hbr]
  · exact (Frm.of_outside ho (List.mem_cons_self)).trans
      (Frm.of_outside o₂ (List.mem_cons_of_mem _ List.mem_cons_self))
  · rw [show t₂.mem.readW (p.B + BitVec.ofNat 64 152) 64 = word t₂.mem p.B 152 from rfl,
      Outside.word o₂ (by simp only [slot, hdrBytes]; omega_arith) (by omega_arith), am]
    exact Mem.readW_writeW_self64 _ _ _

/-- The cut: array 4's top word and'ed with `hTop`, so it holds its number
modulo `2^mb`. -/
theorem dCut_ok {p : PP} {mb : Nat} {s : State} (h : St p s) (hm1 : 511 ≤ mb) (hm2 : mb ≤ p.bits)
    (h7 : s.gpr .a7 = off p.B (slot (wOf mb) 0)) (h0 : s.gpr .t0 = BitVec.ofNat 64 (wOf mb))
    (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (wOf mb + 2)))
    (htop : word s.mem p.B (8 * hTop) = BitVec.ofNat 64 (2 ^ (mb + 64 - 64 * wOf mb) - 1)) :
    WP isa (.block (base .t3 4 ++ ([.shift .sll .d .t2 .t0 3, .add .t3 .t3 .t2, .addi .t3 .t3 (-8), ldh .t4 hTop,
        .load .d .t2 .t3 0, .logic .and .t2 .t2 .t4, .store .d .t2 .t3 0] : List Instr))) s fun t =>
      ((wv t.mem p.B (slot (wOf mb) 4) (wOf mb) = wv s.mem p.B (slot (wOf mb) 4) (wOf mb) % 2 ^ mb ∧
        Frm p.B [(slot (wOf mb) 4, 8 * wOf mb)] s.mem t.mem) ∧ Keep [.t3, .t2, .t4] s t) ∧ t.sp = s.sp := by
  have hb2 := h.dims.b2
  have hn := h.dims.n
  have hnw := h.scr.nowrap
  generalize hwd : wOf mb = w at *
  have hw8 : 8 ≤ w := by simp only [wOf] at hwd; omega_arith
  have hw128 : w ≤ 128 := by simp only [wOf] at hwd; omega_arith
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have hZ : slot w 4 + 8 * w ≤ p.Z := by
    simp only [es, PP.Z] at hn ⊢; simp only [PP.L] at hn; omega_arith
  have hk1 : 1 ≤ mb + 64 - 64 * w := by simp only [wOf] at hwd; omega_arith
  have hk2 : mb + 64 - 64 * w ≤ 64 := by simp only [wOf] at hwd; omega_arith
  have hb : 64 * (w - 1) + (mb + 64 - 64 * w) = mb := by simp only [wOf] at hwd; omega_arith
  generalize hkd : mb + 64 - 64 * w = k at htop hk1 hk2 hb
  rw [WP.block_append_iff]
  refine WP.mono (WP.rdwr (Pub.base_ok (rd := .t3) (by decide) h7 h5 4)) fun v ⟨⟨⟨v3, vm⟩, kv⟩, _, _, vsp⟩ => ?_
  have e3 : off p.B (slot w 4 + 8 * w) - BitVec.ofNat 64 8 = off p.B (slot w 4 + 8 * (w - 1)) := by
    rw [off_sub _ (by omega_arith)]; congr 2; omega_arith
  have hsv : Scr v p.B p.Z := h.scr.congr kv.2.2
  have sT : InRegions v.wr (off p.B (slot w 4 + 8 * (w - 1))) 8 := hsv.st (by omega_arith)
  have lT : InRegions (v.rd ++ v.wr) (off p.B (slot w 4 + 8 * (w - 1))) 8 := hsv.ld (by omega_arith)
  have aT : (off p.B (slot w 4 + 8 * (w - 1))).toNat % 8 = 0 :=
    hsv.al8 (by omega_arith) (by simp only [es]; omega_arith)
  have l192 : InRegions (v.rd ++ v.wr) (p.B + BitVec.ofNat 64 192) 8 := by
    rw [kv.2.1, kv.2.2]; exact h.ld (d := 192) (by decide)
  have a192 : (p.B + BitVec.ofNat 64 192).toNat % 8 = 0 := h.al (d := 192) (by decide) (by decide)
  have tv : v.mem.readW (p.B + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (2 ^ k - 1) := by rw [vm]; exact htop
  refine WP.mono (WP.rdwr (WP.keep [.t2, .t3, .t4] (Q := fun t => t.mem = s.mem.writeW (off p.B (slot w 4 + 8 * (w - 1)))
        (s.mem.readW (off p.B (slot w 4 + 8 * (w - 1))) 64 &&& BitVec.ofNat 64 (2 ^ k - 1))) ?_ (by rfl) (by rfl)))
    fun t ⟨⟨e0, kt⟩, _, _, tsp⟩ => ?_
  · simp only [ldh, hTop]
    brun [v3, (kv.gpr (by decide)).trans h0, (kv.gpr (by decide)).trans h.s6,
      VG.Proof.MillerRabin.RISCV64.shl3_ofNat, e3, sT, lT, aT, l192, a192, tv, BitVec.add_zero,
      add_ofNat_zero, vm, show s.mem.readW (p.B + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (2 ^ k - 1) from htop]
  refine ⟨⟨⟨?_, ?_⟩, (kv.trans kt).mono (by decide)⟩, by rw [tsp, vsp]⟩
  · rw [← hb]
    refine Proof.Ffdh.ParameterCandidate.wv_cut (by omega_arith) hk2 ?_ fun j hj => ?_
    · simp only [word, off] at e0 ⊢; rw [e0, Mem.readW_writeW_self64]
    · simp only [word, off] at e0 ⊢; rw [e0, rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
  · rw [e0]
    exact frm_writeW (Frm.refl _ _ _) _ ⟨_, List.mem_singleton_self _, by dsimp only; omega_arith,
      by dsimp only; omega_arith⟩ (by omega_arith)

/-- The witness drawn at offset `u` of the tape, for a modulus of `mb` bits. -/
def wA (mb : Nat) (r : List Byte) (u : Nat) : Nat := Spec.Rsa.os2ip ((r.drop u).take ((mb + 7) / 8)) % 2 ^ mb

/-- `hStat` after a draw of `a`, from 4. -/
def dStat (N K i a : Nat) : Nat :=
  if 2 ≤ a ∧ a < N - 1 then (if Proof.MillerRabin.Round.round N a then (if i + 1 < K then 4 else 1) else 2) else 4

/-- `hIdx` after a draw of `a`. -/
def dIdx (N i a : Nat) : Nat := if 2 ≤ a ∧ a < N - 1 ∧ Proof.MillerRabin.Round.round N a = true then i + 1 else i

/-- The cut of a witness's top word. -/
abbrev cutB : List Instr :=
  base .t3 4 ++ ([.shift .sll .d .t2 .t0 3, .add .t3 .t3 .t2, .addi .t3 .t3 (-8), ldh .t4 hTop,
    .load .d .t2 .t3 0, .logic .and .t2 .t2 .t4, .store .d .t2 .t3 0] : List Instr)

/-- The draw's branches: on the witness below 2, on its range, and the round. -/
def drawBranch (name : String) (roundCode : Prog isa) : Prog isa :=
  .ite (.zero .a3) (.block []) (.ite (.zero .s4) (.block []) (VG.Impl.MillerRabin.RISCV64.Search.round name roundCode))

theorem draw_eq (name : String) (roundCode : Prog isa) :
    draw name roundCode = .seq (.seq (.block dHeadB) (.seq loadN (.block [.addi .a7 .s6 hdrBytes])))
      (.seq (.block cutB) (.seq atLeast2 (.seq ltN (drawBranch name roundCode)))) := rfl

/-- After the witness's octets are loaded. -/
structure DL (p : PP) (mb N u i C : Nat) (t : State) : Prop where
  m : MSt p mb N C t
  used : word t.mem p.B 152 = BitVec.ofNat 64 (u + (mb + 7) / 8)
  stat : word t.mem p.B 160 = BitVec.ofNat 64 4
  idx : word t.mem p.B 176 = BitVec.ofNat 64 i
  x : wv t.mem p.B (slot (wOf mb) 4) (wOf mb) = Spec.Rsa.os2ip ((p.r.drop u).take ((mb + 7) / 8))

/-- The ranges a draw changes. -/
abbrev drR (w : Nat) : List (Nat × Nat) :=
  [(152, 8), (slot w 4, 8 * w), (slot w 3, 8 * (w + 2)), (slot w 6, 8 * (w + 2))]

theorem drR_free (w : Nat) : ∀ r ∈ drR w, Free w r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Or.inl ⟨by simp, rfl⟩
  · exact Or.inr ⟨4, by decide, by decide, rfl, by dsimp only; omega_arith⟩
  · exact Or.inr ⟨3, by decide, by decide, rfl, Nat.le_refl _⟩
  · exact Or.inr ⟨6, by decide, by decide, rfl, Nat.le_refl _⟩

theorem drR_hdr {w d : Nat} (hd : d = 160 ∨ d = 176) : ∀ r ∈ drR w, d + 8 ≤ r.1 ∨ r.1 + r.2 ≤ d := by
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  have := es 3; have := es 4; have := es 6
  rcases hr with rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith

/-- The load and `a7` back, after the head. -/
theorem drawLoad2_ok {p : PP} {mb N u i : Nat} {s t : State} (h : MSt p mb N C s)
    (hu : word s.mem p.B 152 = BitVec.ofNat 64 u) (hroom : u + (mb + 7) / 8 ≤ p.r.length)
    (hI : word s.mem p.B 176 = BitVec.ofNat 64 i) (hS : word s.mem p.B 160 = BitVec.ofNat 64 4)
    (ht : DHead p mb u s t) :
    WP isa (.seq loadN (.block [.addi .a7 .s6 hdrBytes])) t (DL p mb N u i C) := by
  obtain ⟨hw2, hw128, hZ⟩ := h.w
  have hnw := h.st.scr.nowrap
  have es : ∀ j, slot (wOf mb) j = 256 + j * (8 * (wOf mb + 2)) := fun _ => rfl
  have hD : DPre p mb N u C s := ⟨h, hu, hroom⟩
  refine WP.seq (WP.mono (dLoadN_ok hD ht) fun t₂ ⟨⟨⟨v₂, _, f₂, u₂⟩, k₂⟩, sp₂⟩ => ?_)
  refine WP.mono (WP.rdwr (WP.keep [.a7] (Q := fun t₃ => t₃.gpr .a7 = s.gpr .a7 ∧ t₃.mem = t₂.mem)
    (by brun [(k₂.gpr (by decide)).trans h.st.s6, h.ph.a7, hdrBytes, slot]; simp [off]) (by rfl) (by rfl)))
    fun t₃ ⟨⟨⟨a7, m₃⟩, k₃⟩, _, _, sp₃⟩ => ?_
  have F : Frm p.B (drR (wOf mb)) s.mem t₃.mem := by
    rw [m₃]; exact f₂.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp
  have k := k₂.trans k₃
  have M : MSt p mb N C t₃ := h.frm F (drR_free _) k (sp₃.trans sp₂) (by decide) a7 (k.gpr (by decide))
    (k.gpr (by decide)) (k.gpr (by decide))
  refine ⟨M, by rw [m₃]; exact u₂, ?_, ?_, by rw [m₃]; exact v₂⟩
  · rw [F.word_eq (drR_hdr (Or.inl rfl)) (by omega_arith)]; exact hS
  · rw [F.word_eq (drR_hdr (Or.inr rfl)) (by omega_arith)]; exact hI

theorem drawLoad_ok {p : PP} {mb N u i : Nat} {s : State} (h : MSt p mb N C s)
    (hu : word s.mem p.B 152 = BitVec.ofNat 64 u) (hroom : u + (mb + 7) / 8 ≤ p.r.length)
    (hI : word s.mem p.B 176 = BitVec.ofNat 64 i) (hS : word s.mem p.B 160 = BitVec.ofNat 64 4) :
    WP isa (.seq (.block dHeadB) (.seq loadN (.block [.addi .a7 .s6 hdrBytes]))) s (DL p mb N u i C) :=
  WP.seq (WP.mono (dHead_ok ⟨h, hu, hroom⟩) fun _ ht => drawLoad2_ok h hu hroom hI hS ht)

/-- Before the draw's branches: the witness `wA mb p.r u` in array 4, `a3`
zero exactly when it is below 2, `s4` exactly when it is not below `N − 1`. -/
structure DMid (p : PP) (mb N u i C : Nat) (t : State) : Prop where
  m : MSt p mb N C t
  used : word t.mem p.B 152 = BitVec.ofNat 64 (u + (mb + 7) / 8)
  stat : word t.mem p.B 160 = BitVec.ofNat 64 4
  idx : word t.mem p.B 176 = BitVec.ofNat 64 i
  z3 : t.gpr .a3 = 0#64 ↔ wA mb p.r u < 2
  z4 : t.gpr .s4 = 0#64 ↔ ¬ wA mb p.r u < N - 1
  a4 : A t.mem p.B (wOf mb) 4 = wA mb p.r u

theorem drawMid_ok {p : PP} {mb N u i : Nat} {s : State} (h : DL p mb N u i C s) :
    WP isa (.seq (.seq (.block cutB) atLeast2) ltN) s (DMid p mb N u i C) := by
  obtain ⟨hw2, hw128, hZ⟩ := h.m.w
  have hnw := h.m.st.scr.nowrap
  have es : ∀ j, slot (wOf mb) j = 256 + j * (8 * (wOf mb + 2)) := fun _ => rfl
  have hZ' : 256 + 28 * (8 * (wOf mb + 2)) + saveBytes ≤ p.Z := by rw [← es]; exact hZ
  simp only [saveBytes] at hZ'
  have M := h.m
  refine WP.seq (WP.seq (WP.mono (dCut_ok M.st M.mb1 M.mb2 M.ph.a7 M.ph.t0 M.ph.s5 M.ph.topW)
    fun t₁ ⟨⟨⟨wv₁, f₁⟩, k₁⟩, sp₁⟩ => ?_))
  have ha₁ : wv t₁.mem p.B (slot (wOf mb) 4) (wOf mb) = wA mb p.r u := by rw [wv₁, h.x]; rfl
  have F₁ : Frm p.B (drR (wOf mb)) s.mem t₁.mem := f₁.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; simp [hr]
  have M₁ : MSt p mb N C t₁ := M.frm F₁ (drR_free _) k₁ sp₁ (by decide) (k₁.gpr (by decide)) (k₁.gpr (by decide))
    (k₁.gpr (by decide)) (k₁.gpr (by decide))
  refine WP.mono (WP.rdwr (VG.Proof.MillerRabin.RISCV64.Blinded.atLeast2_ok M₁.prep.env))
    fun t₂ ⟨⟨⟨z₂, m₂⟩, k₂⟩, _, _, sp₂⟩ => ?_
  rw [A, Pre.wordsVal_eq_wv] at z₂
  rw [ha₁] at z₂
  have M₂ : MSt p mb N C t₂ := M₁.frm (rs := []) (by rw [m₂]; exact Frm.refl _ _ _) (by simp) k₂ sp₂ (by decide)
    (k₂.gpr (by decide)) (k₂.gpr (by decide)) (k₂.gpr (by decide)) (k₂.gpr (by decide))
  have hx₂ : A t₂.mem p.B (wOf mb) 4 = wA mb p.r u := by rw [A, Pre.wordsVal_eq_wv, m₂]; exact ha₁
  refine WP.mono (WP.rdwr (VG.Proof.MillerRabin.RISCV64.Blinded.ltN_ok M₂.prep.env M₂.prep.n))
    fun t ⟨⟨⟨z₄, f₄⟩, k₄⟩, _, _, sp₄⟩ => ?_
  rw [hx₂] at z₄
  have F₄ : Frm p.B (drR (wOf mb)) t₂.mem t.mem := f₄.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp
  have M₄ : MSt p mb N C t := M₂.frm F₄ (drR_free _) k₄ sp₄ (by decide) (k₄.gpr (by decide)) (k₄.gpr (by decide))
    (k₄.gpr (by decide)) (k₄.gpr (by decide))
  have F : Frm p.B (drR (wOf mb)) s.mem t.mem := (F₁.trans (by rw [m₂] at F₄; exact F₄))
  refine ⟨M₄, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f₄.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have := es 3; have := es 6
      rcases hr with rfl | rfl <;> dsimp only <;> omega_arith) (by omega_arith), m₂,
      f₁.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have := es 4
      rcases hr with rfl <;> dsimp only <;> omega_arith) (by omega_arith)]
    exact h.used
  · rw [F.word_eq (drR_hdr (Or.inl rfl)) (by omega_arith)]; exact h.stat
  · rw [F.word_eq (drR_hdr (Or.inr rfl)) (by omega_arith)]; exact h.idx
  · rw [k₄.gpr (by decide)]; exact z₂
  · rw [z₄, ← VG.Proof.RsaKeyGen.or_one_lt_iff M₂.prep.odd]
    split
    · exact ⟨fun h => absurd h (by decide), fun h => absurd ‹_› h⟩
    · exact ⟨fun _ => ‹_›, fun _ => rfl⟩
  · rw [← hx₂]
    simp only [A, Pre.wordsVal_eq_wv]
    exact f₄.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have := es 3; have := es 4; have := es 6
      rcases hr with rfl | rfl <;> dsimp only <;> omega_arith) (by have := es 4; omega_arith)

/-- The witness of `DMid`, in range, before its round. -/
theorem DMid.rc {p : PP} {mb N u i : Nat} {t : State} (h : DMid p mb N u i C t) (ha : wA mb p.r u < N) :
    RC ⟨p.B, p.n, wOf mb, N, wA mb p.r u⟩ t :=
  ⟨h.m.prep, h.a4, ha, by rw [h.m.st.sp]; exact h.m.st.sp16, by rw [h.m.st.sp]; exact h.m.st.sp96,
    by rw [h.m.st.sp]; exact h.m.st.stkB⟩

theorem drawTail_ok {R : RoundImpl} {p : PP} {mb N u i : Nat} {t₄ : State}
    (h : DMid p mb N u i C t₄) (hi : i < 2 ^ 62) :
    WP isa (drawBranch R.name R.code) t₄ fun t => MSt p mb N C t ∧
      word t.mem p.B 152 = BitVec.ofNat 64 (u + (mb + 7) / 8) ∧
      word t.mem p.B 160 = BitVec.ofNat 64 (dStat N C i (wA mb p.r u)) ∧
      word t.mem p.B 176 = BitVec.ofNat 64 (dIdx N i (wA mb p.r u)) := by
  obtain ⟨M₄, u₄, hS, hI, z₃, z₄, ha₄⟩ := h
  have hD : DMid p mb N u i C t₄ := ⟨M₄, u₄, hS, hI, z₃, z₄, ha₄⟩
  obtain ⟨hw2, hw128, hZ⟩ := M₄.w
  have es : ∀ j, slot (wOf mb) j = 256 + j * (8 * (wOf mb + 2)) := fun _ => rfl
  have hnw := M₄.st.scr.nowrap
  have hZ' : 256 + 28 * (8 * (wOf mb + 2)) + saveBytes ≤ p.Z := by rw [← es]; exact hZ
  simp only [saveBytes] at hZ'
  have out : ¬ (2 ≤ wA mb p.r u ∧ wA mb p.r u < N - 1) → MSt p mb N C t₄ ∧
      word t₄.mem p.B 152 = BitVec.ofNat 64 (u + (mb + 7) / 8) ∧
      word t₄.mem p.B 160 = BitVec.ofNat 64 (dStat N C i (wA mb p.r u)) ∧
      word t₄.mem p.B 176 = BitVec.ofNat 64 (dIdx N i (wA mb p.r u)) := fun hn =>
    ⟨M₄, u₄, by rw [hS, dStat, ite_eq_right hn], by
      rw [hI, dIdx, ite_eq_right fun ⟨a, b, _⟩ => hn ⟨a, b⟩]⟩
  unfold drawBranch
  refine WP.ite (t₄.gpr .a3 == 0) (eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · rw [WP.block_nil_iff]
    have h0 : t₄.gpr .a3 = 0#64 := beq_iff_eq.mp hb
    exact out fun ⟨a, _⟩ => by have := z₃.mp h0; omega_arith
  refine WP.ite (t₄.gpr .s4 == 0) (eval_zero _ _) (fun hb' => ?_) (fun hb' => ?_)
  · rw [WP.block_nil_iff]
    exact out fun ⟨_, b⟩ => z₄.mp (beq_iff_eq.mp hb') b
  -- A witness in range: its round.
  have ha2 : 2 ≤ wA mb p.r u := by
    by_contra hc
    have : (t₄.gpr .a3 == 0) = true := beq_iff_eq.mpr (z₃.mpr (by omega_arith))
    rw [hb] at this; exact absurd this (by decide)
  have haN : wA mb p.r u < N - 1 := by
    by_contra hc
    have : (t₄.gpr .s4 == 0) = true := beq_iff_eq.mpr (z₄.mpr hc)
    rw [hb'] at this; exact absurd this (by decide)
  have hK : C < 2 ^ 62 := by have := M₄.ph.k2; omega_arith
  refine WP.mono (roundCount_ok (hD.rc (by omega_arith)) hI M₄.ph.checksW hi hK)
    fun t ht => ⟨M₄.round ht, ?_⟩
  obtain ⟨v, hv, tm, -⟩ := ht
  have hn₄ : 8 * p.n = p.Z := rfl
  have u₅ : word v.mem p.B 152 = BitVec.ofNat 64 (u + (mb + 7) / 8) :=
    (keeps_hdr (i := 19) hv.keeps (by decide) (by decide) (by omega_arith)).trans u₄
  simp only [word, off] at u₅ ⊢
  have ht2 : 2 ≤ wA mb p.r u ∧ wA mb p.r u < N - 1 := ⟨ha2, haN⟩
  cases hr : Proof.MillerRabin.Round.round N (wA mb p.r u) <;> simp only [hr, Bool.false_eq_true, ↓reduceIte] at tm <;>
    rw [tm] <;> refine ⟨?_, ?_, ?_⟩
  · rw [rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]; exact u₅
  · rw [Mem.readW_writeW_self64, dStat, ite_eq_left ht2, hr]; rfl
  · rw [rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), dIdx, ite_eq_right (by simp [hr])]
    exact (keeps_hdr (i := 22) hv.keeps (by decide) (by decide) (by omega_arith)).trans hI
  · rw [rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
      rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]; exact u₅
  · rw [Mem.readW_writeW_self64, dStat, ite_eq_left ht2, hr]; rfl
  · rw [rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), Mem.readW_writeW_self64, dIdx, ite_eq_left ⟨ha2, haN, hr⟩]

theorem draw_ok {R : RoundImpl} {p : PP} {mb N u i : Nat} {s : State} (h : MSt p mb N C s)
    (hu : word s.mem p.B 152 = BitVec.ofNat 64 u) (hroom : u + (mb + 7) / 8 ≤ p.r.length)
    (hI : word s.mem p.B 176 = BitVec.ofNat 64 i) (hS : word s.mem p.B 160 = BitVec.ofNat 64 4)
    (hi : i < 2 ^ 62) :
    WP isa (draw R.name R.code) s fun t => MSt p mb N C t ∧
      word t.mem p.B 152 = BitVec.ofNat 64 (u + (mb + 7) / 8) ∧
      word t.mem p.B 160 = BitVec.ofNat 64 (dStat N C i (wA mb p.r u)) ∧
      word t.mem p.B 176 = BitVec.ofNat 64 (dIdx N i (wA mb p.r u)) := by
  rw [draw_eq]
  refine WP.seq (WP.mono (drawLoad_ok h hu hroom hI hS) fun t ht => ?_)
  refine WP.assoc (WP.assoc (WP.seq (WP.mono (drawMid_ok ht) fun t₄ h₄ => drawTail_ok h₄ hi)))

end VG.Proof.Ffdh.RISCV64.ParameterCandidate

namespace VG.Proof.Ffdh.RISCV64.ParameterCandidate

variable {C : Nat}

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Ffdh.RISCV64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.RISCV64
open VG.RISCV64.Steps (eval_zero eval_nonzero eval_zero_ofNat eval_nonzero_ofNat)
open VG.Impl.MillerRabin.RISCV64 VG.Impl.MillerRabin.RISCV64.Search
open VG.Proof.MillerRabin.RISCV64 (Env A MCtx RoundImpl)
open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses checkWitnesses_step onPass sievedTests)

/-! ## The witnesses, one draw at a time -/

theorem mr_round_eq {N : Nat} (a : Nat) (hN : 3 ≤ N) (ho : N % 2 = 1) :
    Proof.MillerRabin.Round.round N a = Spec.Ffdh.mrRound N a := by
  simpa only [Proof.MillerRabin.Round.round] using VG.Proof.Ffdh.rsa_round_eq a hN ho

theorem cw_short {N mb n : Nat} (hbl : Spec.RsaKeyGen.bitLength (N - 1) = mb) (hm : 1 ≤ mb) {r : List Byte} {u : Nat}
    (h : r.length < u + (mb + 7) / 8) : checkWitnesses N (n + 1) (r.drop u) = none := by
  have hw : Spec.Ffdh.witnessOctets N = (mb + 7) / 8 := by simp only [Spec.Ffdh.witnessOctets, hbl]
  rw [checkWitnesses_step (by rw [hw]; omega_arith), hw,
    ite_eq_right (show ¬(mb + 7) / 8 ≤ (r.drop u).length by rw [List.length_drop]; omega_arith)]

theorem cw_step {N mb n : Nat} (hbl : Spec.RsaKeyGen.bitLength (N - 1) = mb) (hm : 1 ≤ mb) {r : List Byte} {u : Nat}
    (h : u + (mb + 7) / 8 ≤ r.length) :
    checkWitnesses N (n + 1) (r.drop u) =
      if 2 ≤ wA mb r u ∧ wA mb r u < N - 1 then
        (if Spec.Ffdh.mrRound N (wA mb r u) then checkWitnesses N n (r.drop (u + (mb + 7) / 8))
          else some (false, r.drop (u + (mb + 7) / 8)))
      else checkWitnesses N (n + 1) (r.drop (u + (mb + 7) / 8)) := by
  have hw : Spec.Ffdh.witnessOctets N = (mb + 7) / 8 := by simp only [Spec.Ffdh.witnessOctets, hbl]
  rw [checkWitnesses_step (by rw [hw]; omega_arith), hw, hbl,
    ite_eq_left (show (mb + 7) / 8 ≤ (r.drop u).length by rw [List.length_drop]; omega_arith)]
  simp only [List.drop_drop]
  rfl

/-! ## The witnesses of a modulus -/

/-- At the head of the loop: `i` witnesses passed, `u` octets read, and
`res` what the rest of the tape gives. -/
structure MrSt (p : PP) (mb N C : Nat) (res : Option (Bool × List Byte)) (i u : Nat) (s : State) : Prop where
  m : MSt p mb N C s
  used : word s.mem p.B 152 = BitVec.ofNat 64 u
  idx : word s.mem p.B 176 = BitVec.ofNat 64 i
  stat : word s.mem p.B 160 = BitVec.ofNat 64 4
  ul : u ≤ p.r.length
  ik : i < C
  rest : checkWitnesses N (C - i) (p.r.drop u) = res

/-- After the loop. -/
def MrEnd (p : PP) (mb N C : Nat) (res : Option (Bool × List Byte)) (t : State) : Prop :=
  MSt p mb N C t ∧ (res = none → word t.mem p.B 160 = BitVec.ofNat 64 0) ∧
    ∀ b rest, res = some (b, rest) → word t.mem p.B 160 = BitVec.ofNat 64 (if b then 1 else 2) ∧
      ∃ u, u ≤ p.r.length ∧ rest = p.r.drop u ∧ word t.mem p.B 152 = BitVec.ofNat 64 u

theorem stat_zero {n : Nat} (hn : n < 2 ^ 60) :
    (BitVec.ofNat 64 n - BitVec.ofNat 64 4 == 0) = decide (n = 4) := by
  by_cases h : n = 4
  · subst h; decide
  · rw [decide_eq_false h]
    apply Bool.eq_false_iff.mpr
    intro he
    have := congrArg BitVec.toNat (beq_iff_eq.mp he)
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
    have h0 : (0 : BitVec 64).toNat = 0 := rfl
    rw [h0] at this
    omega_arith

/-- Between the draw and the test of `hStat`. -/
def MrMid (p : PP) (mb N i u C : Nat) (t : State) : Prop :=
  MSt p mb N C t ∧ ((p.r.length < u + (mb + 7) / 8 ∧ word t.mem p.B 160 = BitVec.ofNat 64 0) ∨
    (u + (mb + 7) / 8 ≤ p.r.length ∧ word t.mem p.B 152 = BitVec.ofNat 64 (u + (mb + 7) / 8) ∧
      word t.mem p.B 160 = BitVec.ofNat 64 (dStat N C i (wA mb p.r u)) ∧
      word t.mem p.B 176 = BitVec.ofNat 64 (dIdx N i (wA mb p.r u))))

theorem sltu_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (if BitVec.ofNat 64 a < BitVec.ofNat 64 b then (1 : BitVec 64) else 0) =
      BitVec.ofNat 64 (if a < b then 1 else 0) := by
  have e : (BitVec.ofNat 64 a < BitVec.ofNat 64 b) ↔ a < b := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  by_cases h : a < b
  · rw [ite_eq_left (e.mpr h), ite_eq_left h]; rfl
  · rw [ite_eq_right (fun h' => h (e.mp h')), ite_eq_right h]; rfl

/-- The head's block: `t4 = 1` exactly when the tape is short. -/
theorem mrHeadBlk_ok {p : PP} {mb N : Nat} {res : Option (Bool × List Byte)} {i u : Nat} {s : State}
    (h : MrSt p mb N C res i u s) :
    WP isa (.block tapeShort) s fun t =>
      ((t.gpr .t4 = BitVec.ofNat 64 (if p.r.length - u < (mb + 7) / 8 then 1 else 0) ∧ t.mem = s.mem) ∧
        Keep [.t2, .t3, .t4] s t) ∧ t.sp = s.sp := by
  have hrl := h.m.st.dims.rl
  have hm2 := h.m.mb2
  have hb2 := h.m.st.dims.b2
  have hul := h.ul
  have hKw := h.m.ph.kW
  have hU := h.used
  have st := h.m.st
  simp only [word, off, Impl.MillerRabin.RISCV64.Search.hK, Nat.reduceMul] at hKw hU
  have hsub : BitVec.ofNat 64 p.r.length - BitVec.ofNat 64 u = BitVec.ofNat 64 (p.r.length - u) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_arith
  refine WP.rdwr (WP.keep [.t2, .t3, .t4] ?_ (by rfl) (by rfl)) |>.mono fun t ⟨a, _, _, b⟩ => ⟨a, b⟩
  simp only [tapeShort, ldh, hRandLen, hUsed, Impl.MillerRabin.RISCV64.Search.hK]
  brun [st.s6, st.ld (d := 144) (by decide), st.ld (d := 152) (by decide), st.ld (d := 216) (by decide),
    st.al (d := 144) (by decide) (by decide), st.al (d := 152) (by decide) (by decide),
    st.al (d := 216) (by decide) (by decide), st.args.rlen', hU, hKw, hsub,
    sltu_ofNat (show p.r.length - u < 2 ^ 64 by omega_arith) (show (mb + 7) / 8 < 2 ^ 64 by omega_arith)]

/-- The head: room for a witness, and the draw if there is. -/
theorem mrHead_ok {R : RoundImpl} {p : PP} {mb N : Nat} {res : Option (Bool × List Byte)}
    {i u : Nat} {s : State} (h : MrSt p mb N C res i u s) :
    WP isa (.seq (.block tapeShort)
      (.ite (.nonzero .t4) (.block [.li .t2 0, sth .t2 hStat]) (draw R.name R.code))) s (MrMid p mb N i u C) := by
  have hrl := h.m.st.dims.rl
  have hm2 := h.m.mb2
  have hb2 := h.m.st.dims.b2
  have hul := h.ul
  refine WP.seq (WP.mono (mrHeadBlk_ok h) fun s₂ ⟨⟨⟨a4, m12⟩, k12⟩, sp12⟩ => ?_)
  refine WP.ite (decide ((if p.r.length - u < (mb + 7) / 8 then 1 else 0) ≠ 0))
    (eval_nonzero_ofNat s₂ .t4 (by split <;> decide) a4) (fun hb => ?_) (fun hb => ?_)
  · -- No room: `hStat := 0`.
    have hr : p.r.length < u + (mb + 7) / 8 := by
      by_contra hc; simp only [decide_eq_true_eq] at hb; rw [ite_eq_right (by omega_arith)] at hb; exact hb rfl
    have st₂ : St p s₂ := h.m.st.step (by rw [m12]; exact Frm.refl _ _ _) k12 sp12
    have l160 : InRegions s₂.wr (p.B + BitVec.ofNat 64 160) 8 := st₂.st (d := 160) (by decide)
    have a160 := st₂.al (d := 160) (by decide) (by decide)
    refine WP.mono (WP.rdwr (WP.keep [.t2] (Q := fun t => t.mem = s₂.mem.writeW (p.B + BitVec.ofNat 64 160)
      (BitVec.ofNat 64 0)) (by simp only [sth, hStat]; brun [st₂.s6, l160, a160, exec_li (show imm12 0 by decide)])
      (by rfl) (by rfl))) fun t ⟨⟨tm, kt⟩, _, _, tsp⟩ => ?_
    have kt' := k12.trans kt
    have hf : Frm p.B [(160, 8)] s.mem t.mem := by
      rw [tm, m12]
      exact frm_writeW (a := 160) (Frm.refl _ _ _) _ ⟨_, List.mem_singleton_self _, by decide, by decide⟩ (by decide)
    have hfr : ∀ r ∈ [((160 : Nat), (8 : Nat))], Free (wOf mb) r := fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact Or.inl ⟨by simp, rfl⟩
    refine ⟨h.m.frm hf hfr kt' (tsp.trans sp12) (by decide) (kt'.gpr (by decide)) (kt'.gpr (by decide))
      (kt'.gpr (by decide)) (kt'.gpr (by decide)), Or.inl ⟨hr, ?_⟩⟩
    simp only [word, off]; rw [tm, Mem.readW_writeW_self64]
  · -- A draw.
    have hr : u + (mb + 7) / 8 ≤ p.r.length := by
      by_contra hc; simp only [decide_eq_false_iff_not, Decidable.not_not] at hb
      rw [ite_eq_left (by omega_arith)] at hb; exact absurd hb (by decide)
    have M₂ : MSt p mb N C s₂ := h.m.frm (rs := []) (by rw [m12]; exact Frm.refl _ _ _) (by simp) k12 sp12 (by decide)
      (k12.gpr (by decide)) (k12.gpr (by decide)) (k12.gpr (by decide)) (k12.gpr (by decide))
    refine WP.mono (draw_ok M₂ (by rw [m12]; exact h.used) hr (by rw [m12]; exact h.idx)
      (by rw [m12]; exact h.stat) (by have := h.ik; have := h.m.ph.k2; omega_arith))
      fun t ⟨mt, ut, st, it⟩ => ⟨mt, Or.inr ⟨hr, ut, st, it⟩⟩

/-- Whether the witness loop goes on after the witness at `u`, `i` passed. -/
def mrGo (r : List Byte) (mb N i u C : Nat) : Bool :=
  decide (u + (mb + 7) / 8 ≤ r.length) &&
    (!decide (2 ≤ wA mb r u ∧ wA mb r u < N - 1) ||
      (Proof.MillerRabin.Round.round N (wA mb r u) && decide (i + 1 < C)))

/-- An iteration: `hStat` tested after the head. -/
theorem mrIter_ok {R : RoundImpl} {p : PP} {mb N : Nat} {res : Option (Bool × List Byte)}
    {i u : Nat} {s : State} (hbl : Spec.RsaKeyGen.bitLength (N - 1) = mb) (h : MrSt p mb N C res i u s) :
    WP isa (.seq (.block tapeShort)
      (.seq (.ite (.nonzero .t4) (.block [.li .t2 0, sth .t2 hStat]) (draw R.name R.code))
        (.block [ldh .t2 hStat, .addi .t2 .t2 (-4)]))) s fun t =>
      isa.eval (.zero .t2) t = some (mrGo p.r mb N i u C) ∧ (mrGo p.r mb N i u C = false → MrEnd p mb N C res t) ∧
      (mrGo p.r mb N i u C = true → MrSt p mb N C res (dIdx N i (wA mb p.r u)) (u + (mb + 7) / 8) t) := by
  have hm1 := h.m.mb1
  have hik := h.ik
  have hN3 := h.m.prep.c3
  have hodd := h.m.prep.odd
  have hK64 : C ≤ 128 := h.m.ph.k2
  have hres := h.rest
  rw [show C - i = (C - i - 1) + 1 by omega_arith] at hres
  refine WP.assoc (WP.seq (WP.mono (mrHead_ok h) fun t ⟨M, hmid⟩ => ?_))
  have l160 : InRegions (t.rd ++ t.wr) (p.B + BitVec.ofNat 64 160) 8 := M.st.ld (d := 160) (by decide)
  have a160 := M.st.al (d := 160) (by decide) (by decide)
  refine WP.mono (WP.rdwr (WP.keep [.t2] (Q := fun v => v.gpr .t2 = word t.mem p.B 160 - BitVec.ofNat 64 4 ∧
      v.mem = t.mem) (by simp only [ldh, hStat]; brun [M.st.s6, l160, a160]) (by rfl) (by rfl)))
    fun v ⟨⟨⟨v3, vm⟩, vk⟩, _, _, vsp⟩ => ?_
  have M' : MSt p mb N C v := M.frm (rs := []) (by rw [vm]; exact Frm.refl _ _ _) (by simp) vk vsp (by decide)
    (vk.gpr (by decide)) (vk.gpr (by decide)) (vk.gpr (by decide)) (vk.gpr (by decide))
  have hw : ∀ d, word v.mem p.B d = word t.mem p.B d := fun d => by rw [vm]
  have ev : ∀ k, k < 2 ^ 60 → word t.mem p.B 160 = BitVec.ofNat 64 k →
      isa.eval (.zero .t2) v = some (decide (k = 4)) := fun k hk he => by
    rw [eval_zero, v3, he, stat_zero hk]
  have hm : 1 ≤ mb := by omega_arith
  rcases hmid with ⟨hr, h0⟩ | ⟨hr, hu, hs, hi⟩
  · -- No room for a witness.
    rw [cw_short hbl hm hr] at hres
    have hg : mrGo p.r mb N i u C = false := by
      simp only [mrGo, Bool.and_eq_false_iff, decide_eq_false_iff_not]; exact Or.inl (by omega_arith)
    rw [hg]
    refine ⟨(ev 0 (by decide) h0).trans (by decide), fun _ => ⟨M', fun _ => by rw [hw]; exact h0, fun b rest hb => ?_⟩,
      fun h => absurd h (by decide)⟩
    rw [← hres] at hb; cases hb
  rw [cw_step hbl hm hr] at hres
  have hround := mr_round_eq (wA mb p.r u) hN3 hodd
  simp only [dStat, dIdx, mrGo, hround, decide_eq_true hr, Bool.true_and] at hs hi ⊢
  generalize wA mb p.r u = a at hs hi hres ⊢
  by_cases hrg : 2 ≤ a ∧ a < N - 1
  · simp only [hrg.1, hrg.2, and_self, true_and, ↓reduceIte, decide_true, Bool.not_true, Bool.false_or]
      at hs hi hres ⊢
    by_cases hmr : Spec.Ffdh.mrRound N a = true
    · simp only [hmr, ↓reduceIte, Bool.true_and] at hs hi hres ⊢
      by_cases hk : i + 1 < C
      · simp only [hk, ↓reduceIte, decide_true] at hs ⊢
        refine ⟨(ev 4 (by decide) hs).trans (by decide), fun h => absurd h (by decide),
          fun _ => ⟨M', by rw [hw]; exact hu, by rw [hw]; exact hi, by rw [hw]; exact hs, hr, hk, ?_⟩⟩
        rw [show C - (i + 1) = C - i - 1 by omega_arith]; exact hres
      · simp only [hk, ↓reduceIte, decide_false] at hs ⊢
        rw [show C - i - 1 = 0 by omega_arith, checkWitnesses] at hres
        refine ⟨(ev 1 (by decide) hs).trans (by decide), fun _ => ⟨M', fun hn => (by rw [← hres] at hn; cases hn),
          fun b rest hb => ?_⟩, fun h => absurd h (by decide)⟩
        rw [← hres, Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        exact ⟨by rw [hw]; exact hs, u + (mb + 7) / 8, hr, rfl, by rw [hw]; exact hu⟩
    · simp only [hmr, Bool.false_eq_true, ↓reduceIte, Bool.false_and] at hs hi hres ⊢
      refine ⟨(ev 2 (by decide) hs).trans (by decide), fun _ => ⟨M', fun hn => (by rw [← hres] at hn; cases hn),
        fun b rest hb => ?_⟩, fun h => absurd h (by decide)⟩
      rw [← hres, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact ⟨by rw [hw]; exact hs, u + (mb + 7) / 8, hr, rfl, by rw [hw]; exact hu⟩
  · have hrg' : ¬(2 ≤ a ∧ a < N - 1 ∧ Spec.Ffdh.mrRound N a = true) := fun h => hrg ⟨h.1, h.2.1⟩
    simp only [hrg, hrg', ↓reduceIte, decide_false, Bool.not_false, Bool.true_or] at hs hi hres ⊢
    refine ⟨(ev 4 (by decide) hs).trans (by decide), fun h => absurd h (by decide),
      fun _ => ⟨M', by rw [hw]; exact hu, by rw [hw]; exact hi, by rw [hw]; exact hs, hr, hik, ?_⟩⟩
    rw [show C - i = C - i - 1 + 1 by omega_arith]; exact hres

/-- The witness loop's start: `hIdx := 0`, `hStat := 4`. -/
theorem mrInit_ok {p : PP} {mb N u : Nat} {s : State} (h : MSt p mb N C s)
    (hu : word s.mem p.B 152 = BitVec.ofNat 64 u) (hul : u ≤ p.r.length) :
    WP isa (.block [.li .t2 0, sth .t2 hIdx, .li .t2 4, sth .t2 hStat]) s
      (MrSt p mb N C (checkWitnesses N C (p.r.drop u)) 0 u) := by
  have hm1 := h.mb1
  have st := h.st
  refine WP.mono (WP.rdwr (WP.keep [.t2] (Q := fun t => t.mem = (s.mem.writeW (p.B + BitVec.ofNat 64 176)
      (BitVec.ofNat 64 0)).writeW (p.B + BitVec.ofNat 64 160) (BitVec.ofNat 64 4))
      (by simp only [sth, hIdx, hStat]
          brun [st.s6, st.st (d := 160) (by decide), st.st (d := 176) (by decide),
            st.al (d := 160) (by decide) (by decide), st.al (d := 176) (by decide) (by decide),
            exec_li (show imm12 0 by decide), exec_li (show imm12 4 by decide)])
      (by rfl) (by rfl))) fun t ⟨⟨tm, kt⟩, _, _, tsp⟩ => ?_
  have hf : Frm p.B [(176, 8), (160, 8)] s.mem t.mem := by
    rw [tm]
    exact frm_writeW (frm_writeW (Frm.refl _ _ _) _ ⟨(176, 8), by simp, by decide, by decide⟩ (by decide)) _
      ⟨(160, 8), by simp, by decide, by decide⟩ (by decide)
  have hfr : ∀ r ∈ [((176 : Nat), (8 : Nat)), (160, 8)], Free (wOf mb) r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Or.inl ⟨by simp, rfl⟩
  have M := h.frm hf hfr kt tsp (by decide) (kt.gpr (by decide)) (kt.gpr (by decide)) (kt.gpr (by decide))
    (kt.gpr (by decide))
  have t152 : word t.mem p.B 152 = BitVec.ofNat 64 u := by
    simp only [word, off] at hu ⊢
    rw [tm, rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
      rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
    exact hu
  have t160 : word t.mem p.B 160 = BitVec.ofNat 64 4 := by
    simp only [word, off]; rw [tm, Mem.readW_writeW_self64]
  have t176 : word t.mem p.B 176 = BitVec.ofNat 64 0 := by
    simp only [word, off]; rw [tm, rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), Mem.readW_writeW_self64]
  have hK : 0 < C := h.ph.k1
  exact ⟨M, t152, t176, t160, hul, hK, by rw [Nat.sub_zero]⟩

/-- The witnesses of `N`, drawn from octet `u` of the tape. -/
theorem millerRabin_ok {R : RoundImpl} {p : PP} {mb N u : Nat} {s : State}
    (hbl : Spec.RsaKeyGen.bitLength (N - 1) = mb) (h : MSt p mb N C s)
    (hu : word s.mem p.B 152 = BitVec.ofNat 64 u) (hul : u ≤ p.r.length) :
    WP isa (millerRabin R.name R.code) s
      (MrEnd p mb N C (checkWitnesses N C (p.r.drop u))) := by
  have hm1 := h.mb1
  refine WP.seq (WP.mono (mrInit_ok h hu hul) fun t ht => ?_)
  show WP isa (.loop _ _) t _
  refine WP.loop (fun m v => ∃ i u', m = p.r.length + 1 - u' ∧
      MrSt p mb N C (checkWitnesses N C (p.r.drop u)) i u' v) ?_ (p.r.length + 1 - u) t ?_
  · rintro m v ⟨i, u', rfl, hv⟩
    have hit := mrIter_ok (R := R) hbl hv
    refine WP.mono hit fun w ⟨he, hend, hgo⟩ => ?_
    cases hg : mrGo p.r mb N i u' C
    · exact Or.inl ⟨by rw [he, hg], hend hg⟩
    · have hw := hgo hg
      have hul' := hw.ul
      have hlt : p.r.length + 1 - (u' + (mb + 7) / 8) < p.r.length + 1 - u' := by omega_using [hul', hm1]
      exact Or.inr ⟨by rw [he, hg], p.r.length + 1 - (u' + (mb + 7) / 8), hlt, _, u' + (mb + 7) / 8, rfl, hw⟩
  · exact ⟨0, u, rfl, ht⟩

/-! ## The test of a modulus -/

/-- `montPrep`: the Montgomery constants of the modulus `N` in array 0. -/
theorem montPrep_mst {p : PP} {mb N : Nat} {s : State} (h : St p s) (hp : Ph p mb C s)
    (hm1 : 511 ≤ mb) (hm2 : mb ≤ p.bits) (hn : wv s.mem p.B (slot (wOf mb) 0) (wOf mb) = N)
    (hodd : N % 2 = 1) (hN3 : 3 ≤ N) :
    WP isa montPrep s fun t => MSt p mb N C t ∧ Frm p.B (mutR p.n) s.mem t.mem ∧
      word t.mem p.B 152 = word s.mem p.B 152 := by
  have hdn := h.dims.n
  have hb2 := h.dims.b2
  have hw8 : 8 ≤ wOf mb := by simp only [wOf]; omega_arith
  have hw128 : wOf mb ≤ 128 := by simp only [wOf]; omega_arith
  have es : ∀ j, slot (wOf mb) j = 256 + j * (8 * (wOf mb + 2)) := fun _ => rfl
  have e1 := es 1; have e4 := es 4; have e6 := es 6; have e8 := es 8; have e9 := es 9; have e11 := es 11
  have e27 := es 27; have e28 := es 28
  have hZn : p.Z = 8 * p.n := rfl
  have hZ : slot (wOf mb) 28 + saveBytes ≤ p.Z := by
    have hwd : wOf mb = (mb + 63) / 64 := rfl
    have hL : p.L = (p.bits + 7) / 8 := rfl
    simp only [saveBytes, PP.Z]; omega_arith
  have env : Env s p.B (8 * p.n) (wOf mb) := ⟨h.scr, hp.a7, hp.s5, hp.t0, h.s6, by omega_arith, hw128,
    by simp only [PP.Z] at hZ; omega_arith⟩
  have harr : A s.mem p.B (wOf mb) 0 = N := by rw [A, Pre.wordsVal_eq_wv]; exact hn
  refine WP.mono (WP.rdwr (VG.Proof.MillerRabin.RISCV64.Search.montPrep_ok env harr hodd hN3))
    fun t ⟨⟨⟨envt, nt, inv, it1, r1, r9, r10, e, l, outs⟩, k⟩, _, _, tsp⟩ => ?_
  have fo : Frm p.B (VG.Proof.MillerRabin.RISCV64.Search.mpRanges (wOf mb)) s.mem t.mem := outs
  have hf : Frm p.B (mutR p.n) s.mem t.mem := Frm.toMut fo fun r hr => by
    simp only [VG.Proof.MillerRabin.RISCV64.Search.mpRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact InMut.hdr (i := 7) (by decide)
    all_goals (try simp only [Impl.MillerRabin.RISCV64.aE]); exact InMut.arrays (by omega_arith) (by omega_arith)
  have st := h.step hf k tsp (by decide)
  have ew : ∀ d, d + 8 ≤ 56 ∨ (64 ≤ d ∧ d + 8 ≤ 256) → word t.mem p.B d = word s.mem p.B d := fun d hd =>
    fo.word_eq (fun r hr => by
      simp only [VG.Proof.MillerRabin.RISCV64.Search.mpRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [Impl.MillerRabin.RISCV64.aE] <;> omega_arith)
      (by omega_arith)
  have ph : Ph p mb C t := ⟨envt.a7, envt.t0, envt.s5, (ew _ (by simp only [hMb]; omega_arith)).trans hp.mbW,
    (ew _ (by simp only [Impl.MillerRabin.RISCV64.Search.hK]; omega_arith)).trans hp.kW,
    (ew _ (by simp only [hW]; omega_arith)).trans hp.wW, (ew _ (by simp only [hStride]; omega_arith)).trans hp.strideW,
    fun j hj => (ew _ (by omega_arith)).trans (hp.arrW j hj),
    (ew _ (by simp only [hChecks]; omega_arith)).trans hp.checksW, hp.k1, hp.k2,
    (ew _ (by simp only [hTop]; omega_arith)).trans hp.topW⟩
  refine ⟨⟨st, ph, ⟨envt, (ew 0 (by omega_arith)).trans h.args.wsLen, (ew 48 (by omega_arith)).trans hp.wW,
    (ew 224 (by omega_arith)).trans hp.strideW, fun j hj => (ew _ (by omega_arith)).trans (hp.arrW j hj), nt, hN3, hodd,
    inv, it1, r1, r9, r10, e, l⟩, hm1, hm2⟩, hf, ew 152 (by omega_arith)⟩

/-- Before a modulus's Montgomery constants: what the test asks. -/
structure TCPre (p : PP) (mb N u C : Nat) (s : State) : Prop where
  st : St p s
  ph : Ph p mb C s
  mb1 : 511 ≤ mb
  mb2 : mb ≤ p.bits
  n : wv s.mem p.B (slot (wOf mb) 0) (wOf mb) = N
  bl : Spec.RsaKeyGen.bitLength (N - 1) = mb
  odd : N % 2 = 1
  n3 : 3 ≤ N
  used : word s.mem p.B 152 = BitVec.ofNat 64 u
  ul : u ≤ p.r.length

theorem TCPre.core {R : RoundImpl} {p : PP} {mb N u : Nat} {s : State} (h : TCPre p mb N u C s) :
    WP isa (.seq montPrep (millerRabin R.name R.code)) s
      (MrEnd p mb N C (checkWitnesses N C (p.r.drop u))) :=
  WP.seq (WP.mono (montPrep_mst h.st h.ph h.mb1 h.mb2 h.n h.odd h.n3) fun _ ⟨M, _, h152⟩ =>
    millerRabin_ok h.bl M (h152.trans h.used) h.ul)

/-- The low `k` words of a number below `2^(64 k)` are the number. -/
theorem wv_low {m : Mem} {B : Addr} {o w k v : Nat} (h : wv m B o w = v) (hk : k ≤ w)
    (hv : v < 2 ^ (64 * k)) : wv m B o k = v := by
  have e := wv_add m B o k (w - k)
  rw [show k + (w - k) = w by omega_arith, h] at e
  generalize 2 ^ (64 * k) = P at e hv
  generalize wv m B (o + 8 * k) (w - k) = hi at e
  rcases Nat.eq_zero_or_pos hi with h0 | hpos
  · rw [h0, Nat.mul_zero, Nat.add_zero] at e; exact e.symm
  · have := Nat.le_mul_of_pos_right P hpos; omega_arith

/-- `Ph` survives a change of memory that keeps the header. -/
theorem Ph.keepHdr {p : PP} {mb : Nat} {s t : State} (h : Ph p mb C s)
    (r7 : t.gpr .a7 = s.gpr .a7) (r0 : t.gpr .t0 = s.gpr .t0) (r5 : t.gpr .s5 = s.gpr .s5)
    (hw : ∀ d, d + 8 ≤ 256 → word t.mem p.B d = word s.mem p.B d) : Ph p mb C t :=
  ⟨r7.trans h.a7, r0.trans h.t0, r5.trans h.s5, (hw 248 (by decide)).trans h.mbW,
    (hw 216 (by decide)).trans h.kW, (hw 48 (by decide)).trans h.wW, (hw 224 (by decide)).trans h.strideW,
    fun j hj => (hw _ (by omega_arith)).trans (h.arrW j hj), (hw 168 (by decide)).trans h.checksW, h.k1, h.k2,
    (hw 192 (by decide)).trans h.topW⟩

/-- The set-up of q's test: its working space. -/
theorem qPrep_ok {p : PP} {s : State} {c u : Nat} (h : St p s)
    (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)))
    (hq : wv s.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) = (c - 1) / 2) (hqo : ((c - 1) / 2) % 2 = 1)
    (hu : word s.mem p.B 152 = BitVec.ofNat 64 u) (hul : u ≤ p.r.length) :
    WP isa (.seq (phase true) (.block [])) s
      (TCPre p (p.bits - 1) ((c - 1) / 2) u (Spec.Ffdh.primeChecks (p.bits - 1))) := by
  have hb1 := h.dims.b1
  have hb2 := h.dims.b2
  have hdn := h.dims.n
  have hn' := h.dims.n'
  obtain ⟨hpo, hl, hu'⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := p.bits) (by omega_arith)
    (Spec.Rsa.os2ip (p.r.take p.L))
  rw [← hc] at hpo hl hu'
  obtain ⟨hql, hqu⟩ := VG.Proof.Ffdh.ParameterCandidate.half_shape (by omega_arith) hpo hl hu'
  have hbl := VG.Proof.Ffdh.ParameterCandidate.half_pred_bitLength (bits := p.bits) (by omega_arith)
    (Spec.Rsa.os2ip (p.r.take p.L)) (by rw [← hc]; exact hqo)
  rw [← hc] at hbl
  refine WP.seq (WP.mono (phase_ok h true) fun t ⟨⟨⟨st, ph, hf⟩, _⟩, _⟩ => ?_)
  simp only [mbOf, ↓reduceIte] at ph
  rw [WP.block_nil_iff]
  have hL : p.L = (p.bits + 7) / 8 := rfl
  have hwq : wOf (p.bits - 1) ≤ wOf p.bits := by simp only [wOf]; omega_arith
  refine ⟨st, ph, by omega_arith, by omega_arith, ?_, hbl, hqo, ?_, ?_, hul⟩
  · rw [slot_zero] at hq ⊢
    refine wv_low (w := wOf p.bits) ?_ hwq (Nat.lt_of_lt_of_le hqu (Nat.pow_le_pow_right (by decide) (by
      simp only [wOf]; omega_arith)))
    rw [hf.wv_eq (fun r hr => .inr (phR_low r hr)) (by simp only [wOf]; omega_arith)]
    exact hq
  · have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 2 ≤ p.bits - 2 by omega_arith)
    omega_arith
  · rw [hf.word_eq phR_used (by decide)]; exact hu

/-- The test of q, halved in array 0 in p's width. -/
theorem testQ_ok {R : RoundImpl} {p : PP} {s : State} {c u : Nat} (h : St p s)
    (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)))
    (hq : wv s.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) = (c - 1) / 2) (hqo : ((c - 1) / 2) % 2 = 1)
    (hu : word s.mem p.B 152 = BitVec.ofNat 64 u) (hul : u ≤ p.r.length) :
    WP isa (test true (.block []) R.name R.code) s
      (MrEnd p (p.bits - 1) ((c - 1) / 2) (Spec.Ffdh.primeChecks (p.bits - 1))
        (checkWitnesses ((c - 1) / 2) (Spec.Ffdh.primeChecks (p.bits - 1)) (p.r.drop u))) := by
  unfold test
  simp only [↓reduceIte]
  exact WP.assoc (WP.seq (WP.mono (qPrep_ok h hc hq hqo hu hul) fun _ ht =>
    WP.seq (WP.block_nil_iff.mpr ht.core)))

/-- The set-up of p's test: its working space, and p from the tape. -/
theorem pPrep_ok {p : PP} {s : State} {c u : Nat} (h : St p s)
    (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)))
    (hu : word s.mem p.B 152 = BitVec.ofNat 64 u) (hul : u ≤ p.r.length) (hL : p.L ≤ p.r.length) :
    WP isa (.seq (phase false) shapeP) s (TCPre p p.bits c u (Spec.Ffdh.primeChecks p.bits)) := by
  have hb1 := h.dims.b1
  have hb2 := h.dims.b2
  have hdn := h.dims.n
  obtain ⟨hpo, hl, _⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := p.bits) (by omega_arith)
    (Spec.Rsa.os2ip (p.r.take p.L))
  have hbl := (VG.Proof.Ffdh.ParameterCandidate.candidate_bitLength (bits := p.bits) (by omega_arith)
    (Spec.Rsa.os2ip (p.r.take p.L))).2
  rw [← hc] at hpo hl hbl
  refine WP.seq (WP.mono (phase_ok h false) fun t ⟨⟨⟨st, ph, hf⟩, _⟩, _⟩ => ?_)
  simp only [mbOf, Bool.false_eq_true, ↓reduceIte] at ph
  refine WP.mono (WP.rdwr (shapeP_ok st ph hL)) fun t₂ ⟨⟨⟨hn₂, f₂⟩, k₂⟩, _, _, sp₂⟩ => ?_
  have hLe : p.L = (p.bits + 7) / 8 := rfl
  have hw : wOf p.bits = (p.bits + 63) / 64 := rfl
  have hsl : slot (wOf p.bits) 0 = 256 := slot_zero _
  have hlow : ∀ d, d + 8 ≤ 256 → word t₂.mem p.B d = word t.mem p.B d := fun d hd =>
    f₂.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (by rw [hsl]; exact hd)) (by omega_arith)
  have st₂ : St p t₂ := st.step (Frm.toMut f₂ fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact InMut.arrays (by rw [hsl]) (by rw [hsl]; simp only [saveBytes]; omega_arith)) k₂ sp₂ (by decide)
  have ph₂ : Ph p p.bits (Spec.Ffdh.primeChecks p.bits) t₂ :=
    ph.keepHdr (k₂.gpr (by decide)) (k₂.gpr (by decide)) (k₂.gpr (by decide)) hlow
  refine ⟨st₂, ph₂, by omega_arith, Nat.le_refl _, by rw [hn₂, hc], hbl, hpo, ?_, ?_, hul⟩
  · have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 2 ≤ p.bits - 1 by omega_arith)
    omega_arith
  · rw [hlow 152 (by decide), hf.word_eq phR_used (by decide)]; exact hu

/-- `hChecks := C'`: the test's other data stay. -/
theorem TCPre.setChecks {C' : Nat} {p : PP} {mb N u : Nat} {s t : State} (h : TCPre p mb N u C s)
    (hm : t.mem = s.mem.writeW (p.B + BitVec.ofNat 64 168) (BitVec.ofNat 64 C')) {regs : List Reg}
    (k : Keep regs s t) (hsp : t.sp = s.sp) (h6 : Reg.s6 ∉ regs) (h7 : Reg.a7 ∉ regs) (h0 : Reg.t0 ∉ regs)
    (h5 : Reg.s5 ∉ regs) (c1 : 1 ≤ C') (c2 : C' ≤ 128) : TCPre p mb N u C' t := by
  have hdn := h.st.dims.n
  have hf : Frm p.B [(168, 8)] s.mem t.mem := by
    rw [hm]; exact frm_writeW (a := 168) (Frm.refl _ _ _) _ ⟨_, List.mem_singleton_self _, by decide, by decide⟩
      (by decide)
  have st := h.st.step (Frm.toMut hf fun r hr => by
    rw [List.mem_singleton.mp hr]; exact InMut.hdr (i := 21) (by decide)) k hsp h6
  have ew : ∀ d, d + 8 ≤ 168 ∨ 176 ≤ d → d + 8 ≤ 2 ^ 64 → word t.mem p.B d = word s.mem p.B d := fun d hd hd' =>
    hf.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; dsimp only; omega_arith) hd'
  have hp := h.ph
  have ph : Ph p mb C' t := ⟨(k.gpr h7).trans hp.a7, (k.gpr h0).trans hp.t0, (k.gpr h5).trans hp.s5,
    (ew _ (by simp only [hMb]; omega_arith) (by simp only [hMb]; omega_arith)).trans hp.mbW,
    (ew _ (by simp only [Impl.MillerRabin.RISCV64.Search.hK]; omega_arith)
      (by simp only [Impl.MillerRabin.RISCV64.Search.hK]; omega_arith)).trans hp.kW,
    (ew _ (by simp only [hW]; omega_arith) (by simp only [hW]; omega_arith)).trans hp.wW,
    (ew _ (by simp only [hStride]; omega_arith) (by simp only [hStride]; omega_arith)).trans hp.strideW,
    fun j hj => (ew _ (by omega_arith) (by omega_arith)).trans (hp.arrW j hj),
    by show t.mem.readW (p.B + BitVec.ofNat 64 168) 64 = _; rw [hm, Mem.readW_writeW_self64], c1, c2,
    (ew _ (by simp only [hTop]; omega_arith) (by simp only [hTop]; omega_arith)).trans hp.topW⟩
  refine ⟨st, ph, h.mb1, h.mb2, ?_, h.bl, h.odd, h.n3, (ew 152 (by decide) (by decide)).trans h.used, h.ul⟩
  have hb2 := h.st.dims.b2
  have hm2 := h.mb2
  rw [hf.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr, slot_zero]; exact .inr (by decide))
    (by rw [slot_zero]; simp only [wOf]; omega_arith)]
  exact h.n

/-- `firstCheck`: one witness. -/
theorem firstCheck_ok {p : PP} {mb N u : Nat} {s : State} (h : TCPre p mb N u C s) :
    WP isa firstCheck s (TCPre p mb N u 1) := by
  have l168 : InRegions s.wr (p.B + BitVec.ofNat 64 168) 8 := h.st.st (d := 168) (by decide)
  have a168 := h.st.al (d := 168) (by decide) (by decide)
  refine WP.mono (WP.rdwr (WP.keep [.t3] (Q := fun t =>
      t.mem = s.mem.writeW (p.B + BitVec.ofNat 64 168) (BitVec.ofNat 64 1))
    (by simp only [firstCheck, sth, hChecks]; brun [h.st.s6, l168, a168, exec_li (show imm12 1 by decide)])
    (by rfl) (by rfl))) fun t ⟨⟨tm, kt⟩, _, _, tsp⟩ => ?_
  exact h.setChecks tm kt tsp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `restChecks`: the witnesses but one. -/
theorem restChecks_ok {p : PP} {mb N u : Nat} {s : State} (h : TCPre p mb N u C s) (hC : 2 ≤ C) :
    WP isa restChecks s (TCPre p mb N u (C - 1)) := by
  have l168 : InRegions (s.rd ++ s.wr) (p.B + BitVec.ofNat 64 168) 8 := h.st.ld (d := 168) (by decide)
  have s168 : InRegions s.wr (p.B + BitVec.ofNat 64 168) 8 := h.st.st (d := 168) (by decide)
  have a168 := h.st.al (d := 168) (by decide) (by decide)
  have hc : s.mem.readW (p.B + BitVec.ofNat 64 168) 64 = BitVec.ofNat 64 C := h.ph.checksW
  have c2 := h.ph.k2
  have hC' : BitVec.ofNat 64 C - BitVec.ofNat 64 1 = BitVec.ofNat 64 (C - 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_arith
  refine WP.mono (WP.rdwr (WP.keep [.t3] (Q := fun t => t.mem = s.mem.writeW (p.B + BitVec.ofNat 64 168)
      (BitVec.ofNat 64 (C - 1)))
    (by simp only [restChecks, ldh, sth, hChecks]; brun [h.st.s6, l168, s168, a168, hc, hC'])
    (by rfl) (by rfl))) fun t ⟨⟨tm, kt⟩, _, _, tsp⟩ => ?_
  exact h.setChecks tm kt tsp (by decide) (by decide) (by decide) (by decide) (by omega_arith) (by omega_arith)

/-- A test of p, loaded again from the tape, its witness count changed by
`adjust` to `K`. -/
theorem testP_of {K : Nat} {R : RoundImpl} {adjust : Prog isa} {p : PP} {s : State} {c u : Nat}
    (hadj : ∀ {t : State}, TCPre p p.bits c u (Spec.Ffdh.primeChecks p.bits) t →
      WP isa adjust t (TCPre p p.bits c u K))
    (h : St p s) (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)))
    (hu : word s.mem p.B 152 = BitVec.ofNat 64 u) (hul : u ≤ p.r.length) (hL : p.L ≤ p.r.length) :
    WP isa (test false adjust R.name R.code) s (MrEnd p p.bits c K (checkWitnesses c K (p.r.drop u))) := by
  unfold test
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact WP.assoc (WP.seq (WP.mono (pPrep_ok h hc hu hul hL) fun _ ht =>
    WP.seq (WP.mono (hadj ht) fun _ ht' => ht'.core)))

/-- The test of p's first witness. -/
theorem testP1_ok {R : RoundImpl} {p : PP} {s : State} {c u : Nat} (h : St p s)
    (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)))
    (hu : word s.mem p.B 152 = BitVec.ofNat 64 u) (hul : u ≤ p.r.length) (hL : p.L ≤ p.r.length) :
    WP isa (test false firstCheck R.name R.code) s (MrEnd p p.bits c 1 (checkWitnesses c 1 (p.r.drop u))) :=
  testP_of (fun ht => firstCheck_ok ht) h hc hu hul hL

/-- The test of p's other witnesses. -/
theorem testPR_ok {R : RoundImpl} {p : PP} {s : State} {c u : Nat} (h : St p s)
    (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)))
    (hu : word s.mem p.B 152 = BitVec.ofNat 64 u) (hul : u ≤ p.r.length) (hL : p.L ≤ p.r.length) :
    WP isa (test false restChecks R.name R.code) s
      (MrEnd p p.bits c (Spec.Ffdh.primeChecks p.bits - 1)
        (checkWitnesses c (Spec.Ffdh.primeChecks p.bits - 1) (p.r.drop u))) :=
  testP_of (fun ht => restChecks_ok ht (by unfold Spec.Ffdh.primeChecks; split <;> decide)) h hc hu hul hL

/-! ## The results -/

/-- `hStat` into `t3`. -/
theorem statLoad_ok {p : PP} {mb N : Nat} {s : State} (M : MSt p mb N C s) :
    WP isa (.block [ldh .t3 hStat]) s fun t => MSt p mb N C t ∧ t.gpr .t3 = word s.mem p.B 160 ∧ t.mem = s.mem ∧
      Keep [.t3] s t := by
  have l160 : InRegions (s.rd ++ s.wr) (p.B + BitVec.ofNat 64 160) 8 := M.st.ld (d := 160) (by decide)
  have a160 := M.st.al (d := 160) (by decide) (by decide)
  refine WP.mono (WP.rdwr (WP.keep [.t3] (Q := fun t => t.gpr .t3 = word s.mem p.B 160 ∧ t.mem = s.mem)
    (by simp only [ldh, hStat]; brun [M.st.s6, l160, a160]) (by rfl) (by rfl))) fun t ⟨⟨⟨t3, tm⟩, k⟩, _, _, tsp⟩ => ?_
  exact ⟨M.frm (rs := []) (by rw [tm]; exact Frm.refl _ _ _) (by simp) k tsp (by decide) (k.gpr (by decide))
    (k.gpr (by decide)) (k.gpr (by decide)) (k.gpr (by decide)), t3, tm, k⟩

/-- `t3 - 1`, in `MSt`. -/
theorem sub1_ok {p : PP} {mb N v : Nat} {s : State} (M : MSt p mb N C s) (h3 : s.gpr .t3 = BitVec.ofNat 64 v) :
    WP isa (.block [.addi .t3 .t3 (-1)]) s fun t => MSt p mb N C t ∧ t.gpr .t3 = BitVec.ofNat 64 v - BitVec.ofNat 64 1 ∧
      t.mem = s.mem := by
  refine WP.mono (WP.rdwr (WP.keep [.t3] (Q := fun t => t.gpr .t3 = BitVec.ofNat 64 v - BitVec.ofNat 64 1 ∧
    t.mem = s.mem) (by brun [h3]) (by rfl) (by rfl))) fun t ⟨⟨⟨t3, tm⟩, k⟩, _, _, tsp⟩ => ?_
  exact ⟨M.frm (rs := []) (by rw [tm]; exact Frm.refl _ _ _) (by simp) k tsp (by decide) (k.gpr (by decide))
    (k.gpr (by decide)) (k.gpr (by decide)) (k.gpr (by decide)), t3, tm⟩

theorem stat_one {n : Nat} (hn : n < 2 ^ 60) :
    (BitVec.ofNat 64 n - BitVec.ofNat 64 1 == 0) = decide (n = 1) := by
  by_cases h : n = 1
  · subst h; decide
  · rw [decide_eq_false h]
    apply Bool.eq_false_iff.mpr
    intro he
    have := congrArg BitVec.toNat (beq_iff_eq.mp he)
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
    have h0 : (0 : BitVec 64).toNat = 0 := rfl
    rw [h0] at this
    omega_arith

/-- After p's test. -/
theorem pResult_ok {p : PP} {s : State} {c : Nat} {resP : Option (Bool × List Byte)}
    (hE : MrEnd p p.bits c C resP s) (hc : c < 2 ^ p.bits) :
    WP isa pResult s (CEnd p (resP.map fun x => (if x.1 then some c else none, x.2))) := by
  obtain ⟨M, hnone, hsome⟩ := hE
  unfold pResult
  refine WP.seq (WP.mono (statLoad_ok M) fun t ⟨Mt, t3, tm, _⟩ => ?_)
  have h152 : word t.mem p.B 152 = word s.mem p.B 152 := by rw [tm]
  rcases resP with _ | ⟨b, rest⟩
  · have h0 := hnone rfl
    refine WP.ite true (eval_zero_ofNat t .t3 (k := 0) (by decide) (t3.trans h0)) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact finEnd Mt.st (r := 0) (Or.inl rfl) rfl rfl rfl (VG.Proof.Bignum.ofNat_toNat64 _).symm
  · obtain ⟨hS, u, hul, rfl, hU⟩ := hsome b rest rfl
    have hU' : word t.mem p.B 152 = BitVec.ofNat 64 u := h152.trans hU
    cases b
    · refine WP.ite false (eval_zero_ofNat t .t3 (k := 2) (by decide) (t3.trans hS)) (fun h => absurd h (by decide))
        (fun _ => ?_)
      refine WP.seq (WP.mono (sub1_ok Mt (t3.trans hS)) fun v ⟨Mv, v3, vm⟩ => ?_)
      refine WP.ite false (by rw [eval_zero, v3]; decide) (fun h => absurd h (by decide)) (fun _ => ?_)
      refine finEnd Mv.st (r := 2) (v := u) (Or.inr rfl) rfl rfl ?_ (by rw [vm]; exact hU')
      simp only [Option.map_some, Bool.false_eq_true, ↓reduceIte, usedOf, List.length_drop, Nat.reduceEqDiff]
      omega_arith
    · refine WP.ite false (eval_zero_ofNat t .t3 (k := 1) (by decide) (t3.trans hS)) (fun h => absurd h (by decide))
        (fun _ => ?_)
      refine WP.seq (WP.mono (sub1_ok Mt (t3.trans hS)) fun v ⟨Mv, v3, vm⟩ => ?_)
      refine WP.ite true (by rw [eval_zero, v3]; decide) (fun _ => ?_) (fun h => absurd h (by decide))
      have hn : wv v.mem p.B 256 (wOf p.bits) = c := by
        have := Mv.prep.n
        rw [A, Pre.wordsVal_eq_wv, slot_zero] at this
        exact this
      exact pEnd Mv.st Mv.ph hn hc (by rw [vm]; exact hU') hul

/-- After a failed test of q. -/
theorem qResult_ok {p : PP} {s : State} {mb N : Nat} {resQ : Option (Bool × List Byte)}
    (hE : MrEnd p mb N C resQ s) (hq : ∀ rest, resQ ≠ some (true, rest)) :
    WP isa qResult s (CEnd p (resQ.map fun x => (none, x.2))) := by
  obtain ⟨M, hnone, hsome⟩ := hE
  unfold qResult
  refine WP.seq (WP.mono (statLoad_ok M) fun t ⟨Mt, t3, tm, _⟩ => ?_)
  rcases resQ with _ | ⟨b, rest⟩
  · refine WP.ite true (eval_zero_ofNat t .t3 (k := 0) (by decide) (t3.trans (hnone rfl))) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact finEnd Mt.st (r := 0) (Or.inl rfl) rfl rfl rfl (VG.Proof.Bignum.ofNat_toNat64 _).symm
  · cases b
    · obtain ⟨hS, u, hul, rfl, hU⟩ := hsome false rest rfl
      refine WP.ite false (eval_zero_ofNat t .t3 (k := 2) (by decide) (t3.trans hS)) (fun h => absurd h (by decide))
        (fun _ => ?_)
      refine finEnd Mt.st (r := 2) (v := u) (Or.inr rfl) rfl rfl ?_ (by rw [tm]; exact hU)
      simp only [Option.map_some, ↓reduceIte, usedOf, List.length_drop, Nat.reduceEqDiff]
      omega_arith
    · exact absurd rfl (hq rest)

/-- `hStat` against 1. -/
theorem stat1_ok {p : PP} {mb N v : Nat} {s : State} (M : MSt p mb N C s) (hv : v < 2 ^ 60)
    (hS : word s.mem p.B 160 = BitVec.ofNat 64 v) :
    WP isa (.block [ldh .t3 hStat, .addi .t3 .t3 (-1)]) s fun t =>
      isa.eval (.zero .t3) t = some (decide (v = 1)) ∧ MSt p mb N C t ∧ t.mem = s.mem := by
  have l160 : InRegions (s.rd ++ s.wr) (p.B + BitVec.ofNat 64 160) 8 := M.st.ld (d := 160) (by decide)
  have a160 := M.st.al (d := 160) (by decide) (by decide)
  refine WP.mono (WP.rdwr (WP.keep [.t3] (Q := fun t => t.gpr .t3 = BitVec.ofNat 64 v - BitVec.ofNat 64 1 ∧ t.mem = s.mem)
    (by simp only [ldh, hStat]; brun [M.st.s6, l160, a160, show s.mem.readW (p.B + BitVec.ofNat 64 160) 64 =
      BitVec.ofNat 64 v from hS]) (by rfl) (by rfl))) fun t ⟨⟨⟨t3, tm⟩, k⟩, _, _, tsp⟩ => ?_
  exact ⟨by rw [eval_zero, t3, stat_one hv], M.frm (rs := []) (by rw [tm]; exact Frm.refl _ _ _) (by simp) k tsp
    (by decide) (k.gpr (by decide)) (k.gpr (by decide)) (k.gpr (by decide)) (k.gpr (by decide)), tm⟩

/-- After a test that ended with `res`: the end of the candidate when it did
not pass (`qResult`), else `cont` from octet `u` of the tape. -/
theorem stage_ok {p : PP} {mb N : Nat} {t₁ : State} {res : Option (Bool × List Byte)}
    {k : List Byte → Option (Option Nat × List Byte)} {cont : Prog isa} (e₁ : MrEnd p mb N C res t₁)
    (hcont : ∀ u t₂, u ≤ p.r.length → res = some (true, p.r.drop u) → MSt p mb N C t₂ → t₂.mem = t₁.mem →
      word t₂.mem p.B 152 = BitVec.ofNat 64 u → WP isa cont t₂ (CEnd p (k (p.r.drop u)))) :
    WP isa (.seq (.block [ldh .t3 hStat, .addi .t3 .t3 (-1)]) (.ite (.zero .t3) cont qResult)) t₁
      (CEnd p (onPass res k)) := by
  obtain ⟨M₁, hnone, hsome⟩ := e₁
  rcases res with _ | ⟨b, rest⟩
  · refine WP.seq (WP.mono (stat1_ok M₁ (v := 0) (by decide) (hnone rfl)) fun t₂ ⟨hz, M₂, hm⟩ => ?_)
    refine WP.ite false hz (fun h => absurd h (by decide)) (fun _ => ?_)
    exact qResult_ok (resQ := none) ⟨M₂, fun _ => (by rw [hm]; exact hnone rfl), fun _ _ h => (by cases h)⟩
      (fun _ h => by cases h)
  · obtain ⟨hS, u, hul, rfl, hUu⟩ := hsome b rest rfl
    refine WP.seq (WP.mono (stat1_ok M₁ (v := if b then 1 else 2) (by cases b <;> decide) hS)
      fun t₂ ⟨hz, M₂, hm⟩ => ?_)
    cases b
    · refine WP.ite false hz (fun h => absurd h (by decide)) (fun _ => ?_)
      have e₂ : MrEnd p mb N C (some (false, p.r.drop u)) t₂ := by
        refine ⟨M₂, fun h => (by cases h), fun b' rest' h => ?_⟩
        cases h
        exact ⟨by rw [hm]; exact hS, u, hul, rfl, by rw [hm]; exact hUu⟩
      exact qResult_ok e₂ (fun _ h => by cases h)
    · refine WP.ite true hz (fun _ => ?_) (fun h => absurd h (by decide))
      exact hcont u t₂ hul rfl M₂ hm (by rw [hm]; exact hUu)

/-- q, from p in array 0. -/
theorem halveQ_from {K : Nat} {p : PP} {s : State} {c u : Nat} (M : MSt p p.bits c K s)
    (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)))
    (hU : word s.mem p.B 152 = BitVec.ofNat 64 u) :
    WP isa halveQ s fun t => St p t ∧ wv t.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) = (c - 1) / 2 ∧
      word t.mem p.B 152 = BitVec.ofNat 64 u := by
  have hb1 := M.st.dims.b1
  have hb2 := M.st.dims.b2
  have hdn := M.st.dims.n
  obtain ⟨hpo, _, _⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := p.bits) (by omega_arith)
    (Spec.Rsa.os2ip (p.r.take p.L))
  rw [← hc] at hpo
  have hsl : slot (wOf p.bits) 0 = 256 := slot_zero _
  have hLe : p.L = (p.bits + 7) / 8 := rfl
  have hwe : wOf p.bits = (p.bits + 63) / 64 := rfl
  have hZe : p.Z = 8 * p.n := rfl
  have hn₂ : wv s.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) = c := by
    have := M.prep.n
    rw [A, Pre.wordsVal_eq_wv] at this
    exact this
  refine WP.mono (WP.rdwr (halveQ_ok M.st M.ph.a7 M.ph.t0 hn₂ (by omega_arith) (by omega_arith)
    (by rw [hsl]; omega_arith))) fun t₃ ⟨⟨⟨hq₃, _, f₃⟩, k₃⟩, _, _, sp₃⟩ => ⟨?_, ?_, ?_⟩
  · exact M.st.step (Frm.toMut f₃ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hsl]; exact InMut.arrays (by decide) (by simp only [saveBytes]; omega_arith)
      · exact InMut.hdr (i := 25) (by decide)) k₃ sp₃
  · rw [hq₃]; omega_arith
  · rw [f₃.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hsl]; exact .inl (by dsimp only; omega_arith)
      · exact .inl (by decide)) (by decide)]
    exact hU

/-- The tests, once the shape passed: one witness of p, all of q's, then
p's others, `used` after p's octets. -/
theorem tests_ok {R : RoundImpl} {p : PP} {s : State} {c : Nat} (h : St p s)
    (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L))) (hqo : ((c - 1) / 2) % 2 = 1)
    (hU : word s.mem p.B 152 = BitVec.ofNat 64 p.L) (hL : p.L ≤ p.r.length) :
    WP isa (tests R.name R.code) s (CEnd p (sievedTests c (p.r.drop p.L))) := by
  have hb1 := h.dims.b1
  have hb2 := h.dims.b2
  have hbq : Spec.RsaKeyGen.bitLength ((c - 1) / 2) = p.bits - 1 := by
    rw [hc]; exact VG.Proof.Ffdh.ParameterCandidate.half_bitLength (by omega_arith) _
  have hbp : Spec.RsaKeyGen.bitLength c = p.bits := by
    rw [hc]; exact (VG.Proof.Ffdh.ParameterCandidate.candidate_bitLength (by omega_arith) _).1
  obtain ⟨_, _, hcu⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := p.bits) (by omega_arith)
    (Spec.Rsa.os2ip (p.r.take p.L))
  rw [← hc] at hcu
  unfold sievedTests tests
  rw [hbq, hbp]
  -- p's first witness.
  refine WP.seq (WP.mono (testP1_ok h hc hU hL hL) fun t₁ e₁ => ?_)
  refine stage_ok e₁ fun u₁ t₂ hu₁ _ M₂ _ hU₂ => ?_
  -- q, from p in array 0, and its test.
  unfold testQ
  refine WP.seq (WP.mono (halveQ_from M₂ hc hU₂) fun t₃ ⟨st₃, hq₃, hU₃⟩ => ?_)
  refine WP.seq (WP.mono (testQ_ok st₃ hc hq₃ hqo hU₃ hu₁) fun t₄ e₄ => ?_)
  refine stage_ok e₄ fun u₂ t₅ hu₂ _ M₅ _ hU₅ => ?_
  -- p's other witnesses.
  unfold testRest
  refine WP.seq (WP.mono (testPR_ok M₅.st hc hU₅ hu₂ hL) fun t₆ e₆ => ?_)
  exact pResult_ok e₆ hcu

end VG.Proof.Ffdh.RISCV64.ParameterCandidate
