module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.ParameterCandidate.Base
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Backend
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Prep
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
public import VerifiedGarbage.Proof.RsaKeyGen.MrWindow
meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.Sieve
import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.MontPrep
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCore
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.WordCut
import VerifiedGarbage.Proof.Rsa.KeyBits32
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RelCTAssoc

-- separate module: a witness's draw and round, whose symbolic executions the witness loop's changes need not re-check

/-!
# An FFDH parameter candidate on RISC-V: the tests' state and the round

As on PPC64LE (`Proof/Ffdh/PPC64LE/ParameterCandidate/{StCall,Round,Keep}.lean`,
and `Prep` of `Proof/MillerRabin/PPC64LE/Search/RoundCall.lean`):

* `Prep`: a modulus's prepared working space, as `montPrep_ok` leaves it.
* `RoundCall R`: what the proof needs of the call of the round `R`
  (`roundCall`, a witness in array 4 into Montgomery form and the round
  called), stated once, so that its proof (`Search`'s `RoundCall` and
  `RoundCallCT`) is plugged in at the end: from `RC`, `a0` is 1 exactly when
  the witness passes, the working space changes only where the round's
  `Keeps` allows and keeps `Prep`, and memory outside it only on the stack
  below `sp` (`ok`); and two runs from the same working space and witness
  leak the same (`ct`).
* `MSt`: between the witnesses of a modulus `N` of `mb` bits, `St`, the
  modulus's header (`Ph`) and `Prep`. `MSt.frm`: it survives a change of
  `Free` ranges; `MSt.round`: and the round (`roundCount_ok`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.ParameterCandidate

variable {C : Nat}

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Ffdh.RISCV64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.RISCV64
open VG.RISCV64.Steps (eval_zero eval_zero_ofNat)
open VG.Impl.MillerRabin.RISCV64 VG.Impl.MillerRabin.RISCV64.Search
open VG.Proof.MillerRabin.RISCV64 (Env A MCtx RoundImpl)
open VG.Proof.MillerRabin.RISCV64.Search (rw_self frm_writeW geFlag_ok)
open VG.Proof.RsaKeyGen (mrE mrA)
open VG.Proof.Bignum.RISCV64.Pre (Two)

/-! ## Words the round keeps -/

/-- A byte the round keeps: not in its header words, its working arrays or
its table. -/
def Kept (w i : Nat) : Prop :=
  (∀ k ∈ [23, 26, 29, 30, 1], i < 8 * k ∨ 8 * k + 8 ≤ i) ∧
    (∀ j ∈ [2, 3, 5, 6, 8], i < slot w j ∨ slot w j + 8 * (w + 2) ≤ i) ∧ (i < slot w 11 ∨ slot w 27 ≤ i)

theorem keeps_byte {m m' : Mem} {B : Addr} {L w i : Nat}
    (h : Proof.MillerRabin.Round.Keeps Proof.MillerRabin.Round.compact B L w m m') (hi : i < 8 * L) (hk : Kept w i) :
    m' (B + BitVec.ofNat 64 i) = m (B + BitVec.ofNat 64 i) :=
  h i hi hk.1 hk.2.1 hk.2.2

/-- A word the round keeps. -/
theorem keeps_word {m m' : Mem} {B : Addr} {L w d : Nat}
    (h : Proof.MillerRabin.Round.Keeps Proof.MillerRabin.Round.compact B L w m m') (hd : d + 8 ≤ 8 * L)
    (hk : ∀ i, d ≤ i → i < d + 8 → Kept w i) : word m' B d = word m B d :=
  (Mem.readW_congr fun i hi => by
    rw [show off B d + BitVec.ofNat 64 i = B + BitVec.ofNat 64 (d + i) by
      simp only [off, BitVec.add_assoc, BitVec.ofNat_add]]
    exact (keeps_byte h (by omega_arith) (hk _ (by omega_arith) (by omega_arith))).symm).symm

/-! ## A prepared modulus -/

/-- A modulus `c` of `w` words prepared in the `L` words at `B` (`s6`): the
round's registers (`MCtx`, with `−c⁻¹ mod 2⁶⁴` in `t1`), the header, and
the Montgomery constants and Miller–Rabin's exponent. -/
structure Prep (s : State) (B : Addr) (L w c : Nat) : Prop where
  ctx : MCtx s B (8 * L) w c
  s6 : s.gpr .s6 = B
  len : word s.mem B 0 = BitVec.ofNat 64 L
  wW : word s.mem B 48 = BitVec.ofNat 64 w
  strideW : word s.mem B 224 = BitVec.ofNat 64 (8 * (w + 2))
  arrW : ∀ j < 8, word s.mem B (8 * (8 + j)) = off B (slot w j)
  c3 : 3 ≤ c
  odd : c % 2 = 1
  inv : ((word s.mem B (slot w 0)).toNat * (word s.mem B 56).toNat + 1) % 2 ^ 64 = 0
  r1 : A s.mem B w 1 = 2 ^ (64 * w) * 2 ^ (64 * w) % c
  r9 : A s.mem B w 9 = 2 ^ (64 * w) % c
  r10 : A s.mem B w 10 = c - 2 ^ (64 * w) % c
  e : A s.mem B w aE = mrE c
  l : s.mem.readW (off B (slot w aE + 8 * w)) 64 = BitVec.twoPow 64 (mrA c % 64)

theorem Prep.env {s : State} {B : Addr} {L w c : Nat} (h : Prep s B L w c) : Env s B (8 * L) w := h.ctx.env h.s6

/-! ## The round's call -/

/-- A round's call: the working space, the modulus and the witness. -/
structure RcD where
  B : Addr
  L : Nat
  w : Nat
  c : Nat
  a : Nat

/-- Before the call of a witness's round: the witness below the modulus in
array 4, and the round's stack. -/
def RC (d : RcD) (s : State) : Prop :=
  Prep s d.B d.L d.w d.c ∧ A s.mem d.B d.w 4 = d.a ∧ d.a < d.c ∧ 96 ≤ s.sp.toNat ∧ s.sp.toNat % 16 = 0 ∧
    (below s.sp 96).Disjoint ⟨d.B, 8 * d.L⟩

/-- What `roundCall` leaves: the prepared modulus, the result in `a0`, the
round's `Keeps`, and everything outside the working space and the round's
stack. -/
structure RcPost (s : State) (B : Addr) (L w c a : Nat) (t : State) : Prop where
  prep : Prep t B L w c
  a0 : t.gpr .a0 = BitVec.ofNat 64 (if Proof.MillerRabin.Round.round c a then 1 else 0)
  keeps : Proof.MillerRabin.Round.Keeps Proof.MillerRabin.Round.compact B L w s.mem t.mem
  frame : Frame [⟨B, 8 * L⟩, below s.sp 96] s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

/-- The call of the round `R`, for a witness in range: correct and in
constant time. -/
structure RoundCall (R : RoundImpl) : Prop where
  ok : ∀ (d : RcD) (s : State), RC d s →
    WP isa (roundCall R.name R.code) s (RcPost s d.B d.L d.w d.c d.a)
  ct : RelCT isa (Two RC) (roundCall R.name R.code) fun _ _ => True

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

/-- `Prep` survives a state that keeps the registers and the words and
numbers it reads. -/
theorem Prep.keep {s t : State} {B : Addr} {L w c : Nat} (h : Prep s B L w c) {regs : List Reg} (k : Keep regs s t)
    (h6 : Reg.s6 ∉ regs) (r7 : t.gpr .a7 = s.gpr .a7) (r0 : t.gpr .t0 = s.gpr .t0) (r5 : t.gpr .s5 = s.gpr .s5)
    (r1 : t.gpr .t1 = s.gpr .t1)
    (hw : ∀ d, Read w d → word t.mem B d = word s.mem B d)
    (hv : ∀ j, (j = 0 ∨ j = 1 ∨ j = 9 ∨ j = 10 ∨ j = 27) → A t.mem B w j = A s.mem B w j) :
    Prep t B L w c := by
  have hc := h.ctx
  have h0 := hw (slot w 0) (by simp [Read])
  have h56 := hw 56 (by simp [Read])
  have hl := hw (slot w 27 + 8 * w) (by simp [Read])
  refine ⟨⟨hc.scr.congr k.2.2, hc.w4, hc.w128, hc.hZ, r7.trans hc.a7, r5.trans hc.s5, r0.trans hc.t0, ?_,
    (hv 0 (by simp)).trans hc.n⟩, (k.gpr h6).trans h.s6, (hw 0 (by simp [Read])).trans h.len,
    (hw 48 (by simp [Read])).trans h.wW, (hw 224 (by simp [Read])).trans h.strideW,
    fun j hj => (hw _ (Read.arr hj)).trans (h.arrW j hj), h.c3, h.odd, by rw [h0, h56]; exact h.inv,
    (hv 1 (by simp)).trans h.r1, (hv 9 (by simp)).trans h.r9, (hv 10 (by simp)).trans h.r10, ?_, ?_⟩
  · have : Mont.word t.mem B (slot w 0) = Mont.word s.mem B (slot w 0) := h0
    rw [this, r1]; exact hc.inv
  · have e27 : aE = 27 := rfl
    have he := h.e
    rw [e27] at he ⊢
    exact (hv 27 (by simp)).trans he
  · have e27 : aE = 27 := rfl
    have hl' := h.l
    rw [e27] at hl' ⊢
    simp only [word] at hl
    rw [hl]; exact hl'

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
    h.ph.keep r7 r0 r5 hw, h.prep.keep k h6 r7 r0 r5 r1 hw (fun j hj => ?_), h.mb1, h.mb2⟩
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
    (hR : RdPost s p.B p.n (wOf mb) N a i K t) : MSt p mb N C t := by
  obtain ⟨u, hu, tm, kt, tsp⟩ := hR
  obtain ⟨hw2, -, hZ⟩ := h.w
  have stu : St p u := h.st.call hu.keeps (by have := hu.frame; rw [h.st.sp] at this; exact this) hu.rd hu.wr
    hu.sp hu.prep.s6 hZ
  have phu : Ph p mb C u := h.ph.keep (hu.prep.ctx.a7.trans h.ph.a7.symm) (hu.prep.ctx.t0.trans h.ph.t0.symm)
    (hu.prep.ctx.s5.trans h.ph.s5.symm) fun d hd => keeps_word hu.keeps (by
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

/-- The round of a witness `a` (`RoundCall.ok`), then `hStat` 2 if it
failed, else the passing witnesses `hIdx` counted and `hStat` 1 once there
are `hChecks` of them, 4 before. -/
theorem roundCount_ok {R : RoundImpl} (hR : RoundCall R) {s : State} {B : Addr} {L w c a i K : Nat}
    (h : RC ⟨B, L, w, c, a⟩ s)
    (hI : word s.mem B 176 = BitVec.ofNat 64 i) (hK : word s.mem B 168 = BitVec.ofNat 64 K)
    (hi : i < 2 ^ 62) (hK' : K < 2 ^ 62) :
    WP isa (Search.round R.name R.code) s (RdPost s B L w c a i K) := by
  have hp : Prep s B L w c := h.1
  have hZ := hp.ctx.hZ
  have hnw := hp.ctx.scr.nowrap
  have es : ∀ j, VG.Proof.Bignum.slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have hZ' : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := by rw [← es]; exact hZ
  unfold Search.round
  refine WP.seq (WP.mono (hR.ok ⟨B, L, w, c, a⟩ s h) fun u (hu : RcPost s B L w c a u) => ?_)
  have hs : Scr u B (8 * L) := hu.prep.ctx.scr
  have h6 : u.gpr .s6 = B := hu.prep.s6
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
      VG.Proof.MillerRabin.RISCV64.Search.shl3_ofNat, e3, sT, lT, aT, l192, a192, tv, BitVec.add_zero,
      add_ofNat_zero, vm, show s.mem.readW (p.B + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (2 ^ k - 1) from htop]
  refine ⟨⟨⟨?_, ?_⟩, (kv.trans kt).mono (by decide)⟩, by rw [tsp, vsp]⟩
  · rw [← hb]
    refine Proof.Ffdh.ParameterCandidate.wv_cut (by omega_arith) hk2 ?_ fun j hj => ?_
    · simp only [word, off] at e0 ⊢; rw [e0, rw_self]
    · simp only [word, off] at e0 ⊢; rw [e0, rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
  · rw [e0]
    exact frm_writeW (Frm.refl _ _ _) _ ⟨_, List.mem_singleton_self _, by dsimp only; omega_arith,
      by dsimp only; omega_arith⟩ (by omega_arith)

theorem wv_lt_two {m : Mem} {B : Addr} {d w : Nat} (hw : 1 ≤ w) :
    wv m B d w < 2 ↔ word m B d >>> 1 = 0#64 ∧ ∀ j, 1 ≤ j → j < w → word m B (d + 8 * j) = 0#64 := by
  have e := wv_add m B d 1 (w - 1)
  rw [show 1 + (w - 1) = w by omega_arith] at e
  simp only [wv, Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.pow_zero, Nat.one_mul, Nat.mul_one] at e
  have hz := wv_eq_zero_iff m B (d + 8) (w - 1)
  have hsh : word m B d >>> 1 = 0#64 ↔ (word m B d).toNat < 2 := by
    rw [← BitVec.toNat_inj, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod]; omega_arith
  rw [e, hsh]
  constructor
  · intro hl
    have h0 : wv m B (d + 8) (w - 1) = 0 := by
      by_contra hc; have : 1 ≤ wv m B (d + 8) (w - 1) := Nat.one_le_iff_ne_zero.mpr hc; omega_arith
    refine ⟨by omega_arith, fun j hj1 hj2 => ?_⟩
    have := hz.mp h0 (j - 1) (by omega_arith)
    rwa [show d + 8 + 8 * (j - 1) = d + 8 * j by omega_arith] at this
  · rintro ⟨hl, hr⟩
    have h0 : wv m B (d + 8) (w - 1) = 0 := hz.mpr fun q hq => by
      rw [show d + 8 + 8 * q = d + 8 * (q + 1) by omega_arith]; exact hr _ (by omega_arith) (by omega_arith)
    omega_arith

/-- `atLeast2`: `a3 = 0` exactly when the number in array 4 is below 2. -/
theorem dScan_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z) (h7 : s.gpr .a7 = off B (slot w 0))
    (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))) (h0 : s.gpr .t0 = BitVec.ofNat 64 w) (hw : 2 ≤ w)
    (hw' : w < 2 ^ 31) (hZ : slot w 4 + 8 * w ≤ Z) :
    WP isa atLeast2 s fun t =>
      (((t.gpr .a3 = 0#64 ↔ wv s.mem B (slot w 4) w < 2) ∧ t.mem = s.mem) ∧ Keep [.t3, .a3, .t5, .t2] s t) ∧
        t.sp = s.sp := by
  have hnw := hs.nowrap
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have a4 : (slot w 4) % 8 = 0 := by simp only [es]; omega_arith
  generalize hd : slot w 4 = d at hZ a4
  unfold atLeast2
  refine WP.rdwr (WP.seq ?_) |>.mono fun t ⟨h, _, _, hsp⟩ => ⟨h, hsp⟩
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .t3) (by decide) h7 h5 4) fun v ⟨⟨v3, vm⟩, kv⟩ => ?_
  rw [hd] at v3
  have hsv : Scr v B Z := hs.congr kv.2.2
  have l0 : InRegions (v.rd ++ v.wr) (off B d) 8 := hsv.ld (by omega_arith)
  have a0 : (off B d).toNat % 8 = 0 := hsv.al8 (by omega_arith) a4
  refine WP.mono (WP.keep [.a3, .t3, .t5] (Q := fun u => u.gpr .a3 = word s.mem B d >>> 1 ∧
      u.gpr .t3 = off B (d + 8) ∧ u.gpr .t5 = BitVec.ofNat 64 (w - 1) ∧ u.mem = s.mem) ?_ (by rfl) (by rfl))
    fun u ⟨⟨u3, ut3, u5, um⟩, ku⟩ => ?_
  · have hsub : BitVec.ofNat 64 w - BitVec.ofNat 64 1 = BitVec.ofNat 64 (w - 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega_arith
    brun [v3, l0, a0, BitVec.add_zero, add_ofNat_zero, (kv.gpr (by decide)).trans h0, hsub, vm]
  let Inv : Nat → State → Prop := fun i t =>
    (t.gpr .t3 = off B (d + 8 * (i + 1)) ∧
      (t.gpr .a3 = 0#64 ↔ word s.mem B d >>> 1 = 0#64 ∧ ∀ j, 1 ≤ j → j ≤ i → word s.mem B (d + 8 * j) = 0#64) ∧
      t.mem = s.mem) ∧ Keep [.t3, .a3, .t5, .t2] s t
  refine WP.mono (wp_countdown (cnt := .t5) (N := w - 1) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨⟨t3, t24, tm⟩, kt⟩ _ => ?_)
    ⟨⟨by rw [ut3], by rw [u3]; exact ⟨fun h => ⟨h, fun j h1 h2 => absurd h2 (by omega_arith)⟩, fun h => h.1⟩, um⟩,
      (kv.trans ku).mono (by decide)⟩ u5) fun t ⟨⟨_, t24, tm⟩, kt⟩ => ⟨⟨?_, tm⟩, kt⟩
  · have ht : Scr t B Z := hs.congr kt.2.2
    have l : InRegions (t.rd ++ t.wr) (off B (d + 8 * (i + 1))) 8 := ht.ld (by omega_arith)
    have al : (off B (d + 8 * (i + 1))).toNat % 8 = 0 := ht.al8 (by omega_arith) (by omega_arith)
    have rv : t.mem.readW (off B (d + 8 * (i + 1))) 64 = word s.mem B (d + 8 * (i + 1)) := by rw [tm]
    refine WP.mono (WP.keep [.t3, .a3, .t5, .t2] (Q := fun u =>
        u.gpr .t3 = off B (d + 8 * (i + 1 + 1)) ∧
        u.gpr .a3 = t.gpr .a3 ||| word s.mem B (d + 8 * (i + 1)) ∧ u.mem = t.mem ∧
        u.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1) ?_ (by rfl) (by rfl))
      fun u ⟨⟨u5, u24, um, u6⟩, ku⟩ => ⟨⟨⟨u5, ?_, um.trans tm⟩, (kt.trans ku).mono (by decide)⟩, u6⟩
    · brun [t3, BitVec.add_zero, add_ofNat_zero, l, al, rv]
      rw [show d + 8 * (i + 1) + 8 = d + 8 * (i + 1 + 1) by omega_arith]
    · rw [u24, BitVec.or_eq_zero_iff, t24]
      constructor
      · rintro ⟨⟨a, b⟩, c⟩
        exact ⟨a, fun j h1 h2 => by
          rcases Nat.lt_or_ge j (i + 1) with hj | hj
          · exact b j h1 (by omega_arith)
          · rw [show j = i + 1 by omega_arith]; exact c⟩
      · rintro ⟨a, b⟩
        exact ⟨⟨a, fun j h1 h2 => b j h1 (by omega_arith)⟩, b _ (by omega_arith) (Nat.le_refl _)⟩
  · rw [t24, wv_lt_two (by omega_arith)]
    exact ⟨fun ⟨a, b⟩ => ⟨a, fun j h1 h2 => b j h1 (by omega_arith)⟩,
      fun ⟨a, b⟩ => ⟨a, fun j h1 h2 => b j h1 (by omega_arith)⟩⟩

/-- The number with its low word or'ed with 1. -/
theorem wv_or1 {m m' : Mem} {B : Addr} {d w : Nat} (hw : 1 ≤ w)
    (h0 : word m' B d = word m B d ||| 1#64) (hr : ∀ j, 1 ≤ j → j < w → word m' B (d + 8 * j) = word m B (d + 8 * j)) :
    wv m' B d w = wv m B d w + (1 - wv m B d w % 2) := by
  have e := fun mm => wv_add mm B d 1 (w - 1)
  rw [show 1 + (w - 1) = w by omega_arith] at e
  rw [e m, e m']
  simp only [wv, Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.pow_zero, Nat.one_mul, Nat.mul_one]
  have hrest : wv m' B (d + 8) (w - 1) = wv m B (d + 8) (w - 1) := wv_congr fun i hi => by
    rw [show d + 8 + 8 * i = d + 8 * (i + 1) by omega_arith]; exact hr _ (by omega_arith) (by omega_arith)
  rw [hrest, h0]
  have hor : (word m B d ||| 1#64).toNat = (word m B d).toNat + (1 - (word m B d).toNat % 2) := by
    rw [BitVec.toNat_or, show (1#64).toNat = 1 from rfl, VG.Proof.Rsa.KeyBits32.or_one]
    omega_arith
  rw [hor]
  have : (2 ^ 64 * wv m B (d + 8) (w - 1)) % 2 = 0 := by
    rw [Nat.mul_mod, show 2 ^ 64 % 2 = 0 from rfl, Nat.zero_mul, Nat.zero_mod]
  omega_arith

/-- The registers `ltN` writes. -/
def drRegs : List Reg := [.t3, .t4, .s0, .t5, .t2, .a5, .a6, .a0, .s1, .s2, .s3, .s4]

/-- `ltN`: with the witness `x` in array 4 and the odd modulus `N` in array
0, `x | 1` into array 3 (its word `w` zeroed) and `x | 1 − N` into array 6:
`s4`, the borrow's mask, is zero exactly when `x` is not below `N − 1`. -/
theorem dRange_ok {s : State} {B : Addr} {Z w N x : Nat} (hs : Scr s B Z) (h7 : s.gpr .a7 = off B (slot w 0))
    (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))) (h0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (hw : 2 ≤ w) (hw' : w ≤ 128) (hZ : slot w 7 ≤ Z) (hN : wv s.mem B (slot w 0) w = N) (hodd : N % 2 = 1)
    (hx : wv s.mem B (slot w 4) w = x) :
    WP isa ltN s fun t =>
      (((t.gpr .s4 = 0#64 ↔ ¬ x < N - 1) ∧
        Frm B [(slot w 3, 8 * (w + 2)), (slot w 6, 8 * (w + 2))] s.mem t.mem) ∧ Keep drRegs s t) ∧
        t.sp = s.sp := by
  have hnw := hs.nowrap
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have hZ' : 256 + 7 * (8 * (w + 2)) ≤ Z := by rw [← es]; exact hZ
  unfold ltN
  refine WP.rdwr ?_ |>.mono fun t ⟨h, _, _, hsp⟩ => ⟨h, hsp⟩
  -- Array 4 copied to array 3.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .t3) (by decide) h7 h5 3) fun s₁ ⟨⟨a3, m₁⟩, k₁⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .t4) (by decide) ((k₁.gpr (by decide)).trans h7)
    ((k₁.gpr (by decide)).trans h5) 4) fun s₂ ⟨⟨a4, m₂⟩, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  refine WP.seq (WP.mono (VG.Proof.MillerRabin.RISCV64.Search.copyWithin_ok (hs.congr k12.2.2) a4
    ((k₂.gpr (by decide)).trans a3) ((k12.gpr (by decide)).trans h0) (by omega_arith) (by omega_arith)
    (by simp only [es]; omega_arith) (by simp only [es]; omega_arith) (by simp only [es]; omega_arith)
    (by simp only [es]; omega_arith) (by simp only [es]; omega_arith)) fun s₃ ⟨⟨_, cp, o₃⟩, k₃⟩ => ?_)
  have k13 := k12.trans k₃
  rw [m₂, m₁] at cp o₃
  -- Its low bit set and its word `w` zeroed.
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  have h7₃ : s₃.gpr .a7 = off B (slot w 0) := (k13.gpr (by decide)).trans h7
  have h5₃ : s₃.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)) := (k13.gpr (by decide)).trans h5
  refine WP.mono (Pub.base_ok (rd := .t3) (by decide) h7₃ h5₃ 3) fun s₄ ⟨⟨b3, m₄⟩, k₄⟩ => ?_
  have k14 := k13.trans k₄
  have hs₄ : Scr s₄ B Z := hs.congr k14.2.2
  have l3 : InRegions (s₄.rd ++ s₄.wr) (off B (slot w 3)) 8 := hs₄.ld (by simp only [es]; omega_arith)
  have st3 : InRegions s₄.wr (off B (slot w 3)) 8 := hs₄.st (by simp only [es]; omega_arith)
  have st3w : InRegions s₄.wr (off B (slot w 3 + 8 * w)) 8 := hs₄.st (by simp only [es]; omega_arith)
  have al3 : (off B (slot w 3)).toNat % 8 = 0 := hs₄.al8 (by simp only [es]; omega_arith) (by simp only [es]; omega_arith)
  have al3w : (off B (slot w 3 + 8 * w)).toNat % 8 = 0 :=
    hs₄.al8 (by simp only [es]; omega_arith) (by simp only [es]; omega_arith)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t2, .t4, .t3] (Q := fun u => u.mem =
      (s₄.mem.writeW (off B (slot w 3)) (s₄.mem.readW (off B (slot w 3)) 64 ||| 1#64)).writeW
        (off B (slot w 3 + 8 * w)) 0#64) ?_ (by rfl) (by rfl)) fun s₅ ⟨m₅, k₅⟩ => ?_
  · brun [b3, BitVec.add_zero, add_ofNat_zero, l3, st3, st3w, al3, al3w, (k14.gpr (by decide)).trans h0,
      VG.Proof.MillerRabin.RISCV64.Search.shl3_ofNat, exec_li (show imm12 0 by decide)]
  have k15 := k14.trans k₅
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .a5) (by decide) ((k15.gpr (by decide)).trans h7)
    ((k15.gpr (by decide)).trans h5) 3) fun s₆ ⟨⟨a5, m₆⟩, k₆⟩ => ?_
  have k16 := k15.trans k₆
  refine WP.mono (Pub.base_ok (rd := .a6) (by decide) ((k16.gpr (by decide)).trans h7)
    ((k16.gpr (by decide)).trans h5) 6) fun s₇ ⟨⟨a6, m₇⟩, k₇⟩ => ?_
  have k17 := k16.trans k₇
  -- `x | 1 − N`.
  refine WP.mono (subMod64_ok (hs.congr k17.2.2) ((k₇.gpr (by decide)).trans a5) a6
    ((k17.gpr (by decide)).trans h7) ((k17.gpr (by decide)).trans h0) (by omega_arith) (by omega_arith)
    (by simp only [es]; omega_arith) (by simp only [es]; omega_arith) (by simp only [es]; omega_arith)
    (by simp only [es]; omega_arith) (by simp only [es]; omega_arith) (by simp only [es]; omega_arith)
    (by simp only [es]; omega_arith) (by simp only [es]; omega_arith)) fun t ⟨⟨c, hc, hsub, h4⟩, o₈, k₈⟩ => ?_
  have m37 : s₇.mem = (s₃.mem.writeW (off B (slot w 3)) (s₃.mem.readW (off B (slot w 3)) 64 ||| 1#64)).writeW
      (off B (slot w 3 + 8 * w)) 0#64 := by rw [m₇, m₆, m₅, m₄]
  -- What changed before `subMod64`: array 3.
  have f₇ : Frm B [(slot w 3, 8 * (w + 2))] s.mem s₇.mem := by
    rw [m37]
    refine frm_writeW (a := slot w 3 + 8 * w) (frm_writeW (a := slot w 3)
      (Frm.of_outside (o₃.mono (o' := slot w 3) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_arith))
      (List.mem_singleton_self _)) _ ⟨_, List.mem_singleton_self _, by dsimp only; omega_arith,
        by dsimp only; omega_arith⟩ (by simp only [es]; omega_arith)) _
      ⟨_, List.mem_singleton_self _, by dsimp only; omega_arith, by dsimp only; omega_arith⟩
      (by simp only [es]; omega_arith)
  have n₇ : VG.Proof.Mont.wordsVal s₇.mem B (slot w 0) w = N := by
    rw [Pre.wordsVal_eq_wv, f₇.wv_eq (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; dsimp only; simp only [es]; omega_arith)
      (by simp only [es]; omega_arith), hN]
  have x₃ : wv s₃.mem B (slot w 3) w = x := by
    rw [← hx]; exact wv_congr2 fun i hi => cp i hi
  have a₇ : VG.Proof.Mont.wordsVal s₇.mem B (slot w 3) w = x + (1 - x % 2) := by
    rw [Pre.wordsVal_eq_wv, ← x₃]
    refine wv_or1 (by omega_arith) ?_ fun j h1 h2 => ?_
    · simp only [word, off] at m37 ⊢
      rw [m37, rw_off _ _ _ (by omega_arith) (by simp only [es]; omega_arith) (by simp only [es]; omega_arith), rw_self]
    · simp only [word, off] at m37 ⊢
      rw [m37, rw_off _ _ _ (by omega_arith) (by simp only [es]; omega_arith) (by simp only [es]; omega_arith),
        rw_off _ _ _ (by omega_arith) (by simp only [es]; omega_arith) (by simp only [es]; omega_arith)]
  have z₇ : (VG.Proof.Mont.word s₇.mem B (slot w 3 + 8 * w)).toNat = 0 := by
    simp only [VG.Proof.Mont.word, VG.Proof.Mont.off] at m37 ⊢; rw [m37, rw_self]; rfl
  rw [n₇, a₇] at hsub
  rw [z₇] at h4
  have hT : VG.Proof.Mont.wordsVal t.mem B (slot w 6) w < 2 ^ (64 * w) := VG.Proof.Mont.wordsVal_lt _ _ _ _
  have hX : x < 2 ^ (64 * w) := by rw [← hx]; exact wv_lt _ _ _ _
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [h4]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl
    · simp only [Nat.lt_irrefl, ↓reduceIte]
      constructor
      · intro _ hlt; omega_arith
      · intro _; rfl
    · simp only [Nat.zero_lt_one, ↓reduceIte]
      constructor
      · intro h; exact absurd h (by decide)
      · intro hn; exfalso; apply hn; omega_arith
  · exact (f₇.mono fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self).trans
      (Frm.of_outside (o₈.mono (o' := slot w 6) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_arith))
        (List.mem_cons_of_mem _ List.mem_cons_self))
  · exact ((k17.trans k₈).mono (by decide))

/-! ## A draw -/

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
  .ite (.zero .a3) (.block []) (.ite (.zero .s4) (.block []) (Search.round name roundCode))

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
  refine WP.mono (dScan_ok M₁.st.scr M₁.ph.a7 M₁.ph.s5 M₁.ph.t0 hw2 (by omega_arith) (by have := es 4; omega_arith))
    fun t₂ ⟨⟨⟨z₂, m₂⟩, k₂⟩, sp₂⟩ => ?_
  rw [ha₁] at z₂
  have M₂ : MSt p mb N C t₂ := M₁.frm (rs := []) (by rw [m₂]; exact Frm.refl _ _ _) (by simp) k₂ sp₂ (by decide)
    (k₂.gpr (by decide)) (k₂.gpr (by decide)) (k₂.gpr (by decide)) (k₂.gpr (by decide))
  have hN₂ : wv t₂.mem p.B (slot (wOf mb) 0) (wOf mb) = N := by
    rw [← Pre.wordsVal_eq_wv]; exact M₂.prep.ctx.n
  have hx₂ : wv t₂.mem p.B (slot (wOf mb) 4) (wOf mb) = wA mb p.r u := by rw [m₂]; exact ha₁
  refine WP.mono (dRange_ok M₂.st.scr M₂.ph.a7 M₂.ph.s5 M₂.ph.t0 hw2 hw128 (by have := es 7; omega_arith) hN₂
    M₂.prep.odd hx₂) fun t ⟨⟨⟨z₄, f₄⟩, k₄⟩, sp₄⟩ => ?_
  have F₄ : Frm p.B (drR (wOf mb)) t₂.mem t.mem := f₄.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp
  have M₄ : MSt p mb N C t := M₂.frm F₄ (drR_free _) k₄ sp₄ (by decide) (k₄.gpr (by decide)) (k₄.gpr (by decide))
    (k₄.gpr (by decide)) (k₄.gpr (by decide))
  have F : Frm p.B (drR (wOf mb)) s.mem t.mem := (F₁.trans (by rw [m₂] at F₄; exact F₄))
  refine ⟨M₄, ?_, ?_, ?_, ?_, z₄, ?_⟩
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
  · simp only [A]
    rw [Pre.wordsVal_eq_wv, ← hx₂]
    exact f₄.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have := es 3; have := es 4; have := es 6
      rcases hr with rfl | rfl <;> dsimp only <;> omega_arith) (by have := es 4; omega_arith)

/-- The witness of `DMid`, in range, before its round. -/
theorem DMid.rc {p : PP} {mb N u i : Nat} {t : State} (h : DMid p mb N u i C t) (ha : wA mb p.r u < N) :
    RC ⟨p.B, p.n, wOf mb, N, wA mb p.r u⟩ t :=
  ⟨h.m.prep, h.a4, ha, by rw [h.m.st.sp]; exact h.m.st.sp96, by rw [h.m.st.sp]; exact h.m.st.sp16,
    by rw [h.m.st.sp]; exact h.m.st.stkB⟩

theorem drawTail_ok {R : RoundImpl} (hR : RoundCall R) {p : PP} {mb N u i : Nat} {t₄ : State}
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
  refine WP.mono (roundCount_ok hR (hD.rc (by omega_arith)) hI M₄.ph.checksW hi hK)
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
  · rw [rw_self, dStat, ite_eq_left ht2, hr]; rfl
  · rw [rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), dIdx, ite_eq_right (by simp [hr])]
    exact (keeps_hdr (i := 22) hv.keeps (by decide) (by decide) (by omega_arith)).trans hI
  · rw [rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
      rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]; exact u₅
  · rw [rw_self, dStat, ite_eq_left ht2, hr]; rfl
  · rw [rw_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), rw_self, dIdx, ite_eq_left ⟨ha2, haN, hr⟩]

theorem draw_ok {R : RoundImpl} (hR : RoundCall R) {p : PP} {mb N u i : Nat} {s : State} (h : MSt p mb N C s)
    (hu : word s.mem p.B 152 = BitVec.ofNat 64 u) (hroom : u + (mb + 7) / 8 ≤ p.r.length)
    (hI : word s.mem p.B 176 = BitVec.ofNat 64 i) (hS : word s.mem p.B 160 = BitVec.ofNat 64 4)
    (hi : i < 2 ^ 62) :
    WP isa (draw R.name R.code) s fun t => MSt p mb N C t ∧
      word t.mem p.B 152 = BitVec.ofNat 64 (u + (mb + 7) / 8) ∧
      word t.mem p.B 160 = BitVec.ofNat 64 (dStat N C i (wA mb p.r u)) ∧
      word t.mem p.B 176 = BitVec.ofNat 64 (dIdx N i (wA mb p.r u)) := by
  rw [draw_eq]
  refine WP.seq (WP.mono (drawLoad_ok h hu hroom hI hS) fun t ht => ?_)
  refine WP.assoc (WP.assoc (WP.seq (WP.mono (drawMid_ok ht) fun t₄ h₄ => drawTail_ok hR h₄ hi)))

end VG.Proof.Ffdh.RISCV64.ParameterCandidate
