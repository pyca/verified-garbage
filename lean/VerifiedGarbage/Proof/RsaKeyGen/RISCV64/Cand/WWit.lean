module

public import VerifiedGarbage.Impl.RsaKeyGen.RISCV64.Witness
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Ctx
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Prep
public import VerifiedGarbage.Spec.RsaKeyGen
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.Witness
import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.MontPrep
import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.WRound
import VerifiedGarbage.Proof.RsaKeyGen.WitnessBits
import VerifiedGarbage.Proof.RsaKeyGen.CandMath
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCore
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# A candidate on RISC-V: a witness from a draw

As on PPC64LE (`Proof/RsaKeyGen/PPC64LE/Cand/{WUni,WForced,WSel}.lean`):
`uniform_ok`, `s9 := 1` if the draw `x` in array 4 is uniform (`x ≥ 2` and
`(x | 1) < c`), else 0; `forced_ok`, `x` copied to array 3 with bit 1 set and
its top bit cleared, `(x | 2) mod 2^(64 w − 1)`; `witness_ok`, the draw
becomes `Spec.RsaKeyGen.witness (c − 1) x`'s witness, selected under the
flag's mask, and the flag added to `hUni`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Cand

open VG VG.RISCV64 VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.MillerRabin.RISCV64.Search
open VG.Impl.Bignum.RISCV64.PublicChecked (base)
open VG.Impl.RsaKeyGen.RISCV64.Witness (hUni uniform forced witness)
open VG.Proof.MillerRabin.RISCV64 (Env A MCtx mask)
open VG.Proof.Bignum (slot Frm word off ofs Outside writeW_outside word_writeW_self)

/-- The registers `uniform` writes. -/
def uniRegs : List Reg := [.a3, .t2, .t3, .t5, .s9, .a0, .t4, .s0, .s1, .s2, .s3, .s4, .a5, .a6]

theorem uniform_ok {s : State} {B : Addr} {Z w c : Nat} (e : Env s B Z w) (hc : A s.mem B w 0 = c) :
    WP isa uniform s fun t =>
      (t.gpr .s9 = BitVec.ofNat 64 (if decide (2 ≤ A s.mem B w 4) && decide ((A s.mem B w 4 ||| 1) < c) then 1 else 0) ∧
        Frm B [(slot w 3, 8 * (w + 2)), (slot w 6, 8 * (w + 2))] s.mem t.mem) ∧ Keep uniRegs s t := by
  unfold uniform
  refine WP.seq (WP.mono (VG.Proof.MillerRabin.RISCV64.Blinded.atLeast2_ok e) fun t1 ⟨⟨a3, tm⟩, k1⟩ => ?_)
  have e1 : Env t1 B Z w := e.keep k1 (by decide)
  refine WP.seq (WP.mono (WP.keep [.t2, .s9] (Q := fun t => t.gpr .s9 =
      BitVec.ofNat 64 (if 2 ≤ A s.mem B w 4 then 1 else 0) ∧ t.mem = t1.mem) (by
    have hv : (if (0#64 : BitVec 64) < t1.gpr .a3 then (1 : BitVec 64) else 0) =
        BitVec.ofNat 64 (if 2 ≤ A s.mem B w 4 then 1 else 0) := by
      by_cases h2 : 2 ≤ A s.mem B w 4
      · have : t1.gpr .a3 ≠ 0#64 := fun h0 => by have := a3.mp h0; omega
        rw [ite_eq_left (by rw [BitVec.lt_def]; have := (BitVec.toNat_ne_iff_ne).mpr this; simp at this ⊢; omega),
          ite_eq_left h2]; rfl
      · have : t1.gpr .a3 = 0#64 := a3.mpr (by omega)
        rw [this, ite_eq_right (by decide), ite_eq_right h2]; rfl
    brun [exec_li (show imm12 0 by decide), hv]) (by decide)) fun t2 ⟨⟨a9, m2⟩, k2⟩ => ?_)
  have e2 : Env t2 B Z w := e1.keep k2 (by decide)
  refine WP.seq (WP.mono (VG.Proof.MillerRabin.RISCV64.Blinded.ltN_ok (c := c) e2 (by rw [m2, tm]; exact hc))
    fun t3 ⟨⟨a4, f3⟩, k3⟩ => ?_)
  refine WP.mono (WP.keep [.s9] (Q := fun t => t.gpr .s9 = t3.gpr .s9 &&& t3.gpr .s4 ∧ t.mem = t3.mem)
    (by brun) (by decide)) fun t ⟨⟨a9', m⟩, k⟩ => ⟨⟨?_, ?_⟩, (((k1.trans k2).trans k3).trans k).mono (by decide)⟩
  · rw [a9', k3.gpr (by decide), a9, a4, m2, tm]
    by_cases h1 : 2 ≤ A s.mem B w 4 <;> by_cases h2 : (A s.mem B w 4 ||| 1) < c <;> simp [h1, h2] <;> decide
  · rw [m]; rw [m2, tm] at f3; exact f3

/-- The registers `forced` writes. -/
def fdRegs : List Reg := [.t2, .t3, .t4, .t5, .s0]

theorem forced_ok {s : State} {B : Addr} {Z w : Nat} (e : Env s B Z w) :
    WP isa forced s fun t =>
      (A t.mem B w 3 = (A s.mem B w 4 ||| 2) % 2 ^ (64 * w - 1) ∧
        Frm B [(slot w 3, 8 * (w + 2))] s.mem t.mem) ∧ Keep fdRegs s t := by
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ Z := e.hZ
  have hw4 := e.hw
  have hw128 := e.hw'
  have hnw := e.hs.nowrap
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have h3 : slot w 3 + 8 * (w + 2) ≤ Z := by rw [es]; omega
  have h4 : slot w 4 + 8 * (w + 2) ≤ Z := by rw [es]; omega
  unfold forced
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (e.base (rd := .t3) (by decide) 3) fun y ⟨⟨y3, ym⟩, ky⟩ => ?_
  have ey : Env y B Z w := e.keep ky (by decide)
  refine WP.mono (ey.base (rd := .t4) (by decide) 4) fun y' ⟨⟨y4, ym'⟩, ky'⟩ => ?_
  have ey' : Env y' B Z w := ey.keep ky' (by decide)
  refine WP.seq (WP.mono (VG.Proof.MillerRabin.RISCV64.Search.copyWithin_ok ey'.hs (dS := slot w 4) (dD := slot w 3)
    y4 ((ky'.gpr (by decide)).trans y3) ey'.t0 (by omega) (by omega) (by omega) (by omega) (by rw [es]; omega)
    (by rw [es]; omega) (by simp only [es]; omega)) fun z ⟨⟨_, zw, zo⟩, kz⟩ => ?_)
  have ez : Env z B Z w := ey'.keep kz (by decide)
  have hz := ez.hs
  -- `m₁`: memory after the copy; the stores follow.
  generalize hm1 : z.mem = m1 at zw zo
  rw [WP.block_append_iff]
  refine WP.mono (ez.base (rd := .t3) (by decide) 3) fun a ⟨⟨a3, am⟩, ka⟩ => ?_
  have ea : Env a B Z w := ez.keep ka (by decide)
  have ha := ea.hs
  have d0 : slot w 3 + 8 ≤ Z := by omega
  have dt : slot w 3 + 8 * (w - 1) + 8 ≤ Z := by omega
  have al0 : (slot w 3) % 8 = 0 := by rw [es]; omega
  have alt : (slot w 3 + 8 * (w - 1)) % 8 = 0 := by rw [es]; omega
  have o1 := writeW_outside m1 B (word m1 B (slot w 3) ||| 2#64) (d := slot w 3) (by omega)
  have rt : (m1.writeW (off B (slot w 3)) (word m1 B (slot w 3) ||| 2#64)).readW (off B (slot w 3 + 8 * (w - 1))) 64 =
      word m1 B (slot w 3 + 8 * (w - 1)) := o1.word (by omega) (by omega)
  have adr : off B (slot w 3 + 8 * w) - BitVec.ofNat 64 8 = off B (slot w 3 + 8 * (w - 1)) := by
    rw [off_sub B (by omega), show slot w 3 + 8 * w - 8 = slot w 3 + 8 * (w - 1) by omega]
  have msk : BitVec.ofInt 64 (-1) >>> 1 = BitVec.ofNat 64 (2 ^ (64 - 1) - 1) := by decide
  have msk' : (-1#64 : BitVec 64) >>> 1 = BitVec.ofNat 64 (2 ^ (64 - 1) - 1) := by decide
  refine WP.mono (WP.keep [.t2, .t3, .t4] (Q := fun t => t.mem =
      (m1.writeW (off B (slot w 3)) (word m1 B (slot w 3) ||| 2#64)).writeW (off B (slot w 3 + 8 * (w - 1)))
        (word m1 B (slot w 3 + 8 * (w - 1)) &&& BitVec.ofNat 64 (2 ^ (64 - 1) - 1))) (by
    brun [a3, am, hm1, (ka.gpr (by decide)).trans ez.t0, ha.ld (d := slot w 3) (n := 8) d0,
      ha.al8 (d := slot w 3) d0 al0, ha.st (d := slot w 3) (n := 8) d0, VG.Proof.MillerRabin.RISCV64.shl3_w w, adr,
      ha.ld (d := slot w 3 + 8 * (w - 1)) (n := 8) dt, ha.al8 (d := slot w 3 + 8 * (w - 1)) dt alt,
      ha.st (d := slot w 3 + 8 * (w - 1)) (n := 8) dt, exec_li (show imm12 (-1) by decide), msk, msk', rt,
      BitVec.add_zero]) (by decide)) fun t ⟨tm, kt⟩ => ?_
  have o2 := writeW_outside (m1.writeW (off B (slot w 3)) (word m1 B (slot w 3) ||| 2#64)) B
    (word m1 B (slot w 3 + 8 * (w - 1)) &&& BitVec.ofNat 64 (2 ^ (64 - 1) - 1)) (d := slot w 3 + 8 * (w - 1)) (by omega)
  have hx1 : VG.Proof.Bignum.wv m1 B (slot w 3) w = A s.mem B w 4 := by
    simp only [A, Pre.wordsVal_eq_wv]
    rw [ym', ym] at zw
    exact VG.Proof.Bignum.wv_congr2 fun i hi => zw i hi
  have hV : VG.Proof.Bignum.wv m1 B (slot w 3) w < 2 ^ (64 * (w - 1) + 64) := by
    rw [show 64 * (w - 1) + 64 = 64 * w by omega]; exact VG.Proof.Bignum.wv_lt _ _ _ _
  have fb := VG.Proof.RsaKeyGen.wv_fallback (m := m1) (m' := t.mem) (p := B) (d := slot w 3) (n := w) (t := w - 1)
    (b := 64) (by omega) (by omega) (by decide) (by decide)
    (by rw [tm, o2.word (by omega) (by omega), word_writeW_self])
    (by rw [tm, word_writeW_self])
    (fun j hj hj0 hjt => by rw [tm, o2.word (by omega) (by omega), o1.word (by omega) (by omega)]) hV
  refine ⟨⟨?_, ?_⟩, ((((ky.trans ky').trans kz).trans ka).trans kt).mono (by decide)⟩
  · simp only [A, Pre.wordsVal_eq_wv]
    rw [fb, hx1, show 64 * (w - 1) + 64 - 1 = 64 * w - 1 by omega]
    simp only [A, Pre.wordsVal_eq_wv]
  · rw [ym', ym] at zo
    refine Frm.trans (Frm.of_outside (o := slot w 3) (n := 8 * (w + 2)) (zo.mono (by omega) (by omega)) (by simp)) ?_
    rw [tm]
    exact Frm.trans (Frm.of_outside (o := slot w 3) (n := 8 * (w + 2)) (o1.mono (by omega) (by omega)) (by simp))
      (Frm.of_outside (o := slot w 3) (n := 8 * (w + 2)) (o2.mono (by omega) (by omega)) (by simp))

theorem or1_nat (a : Nat) : a ||| 1 = a + (1 - a % 2) := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or]
  rcases i with _ | i
  · simp [Nat.testBit_zero]; omega
  · rw [Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
    simp
    congr 1; omega

theorem neg_flag (P : Bool) : BitVec.ofNat 64 0 - BitVec.ofNat 64 (if P then 1 else 0) = mask P := by
  cases P <;> decide

/-- `MCtx` from `Env`, the inverse and the candidate. -/
theorem mctx_of {s : State} {B : Addr} {Z w N : Nat} (e : Env s B Z w)
    (hinv : ((Mont.word s.mem B (slot w 0)).toNat * (s.gpr .t1).toNat + 1) % 2 ^ 64 = 0)
    (hn : A s.mem B w 0 = N) : MCtx s B Z w N :=
  ⟨e.hs, e.hw, e.hw', e.hZ, e.a7, e.s5, e.t0, hinv, hn⟩

/-- The registers `witness` writes. -/
def witRegs : List Reg := [.a0, .a2, .a3, .a5, .a6, .t2, .t3, .t4, .t5, .s0, .s1, .s2, .s3, .s4, .s9]

/-- The arrays `witness` changes: 3, 4 and 6. -/
def arrR (w : Nat) : List (Nat × Nat) :=
  [(slot w 3, 8 * (w + 2)), (slot w 4, 8 * (w + 2)), (slot w 6, 8 * (w + 2))]

/-- What `witness` changes: arrays 3, 4 and 6, and `hUni`. -/
def witRanges (w : Nat) : List (Nat × Nat) :=
  [(8 * hUni, 8), (slot w 3, 8 * (w + 2)), (slot w 4, 8 * (w + 2)), (slot w 6, 8 * (w + 2))]

theorem witness_ok {s : State} {B : Addr} {Z w c u : Nat} (h : MCtx s B Z w c) (h6 : s.gpr .s6 = B)
    (hc2 : c % 2 = 1) (hcb : Spec.RsaKeyGen.bitLength (c - 1) = 64 * w)
    (hu : word s.mem B (8 * hUni) = BitVec.ofNat 64 u) :
    WP isa witness s fun t =>
      (A t.mem B w 4 = (Spec.RsaKeyGen.witness (c - 1) (A s.mem B w 4)).1 ∧
        word t.mem B (8 * hUni) = BitVec.ofNat 64
          (u + if (Spec.RsaKeyGen.witness (c - 1) (A s.mem B w 4)).2 then 1 else 0) ∧
        Frm B (witRanges w) s.mem t.mem) ∧ Keep witRegs s t := by
  have e := h.env h6
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ Z := e.hZ
  have hw4 := e.hw
  have hnw := e.hs.nowrap
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  generalize hx : A s.mem B w 4 = x
  have hxR : x < 2 ^ (64 * w) := by
    rw [← hx]; simp only [A, Pre.wordsVal_eq_wv]; exact VG.Proof.Bignum.wv_lt _ _ _ _
  rw [VG.Proof.RsaKeyGen.witness_eq hc2 hcb hxR]
  generalize hP : (decide (2 ≤ x) && decide (x + (1 - x % 2) < c)) = P
  unfold witness
  -- The words and numbers a step outside arrays 3, 4 and 6 keeps.
  have frw : ∀ {m m' : Mem}, Frm B (arrR w) m m' → ∀ d, d + 8 ≤ slot w 3 →
      word m' B d = word m B d := fun f d hd => f.word_eq (fun r hr => by
    simp only [arrR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [es] at hd ⊢ <;> omega)
    (by rw [es] at hd; omega)
  have frA0 : ∀ {m m' : Mem}, Frm B (arrR w) m m' → A m' B w 0 = A m B w 0 := fun f => by
    simp only [A, Pre.wordsVal_eq_wv]
    exact f.wv_eq (fun r hr => by
      simp only [arrR, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [es] <;> omega) (by rw [es]; omega)
  have fr1 : ∀ {m m' : Mem} {rs : List (Nat × Nat)}, Frm B rs m m' → (∀ r ∈ rs, r ∈ arrR w) →
      Frm B (arrR w) m m' := fun f hs => f.mono hs
  refine WP.seq (WP.mono (uniform_ok e h.n) fun t₁ ⟨⟨a9, o₁⟩, k₁⟩ => ?_)
  rw [hx] at a9
  have e₁ := e.keep k₁ (by decide)
  have o₁' := fr1 o₁ (by simp [arrR])
  have x₁ : A t₁.mem B w 4 = x := by
    rw [← hx]; simp only [A, Pre.wordsVal_eq_wv]
    exact o₁.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [es] <;> omega) (by rw [es]; omega)
  refine WP.seq (WP.mono (forced_ok e₁) fun t₂ ⟨⟨f3, o₂⟩, k₂⟩ => ?_)
  rw [x₁] at f3
  have e₂ := e₁.keep k₂ (by decide)
  have o₂' := fr1 o₂ (by simp [arrR])
  have x₂ : A t₂.mem B w 4 = x := by
    rw [← x₁]; simp only [A, Pre.wordsVal_eq_wv]
    exact o₂.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; simp only [es]; omega) (by rw [es]; omega)
  have s9₂ : t₂.gpr .s9 = BitVec.ofNat 64 (if P then 1 else 0) := by
    rw [k₂.gpr (by decide), a9, ← hP, or1_nat]
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t2, .s4] (Q := fun t => t.gpr .s4 = mask P ∧ t.mem = t₂.mem) (by
    brun [exec_li (show imm12 0 by decide), s9₂, neg_flag]) (by decide)) fun t₃ ⟨⟨a4, m₃⟩, k₃⟩ => ?_
  have e₃ := e₂.keep k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (e₃.base (rd := .a5) (by decide) 4) fun t₄ ⟨⟨a5, m₄⟩, k₄⟩ => ?_
  have e₄ := e₃.keep k₄ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (e₄.base (rd := .a6) (by decide) 3) fun t₅ ⟨⟨a6, m₅⟩, k₅⟩ => ?_
  have e₅ := e₄.keep k₅ (by decide)
  refine WP.mono (e₅.base (rd := .a2) (by decide) 6) fun t₆ ⟨⟨a2, m₆⟩, k₆⟩ => ?_
  have e₆ := e₅.keep k₆ (by decide)
  have m₆' : t₆.mem = t₂.mem := by rw [m₆, m₅, m₄, m₃]
  have K₆ := (((k₁.trans k₂).trans k₃).trans k₄).trans k₅ |>.trans k₆
  have o₆ : Frm B (arrR w) s.mem t₆.mem := by rw [m₆']; exact o₁'.trans o₂'
  have w0 : ∀ {m m' : Mem}, Frm B (arrR w) m m' → Mont.word m' B (slot w 0) = Mont.word m B (slot w 0) :=
    fun f => frw f (slot w 0) (by simp only [es]; omega)
  have inv₆ : ((Mont.word t₆.mem B (slot w 0)).toNat * (t₆.gpr .t1).toNat + 1) % 2 ^ 64 = 0 := by
    rw [w0 o₆, K₆.gpr (by decide)]; exact h.inv
  have c₆ : MCtx t₆ B Z w c := mctx_of e₆ inv₆ ((frA0 o₆).trans h.n)
  have a4₆ : t₆.gpr .s4 = mask P := by rw [k₆.gpr (by decide), k₅.gpr (by decide), k₄.gpr (by decide), a4]
  have a5₆ : t₆.gpr .a5 = off B (slot w 4) := by rw [k₆.gpr (by decide), k₅.gpr (by decide), a5]
  have a6₆ : t₆.gpr .a6 = off B (slot w 3) := by rw [k₆.gpr (by decide), a6]
  refine WP.seq (WP.mono (VG.Proof.MillerRabin.RISCV64.sel_ok c₆ (b := P) (o := 6) (a := 4) (t := 3) (by decide)
    (by decide) (by decide) (by decide) (by decide) a2 a5₆ a6₆ a4₆) fun t₇ ⟨⟨v₇, o₇⟩, k₇⟩ => ?_)
  have e₇ := e₆.keep k₇ (by decide)
  have o₇' : Frm B (arrR w) t₆.mem t₇.mem :=
    Frm.of_outside (o := slot w 6) (n := 8 * (w + 2)) (o₇.mono (by omega) (by omega)) (by simp [arrR])
  have c₇ : MCtx t₇ B Z w c := mctx_of e₇ (by
      rw [w0 o₇', k₇.gpr (by decide)]; exact inv₆)
    ((frA0 o₇').trans c₆.n)
  refine WP.seq (WP.mono (VG.Proof.MillerRabin.RISCV64.copy_ok c₇ (o := 4) (a := 6) (by decide) (by decide)
    (by decide)) fun t₈ ⟨⟨v₈, o₈⟩, k₈⟩ => ?_)
  have e₈ := e₇.keep k₈ (by decide)
  have o₈' : Frm B (arrR w) t₇.mem t₈.mem :=
    Frm.of_outside (o := slot w 4) (n := 8 * (w + 2)) (o₈.mono (by omega) (by omega)) (by simp [arrR])
  have hs₈ := e₈.hs
  have s9₈ : t₈.gpr .s9 = BitVec.ofNat 64 (if P then 1 else 0) := by
    rw [k₈.gpr (by decide), k₇.gpr (by decide), k₆.gpr (by decide),
      k₅.gpr (by decide), k₄.gpr (by decide), k₃.gpr (by decide), s9₂]
  have u₈ : word t₈.mem B 16 = BitVec.ofNat 64 u := by
    have := frw ((o₆.trans o₇').trans o₈') 16 (by simp only [es]; omega)
    simp only [hUni] at hu; rw [this, hu]
  refine WP.mono (WP.keep [.t2] (Q := fun t => t.mem = t₈.mem.writeW (off B (8 * hUni))
      (BitVec.ofNat 64 (u + if P then 1 else 0))) (by
    simp only [ldh, sth, hUni]
    have r16 : t₈.mem.readW (B + 16#64) 64 = BitVec.ofNat 64 u := u₈
    brun [e₈.s6, r16, s9₈, hs₈.ld (d := 16) (n := 8) (by omega), hs₈.al8 (d := 16) (by omega) (by decide),
      hs₈.st (d := 16) (n := 8) (by omega), BitVec.ofNat_add_ofNat]) (by decide)) fun t ⟨tm, kt⟩ => ?_
  have K := (((K₆.trans k₇).trans k₈).trans kt)
  have ou := writeW_outside t₈.mem B (d := 8 * hUni) (BitVec.ofNat 64 (u + if P then 1 else 0))
    (by simp only [hUni]; omega)
  refine ⟨⟨?_, ?_, ?_⟩, K.mono (by simp [witRegs, uniRegs, fdRegs, VG.Proof.MillerRabin.RISCV64.copyRegs])⟩
  · rw [tm]
    have : A (t₈.mem.writeW (off B (8 * hUni)) (BitVec.ofNat 64 (u + if P then 1 else 0))) B w 4 = A t₈.mem B w 4 := by
      simp only [A, Pre.wordsVal_eq_wv]
      exact (Frm.of_outside (rs := [(8 * hUni, 8)]) ou (by simp)).wv_eq (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; simp only [hUni, es]; omega) (by rw [es]; omega)
    rw [this, v₈, v₇]
    have hm4 : A t₆.mem B w 4 = x := by rw [m₆']; exact x₂
    have hm3 : A t₆.mem B w 3 = (x ||| 2) % 2 ^ (64 * w - 1) := by rw [m₆']; exact f3
    rw [hm4, hm3]
  · rw [tm]; exact word_writeW_self _ _ _ _
  · rw [tm]
    exact (((o₆.trans o₇').trans o₈').mono (by simp [arrR, witRanges])).trans
      (Frm.of_outside ou (by simp [witRanges]))

end VG.Proof.RsaKeyGen.RISCV64.Cand
