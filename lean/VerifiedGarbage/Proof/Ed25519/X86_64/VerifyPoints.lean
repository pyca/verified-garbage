module

public import VerifiedGarbage.Proof.Ed25519.X86_64.RecodeStep
public import VerifiedGarbage.Proof.Ed25519.X86_64.WindowStep
import VerifiedGarbage.Proof.Ed25519.X86_64.WindowDigits
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulBatch
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCounter
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Module
import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Lit
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.X25519.Bytes
public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Ed25519.ScalarBytes
import VerifiedGarbage.Proof.Ed25519.X86_64.Bits
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Impl.Ed25519.X86_64.Verify
public import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverParity
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ed25519.Window
import VerifiedGarbage.Proof.Ed25519.X86_64.PointEqual
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMul
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyFrame
import VerifiedGarbage.Proof.Ed25519.X86_64.Points
import VerifiedGarbage.Proof.Ed25519.X86_64.FieldMemory
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.X25519.X86_64.Lit
import Mathlib.Tactic.FieldSimp

/-! ### `Ed25519.X86_64.RecodeLoop`, which this module and modules that import it used -/

section

/-!
# The recoding's loop on x86-64

`recode` runs `Recode.step` from bit 0 while the bit is below the bound `8 nb` (what `bound`
compares `rsi` with), then stores the last carry: the array `dst` then holds
`Recode.digits w X (8 nb)` (`recode_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519.Recode
open VG.Proof.X25519.X86_64 (off ofs Keeps)

theorem Copied.of_keep {m m' : Mem} {base : Addr} {src nb X : Nat} (h : Copied m base src nb X)
    (hsrc : 3104 ≤ src) (hfit : src + nb + 8 ≤ 8192)
    (k : ∀ x, (ofs base x < 2048 ∨ 3104 ≤ ofs base x) → m' x = m x) : Copied m' base src nb X := by
  intro b hb
  rw [← h b hb]
  congr 1
  exact Mem.readW_congr fun i hi => k _ (Or.inr (by
    rw [VG.Proof.X25519.X86_64.ofs_off base (by omega_arith)]; omega_arith))

/-- The recoding's loop: the state `st`, reached from the start, in the registers and the array. -/
structure RecInv (s₀ : State) (base : Addr) (nb X w dst : Nat) (st : St) (t : State) : Prop where
  reach : Reach w X (8 * nb) st
  good : Good w X st
  lt : st.i < 8 * nb + w
  rsi : t.gpr .rsi = BitVec.ofNat 64 st.i
  r8 : t.gpr .r8 = BitVec.ofNat 64 st.c
  dig : ∀ j < 528, dig t.mem base dst j = st.u j
  keep : RecKeep base dst s₀ t

/-- What `bound` does from any state the recoding reaches: CF set if the bit is below `8 nb`. -/
def BoundSpec (s₀ : State) (base : Addr) (dst nb : Nat) (bound : List Instr) : Prop :=
  ∀ t, RecKeep base dst s₀ t → ∀ i, t.gpr .rsi = BitVec.ofNat 64 i → i < 1024 →
    WP isa (.block bound) t fun u => u.cf = some (decide (i < 8 * nb)) ∧ Keeps [.rax] t u

/-- One step of the recoding loop, from bit `st.i < 8 nb`: CF set if it goes on. -/
theorem recodeBody_ok {s₀ s : State} {base : Addr} (hs : Scratch s₀ base) {src nb X w dst : Nat}
    (hw : 2 ≤ w ∧ w ≤ 8) (hdst : dst < 2) (hsrc : 3104 ≤ src) (hfit : src + nb + 8 ≤ 8192)
    (hX : Copied s₀.mem base src nb X) (hnb : 8 * nb ≤ 512) {bound : List Instr}
    (hb : BoundSpec s₀ base dst nb bound) {st : St} (hi : st.i < 8 * nb)
    (ht : RecInv s₀ base nb X w dst st s) :
    WP isa (.seq (recodeStep src w dst) (.block bound)) s fun v =>
      RecInv s₀ base nb X w dst (step w X st) v ∧ v.cf = some (decide ((step w X st).i < 8 * nb)) := by
  have hst : Scratch s base := ht.keep.scratch hs
  have hX' : Copied s.mem base src nb X :=
    hX.of_keep hsrc hfit fun x hx => ht.keep.mem x (by omega_arith)
  refine WP.seq (WP.mono (recodeStep_ok hst hw hdst hfit hX' hi hnb ht.good.c ht.rsi ht.r8 ht.dig)
    fun u ⟨ursi, ur8, udig, ku⟩ => ?_)
  have kt := ht.keep.trans ku
  have hsi := step_i (K := X) (by omega_arith : 1 ≤ w) st
  refine WP.mono (hb u kt _ ursi (by omega_arith)) fun v ⟨vcf, kv⟩ => ?_
  exact ⟨⟨reach_step (by omega_arith) ht.reach hi, step_good hw.1 ht.good, by omega_arith,
    by rw [kv.1 _ (by decide)]; exact ursi, by rw [kv.1 _ (by decide)]; exact ur8,
    fun j hj => by rw [kv.2.1]; exact udig j hj, kt.trans (RecKeep.of_keeps kv (by decide))⟩, vcf⟩

theorem recodeLoop_ok {s₀ s : State} {base : Addr} (hs : Scratch s₀ base) {src nb X w dst : Nat}
    (hw : 2 ≤ w ∧ w ≤ 8) (hdst : dst < 2) (hsrc : 3104 ≤ src) (hfit : src + nb + 8 ≤ 8192)
    (hX : Copied s₀.mem base src nb X) (hnb : 8 * nb ≤ 512) {bound : List Instr}
    (hb : BoundSpec s₀ base dst nb bound) {st : St} (hi : st.i < 8 * nb)
    (h : RecInv s₀ base nb X w dst st s) :
    WP isa (.loop (.seq (recodeStep src w dst) (.block bound)) .b) s fun t =>
      RecInv s₀ base nb X w dst (run w X (8 * nb) (8 * nb) init) t := by
  apply WP.loop (fun m t => ∃ st, RecInv s₀ base nb X w dst st t ∧ st.i < 8 * nb ∧ m = 8 * nb - st.i)
    (n := 8 * nb - st.i)
  · rintro m t ⟨st, ht, hi, rfl⟩
    have hsi := step_i (K := X) (by omega_arith : 1 ≤ w) st
    refine WP.mono (recodeBody_ok hs hw hdst hsrc hfit hX hnb hb hi ht) fun v ⟨hv, vcf⟩ => ?_
    by_cases hlt : (step w X st).i < 8 * nb
    · exact Or.inr ⟨by simp only [eval, vcf, decide_eq_true hlt], _, by omega_arith, _, hv, hlt, rfl⟩
    · refine Or.inl ⟨by simp only [eval, vcf, decide_eq_false hlt], ?_⟩
      rw [← reach_end (reach_step (by omega_arith) ht.reach hi) (by omega_arith)]
      exact hv
  · exact ⟨st, h, hi, rfl⟩

theorem recodeStart_ok (s : State) :
    WP isa (.block [.mov32 .rsi (.imm 0), .mov32 .r8 (.imm 0)]) s fun t =>
      t.gpr .rsi = BitVec.ofNat 64 0 ∧ t.gpr .r8 = BitVec.ofNat 64 0 ∧ Keeps [.rsi, .r8] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
    RegUpd.gpr_setReg, reduceCtorEq, ite_true, ite_false, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨rfl, rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]

/-- The digit 1 at the bit `i`, for the last carry. -/
theorem recodeLast_ok {s : State} {base : Addr} (hs : Scratch s base) {i dst : Nat}
    (hi : i < 528) (hdst : dst < 2) (hrsi : s.gpr .rsi = BitVec.ofNat 64 i) :
    WP isa (.block [.mov .rax (.reg .rsi), .alu .add .rax (.reg .rax), .mov32 .rbx (.imm 1),
      .store8 { base := .rdi, index := some .rax, disp := ((2048 + dst : Nat) : Int) } .rbx]) s fun t =>
      t.mem = s.mem.writeW (off base (2048 + 2 * i + dst)) (BitVec.ofNat 8 1) ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hea : base + (BitVec.ofNat 64 i + BitVec.ofNat 64 i) * BitVec.ofNat 64 1 +
      BitVec.ofInt 64 ((2048 + dst : Nat) : Int) = off base (2048 + 2 * i + dst) := by
    rw [BitVec.ofInt_natCast, BitVec.mul_one, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact congrArg (fun n => off base n) (by omega_arith)
  have hrg : InRegions s.wr (off base (2048 + 2 * i + dst)) 1 :=
    ⟨_, hs.wr, Offset.contains_base _ (show 2048 + 2 * i + dst + 1 ≤ 8192 by omega_arith) (by omega_arith)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu, State.store8,
    State.ea, State.setReg32, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.wr_setReg,
    RegUpd.wr_arithFlags, RegUpd.mem_setReg, RegUpd.mem_arithFlags, RegUpd.rd_setReg,
    RegUpd.rd_arithFlags, hrsi, hs.rdi, hea, hrg, reduceCtorEq, ite_true, ite_false, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, fun r ha hb => ?_, trivial, trivial⟩
  simp only [ha, hb, ite_false]

/-- ZF set if the last carry `c` is zero. -/
theorem testR8_ok (s : State) {c : Nat} (hc : c ≤ 1) (h8 : s.gpr .r8 = BitVec.ofNat 64 c) :
    WP isa (.block [.alu .test .r8 (.reg .r8)]) s fun t => t.zf = some (decide (c = 0)) ∧ Keeps [] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, RegUpd.zf_arithFlags,
    h8, BitVec.and_self, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun _ _ => rfl, rfl, rfl, rfl⟩
  obtain h0 | h1 : c = 0 ∨ c = 1 := by omega_arith
  · rw [h0]; rfl
  · rw [h1]; rfl

/-- The recoding of `X < 2 ^ (8 nb)` into the zeroed array `dst`: its digits' bytes. -/
theorem recode_ok {s : State} {base : Addr} (hs : Scratch s base) {src nb X w dst : Nat}
    (hw : 2 ≤ w ∧ w ≤ 8) (hdst : dst < 2) (hsrc : 3104 ≤ src) (hfit : src + nb + 8 ≤ 8192)
    (hX : Copied s.mem base src nb X) (hnb : 0 < nb ∧ 8 * nb ≤ 512) {bound : List Instr}
    (hb : BoundSpec s base dst nb bound) (hz : ∀ j < 528, dig s.mem base dst j = 0) :
    WP isa (recode src w dst bound) s fun t =>
      (∀ j < 528, dig t.mem base dst j = digits w X (8 * nb) j) ∧ RecKeep base dst s t := by
  rw [recode]
  refine WP.seq (WP.mono (recodeStart_ok s) fun a ⟨arsi, ar8, ka⟩ => ?_)
  have ha : RecInv s base nb X w dst init a :=
    ⟨reach_init w X _, init_good w X, by simp only [init]; omega_arith, arsi, ar8,
      fun j hj => by rw [ka.2.1]; exact hz j hj, RecKeep.of_keeps ka (by decide)⟩
  refine WP.seq (WP.mono (recodeLoop_ok hs hw hdst hsrc hfit hX hnb.2 hb (by simp only [init]; omega_arith) ha)
    fun b hb' => ?_)
  generalize hF : run w X (8 * nb) (8 * nb) init = F at hb'
  have hFi : 8 * nb ≤ F.i := hF ▸ run_end (by omega_arith) _ (by simp only [init]; omega_arith)
  have hFl : F.i < 8 * nb + w := hb'.lt
  have hd : ∀ j, digits w X (8 * nb) j = fin F j := fun j => by rw [← hF]; rfl
  rw [recodeEnd]
  have hc := hb'.good.c
  refine WP.seq (WP.mono (testR8_ok b hc hb'.r8) fun c ⟨cz, kc⟩ => ?_)
  refine WP.ite (!decide (F.c = 0)) (by simp only [eval, cz, Option.map_some]) (fun h => ?_) (fun h => ?_)
  · have hc1 : F.c ≠ 0 := by simpa using h
    refine WP.mono (recodeLast_ok (hb'.keep.scratch hs |>.of_keeps kc (by decide)) (i := F.i) (by omega_arith) hdst
      (by rw [kc.1 _ (by decide)]; exact hb'.rsi)) fun t ⟨tm, tg, trd, twr⟩ => ?_
    refine ⟨fun j hj => ?_, hb'.keep.trans (RecKeep.of_keeps kc (by decide)) |>.trans
      ⟨fun r hr => tg r (fun e => hr (by rw [e]; decide)) (fun e => hr (by rw [e]; decide)), trd, twr,
        fun x hx => by rw [tm, keep_write (by omega_arith) hdst _ x hx]⟩⟩
    rw [tm, dig_write (by omega_arith) hdst (by decide) hj, kc.2.1, hd, fin]
    by_cases hj' : j = F.i
    · rw [ite_eq_left hj', ite_eq_left ⟨hc1, hj'⟩]
    · rw [ite_eq_right hj', ite_eq_right (fun h => hj' h.2), hb'.dig j hj]
  · have hc0 : F.c = 0 := by simpa using h
    refine WP.block_nil ⟨fun j hj => ?_, hb'.keep.trans (RecKeep.of_keeps kc (by decide))⟩
    rw [kc.2.1, hd, fin, ite_eq_right (fun h => h.1 hc0), hb'.dig j hj]

end VG.Proof.Ed25519.X86_64

end

end

/-! ### `Ed25519.X86_64.WindowSlide`, which only this module used -/

section

/-!
# Verification's windows: a doubling and the digits at each position

The digits' arrays hold `fA` (`k`'s) and `fB` (`S`'s) up to position `top` (`DigitsAre`,
`Digits`). After position `p` the accumulator represents `winVal p`, the digits from `p` on
weighted by powers of two (`hiVal`) times `A` and `-B` (`WinLoop`); before the digits at `p` are
added, twice `winVal (p + 1)` (`WinMid`), with `T` computed if a digit at `p` is nonzero, as an
addition needs it. `windows_ok`: from one above `top` with the identity, the windows skip the
leading zero digits and end at position 0.
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open VG.Proof.X25519.X86_64 (off ofs Keeps clob Outside)

variable {fld : Arith} [EdArith fld] {pt : Point64.Ops} [PtOk pt]

/-- What a position of the windows may change. -/
structure ByteKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ clob → r ≠ .rbx → r ≠ .rsi → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside base 56 1832 s.mem t.mem

theorem ByteKeep.refl (base : Addr) (s : State) : ByteKeep base s s :=
  ⟨fun _ _ _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩

theorem ByteKeep.trans {base : Addr} {s t u : State} (h : ByteKeep base s t) (k : ByteKeep base t u) :
    ByteKeep base s u :=
  ⟨fun r a b c => (k.gpr r a b c).trans (h.gpr r a b c), k.rd.trans h.rd, k.wr.trans h.wr,
    h.mem.trans k.mem⟩

theorem ByteKeep.of_win {base : Addr} {s t : State} (h : WinKeep base s t) : ByteKeep base s t :=
  ⟨h.gpr, h.rd, h.wr, Outside.widen h.mem⟩

theorem ByteKeep.of_keeps {base : Addr} {s t : State} {rs : List Reg} (h : Keeps rs s t)
    (hrs : ∀ r ∈ rs, r = .rbx ∨ r = .rsi ∨ r ∈ clob) : ByteKeep base s t :=
  ByteKeep.of_win (WinKeep.of_keeps h hrs)

theorem ByteKeep.scratch {base : Addr} {s t : State} (h : ByteKeep base s t) (hs : Scratch s base) :
    Scratch t base := ⟨(h.gpr _ (by decide) (by decide) (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

theorem WinCtx.of_byte {base kp sp T : Addr} {A : EPoint dZ} {s t : State} (h : WinCtx base kp sp T A s)
    (k : ByteKeep base s t) : WinCtx base kp sp T A t := by
  refine ⟨k.scratch h.scratch, (k.mem.word (Or.inr (by decide)) (by decide)).trans h.kHeader,
    (k.mem.word (Or.inr (by decide)) (by decide)).trans h.sHeader, ?_, ?_, h.kFar, h.sFar, ?_, ?_,
    h.aTab.of_win k.mem (by decide) (by decide),
    (k.mem.word (Or.inr (by decide)) (by decide)).trans h.bHeader,
    h.bTab.of_outside k.rd k.wr k.mem (by decide)⟩
  · intro i hi; rw [k.rd, k.wr]; exact h.kRead i hi
  · intro i hi; rw [k.rd, k.wr]; exact h.sRead i hi
  · intro i hi; rw [k.rd, k.wr]; exact h.kRead8 i hi
  · intro i hi; rw [k.rd, k.wr]; exact h.sRead8 i hi

/-! ## The digits -/

/-- The digits' arrays hold `fA` and `fB` at the positions below 528. -/
def DigitsAre (m : Mem) (base : Addr) (fA fB : Nat → Nat) : Prop :=
  ∀ p < 528, dig m base 0 p = fA p ∧ dig m base 1 p = fB p

theorem DigitsAre.of_byte {m m' : Mem} {base : Addr} {fA fB : Nat → Nat} (h : DigitsAre m base fA fB)
    (k : Outside base 56 1832 m m') : DigitsAre m' base fA fB := by
  intro p hp
  have e (dst : Nat) (hd : dst < 2) : dig m' base dst p = dig m base dst p := by
    simp only [dig]
    rw [k _ (Or.inr (by rw [VG.Proof.X25519.X86_64.ofs_off' base (by omega_arith)]; omega_arith))]
  rw [e 0 (by decide), e 1 (by decide)]
  exact h p hp

/-- What the windows assume of the digits: their bytes are entries of the tables. -/
structure Digits (fA fB : Nat → Nat) (top : Nat) : Prop where
  top : top < 528
  a : ∀ p, fA p ≤ 16
  b : ∀ p, fB p ≤ 128

/-- The value of `f`'s digits from position `p` to `top`. -/
def hiVal (f : Nat → Nat) (top p : Nat) : Int :=
  Recode.hsum (fun j => Recode.dec (f j)) p (top + 1 - p)

theorem hiVal_step (f : Nat → Nat) {top p : Nat} (hp : p ≤ top) :
    hiVal f top p = Recode.dec (f p) + 2 * hiVal f top (p + 1) := by
  simp only [hiVal]
  rw [show top + 1 - p = (top + 1 - (p + 1)) + 1 by omega_arith, Recode.hsum_succ]

theorem hiVal_zero (f : Nat → Nat) {top p : Nat} (h : ∀ j, p ≤ j → j ≤ top → f j = 0) :
    hiVal f top p = 0 :=
  Recode.hsum_eq_zero fun j h1 h2 => by rw [h j h1 (by omega_arith)]; rfl

/-- The accumulated point after position `p`. -/
def winVal (A : EPoint dZ) (fA fB : Nat → Nat) (top p : Nat) : EPoint dZ :=
  (hiVal fA top p) • A + (hiVal fB top p) • (-baseAff)

theorem winVal_step (A : EPoint dZ) (fA fB : Nat → Nat) {top p : Nat} (hp : p ≤ top) :
    winVal A fA fB top p = (2 : Int) • winVal A fA fB top (p + 1) + (Recode.dec (fA p)) • A +
      (Recode.dec (fB p)) • (-baseAff) := by
  simp only [winVal]
  rw [hiVal_step fA hp, hiVal_step fB hp]
  module

/-! ## The invariants -/

/-- The counter is `c` and the accumulator represents `v`. -/
structure WinAt (s₀ : State) (base kp sp T : Addr) (A : EPoint dZ) (fA fB : Nat → Nat) (v : EPoint dZ)
    (c : Nat) (s : State) : Prop where
  ctx : WinCtx base kp sp T A s
  d : env s.mem base 16 = Spec.Ed25519.d
  counter : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 c
  digits : DigitsAre s.mem base fA fB
  value : RepP (point (env s.mem base) 0 1 2 3) v
  keep : ByteKeep base s₀ s

/-- After position `p`: the counter is `p`, and the accumulator represents `winVal p`. -/
abbrev WinLoop (s₀ : State) (base kp sp T : Addr) (A : EPoint dZ) (fA fB : Nat → Nat) (top p : Nat)
    (s : State) : Prop :=
  WinAt s₀ base kp sp T A fA fB (winVal A fA fB top p) p s

/-- Before the digits at `p` are added: the accumulator represents twice `winVal (p + 1)`, with
`T` if a digit at `p` is nonzero. -/
structure WinMid (s₀ : State) (base kp sp T : Addr) (A : EPoint dZ) (fA fB : Nat → Nat) (top p : Nat)
    (s : State) : Prop where
  ctx : WinCtx base kp sp T A s
  d : env s.mem base 16 = Spec.Ed25519.d
  counter : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 p
  digits : DigitsAre s.mem base fA fB
  value : RepP (point (env s.mem base) 0 1 2 3) ((2 : Int) • winVal A fA fB top (p + 1))
  full : fA p ≠ 0 ∨ fB p ≠ 0 → Rep (point (env s.mem base) 0 1 2 3) ((2 : Int) • winVal A fA fB top (p + 1))
  keep : ByteKeep base s₀ s

theorem WinMid.of_byte {s₀ s t : State} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat}
    {top p : Nat} (h : WinMid s₀ base kp sp T A fA fB top p s) (k : ByteKeep base s t)
    (hm : ∀ i : Slot, i.val < 4 ∨ i.val = 16 → env t.mem base i = env s.mem base i)
    (hc : t.mem.readW (off base 56) 64 = s.mem.readW (off base 56) 64) :
    WinMid s₀ base kp sp T A fA fB top p t := by
  obtain hp : point (env t.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 := by
    simp only [point, hm 0 (by decide), hm 1 (by decide), hm 2 (by decide), hm 3 (by decide)]
  exact ⟨h.ctx.of_byte k, (hm 16 (by decide)).trans h.d, hc.trans h.counter,
    h.digits.of_byte k.mem, by rw [hp]; exact h.value,
    fun hf => by rw [hp]; exact h.full hf, h.keep.trans k⟩

/-! ## A position's digits -/

/-- After `k`'s digit at `p` is added: the accumulator represents `v + [dec (fA p)]A`, with `T` if
`S`'s digit at `p` is nonzero. -/
structure WinHalf (s₀ : State) (base kp sp T : Addr) (A : EPoint dZ) (fA fB : Nat → Nat) (top p : Nat)
    (s : State) : Prop where
  ctx : WinCtx base kp sp T A s
  d : env s.mem base 16 = Spec.Ed25519.d
  counter : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 p
  digits : DigitsAre s.mem base fA fB
  value : RepP (point (env s.mem base) 0 1 2 3)
    ((2 : Int) • winVal A fA fB top (p + 1) + (Recode.dec (fA p)) • A)
  full : fB p ≠ 0 → Rep (point (env s.mem base) 0 1 2 3)
    ((2 : Int) • winVal A fA fB top (p + 1) + (Recode.dec (fA p)) • A)
  keep : ByteKeep base s₀ s

/-- `k`'s digit at `p` added, with `T` if `tb`, which `S`'s nonzero digit at `p` needs. -/
theorem addA_ok {s₀ s : State} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat} {top p : Nat}
    {tb : Bool} (hdg : Digits fA fB top) (hp : p ≤ top) (h : WinMid s₀ base kp sp T A fA fB top p s)
    (htb : fB p ≠ 0 → tb = true) :
    WP isa (.seq (.block (digitAt 0)) (addDigit 5376 (pt.add tb))) s
      (WinHalf s₀ base kp sp T A fA fB top p) := by
  obtain hdA : dig s.mem base 0 p = fA p := (h.digits p (by have := hdg.top; omega_arith)).1
  refine WP.seq (WP.mono (digitAt_ok h.ctx.scratch (by have := hdg.top; omega_arith) (by decide) h.counter)
    fun a ⟨ab, az, ka⟩ => ?_)
  rw [hdA] at ab az
  obtain kaw : WinKeep base s a := WinKeep.of_keeps ka (by decide)
  obtain ha := h.ctx.of_keep kaw
  obtain aenv : env a.mem base = env s.mem base := by rw [ka.2.1]
  refine WP.mono (addDigit_ok (a := (2 : Int) • winVal A fA fB top (p + 1)) (addCachedT_spec (pt := pt) tb)
    ha.scratch (by decide) (by decide) ha.aTab (fA p) (hdg.a p) ab az (by rw [aenv]; exact h.d)
    (by rw [aenv]; exact h.value) (fun hv => by rw [aenv]; exact h.full (Or.inl hv)))
    fun b ⟨bp, bf, bd, kb⟩ => ?_
  obtain kab := (ByteKeep.of_win kaw).trans (ByteKeep.of_win kb)
  refine ⟨h.ctx.of_byte kab, by rw [bd, aenv]; exact h.d,
    kb.counter.trans (kaw.counter.trans h.counter), h.digits.of_byte kab.mem, bp,
    fun hv => bf ?_, h.keep.trans kab⟩
  by_cases hA : fA p = 0
  · exact Or.inr ⟨hA, by rw [aenv]; exact h.full (Or.inr hv)⟩
  · exact Or.inl ⟨htb hv, hA⟩

/-- `S`'s digit at `p` added, without `T`. -/
theorem addB_ok {badd : Prog isa} (hb : AddAffSpec badd) {s₀ s : State} {base kp sp T : Addr} {A : EPoint dZ}
    {fA fB : Nat → Nat} {top p : Nat}
    (hdg : Digits fA fB top) (hp : p ≤ top) (h : WinHalf s₀ base kp sp T A fA fB top p s) :
    WP isa (.seq (.block (digitAt 1)) (addBase badd)) s (WinLoop s₀ base kp sp T A fA fB top p) := by
  obtain hdB : dig s.mem base 1 p = fB p := (h.digits p (by have := hdg.top; omega_arith)).2
  refine WP.seq (WP.mono (digitAt_ok h.ctx.scratch (by have := hdg.top; omega_arith) (by decide) h.counter)
    fun c ⟨cb, cz, kc⟩ => ?_)
  rw [hdB] at cb cz
  obtain kcw : WinKeep base s c := WinKeep.of_keeps kc (by decide)
  obtain hc' := h.ctx.of_keep kcw
  obtain cenv : env c.mem base = env s.mem base := by rw [kc.2.1]
  refine WP.mono (addBase_ok hb (a := (2 : Int) • winVal A fA fB top (p + 1) + (Recode.dec (fA p)) • A)
    hc'.scratch hc'.bHeader hc'.bTab (fB p) (hdg.b p) cb cz
    (by rw [cenv]; exact h.d) (by rw [cenv]; exact h.value) (fun hv => by rw [cenv]; exact h.full hv))
    fun t ⟨tp, td, kt⟩ => ?_
  obtain kct := (ByteKeep.of_win kcw).trans (ByteKeep.of_win kt)
  refine ⟨h.ctx.of_byte kct, by rw [td, cenv]; exact h.d, kt.counter.trans (kcw.counter.trans h.counter),
    h.digits.of_byte kct.mem, ?_, h.keep.trans kct⟩
  rw [winVal_step A fA fB hp]; exact tp

/-- The digits at `p` added: from before them to after `p`. `S`'s digit is read first: if it is
zero, `k`'s addition is the last and computes no `T`. -/
theorem addsAt_ok {badd : Prog isa} (hb : AddAffSpec badd) {s₀ s : State} {base kp sp T : Addr} {A : EPoint dZ}
    {fA fB : Nat → Nat} {top p : Nat}
    (hdg : Digits fA fB top) (hp : p ≤ top) (h : WinMid s₀ base kp sp T A fA fB top p s) :
    WP isa (addsAt pt badd) s (WinLoop s₀ base kp sp T A fA fB top p) := by
  rw [addsAt]
  refine WP.seq (WP.mono (digitAt_ok h.ctx.scratch (by have := hdg.top; omega_arith) (by decide) h.counter)
    fun a ⟨_, az, ka⟩ => ?_)
  rw [(h.digits p (by have := hdg.top; omega_arith)).2] at az
  obtain ha := h.of_byte (ByteKeep.of_keeps ka (by decide)) (fun i _ => by rw [ka.2.1]) (by rw [ka.2.1])
  refine WP.ite (!decide (fB p = 0)) (by simp only [eval, az, Option.map_some]) (fun hz => ?_) (fun hz => ?_)
  · apply WP.assoc
    exact WP.seq (WP.mono (addA_ok (tb := true) hdg hp ha fun _ => rfl) fun _ hh => addB_ok hb hdg hp hh)
  · have h0 : fB p = 0 := by simpa using hz
    refine WP.mono (addA_ok (tb := false) hdg hp ha fun hf => absurd h0 hf) fun t ht => ?_
    obtain e : winVal A fA fB top p = (2 : Int) • winVal A fA fB top (p + 1) + (Recode.dec (fA p)) • A := by
      rw [winVal_step A fA fB hp, h0]; simp [Recode.dec]
    exact ⟨ht.ctx, ht.d, ht.counter, ht.digits, by rw [e]; exact ht.value, ht.keep⟩

/-! ## The doubling -/

/-- One doubling, with `T` if a digit at the counter's position `p` is nonzero: after `p + 1`,
with the counter at `p`, to before the digits at `p`. -/
theorem dblAt_ok {s₀ s : State} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat} {top p : Nat}
    (hdg : Digits fA fB top) (hp : p ≤ top) (h : WinAt s₀ base kp sp T A fA fB (winVal A fA fB top (p + 1)) p s) :
    WP isa (dblAt fld) s (WinMid s₀ base kp sp T A fA fB top p) := by
  have hb := h.ctx.scratch.nowrap
  rw [dblAt]
  refine WP.seq (WP.mono (digitsAt_ok h.ctx.scratch (by have := hdg.top; omega_arith) h.counter) fun a ⟨az, ka⟩ => ?_)
  rw [(h.digits p (by have := hdg.top; omega_arith)).1, (h.digits p (by have := hdg.top; omega_arith)).2] at az
  obtain kaw : WinKeep base s a := WinKeep.of_keeps ka (by decide)
  obtain ha := h.ctx.of_keep kaw
  obtain aenv : env a.mem base = env s.mem base := by rw [ka.2.1]
  obtain hv : RepP (point (env a.mem base) 0 1 2 3) (winVal A fA fB top (p + 1)) := by rw [aenv]; exact h.value
  have fin (t : State) (b : Bool) (kt : Keep base a t)
      (tp : RepP (point (env t.mem base) 0 1 2 3) (winVal A fA fB top (p + 1) + winVal A fA fB top (p + 1)))
      (tf : b = true → Rep (point (env t.mem base) 0 1 2 3)
        (winVal A fA fB top (p + 1) + winVal A fA fB top (p + 1)))
      (th : ∀ i : Slot, 16 ≤ i.val → env t.mem base i = env a.mem base i)
      (hbz : (fA p ≠ 0 ∨ fB p ≠ 0) → b = true) :
      WinMid s₀ base kp sp T A fA fB top p t := by
    obtain e : winVal A fA fB top (p + 1) + winVal A fA fB top (p + 1) = (2 : Int) • winVal A fA fB top (p + 1) := by
      rw [two_zsmul]
    rw [e] at tp tf
    obtain kt' : ByteKeep base s t := (ByteKeep.of_win kaw).trans (ByteKeep.of_win (WinKeep.of_keep kt))
    exact ⟨h.ctx.of_byte kt', by rw [th 16 (by decide), aenv]; exact h.d,
      (kt.mem.word (Or.inl (by decide)) (by decide)).trans (kaw.counter.trans h.counter),
      h.digits.of_byte kt'.mem, tp, fun hf => tf (hbz hf), h.keep.trans kt'⟩
  refine WP.ite (!decide (fA p = 0 ∧ fB p = 0)) (by simp only [eval, az, Option.map_some]) (fun hz => ?_)
    (fun hz => ?_)
  · refine WP.mono (dblH_ok (fld := fld) ha.scratch true hv) fun t ⟨kt, tp, tf, th⟩ => ?_
    exact fin t true kt tp tf th fun _ => rfl
  · have h0 : fA p = 0 ∧ fB p = 0 := by simpa using hz
    refine WP.mono (dblH_ok (fld := fld) ha.scratch false hv) fun t ⟨kt, tp, tf, th⟩ => ?_
    exact fin t false kt tp tf th fun hf => by omega_arith

/-- The position below: from after `p + 1` to after `p`, ZF set if `p` is zero. -/
theorem stepAt_ok {s₀ s : State} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat} {top p : Nat}
    (hdg : Digits fA fB top) (hp : p ≤ top) (h : WinLoop s₀ base kp sp T A fA fB top (p + 1) s) :
    WP isa (stepAt fld pt) s fun t => t.zf = some (decide (p = 0)) ∧ WinLoop s₀ base kp sp T A fA fB top p t := by
  have hb := h.ctx.scratch.nowrap
  rw [stepAt]
  refine WP.seq (WP.mono (batchBegin_ok h.ctx.scratch p h.counter) fun a ⟨_, ac, ag, ar, aw, am⟩ => ?_)
  obtain ka : ByteKeep base s a := ⟨fun r _ hb _ => ag r hb, ar, aw, am.mono (by decide) (by decide)⟩
  obtain ha : WinAt s₀ base kp sp T A fA fB (winVal A fA fB top (p + 1)) p a :=
    ⟨h.ctx.of_byte ka, by rw [header_env am]; exact h.d, ac, h.digits.of_byte ka.mem,
      by rw [header_env am]; exact h.value, h.keep.trans ka⟩
  refine WP.seq (WP.mono (dblAt_ok hdg hp ha) fun b hb' => ?_)
  refine WP.seq (WP.mono (addsAt_ok addAff_aff hdg hp hb') fun c hc => ?_)
  refine WP.mono (counterTest_ok hc.ctx.scratch (by have := hdg.top; omega_arith) hc.counter) fun t ⟨tz, kt⟩ => ?_
  obtain kt' := ByteKeep.of_keeps (base := base) kt (by decide)
  exact ⟨tz, hc.ctx.of_byte kt', by rw [kt.2.1]; exact hc.d, by rw [kt.2.1]; exact hc.counter,
    by rw [kt.2.1]; exact hc.digits, by rw [kt.2.1]; exact hc.value, hc.keep.trans kt'⟩

/-! ## Skipping the leading zero digits -/

/-- Skipping, with the counter at `q`: the digits from `q` to `top` are zero, and the accumulator
represents the identity, with `T`. -/
structure SkipAt (s₀ : State) (base kp sp T : Addr) (A : EPoint dZ) (fA fB : Nat → Nat) (top q : Nat)
    (s : State) : Prop where
  loop : WinLoop s₀ base kp sp T A fA fB top q s
  zero : ∀ j, q ≤ j → j ≤ top → fA j = 0 ∧ fB j = 0
  full : Rep (point (env s.mem base) 0 1 2 3) 0
  pos : 0 < q
  le : q ≤ top + 1

theorem cmpSelf_ok (s : State) :
    WP isa (.block [.alu .cmp .rax (.reg .rax)]) s fun t => t.zf = some true ∧ Keeps [] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, RegUpd.zf_arithFlags,
    BitVec.sub_self, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, fun _ _ => rfl, rfl, rfl, rfl⟩

theorem winVal_zero {A : EPoint dZ} {fA fB : Nat → Nat} {top q : Nat}
    (h : ∀ j, q ≤ j → j ≤ top → fA j = 0 ∧ fB j = 0) : winVal A fA fB top q = 0 := by
  simp only [winVal, hiVal_zero fA (fun j h1 h2 => (h j h1 h2).1), hiVal_zero fB (fun j h1 h2 => (h j h1 h2).2),
    zero_smul, add_zero]

/-- Whether the skipping stops at `p`. -/
def skipStops (fA fB : Nat → Nat) (p : Nat) : Bool := !decide (fA p = 0 ∧ fB p = 0) || decide (p = 0)

/-- A step of the skipping, below `p + 1`: it stops at `p` if a digit there is nonzero or `p` is
zero, before the digits at `p`; else it goes on, from `p`. -/
theorem skipTop_ok {s₀ s : State} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat} {top p : Nat}
    (hdg : Digits fA fB top) (h : SkipAt s₀ base kp sp T A fA fB top (p + 1) s) :
    WP isa skipTop s fun t => t.zf = some (skipStops fA fB p) ∧
      (skipStops fA fB p = true → WinMid s₀ base kp sp T A fA fB top p t) ∧
      (skipStops fA fB p = false → SkipAt s₀ base kp sp T A fA fB top p t) := by
  have hle := h.le
  have hl := h.loop
  rw [skipTop]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (batchBegin_ok hl.ctx.scratch p hl.counter) fun a ⟨_, ac, ag, ar, aw, am⟩ => ?_
  obtain ka : ByteKeep base s a := ⟨fun r _ hb _ => ag r hb, ar, aw, am.mono (by decide) (by decide)⟩
  obtain hsa := hl.ctx.of_byte ka
  refine WP.mono (digitsAt_ok hsa.scratch (by have := hdg.top; omega_arith) ac) fun b ⟨bz, kb⟩ => ?_
  obtain hdA := (hl.digits.of_byte ka.mem p (by have := hdg.top; omega_arith))
  rw [hdA.1, hdA.2] at bz
  obtain kb' : ByteKeep base a b := ByteKeep.of_keeps kb (by decide)
  obtain kab := ka.trans kb'
  obtain benv : env b.mem base = env s.mem base := by rw [kb.2.1, header_env am]
  obtain bc : b.mem.readW (off base 56) 64 = BitVec.ofNat 64 p := by rw [kb.2.1]; exact ac
  obtain h0 : winVal A fA fB top (p + 1) = 0 := winVal_zero h.zero
  have mid (t : State) (kt : ByteKeep base s t) (te : env t.mem base = env s.mem base)
      (tc : t.mem.readW (off base 56) 64 = BitVec.ofNat 64 p) : WinMid s₀ base kp sp T A fA fB top p t := by
    obtain hr : Rep (point (env t.mem base) 0 1 2 3) ((2 : Int) • winVal A fA fB top (p + 1)) := by
      rw [te, h0, smul_zero]; exact h.full
    exact ⟨hl.ctx.of_byte kt, by rw [te]; exact hl.d, tc, hl.digits.of_byte kt.mem, hr.proj, fun _ => hr,
      hl.keep.trans kt⟩
  refine WP.ite (!decide (fA p = 0 ∧ fB p = 0)) (by simp only [eval, bz, Option.map_some])
    (fun hz => ?_) (fun hz => ?_)
  · have hst : skipStops fA fB p = true := by
      simp only [skipStops, hz, Bool.true_or]
    refine WP.mono (cmpSelf_ok b) fun t ⟨tz, kt⟩ => ⟨by rw [tz, hst], fun _ => mid t
      (kab.trans (ByteKeep.of_keeps kt (by decide))) (by rw [kt.2.1, benv]) (by rw [kt.2.1]; exact bc),
      fun hf => absurd hf (by rw [hst]; decide)⟩
  · have hz0 : fA p = 0 ∧ fB p = 0 := by simpa using hz
    refine WP.mono (counterTest_ok (kab.scratch hl.ctx.scratch) (by have := hdg.top; omega_arith) bc)
      fun t ⟨tz, kt⟩ => ?_
    obtain kt' := kab.trans (ByteKeep.of_keeps kt (by decide))
    obtain te : env t.mem base = env s.mem base := by rw [kt.2.1, benv]
    obtain tc : t.mem.readW (off base 56) 64 = BitVec.ofNat 64 p := by rw [kt.2.1]; exact bc
    obtain hst : skipStops fA fB p = decide (p = 0) := by
      simp only [skipStops, hz0, and_self, decide_true, Bool.not_true, Bool.false_or]
    by_cases hp0 : p = 0
    · subst hp0
      exact ⟨by rw [tz, hst], fun _ => mid t kt' te tc, fun hf => absurd hf (by rw [hst]; decide)⟩
    · have hz' : ∀ j, p ≤ j → j ≤ top → fA j = 0 ∧ fB j = 0 := fun j h1 h2 => by
        rcases Nat.eq_or_lt_of_le h1 with rfl | h1'
        · exact hz0
        · exact h.zero j (by omega_arith) h2
      refine ⟨by rw [tz, hst], fun ht => absurd ht (by rw [hst]; simp [hp0]),
        fun _ => ⟨⟨hl.ctx.of_byte kt', by rw [te]; exact hl.d, tc,
        hl.digits.of_byte kt'.mem, ?_, hl.keep.trans kt'⟩, hz', by rw [te]; exact h.full, by omega_arith, by omega_arith⟩⟩
      rw [te, winVal_zero hz']; exact h.full.proj

/-- The windows, from one above `top` with the identity, to after position 0. -/
theorem windows_ok {s₀ s : State} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat} {top : Nat}
    (hdg : Digits fA fB top) (h : SkipAt s₀ base kp sp T A fA fB top (top + 1) s) :
    WP isa (windowsWith fld pt) s (WinLoop s₀ base kp sp T A fA fB top 0) := by
  rw [windowsWith]
  refine WP.seq (WP.mono (show WP isa (.loop skipTop .ne) s fun t =>
      ∃ p, p ≤ top ∧ WinMid s₀ base kp sp T A fA fB top p t by
    apply WP.loop (fun q t => SkipAt s₀ base kp sp T A fA fB top q t) (n := top + 1)
    · intro q t ht
      obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := ht.pos; omega_arith : q ≠ 0)
      have hle := ht.le
      refine WP.mono (skipTop_ok hdg ht) fun u ⟨uz, ut, uf⟩ => ?_
      cases hs : skipStops fA fB p
      · exact Or.inr ⟨by simp only [eval, uz, hs, Option.map_some, Bool.not_false], p, by omega_arith, uf hs⟩
      · exact Or.inl ⟨by simp only [eval, uz, hs, Option.map_some, Bool.not_true], p, by omega_arith, ut hs⟩
    · exact h) fun a ⟨p, hp, ha⟩ => ?_)
  refine WP.seq (WP.mono (addsAt_ok addCached_aff hdg hp ha) fun b hb => ?_)
  refine WP.seq (WP.mono (counterTest_ok hb.ctx.scratch (by have := hdg.top; omega_arith) hb.counter)
    fun c ⟨cz, kc⟩ => ?_)
  obtain kc' := ByteKeep.of_keeps (base := base) kc (by decide)
  obtain hc : WinLoop s₀ base kp sp T A fA fB top p c :=
    ⟨hb.ctx.of_byte kc', by rw [kc.2.1]; exact hb.d, by rw [kc.2.1]; exact hb.counter,
      by rw [kc.2.1]; exact hb.digits, by rw [kc.2.1]; exact hb.value, hb.keep.trans kc'⟩
  refine WP.ite (!decide (p = 0)) (by simp only [eval, cz, Option.map_some]) (fun hz => ?_) (fun hz => ?_)
  · have hp0 : p ≠ 0 := by simpa using hz
    apply WP.loop (fun n t => WinLoop s₀ base kp sp T A fA fB top n t ∧ 0 < n ∧ n ≤ top) (n := p)
    · intro n t ⟨ht, hn0, hn⟩
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega_arith : n ≠ 0)
      refine WP.mono (stepAt_ok hdg (by omega_arith) ht) fun u ⟨uz, hu⟩ => ?_
      by_cases hm : m = 0
      · subst hm
        exact Or.inl ⟨by simp only [eval, uz, decide_true, Option.map_some, Bool.not_true], hu⟩
      · exact Or.inr ⟨by simp only [eval, uz, decide_eq_false hm, Option.map_some, Bool.not_false],
          m, by omega_arith, hu, by omega_arith, by omega_arith⟩
    · exact ⟨hc, by omega_arith, hp⟩
  · have hp0 : p = 0 := by simpa using hz
    subst hp0
    exact WP.block_nil hc

end VG.Proof.Ed25519.X86_64

end

end

/-! ### `Ed25519.X86_64.RecodeAll`, which only this module used -/

section

/-!
# Both scalars' digits on x86-64

`recodeAll` zeroes the digits' array (bytes 2048–3103), copies `k` (64 bytes, from the pointer at
byte 7952) to byte 3104 and `S` (32 bytes, from the pointer at byte 7944, plus 32) to byte 3176,
each followed by eight zero bytes, recodes them (`recode_ok`), `k`'s `c` bytes with windows of
five bits into the even bytes of the array and `S`'s with windows of eight bits into the odd ones,
and sets the counter to `8c + 9` (`recodeAll_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519.Recode
open VG.Proof.X25519.X86_64 (off ofs Keeps)
open VG.Impl.X25519.X86_64 (sc at_)

/-! ## Stores into the scratch -/

theorem writeW_byte {m : Mem} {a x : Addr} (v : BitVec 64) :
    m.writeW a v x = if (x - a).toNat < 8 then v.extractLsb' (8 * (x - a).toNat) 8 else m x := by
  simp only [Mem.writeW, Mem.write]
  rfl

/-- Byte `t < 8` of a word read from `b` and written at `a`. -/
theorem writeW_readW_byte (m m' : Mem) (a b : Addr) {t : Nat} (ht : t < 8) :
    m.writeW a (m'.readW b 64) (a + BitVec.ofNat 64 t) = m' (b + BitVec.ofNat 64 t) := by
  rw [writeW_byte, Mem.sub_ofNat_toNat a (by omega_arith), ite_eq_left ht]
  simp only [Mem.readW]
  exact Mem.extractLsb'_read m' b ht

/-- The bytes of the scratch from `d` to `d + n` hold `f`, the rest is as in `m`. -/
def Holds (base : Addr) (d n : Nat) (f : Nat → Byte) (m m' : Mem) : Prop :=
  (∀ j < n, m' (off base (d + j)) = f j) ∧
    ∀ x, (ofs base x < d ∨ d + n ≤ ofs base x) → m' x = m x

theorem storeSc_ok {s : State} {base : Addr} (hs : Scratch s base) (d : Nat) (hd : d + 8 ≤ 8192)
    (r : Reg) :
    WP isa (.block [.store (sc d) r]) s fun t =>
      t.mem = s.mem.writeW (off base d) (s.gpr r) ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain hw : InRegions s.wr (off base d) 8 := ⟨_, hs.wr, Offset.contains_base _ hd (by omega_arith)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64,
    VG.Proof.X25519.X86_64.ea_sc, hs.rdi, hw, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial⟩

/-- A word of `0`s stored at `d`. -/
theorem zeroWord {m : Mem} {base : Addr} {d : Nat}
    (hd : d + 8 ≤ 8192) (x : Addr) :
    m.writeW (off base d) (0 : BitVec 64) x =
      if d ≤ ofs base x ∧ ofs base x < d + 8 then 0 else m x := by
  obtain e := Offset.lt_iff x base (d := d) (n := 8) (by omega_arith)
  rw [writeW_byte]
  by_cases h : (x - off base d).toNat < 8
  · rw [ite_eq_left h, ite_eq_left (e.mp h)]; simp
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (e.mpr h'))]

theorem zeroPrefix_ok {s : State} {base : Addr} (hs : Scratch s base) (hz : s.gpr .rax = 0)
    (n : Nat) (hn : n ≤ 132) :
    WP isa (.block ((List.range n).map fun j => .store (sc (2048 + 8 * j)) .rax)) s fun t =>
      Holds base 2048 (8 * n) (fun _ => 0) s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧
        t.wr = s.wr := by
  induction n with
  | zero => exact WP.block_nil ⟨⟨fun j hj => by omega_arith, fun _ _ => rfl⟩, rfl, rfl, rfl⟩
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, WP.block_append_iff]
    refine WP.mono (ih (by omega_arith)) fun a ⟨⟨ah, ao⟩, ag, ar, aw⟩ => ?_
    obtain ha : Scratch a base := ⟨by rw [ag]; exact hs.rdi, aw ▸ hs.wr, hs.nowrap⟩
    refine WP.mono (storeSc_ok ha (2048 + 8 * n) (by omega_arith) .rax) fun t ⟨tm, tg, tr, tw⟩ => ?_
    have hb := hs.nowrap
    refine ⟨⟨fun j hj => ?_, fun x hx => ?_⟩, tg.trans ag, tr.trans ar, tw.trans aw⟩
    · rw [tm, ag, hz, zeroWord (by omega_arith), VG.Proof.X25519.X86_64.ofs_off' base (by omega_arith)]
      split
      · rfl
      · exact ah j (by omega_arith)
    · rw [tm, ag, hz, zeroWord (by omega_arith), ite_eq_right (by omega_arith), ao x (by omega_arith)]

/-- The digits' array zeroed. -/
theorem zeroDigits_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (.block zeroDigits) s fun t =>
      Holds base 2048 1056 (fun _ => 0) s.mem t.mem ∧ (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧
        t.gpr .rax = 0 ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  rw [zeroDigits, WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.mov32 .rax (.imm 0)]) s fun t =>
      t.gpr .rax = 0 ∧ Keeps [.rax] s t by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
      RegUpd.gpr_setReg, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨rfl, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]) fun a ⟨az, ka⟩ => ?_
  refine WP.mono (zeroPrefix_ok (hs.of_keeps ka (by decide)) az 132 (Nat.le_refl _))
    fun t ⟨th, tg, tr, tw⟩ => ?_
  refine ⟨⟨th.1, fun x hx => by rw [th.2 x hx, ka.2.1]⟩, fun r hr => by rw [tg, ka.1 r (by simpa using hr)],
    by rw [tg, az], tr.trans ka.2.2.1, tw.trans ka.2.2.2⟩

/-! ## The scalars' copies -/

theorem copyPair_ok {s : State} {base P : Addr} (hs : Scratch s base) (hP : s.gpr .rsi = P) (o d : Nat)
    (hd : d + 8 ≤ 8192) (hr : InRegions (s.rd ++ s.wr) (off P o) 8) :
    WP isa (.block [.mov .rax (.mem (at_ .rsi o)), .store (sc d) .rax]) s fun t =>
      t.mem = s.mem.writeW (off base d) (s.mem.readW (off P o) 64) ∧
        (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain hw : InRegions s.wr (off base d) 8 := ⟨_, hs.wr, Offset.contains_base _ hd (by omega_arith)⟩
  obtain hea : s.ea (at_ .rsi o) = off P o := by
    simp only [State.ea, at_, hP, BitVec.ofInt_natCast]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, State.store64, hea,
    VG.Proof.X25519.X86_64.ea_sc, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, hs.rdi, hr, hw, reduceCtorEq, ite_true, ite_false, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, trivial, trivial⟩
  simp only [hr, ite_false]

theorem copyPrefix_ok {s : State} {base P : Addr} (hs : Scratch s base) (hP : s.gpr .rsi = P)
    (o d : Nat) (n : Nat) (hd : d + 8 * n ≤ 8192)
    (hr : ∀ j < n, InRegions (s.rd ++ s.wr) (off P (o + 8 * j)) 8)
    (hf : ∀ j < 8 * n, 8192 ≤ ofs base (off P (o + j))) :
    WP isa (.block ((List.range n).flatMap fun j =>
      [.mov .rax (.mem (at_ .rsi (o + 8 * j))), .store (sc (d + 8 * j)) .rax])) s fun t =>
      Holds base d (8 * n) (fun j => s.mem (off P (o + j))) s.mem t.mem ∧
        (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  induction n with
  | zero => exact WP.block_nil ⟨⟨fun j hj => by omega_arith, fun _ _ => rfl⟩, fun _ _ => rfl, rfl, rfl⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      WP.block_append_iff]
    refine WP.mono (ih (by omega_arith) (fun j hj => hr j (by omega_arith)) (fun j hj => hf j (by omega_arith)))
      fun a ⟨⟨ah, ao⟩, ag, ar, aw⟩ => ?_
    obtain ha : Scratch a base := ⟨by rw [ag _ (by decide)]; exact hs.rdi, aw ▸ hs.wr, hs.nowrap⟩
    obtain hsrc : ∀ t < 8, a.mem (off P (o + 8 * n) + BitVec.ofNat 64 t) = s.mem (off P (o + (8 * n + t))) := by
      intro t ht
      obtain h1 := hf (8 * n + t) (by omega_arith)
      rw [Offset.add_add, show o + 8 * n + t = o + (8 * n + t) by omega_arith]
      exact ao _ (Or.inr (by simp only [off] at h1 ⊢; omega_arith))
    refine WP.mono (copyPair_ok ha (P := P) (by rw [ag _ (by decide)]; exact hP) (o + 8 * n) (d + 8 * n) (by omega_arith)
      (by rw [ar, aw]; exact hr n (by omega_arith))) fun t ⟨tm, tg, tr, tw⟩ => ?_
    have hb := hs.nowrap
    refine ⟨⟨fun j hj => ?_, fun x hx => ?_⟩, fun r hr' => (tg r hr').trans (ag r hr'), tr.trans ar, tw.trans aw⟩
    · rw [tm]
      by_cases hjn : j < 8 * n
      · rw [writeW_byte, ite_eq_right ?_, ah j hjn]
        rw [Offset.lt_iff _ base (by omega_arith), Mem.sub_ofNat_toNat base (by omega_arith)]
        omega_arith
      · have e : off base (d + j) = off base (d + 8 * n) + BitVec.ofNat 64 (j - 8 * n) := by
          rw [Offset.add_add, show d + 8 * n + (j - 8 * n) = d + j by omega_arith]
        rw [e, writeW_readW_byte _ _ _ _ (by omega_arith), hsrc _ (by omega_arith)]
        congr 2; omega_arith
    · rw [tm, writeW_byte, ite_eq_right ?_, ao x (by omega_arith)]
      rw [Offset.lt_iff x base (by omega_arith)]
      simp only [ofs] at hx
      omega_arith

theorem leNum_leBytes_mod (n x : Nat) :
    Proof.X25519.leNum (Proof.X25519.leBytes n x) = x % 256 ^ n := by
  induction n generalizing x with
  | zero => simp [Proof.X25519.leBytes, Proof.X25519.leNum]; omega_arith
  | succ n ih =>
    rw [Proof.X25519.leBytes_succ, Proof.X25519.leNum, ih, BitVec.toNat_ofNat,
      show 256 ^ (n + 1) = 256 * 256 ^ n by rw [Nat.pow_succ, Nat.mul_comm], Nat.mod_mul]

/-- Bytes of `X` from `src` make it `Copied`. -/
theorem copied_of_bytes {m : Mem} {base : Addr} {src N X : Nat}
    (h : ∀ j < N, m (off base (src + j)) = BitVec.ofNat 8 (X / 256 ^ j)) {nb : Nat} (hnb : nb + 8 ≤ N) :
    Copied m base src nb X := by
  intro b hb
  rw [← Proof.X25519.leNum_bytesAt_64]
  obtain e : Spec.X25519.bytesAt m (off base (src + b)) 8 = Proof.X25519.leBytes 8 (X / 256 ^ b) := by
    simp only [Spec.X25519.bytesAt, Proof.X25519.leBytes]
    apply List.map_congr_left
    intro i hi
    obtain hi8 := List.mem_range.mp hi
    rw [Offset.add_add, show src + b + i = src + (b + i) by omega_arith, h (b + i) (by omega_arith),
      Nat.div_div_eq_div_mul, ← Nat.pow_add]
  rw [e, leNum_leBytes_mod, show 256 ^ b = 2 ^ (8 * b) by rw [Nat.pow_mul],
    show (256 : Nat) ^ 8 = 2 ^ 64 from rfl]

/-- `X`'s bytes from `p`, as numbers. -/
theorem input_ofNat (m : Mem) (p : Addr) {n j : Nat} (hj : j < n) :
    m (off p j) = BitVec.ofNat 8 (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p n) / 256 ^ j) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, show 2 ^ 8 = 256 from rfl, decodeLE_byte, input_byte m p n j hj]

theorem past_ofNat (m : Mem) (p : Addr) {n j : Nat} (hj : n ≤ j) :
    (0 : Byte) = BitVec.ofNat 8 (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p n) / 256 ^ j) := by
  obtain hl := decodeLE_lt (Spec.Ed25519.bytesAt m p n)
  obtain hlen : (Spec.Ed25519.bytesAt m p n).length = n := by simp [Spec.Ed25519.bytesAt]
  rw [hlen] at hl
  rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hl (Nat.pow_le_pow_right (by decide) hj))]
  rfl

theorem loadSc_ok {s : State} {base : Addr} (hs : Scratch s base) (r : Reg) (d : Nat)
    (hd : d + 8 ≤ 8192) :
    WP isa (.block [.mov r (.mem (sc d))]) s fun t =>
      t.gpr r = s.mem.readW (off base d) 64 ∧ Keeps [r] s t := by
  obtain hr : InRegions (s.rd ++ s.wr) (off base d) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ hd (by omega_arith)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    VG.Proof.X25519.X86_64.ea_sc, hs.rdi, hr, ite_true, Option.map_some, Option.some.injEq,
    exists_eq_left', RegUpd.gpr_setReg_self]
  refine ⟨trivial, fun k hk => ?_, rfl, rfl, rfl⟩
  exact RegUpd.gpr_setReg_of_ne _ _ (by simpa only [List.mem_singleton] using hk)

/-- `k`'s and `S`'s bytes copied, each followed by eight zero bytes. -/
theorem copyScalars_ok {s : State} {base kp sp : Addr} (hs : Scratch s base)
    (hkp : s.mem.readW (off base 7952) 64 = kp) (hsp : s.mem.readW (off base 7944) 64 = sp)
    (hkr : ∀ j < 8, InRegions (s.rd ++ s.wr) (off kp (8 * j)) 8)
    (hsr : ∀ j < 4, InRegions (s.rd ++ s.wr) (off sp (32 + 8 * j)) 8)
    (hkf : ∀ j < 64, 8192 ≤ ofs base (off kp j))
    (hsf : ∀ j < 32, 8192 ≤ ofs base (off sp (32 + j))) :
    WP isa (.block copyScalars) s fun t =>
      (∀ j < 72, t.mem (off base (3104 + j)) =
        BitVec.ofNat 8 (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) / 256 ^ j)) ∧
      (∀ j < 40, t.mem (off base (3176 + j)) =
        BitVec.ofNat 8 (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sp 32) 32) / 256 ^ j)) ∧
      (∀ x, (ofs base x < 3104 ∨ 3216 ≤ ofs base x) → t.mem x = s.mem x) ∧
      (∀ r, r ≠ .rax → r ≠ .rsi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hb := hs.nowrap
  rw [show copyScalars = [.mov .rsi (.mem (sc 7952))] ++ (((List.range 8).flatMap fun j =>
      [.mov .rax (.mem (at_ .rsi (0 + 8 * j))), .store (sc (3104 + 8 * j)) .rax]) ++
      ([.mov .rsi (.mem (sc 7944))] ++ (((List.range 4).flatMap fun j =>
      [.mov .rax (.mem (at_ .rsi (32 + 8 * j))), .store (sc (3176 + 8 * j)) .rax]) ++
      ([.mov32 .rax (.imm 0)] ++ ([.store (sc 3168) .rax] ++ [.store (sc 3208) .rax]))))) by
    simp only [copyScalars, Nat.zero_add, List.append_assoc, List.cons_append, List.nil_append]]
  rw [WP.block_append_iff]
  refine WP.mono (loadSc_ok hs .rsi 7952 (by decide)) fun a ⟨ap, ka⟩ => ?_
  obtain ha := hs.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copyPrefix_ok ha (P := kp) (by rw [ap, hkp]) 0 3104 8 (by decide)
    (fun j hj => by rw [ka.2.2.1, ka.2.2.2]; simpa using hkr j hj)
    (fun j hj => by simpa using hkf j hj)) fun b ⟨⟨bh, bo⟩, bg, br, bw⟩ => ?_
  obtain hsb : Scratch b base := ⟨by rw [bg _ (by decide), ka.1 _ (by decide)]; exact hs.rdi, bw ▸ ha.wr, hb⟩
  rw [WP.block_append_iff]
  refine WP.mono (loadSc_ok hsb .rsi 7944 (by decide)) fun c ⟨cp, kc⟩ => ?_
  obtain hc := hsb.of_keeps kc (by decide)
  obtain csp : c.gpr .rsi = sp := by
    rw [cp, ← hsp, ← ka.2.1]
    exact Mem.readW_congr fun i hi => bo _ (Or.inr (by
      rw [VG.Proof.X25519.X86_64.ofs_off base (by omega_arith)]; omega_arith))
  obtain hfar : ∀ j < 32, b.mem (off sp (32 + j)) = s.mem (off sp (32 + j)) := fun j hj =>
    (bo _ (Or.inr (by have := hsf j hj; omega_arith))).trans (by rw [ka.2.1])
  rw [WP.block_append_iff]
  refine WP.mono (copyPrefix_ok hc (P := sp) csp 32 3176 4 (by decide)
    (fun j hj => by rw [kc.2.2.1, kc.2.2.2, br, bw, ka.2.2.1, ka.2.2.2]; exact hsr j hj)
    (fun j hj => hsf j hj)) fun d ⟨⟨dh, d_o⟩, dg, dr, dw⟩ => ?_
  obtain hsd : Scratch d base :=
    ⟨by rw [dg _ (by decide), kc.1 _ (by decide), bg _ (by decide), ka.1 _ (by decide)]; exact hs.rdi,
      dw ▸ hc.wr, hb⟩
  rw [WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.mov32 .rax (.imm 0)]) d fun t =>
      t.gpr .rax = 0 ∧ Keeps [.rax] d t by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
      RegUpd.gpr_setReg, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨rfl, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]) fun e ⟨ez, ke⟩ => ?_
  obtain he := hsd.of_keeps ke (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (storeSc_ok he 3168 (by decide) .rax) fun f ⟨fm, fg, fr, fw⟩ => ?_
  obtain hf : Scratch f base := ⟨by rw [fg]; exact he.rdi, fw ▸ he.wr, hb⟩
  refine WP.mono (storeSc_ok hf 3208 (by decide) .rax) fun t ⟨tm, tg, tr, tw⟩ => ?_
  -- What each piece of memory holds.
  obtain z1 := zeroWord (m := e.mem) (base := base) (d := 3168) (by decide)
  obtain z2 := zeroWord (m := f.mem) (base := base) (d := 3208) (by decide)
  rw [ez] at fm
  rw [fg, ez] at tm
  obtain hmem : ∀ x, t.mem x = if 3208 ≤ ofs base x ∧ ofs base x < 3216 then 0 else
      if 3168 ≤ ofs base x ∧ ofs base x < 3176 then 0 else d.mem x := by
    intro x; rw [tm, z2, fm, z1, ke.2.1]
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun x hx => ?_, fun r hr hs' => ?_, ?_, ?_⟩
  · rw [hmem, VG.Proof.X25519.X86_64.ofs_off' base (by omega_arith)]
    by_cases h64 : j < 64
    · rw [ite_eq_right (by omega_arith), ite_eq_right (by omega_arith),
        d_o _ (Or.inl (by rw [VG.Proof.X25519.X86_64.ofs_off' base (by omega_arith)]; omega_arith)), kc.2.1,
        bh j (by omega_arith)]
      simp only [Nat.zero_add, ka.2.1]
      exact input_ofNat s.mem kp h64
    · rw [ite_eq_right (by omega_arith), ite_eq_left (by omega_arith), past_ofNat s.mem kp (n := 64) (j := j) (by omega_arith)]
  · rw [hmem, VG.Proof.X25519.X86_64.ofs_off' base (by omega_arith)]
    by_cases h32 : j < 32
    · rw [ite_eq_right (by omega_arith), ite_eq_right (by omega_arith), dh j (by omega_arith)]
      simp only [kc.2.1]
      rw [hfar j h32, show off sp (32 + j) = off (off sp 32) j from (Offset.add_add _ _ _).symm]
      exact input_ofNat s.mem (off sp 32) h32
    · rw [ite_eq_left (by omega_arith), past_ofNat s.mem (off sp 32) (n := 32) (j := j) (by omega_arith)]
  · rw [hmem, ite_eq_right (by omega_arith), ite_eq_right (by omega_arith), d_o x (by omega_arith), kc.2.1,
      bo x (by omega_arith), ka.2.1]
  · rw [tg, fg, ke.1 r (by simpa using hr), dg r hr, kc.1 r (by simpa using hs'), bg r hr,
      ka.1 r (by simpa using hs')]
  · rw [tr, fr, ke.2.2.1, dr, kc.2.2.1, br, ka.2.2.1]
  · rw [tw, fw, ke.2.2.2, dw, kc.2.2.2, bw, ka.2.2.2]

/-! ## The bounds and the counter -/

theorem boundS_spec (s₀ : State) (base : Addr) (dst : Nat) : BoundSpec s₀ base dst 32 boundS := by
  intro t _ i hi hi1
  obtain hcf : (BitVec.ofNat 64 i).toNat < ((256 : BitVec 32).signExtend 64).toNat ↔ i < 8 * 32 := by
    rw [show (256 : BitVec 32).signExtend 64 = BitVec.ofNat 64 256 from rfl, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  apply WP.of_runBlock
  simp only [boundS, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.cf_arithFlags, hi, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun _ _ => rfl, rfl, rfl, rfl⟩
  rw [decide_eq_decide.mpr hcf]

theorem boundK_spec {s₀ : State} {base : Addr} (hs : Scratch s₀ base) {c : Nat} (hc64 : c ≤ 64)
    (hc : s₀.mem.readW (off base 56) 64 = BitVec.ofNat 64 c) (dst : Nat) :
    BoundSpec s₀ base dst c boundK := by
  intro t kt i hi hi1
  obtain ht := kt.scratch hs
  obtain tc : t.mem.readW (off base 56) 64 = BitVec.ofNat 64 c := by
    rw [← hc]
    exact Mem.readW_congr fun j hj => kt.mem _ (Or.inl (by
      rw [VG.Proof.X25519.X86_64.ofs_off base (by omega_arith)]; omega_arith))
  obtain hr : InRegions (t.rd ++ t.wr) (off base 56) 8 :=
    ⟨_, List.mem_append_right _ ht.wr, Offset.contains_base _ (by decide) (by omega_arith)⟩
  obtain hshl : BitVec.ofNat 64 c <<< 3 = BitVec.ofNat 64 (8 * c) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega_arith
  obtain hcf : (BitVec.ofNat 64 i).toNat < (BitVec.ofNat 64 (8 * c)).toNat ↔ i < 8 * c := by
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  apply WP.of_runBlock
  simp only [boundK, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, execShift,
    State.load64, VG.Proof.X25519.X86_64.ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
    RegUpd.cf_arithFlags, ht.rdi, hr, tc, hshl, hi, show 1 ≤ 3 ∧ 3 ≤ 63 by decide, and_self,
    reduceCtorEq, ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨by rw [decide_eq_decide.mpr hcf], fun r hr => ?_, ?_, ?_, ?_⟩
  · have hr' : r ≠ .rax := by simpa using hr
    simp only [RegUpd.gpr_arithFlags, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr', ite_false]
  all_goals simp only [RegUpd.mem_arithFlags, RegUpd.mem_setReg, RegUpd.mem_setFlags,
    RegUpd.rd_arithFlags, RegUpd.rd_setReg, RegUpd.rd_setFlags, RegUpd.wr_arithFlags,
    RegUpd.wr_setReg, RegUpd.wr_setFlags]

theorem setTop_ok {s : State} {base : Addr} (hs : Scratch s base) {c : Nat}
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 c) :
    WP isa (.block setTop) s fun t =>
      t.mem.readW (off base 56) 64 = BitVec.ofNat 64 (8 * c + 9) ∧
      (∀ x, (ofs base x < 56 ∨ 64 ≤ ofs base x) → t.mem x = s.mem x) ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain hr : InRegions (s.rd ++ s.wr) (off base 56) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by decide) (by omega_arith)⟩
  obtain hw : InRegions s.wr (off base 56) 8 := ⟨_, hs.wr, Offset.contains_base _ (by decide) (by omega_arith)⟩
  obtain hshl : BitVec.ofNat 64 c <<< 3 = BitVec.ofNat 64 (8 * c) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega_arith
  obtain hadd : BitVec.ofNat 64 (8 * c) + (9 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (8 * c + 9) := by
    rw [show (9 : BitVec 32).signExtend 64 = BitVec.ofNat 64 9 from rfl, BitVec.ofNat_add]
  apply WP.of_runBlock
  simp only [setTop, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, execShift,
    State.load64, State.store64, VG.Proof.X25519.X86_64.ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
    RegUpd.gpr_arithFlags, RegUpd.mem_setReg, RegUpd.mem_setFlags, RegUpd.mem_arithFlags,
    RegUpd.wr_setReg, RegUpd.wr_setFlags, RegUpd.wr_arithFlags, RegUpd.rd_setReg, RegUpd.rd_setFlags,
    RegUpd.rd_arithFlags, hs.rdi, hr, hw, hc, hshl, hadd, show 1 ≤ 3 ∧ 3 ≤ 63 by decide, and_self,
    reduceCtorEq, ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨Mem.readW_writeW_self64 _ _ _, fun x hx => ?_, fun r hr => ?_, trivial⟩
  · exact VG.Proof.X25519.X86_64.writeW_outside s.mem base _ (by decide) x (by omega_arith)
  · simp only [hr, ite_false]

/-! ## Both scalars -/

/-- What `recodeAll` may change: its registers, the counter and bytes 2048–3215. -/
structure AllKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ recRegs → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : ∀ x, (ofs base x < 56 ∨ (64 ≤ ofs base x ∧ ofs base x < 2048) ∨ 3216 ≤ ofs base x) →
    t.mem x = s.mem x

/-- The digits' array zeroed and the scalars copied. -/
structure Copies (base : Addr) (c K S : Nat) (b : State) : Prop where
  scratch : Scratch b base
  counter : b.mem.readW (off base 56) 64 = BitVec.ofNat 64 c
  cK : Copied b.mem base 3104 c K
  cS : Copied b.mem base 3176 32 S
  zero : ∀ dst < 2, ∀ j < 528, dig b.mem base dst j = 0

theorem recodeCopy_ok {s : State} {base kp sp : Addr} (hs : Scratch s base) {c : Nat}
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 c) (hc64 : c ≤ 64)
    (hkp : s.mem.readW (off base 7952) 64 = kp) (hsp : s.mem.readW (off base 7944) 64 = sp)
    (hkr : ∀ j < 8, InRegions (s.rd ++ s.wr) (off kp (8 * j)) 8)
    (hsr : ∀ j < 4, InRegions (s.rd ++ s.wr) (off sp (32 + 8 * j)) 8)
    (hkf : ∀ j < 64, 8192 ≤ ofs base (off kp j))
    (hsf : ∀ j < 32, 8192 ≤ ofs base (off sp (32 + j))) :
    WP isa (.block (zeroDigits ++ copyScalars)) s fun b =>
      Copies base c (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64))
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sp 32) 32)) b ∧
      (∀ x, (ofs base x < 2048 ∨ 3216 ≤ ofs base x) → b.mem x = s.mem x) ∧
      (∀ r, r ≠ .rax → r ≠ .rsi → b.gpr r = s.gpr r) ∧ b.rd = s.rd ∧ b.wr = s.wr := by
  have hb := hs.nowrap
  rw [WP.block_append_iff]
  refine WP.mono (zeroDigits_ok hs) fun a ⟨⟨ah, ao⟩, ag, _, ar, aw⟩ => ?_
  obtain ha : Scratch a base := ⟨by rw [ag _ (by decide)]; exact hs.rdi, aw ▸ hs.wr, hb⟩
  have aread (d : Nat) (hd : d + 8 ≤ 2048) : a.mem.readW (off base d) 64 = s.mem.readW (off base d) 64 :=
    Mem.readW_congr fun i hi => ao _ (Or.inl (by
      rw [VG.Proof.X25519.X86_64.ofs_off base (by omega_arith)]; omega_arith))
  have aread' (d : Nat) (hd : 3104 ≤ d) (hd' : d + 8 ≤ 8192) :
      a.mem.readW (off base d) 64 = s.mem.readW (off base d) 64 :=
    Mem.readW_congr fun i hi => ao _ (Or.inr (by
      rw [VG.Proof.X25519.X86_64.ofs_off base (by omega_arith)]; omega_arith))
  have afar (x : Addr) (hx : 8192 ≤ ofs base x) : a.mem x = s.mem x := ao x (Or.inr (by omega_arith))
  refine WP.mono (copyScalars_ok ha (by rw [aread' 7952 (by decide) (by decide)]; exact hkp)
    (by rw [aread' 7944 (by decide) (by decide)]; exact hsp)
    (fun j hj => by rw [ar, aw]; exact hkr j hj) (fun j hj => by rw [ar, aw]; exact hsr j hj)
    hkf hsf) fun b ⟨bK, bS, bo, bg, br, bw⟩ => ?_
  -- The scalars, from `a`'s bytes, are `s`'s.
  obtain eK : Spec.Ed25519.bytesAt a.mem kp 64 = Spec.Ed25519.bytesAt s.mem kp 64 := by
    simp only [Spec.Ed25519.bytesAt]
    exact List.map_congr_left fun j hj => afar _ (hkf j (List.mem_range.mp hj))
  obtain eS : Spec.Ed25519.bytesAt a.mem (off sp 32) 32 = Spec.Ed25519.bytesAt s.mem (off sp 32) 32 := by
    simp only [Spec.Ed25519.bytesAt]
    exact List.map_congr_left fun j hj => afar _ (by
      rw [Offset.add_add]; exact hsf j (List.mem_range.mp hj))
  rw [eK] at bK
  rw [eS] at bS
  obtain hsb : Scratch b base :=
    ⟨by rw [bg _ (by decide) (by decide), ag _ (by decide)]; exact hs.rdi, bw ▸ ha.wr, hb⟩
  obtain bc : b.mem.readW (off base 56) 64 = BitVec.ofNat 64 c := by
    rw [← hc, ← aread 56 (by decide)]
    exact Mem.readW_congr fun i hi => bo _ (Or.inl (by
      rw [VG.Proof.X25519.X86_64.ofs_off base (by omega_arith)]; omega_arith))
  obtain bz : ∀ dst < 2, ∀ j < 528, dig b.mem base dst j = 0 := by
    intro dst hd j hj
    simp only [dig]
    rw [bo _ (Or.inl (by rw [VG.Proof.X25519.X86_64.ofs_off' base (by omega_arith)]; omega_arith)),
      show 2048 + 2 * j + dst = 2048 + (2 * j + dst) by omega_arith, ah _ (by omega_arith)]
    rfl
  refine ⟨⟨hsb, bc, copied_of_bytes bK (by omega_arith), copied_of_bytes bS (by decide), bz⟩,
    fun x hx => by rw [bo x (by omega_arith), ao x (by omega_arith)], fun r hr hs' => by rw [bg r hr hs', ag r hr],
    by rw [br, ar], by rw [bw, aw]⟩

theorem recodeAll_ok {s : State} {base kp sp : Addr} (hs : Scratch s base) {c : Nat}
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 c) (hc32 : 32 ≤ c) (hc64 : c ≤ 64)
    (hkp : s.mem.readW (off base 7952) 64 = kp) (hsp : s.mem.readW (off base 7944) 64 = sp)
    (hkr : ∀ j < 8, InRegions (s.rd ++ s.wr) (off kp (8 * j)) 8)
    (hsr : ∀ j < 4, InRegions (s.rd ++ s.wr) (off sp (32 + 8 * j)) 8)
    (hkf : ∀ j < 64, 8192 ≤ ofs base (off kp j))
    (hsf : ∀ j < 32, 8192 ≤ ofs base (off sp (32 + j))) :
    WP isa recodeAll s fun t =>
      (∀ j < 528, dig t.mem base 0 j =
        digits 5 (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64)) (8 * c) j) ∧
      (∀ j < 528, dig t.mem base 1 j =
        digits 8 (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sp 32) 32)) (8 * 32) j) ∧
      t.mem.readW (off base 56) 64 = BitVec.ofNat 64 (8 * c + 9) ∧ AllKeep base s t := by
  rw [recodeAll]
  refine WP.seq (WP.mono (recodeCopy_ok hs hc hc64 hkp hsp hkr hsr hkf hsf)
    fun b ⟨⟨hsb, bc, cK, cS, bz⟩, bo, bg, br, bw⟩ => ?_)
  generalize Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) = K at cK ⊢
  generalize Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sp 32) 32) = S at cS ⊢
  -- `k`'s digits.
  refine WP.seq (WP.mono (recode_ok hsb (by decide) (by decide) (by decide) (by omega_arith) cK (by omega_arith)
    (boundK_spec hsb hc64 bc 0) (bz 0 (by decide))) fun d ⟨dK, kd⟩ => ?_)
  obtain hsd := kd.scratch hsb
  obtain cS' : Copied d.mem base 3176 32 S := cS.of_keep (by decide) (by decide) fun x hx => kd.mem x (by omega_arith)
  refine WP.seq (WP.mono (recode_ok hsd (by decide) (by decide) (by decide) (by decide) cS' (by decide)
    (boundS_spec d base 1) (fun j hj => by
      simp only [dig]
      rw [kd.mem _ (Or.inr (Or.inr (by
        rw [VG.Proof.X25519.X86_64.ofs_off' base (by omega_arith)]; omega_arith)))]
      exact bz 1 (by decide) j hj)) fun e ⟨eS', ke⟩ => ?_)
  obtain hse := ke.scratch hsd
  obtain ec : e.mem.readW (off base 56) 64 = BitVec.ofNat 64 c := by
    rw [← bc]
    exact Mem.readW_congr fun i hi => (ke.mem _ (Or.inl (by
      rw [VG.Proof.X25519.X86_64.ofs_off base (by omega_arith)]; omega_arith))).trans (kd.mem _ (Or.inl (by
      rw [VG.Proof.X25519.X86_64.ofs_off base (by omega_arith)]; omega_arith)))
  refine WP.mono (setTop_ok hse ec) fun t ⟨tc, tm, tg, tr, tw⟩ => ?_
  refine ⟨fun j hj => ?_, fun j hj => ?_, tc, ⟨fun r hr => ?_, ?_, ?_, fun x hx => ?_⟩⟩
  · simp only [dig]
    rw [tm _ (Or.inr (by rw [VG.Proof.X25519.X86_64.ofs_off' base (by omega_arith)]; omega_arith)),
      ke.mem _ (Or.inr (Or.inr (by rw [VG.Proof.X25519.X86_64.ofs_off' base (by omega_arith)]; omega_arith)))]
    exact dK j hj
  · simp only [dig]
    rw [tm _ (Or.inr (by rw [VG.Proof.X25519.X86_64.ofs_off' base (by omega_arith)]; omega_arith))]
    exact eS' j hj
  · rw [tg r (fun e => hr (by rw [e]; decide)), ke.gpr r hr, kd.gpr r hr,
      bg r (fun e => hr (by rw [e]; decide)) (fun e => hr (by rw [e]; decide))]
  · rw [tr, ke.rd, kd.rd, br]
  · rw [tw, ke.wr, kd.wr, bw]
  · rw [tm x (by omega_arith), ke.mem x (by omega_arith), kd.mem x (by omega_arith), bo x (by omega_arith)]

end VG.Proof.Ed25519.X86_64

end

end


/-!
# Verification's equation, from the windows

`k`'s zero bytes above its low 32 are skipped (`skipZero`, `SkipLoop`), both scalars recoded
(`recodeAll`), and the windows (`EdWindows`) leave a representative of `[k]A - [S]B`, compared
with `-R`: they are equal exactly when `[S]B = R + [k]A`, which, as `A` and `R` represent points
of the group, is the specification's comparison.
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open VG.Proof.X25519.X86_64 (off ofs Keeps clob Outside)

variable {fld : Arith} [EdArith fld] {pt : Point64.Ops} [PtOk pt]

theorem ByteKeep.bytesK {base kp sp T : Addr} {A : EPoint dZ} {s t : State} (h : WinCtx base kp sp T A s)
    (k : ByteKeep base s t) : Spec.Ed25519.bytesAt t.mem kp 64 = Spec.Ed25519.bytesAt s.mem kp 64 :=
  outside_bytes k.mem (by decide) h.kFar

theorem ByteKeep.bytesS {base kp sp T : Addr} {A : EPoint dZ} {s t : State} (h : WinCtx base kp sp T A s)
    (k : ByteKeep base s t) :
    Spec.Ed25519.bytesAt t.mem (off sp 32) 32 = Spec.Ed25519.bytesAt s.mem (off sp 32) 32 :=
  outside_bytes k.mem (by decide) h.sFar

theorem counterCmp_ok {s : State} {base : Addr} (hs : Scratch s base) (i : Nat) (hi : i ≤ 64)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i) :
    WP isa (.block [.mov .rbx (.mem (Impl.X25519.X86_64.sc 56)), .alu .cmp .rbx (.imm 32)]) s
      fun t => t.zf = some (decide (i = 32)) ∧ Keeps [.rbx] s t := by
  obtain hr : InRegions (s.rd ++ s.wr) (off base 56) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by decide) (by decide)⟩
  obtain hz : (BitVec.ofNat 64 i - (32 : BitVec 32).signExtend 64 == 0) = decide (i = 32) := by
    rw [show (32 : BitVec 32).signExtend 64 = BitVec.ofNat 64 32 from rfl]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    bv_omega_using [hi]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, State.load64,
    Proof.X25519.X86_64.ea_sc, RegUpd.gpr_setReg, RegUpd.zf_arithFlags, hs.rdi, hr, hc, hz,
    ite_true, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem scalar_byte {m : Mem} {p : Addr} {n i : Nat} (hi : i < n) :
    (m (off p i)).toNat = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p n) / 256 ^ i % 256 := by
  rw [decodeLE_byte, input_byte m p n i hi]

/-- Skipping `k`'s zero bytes, with `c` bytes left. -/
structure SkipLoop (s₀ : State) (base kp sp T : Addr) (A : EPoint dZ) (K S c : Nat) (s : State) : Prop where
  ctx : WinCtx base kp sp T A s
  d : env s.mem base 16 = Spec.Ed25519.d
  counter : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 c
  kVal : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) = K
  sVal : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sp 32) 32) = S
  value : Rep (point (env s.mem base) 0 1 2 3) ((K / 256 ^ c) • A + (S / 256 ^ c) • (-baseAff))
  keep : ByteKeep base s₀ s

/-- What moving the counter may change: the counter, and the registers a byte may. -/
structure CounterKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ clob → r ≠ .rbx → r ≠ .rsi → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside base 56 8 s.mem t.mem

theorem CounterKeep.trans {base : Addr} {s t u : State} (h : CounterKeep base s t)
    (k : CounterKeep base t u) : CounterKeep base s u :=
  ⟨fun r a b c => (k.gpr r a b c).trans (h.gpr r a b c), k.rd.trans h.rd, k.wr.trans h.wr,
    h.mem.trans k.mem⟩

theorem CounterKeep.of_keeps {base : Addr} {s t : State} {rs : List Reg} (h : Keeps rs s t)
    (hrs : ∀ r ∈ rs, r = .rbx ∨ r = .rsi ∨ r ∈ clob) : CounterKeep base s t :=
  ⟨fun r hc hb hs => h.1 r fun hm => by
    rcases hrs r hm with rfl | rfl | hm'
    · exact hb rfl
    · exact hs rfl
    · exact hc hm', h.2.2.1, h.2.2.2, fun x _ => by rw [h.2.1]⟩

theorem CounterKeep.byte {base : Addr} {s t : State} (h : CounterKeep base s t) : ByteKeep base s t :=
  ⟨h.gpr, h.rd, h.wr, h.mem.mono (by decide) (by decide)⟩

/-- The loops' invariant, with the counter moved from `c` to `c'` where the scalars'
quotients agree. -/
theorem SkipLoop.of_counter {s₀ s t : State} {base kp sp T : Addr} {A : EPoint dZ} {K S c c' : Nat}
    (h : SkipLoop s₀ base kp sp T A K S c s) (k : CounterKeep base s t)
    (hc : t.mem.readW (off base 56) 64 = BitVec.ofNat 64 c')
    (hK : K / 256 ^ c' = K / 256 ^ c) (hS : S / 256 ^ c' = S / 256 ^ c) :
    SkipLoop s₀ base kp sp T A K S c' t :=
  ⟨h.ctx.of_byte k.byte, by rw [header_env k.mem]; exact h.d, hc,
    by rw [k.byte.bytesK h.ctx, h.kVal], by rw [k.byte.bytesS h.ctx, h.sVal],
    by rw [header_env k.mem, hK, hS]; exact h.value, h.keep.trans k.byte⟩

/-! ## Skipping the leading zero bytes of `k` -/

theorem skipStop_ok {s : State} {base : Addr} (hs : Scratch s base) (j : Nat)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 j) :
    WP isa (.block skipStop) s fun t => t.zf = some true ∧
      t.mem.readW (off base 56) 64 = BitVec.ofNat 64 (j + 1) ∧ CounterKeep base s t := by
  obtain hw : InRegions s.wr (off base 56) 8 :=
    ⟨_, hs.wr, Offset.contains_base _ (by decide) (by decide)⟩
  obtain hr : InRegions (s.rd ++ s.wr) (off base 56) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by decide) (by decide)⟩
  obtain he : BitVec.ofNat 64 j + (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (j + 1) := by
    rw [show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add]
  apply WP.of_runBlock
  simp only [skipStop, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    State.load64, State.store64, Proof.X25519.X86_64.ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.zf_arithFlags, RegUpd.rd_setReg, RegUpd.rd_arithFlags, RegUpd.wr_setReg,
    RegUpd.wr_arithFlags, RegUpd.mem_setReg, RegUpd.mem_arithFlags, hs.rdi, hr, hw, hc, he,
    BitVec.sub_self, ite_true, ite_false, reduceCtorEq, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, Mem.readW_writeW_self64 _ _ _, ⟨fun r hr _ _ => ?_, rfl, rfl,
    VG.Proof.X25519.X86_64.writeW_outside _ _ _ (by decide)⟩⟩
  simp only [RegUpd.gpr_arithFlags, RegUpd.gpr_setReg, show r ≠ .rax from fun h => hr (h ▸ by decide),
    ite_false]

private theorem byte_zero : ∀ b : BitVec 8,
    (b.setWidth 64 &&& b.setWidth 64 == 0) = decide (b.toNat = 0) := by decide

theorem testByte_ok (s : State) (b : BitVec 8) (hc : s.gpr .rbx = b.setWidth 64) :
    WP isa (.block [.alu .test .rbx (.reg .rbx)]) s fun t =>
      t.zf = some (decide (b.toNat = 0)) ∧ Keeps [] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.zf_arithFlags, hc, byte_zero, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun _ _ => rfl, rfl, rfl, rfl⟩

/-- The counter moved down from `j + 1` to `j`, and byte `j` of `k` tested. -/
theorem skipLoad_ok {s : State} {base kp sp T : Addr} {A : EPoint dZ} (h : WinCtx base kp sp T A s)
    (j : Nat) (hj : j < 64) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (j + 1)) :
    WP isa (.block skipLoad) s fun t => t.zf = some (decide ((s.mem (off kp j)).toNat = 0)) ∧
      t.mem.readW (off base 56) 64 = BitVec.ofNat 64 j ∧ CounterKeep base s t := by
  rw [skipLoad, List.append_assoc, WP.block_append_iff]
  refine WP.mono (batchBegin_ok h.scratch j hc) fun a ⟨_, ac, ag, ar, aw, am⟩ => ?_
  obtain ka : CounterKeep base s a := ⟨fun r _ hb _ => ag r hb, ar, aw, am⟩
  obtain ha := h.of_byte ka.byte
  rw [WP.block_append_iff]
  refine WP.mono (digitByte_ok ha.scratch 7952 0 (by decide) (by decide) ha.kHeader j ac
    (by rw [off_zero]; exact ha.kRead j hj)) fun b ⟨bv, kb⟩ => ?_
  obtain hm : a.mem (off kp j) = s.mem (off kp j) := am _ (by have := h.kFar j hj; omega_arith)
  rw [off_zero, hm] at bv
  refine WP.mono (testByte_ok b _ bv) fun t ⟨tz, kt⟩ => ?_
  refine ⟨tz, by rw [kt.2.1, kb.2.1]; exact ac, ka.trans ((CounterKeep.of_keeps kb (by decide)).trans
    (CounterKeep.of_keeps kt (by decide)))⟩

/-- Skipping: `c = 32 + n` bytes are left, and the bytes of `k` from `c` on are zero. -/
def SkipInv (s₀ : State) (base kp sp T : Addr) (A : EPoint dZ) (K S : Nat) (n : Nat) (s : State) : Prop :=
  SkipLoop s₀ base kp sp T A K S (32 + n) s ∧ K / 256 ^ (32 + n) = 0 ∧ 0 < n ∧ n ≤ 32

/-- Whether the skipping goes on below `32 + j + 1` bytes left: byte `32 + j` of `k` is zero,
and more than 32 bytes are left after it. -/
def skipOn (K j : Nat) : Bool := decide (K / 256 ^ (32 + j) % 256 = 0 ∧ j ≠ 0)

/-- Where the skipping stops below `32 + j + 1` bytes left, if it does. -/
def skipEnd (K j : Nat) : Nat := if K / 256 ^ (32 + j) % 256 = 0 then 32 else 32 + (j + 1)

theorem skipEnd_range (K j : Nat) (hj : j < 32) : 32 ≤ skipEnd K j ∧ skipEnd K j ≤ 64 := by
  unfold skipEnd; split <;> omega_arith

theorem skipBody_ok {s₀ t : State} {base kp sp T : Addr} {A : EPoint dZ} {K S j : Nat}
    (h : SkipInv s₀ base kp sp T A K S (j + 1) t) :
    WP isa skipBody t fun u => u.zf.map (!·) = some (skipOn K j) ∧
      (skipOn K j = false → SkipLoop s₀ base kp sp T A K S (skipEnd K j) u ∧ K / 256 ^ skipEnd K j = 0) ∧
      (skipOn K j = true → SkipInv s₀ base kp sp T A K S j u) := by
  obtain ⟨hl, hz, _, hn⟩ := h
  obtain hS : S < 256 ^ 32 := hl.sVal ▸ decodeLE_lt32 _ _
  obtain hb : (t.mem (off kp (32 + j))).toNat = K / 256 ^ (32 + j) % 256 := by
    rw [scalar_byte (n := 64) (by omega_arith), hl.kVal]
  rw [skipBody]
  refine WP.seq (WP.mono (skipLoad_ok hl.ctx (32 + j) (by omega_arith) (by rw [hl.counter]; rfl))
    fun a ⟨az, ac, ka⟩ => ?_)
  rw [hb] at az
  refine WP.ite (!decide (K / 256 ^ (32 + j) % 256 = 0)) (by simp only [eval, az, Option.map_some])
    (fun hy => ?_) (fun hy => ?_)
  · have h0 : K / 256 ^ (32 + j) % 256 ≠ 0 := by simpa using hy
    obtain hoff : skipOn K j = false := by simp only [skipOn, h0, false_and, decide_false]
    refine WP.mono (skipStop_ok (ka.byte.scratch hl.ctx.scratch) (32 + j) ac) fun u ⟨uz, uc, ku⟩ => ?_
    obtain e : skipEnd K j = 32 + (j + 1) := by simp only [skipEnd, h0, ↓reduceIte]
    refine ⟨by rw [uz, hoff]; rfl, fun _ => ?_, fun ht => absurd ht (by rw [hoff]; decide)⟩
    rw [e]
    exact ⟨hl.of_counter (ka.trans ku) uc rfl rfl, hz⟩
  · have h0 : K / 256 ^ (32 + j) % 256 = 0 := by simpa using hy
    obtain hK : K / 256 ^ (32 + j) = 0 := by
      have := div_split K (32 + j)
      rw [show 32 + j + 1 = 32 + (j + 1) by omega_arith, hz] at this
      omega_arith
    obtain hw := hl.of_counter ka ac (by rw [hK, hz]) (by rw [high_zero hS (by omega_arith), high_zero hS (by omega_arith)])
    obtain he : skipOn K j = decide (j ≠ 0) := by simp only [skipOn, h0, true_and]
    rw [counterCmp]
    refine WP.mono (counterCmp_ok hw.ctx.scratch (32 + j) (by omega_arith) hw.counter) fun u ⟨uz, ku⟩ => ?_
    obtain hu := hw.of_counter (CounterKeep.of_keeps ku (by decide)) (by rw [ku.2.1]; exact hw.counter) rfl rfl
    refine ⟨by rw [uz, he]; simp, fun hf => ?_, fun ht => ⟨hu, hK, by rw [he] at ht; have := of_decide_eq_true ht; omega_arith,
      by omega_arith⟩⟩
    obtain hj : j = 0 := by rw [he] at hf; simpa using hf
    subst hj
    obtain e : skipEnd K 0 = 32 := by simp only [skipEnd, h0, ↓reduceIte]
    rw [e]
    exact ⟨hu, hK⟩

theorem skipZero_ok {s₀ s : State} {base kp sp T : Addr} {A : EPoint dZ} {K S : Nat}
    (h : SkipLoop s₀ base kp sp T A K S 64 s) :
    WP isa skipZero s fun t => ∃ c, 32 ≤ c ∧ c ≤ 64 ∧ SkipLoop s₀ base kp sp T A K S c t ∧
      K / 256 ^ c = 0 := by
  obtain hK : K / 256 ^ 64 = 0 := Nat.div_eq_of_lt (h.kVal ▸ decodeLE_lt64 _ _)
  rw [skipZero]
  apply WP.loop (SkipInv s₀ base kp sp T A K S) (n := 32)
  · intro n t ht
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := ht.2.2.1; omega_arith : n ≠ 0)
    obtain hj : j < 32 := by have := ht.2.2.2; omega_arith
    refine WP.mono (skipBody_ok ht) fun u ⟨uz, uf, ut⟩ => ?_
    cases hs : skipOn K j
    · exact Or.inl ⟨by show u.zf.map (!·) = _; rw [uz, hs], skipEnd K j, (skipEnd_range K j hj).1,
        (skipEnd_range K j hj).2, (uf hs).1, (uf hs).2⟩
    · exact Or.inr ⟨by show u.zf.map (!·) = _; rw [uz, hs], j, by omega_arith, ut hs⟩
  · exact ⟨h, hK, by decide, by decide⟩


/-! ## The windows -/

/-- A run of the windows: from a state satisfying `R₀`, after position `p`. -/
def LoopRun (R₀ : State → Prop) (base kp sp T : Addr) (A : EPoint dZ) (fA fB : Nat → Nat) (top p : Nat)
    (x : State) : Prop :=
  ∃ s₀, R₀ s₀ ∧ WinLoop s₀ base kp sp T A fA fB top p x

/-- A run of the windows at their start, one above `top`. -/
def StartRun (R₀ : State → Prop) (base kp sp T : Addr) (A : EPoint dZ) (fA fB : Nat → Nat) (top : Nat)
    (x : State) : Prop :=
  ∃ s₀, R₀ s₀ ∧ SkipAt s₀ base kp sp T A fA fB top (top + 1) x

/-- The windows after the recoding, from one above the top position (the identity accumulated)
to after position 0, as `windows` runs them (`Ifma.windows` too): the loops' invariant, and a
trace that depends on the run's start alone. -/
class EdWindows (win : Prog isa) : Prop where
  ok : ∀ {s₀ s : State} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat} {top : Nat},
    Digits fA fB top → SkipAt s₀ base kp sp T A fA fB top (top + 1) s →
      WP isa win s (WinLoop s₀ base kp sp T A fA fB top 0)
  ct : ∀ {R₀ : State → Prop} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat} {top : Nat},
    Digits fA fB top →
    RelCT isa (fun x y => StartRun R₀ base kp sp T A fA fB top x ∧ StartRun R₀ base kp sp T A fA fB top y) win
      (fun x y => LoopRun R₀ base kp sp T A fA fB top 0 x ∧ LoopRun R₀ base kp sp T A fA fB top 0 y)

variable {win : Prog isa} [EdWindows win]

theorem PowersKeep.of_byte {base : Addr} {s t : State} (h : ByteKeep base s t) :
    PowersKeep base 56 7752 s t :=
  ⟨fun r hb hs hc => h.gpr r hc hb hs, h.rd, h.wr, TableFrame.table (h.mem.mono (by decide) (by decide))⟩

theorem PowersKeep.of_all {base : Addr} {s t : State} (h : AllKeep base s t) :
    PowersKeep base 56 7752 s t := by
  refine ⟨fun r hb hs hc => h.gpr r ?_, h.rd, h.wr, fun p _ hp => h.mem p ?_⟩
  · simp only [recRegs, List.mem_cons, List.not_mem_nil, or_false]
    rintro (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp_all [clob]
  · omega_arith

theorem WinCtx.of_all {base kp sp T : Addr} {A : EPoint dZ} {s t : State} (h : WinCtx base kp sp T A s)
    (k : AllKeep base s t) : WinCtx base kp sp T A t := by
  have hb := h.scratch.nowrap
  have word (d : Nat) (hd : 3216 ≤ d) (hd' : d + 8 ≤ 8192) :
      t.mem.readW (off base d) 64 = s.mem.readW (off base d) 64 :=
    Mem.readW_congr fun i hi => k.mem _ (Or.inr (Or.inr (by
      rw [VG.Proof.X25519.X86_64.ofs_off base (by omega_arith)]; omega_arith)))
  refine ⟨⟨(k.gpr _ (by decide)).trans h.scratch.rdi, k.wr ▸ h.scratch.wr, hb⟩,
    (word 7952 (by decide) (by decide)).trans h.kHeader, (word 7944 (by decide) (by decide)).trans h.sHeader,
    fun i hi => by rw [k.rd, k.wr]; exact h.kRead i hi, fun i hi => by rw [k.rd, k.wr]; exact h.sRead i hi,
    h.kFar, h.sFar, fun i hi => by rw [k.rd, k.wr]; exact h.kRead8 i hi,
    fun i hi => by rw [k.rd, k.wr]; exact h.sRead8 i hi, fun e he => ?_,
    (word 7960 (by decide) (by decide)).trans h.bHeader,
    h.bTab.of_mem k.rd k.wr fun p hp => k.mem p (Or.inr (Or.inr (by omega_arith)))⟩
  obtain ⟨q, hq, hr⟩ := h.aTab e he
  obtain tf : TableFrame base 56 3160 s.mem t.mem := fun p _ hp => k.mem p (by omega_arith)
  exact ⟨q, by rw [tf.point (by omega_arith) (Or.inr (by omega_arith)) (by omega_arith)]; exact hq, hr⟩

theorem negR_eval (e : Env) :
    point (evalOps [.const 8 0, .sub 4 8 4, .sub 7 8 7] e) 0 1 2 3 = point e 0 1 2 3 ∧
    point (evalOps [.const 8 0, .sub 4 8 4, .sub 7 8 7] e) 4 5 6 7 = negPoint (point e 4 5 6 7) :=
  ⟨rfl, rfl⟩

/-- `-R`, beside the accumulator. -/
theorem negR_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (.block (negR fld)) s fun t => Keep base s t ∧
      point (env t.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 ∧
      point (env t.mem base) 4 5 6 7 = negPoint (tablePoint s.mem base 7552) := by
  rw [negR, List.append_assoc, WP.block_append_iff]
  refine WP.mono (tableStart_ok hs.rdi 7552) fun a ⟨ap, ka⟩ => ?_
  obtain kae : Keep base s a := Keep.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pointFromTableQ_ok (hs.of_keep kae) ap (by decide) (by decide)) fun b ⟨pb, kb⟩ => ?_
  obtain kbe := Keep.of_tableQ kb
  obtain b_low : ∀ i : Slot, i.val < 4 → env b.mem base i = env s.mem base i := by
    intro i hi
    change Proof.X25519.X86_64.F b.mem base (offset i) = Proof.X25519.X86_64.F s.mem base (offset i)
    rw [Outside_F kb.mem (by simp only [offset]; omega_arith) (Or.inl (by simp only [offset]; omega_arith)), ka.2.1]
  refine WP.mono (fieldCodeWide_ok ((hs.of_keep kae).of_keep kbe) _) fun t ⟨kt, vt⟩ => ?_
  refine ⟨(kae.trans kbe).trans kt, ?_, ?_⟩
  · rw [vt, (negR_eval _).1]
    simp only [point, b_low 0 (by decide), b_low 1 (by decide), b_low 2 (by decide),
      b_low 3 (by decide)]
  · rw [vt, (negR_eval _).2, pb, ka.2.1]

/-- Verification's code before the windows, regrouped. -/
def windowPrep (fld : Arith) (pt : Point64.Ops) : Prog isa :=
  .seq (.seq (.block windowSetup) (aTable fld pt)) (.block (windowInit fld))

/-- Before the windows: the tables, an accumulator representing `0` and the counter at 64. -/
theorem windowPrep_ok {s : State} {base sig challenge : Addr} {Aa : EPoint dZ}
    (hs : Scratch s base)
    (hp : s.mem.readW (off base 7944) 64 = sig)
    (hc : s.mem.readW (off base 7952) 64 = challenge)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off sig 32) i) 1)
    (hf : ∀ i < 32, 8192 ≤ ofs base (off (off sig 32) i))
    (hcr : ∀ i < 64, InRegions (s.rd ++ s.wr) (off challenge i) 1)
    (hcf : ∀ i < 64, 8192 ≤ ofs base (off challenge i))
    (hcr8 : ∀ j < 8, InRegions (s.rd ++ s.wr) (off challenge (8 * j)) 8)
    (hsr8 : ∀ j < 4, InRegions (s.rd ++ s.wr) (off sig (32 + 8 * j)) 8)
    (hA : Rep (tablePoint s.mem base 7424) Aa) {T : Addr} (hT : s.mem.readW (off base 7960) 64 = T)
    (hbt : BaseTbl s base T) :
    WP isa (windowPrep fld pt) s fun e => SkipLoop e base challenge sig T Aa
      (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64))
      (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32)) 64 e ∧
      PowersKeep base 56 7752 s e ∧ tablePoint e.mem base 7552 = tablePoint s.mem base 7552 := by
  rw [windowPrep]
  -- The constant `d`.
  refine WP.seq (WP.seq (WP.mono (constFieldWide_ok hs 16 Spec.Ed25519.d) fun a ⟨ka, va⟩ => ?_))
  obtain ad : env a.mem base 16 = Spec.Ed25519.d := by rw [va]; exact Function.update_self ..
  obtain aA : tablePoint a.mem base 7424 = tablePoint s.mem base 7424 :=
    workspace_tablePoint ka.mem (by decide) (by decide)
  obtain aR : tablePoint a.mem base 7552 = tablePoint s.mem base 7552 :=
    workspace_tablePoint ka.mem (by decide) (by decide)
  obtain ksa : PowersKeep base 56 7752 s a := PowersKeep.of_keep ka
  -- The multiples of `A`.
  refine WP.mono (aTable_ok (pt := pt) (ksa.scratch hs) ad (by rw [aA]; exact hA)) fun b hb => ?_
  obtain ksb := ksa.trans (hb.keep.mono (by decide) (by decide))
  obtain bR : tablePoint b.mem base 7552 = tablePoint s.mem base 7552 := by
    rw [hb.keep.mem.point (by decide) (Or.inr (by decide)) (by decide), aR]
  obtain cA : TableOf cache b.mem base 5376 Aa := fun e he => hb.table e he
  -- The accumulator and the byte counter.
  rw [windowInit, WP.block_append_iff]
  refine WP.mono (fieldCodeWide_ok (ksb.scratch hs) (constPointOps Spec.Ed25519.identity))
    fun d ⟨kd, vd⟩ => ?_
  obtain kcd : PowersKeep base 56 7752 b d := PowersKeep.of_keep kd
  refine WP.mono (mulCounterInit_ok ((ksb.trans kcd).scratch hs) 64) fun e ⟨ec, eg, er, ew, em⟩ => ?_
  obtain kde : ByteKeep base d e :=
    ⟨fun r _ _ _ => eg r (by rintro rfl; contradiction), er, ew, em.mono (by decide) (by decide)⟩
  obtain kce : ByteKeep base b e := (ByteKeep.of_win (WinKeep.of_keep kd)).trans kde
  obtain kse := ksb.trans (PowersKeep.of_byte kce)
  obtain eR : tablePoint e.mem base 7552 = tablePoint s.mem base 7552 := by
    rw [win_tablePoint kce.mem (by decide) (by decide), bR]
  obtain ed : env e.mem base 16 = Spec.Ed25519.d := by rw [header_env em, vd]; exact hb.d
  obtain ctx : WinCtx base challenge sig T Aa e :=
    ⟨kse.scratch hs, (kse.header (by decide) (by decide) (by decide)).trans hc,
      (kse.header (by decide) (by decide) (by decide)).trans hp,
      fun i hi => by rw [kse.rd, kse.wr]; exact hcr i hi,
      fun i hi => by rw [kse.rd, kse.wr]; exact hr i hi, hcf, hf,
      fun i hi => by rw [kse.rd, kse.wr]; exact hcr8 i hi,
      fun i hi => by rw [kse.rd, kse.wr]; exact hsr8 i hi,
      cA.of_win kce.mem (by decide) (by decide),
      (kse.header (by decide) (by decide) (by decide)).trans hT, hbt.of_powers kse (by decide)⟩
  obtain hK : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt e.mem challenge 64) < 256 ^ 64 := by
    obtain h := decodeLE_lt (Spec.Ed25519.bytesAt e.mem challenge 64)
    rwa [show (Spec.Ed25519.bytesAt e.mem challenge 64).length = 64 by
      simp [Spec.Ed25519.bytesAt]] at h
  obtain hS := decodeLE_lt32 e.mem (off sig 32)
  obtain eK := outside_bytes (tableFrame_work kse.mem (by decide) (by decide)) (by decide) hcf
  obtain eS := outside_bytes (tableFrame_work kse.mem (by decide) (by decide)) (by decide) hf
  refine ⟨⟨ctx, ed, ec, by rw [eK], by rw [eS], ?_, ⟨fun _ _ _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩⟩,
    kse, eR⟩
  rw [← eK, ← eS, Nat.div_eq_of_lt hK, Nat.div_eq_of_lt (Nat.lt_trans hS (by decide)), zero_smul,
    zero_smul, add_zero, header_env em, vd, constPoint_eval]
  exact identity_rep

/-- The windows' start, from the recoded digits. -/
theorem skipAt_of_recode {s₀ f g : State} {base kp sp T : Addr} {A : EPoint dZ} {K S c : Nat}
    (hf : SkipLoop s₀ base kp sp T A K S c f) (hK : K / 256 ^ c = 0) (hc32 : 32 ≤ c) (hc64 : c ≤ 64)
    (k : AllKeep base f g) (hdig : DigitsAre g.mem base (Recode.digits 5 K (8 * c)) (Recode.digits 8 S (8 * 32)))
    (hcount : g.mem.readW (off base 56) 64 = BitVec.ofNat 64 (8 * c + 9)) :
    SkipAt g base kp sp T A (Recode.digits 5 K (8 * c)) (Recode.digits 8 S (8 * 32)) (8 * c + 8)
      (8 * c + 8 + 1) g := by
  have hb := hf.ctx.scratch.nowrap
  obtain hS : S < 256 ^ 32 := hf.sVal ▸ decodeLE_lt32 _ _
  obtain henv : env g.mem base = env f.mem base := by
    funext i
    simp only [env, Proof.X25519.X86_64.F, Proof.X25519.X86_64.fe]
    have w (d : Nat) (hd : 64 ≤ d) (hd' : d + 8 ≤ 2048) :
        Proof.X25519.X86_64.word g.mem base d = Proof.X25519.X86_64.word f.mem base d :=
      Mem.readW_congr fun j hj => k.mem _ (Or.inr (Or.inl ⟨by
        rw [VG.Proof.X25519.X86_64.ofs_off base (by omega_arith)]; omega_arith, by
        rw [VG.Proof.X25519.X86_64.ofs_off base (by omega_arith)]; omega_arith⟩))
    have hi := i.isLt
    simp only [offset]
    rw [w _ (by omega_arith) (by omega_arith), w _ (by omega_arith) (by omega_arith), w _ (by omega_arith) (by omega_arith),
      w _ (by omega_arith) (by omega_arith)]
  obtain h0 : Rep (point (env g.mem base) 0 1 2 3) 0 := by
    have v := hf.value
    rw [hK, Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hS (Nat.pow_le_pow_right (by decide) hc32)), zero_smul,
      zero_smul, add_zero] at v
    rw [henv]; exact v
  obtain htop : winVal A (Recode.digits 5 K (8 * c)) (Recode.digits 8 S (8 * 32)) (8 * c + 8) (8 * c + 8 + 1) = 0 := by
    simp only [winVal, hiVal, Nat.sub_self, Recode.hsum_zero, zero_smul, add_zero]
  refine ⟨⟨hf.ctx.of_all k, by rw [henv]; exact hf.d, by rw [hcount], hdig, by rw [htop]; exact h0.proj,
    ByteKeep.refl _ _⟩, fun j h1 h2 => by omega_arith, h0, by omega_arith, le_refl _⟩

theorem verifyEquationPoints_ok {s : State} {base sig challenge : Addr} {Aa Ra : EPoint dZ}
    (hs : Scratch s base)
    (hp : s.mem.readW (off base 7944) 64 = sig)
    (hc : s.mem.readW (off base 7952) 64 = challenge)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off sig 32) i) 1)
    (hf : ∀ i < 32, 8192 ≤ ofs base (off (off sig 32) i))
    (hcr : ∀ i < 64, InRegions (s.rd ++ s.wr) (off challenge i) 1)
    (hcf : ∀ i < 64, 8192 ≤ ofs base (off challenge i))
    (hcr8 : ∀ j < 8, InRegions (s.rd ++ s.wr) (off challenge (8 * j)) 8)
    (hsr8 : ∀ j < 4, InRegions (s.rd ++ s.wr) (off sig (32 + 8 * j)) 8)
    (hA : Rep (tablePoint s.mem base 7424) Aa) (hR : Rep (tablePoint s.mem base 7552) Ra)
    {T : Addr} (hT : s.mem.readW (off base 7960) 64 = T) (hbt : BaseTbl s base T) :
    WP isa (verifyEquationPoints fld pt win) s fun t => PowersKeep base 56 7752 s t ∧
      t.gpr .rax = signWord (Spec.Ed25519.pointEqual
        (Spec.Ed25519.pointMul
          (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32)) Spec.Ed25519.basePoint)
        (Spec.Ed25519.pointAdd (tablePoint s.mem base 7552)
          (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64))
            (tablePoint s.mem base 7424)))) := by
  rw [verifyEquationPoints]
  apply WP.assoc; apply WP.assoc
  refine WP.seq (WP.mono (windowPrep_ok hs hp hc hr hf hcr hcf hcr8 hsr8 hA hT hbt) fun e ⟨w0, kse, eR⟩ => ?_)
  generalize hKd : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64) = K at w0 ⊢
  generalize hSd : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32) = S at w0 ⊢
  -- `k`'s zero bytes.
  refine WP.seq (WP.mono (skipZero_ok w0) fun f ⟨c, hc32, hc64, hf', hK⟩ => ?_)
  -- The digits.
  have fctx := hf'.ctx
  refine WP.seq (WP.mono (recodeAll_ok fctx.scratch hf'.counter hc32 hc64 fctx.kHeader fctx.sHeader
    fctx.kRead8 fctx.sRead8 fctx.kFar (fun j hj => by
      rw [show off sig (32 + j) = off (off sig 32) j from (Offset.add_add _ _ _).symm]; exact fctx.sFar j hj))
    fun g ⟨gA, gB, gc, kg⟩ => ?_)
  rw [hf'.kVal] at gA
  rw [hf'.sVal] at gB
  have gdig : DigitsAre g.mem base (Recode.digits 5 K (8 * c)) (Recode.digits 8 S (8 * 32)) :=
    fun p hp => ⟨gA p hp, gB p hp⟩
  have hg := skipAt_of_recode hf' hK hc32 hc64 kg gdig gc
  have hdg : Digits (Recode.digits 5 K (8 * c)) (Recode.digits 8 S (8 * 32)) (8 * c + 8) :=
    ⟨by omega_arith, fun p => Recode.digits_le (by decide) p, fun p => Recode.digits_le (by decide) p⟩
  -- The windows.
  refine WP.seq (WP.mono (EdWindows.ok hdg hg) fun h hh => ?_)
  have ksh := ((kse.trans (PowersKeep.of_byte hf'.keep)).trans (PowersKeep.of_all kg)).trans
    (PowersKeep.of_byte hh.keep)
  -- The comparison with `-R`.
  refine WP.seq (WP.mono (negR_ok (ksh.scratch hs)) fun u ⟨ku, u0, u4⟩ => ?_)
  have ksu := ksh.trans (PowersKeep.of_keep ku)
  refine WP.mono (pointEqual_ok (ksu.scratch hs)) fun t ⟨kt, tv⟩ => ?_
  refine ⟨ksu.trans (PowersKeep.of_keep kt), ?_⟩
  have hKlt : K < 2 ^ (8 * c) := by
    have := Nat.lt_of_div_eq_zero (by positivity) hK
    rwa [show (256 : Nat) ^ c = 2 ^ (8 * c) by rw [Nat.pow_mul]] at this
  have hSlt : S < 2 ^ (8 * 32) := hSd ▸ decodeLE_lt32 _ _
  have gv := hh.value
  simp only [winVal, hiVal, Nat.sub_zero] at gv
  rw [Recode.digits_sum (by decide) hKlt (by omega_arith), Recode.digits_sum (by decide) hSlt (by omega_arith),
    natCast_zsmul, natCast_zsmul] at gv
  have tf : TableFrame base 56 3160 f.mem g.mem := fun p _ hp => kg.mem p (by omega_arith)
  have hR' : tablePoint h.mem base 7552 = tablePoint s.mem base 7552 := by
    rw [win_tablePoint hh.keep.mem (by decide) (by decide), tf.point (by decide) (Or.inr (by decide)) (by decide),
      win_tablePoint hf'.keep.mem (by decide) (by decide), eR]
  rw [tv, u0, u4, hR', ← hKd, ← hSd]
  rw [← hKd, ← hSd] at gv
  exact congrArg signWord (window_equation hA hR gv hR.neg.proj)

end VG.Proof.Ed25519.X86_64
