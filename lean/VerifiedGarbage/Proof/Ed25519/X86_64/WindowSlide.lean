import VerifiedGarbage.Proof.Ed25519.X86_64.WindowDigits
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# Verification's windows: a doubling and the digits at each position

The digits' arrays hold `fA` (`k`'s) and `fB` (`S`'s) up to position `top` (`DigitsAre`,
`Digits`). After position `p` the accumulator represents `winVal p`, the digits from `p` on
weighted by powers of two (`hiVal`) times `A` and `-B` (`WinLoop`); before the digits at `p` are
added, twice `winVal (p + 1)` (`WinMid`), with `T` computed if a digit at `p` is nonzero, as an
addition needs it. `windows_ok`: from one above `top` with the identity, the windows skip the
leading zero digits and end at position 0.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open VG.Proof.X25519.X86_64 (off ofs Keeps clob Outside)

variable {fld : Arith} [EdArith fld]

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
    rw [k _ (Or.inr (by rw [VG.Proof.X25519.X86_64.ofs_off' base (by omega)]; omega))]
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
  rw [show top + 1 - p = (top + 1 - (p + 1)) + 1 by omega, Recode.hsum_succ]

theorem hiVal_zero (f : Nat → Nat) {top p : Nat} (h : ∀ j, p ≤ j → j ≤ top → f j = 0) :
    hiVal f top p = 0 :=
  Recode.hsum_eq_zero fun j h1 h2 => by rw [h j h1 (by omega)]; rfl

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
  have hp : point (env t.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 := by
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

/-- `k`'s digit at `p` added. -/
theorem addA_ok {s₀ s : State} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat} {top p : Nat}
    (hdg : Digits fA fB top) (hp : p ≤ top) (h : WinMid s₀ base kp sp T A fA fB top p s) :
    WP isa (.seq (.block (digitAt 0)) (addDigit 5376 (pointAddCached fld))) s
      (WinHalf s₀ base kp sp T A fA fB top p) := by
  have hdA : dig s.mem base 0 p = fA p := (h.digits p (by have := hdg.top; omega)).1
  refine WP.seq (WP.mono (digitAt_ok h.ctx.scratch (by have := hdg.top; omega) (by decide) h.counter)
    fun a ⟨ab, az, ka⟩ => ?_)
  rw [hdA] at ab az
  have kaw : WinKeep base s a := WinKeep.of_keeps ka (by decide)
  have ha := h.ctx.of_keep kaw
  have aenv : env a.mem base = env s.mem base := by rw [ka.2.1]
  refine WP.mono (addDigit_ok (a := (2 : Int) • winVal A fA fB top (p + 1)) pointAddCached_spec
    ha.scratch (by decide) (by decide) ha.aTab (fA p) (hdg.a p) ab az (by rw [aenv]; exact h.d)
    (by rw [aenv]; exact h.value) (fun hv => by rw [aenv]; exact h.full (Or.inl hv)))
    fun b ⟨bp, bf, bd, kb⟩ => ?_
  have kab := (ByteKeep.of_win kaw).trans (ByteKeep.of_win kb)
  exact ⟨h.ctx.of_byte kab, by rw [bd, aenv]; exact h.d,
    kb.counter.trans (kaw.counter.trans h.counter), h.digits.of_byte kab.mem, bp,
    fun hv => bf (Or.inr (by rw [aenv]; exact h.full (Or.inr hv))), h.keep.trans kab⟩

/-- `S`'s digit at `p` added. -/
theorem addB_ok {s₀ s : State} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat} {top p : Nat}
    (hdg : Digits fA fB top) (hp : p ≤ top) (h : WinHalf s₀ base kp sp T A fA fB top p s) :
    WP isa (.seq (.block (digitAt 1)) (addBase fld)) s (WinLoop s₀ base kp sp T A fA fB top p) := by
  have hdB : dig s.mem base 1 p = fB p := (h.digits p (by have := hdg.top; omega)).2
  refine WP.seq (WP.mono (digitAt_ok h.ctx.scratch (by have := hdg.top; omega) (by decide) h.counter)
    fun c ⟨cb, cz, kc⟩ => ?_)
  rw [hdB] at cb cz
  have kcw : WinKeep base s c := WinKeep.of_keeps kc (by decide)
  have hc' := h.ctx.of_keep kcw
  have cenv : env c.mem base = env s.mem base := by rw [kc.2.1]
  refine WP.mono (addBase_ok (fld := fld) (a := (2 : Int) • winVal A fA fB top (p + 1) + (Recode.dec (fA p)) • A)
    hc'.scratch hc'.bHeader hc'.bTab (fB p) (hdg.b p) cb cz
    (by rw [cenv]; exact h.d) (by rw [cenv]; exact h.value) (fun hv => by rw [cenv]; exact h.full hv))
    fun t ⟨tp, _, td, kt⟩ => ?_
  have kct := (ByteKeep.of_win kcw).trans (ByteKeep.of_win kt)
  refine ⟨h.ctx.of_byte kct, by rw [td, cenv]; exact h.d, kt.counter.trans (kcw.counter.trans h.counter),
    h.digits.of_byte kct.mem, ?_, h.keep.trans kct⟩
  rw [winVal_step A fA fB hp]; exact tp

/-- The digits at `p` added: from before them to after `p`. -/
theorem addsAt_ok {s₀ s : State} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat} {top p : Nat}
    (hdg : Digits fA fB top) (hp : p ≤ top) (h : WinMid s₀ base kp sp T A fA fB top p s) :
    WP isa (addsAt fld) s (WinLoop s₀ base kp sp T A fA fB top p) := by
  rw [addsAt]
  apply WP.assoc
  exact WP.seq (WP.mono (addA_ok hdg hp h) fun _ ha => addB_ok hdg hp ha)

/-! ## The doubling -/

/-- One doubling, with `T` if a digit at the counter's position `p` is nonzero: after `p + 1`,
with the counter at `p`, to before the digits at `p`. -/
theorem dblAt_ok {s₀ s : State} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat} {top p : Nat}
    (hdg : Digits fA fB top) (hp : p ≤ top) (h : WinAt s₀ base kp sp T A fA fB (winVal A fA fB top (p + 1)) p s) :
    WP isa (dblAt fld) s (WinMid s₀ base kp sp T A fA fB top p) := by
  have hb := h.ctx.scratch.nowrap
  rw [dblAt]
  refine WP.seq (WP.mono (digitsAt_ok h.ctx.scratch (by have := hdg.top; omega) h.counter) fun a ⟨az, ka⟩ => ?_)
  rw [(h.digits p (by have := hdg.top; omega)).1, (h.digits p (by have := hdg.top; omega)).2] at az
  have kaw : WinKeep base s a := WinKeep.of_keeps ka (by decide)
  have ha := h.ctx.of_keep kaw
  have aenv : env a.mem base = env s.mem base := by rw [ka.2.1]
  have hv : RepP (point (env a.mem base) 0 1 2 3) (winVal A fA fB top (p + 1)) := by rw [aenv]; exact h.value
  have fin (t : State) (b : Bool) (kt : Keep base a t)
      (tp : RepP (point (env t.mem base) 0 1 2 3) (winVal A fA fB top (p + 1) + winVal A fA fB top (p + 1)))
      (tf : b = true → Rep (point (env t.mem base) 0 1 2 3)
        (winVal A fA fB top (p + 1) + winVal A fA fB top (p + 1)))
      (th : ∀ i : Slot, 16 ≤ i.val → env t.mem base i = env a.mem base i)
      (hbz : (fA p ≠ 0 ∨ fB p ≠ 0) → b = true) :
      WinMid s₀ base kp sp T A fA fB top p t := by
    have e : winVal A fA fB top (p + 1) + winVal A fA fB top (p + 1) = (2 : Int) • winVal A fA fB top (p + 1) := by
      rw [two_zsmul]
    rw [e] at tp tf
    have kt' : ByteKeep base s t := (ByteKeep.of_win kaw).trans (ByteKeep.of_win (WinKeep.of_keep kt))
    exact ⟨h.ctx.of_byte kt', by rw [th 16 (by decide), aenv]; exact h.d,
      (kt.mem.word (Or.inl (by decide)) (by decide)).trans (kaw.counter.trans h.counter),
      h.digits.of_byte kt'.mem, tp, fun hf => tf (hbz hf), h.keep.trans kt'⟩
  refine WP.ite (!decide (fA p = 0 ∧ fB p = 0)) (by simp only [eval, az, Option.map_some]) (fun hz => ?_)
    (fun hz => ?_)
  · refine WP.mono (dbl_ok (fld := fld) ha.scratch true hv) fun t ⟨kt, tp, tf, th⟩ => ?_
    exact fin t true kt tp tf th fun _ => rfl
  · have h0 : fA p = 0 ∧ fB p = 0 := by simpa using hz
    refine WP.mono (dbl_ok (fld := fld) ha.scratch false hv) fun t ⟨kt, tp, tf, th⟩ => ?_
    exact fin t false kt tp tf th fun hf => by omega

/-- The position below: from after `p + 1` to after `p`, ZF set if `p` is zero. -/
theorem stepAt_ok {s₀ s : State} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat} {top p : Nat}
    (hdg : Digits fA fB top) (hp : p ≤ top) (h : WinLoop s₀ base kp sp T A fA fB top (p + 1) s) :
    WP isa (stepAt fld) s fun t => t.zf = some (decide (p = 0)) ∧ WinLoop s₀ base kp sp T A fA fB top p t := by
  have hb := h.ctx.scratch.nowrap
  rw [stepAt]
  refine WP.seq (WP.mono (batchBegin_ok h.ctx.scratch p h.counter) fun a ⟨_, ac, ag, ar, aw, am⟩ => ?_)
  have ka : ByteKeep base s a := ⟨fun r _ hb _ => ag r hb, ar, aw, am.mono (by decide) (by decide)⟩
  have ha : WinAt s₀ base kp sp T A fA fB (winVal A fA fB top (p + 1)) p a :=
    ⟨h.ctx.of_byte ka, by rw [header_env am]; exact h.d, ac, h.digits.of_byte ka.mem,
      by rw [header_env am]; exact h.value, h.keep.trans ka⟩
  refine WP.seq (WP.mono (dblAt_ok hdg hp ha) fun b hb' => ?_)
  refine WP.seq (WP.mono (addsAt_ok hdg hp hb') fun c hc => ?_)
  refine WP.mono (counterTest_ok hc.ctx.scratch (by have := hdg.top; omega) hc.counter) fun t ⟨tz, kt⟩ => ?_
  have kt' := ByteKeep.of_keeps (base := base) kt (by decide)
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
  have ka : ByteKeep base s a := ⟨fun r _ hb _ => ag r hb, ar, aw, am.mono (by decide) (by decide)⟩
  have hsa := hl.ctx.of_byte ka
  refine WP.mono (digitsAt_ok hsa.scratch (by have := hdg.top; omega) ac) fun b ⟨bz, kb⟩ => ?_
  have hdA := (hl.digits.of_byte ka.mem p (by have := hdg.top; omega))
  rw [hdA.1, hdA.2] at bz
  have kb' : ByteKeep base a b := ByteKeep.of_keeps kb (by decide)
  have kab := ka.trans kb'
  have benv : env b.mem base = env s.mem base := by rw [kb.2.1, header_env am]
  have bc : b.mem.readW (off base 56) 64 = BitVec.ofNat 64 p := by rw [kb.2.1]; exact ac
  have h0 : winVal A fA fB top (p + 1) = 0 := winVal_zero h.zero
  have mid (t : State) (kt : ByteKeep base s t) (te : env t.mem base = env s.mem base)
      (tc : t.mem.readW (off base 56) 64 = BitVec.ofNat 64 p) : WinMid s₀ base kp sp T A fA fB top p t := by
    have hr : Rep (point (env t.mem base) 0 1 2 3) ((2 : Int) • winVal A fA fB top (p + 1)) := by
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
    refine WP.mono (counterTest_ok (kab.scratch hl.ctx.scratch) (by have := hdg.top; omega) bc)
      fun t ⟨tz, kt⟩ => ?_
    have kt' := kab.trans (ByteKeep.of_keeps kt (by decide))
    have te : env t.mem base = env s.mem base := by rw [kt.2.1, benv]
    have tc : t.mem.readW (off base 56) 64 = BitVec.ofNat 64 p := by rw [kt.2.1]; exact bc
    have hst : skipStops fA fB p = decide (p = 0) := by
      simp only [skipStops, hz0, and_self, decide_true, Bool.not_true, Bool.false_or]
    by_cases hp0 : p = 0
    · subst hp0
      exact ⟨by rw [tz, hst], fun _ => mid t kt' te tc, fun hf => absurd hf (by rw [hst]; decide)⟩
    · have hz' : ∀ j, p ≤ j → j ≤ top → fA j = 0 ∧ fB j = 0 := fun j h1 h2 => by
        rcases Nat.eq_or_lt_of_le h1 with rfl | h1'
        · exact hz0
        · exact h.zero j (by omega) h2
      refine ⟨by rw [tz, hst], fun ht => absurd ht (by rw [hst]; simp [hp0]),
        fun _ => ⟨⟨hl.ctx.of_byte kt', by rw [te]; exact hl.d, tc,
        hl.digits.of_byte kt'.mem, ?_, hl.keep.trans kt'⟩, hz', by rw [te]; exact h.full, by omega, by omega⟩⟩
      rw [te, winVal_zero hz']; exact h.full.proj

/-- The windows, from one above `top` with the identity, to after position 0. -/
theorem windows_ok {s₀ s : State} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat} {top : Nat}
    (hdg : Digits fA fB top) (h : SkipAt s₀ base kp sp T A fA fB top (top + 1) s) :
    WP isa (windows fld) s (WinLoop s₀ base kp sp T A fA fB top 0) := by
  rw [windows]
  refine WP.seq (WP.mono (show WP isa (.loop skipTop .ne) s fun t =>
      ∃ p, p ≤ top ∧ WinMid s₀ base kp sp T A fA fB top p t by
    apply WP.loop (fun q t => SkipAt s₀ base kp sp T A fA fB top q t) (n := top + 1)
    · intro q t ht
      obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := ht.pos; omega : q ≠ 0)
      have hle := ht.le
      refine WP.mono (skipTop_ok hdg ht) fun u ⟨uz, ut, uf⟩ => ?_
      cases hs : skipStops fA fB p
      · exact Or.inr ⟨by simp only [eval, uz, hs, Option.map_some, Bool.not_false], p, by omega, uf hs⟩
      · exact Or.inl ⟨by simp only [eval, uz, hs, Option.map_some, Bool.not_true], p, by omega, ut hs⟩
    · exact h) fun a ⟨p, hp, ha⟩ => ?_)
  refine WP.seq (WP.mono (addsAt_ok hdg hp ha) fun b hb => ?_)
  refine WP.seq (WP.mono (counterTest_ok hb.ctx.scratch (by have := hdg.top; omega) hb.counter)
    fun c ⟨cz, kc⟩ => ?_)
  have kc' := ByteKeep.of_keeps (base := base) kc (by decide)
  have hc : WinLoop s₀ base kp sp T A fA fB top p c :=
    ⟨hb.ctx.of_byte kc', by rw [kc.2.1]; exact hb.d, by rw [kc.2.1]; exact hb.counter,
      by rw [kc.2.1]; exact hb.digits, by rw [kc.2.1]; exact hb.value, hb.keep.trans kc'⟩
  refine WP.ite (!decide (p = 0)) (by simp only [eval, cz, Option.map_some]) (fun hz => ?_) (fun hz => ?_)
  · have hp0 : p ≠ 0 := by simpa using hz
    apply WP.loop (fun n t => WinLoop s₀ base kp sp T A fA fB top n t ∧ 0 < n ∧ n ≤ top) (n := p)
    · intro n t ⟨ht, hn0, hn⟩
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      refine WP.mono (stepAt_ok hdg (by omega) ht) fun u ⟨uz, hu⟩ => ?_
      by_cases hm : m = 0
      · subst hm
        exact Or.inl ⟨by simp only [eval, uz, decide_true, Option.map_some, Bool.not_true], hu⟩
      · exact Or.inr ⟨by simp only [eval, uz, decide_eq_false hm, Option.map_some, Bool.not_false],
          m, by omega, hu, by omega, by omega⟩
    · exact ⟨hc, by omega, hp⟩
  · have hp0 : p = 0 := by simpa using hz
    subst hp0
    exact WP.block_nil hc

end VG.Proof.Ed25519.X86_64
