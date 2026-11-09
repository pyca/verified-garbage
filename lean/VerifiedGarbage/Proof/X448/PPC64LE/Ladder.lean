module

public import VerifiedGarbage.Proof.X448.PPC64LE.Slots
public import VerifiedGarbage.Proof.X448.Ladder
import VerifiedGarbage.Proof.X448.PPC64LE.Mul
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# X448 on PPC64LE: the ladder

One iteration of the ladder (`step_ok`) takes the elements `x1, x2, z2, x3,
z3` from the state after the bits `447` down to `n` (`ladderAfter k x1
n`) to the state after `n - 1`, with the swap in `r0` and the counter in
`r12`; the loop (`ladder_ok`) runs it for the bits 447 down to 0.

The field operations (`FOp`, `opsCodeW`) take the multiplication as a
parameter, and the state between them (`CurW`, `StpW`) the registers that
may change: `opsCode`, `Cur` and `Stp` are those of `mul` and `work`, which
Ed448's proofs use, and X448's ladder uses `mulX` (`mulP`) and `workR`,
which adds `r14`–`r31` (`MulCur`, `mulCur_mul`, `mulCur_mulP`).
-/

@[expose] public section

namespace VG.Proof.X448.PPC64LE

open VG VG.PPC64LE VG.Impl.X448.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.X448 (P Fe Ladder ladderStep cswap a24)
open VG.Proof.X448 (toFe ladderAfter ladderAfter_step ladderStep_eq bit bit_le ladderAfter_swap_le)

/-- The registers the code changes: all but the pointers to `out` (`r3`) and
the working space (`r6`). -/
abbrev work : List Reg := [.r0, .r4, .r5, .r7, .r8, .r9, .r10, .r11, .r12]

/-- The registers X448's code changes, with the multiplication in registers
(`mulP`), until it restores `r14`–`r31`. -/
abbrev workR : List Reg :=
  [.r0, .r4, .r5, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22,
    .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]

/-- `s'` is `s` but for the registers `W` and the field area. -/
structure StpW (W : List Reg) (b : Addr) (s s' : State) : Prop where
  rest : Rest W s s'
  frame : Frame [FA b] s.mem s'.mem

/-- `s'` is `s` but for the registers `work` and the field area. -/
abbrev Stp := StpW work

theorem StpW.refl (W : List Reg) (b : Addr) (s : State) : StpW W b s s := ⟨Rest.refl _ _, Frame.refl _ _⟩

theorem StpW.trans {W : List Reg} {b : Addr} {s₁ s₂ s₃ : State} (h₁ : StpW W b s₁ s₂) (h₂ : StpW W b s₂ s₃) :
    StpW W b s₁ s₃ :=
  ⟨h₁.rest.trans h₂.rest, h₁.frame.trans h₂.frame⟩

theorem StpW.of_rest {W : List Reg} {b : Addr} {s s' : State} {ws : List Reg} (hr : Rest ws s s')
    (hws : ∀ r ∈ ws, r ∈ W) (hm : s'.mem = s.mem) : StpW W b s s' :=
  ⟨hr.mono hws, by rw [hm]; exact Frame.refl _ _⟩

theorem StpW.mono {W W' : List Reg} {b : Addr} {s s' : State} (h : StpW W b s s') (hW : ∀ r ∈ W, r ∈ W') :
    StpW W' b s s' :=
  ⟨h.rest.mono hW, h.frame⟩

theorem Stp.refl (b : Addr) (s : State) : Stp b s s := StpW.refl _ _ _

theorem Stp.trans {b : Addr} {s₁ s₂ s₃ : State} (h₁ : Stp b s₁ s₂) (h₂ : Stp b s₂ s₃) : Stp b s₁ s₃ :=
  StpW.trans h₁ h₂

theorem Stp.of_rest {b : Addr} {s s' : State} {ws : List Reg} (hr : Rest ws s s')
    (hws : ∀ r ∈ ws, r ∈ work) (hm : s'.mem = s.mem) : Stp b s s' :=
  StpW.of_rest hr hws hm

/-- Between field operations, from `s0`: `r0` and `r12` hold `a` and `c`,
and the slots `qs` the elements `v`; only the registers `W` changed. -/
structure CurW (W : List Reg) (b : Addr) (s0 : State) (a c : BitVec 64) (qs : List Nat) (v : Nat → Fe)
    (s : State) : Prop where
  ctx : Ctx b s
  stp : StpW W b s0 s
  r0 : s.gpr .r0 = a
  r12 : s.gpr .r12 = c
  slots : SlotsOk s.mem b qs v

/-- `CurW` with only the registers of `work` changed. -/
abbrev Cur := CurW work

section
variable {W : List Reg} {b : Addr} {s0 : State} {a c : BitVec 64} {qs : List Nat} {v : Nat → Fe}

/-- A step that changes only the registers `ws` (not `r0`, `r6` or `r12`) of `W`. -/
theorem CurW.nextR {ws : List Reg} (hws : ∀ r ∈ ws, r ∈ W) (h0 : Reg.r0 ∉ ws) (h6 : Reg.r6 ∉ ws)
    (h12 : Reg.r12 ∉ ws) {s s' : State} (h : CurW W b s0 a c qs v s) (hr : Rest ws s s')
    (hf : Frame [FA b] s.mem s'.mem) {qs' : List Nat} {v' : Nat → Fe}
    (hS : SlotsOk s'.mem b qs' v') : CurW W b s0 a c qs' v' s' :=
  ⟨h.ctx.of_rest hr h6, h.stp.trans ⟨hr.mono hws, hf⟩,
    by rw [hr.gpr _ h0, h.r0], by rw [hr.gpr _ h12, h.r12], hS⟩

theorem CurW.next (hW : ∀ r ∈ clob, r ∈ W) {s s' : State} (h : CurW W b s0 a c qs v s)
    (hr : Rest clob s s') (hf : Frame [FA b] s.mem s'.mem) {qs' : List Nat} {v' : Nat → Fe}
    (hS : SlotsOk s'.mem b qs' v') : CurW W b s0 a c qs' v' s' :=
  h.nextR hW (by decide) (by decide) (by decide) hr hf hS

theorem Cur.next {s s' : State} (h : Cur b s0 a c qs v s) (hr : Rest clob s s')
    (hf : Frame [FA b] s.mem s'.mem) {qs' : List Nat} {v' : Nat → Fe}
    (hS : SlotsOk s'.mem b qs' v') : Cur b s0 a c qs' v' s' :=
  CurW.next (by decide) h hr hf hS

theorem opMul {o x y : Nat} (hq : Sep1 o qs = true) (ho : o + 56 ≤ ACC) (hx : x ∈ qs)
    (hy : y ∈ qs) (hx4 : x % 4 = 0) (hy4 : y % 4 = 0) (ho4 : o % 4 = 0) {s : State}
    (h : Cur b s0 a c qs v s) :
    WP isa (mul o x y) s (Cur b s0 a c (o :: qs) (upd v o (v x * v y))) :=
  WP.mono (mulS hq ho hx hy hx4 hy4 ho4 h.ctx h.slots) fun _ ⟨hr, hf, hS⟩ => h.next hr hf hS

/-- `mulX`, between field operations of `workR`. -/
theorem opMulX {o x y : Nat} (hq : Sep1 o qs = true) (ho : o + 56 ≤ ACC) (hx : x ∈ qs)
    (hy : y ∈ qs) (hx4 : x % 4 = 0) (hy4 : y % 4 = 0) (ho4 : o % 4 = 0) {s : State}
    (h : CurW workR b s0 a c qs v s) :
    WP isa (mulP o x y) s (CurW workR b s0 a c (o :: qs) (upd v o (v x * v y))) :=
  WP.mono (mulXS hq ho hx hy hx4 hy4 ho4 h.ctx h.slots) fun _ ⟨hr, hf, hS⟩ =>
    h.nextR (by decide) (by decide) (by decide) (by decide) hr hf hS

theorem opAddW (hW : ∀ r ∈ clob, r ∈ W) {o x y : Nat} (hq : Sep1 o qs = true) (ho : o + 56 ≤ ACC)
    (hx : x ∈ qs) (hy : y ∈ qs) (ho4 : o % 4 = 0) (hx4 : x % 4 = 0) (hy4 : y % 4 = 0) {s : State}
    (h : CurW W b s0 a c qs v s) :
    WP isa (.block (add o x y)) s (CurW W b s0 a c (o :: qs) (upd v o (v x + v y))) :=
  WP.mono (addS hq ho hx hy ho4 hx4 hy4 h.ctx h.slots) fun _ ⟨hr, hf, hS⟩ => h.next hW hr hf hS

theorem opSubW (hW : ∀ r ∈ clob, r ∈ W) {o x y : Nat} (hq : Sep1 o qs = true) (ho : o + 56 ≤ ACC)
    (hx : x ∈ qs) (hy : y ∈ qs) (ho4 : o % 4 = 0) (hx4 : x % 4 = 0) (hy4 : y % 4 = 0) {s : State}
    (h : CurW W b s0 a c qs v s) :
    WP isa (.block (sub o x y)) s (CurW W b s0 a c (o :: qs) (upd v o (v x - v y))) :=
  WP.mono (subS hq ho hx hy ho4 hx4 hy4 h.ctx h.slots) fun _ ⟨hr, hf, hS⟩ => h.next hW hr hf hS

theorem opMul24W (hW : ∀ r ∈ clob, r ∈ W) {o x : Nat} (hq : Sep1 o qs = true) (ho : o + 56 ≤ ACC)
    (hx : x ∈ qs) (ho4 : o % 4 = 0) (hx4 : x % 4 = 0) {s : State} (h : CurW W b s0 a c qs v s) :
    WP isa (.block (mulA24 o x)) s (CurW W b s0 a c (o :: qs) (upd v o (a24 * v x))) :=
  WP.mono (mul24S hq ho hx ho4 hx4 h.ctx h.slots) fun _ ⟨hr, hf, hS⟩ => h.next hW hr hf hS

theorem opAdd {o x y : Nat} (hq : Sep1 o qs = true) (ho : o + 56 ≤ ACC) (hx : x ∈ qs)
    (hy : y ∈ qs) (ho4 : o % 4 = 0) (hx4 : x % 4 = 0) (hy4 : y % 4 = 0) {s : State} (h : Cur b s0 a c qs v s) :
    WP isa (.block (add o x y)) s (Cur b s0 a c (o :: qs) (upd v o (v x + v y))) :=
  opAddW (by decide) hq ho hx hy ho4 hx4 hy4 h

theorem opSub {o x y : Nat} (hq : Sep1 o qs = true) (ho : o + 56 ≤ ACC) (hx : x ∈ qs)
    (hy : y ∈ qs) (ho4 : o % 4 = 0) (hx4 : x % 4 = 0) (hy4 : y % 4 = 0) {s : State} (h : Cur b s0 a c qs v s) :
    WP isa (.block (sub o x y)) s (Cur b s0 a c (o :: qs) (upd v o (v x - v y))) :=
  opSubW (by decide) hq ho hx hy ho4 hx4 hy4 h

theorem opMul24 {o x : Nat} (hq : Sep1 o qs = true) (ho : o + 56 ≤ ACC) (hx : x ∈ qs)
    (ho4 : o % 4 = 0) (hx4 : x % 4 = 0) {s : State} (h : Cur b s0 a c qs v s) :
    WP isa (.block (mulA24 o x)) s (Cur b s0 a c (o :: qs) (upd v o (a24 * v x))) :=
  opMul24W (by decide) hq ho hx ho4 hx4 h

end

/-- A multiplication `m` takes `CurW W` to `CurW W` with the product in its slot. -/
def MulCur (W : List Reg) (m : Nat → Nat → Nat → Prog isa) : Prop :=
  ∀ {b : Addr} {s0 : State} {a c : BitVec 64} {qs : List Nat} {v : Nat → Fe} {o x y : Nat},
    Sep1 o qs = true → o + 56 ≤ ACC → x ∈ qs → y ∈ qs → x % 4 = 0 → y % 4 = 0 → o % 4 = 0 →
    ∀ {s : State}, CurW W b s0 a c qs v s → WP isa (m o x y) s (CurW W b s0 a c (o :: qs) (upd v o (v x * v y)))

theorem mulCur_mul : MulCur work mul := fun hq ho hx hy hx4 hy4 ho4 _ h => opMul hq ho hx hy hx4 hy4 ho4 h

theorem mulCur_mulP : MulCur workR mulP := fun hq ho hx hy hx4 hy4 ho4 _ h =>
  opMulX hq ho hx hy hx4 hy4 ho4 h

/-! ## Sequences of field operations -/

/-- A field operation: `o = x · y`, `a24 · x`, `x + y` or `x - y`. -/
inductive FOp
  | mul (o x y : Nat)
  | mul24 (o x : Nat)
  | add (o x y : Nat)
  | sub (o x y : Nat)

def FOp.code : FOp → Prog isa
  | .mul o x y => Impl.X448.PPC64LE.mul o x y
  | .mul24 o x => .block (mulA24 o x)
  | .add o x y => .block (Impl.X448.PPC64LE.add o x y)
  | .sub o x y => .block (Impl.X448.PPC64LE.sub o x y)

/-- `FOp.code`, with the multiplication `m`. -/
def FOp.codeW (m : Nat → Nat → Nat → Prog isa) : FOp → Prog isa
  | .mul o x y => m o x y
  | .mul24 o x => .block (mulA24 o x)
  | .add o x y => .block (Impl.X448.PPC64LE.add o x y)
  | .sub o x y => .block (Impl.X448.PPC64LE.sub o x y)

theorem FOp.code_eq (op : FOp) : op.code = op.codeW Impl.X448.PPC64LE.mul := by cases op <;> rfl

def FOp.out : FOp → Nat
  | .mul o _ _ | .mul24 o _ | .add o _ _ | .sub o _ _ => o

def FOp.x : FOp → Nat
  | .mul _ x _ | .mul24 _ x | .add _ x _ | .sub _ x _ => x

def FOp.y : FOp → Nat
  | .mul _ _ y | .add _ _ y | .sub _ _ y => y
  | .mul24 _ x => x

def FOp.val : FOp → (Nat → Fe) → Fe
  | .mul _ x y, v => v x * v y
  | .mul24 _ x, v => a24 * v x
  | .add _ x y, v => v x + v y
  | .sub _ x y, v => v x - v y

/-- The operations `ops`, then `k`. -/
def opsCode : List FOp → Prog isa → Prog isa
  | [], k => k
  | op :: ops, k => .seq op.code (opsCode ops k)

/-- `opsCode`, with the multiplication `m`. -/
def opsCodeW (m : Nat → Nat → Nat → Prog isa) : List FOp → Prog isa → Prog isa
  | [], k => k
  | op :: ops, k => .seq (op.codeW m) (opsCodeW m ops k)

theorem opsCode_eq : ∀ (ops : List FOp) (k : Prog isa), opsCode ops k = opsCodeW Impl.X448.PPC64LE.mul ops k
  | [], _ => rfl
  | op :: ops, k => by rw [opsCode, opsCodeW, FOp.code_eq, opsCode_eq ops k]

/-- Each operation's slots are separate or equal, below `ACC`, and its inputs
known. -/
def opsOk : List FOp → List Nat → Bool
  | [], _ => true
  | op :: ops, qs => Sep1 op.out qs && op.out + 56 ≤ ACC && qs.contains op.x &&
      qs.contains op.y && op.out % 4 == 0 && op.x % 4 == 0 && op.y % 4 == 0 &&
      opsOk ops (op.out :: qs)

/-- The elements after the operations. -/
def runOps : List FOp → (Nat → Fe) → Nat → Fe
  | [], v => v
  | op :: ops, v => runOps ops (upd v op.out (op.val v))

/-- The slots known after the operations. -/
def outsQ : List FOp → List Nat → List Nat
  | [], qs => qs
  | op :: ops, qs => outsQ ops (op.out :: qs)

theorem op_okW {W : List Reg} {m : Nat → Nat → Nat → Prog isa} (hW : ∀ r ∈ clob, r ∈ W) (hm : MulCur W m)
    {b : Addr} {s0 : State} {a c : BitVec 64} {qs : List Nat} {v : Nat → Fe} (op : FOp)
    (hq : Sep1 op.out qs = true) (ho : op.out + 56 ≤ ACC) (hx : op.x ∈ qs) (hy : op.y ∈ qs)
    (ho4 : op.out % 4 = 0) (hx4 : op.x % 4 = 0) (hy4 : op.y % 4 = 0) {s : State}
    (h : CurW W b s0 a c qs v s) :
    WP isa (op.codeW m) s (CurW W b s0 a c (op.out :: qs) (upd v op.out (op.val v))) := by
  cases op with
  | mul o x y => exact hm hq ho hx hy hx4 hy4 ho4 h
  | mul24 o x => exact opMul24W hW hq ho hx ho4 hx4 h
  | add o x y => exact opAddW hW hq ho hx hy ho4 hx4 hy4 h
  | sub o x y => exact opSubW hW hq ho hx hy ho4 hx4 hy4 h

theorem ops_okW {W : List Reg} {m : Nat → Nat → Nat → Prog isa} (hW : ∀ r ∈ clob, r ∈ W) (hm : MulCur W m)
    {b : Addr} {s0 : State} {a c : BitVec 64} {k : Prog isa} {Q : State → Prop} :
    ∀ (ops : List FOp) (qs : List Nat) (v : Nat → Fe) (s : State), opsOk ops qs = true →
      CurW W b s0 a c qs v s → (∀ s', CurW W b s0 a c (outsQ ops qs) (runOps ops v) s' → WP isa k s' Q) →
      WP isa (opsCodeW m ops k) s Q
  | [], _, _, s, _, h, hk => hk s h
  | op :: ops, qs, v, s, hok, h, hk => by
    simp only [opsOk, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem, beq_iff_eq] at hok
    obtain ⟨⟨⟨⟨⟨⟨⟨h1, h3⟩, h4⟩, h5⟩, h9⟩, h7⟩, h8⟩, h6⟩ := hok
    exact WP.seq (WP.mono (op_okW hW hm op h1 h3 h4 h5 h9 h7 h8 h) fun s' h' => ops_okW hW hm ops _ _ s' h6 h' hk)

theorem op_ok {b : Addr} {s0 : State} {a c : BitVec 64} {qs : List Nat} {v : Nat → Fe} (op : FOp)
    (hq : Sep1 op.out qs = true) (ho : op.out + 56 ≤ ACC) (hx : op.x ∈ qs) (hy : op.y ∈ qs)
    (ho4 : op.out % 4 = 0) (hx4 : op.x % 4 = 0) (hy4 : op.y % 4 = 0) {s : State}
    (h : Cur b s0 a c qs v s) :
    WP isa op.code s (Cur b s0 a c (op.out :: qs) (upd v op.out (op.val v))) := by
  rw [FOp.code_eq]; exact op_okW (by decide) mulCur_mul op hq ho hx hy ho4 hx4 hy4 h

theorem ops_ok {b : Addr} {s0 : State} {a c : BitVec 64} {k : Prog isa} {Q : State → Prop} :
    ∀ (ops : List FOp) (qs : List Nat) (v : Nat → Fe) (s : State), opsOk ops qs = true →
      Cur b s0 a c qs v s → (∀ s', Cur b s0 a c (outsQ ops qs) (runOps ops v) s' → WP isa k s' Q) →
      WP isa (opsCode ops k) s Q := fun ops qs v s hok h hk => by
  rw [opsCode_eq]; exact ops_okW (by decide) mulCur_mul ops qs v s hok h hk

/-! ## One iteration -/

/-- The field operations of an iteration, after the swaps. -/
def ladOps : List FOp :=
  [.add A X2 Z2, .mul AA A A, .sub B X2 Z2, .mul BB B B, .sub E AA BB, .add C X3 Z3, .sub D X3 Z3,
    .mul DA D A, .mul CB C B, .add X3 DA CB, .mul X3 X3 X3, .sub Z3 DA CB, .mul Z3 Z3 Z3,
    .mul Z3 X1 Z3, .mul X2 AA BB, .mul24 Z2 E, .add Z2 AA Z2, .mul Z2 E Z2]

/-- The slots the ladder's state lives in. -/
def LQ : List Nat := [X1, X2, Z2, X3, Z3]

theorem ladOps_ok : opsOk ladOps LQ = true := by decide

/-- The elements of the ladder's state `st`, and `x1`. -/
def ladV (x1 : Fe) (st : Ladder) (q : Nat) : Fe :=
  if q = X1 then x1 else if q = X2 then st.x2 else if q = Z2 then st.z2 else if q = X3 then st.x3
  else st.z3

theorem cswap_fst (sw : Nat) (x y : Fe) : (Spec.X448.cswap sw x y).1 = sel sw x y := by
  unfold Spec.X448.cswap sel; split <;> rfl

theorem cswap_snd (sw : Nat) (x y : Fe) : (Spec.X448.cswap sw x y).2 = sel sw y x := by
  unfold Spec.X448.cswap sel; split <;> rfl

/-- The elements after an iteration. -/
theorem ladOps_vals (k : Nat) (x1 : Fe) (st : Ladder) (t : Nat) :
    ∀ q ∈ LQ, runOps ladOps (swapV Z2 Z3 (st.swap ^^^ bit k t) (swapV X2 X3 (st.swap ^^^ bit k t)
      (ladV x1 st))) q = ladV x1 (ladderStep k x1 st t) q := by
  intro q hq
  rw [ladderStep_eq]
  simp only [LQ, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl <;>
    simp only [ladOps, runOps, FOp.out, FOp.val, upd, swapV, ladV, cswap_fst, cswap_snd, X1, X2, Z2, X3,
      Z3, A, B, C, D, AA, BB, E, DA, CB, Nat.reduceEqDiff, ↓reduceIte]

theorem ofNat_xor {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    BitVec.ofNat 64 x ^^^ BitVec.ofNat 64 y = BitVec.ofNat 64 (x ^^^ y) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_xor, toNat_imm hx, toNat_imm hy, toNat_imm (Nat.xor_lt_two_pow hx hy)]

theorem xor_le_one {x y : Nat} (hx : x ≤ 1) (hy : y ≤ 1) : x ^^^ y ≤ 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hx with rfl | rfl <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hy with rfl | rfl <;> decide

/-- The loop invariant of the ladder from `sL`, before the iteration for the
bit `n - 1`. -/
structure LadInv (b : Addr) (k : Nat) (x1 : Fe) (sL : State) (n : Nat) (s : State) : Prop where
  cur : CurW workR b sL (BitVec.ofNat 64 (ladderAfter k x1 n).swap) (BitVec.ofNat 64 n) LQ
    (ladV x1 (ladderAfter k x1 n)) s

/-- The bits of the scalar in `BITS`. -/
def Bits (b : Addr) (k : Nat) (m : Mem) : Prop :=
  ∀ t < 448, m (b + BitVec.ofNat 64 (BITS + t)) = BitVec.ofNat 8 (bit k t)

theorem head_ok {b : Addr} {k : Nat} {x1 : Fe} {sL : State} (hbits : Bits b k sL.mem)
    {n : Nat} (hn : 1 ≤ n) (hn' : n ≤ 448) {s : State} (h : LadInv b k x1 sL n s) :
    WP isa (.block stepHead) s (CurW workR b sL (BitVec.ofNat 64 (bit k (n - 1))) (BitVec.ofNat 64 (n - 1)) LQ
      (swapV Z2 Z3 ((ladderAfter k x1 n).swap ^^^ bit k (n - 1))
        (swapV X2 X3 ((ladderAfter k x1 n).swap ^^^ bit k (n - 1)) (ladV x1 (ladderAfter k x1 n))))) := by
  obtain ⟨hcur⟩ := h
  have hc := hcur.ctx
  have hB : BITS = 1064 := rfl
  have hA := ACC_eq
  have hsw := ladderAfter_swap_le k x1 hn'
  have hbt := bit_le k (n - 1)
  have hx := xor_le_one hsw hbt
  simp only [stepHead, mask, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_subi (by decide) (by decide) fun s1 u1 => ?_
  have e12 : s1.gpr .r12 = BitVec.ofNat 64 (n - 1) := by
    rw [u1.gpr, hcur.r12, ofNat_sub_one hn (by omega_arith)]
  refine wp_add fun s2 u2 => ?_
  refine wp_lbz (a := b + BitVec.ofNat 64 (n - 1 + BITS)) (by decide) (by decide)
    (by rw [u2.gpr, e12, u1.other _ (by decide), hc.r6, Offset.add_add])
    (by rw [u2.rd, u2.wr, u1.rd, u1.wr]; exact hc.inR (by omega_arith)) fun s3 u3 => ?_
  have e4 : s3.gpr .r4 = BitVec.ofNat 64 (bit k (n - 1)) := by
    rw [u3.gpr, u2.mem, u1.mem, hcur.stp.frame _ fun r hr => ?_, Nat.add_comm, hbits _ (by omega_arith)]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
    · rw [List.mem_singleton.mp hr]
      exact fun h => Offset.disjoint_base b (d := n - 1 + BITS) (n := 1) (k := ACC + 112) (by omega_arith)
        (by omega_arith) _ (Region.contains_self _ _) h
  refine wp_xor fun s4 u4 => ?_
  have e0 : s4.gpr .r0 = BitVec.ofNat 64 ((ladderAfter k x1 n).swap ^^^ bit k (n - 1)) := by
    rw [u4.gpr, e4, u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), hcur.r0,
      ofNat_xor (by omega_arith) (by omega_arith)]
  refine wp_li (by decide) fun s5 u5 => wp_sub fun s6 u6 => ?_
  have e11 : s6.gpr .r11 = 0 - BitVec.ofNat 64 ((ladderAfter k x1 n).swap ^^^ bit k (n - 1)) := by
    rw [u6.gpr, u5.gpr, u5.other _ (by decide), e0]; rfl
  have hr6 : Rest [.r0, .r4, .r11, .r12] s s6 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))))
  have hm6 : s6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have hc6 : Ctx b s6 := hc.of_rest hr6 (by decide)
  have hS6 : SlotsOk s6.mem b LQ (ladV x1 (ladderAfter k x1 n)) := by
    rw [hm6]; exact hcur.slots
  refine WP.append (cswapS (by decide) (by decide) (by decide) (by decide) (by decide)
    hc6 hx e11 hS6) fun s7 ⟨hr7, hf7, hS7⟩ => ?_
  have hc7 : Ctx b s7 := hc6.of_rest hr7 (by decide)
  refine WP.append (cswapS (by decide) (by decide) (by decide) (by decide) (by decide)
    hc7 hx (by rw [hr7.gpr _ (by decide), e11]) hS7) fun s8 ⟨hr8, hf8, hS8⟩ => ?_
  refine wp_addi (by decide) (by decide) fun s9 u9 => WP.block_nil ?_
  have hr9 : Rest [.r0, .r4, .r5, .r7, .r8, .r11, .r12] s s9 :=
    (hr6.mono (by decide)).trans ((hr7.mono (by decide)).trans ((hr8.mono (by decide)).trans
      (u9.rest (by decide))))
  exact ⟨hc.of_rest hr9 (by decide),
    hcur.stp.trans ⟨hr9.mono (by decide), by rw [u9.mem, ← hm6]; exact hf7.trans hf8⟩,
    by rw [u9.gpr, hr8.gpr _ (by decide), hr7.gpr _ (by decide), u6.other _ (by decide),
      u5.other _ (by decide), u4.other _ (by decide), e4, BitVec.add_zero],
    by rw [u9.other _ (by decide), hr8.gpr _ (by decide), hr7.gpr _ (by decide), u6.other _ (by decide),
      u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), e12],
    by rw [u9.mem]; exact hS8⟩

theorem step_eq : step = .seq (.block stepHead) (opsCodeW mulP ladOps (.block [])) := rfl

theorem step_ok {b : Addr} {k : Nat} {x1 : Fe} {sL : State} (hbits : Bits b k sL.mem)
    {n : Nat} (hn : 1 ≤ n) (hn' : n ≤ 448) {s : State} (h : LadInv b k x1 sL n s) :
    WP isa step s fun s' => LadInv b k x1 sL (n - 1) s' ∧ (s'.gpr .r12 != 0) = decide (n - 1 ≠ 0) := by
  rw [step_eq]
  refine WP.seq (WP.mono (head_ok hbits hn hn' h) fun s1 h1 =>
    ops_okW (by decide) mulCur_mulP ladOps LQ _ s1 ladOps_ok h1 fun s2 h2 => ?_)
  refine WP.block_nil ⟨⟨h2.ctx, h2.stp, ?_, h2.r12, ?_⟩, ?_⟩
  · rw [h2.r0, ladderAfter_step k x1 (show n - 1 < 448 by omega_arith), Nat.sub_add_cancel hn,
      ladderStep_eq]
  · refine (h2.slots.mono (by decide)).congr fun q hq => ?_
    rw [ladderAfter_step k x1 (show n - 1 < 448 by omega_arith), Nat.sub_add_cancel hn]
    exact ladOps_vals k x1 _ (n - 1) q hq
  · rw [h2.r12, ofNat_ne_zero (by omega_arith)]

/-- The ladder, from the state with the bits of the scalar in `BITS` and the
initial elements in `LQ`. -/
theorem ladder_ok {b : Addr} {k : Nat} {x1 : Fe} {s : State} (hc : Ctx b s) (hbits : Bits b k s.mem)
    (hS : SlotsOk s.mem b LQ (ladV x1 (VG.Proof.X448.init x1))) :
    WP isa ladder s fun s' => StpW workR b s s' ∧ Ctx b s' ∧
      s'.gpr .r0 = BitVec.ofNat 64 (ladderAfter k x1 0).swap ∧
      SlotsOk s'.mem b LQ (ladV x1 (ladderAfter k x1 0)) := by
  unfold ladder
  refine WP.seq (wp_li (by decide) fun s1 u1 => wp_li (by decide) fun s2 u2 => WP.block_nil ?_)
  have hr2 : Rest [.r0, .r12] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  have hbits2 : Bits b k s2.mem := by rw [hm2]; exact hbits
  have h448 : LadInv b k x1 s2 448 s2 :=
    ⟨⟨hc.of_rest hr2 (by decide), StpW.refl _ _ _, by rw [u2.gpr]; rfl,
      by rw [u2.other _ (by decide), u1.gpr], by rw [hm2]; exact hS⟩⟩
  have hst : StpW workR b s s2 := StpW.of_rest hr2 (by decide) hm2
  refine WP.mono (Q := LadInv b k x1 s2 0) (WP.loop (M := isa)
    (fun m s' => 1 ≤ m ∧ m ≤ 448 ∧ LadInv b k x1 s2 m s') ?_ 448 s2 ⟨by decide, Nat.le_refl _, h448⟩)
    fun s' ⟨h'⟩ => ⟨hst.trans h'.stp, h'.ctx, h'.r0, h'.slots⟩
  rintro m s' ⟨h1, h2, hl⟩
  refine WP.mono (step_ok hbits2 h1 h2 hl) fun s'' ⟨hl', hz⟩ => ?_
  by_cases hm : m - 1 = 0
  · exact .inl ⟨by rw [eval_nonzero, hz]; simp [hm], by rw [hm] at hl'; exact hl'⟩
  · exact .inr ⟨by rw [eval_nonzero, hz]; simp [hm], m - 1, by omega_arith, by omega_arith, by omega_arith, hl'⟩

end VG.Proof.X448.PPC64LE
