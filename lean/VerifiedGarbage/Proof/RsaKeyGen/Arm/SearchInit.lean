module

public import VerifiedGarbage.Impl.RsaKeyGen.Arm.SearchInit
public import VerifiedGarbage.Proof.RsaKeyGen.SearchContract
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Slots
public import VerifiedGarbage.Proof.RsaKeyGen.InitWords
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.CountedLoop
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Impl.RsaKeyGen.Arm.SearchInit
meta import VerifiedGarbage.Proof.RsaKeyGen.SearchContract
meta import VerifiedGarbage.Proof.RsaKeyGen.Arm.Slots
meta import VerifiedGarbage.Proof.RsaKeyGen.InitWords
meta import VerifiedGarbage.Proof.X25519.Arm.Instr
meta import VerifiedGarbage.Proof.Bignum.Arm.Workspace
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.Ffdh.Arm.Block
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.CountedLoop
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.WriteBytes

/-! # `vg_rsa_prime_search_init` on ARMv7

Its checks, the words of `primeInit` as halves (`Slots`), and `e`'s
comparison with 3. Its timing depends only on the public arguments, which
its branches and its loop's count are: a taint check.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.SearchInit

open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Bignum.Arm (Workspace)
open VG.Proof.Ffdh.Arm (withRest_all)
open VG.Proof.RsaKeyGen.SearchInit (initValid primeInit_eq bytesAt_succ)
open VG.Impl.RsaKeyGen.Arm.SearchInit

/-! ## The checks -/

theorem carry_eval {s : State} {b : Bool} {P : Prop} [Decidable P] (h : (!b) = decide P) :
    eval .eq (subFlags s (0 + 0 + if b = true then 1 else 0) 0) = some (decide P) := by
  rw [← h]; cases b <;> rfl

theorem not_decide_le (a b : Nat) : (!decide (a ≤ b)) = decide (b < a) := by
  by_cases h : a ≤ b
  · rw [decide_eq_true h, decide_eq_false (by omega)]; rfl
  · rw [decide_eq_false h, decide_eq_true (by omega)]; rfl

theorem checkLow_ok (s : State) :
    WP isa (.block checkLow) s fun t =>
      (isa.eval .eq t = some (decide ((s.gpr .r1).toNat < 32)) ∧ t.mem = s.mem) ∧ Rest [.r12] s t := by
  refine withRest_all [.r12] ?_ (by rfl) (by rfl)
  unfold checkLow carryZ
  ffrun []
  refine carry_eval ?_
  rw [not_decide_le]; rfl

theorem enc512 : encodable 512 = true := by decide

theorem checkHigh_ok (s : State) :
    WP isa (.block checkHigh) s fun t =>
      (isa.eval .eq t = some (decide (512 < (s.gpr .r1).toNat)) ∧ t.mem = s.mem) ∧ Rest [.r12] s t := by
  refine withRest_all [.r12] ?_ (by rfl) (by rfl)
  unfold checkHigh carryZ
  ffrun [List.cons_append, List.nil_append, enc512]
  refine carry_eval (P := 512 < (s.gpr .r1).toNat) ?_
  rw [not_decide_le]; rfl

theorem zero_eq (x : BitVec 32) : (x - 0 == 0) = decide (x.toNat = 0) := by
  have e : x - 0 = x := BitVec.sub_zero x
  rw [e]
  exact Bool.eq_iff_iff.mpr ⟨fun h => by rw [beq_iff_eq.mp h]; rfl,
    fun h => beq_iff_eq.mpr (BitVec.eq_of_toNat_eq (by rw [of_decide_eq_true h]; rfl))⟩

theorem and7_eq (x : BitVec 32) : ((x &&& 7) - 0 == 0) = decide (x.toNat % 8 = 0) := by
  have h : (x &&& 7).toNat = x.toNat % 8 := by
    rw [BitVec.toNat_and, show (7 : BitVec 32).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  rw [zero_eq, h]

theorem eval_eq_sub (s : State) (x : BitVec 32) : eval .eq (subFlags s x 0) = some (x - 0 == 0) := rfl
theorem eval_ne_sub (s : State) (x : BitVec 32) : eval .ne (subFlags s x 0) = some (!(x - 0 == 0)) := rfl

theorem checkMod_ok (s : State) :
    WP isa (.block checkMod) s fun t =>
      (isa.eval .ne t = some (decide ((s.gpr .r1).toNat % 8 ≠ 0)) ∧ t.mem = s.mem) ∧ Rest [.r12] s t := by
  refine withRest_all [.r12] ?_ (by rfl) (by rfl)
  unfold checkMod
  ffrun []
  rw [eval_ne_sub, and7_eq, decide_not]

theorem checkEmpty_ok (s : State) :
    WP isa (.block checkEmpty) s fun t =>
      (isa.eval .eq t = some (decide ((s.gpr .r3).toNat = 0)) ∧ t.mem = s.mem) ∧ Rest [.r12] s t := by
  refine withRest_all [.r12] ?_ (by rfl) (by rfl)
  unfold checkEmpty
  ffrun []
  rw [eval_eq_sub, zero_eq]

theorem checkLong_ok (s : State) :
    WP isa (.block checkLong) s fun t =>
      (isa.eval .eq t = some (decide (8 < (s.gpr .r3).toNat)) ∧ t.mem = s.mem) ∧ Rest [.r12] s t := by
  refine withRest_all [.r12] ?_ (by rfl) (by rfl)
  unfold checkLong carryZ
  ffrun [List.cons_append, List.nil_append]
  refine carry_eval (P := 8 < (s.gpr .r3).toNat) ?_
  rw [not_decide_le]; rfl

/-- A guard: its check keeps all but `r12` and the flags, then zeros when
`P` holds. -/
theorem guard_ok {check : List Instr} {cond : Cond} {rest : Prog isa} {s : State} {P : Prop}
    [Decidable P] {Q : State → Prop}
    (hc : WP isa (.block check) s fun t =>
      (isa.eval cond t = some (decide P) ∧ t.mem = s.mem) ∧ Rest [.r12] s t)
    (hclear : ∀ t, P → t.mem = s.mem → Rest [.r12] s t → WP isa (.block clear) t Q)
    (hrest : ∀ t, ¬P → t.mem = s.mem → Rest [.r12] s t → WP isa rest t Q) :
    WP isa (Impl.RsaKeyGen.Arm.SearchInit.guard check cond rest) s Q := by
  unfold Impl.RsaKeyGen.Arm.SearchInit.guard
  refine WP.seq (WP.mono hc fun t ⟨⟨he, hm⟩, k⟩ => ?_)
  exact WP.ite _ he (fun h => hclear t (of_decide_eq_true h) hm k)
    (fun h => hrest t (of_decide_eq_false h) hm k)

/-! ## The words -/

/-- Zeros at the eight halves. -/
def zeros : List (Nat × BitVec 32) :=
  [(0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (6, 0), (7, 0)]

/-- The words but the first, for a width `L`. -/
def rest (L : Nat) : List (Nat × BitVec 32) :=
  [(1, 0), (3, 0), (5, 0), (7, 0), (2, BitVec.ofNat 32 L), (4, BitVec.ofNat 32 (32769 * L)),
    (6, BitVec.ofNat 32 (32 * L))]

/-- The first word, for a width `L` and whether `e` is 3. -/
def limit (L : Nat) (three : Bool) : Nat := if three then 64 * L else 40 * L

structure Space (B : BitVec 32) (s : State) : Prop where
  space : Workspace s B 32
  ptr : s.gpr .r0 = B

theorem Space.addr {B : BitVec 32} {s : State} (h : Space B s) {d : Nat} (hd : d < 32) :
    State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = off (State.addr B) d := by
  rw [h.ptr]; exact VG.Arm.addr_add (by have := h.space.nowrap; omega)

theorem Space.congr {B : BitVec 32} {s t : State} (h : Space B s) (hw : t.wr = s.wr)
    (h0 : t.gpr .r0 = s.gpr .r0) : Space B t :=
  ⟨h.space.congr hw, h0.trans h.ptr⟩

theorem clear_ok {B : BitVec 32} {s : State} (h : Space B s) :
    WP isa (.block clear) s fun t => t.gpr .r0 = 0 ∧ t.mem = writeSlots s.mem (State.addr B) zeros := by
  unfold clear zeros writeSlots
  ffrun [h.addr (d := 0) (by decide), h.addr (d := 4) (by decide), h.addr (d := 8) (by decide),
    h.addr (d := 12) (by decide), h.addr (d := 16) (by decide), h.addr (d := 20) (by decide),
    h.addr (d := 24) (by decide), h.addr (d := 28) (by decide),
    h.space.write (off := 0) (by decide), h.space.write (off := 4) (by decide),
    h.space.write (off := 8) (by decide), h.space.write (off := 12) (by decide),
    h.space.write (off := 16) (by decide), h.space.write (off := 20) (by decide),
    h.space.write (off := 24) (by decide), h.space.write (off := 28) (by decide)]
  rfl

theorem shl32 (L k : Nat) (h : L * 2 ^ k < 2 ^ 32) :
    BitVec.ofNat 32 L <<< k = BitVec.ofNat 32 (L * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  have hL : L < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k)) h
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hL,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]

theorem words_ok {B : BitVec 32} {s : State} (h : Space B s) {L : Nat} (hL : s.gpr .r1 = BitVec.ofNat 32 L)
    (hb : L ≤ 512) :
    WP isa (.block Impl.RsaKeyGen.Arm.SearchInit.words) s fun t =>
      t.mem = writeSlots s.mem (State.addr B) (rest L) ∧ Rest [.r12] s t := by
  refine withRest_all [.r12] ?_ (by rfl) (by rfl)
  unfold Impl.RsaKeyGen.Arm.SearchInit.words rest writeSlots
  ffrun [h.addr (d := 4) (by decide), h.addr (d := 8) (by decide),
    h.addr (d := 12) (by decide), h.addr (d := 16) (by decide), h.addr (d := 20) (by decide),
    h.addr (d := 24) (by decide), h.addr (d := 28) (by decide),
    h.space.write (off := 4) (by decide),
    h.space.write (off := 8) (by decide), h.space.write (off := 12) (by decide),
    h.space.write (off := 16) (by decide), h.space.write (off := 20) (by decide),
    h.space.write (off := 24) (by decide), h.space.write (off := 28) (by decide), hL,
    shl32 L 15 (by omega), shl32 L 5 (by omega), ← BitVec.ofNat_add]
  simp only [List.foldl_cons, List.foldl_nil, show L * 2 ^ 15 + L = 32769 * L by omega,
    show L * 2 ^ 5 = 32 * L by omega]

/-! ## Whether the exponent is 3 -/

/-- The OR of octets, widened. -/
def orOf32 (bs : List Byte) : BitVec 32 := bs.foldl (fun a b => a ||| b.setWidth 32) 0

theorem orOf32_snoc (bs : List Byte) (b : Byte) : orOf32 (bs ++ [b]) = orOf32 bs ||| b.setWidth 32 := by
  simp only [orOf32, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem byte_lt (b : Byte) (k : Nat) (hk : 8 ≤ k) : b.toNat < 2 ^ k :=
  Nat.lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by decide) hk)

theorem orOf32_toNat (bs : List Byte) : (orOf32 bs).toNat = (SearchInit.orOf bs).toNat := by
  suffices h : ∀ (a : BitVec 32) (c : BitVec 64), a.toNat = c.toNat →
      (bs.foldl (fun a x => a ||| x.setWidth 32) a).toNat = (bs.foldl (fun a x => a ||| x.setWidth 64) c).toNat from
    h 0 0 rfl
  induction bs with
  | nil => intro a c h; exact h
  | cons x xs ih =>
    intro a c h
    apply ih
    rw [BitVec.toNat_or, BitVec.toNat_or, h, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (byte_lt x 32 (by decide)), Nat.mod_eq_of_lt (byte_lt x 64 (by decide))]

theorem three32 (bs : List Byte) (b : Byte) :
    orOf32 bs ||| (b.setWidth 32 ^^^ 3) = 0 ↔ Spec.Rsa.os2ip (bs ++ [b]) = 3 := by
  rw [SearchInit.os2ip_eq_three]
  have key : (orOf32 bs ||| (b.setWidth 32 ^^^ 3)).toNat = (SearchInit.orOf bs ||| (b.setWidth 64 ^^^ 3)).toNat := by
    rw [BitVec.toNat_or, BitVec.toNat_or, BitVec.toNat_xor, BitVec.toNat_xor, orOf32_toNat,
      BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (byte_lt b 32 (by decide)),
      Nat.mod_eq_of_lt (byte_lt b 64 (by decide))]
    rfl
  constructor
  · intro h; apply BitVec.eq_of_toNat_eq; rw [← key, h]; rfl
  · intro h; apply BitVec.eq_of_toNat_eq; rw [key, h]; rfl

/-- After `j` of the `n` leading octets of `e` at `E`. -/
structure LeadInv (s : State) (E : BitVec 32) (n j : Nat) (u : State) : Prop where
  ptr : u.gpr .r2 = E + BitVec.ofNat 32 j
  acc : u.gpr .r1 = orOf32 (Spec.Rsa.bytesAt s.mem (State.addr E) j)
  count : u.gpr .r3 = BitVec.ofNat 32 (n - j)
  z : u.z = decide (n - j = 0)
  mem : u.mem = s.mem
  rest : Rest [.r1, .r2, .r3, .r12] s u

theorem sub_one32 {k : Nat} (h1 : 1 ≤ k) (hk : k < 2 ^ 32) :
    BitVec.ofNat 32 k - 1 = BitVec.ofNat 32 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  change (2 ^ 32 - 1 + k % 2 ^ 32) % 2 ^ 32 = (k - 1) % 2 ^ 32
  omega

theorem ofNat_beq {k : Nat} (hk : k < 2 ^ 32) : (BitVec.ofNat 32 k == 0) = decide (k = 0) := by
  have e := zero_eq (BitVec.ofNat 32 k)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, show BitVec.ofNat 32 k - 0 = BitVec.ofNat 32 k from
    BitVec.sub_zero _] at e
  exact e

theorem add_one32 (E : BitVec 32) (j : Nat) : E + (BitVec.ofNat 32 j + 1) = E + BitVec.ofNat 32 (j + 1) := by
  rw [BitVec.ofNat_add]; rfl

theorem lead_step {s u : State} {E : BitVec 32} {n j : Nat} (hj : j < n) (hn : n < 8)
    (fits : E.toNat + n < 2 ^ 32)
    (hrd : InRegions (s.rd ++ s.wr) (State.addr E + BitVec.ofNat 64 j) 1) (h : LeadInv s E n j u) :
    WP isa (.block leadStep) u (LeadInv s E n (j + 1)) := by
  have addr : State.addr (E + BitVec.ofNat 32 j) = State.addr E + BitVec.ofNat 64 j :=
    VG.Arm.addr_add (by omega)
  have hr : InRegions (u.rd ++ u.wr) (State.addr E + BitVec.ofNat 64 j) 1 := by
    rw [h.rest.rd, h.rest.wr]; exact hrd
  refine WP.mono (withRest_all [.r1, .r2, .r3, .r12] (Q := fun t =>
      t.gpr .r2 = E + BitVec.ofNat 32 (j + 1) ∧
      t.gpr .r1 = orOf32 (Spec.Rsa.bytesAt s.mem (State.addr E) j) ||| (u.mem (State.addr E + BitVec.ofNat 64 j)).setWidth 32 ∧
      t.gpr .r3 = BitVec.ofNat 32 (n - (j + 1)) ∧ t.z = decide (n - (j + 1) = 0) ∧ t.mem = u.mem) ?_
    (by rfl) (by rfl)) fun t ⟨⟨h2, h1, h3, hz, hm⟩, k⟩ => ⟨h2, ?_, h3, hz, hm.trans h.mem, h.rest.trans k⟩
  · unfold leadStep
    ffrun [h.ptr, h.acc, h.count, BitVec.add_zero, addr, hr, BitVec.add_assoc, ← BitVec.ofNat_add,
      sub_one32 (k := n - j) (by omega) (by omega), show n - j - 1 = n - (j + 1) by omega,
      ofNat_beq (k := n - (j + 1)) (by omega), add_one32]
  · rw [h1, bytesAt_succ, orOf32_snoc, h.mem]

theorem lead_loop {s u : State} {E : BitVec 32} {n : Nat} (h1 : 1 ≤ n) (hn : n < 8)
    (fits : E.toNat + n < 2 ^ 32)
    (hrd : ∀ j < n, InRegions (s.rd ++ s.wr) (State.addr E + BitVec.ofNat 64 j) 1) (h : LeadInv s E n 0 u) :
    WP isa (.loop (.block leadStep) .ne) u (LeadInv s E n n) := by
  refine WP.mono (WP.chunk_loop (I := LeadInv s E n) (n := n) (N := 1) (k := 0) (by decide) (by omega) h
    (fun j t hj ht => lead_step (by omega) hn fits (hrd j (by omega)) ht)
    (fun j t _ ht => ?_)) fun t ⟨j, hj, hl, ht⟩ => by
      obtain rfl : j = n := by omega
      exact ht
  have e : isa.eval .ne t = some (!decide (n - j = 0)) := by
    change some (!t.z) = _; rw [ht.z]
  rw [e]
  constructor
  · intro hl; rw [decide_eq_true (by omega)]; rfl
  · intro hl; rw [decide_eq_false (by omega)]; rfl

theorem isThree_ok {s : State} {E : BitVec 32} {len : Nat} (hp : s.gpr .r2 = E)
    (hl : s.gpr .r3 = BitVec.ofNat 32 len) (h1 : 1 ≤ len) (h8 : len ≤ 8) (fits : E.toNat + len ≤ 2 ^ 32)
    (hrd : ∀ i < len, InRegions (s.rd ++ s.wr) (State.addr E + BitVec.ofNat 64 i) 1) :
    WP isa isThree s fun t =>
      (t.gpr .r1 = 0 ↔ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr E) len) = 3) ∧ t.mem = s.mem ∧
        Rest [.r1, .r2, .r3, .r12] s t := by
  unfold isThree
  refine WP.seq (WP.mono (withRest_all [.r1, .r3] (Q := fun t =>
      t.gpr .r1 = 0 ∧ t.gpr .r3 = BitVec.ofNat 32 (len - 1) ∧ t.z = decide (len - 1 = 0) ∧ t.mem = s.mem)
    (by ffrun [hl, sub_one32 h1 (by omega), ofNat_beq (k := len - 1) (by omega)]) (by rfl) (by rfl))
    fun t ⟨⟨h9, h10, hz, hm⟩, k⟩ => ?_)
  have h0 : LeadInv s E (len - 1) 0 t := ⟨by rw [k.gpr .r2 (by decide), hp, BitVec.add_zero], by rw [h9]; rfl,
    h10, hz, hm, k.mono (by decide)⟩
  have hloop : WP isa (.ite .eq (.block []) (.loop (.block leadStep) .ne)) t (LeadInv s E (len - 1) (len - 1)) := by
    refine WP.ite _ (show some t.z = _ from rfl) (fun hz' => ?_) (fun hz' => ?_)
    · rw [hz] at hz'
      have hz' : len - 1 = 0 := of_decide_eq_true hz'
      exact WP.block_nil (by rw [hz'] at h0 ⊢; exact h0)
    · rw [hz] at hz'
      have hz' : len - 1 ≠ 0 := of_decide_eq_false hz'
      exact lead_loop (by omega) (by omega) (by omega) (fun j hj => hrd j (by omega)) h0
  refine WP.seq (WP.mono hloop fun u hu => ?_)
  have addr : State.addr (E + BitVec.ofNat 32 (len - 1)) = State.addr E + BitVec.ofNat 64 (len - 1) :=
    VG.Arm.addr_add (by omega)
  have hr : InRegions (u.rd ++ u.wr) (State.addr E + BitVec.ofNat 64 (len - 1)) 1 := by
    rw [hu.rest.rd, hu.rest.wr]; exact hrd (len - 1) (by omega)
  refine WP.mono (withRest_all [.r1, .r12] (Q := fun t => t.gpr .r1 =
      orOf32 (Spec.Rsa.bytesAt s.mem (State.addr E) (len - 1)) |||
        ((u.mem (State.addr E + BitVec.ofNat 64 (len - 1))).setWidth 32 ^^^ 3) ∧ t.mem = u.mem) ?_
      (by rfl) (by rfl)) fun t ⟨⟨h9, hmt⟩, kt⟩ =>
    ⟨?_, hmt.trans hu.mem, (hu.rest.trans (kt.mono (by decide)))⟩
  · ffrun [hu.ptr, hu.acc, addr, hr, BitVec.add_zero]
  · have hb : Spec.Rsa.bytesAt s.mem (State.addr E) len =
        Spec.Rsa.bytesAt s.mem (State.addr E) (len - 1) ++ [s.mem (State.addr E + BitVec.ofNat 64 (len - 1))] := by
      rw [← bytesAt_succ, Nat.sub_add_cancel h1]
    rw [h9, hu.mem, hb, three32]

/-! ## The first word -/

theorem carry_ofNat (c : Bool) : (0#32 + 0#32 + (if c = true then 1#32 else 0#32)) = BitVec.ofNat 32 c.toNat := by
  cases c <;> rfl

theorem first_value (L : Nat) (hL : L ≤ 512) (c : Bool) :
    BitVec.ofNat 32 L <<< 6 - BitVec.ofNat 32 c.toNat *
      (BitVec.ofNat 32 L <<< 3 + BitVec.ofNat 32 L <<< 4) =
      BitVec.ofNat 32 (if c then 40 * L else 64 * L) := by
  rw [shl32 L 6 (by omega), shl32 L 3 (by omega), shl32 L 4 (by omega), ← BitVec.ofNat_add,
    ← BitVec.ofNat_mul]
  cases c
  · simp only [Bool.false_eq_true, ite_false]
    rw [Bool.toNat_false, Nat.zero_mul, BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    congr 1; omega
  · simp only [ite_true]
    rw [Bool.toNat_true, Nat.one_mul, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
    congr 1
    omega

theorem first_ok {B : BitVec 32} {s : State} (h : Space B s) {L : Nat} (hL : L ≤ 512)
    (hm : s.mem.readW (off (State.addr B) 8) 32 = BitVec.ofNat 32 L) :
    WP isa (.block first) s fun t =>
      t.gpr .r0 = 1 ∧ t.mem = writeSlots s.mem (State.addr B) [(0, BitVec.ofNat 32 (limit L (s.gpr .r1 == 0)))] := by
  have c : decide ((1 : BitVec 32).toNat ≤ (s.gpr .r1).toNat) = !(s.gpr .r1 == 0) := by
    by_cases hz : (s.gpr .r1).toNat = 0
    · rw [show s.gpr .r1 = 0 from BitVec.eq_of_toNat_eq hz]; rfl
    · rw [decide_eq_true (by change 1 ≤ _; omega)]
      have : (s.gpr .r1 == 0) = false := beq_eq_false_iff_ne.mpr fun e => hz (by rw [e]; rfl)
      rw [this]; rfl
  unfold first
  refine WP.block_append (M := isa) (WP.mono (Q := fun (u : State) => (u.gpr .r1 = BitVec.ofNat 32 (!(s.gpr .r1 == 0)).toNat ∧
    u.mem = s.mem) ∧ Rest [.r1] s u) (withRest_all (c := .block notThree) [.r1] ?_ (by rfl) (by rfl))
    fun u hu => ?_)
  · unfold notThree
    ffrun [c]
    exact carry_ofNat _
  · obtain ⟨⟨h1, hmu⟩, ku⟩ := hu
    have hu : Space B u := h.congr ku.wr (ku.gpr .r0 (by decide))
    unfold limitWord writeSlots limit
    ffrun [hu.addr (d := 0) (by decide), hu.addr (d := 8) (by decide), hu.space.read (off := 8) (by decide),
      hu.space.write (off := 0) (by decide), hmu, hm, h1, first_value L hL]
    cases (s.gpr .r1 == 0) <;> rfl

/-! ## The whole initialization -/

/-- The four words written, or zeros. -/
def InitPost (L len : Nat) (m : Mem) (B E : BitVec 32) (t : State) : Prop :=
  if initValid L len then
    t.gpr .r0 = 1 ∧ t.mem = writeSlots (writeSlots m (State.addr B) (rest L)) (State.addr B)
      [(0, BitVec.ofNat 32 (limit L (decide (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (State.addr E) len) = 3))))]
  else t.gpr .r0 = 0 ∧ t.mem = writeSlots m (State.addr B) zeros

theorem slot8_rest (m : Mem) (B : Addr) (L : Nat) :
    (writeSlots m B (rest L)).readW (off B 8) 32 = BitVec.ofNat 32 L := by
  have := slot_writeSlots m B (N := 8) (by decide) (rest L)
    (by simp only [rest, List.mem_cons, List.not_mem_nil, or_false]
        rintro e (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide)
    2 (by decide)
  exact this

theorem rest_bytes (m : Mem) (B E : Addr) (L n : Nat) (disj : (⟨B, 32⟩ : Region).Disjoint ⟨E, n⟩)
    (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt (writeSlots m B (rest L)) E n = Spec.Rsa.bytesAt m E n := by
  have hf := writeSlots_frame m B (N := 8) (by decide) (rest L)
    (by simp only [rest, List.mem_cons, List.not_mem_nil, or_false]
        rintro e (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide)
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  exact hf.bytes (R := ⟨E, n⟩) (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact disj.symm) hn
    (List.mem_range.mp hi)

theorem init_ok {s : State} {B E : BitVec 32} (h : Space B s) (hp : s.gpr .r2 = E)
    (fits : E.toNat + (s.gpr .r3).toNat ≤ 2 ^ 32)
    (disj : (⟨State.addr B, 32⟩ : Region).Disjoint ⟨State.addr E, (s.gpr .r3).toNat⟩)
    (hrd : ∀ i < (s.gpr .r3).toNat, InRegions (s.rd ++ s.wr) (State.addr E + BitVec.ofNat 64 i) 1) :
    WP isa init s (InitPost (s.gpr .r1).toNat (s.gpr .r3).toNat s.mem B E) := by
  have clear_post : ∀ t, t.mem = s.mem → Rest [.r12] s t → ¬ initValid (s.gpr .r1).toNat (s.gpr .r3).toNat →
      WP isa (.block clear) t (InitPost (s.gpr .r1).toNat (s.gpr .r3).toNat s.mem B E) := by
    intro t hm k hv
    refine WP.mono (clear_ok (h.congr k.wr (k.gpr .r0 (by decide)))) fun u ⟨h0, hmu⟩ => ?_
    unfold InitPost
    rw [ite_eq_right_of_eq_false _ _ (eq_false hv)]
    exact ⟨h0, by rw [hmu, hm]⟩
  unfold init
  refine guard_ok (checkLow_ok s) (fun t hb hm k => clear_post t hm k (by unfold initValid; omega)) fun t₁ hb₁ hm₁ k₁ => ?_
  refine guard_ok (checkHigh_ok t₁) (fun t hb hm k => clear_post t (hm.trans hm₁) (k₁.trans k)
    (by rw [k₁.gpr .r1 (by decide)] at hb; unfold initValid; omega)) fun t₂ hb₂ hm₂ k₂ => ?_
  refine guard_ok (checkMod_ok t₂) (fun t hb hm k => clear_post t (hm.trans (hm₂.trans hm₁)) (k₁.trans (k₂.trans k))
    (by rw [k₂.gpr .r1 (by decide), k₁.gpr .r1 (by decide)] at hb; unfold initValid; omega)) fun t₃ hb₃ hm₃ k₃ => ?_
  have k₁₃ := k₁.trans (k₂.trans k₃)
  have hm₁₃ := hm₃.trans (hm₂.trans hm₁)
  refine guard_ok (checkEmpty_ok t₃) (fun t hb hm k => clear_post t (hm.trans hm₁₃) (k₁₃.trans k)
    (by rw [k₁₃.gpr .r3 (by decide)] at hb; unfold initValid; omega)) fun t₄ hb₄ hm₄ k₄ => ?_
  refine guard_ok (checkLong_ok t₄) (fun t hb hm k => clear_post t (hm.trans (hm₄.trans hm₁₃)) (k₁₃.trans (k₄.trans k))
    (by rw [k₄.gpr .r3 (by decide), k₁₃.gpr .r3 (by decide)] at hb; unfold initValid; omega)) fun t₅ hb₅ hm₅ k₅ => ?_
  have k₁₅ := k₁₃.trans (k₄.trans k₅)
  have hm₁₅ := hm₅.trans (hm₄.trans hm₁₃)
  have r1 : t₅.gpr .r1 = s.gpr .r1 := k₁₅.gpr .r1 (by decide)
  have r3 : t₅.gpr .r3 = s.gpr .r3 := k₁₅.gpr .r3 (by decide)
  rw [k₂.gpr .r1 (by decide), k₁.gpr .r1 (by decide)] at hb₃
  rw [k₁.gpr .r1 (by decide)] at hb₂
  rw [k₁₃.gpr .r3 (by decide)] at hb₄
  rw [k₄.gpr .r3 (by decide), k₁₃.gpr .r3 (by decide)] at hb₅
  have hv : initValid (s.gpr .r1).toNat (s.gpr .r3).toNat := by unfold initValid; omega
  obtain ⟨_, hL, _, h1, h8⟩ := hv
  have h5 := h.congr k₁₅.wr (k₁₅.gpr .r0 (by decide))
  unfold valid
  refine WP.seq (WP.mono (words_ok h5 (L := (s.gpr .r1).toNat) (by rw [r1, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hL)
    fun u ⟨hmu, ku⟩ => ?_)
  have hu := h5.congr ku.wr (ku.gpr .r0 (by decide))
  have hru : ∀ i < (s.gpr .r3).toNat, InRegions (u.rd ++ u.wr) (State.addr E + BitVec.ofNat 64 i) 1 := by
    rw [ku.rd, ku.wr, k₁₅.rd, k₁₅.wr]; exact hrd
  refine WP.seq (WP.mono (isThree_ok (len := (s.gpr .r3).toNat) ((ku.gpr .r2 (by decide)).trans ((k₁₅.gpr .r2 (by decide)).trans hp))
    (by rw [ku.gpr .r3 (by decide), r3, BitVec.ofNat_toNat, BitVec.setWidth_eq]) h1 h8 fits hru)
    fun z ⟨hzi, hmz, kz⟩ => ?_)
  have hz := hu.congr kz.wr (kz.gpr .r0 (by decide))
  have h8z : z.mem.readW (off (State.addr B) 8) 32 = BitVec.ofNat 32 (s.gpr .r1).toNat := by
    rw [hmz, hmu]; exact slot8_rest _ _ _
  refine WP.mono (first_ok hz hL h8z) fun t ⟨ht, hmt⟩ => ?_
  unfold InitPost
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, hL, by omega, h1, h8⟩)]
  have three : (z.gpr .r1 == 0) = decide (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr E) (s.gpr .r3).toNat) = 3) := by
    rw [← hm₁₅, ← rest_bytes t₅.mem (State.addr B) (State.addr E) (s.gpr .r1).toNat _ disj
      (by omega), ← hmu]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    exact hzi
  refine ⟨ht, ?_⟩
  rw [hmt, hmz, hmu, hm₁₅, three]

/-! ## The contract -/

def initPre (s : State) : Prop :=
  s.rd = [⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩] ∧ s.wr = [⟨State.addr (s.gpr .r0), 32⟩] ∧
    (s.gpr .r0).toNat + 32 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
    (⟨State.addr (s.gpr .r0), 32⟩ : Region).Disjoint ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩

def initPost (s t : State) : Prop :=
  match Spec.RsaKeyGen.primeInit (s.gpr .r1).toNat
      (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat) with
  | none => ((t.gpr .r1 ++ t.gpr .r0).setWidth 32).toNat = 0 ∧
      Spec.Rsa.wordsAt t.mem (State.addr (s.gpr .r0)) 4 = List.replicate 4 0
  | some values => ((t.gpr .r1 ++ t.gpr .r0).setWidth 32).toNat = 1 ∧
      ∃ first, Spec.Rsa.wordsAt t.mem (State.addr (s.gpr .r0)) 4 =
        (values ++ [first]).map (BitVec.ofNat 64) ∧
        Spec.Entropy.RequestValid (Spec.RsaKeyGen.primeEntropy (s.gpr .r1).toNat) 0 first

def initPub (s t : State) : Prop :=
  s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧ s.gpr .r2 = t.gpr .r2 ∧
    s.gpr .r3 = t.gpr .r3

def initContract : Contract isa where
  pre := initPre
  post := initPost
  pub := initPub

theorem zeros_words (m : Mem) (B : Addr) :
    Spec.Rsa.wordsAt (writeSlots m B zeros) B 4 = List.replicate 4 0 := by
  have hs := slot_writeSlots m B (N := 8) (by decide) zeros (by
    simp only [zeros, List.mem_cons, List.not_mem_nil, or_false]
    rintro e (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide)
  exact wordsAt_slots _ _ (a := 0) (b := 0) (c := 0) (d := 0) (by decide) (by decide) (by decide) (by decide)
    (hs 0 (by decide)) (hs 1 (by decide)) (hs 2 (by decide)) (hs 3 (by decide)) (hs 4 (by decide))
    (hs 5 (by decide)) (hs 6 (by decide)) (hs 7 (by decide))

theorem valid_words (m : Mem) (B : Addr) (L : Nat) (hL : L ≤ 512) (three : Bool) :
    Spec.Rsa.wordsAt (writeSlots (writeSlots m B (rest L)) B [(0, BitVec.ofNat 32 (limit L three))]) B 4 =
      [BitVec.ofNat 64 (limit L three), BitVec.ofNat 64 L, BitVec.ofNat 64 (32769 * L),
        BitVec.ofNat 64 (32 * L)] := by
  have ho := slot_writeSlots (writeSlots m B (rest L)) B (N := 8) (by decide) [(0, BitVec.ofNat 32 (limit L three))]
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro e rfl; dsimp only; decide)
  have hi := slot_writeSlots m B (N := 8) (by decide) (rest L) (by
    simp only [rest, List.mem_cons, List.not_mem_nil, or_false]
    rintro e (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide)
  have hlim : limit L three ≤ 64 * 512 := by unfold limit; split <;> omega
  refine wordsAt_slots _ _ (by omega) (by omega) (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [ho 0 (by decide)]; rfl
  · rw [ho 1 (by decide), hi 1 (by decide)]; rfl
  · rw [ho 2 (by decide), hi 2 (by decide)]; rfl
  · rw [ho 3 (by decide), hi 3 (by decide)]; rfl
  · rw [ho 4 (by decide), hi 4 (by decide)]; rfl
  · rw [ho 5 (by decide), hi 5 (by decide)]; rfl
  · rw [ho 6 (by decide), hi 6 (by decide)]; rfl
  · rw [ho 7 (by decide), hi 7 (by decide)]; rfl

private theorem result_post {s t : State}
    (h : InitPost (s.gpr .r1).toNat (s.gpr .r3).toNat s.mem (s.gpr .r0) (s.gpr .r2) t) :
    initPost s t := by
  unfold InitPost at h
  unfold initPost
  have hl : (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat).length = (s.gpr .r3).toNat := by
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  rw [primeInit_eq, hl]
  split at h
  · rename_i hv
    rw [ite_eq_left_of_eq_true _ _ (eq_true hv)]
    refine ⟨by rw [BitVec.setWidth_append_eq_right, h.1]; rfl, _, ?_, SearchInit.first_valid hv⟩
    rw [h.2, valid_words _ _ _ hv.2.1]
    simp only [limit, decide_eq_true_eq, List.cons_append, List.nil_append, List.map_cons, List.map_nil]
  · rename_i hv
    rw [ite_eq_right_of_eq_false _ _ (eq_false hv)]
    exact ⟨by rw [BitVec.setWidth_append_eq_right, h.1]; rfl, by rw [h.2, zeros_words]⟩

theorem init_correct (s : State) (h : initPre s) :
    ∃ tr t, Exec isa init s tr t ∧ abiPreserved s t ∧ initPost s t := by
  obtain ⟨hrd, hwr, hroom, hroome, disj⟩ := h
  have sp : Space (s.gpr .r0) s := ⟨⟨hroom, by rw [hwr]; exact List.mem_singleton_self _⟩, rfl⟩
  have hreads : ∀ i < (s.gpr .r3).toNat, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r2) + BitVec.ofNat 64 i) 1 :=
    fun i hi => ⟨_, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _),
      Offset.contains_base _ (by omega) (by omega)⟩
  obtain ⟨tr, t, he, hp, k⟩ := withRest_all [.r0, .r1, .r2, .r3, .r12]
    (init_ok sp rfl hroome disj hreads) (by rfl) (by rfl)
  exact ⟨tr, t, he, ⟨fun r hr => k.gpr r (by revert r; decide), k.sp⟩, result_post hp⟩

/-- The initial taint: the arguments are public. -/
def initTaint : VG.Arm.Taint.T := { regs := .ofList [.r0, .r1, .r2, .r3], flags := false }

theorem init_constantTime : ConstantTime isa (fun _ => True) initPub init := by
  refine VG.Taint.constantTime (A := VG.Arm.taint) initTaint (fun s₁ s₂ _ _ hp => ?_) (by taint_decide)
  obtain ⟨_, p0, p1, p2, p3⟩ := hp
  have wf : ∀ s, VG.Arm.Taint.Wf initTaint s := fun s =>
    ⟨(fun h => absurd rfl h), (fun _ h => by simp [initTaint] at h), (fun h => absurd h (by decide)),
      (fun _ h => by simp [initTaint] at h)⟩
  refine ⟨⟨fun r hr => ?_, fun h => by simp [initTaint] at h⟩, (fun h => absurd rfl h), wf s₁, wf s₂,
    (fun _ h => by simp [initTaint] at h), (fun _ h => by simp [initTaint] at h),
    (fun h => absurd h (by decide)), (fun k hk => absurd hk (Nat.not_lt_zero k))⟩
  simp only [initTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

private def initSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 64 | .r2 => 0x2000 | .r3 => 3 | _ => 0
  sp := 0x3000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 3⟩]
  wr := [⟨0x1000, 32⟩]

end VG.Proof.RsaKeyGen.Arm.SearchInit
