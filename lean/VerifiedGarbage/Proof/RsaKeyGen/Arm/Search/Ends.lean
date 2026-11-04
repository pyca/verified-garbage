module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Leaf
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Entry
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

/-! # How the search ends (ARMv7): exhausted, accepted, or asking for more -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Search

open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm (withRest_all)
open VG.Impl.RsaKeyGen.Arm.Search
open VG.Spec.RsaKeyGen (primeSearch primeEntropy primeRequest PrimeSearchResult)

theorem terminal_ok (s : State) (status : Nat) (hs : status < 256) :
    WP isa (.block (terminal status)) s fun t =>
      (t.gpr .r9 = 0 ∧ t.gpr .r10 = 0 ∧ t.gpr .r11 = BitVec.ofNat 32 status ∧ t.mem = s.mem) ∧
        Rest [.r9, .r10, .r11] s t := by
  refine withRest_all [.r9, .r10, .r11] ?_ (by rfl) (by rfl)
  unfold terminal
  ffrun [VG.Proof.Ffdh.Arm.encodable_byte (v := BitVec.ofNat 32 status) (by rw [BitVec.toNat_ofNat]; omega)]

/-- Exhausted: zeros at `out`, after `used` octets. -/
theorem exhausted_ok {p : SearchPublic} {o s : State} {used : Nat} (h : SearchBase p o s)
    (h8 : s.gpr .r8 = BitVec.ofNat 32 used) (hu : used ≤ p.randLen) (tr : List Nat) :
    WP isa exhausted s (SearchDone p o ⟨.exhausted, used, tr⟩) := by
  unfold exhausted
  refine WP.seq (WP.mono (terminal_ok s 3 (by decide)) fun u ⟨⟨h9, h10, h11, hm⟩, k⟩ => ?_)
  have hb := h.keep k hm
  refine WP.mono (zeroOut_ok hb) fun t ⟨⟨hz, hf⟩, kt⟩ => ?_
  exact ⟨hb.step kt (by decide) hf (out_changes h.input) (out_apart h.input),
    (kt.gpr .r8 (by decide)).trans ((k.gpr .r8 (by decide)).trans h8),
    (kt.gpr .r9 (by decide)).trans h9, (kt.gpr .r10 (by decide)).trans h10,
    (kt.gpr .r11 (by decide)).trans h11, hz, hu, Nat.zero_le _, Nat.zero_le _⟩

theorem add_ofNat32 (a b : Nat) : BitVec.ofNat 32 a + BitVec.ofNat 32 b = BitVec.ofNat 32 (a + b) :=
  (BitVec.ofNat_add a b).symm

/-- The prime, after `used + n` octets. -/
theorem accept_ok {p : SearchPublic} {o s : State} {used n c : Nat} (h : SearchBase p o s)
    (h8 : s.gpr .r8 = BitVec.ofNat 32 used) (h12 : s.gpr .r12 = BitVec.ofNat 32 n) (hu : used + n ≤ p.randLen)
    (hout : Spec.Rsa.bytesAt s.mem (State.addr p.op) p.len = Spec.Rsa.i2osp c p.len) (tr : List Nat) :
    WP isa (.block accept) s (SearchDone p o ⟨.accepted c, used + n, tr⟩) := by
  refine WP.mono (withRest_all [.r8, .r9, .r10, .r11] (Q := fun t => t.gpr .r8 = BitVec.ofNat 32 (used + n) ∧
    t.gpr .r9 = 0 ∧ t.gpr .r10 = 0 ∧ t.gpr .r11 = 1 ∧ t.mem = s.mem) ?_ (by rfl) (by rfl))
    fun t ⟨⟨h8', h9, h10, h11, hm⟩, k⟩ => ⟨h.keep k hm, h8', h9, h10, h11, by rw [hm]; exact hout, hu,
      Nat.zero_le _, Nat.zero_le _⟩
  unfold accept terminal
  ffrun [h8, h12, add_ofNat32]

/-! ## Asking for more -/

theorem carry_eval {s : State} {b : Bool} {P : Prop} [Decidable P] (h : (!b) = decide P) :
    eval .eq (subFlags s (0 + 0 + if b = true then 1 else 0) 0) = some (decide P) := by
  rw [← h]; cases b <;> rfl

theorem not_decide_le (a b : Nat) : (!decide (a ≤ b)) = decide (b < a) := by
  by_cases h : a ≤ b
  · rw [decide_eq_true h, decide_eq_false (by omega)]; rfl
  · rw [decide_eq_false h, decide_eq_true (by omega)]; rfl

theorem raise_ok {s : State} {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (h0 : s.gpr .r0 = BitVec.ofNat 32 a) (h2 : s.gpr .r2 = BitVec.ofNat 32 b) :
    WP isa raise s fun t => (t.gpr .r0 = BitVec.ofNat 32 (max a b) ∧ t.mem = s.mem) ∧ Rest [.r0, .r3] s t := by
  refine withRest_all [.r0, .r3] ?_ (by rfl) (by rfl)
  unfold raise
  refine WP.seq (WP.mono (withRest_all (c := .block [.cmp .r0 (.reg .r2), .mov .r3 (.imm 0),
      .adc .r3 .r3 (.imm 0), .cmp .r3 (.imm 0)]) [.r3]
    (Q := fun t => isa.eval .eq t = some (decide (a < b)) ∧ t.mem = s.mem) ?_ (by rfl) (by rfl))
    fun u ⟨⟨he, hm⟩, k⟩ => ?_)
  · ffrun [h0, h2, toNat_small ha, toNat_small hb]
    exact carry_eval (P := a < b) (not_decide_le _ _)
  have k0 : u.gpr .r0 = BitVec.ofNat 32 a := (k.gpr .r0 (by decide)).trans h0
  have k2 : u.gpr .r2 = BitVec.ofNat 32 b := (k.gpr .r2 (by decide)).trans h2
  refine WP.ite _ he (fun hl => ?_) (fun hl => ?_)
  · have hl := of_decide_eq_true hl
    ffrun [k2, hm]
    congr 1; omega
  · have hl := of_decide_eq_false hl
    refine WP.block_nil ⟨?_, hm⟩
    rw [k0]; congr 1; omega

theorem cap_ok {s : State} {a c : Nat} (ha : a < 2 ^ 32) (hc : c < 2 ^ 32)
    (h0 : s.gpr .r0 = BitVec.ofNat 32 a) (h1 : s.gpr .r1 = BitVec.ofNat 32 c) :
    WP isa cap s fun t => (t.gpr .r0 = BitVec.ofNat 32 (min a c) ∧ t.mem = s.mem) ∧ Rest [.r0, .r3] s t := by
  refine withRest_all [.r0, .r3] ?_ (by rfl) (by rfl)
  unfold cap
  refine WP.seq (WP.mono (withRest_all (c := .block [.cmp .r0 (.reg .r1), .mov .r3 (.imm 0),
      .adc .r3 .r3 (.imm 0), .cmp .r3 (.imm 0)]) [.r3]
    (Q := fun t => isa.eval .eq t = some (decide (a < c)) ∧ t.mem = s.mem) ?_ (by rfl) (by rfl))
    fun u ⟨⟨he, hm⟩, k⟩ => ?_)
  · ffrun [h0, h1, toNat_small ha, toNat_small hc]
    exact carry_eval (P := a < c) (not_decide_le _ _)
  have k0 : u.gpr .r0 = BitVec.ofNat 32 a := (k.gpr .r0 (by decide)).trans h0
  have k1 : u.gpr .r1 = BitVec.ofNat 32 c := (k.gpr .r1 (by decide)).trans h1
  refine WP.ite _ he (fun hl => ?_) (fun hl => ?_)
  · have hl := of_decide_eq_true hl
    refine WP.block_nil ⟨?_, hm⟩
    rw [k0]; congr 1; omega
  · have hl := of_decide_eq_false hl
    ffrun [k1, hm]
    congr 1; omega

theorem shl32' (L k : Nat) (h : L * 2 ^ k < 2 ^ 32) :
    BitVec.ofNat 32 L <<< k = BitVec.ofNat 32 (L * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  have hL : L < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k)) h
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hL,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]

/-- The next tape's length, from `left` octets of the tape, the budget `cap`
in `r1` and the width in `r5`. -/
theorem request_ok {s : State} {L left : Nat} (hL : L ≤ 512) (hleft : left ≤ 32769 * L)
    (h0 : s.gpr .r0 = BitVec.ofNat 32 left) (h1 : s.gpr .r1 = BitVec.ofNat 32 (32769 * L))
    (h5 : s.gpr .r5 = BitVec.ofNat 32 L) :
    WP isa request s fun t =>
      (t.gpr .r10 = BitVec.ofNat 32 (primeRequest L left) ∧ t.gpr .r11 = 0 ∧ t.mem = s.mem) ∧
        Rest [.r0, .r2, .r3, .r10, .r11] s t := by
  unfold request
  refine WP.seq (WP.mono (withRest_all (c := .block [.mov .r2 (.shifted .r5 .lsl 4)]) [.r2]
    (Q := fun t => t.gpr .r2 = BitVec.ofNat 32 (16 * L) ∧ t.mem = s.mem)
    (by ffrun [h5, shl32' L 4 (by omega), show L * 2 ^ 4 = 16 * L by omega]) (by rfl) (by rfl))
    fun u ⟨⟨h2, hm⟩, k⟩ => ?_)
  refine WP.seq (WP.mono (raise_ok (a := left) (b := 16 * L) (by omega) (by omega)
    ((k.gpr .r0 (by decide)).trans h0) h2) fun u2 ⟨⟨h0', hm2⟩, k2⟩ => ?_)
  refine WP.seq (WP.mono (withRest_all (c := .block [.dp .add .r0 .r0 (.reg .r0)]) [.r0]
    (Q := fun t => t.gpr .r0 = BitVec.ofNat 32 (2 * max left (16 * L)) ∧ t.mem = u2.mem)
    (by ffrun [h0', add_ofNat32, show max left (16 * L) + max left (16 * L) = 2 * max left (16 * L) by omega])
    (by rfl) (by rfl)) fun u3 ⟨⟨h03, hm3⟩, k3⟩ => ?_)
  have h13 : u3.gpr .r1 = BitVec.ofNat 32 (32769 * L) :=
    (k3.gpr .r1 (by decide)).trans ((k2.gpr .r1 (by decide)).trans ((k.gpr .r1 (by decide)).trans h1))
  refine WP.seq (WP.mono (cap_ok (by omega) (by omega) h03 h13) fun u4 ⟨⟨h04, hm4⟩, k4⟩ => ?_)
  refine WP.mono (withRest_all (c := .block [.mov .r10 (.reg .r0), .mov .r11 (.imm 0)]) [.r10, .r11]
    (Q := fun t => t.gpr .r10 = BitVec.ofNat 32 (min (2 * max left (16 * L)) (32769 * L)) ∧ t.gpr .r11 = 0 ∧
      t.mem = u4.mem) (by ffrun [h04]) (by rfl) (by rfl)) fun t ⟨⟨h10, h11, hmt⟩, kt⟩ => ?_
  refine ⟨⟨?_, h11, by rw [hmt, hm4, hm3, hm2, hm]⟩,
    (k.mono (by decide)).trans ((k2.mono (by decide)).trans ((k3.mono (by decide)).trans
      ((k4.mono (by decide)).trans (kt.mono (by decide)))))⟩
  rw [h10]
  unfold primeRequest Spec.Entropy.request primeEntropy
  congr 2

namespace SearchBase

variable {p : SearchPublic} {o s : State}

/-- The search's stack argument `j`, from below its frame. -/
theorem arg_addr (h : SearchBase p o s) (j : Nat) :
    State.addr (s.sp + BitVec.ofNat 32 (pushBytes + 0 + 4 * j)) = stackArgAddr o j := by
  rw [h.sp, SearchPublic.S1, h.input.sp_eq, show pushBytes + 0 + 4 * j = 40 + 4 * j from rfl, sub_add_ofNat]
  rfl

theorem arg_read (h : SearchBase p o s) {j : Nat} (hj : j < 8) :
    InRegions (s.rd ++ s.wr) (stackArgAddr o j) 4 := by
  have top := h.input.facts.top
  refine ⟨inArgs o, List.mem_append_left _ (by rw [h.rd, h.input.rd]; simp [inReads]), ?_⟩
  have e : stackArgAddr o j = stackArgAddr o 0 + BitVec.ofNat 64 (4 * j) := by
    simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
    exact VG.Arm.addr_add (by rw [← h.input.sp_eq]; omega)
  rw [e]; exact Offset.contains_base _ (by omega) (by omega)

theorem arg_value (h : SearchBase p o s) {j : Nat} (hj : j < 8) :
    s.mem.readW (stackArgAddr o j) 32 = stackArg o j :=
  h.input.arg_frame h.frame hj

end SearchBase

theorem randLen_arg {p : SearchPublic} {o : State} (h : SearchInput p o) :
    stackArg o 4 = BitVec.ofNat 32 p.randLen := by
  rw [← h.2]; exact (VG.Proof.RsaKeyGen.Arm.Search.ofNat_toNat32 _).symm

theorem sub_eq_beq {a c : Nat} (ha : a < 2 ^ 32) (hc : c < 2 ^ 32) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 c == 0) = decide (a = c) := by
  by_cases e : a = c
  · subst e; rw [BitVec.sub_self, decide_eq_true rfl]; rfl
  · rw [decide_eq_false e]
    refine beq_eq_false_iff_ne.mpr fun h => e ?_
    have h' : BitVec.ofNat 32 a - BitVec.ofNat 32 c = 0 := h
    have h'' : BitVec.ofNat 32 a = BitVec.ofNat 32 c := by
      rw [← BitVec.sub_add_cancel (BitVec.ofNat 32 a) (BitVec.ofNat 32 c), h']
      exact BitVec.zero_add _
    have := congrArg BitVec.toNat h''
    rwa [toNat_small ha, toNat_small hc] at this

/-- The tape ended inside a candidate, after `used` octets, with `k`
counted candidates left: exhausted if it had the whole budget, else a
request for more. -/
theorem short_ok {p : SearchPublic} {o s : State} {used k : Nat} (h : SearchBase p o s)
    (h8 : s.gpr .r8 = BitVec.ofNat 32 used) (h9 : s.gpr .r9 = BitVec.ofNat 32 k) (hu : used ≤ p.randLen)
    (hk : k ≤ p.remaining)
    (hout : Spec.Rsa.bytesAt s.mem (State.addr p.op) p.len = List.replicate p.len 0) (tr : List Nat) :
    WP isa short s (SearchDone p o (if primeEntropy p.len ≤ p.randLen - used then ⟨.exhausted, used, tr⟩
      else ⟨.entropy k (primeRequest p.len (p.randLen - used)), used, tr⟩)) := by
  have hi := h.input
  have f := hi.facts
  have hl := f.valid
  unfold Spec.RsaKeyGen.primeLenValid at hl
  have rl := f.randLen
  unfold primeEntropy at rl
  unfold short
  refine WP.seq (WP.mono (withRest_all (c := .block [arg .r0 0 4, .dp .sub .r0 .r0 (.reg .r8),
      .mov .r1 (.shifted .r5 .lsl 15), .dp .add .r1 .r1 (.reg .r5), .cmp .r0 (.reg .r1)]) [.r0, .r1]
    (Q := fun t => t.gpr .r0 = BitVec.ofNat 32 (p.randLen - used) ∧ t.gpr .r1 = BitVec.ofNat 32 (32769 * p.len) ∧
      isa.eval .eq t = some (decide (p.randLen - used = 32769 * p.len)) ∧ t.mem = s.mem) ?_ (by rfl) (by rfl))
    fun u ⟨⟨h0, h1, he, hm⟩, k'⟩ => ?_)
  · unfold arg
    have c : pushBytes + 0 + 4 * 4 < 4096 := by decide
    ffrun [h.arg_addr 4, h.arg_read (j := 4) (by decide), h.arg_value (j := 4) (by decide), randLen_arg hi, h8,
      h.r5, BitVec.ofNat_sub_ofNat_of_le _ _ (show used < 2 ^ 32 by omega) hu, shl32' p.len 15 (by omega),
      add_ofNat32, show p.len * 2 ^ 15 + p.len = 32769 * p.len by omega, c]
    change some (BitVec.ofNat 32 (p.randLen - used) - BitVec.ofNat 32 (32769 * p.len) == 0) = _
    rw [sub_eq_beq (by omega) (by omega)]
  have hu' := h.keep k' hm
  have h8' : u.gpr .r8 = BitVec.ofNat 32 used := (k'.gpr .r8 (by decide)).trans h8
  refine WP.ite _ he (fun hz => ?_) (fun hz => ?_)
  · have hz := of_decide_eq_true hz
    rw [ite_eq_left_of_eq_true _ _ (by unfold primeEntropy; exact eq_true (by omega))]
    exact exhausted_ok hu' h8' hu tr
  · have hz := of_decide_eq_false hz
    rw [ite_eq_right_of_eq_false _ _ (by unfold primeEntropy; exact eq_false (by omega))]
    refine WP.mono (request_ok hl.2.1 (by omega) h0 h1 ((k'.gpr .r5 (by decide)).trans h.r5))
      fun t ⟨⟨h10, h11, hmt⟩, kt⟩ => ⟨hu'.keep kt hmt, (kt.gpr .r8 (by decide)).trans h8',
        (kt.gpr .r9 (by decide)).trans ((k'.gpr .r9 (by decide)).trans h9), h10, h11,
        by rw [hmt, hm]; exact hout, hu, hk, by
          unfold primeRequest Spec.Entropy.request; exact Nat.min_le_right _ _⟩

end VG.Proof.RsaKeyGen.Arm.Search
