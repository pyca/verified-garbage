module

public import VerifiedGarbage.Proof.Rsa.Arm.KeyOps
public import VerifiedGarbage.Proof.Rsa.Arm.KeyWs
public import VerifiedGarbage.Impl.Bignum.Arm.CompareWords
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Rsa.Arm.KeyWs
import VerifiedGarbage.Proof.Rsa.ZeroTest32
import VerifiedGarbage.Proof.Rsa.InverseArithmetic
import VerifiedGarbage.Proof.Framework.Block
import Batteries.Tactic.Alias

/-! ### `Rsa.Arm.KeyEqContext`, which only this module used -/

section

/-! ### `Bignum.Arm.CompareWords`, which only this module used -/

section

/-! A bounded wordwise comparison visits every word and returns exact equality. -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CompareWordStep.lean`, which only this module imported.
section

/-! One wordwise XOR/OR comparison step preserves memory. -/

section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_ldr wp_dp wp_subs op2_imm op2_reg dpVal)

theorem compareWordStep_ok (s : State) (a b : Addr)
    (pa : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = a)
    (pb : State.addr (s.gpr .r1 + BitVec.ofNat 32 0) = b)
    (ra : InRegions (s.rd ++ s.wr) a 4) (rb : InRegions (s.rd ++ s.wr) b 4) :
    WP isa (.block compareWordStep) s fun t => t.mem = s.mem ∧
      t.gpr .r0 = s.gpr .r0 + 4 ∧ t.gpr .r1 = s.gpr .r1 + 4 ∧
      t.gpr .r2 = s.gpr .r2 ||| (s.mem.readW a 32 ^^^ s.mem.readW b 32) ∧
      t.gpr .lr = s.gpr .lr - 1 ∧ t.z = (s.gpr .lr - 1 == 0) ∧
      Rest [.r0, .r1, .r2, .r3, .r12, .lr] s t := by
  unfold compareWordStep
  refine wp_ldr (by decide) pa ra fun s1 u1 => ?_
  refine wp_ldr (a := b) (by decide) (by rw [u1.other .r1 (by decide)]; exact pb)
    (by rw [u1.rd, u1.wr]; exact rb) fun s2 u2 => ?_
  refine wp_dp (op2_reg _ _) fun s3 u3 => ?_
  refine wp_dp (op2_reg _ _) fun s4 u4 => ?_
  refine wp_dp (op2_imm (by decide)) fun s5 u5 => ?_
  refine wp_dp (op2_imm (by decide)) fun s6 u6 => ?_
  refine wp_subs (op2_imm (by decide)) fun t u7 z7 => WP.block_nil ?_
  refine ⟨u7.mem.trans (u6.mem.trans (u5.mem.trans (u4.mem.trans (u3.mem.trans (u2.mem.trans u1.mem))))),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u7.other .r0 (by decide), u6.other .r0 (by decide), u5.gpr, dpVal,
      u4.other .r0 (by decide), u3.other .r0 (by decide), u2.other .r0 (by decide), u1.other .r0 (by decide)]
  · rw [u7.other .r1 (by decide), u6.gpr, dpVal, u5.other .r1 (by decide),
      u4.other .r1 (by decide), u3.other .r1 (by decide), u2.other .r1 (by decide), u1.other .r1 (by decide)]
  · rw [u7.other .r2 (by decide), u6.other .r2 (by decide), u5.other .r2 (by decide), u4.gpr, dpVal,
      u3.other .r2 (by decide), u2.other .r2 (by decide), u1.other .r2 (by decide),
      u3.gpr, dpVal, u2.other .r3 (by decide), u1.gpr, u2.gpr, u1.mem]
  · rw [u7.gpr, u6.other .lr (by decide), u5.other .lr (by decide), u4.other .lr (by decide),
      u3.other .lr (by decide), u2.other .lr (by decide), u1.other .lr (by decide)]
  · rw [z7, u6.other .lr (by decide), u5.other .lr (by decide), u4.other .lr (by decide),
      u3.other .lr (by decide), u2.other .lr (by decide), u1.other .lr (by decide)]
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans (u7.rest (by decide)))))))
end VG.Proof.Bignum.Arm
end

end

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero)

structure WordCompareCtx (s : State) (a b : BitVec 32) (n : Nat) : Prop where
  countFits : n < 2 ^ 32
  readA : ∀ i < n, InRegions (s.rd ++ s.wr) (State.addr (a + BitVec.ofNat 32 (4 * i))) 4
  readB : ∀ i < n, InRegions (s.rd ++ s.wr) (State.addr (b + BitVec.ofNat 32 (4 * i))) 4

structure WordCompareInv (s0 : State) (a b : BitVec 32) (n i : Nat) (s : State) : Prop where
  index : i ≤ n
  first : s.gpr .r0 = a + BitVec.ofNat 32 (4 * i)
  second : s.gpr .r1 = b + BitVec.ofNat 32 (4 * i)
  count : s.gpr .lr = BitVec.ofNat 32 (n - i)
  equal : s.gpr .r2 = 0 ↔ ∀ j < i,
    s0.mem.readW (State.addr (a + BitVec.ofNat 32 (4 * j))) 32 = s0.mem.readW (State.addr (b + BitVec.ofNat 32 (4 * j))) 32
  mem : s.mem = s0.mem
  rest : Rest [.r0, .r1, .r2, .r3, .r12, .lr] s0 s

private theorem word_xor_zero32 (a b : BitVec 32) : a ^^^ b = 0 ↔ a = b :=
  BitVec.xor_eq_zero_iff

theorem compareWordBody_ok {s0 s : State} {a b : BitVec 32} {n i : Nat}
    (ctx : WordCompareCtx s0 a b n) (inv : WordCompareInv s0 a b n i s) (hi : i < n) :
    WP isa (.block compareWordStep) s fun t => WordCompareInv s0 a b n (i + 1) t ∧ t.z = decide (i + 1 = n) := by
  have ra := ctx.readA i hi
  have rb := ctx.readB i hi
  rw [← inv.rest.rd, ← inv.rest.wr] at ra rb
  refine WP.mono (compareWordStep_ok s _ _ (by rw [inv.first]; simp) (by rw [inv.second]; simp) ra rb) ?_
  rintro t ⟨mem, first, second, acc, count, zero, rest⟩
  refine ⟨⟨by omega_using [hi], ?_, ?_, ?_, ?_, mem.trans inv.mem, inv.rest.trans rest⟩, ?_⟩
  · rw [first, inv.first, BitVec.add_assoc]
    change a + (BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 4) = _
    rw [← BitVec.ofNat_add]
    rw [show 4 * i + 4 = 4 * (i + 1) by omega_using []]
  · rw [second, inv.second, BitVec.add_assoc]
    change b + (BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 4) = _
    rw [← BitVec.ofNat_add]
    rw [show 4 * i + 4 = 4 * (i + 1) by omega_using []]
  · rw [count, inv.count]
    change BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [hi])]
    congr 1
  · rw [acc, show (0 : BitVec 32) = 0#32 from rfl, BitVec.or_eq_zero_iff, ← show (0 : BitVec 32) = 0#32 from rfl,
      word_xor_zero32, inv.equal, inv.mem]
    constructor
    · rintro ⟨before, atI⟩ j hj
      by_cases eq : j = i
      · subst j; exact atI
      · exact before j (by omega_using [hj, eq])
    · intro all
      exact ⟨fun j hj => all j (by omega_using [hj]), all i (by omega_using [])⟩
  · rw [zero, inv.count]
    change (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [hi]), ofNat_beq_zero (by have := ctx.countFits; omega_using [this])]
    simp only [show n - i - 1 = 0 ↔ i + 1 = n by omega_using [hi]]

theorem compareWords_ok (s : State) {a b : BitVec 32} {n : Nat}
    (ctx : WordCompareCtx s a b n) (hn : 0 < n)
    (ha : s.gpr .r0 = a) (hb : s.gpr .r1 = b) (hc : s.gpr .lr = BitVec.ofNat 32 n) (hz : s.gpr .r2 = 0) :
    WP isa compareWords s (WordCompareInv s a b n n) := by
  let inv := fun k t => ∃ i, i + k = n ∧ 0 < k ∧ WordCompareInv s a b n i t
  unfold compareWords
  refine WP.loop (M := isa) inv ?_ n s ?_
  · intro k t h
    obtain ⟨i, hik, hk, hi⟩ := h
    refine WP.mono (compareWordBody_ok ctx hi (by omega_using [hik, hk])) ?_
    rintro u ⟨hu, zero⟩
    by_cases he : i + 1 = n
    · left
      refine ⟨?_, he ▸ hu⟩
      change some (!u.z) = some false
      simp only [zero, he, decide_true, Bool.not_true]
    · right
      refine ⟨?_, k - 1, by omega_using [hk], i + 1, by omega_using [hik, hk], by omega_using [hik, hk, he], hu⟩
      change some (!u.z) = some true
      simp only [zero, he, decide_false, Bool.not_false]
  · refine ⟨0, by omega_using [], hn, ?_⟩
    exact ⟨by omega_using [], by simpa using ha, by simpa using hb, by simpa using hc,
      by simp [hz], rfl, Rest.refl _ _⟩

end VG.Proof.Bignum.Arm

end

end

/-! ### `Bignum.WordEquality32`, which only this module used -/

section

/-! Equality of packed 32-bit integers is exactly equality of every limb. -/

@[expose] public section
namespace VG.Proof.Bignum
open VG VG.Proof.Mont

/-- Splitting off the low word preserves equality of arbitrary equal-width arrays. -/
theorem val32_eq_iff_words (m : Mem) (base : Addr) (da db n : Nat) :
    val32 m base da n = val32 m base db n ↔
      ∀ j < n, m.readW (off base (da + 4 * j)) 32 = m.readW (off base (db + 4 * j)) 32 := by
  induction n generalizing da db with
  | zero => simp [val32]
  | succ n ih =>
    have la := (m.readW (off base da) 32).isLt
    have lb := (m.readW (off base db) 32).isLt
    have split : val32 m base da (n + 1) = val32 m base db (n + 1) ↔
        w32 m base da = w32 m base db ∧ val32 m base (da + 4) n = val32 m base (db + 4) n := by
      simp only [val32]
      simp only [w32]
      omega_using []
    rw [split, ih]
    constructor
    · rintro ⟨head, tail⟩ j hj
      cases j with
      | zero => simpa only [Nat.mul_zero, Nat.add_zero] using BitVec.eq_of_toNat_eq head
      | succ j =>
        have eq := tail j (by omega_using [hj])
        simpa only [show da + 4 + 4 * j = da + 4 * (j + 1) by omega_using [],
          show db + 4 + 4 * j = db + 4 * (j + 1) by omega_using []] using eq
    · intro all
      refine ⟨?_, ?_⟩
      · have eq := congrArg BitVec.toNat (all 0 (by omega_using []))
        simpa only [Nat.mul_zero, Nat.add_zero] using eq
      · intro j hj
        have eq := all (j + 1) (by omega_using [hj])
        simpa only [show da + 4 * (j + 1) = da + 4 + 4 * j by omega_using [],
          show db + 4 * (j + 1) = db + 4 + 4 * j by omega_using []] using eq
end VG.Proof.Bignum

end

end


/-! Readable packed-array bounds and the comparison's integer interpretation. -/

@[expose] public section
namespace VG.Proof.Rsa.Arm.Keys
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Proof.Bignum.Arm

theorem Ws.compareAddress {s : State} {B : BitVec 32} {Z w N j i : Nat}
    (h : Ws s B Z w N) (hj : j < N) (hi : i < w) :
    State.addr ((B + BitVec.ofNat 32 (arr w j)) + BitVec.ofNat 32 (4 * i)) =
      off (State.addr B) (arr w j + 4 * i) := by
  rw [Offset.add_add]
  exact h.addr (by have := h.arr_fit hj; simp only [S] at this; omega_using [hi, this])

theorem Ws.compareCtx {s : State} {B : BitVec 32} {Z w N a b : Nat}
    (h : Ws s B Z w N) (ha : a < N) (hb : b < N) :
    WordCompareCtx s (B + BitVec.ofNat 32 (arr w a)) (B + BitVec.ofNat 32 (arr w b)) w := by
  refine ⟨by have := h.wle; omega_using [this], ?_, ?_⟩
  · intro i hi
    rw [h.compareAddress ha hi]
    exact h.read (by have := h.arr_fit ha; simp only [S] at this; omega_using [hi, this])
  · intro i hi
    rw [h.compareAddress hb hi]
    exact h.read (by have := h.arr_fit hb; simp only [S] at this; omega_using [hi, this])

theorem Ws.compareEqual {s : State} {B : BitVec 32} {Z w N a b : Nat} {m : Mem}
    (h : Ws s B Z w N) (ha : a < N) (hb : b < N) :
    (∀ i < w,
      m.readW (State.addr ((B + BitVec.ofNat 32 (arr w a)) + BitVec.ofNat 32 (4 * i))) 32 =
      m.readW (State.addr ((B + BitVec.ofNat 32 (arr w b)) + BitVec.ofNat 32 (4 * i))) 32) ↔
      num m B w a = num m B w b := by
  rw [num, num, VG.Proof.Bignum.val32_eq_iff_words]
  constructor
  · intro eq i hi
    have atI := eq i hi
    rwa [h.compareAddress ha hi, h.compareAddress hb hi] at atI
  · intro eq i hi
    rw [h.compareAddress ha hi, h.compareAddress hb hi]
    exact eq i hi

end VG.Proof.Rsa.Arm.Keys

end

end

/-! ### `Rsa.Arm.KeyEqNormalize`, which only this module used -/

section

/-! Normalize a full-word XOR/OR accumulator without branching on its value. -/

@[expose] public section
namespace VG.Proof.Rsa.Arm.Keys
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Proof.X25519.Arm

theorem eqNormalize_ok (s : State) :
    WP isa (.block eqNormalize) s fun t =>
      (t.gpr .r1 = (if s.gpr .r2 = 0 then 1 else 0) ∧ t.mem = s.mem) ∧ Rest [.r1] s t := by
  unfold eqNormalize
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => ?_
  refine wp_dp (op2_reg _ _) fun s2 u2 => ?_
  refine wp_dp (op2_reg _ _) fun s3 u3 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s4 u4 => ?_
  refine wp_dp (op2_imm (by decide)) fun t u5 => WP.block_nil ?_
  refine ⟨⟨?_, u5.mem.trans (u4.mem.trans (u3.mem.trans (u2.mem.trans u1.mem)))⟩,
    (u1.rest (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans
      ((u4.rest (by simp)).trans (u5.rest (by simp)))))⟩
  rw [u5.gpr, dpVal, u4.gpr, u3.gpr, dpVal, u2.gpr, dpVal, u1.gpr,
    u2.other .r2 (by decide), u1.other .r2 (by decide), VG.Proof.Rsa.zero_test32]
  by_cases h : s.gpr .r2 = 0
  · simp only [h, decide_true, ite_true]; rfl
  · simp only [h, decide_false, ite_false]; rfl

end VG.Proof.Rsa.Arm.Keys

end

end


/-! Compare packed arrays in one read-only pass, preserving the existing scratch contract. -/

@[expose] public section
namespace VG.Proof.Rsa.Arm.Keys
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm

alias borrow_iff := VG.Proof.Rsa.borrow_iff

theorem eqS_ok {s : State} {B : BitVec 32} {Z w N d a b t : Nat} (h : Ws s B Z w N)
    (_ht : t < N) (ha : a < N) (hb : b < N) (hN : N ≤ 256) (_hta : t ≠ a) (_htb : t ≠ b)
    (hd : d + 4 ≤ hdr) :
    WP isa (eqS d a b t) s fun u => Ws u B Z w N ∧ Keep B w [t] [sT, d] s.mem u.mem ∧
      slot u.mem B d = (if num s.mem B w a = num s.mem B w b then 1 else 0) ∧ Rest opRegs s u := by
  rw [eqS, WP.seq_iff]
  simp only [List.append_assoc]
  refine ptr_ok h (by decide) (by omega_using [ha, hN]) fun s1 first rest1 mem1 h1 => ?_
  refine ptr_ok h1 (by decide) (by omega_using [hb, hN]) fun s2 second rest2 mem2 h2 => ?_
  refine wp_mov (op2_reg _ _) fun s3 u3 => ?_
  have h3 := h2.of_upd u3 (by decide) (by decide) (by decide)
  refine wp_mov (op2_imm (by decide)) fun s4 u4 => WP.block_nil ?_
  have h4 := h3.of_upd u4 (by decide) (by decide) (by decide)
  have pa : s4.gpr .r0 = B + BitVec.ofNat 32 (arr w a) := by
    rw [u4.other .r0 (by decide), u3.other .r0 (by decide), rest2.gpr .r0 (by decide), first]
  have pb : s4.gpr .r1 = B + BitVec.ofNat 32 (arr w b) := by
    rw [u4.other .r1 (by decide), u3.other .r1 (by decide), second]
  have pc : s4.gpr .lr = BitVec.ofNat 32 w := by
    rw [u4.other .lr (by decide), u3.gpr, h2.r9]
  have pz : s4.gpr .r2 = 0 := u4.gpr
  have mem4 : s4.mem = s.mem := u4.mem.trans (u3.mem.trans (mem2.trans mem1))
  have rest4 : Rest opRegs s s4 :=
    (rest1.mono (by simp)).trans ((rest2.mono (by simp)).trans
      ((u3.rest (by simp)).trans (u4.rest (by simp))))
  refine WP.seq (WP.mono (compareWords_ok s4 (h4.compareCtx ha hb) h.wpos pa pb pc pz) ?_)
  intro u inv
  have hu := h4.rest inv.rest (by decide) (by decide) (by decide)
  have same : u.gpr .r2 = 0 ↔ num s.mem B w a = num s.mem B w b := by
    rw [inv.equal, mem4]
    exact h.compareEqual ha hb
  rw [WP.block_append_iff]
  refine WP.mono (eqNormalize_ok u) ?_
  rintro v ⟨⟨bit, memV⟩, restV⟩
  have hv := hu.rest restV (by decide) (by decide) (by decide)
  refine wp_strSlot hv hd fun out store => WP.block_nil ?_
  refine ⟨hv.of_mupd store, ?_, ?_, ?_⟩
  · rw [store.mem, memV, inv.mem, mem4]
    exact keep_write _ _ (by simp) (by simp only [hdr] at hd; omega_using [hd])
  · rw [store.mem, slot_write_self, bit]
    by_cases eq : num s.mem B w a = num s.mem B w b
    · rw [ite_eq_left (same.mpr eq), ite_eq_left eq]; rfl
    · rw [ite_eq_right (fun z => eq (same.mp z)), ite_eq_right eq]; rfl
  · exact rest4.trans ((inv.rest.mono (by simp [opRegs])).trans
      ((restV.mono (by simp [opRegs])).trans (store.rest _)))

end VG.Proof.Rsa.Arm.Keys
