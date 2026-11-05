module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.SearchInit
public import VerifiedGarbage.Spec.RsaKeyGen.GenerationContract
public import VerifiedGarbage.Proof.MlDsa.X86.Pack.Run
public import VerifiedGarbage.Proof.Framework.X86.ArgTaint
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Ffdh.X86.ParamInit
public import VerifiedGarbage.Proof.Ffdh.X86.KeyInit
public import VerifiedGarbage.Proof.RsaKeyGen.InitWords
import VerifiedGarbage.Proof.Framework.CountedLoop
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Impl.RsaKeyGen.X86.SearchInit
meta import VerifiedGarbage.Spec.RsaKeyGen.GenerationContract
meta import VerifiedGarbage.Proof.MlDsa.X86.Pack.Run
meta import VerifiedGarbage.Proof.Framework.X86.ArgTaint
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Ffdh.X86.ParamInit
meta import VerifiedGarbage.Proof.Ffdh.X86.KeyInit
meta import VerifiedGarbage.Proof.RsaKeyGen.InitWords
meta import VerifiedGarbage.Proof.Framework.CountedLoop
meta import VerifiedGarbage.Proof.Framework.Contract

/-! # `vg_rsa_prime_search_init` on i686

Its checks, the words of `primeInit` as halves (FFDH's `writes`,
`Proof/Ffdh/X86/ParamInit.lean`), `ebx` saved in the first and restored,
and `e`'s comparison with 3. Its timing depends only on the public
arguments, which its branches and its loop's count are: a taint check.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86.SearchInit

open VG VG.X86 VG.Proof.MlDsa.X86.Pack
open VG.Impl.RsaKeyGen.X86.SearchInit
open VG.Impl.Mont.X86 (at_)
open VG.Impl.Bignum.X86.PublicRt (argAt)


/-- What the function is given. -/
structure ABI (s : State) : Prop where
  stackBound : (s.gpr .esp).toNat + 4 + 16 ≤ 2 ^ 32
  rd : s.rd = [⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩, ⟨argAddr s 0, 16⟩]
  wr : s.wr = [⟨(arg s 0).setWidth 64, 32⟩]
  outE : (⟨(arg s 0).setWidth 64, 32⟩ : Region).Disjoint ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
  outArgs : (⟨(arg s 0).setWidth 64, 32⟩ : Region).Disjoint ⟨argAddr s 0, 16⟩
  retOut : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨(arg s 0).setWidth 64, 32⟩
  retE : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
  retArgs : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argAddr s 0, 16⟩
  outBound : (arg s 0).toNat + 32 ≤ 2 ^ 32
  eBound : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32

theorem abi_of {s : State} (h : (Spec.RsaKeyGen.primeInitContract abi).pre s) : ABI s := by
  sig_pre [Spec.RsaKeyGen.primeInitContract, Spec.RsaKeyGen.primeInitSig, abi, argSlots, argVal, argBytes,
    stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

theorem param_eq (i : Nat) : param i = at_ .esp (4 + 4 * i) := by
  simp only [param, argAt, Nat.mul_zero, Nat.add_zero]

theorem ea0 (s : State) : (s.gpr .esp + BitVec.ofNat 32 4).setWidth 64 = argAddr s 0 := rfl
theorem ea1 (s : State) : (s.gpr .esp + BitVec.ofNat 32 8).setWidth 64 = argAddr s 1 := rfl
theorem ea2 (s : State) : (s.gpr .esp + BitVec.ofNat 32 12).setWidth 64 = argAddr s 2 := rfl
theorem ea3 (s : State) : (s.gpr .esp + BitVec.ofNat 32 16).setWidth 64 = argAddr s 3 := rfl

theorem ABI.argIn {s : State} (A : ABI s) {i : Nat} (hi : i < 4) :
    (⟨argAddr s 0, 16⟩ : Region).Contains (argAddr s i) 4 := by
  have a0 : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 :=
    VG.Proof.MlKem.X86.ea_off (by have := A.stackBound; omega)
  have ai : argAddr s i = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) :=
    VG.Proof.MlKem.X86.ea_off (by have := A.stackBound; omega)
  rw [a0, ai]
  exact Offset.contains _ (by omega) (by omega) (by omega)

theorem ABI.argRd {s : State} (A : ABI s) {i : Nat} (hi : i < 4) : InRegions (s.rd ++ s.wr) (argAddr s i) 4 :=
  ⟨⟨argAddr s 0, 16⟩, by rw [A.rd]; simp, A.argIn hi⟩

/-! ## The checks -/

/-- A state of the checks: only the scratch registers changed. -/
def Same (s t : State) : Prop := Keep [.eax, .ecx, .edx] s t ∧ t.mem = s.mem

theorem Same.refl (s : State) : Same s s := ⟨Keep.refl _ _, rfl⟩

theorem Same.trans {s t u : State} (h : Same s t) (k : Keep [.eax, .ecx, .edx] t u) (hm : u.mem = t.mem) :
    Same s u := ⟨(h.1.trans k).mono (by simp), hm.trans h.2⟩

theorem Same.read {s t : State} (A : ABI s) (h : Same s t) {i : Nat} (hi : i < 4) :
    InRegions (t.rd ++ t.wr) (argAddr s i) 4 ∧ t.gpr .esp = s.gpr .esp ∧ t.mem.readW (argAddr s i) 32 = arg s i := by
  refine ⟨by rw [h.1.2.1, h.1.2.2]; exact A.argRd hi, h.1.gpr (by decide), by rw [h.2]; rfl⟩

theorem not_decide_lt (a b : Nat) : (!decide (a < b)) = decide (b ≤ a) := by
  by_cases h : a < b
  · rw [decide_eq_true h, decide_eq_false (by omega)]; rfl
  · rw [decide_eq_false h, decide_eq_true (by omega)]; rfl

theorem sub_beq32 (a b : BitVec 32) : (a - b == 0) = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  bv_omega

/-- A guard: its check leaves `R`, then zeros when `P` holds. -/
theorem guard_ok {check : List Instr} {cond : Cond} {rest : Prog isa} {t : State} {P : Prop}
    [Decidable P] {R Q : State → Prop}
    (hc : WP isa (.block check) t fun u => isa.eval cond u = some (decide P) ∧ R u)
    (hclear : ∀ u, P → R u → WP isa (.block clear) u Q)
    (hrest : ∀ u, ¬P → R u → WP isa rest u Q) :
    WP isa (Impl.RsaKeyGen.X86.SearchInit.guard check cond rest) t Q := by
  unfold Impl.RsaKeyGen.X86.SearchInit.guard
  refine WP.seq (WP.mono hc fun u ⟨he, k⟩ => ?_)
  exact WP.ite _ he (fun h => hclear u (of_decide_eq_true h) k) (fun h => hrest u (of_decide_eq_false h) k)

theorem checkLow_ok {s t : State} (A : ABI s) (h : Same s t) :
    WP isa (.block checkLow) t fun u =>
      (u.cf = some (decide ((arg s 1).toNat < 32)) ∧ u.gpr .ecx = arg s 1 ∧ u.mem = t.mem) ∧
        Keep [.eax, .ecx, .edx] t u := by
  obtain ⟨r1, sp, v1⟩ := h.read A (i := 1) (by decide)
  refine WP.keep _ ?_ (by rfl)
  simp only [checkLow, param_eq, Nat.reduceMul, Nat.reduceAdd]
  xrun [State.ea, at_, sp, ea1, r1, v1]
  all_goals rfl

theorem checkHigh_ok {s t : State} (hc : t.gpr .ecx = arg s 1) :
    WP isa (.block checkHigh) t fun u =>
      (u.cf = some (decide ((arg s 1).toNat < 513)) ∧ u.gpr .ecx = arg s 1 ∧ u.mem = t.mem) ∧
        Keep [.eax, .ecx, .edx] t u := by
  refine WP.keep _ ?_ (by rfl)
  unfold checkHigh
  xrun [hc]
  all_goals rfl

theorem and7 (x : BitVec 32) : (x &&& 7 == 0) = decide (x.toNat % 8 = 0) := by
  have h : (x &&& 7).toNat = x.toNat % 8 := by
    rw [BitVec.toNat_and, show (7 : BitVec 32).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, decide_eq_true_iff, ← h]
  exact ⟨fun e => by rw [e]; rfl, fun e => BitVec.eq_of_toNat_eq e⟩

theorem checkMod_ok {s t : State} (hc : t.gpr .ecx = arg s 1) :
    WP isa (.block checkMod) t fun u =>
      (u.zf = some (decide ((arg s 1).toNat % 8 = 0)) ∧ u.gpr .ecx = arg s 1 ∧ u.mem = t.mem) ∧
        Keep [.eax, .ecx, .edx] t u := by
  refine WP.keep _ ?_ (by rfl)
  unfold checkMod
  xrun [hc, and7]

theorem checkEmpty_ok {s t : State} (A : ABI s) (h : Same s t) :
    WP isa (.block checkEmpty) t fun u =>
      (u.cf = some (decide ((arg s 3).toNat < 1)) ∧ u.gpr .edx = arg s 3 ∧ u.mem = t.mem) ∧
        Keep [.edx] t u := by
  obtain ⟨r3, sp, v3⟩ := h.read A (i := 3) (by decide)
  refine WP.keep _ ?_ (by rfl)
  simp only [checkEmpty, param_eq, Nat.reduceMul, Nat.reduceAdd]
  xrun [State.ea, at_, sp, ea3, r3, v3]
  all_goals rfl

theorem checkLong_ok {s t : State} (hd : t.gpr .edx = arg s 3) :
    WP isa (.block checkLong) t fun u =>
      (u.cf = some (decide ((arg s 3).toNat < 9)) ∧ u.gpr .edx = arg s 3 ∧ u.mem = t.mem) ∧
        Keep [.edx] t u := by
  refine WP.keep _ ?_ (by rfl)
  unfold checkLong
  xrun [hd]
  all_goals rfl

/-! ## The words -/

open VG.Proof.Ffdh.X86.ParamInit (writes writes_frame words_halves halves zero_half writes_append)
open VG.Proof.Ffdh.X86.KeyInit (read_write_eq read_write_ne)

/-- The state's base address. -/
abbrev B (s : State) : Addr := (arg s 0).setWidth 64

/-- What a state's stores leave, for the state at `S`. -/
structure Stores (s : State) (S : BitVec 32) : Prop where
  fit : S.toNat + 32 ≤ 2 ^ 32
  wr : ⟨S.setWidth 64, 32⟩ ∈ s.wr

theorem Stores.ea {s : State} {S : BitVec 32} (h : Stores s S) {k : Nat} (hk : k < 32) :
    (S + BitVec.ofNat 32 k).setWidth 64 = S.setWidth 64 + BitVec.ofNat 64 k :=
  VG.Proof.MlKem.X86.ea_off (by have := h.fit; omega)

theorem Stores.inRW {s : State} {S : BitVec 32} (h : Stores s S) {k : Nat} (hk : k + 4 ≤ 32) :
    InRegions (s.rd ++ s.wr) (S.setWidth 64 + BitVec.ofNat 64 k) 4 :=
  ⟨_, List.mem_append_right _ h.wr, Offset.contains_base _ (by omega) (by omega)⟩

theorem Stores.inW {s : State} {S : BitVec 32} (h : Stores s S) {k : Nat} (hk : k + 4 ≤ 32) :
    InRegions s.wr (S.setWidth 64 + BitVec.ofNat 64 k) 4 :=
  ⟨_, h.wr, Offset.contains_base _ (by omega) (by omega)⟩

/-- The zeros of `clear`. -/
def zeros : List (Nat × BitVec 32) := [(0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (6, 0), (7, 0)]

theorem clear_ok {s t : State} (A : ABI s) (h : Same s t) :
    WP isa (.block clear) t fun u =>
      (u.gpr .eax = 0 ∧ u.mem = writes t.mem (B s) zeros) ∧ Keep [.eax, .ecx, .edx] t u := by
  obtain ⟨r0, sp, v0⟩ := h.read A (i := 0) (by decide)
  have W : Stores t (arg s 0) := ⟨A.outBound, by rw [h.1.2.2, A.wr]; exact List.mem_singleton_self _⟩
  refine WP.keep _ ?_ (by rfl)
  simp only [clear, st, param_eq, Nat.reduceMul, Nat.reduceAdd]
  xrun [State.ea, at_, sp, ea0, r0, v0, W.ea (k := 0) (by decide), W.ea (k := 4) (by decide),
    W.ea (k := 8) (by decide), W.ea (k := 12) (by decide), W.ea (k := 16) (by decide),
    W.ea (k := 20) (by decide), W.ea (k := 24) (by decide), W.ea (k := 28) (by decide),
    W.inW (k := 0) (by decide), W.inW (k := 4) (by decide), W.inW (k := 8) (by decide),
    W.inW (k := 12) (by decide), W.inW (k := 16) (by decide), W.inW (k := 20) (by decide),
    W.inW (k := 24) (by decide), W.inW (k := 28) (by decide)]
  simp only [writes, zeros, B, Nat.reduceMul]

/-- The words `words` stores: `ebx` saved in the first, then the others. -/
def rest (b : BitVec 32) (L : Nat) : List (Nat × BitVec 32) :=
  [(0, b), (1, 0), (3, 0), (5, 0), (7, 0), (2, BitVec.ofNat 32 L), (4, BitVec.ofNat 32 (32769 * L)),
    (6, BitVec.ofNat 32 (32 * L))]

theorem words_ok {s t : State} (A : ABI s) (h : Same s t) (hc : t.gpr .ecx = arg s 1) :
    WP isa (.block Impl.RsaKeyGen.X86.SearchInit.words) t fun u =>
      (u.mem = writes t.mem (B s) (rest (t.gpr .ebx) (arg s 1).toNat) ∧ u.gpr .ecx = arg s 1) ∧
        Keep [.eax, .ecx, .edx, .ebx] t u := by
  obtain ⟨r0, sp, v0⟩ := h.read A (i := 0) (by decide)
  have W : Stores t (arg s 0) := ⟨A.outBound, by rw [h.1.2.2, A.wr]; exact List.mem_singleton_self _⟩
  refine WP.keep _ ?_ (by rfl)
  simp only [Impl.RsaKeyGen.X86.SearchInit.words, st, stB, param_eq, Nat.reduceMul, Nat.reduceAdd]
  xrun [State.ea, at_, sp, ea0, r0, v0, hc, W.ea (k := 0) (by decide), W.ea (k := 4) (by decide),
    W.ea (k := 8) (by decide), W.ea (k := 12) (by decide), W.ea (k := 16) (by decide),
    W.ea (k := 20) (by decide), W.ea (k := 24) (by decide), W.ea (k := 28) (by decide),
    W.inW (k := 0) (by decide), W.inW (k := 4) (by decide), W.inW (k := 8) (by decide),
    W.inW (k := 12) (by decide), W.inW (k := 16) (by decide), W.inW (k := 20) (by decide),
    W.inW (k := 24) (by decide), W.inW (k := 28) (by decide), execMul]
  simp only [writes, rest, B, Nat.reduceMul, show (32769 : BitVec 32).toNat = 32769 from rfl,
    show (32 : BitVec 32).toNat = 32 from rfl, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-! ## Whether the exponent is 3 -/

open VG.Proof.RsaKeyGen.SearchInit (bytesAt_succ)

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

theorem sub_one32 {k : Nat} (h1 : 1 ≤ k) (hk : k < 2 ^ 32) :
    BitVec.ofNat 32 k - 1 = BitVec.ofNat 32 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  change (2 ^ 32 - 1 + k % 2 ^ 32) % 2 ^ 32 = (k - 1) % 2 ^ 32
  omega

theorem ofNat_beq {k : Nat} (hk : k < 2 ^ 32) : (BitVec.ofNat 32 k == 0) = decide (k = 0) := by
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h; have := congrArg BitVec.toNat h; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this; exact this
  · rintro rfl; rfl

theorem add_one32 (E : BitVec 32) (j : Nat) : E + BitVec.ofNat 32 j + 1 = E + BitVec.ofNat 32 (j + 1) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl

/-- After `j` of the `n` leading octets of `e` at `E`, in the memory `M`. -/
structure LeadInv (M : Mem) (E : BitVec 32) (n j : Nat) (v u : State) : Prop where
  ptr : u.gpr .ecx = E + BitVec.ofNat 32 j
  acc : u.gpr .eax = orOf32 (Spec.Rsa.bytesAt M (E.setWidth 64) j)
  count : u.gpr .edx = BitVec.ofNat 32 (n - j)
  z : u.zf = some (decide (n - j = 0))
  mem : u.mem = M
  keep : Keep [.eax, .ecx, .edx, .ebx] v u

theorem lead_step {v u : State} {M : Mem} {E : BitVec 32} {n j : Nat} (hj : j < n) (hn : n < 8)
    (fits : E.toNat + n < 2 ^ 32)
    (hrd : InRegions (v.rd ++ v.wr) (E.setWidth 64 + BitVec.ofNat 64 j) 1) (h : LeadInv M E n j v u) :
    WP isa (.block leadStep) u (LeadInv M E n (j + 1) v) := by
  have addr : (E + BitVec.ofNat 32 j + BitVec.ofNat 32 0).setWidth 64 = E.setWidth 64 + BitVec.ofNat 64 j := by
    rw [BitVec.add_zero]; exact VG.Proof.MlKem.X86.ea_off (by omega)
  have hr : InRegions (u.rd ++ u.wr) (E.setWidth 64 + BitVec.ofNat 64 j) 1 := by
    rw [h.keep.2.1, h.keep.2.2]; exact hrd
  refine WP.mono (WP.keep [.eax, .ecx, .edx, .ebx] (Q := fun t =>
      t.gpr .ecx = E + BitVec.ofNat 32 (j + 1) ∧
      t.gpr .eax = orOf32 (Spec.Rsa.bytesAt M (E.setWidth 64) j) ||| (u.mem (E.setWidth 64 + BitVec.ofNat 64 j)).setWidth 32 ∧
      t.gpr .edx = BitVec.ofNat 32 (n - (j + 1)) ∧ t.zf = some (decide (n - (j + 1) = 0)) ∧ t.mem = u.mem) ?_
    (by rfl)) fun t ⟨⟨h2, h1, h3, hz, hm⟩, k⟩ => ⟨h2, ?_, h3, hz, hm.trans h.mem, (h.keep.trans k).mono (by simp)⟩
  · unfold leadStep
    xrun [State.ea, at_, h.ptr, h.acc, h.count, addr, hr, add_one32,
      sub_one32 (k := n - j) (by omega) (by omega), show n - j - 1 = n - (j + 1) by omega,
      ofNat_beq (k := n - (j + 1)) (by omega)]
  · rw [h1, bytesAt_succ, orOf32_snoc, h.mem]

theorem lead_loop {v u : State} {M : Mem} {E : BitVec 32} {n : Nat} (h1 : 1 ≤ n) (hn : n < 8)
    (fits : E.toNat + n < 2 ^ 32)
    (hrd : ∀ j < n, InRegions (v.rd ++ v.wr) (E.setWidth 64 + BitVec.ofNat 64 j) 1) (h : LeadInv M E n 0 v u) :
    WP isa (.loop (.block leadStep) .ne) u (LeadInv M E n n v) := by
  refine WP.mono (WP.chunk_loop (I := fun j t => LeadInv M E n j v t) (n := n) (N := 1) (k := 0) (by decide)
    (by omega) h (fun j t hj ht => lead_step (by omega) hn fits (hrd j (by omega)) ht)
    (fun j t _ ht => ?_)) fun t ⟨j, hj, hl, ht⟩ => by
      obtain rfl : j = n := by omega
      exact ht
  have e : isa.eval .ne t = some (!decide (n - j = 0)) := by
    change t.zf.map (!·) = _; rw [ht.z]; rfl
  rw [e]
  constructor
  · intro hl; rw [decide_eq_true (by omega)]; rfl
  · intro hl; rw [decide_eq_false (by omega)]; rfl

theorem isThree_ok {s v : State} (A : ABI s) (sp : v.gpr .esp = s.gpr .esp)
    (r2 : InRegions (v.rd ++ v.wr) (argAddr s 2) 4) (r3 : InRegions (v.rd ++ v.wr) (argAddr s 3) 4)
    (v2 : v.mem.readW (argAddr s 2) 32 = arg s 2) (v3 : v.mem.readW (argAddr s 3) 32 = arg s 3)
    (h1 : 1 ≤ (arg s 3).toNat) (h8 : (arg s 3).toNat ≤ 8)
    (hrd : ∀ i < (arg s 3).toNat, InRegions (v.rd ++ v.wr) ((arg s 2).setWidth 64 + BitVec.ofNat 64 i) 1) :
    WP isa isThree v fun t =>
      (t.gpr .eax = 0 ↔ Spec.Rsa.os2ip (Spec.Rsa.bytesAt v.mem ((arg s 2).setWidth 64) (arg s 3).toNat) = 3) ∧
        t.mem = v.mem ∧ Keep [.eax, .ecx, .edx, .ebx] v t := by
  have fits := A.eBound
  have n3 : arg s 3 = BitVec.ofNat 32 (arg s 3).toNat := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  unfold isThree
  refine WP.seq (WP.mono (WP.keep [.eax, .ecx, .edx, .ebx] (Q := fun t =>
      t.gpr .ecx = arg s 2 ∧ t.gpr .eax = 0 ∧ t.gpr .edx = BitVec.ofNat 32 ((arg s 3).toNat - 1) ∧
        t.zf = some (decide ((arg s 3).toNat - 1 = 0)) ∧ t.mem = v.mem) ?_ (by rfl))
    fun t ⟨⟨hc, ha, hd, hz, hm⟩, k⟩ => ?_)
  · simp only [param_eq, Nat.reduceMul, Nat.reduceAdd]
    rw [n3] at v3
    xrun [State.ea, at_, sp, ea2, ea3, r2, r3, v2, v3, sub_one32 h1 (by omega),
      ofNat_beq (k := (arg s 3).toNat - 1) (by omega)]
  have h0 : LeadInv v.mem (arg s 2) ((arg s 3).toNat - 1) 0 v t :=
    ⟨by rw [hc, BitVec.add_zero], by rw [ha]; rfl, hd, hz, hm, k⟩
  have hloop : WP isa (.ite .e (.block []) (.loop (.block leadStep) .ne)) t
      (LeadInv v.mem (arg s 2) ((arg s 3).toNat - 1) ((arg s 3).toNat - 1) v) := by
    refine WP.ite _ hz (fun hz' => ?_) (fun hz' => ?_)
    · have hz' : (arg s 3).toNat - 1 = 0 := of_decide_eq_true hz'
      exact WP.block_nil (by rw [hz'] at h0 ⊢; exact h0)
    · have hz' : (arg s 3).toNat - 1 ≠ 0 := of_decide_eq_false hz'
      exact lead_loop (by omega) (by omega) (by omega) (fun j hj => hrd j (by omega)) h0
  refine WP.seq (WP.mono hloop fun u hu => ?_)
  have addr : (arg s 2 + BitVec.ofNat 32 ((arg s 3).toNat - 1) + BitVec.ofNat 32 0).setWidth 64 =
      (arg s 2).setWidth 64 + BitVec.ofNat 64 ((arg s 3).toNat - 1) := by
    rw [BitVec.add_zero]; exact VG.Proof.MlKem.X86.ea_off (by omega)
  have hr : InRegions (u.rd ++ u.wr) ((arg s 2).setWidth 64 + BitVec.ofNat 64 ((arg s 3).toNat - 1)) 1 := by
    rw [hu.keep.2.1, hu.keep.2.2]; exact hrd _ (by omega)
  refine WP.mono (WP.keep [.eax, .ecx, .edx, .ebx] (Q := fun t => t.gpr .eax =
      orOf32 (Spec.Rsa.bytesAt v.mem ((arg s 2).setWidth 64) ((arg s 3).toNat - 1)) |||
        ((u.mem ((arg s 2).setWidth 64 + BitVec.ofNat 64 ((arg s 3).toNat - 1))).setWidth 32 ^^^ 3) ∧
      t.mem = u.mem) ?_ (by rfl)) fun t ⟨⟨h9, hmt⟩, kt⟩ =>
    ⟨?_, hmt.trans hu.mem, (hu.keep.trans kt).mono (by simp)⟩
  · xrun [State.ea, at_, hu.ptr, hu.acc, addr, hr]
  · have hb : Spec.Rsa.bytesAt v.mem ((arg s 2).setWidth 64) (arg s 3).toNat =
        Spec.Rsa.bytesAt v.mem ((arg s 2).setWidth 64) ((arg s 3).toNat - 1) ++
          [v.mem ((arg s 2).setWidth 64 + BitVec.ofNat 64 ((arg s 3).toNat - 1))] := by
      rw [← bytesAt_succ, Nat.sub_add_cancel h1]
    rw [h9, hu.mem, hb, three32]

/-! ## The first word -/

/-- The first word, for a width `L` and whether `e` is 3. -/
def limitOf (L : Nat) (three : Bool) : Nat := if three then 64 * L else 40 * L

theorem first_value (L : Nat) (x : BitVec 32) :
    BitVec.ofNat 32 (40 * L) +
        ((0#32 - BitVec.setWidth 32 (BitVec.ofBool (decide (x.toNat < 1)))) &&& BitVec.ofNat 32 (24 * L)) =
      BitVec.ofNat 32 (limitOf L (x == 0)) := by
  unfold limitOf
  by_cases hx : x = 0
  · subst hx
    simp only [show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_lt_one, decide_true, beq_self_eq_true,
      ite_true]
    rw [show (0#32 - BitVec.setWidth 32 (BitVec.ofBool true)) = BitVec.allOnes 32 from rfl,
      BitVec.allOnes_and, ← BitVec.ofNat_add]
    congr 1; omega
  · have h1 : ¬ x.toNat < 1 := fun h => hx (BitVec.eq_of_toNat_eq (by rw [show (0 : BitVec 32).toNat = 0 from rfl]; omega))
    rw [decide_eq_false h1, beq_eq_false_iff_ne.mpr hx]
    simp only [Bool.false_eq_true, ite_false]
    rw [show (0#32 - BitVec.setWidth 32 (BitVec.ofBool false)) = 0#32 from rfl, BitVec.zero_and,
      BitVec.add_zero]

theorem first_ok {s z : State} (sp : z.gpr .esp = s.gpr .esp)
    (r0 : InRegions (z.rd ++ z.wr) (argAddr s 0) 4) (r1 : InRegions (z.rd ++ z.wr) (argAddr s 1) 4)
    (v0 : z.mem.readW (argAddr s 0) 32 = arg s 0) (v1 : z.mem.readW (argAddr s 1) 32 = arg s 1)
    (W : Stores z (arg s 0)) {b : BitVec 32} (vb : z.mem.readW (B s + BitVec.ofNat 64 0) 32 = b) :
    WP isa (.block first) z fun t =>
      (t.gpr .eax = 1 ∧ t.gpr .ebx = b ∧
        t.mem = writes z.mem (B s) [(0, BitVec.ofNat 32 (limitOf (arg s 1).toNat (z.gpr .eax == 0)))]) ∧
        Keep [.eax, .ecx, .edx, .ebx] z t := by
  refine WP.keep _ ?_ (by rfl)
  simp only [first, limit, st, param_eq, Nat.reduceMul, Nat.reduceAdd, List.cons_append, List.nil_append]
  xrun [State.ea, at_, sp, ea0, ea1, r0, r1, v0, v1, W.ea (k := 0) (by decide), W.inW (k := 0) (by decide),
    W.inRW (k := 0) (by decide), execMul, vb, show (24 : BitVec 32).toNat = 24 from rfl,
    show (40 : BitVec 32).toNat = 40 from rfl, show (1 : BitVec 32).toNat = 1 from rfl, first_value _]
  simp only [writes, B, Nat.reduceMul]

/-! ## The whole initialization -/

open VG.Proof.RsaKeyGen.SearchInit (initValid primeInit_eq)

theorem writes_frame32 (m : Mem) (B : Addr) :
    ∀ l : List (Nat × BitVec 32), (∀ p ∈ l, p.1 < 8) → Frame [⟨B, 32⟩] m (writes m B l)
  | [] , _ => Frame.refl _ _
  | (j, v) :: l, h => by
    have hj : j < 8 := h (j, v) (List.mem_cons_self ..)
    exact ((Frame.refl [⟨B, 32⟩] m).writeW (List.mem_singleton_self _) v
      (Offset.contains_base B (by omega) (by omega))).trans
      (writes_frame32 _ B l fun p hp => h p (List.mem_cons_of_mem _ hp))

theorem rest_lt (b : BitVec 32) (L : Nat) : ∀ p ∈ rest b L, p.1 < 8 := by
  simp only [rest, List.mem_cons, List.not_mem_nil, or_false]
  rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

/-- What the function leaves: the scratch registers and `ebx` aside, its
state; `ebx` restored; the status and the words. -/
def InitPost (s t : State) : Prop :=
  Keep [.eax, .ecx, .edx, .ebx] s t ∧ t.gpr .ebx = s.gpr .ebx ∧
    if initValid (arg s 1).toNat (arg s 3).toNat then
      t.gpr .eax = 1 ∧ t.mem = writes (writes s.mem (B s) (rest (s.gpr .ebx) (arg s 1).toNat)) (B s)
        [(0, BitVec.ofNat 32 (limitOf (arg s 1).toNat
          (decide (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat) = 3))))]
    else t.gpr .eax = 0 ∧ t.mem = writes s.mem (B s) zeros

theorem init_ok {s : State} (A : ABI s) : WP isa init s (InitPost s) := by
  have clear_post : ∀ t, Same s t → ¬ initValid (arg s 1).toNat (arg s 3).toNat →
      WP isa (.block clear) t (InitPost s) := by
    intro t h hv
    refine WP.mono (clear_ok A h) fun u ⟨⟨h0, hmu⟩, k⟩ => ⟨(h.1.trans k).mono (by simp), ?_, ?_⟩
    · rw [k.gpr (by decide), h.1.gpr (by decide)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hv)]
      exact ⟨h0, by rw [hmu, h.2]⟩
  unfold init
  -- `prime_len < 32`
  refine guard_ok (P := (arg s 1).toNat < 32) (R := fun u => Same s u ∧ u.gpr .ecx = arg s 1)
    (WP.mono (checkLow_ok A (Same.refl s)) fun u ⟨⟨hc, he, hm⟩, k⟩ => ⟨hc, (Same.refl s).trans k hm, he⟩)
    (fun t hb h => clear_post t h.1 (by unfold initValid; omega)) fun t₁ hb₁ ⟨h₁, c₁⟩ => ?_
  -- `512 < prime_len`
  refine guard_ok (P := 513 ≤ (arg s 1).toNat) (R := fun u => Same s u ∧ u.gpr .ecx = arg s 1)
    (WP.mono (checkHigh_ok c₁) fun u ⟨⟨hc, he, hm⟩, k⟩ => ⟨by
      change u.cf.map (!·) = _; rw [hc, Option.map_some, not_decide_lt], h₁.trans k hm, he⟩)
    (fun t hb h => clear_post t h.1 (by unfold initValid; omega)) fun t₂ hb₂ ⟨h₂, c₂⟩ => ?_
  -- `prime_len % 8 ≠ 0`
  refine guard_ok (P := (arg s 1).toNat % 8 ≠ 0) (R := fun u => Same s u ∧ u.gpr .ecx = arg s 1)
    (WP.mono (checkMod_ok c₂) fun u ⟨⟨hz, he, hm⟩, k⟩ => ⟨by
      change u.zf.map (!·) = _; rw [hz, Option.map_some, decide_not], h₂.trans k hm, he⟩)
    (fun t hb h => clear_post t h.1 (by unfold initValid; omega)) fun t₃ hb₃ ⟨h₃, c₃⟩ => ?_
  -- `e_len = 0`
  refine guard_ok (P := (arg s 3).toNat < 1)
    (R := fun u => Same s u ∧ u.gpr .ecx = arg s 1 ∧ u.gpr .edx = arg s 3)
    (WP.mono (checkEmpty_ok A h₃) fun u ⟨⟨hc, he, hm⟩, k⟩ => ⟨hc, h₃.trans (k.mono (by simp)) hm,
      by rw [k.gpr (by decide), c₃], he⟩)
    (fun t hb h => clear_post t h.1 (by unfold initValid; omega)) fun t₄ hb₄ ⟨h₄, c₄, d₄⟩ => ?_
  -- `8 < e_len`
  refine guard_ok (P := 9 ≤ (arg s 3).toNat) (R := fun u => Same s u ∧ u.gpr .ecx = arg s 1)
    (WP.mono (checkLong_ok d₄) fun u ⟨⟨hc, he, hm⟩, k⟩ => ⟨by
      change u.cf.map (!·) = _; rw [hc, Option.map_some, not_decide_lt], h₄.trans (k.mono (by simp)) hm,
      by rw [k.gpr (by decide), c₄]⟩)
    (fun t hb h => clear_post t h.1 (by unfold initValid; omega)) fun t₅ hb₅ ⟨h₅, c₅⟩ => ?_
  have hv : initValid (arg s 1).toNat (arg s 3).toNat := by unfold initValid; omega
  obtain ⟨_, hL, _, h1, h8⟩ := hv
  have b5 : t₅.gpr .ebx = s.gpr .ebx := h₅.1.gpr (by decide)
  have m5 : t₅.mem = s.mem := h₅.2
  have R (l : List (Nat × BitVec 32)) (hl : ∀ p ∈ l, p.1 < 8) {i : Nat} (hi : i < 4) :
      (writes s.mem (B s) l).readW (argAddr s i) 32 = arg s i :=
    (writes_frame32 _ _ l hl).readW (A.argIn hi) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr; exact A.outArgs.symm) (by decide)
  unfold valid
  refine WP.seq (WP.mono (words_ok A h₅ c₅) fun u ⟨⟨hmu, cu⟩, ku⟩ => ?_)
  rw [m5, b5] at hmu
  have spu : u.gpr .esp = s.gpr .esp := (ku.gpr (by decide)).trans (h₅.1.gpr (by decide))
  have rdu : u.rd = s.rd := ku.2.1.trans h₅.1.2.1
  have wru : u.wr = s.wr := ku.2.2.trans h₅.1.2.2
  have hreads : ∀ i < (arg s 3).toNat, InRegions (u.rd ++ u.wr) ((arg s 2).setWidth 64 + BitVec.ofNat 64 i) 1 :=
    fun i hi => ⟨_, by rw [rdu, A.rd]; exact List.mem_append_left _ (List.mem_cons_self ..),
      Offset.contains_base _ (by have := A.eBound; omega) (by omega)⟩
  refine WP.seq (WP.mono (isThree_ok A spu (by rw [rdu, wru]; exact A.argRd (by decide))
    (by rw [rdu, wru]; exact A.argRd (by decide)) (by rw [hmu]; exact R _ (rest_lt _ _) (by decide))
    (by rw [hmu]; exact R _ (rest_lt _ _) (by decide)) h1 h8 hreads) fun z ⟨hzi, hmz, kz⟩ => ?_)
  have spz : z.gpr .esp = s.gpr .esp := (kz.gpr (by decide)).trans spu
  have rdz : z.rd = s.rd := kz.2.1.trans rdu
  have wrz : z.wr = s.wr := kz.2.2.trans wru
  have W : Stores z (arg s 0) := ⟨A.outBound, by rw [wrz, A.wr]; exact List.mem_singleton_self _⟩
  have vb : z.mem.readW (B s + BitVec.ofNat 64 0) 32 = s.gpr .ebx := by
    rw [hmz, hmu]
    have := (show (writes s.mem (B s) (rest (s.gpr .ebx) (arg s 1).toNat)).readW (B s + BitVec.ofNat 64 (4 * 0)) 32 =
        s.gpr .ebx by
      simp (disch := decide) only [rest, writes, read_write_eq, read_write_ne])
    simpa only [Nat.mul_zero] using this
  refine WP.mono (first_ok spz (by rw [rdz, wrz]; exact A.argRd (by decide)) (by rw [rdz, wrz]; exact A.argRd (by decide))
    (by rw [hmz, hmu]; exact R _ (rest_lt _ _) (by decide)) (by rw [hmz, hmu]; exact R _ (rest_lt _ _) (by decide))
    W vb) fun t ⟨⟨ht, hbt, hmt⟩, kt⟩ => ?_
  have three : (z.gpr .eax == 0) = decide (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem ((arg s 2).setWidth 64)
      (arg s 3).toNat) = 3) := by
    have e : Spec.Rsa.bytesAt u.mem ((arg s 2).setWidth 64) (arg s 3).toNat =
        Spec.Rsa.bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat := by
      rw [hmu]
      simp only [Spec.Rsa.bytesAt]
      refine List.map_congr_left fun i hi => ?_
      exact (writes_frame32 _ _ _ (rest_lt _ _)).bytes (R := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩)
        (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact A.outE.symm) (by change (arg s 3).toNat ≤ 2 ^ 64; omega)
        (List.mem_range.mp hi)
    rw [← e]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    exact hzi
  refine ⟨(((h₅.1.trans ku).trans kz).trans kt).mono (by simp), hbt, ?_⟩
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, hL, by omega, h1, h8⟩)]
  refine ⟨ht, ?_⟩
  rw [hmt, hmz, hmu, three]

/-! ## The contract -/

theorem zeros_words (m : Mem) (B : Addr) :
    Spec.Rsa.wordsAt (writes m B zeros) B 4 = List.replicate 4 0 := by
  rw [words_halves]
  simp (disch := decide) only [zeros, writes, read_write_eq, read_write_ne]
  rfl

theorem valid_words (m : Mem) (B : Addr) (b : BitVec 32) (L : Nat) (hL : L ≤ 512) (three : Bool) :
    Spec.Rsa.wordsAt (writes (writes m B (rest b L)) B [(0, BitVec.ofNat 32 (limitOf L three))]) B 4 =
      [BitVec.ofNat 64 (limitOf L three), BitVec.ofNat 64 L, BitVec.ofNat 64 (32769 * L),
        BitVec.ofNat 64 (32 * L)] := by
  have hlim : limitOf L three ≤ 64 * 512 := by unfold limitOf; split <;> omega
  rw [words_halves]
  simp (disch := decide) only [rest, writes, read_write_eq, read_write_ne]
  rw [show (0 : BitVec 32) = 0#32 from rfl, zero_half (by omega), zero_half (by omega), zero_half (by omega),
    zero_half (by omega)]

theorem post_frame {s t : State} (h : InitPost s t) : Frame [⟨B s, 32⟩] s.mem t.mem := by
  obtain ⟨-, -, h⟩ := h
  split at h
  · rw [h.2, ← writes_append]
    refine writes_frame32 _ _ _ fun p hp => ?_
    rcases List.mem_append.mp hp with hp | hp
    · exact rest_lt _ _ p hp
    · obtain rfl := List.mem_singleton.mp hp; dsimp only; decide
  · rw [h.2]
    refine writes_frame32 _ _ _ fun p hp => ?_
    simp only [zeros, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem correct (s : State) (h : (Spec.RsaKeyGen.primeInitContract abi).pre s) :
    ∃ trace t, Exec isa init s trace t ∧ abiPreserved s t ∧ (Spec.RsaKeyGen.primeInitContract abi).post s t := by
  have A := abi_of h
  obtain ⟨tr, t, E, P⟩ := init_ok A
  refine ⟨tr, t, E, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · by_cases hb : r = .ebx
    · subst hb; exact P.2.1
    · exact P.1.gpr (by revert r; decide)
  · exact (post_frame P).readW (Region.contains_self _ _) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr; exact A.retOut) (by decide)
  · sig_post [Spec.RsaKeyGen.primeInitContract, Spec.RsaKeyGen.primeInitSig, abi, argSlots, argVal, argBytes]
    rw [BitVec.setWidth_append_eq_right]
    have hl : (Spec.Rsa.bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat).length = (arg s 3).toNat := by
      simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
    obtain ⟨-, -, P⟩ := P
    rw [primeInit_eq, hl]
    split at P
    · rename_i hv
      rw [ite_eq_left_of_eq_true _ _ (eq_true hv)]
      refine ⟨by rw [P.1]; rfl, ?_⟩
      rw [P.2, valid_words _ _ _ _ hv.2.1]
      simp only [limitOf, decide_eq_true_eq, List.map_cons, List.map_nil]
    · rename_i hv
      rw [ite_eq_right_of_eq_false _ _ (eq_false hv)]
      exact ⟨by rw [P.1]; rfl, by rw [P.2, zeros_words]⟩

theorem args_out {s : State} (A : ABI s) : ArgsOut 4 s := by
  refine ⟨A.stackBound, fun r hr => ?_⟩
  rw [A.wr] at hr
  obtain rfl := List.mem_singleton.mp hr
  intro a ha hb
  let j := (a - (s.gpr .esp).setWidth 64).toNat
  have hj : j < 20 := by change j + 1 ≤ 20 at ha; omega
  have he : (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 j = a := by
    change (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (a - (s.gpr .esp).setWidth 64).toNat = a
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  have a0 : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 :=
    VG.Proof.MlKem.X86.ea_off (by have := A.stackBound; omega)
  by_cases h : j < 4
  · exact A.retOut a (by rw [← he]; exact Offset.contains_base _ (by omega) (by omega)) hb
  · exact A.outArgs a hb (by rw [a0, ← he]; exact Offset.contains _ (by omega) (by omega) (by decide))

theorem constantTime : ConstantTime isa (Spec.RsaKeyGen.primeInitContract abi).pre
    (Spec.RsaKeyGen.primeInitContract abi).pub init := by
  refine VG.Taint.constantTime (A := VG.X86.taint) (argTaint [] 20) ?_ (by taint_decide)
  intro s t hs ht H
  sig_pub [Spec.RsaKeyGen.primeInitContract, Spec.RsaKeyGen.primeInitSig, abi, argSlots, argVal, argBytes] at H
  obtain ⟨SP, -, a0, a1, a2, a3⟩ := H
  refine agree_argTaint (k := 4) (fun _ h => nomatch h) SP (args_out (abi_of hs)) (args_out (abi_of ht)) ?_
  intro i hi
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
  exacts [a0, a1, a2, a3]

/-- The state at `0x1000`, 64 octets and `e = 3` (three octets) at `0x2000`, the arguments at `0x4004`. -/
def satState : State where
  gpr r := if r = .esp then 0x4000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x4005 then 0x10 else if a = 0x4008 then 0x40 else if a = 0x400D then 0x20 else
    if a = 0x4010 then 3 else 0
  rd := [⟨0x2000, 3⟩, ⟨0x4004, 16⟩]
  wr := [⟨0x1000, 32⟩]

theorem satisfiable : ∃ s, (Spec.RsaKeyGen.primeInitContract abi).pre s := by
  have a0 : arg satState 0 = 0x1000 := by decide
  have a2 : arg satState 2 = 0x2000 := by decide
  have a3 : arg satState 3 = 3 := by decide
  have e : argAddr satState 0 = 0x4004 := by decide
  have esp : satState.gpr .esp = 0x4000 := rfl
  sig_implies_sat [Spec.RsaKeyGen.primeInitContract, Spec.RsaKeyGen.primeInitSig, abi, argSlots, argVal,
    argBytes, stackBelow] [a0, a2, a3, e, esp, satState] using satState

theorem init_verified : Verified target init (Spec.RsaKeyGen.primeInitContract abi) :=
  ⟨correct, constantTime, satisfiable⟩

end VG.Proof.RsaKeyGen.X86.SearchInit
