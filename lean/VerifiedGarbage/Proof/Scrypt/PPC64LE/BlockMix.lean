module

public import VerifiedGarbage.Proof.Scrypt.BlockMix
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Scrypt.Memory
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Scrypt.BlockMix
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Call
meta import VerifiedGarbage.Proof.Scrypt.Memory
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sha256.Stream
public import VerifiedGarbage.Impl.Scrypt.PPC64LE.Salsa
public import VerifiedGarbage.Proof.Scrypt.Spec
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Spec.Scrypt.Contract
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Impl.Scrypt.PPC64LE.Salsa
meta import VerifiedGarbage.Proof.Scrypt.Spec
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Spec.Scrypt.Contract
import all Init.Data.Nat.Power2.Basic
public import VerifiedGarbage.Proof.MdStream.PPC64LE.Basic
public import VerifiedGarbage.Impl.Scrypt.PPC64LE.BlockMix
meta import VerifiedGarbage.Proof.MdStream.PPC64LE.Basic
meta import VerifiedGarbage.Impl.Scrypt.PPC64LE.BlockMix

/-! ### `Scrypt.PPC64LE.Common`, which this module and modules that import it used -/

section

/-!
# scrypt on PPC64LE: common lemmas

The target-independent lemmas about addresses and bytes are in
`Proof/Scrypt/Memory.lean`; here are the contracts of the proofs, and the
64-byte exclusive-or.
-/

@[expose] public section

namespace VG.Proof.Scrypt

open Spec.Scrypt

open VG.PPC64LE in
/-- PPC64LE contract for `vg_scrypt_blockmix(b = r3, r = r4, y = r5, ry = r6,
scratch = r7)`: if `ry = r > 0`, writes scryptBlockMix of the `128 r` bytes at
`b` to `y`. Its frame (saving the link register) is the 48 bytes below the
stack pointer. -/
def blockMixPPC64LE : Contract PPC64LE.isa where
  pre s :=
    let r := (s.gpr .r4).toNat
    let b : Region := ⟨s.gpr .r3, r * 128⟩
    let y : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat * 128⟩
    let scratch : Region := ⟨s.gpr .r7, 128⟩
    let stack : Region := ⟨s.sp - 48, 48⟩
    s.rd = [b] ∧ s.wr = [y, scratch] ∧
    y.Disjoint scratch ∧ b.Disjoint y ∧ b.Disjoint scratch ∧
    48 ≤ s.sp.toNat ∧ stack.Disjoint b ∧ stack.Disjoint y ∧ stack.Disjoint scratch ∧
    (s.gpr .r3).toNat + r * 128 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + (s.gpr .r6).toNat * 128 ≤ 2 ^ 64 ∧
    (s.gpr .r7).toNat + 128 ≤ 2 ^ 64 ∧
    s.gpr .r6 = s.gpr .r4 ∧ 0 < r
  post s s' := let r := (s.gpr .r4).toNat
    bytesAt s'.mem (s.gpr .r5) (128 * r) = blockMix r (bytesAt s.mem (s.gpr .r3) (128 * r))
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.sp = s₂.sp

open VG.PPC64LE in
/-- PPC64LE contract for `vg_scrypt_romix(b = r3, r = r4, v = r5, vlen = r6,
scratch = r7, slen = r8)`: if `r > 0`, `vlen = N r` for a power of two `N`,
and `slen = r + 2`, replaces the `128 r` bytes at `b` by their scryptROMix. It
has no frame (it saves its return address in `scratch`); its calls of
`vg_scrypt_blockmix` use the 48 bytes below the stack pointer. The indices
`j` of step 3 are public. -/
def roMixPPC64LE : Contract PPC64LE.isa where
  pre s :=
    let r := (s.gpr .r4).toNat
    let b : Region := ⟨s.gpr .r3, r * 128⟩
    let v : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat * 128⟩
    let scratch : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat * 128⟩
    let stack : Region := ⟨s.sp - 48, 48⟩
    s.rd = [] ∧ s.wr = [b, v, scratch] ∧
    b.Disjoint v ∧ b.Disjoint scratch ∧ v.Disjoint scratch ∧
    48 ≤ s.sp.toNat ∧ stack.Disjoint b ∧ stack.Disjoint v ∧ stack.Disjoint scratch ∧
    (s.gpr .r3).toNat + r * 128 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + (s.gpr .r6).toNat * 128 ≤ 2 ^ 64 ∧
    (s.gpr .r7).toNat + (s.gpr .r8).toNat * 128 ≤ 2 ^ 64 ∧
    0 < r ∧ (s.gpr .r6).toNat % r = 0 ∧ ((s.gpr .r6).toNat / r).isPowerOfTwo ∧
    (s.gpr .r8).toNat = r + 2
  post s s' := let r := (s.gpr .r4).toNat
    bytesAt s'.mem (s.gpr .r3) (128 * r) =
      roMix r ((s.gpr .r6).toNat / r) (bytesAt s.mem (s.gpr .r3) (128 * r))
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.sp = s₂.sp ∧
    roMixIndices (s₁.gpr .r4).toNat ((s₁.gpr .r6).toNat / (s₁.gpr .r4).toNat)
        (bytesAt s₁.mem (s₁.gpr .r3) (128 * (s₁.gpr .r4).toNat)) =
      roMixIndices (s₂.gpr .r4).toNat ((s₂.gpr .r6).toNat / (s₂.gpr .r4).toNat)
        (bytesAt s₂.mem (s₂.gpr .r3) (128 * (s₂.gpr .r4).toNat))

end VG.Proof.Scrypt

namespace VG.Proof.Scrypt.PPC64LE.BlockMix

open VG VG.PPC64LE VG.Impl.Scrypt.PPC64LE
open VG.Spec.Scrypt (bytesAt)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_append writeBytes_nil)
open VG.Proof.MdStream.PPC64LE (Upd Mupd wp_ld wp_std)
open VG.Proof.Scrypt.Memory (sub_off writeW_xor xorBytes_length bytesAt_length
  bytesAt_add bytesAt_writeBytes_sep)

theorem wp_xor {is : List Instr} {s : State} {Q : State → Prop} {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .xor d n m :: is)) s Q :=
  Proof.MdStream.PPC64LE.WP.cons exec_logic (k _ (Upd.write _ _ _))

/-- The first `n` doublewords of `[dst] ← [x] xor [src]`, for 64-byte blocks
`d`, `x`, `y` in memory, where `d` overlaps neither of the others. The code
uses `r9` and `r10`. -/
theorem xor64_ok {dR xR sR : Reg} (hd : dR ≠ .r9 ∧ dR ≠ .r10 ∧ dR ≠ .r0)
    (hx : xR ≠ .r9 ∧ xR ≠ .r10 ∧ xR ≠ .r0) (hs : sR ≠ .r9 ∧ sR ≠ .r10 ∧ sR ≠ .r0)
    {d x y : Addr} (hdx : Region.Disjoint ⟨d, 64⟩ ⟨x, 64⟩) (hdy : Region.Disjoint ⟨d, 64⟩ ⟨y, 64⟩) :
    ∀ n ≤ 8, ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    s.gpr dR = d → s.gpr xR = x → s.gpr sR = y →
    (∀ k < 8, InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 (8 * k)) 8) →
    (∀ k < 8, InRegions (s.rd ++ s.wr) (y + BitVec.ofNat 64 (8 * k)) 8) →
    (∀ k < 8, InRegions s.wr (d + BitVec.ofNat 64 (8 * k)) 8) →
    (∀ s', (∀ r, r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp →
      s'.mem = writeBytes s.mem d (xorBytes (bytesAt s.mem x (8 * n)) (bytesAt s.mem y (8 * n))) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap (xorW dR xR sR) ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro _ rest s Q _ _ _ _ _ _ k
    exact k s (fun _ _ _ => rfl) rfl rfl rfl (by simp [bytesAt, xorBytes, writeBytes_nil])
  | succ n ih =>
    intro hn rest s Q gd gx gy hinx hiny hout k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih (by omega_using [hn]) _ s Q gd gx gy hinx hiny hout fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [xorW, List.cons_append, List.nil_append]
    refine wp_ld (a := x + BitVec.ofNat 64 (8 * n)) ⟨by omega_using [hn], by omega_using []⟩
      (by rw [g₁ _ hx.1 hx.2.1, gx]) (by rw [rd₁, wr₁]; exact hinx n (by omega_using [hn])) (fun s₂ u₂ => ?_)
      hx.2.2
    refine wp_ld (a := y + BitVec.ofNat 64 (8 * n)) ⟨by omega_using [hn], by omega_using []⟩
      (by rw [u₂.other _ hs.1, g₁ _ hs.1 hs.2.1, gy])
      (by rw [u₂.rd, u₂.wr, rd₁, wr₁]; exact hiny n (by omega_using [hn])) (fun s₃ u₃ => ?_) hs.2.2
    refine wp_xor fun s₄ u₄ => ?_
    refine wp_std (a := d + BitVec.ofNat 64 (8 * n)) ⟨by omega_using [hn], by omega_using []⟩
      (by rw [u₄.other _ hd.1, u₃.other _ hd.2.1, u₂.other _ hd.1, g₁ _ hd.1 hd.2.1, gd])
      (by rw [u₄.wr, u₃.wr, u₂.wr, wr₁]; exact hout n (by omega_using [hn]))
      (fun s₅ u₅ => k s₅ (fun r h9 h10 => by
          rw [u₅.gpr, u₄.other r h9, u₃.other r h10, u₂.other r h9, g₁ r h9 h10])
        (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁])
        (by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]) ?_) hd.2.2
    have hl : (xorBytes (bytesAt s.mem x (8 * n)) (bytesAt s.mem y (8 * n))).length = 8 * n := by
      rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
    have sx : Region.Disjoint ⟨x + BitVec.ofNat 64 (8 * n), 8⟩ ⟨d, (xorBytes (bytesAt s.mem x (8 * n))
        (bytesAt s.mem y (8 * n))).length⟩ := by
      rw [hl]; exact (hdx.symm.sub_left (sub_off (by omega_using [hn]) (by omega_using [hn]))).sub_right
        (Region.sub_prefix (by omega_using [hn]))
    have sy : Region.Disjoint ⟨y + BitVec.ofNat 64 (8 * n), 8⟩ ⟨d, (xorBytes (bytesAt s.mem x (8 * n))
        (bytesAt s.mem y (8 * n))).length⟩ := by
      rw [hl]; exact (hdy.symm.sub_left (sub_off (by omega_using [hn]) (by omega_using [hn]))).sub_right
        (Region.sub_prefix (by omega_using [hn]))
    rw [u₅.mem, u₄.gpr, u₄.mem, u₃.gpr, u₃.other _ (by decide), u₂.gpr, u₃.mem, u₂.mem, writeW_xor,
      m₁, bytesAt_writeBytes_sep _ _ sx (by omega_using []), bytesAt_writeBytes_sep _ _ sy (by omega_using [])]
    have e := writeBytes_append s.mem d _ (xorBytes (bytesAt s.mem (x + BitVec.ofNat 64 (8 * n)) 8)
      (bytesAt s.mem (y + BitVec.ofNat 64 (8 * n)) 8))
      (by rw [hl, xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]; omega_using [hn])
    rw [hl] at e
    rw [e, Nat.mul_succ, bytesAt_add, bytesAt_add, xorBytes, xorBytes, xorBytes,
      List.zipWith_append (by simp [bytesAt])]

end VG.Proof.Scrypt.PPC64LE.BlockMix

end

end

/-! ### `Scrypt.PPC64LE.Salsa`, which only this module used -/

section

/-!
# The Salsa20/8 Core on PPC64LE

The rounds on the low words of the registers (`RI`), then the whole function
(`correct`, and `salsa_correct` from the contract's precondition).
-/

@[expose] public section

namespace VG.Proof.Scrypt.PPC64LE

open VG VG.PPC64LE VG.Impl.Scrypt.PPC64LE
open VG.Spec.Scrypt (Word)
open VG.Proof.Scrypt

/-! ## Registers -/

theorem wreg_inj {j k : Nat} (hj : j < 16) (hk : k < 16) (h : wreg j = wreg k) : j = k := by
  have key : ∀ j, j < 16 → ∀ k, k < 16 → wreg j = wreg k → j = k := by decide
  exact key j hj k hk h

theorem wreg_ne_r0 {k : Nat} (hk : k < 16) : wreg k ≠ .r0 := by
  have key : ∀ k < 16, wreg k ≠ .r0 := by decide
  exact key k hk

/-- The registers that hold words. -/
def Words (r : Reg) : Prop := ∃ k < 16, r = wreg k

theorem not_words_r3 : ¬ Words .r3 := fun ⟨k, hk, h⟩ => by
  have key : ∀ k < 16, wreg k ≠ .r3 := by decide
  exact key k hk h.symm

theorem not_words_r4 : ¬ Words .r4 := fun ⟨k, hk, h⟩ => by
  have key : ∀ k < 16, wreg k ≠ .r4 := by decide
  exact key k hk h.symm

theorem saved_words {i : Nat} (hi : i < 8) : Words (saved i) := by
  have key : ∀ i < 8, saved i = wreg (i + 8) := by decide
  exact ⟨i + 8, by omega_arith, key i hi⟩

theorem saved_inj {i j : Nat} (hi : i < 8) (hj : j < 8) (h : saved i = saved j) : i = j := by
  have key : ∀ i < 8, ∀ j < 8, saved i = saved j → i = j := by decide
  exact key i hi j hj h

theorem saved_ne_r4 {i : Nat} (hi : i < 8) : saved i ≠ .r4 := by
  have key : ∀ i < 8, saved i ≠ .r4 := by decide
  exact key i hi

/-- A preserved register is saved, or not a word register (nor `r0`). -/
theorem preserved_cases {r : Reg} (hr : r ∈ preserved) :
    (∃ i < 8, r = saved i) ∨ (¬ Words r ∧ r ≠ .r0) := by
  have key : ∀ r ∈ preserved, (∃ i < 8, r = saved i) ∨ (∀ k < 16, r ≠ wreg k) ∧ r ≠ .r0 := by
    decide
  rcases key r hr with h | ⟨h, h0⟩
  · exact .inl h
  · exact .inr ⟨fun ⟨k, hk, e⟩ => h k hk e, h0⟩

/-! ## One line, on registers -/

/-- `a ^= R(b + c)` through `r0`, rotating right by `sh`, on the low words. -/
theorem line_regs {a b c : Reg} (ha : a ≠ .r0) {sh : Nat} (hsh : sh < 32) (s : State) (va vb vc : Word)
    (hva : (s.gpr a).setWidth 32 = va) (hvb : (s.gpr b).setWidth 32 = vb)
    (hvc : (s.gpr c).setWidth 32 = vc) :
    WP isa (.block [.add .r0 b c, .rotr .w .r0 .r0 sh, .logic .xor a a .r0]) s fun s' =>
      (s'.gpr a).setWidth 32 = va ^^^ (vb + vc).rotateRight sh ∧
      (∀ r, r ≠ a → r ≠ .r0 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_add, exec_logic, exec_rotr_w hsh, isa,
    State.write, ha, Option.some.injEq, exists_eq_left', ↓reduceIte]
  simp only [lo32_add, BitVec.setWidth_xor, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    hva, hvb, hvc, Nat.reduceLeDiff]
  refine ⟨trivial, fun r h1 h2 => ?_, trivial, trivial, trivial⟩
  simp only [h1, h2, ite_false]

/-! ## Where the words are -/

/-- The words `v` are in the low words of the registers. -/
def Holds (v : Vector Word 16) (s : State) : Prop :=
  ∀ k (hk : k < 16), (s.gpr (wreg k)).setWidth 32 = v[k]

/-- The rounds invariant, relative to the state `s₀` at the start of the rounds. -/
structure RI (v : Vector Word 16) (s₀ s : State) : Prop where
  holds : Holds v s
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, ¬ Words r → r ≠ .r0 → s.gpr r = s₀.gpr r

/-- The side conditions of `line_ok`, decidable for concrete arguments. -/
def LSide (i j k n : Nat) : Bool :=
  decide (i < 16 ∧ j < 16 ∧ k < 16 ∧ 1 ≤ n ∧ n ≤ 31)

theorem line_ok {i j k n : Nat} (hs : LSide i j k n = true) {v : Vector Word 16} {s₀ s : State}
    (h : RI v s₀ s) : WP isa (.block (line i j k n)) s (RI (stepN v i j k n) s₀) := by
  simp only [LSide, decide_eq_true_eq] at hs
  obtain ⟨hi, hj, hk, h1, h2⟩ := hs
  have ne : ∀ {a b}, a < 16 → b < 16 → a ≠ b → wreg a ≠ wreg b := fun ha hb hab e =>
    hab (wreg_inj ha hb e)
  refine WP.mono (line_regs (wreg_ne_r0 hi) (show 32 - n < 32 by omega_arith) s _ _ _ (h.holds i hi)
    (h.holds j hj) (h.holds k hk)) fun s' ⟨ha, hr, hm, hrd, hwr⟩ =>
    ⟨fun m hm' => ?_, hm.trans h.mem, hrd.trans h.rd, hwr.trans h.wr, fun r hw hx => ?_⟩
  · rw [stepN_get v n hi hj hk m hm']
    by_cases e : i = m
    · subst e
      simp only [ite_true]
      rw [ha, rotateLeft_eq _ (by omega_arith) (by omega_arith)]
    · simp only [e, ite_false]
      rw [hr _ (ne hm' hi (Ne.symm e)) (wreg_ne_r0 hm')]
      exact h.holds m hm'
  · rw [hr r (fun e => hw ⟨i, hi, e⟩) hx]
    exact h.keep r hw hx

/-! ## Double rounds -/

theorem lines_ok {s₀ : State} :
    ∀ (l : List (Nat × Nat × Nat × Nat)), (l.all fun (i, j, k, n) => LSide i j k n) = true →
      ∀ (v : Vector Word 16) (s : State), RI v s₀ s →
      WP isa (.block (l.flatMap fun (i, j, k, n) => line i j k n)) s
        (RI (l.foldl (fun x (i, j, k, n) => stepN x i j k n) v) s₀)
  | [], _, _, _, h => WP.block_nil h
  | (i, j, k, n) :: l, hl, v, s, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hl
    rw [List.flatMap_cons, WP.block_append_iff, List.foldl_cons]
    exact WP.mono (line_ok hl.1 h) fun s' h' => lines_ok l hl.2 _ s' h'

theorem doubleRound_eq (v : Vector Word 16) : Spec.Scrypt.doubleRound v =
    lines.foldl (fun x (i, j, k, n) => stepN x i j k n) v := rfl

theorem doubleRound_ok {v : Vector Word 16} {s₀ s : State} (h : RI v s₀ s) :
    WP isa doubleRound s (RI (Spec.Scrypt.doubleRound v) s₀) := by
  rw [doubleRound_eq]
  exact lines_ok lines (by decide) v s h

theorem rounds_ok {v : Vector Word 16} {s₀ : State} (h : Holds v s₀) :
    ∀ n, WP isa (rounds n) s₀ (RI (Nat.repeat Spec.Scrypt.doubleRound n v) s₀)
  | 0 => WP.block_nil ⟨h, rfl, rfl, rfl, fun _ _ _ => rfl⟩
  | n + 1 => WP.seq (WP.mono (rounds_ok h n) fun _ h' => doubleRound_ok h')

end VG.Proof.Scrypt.PPC64LE

namespace VG.Proof.Scrypt

open Spec.Scrypt

open VG.PPC64LE in
/-- PPC64LE contract for `vg_salsa20_8(b: *mut [u8; 64], scratch: *mut [u32;
16])`: replaces the 64 bytes at `b` by their Salsa20/8 Core.

The code may read and write `b` and `scratch` (64 bytes each; the contents of
`scratch` on exit are unspecified), which may not overlap. The pointers are
public; the data is secret. -/
def salsaPPC64LE : Contract PPC64LE.isa where
  pre s :=
    let b : Region := ⟨s.gpr .r3, 64⟩
    let scratch : Region := ⟨s.gpr .r4, 64⟩
    s.rd = [] ∧ s.wr = [b, scratch] ∧ b.Disjoint scratch
  post s s' := bytesAt s'.mem (s.gpr .r3) 64 = salsa (bytesAt s.mem (s.gpr .r3) 64)
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.sp = s₂.sp

end VG.Proof.Scrypt

namespace VG.Proof.Scrypt.PPC64LE

open VG VG.PPC64LE VG.Impl.Scrypt.PPC64LE
open VG.Spec.Scrypt (Word)
open VG.Proof.Scrypt

/-! ## The precondition -/

section
variable (s₀ : State)
/-- `b`. -/
abbrev bp : Addr := s₀.gpr .r3
/-- `scratch`. -/
abbrev sp' : Addr := s₀.gpr .r4
abbrev bR : Region := ⟨bp s₀, 64⟩
abbrev sR : Region := ⟨sp' s₀, 64⟩
/-- The input words. -/
def V : Vector Word 16 := Vector.ofFn fun j => s₀.mem.readW (bp s₀ + BitVec.ofNat 64 (4 * j.1)) 32
/-- The result of the rounds. -/
abbrev Rs : Vector Word 16 := Nat.repeat Spec.Scrypt.doubleRound 4 (V s₀)
end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [bR s₀, sR s₀]
  disj : (bR s₀).Disjoint (sR s₀)

theorem pre_of (s₀ : State) (h : Proof.Scrypt.salsaPPC64LE.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, h3⟩

theorem V_get (s₀ : State) {k : Nat} (hk : k < 16) :
    (V s₀)[k] = s₀.mem.readW (bp s₀ + BitVec.ofNat 64 (4 * k)) 32 := by
  simp only [V, Vector.getElem_ofFn]

theorem contains_off {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem in_b {k : Nat} (hk : k < 16) (rs : List Region) :
    InRegions (rs ++ s₀.wr) (bp s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨bR s₀, by simp [hp.wr], contains_off (by omega_arith) (by omega_arith)⟩

theorem out_b {k : Nat} (hk : k < 16) : InRegions s₀.wr (bp s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨bR s₀, by simp [hp.wr], contains_off (by omega_arith) (by omega_arith)⟩

theorem in_sav {i : Nat} (hi : i < 8) (rs : List Region) :
    InRegions (rs ++ s₀.wr) (sp' s₀ + BitVec.ofNat 64 (8 * i)) 8 :=
  ⟨sR s₀, by simp [hp.wr], contains_off (by omega_arith) (by omega_arith)⟩

theorem out_sav {i : Nat} (hi : i < 8) : InRegions s₀.wr (sp' s₀ + BitVec.ofNat 64 (8 * i)) 8 :=
  ⟨sR s₀, by simp [hp.wr], contains_off (by omega_arith) (by omega_arith)⟩

end Pre

theorem readW_writeW_word (m : Mem) (p : Addr) (v : Word) {j k : Nat} (hj : j < 16) (hk : k < 16)
    (h : j ≠ k) :
    (m.writeW (p + BitVec.ofNat 64 (4 * k)) v).readW (p + BitVec.ofNat 64 (4 * j)) 32 =
      m.readW (p + BitVec.ofNat 64 (4 * j)) 32 :=
  Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)

theorem sav_sep (p : Addr) {i j : Nat} (hi : i < 8) (hj : j < 8) (h : i ≠ j) :
    Mem.Sep (p + BitVec.ofNat 64 (8 * i)) 8 (p + BitVec.ofNat 64 (8 * j)) 8 :=
  Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)

/-! ## Saving the nonvolatile registers -/

/-- The first `n` registers are saved. -/
structure SI (s₀ : State) (n : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [sR s₀] s₀.mem s.mem
  saved : ∀ i < n, s.mem.readW (sp' s₀ + BitVec.ofNat 64 (8 * i)) 64 = s₀.gpr (saved i)

theorem save_step {s₀ : State} (hp : Pre s₀) {n : Nat} (hn : n < 8) {s : State} (h : SI s₀ n s) :
    WP isa (.block [.store .d (saved n) .r4 (8 * n)]) s (SI s₀ (n + 1)) := by
  have hr4 : s.gpr .r4 = sp' s₀ := by rw [h.gpr]
  have hout : InRegions s.wr (s.gpr .r4 + BitVec.ofNat 64 (8 * n)) 8 := by
    rw [h.wr, hr4]; exact hp.out_sav hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_store_d (by decide) (show 8 * n < 2 ^ 15 ∧ (8 * n) % 4 = 0 by omega_arith) hout,
    Option.some.injEq, exists_eq_left', hr4]
  refine ⟨h.gpr, h.rd, h.wr, h.frame.writeW (List.mem_singleton_self _) _
    (contains_off (by omega_arith) (by omega_arith)), fun i hi => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · rw [Mem.readW_writeW_sep (sav_sep _ (by omega_arith) hn (by omega_arith)) (by decide)]
    exact h.saved i hi
  · rw [Mem.readW_writeW_self64, h.gpr]

/-! ## Loading the input -/

/-- After loading `n` words. -/
structure LI (s₀ : State) (n : Nat) (s : State) : Prop where
  loaded : ∀ j (hj : j < 16), j < n → (s.gpr (wreg j)).setWidth 32 = (V s₀)[j]
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, ¬ Words r → s.gpr r = s₀.gpr r

theorem load_step {s₀ : State} (hp : Pre s₀) {n : Nat} (hn : n < 16) {s : State} (h : LI s₀ n s) :
    WP isa (.block [.load .w (wreg n) .r3 (4 * n)]) s (LI s₀ (n + 1)) := by
  have hr3 : s.gpr .r3 = bp s₀ := h.keep _ not_words_r3
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 (4 * n)) 4 := by
    rw [h.rd, h.wr, hr3]; exact hp.in_b hn _
  have hv : s.mem.readW (bp s₀ + BitVec.ofNat 64 (4 * n)) 32 = (V s₀)[n] := by
    rw [h.mem, V_get _ hn]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_w (by decide) (show 4 * n < 2 ^ 15 by omega_arith) hin, isa,
    Option.some.injEq, exists_eq_left', hr3, hv]
  refine ⟨fun j hj hjn => ?_, h.mem, h.rd, h.wr, fun r hr => ?_⟩
  · simp only [State.write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hjn with hjn | rfl
    · have e : wreg j ≠ wreg n := fun e => absurd (wreg_inj hj hn e) (by omega_arith)
      simp only [e, ite_false]; exact h.loaded j hj hjn
    · simp
  · have e : r ≠ wreg n := fun e => hr ⟨n, hn, e⟩
    simp only [State.write, e, ite_false]; exact h.keep r hr

/-! ## Adding the input -/

/-- After finishing words `0 … i - 1`: those words of `b` hold the sums, the
others still hold the input, and words `i … 15` of the rounds' result `R` are
still in their registers. -/
structure FI (s₀ : State) (R : Vector Word 16) (i : Nat) (s : State) : Prop where
  out : ∀ j (hj : j < 16), s.mem.readW (bp s₀ + BitVec.ofNat 64 (4 * j)) 32 =
    if j < i then R[j] + (V s₀)[j] else (V s₀)[j]
  rest : ∀ j (hj : j < 16), i ≤ j → (s.gpr (wreg j)).setWidth 32 = R[j]
  frame : Frame [bR s₀] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, ¬ Words r → r ≠ .r0 → s.gpr r = s₀.gpr r

theorem finish_step {s₀ : State} (hp : Pre s₀) {R : Vector Word 16} {i : Nat} (hi : i < 16)
    {s : State} (h : FI s₀ R i s) : WP isa (.block (finishWord i)) s (FI s₀ R (i + 1)) := by
  have hr3 : s.gpr .r3 = bp s₀ := h.keep _ not_words_r3 (by decide)
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 (4 * i)) 4 := by
    rw [h.rd, h.wr, hr3]; exact hp.in_b hi _
  have hout : InRegions s.wr (s.gpr .r3 + BitVec.ofNat 64 (4 * i)) 4 := by
    rw [h.wr, hr3]; exact hp.out_b hi
  have hv : s.mem.readW (bp s₀ + BitVec.ofNat 64 (4 * i)) 32 = (V s₀)[i] := by
    rw [h.out i hi, ite_eq_right_iff.mpr fun h => absurd h (Nat.lt_irrefl i)]
  have hr := h.rest i hi (Nat.le_refl i)
  have hne : wreg i ≠ .r0 := wreg_ne_r0 hi
  have n3 : Reg.r3 ≠ wreg i := fun e => not_words_r3 ⟨i, hi, e⟩
  have n30 : Reg.r3 ≠ .r0 := by decide
  apply WP.of_runBlock
  simp only [finishWord, runBlock_cons, runStep_some,
    exec_load_w (by decide) (show 4 * i < 2 ^ 15 by omega_arith) hin, exec_add, isa, hr3, hv]
  simp only [State.write, hne, ite_false, ite_true]
  rw [exec_store_w (by decide) (show 4 * i < 2 ^ 15 by omega_arith)
    (by simpa [State.write, hne, n3, n30] using hout)]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left', ite_true, ite_false,
    hr3, n3, n30]
  refine ⟨fun j hj => ?_, fun j hj hij => ?_,
    h.frame.writeW (List.mem_singleton_self _) _ (contains_off (by omega_arith) (by omega_arith)),
    h.rd, h.wr, fun r hw hx => ?_⟩
  · by_cases e : j = i
    · subst e
      rw [Mem.readW_writeW_self32, lo32_add, hr, lo32_ext,
        ite_eq_left_iff.mpr fun h => absurd (Nat.lt_succ_self j) h]
    · rw [readW_writeW_word _ _ _ hj hi e, h.out j hj]
      by_cases hji : j < i
      · rw [ite_eq_left_iff.mpr fun h => absurd hji h, ite_eq_left_iff.mpr fun h => absurd (by omega_arith) h]
      · rw [ite_eq_right_iff.mpr fun h => absurd h hji, ite_eq_right_iff.mpr fun h => absurd h (by omega_arith)]
  · have e1 : wreg j ≠ wreg i := fun e => absurd (wreg_inj hj hi e) (by omega_arith)
    have e2 : wreg j ≠ .r0 := wreg_ne_r0 hj
    simp only [e1, e2, ite_false]; exact h.rest j hj (by omega_arith)
  · have e1 : r ≠ wreg i := fun e => hw ⟨i, hi, e⟩
    simp only [e1, hx, ite_false]; exact h.keep r hw hx

/-! ## Restoring the nonvolatile registers -/

/-- The first `n` registers are restored, from the state `sB` the restoring
starts in. -/
structure RI' (s₀ sB : State) (n : Nat) (s : State) : Prop where
  restored : ∀ i < n, s.gpr (saved i) = s₀.gpr (saved i)
  others : ∀ r, (∀ i < 8, r ≠ saved i) → s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem restore_step {s₀ sB : State} (hp : Pre s₀) (hr4 : sB.gpr .r4 = sp' s₀)
    (hsav : ∀ i < 8, sB.mem.readW (sp' s₀ + BitVec.ofNat 64 (8 * i)) 64 = s₀.gpr (saved i))
    {n : Nat} (hn : n < 8) {s : State} (h : RI' s₀ sB n s) :
    WP isa (.block [.load .d (saved n) .r4 (8 * n)]) s (RI' s₀ sB (n + 1)) := by
  have hr4' : s.gpr .r4 = sp' s₀ := by
    rw [h.others _ fun i hi e => saved_ne_r4 hi e.symm, hr4]
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r4 + BitVec.ofNat 64 (8 * n)) 8 := by
    rw [h.rd, h.wr, hr4']; exact hp.in_sav hn _
  have hv : s.mem.readW (sp' s₀ + BitVec.ofNat 64 (8 * n)) 64 = s₀.gpr (saved n) := by
    rw [h.mem]; exact hsav n hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (by decide) (show 8 * n < 2 ^ 15 ∧ (8 * n) % 4 = 0 by omega_arith) hin,
    Option.some.injEq, exists_eq_left', hr4', hv]
  refine ⟨fun i hi => ?_, fun r hr => ?_, h.mem, h.rd, h.wr⟩
  · simp only [State.write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have e : saved i ≠ saved n := fun e => absurd (saved_inj (by omega_arith) hn e) (by omega_arith)
      simp only [e, ite_false]; exact h.restored i hi
    · simp
  · simp only [State.write, hr n hn, ite_false]; exact h.others r hr

/-! ## The whole function -/

/-- The input words are those the specification reads from the bytes. -/
theorem input_eq (s₀ : State) :
    (Vector.ofFn fun j : Fin 16 => Spec.Scrypt.wordLE (Spec.Scrypt.bytesAt s₀.mem (bp s₀) 64) j.1) =
      V s₀ := by
  apply Vector.ext
  intro j hj
  rw [Vector.getElem_ofFn, V_get _ hj, wordLE_bytesAt _ _ (by omega_arith)]

/-- The result words are where the specification writes its bytes. -/
theorem post_of {s₀ : State} {m : Mem}
    (h : ∀ j (hj : j < 16), m.readW (bp s₀ + BitVec.ofNat 64 (4 * j)) 32 = (Rs s₀)[j] + (V s₀)[j]) :
    Spec.Scrypt.bytesAt m (bp s₀) 64 = Spec.Scrypt.salsa (Spec.Scrypt.bytesAt s₀.mem (bp s₀) 64) := by
  rw [Spec.Scrypt.salsa, input_eq]
  refine bytesAt_eq_serialize _ _ _ fun j hj => ?_
  rw [Spec.Scrypt.core, Vector.getElem_zipWith, ← h j hj]

/-- The main part, from the state `s₁` after saving the registers. -/
theorem main_ok {s₁ : State} (hp : Pre s₁) :
    WP isa main s₁ fun s' =>
      (∀ j (hj : j < 16), s'.mem.readW (bp s₁ + BitVec.ofNat 64 (4 * j)) 32 = (Rs s₁)[j] + (V s₁)[j]) ∧
      Frame [bR s₁] s₁.mem s'.mem ∧ s'.rd = s₁.rd ∧ s'.wr = s₁.wr ∧
      (∀ r, ¬ Words r → r ≠ .r0 → s'.gpr r = s₁.gpr r) := by
  have hl₀ : LI s₁ 0 s₁ := ⟨fun _ _ h => absurd h (by omega_arith), rfl, rfl, rfl, fun _ _ => rfl⟩
  have hload : WP isa (.block load) s₁ (LI s₁ 16) := by
    unfold load
    exact wp_range_flatMap (M := isa) (LI s₁) (fun k s hk h => load_step hp hk h) 16 (Nat.le_refl _) s₁ hl₀
  refine WP.seq (WP.mono hload fun s₂ h₂ => ?_)
  have hh₂ : Holds (V s₁) s₂ := fun k hk => h₂.loaded k hk hk
  refine WP.seq (WP.mono (rounds_ok hh₂ 4) fun s₃ h₃ => ?_)
  have hf₃ : FI s₁ (Rs s₁) 0 s₃ :=
    ⟨fun j hj => by
        rw [ite_eq_right_iff.mpr fun h => absurd h (Nat.not_lt_zero j), h₃.mem, h₂.mem, V_get _ hj],
      fun j hj _ => h₃.holds j hj, by rw [h₃.mem, h₂.mem]; exact Frame.refl _ _,
      h₃.rd.trans h₂.rd, h₃.wr.trans h₂.wr,
      fun r hw hx => (h₃.keep r hw hx).trans (h₂.keep r hw)⟩
  unfold finish
  exact WP.mono (wp_range_flatMap (M := isa) (FI s₁ (Rs s₁)) (fun i s hi h => finish_step hp hi h) 16
    (Nat.le_refl _) s₃ hf₃) fun s' h => ⟨fun j hj => by rw [h.out j hj, ite_eq_left_iff.mpr fun e => absurd hj e],
      h.frame, h.rd, h.wr, h.keep⟩

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa salsa s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Scrypt.salsaPPC64LE.post s₀ s' := by
  have hs₀ : SI s₀ 0 s₀ := ⟨rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega_arith)⟩
  have hsave : WP isa (.block save) s₀ (SI s₀ 8) := by
    unfold save
    exact wp_range_flatMap (M := isa) (SI s₀) (fun k s hk h => save_step hp hk h) 8 (Nat.le_refl _) s₀ hs₀
  refine WP.seq (WP.mono hsave fun s₁ h₁ => ?_)
  have hb : bp s₁ = bp s₀ := by simp only [bp, h₁.gpr]
  have hs : sp' s₁ = sp' s₀ := by simp only [sp', h₁.gpr]
  have hp₁ : Pre s₁ := ⟨by rw [h₁.rd, hp.rd], by rw [h₁.wr, hp.wr, bR, bR, sR, sR, hb, hs],
    by simpa only [bR, sR, hb, hs] using hp.disj⟩
  have hV : V s₁ = V s₀ := by
    apply Vector.ext
    intro j hj
    rw [V_get _ hj, V_get _ hj, hb]
    exact h₁.frame.readW (r := bR s₀) (contains_off (by omega_arith) (by omega_arith))
      (by simpa using hp.disj) (by decide)
  refine WP.seq (WP.mono (main_ok hp₁) fun s₃ ⟨hout, hf, hrd, hwr, hk⟩ => ?_)
  have hr4 : s₃.gpr .r4 = sp' s₀ := by rw [hk _ not_words_r4 (by decide), h₁.gpr]
  have hsav : ∀ i < 8, s₃.mem.readW (sp' s₀ + BitVec.ofNat 64 (8 * i)) 64 = s₀.gpr (saved i) :=
    fun i hi => by
      rw [hf.readW (r := sR s₀) (contains_off (by omega_arith) (by omega_arith))
        (by simpa [bR, hb] using hp.disj.symm) (by decide)]
      exact h₁.saved i hi
  have hr₀ : RI' s₀ s₃ 0 s₃ :=
    ⟨fun _ h => absurd h (by omega_arith), fun _ _ => rfl, rfl, hrd.trans h₁.rd, hwr.trans h₁.wr⟩
  refine WP.mono (wp_range_flatMap (M := isa) (RI' s₀ s₃)
    (fun k s hk h => restore_step hp hr4 hsav hk h) 8 (Nat.le_refl _) s₃ hr₀) fun s' h => ⟨?_, ?_⟩
  · intro r hr
    rcases preserved_cases hr with ⟨i, hi, rfl⟩ | ⟨hw, h0⟩
    · exact h.restored i hi
    · rw [h.others r fun i hi e => hw (e ▸ saved_words hi), hk r hw h0, h₁.gpr]
  · show Spec.Scrypt.bytesAt s'.mem (bp s₀) 64 = Spec.Scrypt.salsa (Spec.Scrypt.bytesAt s₀.mem (bp s₀) 64)
    rw [h.mem]
    refine post_of fun j hj => ?_
    rw [← hb, hout j hj, Rs, hV]

theorem salsa_correct (s : State) (hs : Proof.Scrypt.salsaPPC64LE.pre s) :
    ∃ t s', Exec isa Impl.Scrypt.PPC64LE.salsa s t s' ∧ abiPreserved s s' ∧
      Proof.Scrypt.salsaPPC64LE.post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.lr he (by decide +kernel)
    (by rw [← Code.allInstrs_eq]; decide +kernel)⟩, h₂⟩

end VG.Proof.Scrypt.PPC64LE

end

end

/-!
# scryptBlockMix on PPC64LE: correctness of the loop

As on AArch64 (`Proof/Scrypt/AArch64/Resident/Verified.lean`), the calls of
`vg_salsa20_8` are used through `SalsaSpec`, what its proof says about a call;
the proof of this file holds for any code meeting it.

The function's body runs inside a frame saving the link register (moved to
`r0`); the state `s₀` here is the one the body starts in, and the frame is
handled at the end of this file.
-/

@[expose] public section

namespace VG.Proof.Scrypt.PPC64LE.BlockMix

open VG VG.PPC64LE VG.Impl.Scrypt.PPC64LE
open VG.Spec.Scrypt (bytesAt blk salsa)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Scrypt (yAt xBefore yAt_eq xBefore_succ)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open VG.Proof.MdStream.PPC64LE (Upd wp_mov wp_addi wp_subi sub_ofNat)
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt add_ofNat toNat_add_ofNat contains_off sub_off disj_off
  InRegions.of_mem frame_bytesAt bytesAt_writeBytes_self xorBytes_length bytesAt_length blk_bytesAt)

/-! ## What a call of `vg_salsa20_8` does -/

/-- A call of `c` replaces the 64 bytes at `r3` by their Salsa20/8 Core,
with the 64 bytes at `r4` as working space. -/
def SalsaSpec (c : Prog isa) : Prop :=
  ∀ (s : State) (d sc : Addr), s.gpr .r3 = d → s.gpr .r4 = sc →
    Region.Disjoint ⟨d, 64⟩ ⟨sc, 64⟩ → InRegions s.wr d 64 → InRegions s.wr sc 64 →
    ∀ Q : State → Prop, (∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
        (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
        Frame [⟨d, 64⟩, ⟨sc, 64⟩] s.mem s'.mem →
        bytesAt s'.mem d 64 = salsa (bytesAt s.mem d 64) → Q s') →
    WP isa (.call "vg_salsa20_8" c) s Q

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev bP : Addr := s₀.gpr .r3
abbrev rr : Nat := (s₀.gpr .r4).toNat
abbrev yP : Addr := s₀.gpr .r5
abbrev sc : Addr := s₀.gpr .r7
abbrev bR : Region := ⟨bP s₀, rr s₀ * 128⟩
abbrev yR : Region := ⟨yP s₀, rr s₀ * 128⟩
abbrev scR : Region := ⟨sc s₀, 128⟩
/-- The input. -/
abbrev B : List Byte := bytesAt s₀.mem (bP s₀) (128 * rr s₀)

/-- `Y[2i]` goes to `y + 64 i`. -/
abbrev yE (i : Nat) : Addr := yP s₀ + BitVec.ofNat 64 (64 * i)
/-- `Y[2i + 1]` goes to `y + 64 (r + i)`. -/
abbrev yO (i : Nat) : Addr := yP s₀ + BitVec.ofNat 64 (64 * (rr s₀ + i))
/-- `B[2i]`. -/
abbrev bB (i : Nat) : Addr := bP s₀ + BitVec.ofNat 64 (128 * i)
/-- Where `X` is before the pair `(2k, 2k + 1)`. -/
def xP : Nat → Addr
  | 0 => bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)
  | k + 1 => yO s₀ k

/-- The caller's `r24`–`r29` are saved in the scratch space. -/
abbrev Saved (m : Mem) : Prop := Spill.Saved (sc s₀) s₀.gpr bmSaved m

end

/-- The nonvolatile registers the code never writes. -/
def others : List Reg := [.r2, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r30, .r31]

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [bR s₀]
  wr : s₀.wr = [yR s₀, scR s₀]
  y_s : (yR s₀).Disjoint (scR s₀)
  b_y : (bR s₀).Disjoint (yR s₀)
  b_s : (bR s₀).Disjoint (scR s₀)
  b_nw : (bP s₀).toNat + rr s₀ * 128 ≤ 2 ^ 64
  y_nw : (yP s₀).toNat + rr s₀ * 128 ≤ 2 ^ 64
  s_nw : (sc s₀).toNat + 128 ≤ 2 ^ 64
  r6 : s₀.gpr .r6 = s₀.gpr .r4
  pos : 0 < rr s₀

section
variable {s₀ : State} (hp : Pre s₀)
include hp

/-- `y` is not the whole address space, since `scratch` is not in it. -/
theorem r_lt : 128 * rr s₀ < 2 ^ 64 := by
  by_contra hc
  refine hp.y_s (sc s₀) ?_ (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith)
  simp only [Region.Contains]
  have := (sc s₀ - yP s₀).isLt
  omega_arith

theorem in_y {o n : Nat} (h : o + n ≤ 128 * rr s₀) :
    (yR s₀).Contains (yP s₀ + BitVec.ofNat 64 o) n :=
  contains_off (by omega_arith) (by have := r_lt hp; omega_arith)

theorem in_b {o n : Nat} (h : o + n ≤ 128 * rr s₀) :
    (bR s₀).Contains (bP s₀ + BitVec.ofNat 64 o) n :=
  contains_off (by omega_arith) (by have := r_lt hp; omega_arith)

/-- Two parts of `y`. -/
theorem y_disj {o₁ n₁ o₂ n₂ : Nat} (h : o₁ + n₁ ≤ o₂ ∨ o₂ + n₂ ≤ o₁) (h₁ : o₁ + n₁ ≤ 128 * rr s₀)
    (h₂ : o₂ + n₂ ≤ 128 * rr s₀) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) :
    Region.Disjoint ⟨yP s₀ + BitVec.ofNat 64 o₁, n₁⟩ ⟨yP s₀ + BitVec.ofNat 64 o₂, n₂⟩ :=
  have := r_lt hp
  disj_off _ h (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)

theorem y_sub {o n : Nat} (h : o + n ≤ 128 * rr s₀) : Region.Sub ⟨yP s₀ + BitVec.ofNat 64 o, n⟩ (yR s₀) :=
  sub_off (by omega_arith) (by have := r_lt hp; omega_arith)

theorem b_sub {o n : Nat} (h : o + n ≤ 128 * rr s₀) : Region.Sub ⟨bP s₀ + BitVec.ofNat 64 o, n⟩ (bR s₀) :=
  sub_off (by omega_arith) (by have := r_lt hp; omega_arith)

/-- A part of `y` and a part of `b`. -/
theorem yb_disj {o₁ n₁ o₂ n₂ : Nat} (h₁ : o₁ + n₁ ≤ 128 * rr s₀) (h₂ : o₂ + n₂ ≤ 128 * rr s₀) :
    Region.Disjoint ⟨yP s₀ + BitVec.ofNat 64 o₁, n₁⟩ ⟨bP s₀ + BitVec.ofNat 64 o₂, n₂⟩ :=
  (hp.b_y.symm.sub_left (y_sub hp h₁)).sub_right (b_sub hp h₂)

end

theorem in_s (s₀ : State) {o n : Nat} (h : o + n ≤ 128) :
    (scR s₀).Contains (sc s₀ + BitVec.ofNat 64 o) n :=
  contains_off h (by omega_arith)

theorem s_sub (s₀ : State) {o n : Nat} (h : o + n ≤ 128) :
    Region.Sub ⟨sc s₀ + BitVec.ofNat 64 o, n⟩ (scR s₀) :=
  sub_off h (by omega_arith)

/-! ## The loop invariant -/

/-- After `k` pairs. -/
structure Inv (s₀ : State) (k : Nat) (s : State) : Prop where
  k_le : k ≤ rr s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r24 : s.gpr .r24 = bB s₀ k
  r25 : s.gpr .r25 = yE s₀ k
  r26 : s.gpr .r26 = yO s₀ k
  r27 : s.gpr .r27 = sc s₀
  r28 : s.gpr .r28 = BitVec.ofNat 64 (rr s₀ - k)
  r29 : s.gpr .r29 = xP s₀ k
  keep : ∀ r ∈ others, s.gpr r = s₀.gpr r
  frame : Frame [yR s₀, scR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  done : ∀ i < k, bytesAt s.mem (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
    bytesAt s.mem (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1)
  x : bytesAt s.mem (xP s₀ k) 64 = xBefore (B s₀) (rr s₀) (2 * k)

/-- The input is unchanged in any memory that differs from the initial one
only in `y` and `scratch`. -/
theorem b_frame {s₀ : State} (hp : Pre s₀) {m : Mem} (hf : Frame [yR s₀, scR s₀] s₀.mem m)
    {o n : Nat} (ho : o + n ≤ 128 * rr s₀) :
    bytesAt m (bP s₀ + BitVec.ofNat 64 o) n = bytesAt s₀.mem (bP s₀ + BitVec.ofNat 64 o) n := by
  refine frame_bytesAt hf (fun r hr => ?_) (by have := r_lt hp; omega_arith)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.b_y.sub_left (b_sub hp ho)
  · exact hp.b_s.sub_left (b_sub hp ho)

/-- Block `i` of the input. -/
theorem blk_B (s₀ : State) {i : Nat} (hi : i < 2 * rr s₀) :
    blk (B s₀) i = bytesAt s₀.mem (bP s₀ + BitVec.ofNat 64 (64 * i)) 64 :=
  blk_bytesAt _ _ (by omega_arith)

/-! ## A call of `vg_salsa20_8` on a block of `y` -/

theorem pres_ne : ∀ r ∈ preserved, r ≠ .r3 ∧ r ≠ .r4 ∧ r ≠ .r9 ∧ r ≠ .r10 := by decide

/-- A 64-byte slot of `y` at offset `o`. -/
abbrev slot (s₀ : State) (o : Nat) : Region := ⟨yP s₀ + BitVec.ofNat 64 o, 64⟩

theorem salsaAt_ok {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) {dR : Reg}
    (hd0 : dR ≠ .r0) {s : State} {o : Nat} (ho : o + 64 ≤ 128 * rr s₀)
    (hd : s.gpr dR = yP s₀ + BitVec.ofNat 64 o)
    (h27 : s.gpr .r27 = sc s₀) (hwr : s.wr = s₀.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      Frame [slot s₀ o, ⟨sc s₀, 64⟩] s.mem s'.mem →
      bytesAt s'.mem (yP s₀ + BitVec.ofNat 64 o) 64 =
        salsa (bytesAt s.mem (yP s₀ + BitVec.ofNat 64 o) 64) → Q s') :
    WP isa (salsaAt c dR) s Q := by
  unfold salsaAt
  refine WP.seq (wp_mov (fun s₁ u₁ => wp_mov (fun s₂ u₂ => WP.block_nil ?_)) hd0)
  obtain e₁ : s₂.gpr .r3 = yP s₀ + BitVec.ofNat 64 o := by rw [u₂.other _ (by decide), u₁.gpr, hd]
  obtain e₂ : s₂.gpr .r4 = sc s₀ := by rw [u₂.gpr, u₁.other _ (by decide), h27]
  obtain e₃ : ∀ r ∈ preserved, s₂.gpr r = s.gpr r := fun r hr => by
    rw [u₂.other _ (pres_ne r hr).2.1, u₁.other _ (pres_ne r hr).1]
  obtain hsub : Region.Sub (slot s₀ o) (yR s₀) := y_sub hp ho
  obtain hsub' : Region.Sub ⟨sc s₀, 64⟩ (scR s₀) := Region.sub_prefix (by omega_arith)
  obtain hsc : (scR s₀).Contains (sc s₀) 64 := by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith
  refine hS s₂ _ _ e₁ e₂ (hp.y_s.sub_left hsub |>.sub_right hsub')
    (by rw [u₂.wr, u₁.wr, hwr, hp.wr]; exact InRegions.of_mem (by simp) (in_y hp ho))
    (by rw [u₂.wr, u₁.wr, hwr, hp.wr]; exact InRegions.of_mem (R := scR s₀) (by simp) hsc)
    _ fun s' hrd hwr' hsp hcs hf hb => hQ s' (by rw [hrd, u₂.rd, u₁.rd]) (by rw [hwr', u₂.wr, u₁.wr])
      (by rw [hsp, u₂.sp, u₁.sp]) (fun r hr => by rw [hcs r hr, e₃ r hr])
      (by rw [u₂.mem, u₁.mem] at hf; exact hf) (by rw [hb, u₂.mem, u₁.mem])

/-! ## One pair -/

theorem slot_s {s₀ : State} (hp : Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) :
    (slot s₀ o).Disjoint ⟨sc s₀, 64⟩ :=
  (hp.y_s.sub_left (y_sub hp ho)).sub_right (Region.sub_prefix (by omega_arith))

/-- Where `X` is. -/
theorem xP_in {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) {s : State}
    (hrd : s.rd = [bR s₀]) (hwr : s.wr = [yR s₀, scR s₀]) :
    ∀ i < 8, InRegions (s.rd ++ s.wr) (xP s₀ k + BitVec.ofNat 64 (8 * i)) 8 := by
  intro i hi
  rw [hrd, hwr]
  cases k with
  | zero =>
    simp only [xP]
    rw [add_ofNat]
    exact InRegions.of_mem (by simp) (in_b hp (by have := hp.pos; omega_arith))
  | succ j =>
    simp only [xP]
    rw [add_ofNat]
    exact InRegions.of_mem (by simp) (in_y hp (by omega_arith))

theorem xP_disj {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) :
    Region.Disjoint (slot s₀ (64 * k)) ⟨xP s₀ k, 64⟩ := by
  cases k with
  | zero => exact yb_disj hp (by omega_arith) (by have := hp.pos; omega_arith)
  | succ j => exact y_disj hp (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)

/-- What a call's frame keeps: our caller's saved registers. -/
theorem saved_keep {s₀ : State} (hp : Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) {m m' : Mem}
    (hf : Frame [slot s₀ o, ⟨sc s₀, 64⟩] m m') (h : Saved s₀ m) : Saved s₀ m' :=
  Spill.Saved.frame h hf fun p hp' r hr => by
  obtain hp8 : p.2 + 8 ≤ 128 ∧ 64 ≤ p.2 := by revert p; decide
  obtain hsub : Region.Sub ⟨sc s₀ + BitVec.ofNat 64 p.2, 8⟩ (scR s₀) := s_sub s₀ (by omega_arith)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (hp.y_s.sub_left (y_sub hp ho)).sub_right hsub |>.symm
  · have := disj_off (sc s₀) (o₁ := p.2) (n₁ := 8) (o₂ := 0) (n₂ := 64) (by omega_arith) (by omega_arith)
      (by omega_arith) (by omega_arith) (by omega_arith)
    simpa using this

/-- What a call's frame keeps: the other blocks of `y`. -/
theorem slot_keep {s₀ : State} (hp : Pre s₀) {o o' : Nat} (ho : o + 64 ≤ 128 * rr s₀)
    (ho' : o' + 64 ≤ 128 * rr s₀) (hd : o' + 64 ≤ o ∨ o + 64 ≤ o') {m m' : Mem}
    (hf : Frame [slot s₀ o, ⟨sc s₀, 64⟩] m m') :
    bytesAt m' (yP s₀ + BitVec.ofNat 64 o') 64 = bytesAt m (yP s₀ + BitVec.ofNat 64 o') 64 := by
  refine frame_bytesAt hf (fun r hr => ?_) (by omega_arith)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact y_disj hp hd ho' ho (by omega_arith) (by omega_arith)
  · exact slot_s hp ho'

theorem frame_big {s₀ : State} (hp : Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) {m m' : Mem}
    (hf : Frame [slot s₀ o, ⟨sc s₀, 64⟩] m m') : Frame [yR s₀, scR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨yR s₀, List.mem_cons_self, y_sub hp ho⟩
    · exact ⟨scR s₀, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (by omega_arith)⟩

/-- Half a pair: `T = X xor B[i]` into block `o` of `y`, then Salsa20/8 of it. -/
theorem half_ok {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) {dR xR sR : Reg}
    (hd : dR ≠ .r9 ∧ dR ≠ .r10 ∧ dR ≠ .r0) (hx : xR ≠ .r9 ∧ xR ≠ .r10 ∧ xR ≠ .r0)
    (hs : sR ≠ .r9 ∧ sR ≠ .r10 ∧ sR ≠ .r0)
    {o : Nat} (ho : o + 64 ≤ 128 * rr s₀)
    {x : Addr} {ob : Nat} (hob : ob + 64 ≤ 128 * rr s₀) {s : State}
    (hrd : s.rd = [bR s₀]) (hwr : s.wr = [yR s₀, scR s₀])
    (gd : s.gpr dR = yP s₀ + BitVec.ofNat 64 o) (gx : s.gpr xR = x)
    (gs : s.gpr sR = bP s₀ + BitVec.ofNat 64 ob) (h27 : s.gpr .r27 = sc s₀)
    (hdx : Region.Disjoint (slot s₀ o) ⟨x, 64⟩)
    (hinx : ∀ i < 8, InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 (8 * i)) 8)
    {P : Prog isa} {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      Frame [slot s₀ o, ⟨sc s₀, 64⟩] s.mem s'.mem →
      bytesAt s'.mem (yP s₀ + BitVec.ofNat 64 o) 64 =
        salsa (xorBytes (bytesAt s.mem x 64) (bytesAt s.mem (bP s₀ + BitVec.ofNat 64 ob) 64)) →
      WP isa P s' Q) :
    WP isa (.block (xor64 dR xR sR)) s fun s' => WP isa (.seq (salsaAt c dR) P) s' Q := by
  obtain lt := r_lt hp
  rw [← List.append_nil (xor64 dR xR sR)]
  refine xor64_ok hd hx hs hdx (yb_disj hp ho hob) 8 (Nat.le_refl _) [] s _ gd gx gs hinx
    (fun i hi => by
      rw [hrd, hwr, add_ofNat]; exact InRegions.of_mem (by simp) (in_b hp (by omega_arith)))
    (fun i hi => by
      rw [hwr, add_ofNat]; exact InRegions.of_mem (by simp) (in_y hp (by omega_arith)))
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => WP.block_nil ?_
  obtain l1 : (xorBytes (bytesAt s.mem x 64) (bytesAt s.mem (bP s₀ + BitVec.ofNat 64 ob) 64)).length
      = 64 := by
    rw [xorBytes_length _ _ (by simp [bytesAt_length]), bytesAt_length]
  obtain f₁ : Frame [slot s₀ o] s.mem s₁.mem := by
    rw [m₁]; exact writeBytes_frame _ _ _ (by rw [l1]; exact Region.contains_self _ _)
  obtain hw := bytesAt_writeBytes_self s.mem (yP s₀ + BitVec.ofNat 64 o) _ (by rw [l1]; omega_arith)
  rw [l1] at hw
  refine WP.seq (salsaAt_ok hS hp hd.2.2 ho (by rw [g₁ _ hd.1 hd.2.1, gd])
    (by rw [g₁ _ (by decide) (by decide), h27]) (by rw [wr₁, hwr, hp.wr])
    fun s₂ rd₂ wr₂ sp₂ cs₂ f₂ b₂ => ?_)
  refine hQ s₂ (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) (by rw [sp₂, sp₁])
    (fun r hr => by rw [cs₂ r hr, g₁ r (pres_ne r hr).2.2.1 (pres_ne r hr).2.2.2])
    ((f₁.mono (by simp)).trans f₂) ?_
  rw [b₂, m₁, hw]

/-- The state after both halves of pair `k`. -/
structure Mid (s₀ : State) (k : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r24 : s.gpr .r24 = bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))
  r25 : s.gpr .r25 = yE s₀ k
  r26 : s.gpr .r26 = yO s₀ k
  r27 : s.gpr .r27 = sc s₀
  r28 : s.gpr .r28 = BitVec.ofNat 64 (rr s₀ - k)
  keep : ∀ r ∈ others, s.gpr r = s₀.gpr r
  frame : Frame [yR s₀, scR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  done : ∀ i < k + 1, bytesAt s.mem (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
    bytesAt s.mem (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1)

/-- The memory after pair `k`. -/
theorem mem_ok {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) {s s₂ s₅ : State}
    (h : Inv s₀ k s)
    (f₂ : Frame [slot s₀ (64 * k), ⟨sc s₀, 64⟩] s.mem s₂.mem)
    (b₂ : bytesAt s₂.mem (yE s₀ k) 64 =
      salsa (xorBytes (bytesAt s.mem (xP s₀ k) 64) (bytesAt s.mem (bB s₀ k) 64)))
    (f₅ : Frame [slot s₀ (64 * (rr s₀ + k)), ⟨sc s₀, 64⟩] s₂.mem s₅.mem)
    (b₅ : bytesAt s₅.mem (yO s₀ k) 64 = salsa (xorBytes (bytesAt s₂.mem (yE s₀ k) 64)
      (bytesAt s₂.mem (bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))) 64))) :
    Frame [yR s₀, scR s₀] s₀.mem s₅.mem ∧ Saved s₀ s₅.mem ∧
    ∀ i < k + 1, bytesAt s₅.mem (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
      bytesAt s₅.mem (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1) := by
  obtain lt := r_lt hp
  obtain oE : 64 * k + 64 ≤ 128 * rr s₀ := by omega_arith
  obtain oO : 64 * (rr s₀ + k) + 64 ≤ 128 * rr s₀ := by omega_arith
  obtain F₂ := h.frame.trans (frame_big hp oE f₂)
  obtain yE_eq : bytesAt s₂.mem (yE s₀ k) 64 = yAt (B s₀) (rr s₀) (2 * k) := by
    rw [b₂, h.x, b_frame hp h.frame (by omega_arith : 128 * k + 64 ≤ 128 * rr s₀),
      show 128 * k = 64 * (2 * k) by omega_arith, ← blk_B s₀ (by omega_arith), yAt_eq]
  obtain hb : bytesAt s₂.mem (bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))) 64 =
      blk (B s₀) (2 * k + 1) := by
    rw [blk_B s₀ (by omega_arith)]
    exact b_frame hp F₂ (by omega_arith)
  refine ⟨F₂.trans (frame_big hp oO f₅), saved_keep hp oO f₅ (saved_keep hp oE f₂ h.saved),
    fun i hi => ?_⟩
  by_cases hik : i = k
  · subst i
    refine ⟨?_, ?_⟩
    · rw [slot_keep hp oO oE (by omega_arith) f₅, yE_eq]
    · rw [b₅, yE_eq, hb, yAt_eq (B s₀) (rr s₀) (2 * k + 1), xBefore_succ]
  · have hi' : i < k := by omega_arith
    obtain ⟨d₁, d₂⟩ := h.done i hi'
    refine ⟨?_, ?_⟩
    · rw [slot_keep hp oO (by omega_arith) (by omega_arith) f₅, slot_keep hp oE (by omega_arith) (by omega_arith) f₂, d₁]
    · rw [slot_keep hp oO (by omega_arith) (by omega_arith) f₅, slot_keep hp oE (by omega_arith) (by omega_arith) f₂, d₂]

theorem others_pres : ∀ r ∈ others, r ∈ preserved ∧ r ≠ .r24 := by decide

/-- Both halves of pair `k`. -/
theorem halves_ok {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) {k : Nat}
    (hk : k < rr s₀) {s : State} (h : Inv s₀ k s) {P : Prog isa} {Q : State → Prop}
    (hQ : ∀ s', Mid s₀ k s' → WP isa P s' Q) :
    WP isa (.seq (.block (xor64 .r25 .r29 .r24)) <| .seq (salsaAt c .r25) <|
      .seq (.block (.addi .r24 .r24 64 :: xor64 .r26 .r25 .r24)) <| .seq (salsaAt c .r26) P)
      s Q := by
  obtain lt := r_lt hp
  obtain hrd : s.rd = [bR s₀] := by rw [h.rd, hp.rd]
  obtain hwr : s.wr = [yR s₀, scR s₀] := by rw [h.wr, hp.wr]
  obtain oE : 64 * k + 64 ≤ 128 * rr s₀ := by omega_arith
  obtain oO : 64 * (rr s₀ + k) + 64 ≤ 128 * rr s₀ := by omega_arith
  refine WP.seq (half_ok hS hp (by decide) (by decide) (by decide) oE (ob := 128 * k) (by omega_arith)
    hrd hwr h.r25 h.r29 h.r24 h.r27 (xP_disj hp hk) (xP_in hp hk hrd hwr)
    fun s₂ rd₂ wr₂ sp₂ cs₂ f₂ b₂ => ?_)
  refine WP.seq (wp_addi (by decide) fun s₃ u₃ => ?_)
  obtain k3 : ∀ r, r ≠ .r24 → r ∈ preserved → s₃.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₃.other _ h1, cs₂ r h2]
  obtain e3 : s₃.gpr .r24 = bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1)) := by
    rw [u₃.gpr, cs₂ _ (by decide), h.r24, add_ofNat]; congr 2; omega_arith
  obtain hrd₃ : s₃.rd = [bR s₀] := by rw [u₃.rd, rd₂, hrd]
  obtain hwr₃ : s₃.wr = [yR s₀, scR s₀] := by rw [u₃.wr, wr₂, hwr]
  obtain e25 : s₃.gpr .r25 = yE s₀ k := by rw [k3 _ (by decide) (by decide), h.r25]
  refine half_ok hS hp (by decide) (by decide) (by decide) oO (ob := 64 * (2 * k + 1)) (by omega_arith)
    hrd₃ hwr₃ (by rw [k3 _ (by decide) (by decide), h.r26]) e25 e3
    (by rw [k3 _ (by decide) (by decide), h.r27])
    (y_disj hp (by omega_arith) oO oE (by omega_arith) (by omega_arith))
    (fun i hi => by rw [hrd₃, hwr₃, add_ofNat]; exact InRegions.of_mem (by simp) (in_y hp (by omega_arith)))
    fun s₅ rd₅ wr₅ sp₅ cs₅ f₅ b₅ => ?_
  rw [u₃.mem] at f₅ b₅
  obtain ⟨F, S, D⟩ := mem_ok hp hk h f₂ b₂ f₅ b₅
  obtain k5 : ∀ r, r ≠ .r24 → r ∈ preserved → s₅.gpr r = s.gpr r := fun r h1 h2 => by
    rw [cs₅ r h2, k3 r h1 h2]
  exact hQ s₅ ⟨by rw [rd₅, hrd₃, hp.rd], by rw [wr₅, hwr₃, hp.wr],
    by rw [sp₅, u₃.sp, sp₂, h.sp],
    by rw [cs₅ _ (by decide), e3],
    by rw [k5 _ (by decide) (by decide), h.r25],
    by rw [k5 _ (by decide) (by decide), h.r26],
    by rw [k5 _ (by decide) (by decide), h.r27],
    by rw [k5 _ (by decide) (by decide), h.r28],
    fun r hr => by
      rw [k5 r (others_pres r hr).2 (others_pres r hr).1, h.keep r hr],
    F, S, D⟩

/-- The pointers move on. -/
theorem regs_ok {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) {s : State}
    (h : Mid s₀ k s) :
    WP isa (.block [mov .r29 .r26, .addi .r24 .r24 64, .addi .r25 .r25 64,
      .addi .r26 .r26 64, .subi .r28 .r28 1]) s (Inv s₀ (k + 1)) := by
  obtain lt := r_lt hp
  refine wp_mov fun s₆ u₆ => wp_addi (by decide) fun s₇ u₇ => wp_addi (by decide) fun s₈ u₈ =>
    wp_addi (by decide) fun s₉ u₉ => wp_subi (by decide) fun s₁₀ u₁₀ => WP.block_nil ?_
  obtain m₁₀ : s₁₀.mem = s.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem]
  obtain g : ∀ r, r ≠ .r24 → r ≠ .r25 → r ≠ .r26 → r ≠ .r28 → r ≠ .r29 → s₁₀.gpr r = s.gpr r :=
    fun r h24 h25 h26 h28 h29 => by
      rw [u₁₀.other _ h28, u₉.other _ h26, u₈.other _ h25, u₇.other _ h24, u₆.other _ h29]
  refine ⟨(by omega_arith), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, h.rd]
  · rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, h.wr]
  · rw [u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, h.sp]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr,
      u₆.other _ (by decide), h.r24, add_ofNat]
    congr 2; omega_arith
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide),
      u₆.other _ (by decide), h.r25, add_ofNat]
    congr 2
  · rw [u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), h.r26, add_ofNat]
    congr 2
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r27]
  · rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), h.r28, sub_ofNat (by omega_arith)]
    congr 1
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.gpr, h.r26]
    rfl
  · intro r hr
    have : r ≠ .r24 ∧ r ≠ .r25 ∧ r ≠ .r26 ∧ r ≠ .r28 ∧ r ≠ .r29 := by
      revert r; decide
    rw [g r this.1 this.2.1 this.2.2.1 this.2.2.2.1 this.2.2.2.2, h.keep r hr]
  · rw [m₁₀]; exact h.frame
  · rw [m₁₀]; exact h.saved
  · rw [m₁₀]; exact h.done
  · rw [m₁₀]
    show bytesAt s.mem (yO s₀ k) 64 = _
    rw [(h.done k (by omega_arith)).2]
    rfl

theorem body_ok {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) {k : Nat}
    (hk : k < rr s₀) {s : State} (h : Inv s₀ k s) : WP isa (bmBody c) s (Inv s₀ (k + 1)) :=
  halves_ok hS hp hk h fun _ hm => regs_ok hp hk hm

end VG.Proof.Scrypt.PPC64LE.BlockMix

/-!
# scryptBlockMix on PPC64LE: the whole function

The prologue saves our caller's `r24`–`r29` in `scratch` and sets up the
loop's registers; the loop runs the `r` pairs; the epilogue restores the
registers. Around all of it, a frame saves the link register, which the
calls replace.
-/

namespace VG.Proof.Scrypt.PPC64LE.BlockMix

open VG VG.PPC64LE VG.Impl.Scrypt.PPC64LE
open VG.Spec.Scrypt (bytesAt blk blockMix)
open VG.Proof.Scrypt (yAt xBefore blockMix_eq flatMap_congr)
open VG.Proof.MdStream.PPC64LE (Upd wp_mov wp_add wp_addi wp_subi wp_lsl eval_nonzero ofNat_beq_zero
  write_frame_bytes frame_sub)
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt add_ofNat InRegions.of_mem frame_bytesAt bytesAt_add
  bytesAt_blocks bytesAt_congr)

/-! ## The prologue -/

/-- The memory after the prologue's stores. -/
abbrev saveMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (sc s₀) s₀.gpr bmSaved

theorem saveMem_saved (s₀ : State) : Saved s₀ (saveMem s₀) := Spill.saveMem_saved (by decide) _ _ _

theorem saveMem_frame (s₀ : State) : Frame [scR s₀] s₀.mem (saveMem s₀) :=
  Spill.saveMem_frame_base (by decide) (by decide) _ _ _

theorem prologue_eq : bmPrologue = Spill.saveCode .r7 bmSaved ++
    ([mov .r28 .r4, mov .r24 .r3, mov .r25 .r5, mov .r27 .r7,
     .lsl .r9 .r4 6, .add .r26 .r5 .r9,
     .lsl .r9 .r4 7, .add .r29 .r3 .r9, .subi .r29 .r29 64] : List Instr) := rfl

theorem save_ok {s₀ : State} (hp : Pre s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s₁, s₁.gpr = s₀.gpr → s₁.rd = s₀.rd → s₁.wr = s₀.wr → s₁.sp = s₀.sp →
      s₁.mem = saveMem s₀ → WP isa (.block rest) s₁ Q) :
    WP isa (.block (Spill.saveCode .r7 bmSaved ++ rest)) s₀ Q :=
  Spill.save_ok (by decide) (by decide) (fun p hp' => by
    rw [hp.wr]; exact InRegions.of_mem (by simp) (in_s s₀ (by revert p; decide)))
    (k _ rfl rfl rfl rfl rfl)

theorem shl_eq {x : BitVec 64} {n : Nat} (h : x.toNat * 2 ^ n < 2 ^ 64) :
    x <<< n = BitVec.ofNat 64 (x.toNat * 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, toNat_ofNat_lt h, Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]

theorem add_sub64 (a : Addr) {n : Nat} (h : 64 ≤ n) :
    a + BitVec.ofNat 64 n - BitVec.ofNat 64 64 = a + BitVec.ofNat 64 (n - 64) := by
  rw [show n = (n - 64) + 64 by omega_arith, BitVec.ofNat_add, ← BitVec.add_assoc, Nat.add_sub_cancel,
    BitVec.add_sub_cancel]

/-- The registers the loop starts with. -/
theorem setup_ok {s₀ : State} (hp : Pre s₀) {s₁ : State} (g : s₁.gpr = s₀.gpr)
    (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) (hsp : s₁.sp = s₀.sp) (hm : s₁.mem = saveMem s₀) :
    WP isa (.block [mov .r28 .r4, mov .r24 .r3, mov .r25 .r5, mov .r27 .r7,
     .lsl .r9 .r4 6, .add .r26 .r5 .r9,
     .lsl .r9 .r4 7, .add .r29 .r3 .r9, .subi .r29 .r29 64]) s₁ (Inv s₀ 0) := by
  obtain lt : 128 * (s₀.gpr .r4).toNat < 2 ^ 64 := r_lt hp
  have pos := hp.pos
  refine wp_mov fun a ua => wp_mov fun b ub => wp_mov fun c uc => wp_mov fun d ud =>
    wp_lsl (by decide) fun e ue => wp_add fun f uf => wp_lsl (by decide) fun g' ug =>
    wp_add fun h uh => wp_subi (by decide) fun i ui => WP.block_nil ?_
  obtain r4 : d.gpr .r4 = s₀.gpr .r4 := by
    rw [ud.other _ (by decide), uc.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), g]
  obtain e9 : e.gpr .r9 = BitVec.ofNat 64 (64 * rr s₀) := by
    rw [ue.gpr, r4, shl_eq (by simp; omega_arith), Nat.mul_comm]
  obtain g9 : g'.gpr .r9 = BitVec.ofNat 64 (128 * rr s₀) := by
    rw [ug.gpr, uf.other _ (by decide), ue.other _ (by decide), r4, shl_eq (by simp; omega_arith),
      Nat.mul_comm]
  obtain hm' : i.mem = saveMem s₀ := by
    rw [ui.mem, uh.mem, ug.mem, uf.mem, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem, hm]
  obtain k : ∀ r, r ≠ .r9 → r ≠ .r24 → r ≠ .r25 → r ≠ .r26 → r ≠ .r27 → r ≠ .r28 → r ≠ .r29 →
      i.gpr r = s₀.gpr r := fun r h9 h24 h25 h26 h27 h28 h29 => by
    rw [ui.other _ h29, uh.other _ h29, ug.other _ h9, uf.other _ h26, ue.other _ h9,
      ud.other _ h27, uc.other _ h25, ub.other _ h24, ua.other _ h28, g]
  refine ⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => absurd hi (by omega_arith), ?_⟩
  · rw [ui.rd, uh.rd, ug.rd, uf.rd, ue.rd, ud.rd, uc.rd, ub.rd, ua.rd, hrd]
  · rw [ui.wr, uh.wr, ug.wr, uf.wr, ue.wr, ud.wr, uc.wr, ub.wr, ua.wr, hwr]
  · rw [ui.sp, uh.sp, ug.sp, uf.sp, ue.sp, ud.sp, uc.sp, ub.sp, ua.sp, hsp]
  · rw [ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide),
      uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.gpr, ua.other _ (by decide), g]
    simp
  · rw [ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide),
      uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide), uc.gpr,
      ub.other _ (by decide), ua.other _ (by decide), g]
    simp
  · rw [ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide), uf.gpr, e9,
      ue.other _ (by decide), ud.other _ (by decide), uc.other _ (by decide),
      ub.other _ (by decide), ua.other _ (by decide), g]
    simp
  · rw [ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide),
      uf.other _ (by decide), ue.other _ (by decide), ud.gpr, uc.other _ (by decide),
      ub.other _ (by decide), ua.other _ (by decide), g]
  · rw [ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide),
      uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.other _ (by decide), ua.gpr, g]
    simp
  · rw [ui.gpr, uh.gpr, g9, ug.other _ (by decide), uf.other _ (by decide),
      ue.other _ (by decide), ud.other _ (by decide), uc.other _ (by decide),
      ub.other _ (by decide), ua.other _ (by decide), g, add_sub64 _ (by omega_arith)]
    rfl
  · intro r hr
    have : r ≠ .r9 ∧ r ≠ .r24 ∧ r ≠ .r25 ∧ r ≠ .r26 ∧ r ≠ .r27 ∧ r ≠ .r28 ∧ r ≠ .r29 := by
      revert r; decide
    obtain ⟨h9, h24, h25, h26, h27, h28, h29⟩ := this
    exact k r h9 h24 h25 h26 h27 h28 h29
  · rw [hm']; exact (saveMem_frame s₀).mono (by simp)
  · rw [hm']; exact saveMem_saved s₀
  · rw [hm']
    show bytesAt (saveMem s₀) (bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)) 64 =
      blk (B s₀) (2 * rr s₀ - 1)
    rw [blk_B s₀ (by omega_arith), show 64 * (2 * rr s₀ - 1) = 128 * rr s₀ - 64 by omega_arith]
    refine frame_bytesAt (saveMem_frame s₀) (fun r hr => ?_) (by omega_arith)
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.b_s.sub_left (b_sub hp (by omega_arith))

/-! ## The loop -/

theorem loop_ok {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) {s : State}
    (h : Inv s₀ 0 s) : WP isa (.loop (bmBody c) (.nonzero .d .r28)) s (Inv s₀ (rr s₀)) := by
  obtain lt := r_lt hp
  refine WP.loop (M := isa) (fun n s => ∃ k, n = rr s₀ - k ∧ k < rr s₀ ∧ Inv s₀ k s) ?_ (rr s₀) s
    ⟨0, rfl, hp.pos, h⟩
  rintro n s ⟨k, rfl, hk, hi⟩
  refine WP.mono (body_ok hS hp hk hi) fun s' hi' => ?_
  obtain hz : isa.eval (.nonzero .d .r28) s' = some (decide (rr s₀ - (k + 1) ≠ 0)) := by
    show VG.PPC64LE.eval (.nonzero .d .r28) s' = _
    rw [eval_nonzero, hi'.r28, bne, ofNat_beq_zero (by omega_arith)]
    simp
  by_cases hl : rr s₀ - (k + 1) = 0
  · refine .inl ⟨by rw [hz]; simp [hl], ?_⟩
    rwa [show k + 1 = rr s₀ by omega_arith] at hi'
  · exact .inr ⟨by rw [hz]; simp [hl], rr s₀ - (k + 1), by omega_arith, k + 1, rfl, by omega_arith, hi'⟩

/-! ## The epilogue -/

theorem preserved_cases : ∀ r ∈ preserved, r ∈ bmSaved.map Prod.fst ∨ r ∈ others := by
  decide

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Inv s₀ (rr s₀) s) :
    WP isa (.block bmEpilogue) s fun s' => s'.mem = s.mem ∧ s'.sp = s.sp ∧
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) :=
  WP.mono (Spill.restore_wp (b := .r27) (by decide) h.r27 (by decide) (by decide) (fun p hp' => by
      rw [h.rd, h.wr, hp.rd, hp.wr]; exact InRegions.of_mem (by simp) (in_s s₀ (by revert p; decide)))
    h.saved) fun s' h' => ⟨h'.mem, h'.sp, fun r hr =>
      h'.gpr_of ((preserved_cases r hr).imp id (h.keep r))⟩

/-! ## The body of the frame -/

/-- The output, from the blocks the loop wrote. -/
theorem post_of {s₀ : State} {m : Mem}
    (h : ∀ i < rr s₀, bytesAt m (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
      bytesAt m (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1)) :
    bytesAt m (yP s₀) (128 * rr s₀) = blockMix (rr s₀) (B s₀) := by
  rw [blockMix_eq, show 128 * rr s₀ = 64 * rr s₀ + 64 * rr s₀ by omega_arith, bytesAt_add,
    bytesAt_blocks, bytesAt_blocks]
  congr 1
  · refine flatMap_congr fun i hi => ?_
    rw [List.mem_range] at hi
    exact (h i hi).1
  · refine flatMap_congr fun i hi => ?_
    rw [List.mem_range] at hi
    rw [add_ofNat, ← Nat.mul_add]
    exact (h i hi).2

theorem correctMain {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) :
    WP isa (blockMixMain c) s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      s'.sp = s₀.sp ∧ bytesAt s'.mem (yP s₀) (128 * rr s₀) = blockMix (rr s₀) (B s₀) := by
  unfold blockMixMain
  refine WP.seq ?_
  rw [prologue_eq]
  refine save_ok hp fun s₁ g hrd hwr hsp hm => ?_
  refine WP.mono (setup_ok hp g hrd hwr hsp hm) fun s₂ h₂ => ?_
  refine WP.seq (WP.mono (loop_ok hS hp h₂) fun s₃ h₃ => ?_)
  refine WP.mono (restore_ok hp h₃) fun s' ⟨hm', hsp', hg'⟩ => ⟨hg', hsp'.trans h₃.sp, ?_⟩
  rw [hm']
  exact post_of fun i hi => h₃.done i hi

/-! ## The whole function -/

/-- The frame's 48 bytes are free. -/
structure Stack (s₀ : State) : Prop where
  sp48 : 48 ≤ s₀.sp.toNat
  b : Region.Disjoint ⟨s₀.sp - 48, 48⟩ (bR s₀)
  y : Region.Disjoint ⟨s₀.sp - 48, 48⟩ (yR s₀)
  s : Region.Disjoint ⟨s₀.sp - 48, 48⟩ (scR s₀)

theorem pre_of {s₀ : State} (h : Proof.Scrypt.blockMixPPC64LE.pre s₀) : Pre s₀ ∧ Stack s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  rw [h13] at h2 h3 h4 h8 h11
  exact ⟨⟨h1, h2, h3, h4, h5, h10, h11, h12, h13, h14⟩, ⟨h6, h7, h8, h9⟩⟩

theorem fdepth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : c.fdepth = 0 := by
  induction c <;> simp_all [Code.noFrames, Code.fdepth]

theorem pushFrames_of_noFrames {c : Prog isa} (h : c.noFrames = true) : pushFrames c = true := by
  induction c <;> simp_all [Code.noFrames, pushFrames]

theorem noFrames_main {c : Prog isa} (hc : c.noFrames = true) : (blockMixMain c).noFrames = true := by
  simp only [blockMixMain, bmBody, salsaAt, Code.noFrames, hc, Bool.and_self]

/-- The state `blockMixMain` starts in: the link register moved to `r0`,
then pushed in a frame. -/
abbrev inner (s₀ : State) : State := framed .r0 (s₀.write .r0 s₀.lr)

theorem correct {c : Prog isa} (hS : SalsaSpec c) (hc : c.noFrames = true) {s₀ : State}
    (hpre : Proof.Scrypt.blockMixPPC64LE.pre s₀) :
    WP isa (blockMixWith c) s₀ fun s' =>
      abiPreserved s₀ s' ∧ Proof.Scrypt.blockMixPPC64LE.post s₀ s' := by
  obtain ⟨hp, hs⟩ := pre_of hpre
  obtain hpi : Pre (inner s₀) := ⟨hp.rd, hp.wr, hp.y_s, hp.b_y, hp.b_s, hp.b_nw, hp.y_nw, hp.s_nw,
    hp.r6, hp.pos⟩
  refine WP.seq (Proof.MdStream.PPC64LE.WP.cons PPC64LE.exec_mflr (WP.block_nil (WP.seq ?_)))
  refine WP.frameReg (by exact hs.sp48) (fun R hR => ?_) (WP.mono (correctMain hS hpi)
    fun s' ⟨hk, hsp, hpost⟩ m' u f => ?_) (by rw [fdepth_of_noFrames (noFrames_main hc)]; decide)
    (pushFrames_of_noFrames (noFrames_main hc))
  · rw [show (s₀.write .r0 s₀.lr).wr = s₀.wr from rfl, hp.wr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact hs.y.sub_left (frame_sub _)
    · exact hs.s.sub_left (frame_sub _)
  · refine Proof.MdStream.PPC64LE.WP.cons PPC64LE.exec_mtlr (WP.block_nil ⟨⟨fun r hr => ?_, rfl, ?_⟩, ?_⟩)
    · have h0 : r ≠ .r0 := by revert r hr; decide
      simp only [State.write, h0, ite_false]
      rw [hk r hr]
      simp only [framed, State.write, h0, ite_false]
    · simp [State.write]
    · have e : B (inner s₀) = bytesAt s₀.mem (bP s₀) (128 * rr s₀) :=
        bytesAt_congr fun i hi => by
          have hi' : i < 128 * rr s₀ := hi
          exact write_frame_bytes (R := bR s₀) hs.b (by have := r_lt hp; simp only; omega_arith)
            (by simp only; omega_arith)
      show bytesAt m' (yP s₀) (128 * rr s₀) = blockMix (rr s₀) (bytesAt s₀.mem (bP s₀) (128 * rr s₀))
      rw [← e]
      -- The pop loses the frame's bytes, which lie apart from the output.
      refine Eq.trans (bytesAt_congr fun i hi => lost_byte f (R := yR s₀) hs.y.symm
        (by show i < rr s₀ * 128; have : i < 128 * rr s₀ := hi; omega_arith)) hpost

end VG.Proof.Scrypt.PPC64LE.BlockMix

/-!
# scryptBlockMix on PPC64LE: verified

`SalsaSpec` of the verified Salsa20/8 Core, from its correctness proof by
`WP.call`; then the `Verified` proof of `vg_scrypt_blockmix`. Only the
pointers and `r` are public, and the taint analysis checks that nothing else
reaches an address or a branch.
-/

namespace VG.Proof.Scrypt.PPC64LE.BlockMix

open VG VG.PPC64LE

theorem salsa_noFrames : Impl.Scrypt.PPC64LE.salsa.noFrames = true := by decide +kernel

theorem salsaSpec : SalsaSpec Impl.Scrypt.PPC64LE.salsa := by
  intro s d sc hd hsc hds hind hins Q hQ
  obtain c3 : s.callEntry.gpr .r3 = d := (State.callEntry_gpr _ (by decide)).trans hd
  obtain c4 : s.callEntry.gpr .r4 = sc := (State.callEntry_gpr _ (by decide)).trans hsc
  obtain hw : Covers [⟨d, 64⟩, ⟨sc, 64⟩] s.wr := VG.Covers.pair (VG.Covers.one hind) (VG.Covers.one hins)
  refine WP.call (k := Proof.Scrypt.salsaPPC64LE) Proof.Scrypt.PPC64LE.salsa_correct
    (rd := []) (wr := [⟨d, 64⟩, ⟨sc, 64⟩]) ?_ ?_ hw ?_ salsa_noFrames
  · simp only [Proof.Scrypt.salsaPPC64LE, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c3, c4]
    exact ⟨trivial, trivial, hds⟩
  · intro a n h
    obtain ⟨R, hR, hc⟩ := hw a n (by simpa using h)
    exact ⟨R, List.mem_append_right _ hR, hc⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    simp only [Proof.Scrypt.salsaPPC64LE, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c3] at hpost
    exact hQ s' hrd hwr hsp hcs hf hpost

theorem agree₀ {s₁ s₂ : State} (hpub : Proof.Scrypt.blockMixPPC64LE.pub s₁ s₂) :
    VG.PPC64LE.Taint.Agree (VG.PPC64LE.Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem blockMix_correct (s : State) (hs : Proof.Scrypt.blockMixPPC64LE.pre s) :
    ∃ t s', Exec isa Impl.Scrypt.PPC64LE.blockMix s t s' ∧ abiPreserved s s' ∧
      Proof.Scrypt.blockMixPPC64LE.post s s' :=
  BlockMix.correct salsaSpec salsa_noFrames hs

theorem blockMix_ct : ConstantTime isa Proof.Scrypt.blockMixPPC64LE.pre
    Proof.Scrypt.blockMixPPC64LE.pub Impl.Scrypt.PPC64LE.blockMix := by
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun _ _ _ _ hp => agree₀ hp) (by taint_decide)

end VG.Proof.Scrypt.PPC64LE.BlockMix
