module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.Env
public import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Impl.AesGcm.RISCV64

/-!
# AES-GCM on RISC-V: the byte loops and `minLen`

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/AesGcm/PPC64LE/Loops.lean`): `copyLoop` copies `a2` bytes from `a0`
to `a1`, and `xorLoop` XORs `a2` bytes at `a0` into those at `a1`, a byte at
a time through advancing pointers, counting `a2` down to zero
(`copyLoop_ok`, `xorLoop_ok`); the buffers do not overlap. `minLen` leaves
`min (16 - s6, s5)` in `a2` (`minLen_ok`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)

theorem bytesAt_succ (m : Mem) (p : Addr) (i : Nat) :
    bytesAt m p (i + 1) = bytesAt m p i ++ [m (p + BitVec.ofNat 64 i)] := by
  simp [bytesAt, List.range_succ]

/-- Byte `i` of a region `⟨p, n⟩`, `i < n`, is in it. -/
theorem in_of_covers {rs : List Region} {p : Addr} {n i : Nat} (h : Covers [⟨p, n⟩] rs) (hi : i < n)
    (hn : n < 2 ^ 64) : InRegions rs (p + BitVec.ofNat 64 i) 1 :=
  h _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base p (by omega_arith) (by omega_arith)⟩

/-- What the loops need of the state: `n` (at least 1) bytes at `S` (read)
and `D` (written). -/
structure LoopPre (s : State) (S D : Addr) (n : Nat) : Prop where
  a0 : s.gpr .a0 = S
  a1 : s.gpr .a1 = D
  a2 : s.gpr .a2 = BitVec.ofNat 64 n
  pos : 1 ≤ n
  lt : n < 2 ^ 64
  rd : Covers [⟨S, n⟩] (s.rd ++ s.wr)
  wr : Covers [⟨D, n⟩] s.wr
  disj : (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩

/-- What the loops leave, but memory. -/
structure LoopOut (s : State) (S D : Addr) (n : Nat) (s' : State) : Prop where
  a0 : s'.gpr .a0 = S + BitVec.ofNat 64 n
  a1 : s'.gpr .a1 = D + BitVec.ofNat 64 n
  a2 : s'.gpr .a2 = 0
  other : ∀ r, r ≠ .t0 → r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → s'.gpr r = s.gpr r
  keeps : s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp

theorem dec64 {n i : Nat} (hi : i < n) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 (n - i) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (n - (i + 1)) := by
  rw [ofNat_sub64 (by omega_arith) (by omega_arith)]; congr 1

theorem nz_dec {n i : Nat} (hi : i < n) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 (n - (i + 1)) != 0) = !decide (i + 1 = n) := by
  have := ofNat_eq_zero (n := n - (i + 1)) (by omega_arith)
  by_cases h : i + 1 = n
  · simp [h]
  · have h' : BitVec.ofNat 64 (n - (i + 1)) ≠ 0 := fun e => h (by have := this.mp e; omega_arith)
    simp [h]; exact h'

theorem app0 (x : BitVec 8) : (0#0 ++ x).toNat = x.toNat := by
  rw [BitVec.toNat_append]; simp

theorem rd8 (x : BitVec 8) : BitVec.setWidth 8 (BitVec.setWidth 64 (0#0 ++ x)) = x := by
  apply BitVec.eq_of_toNat_eq; simp [app0]

theorem rd8x (x y : BitVec 8) :
    BitVec.setWidth 8 (BitVec.setWidth 64 (0#0 ++ x) ^^^ BitVec.setWidth 64 (0#0 ++ y)) = x ^^^ y := by
  apply BitVec.eq_of_toNat_eq; simp [app0]

theorem write1 (m : Mem) (a : Addr) (b : Byte) : m.write a 1 b = m.writeW a b := by
  simp only [Mem.writeW]; rfl

/-- The source byte `i` is not overwritten by the copy so far. -/
theorem src_kept {m : Mem} {S D : Addr} {n i : Nat} (hd : (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩) (hi : i < n)
    (hn : n < 2 ^ 64) (xs : List Byte) (hxs : xs.length = i) :
    writeBytes m D xs (S + BitVec.ofNat 64 i) = m (S + BitVec.ofNat 64 i) :=
  (writeBytes_frame m D xs (R := ⟨D, i⟩) (by rw [hxs]; exact Region.contains_self _ _)) _
    fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hd _ (Offset.contains_base S (by omega_arith) (by omega_arith)) (Region.sub_prefix (by omega_arith) _ hcon)

/-! ## `copyLoop` -/

abbrev copyBody : List Instr :=
  [.load .b .t0 .a0 0, .store .b .t0 .a1 0, .addi .a0 .a0 1, .addi .a1 .a1 1, .addi .a2 .a2 (-1)]

theorem copyStep_ok (s : State) {S D : Addr} {i n : Nat} (hs : s.gpr .a0 = S + BitVec.ofNat 64 i)
    (hd : s.gpr .a1 = D + BitVec.ofNat 64 i) (hn : s.gpr .a2 = BitVec.ofNat 64 (n - i))
    (r : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 i) 1)
    (w : InRegions s.wr (D + BitVec.ofNat 64 i) 1) :
    WP isa (.block copyBody) s fun s' =>
      s'.mem = s.mem.writeW (D + BitVec.ofNat 64 i) (s.mem (S + BitVec.ofNat 64 i)) ∧
      s'.gpr .a0 = S + BitVec.ofNat 64 (i + 1) ∧ s'.gpr .a1 = D + BitVec.ofNat 64 (i + 1) ∧
      s'.gpr .a2 = BitVec.ofNat 64 (n - i) - BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .t0 → r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  crun [hs, hd, hn, r, w, rd8, write1, add_ofNat_assoc]
  intro r h₀ h₃ h₄ h₅; simp [h₀, h₃, h₄, h₅]

theorem copyLoop_ok (s : State) {S D : Addr} {n : Nat} (h : LoopPre s S D n) :
    WP isa copyLoop s fun s' => s'.mem = writeBytes s.mem D (bytesAt s.mem S n) ∧
      LoopOut s S D n s' := by
  have hn := h.lt
  refine WP.loop (M := isa) (body := .block copyBody) (c := .nonzero .a2)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .a0 = S + BitVec.ofNat 64 i ∧
      t.gpr .a1 = D + BitVec.ofNat 64 i ∧ t.gpr .a2 = BitVec.ofNat 64 (n - i) ∧
      t.mem = writeBytes s.mem D (bytesAt s.mem S i) ∧
      (∀ r, r ≠ .t0 → r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp) ?_ (n - 0) _
    ⟨0, rfl, h.pos, by rw [h.a0, BitVec.add_zero], by rw [h.a1, BitVec.add_zero], by rw [h.a2]; rfl,
      by simp [bytesAt, writeBytes_nil], fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  rintro k t ⟨i, rfl, hi, r3, r4, r5, mem, g, rd, wr, sp⟩
  refine WP.mono (copyStep_ok t r3 r4 r5 (by rw [rd, wr]; exact in_of_covers h.rd hi hn)
    (by rw [wr]; exact in_of_covers h.wr hi hn)) fun t' ⟨mem', r3', r4', r5', g', rd', wr', sp'⟩ => ?_
  have hlen : (bytesAt s.mem S i).length = i := by simp [bytesAt]
  have hmem : t'.mem = writeBytes s.mem D (bytesAt s.mem S (i + 1)) := by
    rw [mem', mem, src_kept h.disj hi hn _ hlen, bytesAt_succ,
      writeBytes_snoc s.mem _ (bytesAt s.mem _ i) _ (by rw [hlen]; omega_arith), hlen]
  have gg : ∀ r, r ≠ .t0 → r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → t'.gpr r = s.gpr r :=
    fun r h₀ h₃ h₄ h₅ => by rw [g' r h₀ h₃ h₄ h₅, g r h₀ h₃ h₄ h₅]
  have ev : isa.eval (.nonzero .a2) t' = some !decide (i + 1 = n) := by
    show some (t'.gpr .a2 != 0) = _
    rw [r5', dec64 hi hn, nz_dec hi hn]
  by_cases he : i + 1 = n
  · left
    refine ⟨by rw [ev]; simp [he], by rw [hmem, he], ⟨by rw [r3', he], by rw [r4', he], ?_,
      fun r h₀ h₃ h₄ h₅ _ => gg r h₀ h₃ h₄ h₅, by rw [rd', rd], by rw [wr', wr], by rw [sp', sp]⟩⟩
    rw [r5', dec64 hi hn, he, Nat.sub_self]; rfl
  · right
    refine ⟨by rw [ev]; simp [he], n - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, r3', r4',
      by rw [r5', dec64 hi hn], hmem, gg, by rw [rd', rd], by rw [wr', wr], by rw [sp', sp]⟩

/-! ## `xorLoop` -/

/-- In place (`o` false) the data is its own destination, `S = D`; out of
place, the `n` bytes at `S` and at `D` are apart. -/
def Alias : Bool → Addr → Addr → Nat → Prop
  | false, S, D, _ => S = D
  | true, S, D, n => (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩

/-- The body of `xorLoopWith o`. -/
abbrev xorBodyWith (o : Bool) : List Instr :=
  [.load .b .t0 .a1 0, .load .b .a3 .a0 0, .logic .xor .t0 .t0 .a3,
    .store .b .t0 (outReg o) 0, .addi .a0 .a0 1, .addi .a1 .a1 1] ++ outStep o ++
    [.addi .a2 .a2 (-1)]

/-- One byte of the data at `X` XORed with the keystream at `K`, to `O`. -/
theorem xorStepWith_ok (o : Bool) (s : State) {K X O : Addr} {i n : Nat}
    (hk : s.gpr .a0 = K + BitVec.ofNat 64 i) (hx : s.gpr .a1 = X + BitVec.ofNat 64 i)
    (ho : s.gpr (outReg o) = O + BitVec.ofNat 64 i) (hn : s.gpr .a2 = BitVec.ofNat 64 (n - i))
    (rK : InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 i) 1)
    (rX : InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 i) 1)
    (w : InRegions s.wr (O + BitVec.ofNat 64 i) 1) :
    WP isa (.block (xorBodyWith o)) s fun s' =>
      s'.mem = s.mem.writeW (O + BitVec.ofNat 64 i)
        (s.mem (X + BitVec.ofNat 64 i) ^^^ s.mem (K + BitVec.ofNat 64 i)) ∧
      s'.gpr .a0 = K + BitVec.ofNat 64 (i + 1) ∧ s'.gpr .a1 = X + BitVec.ofNat 64 (i + 1) ∧
      s'.gpr (outReg o) = O + BitVec.ofNat 64 (i + 1) ∧
      s'.gpr .a2 = BitVec.ofNat 64 (n - i) - BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .t0 → r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → (o = true → r ≠ .a4) →
        s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have w' : InRegions (s.rd ++ s.wr) (O + BitVec.ofNat 64 i) 1 := in_left w
  cases o
  · simp only [outReg, Bool.false_eq_true, ↓reduceIte] at ho
    have e : X = O := by
      have := hx.symm.trans ho
      simpa using this
    subst e
    simp only [xorBodyWith, outReg, outStep, Bool.false_eq_true, ↓reduceIte, List.cons_append,
      List.nil_append, List.append_nil]
    crun [hk, hx, hn, rK, w, w', rd8x, write1, add_ofNat_assoc]
    intro r h₀ h₃ h₄ h₅ h₆ _; simp [h₀, h₃, h₄, h₅, h₆]
  · simp only [outReg, ↓reduceIte] at ho
    simp only [xorBodyWith, outReg, outStep, ↓reduceIte, List.cons_append, List.nil_append]
    crun [hk, hx, ho, hn, rK, rX, w, w', rd8x, write1, add_ofNat_assoc]
    intro r h₀ h₃ h₄ h₅ h₆ h₇
    have h₈ : r ≠ .a4 := by simpa using h₇
    simp [h₀, h₃, h₄, h₅, h₆, h₈]

/-- The bytes at `D` XORed with those at `S`. -/
def xorBytes (m : Mem) (D S : Addr) (n : Nat) : List Byte :=
  List.zipWith (· ^^^ ·) (bytesAt m D n) (bytesAt m S n)

theorem xorBytes_succ (m : Mem) (D S : Addr) (i : Nat) :
    xorBytes m D S (i + 1) = xorBytes m D S i ++ [m (D + BitVec.ofNat 64 i) ^^^ m (S + BitVec.ofNat 64 i)] := by
  simp [xorBytes, bytesAt_succ, List.zipWith_append, Cmac.bytesAt_length]

theorem length_xorBytes (m : Mem) (D S : Addr) (n : Nat) : (xorBytes m D S n).length = n := by
  simp [xorBytes, Cmac.bytesAt_length]

/-- Byte `i` of the destination, not yet written. -/
theorem dst_kept {m : Mem} {D : Addr} {n i : Nat} (hi : i < n) (hn : n < 2 ^ 64) (xs : List Byte)
    (hxs : xs.length = i) : writeBytes m D xs (D + BitVec.ofNat 64 i) = m (D + BitVec.ofNat 64 i) := by
  simp only [writeBytes, hxs, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega_arith), Nat.lt_irrefl, ite_false]

/-- Byte `i` of the data, not yet written over, in place or out of place. -/
theorem data_kept {o : Bool} {m : Mem} {X O : Addr} {n i : Nat} (ha : Alias o X O n) (hi : i < n)
    (hn : n < 2 ^ 64) (xs : List Byte) (hxs : xs.length = i) :
    writeBytes m O xs (X + BitVec.ofNat 64 i) = m (X + BitVec.ofNat 64 i) := by
  cases o
  · have e : X = O := ha
    subst e; exact dst_kept hi hn xs hxs
  · exact src_kept ha hi hn xs hxs

/-- What `xorLoopWith o` needs: the keystream at `K` (`a0`), `n` (at least
1) bytes of data at `X` (`a1`), written to `O` (`a4` out of place; in place
`X` itself). -/
structure XorPre (o : Bool) (s : State) (K X O : Addr) (n : Nat) : Prop where
  a0 : s.gpr .a0 = K
  a1 : s.gpr .a1 = X
  out : s.gpr (outReg o) = O
  a2 : s.gpr .a2 = BitVec.ofNat 64 n
  pos : 1 ≤ n
  lt : n < 2 ^ 64
  rdK : Covers [⟨K, n⟩] (s.rd ++ s.wr)
  rdX : Covers [⟨X, n⟩] (s.rd ++ s.wr)
  wr : Covers [⟨O, n⟩] s.wr
  disj : (⟨K, n⟩ : Region).Disjoint ⟨O, n⟩
  alias : Alias o X O n

/-- What `xorLoopWith o` leaves, but memory. -/
structure XorOut (o : Bool) (s : State) (K X O : Addr) (n : Nat) (s' : State) : Prop where
  a0 : s'.gpr .a0 = K + BitVec.ofNat 64 n
  a1 : s'.gpr .a1 = X + BitVec.ofNat 64 n
  out : s'.gpr (outReg o) = O + BitVec.ofNat 64 n
  a2 : s'.gpr .a2 = 0
  other : ∀ r, r ≠ .t0 → r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → (o = true → r ≠ .a4) →
    s'.gpr r = s.gpr r
  keeps : s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp

theorem xorLoopWith_ok (o : Bool) (s : State) {K X O : Addr} {n : Nat} (h : XorPre o s K X O n) :
    WP isa (xorLoopWith o) s fun s' =>
      s'.mem = writeBytes s.mem O (xorBytes s.mem X K n) ∧ XorOut o s K X O n s' := by
  have hn := h.lt
  refine WP.loop (M := isa) (body := .block (xorBodyWith o)) (c := .nonzero .a2)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .a0 = K + BitVec.ofNat 64 i ∧
      t.gpr .a1 = X + BitVec.ofNat 64 i ∧ t.gpr (outReg o) = O + BitVec.ofNat 64 i ∧
      t.gpr .a2 = BitVec.ofNat 64 (n - i) ∧
      t.mem = writeBytes s.mem O (xorBytes s.mem X K i) ∧
      (∀ r, r ≠ .t0 → r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → (o = true → r ≠ .a4) →
        t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp) ?_ (n - 0) _
    ⟨0, rfl, h.pos, by rw [h.a0, BitVec.add_zero], by rw [h.a1, BitVec.add_zero],
      by rw [h.out, BitVec.add_zero], by rw [h.a2]; rfl,
      by simp [xorBytes, bytesAt, writeBytes_nil], fun _ _ _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  rintro k t ⟨i, rfl, hi, r3, r4, ro, r5, mem, g, rd, wr, sp⟩
  refine WP.mono (xorStepWith_ok o t r3 r4 ro r5 (by rw [rd, wr]; exact in_of_covers h.rdK hi hn)
    (by rw [rd, wr]; exact in_of_covers h.rdX hi hn)
    (by rw [wr]; exact in_of_covers h.wr hi hn)) fun t' ⟨mem', r3', r4', ro', r5', g', rd', wr', sp'⟩ => ?_
  have hlen := length_xorBytes s.mem X K i
  have hmem : t'.mem = writeBytes s.mem O (xorBytes s.mem X K (i + 1)) := by
    rw [mem', mem, src_kept h.disj hi hn _ hlen, data_kept h.alias hi hn _ hlen, xorBytes_succ,
      writeBytes_snoc s.mem _ _ _ (by rw [hlen]; omega_arith), hlen]
  have gg : ∀ r, r ≠ .t0 → r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → (o = true → r ≠ .a4) →
      t'.gpr r = s.gpr r :=
    fun r h₀ h₃ h₄ h₅ h₆ h₇ => by rw [g' r h₀ h₃ h₄ h₅ h₆ h₇, g r h₀ h₃ h₄ h₅ h₆ h₇]
  have ev : isa.eval (.nonzero .a2) t' = some !decide (i + 1 = n) := by
    show some (t'.gpr .a2 != 0) = _
    rw [r5', dec64 hi hn, nz_dec hi hn]
  by_cases he : i + 1 = n
  · left
    refine ⟨by rw [ev]; simp [he], by rw [hmem, he], ⟨by rw [r3', he], by rw [r4', he], by rw [ro', he], ?_, gg,
      by rw [rd', rd], by rw [wr', wr], by rw [sp', sp]⟩⟩
    rw [r5', dec64 hi hn, he, Nat.sub_self]; rfl
  · right
    refine ⟨by rw [ev]; simp [he], n - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, r3', r4', ro',
      by rw [r5', dec64 hi hn], hmem, gg, by rw [rd', rd], by rw [wr', wr], by rw [sp', sp]⟩

/-- `xorLoop`: XORs the `n` bytes at `S` into those at `D`. -/
theorem xorLoop_ok (s : State) {S D : Addr} {n : Nat} (h : LoopPre s S D n) :
    WP isa xorLoop s fun s' =>
      s'.mem = writeBytes s.mem D (xorBytes s.mem D S n) ∧ LoopOut s S D n s' :=
  WP.mono (xorLoopWith_ok false s (K := S) (X := D) (O := D)
    ⟨h.a0, h.a1, h.a1, h.a2, h.pos, h.lt, h.rd, covers_left h.wr, h.wr, h.disj, rfl⟩)
    fun _ ⟨hm, lo⟩ => ⟨hm, lo.a0, lo.a1, lo.a2,
      fun r a b c d e => lo.other r a b c d e (fun h => Bool.noConfusion h), lo.keeps⟩

/-! ## `minLen` -/

theorem shr63 {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63 = if a < b then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := a) (by omega_arith), Nat.mod_eq_of_lt (a := b) (by omega_arith), Nat.shiftRight_eq_div_pow]
  split
  · rw [show (2 ^ 64 - b + a) % 2 ^ 64 = 2 ^ 64 - b + a by omega_arith]; simp; omega_arith
  · rw [show (2 ^ 64 - b + a) % 2 ^ 64 = a - b by omega_arith]; simp; omega_arith

/-- `a2 := min (16 - s6, s5)`. -/
theorem minLen_ok (s : State) {o n : Nat} (h26 : s.gpr .s6 = BitVec.ofNat 64 o)
    (h25 : s.gpr .s5 = BitVec.ofNat 64 n) (ho : o ≤ 16) (hn : n < 2 ^ 64) :
    WP isa minLen s fun s' => s'.gpr .a2 = BitVec.ofNat 64 (min (16 - o) n) ∧
      (∀ r, r ≠ .a2 → r ≠ .a3 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have e16 : BitVec.ofNat 64 16 - BitVec.ofNat 64 o = BitVec.ofNat 64 (16 - o) :=
    ofNat_sub64 ho (by decide)
  have h₁ : WP isa (.block [.li .a2 16, .sub .a2 .a2 .s6, .shift .srl .d .a3 .s5 4]) s
      (fun s₁ : State => s₁.gpr .a2 = BitVec.ofNat 64 (16 - o) ∧
        s₁.gpr .a3 = BitVec.ofNat 64 (n / 16) ∧ (∀ r, r ≠ .a2 → r ≠ .a3 → s₁.gpr r = s.gpr r) ∧
        Keeps s s₁) := by
    crun [h26, h25]
    exact ⟨e16, shr4 hn, fun r h₅ h₆ => by simp [h₅, h₆], ⟨rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.mono h₁ fun s₁ ⟨r5, r6, g, k⟩ => ?_)
  have hev : isa.eval (.nonzero .a3) s₁ = some (decide (16 ≤ n)) := by
    show some (s₁.gpr .a3 != 0) = _
    rw [r6]
    congr 1
    by_cases h : 16 ≤ n
    · have : BitVec.ofNat 64 (n / 16) ≠ 0 := fun e =>
        absurd ((ofNat_eq_zero (by omega_arith)).mp e) (by omega_arith)
      simp [h]; exact this
    · have : n / 16 = 0 := by omega_arith
      simp [h, this]
  refine WP.ite (decide (16 ≤ n)) hev (fun ht => ?_) (fun hf => ?_)
  · refine WP.block_nil ⟨?_, g, k⟩
    rw [r5, Nat.min_eq_left (by simp at ht; omega_arith)]
  · have hn16 : n < 16 := by simp at hf; omega_arith
    have h₂ : WP isa (.block [.sub .a3 .s5 .a2, .shift .srl .d .a3 .a3 63]) s₁
        (fun s₂ : State => s₂.gpr .a3 = (if n < 16 - o then 1 else 0) ∧
          (∀ r, r ≠ .a3 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂) := by
      crun [r5, g .s5 (by decide) (by decide), h25]
      exact ⟨shr63 (by omega_arith) (by omega_arith), fun r h₆ => by simp [h₆], ⟨rfl, rfl, rfl, rfl⟩⟩
    refine WP.seq (WP.mono h₂ fun s₂ ⟨r6', g', k'⟩ => ?_)
    have hev' : isa.eval (.nonzero .a3) s₂ = some (decide (n < 16 - o)) := by
      show some (s₂.gpr .a3 != 0) = _
      rw [r6']
      split <;> simp_all
    refine WP.ite (decide (n < 16 - o)) hev' (fun ht => ?_) (fun hf => ?_)
    · have h25' : s₂.gpr .s5 = BitVec.ofNat 64 n := by
        rw [g' .s5 (by decide), g .s5 (by decide) (by decide), h25]
      crun [h25', mov, BitVec.or_self]
      refine ⟨by rw [Nat.min_eq_right (by simp at ht; omega_arith)], fun r h₅ h₆ => ?_,
        k.trans k' |>.trans ⟨rfl, rfl, rfl, rfl⟩⟩
      simp only [h₅, ↓reduceIte]; rw [g' r h₆, g r h₅ h₆]
    · refine WP.block_nil ⟨?_, fun r h₅ h₆ => by rw [g' r h₆, g r h₅ h₆], k.trans k'⟩
      rw [g' .a2 (by decide), r5, Nat.min_eq_left (by simp at hf; omega_arith)]

end VG.Proof.AesGcm.RISCV64
