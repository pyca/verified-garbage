module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Env
public import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Cmac.Spec

/-!
# AES-GCM on PPC64LE: the byte loops and `minLen`

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcm/Arm/Loops.lean`): `copyLoop` copies `r5` bytes from `r3` to
`r4`, and `xorLoop` XORs `r5` bytes at `r3` into those at `r4`, a byte at a
time through advancing pointers, counting `r5` down to zero (`copyLoop_ok`,
`xorLoop_ok`); the buffers do not overlap. `minLen` leaves
`min (16 - r26, r25)` in `r5` (`minLen_ok`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE VG.WriteBytes
open VG.Spec.Aes (bytesAt)

theorem bytesAt_succ (m : Mem) (p : Addr) (i : Nat) :
    bytesAt m p (i + 1) = bytesAt m p i ++ [m (p + BitVec.ofNat 64 i)] := by
  simp [bytesAt, List.range_succ]

/-- Byte `i` of a region `⟨p, n⟩`, `i < n`, is in it. -/
theorem in_of_covers {rs : List Region} {p : Addr} {n i : Nat} (h : Covers [⟨p, n⟩] rs) (hi : i < n)
    (hn : n < 2 ^ 64) : InRegions rs (p + BitVec.ofNat 64 i) 1 :=
  h _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base p (by omega) (by omega)⟩

/-- What the loops need of the state: `n` (at least 1) bytes at `S` (read)
and `D` (written). -/
structure LoopPre (s : State) (S D : Addr) (n : Nat) : Prop where
  r3 : s.gpr .r3 = S
  r4 : s.gpr .r4 = D
  r5 : s.gpr .r5 = BitVec.ofNat 64 n
  pos : 1 ≤ n
  lt : n < 2 ^ 64
  rd : Covers [⟨S, n⟩] (s.rd ++ s.wr)
  wr : Covers [⟨D, n⟩] s.wr
  disj : (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩

/-- What the loops leave, but memory. -/
structure LoopOut (s : State) (S D : Addr) (n : Nat) (s' : State) : Prop where
  r3 : s'.gpr .r3 = S + BitVec.ofNat 64 n
  r4 : s'.gpr .r4 = D + BitVec.ofNat 64 n
  r5 : s'.gpr .r5 = 0
  other : ∀ r, r ≠ .r0 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → s'.gpr r = s.gpr r
  keeps : s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.lr = s.lr

theorem dec64 {n i : Nat} (hi : i < n) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 (n - i) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (n - (i + 1)) := by
  rw [ofNat_sub64 (by omega) (by omega)]; congr 1

theorem nz_dec {n i : Nat} (hi : i < n) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 (n - (i + 1)) != 0) = !decide (i + 1 = n) := by
  have := ofNat_eq_zero (n := n - (i + 1)) (by omega)
  by_cases h : i + 1 = n
  · simp [h]
  · have h' : BitVec.ofNat 64 (n - (i + 1)) ≠ 0 := fun e => h (by have := this.mp e; omega)
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
      exact hd _ (Offset.contains_base S (by omega) (by omega)) (Region.sub_prefix (by omega) _ hcon)

/-! ## `copyLoop` -/

abbrev copyBody : List Instr :=
  [.lbz .r0 .r3 0, .stb .r0 .r4 0, .addi .r3 .r3 1, .addi .r4 .r4 1, .subi .r5 .r5 1]

theorem copyStep_ok (s : State) {S D : Addr} {i n : Nat} (hs : s.gpr .r3 = S + BitVec.ofNat 64 i)
    (hd : s.gpr .r4 = D + BitVec.ofNat 64 i) (hn : s.gpr .r5 = BitVec.ofNat 64 (n - i))
    (r : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 i) 1)
    (w : InRegions s.wr (D + BitVec.ofNat 64 i) 1) :
    WP isa (.block copyBody) s fun s' =>
      s'.mem = s.mem.writeW (D + BitVec.ofNat 64 i) (s.mem (S + BitVec.ofNat 64 i)) ∧
      s'.gpr .r3 = S + BitVec.ofNat 64 (i + 1) ∧ s'.gpr .r4 = D + BitVec.ofNat 64 (i + 1) ∧
      s'.gpr .r5 = BitVec.ofNat 64 (n - i) - BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .r0 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.lr = s.lr := by
  crun [hs, hd, hn, r, w, rd8, write1, add_ofNat_assoc]
  intro r h₀ h₃ h₄ h₅; simp [h₀, h₃, h₄, h₅]

theorem copyLoop_ok (s : State) {S D : Addr} {n : Nat} (h : LoopPre s S D n) :
    WP isa copyLoop s fun s' => s'.mem = writeBytes s.mem D (bytesAt s.mem S n) ∧
      LoopOut s S D n s' := by
  have hn := h.lt
  refine WP.loop (M := isa) (body := .block copyBody) (c := .nonzero .d .r5)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .r3 = S + BitVec.ofNat 64 i ∧
      t.gpr .r4 = D + BitVec.ofNat 64 i ∧ t.gpr .r5 = BitVec.ofNat 64 (n - i) ∧
      t.mem = writeBytes s.mem D (bytesAt s.mem S i) ∧
      (∀ r, r ≠ .r0 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp ∧ t.lr = s.lr) ?_ (n - 0) _
    ⟨0, rfl, h.pos, by rw [h.r3, BitVec.add_zero], by rw [h.r4, BitVec.add_zero], by rw [h.r5]; rfl,
      by simp [bytesAt, writeBytes_nil], fun _ _ _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
  rintro k t ⟨i, rfl, hi, r3, r4, r5, mem, g, rd, wr, sp, lr⟩
  refine WP.mono (copyStep_ok t r3 r4 r5 (by rw [rd, wr]; exact in_of_covers h.rd hi hn)
    (by rw [wr]; exact in_of_covers h.wr hi hn)) fun t' ⟨mem', r3', r4', r5', g', rd', wr', sp', lr'⟩ => ?_
  have hlen : (bytesAt s.mem S i).length = i := by simp [bytesAt]
  have hmem : t'.mem = writeBytes s.mem D (bytesAt s.mem S (i + 1)) := by
    rw [mem', mem, src_kept h.disj hi hn _ hlen, bytesAt_succ,
      writeBytes_snoc s.mem _ (bytesAt s.mem _ i) _ (by rw [hlen]; omega), hlen]
  have gg : ∀ r, r ≠ .r0 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → t'.gpr r = s.gpr r :=
    fun r h₀ h₃ h₄ h₅ => by rw [g' r h₀ h₃ h₄ h₅, g r h₀ h₃ h₄ h₅]
  have ev : isa.eval (.nonzero .d .r5) t' = some !decide (i + 1 = n) := by
    show some _ = _
    simp only [State.read, Size.bits, BitVec.setWidth_eq, r5', dec64 hi hn, nz_dec hi hn]
  by_cases he : i + 1 = n
  · left
    refine ⟨by rw [ev]; simp [he], by rw [hmem, he], ⟨by rw [r3', he], by rw [r4', he], ?_,
      fun r h₀ h₃ h₄ h₅ _ => gg r h₀ h₃ h₄ h₅, by rw [rd', rd], by rw [wr', wr], by rw [sp', sp],
      by rw [lr', lr]⟩⟩
    rw [r5', dec64 hi hn, he, Nat.sub_self]; rfl
  · right
    refine ⟨by rw [ev]; simp [he], n - (i + 1), by omega, i + 1, rfl, by omega, r3', r4',
      by rw [r5', dec64 hi hn], hmem, gg, by rw [rd', rd], by rw [wr', wr], by rw [sp', sp],
      by rw [lr', lr]⟩

/-! ## `xorLoop` -/

abbrev xorBody : List Instr :=
  [.lbz .r0 .r4 0, .lbz .r6 .r3 0, .logic .xor .r0 .r0 .r6, .stb .r0 .r4 0,
    .addi .r3 .r3 1, .addi .r4 .r4 1, .subi .r5 .r5 1]

theorem xorStep_ok (s : State) {S D : Addr} {i n : Nat} (hs : s.gpr .r3 = S + BitVec.ofNat 64 i)
    (hd : s.gpr .r4 = D + BitVec.ofNat 64 i) (hn : s.gpr .r5 = BitVec.ofNat 64 (n - i))
    (r : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 i) 1)
    (w : InRegions s.wr (D + BitVec.ofNat 64 i) 1) :
    WP isa (.block xorBody) s fun s' =>
      s'.mem = s.mem.writeW (D + BitVec.ofNat 64 i)
        (s.mem (D + BitVec.ofNat 64 i) ^^^ s.mem (S + BitVec.ofNat 64 i)) ∧
      s'.gpr .r3 = S + BitVec.ofNat 64 (i + 1) ∧ s'.gpr .r4 = D + BitVec.ofNat 64 (i + 1) ∧
      s'.gpr .r5 = BitVec.ofNat 64 (n - i) - BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .r0 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.lr = s.lr := by
  have w' : InRegions (s.rd ++ s.wr) (D + BitVec.ofNat 64 i) 1 := in_left w
  crun [hs, hd, hn, r, w, w', rd8x, write1, add_ofNat_assoc]
  intro r h₀ h₃ h₄ h₅ h₆; simp [h₀, h₃, h₄, h₅, h₆]

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
    Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), Nat.lt_irrefl, ite_false]

theorem xorLoop_ok (s : State) {S D : Addr} {n : Nat} (h : LoopPre s S D n) :
    WP isa xorLoop s fun s' =>
      s'.mem = writeBytes s.mem D (xorBytes s.mem D S n) ∧ LoopOut s S D n s' := by
  have hn := h.lt
  refine WP.loop (M := isa) (body := .block xorBody) (c := .nonzero .d .r5)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .r3 = S + BitVec.ofNat 64 i ∧
      t.gpr .r4 = D + BitVec.ofNat 64 i ∧ t.gpr .r5 = BitVec.ofNat 64 (n - i) ∧
      t.mem = writeBytes s.mem D (xorBytes s.mem D S i) ∧
      (∀ r, r ≠ .r0 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.sp = s.sp ∧ t.lr = s.lr) ?_ (n - 0) _
    ⟨0, rfl, h.pos, by rw [h.r3, BitVec.add_zero], by rw [h.r4, BitVec.add_zero], by rw [h.r5]; rfl,
      by simp [xorBytes, bytesAt, writeBytes_nil], fun _ _ _ _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
  rintro k t ⟨i, rfl, hi, r3, r4, r5, mem, g, rd, wr, sp, lr⟩
  refine WP.mono (xorStep_ok t r3 r4 r5 (by rw [rd, wr]; exact in_of_covers h.rd hi hn)
    (by rw [wr]; exact in_of_covers h.wr hi hn)) fun t' ⟨mem', r3', r4', r5', g', rd', wr', sp', lr'⟩ => ?_
  have hlen := length_xorBytes s.mem D S i
  have hmem : t'.mem = writeBytes s.mem D (xorBytes s.mem D S (i + 1)) := by
    rw [mem', mem, src_kept h.disj hi hn _ hlen, dst_kept hi hn _ hlen, xorBytes_succ,
      writeBytes_snoc s.mem _ _ _ (by rw [hlen]; omega), hlen]
  have gg : ∀ r, r ≠ .r0 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → t'.gpr r = s.gpr r :=
    fun r h₀ h₃ h₄ h₅ h₆ => by rw [g' r h₀ h₃ h₄ h₅ h₆, g r h₀ h₃ h₄ h₅ h₆]
  have ev : isa.eval (.nonzero .d .r5) t' = some !decide (i + 1 = n) := by
    show some _ = _
    simp only [State.read, Size.bits, BitVec.setWidth_eq, r5', dec64 hi hn, nz_dec hi hn]
  by_cases he : i + 1 = n
  · left
    refine ⟨by rw [ev]; simp [he], by rw [hmem, he], ⟨by rw [r3', he], by rw [r4', he], ?_, gg,
      by rw [rd', rd], by rw [wr', wr], by rw [sp', sp], by rw [lr', lr]⟩⟩
    rw [r5', dec64 hi hn, he, Nat.sub_self]; rfl
  · right
    refine ⟨by rw [ev]; simp [he], n - (i + 1), by omega, i + 1, rfl, by omega, r3', r4',
      by rw [r5', dec64 hi hn], hmem, gg, by rw [rd', rd], by rw [wr', wr], by rw [sp', sp],
      by rw [lr', lr]⟩

/-! ## `minLen` -/

theorem shr63 {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63 = if a < b then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := a) (by omega), Nat.mod_eq_of_lt (a := b) (by omega), Nat.shiftRight_eq_div_pow]
  split
  · rw [show (2 ^ 64 - b + a) % 2 ^ 64 = 2 ^ 64 - b + a by omega]; simp; omega
  · rw [show (2 ^ 64 - b + a) % 2 ^ 64 = a - b by omega]; simp; omega

/-- `r5 := min (16 - r26, r25)`. -/
theorem minLen_ok (s : State) {o n : Nat} (h26 : s.gpr .r26 = BitVec.ofNat 64 o)
    (h25 : s.gpr .r25 = BitVec.ofNat 64 n) (ho : o ≤ 16) (hn : n < 2 ^ 64) :
    WP isa minLen s fun s' => s'.gpr .r5 = BitVec.ofNat 64 (min (16 - o) n) ∧
      (∀ r, r ≠ .r5 → r ≠ .r6 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have e16 : BitVec.ofNat 64 16 - BitVec.ofNat 64 o = BitVec.ofNat 64 (16 - o) :=
    ofNat_sub64 ho (by decide)
  have h₁ : WP isa (.block [.li .r5 16, .sub .r5 .r5 .r26, .lsr .d .r6 .r25 4]) s
      (fun s₁ : State => s₁.gpr .r5 = BitVec.ofNat 64 (16 - o) ∧
        s₁.gpr .r6 = BitVec.ofNat 64 (n / 16) ∧ (∀ r, r ≠ .r5 → r ≠ .r6 → s₁.gpr r = s.gpr r) ∧
        Keeps s s₁) := by
    crun [h26, h25]
    exact ⟨e16, shr4 hn, fun r h₅ h₆ => by simp [h₅, h₆], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.mono h₁ fun s₁ ⟨r5, r6, g, k⟩ => ?_)
  have hev : isa.eval (.nonzero .d .r6) s₁ = some (decide (16 ≤ n)) := by
    show some _ = _
    simp only [State.read, Size.bits, BitVec.setWidth_eq, r6]
    congr 1
    by_cases h : 16 ≤ n
    · have : BitVec.ofNat 64 (n / 16) ≠ 0 := fun e =>
        absurd ((ofNat_eq_zero (by omega)).mp e) (by omega)
      simp [h]; exact this
    · have : n / 16 = 0 := by omega
      simp [h, this]
  refine WP.ite (decide (16 ≤ n)) hev (fun ht => ?_) (fun hf => ?_)
  · refine WP.block_nil ⟨?_, g, k⟩
    rw [r5, Nat.min_eq_left (by simp at ht; omega)]
  · have hn16 : n < 16 := by simp at hf; omega
    have h₂ : WP isa (.block [.sub .r6 .r25 .r5, .lsr .d .r6 .r6 63]) s₁
        (fun s₂ : State => s₂.gpr .r6 = (if n < 16 - o then 1 else 0) ∧
          (∀ r, r ≠ .r6 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂) := by
      crun [r5, g .r25 (by decide) (by decide), h25]
      exact ⟨shr63 (by omega) (by omega), fun r h₆ => by simp [h₆], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
    refine WP.seq (WP.mono h₂ fun s₂ ⟨r6', g', k'⟩ => ?_)
    have hev' : isa.eval (.nonzero .d .r6) s₂ = some (decide (n < 16 - o)) := by
      show some _ = _
      simp only [State.read, Size.bits, BitVec.setWidth_eq, r6']
      split <;> simp_all
    refine WP.ite (decide (n < 16 - o)) hev' (fun ht => ?_) (fun hf => ?_)
    · have h25' : s₂.gpr .r25 = BitVec.ofNat 64 n := by
        rw [g' .r25 (by decide), g .r25 (by decide) (by decide), h25]
      crun [h25', mov, BitVec.or_self]
      refine ⟨by rw [Nat.min_eq_right (by simp at ht; omega)], fun r h₅ h₆ => ?_,
        k.trans k' |>.trans ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
      simp only [h₅, ↓reduceIte]; rw [g' r h₆, g r h₅ h₆]
    · refine WP.block_nil ⟨?_, fun r h₅ h₆ => by rw [g' r h₆, g r h₅ h₆], k.trans k'⟩
      rw [g' .r5 (by decide), r5, Nat.min_eq_left (by simp at hf; omega)]

end VG.Proof.AesGcm.PPC64LE
