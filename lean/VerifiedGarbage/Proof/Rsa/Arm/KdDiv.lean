module

public import VerifiedGarbage.Proof.Rsa.Arm.KdRun
public import VerifiedGarbage.Impl.Rsa.Arm.KeyDiv
public import VerifiedGarbage.Proof.Framework.Arm.Keep
public import VerifiedGarbage.Proof.Rsa.Arm.KeyWs
import VerifiedGarbage.Proof.Bignum.WordStep32
public import VerifiedGarbage.Proof.Rsa.Arm.KdStep
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.WordDiv
import VerifiedGarbage.Proof.Bignum.WordTop32

/-! # The key checks' division on ARMv7 (`KeyDiv.divW`): Algorithm D in place -/

@[expose] public section

/-! ## The reciprocal of the key checks' division on ARMv7 (`KeyDiv.recip`) -/

namespace VG.Proof.Rsa.Arm.KeyDiv

open VG VG.Arm VG.Impl.Rsa.Arm.KeyDiv
open VG.Proof.X25519.Arm (Rest)

theorem or_bits (c g : Bool) :
    ((0 : BitVec 32) + 0 + bif c then 1 else 0) ||| ((0 : BitVec 32) + 0 + bif g then 1 else 0) =
      bif c || g then 1 else 0 := by
  cases c <;> cases g <;> decide

theorem neg_bit_and (b : Bool) (x : BitVec 32) :
    (0 - bif b then (1 : BitVec 32) else 0) &&& x = bif b then x else 0 := by
  cases b
  · simp
  · show (0 - 1 : BitVec 32) &&& x = x
    rw [show (0 : BitVec 32) - 1 = BitVec.allOnes 32 by decide]; exact BitVec.allOnes_and

theorem divBit_ok {s : State} {r d q n : Nat} (h1 : s.gpr .r1 = BitVec.ofNat 32 d)
    (h2 : s.gpr .r2 = BitVec.ofNat 32 r) (h3 : s.gpr .r3 = BitVec.ofNat 32 q)
    (hl : s.gpr .lr = BitVec.ofNat 32 (n + 1)) (hr : r < d) (hd : d < 2 ^ 32) (hn : n + 1 < 2 ^ 32) :
    WP isa (.block divBit) s fun t =>
      t.gpr .r2 = BitVec.ofNat 32 (if d ≤ 2 * r + 1 then 2 * r + 1 - d else 2 * r + 1) ∧
      t.gpr .r3 = BitVec.ofNat 32 (2 * q + if d ≤ 2 * r + 1 then 1 else 0) ∧
      t.gpr .lr = BitVec.ofNat 32 n ∧ t.z = (n == 0) ∧ t.gpr .r1 = s.gpr .r1 ∧ t.mem = s.mem := by
  krun [divBit, h1, h2, h3, hl]
  have er : (BitVec.ofNat 32 r).toNat = r := by rw [BitVec.toNat_ofNat]; omega
  have ed : (BitVec.ofNat 32 d).toNat = d := by rw [BitVec.toNat_ofNat]; omega
  have e1 : (1 : BitVec 32).toNat = 1 := rfl
  have eR : (BitVec.ofNat 32 r + BitVec.ofNat 32 r + 1).toNat = (2 * r + 1) % 2 ^ 32 := by
    simp only [BitVec.toNat_add, er, e1]; omega
  have hb : (decide (2 ^ 32 ≤ (BitVec.ofNat 32 r).toNat + (BitVec.ofNat 32 r).toNat) ||
      decide ((BitVec.ofNat 32 d).toNat ≤ (BitVec.ofNat 32 r + BitVec.ofNat 32 r + 1).toNat)) =
      decide (d ≤ 2 * r + 1) := by
    rw [er, ed, eR]
    by_cases h : d ≤ 2 * r + 1
    · simp only [h, decide_true, Bool.or_eq_true, decide_eq_true_eq]; omega
    · simp only [h, decide_false, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
  simp only [or_bits, hb, neg_bit_and]
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    by_cases h : d ≤ 2 * r + 1
    · simp only [h, decide_true, Bool.cond_true, ite_true, BitVec.toNat_sub, eR, ed, BitVec.toNat_ofNat]; omega
    · simp only [h, decide_false, Bool.cond_false, ite_false, BitVec.toNat_sub, eR, BitVec.toNat_ofNat,
        show (0 : BitVec 32).toNat = 0 from rfl]; omega
  · apply BitVec.eq_of_toNat_eq
    by_cases h : d ≤ 2 * r + 1
    · simp only [h, decide_true, Bool.cond_true, ite_true, BitVec.toNat_add, BitVec.toNat_ofNat, e1]; omega
    · simp only [h, decide_false, Bool.cond_false, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat,
        show (0 : BitVec 32).toNat = 0 from rfl]; omega
  · apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  · have : BitVec.ofNat 32 (n + 1) - 1 = BitVec.ofNat 32 n := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    rw [this]
    by_cases h : n = 0
    · subst h; rfl
    · have : (BitVec.ofNat 32 n == 0) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; intro e
        have := congrArg BitVec.toNat e; simp at this; omega
      rw [this]; simp [h]

def rdiv (d j : Nat) : Nat := (2 ^ 32 - 1 - d) * 2 ^ j + (2 ^ j - 1)

theorem rdiv_succ (d j : Nat) : rdiv d (j + 1) = 2 * rdiv d j + 1 := by
  unfold rdiv
  generalize 2 ^ 32 - 1 - d = K
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ j) 2, ← Nat.mul_assoc, Nat.mul_comm K 2, Nat.mul_assoc]
  have := Nat.one_le_two_pow (n := j)
  omega

/-- The loop of `recip`: from `r = 2^32 - 1 - d`, `q = 0` and the count 32,
`q = ⌊rdiv d 32 / d⌋`. -/
theorem recipLoop_ok {s : State} {d : Nat} (hd' : d < 2 ^ 32) (hd0 : 2 ^ 31 ≤ d)
    (h2 : s.gpr .r2 = BitVec.ofNat 32 (2 ^ 32 - 1 - d)) (h1 : s.gpr .r1 = BitVec.ofNat 32 d)
    (h3 : s.gpr .r3 = BitVec.ofNat 32 0) (hl : s.gpr .lr = BitVec.ofNat 32 32) :
    WP isa (.loop (.block divBit) .ne) s fun t => t.gpr .r3 = BitVec.ofNat 32 (rdiv d 32 / d) ∧
      t.mem = s.mem ∧ Rest [.r2, .r3, .r4, .r5, .lr] s t := by
  refine WP.loop (M := isa) (fun n t => ∃ j q r, n = 32 - j ∧ j < 32 ∧ t.gpr .r2 = BitVec.ofNat 32 r ∧
      t.gpr .r3 = BitVec.ofNat 32 q ∧ t.gpr .r1 = BitVec.ofNat 32 d ∧ t.gpr .lr = BitVec.ofNat 32 (32 - j) ∧
      r < d ∧ rdiv d j = q * d + r ∧ t.mem = s.mem ∧ Rest [.r2, .r3, .r4, .r5, .lr] s t) ?_ _ s
    ⟨0, 0, 2 ^ 32 - 1 - d, rfl, by decide, h2, h3, h1, hl, by omega, by simp [rdiv], rfl,
      VG.Proof.X25519.Arm.Rest.refl _ _⟩
  rintro n t ⟨j, q, r, rfl, hj, h2', h3', h1', hl', hr, hP, hm, k⟩
  refine WP.mono (WP.keep [.r2, .r3, .r4, .r5, .lr]
    (divBit_ok (n := 31 - j) h1' h2' h3' (by rw [hl']; congr 1; omega) hr hd' (by omega)) (by decide))
    fun t' ⟨⟨e2, e3, el, ez, e1, hm'⟩, k'⟩ => ?_
  obtain ⟨hP', hr'⟩ := VG.Proof.Bignum.WordStep32.divBit_inv hP hr (show 1 < 2 by decide)
  rw [← rdiv_succ] at hP'
  have K := k.trans k'
  by_cases e : j + 1 = 32
  · refine .inl ⟨by simp only [eval, ez, show 31 - j = 0 by omega]; rfl, ?_, hm'.trans hm, K⟩
    have e32 : rdiv d 32 = (2 * q + if d ≤ 2 * r + 1 then 1 else 0) * d +
        (if d ≤ 2 * r + 1 then 2 * r + 1 - d else 2 * r + 1) := by rw [show (32 : Nat) = j + 1 by omega]; exact hP'
    have key : ∀ Q R, R < d → (Q * d + R) / d = Q := fun Q R h' => by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt h', Nat.zero_add]
    rw [e3, e32, key _ _ hr']
  · refine .inr ⟨by simp only [eval, ez]; simp; omega, 32 - (j + 1), by omega,
      j + 1, _, _, rfl, by omega, e2, e3, by rw [e1]; exact h1', by rw [el]; congr 1; omega, hr', hP',
      hm'.trans hm, K⟩

open VG.Proof.Rsa.Arm.Keys VG.Proof.Mont in
/-- `recip`: `v = ⌊(2^64 - 1) / d⌋ - 2^32` at 144, for `d ≥ 2^31` at 140. -/
theorem recip_ok {s : State} {B : BitVec 32} {Z w N d : Nat} (h : Ws s B Z w N)
    (hD : slot s.mem B sD = d) (hd1 : 2 ^ 31 ≤ d) (hd2 : d < 2 ^ 32) :
    WP isa recip s fun t => slot t.mem B sV = (2 ^ 64 - 1) / d - 2 ^ 32 ∧ Keep B w [] [sV] s.mem t.mem ∧
      Rest [.r1, .r2, .r3, .r4, .r5, .lr] s t := by
  have hz := h.hdr_le
  have aD := h.addr (d := sD) (by simp only [sD, VG.Impl.Rsa.Arm.Keys.hdr] at hz ⊢; omega)
  have rD := h.read (d := sD) (by simp only [sD, VG.Impl.Rsa.Arm.Keys.hdr] at hz ⊢; omega)
  have aV := h.addr (d := sV) (by simp only [sV, VG.Impl.Rsa.Arm.Keys.hdr] at hz ⊢; omega)
  have wV := h.write (d := sV) (by simp only [sV, VG.Impl.Rsa.Arm.Keys.hdr] at hz ⊢; omega)
  have vD : s.mem.readW (off (State.addr B) sD) 32 = BitVec.ofNat 32 d := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd2]; exact hD
  have mvn : ~~~(BitVec.ofNat 32 d) = BitVec.ofNat 32 (2 ^ 32 - 1 - d) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_not, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  rw [recip]
  simp only [VG.Impl.Rsa.Arm.Keys.seqs]
  rw [WP.seq_iff]
  refine WP.mono (WP.keep [.r1, .r2, .r3, .lr] (Q := fun u => u.gpr .r1 = BitVec.ofNat 32 d ∧
      u.gpr .r2 = BitVec.ofNat 32 (2 ^ 32 - 1 - d) ∧ u.gpr .r3 = BitVec.ofNat 32 0 ∧
      u.gpr .lr = BitVec.ofNat 32 32 ∧ u.mem = s.mem) (by
    krun [h.r8, aD, rD, vD, mvn]
    exact ⟨rfl, rfl⟩) (by decide)) fun u ⟨⟨u1, u2, u3, ul, um⟩, ku⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (recipLoop_ok hd2 hd1 u2 u1 u3 ul) fun t ⟨t3, tm, kt⟩ => ?_
  have r8t : t.gpr .r8 = B := by rw [kt.gpr _ (by decide), ku.gpr _ (by decide), h.r8]
  have wt : InRegions t.wr (off (State.addr B) sV) 4 := by rw [kt.wr, ku.wr]; exact wV
  have hq : rdiv d 32 / d = (2 ^ 64 - 1) / d - 2 ^ 32 := by
    rw [← VG.Proof.Bignum.WordStep32.recip_eq hd2 (by omega)]; rfl
  have hv32 : (2 ^ 64 - 1) / d - 2 ^ 32 < 2 ^ 32 := by
    have : (2 ^ 64 - 1) / d < 2 ^ 33 := by rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
    omega
  refine WP.mono (WP.keep [] (Q := fun v => v.mem = t.mem.writeW (off (State.addr B) sV) (t.gpr .r3)) (by
    krun [r8t, aV, wt]) (by decide)) fun v ⟨vm, kv⟩ => ⟨?_, ?_, ?_⟩
  · rw [vm, slot_write_self, t3, hq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv32]
  · rw [vm, tm, um]; exact keep_write _ _ (by simp) (by simp only [sV]; omega)
  · exact ((ku.mono (ws' := [.r1, .r2, .r3, .r4, .r5, .lr]) (by decide)).trans
      (kt.mono (by decide))).trans (kv.mono (by decide))

end VG.Proof.Rsa.Arm.KeyDiv

namespace VG.Proof.Rsa.Arm.KeyDiv

open VG VG.Arm VG.Impl.Rsa.Arm.KeyDiv VG.Proof.Rsa.Arm.Keys VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_cmp wp_dp wp_mov wp_str op2_imm op2_lsl op2_lsr op2_reg dpVal)
open VG.Impl.Rsa.Arm.Keys (copy ptr sub3)

/-! ## The arithmetic of the fold -/

/-- The window at word `j` before its step: the remainder of the words above it
shifted up a word, plus word `j` of `X`. -/
abbrev winY (X M j : Nat) : Nat := X / 2 ^ (32 * (j + 1)) % M * 2 ^ 32 + X / 2 ^ (32 * j) % 2 ^ 32

theorem winY_lt {X M j : Nat} (hM : 0 < M) : winY X M j < M * 2 ^ 32 := by
  have h1 := Nat.mod_lt (X / 2 ^ (32 * (j + 1))) hM
  have h2 := Nat.mod_lt (X / 2 ^ (32 * j)) (Nat.two_pow_pos 32)
  have := Nat.mul_le_mul_right (2 ^ 32) (show X / 2 ^ (32 * (j + 1)) % M + 1 ≤ M by omega)
  rw [Nat.add_mul, Nat.one_mul] at this
  simp only [winY]; omega

/-- A step: the window's remainder is that of the words from `j` (`WordStep.wordDiv_step`). -/
theorem winY_mod (X M j : Nat) : winY X M j % M = X / 2 ^ (32 * j) % M :=
  VG.Proof.Bignum.WordStep.wordDiv_step X M 32 j

/-- The value of `[r]` a word down: the words below `j` and the remainder of those from `j`. -/
theorem fold_next (X M j : Nat) :
    X % 2 ^ (32 * (j + 1)) + 2 ^ (32 * (j + 1)) * (X / 2 ^ (32 * (j + 1)) % M) =
      X % 2 ^ (32 * j) + 2 ^ (32 * j) * winY X M j := by
  have e1 : X % 2 ^ (32 * (j + 1)) = X % 2 ^ (32 * j) + 2 ^ (32 * j) * (X / 2 ^ (32 * j) % 2 ^ 32) := by
    rw [Nat.mul_succ, Nat.pow_add, Nat.mod_mul]
  have e2 : (2 : Nat) ^ (32 * (j + 1)) = 2 ^ (32 * j) * 2 ^ 32 := by rw [Nat.mul_succ, Nat.pow_add]
  simp only [winY]
  generalize X / 2 ^ (32 * (j + 1)) % M = A
  rw [e1, e2, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm (2 ^ 32) A]
  omega

/-- The start: below `M`, the words above `j` are their own remainder. -/
theorem fold_top {X M j : Nat} (h : X / 2 ^ (32 * (j + 1)) < M) :
    X % 2 ^ (32 * j) + 2 ^ (32 * j) * winY X M j = X := by
  simp only [winY]
  rw [Nat.mod_eq_of_lt h, ← VG.Proof.Bignum.WordStep.wordDiv_digits X 32 j, Nat.mod_add_div]

/-- Three parts of a number, from its value: the low `L < 2^K`, the middle `Y` of `J` bits and
the high `H = 0` when the whole is `L' + 2^K Y'` for `L' < 2^K` and `Y' < 2^J`. -/
theorem parts_unique {K J L Y H L' Y' : Nat} (hL : L < 2 ^ K) (hL' : L' < 2 ^ K)
    (hY' : Y' < 2 ^ J) (h : L + 2 ^ K * (Y + 2 ^ J * H) = L' + 2 ^ K * Y') : L = L' ∧ Y = Y' ∧ H = 0 := by
  have hK := Nat.two_pow_pos K
  have m1 := congrArg (· % 2 ^ K) h
  have d1 := congrArg (· / 2 ^ K) h
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hL, Nat.mod_eq_of_lt hL'] at m1
  simp only [Nat.add_mul_div_left _ _ hK, Nat.div_eq_of_lt hL, Nat.div_eq_of_lt hL', Nat.zero_add] at d1
  rcases Nat.eq_zero_or_pos H with h0 | h0
  · subst h0; exact ⟨m1, by omega, rfl⟩
  · have := Nat.mul_le_mul_left (2 ^ J) h0; omega

/-! ## Frames -/

/-- A frame widened to ranges that contain its own. -/
theorem Outs.widen {base : Addr} {rs rs' : List (Nat × Nat)} {m m' : Mem} (h : Outs base rs m m')
    (hr : ∀ r ∈ rs, ∃ r' ∈ rs', r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2) : Outs base rs' m m' := by
  intro x hx
  refine h x fun r hr' => ?_
  obtain ⟨r', hr'', h1, h2⟩ := hr r hr'
  have := hx r' hr''
  omega

/-- Words apart from a step's frame. -/
theorem step_val {B : BitVec 32} {w r t u j : Nat} {m m' : Mem}
    (F : Outs (State.addr B) (stepRanges w r t u j) m m') {o k : Nat}
    (ht : o + 4 * k ≤ arr w t ∨ arr w t + S w ≤ o) (hu : o + 4 * k ≤ arr w u ∨ arr w u + S w ≤ o)
    (hs : VG.Impl.Rsa.Arm.Keys.hdr ≤ o)
    (hwin : o + 4 * k ≤ arr w r + 4 * j ∨ arr w r + 4 * j + 4 * (w / 2 + 1) ≤ o) (fit : o + 4 * k ≤ 2 ^ 64) :
    val32 m' (State.addr B) o k = val32 m (State.addr B) o k := by
  refine Outs.val32 F (fun x hx => ?_) fit
  simp only [stepRanges, ranges, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with (⟨y, hy, rfl⟩ | ⟨d, hd, rfl⟩) | rfl
  · rcases hy with rfl | rfl
    · exact ht
    · exact hu
  · refine .inr ?_
    dsimp only
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [sMk, sQ, sU0, sU2, sJ, VG.Impl.Rsa.Arm.Keys.sC, VG.Impl.Rsa.Arm.Keys.hdr] at hs ⊢ <;> omega
  · exact hwin

/-- A header word apart from a step's frame. -/
theorem step_slot {B : BitVec 32} {w r t u j : Nat} {m m' : Mem}
    (F : Outs (State.addr B) (stepRanges w r t u j) m m') {e : Nat} (he : e + 4 ≤ VG.Impl.Rsa.Arm.Keys.hdr)
    (hd : ∀ d ∈ [sMk, sQ, sU0, sU2, VG.Impl.Rsa.Arm.Keys.sC, sJ], e + 4 ≤ d ∨ d + 4 ≤ e) :
    slot m' B e = slot m B e := by
  have := Outs.val32 (k := 1) (d := e) F (fun x hx => ?_) (by simp only [VG.Impl.Rsa.Arm.Keys.hdr] at he; omega)
  · simpa only [val32, Nat.mul_zero, Nat.add_zero] using this
  simp only [stepRanges, ranges, List.mem_append, List.mem_map] at hx
  rcases hx with (⟨y, -, rfl⟩ | ⟨d, hd', rfl⟩) | hx
  · have : VG.Impl.Rsa.Arm.Keys.hdr ≤ arr w y := Nat.le_add_right _ _; dsimp only; omega
  · exact hd d hd'
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx
    have : VG.Impl.Rsa.Arm.Keys.hdr ≤ arr w r := Nat.le_add_right _ _; dsimp only; omega

/-! ## The loop -/

/-- What the steps read and never change: `w` (16), `P = 2^z` normalizing `M = [m]`
(`w / 2` words), `d`, `d₁` and `v`, `[0]` zero and `[nm] = -M`. -/
structure Prepped (x : State) (B : BitVec 32) (w m nm z M : Nat) : Prop where
  c16 : slot x.mem B 16 = w
  hM : val32 x.mem (State.addr B) (arr w m) (w / 2) = M
  hz : z ≤ 31
  hP : slot x.mem B sP = 2 ^ z
  hMP : M * 2 ^ z < 2 ^ (32 * (w / 2))
  hD : slot x.mem B sD * 2 ^ 32 + slot x.mem B sD1 = M * 2 ^ z / 2 ^ (32 * (w / 2 - 2))
  hDn : 2 ^ 31 ≤ slot x.mem B sD
  hV : slot x.mem B sV = (2 ^ 64 - 1) / slot x.mem B sD - 2 ^ 32
  z0 : val32 x.mem (State.addr B) (arr w 0) (w / 2 + 1) = 0
  hnm : val32 x.mem (State.addr B) (arr w nm) (w / 2 + 1) = 2 ^ (32 * (w / 2 + 1)) - M

theorem Prepped.step {x x' : State} {B : BitVec 32} {Z w N r m t nm u z M j : Nat} (p : Prepped x B w m nm z M)
    (h : Ws x B Z w N) (hm : m < N) (hnm : nm < N) (hN : N ≤ 256) (hmr : m ≠ r) (hmt : m ≠ t) (hmu : m ≠ u)
    (hr0 : r ≠ 0) (ht0 : t ≠ 0) (hu0 : u ≠ 0) (hnr : nm ≠ r) (hnt : nm ≠ t) (hnu : nm ≠ u)
    (hj : j + w / 2 ≤ w) (F : Outs (State.addr B) (stepRanges w r t u j) x.mem x'.mem) :
    Prepped x' B w m nm z M := by
  have := h.wle
  have gm := h.fit64 hm
  have g0 := h.fit64 (j := 0) (by omega)
  have gn := h.fit64 hnm
  have dmr := arr_disj (w := w) hmr
  have dmt := arr_disj (w := w) hmt
  have dmu := arr_disj (w := w) hmu
  have d0r := arr_disj (w := w) hr0
  have d0t := arr_disj (w := w) ht0
  have d0u := arr_disj (w := w) hu0
  have dnr := arr_disj (w := w) hnr
  have dnt := arr_disj (w := w) hnt
  have dnu := arr_disj (w := w) hnu
  simp only [S] at gm g0 gn dmr dmt dmu d0r d0t d0u dnr dnt dnu
  have sl : ∀ {e}, e + 4 ≤ VG.Impl.Rsa.Arm.Keys.hdr →
      (∀ d ∈ [sMk, sQ, sU0, sU2, VG.Impl.Rsa.Arm.Keys.sC, sJ], e + 4 ≤ d ∨ d + 4 ≤ e) →
      slot x'.mem B e = slot x.mem B e := fun he hd => step_slot F he hd
  have hs : ∀ a, VG.Impl.Rsa.Arm.Keys.hdr ≤ arr w a := fun _ => Nat.le_add_right _ _
  refine ⟨?_, ?_, p.hz, ?_, p.hMP, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sl (by decide) (by decide)]; exact p.c16
  · rw [step_val F (by simp only [S]; omega) (by simp only [S]; omega) (hs m) (by omega) (by omega)]; exact p.hM
  · rw [sl (by decide) (by decide)]; exact p.hP
  · rw [sl (by decide) (by decide), sl (by decide) (by decide)]; exact p.hD
  · rw [sl (by decide) (by decide)]; exact p.hDn
  · rw [sl (by decide) (by decide), sl (by decide) (by decide)]; exact p.hV
  · rw [step_val F (by simp only [S]; omega) (by simp only [S]; omega) (hs 0) (by omega) (by omega)]; exact p.z0
  · rw [step_val F (by simp only [S]; omega) (by simp only [S]; omega) (hs nm) (by omega) (by omega)]; exact p.hnm

theorem Prepped.M_pos {x : State} {B : BitVec 32} {w m nm z M : Nat} (p : Prepped x B w m nm z M) : 0 < M :=
  Nat.pos_of_ne_zero fun e => by
    have hD := p.hD
    rw [e, Nat.zero_mul, Nat.zero_div] at hD
    have := Nat.mul_le_mul_right (2 ^ 32) p.hDn; omega

theorem Prepped.M_lt {x : State} {B : BitVec 32} {w m nm z M : Nat} (p : Prepped x B w m nm z M) :
    M < 2 ^ (32 * (w / 2)) :=
  Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)) p.hMP

/-- The loop's invariant at the window at word `j`: `[r]`'s `w + 1` words are `X`'s below `j`
and `winY X M j` from `j`; `Prepped`; and only `[r]`, `[t]`, `[u]` and the steps' header words
changed since `s0`. -/
structure DivSt (s0 x : State) (B : BitVec 32) (Z w N r m t nm u z M X j : Nat) : Prop where
  ws : Ws x B Z w N
  pre : Prepped x B w m nm z M
  J : slot x.mem B sJ = 4 * j
  hj : j + w / 2 ≤ w
  val : val32 x.mem (State.addr B) (arr w r) (w + 1) = X % 2 ^ (32 * j) + 2 ^ (32 * j) * winY X M j
  keep : Keep B w [r, t, u] [sMk, sQ, sU0, sU2, VG.Impl.Rsa.Arm.Keys.sC, sJ] s0.mem x.mem
  rest : Rest divRegs s0 x

/-- A step from the invariant: the remainder of `X`'s words from `j` there. -/
theorem stepD_ok {s0 x : State} {B : BitVec 32} {Z w N r m t nm u z M X j : Nat}
    (I : DivSt s0 x B Z w N r m t nm u z M X j) (hr : r < N) (hm : m < N) (ht : t < N) (hnm : nm < N)
    (hu : u < N) (hN : N ≤ 256) (hrt : r ≠ t) (hru : r ≠ u) (htu : t ≠ u) (hmr : m ≠ r) (hmt : m ≠ t)
    (hmu : m ≠ u) (hnr : nm ≠ r) (htn : t ≠ nm) (hnu : nm ≠ u) (hr0 : r ≠ 0) (ht0 : t ≠ 0) (hu0 : u ≠ 0)
    (hdw : 3 ≤ w / 2) :
    WP isa (step r m t nm u) x fun x' => Ws x' B Z w N ∧ Prepped x' B w m nm z M ∧
      slot x'.mem B sJ = (BitVec.ofNat 32 (4 * j) - 4).toNat ∧
      val32 x'.mem (State.addr B) (arr w r) (w + 1) = X % 2 ^ (32 * j) + 2 ^ (32 * j) * (X / 2 ^ (32 * j) % M) ∧
      Keep B w [r, t, u] [sMk, sQ, sU0, sU2, VG.Impl.Rsa.Arm.Keys.sC, sJ] s0.mem x'.mem ∧ Rest divRegs s0 x' := by
  have := I.ws.wle
  have hj := I.hj
  have gr := I.ws.fit64 hr
  have dt := arr_disj (w := w) hrt
  have du := arr_disj (w := w) hru
  simp only [S] at gr dt du
  have hM0 := I.pre.M_pos
  have hMl := I.pre.M_lt
  have hWY : winY X M j < 2 ^ (32 * (w / 2 + 1)) := by
    have := winY_lt (X := X) (j := j) hM0
    rw [show 32 * (w / 2 + 1) = 32 * (w / 2) + 32 by omega, Nat.pow_add]
    exact Nat.lt_of_lt_of_le this (Nat.mul_le_mul_right _ (Nat.le_of_lt hMl))
  have e1 : w + 1 = j + ((w / 2 + 1) + (w - j - w / 2)) := by omega
  have dec := I.val
  rw [e1, val32_append, val32_append] at dec
  obtain ⟨-, hwin, hhigh⟩ := parts_unique (val32_lt _ _ _ _) (Nat.mod_lt _ (Nat.two_pow_pos _)) hWY dec
  refine WP.mono (step_ok I.ws hr hm ht hnm hu hN hrt hru htu hmt htn hnu ht0 hu0 I.pre.c16 hdw I.J hj hwin
    I.pre.hM (winY_lt hM0) I.pre.hz I.pre.hP I.pre.hMP I.pre.hD I.pre.hDn I.pre.hV I.pre.z0 I.pre.hnm)
    fun x' ⟨W', V', J', F', R'⟩ => ⟨W', I.pre.step I.ws hm hnm hN hmr hmt hmu hr0 ht0 hu0 hnr htn.symm hnu hj F',
      J', ?_, ?_, I.rest.trans R'⟩
  · have hs : VG.Impl.Rsa.Arm.Keys.hdr ≤ arr w r := Nat.le_add_right _ _
    have hlow := I.val
    rw [e1, val32_append, val32_append, V', winY_mod,
      step_val F' (o := arr w r) (k := j) (by simp only [S]; omega) (by simp only [S]; omega) hs (by omega)
        (by omega),
      step_val F' (o := arr w r + 4 * j + 4 * (w / 2 + 1)) (k := w - j - w / 2) (by simp only [S]; omega)
        (by simp only [S]; omega) (by omega) (by omega) (by omega), hhigh]
    rw [e1, val32_append, val32_append, hhigh, hwin] at hlow
    obtain ⟨hl, -, -⟩ := parts_unique (val32_lt _ _ _ _) (Nat.mod_lt _ (Nat.two_pow_pos _)) hWY hlow
    rw [hl, Nat.mul_zero, Nat.add_zero]
  · refine I.keep.trans (show Keep B w [r, t, u] _ x.mem x'.mem from Outs.widen F' fun q hq => ?_)
    simp only [stepRanges, ranges, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
      or_false] at hq ⊢
    rcases hq with (⟨y, hy, rfl⟩ | ⟨d, hd, rfl⟩) | rfl
    · exact ⟨_, .inl ⟨y, by rcases hy with rfl | rfl <;> simp, rfl⟩, Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, .inr ⟨d, hd, rfl⟩, Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, .inl ⟨r, by simp, rfl⟩, by dsimp only; omega, by dsimp only; simp only [S]; omega⟩

theorem Prepped.of_mem {x x' : State} {B : BitVec 32} {w m nm z M : Nat} (p : Prepped x B w m nm z M)
    (e : x'.mem = x.mem) : Prepped x' B w m nm z M := by
  obtain ⟨a, b, c, d, f, g, i, k, l, n⟩ := p
  exact ⟨e ▸ a, e ▸ b, c, e ▸ d, f, e ▸ g, e ▸ i, e ▸ k, e ▸ l, e ▸ n⟩

/-- The window from the invariant. -/
theorem DivSt.window {s0 x : State} {B : BitVec 32} {Z w N r m t nm u z M X j : Nat}
    (I : DivSt s0 x B Z w N r m t nm u z M X j) :
    val32 x.mem (State.addr B) (arr w r + 4 * j) (w / 2 + 1) = winY X M j := by
  have hj := I.hj
  have hM0 := I.pre.M_pos
  have hMl := I.pre.M_lt
  have hWY : winY X M j < 2 ^ (32 * (w / 2 + 1)) := by
    have := winY_lt (X := X) (j := j) hM0
    rw [show 32 * (w / 2 + 1) = 32 * (w / 2) + 32 by omega, Nat.pow_add]
    exact Nat.lt_of_lt_of_le this (Nat.mul_le_mul_right _ (Nat.le_of_lt hMl))
  have e1 : w + 1 = j + ((w / 2 + 1) + (w - j - w / 2)) := by omega
  have dec := I.val
  rw [e1, val32_append, val32_append] at dec
  exact (parts_unique (val32_lt _ _ _ _) (Nat.mod_lt _ (Nat.two_pow_pos _)) hWY dec).2.1

/-- The estimate's frame from the invariant: `Ws`, `w` and the offset. -/
theorem DivSt.est {s0 x : State} {B : BitVec 32} {Z w N r m t nm u z M X j : Nat}
    (I : DivSt s0 x B Z w N r m t nm u z M X j) (hr : r < N) (hN : N ≤ 256) (hdw : 3 ≤ w / 2) :
    WP isa (.block (estimate r)) x fun v => Ws v B Z w N ∧ slot v.mem B 16 = w ∧ slot v.mem B sJ = 4 * j := by
  rw [← List.append_nil (estimate r)]
  exact estimate_ok I.ws hr hN I.pre.c16 hdw I.J I.hj I.window (winY_lt I.pre.M_pos) I.pre.hz I.pre.hP
    I.pre.hMP I.pre.hD I.pre.hDn I.pre.hV fun t q _ _ _ _ K W _ => WP.block_nil ⟨W,
      by rw [K.slot (by decide) (by decide)]; exact I.pre.c16, by rw [K.slot (by decide) (by decide)]; exact I.J⟩

/-- The loop's body: the step, and the condition: not zero unless `j = 1`, then the invariant
a word down. -/
theorem body_ok {s0 x : State} {B : BitVec 32} {Z w N r m t nm u z M X n : Nat}
    (In : DivSt s0 x B Z w N r m t nm u z M X n) (hn : 1 ≤ n) (hr : r < N) (hm : m < N) (ht : t < N)
    (hnm : nm < N) (hu : u < N) (hN : N ≤ 256) (hrt : r ≠ t) (hru : r ≠ u) (htu : t ≠ u) (hmr : m ≠ r)
    (hmt : m ≠ t) (hmu : m ≠ u) (hnr : nm ≠ r) (htn : t ≠ nm) (hnu : nm ≠ u) (hr0 : r ≠ 0) (ht0 : t ≠ 0)
    (hu0 : u ≠ 0) (hdw : 3 ≤ w / 2) :
    WP isa (.seq (step r m t nm u) (.block [.ldr .r0 .r8 sJ, .cmp .r0 (.imm 0)])) x fun y =>
      isa.eval .ne y = some (!decide (n = 1)) ∧ DivSt s0 y B Z w N r m t nm u z M X (n - 1) := by
  have := In.ws.wle
  have hjn := In.hj
  rw [WP.seq_iff]
  refine WP.mono (stepD_ok In hr hm ht hnm hu hN hrt hru htu hmr hmt hmu hnr htn hnu hr0 ht0 hu0 hdw)
    fun y1 ⟨W1, P1, J1, V1, K1, R1⟩ => ?_
  refine wp_ldrSlot W1 (d := sJ) (by decide) fun y2 u2 => ?_
  refine wp_cmp (op2_imm (by decide)) fun y3 f3 hz3 => WP.block_nil ?_
  have r0v : y2.gpr .r0 = BitVec.ofNat 32 (4 * n) - 4 := by
    rw [u2.gpr]; apply BitVec.eq_of_toNat_eq; exact J1
  have e4 : (BitVec.ofNat 32 (4 * n) - 4).toNat = 4 * (n - 1) := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, show (4 : BitVec 32).toNat = 4 from rfl]; omega
  have m3 : y3.mem = y1.mem := f3.mem.trans u2.mem
  have W3 : Ws y3 B Z w N := (W1.of_upd u2 (by decide) (by decide) (by decide)).of (by rw [f3.gpr])
    (by rw [f3.gpr]) (by rw [f3.gpr]) f3.wr
  have R3 : Rest divRegs s0 y3 := R1.trans ((u2.rest (by decide)).trans (f3.rest _))
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  refine ⟨?_, W3, P1.of_mem m3, ?_, by omega, ?_, by rw [m3]; exact K1, R3⟩
  · change some (!y3.z) = some (!decide (k + 1 = 1))
    rw [hz3, r0v, show BitVec.ofNat 32 (4 * (k + 1)) - 4 - 0 = BitVec.ofNat 32 (4 * (k + 1)) - 4 from
      BitVec.sub_zero _]
    by_cases e : k = 0
    · subst e; decide
    · have : BitVec.ofNat 32 (4 * (k + 1)) - 4 ≠ 0 := fun e' => by
        have := congrArg BitVec.toNat e'; rw [e4] at this; simp at this; omega
      rw [show (BitVec.ofNat 32 (4 * (k + 1)) - 4 == 0) = false from beq_eq_false_iff_ne.mpr this]
      simp [e]
  · simp only [slot]; rw [m3]; simp only [slot] at J1; rw [J1, e4]
  · rw [m3, V1, Nat.add_sub_cancel, fold_next]

/-- The loop: the steps at words `j`, …, `1`, while the window's offset, a word down, is not zero. -/
theorem loop_ok {s0 x : State} {B : BitVec 32} {Z w N r m t nm u z M X j : Nat}
    (I : DivSt s0 x B Z w N r m t nm u z M X j) (hj1 : 1 ≤ j) (hr : r < N) (hm : m < N) (ht : t < N)
    (hnm : nm < N) (hu : u < N) (hN : N ≤ 256) (hrt : r ≠ t) (hru : r ≠ u) (htu : t ≠ u) (hmr : m ≠ r)
    (hmt : m ≠ t) (hmu : m ≠ u) (hnr : nm ≠ r) (htn : t ≠ nm) (hnu : nm ≠ u) (hr0 : r ≠ 0) (ht0 : t ≠ 0)
    (hu0 : u ≠ 0) (hdw : 3 ≤ w / 2) :
    WP isa (.loop (.seq (step r m t nm u) (.block [.ldr .r0 .r8 sJ, .cmp .r0 (.imm 0)])) .ne) x
      fun y => DivSt s0 y B Z w N r m t nm u z M X 0 := by
  refine WP.loop (M := isa) (fun n y => DivSt s0 y B Z w N r m t nm u z M X n ∧ 1 ≤ n) ?_ j x ⟨I, hj1⟩
  rintro n y ⟨In, hn⟩
  refine WP.mono (body_ok In hn hr hm ht hnm hu hN hrt hru htu hmr hmt hmu hnr htn hnu hr0 ht0 hu0 hdw)
    fun y' ⟨c, I'⟩ => ?_
  by_cases e : n = 1
  · left; subst e; exact ⟨by rw [c]; rfl, I'⟩
  · right; exact ⟨by rw [c]; simp [e], n - 1, by omega, I', by omega⟩

/-! ## The preparation -/

theorem shl2_val {w : Nat} (_hw : w ≤ 1024) : BitVec.ofNat 32 w <<< 2 = BitVec.ofNat 32 (4 * w) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

/-- The low `k` words of a number of `n` words. -/
theorem val32_low (mem : Mem) (base : Addr) (d : Nat) {k n : Nat} (h : k ≤ n) :
    val32 mem base d k = val32 mem base d n % 2 ^ (32 * k) := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [val32_append, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (val32_lt _ _ _ _)]

/-- `-M` modulo a shorter power: `(2^(32 n) - M) mod 2^(32 k) = 2^(32 k) - M` for `0 < M < 2^(32 k)`. -/
theorem neg_low {M k n : Nat} (hkn : k ≤ n) (hM0 : 0 < M) (hM : M < 2 ^ (32 * k)) :
    (2 ^ (32 * n) - M) % 2 ^ (32 * k) = 2 ^ (32 * k) - M := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hkn
  rw [Nat.mul_add, Nat.pow_add]
  have hE := Nat.two_pow_pos (32 * e)
  obtain ⟨E, hE'⟩ : ∃ E, 2 ^ (32 * e) = E + 1 := ⟨2 ^ (32 * e) - 1, by omega⟩
  rw [hE', Nat.mul_add, Nat.mul_one, show 2 ^ (32 * k) * E + 2 ^ (32 * k) - M = (2 ^ (32 * k) - M) + 2 ^ (32 * k) * E
    by omega, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- The preparation's first half: `[r] := [a]` with word `w` zero, and `[nm] := -[m]`. -/
theorem prepA_ok {s : State} {B : BitVec 32} {Z w N a r m nm : Nat} (h : Ws s B Z w N) (ha : a < N) (hr : r < N)
    (hm : m < N) (hnm : nm < N) (hN : N ≤ 256) (hra : r ≠ a) (hr0 : r ≠ 0) (hrm : r ≠ m) (hn0 : nm ≠ 0)
    (hnm' : nm ≠ m) (hnr : nm ≠ r) {M : Nat} (hM : num s.mem B w m = M) (hM0 : 0 < M)
    (hz : num s.mem B w 0 = 0) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ v, Ws v B Z w N → val32 v.mem (State.addr B) (arr w r) (w + 1) = num s.mem B w a →
      num v.mem B w nm = 2 ^ (32 * w) - M → Keep B w [r, nm] [] s.mem v.mem → Rest opRegs s v →
      WP isa rest v Q) :
    WP isa (.seq (copy r a) (.seq (.block (ptr .r0 r ++ ([.dp .add .r0 .r0 (.shifted .r9 .lsl 2),
      .mov .r1 (.imm 0), .str .r1 .r0 0] : List Instr))) (.seq (sub3 nm 0 m) rest))) s Q := by
  have := h.wle
  have nw := h.nowrap
  have fr := h.arr_fit hr
  have gr := h.fit64 hr
  have g0 := h.fit64 (j := 0) (by omega)
  have gm := h.fit64 hm
  simp only [S] at fr gr g0 gm
  rw [WP.seq_iff]
  refine WP.mono (copy_ok h hr ha hN hra) fun v1 ⟨W1, K1, C1, R1, _⟩ => ?_
  rw [WP.seq_iff]
  refine ptr_ok W1 (r := .r0) (by decide) (j := r) (by omega) fun v2 p2 r2 m2 W2 => ?_
  refine wp_dp (op2_lsl (by decide)) fun v3 u3 => ?_
  refine wp_mov (op2_imm (by decide)) fun v4 u4 => ?_
  have a4 : State.addr (v4.gpr .r0 + BitVec.ofNat 32 0) = off (State.addr B) (arr w r + 4 * w) := by
    rw [u4.other _ (by decide), u3.gpr, dpVal, p2, W2.r9, shl2_val (by omega), BitVec.add_zero, add_ofNat_assoc]
    exact h.addr (by omega)
  refine wp_str (by decide) a4 (by rw [u4.wr, u3.wr, r2.wr, R1.wr]; exact h.write (by omega))
    fun v5 u5 => WP.block_nil ?_
  have W5 : Ws v5 B Z w N := ((W2.of_upd u3 (by decide) (by decide) (by decide)).of_upd u4 (by decide) (by decide)
    (by decide)).of_mupd u5
  have m5 : v5.mem = v1.mem.writeW (off (State.addr B) (arr w r + 4 * w)) (0 : BitVec 32) := by
    rw [u5.mem, u4.gpr, u4.mem, u3.mem, m2]
  have K5 : Keep B w [r] [] s.mem v5.mem := by
    rw [m5]; exact K1.trans (Keep.of_arr (d := 4 * w) (writeW32_outside _ _ _ (by omega)) (by simp only [S]; omega)
      (by simp))
  have V5 : val32 v5.mem (State.addr B) (arr w r) (w + 1) = num s.mem B w a := by
    rw [val32_succ, m5, w32_write_self, Outside.val32 (writeW32_outside _ _ _ (by omega)) (by omega) (by omega)]
    simp only [num] at C1 ⊢
    rw [C1]; rfl
  have R5 : Rest opRegs s v5 :=
    R1.trans ((r2.mono (by simp)).trans ((u3.rest (by simp)).trans ((u4.rest (by simp)).trans (u5.rest _))))
  rw [WP.seq_iff]
  refine WP.mono (sub3_ok W5 hnm (by omega) hm hN hn0 hnm') fun v6 ⟨W6, K6, E6, b6, R6⟩ => ?_
  have Z5 : num v5.mem B w 0 = 0 := by rw [K5.num (by simpa using hr0) (by simp) g0]; exact hz
  have M5 : num v5.mem B w m = M := by rw [K5.num (by simpa using hrm) (by simp) gm]; exact hM
  rw [Z5, M5] at E6
  have hb : (v6.gpr .r11).toNat = 1 := by
    rcases Nat.lt_or_ge (v6.gpr .r11).toNat 1 with h0 | h1
    · have : (v6.gpr .r11).toNat = 0 := by omega
      rw [this] at E6; omega
    · omega
  rw [hb, Nat.mul_one] at E6
  refine k v6 W6 ?_ (by omega) ((K5.mono).trans K6.mono) (R5.trans R6)
  rw [Outs.val32 K6 (fun q hq => ?_) (by omega)]
  · exact V5
  · simp only [ranges, List.mem_map, List.mem_cons, List.not_mem_nil, or_false,
      List.map_nil, List.append_nil] at hq
    obtain ⟨y, rfl, rfl⟩ := hq
    have := arr_disj (w := w) hnr; simp only [S] at this ⊢; omega

open VG.Proof.Bignum.NormMask32 VG.Proof.Bignum.WordTop32 in
/-- The normalization's arithmetic, for `M`'s top three words `T ≠ 0`, `U`, `V` and `z = lz T`:
`M 2^z` fits, its top two words are `norm`'s `d` and `d₁`, `d` has its top bit set, and `M`
is at least `2^(32 (k + 2))`. -/
theorem norm_math {M k T U V L : Nat}
    (hM : M = L + 2 ^ (32 * k) * V + 2 ^ (32 * k) * 2 ^ 32 * (U + 2 ^ 32 * T)) (hL : L < 2 ^ (32 * k))
    (hV : V < 2 ^ 32) (hU : U < 2 ^ 32) (hT0 : 0 < T) (hT : T < 2 ^ 32) :
    M * 2 ^ lz T < 2 ^ (32 * (k + 3)) ∧
      (T * 2 ^ lz T + U * 2 ^ lz T / 2 ^ 32) * 2 ^ 32 + (U * 2 ^ lz T % 2 ^ 32 + V * 2 ^ lz T / 2 ^ 32) =
        M * 2 ^ lz T / 2 ^ (32 * (k + 1)) ∧
      2 ^ 31 ≤ T * 2 ^ lz T + U * 2 ^ lz T / 2 ^ 32 ∧ 2 ^ (32 * (k + 2)) ≤ M ∧ lz T ≤ 31 := by
  obtain ⟨b1, b2⟩ := shifted_bounds hT0 hT (Nat.le_refl (lz T))
  simp only [↓reduceIte] at b2
  have hz : lz T ≤ 31 := by unfold lz; omega
  have b3 : 2 ^ 31 ≤ T * 2 ^ lz T := by
    have := Nat.div_mul_le_self (T * 2 ^ lz T) (2 ^ 31); rw [b2, Nat.one_mul] at this
    refine Nat.le_of_not_lt fun hc => ?_
    rw [Nat.div_eq_of_lt hc] at b2; exact absurd b2 (by decide)
  have e2 : 2 ^ (32 * (k + 2)) = 2 ^ (32 * k) * 2 ^ 32 * 2 ^ 32 := by
    rw [show 32 * (k + 2) = 32 * k + 32 + 32 by omega, Nat.pow_add, Nat.pow_add]
  have hlow : L + 2 ^ (32 * k) * V + 2 ^ (32 * k) * 2 ^ 32 * U < 2 ^ (32 * (k + 2)) := by
    rw [e2]
    have h1 := Nat.mul_le_mul_left (2 ^ (32 * k)) (show V + 1 ≤ 2 ^ 32 by omega)
    have h2 := Nat.mul_le_mul_left (2 ^ (32 * k) * 2 ^ 32) (show U + 1 ≤ 2 ^ 32 by omega)
    rw [Nat.mul_add, Nat.mul_one] at h1 h2
    omega
  have hM' : M = (L + 2 ^ (32 * k) * V + 2 ^ (32 * k) * 2 ^ 32 * U) + 2 ^ (32 * (k + 2)) * T := by
    rw [hM, e2, Nat.mul_add, Nat.mul_assoc (2 ^ (32 * k) * 2 ^ 32) (2 ^ 32)]; omega
  -- `(T + 1) 2^z ≤ 2^32`: both multiples of `2^z`.
  have hT1 : (T + 1) * 2 ^ lz T ≤ 2 ^ 32 := by
    have e : 2 ^ 32 = 2 ^ (32 - lz T) * 2 ^ lz T := by rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
    have hlt : T < 2 ^ (32 - lz T) := by rw [e] at b1; exact Nat.lt_of_mul_lt_mul_right b1
    rw [e]; exact Nat.mul_le_mul_right _ hlt
  have hMP : M * 2 ^ lz T < 2 ^ (32 * (k + 3)) := by
    have h1 : M < (T + 1) * 2 ^ (32 * (k + 2)) := by
      rw [hM', Nat.add_mul, Nat.one_mul, Nat.mul_comm (2 ^ (32 * (k + 2)))]; omega
    have h2 : M * 2 ^ lz T < (T + 1) * 2 ^ lz T * 2 ^ (32 * (k + 2)) := by
      rw [Nat.mul_right_comm]; exact Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos _)
    rw [show 32 * (k + 3) = 32 + 32 * (k + 2) by omega, Nat.pow_add]
    exact Nat.lt_of_lt_of_le h2 (Nat.mul_le_mul_right _ hT1)
  have tm := top_math (a1 := T) (a2 := U) (a3 := V) hz hL (by rw [← hM]; exact hMP)
  rw [Nat.mod_eq_of_lt b1, ← hM] at tm
  refine ⟨hMP, tm, Nat.le_trans b3 (Nat.le_add_right _ _), ?_, hz⟩
  rw [hM']
  exact Nat.le_trans (Nat.le_mul_of_pos_right _ hT0) (Nat.le_add_left _ _)

theorem sj_val {w : Nat} (hw : w ≤ 1024) :
    (BitVec.ofNat 32 w - BitVec.ofNat 32 w >>> 1) <<< 2 = BitVec.ofNat 32 (4 * (w - w / 2)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

open VG.Proof.Bignum.NormMask32 VG.Proof.Bignum.WordTop32 in
/-- The preparation's second half: `P`, `d`, `d₁` by `norm`, `v` by `recip`, and the window at
word `w - w / 2`, which starts the loop's invariant for `X`, `[r]`'s `w + 1` words. -/
theorem prepB_ok {v : State} {B : BitVec 32} {Z w N r m t nm u : Nat} (h : Ws v B Z w N) (hr : r < N) (hm : m < N)
    (hnm : nm < N) (hN : N ≤ 256) (hw6 : 6 ≤ w) (h16 : slot v.mem B 16 = w)
    {M X : Nat} (hM : num v.mem B w m = M) (hMl : M < 2 ^ (32 * (w / 2)))
    (hT0 : 0 < w32 v.mem (State.addr B) (arr w m + 4 * (w / 2 - 1))) (hz : num v.mem B w 0 = 0)
    (hnmv : num v.mem B w nm = 2 ^ (32 * w) - M) (hX : val32 v.mem (State.addr B) (arr w r) (w + 1) = X)
    (hXl : X < 2 ^ (32 * w)) :
    WP isa (.seq (norm m) (.seq recip (.block [.mov .r0 (.shifted .r9 .lsr 1), .dp .sub .r0 .r9 (.reg .r0),
        .mov .r0 (.shifted .r0 .lsl 2), .str .r0 .r8 sJ]))) v fun x =>
      DivSt x x B Z w N r m t nm u (lz (w32 v.mem (State.addr B) (arr w m + 4 * (w / 2 - 1)))) M X (w - w / 2) ∧
      Keep B w [] [sP, sD, sD1, sV, sJ] v.mem x.mem ∧ Rest divRegs v x := by
  have := h.wle
  have nw := h.nowrap
  have hz' := h.hdr_le
  have gm := h.fit64 hm
  have g0 := h.fit64 (j := 0) (by omega)
  have gn := h.fit64 hnm
  have fr := h.fit64 hr
  simp only [S] at gm g0 gn fr
  simp only [VG.Impl.Rsa.Arm.Keys.hdr] at hz'
  obtain ⟨k, hk⟩ : ∃ k, w / 2 = k + 3 := ⟨w / 2 - 3, by omega⟩
  generalize eT : w32 v.mem (State.addr B) (arr w m + 4 * (w / 2 - 1)) = T at hT0 ⊢
  have hT : T < 2 ^ 32 := eT ▸ BitVec.isLt _
  have hMv : val32 v.mem (State.addr B) (arr w m) (k + 3) = M := by
    rw [← hk, val32_low _ _ _ (show w / 2 ≤ w by omega)]; simp only [num] at hM; rw [hM, Nat.mod_eq_of_lt hMl]
  rw [val32_top3] at hMv
  have NM := norm_math (M := M) (k := k) (T := T) (U := w32 v.mem (State.addr B) (arr w m + 4 * (k + 1)))
    (V := w32 v.mem (State.addr B) (arr w m + 4 * k)) (L := val32 v.mem (State.addr B) (arr w m) k)
    (by rw [← eT, show arr w m + 4 * (w / 2 - 1) = arr w m + 4 * (k + 2) by omega]; exact hMv.symm)
    (val32_lt _ _ _ _)
    (BitVec.isLt _) (BitVec.isLt _) hT0 hT
  obtain ⟨hMP, hDv, hDn, hMge, hz31⟩ := NM
  rw [WP.seq_iff]
  refine WP.mono (norm_ok h hm hN hw6 eT (rfl : _ = w32 v.mem (State.addr B) (arr w m + 4 * (w / 2 - 2)))
    (rfl : _ = w32 v.mem (State.addr B) (arr w m + 4 * (w / 2 - 3))) hT0) fun x1 ⟨P1, D1, D11, K1, W1, R1⟩ => ?_
  rw [show arr w m + 4 * (w / 2 - 2) = arr w m + 4 * (k + 1) by omega] at D1 D11
  rw [show arr w m + 4 * (w / 2 - 3) = arr w m + 4 * k by omega] at D11
  rw [WP.seq_iff]
  refine WP.mono (recip_ok W1 (d := slot x1.mem B sD) rfl (by rw [D1]; exact hDn) (BitVec.isLt _))
    fun x2 ⟨V2, K2, R2⟩ => ?_
  have W2 : Ws x2 B Z w N := W1.rest R2
  have aJ : State.addr (B + BitVec.ofNat 32 sJ) = off (State.addr B) sJ := h.addr (by simp only [sJ]; omega)
  have wJ : InRegions x2.wr (off (State.addr B) sJ) 4 := W2.write (by simp only [sJ]; omega)
  refine WP.mono (WP.keep [.r0] (Q := fun x =>
      x.mem = x2.mem.writeW (off (State.addr B) sJ) (BitVec.ofNat 32 (4 * (w - w / 2)))) (by
    krun [W2.r8, W2.r9, aJ, wJ, sj_val this]) (by decide)) fun x3 ⟨m3, R3⟩ => ?_
  have hA : (State.addr B).toNat + Z ≤ 2 ^ 32 := by simp only [State.addr, BitVec.toNat_setWidth]; omega
  have W3 : Ws x3 B Z w N := W2.rest R3
  -- Header words other than `sJ` after the last store.
  have s3 : ∀ {e}, e + 4 ≤ 160 → (e + 4 ≤ sJ ∨ sJ + 4 ≤ e) → slot x3.mem B e = slot x2.mem B e := fun he hd => by
    simp only [slot]; rw [m3, w32_write_ne hA (by simp only [sJ]; omega) (by omega) hd]
  have a3 : ∀ {a o n}, arr w a ≤ o → o + 4 * n ≤ 2 ^ 64 →
      val32 x3.mem (State.addr B) o n = val32 v.mem (State.addr B) o n := fun {a o n} ho hf => by
    have : 160 ≤ arr w a := Nat.le_add_right _ _
    rw [m3, Outside.val32 (writeW32_outside _ _ _ (by simp only [sJ]; omega)) (Or.inr (by simp only [sJ]; omega)) hf]
    rw [Outs.val32 K2 (fun q hq => ?_) hf, Outs.val32 K1 (fun q hq => ?_) hf]
    · simp only [ranges, List.map_nil, List.nil_append, List.mem_map, List.mem_cons, List.not_mem_nil,
        or_false] at hq
      rcases hq with ⟨d, hd, rfl⟩
      rcases hd with rfl | rfl | rfl <;> simp only [sP, sD, sD1] <;> omega
    · simp only [ranges, List.map_nil, List.nil_append, List.mem_map, List.mem_cons, List.not_mem_nil,
        or_false] at hq
      rcases hq with ⟨d, rfl, rfl⟩
      simp only [sV]; omega
  have sl12 : ∀ {e}, e + 4 ≤ 160 → (∀ d ∈ [sP, sD, sD1, sV], e + 4 ≤ d ∨ d + 4 ≤ e) →
      slot x2.mem B e = slot v.mem B e := fun he hd => by
    rw [K2.slot he (fun d hd' => hd d (by simp at hd' ⊢; simp [hd'])), K1.slot he (fun d hd' => hd d (by
      simp at hd' ⊢; rcases hd' with rfl | rfl | rfl <;> simp))]
  have hk1 : w / 2 - 2 = k + 1 := by omega
  refine ⟨⟨W3, ⟨?_, ?_, hz31, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, by omega, ?_, Keep.refl _ _ _ _ _, Rest.refl _ _⟩, ?_, ?_⟩
  · rw [s3 (by decide) (by decide), sl12 (by decide) (by decide)]; exact h16
  · rw [a3 (a := m) (Nat.le_refl _) (by omega), val32_low _ _ _ (show w / 2 ≤ w by omega)]
    simp only [num] at hM; rw [hM, Nat.mod_eq_of_lt hMl]
  · rw [s3 (by decide) (by decide), K2.slot (by decide) (by decide)]; exact P1
  · rw [hk]; exact hMP
  · rw [s3 (by decide) (by decide), s3 (by decide) (by decide), K2.slot (by decide) (by decide),
      K2.slot (by decide) (by decide), D1, D11, hk1]; exact hDv
  · rw [s3 (by decide) (by decide), K2.slot (by decide) (by decide), D1]; exact hDn
  · rw [s3 (by decide) (by decide), s3 (by decide) (by decide), V2, K2.slot (e := sD) (by decide) (by decide)]
  · rw [a3 (a := 0) (Nat.le_refl _) (by omega), val32_low _ _ _ (show w / 2 + 1 ≤ w by omega)]
    simp only [num] at hz; rw [hz, Nat.zero_mod]
  · rw [a3 (a := nm) (Nat.le_refl _) (by omega), val32_low _ _ _ (show w / 2 + 1 ≤ w by omega)]
    simp only [num] at hnmv; rw [hnmv]
    exact neg_low (by omega) (Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hMge)
      (Nat.lt_of_lt_of_le hMl (Nat.pow_le_pow_right (by decide) (by omega)))
  · simp only [slot]; rw [m3, w32_write_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · rw [a3 (a := r) (Nat.le_refl _) (by omega), hX]
    refine (fold_top ?_).symm
    have e : 2 ^ (32 * w) = 2 ^ (32 * (w - w / 2 + 1)) * 2 ^ (32 * (k + 2)) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    rw [e, Nat.mul_comm] at hXl
    exact Nat.lt_of_lt_of_le hXl (Nat.mul_le_mul_right _ hMge)
  · rw [m3]
    exact ((K1.mono).trans K2.mono).trans (keep_write _ _ (by simp) (by simp only [sJ]; omega))
  · exact (R1.mono (by decide)).trans ((R2.mono (by decide)).trans (R3.mono (by decide)))

/-- The preparation: the loop's invariant at the window at word `w - w / 2`. -/
theorem prep_ok {s : State} {B : BitVec 32} {Z w N a r m nm : Nat} (t u : Nat) (h : Ws s B Z w N) (ha : a < N)
    (hr : r < N) (hm : m < N) (hnm : nm < N) (hN : N ≤ 256) (hra : r ≠ a) (hmr : m ≠ r) (hnm' : nm ≠ m)
    (hnr : nm ≠ r) (hr0 : r ≠ 0) (hn0 : nm ≠ 0) (hw6 : 6 ≤ w) (h16 : slot s.mem B 16 = w) {M : Nat}
    (hM : num s.mem B w m = M) (hMl : M < 2 ^ (32 * (w / 2)))
    (hT0 : 0 < w32 s.mem (State.addr B) (arr w m + 4 * (w / 2 - 1))) (hz : num s.mem B w 0 = 0) :
    WP isa (prep a r m nm) s fun x0 => (∃ z, DivSt x0 x0 B Z w N r m t nm u z M (num s.mem B w a) (w - w / 2)) ∧
      Keep B w [r, nm] [sP, sD, sD1, sV, sJ] s.mem x0.mem ∧ Rest divRegs s x0 := by
  have := h.wle
  have gm := h.fit64 hm
  have g0 := h.fit64 (j := 0) (by omega)
  simp only [S] at gm g0
  have hM0 : 0 < M := by
    rw [← hM]; simp only [num]
    rw [show w = (w / 2 - 1) + 1 + (w - w / 2) by omega, val32_append, val32_succ]
    have := Nat.mul_le_mul_left (2 ^ (32 * (w / 2 - 1))) hT0
    have := Nat.two_pow_pos (32 * (w / 2 - 1))
    have e : w / 2 - 1 + 1 + (w - w / 2) = w := by omega
    rw [e] at *
    omega
  rw [prep]
  simp only [VG.Impl.Rsa.Arm.Keys.seqs]
  refine prepA_ok h ha hr hm hnm hN hra hr0 hmr.symm hn0 hnm' hnr hM hM0 hz fun v W V N' K R => ?_
  have Mv : num v.mem B w m = M := by rw [K.num (by simp; exact ⟨hmr.symm, hnm'⟩) (by simp) gm]; exact hM
  have Zv : num v.mem B w 0 = 0 := by rw [K.num (by simp; exact ⟨hr0, hn0⟩) (by simp) g0]; exact hz
  have Tv : 0 < w32 v.mem (State.addr B) (arr w m + 4 * (w / 2 - 1)) := by
    rw [K.word (by simp only [S]; omega) (by simp; exact ⟨hmr.symm, hnm'⟩) (by simp) gm]; exact hT0
  have hv16 : slot v.mem B 16 = w := by rw [K.slot (by decide) (by simp)]; exact h16
  exact WP.mono (prepB_ok (t := t) (u := u) W hr hm hnm hN hw6 hv16 Mv hMl Tv Zv N' V
    (by simp only [num]; exact val32_lt _ _ _ _)) fun x0 ⟨I0, K0, R0⟩ =>
      ⟨⟨_, I0⟩, (K.mono).trans K0.mono, (R.mono (by decide)).trans R0⟩

/-! ## The division -/

/-- The header words the division changes. -/
abbrev divSlots : List Nat := [sP, sD, sD1, sV, sMk, sQ, sU0, sU2, VG.Impl.Rsa.Arm.Keys.sC, sJ]

/-- `divW a r m t nm u`: `[r] := [a] mod M` for `M = [m]` of `w / 2` words, its top word not
zero, through `[t]`, `[nm]` and `[u]`, with `[0]` zero; word `w` of `[r]` zero. -/
theorem divW_ok {s : State} {B : BitVec 32} {Z w N a r m t nm u : Nat} (h : Ws s B Z w N) (ha : a < N)
    (hr : r < N) (hm : m < N) (ht : t < N) (hnm : nm < N) (hu : u < N) (hN : N ≤ 256) (hra : r ≠ a)
    (hrt : r ≠ t) (hru : r ≠ u) (htu : t ≠ u) (hmr : m ≠ r) (hmt : m ≠ t) (hmu : m ≠ u) (hnr : nm ≠ r)
    (htn : t ≠ nm) (hnu : nm ≠ u) (hnm' : nm ≠ m) (hr0 : r ≠ 0) (ht0 : t ≠ 0) (hu0 : u ≠ 0) (hn0 : nm ≠ 0)
    (hw6 : 6 ≤ w) (h16 : slot s.mem B 16 = w) {M : Nat} (hM : num s.mem B w m = M)
    (hMl : M < 2 ^ (32 * (w / 2))) (hT0 : 0 < w32 s.mem (State.addr B) (arr w m + 4 * (w / 2 - 1)))
    (hz : num s.mem B w 0 = 0) :
    WP isa (divW a r m t nm u) s fun v => Ws v B Z w N ∧ num v.mem B w r = num s.mem B w a % M ∧
      w32 v.mem (State.addr B) (arr w r + 4 * w) = 0 ∧ Keep B w [r, t, u, nm] divSlots s.mem v.mem ∧
      Rest divRegs s v := by
  have := h.wle
  have gm := h.fit64 hm
  have g0 := h.fit64 (j := 0) (by omega)
  have gn := h.fit64 hnm
  simp only [S] at gm g0 gn
  have hM0 : 0 < M := by
    rw [← hM]; simp only [num]
    rw [show w = (w / 2 - 1) + 1 + (w - w / 2) by omega, val32_append, val32_succ]
    have := Nat.mul_le_mul_left (2 ^ (32 * (w / 2 - 1))) hT0
    have := Nat.two_pow_pos (32 * (w / 2 - 1))
    have e : w / 2 - 1 + 1 + (w - w / 2) = w := by omega
    rw [e] at *
    omega
  rw [divW]
  simp only [VG.Impl.Rsa.Arm.Keys.seqs]
  rw [WP.seq_iff]
  refine WP.mono (prep_ok t u h ha hr hm hnm hN hra hmr hnm' hnr hr0 hn0 hw6 h16 hM hMl hT0 hz)
    fun x0 ⟨⟨_, I0⟩, K, R⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (loop_ok I0 (by omega) hr hm ht hnm hu hN hrt hru htu hmr hmt hmu hnr htn hnu hr0 ht0 hu0
    (by omega)) fun x1 I1 => ?_
  refine WP.mono (stepD_ok I1 hr hm ht hnm hu hN hrt hru htu hmr hmt hmu hnr htn hnu hr0 ht0 hu0 (by omega))
    fun x2 ⟨W2, _, _, V2, K2, R2⟩ => ?_
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.mod_one, Nat.div_one, Nat.one_mul, Nat.zero_add] at V2
  rw [val32_succ] at V2
  have hlt := val32_lt x2.mem (State.addr B) (arr w r) w
  have hXM : num s.mem B w a % M < 2 ^ (32 * w) :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ hM0) (Nat.le_of_lt (Nat.lt_of_lt_of_le hMl
      (Nat.pow_le_pow_right (by decide) (by omega))))
  generalize 2 ^ (32 * w) = P at hlt hXM V2
  have hw0 : w32 x2.mem (State.addr B) (arr w r + 4 * w) = 0 := by
    rcases Nat.eq_zero_or_pos (w32 x2.mem (State.addr B) (arr w r + 4 * w)) with e | e
    · exact e
    · have := Nat.le_mul_of_pos_right P e; omega
  refine ⟨W2, ?_, hw0, ?_, ?_⟩
  · simp only [num]; rw [hw0, Nat.mul_zero, Nat.add_zero] at V2; exact V2
  · exact K.mono.trans K2.mono
  · exact R.trans R2

end VG.Proof.Rsa.Arm.KeyDiv
