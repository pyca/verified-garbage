module

public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Exp
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSA with AVX512_IFMA on x86-64, any size: the exponent's digits

`recode l p` reads the padded exponent of region `p` (`P` bytes at `oE`, most
significant first) in groups of `w` bytes, and writes each group's 8 digits
of `w` bits, a byte each, at `oD`: digit `i` of the region is `digit l V i`,
`V` the padded exponent's value (`bv`), as the windows read them
(`recode_ok`). One group (`recodeBody`): its bytes into `rax` one at a time
(`accum_ok`), then its digits from `rax` (`digits_ok`); `digit_group` is
the arithmetic.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off ofs_off)
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Bignum.X86_64.AmmSym (writeB_outside ofs_self writeB_self ofs_off0 se_ofNat off_add)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-! ## Big-endian values -/

/-- The big-endian value of the `n` bytes at offset `o` of `F`. -/
def bv (m : Mem) (F : Addr) (o : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => bv m F o n * 256 + (m (off F (o + n))).toNat

theorem bv_lt (m : Mem) (F : Addr) (o : Nat) : ∀ n, bv m F o n < 256 ^ n
  | 0 => by simp [bv]
  | n + 1 => by
    have := bv_lt m F o n
    have := (m (off F (o + n))).isLt
    rw [bv, Nat.pow_succ]; omega

theorem bv_add (m : Mem) (F : Addr) (o n : Nat) :
    ∀ k, bv m F o (n + k) = bv m F o n * 256 ^ k + bv m F (o + n) k
  | 0 => by simp [bv]
  | k + 1 => by
    rw [← Nat.add_assoc, bv, bv_add m F o n k, bv, Nat.pow_succ, Nat.add_assoc o n k]
    grind

theorem bv_congr {m m' : Mem} {F : Addr} {o : Nat} :
    ∀ n, (∀ i < n, m' (off F (o + i)) = m (off F (o + i))) → bv m' F o n = bv m F o n
  | 0, _ => rfl
  | n + 1, h => by
    rw [bv, bv, bv_congr n fun i hi => h i (by omega), h n (by omega)]

/-- The layouts' groups: `P = w G`, `ND = 8 G`. -/
theorem lay_groups (hl : LayOk l) : l.P = l.w * (l.P / l.w) ∧ l.ND = 8 * (l.P / l.w) := by
  rcases hl with rfl | rfl | rfl <;> decide

/-- Digit `8 g + t` of the padded exponent is digit `t` of group `g`'s value. -/
theorem digit_group (hl : LayOk l) {m : Mem} {F : Addr} {o g t : Nat} (hg : g < l.P / l.w) (ht : t < 8) :
    digit l (bv m F o l.P) (8 * g + t) = bv m F (o + l.w * g) l.w / l.T ^ (7 - t) % l.T := by
  obtain ⟨hP, hN⟩ := lay_groups hl
  generalize hG : l.P / l.w = G at hP hN hg
  have hT : l.T ^ 8 = 256 ^ l.w := by rw [Lay.T, ← Nat.pow_mul, Nat.mul_comm, Nat.pow_mul]
  have hTp : 0 < l.T := T_pos hl
  obtain ⟨r, hr⟩ : ∃ r, G = g + 1 + r := ⟨G - 1 - g, by omega⟩
  -- the value: the groups before `g`, group `g`, the rest
  have e1 : l.P = l.w * g + (l.w + l.w * r) := by
    rw [hP, hr, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.add_assoc]
  generalize hH : bv m F o (l.w * g) = H
  generalize hv : bv m F (o + l.w * g) l.w = v
  generalize hLo : bv m F (o + l.w * g + l.w) (l.w * r) = Lo
  have hLlt : Lo < 256 ^ (l.w * r) := hLo ▸ bv_lt m F _ _
  have hV : bv m F o l.P = (H * 256 ^ l.w + v) * 256 ^ (l.w * r) + Lo := by
    rw [e1, bv_add, bv_add m F (o + l.w * g) l.w (l.w * r), hH, hv, hLo, Nat.add_mul, Nat.mul_assoc,
      ← Nat.pow_add]
    grind
  have hd : l.ND - 1 - (8 * g + t) = 8 * r + (7 - t) := by rw [hN, hr]; omega
  have hD : l.T ^ (8 * r) = 256 ^ (l.w * r) := by rw [Nat.pow_mul, hT, ← Nat.pow_mul]
  have q1 : bv m F o l.P / l.T ^ (8 * r) = H * 256 ^ l.w + v := by
    rw [hV, hD, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide)), Nat.div_eq_of_lt hLlt,
      Nat.zero_add]
  have e2 : H * 256 ^ l.w + v = v + l.T ^ (7 - t) * (H * l.T ^ t * l.T) := by
    rw [← hT, show 8 = (7 - t) + t + 1 by omega, Nat.pow_succ, Nat.pow_add]; grind
  rw [digit, hd, Nat.pow_add, ← Nat.div_div_eq_div_mul, q1, e2, Nat.add_mul_div_left _ _ (Nat.pow_pos hTp),
    Nat.add_mul_mod_self_right]

/-! ## A group -/

/-- Byte `j` of the big-endian value of `n` bytes. -/
theorem bv_byte (m : Mem) (F : Addr) (o : Nat) {n j : Nat} (hj : j < n) :
    bv m F o n / 256 ^ (n - 1 - j) % 256 = (m (off F (o + j))).toNat := by
  obtain ⟨k, rfl⟩ : ∃ k, n = j + 1 + k := ⟨n - 1 - j, by omega⟩
  have hr := bv_lt m F (o + (j + 1)) k
  have hb := (m (off F (o + j))).isLt
  rw [bv_add, show j + 1 + k - 1 - j = k by omega, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide)),
    Nat.div_eq_of_lt hr, Nat.zero_add, bv]
  omega

/-- With windows of 4 bits, digit `i` of the padded exponent's value is a
nibble of byte `i / 2` (`nibOf`), as the windows read it without `recode`. -/
theorem digit_nib (hl : LayOk l) (hw : l.w = 4) {m : Mem} {F : Addr} {o i : Nat} (hi : i < l.ND) :
    digit l (bv m F o l.P) i = nibOf l i (m (off F (o + i / 2))).toNat := by
  obtain ⟨hP, hN⟩ := lay_groups hl
  have hg : i / 8 < l.P / l.w := by omega
  have e := digit_group hl (m := m) (F := F) (o := o) hg (show i % 8 < 8 by omega)
  rw [show 8 * (i / 8) + i % 8 = i by omega] at e
  have hT : l.T = 16 := by simp only [Lay.T, hw]
  have hb := bv_byte m F (o + l.w * (i / 8)) (n := l.w) (j := i % 8 / 2) (by omega)
  rw [show o + l.w * (i / 8) + i % 8 / 2 = o + i / 2 by rw [hw]; omega] at hb
  have hpow : ∀ t < 8, 16 ^ (7 - t) = 256 ^ (4 - 1 - t / 2) * 16 ^ (1 - t % 2) := by decide
  rw [e, hT]
  simp only [nibOf, hw, ite_true] at hb ⊢
  rw [show i % 2 = i % 8 % 2 by omega, hpow _ (by omega), ← Nat.div_div_eq_div_mul, ← hb]
  generalize bv m F (o + 4 * (i / 8)) 4 / 256 ^ (4 - 1 - i % 8 / 2) = X
  rcases Nat.mod_two_eq_zero_or_one (i % 8) with h | h
  · simp only [h, ↓reduceIte, Nat.sub_zero, Nat.pow_one]
    rw [show 256 = 16 * 16 from rfl, Nat.mod_mul_right_div_self]
  · simp only [h, Nat.one_ne_zero, ↓reduceIte, Nat.sub_self, Nat.pow_zero, Nat.div_one]
    rw [Nat.mod_mod_of_dvd _ (by decide : 16 ∣ 256)]


theorem shl8_or {a : Nat} (ha : a < 2 ^ 48) (b : BitVec 8) :
    BitVec.ofNat 64 a <<< 8 ||| b.setWidth 64 = BitVec.ofNat 64 (a * 256 + b.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have hb := b.isLt
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show b.toNat < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show a <<< 8 < 2 ^ 64 by rw [Nat.shiftLeft_eq]; omega),
    ← Nat.shiftLeft_add_eq_or_of_lt (show b.toNat < 2 ^ 8 by omega), Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega)]

/-- One byte of a group into `rax`. -/
theorem accStep_ok {s : State} {X : Addr} {a j : Nat} (ha : a < 2 ^ 48) (h8 : s.gpr .r8 = X)
    (hra : s.gpr .rax = BitVec.ofNat 64 a) (hrd : InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 j) 1) :
    WP isa (.block [.shift .shl .rax 8, .movzx8 .rdx (at_ .r8 j), .alu .or .rax (.reg .rdx)]) s fun s' =>
      s'.gpr .rax = BitVec.ofNat 64 (a * 256 + (s.mem (X + BitVec.ofNat 64 j)).toNat) ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rdx] s s' ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr := by
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax, .rdx] (Q := fun s' =>
    s'.gpr .rax = BitVec.ofNat 64 (a * 256 + (s.mem (X + BitVec.ofNat 64 j)).toNat) ∧ s'.mem = s.mem ∧
      s'.mxcsr = s.mxcsr) (by
    xrun [eaG', h8, hra, hrd]
    and_intros
    · exact shl8_or ha _
    all_goals rfl) rfl) fun s' ⟨⟨a, b, c⟩, k⟩ => ⟨a, k, b, c⟩

/-- The accumulation of a group's first `n` bytes. -/
def accCode (n : Nat) : List Instr :=
  (List.range n).flatMap fun j => [.shift .shl .rax 8, .movzx8 .rdx (at_ .r8 j), .alu .or .rax (.reg .rdx)]

theorem pow256_le {n : Nat} (hn : n ≤ 6) : 256 ^ n ≤ 2 ^ 48 :=
  Nat.le_trans (Nat.pow_le_pow_right (show 256 > 0 by decide) hn) (by decide)

/-- The first `n ≤ 6` bytes at `off F o` (`r8`) into `rax`, from 0. -/
theorem accum_ok {F : Addr} {o : Nat} :
    ∀ {n : Nat} {s : State}, n ≤ 6 → s.gpr .r8 = off F o → s.gpr .rax = BitVec.ofNat 64 0 →
      (∀ j < n, InRegions (s.rd ++ s.wr) (off F (o + j)) 1) →
      WP isa (.block (accCode n)) s fun s' =>
        s'.gpr .rax = BitVec.ofNat 64 (bv s.mem F o n) ∧
        VG.Proof.MlKem.X86_64.Keep [.rax, .rdx] s s' ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr
  | 0, s, _, _, hra, _ => WP.block_nil ⟨hra, VG.Proof.MlKem.X86_64.Keep.refl _ _, rfl, rfl⟩
  | n + 1, s, hn, h8, hra, hrd => by
    rw [accCode, List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (accum_ok (by omega) h8 hra fun j hj => hrd j (by omega)) fun t ⟨ra, k, me, mx⟩ => ?_
    have h8t : t.gpr .r8 = off F o := by rw [k.gpr (by decide)]; exact h8
    have hb := bv_lt s.mem F o n
    refine WP.mono (accStep_ok (j := n) (Nat.lt_of_lt_of_le hb (pow256_le (by omega))) h8t ra
      (by rw [k.2.1, k.2.2, off_add]; exact hrd n (by omega))) fun t' ⟨ra', k', me', mx'⟩ =>
      ⟨?_, (k.trans k').mono (by decide), me'.trans me, mx'.trans mx⟩
    rw [ra', bv, me, off_add]

/-- Digit `t` of the group's value `v` (in `rax`) to `r9 + t`. -/
def dgtCode (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (t : Nat) : List Instr :=
  [.mov .rdx (.reg .rax)] ++ (if t = 7 then [] else [.shift .shr .rdx (l.w * (7 - t))]) ++
    [.alu .and .rdx (.imm (BitVec.ofNat 32 (l.T - 1))), .store8 (at_ .r9 t) .rdx]

theorem digit_byte (hl : LayOk l) {v k : Nat} (hv : v < 2 ^ 64) :
    ((BitVec.ofNat 64 v >>> k &&& (BitVec.ofNat 32 (l.T - 1)).signExtend 64).setWidth 8) =
      BitVec.ofNat 8 (v / 2 ^ k % l.T) := by
  have hT := hl.T_bounds
  have hw := hl.w_bounds
  rw [se_ofNat (show l.T - 1 < 2 ^ 31 by omega)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt (show l.T - 1 < 2 ^ 64 by omega),
    Nat.shiftRight_eq_div_pow, show l.T - 1 = 2 ^ l.w - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  rfl

theorem digStep_ok (hl : LayOk l) {s : State} {Y : Addr} {v t : Nat} (hv : v < 2 ^ 64) (ht : t < 8)
    (h9 : s.gpr .r9 = Y) (hra : s.gpr .rax = BitVec.ofNat 64 v) (hwr : InRegions s.wr (Y + BitVec.ofNat 64 t) 1) :
    WP isa (.block (dgtCode l t)) s fun s' =>
      s'.mem = s.mem.writeW (Y + BitVec.ofNat 64 t) (BitVec.ofNat 8 (v / l.T ^ (7 - t) % l.T)) ∧
      VG.Proof.MlKem.X86_64.Keep [.rdx] s s' ∧ s'.mxcsr = s.mxcsr := by
  have hk : l.T ^ (7 - t) = 2 ^ (l.w * (7 - t)) := by rw [Lay.T, ← Nat.pow_mul]
  by_cases h7 : t = 7
  · subst h7
    simp only [dgtCode, ite_true, List.append_nil, List.cons_append, List.nil_append]
    refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rdx] (Q := fun s' =>
      s'.mem = s.mem.writeW (Y + BitVec.ofNat 64 7) (BitVec.ofNat 8 (v / l.T ^ (7 - 7) % l.T)) ∧
        s'.mxcsr = s.mxcsr) (by
      xrun [eaG', h9, hra, hwr]
      and_intros
      · have e := digit_byte hl (k := 0) hv
        rw [BitVec.ushiftRight_zero, Nat.pow_zero, Nat.div_one] at e
        rw [e, Nat.sub_self, Nat.pow_zero, Nat.div_one]
      all_goals rfl) rfl) fun s' ⟨⟨a, b⟩, k⟩ => ⟨a, k, b⟩
  · simp only [dgtCode, h7, ite_false, List.cons_append, List.nil_append]
    have hsh : 1 ≤ l.w * (7 - t) ∧ l.w * (7 - t) ≤ 63 := by
      have := hl.w_bounds
      constructor
      · exact Nat.mul_pos (by omega) (by omega)
      · exact Nat.le_trans (Nat.mul_le_mul this.2 (Nat.sub_le 7 t)) (by decide)
    refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rdx] (Q := fun s' =>
      s'.mem = s.mem.writeW (Y + BitVec.ofNat 64 t) (BitVec.ofNat 8 (v / l.T ^ (7 - t) % l.T)) ∧
        s'.mxcsr = s.mxcsr) (by
      xrun [eaG', h9, hra, hwr, hsh]
      and_intros
      · rw [hk, ← digit_byte hl hv]
      all_goals rfl) rfl) fun s' ⟨⟨a, b⟩, k⟩ => ⟨a, k, b⟩

/-- The first `n ≤ 8` digits of the group's value `v` (in `rax`) to `off F o` (`r9`). -/
theorem digits_ok (hl : LayOk l) {F : Addr} {o v : Nat} (hv : v < 2 ^ 64) (hF : o + 8 < 2 ^ 64) :
    ∀ {n : Nat} {s : State}, n ≤ 8 → s.gpr .r9 = off F o → s.gpr .rax = BitVec.ofNat 64 v →
      (∀ t < n, InRegions s.wr (off F (o + t)) 1) →
      WP isa (.block ((List.range n).flatMap (dgtCode l))) s fun s' =>
        (∀ t < n, s'.mem (off F (o + t)) = BitVec.ofNat 8 (v / l.T ^ (7 - t) % l.T)) ∧
        Outside F o n s.mem s'.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rdx] s s' ∧ s'.mxcsr = s.mxcsr
  | 0, s, _, _, _, _ =>
    WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Outside.refl _ _ _ _,
      VG.Proof.MlKem.X86_64.Keep.refl _ _, rfl⟩
  | n + 1, s, hn, h9, hra, hwr => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (digits_ok hl hv hF (by omega) h9 hra fun t ht => hwr t (by omega))
      fun u ⟨bu, ou, ku, xu⟩ => ?_
    have h9u : u.gpr .r9 = off F o := by rw [ku.gpr (by decide)]; exact h9
    have hrau : u.gpr .rax = BitVec.ofNat 64 v := by rw [ku.gpr (by decide)]; exact hra
    refine WP.mono (digStep_ok hl (t := n) hv (by omega) h9u hrau (by rw [ku.2.2, off_add]; exact hwr n (by omega)))
      fun u' ⟨mu, ku', xu'⟩ => ⟨fun t ht => ?_, ?_, (ku.trans ku').mono (by decide), xu'.trans xu⟩
    · rw [mu, off_add]
      by_cases e : t = n
      · subst e; exact writeB_self _ _ _
      · rw [writeB_outside u.mem F (d := o + n) _ (by omega) _ (by rw [ofs_off0 F (by omega)]; omega)]
        exact bu t (by omega)
    · rw [mu, off_add]
      exact (ou.mono (Nat.le_refl _) (by omega)).trans
        ((writeB_outside u.mem F (d := o + n) _ (by omega)).mono (by omega) (by omega))

/-! ## The groups -/

/-- After `g` groups of the padded exponent at offset `e` of `F`, whose
digits go to offset `d`, from `s₀`. -/
structure RecInv (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (s₀ : State) (F : Addr) (e d g : Nat) (t : State) : Prop where
  r8 : t.gpr .r8 = off F (e + l.w * g)
  r9 : t.gpr .r9 = off F (d + 8 * g)
  rcx : t.gpr .rcx = BitVec.ofNat 64 (l.P / l.w - g)
  dg : ∀ i < 8 * g, (t.mem (off F (d + i))).toNat = digit l (bv s₀.mem F e l.P) i
  out : Outside F d (8 * g) s₀.mem t.mem
  keep : VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rdx, .r8, .r9] s₀ t
  mx : t.mxcsr = s₀.mxcsr

theorem recodeBody_eq : recodeBody l = ([.mov32 .rax (.imm 0)] : List Instr) ++ (accCode l.w ++
    ((List.range 8).flatMap (dgtCode l) ++
      ([.alu .add .r8 (.imm (BitVec.ofNat 32 l.w)), .alu .add .r9 (.imm 8), .alu .sub .rcx (.imm 1)] :
        List Instr))) := by
  rw [recodeBody, List.append_assoc, List.append_assoc]; rfl

/-- Group `g`. -/
theorem recIter_ok (hl : LayOk l) {s₀ t : State} {F : Addr} {e d g : Nat} (hg : g < l.P / l.w)
    (hed : e + l.P ≤ d) (hd : d + l.ND < 2 ^ 63)
    (hrd : ∀ i < l.P, InRegions (s₀.rd ++ s₀.wr) (off F (e + i)) 1)
    (hwr : ∀ i < l.ND, InRegions s₀.wr (off F (d + i)) 1) (h : RecInv l s₀ F e d g t) :
    WP isa (.block (recodeBody l)) t fun t' =>
      t'.zf = some (decide (g + 1 = l.P / l.w)) ∧ RecInv l s₀ F e d (g + 1) t' := by
  obtain ⟨hP, hN⟩ := lay_groups hl
  have hw := hl.w_bounds
  have hwg : l.w * g + l.w ≤ l.P := by rw [hP, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hg
  have h8g : 8 * g + 8 ≤ l.ND := by rw [hN, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hg
  rw [recodeBody_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax] (Q := fun u =>
    u.gpr .rax = BitVec.ofNat 64 0 ∧ u.mem = t.mem ∧ u.mxcsr = t.mxcsr) (by xrun; and_intros <;> rfl) rfl)
    fun u ⟨⟨ra, me, mx⟩, k⟩ => ?_
  have h8u : u.gpr .r8 = off F (e + l.w * g) := by rw [k.gpr (by decide)]; exact h.r8
  rw [WP.block_append_iff]
  refine WP.mono (accum_ok (by omega) h8u ra fun j hj => by
      rw [k.2.1, k.2.2, h.keep.2.1, h.keep.2.2, Nat.add_assoc]; exact hrd _ (by omega))
    fun u₁ ⟨ra₁, k₁, me₁, mx₁⟩ => ?_
  -- the group's value, from `s₀`'s bytes
  have hv : bv u.mem F (e + l.w * g) l.w = bv s₀.mem F (e + l.w * g) l.w := by
    rw [me]
    exact bv_congr _ fun i hi => h.out _ (.inl (by rw [ofs_off0 F (by omega)]; omega))
  have hvl : bv u.mem F (e + l.w * g) l.w < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (bv_lt _ _ _ _) (Nat.le_trans (pow256_le (by omega)) (by decide))
  have h9 : u₁.gpr .r9 = off F (d + 8 * g) := by rw [k₁.gpr (by decide), k.gpr (by decide)]; exact h.r9
  rw [WP.block_append_iff]
  refine WP.mono (digits_ok hl hvl (o := d + 8 * g) (by omega) (Nat.le_refl 8) h9 ra₁ fun i hi => by
      rw [k₁.2.2, k.2.2, h.keep.2.2, Nat.add_assoc]; exact hwr _ (by omega))
    fun u₂ ⟨b₂, o₂, k₂, x₂⟩ => ?_
  have h8₂ : u₂.gpr .r8 = off F (e + l.w * g) := by rw [k₂.gpr (by decide), k₁.gpr (by decide)]; exact h8u
  have h9₂ : u₂.gpr .r9 = off F (d + 8 * g) := by rw [k₂.gpr (by decide)]; exact h9
  have hc₂ : u₂.gpr .rcx = BitVec.ofNat 64 (l.P / l.w - g) := by
    rw [k₂.gpr (by decide), k₁.gpr (by decide), k.gpr (by decide)]; exact h.rcx
  have hG : l.P / l.w < 2 ^ 31 := by rcases hl with rfl | rfl | rfl <;> decide
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rcx, .r8, .r9] (Q := fun u' =>
    u'.gpr .r8 = off F (e + l.w * (g + 1)) ∧ u'.gpr .r9 = off F (d + 8 * (g + 1)) ∧
      u'.gpr .rcx = BitVec.ofNat 64 (l.P / l.w - (g + 1)) ∧ u'.zf = some (decide (g + 1 = l.P / l.w)) ∧
      u'.mem = u₂.mem ∧ u'.mxcsr = u₂.mxcsr) (by
    xrun [h8₂, h9₂, hc₂, se_ofNat (show l.w < 2 ^ 31 by omega)]
    have e1 : BitVec.ofNat 64 (l.P / l.w - g) - 1 = BitVec.ofNat 64 (l.P / l.w - (g + 1)) := by
      rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, VG.Offset.ofNat_sub_ofNat (by omega)]
      congr 1
    and_intros
    · rw [off_add, Nat.mul_succ, Nat.add_assoc]
    · rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, off_add, Nat.mul_succ, Nat.add_assoc]
    · exact e1
    · rw [e1]
      by_cases hz : g + 1 = l.P / l.w
      · simp only [hz, Nat.sub_self, decide_true]; rfl
      · simp only [hz, decide_false, beq_eq_false_iff_ne, ne_eq]
        intro h'
        have := congrArg BitVec.toNat h'
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        change _ = 0 at this
        omega
    all_goals rfl) rfl) fun u' ⟨⟨r8', r9', rc', z', me', mx'⟩, k'⟩ => ⟨z', r8', r9', rc', fun i hi => ?_, ?_,
      (((h.keep.trans k).trans k₁).trans k₂).trans k' |>.mono (by decide), by rw [mx', x₂, mx₁, mx, h.mx]⟩
  · rw [me']
    by_cases hi' : i < 8 * g
    · rw [o₂ _ (.inl (by rw [ofs_off0 F (by omega)]; omega)), me₁, me]
      exact h.dg i hi'
    · obtain ⟨t', ht', rfl⟩ : ∃ t', t' < 8 ∧ i = 8 * g + t' := ⟨i - 8 * g, by omega, by omega⟩
      rw [← Nat.add_assoc, b₂ t' ht', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
          have := digit_lt hl (bv u.mem F (e + l.w * g) l.w / 2 ^ 0) 0; have := hl.T_bounds
          exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (T_pos hl)) (by omega)),
        hv, digit_group hl hg ht']
  · rw [me']
    have o₂' := o₂
    rw [me₁, me] at o₂'
    exact (h.out.mono (Nat.le_refl _) (by omega)).trans (o₂'.mono (by omega) (by omega))

/-- The loop over the groups. -/
theorem recLoop_ok (hl : LayOk l) {s₀ : State} {F : Addr} {e d : Nat}
    (hed : e + l.P ≤ d) (hd : d + l.ND < 2 ^ 63)
    (hrd : ∀ i < l.P, InRegions (s₀.rd ++ s₀.wr) (off F (e + i)) 1)
    (hwr : ∀ i < l.ND, InRegions s₀.wr (off F (d + i)) 1) (h : RecInv l s₀ F e d 0 s₀) :
    WP isa (.loop (.block (recodeBody l)) .ne) s₀ (RecInv l s₀ F e d (l.P / l.w)) :=
  wp_upto (a := 0) (N := l.P / l.w) (by rcases hl with rfl | rfl | rfl <;> decide) (fun g t => RecInv l s₀ F e d g t)
    (fun _ _ hg t hI => recIter_ok hl hg hed hd hrd hwr hI) (fun _ hI => hI) h

/-! ## A region's digits -/

/-- `recode l p`: the digits of the padded exponent of region `p` of the
area `F` (in the header's slot `sIfma`, `rdi = W`). -/
theorem recode_ok (hl : LayOk l) (hw : l.w ≠ 4) {s : State} {W F : Addr} {p : Nat} (hp : p < 2) (hdi : s.gpr .rdi = W)
    (hia : InRegions (s.rd ++ s.wr) (off W (8 * sIfma)) 8) (hiv : word s.mem W (8 * sIfma) = F)
    (hn : l.D * p + l.oK1 < 2 ^ 63)
    (hrd : ∀ i < l.P, InRegions (s.rd ++ s.wr) (off F (l.D * p + l.oE + i)) 1)
    (hwr : ∀ i < l.ND, InRegions s.wr (off F (l.D * p + l.oD + i)) 1) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (recode l p)) s fun s' =>
      (∀ i < l.ND, (s'.mem (off F (l.D * p + l.oD + i))).toNat = digit l (bv s.mem F (l.D * p + l.oE) l.P) i) ∧
      Outside F (l.D * p + l.oD) l.ND s.mem s'.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rdx, .r8, .r9] s s' ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨hP, hN⟩ := lay_groups hl
  obtain ⟨d1, d2⟩ := lay_oD l hw
  have hD := hl.D_bounds
  have hG : l.P / l.w < 2 ^ 31 := by rcases hl with rfl | rfl | rfl <;> decide
  have he : l.D * p + l.oE < 2 ^ 31 := by
    obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
    rcases D_mul (l := l) hp with h | h <;> omega_using [h, hD, o6, o10]
  have hd : l.D * p + l.oD < 2 ^ 31 := by
    obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
    rcases D_mul (l := l) hp with h | h <;> omega_using [h, hD, d2, o7, o10]
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rcx, .r8, .r9] (Q := fun t =>
    t.gpr .r8 = off F (l.D * p + l.oE) ∧ t.gpr .r9 = off F (l.D * p + l.oD) ∧
      t.gpr .rcx = BitVec.ofNat 64 (l.P / l.w) ∧ t.mem = s.mem ∧ t.mxcsr = s.mxcsr) (by
    have hiv' : s.mem.readW (off W (8 * sIfma)) 64 = F := hiv
    xrun [State.ea, VG.Impl.Bignum.X86_64.hdr, hdi, VG.Proof.Bignum.X86_64.hdrOff, hia, hiv', se_ofNat he, se_ofNat hd]
    and_intros
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (a := l.P / l.w) (b := 2 ^ 32) (by omega),
        Nat.mod_eq_of_lt (a := l.P / l.w) (b := 2 ^ 64) (by omega)]
    all_goals rfl) rfl) fun t ⟨⟨r8, r9, rc, me, mx⟩, k⟩ => ?_)
  have i₀ : RecInv l t F (l.D * p + l.oE) (l.D * p + l.oD) 0 t :=
    ⟨by rw [Nat.mul_zero, Nat.add_zero]; exact r8, by rw [Nat.mul_zero, Nat.add_zero]; exact r9,
      by rw [Nat.sub_zero]; exact rc, fun _ h => absurd h (Nat.not_lt_zero _), Outside.refl _ _ _ _,
      VG.Proof.MlKem.X86_64.Keep.refl _ _, rfl⟩
  refine WP.mono (recLoop_ok hl (by omega_using [d1]) (by omega_using [hn, d2])
      (fun i hi => by rw [k.2.1, k.2.2]; exact hrd i hi) (fun i hi => by rw [k.2.2]; exact hwr i hi) i₀)
    fun t' hI => ⟨fun i hi => ?_, ?_, (k.trans hI.keep).mono (by decide), hI.mx.trans mx⟩
  · rw [hI.dg i (by omega), me]
  · rw [← me]; exact hI.out.mono (Nat.le_refl _) (by omega)

/-- The value of bytes at `o` that hold `bs`. -/
theorem bv_os2ip (m : Mem) (F : Addr) (o : Nat) (bs : List Byte)
    (h : ∀ i (hi : i < bs.length), m (off F (o + i)) = bs[i]) :
    ∀ n ≤ bs.length, bv m F o n = Spec.Rsa.os2ip (bs.take n)
  | 0, _ => rfl
  | n + 1, hn => by
    rw [bv, bv_os2ip m F o bs h n (by omega), List.take_add_one, List.getElem?_eq_getElem (by omega),
      Option.toList_some, os2ip_snoc, h n (by omega), Nat.mul_comm]

end VG.Proof.Bignum.X86_64.Ifma
