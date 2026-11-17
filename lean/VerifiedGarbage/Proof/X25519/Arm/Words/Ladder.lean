module

public import VerifiedGarbage.Proof.X25519.Arm.Invert
public import VerifiedGarbage.Proof.X25519.Ladder
import VerifiedGarbage.Proof.X25519.Arm.Cswap
import VerifiedGarbage.Proof.X25519.Field
import VerifiedGarbage.Proof.X25519.Invert
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.X25519.Arm.Field
public import VerifiedGarbage.Impl.X25519.Arm.Words

/-! ### `X25519.Arm.Words.AddSub`, which this module and modules that import it used -/

section

/-! ### `X25519.Arm.Words.Mul`, which this module and modules that import it used -/

section

/-! ### `X25519.Arm.Words.Chain`, which this module and modules that import it used -/

section

/-!
# X25519 on 32-bit ARM with `umaal`: chains of `umaal`

Every sum of `vg_x25519_umaal`'s arithmetic is a chain of `umaal`s over the
words of a number, each taking the carry of the one before:
`c:x_k := n m_k + c + x_k`. Their words and carries (`uo`, `uc`), the number
they make in radix `2³²` (`val32`, `uc_val`), and the code (`wp_umaal`,
`uchain_ok`), for any registers and any code that prepares each step's
operands (`pre`); the element of eight words at an offset of the working
space (`W`), and its stores (`stores_ok`).
-/

@[expose] public section

namespace VG.Proof.X25519.Arm.Words

open VG VG.Arm VG.Impl.X25519.Arm.Words
open VG.Proof.X25519.Arm

/-! ## Numbers of 32-bit words -/

/-- The number with the words `f 0, …, f (n - 1)` in radix `2³²`. -/
def val32 (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => val32 f n + 2 ^ (32 * n) * f n

theorem val32_succ (f : Nat → Nat) (n : Nat) : val32 f (n + 1) = val32 f n + 2 ^ (32 * n) * f n :=
  rfl

theorem val32_congr {f g : Nat → Nat} : ∀ {n : Nat}, (∀ k < n, f k = g k) → val32 f n = val32 g n
  | 0, _ => rfl
  | n + 1, h => by
    rw [val32_succ, val32_succ, val32_congr (fun k hk => h k (by omega_arith)), h n (by omega_arith)]

theorem val32_zero_fn : ∀ n, val32 (fun _ => 0) n = 0
  | 0 => rfl
  | n + 1 => by rw [val32_succ, val32_zero_fn n]; rfl

theorem val32_lt {f : Nat → Nat} : ∀ {n : Nat}, (∀ k < n, f k < 2 ^ 32) → val32 f n < 2 ^ (32 * n)
  | 0, _ => Nat.one_pos
  | n + 1, h => by
    have ih := val32_lt (n := n) fun k hk => h k (by omega_arith)
    rw [val32_succ, Nat.mul_succ, Nat.pow_add]
    have h1 : 2 ^ (32 * n) * f n + 2 ^ (32 * n) ≤ 2 ^ (32 * n) * 2 ^ 32 := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (h n (by omega_arith))
    omega_arith

theorem val32_append (f : Nat → Nat) (m : Nat) :
    ∀ n, val32 f (m + n) = val32 f m + 2 ^ (32 * m) * val32 (fun k => f (m + k)) n
  | 0 => by simp [val32]
  | n + 1 => by
    rw [← Nat.add_assoc, val32_succ, val32_append f m n, val32_succ, Nat.mul_add (2 ^ (32 * m)),
      ← Nat.mul_assoc, ← Nat.pow_add, Nat.mul_add 32 m n]
    omega_arith

/-- A sum `n m + hi + lo` of words is below `2⁶⁴`. -/
theorem umaal_lt {n m h l : Nat} (hn : n < 2 ^ 32) (hm : m < 2 ^ 32) (hh : h < 2 ^ 32) (hl : l < 2 ^ 32) :
    n * m + h + l < 2 ^ 64 := by
  have : n * m ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega_arith) (by omega_arith)
  omega_arith

/-! ## The numbers of a chain -/

/-- The carry into step `k` of the chain `n m_k + c + x_k`, from `cin`. -/
def uc (n : Nat) (m x : Nat → Nat) (cin : Nat) : Nat → Nat
  | 0 => cin
  | k + 1 => (n * m k + uc n m x cin k + x k) / 2 ^ 32

/-- Word `k` of the chain. -/
def uo (n : Nat) (m x : Nat → Nat) (cin k : Nat) : Nat := (n * m k + uc n m x cin k + x k) % 2 ^ 32

theorem uc_succ (n : Nat) (m x : Nat → Nat) (cin k : Nat) :
    uc n m x cin (k + 1) = (n * m k + uc n m x cin k + x k) / 2 ^ 32 := rfl

theorem uo_lt (n : Nat) (m x : Nat → Nat) (cin k : Nat) : uo n m x cin k < 2 ^ 32 :=
  Nat.mod_lt _ (by decide)

theorem uc_val (n : Nat) (m x : Nat → Nat) (cin : Nat) :
    ∀ k, val32 (uo n m x cin) k + 2 ^ (32 * k) * uc n m x cin k = n * val32 m k + val32 x k + cin
  | 0 => by simp [val32, uc]
  | k + 1 => by
    have ih := uc_val n m x cin k
    rw [val32_succ, val32_succ, val32_succ, uc_succ, Nat.mul_succ, Nat.pow_add, uo]
    have e : 2 ^ (32 * k) * ((n * m k + uc n m x cin k + x k) % 2 ^ 32) +
        2 ^ (32 * k) * 2 ^ 32 * ((n * m k + uc n m x cin k + x k) / 2 ^ 32) =
          2 ^ (32 * k) * (n * m k) + 2 ^ (32 * k) * uc n m x cin k + 2 ^ (32 * k) * x k := by
      rw [Nat.mul_assoc, ← Nat.mul_add, Nat.mod_add_div, Nat.mul_add, Nat.mul_add]
    rw [Nat.mul_add n, Nat.mul_left_comm n]
    omega_arith

/-- The chain of eight words. -/
theorem uc_val8 (n : Nat) (m x : Nat → Nat) (cin : Nat) :
    val32 (uo n m x cin) 8 + 2 ^ 256 * uc n m x cin 8 = n * val32 m 8 + val32 x 8 + cin :=
  uc_val n m x cin 8

theorem val32_lt8 {f : Nat → Nat} (h : ∀ k < 8, f k < 2 ^ 32) : val32 f 8 < 2 ^ 256 := val32_lt h

theorem val32_cons (f : Nat → Nat) : ∀ n, val32 f (n + 1) = f 0 + 2 ^ 32 * val32 (fun k => f (k + 1)) n
  | 0 => by simp [val32]
  | n + 1 => by
    rw [val32_succ, val32_cons f n, val32_succ, show 32 * (n + 1) = 32 + 32 * n by omega_arith, Nat.pow_add,
      Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

/-! ## `umaal` -/

/-- `s'` is `s` with `lo` and `hi` set to the low and high words of `r`. -/
structure Upd2 (s s' : State) (lo hi : Reg) (r : Nat) : Prop where
  glo : (s'.gpr lo).toNat = r % 2 ^ 32
  ghi : (s'.gpr hi).toNat = r / 2 ^ 32
  other : ∀ q, q ≠ lo → q ≠ hi → s'.gpr q = s.gpr q
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Upd2.rest {s s' : State} {lo hi : Reg} {r : Nat} (h : Upd2 s s' lo hi r) {ws : List Reg}
    (hl : lo ∈ ws) (hh : hi ∈ ws) : Rest ws s s' :=
  ⟨fun q hq => h.other q (fun e => hq (e ▸ hl)) (fun e => hq (e ▸ hh)), h.rd, h.wr, h.sp⟩

theorem wp_umaal {is : List Instr} {s : State} {Q : State → Prop} {lo hi n m : Reg} (hne : lo ≠ hi)
    (hr : (s.gpr n).toNat * (s.gpr m).toNat + (s.gpr hi).toNat + (s.gpr lo).toNat < 2 ^ 64)
    (k : ∀ s', Upd2 s s' lo hi ((s.gpr n).toNat * (s.gpr m).toNat + (s.gpr hi).toNat + (s.gpr lo).toNat) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.umaal lo hi n m :: is)) s Q := by
  generalize hR : (s.gpr n).toNat * (s.gpr m).toNat + (s.gpr hi).toNat + (s.gpr lo).toNat = R at hr k
  refine WP.cons (s' := (s.setReg lo (BitVec.ofNat 32 R)).setReg hi (BitVec.ofNat 32 (R / 2 ^ 32)))
    (by simp only [exec, hne, ↓reduceIte, hR]) (k _ ⟨?_, ?_, ?_, rfl, rfl, rfl, rfl⟩)
  · simp only [State.setReg, hne, ↓reduceIte, BitVec.toNat_ofNat]
  · simp only [State.setReg, ↓reduceIte, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by rw [Nat.div_lt_iff_lt_mul (by decide)]; exact hr)
  · intro q h1 h2; simp only [State.setReg, h1, h2, ↓reduceIte]

/-! ## The code -/

/-- `s'` is `s` but for the registers other than `r0`, the flags and the
memory: all that the arithmetic keeps. -/
structure Kp (s s' : State) : Prop where
  r0 : s'.gpr .r0 = s.gpr .r0
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Kp.refl (s : State) : Kp s s := ⟨rfl, rfl, rfl, rfl⟩

theorem Kp.trans {s₁ s₂ s₃ : State} (h₁ : Kp s₁ s₂) (h₂ : Kp s₂ s₃) : Kp s₁ s₃ :=
  ⟨h₂.r0.trans h₁.r0, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

theorem Kp.ctx {e : Nat} {b : BitVec 32} {s s' : State} (k : Kp s s') (hc : CtxN e b s) : CtxN e b s' :=
  ⟨by rw [k.r0, hc.r0], hc.fit, by rw [k.wr]; exact hc.wr⟩

theorem Kp.of_upd {s s' : State} {d : Reg} {v : BitVec 32} (u : Upd s s' d v) (hd : Reg.r0 ≠ d) : Kp s s' :=
  ⟨u.other _ hd, u.rd, u.wr, u.sp⟩

theorem Kp.of_mupd {s s' : State} {m : Mem} (u : Mupd s s' m) : Kp s s' :=
  ⟨by rw [u.gpr], u.rd, u.wr, u.sp⟩

theorem Kp.of_rest {s s' : State} {ws : List Reg} (h : Rest ws s s') (h0 : Reg.r0 ∉ ws) : Kp s s' :=
  ⟨h.gpr _ h0, h.rd, h.wr, h.sp⟩

/-- What the preparation of a step leaves: all but the registers `T` and `X`. -/
structure UKeep (X : Reg) (T : List Reg) (s s' : State) : Prop where
  keep : ∀ r, r ∉ T → r ≠ X → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

/-- After `k` steps of a chain from `s0`: into the registers `X`, with the
carry in `C`, and the temporaries `T`. -/
structure UInv (X : Nat → Reg) (C : Reg) (T : List Reg) (nv : Nat) (mv xv : Nat → Nat) (cin : Nat)
    (s0 : State) (k : Nat) (s : State) : Prop where
  keep : ∀ r, r ∉ T → r ≠ C → (∀ j < k, r ≠ X j) → s.gpr r = s0.gpr r
  mem : s.mem = s0.mem
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  c : (s.gpr C).toNat = uc nv mv xv cin k
  outs : ∀ j < k, (s.gpr (X j)).toNat = uo nv mv xv cin j

theorem UInv.kp {X : Nat → Reg} {C : Reg} {T : List Reg} {nv : Nat} {mv xv : Nat → Nat} {cin : Nat}
    {s0 s : State} {k : Nat} (h : UInv X C T nv mv xv cin s0 k s) (hT : Reg.r0 ∉ T) (hC : Reg.r0 ≠ C)
    (hX : ∀ j < k, Reg.r0 ≠ X j) : Kp s0 s := ⟨h.keep _ hT hC hX, h.rd, h.wr, h.sp⟩

theorem uchain_ok {X : Nat → Reg} {C N : Reg} {M : Nat → Reg} {T : List Reg} {pre : Nat → List Instr}
    {n : Nat} {nv : Nat} {mv xv : Nat → Nat} {cin : Nat} {s0 : State}
    (hXC : ∀ j < n, X j ≠ C) (hXT : ∀ j < n, X j ∉ T) (hCT : C ∉ T)
    (hinj : ∀ i < n, ∀ j < n, X i = X j → i = j) (h0 : (s0.gpr C).toNat = cin)
    (hpre : ∀ k < n, ∀ s, UInv X C T nv mv xv cin s0 k s →
      WP isa (.block (pre k)) s fun s' => (s'.gpr (X k)).toNat = xv k ∧ (s'.gpr N).toNat = nv ∧
        (s'.gpr (M k)).toNat = mv k ∧ UKeep (X k) T s s') :
    WP isa (.block ((List.range n).flatMap fun k => pre k ++ ([.umaal (X k) C N (M k)] : List Instr))) s0
      (UInv X C T nv mv xv cin s0 n) := by
  refine wp_range_flatMap (M := isa) (UInv X C T nv mv xv cin s0) (fun k s hk h => ?_) n (Nat.le_refl _) s0
    ⟨fun _ _ _ _ => rfl, rfl, rfl, rfl, rfl, h0, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  refine WP.append (hpre k hk s h) fun s1 ⟨hx, hn, hm, hf⟩ => ?_
  have hc1 : s1.gpr C = s.gpr C := hf.keep C hCT fun e => hXC k hk e.symm
  refine wp_umaal (hXC k hk) (umaal_lt (s1.gpr N).isLt (s1.gpr (M k)).isLt (s1.gpr C).isLt
    (s1.gpr (X k)).isLt) fun s2 u2 => WP.block_nil ?_
  rw [hn, hm, hc1, h.c, hx] at u2
  refine ⟨fun r hT hC hX => ?_, by rw [u2.mem, hf.mem, h.mem], by rw [u2.rd, hf.rd, h.rd],
    by rw [u2.wr, hf.wr, h.wr], by rw [u2.sp, hf.sp, h.sp], ?_, fun j hj => ?_⟩
  · rw [u2.other r (hX k (Nat.lt_succ_self k)) hC, hf.keep r hT (hX k (Nat.lt_succ_self k)),
      h.keep r hT hC fun j hj => hX j (Nat.lt_succ_of_lt hj)]
  · rw [u2.ghi]; rfl
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · have hjn : j < n := Nat.lt_trans hj hk
      have hne : X j ≠ X k := fun e => absurd (hinj j hjn k hk e) (Nat.ne_of_lt hj)
      rw [u2.other _ hne (hXC j hjn), hf.keep _ (hXT j hjn) hne]; exact h.outs j hj
    · rw [u2.glo]; rfl

/-! ## Elements of eight words -/

/-- The number of the element at `o`. -/
def W (m : Mem) (B : Addr) (o : Nat) : Nat := val32 (fun k => wd m B (o + 4 * k)) 8

theorem W_lt (m : Mem) (B : Addr) (o : Nat) : W m B o < 2 ^ 256 := val32_lt8 fun _ _ => wd_lt m B _

theorem W_of {m : Mem} {B : Addr} {o : Nat} {f : Nat → Nat} (h : ∀ k < 8, wd m B (o + 4 * k) = f k) :
    W m B o = val32 f 8 := val32_congr h

/-- An element in a frame that does not overlap it. -/
theorem W_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {B : Addr} {o : Nat}
    (hd : ∀ r ∈ rs, ∀ k < 8, (⟨B + BitVec.ofNat 64 (o + 4 * k), 4⟩ : Region).Disjoint r) :
    W m' B o = W m B o := val32_congr fun k hk => wd_frame hf fun r hr => hd r hr k hk

section
variable {b : BitVec 32}

/-- The registers `X` stored as the element at `o`. -/
theorem stores_ok {X : Nat → Reg} {o : Nat} (ho : o + 32 ≤ 4096) {s : State} (hc : Ctx b s) :
    WP isa (.block (stores o X)) s fun s' =>
      (∀ j < 8, wd s'.mem (State.addr b) (o + 4 * j) = (s.gpr (X j)).toNat) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 o, 32⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ Rest [] s s' := by
  unfold stores
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun m s' => (∀ j < m, wd s'.mem (State.addr b) (o + 4 * j) = (s.gpr (X j)).toNat) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 o, 4 * m⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ Rest [] s s')
    (fun m s' hm ⟨h1, h2, h3, h4⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, rfl, Rest.refl _ _⟩) fun s' h => h
  refine str0_ok (hc.of_rest h4 (by decide)) (d := o + 4 * m) (by omega_using [ho, hm]) fun s2 u2 =>
    WP.block_nil ⟨fun j hj => ?_, ?_, by rw [u2.gpr, h3], h4.trans (u2.rest _)⟩
  · rw [u2.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega_using [hj]) (by omega_arith) (by omega_using [ho, hm])]; exact h1 j hj
    · rw [wd_write_self, h3]
  · rw [u2.mem]
    exact (h2.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_using [])⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (by omega_using []) (by omega_using []) (by omega_using [ho, hm]))

end

end VG.Proof.X25519.Arm.Words

end

end

/-!
# X25519 on 32-bit ARM with `umaal`: multiplication

The fold at bit 255 (`fold19_ok`), for any registers, and `mul` (`mul_ok`):
after `i` rows the words of `ACC` below `i` and the eight registers
`rg (i + 1 + j)` hold `a_{<i} · b` (`RowInv`); `lo + 38 hi` and the fold
leave a number below `2p`, congruent to the product.
-/

@[expose] public section

namespace VG.Proof.X25519.Arm.Words

open VG VG.Arm VG.Impl.X25519.Arm.Words
open VG.Proof.X25519.Arm
open VG.Spec.X25519 (P)
open VG.Proof.X25519 (fold255 fold256)

/-! ## The registers of a product -/

theorem rg_mod (n : Nat) : rg n = rg (n % 9) := by simp only [rg, Nat.mod_mod]

theorem rg_inj9 : ∀ i < 9, ∀ j < 9, rg i = rg j → i = j := by decide

theorem rg_eq {m n : Nat} (h : rg m = rg n) : m % 9 = n % 9 :=
  rg_inj9 _ (Nat.mod_lt _ (by decide)) _ (Nat.mod_lt _ (by decide)) ((rg_mod m).symm.trans (h.trans (rg_mod n)))

theorem rg_of_mod {m n : Nat} (h : m % 9 = n % 9) : rg m = rg n := by rw [rg_mod m, rg_mod n, h]

theorem rg_ne9 : ∀ i < 9, Reg.r0 ≠ rg i ∧ Reg.r1 ≠ rg i ∧ Reg.r2 ≠ rg i ∧ Reg.r12 ≠ rg i ∧ Reg.lr ≠ rg i := by
  decide

theorem rg_ne (n : Nat) : Reg.r0 ≠ rg n ∧ Reg.r1 ≠ rg n ∧ Reg.r2 ≠ rg n ∧ Reg.r12 ≠ rg n ∧ Reg.lr ≠ rg n := by
  rw [rg_mod n]; exact rg_ne9 _ (Nat.mod_lt _ (by decide))

/-! ## The fold at bit 255 -/

theorem toNat_bic31 (x : BitVec 32) : (x &&& ~~~(0x80000000 : BitVec 32)).toNat = x.toNat % 2 ^ 31 := by
  rw [show ~~~(0x80000000 : BitVec 32) = 0x7fffffff by decide, BitVec.toNat_and,
    show (0x7fffffff : BitVec 32).toNat = 2 ^ 31 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- The number `x + 2²⁵⁶ c` with bit 255 and above folded in as 19 times
itself. -/
theorem fold19_num {x : Nat → Nat} (hx : x 7 < 2 ^ 32) (hlo : val32 x 7 < 2 ^ 224) {cv : Nat} (hcv : cv < 2 ^ 26)
    {r c8 : Nat}
    (h : r + 2 ^ 256 * c8 = val32 (fun k => if k = 7 then x 7 % 2 ^ 31 else x k) 8 + 19 * (x 7 / 2 ^ 31 + 2 * cv)) :
    r % P = (val32 x 8 + 2 ^ 256 * cv) % P ∧ r < 2 * P := by
  have hP : P = 2 ^ 255 - 19 := rfl
  have e7 : val32 (fun k => if k = 7 then x 7 % 2 ^ 31 else x k) 7 = val32 x 7 :=
    val32_congr fun k hk => by simp only [show k ≠ 7 by omega_arith, ite_false]
  rw [val32_succ, e7] at h
  simp only [ite_true] at h
  have hc8 : c8 = 0 := by omega_arith
  subst hc8
  have hr : r = (val32 x 7 + 2 ^ 224 * (x 7 % 2 ^ 31)) + 19 * (x 7 / 2 ^ 31 + 2 * cv) := by omega_arith
  refine ⟨?_, by omega_arith⟩
  have e8 : val32 x 8 = val32 x 7 + 2 ^ 224 * x 7 := rfl
  rw [hr, ← fold255, e8]
  congr 1
  omega_arith

theorem fold19_ok {X : Nat → Reg} {c : Reg} (hinj : ∀ i < 8, ∀ j < 8, X i = X j → i = j)
    (hX : ∀ j < 8, Reg.r12 ≠ X j ∧ Reg.lr ≠ X j ∧ c ≠ X j) (hc : c ≠ .r12 ∧ c ≠ .lr)
    {s : State} {cv : Nat} (hcv : (s.gpr c).toNat = cv) (hb : cv < 2 ^ 26) :
    WP isa (.block (fold19 X c)) s fun s' =>
      val32 (fun k => (s'.gpr (X k)).toNat) 8 % P =
        (val32 (fun k => (s.gpr (X k)).toNat) 8 + 2 ^ 256 * cv) % P ∧
      val32 (fun k => (s'.gpr (X k)).toNat) 8 < 2 * P ∧
      (∀ r, r ≠ .r12 → r ≠ .lr → (∀ j < 8, r ≠ X j) → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have h7 := hX 7 (by decide)
  have hx7 := (s.gpr (X 7)).isLt
  unfold fold19
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_lsr (by decide)) fun s1 u1 => wp_dp (op2_lsl (by decide)) fun s2 u2 =>
    wp_dp (op2_imm (by decide)) fun s3 u3 => wp_dp (op2_lsl (by decide)) fun s4 u4 =>
    wp_dp (op2_lsl (by decide)) fun s5 u5 => wp_mov (op2_imm (by decide)) fun s6 u6 => ?_
  -- `q` in `r12`, then `19 q`.
  have e2 : (s2.gpr .r12).toNat = (s.gpr (X 7)).toNat / 2 ^ 31 + 2 * cv := by
    rw [u2.gpr]
    show (s1.gpr .r12 + s1.gpr c <<< 1).toNat = _
    rw [u1.gpr, u1.other c hc.1, BitVec.toNat_add, toNat_shr, toNat_shl, hcv]
    omega_arith
  have e4 : (s4.gpr .lr).toNat = 3 * ((s.gpr (X 7)).toNat / 2 ^ 31 + 2 * cv) := by
    rw [u4.gpr]
    show (s3.gpr .r12 + s3.gpr .r12 <<< 1).toNat = _
    rw [u3.other _ h7.1, BitVec.toNat_add, toNat_shl, e2]
    omega_arith
  have e5 : (s5.gpr .r12).toNat = 19 * ((s.gpr (X 7)).toNat / 2 ^ 31 + 2 * cv) := by
    rw [u5.gpr]
    show (s4.gpr .lr + s4.gpr .r12 <<< 4).toNat = _
    rw [BitVec.toNat_add, toNat_shl, e4, u4.other .r12 (by decide), u3.other .r12 h7.1, e2]
    omega_arith
  have e3 : (s3.gpr (X 7)).toNat = (s.gpr (X 7)).toNat % 2 ^ 31 := by
    rw [u3.gpr]
    show (s2.gpr (X 7) &&& ~~~(0x80000000 : BitVec 32)).toNat = _
    rw [toNat_bic31, u2.other _ h7.1.symm, u1.other _ h7.1.symm]
  -- The words before the chain.
  have ex : ∀ k < 8, (s6.gpr (X k)).toNat =
      if k = 7 then (s.gpr (X 7)).toNat % 2 ^ 31 else (s.gpr (X k)).toNat := by
    intro k hk
    have hk' := hX k hk
    rw [u6.other _ hk'.2.1.symm, u5.other _ hk'.1.symm, u4.other _ hk'.2.1.symm]
    by_cases h : k = 7
    · subst h; rw [e3]; simp only [ite_true]
    · simp only [h, ite_false]
      rw [u3.other _ (fun e => h (hinj k hk 7 (by decide) e)), u2.other _ hk'.1.symm, u1.other _ hk'.1.symm]
  refine WP.mono (uchain_ok (X := X) (C := .r12) (N := .lr) (M := fun _ => .lr) (T := []) (pre := fun _ => [])
    (nv := 0) (mv := fun _ => 0)
    (xv := fun k => if k = 7 then (s.gpr (X 7)).toNat % 2 ^ 31 else (s.gpr (X k)).toNat)
    (cin := 19 * ((s.gpr (X 7)).toNat / 2 ^ 31 + 2 * cv)) (fun j hj => (hX j hj).1.symm)
    (fun _ _ => List.not_mem_nil) List.not_mem_nil hinj (by rw [u6.other _ (by decide), e5])
    fun k hk t ht => WP.block_nil ⟨?_, ?_, ?_, fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩) fun s7 h7' => ?_
  · rw [ht.keep _ List.not_mem_nil (hX k hk).1.symm fun j hj e => absurd (hinj k hk j (Nat.lt_trans hj hk) e)
      (Nat.ne_of_gt hj)]
    exact ex k hk
  · rw [ht.keep _ List.not_mem_nil (by decide) fun j hj => (hX j (Nat.lt_trans hj hk)).2.1, u6.gpr]; rfl
  · rw [ht.keep _ List.not_mem_nil (by decide) fun j hj => (hX j (Nat.lt_trans hj hk)).2.1, u6.gpr]; rfl
  · have hv := uc_val8 0 (fun _ => 0)
      (fun k => if k = 7 then (s.gpr (X 7)).toNat % 2 ^ 31 else (s.gpr (X k)).toNat)
      (19 * ((s.gpr (X 7)).toNat / 2 ^ 31 + 2 * cv))
    rw [Nat.zero_mul, Nat.zero_add] at hv
    have hlo : val32 (fun k => (s.gpr (X k)).toNat) 7 < 2 ^ 224 := val32_lt fun k _ => (s.gpr (X k)).isLt
    have hn := fold19_num (x := fun k => (s.gpr (X k)).toNat) hx7 hlo hb hv
    rw [val32_congr (g := uo 0 (fun _ => 0)
      (fun k => if k = 7 then (s.gpr (X 7)).toNat % 2 ^ 31 else (s.gpr (X k)).toNat)
      (19 * ((s.gpr (X 7)).toNat / 2 ^ 31 + 2 * cv))) h7'.outs]
    refine ⟨hn.1, hn.2, fun r h12 hlr hr => ?_, ?_, ?_, ?_, ?_⟩
    · rw [h7'.keep r List.not_mem_nil h12 hr, u6.other r hlr, u5.other r h12, u4.other r hlr,
        u3.other r (hr 7 (by decide)), u2.other r h12, u1.other r h12]
    · rw [h7'.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    · rw [h7'.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd]
    · rw [h7'.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]
    · rw [h7'.sp, u6.sp, u5.sp, u4.sp, u3.sp, u2.sp, u1.sp]

/-! ## Multiplication -/

/-- A row of a product: the low word joins `lo`, and the others and the carry
are the accumulator `t'`. -/
theorem row_num {lo lo' t t' y : Nat → Nat} {i a pa : Nat}
    (hv : val32 lo i + 2 ^ (32 * i) * val32 t 8 = pa * val32 y 8)
    (hlo : ∀ k < i, lo' k = lo k) (hi : lo' i = uo a y t 0 0)
    (ht : ∀ j < 7, t' j = uo a y t 0 (j + 1)) (h7 : t' 7 = uc a y t 0 8) :
    val32 lo' (i + 1) + 2 ^ (32 * (i + 1)) * val32 t' 8 = (pa + 2 ^ (32 * i) * a) * val32 y 8 := by
  have hc := uc_val8 a y t 0
  rw [val32_cons (uo a y t 0) 7] at hc
  have e1 : val32 lo' (i + 1) = val32 lo i + 2 ^ (32 * i) * uo a y t 0 0 := by
    rw [val32_succ, val32_congr hlo, hi]
  have e2 : val32 t' 8 = val32 (fun k => uo a y t 0 (k + 1)) 7 + 2 ^ 224 * uc a y t 0 8 := by
    rw [val32_succ, val32_congr ht, h7]
  rw [e1, e2, show 32 * (i + 1) = 32 * i + 32 by omega_arith, Nat.pow_add]
  generalize 2 ^ (32 * i) = E at *
  generalize val32 (fun k => uo a y t 0 (k + 1)) 7 = S7 at *
  generalize uo a y t 0 0 = u0 at *
  generalize uc a y t 0 8 = c8 at *
  generalize val32 y 8 = Vy at *
  generalize val32 t 8 = Vt at *
  generalize val32 lo i = L at *
  have key : E * 2 ^ 32 * (S7 + 2 ^ 224 * c8) = E * (2 ^ 32 * S7 + 2 ^ 256 * c8) := by
    rw [Nat.mul_assoc, Nat.mul_add, ← Nat.mul_assoc (2 ^ 32)]
  rw [key, Nat.add_assoc, ← Nat.mul_add, show u0 + (2 ^ 32 * S7 + 2 ^ 256 * c8) = a * Vy + Vt by omega_arith,
    Nat.mul_add, Nat.add_mul, ← hv, Nat.mul_assoc]
  omega_arith

section
variable {b : BitVec 32}

theorem zeros_ok {s : State} :
    WP isa (.block ((List.range 8).flatMap fun j => ([.mov (rg (j + 1)) (.imm 0)] : List Instr))) s fun s' =>
      (∀ j < 8, s'.gpr (rg (j + 1)) = 0) ∧ Kp s s' ∧ s'.mem = s.mem := by
  refine wp_range_flatMap (M := isa)
    (fun m s' => (∀ j < m, s'.gpr (rg (j + 1)) = 0) ∧ Kp s s' ∧ s'.mem = s.mem)
    (fun m s' hm ⟨h1, h2, h3⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Kp.refl _, rfl⟩
  refine wp_mov (op2_imm (by decide)) fun s2 u2 => WP.block_nil
    ⟨fun j hj => ?_, h2.trans (Kp.of_upd u2 (rg_ne _).1), by rw [u2.mem, h3]⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
  · rw [u2.other _ fun e => by have := rg_eq e; omega_using [this, hj, hm]]; exact h1 j hj
  · exact u2.gpr

/-- After `i` rows of the product of `[a]` and `[c]` from `s0`: its low words
in `ACC`, and the accumulator in the registers. -/
structure RowInv (b : BitVec 32) (a c : Nat) (s0 : State) (i : Nat) (s : State) : Prop where
  kp : Kp s0 s
  frame : Frame [⟨State.addr b + BitVec.ofNat 64 ACC, 4 * i⟩] s0.mem s.mem
  val : val32 (fun k => wd s.mem (State.addr b) (ACC + 4 * k)) i +
      2 ^ (32 * i) * val32 (fun j => (s.gpr (rg (i + 1 + j))).toNat) 8 =
        val32 (fun k => wd s0.mem (State.addr b) (a + 4 * k)) i * W s0.mem (State.addr b) c

theorem mulRow_ok {a c i : Nat} (ha : a + 32 ≤ ACC) (hb : c + 32 ≤ ACC) (hi : i < 8) {s0 s : State}
    (hc : Ctx b s0) (h : RowInv b a c s0 i s) :
    WP isa (.block (mulRow a c i)) s (RowInv b a c s0 (i + 1)) := by
  have hA : ACC = 544 := rfl
  have hcs : Ctx b s := h.kp.ctx hc
  have hw : ∀ d, d + 4 ≤ ACC → wd s.mem (State.addr b) d = wd s0.mem (State.addr b) d := fun d hd =>
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inl (by omega_using [hd])) (by omega_using [hd, hA]) (by omega_using [hi, hA])
  have r2n : ∀ n, rg n ∉ [Reg.r2] := fun n hm => (rg_ne n).2.2.1 (List.mem_singleton.mp hm).symm
  unfold mulRow
  simp only [List.cons_append, List.nil_append]
  refine ldr0_ok hcs (d := a + 4 * i) (by omega_using [ha, hA, hi]) fun s1 u1 =>
    wp_mov (op2_imm (by decide)) fun s2 u2 => ?_
  have k2 : Kp s s2 := (Kp.of_upd u1 (by decide)).trans (Kp.of_upd u2 (rg_ne _).1)
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  refine WP.append (uchain_ok (X := fun j => rg (i + 1 + j)) (C := rg i) (N := .r1) (M := fun _ => .r2)
    (T := [.r2]) (pre := fun j => [.ldr .r2 .r0 (c + 4 * j)]) (nv := wd s0.mem (State.addr b) (a + 4 * i))
    (mv := fun j => wd s0.mem (State.addr b) (c + 4 * j)) (xv := fun j => (s.gpr (rg (i + 1 + j))).toNat)
    (cin := 0) (fun j hj e => by have := rg_eq e; omega_using [this, hj])
    (fun j _ => r2n _) (r2n _) (fun j hj j' hj' e => by have := rg_eq e; omega_using [this, hj, hj'])
    (by rw [u2.gpr]; rfl) fun j hj t ht => ?_) fun s3 h3 => ?_
  · have kt : Kp s2 t := ht.kp (by decide) (rg_ne _).1 fun _ _ => (rg_ne _).1
    refine ldr0_ok (kt.ctx (k2.ctx hcs)) (d := c + 4 * j) (by omega_using [hb, hA, hj]) fun t1 v1 =>
      WP.block_nil ⟨?_, ?_, ?_, fun r hT _ => v1.other r fun e => hT (e ▸ List.mem_singleton_self _), v1.mem,
        v1.rd, v1.wr, v1.sp⟩
    · rw [v1.other _ (rg_ne _).2.2.1.symm, ht.keep _ (r2n _) (fun e => by have := rg_eq e; omega_using [this, hj])
        (fun j' hj' e => by have := rg_eq e; omega_using [this, hj, hj']),
        u2.other _ (fun e => by have := rg_eq e; omega_using [this, hj]), u1.other _ (rg_ne _).2.1.symm]
    · rw [v1.other _ (by decide), ht.keep _ (by decide) (rg_ne _).2.1 (fun _ _ => (rg_ne _).2.1),
        u2.other _ (rg_ne _).2.1, u1.gpr]
      exact hw _ (by omega_using [ha, hi])
    · rw [v1.gpr, ht.mem, hm2]
      exact hw _ (by omega_using [hb, hj])
  · have k3 : Kp s2 s3 := h3.kp (by decide) (rg_ne _).1 fun _ _ => (rg_ne _).1
    refine str0_ok (k3.ctx (k2.ctx hcs)) (d := ACC + 4 * i) (by omega_using [hA, hi]) fun s4 u4 =>
      WP.block_nil ⟨h.kp.trans (k2.trans (k3.trans (Kp.of_mupd u4))), ?_, ?_⟩
    · rw [u4.mem, h3.mem, hm2]
      exact (h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_using [])⟩).writeW
        (List.mem_singleton_self _) _ (Offset.contains _ (by omega_using []) (by omega_using []) (by omega_using [hA, hi]))
    · have hm4 : s4.mem = s.mem.writeW (State.addr b + BitVec.ofNat 64 (ACC + 4 * i)) (s3.gpr (rg (i + 1))) := by
        rw [u4.mem, h3.mem, hm2]
      have := row_num (lo' := fun k => wd s4.mem (State.addr b) (ACC + 4 * k))
        (t' := fun j => (s4.gpr (rg (i + 1 + 1 + j))).toNat) (a := wd s0.mem (State.addr b) (a + 4 * i))
        h.val ?_ ?_ ?_ ?_
      · rw [val32_succ]; exact this
      · intro k hk
        show wd s4.mem _ _ = _
        rw [hm4, wd_write_other _ _ _ (by omega_using [hk]) (by omega_using [hA, hk, hi]) (by omega_using [hA, hi])]
      · show wd s4.mem _ _ = _
        rw [hm4, wd_write_self]; exact h3.outs 0 (by decide)
      · intro j hj
        show (s4.gpr _).toNat = _
        rw [u4.gpr, show rg (i + 1 + 1 + j) = rg (i + 1 + (j + 1)) from congrArg rg (by omega_arith)]
        exact h3.outs (j + 1) (by omega_using [hj])
      · show (s4.gpr _).toNat = _
        rw [u4.gpr, rg_of_mod (show (i + 1 + 1 + 7) % 9 = i % 9 by omega_arith)]; exact h3.c

/-- `[o] = [a] · [c]`: a number below `2p`, congruent to the product. -/
theorem mul_ok {o a c : Nat} (ho : o + 32 ≤ 4096) (ha : a + 32 ≤ ACC) (hb : c + 32 ≤ ACC) {s : State}
    (hc : Ctx b s) :
    WP isa (.block (mul o a c)) s fun s' =>
      Kp s s' ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 o, 32⟩, ⟨State.addr b + BitVec.ofNat 64 ACC, 32⟩] s.mem s'.mem ∧
      W s'.mem (State.addr b) o % P = (W s.mem (State.addr b) a * W s.mem (State.addr b) c) % P ∧
      W s'.mem (State.addr b) o < 2 * P := by
  have hA : ACC = 544 := rfl
  unfold mul
  simp only [List.append_assoc]
  refine WP.append zeros_ok fun s1 ⟨hz, k1, hm1⟩ => ?_
  have hc1 : Ctx b s1 := k1.ctx hc
  have ez : val32 (fun j => (s1.gpr (rg (0 + 1 + j))).toNat) 8 = 0 := by
    rw [val32_congr (g := fun _ => 0) fun j hj => by
      show (s1.gpr (rg (0 + 1 + j))).toNat = 0
      rw [show rg (0 + 1 + j) = rg (j + 1) from congrArg rg (by omega_arith), hz j hj]; rfl, val32_zero_fn]
  have h0 : RowInv b a c s1 0 s1 := ⟨Kp.refl _, Frame.refl _ _, by rw [ez]; simp [val32]⟩
  refine WP.append (wp_range_flatMap (M := isa) (RowInv b a c s1) (fun i t hi h => mulRow_ok ha hb hi hc1 h) 8
    (Nat.le_refl _) s1 h0) fun s8 h8 => ?_
  have hc8 : Ctx b s8 := h8.kp.ctx hc1
  unfold mulFold
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_imm (by decide)) fun s9 u9 => wp_mov (op2_imm (by decide)) fun s10 u10 => ?_
  have k10 : Kp s8 s10 := (Kp.of_upd u9 (by decide)).trans (Kp.of_upd u10 (by decide))
  have hm10 : s10.mem = s8.mem := by rw [u10.mem, u9.mem]
  refine WP.append (uchain_ok (X := fun k => rg (k + 8)) (C := .r1) (N := .r2) (M := rg) (T := [])
    (pre := fun k => [.ldr (rg (k + 8)) .r0 (ACC + 4 * k)]) (nv := 38)
    (mv := fun k => (s8.gpr (rg (8 + 1 + k))).toNat) (xv := fun k => wd s8.mem (State.addr b) (ACC + 4 * k))
    (cin := 0) (fun j _ => (rg_ne _).2.1.symm) (fun _ _ => List.not_mem_nil) List.not_mem_nil
    (fun j hj j' hj' e => by have := rg_eq e; omega_using [this, hj, hj'])
    (by rw [u10.other _ (by decide), u9.gpr]; rfl) fun k hk t ht => ?_) fun s11 h11 => ?_
  · have kt : Kp s10 t := ht.kp List.not_mem_nil (by decide) fun _ _ => (rg_ne _).1
    refine ldr0_ok (kt.ctx (k10.ctx hc8)) (d := ACC + 4 * k) (by omega_using [hA, hk]) fun t1 v1 =>
      WP.block_nil ⟨?_, ?_, ?_, fun r _ hX => v1.other r hX, v1.mem, v1.rd, v1.wr, v1.sp⟩
    · rw [v1.gpr, ht.mem, hm10]; rfl
    · rw [v1.other _ (rg_ne _).2.2.1, ht.keep _ List.not_mem_nil (by decide) (fun _ _ => (rg_ne _).2.2.1),
        u10.gpr]; rfl
    · rw [v1.other _ (fun e => by have := rg_eq e; omega_using [this, hk]),
        ht.keep _ List.not_mem_nil (rg_ne _).2.1.symm (fun j hj e => by have := rg_eq e; omega_using [this, hj, hk]),
        u10.other _ (rg_ne _).2.2.1.symm, u9.other _ (rg_ne _).2.1.symm,
        rg_of_mod (show k % 9 = (8 + 1 + k) % 9 by omega_arith)]
  · -- `lo + 38 hi`, and its carry, at most 38.
    have hv := uc_val8 38 (fun k => (s8.gpr (rg (8 + 1 + k))).toNat)
      (fun k => wd s8.mem (State.addr b) (ACC + 4 * k)) 0
    have h8v := h8.val
    have hhi : val32 (fun k => (s8.gpr (rg (8 + 1 + k))).toNat) 8 < 2 ^ 256 :=
      val32_lt8 fun k _ => (s8.gpr _).isLt
    have hlo : val32 (fun k => wd s8.mem (State.addr b) (ACC + 4 * k)) 8 < 2 ^ 256 :=
      val32_lt8 fun k _ => wd_lt _ _ _
    have hc38 : uc 38 (fun k => (s8.gpr (rg (8 + 1 + k))).toNat)
        (fun k => wd s8.mem (State.addr b) (ACC + 4 * k)) 0 8 < 2 ^ 26 := by omega_arith
    have k11 : Kp s10 s11 := h11.kp List.not_mem_nil (by decide) fun _ _ => (rg_ne _).1
    refine WP.append (fold19_ok (X := fun k => rg (k + 8)) (c := .r1)
      (fun j hj j' hj' e => by have := rg_eq e; omega_using [this, hj, hj'])
      (fun j _ => ⟨(rg_ne _).2.2.2.1, (rg_ne _).2.2.2.2, (rg_ne _).2.1⟩) (by decide) h11.c hc38)
      fun s12 ⟨hval, hle, hkeep, hm12, hrd, hwr, hsp⟩ => ?_
    have k12 : Kp s11 s12 := ⟨hkeep _ (by decide) (by decide) fun _ _ => (rg_ne _).1, hrd, hwr, hsp⟩
    have hc12 : Ctx b s12 := k12.ctx (k11.ctx (k10.ctx hc8))
    refine WP.mono (stores_ok ho hc12) fun s13 ⟨hw, hf, hg, hr⟩ => ⟨?_, ?_, ?_, ?_⟩
    · exact k1.trans (h8.kp.trans (k10.trans (k11.trans (k12.trans (Kp.of_rest hr List.not_mem_nil)))))
    · rw [← hm1]
      refine (h8.frame.mono fun r hr => by simp [List.mem_singleton.mp hr]).trans ?_
      rw [← hm10, ← h11.mem, ← hm12]
      exact hf.mono fun r hr => by simp [List.mem_singleton.mp hr]
    · rw [W_of hw, hval, val32_congr (g := uo 38 (fun k => (s8.gpr (rg (8 + 1 + k))).toNat)
        (fun k => wd s8.mem (State.addr b) (ACC + 4 * k)) 0) h11.outs, hv, Nat.add_zero, Nat.add_comm, ← fold256,
        h8v, ← hm1]
      rfl
    · rw [W_of hw]; exact hle

end

end VG.Proof.X25519.Arm.Words

end

end

/-!
# X25519 on 32-bit ARM with `umaal`: sums

`add`, `sub` and `addA24` (`add_ok`, `sub_ok`, `addA24_ok`), and the full
reduction of a number below `2p` in the registers (`freeze_ok`), each a chain
that loads its operands and one that folds its carry in.
-/

@[expose] public section

namespace VG.Proof.X25519.Arm.Words

open VG VG.Arm VG.Impl.X25519.Arm.Words
open VG.Proof.X25519.Arm
open VG.Spec.X25519 (P)
open VG.Proof.X25519 (fold256)

/-! ## The registers of a sum -/

theorem xr_inj : ∀ i < 8, ∀ j < 8, xr i = xr j → i = j := by decide

theorem xr_ne (n : Nat) : Reg.r0 ≠ xr n ∧ Reg.r1 ≠ xr n ∧ Reg.r2 ≠ xr n ∧ Reg.r3 ≠ xr n ∧ Reg.r12 ≠ xr n ∧
    Reg.lr ≠ xr n := by
  unfold xr; split <;> decide

theorem xr_inj' {i j : Nat} (hi : i < 8) (hj : j < i) : xr i ≠ xr j := fun e =>
  absurd (xr_inj i hi j (Nat.lt_trans hj hi) e) (Nat.ne_of_gt hj)

/-! ## Instructions -/

theorem wp_movt {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm ++ (s.gpr d).extractLsb' 0 16 : BitVec 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movt d imm :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_mvn {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {o : Op2} {v : BitVec 32}
    (ho : o.eval s = some v) (k : ∀ s', Upd s s' d (~~~v) → WP isa (.block is) s' Q) :
    WP isa (.block (.mvn d o :: is)) s Q :=
  WP.cons (s' := s.setReg d (~~~v)) (by simp only [exec, ho, Option.map_some]) (k _ (Upd.setReg _ _ _))

section
variable {b : BitVec 32}

/-- Word `k` of `[a]` into `xr k` and of `[c]` into `r3`. -/
theorem ld2_ok {a c k : Nat} (ha : a + 4 * k + 4 ≤ 4096) (hc' : c + 4 * k + 4 ≤ 4096) {t : State}
    (hc : Ctx b t) :
    WP isa (.block [.ldr (xr k) .r0 (a + 4 * k), .ldr .r3 .r0 (c + 4 * k)]) t fun t' =>
      (t'.gpr (xr k)).toNat = wd t.mem (State.addr b) (a + 4 * k) ∧
      (t'.gpr .r3).toNat = wd t.mem (State.addr b) (c + 4 * k) ∧ UKeep (xr k) [.r3] t t' := by
  refine ldr0_ok hc (d := a + 4 * k) ha fun t1 v1 => ?_
  refine ldr0_ok ((Kp.of_upd v1 (xr_ne k).1).ctx hc) (d := c + 4 * k) hc' fun t2 v2 => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [v2.other _ (xr_ne k).2.2.2.1.symm, v1.gpr]; rfl
  · rw [v2.gpr, v1.mem]; rfl
  · exact ⟨fun r hT hX => by
      rw [v2.other r fun e => hT (e ▸ List.mem_singleton_self _), v1.other r hX],
      by rw [v2.mem, v1.mem], by rw [v2.rd, v1.rd], by rw [v2.wr, v1.wr], by rw [v2.sp, v1.sp]⟩

/-- A chain that adds `nv` times `[c]` to `[a]`, with the carry in `r1` and
`nv` in `r2`. -/
theorem ldChain_ok {a c : Nat} (ha : a + 32 ≤ 4096) (hc' : c + 32 ≤ 4096) {s : State} (hc : Ctx b s)
    {nv cin : Nat} (h1 : (s.gpr .r1).toNat = cin) (h2 : (s.gpr .r2).toNat = nv) :
    WP isa (.block ((List.range 8).flatMap fun k =>
      ([.ldr (xr k) .r0 (a + 4 * k), .ldr .r3 .r0 (c + 4 * k), .umaal (xr k) .r1 .r2 .r3] : List Instr))) s
      (UInv xr .r1 [.r3] nv (fun k => wd s.mem (State.addr b) (c + 4 * k))
        (fun k => wd s.mem (State.addr b) (a + 4 * k)) cin s 8) := by
  refine uchain_ok (X := xr) (C := .r1) (N := .r2) (M := fun _ => .r3) (T := [.r3])
    (pre := fun k => [.ldr (xr k) .r0 (a + 4 * k), .ldr .r3 .r0 (c + 4 * k)])
    (fun j _ => (xr_ne j).2.1.symm) (fun j _ hm => (xr_ne j).2.2.2.1 (List.mem_singleton.mp hm).symm)
    (by decide) xr_inj h1 fun k hk t ht => ?_
  have kt : Kp s t := ht.kp (by decide) (by decide) fun j _ => (xr_ne j).1
  refine WP.mono (ld2_ok (a := a) (c := c) (by omega_using [ha, hk]) (by omega_using [hc', hk]) (kt.ctx hc))
    fun t' ⟨hx, hm, hk'⟩ => ⟨by rw [hx, ht.mem], ?_, by rw [hm, ht.mem], hk'⟩
  rw [hk'.keep _ (by decide) (xr_ne k).2.2.1, ht.keep _ (by decide) (by decide) fun j _ => (xr_ne j).2.2.1, h2]

/-! ## Addition -/

theorem add_num {wa wc u1 c1 u2 c2 : Nat} (ha : wa < 2 * P) (hc : wc < 2 * P) (hu1 : u1 < 2 ^ 256)
    (h1 : u1 + 2 ^ 256 * c1 = 1 * wc + wa + 0) (h2 : u2 + 2 ^ 256 * c2 = u1 + 38 * c1) :
    u2 % P = (wa + wc) % P := by
  have hP : P = 2 ^ 255 - 19 := rfl
  have hc1 : c1 ≤ 1 := by omega_arith
  have hc2 : c2 = 0 := by omega_arith
  subst hc2
  rw [show u2 = u1 + 38 * c1 by omega_arith, ← fold256]
  congr 1
  omega_arith

/-- `[o] = [a] + [c]`, for operands below `2p`. -/
theorem add_ok {o a c : Nat} (ho : o + 32 ≤ 4096) (ha : a + 32 ≤ 4096) (hc' : c + 32 ≤ 4096) {s : State}
    (hc : Ctx b s) (hla : W s.mem (State.addr b) a < 2 * P) (hlc : W s.mem (State.addr b) c < 2 * P) :
    WP isa (.block (add o a c)) s fun s' =>
      Kp s s' ∧ Frame [⟨State.addr b + BitVec.ofNat 64 o, 32⟩] s.mem s'.mem ∧
      W s'.mem (State.addr b) o % P = (W s.mem (State.addr b) a + W s.mem (State.addr b) c) % P := by
  unfold add
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => wp_mov (op2_imm (by decide)) fun s2 u2 => ?_
  have k2 : Kp s s2 := (Kp.of_upd u1 (by decide)).trans (Kp.of_upd u2 (by decide))
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  refine WP.append (ldChain_ok (a := a) (c := c) ha hc' (k2.ctx hc) (nv := 1) (cin := 0)
    (by rw [u2.other _ (by decide), u1.gpr]; rfl) (by rw [u2.gpr]; rfl)) fun s3 h3 => ?_
  rw [hm2] at h3
  have hv1 := uc_val8 1 (fun k => wd s.mem (State.addr b) (c + 4 * k))
    (fun k => wd s.mem (State.addr b) (a + 4 * k)) 0
  have hu1 : val32 (uo 1 (fun k => wd s.mem (State.addr b) (c + 4 * k))
      (fun k => wd s.mem (State.addr b) (a + 4 * k)) 0) 8 < 2 ^ 256 := val32_lt8 fun k _ => uo_lt _ _ _ _ _
  have hP : P = 2 ^ 255 - 19 := rfl
  have hc1 : uc 1 (fun k => wd s.mem (State.addr b) (c + 4 * k))
      (fun k => wd s.mem (State.addr b) (a + 4 * k)) 0 8 ≤ 1 := by
    have e1 : val32 (fun k => wd s.mem (State.addr b) (c + 4 * k)) 8 = W s.mem (State.addr b) c := rfl
    have e2 : val32 (fun k => wd s.mem (State.addr b) (a + 4 * k)) 8 = W s.mem (State.addr b) a := rfl
    omega_arith
  refine wp_mov (op2_imm (by decide)) fun s4 u4 => wp_mul fun s5 u5 =>
    wp_mov (op2_imm (by decide)) fun s6 u6 => ?_
  have e1 : (s6.gpr .r1).toNat = 38 * uc 1 (fun k => wd s.mem (State.addr b) (c + 4 * k))
      (fun k => wd s.mem (State.addr b) (a + 4 * k)) 0 8 := by
    rw [u6.other _ (by decide), u5.gpr, u4.gpr, u4.other _ (by decide),
      toNat_mul_lt (by rw [h3.c]; show _ * 38 < _; omega_using [hc1]), h3.c]
    show _ * 38 = _
    omega_arith
  refine WP.append (uchain_ok (X := xr) (C := .r1) (N := .r3) (M := fun _ => .r3) (T := []) (pre := fun _ => [])
    (nv := 0) (mv := fun _ => 0)
    (xv := uo 1 (fun k => wd s.mem (State.addr b) (c + 4 * k)) (fun k => wd s.mem (State.addr b) (a + 4 * k)) 0)
    (fun j _ => (xr_ne j).2.1.symm) (fun _ _ => List.not_mem_nil) List.not_mem_nil xr_inj e1
    fun k hk t ht => WP.block_nil ⟨?_, ?_, ?_, fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩) fun s7 h7 => ?_
  · rw [ht.keep _ List.not_mem_nil (xr_ne k).2.1.symm fun j hj => xr_inj' hk hj, u6.other _ (xr_ne k).2.2.2.1.symm,
      u5.other _ (xr_ne k).2.1.symm, u4.other _ (xr_ne k).2.2.2.1.symm]
    exact h3.outs k hk
  · rw [ht.keep _ List.not_mem_nil (by decide) fun j _ => (xr_ne j).2.2.2.1, u6.gpr]; rfl
  · rw [ht.keep _ List.not_mem_nil (by decide) fun j _ => (xr_ne j).2.2.2.1, u6.gpr]; rfl
  · have k3 : Kp s2 s3 := h3.kp (by decide) (by decide) fun j _ => (xr_ne j).1
    have k6 : Kp s3 s6 := (Kp.of_upd u4 (by decide)).trans ((Kp.of_upd u5 (by decide)).trans (Kp.of_upd u6 (by decide)))
    have k7 : Kp s6 s7 := h7.kp List.not_mem_nil (by decide) fun j _ => (xr_ne j).1
    have hm7 : s7.mem = s.mem := by rw [h7.mem, u6.mem, u5.mem, u4.mem, h3.mem, hm2]
    refine WP.mono (stores_ok ho (k7.ctx (k6.ctx (k3.ctx (k2.ctx hc))))) fun s8 ⟨hw, hf, hg, hr⟩ =>
      ⟨k2.trans (k3.trans (k6.trans (k7.trans (Kp.of_rest hr List.not_mem_nil)))), by rw [← hm7]; exact hf, ?_⟩
    have hv2 := uc_val8 0 (fun _ => 0)
      (uo 1 (fun k => wd s.mem (State.addr b) (c + 4 * k)) (fun k => wd s.mem (State.addr b) (a + 4 * k)) 0)
      (38 * uc 1 (fun k => wd s.mem (State.addr b) (c + 4 * k)) (fun k => wd s.mem (State.addr b) (a + 4 * k)) 0 8)
    rw [Nat.zero_mul, Nat.zero_add] at hv2
    rw [W_of hw, val32_congr h7.outs]
    exact add_num hla hlc hu1 hv1 hv2

/-! ## The fix-up of a difference -/

theorem val32_not {y : Nat → Nat} : ∀ {n : Nat}, (∀ k < n, y k < 2 ^ 32) →
    val32 (fun k => 2 ^ 32 - 1 - y k) n + val32 y n + 1 = 2 ^ (32 * n)
  | 0, _ => rfl
  | n + 1, h => by
    have ih := val32_not (n := n) fun k hk => h k (Nat.lt_succ_of_lt hk)
    have hn := h n (Nat.lt_succ_self n)
    rw [val32_succ, val32_succ, Nat.mul_succ, Nat.pow_add]
    have e : 2 ^ (32 * n) * (2 ^ 32 - 1 - y n) + 2 ^ (32 * n) * y n + 2 ^ (32 * n) = 2 ^ (32 * n) * 2 ^ 32 := by
      rw [← Nat.mul_add, ← Nat.mul_succ]; congr 1; omega_arith
    omega_arith

theorem val32_mask (K : Nat) (hK : K < 2 ^ 32) :
    val32 (fun k => if k = 0 then 2 ^ 32 - 1 - K else 2 ^ 32 - 1) 8 = 2 ^ 256 - 1 - K := by
  simp only [val32, Nat.reduceMul, Nat.reducePow, ↓reduceIte, Nat.reduceEqDiff, Nat.reduceSub]
  omega_arith

/-- `fixup K`: `2²⁵⁶ - 1 - K` added to `xr` if `r1` is 0, and nothing if it is 1. -/
theorem fixup_ok {K : BitVec 32} (hK : encodable K = true) {s : State} {c1 : Nat}
    (h1 : (s.gpr .r1).toNat = c1) (hc1 : c1 ≤ 1) (h2 : s.gpr .r2 = 1) :
    WP isa (.block (fixup K)) s fun s' =>
      (∃ c2, val32 (fun k => (s'.gpr (xr k)).toNat) 8 + 2 ^ 256 * c2 =
        val32 (fun k => (s.gpr (xr k)).toNat) 8 + (1 - c1) * (2 ^ 256 - 1 - K.toNat)) ∧
      (∀ r, r ∉ [Reg.r1, .r3, .r12] → (∀ j < 8, r ≠ xr j) → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold fixup
  simp only [List.cons_append, List.nil_append]
  refine wp_dp (op2_imm (by decide)) fun s1 u1 => wp_dp (op2_imm hK) fun s2 u2 =>
    wp_mov (op2_imm (by decide)) fun s3 u3 => ?_
  -- The mask, and its lowest word.
  have em : (s3.gpr .r1).toNat = (1 - c1) * (2 ^ 32 - 1) ∧ (s3.gpr .r3).toNat = (1 - c1) * (2 ^ 32 - 1 - K.toNat) := by
    rw [u3.other _ (by decide), u2.other _ (by decide), u3.other _ (by decide), u2.gpr, u1.gpr]
    show ((s.gpr .r1 - 1).toNat = _ ∧ ((s.gpr .r1 - 1) &&& ~~~K).toNat = _)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc1 with rfl | rfl
    · rw [show s.gpr .r1 = 0 from BitVec.eq_of_toNat_eq h1, show (0 : BitVec 32) - 1 = BitVec.allOnes 32 by decide,
        BitVec.allOnes_and, BitVec.toNat_not]
      exact ⟨rfl, by omega_arith⟩
    · rw [show s.gpr .r1 = 1 from BitVec.eq_of_toNat_eq h1, show (1 : BitVec 32) - 1 = 0#32 by decide,
        BitVec.zero_and]
      exact ⟨rfl, (Nat.zero_mul _).symm⟩
  refine WP.mono (uchain_ok (X := xr) (C := .r12) (N := .r2) (M := fun k => if k = 0 then .r3 else .r1) (T := [])
    (pre := fun _ => []) (nv := 1)
    (mv := fun k => if k = 0 then (1 - c1) * (2 ^ 32 - 1 - K.toNat) else (1 - c1) * (2 ^ 32 - 1))
    (xv := fun k => (s.gpr (xr k)).toNat) (cin := 0)
    (fun j _ => (xr_ne j).2.2.2.2.1.symm) (fun _ _ => List.not_mem_nil) List.not_mem_nil xr_inj
    (by rw [u3.gpr]; rfl)
    fun k hk t ht => WP.block_nil ⟨?_, ?_, ?_, fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩) fun s4 h4 =>
      ⟨⟨uc 1 (fun k => if k = 0 then (1 - c1) * (2 ^ 32 - 1 - K.toNat) else (1 - c1) * (2 ^ 32 - 1))
        (fun k => (s.gpr (xr k)).toNat) 0 8, ?_⟩, ?_, ?_⟩
  · rw [ht.keep _ List.not_mem_nil (xr_ne k).2.2.2.2.1.symm fun j hj => xr_inj' hk hj,
      u3.other _ (xr_ne k).2.2.2.2.1.symm, u2.other _ (xr_ne k).2.2.2.1.symm, u1.other _ (xr_ne k).2.1.symm]
  · rw [ht.keep _ List.not_mem_nil (by decide) fun j _ => (xr_ne j).2.2.1, u3.other _ (by decide),
      u2.other _ (by decide), u1.other _ (by decide), h2]; rfl
  · by_cases h : k = 0
    · simp only [h, ite_true]
      rw [ht.keep _ List.not_mem_nil (by decide) fun j _ => (xr_ne j).2.2.2.1, em.2]
    · simp only [h, ite_false]
      rw [ht.keep _ List.not_mem_nil (by decide) fun j _ => (xr_ne j).2.1, em.1]
  · have hv := uc_val8 1 (fun k => if k = 0 then (1 - c1) * (2 ^ 32 - 1 - K.toNat) else (1 - c1) * (2 ^ 32 - 1))
      (fun k => (s.gpr (xr k)).toNat) 0
    have eM : val32 (fun k => if k = 0 then (1 - c1) * (2 ^ 32 - 1 - K.toNat) else (1 - c1) * (2 ^ 32 - 1)) 8 =
        (1 - c1) * (2 ^ 256 - 1 - K.toNat) := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc1 with rfl | rfl
      · simp only [Nat.sub_zero, Nat.one_mul]; exact val32_mask _ K.isLt
      · simp only [Nat.sub_self, Nat.zero_mul, ite_self]; exact val32_zero_fn 8
    rw [eM] at hv
    rw [val32_congr h4.outs, hv]
    omega_arith
  · intro r hr hX
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [h4.keep r List.not_mem_nil hr.2.2 fun j hj => hX j hj, u3.other r hr.2.2, u2.other r hr.2.1, u1.other r hr.1]
  · exact ⟨by rw [h4.mem, u3.mem, u2.mem, u1.mem], by rw [h4.rd, u3.rd, u2.rd, u1.rd],
      by rw [h4.wr, u3.wr, u2.wr, u1.wr], by rw [h4.sp, u3.sp, u2.sp, u1.sp]⟩

/-! ## Subtraction -/

theorem sub_num {wa wc u1 c1 u2 c2 m : Nat} (hc : wc < 2 * P) (hwa : wa < 2 ^ 256)
    (hm : m + wc + 1 = 2 ^ 256)
    (h1 : u1 + 2 ^ 256 * c1 = 1 * m + wa + 1) (hu1 : u1 < 2 ^ 256) (hu2 : u2 < 2 ^ 256)
    (h2 : u2 + 2 ^ 256 * c2 = u1 + (1 - c1) * (2 ^ 256 - 1 - 37)) :
    (u2 + wc) % P = wa % P := by
  have hP : P = 2 ^ 255 - 19 := rfl
  have hc1 : c1 = 0 ∨ c1 = 1 := by omega_arith
  rcases hc1 with rfl | rfl
  · simp only [Nat.sub_zero, Nat.one_mul] at h2
    rw [show u2 + wc = wa + 2 * P by omega_arith, Nat.add_mul_mod_self_right]
  · simp only [Nat.sub_self, Nat.zero_mul, Nat.add_zero] at h2
    rw [show u2 + wc = wa by omega_arith]

/-- `[o] = [a] - [c]`, for a subtrahend below `2p`. -/
theorem sub_ok {o a c : Nat} (ho : o + 32 ≤ 4096) (ha : a + 32 ≤ 4096) (hc' : c + 32 ≤ 4096) {s : State}
    (hc : Ctx b s) (hlc : W s.mem (State.addr b) c < 2 * P) :
    WP isa (.block (sub o a c)) s fun s' =>
      Kp s s' ∧ Frame [⟨State.addr b + BitVec.ofNat 64 o, 32⟩] s.mem s'.mem ∧
      (W s'.mem (State.addr b) o + W s.mem (State.addr b) c) % P = W s.mem (State.addr b) a % P := by
  unfold sub
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => wp_mov (op2_imm (by decide)) fun s2 u2 => ?_
  have k2 : Kp s s2 := (Kp.of_upd u1 (by decide)).trans (Kp.of_upd u2 (by decide))
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  refine WP.append (uchain_ok (X := xr) (C := .r1) (N := .r2) (M := fun _ => .r3) (T := [.r3])
    (pre := fun k => [.ldr (xr k) .r0 (a + 4 * k), .ldr .r3 .r0 (c + 4 * k), .mvn .r3 (.reg .r3)])
    (nv := 1) (mv := fun k => 2 ^ 32 - 1 - wd s.mem (State.addr b) (c + 4 * k))
    (xv := fun k => wd s.mem (State.addr b) (a + 4 * k)) (cin := 1)
    (fun j _ => (xr_ne j).2.1.symm) (fun j _ hm => (xr_ne j).2.2.2.1 (List.mem_singleton.mp hm).symm)
    (by decide) xr_inj (by rw [u2.other _ (by decide), u1.gpr]; rfl) fun k hk t ht => ?_) fun s3 h3 => ?_
  · have kt : Kp s2 t := ht.kp (by decide) (by decide) fun j _ => (xr_ne j).1
    refine WP.append (l := [.ldr (xr k) .r0 (a + 4 * k), .ldr .r3 .r0 (c + 4 * k)])
      (rest := [.mvn .r3 (.reg .r3)])
      (ld2_ok (a := a) (c := c) (by omega_using [ha, hk]) (by omega_using [hc', hk]) (kt.ctx (k2.ctx hc)))
      fun t' ⟨hx, hm, hk'⟩ => wp_mvn (op2_reg _ _) fun t3 v3 => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
    · rw [v3.other _ (xr_ne k).2.2.2.1.symm, hx, ht.mem, hm2]
    · rw [v3.other _ (by decide), hk'.keep _ (by decide) (xr_ne k).2.2.1,
        ht.keep _ (by decide) (by decide) fun j _ => (xr_ne j).2.2.1, u2.gpr]; rfl
    · rw [v3.gpr, BitVec.toNat_not, hm, ht.mem, hm2]
    · exact ⟨fun r hT hX => by
        rw [v3.other r fun e => hT (e ▸ List.mem_singleton_self _), hk'.keep r hT hX],
        by rw [v3.mem, hk'.mem], by rw [v3.rd, hk'.rd], by rw [v3.wr, hk'.wr], by rw [v3.sp, hk'.sp]⟩
  · have hv1 := uc_val8 1 (fun k => 2 ^ 32 - 1 - wd s.mem (State.addr b) (c + 4 * k))
      (fun k => wd s.mem (State.addr b) (a + 4 * k)) 1
    have hn : val32 (fun k => 2 ^ 32 - 1 - wd s.mem (State.addr b) (c + 4 * k)) 8 + W s.mem (State.addr b) c + 1 =
        2 ^ 256 := val32_not (n := 8) fun k _ => wd_lt _ _ _
    have hwa : W s.mem (State.addr b) a < 2 ^ 256 := W_lt _ _ _
    have ea : val32 (fun k => wd s.mem (State.addr b) (a + 4 * k)) 8 = W s.mem (State.addr b) a := rfl
    have hu1 : val32 (uo 1 (fun k => 2 ^ 32 - 1 - wd s.mem (State.addr b) (c + 4 * k))
        (fun k => wd s.mem (State.addr b) (a + 4 * k)) 1) 8 < 2 ^ 256 := val32_lt8 fun k _ => uo_lt _ _ _ _ _
    have hc1 : uc 1 (fun k => 2 ^ 32 - 1 - wd s.mem (State.addr b) (c + 4 * k))
        (fun k => wd s.mem (State.addr b) (a + 4 * k)) 1 8 ≤ 1 := by omega_arith
    have k3 : Kp s2 s3 := h3.kp (by decide) (by decide) fun j _ => (xr_ne j).1
    refine WP.append (fixup_ok (K := 37) (by decide) h3.c hc1 (by
      rw [h3.keep _ (by decide) (by decide) fun j _ => (xr_ne j).2.2.1, u2.gpr]))
      fun s4 ⟨⟨c2, hfix⟩, hkeep, hm4, hrd, hwr, hsp⟩ => ?_
    have k4 : Kp s3 s4 := ⟨hkeep _ (by decide) fun j _ => (xr_ne j).1, hrd, hwr, hsp⟩
    have hm4' : s4.mem = s.mem := by rw [hm4, h3.mem, hm2]
    refine WP.mono (stores_ok ho (k4.ctx (k3.ctx (k2.ctx hc)))) fun s5 ⟨hw, hf, hg, hr⟩ =>
      ⟨k2.trans (k3.trans (k4.trans (Kp.of_rest hr List.not_mem_nil))), by rw [← hm4']; exact hf, ?_⟩
    rw [val32_congr h3.outs, show (37 : BitVec 32).toNat = 37 from rfl] at hfix
    rw [W_of hw]
    exact sub_num hlc hwa hn (by rw [ea] at hv1; exact hv1) hu1 (val32_lt8 fun k _ => (s4.gpr _).isLt) hfix

/-! ## `b + 121665 a` -/

/-- `[o] = [c] + 121665 [a]`: a number below `2p`. -/
theorem addA24_ok {o c a : Nat} (ho : o + 32 ≤ 4096) (hc' : c + 32 ≤ 4096) (ha : a + 32 ≤ 4096) {s : State}
    (hc : Ctx b s) :
    WP isa (.block (addA24 o c a)) s fun s' =>
      Kp s s' ∧ Frame [⟨State.addr b + BitVec.ofNat 64 o, 32⟩] s.mem s'.mem ∧
      W s'.mem (State.addr b) o % P = (W s.mem (State.addr b) c + 121665 * W s.mem (State.addr b) a) % P ∧
      W s'.mem (State.addr b) o < 2 * P := by
  unfold addA24
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_movw fun s1 u1 => wp_movt fun s2 u2 => wp_mov (op2_imm (by decide)) fun s3 u3 => ?_
  have k3 : Kp s s3 := (Kp.of_upd u1 (by decide)).trans ((Kp.of_upd u2 (by decide)).trans (Kp.of_upd u3 (by decide)))
  have hm3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  refine WP.append (ldChain_ok (a := c) (c := a) hc' ha (k3.ctx hc) (nv := 121665) (cin := 0)
    (by rw [u3.gpr]; rfl) (by rw [u3.other _ (by decide), u2.gpr, u1.gpr]; rfl)) fun s4 h4 => ?_
  rw [hm3] at h4
  have hv := uc_val8 121665 (fun k => wd s.mem (State.addr b) (a + 4 * k))
    (fun k => wd s.mem (State.addr b) (c + 4 * k)) 0
  have ea : val32 (fun k => wd s.mem (State.addr b) (a + 4 * k)) 8 = W s.mem (State.addr b) a := rfl
  have ec : val32 (fun k => wd s.mem (State.addr b) (c + 4 * k)) 8 = W s.mem (State.addr b) c := rfl
  rw [ea, ec] at hv
  have hwa : W s.mem (State.addr b) a < 2 ^ 256 := W_lt _ _ _
  have hwc : W s.mem (State.addr b) c < 2 ^ 256 := W_lt _ _ _
  have hc26 : uc 121665 (fun k => wd s.mem (State.addr b) (a + 4 * k))
      (fun k => wd s.mem (State.addr b) (c + 4 * k)) 0 8 < 2 ^ 26 := by omega_arith
  have k4 : Kp s3 s4 := h4.kp (by decide) (by decide) fun j _ => (xr_ne j).1
  refine WP.append (fold19_ok (X := xr) (c := .r1) xr_inj
    (fun j _ => ⟨(xr_ne j).2.2.2.2.1, (xr_ne j).2.2.2.2.2, (xr_ne j).2.1⟩) (by decide) h4.c hc26)
    fun s5 ⟨hval, hlt, hkeep, hm5, hrd, hwr, hsp⟩ => ?_
  have k5 : Kp s4 s5 := ⟨hkeep _ (by decide) (by decide) fun j _ => (xr_ne j).1, hrd, hwr, hsp⟩
  have hm5' : s5.mem = s.mem := by rw [hm5, h4.mem, hm3]
  refine WP.mono (stores_ok ho (k5.ctx (k4.ctx (k3.ctx hc)))) fun s6 ⟨hw, hf, hg, hr⟩ =>
    ⟨k3.trans (k4.trans (k5.trans (Kp.of_rest hr List.not_mem_nil))), by rw [← hm5']; exact hf, ?_, ?_⟩
  · rw [W_of hw, hval, val32_congr h4.outs, hv, Nat.add_zero, Nat.add_comm]
  · rw [W_of hw]; exact hlt

/-! ## The full reduction -/

theorem freeze_num {v y c z c2 : Nat} (hv : v < 2 * P) (hy : y + 2 ^ 256 * c = v + 19)
    (hz : z + 2 ^ 256 * c2 = y + (1 - y / 2 ^ 255) * (2 ^ 256 - 1 - 18)) (hy' : y < 2 ^ 256) (hz' : z < 2 ^ 256) :
    z % 2 ^ 255 = v % P := by
  have hP : P = 2 ^ 255 - 19 := rfl
  have hq : y / 2 ^ 255 = 0 ∨ y / 2 ^ 255 = 1 := by omega_arith
  rcases hq with e | e
  · rw [e] at hz
    simp only [Nat.sub_zero, Nat.one_mul] at hz
    rw [Nat.mod_eq_of_lt (show v < P by omega_arith)]
    omega_arith
  · rw [e] at hz
    simp only [Nat.sub_self, Nat.zero_mul, Nat.add_zero] at hz
    rw [Nat.mod_eq_sub_mod (show v ≥ P by omega_arith), Nat.mod_eq_of_lt (show v - P < P by omega_arith)]
    omega_arith

/-- The number in `xr`, below `2p`, reduced fully. -/
theorem freeze_ok {s : State} (hv : val32 (fun k => (s.gpr (xr k)).toNat) 8 < 2 * P) :
    WP isa (.block freeze) s fun s' =>
      val32 (fun k => (s'.gpr (xr k)).toNat) 8 = val32 (fun k => (s.gpr (xr k)).toNat) 8 % P ∧
      (∀ r, r ∉ [Reg.r1, .r2, .r3, .r12] → (∀ j < 8, r ≠ xr j) → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold freeze
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => wp_mov (op2_imm (by decide)) fun s2 u2 => ?_
  refine WP.append (uchain_ok (X := xr) (C := .r12) (N := .r3) (M := fun _ => .r3) (T := []) (pre := fun _ => [])
    (nv := 0) (mv := fun _ => 0) (xv := fun k => (s.gpr (xr k)).toNat) (cin := 19)
    (fun j _ => (xr_ne j).2.2.2.2.1.symm) (fun _ _ => List.not_mem_nil) List.not_mem_nil xr_inj
    (by rw [u2.other _ (by decide), u1.gpr]; rfl)
    fun k hk t ht => WP.block_nil ⟨?_, ?_, ?_, fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩) fun s3 h3 => ?_
  · rw [ht.keep _ List.not_mem_nil (xr_ne k).2.2.2.2.1.symm fun j hj => xr_inj' hk hj,
      u2.other _ (xr_ne k).2.2.2.1.symm, u1.other _ (xr_ne k).2.2.2.2.1.symm]
  · rw [ht.keep _ List.not_mem_nil (by decide) fun j _ => (xr_ne j).2.2.2.1, u2.gpr]; rfl
  · rw [ht.keep _ List.not_mem_nil (by decide) fun j _ => (xr_ne j).2.2.2.1, u2.gpr]; rfl
  have hy := uc_val8 0 (fun _ => 0) (fun k => (s.gpr (xr k)).toNat) 19
  rw [Nat.zero_mul, Nat.zero_add] at hy
  have hy' : val32 (uo 0 (fun _ => 0) (fun k => (s.gpr (xr k)).toNat) 19) 8 < 2 ^ 256 :=
    val32_lt8 fun k _ => uo_lt _ _ _ _ _
  have hy7 : val32 (uo 0 (fun _ => 0) (fun k => (s.gpr (xr k)).toNat) 19) 7 < 2 ^ 224 :=
    val32_lt fun k _ => uo_lt _ _ _ _ _
  have e8 : val32 (uo 0 (fun _ => 0) (fun k => (s.gpr (xr k)).toNat) 19) 8 =
      val32 (uo 0 (fun _ => 0) (fun k => (s.gpr (xr k)).toNat) 19) 7 +
        2 ^ 224 * uo 0 (fun _ => 0) (fun k => (s.gpr (xr k)).toNat) 19 7 := rfl
  refine wp_mov (op2_lsr (by decide)) fun s4 u4 => wp_mov (op2_imm (by decide)) fun s5 u5 => ?_
  have e1 : (s5.gpr .r1).toNat = val32 (uo 0 (fun _ => 0) (fun k => (s.gpr (xr k)).toNat) 19) 8 / 2 ^ 255 := by
    rw [u5.other _ (by decide), u4.gpr, toNat_shr, h3.outs 7 (by decide)]
    omega_arith
  refine WP.append (fixup_ok (K := 18) (by decide) e1 (by omega_arith) u5.gpr)
    fun s6 ⟨⟨c2, hfix⟩, hkeep, hm6, hrd, hwr, hsp⟩ => ?_
  refine wp_dp (op2_imm (by decide)) fun s7 u7 => WP.block_nil ⟨?_, fun r hr hX => ?_, ?_⟩
  · have hz7 : val32 (fun k => (s6.gpr (xr k)).toNat) 7 < 2 ^ 224 := val32_lt fun k _ => (s6.gpr _).isLt
    have ez : val32 (fun k => (s6.gpr (xr k)).toNat) 8 =
        val32 (fun k => (s6.gpr (xr k)).toNat) 7 + 2 ^ 224 * (s6.gpr (xr 7)).toNat := rfl
    have e7 : val32 (fun k => (s7.gpr (xr k)).toNat) 8 =
        val32 (fun k => (s6.gpr (xr k)).toNat) 7 + 2 ^ 224 * ((s6.gpr (xr 7)).toNat % 2 ^ 31) := by
      rw [val32_succ, val32_congr (g := fun k => (s6.gpr (xr k)).toNat) fun k hk => by
        show (s7.gpr (xr k)).toNat = _
        rw [u7.other _ fun e => absurd (xr_inj k (by omega_arith) 7 (by decide) e) (by omega_arith)]]
      show _ + _ * (s7.gpr (xr 7)).toNat = _
      rw [u7.gpr]
      show _ + _ * (s6.gpr (xr 7) &&& ~~~(0x80000000 : BitVec 32)).toNat = _
      rw [toNat_bic31]
    have hs5 : ∀ k < 8, (s5.gpr (xr k)).toNat = uo 0 (fun _ => 0) (fun k => (s.gpr (xr k)).toNat) 19 k :=
      fun k hk => by rw [u5.other _ (xr_ne k).2.2.1.symm, u4.other _ (xr_ne k).2.1.symm]; exact h3.outs k hk
    rw [val32_congr hs5, show (18 : BitVec 32).toNat = 18 from rfl] at hfix
    have := freeze_num hv hy hfix hy' (val32_lt8 fun k _ => (s6.gpr _).isLt)
    rw [← this, e7]
    omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u7.other r (hX 7 (by decide)), hkeep r (by simp [hr.1, hr.2.2.1, hr.2.2.2]) hX, u5.other r hr.2.1,
      u4.other r hr.1, h3.keep r List.not_mem_nil hr.2.2.2 fun j hj => hX j hj, u2.other r hr.2.2.1,
      u1.other r hr.2.2.2]
  · exact ⟨by rw [u7.mem, hm6, u5.mem, u4.mem, h3.mem, u2.mem, u1.mem],
      by rw [u7.rd, hrd, u5.rd, u4.rd, h3.rd, u2.rd, u1.rd], by rw [u7.wr, hwr, u5.wr, u4.wr, h3.wr, u2.wr, u1.wr],
      by rw [u7.sp, hsp, u5.sp, u4.sp, h3.sp, u2.sp, u1.sp]⟩

end

end VG.Proof.X25519.Arm.Words

end

end

-- separate module: the ladder's and the inversion's loops, which build in parallel with the proofs of
-- the setup and the output and are not checked again when those change.

/-!
# X25519 on 32-bit ARM with `umaal`: the ladder and the inversion

`SlotsW m B qs sm v`: each slot `q` of `qs` holds the element `v q`, as a
number below `2p` if `q` is in `sm` (what `add` and `sub` need of their
operands, and `mul` and `addA24` give). The field operations as updates of
`v` (`op_ok`, `opCswap`), between which the counter and the last bit of the
scalar are in the working space (`Cur`); one iteration of the ladder
(`step_ok`) and the loop (`ladder_ok`); and the inversion (`invert_ok`).
-/

@[expose] public section

namespace VG.Proof.X25519.Arm.Words

open VG VG.Arm VG.Impl.X25519.Arm.Words
open VG.Impl.X25519.Arm (BITS cswapStep storeN)
open VG.Spec.X25519 (P Fe Ladder ladderStep a24)
open VG.Proof.X25519 (toFe toFe_mul toFe_add toFe_sub toFe_addA24 ladderAfter ladderAfter_step ladderStep_eq bit
  bit_le ladderAfter_swap_le)

/-! ## The slots -/

/-- What the ladder and the inversion write of the working space: `CNT`,
`SWAP`, the elements and `ACC`. -/
abbrev FAW (b : BitVec 32) : Region := ⟨State.addr b + BitVec.ofNat 64 44, 532⟩

/-- Each slot `q` of `qs` is an element's, and holds `v q`, as a number below
`2p` if `q` is in `sm`. -/
def SlotsW (m : Mem) (B : Addr) (qs sm : List Nat) (v : Nat → Fe) : Prop :=
  ∀ q ∈ qs, (64 ≤ q ∧ q + 32 ≤ ACC) ∧ toFe (W m B q) = v q ∧ (q ∈ sm → W m B q < 2 * P)

theorem SlotsW.mono {m : Mem} {B : Addr} {qs qs' sm sm' : List Nat} {v : Nat → Fe} (h : SlotsW m B qs sm v)
    (hs : ∀ q ∈ qs', q ∈ qs) (hm : ∀ q ∈ qs', q ∈ sm' → q ∈ sm) : SlotsW m B qs' sm' v := fun q hq =>
  ⟨(h q (hs q hq)).1, (h q (hs q hq)).2.1, fun h' => (h q (hs q hq)).2.2 (hm q hq h')⟩

theorem SlotsW.congr {m : Mem} {B : Addr} {qs sm : List Nat} {v w : Nat → Fe} (h : SlotsW m B qs sm v)
    (hs : ∀ q ∈ qs, v q = w q) : SlotsW m B qs sm w := fun q hq =>
  ⟨(h q hq).1, (h q hq).2.1.trans (hs q hq), (h q hq).2.2⟩

/-- The slots in a frame apart from them. -/
theorem SlotsW.frame {m m' : Mem} {B : Addr} {qs sm : List Nat} {v : Nat → Fe} (h : SlotsW m B qs sm v)
    {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, ∀ q ∈ qs, 64 ≤ q → q + 32 ≤ ACC → ∀ k < 8,
      (⟨B + BitVec.ofNat 64 (q + 4 * k), 4⟩ : Region).Disjoint r) : SlotsW m' B qs sm v := fun q hq => by
  obtain ⟨hb, hv, hs⟩ := h q hq
  have e := W_frame hf (o := q) fun r hr k hk => hd r hr q hq hb.1 hb.2 k hk
  exact ⟨hb, by rw [e]; exact hv, fun h' => by rw [e]; exact hs h'⟩

/-- The slots after a write of `CNT` or `SWAP`. -/
theorem SlotsW.low {m m' : Mem} {B : Addr} {qs sm : List Nat} {v : Nat → Fe} (h : SlotsW m B qs sm v)
    (hf : Frame [⟨B + BitVec.ofNat 64 44, 8⟩] m m') : SlotsW m' B qs sm v :=
  h.frame hf fun r hr q _ h1 h2 k hk => by
    have hA : ACC = 544 := rfl
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inr (by omega_using [h1])) (by omega_using [h2, hA, hk]) (by omega_arith)

theorem cell_frame {B : Addr} (m : Mem) {d : Nat} (hd : 44 ≤ d ∧ d + 4 ≤ 52) (x : BitVec 32) :
    Frame [⟨B + BitVec.ofNat 64 44, 8⟩] m (m.writeW (B + BitVec.ofNat 64 d) x) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (Offset.contains _ (by omega_using [hd]) (by omega_using [hd]) (by omega_arith))

theorem low_FAW {b : BitVec 32} {m m' : Mem} (hf : Frame [⟨State.addr b + BitVec.ofNat 64 44, 8⟩] m m') :
    Frame [FAW b] m m' :=
  hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_arith)⟩

/-- The bits of the scalar stay where the code below them writes. -/
theorem Bits.frame' {b : BitVec 32} {k : Nat} {m m' : Mem} (h : Bits b k m) {e n : Nat}
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 e, n⟩] m m') (he : e + n ≤ BITS) : Bits b k m' := fun t ht => by
  have hB : BITS = 1280 := rfl
  rw [hf _ fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact fun hc => Offset.disjoint (State.addr b) (d := BITS + t) (n := 1) (e := e) (k := n)
      (.inr (by omega_using [he])) (by omega_using [hB, ht]) (by omega_using [he, hB]) _
      (Region.contains_self _ _) hc]
  exact h t ht

theorem Bits.frame {b : BitVec 32} {k : Nat} {m m' : Mem} (h : Bits b k m) (hf : Frame [FAW b] m m') :
    Bits b k m' := Bits.frame' h hf (by decide)

/-- Every slot of `qs` is `o` or apart from it. -/
def SepW (o : Nat) (qs : List Nat) : Bool := qs.all fun q => q == o || q + 32 ≤ o || o + 32 ≤ q

theorem sep_get {o : Nat} {qs : List Nat} (h : SepW o qs = true) {q : Nat} (hq : q ∈ qs) :
    q = o ∨ q + 32 ≤ o ∨ o + 32 ≤ q := by
  have := List.all_eq_true.mp h q hq
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  exact this.elim (fun h => h.elim .inl (fun h => .inr (.inl h))) (fun h => .inr (.inr h))

/-- Between field operations, from `s0`: the counter `c` and the bit `w` in
the working space, and the slots `qs` the elements `v`. -/
structure Cur (b : BitVec 32) (s0 : State) (c w : Nat) (qs sm : List Nat) (v : Nat → Fe) (s : State) :
    Prop where
  ctx : Ctx b s
  kp : Kp s0 s
  frame : Frame [FAW b] s0.mem s.mem
  cnt : wd s.mem (State.addr b) CNT = c
  swp : wd s.mem (State.addr b) SWAP = w
  slots : SlotsW s.mem (State.addr b) qs sm v

section
variable {b : BitVec 32} {s0 : State} {c w : Nat} {qs sm : List Nat} {v : Nat → Fe}

theorem Cur.congr {s : State} {qs' sm' : List Nat} {v' : Nat → Fe} (h : Cur b s0 c w qs sm v s)
    (hq : ∀ q ∈ qs', q ∈ qs) (hm : ∀ q ∈ qs', q ∈ sm' → q ∈ sm) (hv : ∀ q ∈ qs', v q = v' q) :
    Cur b s0 c w qs' sm' v' s :=
  ⟨h.ctx, h.kp, h.frame, h.cnt, h.swp, (h.slots.mono hq hm).congr hv⟩

/-- After an operation that writes the slot `o` (and `ACC`). -/
theorem Cur.next {o : Nat} (hq : SepW o qs = true) (ho : 64 ≤ o ∧ o + 32 ≤ ACC) {s s' : State}
    (h : Cur b s0 c w qs sm v s) (hk : Kp s s')
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 o, 32⟩, ⟨State.addr b + BitVec.ofNat 64 ACC, 32⟩] s.mem s'.mem)
    {x : Fe} (hx : toFe (W s'.mem (State.addr b) o) = x) {sm' : List Nat} (hsm : ∀ q ∈ sm', q ≠ o → q ∈ sm)
    (hsmall : o ∈ sm' → W s'.mem (State.addr b) o < 2 * P) : Cur b s0 c w (o :: qs) sm' (upd v o x) s' := by
  have hA : ACC = 544 := rfl
  have hC : CNT = 44 := rfl
  have hS : SWAP = 48 := rfl
  have hw : ∀ d, d + 4 ≤ 64 → wd s'.mem (State.addr b) d = wd s.mem (State.addr b) d := fun d hd =>
    wd_frame hf fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;>
        exact Offset.disjoint _ (.inl (by omega_using [hd, ho, hA])) (by omega_using [hd]) (by omega_using [ho, hA])
  refine ⟨hk.ctx h.ctx, h.kp.trans hk, h.frame.trans (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩),
    by rw [hw _ (by omega_using [hC])]; exact h.cnt, by rw [hw _ (by omega_using [hS])]; exact h.swp,
    fun q hq' => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.sub _ (by omega_using [ho, hA]) (by omega_using [ho, hA])
  · by_cases hqo : q = o
    · subst hqo; exact ⟨ho, by rw [upd_self]; exact hx, hsmall⟩
    · have hq'' := (List.mem_cons.mp hq').resolve_left hqo
      obtain ⟨hb, hv, hs⟩ := h.slots q hq''
      have hsep := sep_get hq hq''
      have e : W s'.mem (State.addr b) q = W s.mem (State.addr b) q := W_frame hf fun r hr k hk' => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Offset.disjoint _ (by omega_using [hsep, hqo, hk']) (by omega_using [hb, hA, hk'])
            (by omega_using [ho, hA])
        · exact Offset.disjoint _ (.inl (by omega_using [hb, hk'])) (by omega_using [hb, hA, hk'])
            (by omega_using [hA])
      exact ⟨hb, by rw [upd_of_ne _ _ hqo, e]; exact hv, fun h' => by rw [e]; exact hs (hsm q h' hqo)⟩

end

/-! ## Field operations -/

/-- A field operation: `o = x · y`, `x + y`, `x - y` or `x + a24 · y`. -/
inductive FOp
  | mul (o x y : Nat)
  | add (o x y : Nat)
  | sub (o x y : Nat)
  | a24 (o x y : Nat)

def FOp.code : FOp → List Instr
  | .mul o x y => Impl.X25519.Arm.Words.mul o x y
  | .add o x y => Impl.X25519.Arm.Words.add o x y
  | .sub o x y => Impl.X25519.Arm.Words.sub o x y
  | .a24 o x y => addA24 o x y

def FOp.out : FOp → Nat
  | .mul o _ _ | .add o _ _ | .sub o _ _ | .a24 o _ _ => o

def FOp.x : FOp → Nat
  | .mul _ x _ | .add _ x _ | .sub _ x _ | .a24 _ x _ => x

def FOp.y : FOp → Nat
  | .mul _ _ y | .add _ _ y | .sub _ _ y | .a24 _ _ y => y

def FOp.val : FOp → (Nat → Fe) → Fe
  | .mul _ x y, v => v x * v y
  | .add _ x y, v => v x + v y
  | .sub _ x y, v => v x - v y
  | .a24 _ x y, v => v x + Spec.X25519.a24 * v y

/-- The operands that must be below `2p` are. -/
def FOp.needs : FOp → List Nat → Bool
  | .mul .., _ | .a24 .., _ => true
  | .add _ x y, sm => sm.contains x && sm.contains y
  | .sub _ _ y, sm => sm.contains y

/-- The slots below `2p` after the operation. -/
def FOp.sm : FOp → List Nat → List Nat
  | .mul o _ _, sm | .a24 o _ _, sm => o :: sm
  | .add o _ _, sm | .sub o _ _, sm => sm.filter (· != o)

section
variable {b : BitVec 32} {s0 : State} {c w : Nat} {qs sm : List Nat} {v : Nat → Fe}

theorem not_mem_filter_ne {o : Nat} {l : List Nat} (h : o ∈ l.filter (· != o)) : False := by
  have := (List.mem_filter.mp h).2
  simp at this

theorem op_ok (op : FOp) (hq : SepW op.out qs = true) (ho : 64 ≤ op.out ∧ op.out + 32 ≤ ACC) (hx : op.x ∈ qs)
    (hy : op.y ∈ qs) (hn : op.needs sm = true) {s : State} (h : Cur b s0 c w qs sm v s) :
    WP isa (.block op.code) s (Cur b s0 c w (op.out :: qs) (op.sm sm) (upd v op.out (op.val v))) := by
  have hA : ACC = 544 := rfl
  cases op with
  | mul o x y =>
    have hq : SepW o qs = true := hq
    have hx : x ∈ qs := hx
    have hy : y ∈ qs := hy
    obtain ⟨hbx, hvx, hsx⟩ := h.slots _ hx
    obtain ⟨hby, hvy, hsy⟩ := h.slots _ hy
    have ho' : 64 ≤ o ∧ o + 32 ≤ ACC := ho
    show WP isa (.block (Impl.X25519.Arm.Words.mul o x y)) s (Cur b s0 c w (o :: qs) (o :: sm) (upd v o (v x * v y)))
    exact WP.mono (mul_ok (o := o) (by omega_using [ho', hA]) hbx.2 hby.2 h.ctx) fun s' ⟨hk, hf, hv, hl⟩ =>
      h.next hq ho' hk hf (by rw [← hvx, ← hvy]; exact toFe_mul hv)
        (fun q hq' hne => (List.mem_cons.mp hq').resolve_left hne) (fun _ => hl)
  | add o x y =>
    have hq : SepW o qs = true := hq
    have hx : x ∈ qs := hx
    have hy : y ∈ qs := hy
    obtain ⟨hbx, hvx, hsx⟩ := h.slots _ hx
    obtain ⟨hby, hvy, hsy⟩ := h.slots _ hy
    have ho' : 64 ≤ o ∧ o + 32 ≤ ACC := ho
    have hn' : (sm.contains x && sm.contains y) = true := hn
    simp only [Bool.and_eq_true, List.contains_iff_mem] at hn'
    show WP isa (.block (Impl.X25519.Arm.Words.add o x y)) s
      (Cur b s0 c w (o :: qs) (sm.filter (· != o)) (upd v o (v x + v y)))
    exact WP.mono (add_ok (o := o) (by omega_using [ho', hA]) (by omega_using [hbx, hA]) (by omega_using [hby, hA])
      h.ctx (hsx hn'.1) (hsy hn'.2)) fun s' ⟨hk, hf, hv⟩ =>
      h.next hq ho' hk (hf.mono fun r hr => by simp [List.mem_singleton.mp hr])
        (by rw [← hvx, ← hvy]; exact toFe_add hv) (fun q hq' _ => (List.mem_filter.mp hq').1)
        (fun h' => (not_mem_filter_ne h').elim)
  | sub o x y =>
    have hq : SepW o qs = true := hq
    have hx : x ∈ qs := hx
    have hy : y ∈ qs := hy
    obtain ⟨hbx, hvx, hsx⟩ := h.slots _ hx
    obtain ⟨hby, hvy, hsy⟩ := h.slots _ hy
    have ho' : 64 ≤ o ∧ o + 32 ≤ ACC := ho
    have hn' : sm.contains y = true := hn
    simp only [List.contains_iff_mem] at hn'
    show WP isa (.block (Impl.X25519.Arm.Words.sub o x y)) s
      (Cur b s0 c w (o :: qs) (sm.filter (· != o)) (upd v o (v x - v y)))
    exact WP.mono (sub_ok (o := o) (by omega_using [ho', hA]) (by omega_using [hbx, hA]) (by omega_using [hby, hA])
      h.ctx (hsy hn')) fun s' ⟨hk, hf, hv⟩ =>
      h.next hq ho' hk (hf.mono fun r hr => by simp [List.mem_singleton.mp hr])
        (by rw [← hvx, ← hvy]; exact toFe_sub hv) (fun q hq' _ => (List.mem_filter.mp hq').1)
        (fun h' => (not_mem_filter_ne h').elim)
  | a24 o x y =>
    have hq : SepW o qs = true := hq
    have hx : x ∈ qs := hx
    have hy : y ∈ qs := hy
    obtain ⟨hbx, hvx, hsx⟩ := h.slots _ hx
    obtain ⟨hby, hvy, hsy⟩ := h.slots _ hy
    have ho' : 64 ≤ o ∧ o + 32 ≤ ACC := ho
    show WP isa (.block (addA24 o x y)) s (Cur b s0 c w (o :: qs) (o :: sm) (upd v o (v x + Spec.X25519.a24 * v y)))
    exact WP.mono (addA24_ok (o := o) (by omega_using [ho', hA]) (by omega_using [hbx, hA])
      (by omega_using [hby, hA]) h.ctx) fun s' ⟨hk, hf, hv, hl⟩ =>
      h.next hq ho' hk (hf.mono fun r hr => by simp [List.mem_singleton.mp hr])
        (by rw [← hvx, ← hvy]; exact toFe_addA24 hv) (fun q hq' hne => (List.mem_cons.mp hq').resolve_left hne)
        (fun _ => hl)

/-! ## Sequences of field operations -/

/-- The operations `ops`, then `k`. -/
def opsCode : List FOp → Prog isa → Prog isa
  | [], k => k
  | op :: ops, k => .seq (.block op.code) (opsCode ops k)

/-- Each operation's slots are separate or equal, the elements' own, and its
inputs known, and below `2p` where it needs that. -/
def opsOk : List FOp → List Nat → List Nat → Bool
  | [], _, _ => true
  | op :: ops, qs, sm => SepW op.out qs && 64 ≤ op.out && op.out + 32 ≤ ACC && qs.contains op.x &&
      qs.contains op.y && op.needs sm && opsOk ops (op.out :: qs) (op.sm sm)

/-- The elements after the operations. -/
def runOps : List FOp → (Nat → Fe) → Nat → Fe
  | [], v => v
  | op :: ops, v => runOps ops (upd v op.out (op.val v))

/-- The slots known after the operations. -/
def outsQ : List FOp → List Nat → List Nat
  | [], qs => qs
  | op :: ops, qs => outsQ ops (op.out :: qs)

/-- The slots below `2p` after the operations. -/
def outsS : List FOp → List Nat → List Nat
  | [], sm => sm
  | op :: ops, sm => outsS ops (op.sm sm)

theorem ops_ok {k : Prog isa} {Q : State → Prop} :
    ∀ (ops : List FOp) (qs sm : List Nat) (v : Nat → Fe) (s : State), opsOk ops qs sm = true →
      Cur b s0 c w qs sm v s →
      (∀ s', Cur b s0 c w (outsQ ops qs) (outsS ops sm) (runOps ops v) s' → WP isa k s' Q) →
      WP isa (opsCode ops k) s Q
  | [], _, _, _, s, _, h, hk => hk s h
  | op :: ops, qs, sm, v, s, hok, h, hk => by
    simp only [opsOk, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hok
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hok
    exact WP.seq (WP.mono (op_ok op h1 ⟨h2, h3⟩ h4 h5 h6 h) fun s' h' => ops_ok ops _ _ _ s' h7 h' hk)

/-! ## The conditional swap -/

theorem sel_lt {sw x y n : Nat} (hx : x < n) (hy : y < n) : sel sw x y < n := by
  unfold sel; split <;> with_reducible assumption

theorem toFe_sel (sw x y : Nat) : toFe (sel sw x y) = sel sw (toFe x) (toFe y) := by
  unfold sel; split <;> rfl

theorem opCswap {x y : Nat} (hqx : SepW x qs = true) (hqy : SepW y qs = true) (hx : x ∈ qs) (hy : y ∈ qs)
    (hxy : x + 32 ≤ y ∨ y + 32 ≤ x) (hsx : x ∈ sm) (hsy : y ∈ sm) {s : State} (h : Cur b s0 c w qs sm v s)
    {sw : Nat} (hsw : sw ≤ 1) (h9 : s.gpr .r9 = 0 - BitVec.ofNat 32 sw) :
    WP isa (.block (cswap x y)) s fun s' =>
      Cur b s0 c w qs sm (swapV x y sw v) s' ∧ s'.gpr .r9 = s.gpr .r9 := by
  have hA : ACC = 544 := rfl
  have hC : CNT = 44 := rfl
  have hS : SWAP = 48 := rfl
  obtain ⟨hbx, hvx, hlx⟩ := h.slots _ hx
  obtain ⟨hby, hvy, hly⟩ := h.slots _ hy
  refine WP.mono (cswapN_ok (n := 8) (b := b) (by omega_using [hbx, hA]) (by omega_using [hby, hA]) hxy h.ctx
    hsw h9) fun s' hs => ?_
  have hf : Frame [⟨State.addr b + BitVec.ofNat 64 x, 32⟩, ⟨State.addr b + BitVec.ofNat 64 y, 32⟩] s.mem s'.mem :=
    hs.frame
  have ex : W s'.mem (State.addr b) x = sel sw (W s.mem (State.addr b) x) (W s.mem (State.addr b) y) := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
    · exact val32_congr fun k hk => (hs.lx k hk).trans rfl
    · exact val32_congr fun k hk => (hs.lx k hk).trans rfl
  have ey : W s'.mem (State.addr b) y = sel sw (W s.mem (State.addr b) y) (W s.mem (State.addr b) x) := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
    · exact val32_congr fun k hk => (hs.ly k hk).trans rfl
    · exact val32_congr fun k hk => (hs.ly k hk).trans rfl
  have hw : ∀ d, d + 4 ≤ 64 → wd s'.mem (State.addr b) d = wd s.mem (State.addr b) d := fun d hd =>
    wd_frame hf fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (.inl (by omega_using [hd, hbx])) (by omega_using [hd]) (by omega_using [hbx, hA])
      · exact Offset.disjoint _ (.inl (by omega_using [hd, hby])) (by omega_using [hd]) (by omega_using [hby, hA])
  have hk : Kp s s' := Kp.of_rest hs.rest (by decide)
  refine ⟨⟨hk.ctx h.ctx, h.kp.trans hk, h.frame.trans (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩),
    by rw [hw _ (by omega_using [hC])]; exact h.cnt, by rw [hw _ (by omega_using [hS])]; exact h.swp,
    fun q hq => ?_⟩, hs.rest.gpr _ (by decide)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.sub _ (by omega_using [hbx]) (by omega_using [hbx, hA])
    · exact Offset.sub _ (by omega_using [hby]) (by omega_using [hby, hA])
  · by_cases hnx : q = x
    · subst hnx
      refine ⟨hbx, ?_, fun _ => by rw [ex]; exact sel_lt (hlx hsx) (hly hsy)⟩
      simp only [swapV, ite_true]
      rw [ex, toFe_sel, hvx, hvy]
    by_cases hny : q = y
    · subst hny
      refine ⟨hby, ?_, fun _ => by rw [ey]; exact sel_lt (hly hsy) (hlx hsx)⟩
      simp only [swapV, hnx, ite_false, ite_true]
      rw [ey, toFe_sel, hvx, hvy]
    · obtain ⟨hb, hv, hl⟩ := h.slots q hq
      have h1 := sep_get hqx hq
      have h2 := sep_get hqy hq
      have e : W s'.mem (State.addr b) q = W s.mem (State.addr b) q := W_frame hf fun r hr k hk' => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Offset.disjoint _ (by omega_using [h1, hnx, hk']) (by omega_using [hb, hA, hk'])
            (by omega_using [hbx, hA])
        · exact Offset.disjoint _ (by omega_using [h2, hny, hk']) (by omega_using [hb, hA, hk'])
            (by omega_using [hby, hA])
      refine ⟨hb, ?_, fun h' => by rw [e]; exact hl h'⟩
      simp only [swapV, hnx, hny, ite_false]
      rw [e]; exact hv

end

/-! ## One iteration of the ladder -/

/-- The field operations of an iteration, after the swaps. -/
def ladOps : List FOp :=
  [.add A X2 Z2, .mul AA A A, .sub B X2 Z2, .mul BB B B, .sub E AA BB, .add C X3 Z3, .sub D X3 Z3,
    .mul DA D A, .mul CB C B, .add X3 DA CB, .mul X3 X3 X3, .sub Z3 DA CB, .mul Z3 Z3 Z3,
    .mul Z3 X1 Z3, .mul X2 AA BB, .a24 Z2 AA E, .mul Z2 E Z2]

/-- The slots the ladder's state lives in, each below `2p`. -/
def LQ : List Nat := [X1, X2, Z2, X3, Z3]

theorem ladOps_ok : opsOk ladOps LQ LQ = true := by decide

theorem ladOps_q : ∀ q ∈ LQ, q ∈ outsQ ladOps LQ := by decide

theorem ladOps_s : ∀ q ∈ LQ, q ∈ outsS ladOps LQ := by decide

/-- The elements of the ladder's state `st`, and `x1`. -/
def ladV (x1 : Fe) (st : Ladder) (q : Nat) : Fe :=
  if q = X1 then x1 else if q = X2 then st.x2 else if q = Z2 then st.z2 else if q = X3 then st.x3 else st.z3

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

theorem cmp_z {x y : BitVec 32} {m : Nat} (h : x.toNat = m) : (x - y == 0) = decide (m = y.toNat) := by
  subst h
  by_cases e : x = y
  · subst e; simp
  · have hne : x.toNat ≠ y.toNat := fun h' => e (BitVec.eq_of_toNat_eq h')
    simp only [hne, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    apply e
    rw [← BitVec.sub_add_cancel x y, h']
    exact BitVec.zero_add y

/-- The loop invariant of the ladder from `sL`, before the iteration for the
bit `n - 1`. -/
structure LadInv (b : BitVec 32) (k : Nat) (x1 : Fe) (sL : State) (n : Nat) (s : State) : Prop where
  cur : Cur b sL n (ladderAfter k x1 n).swap LQ LQ (ladV x1 (ladderAfter k x1 n)) s

section
variable {b : BitVec 32}

/-- The counter decremented in `CNT`, and in `r1`. -/
theorem dec_ok {s0 : State} {n w : Nat} {qs sm : List Nat} {v : Nat → Fe} {s : State}
    (h : Cur b s0 n w qs sm v s) (hn : 1 ≤ n) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Cur b s0 (n - 1) w qs sm v s' → s'.gpr .r1 = BitVec.ofNat 32 (n - 1) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldr .r1 .r0 CNT :: .dp .sub .r1 .r1 (.imm 1) :: .str .r1 .r0 CNT :: is)) s Q := by
  have hC : CNT = 44 := rfl
  have hS : SWAP = 48 := rfl
  refine ldr0_ok h.ctx (d := CNT) (by decide) fun s1 u1 => wp_dp (op2_imm (by decide)) fun s2 u2 => ?_
  have hlt : n < 2 ^ 32 := by rw [← h.cnt]; exact wd_lt _ _ _
  have e2 : s2.gpr .r1 = BitVec.ofNat 32 (n - 1) := by
    rw [u2.gpr]
    show s1.gpr .r1 - 1 = _
    rw [u1.gpr]
    have e : (s.mem.readW (State.addr b + BitVec.ofNat 64 CNT) 32).toNat = n := h.cnt
    apply BitVec.eq_of_toNat_eq
    rw [toNat_sub_le (by rw [e]; exact hn), e, toNat_imm (by omega_using [hlt])]; rfl
  have k2 : Kp s s2 := (Kp.of_upd u1 (by decide)).trans (Kp.of_upd u2 (by decide))
  refine str0_ok (k2.ctx h.ctx) (d := CNT) (by decide) fun s3 u3 => ?_
  have hm3 : s3.mem = s.mem.writeW (State.addr b + BitVec.ofNat 64 CNT) (BitVec.ofNat 32 (n - 1)) := by
    rw [u3.mem, e2, u2.mem, u1.mem]
  have hf3 : Frame [⟨State.addr b + BitVec.ofNat 64 44, 8⟩] s.mem s3.mem := by
    rw [hm3]; exact cell_frame _ (by omega_using [hC]) _
  have k3 : Kp s s3 := k2.trans (Kp.of_mupd u3)
  refine k s3 ⟨k3.ctx h.ctx, h.kp.trans k3, h.frame.trans (low_FAW hf3), ?_, ?_, h.slots.low hf3⟩
    (by rw [u3.gpr, e2])
  · rw [hm3, wd_write_self, toNat_imm (by omega_using [hlt])]
  · rw [hm3, wd_write_other _ _ _ (by omega_using [hC, hS]) (by omega_using [hS]) (by omega_using [hC])]
    exact h.swp

/-- The counter from `CNT`, compared with `c`. -/
theorem cnt_cmp_ok {s0 : State} {n w : Nat} {qs sm : List Nat} {v : Nat → Fe} {s : State}
    (h : Cur b s0 n w qs sm v s) {c : BitVec 32} (hc : encodable c = true) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Cur b s0 n w qs sm v s' → (s'.gpr .r1).toNat = n → s'.z = decide (n = c.toNat) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.ldr .r1 .r0 CNT :: .cmp .r1 (.imm c) :: is)) s Q := by
  refine ldr0_ok h.ctx (d := CNT) (by decide) fun s1 u1 => wp_cmp (op2_imm hc) fun s2 u2 hz => ?_
  have e1 : (s1.gpr .r1).toNat = n := by rw [u1.gpr]; exact h.cnt
  have k2 : Kp s s2 := (Kp.of_upd u1 (by decide)).trans ⟨by rw [u2.gpr], u2.rd, u2.wr, u2.sp⟩
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  exact k s2 ⟨k2.ctx h.ctx, h.kp.trans k2, by rw [hm2]; exact h.frame, by rw [hm2]; exact h.cnt,
    by rw [hm2]; exact h.swp, by rw [hm2]; exact h.slots⟩ (by rw [u2.gpr, e1]) (by rw [hz]; exact cmp_z e1)

theorem head_ok {k : Nat} {x1 : Fe} {sL : State} (hbits : Bits b k sL.mem)
    {n : Nat} (hn : 1 ≤ n) (hn' : n ≤ 255) {s : State} (h : LadInv b k x1 sL n s) :
    WP isa (.block stepHead) s (Cur b sL (n - 1) (bit k (n - 1)) LQ LQ
      (swapV Z2 Z3 ((ladderAfter k x1 n).swap ^^^ bit k (n - 1))
        (swapV X2 X3 ((ladderAfter k x1 n).swap ^^^ bit k (n - 1)) (ladV x1 (ladderAfter k x1 n))))) := by
  obtain ⟨hcur⟩ := h
  have hB : BITS = 1280 := rfl
  have hC : CNT = 44 := rfl
  have hS : SWAP = 48 := rfl
  have hsw := ladderAfter_swap_le k x1 hn'
  have hbt := bit_le k (n - 1)
  have hx := xor_le_one hsw hbt
  unfold stepHead
  simp only [List.cons_append, List.nil_append]
  refine dec_ok hcur hn fun s3 h3 e3 => ?_
  have hc3 := h3.ctx
  have hfit := hc3.fit
  refine wp_dp (op2_reg _ _) fun s4 u4 => ?_
  refine wp_ldrb (a := State.addr b + BitVec.ofNat 64 (n - 1 + BITS)) (by decide)
    (by rw [u4.gpr]; show State.addr (s3.gpr .r0 + s3.gpr .r1 + _) = _
        rw [e3, hc3.r0, ea2 hfit (by omega_using [hn', hB])])
    (by rw [u4.rd, u4.wr]; exact hc3.inR (by omega_using [hn', hB])) fun s5 u5 => ?_
  have e5 : s5.gpr .r2 = BitVec.ofNat 32 (bit k (n - 1)) := by
    rw [u5.gpr, u4.mem, Nat.add_comm (n - 1) BITS, Bits.frame hbits h3.frame (n - 1) (by omega_using [hn, hn'])]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, toNat_imm (by omega_using [hbt])]; omega_using [hbt]
  have k5 : Kp s3 s5 := (Kp.of_upd u4 (by decide)).trans (Kp.of_upd u5 (by decide))
  have hm5 : s5.mem = s3.mem := by rw [u5.mem, u4.mem]
  refine ldr0_ok (k5.ctx hc3) (d := SWAP) (by decide) fun s6 u6 => ?_
  have e6 : s6.gpr .r3 = BitVec.ofNat 32 (ladderAfter k x1 n).swap := by
    rw [u6.gpr, hm5]
    apply BitVec.eq_of_toNat_eq
    rw [toNat_imm (by omega_using [hsw])]; exact h3.swp
  have k6 : Kp s3 s6 := k5.trans (Kp.of_upd u6 (by decide))
  refine str0_ok (k6.ctx hc3) (d := SWAP) (by decide) fun s7 u7 => ?_
  refine wp_dp (op2_reg _ _) fun s8 u8 => wp_mov (op2_imm (by decide)) fun s9 u9 =>
    wp_dp (op2_reg _ _) fun s10 u10 => ?_
  have e9 : s10.gpr .r9 = 0 - BitVec.ofNat 32 ((ladderAfter k x1 n).swap ^^^ bit k (n - 1)) := by
    rw [u10.gpr]
    show s9.gpr .r9 - s9.gpr .r2 = _
    rw [u9.gpr, u9.other _ (by decide), u8.gpr]
    show _ - (s7.gpr .r2 ^^^ s7.gpr .r3) = _
    rw [u7.gpr, e6, u6.other _ (by decide), e5, BitVec.xor_comm,
      ofNat_xor (by omega_using [hsw]) (by omega_using [hbt])]
  have hm10 : s10.mem = s3.mem.writeW (State.addr b + BitVec.ofNat 64 SWAP) (BitVec.ofNat 32 (bit k (n - 1))) := by
    rw [u10.mem, u9.mem, u8.mem, u7.mem, u6.other _ (by decide), e5, u6.mem, hm5]
  have hf10 : Frame [⟨State.addr b + BitVec.ofNat 64 44, 8⟩] s3.mem s10.mem := by
    rw [hm10]; exact cell_frame _ (by omega_using [hS]) _
  have k10 : Kp s3 s10 := k6.trans ((Kp.of_mupd u7).trans ((Kp.of_upd u8 (by decide)).trans
    ((Kp.of_upd u9 (by decide)).trans (Kp.of_upd u10 (by decide)))))
  have h10 : Cur b sL (n - 1) (bit k (n - 1)) LQ LQ (ladV x1 (ladderAfter k x1 n)) s10 := by
    refine ⟨k10.ctx hc3, h3.kp.trans k10, h3.frame.trans (low_FAW hf10), ?_, ?_, h3.slots.low hf10⟩
    · rw [hm10, wd_write_other _ _ _ (by omega_using [hC, hS]) (by omega_using [hC]) (by omega_using [hS])]
      exact h3.cnt
    · rw [hm10, wd_write_self, toNat_imm (by omega_using [hbt])]
  refine WP.append (opCswap (x := X2) (y := X3) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) h10 hx e9) fun s11 ⟨h11, h9'⟩ => ?_
  exact WP.mono (opCswap (x := Z2) (y := Z3) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) h11 hx (by rw [h9', e9])) fun s12 h12 => h12.1

theorem step_eq :
    step = .seq (.block stepHead) (opsCode ladOps (.block [.ldr .r1 .r0 CNT, .cmp .r1 (.imm 0)])) := rfl

theorem step_ok {k : Nat} {x1 : Fe} {sL : State} (hbits : Bits b k sL.mem)
    {n : Nat} (hn : 1 ≤ n) (hn' : n ≤ 255) {s : State} (h : LadInv b k x1 sL n s) :
    WP isa step s fun s' => LadInv b k x1 sL (n - 1) s' ∧ s'.z = decide (n - 1 = 0) := by
  rw [step_eq]
  refine WP.seq (WP.mono (head_ok hbits hn hn' h) fun s1 h1 =>
    ops_ok ladOps LQ LQ _ s1 ladOps_ok h1 fun s2 h2 => ?_)
  refine cnt_cmp_ok h2 (by decide) fun s3 h3 _ hz => WP.block_nil ⟨⟨?_⟩, hz⟩
  have e : ladderAfter k x1 (n - 1) = ladderStep k x1 (ladderAfter k x1 n) (n - 1) := by
    rw [ladderAfter_step k x1 (show n - 1 < 255 by omega_using [hn']), Nat.sub_add_cancel hn]
  refine ⟨h3.ctx, h3.kp, h3.frame, h3.cnt, ?_, ?_⟩
  · rw [h3.swp, e, ladderStep_eq]
  · refine (h3.slots.mono ladOps_q fun q hq _ => ladOps_s q hq).congr fun q hq => ?_
    rw [e]; exact ladOps_vals k x1 _ (n - 1) q hq

/-- The ladder, from the state with the bits of the scalar in `BITS` and the
initial elements in `LQ`. -/
theorem ladder_ok {k : Nat} {x1 : Fe} {s : State} (hc : Ctx b s) (hbits : Bits b k s.mem)
    (hS : SlotsW s.mem (State.addr b) LQ LQ (ladV x1 (VG.Proof.X25519.init x1))) :
    WP isa ladder s fun s' => Kp s s' ∧ Frame [FAW b] s.mem s'.mem ∧ Ctx b s' ∧
      wd s'.mem (State.addr b) SWAP = (ladderAfter k x1 0).swap ∧
      SlotsW s'.mem (State.addr b) LQ LQ (ladV x1 (ladderAfter k x1 0)) := by
  have hC : CNT = 44 := rfl
  have hSW : SWAP = 48 := rfl
  unfold ladder
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s1 u1 => ?_)
  refine str0_ok ((Kp.of_upd u1 (by decide)).ctx hc) (d := CNT) (by decide) fun s2 u2 =>
    wp_mov (op2_imm (by decide)) fun s3 u3 => ?_
  have k3 : Kp s s3 := (Kp.of_upd u1 (by decide)).trans ((Kp.of_mupd u2).trans (Kp.of_upd u3 (by decide)))
  refine str0_ok (k3.ctx hc) (d := SWAP) (by decide) fun s4 u4 => WP.block_nil ?_
  have k4 : Kp s s4 := k3.trans (Kp.of_mupd u4)
  have hm4 : s4.mem = (s.mem.writeW (State.addr b + BitVec.ofNat 64 CNT) (255 : BitVec 32)).writeW
      (State.addr b + BitVec.ofNat 64 SWAP) (0 : BitVec 32) := by
    rw [u4.mem, u3.gpr, u3.mem, u2.mem, u1.gpr, u1.mem]
  have hf4 : Frame [⟨State.addr b + BitVec.ofNat 64 44, 8⟩] s.mem s4.mem := by
    rw [hm4]
    exact (cell_frame _ (by omega_using [hC]) _).trans (cell_frame _ (by omega_using [hSW]) _)
  have hbits4 : Bits b k s4.mem := Bits.frame hbits (low_FAW hf4)
  have h255 : LadInv b k x1 s4 255 s4 := ⟨⟨k4.ctx hc, Kp.refl _, Frame.refl _ _, by
    rw [hm4, wd_write_other _ _ _ (by omega_using [hC, hSW]) (by omega_using [hC]) (by omega_using [hSW]),
      wd_write_self]; rfl, by rw [hm4, wd_write_self]; rfl, hS.low hf4⟩⟩
  refine WP.mono (Q := LadInv b k x1 s4 0) (WP.loop (M := isa)
    (fun m s' => 1 ≤ m ∧ m ≤ 255 ∧ LadInv b k x1 s4 m s') ?_ 255 s4 ⟨by decide, Nat.le_refl _, h255⟩)
    fun s' ⟨h'⟩ => ⟨k4.trans h'.kp, (low_FAW hf4).trans h'.frame, h'.ctx, h'.swp, h'.slots⟩
  rintro m s' ⟨h1, h2, hl⟩
  refine WP.mono (step_ok hbits4 h1 h2 hl) fun s'' ⟨hl', hz⟩ => ?_
  by_cases hm : m - 1 = 0
  · exact .inl ⟨by rw [eval_ne, hz]; simp [hm], by rw [hm] at hl'; exact hl'⟩
  · exact .inr ⟨by rw [eval_ne, hz]; simp [hm], m - 1, by omega_arith, by omega_arith, by omega_arith, hl'⟩

/-! ## The inversion -/

/-- The slots of the inversion. -/
def IQ : List Nat := [Z2, R, X2]

/-- `z^((p - 2) >> n)` in `R`, for `z` at `Z2`. -/
def invV (v : Nat → Fe) (n : Nat) : Nat → Fe := upd v R (VG.Proof.X25519.pw (v Z2) ((P - 2) >>> n))

/-- The loop invariant of the inversion from `sI`, before the step for the bit
`n - 1`. -/
structure InvInv (b : BitVec 32) (sI : State) (w : Nat) (v : Nat → Fe) (n : Nat) (s : State) : Prop where
  cur : Cur b sI n w IQ [] (invV v n) s

theorem Cur.of_fupd {s0 : State} {c w : Nat} {qs sm : List Nat} {v : Nat → Fe} {s s' : State}
    (h : Cur b s0 c w qs sm v s) (u : Fupd s s') : Cur b s0 c w qs sm v s' :=
  have k : Kp s s' := ⟨by rw [u.gpr], u.rd, u.wr, u.sp⟩
  ⟨k.ctx h.ctx, h.kp.trans k, by rw [u.mem]; exact h.frame, by rw [u.mem]; exact h.cnt,
    by rw [u.mem]; exact h.swp, by rw [u.mem]; exact h.slots⟩

theorem invStep_ok {sI : State} {w : Nat} {v : Nat → Fe} {n : Nat} (hn : 1 ≤ n) (hn' : n ≤ 255)
    {s : State} (h : InvInv b sI w v n s) :
    WP isa invStep s fun s' => InvInv b sI w v (n - 1) s' ∧ s'.z = decide (n - 1 = 0) := by
  obtain ⟨hcur⟩ := h
  have hb := pbits (n - 1) (by omega_using [hn'])
  have he := shr_step (P - 2) (n - 1)
  rw [Nat.sub_add_cancel hn] at he
  unfold invStep
  refine WP.seq (dec_ok hcur hn fun s1 h1 _ => WP.block_nil ?_)
  refine WP.seq (WP.mono (op_ok (.mul R R R) (by decide) (by decide) (by decide) (by decide) rfl h1)
    fun s2 h2 => ?_)
  have h2 : Cur b sI (n - 1) w (R :: IQ) [R] (upd (invV v n) R (invV v n R * invV v n R)) s2 := h2
  -- After the square.
  have hsq : ∀ q ∈ IQ, upd (invV v n) R (invV v n R * invV v n R) q =
      upd v R (VG.Proof.X25519.pw (v Z2) (2 * ((P - 2) >>> n))) q := by
    intro q _
    by_cases hq : q = R
    · subst hq; rw [upd_self, invV, upd_self, upd_self, Nat.two_mul, ← VG.Proof.X25519.pw_mul]
    · rw [upd_of_ne _ _ hq, invV, upd_of_ne _ _ hq, upd_of_ne _ _ hq]
  have h2' := h2.congr (qs' := IQ) (sm' := []) (by decide) (fun _ _ h => absurd h List.not_mem_nil) hsq
  refine WP.seq (cnt_cmp_ok h2' (c := 4) (by decide) fun s3 h3 e3 hz3 => WP.block_nil ?_)
  have hz3' : s3.z = decide (n - 1 = 4) := hz3
  refine WP.seq (WP.mono (Q := Cur b sI (n - 1) w IQ [] (invV v (n - 1))) ?_ fun s4 h4 =>
    cnt_cmp_ok h4 (c := 0) (by decide) fun s5 h5 _ hz5 => WP.block_nil ⟨⟨h5⟩, hz5⟩)
  refine WP.ite s3.z (eval_eq _) (fun ht => WP.block_nil (h3.congr (fun q hq => hq) (fun _ _ h => h) fun q _ => ?_))
    (fun hf => ?_)
  · have h4 : n - 1 = 4 := by rw [hz3'] at ht; simpa using ht
    by_cases hq : q = R
    · subst hq; rw [upd_self, invV, upd_self, he, hb, iteT (.inl h4), Nat.add_zero]
    · rw [upd_of_ne _ _ hq, invV, upd_of_ne _ _ hq]
  · have h4 : n - 1 ≠ 4 := by rw [hz3'] at hf; simpa using hf
    refine WP.seq (wp_cmp (op2_imm (by decide)) fun s4 u4 hz4 => WP.block_nil ?_)
    have h4' := h3.of_fupd u4
    have hz4' : s4.z = decide (n - 1 = 2) := by rw [hz4]; exact cmp_z e3
    refine WP.ite s4.z (eval_eq _) (fun ht => WP.block_nil (h4'.congr (fun q hq => hq) (fun _ _ h => h) fun q _ => ?_))
      (fun hf => ?_)
    · have h2 : n - 1 = 2 := by rw [hz4'] at ht; simpa using ht
      by_cases hq : q = R
      · subst hq; rw [upd_self, invV, upd_self, he, hb, iteT (.inr h2), Nat.add_zero]
      · rw [upd_of_ne _ _ hq, invV, upd_of_ne _ _ hq]
    · have h2 : n - 1 ≠ 2 := by rw [hz4'] at hf; simpa using hf
      refine WP.mono (op_ok (.mul R R Z2) (by decide) (by decide) (by decide) (by decide) rfl h4')
        fun s5 h5 => ?_
      have h5 : Cur b sI (n - 1) w (R :: IQ) [R] (upd (upd v R (VG.Proof.X25519.pw (v Z2) (2 * ((P - 2) >>> n)))) R
          (upd v R (VG.Proof.X25519.pw (v Z2) (2 * ((P - 2) >>> n))) R *
            upd v R (VG.Proof.X25519.pw (v Z2) (2 * ((P - 2) >>> n))) Z2)) s5 := h5
      refine h5.congr (by decide) (fun _ _ h => absurd h List.not_mem_nil) fun q _ => ?_
      by_cases hq : q = R
      · subst hq
        rw [upd_self, upd_self, upd_of_ne _ _ (by decide : Z2 ≠ R), invV, upd_self, he, hb,
          iteF (show ¬ (n - 1 = 4 ∨ n - 1 = 2) by omega_using [h4, h2]), ← VG.Proof.X25519.pw_mul,
          VG.Proof.X25519.pw_one]
      · rw [upd_of_ne _ _ hq, upd_of_ne _ _ hq, invV, upd_of_ne _ _ hq]

theorem val32_one : val32 (fun k => if k = 0 then 1 else 0) 8 = 1 := by decide

theorem invert_ok {v : Nat → Fe} {s : State} (hc : Ctx b s)
    (hS : SlotsW s.mem (State.addr b) [Z2, X2] [] v) :
    WP isa Impl.X25519.Arm.Words.invert s fun s' => Kp s s' ∧ Frame [FAW b] s.mem s'.mem ∧ Ctx b s' ∧
      SlotsW s'.mem (State.addr b) IQ [] (upd v R (VG.Proof.X25519.pw (v Z2) (P - 2))) := by
  have hR : R = 512 := rfl
  have hC : CNT = 44 := rfl
  have hA : ACC = 544 := rfl
  unfold Impl.X25519.Arm.Words.invert
  refine WP.seq ?_
  simp only [one, List.cons_append, List.nil_append]
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => wp_mov (op2_imm (by decide)) fun s2 u2 => ?_
  have k2 : Kp s s2 := (Kp.of_upd u1 (by decide)).trans (Kp.of_upd u2 (by decide))
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  refine str0_ok (k2.ctx hc) (d := R) (by decide) fun s3 u3 => ?_
  have k3 : Kp s s3 := k2.trans (Kp.of_mupd u3)
  refine WP.append (VG.Proof.X25519.Arm.stores_ok (o := R + 4) (n := 7) (by decide) (k3.ctx hc))
    fun s4 ⟨h4w, h4f, h4g, h4r⟩ => ?_
  have k4 : Kp s s4 := k3.trans (Kp.of_rest h4r List.not_mem_nil)
  refine wp_mov (op2_imm (by decide)) fun s5 u5 => ?_
  have k5 : Kp s s5 := k4.trans (Kp.of_upd u5 (by decide))
  refine str0_ok (k5.ctx hc) (d := CNT) (by decide) fun s6 u6 => WP.block_nil ?_
  have k6 : Kp s s6 := k5.trans (Kp.of_mupd u6)
  have hm6 : s6.mem = s4.mem.writeW (State.addr b + BitVec.ofNat 64 CNT) (255 : BitVec 32) := by
    rw [u6.mem, u5.gpr, u5.mem]
  -- The words of `R`: 1, then zeros.
  have hwR : ∀ k < 8, wd s6.mem (State.addr b) (R + 4 * k) = if k = 0 then 1 else 0 := by
    intro k hk
    rw [hm6, wd_write_other _ _ _ (by omega_using [hR, hC]) (by omega_using [hR, hk]) (by omega_using [hC])]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [Nat.mul_zero, Nat.add_zero, wd_frame h4f fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide),
        u3.mem, wd_write_self, u2.other _ (by decide), u1.gpr]; rfl
    · have := h4w (k - 1) (by omega_using [hk])
      rw [show R + 4 + 4 * (k - 1) = R + 4 * k by omega_using [hk0], u3.gpr, u2.gpr] at this
      rw [this]; simp only [show k ≠ 0 by omega_using [hk0], ite_false]; rfl
  have hf6 : Frame [⟨State.addr b + BitVec.ofNat 64 R, 32⟩, ⟨State.addr b + BitVec.ofNat 64 44, 8⟩] s.mem s6.mem := by
    rw [hm6, ← hm2]
    refine ((((Frame.refl _ _).writeW (List.mem_cons_self ..) (s2.gpr .r1)
      (Offset.contains (State.addr b) (d := R) (n := 4) (e := R) (k := 32) (Nat.le_refl _) (by decide)
        (by decide))).trans ?_).writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
      (Offset.contains (State.addr b) (d := CNT) (n := 4) (e := 44) (k := 8) (by decide) (by decide) (by decide)))
    rw [← u3.mem]
    exact h4f.sub fun r hr => ⟨_, List.mem_cons_self .., by
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by decide) (by decide)⟩
  have hfa : Frame [FAW b] s.mem s6.mem := hf6.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.sub _ (by decide) (by decide)⟩
  have hS6 : SlotsW s6.mem (State.addr b) [Z2, X2] [] v := hS.frame hf6 fun r hr q hq h1 h2 k hk => by
    have hq' : q + 32 ≤ R := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> decide
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint _ (.inl (by omega_using [hq', hk])) (by omega_using [h2, hA, hk]) (by omega_using [hR])
    · exact Offset.disjoint _ (.inr (by omega_using [h1])) (by omega_using [h2, hA, hk]) (by decide)
  have hI6 : SlotsW s6.mem (State.addr b) IQ [] (invV v 255) := by
    intro q hq
    simp only [IQ, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · obtain ⟨h1, h2, -⟩ := hS6 Z2 (by decide)
      exact ⟨h1, by rw [invV, upd_of_ne _ _ (by decide)]; exact h2, fun h => absurd h List.not_mem_nil⟩
    · refine ⟨by decide, ?_, fun h => absurd h List.not_mem_nil⟩
      rw [W_of hwR, val32_one, invV, upd_self, p255, VG.Proof.X25519.pw_zero]
      rfl
    · obtain ⟨h1, h2, -⟩ := hS6 X2 (by decide)
      exact ⟨h1, by rw [invV, upd_of_ne _ _ (by decide)]; exact h2, fun h => absurd h List.not_mem_nil⟩
  have h255 : InvInv b s6 (wd s6.mem (State.addr b) SWAP) v 255 s6 :=
    ⟨⟨k6.ctx hc, Kp.refl _, Frame.refl _ _, by rw [hm6, wd_write_self]; rfl, rfl, hI6⟩⟩
  refine WP.mono (Q := InvInv b s6 (wd s6.mem (State.addr b) SWAP) v 0) (WP.loop (M := isa)
    (fun m s' => 1 ≤ m ∧ m ≤ 255 ∧ InvInv b s6 (wd s6.mem (State.addr b) SWAP) v m s') ?_ 255 s6
    ⟨by decide, Nat.le_refl _, h255⟩)
    fun s' ⟨h'⟩ => ⟨k6.trans h'.kp, hfa.trans h'.frame, h'.ctx, h'.slots.congr fun q _ => by
      simp only [invV, Nat.shiftRight_zero]⟩
  rintro m s' ⟨h1, h2, hl⟩
  refine WP.mono (invStep_ok h1 h2 hl) fun s'' ⟨hl', hz⟩ => ?_
  by_cases hm : m - 1 = 0
  · exact .inl ⟨by rw [eval_ne, hz]; simp [hm], by rw [hm] at hl'; exact hl'⟩
  · exact .inr ⟨by rw [eval_ne, hz]; simp [hm], m - 1, by omega_using [hm], by omega_using [hm], by omega_using [h2], hl'⟩

end

end VG.Proof.X25519.Arm.Words
