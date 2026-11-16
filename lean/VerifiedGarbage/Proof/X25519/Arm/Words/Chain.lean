module

public import VerifiedGarbage.Proof.X25519.Arm.Field
public import VerifiedGarbage.Impl.X25519.Arm.Words
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

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
