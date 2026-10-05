import VerifiedGarbage.Proof.MlKem.AArch64.CompressEncode
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.Impl.MlKem1024.AArch64.Compress
import VerifiedGarbage.Proof.Framework.Range

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem1024.AArch64.Stream`. -/
section

/-!
# ML-KEM-1024 on AArch64: bits streaming through a register

The arithmetic of the compression loops of ML-KEM-1024, which stream the bits
of a group of 8 coefficients of `d` bits (`8d` bits, `d` bytes) through `x9`,
for `d` = 5 and 11:

* a number's low bits determine its low digits (`digits_range_mod`), so
  byte `j` of a group is byte `j` of the number of its first coefficients
  once they hold its bits (`byte_of_mod`);
* adding a digit above the bits a register holds (`add_shift_div`), and
  shifting a byte out of it (`div_div8`).
-/

namespace VG.Proof.MlKem1024.AArch64

open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64

/-- The widths of ML-KEM-1024's compression. -/
theorem mem_widths {d : Nat} (hd : d ∈ Spec.MlKem1024.compressWidths) : d = 5 ∨ d = 11 :=
  mem_compressWidths1024 hd

/-- The digits of the first `e'` values, modulo `2^(w e)` for `e ≤ e'`, are
those of the first `e`. -/
theorem digits_range_mod {w : Nat} {f : Nat → Nat} (hf : ∀ i, f i < 2 ^ w) {e : Nat} :
    ∀ {e'}, e ≤ e' → digits w ((List.range e').map f) % 2 ^ (w * e) = digits w ((List.range e).map f)
  | e', h => by
    induction e' with
    | zero =>
      have : e = 0 := by omega
      subst this
      exact Nat.mod_eq_of_lt (digits_range_lt hf 0)
    | succ e' ih =>
      rcases (by omega : e ≤ e' ∨ e = e' + 1) with h' | rfl
      · rw [digits_range_succ, show w * e' = w * e + w * (e' - e) by
          rw [← Nat.mul_add, Nat.add_sub_cancel' h'], Nat.pow_add, Nat.mul_assoc,
          Nat.add_mul_mod_self_left, ih h']
      · exact Nat.mod_eq_of_lt (digits_range_lt hf _)

/-- Bits `[s, s + w)` of numbers equal modulo `2^M`, for `s + w ≤ M`. -/
theorem bits_of_mod {a b M s w : Nat} (h : a % 2 ^ M = b % 2 ^ M) (hs : s + w ≤ M) :
    a / 2 ^ s % 2 ^ w = b / 2 ^ s % 2 ^ w := by
  have e : ∀ x, x / 2 ^ s % 2 ^ w = x % 2 ^ M % 2 ^ (s + w) / 2 ^ s := fun x => by
    rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hs), Nat.pow_add, Nat.mod_mul_right_div_self]
  rw [e, e b, h]

/-- Byte `j` of numbers equal modulo `2^M`, for `8 j + 8 ≤ M`. -/
theorem byte_of_mod {a b M j : Nat} (h : a % 2 ^ M = b % 2 ^ M) (hj : 8 * j + 8 ≤ M) :
    a / 2 ^ (8 * j) % 256 = b / 2 ^ (8 * j) % 256 :=
  VG.Proof.MlKem1024.AArch64.bits_of_mod (w := 8) h hj

/-- A digit `c` added above the `D mod 8` bits left of a number `a < 2^D`
after its `⌊D / 8⌋` whole bytes. -/
theorem add_shift_div (a c D : Nat) :
    a / 2 ^ (8 * (D / 8)) + c * 2 ^ (D % 8) = (a + 2 ^ D * c) / 2 ^ (8 * (D / 8)) := by
  have e : 2 ^ D * c = 2 ^ (8 * (D / 8)) * (c * 2 ^ (D % 8)) := by
    conv => lhs; rw [← Nat.div_add_mod D 8]
    rw [Nat.pow_add, Nat.mul_comm c, Nat.mul_assoc]
  rw [e, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _)]

/-- The bits left of a number `a < 2^D` after its `⌊D / 8⌋` whole bytes. -/
theorem shift_lt {a D : Nat} (h : a < 2 ^ D) : a / 2 ^ (8 * (D / 8)) < 2 ^ (D % 8) := by
  refine Nat.div_lt_of_lt_mul ?_
  rw [← Nat.pow_add, Nat.div_add_mod]
  exact h

/-- A byte `b` added at bit `8 j` of a number `a`, above the `D ≤ 8 j` bits
shifted out. -/
theorem add_byte_div {a b D j : Nat} (h : D ≤ 8 * j) :
    a / 2 ^ D + b * 2 ^ (8 * j - D) = (a + 2 ^ (8 * j) * b) / 2 ^ D := by
  have e : 2 ^ (8 * j) * b = 2 ^ D * (b * 2 ^ (8 * j - D)) := by
    rw [Nat.mul_comm b, ← Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_cancel' h]
  rw [e, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _)]

/-- A number less than `2^N`, shifted right by `D ≤ N`. -/
theorem div_lt_sub {a D N : Nat} (h : a < 2 ^ N) (hD : D ≤ N) : a / 2 ^ D < 2 ^ (N - D) := by
  refine Nat.div_lt_of_lt_mul ?_
  rw [← Nat.pow_add, Nat.add_sub_cancel' hD]
  exact h

/-- A byte shifted out. -/
theorem div_div8 (a j : Nat) : a / 2 ^ (8 * j) / 2 ^ 8 = a / 2 ^ (8 * (j + 1)) := by
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.mul_succ]

end VG.Proof.MlKem1024.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem1024.AArch64.CompressEncode`. -/
section

/-!
# ML-KEM-1024 on AArch64: `vg_mlkem1024_compress_encode`

Group `g` of the output is the number whose base-`2ᵈ` digits are the
compressed coefficients `8g … 8g + 7` (`byteEncode_group`), `acc g 8`. Before
coefficient `e` of the group, the output holds its first `⌊d e / 8⌋` bytes,
and `x9` the bits of `acc g e` above them (`SInv`); the coefficient is added
above those bits (`coeff_step`), and each byte that the bits of `acc g (e +
1)` complete is stored and shifted out (`byte_step`).
-/

namespace VG.Proof.MlKem1024

open VG VG.AArch64 VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- AArch64 contract for `vg_mlkem1024_compress_encode(f = x0, d = w1, out =
x2, len = x3)`: if `d` is 5 or 11, `len = 32 d` and the polynomial at `f` is
reduced, writes `ByteEncode_d(Compress_d(f))` to the `len` bytes at `out`. The
code may read `f` and write `out`, which do not overlap. -/
def compressEncodeAArch64 : Contract AArch64.isa where
  pre s :=
    s.rd = [⟨s.gpr .x0, 1024⟩] ∧ s.wr = [⟨s.gpr .x2, (s.gpr .x3).toNat⟩] ∧
    Region.Disjoint ⟨s.gpr .x0, 1024⟩ ⟨s.gpr .x2, (s.gpr .x3).toNat⟩ ∧
    ((s.gpr .x1).setWidth 32).toNat ∈ Spec.MlKem1024.compressWidths ∧
    (s.gpr .x3).toNat = 32 * ((s.gpr .x1).setWidth 32).toNat ∧ Reduced s.mem (s.gpr .x0)
  post s s' := bytesAt s'.mem (s.gpr .x2) (s.gpr .x3).toNat =
    compressEncode ((s.gpr .x1).setWidth 32).toNat (polyAt s.mem (s.gpr .x0))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧
    s₁.sp = s₂.sp

end VG.Proof.MlKem1024

namespace VG.Proof.MlKem1024.AArch64.CE

open VG VG.AArch64 VG.Impl.MlKem1024.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
  VG.Proof.MlKem1024.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

section
variable (d : Nat) (s₀ : State)

abbrev fP : Addr := s₀.gpr .x0
abbrev oP : Addr := s₀.gpr .x2
abbrev oR : Region := ⟨VG.Proof.MlKem1024.AArch64.CE.oP s₀, 32 * d⟩
abbrev P : Poly := polyAt s₀.mem (VG.Proof.MlKem1024.AArch64.CE.fP s₀)
/-- Coefficient `i`, compressed. -/
def C (i : Nat) : Nat := compress d (VG.Proof.MlKem1024.AArch64.CE.P s₀)[i]!
/-- Byte `j` of the output. -/
def L (j : Nat) : Byte := (compressEncode d (VG.Proof.MlKem1024.AArch64.CE.P s₀))[j]!
/-- The first `e` compressed coefficients of group `g`, as the digits of a number. -/
def acc (g e : Nat) : Nat := digits d ((List.range e).map fun e' => VG.Proof.MlKem1024.AArch64.CE.C d s₀ (8 * g + e'))
/-- The output's bytes before. -/
def old (j : Nat) : Byte := s₀.mem (VG.Proof.MlKem1024.AArch64.CE.oP s₀ + BitVec.ofNat 64 j)

end

structure Pre (d : Nat) (s₀ : State) : Prop where
  hd : d = 5 ∨ d = 11
  rd : s₀.rd = [polyRegion (VG.Proof.MlKem1024.AArch64.CE.fP s₀)]
  wr : s₀.wr = [VG.Proof.MlKem1024.AArch64.CE.oR d s₀]
  disj : (polyRegion (VG.Proof.MlKem1024.AArch64.CE.fP s₀)).Disjoint (VG.Proof.MlKem1024.AArch64.CE.oR d s₀)
  red : Reduced s₀.mem (VG.Proof.MlKem1024.AArch64.CE.fP s₀)
  x6 : (s₀.gpr .x6).toNat = 261888

/-- After `g` groups. -/
structure Inv (d : Nat) (s₀ : State) (g : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x0 : s.gpr .x0 = VG.Proof.MlKem1024.AArch64.CE.fP s₀ + BitVec.ofNat 64 (32 * g)
  x2 : s.gpr .x2 = VG.Proof.MlKem1024.AArch64.CE.oP s₀ + BitVec.ofNat 64 (d * g)
  x5 : (s.gpr .x5).toNat = compressMul1024 d
  x6 : (s.gpr .x6).toNat = 261888
  x7 : (s.gpr .x7).toNat = 2 ^ d - 1
  x11 : (s.gpr .x11).toNat = 32 - g
  out : BytesUpTo s.mem (VG.Proof.MlKem1024.AArch64.CE.oP s₀) (32 * d) (d * g) (VG.Proof.MlKem1024.AArch64.CE.L d s₀) (VG.Proof.MlKem1024.AArch64.CE.old s₀)
  frame : Frame [VG.Proof.MlKem1024.AArch64.CE.oR d s₀] s₀.mem s.mem

theorem C_lt (d : Nat) (s₀ : State) (i : Nat) : VG.Proof.MlKem1024.AArch64.CE.C d s₀ i < 2 ^ d := compress_lt _ _

theorem acc_succ (d : Nat) (s₀ : State) (g e : Nat) :
    VG.Proof.MlKem1024.AArch64.CE.acc d s₀ g (e + 1) = VG.Proof.MlKem1024.AArch64.CE.acc d s₀ g e + 2 ^ (d * e) * VG.Proof.MlKem1024.AArch64.CE.C d s₀ (8 * g + e) :=
  digits_range_succ _ _ _

theorem acc_lt (d : Nat) (s₀ : State) (g e : Nat) : VG.Proof.MlKem1024.AArch64.CE.acc d s₀ g e < 2 ^ (d * e) :=
  digits_range_lt (fun _ => VG.Proof.MlKem1024.AArch64.CE.C_lt _ _ _) _

theorem acc_mod (d : Nat) (s₀ : State) (g : Nat) {e e' : Nat} (h : e ≤ e') :
    VG.Proof.MlKem1024.AArch64.CE.acc d s₀ g e' % 2 ^ (d * e) = VG.Proof.MlKem1024.AArch64.CE.acc d s₀ g e :=
  VG.Proof.MlKem1024.AArch64.digits_range_mod (fun _ => VG.Proof.MlKem1024.AArch64.CE.C_lt _ _ _) h

/-- Byte `j` of group `g` of the output. -/
theorem L_eq {d : Nat} (hd : d = 5 ∨ d = 11) (s₀ : State) {g j : Nat} (hg : g < 32) (hj : j < d) :
    VG.Proof.MlKem1024.AArch64.CE.L d s₀ (d * g + j) = BitVec.ofNat 8 (VG.Proof.MlKem1024.AArch64.CE.acc d s₀ g 8 / 2 ^ (8 * j)) := by
  have hk : d * g + j < 32 * d := by rcases hd with rfl | rfl <;> omega
  rw [VG.Proof.MlKem1024.AArch64.CE.L, Spec.MlKem.compressEncode, byteEncode_group (c := 8) (by omega) (Nat.mul_comm d 8)
    (map_toList_lt _ (compress_lt d)) hj hk,
    take_drop_eq _ 0 (by rw [map_toList_length]; omega), VG.Proof.MlKem1024.AArch64.CE.acc]
  refine congrArg (fun x => BitVec.ofNat 8 (digits d x / 2 ^ (8 * j))) (List.map_congr_left ?_)
  intro e he
  rw [map_toList_getD _ _ (by have := List.mem_range.mp he; omega)]
  rfl

theorem Pre.coeff {d : Nat} {s₀ : State} (hp : VG.Proof.MlKem1024.AArch64.CE.Pre d s₀) {m : Mem}
    (hf : Frame [VG.Proof.MlKem1024.AArch64.CE.oR d s₀] s₀.mem m) {i : Nat} (hi : i < 256) :
    (coeffAt m (VG.Proof.MlKem1024.AArch64.CE.fP s₀) i).toNat = ((VG.Proof.MlKem1024.AArch64.CE.P s₀)[i]!).val := by
  rw [coeffAt_frame hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.disj) hi,
    polyAt_val hp.red (show i < n from hi)]

/-- Within group `g`, before coefficient `e`: the bytes before `⌊d e / 8⌋`
stored, and the bits of `acc g e` above them in `x9`. -/
structure SInv (d : Nat) (s₀ : State) (g : Nat) (s : State) (e : Nat) (t : State) : Prop where
  keep : Keep [.x9, .x10] s t
  x9 : (t.gpr .x9).toNat = VG.Proof.MlKem1024.AArch64.CE.acc d s₀ g e / 2 ^ (8 * ceJ d e)
  out : BytesUpTo t.mem (VG.Proof.MlKem1024.AArch64.CE.oP s₀) (32 * d) (d * g + ceJ d e) (VG.Proof.MlKem1024.AArch64.CE.L d s₀) (VG.Proof.MlKem1024.AArch64.CE.old s₀)
  frame : Frame [VG.Proof.MlKem1024.AArch64.CE.oR d s₀] s₀.mem t.mem

/-- Within coefficient `e` of group `g`, after `k` of the bytes it completes. -/
structure BInv (d : Nat) (s₀ : State) (g : Nat) (s : State) (e k : Nat) (t : State) : Prop where
  keep : Keep [.x9, .x10] s t
  x9 : (t.gpr .x9).toNat = VG.Proof.MlKem1024.AArch64.CE.acc d s₀ g (e + 1) / 2 ^ (8 * (ceJ d e + k))
  out : BytesUpTo t.mem (VG.Proof.MlKem1024.AArch64.CE.oP s₀) (32 * d) (d * g + (ceJ d e + k)) (VG.Proof.MlKem1024.AArch64.CE.L d s₀) (VG.Proof.MlKem1024.AArch64.CE.old s₀)
  frame : Frame [VG.Proof.MlKem1024.AArch64.CE.oR d s₀] s₀.mem t.mem

theorem ceJ_le (d e : Nat) : ceJ d e ≤ ceJ d (e + 1) := by
  unfold ceJ; rw [Nat.mul_succ]; omega

/-- Coefficient `e` of group `g`, compressed, into `x9` above its bits. -/
theorem coeff_step {d : Nat} {s₀ : State} (hp : VG.Proof.MlKem1024.AArch64.CE.Pre d s₀) {g : Nat} (hg : g < 32) {s : State}
    (h : VG.Proof.MlKem1024.AArch64.CE.Inv d s₀ g s) (e : Nat) (he : e < 8) (t : State) (ht : VG.Proof.MlKem1024.AArch64.CE.SInv d s₀ g s e t) :
    WP isa (.block (ceCoeff d e)) t (VG.Proof.MlKem1024.AArch64.CE.BInv d s₀ g s e 0) := by
  have hd := hp.hd
  have hi : 8 * g + e < 256 := by omega
  refine wp_ldrw (a := coeffAddr (VG.Proof.MlKem1024.AArch64.CE.fP s₀) (8 * g + e)) ⟨by omega, by omega⟩ ?_ ?_ fun t₁ h₁ e₁ => ?_
  · rw [ht.keep.get .x0, h.x0, ptr_add, coeffAddr, Nat.mul_add, ← Nat.mul_assoc]
  · rw [ht.keep.rd, ht.keep.wr, h.rd, h.wr, hp.rd, hp.wr]
    exact in_rd (in_regions (List.mem_singleton_self _) (coeff_contains _ (show _ < n from hi)))
  have va : (t₁.gpr .x10).toNat = ((VG.Proof.MlKem1024.AArch64.CE.P s₀)[8 * g + e]!).val := by
    rw [e₁, toNat_readW32, ← coeffAt_eq, hp.coeff ht.frame hi]
  have hdw : d ∈ Spec.MlKem1024.compressWidths := by rcases hd with rfl | rfl <;> decide
  have harg := compress1024_arg_lt hdw (VG.Proof.MlKem1024.AArch64.CE.P s₀)[8 * g + e]!
  have x5 : (t₁.gpr .x5).toNat = compressMul1024 d := by rw [h₁.get .x5, ht.keep.get .x5, h.x5]
  have x6 : ∀ {u : State}, u.gpr .x6 = s.gpr .x6 → (u.gpr .x6).toNat = compressAdd1024 := fun e =>
    by rw [e, h.x6]; rfl
  have x7 : ∀ {u : State}, u.gpr .x7 = s.gpr .x7 → (u.gpr .x7).toNat = 2 ^ d - 1 := fun e =>
    by rw [e, h.x7]
  refine wp_mul fun t₂ h₂ e₂ => wp_add fun t₃ h₃ e₃ => wp_lsr (by decide) fun t₄ h₄ e₄ =>
    wp_and fun t₅ h₅ e₅ => wp_lsl (by omega) fun t₆ h₆ e₆ => wp_add fun t₇ h₇ e₇ => wp_nil ?_
  have v₂ : (t₂.gpr .x10).toNat = ((VG.Proof.MlKem1024.AArch64.CE.P s₀)[8 * g + e]!).val * compressMul1024 d := by
    rw [e₂, toNat_mul_n (by rw [va, x5]; omega), va, x5]
  have k₂ := (ht.keep.trans h₁.keep).trans h₂.keep
  have v₃ : (t₃.gpr .x10).toNat = ((VG.Proof.MlKem1024.AArch64.CE.P s₀)[8 * g + e]!).val * compressMul1024 d + compressAdd1024 := by
    rw [e₃, toNat_add_n (by rw [v₂, x6 (k₂.get .x6)]; omega), v₂, x6 (k₂.get .x6)]
  have v₅ : (t₅.gpr .x10).toNat = VG.Proof.MlKem1024.AArch64.CE.C d s₀ (8 * g + e) := by
    rw [e₅, toNat_and_mask _ _ (x7 ((k₂.trans h₃.keep).trans h₄.keep |>.get .x7)), e₄, toNat_lsr, v₃,
      VG.Proof.MlKem1024.AArch64.CE.C, compress1024_eq hdw]
  have hC : VG.Proof.MlKem1024.AArch64.CE.C d s₀ (8 * g + e) < 2048 := by
    have := VG.Proof.MlKem1024.AArch64.CE.C_lt d s₀ (8 * g + e)
    have : 2 ^ d ≤ 2048 := by rcases hd with rfl | rfl <;> decide
    omega
  have p8 : 2 ^ (d * e % 8) ≤ 128 :=
    Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega : d * e % 8 ≤ 7)) (by decide)
  have hlt : VG.Proof.MlKem1024.AArch64.CE.C d s₀ (8 * g + e) * 2 ^ (d * e % 8) ≤ 2047 * 128 :=
    Nat.mul_le_mul (by omega) p8
  have v₆ : (t₆.gpr .x10).toNat = VG.Proof.MlKem1024.AArch64.CE.C d s₀ (8 * g + e) * 2 ^ (d * e % 8) := by
    rw [e₆, toNat_lsl_n (by rw [v₅]; omega), v₅]
  have hx9 : VG.Proof.MlKem1024.AArch64.CE.acc d s₀ g e / 2 ^ (8 * ceJ d e) < 128 :=
    Nat.lt_of_lt_of_le (VG.Proof.MlKem1024.AArch64.shift_lt (VG.Proof.MlKem1024.AArch64.CE.acc_lt d s₀ g e)) p8
  have v₉ : (t₆.gpr .x9).toNat = VG.Proof.MlKem1024.AArch64.CE.acc d s₀ g e / 2 ^ (8 * ceJ d e) := by
    rw [h₆.get .x9, h₅.get .x9, h₄.get .x9, h₃.get .x9, h₂.get .x9, h₁.get .x9, ht.x9]
  have m₇ : t₇.mem = t.mem := by
    rw [h₇.mem, h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  refine ⟨(((((((ht.keep.trans h₁.keep).trans h₂.keep).trans h₃.keep).trans h₄.keep).trans
    h₅.keep).trans h₆.keep).trans h₇.keep).mono, ?_, by rw [m₇, Nat.add_zero]; exact ht.out,
    by rw [m₇]; exact ht.frame⟩
  rw [e₇, toNat_add_n (by rw [v₉, v₆]; omega), v₉, v₆, ceJ, VG.Proof.MlKem1024.AArch64.add_shift_div, ← VG.Proof.MlKem1024.AArch64.CE.acc_succ]
  rfl

/-- Byte `k` of those coefficient `e` of group `g` completes, stored and shifted out of `x9`. -/
theorem byte_step {d : Nat} {s₀ : State} (hp : VG.Proof.MlKem1024.AArch64.CE.Pre d s₀) {g : Nat} (hg : g < 32) {s : State}
    (h : VG.Proof.MlKem1024.AArch64.CE.Inv d s₀ g s) (e : Nat) (he : e < 8) (k : Nat) (t : State)
    (hk : k < ceJ d (e + 1) - ceJ d e) (ht : VG.Proof.MlKem1024.AArch64.CE.BInv d s₀ g s e k t) :
    WP isa (.block (ceByte (ceJ d e + k))) t (VG.Proof.MlKem1024.AArch64.CE.BInv d s₀ g s e (k + 1)) := by
  have hd := hp.hd
  have hJ : ceJ d e + k < ceJ d (e + 1) := by omega
  have hJ' : 8 * (ceJ d e + k) + 8 ≤ d * (e + 1) := by
    have : 8 * ceJ d (e + 1) ≤ d * (e + 1) := by unfold ceJ; omega
    omega
  have hjd : ceJ d e + k < d := by
    have : ceJ d (e + 1) ≤ d := by
      unfold ceJ; rw [Nat.mul_succ]; rcases hd with rfl | rfl <;> omega
    omega
  have hN : d * g + (ceJ d e + k) < 32 * d := by rcases hd with rfl | rfl <;> omega
  have hj4 : ceJ d e + k < 4096 := by rcases hd with rfl | rfl <;> omega
  refine wp_strb (a := VG.Proof.MlKem1024.AArch64.CE.oP s₀ + BitVec.ofNat 64 (d * g + (ceJ d e + k))) hj4
    (by rw [ht.keep.get .x2, h.x2, ptr_add]) ?_ fun t₁ h₁ => wp_lsr (by decide) fun t₂ h₂ e₂ => wp_nil ?_
  · rw [ht.keep.wr, h.wr, hp.wr]
    exact in_regions (List.mem_singleton_self _) (contains_off (by omega) (by omega))
  have hb : (t.gpr .x9).setWidth 8 = VG.Proof.MlKem1024.AArch64.CE.L d s₀ (d * g + (ceJ d e + k)) := by
    rw [setWidth8_of_toNat ht.x9, VG.Proof.MlKem1024.AArch64.CE.L_eq hd s₀ hg hjd]
    exact ofNat8_eq (VG.Proof.MlKem1024.AArch64.byte_of_mod ((VG.Proof.MlKem1024.AArch64.CE.acc_mod d s₀ g (show e + 1 ≤ 8 by omega)).trans
      (Nat.mod_eq_of_lt (VG.Proof.MlKem1024.AArch64.CE.acc_lt d s₀ g (e + 1))).symm) hJ').symm
  refine ⟨(ht.keep.trans (h₁.keep.trans h₂.keep)).mono, ?_, ?_, ?_⟩
  · rw [e₂, toNat_lsr, h₁.gpr, ht.x9, VG.Proof.MlKem1024.AArch64.div_div8]
    rfl
  · rw [h₂.mem, h₁.mem, hb, show d * g + (ceJ d e + (k + 1)) = d * g + (ceJ d e + k) + 1 by omega]
    exact ht.out.write (by omega) hN rfl
  · rw [h₂.mem, h₁.mem]
    exact ht.frame.writeW (List.mem_singleton_self _) _ (contains_off (by omega) (by omega))

/-- Coefficient `e` of group `g`, and the bytes it completes. -/
theorem coeffs_step {d : Nat} {s₀ : State} (hp : VG.Proof.MlKem1024.AArch64.CE.Pre d s₀) {g : Nat} (hg : g < 32) {s : State}
    (h : VG.Proof.MlKem1024.AArch64.CE.Inv d s₀ g s) (e : Nat) (t : State) (he : e < 8) (ht : VG.Proof.MlKem1024.AArch64.CE.SInv d s₀ g s e t) :
    WP isa (.block (ceStep d e)) t (VG.Proof.MlKem1024.AArch64.CE.SInv d s₀ g s (e + 1)) := by
  rw [ceStep, WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem1024.AArch64.CE.coeff_step hp hg h e he t ht) fun t₁ h₁ => ?_
  have hJ := VG.Proof.MlKem1024.AArch64.CE.ceJ_le d e
  refine WP.mono (wp_range_flatMap (M := isa) (VG.Proof.MlKem1024.AArch64.CE.BInv d s₀ g s e)
    (fun k u hk hu => VG.Proof.MlKem1024.AArch64.CE.byte_step hp hg h e he k u hk hu) _ (Nat.le_refl _) t₁ h₁) fun t₂ h₂ => ?_
  have e' : ceJ d e + (ceJ d (e + 1) - ceJ d e) = ceJ d (e + 1) := by omega
  have x9 := h₂.x9
  have o := h₂.out
  rw [e'] at x9 o
  exact ⟨h₂.keep, x9, o, h₂.frame⟩

theorem ceBody_eq (d : Nat) : ceBody d = .movz .x .x9 0 0 :: ((List.range 8).flatMap (ceStep d) ++
    ([.addImm .x .x0 .x0 32, .addImm .x .x2 .x2 d, .subImm .x .x11 .x11 1] : List Instr)) := by
  simp only [ceBody, List.cons_append]

/-- One group. -/
theorem step {d : Nat} {s₀ : State} (hp : VG.Proof.MlKem1024.AArch64.CE.Pre d s₀) {g : Nat} (hg : g < 32) {s : State}
    (h : VG.Proof.MlKem1024.AArch64.CE.Inv d s₀ g s) :
    WP isa (.block (ceBody d)) s fun s' =>
      VG.Proof.MlKem1024.AArch64.CE.Inv d s₀ (g + 1) s' ∧ ((s'.gpr .x11).toNat ≠ 0 ↔ g + 1 ≠ 32) := by
  have hd := hp.hd
  rw [VG.Proof.MlKem1024.AArch64.CE.ceBody_eq]
  refine wp_movz fun s₁ h₁ e₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (VG.Proof.MlKem1024.AArch64.CE.SInv d s₀ g s)
    (fun e t he ht => VG.Proof.MlKem1024.AArch64.CE.coeffs_step hp hg h e t he ht) 8 (Nat.le_refl _) s₁
    ⟨h₁.keep.mono, by
      rw [e₁, toNat_imm]; simp only [VG.Proof.MlKem1024.AArch64.CE.acc, List.range_zero, List.map_nil, digits_nil, Nat.zero_div]; rfl,
      by rw [h₁.mem, show ceJ d 0 = 0 by simp [ceJ], Nat.add_zero]; exact h.out,
      by rw [h₁.mem]; exact h.frame⟩)
    fun s₂ h₂ => ?_
  have e8 : ceJ d 8 = d := by unfold ceJ; omega
  have o₂ := h₂.out
  rw [e8] at o₂
  refine wp_addImm (by decide) fun s₃ h₃ e₃ => wp_addImm (by rcases hd with rfl | rfl <;> decide)
    fun s₄ h₄ e₄ => wp_subImm (by decide) fun s₅ h₅ e₅ => wp_nil ?_
  have k₄ := (h₂.keep.trans h₃.keep).trans h₄.keep
  have c11 : (s₄.gpr .x11).toNat = 32 - g := by rw [k₄.get .x11, h.x11]
  have v11 : (s₅.gpr .x11).toNat = 32 - (g + 1) := by
    rw [e₅, toNat_sub_n (by rw [c11]; simp; omega), c11]
    simp
    omega
  have k₅ := k₄.trans h₅.keep
  refine ⟨⟨by rw [k₅.rd, h.rd], by rw [k₅.wr, h.wr], by rw [k₅.sp, h.sp], ?_, ?_,
    by rw [k₅.get .x5, h.x5], by rw [k₅.get .x6, h.x6], by rw [k₅.get .x7, h.x7], v11, ?_, ?_⟩,
    by rw [v11]; omega⟩
  · rw [h₅.get .x0, h₄.get .x0, e₃, h₂.keep.get .x0, h.x0, ptr_next]
  · rw [h₅.get .x2, e₄, h₃.get .x2, h₂.keep.get .x2, h.x2, ptr_next]
  · rw [h₅.mem, h₄.mem, h₃.mem, Nat.mul_succ]
    exact o₂
  · rw [h₅.mem, h₄.mem, h₃.mem]
    exact h₂.frame

/-- The loop: `ByteEncode_d(Compress_d(f))` into the output. -/
theorem loop_ok {d : Nat} {s₀ : State} (hp : VG.Proof.MlKem1024.AArch64.CE.Pre d s₀) :
    WP isa (ceLoop d) s₀ fun s' => s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
      bytesAt s'.mem (VG.Proof.MlKem1024.AArch64.CE.oP s₀) (32 * d) = compressEncode d (VG.Proof.MlKem1024.AArch64.CE.P s₀) := by
  have hd := hp.hd
  refine WP.seq ?_
  rw [List.append_assoc]
  refine wp_movImm fun s₁ h₁ e₁ => wp_movImm fun s₂ h₂ e₂ => wp_movz fun s₃ h₃ e₃ => wp_nil ?_
  refine WP.mono (count_loop (by decide) (VG.Proof.MlKem1024.AArch64.CE.Inv d s₀) (fun g hg s h => VG.Proof.MlKem1024.AArch64.CE.step hp hg h) ?_)
    fun s' h => ⟨h.rd, h.wr, h.sp, (show BytesUpTo _ _ _ (32 * d) _ _ from Nat.mul_comm d 32 ▸ h.out).eq
      (compressEncode_length _ _) fun _ _ => rfl⟩
  have k₃ := (h₁.keep.trans h₂.keep).trans h₃.keep
  have m₃ : s₃.mem = s₀.mem := by rw [h₃.mem, h₂.mem, h₁.mem]
  have p5 : ceMul d < 2 ^ 64 := by unfold ceMul; split <;> decide
  have p7 : 2 ^ d - 1 < 2 ^ 64 := by rcases hd with rfl | rfl <;> decide
  refine ⟨k₃.rd, k₃.wr, k₃.sp, by rw [k₃.get .x0, Nat.mul_zero, ptr_zero],
    by rw [k₃.get .x2, Nat.mul_zero, ptr_zero],
    by rw [h₃.get .x5, h₂.get .x5, e₁, toNat_ofNat_lt p5]; rfl,
    by rw [k₃.get .x6, hp.x6], by rw [h₃.get .x7, e₂, toNat_ofNat_lt p7],
    by rw [e₃, toNat_imm]; rfl, ?_, ?_⟩
  · rw [m₃, Nat.mul_zero]; exact BytesUpTo.zero _
  · rw [m₃]; exact Frame.refl _ _

/-- One width, from the state after the dispatch. -/
theorem width_ok {d : Nat} (hd : d = 5 ∨ d = 11) {s₀ s : State} (hs : compressEncodeAArch64.pre s₀)
    (hdd : ((s₀.gpr .x1).setWidth 32).toNat = d) (hk : Keep [.x6, .x9] s₀ s) (hm : s.mem = s₀.mem)
    (h6 : (s.gpr .x6).toNat = 261888) :
    WP isa (ceLoop d) s fun s' => s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
      compressEncodeAArch64.post s₀ s' := by
  obtain ⟨h1, h2, h3, -, h5, h6'⟩ := hs
  rw [hdd] at h5
  have e0 : VG.Proof.MlKem1024.AArch64.CE.fP s = s₀.gpr .x0 := hk.get .x0
  have e2 : VG.Proof.MlKem1024.AArch64.CE.oP s = s₀.gpr .x2 := hk.get .x2
  have hp : VG.Proof.MlKem1024.AArch64.CE.Pre d s :=
    ⟨hd, by rw [hk.rd, h1, e0], by rw [hk.wr, h2, VG.Proof.MlKem1024.AArch64.CE.oR, e2, h5], by rw [e0, VG.Proof.MlKem1024.AArch64.CE.oR, e2, ← h5]; exact h3,
      by rw [hm, e0]; exact h6', h6⟩
  refine WP.mono (VG.Proof.MlKem1024.AArch64.CE.loop_ok hp) fun s' ⟨r, wr, sp, e⟩ => ⟨by rw [r, hk.rd], by rw [wr, hk.wr],
    by rw [sp, hk.sp], ?_⟩
  show bytesAt s'.mem (s₀.gpr .x2) (s₀.gpr .x3).toNat = _
  rw [h5, hdd, ← hk.get .x2, e, VG.Proof.MlKem1024.AArch64.CE.P, VG.Proof.MlKem1024.AArch64.CE.fP, hm, hk.get .x0]

theorem correct (s : State) (hs : compressEncodeAArch64.pre s) :
    ∃ t s', Exec isa compressEncode s t s' ∧ abiPreserved s s' ∧ compressEncodeAArch64.post s s' := by
  have hs' := hs
  obtain ⟨-, -, -, hd, hlen, -⟩ := hs'
  have hd' := VG.Proof.MlKem1024.AArch64.mem_widths hd
  suffices h : WP isa compressEncode s fun s' => s'.sp = s.sp ∧ compressEncodeAArch64.post s s' by
    obtain ⟨t, s', he, hsp, hpost⟩ := h
    exact ⟨t, s', he, abi_of rfl (by decide +kernel) he, hpost⟩
  refine WP.seq ?_
  refine wp_movImm fun s₁ h₁ e₁ => wp_subImm (by decide) fun s₂ h₂ e₂ => wp_nil ?_
  have k₂ : Keep [.x6, .x9] s s₂ := (h₁.keep.trans h₂.keep).mono
  have m₂ : s₂.mem = s.mem := by rw [h₂.mem, h₁.mem]
  have x6 : (s₂.gpr .x6).toNat = 261888 := by rw [h₂.get .x6, e₁]; rfl
  have z₂ : isa.eval (.zero .x .x9) s₂ = some (decide ((s.gpr .x3).toNat = 160)) := by
    rw [eval_zero, eq_zero_iff, e₂, h₁.get .x3, BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    congr 1
    apply decide_eq_decide.mpr
    rcases hd' with h | h <;> rw [h] at hlen <;> omega
  refine WP.ite _ z₂ (fun hb => ?_) (fun hb => ?_)
  · have e : ((s.gpr .x1).setWidth 32).toNat = 5 := by simp at hb; omega
    exact WP.mono (VG.Proof.MlKem1024.AArch64.CE.width_ok (.inl rfl) hs e k₂ m₂ x6) fun s' ⟨_, _, sp, p⟩ => ⟨sp, p⟩
  · have e : ((s.gpr .x1).setWidth 32).toNat = 11 := by
      simp at hb
      rcases hd' with h | h <;> rw [h] at hlen <;> omega
    exact WP.mono (VG.Proof.MlKem1024.AArch64.CE.width_ok (.inr rfl) hs e k₂ m₂ x6) fun s' ⟨_, _, sp, p⟩ => ⟨sp, p⟩

theorem ct : ConstantTime isa compressEncodeAArch64.pre compressEncodeAArch64.pub compressEncode :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x2, .x3])
    (fun _ _ _ _ ⟨h0, h2, h3, hsp⟩ => agree_of hsp (by simp [h0, h2, h3])) (by taint_decide)

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 5 | .x2 => 0x2000 | .x3 => 160 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 160⟩]

theorem compressEncode_verified :
    Verified AArch64.target compressEncode (Spec.MlKem1024.compressEncodeContract AArch64.abi) :=
  Verified.of_correct VG.Proof.MlKem1024.AArch64.CE.correct VG.Proof.MlKem1024.AArch64.CE.ct (by
    mlkem_implies [Spec.MlKem1024.compressEncodeContract, Spec.MlKem1024.compressEncodeSig,
      VG.Proof.MlKem1024.compressEncodeAArch64, AArch64.abi, AArch64.argRegs] [sat] using VG.Proof.MlKem1024.AArch64.CE.sat)

end VG.Proof.MlKem1024.AArch64.CE

end
