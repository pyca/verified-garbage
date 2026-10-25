module

public import VerifiedGarbage.Proof.Ed448.PPC64LE.VChecks
public import VerifiedGarbage.Proof.Ed448.PPC64LE.BaseBits
public import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.X448.PPC64LE.Invert
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.X25519.PPC64LE.Pass

/-!
# Ed448's verification on PPC64LE: the masks

`TAB` holds the mask of each of the 1832 iterations (`tab_ok`): byte `4t + i`
is 1 for `i = 3`, and bit `t` of `4S`, `4k` and `4` for `i = 2`, `1` and `0`
(`tabV`). `tabFill` writes the 1s of `i = 3` and of bit 2 of `4`
(`tabFill_ok`), and `tabBits` the bits of a scalar into the entries `e`
(`tabBits_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE VG.Proof.X448.PPC64LE
open VG.Proof.X25519.PPC64LE hiding V FS V_lt pass_ok limb_frame

/-- The table's bytes are `f`. -/
def TabIs (b : Addr) (m : Mem) (f : Nat → Nat) : Prop :=
  ∀ h < 1832, m (b + BitVec.ofNat 64 (TAB + h)) = BitVec.ofNat 8 (f h)

/-- After `tabFill`. -/
def fill0 (h : Nat) : Nat := if h % 4 = 3 ∨ h = 8 then 1 else 0

/-- Bit `(h - 8) / 4` of `k` into the entries `e` from 8 up. -/
def tabSet (e k : Nat) (f : Nat → Nat) (h : Nat) : Nat :=
  if 8 ≤ h ∧ h % 4 = e then (k >>> ((h - 8) / 4)) &&& 1 else f h

/-- The masks of the iterations, for the scalars `S` and `K`. -/
def tabV (S K h : Nat) : Nat :=
  if h % 4 = 3 then 1 else if h % 4 = 2 then ((4 * S) >>> (h / 4)) &&& 1
  else if h % 4 = 1 then ((4 * K) >>> (h / 4)) &&& 1 else (4 >>> (h / 4)) &&& 1

/-- Bit `q` of `4x`. -/
theorem bit4 (x q : Nat) : ((4 * x) >>> q) &&& 1 = if 2 ≤ q then (x >>> (q - 2)) &&& 1 else 0 := by
  by_cases hq : 2 ≤ q
  · rw [ite_eq_left hq]
    obtain ⟨n, rfl⟩ : ∃ n, q = n + 2 := ⟨q - 2, by omega_arith⟩
    rw [Nat.add_sub_cancel, Nat.add_comm n 2, Nat.shiftRight_add,
      show (4 * x) >>> 2 = x by rw [Nat.shiftRight_eq_div_pow]; omega_arith]
  · rw [ite_eq_right hq, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
    rcases (by omega_arith : q = 0 ∨ q = 1) with rfl | rfl
    · simp only [Nat.pow_zero, Nat.div_one]; omega_arith
    · simp only [Nat.pow_one]; omega_arith

theorem one_shr (n : Nat) : (1 >>> n) &&& 1 = if n = 0 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rfl
  · rw [ite_eq_right (by omega_arith), Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (Nat.one_lt_two_pow (by omega_arith))]
    rfl

theorem tab_eq (S K : Nat) : ∀ h < 1832, tabSet 1 K (tabSet 2 S fill0) h = tabV S K h := by
  intro h _
  have e8 : 8 ≤ h ↔ 2 ≤ h / 4 := by omega_arith
  have e4 : 8 ≤ h → (h - 8) / 4 = h / 4 - 2 := fun _ => by omega_arith
  unfold tabSet fill0 tabV
  rcases (by omega_arith : h % 4 = 0 ∨ h % 4 = 1 ∨ h % 4 = 2 ∨ h % 4 = 3) with r | r | r | r <;>
    simp only [r, Nat.reduceEqDiff, and_false, ite_false, ite_true, false_or, true_or, and_true]
  · -- The entries of `4`.
    rw [show (4 : Nat) = 4 * 1 from rfl, bit4, one_shr]
    by_cases h8 : 8 ≤ h
    · rw [ite_eq_left (e8.mp h8)]
      by_cases h8' : h = 8
      · subst h8'; rfl
      · rw [ite_eq_right h8', ite_eq_right (by omega_arith)]
    · rw [ite_eq_right (fun h' => h8 (e8.mpr h')), ite_eq_right (by omega_arith)]
  · rw [bit4]
    by_cases h8 : 8 ≤ h
    · rw [ite_eq_left h8, ite_eq_left (e8.mp h8), e4 h8]
    · rw [ite_eq_right h8, ite_eq_right (fun h' => h8 (e8.mpr h')), ite_eq_right (by omega_arith)]
  · rw [bit4]
    by_cases h8 : 8 ≤ h
    · rw [ite_eq_left h8, ite_eq_left (e8.mp h8), e4 h8]
    · rw [ite_eq_right h8, ite_eq_right (fun h' => h8 (e8.mpr h')), ite_eq_right (by omega_arith)]

section
variable {b : Addr}

/-- After `j` iterations of the fill, from `s0`. -/
structure FInv (b : Addr) (s0 : State) (j : Nat) (s : State) : Prop where
  rest : Rest [.r9, .r11] s0 s
  r9 : s.gpr .r9 = b + BitVec.ofNat 64 (4 * j)
  r11 : s.gpr .r11 = BitVec.ofNat 64 (458 - j)
  frame : Frame [⟨b + BitVec.ofNat 64 TAB, 4 * j⟩] s0.mem s.mem
  vals : ∀ h < 4 * j, s.mem (b + BitVec.ofNat 64 (TAB + h)) = BitVec.ofNat 8 (if h % 4 = 3 then 1 else 0)

theorem setWidth8_ofNat {x : Nat} (hx : x < 256) : (BitVec.ofNat 64 x).setWidth 8 = BitVec.ofNat 8 x :=
  stb_byte (toNat_imm (by omega_arith))

theorem fillStep_ok {s0 s : State} (hc : VCtx b s0) (h7 : s0.gpr .r7 = BitVec.ofNat 64 0)
    (h8 : s0.gpr .r8 = BitVec.ofNat 64 1) {j : Nat} (hj : j < 458) (h : FInv b s0 j s) :
    WP isa (.block [.stb .r7 .r9 TAB, .stb .r7 .r9 (TAB + 1), .stb .r7 .r9 (TAB + 2), .stb .r8 .r9 (TAB + 3),
        .addi .r9 .r9 4, .subi .r11 .r11 1]) s fun t =>
      FInv b s0 (j + 1) t ∧ (t.gpr .r11 != 0) = decide (458 - (j + 1) ≠ 0) := by
  have hT : TAB = 1064 := rfl
  have hcs : VCtx b s := hc.of_rest h.rest (by decide) (by decide)
  have a : ∀ i < 4, s.gpr .r9 + BitVec.ofNat 64 (TAB + i) = b + BitVec.ofNat 64 (TAB + (4 * j + i)) := fun i _ => by
    rw [h.r9, Offset.add_add]; congr 2; omega_arith
  have e7 : s.gpr .r7 = BitVec.ofNat 64 0 := by rw [h.rest.gpr _ (by decide), h7]
  have e8 : s.gpr .r8 = BitVec.ofNat 64 1 := by rw [h.rest.gpr _ (by decide), h8]
  refine wp_stb (a := b + BitVec.ofNat 64 (TAB + (4 * j + 0))) (by decide) (by decide) (a 0 (by decide))
    (hcs.inW (by omega_arith)) fun s1 u1 => ?_
  refine wp_stb (a := b + BitVec.ofNat 64 (TAB + (4 * j + 1))) (by decide) (by decide)
    (by rw [u1.gpr]; exact a 1 (by decide)) (by rw [u1.wr]; exact hcs.inW (by omega_arith)) fun s2 u2 => ?_
  refine wp_stb (a := b + BitVec.ofNat 64 (TAB + (4 * j + 2))) (by decide) (by decide)
    (by rw [u2.gpr, u1.gpr]; exact a 2 (by decide)) (by rw [u2.wr, u1.wr]; exact hcs.inW (by omega_arith)) fun s3 u3 => ?_
  refine wp_stb (a := b + BitVec.ofNat 64 (TAB + (4 * j + 3))) (by decide) (by decide)
    (by rw [u3.gpr, u2.gpr, u1.gpr]; exact a 3 (by decide)) (by rw [u3.wr, u2.wr, u1.wr]; exact hcs.inW (by omega_arith))
    fun s4 u4 => ?_
  refine wp_addi (by decide) (by decide) fun s5 u5 => wp_subi (by decide) (by decide) fun s6 u6 => WP.block_nil ?_
  have hg4 : s4.gpr = s.gpr := by rw [u4.gpr, u3.gpr, u2.gpr, u1.gpr]
  have hm6 : s6.mem = (((s.mem.writeW (b + BitVec.ofNat 64 (TAB + (4 * j + 0))) (BitVec.ofNat 8 0)).writeW
      (b + BitVec.ofNat 64 (TAB + (4 * j + 1))) (BitVec.ofNat 8 0)).writeW
      (b + BitVec.ofNat 64 (TAB + (4 * j + 2))) (BitVec.ofNat 8 0)).writeW
      (b + BitVec.ofNat 64 (TAB + (4 * j + 3))) (BitVec.ofNat 8 1) := by
    rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, u3.gpr, u2.gpr, u1.gpr, e7, e8, setWidth8_ofNat (by decide),
      setWidth8_ofNat (by decide)]
  have r11' : s6.gpr .r11 = BitVec.ofNat 64 (458 - (j + 1)) := by
    rw [u6.gpr, u5.other _ (by decide), hg4, h.r11, ofNat_sub_one (by omega_arith) (by omega_arith)]; congr 1
  have hr6 : Rest [.r9, .r11] s s6 := ((u1.rest _).trans ((u2.rest _).trans ((u3.rest _).trans (u4.rest _)))).trans
    ((u5.rest (by decide)).trans (u6.rest (by decide)))
  refine ⟨⟨h.rest.trans hr6, ?_, r11', ?_, fun h' hh => ?_⟩, by rw [r11', ofNat_ne_zero (by omega_arith)]⟩
  · rw [u6.other _ (by decide), u5.gpr, hg4, h.r9, Offset.add_add, Nat.mul_succ]
  · rw [hm6]
    refine ((((h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_arith)⟩).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (Nat.le_add_right _ _) (by omega_arith) (by omega_arith))).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (Nat.le_add_right _ _) (by omega_arith) (by omega_arith))).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (Nat.le_add_right _ _) (by omega_arith) (by omega_arith))).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (Nat.le_add_right _ _) (by omega_arith) (by omega_arith))
  · rw [hm6]
    simp only [VG.WriteBytes.writeW8_apply]
    have ne : ∀ i < 4, h' ≠ 4 * j + i → b + BitVec.ofNat 64 (TAB + h') ≠ b + BitVec.ofNat 64 (TAB + (4 * j + i)) :=
      fun i _ hne => Offset.add_ofNat_ne _ (by omega_arith) (by omega_arith) (by omega_arith)
    rcases Nat.lt_or_ge h' (4 * j) with hl | hl
    · rw [iteF (ne 3 (by decide) (by omega_arith)), iteF (ne 2 (by decide) (by omega_arith)), iteF (ne 1 (by decide) (by omega_arith)),
        iteF (ne 0 (by decide) (by omega_arith))]
      exact h.vals h' hl
    · rcases (by omega_arith : h' = 4 * j + 0 ∨ h' = 4 * j + 1 ∨ h' = 4 * j + 2 ∨ h' = 4 * j + 3) with e | e | e | e <;>
        subst e
      · rw [iteF (ne 3 (by decide) (by omega_arith)), iteF (ne 2 (by decide) (by omega_arith)),
          iteF (ne 1 (by decide) (by omega_arith)), iteT rfl, ite_eq_right (by omega_arith)]
      · rw [iteF (ne 3 (by decide) (by omega_arith)), iteF (ne 2 (by decide) (by omega_arith)), iteT rfl, ite_eq_right (by omega_arith)]
      · rw [iteF (ne 3 (by decide) (by omega_arith)), iteT rfl, ite_eq_right (by omega_arith)]
      · rw [iteT rfl, ite_eq_left (by omega_arith)]

theorem tabFill_ok {s : State} (hc : VCtx b s) :
    WP isa tabFill s fun t => VCtx b t ∧ Rest [.r7, .r8, .r9, .r11] s t ∧
      Frame [⟨b + BitVec.ofNat 64 TAB, 1832⟩] s.mem t.mem ∧ TabIs b t.mem fill0 := by
  have hT : TAB = 1064 := rfl
  unfold tabFill
  refine WP.seq (wp_addi (by decide) (by decide) fun s1 u1 => wp_li (by decide) fun s2 u2 =>
    wp_li (by decide) fun s3 u3 => wp_li (by decide) fun s4 u4 => WP.block_nil ?_)
  have hr4 : Rest [.r7, .r8, .r9, .r11] s s4 := (u1.rest (by decide)).trans ((u2.rest (by decide)).trans
    ((u3.rest (by decide)).trans (u4.rest (by decide))))
  have hm4 : s4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
  have hc4 : VCtx b s4 := hc.of_rest hr4 (by decide) (by decide)
  have h0 : FInv b s4 0 s4 := ⟨Rest.refl _ _, by
      rw [u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.gpr, hc.ctx.r6],
    by rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr], Frame.refl _ _, fun h hh => absurd hh (by omega_arith)⟩
  have h7 : s4.gpr .r7 = BitVec.ofNat 64 0 := by rw [u4.other _ (by decide), u3.gpr]
  have h8 : s4.gpr .r8 = BitVec.ofNat 64 1 := by rw [u4.gpr]
  refine WP.seq (WP.mono (Q := FInv b s4 458) (WP.loop (M := isa)
    (fun m s' => ∃ j, m = 458 - j ∧ j < 458 ∧ FInv b s4 j s') ?_ 458 s4 ⟨0, rfl, by decide, h0⟩) fun s5 h5 => ?_)
  · rintro m s' ⟨j, rfl, hj, hf⟩
    refine WP.mono (fillStep_ok hc4 h7 h8 hj hf) fun s'' ⟨hf', hz⟩ => ?_
    by_cases h458 : j + 1 = 458
    · exact .inl ⟨by rw [eval_nonzero, hz]; simp [h458], by rw [h458] at hf'; exact hf'⟩
    · exact .inr ⟨by rw [eval_nonzero, hz]; simp; omega_arith, 458 - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, hf'⟩
  have hc5 : VCtx b s5 := hc4.of_rest h5.rest (by decide) (by decide)
  refine wp_stb (a := b + BitVec.ofNat 64 (TAB + 8)) (by decide) (by decide) (by rw [hc5.ctx.r6])
    (hc5.inW (by omega_arith)) fun t ut => WP.block_nil ?_
  have hmt : t.mem = s5.mem.writeW (b + BitVec.ofNat 64 (TAB + 8)) (BitVec.ofNat 8 1) := by
    rw [ut.mem, h5.rest.gpr _ (by decide), h8, setWidth8_ofNat (by decide)]
  have hrt : Rest [.r7, .r8, .r9, .r11] s t := hr4.trans ((h5.rest.mono (by decide)).trans (ut.rest _))
  refine ⟨hc.of_rest hrt (by decide) (by decide), hrt, ?_, fun h hh => ?_⟩
  · rw [hmt, ← hm4]
    exact (h5.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_arith)⟩).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (Nat.le_add_right _ _) (by omega_arith) (by omega_arith))
  · rw [hmt, VG.WriteBytes.writeW8_apply, fill0]
    by_cases e : h = 8
    · subst e; rw [iteT rfl, ite_eq_left (.inr rfl)]
    · rw [iteF (Offset.add_ofNat_ne _ (by omega_arith) (by omega_arith) (by omega_arith)), h5.vals h (by omega_arith)]
      congr 1
      by_cases e3 : h % 4 = 3
      · rw [ite_eq_left e3, ite_eq_left (.inl e3)]
      · rw [ite_eq_right e3, ite_eq_right (by omega_arith)]

/-- The table after the bits of the first `i` bytes and `j` bits of byte `i`
at `sc` (in `m0`) into the entries `e`, over `f`. -/
def tabCur (m0 : Mem) (sc : Addr) (e : Nat) (f : Nat → Nat) (i j : Nat) (h : Nat) : Nat :=
  if 8 ≤ h ∧ h % 4 = e ∧ ((h - 8) / 32 < i ∨ (h - 8) / 32 = i ∧ (h - 8) % 32 / 4 < j)
  then rawBit m0 sc ((h - 8) / 4) else f h

/-- While storing the bits of byte `i`, from `s1` (with the byte in `r7`). -/
structure TJInv (b : Addr) (m0 : Mem) (sc : Addr) (e : Nat) (f : Nat → Nat) (i : Nat) (s1 : State) (j : Nat)
    (s : State) : Prop where
  rest : Rest [.r8] s1 s
  frame : Frame [⟨b + BitVec.ofNat 64 TAB, 1832⟩] s1.mem s.mem
  tab : TabIs b s.mem (tabCur m0 sc e f i j)

theorem tabStep_ok {m0 : Mem} {sc : Addr} {e : Nat} (he : e < 4) {f : Nat → Nat} {i j : Nat} (hi : i < 57)
    (hj : j < 8) {s1 s : State} (hc : VCtx b s1) (h7 : (s1.gpr .r7).toNat = (m0 (sc + BitVec.ofNat 64 i)).toNat)
    (h9 : s1.gpr .r9 = b + BitVec.ofNat 64 (32 * i)) (h : TJInv b m0 sc e f i s1 j s) :
    WP isa (.block [.lsl .r8 .r7 (63 - j), .lsr .d .r8 .r8 63, .stb .r8 .r9 (TAB + 8 + 4 * j + e)]) s
      (TJInv b m0 sc e f i s1 (j + 1)) := by
  have hT : TAB = 1064 := rfl
  have e7 : (s.gpr .r7).toNat = (m0 (sc + BitVec.ofNat 64 i)).toNat := by rw [h.rest.gpr _ (by decide), h7]
  have e9 : s.gpr .r9 = b + BitVec.ofNat 64 (32 * i) := by rw [h.rest.gpr _ (by decide), h9]
  have hcs : VCtx b s := hc.of_rest h.rest (by decide) (by decide)
  refine wp_lsl (by omega_arith) fun s2 u2 => wp_lsr (by decide) fun s3 u3 => ?_
  have e8 : (s3.gpr .r8).toNat = ((m0 (sc + BitVec.ofNat 64 i)).toNat >>> j) &&& 1 := by
    rw [u3.gpr, u2.gpr, bit_shift _ (by omega_arith), e7]
  refine wp_stb (a := b + BitVec.ofNat 64 (TAB + (8 + 32 * i + 4 * j + e))) (by decide) (by omega_arith)
    (by rw [u3.other _ (by decide), u2.other _ (by decide), e9, Offset.add_add]; congr 2; omega_arith)
    (by rw [u3.wr, u2.wr]; exact hcs.inW (by omega_arith)) fun s4 u4 => WP.block_nil ⟨?_, ?_, fun h' hh => ?_⟩
  · exact h.rest.trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans (u4.rest _)))
  · rw [u4.mem, u3.mem, u2.mem]
    exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
  · rw [u4.mem, VG.WriteBytes.writeW8_apply, u3.mem, u2.mem]
    by_cases e0 : h' = 8 + 32 * i + 4 * j + e
    · subst e0
      rw [iteT rfl, stb_byte e8, tabCur, ite_eq_left (by omega_arith), rawBit,
        show (8 + 32 * i + 4 * j + e - 8) / 4 / 8 = i by omega_arith, show (8 + 32 * i + 4 * j + e - 8) / 4 % 8 = j by omega_arith]
    · rw [iteF (Offset.add_ofNat_ne _ (by omega_arith) (by omega_arith) (by omega_arith)), h.tab h' hh]
      congr 1
      unfold tabCur
      by_cases c : 8 ≤ h' ∧ h' % 4 = e ∧ ((h' - 8) / 32 < i ∨ (h' - 8) / 32 = i ∧ (h' - 8) % 32 / 4 < j)
      · rw [ite_eq_left c, ite_eq_left (by omega_arith)]
      · rw [ite_eq_right c, ite_eq_right (by omega_arith)]

/-- The loop invariant of `tabBits` from `s0`, before byte `i`. -/
structure TInv (b : Addr) (sc : Addr) (e : Nat) (f : Nat → Nat) (s0 : State) (i : Nat) (s : State) : Prop where
  ctx : VCtx b s
  rest : Rest [.r4, .r7, .r8, .r9, .r11] s0 s
  r4 : s.gpr .r4 = sc + BitVec.ofNat 64 i
  r9 : s.gpr .r9 = b + BitVec.ofNat 64 (32 * i)
  r11 : s.gpr .r11 = BitVec.ofNat 64 (57 - i)
  frame : Frame [⟨b + BitVec.ofNat 64 TAB, 1832⟩] s0.mem s.mem
  tab : TabIs b s.mem (tabCur s0.mem sc e f i 0)

theorem tabBody_ok {src e : Nat} (hsrc : 2896 ≤ src) (hsrc' : src + 57 ≤ 4096) (he : e < 4) {f : Nat → Nat}
    {s0 : State} {i : Nat} (hi : i < 57) {s : State} (h : TInv b (b + BitVec.ofNat 64 src) e f s0 i s) :
    WP isa (.block (tabBody e)) s fun s' => TInv b (b + BitVec.ofNat 64 src) e f s0 (i + 1) s' ∧
      (s'.gpr .r11 != 0) = decide (57 - (i + 1) ≠ 0) := by
  have hT : TAB = 1064 := rfl
  unfold tabBody
  simp only [List.cons_append, List.nil_append]
  refine wp_lbz (a := b + BitVec.ofNat 64 (src + i)) (by decide) (by decide)
    (by rw [h.r4, BitVec.add_zero, Offset.add_add]) (h.ctx.inR (by omega_arith)) fun s1 u1 => ?_
  have hc1 : VCtx b s1 := h.ctx.of_rest (u1.rest (ws := [.r7]) (by decide)) (by decide) (by decide)
  have hx : (s1.gpr .r7).toNat = (s0.mem (b + BitVec.ofNat 64 src + BitVec.ofNat 64 i)).toNat := by
    rw [u1.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide)), Offset.add_add]
    congr 1
    refine h.frame _ fun r hr hcon => ?_
    rw [List.mem_singleton.mp hr] at hcon
    exact Offset.disjoint b (d := src + i) (n := 1) (e := TAB) (k := 1832) (by omega_arith) (by omega_arith) (by omega_arith) _
      (Region.contains_self _ _) hcon
  refine WP.append (wp_range_flatMap (M := isa) (TJInv b s0.mem (b + BitVec.ofNat 64 src) e f i s1)
    (fun j s' hj h' => tabStep_ok he hi hj hc1 hx (by rw [u1.other _ (by decide), h.r9]) h') 8 (Nat.le_refl _) s1
    ⟨Rest.refl _ _, Frame.refl _ _, fun h' hh => by rw [u1.mem]; exact h.tab h' hh⟩) fun s2 h2 => ?_
  refine wp_addi (by decide) (by decide) fun s3 u3 => wp_addi (by decide) (by decide) fun s4 u4 =>
    wp_subi (by decide) (by decide) fun s5 u5 => WP.block_nil ?_
  have hr5 : Rest [.r4, .r7, .r8, .r9, .r11] s s5 :=
    (u1.rest (by decide)).trans ((h2.rest.mono (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans (u5.rest (by decide)))))
  have hm5 : s5.mem = s2.mem := by rw [u5.mem, u4.mem, u3.mem]
  have r11' : s5.gpr .r11 = BitVec.ofNat 64 (57 - (i + 1)) := by
    rw [u5.gpr, u4.other _ (by decide), u3.other _ (by decide), h2.rest.gpr _ (by decide),
      u1.other _ (by decide), h.r11, ofNat_sub_one (by omega_arith) (by omega_arith), Nat.sub_sub]
  refine ⟨⟨h.ctx.of_rest hr5 (by decide) (by decide), h.rest.trans hr5, ?_, ?_, r11', ?_, fun h' hh => ?_⟩, ?_⟩
  · rw [u5.other _ (by decide), u4.other _ (by decide), u3.gpr, h2.rest.gpr _ (by decide),
      u1.other _ (by decide), h.r4, Offset.add_add]
  · rw [u5.other _ (by decide), u4.gpr, u3.other _ (by decide), h2.rest.gpr _ (by decide),
      u1.other _ (by decide), h.r9, Offset.add_add, Nat.mul_succ]
  · rw [hm5]
    exact h.frame.trans (by rw [← u1.mem]; exact h2.frame)
  · rw [hm5, h2.tab h' hh]
    congr 1
    unfold tabCur
    by_cases c : 8 ≤ h' ∧ h' % 4 = e ∧ ((h' - 8) / 32 < i ∨ (h' - 8) / 32 = i ∧ (h' - 8) % 32 / 4 < 8)
    · rw [ite_eq_left c, ite_eq_left (by omega_arith)]
    · rw [ite_eq_right c, ite_eq_right (by omega_arith)]
  · rw [r11', ofNat_ne_zero (by omega_arith)]

theorem tabBits_ok {s : State} (hc : VCtx b s) {src e : Nat} (hsrc : 2896 ≤ src) (hsrc' : src + 57 ≤ 4096)
    (he : e < 4) {f : Nat → Nat} (hf : TabIs b s.mem f) :
    WP isa (tabBits src e) s fun t => VCtx b t ∧ Rest [.r4, .r7, .r8, .r9, .r11] s t ∧
      Frame [⟨b + BitVec.ofNat 64 TAB, 1832⟩] s.mem t.mem ∧
      TabIs b t.mem (tabSet e (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (b + BitVec.ofNat 64 src) 57)) f) := by
  have hT : TAB = 1064 := rfl
  unfold tabBits
  refine WP.seq (wp_addi (by decide) (by decide) fun s1 u1 => wp_addi (by decide) (by omega_arith) fun s2 u2 =>
    wp_li (by decide) fun s3 u3 => WP.block_nil ?_)
  have hr3 : Rest [.r4, .r9, .r11] s s3 := (u1.rest (by decide)).trans ((u2.rest (by decide)).trans
    (u3.rest (by decide)))
  have hm3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  have h0 : TInv b (b + BitVec.ofNat 64 src) e f s3 0 s3 :=
    ⟨hc.of_rest hr3 (by decide) (by decide), Rest.refl _ _,
      by rw [u3.other _ (by decide), u2.gpr, u1.other _ (by decide), hc.ctx.r6, BitVec.add_zero],
      by rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr, hc.ctx.r6],
      by rw [u3.gpr], Frame.refl _ _, fun h' hh => by
        rw [hm3, hf h' hh]; congr 1; unfold tabCur; rw [ite_eq_right (by omega_arith)]⟩
  refine WP.mono (Q := TInv b (b + BitVec.ofNat 64 src) e f s3 57) (WP.loop (M := isa)
    (fun m s' => ∃ i, m = 57 - i ∧ i < 57 ∧ TInv b (b + BitVec.ofNat 64 src) e f s3 i s') ?_ 57 s3
      ⟨0, rfl, by decide, h0⟩) fun t ht => ⟨ht.ctx, (hr3.mono (by decide)).trans ht.rest, by
        rw [← hm3]; exact ht.frame, fun h' hh => ?_⟩
  · rintro m s' ⟨i, rfl, hi, hb⟩
    refine WP.mono (tabBody_ok hsrc hsrc' he hi hb) fun s'' ⟨hb', hz⟩ => ?_
    by_cases h57 : i + 1 = 57
    · exact .inl ⟨by rw [eval_nonzero, hz]; simp [h57], by rw [h57] at hb'; exact hb'⟩
    · exact .inr ⟨by rw [eval_nonzero, hz]; simp; omega_arith, 57 - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, hb'⟩
  · rw [ht.tab h' hh]
    congr 1
    unfold tabCur tabSet
    by_cases c : 8 ≤ h' ∧ h' % 4 = e
    · rw [ite_eq_left (by omega_arith), ite_eq_left c, hm3, rawBit, Proof.Ed448.scalar_bit s.mem _ (by omega_arith)]
    · rw [ite_eq_right (by omega_arith), ite_eq_right c]

end

end VG.Proof.Ed448.PPC64LE
