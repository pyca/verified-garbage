module

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.ContextMath
import VerifiedGarbage.Proof.Mont.X86.ExponentShift
import VerifiedGarbage.Proof.Mont.X86.PowerInit
import VerifiedGarbage.Proof.Dsa.Arithmetic
public import VerifiedGarbage.Proof.Mont.X86.ContextInit
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Impl.Dsa.X86.Pow
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
import VerifiedGarbage.Proof.Mont.X86.ExponentMask
import VerifiedGarbage.Proof.Mont.X86.ShiftDown
public import VerifiedGarbage.Proof.Mont.X86.ArgWs
public import VerifiedGarbage.Proof.Mont.X86.ContextFrame
public import VerifiedGarbage.Proof.Bignum.X86.RtCall
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Callee
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Mont.X86.Context
public import VerifiedGarbage.Proof.Mont.X86.OutsZ

/-! ### `Dsa.X86.PowSteps`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86.PowMul`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86.PowOuts`, which this module and modules that import it used -/

section

/-! # Memory that changes in given ranges and in the stack of a call

`OutsS base sp rs m m'`: `m'` agrees with `m` but on the ranges `rs` of
offsets from `base` and on the 96 bytes below `sp`, which a call of
`vg_rsa_mont_mul_at` uses (a frame of 36 bytes of arguments, the return
address and the callee's 56). The working space lies apart from those bytes
(`CallRoom`), so its numbers keep their values (`OutsS.val32`), and so does a
context (`Context.outsS_keep`).
-/

@[expose] public section

namespace VG.Proof.Dsa.X86.Pow

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Dynamic

/-- `m'` agrees with `m` but on the ranges `rs` of offsets from `base` and on
the 96 bytes below `sp`, which a call of `vg_rsa_mont_mul_at` uses. -/
def OutsS (base : Addr) (sp : BitVec 32) (rs : List (Nat × Nat)) (m m' : Mem) : Prop :=
  ∀ x, (∀ r ∈ rs, ofs base x < r.1 ∨ r.1 + r.2 ≤ ofs base x) → ¬ (below sp 96).Contains x 1 → m' x = m x

namespace OutsS

variable {base : Addr} {sp : BitVec 32} {rs rs' : List (Nat × Nat)} {m₁ m₂ m₃ : Mem}

theorem trans (h₁ : OutsS base sp rs m₁ m₂) (h₂ : OutsS base sp rs m₂ m₃) : OutsS base sp rs m₁ m₃ :=
  fun x hx hz => (h₂ x hx hz).trans (h₁ x hx hz)

theorem of_outs (h : Outs base rs m₁ m₂) : OutsS base sp rs m₁ m₂ := fun x hx _ => h x hx

/-- Changes within some ranges, as changes within ranges covering them. -/
theorem widen (h : OutsS base sp rs m₁ m₂)
    (hr : ∀ y : Nat, (∀ r ∈ rs', y < r.1 ∨ r.1 + r.2 ≤ y) → ∀ r ∈ rs, y < r.1 ∨ r.1 + r.2 ≤ y) :
    OutsS base sp rs' m₁ m₂ :=
  fun x hx hz => h x (hr _ hx) hz

/-- The stack a call uses is past the working space. -/
theorem zone_ofs {size : Nat} (R : CallRoom sp base size) {x : Addr} (hx : (below sp 96).Contains x 1) :
    size ≤ ofs base x := by
  have h96 := R.low
  have hsp := sp.isLt
  by_contra hc
  have hcx : (⟨base, size⟩ : Region).Contains x 1 := by
    simp only [Region.Contains, ofs] at hc ⊢; omega
  exact R.apart x hx hcx

/-- A number in the working space keeps its value. -/
theorem val32 {m m' : Mem} {size : Nat} (h : OutsS base sp rs m m') (R : CallRoom sp base size)
    (hn : base.toNat + size ≤ 2 ^ 32) {d k : Nat} (hd : ∀ r ∈ rs, d + 4 * k ≤ r.1 ∨ r.1 + r.2 ≤ d)
    (hs : d + 4 * k ≤ size) : VG.Proof.Mont.val32 m' base d k = VG.Proof.Mont.val32 m base d k :=
  val32_congr fun j hj => congrArg BitVec.toNat (Mem.readW_congr fun i hi => h _ (fun r hr => by
    have := hd r hr
    rw [ofs_off base (by omega_using [hn, hs, hj, hi])]; omega_using [hj, hi, this]) fun hz => by
      have := zone_ofs R hz
      rw [ofs_off base (by omega_using [hn, hs, hj, hi])] at this; omega_using [hs, hj, hi, this])

theorem wordsVal {m m' : Mem} {size : Nat} (h : OutsS base sp rs m m') (R : CallRoom sp base size)
    (hn : base.toNat + size ≤ 2 ^ 32) {d k : Nat} (hd : ∀ r ∈ rs, d + 8 * k ≤ r.1 ∨ r.1 + r.2 ≤ d)
    (hs : d + 8 * k ≤ size) : VG.Proof.Mont.wordsVal m' base d k = VG.Proof.Mont.wordsVal m base d k := by
  rw [wordsVal_eq_val32, wordsVal_eq_val32]
  exact h.val32 R hn (fun r hr => by have := hd r hr; omega_using [this]) (by omega_using [hs])

theorem readW32 {m m' : Mem} {size : Nat} (h : OutsS base sp rs m m') (R : CallRoom sp base size)
    (hn : base.toNat + size ≤ 2 ^ 32) {d : Nat} (hd : ∀ r ∈ rs, d + 4 ≤ r.1 ∨ r.1 + r.2 ≤ d)
    (hs : d + 4 ≤ size) : m'.readW (off base d) 32 = m.readW (off base d) 32 :=
  Mem.readW_congr fun i hi => h _ (fun r hr => by
    have := hd r hr
    rw [ofs_off base (by omega_using [hn, hs, hi])]; omega_using [hi, this]) fun hz => by
      have := zone_ofs R hz
      rw [ofs_off base (by omega_using [hn, hs, hi])] at this; omega_using [hs, hi, this]

end OutsS

/-- Preserve the arithmetic context across writes to ranges apart from its
modulus and inverse, and to the stack below `esp`. -/
theorem Context.outsS_keep {n size m : Nat} {base : Addr} {s t : State}
    (h : Context n m base size s) (R : CallRoom (s.gpr .esp) base size) {regs : List Reg}
    {ranges : List (Nat × Nat)} (K : Keeps regs s t) (hdi : .edi ∉ regs) (hsp : .esp ∉ regs)
    (O : OutsS base (s.gpr .esp) ranges s.mem t.mem)
    (hm : ∀ r ∈ ranges, slot n 0 + 8 * n ≤ r.1 ∨ r.1 + r.2 ≤ slot n 0)
    (hi : ∀ r ∈ ranges, 4 ≤ r.1) : Context n m base size t := by
  have nw := h.scr.nowrap
  refine ⟨h.scr.of_keeps K hdi hsp, h.size_le, ?_, h.gt_one, ?_⟩
  · refine ⟨h.modulus.n0, h.modulus.mo, h.modulus.tmp, h.modulus.sep, ?_⟩
    change VG.Proof.Mont.wordsVal t.mem base (slot n 0) n = m
    rw [O.wordsVal R nw (fun r hr => by have := hm r hr; omega_using [this])
      (by have := h.modulus.mo; change slot n 0 + 8 * n ≤ size at this; omega_using [this])]
    exact h.modulus.val
  · have same := O.val32 R nw (d := 0) (k := 1) (fun r hr => Or.inl (by have := hi r hr; omega_using [this]))
      (by have := h.size_le; have := slot_header n 9; simp only [contextBytes] at *; omega_arith)
    have word : w32 t.mem base 0 = w32 s.mem base 0 := by
      simpa only [VG.Proof.Mont.val32, Nat.mul_zero, Nat.add_zero] using same
    rw [word]; exact h.inverse

end VG.Proof.Dsa.X86.Pow

end

end

/-! # A multiplication of DSA's exponentiation, by a call

`mul n o a b` (`Impl/Dsa/X86/Pow.lean`) stores the arguments of
`vg_rsa_mont_mul_at` for slots `o`, `a` and `b` of the context into a frame
of 36 bytes below `esp` (`mulArgs_ok`), and calls it on the context's bytes
alone. From a context (`Context`) whose 96 bytes of stack below `esp` lie
apart from the working space (`CallRoom`), it writes the Montgomery product of
slots `a` and `b` into slot `o`, changing only it, the callee's range (slots 1
to 3) and those 96 bytes of stack (`mul_ok`, as `OutsS`).
-/

@[expose] public section

namespace VG.Proof.Dsa.X86.Pow

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Dynamic VG.Impl.Dsa.X86.Pow
open VG.Proof.Rsa.MontMul (scratchBytes)

/-! ## The arguments -/

section
variable {P : Addr}

theorem immStores_ok (vs : List Nat) : ∀ (d : Nat) (f : State), (f.gpr .esp).setWidth 64 = P →
    (f.gpr .esp).toNat + 36 ≤ 2 ^ 32 → (⟨P, 36⟩ : Region) ∈ f.wr → d + 4 * vs.length ≤ 36 →
    ∀ {is : List Instr} {Q : State → Prop},
    (∀ g, Keeps [.eax] f g → Frame [⟨P, 36⟩] f.mem g.mem →
      (∀ j, j + 4 ≤ d → g.mem.readW (P + BitVec.ofNat 64 j) 32 = f.mem.readW (P + BitVec.ofNat 64 j) 32) →
      (∀ i (hi : i < vs.length), g.mem.readW (P + BitVec.ofNat 64 (d + 4 * i)) 32 = BitVec.ofNat 32 vs[i]) →
      WP isa (.block is) g Q) →
    WP isa (.block (immStores vs d ++ is)) f Q := by
  induction vs with
  | nil =>
    intro d f _ _ _ _ is Q k
    exact k f (Keeps.refl _ _) (Frame.refl _ _) (fun _ _ => rfl) (fun i hi => absurd hi (by simp))
  | cons v vs ih =>
    intro d f hP hesp hfr hd is Q k
    simp only [immStores, List.cons_append, List.length_cons] at hd ⊢
    refine wp_movS rfl fun f₁ u₁ _ => ?_
    obtain ⟨a₁, w₁⟩ := VG.Proof.Bignum.X86.PublicRt.frame_store (t := f₁) (P := P) (k := d)
      (by rw [u₁.other _ (by decide)]; exact hP) (by rw [u₁.other _ (by decide)]; exact hesp)
      (by rw [u₁.wr]; exact hfr) (by omega_arith)
    refine wp_storeS a₁ w₁ fun f₂ m₂ => ?_
    have K₂ : Keeps [.eax] f f₂ := u₁.keeps.trans (m₂.keeps _)
    refine ih (d + 4) f₂ (by rw [K₂.1 _ (by decide)]; exact hP) (by rw [K₂.1 _ (by decide)]; exact hesp)
      (by rw [K₂.2.2]; exact hfr) (by omega_arith) fun g K F L R => k g (K₂.trans K) ?_ ?_ ?_
    · have F₂ : Frame [⟨P, 36⟩] f.mem f₂.mem := by
        rw [m₂.mem, u₁.mem]
        exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
          (Offset.contains_base P (by omega_arith) (by omega_arith))
      exact F₂.trans F
    · intro j hj
      rw [L j (by omega_arith), m₂.mem, u₁.mem]
      exact Mem.readW_writeW_sep (Offset.sep P (Or.inl hj) (by omega_arith) (by omega_arith)) (by decide)
    · intro i hi
      cases i with
      | zero =>
        rw [Nat.mul_zero, Nat.add_zero, L d (by omega_arith), m₂.mem, u₁.gpr, Mem.readW_writeW_self32]
        rfl
      | succ i =>
        have := R i (by simpa using hi)
        rw [show d + 4 * (i + 1) = d + 4 + 4 * i by omega_arith, this]
        rfl

end

theorem contextBytes_div (n : Nat) : contextBytes n / 8 * 8 = contextBytes n := by
  simp only [contextBytes, slot, stride]; omega_arith

/-- The callee's offsets for slots `o`, `a` and `b` (4 to 7) of a context. -/
theorem offs {n o a b : Nat} (hn : 2 ≤ n) (ho : 4 ≤ o) (ho7 : o ≤ 7) (ha : 4 ≤ a) (ha7 : a ≤ 7)
    (hb : 4 ≤ b) (hb7 : b ≤ 7) :
    VG.Proof.Bignum.X86.RtCall.Offs (contextBytes n) n (slot n 0) 0 (calleeScratch n) (slot n o)
      (slot n a) (slot n b) := by
  have so := Nat.mul_le_mul_right (stride n) ho
  have so7 := Nat.mul_le_mul_right (stride n) ho7
  have sa := Nat.mul_le_mul_right (stride n) ha
  have sa7 := Nat.mul_le_mul_right (stride n) ha7
  have sb := Nat.mul_le_mul_right (stride n) hb
  have sb7 := Nat.mul_le_mul_right (stride n) hb7
  simp only [stride] at so so7 sa sa7 sb sb7
  refine ⟨by omega_arith, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [contextBytes, calleeScratch, slot, stride, scratchBytes, VG.Proof.Rsa.MontMul.Apart] <;> omega_arith

theorem mulBody_noSp (n o a b : Nat) :
    NoSp (.seq (.block (mulArgs n o a b)) (.call "vg_rsa_mont_mul_at" Sse2.atBody) : Prog isa) := by
  apply NoSp.of_all
  rw [Code.allInstrs_eq]
  simp only [instrs, mulArgs, immStores, List.all_append, List.all_cons, List.all_nil]
  rw [← Code.allInstrs_eq, VG.Proof.Mont.X86.Sse2.atBody_allNoSp]
  rfl

theorem mul_allNoSp (n o a b : Nat) :
    (VG.Impl.Dsa.X86.Pow.mul n o a b).allInstrs (fun i => !VG.X86.Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq]
  simp only [VG.Impl.Dsa.X86.Pow.mul, instrs, mulArgs, immStores, List.all_append, List.all_cons, List.all_nil]
  rw [← Code.allInstrs_eq, VG.Proof.Mont.X86.Sse2.atBody_allNoSp]
  rfl

theorem mul_noSp (n o a b : Nat) : NoSp (VG.Impl.Dsa.X86.Pow.mul n o a b) := NoSp.of_all (mul_allNoSp n o a b)

theorem mul_stackUse (n o a b : Nat) : stackUse (VG.Impl.Dsa.X86.Pow.mul n o a b) = 96 := by
  simp only [VG.Impl.Dsa.X86.Pow.mul, stackUse, VG.Proof.Mont.X86.Sse2.atBody_stack]
  rfl

/-- A range of offsets past which `x` lies is apart from it. -/
theorem not_contains_of_ofs {base x : Addr} {d k : Nat} (hd : base.toNat + d + k ≤ 2 ^ 64)
    (h : ofs base x < d ∨ d + k ≤ ofs base x) : ¬ (⟨off base d, k⟩ : Region).Contains x 1 := by
  simp only [Region.Contains, off, ofs] at *
  bv_omega

/-- The arguments' block: `ws` and the eight numbers into the frame at `esp`. -/
theorem mulArgs_ok {f : State} {n o a b : Nat} (hesp : (f.gpr .esp).toNat + 36 ≤ 2 ^ 32)
    (hfr : (⟨(f.gpr .esp).setWidth 64, 36⟩ : Region) ∈ f.wr) :
    WP isa (.block (mulArgs n o a b)) f fun g =>
      Keeps [.eax, .edx] f g ∧ Frame [⟨(f.gpr .esp).setWidth 64, 36⟩] f.mem g.mem ∧
      ∀ i < 9, g.mem.readW ((f.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 * i)) 32 =
        VG.Proof.Bignum.X86.RtCall.callArg (f.gpr .edi) (BitVec.ofNat 32 (contextBytes n / 8)) n (slot n 0) 0
          (calleeScratch n) (slot n o) (slot n a) (slot n b) i := by
  obtain ⟨a₀, w₀⟩ := VG.Proof.Bignum.X86.PublicRt.frame_store (t := f) (k := 0) rfl hesp hfr (by decide)
  unfold mulArgs
  refine wp_storeS a₀ w₀ fun f₁ m₁ => ?_
  rw [← List.append_nil (immStores _ 4)]
  refine immStores_ok (P := (f.gpr .esp).setWidth 64) _ 4 f₁ (by rw [m₁.gpr]) (by rw [m₁.gpr]; exact hesp) (by rw [m₁.wr]; exact hfr)
    (by simp) fun g K F L R => WP.block_nil ?_
  have K₁ : Keeps [.eax] f f₁ := m₁.keeps _
  refine ⟨(K₁.trans K).mono (by decide), ?_, ?_⟩
  · have F₁ : Frame [⟨(f.gpr .esp).setWidth 64, 36⟩] f.mem f₁.mem := by
      rw [m₁.mem]
      exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
        (Offset.contains_base _ (d := 0) (by decide) (by decide))
    exact F₁.trans F
  · intro i hi
    match i, hi with
    | 0, _ =>
      rw [Nat.mul_zero, L 0 (by decide), m₁.mem, Mem.readW_writeW_self32]
      rfl
    | i + 1, hi =>
      rw [show 4 * (i + 1) = 4 + 4 * i by omega_arith, R i (by simp; omega_arith)]
      match i with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => rfl

/-- `StkOk` for a working space within another. -/
theorem stkOk_mono {sp : BitVec 32} {base : Addr} {size k : Nat} (h : StkOk sp base size) (hk : k ≤ size) :
    StkOk sp base k := ⟨h.1, h.2.imp id fun h' => by omega_arith⟩

/-- A multiplication of slots of a context, by a call. -/
theorem mul_ok {s : State} {base : Addr} {size n m o a b : Nat}
    (h : Context n m base size s) (R : CallRoom (s.gpr .esp) base size) (hn : 2 ≤ n)
    (ho : 4 ≤ o) (ho7 : o ≤ 7) (ha : 4 ≤ a) (ha7 : a ≤ 7) (hb : 4 ≤ b) (hb7 : b ≤ 7)
    (hB : VG.Proof.Mont.wordsVal s.mem base (slot n b) n < m) :
    WP isa (VG.Impl.Dsa.X86.Pow.mul n o a b) s fun t =>
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      OutsS base (s.gpr .esp) [(slot n o, 8 * n), (calleeScratch n, scratchBytes n)] s.mem t.mem ∧
      VG.Proof.Mont.wordsVal t.mem base (slot n o) n < m ∧
      VG.Proof.Mont.wordsVal t.mem base (slot n o) n * 2 ^ (64 * n) % m =
        VG.Proof.Mont.wordsVal s.mem base (slot n a) n * VG.Proof.Mont.wordsVal s.mem base (slot n b) n % m := by
  have cb := h.size_le
  have nw := h.scr.nowrap
  have low := R.low
  have hsp := (s.gpr .esp).isLt
  have hcov : Covers [⟨base, contextBytes n⟩] s.wr :=
    Covers.of_sub fun r hr => ⟨⟨base, size⟩, h.scr.wr, 0, by
      rw [List.mem_singleton.mp hr]; simp, by rw [List.mem_singleton.mp hr]; simpa using cb⟩
  have hscr : Scr (s.withRegions s.rd [⟨base, contextBytes n⟩]) base (contextBytes n) :=
    ⟨h.scr.edi, List.mem_singleton_self _, by omega_arith, stkOk_mono h.scr.stk cb⟩
  have R' : CallRoom ((s.withRegions s.rd [⟨base, contextBytes n⟩]).gpr .esp) base (contextBytes n) :=
    ⟨low, fun x h₁ h₂ => R.apart x h₁ (by simp only [Region.Contains] at h₂ ⊢; omega_arith)⟩
  have hv : VG.Proof.Mont.wordsVal s.mem base (slot n 0) n = m := h.modulus.val
  have hinv : (VG.Proof.Mont.val32 s.mem base (slot n 0) (2 * n) * w32 s.mem base 0 + 1) % 2 ^ 32 = 0 := by
    rw [← wordsVal_eq_val32, hv]; exact h.inverse
  have hB' : VG.Proof.Mont.val32 s.mem base (slot n b) (2 * n) < VG.Proof.Mont.val32 s.mem base (slot n 0) (2 * n) := by
    rw [← wordsVal_eq_val32, ← wordsVal_eq_val32, hv]; exact hB
  have fEsp := allocFrame_esp 36 (s.withRegions s.rd [⟨base, contextBytes n⟩])
  have l36 : 36 ≤ ((s.withRegions s.rd [⟨base, contextBytes n⟩]).gpr .esp).toNat := by simp; omega_arith
  have hlen : contextBytes n = (BitVec.ofNat 32 (contextBytes n / 8)).toNat * 8 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith), contextBytes_div]
  have C := VG.Proof.Bignum.X86.RtCall.call_ok (is := mulArgs n o a b) hscr hlen R'
    (offs hn ho ho7 ha ha7 hb hb7) hinv hB' (mulBody_noSp n o a b)
    (by
      refine WP.mono (mulArgs_ok (by rw [fEsp, VG.X86.sub_toNat l36]; simp; omega_arith)
        (by rw [allocFrame_wr]; exact List.mem_cons_self ..)) fun g ⟨K, F, Rd⟩ => ⟨K, F, ?_⟩
      rwa [show (allocFrame 36 (s.withRegions s.rd [⟨base, contextBytes n⟩])).gpr .edi =
        (s.withRegions s.rd [⟨base, contextBytes n⟩]).gpr .edi from allocFrame_gpr _ _ (by decide)] at Rd)
  refine WP.narrowSp C (Covers.append (Covers.refl _) hcov) hcov
    (mul_noSp n o a b) (by change stackUse (VG.Impl.Dsa.X86.Pow.mul n o a b) ≤ _; rw [mul_stackUse]; exact low)
    fun t rd wr _ P => ?_
  obtain ⟨cs, rd', wr', F', L, V⟩ := P
  simp only [State.withRegions_gpr, State.withRegions_mem] at cs F' L V
  have hm : VG.Proof.Mont.val32 s.mem base (slot n 0) (2 * n) = m := by
    rw [← wordsVal_eq_val32]; exact h.modulus.val
  rw [hm, ← wordsVal_eq_val32] at L V
  rw [← wordsVal_eq_val32, ← wordsVal_eq_val32] at V
  refine ⟨cs, rd, wr, ?_, L, V⟩
  intro x hx hz
  have so := Nat.mul_le_mul_right (stride n) ho7
  simp only [stride] at so
  refine F' x fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact not_contains_of_ofs (by simp only [contextBytes, slot, stride] at cb ⊢; omega_arith) (hx _ (List.mem_cons_self ..))
  · exact not_contains_of_ofs (by simp only [contextBytes, calleeScratch, slot, stride, scratchBytes] at cb ⊢; omega_arith)
      (hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  · exact hz

end VG.Proof.Dsa.X86.Pow

end

end

/-! # The pieces of DSA's exponentiation, between calls

`St s₀ t`: from the exponentiation's start `s₀`, `t` has the context, the
registers but `powerClob` of `s₀` (`esp` and `edi` among them), and changes
only the context's own bytes (`coreRanges`) and the 96 bytes of stack below
`esp`, which lie apart from the working space. Each piece keeps it, and says
what it writes: a multiplication by a call (`mulSt_ok`), one in a slot
(`oneSt_ok`), the exponent's low bit as a mask (`maskSt_ok`), the masked
selection (`selectSt_ok`) and the exponent's shift (`shiftSt_ok`).
-/

@[expose] public section

namespace VG.Proof.Dsa.X86.Pow

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Dynamic VG.Impl.Dsa.X86.Pow
open VG.Proof.Rsa.MontMul (scratchBytes)

/-- The bytes the exponentiation's core may change: the inverse and the mask
in the header, and every slot but the modulus's. -/
def coreRanges (n : Nat) : List (Nat × Nat) := [(0, 8), (slot n 1, contextBytes n - slot n 1)]

structure St (n m size : Nat) (base : Addr) (s₀ t : State) : Prop where
  ctx : Context n m base size t
  room : CallRoom (s₀.gpr .esp) base size
  keeps : Keeps powerClob s₀ t
  mem : OutsS base (s₀.gpr .esp) (coreRanges n) s₀.mem t.mem

section
variable {n m size : Nat} {base : Addr} {s₀ : State}

theorem St.esp {t : State} (S : St n m size base s₀ t) : t.gpr .esp = s₀.gpr .esp := S.keeps.1 _ (by decide)

theorem St.room' {t : State} (S : St n m size base s₀ t) : CallRoom (t.gpr .esp) base size := by
  rw [S.esp]; exact S.room

/-- Ranges within the core's. -/
theorem OutsS.core {sp : BitVec 32} {rs : List (Nat × Nat)} {m₁ m₂ : Mem}
    (h : OutsS base sp rs m₁ m₂) (hr : ∀ r ∈ rs, ∃ c ∈ coreRanges n, c.1 ≤ r.1 ∧ r.1 + r.2 ≤ c.1 + c.2) :
    OutsS base sp (coreRanges n) m₁ m₂ :=
  h.widen fun y hy r hr' => by
    obtain ⟨c, hc, h₁, h₂⟩ := hr r hr'
    have := hy c hc
    omega_using [h₁, h₂, this]

/-- A state after a piece that keeps the context and changes only ranges within the core's. -/
theorem St.next {t u : State} (S : St n m size base s₀ t) (C : Context n m base size u)
    (K : Keeps powerClob t u) {rs : List (Nat × Nat)} (O : OutsS base (s₀.gpr .esp) rs t.mem u.mem)
    (hr : ∀ r ∈ rs, ∃ c ∈ coreRanges n, c.1 ≤ r.1 ∧ r.1 + r.2 ≤ c.1 + c.2) : St n m size base s₀ u :=
  ⟨C, S.room, S.keeps.trans K, S.mem.trans (O.core hr)⟩

theorem slot_lin (n i : Nat) : slot n i = 64 + i * (16 * n + 8) := rfl

/-- Slot `i` (4 to 8) keeps its value when a call writes slot `o` (4 to 7). -/
theorem mul_slot_keep {sp : BitVec 32} {m₁ m₂ : Mem} {o i k : Nat}
    (O : OutsS base sp [(slot n o, 8 * n), (calleeScratch n, scratchBytes n)] m₁ m₂)
    (R : CallRoom sp base size) (nw : base.toNat + size ≤ 2 ^ 32) (cb : contextBytes n ≤ size) (hn : 2 ≤ n)
    (hi4 : 4 ≤ i) (hi : i < 9) (hio : i ≠ o) (hk : k ≤ 2 * n) :
    val32 m₂ base (slot n i) k = val32 m₁ base (slot n i) k := by
  have sep := slot_sep (n := n) hio
  have b := slot_bound (n := n) hi
  have l4 := Nat.mul_le_mul_right (16 * n + 8) hi4
  simp only [stride] at sep b
  refine O.val32 R nw (fun r hr => ?_) (by omega_using [cb, hk, b])
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · dsimp only; omega_using [hk, sep]
  · simp only [calleeScratch, scratchBytes, slot_lin] at b ⊢; omega_using [hn, l4]

theorem mulSt_ok {t : State} {o a b : Nat} (S : St n m size base s₀ t) (hn : 2 ≤ n)
    (ho : 4 ≤ o) (ho7 : o ≤ 7) (ha : 4 ≤ a) (ha7 : a ≤ 7) (hb : 4 ≤ b) (hb7 : b ≤ 7)
    (hB : wordsVal t.mem base (slot n b) n < m) :
    WP isa (VG.Impl.Dsa.X86.Pow.mul n o a b) t fun u => St n m size base s₀ u ∧ u.gpr .esi = t.gpr .esi ∧
      wordsVal u.mem base (slot n o) n < m ∧
      wordsVal u.mem base (slot n o) n * 2 ^ (64 * n) % m =
        wordsVal t.mem base (slot n a) n * wordsVal t.mem base (slot n b) n % m ∧
      (∀ i, 4 ≤ i → i < 9 → i ≠ o → ∀ k ≤ 2 * n, val32 u.mem base (slot n i) k = val32 t.mem base (slot n i) k) ∧
      u.mem.readW (off base 4) 32 = t.mem.readW (off base 4) 32 := by
  have h := S.ctx
  have cb := h.size_le
  have nw := h.scr.nowrap
  refine WP.mono (mul_ok h S.room' hn ho ho7 ha ha7 hb hb7 hB) fun u ⟨cs, rd, wr, O, L, V⟩ => ?_
  have K : Keeps powerClob t u :=
    ⟨fun r hr => cs r (by revert hr; cases r <;> simp [powerClob, calleeSaved]), rd, wr⟩
  have lo := Nat.mul_le_mul_right (16 * n + 8) ho
  have hi := Nat.mul_le_mul_right (16 * n + 8) ho7
  have C : Context n m base size u := Context.outsS_keep h S.room' K (by decide) (by decide) O
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [calleeScratch, slot_lin] <;> omega_arith)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [calleeScratch, slot_lin] <;> omega_using [])
  rw [S.esp] at O
  refine ⟨S.next C K O fun r hr => ⟨(slot n 1, contextBytes n - slot n 1), List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_⟩,
    cs .esi (by decide), L, V, fun i hi4 hi hio k hk => mul_slot_keep O S.room nw cb hn hi4 hi hio hk,
    O.readW32 S.room nw (fun r hr => ?_) (by simp only [contextBytes, slot_lin] at cb; omega_using [cb])⟩
  rotate_left
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [calleeScratch, slot_lin] <;> omega_using []
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  have b8 := slot_bound (n := n) (i := 8) (by decide)
  simp only [stride] at b8
  rcases hr with rfl | rfl <;> simp only [contextBytes, calleeScratch, scratchBytes, slot_lin] at b8 ⊢ <;> omega_arith

/-- The core's second range holds slots 1 to 8. -/
theorem in_core {i k : Nat} (hi : 1 ≤ i) (hk : slot n i + k ≤ contextBytes n) :
    ∃ c ∈ coreRanges n, c.1 ≤ slot n i ∧ slot n i + k ≤ c.1 + c.2 := by
  have := Nat.mul_le_mul_right (16 * n + 8) hi
  refine ⟨(slot n 1, contextBytes n - slot n 1), List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_, ?_⟩ <;>
    simp only [slot_lin, contextBytes] at * <;> omega_arith

/-- Slot `j` keeps its value outside a write of slot `i`. -/
theorem outside_slot {m₁ m₂ : Mem} {i j k len : Nat} (O : Outside base (slot n i) len m₁ m₂)
    (hlen : len ≤ 16 * n + 8) (hij : j ≠ i) (hj : j < 9) (hk : k ≤ 2 * n) (nw : contextBytes n ≤ 2 ^ 64) :
    val32 m₂ base (slot n j) k = val32 m₁ base (slot n j) k := by
  have sep := slot_sep (n := n) hij
  have b := slot_bound (n := n) hj
  simp only [stride] at sep b
  exact O.val32 (by omega_using [hlen, hk, sep]) (by omega_using [hk, nw, b])

theorem oneSt_ok {t : State} {i : Nat} (S : St n m size base s₀ t) (hi1 : 1 ≤ i) (hi : i < 9) :
    WP isa (VG.Impl.Mont.X86.Dynamic.one n (slot n i)) t fun u => St n m size base s₀ u ∧ u.gpr .esi = t.gpr .esi ∧
      wordsVal u.mem base (slot n i) n = 1 ∧
      ∀ j, j < 9 → j ≠ i → ∀ k ≤ 2 * n, val32 u.mem base (slot n j) k = val32 t.mem base (slot n j) k := by
  have h := S.ctx
  have cb := h.size_le
  have nw := h.scr.nowrap
  have b := slot_bound (n := n) hi
  have n0 : 0 < n := h.modulus.n0
  have s0 := slot_le (n := n) (i := 0) (j := i) (by omega_using [hi1])
  simp only [stride] at b s0
  refine WP.mono (one_ok h.scr n0 (by omega_using [cb, b])) fun u ⟨O, V, K⟩ => ?_
  have C := h.outside_keep K (by decide) (by decide) O (.inl (by omega_using [s0])) (by have := slot_header n i; omega_using [s0])
  refine ⟨S.next C (K.mono (by decide)) (rs := [(slot n i, 8 * n)]) (OutsS.of_outs (Outs.of_outside O (by simp)))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact in_core hi1 (by omega_using [b])), K.1 _ (by decide), V,
    fun j hj hji k hk => outside_slot O (by omega_using []) hji hj hk (by omega_using [cb, nw])⟩

theorem maskSt_ok {t : State} (S : St n m size base s₀ t) :
    WP isa (.block (exponentMask (slot n 8) 4)) t fun u => St n m size base s₀ u ∧ u.gpr .esi = t.gpr .esi ∧
      u.mem.readW (off base 4) 32 = (if w32 t.mem base (slot n 8) % 2 = 1 then BitVec.allOnes 32 else 0) ∧
      ∀ j, j < 9 → ∀ k ≤ 2 * n, val32 u.mem base (slot n j) k = val32 t.mem base (slot n j) k := by
  have h := S.ctx
  have cb := h.size_le
  have nw := h.scr.nowrap
  have b := slot_bound (n := n) (i := 8) (by decide)
  simp only [stride] at b
  refine WP.mono (exponentMask_ok h.scr (by omega_using [cb, b]) (by simp only [contextBytes, slot_lin] at cb; omega_using [cb]))
    fun u ⟨O, V, K⟩ => ?_
  have C := h.outside_keep K (by decide) (by decide) O (.inr (by simp only [slot_lin]; omega_using [])) (by decide)
  refine ⟨S.next C (K.mono (by decide)) (rs := [(4, 4)]) (OutsS.of_outs (Outs.of_outside O (by simp)))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨(0, 8), List.mem_cons_self .., by decide, by decide⟩),
    K.1 _ (by decide), V, fun j hj k hk => ?_⟩
  have := slot_header n j
  have bj := slot_bound (n := n) hj
  simp only [stride] at bj
  exact O.val32 (.inr (by omega_using [this])) (by omega_using [cb, nw, hk, bj])

theorem selectSt_ok {t : State} {bit : Bool} (S : St n m size base s₀ t)
    (hmask : t.mem.readW (off base 4) 32 = if bit then BitVec.allOnes 32 else 0) :
    WP isa (selectProduct (contextMod n) (slot n 6) (slot n 7) 4) t fun u => St n m size base s₀ u ∧ u.gpr .esi = t.gpr .esi ∧
      wordsVal u.mem base (slot n 6) n = wordsVal t.mem base (slot n (if bit then 7 else 6)) n ∧
      ∀ j, j < 9 → j ≠ 6 → ∀ k ≤ 2 * n, val32 u.mem base (slot n j) k = val32 t.mem base (slot n j) k := by
  have h := S.ctx
  have cb := h.size_le
  have nw := h.scr.nowrap
  have n0 : 0 < n := h.modulus.n0
  have b6 := slot_bound (n := n) (i := 6) (by decide)
  have b7 := slot_bound (n := n) (i := 7) (by decide)
  have s67 := slot_le (n := n) (i := 6) (j := 7) (by decide)
  have s06 := slot_le (n := n) (i := 0) (j := 6) (by decide)
  simp only [stride] at b6 b7 s67 s06
  refine WP.mono (selectProduct_ok (M := contextMod n) h.scr
    (by change slot n 6 + 8 * n ≤ size; omega_using [cb, b6]) (by change slot n 7 + 8 * n ≤ size; omega_using [cb, b7])
    (by simp only [contextBytes, slot_lin] at cb; omega_using [cb]) (.inr (.inl (by change slot n 6 + 8 * n ≤ slot n 7; omega_using [s67])))
    bit hmask n0) fun u ⟨O, V, K⟩ => ?_
  change Outside base (slot n 6) (8 * n) t.mem u.mem at O
  have C := h.outside_keep K (by decide) (by decide) O (.inl (by omega_using [s06])) (by have := slot_header n 6; omega_using [s06])
  refine ⟨S.next C (K.mono (by decide)) (rs := [(slot n 6, 8 * n)]) (OutsS.of_outs (Outs.of_outside O (by simp)))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact in_core (by decide) (by omega_using [b6])), K.1 _ (by decide), ?_,
    fun j hj hji k hk => outside_slot O (by omega_using []) hji hj hk (by omega_using [cb, nw])⟩
  change wordsVal u.mem base (slot n 6) n = _ at V
  rw [V]; cases bit <;> rfl

theorem shiftSt_ok {t : State} {e : Nat} (S : St n m size base s₀ t) (he : 2 ≤ e) (hen : e ≤ 2 * n) :
    WP isa (shiftDown e (slot n 8)) t fun u => St n m size base s₀ u ∧ u.gpr .esi = t.gpr .esi ∧
      val32 u.mem base (slot n 8) e = val32 t.mem base (slot n 8) e / 2 ∧
      ∀ j, j < 9 → j ≠ 8 → ∀ k ≤ 2 * n, val32 u.mem base (slot n j) k = val32 t.mem base (slot n j) k := by
  have h := S.ctx
  have cb := h.size_le
  have nw := h.scr.nowrap
  have b8 := slot_bound (n := n) (i := 8) (by decide)
  have s08 := slot_le (n := n) (i := 0) (j := 8) (by decide)
  simp only [stride] at b8 s08
  refine WP.mono (shiftDown_ok h.scr he (by omega_using [hen, cb, b8])) fun u ⟨O, V, K⟩ => ?_
  have C := h.outside_keep K (by decide) (by decide) O (.inl (by omega_using [s08])) (by have := slot_header n 8; omega_using [s08])
  refine ⟨S.next C (K.mono (by decide)) (rs := [(slot n 8, 4 * e)]) (OutsS.of_outs (Outs.of_outside O (by simp)))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact in_core (by decide) (by omega_using [hen, b8])), K.1 _ (by decide), V,
    fun j hj hji k hk => outside_slot O (by omega_using [hen]) hji hj hk (by omega_using [cb, nw])⟩

end

end VG.Proof.Dsa.X86.Pow

end

end

/-! ### `Dsa.X86.PowLoop`, which only this module used -/

section

/-! # The loop of DSA's exponentiation

An iteration (`step`) multiplies the result (slot 6) by the base (slot 5) where
the exponent's (slot 8) low bit is set, squares the base, and shifts the
exponent, each multiplication a call (`stepSt_ok`); `32 e` iterations consume
the exponent (`loopSt_ok`).
-/

@[expose] public section

namespace VG.Proof.Dsa.X86.Pow

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Dynamic VG.Impl.Dsa.X86.Pow

section
variable {n m size : Nat} {base : Addr} {s₀ : State}

theorem stepSt_ok {t : State} {y b k e : Nat} (S : St n m size base s₀ t) (hn : 2 ≤ n) (he : 2 ≤ e)
    (hen : e ≤ 2 * n)
    (hy : wordsVal t.mem base (slot n 6) n = y * 2 ^ (64 * n) % m)
    (hb : wordsVal t.mem base (slot n 5) n = b * 2 ^ (64 * n) % m)
    (hk : 0 < k) (hk32 : k < 2 ^ 32) (hc : t.gpr .esi = BitVec.ofNat 32 k) :
    WP isa (step n e) t fun u => St n m size base s₀ u ∧
      u.gpr .esi = BitVec.ofNat 32 (k - 1) ∧ u.zf = some (decide (k = 1)) ∧
      wordsVal u.mem base (slot n 6) n =
        (if val32 t.mem base (slot n 8) e % 2 = 1 then y * b else y) * 2 ^ (64 * n) % m ∧
      wordsVal u.mem base (slot n 5) n = (b * b) * 2 ^ (64 * n) % m ∧
      val32 u.mem base (slot n 8) e = val32 t.mem base (slot n 8) e / 2 := by
  have h := S.ctx
  have hm1 := h.gt_one
  have cop := h.coprime
  obtain wv : ∀ {m₁ m₂ : Mem} {j : Nat}, (∀ k ≤ 2 * n, val32 m₂ base (slot n j) k = val32 m₁ base (slot n j) k) →
      wordsVal m₂ base (slot n j) n = wordsVal m₁ base (slot n j) n := fun H => by
    rw [wordsVal_eq_val32, wordsVal_eq_val32, H _ (Nat.le_refl _)]
  unfold step
  refine WP.seq (WP.mono (maskSt_ok S) fun s₁ ⟨S₁, i₁, M₁, V₁⟩ => ?_)
  obtain y₁ : wordsVal s₁.mem base (slot n 6) n = y * 2 ^ (64 * n) % m := by rw [wv (V₁ 6 (by decide)), hy]
  obtain b₁ : wordsVal s₁.mem base (slot n 5) n = b * 2 ^ (64 * n) % m := by rw [wv (V₁ 5 (by decide)), hb]
  obtain bl₁ : wordsVal s₁.mem base (slot n 5) n < m := by rw [b₁]; exact Nat.mod_lt _ (by omega_using [hm1])
  refine WP.seq (WP.mono (mulSt_ok (o := 7) (a := 6) (b := 5) S₁ hn (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) bl₁) fun s₂ ⟨S₂, i₂, L₂, P₂, V₂, M₂⟩ => ?_)
  obtain p₂ : wordsVal s₂.mem base (slot n 7) n = y * b * 2 ^ (64 * n) % m := by
    obtain v := VG.Proof.Dsa.mont_product cop (a := y) (b := b) (by rw [y₁, Nat.mod_mod])
      (by rw [b₁, Nat.mod_mod]) P₂
    rwa [Nat.mod_eq_of_lt L₂] at v
  refine WP.seq (WP.mono (selectSt_ok (bit := decide (w32 t.mem base (slot n 8) % 2 = 1)) S₂ (by
      rw [M₂, M₁]; simp only [decide_eq_true_eq])) fun s₃ ⟨S₃, i₃, Y₃, V₃⟩ => ?_)
  obtain b₃ : wordsVal s₃.mem base (slot n 5) n = b * 2 ^ (64 * n) % m := by
    rw [wv (V₃ 5 (by decide) (by decide)), wv (V₂ 5 (by decide) (by decide) (by decide)), b₁]
  refine WP.seq (WP.mono (mulSt_ok (o := 5) (a := 5) (b := 5) S₃ hn (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [b₃]; exact Nat.mod_lt _ (by omega_using [hm1])))
    fun s₄ ⟨S₄, i₄, L₄, P₄, V₄, _⟩ => ?_)
  obtain b₄ : wordsVal s₄.mem base (slot n 5) n = b * b * 2 ^ (64 * n) % m := by
    obtain v := VG.Proof.Dsa.mont_product cop (a := b) (b := b) (by rw [b₃, Nat.mod_mod])
      (by rw [b₃, Nat.mod_mod]) P₄
    rwa [Nat.mod_eq_of_lt L₄] at v
  obtain e₄ : val32 s₄.mem base (slot n 8) e = val32 t.mem base (slot n 8) e := by
    rw [V₄ 8 (by decide) (by decide) (by decide) e hen, V₃ 8 (by decide) (by decide) e hen,
      V₂ 8 (by decide) (by decide) (by decide) e hen, V₁ 8 (by decide) e hen]
  refine WP.seq (WP.mono (shiftSt_ok S₄ he hen) fun s₅ ⟨S₅, i₅, E₅, V₅⟩ => ?_)
  obtain c₅ : s₅.gpr .esi = BitVec.ofNat 32 k := by rw [i₅, i₄, i₃, i₂, i₁, hc]
  refine wp_subS rfl fun v uv _ => ?_
  refine wp_cmpS rfl fun u fu zu => WP.block_nil ?_
  obtain mu : u.mem = s₅.mem := fu.mem.trans uv.mem
  obtain ku : Keeps powerClob s₅ u := (uv.keeps.mono (by decide)).trans (fu.keeps _)
  obtain Cu : Context n m base size u := ⟨S₅.ctx.scr.of_keeps ku (by decide), S₅.ctx.size_le,
    mu ▸ S₅.ctx.modulus, S₅.ctx.gt_one, mu ▸ S₅.ctx.inverse⟩
  refine ⟨⟨Cu, S₅.room, S₅.keeps.trans ku, mu ▸ S₅.mem⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [fu.gpr, uv.gpr, c₅, counter_sub hk32 hk]
  · rw [zu, uv.gpr, c₅, counter_sub hk32 hk, counter_zero hk32 hk]
  · rw [mu, wv (V₅ 6 (by decide) (by decide)), wv (V₄ 6 (by decide) (by decide) (by decide)), Y₃]
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega_using [he]⟩
    rw [val32_parity]
    by_cases hbit : w32 t.mem base (slot n 8) % 2 = 1
    · simp only [hbit, decide_true, ite_true]; exact p₂
    · simp only [hbit, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [wv (V₂ 6 (by decide) (by decide) (by decide)), y₁]
  · rw [mu, wv (V₅ 5 (by decide) (by decide)), b₄]
  · rw [mu, E₅, e₄]

structure LoopInv (n m size e target steps i : Nat) (base : Addr) (s₀ t : State) : Prop where
  st : St n m size base s₀ t
  counter : t.gpr .esi = BitVec.ofNat 32 (steps - i)
  bound : val32 t.mem base (slot n 8) e < 2 ^ (steps - i)
  value : ∃ y b,
    wordsVal t.mem base (slot n 6) n = y * 2 ^ (64 * n) % m ∧
    wordsVal t.mem base (slot n 5) n = b * 2 ^ (64 * n) % m ∧
    (y * b ^ val32 t.mem base (slot n 8) e) % m = target

theorem loopSt_ok {t : State} {a e : Nat} (S : St n m size base s₀ t) (hn : 2 ≤ n) (he : 2 ≤ e)
    (hen : e ≤ 2 * n)
    (hy : wordsVal t.mem base (slot n 6) n = 2 ^ (64 * n) % m)
    (hb : wordsVal t.mem base (slot n 5) n = a * 2 ^ (64 * n) % m)
    (hk32 : 32 * e < 2 ^ 32) (hc : t.gpr .esi = BitVec.ofNat 32 (32 * e)) :
    WP isa (.loop (step n e) .ne) t
      (LoopInv n m size e (a ^ val32 t.mem base (slot n 8) e % m) (32 * e) (32 * e) base s₀) := by
  let steps := 32 * e
  let target := a ^ val32 t.mem base (slot n 8) e % m
  obtain hspos : 0 < steps := by dsimp [steps]; omega_using [he]
  obtain init : LoopInv n m size e target steps 0 base s₀ t := by
    refine ⟨S, ?_, ?_, ⟨1, a, ?_, hb, ?_⟩⟩
    · simpa only [Nat.sub_zero] using hc
    · simpa only [Nat.sub_zero] using val32_lt t.mem base (slot n 8) e
    · simpa only [Nat.one_mul] using hy
    · simp only [Nat.one_mul]; rfl
  refine WP.loop (M := isa)
    (fun k u => ∃ i, k = steps - i ∧ i < steps ∧ LoopInv n m size e target steps i base s₀ u)
    ?_ steps t ⟨0, rfl, hspos, init⟩
  rintro k u ⟨i, rfl, hi, I⟩
  obtain ⟨y, b, Y, B, V⟩ := I.value
  refine WP.mono (stepSt_ok I.st hn he hen Y B (by omega_using [hi]) (by dsimp [steps] at *; omega_using [hk32]) I.counter)
    fun w ⟨S', count, zf, Y', B', E'⟩ => ?_
  obtain next : LoopInv n m size e target steps (i + 1) base s₀ w := by
    refine ⟨S', ?_, ?_, ⟨_, _, Y', B', ?_⟩⟩
    · rw [count, show steps - i - 1 = steps - (i + 1) by omega_using []]
    · rw [E']
      obtain hp : 2 ^ (steps - i) = 2 ^ (steps - (i + 1)) * 2 := by
        rw [show steps - i = steps - (i + 1) + 1 by omega_using [hi], Nat.pow_succ]
      have bound := I.bound
      rw [hp] at bound
      omega_using [bound]
    · rw [E', exponent_step_value]
      exact V
  by_cases hdone : i + 1 = steps
  · refine .inl ⟨?_, ?_⟩
    · have eq : steps - i = 1 := by omega_using [hdone]
      simp only [eval, zf, eq, decide_true, Option.map_some, Bool.not_true]
    · change LoopInv n m size e target steps steps base s₀ w
      rw [hdone] at next
      exact next
  · refine .inr ⟨?_, steps - (i + 1), by omega_using [hi], i + 1, rfl, by omega_using [hi, hdone], next⟩
    obtain ne : steps - i ≠ 1 := by omega_using [hdone]
    simp only [eval, zf, decide_eq_false ne, Option.map_some, Bool.not_false]

theorem LoopInv.finished {e target steps : Nat} {t : State}
    (I : LoopInv n m size e target steps steps base s₀ t) :
    wordsVal t.mem base (slot n 6) n = target * 2 ^ (64 * n) % m := by
  have bound := I.bound
  simp only [Nat.sub_self, Nat.pow_zero] at bound
  obtain ez : val32 t.mem base (slot n 8) e = 0 := by omega_using [bound]
  obtain ⟨y, b, Y, _, V⟩ := I.value
  rw [ez, Nat.pow_zero, Nat.mul_one] at V
  rw [Y, Nat.mul_mod y, V, Nat.mul_mod_mod]

end

end VG.Proof.Dsa.X86.Pow

end

end


/-! # Shared IA-32 DSA exponentiation: arithmetic and memory effects

The setup leaves `2^(65 n) mod m` in slot 4, and each Montgomery square of
`2^(64 n + c) mod m` is `2^(64 n + 2 c) mod m` (`square_value`), so six of
them leave `R² mod m`, `R = 2^(64 n)` (`squarings_ok`). Then the result is
`R mod m` and the base is encoded (`encode_ok`), the loop raises it to the
exponent, and a product with one decodes it (`core_ok`).
-/

@[expose] public section
namespace VG.Proof.Dsa.X86.Pow
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.X86.Pow

theorem square_value {n m c X out : Nat} (hR : Nat.Coprime (2 ^ (64 * n)) m)
    (hX : X = 2 ^ (64 * n + c) % m) (h : out * 2 ^ (64 * n) % m = X * X % m) (hlt : out < m) :
    out = 2 ^ (64 * n + 2 * c) % m := by
  obtain v := VG.Proof.Bignum.mont_cancel hR (o := out) (c := 2 ^ (64 * n + 2 * c)) (by
    rw [h, hX, ← Nat.mul_mod, ← Nat.pow_add, ← Nat.pow_add]
    congr 2
    omega_arith)
  rwa [Nat.mod_eq_of_lt hlt] at v

section
variable {n m size : Nat} {base : Addr} {s₀ : State}

theorem squarings_ok {t : State} (hn : 2 ≤ n) (j : Nat) :
    ∀ k, St n m size base s₀ t →
    wordsVal t.mem base (slot n 4) n = 2 ^ (64 * n + n * 2 ^ j) % m →
    WP isa (squarings n k) t fun u => St n m size base s₀ u ∧
      wordsVal u.mem base (slot n 4) n = 2 ^ (64 * n + n * 2 ^ (j + k)) % m ∧
      ∀ i, 5 ≤ i → i < 9 → ∀ k ≤ 2 * n, val32 u.mem base (slot n i) k = val32 t.mem base (slot n i) k
  | 0, S, hx => WP.block_nil ⟨S, hx, fun _ _ _ _ _ => rfl⟩
  | k + 1, S, hx => by
    refine WP.seq (WP.mono (squarings_ok hn j k S hx) fun u ⟨Su, xu, Vu⟩ => ?_)
    refine WP.mono (mulSt_ok (o := 4) (a := 4) (b := 4) Su hn (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by rw [xu]; exact Nat.mod_lt _ (by have := Su.ctx.gt_one; omega_arith)))
      fun w ⟨Sw, _, L, P, V, _⟩ => ⟨Sw, ?_, fun i hi5 hi k hk => ?_⟩
    · rw [square_value Su.ctx.coprime xu P L, show j + (k + 1) = (j + k) + 1 from rfl, Nat.pow_succ,
        Nat.mul_comm (2 ^ (j + k)) 2, Nat.mul_left_comm]
    · rw [V i (by omega_arith) hi (by omega_arith) k hk, Vu i hi5 hi k hk]

theorem encode_ok {t : State} (S : St n m size base s₀ t) (hn : 2 ≤ n)
    (hr2 : wordsVal t.mem base (slot n 4) n = 2 ^ (128 * n) % m) :
    WP isa (encode n) t fun u => St n m size base s₀ u ∧ u.gpr .esi = t.gpr .esi ∧
      wordsVal u.mem base (slot n 6) n = 2 ^ (64 * n) % m ∧
      wordsVal u.mem base (slot n 5) n = wordsVal t.mem base (slot n 5) n * 2 ^ (64 * n) % m ∧
      ∀ k ≤ 2 * n, val32 u.mem base (slot n 8) k = val32 t.mem base (slot n 8) k := by
  have cop := S.ctx.coprime
  have hm1 := S.ctx.gt_one
  obtain wv : ∀ {m₁ m₂ : Mem} {j : Nat}, (∀ k ≤ 2 * n, val32 m₂ base (slot n j) k = val32 m₁ base (slot n j) k) →
      wordsVal m₂ base (slot n j) n = wordsVal m₁ base (slot n j) n := fun H => by
    rw [wordsVal_eq_val32, wordsVal_eq_val32, H _ (Nat.le_refl _)]
  obtain RR : 2 ^ (128 * n) = 2 ^ (64 * n) * 2 ^ (64 * n) := by rw [← Nat.pow_add]; congr 1; omega_arith
  unfold encode
  refine WP.seq (WP.mono (oneSt_ok S (i := 7) (by decide) (by decide)) fun s₁ ⟨S₁, i₁, O₁, V₁⟩ => ?_)
  obtain x₁ : wordsVal s₁.mem base (slot n 4) n = 2 ^ (128 * n) % m := by rw [wv (V₁ 4 (by decide) (by decide)), hr2]
  refine WP.seq (WP.mono (mulSt_ok (o := 6) (a := 4) (b := 7) S₁ hn (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [O₁]; exact hm1)) fun s₂ ⟨S₂, i₂, L₂, P₂, V₂, _⟩ => ?_)
  obtain y₂ : wordsVal s₂.mem base (slot n 6) n = 2 ^ (64 * n) % m := by
    obtain v := VG.Proof.Dsa.mont_decode cop (A := wordsVal s₁.mem base (slot n 4) n) (a := 2 ^ (64 * n))
      (by rw [x₁, Nat.mod_mod, RR]) (by rw [P₂, O₁])
    rwa [Nat.mod_eq_of_lt L₂] at v
  obtain x₂ : wordsVal s₂.mem base (slot n 4) n = 2 ^ (128 * n) % m := by
    rw [wv (V₂ 4 (by decide) (by decide) (by decide)), x₁]
  refine WP.mono (mulSt_ok (o := 5) (a := 5) (b := 4) S₂ hn (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [x₂]; exact Nat.mod_lt _ (by omega_arith)))
    fun u ⟨Su, iu, Lu, Pu, Vu, _⟩ => ⟨Su, by rw [iu, i₂, i₁], ?_, ?_, fun k hk => ?_⟩
  · rw [wv (Vu 6 (by decide) (by decide) (by decide)), y₂]
  · have b₂ : wordsVal s₂.mem base (slot n 5) n = wordsVal t.mem base (slot n 5) n := by
      rw [wv (V₂ 5 (by decide) (by decide) (by decide)), wv (V₁ 5 (by decide) (by decide))]
    obtain v := VG.Proof.Bignum.mont_cancel cop (o := wordsVal u.mem base (slot n 5) n)
      (c := wordsVal t.mem base (slot n 5) n * 2 ^ (64 * n)) (by
        rw [Pu, x₂, b₂, Nat.mul_mod_mod, RR, Nat.mul_assoc])
    rwa [Nat.mod_eq_of_lt Lu] at v
  · rw [Vu 8 (by decide) (by decide) (by decide) k hk, V₂ 8 (by decide) (by decide) (by decide) k hk,
      V₁ 8 (by decide) (by decide) k hk]

theorem finish_ok {t : State} {T : Nat} (S : St n m size base s₀ t) (hn : 2 ≤ n)
    (hY : wordsVal t.mem base (slot n 6) n = T * 2 ^ (64 * n) % m) (hT : T < m) :
    WP isa (finish n) t fun u => St n m size base s₀ u ∧ wordsVal u.mem base (slot n 6) n = T := by
  unfold finish
  refine WP.seq (WP.mono (oneSt_ok S (i := 7) (by decide) (by decide)) fun s₁ ⟨S₁, _, O₁, V₁⟩ => ?_)
  obtain y₁ : wordsVal s₁.mem base (slot n 6) n = T * 2 ^ (64 * n) % m := by
    rw [wordsVal_eq_val32, V₁ 6 (by decide) (by decide) _ (Nat.le_refl _), ← wordsVal_eq_val32, hY]
  refine WP.mono (mulSt_ok (o := 6) (a := 6) (b := 7) S₁ hn (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [O₁]; exact S.ctx.gt_one)) fun u ⟨Su, _, Lu, Pu, _⟩ => ⟨Su, ?_⟩
  obtain v := VG.Proof.Dsa.mont_decode S.ctx.coprime (A := wordsVal s₁.mem base (slot n 6) n) (a := T)
    (by rw [y₁, Nat.mod_mod]) (by rw [Pu, O₁])
  rwa [Nat.mod_eq_of_lt Lu, Nat.mod_eq_of_lt hT] at v

theorem core_ok {s : State} {base : Addr} {size n e m : Nat}
    (hs : Scr s base size) (R : CallRoom (s.gpr .esp) base size) (hz : contextBytes n ≤ size)
    (hn : 2 ≤ n) (hn48 : n ≤ 48) (he : 1 < e) (hen : e ≤ 2 * n)
    (hv : wordsVal s.mem base (slot n 0) n = m) (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (core n e) s fun t =>
      wordsVal t.mem base (slot n 6) n =
        wordsVal s.mem base (slot n 5) n ^ val32 s.mem base (slot n 8) e % m ∧
      OutsS base (s.gpr .esp) (coreRanges n) s.mem t.mem ∧ Keeps powerClob s t := by
  have nw := hs.nowrap
  obtain hnz : contextBytes n ≤ 2 ^ 64 := by omega_arith
  obtain b8 := slot_bound (n := n) (i := 8) (by decide)
  simp only [stride] at b8
  unfold core setup
  refine WP.seq (WP.seq (WP.mono (contextSeed_ok (bits := 65 * n) hs (by omega_arith) (by omega_arith) (by omega_arith) hz hv hm1
    hodd) fun u ⟨Cu, _, Xu, Ou, Ku⟩ => ?_))
  obtain hset : ∀ r ∈ setupRanges n, ∃ c ∈ coreRanges n, c.1 ≤ r.1 ∧ r.1 + r.2 ≤ c.1 + c.2 := by
    intro r hr
    simp only [setupRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨(0, 8), List.mem_cons_self .., by decide, by decide⟩
    all_goals exact in_core (by decide) (by simp only [contextBytes, slot_lin] at b8 ⊢; omega_arith)
  obtain Su : St n m size base s u := ⟨Cu, R, Ku, (OutsS.of_outs Ou).core hset⟩
  obtain keep₀ : ∀ i, 5 ≤ i → i < 9 → ∀ k ≤ 2 * n, val32 u.mem base (slot n i) k = val32 s.mem base (slot n i) k := by
    intro i hi5 hi k hk
    obtain bi := slot_bound (n := n) hi
    obtain l5 := Nat.mul_le_mul_right (16 * n + 8) hi5
    simp only [stride] at bi
    apply Ou.val32
    · simp only [setupRanges, List.forall_mem_cons, List.not_mem_nil, false_imp_iff,
        implies_true, and_true]
      simp only [slot_lin] at *
      omega_arith
    · omega_arith
  refine WP.mono (squarings_ok hn 0 6 Su (by
    rw [Xu, Nat.pow_zero, Nat.mul_one, show 64 * n + n = 65 * n by omega_arith])) fun w ⟨Sw, Xw, Vw⟩ => ?_
  refine WP.seq (WP.mono (encode_ok Sw hn (by
    rw [Xw, show 64 * n + n * 2 ^ (0 + 6) = 128 * n by rw [show (2 : Nat) ^ (0 + 6) = 64 from rfl]; omega_arith]))
    fun v ⟨Sv, _, Yv, Bv, Ev⟩ => ?_)
  refine WP.seq (wp_movS rfl fun v₁ u₁ _ => WP.block_nil ?_)
  obtain k₁ : Keeps powerClob v v₁ := u₁.keeps.mono (by decide)
  obtain S₁ : St n m size base s v₁ := ⟨⟨Sv.ctx.scr.of_keeps k₁ (by decide), Sv.ctx.size_le,
    u₁.mem ▸ Sv.ctx.modulus, Sv.ctx.gt_one, u₁.mem ▸ Sv.ctx.inverse⟩, Sv.room, Sv.keeps.trans k₁, u₁.mem ▸ Sv.mem⟩
  obtain B₀ : wordsVal v₁.mem base (slot n 5) n = wordsVal s.mem base (slot n 5) n * 2 ^ (64 * n) % m := by
    rw [u₁.mem, Bv, wordsVal_eq_val32, wordsVal_eq_val32 (d := slot n 5), Vw 5 (by decide) (by decide) _ (Nat.le_refl _),
      keep₀ 5 (by decide) (by decide) _ (Nat.le_refl _)]
  obtain E₀ : val32 v₁.mem base (slot n 8) e = val32 s.mem base (slot n 8) e := by
    rw [u₁.mem, Ev e hen, Vw 8 (by decide) (by decide) e hen, keep₀ 8 (by decide) (by decide) e hen]
  refine WP.seq (WP.mono (loopSt_ok S₁ hn he hen (by rw [u₁.mem]; exact Yv) B₀ (by omega_arith) u₁.gpr) fun x I => ?_)
  refine WP.mono (finish_ok I.st hn I.finished (Nat.mod_lt _ (by omega_arith))) fun t ⟨St, V⟩ => ⟨?_, St.mem, St.keeps⟩
  rw [V, E₀]

end

end VG.Proof.Dsa.X86.Pow
