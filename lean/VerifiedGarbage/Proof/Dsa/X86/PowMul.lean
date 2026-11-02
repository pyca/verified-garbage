module

public import VerifiedGarbage.Impl.Dsa.X86.Pow
public import VerifiedGarbage.Proof.Mont.X86.ContextFrame
public import VerifiedGarbage.Proof.Dsa.X86.PowOuts
public import VerifiedGarbage.Proof.Bignum.X86.RtCall
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.MulArgs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.X86.Instr

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
