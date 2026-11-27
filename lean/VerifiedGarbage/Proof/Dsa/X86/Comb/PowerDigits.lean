module

public import VerifiedGarbage.Proof.Dsa.X86.Comb.PowerFrame
public import VerifiedGarbage.Impl.Mont.X86.CombPower
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Mont.X86.WindowWords
import Init.Data.BitVec.Basic
import VerifiedGarbage.TCB.Mem
import VerifiedGarbage.Proof.Mont.X86.DynamicFrame
import VerifiedGarbage.Proof.Mont.X86.ContextMul
import VerifiedGarbage.Proof.Mont.X86.ContextMath
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Rsa.FixedBaseCombMont
import VerifiedGarbage.Proof.Dsa.X86.Comb.SelectTable
public import VerifiedGarbage.Proof.Rsa.FixedBaseComb
import VerifiedGarbage.Proof.Mont.X86.CombDigitMath
import VerifiedGarbage.Proof.Mont.X86.ExponentWord

/-! ### `Mont.X86.CombDigit`, which this module and modules that import it used -/

section

/-! ### `Mont.X86.CombTooth`, which only this module used -/

section

/-! Extract one fixed comb bit; its memory address is independent of its value. -/

@[expose] public section
namespace VG.Proof.Mont.X86.Comb
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Comb
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Proof.Rsa.FixedBaseComb (bit)

theorem toothRead_ok {s : State} {base : Addr} {size o k p : Nat}
    (hs : Scr s base size) (ho : o+4*k≤size) (hp : p<32*k) :
    WP isa (.block (toothRead o p)) s fun t =>
      t.mem=s.mem ∧ (t.gpr .eax).toNat=bit (val32 s.mem base o k) p ∧ Keeps [.eax] s t := by
  unfold toothRead
  simp only [List.cons_append,List.nil_append]
  refine wp_movS (readSrc_sc hs (by omega_using [ho, hp])) fun u U _ => ?_
  have finish {v : State} (M : v.mem=s.mem) (K : Keeps [.eax] s v)
      (V : (v.gpr .eax).toNat = w32 s.mem base (o+4*(p/32)) / 2^(p%32)) :
      WP isa (.block [.alu .and .eax (imm 1)]) v fun t =>
        t.mem=s.mem ∧ (t.gpr .eax).toNat=bit (val32 s.mem base o k) p ∧ Keeps [.eax] s t := by
    refine wp_andi fun t T => WP.block_nil ⟨T.mem.trans M,?_,K.trans (T.keeps.mono (by decide))⟩
    rw [T.gpr,BitVec.toNat_and,show (1#32).toNat=1 from rfl,Nat.and_one_is_mod,V]
    exact word_bit hp
  by_cases zero : p%32=0
  · simp only [zero,beq_self_eq_true,ite_true,List.nil_append]
    apply finish U.mem (U.keeps.mono (by decide))
    rw [U.gpr,zero,Nat.pow_zero,Nat.div_one]
  · simp only [show (p%32 == 0)=false by exact beq_eq_false_iff_ne.mpr zero]
    refine wp_shr (by omega_using [zero]) fun v V _ => ?_
    apply finish (V.mem.trans U.mem) ((U.keeps.mono (by decide)).trans (V.keeps.mono (by decide)))
    rw [V.gpr,U.gpr,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]

end VG.Proof.Mont.X86.Comb

end

end

/-! The five fixed-position comb bits form a bounded table index. -/

-- Formerly `VerifiedGarbage/Proof/Mont/X86/CombDigitControl.lean`, which only this module imported.
section

/-! Accumulate five extracted bits without value-dependent control flow. -/

section
namespace VG.Proof.Mont.X86.Comb
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Comb
open VG.Proof.Mont VG.Proof.Mont.X86

theorem doubleBits_ok (j : Nat) {s : State} (bound : (s.gpr .eax).toNat*2^j<2^32) :
    WP isa (.block (List.replicate j (.alu .add .eax (.reg .eax)))) s fun t =>
      t.mem=s.mem ∧ (t.gpr .eax).toNat=(s.gpr .eax).toNat*2^j ∧ Keeps [.eax] s t := by
  induction j generalizing s with
  | zero => exact WP.block_nil ⟨rfl,by simp only [Nat.pow_zero,Nat.mul_one],Keeps.refl _ _⟩
  | succ j ih =>
    rw [List.replicate_succ]
    refine wp_addS rfl fun u U _ => ?_
    have eq : (u.gpr .eax).toNat=(s.gpr .eax).toNat*2 := by
      rw [U.gpr,BitVec.toNat_add,Nat.mod_eq_of_lt]
      · omega
      · have pow : 2≤2^(j+1) := Nat.le_self_pow (by omega) 2
        have := Nat.mul_le_mul_left (s.gpr .eax).toNat pow
        omega
    have next : (u.gpr .eax).toNat*2^j=(s.gpr .eax).toNat*2^(j+1) := by
      rw [eq,Nat.pow_succ]; ac_rfl
    exact WP.mono (ih (by rw [next]; exact bound)) fun t ⟨M,V,K⟩ =>
      ⟨M.trans U.mem,V.trans next,(U.keeps.mono (by decide)).trans K⟩

theorem addBit_ok {s : State} {j b a : Nat} (hj : j<5) (hb : b<2) (ha : a<2^j)
    (A : (s.gpr .eax).toNat=b) (B : (s.gpr .ebx).toNat=a) :
    WP isa (.block (List.replicate j (.alu .add .eax (.reg .eax)) ++ ([.alu .or .ebx (.reg .eax)] : List Instr))) s
      fun t => t.mem=s.mem ∧ (t.gpr .ebx).toNat=a+b*2^j ∧ Keeps [.eax,.ebx] s t := by
  have p32 : 2^j ≤ 16 := by
    have finite : ∀ j<5, 2^j≤16 := by decide
    exact finite j hj
  refine WP.block_append (WP.mono (doubleBits_ok j (by rw [A]; have := Nat.mul_le_mul_right (2^j) (show b≤1 by omega); omega))
    fun u ⟨M,V,K⟩ => ?_)
  refine wp_or fun t T => WP.block_nil ⟨T.mem.trans M,?_,(K.mono (by decide)).trans (T.keeps.mono (by decide))⟩
  rw [T.gpr,BitVec.toNat_or,K.1 .ebx (by decide),B,V,A,Nat.or_comm]
  rw [←Nat.shiftLeft_eq,←Nat.shiftLeft_add_eq_or_of_lt ha,Nat.shiftLeft_eq,Nat.add_comm]

end VG.Proof.Mont.X86.Comb
end

end

@[expose] public section
namespace VG.Proof.Mont.X86.Comb
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Comb
open VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.FixedBaseComb (bit bit_lt)

def partialDigit (d x : Nat) : Nat → Nat
  | 0 => 0
  | j+1 => partialDigit d x j + bit x ((j+1)*d-1)*2^j

theorem partialDigit_lt (d x j : Nat) : partialDigit d x j<2^j := by
  induction j with
  | zero => exact Nat.zero_lt_one
  | succ j ih =>
    have h := Nat.mul_le_mul_right (2^j) (show bit x ((j+1)*d-1)≤1 from by have := bit_lt x ((j+1)*d-1); omega_using [this])
    simp only [Nat.one_mul] at h
    rw [partialDigit,Nat.pow_succ]; omega_using [ih, h]

/-- Zero padding and repeated shifts expose the original exponent's comb row. -/
theorem partialDigit_shifted (bits x width row : Nat)
    (hr : row<Spec.Rsa.FixedBaseComb.rows bits) (hw : 5*Spec.Rsa.FixedBaseComb.rows bits≤width) :
    partialDigit (Spec.Rsa.FixedBaseComb.rows bits)
      ((x*2^(Spec.Rsa.FixedBaseComb.rows bits-1-row))%2^width) 5 =
      VG.Proof.Rsa.FixedBaseComb.digit bits x row := by
  simp only [partialDigit]
  rw [VG.Proof.Rsa.FixedBaseComb.shifted_tooth bits x width row 0 hr (by decide) hw,
    VG.Proof.Rsa.FixedBaseComb.shifted_tooth bits x width row 1 hr (by decide) hw,
    VG.Proof.Rsa.FixedBaseComb.shifted_tooth bits x width row 2 hr (by decide) hw,
    VG.Proof.Rsa.FixedBaseComb.shifted_tooth bits x width row 3 hr (by decide) hw,
    VG.Proof.Rsa.FixedBaseComb.shifted_tooth bits x width row 4 hr (by decide) hw]
  simp only [VG.Proof.Rsa.FixedBaseComb.digit,Nat.zero_mul,Nat.add_zero,Nat.one_mul,
    Nat.pow_zero,Nat.mul_one,Nat.zero_add]
  omega_using []

theorem digitParts_ok {s : State} {base : Addr} {size o k d : Nat}
    (hs : Scr s base size) (ho : o+4*k≤size) (hd : 0<d) (cover : 5*d≤32*k)
    (B : s.gpr .ebx=0) : ∀ j, j≤5 →
    WP isa (.block ((List.range j).flatMap (fun j =>
      toothRead o ((j+1)*d-1) ++ List.replicate j (.alu .add .eax (.reg .eax)) ++
      ([.alu .or .ebx (.reg .eax)] : List Instr)))) s fun t =>
      t.mem=s.mem ∧ (t.gpr .ebx).toNat=partialDigit d (val32 s.mem base o k) j ∧ Keeps [.eax,.ebx] s t
  | 0, _ => WP.block_nil ⟨rfl,by rw [B]; rfl,Keeps.refl _ _⟩
  | j+1, hj => by
    rw [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    refine WP.block_append (WP.mono (digitParts_ok hs ho hd cover B j (by omega_using [hj])) fun u ⟨M,V,K⟩ => ?_)
    have hu := hs.of_keeps K (by decide)
    have position : (j+1)*d-1<32*k := by
      have := Nat.mul_le_mul_right d hj
      have := Nat.mul_le_mul_right d (show 1≤j+1 by omega_using [])
      simp only [Nat.one_mul] at this
      omega_arith
    rw [List.append_assoc]
    refine WP.block_append (WP.mono (toothRead_ok hu ho position) fun v ⟨Mv,Vv,Kv⟩ => ?_)
    have Bv : (v.gpr .ebx).toNat=partialDigit d (val32 s.mem base o k) j := by
      rw [Kv.1 .ebx (by decide),V]
    rw [M] at Vv
    exact WP.mono (addBit_ok (by omega_using [hj]) (bit_lt _ _) (partialDigit_lt _ _ _) Vv Bv)
      fun t ⟨Mt,Vt,Kt⟩ => ⟨Mt.trans (Mv.trans M),Vt,(K.trans (Kv.mono (by decide))).trans Kt⟩

theorem digit_ok {s : State} {base : Addr} {size o k d : Nat}
    (hs : Scr s base size) (ho : o+4*k≤size) (hd : 0<d) (cover : 5*d≤32*k) (hw : 8≤size) :
    WP isa (VG.Impl.Mont.X86.Comb.digit o d) s fun t =>
      Outside base 4 4 s.mem t.mem ∧
      w32 t.mem base 4=partialDigit d (val32 s.mem base o k) 5 ∧ Keeps [.eax,.ebx] s t := by
  unfold VG.Impl.Mont.X86.Comb.digit VG.Impl.Mont.X86.Dynamic.windowOffset
  simp only [List.cons_append,List.nil_append]
  refine wp_movS rfl fun u U _ => ?_
  refine WP.block_append (WP.mono (digitParts_ok (hs.of_keeps U.keeps (by decide)) ho hd cover U.gpr 5 (by decide))
    fun v ⟨M,V,K⟩ => ?_)
  have Kv : Keeps [.eax,.ebx] s v := (U.keeps.mono (by decide)).trans K
  have hv := hs.of_keeps Kv (by decide)
  refine wp_storeS (hv.ea (by omega_using [hw])) (hv.write hw) fun t T => WP.block_nil ⟨?_,?_,Kv.trans (T.keeps _)⟩
  · rw [T.mem,M,U.mem]; exact writeW32_outside _ _ _ (by decide)
  · rw [T.mem,w32_write_self,V,U.mem]

end VG.Proof.Mont.X86.Comb

end

end

/-! ### `Mont.X86.CombShift`, which only this module used -/

section

/-! # Shifting a number's words up by one bit, in a loop over its words

From the lowest word up, each word times 2, plus the one bit carried out
of the word below (in `ecx`).
-/

-- Formerly `VerifiedGarbage/Proof/Mont/X86/CombShiftMath.lean`, which only this module imported.
section

/-! # The window's exponent words: their top four bits, and the arithmetic of their shift -/

section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont
open VG.Proof.Mont.X86

theorem times2_toNat (x : BitVec 32) : (x+x).toNat = x.toNat*2%2^32 := by
  rw [BitVec.toNat_add]; congr 1; omega

theorem shr31_toNat (x : BitVec 32) : (x >>> 31).toNat = x.toNat / 2 ^ 31 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- `(V + P w) · 2 mod P 2³²`, for `V < P`: the low part times 2 mod `P`, and
the top word times 2 mod 2³² with the four bits carried up from below. -/
theorem shift_top_one {V P w : Nat} (hP : 0 < P) (hV : V < P) :
    (V + P * w) * 2 % (P * 2 ^ 32) = V * 2 % P + P * (w * 2 % 2 ^ 32 + V * 2 / P) :=
  shift_top_scale (by decide) (by decide) hP hV

theorem val32_top_bit (m : Mem) (base : Addr) (d j : Nat) :
    val32 m base d (j + 1) * 2 / 2 ^ (32 * (j + 1)) = w32 m base (d + 4 * j) / 2 ^ 31 := by
  have hP : 0 < 2 ^ (32 * j) := Nat.two_pow_pos _
  have hV := val32_lt m base d j
  have hq : val32 m base d j * 2 / 2 ^ (32 * j) < 2 := (Nat.div_lt_iff_lt_mul hP).2 (by omega)
  rw [val32_succ, pow32_succ, Nat.mul_comm (2 ^ 32), ← Nat.div_div_eq_div_mul, Nat.add_mul,
    Nat.mul_assoc, Nat.add_mul_div_left _ _ hP]
  generalize val32 m base d j * 2 / 2 ^ (32 * j) = q at hq
  omega


end VG.Proof.Mont.X86.Dynamic
end

end

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont
open VG.Proof.Mont.X86

/-- The `k` words at `o` times 2, modulo their width. -/
theorem shiftOne_ok {s : State} {base : Addr} {size k o : Nat} (hs : Scr s base size)
    (hk : 0 < k) (ho : o + 4 * k ≤ size) :
    WP isa (VG.Impl.Mont.X86.Comb.shiftOne k o) s fun t =>
      Outside base o (4 * k) s.mem t.mem ∧
      val32 t.mem base o k = val32 s.mem base o k * 2 % 2 ^ (32 * k) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have hn := hs.nowrap
  unfold VG.Impl.Mont.X86.Comb.shiftOne
  refine WP.seq (wp_movS rfl fun s₁ u₁ _ => WP.block_nil ?_)
  refine wordLoop_ok (fun j t => Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t ∧
      Outside base o (4 * j) s.mem t.mem ∧
      val32 t.mem base o j = val32 s.mem base o j * 2 % 2 ^ (32 * j) ∧
      (t.gpr .ecx).toNat = val32 s.mem base o j * 2 / 2 ^ (32 * j)) hk
    (by have := hs.size_lt; omega_using [ho, this])
    (fun j u u' ⟨K, O, V, C⟩ ⟨hm, hr, hw, hg⟩ =>
      ⟨⟨fun r h => (hg r (by simp_all) (by simp_all)).trans (K.1 r h), hr.trans K.2.1, hw.trans K.2.2⟩,
        hm ▸ O, hm ▸ V, by rw [hg _ (by decide) (by decide)]; exact C⟩)
    ⟨u₁.keeps.mono (by decide), u₁.mem ▸ VG.Proof.Mont.Outside.refl _ _ _ _,
      by simp only [val32, Nat.zero_mul, Nat.zero_mod],
      by rw [u₁.gpr]; simp only [val32, Nat.zero_mul, Nat.zero_div]; rfl⟩
    (fun j hj t ⟨K, O, V, C⟩ ej => ?_) (fun u ⟨K, O, V, _⟩ => ⟨O, V, K⟩)
  have ht := hs.of_keeps K (by decide)
  refine wp_movS (readSrc_at' ht ej (d := o) (by omega_using [ho, hj])) fun s₂ u₂ _ => ?_
  refine wp_movS rfl fun s₃ u₃ _ => ?_
  refine wp_shr (by decide) fun s₄ u₄ _ => ?_
  refine wp_addS rfl fun s₈ u₈ _ => ?_
  refine wp_addS rfl fun s₉ u₉ _ => ?_
  have k₉ : Keeps [.eax, .ebx] t s₉ := ((((u₂.keeps.mono (by decide)).widen u₃.keeps).widen
    u₄.keeps).widen u₈.keeps).widen u₉.keeps
  have hs₉ := ht.of_keeps k₉ (by decide)
  have ej₉ : s₉.gpr .ebp = s₉.gpr .edi + BitVec.ofNat 32 (4 * j) := by
    rw [k₉.1 _ (by decide), k₉.1 _ (by decide)]; exact ej
  refine wp_storeS (hs₉.ea_at' ej₉ (d := o) (by omega_using [ho, hj])) (hs₉.write (d := o + 4 * j) (n := 4) (by omega_using [ho, hj]))
    fun s₁₀ m₁₀ => ?_
  refine wp_movS rfl fun u u₁₁ _ => WP.block_nil ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact (K.trans ((k₉.mono (by decide)).trans (m₁₀.keeps _))).trans (u₁₁.keeps.mono (by decide))
  · have mem₉ : s₉.mem = t.mem := by
      rw [u₉.mem, u₈.mem, u₄.mem, u₃.mem, u₂.mem]
    rw [u₁₁.mem, m₁₀.mem, mem₉]
    exact (O.mono (Nat.le_refl _) (by omega_using [])).trans
      ((writeW32_outside _ _ _ (by omega_using [ho, hn, hj])).mono (by omega_using []) (by omega_using []))
  · have mem₉ : s₉.mem = t.mem := by
      rw [u₉.mem, u₈.mem, u₄.mem, u₃.mem, u₂.mem]
    have word : w32 t.mem base (o + 4 * j) = w32 s.mem base (o + 4 * j) := O.w32 (by omega_using []) (by omega_using [ho, hn, hj])
    have ecx₈ : s₈.gpr .ecx = t.gpr .ecx := by
      rw [u₈.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide)]
    have value : (s₉.gpr .eax).toNat =
        w32 s.mem base (o + 4 * j) * 2 % 2 ^ 32 + val32 s.mem base o j * 2 / 2 ^ (32 * j) := by
      rw [u₉.gpr, BitVec.toNat_add, ecx₈, C, u₈.gpr,
        u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, times2_toNat]
      change (w32 t.mem base (o + 4 * j) * 2 % 2 ^ 32 + _) % 2 ^ 32 = _
      rw [word]
      have : val32 s.mem base o j * 2 / 2 ^ (32 * j) < 2 :=
        (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2 (by have := val32_lt s.mem base o j; omega_using [this])
      omega_using [C, this]
    rw [u₁₁.mem, m₁₀.mem, mem₉, val32_store hn (by omega_using [ho, hj]), V, value, val32_succ, pow32_succ,
      Nat.mul_comm (2 ^ 32), shift_top_one (Nat.two_pow_pos _) (val32_lt _ _ _ _)]
  · rw [u₁₁.gpr, m₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₄.gpr, u₃.gpr, u₂.gpr, shr31_toNat,
      val32_top_bit]
    exact congrArg (· / 2 ^ 31) (O.w32 (by omega_using []) (by omega_using [ho, hn, hj]))
  · rw [u₁₁.other _ (by decide), m₁₀.gpr, k₉.1 _ (by decide)]
  · rw [u₁₁.other _ (by decide), m₁₀.gpr, k₉.1 _ (by decide)]

end VG.Proof.Mont.X86.Dynamic

end

end


/-! Square the accumulator and extract the next digit before table selection. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Proof.Mont.X86.Comb (TableAt tableValue partialDigit)

theorem powerDigits_ok {n e m g E : Nat} {base : Addr} {s : State}
    (h : Supported n e) (C : Context n m base (layout n e).size s)
    (T : TableAt n (context n) m g (32*e) base (fun _ => True) s.mem)
    (A : wordsVal s.mem base (slot n 6) n = Spec.Rsa.powMod g E m * 2^(64*n)%m) :
    WP isa (VG.Impl.Mont.X86.Comb.powerDigits n e) s fun t =>
      Context n m base (layout n e).size t ∧
      TableAt n (context n) m g (32*e) base (fun _ => True) t.mem ∧
      wordsVal t.mem base (slot n 6) n = Spec.Rsa.powMod g (2*E) m * 2^(64*n)%m ∧
      val32 t.mem base (slot n 8) (expWords e) =
        val32 s.mem base (slot n 8) (expWords e)*2%2^(32*expWords e) ∧
      w32 t.mem base 4=partialDigit (rows e) (val32 s.mem base (slot n 8) (expWords e)) 5 ∧
      Outs base (powerRanges n e) s.mem t.mem ∧ Keeps [.eax,.ebx,.ecx,.edx,.ebp] s t := by
  obtain ⟨dp,_,ep,ew,cover,eb,sz⟩ := power_bounds h
  unfold VG.Impl.Mont.X86.Comb.powerDigits VG.Impl.Mont.X86.Comb.seq
  simp only [List.foldr_cons,List.foldr_nil]
  refine WP.seq (WP.mono (context_mul_ok C (o := 6) (a := 6) (b := 6)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [A]; exact Nat.mod_lt _ (by have := C.gt_one; omega_using [this]))) fun u ⟨Cu,Ku,lu,Vu⟩ => ?_)
  have Au := VG.Proof.Rsa.FixedBaseComb.mont_square_encoded C.coprime lu A Vu
  have Eu := context_slot_val32 C (i := 8) (by decide) ew (by decide) (by decide) (by decide) Ku
  have Tu := T.op (table_layout h) C (by decide) Ku
  refine WP.seq (WP.mono (VG.Proof.Mont.X86.Comb.digit_ok Cu.scr eb dp cover sz)
    fun v ⟨Ov,Vv,Kv⟩ => ?_)
  have Cv := Cu.outside_keep Kv (by decide) (by decide) Ov (.inr (by simp [slot])) (by decide)
  have Tv := Tu.outside (table_layout h) Cu.scr Ov (by
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide)
  have Av : wordsVal v.mem base (slot n 6) n = Spec.Rsa.powMod g (2*E) m * 2^(64*n)%m := by
    rw [Ov.wordsVal (.inr (by have := slot_header n 6; omega_using [this])) (by
      rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide),Au]
  have Ev : val32 v.mem base (slot n 8) (expWords e) = val32 s.mem base (slot n 8) (expWords e) := by
    rw [Ov.val32 (.inr (by have := slot_header n 8; omega_using [this])) (by
      rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide),Eu]
  rw [Eu] at Vv
  refine WP.seq (WP.mono (shiftOne_ok Cv.scr ep eb) fun w ⟨Ow,Vw,Kw⟩ => ?_)
  have Cw := Cv.outside_keep Kw (by decide) (by decide) Ow (by
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide)
    (by have := slot_header n 8; omega_using [this])
  have Tw := Tv.outside (table_layout h) Cv.scr Ow (by
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide)
  have Ww : w32 w.mem base 4 = partialDigit (rows e) (val32 s.mem base (slot n 8) (expWords e)) 5 := by
    rw [Ow.w32 (.inl (by have := slot_header n 8; omega_using [this])) (by decide),Vv]
    rfl
  have Aw : wordsVal w.mem base (slot n 6) n = Spec.Rsa.powMod g (2*E) m * 2^(64*n)%m := by
    rw [Ow.wordsVal (by
      rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide) (by
      rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide),Av]
  change val32 w.mem base (slot n 8) (expWords e) = val32 v.mem base (slot n 8) (expWords e)*2%2^(32*expWords e) at Vw
  rw [Ev] at Vw
  refine WP.block_nil ⟨Cw,Tw,Aw,Vw,Ww,?_,?_⟩
  · have ou : Outs base (powerRanges n e) s.mem u.mem := Ku.mem.mono (by
      intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl <;> simp [powerRanges,contextMod,accLen,words] <;> omega_using [])
    have ov := Outs.of_outside Ov (rs := powerRanges n e) (by simp [powerRanges])
    have ow := Outs.of_outside Ow (rs := powerRanges n e) (by simp [powerRanges,expWords,rows])
    exact (ou.trans ov).trans ow
  · exact (((OpKeep.keeps Ku).mono (by decide)).trans (Kv.mono (by decide))).trans Kw

end VG.Proof.Dsa.X86.Comb
