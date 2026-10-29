module

public import VerifiedGarbage.Impl.Words.RISCV64.CopyFast
import VerifiedGarbage.Proof.Framework.RISCV64.Loops
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep

/-!
# Copies a doubleword at a time when the buffers allow it (RISC-V)

Untrusted: everything here is checked by Lean. `copyAny_ok`: `copyAny`
copies `N` bytes, a nonzero multiple of 8, between separate buffers, writing
only the destination and changing only its registers, as `copyLoop_ok` says
of `copyLoop`: through `copyLoopW_ok` when both pointers are 8-byte aligned,
and `copyLoop_ok` otherwise.
-/

@[expose] public section

namespace VG.RISCV64

open VG.Impl.Words.RISCV64

/-- Byte `j < 8` of the doubleword at `a`. -/
theorem byte_readW (m : Mem) (a : Addr) {j : Nat} (hj : j < 8) :
    m (a + BitVec.ofNat 64 j) = (m.readW a 64).extractLsb' (8 * j) 8 := by
  rw [← Mem.extractLsb'_read m a (n := 8) hj]
  simp only [Mem.readW]
  rfl

/-- A doubleword copied from `b` to `a`, byte by byte. -/
theorem writeW_readW_byte (m m' : Mem) (a b : Addr) {j : Nat} (hj : j < 8) :
    (m.writeW a (m'.readW b 64)) (a + BitVec.ofNat 64 j) = m' (b + BitVec.ofNat 64 j) := by
  rw [byte_readW (m.writeW a (m'.readW b 64)) a hj, Mem.readW_writeW_self64, ← byte_readW m' b hj]

theorem toNat_add_mul8 {p : Addr} {k : Nat} (hal : p.toNat % 8 = 0) (hk : 8 * k < 2 ^ 64) :
    (p + BitVec.ofNat 64 (8 * k)).toNat % 8 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * k) hk]
  have := p.isLt
  omega

/-- After `k` doublewords of `copyLoopW` from `s₀`. -/
structure CopyWInv (tmp src dst cnt : Reg) (N : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  le : k < N
  hsrc : s.gpr src = s₀.gpr src + BitVec.ofNat 64 (8 * k)
  hdst : s.gpr dst = s₀.gpr dst + BitVec.ofNat 64 (8 * k)
  hcnt : s.gpr cnt = BitVec.ofNat 64 (N - k)
  copied : ∀ j < 8 * k, s.mem (s₀.gpr dst + BitVec.ofNat 64 j) = s₀.mem (s₀.gpr src + BitVec.ofNat 64 j)
  frame : Frame [⟨s₀.gpr dst, 8 * N⟩] s₀.mem s.mem
  keep : Keep [tmp, src, dst, cnt] s₀ s

/-- `copyLoopW` copies `N ≥ 1` doublewords between separate, 8-byte aligned
buffers. -/
theorem copyLoopW_ok {tmp src dst cnt : Reg} (h1 : tmp ≠ src) (h2 : tmp ≠ dst) (h3 : tmp ≠ cnt)
    (h4 : src ≠ dst) (h5 : src ≠ cnt) (h6 : dst ≠ cnt) (s : State) {N : Nat} (hN : 0 < N)
    (hN' : 8 * N < 2 ^ 64) (hc : s.gpr cnt = BitVec.ofNat 64 N)
    (has : (s.gpr src).toNat % 8 = 0) (had : (s.gpr dst).toNat % 8 = 0)
    (hr : ∀ i < N, InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 (8 * i)) 8)
    (hw : ∀ i < N, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 (8 * i)) 8)
    (hsep : Mem.Sep (s.gpr dst) (8 * N) (s.gpr src) (8 * N)) :
    WP isa (copyLoopW tmp src dst cnt) s fun t =>
      (∀ i < 8 * N, t.mem (s.gpr dst + BitVec.ofNat 64 i) = s.mem (s.gpr src + BitVec.ofNat 64 i)) ∧
      Frame [⟨s.gpr dst, 8 * N⟩] s.mem t.mem ∧ Keep [tmp, src, dst, cnt] s t := by
  refine WP.loop (M := isa) (fun n t => ∃ k, n = N - k ∧ CopyWInv tmp src dst cnt N s k t) ?_ N s
    ⟨0, rfl, hN, by simp, by simp, by simp [hc], fun j hj => absurd hj (by omega), Frame.refl _ _,
      Keep.refl _ _⟩
  rintro n t ⟨k, rfl, I⟩
  have hk := I.le
  have hsrc : InRegions (t.rd ++ t.wr) (s.gpr src + BitVec.ofNat 64 (8 * k)) 8 := by
    rw [I.keep.2.1, I.keep.2.2]; exact hr k hk
  have hdst : InRegions t.wr (s.gpr dst + BitVec.ofNat 64 (8 * k)) 8 := by
    rw [I.keep.2.2]; exact hw k hk
  have als : (s.gpr src + BitVec.ofNat 64 (8 * k)).toNat % 8 = 0 := toNat_add_mul8 has (by omega)
  have ald : (s.gpr dst + BitVec.ofNat 64 (8 * k)).toNat % 8 = 0 := toNat_add_mul8 had (by omega)
  -- The doubleword read is the source's: the destination is elsewhere.
  have hword : t.mem.readW (s.gpr src + BitVec.ofNat 64 (8 * k)) 64 =
      s.mem.readW (s.gpr src + BitVec.ofNat 64 (8 * k)) 64 :=
    I.frame.readW (Region.contains_self _ _) (fun r hr x h₁ h₂ => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains] at h₁ h₂
      rw [Offset.toNat_sub_add x (s.gpr src) (by omega)] at h₁
      exact hsep x h₂ (by omega)) (by decide)
  have e : WP isa (.block [.load .d tmp src 0, .store .d tmp dst 0, .addi src src 8, .addi dst dst 8,
      .addi cnt cnt (-1)]) t fun u =>
      u.mem = t.mem.writeW (s.gpr dst + BitVec.ofNat 64 (8 * k))
        (t.mem.readW (s.gpr src + BitVec.ofNat 64 (8 * k)) 64) ∧
      u.gpr src = s.gpr src + BitVec.ofNat 64 (8 * k) + 8#64 ∧
      u.gpr dst = s.gpr dst + BitVec.ofNat 64 (8 * k) + 8#64 ∧
      u.gpr cnt = BitVec.ofNat 64 (N - k) - 1#64 := by
    mrun [I.hsrc, I.hdst, I.hcnt, hsrc, hdst, als, ald, h1, h2, h3, h4, h5, h6, Ne.symm h1, Ne.symm h2,
      Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6]
  refine WP.mono (WP.keep [tmp, src, dst, cnt] e (by
      simp [writesOnly, Code.allInstrs_eq, instrs, dstOf]) rfl) fun u ⟨⟨um, us, ud, uc⟩, uk⟩ => ?_
  have hc' : u.gpr cnt = BitVec.ofNat 64 (N - (k + 1)) := by
    rw [uc, show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]
    congr 1
  have hcopied : ∀ j < 8 * (k + 1), u.mem (s.gpr dst + BitVec.ofNat 64 j) =
      s.mem (s.gpr src + BitVec.ofNat 64 j) := by
    intro j hj
    rw [um]
    by_cases e : 8 * k ≤ j
    · obtain ⟨r, hr, rfl⟩ : ∃ r, r < 8 ∧ j = 8 * k + r := ⟨j - 8 * k, by omega, by omega⟩
      rw [← Offset.add_add, writeW_readW_byte _ _ _ _ hr, byte_readW t.mem _ hr, hword, ← byte_readW s.mem _ hr,
        Offset.add_add]
    · have hsep' : Mem.Sep (s.gpr dst + BitVec.ofNat 64 j) 1 (s.gpr dst + BitVec.ofNat 64 (8 * k)) 8 :=
        Offset.sep _ (.inl (by omega)) (by omega) (by omega)
      have := Mem.read_write_sep (m := t.mem) (v := (t.mem.readW (s.gpr src + BitVec.ofNat 64 (8 * k)) 64))
        hsep' (by decide)
      rw [read_one, read_one] at this
      rw [show t.mem.writeW _ _ = t.mem.write _ 8 _ from (write_eight _ _ _).symm, this,
        I.copied j (by omega)]
  have hframe : Frame [⟨s.gpr dst, 8 * N⟩] s.mem u.mem := by
    rw [um]
    exact I.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  have hkeep : Keep [tmp, src, dst, cnt] s u := (I.keep.trans uk).mono (by simp)
  rw [Steps.eval_nonzero, hc', ofNat_bne_zero' (by omega)]
  by_cases e : k + 1 = N
  · exact .inl ⟨by simp [e], fun i hi => hcopied i (by omega), hframe, hkeep⟩
  · refine .inr ⟨by simp; omega, N - (k + 1), by omega, k + 1, rfl, by omega, ?_, ?_, hc', hcopied, hframe,
      hkeep⟩
    · rw [us, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, Offset.add_add]; congr 2
    · rw [ud, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, Offset.add_add]; congr 2

/-- Both pointers are 8-byte aligned exactly when their `or`'s low three
bits are zero. -/
theorem or_and7 (a b : BitVec 64) :
    ((a ||| b) &&& BitVec.ofInt 64 7 == 0) = decide (a.toNat % 8 = 0 ∧ b.toNat % 8 = 0) := by
  have h7 : BitVec.ofInt 64 7 = BitVec.ofNat 64 (2 ^ 3 - 1) := rfl
  have e : ((a ||| b) &&& BitVec.ofInt 64 7).toNat = (a.toNat ||| b.toNat) % 2 ^ 3 := by
    rw [h7, BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := 2 ^ 3 - 1) (by decide), Nat.and_two_pow_sub_one_eq_mod]
  rw [Nat.or_mod_two_pow] at e
  by_cases h : a.toNat % 8 = 0 ∧ b.toNat % 8 = 0
  · rw [decide_eq_true h]
    apply beq_iff_eq.mpr
    apply BitVec.eq_of_toNat_eq
    rw [e, show (2 : Nat) ^ 3 = 8 from rfl, h.1, h.2]; rfl
  · rw [decide_eq_false h]
    apply beq_eq_false_iff_ne.mpr
    intro hz
    have := congrArg BitVec.toNat hz
    rw [e, show (2 : Nat) ^ 3 = 8 from rfl, show (0 : BitVec 64).toNat = 0 from rfl, Nat.or_eq_zero_iff] at this
    exact h this

/-- `copyAny` copies `N` bytes, a nonzero multiple of 8, between separate
buffers. -/
theorem copyAny_ok {tmp src dst cnt : Reg} (h1 : tmp ≠ src) (h2 : tmp ≠ dst) (h3 : tmp ≠ cnt)
    (h4 : src ≠ dst) (h5 : src ≠ cnt) (h6 : dst ≠ cnt) (s : State) {N : Nat} (hN : 0 < N)
    (hN' : N < 2 ^ 64) (h8 : N % 8 = 0) (hc : s.gpr cnt = BitVec.ofNat 64 N)
    (hr : ∀ i < N, InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < N, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 i) 1)
    (hr8 : ∀ i < N / 8, (s.gpr src).toNat % 8 = 0 →
      InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 (8 * i)) 8)
    (hw8 : ∀ i < N / 8, (s.gpr dst).toNat % 8 = 0 → InRegions s.wr (s.gpr dst + BitVec.ofNat 64 (8 * i)) 8)
    (hsep : Mem.Sep (s.gpr dst) N (s.gpr src) N) :
    WP isa (copyAny tmp src dst cnt) s fun t =>
      (∀ i < N, t.mem (s.gpr dst + BitVec.ofNat 64 i) = s.mem (s.gpr src + BitVec.ofNat 64 i)) ∧
      Frame [⟨s.gpr dst, N⟩] s.mem t.mem ∧ Keep [tmp, src, dst, cnt] s t := by
  have e : WP isa (.block [.logic .or tmp src dst, .logicImm .and tmp tmp 7]) s fun u =>
      u.gpr tmp = (s.gpr src ||| s.gpr dst) &&& BitVec.ofInt 64 7 ∧ u.mem = s.mem := by
    mrun [h1, h2, Ne.symm h1, Ne.symm h2]
  refine WP.seq (WP.mono (WP.keep [tmp] e (by simp [writesOnly, Code.allInstrs_eq, instrs, dstOf]) rfl)
    fun u ⟨⟨ut, um⟩, uk⟩ => ?_)
  have us : u.gpr src = s.gpr src := uk.gpr (by simp [Ne.symm h1])
  have ud : u.gpr dst = s.gpr dst := uk.gpr (by simp [Ne.symm h2])
  have uc : u.gpr cnt = s.gpr cnt := uk.gpr (by simp [Ne.symm h3])
  have urd : u.rd = s.rd := uk.2.1
  have uwr : u.wr = s.wr := uk.2.2
  have fin : ∀ t, Keep [tmp, src, dst, cnt] u t → Keep [tmp, src, dst, cnt] s t := fun t ht =>
    (uk.trans ht).mono (by simp)
  by_cases hal : (s.gpr src).toNat % 8 = 0 ∧ (s.gpr dst).toNat % 8 = 0
  · refine WP.ite true (by rw [Steps.eval_zero, ut, or_and7, decide_eq_true hal]) (fun _ => ?_)
      fun h => by cases h
    have e2 : WP isa (.block [.shift .srl .d cnt cnt 3]) u fun v =>
        v.gpr cnt = u.gpr cnt >>> 3 ∧ v.mem = u.mem := by
      mrun []
    refine WP.seq (WP.mono (WP.keep [cnt] e2 (by simp [writesOnly, Code.allInstrs_eq, instrs, dstOf]) rfl)
      fun v ⟨⟨vc, vm⟩, vk⟩ => ?_)
    have vs : v.gpr src = s.gpr src := (vk.gpr (by simp [h5])).trans us
    have vd : v.gpr dst = s.gpr dst := (vk.gpr (by simp [h6])).trans ud
    have vrd : v.rd = s.rd := vk.2.1.trans urd
    have vwr : v.wr = s.wr := vk.2.2.trans uwr
    have vc' : v.gpr cnt = BitVec.ofNat 64 (N / 8) := by
      rw [vc, uc, hc]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN',
        Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]
    have hNe : 8 * (N / 8) = N := by omega
    refine WP.mono (copyLoopW_ok h1 h2 h3 h4 h5 h6 v (N := N / 8) (by omega) (by omega) vc'
      (by rw [vs]; exact hal.1) (by rw [vd]; exact hal.2)
      (fun i hi => by rw [vs, vrd, vwr]; exact hr8 i hi hal.1)
      (fun i hi => by rw [vd, vwr]; exact hw8 i hi hal.2)
      (by rw [vs, vd, hNe]; exact hsep)) fun t ⟨tc, tf, tk⟩ => ?_
    rw [vs, vd, vm, um, hNe] at tc
    rw [vd, vm, um, hNe] at tf
    exact ⟨tc, tf, fin t ((vk.trans tk).mono (by simp))⟩
  · refine WP.ite false (by rw [Steps.eval_zero, ut, or_and7, decide_eq_false hal]) (fun h => by cases h)
      fun _ => ?_
    refine WP.mono (copyLoop_ok h1 h2 h3 h4 h5 h6 u hN hN' (by rw [uc]; exact hc)
      (fun i hi => by rw [us, urd, uwr]; exact hr i hi) (fun i hi => by rw [ud, uwr]; exact hw i hi)
      (by rw [us, ud]; exact hsep)) fun t ⟨tc, tf, tk⟩ => ?_
    rw [us, ud, um] at tc
    rw [ud, um] at tf
    exact ⟨tc, tf, fin t tk⟩

end VG.RISCV64
