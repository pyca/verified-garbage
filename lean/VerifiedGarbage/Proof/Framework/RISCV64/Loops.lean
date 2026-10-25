module

public import VerifiedGarbage.Impl.Words.RISCV64.Loops
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad

/-!
# Loops over buffers (RISC-V)

Untrusted: everything here is checked by Lean. `copyLoop_ok`: `copyLoop`
copies `N ≥ 1` bytes between separate buffers, writing only the
destination; `fillLoop_ok`: `fillLoop` writes `v` into the `N ≥ 1` doublewords
at an 8-byte aligned pointer, and nothing else. Each changes only its registers.
-/

@[expose] public section

namespace VG.RISCV64

open VG.Impl.Words.RISCV64

/-- After `k` bytes of `copyLoop` from `s₀`. -/
structure CopyInv (tmp src dst cnt : Reg) (N : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  le : k < N
  hsrc : s.gpr src = s₀.gpr src + BitVec.ofNat 64 k
  hdst : s.gpr dst = s₀.gpr dst + BitVec.ofNat 64 k
  hcnt : s.gpr cnt = BitVec.ofNat 64 (N - k)
  copied : ∀ j < k, s.mem (s₀.gpr dst + BitVec.ofNat 64 j) = s₀.mem (s₀.gpr src + BitVec.ofNat 64 j)
  frame : Frame [⟨s₀.gpr dst, N⟩] s₀.mem s.mem
  keep : Keep [tmp, src, dst, cnt] s₀ s

theorem ofNat_bne_zero' {a : Nat} (ha : a < 2 ^ 64) :
    (BitVec.ofNat 64 a != (0 : BitVec 64)) = !decide (a = 0) := by
  by_cases h : a = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 a ≠ 0 := by
      intro e
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_ofNat, show BitVec.toNat (0 : BitVec 64) = 0 from rfl] at this
      omega
    rw [decide_eq_false h, Bool.not_false]
    exact bne_iff_ne.mpr this

theorem copyLoop_ok {tmp src dst cnt : Reg} (h1 : tmp ≠ src) (h2 : tmp ≠ dst) (h3 : tmp ≠ cnt)
    (h4 : src ≠ dst) (h5 : src ≠ cnt) (h6 : dst ≠ cnt) (s : State) {N : Nat} (hN : 0 < N)
    (hN' : N < 2 ^ 64) (hc : s.gpr cnt = BitVec.ofNat 64 N)
    (hr : ∀ i < N, InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < N, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 i) 1)
    (hsep : Mem.Sep (s.gpr dst) N (s.gpr src) N) :
    WP isa (copyLoop tmp src dst cnt) s fun t =>
      (∀ i < N, t.mem (s.gpr dst + BitVec.ofNat 64 i) = s.mem (s.gpr src + BitVec.ofNat 64 i)) ∧
      Frame [⟨s.gpr dst, N⟩] s.mem t.mem ∧ Keep [tmp, src, dst, cnt] s t := by
  refine WP.loop (M := isa) (fun n t => ∃ k, n = N - k ∧ CopyInv tmp src dst cnt N s k t) ?_ N s
    ⟨0, rfl, hN, by simp, by simp, by simp [hc], fun j hj => absurd hj (by omega), Frame.refl _ _,
      Keep.refl _ _⟩
  rintro n t ⟨k, rfl, I⟩
  have hk := I.le
  have hsrc : InRegions (t.rd ++ t.wr) (s.gpr src + BitVec.ofNat 64 k) 1 := by
    rw [I.keep.2.1, I.keep.2.2]; exact hr k hk
  have hdst : InRegions t.wr (s.gpr dst + BitVec.ofNat 64 k) 1 := by
    rw [I.keep.2.2]; exact hw k hk
  -- The byte read is the source's: the destination is elsewhere.
  have hbyte : t.mem (s.gpr src + BitVec.ofNat 64 k) = s.mem (s.gpr src + BitVec.ofNat 64 k) :=
    I.frame _ fun r hr hc' => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hsep (s.gpr src + BitVec.ofNat 64 k) (by simp only [Region.Contains] at hc'; omega)
        (by rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)
  have e : WP isa (.block [.load .b tmp src 0, .store .b tmp dst 0, .addi src src 1, .addi dst dst 1,
      .addi cnt cnt (-1)]) t fun u =>
      u.mem = t.mem.write (s.gpr dst + BitVec.ofNat 64 k) 1 (t.mem (s.gpr src + BitVec.ofNat 64 k)) ∧
      u.gpr src = s.gpr src + BitVec.ofNat 64 k + 1#64 ∧ u.gpr dst = s.gpr dst + BitVec.ofNat 64 k + 1#64 ∧
      u.gpr cnt = BitVec.ofNat 64 (N - k) - 1#64 := by
    mrun [I.hsrc, I.hdst, I.hcnt, hsrc, hdst, h1, h2, h3, h4, h5, h6, Ne.symm h1, Ne.symm h2, Ne.symm h3,
      Ne.symm h4, Ne.symm h5, Ne.symm h6]
    rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
  refine WP.mono (WP.keep [tmp, src, dst, cnt] e (by
      simp [writesOnly, Code.allInstrs_eq, instrs, dstOf]) rfl) fun u ⟨⟨um, us, ud, uc⟩, uk⟩ => ?_
  have hc' : u.gpr cnt = BitVec.ofNat 64 (N - (k + 1)) := by
    rw [uc, show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]
    congr 1
  have hcopied : ∀ j < k + 1, u.mem (s.gpr dst + BitVec.ofNat 64 j) = s.mem (s.gpr src + BitVec.ofNat 64 j) := by
    intro j hj
    rw [um, ← ByteLoad.writeW_byte, WriteBytes.writeW8_apply]
    by_cases e : j = k
    · subst e; rw [ite_eq_left rfl, hbyte]
    · rw [ite_eq_right (Offset.add_ofNat_ne _ (by omega) (by omega) e), I.copied j (by omega)]
  have hframe : Frame [⟨s.gpr dst, N⟩] s.mem u.mem := by
    rw [um]
    exact I.frame.write (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  have hkeep : Keep [tmp, src, dst, cnt] s u := (I.keep.trans uk).mono (by simp)
  rw [Steps.eval_nonzero, hc', ofNat_bne_zero' (by omega)]
  by_cases e : k + 1 = N
  · refine .inl ⟨by simp [e], fun i hi => hcopied i (by omega), hframe, hkeep⟩
  · refine .inr ⟨by simp; omega, N - (k + 1), by omega, k + 1, rfl, by omega, ?_, ?_, hc', hcopied, hframe, hkeep⟩
    · rw [us, show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.add_add]
    · rw [ud, show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.add_add]

/-- After `k` doublewords of `fillLoop` from `s₀`. -/
structure FillInv (v ptr cnt : Reg) (N : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  le : k < N
  hptr : s.gpr ptr = s₀.gpr ptr + BitVec.ofNat 64 (8 * k)
  hcnt : s.gpr cnt = BitVec.ofNat 64 (N - k)
  filled : ∀ j < k, s.mem.readW (s₀.gpr ptr + BitVec.ofNat 64 (8 * j)) 64 = s₀.gpr v
  frame : Frame [⟨s₀.gpr ptr, 8 * N⟩] s₀.mem s.mem
  keep : Keep [ptr, cnt] s₀ s

theorem fillLoop_ok {v ptr cnt : Reg} (h3 : ptr ≠ cnt) (h1 : v ≠ ptr) (h2 : v ≠ cnt) (s : State)
    {N : Nat} (hN : 0 < N) (hN' : 8 * N < 2 ^ 64) (hc : s.gpr cnt = BitVec.ofNat 64 N)
    (hal : (s.gpr ptr).toNat % 8 = 0)
    (hw : ∀ i < N, InRegions s.wr (s.gpr ptr + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (fillLoop v ptr cnt) s fun t =>
      (∀ j < N, t.mem.readW (s.gpr ptr + BitVec.ofNat 64 (8 * j)) 64 = s.gpr v) ∧
      Frame [⟨s.gpr ptr, 8 * N⟩] s.mem t.mem ∧ Keep [ptr, cnt] s t := by
  refine WP.loop (M := isa) (fun n t => ∃ k, n = N - k ∧ FillInv v ptr cnt N s k t) ?_ N s
    ⟨0, rfl, hN, by simp, by simp [hc], fun j hj => absurd hj (by omega), Frame.refl _ _, Keep.refl _ _⟩
  rintro n t ⟨k, rfl, I⟩
  have hk := I.le
  have hdst : InRegions t.wr (s.gpr ptr + BitVec.ofNat 64 (8 * k)) 8 := by
    rw [I.keep.2.2]; exact hw k hk
  have hal' : (s.gpr ptr + BitVec.ofNat 64 (8 * k)).toNat % 8 = 0 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * k) (by omega)]
    have := (s.gpr ptr).isLt
    omega
  have e : WP isa (.block [.store .d v ptr 0, .addi ptr ptr 8, .addi cnt cnt (-1)]) t fun u =>
      u.mem = t.mem.writeW (s.gpr ptr + BitVec.ofNat 64 (8 * k)) (t.gpr v) ∧
      u.gpr ptr = s.gpr ptr + BitVec.ofNat 64 (8 * k) + 8#64 ∧
      u.gpr cnt = BitVec.ofNat 64 (N - k) - 1#64 := by
    mrun [I.hptr, I.hcnt, hdst, hal', h3, Ne.symm h3]
  refine WP.mono (WP.keep [ptr, cnt] e (by
      simp [writesOnly, Code.allInstrs_eq, instrs, dstOf]) rfl) fun u ⟨⟨um, up, uc⟩, uk⟩ => ?_
  have hc' : u.gpr cnt = BitVec.ofNat 64 (N - (k + 1)) := by
    rw [uc, show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]
    congr 1
  have hframe : Frame [⟨s.gpr ptr, 8 * N⟩] s.mem u.mem := by
    rw [um]
    exact I.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  have hkeep : Keep [ptr, cnt] s u := (I.keep.trans uk).mono (by simp)
  have hfill : ∀ j < k + 1, u.mem.readW (s.gpr ptr + BitVec.ofNat 64 (8 * j)) 64 = s.gpr v := by
    intro j hj
    rw [um, ← I.keep.gpr (r := v) (by simp [h1, h2])]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide),
        I.keep.gpr (r := v) (by simp [h1, h2])]
      exact I.filled j hj
    · exact Mem.readW_writeW_self64 _ _ _
  rw [Steps.eval_nonzero, hc', ofNat_bne_zero' (by omega)]
  by_cases e : k + 1 = N
  · exact .inl ⟨by simp [e], fun j hj => hfill j (by omega), hframe, hkeep⟩
  · refine .inr ⟨by simp; omega, N - (k + 1), by omega, k + 1, rfl, by omega, ?_, hc', hfill, hframe, hkeep⟩
    rw [up, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, Offset.add_add]
    congr 2

end VG.RISCV64
