module

public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.VerifyHash
public import VerifiedGarbage.Proof.Ecdsa.Verify.Hash
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
public import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.ByteStep
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Impl.Ecdsa.PPC64LE.VerifyHash

/-!
# ECDSA verification of the hash function's output on PPC64LE: the conversion

Untrusted: everything here is checked by Lean. `convert_ok`: `convert len
wide` writes `fixedDigest len wide` of the hash at `r4` (`r5` bytes) to the
first `len` bytes of the buffer at `r8`, changing only the buffer's 80 bytes
and the registers `r4`, `r5` and `r9`–`r12`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.PPC64LE.Hash

open VG VG.PPC64LE VG.Impl.Ecdsa.PPC64LE.VerifyHash

variable {len : Nat} {s : State}

/-- What `convert` needs of its state: the hash's bytes readable, the
buffer's 80 bytes writable and apart from them, neither wrapping around. -/
structure CPre (len : Nat) (s : State) : Prop where
  len1 : 0 < len
  len66 : len ≤ 66
  rd : ∀ i < (s.gpr .r5).toNat, InRegions (s.rd ++ s.wr) (s.gpr .r4 + BitVec.ofNat 64 i) 1
  wr : ∀ i < 80, InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 i) 1
  sep : (⟨s.gpr .r8, 80⟩ : Region).Disjoint ⟨s.gpr .r4, (s.gpr .r5).toNat⟩
  fitB : (s.gpr .r8).toNat + 80 ≤ 2 ^ 64
  fitD : (s.gpr .r4).toNat + (s.gpr .r5).toNat ≤ 2 ^ 64

/-- The hash. -/
abbrev hashOf (s : State) : List Byte := Spec.Ecdsa.bytesAt s.mem (s.gpr .r4) (s.gpr .r5).toNat

/-- The registers `convert` writes. -/
abbrev convRegs : List Reg := [.r4, .r5, .r9, .r10, .r11, .r12]

/-- What `convert` leaves. -/
structure CPost (len : Nat) (wide : Bool) (s t : State) : Prop where
  buf : ∀ i < len, t.mem (s.gpr .r8 + BitVec.ofNat 64 i) = (fixedDigest len wide (hashOf s)).getD i 0
  frame : Frame [⟨s.gpr .r8, 80⟩] s.mem t.mem
  keep : Keep convRegs s t
  sp : t.sp = s.sp

/-! ## Whether the hash is short -/

/-- The borrow of `x - L`, for `L < 2⁶³`: the sign bit of `(x ⊕ (x - L)) ∧ (x - L)`. -/
theorem borrow_bne (x : BitVec 64) {L : Nat} (hL : L < 2 ^ 63) :
    ((((x ^^^ (x - BitVec.ofNat 64 L)) &&& (x - BitVec.ofNat 64 L)) >>> 63) != 0) =
      decide (x.toNat < L) := by
  have hx := x.isLt
  have hd : (x - BitVec.ofNat 64 L).toNat = (2 ^ 64 - L + x.toNat) % 2 ^ 64 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := L) (by omega)]
  have key : ∀ y : BitVec 64, (y >>> 63 != 0) = y.msb := by
    intro y
    rw [BitVec.msb_eq_decide]
    have hy := y.isLt
    by_cases h : 2 ^ 63 ≤ y.toNat
    · rw [decide_eq_true (by simpa using h)]
      refine bne_iff_ne.mpr fun e => ?_
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at this
      rw [show (0 : BitVec 64).toNat = 0 from rfl] at this
      omega
    · rw [decide_eq_false (by simpa using h)]
      refine bne_eq_false_iff_eq.mpr (BitVec.eq_of_toNat_eq ?_)
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      rw [show (0 : BitVec 64).toNat = 0 from rfl]
      omega
  rw [key, BitVec.msb_and, BitVec.msb_xor, BitVec.msb_eq_decide, BitVec.msb_eq_decide, hd]
  simp only [Nat.add_one_sub_one]
  by_cases h₁ : x.toNat < L
  · rw [decide_eq_true h₁]
    have : 2 ^ 63 ≤ (2 ^ 64 - L + x.toNat) % 2 ^ 64 := by
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    simp [this, show ¬ 2 ^ 63 ≤ x.toNat by omega]
  · rw [decide_eq_false h₁]
    have e : (2 ^ 64 - L + x.toNat) % 2 ^ 64 = x.toNat - L := by omega
    rw [e]
    by_cases h₂ : 2 ^ 63 ≤ x.toNat - L
    · simp [h₂, show 2 ^ 63 ≤ x.toNat by omega]
    · simp [h₂]

theorem isShort_ok (hp : CPre len s) :
    WP isa (.block (isShort len)) s fun s₁ =>
      (s₁.gpr .r12 != 0) = decide ((s.gpr .r5).toNat < len) ∧ Keep [.r11, .r12] s s₁ ∧ s₁.mem = s.mem := by
  have h66 := hp.len66
  refine wp_li (by omega) fun s₁ u₁ => wp_sub fun s₂ u₂ => wp_xor fun s₃ u₃ => wp_and fun s₄ u₄ =>
    wp_lsr (by decide) fun s₅ u₅ => wp_nil ⟨?_, ⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · have e5 : s₂.gpr .r5 = s.gpr .r5 := by rw [u₂.other _ (by decide), u₁.other _ (by decide)]
    rw [u₅.gpr, u₄.gpr, u₃.gpr, u₃.other .r12 (by decide), u₂.gpr, e5, u₁.gpr,
      u₁.other .r5 (by decide)]
    exact borrow_bne _ (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₅.other _ hr.2, u₄.other _ hr.2, u₃.other _ hr.1, u₂.other _ hr.2, u₁.other _ hr.1]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]

/-! ## Copies and stores of bytes -/

/-- Code keeps the permissions and the stack pointer. -/
theorem WP.rdwr {c : Prog isa} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.rdwr he⟩

/-- Bytes `0 … k - 1` copied. -/
structure CopyI (src dst : Reg) (soff doff n : Nat) (s : State) (k : Nat) (s' : State) : Prop where
  keep : Keep [.r9] s s'
  copied : ∀ j < k, s'.mem (s.gpr dst + BitVec.ofNat 64 (doff + j)) =
    s.mem (s.gpr src + BitVec.ofNat 64 (soff + j))
  frame : Frame [⟨s.gpr dst + BitVec.ofNat 64 doff, n⟩] s.mem s'.mem

/-- `copyBytes` through `r9`, from a source the writes do not overlap. -/
theorem copyBytes_ok {src dst : Reg} {soff doff n : Nat} (hs0 : src ≠ .r0) (hd0 : dst ≠ .r0)
    (hts : Reg.r9 ≠ src) (htd : Reg.r9 ≠ dst) (hs : soff + n ≤ 2 ^ 15) (hd : doff + n ≤ 2 ^ 15)
    (hr : ∀ i < n, InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 (soff + i)) 1)
    (hw : ∀ i < n, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 (doff + i)) 1)
    (hsep : ∀ i < n,
      ¬ (⟨s.gpr dst + BitVec.ofNat 64 doff, n⟩ : Region).Contains (s.gpr src + BitVec.ofNat 64 (soff + i)) 1) :
    WP isa (.block (copyBytes .r9 src dst soff doff n)) s (CopyI src dst soff doff n s n) := by
  refine wp_range_flatMap (M := isa) (CopyI src dst soff doff n s) (fun k s₁ hk h => ?_) n
    (Nat.le_refl _) s ⟨Keep.refl _ _, fun _ h => absurd h (by omega), Frame.refl _ _⟩
  have hsrc : s₁.gpr src = s.gpr src := h.keep.gpr (by simpa using Ne.symm hts)
  have hdst : s₁.gpr dst = s.gpr dst := h.keep.gpr (by simpa using Ne.symm htd)
  refine wp_lbz (a := s.gpr src + BitVec.ofNat 64 (soff + k)) hs0 (by omega) (by rw [hsrc])
    (by rw [h.keep.2.1, h.keep.2.2]; exact hr k hk) fun s₂ u₂ => ?_
  refine wp_stb (a := s.gpr dst + BitVec.ofNat 64 (doff + k)) hd0 (by omega)
    (by rw [u₂.other _ (Ne.symm htd), hdst]) (by rw [u₂.wr, h.keep.2.2]; exact hw k hk) fun s₃ g₃ =>
    wp_nil ?_
  have hv : (s₂.gpr .r9).setWidth 8 = s.mem (s.gpr src + BitVec.ofNat 64 (soff + k)) := by
    rw [u₂.gpr, h.frame _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hsep k hk]
    exact setWidth8_64 _
  have hm : s₃.mem = s₁.mem.writeW (s.gpr dst + BitVec.ofNat 64 (doff + k))
      (s.mem (s.gpr src + BitVec.ofNat 64 (soff + k))) := by
    rw [g₃.mem, hv, u₂.mem]
  refine ⟨⟨fun r hr => by
      rw [g₃.gpr, u₂.other r (by simpa using hr), h.keep.gpr hr],
    by rw [g₃.rd, u₂.rd, h.keep.2.1], by rw [g₃.wr, u₂.wr, h.keep.2.2]⟩, fun j hj => ?_, ?_⟩
  · rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [byte_writeW_ne' _ _ _ (by omega) (by omega) (by omega)]; exact h.copied j hj
    · exact byte_writeW_eq _ _ _ _
  · rw [hm]
    exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))

/-- Bytes `0 … k - 1` of the buffer zeroed. -/
structure ZeroI (s : State) (k : Nat) (s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  stored : ∀ j < k, s'.mem (s.gpr .r8 + BitVec.ofNat 64 j) = 0
  frame : Frame [⟨s.gpr .r8, 72⟩] s.mem s'.mem

/-- `zeroBytes`, with `r9` zero. -/
theorem zeroBytes_ok (h9 : s.gpr .r9 = 0)
    (hw : ∀ i < 72, InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 i) 1) :
    WP isa (.block zeroBytes) s (ZeroI s 72) := by
  refine wp_range_flatMap (M := isa) (ZeroI s) (fun k s₁ hk h => ?_) 72
    (Nat.le_refl _) s ⟨rfl, rfl, rfl, fun _ h => absurd h (by omega), Frame.refl _ _⟩
  refine wp_stb (a := s.gpr .r8 + BitVec.ofNat 64 k) (by decide) (by omega) (by rw [h.gpr])
    (by rw [h.wr]; exact hw k hk) fun s₂ g₂ => wp_nil ?_
  have hm : s₂.mem = s₁.mem.writeW (s.gpr .r8 + BitVec.ofNat 64 k) (0 : Byte) := by
    rw [g₂.mem, h.gpr, h9]; rfl
  refine ⟨by rw [g₂.gpr, h.gpr], by rw [g₂.rd, h.rd], by rw [g₂.wr, h.wr], fun j hj => ?_, ?_⟩
  · rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [byte_writeW_ne' _ _ _ (by omega) (by omega) (by omega)]; exact h.stored j hj
    · exact byte_writeW_eq _ _ _ _
  · rw [hm]
    exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))

/-- After `k` bytes of `copyLoop .r9 .r4 .r10 .r5` from `s₀`. -/
structure CopyInv (N : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  le : k < N
  hsrc : s.gpr .r4 = s₀.gpr .r4 + BitVec.ofNat 64 k
  hdst : s.gpr .r10 = s₀.gpr .r10 + BitVec.ofNat 64 k
  hcnt : s.gpr .r5 = BitVec.ofNat 64 (N - k)
  copied : ∀ j < k, s.mem (s₀.gpr .r10 + BitVec.ofNat 64 j) = s₀.mem (s₀.gpr .r4 + BitVec.ofNat 64 j)
  frame : Frame [⟨s₀.gpr .r10, N⟩] s₀.mem s.mem
  keep : Keep [.r9, .r4, .r10, .r5] s₀ s

theorem ofNat_bne_zero' {a : Nat} (ha : a < 2 ^ 64) :
    (BitVec.ofNat 64 a != (0 : BitVec 64)) = !decide (a = 0) := by
  rw [bne, ofNat_beq_zero ha]

/-- The loop's body, from the state after `k` bytes. -/
theorem copyBody_ok {N : Nat} {s₀ : State} {k : Nat} (I : CopyInv N s₀ k s)
    (hs : InRegions (s.rd ++ s.wr) (s₀.gpr .r4 + BitVec.ofNat 64 k) 1)
    (hd : InRegions s.wr (s₀.gpr .r10 + BitVec.ofNat 64 k) 1) :
    WP isa (.block [.lbz .r9 .r4 0, .stb .r9 .r10 0, .addi .r4 .r4 1, .addi .r10 .r10 1, .subi .r5 .r5 1])
      s fun u =>
      u.mem = s.mem.writeW (s₀.gpr .r10 + BitVec.ofNat 64 k) (s.mem (s₀.gpr .r4 + BitVec.ofNat 64 k)) ∧
      u.gpr .r4 = s₀.gpr .r4 + BitVec.ofNat 64 k + BitVec.ofNat 64 1 ∧
      u.gpr .r10 = s₀.gpr .r10 + BitVec.ofNat 64 k + BitVec.ofNat 64 1 ∧
      u.gpr .r5 = BitVec.ofNat 64 (N - k) - BitVec.ofNat 64 1 := by
  refine wp_lbz (a := s₀.gpr .r4 + BitVec.ofNat 64 k) (by decide) (by decide)
    (by rw [I.hsrc, BitVec.add_zero]) hs fun s₁ u₁ => ?_
  refine wp_stb (a := s₀.gpr .r10 + BitVec.ofNat 64 k) (by decide) (by decide)
    (by rw [u₁.other _ (by decide), I.hdst, BitVec.add_zero]) (by rw [u₁.wr]; exact hd) fun s₂ g₂ => ?_
  refine wp_addi (by decide) (by decide) fun s₃ u₃ => wp_addi (by decide) (by decide) fun s₄ u₄ =>
    wp_subi (by decide) (by decide) fun s₅ u₅ => wp_nil ⟨?_, ?_, ?_, ?_⟩
  · rw [u₅.mem, u₄.mem, u₃.mem, g₂.mem, u₁.gpr, setWidth8_64, u₁.mem]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂.gpr, u₁.other _ (by decide), I.hsrc]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), I.hdst]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), I.hcnt]

theorem copyLoop_ok (s : State) {N : Nat} (hN : 0 < N)
    (hN' : N < 2 ^ 64) (hc : s.gpr .r5 = BitVec.ofNat 64 N)
    (hr : ∀ i < N, InRegions (s.rd ++ s.wr) (s.gpr .r4 + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < N, InRegions s.wr (s.gpr .r10 + BitVec.ofNat 64 i) 1)
    (hsep : Mem.Sep (s.gpr .r10) N (s.gpr .r4) N) :
    WP isa (copyLoop .r9 .r4 .r10 .r5) s fun t =>
      (∀ i < N, t.mem (s.gpr .r10 + BitVec.ofNat 64 i) = s.mem (s.gpr .r4 + BitVec.ofNat 64 i)) ∧
      Frame [⟨s.gpr .r10, N⟩] s.mem t.mem ∧ Keep [.r9, .r4, .r10, .r5] s t := by
  refine WP.loop (M := isa) (fun n t => ∃ k, n = N - k ∧ CopyInv N s k t) ?_ N s
    ⟨0, rfl, hN, by simp, by simp, by simp [hc], fun j hj => absurd hj (by omega), Frame.refl _ _,
      Keep.refl _ _⟩
  rintro n t ⟨k, rfl, I⟩
  have hk := I.le
  have hsrc : InRegions (t.rd ++ t.wr) (s.gpr .r4 + BitVec.ofNat 64 k) 1 := by
    rw [I.keep.2.1, I.keep.2.2]; exact hr k hk
  have hdst : InRegions t.wr (s.gpr .r10 + BitVec.ofNat 64 k) 1 := by
    rw [I.keep.2.2]; exact hw k hk
  -- The byte read is the source's: the destination is elsewhere.
  have hbyte : t.mem (s.gpr .r4 + BitVec.ofNat 64 k) = s.mem (s.gpr .r4 + BitVec.ofNat 64 k) :=
    I.frame _ fun r hr hc' => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hsep (s.gpr .r4 + BitVec.ofNat 64 k) (by simp only [Region.Contains] at hc'; omega)
        (by rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)
  refine WP.mono (WP.keep [.r9, .r4, .r10, .r5] (copyBody_ok I hsrc hdst) (by
      simp [writesOnly, Code.allInstrs_eq, instrs, dstOf]) rfl) fun u ⟨⟨um, us, ud, uc⟩, uk⟩ => ?_
  have hc' : u.gpr .r5 = BitVec.ofNat 64 (N - (k + 1)) := by
    rw [uc, Offset.ofNat_sub_ofNat (by omega)]
    congr 1
  have hcopied : ∀ j < k + 1, u.mem (s.gpr .r10 + BitVec.ofNat 64 j) = s.mem (s.gpr .r4 + BitVec.ofNat 64 j) := by
    intro j hj
    rw [um, WriteBytes.writeW8_apply]
    by_cases e : j = k
    · subst e; rw [ite_eq_left rfl, hbyte]
    · rw [ite_eq_right (Offset.add_ofNat_ne _ (by omega) (by omega) e), I.copied j (by omega)]
  have hframe : Frame [⟨s.gpr .r10, N⟩] s.mem u.mem := by
    rw [um]
    exact I.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  have hkeep : Keep [.r9, .r4, .r10, .r5] s u := (I.keep.trans uk).mono (by simp)
  rw [eval_nonzero, hc', ofNat_bne_zero' (by omega)]
  by_cases e : k + 1 = N
  · exact .inl ⟨by simp [e], fun i hi => hcopied i (by omega), hframe, hkeep⟩
  · refine .inr ⟨by simp; omega, N - (k + 1), by omega, k + 1, rfl, by omega, ?_, ?_, hc', hcopied, hframe, hkeep⟩
    · rw [us, Offset.add_add]
    · rw [ud, Offset.add_add]

/-! ## The cases -/

theorem hash_byte {i : Nat} (hi : i < (s.gpr .r5).toNat) :
    (hashOf s).getD i 0 = s.mem (s.gpr .r4 + BitVec.ofNat 64 i) :=
  bytesAt_getD _ _ _ _ hi

/-- A byte of the buffer is not one of the hash's. -/
theorem buf_not_hash (hp : CPre len s) {x : Addr} (hx : (⟨s.gpr .r8, 80⟩ : Region).Contains x 1) {i : Nat}
    (hi : i < (s.gpr .r5).toNat) : x ≠ s.gpr .r4 + BitVec.ofNat 64 i := by
  rintro rfl
  exact hp.sep _ hx (Offset.contains_base _ (by omega) (by omega))

/-- The buffer's contents and what `convert` changes in memory. -/
structure MPost (len : Nat) (wide : Bool) (s t : State) : Prop where
  buf : ∀ i < len, t.mem (s.gpr .r8 + BitVec.ofNat 64 i) = (fixedDigest len wide (hashOf s)).getD i 0
  frame : Frame [⟨s.gpr .r8, 80⟩] s.mem t.mem

/-- A hash of at least `len` bytes: its leftmost `len`. -/
theorem long_ok {len : Nat} (wide : Bool) {s s₁ : State} (hp : CPre len s)
    (hk : Keep [.r11, .r12] s s₁) (hm : s₁.mem = s.mem) (hl : len ≤ (s.gpr .r5).toNat) :
    WP isa (.block (copyBytes .r9 .r4 .r8 0 0 len)) s₁ (MPost len wide s) := by
  have ha4 : s₁.gpr .r4 = s.gpr .r4 := hk.gpr (by decide)
  have ha8 : s₁.gpr .r8 = s.gpr .r8 := hk.gpr (by decide)
  have h66 := hp.len66
  refine WP.mono (copyBytes_ok (s := s₁) (src := .r4) (dst := .r8) (soff := 0)
    (doff := 0) (n := len) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega) ?_ ?_ ?_)
    fun t ht => ⟨fun i hi => ?_, ?_⟩
  · intro i hi; rw [hk.2.1, hk.2.2, ha4, Nat.zero_add]; exact hp.rd i (by omega)
  · intro i hi; rw [hk.2.2, ha8, Nat.zero_add]; exact hp.wr i (by omega)
  · intro i hi hc
    rw [ha8, ha4, Nat.zero_add, BitVec.add_zero] at hc
    exact buf_not_hash hp (contains_sub hc (by omega)) (i := i) (by omega) rfl
  · have hc := ht.copied i hi
    simp only [ha8, ha4, Nat.zero_add, hm] at hc
    rw [hc, ← hash_byte (by omega), fixedDigest, ite_eq_left_of_eq_true _ _ (eq_true (by rw [length_bytesAt]; exact hl)),
      List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]
  · intro x hx
    rw [ht.frame x fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [ha8, BitVec.add_zero]
      intro hc; exact hx _ (List.mem_singleton_self _) (contains_sub hc (by omega)), hm]

/-- The buffer holds the zeros and the hash (`tz`), in a state with the
entry's buffer pointer and permissions. -/
structure ZInv (len : Nat) (s u : State) : Prop where
  mem : ∀ j < 72, u.mem (s.gpr .r8 + BitVec.ofNat 64 j) = tz len (hashOf s) j
  frame : Frame [⟨s.gpr .r8, 80⟩] s.mem u.mem
  a8 : u.gpr .r8 = s.gpr .r8
  wr : u.wr = s.wr

/-- After `k` bytes of the shift. -/
structure SInv (len : Nat) (s : State) (k : Nat) (u : State) : Prop where
  mem : ∀ j < 72, u.mem (s.gpr .r8 + BitVec.ofNat 64 j) =
    if j < k then sh (tz len (hashOf s) j) (tz len (hashOf s) (j + 1)) else tz len (hashOf s) j
  frame : Frame [⟨s.gpr .r8, 80⟩] s.mem u.mem
  a8 : u.gpr .r8 = s.gpr .r8
  wr : u.wr = s.wr

theorem shift_ok (hp : CPre len s) (hl : (s.gpr .r5).toNat < len) {u : State} (hz : ZInv len s u) :
    WP isa (.block (shiftBytes len)) u (MPost len true s) := by
  have h66 := hp.len66
  have hB := hp.fitB
  refine WP.mono (wp_range_flatMap (M := isa) (SInv len s) (fun k u₁ hk h => ?_) len (Nat.le_refl _) u
    ⟨fun j hj => by simp only [Nat.not_lt_zero, ite_false]; exact hz.mem j hj, hz.frame, hz.a8, hz.wr⟩)
    fun t ht => ⟨fun i hi => ?_, ht.frame⟩
  · have hw : ∀ j < 80, InRegions u₁.wr (s.gpr .r8 + BitVec.ofNat 64 j) 1 := fun j hj => by
      rw [h.wr]; exact hp.wr j hj
    refine wp_lbz (a := s.gpr .r8 + BitVec.ofNat 64 k) (by decide) (by omega) (by rw [h.a8])
      (inRegions_wr (hw k (by omega))) fun u₂ g₂ => ?_
    refine wp_lbz (a := s.gpr .r8 + BitVec.ofNat 64 (k + 1)) (by decide) (by omega)
      (by rw [g₂.other .r8 (by decide), h.a8])
      (by rw [g₂.rd, g₂.wr]; exact inRegions_wr (hw (k + 1) (by omega))) fun u₃ g₃ => ?_
    refine wp_lsl (by decide) fun u₄ g₄ => wp_lsr (by decide) fun u₅ g₅ => wp_add fun u₆ g₆ => ?_
    refine wp_stb (a := s.gpr .r8 + BitVec.ofNat 64 k) (by decide) (by omega)
      (by rw [g₆.other .r8 (by decide), g₅.other .r8 (by decide), g₄.other .r8 (by decide),
        g₃.other .r8 (by decide), g₂.other .r8 (by decide), h.a8])
      (by rw [g₆.wr, g₅.wr, g₄.wr, g₃.wr, g₂.wr]; exact hw k (by omega)) fun u₇ g₇ => wp_nil ?_
    have hv : (u₆.gpr .r9).setWidth 8 = sh (tz len (hashOf s) k) (tz len (hashOf s) (k + 1)) := by
      rw [g₆.gpr, g₅.other .r9 (by decide), g₅.gpr, g₄.gpr, g₄.other .r10 (by decide), g₃.gpr,
        g₃.other .r9 (by decide), g₂.gpr, g₂.mem, h.mem k (by omega), h.mem (k + 1) (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega)]
      exact shift_byte _ _
    have hm : u₇.mem = u₁.mem.writeW (s.gpr .r8 + BitVec.ofNat 64 k)
        (sh (tz len (hashOf s) k) (tz len (hashOf s) (k + 1))) := by
      rw [g₇.mem, hv, g₆.mem, g₅.mem, g₄.mem, g₃.mem, g₂.mem]
    refine ⟨fun j hj => ?_, ?_, ?_, ?_⟩
    · rw [hm]
      by_cases e : j = k
      · subst e; rw [byte_writeW_eq, ite_eq_left (by omega)]
      · rw [byte_writeW_ne' _ _ _ (by omega) (by omega) e, h.mem j hj]
        by_cases hjk : j < k
        · rw [ite_eq_left hjk, ite_eq_left (by omega)]
        · rw [ite_eq_right hjk, ite_eq_right (by omega)]
    · rw [hm]
      exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    · rw [g₇.gpr, g₆.other .r8 (by decide), g₅.other .r8 (by decide), g₄.other .r8 (by decide),
        g₃.other .r8 (by decide), g₂.other .r8 (by decide), h.a8]
    · rw [g₇.wr, g₆.wr, g₅.wr, g₄.wr, g₃.wr, g₂.wr, h.wr]
  · rw [ht.mem i (by omega), ite_eq_left hi, fixed_short (by rw [length_bytesAt]; exact hl) true hi]
    rfl

theorem tail_ok (wide : Bool) (hp : CPre len s) (hl : (s.gpr .r5).toNat < len) {u : State}
    (hz : ZInv len s u) :
    WP isa (.block (if wide then shiftBytes len else [])) u (MPost len wide s) := by
  cases wide with
  | true => exact shift_ok hp hl hz
  | false =>
    refine wp_nil ⟨fun i hi => ?_, hz.frame⟩
    rw [hz.mem i (by have := hp.len66; omega), fixed_short (by rw [length_bytesAt]; exact hl) false hi]
    rfl

theorem short_ok (wide : Bool) (hp : CPre len s) {s₁ : State} (hk : Keep [.r11, .r12] s s₁)
    (hm : s₁.mem = s.mem) (hl : (s.gpr .r5).toNat < len) :
    WP isa (short len wide) s₁ (MPost len wide s) := by
  have h66 := hp.len66
  have hB := hp.fitB
  have ha4 : s₁.gpr .r4 = s.gpr .r4 := hk.gpr (by decide)
  have ha5 : s₁.gpr .r5 = s.gpr .r5 := hk.gpr (by decide)
  have ha8 : s₁.gpr .r8 = s.gpr .r8 := hk.gpr (by decide)
  unfold short
  refine WP.seq (wp_li (by decide) fun s₀ u₀ => WP.block_append (WP.mono (zeroBytes_ok (s := s₀) u₀.gpr
    (fun i hi => ?_)) fun s₂ h₂ => ?_))
  · rw [u₀.wr, hk.2.2, u₀.other .r8 (by decide), ha8]; exact hp.wr i (by omega)
  have g4 : s₂.gpr .r4 = s.gpr .r4 := by rw [h₂.gpr, u₀.other .r4 (by decide), ha4]
  have g5 : s₂.gpr .r5 = s.gpr .r5 := by rw [h₂.gpr, u₀.other .r5 (by decide), ha5]
  have g8 : s₂.gpr .r8 = s.gpr .r8 := by rw [h₂.gpr, u₀.other .r8 (by decide), ha8]
  refine wp_addi (by decide) (by omega) fun s₃ u₃ => wp_sub fun s₄ u₄ => wp_nil ?_
  have e4 : s₄.gpr .r4 = s.gpr .r4 := by rw [u₄.other _ (by decide), u₃.other _ (by decide), g4]
  have e5 : s₄.gpr .r5 = s.gpr .r5 := by rw [u₄.other _ (by decide), u₃.other _ (by decide), g5]
  have e8 : s₄.gpr .r8 = s.gpr .r8 := by rw [u₄.other _ (by decide), u₃.other _ (by decide), g8]
  have et10 : s₄.gpr .r10 = s.gpr .r8 + BitVec.ofNat 64 (len - (s.gpr .r5).toNat) := by
    rw [u₄.gpr, u₃.gpr, u₃.other .r5 (by decide), g8, g5]
    conv => lhs; rw [← ofNat_toNat64 (s.gpr .r5)]
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg, Offset.ofNat_sub_ofNat (by omega)]
  have em : s₄.mem = s₂.mem := by rw [u₄.mem, u₃.mem]
  have ewr : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, h₂.wr, u₀.wr, hk.2.2]
  have erd : s₄.rd = s.rd := by rw [u₄.rd, u₃.rd, h₂.rd, u₀.rd, hk.2.1]
  have hz : ∀ j < 72, s₄.mem (s.gpr .r8 + BitVec.ofNat 64 j) = 0 := by
    intro j hj
    have := h₂.stored j hj
    rw [u₀.other .r8 (by decide), ha8] at this
    rw [em, this]
  have hzf : Frame [⟨s.gpr .r8, 80⟩] s.mem s₄.mem := by
    intro x hx
    rw [em, h₂.frame x fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [u₀.other .r8 (by decide), ha8]
      intro hc; exact hx _ (List.mem_singleton_self _) (contains_sub hc (by omega)), u₀.mem, hm]
  have hdig : ∀ i < (s.gpr .r5).toNat, s₄.mem (s.gpr .r4 + BitVec.ofNat 64 i) =
      s.mem (s.gpr .r4 + BitVec.ofNat 64 i) := by
    intro i hi
    exact hzf _ fun r hr hc => by
      simp only [List.mem_singleton] at hr; subst hr
      exact buf_not_hash hp hc hi rfl
  refine WP.seq (WP.ite (s₄.gpr .r5 == 0) (eval_zero _ _) (fun h0 => ?_) (fun h0 => ?_))
  · refine wp_nil (tail_ok wide hp hl ⟨fun j hj => ?_, hzf, e8, ewr⟩)
    have hd0 : (s.gpr .r5).toNat = 0 := by
      rw [← e5]; simp only [beq_iff_eq] at h0; rw [h0]; rfl
    rw [hz j hj, tz, ite_eq_right (by rw [length_bytesAt, hd0]; omega)]
  · have hd0 : (s.gpr .r5).toNat ≠ 0 := by
      intro e; rw [← e5] at e; simp only [beq_eq_false_iff_ne, ne_eq] at h0
      exact h0 (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    refine WP.mono (copyLoop_ok s₄ (N := (s.gpr .r5).toNat) (by omega)
      (s.gpr .r5).isLt (by rw [e5, ofNat_toNat64]) (fun i hi => ?_) (fun i hi => ?_) ?_)
      fun t ⟨hc, hf, hkp⟩ => tail_ok wide hp hl ⟨fun j hj => ?_, ?_, ?_, ?_⟩
    · rw [erd, ewr, e4]; exact hp.rd i hi
    · rw [ewr, et10, Offset.add_add]; exact hp.wr _ (by omega)
    · intro x h1 h2
      rw [et10] at h1
      rw [e4] at h2
      exact hp.sep x (in_buf (off := len - (s.gpr .r5).toNat) (n := (s.gpr .r5).toNat)
        (by unfold Region.Contains; simp only; omega) (by omega)) (by unfold Region.Contains; simp only; omega)
    · by_cases hin : len - (s.gpr .r5).toNat ≤ j ∧ j < len
      · have e := hc (j - (len - (s.gpr .r5).toNat)) (by omega)
        rw [et10, e4, Offset.add_add, show len - (s.gpr .r5).toNat + (j - (len - (s.gpr .r5).toNat)) = j by
          omega, hdig _ (by omega)] at e
        rw [e, tz, ite_eq_left (by rw [length_bytesAt]; exact hin), length_bytesAt, hash_byte (by omega)]
      · rw [hf _ fun r hr hcon => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [et10] at hcon
          unfold Region.Contains at hcon
          simp only at hcon
          have := (Offset.lt_iff (s.gpr .r8 + BitVec.ofNat 64 j) (s.gpr .r8) (d := len - (s.gpr .r5).toNat)
            (n := (s.gpr .r5).toNat) (by omega)).mp (by omega)
          rw [Mem.sub_ofNat_toNat _ (by omega)] at this
          omega, hz j hj, tz, ite_eq_right (by rw [length_bytesAt]; exact hin)]
    · refine hzf.trans (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
      simp only [List.mem_singleton] at hr; subst hr
      rw [et10]; exact Offset.sub_base _ (by omega)
    · rw [hkp.gpr (by decide), e8]
    · rw [hkp.2.2, ewr]

theorem convert_writes (wide : Bool) : writesOnly convRegs (convert len wide) = true := by
  cases wide <;>
  simp [writesOnly, Code.allInstrs_eq, instrs, convert, short, shiftBytes, copyBytes, zeroBytes, isShort,
    copyLoop, List.all_flatMap, dstOf]

theorem convert_mem (wide : Bool) (hp : CPre len s) : WP isa (convert len wide) s (MPost len wide s) := by
  unfold convert
  refine WP.seq (WP.mono (isShort_ok hp) fun s₁ ⟨hb, hk, hm⟩ => ?_)
  refine WP.ite (s₁.gpr .r12 != 0) (eval_nonzero _ _) (fun h => short_ok wide hp hk hm ?_)
    (fun h => long_ok wide hp hk hm ?_)
  · rw [hb] at h; exact of_decide_eq_true h
  · rw [hb] at h; exact Nat.le_of_not_lt (of_decide_eq_false h)

/-- `convert`: the buffer's first `len` bytes are `fixedDigest` of the hash,
and only the buffer and `r4`, `r5`, `r9`–`r12` change. -/
theorem convert_ok (wide : Bool) (hp : CPre len s) : WP isa (convert len wide) s (CPost len wide s) :=
  WP.mono (WP.rdwr (WP.keep convRegs (convert_mem wide hp) (convert_writes wide)
    (by cases wide <;> rfl))) fun _ ⟨⟨hm, hk⟩, _, _, hsp⟩ => ⟨hm.buf, hm.frame, hk, hsp⟩

/-- Code without calls that never writes `LR` keeps it. -/
theorem WP.lr {c : Prog isa} {Q : State → Prop} (h : WP isa c s Q) (hn : c.noCalls = true)
    (hl : (instrs c).all (fun i => !i.writesLr) = true) : WP isa c s fun s' => Q s' ∧ s'.lr = s.lr := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.lr he hn hl⟩

/-- `convert_ok`, and `LR` kept. -/
theorem convert_okL (wide : Bool) (hp : CPre len s) :
    WP isa (convert len wide) s fun t => CPost len wide s t ∧ t.lr = s.lr :=
  WP.lr (convert_ok wide hp) (by cases wide <;> rfl) (by
    cases wide <;> simp [instrs, convert, short, shiftBytes, copyBytes, zeroBytes, isShort, copyLoop,
      List.all_flatMap, Instr.writesLr])

/-! ## The contracts, by register -/

variable (I : Spec.Ecdsa.Instance)

/-- The regions of `hashed`'s arguments: `verifyHashContract`'s, and the
buffer in `r8`. -/
structure IPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r3, 2 * I.curve.len + 1⟩, ⟨s.gpr .r4, (s.gpr .r5).toNat⟩, ⟨s.gpr .r6, 2 * I.curve.len⟩]
  wr : s.wr = [⟨s.gpr .r7, 8192⟩, ⟨s.gpr .r8, 80⟩]
  d37 : (⟨s.gpr .r3, 2 * I.curve.len + 1⟩ : Region).Disjoint ⟨s.gpr .r7, 8192⟩
  d38 : (⟨s.gpr .r3, 2 * I.curve.len + 1⟩ : Region).Disjoint ⟨s.gpr .r8, 80⟩
  d47 : (⟨s.gpr .r4, (s.gpr .r5).toNat⟩ : Region).Disjoint ⟨s.gpr .r7, 8192⟩
  d48 : (⟨s.gpr .r4, (s.gpr .r5).toNat⟩ : Region).Disjoint ⟨s.gpr .r8, 80⟩
  d67 : (⟨s.gpr .r6, 2 * I.curve.len⟩ : Region).Disjoint ⟨s.gpr .r7, 8192⟩
  d68 : (⟨s.gpr .r6, 2 * I.curve.len⟩ : Region).Disjoint ⟨s.gpr .r8, 80⟩
  d78 : (⟨s.gpr .r7, 8192⟩ : Region).Disjoint ⟨s.gpr .r8, 80⟩
  f3 : (s.gpr .r3).toNat + (2 * I.curve.len + 1) ≤ 2 ^ 64
  f4 : (s.gpr .r4).toNat + (s.gpr .r5).toNat ≤ 2 ^ 64
  f6 : (s.gpr .r6).toNat + 2 * I.curve.len ≤ 2 ^ 64
  f7 : (s.gpr .r7).toNat + 8192 ≤ 2 ^ 64
  f8 : (s.gpr .r8).toNat + 80 ≤ 2 ^ 64

/-- What the verification that takes the `len` bytes needs, by register:
`public` in `r3`, the bytes in `r4`, `sig` in `r5`, `scratch` in `r6`. -/
structure KPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r3, 2 * I.curve.len + 1⟩, ⟨s.gpr .r4, I.curve.len⟩, ⟨s.gpr .r5, 2 * I.curve.len⟩]
  wr : s.wr = [⟨s.gpr .r6, 8192⟩]
  d36 : (⟨s.gpr .r3, 2 * I.curve.len + 1⟩ : Region).Disjoint ⟨s.gpr .r6, 8192⟩
  d46 : (⟨s.gpr .r4, I.curve.len⟩ : Region).Disjoint ⟨s.gpr .r6, 8192⟩
  d56 : (⟨s.gpr .r5, 2 * I.curve.len⟩ : Region).Disjoint ⟨s.gpr .r6, 8192⟩
  f3 : (s.gpr .r3).toNat + (2 * I.curve.len + 1) ≤ 2 ^ 64
  f4 : (s.gpr .r4).toNat + I.curve.len ≤ 2 ^ 64
  f5 : (s.gpr .r5).toNat + 2 * I.curve.len ≤ 2 ^ 64
  f6 : (s.gpr .r6).toNat + 8192 ≤ 2 ^ 64

/-- The key's bytes, at `r3`. -/
abbrev pkB (s : State) : List Byte := Spec.Ecdsa.bytesAt s.mem (s.gpr .r3) (2 * I.curve.len + 1)

/-- The verification, of the bytes at `pk`, `e` and `sg`, as the function returns it. -/
abbrev vres (m : Mem) (pk : Addr) (e : Nat) (sg : Addr) : BitVec 32 :=
  if Spec.Ecdsa.verify I.curve (Spec.Ecdsa.bytesAt m pk (2 * I.curve.len + 1)) e
    (Spec.Ecdsa.bytesAt m sg (2 * I.curve.len)) then 1 else 0

/-- `hashed`'s contract, by register. -/
def hashR : Contract isa where
  pre s := IPre I s
  post s s' := (s'.gpr .r3).setWidth 32 =
    vres I s.mem (s.gpr .r3) (Spec.Ecdsa.hashToInt I.curve (hashOf s)) (s.gpr .r6)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧
    s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧
    s₁.gpr .r8 = s₂.gpr .r8 ∧
    (pkB I s₁ ++ hashOf s₁ ++ Spec.Ecdsa.bytesAt s₁.mem (s₁.gpr .r6) (2 * I.curve.len)).map (·.toNat) =
      (pkB I s₂ ++ hashOf s₂ ++ Spec.Ecdsa.bytesAt s₂.mem (s₂.gpr .r6) (2 * I.curve.len)).map (·.toNat)

/-- The contract of the verification that takes the `len` bytes, by register. -/
def coreR : Contract isa where
  pre s := KPre I s
  post s s' := (s'.gpr .r3).setWidth 32 =
    vres I s.mem (s.gpr .r3)
      (Spec.Ecdsa.hashToInt I.curve (Spec.Ecdsa.bytesAt s.mem (s.gpr .r4) I.curve.len)) (s.gpr .r5)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧
    s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.gpr .r6 = s₂.gpr .r6 ∧
    (pkB I s₁ ++ Spec.Ecdsa.bytesAt s₁.mem (s₁.gpr .r4) I.curve.len ++
        Spec.Ecdsa.bytesAt s₁.mem (s₁.gpr .r5) (2 * I.curve.len)).map (·.toNat) =
      (pkB I s₂ ++ Spec.Ecdsa.bytesAt s₂.mem (s₂.gpr .r4) I.curve.len ++
        Spec.Ecdsa.bytesAt s₂.mem (s₂.gpr .r5) (2 * I.curve.len)).map (·.toNat)

/-! ## Running the verification on the bytes -/

/-- Verified code run from `s` with narrower permissions: its run from `s`. -/
theorem WP.narrowRun {c : Prog isa} {P : State → Prop} {Q : State → State → Prop}
    (hv : ∀ s, P s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ Q s s') {s : State}
    {rd wr : List Region} (hpre : P (s.withRegions rd wr)) (hc : PPC64LE.Covers (rd ++ wr) (s.rd ++ s.wr))
    (hw : PPC64LE.Covers wr s.wr) :
    WP isa c s fun s' => abiPreserved s s' ∧ Q (s.withRegions rd wr) (s'.withRegions rd wr) := by
  obtain ⟨t, s₁, he, ha, hq⟩ := hv _ hpre
  obtain ⟨hr, hwr, -⟩ := Exec.rdwr he
  simp only [State.withRegions_rd, State.withRegions_wr] at hr hwr
  have he' := Exec.widen he (rd := s.rd) (wr := s.wr) (by simpa using hc) (by simpa using hw)
  simp only [State.withRegions_withRegions, State.withRegions_self] at he'
  have e : (s₁.withRegions s.rd s.wr).withRegions rd wr = s₁ := by
    rw [State.withRegions_withRegions, ← hr, ← hwr]; rfl
  exact ⟨t, _, he', ⟨fun r hr' => ha.1 r hr', ha.2.1, ha.2.2⟩, by rw [e]; exact hq⟩

theorem covers_self {r : Region} {rs : List Region} (h : r ∈ rs) :
    ∃ r' ∈ rs, ∃ off, r.base = r'.base + BitVec.ofNat 64 off ∧ off + r.len ≤ r'.len :=
  ⟨r, h, 0, by simp, by omega⟩

/-- The state after `convert` (`u`) and the moves of the arguments (`v`). -/
structure VFacts (s u v : State) : Prop where
  a3 : v.gpr .r3 = s.gpr .r3
  a4 : v.gpr .r4 = s.gpr .r8
  a5 : v.gpr .r5 = s.gpr .r6
  a6 : v.gpr .r6 = s.gpr .r7
  mem : v.mem = u.mem
  rd : v.rd = s.rd
  wr : v.wr = s.wr
  sp : v.sp = s.sp
  pres : ∀ r ∈ preserved, v.gpr r = s.gpr r
  lr : v.lr = s.lr

/-- The verification's readable regions: the key, the `len` bytes and the
signature. -/
abbrev rdV (s : State) : List Region :=
  [⟨s.gpr .r3, 2 * I.curve.len + 1⟩, ⟨s.gpr .r8, I.curve.len⟩, ⟨s.gpr .r6, 2 * I.curve.len⟩]

/-- Its writable region: `scratch`. -/
abbrev wrV (s : State) : List Region := [⟨s.gpr .r7, 8192⟩]

section
variable {I} {wide : Bool}

theorem cpre_of (hL : 8 * I.curve.len = Spec.Ecdsa.nBits I.curve + if wide then 7 else 0)
    (h66 : I.curve.len ≤ 66) {s : State} (hs : (hashR I).pre s) : CPre I.curve.len s := by
  have hp : IPre I s := hs
  have hn := nBits_pos I.curve
  have f8 := hp.f8
  have f4 := hp.f4
  refine ⟨by split at hL <;> omega, h66,
    fun i hi => ⟨⟨s.gpr .r4, (s.gpr .r5).toNat⟩, ?_, Offset.contains_base _ (by omega) (by omega)⟩,
    fun i hi => ⟨⟨s.gpr .r8, 80⟩, ?_, Offset.contains_base _ (by omega) (by omega)⟩, hp.d48.symm, f8, f4⟩
  · rw [hp.rd]; simp
  · rw [hp.wr]; simp

theorem args_ok {s u : State} (hu : CPost I.curve.len wide s u) (hlr : u.lr = s.lr) :
    WP isa (.block args) u (VFacts s u) := by
  refine WP.mono (WP.rdwr (WP.lr (wp_mr fun v₁ g₁ => wp_mr fun v₂ g₂ => wp_mr fun v g₃ => wp_nil
    (Q := fun v => v.gpr .r3 = s.gpr .r3 ∧ v.gpr .r4 = s.gpr .r8 ∧ v.gpr .r5 = s.gpr .r6 ∧
      v.gpr .r6 = s.gpr .r7 ∧ v.mem = u.mem ∧ ∀ r ∈ preserved, v.gpr r = s.gpr r) ?_) rfl rfl))
    fun v ⟨⟨⟨h3, h4, h5, h6, hm, hpr⟩, hl⟩, hr, hw, hsp⟩ =>
      ⟨h3, h4, h5, h6, hm, hr.trans hu.keep.2.1, hw.trans hu.keep.2.2, hsp.trans hu.sp, hpr, hl.trans hlr⟩
  have k := hu.keep
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
  · rw [g₃.other _ (by decide), g₂.other _ (by decide), g₁.other _ (by decide), k.gpr (by decide)]
  · rw [g₃.other _ (by decide), g₂.other _ (by decide), g₁.gpr, k.gpr (by decide)]
  · rw [g₃.other _ (by decide), g₂.gpr, g₁.other _ (by decide), k.gpr (by decide)]
  · rw [g₃.gpr, g₂.other _ (by decide), g₁.other _ (by decide), k.gpr (by decide)]
  · rw [g₃.mem, g₂.mem, g₁.mem]
  · have h1 : r ∉ convRegs := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl <;> decide
    have h2 : r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl <;> decide
    rw [g₃.other _ h2.2.2, g₂.other _ h2.2.1, g₁.other _ h2.1, k.gpr h1]

theorem vpre (h66 : I.curve.len ≤ 66) {s u v : State} (hs : (hashR I).pre s)
    (hv : VFacts s u v) :
    (coreR I).pre (v.withRegions (rdV I s) (wrV s)) ∧
      PPC64LE.Covers (rdV I s ++ wrV s) (v.rd ++ v.wr) ∧ PPC64LE.Covers (wrV s) v.wr := by
  have hp : IPre I s := hs
  have hL80 : I.curve.len ≤ 80 := by omega
  have f8 := hp.f8
  have hsc : (⟨s.gpr .r7, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hbf : (⟨s.gpr .r8, 80⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only [State.withRegions_rd, State.withRegions_gpr, hv.a3, hv.a4, hv.a5]
  · simp only [State.withRegions_wr, State.withRegions_gpr, hv.a6]
  · simp only [State.withRegions_gpr, hv.a3, hv.a6]; exact hp.d37
  · simp only [State.withRegions_gpr, hv.a4, hv.a6]
    exact (hp.d78.sub_right (sub_prefix _ hL80)).symm
  · simp only [State.withRegions_gpr, hv.a5, hv.a6]; exact hp.d67
  · simp only [State.withRegions_gpr, hv.a3]; exact hp.f3
  · simp only [State.withRegions_gpr, hv.a4]; omega
  · simp only [State.withRegions_gpr, hv.a5]; exact hp.f6
  · simp only [State.withRegions_gpr, hv.a6]; exact hp.f7
  · refine PPC64LE.Covers.of_sub fun r hr => ?_
    rw [hv.rd, hv.wr]
    simp only [rdV, wrV, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact covers_self (by rw [hp.rd]; simp)
    · exact ⟨_, List.mem_append_right _ hbf, 0, by simp, by simp; omega⟩
    · exact covers_self (by rw [hp.rd]; simp)
    · exact covers_self (List.mem_append_right _ hsc)
  · refine PPC64LE.Covers.of_sub fun r hr => ?_
    simp only [wrV, List.mem_singleton] at hr; subst hr
    rw [hv.wr]; exact covers_self hsc

theorem vpost {s u v : State}
    (hs : (hashR I).pre s) (hu : CPost I.curve.len wide s u) (hv : VFacts s u v) :
    Spec.Ecdsa.bytesAt v.mem (s.gpr .r8) I.curve.len = fixedDigest I.curve.len wide (hashOf s) ∧
      Spec.Ecdsa.bytesAt v.mem (s.gpr .r3) (2 * I.curve.len + 1) =
        Spec.Ecdsa.bytesAt s.mem (s.gpr .r3) (2 * I.curve.len + 1) ∧
      Spec.Ecdsa.bytesAt v.mem (s.gpr .r6) (2 * I.curve.len) =
        Spec.Ecdsa.bytesAt s.mem (s.gpr .r6) (2 * I.curve.len) := by
  have hp : IPre I s := hs
  have f3 := hp.f3
  have f6 := hp.f6
  refine ⟨bytesAt_ext (length_fixedDigest _ _ _) fun i hi => by rw [hv.mem]; exact hu.buf i hi, ?_, ?_⟩
  · rw [hv.mem]; exact bytesAt_frame hu.frame hp.d38 (by omega)
  · rw [hv.mem]; exact bytesAt_frame hu.frame hp.d68 (by omega)

end

theorem hashed_correct {wide : Bool} {core : Prog isa}
    (hL : 8 * I.curve.len = Spec.Ecdsa.nBits I.curve + if wide then 7 else 0) (h66 : I.curve.len ≤ 66)
    (hcv : ∀ s, (coreR I).pre s →
      ∃ t s', Exec isa core s t s' ∧ abiPreserved s s' ∧ (coreR I).post s s')
    (s : State) (hs : (hashR I).pre s) :
    ∃ t s', Exec isa (hashed I.curve.len wide core) s t s' ∧ abiPreserved s s' ∧ (hashR I).post s s' := by
  unfold hashed
  refine WP.seq (WP.mono (convert_okL wide (cpre_of hL h66 hs)) fun u ⟨hu, hlr⟩ => ?_)
  refine WP.seq (WP.mono (args_ok hu hlr) fun v hv => ?_)
  obtain ⟨hpre, hc, hw⟩ := vpre h66 hs hv
  refine WP.mono (WP.narrowRun hcv hpre hc hw) fun s' ⟨habi, hpost⟩ =>
    ⟨⟨fun r hr => (habi.1 r hr).trans (hv.pres r hr), habi.2.1.trans hv.sp, habi.2.2.trans hv.lr⟩, ?_⟩
  obtain ⟨e1, e2, e3⟩ := vpost hs hu hv
  have hq : (s'.gpr .r3).setWidth 32 = vres I v.mem (s.gpr .r3)
      (Spec.Ecdsa.hashToInt I.curve (Spec.Ecdsa.bytesAt v.mem (s.gpr .r8) I.curve.len)) (s.gpr .r6) := by
    have := hpost
    simp only [coreR, State.withRegions_gpr, State.withRegions_mem, hv.a3, hv.a4, hv.a5] at this
    exact this
  show (s'.gpr .r3).setWidth 32 = vres I s.mem (s.gpr .r3) (Spec.Ecdsa.hashToInt I.curve (hashOf s)) (s.gpr .r6)
  rw [hq, e1, hashToInt_fixedDigest hL]
  simp only [vres, e2, e3]

/-! ## Constant time -/

/-- Inlined verified code: two runs, from states that narrow to ones its
contract relates, leak the same. -/
theorem RelCT.inlineV {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      k.pre (s₁.withRegions rd₁ wr₁) ∧ k.pre (s₂.withRegions rd₂ wr₂) ∧
      k.pub (s₁.withRegions rd₁ wr₁) (s₂.withRegions rd₂ wr₂) ∧
      PPC64LE.Covers (rd₁ ++ wr₁) (s₁.rd ++ s₁.wr) ∧ PPC64LE.Covers wr₁ s₁.wr ∧
      PPC64LE.Covers (rd₂ ++ wr₂) (s₂.rd ++ s₂.wr) ∧ PPC64LE.Covers wr₂ s₂.wr) :
    RelCT isa P c fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨rd₁, wr₁, rd₂, wr₂, p₁, p₂, hpub, c₁, w₁, c₂, w₂⟩ := hP _ _ hp
  obtain ⟨_, n₁⟩ := trace_narrow hv p₁ c₁ w₁ e₁
  obtain ⟨_, n₂⟩ := trace_narrow hv p₂ c₂ w₂ e₂
  exact ⟨hct _ _ _ _ _ _ p₁ p₂ hpub n₁ n₂, trivial⟩

/-- The arguments' moves leak nothing. -/
theorem args_taint : (taint.check (Taint.ofRegs [.r3, .r6, .r7, .r8]) (.block args)
    (.block [] 256)).isSome = true := by
  decide

section
variable {I} {wide : Bool}

/-- Two runs as `hashR` relates them. -/
abbrev HP (s₁ s₂ : State) : Prop := (hashR I).pre s₁ ∧ (hashR I).pre s₂ ∧ (hashR I).pub s₁ s₂

/-- `convert_okL`'s facts. -/
abbrev CF (len : Nat) (wide : Bool) (s t : State) : Prop := CPost len wide s t ∧ t.lr = s.lr

theorem hashed_ct {core : Prog isa}
    (hL : 8 * I.curve.len = Spec.Ecdsa.nBits I.curve + if wide then 7 else 0) (h66 : I.curve.len ≤ 66)
    (hcv : ∀ s, (coreR I).pre s →
      ∃ t s', Exec isa core s t s' ∧ abiPreserved s s' ∧ (coreR I).post s s')
    (hct : ConstantTime isa (coreR I).pre (coreR I).pub core) {hc : Taint.Hint taint.T}
    (htc : (taint.check (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8]) (convert I.curve.len wide) hc).isSome = true) :
    ConstantTime isa (hashR I).pre (hashR I).pub (hashed I.curve.len wide core) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold hashed
  refine RelCT.seq (R := fun u₁ u₂ => ∃ σ₁ σ₂ x₁ x₂ : State, u₁ = x₁ ∧ u₂ = x₂ ∧ HP (I := I) σ₁ σ₂ ∧
      CF I.curve.len wide σ₁ x₁ ∧ CF I.curve.len wide σ₂ x₂)
    ?_ (RelCT.seq (R := fun v₁ v₂ => ∃ σ₁ σ₂ x₁ x₂ : State, HP (I := I) σ₁ σ₂ ∧
      CPost I.curve.len wide σ₁ x₁ ∧ VFacts σ₁ x₁ v₁ ∧ CPost I.curve.len wide σ₂ x₂ ∧ VFacts σ₂ x₂ v₂) ?_ ?_)
  · refine ((RelCT.taint (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8]) (fun s₁ s₂ h => ?_) htc).wpDep
      (F := CF I.curve.len wide) fun s₁ s₂ h =>
        ⟨convert_okL wide (cpre_of hL h66 h.1), convert_okL wide (cpre_of hL h66 h.2.1)⟩).mono (fun _ _ h => h)
      fun t₁ t₂ ⟨_, σ₁, σ₂, hp, a₁, a₂⟩ => ⟨σ₁, σ₂, t₁, t₂, rfl, rfl, hp, a₁, a₂⟩
    obtain ⟨-, -, psp, p3, p4, p5, p6, p7, p8, -⟩ := h
    refine ⟨psp, fun r hr => ?_⟩
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  · refine RelCT.exists_ fun σ₁ => RelCT.exists_ fun σ₂ => RelCT.exists_ fun x₁ => RelCT.exists_ fun x₂ => ?_
    refine ((RelCT.taint (A := taint) (Taint.ofRegs [.r3, .r6, .r7, .r8]) (fun s₁ s₂ h => ?_) args_taint).wp
      (F₁ := fun v => (HP (I := I) σ₁ σ₂ ∧ CPost I.curve.len wide σ₁ x₁ ∧
        CPost I.curve.len wide σ₂ x₂) ∧ VFacts σ₁ x₁ v) (F₂ := VFacts σ₂ x₂)
      fun u₁ u₂ ⟨e₁, e₂, hp, ⟨c₁, y₁⟩, ⟨c₂, y₂⟩⟩ => by
        subst e₁ e₂; exact ⟨WP.mono (args_ok c₁ y₁) fun _ h => ⟨⟨hp, c₁, c₂⟩, h⟩, args_ok c₂ y₂⟩).mono
      (fun _ _ h => h) fun v₁ v₂ ⟨_, ⟨⟨hp, c₁, c₂⟩, f₁⟩, f₂⟩ => ⟨σ₁, σ₂, x₁, x₂, hp, c₁, f₁, c₂, f₂⟩
    obtain ⟨e₁, e₂, ⟨-, -, psp, p3, -, -, p6, p7, p8, -⟩, ⟨c₁, -⟩, ⟨c₂, -⟩⟩ := h
    subst e₁ e₂
    have k₁ := c₁.keep
    have k₂ := c₂.keep
    refine ⟨by rw [c₁.sp, c₂.sp, psp], fun r hr => ?_⟩
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [k₁.gpr (by decide), k₂.gpr (by decide), p3]
    · rw [k₁.gpr (by decide), k₂.gpr (by decide), p6]
    · rw [k₁.gpr (by decide), k₂.gpr (by decide), p7]
    · rw [k₁.gpr (by decide), k₂.gpr (by decide), p8]
  · refine RelCT.inlineV hcv hct fun v₁ v₂ ⟨σ₁, σ₂, x₁, x₂, hp, c₁, f₁, c₂, f₂⟩ => ?_
    obtain ⟨q₁, cv₁, cw₁⟩ := vpre h66 hp.1 f₁
    obtain ⟨q₂, cv₂, cw₂⟩ := vpre h66 hp.2.1 f₂
    refine ⟨_, _, _, _, q₁, q₂, ?_, cv₁, cw₁, cv₂, cw₂⟩
    obtain ⟨psp, p3, p4, p5, p6, p7, p8, pl⟩ := hp.2.2
    obtain ⟨b₁, k₁, g₁⟩ := vpost hp.1 c₁ f₁
    obtain ⟨b₂, k₂, g₂⟩ := vpost hp.2.1 c₂ f₂
    obtain ⟨ek, eh, eg⟩ := bytes_of_leak (by simp only [pkB, length_bytesAt])
      (by simp only [hashOf, length_bytesAt, p5]) pl
    refine ⟨by simp only [State.withRegions_sp, f₁.sp, f₂.sp, psp], by simp only [State.withRegions_gpr, f₁.a3, f₂.a3, p3],
      by simp only [State.withRegions_gpr, f₁.a4, f₂.a4, p8], by simp only [State.withRegions_gpr, f₁.a5, f₂.a5, p6],
      by simp only [State.withRegions_gpr, f₁.a6, f₂.a6, p7], ?_⟩
    simp only [pkB, State.withRegions_mem, State.withRegions_gpr, f₁.a3, f₁.a4, f₁.a5, f₂.a3, f₂.a4, f₂.a5]
    rw [b₁, k₁, g₁, b₂, k₂, g₂]
    simp only [pkB] at ek
    rw [ek, eh, eg]
end

/-! ## The contracts of `Spec/`, by register -/

section
variable {I}

/-- The verification's precondition under `abi`, from `KPre`. -/
theorem core_pre {s : State} (h : KPre I s) : (I.verifyContract abi 0).pre s := by
  sig_pre [Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig, Spec.Ecdsa.scratchWords,
    PPC64LE.abi, PPC64LE.argRegs]
  exact ⟨h.rd, h.wr, h.d36, h.d46, h.d56, h.f3, h.f4, h.f5, h.f6⟩

theorem core_post {s s' : State} (h : (I.verifyContract abi 0).post s s') :
    (s'.gpr .r3).setWidth 32 = vres I s.mem (s.gpr .r3)
      (Spec.Ecdsa.hashToInt I.curve (Spec.Ecdsa.bytesAt s.mem (s.gpr .r4) I.curve.len)) (s.gpr .r5) := by
  sig_post [Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig, Spec.Ecdsa.scratchWords,
    PPC64LE.abi, PPC64LE.argRegs] at h
  exact h

theorem core_pub {s₁ s₂ : State} (h : (coreR I).pub s₁ s₂) : (I.verifyContract abi 0).pub s₁ s₂ := by
  sig_pub [Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig, Spec.Ecdsa.scratchWords,
    PPC64LE.abi, PPC64LE.argRegs]
  obtain ⟨psp, p3, p4, p5, p6, pl⟩ := h
  exact ⟨psp, pl, p3, p4, p5, p6⟩

/-- The verification, run as `coreR` describes it, from its proof under `abi`. -/
theorem coreR_of {core : Prog isa} (h : Verified target core (I.verifyContract abi 0)) :
    (∀ s, (coreR I).pre s → ∃ t s', Exec isa core s t s' ∧ abiPreserved s s' ∧ (coreR I).post s s') ∧
      ConstantTime isa (coreR I).pre (coreR I).pub core := by
  obtain ⟨hc, hct, -⟩ := h
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_⟩
  · obtain ⟨t, s', he, ha, hq⟩ := hc s (core_pre hs)
    exact ⟨t, s', he, ha, core_post hq⟩
  · exact hct _ _ _ _ _ _ (core_pre h₁) (core_pre h₂) (core_pub hpub) e₁ e₂

/-- `verifyHashContract`'s postcondition. -/
abbrev hPost : I.verifyHashSig.Post abi.ptrBits := fun pk digest digestLen sig _scratch m _m' r =>
  r = if Spec.Ecdsa.verify I.curve (Spec.Ecdsa.bytesAt m pk (2 * I.curve.len + 1))
      (Spec.Ecdsa.hashToInt I.curve (Spec.Ecdsa.bytesAt m digest digestLen.toNat))
      (Spec.Ecdsa.bytesAt m sig (2 * I.curve.len))
    then 1 else 0

/-- `verifyHashContract`'s leak. -/
abbrev hLeak : Curry (I.verifyHashSig.words abi.ptrBits) (Mem → List Nat) :=
  fun pk digest digestLen sig _scratch m =>
    (Spec.Ecdsa.bytesAt m pk (2 * I.curve.len + 1) ++ Spec.Ecdsa.bytesAt m digest digestLen.toNat ++
      Spec.Ecdsa.bytesAt m sig (2 * I.curve.len)).map (·.toNat)

/-- `hashed`'s contract under `abi`, with the buffer as a last argument. -/
abbrev innerA : Contract isa :=
  Sig.scratchContract abi I.verifyHashSig "buf" .u8 80 (Curry.const (fun _ => True) _) (hPost (I := I)) true 0
    (some (hLeak (I := I)))

theorem inner_ipre {s : State} (h : (innerA (I := I)).pre s) : IPre I s := by
  sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, hPost,
    Spec.Ecdsa.Instance.verifyHashSig, Spec.Ecdsa.scratchWords, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨hrd, hwr, d37, d38, d47, d48, d67, d68, d78, f3, f4, f6, f7, f8⟩ := h
  exact ⟨hrd, hwr, d37, d38, d47, d48, d67, d68, d78, f3, f4, f6, f7, f8⟩

theorem inner_post {s s' : State} (h : (hashR I).post s s') : (innerA (I := I)).post s s' := by
  sig_post [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, hPost,
    Spec.Ecdsa.Instance.verifyHashSig, Spec.Ecdsa.scratchWords, PPC64LE.abi, PPC64LE.argRegs]
  exact h

theorem inner_pub {s₁ s₂ : State} (h : (innerA (I := I)).pub s₁ s₂) : (hashR I).pub s₁ s₂ := by
  sig_pub [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, hPost, hLeak, Option.map,
    Spec.Ecdsa.Instance.verifyHashSig, Spec.Ecdsa.scratchWords, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨psp, pl, p3, p4, p5, p6, p7, p8⟩ := h
  exact ⟨psp, p3, p4, p5, p6, p7, p8, pl⟩

/-- `hashed` under `abi`. -/
theorem hashed_verified {wide : Bool} {core : Prog isa}
    (hL : 8 * I.curve.len = Spec.Ecdsa.nBits I.curve + if wide then 7 else 0) (h66 : I.curve.len ≤ 66)
    (hcore : Verified target core (I.verifyContract abi 0)) {hc : Taint.Hint taint.T}
    (htc : (taint.check (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8]) (convert I.curve.len wide) hc).isSome = true)
    (hsat : ∃ s, (innerA (I := I)).pre s) :
    Verified target (hashed I.curve.len wide core) (innerA (I := I)) := by
  obtain ⟨hcv, hct⟩ := coreR_of hcore
  exact Verified.of_correct (T := target) (k := hashR I) (k' := innerA (I := I))
    (hashed_correct I hL h66 hcv) (hashed_ct hL h66 hcv hct htc)
    ⟨fun s hs => inner_ipre hs, fun s s' _ h => inner_post h, fun s₁ s₂ _ _ h => inner_pub h, hsat⟩

end

/-! ## In a frame on the stack -/

section
variable {I}

theorem hashSig_words :
    I.verifyHashSig.words abi.ptrBits = [.addr, .addr, .int 64, .addr, .addr] := rfl

theorem bytesAt_congr {m₁ m₂ : Mem} {p : Addr} {n : Nat}
    (h : ∀ a, (⟨p, n⟩ : Region).Contains a 1 → m₁ a = m₂ a) :
    Spec.Ecdsa.bytesAt m₁ p n = Spec.Ecdsa.bytesAt m₂ p n := by
  simp only [Spec.Ecdsa.bytesAt]
  refine List.map_congr_left fun i hi => h _ ?_
  have hi : i < n := by simpa using hi
  show (p + BitVec.ofNat 64 i - p).toNat + 1 ≤ n
  rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  have := Nat.mod_le i (2 ^ 64)
  omega

/-- The three buffers the result and the leak read have the same bytes in
memories that agree on the arguments' buffers. -/
theorem bufs_same {pk d l sg sc : BitVec 64} {m₁ m₂ : Mem}
    (hb : ∀ b ∈ Sig.bufs I.verifyHashSig.params [pk, d, l, sg, sc], ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) :
    Spec.Ecdsa.bytesAt m₁ pk (2 * I.curve.len + 1) = Spec.Ecdsa.bytesAt m₂ pk (2 * I.curve.len + 1) ∧
      Spec.Ecdsa.bytesAt m₁ d l.toNat = Spec.Ecdsa.bytesAt m₂ d l.toNat ∧
      Spec.Ecdsa.bytesAt m₁ sg (2 * I.curve.len) = Spec.Ecdsa.bytesAt m₂ sg (2 * I.curve.len) := by
  simp only [Spec.Ecdsa.Instance.verifyHashSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  exact ⟨bytesAt_congr hb.1, bytesAt_congr hb.2.1, bytesAt_congr hb.2.2.1⟩

theorem pre_local : ∀ vs m₁ m₂, vs.length = (I.verifyHashSig.words abi.ptrBits).length →
    (∀ b ∈ Sig.bufs I.verifyHashSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (I.verifyHashSig.words abi.ptrBits) (Curry.const (fun (_ : Mem) => True) _) vs m₁ →
      Curry.apply (I.verifyHashSig.words abi.ptrBits) (Curry.const (fun (_ : Mem) => True) _) vs m₂ := by
  intro vs m₁ m₂ hlen _ _
  rw [hashSig_words] at hlen
  match vs, hlen with
  | [_, _, _, _, _], _ => trivial

theorem post_local : ∀ vs m₁ m₂ m' r, vs.length = (I.verifyHashSig.words abi.ptrBits).length →
    Curry.apply (I.verifyHashSig.words abi.ptrBits) (Curry.const (fun (_ : Mem) => True) _) vs m₂ →
    (∀ b ∈ Sig.bufs I.verifyHashSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (I.verifyHashSig.words abi.ptrBits) (hPost (I := I)) vs m₁ m' r →
      Curry.apply (I.verifyHashSig.words abi.ptrBits) (hPost (I := I)) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen _ hb h
  rw [hashSig_words] at hlen
  match vs, hlen with
  | [pk, d, l, sg, sc], _ =>
  obtain ⟨e1, e2, e3⟩ := bufs_same hb
  change Curry.apply [ArgWord.addr, .addr, .int 64, .addr, .addr] (hPost (I := I)) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, .addr, .int 64, .addr, .addr] (hPost (I := I)) _ m₂ m' r
  dsimp only [Curry.apply, hPost, ArgWord.ofRaw] at h ⊢
  simp only [BitVec.setWidth_eq] at h ⊢
  have e2' : Spec.Ecdsa.bytesAt m₁ d (show BitVec abi.ptrBits from l).toNat =
      Spec.Ecdsa.bytesAt m₂ d (show BitVec abi.ptrBits from l).toNat := e2
  rw [← e1, ← e2', ← e3]; exact h

theorem leak_local : ∀ f, some (hLeak (I := I)) = some f → ∀ vs m₁ m₂,
    vs.length = (I.verifyHashSig.words abi.ptrBits).length →
    Curry.apply (I.verifyHashSig.words abi.ptrBits) (Curry.const (fun (_ : Mem) => True) _) vs m₂ →
    (∀ b ∈ Sig.bufs I.verifyHashSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply _ f vs m₁ = Curry.apply _ f vs m₂ := by
  intro f hf vs m₁ m₂ hlen _ hb
  cases hf
  rw [hashSig_words] at hlen
  match vs, hlen with
  | [pk, d, l, sg, sc], _ =>
  obtain ⟨e1, e2, e3⟩ := bufs_same hb
  change Curry.apply [ArgWord.addr, .addr, .int 64, .addr, .addr] (hLeak (I := I)) _ m₁ =
    Curry.apply [ArgWord.addr, .addr, .int 64, .addr, .addr] (hLeak (I := I)) _ m₂
  dsimp only [Curry.apply, hLeak, ArgWord.ofRaw]
  simp only [BitVec.setWidth_eq]
  have e2' : Spec.Ecdsa.bytesAt m₁ d (show BitVec abi.ptrBits from l).toNat =
      Spec.Ecdsa.bytesAt m₂ d (show BitVec abi.ptrBits from l).toNat := e2
  rw [e1, e2', e3]

/-- A state satisfying `verifyHashContract`'s precondition, with an empty hash. -/
def hashSatState (L : Nat) : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r6 => 0x3000 | .r7 => 0x8000 | _ => 0
  lr := 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x1000, 2 * L + 1⟩, ⟨0x2000, 0⟩, ⟨0x3000, 2 * L⟩]
  wr := [⟨0x8000, 8192⟩]

theorem hashSat (h66 : I.curve.len ≤ 66) : (I.verifyHashContract abi 112).pre (hashSatState I.curve.len) := by
  sig_pre [Spec.Ecdsa.Instance.verifyHashContract, Spec.Ecdsa.Instance.verifyHashSig, Spec.Ecdsa.scratchWords,
    PPC64LE.abi, PPC64LE.argRegs, stackBelow, hashSatState]
  sig_and_intros
  all_goals first
    | decide
    | rfl
    | (refine Region.disjoint_of_le ?_ ?_ ?_ <;> simp only [BitVec.reduceToNat, BitVec.reduceSub] <;> omega)
    | (simp only [BitVec.reduceToNat]; omega)

/-- `vg_ecdsa_<curve>_verify`, from the verification of the `len` bytes. -/
theorem verifyHash_verified {wide : Bool} {core : Prog isa}
    (hL : 8 * I.curve.len = Spec.Ecdsa.nBits I.curve + if wide then 7 else 0) (h66 : I.curve.len ≤ 66)
    (hcore : Verified target core (I.verifyContract abi 0)) {hc : Taint.Hint taint.T}
    (htc : (taint.check (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8]) (convert I.curve.len wide) hc).isSome = true) :
    Verified target (verifyHash I.curve.len wide core) (I.verifyHashContract abi 112) := by
  have hk : (I.verifyHashSig.words abi.ptrBits).length < 8 := by rw [hashSig_words]; decide
  have hb : 32 < 112 ∧ 112 < 4096 ∧ 112 % 16 = 0 ∧ 80 * Elem.u8.size + 32 ≤ 112 := by decide
  have hsat : ∃ s, (I.verifyHashContract abi 112).pre s := ⟨_, hashSat h66⟩
  exact Verified.stackScratchL (sig := I.verifyHashSig) (nm := "buf") (e := .u8) (n := 80)
    (pre := Curry.const (fun _ => True) _) (post := hPost (I := I)) (wa := true) (stack := 0) (bytes := 112)
    (hashed_verified hL h66 hcore htc ⟨_, narrow_pre (nm := "buf") hk hb pre_local hsat.choose_spec rfl⟩)
    hk hb pre_local post_local leak_local hsat rfl

end

end VG.Proof.Ecdsa.Verify.PPC64LE.Hash
