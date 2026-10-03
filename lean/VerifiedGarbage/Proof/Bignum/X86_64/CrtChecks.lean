import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Bignum.X86_64.Cmp
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFrame
import VerifiedGarbage.Impl.Rsa.X86_64.Crt

/-!
# `vg_rsa_private_crt` on x86-64: small pieces of the checks

`zeroArr j` clears array `j` (`zeroArr_ok`), `copyArr o a` copies `[a]` to
`[o]` (`copyArr_ok`), `maskArr j` ands `[j]` with the mask in `sMaskX`
(`maskArr_ok`); `eqCheck` ands into `sMask` the mask of `p q = n`
(`eqCheck_ok`), and `qinvCheck`, in `p`'s workspace, that of `qInv < p`
(`qinvCheck_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64

/-! ## Clearing, copying and masking an array -/

/-- `[j] := 0` over `w + 2` words. -/
theorem zeroArr_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) {j : Nat} (hj : j < 8) :
    WP isa (Crt.zeroArr j) s fun t => wv t.mem B (slot w j) (w + 2) = 0 ∧
      Outside B (slot w j) (8 * (w + 2)) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  unfold Crt.zeroArr
  refine WP.seq (WP.mono (WP.keep [.r8, .r12] (Q := fun t => t.gpr .r8 = off B (slot w j) ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl (sArr j) (by unfold sArr; omega), hl sW (by decide),
      hg.hdr.harr j hj, hg.hdr.hw]) rfl) fun s₁ ⟨⟨h8, h12, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (zeroAccLoop_ok (hg.scr.congr k₁.2.2) h8 h12 hw hw' ((slot_le hj).trans hZ))
    fun t ⟨hv, ho, k⟩ => ⟨hv, by rw [hm₁] at ho; exact ho, (k₁.trans k).mono (by decide)⟩

/-- `[o] := [a]` over `w` words. -/
theorem copyArr_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) {o a : Nat} (ho : o < 8) (ha : a < 8) (hoa : o ≠ a) :
    WP isa (seqs (Crt.copyArr o a)) s fun t => wv t.mem B (slot w o) w = wv s.mem B (slot w a) w ∧
      Outside B (slot w o) (8 * w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have so := (slot_le (w := w) ho).trans hZ
  have sa := (slot_le (w := w) ha).trans hZ
  have sp := slot_sep (w := w) hoa
  unfold Crt.copyArr
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.r12, .rsi, .rbx] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rsi = off B (slot w a) ∧ t.gpr .rbx = off B (slot w o) ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl (sArr a) (by unfold sArr; omega),
      hl (sArr o) (by unfold sArr; omega), hl sW (by decide), hg.hdr.harr a ha, hg.hdr.harr o ho,
      hg.hdr.hw]) rfl) fun s₁ ⟨⟨h12, hsi, hbx, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hg.scr.congr k₁.2.2
  refine WP.mono (copyWords_ok hsi hbx h12 hw hw' (by omega) (fun i hi => hs₁.ld (by omega))
    (fun i hi => hs₁.st (by omega)) (fun i hi b hb => by rw [ofs_off B (by omega)]; omega))
    fun t ⟨hv, _, ho', k⟩ => ⟨by rw [hv, hm₁], by rw [hm₁] at ho'; exact ho', (k₁.trans k).mono (by decide)⟩

/-- After `j` words of `maskArr`'s loop from `s₀`. -/
structure MaskInv (s₀ : State) (B : Addr) (Z e : Nat) (c : Bool) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : Outside B e (8 * j) s₀.mem t.mem
  done : ∀ i < j, word t.mem B (e + 8 * i) = word s₀.mem B (e + 8 * i) &&& mask c

theorem maskStep_ok {s₀ : State} {B : Addr} {Z w e : Nat} {c : Bool}
    (hbx : s₀.gpr .rbx = off B e) (h15 : s₀.gpr .r15 = mask c) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w)
    (hw : w < 2 ^ 32) (he : e + 8 * w ≤ Z) {j : Nat} (hj : j < w) {t : State}
    (hI : MaskInv s₀ B Z e c j t) :
    WP isa (.block (([.mov .rax (.mem (ix .rbx .r14)), .alu .and .rax (.reg .r15), .store (ix .rbx .r14) .rax] :
        List Instr) ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ MaskInv s₀ B Z e c (j + 1) t' := by
  have hn := hI.scr.nowrap
  have tbx : t.gpr .rbx = off B e := (hI.keep.gpr (by decide)).trans hbx
  have t15 : t.gpr .r15 = mask c := (hI.keep.gpr (by decide)).trans h15
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  have hv : word t.mem B (e + 8 * j) = word s₀.mem B (e + 8 * j) := hI.out.word (by omega) (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off B (e + 8 * j)) (word s₀.mem B (e + 8 * j) &&& mask c)) ?_ rfl)
    fun t₁ ⟨hm, k₁⟩ => ?_
  · xrun [State.ea, ix, addr0 tbx hI.r14, t15, hI.scr.ld (show e + 8 * j + 8 ≤ Z by omega),
      hI.scr.st (show e + 8 * j + 8 ≤ Z by omega), hv]
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14, ?_,
    fun i hi => ?_⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B _ (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hm', hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [(writeW_outside t.mem B _ (by omega)).word (by omega) (by omega)]; exact hI.done i hi
    · exact word_writeW_self _ _ _ _

/-- `[j] &= sMaskX` over `w` words. -/
theorem maskArr_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) {j : Nat} (hj : j < 8) {c : Bool}
    (hm : word s.mem B (8 * Crt.sMaskX) = mask c) :
    WP isa (seqs (Crt.maskArr j)) s fun t =>
      (∀ i < w, word t.mem B (slot w j + 8 * i) = word s.mem B (slot w j + 8 * i) &&& mask c) ∧
      wv t.mem B (slot w j) w = (if c then wv s.mem B (slot w j) w else 0) ∧
      Outside B (slot w j) (8 * w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have sj := (slot_le (w := w) hj).trans hZ
  unfold Crt.maskArr
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.r15, .r12, .rbx] (Q := fun t => t.gpr .r15 = mask c ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .rbx = off B (slot w j) ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl Crt.sMaskX (by decide),
      hl (sArr j) (by unfold sArr; omega), hl sW (by decide), hm, hg.hdr.harr j hj,
      hg.hdr.hw]) rfl) fun s₁ ⟨⟨h15, h12, hbx, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hg.scr.congr k₁.2.2
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₁.mem → Keep [.r14] s₁ t → t.cf = s₁.cf →
      MaskInv s₁ B Z (slot w j) c 0 t := fun t h14 hm k _ =>
    ⟨hs₁.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := w) (by omega) hw' (MaskInv s₁ B Z (slot w j) c) h0
    (fun i _ hi t hI => maskStep_ok hbx h15 h12 (by omega) (by omega) hi hI)) fun t hI => ?_
  have hd := hI.done
  have ho := hI.out
  rw [hm₁] at hd ho
  refine ⟨hd, ?_, ho, (k₁.trans hI.keep).mono (by decide)⟩
  cases c
  · exact (wv_eq_zero_iff _ _ _ _).mpr fun i hi => by rw [hd i hi, mask_false]; exact BitVec.and_zero
  · exact wv_congr fun i hi => by rw [hd i hi, mask_true, BitVec.and_allOnes]

/-! ## `p q = n` -/

/-- Two numbers of `n` words are equal only if their words are. -/
theorem wv_inj {m : Mem} {p : Addr} {d e : Nat} :
    ∀ n, wv m p d n = wv m p e n → ∀ i < n, word m p (d + 8 * i) = word m p (e + 8 * i)
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, h, i, hi => by
    simp only [wv] at h
    have hd := wv_lt m p d n
    have he := wv_lt m p e n
    have h1 : wv m p d n = wv m p e n := by
      have := congrArg (· % 2 ^ (64 * n)) h
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt he] at this
      exact this
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact wv_inj n h1 i hi
    · rw [h1] at h
      exact BitVec.eq_of_toNat_eq (Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos _) (Nat.add_left_cancel h))

theorem split_eq_iff {L H N R : Nat} (hN : N < R) : L + R * H = N ↔ L = N ∧ H = 0 := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos H with rfl | hH
    · rw [Nat.mul_zero, Nat.add_zero] at h; exact ⟨h, rfl⟩
    · have := Nat.le_mul_of_pos_right R hH; omega
  · rintro ⟨rfl, rfl⟩
    rw [Nat.mul_zero, Nat.add_zero]

theorem or_eq_zero (a b : BitVec 64) : a ||| b = 0 ↔ a = 0 ∧ b = 0 := BitVec.or_eq_zero_iff

theorem xor_eq_zero (a b : BitVec 64) : a ^^^ b = 0 ↔ a = b := BitVec.xor_eq_zero_iff

/-- After `j` words of a loop that ORs words into `rbp`, memory unchanged:
`rbp = 0` iff `P j`. -/
structure OrInv (s₀ : State) (B : Addr) (Z : Nat) (P : Nat → Prop) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rbp, .r14] s₀ t
  mem : t.mem = s₀.mem
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  val : t.gpr .rbp = 0 ↔ P j

theorem xorStep_ok {s₀ : State} {B : Addr} {Z w eA eN : Nat}
    (hbx : s₀.gpr .rbx = off B eA) (h10 : s₀.gpr .r10 = off B eN) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w)
    (hw : w < 2 ^ 32) (hA : eA + 8 * w ≤ Z) (hN : eN + 8 * w ≤ Z) {j : Nat} (hj : j < w) {t : State}
    (hI : OrInv s₀ B Z (fun j => ∀ i < j, word s₀.mem B (eA + 8 * i) = word s₀.mem B (eN + 8 * i)) j t) :
    WP isa (.block (([.mov .rax (.mem (ix .rbx .r14)), .alu .xor .rax (.mem (ix .r10 .r14)),
        .alu .or .rbp (.reg .rax)] : List Instr) ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] :
        List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧
        OrInv s₀ B Z (fun j => ∀ i < j, word s₀.mem B (eA + 8 * i) = word s₀.mem B (eN + 8 * i)) (j + 1) t' := by
  have hn := hI.scr.nowrap
  have tbx : t.gpr .rbx = off B eA := (hI.keep.gpr (by decide)).trans hbx
  have t10 : t.gpr .r10 = off B eN := (hI.keep.gpr (by decide)).trans h10
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t₁ => t₁.mem = t.mem ∧
      t₁.gpr .rbp = t.gpr .rbp ||| (word t.mem B (eA + 8 * j) ^^^ word t.mem B (eN + 8 * j))) ?_ rfl)
    fun t₁ ⟨⟨hm, hbp⟩, k₁⟩ => ?_
  · xrun [State.ea, ix, addr0 tbx hI.r14, addr0 t10 hI.r14, hI.scr.ld (show eA + 8 * j + 8 ≤ Z by omega),
      hI.scr.ld (show eN + 8 * j + 8 ≤ Z by omega)]
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide),
    by rw [hm', hm, hI.mem], h14, ?_⟩
  rw [(k'.gpr (by decide) : t'.gpr .rbp = t₁.gpr .rbp), hbp, or_eq_zero, xor_eq_zero,
    hI.val, hI.mem]
  constructor
  · rintro ⟨h1, h2⟩ i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    exacts [h1 i hi, h2]
  · intro h
    exact ⟨fun i hi => h i (by omega), h j (by omega)⟩

theorem orStep_ok {s₀ : State} {B : Addr} {Z w e : Nat} {A : Prop}
    (hbx : s₀.gpr .rbx = off B e) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w)
    (hw : w < 2 ^ 32) (he : e + 8 * w ≤ Z) {j : Nat} (hj : j < w) {t : State}
    (hI : OrInv s₀ B Z (fun j => A ∧ ∀ i < j, word s₀.mem B (e + 8 * i) = 0) j t) :
    WP isa (.block (([.mov .rax (.mem (ix .rbx .r14)), .alu .or .rbp (.reg .rax)] : List Instr) ++
        ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧
        OrInv s₀ B Z (fun j => A ∧ ∀ i < j, word s₀.mem B (e + 8 * i) = 0) (j + 1) t' := by
  have hn := hI.scr.nowrap
  have tbx : t.gpr .rbx = off B e := (hI.keep.gpr (by decide)).trans hbx
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t₁ => t₁.mem = t.mem ∧
      t₁.gpr .rbp = t.gpr .rbp ||| word t.mem B (e + 8 * j)) ?_ rfl)
    fun t₁ ⟨⟨hm, hbp⟩, k₁⟩ => ?_
  · xrun [State.ea, ix, addr0 tbx hI.r14, hI.scr.ld (show e + 8 * j + 8 ≤ Z by omega)]
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide),
    by rw [hm', hm, hI.mem], h14, ?_⟩
  rw [(k'.gpr (by decide) : t'.gpr .rbp = t₁.gpr .rbp), hbp, or_eq_zero, hI.val, hI.mem]
  constructor
  · rintro ⟨⟨hA, h1⟩, h2⟩
    refine ⟨hA, fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    exacts [h1 i hi, h2]
  · rintro ⟨hA, h⟩
    exact ⟨⟨hA, fun i hi => h i (by omega)⟩, h j (by omega)⟩

/-- `cmp rbp, 1; sbb rbp, rbp`: all ones iff `rbp` was zero. -/
theorem decide_lt_one (x : BitVec 64) : decide (x.toNat < (1 : BitVec 64).toNat) = decide (x = 0) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, ← BitVec.toNat_inj,
    show (1 : BitVec 64).toNat = 1 from rfl, show (0 : BitVec 64).toNat = 0 from rfl]
  constructor <;> intro h <;> omega

/-- The mask of `p q = n` (the accumulator's `2 w + 2` words against
`aN`'s `w`), and'ed into `sMask`. -/
theorem eqCheck_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 30) :
    WP isa (seqs Crt.eqCheck) s fun t =>
      word t.mem B (8 * sMask) = word s.mem B (8 * sMask) &&&
        mask (decide (wv s.mem B (slot w aAcc) (2 * w + 2) = wv s.mem B (slot w aN) w)) ∧
      Outside B (8 * sMask) 8 s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have hA : slot w aAcc + 16 * (w + 2) ≤ Z := by
    have := (slot_le (w := w) (show aTmp < 8 by decide)).trans hZ; simp only [slot, aTmp, aAcc] at this ⊢; omega
  have hN := (slot_le (w := w) (show aN < 8 by decide)).trans hZ
  have hS := hdr_lt_slot w aN (show sMask < 32 by decide)
  unfold Crt.eqCheck
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.r12, .rbx, .r10, .rbp] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rbx = off B (slot w aAcc) ∧ t.gpr .r10 = off B (slot w aN) ∧ t.gpr .rbp = 0 ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl (sArr aAcc) (by decide),
      hl (sArr aN) (by decide), hg.hdr.hw, hg.hdr.harr aAcc (by decide), hg.hdr.harr aN (by decide)]) rfl)
    fun s₁ ⟨⟨h12, hbx, h10, hbp, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hg.scr.congr k₁.2.2
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₁.mem → Keep [.r14] s₁ t → t.cf = s₁.cf →
      OrInv s₁ B Z (fun j => ∀ i < j, word s₁.mem B (slot w aAcc + 8 * i) = word s₁.mem B (slot w aN + 8 * i))
        0 t := fun t h14 hm k _ =>
    ⟨hs₁.congr k.2.2, k.mono (by decide), hm, h14, by
      rw [(k.gpr (by decide) : t.gpr .rbp = s₁.gpr .rbp), hbp]
      exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero _), fun _ => rfl⟩⟩
  refine WP.seq (WP.mono (wordLoop_ok (start := 0) (N := w) (by omega) (by omega) _ h0
    (fun j _ hj t hI => xorStep_ok hbx h10 h12 (by omega) (by omega) (by omega) hj hI)) fun s₂ hI => ?_)
  have s₂12 : s₂.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  have s₂bx : s₂.gpr .rbx = off B (slot w aAcc) := (hI.keep.gpr (by decide)).trans hbx
  refine WP.seq (WP.mono (WP.keep [.rax, .rbx, .r12] (Q := fun t => t.gpr .rbx = off B (slot w aAcc + 8 * w) ∧
      t.gpr .r12 = BitVec.ofNat 64 (w + 2) ∧ t.mem = s₂.mem) (by
      xrun [s₂12, s₂bx]
      refine ⟨?_, by rw [show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl, BitVec.ofNat_add_ofNat]⟩
      simp only [off, BitVec.ofNat_add_ofNat, BitVec.add_assoc]
      congr 2; omega) rfl)
    fun s₃ ⟨⟨hbx₃, h12₃, hm₃⟩, k₃⟩ => ?_)
  have hs₃ := hI.scr.congr k₃.2.2
  have h0' : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₃.mem → Keep [.r14] s₃ t → t.cf = s₃.cf →
      OrInv s₃ B Z (fun j => (∀ i < w, word s₁.mem B (slot w aAcc + 8 * i) = word s₁.mem B (slot w aN + 8 * i)) ∧
        ∀ i < j, word s₃.mem B (slot w aAcc + 8 * w + 8 * i) = 0) 0 t := fun t h14 hm k _ =>
    ⟨hs₃.congr k.2.2, k.mono (by decide), hm, h14, by
      rw [(k.gpr (by decide) : t.gpr .rbp = s₃.gpr .rbp), (k₃.gpr (by decide) : s₃.gpr .rbp = s₂.gpr .rbp),
        hI.val]
      exact ⟨fun h => ⟨h, fun i hi => absurd hi (Nat.not_lt_zero _)⟩, fun h => h.1⟩⟩
  refine WP.seq (WP.mono (wordLoop_ok (start := 0) (N := w + 2) (by omega) (by omega) _ h0'
    (fun j _ hj t hI => orStep_ok hbx₃ h12₃ (by omega) (by omega) hj hI)) fun s₄ hI₂ => ?_)
  have hm₄ : s₄.mem = s.mem := hI₂.mem.trans (hm₃.trans (hI.mem.trans hm₁))
  have hdi₄ : s₄.gpr .rdi = B :=
    ((((k₁.trans hI.keep).trans k₃).trans hI₂.keep).gpr (by decide)).trans hg.rdi
  refine WP.mono (WP.keep [.rbp] (Q := fun t => ∃ b : Bool, b = decide (s₄.gpr .rbp = 0) ∧
      t.mem = s₄.mem.writeW (off B (8 * sMask)) (mask b &&& word s₄.mem B (8 * sMask)))
    (by
      xrun [State.ea, hdr, hdi₄, hdrOff, hI₂.scr.ld (show 8 * sMask + 8 ≤ Z by omega),
        hI₂.scr.st (show 8 * sMask + 8 ≤ Z by omega)]
      exact ⟨_, decide_lt_one _, rfl⟩) rfl) fun t ⟨⟨b, hb, hm⟩, k₄⟩ => ?_
  have hR : b = decide (wv s.mem B (slot w aAcc) (2 * w + 2) = wv s.mem B (slot w aN) w) := by
    rw [hb, Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, hI₂.val, hm₃, hI.mem, hm₁,
      show 2 * w + 2 = w + (w + 2) by omega, wv_add, split_eq_iff (wv_lt _ _ _ _), wv_eq_zero_iff]
    exact and_congr ⟨fun h => wv_congr2 h, fun h => wv_inj w h⟩ Iff.rfl
  refine ⟨?_, ?_, ((((k₁.trans hI.keep).trans k₃).trans hI₂.keep).trans k₄).mono (by decide)⟩
  · rw [hm, word_writeW_self, hm₄, BitVec.and_comm, hR]
  · rw [hm, ← hm₄]
    exact writeW_outside _ B _ (by omega)

/-! ## `qInv < p` -/

/-- In a workspace at `off B o` linked to `B`: the mask of `qInv < p`
(`[aChunk] < [aN]`), and'ed into the `sMask` of the workspace at `B`. -/
theorem qinvCheck_ok {s : State} {B : Addr} {Z w o : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = off B o) (hH : Hdr s.mem (off B o) w minv) (hZ : o + slot w 8 ≤ Z)
    (hM : 8 * sMask + 8 ≤ o) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hL : word s.mem (off B o) (8 * Crt.sLink) = B) :
    WP isa (seqs Crt.qinvCheck) s fun t =>
      word t.mem B (8 * sMask) = word s.mem B (8 * sMask) &&&
        mask (decide (wv s.mem (off B o) (slot w Crt.aChunk) w < wv s.mem (off B o) (slot w aN) w)) ∧
      Outside B (8 * sMask) 8 s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hs' : Scr s (off B o) (Z - o) := hs.sub (by omega) (by omega)
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off B o) (8 * i)) 8 := fun i hi =>
    hs'.ld (by have := hdr_lt_slot w 8 hi; omega)
  have hC := slot_le (w := w) (show Crt.aChunk < 8 by decide)
  have hN := slot_le (w := w) (show aN < 8 by decide)
  unfold Crt.qinvCheck
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.r12, .rbx, .r10, .rbp] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rbx = off (off B o) (slot w Crt.aChunk) ∧ t.gpr .r10 = off (off B o) (slot w aN) ∧
      t.gpr .rbp = mask false ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hdi, hdrOff, hl sW (by decide), hl (sArr Crt.aChunk) (by decide),
      hl (sArr aN) (by decide), hH.hw, hH.harr Crt.aChunk (by decide), hH.harr aN (by decide)]) rfl)
    fun s₁ ⟨⟨h12, hbx, h10, hbp, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (cmpLoop_ok (hs'.congr k₁.2.2) hbx h10 h12 hbp hw hw' (by omega) (by omega))
    fun s₂ ⟨hbp₂, hm₂, k₂⟩ => ?_)
  rw [hm₁] at hbp₂
  have k12 := k₁.trans k₂
  have hdi₂ : s₂.gpr .rdi = off B o := (k12.gpr (by decide)).trans hdi
  have hs₂ := hs.congr k12.2.2
  have hL₂ : word s₂.mem (off B o) (8 * Crt.sLink) = B := by rw [hm₂, hm₁]; exact hL
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t =>
      t.mem = s₂.mem.writeW (off B (8 * sMask)) (s₂.gpr .rbp &&& word s₂.mem B (8 * sMask)))
    (by xrun [State.ea, hdr, Crt.ws, hdi₂, hdrOff, (hs'.congr k12.2.2).ld (d := 8 * Crt.sLink) (by
      have := hdr_lt_slot w 8 (show Crt.sLink < 32 by decide); omega), hL₂,
      hs₂.ld (show 8 * sMask + 8 ≤ Z by omega), hs₂.st (show 8 * sMask + 8 ≤ Z by omega)]) rfl)
    fun t ⟨hm, k₃⟩ => ?_
  refine ⟨?_, ?_, (k12.trans k₃).mono (by decide)⟩
  · rw [hm, word_writeW_self, hbp₂, hm₂, hm₁, BitVec.and_comm]
  · rw [hm, hm₂, hm₁]; exact writeW_outside _ B _ (by omega)

end VG.Proof.Bignum.X86_64
