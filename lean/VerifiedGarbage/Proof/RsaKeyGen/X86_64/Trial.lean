import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdE
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.RsaKeyGen.TrialMath

/-!
# A candidate on x86-64: trial division

For each prime `s` of the table, `acc := (acc + h) 2^(−32) mod s` over the
32-bit halves `h` of `c` from the least significant (`redc32`, Montgomery
reduction with `−s⁻¹ mod 2^64`): `acc < 2 s` and
`acc 2^(64 w) ≡ c (mod s)`, so `s` divides `c` iff `acc` is 0 or `s`.
-/

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- `redc32`: `acc := (acc + h) 2^(−32) mod s`, below `2 s`, for `h = rax <
2^32`, `acc = rbp < 2 s`, `s = rbx` and `−s⁻¹ = r15`. -/
theorem redc32_ok {t : State} {s : Nat} (hax : (t.gpr .rax).toNat < 2 ^ 32) (hbp : (t.gpr .rbp).toNat < 2 * s)
    (hbx : (t.gpr .rbx).toNat = s) (h15 : (s * (t.gpr .r15).toNat + 1) % 2 ^ 64 = 0) (hs3 : 3 ≤ s) (hs : s < 2 ^ 13) :
    WP isa (.block redc32) t fun t' =>
      (t'.gpr .rbp).toNat < 2 * s ∧
      ((t'.gpr .rbp).toNat * 2 ^ 32) % s = ((t.gpr .rax).toNat + (t.gpr .rbp).toNat) % s ∧
      t'.mem = t.mem ∧ Keep [.rax, .rcx, .rdx, .rbp] t t' := by
  have hX : (t.gpr .rax + t.gpr .rbp).toNat = (t.gpr .rax).toNat + (t.gpr .rbp).toNat := by
    rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have hXs : (t.gpr .rax).toNat + (t.gpr .rbp).toNat < s * 2 ^ 32 := by
    have : 2 ≤ s := by omega
    have : 2 * s ≤ s * 2 ^ 31 := by rw [Nat.mul_comm 2]; exact Nat.mul_le_mul_left _ (by decide)
    have : s * 2 ^ 31 + s * 2 ^ 31 = s * 2 ^ 32 := by rw [← Nat.mul_add]; rfl
    omega
  obtain ⟨_, hlt, hmod⟩ := redc_math (X := (t.gpr .rax).toNat + (t.gpr .rbp).toNat) (sv := (t.gpr .r15).toNat) h15 hXs
  refine WP.mono (WP.keep [.rax, .rcx, .rdx, .rbp] (Q := fun t' =>
      (t'.gpr .rbp).toNat = ((t.gpr .rax).toNat + (t.gpr .rbp).toNat +
        ((t.gpr .rax).toNat + (t.gpr .rbp).toNat) * (t.gpr .r15).toNat % 2 ^ 64 % 2 ^ 32 * s) / 2 ^ 32 ∧
      t'.mem = t.mem) ?_ rfl) fun t' ⟨⟨h, hm⟩, k⟩ => ⟨by rw [h]; exact hlt, by rw [h]; exact hmod, hm, k⟩
  unfold redc32
  xrun
  have hu : ((t.gpr .rax).toNat + (t.gpr .rbp).toNat) * (t.gpr .r15).toNat % 2 ^ 64 % 2 ^ 32 < 2 ^ 32 :=
    Nat.mod_lt _ (by decide)
  have hus : ((t.gpr .rax).toNat + (t.gpr .rbp).toNat) * (t.gpr .r15).toNat % 2 ^ 64 % 2 ^ 32 * s < 2 ^ 45 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le hu (Nat.le_of_lt hs) (by omega)) (by decide)
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add, BitVec.toNat_ofNat, hX,
    BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat, hbx]
  generalize ((t.gpr .rax).toNat + (t.gpr .rbp).toNat) * (t.gpr .r15).toNat % 2 ^ 64 % 2 ^ 32 = U at hu hus ⊢
  rw [Nat.mod_eq_of_lt (b := 2 ^ 64) (by omega : U < 2 ^ 64), Nat.mod_eq_of_lt (b := 2 ^ 64) (by omega : U * s < 2 ^ 64),
    Nat.mod_eq_of_lt (b := 2 ^ 64) (by omega), Nat.add_comm]

/-- After `j` words of a prime's reduction. -/
structure TrInv (s₀ : State) (B : Addr) (d sp : Nat) (j : Nat) (t : State) : Prop where
  acc : (t.gpr .rbp).toNat < 2 * sp
  val : (t.gpr .rbp).toNat * 2 ^ (64 * j) % sp = wv s₀.mem B d j % sp
  mem : t.mem = s₀.mem
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  keep : Keep [.rax, .rcx, .rdx, .rbp, .rsi, .r14] s₀ t

theorem trStep_ok {s₀ : State} {B : Addr} {Z d w sp : Nat} (hs : Scr s₀ B Z) (h8 : s₀.gpr .r8 = off B d)
    (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w) (hbx : (s₀.gpr .rbx).toNat = sp)
    (h15 : (sp * (s₀.gpr .r15).toNat + 1) % 2 ^ 64 = 0) (hs3 : 3 ≤ sp) (hs13 : sp < 2 ^ 13)
    (hw : w < 2 ^ 31) (hd : d + 8 * w ≤ Z) {j : Nat} (hj : j < w) {t : State} (hI : TrInv s₀ B d sp j t) :
    WP isa (.block ((([.mov .rsi (.mem (ix .r8 .r14)), .mov32 .rax (.reg .rsi)] : List Instr) ++ redc32 ++
        ([.mov .rax (.reg .rsi), .shift .shr .rax 32] : List Instr) ++ redc32) ++
        ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ TrInv s₀ B d sp (j + 1) t' := by
  have hn := hs.nowrap
  have t8 : t.gpr .r8 = off B d := (hI.keep.gpr (by decide)).trans h8
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  have tbx : (t.gpr .rbx).toNat = sp := by rw [hI.keep.gpr (by decide)]; exact hbx
  have t15 : (sp * (t.gpr .r15).toNat + 1) % 2 ^ 64 = 0 := by rw [hI.keep.gpr (by decide)]; exact h15
  have hld : InRegions (t.rd ++ t.wr) (off B (d + 8 * j)) 8 := by
    rw [hI.keep.2.1, hI.keep.2.2]; exact hs.ld (by omega)
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rsi, .rax] (Q := fun t₁ => t₁.gpr .rsi = word s₀.mem B (d + 8 * j) ∧
      (t₁.gpr .rax).toNat = (word s₀.mem B (d + 8 * j)).toNat % 2 ^ 32 ∧ t₁.mem = t.mem) (by
    xrun [State.ea, ix, addr0 t8 hI.r14, hld, hI.mem]
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (b := 2 ^ 64) (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))]) rfl) fun t₁ ⟨⟨hsi₁, hax₁, hm₁⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (redc32_ok (s := sp) (by rw [hax₁]; exact Nat.mod_lt _ (by decide))
    (by rw [k₁.gpr (by decide)]; exact hI.acc) (by rw [k₁.gpr (by decide)]; exact tbx)
    (by rw [k₁.gpr (by decide)]; exact t15) hs3 hs13) fun t₂ ⟨hacc₂, hval₂, hm₂, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun t₃ => (t₃.gpr .rax).toNat = (word s₀.mem B (d + 8 * j)).toNat / 2 ^ 32 ∧
      t₃.mem = t₂.mem) (by
    xrun [show t₂.gpr .rsi = word s₀.mem B (d + 8 * j) from (k₂.gpr (by decide)).trans hsi₁]
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]) rfl) fun t₃ ⟨⟨hax₃, hm₃⟩, k₃⟩ => ?_
  rw [WP.block_append_iff]
  have hhi : (word s₀.mem B (d + 8 * j)).toNat / 2 ^ 32 < 2 ^ 32 := by
    have := (word s₀.mem B (d + 8 * j)).isLt; omega
  refine WP.mono (redc32_ok (s := sp) (by rw [hax₃]; exact hhi) (by rw [k₃.gpr (by decide)]; exact hacc₂)
    (by rw [k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide)]; exact tbx)
    (by rw [k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide)]; exact t15) hs3 hs13)
    fun t₄ ⟨hacc₄, hval₄, hm₄, k₄⟩ => ?_
  have kk := ((k₁.trans k₂).trans k₃).trans k₄
  refine WP.mono (count_ok t₄ ((kk.gpr (by decide)).trans hI.r14) ((kk.gpr (by decide)).trans t12) (by omega) (by omega))
    fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ⟨by rw [k'.gpr (by decide)]; exact hacc₄, ?_,
      by rw [hm', hm₄, hm₃, hm₂, hm₁, hI.mem], h14, ((hI.keep.trans kk).trans k').mono (by decide)⟩⟩
  rw [k'.gpr (by decide), wv]
  rw [hax₃, show t₃.gpr .rbp = t₂.gpr .rbp from k₃.gpr (by decide)] at hval₄
  rw [hax₁, show t₁.gpr .rbp = t.gpr .rbp from k₁.gpr (by decide)] at hval₂
  exact trial_word_math hval₂ hval₄ hI.val

theorem xor_lt1 (a b : BitVec 64) : (a ^^^ b).toNat < BitVec.toNat (1 : BitVec 64) ↔ a = b := by
  rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]
  constructor
  · intro h
    have h0 : a ^^^ b = 0 := BitVec.eq_of_toNat_eq (by rw [show BitVec.toNat (0 : BitVec 64) = 0 from rfl]; omega)
    have := congrArg (· ^^^ b) h0
    simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero, z_xor] at this
    exact this
  · rintro rfl; rw [BitVec.xor_self]; decide

/-- The masks of `acc = 0` and `acc = s`, or'ed. -/
theorem flag_eq (a b : BitVec 64) :
    (0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide (a.toNat < BitVec.toNat (1 : BitVec 64)))) |||
      0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide ((a ^^^ b).toNat < BitVec.toNat (1 : BitVec 64))))) =
      mask (decide (a.toNat = 0 ∨ a.toNat = b.toNat)) := by
  have h1 : decide (a.toNat < BitVec.toNat (1 : BitVec 64)) = decide (a.toNat = 0) :=
    decide_eq_decide.mpr (by rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega)
  have h2 : decide ((a ^^^ b).toNat < BitVec.toNat (1 : BitVec 64)) = decide (a.toNat = b.toNat) :=
    decide_eq_decide.mpr ((xor_lt1 a b).trans BitVec.toNat_inj.symm)
  rw [h1, h2, mask_or']
  unfold mask
  congr 3
  exact (Bool.decide_or _ _).symm

theorem sxFFFF : BitVec.signExtend 64 (0xFFFF : BitVec 32) = 0xFFFF := by decide

/-- Entry `j` of the table word in `kT1` into `rbx`. -/
theorem entryLoad_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good t B Z w minv) (hZ : slot w 8 ≤ Z)
    {i j : Nat} (hi : i < 256) (hj : j < 4) (hT : word t.mem B (8 * kT1) = BitVec.ofNat 64 (tabWord i)) :
    WP isa (.block (([.mov .rbx (.mem (hdr kT1))] : List Instr) ++ (if j = 0 then [] else [.shift .shr .rbx (16 * j)]) ++
      ([.alu .and .rbx (.imm 0xFFFF)] : List Instr))) t fun t' =>
      (t'.gpr .rbx).toNat = tabEntry (4 * i + j) ∧ t'.mem = t.mem ∧ Keep [.rbx] t t' := by
  have hn := hg.scr.nowrap
  have hl : InRegions (t.rd ++ t.wr) (off B (8 * kT1)) 8 := hg.scr.ld (by have := hdr_lt_slot w 8 (show kT1 < 32 by decide); omega)
  have he := tabWord_entry hi hj
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
  · simp only [↓reduceIte, List.singleton_append]
    refine WP.mono (WP.keep [.rbx] (Q := fun t' => (t'.gpr .rbx).toNat = tabEntry (4 * i + 0) ∧ t'.mem = t.mem) ?_ rfl)
      fun t' ⟨⟨h1, h2⟩, k⟩ => ⟨h1, h2, k⟩
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl, hT, sxFFFF]
    rw [← he, Nat.mul_zero, BitVec.ushiftRight_zero]
  all_goals
    simp only [Nat.succ_ne_zero, Nat.reduceMul, ↓reduceIte, List.cons_append, List.nil_append]
    refine WP.mono (WP.keep [.rbx] (Q := fun t' => (t'.gpr .rbx).toNat = tabEntry _ ∧ t'.mem = t.mem) ?_ rfl)
      fun t' ⟨⟨h1, h2⟩, k⟩ => ⟨h1, h2, k⟩
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl, hT, sxFFFF]
    exact he

/-- `trialEntry j`: the mask of `s ∣ c`, for entry `j` of the table word in
`kT1`, or'ed into `kT2`. -/
theorem trialEntry_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) {i j : Nat} (hi : i < 256) (hj : j < 4)
    (hT : word s.mem B (8 * kT1) = BitVec.ofNat 64 (tabWord i)) :
    WP isa (seqs (trialEntry j)) s fun t =>
      word t.mem B (8 * kT2) =
        mask (decide (wv s.mem B (slot w aN) w % tabEntry (4 * i + j) = 0)) ||| word s.mem B (8 * kT2) ∧
      Good t B Z w minv ∧ Outside B (8 * kT2) 8 s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r12, .r14, .r15] s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have sN := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  obtain ⟨hodd, hs3, hs13⟩ := tabEntry_facts (i := 4 * i + j) (by omega)
  generalize hsp : tabEntry (4 * i + j) = sp at hodd hs3 hs13 ⊢
  unfold trialEntry
  simp only [seqs]
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (entryLoad_ok hg hZ hi hj hT) fun s₁ ⟨hbx₁, hm₁, k₁⟩ => ?_
  rw [hsp] at hbx₁
  refine WP.mono (minv_ok s₁ (by rw [hbx₁]; exact hodd)) fun s₂ ⟨h15, k₂, hm₂⟩ => ?_
  rw [hbx₁] at h15
  have hbx₂ : (s₂.gpr .rbx).toNat = sp := by rw [k₂.gpr (by decide)]; exact hbx₁
  have hdi₂ : s₂.gpr .rdi = B := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hg.rdi)
  have hl₂ : ∀ i < 32, InRegions (s₂.rd ++ s₂.wr) (off B (8 * i)) 8 := fun i hi => by
    rw [k₂.2.1, k₂.2.2, k₁.2.1, k₁.2.2]; exact hl i hi
  have hm12 : s₂.mem = s.mem := hm₂.trans hm₁
  refine WP.mono (WP.keep [.r12, .r8, .rbp] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .r8 = off B (slot w aN) ∧ t.gpr .rbp = 0 ∧ t.mem = s₂.mem) (by
    xrun [State.ea, hdr, hdi₂, hdrOff, hl₂ sW (by decide), hl₂ (sArr aN) (by decide), hm12, hg.hdr.hw,
      hg.hdr.harr aN (by decide)]) rfl) fun s₃ ⟨⟨h12, h8, hbp, hm₃⟩, k₃⟩ => ?_
  have hs₃ := hg.scr.congr (k₃.2.2.trans (k₂.2.2.trans k₁.2.2))
  have hbx₃ : (s₃.gpr .rbx).toNat = sp := by rw [k₃.gpr (by decide)]; exact hbx₂
  have h15₃ : (sp * (s₃.gpr .r15).toNat + 1) % 2 ^ 64 = 0 := by rw [k₃.gpr (by decide)]; exact h15
  refine WP.seq (WP.mono (wordLoop_ok (start := 0) (N := w) (by omega) hw' (TrInv s₃ B (slot w aN) sp)
    (fun t h14 hm k _ => ⟨by rw [k.gpr (by decide), hbp]; show 0 < 2 * sp; omega,
      by rw [k.gpr (by decide), hbp]; simp [wv], hm, h14, k.mono (by decide)⟩)
    (fun j' _ hj' t hI => trStep_ok hs₃ h8 h12 hbx₃ h15₃ hs3 (by omega) hw' (by omega) hj' hI)) fun s₄ hI => ?_)
  have hdi₄ : s₄.gpr .rdi = B := (hI.keep.gpr (by decide)).trans ((k₃.gpr (by decide)).trans hdi₂)
  have hs₄ := hs₃.congr hI.keep.2.2
  have hm4 : s₄.mem = s.mem := by rw [hI.mem, hm₃, hm12]
  have hl4 : InRegions (s₄.rd ++ s₄.wr) (off B (8 * kT2)) 8 := hs₄.ld (by have := hdr_lt_slot w 8 (show kT2 < 32 by decide); omega)
  have hw4 : InRegions s₄.wr (off B (8 * kT2)) 8 := hs₄.st (by have := hdr_lt_slot w 8 (show kT2 < 32 by decide); omega)
  have hdiv := trial_div hodd hI.acc hI.val
  rw [hm₃, hm12] at hdiv
  refine WP.mono (WP.keep [.rax, .rcx, .rdx] (Q := fun t => t.mem = s₄.mem.writeW (off B (8 * kT2))
      (mask (decide ((s₄.gpr .rbp).toNat = 0 ∨ (s₄.gpr .rbp).toNat = (s₄.gpr .rbx).toNat)) |||
        s₄.mem.readW (off B (8 * kT2)) 64)) (by
    xrun [State.ea, hdr, hdi₄, hdrOff, hl4, hw4, sx1]
    rw [flag_eq]) rfl) fun t ⟨hmt, kt⟩ => ⟨?_, ⟨hs₄.congr kt.2.2, (kt.gpr (by decide)).trans hdi₄, ?_⟩, ?_, ?_⟩
  · have hd : decide ((s₄.gpr .rbp).toNat = 0 ∨ (s₄.gpr .rbp).toNat = (s₄.gpr .rbx).toNat) =
        decide (wv s.mem B (slot w aN) w % sp = 0) := decide_eq_decide.mpr (by
      rw [show (s₄.gpr .rbx).toNat = sp by rw [hI.keep.gpr (by decide)]; exact hbx₃]; exact hdiv.symm)
    rw [hmt, word_writeW_self, hd, hm4]
  · rw [hmt, hm4]; exact hg.hdr.store (by decide) (by decide) _
  · rw [hmt, hm4]; exact writeW_outside _ _ _ (by have := hdr_lt_slot w 8 (show kT2 < 32 by decide); omega)
  · exact ((((k₁.trans k₂).trans k₃).trans hI.keep).trans kt).mono (by decide)

end VG.Proof.RsaKeyGen.X86_64
