module

public import VerifiedGarbage.Proof.Bignum.X86_64.CrtFrame
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtPreR2
public import VerifiedGarbage.Impl.Rsa.X86_64.CrtIfma
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix

/-!
# RSA with AVX512_IFMA on x86-64: `R_X² mod X` from the key's precomputed values

`r2X q j`, in a prime's workspace, copies `R_X² mod X` from the key's
precomputed values `pre` into its array `j`, masked by `n`'s mask as the
prime is: where the mask is clear the prime is 3, whose `R_X² mod 3` is 1,
which `orOne` writes. From a state where `pre`'s address and the words
copied are outside the working space (`PreW`), the array holds `R_X² mod X`
in both cases (`r2X_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.MlKem.X86_64

/-- The low word: the masked word or'ed with 1 where the mask is clear. -/
theorem oneWord (c : Bool) (x : BitVec 64) :
    (mask c ^^^ BitVec.signExtend 64 (BitVec.ofInt 32 (-1))) &&& (1 : BitVec 64) ||| x &&& mask c =
      if c then x else 1 := by
  cases c
  · rw [mask_false, show x &&& (0 : BitVec 64) = 0 from BitVec.and_zero,
      show ∀ y : BitVec 64, y ||| (0 : BitVec 64) = y from fun _ => BitVec.or_zero]
    show _ = (1 : BitVec 64); decide
  · rw [mask_true, BitVec.and_allOnes, show (BitVec.allOnes 64 ^^^ BitVec.signExtend 64 (BitVec.ofInt 32 (-1))) &&&
      (1 : BitVec 64) = 0#64 by decide, BitVec.zero_or]; rfl

theorem orOne_ok {t : State} {G : Addr} {Zx d : Nat} {c : Bool} {x : BitVec 64} (hs : Scr t G Zx)
    (hbx : t.gpr .rbx = off G d) (h15 : t.gpr .r15 = mask c) (hd : d + 8 ≤ Zx)
    (hx : word t.mem G d = x &&& mask c) :
    WP isa (.block orOne) t fun t' => t'.mem = t.mem.writeW (off G d) (if c then x else 1) ∧ Keep [.rax] t t' :=
  WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = t.mem.writeW (off G d) (if c then x else 1)) (by
    unfold orOne
    xrun [State.ea, at0, hbx, h15, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hs.ld hd, hs.st hd, hx,
      oneWord]) rfl) fun t' ⟨h, k⟩ => ⟨h, k⟩

/-- The word of `pre` that `r2X q` starts from: `4 w_X`, or `5 w_X` for `q`. -/
abbrev r2XOff (q : Bool) (wx : Nat) : Nat := 4 * wx + if q then wx else 0

/-- `r2X`'s block: `pre`'s word `r2XOff` into `rsi`, `w_X` into `r12`, the
array into `rbx`. -/
theorem r2XBlk_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {k n V : Nat} {q : Bool} {j : Nat}
    (hj : j < 8) (hc : SubCtx s B Z o w wx minv) (hp : PreW s B Z k n V) :
    WP isa (.block (r2XBlk q j)) s fun t => t.gpr .rsi = off (stackArg s 12) (8 * r2XOff q wx) ∧
      t.gpr .rbx = off (off B o) (slot wx j) ∧ t.gpr .r12 = BitVec.ofNat 64 wx ∧ t.mem = s.mem ∧
      Keep [.rax, .rsi, .rbx, .r12] s t := by
  have hg := hc.good
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off B o) (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot wx 8 hi; omega_arith)
  have e104 : off (s.gpr .rsp) (8 * 13) = stackArgAddr s 12 := rfl
  have hA : s.mem.readW (stackArgAddr s 12) 64 = stackArg s 12 := rfl
  have hoff : ∀ d : Nat, stackArg s 12 + BitVec.ofNat 64 d = off (stackArg s 12) d := fun _ => rfl
  refine WP.mono (WP.keep (c := .block (r2XBlk q j)) [.rax, .rsi, .rbx, .r12] (Q := fun t =>
      t.gpr .rsi = off (stackArg s 12) (8 * r2XOff q wx) ∧ t.gpr .rbx = off (off B o) (slot wx j) ∧
      t.gpr .r12 = BitVec.ofNat 64 wx ∧ t.mem = s.mem) ?_ (by cases q <;> rfl))
    fun t ⟨⟨h1, h2, h3, h4⟩, k⟩ => ⟨h1, h2, h3, h4, k⟩
  cases q
  · unfold r2XBlk Crt.preArg Crt.stk
    simp only [List.cons_append, List.nil_append, Bool.false_eq_true, ↓reduceIte, List.append_nil]
    xrun [State.ea, hdr, hg.rdi, hdrOff, e104, hp.arg, hA, hl sW (by decide), hg.hdr.hw, hl (sArr j) (by unfold sArr; omega),
      hg.hdr.harr j hj, BitVec.ofNat_add_ofNat]
    rw [hoff]; congr 1; simp only [r2XOff, Bool.false_eq_true, ↓reduceIte]; omega
  · unfold r2XBlk Crt.preArg Crt.stk
    simp only [List.cons_append, List.nil_append, ↓reduceIte]
    xrun [State.ea, hdr, hg.rdi, hdrOff, e104, hp.arg, hA, hl sW (by decide), hg.hdr.hw, hl (sArr j) (by unfold sArr; omega),
      hg.hdr.harr j hj, BitVec.ofNat_add_ofNat]
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, hoff]; congr 1; simp only [r2XOff, ↓reduceIte]; omega

/-- `r2X q j`: `[j] := c ? V : 1`, `V` the value of `pre`'s `w_X` words from
`r2XOff q w_X`, `c` the prime's mask. Only the array changes. -/
theorem r2X_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {V : Nat} {c : Bool} {q : Bool} {j : Nat}
    (hj : j < 8) (hc : SubCtx s B Z o w wx minv) (hw2 : 2 ≤ wx) (hwx : wx ≤ w)
    (hw30 : w < 2 ^ 30) (hm : word s.mem B (8 * sMask) = mask c)
    (hp : PreW s B Z (r2XOff q wx) wx V) :
    WP isa (seqs (r2X q j)) s fun t => SubCtx t B Z o w wx minv ∧
      wv t.mem (off B o) (slot wx j) wx = (if c then V else 1) ∧
      Frm (off B o) [(slot wx j, 8 * (wx + 2))] s.mem t.mem ∧ Keep mmRegs s t := by
  have hg := hc.good
  have hBn := hc.scr.nowrap
  have hGn : (off B o).toNat + slot wx 8 ≤ 2 ^ 64 := hg.scr.nowrap
  have hi := hc.hi
  have hlo := hc.lo
  have sJ := slot_le (w := wx) hj
  have hJ0 := hdr_lt_slot wx j (show 31 < 32 by decide)
  have h256 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_arith
  unfold r2X maskN
  simp only [List.cons_append, List.nil_append, seqs]
  -- `rsi`, `r12`, `rbx`.
  refine WP.seq (WP.mono (r2XBlk_ok hj hc hp) fun t₁ ⟨hsi, hbx, h12, hm₁, k₁⟩ => ?_)
  have hs₁ : Scr t₁ (off B o) (slot wx 8) := hg.scr.congr k₁.2.2
  -- The copy from `pre`.
  have hout : ∀ i < wx, ∀ b < 8, slot wx 8 ≤
      ofs (off B o) (off (stackArg s 12) (8 * r2XOff q wx + 8 * i) + BitVec.ofNat 64 b) := fun i hi' b hb => by
    have := hp.out i hi' b hb
    rcases ofs_rebase B (off (stackArg s 12) (8 * r2XOff q wx + 8 * i) + BitVec.ofNat 64 b) (o := o)
      (by omega_arith) with ⟨_, h2⟩ | ⟨h1, _⟩
    · omega_arith
    · omega_arith
  refine WP.seq (WP.mono (copyWords_ok (S := stackArg s 12) (eS := 8 * r2XOff q wx) (D := off B o) (eD := slot wx j)
    hsi hbx h12 (by omega_arith) (by omega_arith) (by omega_arith)
    (fun i hi' => by rw [k₁.2.1, k₁.2.2]; exact hp.rd i hi') (fun i hi' => hs₁.st (by omega_arith))
    (fun i hi' b hb => Or.inr (by have := hout i hi' b hb; omega_arith))) fun t₂ ⟨hv₂, _, ho₂, k₂⟩ => ?_)
  rw [hm₁, hp.val] at hv₂
  rw [hm₁] at ho₂
  have k₁₂ := k₁.trans k₂
  have f₂ : Frm (off B o) [(slot wx j, 8 * wx)] s.mem t₂.mem := Frm.of_outside ho₂ (by simp)
  have hc₂ : SubCtx t₂ B Z o w wx minv := hc.of_frm f₂ (fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only; omega_arith) k₁₂.2.2 (k₁₂.gpr (by decide))
  have hM₂ : word t₂.mem B (8 * sMask) = mask c := by
    rw [f₂.word_below (L := slot wx 8) (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega_arith)
      (by omega_arith) (by omega_arith) (by have := hdr_lt_slot w 8 (show sMask < 32 by decide); omega_arith)]; exact hm
  -- The mask.
  have g₂ := hc₂.good
  have hl : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (off (off B o) (8 * i)) 8 := fun i hi' =>
    g₂.scr.ld (by have := hdr_lt_slot wx 8 hi'; omega_arith)
  have hln : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (off B (8 * i)) 8 := fun i hi' =>
    hc₂.scr.ld (by have := hdr_lt_slot w 8 hi'; omega_arith)
  refine WP.seq (WP.mono (WP.keep [.rax, .r15, .r12, .rbx] (Q := fun t => t.gpr .r15 = mask c ∧
      t.gpr .r12 = BitVec.ofNat 64 wx ∧ t.gpr .rbx = off (off B o) (slot wx j) ∧ t.mem = t₂.mem)
    (by xrun [State.ea, hdr, Crt.ws, hc₂.rdi, hdrOff, hl Crt.sLink (by decide), hc₂.link, hln sMask (by decide), hM₂,
      hl (sArr j) (by unfold sArr; omega_arith), hl sW (by decide), g₂.hdr.harr j hj, g₂.hdr.hw]) rfl)
    fun t₃ ⟨⟨h15, h12', hbx', hm₃⟩, k₃⟩ => ?_)
  have hs₃ := g₂.scr.congr k₃.2.2
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = t₃.mem → Keep [.r14] t₃ t → t.cf = t₃.cf →
      MaskInv t₃ (off B o) (slot wx 8) (slot wx j) c 0 t := fun t h14 hm' k _ =>
    ⟨hs₃.congr k.2.2, k.mono (by decide), h14, by rw [hm']; exact Outside.refl _ _ _ _,
      fun i hi' => absurd hi' (Nat.not_lt_zero _)⟩
  refine WP.seq (WP.mono (wordLoop_ok (start := 0) (N := wx) (by omega_arith) (by omega_arith)
    (MaskInv t₃ (off B o) (slot wx 8) (slot wx j) c) h0
    (fun i _ hi' t hI => maskStep_ok hbx' h15 h12' (by omega_arith) (by omega_arith) hi' hI)) fun t₄ hI => ?_)
  -- `1` where the mask is clear.
  have k₄ := hI.keep
  have hbx₄ : t₄.gpr .rbx = off (off B o) (slot wx j) := (k₄.gpr (by decide)).trans hbx'
  have h15₄ : t₄.gpr .r15 = mask c := (k₄.gpr (by decide)).trans h15
  have hx₄ : word t₄.mem (off B o) (slot wx j) = word t₂.mem (off B o) (slot wx j) &&& mask c := by
    have := hI.done 0 (by omega_arith); rw [Nat.mul_zero, Nat.add_zero, hm₃] at this; exact this
  refine WP.mono (orOne_ok hI.scr hbx₄ h15₄ (by omega_arith) hx₄) fun t ⟨hm₅, k₅⟩ => ?_
  have o₄ := hI.out
  rw [hm₃] at o₄
  have o₅ := writeW_outside t₄.mem (off B o) (d := slot wx j) (if c then word t₂.mem (off B o) (slot wx j) else 1)
    (by omega_arith)
  rw [← hm₅] at o₅
  have f₂t : Frm (off B o) [(slot wx j, 8 * wx)] t₂.mem t.mem :=
    (Frm.of_outside o₄ (by simp)).trans (Frm.of_outside (o₅.mono (o' := slot wx j) (n' := 8 * wx) (Nat.le_refl _)
      (by omega_arith)) (by simp))
  have K := ((k₁₂.trans k₃).trans k₄).trans k₅
  have hup : ∀ i < wx, i ≠ 0 → word t.mem (off B o) (slot wx j + 8 * i) =
      word t₂.mem (off B o) (slot wx j + 8 * i) &&& mask c := fun i hi' hne => by
    rw [hm₅, (writeW_outside _ _ _ (by omega_arith)).word (Or.inr (by omega_arith)) (by omega_arith), hI.done i hi', hm₃]
  refine ⟨hc₂.of_frm f₂t (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega_arith)
    (k₃.trans k₄ |>.trans k₅).2.2 ((k₃.trans k₄ |>.trans k₅).gpr (by decide)), ?_, ?_, K.mono (by decide)⟩
  · cases c
    · rw [wv_single _ _ _ (i := 0) wx (by omega_arith) fun q hq hne => by
        rw [hup q hq hne, mask_false]; exact BitVec.and_zero, Nat.mul_zero, Nat.add_zero, hm₅, word_writeW_self]
      rfl
    · simp only [↓reduceIte]; rw [← hv₂]
      refine wv_congr fun i hi' => ?_
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rw [Nat.mul_zero, Nat.add_zero, hm₅, word_writeW_self]; rfl
      · rw [hup i hi' (by omega_arith), mask_true, BitVec.and_allOnes]
  · exact (f₂.trans f₂t).widen fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; simp only; omega_arith⟩

end VG.Proof.Bignum.X86_64
