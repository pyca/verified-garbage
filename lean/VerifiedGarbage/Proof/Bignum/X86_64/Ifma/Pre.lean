module

import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtUnit
import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
public import VerifiedGarbage.Impl.Rsa.X86_64.CrtIfma
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.Math
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtFrame
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Impl.Rsa.X86_64.Crt
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
meta import VerifiedGarbage.Impl.Rsa.X86_64.Crt
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy

/-! ### `Bignum.X86_64.CrtPreR2`, which this module and modules that import it used -/

section

/-!
# RSA with the CRT on x86-64: `R² mod n` from the key's precomputed values

`vg_rsa_private_crt_precomputed` copies `R² mod n` from the key's
precomputed values `pre`, its stack argument 12, rather than computing it
(`r2Pre`): `r2Pre_ok` gives what `R2w.choice_ok` gives of the computation,
from a state where `pre`'s address and its words `w` to `2 w - 1` are
outside the working space (`PreR2`), which every step that changes only the
working space and keeps the stack pointer keeps (`PreR2.congr`). It leaks
only the stack pointer, `w`, the working space and `pre`'s address
(`r2Pre_ct`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- Stack argument 12, `pre`, and its `n` words from `k`, whose value is `V`,
outside the working space at `B` of `Z` bytes. -/
structure PreW (t : State) (B : Addr) (Z k n V : Nat) : Prop where
  arg : InRegions (t.rd ++ t.wr) (stackArgAddr t 12) 8
  argOut : ∀ b < 8, Z ≤ ofs B (stackArgAddr t 12 + BitVec.ofNat 64 b)
  rd : ∀ j < n, InRegions (t.rd ++ t.wr) (off (stackArg t 12) (8 * k + 8 * j)) 8
  out : ∀ j < n, ∀ b < 8, Z ≤ ofs B (off (stackArg t 12) (8 * k + 8 * j) + BitVec.ofNat 64 b)
  val : wv t.mem (stackArg t 12) (8 * k) n = V

/-- `pre`'s address, after a step that changes only the working space and
keeps the stack pointer. -/
theorem PreW.arg_eq {t t' : State} {B : Addr} {Z k n V : Nat} (h : PreW t B Z k n V)
    (hi : InScr B Z t.mem t'.mem) (hsp : t'.gpr .rsp = t.gpr .rsp) : stackArg t' 12 = stackArg t 12 := by
  have ha : stackArgAddr t' 12 = stackArgAddr t 12 := by unfold stackArgAddr; rw [hsp]
  unfold stackArg
  rw [ha]
  exact Mem.readW_congr fun b hb => hi _ (h.argOut b hb)

/-- `PreW` holds after a step that changes only the working space and
keeps the stack pointer and the regions. -/
theorem PreW.congr {t t' : State} {B : Addr} {Z k n V : Nat} (h : PreW t B Z k n V)
    (hi : InScr B Z t.mem t'.mem) (hsp : t'.gpr .rsp = t.gpr .rsp) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) :
    PreW t' B Z k n V := by
  have ha : stackArgAddr t' 12 = stackArgAddr t 12 := by unfold stackArgAddr; rw [hsp]
  have hv := h.arg_eq hi hsp
  refine ⟨by rw [ha, hrd, hwr]; exact h.arg, fun b hb => by rw [ha]; exact h.argOut b hb,
    fun j hj => by rw [hv, hrd, hwr]; exact h.rd j hj, fun j hj => by rw [hv]; exact h.out j hj, ?_⟩
  rw [hv, ← h.val]
  exact wv_congr fun j hj => Mem.readW_congr fun b hb => hi _ (h.out j hj b hb)

/-- `pre`'s words `w` to `2 w - 1`, `R² mod N`. -/
abbrev PreR2 (t : State) (B : Addr) (Z w N : Nat) : Prop := PreW t B Z w w (2 ^ (128 * w) % N)

theorem PreR2.arg_eq {t t' : State} {B : Addr} {Z w N : Nat} (h : PreR2 t B Z w N)
    (hi : InScr B Z t.mem t'.mem) (hsp : t'.gpr .rsp = t.gpr .rsp) : stackArg t' 12 = stackArg t 12 :=
  PreW.arg_eq h hi hsp

theorem PreR2.congr {t t' : State} {B : Addr} {Z w N : Nat} (h : PreR2 t B Z w N)
    (hi : InScr B Z t.mem t'.mem) (hsp : t'.gpr .rsp = t.gpr .rsp) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) :
    PreR2 t' B Z w N :=
  PreW.congr h hi hsp hrd hwr

/-- `r2Pre`'s block. -/
abbrev r2PreBlk : List Instr :=
  ([.mov .rsi (.mem preArg)] : List Instr) ++ eightW ++
    ([.alu .add .rsi (.reg .rax), .mov .rbx (.mem (hdr (sArr aR2)))] : List Instr)

theorem r2Pre_eq : r2Pre = .seq (.block r2PreBlk) copyWords := rfl

/-- `r2Pre`'s block: `pre`'s word `w` into `rsi` and `aR2` into `rbx`. -/
theorem r2PreBlk_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N : Nat}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (hp : PreR2 s B Z w N) :
    WP isa (.block r2PreBlk) s fun t => t.gpr .rsi = off (stackArg s 12) (8 * w) ∧
      t.gpr .rbx = off B (slot w aR2) ∧ t.mem = s.mem ∧ Keep [.rax, .rsi, .rbx] s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  have e104 : off (s.gpr .rsp) (8 * 13) = stackArgAddr s 12 := rfl
  have hA : s.mem.readW (stackArgAddr s 12) 64 = stackArg s 12 := rfl
  have hax8 : ∀ r : BitVec 64, r = BitVec.ofNat 64 w → r + r + (r + r) + (r + r + (r + r)) =
      BitVec.ofNat 64 (8 * w) := by
    rintro r rfl; simp only [BitVec.ofNat_add_ofNat]; congr 1; omega_arith
  have hoff : stackArg s 12 + BitVec.ofNat 64 (8 * w) = off (stackArg s 12) (8 * w) := rfl
  refine WP.mono (WP.keep [.rax, .rsi, .rbx] (Q := fun t => t.gpr .rsi = off (stackArg s 12) (8 * w) ∧
      t.gpr .rbx = off B (slot w aR2) ∧ t.mem = s.mem) (by
    unfold r2PreBlk eightW preArg stk
    simp only [List.cons_append, List.nil_append]
    xrun [State.ea, hdr, hg.rdi, hdrOff, e104, hp.arg, hA, hl (sArr aR2) (by decide), hg.hdr.harr aR2 (by decide),
      h12, hax8 _ rfl, hoff]) rfl) fun t ⟨⟨hsi, hbx, hm⟩, k⟩ => ⟨hsi, hbx, hm, k⟩

/-- `r2Pre`: `R² mod N` from `pre` into `aR2`, as `R2w.choice_ok`
computes it. -/
theorem r2Pre_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N : Nat}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw30 : w < 2 ^ 30)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (hN : 0 < N) (hp : PreR2 s B Z w N) :
    WP isa r2Pre s fun t => Good t B Z w minv ∧
      wv t.mem B (slot w aR2) w < N ∧ wv t.mem B (slot w aR2) w % N = 2 ^ (64 * w) * 2 ^ (64 * w) % N ∧
      Frm B (r2Ranges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have hsR := slot_le (w := w) (show aR2 < 8 by decide)
  rw [r2Pre_eq]
  refine WP.seq (WP.mono (r2PreBlk_ok hg hZ h12 hp) fun t₁ ⟨hsi, hbx, hm₁, k₁⟩ => ?_)
  have hs₁ := hg.scr.congr k₁.2.2
  have h12₁ : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans h12
  refine WP.mono (copyWords_ok hsi hbx h12₁ (by omega_arith) (by omega_arith) (by omega_arith)
    (fun j hj => by rw [k₁.2.1, k₁.2.2]; exact hp.rd j hj) (fun j hj => hs₁.st (by omega_arith))
    (fun j hj b hb => Or.inr (by have := hp.out j hj b hb; omega_arith)))
    fun t ⟨hv, _, ho, k⟩ => ?_
  rw [hm₁] at hv ho
  have k₂ := k₁.trans k
  have hvR : wv t.mem B (slot w aR2) w = 2 ^ (128 * w) % N := by rw [hv, hp.val]
  have hA₂ : Arrays B w [aR2] s.mem t.mem :=
    Arrays.of_outside (w := w) (j := aR2) (by simp) ho (Nat.le_refl _) (by omega_arith)
  have hpow : 2 ^ (128 * w) = 2 ^ (64 * w) * 2 ^ (64 * w) := by
    rw [← Nat.pow_add]; congr 1; omega_arith
  refine ⟨⟨hg.scr.congr k₂.2.2, (k₂.gpr (by decide)).trans hg.rdi, ?_⟩, by rw [hvR]; exact Nat.mod_lt _ hN,
    by rw [hvR, Nat.mod_mod, hpow], ?_, k₂.mono (by decide)⟩
  · exact hA₂.hdr hg.hdr
  · exact Frm.of_arrays hA₂ (by intro j hj; simp only [List.mem_singleton] at hj; subst hj; simp [r2Ranges])

/-! ## Constant time -/

/-- The public data of `r2Pre`: the stack pointer, the working space, `w`
and `pre`'s address. -/
structure R2PPub where
  sp : Addr
  B : Addr
  w : Nat
  A : Addr

/-- Before `r2Pre`. -/
def R2PreCT (p : R2PPub) (s : State) : Prop :=
  s.gpr .rsp = p.sp ∧ s.gpr .rdi = p.B ∧ s.gpr .r12 = BitVec.ofNat 64 p.w ∧
    WP isa (.block r2PreBlk) s fun t => t.gpr .rsi = off p.A (8 * p.w) ∧ t.gpr .rbx = off p.B (slot p.w aR2) ∧
      t.gpr .r12 = BitVec.ofNat 64 p.w

/-- `r2Pre` leaks the same in runs that agree on its public data. -/
theorem r2Pre_ct : RelCT isa (Two R2PreCT) r2Pre fun _ _ => True := by
  rw [r2Pre_eq]
  refine RelCT.seq (two_piece (Ψ := fun (p : R2PPub) t => t.gpr .rsi = off p.A (8 * p.w) ∧
      t.gpr .rbx = off p.B (slot p.w aR2) ∧ t.gpr .r12 = BitVec.ofNat 64 p.w) [.rsp, .rdi, .r12]
    (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2.1, h₂.2.2.1]) (by taint_decide) fun _ _ h => h.2.2.2) ?_
  exact two_taint [.rsi, .rbx, .r12] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.1, h₂.1]
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2, h₂.2.2]) (by taint_decide)

/-- `R2PreCT` from `r2Pre_ok`'s hypotheses. -/
theorem r2PreCT_of {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N : Nat}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (hp : PreR2 s B Z w N) :
    R2PreCT ⟨s.gpr .rsp, B, w, stackArg s 12⟩ s :=
  ⟨rfl, hg.rdi, h12, WP.mono (r2PreBlk_ok hg hZ h12 hp) fun t ⟨hsi, hbx, _, k⟩ =>
    ⟨hsi, hbx, (k.gpr (by decide)).trans h12⟩⟩

end VG.Proof.Bignum.X86_64

end

end

/-! ### `Bignum.X86_64.Ifma.R2X`, which this module and modules that import it used -/

section

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
  obtain hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off B o) (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot wx 8 hi; omega_arith)
  have e104 : off (s.gpr .rsp) (8 * 13) = stackArgAddr s 12 := rfl
  have hA : s.mem.readW (stackArgAddr s 12) 64 = stackArg s 12 := rfl
  obtain hoff : ∀ d : Nat, stackArg s 12 + BitVec.ofNat 64 d = off (stackArg s 12) d := fun _ => rfl
  refine WP.mono (WP.keep (c := .block (r2XBlk q j)) [.rax, .rsi, .rbx, .r12] (Q := fun t =>
      t.gpr .rsi = off (stackArg s 12) (8 * r2XOff q wx) ∧ t.gpr .rbx = off (off B o) (slot wx j) ∧
      t.gpr .r12 = BitVec.ofNat 64 wx ∧ t.mem = s.mem) ?_ (by cases q <;> rfl))
    fun t ⟨⟨h1, h2, h3, h4⟩, k⟩ => ⟨h1, h2, h3, h4, k⟩
  cases q
  · unfold r2XBlk Crt.preArg Crt.stk
    simp only [List.cons_append, List.nil_append, Bool.false_eq_true, ↓reduceIte, List.append_nil]
    xrun [State.ea, hdr, hg.rdi, hdrOff, e104, hp.arg, hA, hl sW (by decide), hg.hdr.hw, hl (sArr j) (by unfold sArr; omega_using [hj]),
      hg.hdr.harr j hj, BitVec.ofNat_add_ofNat]
    rw [hoff]; congr 1; simp only [r2XOff, Bool.false_eq_true, ↓reduceIte]; omega_using []
  · unfold r2XBlk Crt.preArg Crt.stk
    simp only [List.cons_append, List.nil_append, ↓reduceIte]
    xrun [State.ea, hdr, hg.rdi, hdrOff, e104, hp.arg, hA, hl sW (by decide), hg.hdr.hw, hl (sArr j) (by unfold sArr; omega_using [hj]),
      hg.hdr.harr j hj, BitVec.ofNat_add_ofNat]
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, hoff]; congr 1; simp only [r2XOff, ↓reduceIte]; omega_using []

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
  obtain sJ := slot_le (w := wx) hj
  obtain hJ0 := hdr_lt_slot wx j (show 31 < 32 by decide)
  obtain h256 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_arith
  unfold r2X maskN
  simp only [List.cons_append, List.nil_append, seqs]
  -- `rsi`, `r12`, `rbx`.
  refine WP.seq (WP.mono (r2XBlk_ok hj hc hp) fun t₁ ⟨hsi, hbx, h12, hm₁, k₁⟩ => ?_)
  obtain hs₁ : Scr t₁ (off B o) (slot wx 8) := hg.scr.congr k₁.2.2
  -- The copy from `pre`.
  obtain hout : ∀ i < wx, ∀ b < 8, slot wx 8 ≤
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
  obtain k₁₂ := k₁.trans k₂
  obtain f₂ : Frm (off B o) [(slot wx j, 8 * wx)] s.mem t₂.mem := Frm.of_outside ho₂ (by simp)
  obtain hc₂ : SubCtx t₂ B Z o w wx minv := hc.of_frm f₂ (fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only; omega_arith) k₁₂.2.2 (k₁₂.gpr (by decide))
  obtain hM₂ : word t₂.mem B (8 * sMask) = mask c := by
    rw [f₂.word_below (L := slot wx 8) (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega_arith)
      (by omega_arith) (by omega_arith) (by have := hdr_lt_slot w 8 (show sMask < 32 by decide); omega_arith)]; exact hm
  -- The mask.
  have g₂ := hc₂.good
  obtain hl : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (off (off B o) (8 * i)) 8 := fun i hi' =>
    g₂.scr.ld (by have := hdr_lt_slot wx 8 hi'; omega_arith)
  obtain hln : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (off B (8 * i)) 8 := fun i hi' =>
    hc₂.scr.ld (by have := hdr_lt_slot w 8 hi'; omega_arith)
  refine WP.seq (WP.mono (WP.keep [.rax, .r15, .r12, .rbx] (Q := fun t => t.gpr .r15 = mask c ∧
      t.gpr .r12 = BitVec.ofNat 64 wx ∧ t.gpr .rbx = off (off B o) (slot wx j) ∧ t.mem = t₂.mem)
    (by xrun [State.ea, hdr, Crt.ws, hc₂.rdi, hdrOff, hl Crt.sLink (by decide), hc₂.link, hln sMask (by decide), hM₂,
      hl (sArr j) (by unfold sArr; omega_arith), hl sW (by decide), g₂.hdr.harr j hj, g₂.hdr.hw]) rfl)
    fun t₃ ⟨⟨h15, h12', hbx', hm₃⟩, k₃⟩ => ?_)
  obtain hs₃ := g₂.scr.congr k₃.2.2
  obtain h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = t₃.mem → Keep [.r14] t₃ t → t.cf = t₃.cf →
      MaskInv t₃ (off B o) (slot wx 8) (slot wx j) c 0 t := fun t h14 hm' k _ =>
    ⟨hs₃.congr k.2.2, k.mono (by decide), h14, by rw [hm']; exact Outside.refl _ _ _ _,
      fun i hi' => absurd hi' (Nat.not_lt_zero _)⟩
  refine WP.seq (WP.mono (wordLoop_ok (start := 0) (N := wx) (by omega_arith) (by omega_arith)
    (MaskInv t₃ (off B o) (slot wx 8) (slot wx j) c) h0
    (fun i _ hi' t hI => maskStep_ok hbx' h15 h12' (by omega_arith) (by omega_arith) hi' hI)) fun t₄ hI => ?_)
  -- `1` where the mask is clear.
  have k₄ := hI.keep
  obtain hbx₄ : t₄.gpr .rbx = off (off B o) (slot wx j) := (k₄.gpr (by decide)).trans hbx'
  obtain h15₄ : t₄.gpr .r15 = mask c := (k₄.gpr (by decide)).trans h15
  obtain hx₄ : word t₄.mem (off B o) (slot wx j) = word t₂.mem (off B o) (slot wx j) &&& mask c := by
    have := hI.done 0 (by omega_arith); rw [Nat.mul_zero, Nat.add_zero, hm₃] at this; exact this
  refine WP.mono (orOne_ok hI.scr hbx₄ h15₄ (by omega_arith) hx₄) fun t ⟨hm₅, k₅⟩ => ?_
  have o₄ := hI.out
  rw [hm₃] at o₄
  obtain o₅ := writeW_outside t₄.mem (off B o) (d := slot wx j) (if c then word t₂.mem (off B o) (slot wx j) else 1)
    (by omega_arith)
  rw [← hm₅] at o₅
  obtain f₂t : Frm (off B o) [(slot wx j, 8 * wx)] t₂.mem t.mem :=
    (Frm.of_outside o₄ (by simp)).trans (Frm.of_outside (o₅.mono (o' := slot wx j) (n' := 8 * wx) (Nat.le_refl _)
      (by omega_arith)) (by simp))
  obtain K := ((k₁₂.trans k₃).trans k₄).trans k₅
  obtain hup : ∀ i < wx, i ≠ 0 → word t.mem (off B o) (slot wx j + 8 * i) =
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

end

end

/-!
# RSA with AVX512_IFMA on x86-64: the bases in the primes' workspaces

`pre` computes `G` once in `n`'s workspace and, for each prime `X`, enters
its workspace and reduces (`enterRedc_ok`): `R_X` into `aY` (from `G`)
and `x R_X` into `aXc` (from `x G`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- Back to `n`'s workspace, whose header the prime's phase kept. -/
theorem leaveBack_ok {s₀ t : State} {B : Addr} {Z w : Nat} {minv mx : BitVec 64} {o wx : Nat}
    (hg : Good s₀ B Z w minv) (hc : SubCtx t B Z o w wx mx) (hf : Frm B [xRange o wx] s₀.mem t.mem)
    (hlo : slot w 8 ≤ o) :
    WP isa (.block [leave]) t fun t' => Good t' B Z w minv ∧ t'.mem = t.mem ∧ Keep [.rdi] t t' := by
  have hn := hc.scr.nowrap
  have hhi := hc.hi
  obtain h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  obtain hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_using []
  obtain ho64 : o < 2 ^ 64 := by omega_using [hn, hhi, hX8]
  obtain hl : InRegions (t.rd ++ t.wr) (off (off B o) (8 * sLink)) 8 :=
    hc.good.scr.ld (by unfold sLink sFn; omega_using [hX8])
  refine WP.mono (WP.keep [.rdi] (Q := fun t' => t'.gpr .rdi = B ∧ t'.mem = t.mem)
    (by xrun [leave, State.ea, hdr, hc.rdi, hdrOff, hl, hc.link]) rfl) fun t' ⟨⟨hdi, hm⟩, k⟩ => ?_
  obtain hb : ∀ d, d + 8 ≤ o → word t'.mem B d = word s₀.mem B d := fun d hd => by
    rw [hm]; exact hf.x_below hd ho64
  have hH := hg.hdr
  exact ⟨⟨hc.scr.congr k.2.2, hdi, (hb _ (by unfold sW; omega_using [hlo, h8])).trans hH.hw,
    (hb _ (by unfold sMinv; omega_using [hlo, h8])).trans hH.hminv,
    fun j hj => (hb _ (by have := hdr_lt_slot w 8 (show sArr j < 32 by unfold sArr; omega_using [hj]); omega_using [hlo, this])).trans
      (hH.harr j hj)⟩, hm, k⟩

/-- `K = 2` chunks of the prime's words in `n`'s. -/
theorem nChunks_two {w wx : Nat} (hw2 : w = 2 * wx) (hwx : 1 ≤ wx) : nChunks w wx = 2 := by
  show (w + wx - 1) / wx = 2
  exact Nat.div_eq_of_lt_le (by omega_using [hw2]) (by omega_using [hw2, hwx])

/-- What `prep` leaves: `R_X` in the prime's `aY`, `x R_X` in its `aXc`;
only the prime's workspace changes. -/
abbrev PrepPost (s : State) (B : Addr) (Z w : Nat) (minv mx : BitVec 64) (N X C o wx : Nat) (t : State) : Prop :=
  Good t B Z w minv ∧ WsAt t.mem B o wx mx ∧
    XVals t B o wx mx X ∧ wv t.mem (off B o) (slot wx Public.aY) wx < X ∧
    (X ∣ N → wv t.mem (off B o) (slot wx Public.aY) wx % X = 2 ^ (64 * wx) % X) ∧
    wv t.mem (off B o) (slot wx aXc) wx < X ∧
    (X ∣ N → wv t.mem (off B o) (slot wx aXc) wx % X = C * 2 ^ (64 * wx) % X) ∧
    Frm B [xRange o wx] s.mem t.mem ∧ Keep mmRegs s t ∧
    word t.mem (off B o) (8 * sMaskX) = word s.mem (off B o) (8 * sMaskX)

/-- `prep` after its start, from `s₂` in the prime's workspace (entered from
`s`, in `n`'s), whose `aY` holds `R_X²` modulo `X` (when `X ∣ N`): `x R_X`
into `aXc` (from `n`'s `x R_n mod n`), `R_X` into `aY`, and back to `n`'s
workspace. -/
theorem prepTail_ok (M : Mont) {s s₂ : State} {B : Addr} {Z w : Nat} {minv mx : BitVec 64} {N X C : Nat}
    {o wx : Nat} (hg : Good s B Z w minv) (hw28 : w < 2 ^ 28) (hlo : slot w 8 ≤ o)
    (hhi : o + slot wx 8 + wsTab wx ≤ Z) (hwx2 : 2 ≤ wx) (hw2 : w = 2 * wx)
    (hXm : wv s.mem B (slot w Public.aXm) w % N = C * 2 ^ (64 * w) % N) (hX1 : 1 < X) (hXodd : X % 2 = 1)
    (hc₂ : SubCtx s₂ B Z o w wx mx) (hX₂ : XVals s₂ B o wx mx X) (f02 : Frm B [xRange o wx] s.mem s₂.mem)
    (k02 : Keep (mmRegs ++ ([.rdi] : List Reg)) s s₂)
    (hY : X ∣ N → wv s₂.mem (off B o) (slot wx Public.aY) wx % X = 2 ^ (64 * wx * 2) % X)
    (hmk : word s₂.mem (off B o) (8 * sMaskX) = word s.mem (off B o) (8 * sMaskX)) :
    WP isa (seqs (redc M.mm Public.aXm ++ (([M.mm aT Public.aY aXc] : List (Prog isa)) ++
      (copyArr aXc aT ++ [M.mm Public.aY Public.aY Public.aOne, .block [leave]])))) s₂
      (PrepPost s B Z w minv mx N X C o wx) := by
  have hs := hg.scr
  have hn := hs.nowrap
  obtain h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  obtain hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_using []
  obtain ho64 : o < 2 ^ 64 := by omega_using [hhi, hn, hX8]
  obtain hoL : o + slot wx 8 ≤ 2 ^ 64 := by omega_using [hhi, hn]
  obtain hwx : wx ≤ w := by omega_using [hw2]
  obtain hK := nChunks_two hw2 (by omega_using [hwx2])
  obtain hRx : Nat.Coprime (2 ^ (64 * wx)) X := VG.Proof.Bignum.coprime_pow2 hXodd _
  obtain hRR : Nat.Coprime (2 ^ (64 * wx * 2)) X := VG.Proof.Bignum.coprime_pow2 hXodd _
  obtain e2 : 2 ^ (64 * w) = 2 ^ (64 * wx * 2) := by rw [hw2]; congr 1; omega_using []
  obtain lY := slot_le (w := wx) (show Public.aY < 8 by decide)
  obtain hrm : ∀ r ∈ redcRanges wx, 8 * sMaskX + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * sMaskX := fun r hr => by
    simp only [redcRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [sMaskX, sSrc, sRem, sFn, slot, hdrBytes] <;>
      omega_using []
  obtain rY := redcRanges_arr wx (j := Public.aY) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  -- `aXc := x R_n R_X^-2 = x`.
  refine wp_seqs_append (by simp [redc]) (by simp) (WP.mono (redc_ok M hc₂ hX₂ hwx2 hwx (by omega_using [hw28]) hX1
    (j := Public.aXm) (by decide)) fun s₃ ⟨hc₃, hX₃, hlt₃, hv₃, r₃, k₃⟩ => ?_)
  rw [show (w + wx - 1) / wx = 2 from hK] at hv₃
  obtain fx₃ : Frm B [xRange o wx] s₂.mem s₃.mem := r₃.to_x (redcRanges_ok wx) hoL (List.mem_singleton_self _)
  obtain hXm₂ : wv s₂.mem B (slot w Public.aXm) w = wv s.mem B (slot w Public.aXm) w :=
    wv_congr fun i hi => f02.x_below (by have := slot_le (w := w) (show Public.aXm < 8 by decide); omega_using [hlo, hi, this]) ho64
  obtain hY₃ : wv s₃.mem (off B o) (slot wx Public.aY) wx = wv s₂.mem (off B o) (slot wx Public.aY) wx :=
    r₃.wv_eq (fun r hr => by have := rY r hr; omega_using [this]) (by omega_using [hoL, lY])
  -- `aT := x R_X`.
  refine wp_seqs_append (by simp) (by simp [copyArr]) (WP.mono (M.mm_ok (o := aT) (a := Public.aY) (b := aXc)
    hc₃.good (Nat.le_refl _) hwx2 (by omega_using [hw28, hwx]) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hX₃.inv (by rw [hX₃.n]; exact hlt₃)) fun s₄ ⟨_, hT₄, hm₄, ha₄, k₄⟩ => ?_)
  rw [hX₃.n] at hT₄ hm₄
  obtain ⟨hc₄, hX₄, fx₄⟩ := hc₃.of_arrays hX₃ ha₄ (by
    intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> decide) k₄.2.2 (k₄.gpr (by decide)) (by omega_using [hwx2])
  obtain hz₄ : (off B o).toNat + slot wx 8 ≤ 2 ^ 64 := by have := hc₄.good.scr.nowrap; omega_using [this]
  obtain hY₄ : wv s₄.mem (off B o) (slot wx Public.aY) wx = wv s₃.mem (off B o) (slot wx Public.aY) wx :=
    ha₄.wv_of_not_mem (by decide) (by decide) hz₄
  -- `aXc := aT`.
  refine wp_seqs_append (by simp [copyArr]) (by simp) (WP.mono (copyArr_ok hc₄.good (Nat.le_refl _)
    (by omega_using [hwx2]) (by omega_using [hw28, hwx]) (o := aXc) (a := aT) (by decide) (by decide) (by decide))
    fun s₅ ⟨hv₅, ho₅, k₅⟩ => ?_)
  obtain lC := slot_le (w := wx) (show aXc < 8 by decide)
  obtain hC0 := hdr_lt_slot wx aXc (show 31 < 32 by decide)
  obtain hc₅ := hc₄.of_frm (rs := [(slot wx aXc, 8 * wx)]) (Frm.of_outside ho₅ (by simp)) (fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only; omega_using [lC, hC0]) k₅.2.2 (k₅.gpr (by decide))
  obtain hX₅ : XVals s₅ B o wx mx X := hX₄.of_outside ho₅ (by decide) (by decide) (by decide) (by omega_using []) hz₄
  obtain fx₅ : Frm B [xRange o wx] s₄.mem s₅.mem :=
    (ho₅.mono (o' := slot wx aXc) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega_using [])).to_x
      (by decide) hoL (List.mem_singleton_self _)
  obtain hY₅ : wv s₅.mem (off B o) (slot wx Public.aY) wx = wv s₄.mem (off B o) (slot wx Public.aY) wx := by
    have := slot_sep (w := wx) (show Public.aY ≠ aXc by decide)
    exact ho₅.wv (by omega_using [this]) (by omega_using [lY, hz₄])
  -- `aY := R_X² R_X^-1 = R_X`.
  refine WP.seq (WP.mono (M.mm_ok (o := Public.aY) (a := Public.aY) (b := Public.aOne) hc₅.good (Nat.le_refl _)
    hwx2 (by omega_using [hw28, hwx]) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hX₅.inv
    (by rw [hX₅.n, hX₅.one]; exact hX1)) fun s₆ ⟨_, hlt₆, hm₆, ha₆, k₆⟩ => ?_)
  rw [hX₅.n, hX₅.one, Nat.mul_one] at hm₆
  rw [hX₅.n] at hlt₆
  obtain ⟨hc₆, hX₆, fx₆⟩ := hc₅.of_arrays hX₅ ha₆ (by
    intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> decide) k₆.2.2 (k₆.gpr (by decide)) (by omega_using [hwx2])
  obtain hC₆ : wv s₆.mem (off B o) (slot wx aXc) wx = wv s₄.mem (off B o) (slot wx aT) wx := by
    rw [ha₆.wv_of_not_mem (by decide) (by decide) hz₄, hv₅]
  obtain fall := ((((f02.trans fx₃).trans fx₄).trans fx₅).trans fx₆)
  refine WP.mono (leaveBack_ok hg hc₆ fall hlo) fun t ⟨hg', hm', k'⟩ => ?_
  obtain kall := ((((k02.trans k₃).trans k₄).trans k₅).trans k₆).trans k'
  refine ⟨hg', by rw [hm']; exact hc₆.ws, ?_, by rw [hm']; exact hlt₆, fun hd => ?_,
    by rw [hm', hC₆]; exact hT₄, fun hd => ?_, by rw [hm']; exact fall, ⟨fun r hr => ?_, kall.2⟩, ?_⟩
  · rw [show t = { t with mem := s₆.mem } by rw [← hm']]; exact ⟨hX₆.n, hX₆.inv, hX₆.one⟩
  · -- `aY₂ ≡ R_X²`, so `aY R_X ≡ R_X²`.
    apply VG.Proof.Bignum.mont_cancel hRx
    rw [hm', hm₆, hY₅, hY₄, hY₃, hY hd, ← Nat.pow_add]
    congr 2; omega_using []
  · -- `aXc₃ = x`, so `aT₄ R_X ≡ R_X² x`.
    obtain h3 : wv s₃.mem (off B o) (slot wx aXc) wx % X = C % X :=
      VG.Proof.Bignum.mont_cancel hRR (by
        rw [hv₃, hXm₂, ← Nat.mod_mod_of_dvd _ hd, hXm, Nat.mod_mod_of_dvd _ hd, e2])
    apply VG.Proof.Bignum.mont_cancel hRx
    rw [hm', hC₆, hm₄, hY₃, Nat.mul_mod, h3, hY hd, ← Nat.mul_mod, Nat.mul_comm, Nat.mul_assoc C, ← Nat.pow_add]
    congr 3; omega_using []
  · by_cases h : r = .rdi
    · subst h; rw [hg'.rdi, hg.rdi]
    · exact kall.1 r (by revert hr h; cases r <;> decide)
  · have hmx : 8 * sMaskX + 8 ≤ 8 * 31 + 8 := by unfold sMaskX sFn; omega_using []
    rw [hm', ha₆.hslot (by decide), ho₅.word (.inl (by omega_using [hC0, hmx])) (by omega_using [hmx]), ha₄.hslot (by decide),
      r₃.word_eq hrm (by omega_using [hmx]), hmk]

/-- Into a prime's workspace (`rdi := [sl]`). -/
theorem enter_ok {s : State} {B : Addr} {Z w : Nat} {minv mx : BitVec 64} {X sl o wx : Nat}
    (hg : Good s B Z w minv) (hlo : slot w 8 ≤ o) (hhi : o + slot wx 8 + wsTab wx ≤ Z) (hsl : sl < 32)
    (hslv : word s.mem B (8 * sl) = off B o) (hws : WsAt s.mem B o wx mx) (hX : XVals s B o wx mx X) :
    WP isa (.block [.mov .rdi (.mem (hdr sl))]) s fun s₁ =>
      SubCtx s₁ B Z o w wx mx ∧ XVals s₁ B o wx mx X ∧ s₁.mem = s.mem ∧ Keep [.rdi] s s₁ := by
  have hs := hg.scr
  obtain hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_using []
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = off B o ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hs.ld (d := 8 * sl) (by omega_using [hhi, hsl, hX8]), hslv]) rfl)
    fun s₁ ⟨⟨hdi₁, hm₁⟩, k₁⟩ => ⟨SubCtx.mk' (hs.congr k₁.2.2) (by rw [hm₁]; exact hg.hdr) (by rw [hm₁]; exact hws)
      hdi₁ hlo (by have := tabBytes_le_wsTab wx; omega_using [hhi, this]),
      by rw [show s₁ = { s₁ with mem := s.mem } by rw [← hm₁]]; exact ⟨hX.n, hX.inv, hX.one⟩, hm₁, k₁⟩

theorem two_pow_mod_three (k : Nat) : 2 ^ (64 * k * 2) % 3 = 1 := by
  rw [show 64 * k * 2 = 2 * (64 * k) by omega_using [], Nat.pow_mul, Nat.pow_mod]
  simp

/-- `prepP q`: `prep` with `R_X² mod X` from `pre`'s words from `r2XOff q`
(whose value `V` is it where `n`'s mask `c` is set; where it is clear the
prime is 3). -/
theorem prepP_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv mx : BitVec 64} {N X C V : Nat} {c q : Bool}
    {sl o wx : Nat} (hg : Good s B Z w minv) (hw28 : w < 2 ^ 28) (hlo : slot w 8 ≤ o)
    (hhi : o + slot wx 8 + wsTab wx ≤ Z) (hwx2 : 2 ≤ wx) (hw2 : w = 2 * wx) (hsl : sl < 32)
    (hslv : word s.mem B (8 * sl) = off B o) (hws : WsAt s.mem B o wx mx)
    (hXm : wv s.mem B (slot w Public.aXm) w % N = C * 2 ^ (64 * w) % N)
    (hX : XVals s B o wx mx X) (hX1 : 1 < X) (hXodd : X % 2 = 1)
    (hM : word s.mem B (8 * Public.sMask) = mask c) (hp : PreW s B Z (r2XOff q wx) wx V)
    (hc3 : c = false → X = 3) (hV : c = true → V % X = 2 ^ (64 * wx * 2) % X) :
    WP isa (seqs (CrtIfma.prepP M.mm sl q)) s (PrepPost s B Z w minv mx N X C o wx) := by
  have hs := hg.scr
  have hn := hs.nowrap
  obtain hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_using []
  obtain hoL : o + slot wx 8 ≤ 2 ^ 64 := by omega_using [hhi, hn]
  obtain hwx : wx ≤ w := by omega_using [hw2]
  obtain lY := slot_le (w := wx) (show Public.aY < 8 by decide)
  obtain hY0 := hdr_lt_slot wx Public.aY (show 31 < 32 by decide)
  obtain hmx : 8 * sMaskX + 8 ≤ 8 * 31 + 8 := by unfold sMaskX sFn; omega_using []
  rw [show CrtIfma.prepP M.mm sl q = ([.block [.mov .rdi (.mem (hdr sl))]] : List (Prog isa)) ++ (CrtIfma.r2X q Public.aY ++
      (redc M.mm Public.aXm ++ (([M.mm aT Public.aY aXc] : List (Prog isa)) ++
        (copyArr aXc aT ++ [M.mm Public.aY Public.aY Public.aOne, .block [leave]])))) by
    simp only [CrtIfma.prepP, List.append_assoc]]
  -- Into the prime's workspace.
  refine wp_seqs_append (by simp) (by simp [CrtIfma.r2X, CrtIfma.r2XBlk]) (WP.mono (enter_ok hg hlo hhi hsl hslv hws hX)
    fun s₁ ⟨hc₁, hX₁, hm₁, k₁⟩ => ?_)
  obtain hp₁ : PreW s₁ B Z (r2XOff q wx) wx V :=
    hp.congr (fun x _ => by rw [hm₁]) (k₁.gpr (by decide)) k₁.2.1 k₁.2.2
  -- `aY := c ? V : 1`.
  refine wp_seqs_append (by simp [CrtIfma.r2X, CrtIfma.r2XBlk]) (by simp [redc]) (WP.mono (r2X_ok (j := Public.aY) (c := c) (by decide) hc₁
    hwx2 hwx (by omega_using [hw28]) (by rw [hm₁]; exact hM) hp₁) fun s₂ ⟨hc₂, hv₂, f₂, k₂⟩ => ?_)
  obtain ho₂ : Outside (off B o) (slot wx Public.aY) (8 * (wx + 2)) s₁.mem s₂.mem := fun x hx =>
    f₂ x fun r hr => by rw [List.mem_singleton.mp hr]; exact hx
  rw [hm₁] at f₂ ho₂
  refine prepTail_ok M hg hw28 hlo hhi hwx2 hw2 hXm hX1 hXodd hc₂
    (hX₁.of_outside (by rw [hm₁]; exact ho₂) (by decide) (by decide) (by decide) (Nat.le_refl _)
      (by have := hc₁.good.scr.nowrap; omega_using [this]))
    (f₂.to_x (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega_using [lY, hY0]) hoL
      (List.mem_singleton_self _))
    ((k₁.trans k₂).mono (by decide)) (fun _ => ?_)
    (f₂.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega_using [hY0, hmx])
      (by have := hc₁.good.scr.nowrap; omega_using [this, hmx]))
  rw [hv₂]
  cases c
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hc3 rfl, two_pow_mod_three]
  · simp only [↓reduceIte]
    exact hV rfl

theorem Good.of_outsideArr {s t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {j n : Nat}
    (h : Good s B Z w minv) (ho : Outside B (slot w j) n s.mem t.mem) (hk : Keep mmRegs s t) :
    Good t B Z w minv := by
  have hn := h.scr.nowrap
  obtain hh : ∀ i < 32, word t.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    ho.word (Or.inl (by have := hdr_lt_slot w j hi; omega_using [this])) (by have := hdr_lt_slot w j hi; omega_using [hi])
  exact ⟨h.scr.congr hk.2.2, (hk.gpr (by decide)).trans h.rdi, (hh _ (by decide)).trans h.hdr.hw,
    (hh _ (by decide)).trans h.hdr.hminv, fun j hj => (hh _ (by unfold sArr; omega_using [hj])).trans (h.hdr.harr j hj)⟩

/-- `n`'s header and the arrays but `aAcc`, `aTmp`, `aY` and `aX`, and both primes' workspaces: what
`pre` may change (it changes only the primes' workspaces). -/
def preRanges (w op wp oq wq : Nat) : List (Nat × Nat) :=
  gRanges w ++ [(slot w Public.aX, 8 * (w + 2)), xRange oq wq, xRange op wp]

/-- A prime's values after a change on either side of its workspace. -/
theorem XVals.of_disj {s t : State} {B : Addr} {o wx : Nat} {mx : BitVec 64} {X : Nat}
    {rs : List (Nat × Nat)} (h : XVals s B o wx mx X) (hf : Frm B rs s.mem t.mem)
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ o ∨ o + slot wx 8 ≤ r.1) (ho : o + slot wx 8 ≤ 2 ^ 64) : XVals t B o wx mx X := by
  obtain hN := slot_le (w := wx) (show Public.aN < 8 by decide)
  obtain hO := slot_le (w := wx) (show Public.aOne < 8 by decide)
  obtain hd : ∀ d n, d + n ≤ slot wx 8 → ∀ r ∈ rs, o + d + n ≤ r.1 ∨ r.1 + r.2 ≤ o + d := fun d n hd r h' => by
    rcases hr r h' with h | h <;> omega_using [h, hd]
  exact ⟨by rw [wv_off, hf.wv_eq (hd _ _ (by omega_using [hN])) (by omega_arith), ← wv_off]; exact h.n,
    by rw [word_off, hf.word_eq (fun r h' => by have := hd (slot wx Public.aN) 8 (by omega_using [hN]) r h'; omega_using [this])
      (by omega_using [ho, hN]), ← word_off]; exact h.inv,
    by rw [wv_off, hf.wv_eq (hd _ _ (by omega_using [hO])) (by omega_using [ho, hO]), ← wv_off]; exact h.one⟩

theorem _root_.VG.Proof.Bignum.WsAt.of_disj {m m' : Mem} {B : Addr} {o wx : Nat} {mx : BitVec 64} {rs : List (Nat × Nat)}
    (h : WsAt m B o wx mx) (hf : Frm B rs m m') (hr : ∀ r ∈ rs, r.1 + r.2 ≤ o ∨ o + 8 * 17 ≤ r.1)
    (ho : o + 8 * 17 ≤ 2 ^ 64) : WsAt m' B o wx mx :=
  h.of_words fun i hi => by
    rw [word_off, word_off]
    exact hf.word_eq (fun r h' => by rcases hr r h' with h | h <;> omega_using [h, hi]) (by omega_using [ho, hi])

theorem wvX_disj {m m' : Mem} {B : Addr} {o wx j : Nat} {rs : List (Nat × Nat)} (hf : Frm B rs m m')
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ o ∨ o + slot wx 8 ≤ r.1) (ho : o + slot wx 8 ≤ 2 ^ 64) (hj : j < 8) :
    wv m' (off B o) (slot wx j) wx = wv m (off B o) (slot wx j) wx := by
  have := slot_le (w := wx) hj
  rw [wv_off, wv_off]
  exact hf.wv_eq (fun r h' => by rcases hr r h' with h | h <;> omega_using [h, this]) (by omega_using [ho, this])

theorem gRanges_lt (w : Nat) : ∀ r ∈ gRanges w, 8 * 22 ≤ r.1 ∧ r.1 + r.2 ≤ slot w 8 := by
  have := slot_le (w := w) (show Public.aAcc < 8 by decide)
  have := slot_le (w := w) (show Public.aTmp < 8 by decide)
  have := slot_le (w := w) (show Public.aY < 8 by decide)
  have := hdr_lt_slot w Public.aAcc (show 31 < 32 by decide)
  have := hdr_lt_slot w Public.aTmp (show 31 < 32 by decide)
  have := hdr_lt_slot w Public.aY (show 31 < 32 by decide)
  simp only [gRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl) <;> simp only [Crt.sD, Public.sCnt, sFn] <;> omega_arith

/-- A prime's part of `pre`'s result: `R_X` in its `aY`, `x R_X` in its `aXc`. -/
structure PrimeRdy (t : State) (B : Addr) (o wx : Nat) (mx : BitVec 64) (N X C : Nat) : Prop where
  ws : WsAt t.mem B o wx mx
  x : XVals t B o wx mx X
  ylt : wv t.mem (off B o) (slot wx Public.aY) wx < X
  yv : X ∣ N → wv t.mem (off B o) (slot wx Public.aY) wx % X = 2 ^ (64 * wx) % X
  clt : wv t.mem (off B o) (slot wx aXc) wx < X
  cv : X ∣ N → wv t.mem (off B o) (slot wx aXc) wx % X = C * 2 ^ (64 * wx) % X

theorem PrimeRdy.of_disj {s t : State} {B : Addr} {o wx : Nat} {mx : BitVec 64} {N X C : Nat}
    {rs : List (Nat × Nat)} (h : PrimeRdy s B o wx mx N X C) (hf : Frm B rs s.mem t.mem)
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ o ∨ o + slot wx 8 ≤ r.1) (ho : o + slot wx 8 ≤ 2 ^ 64) :
    PrimeRdy t B o wx mx N X C := by
  obtain h17 : 8 * 17 ≤ slot wx 8 := by unfold slot hdrBytes; omega_using []
  refine ⟨h.ws.of_disj hf (fun r hr' => by rcases hr r hr' with h | h <;> omega_using [h, h17]) (by omega_using [ho, h17]),
    h.x.of_disj hf hr ho, ?_, fun hd => ?_, ?_, fun hd => ?_⟩
  · rw [wvX_disj hf hr ho (by decide)]; exact h.ylt
  · rw [wvX_disj hf hr ho (by decide)]; exact h.yv hd
  · rw [wvX_disj hf hr ho (by decide)]; exact h.clt
  · rw [wvX_disj hf hr ho (by decide)]; exact h.cv hd

/-- What `pre` leaves: both primes ready; only their workspaces change. -/
abbrev PrePost (s : State) (B : Addr) (Z w : Nat) (minv mp mq : BitVec 64) (N P Q C op wp oq : Nat) (t : State) : Prop :=
  Good t B Z w minv ∧ NVals t B w minv N ∧
    PrimeRdy t B op wp mp N P C ∧ PrimeRdy t B oq wp mq N Q C ∧
    Frm B (preRanges w op wp oq wp) s.mem t.mem ∧ Keep mmRegs s t ∧
    word t.mem (off B op) (8 * sMaskX) = word s.mem (off B op) (8 * sMaskX)

/-- `q`'s part `cq` then `p`'s `cp`, each `prep`'s: both primes ready. `cp`
runs from any state that `cq` leaves (`hcp`). -/
theorem preWith_ok {cq cp : List (Prog isa)} (hcq0 : cq ≠ []) (hcp0 : cp ≠ []) {s : State} {B : Addr} {Z w : Nat}
    {minv mp mq : BitVec 64} {N P Q C op wp oq : Nat}
    (hg : Good s B Z w minv) (hlo : slot w 8 ≤ op)
    (hpq : op + slot wp 8 + wsTab wp ≤ oq) (hoq : oq + slot wp 8 + wsTab wp ≤ Z) (hwp2 : 2 ≤ wp)
    (hw2 : w = 2 * wp) (hN : NVals s B w minv N)
    (hcq : WP isa (seqs cq) s (PrepPost s B Z w minv mq N Q C oq wp))
    (hcp : ∀ s₁, Good s₁ B Z w minv → Frm B [xRange oq wp] s.mem s₁.mem → Keep mmRegs s s₁ →
      NVals s₁ B w minv N → WP isa (seqs cp) s₁ (PrepPost s₁ B Z w minv mp N P C op wp)) :
    WP isa (seqs (cq ++ cp)) s (PrePost s B Z w minv mp mq N P Q C op wp oq) := by
  have hs := hg.scr
  have hn := hs.nowrap
  obtain h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  obtain hX8 : 256 ≤ slot wp 8 := by unfold slot hdrBytes; omega_using []
  obtain hz : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega_using [hlo, hpq, hoq, hn]
  obtain hmk : 8 * sMaskX + 8 ≤ slot wp 8 := by unfold sMaskX sFn; omega_using [hX8]
  -- `q`.
  refine wp_seqs_append hcq0 hcp0 (WP.mono hcq fun s₁ ⟨hg₁, hwsq₁, hQ₁, hqy, hqyv, hqx, hqxv, fQ, kQ, _⟩ => ?_)
  obtain ho64 : oq < 2 ^ 64 := by omega_using [hoq, hn, hmk]
  obtain hQd : ∀ r ∈ [xRange oq wp], r.1 + r.2 ≤ op ∨ op + slot wp 8 ≤ r.1 := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact .inr (by simp only [xRange]; omega_using [hpq])
  obtain hN₁ : NVals s₁ B w minv N := hN.of_frm (fQ.mono fun r hr => List.mem_append_right _ hr) (by omega_using [hlo, hpq]) hz
    (by omega_using [hwp2, hw2])
  -- `p`.
  refine WP.mono (hcp s₁ hg₁ fQ kQ hN₁) fun t ⟨hgt, hwspt, hPt, hpy, hpyv, hpx, hpxv, fP, kP, mkP⟩ => ?_
  obtain hPd : ∀ r ∈ [xRange op wp], r.1 + r.2 ≤ oq ∨ oq + slot wp 8 ≤ r.1 := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact .inl (by simp only [xRange]; omega_using [hpq, hX8])
  refine ⟨hgt, hN₁.of_frm (fP.mono fun r hr => List.mem_append_right _ hr) hlo hz (by omega_using [hwp2, hw2]),
    ⟨hwspt, hPt, hpy, hpyv, hpx, hpxv⟩,
    PrimeRdy.of_disj ⟨hwsq₁, hQ₁, hqy, hqyv, hqx, hqxv⟩ fP hPd (by omega_using [hoq, hn]),
    (fQ.mono fun r hr => by rw [List.mem_singleton.mp hr]; simp [preRanges]).trans
      (fP.mono fun r hr => by rw [List.mem_singleton.mp hr]; simp [preRanges]),
    kQ.trans kP |>.mono (by decide), ?_⟩
  rw [mkP, word_off, word_off, fQ.word_eq (fun r hr => by rcases hQd r hr with h | h <;> omega_arith) (by omega_using [hpq, hmk, ho64])]

/-- `p`'s workspace and values, after a change within `q`'s, after it. -/
theorem primeP_of {s s₁ : State} {B : Addr} {Z : Nat} {mp : BitVec 64} {P op wp oq : Nat}
    (hpq : op + slot wp 8 + wsTab wp ≤ oq) (hoq : oq + slot wp 8 + wsTab wp ≤ Z) (hn : B.toNat + Z ≤ 2 ^ 64)
    (fQ : Frm B [xRange oq wp] s.mem s₁.mem) (hsp : word s.mem B (8 * sWsP) = off B op)
    (hwsp : WsAt s.mem B op wp mp) (hP : XVals s B op wp mp P) :
    word s₁.mem B (8 * sWsP) = off B op ∧ WsAt s₁.mem B op wp mp ∧ XVals s₁ B op wp mp P ∧
      ∀ d, d + 8 ≤ oq → word s₁.mem B d = word s.mem B d := by
  obtain hX8 : 256 ≤ slot wp 8 := by unfold slot hdrBytes; omega_using []
  obtain ho64 : oq < 2 ^ 64 := by omega_using [hoq, hn, hX8]
  obtain hb : ∀ d, d + 8 ≤ oq → word s₁.mem B d = word s.mem B d := fun d hd => fQ.x_below hd ho64
  obtain hQd : ∀ r ∈ [xRange oq wp], r.1 + r.2 ≤ op ∨ op + slot wp 8 ≤ r.1 := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact .inr (by simp only [xRange]; omega_using [hpq])
  exact ⟨by rw [hb _ (by unfold sWsP sFn; omega_using [hpq, hX8])]; exact hsp,
    hwsp.of_disj fQ (fun r hr => by rcases hQd r hr with h | h <;> omega_using [h, hX8]) (by omega_using [hpq, hX8, ho64]),
    hP.of_disj fQ hQd (by omega_using [hpq, ho64]), hb⟩

/-- `preP`: `pre` with `R_q² mod q` and `R_p² mod p` from `pre`'s words
(whose values `VQ`, `VP` are them where `n`'s mask `c` is set; where it is
clear the primes are 3). -/
theorem preP_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv mp mq : BitVec 64}
    {N P Q C op wp oq VP VQ : Nat} {c : Bool}
    (hg : Good s B Z w minv) (hw28 : w < 2 ^ 28) (hlo : slot w 8 ≤ op)
    (hpq : op + slot wp 8 + wsTab wp ≤ oq) (hoq : oq + slot wp 8 + wsTab wp ≤ Z) (hwp2 : 2 ≤ wp)
    (hw2 : w = 2 * wp) (hsp : word s.mem B (8 * sWsP) = off B op) (hsq : word s.mem B (8 * sWsQ) = off B oq)
    (hwsp : WsAt s.mem B op wp mp) (hwsq : WsAt s.mem B oq wp mq) (hN : NVals s B w minv N)
    (hXm : wv s.mem B (slot w Public.aXm) w % N = C * 2 ^ (64 * w) % N)
    (hP : XVals s B op wp mp P) (hP1 : 1 < P) (hPodd : P % 2 = 1)
    (hQ : XVals s B oq wp mq Q) (hQ1 : 1 < Q) (hQodd : Q % 2 = 1)
    (hM : word s.mem B (8 * Public.sMask) = mask c)
    (hpP : PreW s B Z (r2XOff false wp) wp VP) (hpQ : PreW s B Z (r2XOff true wp) wp VQ)
    (hP3 : c = false → P = 3) (hVP : c = true → VP % P = 2 ^ (64 * wp * 2) % P)
    (hQ3 : c = false → Q = 3) (hVQ : c = true → VQ % Q = 2 ^ (64 * wp * 2) % Q) :
    WP isa (seqs (CrtIfma.preP M.mm)) s (PrePost s B Z w minv mp mq N P Q C op wp oq) := by
  have hn := hg.scr.nowrap
  obtain hX8 : 256 ≤ slot wp 8 := by unfold slot hdrBytes; omega_using []
  obtain h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  refine preWith_ok (by simp [CrtIfma.prepP]) (by simp [CrtIfma.prepP]) hg hlo hpq hoq hwp2 hw2 hN
    (prepP_ok M hg hw28 (by omega_using [hlo, hpq]) hoq hwp2 hw2 (by decide) hsq hwsq hXm hQ hQ1 hQodd hM hpQ hQ3 hVQ)
    fun s₁ hg₁ fQ kQ hN₁ => ?_
  obtain ⟨hsp₁, hwsp₁, hP₁, hb⟩ := primeP_of hpq hoq hn fQ hsp hwsp hP
  obtain hXm₁ : wv s₁.mem B (slot w Public.aXm) w = wv s.mem B (slot w Public.aXm) w :=
    wv_congr fun i hi => hb _ (by have := slot_le (w := w) (show Public.aXm < 8 by decide); omega_using [hlo, hpq, hi, this])
  obtain hi : InScr B Z s.mem s₁.mem := InScr.of_frm fQ fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only [xRange]; omega_using [hoq, hX8]
  exact prepP_ok M hg₁ hw28 hlo (by omega_using [hpq, hoq]) hwp2 hw2 (by decide) hsp₁ hwsp₁
    (by rw [hXm₁]; exact hXm) hP₁ hP1 hPodd
    (by rw [hb _ (by have := hdr_lt_slot w 8 (show Public.sMask < 32 by decide); omega_using [hlo, hpq, this])]; exact hM)
    (hpP.congr hi (kQ.gpr (by decide)) kQ.2.1 kQ.2.2) hP3 hVP

end VG.Proof.Bignum.X86_64
