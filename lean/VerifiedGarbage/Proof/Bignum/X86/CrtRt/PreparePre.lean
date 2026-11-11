module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Stage
public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedRt.Copy

/-! # A context prepared from a cached `R² mod p` (i686)

`vg_rsa_private_crt_precomputed` sets a factor's context up from its
`R_pre² mod p` in `pre`, for `R_pre = 2^(64 w)`, `w = max(2, ⌈l / 8⌉)` and
the factor's length `l`: `primeBytes` computes `8 w` (`primeBytes_ok`);
`loadR2` copies the value into slot 4 and counts the doublings to the
context's radix (`loadR2_ok`); `preparePre` leaves what `prepare` does
(`preparePre_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Impl.Bignum.X86.PublicRt (argAt)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `add d, src`, and ZF. -/
theorem wp_addZ {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ t, Upd s t d (s.gpr d + v) → t.zf = some (s.gpr d + v == 0) → WP isa (.block is) t Q) :
    WP isa (.block (.alu .add d src :: is)) s Q :=
  cons (by simp only [exec, execAlu, h, Option.bind_some]; rfl) (k _ (Upd.flags _ _ _ _ _ _) rfl)

/-- `primeBytes r t`: `r = 8 max(2, ⌈l / 8⌉)` from `r = l ≥ 1`. -/
theorem primeBytes_ok {r t : Reg} (hrt : r ≠ t) {l : Nat} (hr : s.gpr r = BitVec.ofNat 32 l) (hl : 1 ≤ l)
    (hl' : l < 2 ^ 31)
    (kk : ∀ u, Keeps [r, t] s u → u.mem = s.mem →
      u.gpr r = BitVec.ofNat 32 (8 * Spec.Rsa.primeWords l) → WP isa (.block is) u Q) :
    WP isa (.block (primeBytes r t ++ is)) s Q := by
  simp only [primeBytes, List.cons_append, List.nil_append]
  refine wp_addS rfl fun u₁ U₁ _ => VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun u₂ U₂ => ?_
  refine wp_movS rfl fun u₃ U₃ _ => wp_subS rfl fun u₄ U₄ c₄ => wp_sbbS rfl c₄ fun u₅ U₅ _ => ?_
  refine wp_logicS (.inl rfl) rfl fun u₆ U₆ => wp_addS rfl fun u₇ U₇ _ => ?_
  refine wp_addS rfl fun u₈ U₈ _ => wp_addS rfl fun u₉ U₉ _ => wp_addS rfl fun u₁₀ U₁₀ _ => ?_
  have K : Keeps [r, t] s u₁₀ := by
    refine ((((U₁.keeps.mono (by simp)).trans (U₂.keeps.mono (by simp))).trans
      ((U₃.keeps.mono (by simp)).trans (U₄.keeps.mono (by simp)))).trans
      (((U₅.keeps.mono (by simp)).trans (U₆.keeps.mono (by simp))).trans
      ((U₇.keeps.mono (by simp)).trans (U₈.keeps.mono (by simp))))).trans
      ((U₉.keeps.mono (by simp)).trans (U₁₀.keeps.mono (by simp)))
  refine kk u₁₀ K (by rw [U₁₀.mem, U₉.mem, U₈.mem, U₇.mem, U₆.mem, U₅.mem, U₄.mem, U₃.mem, U₂.mem, U₁.mem]) ?_
  -- `x = ⌈l / 8⌉`, and one more if it is one.
  have hx : (u₂.gpr r).toNat = (l + 7) / 8 := by
    rw [U₂.gpr, BitVec.toNat_ushiftRight, U₁.gpr, hr, BitVec.toNat_add, BitVec.toNat_ofNat,
      show (7 : BitVec 32).toNat = 7 from rfl, Nat.shiftRight_eq_div_pow]
    congr 1; omega
  have r₅ : u₅.gpr r = u₂.gpr r := by
    rw [U₅.other _ hrt, U₄.other _ hrt, U₃.other _ hrt]
  have t₆ : (u₆.gpr t).toNat = if (l + 7) / 8 < 2 then 1 else 0 := by
    rw [U₆.gpr, ite_eq_left rfl, U₅.gpr, BitVec.sub_self, BitVec.toNat_and, U₃.gpr, hx]
    by_cases e : (l + 7) / 8 < 2 <;> simp [e]
  have r₇ : (u₇.gpr r).toNat = (l + 7) / 8 + (if (l + 7) / 8 < 2 then 1 else 0) := by
    rw [U₇.gpr, BitVec.toNat_add, t₆, U₆.other _ hrt, r₅, hx]
    split <;> omega
  apply BitVec.eq_of_toNat_eq
  rw [U₁₀.gpr, U₉.gpr, U₈.gpr]
  simp only [BitVec.toNat_add, r₇, BitVec.toNat_ofNat, Spec.Rsa.primeWords, Spec.Rsa.modulusWords]
  split <;> omega

/-- The byte offset in `pre`, from argument 18, of factor `i`'s cached value. -/
abbrev preOff (args : Nat → BitVec 32) (i : Nat) : Nat :=
  if i = 0 then 0 else 8 * Spec.Rsa.primeWords (args 7).toNat

/-- The words of 64 bits of factor `i`'s cached value. -/
abbrev preW (args : Nat → BitVec 32) (i : Nat) : Nat := Spec.Rsa.primeWords (args (7 + 2 * i)).toNat

/-- Factor `i`'s cached `R_pre² mod p` in `pre`, readable, apart from the
working space, and fitting the context `c`. -/
structure PreR2 (s : State) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (i : Nat) (c : Ctx) (p : Nat) :
    Prop where
  arg : CallArgument s base bytes preArg (args preArg)
  hi : i ≤ 1
  pos : 1 ≤ (args (7 + 2 * i)).toNat
  lt : (args (7 + 2 * i)).toNat < 1024
  lt7 : (args 7).toNat < 1024
  pos7 : 1 ≤ (args 7).toNat
  fits : 8 * preW args i ≤ bc len c
  read : InRegions (s.rd ++ s.wr) (byteAddr (args preArg)) (preOff args i + 8 * preW args i)
  fit : (args preArg).toNat + (preOff args i + 8 * preW args i) ≤ 2 ^ 32
  apart : Region.Disjoint ⟨byteAddr (args preArg), preOff args i + 8 * preW args i⟩ ⟨base, bytes⟩
  val : val32 s.mem (byteAddr (args preArg)) (preOff args i) (2 * preW args i) = 2 ^ (128 * preW args i) % p

variable {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

/-- `loadR2`: factor `i`'s cached value in slot 4, and `esi` its doublings to the context's radix. -/
theorem loadR2_ok (h : In Ex base bytes len args s) {i : Nat} {c : Ctx} {p : Nat} (P : PreR2 s base bytes len args i c p) :
    WP isa (loadR2 c i) s fun u => In Ex base bytes len args u ∧
      sv u.mem base len c 4 = 2 ^ (128 * preW args i) % p ∧
      (u.gpr .esi).toNat = 16 * (bc len c - 8 * preW args i) ∧
      u.zf = some (u.gpr .esi == 0) ∧
      Outside base (lo len (.slot c 4)) (bc len c) s.mem u.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .esi] s u := by
  have nw' := h.scratch.nowrap
  have bl := h.bytes_lt
  have f8 := h.slot_fit c (j := 8) (by decide)
  have s48 : lo len (.slot c 4) + st len c ≤ lo len (.slot c 8) := sl_le (len := len) c (by decide)
  have est : st len c = 2 * bc len c + 32 := rfl
  have bw := bc_eq_cwc len c
  have hb := bc_le h.upper' c
  have cb1 : cb len (one c) = bc len c := by simp [cb, one]
  have cw1 : cw len (one c) = cwc len c := by simp [cw, cwc, cb, one]
  have fits := P.fits
  have hi := P.hi
  have pw2 : 2 ≤ preW args i := by simp only [preW, Spec.Rsa.primeWords]; omega
  unfold loadR2
  refine WP.seq (WP.mono (zero_ok h (x := .slot c 4) (one_ok c) (by rw [cb1]; omega)) fun u₁ ⟨O₁, Z₁, K₁⟩ => ?_)
  rw [cb1] at O₁
  rw [cw1] at Z₁
  have h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega))
  have A₁ := P.arg.keep K₁ (by decide) (O₁.mono (Nat.zero_le _) (by omega))
  have l7 := P.lt7
  have li := P.lt
  have pos := P.pos
  -- The pointers and the count.
  refine WP.seq (wp_movS (h₁.arg (i := 7 + 2 * i) (by omega)) fun u₂ U₂ _ => ?_)
  refine primeBytes_ok (r := .ecx) (t := .eax) (by decide) (l := (args (7 + 2 * i)).toNat)
    (by rw [U₂.gpr, BitVec.ofNat_toNat, BitVec.setWidth_eq]) pos (by omega) fun u₃ K₃ m₃ e₃ => ?_
  have A₃ := A₁.keep ((U₂.keeps.mono (by decide)).trans K₃) (by simp) (by rw [m₃, U₂.mem]; exact Outside.refl _ _ _ _)
  refine wp_movS A₃.readSrc fun u₄ U₄ _ => ?_
  -- `esi` at factor `i`'s value, `ecx` its bytes.
  have hpt : ∀ {is' : List Instr} {Q' : State → Prop},
      (∀ v, Keeps [.eax, .ecx, .edx, .esi] u₄ v → v.mem = u₄.mem →
        PtrAt v (byteAddr (args preArg)) .esi (preOff args i) →
        v.gpr .ecx = BitVec.ofNat 32 (8 * preW args i) → WP isa (.block is') v Q') →
      WP isa (.block ((if i = 0 then [] else [.mov .edx (.mem (argAt 0 7))] ++ primeBytes .edx .eax ++
        [.alu .add .esi (.reg .edx)]) ++ is')) u₄ Q' := by
    intro is' Q' kk
    have esi₄ : (u₄.gpr .esi).toNat = (args preArg).toNat := by rw [U₄.gpr]
    have ecx₄ : u₄.gpr .ecx = BitVec.ofNat 32 (8 * preW args i) := by rw [U₄.other _ (by decide), e₃]
    have bA : (byteAddr (args preArg)).toNat = (args preArg).toNat := by
      simp [byteAddr, BitVec.toNat_setWidth]; omega
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · refine kk u₄ (Keeps.refl _ _) rfl ?_ ecx₄
      rw [PtrAt, esi₄, bA]; simp only [preOff, ite_true, Nat.add_zero]
      exact (Nat.mod_eq_of_lt (by have := (args preArg).isLt; omega)).symm
    · simp only [show (1 : Nat) ≠ 0 from by decide, ite_false, List.append_assoc, List.cons_append,
        List.nil_append]
      have h₄ := h₁.regs ((U₂.keeps.mono (by decide)).trans ((K₃.mono (by decide)).trans (U₄.keeps.mono (by decide)))
        : Keeps [.eax, .ecx, .esi] u₁ u₄) (by rw [U₄.mem, m₃, U₂.mem])
      refine wp_movS (h₄.arg (i := 7) (by decide)) fun v₁ V₁ _ => ?_
      refine primeBytes_ok (r := .edx) (t := .eax) (by decide) (l := (args 7).toNat)
        (by rw [V₁.gpr, BitVec.ofNat_toNat, BitVec.setWidth_eq]) P.pos7 (by omega) fun v₂ K₂ m₂ e₂ => ?_
      refine wp_addS rfl fun v₃ V₃ _ => kk v₃ ?_ (by rw [V₃.mem, m₂, V₁.mem]) ?_ ?_
      · exact ((V₁.keeps.mono (by decide)).trans (K₂.mono (by decide))).trans (V₃.keeps.mono (by decide))
      · rw [PtrAt, V₃.gpr, BitVec.toNat_add, e₂, K₂.1 _ (by decide), V₁.other _ (by decide), esi₄, bA,
          BitVec.toNat_ofNat]
        simp only [preOff, show (1 : Nat) ≠ 0 from by decide, ite_false]
        have := (args preArg).isLt
        have : 8 * Spec.Rsa.primeWords (args 7).toNat < 2 ^ 32 := by
          simp only [Spec.Rsa.primeWords, Spec.Rsa.modulusWords]; omega
        omega
      · rw [V₃.other _ (by decide), K₂.1 _ (by decide), V₁.other _ (by decide), ecx₄]
  have K₄ : Keeps [.eax, .ecx, .esi] u₁ u₄ :=
    (U₂.keeps.mono (by decide)).trans ((K₃.mono (by decide)).trans (U₄.keeps.mono (by decide)))
  have m₄ : u₄.mem = u₁.mem := by rw [U₄.mem, m₃, U₂.mem]
  refine hpt (is' := ptrTo (.slot c 4) .ebp .eax) fun v Kv mv pv cv => ?_
  have hv := h₁.regs ((K₄.mono (by decide)).trans Kv : Keeps [.eax, .ecx, .edx, .esi] u₁ v) (by rw [mv, m₄])
  rw [← List.append_nil (ptrTo (.slot c 4) .ebp .eax)]
  refine ptrTo_ok (r := .ebp) (t := .eax) (by decide) (by decide) hv.edi hv.width h.upper' (by omega)
    fun w Kw mw pw => WP.block_nil ?_
  have hw := hv.regs Kw mw
  have Kw₁ : Keeps [.eax, .ecx, .edx, .esi, .ebp] u₁ w := ((K₄.mono (by decide)).trans (Kv.mono (by decide))).trans (Kw.mono (by decide))
  -- The copy.
  have hr : InRegions (w.rd ++ w.wr) (byteAddr (args preArg)) (preOff args i + 8 * preW args i) := by
    rw [Kw₁.2.1, Kw₁.2.2, K₁.2.1, K₁.2.2]; exact P.read
  have bA : (byteAddr (args preArg)).toNat = (args preArg).toNat := by
    simp [byteAddr, BitVec.toNat_setWidth]; omega
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86.PrecomputedRt.copyLoop_ok (N := 2 * preW args i)
    (x := lo len (.slot c 4)) (y := preOff args i) hw.ws hr
    (by rw [bA]; exact P.fit) P.apart (by omega) (by omega) (by omega) pw
    (by rw [PtrAt, Kw.1 _ (by decide)]; exact pv)
    (by rw [Kw.1 _ (by decide), cv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega))
    fun t₁ ⟨Ot, Vt, Kt⟩ => ?_)
  sorry

end

end VG.Proof.Bignum.X86.CrtRt
