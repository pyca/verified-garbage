module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Stage
public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
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
  top : (s.gpr .esp).toNat + 80 ≤ 2 ^ 32
  apartSp : Region.Disjoint ⟨byteAddr (args preArg), preOff args i + 8 * preW args i⟩ (below (s.gpr .esp) 96)

section
variable {s t : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {i : Nat} {c : Ctx} {p : Nat}

/-- The cached value holds after a stage that changes registers but `esp`, and memory in its ranges. -/
theorem PreR2.keepF (P : PreR2 s base bytes len args i c p)
    (room : CallRoom (s.gpr .esp) base bytes) {regs : List Reg} (K : Keeps regs s t) (sp : .esp ∉ regs)
    {ws : List (Nat × Nat)} (F : Frame (frameR base (s.gpr .esp) ws) s.mem t.mem)
    (hfit : ∀ q ∈ ws, q.1 + q.2 ≤ bytes) : PreR2 t base bytes len args i c p := by
  have esp : t.gpr .esp = s.gpr .esp := K.1 _ sp
  have low := room.low
  have top := P.top
  have fit := P.fit
  refine ⟨⟨P.arg.stack.keep K sp, ?_⟩, P.hi, P.pos, P.lt, P.lt7, P.pos7, P.fits, by rw [K.2.1, K.2.2]; exact P.read,
    P.fit, P.apart, ?_, by rw [esp]; exact P.top, by rw [esp]; exact P.apartSp⟩
  · rw [← P.arg.value]
    unfold VG.Proof.Dsa.X86.stackValue
    rw [show VG.Proof.Dsa.X86.stackAddress t preArg = VG.Proof.Dsa.X86.stackAddress s preArg by
      simp only [VG.Proof.Dsa.X86.stackAddress, esp]]
    refine F.readW (r := ⟨VG.Proof.Dsa.X86.stackAddress s preArg, 4⟩) (Region.contains_self _ _) (fun r hr => ?_)
      (by decide)
    simp only [frameR, List.mem_cons, List.mem_map] at hr
    rcases hr with rfl | ⟨q, hq, rfl⟩
    · have ea : (VG.Proof.Dsa.X86.stackAddress s preArg).toNat = (s.gpr .esp).toNat + (4 + 4 * preArg) := by
        simp only [VG.Proof.Dsa.X86.stackAddress, addr, PublicRt.setWidth_toNat, BitVec.toNat_add, BitVec.toNat_ofNat,
          preArg]
        omega
      have eb : ((s.gpr .esp - BitVec.ofNat 32 96).setWidth 64).toNat = (s.gpr .esp).toNat - 96 := by
        rw [PublicRt.setWidth_toNat, VG.X86.sub_toNat (by omega)]
      exact (Region.disjoint_of_le (r₁ := below (s.gpr .esp) 96) (.inl (by dsimp only; rw [eb, ea]; omega))
        (by dsimp only; rw [eb]; omega) (by dsimp only; rw [ea]; simp only [preArg]; omega)).symm
    · refine P.arg.stack.apart.sub_right ?_
      have := hfit q hq
      have := Offset.sub base (d := q.1) (n := q.2) (e := 0) (k := bytes) (Nat.zero_le _) (by omega)
      simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  · rw [← P.val, ← VG.Proof.Bignum.read_eq_val32, ← VG.Proof.Bignum.read_eq_val32]
    have bA : (byteAddr (args preArg)).toNat = (args preArg).toNat := by
      simp [byteAddr, BitVec.toNat_setWidth]; omega
    have hsub : Region.Sub ⟨off (byteAddr (args preArg)) (preOff args i), 4 * (2 * preW args i)⟩
        ⟨byteAddr (args preArg), preOff args i + 8 * preW args i⟩ := by
      have := Offset.sub (byteAddr (args preArg)) (d := preOff args i) (n := 4 * (2 * preW args i)) (e := 0)
        (k := preOff args i + 8 * preW args i) (Nat.zero_le _) (by omega)
      simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
    refine congrArg BitVec.toNat (F.read (Region.contains_self _ _) (fun r hr => ?_) (by omega))
    simp only [frameR, List.mem_cons, List.mem_map] at hr
    rcases hr with rfl | ⟨q, hq, rfl⟩
    · exact (P.apartSp.sub_left hsub)
    · refine (P.apart.sub_left hsub).sub_right ?_
      have := hfit q hq
      have := Offset.sub base (d := q.1) (n := q.2) (e := 0) (k := bytes) (Nat.zero_le _) (by omega)
      simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this

end

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
  have fitsW : 8 * Spec.Rsa.primeWords (args (7 + 2 * i)).toNat ≤ bc len c := P.fits
  have pw2' : 2 ≤ Spec.Rsa.primeWords (args (7 + 2 * i)).toNat := pw2
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
  have Ot₀ : Outside base 0 bytes w.mem t₁.mem := Ot.mono (Nat.zero_le _) (by omega)
  have ht₁ := hw.keep Kt (by decide) (by decide) Ot₀
  refine wp_movS (ht₁.arg (i := 7 + 2 * i) (by omega)) fun t₂ T₂ _ => ?_
  refine primeBytes_ok (r := .edx) (t := .eax) (by decide) (l := (args (7 + 2 * i)).toNat)
    (by rw [T₂.gpr, BitVec.ofNat_toNat, BitVec.setWidth_eq]) pos (by omega) fun t₃ K₃' m₃' e₃' => ?_
  have K₃'' : Keeps [.eax, .edx] t₁ t₃ := (T₂.keeps.mono (by decide)).trans (K₃'.mono (by decide))
  have ht₃ := ht₁.regs K₃'' (by rw [m₃', T₂.mem])
  refine widthC_ok ht₃.width h.upper' fun t₄ K₄' m₄' e₄' => ?_
  refine wp_subS rfl fun t₅ T₅ _ => wp_addS rfl fun t₆ T₆ _ => wp_addS rfl fun t₇ T₇ _ =>
    wp_addS rfl fun t₈ T₈ _ => wp_addZ rfl fun u U z => WP.block_nil ?_
  have Ku : Keeps [.eax, .edx, .esi] t₃ u := (K₄'.mono (by decide)).trans ((((T₅.keeps.mono (by decide)).trans
    (T₆.keeps.mono (by decide))).trans ((T₇.keeps.mono (by decide)).trans (T₈.keeps.mono (by decide)))).trans
    (U.keeps.mono (by decide)))
  have mu : u.mem = t₁.mem := by rw [U.mem, T₈.mem, T₇.mem, T₆.mem, T₅.mem, m₄', m₃', T₂.mem]
  -- The count.
  have hd : (t₄.gpr .edx).toNat = 8 * preW args i := by
    rw [K₄'.1 _ (by decide), e₃', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h5 : (t₅.gpr .esi).toNat = bc len c - 8 * preW args i := by
    rw [T₅.gpr, BitVec.toNat_sub, hd, e₄', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := bc len c) (by omega)]; omega
  have h8 : (t₈.gpr .esi).toNat = 8 * (bc len c - 8 * preW args i) := by
    rw [T₈.gpr, BitVec.toNat_add, T₇.gpr, BitVec.toNat_add, T₆.gpr, BitVec.toNat_add, h5]; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ht₃.regs Ku (by rw [mu, m₃', T₂.mem])
  · -- The value: the copy, and zero above it.
    have mw₁ : w.mem = u₁.mem := by rw [mw, mv, m₄]
    have tail : val32 t₁.mem base (lo len (.slot c 4) + 4 * (2 * preW args i)) (cwc len c - 2 * preW args i) = 0 := by
      rw [Ot.val32 (.inr (Nat.le_refl _)) (by omega), mw₁]
      have Zs := Z₁
      rw [show cwc len c = 2 * preW args i + (cwc len c - 2 * preW args i) by omega, val32_append] at Zs
      simp only [Nat.add_eq_zero_iff, Nat.mul_eq_zero, Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _), false_or] at Zs
      exact Zs.2
    have src : val32 w.mem (byteAddr (args preArg)) (preOff args i) (2 * preW args i) =
        val32 s.mem (byteAddr (args preArg)) (preOff args i) (2 * preW args i) := by
      rw [mw₁]
      refine val32_congr fun j hj => congrArg BitVec.toNat (Mem.readW_congr fun k hk =>
        VG.Proof.Bignum.X86.PrecomputedRt.outside_apart O₁ (L := bytes) (by omega) ?_)
      intro hc
      refine P.apart _ ?_ hc
      rw [Offset.add_add]
      exact Region.contains_ofNat _ (by omega)
    simp only [sv]
    rw [mu, show cwc len c = 2 * preW args i + (cwc len c - 2 * preW args i) by omega, val32_append, tail,
      Nat.mul_zero, Nat.add_zero, Vt, src, P.val]
  · rw [U.gpr, BitVec.toNat_add, h8]; omega
  · rw [z, U.gpr]
  · rw [mu]
    have O' := Ot.mono (o' := lo len (.slot c 4)) (n' := bc len c) (Nat.le_refl _) (by omega)
    rw [mw, mv, m₄] at O'
    exact O₁.trans O'
  · exact (K₁.mono (by decide)).trans (((K₄.mono (by decide)).trans (Kv.mono (by decide))).trans
      ((Kw.mono (by decide)).trans ((Kt.mono (by decide)).trans ((K₃''.mono (by decide)).trans (Ku.mono (by decide))))))

end

end VG.Proof.Bignum.X86.CrtRt
