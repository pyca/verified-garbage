module

public import VerifiedGarbage.Proof.Bignum.X86.PrivPre.Prime
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Validate
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Import
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedRt.Key
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # An RSA private key's precomputed values on x86: the factors' values

`pqCheck_ok`: the mask at `accOff` all ones exactly when `p q = n` (as the
first half of `CrtRt.validate`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PrivPre

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Impl.Bignum.X86.PrivPre (pqCheck primesInit setLen outOff shl primesBody check factor)
open VG.Proof.Bignum.X86.Crt (componentValue componentArguments)

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

theorem pqCheck_ok (h : In Ex base bytes len args s) {n p q : Nat}
    (hn : val32 s.mem base (lo len (.slot .wide 9)) (2 * cwc len .wide) = n)
    (hp : val32 s.mem base (lo len (.slot .wide 10)) (cwc len .wide) = p)
    (hq : val32 s.mem base (lo len (.slot .wide 11)) (cwc len .wide) = q) :
    WP isa pqCheck s fun u =>
      Frame (frameR base (s.gpr .esp) (valR len)) s.mem u.mem ∧
      w32 u.mem base accOff = (cmask (decide (p * q = n))).toNat ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have pf := h.prod_fit
  have bw := bc_eq_cwc len .wide
  have g := bc_ge h.lower' .wide
  have nw := h.scratch.nowrap
  have f17 := h.slot_fit .wide (j := 17) (by decide)
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have e9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide := rfl
  have e10 : lo len (.slot .wide 10) = numBase + 10 * st len .wide := rfl
  have e11 : lo len (.slot .wide 11) = numBase + 11 * st len .wide := rfl
  have e14 : lo len (.slot .wide 14) = numBase + 14 * st len .wide := rfl
  have e15 : lo len (.slot .wide 15) = numBase + 15 * st len .wide := rfl
  have e17 : lo len (.slot .wide 17) = numBase + 17 * st len .wide := rfl
  have nb : numBase = 3336 := rfl
  have ao : accOff = 8 := rfl
  have cb1 : cb len (one .wide) = bc len .wide := by simp [cb, one]
  have cw1 : cw len (one .wide) = cwc len .wide := by simp [cw, cwc, cb, one]
  have cb2 : cb len (two .wide) = 2 * bc len .wide := by simp [cb, two]
  have cw2 : cw len (two .wide) = 2 * cwc len .wide := by
    have := bc_dvd len .wide; simp [cw, cb, two, cwc]; omega_arith
  have ma : mulAOff = 2312 := rfl
  have po : prodOff = 256 := rfl
  have fitV := valR_fit h
  let cn := cwc len .wide
  unfold pqCheck
  -- `p` into the multiplicand, and `p q`.
  refine WP.seq (WP.mono (copy_ok h (x := .slot .wide 10) (d := mulA) (one_ok .wide) (by rw [cb1]; omega_arith)
    (by rw [cb1]; simp only [mulA, lo]; omega_arith) (by rw [cb1]; simp only [mulA, lo]; exact .inl (by omega_arith)))
    fun u₁ ⟨O₁, V₁, K₁⟩ => ?_)
  simp only [mulA, lo, cb1, cw1] at O₁ V₁
  rw [show numBase + 10 * st len .wide = lo len (.slot .wide 10) from rfl, hp] at V₁
  have h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega_arith))
  have k₁ : ∀ {d k}, numBase ≤ d → d + 4 * k ≤ bytes → val32 u₁.mem base d k = val32 s.mem base d k :=
    fun hd hk => O₁.val32 (.inr (by omega_using [pf.2.1, hd])) (by omega_using [hk, h.bytes_lt])
  refine WP.seq (WP.mono (wideProduct_ok h₁ (b := .slot .wide 11) (by omega_arith) (by simp only [lo]; omega_arith))
    fun u₂ ⟨F₂, V₂, K₂⟩ => ?_)
  rw [V₁, k₁ (d := lo len (.slot .wide 11)) (k := cwc len .wide) (by omega_arith) (by omega_arith), hq] at V₂
  have h₂ := h₁.keepF K₂ (by decide) (by decide) F₂ (prodR_fit h₁)
  have sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  rw [sp₁] at F₂
  have k₂ : ∀ {d k}, numBase ≤ d → d + 4 * k ≤ bytes → val32 u₂.mem base d k = val32 s.mem base d k :=
    fun hd hk => (prodR_keep h₁ F₂ (sp₁ ▸ h₁.room) (by omega_arith) hk).trans (k₁ hd hk)
  -- `p q = n`.
  have pq : val32 u₂.mem base prodOff (2 * cn) = p * q := by
    have sp := val32_succ u₂.mem base prodOff (2 * cn)
    rw [V₂] at sp
    have hl := val32_lt u₂.mem base prodOff (2 * cn)
    have hpq : p * q < 2 ^ (32 * (2 * cn)) := by
      have := val32_lt s.mem base (lo len (.slot .wide 10)) cn
      have := val32_lt s.mem base (lo len (.slot .wide 11)) cn
      rw [hp] at *; rw [hq] at *
      rw [show 32 * (2 * cn) = 32 * cn + 32 * cn by omega_arith, Nat.pow_add]
      exact Nat.mul_lt_mul'' (by assumption) (by assumption)
    have : w32 u₂.mem base (prodOff + 4 * (2 * cn)) = 0 := by
      by_contra hne
      have : 2 ^ (32 * (2 * cn)) ≤ 2 ^ (32 * (2 * cn)) * w32 u₂.mem base (prodOff + 4 * (2 * cn)) :=
        Nat.le_mul_of_pos_right _ (by omega_arith)
      omega_arith
    rw [this, Nat.mul_zero, Nat.add_zero] at sp
    exact sp.symm
  refine WP.seq (WP.mono (equal_ok h₂ (a := prod) (b := .slot .wide 9) (two_ok .wide)
    (by rw [cb2]; simp only [prod, lo]; omega_using [pf.1, pf.2.1, pf.2.2]) (by rw [cb2]; omega_arith)) fun u₃ ⟨M₃, C₃, K₃⟩ => ?_)
  simp only [prod, lo, cw2] at C₃
  rw [show numBase + 9 * st len .wide = lo len (.slot .wide 9) from rfl, k₂ (d := lo len (.slot .wide 9)) (k := 2 * cwc len .wide) (by omega_arith) (by omega_arith), hn,
    show 2 * cwc len .wide = 2 * cn from rfl, pq] at C₃
  have h₃ := h₂.regs K₃ M₃
  -- The mask stored.
  refine wp_storeS (h₃.scratch.ea (d := accOff) (by omega_arith))
    (h₃.scratch.write (d := accOff) (n := 4) (by omega_arith)) fun u₄ m₄ => WP.block_nil ?_
  have O₄ : Outside base accOff 4 u₃.mem u₄.mem := by rw [m₄.mem]; exact writeW32_outside _ _ _ (by omega_arith)
  have A₄ : w32 u₄.mem base accOff = (cmask (decide (p * q = n))).toNat := by
    rw [m₄.mem, w32_write_self, C₃]
  refine ⟨?_, A₄, (((K₁.mono (by decide)).trans K₂).trans K₃).trans ((m₄.keeps []).mono (by decide))⟩
  have sp₂ : u₂.gpr .esp = s.gpr .esp := (K₂.1 _ (by decide)).trans sp₁
  have F₁ : Frame (frameR base (s.gpr .esp) (valR len)) s.mem u₁.mem :=
    frameR_of_outside O₁ (by omega_arith) (by simp)
  have F₂' : Frame (frameR base (s.gpr .esp) (valR len)) u₁.mem u₂.mem :=
    frameR_mono F₂ fun p hp => by
      simp only [prodR, List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> simp
  have F₄ : Frame (frameR base (s.gpr .esp) (valR len)) u₂.mem u₄.mem := by
    rw [← M₃]; exact frameR_of_outside O₄ (by omega_arith) (by simp)
  exact (F₁.trans F₂').trans F₄

/-- The header: where the first factor's values go, `16 w` bytes into the
output, and the first factor's length. -/
theorem init_ok (h : RIn base bytes len args s) :
    WP isa (.block (primesInit ++ setLen 7)) s fun u =>
      Outside base outOff 16 s.mem u.mem ∧
      w32 u.mem base outOff = ((args 0).toNat + 16 * Spec.Rsa.modulusWords len) % 2 ^ 32 ∧
      w32 u.mem base lenOff = (args 7).toNat ∧
      w32 u.mem base accOff = w32 s.mem base accOff ∧
      Keeps [.eax, .ecx] s u := by
  have nw := h.scratch.nowrap
  have hup := h.upper'
  have pf := h.prod_fit
  have nb : numBase = 3336 := rfl
  have bl : 3336 ≤ bytes := by
    have := h.slot_fit .wide (j := 0) (by decide); simp only [lo] at this; omega_arith
  simp only [primesInit, setLen, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_movS (h.arg (i := 3) (by decide)) fun u₁ a₁ _ => ?_
  refine wp_addS rfl fun u₂ a₂ _ => wp_shr (by decide) fun u₃ a₃ _ => ?_
  refine PrivPre.shl_ok 4 fun u₄ K₄ m₄ e₄ => ?_
  have K₄' : Keeps [.ecx] s u₄ :=
    (((a₁.keeps.mono (by decide)).trans (a₂.keeps.mono (by decide))).trans (a₃.keeps.mono (by decide))).trans K₄
  have m₄' : u₄.mem = s.mem := by rw [m₄, a₃.mem, a₂.mem, a₁.mem]
  have h₄ := h.regs K₄' m₄'
  refine wp_movS (h₄.arg (i := 0) (by decide)) fun u₅ a₅ _ => wp_addS rfl fun u₆ a₆ _ => ?_
  have K₆ : Keeps [.eax, .ecx] s u₆ :=
    ((K₄'.mono (by decide)).trans (a₅.keeps.mono (by decide))).trans (a₆.keeps.mono (by decide))
  have m₆ : u₆.mem = s.mem := by rw [a₆.mem, a₅.mem, m₄']
  have h₆ := h.regs K₆ m₆
  refine wp_storeS (h₆.scratch.ea (d := outOff) (by simp only [outOff, winOff]; omega_arith))
    (h₆.scratch.write (d := outOff) (by simp only [outOff, winOff]; omega_arith)) fun u₇ s₇ => ?_
  have O₇ : Outside base 0 bytes u₆.mem u₇.mem := by
    rw [s₇.mem]
    exact (writeW32_outside _ _ _ (by simp only [outOff, winOff]; omega_arith)).mono (Nat.zero_le _)
      (by simp only [outOff, winOff]; omega_arith)
  have h₇ := h₆.keep (s₇.keeps []) (by decide) (by decide) O₇
  refine wp_movS (h₇.arg (i := 7) (by decide)) fun u₈ a₈ _ => ?_
  have h₈ := h₇.regs a₈.keeps a₈.mem
  refine wp_storeS (h₈.scratch.ea (d := lenOff) (by simp only [lenOff]; omega_arith))
    (h₈.scratch.write (d := lenOff) (by simp only [lenOff]; omega_arith)) fun u s₉ => WP.block_nil ?_
  have ecx₄ : (u₄.gpr .ecx).toNat = 16 * Spec.Rsa.modulusWords len := by
    rw [e₄, a₃.gpr, a₂.gpr, a₁.gpr, h.extra.nLen]
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      Spec.Rsa.modulusWords]
    rw [show (7 : BitVec 32).toNat = 7 from rfl]
    omega_arith
  have eax₆ : (u₆.gpr .eax).toNat = ((args 0).toNat + 16 * Spec.Rsa.modulusWords len) % 2 ^ 32 := by
    rw [a₆.gpr, a₅.gpr, BitVec.toNat_add, a₅.other _ (by decide), ecx₄]
  have mu : u.mem = (s.mem.writeW (off base outOff) (u₆.gpr .eax)).writeW (off base lenOff) (args 7) := by
    rw [s₉.mem, a₈.mem, s₇.mem, m₆, a₈.gpr]
  have hw : ∀ d, d + 4 ≤ 20 → d + 4 ≤ bytes := fun d hd => by omega_arith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [mu]
    exact ((writeW32_outside _ _ _ (by simp only [outOff, winOff]; omega_arith)).mono
      (by simp only [outOff, winOff]; omega) (by simp only [outOff, winOff]; omega)).trans
      ((writeW32_outside _ _ _ (by simp only [lenOff]; omega_arith)).mono
        (by simp only [outOff, winOff, lenOff]; omega) (by simp only [outOff, winOff, lenOff]; omega))
  · rw [mu, w32_write_ne nw (hw lenOff (by simp only [lenOff]; omega)) (hw outOff (by simp only [outOff, winOff]; omega))
      (by simp only [outOff, winOff, lenOff]; omega), w32_write_self, eax₆]
  · rw [mu, w32_write_self]
  · rw [mu, w32_write_ne nw (hw lenOff (by simp only [lenOff]; omega)) (hw accOff (by simp only [accOff]; omega))
      (by simp only [accOff, lenOff]; omega), w32_write_ne nw (hw outOff (by simp only [outOff, winOff]; omega))
      (hw accOff (by simp only [accOff]; omega)) (by simp only [accOff, outOff, winOff]; omega)]
  · exact (K₆.trans ((s₇.keeps []).mono (by decide))).trans
      ((a₈.keeps.mono (by decide)).trans ((s₉.keeps []).mono (by decide)))

/-- A frame of the working space's ranges (and of the stack below `sp`)
keeps a region apart from both. -/
theorem val32_frameR_apart {sp : BitVec 32} {ws : List (Nat × Nat)} {m m' : Mem}
    (F : Frame (frameR base sp ws) m m') (hfit : ∀ p ∈ ws, p.1 + p.2 ≤ bytes)
    {P : Addr} {L' : Nat} (hap : Region.Disjoint ⟨P, L'⟩ ⟨base, bytes⟩)
    (hs : Region.Disjoint ⟨P, L'⟩ (below sp 96)) (hPn : L' < 2 ^ 64) {d k : Nat} (hd : d + 4 * k ≤ L') :
    val32 m' P d k = val32 m P d k := by
  rw [← VG.Proof.Bignum.read_eq_val32, ← VG.Proof.Bignum.read_eq_val32]
  refine congrArg BitVec.toNat (F.read (r := ⟨off P d, 4 * k⟩) (Region.contains_self _ _) (fun r hr => ?_) (by omega))
  have sub : Region.Sub ⟨off P d, 4 * k⟩ ⟨P, L'⟩ := Offset.sub_base P (by omega)
  simp only [frameR, List.mem_cons, List.mem_map] at hr
  rcases hr with rfl | ⟨q, hq, rfl⟩
  · exact hs.sub_left sub
  · exact (hap.sub_left sub).sub_right (Offset.sub_base base (hfit q hq))

/-- A factor's value is below `2^(8 L)` for its length `L`. -/
theorem component_lt (m : Mem) (args : Nat → BitVec 32) (i : Nat) :
    componentValue m args i < 2 ^ (8 * (args (i + 1)).toNat) := by
  have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt m (byteAddr (args i)) (args (i + 1)).toNat)
  rwa [VG.Proof.Bignum.bytesAt_length, VG.Proof.Bignum.pow256_eq] at this

/-- The body of the factors' values, after the entry: `n`, `p` and `q`
loaded, the mask of `p q = n`, then each factor's `R² mod p` written to
`pre` after `n`'s values, and the mask's low bit in `eax`. -/
theorem primesBody_ok (h : RIn base bytes len args s) {L' : Nat}
    (hpw : InRegions s.wr (byteAddr (args 0)) L') (hn : (args 0).toNat + L' ≤ 2 ^ 32)
    (hap : Region.Disjoint ⟨byteAddr (args 0), L'⟩ ⟨base, bytes⟩)
    (hPa : ∀ i < 18, Region.Disjoint ⟨VG.Proof.Dsa.X86.stackAddress s i, 4⟩ ⟨byteAddr (args 0), L'⟩)
    (hs : Region.Disjoint ⟨byteAddr (args 0), L'⟩ (below (s.gpr .esp) 96))
    (hfit : 16 * Spec.Rsa.modulusWords len + 8 * Spec.Rsa.primeWords (args 7).toNat +
      8 * Spec.Rsa.primeWords (args 9).toNat ≤ L') :
    WP isa primesBody s fun u =>
      Frame [below (s.gpr .esp) 96, ⟨base, bytes⟩, ⟨byteAddr (args 0), L'⟩] s.mem u.mem ∧
      val32 u.mem (byteAddr (args 0)) (16 * Spec.Rsa.modulusWords len)
          (2 * Spec.Rsa.primeWords (args 7).toNat) =
        2 ^ r2Exp (args 7).toNat % safeM (componentValue s.mem args 6) ∧
      val32 u.mem (byteAddr (args 0)) (16 * Spec.Rsa.modulusWords len + 8 * Spec.Rsa.primeWords (args 7).toNat)
          (2 * Spec.Rsa.primeWords (args 9).toNat) =
        2 ^ r2Exp (args 9).toNat % safeM (componentValue s.mem args 8) ∧
      u.gpr .eax = BitVec.ofNat 32 (decide (componentValue s.mem args 6 * componentValue s.mem args 8 =
        componentValue s.mem args 2)).toNat ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have nw := h.scratch.nowrap
  have bl := h.bytes_lt
  have pf := h.prod_fit
  have hup := h.upper'
  have f18 := h.slot_fit .wide (j := 18) (by decide)
  have bw := bc_eq_cwc len .wide
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have el : ∀ j, lo len (.slot .wide j) = numBase + j * st len .wide := fun _ => rfl
  have nb : numBase = 3336 := rfl
  have pn : (byteAddr (args 0)).toNat = (args 0).toNat := VG.Proof.Bignum.X86.PublicRt.setWidth_toNat _
  have L64 : L' < 2 ^ 64 := by omega
  have p7 : 0 < (args 7).toNat := h.extra.positive 6 (by simp [componentArguments])
  have b7 : (args 7).toNat ≤ len := h.extra.bounded 6 (by simp [componentArguments])
  have p9 : 0 < (args 9).toNat := h.extra.positive 8 (by simp [componentArguments])
  have b9 : (args 9).toNat ≤ len := h.extra.bounded 8 (by simp [componentArguments])
  let W := Spec.Rsa.modulusWords len
  let wp := Spec.Rsa.primeWords (args 7).toNat
  let wq := Spec.Rsa.primeWords (args 9).toNat
  have wp2 : 2 ≤ wp := by simp only [wp, Spec.Rsa.primeWords]; omega
  have wq2 : 2 ≤ wq := by simp only [wq, Spec.Rsa.primeWords]; omega
  have e9 := el 9
  have e10 := el 10
  have e11 := el 11
  have e18 := el 18
  unfold primesBody check
  -- `n`, `p` and `q` (and the rest of the components).
  refine WP.seq (WP.seq (WP.mono (importComponents_ok h) fun u₁ ⟨O₁, n₁, _, p₁, q₁, _, _, _, K₁⟩ => ?_))
  have h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega_arith))
  -- `p q = n`.
  refine WP.mono (pqCheck_ok h₁ n₁ p₁ q₁) fun u₂ ⟨F₂, A₂, K₂⟩ => ?_
  have h₂ := h₁.keepF K₂ (by decide) (by decide) F₂ (valR_fit h₁)
  have sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  have k₂ : ∀ {d k}, numBase ≤ d → d + 4 * k ≤ bytes → val32 u₂.mem base d k = val32 u₁.mem base d k :=
    fun hd hk => valR_keep h₁ F₂ h₁.room hd hk
  -- The header.
  refine WP.seq (WP.mono (init_ok h₂) fun u₃ ⟨O₃, o₃, l₃, a₃, K₃⟩ => ?_)
  have h₃ := h₂.keep K₃ (by decide) (by decide) (O₃.mono (Nat.zero_le _) (by simp only [outOff, winOff]; omega_arith))
  have k₃ : ∀ {d k}, numBase ≤ d → d + 4 * k ≤ bytes → val32 u₃.mem base d k = val32 u₁.mem base d k :=
    fun hd hk => by
      rw [VG.Proof.Mont.Outside.val32 O₃ (.inr (by simp only [outOff, winOff]; omega_arith))
        (by omega_arith)]; exact k₂ hd hk
  have sp₃ : u₃.gpr .esp = s.gpr .esp := by rw [K₃.1 _ (by decide), K₂.1 _ (by decide), sp₁]
  have wr₃ : u₃.wr = s.wr := by rw [K₃.2.2, K₂.2.2, K₁.2.2]
  have sa₃ : ∀ i, VG.Proof.Dsa.X86.stackAddress u₃ i = VG.Proof.Dsa.X86.stackAddress s i := fun i => by
    simp only [VG.Proof.Dsa.X86.stackAddress, sp₃]
  -- The factor `p`.
  have W16 : (args 0).toNat + 16 * W < 2 ^ 32 := by omega
  refine WP.seq (WP.mono (factor_ok h₃ (f := 10) (p := componentValue s.mem args 6) (by decide) (by decide)
    (by rw [k₃ (by omega_arith) (by omega_arith), p₁])
    (by rw [l₃]; omega) (by rw [l₃]; exact b7) (by rw [l₃]; exact component_lt s.mem args 6)
    (P := byteAddr (args 0)) (L' := L') (y := 16 * W) (by rw [wr₃]; exact hpw) (by rw [pn]; exact hn) hap
    (by rw [o₃, pn]; exact Nat.mod_eq_of_lt W16) (by rw [l₃]; omega))
    fun u₄ ⟨⟨m₄, F₄, O₄⟩, V₄, W₄, K₄⟩ => ?_)
  rw [l₃] at O₄ V₄ W₄
  have eW : W = Spec.Rsa.modulusWords len := rfl
  have h₄ := in_keepFOut h₃ K₄ (by decide) (by decide) F₄ (primeR2_fit h₃) (L' := L') O₄ (by rw [eW]; omega)
    fun i hi => by rw [sa₃]; exact hPa i hi
  have sp₄ : u₄.gpr .esp = s.gpr .esp := by rw [K₄.1 _ (by decide), sp₃]
  rw [sp₃] at F₄
  -- What the factor `p`'s step keeps: the slots from the wide slot 9 on, the word at `accOff`, and `pre`
  -- outside its values.
  have F₄w : ∀ {d k}, lo len (.slot .wide 9) ≤ d → d + 4 * k ≤ bytes → val32 u₄.mem base d k = val32 u₃.mem base d k :=
    fun hd hk => by
      rw [PrecomputedRt.val32_apart (base := byteAddr (args 0)) (P := base) (L := bytes) O₄ (by rw [eW]; omega)
        hap.symm hk]
      exact frameR_val32 F₄ h.room nw hk (fun q hq => .inr (Nat.le_trans (primeR2_below h₃ q hq).1 hd)) (primeR2_fit h₃)
  have A₄ : w32 u₄.mem base accOff = w32 u₃.mem base accOff := by
    rw [← w32_val32_one, ← w32_val32_one,
      PrecomputedRt.val32_apart (base := byteAddr (args 0)) (P := base) (L := bytes) O₄ (by rw [eW]; omega)
        hap.symm (by simp only [accOff]; omega_arith)]
    exact frameR_val32 F₄ h.room nw (by simp only [accOff]; omega_arith)
      (fun q hq => by have := (primeR2_below h₃ q hq).2; simpa using this) (primeR2_fit h₃)
  have P₄ : ∀ {d k}, d + 4 * k ≤ 16 * W → val32 u₄.mem (byteAddr (args 0)) d k = val32 u₃.mem (byteAddr (args 0)) d k :=
    fun hd => by
      rw [VG.Proof.Mont.Outside.val32 O₄ (.inl hd) (by omega)]
      exact val32_frameR_apart F₄ (primeR2_fit h₃) hap hs L64 (by omega)
  -- The second factor's length.
  unfold setLen
  refine WP.seq (wp_movS (h₄.arg (i := 9) (by decide)) fun v₁ b₁ _ => ?_)
  have hv₁ := h₄.regs b₁.keeps b₁.mem
  refine wp_storeS (hv₁.scratch.ea (d := lenOff) (by simp only [lenOff]; omega_arith))
    (hv₁.scratch.write (d := lenOff) (by simp only [lenOff]; omega_arith)) fun u₅ s₅ => WP.block_nil ?_
  have m₅ : u₅.mem = u₄.mem.writeW (off base lenOff) (args 9) := by rw [s₅.mem, b₁.mem, b₁.gpr]
  have O₅ : VG.Proof.Mont.Outside base lenOff 4 u₄.mem u₅.mem := by
    rw [m₅]; exact writeW32_outside _ _ _ (by simp only [lenOff]; omega_arith)
  have h₅ := hv₁.keep (s₅.keeps []) (by decide) (by decide)
    (by rw [b₁.mem]; exact O₅.mono (Nat.zero_le _) (by simp only [lenOff]; omega_arith))
  have K₅ : Keeps [.eax] u₄ u₅ := b₁.keeps.trans ((s₅.keeps []).mono (by decide))
  have sp₅ : u₅.gpr .esp = s.gpr .esp := by rw [K₅.1 _ (by decide), sp₄]
  have hw20 : ∀ d, d + 4 ≤ 20 → d + 4 ≤ bytes := fun d hd => by omega_arith
  sorry


end

end VG.Proof.Bignum.X86.PrivPre
