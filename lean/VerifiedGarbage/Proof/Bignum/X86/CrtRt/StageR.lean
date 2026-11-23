module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Stage
public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedRt.Copy

/-! # A factor's context from a cached `R² mod p`, and the ranges its power changes (i686)

## A context prepared from a cached `R² mod p`

`vg_rsa_private_crt_precomputed` sets a factor's context up from its
`R_pre² mod p` in `pre`, for `R_pre = 2^(64 w)`, `w = max(2, ⌈l / 8⌉)` and
the factor's length `l`: `primeBytes` computes `8 w` (`primeBytes_ok`);
the current factor is the one the header names (`PreHdr`): its length at
`lenOff`, and the parity of the count of factors left at `leftOff`.
`loadHead` points at its value from them (`loadHead_ok`), `loadTail` copies
the value into slot 4 and counts the doublings to the context's radix
(`loadTail_ok`); `preparePre` leaves what `prepare` does (`preparePre_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Impl.Bignum.X86.PublicRt (argAt)
open VG.Proof.Bignum.X86.PublicRt (count1_zf countLoop)

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
  obtain K : Keeps [r, t] s u₁₀ := by
    refine ((((U₁.keeps.mono (by simp)).trans (U₂.keeps.mono (by simp))).trans
      ((U₃.keeps.mono (by simp)).trans (U₄.keeps.mono (by simp)))).trans
      (((U₅.keeps.mono (by simp)).trans (U₆.keeps.mono (by simp))).trans
      ((U₇.keeps.mono (by simp)).trans (U₈.keeps.mono (by simp))))).trans
      ((U₉.keeps.mono (by simp)).trans (U₁₀.keeps.mono (by simp)))
  refine kk u₁₀ K (by rw [U₁₀.mem, U₉.mem, U₈.mem, U₇.mem, U₆.mem, U₅.mem, U₄.mem, U₃.mem, U₂.mem, U₁.mem]) ?_
  -- `x = ⌈l / 8⌉`, and one more if it is one.
  obtain hx : (u₂.gpr r).toNat = (l + 7) / 8 := by
    rw [U₂.gpr, BitVec.toNat_ushiftRight, U₁.gpr, hr, BitVec.toNat_add, BitVec.toNat_ofNat,
      show (7 : BitVec 32).toNat = 7 from rfl, Nat.shiftRight_eq_div_pow]
    congr 1; omega_using [hl']
  obtain r₅ : u₅.gpr r = u₂.gpr r := by
    rw [U₅.other _ hrt, U₄.other _ hrt, U₃.other _ hrt]
  obtain t₆ : (u₆.gpr t).toNat = if (l + 7) / 8 < 2 then 1 else 0 := by
    rw [U₆.gpr, ite_eq_left rfl, U₅.gpr, BitVec.sub_self, BitVec.toNat_and, U₃.gpr, hx]
    by_cases e : (l + 7) / 8 < 2 <;> simp [e]
  obtain r₇ : (u₇.gpr r).toNat = (l + 7) / 8 + (if (l + 7) / 8 < 2 then 1 else 0) := by
    rw [U₇.gpr, BitVec.toNat_add, t₆, U₆.other _ hrt, r₅, hx]
    split <;> omega_using [hl']
  apply BitVec.eq_of_toNat_eq
  rw [U₁₀.gpr, U₉.gpr, U₈.gpr]
  simp only [BitVec.toNat_add, r₇, BitVec.toNat_ofNat, Spec.Rsa.primeWords, Spec.Rsa.modulusWords]
  split <;> omega_arith

/-- The byte offset in `pre`, from argument 18, of factor `i`'s cached value. -/
abbrev preOff (args : Nat → BitVec 32) (i : Nat) : Nat :=
  if i = 0 then 0 else 8 * Spec.Rsa.primeWords (args 7).toNat

/-- The words of 64 bits of factor `i`'s cached value. -/
abbrev preW (args : Nat → BitVec 32) (i : Nat) : Nat := Spec.Rsa.primeWords (args (7 + 2 * i)).toNat

/-- Factor `i`'s cached `R_pre² mod p` in `pre`, readable, apart from the
working space. -/
structure PreR2 (s : State) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (i : Nat) (p : Nat) :
    Prop where
  arg : CallArgument s base bytes preArg (args preArg)
  hi : i ≤ 1
  pos : 1 ≤ (args (7 + 2 * i)).toNat
  lt : (args (7 + 2 * i)).toNat < 1024
  lt7 : (args 7).toNat < 1024
  pos7 : 1 ≤ (args 7).toNat
  read : InRegions (s.rd ++ s.wr) (byteAddr (args preArg)) (preOff args i + 8 * preW args i)
  fit : (args preArg).toNat + (preOff args i + 8 * preW args i) ≤ 2 ^ 32
  apart : Region.Disjoint ⟨byteAddr (args preArg), preOff args i + 8 * preW args i⟩ ⟨base, bytes⟩
  val : val32 s.mem (byteAddr (args preArg)) (preOff args i) (2 * preW args i) = 2 ^ (128 * preW args i) % p
  top : (s.gpr .esp).toNat + 80 ≤ 2 ^ 32
  apartSp : Region.Disjoint ⟨byteAddr (args preArg), preOff args i + 8 * preW args i⟩ (below (s.gpr .esp) 96)

section
variable {s t : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {i : Nat} {p : Nat}

/-- The cached value holds after a stage that changes registers but `esp`, and memory in regions
apart from argument 18 and from the value. -/
theorem PreR2.keep (P : PreR2 s base bytes len args i p) {regs : List Reg} (K : Keeps regs s t) (sp : .esp ∉ regs)
    {rs : List Region} (F : Frame rs s.mem t.mem)
    (ha : ∀ r ∈ rs, Region.Disjoint ⟨VG.Proof.Dsa.X86.stackAddress s preArg, 4⟩ r)
    (hv : ∀ r ∈ rs, Region.Disjoint ⟨byteAddr (args preArg), preOff args i + 8 * preW args i⟩ r) :
    PreR2 t base bytes len args i p := by
  obtain esp : t.gpr .esp = s.gpr .esp := K.1 _ sp
  have fit := P.fit
  refine ⟨⟨P.arg.stack.keep K sp, ?_⟩, P.hi, P.pos, P.lt, P.lt7, P.pos7, by rw [K.2.1, K.2.2]; exact P.read,
    P.fit, P.apart, ?_, by rw [esp]; exact P.top, by rw [esp]; exact P.apartSp⟩
  · rw [← P.arg.value]
    unfold VG.Proof.Dsa.X86.stackValue
    rw [show VG.Proof.Dsa.X86.stackAddress t preArg = VG.Proof.Dsa.X86.stackAddress s preArg by
      simp only [VG.Proof.Dsa.X86.stackAddress, esp]]
    exact F.readW (r := ⟨VG.Proof.Dsa.X86.stackAddress s preArg, 4⟩) (Region.contains_self _ _) ha (by decide)
  · rw [← P.val, ← VG.Proof.Bignum.read_eq_val32, ← VG.Proof.Bignum.read_eq_val32]
    obtain bA : (byteAddr (args preArg)).toNat = (args preArg).toNat := by
      simp [byteAddr, BitVec.toNat_setWidth]; omega_using []
    obtain hsub : Region.Sub ⟨off (byteAddr (args preArg)) (preOff args i), 4 * (2 * preW args i)⟩
        ⟨byteAddr (args preArg), preOff args i + 8 * preW args i⟩ := by
      have := Offset.sub (byteAddr (args preArg)) (d := preOff args i) (n := 4 * (2 * preW args i)) (e := 0)
        (k := preOff args i + 8 * preW args i) (Nat.zero_le _) (by omega_using [])
      simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
    exact congrArg BitVec.toNat (F.read (Region.contains_self _ _) (fun r hr => (hv r hr).sub_left hsub) (by omega_using [fit]))

/-- Argument 18 is apart from the zone below `esp` that calls write. -/
theorem PreR2.argBelow (P : PreR2 s base bytes len args i p) (room : CallRoom (s.gpr .esp) base bytes) :
    Region.Disjoint ⟨VG.Proof.Dsa.X86.stackAddress s preArg, 4⟩ (below (s.gpr .esp) 96) := by
  have low := room.low
  have top := P.top
  obtain ea : (VG.Proof.Dsa.X86.stackAddress s preArg).toNat = (s.gpr .esp).toNat + (4 + 4 * preArg) := by
    simp only [VG.Proof.Dsa.X86.stackAddress, addr, PublicRt.setWidth_toNat, BitVec.toNat_add, BitVec.toNat_ofNat,
      preArg]
    omega_using [top]
  obtain eb : ((s.gpr .esp - BitVec.ofNat 32 96).setWidth 64).toNat = (s.gpr .esp).toNat - 96 := by
    rw [PublicRt.setWidth_toNat, VG.X86.sub_toNat (by omega_using [low])]
  exact (Region.disjoint_of_le (r₁ := below (s.gpr .esp) 96) (.inl (by dsimp only; rw [eb, ea]; omega_using [low]))
    (by dsimp only; rw [eb]; omega_using []) (by dsimp only; rw [ea]; simp only [preArg]; omega_using [])).symm

/-- Regions within the working space are apart from argument 18 and the value. -/
theorem PreR2.apart_sub (P : PreR2 s base bytes len args i p) {r : Region} (hr : Region.Sub r ⟨base, bytes⟩) :
    Region.Disjoint ⟨VG.Proof.Dsa.X86.stackAddress s preArg, 4⟩ r ∧
      Region.Disjoint ⟨byteAddr (args preArg), preOff args i + 8 * preW args i⟩ r :=
  ⟨P.arg.stack.apart.sub_right hr, P.apart.sub_right hr⟩

/-- The cached value holds after a stage that changes registers but `esp`, and memory in its ranges. -/
theorem PreR2.keepF (P : PreR2 s base bytes len args i p)
    (room : CallRoom (s.gpr .esp) base bytes) {regs : List Reg} (K : Keeps regs s t) (sp : .esp ∉ regs)
    {ws : List (Nat × Nat)} (F : Frame (frameR base (s.gpr .esp) ws) s.mem t.mem)
    (hfit : ∀ q ∈ ws, q.1 + q.2 ≤ bytes) : PreR2 t base bytes len args i p := by
  obtain inW : ∀ q ∈ ws, Region.Sub ⟨off base q.1, q.2⟩ ⟨base, bytes⟩ := fun q hq => by
    have := hfit q hq
    have := Offset.sub base (d := q.1) (n := q.2) (e := 0) (k := bytes) (Nat.zero_le _) (by omega_using [this])
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  refine P.keep K sp F (fun r hr => ?_) (fun r hr => ?_) <;>
    simp only [frameR, List.mem_cons, List.mem_map] at hr <;> rcases hr with rfl | ⟨q, hq, rfl⟩
  · exact P.argBelow room
  · exact (P.apart_sub (inW q hq)).1
  · exact P.apartSp
  · exact (P.apart_sub (inW q hq)).2
/-- The cached value holds after a stage that changes only the working space. -/
theorem PreR2.keepO (P : PreR2 s base bytes len args i p) {regs : List Reg} (K : Keeps regs s t)
    (spn : .esp ∉ regs) (O : Outside base 0 bytes s.mem t.mem) (fit : bytes ≤ 2 ^ 64) :
    PreR2 t base bytes len args i p := by
  have F := VG.Proof.Bignum.outside_frame O (by omega_using [fit])
  simp only [BitVec.add_zero] at F
  exact P.keep K spn F (fun r hr => by rw [List.mem_singleton.mp hr]; exact (P.apart_sub fun _ h => h).1)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact (P.apart_sub fun _ h => h).2)
end

/-- `prepBasePre`'s ranges lie apart from the header words naming the factor. -/
theorem baseR_hdr (len : Nat) (c : Ctx) : ∀ q ∈ baseR len c, 28 ≤ q.1 ∨ q.1 + q.2 ≤ 16 := by
  have nb : numBase = 3336 := rfl
  intro q hq
  simp only [baseR, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inr (by decide)
  all_goals exact .inl (by simp only [lo]; omega_using [nb])

variable {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

/-- The header words naming the current factor `i`: its length at `lenOff`, and the
count of factors left at `leftOff`, odd for factor 1. -/
structure PreHdr (s : State) (base : Addr) (args : Nat → BitVec 32) (i : Nat) : Prop where
  len : w32 s.mem base lenOff = (args (7 + 2 * i)).toNat
  left : w32 s.mem base leftOff % 2 = i

/-- The header words hold after a stage that changes ranges apart from them. -/
theorem PreHdr.keepF {t : State} {i : Nat} (H : PreHdr s base args i) (h : In Ex base bytes len args s)
    {ws : List (Nat × Nat)} (F : Frame (frameR base (s.gpr .esp) ws) s.mem t.mem)
    (hfit : ∀ q ∈ ws, q.1 + q.2 ≤ bytes) (hh : ∀ q ∈ ws, 28 ≤ q.1 ∨ q.1 + q.2 ≤ 16) :
    PreHdr t base args i := by
  obtain f := h.slot_fit .wide (j := 0) (by decide)
  obtain z : lo len (.slot .wide 0) = numBase := sl_zero len .wide
  have nb : numBase = 3336 := rfl
  obtain e : ∀ d, 16 ≤ d → d + 4 ≤ 28 → w32 t.mem base d = w32 s.mem base d := fun d h1 h2 => by
    rw [← w32_val32_one, ← w32_val32_one]
    exact frameR_val32 F h.room h.scratch.nowrap (by omega_using [f, z, nb, h2])
      (fun q hq => by have := hh q hq; omega_using [this, h1, h2]) hfit
  exact ⟨by rw [e lenOff (by decide) (by decide)]; exact H.len, by rw [e leftOff (by decide) (by decide)]; exact H.left⟩

/-- The header words hold after a stage that changes only memory apart from them. -/
theorem PreHdr.keepO {t : State} {i : Nat} (H : PreHdr s base args i) {o n : Nat}
    (O : Outside base o n s.mem t.mem) (ho : 28 ≤ o) : PreHdr t base args i :=
  ⟨by rw [O.w32 (.inl (by simp only [lenOff]; omega_using [ho])) (by decide)]; exact H.len,
    by rw [O.w32 (.inl (by simp only [leftOff]; omega_using [ho])) (by decide)]; exact H.left⟩

/-- `v & ~((x & 1) - 1)`: `v` for `x` odd, zero for `x` even. -/
theorem and_oddMask (v x : BitVec 32) :
    v &&& ((x &&& 1) - 1 ^^^ BitVec.allOnes 32) = if x.toNat % 2 = 0 then 0 else v := by
  obtain e : x &&& 1 = BitVec.ofNat 32 (x.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]
    exact (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))).symm
  rw [e]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h | h <;> rw [h]
  · rw [ite_eq_left rfl, show (BitVec.ofNat 32 0 - 1 ^^^ BitVec.allOnes 32) = 0 by decide]
    simp
  · rw [ite_eq_right (by decide), show (BitVec.ofNat 32 1 - 1 ^^^ BitVec.allOnes 32) = BitVec.allOnes 32 by decide,
      BitVec.and_allOnes]

/-- `loadHead`: slot 4 zeroed, `edx` and `ecx` the bytes of the current factor `i`'s cached value, `esi`
at it, and `ebp` at slot 4. -/
theorem loadHead_ok (h : In Ex base bytes len args s) {i : Nat} {c : Ctx} {p : Nat}
    (P : PreR2 s base bytes len args i p) (H : PreHdr s base args i) (fits : 8 * preW args i ≤ bc len c) :
    WP isa (loadHead c) s fun u => In Ex base bytes len args u ∧
      u.gpr .edx = BitVec.ofNat 32 (8 * preW args i) ∧ u.gpr .ecx = BitVec.ofNat 32 (8 * preW args i) ∧
      PtrAt u (byteAddr (args preArg)) .esi (preOff args i) ∧ PtrAt u base .ebp (lo len (.slot c 4)) ∧
      val32 u.mem base (lo len (.slot c 4)) (cwc len c) = 0 ∧
      Outside base (lo len (.slot c 4)) (bc len c) s.mem u.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .esi] s u := by
  have bl := h.bytes_lt
  obtain f8 := h.slot_fit c (j := 8) (by decide)
  obtain s48 : lo len (.slot c 4) + st len c ≤ lo len (.slot c 8) := sl_le (len := len) c (by decide)
  have est : st len c = 2 * bc len c + 32 := rfl
  obtain hb := bc_le h.upper' c
  obtain cb1 : cb len (one c) = bc len c := by simp [cb, one]
  obtain cw1 : cw len (one c) = cwc len c := by simp [cw, cwc, cb, one]
  have hi := P.hi
  have l7 := P.lt7
  have li := P.lt
  have nb : numBase = 3336 := rfl
  obtain lo4 : numBase ≤ lo len (.slot c 4) := by simp [lo]
  have fitsW : 8 * Spec.Rsa.primeWords (args (7 + 2 * i)).toNat ≤ bc len c := fits
  unfold loadHead
  refine WP.seq (WP.mono (zero_ok h (x := .slot c 4) (one_ok c) (by rw [cb1]; omega_using [f8, s48, est]))
    fun u₁ ⟨O₁, Z₁, K₁⟩ => ?_)
  rw [cb1] at O₁
  rw [cw1] at Z₁
  obtain h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega_using [f8, s48, est]))
  obtain A₁ := P.arg.keep K₁ (by decide) (O₁.mono (Nat.zero_le _) (by omega_using [f8, s48, est]))
  obtain H₁ := H.keepO O₁ (by omega_using [lo4, nb])
  -- `edx`: the first factor's bytes.
  refine wp_movS (h₁.arg (i := 7) (by decide)) fun u₂ U₂ _ => ?_
  refine primeBytes_ok (r := .edx) (t := .eax) (by decide) (l := (args 7).toNat)
    (by rw [U₂.gpr, BitVec.ofNat_toNat, BitVec.setWidth_eq]) P.pos7 (by omega_using [l7]) fun u₃ K₃ m₃ e₃ => ?_
  obtain K₃' : Keeps [.eax, .edx] u₁ u₃ := (U₂.keeps.mono (by decide)).trans (K₃.mono (by decide))
  obtain m₃' : u₃.mem = u₁.mem := by rw [m₃, U₂.mem]
  obtain h₃ := h₁.regs K₃' m₃'
  -- `eax`: all ones for factor 1, zero for factor 0; `edx` masked by it.
  refine wp_movS (readSrc_sc h₃.scratch (d := leftOff) (by simp only [leftOff]; omega_using [lo4, nb, f8, s48, est]))
    fun u₄ U₄ _ => ?_
  refine wp_logicS (.inl rfl) rfl fun u₅ U₅ => wp_subS rfl fun u₆ U₆ _ => wp_logicS (.inr rfl) rfl fun u₇ U₇ => ?_
  refine wp_logicS (.inl rfl) rfl fun u₈ U₈ => ?_
  obtain edx₈ : u₈.gpr .edx = BitVec.ofNat 32 (preOff args i) := by
    rw [U₈.gpr, ite_eq_left rfl, U₇.gpr, ite_eq_right (by decide), U₇.other _ (by decide), U₆.gpr, U₆.other _ (by decide),
      U₅.gpr, ite_eq_left rfl, U₅.other _ (by decide), U₄.gpr, U₄.other _ (by decide), e₃, and_oddMask]
    obtain hL : (u₃.mem.readW (off base leftOff) 32).toNat % 2 = i := by
      show w32 u₃.mem base leftOff % 2 = i
      rw [m₃']; exact H₁.left
    rw [hL]
    rcases (show i = 0 ∨ i = 1 by omega_using [hi]) with rfl | rfl
    · rfl
    · simp only [preOff, show (1 : Nat) ≠ 0 from by decide, ite_false]
  obtain K₈ : Keeps [.eax, .edx] u₃ u₈ := ((U₄.keeps.mono (by decide)).trans (U₅.keeps.mono (by decide))).trans
    ((U₆.keeps.mono (by decide)).trans ((U₇.keeps.mono (by decide)).trans (U₈.keeps.mono (by decide))))
  obtain m₈ : u₈.mem = u₁.mem := by rw [U₈.mem, U₇.mem, U₆.mem, U₅.mem, U₄.mem, m₃']
  obtain A₈ := A₁.keep (K₃'.trans K₈) (by simp) (by rw [m₈]; exact Outside.refl _ _ _ _)
  -- `esi` at factor `i`'s value.
  refine wp_movS A₈.readSrc fun u₉ U₉ _ => wp_addS rfl fun u₁₀ U₁₀ _ => ?_
  obtain bA : (byteAddr (args preArg)).toNat = (args preArg).toNat := by
    simp [byteAddr, BitVec.toNat_setWidth]; omega_using []
  obtain po : preOff args i < 2 ^ 32 := by
    simp only [preOff]; split
    · decide
    · simp only [Spec.Rsa.primeWords, Spec.Rsa.modulusWords]; omega_using [l7]
  obtain esi₁₀ : PtrAt u₁₀ (byteAddr (args preArg)) .esi (preOff args i) := by
    rw [PtrAt, U₁₀.gpr, BitVec.toNat_add, U₉.gpr, U₉.other _ (by decide), edx₈, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := preOff args i) po, bA]
  obtain K₁₀ : Keeps [.eax, .edx, .esi] u₁ u₁₀ :=
    ((K₃'.trans K₈).mono (by decide)).trans ((U₉.keeps.mono (by decide)).trans (U₁₀.keeps.mono (by decide)))
  obtain m₁₀ : u₁₀.mem = u₁.mem := by rw [U₁₀.mem, U₉.mem, m₈]
  obtain h₁₀ := h₁.regs K₁₀ m₁₀
  -- `edx` and `ecx` the bytes of factor `i`'s value, from its length.
  refine wp_movS (readSrc_sc h₁₀.scratch (d := lenOff) (by simp only [lenOff]; omega_using [lo4, nb, f8, s48, est]))
    fun u₁₁ U₁₁ _ => ?_
  refine primeBytes_ok (r := .edx) (t := .eax) (by decide) (l := (args (7 + 2 * i)).toNat) ?_ P.pos
    (by omega_using [li]) fun u₁₂ K₁₂ m₁₂ e₁₂ => ?_
  · apply BitVec.eq_of_toNat_eq
    rw [U₁₁.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [li])]
    show w32 u₁₀.mem base lenOff = _
    rw [m₁₀]; exact H₁.len
  refine wp_movS rfl fun u₁₃ U₁₃ _ => ?_
  obtain K₁₃ : Keeps [.eax, .ecx, .edx, .esi] u₁ u₁₃ := (K₁₀.mono (by decide)).trans
    (((U₁₁.keeps.mono (by decide)).trans (K₁₂.mono (by decide))).trans (U₁₃.keeps.mono (by decide)))
  obtain m₁₃ : u₁₃.mem = u₁.mem := by rw [U₁₃.mem, m₁₂, U₁₁.mem, m₁₀]
  obtain h₁₃ := h₁.regs K₁₃ m₁₃
  rw [← List.append_nil (ptrTo (.slot c 4) .ebp .eax)]
  refine ptrTo_ok (r := .ebp) (t := .eax) (by decide) (by decide) h₁₃.edi h₁₃.width h.upper'
    (by omega_using [bl, f8, s48]) fun w Kw mw pw => WP.block_nil ?_
  obtain mw₁ : w.mem = u₁.mem := by rw [mw, m₁₃]
  obtain edx₁₃ : u₁₃.gpr .edx = BitVec.ofNat 32 (8 * preW args i) := by rw [U₁₃.other _ (by decide), e₁₂]
  refine ⟨h₁₃.regs Kw mw, by rw [Kw.1 _ (by decide)]; exact edx₁₃, by rw [Kw.1 _ (by decide), U₁₃.gpr]; exact e₁₂,
    ?_, pw, by rw [mw₁]; exact Z₁, by rw [mw₁]; exact O₁, ?_⟩
  · rw [PtrAt, Kw.1 _ (by decide), U₁₃.other _ (by decide), K₁₂.1 _ (by decide), U₁₁.other _ (by decide)]
    exact esi₁₀
  · exact (K₁.mono (by decide)).trans ((K₁₃.mono (by decide)).trans (Kw.mono (by decide)))

/-- `loadTail`: the current factor `i`'s cached value copied into slot 4 (zero above it), and `esi` its
doublings to the context's radix. -/
theorem loadTail_ok (h : In Ex base bytes len args s) {i : Nat} {c : Ctx} {p : Nat}
    (P : PreR2 s base bytes len args i p) (fits : 8 * preW args i ≤ bc len c)
    (edx : s.gpr .edx = BitVec.ofNat 32 (8 * preW args i)) (ecx : s.gpr .ecx = BitVec.ofNat 32 (8 * preW args i))
    (esi : PtrAt s (byteAddr (args preArg)) .esi (preOff args i)) (ebp : PtrAt s base .ebp (lo len (.slot c 4)))
    (Z : val32 s.mem base (lo len (.slot c 4)) (cwc len c) = 0) :
    WP isa (loadTail c) s fun u => In Ex base bytes len args u ∧
      sv u.mem base len c 4 = 2 ^ (128 * preW args i) % p ∧
      (u.gpr .esi).toNat = 16 * (bc len c - 8 * preW args i) ∧
      u.zf = some (u.gpr .esi == 0) ∧
      Outside base (lo len (.slot c 4)) (bc len c) s.mem u.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .esi] s u := by
  have nw' := h.scratch.nowrap
  have bl := h.bytes_lt
  obtain f8 := h.slot_fit c (j := 8) (by decide)
  obtain s48 : lo len (.slot c 4) + st len c ≤ lo len (.slot c 8) := sl_le (len := len) c (by decide)
  have est : st len c = 2 * bc len c + 32 := rfl
  obtain bw := bc_eq_cwc len c
  obtain hb := bc_le h.upper' c
  obtain pw2 : 2 ≤ preW args i := by simp only [preW, Spec.Rsa.primeWords]; omega_using []
  have fitsW : 8 * Spec.Rsa.primeWords (args (7 + 2 * i)).toNat ≤ bc len c := fits
  obtain pwE : preW args i = Spec.Rsa.primeWords (args (7 + 2 * i)).toNat := rfl
  obtain bA : (byteAddr (args preArg)).toNat = (args preArg).toNat := by
    simp [byteAddr, BitVec.toNat_setWidth]; omega_using []
  unfold loadTail
  -- The copy.
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86.PrecomputedRt.copyLoop_ok (N := 2 * preW args i)
    (x := lo len (.slot c 4)) (y := preOff args i) h.ws P.read
    (by rw [bA]; exact P.fit) P.apart (by omega_using [pw2, pwE]) (by omega_using [fits, fitsW, pwE, f8, s48, est]) (by omega_using [])
    ebp esi (by rw [ecx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [fits, fitsW, pwE, hb])]; omega_using []))
    fun t₁ ⟨Ot, Vt, Kt⟩ => ?_)
  obtain Ot₀ : Outside base 0 bytes s.mem t₁.mem := Ot.mono (Nat.zero_le _) (by omega_using [fits, fitsW, pwE, f8, s48, est])
  obtain ht₁ := h.keep Kt (by decide) (by decide) Ot₀
  refine widthC_ok ht₁.width h.upper' fun t₄ K₄' m₄' e₄' => ?_
  refine wp_subS rfl fun t₅ T₅ _ => wp_addS rfl fun t₆ T₆ _ => wp_addS rfl fun t₇ T₇ _ =>
    wp_addS rfl fun t₈ T₈ _ => wp_addZ rfl fun u U z => WP.block_nil ?_
  obtain Ku : Keeps [.esi] t₁ u := (K₄'.mono (by decide)).trans ((((T₅.keeps.mono (by decide)).trans
    (T₆.keeps.mono (by decide))).trans ((T₇.keeps.mono (by decide)).trans (T₈.keeps.mono (by decide)))).trans
    (U.keeps.mono (by decide)))
  obtain mu : u.mem = t₁.mem := by rw [U.mem, T₈.mem, T₇.mem, T₆.mem, T₅.mem, m₄']
  -- The count.
  obtain hd : (t₄.gpr .edx).toNat = 8 * preW args i := by
    rw [K₄'.1 _ (by decide), Kt.1 _ (by decide), edx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hb, fitsW, pwE])]
  obtain h5 : (t₅.gpr .esi).toNat = bc len c - 8 * preW args i := by
    rw [T₅.gpr, BitVec.toNat_sub, hd, e₄', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := bc len c) (by omega_using [hb])]
    omega_using [fits, fitsW, pwE, hb]
  obtain h8 : (t₈.gpr .esi).toNat = 8 * (bc len c - 8 * preW args i) := by
    rw [T₈.gpr, BitVec.toNat_add, T₇.gpr, BitVec.toNat_add, T₆.gpr, BitVec.toNat_add, h5]; omega_using [hb]
  refine ⟨ht₁.regs Ku mu, ?_, ?_, ?_, by rw [mu]; exact Ot.mono (Nat.le_refl _) (by omega_using [fits, fitsW, pwE]), (Kt.mono (by decide)).trans (Ku.mono (by decide))⟩
  · -- The value: the copy, and zero above it.
    obtain tail : val32 t₁.mem base (lo len (.slot c 4) + 4 * (2 * preW args i)) (cwc len c - 2 * preW args i) = 0 := by
      rw [Ot.val32 (.inr (Nat.le_refl _)) (by omega_using [fits, nw', bl, f8, s48, est, bw, hb, pw2, fitsW, pwE])]
      have Zs := Z
      rw [show cwc len c = 2 * preW args i + (cwc len c - 2 * preW args i) by omega_using [fits, fitsW, pwE, bw], val32_append] at Zs
      simp only [Nat.add_eq_zero_iff, Nat.mul_eq_zero, Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _), false_or] at Zs
      exact Zs.2
    simp only [sv]
    rw [mu, show cwc len c = 2 * preW args i + (cwc len c - 2 * preW args i) by omega_using [fits, fitsW, pwE, bw], val32_append, tail,
      Nat.mul_zero, Nat.add_zero, Vt, P.val]
  · rw [U.gpr, BitVec.toNat_add, h8]; omega_using [hb]
  · rw [z, U.gpr]

/-- `preparePre`: what `prepare` leaves (`prepCtx_ok`), from factor `i`'s cached `R_pre² mod M`
doubled to the context's radix. -/
theorem preparePre_ok (h : In Ex base bytes len args s) {i : Nat} {c : Ctx}
    (P : PreR2 s base bytes len args i (safeM (sv s.mem base len c 0))) (H : PreHdr s base args i)
    (fits : 8 * preW args i ≤ bc len c) :
    WP isa (preparePre c) s fun u =>
      CtxOk Ex base bytes len args c (safeM (sv s.mem base len c 0)) u ∧ sv u.mem base len c 3 = 1 ∧
      sv u.mem base len c 4 = 2 ^ (16 * bc len c) % safeM (sv s.mem base len c 0) ∧
      Frame (frameR base (s.gpr .esp) (prepR len c)) s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have nw := h.scratch.nowrap
  obtain fit := prepR_fit2 h c
  obtain f8 := h.slot_fit c (j := 8) (by decide)
  obtain bw := bc_eq_cwc len c
  have est : st len c = 2 * bc len c + 32 := rfl
  obtain s01 : lo len (.slot c 0) + st len c ≤ lo len (.slot c 1) := sl_le (len := len) c (by decide)
  obtain s13 : lo len (.slot c 1) + st len c ≤ lo len (.slot c 3) := sl_le (len := len) c (by decide)
  obtain s34 : lo len (.slot c 3) + st len c ≤ lo len (.slot c 4) := sl_le (len := len) c (by decide)
  obtain s48 : lo len (.slot c 4) + st len c ≤ lo len (.slot c 8) := sl_le (len := len) c (by decide)
  obtain z0 : lo len (.slot c 0) = numBase := sl_zero len c
  have nb : numBase = 3336 := rfl
  have io : invOff = 0 := rfl
  obtain fitW : ∀ p ∈ powR len c, p.1 + p.2 ≤ bytes := by
    intro p hp
    simp only [powR, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> dsimp only <;> omega_arith
  obtain hws : ∀ {d k : Nat}, d + 4 * k ≤ lo len (.slot c 1) ∨ lo len (.slot c 1) + (bc len c + 4) ≤ d →
      d + 4 * k ≤ lo len (.slot c 4) ∨ lo len (.slot c 4) + bc len c ≤ d →
      ∀ q ∈ powR len c, d + 4 * k ≤ q.1 ∨ q.1 + q.2 ≤ d := by
    intro d k hd hd' q hq
    simp only [powR, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> dsimp only <;> omega_arith
  unfold preparePre
  refine WP.seq (WP.mono (prepBasePre_ok h c) fun u₈ ⟨h₈, F₈, M₈, one₈, I₈, K₈⟩ => ?_)
  obtain P₈ := P.keepF h.room K₈ (by decide) F₈ fit.2
  obtain H₈ := H.keepF h F₈ fit.2 (baseR_hdr len c)
  obtain sp₈ : u₈.gpr .esp = s.gpr .esp := K₈.1 _ (by decide)
  -- What `prepBasePre` leaves stays: the rest changes only slots 1 and 4.
  obtain rest : ∀ t : State, Frame (frameR base (s.gpr .esp) (powR len c)) u₈.mem t.mem →
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] u₈ t →
      sv t.mem base len c 4 = 2 ^ (16 * bc len c) % safeM (sv s.mem base len c 0) →
      CtxOk Ex base bytes len args c (safeM (sv s.mem base len c 0)) t ∧ sv t.mem base len c 3 = 1 ∧
      sv t.mem base len c 4 = 2 ^ (16 * bc len c) % safeM (sv s.mem base len c 0) ∧
      Frame (frameR base (s.gpr .esp) (prepR len c)) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
    intro t Ft Kt Vt
    obtain W : Frame (frameR base (s.gpr .esp) (prepR len c)) s.mem t.mem := by
      refine (frameR_widen F₈ fun p hp => ?_).trans (frameR_widen Ft fun p hp => ?_)
      · simp only [baseR, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨(invOff, 4), by simp, Nat.le_refl _, Nat.le_refl _⟩
        · exact ⟨(lo len (.slot c 0), bc len c), by simp, Nat.le_refl _, Nat.le_refl _⟩
        · exact ⟨(lo len (.slot c 1), 3 * bc len c + 56), by simp, Nat.le_refl _, by dsimp only; omega_using []⟩
        · exact ⟨(lo len (.slot c 3), bc len c), by simp, Nat.le_refl _, Nat.le_refl _⟩
        · exact ⟨(lo len (.slot c 4), bc len c), by simp, Nat.le_refl _, Nat.le_refl _⟩
        · exact ⟨(lo len (.slot c 7), bc len c), by simp, Nat.le_refl _, Nat.le_refl _⟩
      · simp only [powR, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact ⟨(lo len (.slot c 1), 3 * bc len c + 56), by simp, Nat.le_refl _, by dsimp only; omega_using []⟩
        · exact ⟨(lo len (.slot c 4), bc len c), by simp, Nat.le_refl _, Nat.le_refl _⟩
    obtain K : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := K₈.trans Kt
    obtain v0 : val32 t.mem base (lo len (.slot c 0)) (cwc len c) = val32 u₈.mem base (lo len (.slot c 0)) (cwc len c) :=
      frameR_val32 Ft h.room nw (by omega_arith) (hws (.inl (by omega_arith)) (.inl (by omega_arith))) fitW
    obtain v3 : val32 t.mem base (lo len (.slot c 3)) (cwc len c) = val32 u₈.mem base (lo len (.slot c 3)) (cwc len c) :=
      frameR_val32 Ft h.room nw (by omega_arith) (hws (.inr (by omega_arith)) (.inl (by omega_arith))) fitW
    obtain vi : val32 t.mem base invOff 1 = val32 u₈.mem base invOff 1 :=
      frameR_val32 Ft h.room nw (by omega_arith) (hws (.inl (by omega_arith)) (.inl (by omega_arith))) fitW
    simp only [sv] at M₈ one₈ Vt ⊢
    rw [w32_val32_one] at vi
    rw [w32_val32_one] at vi
    refine ⟨⟨h.keepF K (by decide) (by decide) W fit.1, by simp only [sv]; rw [v0, M₈], safeM_gt _, safeM_odd _, ?_⟩,
      by rw [v3, one₈], Vt, W, K⟩
    rw [vi]; exact I₈
  obtain keep0 : ∀ t : State, Frame (frameR base (s.gpr .esp) (powR len c)) u₈.mem t.mem →
      sv t.mem base len c 0 = safeM (sv s.mem base len c 0) := fun t Ft => by
    simp only [sv] at M₈ ⊢
    rw [frameR_val32 Ft h.room nw (by omega_arith) (hws (.inl (by omega_arith)) (.inl (by omega_arith))) fitW, M₈]
  refine WP.seq (WP.mono (loadHead_ok h₈ P₈ H₈ fits) fun u₇ ⟨h₇, edx₇, ecx₇, esi₇, ebp₇, Z₇, O₇, K₇⟩ => ?_)
  obtain P₇ := P₈.keepO K₇ (by decide) (O₇.mono (Nat.zero_le _) (by omega_arith)) (by omega_arith)
  refine WP.seq (WP.mono (loadTail_ok h₇ P₇ fits edx₇ ecx₇ esi₇ ebp₇ Z₇) fun u₉ ⟨h₉, V₉, esi₉, z₉, O₉', K₉'⟩ => ?_)
  obtain O₉ : Outside base (lo len (.slot c 4)) (bc len c) u₈.mem u₉.mem := O₇.trans O₉'
  obtain K₉ : Keeps [.eax, .ecx, .edx, .ebp, .esi] u₈ u₉ := K₇.trans K₉'
  obtain sp₉ : u₉.gpr .esp = s.gpr .esp := by rw [K₉.1 _ (by decide), sp₈]
  obtain F₉ : Frame (frameR base (s.gpr .esp) (powR len c)) u₈.mem u₉.mem :=
    frameR_of_outside O₉ (by omega_arith) (by simp [powR])
  obtain K₉' : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] u₈ u₉ := K₉.mono (by decide)
  refine WP.ite (u₉.gpr .esi == 0) z₉ (fun hz => WP.block_nil ?_) (fun hz => ?_)
  · have e : (u₉.gpr .esi).toNat = 0 := by rw [beq_iff_eq.mp hz]; rfl
    refine rest u₉ F₉ K₉' ?_
    rw [V₉, show 16 * bc len c = 128 * preW args i by omega_using [fits, esi₉, e]]
  · have hN : 0 < 16 * (bc len c - 8 * preW args i) := by
      rw [← esi₉]
      refine Nat.pos_of_ne_zero fun e => ?_
      have : u₉.gpr .esi = 0 := BitVec.eq_of_toNat_eq (by rw [e]; rfl)
      simp [this] at hz
    let M := safeM (sv s.mem base len c 0)
    obtain hM : 0 < M := Nat.lt_trans Nat.zero_lt_one (safeM_gt _)
    let I : Nat → State → Prop := fun j t =>
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] u₉ t ∧
        Frame (frameR base (s.gpr .esp) (powR len c)) u₉.mem t.mem ∧
        sv t.mem base len c 4 = 2 ^ (128 * preW args i + j) % M ∧
        (t.gpr .esi).toNat = 16 * (bc len c - 8 * preW args i) - j
    refine WP.mono (countLoop hN I ?_ ⟨Keeps.refl _ _, Frame.refl _ _, V₉, esi₉⟩) fun t ⟨Kt, Ft, Vt, _⟩ => ?_
    · rintro j t hj ⟨Kt, Ft, Vt, esit⟩
      obtain ht := h₉.keepF Kt (by decide) (by decide) (by rw [sp₉]; exact Ft) fitW
      obtain Mt : sv t.mem base len c 0 = M := keep0 t (F₉.trans Ft)
      refine WP.mono (doubleStep_ok ht c (by rw [Vt, Mt]; exact Nat.mod_lt _ hM)) fun u ⟨Fu, Vu, esiu, zu, Ku⟩ => ?_
      obtain ⟨c₁, c₂⟩ := count1_zf esit hj
      obtain spt : t.gpr .esp = s.gpr .esp := by rw [Kt.1 _ (by decide), sp₉]
      refine ⟨⟨Kt.trans Ku, Ft.trans (by rw [← spt]; exact Fu), ?_, by rw [esiu]; exact c₁⟩, by rw [zu, c₂]⟩
      rw [Vu, Vt, Mt, ← Nat.add_mod, ← Nat.two_mul, Nat.mul_comm, ← Nat.pow_succ]; rfl
    · refine rest t (F₉.trans Ft) (K₉'.trans Kt) ?_
      rw [Vt, show 128 * preW args i + 16 * (bc len c - 8 * preW args i) = 16 * bc len c by omega_using [fits]]

/-- With `some i`, factor `i`'s cached value (`PreR2`) and the header words naming it (`PreHdr`);
with `none`, nothing. -/
def PreG (s : State) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) : Option Nat → Nat → Prop
  | none, _ => True
  | some i, p => PreR2 s base bytes len args i p ∧ PreHdr s base args i

/-- With `some i`, factor `i`'s cached value fits the context `c`. -/
def FitG (len : Nat) (args : Nat → BitVec 32) : Option Nat → Ctx → Prop
  | none, _ => True
  | some i, c => 8 * preW args i ≤ bc len c

theorem PreG.keepF {t : State} {p : Nat} {pc : Option Nat} (P : PreG s base bytes len args pc p)
    (h : In Ex base bytes len args s) {regs : List Reg} (K : Keeps regs s t) (sp : .esp ∉ regs) {ws : List (Nat × Nat)}
    (F : Frame (frameR base (s.gpr .esp) ws) s.mem t.mem) (hfit : ∀ q ∈ ws, q.1 + q.2 ≤ bytes)
    (hh : ∀ q ∈ ws, 28 ≤ q.1 ∨ q.1 + q.2 ≤ 16) :
    PreG t base bytes len args pc p := by
  cases pc with
  | none => trivial
  | some i => exact ⟨PreR2.keepF P.1 h.room K sp F hfit, P.2.keepF h F hfit hh⟩

/-- `prepareG`: what `prepare` leaves (`prepCtx_ok`), either way. -/
theorem prepareG_ok (h : In Ex base bytes len args s) (c : Ctx) {pc : Option Nat}
    (P : PreG s base bytes len args pc (safeM (sv s.mem base len c 0))) (fits : FitG len args pc c) :
    WP isa (prepareG pc.isSome c) s fun u =>
      CtxOk Ex base bytes len args c (safeM (sv s.mem base len c 0)) u ∧ sv u.mem base len c 3 = 1 ∧
      sv u.mem base len c 4 = 2 ^ (16 * bc len c) % safeM (sv s.mem base len c 0) ∧
      Frame (frameR base (s.gpr .esp) (prepR len c)) s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  cases pc with
  | none => exact prepCtx_ok h c
  | some i => exact preparePre_ok h P.1 P.2 fits

/-- A factor's cached value fits a context its length fits. -/
theorem fitG_of {i : Nat} {c : Ctx} (hl : 64 ≤ len) (h : (args (7 + 2 * i)).toNat ≤ bc len c) :
    FitG len args (some i) c := by
  have := bc_ge hl c
  have := bc_dvd len c
  show 8 * Spec.Rsa.primeWords _ ≤ _
  simp only [Spec.Rsa.primeWords, Spec.Rsa.modulusWords]
  omega_arith

end

end VG.Proof.Bignum.X86.CrtRt

/-! ## The ranges a factor's power changes

`stR len o`: the header's first two words, the first nine wide slots (both
contexts' slots), the table, and the result's wide slot `o`. Every range a
step of a power changes lies within one of them (`stR_widen`), and they
keep the key's components in the wide slots 9 to 15 and the other result
(`stR_keep`).
-/


namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86

/-- The ranges a factor's power into the wide slot `o` changes. -/
abbrev stR (len o : Nat) : List (Nat × Nat) :=
  [(0, 8), (numBase, 9 * st len .wide), (te len .wide 0, 16 * bc len .wide),
    (lo len (.slot .wide o), 2 * bc len .wide)]

/-- A range within another. -/
abbrev Within (p q : Nat × Nat) : Prop := q.1 ≤ p.1 ∧ p.1 + p.2 ≤ q.1 + q.2

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

/-- A context's slots 0 to 8 lie within the first nine wide slots. -/
theorem ctx_in (h : In Ex base bytes len args s) (c : Ctx) {j : Nat} (hj : j ≤ 8) :
    numBase ≤ lo len (.slot c j) ∧ lo len (.slot c j) + st len c ≤ numBase + 9 * st len .wide := by
  have e : lo len (.slot c j) = numBase + j * st len c := rfl
  refine ⟨by omega_using [e], ?_⟩
  cases c with
  | half =>
    have := half_in_wide h hj
    have e9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide := rfl
    omega_using [this, e9]
  | wide =>
    have := Nat.mul_le_mul_right (st len .wide) hj
    have e' : lo len (.slot .wide j) = numBase + j * st len .wide := rfl
    omega_using [e, this]

theorem bc_le_wide (len : Nat) (c : Ctx) : bc len c ≤ bc len .wide := by
  obtain hb := bc_half_le' len
  have := bc_dvd len .half
  cases c <;> omega_arith

/-- The context's ranges from its slot 1 on, within the first nine wide slots. -/
theorem slot1_in (h : In Ex base bytes len args s) (c : Ctx) :
    Within (lo len (.slot c 1), 3 * bc len c + 56) (numBase, 9 * st len .wide) := by
  obtain a := ctx_in h c (j := 1) (by decide)
  obtain b := ctx_in h c (j := 2) (by decide)
  obtain e1 : lo len (.slot c 1) = numBase + st len c := by simp [lo]
  have e2 : lo len (.slot c 2) = numBase + 2 * st len c := rfl
  have est : st len c = 2 * bc len c + 32 := rfl
  exact ⟨a.1, by dsimp only; omega_using [b, e1, e2, est]⟩

theorem slot_in (h : In Ex base bytes len args s) (c : Ctx) {j : Nat} (hj : j ≤ 8) :
    Within (lo len (.slot c j), bc len c) (numBase, 9 * st len .wide) := by
  obtain a := ctx_in h c hj
  have est : st len c = 2 * bc len c + 32 := rfl
  exact ⟨a.1, by dsimp only; omega_using [a, est]⟩

theorem table_in (c : Ctx) (len : Nat) :
    Within (te len c 0, 16 * bc len c) (te len .wide 0, 16 * bc len .wide) := by
  have := bc_le_wide len c
  obtain e : te len c 0 = te len .wide 0 := by simp [te]
  exact ⟨by rw [e], by dsimp only; rw [e]; omega_using [this]⟩

/-- Every range of `ws` within one of `stR`. -/
abbrev InSt (len o : Nat) (ws : List (Nat × Nat)) : Prop := ∀ p ∈ ws, ∃ q ∈ stR len o, Within p q

theorem stR_widen {sp : BitVec 32} {o : Nat} {ws : List (Nat × Nat)} {m m' : Mem}
    (F : Frame (frameR base sp ws) m m') (hw : InSt len o ws) : Frame (frameR base sp (stR len o)) m m' :=
  frameR_widen F hw

theorem prepR_in (h : In Ex base bytes len args s) (c : Ctx) (o : Nat) : InSt len o (prepR len c) := by
  intro p hp
  simp only [prepR, List.mem_cons, List.not_mem_nil, or_false] at hp
  obtain s1 := slot1_in h c
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨(0, 8), by simp, by simp only [invOff]; omega_using [], by simp only [invOff]; omega_using []⟩
  · exact ⟨_, by simp, slot_in h c (by decide)⟩
  · exact ⟨_, by simp, s1.1, by have := s1.2; dsimp only at *; have := bc_ge h.lower' c; omega_arith⟩
  · exact ⟨_, by simp, slot_in h c (by decide)⟩
  · exact ⟨_, by simp, slot_in h c (by decide)⟩
  · exact ⟨_, by simp, slot_in h c (by decide)⟩

theorem mulR_in (h : In Ex base bytes len args s) (c : Ctx) {j : Nat} (hj : j ≤ 8) (o : Nat) :
    InSt len o (mulR len c j) := by
  intro p hp
  simp only [mulR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨_, by simp, slot_in h c hj⟩
  · exact ⟨_, by simp, slot1_in h c⟩

theorem pwR_in (h : In Ex base bytes len args s) (c : Ctx) (o : Nat) : InSt len o (pwR len c) := by
  intro p hp
  simp only [pwR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨(0, 8), by simp, by simp only [winOff]; omega_using [], by simp only [winOff]; omega_using []⟩
  · exact ⟨_, by simp, slot1_in h c⟩
  · exact ⟨_, by simp, slot_in h c (by decide)⟩
  · exact ⟨_, by simp, slot_in h c (by decide)⟩
  · exact ⟨_, by simp, slot_in h c (by decide)⟩
  · exact ⟨_, by simp, slot_in h c (by decide)⟩
  · exact ⟨_, by simp, table_in c len⟩

/-- A power's ranges lie apart from the header words naming the factor. -/
theorem stR_hdr (len o : Nat) : ∀ q ∈ stR len o, 28 ≤ q.1 ∨ q.1 + q.2 ≤ 16 := by
  have nb : numBase = 3336 := rfl
  obtain t0 : te len .wide 0 = lo len (.slot .wide 20) := by simp [te]
  intro q hq
  simp only [stR, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact .inr (by decide)
  · exact .inl (by simp only [nb]; decide)
  · exact .inl (by rw [t0]; simp only [lo]; omega_using [nb])
  · exact .inl (by simp only [lo]; omega_using [nb])

theorem stR_fit (h : In Ex base bytes len args s) {o : Nat} (ho : o ≤ 19) :
    ∀ q ∈ stR len o, q.1 + q.2 ≤ bytes := by
  obtain T := h.table_fit .wide
  obtain W := h.wide_fit ho
  obtain f8 := h.slot_fit .wide (j := 8) (by decide)
  have e8 : lo len (.slot .wide 8) = numBase + 8 * st len .wide := rfl
  have nb : numBase = 3336 := rfl
  obtain t16 : te len .wide 16 = te len .wide 0 + 16 * bc len .wide := by simp only [te]; omega_using []
  intro q hq
  simp only [stR, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith

/-- A change within one range of `stR`. -/
theorem stR_of_outside (h : In Ex base bytes len args s) {sp : BitVec 32} {o a n : Nat} (ho : o ≤ 19) {m m' : Mem}
    (O : Outside base a n m m') (hq : ∃ q ∈ stR len o, Within (a, n) q) :
    Frame (frameR base sp (stR len o)) m m' := by
  obtain ⟨q, hq, w⟩ := hq
  have := stR_fit h ho q hq
  have bl := h.bytes_lt
  have w2 : a + n ≤ q.1 + q.2 := w.2
  refine stR_widen (ws := [(a, n)]) (frameR_of_outside O (by omega_using [this, bl, w2]) (by simp)) ?_
  intro p hp
  rw [List.mem_singleton.mp hp]
  exact ⟨q, hq, w⟩

/-- A power keeps the key's components and the other result: everything from wide slot 9 on but
the result's slot and the table. -/
theorem stR_keep (h : In Ex base bytes len args s) {sp : BitVec 32} {o : Nat} (ho16 : 16 ≤ o) (ho : o ≤ 17)
    {m m' : Mem} (F : Frame (frameR base sp (stR len o)) m m') (R : CallRoom sp base bytes) {d k : Nat}
    (hd : lo len (.slot .wide 9) ≤ d) (hk : d + 4 * k ≤ lo len (.slot .wide 18))
    (hdo : d + 4 * k ≤ lo len (.slot .wide o) ∨ lo len (.slot .wide o) + 2 * bc len .wide ≤ d) :
    val32 m' base d k = val32 m base d k := by
  obtain W := h.wide_fit (j := 18) (by decide)
  obtain T := h.table_fit .wide
  have e9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide := rfl
  have e18 : lo len (.slot .wide 18) = numBase + 18 * st len .wide := rfl
  have e20 : lo len (.slot .wide 20) = numBase + 20 * st len .wide := rfl
  obtain t0 : te len .wide 0 = lo len (.slot .wide 20) := by simp [te]
  obtain W19 := h.wide_fit (j := 19) (by decide)
  have e19 : lo len (.slot .wide 19) = numBase + 19 * st len .wide := rfl
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  refine frameR_val32 F R h.scratch.nowrap (by omega) ?_ (stR_fit h (by omega))
  intro q hq
  simp only [stR, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> (try dsimp only)
  · have nb : numBase = 3336 := rfl
    omega
  · omega
  · omega
  · exact hdo

end

end VG.Proof.Bignum.X86.CrtRt
