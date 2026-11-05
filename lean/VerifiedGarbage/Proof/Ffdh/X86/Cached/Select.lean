module

public import VerifiedGarbage.Proof.Ffdh.X86.Cached.Digit
import VerifiedGarbage.Proof.Mont.X86.WindowSelect
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Num
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.MulOk
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Ffdh.X86.Stages
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
public import VerifiedGarbage.Proof.Mont.X86.Csub
public import VerifiedGarbage.Impl.Bignum.X86.CrtRt
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops2

/-!
# FFDH key generation from the context on i686: the digit's entry

`select_ok`: slot 7 the context's entry of the digit in the window word, by
scanning all 32 entries under an equality mask, each copied by
`selectLoop_far_ok`; the context's rows, at `ctx + 24 + B j` (`rowAt_ok`),
are read only.
-/

@[expose] public section

/-!
# FFDH's key-generation context on i686: copying its rows

A row of the context and a slot of the working space are copied, either way,
by `selectLoop` under a mask (`selectLoop_far_ok`): the source is any
readable span, apart from the destination, a span of a writable region.
-/

namespace VG.Proof.Ffdh.X86.Cached

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Bignum.X86.PublicRt (countLoop ptr4)

/-- Memory changed only in `[d, d + n)` of `D` is framed by that span. -/
theorem Outside.frame_span {D : Addr} {d n : Nat} {m m' : Mem} (h : Outside D d n m m')
    (hn : D.toNat + d + n ≤ 2 ^ 64) : Frame [⟨off D d, n⟩] m m' := by
  intro x hx
  have hc := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at hc
  refine h x (Classical.byContradiction fun hne => hc ?_)
  have h₁ : d ≤ ofs D x := by omega
  have h₂ : ofs D x < d + n := by omega
  have e : (x - off D d).toNat = ofs D x - d := by
    simp only [ofs, off]
    rw [← BitVec.sub_sub]
    rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact h₁
  omega

/-- A word read apart from a span that changed. -/
theorem Outside.readW_far {D : Addr} {d n : Nat} {m m' : Mem} (h : Outside D d n m m')
    (hn : D.toNat + d + n ≤ 2 ^ 64) {a : Addr} (ha : Region.Disjoint ⟨a, 4⟩ ⟨off D d, n⟩) :
    m'.readW a 32 = m.readW a 32 :=
  (Outside.frame_span h hn).readW (r := ⟨a, 4⟩) (Region.contains_self _ _)
    (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact ha) (by decide)

/-- `[r + 0]` for `r = S + x`, `S + x + 4` within 32 bits. -/
theorem ea_far {s : State} {S : Addr} {r : Reg} {x : Nat} (hp : PtrAt s S r x)
    (hx : S.toNat + x + 4 ≤ 2 ^ 32) : s.ea (at_ r 0) = off S x := by
  rw [at_, ea_mk, addr_eq (by omega)]
  apply BitVec.eq_of_toNat_eq
  simp only [off, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have hS : S.toNat < 2 ^ 64 := S.isLt
  rw [Nat.mod_eq_of_lt (a := (s.gpr r).toNat) (by have := (s.gpr r).isLt; omega), hp]
  repeat rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- A readable span at `S + x`. -/
structure Span (s : State) (S : Addr) (x n : Nat) : Prop where
  read : InRegions (s.rd ++ s.wr) (off S x) n
  fit : S.toNat + x + n ≤ 2 ^ 32

theorem Span.of_keeps {s t : State} {S : Addr} {x n : Nat} {rs : List Reg} (h : Span s S x n) (K : Keeps rs s t) :
    Span t S x n := ⟨by rw [K.2.1, K.2.2]; exact h.read, h.fit⟩

theorem Span.sub {s : State} {S : Addr} {x n : Nat} (h : Span s S x n) {y k : Nat} (hy : x ≤ y)
    (hk : y + k ≤ x + n) : Span s S y k := by
  refine ⟨?_, by have := h.fit; omega⟩
  have := VG.CallLay.inRegions_sub h.read (off := y - x) (l := k) (by omega) (by have := h.fit; omega)
  rwa [show off S x + BitVec.ofNat 64 (y - x) = off S y by
    rw [off, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega] at this

/-- A load through `r = S + x` of a readable span. -/
theorem readSrc_far {s : State} {S : Addr} {r : Reg} {x : Nat} (hp : PtrAt s S r x) (hs : Span s S x 4) :
    readSrc s (.mem (at_ r 0)) = some (s.mem.readW (off S x) 32) := by
  show s.load32 (s.ea (at_ r 0)) = _
  rw [ea_far hp hs.fit, State.load32, ite_eq_left_iff.mpr fun h => absurd hs.read h]

/-- `selectLoop`: the destination's `N` words (at `D + d`, of a writable
region) set to the source's (a readable span at `S + x`, apart from them)
where the mask `ecx` is all ones, else kept. -/
theorem selectLoop_far_ok {t₀ : State} {D S : Addr} {L : Nat} (hw : Ws t₀ D L) {x d N : Nat} (k : Bool)
    (hN : 0 < N) (hs : Span t₀ S x (4 * N)) (hd : d + 4 * N ≤ L)
    (hdx : Region.Disjoint ⟨off S x, 4 * N⟩ ⟨off D d, 4 * N⟩)
    (hebp : PtrAt t₀ S .ebp x) (hebx : PtrAt t₀ D .ebx d)
    (hedi : (t₀.gpr .edi).toNat = 4 * N) (hecx : t₀.gpr .ecx = cmask k) :
    WP isa VG.Impl.Bignum.X86.CrtRt.selectLoop t₀
      fun u => Outside D d (4 * N) t₀.mem u.mem ∧
        val32 u.mem D d N = (if k then val32 t₀.mem S x N else val32 t₀.mem D d N) ∧
        PtrAt u D .ebx (d + 4 * N) ∧ PtrAt u S .ebp (x + 4 * N) ∧ Keeps [.eax, .ebx, .edx, .ebp, .edi] t₀ u := by
  have hn := hw.nowrap
  have hsf := hs.fit
  unfold VG.Impl.Bignum.X86.CrtRt.selectLoop
  refine WP.mono (countLoop hN (fun j t => Keeps [.eax, .ebx, .edx, .ebp, .edi] t₀ t ∧
      PtrAt t S .ebp (x + 4 * j) ∧ PtrAt t D .ebx (d + 4 * j) ∧ (t.gpr .edi).toNat = 4 * (N - j) ∧
      Outside D d (4 * j) t₀.mem t.mem ∧
      val32 t.mem D d j = (if k then val32 t₀.mem S x j else val32 t₀.mem D d j)) ?_
    ⟨Keeps.refl _ _, by simpa using hebp, by simpa using hebx, by simpa using hedi, Outside.refl _ _ _ _,
      by cases k <;> rfl⟩) fun u ⟨K, pe, P, _, O, V⟩ => ⟨O, V, P, pe, K⟩
  rintro j t hj ⟨Kt, ebp, ebx, edi, O, V⟩
  have ht := hw.of_keeps Kt
  have ecx : t.gpr .ecx = cmask k := by rw [Kt.1 _ (by decide)]; exact hecx
  have sj : Span t S (x + 4 * j) 4 := (hs.of_keeps Kt).sub (by omega) (by omega)
  have xw : t.mem.readW (off S (x + 4 * j)) 32 = t₀.mem.readW (off S (x + 4 * j)) 32 :=
    Outside.readW_far (n := 4 * N) (O.mono (Nat.le_refl _) (by omega)) (by omega)
      (hdx.sub_left (Offset.sub S (by omega) (by omega)))
  have dw : w32 t.mem D (d + 4 * j) = w32 t₀.mem D (d + 4 * j) :=
    O.w32 (by omega_using []) (by omega_using [hd, hj, hn])
  refine wp_movS (readSrc_ptr ht ebx (d := 0) (by omega_using [hd, hj])) fun s₁ u₁ _ => ?_
  have ebp₁ : PtrAt s₁ S .ebp (x + 4 * j) := by rw [PtrAt, u₁.other _ (by decide)]; exact ebp
  refine wp_movS (readSrc_far ebp₁ (sj.of_keeps u₁.keeps)) fun s₂ u₂ _ => ?_
  refine wp_logicS (.inr rfl) rfl fun s₃ u₃ => ?_
  refine wp_logicS (.inl rfl) rfl fun s₄ u₄ => ?_
  refine wp_logicS (.inr rfl) rfl fun s₅ u₅ => ?_
  have K₅ : Keeps [.eax, .edx] t s₅ :=
    (((u₁.keeps.mono (by decide)).widen u₂.keeps).widen u₃.keeps |>.widen u₄.keeps).widen u₅.keeps
  have ht₅ := ht.of_keeps K₅
  have ebx₅ : PtrAt s₅ D .ebx (d + 4 * j) := by rw [PtrAt, K₅.1 _ (by decide)]; exact ebx
  refine wp_storeS (ea_ptr ht₅ ebx₅ (d := 0) (by omega_using [hd, hj]))
    (ws_write ht₅ (y := d + 4 * j + 0) (n := 4) (by omega_using [hd, hj])) fun s₆ m₆ => ?_
  refine wp_addS rfl fun s₇ u₇ _ => wp_addS rfl fun s₈ u₈ _ => wp_subZ rfl fun s₉ u₉ z₉ => WP.block_nil ?_
  obtain ⟨c₁, c₂⟩ := count_zf edi hj
  have r₆ : ∀ r, r = .ebp ∨ r = .ebx ∨ r = .edi → s₆.gpr r = t.gpr r := by
    intro r hr; rw [m₆.gpr]; apply K₅.1; rcases hr with rfl | rfl | rfl <;> decide
  have mem₅ : s₅.mem = t.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have ecx₃ : s₃.gpr .ecx = t.gpr .ecx := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have eax₅ : s₅.gpr .eax = t.mem.readW (off D (d + 4 * j)) 32 ^^^
      ((t.mem.readW (off S (x + 4 * j)) 32 ^^^ t.mem.readW (off D (d + 4 * j)) 32) &&&
        (if k then BitVec.allOnes 32 else 0)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₄.gpr, ecx₃, ecx, u₃.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₂.gpr, u₁.gpr, u₁.mem, Nat.add_zero]
    rfl
  rw [select_val] at eax₅
  refine ⟨⟨Kt.trans ((((K₅.mono (by decide)).widen (m₆.keeps [])).widen u₇.keeps |>.widen u₈.keeps).widen u₉.keeps),
    ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [PtrAt, u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, r₆ _ (.inl rfl)]
    rw [VG.Proof.Mont.X86.Rt.ptr_add ebp]; congr 1
  · rw [PtrAt, u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), r₆ _ (.inr (.inl rfl))]; exact ptr4 ebx
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), r₆ _ (.inr (.inr rfl))]; exact c₁
  · rw [u₉.mem, u₈.mem, u₇.mem, m₆.mem, mem₅, Nat.add_zero]
    exact (O.mono (Nat.le_refl _) (by omega_using [])).trans
      ((writeW32_outside _ _ _ (by omega_using [hd, hj, hn])).mono (by omega_using []) (by omega_using []))
  · rw [u₉.mem, u₈.mem, u₇.mem, m₆.mem, mem₅, Nat.add_zero, val32_store hn (by omega_using [hd, hj]), V, eax₅,
      val32_succ t₀.mem S x, val32_succ t₀.mem D d]
    have xw' : (t.mem.readW (off S (x + 4 * j)) 32).toNat = w32 t₀.mem S (x + 4 * j) := by rw [xw]
    have dw' : (t.mem.readW (off D (d + 4 * j)) 32).toNat = w32 t₀.mem D (d + 4 * j) := dw
    cases k
    · simp only [Bool.false_eq_true, ite_false, dw']
    · simp only [ite_true, xw']
  · rw [z₉, u₈.other _ (by decide), u₇.other _ (by decide), r₆ _ (.inr (.inr rfl)), c₂]

end VG.Proof.Ffdh.X86.Cached

namespace VG.Proof.Ffdh.X86.Cached

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Impl.Ffdh.X86.Cached VG.Impl.Ffdh.X86.Cached.Generate
open VG.Impl.Bignum.X86.PublicRt (argAt)

/-- A number apart from the bytes that changed keeps its value. -/
theorem val32_far {rs : List Region} {m m' : Mem} (F : Frame rs m m') {P : Addr} {d N : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨off P d, 4 * N⟩ r) (hn : 4 * N < 2 ^ 64) :
    val32 m' P d N = val32 m P d N := by
  rw [← VG.Proof.Bignum.read_eq_val32, ← VG.Proof.Bignum.read_eq_val32]
  exact congrArg BitVec.toNat (F.read (Region.contains_self _ _) hd hn)

section
variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

/-- The context's address. -/
abbrev ctxAddr (args : Nat → BitVec 32) : Addr := byteAddr (args ctxArg)

/-- The context's bytes: three words, then 34 rows of `B` bytes. -/
abbrev ctxBytes (len : Nat) : Nat := 24 + bc len .wide * 34

/-- `r :=` the address of row `j` of the context, `ctx + 24 + B j`. -/
theorem rowAt_ok {is : List Instr} {Q : State → Prop} (h : In Ex base bytes len args s) {r : Reg} {j : Nat}
    (hj : j ≤ 34) (heax : s.gpr .eax = BitVec.ofNat 32 j)
    (k : ∀ u, Keeps [.eax, .ecx, .edx, r] s u → u.mem = s.mem →
      PtrAt u (ctxAddr args) r (24 + bc len .wide * j) → WP isa (.block is) u Q) :
    WP isa (.block (rowAt r ++ is)) s Q := by
  have hb := bc_le h.upper' .wide
  unfold rowAt
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine widthC_ok h.width h.upper' fun s₁ K₁ m₁ e₁ => wp_mul fun s₂ U₂ => ?_
  have h₁ := h.regs K₁ m₁
  have h₂ := h₁.regs ⟨fun q hq => U₂.other q (by simp at hq; exact hq.1) (by simp at hq; exact hq.2), U₂.rd,
    U₂.wr⟩ U₂.mem (rs := [.eax, .edx])
  refine wp_movS (h₂.arg (i := ctxArg) (by decide)) fun s₃' U₃' _ => wp_addS rfl fun s₃ U₃ _ =>
    wp_addS rfl fun s₄ U₄ _ => wp_mov fun u U => ?_
  refine k u ?_ (by rw [U.mem, U₄.mem, U₃.mem, U₃'.mem, U₂.mem, m₁]) ?_
  · refine ⟨fun q hq => ?_, by rw [U.rd, U₄.rd, U₃.rd, U₃'.rd, U₂.rd, K₁.2.1],
      by rw [U.wr, U₄.wr, U₃.wr, U₃'.wr, U₂.wr, K₁.2.2]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    rw [U.other q hq.2.2.2, U₄.other q hq.1, U₃.other q hq.1, U₃'.other q hq.2.1, U₂.other q hq.1 hq.2.2.1,
      K₁.1 q (by simpa using hq.2.2.1)]
  · have ea : (s₁.gpr .eax).toNat = j := by
      rw [K₁.1 _ (by decide), heax, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [PtrAt, U.gpr, U₄.gpr, U₃.gpr, U₃'.gpr, U₃'.other _ (by decide), U₂.eax, e₁, ea, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, ctxAddr, byteAddr, BitVec.toNat_setWidth]
    have a32 := (args ctxArg).isLt
    rw [Nat.mod_eq_of_lt (a := (args ctxArg).toNat) (by omega)]
    rw [Nat.mod_eq_of_lt (a := j * bc len .wide) (by
      have := Nat.mul_le_mul_right (bc len .wide) hj; omega)]
    rw [show BitVec.toNat (24 : BitVec 32) = 24 from rfl, Nat.mul_comm j]
    omega

/-- The context readable, apart from the working space. -/
structure CtxRd (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (s : State) : Prop where
  span : Span s (ctxAddr args) 0 (ctxBytes len)
  apart : Region.Disjoint ⟨ctxAddr args, ctxBytes len⟩ ⟨base, bytes⟩

theorem CtxRd.keep {t : State} {rs : List Reg} (C : CtxRd base bytes len args s) (K : Keeps rs s t) :
    CtxRd base bytes len args t := ⟨C.span.of_keeps K, C.apart⟩

/-- The context's 32-bit address does not wrap. -/
theorem CtxRd.afit (C : CtxRd base bytes len args s) : (args ctxArg).toNat + ctxBytes len ≤ 2 ^ 32 := by
  have fit := C.span.fit
  have hv : (byteAddr (args ctxArg)).toNat = (args ctxArg).toNat := by
    simp only [byteAddr, BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := (args ctxArg).isLt; omega)
  simp only [ctxAddr] at fit
  omega

/-- A span of the context, within it. -/
theorem CtxRd.row (C : CtxRd base bytes len args s) {d n : Nat} (hd : d + n ≤ ctxBytes len) :
    Span s (ctxAddr args) d n := C.span.sub (Nat.zero_le _) (by omega)

/-- Entry `e` (at `ebp`) into slot 7 if it is the window word's; `ebp` past it. -/
theorem combSelectStep_ok (h : In Ex base bytes len args s) (C : CtxRd base bytes len args s) {e D : Nat} (he : e < 32)
    (hw : w32 s.mem base winOff = D) (hD : D < 32)
    (hebp : PtrAt s (ctxAddr args) .ebp (24 + bc len .wide * (2 + e))) :
    WP isa (selectStep e) s fun u =>
      In Ex base bytes len args u ∧ Outside base (lo len (.slot .wide 7)) (bc len .wide) s.mem u.mem ∧
      PtrAt u (ctxAddr args) .ebp (24 + bc len .wide * (2 + (e + 1))) ∧
      sv u.mem base len .wide 7 = (if D = e then val32 s.mem (ctxAddr args) (24 + bc len .wide * (2 + e))
        (cwc len .wide) else sv s.mem base len .wide 7) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  have bl := h.bytes_lt
  have nw := h.scratch.nowrap
  have f7 := h.slot_fit .wide (j := 7) (by decide)
  have bw := bc_eq_cwc len .wide
  have g := bc_ge h.lower' .wide
  have hb := bc_le h.upper' .wide
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have e7 : lo len (.slot .wide 7) = numBase + 7 * st len .wide := rfl
  have nb : numBase = 3336 := rfl
  have wo : winOff = 4 := rfl
  have ce : 2 + e ≤ 33 := by omega
  have row := Nat.mul_le_mul_left (bc len .wide) (show 2 + e + 1 ≤ 34 by omega)
  rw [Nat.mul_add, Nat.mul_one] at row
  unfold Generate.selectStep
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (VG.Proof.Mont.X86.Dynamic.windowMask_ok h.scratch (j := e)
    (by omega) (by rw [← wo, hw]; exact hD) he) fun s₁ ⟨m₁, c₁, K₁⟩ => ?_))
  have h₁ := h.regs K₁ m₁
  refine ptrTo_ok (r := .ebx) (t := .edx) (x := .slot .wide 7) (by decide) (by decide) h₁.edi h₁.width h.upper'
    (by omega) fun s₂ K₂ m₂ p₂ => ?_
  have h₂ := h₁.regs K₂ m₂
  refine cntTo_ok (n := one .wide) (r := .edi) h₂.width h.upper' (by decide) fun s₃ K₃ m₃ e₃ => WP.block_nil ?_
  have K₁₃ : Keeps [.eax, .ebx, .ecx, .edx, .edi] s s₃ :=
    ((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₃.mono (by decide))
  have m₁₃ : s₃.mem = s.mem := by rw [m₃, m₂, m₁]
  have ws₃ : Ws s₃ base bytes := h.ws.of_keeps K₁₃
  have ebp₃ : PtrAt s₃ (ctxAddr args) .ebp (24 + bc len .wide * (2 + e)) := by
    rw [PtrAt, K₁₃.1 _ (by decide)]; exact hebp
  have ebx₃ : PtrAt s₃ base .ebx (lo len (.slot .wide 7)) := by rw [PtrAt, K₃.1 _ (by decide)]; exact p₂
  have edi₃ : (s₃.gpr .edi).toNat = 4 * cwc len .wide := by
    rw [e₃, cb1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact bw
  have ecx₃ : s₃.gpr .ecx = cmask (decide (D = e)) := by
    rw [K₃.1 _ (by decide), K₂.1 _ (by decide), c₁, show w32 s.mem base 4 = D from hw]
    simp only [cmask, decide_eq_true_eq]
  have span : Span s₃ (ctxAddr args) (24 + bc len .wide * (2 + e)) (4 * cwc len .wide) :=
    (C.keep K₁₃).row (by simp only [ctxBytes]; omega)
  have dis : Region.Disjoint ⟨off (ctxAddr args) (24 + bc len .wide * (2 + e)), 4 * cwc len .wide⟩
      ⟨off base (lo len (.slot .wide 7)), 4 * cwc len .wide⟩ :=
    (C.apart.sub_left (Offset.sub_base _ (by simp only [ctxBytes]; omega))).sub_right
      (Offset.sub_base _ (by omega))
  refine WP.seq (WP.mono (selectLoop_far_ok ws₃ (decide (D = e)) (by omega) span (by omega) dis ebp₃ ebx₃ edi₃ ecx₃)
    fun t ⟨O, V, _, pe, Kt⟩ => ?_)
  have K₀ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s t := (K₁₃.mono (by decide)).trans (Kt.mono (by decide))
  have Oall : Outside base 0 bytes s.mem t.mem := by rw [← m₁₃]; exact O.mono (Nat.zero_le _) (by omega)
  refine wp_movS ((h.stack 16 (by decide)).keep K₀ (by decide) Oall).readSrc fun u U _ => WP.block_nil ?_
  have ed : u.gpr .edi = s.gpr .edi := by rw [U.gpr]; exact h.edi_eq
  have Ku : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u :=
    VG.Proof.Bignum.X86.PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .ecx, .edx, .ebp])
      ((K₀.trans (U.keeps.mono (by decide))).mono (by decide)) ed
  have Ou : Outside base (lo len (.slot .wide 7)) (bc len .wide) s.mem u.mem := by
    rw [U.mem, ← m₁₃, bw]; exact O
  refine ⟨h.keep Ku (by decide) (by decide) (by rw [U.mem]; exact Oall), Ou, ?_, ?_, Ku⟩
  · rw [PtrAt, U.other _ (by decide), pe, ← bw, show 2 + (e + 1) = (2 + e) + 1 by omega, Nat.mul_succ]
    congr 1; omega
  · simp only [sv]
    rw [U.mem, V, m₁₃]
    by_cases d : D = e <;> simp [d]

/-- Slot 7 the context's entry of the digit in the window word (below 32), by scanning all 32 entries. -/
theorem select_ok (h : In Ex base bytes len args s) (C : CtxRd base bytes len args s) {D : Nat}
    (hw : w32 s.mem base winOff = D) (hD : D < 32) :
    WP isa Generate.select s fun u =>
      In Ex base bytes len args u ∧ Outside base (lo len (.slot .wide 7)) (bc len .wide) s.mem u.mem ∧
      sv u.mem base len .wide 7 = val32 s.mem (ctxAddr args) (24 + bc len .wide * (2 + D)) (cwc len .wide) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  have bl := h.bytes_lt
  have nw := h.scratch.nowrap
  have f7 := h.slot_fit .wide (j := 7) (by decide)
  have bw := bc_eq_cwc len .wide
  have hb := bc_le h.upper' .wide
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have e7 : lo len (.slot .wide 7) = numBase + 7 * st len .wide := rfl
  have nb : numBase = 3336 := rfl
  have wo : winOff = 4 := rfl
  unfold Generate.select
  refine WP.seq (WP.mono (zero_ok h (x := .slot .wide 7) (one_ok .wide) (by rw [cb1]; omega))
    fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
  rw [cb1] at O₁
  rw [cw1] at V₁
  have h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega))
  refine WP.seq (wp_movS rfl fun s₂ U₂ _ => rowAt_ok (r := .ebp) (j := 2) (h₁.regs U₂.keeps U₂.mem) (by decide)
    U₂.gpr fun s₃ K₃ m₃ p₃ => WP.block_nil ?_)
  have K₁₃ : Keeps [.eax, .ecx, .edx, .ebp] s s₃ :=
    (K₁.trans (U₂.keeps.mono (by decide))).trans (K₃.mono (by decide))
  have m₁₃ : s₃.mem = s₁.mem := by rw [m₃, U₂.mem]
  have h₃ := h₁.regs ((U₂.keeps.mono (by decide)).trans (K₃.mono (by decide)) : Keeps [.eax, .ecx, .edx, .ebp] s₁ s₃)
    m₁₃
  have C₀ : CtxRd base bytes len args s₃ := C.keep K₁₃
  -- The context did not change: only slot 7 did.
  have far : ∀ {m m' : Mem}, Outside base (lo len (.slot .wide 7)) (bc len .wide) m m' → ∀ j < 32,
      val32 m' (ctxAddr args) (24 + bc len .wide * (2 + j)) (cwc len .wide) =
        val32 m (ctxAddr args) (24 + bc len .wide * (2 + j)) (cwc len .wide) := fun {m m'} O j hj => by
    have row := Nat.mul_le_mul_left (bc len .wide) (show 2 + j + 1 ≤ 34 by omega)
    rw [Nat.mul_add, Nat.mul_one] at row
    refine val32_far (Outside.frame_span O (by omega)) (fun r hr => ?_) (by omega)
    obtain rfl := List.mem_singleton.mp hr
    exact (C.apart.sub_left (Offset.sub_base _ (by simp only [ctxBytes]; omega))).sub_right
      (Offset.sub_base _ (by omega))
  refine WP.mono (wp_seqs_range Generate.selectStep (fun e u => In Ex base bytes len args u ∧
      Outside base (lo len (.slot .wide 7)) (bc len .wide) s.mem u.mem ∧
      PtrAt u (ctxAddr args) .ebp (24 + bc len .wide * (2 + e)) ∧
      sv u.mem base len .wide 7 = (if D < e then val32 s.mem (ctxAddr args) (24 + bc len .wide * (2 + D))
        (cwc len .wide) else 0) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u) 32 (fun e he u ⟨Iu, Ou, pu, Vu, Ku⟩ => ?_)
    ⟨h₃, by rw [m₁₃]; exact O₁, p₃, by simp only [sv]; rw [m₁₃, V₁]; simp, K₁₃.mono (by decide)⟩)
    fun u ⟨Iu, Ou, _, Vu, Ku⟩ => ⟨Iu, Ou, by rw [Vu]; simp [hD], Ku⟩
  have wu : w32 u.mem base winOff = D := by rw [Ou.w32 (by omega) (by omega)]; exact hw
  refine WP.mono (combSelectStep_ok Iu (C.keep Ku) he wu hD pu) fun v ⟨Iv, Ov, pv, Vv, Kv⟩ =>
    ⟨Iv, Ou.trans Ov, pv, ?_, Ku.trans Kv⟩
  rw [Vv, Vu, far Ou e he]
  by_cases d : D = e
  · subst d; simp
  · by_cases l : D < e
    · simp [d, l, show D < e + 1 by omega]
    · simp [d, l, show ¬ D < e + 1 by omega]

end

end VG.Proof.Ffdh.X86.Cached
