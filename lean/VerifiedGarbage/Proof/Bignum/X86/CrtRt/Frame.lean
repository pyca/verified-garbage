module

public import VerifiedGarbage.Proof.Bignum.MemoryFrame
public import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.X86.Sse2.Shape
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.In
public import VerifiedGarbage.Proof.Bignum.X86.RtCall
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Callee
public import VerifiedGarbage.Impl.Mont.X86.MulRt
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Load
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Dsa.Frame
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.SelectX
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops2

/-! ### `Bignum.X86.CrtRt.Num`, which this module and modules that import it used -/

section

/-! # Numbers in private CRT at a run-time width

A number is the `cb len n` bytes at `lo len x`, its value the `cw len n`
words there. Zeroing (`zero_ok`), a small value (`setSmall_ok`), a
selection under a mask and a copy (`select_ok`, `copy_ok`), the difference
and the sum of two numbers with their borrow or carry (`chainSub_ok`,
`chainAdd_ok`), comparisons (`lessThan_ok`, `equal_ok`) and the import of
big-endian bytes (`load_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.PublicRt (zeroLoop_ok selectLoop_ok reduceLoop_ok compareLoop_ok byteAddr_ptr)
open VG.Impl.Bignum.X86.PublicRt (argAt)

/-- The words of a count. -/
abbrev cw (len : Nat) (n : Cnt) : Nat := cb len n / 4

/-- A count the loops run over: of whole words, its extra bytes few. -/
structure CntOk (n : Cnt) : Prop where
  extra : n.extra ≤ 64
  words : n.extra % 4 = 0

theorem one_ok (c : Ctx) : CntOk (one c) := ⟨by show 0 ≤ 64; decide, rfl⟩
theorem two_ok (c : Ctx) : CntOk (two c) := ⟨by show 0 ≤ 64; decide, rfl⟩

section
variable {len : Nat} {n : Cnt}

theorem cb_le (hl : len ≤ 1024) (N : CntOk n) : cb len n ≤ 2112 := by
  have := bc_le hl n.c
  have := N.extra
  simp only [cb]; split <;> omega_arith

theorem cb_eq (N : CntOk n) : cb len n = 4 * cw len n := by
  have := bc_dvd len n.c
  have := N.words
  simp only [cw, cb]; split <;> omega_arith

theorem cw_pos (hl : 64 ≤ len) : 0 < cw len n := by
  have := bc_ge hl n.c
  simp only [cw, cb]; split <;> omega_using [this]

theorem bc_cw (c : Ctx) : cw len (one c) = bc len c / 4 := by simp [cw, cb, one]

theorem cnt_toNat (hl : len ≤ 1024) (N : CntOk n) {x : BitVec 32} (hx : x = BitVec.ofNat 32 (cb len n)) :
    x.toNat = 4 * cw len n := by
  rw [hx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := cb_le hl N; omega_using [this])]
  exact cb_eq N

end

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

/-- Registers changed, memory kept: the inputs hold. -/
theorem In.regs (h : In Ex base bytes len args s) {t : State} {rs : List Reg} (K : Keeps rs s t) (m : t.mem = s.mem)
    (di : .edi ∉ rs := by decide) (sp : .esp ∉ rs := by decide) : In Ex base bytes len args t :=
  h.keep K di sp (by rw [m]; exact Outside.refl _ _ _ _)

theorem zero_ok (h : In Ex base bytes len args s) {x : Loc} {n : Cnt} (N : CntOk n)
    (hx : lo len x + cb len n ≤ bytes) :
    WP isa (zero x n) s fun u => Outside base (lo len x) (cb len n) s.mem u.mem ∧
      val32 u.mem base (lo len x) (cw len n) = 0 ∧ Keeps [.eax, .ecx, .edx, .ebp] s u := by
  have bl := h.bytes_lt
  obtain ce := cb_eq (len := len) N
  unfold zero
  simp only [List.append_assoc]
  refine WP.seq (ptrTo_ok (r := .ebp) (t := .edx) (by decide) (by decide) h.edi h.width h.upper' (by omega_using [hx, bl])
    fun u K m p => ?_)
  obtain hu := h.regs K m
  refine cntTo_ok (r := .ecx) hu.width h.upper' N.extra fun v Kv mv cv => wp_movS rfl fun w uw _ => WP.block_nil ?_
  obtain Kw : Keeps [.eax, .ecx, .edx, .ebp] s w :=
    ((K.mono (by decide)).trans (Kv.mono (by decide))).trans (uw.keeps.mono (by decide))
  obtain mw : w.mem = s.mem := by rw [uw.mem, mv, m]
  refine WP.mono (zeroLoop_ok (h.ws.of_keeps Kw) (x := lo len x) (N := cw len n) (cw_pos h.lower') (by omega_using [hx, ce])
    (by rw [PtrAt, uw.other _ (by decide), Kv.1 _ (by decide)]; exact p)
    (cnt_toNat h.upper' N (by rw [uw.other _ (by decide), cv])) uw.gpr) fun t ⟨O, V, Kt⟩ => ?_
  refine ⟨by rw [← mw, ce]; exact O, V, Kw.trans (Kt.mono (by decide))⟩

theorem setSmall_ok (h : In Ex base bytes len args s) {x : Loc} {n : Cnt} (N : CntOk n)
    (hx : lo len x + cb len n ≤ bytes) {v : Nat} (hv : v < 2 ^ 32) :
    WP isa (setSmall x n v) s fun u => Outside base (lo len x) (cb len n) s.mem u.mem ∧
      val32 u.mem base (lo len x) (cw len n) = v ∧ Keeps [.eax, .ecx, .edx, .ebp] s u := by
  have bl := h.bytes_lt
  have hn := h.scratch.nowrap
  obtain ce := cb_eq (len := len) N
  obtain cp := cw_pos (n := n) h.lower'
  unfold setSmall
  refine WP.seq (WP.mono (zero_ok h N hx) fun u ⟨O, V, K⟩ => ?_)
  obtain hu := h.keep K (by decide) (by decide) (O.mono (Nat.zero_le _) (by omega_using [hx]))
  refine ptrTo_ok (r := .eax) (t := .edx) (by decide) (by decide) hu.edi hu.width h.upper' (by omega_using [hx, bl])
    fun w Kw mw pw => wp_movS rfl fun w₁ u₁ _ => ?_
  obtain hw₁ := h.ws.of_keeps (K.trans ((Kw.mono (by decide)).trans (u₁.keeps.mono (by decide))))
  obtain p₁ : PtrAt w₁ base .eax (lo len x) := by rw [PtrAt, u₁.other _ (by decide)]; exact pw
  refine wp_storeS (ea_ptr hw₁ p₁ (d := 0) (by omega_using [hx, ce, cp]))
    (ws_write hw₁ (y := lo len x + 0) (n := 4) (by omega_using [hx, ce, cp])) fun t mt => WP.block_nil ?_
  obtain mw₁ : w₁.mem = u.mem := by rw [u₁.mem, mw]
  refine ⟨?_, ?_, (K.trans ((Kw.mono (by decide)).trans (u₁.keeps.mono (by decide)))).trans (mt.keeps _)⟩
  · rw [mt.mem, mw₁, Nat.add_zero]
    exact O.trans ((writeW32_outside _ _ _ (by omega_using [hx, bl])).mono (by omega_using []) (by omega_using [ce, cp]))
  · rw [mt.mem, mw₁, Nat.add_zero, u₁.gpr]
    obtain ⟨k, hk⟩ : ∃ k, cw len n = k + 1 := ⟨cw len n - 1, by omega_using [cp]⟩
    rw [hk] at V ⊢
    have V' := V
    rw [val32] at V'
    rw [val32, w32_write_self]
    obtain rest : val32 (u.mem.writeW (off base (lo len x)) (BitVec.ofNat 32 v)) base (lo len x + 4) k =
        val32 u.mem base (lo len x + 4) k :=
      (writeW32_outside u.mem base _ (by omega_using [hx, bl])).val32 (by omega_using []) (by omega_using [hx, bl, ce, hk])
    rw [rest, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
    omega_using [V']

/-- The ranges of two numbers are apart. -/
abbrev Apart (a k b l : Nat) : Prop := a + k ≤ b ∨ b + l ≤ a

theorem select_ok (h : In Ex base bytes len args s) {x d : Loc} {n : Cnt} (N : CntOk n)
    (hx : lo len x + cb len n ≤ bytes) (hd : lo len d + cb len n ≤ bytes)
    (hxd : Apart (lo len d) (cb len n) (lo len x) (cb len n)) {k : Bool} (hk : s.gpr .ecx = cmask k) :
    WP isa (select x d n) s fun u => Outside base (lo len d) (cb len n) s.mem u.mem ∧
      val32 u.mem base (lo len d) (cw len n) =
        (if k then val32 s.mem base (lo len x) (cw len n) else val32 s.mem base (lo len d) (cw len n)) ∧
      Keeps [.eax, .ebx, .edx, .ebp] s u := by
  have bl := h.bytes_lt
  obtain ce := cb_eq (len := len) N
  unfold select
  simp only [List.append_assoc]
  refine WP.seq (ptrTo_ok (r := .ebp) (t := .edx) (by decide) (by decide) h.edi h.width h.upper' (by omega_using [hx, bl])
    fun u K m p => ?_)
  obtain hu := h.regs K m
  refine ptrTo_ok (r := .ebx) (t := .edx) (by decide) (by decide) hu.edi hu.width h.upper' (by omega_using [hd, bl])
    fun v Kv mv pv => ?_
  obtain hv := hu.regs Kv mv
  rw [← List.append_nil (cntTo n .edi)]
  refine cntTo_ok (r := .edi) hv.width h.upper' N.extra fun w Kw mw cw' => WP.block_nil ?_
  obtain Kw' : Keeps [.ebx, .edx, .ebp, .edi] s w :=
    ((K.mono (by decide)).trans (Kv.mono (by decide))).trans (Kw.mono (by decide))
  obtain mw' : w.mem = s.mem := by rw [mw, mv, m]
  refine WP.seq (WP.mono (selectLoop_ok (h.ws.of_keeps Kw') (x := lo len x) (d := lo len d) (N := cw len n) k
    (cw_pos h.lower') (by omega_using [hx, ce]) (by omega_using [hd, ce]) (by omega)
    (by rw [PtrAt, Kw.1 _ (by decide), Kv.1 _ (by decide)]; exact p)
    (by rw [PtrAt, Kw.1 _ (by decide)]; exact pv)
    (cnt_toNat h.upper' N cw')
    (by rw [Kw.1 _ (by decide), Kv.1 _ (by decide), K.1 _ (by decide)]; exact hk))
    fun t ⟨O, V, _, Kt⟩ => ?_)
  obtain Kall : Keeps [.eax, .ebx, .edx, .ebp, .edi] s t := (Kw'.mono (by decide)).trans Kt
  obtain Oall : Outside base 0 bytes s.mem t.mem := by rw [← mw']; exact O.mono (Nat.zero_le _) (by omega_using [hd, ce])
  refine wp_movS ((h.stack 16 (by decide)).keep Kall (by decide) Oall).readSrc fun t₁ u₁ _ => WP.block_nil ?_
  obtain e : t₁.gpr .edi = s.gpr .edi := by rw [u₁.gpr]; exact h.edi_eq
  refine ⟨by rw [u₁.mem, ← mw', ce]; exact O, by rw [u₁.mem, V, mw'],
    PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .edx, .ebp]) (Kall.trans (u₁.keeps.mono (by decide))) e⟩

/-- `select_ok` for `selectX`. -/
theorem selectX_ok (h : In Ex base bytes len args s) {x d : Loc} {n : Cnt} (N : CntOk n)
    (hx : lo len x + cb len n ≤ bytes) (hd : lo len d + cb len n ≤ bytes)
    (hxd : Apart (lo len d) (cb len n) (lo len x) (cb len n)) (h4 : 4 ≤ cw len n) {k : Bool} (hk : s.gpr .ecx = cmask k) :
    WP isa (selectX x d n) s fun u => Outside base (lo len d) (cb len n) s.mem u.mem ∧
      val32 u.mem base (lo len d) (cw len n) =
        (if k then val32 s.mem base (lo len x) (cw len n) else val32 s.mem base (lo len d) (cw len n)) ∧
      Keeps [.eax, .ebx, .edx, .ebp] s u := by
  have bl := h.bytes_lt
  obtain ce := cb_eq (len := len) N
  unfold selectX
  simp only [List.append_assoc]
  refine WP.seq (ptrTo_ok (r := .ebp) (t := .edx) (by decide) (by decide) h.edi h.width h.upper' (by omega_using [hx, bl])
    fun u K m p => ?_)
  obtain hu := h.regs K m
  refine ptrTo_ok (r := .ebx) (t := .edx) (by decide) (by decide) hu.edi hu.width h.upper' (by omega_using [hd, bl])
    fun v Kv mv pv => ?_
  obtain hv := hu.regs Kv mv
  rw [← List.append_nil (cntTo n .edi)]
  refine cntTo_ok (r := .edi) hv.width h.upper' N.extra fun w Kw mw cw' => WP.block_nil ?_
  obtain Kw' : Keeps [.ebx, .edx, .ebp, .edi] s w :=
    ((K.mono (by decide)).trans (Kv.mono (by decide))).trans (Kw.mono (by decide))
  obtain mw' : w.mem = s.mem := by rw [mw, mv, m]
  refine WP.seq (WP.mono (selectLoopX_ok (h.ws.of_keeps Kw') (x := lo len x) (d := lo len d) (N := cw len n) k
    h4 (by omega_using [hx, ce]) (by omega_using [hd, ce]) (by omega)
    (by rw [PtrAt, Kw.1 _ (by decide), Kv.1 _ (by decide)]; exact p)
    (by rw [PtrAt, Kw.1 _ (by decide)]; exact pv)
    (cnt_toNat h.upper' N cw')
    (by rw [Kw.1 _ (by decide), Kv.1 _ (by decide), K.1 _ (by decide)]; exact hk))
    fun t ⟨O, V, _, _, Kt⟩ => ?_)
  obtain Kall : Keeps [.eax, .ebx, .edx, .ebp, .edi] s t := (Kw'.mono (by decide)).trans Kt
  obtain Oall : Outside base 0 bytes s.mem t.mem := by rw [← mw']; exact O.mono (Nat.zero_le _) (by omega_using [hd, ce])
  refine wp_movS ((h.stack 16 (by decide)).keep Kall (by decide) Oall).readSrc fun t₁ u₁ _ => WP.block_nil ?_
  obtain e : t₁.gpr .edi = s.gpr .edi := by rw [u₁.gpr]; exact h.edi_eq
  refine ⟨by rw [u₁.mem, ← mw', ce]; exact O, by rw [u₁.mem, V, mw'],
    PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .edx, .ebp]) (Kall.trans (u₁.keeps.mono (by decide))) e⟩

theorem copy_ok (h : In Ex base bytes len args s) {x d : Loc} {n : Cnt} (N : CntOk n)
    (hx : lo len x + cb len n ≤ bytes) (hd : lo len d + cb len n ≤ bytes)
    (hxd : Apart (lo len d) (cb len n) (lo len x) (cb len n)) :
    WP isa (copy x d n) s fun u => Outside base (lo len d) (cb len n) s.mem u.mem ∧
      val32 u.mem base (lo len d) (cw len n) = val32 s.mem base (lo len x) (cw len n) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  unfold copy
  refine WP.seq (wp_movS rfl fun u uu _ => WP.block_nil ?_)
  obtain hu := h.regs uu.keeps uu.mem
  refine WP.mono (select_ok hu N hx hd hxd (k := true) (by rw [uu.gpr]; rfl)) fun t ⟨O, V, K⟩ => ?_
  refine ⟨by rw [← uu.mem]; exact O, by rw [V, uu.mem]; rfl, (uu.keeps.mono (by decide)).trans (K.mono (by decide))⟩


/-- The top half of the wide slot `j` (`Bh` bytes from byte `Bh`) into the half slot `d`. -/
theorem copyHigh_ok (h : In Ex base bytes len args s) {j d : Nat}
    (hx : lo len (.slot .wide j) + 2 * bc len .half ≤ bytes) (hd : lo len (.slot .half d) + bc len .half ≤ bytes)
    (hxd : lo len (.slot .half d) + bc len .half ≤ lo len (.slot .wide j)) :
    WP isa (copyHigh j d) s fun u => Outside base (lo len (.slot .half d)) (bc len .half) s.mem u.mem ∧
      val32 u.mem base (lo len (.slot .half d)) (cw len (one .half)) =
        val32 s.mem base (lo len (.slot .wide j) + bc len .half) (cw len (one .half)) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  have bl := h.bytes_lt
  obtain N := one_ok .half
  obtain ce := cb_eq (len := len) N
  obtain cb1 : cb len (one .half) = bc len .half := by simp [cb, one]
  obtain bhl := bc_le h.upper' .half
  unfold copyHigh
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.seq (wp_movS rfl fun u₀ a₀ _ => ?_)
  obtain h₀ := h.regs a₀.keeps a₀.mem
  refine ptrTo_ok (r := .ebp) (t := .edx) (by decide) (by decide) h₀.edi h₀.width h.upper' (by omega_using [hx, bl])
    fun u₁ K₁ m₁ p₁ => ?_
  obtain h₁ := h₀.regs K₁ m₁
  refine widthC_ok (k := 0) h₁.width h.upper' fun u₂ K₂ m₂ e₂ => wp_addS rfl fun u₃ a₃ _ => ?_
  obtain K₃ : Keeps [.ebp, .edx] u₁ u₃ := (K₂.mono (by decide)).trans (a₃.keeps.mono (by decide))
  obtain m₃ : u₃.mem = u₁.mem := by rw [a₃.mem, m₂]
  obtain p₃ : PtrAt u₃ base .ebp (lo len (.slot .wide j) + bc len .half) := by
    rw [PtrAt, a₃.gpr, K₂.1 _ (by decide), e₂, ptr_add p₁, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := bc len .half) (by omega_using [bhl])]
  obtain h₃ := h₁.regs K₃ m₃
  refine ptrTo_ok (r := .ebx) (t := .edx) (by decide) (by decide) h₃.edi h₃.width h.upper' (by omega_using [hd, bl])
    fun u₄ K₄ m₄ p₄ => ?_
  obtain h₄ := h₃.regs K₄ m₄
  rw [← List.append_nil (cntTo (one .half) .edi)]
  refine cntTo_ok (r := .edi) h₄.width h.upper' N.extra fun u₅ K₅ m₅ c₅ => WP.block_nil ?_
  obtain Kw' : Keeps [.ebx, .ecx, .edx, .ebp, .edi] s u₅ :=
    ((((a₀.keeps.mono (by decide)).trans (K₁.mono (by decide))).trans (K₃.mono (by decide))).trans
      (K₄.mono (by decide))).trans (K₅.mono (by decide))
  obtain mw' : u₅.mem = s.mem := by rw [m₅, m₄, m₃, m₁, a₀.mem]
  obtain ecx₅ : u₅.gpr .ecx = cmask true := by
    rw [K₅.1 _ (by decide), K₄.1 _ (by decide), K₃.1 _ (by decide), K₁.1 _ (by decide), a₀.gpr]; rfl
  refine WP.seq (WP.mono (selectLoop_ok (h.ws.of_keeps Kw') (x := lo len (.slot .wide j) + bc len .half)
    (d := lo len (.slot .half d)) (N := cw len (one .half)) true
    (by have := bc_ge h.lower' .half; omega) (by omega) (by omega) (.inl (by omega))
    (by rw [PtrAt, K₅.1 _ (by decide), K₄.1 _ (by decide)]; exact p₃)
    (by rw [PtrAt, K₅.1 _ (by decide)]; exact p₄)
    (cnt_toNat h.upper' N c₅) ecx₅)
    fun t ⟨O, V, _, Kt⟩ => ?_)
  obtain Kall : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s t := (Kw'.mono (by decide)).trans (Kt.mono (by decide))
  obtain Oall : Outside base 0 bytes s.mem t.mem := by rw [← mw']; exact O.mono (Nat.zero_le _) (by omega)
  refine wp_movS ((h.stack 16 (by decide)).keep Kall (by decide) Oall).readSrc fun t₁ u₁ _ => WP.block_nil ?_
  obtain e : t₁.gpr .edi = s.gpr .edi := by rw [u₁.gpr]; exact h.edi_eq
  refine ⟨by rw [u₁.mem, ← mw', show 4 * cw len (one .half) = bc len .half by omega] at *; exact O,
    by rw [u₁.mem, V, mw']; rfl,
    PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .ecx, .edx, .ebp]) (Kall.trans (u₁.keeps.mono (by decide))) e⟩

end

end VG.Proof.Bignum.X86.CrtRt

end

end

/-! ### `Bignum.X86.CrtRt.MulOk`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86.CrtRt.Mul`, which only this module used -/

section

/-! # A multiplication by a call, in private CRT at a run-time width

`mulArgs c o a b` stores the arguments of `vg_rsa_mont_mul_at` for the slots
`o`, `a` and `b` of the context `c` (`mulArgs_ok`); `mul c o a b` writes the
Montgomery product of slots `a` and `b` into slot `o`, changing only it,
the callee's range (from slot 1) and the 40 bytes below `esp` (`mul_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.RtCall
open VG.Proof.Bignum.X86.PublicRt (adds_ok frame_store frame_other argAt_alloc)
open VG.Impl.Bignum.X86.PublicRt (argAt)
open VG.Proof.Rsa.MontMul (scratchBytes)

/-- `offIn (.slot c j)`: `eax = numBase + j t` from `edx = t`. -/
theorem offIn_ok {s : State} {is : List Instr} {Q : State → Prop} {c : Ctx} {j t : Nat}
    (hedx : s.gpr .edx = BitVec.ofNat 32 t) (ht : t ≤ 2080) (hj : j ≤ 28)
    (kk : ∀ u, Keeps [.eax] s u → u.mem = s.mem → u.gpr .eax = BitVec.ofNat 32 (numBase + j * t) →
      WP isa (.block is) u Q) :
    WP isa (.block (offIn (.slot c j) ++ is)) s Q := by
  simp only [offIn, List.cons_append]
  refine wp_movS rfl fun s₁ u₁ _ => adds_ok (r := .eax) (t := .edx) (by decide) j fun u K m e => ?_
  refine kk u (u₁.keeps.trans K) (by rw [m, u₁.mem]) ?_
  rw [e, u₁.gpr, u₁.other _ (by decide), hedx]
  apply BitVec.eq_of_toNat_eq
  have : j * t ≤ 28 * 2080 := Nat.mul_le_mul hj ht
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, numBase]
  rw [Nat.mod_eq_of_lt (a := t) (by omega_using [ht]), Nat.mod_eq_of_lt (a := j * t) (by omega_using [this])]

theorem mulArgs_ok {f : State} {len : Nat} {c : Ctx} {o a b : Nat} {wsLen : BitVec 32}
    (hr1 : readSrc f (.mem (argAt 9 1)) = some (BitVec.ofNat 32 len))
    (hr17 : readSrc f (.mem (argAt 9 wsLenArg)) = some wsLen)
    (hl : len ≤ 1024) (ho : o ≤ 28) (ha : a ≤ 28) (hb : b ≤ 28)
    (hesp : (f.gpr .esp).toNat + 36 ≤ 2 ^ 32) (hfr : (⟨(f.gpr .esp).setWidth 64, 36⟩ : Region) ∈ f.wr) :
    WP isa (.block (mulArgs c o a b)) f fun g =>
      Keeps [.eax, .edx] f g ∧ Frame [⟨(f.gpr .esp).setWidth 64, 36⟩] f.mem g.mem ∧
      ∀ i < 9, g.mem.readW ((f.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 * i)) 32 =
        callArg (f.gpr .edi) wsLen (bc len c / 8) numBase invOff (lo len (.slot c 1)) (lo len (.slot c o))
          (lo len (.slot c a)) (lo len (.slot c b)) i := by
  obtain hw := bc_le hl c
  obtain h8 := bc_dvd len c
  generalize hP : (f.gpr .esp).setWidth 64 = P at hfr ⊢
  simp only [mulArgs, List.append_assoc, List.cons_append, List.nil_append]
  refine widthC_ok hr1 hl fun s₁ K₁ m₁ e₁ => ?_
  obtain fr : ∀ t : State, t.gpr .esp = f.gpr .esp → t.wr = f.wr → ∀ k, k + 4 ≤ 36 →
      t.ea (at_ .esp k) = P + BitVec.ofNat 64 k ∧ InRegions t.wr (P + BitVec.ofNat 64 k) 4 :=
    fun t he hw' k hk => frame_store (by rw [he, hP]) (by rw [he]; exact hesp) (by rw [hw']; exact hfr) hk
  obtain sp₁ : s₁.gpr .esp = f.gpr .esp := K₁.1 _ (by decide)
  obtain edi₁ : s₁.gpr .edi = f.gpr .edi := K₁.1 _ (by decide)
  obtain hr17₁ : readSrc s₁ (.mem (argAt 9 wsLenArg)) = some wsLen := by
    rw [← hr17]; simp only [readSrc, State.load32, State.ea, argAt, at_, sp₁, m₁, K₁.2.1, K₁.2.2]; rfl
  refine wp_movS hr17₁ fun s₂ u₂ _ => ?_
  obtain K₂ : Keeps [.eax, .edx] f s₂ := (K₁.mono (by decide)).trans (u₂.keeps.mono (by decide))
  obtain ⟨a₄, w₄⟩ := fr s₂ (K₂.1 _ (by decide)) K₂.2.2 4 (by decide)
  refine wp_storeS a₄ w₄ fun s₃ m₃ => ?_
  obtain ⟨a₀, w₀⟩ := fr s₃ (by rw [m₃.gpr]; exact K₂.1 _ (by decide)) (by rw [m₃.wr]; exact K₂.2.2) 0 (by decide)
  refine wp_storeS a₀ w₀ fun s₄ m₄ => ?_
  obtain K₄ : Keeps [.eax, .edx] f s₄ := (K₂.trans (m₃.keeps _)).trans (m₄.keeps _)
  refine wp_movS rfl fun s₅ u₅ _ => VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun s₆ u₆ => ?_
  obtain K₆ : Keeps [.eax, .edx] f s₆ := (K₄.trans (u₅.keeps.mono (by decide))).trans (u₆.keeps.mono (by decide))
  obtain ⟨a₈, w₈⟩ := fr s₆ (K₆.1 _ (by decide)) K₆.2.2 8 (by decide)
  refine wp_storeS a₈ w₈ fun s₇ m₇ => wp_addS rfl fun s₇' u₇' _ => wp_addS rfl fun s₇'' u₇'' _ => ?_
  refine wp_movS rfl fun s₈ u₈ _ => ?_
  obtain K₈ : Keeps [.eax, .edx] f s₈ :=
    (((K₆.trans (m₇.keeps _)).trans (u₇'.keeps.mono (by decide))).trans (u₇''.keeps.mono (by decide))).trans
      (u₈.keeps.mono (by decide))
  obtain ⟨a₁₂, w₁₂⟩ := fr s₈ (K₈.1 _ (by decide)) K₈.2.2 12 (by decide)
  refine wp_storeS a₁₂ w₁₂ fun s₉ m₉ => wp_movS rfl fun s₁₀ u₁₀ _ => ?_
  obtain K₁₀ : Keeps [.eax, .edx] f s₁₀ := (K₈.trans (m₉.keeps _)).trans (u₁₀.keeps.mono (by decide))
  obtain ⟨a₁₆, w₁₆⟩ := fr s₁₀ (K₁₀.1 _ (by decide)) K₁₀.2.2 16 (by decide)
  refine wp_storeS a₁₆ w₁₆ fun s₁₁ m₁₁ => ?_
  obtain K₁₁ : Keeps [.eax, .edx] f s₁₁ := K₁₀.trans (m₁₁.keeps _)
  -- `edx` holds the stride from the two additions on.
  obtain edxS : s₇''.gpr .edx = BitVec.ofNat 32 (st len c) := by
    rw [u₇''.gpr, u₇'.gpr, m₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), m₄.gpr, m₃.gpr,
      u₂.other _ (by decide), e₁]
    apply BitVec.eq_of_toNat_eq
    have e32 : (32 : BitVec 32).toNat = 32 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, e32, st]
    rw [Nat.mod_eq_of_lt (a := bc len c) (by omega_using [hw])]
    omega_using []
  obtain edx₁₁ : s₁₁.gpr .edx = BitVec.ofNat 32 (st len c) := by
    rw [m₁₁.gpr, u₁₀.other _ (by decide), m₉.gpr, u₈.other _ (by decide), edxS]
  obtain hst : st len c ≤ 2080 := by simp only [st]; omega_using [hw]
  refine offIn_ok (c := c) (j := 1) edx₁₁ hst (by decide) fun s₁₂ K₁₂ m₁₂ e₁₂ => ?_
  obtain K₁₂' : Keeps [.eax, .edx] f s₁₂ := K₁₁.trans (K₁₂.mono (by decide))
  obtain ⟨a₂₀, w₂₀⟩ := fr s₁₂ (K₁₂'.1 _ (by decide)) K₁₂'.2.2 20 (by decide)
  refine wp_storeS a₂₀ w₂₀ fun s₁₃ m₁₃ => ?_
  obtain edx₁₃ : s₁₃.gpr .edx = BitVec.ofNat 32 (st len c) := by rw [m₁₃.gpr, K₁₂.1 _ (by decide), edx₁₁]
  refine offIn_ok (c := c) (j := o) edx₁₃ hst ho fun s₁₄ K₁₄ m₁₄ e₁₄ => ?_
  obtain K₁₄' : Keeps [.eax, .edx] f s₁₄ := (K₁₂'.trans (m₁₃.keeps _)).trans (K₁₄.mono (by decide))
  obtain ⟨a₂₄, w₂₄⟩ := fr s₁₄ (K₁₄'.1 _ (by decide)) K₁₄'.2.2 24 (by decide)
  refine wp_storeS a₂₄ w₂₄ fun s₁₅ m₁₅ => ?_
  obtain edx₁₅ : s₁₅.gpr .edx = BitVec.ofNat 32 (st len c) := by rw [m₁₅.gpr, K₁₄.1 _ (by decide), edx₁₃]
  refine offIn_ok (c := c) (j := a) edx₁₅ hst ha fun s₁₆ K₁₆ m₁₆ e₁₆ => ?_
  obtain K₁₆' : Keeps [.eax, .edx] f s₁₆ := (K₁₄'.trans (m₁₅.keeps _)).trans (K₁₆.mono (by decide))
  obtain ⟨a₂₈, w₂₈⟩ := fr s₁₆ (K₁₆'.1 _ (by decide)) K₁₆'.2.2 28 (by decide)
  refine wp_storeS a₂₈ w₂₈ fun s₁₇ m₁₇ => ?_
  obtain edx₁₇ : s₁₇.gpr .edx = BitVec.ofNat 32 (st len c) := by rw [m₁₇.gpr, K₁₆.1 _ (by decide), edx₁₅]
  refine offIn_ok (c := c) (j := b) edx₁₇ hst hb fun s₁₈ K₁₈ m₁₈ e₁₈ => ?_
  obtain K₁₈' : Keeps [.eax, .edx] f s₁₈ := (K₁₆'.trans (m₁₇.keeps _)).trans (K₁₈.mono (by decide))
  obtain ⟨a₃₂, w₃₂⟩ := fr s₁₈ (K₁₈'.1 _ (by decide)) K₁₈'.2.2 32 (by decide)
  refine wp_storeS a₃₂ w₃₂ fun g mg => WP.block_nil ?_
  obtain edx₄ : s₄.gpr .edx = BitVec.ofNat 32 (bc len c) := by rw [m₄.gpr, m₃.gpr, u₂.other _ (by decide), e₁]
  obtain eW : s₆.gpr .eax = BitVec.ofNat 32 (bc len c / 8) := by
    rw [u₆.gpr, u₅.gpr, edx₄]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (a := bc len c) (by omega_using [hw]), Nat.mod_eq_of_lt (by omega_using [hw])]
  obtain mem : g.mem = ((((((((f.mem.writeW (P + BitVec.ofNat 64 4) wsLen).writeW (P + BitVec.ofNat 64 0)
      (f.gpr .edi)).writeW (P + BitVec.ofNat 64 8) (BitVec.ofNat 32 (bc len c / 8))).writeW
      (P + BitVec.ofNat 64 12) (BitVec.ofNat 32 numBase)).writeW (P + BitVec.ofNat 64 16)
      (BitVec.ofNat 32 invOff)).writeW (P + BitVec.ofNat 64 20) (BitVec.ofNat 32 (lo len (.slot c 1)))).writeW
      (P + BitVec.ofNat 64 24) (BitVec.ofNat 32 (lo len (.slot c o)))).writeW (P + BitVec.ofNat 64 28)
      (BitVec.ofNat 32 (lo len (.slot c a)))).writeW (P + BitVec.ofNat 64 32)
        (BitVec.ofNat 32 (lo len (.slot c b))) := by
    rw [mg.mem, m₁₈, m₁₇.mem, m₁₆, m₁₅.mem, m₁₄, m₁₃.mem, m₁₂, m₁₁.mem, u₁₀.mem, m₉.mem, u₈.mem,
      u₇''.mem, u₇'.mem, m₇.mem, u₆.mem, u₅.mem, m₄.mem, m₃.mem, u₂.mem, m₁, e₁₈, e₁₆, e₁₄, e₁₂, u₁₀.gpr, u₈.gpr,
      eW, m₃.gpr, u₂.gpr, u₂.other .edi (by decide), edi₁]
    rfl
  refine ⟨K₁₈'.trans (mg.keeps _), ?_, ?_⟩
  · have fw : ∀ {m : Mem} (k : Nat) (v : BitVec 32), k + 4 ≤ 36 → Frame [⟨P, 36⟩] f.mem m →
        Frame [⟨P, 36⟩] f.mem (m.writeW (P + BitVec.ofNat 64 k) v) := fun k v hk F =>
      F.writeW (List.mem_singleton_self _) v (Offset.contains_base _ hk (by omega_using [hk]))
    rw [mem]
    exact fw _ _ (by decide) <| fw _ _ (by decide) <| fw _ _ (by decide) <| fw _ _ (by decide) <|
      fw _ _ (by decide) <| fw _ _ (by decide) <| fw _ _ (by decide) <| fw _ _ (by decide) <|
      fw _ _ (by decide) (Frame.refl _ _)
  · intro i hi
    rw [mem]
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i
    all_goals first
      | omega
      | simp (disch := decide) only [frame_other, Mem.readW_writeW_self32, callArg, Nat.mul_zero, Nat.reduceMul,
          Nat.reduceAdd, Nat.zero_add]

end VG.Proof.Bignum.X86.CrtRt

end

end


/-! # The Montgomery product of two slots of a context, by a call -/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.RtCall
open VG.Proof.Bignum.X86.PublicRt (argAt_alloc)
open VG.Impl.Bignum.X86.PublicRt (argAt)
open VG.Proof.Rsa.MontMul (scratchBytes)

/-- The words of a number of the context. -/
abbrev cwc (len : Nat) (c : Ctx) : Nat := bc len c / 4

theorem cwc_eq (len : Nat) (c : Ctx) : 2 * (bc len c / 8) = cwc len c := by
  have := bc_dvd len c; simp only [cwc]; omega_using [this]

theorem bc_eq_cwc (len : Nat) (c : Ctx) : bc len c = 4 * cwc len c := by
  have := bc_dvd len c; simp only [cwc]; omega_using [this]

theorem mulBody_noSp (c : Ctx) (o a b : Nat) :
    NoSp (.seq (.block (mulArgs c o a b)) (.call "vg_rsa_mont_mul_at" Sse2.atBody) : Prog isa) := by
  apply NoSp.of_all
  have e : (!Taint.clobbers (Instr.alu AluOp.add Reg.eax (Src.reg Reg.edx)) Reg.esp) = true := rfl
  rw [Code.allInstrs_eq]
  cases c <;>
  simp only [instrs, mulArgs, widthC, VG.Impl.Bignum.X86.PublicRt.widthB, offIn, List.all_append, List.all_cons,
    List.all_nil, List.all_replicate, e, ite_self] <;>
  rw [← Code.allInstrs_eq] <;>
  rw [show Sse2.atBody.allInstrs (fun i => !Taint.clobbers i .esp)=true from VG.Proof.Mont.X86.Sse2.atBody_allNoSp] <;> rfl

/-- The callee's offsets for slots `o`, `a` and `b` (3 to 8) of a context. -/
theorem In.offs {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : In Ex base bytes len args s) (c : Ctx) {o a b : Nat} (ho3 : 3 ≤ o) (ho : o ≤ 8) (ha3 : 3 ≤ a) (ha : a ≤ 8)
    (hb3 : 3 ≤ b) (hb : b ≤ 8) :
    Offs bytes (bc len c / 8) numBase invOff (lo len (.slot c 1)) (lo len (.slot c o)) (lo len (.slot c a))
      (lo len (.slot c b)) := by
  obtain f8 := h.slot_fit c (j := 8) (by decide)
  obtain g := bc_ge h.lower' c
  obtain e8 := bc_dvd len c
  obtain mo : ∀ j, 3 ≤ j → j ≤ 8 → numBase + 3 * st len c ≤ lo len (.slot c j) ∧
      lo len (.slot c j) + st len c ≤ lo len (.slot c 8) + st len c := fun j h3 h8 => by
    have := Nat.mul_le_mul_right (st len c) h3
    have := Nat.mul_le_mul_right (st len c) h8
    simp only [lo]; omega_arith
  obtain ⟨o1, o2⟩ := mo o ho3 ho
  obtain ⟨a1, a2⟩ := mo a ha3 ha
  obtain ⟨b1, b2⟩ := mo b hb3 hb
  obtain hb8 : 8 * (bc len c / 8) = bc len c := by omega_using [e8]
  have est : st len c = 2 * bc len c + 32 := rfl
  have nb : numBase = 3336 := rfl
  simp only [lo] at f8 o1 o2 a1 a2 b1 b2
  refine ⟨by omega_using [g], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [lo, scratchBytes, VG.Proof.Rsa.MontMul.Apart, invOff, hb8] <;> omega_arith

theorem mul_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : In Ex base bytes len args s) (c : Ctx) {o a b : Nat} (ho3 : 3 ≤ o) (ho : o ≤ 8) (ha3 : 3 ≤ a) (ha : a ≤ 8)
    (hb3 : 3 ≤ b) (hb : b ≤ 8)
    (hinv : (val32 s.mem base numBase (cwc len c) * w32 s.mem base invOff + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem base (lo len (.slot c b)) (cwc len c) < val32 s.mem base numBase (cwc len c)) :
    WP isa (mul c o a b) s fun t =>
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [⟨off base (lo len (.slot c o)), bc len c⟩, ⟨off base (lo len (.slot c 1)), 3 * bc len c + 56⟩,
        below (s.gpr .esp) 96] s.mem t.mem ∧
      val32 t.mem base (lo len (.slot c o)) (cwc len c) < val32 s.mem base numBase (cwc len c) ∧
      val32 t.mem base (lo len (.slot c o)) (cwc len c) * 2 ^ (8 * bc len c) % val32 s.mem base numBase (cwc len c) =
        val32 s.mem base (lo len (.slot c a)) (cwc len c) * val32 s.mem base (lo len (.slot c b)) (cwc len c) %
          val32 s.mem base numBase (cwc len c) := by
  have low := h.room.low
  have top := h.top
  obtain e8 := bc_dvd len c
  obtain hb8 : 8 * (bc len c / 8) = bc len c := by omega_using [e8]
  obtain sb : scratchBytes (bc len c / 8) = 3 * bc len c + 56 := by simp only [scratchBytes]; omega_using [e8]
  obtain p64 : 64 * (bc len c / 8) = 8 * bc len c := by omega_using [e8]
  obtain fEsp : (allocFrame 36 s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 36 := allocFrame_esp _ _
  obtain fEspN : ((allocFrame 36 s).gpr .esp).toNat = (s.gpr .esp).toNat - 36 := by
    rw [fEsp, VG.X86.sub_toNat (by omega_using [low])]
  obtain C := call_ok (is := mulArgs c o a b) h.scratch h.hbytes h.room (h.offs c ho3 ho ha3 ha hb3 hb)
    (by rw [cwc_eq]; exact hinv) (by rw [cwc_eq]; exact hB) (mulBody_noSp c o a b)
    (by
      have := mulArgs_ok (f := allocFrame 36 s) (len := len) (c := c) (o := o) (a := a) (b := b)
        (argAt_alloc h.width) (argAt_alloc (h.arg (i := wsLenArg) (by decide))) h.upper' (by omega_using [ho]) (by omega_using [ha])
        (by omega_using [hb]) (by omega_using [fEspN]) (by rw [allocFrame_wr, fEsp]; exact List.mem_cons_self ..)
      rwa [show (allocFrame 36 s).gpr .edi = s.gpr .edi from allocFrame_gpr _ _ (by decide)] at this)
  refine WP.mono C fun t ⟨cs, rd, wr, F, L, V⟩ => ⟨cs, rd, wr, ?_, ?_, ?_⟩
  · rw [hb8, sb] at F; exact F
  · rw [cwc_eq] at L; exact L
  · rw [cwc_eq, p64] at V; exact V

end VG.Proof.Bignum.X86.CrtRt

end

end

/-! # What a stage of private CRT at a run-time width changes

`frameR base sp ws`: ranges `ws` of the working space and the 96 bytes below
`sp`, where the calls write their arguments and return addresses. A number
apart from the ranges keeps its value (`frameR_val32`), and so do the inputs
(`In.keepF`): the arguments lie above `sp`.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Dsa.X86 (stackAddress stackValue)

/-- The regions a stage may change. -/
def frameR (base : Addr) (sp : BitVec 32) (ws : List (Nat × Nat)) : List Region :=
  below sp 96 :: ws.map fun p => ⟨off base p.1, p.2⟩

section
variable {base : Addr} {sp : BitVec 32} {ws ws' : List (Nat × Nat)} {m m' : Mem}

theorem frameR_mono (F : Frame (frameR base sp ws) m m') (h : ∀ p ∈ ws, p ∈ ws' := by decide) :
    Frame (frameR base sp ws') m m' :=
  F.mono fun r hr => by
    simp only [frameR, List.mem_cons, List.mem_map] at hr ⊢
    rcases hr with rfl | ⟨p, hp, rfl⟩
    · exact .inl rfl
    · exact .inr ⟨p, h p hp, rfl⟩

theorem frameR_of_outside {o n : Nat} (O : Outside base o n m m') (fit : o + n ≤ 2 ^ 64) (h : (o, n) ∈ ws) :
    Frame (frameR base sp ws) m m' :=
  (outside_frame O fit).mono fun r hr => by
    rw [List.mem_singleton.mp hr]
    simp only [frameR, List.mem_cons, List.mem_map]
    exact .inr ⟨_, h, rfl⟩

theorem frameR_of_mul {o n sc k : Nat} (F : Frame [⟨off base o, n⟩, ⟨off base sc, k⟩, below sp 96] m m')
    (ho : (o, n) ∈ ws) (hs : (sc, k) ∈ ws) : Frame (frameR base sp ws) m m' :=
  F.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [frameR, List.mem_cons, List.mem_map]
    rcases hr with rfl | rfl | rfl
    · exact .inr ⟨_, ho, rfl⟩
    · exact .inr ⟨_, hs, rfl⟩
    · exact .inl rfl

/-- A number apart from the ranges keeps its value. -/
theorem frameR_val32 {bytes : Nat} (F : Frame (frameR base sp ws) m m') (R : CallRoom sp base bytes)
    (nw : base.toNat + bytes ≤ 2 ^ 32) {d k : Nat} (hd : d + 4 * k ≤ bytes)
    (hws : ∀ p ∈ ws, d + 4 * k ≤ p.1 ∨ p.1 + p.2 ≤ d) (hfit : ∀ p ∈ ws, p.1 + p.2 ≤ bytes) :
    val32 m' base d k = val32 m base d k := by
  rw [← VG.Proof.Bignum.read_eq_val32, ← VG.Proof.Bignum.read_eq_val32]
  refine congrArg BitVec.toNat (F.read (r := ⟨off base d, 4 * k⟩) (Region.contains_self _ _) (fun r hr => ?_) (by omega_using [nw, hd]))
  simp only [frameR, List.mem_cons, List.mem_map] at hr
  rcases hr with rfl | ⟨p, hp, rfl⟩
  · refine (R.apart.sub_right ?_).symm
    have := Offset.sub base (d := d) (n := 4 * k) (e := 0) (k := bytes) (Nat.zero_le _) (by omega_using [hd])
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  · have := hws p hp
    have := hfit p hp
    exact Offset.disjoint base (by omega_arith) (by omega_using [nw, hd]) (by omega_using [nw, this])

end

section
variable {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {s t : State}

/-- The inputs hold after a stage that changes registers but `edi` and `esp`, and memory in its ranges. -/
theorem In.keepF (h : In Ex base bytes len args s) {regs : List Reg} (K : Keeps regs s t)
    (di : .edi ∉ regs) (sp : .esp ∉ regs) {ws : List (Nat × Nat)}
    (F : Frame (frameR base (s.gpr .esp) ws) s.mem t.mem) (hfit : ∀ p ∈ ws, p.1 + p.2 ≤ bytes) :
    In Ex base bytes len args t := by
  have hc := h
  have nw := hc.scratch.nowrap
  have low := hc.room.low
  have top := hc.top
  have esp : t.gpr .esp = s.gpr .esp := K.1 _ sp
  refine ⟨hc.scratch.of_keeps K di sp, hc.lower, hc.upper, fun i hi => ⟨(hc.stack i hi).stack.keep K sp, ?_⟩,
    hc.outLen, by rw [esp]; exact hc.room, by rw [esp]; exact hc.top, h.need, h.hbase, h.hbytes,
    by rw [K.2.1, K.2.2]; exact h.extra⟩
  have A := hc.stack i hi
  rw [← A.value]
  unfold stackValue
  rw [show stackAddress t i = stackAddress s i by simp only [stackAddress, esp]]
  refine F.readW (r := ⟨stackAddress s i, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [frameR, List.mem_cons, List.mem_map] at hr
  rcases hr with rfl | ⟨p, hp, rfl⟩
  · have ea : (stackAddress s i).toNat = (s.gpr .esp).toNat + (4 + 4 * i) := by
      simp only [stackAddress, addr, PublicRt.setWidth_toNat, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega_using [top, hi]
    have eb : ((s.gpr .esp - BitVec.ofNat 32 96).setWidth 64).toNat = (s.gpr .esp).toNat - 96 := by
      rw [PublicRt.setWidth_toNat, VG.X86.sub_toNat (by omega_using [low])]
    exact (Region.disjoint_of_le (r₁ := below (s.gpr .esp) 96) (.inl (by dsimp only; rw [eb, ea]; omega_using [low]))
      (by dsimp only; rw [eb]; omega_using []) (by dsimp only; rw [ea]; omega_using [hi])).symm
  · refine A.stack.apart.sub_right ?_
    have := hfit p hp
    have := Offset.sub base (d := p.1) (n := p.2) (e := 0) (k := bytes) (Nat.zero_le _) (by omega_using [this])
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this

end

end VG.Proof.Bignum.X86.CrtRt
