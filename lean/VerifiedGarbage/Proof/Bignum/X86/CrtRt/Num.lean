module

public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Load
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Dsa.Frame
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.SelectX
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops2
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.In

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
  have ce := cb_eq (len := len) N
  unfold zero
  simp only [List.append_assoc]
  refine WP.seq (ptrTo_ok (r := .ebp) (t := .edx) (by decide) (by decide) h.edi h.width h.upper' (by omega_using [hx, bl])
    fun u K m p => ?_)
  have hu := h.regs K m
  refine cntTo_ok (r := .ecx) hu.width h.upper' N.extra fun v Kv mv cv => wp_movS rfl fun w uw _ => WP.block_nil ?_
  have Kw : Keeps [.eax, .ecx, .edx, .ebp] s w :=
    ((K.mono (by decide)).trans (Kv.mono (by decide))).trans (uw.keeps.mono (by decide))
  have mw : w.mem = s.mem := by rw [uw.mem, mv, m]
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
  have ce := cb_eq (len := len) N
  have cp := cw_pos (n := n) h.lower'
  unfold setSmall
  refine WP.seq (WP.mono (zero_ok h N hx) fun u ⟨O, V, K⟩ => ?_)
  have hu := h.keep K (by decide) (by decide) (O.mono (Nat.zero_le _) (by omega_using [hx]))
  refine ptrTo_ok (r := .eax) (t := .edx) (by decide) (by decide) hu.edi hu.width h.upper' (by omega_using [hx, bl])
    fun w Kw mw pw => wp_movS rfl fun w₁ u₁ _ => ?_
  have hw₁ := h.ws.of_keeps (K.trans ((Kw.mono (by decide)).trans (u₁.keeps.mono (by decide))))
  have p₁ : PtrAt w₁ base .eax (lo len x) := by rw [PtrAt, u₁.other _ (by decide)]; exact pw
  refine wp_storeS (ea_ptr hw₁ p₁ (d := 0) (by omega_using [hx, ce, cp]))
    (ws_write hw₁ (y := lo len x + 0) (n := 4) (by omega_using [hx, ce, cp])) fun t mt => WP.block_nil ?_
  have mw₁ : w₁.mem = u.mem := by rw [u₁.mem, mw]
  refine ⟨?_, ?_, (K.trans ((Kw.mono (by decide)).trans (u₁.keeps.mono (by decide)))).trans (mt.keeps _)⟩
  · rw [mt.mem, mw₁, Nat.add_zero]
    exact O.trans ((writeW32_outside _ _ _ (by omega_using [hx, bl])).mono (by omega_using []) (by omega_using [ce, cp]))
  · rw [mt.mem, mw₁, Nat.add_zero, u₁.gpr]
    obtain ⟨k, hk⟩ : ∃ k, cw len n = k + 1 := ⟨cw len n - 1, by omega_using [cp]⟩
    rw [hk] at V ⊢
    have V' := V
    rw [val32] at V'
    rw [val32, w32_write_self]
    have rest : val32 (u.mem.writeW (off base (lo len x)) (BitVec.ofNat 32 v)) base (lo len x + 4) k =
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
  have ce := cb_eq (len := len) N
  unfold select
  simp only [List.append_assoc]
  refine WP.seq (ptrTo_ok (r := .ebp) (t := .edx) (by decide) (by decide) h.edi h.width h.upper' (by omega_using [hx, bl])
    fun u K m p => ?_)
  have hu := h.regs K m
  refine ptrTo_ok (r := .ebx) (t := .edx) (by decide) (by decide) hu.edi hu.width h.upper' (by omega_using [hd, bl])
    fun v Kv mv pv => ?_
  have hv := hu.regs Kv mv
  rw [← List.append_nil (cntTo n .edi)]
  refine cntTo_ok (r := .edi) hv.width h.upper' N.extra fun w Kw mw cw' => WP.block_nil ?_
  have Kw' : Keeps [.ebx, .edx, .ebp, .edi] s w :=
    ((K.mono (by decide)).trans (Kv.mono (by decide))).trans (Kw.mono (by decide))
  have mw' : w.mem = s.mem := by rw [mw, mv, m]
  refine WP.seq (WP.mono (selectLoop_ok (h.ws.of_keeps Kw') (x := lo len x) (d := lo len d) (N := cw len n) k
    (cw_pos h.lower') (by omega_using [hx, ce]) (by omega_using [hd, ce]) (by omega)
    (by rw [PtrAt, Kw.1 _ (by decide), Kv.1 _ (by decide)]; exact p)
    (by rw [PtrAt, Kw.1 _ (by decide)]; exact pv)
    (cnt_toNat h.upper' N cw')
    (by rw [Kw.1 _ (by decide), Kv.1 _ (by decide), K.1 _ (by decide)]; exact hk))
    fun t ⟨O, V, _, Kt⟩ => ?_)
  have Kall : Keeps [.eax, .ebx, .edx, .ebp, .edi] s t := (Kw'.mono (by decide)).trans Kt
  have Oall : Outside base 0 bytes s.mem t.mem := by rw [← mw']; exact O.mono (Nat.zero_le _) (by omega_using [hd, ce])
  refine wp_movS ((h.stack 16 (by decide)).keep Kall (by decide) Oall).readSrc fun t₁ u₁ _ => WP.block_nil ?_
  have e : t₁.gpr .edi = s.gpr .edi := by rw [u₁.gpr]; exact h.edi_eq
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
  have ce := cb_eq (len := len) N
  unfold selectX
  simp only [List.append_assoc]
  refine WP.seq (ptrTo_ok (r := .ebp) (t := .edx) (by decide) (by decide) h.edi h.width h.upper' (by omega_using [hx, bl])
    fun u K m p => ?_)
  have hu := h.regs K m
  refine ptrTo_ok (r := .ebx) (t := .edx) (by decide) (by decide) hu.edi hu.width h.upper' (by omega_using [hd, bl])
    fun v Kv mv pv => ?_
  have hv := hu.regs Kv mv
  rw [← List.append_nil (cntTo n .edi)]
  refine cntTo_ok (r := .edi) hv.width h.upper' N.extra fun w Kw mw cw' => WP.block_nil ?_
  have Kw' : Keeps [.ebx, .edx, .ebp, .edi] s w :=
    ((K.mono (by decide)).trans (Kv.mono (by decide))).trans (Kw.mono (by decide))
  have mw' : w.mem = s.mem := by rw [mw, mv, m]
  refine WP.seq (WP.mono (selectLoopX_ok (h.ws.of_keeps Kw') (x := lo len x) (d := lo len d) (N := cw len n) k
    h4 (by omega_using [hx, ce]) (by omega_using [hd, ce]) (by omega)
    (by rw [PtrAt, Kw.1 _ (by decide), Kv.1 _ (by decide)]; exact p)
    (by rw [PtrAt, Kw.1 _ (by decide)]; exact pv)
    (cnt_toNat h.upper' N cw')
    (by rw [Kw.1 _ (by decide), Kv.1 _ (by decide), K.1 _ (by decide)]; exact hk))
    fun t ⟨O, V, _, _, Kt⟩ => ?_)
  have Kall : Keeps [.eax, .ebx, .edx, .ebp, .edi] s t := (Kw'.mono (by decide)).trans Kt
  have Oall : Outside base 0 bytes s.mem t.mem := by rw [← mw']; exact O.mono (Nat.zero_le _) (by omega_using [hd, ce])
  refine wp_movS ((h.stack 16 (by decide)).keep Kall (by decide) Oall).readSrc fun t₁ u₁ _ => WP.block_nil ?_
  have e : t₁.gpr .edi = s.gpr .edi := by rw [u₁.gpr]; exact h.edi_eq
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
  have hu := h.regs uu.keeps uu.mem
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
  have N := one_ok .half
  have ce := cb_eq (len := len) N
  have cb1 : cb len (one .half) = bc len .half := by simp [cb, one]
  have bhl := bc_le h.upper' .half
  unfold copyHigh
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.seq (wp_movS rfl fun u₀ a₀ _ => ?_)
  have h₀ := h.regs a₀.keeps a₀.mem
  refine ptrTo_ok (r := .ebp) (t := .edx) (by decide) (by decide) h₀.edi h₀.width h.upper' (by omega_using [hx, bl])
    fun u₁ K₁ m₁ p₁ => ?_
  have h₁ := h₀.regs K₁ m₁
  refine widthC_ok (k := 0) h₁.width h.upper' fun u₂ K₂ m₂ e₂ => wp_addS rfl fun u₃ a₃ _ => ?_
  have K₃ : Keeps [.ebp, .edx] u₁ u₃ := (K₂.mono (by decide)).trans (a₃.keeps.mono (by decide))
  have m₃ : u₃.mem = u₁.mem := by rw [a₃.mem, m₂]
  have p₃ : PtrAt u₃ base .ebp (lo len (.slot .wide j) + bc len .half) := by
    rw [PtrAt, a₃.gpr, K₂.1 _ (by decide), e₂, ptr_add p₁, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := bc len .half) (by omega_using [bhl])]
  have h₃ := h₁.regs K₃ m₃
  refine ptrTo_ok (r := .ebx) (t := .edx) (by decide) (by decide) h₃.edi h₃.width h.upper' (by omega_using [hd, bl])
    fun u₄ K₄ m₄ p₄ => ?_
  have h₄ := h₃.regs K₄ m₄
  rw [← List.append_nil (cntTo (one .half) .edi)]
  refine cntTo_ok (r := .edi) h₄.width h.upper' N.extra fun u₅ K₅ m₅ c₅ => WP.block_nil ?_
  have Kw' : Keeps [.ebx, .ecx, .edx, .ebp, .edi] s u₅ :=
    ((((a₀.keeps.mono (by decide)).trans (K₁.mono (by decide))).trans (K₃.mono (by decide))).trans
      (K₄.mono (by decide))).trans (K₅.mono (by decide))
  have mw' : u₅.mem = s.mem := by rw [m₅, m₄, m₃, m₁, a₀.mem]
  have ecx₅ : u₅.gpr .ecx = cmask true := by
    rw [K₅.1 _ (by decide), K₄.1 _ (by decide), K₃.1 _ (by decide), K₁.1 _ (by decide), a₀.gpr]; rfl
  refine WP.seq (WP.mono (selectLoop_ok (h.ws.of_keeps Kw') (x := lo len (.slot .wide j) + bc len .half)
    (d := lo len (.slot .half d)) (N := cw len (one .half)) true
    (by have := bc_ge h.lower' .half; omega) (by omega) (by omega) (.inl (by omega))
    (by rw [PtrAt, K₅.1 _ (by decide), K₄.1 _ (by decide)]; exact p₃)
    (by rw [PtrAt, K₅.1 _ (by decide)]; exact p₄)
    (cnt_toNat h.upper' N c₅) ecx₅)
    fun t ⟨O, V, _, Kt⟩ => ?_)
  have Kall : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s t := (Kw'.mono (by decide)).trans (Kt.mono (by decide))
  have Oall : Outside base 0 bytes s.mem t.mem := by rw [← mw']; exact O.mono (Nat.zero_le _) (by omega)
  refine wp_movS ((h.stack 16 (by decide)).keep Kall (by decide) Oall).readSrc fun t₁ u₁ _ => WP.block_nil ?_
  have e : t₁.gpr .edi = s.gpr .edi := by rw [u₁.gpr]; exact h.edi_eq
  refine ⟨by rw [u₁.mem, ← mw', show 4 * cw len (one .half) = bc len .half by omega] at *; exact O,
    by rw [u₁.mem, V, mw']; rfl,
    PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .ecx, .edx, .ebp]) (Kall.trans (u₁.keeps.mono (by decide))) e⟩

end

end VG.Proof.Bignum.X86.CrtRt
