module

public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.MulEnv
public import VerifiedGarbage.Proof.Mont.X86.ExponentShift
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.ByteWords
public import VerifiedGarbage.Proof.Mont.X86.ContextMath
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Impl.Bignum.X86.SparseExponent
public import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.ExponentWord
import VerifiedGarbage.Proof.Mont.X86.Ops

/-! ### `Bignum.X86.PublicRt.Seed`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86.ExponentBits`, which this module and modules that import it used -/

section

/-! # The tests of the public exponent's low bit and of what is left of it -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Bignum.X86.PublicContext

theorem sub0 (x : BitVec 32) : x - 0 = x := BitVec.sub_zero x

theorem bitTest_ok {s : State} {base : Addr} {bytes : Nat} (hs : Scr s base bytes)
    (hb : 128 + 4 ≤ bytes) :
    WP isa (.block bitTest) s fun t =>
      t.mem = s.mem ∧ Keeps [.ecx] s t ∧ t.zf = some (decide (w32 s.mem base 128 % 2 = 0)) := by
  unfold bitTest exponentOffset
  refine wp_movS (readSrc_sc hs hb) fun s₁ u₁ _ => ?_
  refine wp_logicS (.inl rfl) rfl fun s₂ u₂ => ?_
  refine wp_cmpS rfl fun t ft zt => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [ft.mem, u₂.mem, u₁.mem]
  · exact ((u₁.keeps.trans (u₂.keeps)).trans (ft.keeps _))
  · rw [zt, u₂.gpr, u₁.gpr, ite_eq_left rfl, sub0]
    congr 1
    by_cases h : w32 s.mem base 128 % 2 = 0
    · rw [decide_eq_true h, beq_iff_eq]
      apply BitVec.eq_of_toNat_eq
      rw [lowBit_nat]
      exact h
    · rw [decide_eq_false h]
      apply beq_false_of_ne
      intro e
      have := congrArg BitVec.toNat e
      rw [lowBit_nat] at this
      exact h this

theorem exponentLeft_ok {s : State} {base : Addr} {bytes : Nat} (hs : Scr s base bytes)
    (hb : 128 + 8 ≤ bytes) :
    WP isa (.block exponentLeft) s fun t =>
      t.mem = s.mem ∧ Keeps [.eax] s t ∧ t.zf = some (decide (val32 s.mem base 128 2 = 0)) := by
  unfold exponentLeft exponentOffset
  refine wp_movS (readSrc_sc hs (by omega_using [hb])) fun s₁ u₁ _ => ?_
  have hs₁ := hs.of_keeps u₁.keeps (by decide)
  refine wp_orS (readSrc_sc hs₁ (by omega_using [hb])) fun s₂ u₂ => ?_
  refine wp_cmpS rfl fun t ft zt => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [ft.mem, u₂.mem, u₁.mem]
  · exact ((u₁.keeps.trans (u₂.keeps)).trans (ft.keeps _))
  · rw [zt, u₂.gpr, u₁.gpr, u₁.mem, sub0]
    congr 1
    have hv : val32 s.mem base 128 2 = w32 s.mem base 128 + 2 ^ 32 * w32 s.mem base (128 + 4) := by
      simp only [val32]; omega_using []
    rw [hv]
    have key : (s.mem.readW (off base 128) 32 ||| s.mem.readW (off base (128 + 4)) 32) = 0 ↔
        w32 s.mem base 128 + 2 ^ 32 * w32 s.mem base (128 + 4) = 0 := by
      rw [show (0 : BitVec 32) = 0#32 from rfl, BitVec.or_eq_zero_iff]
      constructor
      · rintro ⟨h₁, h₂⟩
        simp only [w32, h₁, h₂, BitVec.toNat_zero]
      · intro z
        exact ⟨BitVec.eq_of_toNat_eq (by change w32 s.mem base 128 = 0; omega_using [z]),
          BitVec.eq_of_toNat_eq (by change w32 s.mem base (128 + 4) = 0; omega_using [z])⟩
    exact Bool.eq_iff_iff.mpr (by rw [beq_iff_eq, decide_eq_true_iff]; exact key)

end VG.Proof.Bignum.X86.PublicContext

end

end

/-! # Seeding public exponentiation from its converted input -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicRt
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86

theorem seedCopyLoop_ok {t₀ : State} {W : Addr} {L : Nat} (hw : Ws t₀ W L)
    {x y N : Nat} (hN : 0 < N) (apart : y + 4 * N ≤ x)
    (hx : x + 4 * N ≤ L) (hy : y + 4 * N ≤ L) (hebp : PtrAt t₀ W .ebp x) (hesi : PtrAt t₀ W .esi y)
    (hecx : (t₀.gpr .ecx).toNat = 4 * N) :
    WP isa (.loop (.block [.mov .eax (.mem (at_ .esi 0)), .store (at_ .ebp 0) .eax, .alu .add .esi (.imm 4),
      .alu .add .ebp (.imm 4), .alu .sub .ecx (.imm 4)]) .ne) t₀
      fun u => Outside W x (4 * N) t₀.mem u.mem ∧ val32 u.mem W x N = val32 t₀.mem W y N ∧
        Keeps [.eax, .ecx, .ebp, .esi] t₀ u := by
  have hwn := hw.nowrap
  refine WP.mono (countLoop hN (fun j t => Keeps [.eax, .ecx, .ebp, .esi] t₀ t ∧ PtrAt t W .ebp (x + 4 * j) ∧
      PtrAt t W .esi (y + 4 * j) ∧ (t.gpr .ecx).toNat = 4 * (N - j) ∧ Outside W x (4 * j) t₀.mem t.mem ∧
      val32 t.mem W x j = val32 t₀.mem W y j) ?_
    ⟨Keeps.refl _ _, by simpa using hebp, by simpa using hesi, by simpa using hecx, Outside.refl _ _ _ _, rfl⟩)
    fun u ⟨K, _, _, _, O, V⟩ => ⟨O, V, K⟩
  rintro j t hj ⟨Kt, ebp, esi, ecx, O, V⟩
  obtain ht := hw.of_keeps Kt
  refine wp_movS (readSrc_ptr ht esi (d := 0) (by omega_using [hy, hj])) fun s₁ u₁ _ => ?_
  obtain ht₁ := ht.of_keeps u₁.keeps
  obtain ebp₁ : PtrAt s₁ W .ebp (x + 4 * j) := by rw [PtrAt, u₁.other _ (by decide)]; exact ebp
  refine wp_storeS (ea_ptr ht₁ ebp₁ (d := 0) (by omega_using [hx, hj]))
    (ws_write ht₁ (y := x + 4 * j + 0) (n := 4) (by omega_using [hx, hj])) fun s₂ m₂ => ?_
  refine wp_addS rfl fun s₃ u₃ _ => wp_addS rfl fun s₄ u₄ _ => wp_subZ rfl fun s₅ u₅ z₅ => WP.block_nil ?_
  obtain ⟨c₁, c₂⟩ := count_zf ecx hj
  obtain ecx₄ : s₄.gpr .ecx = t.gpr .ecx := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide)]
  -- The source word, unchanged since the start.
  obtain word : (t.mem.readW (off W (y + 4 * j + 0)) 32).toNat = w32 t₀.mem W (y + 4 * j) := by
    rw [Nat.add_zero]
    exact O.w32 (.inl (by omega_arith)) (by omega_arith)
  refine ⟨⟨(((Kt.widen (u₁.keeps.widen (m₂.keeps []))).widen u₃.keeps).widen u₄.keeps).widen u₅.keeps,
    ?_, ?_, by rw [u₅.gpr, ecx₄]; exact c₁, ?_, ?_⟩, by rw [z₅, ecx₄, c₂]⟩
  · rw [PtrAt, u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide)]
    exact ptr4 ebp
  · rw [PtrAt, u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, m₂.gpr, u₁.other _ (by decide)]
    exact ptr4 esi
  · rw [u₅.mem, u₄.mem, u₃.mem, m₂.mem, u₁.mem, Nat.add_zero]
    exact (O.mono (Nat.le_refl _) (by omega_using [])).trans
      ((writeW32_outside _ _ _ (by omega_using [hx, hj, hwn])).mono (by omega_using []) (by omega_using []))
  · rw [u₅.mem, u₄.mem, u₃.mem, m₂.mem, u₁.mem, Nat.add_zero, val32_store hwn (by omega_using [hx, hj]), V,
      u₁.gpr, val32_succ t₀.mem W y, ← word, Nat.add_zero]


theorem seedCopy_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : RtIn base bytes len args s) :
    WP isa seedCopy s fun u => Outside base (numAt len 2) (wb len) s.mem u.mem ∧
      val32 u.mem base (numAt len 2) (nw len) = val32 s.mem base (numAt len 1) (nw len) ∧
      Keeps [.eax, .ecx, .ebp, .esi] s u := by
  obtain fit := (h.fits (j := 2) (by decide)).1
  have dims := h.dimensions
  obtain wbe := wb_eq len
  obtain e12 : numAt len 2 = numAt len 1 + wb len := numAt_succ len 1
  obtain hw := wb_le h.upper
  unfold seedCopy
  refine WP.seq (slotPtr_ok (r := .esi) (t := .ecx) (j := 1) (by decide) (by decide)
    h.edi h.width h.upper (by omega_arith) fun v K m ps _ => ?_)
  obtain hv := h.keep K (by decide) (by decide) (by rw [m]; exact Outside.refl _ _ _ _)
  refine slotPtr_ok (r := .ebp) (t := .ecx) (j := 2) (by decide) (by decide)
    hv.edi hv.width h.upper (by omega_arith) fun t₀ K₀ m₀ pd c => ?_
  refine WP.block_nil ?_
  obtain Kstart : Keeps [.ecx, .ebp, .esi] s t₀ := (K.mono (by decide)).trans (K₀.mono (by decide))
  obtain mstart : t₀.mem = s.mem := m₀.trans m
  obtain psrc : PtrAt t₀ base .esi (numAt len 1) := by rw [PtrAt, K₀.1 _ (by decide)]; exact ps
  obtain count : (t₀.gpr .ecx).toNat = 4 * nw len := by
    rw [c, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith), ← wbe]
  refine WP.mono (seedCopyLoop_ok (h.ws.of_keeps Kstart) (N := nw len) (by simp only [nw]; omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) pd psrc count) fun u ⟨O, V, K⟩ => ?_
  rw [mstart, ← wbe] at O
  rw [mstart] at V
  exact ⟨O, V, (Kstart.mono (by decide)).trans K⟩

/-- An odd low word is nonzero, so decrementing it needs no high-word borrow. -/
theorem seedConsume_ok {s : State} {base : Addr} {bytes : Nat} (h : Scr s base bytes)
    (hb : 136 ≤ bytes) (odd : val32 s.mem base 128 2 % 2 = 1) :
    WP isa (.block seedConsume) s fun u =>
      Outside base 128 4 s.mem u.mem ∧ val32 u.mem base 128 2 = val32 s.mem base 128 2 - 1 ∧
      Keeps [.eax] s u := by
  obtain parity : val32 s.mem base 128 2 % 2 = w32 s.mem base 128 % 2 := VG.Proof.Mont.X86.Dynamic.val32_parity s.mem base 128 1
  have hn := h.nowrap
  obtain lo : 0 < w32 s.mem base 128 := by omega_arith
  unfold seedConsume
  refine wp_movS (readSrc_sc h (by omega_arith)) fun u₁ e₁ _ => wp_subS rfl fun u₂ e₂ _ => ?_
  obtain K := e₁.keeps.trans e₂.keeps
  obtain h₂ := h.of_keeps K (by decide)
  refine wp_storeS (h₂.ea (by omega_arith)) (h₂.write (by omega_arith)) fun t mt => WP.block_nil ?_
  obtain mv : u₂.mem = s.mem := e₂.mem.trans e₁.mem
  obtain ev : u₂.gpr .eax = s.mem.readW (off base 128) 32 - 1 := by rw [e₂.gpr, e₁.gpr]
  obtain O := writeW32_outside s.mem base (s.mem.readW (off base 128) 32 - 1) (by decide : 128 + 4 ≤ 2 ^ 64)
  refine ⟨by rw [mt.mem, mv, ev]; exact O, ?_, K.trans (mt.keeps _)⟩
  rw [mt.mem, mv, ev]
  obtain tail := O.w32 (d := 132) (.inr (by omega_arith)) (by omega_arith)
  obtain head := w32_write_self s.mem base 128 (s.mem.readW (off base 128) 32 - 1)
  obtain sub : (s.mem.readW (off base 128) 32 - 1).toNat = w32 s.mem base 128 - 1 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact lo)]
    rfl
  simp only [val32, Nat.mul_zero, Nat.add_zero, Nat.reduceAdd]
  rw [head, tail, sub]
  omega_arith

/-- Seeding changes only the accumulator and, for odd exponents, their low word. -/
theorem seed_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {M : Nat}
    (E : Env base bytes len args M s) (hbytes : bytes = (args 9).toNat * 8)
    (hX : val32 s.mem base (numAt len 1) (nw len) < M)
    (hO : val32 s.mem base (numAt len 3) (nw len) < M) :
    WP isa seed s fun t =>
      Env base bytes len args M t ∧ Frame (Chg base len bytes (s.gpr .esp)) s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .esi] s t ∧ val32 t.mem base (numAt len 2) (nw len) < M ∧
      (∀ j ≤ 4, j ≠ 2 → val32 t.mem base (numAt len j) (nw len) = val32 s.mem base (numAt len j) (nw len)) ∧
      val32 t.mem base 128 2 = val32 s.mem base 128 2 - val32 s.mem base 128 2 % 2 ∧
      (if val32 s.mem base 128 2 % 2 = 1 then
        val32 t.mem base (numAt len 2) (nw len) = val32 s.mem base (numAt len 1) (nw len)
       else val32 t.mem base (numAt len 2) (nw len) * 2 ^ (32 * nw len) % M =
        val32 s.mem base (numAt len 4) (nw len) * val32 s.mem base (numAt len 3) (nw len) % M) := by
  have h := E.pi
  have dims := h.dimensions
  obtain wbe := wb_eq len
  obtain f2 := (h.fits (j := 2) (by decide)).1
  obtain f5 := (h.fits (j := 5) (by decide)).2
  obtain e1 : numAt len 1 = 256 + wb len := by simp only [numAt, numOff] <;> omega_arith
  obtain e2 : numAt len 2 = 256 + 2 * wb len := by simp only [numAt, numOff] <;> omega_arith
  obtain e3 : numAt len 3 = 256 + 3 * wb len := by simp only [numAt, numOff] <;> omega_arith
  obtain e5 : numAt len 5 = 256 + 5 * wb len := by simp only [numAt, numOff] <;> omega_arith
  unfold seed
  refine WP.seq (WP.mono (PublicContext.bitTest_ok h.scratch (by omega_arith)) fun u ⟨mu, Ku, Zu⟩ => ?_)
  obtain Eu := E.keep Ku (by decide) (by decide) (by rw [mu]; exact Frame.refl _ _)
  obtain par : val32 s.mem base 128 2 % 2 = w32 s.mem base 128 % 2 := VG.Proof.Mont.X86.Dynamic.val32_parity s.mem base 128 1
  by_cases even : val32 s.mem base 128 2 % 2 = 0
  · refine WP.ite true (by change u.zf = _; rw [Zu, decide_eq_true (by omega_arith)])
      (fun _ => ?_) (fun e => nomatch e)
    refine WP.mono (mulRaw_ok Eu hbytes (o := 2) (a := 4) (b := 3) (by decide) (by decide)
      (by decide) (by decide) (by rw [mu]; exact hO)) fun t ⟨Et, Ct, Kt, Ft, Lt, Vt⟩ => ?_
    refine ⟨Et, by rw [Ku.1 _ (by decide), mu] at Ct; exact Ct,
      (Ku.mono (by decide)).trans (Kt.mono (by decide)), Lt, ?_, ?_, ?_⟩
    · intro j hj hj2
      obtain sep : numAt len j + 4 * nw len ≤ numAt len 2 ∨ numAt len 2 + wb len ≤ numAt len j := by
        obtain hjc : j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4 := by omega_arith
        rcases hjc with rfl | rfl | rfl | rfl <;> simp only [numAt, numOff] <;> omega_arith
      rw [mulFrame_val32 Eu.room h.scratch.nowrap Ft sep (by have hjw := Nat.mul_le_mul_right (wb len) hj; simp only [numAt] at *; omega_arith)
        (by have := (h.fits (by omega_arith : j ≤ 7)).1; omega_arith) f2 f5, mu]
    · rw [← read_eq_val32, mulFrame_hdr Eu.room h.scratch.nowrap Ft (by decide) (by omega_arith) f2 f5, mu,
        read_eq_val32, even, Nat.sub_zero]
    · rw [mu] at Vt
      rw [ite_eq_right (by omega_arith)]
      exact Vt
  · have odd : val32 s.mem base 128 2 % 2 = 1 := by omega_arith
    refine WP.ite false (by change u.zf = _; rw [Zu, decide_eq_false (by omega_arith)])
      (fun e => nomatch e) (fun _ => ?_)
    refine WP.seq (WP.mono (seedCopy_ok Eu.pi) fun v ⟨Ov, Vv, Kv⟩ => ?_)
    obtain Cv := Outside.chg (len := len) (bytes := bytes) (sp := u.gpr .esp) Ov (.inr ⟨by omega_arith, f2⟩)
    obtain Ev := Eu.keep Kv (by decide) (by decide) Cv
    obtain Wv : val32 v.mem base 128 2 = val32 s.mem base 128 2 := by rw [Ov.val32 (.inl (by omega_arith)) (by omega_arith), mu]
    refine WP.mono (seedConsume_ok Ev.pi.scratch (by omega_arith) (by rw [Wv]; exact odd)) fun t ⟨Ot, Wt, Kt⟩ => ?_
    obtain Ct := Outside.chg (len := len) (bytes := bytes) (sp := v.gpr .esp) Ot (.inl ⟨by decide, by decide⟩)
    obtain Et := Ev.keep Kt (by decide) (by decide) Ct
    refine ⟨Et, ?_, (Ku.mono (by decide)).trans ((Kv.mono (by decide)).trans (Kt.mono (by decide))),
      ?_, ?_, by rw [Wt, Wv, odd], ?_⟩
    · rw [Ku.1 _ (by decide), mu] at Cv
      rw [Kv.1 _ (by decide), Ku.1 _ (by decide)] at Ct
      exact Cv.trans Ct
    · rw [Ot.val32 (.inr (by omega_arith)) (by omega_arith), Vv, mu]; exact hX
    · intro j hj hj2
      obtain fj := (h.fits (by omega_arith : j ≤ 7)).1
      obtain nj : 256 ≤ numAt len j := by simp only [numAt, numOff] <;> omega_arith
      obtain sep : numAt len j + 4 * nw len ≤ numAt len 2 ∨ numAt len 2 + wb len ≤ numAt len j := by
        obtain hjc : j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4 := by omega_arith
        rcases hjc with rfl | rfl | rfl | rfl <;> simp only [numAt, numOff] <;> omega_arith
      rw [Ot.val32 (.inr (by omega_arith)) (by omega_arith), Ov.val32 sep (by omega_arith), mu]
    · rw [ite_eq_left odd, Ot.val32 (.inr (by omega_arith)) (by omega_arith), Vv, mu]

end VG.Proof.Bignum.X86.PublicRt

end

end

/-! ### `Bignum.X86.PublicRt.Exp`, which only this module used -/

section

/-! # A step of the exponentiation of public RSA at a run-time width

`sparseRound`: with the result `y R` (number 2), the base `b R` (number 1)
and the exponent's remaining bits `E` (two words at 128), the result times
the base where `E` is odd (`product_ok`), `E` halved, the base squared only if another bit remains, and
`zf` set once `E` is gone (`sparseRound_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Mont.X86.Dynamic

theorem Env.pos {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {M : Nat} {s : State}
    (E : Env base bytes len args M s) : 0 < M := by
  have := E.inv
  rcases Nat.eq_zero_or_pos M with rfl | h
  · simp at this
  · exact h

/-- The product of a set bit: the result `y R` times the base where the exponent is odd. -/
theorem product_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {M : Nat}
    (E : Env base bytes len args M s) (hbytes : bytes = (args 9).toNat * 8)
    {y b : Nat} (hY : val32 s.mem base (numAt len 2) (nw len) = y * 2 ^ (32 * nw len) % M)
    (hX : val32 s.mem base (numAt len 1) (nw len) = b * 2 ^ (32 * nw len) % M) :
    WP isa (.seq (.block PublicContext.bitTest) (.ite .e (.block []) (PublicRt.mul 2 2 1))) s fun t =>
      Env base bytes len args M t ∧ Frame (Chg base len bytes (s.gpr .esp)) s.mem t.mem ∧
      val32 t.mem base (numAt len 2) (nw len) =
        (if val32 s.mem base 128 2 % 2 = 1 then y * b else y) * 2 ^ (32 * nw len) % M ∧
      val32 t.mem base (numAt len 1) (nw len) = val32 s.mem base (numAt len 1) (nw len) ∧
      val32 t.mem base 128 2 = val32 s.mem base 128 2 ∧ Keeps [.eax, .ecx, .edx] s t ∧
      val32 t.mem base (numAt len 3) (nw len) = val32 s.mem base (numAt len 3) (nw len) := by
  have h := E.pi
  have nw' := h.scratch.nowrap
  have dims := h.dimensions
  have wbe := wb_eq len
  have hM := E.pos
  have f5 := (h.fits (j := 5) (by decide)).2
  have f2 := (h.fits (j := 2) (by decide)).1
  have e1 : numAt len 1 = 256 + wb len := by simp only [numAt, numOff] <;> omega_using []
  have e2 : numAt len 2 = 256 + 2 * wb len := by simp only [numAt, numOff] <;> omega
  have e3 : numAt len 3 = 256 + 3 * wb len := by simp only [numAt, numOff] <;> omega
  have e5 : numAt len 5 = 256 + 5 * wb len := by simp only [numAt, numOff] <;> omega
  refine WP.seq (WP.mono (PublicContext.bitTest_ok h.scratch (by omega_using [f2, e2])) fun u ⟨M₁, K₁, Z₁⟩ => ?_)
  have E₁ := E.keep K₁ (by decide) (by decide) (by rw [M₁]; exact Frame.refl _ _)
  have K₁' : Keeps [.eax, .ecx, .edx] s u := K₁.mono (by decide)
  have par : val32 s.mem base 128 2 % 2 = w32 s.mem base 128 % 2 := val32_parity _ _ _ _
  by_cases bit : w32 s.mem base 128 % 2 = 0
  · refine WP.ite true (by change u.zf = _; rw [Z₁, decide_eq_true bit]) (fun _ => WP.block_nil ?_)
      (fun e => nomatch e)
    refine ⟨E₁, by rw [M₁]; exact Frame.refl _ _, ?_, by rw [M₁], by rw [M₁], K₁', by rw [M₁]⟩
    rw [M₁, hY, ite_eq_right (by omega_using [par, bit])]
  · refine WP.ite false (by change u.zf = _; rw [Z₁, decide_eq_false bit]) (fun e => nomatch e)
      (fun _ => ?_)
    refine WP.mono (mulEnv_ok E₁ hbytes (o := 2) (a := 2) (b := 1) (by decide) (by decide) (by decide)
      (by decide) (x := y) (y := b) (by rw [M₁, hY, Nat.mod_mod]) (by rw [M₁, hX, Nat.mod_mod])
      (by rw [M₁, hX]; exact Nat.mod_lt _ hM)) fun t ⟨Et, Ct, cst, Ft, Tt⟩ => ?_
    have sp₁ : u.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
    refine ⟨Et, ?_, ?_, ?_, ?_, K₁'.trans cst, ?_⟩
    · rw [← M₁, ← sp₁]; exact Ct
    · rw [Tt, ite_eq_left (by omega_using [par, bit])]
    · rw [mulFrame_val32 E₁.room nw' Ft (.inl (by omega_using [wbe, e1, e2])) (by omega_using [wbe, e1, e5]) (by omega_using [wbe, f2, e1, e2]) f2 f5, M₁]
    · rw [← read_eq_val32, ← read_eq_val32, mulFrame_hdr E₁.room nw' Ft (by decide) (by omega_using [f2, e2]) f2 f5, M₁]
    · rw [mulFrame_val32 E₁.room nw' Ft (.inr (by omega_using [e2, e3])) (by omega_using [wbe, e3, e5]) (by omega_using [wbe, f5, e3, e5]) f2 f5, M₁]

theorem sparseRound_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {M : Nat}
    (E : Env base bytes len args M s) (hbytes : bytes = (args 9).toNat * 8)
    {y b : Nat} (hY : val32 s.mem base (numAt len 2) (nw len) = y * 2 ^ (32 * nw len) % M)
    (hX : val32 s.mem base (numAt len 1) (nw len) = b * 2 ^ (32 * nw len) % M) :
    WP isa sparseRound s fun t =>
      Env base bytes len args M t ∧ Frame (Chg base len bytes (s.gpr .esp)) s.mem t.mem ∧
      t.zf = some (decide (val32 s.mem base 128 2 / 2 = 0)) ∧
      val32 t.mem base (numAt len 2) (nw len) =
        (if val32 s.mem base 128 2 % 2 = 1 then y * b else y) * 2 ^ (32 * nw len) % M ∧
      val32 t.mem base (numAt len 1) (nw len) =
        (if val32 s.mem base 128 2 / 2 = 0 then b else b * b) * 2 ^ (32 * nw len) % M ∧
      val32 t.mem base 128 2 = val32 s.mem base 128 2 / 2 ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧
      val32 t.mem base (numAt len 3) (nw len) = val32 s.mem base (numAt len 3) (nw len) := by
  have h := E.pi
  have nw' := h.scratch.nowrap
  have dims := h.dimensions
  have wbe := wb_eq len
  have hM := E.pos
  have f5 := (h.fits (j := 5) (by decide)).2
  have f1 := (h.fits (j := 1) (by decide)).1
  have e1 : numAt len 1 = 256 + wb len := by simp only [numAt, numOff] <;> omega_arith
  have e2 : numAt len 2 = 256 + 2 * wb len := by simp only [numAt, numOff] <;> omega_arith
  have e3 : numAt len 3 = 256 + 3 * wb len := by simp only [numAt, numOff] <;> omega_arith
  have e5 : numAt len 5 = 256 + 5 * wb len := by simp only [numAt, numOff] <;> omega_arith
  unfold sparseRound
  refine WP.seq (WP.mono (product_ok E hbytes hY hX) fun u₁ ⟨E₁, C₁, Y₁, X₁, W₁, K₁, O₁⟩ => ?_)
  have sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  -- Shift first: the last round has no use for another square.
  refine WP.seq (WP.block_append (WP.mono (shiftExponent_ok E₁.pi.scratch 2 128 (by omega_arith))
    fun u₂ ⟨O₂, V₂, K₂⟩ => ?_))
  have E₂ := E₁.keep K₂ (by decide) (by decide) (Outside.chg O₂ (.inl ⟨by decide, by decide⟩))
  refine WP.mono (PublicContext.exponentLeft_ok E₂.pi.scratch (by omega_arith)) fun u₃ ⟨M₃, K₃, Z₃⟩ => ?_
  have E₃ := E₂.keep K₃ (by decide) (by decide) (by rw [M₃]; exact Frame.refl _ _)
  have W₃ : val32 u₃.mem base 128 2 = val32 s.mem base 128 2 / 2 := by rw [M₃, V₂, W₁]
  have X₃ : val32 u₃.mem base (numAt len 1) (nw len) = b * 2 ^ (32 * nw len) % M := by
    rw [M₃, O₂.val32 (.inr (by omega_arith)) (by omega_arith), X₁, hX]
  have Y₃ : val32 u₃.mem base (numAt len 2) (nw len) =
      (if val32 s.mem base 128 2 % 2 = 1 then y * b else y) * 2 ^ (32 * nw len) % M := by
    rw [M₃, O₂.val32 (.inr (by omega_arith)) (by omega_arith), Y₁]
  have C₃ : Frame (Chg base len bytes (s.gpr .esp)) s.mem u₃.mem := by
    refine C₁.trans ?_
    rw [M₃]
    exact Outside.chg O₂ (.inl ⟨by decide, by decide⟩)
  have O₃ : val32 u₃.mem base (numAt len 3) (nw len) = val32 s.mem base (numAt len 3) (nw len) := by
    rw [M₃, O₂.val32 (.inr (by omega_arith)) (by omega_arith), O₁]
  have K₃' : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u₃ :=
    ((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₃.mono (by decide))
  have sp₃ : u₃.gpr .esp = s.gpr .esp := K₃'.1 _ (by decide)
  by_cases done : val32 s.mem base 128 2 / 2 = 0
  · refine WP.ite true (by change u₃.zf = _; rw [Z₃, V₂, W₁, done]; rfl)
      (fun _ => WP.block_nil ?_) (fun e => nomatch e)
    exact ⟨E₃, C₃, by rw [Z₃, V₂, W₁], Y₃, by rw [ite_eq_left done]; exact X₃, W₃, K₃', O₃⟩
  · refine WP.ite false (by change u₃.zf = _; rw [Z₃, V₂, W₁, decide_eq_false done])
      (fun e => nomatch e) (fun _ => ?_)
    refine WP.seq (WP.mono (mulEnv_ok E₃ hbytes (o := 1) (a := 1) (b := 1) (by decide) (by decide) (by decide)
      (by decide) (x := b) (y := b) (by rw [X₃, Nat.mod_mod]) (by rw [X₃, Nat.mod_mod])
      (by rw [X₃]; exact Nat.mod_lt _ hM)) fun u₄ ⟨E₄, C₄, cs₄, F₄, X₄⟩ => ?_)
    have Y₄ := mulFrame_val32 E₃.room nw' F₄ (d := numAt len 2)
      (.inr (by omega_arith)) (by omega_arith) (by omega_arith) f1 f5
    have O₄ := mulFrame_val32 E₃.room nw' F₄ (d := numAt len 3)
      (.inr (by omega_arith)) (by omega_arith) (by omega_arith) f1 f5
    have W₄ : val32 u₄.mem base 128 2 = val32 u₃.mem base 128 2 := by
      rw [← read_eq_val32, ← read_eq_val32, mulFrame_hdr E₃.room nw' F₄ (by decide) (by omega_arith) f1 f5]
    refine WP.mono (PublicContext.exponentLeft_ok E₄.pi.scratch (by omega_arith)) fun t ⟨M₅, K₅, Z₅⟩ => ?_
    refine ⟨E₄.keep K₅ (by decide) (by decide) (by rw [M₅]; exact Frame.refl _ _), ?_,
      by rw [Z₅, W₄, W₃], by rw [M₅, Y₄]; exact Y₃,
      by rw [M₅, ite_eq_right done]; exact X₄, by rw [M₅, W₄, W₃],
      (K₃'.trans (cs₄.mono (by decide))).trans (K₅.mono (by decide)), by rw [M₅, O₄, O₃]⟩
    rw [M₅]
    exact C₃.trans (by rw [← sp₃]; exact C₄)

end VG.Proof.Bignum.X86.PublicRt

end

end


/-! # The exponentiation of public RSA at a run-time width

From `R² mod M` (number 4), one (number 3) and the input `x < M` (number
1): convert the base to `x R mod M`, seed the accumulator with that base
for an odd exponent and consume its low bit (or use `R mod M` for an even
exponent), process the remaining bits (`sparseLoop_ok`), and leave Montgomery form,
`x^e mod M` in number 2 for the exponent `e` at 128 (`exponentiate_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86

/-- The loop's state after some rounds from `s₀`, towards `target`. -/
structure LoopInv (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (M target : Nat)
    (s₀ t : State) : Prop where
  env : Env base bytes len args M t
  frame : Frame (Chg base len bytes (s₀.gpr .esp)) s₀.mem t.mem
  value : ∃ y b, val32 t.mem base (numAt len 2) (nw len) = y * 2 ^ (32 * nw len) % M ∧
    val32 t.mem base (numAt len 1) (nw len) = b * 2 ^ (32 * nw len) % M ∧
    (y * b ^ val32 t.mem base 128 2) % M = target
  keeps : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s₀ t
  one : val32 t.mem base (numAt len 3) (nw len) = val32 s₀.mem base (numAt len 3) (nw len)

theorem sparseLoop_ok {s₀ : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {M target : Nat}
    (hbytes : bytes = (args 9).toNat * 8) (I₀ : LoopInv base bytes len args M target s₀ s₀) :
    WP isa (.loop sparseRound .ne) s₀ fun t =>
      LoopInv base bytes len args M target s₀ t ∧ val32 t.mem base 128 2 = 0 := by
  refine WP.loop (M := isa)
    (fun k t => val32 t.mem base 128 2 = k ∧ LoopInv base bytes len args M target s₀ t) ?_
    (val32 s₀.mem base 128 2) s₀ ⟨rfl, I₀⟩
  rintro k t ⟨rfl, I⟩
  obtain ⟨y, b, Y, B, V⟩ := I.value
  refine WP.mono (sparseRound_ok I.env hbytes Y B) fun u ⟨Eu, Fu, Zu, Yu, Bu, Wu, Ku, ou⟩ => ?_
  have next : LoopInv base bytes len args M target s₀ u := by
    refine ⟨Eu, ?_, ⟨_, _, Yu, Bu, ?_⟩, I.keeps.trans Ku, ?_⟩
    · exact I.frame.trans (by rw [← I.keeps.1 _ (by decide)]; exact Fu)
    · by_cases done : val32 t.mem base 128 2 / 2 = 0
      · rw [Wu, done, Nat.pow_zero, Nat.mul_one]
        have h := congrArg (· % M) (VG.Proof.Mont.X86.Dynamic.exponent_step_value y b
          (val32 t.mem base 128 2))
        simpa only [done, Nat.pow_zero, Nat.mul_one] using h.trans V
      · rw [Wu, ite_eq_right done, VG.Proof.Mont.X86.Dynamic.exponent_step_value]; exact V
    · rw [ou, I.one]
  by_cases done : val32 t.mem base 128 2 / 2 = 0
  · refine .inl ⟨?_, next, by rw [Wu, done]⟩
    simp only [eval, Zu, done, decide_true, Option.map_some, Bool.not_true]
  · refine .inr ⟨?_, val32 u.mem base 128 2, by rw [Wu]; omega_using [done], rfl, next⟩
    simp only [eval, Zu, decide_eq_false done, Option.map_some, Bool.not_false]

theorem exponentiate_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {M : Nat}
    (E : Env base bytes len args M s) (_hbase : (args 8).toNat = base.toNat) (hbytes : bytes = (args 9).toNat * 8)
    (hM1 : 1 < M)
    (hT : val32 s.mem base (numAt len 4) (nw len) = 2 ^ (32 * nw len) * 2 ^ (32 * nw len) % M)
    (hO : val32 s.mem base (numAt len 3) (nw len) = 1) :
    WP isa exponentiate s fun t =>
      Env base bytes len args M t ∧ Frame (Chg base len bytes (s.gpr .esp)) s.mem t.mem ∧
      val32 t.mem base (numAt len 2) (nw len) =
        val32 s.mem base (numAt len 1) (nw len) ^ val32 s.mem base 128 2 % M ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have h := E.pi
  have nw' := h.scratch.nowrap
  have dims := h.dimensions
  have wbe := wb_eq len
  have f5 := (h.fits (j := 5) (by decide)).2
  have f1 := (h.fits (j := 1) (by decide)).1
  have f2 := (h.fits (j := 2) (by decide)).1
  have e1 : numAt len 1 = 256 + wb len := by simp only [numAt, numOff] <;> omega_using []
  have e2 : numAt len 2 = 256 + 2 * wb len := by simp only [numAt, numOff] <;> omega
  have e3 : numAt len 3 = 256 + 3 * wb len := by simp only [numAt, numOff] <;> omega
  have e4 : numAt len 4 = 256 + 4 * wb len := by simp only [numAt, numOff] <;> omega
  have e5 : numAt len 5 = 256 + 5 * wb len := by simp only [numAt, numOff] <;> omega
  have n0 : numOff = 256 := rfl
  have hR := E.coprime (32 * nw len)
  generalize hRd : 2 ^ (32 * nw len) = R at hT hR
  -- Convert the input once, then seed from it for an odd exponent.
  unfold exponentiate
  refine WP.seq (WP.mono (mulRaw_ok E hbytes (o := 1) (a := 1) (b := 4) (by decide) (by decide) (by decide)
    (by decide) (by rw [hT]; exact Nat.mod_lt _ (by omega_using [hM1]))) fun u₁ ⟨E₁, C₁, cs₁, F₁, L₁, V₁⟩ => ?_)
  rw [hT, hRd] at V₁
  have X₁ : val32 u₁.mem base (numAt len 1) (nw len) = val32 s.mem base (numAt len 1) (nw len) * R % M := by
    rw [← Nat.mod_eq_of_lt L₁]
    refine VG.Proof.Bignum.mont_cancel hR (V₁.trans ?_)
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc]
  have pv : ∀ {d}, (d + 4 * nw len ≤ numAt len 1 ∨ numAt len 1 + wb len ≤ d) → d + 4 * nw len ≤ numAt len 5 →
      val32 u₁.mem base d (nw len) = val32 s.mem base d (nw len) := fun hd h5 =>
    mulFrame_val32 E.room nw' F₁ hd h5 (by omega_using [f5, h5]) f1 f5
  have T₁ := pv (d := numAt len 4) (.inr (by omega_using [e1, e4])) (by omega_using [wbe, e4, e5])
  have O₁ := pv (d := numAt len 3) (.inr (by omega_using [e1, e3])) (by omega_using [wbe, e3, e5])
  have W₁ : val32 u₁.mem base 128 2 = val32 s.mem base 128 2 := by
    rw [← read_eq_val32, ← read_eq_val32, mulFrame_hdr E.room nw' F₁ (by decide) (by omega_using [f1, e1]) f1 f5]
  refine WP.seq (WP.mono (seed_ok E₁ hbytes L₁ (by rw [O₁, hO]; exact hM1))
    fun u₂ ⟨E₂, C₂, cs₂, L₂, pv₂, W₂, V₂⟩ => ?_)
  have X₂ : val32 u₂.mem base (numAt len 1) (nw len) = val32 s.mem base (numAt len 1) (nw len) * R % M := by
    rw [pv₂ 1 (by decide) (by decide), X₁]
  have O₂ := pv₂ 3 (by decide) (by decide)
  let k := val32 s.mem base 128 2
  let x := val32 s.mem base (numAt len 1) (nw len)
  let y := if k % 2 = 1 then x else 1
  have Y₂ : val32 u₂.mem base (numAt len 2) (nw len) = y * R % M := by
    by_cases odd : k % 2 = 1
    · rw [W₁, ite_eq_left odd, X₁] at V₂
      simpa only [y, ite_eq_left odd] using V₂
    · rw [W₁, ite_eq_right odd, T₁, O₁, hT, hO, hRd, Nat.mul_one, Nat.mod_mod] at V₂
      simp only [y, ite_eq_right odd, Nat.one_mul]
      rw [← Nat.mod_eq_of_lt L₂]
      exact VG.Proof.Bignum.mont_cancel hR V₂
  -- A round per bit of the exponent.
  have sp₁ : u₁.gpr .esp = s.gpr .esp := cs₁.1 _ (by decide)
  have sp₂ : u₂.gpr .esp = s.gpr .esp := (cs₂.1 _ (by decide)).trans sp₁
  have I₀ : LoopInv base bytes len args M (val32 s.mem base (numAt len 1) (nw len) ^ val32 s.mem base 128 2 % M)
      u₂ u₂ := by
    refine ⟨E₂, Frame.refl _ _, ⟨y, x, ?_, ?_, ?_⟩, Keeps.refl _ _, rfl⟩
    · rw [Y₂, ← hRd]
    · rw [X₂, ← hRd]
    · rw [W₂, W₁]
      change (y * x ^ (k - k % 2)) % M = x ^ k % M
      by_cases odd : k % 2 = 1
      · simp only [y, ite_eq_left odd]
        rw [odd, ← Nat.pow_succ', show (k - 1).succ = k from by omega_using [odd]]
      · have even : k % 2 = 0 := by omega_using [odd]
        simp only [y, ite_eq_right odd]
        rw [even, Nat.sub_zero, Nat.one_mul]
  refine WP.seq (WP.mono (sparseLoop_ok hbytes I₀) fun u₄ ⟨I, z⟩ => ?_)
  obtain ⟨y, b, Y₄, -, V₄⟩ := I.value
  rw [z, Nat.pow_zero, Nat.mul_one] at V₄
  have O₄ : val32 u₄.mem base (numAt len 3) (nw len) = 1 := by rw [I.one, O₂, O₁, hO]
  -- The result out of Montgomery form.
  refine WP.mono (mulRaw_ok I.env hbytes (o := 2) (a := 2) (b := 3) (by decide) (by decide) (by decide)
    (by decide) (by rw [O₄]; exact hM1)) fun t ⟨Et, Ct, cst, _, Lt, Vt⟩ => ?_
  rw [Y₄, O₄, Nat.mul_one, Nat.mod_mod, hRd] at Vt
  have sp₄ : u₄.gpr .esp = s.gpr .esp := by rw [I.keeps.1 _ (by decide), sp₂]
  refine ⟨Et, ?_, ?_, ?_⟩
  · have G₂ : Frame (Chg base len bytes (s.gpr .esp)) u₁.mem u₂.mem := by rw [← sp₁]; exact C₂
    have G₄ : Frame (Chg base len bytes (s.gpr .esp)) u₂.mem u₄.mem := by
      have := I.frame; rwa [sp₂] at this
    have Gt : Frame (Chg base len bytes (s.gpr .esp)) u₄.mem t.mem := by rw [← sp₄]; exact Ct
    exact ((C₁.trans G₂).trans G₄).trans Gt
  · rw [← Nat.mod_eq_of_lt Lt, ← V₄]
    exact VG.Proof.Bignum.mont_cancel hR (by rw [← hRd] at Vt ⊢; exact Vt)
  · exact ((cs₁.mono (by decide)).trans (cs₂.mono (by decide))).trans (I.keeps.trans (cst.mono (by decide)))

end VG.Proof.Bignum.X86.PublicRt
