module

public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Env
import VerifiedGarbage.Proof.Bignum.X86.ExponentBits
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.MulEnv
import VerifiedGarbage.Proof.Mont.X86.ExponentShift
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.ByteWords

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
  have ht := hw.of_keeps Kt
  refine wp_movS (readSrc_ptr ht esi (d := 0) (by omega_using [hy, hj])) fun s₁ u₁ _ => ?_
  have ht₁ := ht.of_keeps u₁.keeps
  have ebp₁ : PtrAt s₁ W .ebp (x + 4 * j) := by rw [PtrAt, u₁.other _ (by decide)]; exact ebp
  refine wp_storeS (ea_ptr ht₁ ebp₁ (d := 0) (by omega_using [hx, hj]))
    (ws_write ht₁ (y := x + 4 * j + 0) (n := 4) (by omega_using [hx, hj])) fun s₂ m₂ => ?_
  refine wp_addS rfl fun s₃ u₃ _ => wp_addS rfl fun s₄ u₄ _ => wp_subZ rfl fun s₅ u₅ z₅ => WP.block_nil ?_
  obtain ⟨c₁, c₂⟩ := count_zf ecx hj
  have ecx₄ : s₄.gpr .ecx = t.gpr .ecx := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide)]
  -- The source word, unchanged since the start.
  have word : (t.mem.readW (off W (y + 4 * j + 0)) 32).toNat = w32 t₀.mem W (y + 4 * j) := by
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
  have fit := (h.fits (j := 2) (by decide)).1
  have dims := h.dimensions
  have wbe := wb_eq len
  have e12 : numAt len 2 = numAt len 1 + wb len := numAt_succ len 1
  have hw := wb_le h.upper
  unfold seedCopy
  refine WP.seq (slotPtr_ok (r := .esi) (t := .ecx) (j := 1) (by decide) (by decide)
    h.edi h.width h.upper (by omega_arith) fun v K m ps _ => ?_)
  have hv := h.keep K (by decide) (by decide) (by rw [m]; exact Outside.refl _ _ _ _)
  refine slotPtr_ok (r := .ebp) (t := .ecx) (j := 2) (by decide) (by decide)
    hv.edi hv.width h.upper (by omega_arith) fun t₀ K₀ m₀ pd c => ?_
  refine WP.block_nil ?_
  have Kstart : Keeps [.ecx, .ebp, .esi] s t₀ := (K.mono (by decide)).trans (K₀.mono (by decide))
  have mstart : t₀.mem = s.mem := m₀.trans m
  have psrc : PtrAt t₀ base .esi (numAt len 1) := by rw [PtrAt, K₀.1 _ (by decide)]; exact ps
  have count : (t₀.gpr .ecx).toNat = 4 * nw len := by
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
  have parity : val32 s.mem base 128 2 % 2 = w32 s.mem base 128 % 2 := VG.Proof.Mont.X86.Dynamic.val32_parity s.mem base 128 1
  have hn := h.nowrap
  have lo : 0 < w32 s.mem base 128 := by omega_arith
  unfold seedConsume
  refine wp_movS (readSrc_sc h (by omega_arith)) fun u₁ e₁ _ => wp_subS rfl fun u₂ e₂ _ => ?_
  have K := e₁.keeps.trans e₂.keeps
  have h₂ := h.of_keeps K (by decide)
  refine wp_storeS (h₂.ea (by omega_arith)) (h₂.write (by omega_arith)) fun t mt => WP.block_nil ?_
  have mv : u₂.mem = s.mem := e₂.mem.trans e₁.mem
  have ev : u₂.gpr .eax = s.mem.readW (off base 128) 32 - 1 := by rw [e₂.gpr, e₁.gpr]
  have O := writeW32_outside s.mem base (s.mem.readW (off base 128) 32 - 1) (by decide : 128 + 4 ≤ 2 ^ 64)
  refine ⟨by rw [mt.mem, mv, ev]; exact O, ?_, K.trans (mt.keeps _)⟩
  rw [mt.mem, mv, ev]
  have tail := O.w32 (d := 132) (.inr (by omega_arith)) (by omega_arith)
  have head := w32_write_self s.mem base 128 (s.mem.readW (off base 128) 32 - 1)
  have sub : (s.mem.readW (off base 128) 32 - 1).toNat = w32 s.mem base 128 - 1 := by
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
  have wbe := wb_eq len
  have f2 := (h.fits (j := 2) (by decide)).1
  have f5 := (h.fits (j := 5) (by decide)).2
  have e1 : numAt len 1 = 256 + wb len := by simp only [numAt, numOff] <;> omega_arith
  have e2 : numAt len 2 = 256 + 2 * wb len := by simp only [numAt, numOff] <;> omega_arith
  have e3 : numAt len 3 = 256 + 3 * wb len := by simp only [numAt, numOff] <;> omega_arith
  have e5 : numAt len 5 = 256 + 5 * wb len := by simp only [numAt, numOff] <;> omega_arith
  unfold seed
  refine WP.seq (WP.mono (PublicContext.bitTest_ok h.scratch (by omega_arith)) fun u ⟨mu, Ku, Zu⟩ => ?_)
  have Eu := E.keep Ku (by decide) (by decide) (by rw [mu]; exact Frame.refl _ _)
  have par : val32 s.mem base 128 2 % 2 = w32 s.mem base 128 % 2 := VG.Proof.Mont.X86.Dynamic.val32_parity s.mem base 128 1
  by_cases even : val32 s.mem base 128 2 % 2 = 0
  · refine WP.ite true (by change u.zf = _; rw [Zu, decide_eq_true (by omega_arith)])
      (fun _ => ?_) (fun e => nomatch e)
    refine WP.mono (mulRaw_ok Eu hbytes (o := 2) (a := 4) (b := 3) (by decide) (by decide)
      (by decide) (by decide) (by rw [mu]; exact hO)) fun t ⟨Et, Ct, Kt, Ft, Lt, Vt⟩ => ?_
    refine ⟨Et, by rw [Ku.1 _ (by decide), mu] at Ct; exact Ct,
      (Ku.mono (by decide)).trans (Kt.mono (by decide)), Lt, ?_, ?_, ?_⟩
    · intro j hj hj2
      have sep : numAt len j + 4 * nw len ≤ numAt len 2 ∨ numAt len 2 + wb len ≤ numAt len j := by
        have hjc : j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4 := by omega_arith
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
    have Cv := Outside.chg (len := len) (bytes := bytes) (sp := u.gpr .esp) Ov (.inr ⟨by omega_arith, f2⟩)
    have Ev := Eu.keep Kv (by decide) (by decide) Cv
    have Wv : val32 v.mem base 128 2 = val32 s.mem base 128 2 := by rw [Ov.val32 (.inl (by omega_arith)) (by omega_arith), mu]
    refine WP.mono (seedConsume_ok Ev.pi.scratch (by omega_arith) (by rw [Wv]; exact odd)) fun t ⟨Ot, Wt, Kt⟩ => ?_
    have Ct := Outside.chg (len := len) (bytes := bytes) (sp := v.gpr .esp) Ot (.inl ⟨by decide, by decide⟩)
    have Et := Ev.keep Kt (by decide) (by decide) Ct
    refine ⟨Et, ?_, (Ku.mono (by decide)).trans ((Kv.mono (by decide)).trans (Kt.mono (by decide))),
      ?_, ?_, by rw [Wt, Wv, odd], ?_⟩
    · rw [Ku.1 _ (by decide), mu] at Cv
      rw [Kv.1 _ (by decide), Ku.1 _ (by decide)] at Ct
      exact Cv.trans Ct
    · rw [Ot.val32 (.inr (by omega_arith)) (by omega_arith), Vv, mu]; exact hX
    · intro j hj hj2
      have fj := (h.fits (by omega_arith : j ≤ 7)).1
      have nj : 256 ≤ numAt len j := by simp only [numAt, numOff] <;> omega_arith
      have sep : numAt len j + 4 * nw len ≤ numAt len 2 ∨ numAt len 2 + wb len ≤ numAt len j := by
        have hjc : j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4 := by omega_arith
        rcases hjc with rfl | rfl | rfl | rfl <;> simp only [numAt, numOff] <;> omega_arith
      rw [Ot.val32 (.inr (by omega_arith)) (by omega_arith), Ov.val32 sep (by omega_arith), mu]
    · rw [ite_eq_left odd, Ot.val32 (.inr (by omega_arith)) (by omega_arith), Vv, mu]

end VG.Proof.Bignum.X86.PublicRt
