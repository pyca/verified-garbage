import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombSelect

/-!
# Ed25519's comb on x86-64: the selection with AVX2

`combSelectY` selects the entry as the comb with AVX512_IFMA does (`Ifma.vselect`, 32 bytes at a
time in `ymm11–ymm13`), stores the three rows to slots 4–6, and writes the identity's ones for a
zero magnitude as `combSelect` does (`combSelOne_slots`): the slots then hold the same entry as
after `combSelect` (`combSelectY_ok`, `combSelect_ok`'s statement).
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Impl.X25519.X86_64 (sc)
open VG.Impl.X25519.X86_64.Ifma (y st)
open VG.Proof.X25519.X86_64 (off Outside F)
open VG.Proof.Poly1305.X86_64.Avx2 (xr qw)

/-- Quadword `k` of a `ymm` register, as bytes. -/
theorem ymm_qword' (s : State) (r : XReg) {k : Nat} (hk : k < 4) :
    (s.ymm r).extractLsb' (8 * (8 * k)) (8 * 8) = qw s r k := by
  rw [← VG.Proof.Poly1305.X86_64.Avx2.qword256_ymm s r hk, qword256]
  congr 1; omega

/-- A `ymm` register to the 32 bytes at `d`. -/
theorem stY_ok {s : State} {base : Addr} (hs : Scratch s base) {d : Nat} (hd : d + 32 ≤ 8192) (r : Nat) :
    WP isa (.block [st d r]) s fun t => t = s.setMem (s.mem.writeW (off base d) (s.ymm (y r))) := by
  have hw : InRegions s.wr (off base d) 32 := ⟨_, hs.wr, Offset.contains_base base hd (by omega)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, st, Proof.X25519.X86_64.ea_sc, hs.rdi,
    State.store256_eq, hw, ite_true, Option.some.injEq, exists_eq_left']

/-- The words of a stored `ymm` register. -/
theorem word_stY (m : Mem) (base : Addr) (s : State) (r : XReg) {d k : Nat} (hk : k < 4) :
    Proof.X25519.X86_64.word (m.writeW (off base d) (s.ymm r)) base (d + 8 * k) = qw s r k := by
  have e := readW_writeW_inside m (off base d) (s.ymm r) (k := 8 * k) (n := 8) (by omega) (by decide)
  rw [ymm_qword' s r hk, off, Offset.add_ofNat_add_ofNat] at e
  exact e

/-- The words elsewhere. -/
theorem word_stY_off (m : Mem) (base : Addr) (v : BitVec 256) {d e : Nat} (hd : e + 8 < 2 ^ 62)
    (hd' : d + 32 < 2 ^ 62) (h : e + 8 ≤ d ∨ d + 32 ≤ e) :
    Proof.X25519.X86_64.word (m.writeW (off base d) v) base e = Proof.X25519.X86_64.word m base e :=
  readW_writeW_off m base v (d := e) (e := d) (n := 8) (by omega) (by omega) (by omega)

/-- A store to slots 4–6 keeps the bytes outside them. -/
theorem writeW_byte_off' {m : Mem} {base x : Addr} {v : BitVec 256}
    (hx : Proof.X25519.X86_64.ofs base x < offset 4 ∨ offset 4 + 96 ≤ Proof.X25519.X86_64.ofs base x)
    {d : Nat} (hd : offset 4 ≤ d ∧ d + 32 ≤ offset 4 + 96) : (m.writeW (off base d) v) x = m x := by
  refine writeW_byte_off m (off base d) v x ?_
  simp only [Proof.X25519.X86_64.ofs] at hx
  rw [off, Offset.sub_add_eq, Offset.toNat_sub_ofNat]
  have := (x - base).isLt
  simp only [offset] at hx hd
  omega

theorem vzeroupper_ok (s : State) :
    WP isa (.block [.vop .vzeroupper]) s fun t => t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.syms = s.syms := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `combSelectY`: as `combSelect_ok`. -/
theorem combSelectY_ok {s : State} {base T : Addr} (hs : Scratch s base) (ht : CombTbl s T)
    {j a : Nat} (hj : j < 26) (ha : a ≤ 16) (hd : s.gpr .rdx = BitVec.ofNat 64 j)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 a) :
    WP isa (.block combSelectY) s fun t =>
      (∀ f < 3, F t.mem base (offset 4 + 32 * f) = combField j a f) ∧
      Outside base (offset 4) 96 s.mem t.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.syms = s.syms := by
  rw [combSelectY, List.append_assoc, WP.block_append_iff]
  refine WP.mono (Ifma.vselect_ok ht hj ha hd h8) fun s₁ ⟨q₁, k₁⟩ => ?_
  have hs₁ : Scratch s₁ base := ⟨by rw [k₁.gpr _ (by decide)]; exact hs.rdi, by rw [k₁.wr]; exact hs.wr, hs.nowrap⟩
  rw [show ([st (offset 4) 11, st (offset 5) 12, st (offset 6) 13, .vop .vzeroupper] : List Instr) ++
      combSelOne = [st (offset 4) 11] ++ ([st (offset 5) 12] ++ ([st (offset 6) 13] ++
      ([.vop .vzeroupper] ++ combSelOne))) from rfl, WP.block_append_iff]
  refine WP.mono (stY_ok hs₁ (d := offset 4) (by decide) 11) fun s₂ e₂ => ?_
  have hs₂ : Scratch s₂ base := ⟨by rw [e₂]; exact hs₁.rdi, by rw [e₂]; exact hs₁.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (stY_ok hs₂ (d := offset 5) (by decide) 12) fun s₃ e₃ => ?_
  have hs₃ : Scratch s₃ base := ⟨by rw [e₃]; exact hs₂.rdi, by rw [e₃]; exact hs₂.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (stY_ok hs₃ (d := offset 6) (by decide) 13) fun s₄ e₄ => ?_
  have hs₄ : Scratch s₄ base := ⟨by rw [e₄]; exact hs₃.rdi, by rw [e₄]; exact hs₃.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (vzeroupper_ok s₄) fun s₅ ⟨g₅, m₅, r₅, w₅, y₅⟩ => ?_
  have hs₅ : Scratch s₅ base := ⟨by rw [g₅]; exact hs₄.rdi, by rw [w₅]; exact hs₄.wr, hs.nowrap⟩
  have q₃ : ∀ r k, qw s₃ r k = qw s₁ r k := fun r k => by rw [e₃, e₂]; rfl
  have q₂ : ∀ r k, qw s₂ r k = qw s₁ r k := fun r k => by rw [e₂]; rfl
  -- The words of slots 4–6: the selected rows.
  have hw : ∀ c < 3, ∀ k < 4, Proof.X25519.X86_64.word s₅.mem base (offset 4 + 32 * c + 8 * k) =
      qw s₁ (xr (11 + c)) k := by
    intro c hc k hk
    rw [m₅, e₄]
    obtain rfl | rfl | rfl : c = 0 ∨ c = 1 ∨ c = 2 := by omega
    · rw [State.setMem_mem, word_stY_off _ _ _ (by simp only [offset]; omega) (by decide)
        (Or.inl (by simp only [offset]; omega)), e₃, State.setMem_mem,
        word_stY_off _ _ _ (by simp only [offset]; omega) (by decide) (Or.inl (by simp only [offset]; omega)),
        e₂, State.setMem_mem, show offset 4 + 32 * 0 + 8 * k = offset 4 + 8 * k by omega, word_stY _ _ _ _ hk]
      rfl
    · rw [State.setMem_mem, word_stY_off _ _ _ (by simp only [offset]; omega) (by decide)
        (Or.inl (by simp only [offset]; omega)), e₃, State.setMem_mem,
        show offset 4 + 32 * 1 + 8 * k = offset 5 + 8 * k by simp only [offset]; omega, word_stY _ _ _ _ hk, q₂]
      rfl
    · rw [State.setMem_mem, show offset 4 + 32 * 2 + 8 * k = offset 6 + 8 * k by simp only [offset]; omega,
        word_stY _ _ _ _ hk, q₃]
      rfl
  have hw₂ : ∀ i < 12, Proof.X25519.X86_64.word s₅.mem base (offset 4 + 8 * i) =
      if 1 ≤ a then (entryWords ((combTable.getD j []).getD (a - 1) (1, 1, 0))).getD i 0 else 0 := by
    intro i hi
    obtain ⟨c, k, hc, hk, rfl⟩ : ∃ c k, c < 3 ∧ k < 4 ∧ i = 4 * c + k :=
      ⟨i / 4, i % 4, by omega, by omega, by omega⟩
    rw [show offset 4 + 8 * (4 * c + k) = offset 4 + 32 * c + 8 * k by omega, hw c hc k hk, q₁ c hc k hk]
    by_cases h1 : 1 ≤ a
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_left_of_eq_true _ _ (eq_true h1),
        entryWords_getD _ c k hc hk, combField, combCached_succ j a h1]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h1)]
  have h8₅ : s₅.gpr .r8 = BitVec.ofNat 64 a := by
    rw [g₅, e₄, State.setMem_gpr, e₃, State.setMem_gpr, e₂, State.setMem_gpr, k₁.gpr _ (by decide), h8]
  refine WP.mono (combSelOne_slots hs₅ ha h8₅ hw₂) fun t ⟨ft, ot, gt, rt, wt, yt⟩ => ⟨ft, ?_, ?_, ?_, ?_, ?_⟩
  · -- The stores' bytes are in slots 4–6.
    intro x hx
    rw [ot x hx, m₅, e₄, State.setMem_mem, writeW_byte_off' hx (d := offset 6) (by decide), e₃, State.setMem_mem,
      writeW_byte_off' hx (d := offset 5) (by decide), e₂, State.setMem_mem, writeW_byte_off' hx (d := offset 4) (by decide), k₁.mem]
  · intro r h1 h2 h3
    rw [gt r h1 h2, g₅, e₄, State.setMem_gpr, e₃, State.setMem_gpr, e₂, State.setMem_gpr,
      k₁.gpr r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1, h2, h3⟩)]
  · rw [rt, r₅, e₄, e₃, e₂]; exact k₁.rd
  · rw [wt, w₅, e₄, e₃, e₂]; exact k₁.wr
  · rw [yt, y₅, e₄, e₃, e₂]; exact k₁.syms

theorem combSelectY_sel : SelOk combSelectY := by
  intro _ _ _ hs ht _ _ hj ha hd h8; exact combSelectY_ok hs ht hj ha hd h8

end VG.Proof.Ed25519.X86_64
