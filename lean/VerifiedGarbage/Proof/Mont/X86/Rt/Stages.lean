module

public import VerifiedGarbage.Proof.Mont.X86.Rt.ABI
import VerifiedGarbage.Proof.Framework.Omega

/-! # The stages of the run-time width multiplication

`zeroAcc` (`zero_ok`), then the rows from the zeroed accumulator
(`rowsAll_ok`): its high half and top word, `T`, below `2 M`, with
`2^(32 N) T ≡ A B` modulo `M`.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Rt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt VG.Proof.Mont VG.Proof.Mont.X86

/-- The accumulator, `2 N + 1` words at `S + accOff`, zeroed. -/
theorem zero_ok {t : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32} (hw : Ws t W L) (ha : Args t W L A)
    {N S mo inv o a b : Nat} (V : ArgVals A W N S mo inv o a b) (hL : Lay L N S mo inv a b)
    (hN32 : 4 * N < 2 ^ 32) (hedi : PtrAt t W .edi S) :
    WP isa zeroAcc t fun u =>
      val32 u.mem W (S + accOff) (2 * N + 1) = 0 ∧
      Outside W (S + accOff) (4 * (2 * N + 1)) t.mem u.mem ∧ Keeps [.eax, .ebp, .esi] t u := by
  have hn := hw.nowrap
  have hscr := hL.scr
  have eacc := accOff_eq
  unfold zeroAcc
  simp only [accPtr, List.cons_append, List.append_assoc]
  refine WP.seq (wp_movS rfl fun s₁ u₁ _ => wp_addS rfl fun s₂ u₂ _ => ?_)
  have ha₂ : Args s₂ W L A := (ha.of_upd u₁ (by decide)).of_upd u₂ (by decide)
  rw [List.nil_append]
  refine WP.block_append (WP.mono (lenTimes_ok ha₂ (r := .esi) 1) fun s₃ ⟨l₃, m₃, K₃⟩ => ?_)
  refine wp_addS rfl fun s₄ u₄ _ => wp_movS rfl fun s₅ u₅ _ => WP.block_nil ?_
  have K₅ : Keeps [.eax, .ebp, .esi] t s₅ :=
    ((((u₁.keeps.mono (by decide)).widen u₂.keeps).widen K₃).widen u₄.keeps).widen u₅.keeps
  have ebp₅ : PtrAt s₅ W .ebp (S + accOff) := by
    rw [PtrAt, u₅.other _ (by decide), u₄.other _ (by decide), K₃.1 _ (by decide), u₂.gpr, u₁.gpr,
      ptr_add hedi]
    simp only [BitVec.toNat_ofNat]; omega_using [eacc]
  have esi₅ : (s₅.gpr .esi).toNat = 4 * (2 * N + 1) := by
    rw [u₅.other _ (by decide), u₄.gpr, BitVec.toNat_add, l₃]
    have hn8 := V.n
    rw [show (A 2).toNat * 2 ^ (3 + 1) = 2 * ((A 2).toNat * 8) by rw [show 2 ^ (3 + 1) = 16 from rfl]; omega_using [],
      hn8]
    rw [show (4 : BitVec 32).toNat = 4 from rfl]
    omega_using [hN32, hscr, hn]
  refine WP.mono (zeroLoop_ok (hw.of_keeps K₅) (by omega_using []) (by omega_using [hscr, eacc]) ebp₅ esi₅ u₅.gpr)
    fun u ⟨O, Z, K⟩ => ⟨Z, ?_, K₅.trans (K.mono (by decide))⟩
  rwa [u₅.mem, u₄.mem, m₃, u₂.mem, u₁.mem] at O

/-- The rows, from the zeroed accumulator. -/
theorem rowsAll_ok {t : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32} (hw : Ws t W L) (ha : Args t W L A)
    {N S mo inv o a b m : Nat} (V : ArgVals A W N S mo inv o a b) (hL : Lay L N S mo inv a b)
    (hN : 0 < N) (hN32 : 4 * N < 2 ^ 32) (hedi : PtrAt t W .edi S)
    (hm : val32 t.mem W mo N = m) (hinv : (m * w32 t.mem W inv + 1) % 2 ^ 32 = 0)
    (hB : val32 t.mem W b N < m) (hZ : val32 t.mem W (S + accOff) (2 * N + 1) = 0) :
    WP isa rows t fun u => ∃ s₁, Keeps [.ebp] t s₁ ∧ s₁.mem = t.mem ∧ LoopInvR W N S a b m N s₁ u := by
  have hn := hw.nowrap
  have := accOff_eq
  unfold rows
  simp only [accPtr]
  refine WP.seq (wp_movS rfl fun s₁ u₁ _ => wp_addS rfl fun s₂ u₂ _ => WP.block_nil ?_)
  have K₂ : Keeps [.ebp] t s₂ := (u₁.keeps.mono (by decide)).widen u₂.keeps
  have m₂ : s₂.mem = t.mem := by rw [u₂.mem, u₁.mem]
  have hw₂ := hw.of_keeps K₂
  have ha₂ : Args s₂ W L A := (ha.of_upd u₁ (by decide)).of_upd u₂ (by decide)
  have edi₂ : PtrAt s₂ W .edi S := by rw [PtrAt, K₂.1 _ (by decide)]; exact hedi
  have ebp₂ : PtrAt s₂ W .ebp (S + accOff) := by
    rw [PtrAt, u₂.gpr, u₁.gpr, ptr_add hedi]; simp only [BitVec.toNat_ofNat]; omega_using [this]
  have hmpos : 0 < m := by omega_using [hB]
  have I₀ : LoopInvR W N S a b m 0 s₂ s₂ := by
    refine ⟨by simpa using ebp₂, Outs.refl _ _ _, Keeps.refl _ _, ?_, ⟨0, ?_⟩⟩
    · rw [m₂]; simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero, hZ]; omega_using [hmpos]
    · rw [m₂]; simp [val32, hZ]
  exact WP.mono (loopR_ok hw₂ ha₂ V hL hN hN32 edi₂ (by rw [m₂]; exact hm) (by rw [m₂]; exact hinv)
    (by rw [m₂]; exact hB) I₀) fun u I => ⟨s₂, K₂, m₂, I⟩

/-- The high half `- M` into the temporary, the borrow as a mask; `ebp` at
the top word and `edi` back at the function's range. -/
theorem subAll_ok {t : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32} (hw : Ws t W L) (ha : Args t W L A)
    {N S mo inv o a b : Nat} (V : ArgVals A W N S mo inv o a b) (hL : Lay L N S mo inv a b)
    (hN : 0 < N) (hN32 : 4 * N < 2 ^ 32) (hebp : PtrAt t W .ebp (S + accOff + 4 * N)) :
    WP isa subM t fun u =>
      Outside W (S + accOff + 8 * N + 4) (4 * N) t.mem u.mem ∧
      (∃ c : Bool, u.gpr .ecx = cmask c ∧
        val32 u.mem W (S + accOff + 8 * N + 4) N + val32 t.mem W mo N =
          val32 t.mem W (S + accOff + 4 * N) N + 2 ^ (32 * N) * c.toNat) ∧
      PtrAt u W .ebp (S + accOff + 8 * N) ∧ PtrAt u W .edi S ∧ Keeps clob7 t u := by
  have hn := hw.nowrap
  have hscr := hL.scr
  have hmo := hL.mo_le
  have hsmo := hL.smo
  have eacc := accOff_eq
  unfold subM
  simp only [List.append_assoc]
  -- The pointers and the count.
  refine WP.seq (WP.block_append (WP.mono (lenTimes_ok ha (r := .ebx) 0) fun s₁ ⟨l₁, m₁, K₁⟩ => ?_))
  refine wp_addS rfl fun s₂ u₂ _ => wp_addS rfl fun s₃ u₃ _ => ?_
  simp only [List.append_eq, List.nil_append]
  have K₃ : Keeps [.ebx] t s₃ := (K₁.widen u₂.keeps).widen u₃.keeps
  have ha₃ : Args s₃ W L A := ha.of_keeps K₃ (by decide) (by rw [u₃.mem, u₂.mem, m₁]; exact Outs.refl _ _ _)
  refine WP.block_append (WP.mono (ptr_ok ha₃ (r := .esi) (t := .eax) (i := 3) (by decide) (by decide) (by decide))
    fun s₄ ⟨e₄, _, m₄, K₄⟩ => ?_)
  have ha₄ : Args s₄ W L A := ha₃.of_keeps K₄ (by decide) (by rw [m₄]; exact Outs.refl _ _ _)
  refine WP.block_append (WP.mono (lenTimes_ok ha₄ (r := .edi) 0) fun s₅ ⟨l₅, m₅, K₅⟩ => ?_)
  refine wp_movS rfl fun s₆ u₆ _ => WP.block_nil ?_
  have K₆ : Keeps [.eax, .ebx, .ecx, .esi, .edi] t s₆ :=
    ((((K₃.mono (by decide)).widen K₄).widen K₅).widen u₆.keeps)
  have m₆ : s₆.mem = t.mem := by rw [u₆.mem, m₅, m₄, u₃.mem, u₂.mem, m₁]
  have hlen : (A 2).toNat * 2 ^ (3 + 0) % 2 ^ 32 = 4 * N := len_ok V.n hN32
  have ebp₆ : PtrAt s₆ W .ebp (S + accOff + 4 * N) := by rw [PtrAt, K₆.1 _ (by decide)]; exact hebp
  have esi₆ : PtrAt s₆ W .esi mo := by
    rw [PtrAt, u₆.other _ (by decide), K₅.1 _ (by decide), e₄, BitVec.toNat_add, V.ws, V.mo]
  have ebx₆ : PtrAt s₆ W .ebx (S + accOff + 8 * N + 4) := by
    rw [PtrAt, u₆.other _ (by decide), K₅.1 _ (by decide), K₄.1 _ (by decide), u₃.gpr, u₂.gpr,
      BitVec.toNat_add, BitVec.toNat_add, l₁, hlen, K₁.1 _ (by decide), hebp,
      show (4 : BitVec 32).toNat = 4 from rfl]
    omega_using [hN32]
  have edi₆ : (s₆.gpr .edi).toNat = 4 * N := by rw [u₆.other _ (by decide), l₅, hlen]
  refine WP.seq (WP.mono (subLoop_ok (hw.of_keeps K₆) hN (by omega_using [hscr, eacc]) hmo
      (by omega_using [hscr, eacc]) (by omega_using []) (by omega_using [hsmo, eacc]) ebp₆ esi₆ ebx₆ edi₆ u₆.gpr)
    fun u₇ ⟨O₇, V₇, ebp₇, K₇⟩ => ?_)
  -- `edi` back.
  have Kt₇ : Keeps clob7 t u₇ := (K₆.mono (by decide)).trans K₇
  have O₇t : Outs W [(0, L)] t.mem u₇.mem := by
    rw [← m₆]
    exact Outs.of_outside (O₇.mono (by omega_using []) (by omega_using [hscr, eacc])) (List.mem_singleton_self _)
  have ha₇ : Args u₇ W L A := ha.of_keeps Kt₇ (by decide) O₇t
  refine WP.mono (ptr_ok ha₇ (r := .edi) (t := .eax) (i := 5) (by decide) (by decide) (by decide))
    fun u ⟨eu, _, mu, Ku⟩ => ⟨?_, ?_, ?_, ?_, Kt₇.trans (Ku.mono (by decide))⟩
  · rw [mu, ← m₆]; exact O₇
  · obtain ⟨c, ec, V'⟩ := V₇
    refine ⟨c, by rw [Ku.1 _ (by decide)]; exact ec, ?_⟩
    rw [mu]; rw [m₆] at V'; exact V'
  · rw [PtrAt, Ku.1 _ (by decide)]
    rw [show S + accOff + 8 * N = S + accOff + 4 * N + 4 * N by omega_using []]; exact ebp₇
  · rw [PtrAt, eu, BitVec.toNat_add, V.ws, V.s]

/-- The mask from the top word, then the result at `o`: the reduced high half. -/
theorem selAll_ok {t : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32} (hw : Ws t W L) (ha : Args t W L A)
    {N S mo inv o a b : Nat} (V : ArgVals A W N S mo inv o a b) (hL : Lay L N S mo inv a b)
    (ho : o + 4 * N ≤ L) (hso : o + 4 * N ≤ S ∨ S + 12 * N + 56 ≤ o)
    (hN : 0 < N) (hN32 : 4 * N < 2 ^ 32) (hebp : PtrAt t W .ebp (S + accOff + 8 * N)) {c : Bool}
    (hc : t.gpr .ecx = cmask c) :
    WP isa (.seq (.block Rt.mask) select) t fun u =>
      Outside W o (4 * N) t.mem u.mem ∧
      val32 u.mem W o N = val32 t.mem W (if !(decide (w32 t.mem W (S + accOff + 8 * N) < c.toNat))
        then S + accOff + 8 * N + 4 else S + accOff + 4 * N) N ∧
      Keeps clob7 t u := by
  have hn := hw.nowrap
  have hscr := hL.scr
  have eacc := accOff_eq
  refine WP.seq (WP.mono (mask_ok hw hebp (by omega_using [hscr, eacc]) hc) fun t₁ ⟨mk, m₁, K₁⟩ => ?_)
  generalize hk : (!(decide (w32 t.mem W (S + accOff + 8 * N) < c.toNat))) = k at mk ⊢
  have ha₁ : Args t₁ W L A := ha.of_keeps K₁ (by decide) (by rw [m₁]; exact Outs.refl _ _ _)
  unfold select
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.seq (WP.block_append (WP.mono (lenTimes_ok ha₁ (r := .eax) 0) fun s₂ ⟨l₂, m₂, K₂⟩ => ?_))
  refine wp_subS rfl fun s₃ u₃ _ => wp_movS rfl fun s₄ u₄ _ => wp_addS rfl fun s₅ u₅ _ =>
    wp_addS rfl fun s₆ u₆ _ => ?_
  have K₆ : Keeps [.eax, .ebx, .ebp] t₁ s₆ :=
    ((((K₂.mono (by decide)).widen u₃.keeps).widen u₄.keeps).widen u₅.keeps).widen u₆.keeps
  have ha₆ : Args s₆ W L A := ha₁.of_keeps K₆ (by decide)
    (by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂]; exact Outs.refl _ _ _)
  refine WP.block_append (WP.mono (ptr_ok ha₆ (r := .esi) (t := .edx) (i := 6) (by decide) (by decide) (by decide))
    fun s₇ ⟨e₇, _, m₇, K₇⟩ => ?_)
  refine wp_movS rfl fun s₈ u₈ _ => WP.block_nil ?_
  have hlen : (A 2).toNat * 2 ^ (3 + 0) % 2 ^ 32 = 4 * N := len_ok V.n hN32
  have eax₂ : (s₂.gpr .eax).toNat = 4 * N := by rw [l₂, hlen]
  have hp₂ : PtrAt s₂ W .ebp (S + accOff + 8 * N) := by
    rw [PtrAt, K₂.1 _ (by decide), K₁.1 _ (by decide)]; exact hebp
  have ebp₃ : PtrAt s₃ W .ebp (S + accOff + 4 * N) := by
    rw [PtrAt, u₃.gpr, ptr_sub hp₂ _ (by rw [eax₂]; omega_using []), eax₂]
    congr 2; omega_using []
  have m₈ : s₈.mem = t₁.mem := by rw [u₈.mem, m₇, u₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂]
  have K₈ : Keeps [.eax, .ebx, .edx, .ebp, .esi, .edi] t₁ s₈ := ((K₆.mono (by decide)).widen K₇).widen u₈.keeps
  have ebp₈ : PtrAt s₈ W .ebp (S + accOff + 4 * N) := by
    rw [PtrAt, u₈.other _ (by decide), K₇.1 _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide)]; exact ebp₃
  have ebx₈ : PtrAt s₈ W .ebx (S + accOff + 8 * N + 4) := by
    rw [PtrAt, u₈.other _ (by decide), K₇.1 _ (by decide), u₆.gpr, u₅.gpr, u₄.gpr,
      u₄.other .eax (by decide), u₃.other .eax (by decide), BitVec.toNat_add, BitVec.toNat_add, ebp₃, eax₂,
      show (4 : BitVec 32).toNat = 4 from rfl]
    omega_using [hN32]
  have esi₈ : PtrAt s₈ W .esi o := by
    rw [PtrAt, u₈.other _ (by decide), e₇, BitVec.toNat_add, V.ws, V.o]
  have edi₈ : (s₈.gpr .edi).toNat = 4 * N := by
    rw [u₈.gpr, K₇.1 _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), eax₂]
  have ecx₈ : s₈.gpr .ecx = if k then BitVec.allOnes 32 else 0 := by
    rw [K₈.1 _ (by decide)]; exact mk
  refine WP.mono (selLoop_ok (hw.of_keeps ((K₁.mono (rs' := clob7) (by decide)).trans (K₈.mono (by decide)))) k hN (by omega_using [hscr, eacc])
    (by omega_using [hscr, eacc]) ho (by omega_using [hso, eacc]) (by omega_using [hso, eacc]) ebp₈ ebx₈ esi₈ edi₈ ecx₈)
    fun u ⟨O, Vu, Ku⟩ => ⟨?_, ?_, ((K₁.mono (by decide)).trans (K₈.mono (by decide))).trans (Ku.mono (by decide))⟩
  · rw [m₈, m₁] at O; exact O
  · rw [Vu, m₈, m₁]

end VG.Proof.Mont.X86.Rt
