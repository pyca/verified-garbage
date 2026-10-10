import VerifiedGarbage.Impl.Weierstrass.X86.Inv
import VerifiedGarbage.Proof.Weierstrass.X86.Loop
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Divstep.Word32Bits

/-! ## `InvStep` -/

section

/-! # Register arithmetic for a 32-bit word divstep -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86

def pairRight (left right odd swap : BitVec 32) : BitVec 32 :=
  right + (((left ^^^ swap) - swap) &&& odd)

theorem pairRegs_ok (s : State) :
    WP isa (.block pairRegs) s fun u =>
      u.gpr .eax = pairRight (s.gpr .ebx) (s.gpr .eax) (s.gpr .ecx) (s.gpr .edx) ∧
      u.gpr .ebx = s.gpr .ebx +
        (pairRight (s.gpr .ebx) (s.gpr .eax) (s.gpr .ecx) (s.gpr .edx) &&& s.gpr .edx) ∧
      Keeps [.eax, .ebx, .ebp] s u ∧ u.mem = s.mem := by
  apply WP.of_runBlock
  simp only [pairRegs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    Option.bind_some, Option.map_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left',
    pairRight]
  refine ⟨trivial, trivial, ⟨?_, rfl, rfl⟩, rfl⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    hr.1, hr.2.1, hr.2.2, ↓reduceIte]

def oddMask (g : BitVec 32) : BitVec 32 := 0 - (g &&& 1)
def swapMask (d g : BitVec 32) : BitVec 32 := ((d >>> 31) - 1) &&& oddMask g
def nextDelta (d g : BitVec 32) : BitVec 32 := ((d ^^^ swapMask d g) - swapMask d g) + 2

theorem maskRegs_ok (s : State) :
    WP isa (.block maskRegs) s fun u =>
      u.gpr .ecx = oddMask (s.gpr .eax) ∧
      u.gpr .edx = swapMask (s.gpr .edx) (s.gpr .eax) ∧
      u.gpr .eax = nextDelta (s.gpr .edx) (s.gpr .eax) ∧
      Keeps [.eax, .ebx, .ecx, .edx] s u ∧ u.mem = s.mem := by
  apply WP.of_runBlock
  simp only [maskRegs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    execShift, Option.bind_some, Option.map_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.gpr_setFlags, reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left',
    oddMask, swapMask, nextDelta, and_self, show 1 ≤ (31 : Nat) ∧ 31 ≤ 31 by decide,
    show (31 : Nat) ≠ 1 by decide]
  refine ⟨trivial, trivial, trivial, ⟨?_, rfl, rfl⟩, rfl⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags,
    hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ↓reduceIte]

end VG.Proof.Weierstrass.X86.Inv

end

/-! ## `InvPair` -/

section

/-! # A pair of divstep words in the working space -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem pairShift_ok (s : State) (matrix : Bool) :
    WP isa (.block (if matrix then [.alu .add .ebx (.reg .ebx)] else [.shift .shr .eax 1])) s fun u =>
      u.gpr .ebx = (if matrix then s.gpr .ebx + s.gpr .ebx else s.gpr .ebx) ∧
      u.gpr .eax = (if matrix then s.gpr .eax else s.gpr .eax >>> 1) ∧
      Keeps [.eax, .ebx] s u ∧ u.mem = s.mem := by
  cases matrix with
  | false =>
    exact wp_shr (by decide) fun u U _ => WP.block_nil
      ⟨U.other _ (by decide), U.gpr, U.keeps.mono (by decide), U.mem⟩
  | true =>
    exact wp_addS rfl fun u U _ => WP.block_nil
      ⟨U.gpr, U.other _ (by decide), U.keeps.mono (by decide), U.mem⟩

theorem storePair_ok {s : State} {base : Addr} {size left right : Nat} (hs : Scr s base size)
    (hl : left + 4 ≤ size) (hr : right + 4 ≤ size) (sep : left + 4 ≤ right ∨ right + 4 ≤ left) :
    WP isa (.block [.store (sc left) .ebx, .store (sc right) .eax]) s fun u =>
      u.mem.readW (off base left) 32 = s.gpr .ebx ∧
      u.mem.readW (off base right) 32 = s.gpr .eax ∧
      Keeps [] s u ∧ Unch base [(left, 4), (right, 4)] s.mem u.mem := by
  have hn := hs.nowrap
  refine wp_storeS (hs.ea (by omega)) (hs.write hl) fun s₁ U₁ => ?_
  have hs₁ := hs.of_keeps (U₁.keeps []) (by decide)
  refine wp_storeS (hs₁.ea (by omega)) (hs₁.write hr) fun u U₂ => WP.block_nil ?_
  refine ⟨?_, ?_, (U₁.keeps []).trans (U₂.keeps []), ?_⟩
  · apply BitVec.eq_of_toNat_eq
    change w32 u.mem base left = _
    rw [U₂.mem, w32_write_ne hn hr hl sep, U₁.mem, w32_write_self]
  · apply BitVec.eq_of_toNat_eq
    change w32 u.mem base right = _
    rw [U₂.mem, w32_write_self, U₁.gpr]
  · have O₁ := writeW32_outside s.mem base (d := left) (s.gpr .ebx) (by omega)
    have O₂ := writeW32_outside s₁.mem base (d := right) (s₁.gpr .eax) (by omega)
    intro x hx
    rw [U₂.mem, O₂ x (hx (right, 4) (by simp)), U₁.mem, O₁ x (hx (left, 4) (by simp))]

theorem pair_ok {s : State} {base : Addr} {size left right : Nat} (hs : Scr s base size)
    (hl : left + 4 ≤ size) (hr : right + 4 ≤ size) (sep : left + 4 ≤ right ∨ right + 4 ≤ left)
    (matrix : Bool) :
    let L := s.mem.readW (off base left) 32
    let R := pairRight L (s.mem.readW (off base right) 32) (s.gpr .ecx) (s.gpr .edx)
    let F := L + (R &&& s.gpr .edx)
    WP isa (.block (pair left right matrix)) s fun u =>
      u.mem.readW (off base left) 32 = (if matrix then F + F else F) ∧
      u.mem.readW (off base right) 32 = (if matrix then R else R >>> 1) ∧
      Keeps [.eax, .ebx, .ebp] s u ∧ Unch base [(left, 4), (right, 4)] s.mem u.mem := by
  dsimp only
  unfold pair
  refine WP.block_append (WP.block_append (WP.block_append ?_))
  refine wp_movS (readSrc_sc hs hl) fun s₁ U₁ _ => ?_
  have hs₁ := hs.of_keeps U₁.keeps (by decide)
  refine wp_movS (readSrc_sc hs₁ hr) fun s₂ U₂ _ => WP.block_nil ?_
  have K₀ : Keeps [.eax, .ebx, .ebp] s s₂ :=
    (U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))
  have M₀ : s₂.mem = s.mem := U₂.mem.trans U₁.mem
  refine WP.mono (pairRegs_ok s₂) fun s₃ ⟨R₃, L₃, K₃, M₃⟩ => ?_
  have hs₃ := ((hs.of_keeps K₀ (by decide)).of_keeps K₃ (by decide))
  refine WP.mono (pairShift_ok s₃ matrix) fun s₄ ⟨L₄, R₄, K₄, M₄⟩ => ?_
  refine WP.mono (storePair_ok (hs₃.of_keeps K₄ (by decide)) hl hr sep) fun u ⟨L, R, K, U⟩ => ?_
  refine ⟨?_, ?_, ((K₀.trans K₃).trans (K₄.mono (by decide))).trans (K.mono (by decide)), ?_⟩
  · rw [L, L₄, L₃, U₂.other _ (by decide), U₁.gpr, U₂.gpr, U₁.mem,
      K₀.1 .ecx (by decide), K₀.1 .edx (by decide)]
  · rw [R, R₄, R₃, U₂.other _ (by decide), U₁.gpr, U₂.gpr, U₁.mem,
      K₀.1 .ecx (by decide), K₀.1 .edx (by decide)]
  · intro x hx
    rw [U x hx, M₄, M₃, M₀]

end VG.Proof.Weierstrass.X86.Inv

end

/-! ## `InvMasks` -/

section

/-! # The odd/swap masks and delta of a word divstep -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem masks_ok {s : State} {base : Addr} {size t : Nat} (hs : Scr s base size)
    (ht : t + 12 ≤ size) :
    let D := s.mem.readW (off base t) 32
    let G := s.mem.readW (off base (t + 8)) 32
    WP isa (.block (masks t)) s fun u =>
      u.gpr .ecx = oddMask G ∧ u.gpr .edx = swapMask D G ∧
      u.mem.readW (off base t) 32 = nextDelta D G ∧
      Keeps [.eax, .ebx, .ecx, .edx] s u ∧ Outside base t 4 s.mem u.mem := by
  dsimp only
  have hn := hs.nowrap
  unfold masks
  refine WP.block_append (WP.block_append ?_)
  refine wp_movS (readSrc_sc hs (by omega)) fun s₁ U₁ _ => ?_
  have hs₁ := hs.of_keeps U₁.keeps (by decide)
  refine wp_movS (readSrc_sc hs₁ (by omega)) fun s₂ U₂ _ => WP.block_nil ?_
  have K₀ : Keeps [.eax, .ebx, .ecx, .edx] s s₂ :=
    (U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))
  have M₀ : s₂.mem = s.mem := U₂.mem.trans U₁.mem
  refine WP.mono (maskRegs_ok s₂) fun s₃ ⟨C, D, A, K, M⟩ => ?_
  have hs₃ := (hs.of_keeps K₀ (by decide)).of_keeps K (by decide)
  refine wp_storeS (hs₃.ea (by omega)) (hs₃.write (by omega)) fun u U => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, (K₀.trans K).trans (U.keeps _), ?_⟩
  · rw [U.gpr, C, U₂.other _ (by decide), U₁.gpr]
  · rw [U.gpr, D, U₂.gpr, U₁.mem, U₂.other _ (by decide), U₁.gpr]
  · apply BitVec.eq_of_toNat_eq
    change w32 u.mem base t = _
    rw [U.mem, w32_write_self, A, U₂.gpr, U₁.mem, U₂.other _ (by decide), U₁.gpr]
  · rw [U.mem, M, M₀]
    exact writeW32_outside _ _ _ (by omega)

end VG.Proof.Weierstrass.X86.Inv

end

/-! ## `InvWord` -/

section

/-! # One complete word divstep on x86 -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86 VG.Proof.Mont

def atWord (m : Mem) (base : Addr) (t i : Nat) : BitVec 32 :=
  m.readW (off base (t + 4 * i)) 32

def wordState (m : Mem) (base : Addr) (t : Nat) : Divstep.W32.WSt :=
  ⟨atWord m base t 0, atWord m base t 1, atWord m base t 2,
   atWord m base t 3, atWord m base t 4, atWord m base t 5, atWord m base t 6⟩

theorem pair_away {base : Addr} {t left right j : Nat} {m m' : Mem}
    (U : Unch base [(t + 4 * left, 4), (t + 4 * right, 4)] m m')
    (h : t + 28 ≤ 2 ^ 64) (hj : j < 7) (hl : j ≠ left) (hr : j ≠ right) :
    atWord m' base t j = atWord m base t j := by
  apply Mem.readW_congr
  intro i hi
  apply U
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rw [ofs_off base (by omega)]
  rcases hw with rfl | rfl <;> omega

theorem mask_away {base : Addr} {t j : Nat} {m m' : Mem}
    (U : Outside base t 4 m m') (h : t + 28 ≤ 2 ^ 64) (hj : j < 7) (h0 : 1 ≤ j) :
    atWord m' base t j = atWord m base t j := by
  apply BitVec.eq_of_toNat_eq
  exact U.w32 (by omega) (by omega)

theorem wordStep_ok {s : State} {base : Addr} {size t : Nat} (hs : Scr s base size)
    (ht : t + 28 ≤ size) :
    WP isa (.block (wordStep t)) s fun u =>
      wordState u.mem base t = Divstep.W32.wstep (wordState s.mem base t) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u ∧ Outside base t 28 s.mem u.mem := by
  have hn := hs.nowrap
  have ht' : t + 28 ≤ 2 ^ 64 := by omega
  unfold wordStep
  refine WP.block_append (WP.block_append (WP.block_append
    (WP.mono (masks_ok hs (by omega)) fun s₁ ⟨C₁, D₁, V₁, K₁, O₁⟩ => ?_)))
  have hs₁ := hs.of_keeps K₁ (by decide)
  refine WP.mono (pair_ok hs₁ (left := t + 4) (right := t + 8)
    (by omega) (by omega) (by omega) false) fun s₂ ⟨F₂, G₂, K₂, U₂⟩ => ?_
  have hs₂ := hs₁.of_keeps K₂ (by decide)
  refine WP.mono (pair_ok hs₂ (left := t + 12) (right := t + 20)
    (by omega) (by omega) (by omega) true) fun s₃ ⟨U₃, Q₃, K₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keeps K₃ (by decide)
  refine WP.mono (pair_ok hs₃ (left := t + 16) (right := t + 24)
    (by omega) (by omega) (by omega) true) fun u ⟨V₄, R₄, K₄, O₄⟩ => ?_
  have E₁ (j : Nat) (hj : j < 7) (h0 : 1 ≤ j) := mask_away O₁ ht' hj h0
  have E₂ (j : Nat) (hj : j < 7) (hl : j ≠ 1) (hr : j ≠ 2) := pair_away U₂ ht' hj hl hr
  have E₃ (j : Nat) (hj : j < 7) (hl : j ≠ 3) (hr : j ≠ 5) := pair_away O₃ ht' hj hl hr
  have E₄ (j : Nat) (hj : j < 7) (hl : j ≠ 4) (hr : j ≠ 6) := pair_away O₄ ht' hj hl hr
  have C₂ : s₂.gpr .ecx = s₁.gpr .ecx := K₂.1 _ (by decide)
  have D₂ : s₂.gpr .edx = s₁.gpr .edx := K₂.1 _ (by decide)
  have C₃ : s₃.gpr .ecx = s₁.gpr .ecx := (K₂.trans K₃).1 _ (by decide)
  have D₃ : s₃.gpr .edx = s₁.gpr .edx := (K₂.trans K₃).1 _ (by decide)
  have E₁' : ∀ j, j < 7 → 1 ≤ j →
      s₁.mem.readW (off base (t + 4 * j)) 32 = s.mem.readW (off base (t + 4 * j)) 32 := E₁
  have EU : s₂.mem.readW (off base (t + 12)) 32 = s.mem.readW (off base (t + 12)) 32 :=
    (E₂ 3 (by decide) (by decide) (by decide)).trans (E₁ 3 (by decide) (by decide))
  have EQ : s₂.mem.readW (off base (t + 20)) 32 = s.mem.readW (off base (t + 20)) 32 :=
    (E₂ 5 (by decide) (by decide) (by decide)).trans (E₁ 5 (by decide) (by decide))
  have EV : s₃.mem.readW (off base (t + 16)) 32 = s.mem.readW (off base (t + 16)) 32 :=
    (E₃ 4 (by decide) (by decide) (by decide)).trans
      ((E₂ 4 (by decide) (by decide) (by decide)).trans (E₁ 4 (by decide) (by decide)))
  have ER : s₃.mem.readW (off base (t + 24)) 32 = s.mem.readW (off base (t + 24)) 32 :=
    (E₃ 6 (by decide) (by decide) (by decide)).trans
      ((E₂ 6 (by decide) (by decide) (by decide)).trans (E₁ 6 (by decide) (by decide)))
  simp only [Bool.false_eq_true, ite_false, ite_true] at F₂ G₂ U₃ Q₃ V₄ R₄
  rw [E₁' 1 (by decide) (by decide), E₁' 2 (by decide) (by decide), C₁, D₁] at F₂ G₂
  rw [EU, EQ, C₂, D₂, C₁, D₁] at U₃ Q₃
  rw [EV, ER, C₃, D₃, C₁, D₁] at V₄ R₄
  refine ⟨?_, (((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans
    (K₃.mono (by decide))).trans (K₄.mono (by decide)), ?_⟩
  · simp only [wordState, Divstep.W32.wstep, Divstep.W32.WSt.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change atWord u.mem base t 0 = _
      rw [E₄ 0 (by decide) (by decide) (by decide), E₃ 0 (by decide) (by decide) (by decide),
        E₂ 0 (by decide) (by decide) (by decide)]
      exact V₁
    · change atWord u.mem base t 1 = _
      rw [E₄ 1 (by decide) (by decide) (by decide), E₃ 1 (by decide) (by decide) (by decide)]
      exact F₂
    · change atWord u.mem base t 2 = _
      rw [E₄ 2 (by decide) (by decide) (by decide), E₃ 2 (by decide) (by decide) (by decide)]
      exact G₂
    · change atWord u.mem base t 3 = _
      rw [E₄ 3 (by decide) (by decide) (by decide)]
      simpa only [Divstep.W32.wstep, wordState, atWord, pairRight, oddMask, swapMask,
        Divstep.W32.shl1, Nat.reduceMul, Nat.add_zero] using U₃
    · simpa only [Divstep.W32.wstep, wordState, atWord, pairRight, oddMask, swapMask,
        Divstep.W32.shl1, Nat.reduceMul, Nat.add_zero] using V₄
    · change atWord u.mem base t 5 = _
      rw [E₄ 5 (by decide) (by decide) (by decide)]
      exact Q₃
    · exact R₄
  · intro x hx
    have h (j : Nat) (hj : j < 7) : ofs base x < t + 4 * j ∨ t + 4 * j + 4 ≤ ofs base x := by omega
    rw [O₄ x (by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
                 rcases hw with rfl | rfl <;> first | exact h 4 (by decide) | exact h 6 (by decide)),
      O₃ x (by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
               rcases hw with rfl | rfl <;> first | exact h 3 (by decide) | exact h 5 (by decide)),
      U₂ x (by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
               rcases hw with rfl | rfl <;> first | exact h 1 (by decide) | exact h 2 (by decide)),
      O₁ x (by omega)]

end VG.Proof.Weierstrass.X86.Inv

end

/-! ## `InvLoop` -/

section

/-! # A public-count loop of word divsteps -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86 VG.Proof.Mont

def wordClob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi]

theorem wordSteps_ok {s : State} {base : Addr} {size t n : Nat} (hs : Scr s base size)
    (ht : t + 28 ≤ size) (hn : 1 ≤ n) (hn32 : n < 2 ^ 32) :
    WP isa (wordSteps t n) s fun u =>
      wordState u.mem base t = Divstep.W32.wsteps n (wordState s.mem base t) ∧
      Keeps wordClob s u ∧ Outside base t 28 s.mem u.mem := by
  unfold wordSteps
  refine WP.seq (wp_movS rfl fun s₁ U₁ _ => WP.block_nil ?_)
  let Inv := fun j u =>
    Scr u base size ∧ u.gpr .esi = BitVec.ofNat 32 j ∧
    wordState u.mem base t = Divstep.W32.wsteps (n - j) (wordState s.mem base t) ∧
    Keeps wordClob s u ∧ Outside base t 28 s.mem u.mem
  refine countLoop_ok (Inv := Inv) (n := n) ?_ ?_ hn ?_
  · intro j v hj hjn hI
    obtain ⟨hv, ev, Wv, Kv, Ov⟩ := hI
    refine wp_decCounter hj ev fun v₁ E₁ K₁ M₁ => ?_
    have hv₁ := hv.of_keeps K₁ (by decide)
    refine WP.block_append (WP.mono (wordStep_ok hv₁ ht) fun v₂ ⟨W₂, K₂, O₂⟩ => ?_)
    have e₂ : v₂.gpr .esi = BitVec.ofNat 32 (j - 1) := by rw [K₂.1 _ (by decide), E₁]
    refine wp_testCounter (by omega) e₂ fun u F hz => WP.block_nil ⟨?_, hz⟩
    refine ⟨(hv₁.of_keeps K₂ (by decide)).of_keeps (F.keeps []) (by decide),
      by rw [F.gpr]; exact e₂, ?_,
      (((Kv.trans (K₁.mono (by decide))).trans (K₂.mono (by decide))).trans (F.keeps _)), ?_⟩
    · rw [F.mem, W₂, M₁, Wv, show n - (j - 1) = (n - j) + 1 by omega,
        Divstep.W32.wsteps_succ]
    · intro x hx
      rw [F.mem, O₂ x hx, M₁, Ov x hx]
  · intro u ⟨_, _, W, K, O⟩
    exact ⟨by simpa only [Nat.sub_zero] using W, K, O⟩
  · refine ⟨hs.of_keeps U₁.keeps (by decide), U₁.gpr, ?_, U₁.keeps.mono (by decide), ?_⟩
    · rw [U₁.mem, Nat.sub_self]; rfl
    · rw [U₁.mem]; exact fun _ _ => rfl

end VG.Proof.Weierstrass.X86.Inv

end
