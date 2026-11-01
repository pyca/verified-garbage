module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCore
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontSave
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Bignum.Minv32
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Mont.Words32

/-!
# Montgomery multiplication on PPC64LE: the function

`vg_rsa_mont_mul(ws = r3, ws_len = r4, o = r5, a = r6, b = r7, scratch = r8)`
(`fnContract`): `mul` saves the nonvolatile registers in the scratch buffer,
runs the arithmetic (`core_ok`) and restores them (`fn_correct`).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum.PPC64LE VG.Impl.Bignum
open VG.Proof.Rsa.Mont (numAt wOf wordAt Layout Operand Keeps arrAt aM minvWord)

/-- The index in the low half of `r`. -/
abbrev idx (s : State) (r : Reg) : Nat := ((s.gpr r).setWidth 32).toNat

/-- The working space: `ws_len` words at `r3`. -/
abbrev wsR (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat * 8⟩

/-- `vg_rsa_mont_mul(ws = r3, ws_len = r4, o = r5, a = r6, b = r7, scratch = r8)`,
the scratch buffer 72 bytes. -/
def fnContract : Contract isa where
  pre s :=
    let ws := s.gpr .r3
    let n := (s.gpr .r4).toNat
    let w := wOf s.mem ws
    s.rd = [] ∧ s.wr = [wsR s, savR (s.gpr .r8)] ∧ (wsR s).Disjoint (savR (s.gpr .r8)) ∧
      ws.toNat + n * 8 ≤ 2 ^ 64 ∧ Layout s.mem ws n ∧ Operand (idx s .r5) ∧ Operand (idx s .r6) ∧
      Operand (idx s .r7) ∧
      ((s.mem.readW (ws + BitVec.ofNat 64 (arrAt w aM)) 64).toNat * (wordAt s.mem ws minvWord).toNat + 1) %
        2 ^ 64 = 0 ∧
      numAt s.mem ws w (idx s .r7) < numAt s.mem ws w aM
  post s s' :=
    let ws := s.gpr .r3
    let w := wOf s.mem ws
    let M := numAt s.mem ws w aM
    numAt s'.mem ws w (idx s .r5) < M ∧
      numAt s'.mem ws w (idx s .r5) * 2 ^ (64 * w) % M =
        numAt s.mem ws w (idx s .r6) * numAt s.mem ws w (idx s .r7) % M ∧
      Keeps ws (s.gpr .r4).toNat w (idx s .r5) s.mem s'.mem
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧
      (s₁.gpr .r5).setWidth 32 = (s₂.gpr .r5).setWidth 32 ∧
      (s₁.gpr .r6).setWidth 32 = (s₂.gpr .r6).setWidth 32 ∧
      (s₁.gpr .r7).setWidth 32 = (s₂.gpr .r7).setWidth 32 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
      wOf s₁.mem (s₁.gpr .r3) = wOf s₂.mem (s₂.gpr .r3)

theorem idx_eq (s : State) (r : Reg) : (s.gpr r).setWidth 32 = BitVec.ofNat 32 (idx s r) := by
  apply BitVec.eq_of_toNat_eq; simp [idx]

theorem slot_eq (w j : Nat) : arrAt w j = slot w j := rfl

/-- A number of the working space is its `2 w` digits. -/
theorem numAt_eq (m : Mem) (B : Addr) (w j : Nat) : numAt m B w j = val32 m B (slot w j) (2 * w) := by
  rw [← wordsVal_eq_val32, ← read_eq_wordsVal]; rfl

/-- A store to the scratch buffer leaves the working space. -/
theorem frame_outside {m m' : Mem} {B S : Addr} {Z : Nat} (hf : Frame [savR S] m m')
    (hd : (⟨B, Z⟩ : Region).Disjoint (savR S)) : Mont.Outside B Z (2 ^ 64) m m' := by
  intro x hx
  simp only [Mont.ofs] at hx
  refine hf x fun r hr hc => ?_
  simp only [List.mem_singleton] at hr
  subst hr
  have := (x - B).isLt
  exact hd x (by simp only [Region.Contains]; omega_arith) hc

/-- The arithmetic leaves the scratch buffer. -/
theorem outs_scratch {m m' : Mem} {B S : Addr} {Z : Nat} {rs : List (Nat × Nat)} (h : Outs B rs m m')
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ Z) (hd : (⟨B, Z⟩ : Region).Disjoint (savR S)) {x : Addr}
    (hx : (savR S).Contains x 1) : m' x = m x := by
  refine h x fun r hm => .inr ?_
  show r.1 + r.2 ≤ (x - B).toNat
  have := hr r hm
  by_contra hc
  exact hd x (by simp only [Region.Contains]; omega) hx

/-- The public data of a run: the working space, its size in bytes, the
scratch buffer, `w` and the indices. -/
structure FnData where
  B : Addr
  Z : Nat
  S : Addr
  w : Nat
  o : Nat
  a : Nat
  b : Nat

/-- The data of a state on entry. -/
def dataOf (s : State) : FnData :=
  ⟨s.gpr .r3, (s.gpr .r4).toNat * 8, s.gpr .r8, wOf s.mem (s.gpr .r3), idx s .r5, idx s .r6, idx s .r7⟩

/-- What holds of the memory and the permissions before the arithmetic. -/
structure Mid (d : FnData) (s : State) : Prop where
  scr : Scr s d.B d.Z
  sin : savR d.S ∈ s.wr
  w2 : 2 ≤ d.w
  w31 : d.w < 2 ^ 31
  hZ : slot d.w 8 ≤ d.Z
  ho : d.o < 8
  ha : d.a < 8
  hb : d.b < 8
  ho2 : d.o ≠ 2
  ho3 : d.o ≠ 3
  ha2 : d.a ≠ 2
  hb2 : d.b ≠ 2
  harr : ∀ j < 8, s.mem.readW (off d.B (8 * j + 64)) 64 = off d.B (slot d.w j)
  hw : s.mem.readW (off d.B 48) 64 = BitVec.ofNat 64 d.w
  hinv : (w32 s.mem d.B (slot d.w 0) * w32 s.mem d.B 56 + 1) % 2 ^ 32 = 0
  hB : val32 s.mem d.B (slot d.w d.b) (2 * d.w) < val32 s.mem d.B (slot d.w 0) (2 * d.w)

theorem Mid.congr {d : FnData} {s t : State} (h : Mid d s) (hm : t.mem = s.mem) (hw : t.wr = s.wr) :
    Mid d t := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ := h
  exact ⟨a1.congr hw, hw ▸ a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, hm ▸ a13, hm ▸ a14,
    hm ▸ a15, hm ▸ a16⟩

/-- After saving the registers. -/
def P1 (d : FnData) (s : State) : Prop :=
  Mid d s ∧ s.gpr .r3 = d.B ∧ (s.gpr .r5).setWidth 32 = BitVec.ofNat 32 d.o ∧
    (s.gpr .r6).setWidth 32 = BitVec.ofNat 32 d.a ∧ (s.gpr .r7).setWidth 32 = BitVec.ofNat 32 d.b ∧
    s.gpr .r21 = d.S

/-- After `args`. -/
def P2 (d : FnData) (s : State) : Prop :=
  Mid d s ∧ s.gpr .r3 = d.B ∧ s.gpr .r5 = off d.B (8 * d.o) ∧ s.gpr .r6 = off d.B (8 * d.a) ∧
    s.gpr .r7 = off d.B (8 * d.b) ∧ s.gpr .r21 = d.S

/-- After `loads`. -/
def P3 (d : FnData) (s : State) : Prop :=
  Mid d s ∧ s.gpr .r5 = off d.B (slot d.w d.o) ∧ s.gpr .r6 = off d.B (slot d.w d.a) ∧
    s.gpr .r7 = off d.B (slot d.w d.b) ∧ s.gpr .r8 = off d.B (slot d.w 2) ∧
    s.gpr .r9 = off d.B (slot d.w 3) ∧ s.gpr .r10 = off d.B (slot d.w 0) ∧
    s.gpr .r11 = BitVec.ofNat 64 (2 * d.w) ∧ s.gpr .r4 = BitVec.ofNat 64 (2 * d.w) ∧
    (s.gpr .r12).toNat = w32 s.mem d.B 56 ∧ s.gpr .r21 = d.S

theorem pre_saved {s₀ s₁ : State} (h : fnContract.pre s₀) (hS : Saved s₀ s₁) :
    P1 (dataOf s₀) s₁ ∧ Mont.Outside (s₀.gpr .r3) ((s₀.gpr .r4).toNat * 8) (2 ^ 64) s₀.mem s₁.mem := by
  obtain ⟨-, hwr, hdis, hnw, ⟨hw2, hw', h8, harr⟩, ⟨ho, ho2, ho3⟩, ⟨ha, ha2, -⟩, ⟨hb, hb2, -⟩, hinv, hB⟩ := h
  have hs : Scr s₀ (s₀.gpr .r3) ((s₀.gpr .r4).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) hnw
  have hZ : slot (wOf s₀.mem (s₀.gpr .r3)) 8 ≤ (s₀.gpr .r4).toNat * 8 := by rw [← slot_eq]; omega_arith
  have hsin : savR (s₀.gpr .r8) ∈ s₀.wr := by rw [hwr]; simp
  have hout₁ := frame_outside hS.frame hdis
  simp only [dataOf]
  simp only [wsR] at hdis
  generalize hBd : s₀.gpr .r3 = B at hs harr hZ hdis hnw hinv hB hout₁ hw2 hw' ⊢
  generalize hZd : (s₀.gpr .r4).toNat * 8 = Z at hs hZ hdis hnw hout₁ ⊢
  generalize hwd : wOf s₀.mem B = w at harr hw2 hw' hZ hinv hB ⊢
  have sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have g₁ : ∀ r ∈ [Reg.r3, .r5, .r6, .r7], s₁.gpr r = s₀.gpr r := fun r hr =>
    hS.keep.gpr r (by revert r hr; decide)
  have rd₁ : ∀ {d k}, d + k ≤ Z → s₁.mem.readW (off B d) (8 * k) = s₀.mem.readW (off B d) (8 * k) :=
    fun {d k} hk => Mem.readW_congr fun i hi => (hout₁ _ (by
      rw [Mont.ofs_off B (show d + i < 2 ^ 64 by omega_arith)]; omega_arith))
  have v₁ : ∀ {j}, j < 8 → val32 s₁.mem B (slot w j) (2 * w) = val32 s₀.mem B (slot w j) (2 * w) :=
    fun hj => hout₁.val32 (by have := sl _ hj; omega_arith) (by have := sl _ hj; omega_arith)
  have w₁ : ∀ {d}, d + 4 ≤ Z → w32 s₁.mem B d = w32 s₀.mem B d := fun hd => hout₁.w32 (by omega_arith) (by omega_arith)
  have s0 := sl 0 (by decide)
  have h56 := hdr_lt_slot w 0 (i := 7) (by decide)
  refine ⟨⟨?_, by rw [g₁ .r3 (by decide), hBd], by rw [g₁ .r5 (by decide)]; exact idx_eq s₀ .r5,
    by rw [g₁ .r6 (by decide)]; exact idx_eq s₀ .r6, by rw [g₁ .r7 (by decide)]; exact idx_eq s₀ .r7,
    hS.r21⟩, hout₁⟩
  refine ⟨hs.congr hS.keep.wr, by rw [hS.keep.wr]; exact hsin, hw2, hw', hZ, ho, ha, hb, ho2, ho3, ha2, hb2,
    fun j hj => ?_, ?_, ?_, ?_⟩
  · have := hdr_lt_slot w 0 (i := 8 + j) (by omega_arith)
    exact (rd₁ (k := 8) (by omega_arith)).trans (by rw [show 8 * j + 64 = 8 * (8 + j) by omega_arith]; exact harr j hj)
  · have := hdr_lt_slot w 0 (i := 6) (by decide)
    refine (rd₁ (k := 8) (by omega_arith)).trans ?_
    rw [← hwd, ← hBd]
    simp only [wOf, wordAt, Proof.Rsa.Mont.wWord, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [w₁ (d := slot w 0) (by omega_arith), w₁ (d := 56) (by omega_arith), w32_eq_mod, w32_eq_mod]
    exact Minv32.minv_low hinv
  · rw [v₁ hb, v₁ (by decide)]; rw [numAt_eq, numAt_eq] at hB; exact hB

theorem args_P {d : FnData} {s : State} (h : P1 d s) :
    WP isa (.block args) s fun t => P2 d t ∧ t.mem = s.mem ∧ Keep [.r5, .r6, .r7] s t := by
  obtain ⟨hm, h3, h5, h6, h7, h21⟩ := h
  refine WP.mono (args_ok h3 hm.ho hm.ha hm.hb h5 h6 h7) fun t ⟨⟨t5, t6, t7, tm⟩, k⟩ =>
    ⟨⟨hm.congr tm k.wr, by rw [k.gpr _ (by decide), h3], t5, t6, t7, by rw [k.gpr _ (by decide), h21]⟩,
      tm, k⟩

theorem loads_P {d : FnData} {s : State} (h : P2 d s) :
    WP isa (.block loads) s fun t => P3 d t ∧ t.mem = s.mem ∧ Keep basesRegs s t := by
  obtain ⟨hm, h3, h5, h6, h7, h21⟩ := h
  refine WP.mono (loads_ok hm.scr h3 hm.ho hm.ha hm.hb h5 h6 h7
    (by have := hm.hZ; unfold slot hdrBytes at this; omega_arith) hm.harr hm.hw)
    fun t ⟨⟨t5, t6, t7, t8, t9, t10, t11, t4, t12, tm⟩, k⟩ =>
    ⟨⟨hm.congr tm k.wr, t5, t6, t7, t8, t9, t10, t11, t4, by rw [tm]; exact t12,
      by rw [k.gpr _ (by decide), h21]⟩, tm, k⟩

theorem tail_P {d : FnData} {s : State} (h : P3 d s) :
    WP isa tail s fun t =>
      (val32 t.mem d.B (slot d.w d.o) (2 * d.w) < val32 s.mem d.B (slot d.w 0) (2 * d.w) ∧
        val32 t.mem d.B (slot d.w d.o) (2 * d.w) * 2 ^ (64 * d.w) % val32 s.mem d.B (slot d.w 0) (2 * d.w) =
          val32 s.mem d.B (slot d.w d.a) (2 * d.w) * val32 s.mem d.B (slot d.w d.b) (2 * d.w) %
            val32 s.mem d.B (slot d.w 0) (2 * d.w) ∧
        Outs d.B [(slot d.w 2, 8 * (d.w + 2)), (slot d.w 3, 8 * (d.w + 2)),
          (slot d.w d.o, 8 * (d.w + 2))] s.mem t.mem) ∧
      Keep tailRegs s t := by
  obtain ⟨hm, h5, h6, h7, h8, h9, h10, h11, h4, h12, -⟩ := h
  exact tail_ok hm.scr hm.ho hm.ha hm.hb hm.ho2 hm.ho3 hm.ha2 hm.hb2 hm.w2 hm.w31 hm.hZ h5 h6 h7 h8 h9 h10
    h11 h4 (by rw [h12]; exact (s.mem.readW _ 32).isLt) (by rw [h12]; exact hm.hinv) hm.hB

theorem pres_not_core : ∀ r ∈ preserved, (∀ i < 9, r ≠ saved i) →
    r ∉ [Reg.r5, .r6, .r7] ++ basesRegs ++ tailRegs ∧ r ≠ .r21 := by
  decide

theorem fn_correct (s : State) (h : fnContract.pre s) :
    ∃ tr t, Exec isa mul s tr t ∧ abiPreserved s t ∧ fnContract.post s t := by
  have hsin : savR (s.gpr .r8) ∈ s.wr := by rw [h.2.1]; simp
  have hdis := h.2.2.1
  have hnw := h.2.2.2.1
  have hBo := h.2.2.2.2.2.1.1
  show WP isa mul s fun t => abiPreserved s t ∧ fnContract.post s t
  unfold mul
  refine WP.seq (WP.mono (save_ok s hsin) fun s₁ hS => ?_)
  obtain ⟨hP1, hout₁⟩ := pre_saved h hS
  refine WP.seq (WP.seq (WP.mono (args_P hP1) fun s₂ ⟨hP2, m₂, k₂⟩ => WP.seq (WP.mono (loads_P hP2)
    fun s₃ ⟨hP3, m₃, k₃⟩ => WP.mono (tail_P hP3) fun t ⟨⟨hlt, heq, hout⟩, kt⟩ => ?_)))
  obtain ⟨hm, -⟩ := hP1
  simp only [dataOf] at hlt heq hout hm
  simp only [wsR] at hdis
  rw [m₃, m₂] at hlt heq hout
  generalize hBd : s.gpr .r3 = B at hout₁ hlt heq hout hm hdis hnw
  generalize hZd : (s.gpr .r4).toNat * 8 = Z at hout₁ hm hdis hnw
  generalize hwd : wOf s.mem B = w at hlt heq hout hm
  have sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hm.hZ
  have v₁ : ∀ {j}, j < 8 → val32 s₁.mem B (slot w j) (2 * w) = val32 s.mem B (slot w j) (2 * w) :=
    fun hj => hout₁.val32 (by have := sl _ hj; omega_arith) (by have := sl _ hj; omega_arith)
  have kt' := (k₂.trans k₃).trans kt
  -- The registers are restored.
  have hsav : ∀ i < 9, t.mem.readW (off (s.gpr .r8) (8 * i)) 64 = s.gpr (saved i) := fun i hi => by
    rw [← hS.saved i hi]
    exact Mem.readW_congr fun k hk => outs_scratch hout (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sl 2 (by decide)
      · exact sl 3 (by decide)
      · exact sl _ hm.ho) hdis (Region.Contains.byte (sav_contains _ hi) (by
          rw [Mem.sub_ofNat_toNat _ (by omega_arith)]; omega_arith))
  refine WP.mono (restore_ok t (kt'.gpr .r21 (by decide) |>.trans hS.r21)
    (by rw [kt'.wr, hS.keep.wr]; exact hsin) hsav) fun u ⟨urs, uot, um, _, _, usp, ulr⟩ => ?_
  have hpost : numAt u.mem B w (idx s .r5) < numAt s.mem B w aM ∧
      numAt u.mem B w (idx s .r5) * 2 ^ (64 * w) % numAt s.mem B w aM =
        numAt s.mem B w (idx s .r6) * numAt s.mem B w (idx s .r7) % numAt s.mem B w aM ∧
      Keeps B (s.gpr .r4).toNat w (idx s .r5) s.mem u.mem := by
    refine ⟨?_, ?_, ?_⟩
    · rw [um, numAt_eq, numAt_eq, ← v₁ (by decide)]; exact hlt
    · rw [um, numAt_eq, numAt_eq, numAt_eq, numAt_eq, ← v₁ (by decide), ← v₁ hm.ha, ← v₁ hm.hb]; exact heq
    · intro i hi hj
      have hi' : i < Z := by omega_arith
      have hofs : Mont.ofs B (B + BitVec.ofNat 64 i) = i := by
        show (B + BitVec.ofNat 64 i - B).toNat = i
        rw [Mem.sub_ofNat_toNat _ (by omega_arith)]
      rw [um, hout _ fun r hr => ?_, hout₁ _ (by rw [hofs]; omega_arith)]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [hofs]
      rcases hr with rfl | rfl | rfl
      · exact hj Proof.Rsa.Mont.aAcc (by simp)
      · exact hj Proof.Rsa.Mont.aTmp (by simp)
      · exact hj (idx s .r5) (by simp)
  refine ⟨⟨fun r hr => ?_, by rw [usp, kt'.sp, hS.keep.sp], by rw [ulr, kt'.lr, hS.keep.lr]⟩, ?_⟩
  · by_cases hs' : ∃ i < 9, r = saved i
    · obtain ⟨i, hi, rfl⟩ := hs'
      exact urs i hi
    · have hn : ∀ i < 9, r ≠ saved i := fun i hi e => hs' ⟨i, hi, e⟩
      obtain ⟨h1, h2⟩ := pres_not_core r hr hn
      rw [uot r hn, kt'.gpr r h1, hS.keep.gpr r (by simpa using h2)]
  · show numAt u.mem (s.gpr .r3) (wOf s.mem (s.gpr .r3)) (idx s .r5) < _ ∧ _ ∧ _
    rw [hBd, hwd]
    exact hpost

end VG.Proof.Bignum.PPC64LE
