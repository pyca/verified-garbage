import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtExp

/-!
# RSA with the CRT on AArch64: the exponentiation is constant time

`expLoop` reads the exponent's bytes, a secret, but at public addresses (its
pointer plus the byte index), and reads its table by a masked selection
from every entry, the mask computed from each window: the windows flow only
into data. Its loops count public numbers (the exponent's length, 2
windows a byte, 16 entries and the table's 14 products), the products are
Montgomery multiplications (constant time for any prime, `Mont.ct`), and
the addresses and counts it loads from the header, which the taint analysis
takes as secret, are pinned in both runs by the steps' correctness
(`CrtExp.lean`, for the bounds alone: `Q := False`).
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-- A piece whose only public input is `x0`. -/
theorem x0_ct {α : Type} {Φ : α → State → Prop} (f : α → Addr) (h : ∀ a s, Φ a s → s.gpr .x0 = f a)
    {c : Prog isa} {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) c hc).isSome = true) : RelCT isa (Two Φ) c fun _ _ => True :=
  two_taint [.x0] (pins_x0B f h) hT

/-- The prime's workspace of `p` and its context, as the steps' bounds need it. -/
def XCtx (p : XPub) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (X Xc : Nat), CExpCtx s (off p.B p.o) p.wx minv X Xc ∧ Xc < X ∧ 2 ≤ p.wx ∧ p.wx < 2 ^ 30

theorem XCtx.goodW {p : XPub} {s : State} (h : XCtx p s) : GoodW p.ws s :=
  let ⟨minv, _, _, hc, _⟩ := h; ⟨minv, hc.good, Nat.le_refl _⟩

theorem XCtx.x0 {p : XPub} {s : State} (h : XCtx p s) : s.gpr .x0 = off p.B p.o :=
  let ⟨_, _, _, hc, _⟩ := h; hc.good.x0

/-! ## Reading an entry -/

/-- After `j` entries of the selection, in the workspace of `p`. -/
def SelI (p : XPub) (j : Nat) (s : State) : Prop :=
  ∃ (t₀ : State) (minv : BitVec 64) (X Xc v : Nat), TabSelInv t₀ (off p.B p.o) p.wx minv X Xc v j s ∧
    2 ≤ p.wx ∧ p.wx < 2 ^ 30 ∧ v < 16

/-- Before the selection of entry `j`: its bases, `w_X` and the mask. -/
def SelB (q : XPub × Nat) (t : State) : Prop :=
  ∃ lt : Bool, Scr t (off q.1.B q.1.o) (slot q.1.wx 8 + tabBytes q.1.wx) ∧ t.gpr .x0 = off q.1.B q.1.o ∧
    t.gpr .x15 = mask lt ∧ t.gpr .x14 = BitVec.ofNat 64 q.1.wx ∧
    t.gpr .x16 = off (off q.1.B q.1.o) (slot q.1.wx (8 + q.2)) ∧
    t.gpr .x17 = off (off q.1.B q.1.o) (slot q.1.wx Crt.aT) ∧ 2 ≤ q.1.wx ∧ q.1.wx < 2 ^ 30 ∧ q.2 < 16

theorem pins_selB : Pins SelB [.x0, .x14, .x16, .x17] := by
  intro p s₁ s₂ ⟨_, _, a₁, _, b₁, c₁, d₁, _⟩ ⟨_, _, a₂, _, b₂, c₂, d₂, _⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [a₁, a₂]
  · rw [b₁, b₂]
  · rw [c₁, c₂]
  · rw [d₁, d₂]

/-- An entry of the selection leaks the same in runs with the same workspace,
whatever the window. -/
theorem selBody_ct : RelCT isa (Two fun (q : XPub × Nat) s => q.2 < 16 ∧ SelI q.1 q.2 s) (seqs selBody)
    fun _ _ => True := by
  simp only [selBody, seqs]
  -- The mask and the bases.
  refine RelCT.seq (two_piece (Ψ := SelB) [.x0] (pins_x0B (fun q => off q.1.B q.1.o)
    fun _ _ ⟨_, _, _, _, _, _, hI, _⟩ => hI.ctx.good.x0) (by taint_decide)
    fun q s ⟨hj, t₀, minv, X, Xc, v, hI, hw, hw', hv⟩ =>
      WP.mono (selHead_ok hI.ctx hj hv hI.idx hI.nib hI.ent) fun t ⟨⟨h15, h14, h16, h17, _⟩, k⟩ =>
        ⟨_, hI.ctx.scrT.congr k.wr, (k.gpr .x0 (by decide)).trans hI.ctx.good.x0, h15, h14, h16, h17, hw, hw',
          hj⟩) ?_
  -- `T := j = v ? T_j : T`.
  refine RelCT.seq (two_post (Ψ := fun (q : XPub × Nat) t => t.gpr .x0 = off q.1.B q.1.o)
    (two_taint [.x0, .x14, .x16, .x17] pins_selB (by taint_decide)) fun q s h => ?_) ?_
  · obtain ⟨lt, hs, h0, h15, h14, h16, h17, hw, hw', hj⟩ := h
    have hn := hs.nowrap
    have hT0 := slot_le (w := q.1.wx) (show Crt.aT < 8 by decide)
    have hE := ent_le q.1.wx hj
    have hTE := slot_sep (w := q.1.wx) (show Crt.aT ≠ 8 + q.2 by unfold Crt.aT; omega)
    exact WP.mono (selLoop_ok hs h16 h17 h14 h15 (by omega) (by omega) (by omega) (by omega) (by omega))
      fun t ⟨_, _, k⟩ => (k.gpr .x0 (by decide)).trans h0
  -- The next entry, and the index.
  exact x0_ct (fun q : XPub × Nat => off q.1.B q.1.o) (fun _ _ h => h) (by taint_decide)

/-- `tabSel_ok`'s hypotheses. -/
def SelP (p : XPub) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (X Xc v : Nat), CExpCtx s (off p.B p.o) p.wx minv X Xc ∧ 2 ≤ p.wx ∧ p.wx < 2 ^ 30 ∧
    v < 16 ∧ word s.mem (off p.B p.o) (8 * Crt.sTab) = off (off p.B p.o) (slot p.wx 8) ∧
    word s.mem (off p.B p.o) (8 * Crt.sNib) = BitVec.ofNat 64 v

/-- The selection leaks the same in runs with the same workspace. -/
theorem tabSel_ct : RelCT isa (Two SelP) (seqs tabSelect) fun _ _ => True := by
  rw [tabSelect_eq]
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := fun p s => 0 < 16 ∧ SelI p 0 s) [.x0]
    (pins_x0B (fun p : XPub => off p.B p.o) fun _ _ ⟨_, _, _, _, hc, _⟩ => hc.good.x0) (by taint_decide)
    fun p s ⟨minv, X, Xc, v, hc, hw, hw', hv, ht, hN⟩ => ?_) ?_
  · have hn := hc.scrT.nowrap
    refine WP.mono (selInit_ok hc ht) fun t₁ ⟨hm₁, k₁⟩ => ⟨by decide, t₁, minv, X, Xc, v, ?_, hw, hw', hv⟩
    have o1 := writeW_outside s.mem (off p.B p.o) (d := 8 * Crt.sEnt) (off (off p.B p.o) (slot p.wx 8)) (by decide)
    have o2 := writeW_outside (s.mem.writeW (off (off p.B p.o) (8 * Crt.sEnt)) (off (off p.B p.o) (slot p.wx 8)))
      (off p.B p.o) (d := 8 * Crt.sJ) (BitVec.ofNat 64 0) (by decide)
    rw [← hm₁] at o2
    have f₁ : Frm (off p.B p.o) (selRanges p.wx) s.mem t₁.mem :=
      (Frm.of_outside o1 (by simp [selRanges])).trans (Frm.of_outside o2 (by simp [selRanges]))
    refine ⟨hc.of_win (f₁.mono (selRanges_sub p.wx)) k₁.wr (k₁.gpr .x0 (by decide)), ?_, ?_, ?_, by simp,
      Frm.refl _ _ _, Keep.refl _ _⟩
    · rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
        hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact hN
    · rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
    · rw [hm₁, word_writeW_self]
  exact (two_loop (Φ := SelI) (Ψ := fun _ _ => True) (fun _ => 16) selBody_ct
    fun p j s hj ⟨t₀, minv, X, Xc, v, hI, hw, hw', hv⟩ =>
      WP.mono (selStep_ok hw hw' hv hj hI) fun s' ⟨hI', hz⟩ =>
        ⟨eval_nz_count hj hz, fun _ => ⟨t₀, minv, X, Xc, v, hI', hw, hw', hv⟩, fun _ => trivial⟩).mono
    (fun _ _ h => h) fun _ _ _ => trivial

/-! ## A window -/

/-- After `j` windows of a byte, in the prime's workspace of `p`. -/
def WinI (p : XPub) (j : Nat) (s : State) : Prop :=
  ∃ (t₀ : State) (minv : BitVec 64) (X Xc E v : Nat),
    CWinInv t₀ (off p.B p.o) p.wx minv X Xc False 0 E v j s ∧ 2 ≤ p.wx ∧ p.wx < 2 ^ 30 ∧
    Nat.Coprime (2 ^ (64 * p.wx)) X ∧ Xc < X ∧ v < 256

/-- Within a window: the workspace, its table, `Y < X` and the value in `sV`. -/
def WinQ (p : XPub) (t : State) : Prop :=
  ∃ (minv : BitVec 64) (X Xc V : Nat), CExpCtx t (off p.B p.o) p.wx minv X Xc ∧
    CTab t.mem (off p.B p.o) p.wx X False 0 ∧ wv t.mem (off p.B p.o) (slot p.wx aY) p.wx < X ∧
    word t.mem (off p.B p.o) (8 * Crt.sV) = BitVec.ofNat 64 V ∧ V < 2 ^ 56 ∧ 2 ≤ p.wx ∧ p.wx < 2 ^ 30 ∧
    Nat.Coprime (2 ^ (64 * p.wx)) X

theorem WinQ.goodW {p : XPub} {t : State} (h : WinQ p t) : GoodW p.ws t :=
  let ⟨minv, _, _, _, hc, _⟩ := h; ⟨minv, hc.good, Nat.le_refl _⟩

theorem WinQ.x0 {p : XPub} {t : State} (h : WinQ p t) : t.gpr .x0 = off p.B p.o :=
  let ⟨_, _, _, _, hc, _⟩ := h; hc.good.x0

/-- A squaring keeps `WinQ`. -/
theorem winSq_q (M : Mont) {p : XPub} {s : State} (h : WinQ p s) :
    WP isa (M.mm aY aY aY) s (WinQ p) := by
  obtain ⟨minv, X, Xc, V, hc, htab, hY, hV, hV', hw, hw', hR⟩ := h
  refine WP.mono (crtSq_ok M (Q := False) (x := 0) (E := 0) hc hw hw' hR hY False.elim)
    fun t ⟨hc', hY', _, hh, hf, _⟩ => ⟨minv, X, Xc, V, hc', htab.of_win hf hc.scrT.nowrap, hY', ?_, hV', hw, hw', hR⟩
  rw [hh _ (by decide)]; exact hV

/-- Before the selection: `tabSel_ok`'s hypotheses, and the rest of `WinQ`. -/
def WinS (p : XPub) (t : State) : Prop :=
  SelP p t ∧ ∃ (minv : BitVec 64) (X Xc : Nat), CExpCtx t (off p.B p.o) p.wx minv X Xc ∧
    CTab t.mem (off p.B p.o) p.wx X False 0 ∧ wv t.mem (off p.B p.o) (slot p.wx aY) p.wx < X ∧
    Nat.Coprime (2 ^ (64 * p.wx)) X

/-- After the selection: `T < X`, for `Y := Y T`. -/
def WinT (p : XPub) (t : State) : Prop :=
  ∃ (minv : BitVec 64) (X Xc : Nat), CExpCtx t (off p.B p.o) p.wx minv X Xc ∧
    wv t.mem (off p.B p.o) (slot p.wx Crt.aT) p.wx < X ∧ 2 ≤ p.wx ∧ p.wx < 2 ^ 30

/-- The window into `sNib`, and `sV` up. -/
theorem winMid_ct : RelCT isa (Two fun (q : XPub × Nat) s => WinQ q.1 s) (.block winMid)
    (Two fun (q : XPub × Nat) s => WinS q.1 s) := by
  refine two_piece [.x0] (pins_x0B (fun q : XPub × Nat => off q.1.B q.1.o) fun _ _ h => h.x0) (by taint_decide)
    fun q s h => ?_
  obtain ⟨minv, X, Xc, V, hc, htab, hY, hV, hV', hw, hw', hR⟩ := h
  have hn := hc.scrT.nowrap
  refine WP.mono (winMid_ok hc hV (by omega)) fun t ⟨hm, k⟩ => ?_
  have o1 := writeW_outside s.mem (off q.1.B q.1.o) (d := 8 * Crt.sV) (BitVec.ofNat 64 (16 * V)) (by decide)
  have o2 := writeW_outside (s.mem.writeW (off (off q.1.B q.1.o) (8 * Crt.sV)) (BitVec.ofNat 64 (16 * V)))
    (off q.1.B q.1.o) (d := 8 * Crt.sNib) (BitVec.ofNat 64 (V / 16 % 16)) (by decide)
  rw [← hm] at o2
  have f : Frm (off q.1.B q.1.o) (crtWinRanges q.1.wx) s.mem t.mem :=
    (Frm.of_outside o1 (by simp [crtWinRanges])).trans (Frm.of_outside o2 (by simp [crtWinRanges]))
  have hc' := hc.of_win f k.wr (k.gpr .x0 (by decide))
  have hY0 := slot_le (w := q.1.wx) (show aY < 8 by decide)
  have hYe : wv t.mem (off q.1.B q.1.o) (slot q.1.wx aY) q.1.wx =
      wv s.mem (off q.1.B q.1.o) (slot q.1.wx aY) q.1.wx := by
    rw [o2.wv (by have := hdr_lt_slot q.1.wx aY (show Crt.sNib < 32 by decide); omega) (by omega),
      o1.wv (by have := hdr_lt_slot q.1.wx aY (show Crt.sV < 32 by decide); omega) (by omega)]
  exact ⟨⟨minv, X, Xc, V / 16 % 16, hc', hw, hw', Nat.mod_lt _ (by decide), by
      rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
        hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact htab.tab,
      by rw [hm, word_writeW_self]⟩,
    minv, X, Xc, hc', htab.of_win f hn, hYe ▸ hY, hR⟩

/-- A window leaks the same in runs with the same workspace, whatever the window. -/
theorem crtWin_ct (M : Mont) :
    RelCT isa (Two fun (q : XPub × Nat) s => q.2 < 2 ∧ WinI q.1 q.2 s) (seqs (expWin M.mm))
      fun _ _ => True := by
  rw [expWin_eq]
  refine RelCT.seqs_append (by simp) (by simp [tabSelect_eq]) ?_
  have sq : RelCT isa (Two fun (q : XPub × Nat) s => WinQ q.1 s) (M.mm aY aY aY)
      (Two fun (q : XPub × Nat) s => WinQ q.1 s) :=
    two_post (two_map (fun q : XPub × Nat => q.1.ws) (fun _ _ h => h.goodW) (M.ct (by unfold MmUse; decide)))
      fun _ _ h => winSq_q M h
  -- Four squarings.
  have sq0 : RelCT isa (Two fun (q : XPub × Nat) s => q.2 < 2 ∧ WinI q.1 q.2 s) (M.mm aY aY aY)
      (Two fun (q : XPub × Nat) s => WinQ q.1 s) :=
    two_post (two_map (fun q : XPub × Nat => q.1.ws)
      (fun _ _ ⟨_, _, _, _, _, _, _, hI, _⟩ => ⟨_, hI.ctx.good, Nat.le_refl _⟩)
      (M.ct (by unfold MmUse; decide))) fun q s ⟨_, t₀, minv, X, Xc, E, v, hI, hw, hw', hR, hXN, hv⟩ => by
        have hp : v * 16 ^ q.2 < 2 ^ 56 := by
          have : 16 ^ q.2 ≤ 16 := by rcases (show q.2 = 0 ∨ q.2 = 1 by omega) with h | h <;> rw [h] <;> decide
          have := Nat.mul_le_mul_left v this; omega
        exact winSq_q M ⟨minv, X, Xc, _, hI.ctx, hI.tab, hI.ylt, hI.v, hp, hw, hw', hR⟩
  refine RelCT.seq (R := Two fun (q : XPub × Nat) s => WinS q.1 s) ?_ ?_
  · simp only [seqs]
    exact RelCT.seq sq0 (RelCT.seq sq (RelCT.seq sq (RelCT.seq sq winMid_ct)))
  -- The selection, `Y := Y T` and the count.
  refine RelCT.seqs_append (by simp [tabSelect_eq]) (by simp) ?_
  refine RelCT.seq (two_post (Ψ := fun (q : XPub × Nat) s => WinT q.1 s)
    (two_map (fun q : XPub × Nat => q.1) (fun _ _ h => h.1) tabSel_ct) fun q s h => ?_) ?_
  · obtain ⟨⟨minv, X, Xc, v, hc, hw, hw', hv, ht, hN⟩, minv', X', Xc', hc₂, htab, -, -⟩ := h
    refine WP.mono (tabSel_ok hc hw hw' hv ht hN) fun t ⟨hc', hT, _, _⟩ => ⟨minv, X, Xc, hc', ?_, hw, hw'⟩
    have hX : X' = X := hc₂.n.symm.trans hc.n
    rw [hT, ← hX]; exact htab.lt _ hv
  simp only [seqs]
  refine RelCT.seq (two_post (Ψ := fun (q : XPub × Nat) t => t.gpr .x0 = off q.1.B q.1.o)
    (two_map (fun q : XPub × Nat => q.1.ws) (fun _ _ ⟨minv, _, _, hc, _⟩ => ⟨minv, hc.good, Nat.le_refl _⟩)
      (M.ct (o := aY) (a := aY) (b := Crt.aT) (by unfold MmUse; decide)))
    fun q s ⟨minv, X, Xc, hc, hT, hw, hw'⟩ => ?_) ?_
  · exact WP.mono (M.mm_ok (o := aY) (a := aY) (b := Crt.aT) hc.good (Nat.le_refl _) hw (by omega)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
      (by rw [hc.n]; exact hT)) fun t ⟨hg, _⟩ => hg.x0
  exact x0_ct (fun q : XPub × Nat => off q.1.B q.1.o) (fun _ _ h => h) (by taint_decide)

/-- The two windows of a byte leak the same in runs with the same workspace. -/
theorem crtWins_ct (M : Mont) :
    RelCT isa (Two fun p s => 0 < 2 ∧ WinI p 0 s) (.loop (seqs (expWin M.mm)) (.nonzero .x .x3))
      (Two fun p s => WinI p 2 s) :=
  two_loop (Φ := WinI) (fun _ => 2) (crtWin_ct M)
    fun _ _ _ hj ⟨t₀, minv, X, Xc, E, v, hI, hw, hw', hR, hXN, hv⟩ =>
      WP.mono (crtWinStep_ok M hw hw' hR hv hj hI) fun _ ⟨hI', hz⟩ =>
        ⟨eval_nz_count hj hz, fun _ => ⟨t₀, minv, X, Xc, E, v, hI', hw, hw', hR, hXN, hv⟩,
          fun h => h ▸ ⟨t₀, minv, X, Xc, E, v, hI', hw, hw', hR, hXN, hv⟩⟩

/-! ## The bytes of the exponent -/

/-- After `i` bytes of the exponent (at `a.ptr`, `a.len` bytes). -/
def CBytesInv (a : BPub) (i : Nat) (s : State) : Prop :=
  ∃ (t₀ : State) (minv : BitVec 64) (X Xc : Nat) (eb : List Byte),
    CByteInv t₀ (off a.x.B a.x.o) a.x.wx minv X Xc False 0 a.ptr eb.length eb i s ∧ 2 ≤ a.x.wx ∧
    a.x.wx < 2 ^ 30 ∧ Nat.Coprime (2 ^ (64 * a.x.wx)) X ∧ Xc < X ∧
    eb.length = a.len ∧ eb.length < 2 ^ 31 ∧ Src t₀ a.x.B a.x.Z a.ptr eb ∧
    ∀ i < eb.length, slot a.x.wx 8 + tabBytes a.x.wx ≤ ofs (off a.x.B a.x.o) (a.ptr + BitVec.ofNat 64 i)

/-- The byte's address. -/
def byteAddr : List Instr := [ldh .x3 Crt.sExp, ldh .x4 Crt.sI, .add .x .x3 .x3 .x4]

/-- The byte into `sV`, and the window count. -/
def byteLoad : List Instr := [.ldrb .x3 .x3 0, sth .x3 Crt.sV, movi .x3 2, sth .x3 Crt.sBit]

theorem crtByteHead_eq : byteHead = byteAddr ++ byteLoad := rfl

/-- After the byte's address: it, and the rest of the head. -/
def CHeadMid (q : BPub × Nat) (s : State) : Prop :=
  s.gpr .x0 = off q.1.x.B q.1.x.o ∧ s.gpr .x3 = q.1.ptr + BitVec.ofNat 64 q.2 ∧
    WP isa (.block byteLoad) s fun t => 0 < 2 ∧ WinI q.1.x 0 t

theorem pins_cBytes : Pins (fun (q : BPub × Nat) s => q.2 < q.1.len ∧ CBytesInv q.1 q.2 s) [.x0] :=
  pins_x0B (fun q : BPub × Nat => off q.1.x.B q.1.x.o) fun _ _ ⟨_, _, _, _, _, _, hI, _⟩ => hI.ctx.good.x0

theorem pins_cHeadMid : Pins CHeadMid [.x0, .x3] := by
  rintro q s₁ s₂ ⟨a₁, b₁, -⟩ ⟨a₂, b₂, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a₁, a₂]
  · rw [b₁, b₂]

/-- The byte's address, in the workspace at `P`. -/
theorem byteAddr_run {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : CExpCtx t P wx minv X Xc) {ep : Addr} {i : Nat} (he : word t.mem P (8 * Crt.sExp) = ep)
    (hi : word t.mem P (8 * Crt.sI) = BitVec.ofNat 64 i) :
    WP isa (.block byteAddr) t fun t' => t'.gpr .x3 = ep + BitVec.ofNat 64 i ∧ Keep [.x3, .x4] t t' := by
  refine WP.keep [.x3, .x4] ?_ (by decide) (by decide) (by decide +kernel)
  brun [byteAddr, hc.good.x0, hdr_enc (show Crt.sExp < 32 by decide), hdr_enc (show Crt.sI < 32 by decide),
    hc.ld (i := Crt.sExp) (by decide), hc.ld (i := Crt.sI) (by decide), he, hi]

/-- The byte's address, and the rest of the head by `crtByteHead_ok`. -/
theorem byteAddr_ok {q : BPub × Nat} {s : State} (h : q.2 < q.1.len ∧ CBytesInv q.1 q.2 s) :
    WP isa (.block byteAddr) s (CHeadMid q) := by
  obtain ⟨hi, t₀, minv, X, Xc, eb, hI, hw, hw', hR, hXN, hL, -, he, hout⟩ := h
  have hc := hI.ctx
  have hi' : q.2 < eb.length := by omega
  have hw₁ := WP.block_append_iff.mp (crtByteHead_eq ▸ crtByteHead_ok rfl hi' he.rd he.val hout hI)
  refine WP.mono (wp_and hw₁ (byteAddr_run hc hI.e hI.idx)) fun t ⟨h₂, h3, k⟩ =>
      ⟨(k.gpr .x0 (by decide)).trans hc.good.x0, h3, WP.mono h₂ fun t' ⟨_, _, hB⟩ =>
        ⟨by decide, t', minv, X, Xc, _, _, hB, hw, hw', hR, hXN, (eb[q.2]'hi').isLt⟩⟩

/-- One byte of the exponent leaks the same in runs with the same workspace
and the same exponent's pointer and length. -/
theorem crtByte_ct (M : Mont) : RelCT isa (Two fun (q : BPub × Nat) s => q.2 < q.1.len ∧ CBytesInv q.1 q.2 s)
    (seqs [.block byteHead, .loop (seqs (expWin M.mm)) (.nonzero .x .x3), .block byteNext]) fun _ _ => True := by
  simp only [seqs]
  rw [crtByteHead_eq]
  have h₃ : RelCT isa (Two fun (p : XPub) s => WinI p 2 s) (.block byteNext) fun _ _ => True :=
    x0_ct (fun p : XPub => off p.B p.o) (fun _ _ ⟨_, _, _, _, _, _, hI, _⟩ => hI.ctx.good.x0) (by taint_decide)
  exact RelCT.seq (RelCT.block_append (RelCT.seq (two_piece _ pins_cBytes (by taint_decide) fun _ _ h => byteAddr_ok h)
      (two_piece _ pins_cHeadMid (by taint_decide) fun _ _ h => h.2.2)))
    (RelCT.seq (two_map (fun q : BPub × Nat => q.1.x) (fun _ _ h => h) (crtWins_ct M)) h₃)

/-! ## The table -/

/-- `toEnt a` into entry `q.2`: its bases, as the header gives them. -/
def EntP (a : Nat) (q : XPub × Nat) (s : State) : Prop :=
  XCtx q.1 s ∧ word s.mem (off q.1.B q.1.o) (8 * Crt.sEnt) = off (off q.1.B q.1.o) (slot q.1.wx (8 + q.2)) ∧
    q.2 < 16 ∧ a < 8

/-- `toEnt a`'s bases. -/
def EntB (a : Nat) (q : XPub × Nat) (s : State) : Prop :=
  s.gpr .x12 = BitVec.ofNat 64 q.1.wx ∧ s.gpr .x16 = off (off q.1.B q.1.o) (slot q.1.wx a) ∧
    s.gpr .x17 = off (off q.1.B q.1.o) (slot q.1.wx (8 + q.2))

theorem pins_entB (a : Nat) : Pins (EntB a) [.x12, .x16, .x17] := by
  intro q s₁ s₂ ⟨a₁, b₁, c₁⟩ ⟨a₂, b₂, c₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [a₁, a₂]
  · rw [b₁, b₂]
  · rw [c₁, c₂]

/-- `toEnt a`'s loads, in the workspace at `P`. -/
theorem toEntHd_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : CExpCtx t P wx minv X Xc) {a e : Nat} (ha : a < 8) (he : word t.mem P (8 * Crt.sEnt) = off P e) :
    WP isa (.block [ldh .x12 sW, ldh .x16 (sArr a), ldh .x17 Crt.sEnt]) t fun t' =>
      t'.gpr .x12 = BitVec.ofNat 64 wx ∧ t'.gpr .x16 = off P (slot wx a) ∧ t'.gpr .x17 = off P e :=
  WP.mono (WP.keep [.x12, .x16, .x17] (Q := fun t' => t'.gpr .x12 = BitVec.ofNat 64 wx ∧
      t'.gpr .x16 = off P (slot wx a) ∧ t'.gpr .x17 = off P e)
    (by brun [hc.good.x0, hdr_enc (show sW < 32 by decide), hdr_enc (sArr_lt ha),
      hdr_enc (show Crt.sEnt < 32 by decide), hc.ld (i := sArr a) (sArr_lt ha), hc.ld (i := Crt.sEnt) (by decide),
      hc.ld (i := sW) (by decide), hc.good.hdr.harr a ha, he, hc.good.hdr.hw]) rfl rfl rfl) fun _ h => h.1

/-- `toEnt a` leaks the same in runs with the same workspace and entry,
given that the taint analysis checks its loads from `x0`. -/
theorem toEnt_ct {a : Nat} {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x12 sW, ldh .x16 (sArr a), ldh .x17 Crt.sEnt])
      hc).isSome = true) :
    RelCT isa (Two (EntP a)) (seqs (toEnt a)) fun _ _ => True := by
  unfold toEnt
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := EntB a) [.x0] (pins_x0B (fun q : XPub × Nat => off q.1.B q.1.o)
    fun _ _ h => h.1.x0) hT fun q s ⟨⟨minv, X, Xc, hc, _⟩, he, hj, ha⟩ => ?_)
    (two_taint [.x12, .x16, .x17] (pins_entB a) (by taint_decide))
  exact WP.mono (toEntHd_ok hc ha he) fun _ h => h

/-- After `i` of the table's products, in the workspace of `p`. -/
def BldI (p : XPub) (i : Nat) (s : State) : Prop :=
  ∃ (t₀ : State) (minv : BitVec 64) (X Xc : Nat), BuildInv t₀ (off p.B p.o) p.wx minv X Xc False 0 i s ∧
    2 ≤ p.wx ∧ p.wx < 2 ^ 30 ∧ Nat.Coprime (2 ^ (64 * p.wx)) X ∧ Xc < X

/-- After the product `i`: the entry `i + 1` in `sEnt`. -/
def BldM (q : XPub × Nat) (s : State) : Prop :=
  XCtx q.1 s ∧ word s.mem (off q.1.B q.1.o) (8 * Crt.sEnt) = off (off q.1.B q.1.o) (slot q.1.wx (8 + (q.2 + 1))) ∧
    q.2 < 14

/-- `sEnt` up from entry `j` keeps the context. -/
theorem nextEnt_post {p : XPub} {j : Nat} {s : State} (h : XCtx p s)
    (he : word s.mem (off p.B p.o) (8 * Crt.sEnt) = off (off p.B p.o) (slot p.wx (8 + j))) :
    WP isa nextEnt s fun t => XCtx p t ∧
      word t.mem (off p.B p.o) (8 * Crt.sEnt) = off (off p.B p.o) (slot p.wx (8 + (j + 1))) := by
  obtain ⟨minv, X, Xc, hc, hXN, hw, hw'⟩ := h
  refine WP.mono (nextEnt_ok hc hw' he) fun t ⟨hm, k⟩ => ?_
  have o := writeW_outside s.mem (off p.B p.o) (d := 8 * Crt.sEnt)
    (off (off p.B p.o) (slot p.wx (8 + j) + 8 * (p.wx + 2))) (by decide)
  rw [← hm] at o
  exact ⟨⟨minv, X, Xc, hc.of_frm (Frm.of_outside o (by simp [crtExpRanges, crtWinRanges])) k.wr
    (k.gpr .x0 (by decide)), hXN, hw, hw'⟩, by rw [hm, word_writeW_self, ← slot_succ]; rfl⟩

/-- A product of the table's build leaks the same in runs with the same workspace. -/
theorem buildBody_ct (M : Mont) :
    RelCT isa (Two fun (q : XPub × Nat) s => q.2 < 14 ∧ BldI q.1 q.2 s)
      (seqs (tabBody M.mm)) fun _ _ => True := by
  -- `T := T Xc`.
  have mmPart : RelCT isa (Two fun (q : XPub × Nat) s => q.2 < 14 ∧ BldI q.1 q.2 s) (M.mm Crt.aT Crt.aT Crt.aXc)
      (Two BldM) := by
    refine two_post (two_map (fun q : XPub × Nat => q.1.ws)
      (fun _ _ ⟨_, _, minv, _, _, hI, _⟩ => ⟨minv, hI.ctx.good, Nat.le_refl _⟩)
      (M.ct (o := Crt.aT) (a := Crt.aT) (b := Crt.aXc) (by unfold MmUse; decide)))
      fun q s ⟨hi, t₀, minv, X, Xc, hI, hw, hw', hR, hXN⟩ => ?_
    have hc := hI.ctx
    refine WP.mono (M.mm_ok (o := Crt.aT) (a := Crt.aT) (b := Crt.aXc) hc.good (Nat.le_refl _) hw (by omega)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
      (by rw [hc.x, hc.n]; exact hXN)) fun t ⟨_, _, _, ha, k⟩ => ?_
    have f : Frm (off q.1.B q.1.o) (buildRanges q.1.wx) s.mem t.mem := Frm.of_arrays ha (by simp [buildRanges])
    exact ⟨⟨minv, X, Xc, hc.of_frm (f.mono (buildRanges_sub q.1.wx)) k.wr (k.gpr .x0 (by decide)), hXN, hw, hw'⟩,
      by rw [ha.hslot (by decide)]; exact hI.ent, hi⟩
  -- `sEnt` up.
  have entPart : RelCT isa (Two BldM) nextEnt (Two fun (q : XPub × Nat) s => EntP Crt.aT (q.1, q.2 + 2) s) :=
    two_post (x0_ct (fun q : XPub × Nat => off q.1.B q.1.o) (fun _ _ h => h.1.x0) (by taint_decide))
      fun q s ⟨hx, he, hi⟩ => WP.mono (nextEnt_post hx he) fun t ⟨hx', he'⟩ =>
        ⟨hx', he', by simp only; omega, by decide⟩
  -- Entry `i + 2 := T`, the count.
  have restPart : RelCT isa (Two fun (q : XPub × Nat) s => EntP Crt.aT (q.1, q.2 + 2) s)
      (seqs (toEnt Crt.aT ++ [.block [ldh .x3 Crt.sBit, .subImm .x .x3 .x3 1, sth .x3 Crt.sBit]]))
      fun _ _ => True := by
    refine RelCT.seqs_append (by simp [toEnt]) (by simp) (RelCT.seq (two_post (Ψ := fun q t =>
      t.gpr .x0 = off q.1.B q.1.o) (two_map (fun q : XPub × Nat => (q.1, q.2 + 2)) (fun _ _ h => h)
        (toEnt_ct (by taint_decide))) fun q s ⟨⟨minv, X, Xc, hc, _, hw, hw'⟩, he, hj, ha⟩ =>
      WP.mono (toEnt_ok hc hw hw' ha hj he) fun t ⟨_, _, k⟩ => (k.gpr .x0 (by decide)).trans hc.good.x0) ?_)
    simp only [seqs]
    exact x0_ct (fun q : XPub × Nat => off q.1.B q.1.o) (fun _ _ h => h) (by taint_decide)
  unfold tabBody
  refine RelCT.seqs_append (by simp) (by simp [toEnt]) (RelCT.seq ?_ restPart)
  simp only [seqs]
  exact RelCT.seq mmPart entPart

/-- `tabBuild_ok`'s hypotheses, for the bounds. -/
def TPre (p : XPub) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (X Xc : Nat), CExpCtx s (off p.B p.o) p.wx minv X Xc ∧ Xc < X ∧
    wv s.mem (off p.B p.o) (slot p.wx aY) p.wx < X ∧ 2 ≤ p.wx ∧ p.wx < 2 ^ 30 ∧
    Nat.Coprime (2 ^ (64 * p.wx)) X

theorem toEnt_post {a : Nat} {q : XPub × Nat} {s : State} (h : EntP a q s) :
    WP isa (seqs (toEnt a)) s fun t => XCtx q.1 t ∧
      ∀ k < 32, word t.mem (off q.1.B q.1.o) (8 * k) = word s.mem (off q.1.B q.1.o) (8 * k) := by
  obtain ⟨⟨minv, X, Xc, hc, hXN, hw, hw'⟩, he, hj, ha⟩ := h
  have hn := hc.scrT.nowrap
  have hE := ent_le q.1.wx hj
  have hE8 := slot_mono q.1.wx (show 8 ≤ 8 + q.2 by omega)
  refine WP.mono (toEnt_ok hc hw hw' ha hj he) fun t ⟨_, o, k⟩ => ⟨⟨minv, X, Xc, hc.of_frm
    (Frm.of_outside (o.mono (o' := slot q.1.wx 8) (n' := tabBytes q.1.wx) hE8 (by omega)) (by simp [crtExpRanges]))
    k.wr (k.gpr .x0 (by decide)), hXN, hw, hw'⟩, fun k hk => ?_⟩
  exact o.word (by have := hdr_lt_slot q.1.wx (8 + q.2) hk; omega) (by omega)

/-- The table's first entries leak the same in runs with the same workspace. -/
theorem tabPre_ct : RelCT isa (Two TPre) (seqs tabPre) fun _ _ => True := by
  unfold tabPre
  refine RelCT.seqs_append (by simp) (by simp [toEnt]) ?_
  simp only [seqs]
  -- The base.
  refine RelCT.seq (two_post (Ψ := fun p s => EntP aY (p, 0) s)
    (x0_ct (fun p : XPub => off p.B p.o) (fun _ _ ⟨_, _, _, hc, _⟩ => hc.good.x0) (by taint_decide))
    fun p s ⟨minv, X, Xc, hc, hXN, hY, hw, hw', hR⟩ => ?_) ?_
  · refine WP.mono (tabInit_ok hc hw') fun t ⟨hm, k⟩ => ?_
    have o1 := writeW_outside s.mem (off p.B p.o) (d := 8 * Crt.sTab) (off (off p.B p.o) (slot p.wx 8)) (by decide)
    have o2 := writeW_outside (s.mem.writeW (off (off p.B p.o) (8 * Crt.sTab)) (off (off p.B p.o) (slot p.wx 8)))
      (off p.B p.o) (d := 8 * Crt.sEnt) (off (off p.B p.o) (slot p.wx 8)) (by decide)
    rw [← hm] at o2
    have f : Frm (off p.B p.o) (buildRanges p.wx) s.mem t.mem :=
      (Frm.of_outside o1 (by simp [buildRanges])).trans (Frm.of_outside o2 (by simp [buildRanges]))
    exact ⟨⟨minv, X, Xc, hc.of_frm (f.mono (buildRanges_sub p.wx)) k.wr (k.gpr .x0 (by decide)), hXN, hw, hw'⟩,
      by rw [hm, word_writeW_self]; rfl, by simp only; omega, by decide⟩
  -- `T_0 := Y`.
  refine RelCT.seqs_append (by simp [toEnt]) (by simp) (RelCT.seq (two_post
    (Ψ := fun p s => XCtx p s ∧ word s.mem (off p.B p.o) (8 * Crt.sEnt) = off (off p.B p.o) (slot p.wx (8 + 0)))
    (two_map (fun p : XPub => (p, 0)) (fun _ _ h => h) (toEnt_ct (by taint_decide))) fun p s h =>
      WP.mono (toEnt_post h) fun t ⟨hx, hh⟩ => ⟨hx, by rw [hh _ (by decide)]; exact h.2.1⟩) ?_)
  refine RelCT.seqs_append (by simp) (by simp [toEnt]) ?_
  simp only [seqs]
  -- `sEnt` up.
  refine RelCT.seq (two_post (Ψ := fun p s => EntP Crt.aXc (p, 1) s)
    (x0_ct (fun p : XPub => off p.B p.o) (fun _ _ h => h.1.x0) (by taint_decide))
    fun p s ⟨hx, he⟩ => WP.mono (nextEnt_post hx he) fun t ⟨hx', he'⟩ => ⟨hx', he', show 1 < 16 by decide, by decide⟩) ?_
  -- `T_1 := Xc`.
  refine RelCT.seqs_append (by simp [toEnt]) (by simp [copyArr]) (RelCT.seq (two_post
    (Ψ := fun p s => XCtx p s) (two_map (fun p : XPub => (p, 1)) (fun _ _ h => h) (toEnt_ct (by taint_decide)))
    fun p s h => WP.mono (toEnt_post h) fun t ⟨hx, _⟩ => hx) ?_)
  -- `T := Xc`, the count.
  refine RelCT.seqs_append (by simp [copyArr]) (by simp) (RelCT.seq (two_post
    (Ψ := fun p t => t.gpr .x0 = off p.B p.o) (two_map (fun p : XPub => p.ws) (fun _ _ h => h.goodW)
      (copyArr_ct (by decide) (by decide) (by taint_decide))) fun p s ⟨minv, X, Xc, hc, _, hw, hw'⟩ =>
    WP.mono (copyArr_ok hc.good (Nat.le_refl _) (by omega) (by omega) (o := Crt.aT) (a := Crt.aXc)
      (by decide) (by decide) (by decide)) fun t ⟨_, _, k⟩ => (k.gpr .x0 (by decide)).trans hc.good.x0) ?_)
  simp only [seqs]
  exact x0_ct (fun p : XPub => off p.B p.o) (fun _ _ h => h) (by taint_decide)

/-- The table's build leaks the same in runs with the same workspace. -/
theorem tabBuild_ct (M : Mont) : RelCT isa (Two TPre) (seqs (tabBuild M.mm)) fun _ _ => True := by
  rw [tabBuild_eq]
  refine RelCT.seqs_append (by simp [tabPre]) (by simp) (RelCT.seq (two_post (Ψ := fun p s => 0 < 14 ∧ BldI p 0 s)
    tabPre_ct fun p s ⟨minv, X, Xc, hc, hXN, hY, hw, hw', hR⟩ =>
      WP.mono (tabPre_ok (Q := False) (x := 0) hc hw hw' hXN False.elim hY False.elim) fun t hI =>
        ⟨by decide, s, minv, X, Xc, hI, hw, hw', hR, hXN⟩) ?_)
  simp only [seqs, tabLoop]
  exact (two_loop (Φ := BldI) (Ψ := fun _ _ => True) (fun _ => 14) (buildBody_ct M)
    fun p i s hi ⟨t₀, minv, X, Xc, hI, hw, hw', hR, hXN⟩ =>
      WP.mono (buildStep_ok M hw hw' hR hXN False.elim hi hI) fun s' ⟨hI', hz⟩ =>
        ⟨eval_nz_count hi hz, fun _ => ⟨t₀, minv, X, Xc, hI', hw, hw', hR, hXN⟩, fun _ => trivial⟩).mono
    (fun _ _ h => h) fun _ _ _ => trivial

/-! ## The exponentiation -/

/-- The link into `x5`: the modulus' workspace. -/
theorem crtLink_ok {sp sl : Nat} {a : BPub} {s : State} (h : EPre sp sl a s) :
    WP isa (.block [ldh .x5 Crt.sLink]) s fun t => t.gpr .x0 = off a.x.B a.x.o ∧ t.gpr .x5 = a.x.B := by
  obtain ⟨_, _, _, _, _, hc, -⟩ := h
  exact WP.mono (WP.keep [.x5] (Q := fun t => t.gpr .x5 = a.x.B)
    (by brun [hc.x0, hdr_enc (show Crt.sLink < 32 by decide), hc.ld' (show Crt.sLink < 32 by decide), hc.link'])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨h1, k⟩ => ⟨(k.gpr .x0 (by decide)).trans hc.x0, h1⟩

/-- `expLoop`'s start keeps `tabBuild_ok`'s hypotheses. -/
theorem crtExpInit_tpre {sp sl : Nat} {a : BPub} {s : State} (h : EPre sp sl a s) :
    WP isa (expInit sp sl) s (TPre a.x) := by
  obtain ⟨minv, X, x, y, eb, hc, hw2, hwx, hw30, hn, hinv, hodd, hxl, -, hyl, -, hsp, hsl, hep, hel, -⟩ := h
  have hPn := hc.scrT.nowrap
  have hY0 := slot_le (w := a.x.wx) (show aY < 8 by decide)
  have hY1 := hdr_lt_slot a.x.wx aY (show 31 < 32 by decide)
  have hc₀ : CExpCtx s (off a.x.B a.x.o) a.x.wx minv X (wv s.mem (off a.x.B a.x.o) (slot a.x.wx Crt.aXc) a.x.wx) :=
    ⟨hc.good, hc.scrT, hn, hinv, rfl⟩
  refine WP.mono (crtExpInit_ok hc hsp hsl hep hel) fun t₁ ⟨hm₁, k₁⟩ => ?_
  have o1 := writeW_outside s.mem (off a.x.B a.x.o) (d := 8 * Crt.sExp) a.ptr (by decide)
  have o2 := writeW_outside (s.mem.writeW (off (off a.x.B a.x.o) (8 * Crt.sExp)) a.ptr) (off a.x.B a.x.o)
    (d := 8 * Crt.sExpLen) (BitVec.ofNat 64 eb.length) (by decide)
  have o3 := writeW_outside ((s.mem.writeW (off (off a.x.B a.x.o) (8 * Crt.sExp)) a.ptr).writeW
    (off (off a.x.B a.x.o) (8 * Crt.sExpLen)) (BitVec.ofNat 64 eb.length)) (off a.x.B a.x.o) (d := 8 * Crt.sI)
    (BitVec.ofNat 64 0) (by decide)
  rw [← hm₁] at o3
  have f₁ : Frm (off a.x.B a.x.o) (crtExpRanges a.x.wx) s.mem t₁.mem :=
    ((Frm.of_outside o1 (by simp [crtExpRanges])).trans (Frm.of_outside o2 (by simp [crtExpRanges]))).trans
      (Frm.of_outside o3 (by simp [crtExpRanges]))
  refine ⟨minv, X, _, hc₀.of_frm f₁ k₁.wr (k₁.gpr .x0 (by decide)), hxl, ?_, hw2, by omega,
    VG.Proof.Bignum.coprime_pow2 hodd _⟩
  rw [o3.wv (by unfold Crt.sI sFn at *; omega) (by omega), o2.wv (by unfold Crt.sExpLen sFn at *; omega)
    (by omega), o1.wv (by unfold Crt.sExp sFn at *; omega) (by omega)]
  exact hyl

/-- `expLoop M.mm sp sl` is constant time, given that the taint analysis
checks its start after the link's load. -/
theorem crtExpLoop_ct (M : Mont) {sp sl : Nat} {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0, .x5]) (.block [ldw .x3 .x5 sp, sth .x3 Crt.sExp, ldw .x3 .x5 sl,
      sth .x3 Crt.sExpLen, movi .x3 0, sth .x3 Crt.sI]) hc).isSome = true) :
    ExpCT M sp sl := by
  unfold ExpCT
  rw [expLoop_eq, ← List.cons_append]
  refine RelCT.seqs_append (by simp) (by simp) (RelCT.seq (two_post
    (Ψ := fun a s => 0 < a.len ∧ CBytesInv a 0 s) ?_ fun a s h => ?_) ?_)
  · -- The start and the table.
    rw [← List.singleton_append]
    refine RelCT.seqs_append (by simp) (by simp [tabBuild_eq, tabPre]) (RelCT.seq (two_post (Ψ := fun a s => TPre a.x s)
      ?_ fun _ _ h => by simp only [seqs]; exact crtExpInit_tpre h) (two_map (fun a : BPub => a.x) (fun _ _ h => h) (tabBuild_ct M)))
    simp only [seqs, expInit]
    exact RelCT.block_append (l₁ := ([ldh .x5 Crt.sLink] : List Instr))
      (RelCT.seq (two_piece (Ψ := fun (a : BPub) t => t.gpr .x0 = off a.x.B a.x.o ∧ t.gpr .x5 = a.x.B) [.x0]
        (pins_x0B (fun a : BPub => off a.x.B a.x.o) fun a s (h : EPre sp sl a s) =>
          let ⟨_, _, _, _, _, hc, _⟩ := h; hc.x0) (by taint_decide)
        fun _ _ h => crtLink_ok h)
      (two_taint [.x0, .x5] (pins_of (fun a r => if r = .x0 then off a.x.B a.x.o else a.x.B)
        fun a s h r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact h.1
          · exact h.2) hT))
  · obtain ⟨minv, X, x, y, eb, hc, hw2, hwx, hw30, hn, hinv, hodd, hxl, -, hyl, -, hsp, hsl, hep, hel, hL, hL1, hL2,
      he⟩ := h
    have hPn := hc.scrT.nowrap
    have hBn := hc.scr.nowrap
    have hi := hc.hi
    have hlo := hc.lo
    have h256 : 256 ≤ slot a.x.wx 8 := by unfold slot hdrBytes; omega
    have hout : ∀ i < eb.length, slot a.x.wx 8 + tabBytes a.x.wx ≤ ofs (off a.x.B a.x.o) (a.ptr + BitVec.ofNat 64 i) :=
      fun i hi' => by
        have := he.out i hi'
        rcases ofs_rebase a.x.B (a.ptr + BitVec.ofNat 64 i) (o := a.x.o) (by omega) with ⟨_, h2⟩ | ⟨h1, _⟩
        · omega
        · omega
    exact WP.mono (crtExpHead_ok M (Q := False) (x := 0) hc hw2 hwx hw30 hn hinv hodd hxl False.elim hyl False.elim
      hsp hsl hep hel) fun t hI => ⟨by omega, s, minv, X, _, eb, hI, hw2, by omega,
        VG.Proof.Bignum.coprime_pow2 hodd _, hxl, hL, by omega, he, hout⟩
  simp only [seqs, expBytes]
  refine (two_loop (Φ := CBytesInv) (Ψ := fun _ _ => True) (fun a => a.len) (crtByte_ct M) ?_).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  rintro a i s hi ⟨t₀, minv, X, Xc, eb, hI, hw, hw', hR, hXN, hL, hL', he, hout⟩
  exact WP.mono (crtByte_ok M hw hw' hR rfl hL' (by omega) he.rd he.val hout hI)
    fun s' ⟨hI', hz⟩ => ⟨eval_nz_count hi (by rw [← hL]; exact hz), fun _ => ⟨t₀, minv, X, Xc, eb, hI', hw, hw', hR,
      hXN, hL, hL', he, hout⟩, fun _ => trivial⟩

theorem expLoop_ct_P (M : Mont) : ExpCT M Crt.sDp Crt.sPlen := crtExpLoop_ct M (by taint_decide)

theorem expLoop_ct_Q (M : Mont) : ExpCT M Crt.sDq Crt.sQlen := crtExpLoop_ct M (by taint_decide)

end VG.Proof.Bignum.AArch64
