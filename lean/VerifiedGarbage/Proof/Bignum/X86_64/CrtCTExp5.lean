module

public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# RSA with the CRT on x86-64: the exponentiation by windows of 5 bits is constant time

As `crtExpLoop_ct` for `Crt.expLoop5`. Its one branch, on whether fewer
than 5 bits are left, is on public numbers: after `j` windows of an
exponent of `L` bytes, `padBits L + 8 i = 5 j + b` with `b < 8` decides
the `i` bytes read and the `b` bits left. A byte is read at its pointer
plus `i`, both public; the bits flow only into data and the selection's
masks. The windows' count, `(padBits L + 8 L) / 5`, is public too.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- `expLoop5S Sq.mm M.mm S.code sp sl` is constant time. -/
def ExpCT5S (M : Mont) (Sq : MontS) (S : CrtSel 32) (sp sl : Nat) : Prop :=
  RelCT isa (Two (EPre5 sp sl)) (seqs (Crt.expLoop5S Sq.mm M.mm S.code sp sl)) fun _ _ => True

/-- `expLoop5 M.mm S.code sp sl` is constant time. -/
def ExpCT5 (M : Mont) (S : CrtSel 32) (sp sl : Nat) : Prop :=
  RelCT isa (Two (EPre5 sp sl)) (seqs (Crt.expLoop5 M.mm S.code sp sl)) fun _ _ => True

/-- The number of windows of an exponent of `a.len` bytes. -/
def K5 (a : BPub) : Nat := (padBits a.len + 8 * a.len) / 5

theorem K5_mul (a : BPub) : 5 * K5 a = padBits a.len + 8 * a.len := by
  have := win5_dvd a.len; unfold K5; omega

/-! ## A window -/

/-- After `j` windows of the exponent at `a.ptr`, `a.len` bytes. -/
def Win5I (a : BPub) (j : Nat) (s : State) : Prop :=
  ∃ (t₀ : State) (minv : BitVec 64) (X Xc : Nat) (eb : List Byte),
    W5Inv t₀ (off a.x.B a.x.o) a.x.wx minv X Xc False 0 a.ptr eb.length eb j s ∧ 2 ≤ a.x.wx ∧
    a.x.wx < 2 ^ 30 ∧ Nat.Coprime (2 ^ (64 * a.x.wx)) X ∧ eb.length = a.len ∧ eb.length < 2 ^ 31 ∧
    Src t₀ a.x.B a.x.Z a.ptr eb ∧
    ∀ i < eb.length, slot a.x.wx 8 + tabBytes a.x.wx 32 ≤ ofs (off a.x.B a.x.o) (a.ptr + BitVec.ofNat 64 i)

/-- After the comparison of the bits left with 5. -/
def W5Cmp (q : BPub × Nat) (s : State) : Prop :=
  q.2 < K5 q.1 ∧ ∃ (t₀ : State) (minv : BitVec 64) (X Xc : Nat) (eb : List Byte) (i b : Nat),
    eb.length = q.1.len ∧ padBits eb.length + 8 * i = 5 * q.2 + b ∧ b < 8 ∧ i ≤ eb.length ∧
    s.cf = some (decide (b < 5)) ∧ W5At t₀ (off q.1.x.B q.1.x.o) q.1.x.wx minv X Xc False 0 q.1.ptr eb.length eb i b s

/-- After `refill`'s loads of the exponent's pointer and the byte's index. -/
def W5Ld (q : BPub × Nat) (s : State) : Prop :=
  s.gpr .rdi = off q.1.x.B q.1.x.o ∧ s.gpr .rax = q.1.ptr ∧
    ∃ i b, padBits q.1.len + 8 * i = 5 * q.2 + b ∧ b < 8 ∧ s.gpr .rcx = BitVec.ofNat 64 i

theorem pins_w5Cmp : Pins W5Cmp [.rdi] :=
  pins_rdi (fun q : BPub × Nat => off q.1.x.B q.1.x.o) fun _ _ ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hI⟩ =>
    hI.ctx.good.rdi

theorem pins_w5Ld : Pins W5Ld [.rdi, .rax, .rcx] := by
  rintro q s₁ s₂ ⟨d₁, a₁, i₁, b₁, h₁, hb₁, c₁⟩ ⟨d₂, a₂, i₂, b₂, h₂, hb₂, c₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [d₁, d₂]
  · rw [a₁, a₂]
  · have : i₁ = i₂ := by omega
    rw [c₁, c₂, this]

theorem refill_eq : Crt.refill = ([.mov .rax (.mem (hdr Crt.sExp)), .mov .rcx (.mem (hdr Crt.sI))] : List Instr) ++
    ([.mov .rdx (.mem (hdr Crt.sPow)), .mov .r8 (.mem (hdr Crt.sBit)),
      .movzx8 .rax { base := .rax, index := some .rcx }, .imul .rax .rdx, .alu .or .rax (.mem (hdr Crt.sV)),
      .store (hdr Crt.sV) .rax, .alu .add .rcx (.imm 1), .store (hdr Crt.sI) .rcx, .shift .shr .rdx 8,
      .store (hdr Crt.sPow) .rdx, .alu .add .r8 (.imm 8), .store (hdr Crt.sBit) .r8] : List Instr) := rfl

/-- `refill`'s loads of the exponent's pointer and the byte's index. -/
theorem refillLd_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc n : Nat}
    (hc : CExpCtx t P wx minv X Xc n) {ep : Addr} {i : Nat} (he : word t.mem P (8 * Crt.sExp) = ep)
    (hi : word t.mem P (8 * Crt.sI) = BitVec.ofNat 64 i) :
    WP isa (.block [.mov .rax (.mem (hdr Crt.sExp)), .mov .rcx (.mem (hdr Crt.sI))]) t fun t₁ =>
      t₁.gpr .rax = ep ∧ t₁.gpr .rcx = BitVec.ofNat 64 i ∧ t₁.gpr .rdi = t.gpr .rdi :=
  WP.mono (WP.keep [.rax, .rcx] (Q := fun t₁ => t₁.gpr .rax = ep ∧ t₁.gpr .rcx = BitVec.ofNat 64 i) (by
    xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.ld (i := Crt.sExp) (by decide), hc.ld (i := Crt.sI) (by decide),
      he, hi]) rfl)
    fun _ ⟨⟨h1, h2⟩, k⟩ => ⟨h1, h2, k.gpr (by decide)⟩

/-- The comparison of the bits left with 5, and a byte more if fewer are
left, leak the same in runs with the same exponent's pointer and length. -/
theorem fill_ct : RelCT isa (Two fun (q : BPub × Nat) s => q.2 < K5 q.1 ∧ Win5I q.1 q.2 s)
    (seqs [.block [.mov .rax (.mem (hdr Crt.sBit)), .alu .cmp .rax (.imm 5)],
      .ite .b (.block Crt.refill) (.block [])]) fun _ _ => True := by
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := W5Cmp) [.rdi]
    (pins_rdi (fun q : BPub × Nat => off q.1.x.B q.1.x.o)
      fun _ _ ⟨_, _, _, _, _, _, ⟨_, _, _, _, _, hI⟩, _⟩ => hI.ctx.good.rdi) (by taint_decide)
    fun q s ⟨hj, t₀, minv, X, Xc, eb, ⟨i, b, hib, hb, hiL, hI⟩, _, _, _, hL, _⟩ => ?_) ?_
  · exact WP.mono (bitCmp_ok hI.ctx hI.bit (by omega)) fun t ⟨hcf, hm, k⟩ =>
      ⟨hj, t₀, minv, X, Xc, eb, i, b, hL, hib, hb, hiL, hcf, hI.of_mem hm k (by decide) (k.gpr (by decide))⟩
  refine two_ite (fun q s₁ s₂ h₁ h₂ => ?_) ?_ ?_
  · obtain ⟨_, _, _, _, _, eb₁, i₁, b₁, hL₁, h₁, hb₁, _, c₁, _⟩ := h₁
    obtain ⟨_, _, _, _, _, eb₂, i₂, b₂, hL₂, h₂, hb₂, _, c₂, _⟩ := h₂
    rw [hL₁] at h₁
    rw [hL₂] at h₂
    have : b₁ = b₂ := by omega
    simp only [eval, c₁, c₂, this]
  · -- The byte, at its pointer plus its index.
    rw [refill_eq]
    refine RelCT.block_append (RelCT.seq (two_piece (Ψ := W5Ld) [.rdi]
      (pins_rdi (fun q : BPub × Nat => off q.1.x.B q.1.x.o) fun _ _ ⟨⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hI⟩, _⟩ => hI.ctx.good.rdi) (by taint_decide)
      fun q s ⟨⟨_, t₀, minv, X, Xc, eb, i, b, hL, hib, hb, _, _, hI⟩, _⟩ => ?_)
      (two_taint _ pins_w5Ld (by taint_decide)))
    exact WP.mono (refillLd_ok hI.ctx hI.e hI.idx) fun t ⟨h1, h2, h3⟩ =>
      ⟨h3.trans hI.ctx.good.rdi, h1, i, b, hL ▸ hib, hb, h2⟩
  · exact rdi_ct (fun q : BPub × Nat => off q.1.x.B q.1.x.o)
      (fun _ _ ⟨⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hI⟩, _⟩ => hI.ctx.good.rdi) (by taint_decide)

/-- Within a window, before the selection: the workspace, its table,
`Y < bd X R` (`Y < X` but for lazy squarings) and the bits in `sV`. -/
def WQ5 (p : XPub) (t : State) (bd : Nat → Nat → Nat := fun m _ => m) : Prop :=
  ∃ (minv : BitVec 64) (X Xc b r : Nat), CExpCtx t (off p.B p.o) p.wx minv X Xc 32 ∧
    CTab t.mem (off p.B p.o) p.wx X False 0 32 ∧
    wv t.mem (off p.B p.o) (slot p.wx Public.aY) p.wx < bd X (2 ^ (64 * p.wx)) ∧
    word t.mem (off p.B p.o) (8 * Crt.sPow) = BitVec.ofNat 64 (2 ^ (56 - b)) ∧
    word t.mem (off p.B p.o) (8 * Crt.sV) = BitVec.ofNat 64 (r * 2 ^ (64 - b)) ∧
    word t.mem (off p.B p.o) (8 * Crt.sBit) = BitVec.ofNat 64 b ∧ 5 ≤ b ∧ b ≤ 12 ∧ r < 2 ^ b ∧
    2 ≤ p.wx ∧ p.wx < 2 ^ 30 ∧ Nat.Coprime (2 ^ (64 * p.wx)) X

theorem WQ5.goodW {p : XPub} {t : State} {bd : Nat → Nat → Nat} (h : WQ5 p t bd) : GoodW p.ws t :=
  let ⟨minv, _, _, _, _, hc, _⟩ := h; ⟨minv, hc.good, Nat.le_refl _⟩

/-- A squaring by `Sq` keeps `WQ5` with its bound. -/
theorem winSq5_q (Sq : MontS) {p : XPub} {s : State} (h : WQ5 p s Sq.bd) :
    WP isa Sq.mm s (WQ5 p · Sq.bd) := by
  obtain ⟨minv, X, Xc, b, r, hc, htab, hY, hp, hv, hbit, hb5, hb12, hr, hw, hw', hR⟩ := h
  refine WP.mono (crtSqS_ok Sq (Q := False) (x := 0) (E := 0) hc hw hw' hR hY False.elim)
    fun t ⟨hc', hY', _, hh, hf, _⟩ => ⟨minv, X, Xc, b, r, hc', htab.of_win hf hc.scrT.nowrap, hY', ?_, ?_, ?_,
      hb5, hb12, hr, hw, hw', hR⟩
  · rw [hh _ (by decide)]; exact hp
  · rw [hh _ (by decide)]; exact hv
  · rw [hh _ (by decide)]; exact hbit

/-- Before the selection: `S.ok`'s hypotheses, and the table and `Y < X`. -/
def WS5 (p : XPub) (t : State) : Prop :=
  SelP 32 p t ∧ ∃ (minv : BitVec 64) (X Xc : Nat), CExpCtx t (off p.B p.o) p.wx minv X Xc 32 ∧
    CTab t.mem (off p.B p.o) p.wx X False 0 32

/-- After the selection: `T < X`. -/
def WT5 (p : XPub) (t : State) : Prop :=
  ∃ (minv : BitVec 64) (X Xc : Nat), CExpCtx t (off p.B p.o) p.wx minv X Xc 32 ∧
    wv t.mem (off p.B p.o) (slot p.wx Crt.aT) p.wx < X ∧ 2 ≤ p.wx ∧ p.wx < 2 ^ 30

/-- `takeWin` gives the selection's hypotheses. -/
theorem takeWin_sel {p : XPub} {s : State} {bd : Nat → Nat → Nat} (h : WQ5 p s bd) :
    WP isa (.block Crt.takeWin) s (WS5 p) := by
  obtain ⟨minv, X, Xc, b, r, hc, htab, hY, hp, hv, hbit, hb5, hb12, hr, hw, hw', hR⟩ := h
  have hn := hc.scrT.nowrap
  have hnT : slot p.wx 8 + tabBytes p.wx 32 ≤ 2 ^ 64 := by omega_arith
  refine WP.mono (takeWin_ok hc hp hv hbit hb5 hb12 hr) fun t ⟨hm, k⟩ => ?_
  have f : Frm (off p.B p.o) (crtExpRanges5 p.wx) s.mem t.mem := by
    rw [hm]
    exact (((frm5_hdrW _ _ p.wx _ (by simp [crtExpRanges5]) (by decide)).trans
      (frm5_hdrW _ _ p.wx _ (by simp [crtExpRanges5, crtExpRanges, crtWinRanges]) (by decide))).trans
      (frm5_hdrW _ _ p.wx _ (by simp [crtExpRanges5, crtExpRanges, crtWinRanges]) (by decide))).trans
      (frm5_hdrW _ _ p.wx _ (by simp [crtExpRanges5, crtExpRanges, crtWinRanges]) (by decide))
  have hc' := hc.of_frm5 f k.2.2 (k.gpr (by decide))
  have hv32 : r / 2 ^ (b - 5) < 32 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), show (32 : Nat) = 2 ^ 5 from rfl, ← Nat.pow_add,
      show 5 + (b - 5) = b by omega]
    exact hr
  refine ⟨⟨minv, X, Xc, _, hc', hw, hw', hv32, ?_, ?_⟩, minv, X, Xc, hc', ?_⟩
  · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]
    exact htab.tab
  · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  · rw [hm]
    exact (((htab.hdrW _ (by decide) (by decide) hnT).hdrW _ (by decide) (by decide) hnT).hdrW _ (by decide)
      (by decide) hnT).hdrW _ (by decide) (by decide) hnT

/-- A window leaks the same in runs with the same workspace and the same
exponent's pointer and length, whatever the exponent. -/
theorem crtWin5_ct (M : Mont) (Sq : MontS) (S : CrtSel 32) (hS : S.CT) :
    RelCT isa (Two fun (q : BPub × Nat) s => q.2 < K5 q.1 ∧ Win5I q.1 q.2 s) (seqs (Crt.expWin5 Sq.mm M.mm S.code))
      fun _ _ => True := by
  rw [expWin5_eq]
  refine RelCT.seqs_append (by simp) (by simp) (RelCT.seq (two_post (Ψ := fun q s => WQ5 q.1.x s Sq.bd) fill_ct
    fun q s ⟨hj, t₀, minv, X, Xc, eb, ⟨i, b, hib, hb, hiL, hI⟩, hw, hw', hR, hL, _, he, hout⟩ => ?_) ?_)
  · have hK := K5_mul q.1
    rw [← hL] at hK
    refine WP.mono (fill_ok rfl he.rd he.val hout hb hiL (fun h5 => by
      rcases Nat.lt_or_ge i eb.length with h | h
      · exact h
      · omega) hI) fun t ⟨i', b', hb5, hb12, _, _, hI'⟩ => ?_
    have hXR : X ≤ 2 ^ (64 * q.1.x.wx) := by rw [← hI'.ctx.n]; exact Nat.le_of_lt (wv_lt _ _ _ _)
    exact ⟨minv, X, Xc, b', _, hI'.ctx, hI'.tab, Nat.lt_of_lt_of_le hI'.ylt (Sq.le hXR), hI'.pow, hI'.v, hI'.bit,
      hb5, hb12, Nat.mod_lt _ (Nat.two_pow_pos b'), hw, hw', hR⟩
  have sq : RelCT isa (Two fun (q : BPub × Nat) s => WQ5 q.1.x s Sq.bd) Sq.mm
      (Two fun (q : BPub × Nat) s => WQ5 q.1.x s Sq.bd) :=
    two_post (two_map (fun q : BPub × Nat => q.1.x.ws) (fun _ _ h => h.goodW) Sq.ct)
      fun _ _ h => winSq5_q Sq h
  refine RelCT.seqs_append (by simp) (by simp) (RelCT.seq (R := Two fun (q : BPub × Nat) s => WS5 q.1.x s) ?_ ?_)
  · simp only [seqs]
    exact RelCT.seq sq (RelCT.seq sq (RelCT.seq sq (RelCT.seq sq (RelCT.seq sq
      (two_piece [.rdi] (pins_rdi (fun q : BPub × Nat => off q.1.x.B q.1.x.o)
        fun _ _ ⟨_, _, _, _, _, hc, _⟩ => hc.good.rdi) (by taint_decide) fun _ _ h => takeWin_sel h)))))
  -- The selection, `Y := Y T` and the end.
  refine RelCT.seqs_append S.ne (by simp) ?_
  refine RelCT.seq (two_post (Ψ := fun (q : BPub × Nat) s => WT5 q.1.x s)
    (two_map (fun q : BPub × Nat => q.1.x) (fun _ _ h => h.1) hS) fun q s h => ?_) ?_
  · obtain ⟨⟨minv, X, Xc, v, hc, hw, hw', hv, ht, hN⟩, minv', X', Xc', hc₂, htab⟩ := h
    refine WP.mono (S.ok hc hw hw' hv ht hN) fun t ⟨hc', hT, _, _⟩ => ⟨minv, X, Xc, hc', ?_, hw, hw'⟩
    have hX : X' = X := hc₂.n.symm.trans hc.n
    rw [hT, ← hX]; exact htab.lt _ hv
  simp only [seqs]
  refine RelCT.seq (two_post (Ψ := fun (q : BPub × Nat) t => t.gpr .rdi = off q.1.x.B q.1.x.o)
    (two_map (fun q : BPub × Nat => q.1.x.ws) (fun _ _ ⟨minv, _, _, hc, _⟩ => ⟨minv, hc.good, Nat.le_refl _⟩)
      (M.ct (o := Public.aY) (a := Public.aY) (b := Crt.aT) (by unfold MmUse; decide)))
    fun q s ⟨minv, X, Xc, hc, hT, hw, hw'⟩ => ?_) ?_
  · exact WP.mono (M.mm_ok (o := Public.aY) (a := Public.aY) (b := Crt.aT) hc.good (Nat.le_refl _) hw (by omega_arith)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
      (by rw [hc.n]; exact hT)) fun t ⟨hg, _⟩ => hg.rdi
  exact rdi_ct (fun q : BPub × Nat => off q.1.x.B q.1.x.o) (fun _ _ h => h) (by taint_decide)

/-! ## The exponentiation -/

theorem pins_ePre5 (sp sl : Nat) : Pins (EPre5 sp sl) [.rdi] :=
  fun a s₁ s₂ h₁ h₂ => pins_ePre sp sl a s₁ s₂ h₁.1 h₂.1

/-- `expLoop5`'s start keeps `tabBuild_ok`'s hypotheses for 32 entries. -/
theorem crtExpInit_tpre5 {sp sl : Nat} {a : BPub} {s : State} (h : EPre5 sp sl a s) :
    WP isa (.block [.mov .rax (.mem (hdr Crt.sLink)), .mov .rdx (.mem (Crt.ws .rax sp)),
      .store (hdr Crt.sExp) .rdx, .mov .rdx (.mem (Crt.ws .rax sl)), .store (hdr Crt.sExpLen) .rdx,
      .mov32 .rdx (.imm 0), .store (hdr Crt.sI) .rdx]) s (TPre 32 a.x) := by
  obtain ⟨⟨minv, X, x, y, eb, hc, hw2, hwx, hw30, hn, hinv, hodd, hxl, -, hyl, -, hsp, hsl, hep, hel, -⟩, hT⟩ := h
  have hs32 := hc.scr32 hT
  have hPn := hs32.nowrap
  have hY0 := slot_le (w := a.x.wx) (show Public.aY < 8 by decide)
  have hY1 := hdr_lt_slot a.x.wx Public.aY (show 31 < 32 by decide)
  have hc₀ : CExpCtx s (off a.x.B a.x.o) a.x.wx minv X
      (wv s.mem (off a.x.B a.x.o) (slot a.x.wx Crt.aXc) a.x.wx) 32 :=
    ⟨hc.good, hs32, hn, hinv, rfl⟩
  refine WP.mono (crtExpInit_ok hc hsp hsl hep hel) fun t₁ ⟨hm₁, k₁⟩ => ?_
  have o1 := writeW_outside s.mem (off a.x.B a.x.o) (d := 8 * Crt.sExp) a.ptr (by decide)
  have o2 := writeW_outside (s.mem.writeW (off (off a.x.B a.x.o) (8 * Crt.sExp)) a.ptr) (off a.x.B a.x.o)
    (d := 8 * Crt.sExpLen) (BitVec.ofNat 64 eb.length) (by decide)
  have o3 := writeW_outside ((s.mem.writeW (off (off a.x.B a.x.o) (8 * Crt.sExp)) a.ptr).writeW
    (off (off a.x.B a.x.o) (8 * Crt.sExpLen)) (BitVec.ofNat 64 eb.length)) (off a.x.B a.x.o) (d := 8 * Crt.sI)
    (BitVec.setWidth 64 (0 : BitVec 32)) (by decide)
  rw [← hm₁] at o3
  have f₁ : Frm (off a.x.B a.x.o) (crtExpRanges a.x.wx 32) s.mem t₁.mem :=
    ((Frm.of_outside o1 (by simp [crtExpRanges])).trans (Frm.of_outside o2 (by simp [crtExpRanges]))).trans
      (Frm.of_outside o3 (by simp [crtExpRanges]))
  refine ⟨minv, X, _, hc₀.of_frm f₁ k₁.2.2 (k₁.gpr (by decide)), hxl, ?_, hw2, by omega_arith,
    VG.Proof.Bignum.coprime_pow2 hodd _⟩
  rw [o3.wv (by unfold Crt.sI sFn at *; omega_arith) (by omega_arith), o2.wv (by unfold Crt.sExpLen sFn at *; omega_arith)
    (by omega_arith), o1.wv (by unfold Crt.sExp sFn at *; omega_arith) (by omega_arith)]
  exact hyl

/-- `expLoop5`'s start, table and padding leak the same in runs with the
same workspace, given that the taint analysis checks its start after the
link's load. -/
theorem crtExpHead5_ct (M : Mont) {sp sl : Nat} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi, .rax]) (.block [.mov .rdx (.mem (Crt.ws .rax sp)),
      .store (hdr Crt.sExp) .rdx, .mov .rdx (.mem (Crt.ws .rax sl)), .store (hdr Crt.sExpLen) .rdx,
      .mov32 .rdx (.imm 0), .store (hdr Crt.sI) .rdx]) hc).isSome = true) :
    RelCT isa (Two (EPre5 sp sl)) (seqs ((expInit sp sl :: Crt.tabBuildN M.mm 30) ++ ([.block Crt.padInit] : List (Prog isa))))
      fun _ _ => True := by
  refine RelCT.seqs_append (by simp) (by simp) (RelCT.seq (two_post
    (Ψ := fun (a : BPub) t => t.gpr .rdi = off a.x.B a.x.o) ?_ fun a s h => ?_)
    (rdi_ct (fun a : BPub => off a.x.B a.x.o) (fun _ _ h => h) (by taint_decide)))
  · -- The start and the table.
    rw [← List.singleton_append]
    refine RelCT.seqs_append (by simp) (by simp [tabBuild_eq, tabPre]) (RelCT.seq (two_post
      (Ψ := fun a s => TPre 32 a.x s) ?_ fun _ _ h => by simp only [seqs, expInit]; exact crtExpInit_tpre5 h)
      (two_map (fun a : BPub => a.x) (fun _ _ h => h) (tabBuild_ct M 32 (by decide) (by decide) (by taint_decide))))
    simp only [seqs, expInit]
    rw [crtExpInit_eq]
    exact RelCT.block_append (RelCT.seq (two_piece (Ψ := fun (a : BPub) t => t.gpr .rdi = off a.x.B a.x.o ∧
        t.gpr .rax = a.x.B) [.rdi] (pins_ePre5 sp sl) (by taint_decide) fun _ _ h => crtLink_ok h.1)
      (two_taint [.rdi, .rax] (pins_of (fun a r => if r = .rdi then off a.x.B a.x.o else a.x.B)
        fun a s h r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact h.1
          · exact h.2) hT))
  · rw [← List.singleton_append]
    refine wp_seqs_append (by simp) (by simp [tabBuild_eq, tabPre]) ?_
    simp only [seqs, expInit]
    refine WP.mono (crtExpInit_tpre5 h) fun t ⟨minv, X, Xc, hc, hXN, hY, hw, hw', hR⟩ => ?_
    exact WP.mono (tabBuild_ok M (Q := False) (x := 0) hc (by decide) (by decide) hw (by omega_arith) hR hXN
      False.elim hY False.elim) fun t' h' => h'.1.good.rdi

/-- `expLoop5 M.mm S.code sp sl` is constant time, given that the taint
analysis checks its start after the link's load. -/
theorem crtExpLoop5S_ct (M : Mont) (Sq : MontS) (S : CrtSel 32) (hS : S.CT) {sp sl : Nat}
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi, .rax]) (.block [.mov .rdx (.mem (Crt.ws .rax sp)),
      .store (hdr Crt.sExp) .rdx, .mov .rdx (.mem (Crt.ws .rax sl)), .store (hdr Crt.sExpLen) .rdx,
      .mov32 .rdx (.imm 0), .store (hdr Crt.sI) .rdx]) hc).isSome = true) :
    ExpCT5S M Sq S sp sl := by
  unfold ExpCT5S
  rw [expLoop5_eq]
  refine RelCT.seqs_append (by simp) (by simp) (RelCT.seq (two_post
    (Ψ := fun a s => 0 < K5 a ∧ Win5I a 0 s) (crtExpHead5_ct M hT) fun a s h => ?_) ?_)
  · obtain ⟨⟨minv, X, x, y, eb, hc, hw2, hwx, hw30, hn, hinv, hodd, hxl, -, hyl, -, hsp, hsl, hep, hel, hL, hL1,
      hL2, he⟩, hT⟩ := h
    have hBn := hc.scr.nowrap
    have hPn := (hc.scr32 hT).nowrap
    have hi := hc.hi
    have hlo := hc.lo
    have hT' := hT
    simp only [wsTab] at hT'
    have h256 : 256 ≤ slot a.x.wx 8 := by unfold slot hdrBytes; omega_arith
    have hout : ∀ i < eb.length, slot a.x.wx 8 + tabBytes a.x.wx 32 ≤
        ofs (off a.x.B a.x.o) (a.ptr + BitVec.ofNat 64 i) := fun i hi' => by
      have := he.out i hi'
      rcases ofs_rebase a.x.B (a.ptr + BitVec.ofNat 64 i) (o := a.x.o) (by omega_arith) with ⟨_, h2⟩ | ⟨h1, _⟩
      · omega_arith
      · omega_arith
    have hK := K5_mul a
    exact WP.mono (crtExpHead5_ok M (Q := False) (x := 0) hc hT hw2 hwx hw30 hn hinv hodd hxl False.elim hyl
      False.elim hsp hsl hep hel hL2) fun t h0 => ⟨by omega, s, minv, X, _, eb, h0, hw2, by omega_arith,
        VG.Proof.Bignum.coprime_pow2 hodd _, hL, by omega_arith, he, hout⟩
  simp only [seqs]
  refine (two_loop (Φ := Win5I) (Ψ := fun _ _ => True) K5 (crtWin5_ct M Sq S hS) ?_).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  rintro a j s hj ⟨t₀, minv, X, Xc, eb, ⟨i, b, hib, hb, hiL, hI⟩, hw, hw', hR, hL, hL', he, hout⟩
  have hK := K5_mul a
  exact WP.mono (crtWin5_ok M Sq S hw hw' hR rfl hL' he.rd he.val hout (K := K5 a) (by rw [hK, hL]) hj hib hb hiL hI)
    fun s' ⟨hz, i', b', hib', hb', hiL', hI'⟩ => ⟨eval_ne_count hj hz,
      fun _ => ⟨t₀, minv, X, Xc, eb, ⟨i', b', hib', hb', hiL', hI'⟩, hw, hw', hR, hL, hL', he, hout⟩, fun _ => trivial⟩

/-- `crtExpLoop5S_ct` with the squarings by `M`: `expLoop5 M.mm`. -/
theorem crtExpLoop5_ct (M : Mont) (S : CrtSel 32) (hS : S.CT) {sp sl : Nat}
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi, .rax]) (.block [.mov .rdx (.mem (Crt.ws .rax sp)),
      .store (hdr Crt.sExp) .rdx, .mov .rdx (.mem (Crt.ws .rax sl)), .store (hdr Crt.sExpLen) .rdx,
      .mov32 .rdx (.imm 0), .store (hdr Crt.sI) .rdx]) hc).isSome = true) :
    ExpCT5 M S sp sl :=
  crtExpLoop5S_ct M M.toS S hS hT

theorem expLoop5_ct_P (M : Mont) (S : CrtSel 32) (hS : S.CT) : ExpCT5 M S sDp sPlen :=
  crtExpLoop5_ct M S hS (by taint_decide)

theorem expLoop5_ct_Q (M : Mont) (S : CrtSel 32) (hS : S.CT) : ExpCT5 M S sDq sQlen :=
  crtExpLoop5_ct M S hS (by taint_decide)

theorem expLoop5S_ct_P (M : Mont) (Sq : MontS) (S : CrtSel 32) (hS : S.CT) : ExpCT5S M Sq S sDp sPlen :=
  crtExpLoop5S_ct M Sq S hS (by taint_decide)

theorem expLoop5S_ct_Q (M : Mont) (Sq : MontS) (S : CrtSel 32) (hS : S.CT) : ExpCT5S M Sq S sDq sQlen :=
  crtExpLoop5S_ct M Sq S hS (by taint_decide)

end VG.Proof.Bignum.X86_64
