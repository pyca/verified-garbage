import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Bignum.X86_64.CTExp

/-!
# RSA with the CRT on x86-64: the exponentiation is constant time

`expLoop` reads the exponent's bytes, a secret, but at public addresses (its
pointer plus the byte index), and selects with a mask computed from each
bit: the bit flows only into data. Its loops count public numbers, the
exponent's length and 8 (`crtByte_ct`, `crtBits_ct`), and a bit is two
Montgomery multiplications (constant time for any prime, `Mont.ct`), the
mask and a masked selection (`crtExpBit_ct`). The steps' correctness
(`CrtExp.lean`) gives the header facts each next piece needs.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-! ## A bit -/

/-- What every step needs of the prime's workspace (`w_X` words) and of
`Xc ≡ x R`. -/
def CFacts (wx X Xc x : Nat) : Prop :=
  2 ≤ wx ∧ wx < 2 ^ 30 ∧ Nat.Coprime (2 ^ (64 * wx)) X ∧ Xc < X ∧ Xc % X = x * 2 ^ (64 * wx) % X

/-- After `j` bits of a byte, in the prime's workspace of `p`. -/
def CBitsInv (p : XPub) (j : Nat) (s : State) : Prop :=
  ∃ (t₀ : State) (minv : BitVec 64) (X Xc y F x E v : Nat),
    CBitInv t₀ (off p.B p.o) p.wx minv X Xc y F x E v j s ∧ CFacts p.wx X Xc x ∧ v < 256

/-- Before each product of a bit: the workspace and the byte in `sV`. -/
def CBitQ (p : XPub) (t : State) : Prop :=
  ∃ (minv : BitVec 64) (X Xc V : Nat), CExpCtx t (off p.B p.o) p.wx minv X Xc ∧ Xc < X ∧ 2 ≤ p.wx ∧
    p.wx < 2 ^ 30 ∧ word t.mem (off p.B p.o) (8 * Crt.sV) = BitVec.ofNat 64 V ∧ V < 2 ^ 62

/-- Before the selection: its bases, `w_X` and the mask. -/
def CBitSel (p : XPub) (t : State) : Prop :=
  ∃ lt : Bool, Scr t (off p.B p.o) (slot p.wx 8) ∧ t.gpr .rdi = off p.B p.o ∧ t.gpr .rbp = mask lt ∧
    t.gpr .r12 = BitVec.ofNat 64 p.wx ∧ t.gpr .r8 = off (off p.B p.o) (slot p.wx Crt.aT) ∧
    t.gpr .rsi = off (off p.B p.o) (slot p.wx Public.aY) ∧
    t.gpr .rbx = off (off p.B p.o) (slot p.wx Public.aY) ∧ 2 ≤ p.wx ∧ p.wx < 2 ^ 30

theorem CBitQ.goodW {p : XPub} {t : State} (h : CBitQ p t) : GoodW p.ws t :=
  let ⟨minv, _, _, _, hc, _⟩ := h; ⟨minv, hc.good, Nat.le_refl _⟩

theorem pins_cBitQ : Pins CBitQ [.rdi] := fun _ _ _ ⟨_, _, _, _, h₁, _⟩ ⟨_, _, _, _, h₂, _⟩ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.good.rdi, h₂.good.rdi]

theorem pins_cBitSel : Pins CBitSel [.r8, .rsi, .rbx, .r12] := by
  intro p s₁ s₂ ⟨_, _, _, _, a₁, b₁, c₁, d₁, _⟩ ⟨_, _, _, _, a₂, b₂, c₂, d₂, _⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [b₁, b₂]
  · rw [c₁, c₂]
  · rw [d₁, d₂]
  · rw [a₁, a₂]

/-- The squaring keeps the workspace and the byte. -/
theorem crtBitSq_q (M : Mont) {p : XPub} {j : Nat} {s : State} (hj : j < 8) (h : CBitsInv p j s) :
    WP isa (M.mm Public.aY Public.aY Public.aY) s (CBitQ p) := by
  obtain ⟨t₀, minv, X, Xc, y, F, x, E, v, hI, ⟨hw, hw', -, hXN, -⟩, hv⟩ := h
  obtain ⟨Y, hY, hYN, -⟩ := hI.y
  have hc := hI.ctx
  refine WP.mono (M.mm_ok (o := Public.aY) (a := Public.aY) (b := Public.aY) hc.good (Nat.le_refl _) hw
    (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
    (by rw [hY, hc.n]; exact hYN)) fun t₁ ⟨_, _, _, ha₁, k₁⟩ => ?_
  have f₁ : Frm (off p.B p.o) (crtBitRanges p.wx) s.mem t₁.mem := Frm.of_arrays ha₁ (by simp [crtBitRanges])
  have hp : 2 ^ j ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
  exact ⟨minv, X, Xc, v * 2 ^ j, hc.of_bit f₁ k₁.2.2 (k₁.gpr (by decide)), hXN, hw, hw',
    by rw [ha₁.hslot (by decide)]; exact hI.v, by have := Nat.mul_le_mul_left v hp; omega⟩

/-- `T := Y Xc` keeps the workspace and the byte. -/
theorem crtBitMul_q (M : Mont) {p : XPub} {s : State} (h : CBitQ p s) :
    WP isa (M.mm Crt.aT Public.aY Crt.aXc) s (CBitQ p) := by
  obtain ⟨minv, X, Xc, V, hc, hXN, hw, hw', hV, hV'⟩ := h
  refine WP.mono (M.mm_ok (o := Crt.aT) (a := Public.aY) (b := Crt.aXc) hc.good (Nat.le_refl _) hw
    (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
    (by rw [hc.x, hc.n]; exact hXN)) fun t₂ ⟨_, _, _, ha₂, k₂⟩ => ?_
  have f₂ : Frm (off p.B p.o) (crtBitRanges p.wx) s.mem t₂.mem := Frm.of_arrays ha₂ (by simp [crtBitRanges])
  exact ⟨minv, X, Xc, V, hc.of_bit f₂ k₂.2.2 (k₂.gpr (by decide)), hXN, hw, hw',
    by rw [ha₂.hslot (by decide)]; exact hV, hV'⟩

/-- A bit leaks the same in runs with the same workspace, whatever the bit. -/
theorem crtExpBit_ct (M : Mont) :
    RelCT isa (Two fun (q : XPub × Nat) s => q.2 < 8 ∧ CBitsInv q.1 q.2 s) (seqs (Crt.expBit M.mm))
      fun _ _ => True := by
  simp only [Crt.expBit, seqs]
  -- `Y := Y²`.
  refine RelCT.seq (two_post (Ψ := fun (q : XPub × Nat) t => CBitQ q.1 t)
    (two_map (fun q : XPub × Nat => q.1.ws) (fun _ _ h => ?_) (M.ct (by unfold MmUse; decide)))
    fun _ _ h => crtBitSq_q M h.1 h.2) ?_
  · obtain ⟨-, t₀, minv, X, Xc, y, F, x, E, v, hI, -⟩ := h
    exact ⟨minv, hI.ctx.good, Nat.le_refl _⟩
  -- `T := Y Xc`.
  refine RelCT.seq (two_post (Ψ := fun (q : XPub × Nat) t => CBitQ q.1 t)
    (two_map (fun q : XPub × Nat => q.1.ws) (fun _ _ h => h.goodW) (M.ct (by unfold MmUse; decide)))
    fun _ _ h => crtBitMul_q M h) ?_
  -- The mask, `sV` doubled, the bases.
  refine RelCT.seq (two_piece (Ψ := fun (q : XPub × Nat) t => CBitSel q.1 t) [.rdi]
    (fun q => pins_cBitQ q.1) (by taint_decide) fun q s h => ?_) ?_
  · obtain ⟨minv, X, Xc, V, hc, -, hw, hw', hV, hV'⟩ := h
    exact WP.mono (crtBitMid_ok hc hV hV') fun t ⟨hbp, h12, h8, hsi, hbx, _, k⟩ =>
      ⟨_, hc.good.scr.congr k.2.2, (k.gpr (by decide)).trans hc.good.rdi, hbp, h12, h8, hsi, hbx, hw, hw'⟩
  -- `Y := bit ? T : Y`.
  refine RelCT.seq (two_post (Ψ := fun (q : XPub × Nat) t => t.gpr .rdi = off q.1.B q.1.o)
    (two_taint [.r8, .rsi, .rbx, .r12] (fun q => pins_cBitSel q.1) (by taint_decide)) fun q s h => ?_) ?_
  · obtain ⟨lt, hs, hdi, hbp, h12, h8, hsi, hbx, hw, hw'⟩ := h
    have hY0 := slot_le (w := q.1.wx) (show Public.aY < 8 by decide)
    have hT0 := slot_le (w := q.1.wx) (show Crt.aT < 8 by decide)
    have hYT := slot_sep (w := q.1.wx) (show Public.aY ≠ Crt.aT by decide)
    exact WP.mono (selectAcc_self_ok hs h8 hsi hbx h12 hbp (by omega) (by omega) (by omega) (by omega)
      (by omega)) fun t ⟨_, _, k⟩ => (k.gpr (by decide)).trans hdi
  -- The bit count.
  exact two_taint [.rdi] (fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁, h₂]) (by taint_decide)

/-! ## The bits of a byte -/

/-- The eight bits of a byte leak the same in runs with the same workspace. -/
theorem crtBits_ct (M : Mont) :
    RelCT isa (Two fun p s => 0 < 8 ∧ CBitsInv p 0 s) (.loop (seqs (Crt.expBit M.mm)) .ne)
      (Two fun p s => CBitsInv p 8 s) :=
  two_loop (Φ := CBitsInv) (fun _ => 8) (crtExpBit_ct M)
    fun _ _ _ hj ⟨t₀, minv, X, Xc, y, F, x, E, v, hI, hf, hv⟩ =>
      WP.mono (crtBitStep_ok M hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2 hv hj hI) fun _ ⟨hz, hI'⟩ =>
        ⟨eval_ne_count hj hz, fun _ => ⟨t₀, minv, X, Xc, y, F, x, E, v, hI', hf, hv⟩,
          fun h => h ▸ ⟨t₀, minv, X, Xc, y, F, x, E, v, hI', hf, hv⟩⟩

/-! ## The bytes of the exponent -/

/-- After `i` bytes of the exponent (at `a.ptr`, `a.len` bytes). -/
def CBytesInv (a : BPub) (i : Nat) (s : State) : Prop :=
  ∃ (t₀ : State) (minv : BitVec 64) (X Xc y x : Nat) (eb : List Byte),
    CByteInv t₀ (off a.x.B a.x.o) a.x.wx minv X Xc y x a.ptr eb.length eb i s ∧ CFacts a.x.wx X Xc x ∧
    eb.length = a.len ∧ eb.length < 2 ^ 31 ∧ Src t₀ a.x.B a.x.Z a.ptr eb ∧
    ∀ i < eb.length, slot a.x.wx 8 ≤ ofs (off a.x.B a.x.o) (a.ptr + BitVec.ofNat 64 i)

/-- After the loads of the byte's address. -/
def CHeadMid (q : BPub × Nat) (s : State) : Prop :=
  q.2 < q.1.len ∧ CBytesInv q.1 q.2 s ∧ s.gpr .rax = q.1.ptr ∧ s.gpr .rcx = BitVec.ofNat 64 q.2

theorem pins_cBytes : Pins (fun (q : BPub × Nat) s => q.2 < q.1.len ∧ CBytesInv q.1 q.2 s) [.rdi] :=
  fun _ _ _ ⟨_, _, _, _, _, _, _, _, h₁, _⟩ ⟨_, _, _, _, _, _, _, _, h₂, _⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ctx.good.rdi, h₂.ctx.good.rdi]

theorem pins_cHeadMid : Pins CHeadMid [.rdi, .rax, .rcx] := by
  rintro q s₁ s₂ ⟨-, ⟨_, _, _, _, _, _, _, i₁, _⟩, a₁, c₁⟩ ⟨-, ⟨_, _, _, _, _, _, _, i₂, _⟩, a₂, c₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [i₁.ctx.good.rdi, i₂.ctx.good.rdi]
  · rw [a₁, a₂]
  · rw [c₁, c₂]

/-- One byte of the exponent leaks the same in runs with the same workspace
and the same exponent's pointer and length. -/
theorem crtByte_ct (M : Mont) : RelCT isa (Two fun (q : BPub × Nat) s => q.2 < q.1.len ∧ CBytesInv q.1 q.2 s)
    (seqs [.block [.mov .rax (.mem (hdr Crt.sExp)), .mov .rcx (.mem (hdr Crt.sI)),
        .movzx8 .rax { base := .rax, index := some .rcx }, .store (hdr Crt.sV) .rax, .mov32 .rax (.imm 8),
        .store (hdr Crt.sBit) .rax],
      .loop (seqs (Crt.expBit M.mm)) .ne,
      .block [.mov .rax (.mem (hdr Crt.sI)), .alu .add .rax (.imm 1), .store (hdr Crt.sI) .rax,
        .alu .cmp .rax (.mem (hdr Crt.sExpLen))]]) fun _ _ => True := by
  simp only [seqs]
  rw [crtByteHead_eq]
  have w₁ : ∀ (q : BPub × Nat) s, q.2 < q.1.len ∧ CBytesInv q.1 q.2 s →
      WP isa (.block [.mov .rax (.mem (hdr Crt.sExp)), .mov .rcx (.mem (hdr Crt.sI))]) s (CHeadMid q) := by
    rintro q s ⟨hi, t₀, minv, X, Xc, y, x, eb, hI, hrest⟩
    exact WP.mono (crtByteHead1_ok hI) fun t ⟨h1, h2, h3⟩ =>
      ⟨hi, ⟨t₀, minv, X, Xc, y, x, eb, h3, hrest⟩, h1, h2⟩
  have w₂ : ∀ (q : BPub × Nat) s, CHeadMid q s →
      WP isa (.block [.movzx8 .rax { base := .rax, index := some .rcx }, .store (hdr Crt.sV) .rax,
        .mov32 .rax (.imm 8), .store (hdr Crt.sBit) .rax]) s fun t => 0 < 8 ∧ CBitsInv q.1.x 0 t := by
    rintro q s ⟨hi, ⟨t₀, minv, X, Xc, y, x, eb, hI, hf, hL, -, he, hout⟩, hax, hcx⟩
    have hi' : q.2 < eb.length := by omega
    exact WP.mono (crtByteHead2_ok rfl hi' he.rd he.val hout hI hax hcx) fun t ⟨_, _, hB⟩ =>
      ⟨by decide, t, minv, X, Xc, y, _, x, _, _, hB, hf, (eb[q.2]'hi').isLt⟩
  have h₃ : RelCT isa (Two fun (p : XPub) s => CBitsInv p 8 s)
      (.block [.mov .rax (.mem (hdr Crt.sI)), .alu .add .rax (.imm 1), .store (hdr Crt.sI) .rax,
        .alu .cmp .rax (.mem (hdr Crt.sExpLen))]) fun _ _ => True :=
    two_taint [.rdi] (fun _ _ _ ⟨_, _, _, _, _, _, _, _, _, h₁, _⟩ ⟨_, _, _, _, _, _, _, _, _, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ctx.good.rdi, h₂.ctx.good.rdi]) (by taint_decide)
  exact RelCT.seq (RelCT.block_append (RelCT.seq (two_piece _ pins_cBytes (by taint_decide) w₁)
      (two_piece _ pins_cHeadMid (by taint_decide) w₂)))
    (RelCT.seq (two_map (fun q : BPub × Nat => q.1.x) (fun _ _ h => h) (crtBits_ct M)) h₃)

/-! ## The exponentiation -/

/-- `expLoop`'s start: the load of the link, then the rest. -/
theorem crtExpInit_eq (sp sl : Nat) : ([.mov .rax (.mem (hdr Crt.sLink)), .mov .rdx (.mem (Crt.ws .rax sp)),
      .store (hdr Crt.sExp) .rdx, .mov .rdx (.mem (Crt.ws .rax sl)), .store (hdr Crt.sExpLen) .rdx,
      .mov32 .rdx (.imm 0), .store (hdr Crt.sI) .rdx] : List Instr) =
    ([.mov .rax (.mem (hdr Crt.sLink))] : List Instr) ++
    ([.mov .rdx (.mem (Crt.ws .rax sp)), .store (hdr Crt.sExp) .rdx, .mov .rdx (.mem (Crt.ws .rax sl)),
      .store (hdr Crt.sExpLen) .rdx, .mov32 .rdx (.imm 0), .store (hdr Crt.sI) .rdx] : List Instr) := rfl

theorem pins_ePre (sp sl : Nat) : Pins (EPre sp sl) [.rdi] :=
  fun _ _ _ ⟨_, _, _, _, _, h₁, _⟩ ⟨_, _, _, _, _, h₂, _⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.rdi, h₂.rdi]

/-- The link into `rax`: the modulus' workspace. -/
theorem crtLink_ok {sp sl : Nat} {a : BPub} {s : State} (h : EPre sp sl a s) :
    WP isa (.block [.mov .rax (.mem (hdr Crt.sLink))]) s fun t =>
      t.gpr .rdi = off a.x.B a.x.o ∧ t.gpr .rax = a.x.B := by
  obtain ⟨minv, X, x, y, eb, hc, -⟩ := h
  have hn := hc.scr.nowrap
  have hi := hc.hi
  have hlo := hc.lo
  have hl : InRegions (s.rd ++ s.wr) (off (off a.x.B a.x.o) (8 * Crt.sLink)) 8 :=
    hc.good.scr.ld (by have := hdr_lt_slot a.x.wx 8 (show Crt.sLink < 32 by decide); omega)
  exact WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = a.x.B)
    (by xrun [State.ea, hdr, hc.rdi, hdrOff, hl, hc.link]) rfl)
    fun t ⟨h, k⟩ => ⟨(k.gpr (by decide)).trans hc.rdi, h⟩

/-- `expLoop`'s start sets up the bytes' invariant. -/
theorem crtExpInit_inv {sp sl : Nat} {a : BPub} {s : State} (h : EPre sp sl a s) :
    WP isa (.block [.mov .rax (.mem (hdr Crt.sLink)), .mov .rdx (.mem (Crt.ws .rax sp)),
      .store (hdr Crt.sExp) .rdx, .mov .rdx (.mem (Crt.ws .rax sl)), .store (hdr Crt.sExpLen) .rdx,
      .mov32 .rdx (.imm 0), .store (hdr Crt.sI) .rdx]) s fun t => 0 < a.len ∧ CBytesInv a 0 t := by
  obtain ⟨minv, X, x, y, eb, hc, hw2, hwx, hw30, hn, hinv, hodd, hxl, hxc, hyl, hyc, hsp, hsl, hep, hel, hL,
    hL1, hL2, he⟩ := h
  have hPn := hc.good.scr.nowrap
  have hBn := hc.scr.nowrap
  have hi := hc.hi
  have hlo := hc.lo
  have h256 : 256 ≤ slot a.x.wx 8 := by unfold slot hdrBytes; omega
  have hR : Nat.Coprime (2 ^ (64 * a.x.wx)) X := VG.Proof.Bignum.coprime_pow2 hodd _
  have hout : ∀ i < eb.length, slot a.x.wx 8 ≤ ofs (off a.x.B a.x.o) (a.ptr + BitVec.ofNat 64 i) :=
    fun i hi' => by
      have := he.out i hi'
      rcases ofs_rebase a.x.B (a.ptr + BitVec.ofNat 64 i) (o := a.x.o) (by omega) with ⟨_, h2⟩ | ⟨h1, _⟩
      · omega
      · omega
  have hc₀ : CExpCtx s (off a.x.B a.x.o) a.x.wx minv X (wv s.mem (off a.x.B a.x.o) (slot a.x.wx Crt.aXc) a.x.wx) :=
    ⟨hc.good, hn, hinv, rfl⟩
  refine WP.mono (crtExpInit_ok hc hsp hsl hep hel) fun t₁ ⟨hm₁, k₁⟩ => ⟨by omega, s, minv, X, _, y, x, eb, ?_,
    ⟨hw2, by omega, hR, hxl, hxc⟩, hL, by omega, he, hout⟩
  have o1 := writeW_outside s.mem (off a.x.B a.x.o) (d := 8 * Crt.sExp) a.ptr (by decide)
  have o2 := writeW_outside (s.mem.writeW (off (off a.x.B a.x.o) (8 * Crt.sExp)) a.ptr) (off a.x.B a.x.o)
    (d := 8 * Crt.sExpLen) (BitVec.ofNat 64 eb.length) (by decide)
  have o3 := writeW_outside ((s.mem.writeW (off (off a.x.B a.x.o) (8 * Crt.sExp)) a.ptr).writeW
    (off (off a.x.B a.x.o) (8 * Crt.sExpLen)) (BitVec.ofNat 64 eb.length)) (off a.x.B a.x.o) (d := 8 * Crt.sI)
    (BitVec.setWidth 64 (0 : BitVec 32)) (by decide)
  rw [← hm₁] at o3
  have f₁ : Frm (off a.x.B a.x.o) (crtExpRanges a.x.wx) s.mem t₁.mem :=
    ((Frm.of_outside o1 (by simp [crtExpRanges])).trans (Frm.of_outside o2 (by simp [crtExpRanges]))).trans
      (Frm.of_outside o3 (by simp [crtExpRanges]))
  have hY0 := slot_le (w := a.x.wx) (show Public.aY < 8 by decide)
  have hY1 := hdr_lt_slot a.x.wx Public.aY (show 31 < 32 by decide)
  refine ⟨hc₀.of_frm f₁ k₁.2.2 (k₁.gpr (by decide)), ⟨_, ?_, hyl, ?_⟩, ?_, ?_, ?_, f₁, k₁.mono (by decide)⟩
  · rw [o3.wv (by unfold Crt.sI sFn at *; omega) (by omega), o2.wv (by unfold Crt.sExpLen sFn at *; omega)
      (by omega), o1.wv (by unfold Crt.sExp sFn at *; omega) (by omega)]
  · rw [hyc, pre_zero, Nat.pow_zero, Nat.pow_zero, Nat.pow_one, Nat.mul_one]
  · rw [hm₁, word_writeW_self]; rfl
  · rw [hm₁, hdrStore_hdr (i := Crt.sI) _ _ _ (by decide) (by decide) (by decide),
      hdrStore_hdr (i := Crt.sExpLen) _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  · rw [hm₁, hdrStore_hdr (i := Crt.sI) _ _ _ (by decide) (by decide) (by decide), word_writeW_self]

/-- `expLoop M.mm sp sl` is constant time, given that the taint analysis
checks its start after the link's load. -/
theorem crtExpLoop_ct (M : Mont) {sp sl : Nat} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi, .rax]) (.block [.mov .rdx (.mem (Crt.ws .rax sp)),
      .store (hdr Crt.sExp) .rdx, .mov .rdx (.mem (Crt.ws .rax sl)), .store (hdr Crt.sExpLen) .rdx,
      .mov32 .rdx (.imm 0), .store (hdr Crt.sI) .rdx]) hc).isSome = true) :
    ExpCT M sp sl := by
  unfold ExpCT
  simp only [Crt.expLoop, seqs]
  refine RelCT.seq (two_post (Ψ := fun a s => 0 < a.len ∧ CBytesInv a 0 s) ?_ fun _ _ h => crtExpInit_inv h) ?_
  · rw [crtExpInit_eq]
    exact RelCT.block_append (RelCT.seq (two_piece (Ψ := fun (a : BPub) t => t.gpr .rdi = off a.x.B a.x.o ∧
        t.gpr .rax = a.x.B) [.rdi] (pins_ePre sp sl) (by taint_decide) fun _ _ h => crtLink_ok h)
      (two_taint [.rdi, .rax] (pins_of (fun a r => if r = .rdi then off a.x.B a.x.o else a.x.B)
        fun a s h r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact h.1
          · exact h.2) hT))
  refine (two_loop (Φ := CBytesInv) (Ψ := fun _ _ => True) (fun a => a.len) (crtByte_ct M) ?_).mono (fun _ _ h => h) fun _ _ _ => trivial
  rintro a i s hi ⟨t₀, minv, X, Xc, y, x, eb, hI, hf, hL, hL', he, hout⟩
  exact WP.mono (crtByte_ok M hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2 rfl hL' (by omega) he.rd he.val hout hI)
    fun s' ⟨hz, hI'⟩ => ⟨eval_ne_count hi (by rw [hz, hL]), fun _ => ⟨t₀, minv, X, Xc, y, x, eb, hI', hf, hL, hL',
      he, hout⟩, fun _ => trivial⟩

theorem expLoop_ct_P (M : Mont) : ExpCT M sDp sPlen := crtExpLoop_ct M (by taint_decide)

theorem expLoop_ct_Q (M : Mont) : ExpCT M sDq sQlen := crtExpLoop_ct M (by taint_decide)

end VG.Proof.Bignum.X86_64
