import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow

/-!
# RSA with the CRT on x86-64: `redc` is constant time

`redc j` reduces `n`'s array `j` in chunks of `w_X` words: the number of
chunks `K = ⌈w / w_X⌉`, the words left (`sRem`) and whether the last chunk is
short depend only on `w`, `w_X` and the iteration, which both runs share
(`RInv`), and its multiplications are constant time for any modulus (`M.ct`).
Its loads from the header are pinned by correctness (`redcLoad_ok`,
`redcAcc_ok` and their steps), and `addMod`'s reload of its output's base by
`addStep_ok`'s invariant (`addMod_ct`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

theorem RelCT.assoc' {P Q : State → State → Prop} {a b c : Prog isa}
    (h : RelCT isa P (.seq a (.seq b c)) Q) : RelCT isa P (.seq (.seq a b) c) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq e₁ c₁ =>
    cases e₁ with
    | seq a₁ b₁ =>
      cases e₂ with
      | seq e₂ c₂ =>
        cases e₂ with
        | seq a₂ b₂ =>
          obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq a₁ (.seq b₁ c₁)) (.seq a₂ (.seq b₂ c₂))
          simp only [List.append_assoc] at ht ⊢
          exact ⟨ht, hq⟩

theorem SubCtx.of_keep {s t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {rs : List Reg}
    (h : SubCtx s B Z o w wx minv) (hm : t.mem = s.mem) (k : Keep rs s t) (hr : Reg.rdi ∉ rs) :
    SubCtx t B Z o w wx minv :=
  h.of_frm (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k.2.2 (k.gpr hr)

theorem lt_of_cf {t : State} {a b : Nat} (hcf : t.cf = some (decide (a < b))) (h : isa.eval .b t = some true) :
    a < b := by
  simp only [eval, hcf, Option.some.injEq, decide_eq_true_eq] at h; exact h

theorem ge_of_cf {t : State} {a b : Nat} (hcf : t.cf = some (decide (a < b))) (h : isa.eval .b t = some false) :
    b ≤ a := by
  simp only [eval, hcf, Option.some.injEq, decide_eq_false_iff_not] at h; omega

/-! ## `addMod aXc aXc aT` -/

/-- `addMod`'s loads. -/
def amB1 : List Instr :=
  [.mov .rbx (.mem (hdr (sArr aXc))), .mov .r9 (.mem (hdr (sArr aT))), .mov .r10 (.mem (hdr (sArr Public.aN))),
    .mov .r8 (.mem (hdr (sArr Public.aAcc))), .mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr Public.aTmp))),
    .mov32 .rbp (.imm 0)]

/-- `addMod`'s sum. -/
def amLoop : Prog isa :=
  wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .adc .rax (.mem (ix .r9 .r14)),
    .store (ix .r8 .r14) .rax, cfToRbp]

/-- `addMod`'s carry and the reload of its output's base. -/
def amB3 : List Instr :=
  [.mov32 .rax (.imm 0), cfFromRbp, .alu .adc .rax (.imm 0), .store (ix .r8 .r12) .rax,
    .mov .rbx (.mem (hdr (sArr aXc)))]

theorem addMod_eq :
    addMod aXc aXc aT = .seq (.block amB1) (.seq amLoop (.seq (.block amB3) (.seq subMod selectAcc))) := rfl

/-- The workspace of `addMod`, for some `-m⁻¹`. -/
def AmPre (L : Ws) (s : State) : Prop := GoodW L s ∧ 1 ≤ L.w ∧ L.w < 2 ^ 31

/-- After `addMod`'s loads. -/
def AmHd (L : Ws) (t : State) : Prop :=
  t.gpr .rdi = L.B ∧ t.gpr .rbx = off L.B (slot L.w aXc) ∧ t.gpr .r9 = off L.B (slot L.w aT) ∧
    t.gpr .r10 = off L.B (slot L.w Public.aN) ∧ t.gpr .r8 = off L.B (slot L.w Public.aAcc) ∧
    t.gpr .r12 = BitVec.ofNat 64 L.w ∧ t.gpr .rsi = off L.B (slot L.w Public.aTmp) ∧ t.gpr .rbp = mask false ∧
    GoodW L t ∧ 1 ≤ L.w ∧ L.w < 2 ^ 31

/-- Before `addMod`'s subtraction and selection. -/
def AmMid (L : Ws) (t : State) : Prop :=
  t.gpr .rbx = off L.B (slot L.w aXc) ∧ t.gpr .r10 = off L.B (slot L.w Public.aN) ∧
    t.gpr .r8 = off L.B (slot L.w Public.aAcc) ∧ t.gpr .r12 = BitVec.ofNat 64 L.w ∧
    t.gpr .rsi = off L.B (slot L.w Public.aTmp)

theorem amHd_ok {L : Ws} {s : State} (h : AmPre L s) : WP isa (.block amB1) s (AmHd L) := by
  obtain ⟨⟨minv, hg, hZ⟩, hw, hw'⟩ := h
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off L.B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot L.w 8 hi; omega)
  refine WP.mono (WP.keep [.rbx, .r9, .r10, .r8, .r12, .rsi, .rbp] (Q := fun t =>
      t.gpr .rbx = off L.B (slot L.w aXc) ∧ t.gpr .r9 = off L.B (slot L.w aT) ∧
      t.gpr .r10 = off L.B (slot L.w Public.aN) ∧ t.gpr .r8 = off L.B (slot L.w Public.aAcc) ∧
      t.gpr .r12 = BitVec.ofNat 64 L.w ∧ t.gpr .rsi = off L.B (slot L.w Public.aTmp) ∧ t.gpr .rbp = mask false ∧
      t.mem = s.mem)
    (by unfold amB1; xrun [State.ea, hdr, hg.rdi, hdrOff, hl (sArr aXc) (by decide), hl (sArr aT) (by decide),
      hl (sArr Public.aN) (by decide), hl (sArr Public.aAcc) (by decide), hl sW (by decide),
      hl (sArr Public.aTmp) (by decide), hg.hdr.harr aXc (by decide), hg.hdr.harr aT (by decide),
      hg.hdr.harr Public.aN (by decide), hg.hdr.harr Public.aAcc (by decide), hg.hdr.harr Public.aTmp (by decide),
      hg.hdr.hw]) rfl)
    fun t ⟨⟨h1, h2, h3, h4, h5, h6, h7, hm⟩, k⟩ => ⟨(k.gpr (by decide)).trans hg.rdi, h1, h2, h3, h4, h5, h6, h7,
      ⟨minv, ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi, hm ▸ hg.hdr⟩, hZ⟩, hw, hw'⟩

theorem amTail_ok {L : Ws} {s₁ : State} (h : AmHd L s₁) : WP isa (.seq amLoop (.block amB3)) s₁ (AmMid L) := by
  obtain ⟨hdi, hbx, h9, h10, h8, h12, hsi, hbp, ⟨minv, hg, hZ⟩, hw, hw'⟩ := h
  have hs₁ := hg.scr
  have hn := hs₁.nowrap
  have sl : ∀ j < 8, slot L.w j + 8 * (L.w + 2) ≤ L.Z := fun j hj => (slot_le hj).trans hZ
  have sA := sl Public.aAcc (by decide)
  have sX := sl aXc (by decide)
  have sT := sl aT (by decide)
  have p1 := slot_sep (w := L.w) (show aXc ≠ Public.aAcc by decide)
  have p2 := slot_sep (w := L.w) (show aT ≠ Public.aAcc by decide)
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₁.mem → Keep [.r14] s₁ t → t.cf = s₁.cf →
      AddInv s₁ L.B L.Z (slot L.w Public.aAcc) (slot L.w aXc) (slot L.w aT) 0 t := fun t h14 hm k _ =>
    ⟨hs₁.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      ⟨false, (k.gpr (by decide)).trans hbp, by rw [hm]; rfl⟩⟩
  refine WP.seq (WP.mono (wordLoop_ok (start := 0) (N := L.w) (by omega) hw'
    (AddInv s₁ L.B L.Z (slot L.w Public.aAcc) (slot L.w aXc) (slot L.w aT)) h0
    (fun j _ hj t hI => addStep_ok h8 hbx h9 h12 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) hj hI)) fun s₂ hI => ?_)
  obtain ⟨c, hc, -⟩ := hI.val
  have s₂8 : s₂.gpr .r8 = off L.B (slot L.w Public.aAcc) := (hI.keep.gpr (by decide)).trans h8
  have s₂12 : s₂.gpr .r12 = BitVec.ofNat 64 L.w := (hI.keep.gpr (by decide)).trans h12
  have s₂di : s₂.gpr .rdi = L.B := (hI.keep.gpr (by decide)).trans hdi
  have hl₂ : ∀ i < 32, InRegions (s₂.rd ++ s₂.wr) (off L.B (8 * i)) 8 := fun i hi =>
    hI.scr.ld (by have := hdr_lt_slot L.w 8 hi; omega)
  have q1 := hdr_lt_slot L.w Public.aAcc (show sArr aXc < 32 by decide)
  have q2 := hdr_lt_slot L.w 8 (show sArr aXc < 32 by decide)
  have ho₂ : word s₂.mem L.B (8 * sArr aXc) = off L.B (slot L.w aXc) := by
    rw [hI.out.word (by omega) (by omega)]
    exact hg.hdr.harr aXc (by decide)
  have hX : ∀ v : BitVec 64,
      (s₂.mem.writeW (off L.B (slot L.w Public.aAcc + 8 * L.w)) v).readW (off L.B (8 * sArr aXc)) 64 =
        off L.B (slot L.w aXc) := fun v =>
    ((writeW_outside s₂.mem L.B v (by omega)).word (Or.inl (by omega)) (by omega)).trans ho₂
  refine WP.mono (WP.keep [.rax, .rbp, .rbx] (Q := fun t => t.gpr .rbx = off L.B (slot L.w aXc))
    (by
      unfold amB3 cfFromRbp
      xrun [State.ea, ix, hdr, s₂di, hdrOff, addr0 s₂8 s₂12, hc, cf_mask,
        hI.scr.st (show slot L.w Public.aAcc + 8 * L.w + 8 ≤ L.Z by omega), sx0, hl₂ (sArr aXc) (by decide),
        hX]) rfl) fun t ⟨hbx', k⟩ => ⟨hbx', ?_, ?_, ?_, ?_⟩
  · exact (k.gpr (by decide)).trans ((hI.keep.gpr (by decide)).trans h10)
  · exact (k.gpr (by decide)).trans s₂8
  · exact (k.gpr (by decide)).trans s₂12
  · exact (k.gpr (by decide)).trans ((hI.keep.gpr (by decide)).trans hsi)

theorem pins_amHd : Pins AmHd [.rdi, .rbx, .r9, .r10, .r8, .r12, .rsi] := by
  intro L s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  obtain ⟨a₁, b₁, c₁, d₁, e₁, f₁, g₁, -⟩ := h₁
  obtain ⟨a₂, b₂, c₂, d₂, e₂, f₂, g₂, -⟩ := h₂
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a₁, a₂]
  · rw [b₁, b₂]
  · rw [c₁, c₂]
  · rw [d₁, d₂]
  · rw [e₁, e₂]
  · rw [f₁, f₂]
  · rw [g₁, g₂]

theorem pins_amMid : Pins AmMid [.rbx, .r10, .r8, .r12, .rsi] := by
  intro L s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  obtain ⟨a₁, b₁, c₁, d₁, e₁⟩ := h₁
  obtain ⟨a₂, b₂, c₂, d₂, e₂⟩ := h₂
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [a₁, a₂]
  · rw [b₁, b₂]
  · rw [c₁, c₂]
  · rw [d₁, d₂]
  · rw [e₁, e₂]

/-- `addMod aXc aXc aT` is constant time for any modulus. -/
theorem addMod_ct : RelCT isa (Two AmPre) (addMod aXc aXc aT) fun _ _ => True := by
  rw [addMod_eq]
  exact RelCT.assoc (RelCT.assoc (RelCT.seq (two_post (Ψ := AmMid)
    (RelCT.assoc' (RelCT.seq (two_piece (Ψ := AmHd) [.rdi]
      (pins_rdiB (fun L => L.B) fun _ _ ⟨⟨_, hg, _⟩, _⟩ => hg.rdi) (by taint_decide) fun _ _ h => amHd_ok h)
      (two_taint _ pins_amHd (by taint_decide))))
    fun _ _ h => WP.seq (WP.seq (WP.mono (amHd_ok h) fun _ h₁ => WP.seq_iff.mp (amTail_ok h₁))))
    (two_taint _ pins_amMid (by taint_decide))))

/-! ## The loop's body -/

/-- The prime's workspace. -/
abbrev XPub.ws (p : XPub) : Ws := ⟨off p.B p.o, slot p.wx 8, p.wx⟩

/-- The sizes. -/
def XF (p : XPub) : Prop := 2 ≤ p.wx ∧ p.wx ≤ p.w ∧ p.w < 2 ^ 30

/-- After `k` chunks. -/
def RLoop (j : Nat) (p : XPub) (k : Nat) (t : State) : Prop :=
  ∃ (s : State) (minv : BitVec 64) (X : Nat), RInv s p.B p.Z p.o p.w p.wx j minv X k t ∧ XF p ∧ 1 < X ∧ j < 8

/-- Before chunk `k`. -/
def RBody (j : Nat) (q : XPub × Nat) (t : State) : Prop :=
  q.2 < (q.1.w + q.1.wx - 1) / q.1.wx ∧ RLoop j q.1 q.2 t

/-- After the chunk's array is cleared. -/
def RB1 (j : Nat) (q : XPub × Nat) (t : State) : Prop :=
  ∃ minv, SubCtx t q.1.B q.1.Z q.1.o q.1.w q.1.wx minv ∧
    word t.mem (off q.1.B q.1.o) (8 * sRem) = BitVec.ofNat 64 (q.1.w - q.2 * q.1.wx) ∧
    word t.mem (off q.1.B q.1.o) (8 * sSrc) = off q.1.B (slot q.1.w j + 8 * (q.2 * q.1.wx)) ∧ XF q.1

/-- After the comparison of the words left with `w_X`. -/
def RB2 (j : Nat) (q : XPub × Nat) (t : State) : Prop :=
  ∃ minv, SubCtx t q.1.B q.1.Z q.1.o q.1.w q.1.wx minv ∧
    word t.mem (off q.1.B q.1.o) (8 * sSrc) = off q.1.B (slot q.1.w j + 8 * (q.2 * q.1.wx)) ∧
    t.gpr .r12 = BitVec.ofNat 64 (q.1.w - q.2 * q.1.wx) ∧
    t.cf = some (decide (q.1.w - q.2 * q.1.wx < q.1.wx))

/-- The chunk's length. -/
def RB3 (j : Nat) (q : XPub × Nat) (t : State) : Prop :=
  ∃ minv, SubCtx t q.1.B q.1.Z q.1.o q.1.w q.1.wx minv ∧
    word t.mem (off q.1.B q.1.o) (8 * sSrc) = off q.1.B (slot q.1.w j + 8 * (q.2 * q.1.wx)) ∧
    t.gpr .r12 = BitVec.ofNat 64 (min (q.1.w - q.2 * q.1.wx) q.1.wx)

/-- Before the chunk's copy. -/
def RB4 (j : Nat) (q : XPub × Nat) (t : State) : Prop :=
  t.gpr .rsi = off q.1.B (slot q.1.w j + 8 * (q.2 * q.1.wx)) ∧
    t.gpr .rbx = off (off q.1.B q.1.o) (slot q.1.wx aChunk) ∧
    t.gpr .r12 = BitVec.ofNat 64 (min (q.1.w - q.2 * q.1.wx) q.1.wx)

/-- After the chunk's copy (`redcLoad_ok`). -/
def RB5 (j : Nat) (q : XPub × Nat) (t : State) : Prop :=
  ∃ (minv : BitVec 64) (X : Nat), SubCtx t q.1.B q.1.Z q.1.o q.1.w q.1.wx minv ∧
    XVals t q.1.B q.1.o q.1.wx minv X ∧ 1 < X ∧
    t.gpr .r12 = BitVec.ofNat 64 (min (q.1.w - q.2 * q.1.wx) q.1.wx) ∧
    word t.mem (off q.1.B q.1.o) (8 * sRem) = BitVec.ofNat 64 (q.1.w - q.2 * q.1.wx) ∧
    word t.mem (off q.1.B q.1.o) (8 * sSrc) = off q.1.B (slot q.1.w j + 8 * (q.2 * q.1.wx)) ∧ XF q.1

/-- The prime, before a multiplication. -/
def RA0 (p : XPub) (t : State) : Prop :=
  ∃ (minv : BitVec 64) (X : Nat), SubCtx t p.B p.Z p.o p.w p.wx minv ∧ XVals t p.B p.o p.wx minv X ∧ 1 < X ∧ XF p

/-- After `A' := A R⁻¹`. -/
def RA1 (p : XPub) (t : State) : Prop :=
  ∃ (minv : BitVec 64) (X : Nat), SubCtx t p.B p.Z p.o p.w p.wx minv ∧ XVals t p.B p.o p.wx minv X ∧ 1 < X ∧
    wv t.mem (off p.B p.o) (slot p.wx aXc) p.wx < X ∧ XF p

/-- After `T := c R⁻¹`. -/
def RA2 (p : XPub) (t : State) : Prop :=
  ∃ (minv : BitVec 64) (X : Nat), SubCtx t p.B p.Z p.o p.w p.wx minv ∧ XVals t p.B p.o p.wx minv X ∧
    wv t.mem (off p.B p.o) (slot p.wx aXc) p.wx < X ∧ wv t.mem (off p.B p.o) (slot p.wx aT) p.wx < X ∧ XF p

theorem rb1_ok {j : Nat} {q : XPub × Nat} {t : State} (h : RBody j q t) :
    WP isa (zeroArr aChunk) t (RB1 j q) := by
  obtain ⟨hk, s, minv, X, hI, hf, -, -⟩ := h
  obtain ⟨hw2, hwx, hw30⟩ := id hf
  have hkw : q.2 * q.1.wx < q.1.w := (lt_chunks (by omega)).mp hk
  have hlw : lowW q.1.w q.1.wx q.2 = q.2 * q.1.wx := Nat.min_eq_right (by omega)
  have hc := hI.ctx
  have hn := hc.scr.nowrap
  have hi := hc.hi
  have hC := slot_le (w := q.1.wx) (show aChunk < 8 by decide)
  have hC0 := hdr_lt_slot q.1.wx aChunk (show 31 < 32 by decide)
  refine WP.mono (zeroArr_ok hc.good (Nat.le_refl _) (by omega) (by omega) (show aChunk < 8 by decide))
    fun t₁ ⟨_, ho₁, k₁⟩ => ⟨minv, hc.of_frm (Frm.of_outside ho₁ (by simp [redcRanges])) (redcRanges_ok _) k₁.2.2
      (k₁.gpr (by decide)), ?_, ?_, hf⟩
  · rw [ho₁.word (by unfold sRem sFn; omega) (by unfold sRem sFn; omega), hI.rem, hlw]
  · rw [ho₁.word (by unfold sSrc sFn; omega) (by unfold sSrc sFn; omega), hI.src, hlw]

theorem rb2_ok {j : Nat} {q : XPub × Nat} {t : State} (h : RB1 j q t) :
    WP isa (.block [.mov .r12 (.mem (hdr sRem)), .alu .cmp .r12 (.mem (hdr sW))]) t (RB2 j q) := by
  obtain ⟨minv, hc, hrem, hsrc, hw2, hwx, hw30⟩ := h
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off (off q.1.B q.1.o) (8 * i)) 8 := fun i hi' =>
    hc.good.scr.ld (by have := hdr_lt_slot q.1.wx 8 hi'; omega)
  exact WP.mono (WP.keep [.r12] (Q := fun t₂ => t₂.gpr .r12 = BitVec.ofNat 64 (q.1.w - q.2 * q.1.wx) ∧
      t₂.cf = some (decide (q.1.w - q.2 * q.1.wx < q.1.wx)) ∧ t₂.mem = t.mem)
    (by xrun [State.ea, hdr, hc.rdi, hdrOff, hl sRem (by decide), hrem, hl sW (by decide), hc.hdr.hw,
      ofNat_lt_ofNat (show q.1.w - q.2 * q.1.wx < 2 ^ 64 by omega) (show q.1.wx < 2 ^ 64 by omega)]) rfl)
    fun t₂ ⟨⟨h12, hcf, hm⟩, k⟩ => ⟨minv, hc.of_keep hm k (by decide), by rw [hm]; exact hsrc, h12, hcf⟩

theorem rb3_ok {j : Nat} {q : XPub × Nat} {t : State} (h : RB2 j q t ∧ isa.eval .b t = some false) :
    WP isa (.block [.mov .r12 (.mem (hdr sW))]) t (RB3 j q) := by
  obtain ⟨⟨minv, hc, hsrc, -, hcf⟩, hb⟩ := h
  have hge := ge_of_cf hcf hb
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off (off q.1.B q.1.o) (8 * i)) 8 := fun i hi' =>
    hc.good.scr.ld (by have := hdr_lt_slot q.1.wx 8 hi'; omega)
  exact WP.mono (WP.keep [.r12] (Q := fun t' => t'.gpr .r12 = BitVec.ofNat 64 (min (q.1.w - q.2 * q.1.wx) q.1.wx) ∧
      t'.mem = t.mem)
    (by xrun [State.ea, hdr, hc.rdi, hdrOff, hl sW (by decide), hc.hdr.hw, Nat.min_eq_right hge]) rfl)
    fun t' ⟨⟨h12, hm⟩, k⟩ => ⟨minv, hc.of_keep hm k (by decide), by rw [hm]; exact hsrc, h12⟩

theorem rb4_ok {j : Nat} {q : XPub × Nat} {t : State} (h : RB3 j q t) :
    WP isa (.block [.mov .rsi (.mem (hdr sSrc)), .mov .rbx (.mem (hdr (sArr aChunk)))]) t (RB4 j q) := by
  obtain ⟨minv, hc, hsrc, h12⟩ := h
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off (off q.1.B q.1.o) (8 * i)) 8 := fun i hi' =>
    hc.good.scr.ld (by have := hdr_lt_slot q.1.wx 8 hi'; omega)
  exact WP.mono (WP.keep [.rsi, .rbx] (Q := fun t' => t'.gpr .rsi = off q.1.B (slot q.1.w j + 8 * (q.2 * q.1.wx)) ∧
      t'.gpr .rbx = off (off q.1.B q.1.o) (slot q.1.wx aChunk))
    (by xrun [State.ea, hdr, hc.rdi, hdrOff, hl sSrc (by decide), hsrc, hl (sArr aChunk) (by decide),
      hc.hdr.harr aChunk (by decide)]) rfl)
    fun t' ⟨⟨h1, h2⟩, k⟩ => ⟨h1, h2, (k.gpr (by decide)).trans h12⟩

theorem pins_subCtx {α : Type} {Φ : α → State → Prop} (f : α → XPub)
    (h : ∀ a s, Φ a s → ∃ minv, SubCtx s (f a).B (f a).Z (f a).o (f a).w (f a).wx minv) : Pins Φ [.rdi] :=
  pins_rdiB (fun a => off (f a).B (f a).o) fun a s hs => let ⟨_, hc⟩ := h a s hs; hc.rdi

/-- A chunk into its array. -/
theorem redcLoad_ct (j : Nat) : RelCT isa (Two (RBody j)) (seqs redcLoad) fun _ _ => True := by
  simp only [redcLoad, seqs]
  refine RelCT.seq (two_post (Ψ := RB1 j) (two_map (fun q => q.1.ws)
    (fun q t ⟨_, _, minv, _, hI, _⟩ => ⟨minv, hI.ctx.good, Nat.le_refl _⟩) (zeroArr_ct (by decide) (by taint_decide)))
    fun _ _ h => rb1_ok h) ?_
  refine RelCT.seq (two_piece (Ψ := RB2 j) [.rdi] (pins_subCtx (·.1) fun _ _ ⟨minv, hc, _⟩ => ⟨minv, hc⟩)
    (by taint_decide) fun _ _ h => rb2_ok h) ?_
  refine RelCT.seq (R := Two (RB3 j)) (two_ite (fun q s₁ s₂ ⟨_, _, _, _, h₁⟩ ⟨_, _, _, _, h₂⟩ => by
    simp only [eval, h₁, h₂]) ?_ ?_) ?_
  · exact RelCT.block_nil fun _ _ hp => two_mono (fun q t ⟨⟨minv, hc, hs, h12, hcf⟩, hb⟩ =>
      ⟨minv, hc, hs, by rw [h12, Nat.min_eq_left (Nat.le_of_lt (lt_of_cf hcf hb))]⟩) hp
  · exact two_piece [.rdi] (pins_subCtx (·.1) fun _ _ ⟨⟨minv, hc, _⟩, _⟩ => ⟨minv, hc⟩) (by taint_decide)
      fun _ _ h => rb3_ok h
  refine RelCT.seq (two_piece (Ψ := RB4 j) [.rdi] (pins_subCtx (·.1) fun _ _ ⟨minv, hc, _⟩ => ⟨minv, hc⟩)
    (by taint_decide) fun _ _ h => rb4_ok h) ?_
  refine two_taint [.rsi, .rbx, .r12] (pins_of (fun q r => if r = .rsi then off q.1.B (slot q.1.w j + 8 * (q.2 *
      q.1.wx))
    else if r = .rbx then off (off q.1.B q.1.o) (slot q.1.wx aChunk)
    else BitVec.ofNat 64 (min (q.1.w - q.2 * q.1.wx) q.1.wx)) fun q s h r hr => ?_) (by taint_decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2

theorem ra0_ok {j : Nat} {q : XPub × Nat} {t : State} (h : RB5 j q t) :
    WP isa (.block [.mov .rax (.mem (hdr sRem)), .alu .sub .rax (.reg .r12), .store (hdr sRem) .rax,
      .alu .add .r12 (.reg .r12), .alu .add .r12 (.reg .r12), .alu .add .r12 (.reg .r12),
      .alu .add .r12 (.mem (hdr sSrc)), .store (hdr sSrc) .r12]) t (RA0 q.1) := by
  obtain ⟨minv, X, hc, hv, hX1, h12, hrem, hsrc, hf⟩ := h
  obtain ⟨hw2, hwx, hw30⟩ := id hf
  have hcr : min (q.1.w - q.2 * q.1.wx) q.1.wx ≤ q.1.w - q.2 * q.1.wx := Nat.min_le_left _ _
  have hr : q.1.w - q.2 * q.1.wx < 2 ^ 31 := by omega
  generalize q.1.w - q.2 * q.1.wx = r at hrem h12 hcr hr
  generalize min r q.1.wx = c at h12 hcr
  generalize slot q.1.w j + 8 * (q.2 * q.1.wx) = e at hsrc
  have hn := hc.good.scr.nowrap
  have rok := redcRanges_ok q.1.wx
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off (off q.1.B q.1.o) (8 * i)) 8 := fun i hi' =>
    hc.good.scr.ld (by have := hdr_lt_slot q.1.wx 8 hi'; omega)
  have hst : ∀ i < 32, InRegions t.wr (off (off q.1.B q.1.o) (8 * i)) 8 := fun i hi' =>
    hc.good.scr.st (by have := hdr_lt_slot q.1.wx 8 hi'; omega)
  have hX : ∀ v : BitVec 64, (t.mem.writeW (off (off q.1.B q.1.o) (8 * sRem)) v).readW
      (off (off q.1.B q.1.o) (8 * sSrc)) 64 = off q.1.B e := fun v =>
    (hdrStore_hdr t.mem (off q.1.B q.1.o) v (by decide) (by decide) (by decide)).trans hsrc
  refine WP.mono (WP.keep [.rax, .r12] (Q := fun t₁ => t₁.mem = (t.mem.writeW (off (off q.1.B q.1.o) (8 * sRem))
      (BitVec.ofNat 64 (r - c))).writeW (off (off q.1.B q.1.o) (8 * sSrc)) (off q.1.B (e + 8 * c)))
    (by xrun [State.ea, hdr, hc.rdi, hdrOff, hl sRem (by decide), hrem, h12, VG.Offset.ofNat_sub_ofNat hcr,
      hst sRem (by decide), ofNat_dbl, hX, hl sSrc (by decide), hst sSrc (by decide), ofNat_add_off,
      show e + 2 * (2 * (2 * c)) = e + 8 * c by omega]) rfl)
    fun t₁ ⟨hm₁, k₁⟩ => ?_
  have o1 := writeW_outside t.mem (off q.1.B q.1.o) (d := 8 * sRem) (BitVec.ofNat 64 (r - c)) (by decide)
  have o2 := writeW_outside (t.mem.writeW (off (off q.1.B q.1.o) (8 * sRem)) (BitVec.ofNat 64 (r - c)))
    (off q.1.B q.1.o) (d := 8 * sSrc) (off q.1.B (e + 8 * c)) (by decide)
  rw [← hm₁] at o2
  have f₁ : Frm (off q.1.B q.1.o) (redcRanges q.1.wx) t.mem t₁.mem :=
    (Frm.of_outside o1 (by simp [redcRanges])).trans (Frm.of_outside o2 (by simp [redcRanges]))
  exact ⟨minv, X, hc.of_frm f₁ rok k₁.2.2 (k₁.gpr (by decide)), hv.of_frm (by omega) (by omega) f₁, hX1, hf⟩

theorem ra1_ok (M : Mont) {p : XPub} {t : State} (h : RA0 p t) :
    WP isa (M.mm aXc aXc Public.aOne) t (RA1 p) := by
  obtain ⟨minv, X, hc, hv, hX1, hf⟩ := h
  obtain ⟨hw2, hwx, hw30⟩ := id hf
  exact WP.mono (mmOne_ok M hc hv hw2 (by omega) hX1 (d := aXc) (a := aXc) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by simp [redcRanges]))
    fun t' ⟨hc', hv', hlt, _⟩ => ⟨minv, X, hc', hv', hX1, hlt, hf⟩

theorem ra2_ok (M : Mont) {p : XPub} {t : State} (h : RA1 p t) :
    WP isa (M.mm aT aChunk Public.aOne) t (RA2 p) := by
  obtain ⟨minv, X, hc, hv, hX1, hlt, hf⟩ := h
  obtain ⟨hw2, hwx, hw30⟩ := id hf
  have hn : (off p.B p.o).toNat + slot p.wx 8 ≤ 2 ^ 64 := hc.good.scr.nowrap
  exact WP.mono (mmOne_ok M hc hv hw2 (by omega) hX1 (d := aT) (a := aChunk) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by simp [redcRanges]))
    fun t' ⟨hc', hv', hlt', _, ha, _⟩ =>
      ⟨minv, X, hc', hv', by rw [ha.wv_of_not_mem (by decide) (by decide) hn]; exact hlt, hlt', hf⟩

theorem ra3_ok {p : XPub} {t : State} (h : RA2 p t) :
    WP isa (addMod aXc aXc aT) t fun t' => t'.gpr .rdi = off p.B p.o := by
  obtain ⟨minv, X, hc, hv, hlt, hlt', hw2, hwx, hw30⟩ := h
  exact WP.mono (addMod_ok hc.good.scr hc.rdi hc.hdr (Nat.le_refl _) hw2 (by omega) (o := aXc) (a := aXc) (b := aT)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hv.n]; exact hlt) (by rw [hv.n]; exact hlt')) fun t' ⟨_, _, k⟩ => (k.gpr (by decide)).trans hc.rdi

/-- The words left and the source advanced, and `A := A R⁻¹ + c R⁻¹`. -/
theorem redcAcc_ct (M : Mont) (j : Nat) : RelCT isa (Two (RB5 j)) (seqs (redcAcc M.mm)) fun _ _ => True := by
  simp only [redcAcc, seqs]
  refine RelCT.seq (two_piece (Ψ := fun q t => RA0 q.1 t) [.rdi]
    (pins_subCtx (·.1) fun _ _ ⟨minv, _, hc, _⟩ => ⟨minv, hc⟩) (by taint_decide) fun _ _ h => ra0_ok h)
    (two_map (fun q => q.1) (fun _ _ h => h) ?_)
  refine RelCT.seq (two_post (Ψ := RA1) (two_map XPub.ws (fun _ _ ⟨minv, _, hc, _⟩ => ⟨minv, hc.good, Nat.le_refl _⟩)
    (M.ct (by unfold MmUse; decide))) fun _ _ h => ra1_ok M h) ?_
  refine RelCT.seq (two_post (Ψ := RA2) (two_map XPub.ws (fun _ _ ⟨minv, _, hc, _⟩ => ⟨minv, hc.good, Nat.le_refl _⟩)
    (M.ct (by unfold MmUse; decide))) fun _ _ h => ra2_ok M h) ?_
  refine RelCT.seq (two_post (Ψ := fun p t => t.gpr .rdi = off p.B p.o) (two_map XPub.ws
    (fun p _ ⟨minv, _, hc, _, _, _, hw2, _, hw30⟩ => ⟨⟨minv, hc.good, Nat.le_refl _⟩, show 1 ≤ p.wx by omega,
      show p.wx < 2 ^ 31 by omega⟩) addMod_ct) fun _ _ h => ra3_ok h) ?_
  exact two_taint [.rdi] (pins_rdiB (fun p => off p.B p.o) fun _ _ h => h) (by taint_decide)

/-- One chunk. -/
theorem redcBody_ct (M : Mont) (j : Nat) :
    RelCT isa (Two (RBody j)) (seqs (redcLoad ++ redcAcc M.mm)) fun _ _ => True := by
  refine RelCT.seqs_split (by simp [redcLoad]) (by simp [redcAcc])
    (RelCT.seq (two_post (Ψ := RB5 j) (redcLoad_ct j) fun q t h => ?_) (redcAcc_ct M j))
  obtain ⟨hk, s, minv, X, hI, hf, hX1, hj⟩ := h
  obtain ⟨hw2, hwx, hw30⟩ := id hf
  have hkw : q.2 * q.1.wx < q.1.w := (lt_chunks (by omega)).mp hk
  have hlw : lowW q.1.w q.1.wx q.2 = q.2 * q.1.wx := Nat.min_eq_right (by omega)
  have hsl := slot_le (w := q.1.w) hj
  have hrem0 := hI.rem
  have hsrc0 := hI.src
  rw [hlw] at hrem0 hsrc0
  exact WP.mono (redcLoad_ok hI.ctx hw2 hwx hw30 hj (r := q.1.w - q.2 * q.1.wx) (e := slot q.1.w j + 8 * (q.2 *
      q.1.wx))
    (by omega) (by omega) (by omega) hrem0 hsrc0) fun t₁ ⟨hc₁, h12₁, _, hrem₁, hsrc₁, _, f₁, _⟩ =>
      ⟨minv, X, hc₁, hI.xv.of_frm (by have := hc₁.good.scr.nowrap; omega) (by omega) f₁, hX1, h12₁, hrem₁, hsrc₁, hf⟩

/-! ## `redc` -/

/-- After `A := 0`. -/
def RZ (p : XPub) (t : State) : Prop := ∃ minv, SubCtx t p.B p.Z p.o p.w p.wx minv ∧ XF p

/-- After the load of `n`'s base. -/
def RL (p : XPub) (t : State) : Prop := t.gpr .rdi = off p.B p.o ∧ t.gpr .rax = p.B

theorem rz_ok {j : Nat} {p : XPub} {s : State} (h : RPre j p s) : WP isa (zeroArr aXc) s (RZ p) := by
  obtain ⟨minv, X, hc, _, hw2, hwx, hw30, _⟩ := h
  have hn := hc.scr.nowrap
  have hi := hc.hi
  exact WP.mono (zeroArr_ok hc.good (Nat.le_refl _) (by omega) (by omega) (show aXc < 8 by decide))
    fun s₁ ⟨_, ho₁, k₁⟩ => ⟨minv, hc.of_frm (Frm.of_outside ho₁ (by simp [redcRanges])) (redcRanges_ok _) k₁.2.2
      (k₁.gpr (by decide)), hw2, hwx, hw30⟩

theorem rl_ok {p : XPub} {t : State} (h : RZ p t) : WP isa (.block [.mov .rax (.mem (hdr sLink))]) t (RL p) := by
  obtain ⟨_, hc, _⟩ := h
  have hl : InRegions (t.rd ++ t.wr) (off (off p.B p.o) (8 * sLink)) 8 :=
    hc.good.scr.ld (by have := hdr_lt_slot p.wx 8 (show sLink < 32 by decide); omega)
  exact WP.mono (WP.keep [.rax] (Q := fun t' => t'.gpr .rax = p.B)
    (by xrun [State.ea, hdr, hc.rdi, hdrOff, hl, hc.link]) rfl) fun t' ⟨h1, k⟩ => ⟨(k.gpr (by decide)).trans
        hc.rdi, h1⟩

/-- `redc`'s start, given that the taint analysis checks its loads through
`n`'s base (`by taint_decide` for a given `j`). -/
theorem redcHead_ct {j : Nat} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi, .rax]) (.block [.mov .rdx (.mem (ws .rax (sArr j))),
      .store (hdr sSrc) .rdx, .mov .rdx (.mem (ws .rax sW)), .store (hdr sRem) .rdx]) hc).isSome = true) :
    RelCT isa (Two (RPre j)) (.seq (zeroArr aXc) (.block [.mov .rax (.mem (hdr sLink)),
      .mov .rdx (.mem (ws .rax (sArr j))), .store (hdr sSrc) .rdx, .mov .rdx (.mem (ws .rax sW)),
      .store (hdr sRem) .rdx])) fun _ _ => True :=
  RelCT.seq (two_post (Ψ := RZ) (two_map XPub.ws (fun _ _ ⟨minv, _, hc, _⟩ => ⟨minv, hc.good, Nat.le_refl _⟩)
      (zeroArr_ct (by decide) (by taint_decide))) fun _ _ h => rz_ok h)
    (RelCT.block_append (l₁ := ([.mov .rax (.mem (hdr sLink))] : List Instr))
      (RelCT.seq (two_piece (Ψ := RL) [.rdi] (pins_subCtx id fun _ _ ⟨minv, hc, _⟩ => ⟨minv, hc⟩) (by taint_decide)
        fun _ _ h => rl_ok h)
      (two_taint [.rdi, .rax] (pins_of (fun p r => if r = .rdi then off p.B p.o else p.B) fun p s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1
        · exact h.2) hT)))

/-- `redc j`, given that the taint analysis checks its loads through `n`'s
base. -/
theorem redc_ct_of (M : Mont) {j : Nat} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi, .rax]) (.block [.mov .rdx (.mem (ws .rax (sArr j))),
      .store (hdr sSrc) .rdx, .mov .rdx (.mem (ws .rax sW)), .store (hdr sRem) .rdx]) hc).isSome = true) :
    RedcCT M j := by
  unfold RedcCT
  rw [redc_eq]
  refine RelCT.assoc (RelCT.seq (two_post (Ψ := fun p t => 0 < (p.w + p.wx - 1) / p.wx ∧ RLoop j p 0 t)
    (redcHead_ct hT) fun p s h => ?_) ((two_loop (Φ := RLoop j) (Ψ := fun _ _ => True) (fun p => (p.w + p.wx - 1) /
        p.wx)
      (redcBody_ct M j) ?_).mono (fun _ _ h => h) fun _ _ _ => trivial))
  · obtain ⟨minv, X, hc, hv, hw2, hwx, hw30, hX1, hj⟩ := h
    have hn := hc.good.scr.nowrap
    have hK : 0 < (p.w + p.wx - 1) / p.wx := (lt_chunks (k := 0) (by omega)).mpr (by omega)
    have hl0 : lowW p.w p.wx 0 = 0 := by simp [lowW]
    exact WP.mono (redcHead_ok hc hw2 hwx hw30 hj) fun t₁ ⟨hc₁, hz₁, hsrc₁, hrem₁, f₁, k₁⟩ =>
      ⟨hK, s, minv, X, ⟨hc₁, hv.of_frm hn (by omega) f₁, by rw [hl0, Nat.sub_zero]; exact hrem₁,
        by rw [hl0, Nat.mul_zero, Nat.add_zero]; exact hsrc₁, by rw [hz₁]; omega, by rw [hz₁, hl0]; rfl, f₁, k₁⟩,
        ⟨hw2, hwx, hw30⟩, hX1, hj⟩
  · rintro p k t hk ⟨s, minv, X, hI, hf, hX1, hj⟩
    obtain ⟨hw2, hwx, hw30⟩ := id hf
    exact WP.mono (redcStep_ok M hw2 hwx hw30 hX1 hj hk hI) fun t' ⟨hz, hI'⟩ =>
      ⟨eval_ne_count hk hz, fun _ => ⟨s, minv, X, hI', hf, hX1, hj⟩, fun _ => trivial⟩

theorem redc_ct_Y (M : Mont) : RedcCT M Public.aY := redc_ct_of M (by taint_decide)

theorem redc_ct_X (M : Mont) : RedcCT M Public.aX := redc_ct_of M (by taint_decide)

end VG.Proof.Bignum.X86_64
