module

public import VerifiedGarbage.Proof.Dsa.Arm.RandomTwo
public import VerifiedGarbage.Proof.Dsa.Arm.RandomScan
meta import VerifiedGarbage.Proof.Dsa.Arm.RandomTwo
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.RandomPrepare
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Arm.ArithCall
import VerifiedGarbage.Proof.Dsa.Arm.Bytes
import VerifiedGarbage.Proof.Dsa.Arm.Dispatch
import VerifiedGarbage.Proof.Dsa.Arm.Doubling
import VerifiedGarbage.Proof.Dsa.Arm.PowCall
import VerifiedGarbage.Proof.Dsa.Arm.PublicValidationBody
import VerifiedGarbage.Proof.Dsa.Arm.PublicValidationCall
import VerifiedGarbage.Proof.Dsa.Arm.PublicValidationCorrect
import VerifiedGarbage.Proof.Dsa.Arm.PublicValidationTrace
import VerifiedGarbage.Proof.Dsa.Arm.RandomBody
import VerifiedGarbage.Proof.Dsa.Arm.RandomSample
import VerifiedGarbage.Proof.Dsa.Arm.RandomSignCorrect
import VerifiedGarbage.Proof.Dsa.Arm.SignCorrect
import VerifiedGarbage.Proof.Dsa.Arm.ValidateTrace
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.DomainWidths
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Frame
import VerifiedGarbage.Proof.Dsa.OutputBytes
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Dsa.Random
import VerifiedGarbage.Proof.Dsa.RandomEncoding
import VerifiedGarbage.Proof.Dsa.RandomSign
import VerifiedGarbage.Proof.Dsa.RandomSignResult
import VerifiedGarbage.Proof.Dsa.RandomTrace
import VerifiedGarbage.Proof.Dsa.SignVerify
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.StreamBytes
import VerifiedGarbage.Proof.Dsa.Zero
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Mont.Arm.Csub
import VerifiedGarbage.Proof.Mont.Arm.Dyn.ContextInit
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Csub
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Digit
import VerifiedGarbage.Proof.Mont.Arm.Dyn.DigitRow
import VerifiedGarbage.Proof.Mont.Arm.Dyn.ExponentParts
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Inverse
import VerifiedGarbage.Proof.Mont.Arm.Dyn.MulRow
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Ops
import VerifiedGarbage.Proof.Mont.Arm.Dyn.PowerTwo
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Select
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Zeros
import VerifiedGarbage.Proof.Mont.Arm.Row
import VerifiedGarbage.Proof.Mont.Arm.Step
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.Weierstrass.Arm.Bytes
import VerifiedGarbage.Proof.Weierstrass.Arm.Const
import VerifiedGarbage.Proof.Weierstrass.Arm.Copy
import VerifiedGarbage.Proof.Weierstrass.Arm.Fprog
import VerifiedGarbage.Proof.Weierstrass.BytesLen32
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Weierstrass.Words32
meta import VerifiedGarbage.Proof.Dsa.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.Arm.ArithCall
meta import VerifiedGarbage.Proof.Dsa.Arm.Bytes
meta import VerifiedGarbage.Proof.Dsa.Arm.Dispatch
meta import VerifiedGarbage.Proof.Dsa.Arm.Doubling
meta import VerifiedGarbage.Proof.Dsa.Arm.PowCall
meta import VerifiedGarbage.Proof.Dsa.Arm.PublicValidationBody
meta import VerifiedGarbage.Proof.Dsa.Arm.PublicValidationCall
meta import VerifiedGarbage.Proof.Dsa.Arm.PublicValidationCorrect
meta import VerifiedGarbage.Proof.Dsa.Arm.PublicValidationTrace
meta import VerifiedGarbage.Proof.Dsa.Arm.RandomBody
meta import VerifiedGarbage.Proof.Dsa.Arm.RandomSample
meta import VerifiedGarbage.Proof.Dsa.Arm.RandomScan
meta import VerifiedGarbage.Proof.Dsa.Arm.RandomSignCorrect
meta import VerifiedGarbage.Proof.Dsa.Arm.SignCorrect
meta import VerifiedGarbage.Proof.Dsa.Arm.ValidateTrace
meta import VerifiedGarbage.Proof.Dsa.BitLengthBounds
meta import VerifiedGarbage.Proof.Dsa.Digest
meta import VerifiedGarbage.Proof.Dsa.DomainWidths
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Dsa.Frame
meta import VerifiedGarbage.Proof.Dsa.OutputBytes
meta import VerifiedGarbage.Proof.Dsa.PackedBytes
meta import VerifiedGarbage.Proof.Dsa.Random
meta import VerifiedGarbage.Proof.Dsa.RandomEncoding
meta import VerifiedGarbage.Proof.Dsa.RandomSign
meta import VerifiedGarbage.Proof.Dsa.RandomSignResult
meta import VerifiedGarbage.Proof.Dsa.RandomTrace
meta import VerifiedGarbage.Proof.Dsa.SignVerify
meta import VerifiedGarbage.Proof.Dsa.SizeBounds
meta import VerifiedGarbage.Proof.Dsa.StreamBytes
meta import VerifiedGarbage.Proof.Dsa.Zero
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Mont.Arm.Csub
meta import VerifiedGarbage.Proof.Mont.Arm.Dyn.ContextInit
meta import VerifiedGarbage.Proof.Mont.Arm.Dyn.Csub
meta import VerifiedGarbage.Proof.Mont.Arm.Dyn.Digit
meta import VerifiedGarbage.Proof.Mont.Arm.Dyn.DigitRow
meta import VerifiedGarbage.Proof.Mont.Arm.Dyn.ExponentParts
meta import VerifiedGarbage.Proof.Mont.Arm.Dyn.Inverse
meta import VerifiedGarbage.Proof.Mont.Arm.Dyn.MulRow
meta import VerifiedGarbage.Proof.Mont.Arm.Dyn.Ops
meta import VerifiedGarbage.Proof.Mont.Arm.Dyn.PowerTwo
meta import VerifiedGarbage.Proof.Mont.Arm.Dyn.Select
meta import VerifiedGarbage.Proof.Mont.Arm.Dyn.Zeros
meta import VerifiedGarbage.Proof.Mont.Arm.Row
meta import VerifiedGarbage.Proof.Mont.Arm.Step
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.RsaPss.Params
meta import VerifiedGarbage.Proof.Weierstrass.Arm.Bytes
meta import VerifiedGarbage.Proof.Weierstrass.Arm.Const
meta import VerifiedGarbage.Proof.Weierstrass.Arm.Copy
meta import VerifiedGarbage.Proof.Weierstrass.Arm.Fprog
meta import VerifiedGarbage.Proof.Weierstrass.BytesLen32
meta import VerifiedGarbage.Proof.Weierstrass.Words
meta import VerifiedGarbage.Proof.Weierstrass.Words32

/-!
# Preparing leaks only public data (32-bit ARM)

`prepare` branches on q's bytes, which are public: the scan's registers
after `j` bytes are a function of them (`scanAfter`), so two runs with the
same public data take the same branches.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_dp wp_ldrb op2_imm op2_reg eval_eq eval_ne)
open VG.Proof.Dsa (scanAfter scanNext)

/-- The scan before byte `j`. -/
def ScanAt (j : Nat) (s₀ t : State) : Prop :=
  RReady s₀ t ∧ ScanState t (rQ s₀ + BitVec.ofNat 32 j) ((rQBytes s₀).drop j) (scanAfter (rQBytes s₀) j)

/-- After loading byte `j`. -/
def ScanLoaded (j : Nat) (s₀ t : State) : Prop :=
  ScanAt j s₀ t ∧ t.gpr .r0 = ((rQBytes s₀).getD j 0).setWidth 32

theorem scanAt_pins {j : Nat} {a : Pub} {t₁ t₂ : State} (h₁ : At (ScanLoaded j) a t₁) (h₂ : At (ScanLoaded j) a t₂) :
    ∀ r ∈ [Reg.r0, .r1, .r2, .r3, .r4], t₁.gpr r = t₂.gpr r := by
  obtain ⟨s₁, -, e₁, ⟨-, S₁⟩, x₁⟩ := h₁
  obtain ⟨s₂, -, e₂, ⟨-, S₂⟩, x₂⟩ := h₂
  have e := e₁.trans e₂.symm
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [x₁, x₂, pub_qBytes e]
  · rw [S₁.r1, S₂.r1, pub_rQ e]
  · rw [S₁.r2, S₂.r2, pub_qBytes e]
  · rw [S₁.r3, S₂.r3, pub_qBytes e]
  · rw [S₁.r4, S₂.r4, pub_qBytes e]

theorem scanAt_r1 {j : Nat} {a : Pub} {t₁ t₂ : State} (h₁ : At (ScanAt j) a t₁) (h₂ : At (ScanAt j) a t₂) :
    t₁.gpr .r1 = t₂.gpr .r1 := by
  obtain ⟨s₁, -, e₁, -, S₁⟩ := h₁
  obtain ⟨s₂, -, e₂, -, S₂⟩ := h₂
  rw [S₁.r1, S₂.r1, pub_rQ (e₁.trans e₂.symm)]

theorem loadByte_ok {s₀ t : State} {j : Nat} (h : ScanAt j s₀ t) (hj : j < (rQBytes s₀).length) :
    WP isa (.block [.ldrb .r0 .r1 0]) t (ScanLoaded j s₀) := by
  obtain ⟨hr, S⟩ := h
  have hb := S.bytes
  have hl : 0 < ((rQBytes s₀).drop j).length := by rw [List.length_drop]; omega
  refine wp_ldrb (a := State.addr (rQ s₀ + BitVec.ofNat 32 j) + BitVec.ofNat 64 0) (by decide)
    (by rw [BitVec.add_zero, S.r1, BitVec.add_zero]) (hb.rd 0 hl) fun u v => WP.block_nil ?_
  have hv := hb.val 0 hl
  simp only [List.getElem_drop, Nat.add_zero] at hv
  rw [hv] at v
  refine ⟨⟨hr.upd v, ⟨by rw [v.other _ (by decide)]; exact S.r1,
    by rw [v.other _ (by decide)]; exact S.r2, by rw [v.other _ (by decide)]; exact S.r3,
    by rw [v.other _ (by decide)]; exact S.r4, hb.congr v.mem v.rd v.wr, S.bound, S.zero⟩⟩, ?_⟩
  rw [v.gpr, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl

theorem scanStep_ok {s₀ t : State} (A : RandomABI s₀) {j : Nat} (h : ScanAt j s₀ t)
    (hj : j < (rQBytes s₀).length) :
    WP isa significantByte t fun u => isa.eval .ne u = some (decide (j + 1 < (rQBytes s₀).length)) ∧
      ScanAt (j + 1) s₀ u := by
  obtain ⟨hr, S⟩ := h
  have hql := rQBytes_le A
  obtain ⟨b, rest, hbr⟩ : ∃ b rest, (rQBytes s₀).drop j = b :: rest :=
    ⟨_, _, List.drop_eq_getElem_cons hj⟩
  have hrl : rest.length + 1 = (rQBytes s₀).length - j := by
    have := congrArg List.length hbr; simp only [List.length_drop, List.length_cons] at this; omega
  rw [hbr] at S
  refine WP.mono (significantByte_ok S (by omega)) fun u ⟨S', z, m, k⟩ => ?_
  have hb : b = (rQBytes s₀).getD j 0 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    have := congrArg List.head? hbr
    rw [List.head?_drop, List.head?_cons] at this
    rw [List.getElem?_eq_getElem hj] at this
    exact (Option.some.inj this).symm
  have hd : (rQBytes s₀).drop (j + 1) = rest := by
    rw [← List.drop_drop, hbr, List.drop_one, List.tail_cons]
  refine ⟨?_, hr.congr k (by rw [m]; exact Frame.refl _ _), ?_⟩
  · rw [eval_ne, z]
    by_cases h0 : rest.length = 0
    · rw [decide_eq_true h0, decide_eq_false (by omega)]; rfl
    · rw [decide_eq_false h0, decide_eq_true (by omega)]; rfl
  · rw [hd, show rQ s₀ + BitVec.ofNat 32 (j + 1) = rQ s₀ + BitVec.ofNat 32 j + 1 by
      rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl]
    show ScanState u _ rest (scanNext (scanAfter (rQBytes s₀) j) ((rQBytes s₀).length - j)
      ((rQBytes s₀).getD j 0))
    rw [← hrl, ← hb]; exact S'

/-- Before the scan. -/
def ScanPre (s₀ t : State) : Prop :=
  RReady s₀ t ∧ t.gpr .r1 = rQ s₀ ∧ t.gpr .r2 = BitVec.ofNat 32 (rQBytes s₀).length

theorem significant_ct :
    RelCT isa (Two (At ScanPre)) Random.significant (Two fun a => At (ScanAt a.qBytes.length) a) := by
  unfold Random.significant
  refine RelCT.seq (two_piece (Ψ := fun a t => 0 < a.qBytes.length ∧ At (ScanAt 0) a t) []
    (by intro _ _ _ _ _ _ h; cases h) (by taint_decide) ?_) ?_
  · rintro a t ⟨s₀, A, e, hr, h1, h2⟩
    refine wp_mov (op2_imm (by decide)) fun u₁ v₁ => wp_mov (op2_imm (by decide)) fun u₂ v₂ => WP.block_nil ?_
    have R : Rest [.r3, .r4] t u₂ := (v₁.rest (by decide)).trans (v₂.rest (by decide))
    refine ⟨by rw [← e]; exact rQBytes_pos A, s₀, A, e, hr.congr R (by rw [v₂.mem, v₁.mem]; exact Frame.refl _ _),
      ⟨?_, ?_, ?_, ?_, ?_, by simp [scanAfter], fun _ => rfl⟩⟩
    · rw [BitVec.add_zero, R.gpr _ (by decide)]; exact h1
    · rw [List.drop_zero, R.gpr _ (by decide)]; exact h2
    · rw [v₂.other _ (by decide), v₁.gpr]; rfl
    · rw [v₂.gpr]; rfl
    · rw [BitVec.add_zero, List.drop_zero]
      exact (hr.q A).congr (by rw [v₂.mem, v₁.mem]) (by rw [R.rd]) (by rw [R.wr])
  · refine two_loop (Φ := fun a j => At (ScanAt j) a) (Ψ := fun a => At (ScanAt a.qBytes.length) a)
      (fun a => a.qBytes.length) ?_ ?_
    · unfold significantByte
      refine RelCT.seq (two_piece (Ψ := fun p => At (ScanLoaded p.2) p.1) [.r1]
        (fun p t₁ t₂ h₁ h₂ r hr => by
          rw [List.mem_singleton] at hr; subst hr; exact scanAt_r1 h₁.2 h₂.2) (by taint_decide) ?_) ?_
      · rintro ⟨a, j⟩ t ⟨hj, s₀, A, e, h⟩
        subst e
        exact WP.mono (loadByte_ok h hj) fun u hu => ⟨s₀, A, rfl, hu⟩
      · exact two_taint [.r0, .r1, .r2, .r3, .r4] (fun p t₁ t₂ h₁ h₂ => scanAt_pins h₁ h₂) (by taint_decide)
    · rintro a j t hj ⟨s₀, A, e, h⟩
      subst e
      refine WP.mono (scanStep_ok A h hj) fun u ⟨z, hu⟩ => ⟨z, fun _ => ⟨s₀, A, rfl, hu⟩, fun he => ?_⟩
      have he' : j + 1 = (rQBytes s₀).length := he
      exact ⟨s₀, A, rfl, by show ScanAt (rQBytes s₀).length s₀ u; rw [← he']; exact hu⟩

theorem prepHead_ok {s₀ t : State} (A : RandomABI s₀) (h : RReady s₀ t)
    (hk : slot t.mem (rBase s₀) oKey = s₀.gpr .r3) :
    WP isa (.block (clearNonce ++ ([ld .r1 oKey, ld .r0 (Random.arg aPLen), .dp .add .r1 .r1 (.reg .r0),
      ld .r2 (Random.arg aQLen)] : List Instr))) t (ScanPre s₀) := by
  have hqn := rQBytes_length A
  refine clearNonce_ok h fun t₁ h₁ m₁ k₁ _ => ?_
  have hk₁ : slot t₁.mem (rBase s₀) oKey = s₀.gpr .r3 := by
    rw [m₁, slot_outs (Outs.of_outside (clearMem_outside t.mem _ 8 (by decide)) (List.mem_singleton_self _))
      (by intro r hr; simp only [List.mem_singleton] at hr; subst hr; decide), hk]
  refine wp_ld h₁ (by decide) fun t₂ u₂ => wp_ldArg A (h₁.upd u₂) (j := 1) (by decide) fun t₃ u₃ =>
    wp_dp (op2_reg _ _) fun t₄ u₄ => wp_ldArg A (((h₁.upd u₂).upd u₃).upd u₄) (j := 2) (by decide)
      fun t₅ u₅ => WP.block_nil ?_
  refine ⟨(((((h₁.upd u₂).upd u₃).upd u₄).upd u₅)), ?_, ?_⟩
  · rw [u₅.other _ (by decide), u₄.gpr]
    show t₃.gpr .r1 + t₃.gpr .r0 = _
    rw [u₃.other _ (by decide), u₃.gpr, u₂.gpr, hk₁]; rfl
  · rw [u₅.gpr, hqn, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- After the scan. -/
def Scanned (s₀ t : State) : Prop :=
  RReady s₀ t ∧ t.gpr .r3 = BitVec.ofNat 32 (scanAfter (rQBytes s₀) (rQBytes s₀).length).1 ∧
    t.gpr .r4 = (scanAfter (rQBytes s₀) (rQBytes s₀).length).2.setWidth 32

theorem prepStore_ok {s₀ t : State} (A : RandomABI s₀) (h : RReady s₀ t) :
    WP isa (.block [ld .r1 oKey, ld .r0 (Random.arg aPLen), .dp .add .r1 .r1 (.reg .r0), ld .r0 (Random.arg aQLen),
      .dp .add .r1 .r1 (.reg .r0), .dp .sub .r1 .r1 (.reg .r3), st .r1 oQ, st .r3 oWidth]) t fun u =>
      RReady s₀ u ∧ u.gpr .r3 = t.gpr .r3 ∧ u.gpr .r4 = t.gpr .r4 := by
  refine wp_ld h (by decide) fun t₁ u₁ => wp_ldArg A (h.upd u₁) (j := 1) (by decide) fun t₂ u₂ =>
    wp_dp (op2_reg _ _) fun t₃ u₃ => wp_ldArg A (((h.upd u₁).upd u₂).upd u₃) (j := 2) (by decide) fun t₄ u₄ =>
    wp_dp (op2_reg _ _) fun t₅ u₅ => wp_dp (op2_reg _ _) fun t₆ u₆ =>
    wp_st ((((((h.upd u₁).upd u₂).upd u₃).upd u₄).upd u₅).upd u₆) (by decide) fun t₇ m₇ h₇ =>
    wp_st h₇ (by decide) fun t₈ m₈ h₈ => WP.block_nil ?_
  have R : Rest [.r0, .r1] t t₈ := (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans ((u₃.rest (by decide)).trans
    ((u₄.rest (by decide)).trans ((u₅.rest (by decide)).trans ((u₆.rest (by decide)).trans
    ((m₇.rest _).trans (m₈.rest _)))))))
  exact ⟨h₈, R.gpr _ (by decide), R.gpr _ (by decide)⟩

/-- Before preparing. -/
def PrepPre (s₀ t : State) : Prop := RReady s₀ t ∧ slot t.mem (rBase s₀) oKey = s₀.gpr .r3

theorem prepare_ct : RelCT isa (Two (At PrepPre)) Random.prepare fun _ _ => True := by
  unfold Random.prepare
  refine RelCT.seq (two_piece (Ψ := At ScanPre) [.r11] (pins_at (P := fun _ => PrepPre) id fun _ _ _ h => h.1)
    (by taint_decide)
    fun a t ⟨s₀, A, e, h, hk⟩ => WP.mono (prepHead_ok A h hk) fun u hu => ⟨s₀, A, e, hu⟩) ?_
  refine RelCT.seq (significant_ct.mono (fun _ _ h => h) fun _ _ h => h) ?_
  refine RelCT.seq (two_piece (Ψ := At Scanned) [.r11]
    (pins_r11 (Φ := fun a => At (ScanAt a.qBytes.length) a) id (P := fun a => ScanAt a.qBytes.length)
      (fun _ _ h => h) fun _ _ _ h => h.1) (by taint_decide) ?_) ?_
  · rintro a t ⟨s₀, A, e, hr, S⟩
    subst e
    refine WP.mono (prepStore_ok A hr) fun u ⟨hu, h3, h4⟩ => ⟨s₀, A, rfl, hu, ?_, ?_⟩
    · rw [h3]; exact S.r3
    · rw [h4]; exact S.r4
  · refine two_taint [.r11, .r3, .r4] (fun a t₁ t₂ h₁ h₂ r hr => ?_) (by taint_decide)
    obtain ⟨s₁, -, e₁, r₁, b₁, d₁⟩ := h₁
    obtain ⟨s₂, -, e₂, r₂, b₂, d₂⟩ := h₂
    have e := e₁.trans e₂.symm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact r11_of_rf r₁.rf (pub_rBase e ▸ r₂.rf)
    · rw [b₁, b₂, pub_qBytes e]
    · rw [d₁, d₂, pub_qBytes e]

end VG.Proof.Dsa.Arm
