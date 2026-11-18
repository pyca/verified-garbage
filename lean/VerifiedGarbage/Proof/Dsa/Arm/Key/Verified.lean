module

public import VerifiedGarbage.Proof.Dsa.Arm.Key.Frame
public import VerifiedGarbage.Impl.Dsa.Arm.GenerateKey
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.Proof.Dsa.Arm.Key.Two
public import VerifiedGarbage.Proof.Framework.Arm.Call
public import VerifiedGarbage.Impl.Dsa.Arm.Generate
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.Arm.Key.Saved
public import VerifiedGarbage.Proof.Dsa.Arm.Key.Body
import VerifiedGarbage.Proof.Dsa.Random
import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Dsa.Arm.Key.Prepare
import VerifiedGarbage.Proof.Dsa.RandomTraceResult
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.Arm.Key.Body
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Dsa.Arm.Key.Prepare
meta import VerifiedGarbage.Proof.Dsa.RandomTraceResult
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Dsa.Arm.Key.Sample
meta import VerifiedGarbage.Proof.Dsa.Arm.Key.Sample
public import VerifiedGarbage.Proof.Dsa.Arm.Key.Call
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Dsa.Arm.GenerateCheck
import VerifiedGarbage.Proof.Dsa.Arm.GenerateCheckCT
import VerifiedGarbage.Proof.Dsa.Arm.GenerateDerive
import VerifiedGarbage.Proof.Dsa.Arm.GenerateDeriveCT
public import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Dsa.Arm.Key.Call
meta import VerifiedGarbage.Proof.Dsa.Arm.Key.Two
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Dsa.Arm.GenerateCheck
meta import VerifiedGarbage.Proof.Dsa.Arm.GenerateCheckCT
meta import VerifiedGarbage.Proof.Dsa.Arm.GenerateDerive
meta import VerifiedGarbage.Proof.Dsa.Arm.GenerateDeriveCT
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Dsa.RandomTrace
meta import VerifiedGarbage.Proof.Dsa.RandomTrace
meta import VerifiedGarbage.Impl.Dsa.Arm.KeyRandom
public import VerifiedGarbage.Impl.Dsa.Arm.KeyRandom
public import VerifiedGarbage.Proof.Dsa.Arm.Key.Draw
import VerifiedGarbage.Proof.Dsa.RandomEncoding
meta import VerifiedGarbage.Proof.Dsa.Arm.Key.Draw
meta import VerifiedGarbage.Proof.Dsa.RandomEncoding

/-! ### `Dsa.Arm.Key.BodyCT`, which only this module used -/

section

/-! ### `Dsa.Arm.Key.PrepareCT`, which only this module used -/

section

/-!
# Preparing leaks only public data (32-bit ARM)

`prepare` branches on q's bytes, which are public: the scan's registers
after `j` bytes are a function of them (`scanAfter`), so two runs with the
same public data take the same branches.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Key

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
  have hl : 0 < ((rQBytes s₀).drop j).length := by rw [List.length_drop]; omega_using [hj]
  refine wp_ldrb (a := State.addr (rQ s₀ + BitVec.ofNat 32 j) + BitVec.ofNat 64 0) (by decide)
    (by rw [BitVec.add_zero, S.r1, BitVec.add_zero]) (hb.rd 0 hl) fun u v => WP.block_nil ?_
  have hv := hb.val 0 hl
  simp only [List.getElem_drop, Nat.add_zero] at hv
  rw [hv] at v
  refine ⟨⟨hr.upd v, ⟨by rw [v.other _ (by decide)]; exact S.r1,
    by rw [v.other _ (by decide)]; exact S.r2, by rw [v.other _ (by decide)]; exact S.r3,
    by rw [v.other _ (by decide)]; exact S.r4, hb.congr v.mem v.rd v.wr, S.bound, S.zero⟩⟩, ?_⟩
  rw [v.gpr, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl

theorem scanStep_ok {s₀ t : State} (A : KeyABI s₀) {j : Nat} (h : ScanAt j s₀ t)
    (hj : j < (rQBytes s₀).length) :
    WP isa significantByte t fun u => isa.eval .ne u = some (decide (j + 1 < (rQBytes s₀).length)) ∧
      ScanAt (j + 1) s₀ u := by
  obtain ⟨hr, S⟩ := h
  have hql := rQBytes_le A
  obtain ⟨b, rest, hbr⟩ : ∃ b rest, (rQBytes s₀).drop j = b :: rest :=
    ⟨_, _, List.drop_eq_getElem_cons hj⟩
  have hrl : rest.length + 1 = (rQBytes s₀).length - j := by
    have := congrArg List.length hbr; simp only [List.length_drop, List.length_cons] at this; omega_using [this]
  rw [hbr] at S
  refine WP.mono (significantByte_ok S (by omega_using [hql, hrl])) fun u ⟨S', z, m, k⟩ => ?_
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
    · rw [decide_eq_true h0, decide_eq_false (by omega_using [hrl, h0])]; rfl
    · rw [decide_eq_false h0, decide_eq_true (by omega_using [hrl, h0])]; rfl
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

theorem prepHead_ok {s₀ t : State} (A : KeyABI s₀) (h : RReady s₀ t)
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

theorem prepStore_ok {s₀ t : State} (A : KeyABI s₀) (h : RReady s₀ t) :
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

end VG.Proof.Dsa.Arm.Key

end

end

/-! ### `Dsa.Arm.Key.SampleCT`, which only this module used -/

section

/-! ### `Dsa.Arm.Key.DrawCT`, which only this module used -/

section

/-!
# A draw leaks only its public bounds and its decision (32-bit ARM)

Two runs of `draw` with the same public data, consumption and budget, whose
complete draws are both accepted or both rejected (`DrawPub.acc`), take
the same branches and addresses: the candidate's bytes reach neither.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Key

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd eval_eq eval_ne)
open VG.Proof.Dsa (maskValue copied copiedList copiedList_length copiedList_getD)

/-- The candidate of the draw at `used`. -/
abbrev drawCand (s₀ : State) (used : Nat) : List Byte :=
  copiedList (drawBytes s₀ used) (maskValue (rLead s₀).toNat) (rWidth s₀)

/-- What two runs of a draw share. -/
structure DrawPub where
  pub : Pub
  used : Nat
  draws : Nat
  /-- Whether a complete draw is accepted. -/
  acc : Bool

/-- A draw's entry. -/
structure DrawPre (a : DrawPub) (s₀ t : State) : Prop where
  smp : Smp s₀ a.used a.draws t
  pos : 1 ≤ a.draws
  le : a.draws ≤ 128
  q : 1 < rq s₀
  acc : a.used + rWidth s₀ ≤ (rInput s₀).rand.length → accepts s₀ (drawCand s₀ a.used) = a.acc

theorem width_pos {s₀ : State} (hq : 1 < rq s₀) : 1 ≤ rWidth s₀ :=
  Nat.pos_of_ne_zero ((VG.Proof.Dsa.random_valid_scan (rQBytes s₀)).mp hq).1

/-- After the head: the tape's length against the width. -/
def DrawHead (a : DrawPub) (s₀ t : State) : Prop :=
  DrawPre a s₀ t ∧ t.z = decide ((rInput s₀).rand.length - a.used < rWidth s₀)

/-- A complete draw. -/
def DrawFull (a : DrawPub) (s₀ t : State) : Prop :=
  DrawPre a s₀ t ∧ a.used + rWidth s₀ ≤ (rInput s₀).rand.length

/-- After the copy's header and first byte. -/
def CopyHead (a : DrawPub) (s₀ t : State) : Prop :=
  (∃ t₀, CopyInv s₀ t₀ (stackArg s₀ 3 + BitVec.ofNat 32 a.used) (drawPlace s₀) (drawBytes s₀ a.used)
    (maskValue (rLead s₀).toNat) 1 t) ∧ t.z = decide (rWidth s₀ - 1 = 0) ∧
  (drawBytes s₀ a.used).length = rWidth s₀

/-- After the copy's header. -/
def CopyHdr (a : DrawPub) (s₀ t : State) : Prop :=
  RReady s₀ t ∧ t.gpr .r1 = stackArg s₀ 3 + BitVec.ofNat 32 a.used ∧ t.gpr .r2 = BitVec.ofNat 32 (rWidth s₀) ∧
    t.gpr .r4 = t.gpr .r11 + BitVec.ofNat 32 (drawPlace s₀)

theorem copyInit_ct : RelCT isa (Two fun a => At (DrawFull a) a.pub) (.block KeyRandom.copyInit) fun _ _ => True := by
  unfold KeyRandom.copyInit
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := fun a => At (CopyHdr a) a.pub) [.r11]
    (pins_at DrawPub.pub fun _ _ _ h => h.1.smp.ready) (by taint_decide)
    fun a t ⟨s₀, A, e, D, _⟩ => WP.mono (copyHeader_ok A D.smp.ready D.smp.usedW D.smp.width)
      fun u ⟨h, _, _, x, c, d⟩ => ⟨s₀, A, e, h, x, c, d⟩) ?_
  refine two_taint [.r11, .r1, .r2, .r4] (fun a t₁ t₂ h₁ h₂ r hr => ?_) (by taint_decide)
  obtain ⟨s₁, _, e₁, r₁, x₁, c₁, d₁⟩ := h₁
  obtain ⟨s₂, _, e₂, r₂, x₂, c₂, d₂⟩ := h₂
  have e := e₁.trans e₂.symm
  have r11 := r11_of_rf r₁.rf (pub_rBase e ▸ r₂.rf)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact r11
  · rw [x₁, x₂, pub_arg e 3 (by decide)]
  · rw [c₁, c₂, pub_rWidth e]
  · rw [d₁, d₂, r11, pub_drawPlace e]

theorem copy_ct : RelCT isa (Two fun a => At (DrawFull a) a.pub) KeyRandom.copy fun _ _ => True := by
  unfold KeyRandom.copy
  refine RelCT.seq (two_post (Ψ := fun a => At (CopyHead a) a.pub) copyInit_ct
    fun a t ⟨s₀, A, e, D, hf⟩ => ?_) ?_
  · exact WP.mono (copyInit_ok A D.smp.ready D.smp.usedW D.smp.width D.smp.mask hf (width_pos D.q))
      fun u ⟨I, z⟩ => ⟨s₀, A, e, ⟨t, I⟩, z, drawBytes_length hf⟩
  unfold copyRest
  refine two_ite (fun a t₁ t₂ ⟨s₁, _, e₁, _, z₁, _⟩ ⟨s₂, _, e₂, _, z₂, _⟩ => by
    rw [eval_ne, eval_ne, z₁, z₂, pub_rWidth (e₁.trans e₂.symm)]) ?_ ?_
  · refine two_taint [.r1, .r2, .r4] (fun a t₁ t₂ h₁ h₂ r hr => ?_) (by taint_decide)
    obtain ⟨⟨s₁, _, e₁, ⟨_, I₁⟩, _, l₁⟩, _⟩ := h₁
    obtain ⟨⟨s₂, _, e₂, ⟨_, I₂⟩, _, l₂⟩, _⟩ := h₂
    have e := e₁.trans e₂.symm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [I₁.r1, I₂.r1, pub_arg e 3 (by decide)]
    · rw [I₁.r2, I₂.r2, l₁, l₂, pub_rWidth e]
    · rw [I₁.r4, I₂.r4, r11_of_rf I₁.ready.rf (pub_rBase e ▸ I₂.ready.rf), pub_drawPlace e]
  · exact two_taint [] (fun _ _ _ _ _ _ h => by cases h) (by taint_decide)

/-- After the copy. -/
structure Copied (a : DrawPub) (s₀ t : State) : Prop where
  pre : DrawPre a s₀ t
  full : a.used + rWidth s₀ ≤ (rInput s₀).rand.length
  bytes : ∀ i < rWidth s₀, t.mem (off (rBase s₀) (drawPlace s₀ + i)) =
    copied (drawBytes s₀ a.used) (maskValue (rLead s₀).toNat) i

/-- After consuming the draw. -/
structure Consumed (a : DrawPub) (s₀ t : State) : Prop where
  smp : Smp s₀ (a.used + rWidth s₀) a.draws t
  pos : 1 ≤ a.draws
  le : a.draws ≤ 128
  q : 1 < rq s₀
  acc : accepts s₀ (drawCand s₀ a.used) = a.acc
  bytes : ∀ i < rWidth s₀, t.mem (off (rBase s₀) (drawPlace s₀ + i)) =
    copied (drawBytes s₀ a.used) (maskValue (rLead s₀).toNat) i

/-- Before the comparison's loop. -/
def RangeHead (s₀ t : State) : Prop := ∃ t₀ cs, RangeInv s₀ t₀ cs (rWidth s₀) t

theorem inRange_ct : RelCT isa (Two fun a => At (Consumed a) a.pub) inRange fun _ _ => True := by
  unfold inRange
  refine RelCT.seq (two_piece (Ψ := fun a => At RangeHead a.pub) [.r11]
    (pins_at DrawPub.pub fun _ _ _ h => h.smp.ready) (by taint_decide)
    fun a t ⟨s₀, A, e, C⟩ => WP.mono (rangeInit_ok A C.smp.ready (cs := drawCand s₀ a.used) C.smp.q
      C.smp.width (copiedList_length _ _ _)) fun u ⟨I, _⟩ => ⟨s₀, A, e, t, _, I⟩) ?_
  refine two_taint [.r1, .r2, .r4] (fun a t₁ t₂ h₁ h₂ r hr => ?_) (by taint_decide)
  obtain ⟨s₁, _, e₁, _, _, I₁⟩ := h₁
  obtain ⟨s₂, _, e₂, _, _, I₂⟩ := h₂
  have e := e₁.trans e₂.symm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [I₁.r1, I₂.r1, pub_rQ e, pub_qBytes e, pub_rWidth e]
  · rw [I₁.r2, I₂.r2, pub_rWidth e]
  · rw [I₁.r4, I₂.r4, r11_of_rf I₁.ready.rf (pub_rBase e ▸ I₂.ready.rf), pub_drawPlace e, pub_rWidth e]

/-- Before the decision. -/
structure Decided (a : DrawPub) (s₀ t : State) : Prop where
  smp : Smp s₀ (a.used + rWidth s₀) a.draws t
  pos : 1 ≤ a.draws
  le : a.draws ≤ 128
  z : t.z = !a.acc

/-- After spending a draw. -/
def Spent (a : DrawPub) (s₀ t : State) : Prop :=
  RReady s₀ t ∧ t.z = decide (a.draws - 1 = 0)

theorem drawFinish_ct : RelCT isa (Two fun a => At (Decided a) a.pub) drawFinish fun _ _ => True := by
  unfold drawFinish
  refine two_ite (fun a t₁ t₂ ⟨_, _, _, D₁⟩ ⟨_, _, _, D₂⟩ => by rw [eval_ne, eval_ne, D₁.z, D₂.z]) ?_ ?_
  · exact two_taint [.r11] (pins_at' DrawPub.pub fun _ _ _ h => h.smp.ready) (by taint_decide)
  refine RelCT.seq (two_piece (Ψ := fun a => At (Spent a) a.pub) [.r11]
    (pins_at' DrawPub.pub fun _ _ _ h => h.smp.ready) (by taint_decide)
    fun a t ⟨⟨s₀, A, e, D⟩, _⟩ => WP.mono (drawDec_ok A D.smp D.pos D.le)
      fun u ⟨_, _, _, h, z, _⟩ => ⟨s₀, A, e, h, z⟩) ?_
  refine two_ite (fun a t₁ t₂ ⟨_, _, _, _, z₁⟩ ⟨_, _, _, _, z₂⟩ => by rw [eval_eq, eval_eq, z₁, z₂]) ?_ ?_
  · exact two_taint [.r11] (pins_at' DrawPub.pub fun _ _ _ h => h.1) (by taint_decide)
  · exact two_taint [] (fun _ _ _ _ _ _ h => by cases h) (by taint_decide)

/-- After the comparison, the decision: the draw's acceptance. -/
theorem inRange_decided {a : DrawPub} {s₀ t : State} (A : KeyABI s₀) (C : Consumed a s₀ t) :
    WP isa inRange t (Decided a s₀) :=
  WP.mono (inRange_ok A C.smp.ready (cs := drawCand s₀ a.used) C.smp.q C.smp.width (copiedList_length _ _ _)
    (width_pos C.q) fun i hi => by rw [copiedList_getD _ _ hi]; exact C.bytes i hi)
    fun u ⟨_, z, m, h, _⟩ => ⟨C.smp.congr A h (by rw [m]; exact Outs.refl _ _ _) (by rw [m]) (by rw [m]),
      C.pos, C.le, by rw [z, C.acc]⟩

theorem full_ct : RelCT isa (Two fun a => At (DrawFull a) a.pub)
    (.seq KeyRandom.copy (.seq (.block [ld .r0 oUsed, ld .r7 oWidth, .dp .add .r0 .r0 (.reg .r7), st .r0 oUsed])
      (.seq inRange drawFinish))) fun _ _ => True := by
  refine RelCT.seq (two_post (Ψ := fun a => At (Copied a) a.pub) copy_ct
    fun a t ⟨s₀, A, e, D, hf⟩ => WP.mono (drawCopy_ok A D.smp hf (width_pos D.q))
      fun u ⟨S, hc, _, _⟩ => ⟨s₀, A, e, { D with smp := S }, hf, hc⟩) ?_
  refine RelCT.seq (two_piece (Ψ := fun a => At (Consumed a) a.pub) [.r11]
    (pins_at DrawPub.pub fun _ _ _ h => h.pre.smp.ready) (by taint_decide)
    fun a t ⟨s₀, A, e, C⟩ => WP.mono (drawUsed_ok A C.pre.smp C.full)
      fun u ⟨S, hm, _⟩ => ⟨s₀, A, e, S, C.pre.pos, C.pre.le, C.pre.q, C.pre.acc C.full,
        drawUsed_bytes A hm C.bytes⟩) ?_
  exact RelCT.seq (two_post (Ψ := fun a => At (Decided a) a.pub) inRange_ct
    fun a t ⟨s₀, A, e, C⟩ => WP.mono (inRange_decided A C) fun u D => ⟨s₀, A, e, D⟩) drawFinish_ct

theorem draw_ct : RelCT isa (Two fun a => At (DrawPre a) a.pub) KeyRandom.draw fun _ _ => True := by
  unfold KeyRandom.draw
  refine RelCT.seq (two_piece (Ψ := fun a => At (DrawHead a) a.pub) [.r11]
    (pins_at DrawPub.pub fun _ _ _ h => h.smp.ready) (by taint_decide)
    fun a t ⟨s₀, A, e, D⟩ => WP.mono (drawHead_ok A D.smp)
      fun u ⟨S, _, _, c⟩ => ⟨s₀, A, e, { D with smp := S }, c⟩) ?_
  refine two_ite (fun a t₁ t₂ ⟨s₁, _, e₁, _, c₁⟩ ⟨s₂, _, e₂, _, c₂⟩ => by
    have e := e₁.trans e₂.symm
    rw [eval_eq, eval_eq, c₁, c₂, pub_randLen e, pub_rWidth e]) ?_ ?_
  · exact two_taint [.r11] (pins_at' DrawPub.pub fun _ _ _ h => h.1.smp.ready) (by taint_decide)
  · refine two_map id (fun a t ⟨⟨s₀, A, e, D, c⟩, hb⟩ => ⟨s₀, A, e, D, ?_⟩) full_ct
    have := D.smp.usedBound
    show a.used + rWidth s₀ ≤ (rInput s₀).rand.length
    rw [eval_eq, c, Option.some.injEq, decide_eq_false_iff_not] at hb
    omega_using [hb, this]

end VG.Proof.Dsa.Arm.Key

end

end

/-!
# Sampling leaks only its trace (32-bit ARM)

Two runs of the sampler whose specification traces agree draw alike: each
draw's decision is the trace's head (`LoopAt.drawPre`), so they take the
same branches; after a rejection the rest of the trace is the next draw's.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Key

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_cmp op2_imm eval_eq eval_ne)

/-- The width of q's significant bytes. -/
def Pub.width (a : Pub) : Nat := (VG.Proof.Dsa.significant a.qBytes).1

theorem pub_width {s₀ : State} {a : Pub} (e : pubOf s₀ = a) : a.width = rWidth s₀ := by
  rw [← e]; rfl

/-- What two runs share before a draw of the sampling loop. -/
structure LoopPub where
  pub : Pub
  used : Nat
  draws : Nat
  tr : List Nat

/-- Before a draw of the sampling loop, whose trace is `tr`. -/
structure LoopAt (a : LoopPub) (s₀ t : State) : Prop where
  smp : Smp s₀ a.used a.draws t
  status : slot t.mem (rBase s₀) oStatus = 4
  pos : 1 ≤ a.draws
  le : a.draws ≤ 128
  q : 1 < rq s₀
  tr : (spl s₀ a.draws a.used).trace = a.tr

/-- Whether the loop draws again: a rejection, and draws left. -/
def LoopPub.cont (a : LoopPub) : Bool := (a.tr.head? == some 0) && decide (2 ≤ a.draws)

def LoopPub.next (a : LoopPub) : LoopPub := ⟨a.pub, a.used + a.pub.width, a.draws - 1, a.tr.tail⟩

/-- The draw's decision is the trace's. -/
theorem LoopAt.drawPre {a : LoopPub} {s₀ t : State} (L : LoopAt a s₀ t) :
    DrawPre ⟨a.pub, a.used, a.draws, a.tr.head? == some 1⟩ s₀ t := by
  refine ⟨L.smp, L.pos, L.le, L.q, fun hfull => ?_⟩
  dsimp only at hfull
  obtain ⟨d', hd'⟩ : ∃ d', a.draws = d' + 1 := ⟨a.draws - 1, by have := L.pos; omega_using [this]⟩
  have hdw : Spec.Dsa.Random.drawBytes (rq s₀) = rWidth s₀ := rWidth_eq s₀
  have hdl : (drawBytes s₀ a.used).length = rWidth s₀ := drawBytes_length hfull
  have htr := L.tr
  rw [hd'] at htr
  show accepts s₀ (drawCand s₀ a.used) = (a.tr.head? == some 1)
  rw [accepts_candidate hdl (width_pos L.q), ← htr, spl,
    VG.Proof.Dsa.Random.sample_trace_head _ _ _ L.q (by rw [hdw, List.length_drop]; omega_using [hfull]), hdw]

def sampleBody : Prog isa := .seq KeyRandom.draw (.block [ld .r0 oStatus, .cmp .r0 (.imm 4)])

/-- After a draw and the loop's test. -/
def StepPost (a : LoopPub) (s₀ t : State) : Prop :=
  RReady s₀ t ∧ t.z = a.cont ∧ (a.cont = true → LoopAt a.next s₀ t)

theorem sub_four_ne {x : BitVec 32} (h : x ≠ 4) : (x - 4 == 0) = false := by
  simp only [beq_eq_false_iff_ne, ne_eq]
  intro h'
  apply h
  calc x = x - 4 + 4 := (BitVec.sub_add_cancel x 4).symm
    _ = 4 := by rw [h']; rfl

theorem step_ok {a : LoopPub} {s₀ t : State} (A : KeyABI s₀) (e : pubOf s₀ = a.pub) (L : LoopAt a s₀ t) :
    WP isa sampleBody t (StepPost a s₀) := by
  unfold sampleBody
  refine WP.seq (WP.mono (draw_ok A L.smp L.pos L.le L.q L.status) fun v ⟨hv, _, _, hcase⟩ => ?_)
  refine wp_ld hv (by decide) fun v₁ uv₁ => wp_cmp (op2_imm (by decide)) fun v₂ fv₂ zv₂ => WP.block_nil ?_
  have hv₂ : RReady s₀ v₂ := (hv.upd uv₁).fupd fv₂
  have mv₂ : v₂.mem = v.mem := by rw [fv₂.mem, uv₁.mem]
  have htr := L.tr
  rcases hcase with ⟨stv, h2, Sv, _, hspl⟩ | ⟨stv, _, hh⟩
  · have hc : a.cont = true := by
      simp only [LoopPub.cont, ← htr, hspl, List.head?_cons, beq_self_eq_true, Bool.true_and,
        decide_eq_true_eq]
      exact h2
    refine ⟨hv₂, by rw [zv₂, uv₁.gpr, stv, hc]; rfl, fun _ => ⟨?_, by rw [mv₂]; exact stv,
      by show 1 ≤ a.draws - 1; omega_using [h2], by show a.draws - 1 ≤ 128; have := L.le; omega_using [this], L.q, ?_⟩⟩
    · show Smp s₀ (a.used + a.pub.width) (a.draws - 1) v₂
      rw [pub_width e]; exact Sv.mem A hv₂ mv₂
    · show (spl s₀ (a.draws - 1) (a.used + a.pub.width)).trace = a.tr.tail
      rw [pub_width e, ← htr, hspl]; rfl
  · have hc : a.cont = false := by
      simp only [LoopPub.cont, ← htr, Bool.and_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not]
      rcases hh with hh | hh
      · exact .inl hh
      · exact .inr (by omega_using [hh])
    refine ⟨hv₂, by rw [zv₂, uv₁.gpr, sub_four_ne stv, hc], fun h => by rw [hc] at h; cases h⟩

theorem sampleLoop_ct (n : Nat) :
    RelCT isa (Two fun a t => a.draws = n ∧ At (LoopAt a) a.pub t) (.loop sampleBody .eq)
      (Two fun (a : Pub) => At (fun s₀ t => RReady s₀ t) a) := by
  refine RelCT.loop (M := isa) (fun n => Two fun a t => a.draws = n ∧ At (LoopAt a) a.pub t) (fun n => ?_) n
  have hct : RelCT isa (Two fun a t => a.draws = n ∧ At (LoopAt a) a.pub t) sampleBody fun _ _ => True := by
    unfold sampleBody
    refine RelCT.seq (two_post (Ψ := fun a => At (fun s₀ t => RReady s₀ t) a.pub)
      (two_map (fun a => (⟨a.pub, a.used, a.draws, a.tr.head? == some 1⟩ : DrawPub))
        (fun a t ⟨_, s₀, A, e, L⟩ => ⟨s₀, A, e, L.drawPre⟩) draw_ct)
      (fun a t ⟨_, s₀, A, e, L⟩ => WP.mono (draw_ok A L.smp L.pos L.le L.q L.status)
        fun u h => ⟨s₀, A, e, h.1⟩)) ?_
    exact two_taint [.r11] (pins_at (P := fun _ s₀ t => RReady s₀ t) LoopPub.pub fun _ _ _ h => h)
      (by taint_decide)
  have hp := two_post (Ψ := fun a t => a.draws = n ∧ At (StepPost a) a.pub t) hct
    fun a t ⟨hn, s₀, A, e, L⟩ => WP.mono (step_ok A e L) fun u h => ⟨hn, s₀, A, e, h⟩
  refine hp.mono (fun _ _ h => h) ?_
  rintro t₁ t₂ ⟨a, ⟨hn, s₁, A₁, e₁, r₁, z₁, c₁⟩, ⟨_, s₂, A₂, e₂, r₂, z₂, c₂⟩⟩
  refine ⟨by rw [eval_eq, eval_eq, z₁, z₂], fun _ => ⟨a.pub, ⟨s₁, A₁, e₁, r₁⟩, ⟨s₂, A₂, e₂, r₂⟩⟩, fun hc => ?_⟩
  have hc' : a.cont = true := by rw [eval_eq, z₁, Option.some.injEq] at hc; exact hc
  have h2 : 2 ≤ a.draws := by
    simp only [LoopPub.cont, Bool.and_eq_true, decide_eq_true_eq] at hc'; exact hc'.2
  exact ⟨n - 1, by omega, a.next, ⟨by show a.draws - 1 = n - 1; omega_using [hn], s₁, A₁, e₁, c₁ hc'⟩,
    ⟨by show a.draws - 1 = n - 1; omega_using [hn], s₂, A₂, e₂, c₂ hc'⟩⟩

/-- What two runs of the sampler share. -/
structure SmpPub where
  pub : Pub
  used : Nat
  tr : List Nat

/-- The sampler's entry. -/
def SamplePre (a : SmpPub) (s₀ t : State) : Prop :=
  (∃ d, Smp s₀ a.used d t) ∧ 1 < rq s₀ ∧ (spl s₀ 128 a.used).trace = a.tr

theorem sample_ct : RelCT isa (Two fun a => At (SamplePre a) a.pub) KeyRandom.sample fun _ _ => True := by
  unfold KeyRandom.sample
  refine RelCT.seq (two_piece (Ψ := fun a => At (LoopAt ⟨a.pub, a.used, 128, a.tr⟩) a.pub) [.r11]
    (pins_at SmpPub.pub fun _ _ _ h => h.1.choose_spec.ready) (by taint_decide)
    fun a t ⟨s₀, A, e, ⟨d, S⟩, hq, htr⟩ => WP.mono (sampleInit_ok A S)
      fun u ⟨S', st, _, _⟩ => ⟨s₀, A, e, S', st, (by decide : 1 ≤ 128), (by decide : 128 ≤ 128), hq, htr⟩) ?_
  refine RelCT.seq (two_map (fun a => (⟨a.pub, a.used, 128, a.tr⟩ : LoopPub)) (fun _ _ h => ⟨rfl, h⟩)
    (sampleLoop_ct 128)) ?_
  exact two_taint [.r11] (pins_at (P := fun _ s₀ t => RReady s₀ t) id fun _ _ _ h => h) (by taint_decide)

end VG.Proof.Dsa.Arm.Key

end

end

/-! ### `Dsa.Arm.Key.FinishCT`, which only this module used -/

section

/-!
# Key generation's exit leaks only the status (32-bit ARM)

`finish` branches on the overall status, and writes through the public `out`
and `used` pointers.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Key

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random VG.Impl.Dsa.Arm.RandomSign
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_cmp op2_imm eval_eq eval_ne)

/-- At the end: the frame's slots, and the overall status `p.2`. -/
def FinAt (p : Pub × Nat) : State → Prop := At (fun s₀ t => RFin s₀ t ∧ (rResult s₀).status = p.2) p.1

/-! ## The end -/

/-- Test the overall status. -/
theorem finTest_ok {s₀ t : State} (A : KeyABI s₀) (F : RFin s₀ t) :
    WP isa (.block [ld .r0 oStatus, .cmp .r0 (.imm 1)]) t fun u =>
      RReady s₀ u ∧ Saved s₀ u.mem ∧ u.z = decide ((rResult s₀).status = 1) := by
  have hR := rResult_status_le A
  refine wp_ld F.ready (by decide) fun t₁ u₁ => wp_cmp (op2_imm (by decide)) fun t₂ f₂ z₂ => WP.block_nil ?_
  rw [u₁.gpr, F.status, one_beq (by omega_using [hR])] at z₂
  exact ⟨(F.ready.upd u₁).fupd f₂, by rw [f₂.mem, u₁.mem]; exact F.saved, z₂⟩

/-- Ready, with public data `p.1`. -/
def ReadyAt (p : Pub × Nat) : State → Prop := At (fun s₀ t => RReady s₀ t ∧ Saved s₀ t.mem) p.1

/-- The output's address and length. -/
theorem zeroHead_ok {s₀ t : State} (h : RReady s₀ t) (sv : Saved s₀ t.mem) :
    WP isa (.block [ld .r1 oOut, ld .r2 oOutLen, .mov .r0 (.imm 0)]) t fun u =>
      u.gpr .r1 = s₀.gpr .r0 ∧ u.gpr .r2 = s₀.gpr .r1 := by
  refine wp_ld h (by decide) fun t₁ u₁ => wp_ld (h.upd u₁) (by decide) fun t₂ u₂ =>
    VG.Proof.X25519.Arm.wp_mov (op2_imm (by decide)) fun t₃ u₃ => WP.block_nil ⟨?_, ?_⟩
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, sv.2.1]
  · rw [u₃.other _ (by decide), u₂.gpr, u₁.mem, sv.2.2.1]

theorem zeroOut_ct : RelCT isa (Two fun p s => ReadyAt p s ∧ isa.eval .ne s = some true) zeroOut
    fun _ _ => True := by
  unfold zeroOut
  refine RelCT.seq (two_piece (Ψ := fun p => At (fun s₀ t => t.gpr .r1 = s₀.gpr .r0 ∧ t.gpr .r2 = s₀.gpr .r1) p.1)
    [.r11] (pins_at' (P := fun _ s₀ t => RReady s₀ t ∧ Saved s₀ t.mem) Prod.fst fun _ _ _ h => h.1)
    (by taint_decide) fun p t ⟨⟨s₀, A, e, h, sv⟩, _⟩ => WP.mono (zeroHead_ok h sv) fun u hu => ⟨s₀, A, e, hu⟩) ?_
  refine two_taint [.r1, .r2] (fun p t₁ t₂ h₁ h₂ r hr => ?_) (by taint_decide)
  obtain ⟨s₁, _, e₁, x₁, c₁⟩ := h₁
  obtain ⟨s₂, _, e₂, x₂, c₂⟩ := h₂
  have e := e₁.trans e₂.symm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [x₁, x₂, pub_r0 e]
  · rw [c₁, c₂, pub_r1 e]

/-- The nonce cleared, and the address of `used`. -/
theorem finPrefix_ok {s₀ t : State} (h : RReady s₀ t) (sv : Saved s₀ t.mem) :
    WP isa (.block (clearNonce ++ ([ld .r4 oUsedPtr] : List Instr))) t fun u =>
      RReady s₀ u ∧ u.gpr .r4 = s₀.gpr .r2 := by
  refine clearNonce_ok h fun t₁ h₁ m₁ _ _ => ?_
  have o₁ : Outs (rBase s₀) [(oNonce, 32)] t.mem t₁.mem := by
    rw [m₁]; exact Outs.of_outside (clearMem_outside _ _ 8 (by decide)) (List.mem_singleton_self _)
  have sv₁ : Saved s₀ t₁.mem := sv.of_outs o₁ (by decide)
  exact wp_ld h₁ (by decide) fun t₂ u₂ => WP.block_nil ⟨h₁.upd u₂, by rw [u₂.gpr]; exact sv₁.2.2.2.1⟩

theorem finalBlock_ct : RelCT isa (Two ReadyAt) (.block (clearNonce ++ finalList)) fun _ _ => True := by
  show RelCT isa _ (.block ((clearNonce ++ [ld .r4 oUsedPtr]) ++
    [ld .r0 oUsed, .str .r0 .r4 0, .mov .r0 (.imm 0), .str .r0 .r4 4, ld .r0 oStatus,
      ld .r4 0, ld .r5 4, ld .r6 8, ld .r7 12, ld .r8 16, ld .r9 20, ld .r10 24, ld .lr 32, ld .r11 28])) _
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := fun p => At (fun s₀ t => RReady s₀ t ∧ t.gpr .r4 = s₀.gpr .r2) p.1)
    [.r11] (pins_at (P := fun _ s₀ t => RReady s₀ t ∧ Saved s₀ t.mem) Prod.fst fun _ _ _ h => h.1)
    (by taint_decide) fun p t ⟨s₀, A, e, h, sv⟩ => WP.mono (finPrefix_ok h sv) fun u hu => ⟨s₀, A, e, hu⟩) ?_
  refine two_taint [.r11, .r4] (fun p t₁ t₂ h₁ h₂ r hr => ?_) (by taint_decide)
  obtain ⟨s₁, _, e₁, r₁, d₁⟩ := h₁
  obtain ⟨s₂, _, e₂, r₂, d₂⟩ := h₂
  have e := e₁.trans e₂.symm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact r11_of_rf r₁.rf (pub_rBase e ▸ r₂.rf)
  · rw [d₁, d₂, pub_r2 e]

theorem finish_ct : RelCT isa (Two FinAt) finish fun _ _ => True := by
  unfold finish
  rw [finishBlock_eq]
  refine RelCT.seq (two_piece (Ψ := fun (p : Pub × Nat) => At (fun s₀ t => RReady s₀ t ∧ Saved s₀ t.mem ∧
      t.z = decide (p.2 = 1)) p.1) [.r11]
    (pins_at (P := fun p s₀ t => RFin s₀ t ∧ (rResult s₀).status = p.2) Prod.fst fun _ _ _ h => h.1.ready)
    (by taint_decide) fun p t ⟨s₀, A, e, Fi, st⟩ => WP.mono (finTest_ok A Fi)
      fun u ⟨h, sv, z⟩ => ⟨s₀, A, e, h, sv, by rw [z, st]⟩) ?_
  refine RelCT.seq (R := Two ReadyAt) (two_ite (fun p t₁ t₂ ⟨s₁, _, e₁, _, _, z₁⟩ ⟨s₂, _, e₂, _, _, z₂⟩ => by
    rw [eval_ne, eval_ne, z₁, z₂]) ?_ ?_) finalBlock_ct
  · exact two_post (Ψ := ReadyAt) (two_map id (fun p t ⟨⟨s₀, A, e, h, sv, _⟩, hb⟩ => ⟨⟨s₀, A, e, h, sv⟩, hb⟩)
      zeroOut_ct) fun p t ⟨⟨s₀, A, e, h, sv, _⟩, _⟩ => WP.mono (zeroOut_ok A h sv)
        fun u ⟨hv, fv, _, _⟩ => ⟨s₀, A, e, hv, sv.of_slots fun d _ hd => apart_slot fv A.stackOut hd⟩
  · exact two_post (Ψ := ReadyAt) (two_taint [] (fun _ _ _ _ _ _ h => by cases h) (by taint_decide))
      fun p t ⟨⟨s₀, A, e, h, sv, _⟩, _⟩ => WP.block_nil ⟨s₀, A, e, h, sv⟩

end VG.Proof.Dsa.Arm.Key

end

end

/-! ### `Dsa.Arm.Key.CallCT`, which only this module used -/

section

/-!
# The calls of key generation leak only what their contracts allow (32-bit ARM)

Two runs with the same public data and domain push the same words and call
`vg_dsa_check_parameters` with the same public arguments and domain
(`checkCall_ct`), and `vg_dsa_derive_key` with the same public arguments,
domain and status (`deriveCall_ct`), which their contracts' constant time
covers.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Key

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random VG.Impl.Dsa.Arm.GenerateKey

variable {umaal : Bool}

theorem pub_checkRd {s₁ s₂ : State} (e : pubOf s₁ = pubOf s₂) : checkRd s₁ = checkRd s₂ := by
  simp only [checkRd, rKeyR, pub_r3 e, pub_arg e 0 (by decide), pub_rLow e]

theorem pub_checkWr {s₁ s₂ : State} (e : pubOf s₁ = pubOf s₂) : checkWr s₁ = checkWr s₂ := by
  simp only [checkWr, rScratch, pub_arg e 5 (by decide), pub_arg e 6 (by decide)]

theorem pub_deriveRd {s₁ s₂ : State} (e : pubOf s₁ = pubOf s₂) : deriveRd s₁ = deriveRd s₂ := by
  simp only [deriveRd, nonceR, rKeyR, pub_r3 e, pub_arg e 0 (by decide), pub_arg e 2 (by decide),
    pub_rLow e, pub_rBase e]

theorem pub_deriveWr {s₁ s₂ : State} (e : pubOf s₁ = pubOf s₂) : deriveWr s₁ = deriveWr s₂ := by
  simp only [deriveWr, rOut, rScratch, pub_r0 e, pub_r1 e, pub_arg e 5 (by decide), pub_arg e 6 (by decide)]

/-- The domain the callee reads is the key's. -/
theorem params_call {s₀ u : State} (A : KeyABI s₀) (h : RReady s₀ u) (rd wr : List Region) :
    Spec.Rsa.bytesAt (callEntryOf rd wr u).mem (State.addr (s₀.gpr .r3)) (stackArg s₀ 0).toNat =
      (rInput s₀).key := by
  simp only [State.withRegions_mem, State.callEntry_mem]
  rw [rBytes_frame (call_push_frame A h) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (A.stackKey.sub_left (low_sub s₀ (by decide))).symm)
    (by have := (stackArg s₀ 0).isLt; omega_using []), key_bytes A h]

theorem pushed_sp_eq {s₁ s₂ t₁ t₂ : State} (e : pubOf s₁ = pubOf s₂) (h₁ : RReady s₁ t₁) (h₂ : RReady s₂ t₂)
    (rd₁ wr₁ rd₂ wr₂ : List Region) : (callEntryOf rd₁ wr₁ t₁).sp = (callEntryOf rd₂ wr₂ t₂).sp := by
  show (pushed callPush t₁).sp = (pushed callPush t₂).sp
  rw [pushed_sp, pushed_sp, h₁.sp, h₂.sp, pub_sp e]

/-! ## The domain check -/

/-- Two runs about to call the check alike. -/
def CheckRel (t₁ t₂ : State) : Prop :=
  ∃ s₁ s₂, KeyABI s₁ ∧ KeyABI s₂ ∧ pubOf s₁ = pubOf s₂ ∧ (rInput s₁).key = (rInput s₂).key ∧
    RReady s₁ t₁ ∧ RReady s₂ t₂ ∧ CheckRegs s₁ t₁ ∧ CheckRegs s₂ t₂

theorem check_pub {s₁ s₂ t₁ t₂ : State} (A₁ : KeyABI s₁) (A₂ : KeyABI s₂) (e : pubOf s₁ = pubOf s₂)
    (hk : (rInput s₁).key = (rInput s₂).key) (h₁ : RReady s₁ t₁) (h₂ : RReady s₂ t₂) (C₁ : CheckRegs s₁ t₁)
    (C₂ : CheckRegs s₂ t₂) :
    checkArm.pub (callEntryOf (checkRd s₁) (checkWr s₁) t₁) (callEntryOf (checkRd s₂) (checkWr s₂) t₂) := by
  refine ⟨pushed_sp_eq e h₁ h₂ _ _ _ _, ?_, by rw [cc_r0 C₁, cc_r0 C₂, pub_r3 e],
    by rw [cc_r1 C₁, cc_r1 C₂, pub_arg e 0 (by decide)], by rw [cc_r2 C₁, cc_r2 C₂, pub_arg e 1 (by decide)],
    by rw [cc_r3 C₁, cc_r3 C₂, pub_arg e 2 (by decide)], fun i hi => ?_⟩
  · unfold checkParams
    rw [cc_r0 C₁, cc_r0 C₂, cc_r1 C₁, cc_r1 C₂, params_call A₁ h₁, params_call A₂ h₂, hk]
  · show stackArg _ i = stackArg _ i
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega_using [hi]
    · rw [cc_a0 A₁ h₁ C₁, cc_a0 A₂ h₂ C₂, pub_arg e 5 (by decide)]
    · rw [cc_a1 A₁ h₁ C₁, cc_a1 A₂ h₂ C₂, pub_arg e 6 (by decide)]

theorem checkCall_ct (name : String) : RelCT isa CheckRel (callWith name (Generate.checkParameters umaal))
    fun _ _ => True := by
  unfold callWith
  refine RelCT.frame (fun t₁ t₂ ⟨s₁, s₂, _, _, e, _, h₁, h₂, _⟩ => by rw [h₁.sp, h₂.sp, pub_sp e]) ?_
  intro a b ta tb a' b' hp ea eb
  obtain ⟨t₁, t₂, ⟨s₁, s₂, A₁, A₂, e, hk, h₁, h₂, C₁, C₂⟩, p₁, p₂⟩ := hp
  rw [push_pushed (by decide) (call_sp_le A₁ h₁), Option.some.injEq] at p₁
  rw [push_pushed (by decide) (call_sp_le A₂ h₂), Option.some.injEq] at p₂
  subst p₁ p₂
  refine RelCT.call (P := fun x y => x = pushed callPush t₁ ∧ y = pushed callPush t₂) (k := checkArm)
    (fun s hs => let ⟨t, s', e, ha, hp⟩ := check_correct hs; ⟨t, s', e, ha, hp⟩) check_constantTime
    (checkRd s₁) (checkWr s₁) (fun _ _ ⟨r₁, r₂⟩ => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ ea eb
  subst r₁ r₂
  obtain ⟨c₁, w₁⟩ := check_covers A₁ h₁
  obtain ⟨c₂, w₂⟩ := check_covers A₂ h₂
  have p₂ : checkArm.pre (callEntryOf (checkRd s₂) (checkWr s₂) t₂) := check_call_pre A₂ h₂ C₂
  have pb := check_pub A₁ A₂ e hk h₁ h₂ C₁ C₂
  rw [← pub_checkRd e, ← pub_checkWr e] at p₂ c₂ pb
  rw [← pub_checkWr e] at w₂
  exact ⟨check_call_pre A₁ h₁ C₁, p₂, pb, c₁, w₁, c₂, w₂⟩

/-! ## The derivation -/

/-- Two runs about to call the derivation alike, with the same status, their
domains checked. -/
def DeriveRel (t₁ t₂ : State) : Prop :=
  ∃ s₁ s₂, KeyABI s₁ ∧ KeyABI s₂ ∧ pubOf s₁ = pubOf s₂ ∧ (rInput s₁).key = (rInput s₂).key ∧
    RReady s₁ t₁ ∧ RReady s₂ t₂ ∧ DeriveRegs s₁ t₁ ∧ DeriveRegs s₂ t₂ ∧
    Spec.Dsa.signStatus (deriveResult s₁ t₁) = Spec.Dsa.signStatus (deriveResult s₂ t₂) ∧
    Spec.Dsa.checkParametersBytes (rInput s₁).pLen (rInput s₁).qLen (rInput s₁).key = true ∧
    Spec.Dsa.checkParametersBytes (rInput s₂).pLen (rInput s₂).qLen (rInput s₂).key = true

theorem derive_pub {s₁ s₂ t₁ t₂ : State} (A₁ : KeyABI s₁) (A₂ : KeyABI s₂) (e : pubOf s₁ = pubOf s₂)
    (hk : (rInput s₁).key = (rInput s₂).key) (h₁ : RReady s₁ t₁) (h₂ : RReady s₂ t₂) (C₁ : DeriveRegs s₁ t₁)
    (C₂ : DeriveRegs s₂ t₂)
    (hr : Spec.Dsa.signStatus (deriveResult s₁ t₁) = Spec.Dsa.signStatus (deriveResult s₂ t₂)) :
    deriveArm.pub (callEntryOf (deriveRd s₁) (deriveWr s₁) t₁)
      (callEntryOf (deriveRd s₂) (deriveWr s₂) t₂) := by
  refine ⟨pushed_sp_eq e h₁ h₂ _ _ _ _, ?_, by rw [dc_r0 C₁, dc_r0 C₂, pub_r0 e],
    by rw [dc_r1 C₁, dc_r1 C₂, pub_r1 e], by rw [dc_r2 C₁, dc_r2 C₂, pub_r3 e],
    by rw [dc_r3 C₁, dc_r3 C₂, pub_arg e 0 (by decide)], fun i hi => ?_⟩
  · unfold deriveLeak
    rw [deriveRes_call A₁ h₁ C₁, deriveRes_call A₂ h₂ C₂, hr]
    unfold deriveParams
    rw [dc_r2 C₁, dc_r2 C₂, dc_r3 C₁, dc_r3 C₂, params_call A₁ h₁, params_call A₂ h₂, hk]
  · show stackArg _ i = stackArg _ i
    obtain rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega_using [hi]
    · rw [dc_a0 A₁ h₁ C₁, dc_a0 A₂ h₂ C₂, pub_arg e 1 (by decide)]
    · exact addr_inj32 (by rw [dc_a1 A₁ h₁ C₁, dc_a1 A₂ h₂ C₂, pub_rBase e])
    · rw [dc_a2 A₁ h₁ C₁, dc_a2 A₂ h₂ C₂, pub_arg e 2 (by decide)]
    · rw [dc_a3 A₁ h₁ C₁, dc_a3 A₂ h₂ C₂, pub_arg e 5 (by decide)]
    · rw [dc_a4 A₁ h₁ C₁, dc_a4 A₂ h₂ C₂, pub_arg e 6 (by decide)]

theorem deriveCall_ct (name : String) : RelCT isa DeriveRel (callWith name (Generate.deriveChecked umaal))
    fun _ _ => True := by
  unfold callWith
  refine RelCT.frame (fun t₁ t₂ ⟨s₁, s₂, _, _, e, _, h₁, h₂, _⟩ => by rw [h₁.sp, h₂.sp, pub_sp e]) ?_
  intro a b ta tb a' b' hp ea eb
  obtain ⟨t₁, t₂, ⟨s₁, s₂, A₁, A₂, e, hk, h₁, h₂, C₁, C₂, hr, hc₁, hc₂⟩, p₁, p₂⟩ := hp
  rw [push_pushed (by decide) (call_sp_le A₁ h₁), Option.some.injEq] at p₁
  rw [push_pushed (by decide) (call_sp_le A₂ h₂), Option.some.injEq] at p₂
  subst p₁ p₂
  refine RelCT.call (P := fun x y => x = pushed callPush t₁ ∧ y = pushed callPush t₂) (k := deriveCheckedArm)
    (fun s hs => let ⟨t, s', e, ha, hp⟩ := deriveChecked_correct hs; ⟨t, s', e, ha, hp⟩) deriveChecked_constantTime
    (deriveRd s₁) (deriveWr s₁) (fun _ _ ⟨r₁, r₂⟩ => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ ea eb
  subst r₁ r₂
  obtain ⟨c₁, w₁⟩ := derive_covers A₁ h₁
  obtain ⟨c₂, w₂⟩ := derive_covers A₂ h₂
  have p₂ : deriveCheckedArm.pre (callEntryOf (deriveRd s₂) (deriveWr s₂) t₂) :=
    derive_call_checked A₂ h₂ C₂ (by rw [key_bytes A₂ h₂]; exact hc₂)
  have pb := derive_pub A₁ A₂ e hk h₁ h₂ C₁ C₂ hr
  rw [← pub_deriveRd e, ← pub_deriveWr e] at p₂ c₂ pb
  rw [← pub_deriveWr e] at w₂
  exact ⟨derive_call_checked A₁ h₁ C₁ (by rw [key_bytes A₁ h₁]; exact hc₁), p₂, pb, c₁, w₁, c₂, w₂⟩

end VG.Proof.Dsa.Arm.Key

end

end

/-!
# Key generation's body leaks only its public data (32-bit ARM)

The domain is public, so whether it passes the check is (`pub_checked`).
The sampling trace is the generation trace without the derivation's last
entry, 5 or 6, which no sampling trace has (`spl_trace`); it fixes whether
x is found (`BodyPub.ok`), and the generation's status is the derivation's.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Key

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random VG.Impl.Dsa.Arm.GenerateKey
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_cmp op2_imm eval_eq eval_ne)

variable {umaal : Bool}

/-! ## What two runs share -/

/-- A sampling trace has no entry above 4. -/
theorem sample_trace_le (q fuel : Nat) (rand : List Byte) :
    ∀ x ∈ (Spec.Dsa.Random.sample q fuel rand).trace, x ≤ 4 := by
  induction fuel generalizing rand with
  | zero => simp [Spec.Dsa.Random.sample]
  | succ fuel ih =>
    rw [Spec.Dsa.Random.sample]
    split
    · simp
    · dsimp only
      split
      · simp
      · split
        · simp
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · decide
          · exact ih _ x hx

/-- The public data of two runs of the body: the entry's, the domain, and
the generation's status and trace. -/
structure BodyPub where
  pub : Pub
  key : List Byte
  status : Nat
  tr : List Nat

structure BodyFacts (b : BodyPub) (s₀ : State) : Prop where
  key : (rInput s₀).key = b.key
  status : (rResult s₀).status = b.status
  tr : (rResult s₀).trace = b.tr

/-- The sampling trace: the trace without the derivation's entry. -/
def BodyPub.splTr (b : BodyPub) : List Nat := if b.tr.getLast?.any (4 < ·) then b.tr.dropLast else b.tr

/-- Whether sampling finds x. -/
def BodyPub.ok (b : BodyPub) : Bool := b.splTr.getLast? == some 1

theorem pub_checked {s₁ s₂ : State} (e : pubOf s₁ = pubOf s₂) (hk : (rInput s₁).key = (rInput s₂).key) :
    rChecked s₁ = rChecked s₂ := by
  have hp : (rInput s₁).pLen = (rInput s₂).pLen := congrArg BitVec.toNat (pub_arg e 1 (by decide))
  have hq : (rInput s₁).qLen = (rInput s₂).qLen := congrArg BitVec.toNat (pub_arg e 2 (by decide))
  unfold rChecked; rw [hp, hq, hk]

theorem splTr_append (tr : List Nat) {c : Nat} (hc : 4 < c) :
    (if (tr ++ [c]).getLast?.any (4 < ·) then (tr ++ [c]).dropLast else tr ++ [c]) = tr := by
  simp [hc]

theorem spl_trace {b : BodyPub} {s₀ : State} (A : KeyABI s₀) (F : BodyFacts b s₀) (hc : rChecked s₀ = true) :
    (spl s₀ 128 0).trace = b.splTr := by
  have hR := rResult_eq A
  rw [ite_eq_left hc] at hR
  have ht := F.tr
  unfold BodyPub.splTr
  rw [← ht, hR]
  cases hk : (spl s₀ 128 0).scalar with
  | none =>
    dsimp only
    have h4 : (spl s₀ 128 0).trace.getLast?.any (4 < ·) = false := by
      cases hl : (spl s₀ 128 0).trace.getLast? with
      | none => rfl
      | some x =>
        have := sample_trace_le _ _ _ x (List.mem_of_getLast? hl)
        simp only [Option.any_some, decide_eq_false_iff_not]; omega_using [this]
    rw [h4]; rfl
  | some x =>
    dsimp only
    exact (splTr_append _ (by split <;> decide)).symm

theorem spl_ok {b : BodyPub} {s₀ : State} (A : KeyABI s₀) (F : BodyFacts b s₀) (hc : rChecked s₀ = true) :
    decide (VG.Proof.Dsa.Random.sampleStatus (spl s₀ 128 0) = 1) = b.ok := by
  unfold BodyPub.ok
  have hs : (spl s₀ 128 0).scalar.isSome = ((spl s₀ 128 0).trace.getLast? == some 1) :=
    (VG.Proof.Dsa.Random.sample_trace_result _ _ _).2
  rw [← spl_trace A F hc, ← hs]
  cases hk : (spl s₀ 128 0).scalar with
  | none => rw [decide_eq_false (sampleStatus_none hk)]; rfl
  | some k => rw [decide_eq_true (sampleStatus_some hk)]; rfl

/-! ## The entry -/

/-- The body's entry, after the frame's allocation. -/
def BodyEntry (b : BodyPub) (s₀ t : State) : Prop := BodyFacts b s₀ ∧ t = allocated frameBytes s₀

/-- After the entry's first instruction, which puts the frame's base in `r12`. -/
def entryBase (s₀ : State) : State :=
  (allocated frameBytes s₀).setReg .r12 ((allocated frameBytes s₀).sp + BitVec.ofNat 32 0)

def Based (b : BodyPub) (s₀ t : State) : Prop := BodyFacts b s₀ ∧ t = entryBase s₀

/-- Between the calls: the saved words, and the counts. -/
structure Kept (b : BodyPub) (s₀ t : State) : Prop where
  facts : BodyFacts b s₀
  ready : RReady s₀ t
  saved : Saved s₀ t.mem
  used : slot t.mem (rBase s₀) oUsed = 0
  status : slot t.mem (rBase s₀) oStatus = 0

theorem Kept.fupd {b : BodyPub} {s₀ t u : State} (h : Kept b s₀ t) (f : Fupd t u) : Kept b s₀ u := by
  have hm : u.mem = t.mem := f.mem
  exact ⟨h.facts, h.ready.fupd f, by rw [hm]; exact h.saved, by rw [hm]; exact h.used, by rw [hm]; exact h.status⟩

theorem exec_entryBase (s₀ : State) : isa.exec (.addSp .r12 0) (allocated frameBytes s₀) = some (entryBase s₀) := by
  simp [exec, entryBase]

theorem entryRest_ok {s₀ : State} (A : KeyABI s₀) :
    WP isa (.block entry.tail) (entryBase s₀) fun u => RReady s₀ u ∧ Saved s₀ u.mem ∧
      slot u.mem (rBase s₀) oUsed = 0 ∧ slot u.mem (rBase s₀) oStatus = 0 := by
  have h := entry_ok A
  rw [show entry = .addSp .r12 0 :: entry.tail from rfl, WP.block_cons_iff] at h
  obtain ⟨s', hs, W⟩ := h
  rw [exec_entryBase, Option.some.injEq] at hs
  subst hs
  exact WP.mono W fun u ⟨a, b, c, d, _⟩ => ⟨a, b, c, d⟩

theorem entryBase_r12 (s₀ : State) : (entryBase s₀).gpr .r12 = s₀.sp - BitVec.ofNat 32 frameBytes := by
  simp [entryBase, State.setReg, allocated]

theorem entry_ct : RelCT isa (Two fun b => At (BodyEntry b) b.pub) (.block entry) (Two fun b => At (Kept b) b.pub) := by
  rw [show entry = [.addSp .r12 0] ++ entry.tail from rfl]
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := fun b => At (Based b) b.pub) []
    (fun _ _ _ _ _ _ h => by cases h) (by taint_decide) fun b t ⟨s₀, A, e, Fb, ht⟩ => ?_)
    (two_piece [.r12] (fun b t₁ t₂ ⟨s₁, _, e₁, _, h₁⟩ ⟨s₂, _, e₂, _, h₂⟩ r hr => ?_) (by taint_decide)
      fun b t ⟨s₀, A, e, Fb, ht⟩ => ?_))
  · subst ht
    exact VG.Proof.X25519.Arm.WP.cons (exec_entryBase s₀) (WP.block_nil ⟨s₀, A, e, Fb, rfl⟩)
  · rw [List.mem_singleton] at hr; subst hr h₁ h₂
    rw [entryBase_r12, entryBase_r12, pub_sp (e₁.trans e₂.symm)]
  · subst ht
    exact WP.mono (entryRest_ok A) fun u ⟨h, sv, us, st⟩ => ⟨s₀, A, e, Fb, h, sv, us, st⟩

/-! ## The domain check -/

def CheckIn (b : BodyPub) (s₀ t : State) : Prop := Kept b s₀ t ∧ CheckRegs s₀ t

/-- After the check. -/
def Checked (b : BodyPub) (s₀ t : State) : Prop :=
  Kept b s₀ t ∧ t.gpr .r0 = if rChecked s₀ then 1 else 0

theorem checked_ok (name : String) {b : BodyPub} {s₀ t : State} (A : KeyABI s₀) (C : CheckIn b s₀ t) :
    WP isa (callWith name (Generate.checkParameters umaal)) t (Checked b s₀) := by
  obtain ⟨K, R⟩ := C
  refine WP.mono (callCheck_ok A K.ready R name) fun u ⟨h, f, _, r0⟩ => ?_
  have sl : ∀ d, d + 4 ≤ frameBytes → slot u.mem (rBase s₀) d = slot t.mem (rBase s₀) d := fun d hd =>
    slot_keep f (check_keeps A) hd
  have hck : checkResult s₀ t = rChecked s₀ := by
    unfold checkResult; rw [key_bytes A K.ready]; rfl
  rw [hck] at r0
  exact ⟨⟨K.facts, h, K.saved.of_slots fun d _ hd => sl d hd, by rw [sl _ (by decide)]; exact K.used,
    by rw [sl _ (by decide)]; exact K.status⟩, r0⟩

/-- After the test of the check. -/
def Tested (b : BodyPub) (s₀ t : State) : Prop := Kept b s₀ t ∧ t.z = !rChecked s₀

/-- An unchecked domain: the end. -/
theorem unchecked_fin {b : BodyPub} {s₀ t : State} (A : KeyABI s₀) (T : Tested b s₀ t) (hc : rChecked s₀ = false) :
    RFin s₀ t ∧ (rResult s₀).status = b.status := by
  obtain ⟨K, _⟩ := T
  have hR := rResult_unchecked A hc
  exact ⟨⟨K.ready, by rw [K.used, hR]; rfl, by rw [K.status, hR]; rfl, fun e => by rw [hR] at e; exact absurd e (by decide),
    K.saved⟩, K.facts.status⟩

/-! ## Sampling -/

/-- After `prepare`. -/
def Prepped (b : BodyPub) (s₀ t : State) : Prop :=
  BodyFacts b s₀ ∧ rChecked s₀ = true ∧ Smp s₀ 0 (slot t.mem (rBase s₀) oDraws).toNat t ∧ Saved s₀ t.mem

theorem prepped_ok {b : BodyPub} {s₀ t : State} (A : KeyABI s₀) (T : Tested b s₀ t) (hc : rChecked s₀ = true) :
    WP isa prepare t (Prepped b s₀) := by
  obtain ⟨K, _⟩ := T
  have hq := rq_of_checked A hc
  have hql := rQBytes_le A
  have hfit := rWidth_le s₀
  refine WP.mono (prepare_ok A K.ready K.saved.2.2.2.2) fun t₅ ⟨_, P₅, h₅, o₅, _⟩ => ?_
  have P := P₅ hq
  have lo₅ : ∀ d, d + 4 ≤ oQ → slot t₅.mem (rBase s₀) d = slot t.mem (rBase s₀) d := fun d hd =>
    outs_low o₅ (by decide) hd (by unfold oQ at hd; omega_using [hd])
  have us₅ : slot t₅.mem (rBase s₀) oUsed = BitVec.ofNat 32 0 := by
    rw [lo₅ _ (by decide)]; exact K.used
  exact ⟨K.facts, hc, ⟨h₅, P.q, P.width, P.mask, us₅, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq],
    fun i hi => P.nonce i (by omega_using [hql, hi]), Nat.zero_le _⟩, K.saved.of_outs o₅ (by decide)⟩

/-- After sampling. -/
structure Sampled (b : BodyPub) (s₀ t : State) : Prop where
  facts : BodyFacts b s₀
  checked : rChecked s₀ = true
  out : SampleOut s₀ 0 (spl s₀ 128 0) t
  r0 : t.gpr .r0 = BitVec.ofNat 32 (VG.Proof.Dsa.Random.sampleStatus (spl s₀ 128 0))
  ready : RReady s₀ t
  saved : Saved s₀ t.mem

theorem sampled_ok {b : BodyPub} {s₀ t : State} (A : KeyABI s₀) (P : Prepped b s₀ t) :
    WP isa KeyRandom.sample t (Sampled b s₀) := by
  obtain ⟨F, hc, S, sv⟩ := P
  exact WP.mono (sample_ok A S (rq_of_checked A hc)) fun u ⟨O, r0, h, o, _⟩ =>
    ⟨F, hc, O, r0, h, sv.of_outs o (by decide)⟩

/-- After the test of the sampling's status. -/
def SampleTested (b : BodyPub) (s₀ t : State) : Prop := Sampled b s₀ t ∧ t.z = b.ok

theorem Sampled.fupd {b : BodyPub} {s₀ t u : State} (A : KeyABI s₀) (h : Sampled b s₀ t) (f : Fupd t u) :
    Sampled b s₀ u :=
  ⟨h.facts, h.checked, h.out.mem A (h.ready.fupd f) f.mem, by rw [f.gpr]; exact h.r0, h.ready.fupd f,
    by rw [f.mem]; exact h.saved⟩

/-- No x: the end. -/
theorem rejected_fin {b : BodyPub} {s₀ t : State} (A : KeyABI s₀) (T : SampleTested b s₀ t) (hb : b.ok = false) :
    RFin s₀ t ∧ (rResult s₀).status = b.status := by
  obtain ⟨S, _⟩ := T
  have hR := rResult_eq A
  simp only [S.checked, ↓reduceIte] at hR
  have hn : VG.Proof.Dsa.Random.sampleStatus (spl s₀ 128 0) ≠ 1 := by
    have := spl_ok A S.facts S.checked; rw [hb] at this; simpa using this
  cases hk : (spl s₀ 128 0).scalar with
  | some k => exact absurd (sampleStatus_some hk) hn
  | none =>
    simp only [hk] at hR
    obtain ⟨d, Sm⟩ := S.out.smp
    refine ⟨⟨S.ready, ?_, ?_, fun e => by rw [hR] at e; exact absurd e hn, S.saved⟩, S.facts.status⟩
    · rw [Sm.usedW, hR]; simp
    · rw [S.out.status, hR]

/-! ## The derivation -/

/-- With x, before the derivation's call. -/
structure DeriveIn (b : BodyPub) (s₀ t : State) : Prop where
  facts : BodyFacts b s₀
  checked : rChecked s₀ = true
  ready : RReady s₀ t
  regs : DeriveRegs s₀ t
  x : ∃ k, (spl s₀ 128 0).scalar = some k ∧ deriveResult s₀ t =
    Spec.Dsa.deriveKeyBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key (Spec.Dsa.encodeBE (rInput s₀).qLen k)
  used : slot t.mem (rBase s₀) oUsed = BitVec.ofNat 32 (spl s₀ 128 0).used
  saved : Saved s₀ t.mem

theorem deriveIn_ok {b : BodyPub} {s₀ t : State} (A : KeyABI s₀) (T : SampleTested b s₀ t) (hb : b.ok = true) :
    WP isa (.block deriveArgs) t (DeriveIn b s₀) := by
  obtain ⟨S, _⟩ := T
  have hqn := rQBytes_length A
  have h1 : VG.Proof.Dsa.Random.sampleStatus (spl s₀ 128 0) = 1 := by
    have := spl_ok A S.facts S.checked; rw [hb] at this; simpa using this
  obtain ⟨k, hk⟩ : ∃ k, (spl s₀ 128 0).scalar = some k := by
    cases hk : (spl s₀ 128 0).scalar with
    | none => exact absurd h1 (sampleStatus_none hk)
    | some k => exact ⟨k, rfl⟩
  obtain ⟨d, Sm⟩ := S.out.smp
  refine WP.mono (deriveArgs_ok A S.ready S.saved) fun u ⟨h, m, C, _⟩ => ⟨S.facts, S.checked, h, C, ⟨k, hk, ?_⟩,
    by rw [m, Sm.usedW, Nat.zero_add], by rw [m]; exact S.saved⟩
  unfold deriveResult
  rw [key_bytes A h, m, ← hqn, S.out.nonce k hk, hqn]
  rfl

theorem DeriveIn.status {b : BodyPub} {s₀ t : State} (A : KeyABI s₀) (D : DeriveIn b s₀ t) :
    Spec.Dsa.signStatus (deriveResult s₀ t) = b.status := by
  obtain ⟨k, hk, hr⟩ := D.x
  have hR := rResult_eq A
  simp only [D.checked, ↓reduceIte, hk] at hR
  rw [hr, ← D.facts.status, hR]

/-- After the derivation's call. -/
structure Derived (b : BodyPub) (s₀ t : State) : Prop where
  facts : BodyFacts b s₀
  ready : RReady s₀ t
  r0 : t.gpr .r0 = BitVec.ofNat 32 (rResult s₀).status
  out : Spec.Rsa.bytesAt t.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat =
    (rResult s₀).key.getD (List.replicate (s₀.gpr .r1).toNat 0)
  used : slot t.mem (rBase s₀) oUsed = BitVec.ofNat 32 (rResult s₀).used
  saved : Saved s₀ t.mem

theorem derived_ok (name : String) {b : BodyPub} {s₀ t : State} (A : KeyABI s₀) (D : DeriveIn b s₀ t) :
    WP isa (callWith name (Generate.deriveChecked umaal)) t (Derived b s₀) := by
  obtain ⟨k, hk, hres⟩ := D.x
  have hR := rResult_eq A
  simp only [D.checked, ↓reduceIte, hk] at hR
  refine WP.mono (callDerive_ok A D.ready D.regs name (by rw [key_bytes A D.ready]; exact D.checked))
    fun u ⟨h, f, _, r0, out⟩ => ?_
  rw [hres] at r0 out
  have sl : ∀ d, d + 4 ≤ frameBytes → slot u.mem (rBase s₀) d = slot t.mem (rBase s₀) d := fun d hd =>
    slot_keep f (derive_keeps A) hd
  exact ⟨D.facts, h, by rw [r0, hR], by rw [out, hR], by rw [sl _ (by decide), D.used, hR],
    D.saved.of_slots fun d _ hd => sl d hd⟩

theorem stored_fin {b : BodyPub} {s₀ t : State} (A : KeyABI s₀) (D : Derived b s₀ t) :
    WP isa (.block [st .r0 oStatus]) t fun u => RFin s₀ u ∧ (rResult s₀).status = b.status := by
  refine wp_st D.ready (by decide) fun u mm hu => WP.block_nil ?_
  have mem : u.mem = t.mem.writeW (off (rBase s₀) oStatus) (t.gpr .r0) := mm.mem
  refine ⟨⟨hu, ?_, ?_, fun _ => ?_, ?_⟩, D.facts.status⟩
  · rw [mem, slot_write_ne _ _ _ (by decide) (by decide) (by decide), D.used]
  · rw [mem, slot_write_self, D.r0]
  · rw [mem, rBytes_frame (frame_store s₀ t.mem (by decide) _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact A.stackOut.symm)
      (by have := (s₀.gpr .r1).isLt; omega_using []), D.out]
  · exact D.saved.of_slots fun d hd hd' => by
      rw [mem, slot_write_ne _ _ _ (by unfold oStatus; omega_using [hd]) (by omega_using [hd']) (by decide)]

/-! ## The pieces' constant time -/

/-- The end of a branch, with its status. -/
theorem fin_two {Φ : BodyPub → State → Prop} {c : Prog isa}
    (h : RelCT isa (Two Φ) c (Two fun (b : BodyPub) => At (fun s₀ t => RFin s₀ t ∧ (rResult s₀).status = b.status) b.pub)) :
    RelCT isa (Two Φ) c (Two FinAt) :=
  h.mono (fun _ _ h => h) fun _ _ ⟨(b : BodyPub), h₁, h₂⟩ => ⟨(b.pub, b.status), h₁, h₂⟩

theorem derived_ct (name : String) :
    RelCT isa (Two fun b s => At (SampleTested b) b.pub s ∧ isa.eval .eq s = some true)
      (.seq (.block deriveArgs) (.seq (callWith name (Generate.deriveChecked umaal)) (.block [st .r0 oStatus])))
      (Two FinAt) := by
  refine RelCT.seq (two_piece (Ψ := fun b => At (DeriveIn b) b.pub) [.r11]
    (pins_at' BodyPub.pub fun _ _ _ h => h.1.ready) (by taint_decide)
    fun b t ⟨⟨s₀, A, e, T⟩, hb⟩ => WP.mono (deriveIn_ok A T (by
      rw [eval_eq, T.2, Option.some.injEq] at hb; exact hb)) fun u hu => ⟨s₀, A, e, hu⟩) ?_
  refine RelCT.seq (two_post (Ψ := fun b => At (Derived b) b.pub)
    ((deriveCall_ct name).mono (fun t₁ t₂ ⟨_, ⟨s₁, A₁, e₁, D₁⟩, ⟨s₂, A₂, e₂, D₂⟩⟩ =>
      ⟨s₁, s₂, A₁, A₂, e₁.trans e₂.symm, D₁.facts.key.trans D₂.facts.key.symm, D₁.ready, D₂.ready,
        D₁.regs, D₂.regs, by rw [D₁.status A₁, D₂.status A₂], D₁.checked, D₂.checked⟩) fun _ _ h => h)
    fun b t ⟨s₀, A, e, D⟩ => WP.mono (derived_ok name A D) fun u hu => ⟨s₀, A, e, hu⟩) ?_
  exact fin_two (two_piece [.r11] (pins_at BodyPub.pub fun _ _ _ h => h.ready) (by taint_decide)
    fun b t ⟨s₀, A, e, D⟩ => WP.mono (stored_fin A D) fun u hu => ⟨s₀, A, e, hu⟩)

theorem rejected_ct : RelCT isa (Two fun b s => At (SampleTested b) b.pub s ∧ isa.eval .eq s = some false)
    (.block []) (Two FinAt) :=
  fin_two (two_post (two_taint [] (fun _ _ _ _ _ _ h => by cases h) (by taint_decide))
    fun b t ⟨⟨s₀, A, e, T⟩, hb⟩ => WP.block_nil ⟨s₀, A, e, rejected_fin A T (by
      rw [eval_eq, T.2, Option.some.injEq] at hb; exact hb)⟩)

theorem generate_ct (name : String) :
    RelCT isa (Two fun b s => At (Tested b) b.pub s ∧ isa.eval .eq s = some false)
      (generate name (Generate.deriveChecked umaal)) (Two FinAt) := by
  unfold generate derived
  refine RelCT.seq (two_post (Ψ := fun b => At (Prepped b) b.pub)
    (two_map BodyPub.pub (fun b t ⟨⟨s₀, A, e, K, _⟩, _⟩ => ⟨s₀, A, e, K.ready, K.saved.2.2.2.2⟩) prepare_ct)
    fun b t ⟨⟨s₀, A, e, T⟩, hb⟩ => WP.mono (prepped_ok A T (by
      rw [eval_eq, T.2, Option.some.injEq] at hb; simpa using hb)) fun u hu => ⟨s₀, A, e, hu⟩) ?_
  refine RelCT.seq (two_post (Ψ := fun b => At (Sampled b) b.pub)
    (two_map (fun b => (⟨b.pub, 0, b.splTr⟩ : SmpPub))
      (fun b t ⟨s₀, A, e, F, hc, S, _⟩ => ⟨s₀, A, e, ⟨_, S⟩, rq_of_checked A hc, spl_trace A F hc⟩) sample_ct)
    fun b t ⟨s₀, A, e, P⟩ => WP.mono (sampled_ok A P) fun u hu => ⟨s₀, A, e, hu⟩) ?_
  refine RelCT.seq (two_piece (Ψ := fun b => At (SampleTested b) b.pub) []
    (fun _ _ _ _ _ _ h => by cases h) (by taint_decide)
    fun b t ⟨s₀, A, e, S⟩ => wp_cmp (op2_imm (by decide)) fun u fu z =>
      WP.block_nil ⟨s₀, A, e, S.fupd A fu, ?_⟩) ?_
  · have hle := sampleStatus_le (spl s₀ 128 0)
    rw [z, S.r0, one_beq (by omega_using [hle]), spl_ok A S.facts S.checked]
  exact two_ite (fun b t₁ t₂ ⟨_, _, _, _, z₁⟩ ⟨_, _, _, _, z₂⟩ => by rw [eval_eq, eval_eq, z₁, z₂])
    (derived_ct name) rejected_ct

theorem body_ct (check derive : String) :
    RelCT isa (Two fun b => At (BodyEntry b) b.pub)
      (body check derive (Generate.checkParameters umaal) (Generate.deriveChecked umaal)) fun _ _ => True := by
  unfold body
  refine RelCT.seq entry_ct ?_
  refine RelCT.seq (two_piece (Ψ := fun b => At (CheckIn b) b.pub) [.r11]
    (pins_at BodyPub.pub fun _ _ _ h => h.ready) (by taint_decide)
    fun b t ⟨s₀, A, e, K⟩ => WP.mono (checkArgs_ok A K.ready K.saved) fun u ⟨h, m, C, _⟩ =>
      ⟨s₀, A, e, ⟨K.facts, h, by rw [m]; exact K.saved, by rw [m]; exact K.used, by rw [m]; exact K.status⟩,
        C⟩) ?_
  refine RelCT.seq (two_post (Ψ := fun b => At (Checked b) b.pub)
    ((checkCall_ct check).mono (fun t₁ t₂ ⟨_, ⟨s₁, A₁, e₁, K₁, C₁⟩, ⟨s₂, A₂, e₂, K₂, C₂⟩⟩ =>
      ⟨s₁, s₂, A₁, A₂, e₁.trans e₂.symm, K₁.facts.key.trans K₂.facts.key.symm, K₁.ready, K₂.ready, C₁, C₂⟩)
      fun _ _ h => h)
    fun b t ⟨s₀, A, e, C⟩ => WP.mono (checked_ok check A C) fun u hu => ⟨s₀, A, e, hu⟩) ?_
  refine RelCT.seq (two_piece (Ψ := fun b => At (Tested b) b.pub) []
    (fun _ _ _ _ _ _ h => by cases h) (by taint_decide)
    fun b t ⟨s₀, A, e, K, r0⟩ => wp_cmp0 fun u f z => WP.block_nil ⟨s₀, A, e, K.fupd f, ?_⟩) ?_
  · rw [z, r0]; cases rChecked s₀ <;> rfl
  refine RelCT.seq (R := Two FinAt) (two_ite (fun b t₁ t₂ ⟨s₁, _, e₁, K₁, z₁⟩ ⟨s₂, _, e₂, K₂, z₂⟩ => by
    rw [eval_eq, eval_eq, z₁, z₂, pub_checked (e₁.trans e₂.symm) (K₁.facts.key.trans K₂.facts.key.symm)])
    ?_ (generate_ct derive)) finish_ct
  exact fin_two (two_post (two_taint [] (fun _ _ _ _ _ _ h => by cases h) (by taint_decide))
    fun b t ⟨⟨s₀, A, e, T⟩, hb⟩ => WP.block_nil ⟨s₀, A, e, unchecked_fin A T (by
      rw [eval_eq, T.2, Option.some.injEq] at hb; simpa using hb)⟩)

end VG.Proof.Dsa.Arm.Key

end

end

/-! ### `Dsa.Arm.Key.CT`, which only this module used -/

section

/-!
# DSA key generation is constant time (32-bit ARM)

The contract's public data (the arguments, the domain, the status, the
consumption and the trace) gives two entries the same `BodyPub`, and the
frame's allocation leaks nothing.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Key

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random VG.Impl.Dsa.Arm.GenerateKey

variable {umaal : Bool}

/-- Two entries with the same public data: the same arguments, domain,
status and trace. -/
theorem key_public {s t : State} (H : (Spec.Dsa.generateKeyContract Arm.abi 144).pub s t) :
    pubOf s = pubOf t ∧ (rInput s).key = (rInput t).key ∧ (rResult s).status = (rResult t).status ∧
      (rResult s).trace = (rResult t).trace := by
  sig_pub [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.stackArgAddr, BitVec.add_zero] at H
  obtain ⟨hsp, hleak, r0, r1, r2, r3, a0, a1, a2, a3, a4, a5, a6⟩ := H
  change (rInput s).key.map (·.toNat) ++ [(rResult s).status, (rResult s).used] ++ (rResult s).trace =
    (rInput t).key.map (·.toNat) ++ [(rResult t).status, (rResult t).used] ++ (rResult t).trace at hleak
  have hlen : ((rInput s).key.map (·.toNat)).length = ((rInput t).key.map (·.toNat)).length := by
    simp only [rInput, List.length_map, rBytes_length, a0]
  rw [List.append_assoc, List.append_assoc] at hleak
  obtain ⟨hk, hrest⟩ := List.append_inj hleak hlen
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at hrest
  obtain ⟨hst, -, htr⟩ := hrest
  have hkey : (rInput s).key = (rInput t).key := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hk
  refine ⟨?_, hkey, hst, htr⟩
  have hargs : ∀ i < 7, stackArg s i = stackArg t i := by
    intro i hi
    have c : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega_using [hi]
    rcases c with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0, a1, a2, a3, a4, a5, a6]
  have hp : (rInput s).pLen = (rInput t).pLen := congrArg BitVec.toNat a1
  have hq : (rInput s).qLen = (rInput t).qLen := congrArg BitVec.toNat a2
  simp only [pubOf, Pub.mk.injEq]
  refine ⟨hsp, by rw [r0, r1, r2, r3], List.map_congr_left fun i hi => hargs i (List.mem_range.mp hi), ?_⟩
  unfold rQBytes
  rw [hkey, hp, hq]

theorem alloc_push {s₀ : State} (A : KeyABI s₀) :
    isa.push (.alloc frameBytes) s₀ = some (allocated frameBytes s₀) := by
  have hsp : frameBytes ≤ s₀.sp.toNat := by have := A.stackLow; unfold frameBytes; omega_using [this]
  have hn : 0 < frameBytes ∧ frameBytes < 4096 ∧ frameBytes % 8 = 0 ∧
      encodable (BitVec.ofNat 32 frameBytes) = true := by decide
  simp only [isa, push, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2, hsp, and_self, ite_true]
  rfl

/-- `vg_dsa_generate_key` leaks only what its contract makes public. -/
theorem generateKey_constantTime (check derive : String) :
    ConstantTime isa (Spec.Dsa.generateKeyContract Arm.abi 144).pre
      (Spec.Dsa.generateKeyContract Arm.abi 144).pub
      (code check derive (Generate.checkParameters umaal) (Generate.deriveChecked umaal)) := by
  intro s t tsa tsb u w hs ht hpub ea eb
  have As := keyABI_of hs
  have At' := keyABI_of ht
  obtain ⟨e, hk, hst, htr⟩ := key_public hpub
  cases ea with
  | frame hap hab _ =>
    cases eb with
    | frame hbp hbb _ =>
      rw [alloc_push As, Option.some.injEq] at hap
      rw [alloc_push At', Option.some.injEq] at hbp
      subst hap hbp
      have hh := body_ct check derive _ _ _ _ _ _
        ⟨⟨pubOf s, (rInput s).key, (rResult s).status, (rResult s).trace⟩,
        ⟨s, As, rfl, ⟨rfl, rfl, rfl⟩, rfl⟩, ⟨t, At', e.symm, ⟨hk.symm, hst.symm, htr.symm⟩, rfl⟩⟩ hab hbb |>.1
      simpa only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] using hh

end VG.Proof.Dsa.Arm.Key

end

end

/-! ### `Dsa.Arm.Key.Correct`, which only this module used -/

section

/-!
# DSA key generation on 32-bit ARM: correctness

`generateKey_correct`: from the shared contract's precondition,
`vg_dsa_generate_key` returns the status of `Spec.Dsa.generateKeyBytes`,
writes its key (or zeros) and publishes its consumption as a 64-bit count,
and restores the registers the ABI preserves.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Key

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random VG.Impl.Dsa.Arm.GenerateKey
open VG.Proof.X25519.Arm (toNat_imm)

variable {umaal : Bool}

theorem rResult_used_le {s₀ : State} (A : KeyABI s₀) : (rResult s₀).used ≤ (rInput s₀).rand.length := by
  rw [rResult_eq A]
  split
  · split
    all_goals
      have := VG.Proof.Dsa.Random.sample_used_le (rq s₀) 128 ((rInput s₀).rand.drop 0)
      simpa [spl] using this
  · exact Nat.zero_le _

theorem code_ok (check derive : String) {s₀ : State} (A : KeyABI s₀) :
    WP isa (code check derive (Generate.checkParameters umaal) (Generate.deriveChecked umaal)) s₀ fun s' =>
      ∃ u m un, Finished s₀ u ∧ Frame [⟨State.addr (s₀.sp - BitVec.ofNat 32 frameBytes), frameBytes⟩] u.mem m ∧
        s' = { freed frameBytes u with mem := m, unknowns := un } :=
  WP.alloc ⟨by decide, by decide, by decide, by decide⟩ (by have := A.stackLow; unfold frameBytes; omega_using [this])
    (WP.mono (body_ok check derive A) fun u hu m un hfl => ⟨u, m, un, hu, hfl, rfl⟩)

/-- `vg_dsa_generate_key` meets its contract. -/
theorem generateKey_correct (check derive : String) (s : State)
    (hpre : (Spec.Dsa.generateKeyContract Arm.abi 144).pre s) :
    ∃ t s', Exec isa (code check derive (Generate.checkParameters umaal) (Generate.deriveChecked umaal)) s t s' ∧
      abiPreserved s s' ∧ (Spec.Dsa.generateKeyContract Arm.abi 144).post s s' := by
  have A := keyABI_of hpre
  obtain ⟨t, s', he, u, m, un, hF, hfl, rfl⟩ := code_ok check derive A
  have fsub : Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 frameBytes), frameBytes⟩ (rStack s) := by
    have := A.stackLow
    rw [FrameStack.addr_sub' (by unfold frameBytes; omega_using [this])]
    exact Offset.sub_below _ (by unfold frameBytes; omega_using []) (by unfold frameBytes; omega_using [])
  have dU : ∀ r ∈ [(⟨State.addr (s.sp - BitVec.ofNat 32 frameBytes), frameBytes⟩ : Region)], (rUsed s).Disjoint r := by
    intro r hr; obtain rfl := List.mem_singleton.mp hr; exact A.stackUsed.symm.sub_right fsub
  have out : Spec.Rsa.bytesAt m (State.addr (s.gpr .r0)) (s.gpr .r1).toNat =
      (rResult s).key.getD (List.replicate (s.gpr .r1).toNat 0) := by
    rw [rBytes_frame hfl (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact A.stackOut.symm.sub_right fsub)
      (by have := (s.gpr .r1).isLt; omega_using [])]
    exact hF.out
  refine ⟨t, _, he, ⟨fun r hr => hF.regs r hr, by
    show u.sp + BitVec.ofNat 32 frameBytes = s.sp
    rw [hF.sp, BitVec.sub_add_cancel]⟩, ?_⟩
  sig_post [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.stackArgAddr, BitVec.add_zero]
  have hle := rResult_status_le A
  have hul : (rResult s).used < 2 ^ 32 := by
    have := rResult_used_le A
    have : (rInput s).rand.length < 2 ^ 32 := by simp only [rInput, rBytes_length]; exact BitVec.isLt _
    omega_arith
  refine ⟨?_, out, ?_⟩
  · rw [BitVec.setWidth_append_eq_right]
    show (u.gpr .r0).toNat = (rResult s).status
    rw [hF.r0, toNat_imm (by omega_using [hle])]
  · show Spec.Rsa.wordsAt m (State.addr (s.gpr .r2)) 1 = [BitVec.ofNat 64 (rResult s).used]
    simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero]
    refine congrArg (· :: []) (BitVec.eq_of_toNat_eq ?_)
    have := word_eq_w32 m (State.addr (s.gpr .r2)) 0
    simp only [Mont.word, w32, off] at this
    show (m.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 0) 64).toNat = _
    rw [this, show (0 + 4 : Nat) = 4 from rfl]
    have lo : (m.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 0) 32) = _ :=
      (hfl.readW (r := rUsed s) (Offset.contains_base _ (by decide) (by decide)) dU (by decide)).trans hF.usedLo
    have hi : (m.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 4) 32) = _ :=
      (hfl.readW (r := rUsed s) (Offset.contains_base _ (by decide) (by decide)) dU (by decide)).trans hF.usedHi
    rw [lo, hi, toNat_imm hul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hul])]
    rfl

end VG.Proof.Dsa.Arm.Key

end

end


/-! # 32-bit ARM DSA key generation meets its contract -/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Key

open VG VG.Arm VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.GenerateKey

variable {umaal : Bool}

/-- A 1024/160 call with an empty tape: the output at `0x1000`, `used` at
`0x7000`, the domain at `0x2000` and the working space at `0x8000`. -/
def generateKeySat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 424 | .r2 => 0x7000 | .r3 => 0x2000 | _ => 0
  sp := 0x20000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x20000 then 0x14 else if a = 0x20001 then 1 else if a = 0x20004 then 0x80
    else if a = 0x20008 then 20 else if a = 0x2000d then 0x50 else if a = 0x20015 then 0x80
    else if a = 0x20019 then 0x24 else 0
  rd := [⟨0x2000, 276⟩, ⟨0x5000, 0⟩, ⟨0x20000, 28⟩]
  wr := [⟨0x1000, 424⟩, ⟨0x7000, 8⟩, ⟨0x8000, 73728⟩]

theorem generateKey_satisfiable : ∃ s, (Spec.Dsa.generateKeyContract Arm.abi 144).pre s := by
  sig_implies_sat [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Arm.stackArgAddr, BitVec.add_zero]
    [generateKeySat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using generateKeySat

theorem generateKey_verified (check derive : String) :
    Verified Arm.target (code check derive (Generate.checkParameters umaal) (Generate.deriveChecked umaal))
      (Spec.Dsa.generateKeyContract Arm.abi 144) :=
  ⟨generateKey_correct check derive, generateKey_constantTime check derive, generateKey_satisfiable⟩

/-- Key generation, calling `vg_dsa_check_parameters` and the internal
`vg_dsa_derive_key_checked`. -/
theorem generating_verified :
    Verified Arm.target (code (Generate.checkName umaal) (Generate.deriveName umaal) (Generate.checkParameters umaal)
      (Generate.deriveChecked umaal)) (Spec.Dsa.generateKeyContract Arm.abi 144) :=
  generateKey_verified _ _

end VG.Proof.Dsa.Arm.Key
