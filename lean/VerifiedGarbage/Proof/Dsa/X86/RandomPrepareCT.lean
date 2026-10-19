module

public import VerifiedGarbage.Proof.Dsa.X86.RandomCTDefs
meta import VerifiedGarbage.Proof.Dsa.X86.RandomCTDefs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86.RandomPrepare
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Random
import VerifiedGarbage.Proof.Dsa.RandomEncoding
import VerifiedGarbage.Proof.Dsa.RandomSign
import VerifiedGarbage.Proof.Dsa.RandomSignResult
import VerifiedGarbage.Proof.Dsa.RandomTrace
import VerifiedGarbage.Proof.Dsa.X86.Bytes
import VerifiedGarbage.Proof.Dsa.X86.CoreSetup
import VerifiedGarbage.Proof.Dsa.X86.EntrySave
import VerifiedGarbage.Proof.Dsa.X86.FetchByte
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Dsa.X86.LoadSlot
import VerifiedGarbage.Proof.Dsa.X86.LocalOperand
import VerifiedGarbage.Proof.Dsa.X86.Moduli
import VerifiedGarbage.Proof.Dsa.X86.RandomAttempt
import VerifiedGarbage.Proof.Dsa.X86.RandomBody
import VerifiedGarbage.Proof.Dsa.X86.RandomCT
import VerifiedGarbage.Proof.Dsa.X86.RandomCallArgs
import VerifiedGarbage.Proof.Dsa.X86.RandomSample
import VerifiedGarbage.Proof.Dsa.X86.RandomSignCorrect
import VerifiedGarbage.Proof.Dsa.X86.Reduce
import VerifiedGarbage.Proof.Dsa.X86.RunBytes
import VerifiedGarbage.Proof.Dsa.X86.SaveArgument
import VerifiedGarbage.Proof.Dsa.X86.StackArgument
import VerifiedGarbage.Proof.Dsa.X86.StageFrame
import VerifiedGarbage.Proof.Dsa.Zero
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Mont.X86.Chain
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Mont.X86.ContextMath
import VerifiedGarbage.Proof.Mont.X86.ContextMul
import VerifiedGarbage.Proof.Mont.X86.DynamicAdd
import VerifiedGarbage.Proof.Mont.X86.DynamicFrame
import VerifiedGarbage.Proof.Mont.X86.DynamicSelect
import VerifiedGarbage.Proof.Mont.X86.ExponentInitMath
import VerifiedGarbage.Proof.Mont.X86.ExponentLoop
import VerifiedGarbage.Proof.Mont.X86.ExponentMask
import VerifiedGarbage.Proof.Mont.X86.ExponentShift
import VerifiedGarbage.Proof.Mont.X86.ExponentStep
import VerifiedGarbage.Proof.Mont.X86.ExponentWord
import VerifiedGarbage.Proof.Mont.X86.Exponentiate
import VerifiedGarbage.Proof.Mont.X86.Inverse
import VerifiedGarbage.Proof.Mont.X86.P256Red
import VerifiedGarbage.Proof.Mont.X86.PowerInit
import VerifiedGarbage.Proof.Mont.X86.PowerLoop
import VerifiedGarbage.Proof.Mont.X86.PowerTwo
import VerifiedGarbage.Proof.Mont.X86.RedRow
import VerifiedGarbage.Proof.Mont.X86.Row
import VerifiedGarbage.Proof.Mont.X86.RowW
import VerifiedGarbage.Proof.Mont.X86.SparseShift
import VerifiedGarbage.Proof.Mont.X86.SparseStep
import VerifiedGarbage.Proof.Mont.X86.Step
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Weierstrass.Words32
import VerifiedGarbage.Proof.Weierstrass.X86.Bytes
import VerifiedGarbage.Proof.Weierstrass.X86.BytesLen
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
import VerifiedGarbage.Proof.Weierstrass.X86.MontRed
meta import VerifiedGarbage.Proof.Dsa.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.Digest
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Dsa.Random
meta import VerifiedGarbage.Proof.Dsa.RandomEncoding
meta import VerifiedGarbage.Proof.Dsa.RandomSign
meta import VerifiedGarbage.Proof.Dsa.RandomSignResult
meta import VerifiedGarbage.Proof.Dsa.RandomTrace
meta import VerifiedGarbage.Proof.Dsa.X86.Bytes
meta import VerifiedGarbage.Proof.Dsa.X86.CoreSetup
meta import VerifiedGarbage.Proof.Dsa.X86.EntrySave
meta import VerifiedGarbage.Proof.Dsa.X86.FetchByte
meta import VerifiedGarbage.Proof.Dsa.X86.Layout
meta import VerifiedGarbage.Proof.Dsa.X86.LoadSlot
meta import VerifiedGarbage.Proof.Dsa.X86.LocalOperand
meta import VerifiedGarbage.Proof.Dsa.X86.Moduli
meta import VerifiedGarbage.Proof.Dsa.X86.RandomAttempt
meta import VerifiedGarbage.Proof.Dsa.X86.RandomBody
meta import VerifiedGarbage.Proof.Dsa.X86.RandomCT
meta import VerifiedGarbage.Proof.Dsa.X86.RandomCallArgs
meta import VerifiedGarbage.Proof.Dsa.X86.RandomPrepare
meta import VerifiedGarbage.Proof.Dsa.X86.RandomSample
meta import VerifiedGarbage.Proof.Dsa.X86.RandomSignCorrect
meta import VerifiedGarbage.Proof.Dsa.X86.Reduce
meta import VerifiedGarbage.Proof.Dsa.X86.RunBytes
meta import VerifiedGarbage.Proof.Dsa.X86.SaveArgument
meta import VerifiedGarbage.Proof.Dsa.X86.StackArgument
meta import VerifiedGarbage.Proof.Dsa.X86.StageFrame
meta import VerifiedGarbage.Proof.Dsa.Zero
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86.Mmx
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Mont.X86.Chain
meta import VerifiedGarbage.Proof.Mont.X86.ContextLayout
meta import VerifiedGarbage.Proof.Mont.X86.ContextMath
meta import VerifiedGarbage.Proof.Mont.X86.ContextMul
meta import VerifiedGarbage.Proof.Mont.X86.DynamicAdd
meta import VerifiedGarbage.Proof.Mont.X86.DynamicFrame
meta import VerifiedGarbage.Proof.Mont.X86.DynamicSelect
meta import VerifiedGarbage.Proof.Mont.X86.ExponentInitMath
meta import VerifiedGarbage.Proof.Mont.X86.ExponentLoop
meta import VerifiedGarbage.Proof.Mont.X86.ExponentMask
meta import VerifiedGarbage.Proof.Mont.X86.ExponentShift
meta import VerifiedGarbage.Proof.Mont.X86.ExponentStep
meta import VerifiedGarbage.Proof.Mont.X86.ExponentWord
meta import VerifiedGarbage.Proof.Mont.X86.Exponentiate
meta import VerifiedGarbage.Proof.Mont.X86.Instr
meta import VerifiedGarbage.Proof.Mont.X86.Inverse
meta import VerifiedGarbage.Proof.Mont.X86.P256Red
meta import VerifiedGarbage.Proof.Mont.X86.PowerInit
meta import VerifiedGarbage.Proof.Mont.X86.PowerLoop
meta import VerifiedGarbage.Proof.Mont.X86.PowerTwo
meta import VerifiedGarbage.Proof.Mont.X86.RedRow
meta import VerifiedGarbage.Proof.Mont.X86.Row
meta import VerifiedGarbage.Proof.Mont.X86.RowW
meta import VerifiedGarbage.Proof.Mont.X86.SparseShift
meta import VerifiedGarbage.Proof.Mont.X86.SparseStep
meta import VerifiedGarbage.Proof.Mont.X86.Step
meta import VerifiedGarbage.Proof.Mont.X86.WordOps
meta import VerifiedGarbage.Proof.RsaPss.Params
meta import VerifiedGarbage.Proof.Weierstrass.Words
meta import VerifiedGarbage.Proof.Weierstrass.Words32
meta import VerifiedGarbage.Proof.Weierstrass.X86.Bytes
meta import VerifiedGarbage.Proof.Weierstrass.X86.BytesLen
meta import VerifiedGarbage.Proof.Weierstrass.X86.Copy
meta import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontRed

/-!
# Preparing leaks only public data (x86)

`prepare` branches on q's bytes, which are public: the scan's registers
after `j` bytes are a function of them (`scanAfter`), so two runs with the
same public data take the same branches.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Random

/-- The scan's pair after its first `j` bytes. -/
def scanAfter (bs : List Byte) : Nat → Nat × Byte
  | 0 => (0, 0)
  | j + 1 => scanNext (scanAfter bs j) (bs.length - j) (bs.getD j 0)

theorem scanAfter_bound (bs : List Byte) (hl : bs.length < 2 ^ 32) :
    ∀ j, (scanAfter bs j).1 < 2 ^ 32 ∧ ((scanAfter bs j).1 = 0 → (scanAfter bs j).2 = 0)
  | 0 => ⟨by simp [scanAfter], fun _ => rfl⟩
  | j + 1 => by
    have ih := scanAfter_bound bs hl j
    unfold scanAfter scanNext
    split
    · rename_i hc
      refine ⟨by simp only; omega, fun e => ?_⟩
      simp only at e
      exfalso; apply hc.2
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    · exact ih

/-- The scan before byte `j`. -/
def ScanAt (j : Nat) (s₀ t : State) : Prop :=
  Ready s₀ t ∧ ScanState t (rQ s₀ + BitVec.ofNat 32 j) ((rQBytes s₀).drop j) (scanAfter (rQBytes s₀) j)

/-- After loading byte `j`. -/
def ScanLoaded (j : Nat) (s₀ t : State) : Prop :=
  ScanAt j s₀ t ∧ t.gpr .eax = ((rQBytes s₀).getD j 0).setWidth 32

theorem scanAt_pins {j : Nat} {a : Pub} {t₁ t₂ : State} (h₁ : At (ScanLoaded j) a t₁) (h₂ : At (ScanLoaded j) a t₂) :
    ∀ r ∈ [Reg.eax, .ebx, .ecx, .edx, .esi], t₁.gpr r = t₂.gpr r := by
  obtain ⟨s₁, -, e₁, ⟨-, S₁⟩, x₁⟩ := h₁
  obtain ⟨s₂, -, e₂, ⟨-, S₂⟩, x₂⟩ := h₂
  have e := e₁.trans e₂.symm
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [x₁, x₂, pub_qBytes e]
  · rw [S₁.ebx, S₂.ebx, pub_qBytes e]
  · rw [S₁.ecx, S₂.ecx, pub_qBytes e]
  · rw [S₁.edx, S₂.edx, pub_qBytes e]
  · rw [S₁.esi, S₂.esi, pub_rQ e]

theorem scanAt_esi {j : Nat} {a : Pub} {t₁ t₂ : State} (h₁ : At (ScanAt j) a t₁) (h₂ : At (ScanAt j) a t₂) :
    t₁.gpr .esi = t₂.gpr .esi := by
  obtain ⟨s₁, -, e₁, -, S₁⟩ := h₁
  obtain ⟨s₂, -, e₂, -, S₂⟩ := h₂
  rw [S₁.esi, S₂.esi, pub_rQ (e₁.trans e₂.symm)]

theorem loadByte_ok {s₀ t : State} {j : Nat} (h : ScanAt j s₀ t) (hj : j < (rQBytes s₀).length) :
    WP isa (.block [.movzx8 .eax (at_ .esi 0)]) t (ScanLoaded j s₀) := by
  obtain ⟨hr, S⟩ := h
  have hb := S.bytes
  have hl : 0 < ((rQBytes s₀).drop j).length := by rw [List.length_drop]; omega
  refine wp_load8 (a := (rQ s₀ + BitVec.ofNat 32 j).setWidth 64 + BitVec.ofNat 64 0)
    (by rw [ea_at0, S.esi, BitVec.add_zero]) (hb.rd 0 hl) fun u v _ _ => WP.block_nil ?_
  have hv := hb.val 0 hl
  simp only [List.getElem_drop, Nat.add_zero] at hv
  rw [hv] at v
  refine ⟨⟨hr.upd v (by decide), ⟨by rw [v.other _ (by decide)]; exact S.esi,
    by rw [v.other _ (by decide)]; exact S.ecx, by rw [v.other _ (by decide)]; exact S.ebx,
    by rw [v.other _ (by decide)]; exact S.edx, hb.congr v.mem v.rd v.wr, S.bound, S.zero⟩⟩, ?_⟩
  rw [v.gpr, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl

theorem scanStep_ok {s₀ t : State} (A : RandomSignABI s₀) {j : Nat} (h : ScanAt j s₀ t)
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
  · simp only [eval, z, Option.map_some]
    congr 1
    by_cases h0 : rest.length = 0 <;> simp [h0] <;> omega
  · rw [hd, show rQ s₀ + BitVec.ofNat 32 (j + 1) = rQ s₀ + BitVec.ofNat 32 j + 1 by
      rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl]
    show ScanState u _ rest (scanNext (scanAfter (rQBytes s₀) j) ((rQBytes s₀).length - j)
      ((rQBytes s₀).getD j 0))
    rw [← hrl, ← hb]; exact S'

/-- Before the scan. -/
def ScanPre (s₀ t : State) : Prop :=
  Ready s₀ t ∧ t.gpr .esi = rQ s₀ ∧ t.gpr .ecx = BitVec.ofNat 32 (rQBytes s₀).length

theorem significant_ct :
    RelCT isa (Two (At ScanPre)) Random.significant (Two fun a => At (ScanAt a.qBytes.length) a) := by
  unfold Random.significant
  refine RelCT.seq (two_piece (Ψ := fun a t => 0 < a.qBytes.length ∧ At (ScanAt 0) a t) []
    (by intro _ _ _ _ _ _ h; cases h) (by taint_decide) ?_) ?_
  · rintro a t ⟨s₀, A, e, hr, hsi, hcx⟩
    have hql := rQBytes_le A
    refine wp_movS rfl fun u₁ v₁ _ => wp_movS rfl fun u₂ v₂ _ => WP.block_nil ?_
    have k₂ : Keeps [.ebx, .edx] t u₂ := (v₁.keeps.mono (by decide)).trans (v₂.keeps.mono (by decide))
    refine ⟨by rw [← e]; exact rQBytes_pos A, s₀, A, e, hr.congr k₂ (by rw [v₂.mem, v₁.mem]; exact Frame.refl _ _),
      ⟨?_, ?_, ?_, ?_, ?_, by simp [scanAfter], fun _ => rfl⟩⟩
    · rw [BitVec.add_zero, k₂.1 _ (by decide)]; exact hsi
    · rw [List.drop_zero, k₂.1 _ (by decide)]; exact hcx
    · rw [v₂.other _ (by decide), v₁.gpr]; rfl
    · rw [v₂.gpr]; rfl
    · rw [BitVec.add_zero, List.drop_zero]
      exact (hr.q A).congr (by rw [v₂.mem, v₁.mem]) (by rw [v₂.rd, v₁.rd]) (by rw [v₂.wr, v₁.wr])
  · refine two_loop (Φ := fun a j => At (ScanAt j) a) (Ψ := fun a => At (ScanAt a.qBytes.length) a)
      (fun a => a.qBytes.length) ?_ ?_
    · unfold significantByte
      refine RelCT.seq (two_piece (Ψ := fun p => At (ScanLoaded p.2) p.1) [.esi]
        (fun p t₁ t₂ h₁ h₂ r hr => by
          rw [List.mem_singleton] at hr; subst hr; exact scanAt_esi h₁.2 h₂.2) (by taint_decide) ?_) ?_
      · rintro ⟨a, j⟩ t ⟨hj, s₀, A, e, h⟩
        subst e
        exact WP.mono (loadByte_ok h hj) fun u hu => ⟨s₀, A, rfl, hu⟩
      · exact two_taint [.eax, .ebx, .ecx, .edx, .esi] (fun p t₁ t₂ h₁ h₂ => scanAt_pins h₁ h₂)
          (by taint_decide)
    · rintro a j t hj ⟨s₀, A, e, h⟩
      subst e
      refine WP.mono (scanStep_ok A h hj) fun u ⟨z, hu⟩ => ⟨z, fun _ => ⟨s₀, A, rfl, hu⟩, fun he => ?_⟩
      have he' : j + 1 = (rQBytes s₀).length := he
      exact ⟨s₀, A, rfl, by show ScanAt (rQBytes s₀).length s₀ u; rw [← he']; exact hu⟩

theorem prepHead_ok {s₀ t : State} (A : RandomSignABI s₀) (h : Ready s₀ t) :
    WP isa (.block (clearNonce ++ ([.mov .esi (.mem (Random.arg aKey)), .alu .add .esi (.mem (Random.arg aPLen)),
      .mov .ecx (.mem (Random.arg aQLen))] : List Instr))) t (ScanPre s₀) := by
  have hqn := rQBytes_length A
  refine clearNonce_ok h.rf fun t₁ _ m₁ k₁ _ => ?_
  have h₁ : Ready s₀ t₁ := h.congr k₁ (by rw [m₁]; exact clearMem_frame s₀ _ 8 (by decide))
  refine wp_movS (h₁.argSrc A (j := 3) (by decide)) fun t₂ u₂ _ => ?_
  have h₂ := h₁.upd u₂ (by decide)
  refine wp_addS (h₂.argSrc A (j := 5) (by decide)) fun t₃ u₃ _ => ?_
  have h₃ := h₂.upd u₃ (by decide)
  refine wp_movS (h₃.argSrc A (j := 6) (by decide)) fun t₄ u₄ _ => WP.block_nil ?_
  exact ⟨h₃.upd u₄ (by decide), by rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr]; rfl,
    by rw [u₄.gpr, hqn, BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩

theorem prepStore_ok {s₀ t : State} (A : RandomSignABI s₀) (h : Ready s₀ t) :
    WP isa (.block [.mov .esi (.mem (Random.arg aKey)), .alu .add .esi (.mem (Random.arg aPLen)),
      .alu .add .esi (.mem (Random.arg aQLen)), .alu .sub .esi (.reg .ebx),
      .store (sp oQ) .esi, .store (sp oWidth) .ebx]) t fun u =>
      Ready s₀ u ∧ u.gpr .ebx = t.gpr .ebx ∧ u.gpr .edx = t.gpr .edx := by
  refine wp_movS (h.argSrc A (j := 3) (by decide)) fun t₁ u₁ _ => ?_
  have h₁ := h.upd u₁ (by decide)
  refine wp_addS (h₁.argSrc A (j := 5) (by decide)) fun t₂ u₂ _ => ?_
  have h₂ := h₁.upd u₂ (by decide)
  refine wp_addS (h₂.argSrc A (j := 6) (by decide)) fun t₃ u₃ _ => ?_
  have h₃ := h₂.upd u₃ (by decide)
  refine wp_subS rfl fun t₄ u₄ _ => ?_
  have h₄ := h₃.upd u₄ (by decide)
  refine wp_slot h₄.rf (by decide) rfl fun t₅ f₅ m₅ g₅ r₅ w₅ _ _ => ?_
  refine wp_slot f₅ (by decide) rfl fun t₆ f₆ m₆ g₆ r₆ w₆ _ _ => WP.block_nil ?_
  have kk : Keeps [.esi] t t₆ := ((((u₁.keeps.trans u₂.keeps).trans u₃.keeps).trans u₄.keeps).trans
    ⟨fun r _ => by rw [g₅], r₅, w₅⟩).trans ⟨fun r _ => by rw [g₆], r₆, w₆⟩
  refine ⟨h.congr kk (by
      rw [m₆, m₅, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
      exact (frame_store s₀ _ (by decide) _).trans (frame_store s₀ _ (by decide) _)),
    kk.1 _ (by decide), kk.1 _ (by decide)⟩

/-- After the scan. -/
def Scanned (s₀ t : State) : Prop :=
  Ready s₀ t ∧ t.gpr .ebx = BitVec.ofNat 32 (scanAfter (rQBytes s₀) (rQBytes s₀).length).1 ∧
    t.gpr .edx = (scanAfter (rQBytes s₀) (rQBytes s₀).length).2.setWidth 32

theorem prepare_ct : RelCT isa (Two (At Ready)) Random.prepare fun _ _ => True := by
  unfold Random.prepare
  refine RelCT.seq (two_piece (Ψ := At ScanPre) [.esp] (pins_esp id (fun _ _ h => h) (fun _ _ _ h => h))
    (by taint_decide) fun a t ⟨s₀, A, e, h⟩ => WP.mono (prepHead_ok A h) fun u hu => ⟨s₀, A, e, hu⟩) ?_
  refine RelCT.seq significant_ct ?_
  refine RelCT.seq (two_piece (Ψ := At Scanned) [.esp]
    (pins_esp id (fun _ _ h => h) (fun _ _ _ h => h.1)) (by taint_decide)
    fun a t ⟨s₀, A, e, h, S⟩ => ?_) ?_
  · subst e
    refine WP.mono (prepStore_ok A h) fun u ⟨hu, bx, dx⟩ => ⟨s₀, A, rfl, hu, ?_, ?_⟩
    · rw [bx]; exact S.ebx
    · rw [dx]; exact S.edx
  · refine two_taint [.esp, .ebx, .edx] (fun a t₁ t₂ h₁ h₂ r hr => ?_) (by taint_decide)
    obtain ⟨s₁, -, e₁, r₁, b₁, d₁⟩ := h₁
    obtain ⟨s₂, -, e₂, r₂, b₂, d₂⟩ := h₂
    have e := e₁.trans e₂.symm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact esp_of_rf r₁.rf (pub_rBase e ▸ r₂.rf)
    · rw [b₁, b₂, pub_qBytes e]
    · rw [d₁, d₂, pub_qBytes e]

end VG.Proof.Dsa.X86
