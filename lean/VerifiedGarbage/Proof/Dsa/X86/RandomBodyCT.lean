module

public import VerifiedGarbage.Proof.Dsa.X86.RandomAttempt
public import VerifiedGarbage.Proof.Dsa.X86.RandomFinish
public import VerifiedGarbage.Proof.Dsa.X86.RandomPrepare
import VerifiedGarbage.Proof.Dsa.X86.RandomBody
import VerifiedGarbage.Proof.Dsa.RandomTraceResult
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Spec.Weierstrass
meta import VerifiedGarbage.Proof.Dsa.X86.RandomAttempt
meta import VerifiedGarbage.Proof.Dsa.X86.RandomFinish
meta import VerifiedGarbage.Proof.Dsa.X86.RandomPrepare
meta import VerifiedGarbage.Proof.Dsa.X86.RandomBody
meta import VerifiedGarbage.Proof.Dsa.RandomTraceResult
meta import VerifiedGarbage.Proof.Mont.X86.Instr
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Impl.Dsa.X86.RandomSign
public import VerifiedGarbage.Proof.Dsa.RandomSignTrace
import VerifiedGarbage.Proof.Dsa.X86.RandomCallArgs
public import VerifiedGarbage.Proof.Dsa.X86.RandomSample
meta import VerifiedGarbage.Impl.Dsa.X86.RandomSign
meta import VerifiedGarbage.Proof.Dsa.RandomSignTrace
meta import VerifiedGarbage.Proof.Dsa.X86.RandomCallArgs
meta import VerifiedGarbage.Proof.Dsa.X86.RandomSample
import Batteries.Logic
meta import Batteries.Logic
import VerifiedGarbage.Proof.Dsa.RandomTrace
meta import VerifiedGarbage.Proof.Dsa.RandomTrace
import VerifiedGarbage.Proof.Dsa.RandomEncoding
meta import VerifiedGarbage.Proof.Dsa.RandomEncoding
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
public import VerifiedGarbage.Impl.Dsa.X86.Random
meta import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
meta import VerifiedGarbage.Impl.Dsa.X86.Random
public import VerifiedGarbage.Proof.Dsa.X86.RandomCandidate
meta import VerifiedGarbage.Proof.Dsa.X86.RandomCandidate

/-! ### `Dsa.X86.RandomCTDefs`, which only this module used -/

section

/-!
# What two runs of the randomized signer share (x86)

`pubOf s₀`: the entry's stack pointer, its thirteen arguments and q's
bytes, which two runs with related entry states share. Everything the code
uses as an address or count is a function of it (`pub_*`). `At P a t`: some
entry state with public data `a` and state `t` satisfy `P`.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Random

/-- The public data of an entry state. -/
structure Pub where
  esp : BitVec 32
  args : List (BitVec 32)
  qBytes : List Byte

def pubOf (s₀ : State) : Pub := ⟨s₀.gpr .esp, (List.range 13).map (X86.arg s₀), rQBytes s₀⟩

/-- Some entry state with public data `a` relates to `t` by `P`. -/
def At (P : State → State → Prop) (a : Pub) (t : State) : Prop :=
  ∃ s₀, RandomSignABI s₀ ∧ pubOf s₀ = a ∧ P s₀ t

section
variable {s₁ s₂ : State} (h : pubOf s₁ = pubOf s₂)
include h

theorem pub_esp : s₁.gpr .esp = s₂.gpr .esp := congrArg Pub.esp h
theorem pub_arg (j : Nat) (hj : j < 13) : X86.arg s₁ j = X86.arg s₂ j := by
  have := congrArg (fun a => a.args[j]?) h
  simpa only [pubOf, List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.some.injEq] using this
theorem pub_qBytes : rQBytes s₁ = rQBytes s₂ := congrArg Pub.qBytes h
theorem pub_rLow : rLow s₁ = rLow s₂ := by rw [rLow, rLow, pub_esp h]
theorem pub_rBase : rBase s₁ = rBase s₂ := by rw [rBase, rBase, pub_rLow h]
theorem pub_rQ : rQ s₁ = rQ s₂ := by rw [rQ, rQ, pub_arg h 3 (by decide), pub_arg h 5 (by decide)]
theorem pub_rWidth : rWidth s₁ = rWidth s₂ := by rw [rWidth, rWidth, pub_qBytes h]
theorem pub_rq : rq s₁ = rq s₂ := by rw [rq, rq, pub_qBytes h]
theorem pub_randLen : (rInput s₁).rand.length = (rInput s₂).rand.length := by
  simp only [rInput, rBytes_length, pub_arg h 10 (by decide)]
end

/-- Two states whose frames have the same base agree on `esp`. -/
theorem esp_of_rf {t₁ t₂ : State} {B : Addr} (h₁ : RF t₁ B) (h₂ : RF t₂ B) : t₁.gpr .esp = t₂.gpr .esp := by
  apply BitVec.eq_of_toNat_eq
  rw [h₁.esp_toNat, h₂.esp_toNat]

theorem At.esp {P : State → State → Prop} (hr : ∀ s₀ t, P s₀ t → Ready s₀ t) {a : Pub} {t₁ t₂ : State}
    (h₁ : At P a t₁) (h₂ : At P a t₂) : t₁.gpr .esp = t₂.gpr .esp := by
  obtain ⟨s₁, -, e₁, p₁⟩ := h₁
  obtain ⟨s₂, -, e₂, p₂⟩ := h₂
  exact esp_of_rf (hr _ _ p₁).rf ((pub_rBase (e₁.trans e₂.symm)) ▸ (hr _ _ p₂).rf)

/-- `esp` is pinned. -/
theorem pins_esp {α : Type} {Φ : α → State → Prop} (f : α → Pub) {P : α → State → State → Prop}
    (hΦ : ∀ a t, Φ a t → At (P a) (f a) t) (hr : ∀ a s₀ t, P a s₀ t → Ready s₀ t) : Pins Φ [.esp] := by
  intro a t₁ t₂ h₁ h₂ r hr'
  rw [List.mem_singleton] at hr'; subst hr'
  exact At.esp (hr a) (hΦ a t₁ h₁) (hΦ a t₂ h₂)

end VG.Proof.Dsa.X86

end

end

/-! ### `Dsa.X86.RandomPrepareCT`, which only this module used -/

section

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
  have hl : 0 < ((rQBytes s₀).drop j).length := by rw [List.length_drop]; omega_using [hj]
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
  · simp only [eval, z, Option.map_some]
    congr 1
    by_cases h0 : rest.length = 0 <;> simp [h0] <;> omega_using [hrl, h0]
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

end

end

/-! ### `Dsa.X86.RandomAttemptCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86.RandomSampleCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86.RandomDrawCT`, which only this module used -/

section

/-! ### `Dsa.X86.RandomCT`, which only this module used -/

section

/-!
# The sampler's secret-byte loops leak nothing (x86)

Only pointers and counts are shared between runs; neither candidate bytes,
the borrow, nor the nonzero accumulator is assumed equal. The leading byte
of q, on which `mask` branches, is public.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Dsa.X86

theorem copyLoop_ct {α : Type} {Φ : α → State → Prop} (h : Pins Φ [.esi, .edx, .ecx]) :
    RelCT isa (Two Φ) (.loop (.block Random.copyByte) .ne) (fun _ _ => True) :=
  two_taint [.esi, .edx, .ecx] h (by taint_decide)

theorem rangeBody_ct {α : Type} {Φ : α → State → Prop} (h : Pins Φ [.esi, .edx, .ecx]) :
    RelCT isa (Two Φ) (.seq (.loop (.block Random.rangeByte) .ne) (.block Random.rangeFinish))
      (fun _ _ => True) :=
  two_taint [.esi, .edx, .ecx] h (by taint_decide)

end VG.Proof.Dsa.X86

end

end

/-!
# A draw leaks only its public bounds and its decision (x86)

Two runs of `draw` with the same public data, consumption and budget, whose
complete draws are both accepted or both rejected (`DrawPub.acc`), take
the same branches and addresses: the candidate's bytes reach neither.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Random

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

/-- `esp` is pinned by a predicate about the frame. -/
theorem pins_at {α : Type} {P : α → State → State → Prop} (f : α → Pub)
    (hr : ∀ a s₀ t, P a s₀ t → Ready s₀ t) : Pins (fun a => At (P a) (f a)) [.esp] :=
  pins_esp f (fun _ _ h => h) hr

/-- `esp` is pinned in a branch. -/
theorem pins_at' {α : Type} {P : α → State → State → Prop} {X : α → State → Prop} (f : α → Pub)
    (hr : ∀ a s₀ t, P a s₀ t → Ready s₀ t) : Pins (fun a s => At (P a) (f a) s ∧ X a s) [.esp] :=
  pins_esp (P := P) f (fun _ _ h => h.1) hr

/-- After the head: the tape's length against the width. -/
def DrawHead (a : DrawPub) (s₀ t : State) : Prop :=
  DrawPre a s₀ t ∧ t.cf = some (decide ((rInput s₀).rand.length - a.used < rWidth s₀))

/-- A complete draw. -/
def DrawFull (a : DrawPub) (s₀ t : State) : Prop :=
  DrawPre a s₀ t ∧ a.used + rWidth s₀ ≤ (rInput s₀).rand.length

/-- After the copy's header and first byte. -/
def CopyHead (a : DrawPub) (s₀ t : State) : Prop :=
  (∃ t₀, CopyInv s₀ t₀ (X86.arg s₀ 9 + BitVec.ofNat 32 a.used) (drawPlace s₀) (drawBytes s₀ a.used)
    (maskValue (rLead s₀).toNat) 1 t) ∧ t.zf = some (decide (rWidth s₀ - 1 = 0)) ∧
  (drawBytes s₀ a.used).length = rWidth s₀

/-- After the copy's header. -/
def CopyHdr (a : DrawPub) (s₀ t : State) : Prop :=
  Ready s₀ t ∧ t.gpr .esi = X86.arg s₀ 9 + BitVec.ofNat 32 a.used ∧ t.gpr .ecx = BitVec.ofNat 32 (rWidth s₀) ∧
    t.gpr .edx = t.gpr .esp + BitVec.ofNat 32 (drawPlace s₀)

theorem copyInit_ct : RelCT isa (Two fun a => At (DrawFull a) a.pub) (.block copyInit) fun _ _ => True := by
  unfold copyInit
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := fun a => At (CopyHdr a) a.pub) [.esp]
    (pins_at DrawPub.pub fun _ _ _ h => h.1.smp.ready) (by taint_decide)
    fun a t ⟨s₀, A, e, D, _⟩ => WP.mono (copyHeader_ok A D.smp.ready D.smp.usedW D.smp.width)
      fun u ⟨h, _, _, x, c, d⟩ => ⟨s₀, A, e, h, x, c, d⟩) ?_
  refine two_taint [.esp, .esi, .ecx, .edx] (fun a t₁ t₂ h₁ h₂ r hr => ?_) (by taint_decide)
  obtain ⟨s₁, _, e₁, r₁, x₁, c₁, d₁⟩ := h₁
  obtain ⟨s₂, _, e₂, r₂, x₂, c₂, d₂⟩ := h₂
  have e := e₁.trans e₂.symm
  have esp := esp_of_rf r₁.rf (pub_rBase e ▸ r₂.rf)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact esp
  · rw [x₁, x₂, pub_arg e 9 (by decide)]
  · rw [c₁, c₂, pub_rWidth e]
  · rw [d₁, d₂, esp]
    simp only [drawPlace, pub_qBytes e, pub_rWidth e]

theorem copy_ct : RelCT isa (Two fun a => At (DrawFull a) a.pub) copy fun _ _ => True := by
  unfold copy
  refine RelCT.seq (two_post (Ψ := fun a => At (CopyHead a) a.pub) copyInit_ct
    fun a t ⟨s₀, A, e, D, hf⟩ => ?_) ?_
  · have hdl : (drawBytes s₀ a.used).length = rWidth s₀ := by
      simp only [drawBytes, List.length_take, List.length_drop]; omega_using [hf]
    exact WP.mono (copyInit_ok A D.smp.ready D.smp.usedW D.smp.width D.smp.mask hf (width_pos D.q))
      fun u ⟨I, z⟩ => ⟨s₀, A, e, ⟨t, I⟩, z, hdl⟩
  unfold copyRest
  refine two_ite (fun a t₁ t₂ ⟨s₁, _, e₁, _, z₁, _⟩ ⟨s₂, _, e₂, _, z₂, _⟩ => by
    simp only [eval, z₁, z₂, pub_rWidth (e₁.trans e₂.symm)]) ?_ ?_
  · refine copyLoop_ct fun a t₁ t₂ h₁ h₂ r hr => ?_
    obtain ⟨⟨s₁, _, e₁, ⟨_, I₁⟩, _, l₁⟩, _⟩ := h₁
    obtain ⟨⟨s₂, _, e₂, ⟨_, I₂⟩, _, l₂⟩, _⟩ := h₂
    have e := e₁.trans e₂.symm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [I₁.esi, I₂.esi, pub_arg e 9 (by decide)]
    · rw [I₁.edx, I₂.edx, esp_of_rf I₁.ready.rf (pub_rBase e ▸ I₂.ready.rf)]
      simp only [drawPlace, pub_qBytes e, pub_rWidth e]
    · rw [I₁.ecx, I₂.ecx, l₁, l₂, pub_rWidth e]
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
  refine RelCT.seq (two_piece (Ψ := fun a => At RangeHead a.pub) [.esp]
    (pins_at DrawPub.pub fun _ _ _ h => h.smp.ready) (by taint_decide)
    fun a t ⟨s₀, A, e, C⟩ => WP.mono (rangeInit_ok A C.smp.ready (cs := drawCand s₀ a.used) C.smp.q
      C.smp.width (copiedList_length _ _ _)) fun u ⟨I, _⟩ => ⟨s₀, A, e, t, _, I⟩) ?_
  refine rangeBody_ct fun a t₁ t₂ h₁ h₂ r hr => ?_
  obtain ⟨s₁, _, e₁, _, _, I₁⟩ := h₁
  obtain ⟨s₂, _, e₂, _, _, I₂⟩ := h₂
  have e := e₁.trans e₂.symm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [I₁.esi, I₂.esi, pub_rQ e, pub_qBytes e, pub_rWidth e]
  · rw [I₁.edx, I₂.edx, esp_of_rf I₁.ready.rf (pub_rBase e ▸ I₂.ready.rf)]
    simp only [drawPlace, pub_qBytes e, pub_rWidth e]
  · rw [I₁.ecx, I₂.ecx, pub_rWidth e]

/-- Before the decision. -/
structure Decided (a : DrawPub) (s₀ t : State) : Prop where
  smp : Smp s₀ (a.used + rWidth s₀) a.draws t
  pos : 1 ≤ a.draws
  le : a.draws ≤ 128
  zf : t.zf = some (!a.acc)

/-- After spending a draw. -/
def Spent (a : DrawPub) (s₀ t : State) : Prop :=
  Ready s₀ t ∧ t.zf = some (decide (a.draws - 1 = 0))

theorem drawFinish_ct : RelCT isa (Two fun a => At (Decided a) a.pub) drawFinish fun _ _ => True := by
  unfold drawFinish
  refine two_ite (fun a t₁ t₂ ⟨_, _, _, D₁⟩ ⟨_, _, _, D₂⟩ => by simp only [eval, D₁.zf, D₂.zf]) ?_ ?_
  · exact two_taint [.esp] (pins_at' DrawPub.pub fun _ _ _ h => h.smp.ready) (by taint_decide)
  refine RelCT.seq (two_piece (Ψ := fun a => At (Spent a) a.pub) [.esp]
    (pins_at' DrawPub.pub fun _ _ _ h => h.smp.ready) (by taint_decide)
    fun a t ⟨⟨s₀, A, e, D⟩, _⟩ => WP.mono (drawDec_ok A D.smp D.pos D.le)
      fun u ⟨_, _, _, h, z, _⟩ => ⟨s₀, A, e, h, z⟩) ?_
  refine two_ite (fun a t₁ t₂ ⟨_, _, _, _, z₁⟩ ⟨_, _, _, _, z₂⟩ => by simp only [eval, z₁, z₂]) ?_ ?_
  · exact two_taint [.esp] (pins_at' DrawPub.pub fun _ _ _ h => h.1) (by taint_decide)
  · exact two_taint [] (fun _ _ _ _ _ _ h => by cases h) (by taint_decide)

/-- After the comparison, the decision: the draw's acceptance. -/
theorem inRange_decided {a : DrawPub} {s₀ t : State} (A : RandomSignABI s₀) (C : Consumed a s₀ t) :
    WP isa inRange t (Decided a s₀) :=
  WP.mono (inRange_ok A C.smp.ready (cs := drawCand s₀ a.used) C.smp.q C.smp.width (copiedList_length _ _ _)
    (width_pos C.q) fun i hi => by rw [copiedList_getD _ _ hi]; exact C.bytes i hi)
    fun u ⟨_, z, m, h, _⟩ => ⟨C.smp.congr A h (by rw [m]; exact Outs.refl _ _ _) (by rw [m]) (by rw [m]),
      C.pos, C.le, by rw [z, C.acc]⟩

theorem full_ct : RelCT isa (Two fun a => At (DrawFull a) a.pub)
    (.seq copy (.seq (.block [.mov .eax (.mem (sp oUsed)), .alu .add .eax (.mem (sp oWidth)),
      .store (sp oUsed) .eax]) (.seq inRange drawFinish))) fun _ _ => True := by
  refine RelCT.seq (two_post (Ψ := fun a => At (Copied a) a.pub) copy_ct
    fun a t ⟨s₀, A, e, D, hf⟩ => WP.mono (drawCopy_ok A D.smp hf (width_pos D.q))
      fun u ⟨S, hc, _, _⟩ => ⟨s₀, A, e, { D with smp := S }, hf, hc⟩) ?_
  refine RelCT.seq (two_piece (Ψ := fun a => At (Consumed a) a.pub) [.esp]
    (pins_at DrawPub.pub fun _ _ _ h => h.pre.smp.ready) (by taint_decide)
    fun a t ⟨s₀, A, e, C⟩ => WP.mono (drawUsed_ok A C.pre.smp C.full)
      fun u ⟨S, hm, _⟩ => ⟨s₀, A, e, S, C.pre.pos, C.pre.le, C.pre.q, C.pre.acc C.full,
        drawUsed_bytes A hm C.bytes⟩) ?_
  exact RelCT.seq (two_post (Ψ := fun a => At (Decided a) a.pub) inRange_ct
    fun a t ⟨s₀, A, e, C⟩ => WP.mono (inRange_decided A C) fun u D => ⟨s₀, A, e, D⟩) drawFinish_ct

theorem draw_ct : RelCT isa (Two fun a => At (DrawPre a) a.pub) draw fun _ _ => True := by
  unfold draw
  refine RelCT.seq (two_piece (Ψ := fun a => At (DrawHead a) a.pub) [.esp]
    (pins_at DrawPub.pub fun _ _ _ h => h.smp.ready) (by taint_decide)
    fun a t ⟨s₀, A, e, D⟩ => WP.mono (drawHead_ok A D.smp)
      fun u ⟨S, _, _, c⟩ => ⟨s₀, A, e, { D with smp := S }, c⟩) ?_
  refine two_ite (fun a t₁ t₂ ⟨s₁, _, e₁, _, c₁⟩ ⟨s₂, _, e₂, _, c₂⟩ => by
    have e := e₁.trans e₂.symm
    simp only [eval, c₁, c₂, pub_randLen e, pub_rWidth e]) ?_ ?_
  · exact two_taint [.esp] (pins_at' DrawPub.pub fun _ _ _ h => h.1.smp.ready) (by taint_decide)
  · refine two_map id (fun a t ⟨⟨s₀, A, e, D, c⟩, hb⟩ => ⟨s₀, A, e, D, ?_⟩) full_ct
    have := D.smp.usedBound
    show a.used + rWidth s₀ ≤ (rInput s₀).rand.length
    simp only [eval, c, Option.some.injEq, decide_eq_false_iff_not] at hb
    omega_using [this, hb]

end VG.Proof.Dsa.X86

end

end

/-!
# Sampling leaks only its public trace (x86)

The specification's trace of a sampling (`Spec.Dsa.Random.Sample.trace`)
records each draw's decision. Two runs with the same public data, tape
offset and trace accept or reject each draw alike (`sample_trace_head`), so
they take the same branches; after a rejection the rest of the trace is the
next draw's.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Random

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
  have hdl : (drawBytes s₀ a.used).length = rWidth s₀ := by
    simp only [drawBytes, List.length_take, List.length_drop]; omega_using [hfull]
  have htr := L.tr
  rw [hd'] at htr
  show accepts s₀ (drawCand s₀ a.used) = (a.tr.head? == some 1)
  rw [accepts_candidate s₀ hdl (width_pos L.q), ← htr, spl,
    VG.Proof.Dsa.Random.sample_trace_head _ _ _ L.q (by rw [hdw, List.length_drop]; omega_using [hfull]), hdw]

def sampleBody : Prog isa := .seq draw (.block [.mov .eax (.mem (sp oStatus)), .alu .cmp .eax (.imm 4)])

/-- After a draw and the loop's test. -/
def StepPost (a : LoopPub) (s₀ t : State) : Prop :=
  Ready s₀ t ∧ t.zf = some a.cont ∧ (a.cont = true → LoopAt a.next s₀ t)

theorem sub_four_ne {x : BitVec 32} (h : x ≠ 4) : (x - 4 == 0) = false := by
  simp only [beq_eq_false_iff_ne, ne_eq]
  intro h'
  apply h
  calc x = x - 4 + 4 := (BitVec.sub_add_cancel x 4).symm
    _ = 4 := by rw [h']; rfl

theorem step_ok {a : LoopPub} {s₀ t : State} (A : RandomSignABI s₀) (e : pubOf s₀ = a.pub) (L : LoopAt a s₀ t) :
    WP isa sampleBody t (StepPost a s₀) := by
  unfold sampleBody
  refine WP.seq (WP.mono (draw_ok A L.smp L.pos L.le L.q L.status) fun v ⟨hv, _, _, hcase⟩ => ?_)
  refine wp_movS (v := slot v.mem (rBase s₀) oStatus) (hv.rf.readSlot (by decide)) fun v₁ uv₁ _ =>
    wp_cmpi fun v₂ fv₂ _ zv₂ => WP.block_nil ?_
  have hv₂ : Ready s₀ v₂ := (hv.upd uv₁ (by decide)).fupd fv₂
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
    RelCT isa (Two fun a t => a.draws = n ∧ At (LoopAt a) a.pub t) (.loop sampleBody .e)
      (Two fun (a : Pub) => At (fun s₀ t => Ready s₀ t) a) := by
  refine RelCT.loop (M := isa) (fun n => Two fun a t => a.draws = n ∧ At (LoopAt a) a.pub t) (fun n => ?_) n
  have hct : RelCT isa (Two fun a t => a.draws = n ∧ At (LoopAt a) a.pub t) sampleBody fun _ _ => True := by
    unfold sampleBody
    refine RelCT.seq (two_post (Ψ := fun a => At (fun s₀ t => Ready s₀ t) a.pub)
      (two_map (fun a => (⟨a.pub, a.used, a.draws, a.tr.head? == some 1⟩ : DrawPub))
        (fun a t ⟨_, s₀, A, e, L⟩ => ⟨s₀, A, e, L.drawPre⟩) draw_ct)
      (fun a t ⟨_, s₀, A, e, L⟩ => WP.mono (draw_ok A L.smp L.pos L.le L.q L.status)
        fun u h => ⟨s₀, A, e, h.1⟩)) ?_
    exact two_taint [.esp] (pins_at (P := fun _ s₀ t => Ready s₀ t) LoopPub.pub fun _ _ _ h => h)
      (by taint_decide)
  have hp := two_post (Ψ := fun a t => a.draws = n ∧ At (StepPost a) a.pub t) hct
    fun a t ⟨hn, s₀, A, e, L⟩ => WP.mono (step_ok A e L) fun u h => ⟨hn, s₀, A, e, h⟩
  refine hp.mono (fun _ _ h => h) ?_
  rintro t₁ t₂ ⟨a, ⟨hn, s₁, A₁, e₁, r₁, z₁, c₁⟩, ⟨_, s₂, A₂, e₂, r₂, z₂, c₂⟩⟩
  refine ⟨by simp only [eval, z₁, z₂], fun _ => ⟨a.pub, ⟨s₁, A₁, e₁, r₁⟩, ⟨s₂, A₂, e₂, r₂⟩⟩, fun hc => ?_⟩
  have hc' : a.cont = true := by simpa only [eval, z₁, Option.some.injEq] using hc
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

theorem sample_ct : RelCT isa (Two fun a => At (SamplePre a) a.pub) sample fun _ _ => True := by
  unfold sample
  refine RelCT.seq (two_piece (Ψ := fun a => At (LoopAt ⟨a.pub, a.used, 128, a.tr⟩) a.pub) [.esp]
    (pins_at SmpPub.pub fun _ _ _ h => h.1.choose_spec.ready) (by taint_decide)
    fun a t ⟨s₀, A, e, ⟨d, S⟩, hq, htr⟩ => WP.mono (sampleInit_ok A S)
      fun u ⟨S', st, _, _⟩ => ⟨s₀, A, e, S', st, (by decide : 1 ≤ 128), (by decide : 128 ≤ 128), hq, htr⟩) ?_
  refine RelCT.seq (two_map (fun a => (⟨a.pub, a.used, 128, a.tr⟩ : LoopPub)) (fun _ _ h => ⟨rfl, h⟩)
    (sampleLoop_ct 128)) ?_
  exact two_taint [.esp] (pins_at (P := fun _ s₀ t => Ready s₀ t) id fun _ _ _ h => h) (by taint_decide)

end VG.Proof.Dsa.X86

end

end

/-! ### `Dsa.X86.RandomCallCT`, which this module and modules that import it used -/

section

/-!
# The signer's call leaks only what its contract allows (x86)

Two runs call `vg_dsa_sign` with the same public arguments, public key
bytes and signing status (`call_pub`), which its contract's constant time
covers (`call_ct`).
-/

@[expose] public section

namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Random

theorem call_pub {valid : Nat → Nat → List Byte → Bool} {s₁ s₂ t₁ t₂ : State} (A₁ : RandomSignABI s₁) (A₂ : RandomSignABI s₂) (e : pubOf s₁ = pubOf s₂)
    (h₁ : Ready s₁ t₁) (h₂ : Ready s₂ t₂) (C₁ : CallSlots s₁ t₁) (C₂ : CallSlots s₂ t₂) (rd wr : List Region)
    (hk : Spec.Dsa.publicBytesLeak (rInput s₁).pLen (rInput s₁).qLen (rInput s₁).key =
      Spec.Dsa.publicBytesLeak (rInput s₂).pLen (rInput s₂).qLen (rInput s₂).key)
    (hr : Spec.Dsa.signStatus (callResult s₁ t₁) = Spec.Dsa.signStatus (callResult s₂ t₂)) :
    (signContractWith valid abi 108).pub (t₁.callEntry.withRegions rd wr) (t₂.callEntry.withRegions rd wr) := by
  sig_pub [signContractWith, Spec.Dsa.signSig, abi, argSlots, argVal, argBytes]
  simp only [ce_arg A₁ h₁ C₁ rd wr (show 0 < 11 by decide),
    ce_arg A₁ h₁ C₁ rd wr (show 1 < 11 by decide),
    ce_arg A₁ h₁ C₁ rd wr (show 2 < 11 by decide),
    ce_arg A₁ h₁ C₁ rd wr (show 3 < 11 by decide),
    ce_arg A₁ h₁ C₁ rd wr (show 4 < 11 by decide),
    ce_arg A₁ h₁ C₁ rd wr (show 5 < 11 by decide),
    ce_arg A₁ h₁ C₁ rd wr (show 6 < 11 by decide),
    ce_arg A₁ h₁ C₁ rd wr (show 7 < 11 by decide),
    ce_arg A₁ h₁ C₁ rd wr (show 8 < 11 by decide),
    ce_arg A₁ h₁ C₁ rd wr (show 9 < 11 by decide),
    ce_arg A₁ h₁ C₁ rd wr (show 10 < 11 by decide),
    ce_arg A₂ h₂ C₂ rd wr (show 0 < 11 by decide),
    ce_arg A₂ h₂ C₂ rd wr (show 1 < 11 by decide),
    ce_arg A₂ h₂ C₂ rd wr (show 2 < 11 by decide),
    ce_arg A₂ h₂ C₂ rd wr (show 3 < 11 by decide),
    ce_arg A₂ h₂ C₂ rd wr (show 4 < 11 by decide),
    ce_arg A₂ h₂ C₂ rd wr (show 5 < 11 by decide),
    ce_arg A₂ h₂ C₂ rd wr (show 6 < 11 by decide),
    ce_arg A₂ h₂ C₂ rd wr (show 7 < 11 by decide),
    ce_arg A₂ h₂ C₂ rd wr (show 8 < 11 by decide),
    ce_arg A₂ h₂ C₂ rd wr (show 9 < 11 by decide),
    ce_arg A₂ h₂ C₂ rd wr (show 10 < 11 by decide),
    callVal, esp_ptr h₁ (d := oNonce) (by decide), esp_ptr h₂ (d := oNonce) (by decide),
    show 24 + oNonce = 112 from rfl]
  have hql₁ := rQBytes_le A₁
  have hqn₁ := rQBytes_length A₁
  have hql₂ := rQBytes_le A₂
  have hqn₂ := rQBytes_length A₂
  have esp := esp_of_rf h₁.rf (pub_rBase e ▸ h₂.rf)
  rw [callEntry_bytes A₁ h₁ (A₁.stackKeyWide.symm.sub_right (stk_sub s₁ (by decide))) (by omega_using []),
    callEntry_bytes A₁ h₁ ((Offset.disjoint _ (by omega_using []) (by omega_using []) (by omega_using []) :
      Region.Disjoint ⟨off (rLow s₁) 20, 4⟩ ⟨off (rLow s₁) 112, (X86.arg s₁ 6).toNat⟩).symm) (by omega_using []),
    callEntry_bytes A₁ h₁ (A₁.stackDigestWide.symm.sub_right (stk_sub s₁ (by decide))) (by omega_using []),
    callEntry_bytes A₂ h₂ (A₂.stackKeyWide.symm.sub_right (stk_sub s₂ (by decide))) (by omega_using []),
    callEntry_bytes A₂ h₂ ((Offset.disjoint _ (by omega_using []) (by omega_using []) (by omega_using []) :
      Region.Disjoint ⟨off (rLow s₂) 20, 4⟩ ⟨off (rLow s₂) 112, (X86.arg s₂ 6).toNat⟩).symm) (by omega_using []),
    callEntry_bytes A₂ h₂ (A₂.stackDigestWide.symm.sub_right (stk_sub s₂ (by decide))) (by omega_using [])]
  have k₁ := callKey A₁ h₁
  have k₂ := callKey A₂ h₂
  simp only [argumentPointer] at k₁ k₂
  refine ⟨by rw [esp], congrArg₂ (fun x y => x ++ [y]) (by rw [k₁, k₂]; exact hk) hr,
    pub_arg e 0 (by decide), pub_arg e 1 (by decide), pub_arg e 3 (by decide), pub_arg e 4 (by decide),
    pub_arg e 5 (by decide), by rw [esp], pub_arg e 6 (by decide), pub_arg e 7 (by decide),
    pub_arg e 8 (by decide), pub_arg e 11 (by decide), pub_arg e 12 (by decide)⟩

theorem pub_callRd {s₁ s₂ : State} (e : pubOf s₁ = pubOf s₂) : callRd s₁ = callRd s₂ := by
  simp only [callRd, argRegion, argumentPointer, pub_arg e 3 (by decide), pub_arg e 4 (by decide),
    pub_arg e 6 (by decide), pub_arg e 7 (by decide), pub_arg e 8 (by decide), pub_rLow e]

theorem pub_callWr {s₁ s₂ : State} (e : pubOf s₁ = pubOf s₂) : callWr s₁ = callWr s₂ := by
  simp only [callWr, argRegion, argumentPointer, pub_arg e 0 (by decide), pub_arg e 1 (by decide),
    pub_arg e 11 (by decide), pub_arg e 12 (by decide), pub_rLow e]

/-- The public key bytes of the entry. -/
abbrev keyLeak (s₀ : State) : List Nat :=
  Spec.Dsa.publicBytesLeak (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key

/-- Two runs about to call the signer alike, with keys the signer accepts. -/
def CallRel (valid : Nat → Nat → List Byte → Bool) (t₁ t₂ : State) : Prop :=
  ∃ s₁ s₂, RandomSignABI s₁ ∧ RandomSignABI s₂ ∧ pubOf s₁ = pubOf s₂ ∧ keyLeak s₁ = keyLeak s₂ ∧
    Ready s₁ t₁ ∧ Ready s₂ t₂ ∧ CallSlots s₁ t₁ ∧ CallSlots s₂ t₂ ∧
    Spec.Dsa.signStatus (callResult s₁ t₁) = Spec.Dsa.signStatus (callResult s₂ t₂) ∧
    KeyValid valid s₁ ∧ KeyValid valid s₂

theorem call_ct (F : SignFn) : RelCT isa (CallRel F.valid) (.call F.name F.code) fun _ _ => True := by
  intro t₁ t₂ u₁ u₂ v₁ v₂ hp x₁ x₂
  obtain ⟨s₁, s₂, A₁, A₂, e, hk, h₁, h₂, C₁, C₂, hr, v₁', v₂'⟩ := hp
  refine RelCT.call (P := fun x y => x = t₁ ∧ y = t₂) F.verified.1 F.verified.2.1 (callRd s₁) (callWr s₁)
    (fun _ _ ⟨r₁, r₂⟩ => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ x₁ x₂
  subst r₁ r₂
  obtain ⟨c₁, w₁⟩ := call_covers A₁ h₁
  obtain ⟨c₂, w₂⟩ := call_covers A₂ h₂
  have p₂ := call_pre_with A₂ h₂ C₂ v₂'
  rw [← pub_callRd e, ← pub_callWr e] at p₂ c₂
  rw [← pub_callWr e] at w₂
  exact ⟨call_pre_with A₁ h₁ C₁ v₁', p₂, call_pub A₁ A₂ e h₁ h₂ C₁ C₂ _ _ hk hr, c₁, w₁, c₂, w₂,
    esp_of_rf h₁.rf (pub_rBase e ▸ h₂.rf)⟩

end VG.Proof.Dsa.X86

end

end

/-!
# An attempt leaks only its public trace (x86)

The rest of the specification's signing (`randomSignRemaining`) has a trace
that records the attempt's sampling (`randomSamplingTrace`), whether it
found a nonce (`AttPub.ok`) and whether signing with it succeeded
(`AttPub.signed`). Two runs with the same public data, consumption,
attempts and trace take the same branches.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Random VG.Impl.Dsa.X86.RandomSign
open VG.Proof.Dsa (randomSignRemaining randomSamplingTrace randomSigningTrace)

variable {V : Nat → Nat → List Byte → Bool}

/-- What two runs share before an attempt, for a signer that accepts the
keys `V` accepts. -/
structure AttPub (V : Nat → Nat → List Byte → Bool) where
  pub : Pub
  leak : List Nat
  used : Nat
  fuel : Nat
  tr : List Nat
  /-- The overall status. -/
  status : Nat

/-- Whether the attempt's sampling finds a nonce. -/
def AttPub.ok (a : AttPub V) : Bool := (randomSamplingTrace a.tr).getLast? == some 1

/-- Whether signing with it succeeds. -/
def AttPub.signed (a : AttPub V) : Bool := randomSigningTrace a.tr == [5]

/-- What the attempt keeps of its entry. -/
structure AttFacts (a : AttPub V) (s₀ : State) : Prop where
  q : 1 < rq s₀
  pos : 1 ≤ a.fuel
  le : a.fuel ≤ 8
  leak : keyLeak s₀ = a.leak
  tr : (randomSignRemaining (rInput s₀) a.used a.fuel).trace = a.tr
  valid : KeyValid V s₀

/-- Before an attempt. -/
def AttAt (a : AttPub V) (s₀ t : State) : Prop := AttFacts a s₀ ∧ Att s₀ a.used a.fuel t

theorem AttFacts.spl_trace {a : AttPub V} {s₀ : State} (F : AttFacts a s₀) :
    (spl s₀ 128 a.used).trace = randomSamplingTrace a.tr := by
  obtain ⟨f, hf⟩ : ∃ f, a.fuel = f + 1 := ⟨a.fuel - 1, by have := F.pos; omega_using [this]⟩
  rw [← F.tr, hf]
  exact (VG.Proof.Dsa.random_sign_trace_draw _ _ _).symm

theorem AttFacts.ok {a : AttPub V} {s₀ : State} (F : AttFacts a s₀) :
    (spl s₀ 128 a.used).scalar.isSome = a.ok := by
  rw [(VG.Proof.Dsa.Random.sample_trace_result _ _ _).2, F.spl_trace]; rfl

theorem AttFacts.status {a : AttPub V} {s₀ : State} (F : AttFacts a s₀) :
    decide (VG.Proof.Dsa.Random.sampleStatus (spl s₀ 128 a.used) = 1) = a.ok := by
  rw [← F.ok]
  unfold VG.Proof.Dsa.Random.sampleStatus
  split
  · next h => simp [h]
  · next h => simp only [h, Option.isSome_none]; split <;> decide

theorem AttFacts.signed {a : AttPub V} {s₀ : State} (F : AttFacts a s₀) {k : Nat}
    (hk : (spl s₀ 128 a.used).scalar = some k) :
    (Spec.Dsa.signBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key
      (Spec.Dsa.encodeBE (rInput s₀).qLen k) (rInput s₀).digest).isSome = a.signed := by
  obtain ⟨f, hf⟩ : ∃ f, a.fuel = f + 1 := ⟨a.fuel - 1, by have := F.pos; omega_using [this]⟩
  have htr := F.tr
  rw [hf] at htr
  unfold AttPub.signed
  rw [← htr]
  cases hs : Spec.Dsa.signBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key
      (Spec.Dsa.encodeBE (rInput s₀).qLen k) (rInput s₀).digest with
  | some sig => rw [VG.Proof.Dsa.random_sign_trace_success _ _ _ _ hk hs]; rfl
  | none => rw [VG.Proof.Dsa.random_sign_trace_retry _ _ _ _ hk hs]; simp

/-- After sampling. -/
structure Sampled (a : AttPub V) (s₀ t : State) : Prop where
  facts : AttFacts a s₀
  out : SampleOut s₀ a.used (spl s₀ 128 a.used) t
  ready : Ready s₀ t
  attempts : slot t.mem (rBase s₀) oAttempts = BitVec.ofNat 32 a.fuel

theorem sample_sampled {a : AttPub V} {s₀ t : State} (A : RandomSignABI s₀) (h : AttAt a s₀ t) :
    WP isa sample t fun u => Sampled a s₀ u ∧
      u.gpr .eax = BitVec.ofNat 32 (VG.Proof.Dsa.Random.sampleStatus (spl s₀ 128 a.used)) := by
  obtain ⟨F, T⟩ := h
  obtain ⟨d₀, Sm⟩ := T.smp
  exact WP.mono (sample_ok A Sm F.q) fun u₁ ⟨O, eax₁, h₁, o₁, _⟩ =>
    ⟨⟨F, O, h₁, (slot_outs o₁ (by decide) (by decide)).trans T.attempts⟩, eax₁⟩

/-- After the test of the sampling's status. -/
def Tested (a : AttPub V) (s₀ t : State) : Prop := Sampled a s₀ t ∧ t.zf = some a.ok

/-- After storing the signer's arguments. -/
structure Args (a : AttPub V) (s₀ t : State) : Prop where
  facts : AttFacts a s₀
  ready : Ready s₀ t
  slots : CallSlots s₀ t
  nonce : ∃ k, (spl s₀ 128 a.used).scalar = some k ∧
    Spec.Rsa.bytesAt t.mem (off (rBase s₀) oNonce) (rQBytes s₀).length = Spec.Dsa.encodeBE (rQBytes s₀).length k
  attempts : slot t.mem (rBase s₀) oAttempts = BitVec.ofNat 32 a.fuel

theorem args_ok {a : AttPub V} {s₀ t : State} (A : RandomSignABI s₀) (h : Tested a s₀ t)
    (hok : a.ok = true) : WP isa (.block callArgs) t (Args a s₀) := by
  obtain ⟨S, -⟩ := h
  have hql := rQBytes_le A
  obtain ⟨k, hk⟩ : ∃ k, (spl s₀ 128 a.used).scalar = some k := by
    have := S.facts.ok
    rw [hok] at this
    exact Option.isSome_iff_exists.mp this
  refine (callArgs_ok (is := []) A S.ready fun u₃ h₃ m₃ k₃ => WP.block_nil ?_ :
    WP isa (.block (callArgs ++ [])) t _)
  have o₃ := argsMem_outs s₀ t.mem (t.gpr .esp)
  rw [← m₃] at o₃
  refine ⟨S.facts, h₃, fun i hi => ?_, ⟨k, hk, ?_⟩, ?_⟩
  · rw [m₃, k₃.1 .esp (by decide)]; exact argsMem_slots s₀ _ _ i hi
  · rw [outs_frame_bytes o₃ (by decide) (by unfold oNonce; omega_using [hql])]; exact S.out.nonce k hk
  · rw [outs_high o₃ (e := 44) (by decide) (by decide) (by decide)]; exact S.attempts

/-- After the call. -/
structure Called (a : AttPub V) (s₀ t : State) : Prop where
  pos : 1 ≤ a.fuel
  le : a.fuel ≤ 8
  ready : Ready s₀ t
  eax : t.gpr .eax = BitVec.ofNat 32 (if a.signed then 1 else 0)
  attempts : slot t.mem (rBase s₀) oAttempts = BitVec.ofNat 32 a.fuel

theorem Args.status {a : AttPub V} {s₀ t : State} (A : RandomSignABI s₀) (h : Args a s₀ t) :
    Spec.Dsa.signStatus (callResult s₀ t) = if a.signed then 1 else 0 := by
  obtain ⟨k, hk, hn⟩ := h.nonce
  rw [callResult_eq A h.ready hn, Spec.Dsa.signStatus, h.facts.signed hk]

theorem call_called (F : SignFn) {a : AttPub F.valid} {s₀ t : State} (A : RandomSignABI s₀) (h : Args a s₀ t) :
    WP isa (.call F.name F.code) t (Called a s₀) :=
  WP.mono (call_ok F A h.ready h.slots h.facts.valid) fun u ⟨h₄, f₄, _, eax₄, _⟩ =>
    ⟨h.facts.pos, h.facts.le, h₄, by rw [eax₄, h.status A],
      by rw [call_frame_slot A f₄ (by decide) (by decide)]; exact h.attempts⟩

/-- After recording the signer's status. -/
def Recorded (a : AttPub V) (s₀ t : State) : Prop :=
  Ready s₀ t ∧ t.zf = some (!a.signed) ∧ slot t.mem (rBase s₀) oAttempts = BitVec.ofNat 32 a.fuel ∧
    1 ≤ a.fuel ∧ a.fuel ≤ 8

/-- After spending an attempt. -/
def Spent' (a : AttPub V) (s₀ t : State) : Prop := Ready s₀ t ∧ t.zf = some (decide (a.fuel - 1 = 0))

theorem callFinish_ct : RelCT isa (Two fun (a : AttPub V) => At (Called a) a.pub) callFinish
    fun _ _ => True := by
  unfold callFinish
  refine RelCT.seq (two_piece (Ψ := fun a => At (Recorded a) a.pub) [.esp]
    (pins_at AttPub.pub fun _ _ _ h => h.ready) (by taint_decide) fun a t ⟨s₀, A, e, C⟩ => ?_) ?_
  · refine WP.mono (finHead_ok C.ready (st := if a.signed then 1 else 0) (by split <;> decide) C.eax)
      fun u ⟨h, _, m, z⟩ => ⟨s₀, A, e, h, ?_, ?_, C.pos, C.le⟩
    · rw [z]; cases a.signed <;> rfl
    · rw [m, slot_write_ne _ _ _ (by decide) (by decide) (by decide)]; exact C.attempts
  refine two_ite (fun a t₁ t₂ ⟨_, _, _, _, z₁, _⟩ ⟨_, _, _, _, z₂, _⟩ => by simp only [eval, z₁, z₂]) ?_ ?_
  · refine RelCT.seq (two_piece (Ψ := fun a => At (Spent' a) a.pub) [.esp]
      (pins_at' AttPub.pub fun _ _ _ h => h.1) (by taint_decide)
      fun a t ⟨⟨s₀, A, e, h, _, ha, hp, hl⟩, _⟩ => ?_) ?_
    · obtain ⟨f, hf⟩ : ∃ f, a.fuel = f + 1 := ⟨a.fuel - 1, by omega_using [hp]⟩
      rw [hf] at ha hl
      refine WP.mono (finDec_ok h ha hl) fun u ⟨h', _, _, z⟩ => ⟨s₀, A, e, h', ?_⟩
      rw [z, hf, Nat.add_sub_cancel]
    · refine two_ite (fun a t₁ t₂ ⟨_, _, _, _, z₁⟩ ⟨_, _, _, _, z₂⟩ => by simp only [eval, z₁, z₂]) ?_ ?_
      · exact two_taint [.esp] (pins_at' AttPub.pub fun _ _ _ h => h.1) (by taint_decide)
      · exact two_taint [] (fun _ _ _ _ _ _ h => by cases h) (by taint_decide)
  · exact two_taint [] (fun _ _ _ _ _ _ h => by cases h) (by taint_decide)

theorem signerCall_ct (F : SignFn) :
    RelCT isa (Two fun (a : AttPub F.valid) => At (Args a) a.pub) (.call F.name F.code)
    fun _ _ => True :=
  (call_ct F).mono (fun t₁ t₂ ⟨a, ⟨s₁, A₁, e₁, h₁⟩, ⟨s₂, A₂, e₂, h₂⟩⟩ =>
    ⟨s₁, s₂, A₁, A₂, e₁.trans e₂.symm, h₁.facts.leak.trans h₂.facts.leak.symm, h₁.ready, h₂.ready,
      h₁.slots, h₂.slots, by rw [h₁.status A₁, h₂.status A₂], h₁.facts.valid, h₂.facts.valid⟩)
    fun _ _ h => h

theorem attempt_ct (F : SignFn) :
    RelCT isa (Two fun (a : AttPub F.valid) => At (AttAt a) a.pub) (attempt F.name F.code)
      fun _ _ => True := by
  unfold attempt
  refine RelCT.seq (two_post (Ψ := fun a => At (fun s₀ t => Sampled a s₀ t ∧
      t.gpr .eax = BitVec.ofNat 32 (VG.Proof.Dsa.Random.sampleStatus (spl s₀ 128 a.used))) a.pub)
    (two_map (fun a => (⟨a.pub, a.used, randomSamplingTrace a.tr⟩ : SmpPub))
      (fun a t ⟨s₀, A, e, F, T⟩ => ⟨s₀, A, e, T.smp, F.q, F.spl_trace⟩) sample_ct)
    fun a t ⟨s₀, A, e, h⟩ => WP.mono (sample_sampled A h) fun u hu => ⟨s₀, A, e, hu⟩) ?_
  refine RelCT.seq (two_piece (Ψ := fun a => At (Tested a) a.pub) [.esp]
    (pins_at AttPub.pub fun _ _ _ h => h.1.ready) (by taint_decide)
    fun a t ⟨s₀, A, e, S, eax⟩ => wp_cmpi fun u fu _ z => WP.block_nil ⟨s₀, A, e, ?_, ?_⟩) ?_
  · exact ⟨S.facts, ⟨let ⟨d, Sd⟩ := S.out.smp; ⟨d, Sd.mem A (S.ready.fupd fu) fu.mem⟩,
      by rw [fu.mem]; exact S.out.status, by rw [fu.mem]; exact S.out.nonce⟩, S.ready.fupd fu,
      by rw [fu.mem]; exact S.attempts⟩
  · have hle := sampleStatus_le (spl s₀ 128 a.used)
    rw [z, eax, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_beq (by omega_using [hle]) (by decide),
      S.facts.status]
  refine two_ite (fun a t₁ t₂ ⟨_, _, _, _, z₁⟩ ⟨_, _, _, _, z₂⟩ => by simp only [eval, z₁, z₂]) ?_ ?_
  · refine RelCT.seq (two_piece (Ψ := fun a => At (Args a) a.pub) [.esp]
      (pins_at' AttPub.pub fun _ _ _ h => h.1.ready) (by taint_decide)
      fun a t ⟨⟨s₀, A, e, h⟩, hb⟩ => WP.mono (args_ok A h (by
        simpa only [eval, h.2, Option.some.injEq] using hb)) fun u hu => ⟨s₀, A, e, hu⟩) ?_
    exact RelCT.seq (two_post (Ψ := fun a => At (Called a) a.pub) (signerCall_ct F)
      fun a t ⟨s₀, A, e, h⟩ => WP.mono (call_called F A h) fun u hu => ⟨s₀, A, e, hu⟩) callFinish_ct
  · exact two_taint [] (fun _ _ _ _ _ _ h => by cases h) (by taint_decide)

end VG.Proof.Dsa.X86

end

end

/-!
# The randomized signer's body leaks only its public data (x86)

The attempts continue after a retry with attempts left, which the signing
trace records (`AttPub.cont`); the next attempt's trace is the rest of it.
`finish` branches on the overall status, and writes through the public
`out` and `used` pointers.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Random VG.Impl.Dsa.X86.RandomSign
open VG.Proof.Dsa (randomSignRemaining randomSamplingTrace randomSigningTrace)

variable {V : Nat → Nat → List Byte → Bool}

/-! ## The attempts -/

/-- Whether another attempt follows: a retry, with attempts left. -/
def AttPub.cont (a : AttPub V) : Bool := ((randomSigningTrace a.tr).head? == some 6) && decide (2 ≤ a.fuel)

def AttPub.next (a : AttPub V) : AttPub V :=
  ⟨a.pub, a.leak, a.used + a.pub.width * (randomSamplingTrace a.tr).countP (· ≤ 1), a.fuel - 1,
    (randomSigningTrace a.tr).tail, a.status⟩

/-- The test of the attempt's status. -/
abbrev attTest : Prog isa := .block [.mov .eax (.mem (sp oStatus)), .alu .cmp .eax (.imm 4)]

theorem AttemptOut.ready {s₀ u : State} {used f : Nat} (h : AttemptOut s₀ used f u) : Ready s₀ u := by
  rcases h with ⟨_, _, T, _⟩ | ⟨_, D, _⟩
  · obtain ⟨_, S⟩ := T.smp; exact S.ready
  · obtain ⟨_, S⟩ := D.smp; exact S.ready

/-- After an attempt and its test. -/
def AStep (a : AttPub V) (s₀ t : State) : Prop :=
  Ready s₀ t ∧ t.zf = some a.cont ∧ (a.cont = true → AttAt a.next s₀ t) ∧ (a.cont = false → Fin s₀ t)

theorem astep_ok (F : SignFn) {a : AttPub F.valid} {s₀ t : State} (A : RandomSignABI s₀) (e : pubOf s₀ = a.pub)
    (L : AttAt a s₀ t) : WP isa (.seq (attempt F.name F.code) attTest) t (AStep a s₀) := by
  obtain ⟨Fa, T⟩ := L
  obtain ⟨f, hf⟩ : ∃ f, a.fuel = f + 1 := ⟨a.fuel - 1, by have := Fa.pos; omega_using [this]⟩
  have hf8 : f + 1 ≤ 8 := hf ▸ Fa.le
  rw [hf] at T
  refine WP.seq (WP.mono (attempt_ok F A T hf8 Fa.q Fa.valid) fun v hv => ?_)
  have hrv := hv.ready
  refine wp_movS (hrv.rf.readSlot (by decide)) fun v₁ uv₁ _ => wp_cmpi fun v₂ fv₂ _ zv₂ => WP.block_nil ?_
  have hv₂ := (hrv.upd uv₁ (by decide)).fupd fv₂
  have mv₂ : v₂.mem = v.mem := by rw [fv₂.mem, uv₁.mem]
  rw [uv₁.gpr] at zv₂
  have htr := Fa.tr
  rw [hf] at htr
  rcases hv with ⟨st, h1f, T', hs⟩ | ⟨st, D, hh⟩
  · have hc : a.cont = true := by
      simp only [AttPub.cont, ← htr, hs, List.head?_cons, beq_self_eq_true, Bool.true_and, decide_eq_true_eq]
      omega_using [hf, h1f]
    have st' : v.mem.readW (off (rBase s₀) oStatus) 32 = 4 := st
    refine ⟨hv₂, by rw [zv₂, st', hc]; rfl, fun _ => ?_, fun h => Bool.noConfusion (hc.symm.trans h)⟩
    have hu : a.pub.width * (randomSamplingTrace a.tr).countP (· ≤ 1) = (spl s₀ 128 a.used).used := by
      rw [(VG.Proof.Dsa.Random.sample_trace_result _ _ _).1, Fa.spl_trace, pub_width e, rWidth_eq]
    refine ⟨⟨Fa.q, by show 1 ≤ a.fuel - 1; omega_using [hf, h1f], by show a.fuel - 1 ≤ 8; omega_using [hf, hf8], Fa.leak, ?_, Fa.valid⟩, ?_⟩
    · show (randomSignRemaining (rInput s₀) (a.used + a.pub.width * _) (a.fuel - 1)).trace =
        (randomSigningTrace a.tr).tail
      rw [hu, hf, Nat.add_sub_cancel, ← htr, hs]; rfl
    · show Att s₀ (a.used + a.pub.width * _) (a.fuel - 1) v₂
      rw [hu, hf, Nat.add_sub_cancel]; exact T'.mem A hv₂ mv₂
  · have hc : a.cont = false := by
      simp only [AttPub.cont, ← htr, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
        decide_eq_false_iff_not]
      by_cases h6 : (randomSigningTrace (randomSignRemaining (rInput s₀) a.used (f + 1)).trace).head? = some 6
      · exact .inr fun h2 => hh ⟨h6, by omega⟩
      · exact .inl h6
    exact ⟨hv₂, by rw [zv₂, sub_four_ne st, hc], fun h => Bool.noConfusion (hc.symm.trans h),
      fun _ => (D.mem A hv₂ mv₂).fin⟩

/-- At the end: the frame's slots, and the overall status `p.2`. -/
def FinAt (p : Pub × Nat) : State → Prop := At (fun s₀ t => Fin s₀ t ∧ (rResult s₀).status = p.2) p.1

/-- Before an attempt, with the overall status. -/
def LoopAt' (a : AttPub V) : State → Prop := At (fun s₀ t => AttAt a s₀ t ∧ (rResult s₀).status = a.status) a.pub

theorem attemptLoop_ct (F : SignFn) (n : Nat) :
    RelCT isa (Two fun (a : AttPub F.valid) t => a.fuel = n ∧ LoopAt' a t)
      (.loop (.seq (attempt F.name F.code) attTest) .e)
      (Two FinAt) := by
  refine RelCT.loop (M := isa) (fun n => Two fun (a : AttPub F.valid) t => a.fuel = n ∧ LoopAt' a t)
    (fun n => ?_) n
  have hct : RelCT isa (Two fun (a : AttPub F.valid) t => a.fuel = n ∧ LoopAt' a t)
      (.seq (attempt F.name F.code) attTest)
      fun _ _ => True := by
    refine RelCT.seq (two_post (Ψ := fun a => At (fun s₀ t => Ready s₀ t) a.pub)
      (two_map id (fun a t ⟨_, s₀, A, e, L, _⟩ => ⟨s₀, A, e, L⟩) (attempt_ct F))
      (fun a t ⟨_, s₀, A, e, ⟨Fa, T⟩, _⟩ => ?_)) ?_
    · obtain ⟨f, hf⟩ : ∃ f, a.fuel = f + 1 := ⟨a.fuel - 1, by have := Fa.pos; omega_using [this]⟩
      have hf8 : f + 1 ≤ 8 := hf ▸ Fa.le
      rw [hf] at T
      exact WP.mono (attempt_ok F A T hf8 Fa.q Fa.valid) fun u h => ⟨s₀, A, e, h.ready⟩
    · exact two_taint [.esp] (pins_at (P := fun _ s₀ t => Ready s₀ t) AttPub.pub fun _ _ _ h => h)
        (by taint_decide)
  have hp := two_post (Ψ := fun a t => a.fuel = n ∧ At (fun s₀ t => AStep a s₀ t ∧
      (rResult s₀).status = a.status) a.pub t) hct
    fun a t ⟨hn, s₀, A, e, L, st⟩ => WP.mono (astep_ok F A e L) fun u h => ⟨hn, s₀, A, e, h, st⟩
  refine hp.mono (fun _ _ h => h) ?_
  rintro t₁ t₂ ⟨a, ⟨hn, s₁, A₁, e₁, ⟨r₁, z₁, c₁, d₁⟩, st₁⟩, ⟨_, s₂, A₂, e₂, ⟨r₂, z₂, c₂, d₂⟩, st₂⟩⟩
  refine ⟨by simp only [eval, z₁, z₂], fun hc => ?_, fun hc => ?_⟩
  · have hc' : a.cont = false := by simpa only [eval, z₁, Option.some.injEq] using hc
    exact ⟨(a.pub, a.status), ⟨s₁, A₁, e₁, d₁ hc', st₁⟩, ⟨s₂, A₂, e₂, d₂ hc', st₂⟩⟩
  · have hc' : a.cont = true := by simpa only [eval, z₁, Option.some.injEq] using hc
    have h2 : 2 ≤ a.fuel := by
      simp only [AttPub.cont, Bool.and_eq_true, decide_eq_true_eq] at hc'; exact hc'.2
    exact ⟨n - 1, by omega, a.next, ⟨by show a.fuel - 1 = n - 1; omega_using [hn], s₁, A₁, e₁, c₁ hc', st₁⟩,
      ⟨by show a.fuel - 1 = n - 1; omega_using [hn], s₂, A₂, e₂, c₂ hc', st₂⟩⟩

/-! ## The end -/

/-- Test the overall status. -/
theorem finTest_ok {s₀ t : State} (A : RandomSignABI s₀) (Fi : Fin s₀ t) :
    WP isa (.block [.mov .eax (.mem (sp oStatus)), .alu .cmp .eax (.imm 1)]) t fun u =>
      Ready s₀ u ∧ u.zf = some (decide ((rResult s₀).status = 1)) := by
  have hR := rResult_status_le A
  refine wp_movS (v := BitVec.ofNat 32 (rResult s₀).status)
    (by rw [Fi.ready.rf.readSlot (by decide)]; exact congrArg some Fi.status)
    fun t₁ u₁ _ => wp_cmpi fun t₂ f₂ _ z₂ => WP.block_nil ⟨(Fi.ready.upd u₁ (by decide)).fupd f₂, ?_⟩
  rw [z₂, u₁.gpr, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_beq (by omega_using [hR]) (by decide)]

/-- The output's address and length. -/
theorem zeroHead_ok {s₀ t : State} (A : RandomSignABI s₀) (h : Ready s₀ t) :
    WP isa (.block [.mov .esi (.mem (Random.arg aOut)), .mov .ecx (.mem (Random.arg aOutLen)), .mov .eax (.imm 0)])
      t fun u => Ready s₀ u ∧ u.gpr .esi = X86.arg s₀ 0 ∧ u.gpr .ecx = X86.arg s₀ 1 := by
  refine wp_movS (h.argSrc A (j := 0) (by decide)) fun t₁ u₁ _ => ?_
  have h₁ := h.upd u₁ (by decide)
  refine wp_movS (h₁.argSrc A (j := 1) (by decide)) fun t₂ u₂ _ => wp_movS rfl fun t₃ u₃ _ => WP.block_nil ?_
  exact ⟨(h₁.upd u₂ (by decide)).upd u₃ (by decide), by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr],
    by rw [u₃.other _ (by decide), u₂.gpr]⟩

/-- The nonce cleared, and the address of `used`. -/
theorem finPrefix_ok {s₀ t : State} (A : RandomSignABI s₀) (h : Ready s₀ t) :
    WP isa (.block (clearNonce ++ ([.mov .edx (.mem (Random.arg aUsed))] : List Instr))) t fun u =>
      Ready s₀ u ∧ u.gpr .edx = X86.arg s₀ 2 := by
  refine clearNonce_ok h.rf fun t₁ _ m₁ k₁ _ => ?_
  have h₁ : Ready s₀ t₁ := h.congr k₁ (by rw [m₁]; exact clearMem_frame s₀ _ 8 (by decide))
  exact wp_movS (h₁.argSrc A (j := 2) (by decide)) fun t₂ u₂ _ => WP.block_nil ⟨h₁.upd u₂ (by decide), u₂.gpr⟩

/-- Ready, with public data `p.1`. -/
def ReadyAt (p : Pub × Nat) : State → Prop := At (fun s₀ t => Ready s₀ t) p.1

theorem zeroOut_ct : RelCT isa (Two fun p s => ReadyAt p s ∧ isa.eval .ne s = some true) zeroOut
    fun _ _ => True := by
  unfold zeroOut
  refine RelCT.seq (two_piece (Ψ := fun p => At (fun s₀ t => Ready s₀ t ∧ t.gpr .esi = X86.arg s₀ 0 ∧
      t.gpr .ecx = X86.arg s₀ 1) p.1) [.esp] (pins_at' (P := fun _ s₀ t => Ready s₀ t) Prod.fst
      fun _ _ _ h => h) (by taint_decide)
    fun p t ⟨⟨s₀, A, e, h⟩, _⟩ => WP.mono (zeroHead_ok A h) fun u hu => ⟨s₀, A, e, hu⟩) ?_
  refine two_taint [.esi, .ecx] (fun p t₁ t₂ h₁ h₂ r hr => ?_) (by taint_decide)
  obtain ⟨s₁, _, e₁, _, x₁, c₁⟩ := h₁
  obtain ⟨s₂, _, e₂, _, x₂, c₂⟩ := h₂
  have e := e₁.trans e₂.symm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [x₁, x₂, pub_arg e 0 (by decide)]
  · rw [c₁, c₂, pub_arg e 1 (by decide)]

theorem finalBlock_ct : RelCT isa (Two ReadyAt)
    (.block (clearNonce ++ ([.mov .edx (.mem (Random.arg aUsed)), .mov .eax (.mem (sp oUsed)),
      .store (at_ .edx 0) .eax, .mov .eax (.imm 0), .store (at_ .edx 4) .eax,
      .mov .ebx (.mem (sp oSaveEbx)), .mov .esi (.mem (sp oSaveEsi)),
      .mov .edi (.mem (sp oSaveEdi)), .mov .ebp (.mem (sp oSaveEbp)),
      .mov .eax (.mem (sp oStatus))] : List Instr))) fun _ _ => True := by
  show RelCT isa _ (.block ((clearNonce ++ [.mov .edx (.mem (Random.arg aUsed))]) ++
    [.mov .eax (.mem (sp oUsed)), .store (at_ .edx 0) .eax, .mov .eax (.imm 0), .store (at_ .edx 4) .eax,
      .mov .ebx (.mem (sp oSaveEbx)), .mov .esi (.mem (sp oSaveEsi)),
      .mov .edi (.mem (sp oSaveEdi)), .mov .ebp (.mem (sp oSaveEbp)),
      .mov .eax (.mem (sp oStatus))])) _
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := fun p => At (fun s₀ t => Ready s₀ t ∧ t.gpr .edx = X86.arg s₀ 2) p.1)
    [.esp] (pins_at (P := fun _ s₀ t => Ready s₀ t) Prod.fst fun _ _ _ h => h) (by taint_decide)
    fun p t ⟨s₀, A, e, h⟩ => WP.mono (finPrefix_ok A h) fun u hu => ⟨s₀, A, e, hu⟩) ?_
  refine two_taint [.esp, .edx] (fun p t₁ t₂ h₁ h₂ r hr => ?_) (by taint_decide)
  obtain ⟨s₁, _, e₁, r₁, d₁⟩ := h₁
  obtain ⟨s₂, _, e₂, r₂, d₂⟩ := h₂
  have e := e₁.trans e₂.symm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact esp_of_rf r₁.rf (pub_rBase e ▸ r₂.rf)
  · rw [d₁, d₂, pub_arg e 2 (by decide)]

theorem finish_ct : RelCT isa (Two FinAt) finish fun _ _ => True := by
  unfold finish
  refine RelCT.seq (two_piece (Ψ := fun (p : Pub × Nat) => At (fun s₀ t => Ready s₀ t ∧
      t.zf = some (decide (p.2 = 1))) p.1) [.esp]
    (pins_at (P := fun p s₀ t => Fin s₀ t ∧ (rResult s₀).status = p.2) Prod.fst fun _ _ _ h => h.1.ready)
    (by taint_decide) fun p t ⟨s₀, A, e, Fi, st⟩ => WP.mono (finTest_ok A Fi)
      fun u ⟨h, z⟩ => ⟨s₀, A, e, h, by rw [z, st]⟩) ?_
  refine RelCT.seq (R := Two ReadyAt) (two_ite (fun p t₁ t₂ ⟨_, _, _, _, z₁⟩ ⟨_, _, _, _, z₂⟩ => by
    simp only [eval, z₁, z₂]) ?_ ?_) finalBlock_ct
  · exact two_post (Ψ := ReadyAt) (two_map id (fun p t ⟨⟨s₀, A, e, h, _⟩, hb⟩ => ⟨⟨s₀, A, e, h⟩, hb⟩) zeroOut_ct)
      fun p t ⟨⟨s₀, A, e, h, _⟩, _⟩ => WP.mono (zeroOut_ok A h) fun u hu => ⟨s₀, A, e, hu.1⟩
  · exact two_post (Ψ := ReadyAt) (two_taint [] (fun _ _ _ _ _ _ h => by cases h) (by taint_decide))
      fun p t ⟨⟨s₀, A, e, h, _⟩, _⟩ => WP.block_nil ⟨s₀, A, e, h⟩

/-! ## The body -/

/-- What two runs of the body share: the public data and key bytes, and
the overall status and trace. -/
structure BodyPub (V : Nat → Nat → List Byte → Bool) where
  pub : Pub
  leak : List Nat
  status : Nat
  tr : List Nat

structure BodyFacts (b : BodyPub V) (s₀ : State) : Prop where
  leak : keyLeak s₀ = b.leak
  status : (rResult s₀).status = b.status
  tr : (rResult s₀).trace = b.tr
  valid : KeyValid V s₀

/-- The body's entry, after the frame's allocation. -/
def BodyEntry (b : BodyPub V) (s₀ t : State) : Prop := BodyFacts b s₀ ∧ t = allocated Random.frameBytes s₀

/-- After the entry block. -/
def Entered (b : BodyPub V) (s₀ t : State) : Prop :=
  BodyFacts b s₀ ∧ Ready s₀ t ∧ Saved s₀ t.mem ∧ slot t.mem (rBase s₀) oUsed = 0 ∧
    slot t.mem (rBase s₀) oAttempts = 8

/-- After `prepare`. -/
structure Prepped (b : BodyPub V) (s₀ t : State) : Prop where
  facts : BodyFacts b s₀
  ready : Ready s₀ t
  eax : t.gpr .eax = if 1 < rq s₀ then 1 else 0
  prep : 1 < rq s₀ → Prepared s₀ t
  saved : Saved s₀ t.mem
  used : slot t.mem (rBase s₀) oUsed = 0
  attempts : slot t.mem (rBase s₀) oAttempts = 8

theorem Prepped.fupd {b : BodyPub V} {s₀ t u : State} (h : Prepped b s₀ t) (f : Fupd t u) : Prepped b s₀ u := by
  have hr := h.ready.fupd f
  have hm : u.mem = t.mem := f.mem
  refine ⟨h.facts, hr, by rw [f.gpr]; exact h.eax, fun hq => ?_, by rw [hm]; exact h.saved,
    by rw [hm]; exact h.used, by rw [hm]; exact h.attempts⟩
  have P := h.prep hq
  exact ⟨hr, by rw [hm]; exact P.q, by rw [hm]; exact P.width, by rw [hm]; exact P.mask,
    by rw [hm]; exact P.nonce⟩

theorem prepped_ok {b : BodyPub V} {s₀ t : State} (A : RandomSignABI s₀) (E : Entered b s₀ t) :
    WP isa prepare t (Prepped b s₀) := by
  obtain ⟨Fb, h₁, sv₁, us₁, at₁⟩ := E
  refine WP.mono (prepare_ok A h₁) fun t₂ ⟨ax₂, P₂, h₂, o₂, _⟩ => ?_
  have lo₂ : ∀ d, d + 4 ≤ oQ → slot t₂.mem (rBase s₀) d = slot t.mem (rBase s₀) d := fun d hd =>
    outs_low o₂ (by decide) hd (by unfold oQ at hd; omega_using [hd])
  exact ⟨Fb, h₂, ax₂, P₂, sv₁.of_slots fun d _ hd => lo₂ d (by unfold oQ; omega_using [hd]),
    by rw [lo₂ _ (by decide)]; exact us₁, by rw [lo₂ _ (by decide)]; exact at₁⟩

/-- After the test of q. -/
def Checked (b : BodyPub V) (s₀ t : State) : Prop := Prepped b s₀ t ∧ t.zf = some (!decide (1 < rq s₀))

/-- q ≤ 1: the status, and the end. -/
theorem small_fin {b : BodyPub V} {s₀ t : State} (A : RandomSignABI s₀) (C : Checked b s₀ t) (hq : ¬ 1 < rq s₀) :
    WP isa (.block [.store (sp oStatus) .eax]) t fun u => Fin s₀ u ∧ (rResult s₀).status = b.status := by
  obtain ⟨Pp, _⟩ := C
  have hR := rResult_small A hq
  have ax₃ : t.gpr .eax = BitVec.ofNat 32 (rResult s₀).status := by
    rw [Pp.eax, hR]; simp only [hq, ↓reduceIte]; rfl
  refine wp_slot Pp.ready.rf (by decide) ax₃ fun t₄ f₄ m₄ g₄ r₄ w₄ _ _ => WP.block_nil ?_
  have h₄ : Ready s₀ t₄ := Pp.ready.congr (rs := []) ⟨fun r _ => by rw [g₄], r₄, w₄⟩
    (by rw [m₄]; exact frame_store s₀ _ (by decide) _)
  refine ⟨⟨h₄, ?_, by rw [m₄, slot_write_self], fun e => by rw [hR] at e; exact absurd e (by decide),
    Pp.saved.of_slots fun d _ hd => by rw [m₄, slot_write_ne _ _ _ (by unfold oStatus; omega_using [hd]) (by omega_using [hd])
      (by decide)]⟩, Pp.facts.status⟩
  rw [m₄, slot_write_ne _ _ _ (by decide) (by decide) (by decide), Pp.used, hR]; rfl

theorem body_ct (F : SignFn) :
    RelCT isa (Two fun (b : BodyPub F.valid) => At (BodyEntry b) b.pub) (body F.name F.code)
      fun _ _ => True := by
  unfold body
  refine RelCT.seq (two_piece (Ψ := fun b => At (Entered b) b.pub) [.esp]
    (fun b t₁ t₂ ⟨s₁, _, e₁, _, h₁⟩ ⟨s₂, _, e₂, _, h₂⟩ r hr => by
      rw [List.mem_singleton] at hr; subst hr h₁ h₂
      rw [allocated_esp, allocated_esp, pub_esp (e₁.trans e₂.symm)]) (by taint_decide)
    fun b t ⟨s₀, A, e, Fb, ht⟩ => ?_) ?_
  · subst ht
    exact WP.mono (entry_ok (alloc_ready A) (allocated_gpr _ _ (by decide)) (allocated_gpr _ _ (by decide))
      (allocated_gpr _ _ (by decide)) (allocated_gpr _ _ (by decide)))
      fun u ⟨h, sv, us, at₁, _⟩ => ⟨s₀, A, e, Fb, h, sv, us, at₁⟩
  refine RelCT.seq (two_post (Ψ := fun b => At (Prepped b) b.pub)
    (two_map BodyPub.pub (fun b t ⟨s₀, A, e, E⟩ => ⟨s₀, A, e, E.2.1⟩) prepare_ct)
    fun b t ⟨s₀, A, e, E⟩ => WP.mono (prepped_ok A E) fun u hu => ⟨s₀, A, e, hu⟩) ?_
  refine RelCT.seq (two_piece (Ψ := fun b => At (Checked b) b.pub) [.esp]
    (pins_at BodyPub.pub fun _ _ _ h => h.ready) (by taint_decide)
    fun b t ⟨s₀, A, e, Pp⟩ => wp_cmpi fun u f _ z => WP.block_nil ⟨s₀, A, e, Pp.fupd f, ?_⟩) ?_
  · rw [z, Pp.eax]
    by_cases hq : 1 < rq s₀ <;> simp [hq]
  refine RelCT.seq (R := Two FinAt) (two_ite (fun b t₁ t₂ ⟨s₁, _, e₁, _, z₁⟩ ⟨s₂, _, e₂, _, z₂⟩ => by
    simp only [eval, z₁, z₂, pub_rq (e₁.trans e₂.symm)]) ?_ ?_) finish_ct
  · refine (two_post (Ψ := fun (b : BodyPub F.valid) => At (fun s₀ t => Fin s₀ t ∧ (rResult s₀).status = b.status) b.pub)
      (two_taint [.esp] (pins_at' BodyPub.pub fun _ _ _ h => h.1.ready) (by taint_decide))
      fun b t ⟨⟨s₀, A, e, C⟩, hb⟩ => WP.mono (small_fin A C (by
        have := C.2; simp only [eval, this, Option.some.injEq, Bool.not_eq_true', decide_eq_false_iff_not] at hb
        exact hb)) fun u hu => ⟨s₀, A, e, hu⟩).mono (fun _ _ h => h)
      fun _ _ ⟨b, h₁, h₂⟩ => ⟨(b.pub, b.status), h₁, h₂⟩
  · refine two_map (fun b => (⟨b.pub, b.leak, 0, 8, b.tr, b.status⟩ : AttPub F.valid))
      (fun b t ⟨⟨s₀, A, e, Pp, z⟩, hb⟩ => ⟨rfl, s₀, A, e, ?_, Pp.facts.status⟩) (attemptLoop_ct F 8)
    have hq : 1 < rq s₀ := by
      simp only [eval, z, Option.some.injEq, Bool.not_eq_false', decide_eq_true_eq] at hb
      exact hb
    have P := Pp.prep hq
    have hql := rQBytes_le A
    have er : randomSignRemaining (rInput s₀) 0 8 = rResult s₀ := by rw [rResult_loop A]; rfl
    refine ⟨⟨hq, (by decide : 1 ≤ 8), (by decide : 8 ≤ 8), Pp.facts.leak, by
      show (randomSignRemaining (rInput s₀) 0 8).trace = b.tr; rw [er]; exact Pp.facts.tr, Pp.facts.valid⟩, ?_⟩
    refine ⟨⟨(slot t.mem (rBase s₀) oDraws).toNat, ⟨Pp.ready, P.q, P.width, P.mask, Pp.used,
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], fun i hi => P.nonce i (by omega_using [hql, hi]), Nat.zero_le _⟩⟩,
      Pp.attempts, Pp.saved, ?_⟩
    exact ⟨by rw [er], by rw [er], by rw [er]⟩

end VG.Proof.Dsa.X86
