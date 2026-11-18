module

public import VerifiedGarbage.Proof.MlKem.PPC64LE.RowSum
public import VerifiedGarbage.Proof.MlKem.PPC64LE.CallsCT
public import VerifiedGarbage.Proof.MlKem.PPC64LE.HashCT
import VerifiedGarbage.Proof.MlKem.PPC64LE.Loops
import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.RowSum
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.CallsCT
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.HashCT
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Loops
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MlKem.PPC64LE.Prf
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Prf

/-! ### `MlKem.PPC64LE.PrfCT`, which the modules that import this one used -/

section

/-!
# ML-KEM on PPC64LE: the `PRF`s in constant time

As on 32-bit ARM (`Proof/MlKem/Arm/RowCT.lean`): two runs of `prfLoop` with
the same `scratch` leak the same trace (`prfLoop_ct`), since every address is
`scratch` plus an offset that depends only on the counter `N`, and the calls
take the same pointers in both runs. What each run is at each point comes
from its correctness (`relct_wp`).
-/

@[expose] public section

namespace VG.Proof.MlKem.PPC64LE

open VG VG.PPC64LE VG.Impl.MlKem.PPC64LE
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.PPC64LE.Sample (taint_block relct_wp)

theorem prf_hashOk {L : Lay} {s : State} (hc : Ctx L s) :
    HashOk L (fun _ => 0) [⟨.r31, oSigma, 33⟩] [⟨.r31, oPrf, 128⟩] s := by
  refine ⟨hc, fun p hp => ?_, fun p hp => ?_⟩ <;> rw [List.mem_singleton] at hp <;> subst hp
  · exact ⟨by decide, hc.r31, by decide, by decide, by decide, hc.sepAll0 (by decide) (by decide),
      mem_rd_wr hc.cw⟩
  · exact ⟨by decide, hc.r31, by decide, by decide, by decide, hc.sepAll0 (by decide) (by decide), hc.cw⟩

/-- A state `prfBody` runs from, as far as its timing is concerned. -/
abbrev PS (L : Lay) (N : Nat) (s : State) : Prop := Ctx L s ∧ s.gpr .r26 = BitVec.ofNat 64 N

theorem prfBody_ct {K : KemLay} (hK : K.WF) {L : Lay} (withNtt : Bool) {N₁ N : Nat} (hN : N < N₁)
    (hN₁ : N₁ ≤ 2 * K.k + 1) :
    RelCT isa (fun a b => PS L N a ∧ PS L N b) (K.prfBody withNtt N₁) fun _ _ => True := by
  have k4 := hK.k4
  -- the counter
  refine RelCT.seq (R := fun a b => PS L N a ∧ PS L N b)
    (relct_wp (taint_block [.r31] (fun a b hab => hab.1.1.sp_eq hab.2.1) (fun a b hab r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [hab.1.1.r31, hab.2.1.r31]) (by taint_decide))
      fun a b hab => ⟨WP.mono (stb26_ok hab.1.1 (by omega_using [hN, hN₁, k4]) hab.1.2) fun s' ⟨k', _⟩ =>
          ⟨k'.ctx (by decide) hab.1.1, by rw [k'.cs .r26 (by decide) (by decide), hab.1.2]⟩,
        WP.mono (stb26_ok hab.2.1 (by omega_using [hN, hN₁, k4]) hab.2.2) fun s' ⟨k', _⟩ =>
          ⟨k'.ctx (by decide) hab.2.1, by rw [k'.cs .r26 (by decide) (by decide), hab.2.2]⟩⟩) ?_
  -- `PRF`
  have hh : ∀ s, PS L N s → WP isa (hash 136 0x1f [⟨.r31, oSigma, 33⟩] [⟨.r31, oPrf, 128⟩]) s (PS L N) :=
    fun s h => WP.mono (hash_ok (idx := fun _ => 0) rate136 (by decide) h.1 (List.cons_ne_nil _ _)
      (prf_hashOk h.1).ins (prf_hashOk h.1).outs (List.pairwise_singleton _ _)) fun s' ⟨k', _⟩ =>
      ⟨h.1.kept k', by rw [k'.cs .r26 (by decide), h.2]⟩
  refine RelCT.seq (R := fun a b => PS L N a ∧ PS L N b)
    (relct_wp (hash_ct rate136 (by decide) (List.cons_ne_nil _ _) fun a b hab =>
      ⟨prf_hashOk hab.1.1, prf_hashOk hab.2.1, hab.1.1.sp_eq hab.2.1⟩) fun a b hab => ⟨hh a hab.1, hh b hab.2⟩) ?_
  -- `SamplePolyCBD₂`
  let F : State → Prop := fun s => PS L N s ∧ s.gpr .r3 = L.ptr 0 + BitVec.ofNat 64 oPrf ∧
    s.gpr .r4 = L.ptr 0 + BitVec.ofNat 64 (oPoly (K.k + N))
  have eo : oPoly (K.k + N) = oPoly K.k + 1024 * N := by unfold oPoly; omega_using []
  have ha : ∀ s, PS L N s → WP isa (.block (.addi .r3 .r31 oPrf :: slotAt .r4 .r26 (oPoly K.k))) s F :=
    fun s h => WP.mono (cbdArgs_ok hK h.1.r31 h.2) fun s' ⟨o', g3, g4⟩ =>
      ⟨⟨h.1.only o', by rw [o'.cs .r26 (by decide), h.2]⟩, g3, by rw [g4, slot_eq _ (by offs), ← eo]⟩
  refine RelCT.seq (R := fun a b => F a ∧ F b)
    (relct_wp (relct_noMem (by rfl)) fun a b hab => ⟨ha a hab.1, ha b hab.2⟩) ?_
  have hcb : ∀ s, F s → WP isa callCbd2 s (PS L N) := fun s h =>
    cbd2L h.1.1.ok h.2.1 h.2.2 (h.1.1.sep00 (by offs) (by offs) (by offs)) (mem_rd_wr h.1.1.cw) h.1.1.cw
      fun s' k' _ => ⟨h.1.1.kept k', by rw [k'.cs .r26 (by decide), h.1.2]⟩
  refine RelCT.seq (R := fun a b => PS L N a ∧ PS L N b)
    (relct_wp (RelCT.callT cbd2T (regs2 fun a b hab =>
      ⟨hab.1.1.1.sp_eq hab.2.1.1, by rw [hab.1.2.1, hab.2.2.1], by rw [hab.1.2.2, hab.2.2.2]⟩))
      fun a b hab => ⟨hcb a hab.1, hcb b hab.2⟩) ?_
  -- the NTT, and the counter
  cases withNtt
  · exact RelCT.seq (R := fun _ _ => True) (relct_noMem (by rfl)) (relct_noMem (by rfl))
  · refine RelCT.seq (R := fun _ _ => True) ?_ (relct_noMem (by rfl))
    let G : State → Prop := fun s => s.sp = s.sp ∧ s.gpr .r3 = L.ptr 0 + BitVec.ofNat 64 (oPoly (K.k + N)) ∧
      s.gpr .r4 = L.ptr 0 + BitVec.ofNat 64 K.oNtt
    have hn : ∀ s, PS L N s → WP isa (.block (slotAt .r3 .r26 (oPoly K.k) ++ [.addi .r4 .r31 K.oNtt])) s
        fun s' => G s' ∧ Ctx L s' := fun s h =>
      WP.mono (nttArgs_ok hK h.1.r31 h.2) fun s' ⟨o', g3, g4⟩ =>
        ⟨⟨rfl, by rw [g3, slot_eq _ (by offs), ← eo], g4⟩, h.1.only o'⟩
    exact RelCT.seq (R := fun a b => (G a ∧ Ctx L a) ∧ (G b ∧ Ctx L b))
      (relct_wp (relct_noMem (by rfl)) fun a b hab => ⟨hn a hab.1, hn b hab.2⟩)
      (RelCT.callT nttT (regs2 fun a b hab =>
        ⟨hab.1.2.sp_eq hab.2.2, by rw [hab.1.1.2.1, hab.2.1.2.1], by rw [hab.1.1.2.2, hab.2.1.2.2]⟩))

theorem prfLoop_ct {K : KemLay} (hK : K.WF) {L : Lay} (withNtt : Bool) {N₀ N₁ : Nat} (h01 : N₀ < N₁)
    (hN₁ : N₁ ≤ 2 * K.k + 1) {s₀₁ s₀₂ : State} (hc₁ : Ctx L s₀₁) (hc₂ : Ctx L s₀₂) {σ₁ σ₂ : List Byte}
    (hσ₁ : bytesAt s₀₁.mem (L.A 0 oSigma) 32 = σ₁) (hσ₂ : bytesAt s₀₂.mem (L.A 0 oSigma) 32 = σ₂) :
    RelCT isa (fun a b => a = s₀₁ ∧ b = s₀₂) (K.prfLoop withNtt N₀ N₁) fun _ _ => True := by
  have k4 := hK.k4
  refine RelCT.seq (R := fun a b => PrfInv K L withNtt σ₁ N₀ N₁ s₀₁ 0 a ∧ PrfInv K L withNtt σ₂ N₀ N₁ s₀₂ 0 b)
    (relct_wp (relct_noMem (by rfl)) fun a b hab => ⟨?_, ?_⟩)
    (RelCT.mono (relct_loop_nz (I₁ := PrfInv K L withNtt σ₁ N₀ N₁ s₀₁)
      (I₂ := PrfInv K L withNtt σ₂ N₀ N₁ s₀₂) (N := N₁ - N₀) (by omega_using [h01]) fun t ht => ?_)
      (fun _ _ h => h) fun _ _ _ => trivial)
  · rw [hab.1]
    exact WP.mono (li26_ok (by omega_using [h01, hN₁, k4])) fun s₁ ⟨k₁, g₁, m₁⟩ =>
      ⟨k₁.mono (fun _ h => absurd h List.not_mem_nil), by rw [g₁, Nat.add_zero], by rw [m₁]; exact hσ₁,
        fun N h1 h2 => absurd h2 (by omega_using [h1])⟩
  · rw [hab.2]
    exact WP.mono (li26_ok (by omega_using [h01, hN₁, k4])) fun s₁ ⟨k₁, g₁, m₁⟩ =>
      ⟨k₁.mono (fun _ h => absurd h List.not_mem_nil), by rw [g₁, Nat.add_zero], by rw [m₁]; exact hσ₂,
        fun N h1 h2 => absurd h2 (by omega_using [h1])⟩
  -- one iteration: the body's timing from where it runs, and each run by correctness
  exact relct_wp (RelCT.mono (prfBody_ct hK (N := N₀ + t) withNtt (by omega_using [ht]) hN₁) (fun a b hab =>
      ⟨⟨hab.1.kx.ctx (by decide) hc₁, hab.1.r26⟩, ⟨hab.2.kx.ctx (by decide) hc₂, hab.2.r26⟩⟩) fun _ _ h => h)
    fun a b hab => ⟨prfStep_ok hK hc₁ withNtt hN₁ ht hab.1, prfStep_ok hK hc₂ withNtt hN₁ ht hab.2⟩

end VG.Proof.MlKem.PPC64LE

end

end

/-!
# ML-KEM on PPC64LE: the rows and the dot product in constant time

As on 32-bit ARM (`Proof/MlKem/Arm/RowCT.lean`): two runs of `rowSum` or of
`dot` whose layouts agree leak the same trace (`rowSum_ct`, `dot_ct`). Every
address is a pointer of the layout plus an offset that depends only on the
counters, which are the same in both runs; the only branch on data is the
selection of the entry, on the result of `SampleNTT`, which the contract
lets the function leak, since it is a function of `ρ`.
-/

@[expose] public section

namespace VG.Proof.MlKem.PPC64LE

open VG VG.PPC64LE VG.Impl.MlKem.PPC64LE
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.PPC64LE.Sample (taint_block relct_wp)

/-- Constant time from any two states related by `P`, proved for each pair. -/
theorem RelCT.pointwise {P Q : State → State → Prop} {c : Prog isa}
    (h : ∀ s₁ s₂, P s₁ s₂ → RelCT isa (fun a b => a = s₁ ∧ b = s₂) c Q) : RelCT isa P c Q :=
  fun s₁ s₂ _ _ _ _ hp e₁ e₂ => h s₁ s₂ hp s₁ s₂ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂

/-! ## The rows -/

section
variable {K : KemLay} (hT : K.CallsOk) {L : Lay} {ρ : List Byte} {v₁ v₂ : Nat → Poly} {i : Nat}
  {fl₁ fl₂ : Bool} {s₀₁ s₀₂ : State}

include hT in
theorem rowBody_ct {transpose : Bool} (hp₁ : RowPre K L ρ v₁ i fl₁ s₀₁) (hp₂ : RowPre K L ρ v₂ i fl₂ s₀₂)
    {j : Nat} (hj : j < K.k) :
    RelCT isa (fun a b => RowInv K L transpose ρ v₁ i fl₁ s₀₁ j a ∧ RowInv K L transpose ρ v₂ i fl₂ s₀₂ j b)
      (K.rowBody transpose) fun _ _ => True := by
  have hK := hp₁.wf
  -- the seed, and the arguments of `SampleNTT`
  refine RelCT.seq (R := fun a b => RA K L transpose ρ v₁ i fl₁ s₀₁ j a ∧ RA K L transpose ρ v₂ i fl₂ s₀₂ j b)
    (relct_wp ?_ fun a b hab => ⟨rowA_ok hp₁ hj hab.1, rowA_ok hp₂ hj hab.2⟩) ?_
  · refine (hT.seedT transpose).relct (fun a b hab => ?_) fun a b hab r hr => ?_
    · rw [(hab.1.kx.ctx (by decide) hp₁.ctx).sp_eq (hab.2.kx.ctx (by decide) hp₂.ctx)]
    · rw [List.mem_singleton] at hr; subst hr
      rw [(hab.1.kx.ctx (by decide) hp₁.ctx).r31, (hab.2.kx.ctx (by decide) hp₂.ctx).r31]
  -- `SampleNTT`
  refine RelCT.seq (R := fun a b => RB K L transpose ρ v₁ i fl₁ s₀₁ j a ∧ RB K L transpose ρ v₂ i fl₂ s₀₂ j b)
    (relct_wp (sample_ct (L := L) (i := 0) (o := oSeed) (j := 0) (o' := K.oAhat) (k := 0) (o'' := K.oSample)
      (fun a b hab => ?_) (sepF hp₁).1 (sepF hp₁).2.1 (sepF hp₁).2.2.1 (sepF hp₁).2.2.2.1
      (sepF hp₁).2.2.2.2.1 (sepF hp₁).2.2.2.2.2)
      fun a b hab => ⟨rowB_ok hp₁ hab.1, rowB_ok hp₂ hab.2⟩) ?_
  · have ca := hab.1.rs.ctx hp₁
    have cb := hab.2.rs.ctx hp₂
    exact ⟨ca, cb, hab.1.r3, hab.1.r4, hab.1.r5, hab.2.r3, hab.2.r4, hab.2.r5,
      by rw [hab.1.seed, hab.2.seed], mem_rd_wr ca.cw, ca.cw, ca.cw, mem_rd_wr cb.cw, cb.cw, cb.cw⟩
  -- the flag
  refine RelCT.seq (R := fun a b => RC K L transpose ρ v₁ i fl₁ s₀₁ j a ∧ RC K L transpose ρ v₂ i fl₂ s₀₂ j b)
    (relct_wp (relct_noMem (by rfl)) fun a b hab => ⟨rowC_ok hp₁ hab.1, rowC_ok hp₂ hab.2⟩) ?_
  -- the entry
  refine RelCT.seq (R := fun a b => RD K L transpose ρ v₁ i fl₁ s₀₁ j a ∧ RD K L transpose ρ v₂ i fl₂ s₀₂ j b)
    (relct_wp (RelCT.ite (fun a b hab => by
      show isa.eval (.zero .d .r3) a = isa.eval (.zero .d .r3) b
      simp only [VG.PPC64LE.eval, State.read, hab.1.r3, hab.2.r3])
      (relct_noMem (by rfl)) (relct_noMem (by rfl)))
      fun a b hab => ⟨rowD_ok hp₁ hj hab.1, rowD_ok hp₂ hj hab.2⟩) ?_
  -- the product
  refine RelCT.seq (R := fun a b => RE K L transpose ρ v₁ i fl₁ s₀₁ j a ∧ RE K L transpose ρ v₂ i fl₂ s₀₂ j b)
    (relct_wp (relct_noMem (by rfl)) fun a b hab => ⟨rowE_ok hp₁ hj hab.1, rowE_ok hp₂ hj hab.2⟩) ?_
  refine RelCT.seq (R := fun a b => RF K L transpose ρ v₁ i fl₁ s₀₁ j a ∧ RF K L transpose ρ v₂ i fl₂ s₀₂ j b)
    (relct_wp (RelCT.callT mulT (regs4 fun a b hab =>
      ⟨(hab.1.rd.rs.ctx hp₁).sp_eq (hab.2.rd.rs.ctx hp₂), by rw [hab.1.r3, hab.2.r3],
        by rw [hab.1.rd.r4, hab.2.rd.r4], by rw [hab.1.r5, hab.2.r5], by rw [hab.1.r6, hab.2.r6]⟩))
      fun a b hab => ⟨rowF_ok hp₁ hj hab.1, rowF_ok hp₂ hj hab.2⟩) ?_
  -- the sum, and the counter
  refine RelCT.seq (R := fun a b => RG K L transpose ρ v₁ i fl₁ s₀₁ j a ∧ RG K L transpose ρ v₂ i fl₂ s₀₂ j b)
    (relct_wp (relct_noMem (by rfl)) fun a b hab => ⟨rowG_ok hp₁ hab.1, rowG_ok hp₂ hab.2⟩) ?_
  exact RelCT.seq (R := fun _ _ => True)
    (RelCT.callT addT (regs2 fun a b hab =>
      ⟨(hab.1.rf.rs.ctx hp₁).sp_eq (hab.2.rf.rs.ctx hp₂), by rw [hab.1.r3, hab.2.r3],
        by rw [hab.1.r4, hab.2.r4]⟩))
    (relct_noMem (by rfl))
where
  sepF (hp : RowPre K L ρ v₁ i fl₁ s₀₁) :
      sepB L.sizes (0, oSeed, 34) (0, K.oAhat, 1024) = true ∧
      sepB L.sizes (0, oSeed, 34) (0, K.oSample, 2048) = true ∧
      sepB L.sizes (0, K.oAhat, 1024) (0, K.oSample, 2048) = true ∧
      sepB L.sizes (0, oSeed, 34) (1, 0, 48) = true ∧ sepB L.sizes (0, K.oAhat, 1024) (1, 0, 48) = true ∧
      sepB L.sizes (0, K.oSample, 2048) (1, 0, 48) = true := by
    have hK := hp.wf
    exact ⟨hp.ctx.sep00 (by offs) (by offs) (by offs), hp.ctx.sep00 (by offs) (by offs) (by offs),
      hp.ctx.sep00 (by offs) (by offs) (by offs), hp.ctx.sep01 (by offs) (by offs),
      hp.ctx.sep01 (by offs) (by offs), hp.ctx.sep01 (by offs) (by offs)⟩

include hT in
theorem rowSum_ct {transpose : Bool} (hp₁ : RowPre K L ρ v₁ i fl₁ s₀₁) (hp₂ : RowPre K L ρ v₂ i fl₂ s₀₂) :
    RelCT isa (fun a b => a = s₀₁ ∧ b = s₀₂) (K.rowSum transpose) fun _ _ => True := by
  have hK := hp₁.wf
  have lf := row_lf hK
  let Z : State → State → Prop := fun s₀ s =>
    Kept (L.RL [(0, K.oAcc, 1024)]) s₀ s ∧ PolyIs s.mem (L.A 0 K.oAcc) zero
  refine RelCT.seq (R := fun a b => Z s₀₁ a ∧ Z s₀₂ b)
    (relct_wp (hT.zeroT.relct (fun a b hab => by
      rw [hab.1, hab.2, hp₁.ctx.sp_eq hp₂.ctx]) (fun a b hab r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [hab.1, hab.2, hp₁.ctx.r31, hp₂.ctx.r31])) fun a b hab =>
      ⟨by rw [hab.1]; exact zeroPoly_ok hp₁.ctx lf.2.2.1,
        by rw [hab.2]; exact zeroPoly_ok hp₂.ctx lf.2.2.1⟩) ?_
  have init : ∀ {v : Nat → Poly} {fl : Bool} {s₀ : State}, RowPre K L ρ v i fl s₀ → ∀ s₁, Z s₀ s₁ →
      WP isa (.block [.li .r25 0]) s₁ (RowInv K L transpose ρ v i fl s₀ 0) :=
    fun {v fl s₀} hp s₁ ⟨k₁, z₁⟩ => WP.mono (li_ok .r25 (N := 0) (by decide)) fun s₂ ⟨k₂, g₂, m₂⟩ =>
      ⟨((k₁.x _).subL hp.ctx lf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2).trans
          ((k₂.weaken (by simp)).mono (fun _ h => absurd h List.not_mem_nil)),
        g₂, by rw [k₂.cs .r24 (by decide) (by decide), k₁.cs .r24 (by decide), hp.r24]
               simp [okRow], by rw [m₂]; exact z₁⟩
  refine RelCT.seq (R := fun a b => RowInv K L transpose ρ v₁ i fl₁ s₀₁ 0 a ∧
      RowInv K L transpose ρ v₂ i fl₂ s₀₂ 0 b)
    (relct_wp (relct_noMem (by rfl)) fun a b hab => ⟨init hp₁ a hab.1, init hp₂ b hab.2⟩) ?_
  exact RelCT.mono (relct_loop_nz (N := K.k) (by have := hK.k1; omega_using [this]) fun j hj =>
    relct_wp (rowBody_ct hT hp₁ hp₂ hj) fun a b hab => ⟨rowBody_ok hp₁ hj hab.1, rowBody_ok hp₂ hj hab.2⟩)
    (fun _ _ h => h) fun _ _ _ => trivial

end

/-! ## The dot product -/

section
variable {K : KemLay} (hK : K.WF) {L : Lay} {a₁ v₁ a₂ v₂ : Nat → Poly} {x y : State} (hc₁ : Ctx L x)
    (hc₂ : Ctx L y)
    (ha₁ : ∀ j < K.k, PolyIs x.mem (L.A 0 (oPoly j)) (a₁ j))
    (hv₁ : ∀ j < K.k, PolyIs x.mem (L.A 0 (oPoly (K.k + j))) (v₁ j))
    (ha₂ : ∀ j < K.k, PolyIs y.mem (L.A 0 (oPoly j)) (a₂ j))
    (hv₂ : ∀ j < K.k, PolyIs y.mem (L.A 0 (oPoly (K.k + j))) (v₂ j))
include hK hc₁ hc₂ ha₁ hv₁ ha₂ hv₂

theorem dotBody_ct {j : Nat} (hj : j < K.k) :
    RelCT isa (fun a b => DotInv K L a₁ v₁ x j a ∧ DotInv K L a₂ v₂ y j b) K.dotBody fun a b =>
      (DotInv K L a₁ v₁ x (j + 1) a ∧ (a.gpr .r0 != 0) = decide (j + 1 ≠ K.k)) ∧
      (DotInv K L a₂ v₂ y (j + 1) b ∧ (b.gpr .r0 != 0) = decide (j + 1 ≠ K.k)) := by
  refine relct_wp (RelCT.pointwise fun u w ⟨hu, hw⟩ => ?_) fun a b hab =>
    ⟨dotBody_ok hK hc₁ ha₁ hv₁ hj hab.1, dotBody_ok hK hc₂ ha₂ hv₂ hj hab.2⟩
  refine RelCT.seq (R := fun (a b : State) =>
      (Only u a ∧ a.gpr .r3 = L.A 0 K.oTmp ∧ a.gpr .r4 = L.A 0 (oPoly j) ∧
        a.gpr .r5 = L.A 0 (oPoly (K.k + j)) ∧ a.gpr .r6 = L.A 0 K.oNtt) ∧
      (Only w b ∧ b.gpr .r3 = L.A 0 K.oTmp ∧ b.gpr .r4 = L.A 0 (oPoly j) ∧
        b.gpr .r5 = L.A 0 (oPoly (K.k + j)) ∧ b.gpr .r6 = L.A 0 K.oNtt))
    (relct_wp (relct_noMem (by rfl)) fun a b hab => ⟨by rw [hab.1]; exact dot1_ok hK hc₁ hj hu,
      by rw [hab.2]; exact dot1_ok hK hc₂ hj hw⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => DB K L a₁ v₁ x j a ∧ DB K L a₂ v₂ y j b)
    (relct_wp (RelCT.callT mulT (regs4 fun a b hab =>
      ⟨by rw [hab.1.1.sp, hab.2.1.sp]
          exact (hu.kx.ctx (by decide) hc₁).sp_eq (hw.kx.ctx (by decide) hc₂), by rw [hab.1.2.1, hab.2.2.1],
        by rw [hab.1.2.2.1, hab.2.2.2.1], by rw [hab.1.2.2.2.1, hab.2.2.2.2.1],
        by rw [hab.1.2.2.2.2, hab.2.2.2.2.2]⟩))
      fun a b ⟨⟨o₁, m3, m4, m5, m6⟩, ⟨o₂, n3, n4, n5, n6⟩⟩ =>
        ⟨dot2_ok hK hc₁ ha₁ hv₁ hj hu o₁ m3 m4 m5 m6, dot2_ok hK hc₂ ha₂ hv₂ hj hw o₂ n3 n4 n5 n6⟩) ?_
  refine RelCT.seq (R := fun (a b : State) =>
      (DB K L a₁ v₁ x j a ∧ a.gpr .r3 = L.A 0 K.oAcc ∧ a.gpr .r4 = L.A 0 K.oTmp) ∧
      (DB K L a₂ v₂ y j b ∧ b.gpr .r3 = L.A 0 K.oAcc ∧ b.gpr .r4 = L.A 0 K.oTmp))
    (relct_wp (relct_noMem (by rfl)) fun a b hab =>
      ⟨dot3_ok hK hc₁ hab.1, dot3_ok hK hc₂ hab.2⟩) ?_
  exact RelCT.seq (R := fun _ _ => True)
    (RelCT.callT addT (regs2 fun a b hab =>
      ⟨(hab.1.1.kx.ctx (by decide) hc₁).sp_eq (hab.2.1.kx.ctx (by decide) hc₂),
        by rw [hab.1.2.1, hab.2.2.1], by rw [hab.1.2.2, hab.2.2.2]⟩))
    (relct_noMem (by rfl))

theorem dot_ct (hT : K.CallsOk) : RelCT isa (fun a b => a = x ∧ b = y) K.dot fun _ _ => True := by
  have lf := row_lf hK
  let Z : State → State → Prop := fun s₀ s =>
    Kept (L.RL [(0, K.oAcc, 1024)]) s₀ s ∧ PolyIs s.mem (L.A 0 K.oAcc) zero
  refine RelCT.seq (R := fun a b => Z x a ∧ Z y b)
    (relct_wp (hT.zeroT.relct (fun a b hab => by rw [hab.1, hab.2, hc₁.sp_eq hc₂])
      (fun a b hab r hr => by
        rw [List.mem_singleton] at hr; subst hr; rw [hab.1, hab.2, hc₁.r31, hc₂.r31])) fun a b hab =>
      ⟨by rw [hab.1]; exact zeroPoly_ok hc₁ lf.2.2.1, by rw [hab.2]; exact zeroPoly_ok hc₂ lf.2.2.1⟩) ?_
  have init : ∀ {a v : Nat → Poly} {s₀ : State}, Ctx L s₀ → ∀ s₁, Z s₀ s₁ →
      WP isa (.block [.li .r25 0]) s₁ (DotInv K L a v s₀ 0) :=
    fun {a v s₀} hc s₁ ⟨k₁, z₁⟩ => WP.mono (li_ok .r25 (N := 0) (by decide)) fun s₂ ⟨k₂, g₂, m₂⟩ =>
      ⟨((k₁.x _).subL hc (by kdecide)).trans (k₂.mono (fun _ h => absurd h List.not_mem_nil)), g₂,
        by rw [m₂]; exact z₁⟩
  refine RelCT.seq (R := fun a b => DotInv K L a₁ v₁ x 0 a ∧ DotInv K L a₂ v₂ y 0 b)
    (relct_wp (relct_noMem (by rfl)) fun a b hab => ⟨init hc₁ a hab.1, init hc₂ b hab.2⟩) ?_
  exact RelCT.mono (relct_loop_nz (N := K.k) (by have := hK.k1; omega_using [this]) fun j hj =>
      dotBody_ct hK hc₁ hc₂ ha₁ hv₁ ha₂ hv₂ hj)
    (fun _ _ h => h) fun _ _ _ => trivial

end

end VG.Proof.MlKem.PPC64LE
