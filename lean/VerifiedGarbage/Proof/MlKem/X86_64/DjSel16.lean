module

public import VerifiedGarbage.Proof.MlKem.X86_64.Top16Ctl
public import VerifiedGarbage.Proof.MlKem.X86_64.Narrow
public import VerifiedGarbage.Proof.MlKem.X86_64.KgBase
public import VerifiedGarbage.Proof.MlKem.X86_64.EkFusedCT16
public meta import VerifiedGarbage.Proof.MlKem.X86_64.Top16Ctl
meta import VerifiedGarbage.Proof.MlKem.X86_64.EkFusedCT16
meta import VerifiedGarbage.Proof.MlKem.X86_64.Narrow
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.MlKem.X86_64.EncTop
meta import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
import VerifiedGarbage.Proof.MlKem.X86_64.EkFused16
meta import VerifiedGarbage.Proof.MlKem.X86_64.EkFused16
public import VerifiedGarbage.Proof.MlKem.X86_64.EkFrag16
meta import VerifiedGarbage.Proof.MlKem.X86_64.EkFrag16
public import VerifiedGarbage.Proof.MlKem.X86_64.DcTop
meta import VerifiedGarbage.Proof.MlKem.X86_64.DcTop
public import VerifiedGarbage.Impl.MlKem.X86_64.DecapsJ16
meta import VerifiedGarbage.Impl.MlKem.X86_64.DecapsJ16
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.X86_64.EncTop

/-! ### `MlKem.X86_64.DjFusedCT16`, which this module and modules that import it used -/

section

/-! ### `MlKem.X86_64.DjFused16`, which this module and modules that import it used -/

section

/-! ### `MlKem.X86_64.DcTop16`, which only this module used -/

section

/-!
# ML-KEM on x86-64: the end of decapsulation's re-encryption, with 16-bit polynomials

The state after the re-encryption with 16-bit polynomials (`Enc16.lean`)
writes `c'` to `oCT16` (`EncO16`), the input of the choice of the key
(`EncO16.sel`), for `kemDecapsJ16_correct` (`DjFused16.lean`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace Decaps16

open Decaps

/-- The end of the re-encryption. -/
abbrev EncO16 {K : Kem16} (W : Dc16Wf K) (σ s : State) : Prop :=
  Enc16.EOut16 K (dcX W.toDcWfB σ) (sc oCT16) (dcEk K.L σ) (dcM' K.L σ) (dcG K.L σ).2 s

theorem EncO16.sel {K : Kem16} {W : Dc16Wf K} {σ s : State} (h : EncO16 W σ s) : SelIn K.L oCT16 σ s :=
  ⟨h.out.1, h.out.2, h.r15, h.ct⟩

end Decaps16

end VG.Proof.MlKem.X86_64

end

end

/-! ### `MlKem.X86_64.DjFrag16`, which this module and modules that import it used -/

section

/-!
# ML-KEM on x86-64: decapsulation hashing `z ‖ c` in the matrix's fragments, the fragments

As `EkFrag16.lean`, for `kemDecapsJ16`'s fragments (`DecapsJ16.frag`):
before them, decapsulation knows `K'` at `G` but not yet `K̄`, so the
inputs of the re-encryption (`Enc16.EB16`) are in the context `dcXG`, which
keeps `DC` and `K'` (`DCG`). Each fragment copies 408 bytes of
`pad(z ‖ c)` (suffix `0x1f`, `hbE`) to `HB`: the first from `z` and the
start of `c`, the others from `c`, the last followed by the padding
(`jblk_ok`); the sponge's state is `hstate (z ‖ c) (3i) 0x1f` before
fragment `i` (`FJ`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.DjF16

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt keccakF)
open VG.Proof.MlKem.X86_64.Decaps (DC dcDk dcC dcEk dcM' dcG dcKb dcR dcW dcB dcB_bases dcChk DcWfB slice_of)
open VG.Proof.MlKem.HSponge (hstate)
open VG.Proof.MlKem.X86_64.EkF (blk Partial stateAt_keep hbE hbE_blk habs_blk habs_congr)
open VG.Proof.MlKem.X86_64.EkF16 (padTail16_ok)
open VG.Impl.MlKem.X86_64.Encaps (nb)
open VG.Impl.MlKem.X86_64.Encaps16 (oHS oHB padTail)
open VG.Impl.MlKem.X86_64.DecapsJ16 (jLen jblk frag)
open VG.Impl.MlKem.X86_64.Top16 (aP)

/-! ## The context before `K̄` -/

/-- A piece writing `ws` keeps `DC` and `K'`. -/
def dcgChk (L : Kem) (ws : List (Ptr × Nat)) : Bool := dcChk L ws && keepB (dcB L) ws (sc oG) 32

/-- `DC`, and `K'` at `G`. -/
structure DCG (L : Kem) (σ s : State) : Prop where
  dc : DC L σ s
  k : bytesAt s.mem (pa s (sc oG)) 32 = (dcG L σ).1

theorem DCG.step {L : Kem} {oc : Nat} (W : DcWfB L oc) {σ : State} (hp : (decapsK L).pre σ) {s s' : State}
    (h : DCG L σ s) {ws : List (Ptr × Nat)} (hP : PPostB s s' ws) (hc : dcgChk L ws = true) : DCG L σ s' := by
  simp only [dcgChk, Bool.and_eq_true] at hc
  have L₀ := h.dc.lay W hp
  exact ⟨h.dc.step W hp hP hc.1, by rw [L₀.keepBytes hP hc.2]; exact h.k⟩

/-- The context of the re-encryption's inputs before `K̄`, in a run from `σ`. -/
def dcXG {L : Kem} {oc : Nat} (W : DcWfB L oc) (σ : State) : Ctx (dcR L) (dcW L) where
  Out s := (decapsK L).pre σ ∧ DCG L σ s
  chk := dcgChk L
  bs := dcB_bases L
  lay h := h.2.dc.lay W h.1
  step h hP hc := ⟨h.1, h.2.step W h.1 hP hc⟩

/-- `z ‖ c`. -/
abbrev zcE (L : Kem) (σ : State) : List Byte := KPke.dkZ L.p (dcDk L σ) ++ dcC L σ

theorem zcE_length (L : Kem) (σ : State) : (zcE L σ).length = 32 + L.ctLen := by
  simp only [zcE, List.length_append, KPke.dkZ, List.length_take, List.length_drop, dcDk, dcC, bytesAt_length]
  have : L.dkLen = 768 * L.p.k + 96 := rfl
  omega_using [this]

/-! ## The checks of the layout -/

variable (K : Kem16)

/-- A piece writing `ws` keeps the re-encryption's inputs, `ρ` at `SB` and the first `e` entries of `Â`. -/
def fkeep (ws : List (Ptr × Nat)) (e : Nat) : Bool :=
  Enc.inKeep K.L (dcB K.L) (dcgChk K.L) (.rbp, 384 * K.L.k) ws && keepB (dcB K.L) ws (sc oSB) 32 &&
    (List.range e).all fun e' => keepB (dcB K.L) ws (aP K e') 512

/-- ... and the sponge's state. -/
def hkeep (ws : List (Ptr × Nat)) (e : Nat) : Bool := fkeep K ws e && keepB (dcB K.L) ws (sc (oHS K)) 200

/-- The blocks of fragment `i`. -/
def jbChk (i : Nat) : Bool :=
  (if i = 0 then
      copyChk (dcB K.L) (dcW K.L) (sc (oHB K)) (.rbp, 768 * K.L.k + 64) 32 &&
        copyChk (dcB K.L) (dcW K.L) (sc (oHB K + 32)) (.r14, 0) 376 &&
        keepB (dcB K.L) [(sc (oHB K), 32)] (.r14, 0) K.L.ctLen &&
        keepB (dcB K.L) [(sc (oHB K + 32), 376)] (sc (oHB K)) 32
    else if 408 * i + 408 ≤ jLen K then copyChk (dcB K.L) (dcW K.L) (sc (oHB K)) (.r14, 408 * i - 32) 408
    else copyChk (dcB K.L) (dcW K.L) (sc (oHB K)) (.r14, 408 * i - 32) (jLen K - 408 * i) &&
      inB (dcW K.L) (sc (oHB K)) 408 &&
      keepB (dcB K.L) [(sc (oHB K + (jLen K - 408 * i)), 408 - (jLen K - 408 * i))] (sc (oHB K)) (jLen K - 408 * i)) &&
  hkeep K [(sc (oHB K), 408)] (3 * i)

/-- The seeds of fragment `i`. -/
def sdChk (i : Nat) : Bool :=
  (List.range 4).all fun J => seedsChk (dcB K.L) (dcW K.L) J && hkeep K (seedW J) (3 * i) &&
    keepB (dcB K.L) (seedW J) (sc (oHB K)) 408

/-- The fragment inlined, of fragment `i`. -/
def smChk (i : Nat) : Bool :=
  s4_16Chk (dcB K.L) (dcW K.L) (K.oA + 512 * (3 * i)) K.oW &&
    fkeep K [(sc (K.oA + 512 * (3 * i)), 2048), (sc K.oW, 8192)] (3 * i)

/-- What the fragments need of the layout, evaluated for each parameter set. -/
structure DjFWf : Prop extends Decaps16.Dc16Wf K where
  part : 0 < jLen K % 136 ∧ jLen K % 136 < 135
  nbJ : 3 * nb K.L = jLen K / 136 + 1
  nbK : 1 < nb K.L ∧ 3 * nb K.L ≤ K.L.k * K.L.k
  last : 272 < jLen K - 408 * (nb K.L - 1) ∧ jLen K - 408 * (nb K.L - 1) < 406 ∧ jLen K < 408 * nb K.L
  len8 : jLen K % 8 = 0 ∧ jLen K < 2 ^ 20
  rC : (copyChk (dcB K.L) (dcW K.L) (sc oSB) (.rbp, 384 * K.L.k + 384 * K.L.k) 32 &&
    Enc.inKeep K.L (dcB K.L) (dcgChk K.L) (.rbp, 384 * K.L.k) [(sc oSB, 32)]) = true
  zC : (inB (dcW K.L) (sc (oHS K)) 200 && fkeep K [(sc (oHS K), 200)] 0) = true
  jb : ∀ i < nb K.L, jbChk K i = true
  sd : ∀ i < nb K.L, sdChk K i = true
  sm : ∀ i < nb K.L, smChk K i = true

/-! ## What holds before each fragment -/

variable {K}

/-- The re-encryption's inputs in the context before `K̄`, with the first `e` entries of `Â`. -/
abbrev EBG (W : DcWfB K.L oCT16) (σ : State) (e : Nat) (s : State) : Prop :=
  Enc16.EB16 K (dcXG W σ) (.rbp, 384 * K.L.k) (dcEk K.L σ) (dcM' K.L σ) (dcG K.L σ).2 e s

/-- Before fragment `i`. -/
structure FJ (W : DcWfB K.L oCT16) (σ : State) (i : Nat) (s : State) : Prop where
  eb : EBG W σ (3 * i) s
  hs : stateAt s.mem (pa s (sc (oHS K))) = hstate (zcE K.L σ) (3 * i) (BitVec.ofNat 8 0x1f)

/-- A piece that writes `ws` and keeps `r15` keeps `FJ`. -/
theorem FJ.keep {W : DcWfB K.L oCT16} {σ : State} {i : Nat} {s s' : State} (h : FJ W σ i s)
    {ws : List (Ptr × Nat)} (hP : PPostB s s' ws) (h15 : s'.gpr .r15 = s.gpr .r15)
    (hc : hkeep K ws (3 * i) = true) : FJ W σ i s' := by
  simp only [hkeep, fkeep, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨hE, hS⟩, hA⟩, hH⟩ := hc
  have L₀ := (dcXG W σ).lay h.eb.i.out
  exact ⟨⟨h.eb.i.keep hP hE, by rw [L₀.keepBytes hP hS]; exact h.eb.sb,
    ⟨by rw [h15]; exact h.eb.m.r15, fun e he f hf => L₀.keepPoly16 hP (hA e he) (h.eb.m.mat e he f hf)⟩⟩,
    by rw [stateAt_keep L₀ hP hH]; exact h.hs⟩

theorem dkZ_length (L : Kem) (σ : State) : (KPke.dkZ L.p (dcDk L σ)).length = 32 := by
  simp only [KPke.dkZ, List.length_take, List.length_drop, dcDk, bytesAt_length]
  have : L.dkLen = 768 * L.p.k + 96 := rfl
  omega_using [this]

theorem zc_drop (L : Kem) (σ : State) {n : Nat} (hn : 32 ≤ n) : (zcE L σ).drop n = (dcC L σ).drop (n - 32) := by
  rw [zcE, List.drop_append, List.drop_eq_nil_of_le (by rw [dkZ_length]; omega_using [hn]), List.nil_append, dkZ_length]

theorem jblk_ok (F : DjFWf K) {σ : State} {i : Nat} (hi : i < nb K.L) {s : State} (h : FJ F.toDcWfB σ i s) :
    WP isa (jblk K i) s fun s' => PPostB s s' [(sc (oHB K), 408)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      bytesAt s'.mem (pa s (sc (oHB K))) 408 = hbE (zcE K.L σ) i (BitVec.ofNat 8 0x1f) := by
  have L₀ := (dcXG F.toDcWfB σ).lay h.eb.i.out
  have dc := h.eb.i.out.2.dc
  have hc := F.jb i hi
  have hzl : (zcE K.L σ).length = jLen K := zcE_length K.L σ
  have hdk : 768 * K.L.k + 96 = K.L.dkLen := rfl
  have hl := F.last
  have hn := F.nbJ
  have hk := F.nbK
  have h8 := F.len8
  have hcl : jLen K = 32 + K.L.ctLen := rfl
  unfold jblk
  unfold jbChk at hc
  by_cases h0 : i = 0
  · subst h0
    simp only [↓reduceIte, Bool.and_eq_true] at hc ⊢
    obtain ⟨⟨⟨⟨hz, hcc⟩, hkc⟩, hkz⟩, -⟩ := hc
    refine WP.seq (WP.mono (copy_okL L₀ (show Reg.rbp ≠ .rdi by decide) hz) fun s₁ ⟨hP₁, hb₁⟩ => ?_)
    have L₁ := L₀.post hP₁.b (dcB_bases K.L)
    refine WP.mono (copy_okL L₁ (show Reg.r14 ≠ .rdi by decide) hcc) fun s₂ ⟨hP₂, hb₂⟩ => ?_
    have e : pa s (sc (oHB K + 32)) = pa s (sc (oHB K)) + BitVec.ofNat 64 32 := (off_add _ _ _).symm
    have p₁ : ∀ o, pa s₁ (sc o) = pa s (sc o) := fun _ => hP₁.pa rbx_cs
    have p₂ : ∀ o, pa s₂ (sc o) = pa s₁ (sc o) := fun _ => hP₂.pa rbx_cs
    have r₁ : pa s₁ (.r14, 0) = pa s (.r14, 0) := hP₁.pa (by decide)
    have hP : PPost s s₂ [(sc (oHB K), 408)] := by
      refine (PPost.trans hP₁ hP₂ (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; exact rbx_cs)
        (ws := [(sc (oHB K), 32), (sc (oHB K + 32), 376)])
        (fun w hw => List.mem_cons.2 (.inl (List.mem_singleton.1 hw)))
        (fun w hw => List.mem_cons.2 (.inr hw))).weaken fun w hw => ⟨_, List.mem_singleton_self _, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact Region.sub_prefix (by omega_using [])
      · show Region.Sub ⟨pa s (sc (oHB K + 32)), _⟩ ⟨pa s (sc (oHB K)), 408⟩
        rw [e]; exact Offset.sub_base _ (by omega_using [])
    refine ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
    have A : bytesAt s₂.mem (pa s (sc (oHB K))) 32 = KPke.dkZ K.L.p (dcDk K.L σ) := by
      have k₁ := L₁.keepBytes hP₂.b hkz
      rw [p₂, p₁] at k₁
      rw [k₁, hb₁, slice_of dc.dk (show 768 * K.L.k + 64 + 32 ≤ K.L.dkLen by omega_using [hdk])]
      rfl
    have B : bytesAt s₂.mem (pa s (sc (oHB K + 32))) 376 = (dcC K.L σ).take 376 := by
      have kc := L₀.keepBytes hP₁.b hkc
      rw [r₁, dc.c] at kc
      rw [← p₁, hb₂, r₁, ← bytesAt_take _ _ (show 376 ≤ K.L.ctLen by omega), kc]
    have sp := bytesAt_add s₂.mem (pa s (sc (oHB K))) 32 376
    rw [← e, A, B] at sp
    rw [sp, hbE, ite_eq_left (show 408 * 0 + 408 ≤ (zcE K.L σ).length by omega_using [hzl, hl, hk]), Nat.mul_zero, List.drop_zero, zcE,
      List.take_append, List.take_of_length_le (l := KPke.dkZ K.L.p (dcDk K.L σ)) (by rw [dkZ_length]; omega_using []),
      dkZ_length]
  · simp only [h0, ↓reduceIte] at hc ⊢
    have h32 : 32 ≤ 408 * i := by omega_using [h0]
    by_cases hf : 408 * i + 408 ≤ jLen K
    · simp only [hf, ↓reduceIte, Bool.and_eq_true] at hc ⊢
      refine WP.mono (copy_okL L₀ (show Reg.r14 ≠ .rdi by decide) hc.1) fun s' ⟨hP, hb⟩ =>
        ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
      rw [hb, slice_of dc.c (show 408 * i - 32 + 408 ≤ K.L.ctLen by omega_using [hl, hcl, hf]), hbE,
        ite_eq_left (show 408 * i + 408 ≤ (zcE K.L σ).length by omega_using [hzl, hf]), zc_drop K.L σ h32]
    · simp only [hf, ↓reduceIte, Bool.and_eq_true] at hc ⊢
      obtain ⟨⟨⟨hcp, hin⟩, hkp⟩, -⟩ := hc
      have hii : i = nb K.L - 1 := by omega_using [hi, hl, hf]
      have hlen : 272 < jLen K - 408 * i ∧ jLen K - 408 * i < 406 := by rw [hii]; exact ⟨hl.1, hl.2.1⟩
      have hm8 : (jLen K - 408 * i) % 8 = 0 := by omega_using [h8]
      refine WP.seq (WP.mono (copy_okL L₀ (show Reg.r14 ≠ .rdi by decide) hcp) fun s₁ ⟨hP₁, hb₁⟩ => ?_)
      have L₁ := L₀.post hP₁.b (dcB_bases K.L)
      refine WP.mono (padTail16_ok K L₁ hlen.2 hm8 hin (d := 0x1f) (by decide)) fun s₂ ⟨hP₂, hb₂⟩ => ?_
      have e : pa s (sc (oHB K + (jLen K - 408 * i))) = pa s (sc (oHB K)) + BitVec.ofNat 64 (jLen K - 408 * i) :=
        (off_add _ _ _).symm
      have hP : PPost s s₂ [(sc (oHB K), 408)] := by
        refine (PPost.trans hP₁ hP₂ (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; exact rbx_cs)
          (ws := [(sc (oHB K), jLen K - 408 * i), (sc (oHB K + (jLen K - 408 * i)), 408 - (jLen K - 408 * i))])
          (fun w hw => List.mem_cons.2 (.inl (List.mem_singleton.1 hw)))
          (fun w hw => List.mem_cons.2 (.inr hw))).weaken fun w hw => ⟨_, List.mem_singleton_self _, ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact Region.sub_prefix (by omega)
        · show Region.Sub ⟨pa s (sc (oHB K + (jLen K - 408 * i))), _⟩ ⟨pa s (sc (oHB K)), 408⟩
          rw [e]; exact Offset.sub_base _ (by omega_using [hf])
      refine ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
      have k₁ := L₁.keepBytes hP₂.b hkp
      rw [hP₂.pa rbx_cs, hP₁.pa rbx_cs, hb₁] at k₁
      rw [hP₁.pa rbx_cs] at hb₂
      have sp := bytesAt_add s₂.mem (pa s (sc (oHB K))) (jLen K - 408 * i) (408 - (jLen K - 408 * i))
      rw [Nat.add_sub_cancel' (by omega_using [hf]), ← e, hb₂, k₁] at sp
      rw [sp, slice_of dc.c (show 408 * i - 32 + (jLen K - 408 * i) ≤ K.L.ctLen by omega_using [hi, hl, hcl, h0]), hbE,
        ite_eq_right (show ¬408 * i + 408 ≤ (zcE K.L σ).length by omega_using [hzl, hf]), zc_drop K.L σ h32, hzl,
        List.take_of_length_le (by rw [List.length_drop, dcC, bytesAt_length]; omega_using [hcl])]

/-- While the seeds of fragment `i` are written. -/
structure SJ (W : DcWfB K.L oCT16) (σ : State) (i J : Nat) (s : State) : Prop where
  fi : FJ W σ i s
  sd : SeedsIs (Enc.rhoE K.L (dcEk K.L σ)) K.L.k (3 * i) J s
  hb : bytesAt s.mem (pa s (sc (oHB K))) 408 = hbE (zcE K.L σ) i (BitVec.ofNat 8 0x1f)

theorem seedJ_ok (F : DjFWf K) {σ : State} {i : Nat} (hi : i < nb K.L) {J : Nat} (hJ : J < 4) {s : State}
    (h : SJ F.toDcWfB σ i J s) :
    WP isa (seedAt J ((3 * i + J) / K.L.k) ((3 * i + J) % K.L.k)) s (SJ F.toDcWfB σ i (J + 1)) := by
  have hsd := F.sd i hi
  simp only [sdChk, List.all_eq_true, List.mem_range, Bool.and_eq_true] at hsd
  obtain ⟨⟨hs, hk⟩, hB⟩ := hsd J hJ
  have L₀ := (dcXG F.toDcWfB σ).lay h.fi.eb.i.out
  have h16 : K.L.k * K.L.k ≤ 16 := Nat.mul_le_mul F.k.2 F.k.2
  have := F.nbK
  refine WP.mono (seed_step L₀ (dcB_bases K.L) (by omega_using [hi, hJ, h16, this]) hs h.sd) fun s' ⟨hP, hS⟩ =>
    ⟨h.fi.keep hP.b (hP.cs .r15 (by decide)) hk, hS, ?_⟩
  rw [L₀.keepBytes hP.b hB]; exact h.hb

theorem blocksJ_eq (F : DjFWf K) {σ : State} {i : Nat} (hi : i < nb K.L) {s : State}
    (hb : bytesAt s.mem (pa s (sc (oHB K))) 408 = hbE (zcE K.L σ) i (BitVec.ofNat 8 0x1f)) {j : Nat} (hj : j < 3) :
    bytesAt s.mem (pa s (sc (K.oW)) + BitVec.ofNat 64 (Sample4.oHB + 136 * j)) 136 =
      blk (zcE K.L σ) (3 * i + j) (BitVec.ofNat 8 0x1f) := by
  have hE : (zcE K.L σ).length = jLen K := zcE_length K.L σ
  have hl := F.last
  have hn := F.nbJ
  rw [← hbE_blk hj (by rw [hE]; omega_using [hi, hl]), ← hb, bytesAt_slice _ _ (by omega_using [hj])]
  show bytesAt _ (s.gpr .rbx + BitVec.ofNat 64 (K.oW) + BitVec.ofNat 64 (Sample4.oHB + 136 * j)) 136 =
    bytesAt _ (s.gpr .rbx + BitVec.ofNat 64 (K.oW + Sample4.oHB) + BitVec.ofNat 64 (136 * j)) 136
  rw [off_add, off_add, Nat.add_assoc]

theorem fragJ_ok (F : DjFWf K) {b : Prog isa} (hb : BatchHOk16 b) {σ : State} {i : Nat} (hi : i < nb K.L)
    {s : State} (h : FJ F.toDcWfB σ i s) : WP isa (frag K b i) s (FJ F.toDcWfB σ (i + 1)) := by
  have hsm := F.sm i hi
  simp only [smChk, Bool.and_eq_true] at hsm
  have hc := F.jb i hi
  simp only [jbChk, Bool.and_eq_true] at hc
  unfold frag
  refine WP.seq (WP.mono (jblk_ok F hi h) fun s₁ ⟨hP₁, h15₁, hb₁⟩ => ?_)
  have f₁ := h.keep hP₁ h15₁ hc.2
  have i₁ : SJ F.toDcWfB σ i 0 s₁ := ⟨f₁, ⟨f₁.eb.sb, fun _ h => absurd h (Nat.not_lt_zero _)⟩,
    by rw [hP₁.pa rbx_bases]; exact hb₁⟩
  refine WP.seq (WP.mono (seedJ_ok F hi (J := 0) (by decide) i₁) fun s₂ i₂ => ?_)
  refine WP.seq (WP.mono (seedJ_ok F hi (J := 1) (by decide) i₂) fun s₃ i₃ => ?_)
  refine WP.seq (WP.mono (seedJ_ok F hi (J := 2) (by decide) i₃) fun s₄ i₄ => ?_)
  refine WP.seq (WP.mono (seedJ_ok F hi (J := 3) (by decide) i₄) fun s₅ i₅ => ?_)
  have L₅ := (dcXG F.toDcWfB σ).lay i₅.fi.eb.i.out
  refine WP.mono (sampleHAt16_ok hb (SHH16.of L₅ hsm.1)) fun s₆ h₆ => ?_
  have hk := hsm.2
  simp only [fkeep, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hk
  obtain ⟨⟨hE, hS⟩, hA⟩ := hk
  have hl := F.last
  have hn := F.nbJ
  have hpart : Partial (zcE K.L σ) := by rw [Partial, zcE_length]; exact F.part
  have hlen : (zcE K.L σ).length = jLen K := zcE_length K.L σ
  refine ⟨⟨i₅.fi.eb.i.keep h₆.b hE, by rw [L₅.keepBytes h₆.b hS]; exact i₅.fi.eb.sb, ?_⟩, ?_⟩
  · rw [show 3 * (i + 1) = 3 * i + 3 by omega_using []]
    refine EkF16.MatB16.three i₅.fi.eb.m L₅ h₆.b hA ?_ fun t ht f hf => ?_
    · rw [h₆.r15, all3_16, range_all_congr fun k hk => congrArg (fun B => (sampleNTT minIterations B).isSome)
        (seed4_eq i₅.sd (k := k) (by omega_using [hk]))]
    · have := h₆.res t ht f (by rw [seed4_eq i₅.sd (by omega_using [ht])]; exact hf)
      rwa [poly4W, pBytes_true, pa, off_add] at this
  · have e1 : pa s₅ (sc (oHS K)) = pa s₅ (sc (K.oW)) + BitVec.ofNat 64 Sample4.oHS := (off_add _ _ _).symm
    rw [h₆.b.pa rbx_bases, e1, h₆.hs, ← e1, i₅.fi.hs,
      habs_congr _ 3 fun j hj => blocksJ_eq F hi i₅.hb hj, show 3 * (i + 1) = 3 * i + 3 by omega_using []]
    exact habs_blk hpart (by rw [hlen]; omega_using [hi, hl])

theorem fragsJ_ok (F : DjFWf K) {b : Prog isa} (hb : BatchHOk16 b) {σ : State} {s : State}
    (h : FJ F.toDcWfB σ 0 s) : WP isa (seqR (frag K b) 0 (nb K.L)) s (FJ F.toDcWfB σ (nb K.L)) := by
  have := seqR_ok (I := FJ F.toDcWfB σ) (nb K.L) 0 (fun k _ hk s hs => fragJ_ok F hb (by omega_using [hk]) hs) s h
  rwa [Nat.zero_add] at this

end VG.Proof.MlKem.X86_64.DjF16

end

end

/-!
# ML-KEM on x86-64: decapsulation hashing `z ‖ c` in the matrix's fragments, with 16-bit polynomials

`kemDecapsJ16_correct`: the prologue and `m'` (`Dc16Dec.lean`);
`G(m' ‖ h)` alone, which gives the re-encryption's inputs in the context
before `K̄` (`hashG_ok`, `dcXG`); `ρ` to `SB` and `J`'s sponge zeroed; the
fragments (`fragsJ_ok`, `DjFrag16.lean`); `J(z ‖ c)` to `KB`, which moves
the inputs to the context of the re-encryption after the hashes (`dcX`,
`kbJ_ok`); the remaining entries of `Â` (`entsJ_ok`); and, if every
`SampleNTT` succeeded, the rest of the re-encryption and the choice of the
key.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt)

namespace DjF16

open VG.Proof.MlKem.X86_64.Decaps (DC DCK DM dcDk dcC dcEk dcM' dcG dcKb dcR dcW dcB dcB_bases dcChk dckChk DcWfB
  slice_of dcX)
open VG.Impl.MlKem.X86_64.Encaps (nb)
open VG.Impl.MlKem.X86_64.Encaps16 (oHS oHB hzero)
open VG.Impl.MlKem.X86_64.DecapsJ16 (jLen hashG frag matJ)
open VG.Impl.MlKem.X86_64.Top16 (aP)

variable (K : Kem16)

/-- What decapsulation hashing `z ‖ c` in the fragments needs of the layout, besides the fragments'. -/
structure DjHWf : Prop extends DjFWf K where
  /-- The entries after the fragments are sampled four at a time. -/
  eS : 3 * nb K.L % 4 = 0 ∨ 4 * (K.L.k * K.L.k / 4) ≤ 3 * nb K.L
  noS : K.L.k * K.L.k ≤ 4 * (K.L.k * K.L.k / 4) ∨ K.L.k * K.L.k ≤ 3 * nb K.L
  -- `J(z ‖ c)` to `KB`
  kC : (copyChk (dcB K.L) (dcW K.L) (sc oKB) (sc (oHS K)) 32 && fkeep K [(sc oKB, 32)] (3 * nb K.L)) = true

variable {K}

/-- After `G(m' ‖ h)`: the re-encryption's inputs in the context before `K̄`, and `r15 = 1`. -/
abbrev GI (W : DcWfB K.L oCT16) (σ s : State) : Prop :=
  Enc.EIn K.L (dcXG W σ) (.rbp, 384 * K.L.k) (dcEk K.L σ) (dcM' K.L σ) (dcG K.L σ).2 s ∧ s.gpr .r15 = 1

/-- The re-encryption's inputs in its context, with the first `e` entries of `Â`. -/
abbrev EBX (W : DcWfB K.L oCT16) (σ : State) (e : Nat) (s : State) : Prop :=
  Enc16.EB16 K (dcX W σ) (.rbp, 384 * K.L.k) (dcEk K.L σ) (dcM' K.L σ) (dcG K.L σ).2 e s

theorem hashG_ok (W : DcWfB K.L oCT16) {σ : State} (hp : (decapsK K.L).pre σ) {s : State} (h : DM K.L σ s) :
    WP isa (hashG K) s (GI W σ) := by
  have L₀ := h.dc.lay W hp
  have hdk : 768 * K.L.k + 96 = K.L.dkLen := rfl
  unfold hashG
  refine WP.mono (hash_ok (dcB_bases K.L) (ps := [(sc oM, 32), ((.rbp, 768 * K.L.k + 32), 32)]) (rate := 72)
    (out := sc oG) (len := 64) W.h₁ (show 6 < 256 by decide) L₀) fun s₁ ⟨hP₁, hb₁⟩ => ?_
  have k₁ := h.dc.step W hp hP₁.b W.h₁K
  simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, h.m,
    slice_of h.dc.dk (show 768 * K.L.k + 32 + 32 ≤ K.L.dkLen by omega_using [hdk]), KeyGen.sha3Suffix6] at hb₁
  rw [← sha3_512_eq, ← hP₁.pa rbx_cs] at hb₁
  have hK : bytesAt s₁.mem (pa s₁ (sc oG)) 32 = (dcG K.L σ).1 := by
    rw [← bytesAt_take _ _ (show 32 ≤ 64 by decide), hb₁]; rfl
  have hr : bytesAt s₁.mem (pa s₁ sigP) 32 = (dcG K.L σ).2 := by
    have e := bytesAt_drop s₁.mem (pa s₁ (sc oG)) (k := 32) (len := 64) (by decide)
    have e' : (bytesAt s₁.mem (pa s₁ (sc oG)) 64).drop 32 = bytesAt s₁.mem (pa s₁ sigP) 32 := by
      rw [e, pa, pa, off_add]
    rw [← e', hb₁]; rfl
  refine ⟨⟨⟨hp, k₁, hK⟩, slice_of k₁.dk (show 384 * K.L.k + (384 * K.L.k + 32) ≤ K.L.dkLen by omega_using [hdk]), ?_, hr⟩, ?_⟩
  · rw [L₀.keepBytes hP₁.b W.h₁M]; exact h.m
  · rw [hP₁.cs .r15 (by decide), h.r15]

theorem rhoJ_ok (F : DjHWf K) {σ : State} {s : State} (h : GI F.toDcWfB σ s) :
    WP isa (copy (sc oSB) (.rbp, 384 * K.L.k + 384 * K.L.k) 32) s (EBG F.toDcWfB σ 0) := by
  have L₀ := (dcXG F.toDcWfB σ).lay h.1.out
  have hrC := F.rC
  simp only [Bool.and_eq_true] at hrC
  refine WP.mono (copy_okL L₀ (show Reg.rbp ≠ .rdi by decide) hrC.1) fun s₁ ⟨hP₁, hb₁⟩ =>
    ⟨h.1.keep hP₁.b hrC.2, ?_, MatB16.zero _ _ _ (by rw [hP₁.cs .r15 (by decide), h.2])⟩
  rw [show pa s₁ (sc oSB) = pa s (sc oSB) from hP₁.pa rbx_cs, hb₁]
  exact h.1.rho

theorem hzJ_ok (F : DjHWf K) {σ : State} {s : State} (h : EBG F.toDcWfB σ 0 s) :
    WP isa (.block (hzero K)) s (FJ F.toDcWfB σ 0) := by
  have L₁ := (dcXG F.toDcWfB σ).lay h.i.out
  have hzC := F.zC
  simp only [fkeep, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hzC
  obtain ⟨hzin, ⟨hzE, hzS⟩, -⟩ := hzC
  exact WP.mono (EkF16.hzero16_ok L₁ hzin) fun s₂ ⟨hP₂, hz⟩ =>
    ⟨⟨h.i.keep hP₂.b hzE, by rw [L₁.keepBytes hP₂.b hzS]; exact h.sb,
      ⟨by rw [hP₂.cs .r15 (by decide)]; exact h.m.r15, fun _ he => absurd he (Nat.not_lt_zero _)⟩⟩,
      by rw [hP₂.pa rbx_cs, hz, HSponge.hstate_zero]⟩

/-- `J(z ‖ c)` to `KB`: the inputs move to the re-encryption's context. -/
theorem kbJ_ok (F : DjHWf K) {σ : State} {s : State} (h : FJ F.toDcWfB σ (nb K.L) s) :
    WP isa (copy (sc oKB) (sc (oHS K)) 32) s (EBX F.toDcWfB σ (3 * nb K.L)) := by
  have L₃ := (dcXG F.toDcWfB σ).lay h.eb.i.out
  have hkC := F.kC
  simp only [fkeep, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hkC
  obtain ⟨hcp, ⟨hE, hS⟩, hA⟩ := hkC
  have hn := F.nbJ
  have hlen := zcE_length K.L σ
  have hjl : jLen K = 32 + K.L.ctLen := rfl
  refine WP.mono (copy_okL L₃ (show Reg.rbx ≠ .rdi by decide) hcp) fun s₄ ⟨hP₄, hb₄⟩ => ?_
  have i₄ := h.eb.i.keep hP₄.b hE
  refine ⟨⟨⟨i₄.out.1, i₄.out.2.dc, i₄.out.2.k, ?_⟩, i₄.ek, i₄.m, i₄.r⟩,
    by rw [L₃.keepBytes hP₄.b hS]; exact h.eb.sb,
    ⟨by rw [hP₄.cs .r15 (by decide)]; exact h.eb.m.r15,
      fun e he f hf => L₃.keepPoly16 hP₄.b (hA e he) (h.eb.m.mat e he f hf)⟩⟩
  rw [hP₄.pa rbx_cs, hb₄, HSponge.bytesAt_stateAt, h.hs,
    ← HSponge.J_of_hstate (by rw [hlen]; omega_using [hn, hjl])]

theorem entsJ_ok {n : String} {c : Prog isa} (v : S16Ok c) (F : DjHWf K) {σ : State} {s : State}
    (h : EBX F.toDcWfB σ (3 * nb K.L) s) :
    WP isa (ents16 (n, c) K.L.k K.oA (sc K.oW) (3 * nb K.L) (K.L.k * K.L.k - 3 * nb K.L)) s
      (EBX F.toDcWfB σ (K.L.k * K.L.k)) := by
  have h16 : K.L.k * K.L.k ≤ 16 := Nat.mul_le_mul F.k.2 F.k.2
  have := ents16_ok (n, c) K.L.k K.oA (sc K.oW) (I := fun e s => 3 * nb K.L ≤ e ∧ EBX F.toDcWfB σ e s)
    (fun e he he' _ hs => absurd F.noS (by omega))
    (fun q hq _ hs => WP.mono (Enc16.quadE_step v (C := dcX F.toDcWfB σ) (by omega_using [h16, hq]) (F.enc.q q hq) hs.2) fun _ h => ⟨by omega, h.2⟩)
    (K.L.k * K.L.k - 3 * nb K.L) (3 * nb K.L) (by have := F.nbK; omega_using [this]) F.eS s ⟨Nat.le_refl _, h⟩
  rw [Nat.add_sub_cancel' F.nbK.2] at this
  exact WP.mono this fun _ h => h.2

/-- `ρ` to `SB`, the fragments, `J(z ‖ c)` to `KB`, and the remaining entries of `Â`. -/
theorem matJ_ok {n : String} {c : Prog isa} (v : S16Ok c) (F : DjHWf K) {b : Prog isa} (hb : BatchHOk16 b)
    {σ : State} {s : State} (h : GI F.toDcWfB σ s) :
    WP isa (matJ K (n, c) b) s (EBX F.toDcWfB σ (K.L.k * K.L.k)) := by
  unfold matJ
  exact WP.seq (WP.mono (rhoJ_ok F h) fun _ h₁ => WP.seq (WP.mono (hzJ_ok F h₁) fun _ h₂ =>
    WP.seq (WP.mono (fragsJ_ok F.toDjFWf hb h₂) fun _ h₃ => WP.seq (WP.mono (kbJ_ok F h₃) fun _ h₄ =>
      entsJ_ok v F h₄))))

/-- The rest of the re-encryption, if every `SampleNTT` succeeded. -/
theorem ifRestJ_ok (hK : KpkeOk K.L) (v : Sample4Impl) (F : DjHWf K) {σ s : State}
    (h : EBX F.toDcWfB σ (K.L.k * K.L.k) s) :
    WP isa (ifOk (Top16.encRest K v.callee (.rbp, 384 * K.L.k) (sc oCT16))) s (Decaps16.EncO16 F.toDc16Wf σ) := by
  refine ifOk_ok (fun s₁ hP hne => Enc16.rest_ok hK v (show Reg.rbp ∉ argRegs by decide) (by decide) F.k.2 F.enc F.tl
    (Enc16.ER0.start (h.flag hP F.enc) (KeyGen.r15_ne h.m.r15 hne))) fun s₁ hP he => ?_
  have h₁ := h.flag hP F.enc
  exact ⟨h₁.i.out, h₁.m.r15, fun ho => absurd ho (KeyGen.r15_eq h.m.r15 he)⟩

end DjF16

open Decaps Decaps16 DjF16 in
theorem kemDecapsJ16_correct {K : Kem16} (hK : KpkeOk K.L) (v : Sample4Impl) (F : DjHWf K) {n : String}
    {c : Prog isa} (hs : v.callee.s16 = some (n, c)) {b : Prog isa} (hb : v.callee.batchH16 = some b)
    (hctl : ctlOk (kemDecapsJ16 K v.callee (n, c) b) = true) (σ : State) (hp : (decapsK K.L).pre σ) :
    ∃ t s', Exec isa (kemDecapsJ16 K v.callee (n, c) b) σ t s' ∧ abiPreserved σ s' ∧ (decapsK K.L).post σ s' := by
  have hB := v.batchH16 b hb
  have hS := v.s16 n c hs
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (pro_ok F.toDcWfB hp) fun s₁ ⟨h₁, h15⟩ =>
    WP.seq (WP.mono (dec_ok hK F.toDc16Wf hp h₁ h15) fun s₂ h₂ =>
      WP.seq (WP.mono (hashG_ok F.toDcWfB hp h₂) fun s₃ h₃ =>
        WP.seq (WP.mono (matJ_ok hS F hB h₃) fun s₄ h₄ =>
          WP.seq (WP.mono (ifRestJ_ok hK v F h₄) fun s₅ h₅ =>
            WP.seq (WP.mono (select_okD F.toDcWfB (EncO16.sel (W := F.toDc16Wf) h₅)) fun s₆ h₆ =>
              WP.mono (topEpi_ok h₆.dc.top (h₆.hin F.toDcWfB hp)) fun s₇ ⟨hr, hg, hm⟩ =>
                (⟨hg, post_of F.toDcWfB h₆ hr hm⟩ : gprPreserved σ s₇ ∧ (decapsK K.L).post σ s₇)))))))
  exact ⟨t, s', he, abiPreserved_of_ctl hctl he hF.1, hF.2⟩

end VG.Proof.MlKem.X86_64

end

end

/-!
# ML-KEM on x86-64: decapsulation hashing `z ‖ c` in the matrix's fragments, constant time

`kemDecapsJ16_ct`: two runs whose pointers and `ρ` agree leak the same. The
fragments' blocks of `pad(z ‖ c)` and the sponge's state, which only the
fourth Keccak state absorbs, are at fixed addresses (`jblk` and the copies
pass the taint analysis from the pointers, `DjTWf`), and the sampling's
branches and addresses depend on the seeds of `ρ` alone, as in
`kemEncaps16_ct`; the rest leaks only the pointers, as in the
decapsulation of `u32` polynomials.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace DjF16

open VG.Proof.MlKem.X86_64.Decaps (DC DM dcEk dcR dcW dcB dcB_bases DcWfB R dc_lrel rho_pub dcXA)
open VG.Proof.MlKem.X86_64.EkF (relFalse)
open VG.Impl.MlKem.X86_64.Encaps (nb)
open VG.Impl.MlKem.X86_64.Encaps16 (oHS oHB hzero)
open VG.Impl.MlKem.X86_64.DecapsJ16 (hashG jblk frag matJ)

variable (K : Kem16)

/-- The taint checks of the pieces the fused decapsulation adds, from the pointers. -/
structure DjTWf : Prop where
  rbpIn : inB (dcB K.L) (.rbp, 0) 1 = true
  zT : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r14]) (.block (hzero K)) h).isSome = true
  jT : ∀ i < nb K.L, ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r14]) (jblk K i) h).isSome = true
  kT : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r14])
    (copy (sc oKB) (sc (oHS K)) 32) h).isSome = true
  ij : ∀ i < nb K.L, ∀ J < 4, (3 * i + J) / K.L.k < 4 ∧ (3 * i + J) % K.L.k < 4

variable {K}

section
variable (F : DjHWf K) (T : DjTWf K)
include F T

/-- Code the taint analysis proves constant time from the pointers. -/
theorem trLD {c : Prog isa} {h : VG.Taint.Hint X86_64.Taint.T}
    (ht : (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r14]) c h).isSome = true) :
    RelCT isa (LRel (dcR K.L) (dcW K.L)) c fun _ _ => True :=
  taintRel [.rbx, .rbp, .r12, .r14] (fun _ _ h =>
    fa4 (h.eq (p := sc 0) (l := 1) F.inBs.1) (h.eq (p := (.rbp, 0)) (l := 1) T.rbpIn)
      (h.eq (p := (.r12, 0)) (l := 1) F.inBs.2.1) (h.eq (p := (.r14, 0)) (l := 1) F.inBs.2.2)) ht

theorem rhoJ_tr :
    RelCT isa (R K.L (GI F.toDcWfB)) (copy (sc oSB) (.rbp, 384 * K.L.k + 384 * K.L.k) 32) fun _ _ => True := by
  obtain ⟨_, t⟩ := F.rhoT
  exact rel2_of (taintRel [.rbx, .rbp] (fun _ _ h =>
      fa2 (h.eq (p := sc 0) (l := 1) F.inBs.1) (h.eq (p := (.rbp, 0)) (l := 1) T.rbpIn)) t)
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => dc_lrel F.toDcWfB p₁ p₂ pub h₁.1.out.2.dc h₂.1.out.2.dc

theorem hzJ_tr : RelCT isa (R K.L fun σ s => EBG F.toDcWfB σ 0 s) (.block (hzero K)) fun _ _ => True := by
  obtain ⟨_, t⟩ := T.zT
  exact rel2_of (trLD F T t) fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
    dc_lrel F.toDcWfB p₁ p₂ pub h₁.i.out.2.dc h₂.i.out.2.dc

theorem kbJ_tr : RelCT isa (R K.L fun σ s => FJ F.toDcWfB σ (nb K.L) s) (copy (sc oKB) (sc (oHS K)) 32)
    fun _ _ => True := by
  obtain ⟨_, t⟩ := T.kT
  exact rel2_of (trLD F T t) fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
    dc_lrel F.toDcWfB p₁ p₂ pub h₁.eb.i.out.2.dc h₂.eb.i.out.2.dc

end

theorem hashG_tr (W : DcWfB K.L oCT16) : RelCT isa (R K.L (DM K.L)) (hashG K) fun _ _ => True := by
  unfold hashG
  exact rel2_of (hash_tr (dcB_bases K.L) (ps := [(sc oM, 32), ((.rbp, 768 * K.L.k + 32), 32)]) (rate := 72)
    (out := sc oG) (len := 64) W.h₁ (show 6 < 256 by decide)) fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
    dc_lrel W p₁ p₂ pub h₁.dc h₂.dc

/-- Before fragment `i`, for the `ρ` of `dk`'s key. -/
abbrev FJρ (W : DcWfB K.L oCT16) (ρ : List Byte) (i : Nat) (s : State) : Prop :=
  ∃ σ, (decapsK K.L).pre σ ∧ FJ W σ i s ∧ Enc.rhoE K.L (dcEk K.L σ) = ρ

theorem fragJ_tr (F : DjHWf K) (T : DjTWf K) {b : Prog isa} (hB : BatchHOk16 b) {i : Nat} (hi : i < nb K.L) :
    RelCT isa (R K.L fun σ s => FJ F.toDcWfB σ i s) (frag K b i) fun _ _ => True := by
  obtain ⟨_, t⟩ := T.jT i hi
  have hsd := F.sd i hi
  simp only [sdChk, List.all_eq_true, List.mem_range, Bool.and_eq_true] at hsd
  have hsm := F.sm i hi
  simp only [smChk, Bool.and_eq_true] at hsm
  have hc := F.jb i hi
  simp only [jbChk, Bool.and_eq_true] at hc
  have h16 : K.L.k * K.L.k ≤ 16 := Nat.mul_le_mul F.k.2 F.k.2
  have hnb := F.nbK
  have c4 := hsm.1
  refine RelCT.mono (RelCT.exists_ (P := fun ρ x y => LRel (dcR K.L) (dcW K.L) x y ∧ FJρ F.toDcWfB ρ i x ∧
    FJρ F.toDcWfB ρ i y) (Q := fun _ _ => True) fun ρ => ?_) ?_ fun _ _ _ => trivial
  · unfold frag
    have hok : ∀ x, FJρ F.toDcWfB ρ i x → WP isa (jblk K i) x fun x' =>
        PPostB x x' [(sc (oHB K), 408)] ∧ SeedsIs ρ K.L.k (3 * i) 0 x' := fun x ⟨σ, hp, h, e⟩ =>
      WP.mono (jblk_ok F.toDjFWf hi h) fun x' ⟨hP, h15, _⟩ =>
        ⟨hP, ⟨by rw [(h.keep hP h15 hc.2).eb.sb, e], fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩
    refine RelCT.seq (RelCT.postDep (RelCT.mono (trLD F T t) (fun _ _ h => h.1) fun _ _ h => h)
      (F := fun x x' => PPostB x x' [(sc (oHB K), 408)] ∧ SeedsIs ρ K.L.k (3 * i) 0 x')
      (Q := RQ (dcR K.L) (dcW K.L) ρ K.L.k (3 * i) 0) (fun x y h => ⟨hok x h.2.1, hok y h.2.2⟩)
      fun _ _ _ _ h hx hy => ⟨h.1.post (dcB_bases K.L) hx.1 hy.1, hx.2, hy.2⟩) ?_
    refine RelCT.seq (seed_tr (dcB_bases K.L) (K := 0) (by omega_using [hi, h16, hnb]) (by decide) (T.ij i hi 0 (by decide)).1
      (T.ij i hi 0 (by decide)).2 (hsd 0 (by decide)).1.1) ?_
    refine RelCT.seq (seed_tr (dcB_bases K.L) (K := 1) (by omega_using [hi, h16, hnb]) (by decide) (T.ij i hi 1 (by decide)).1
      (T.ij i hi 1 (by decide)).2 (hsd 1 (by decide)).1.1) ?_
    refine RelCT.seq (seed_tr (dcB_bases K.L) (K := 2) (by omega_using [hi, h16, hnb]) (by decide) (T.ij i hi 2 (by decide)).1
      (T.ij i hi 2 (by decide)).2 (hsd 2 (by decide)).1.1) ?_
    refine RelCT.seq (seed_tr (dcB_bases K.L) (K := 3) (by omega_using [hi, h16, hnb]) (by decide) (T.ij i hi 3 (by decide)).1
      (T.ij i hi 3 (by decide)).2 (hsd 3 (by decide)).1.1) ?_
    refine RelCT.mono (sampleHAt16_tr hB) (fun x y h => ⟨SHH16.of h.1.1 c4, SHH16.of h.1.2.1 c4, h.1.eq F.inBs.1,
      h.1.2.2.2, ?_⟩) fun _ _ h => h
    rw [bytesAt136, bytesAt136, seed4_eq h.2.1 (k := 0) (by decide), seed4_eq h.2.1 (k := 1) (by decide),
      seed4_eq h.2.1 (k := 2) (by decide), seed4_eq h.2.1 (k := 3) (by decide), seed4_eq h.2.2 (k := 0) (by decide),
      seed4_eq h.2.2 (k := 1) (by decide), seed4_eq h.2.2 (k := 2) (by decide), seed4_eq h.2.2 (k := 3) (by decide)]
  · rintro x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩
    exact ⟨Enc.rhoE K.L (dcEk K.L σ₁), dc_lrel F.toDcWfB p₁ p₂ pub h₁.eb.i.out.2.dc h₂.eb.i.out.2.dc,
      ⟨σ₁, p₁, h₁, rfl⟩, ⟨σ₂, p₂, h₂, (rho_pub pub).symm⟩⟩

theorem fragsJ_tr (F : DjHWf K) (T : DjTWf K) {b : Prog isa} (hB : BatchHOk16 b) :
    RelCT isa (R K.L fun σ s => FJ F.toDcWfB σ 0 s) (seqR (frag K b) 0 (nb K.L))
      (R K.L fun σ s => FJ F.toDcWfB σ (nb K.L) s) := by
  have := seqR_tr (R := fun i => R K.L fun σ s => FJ F.toDcWfB σ i s) (nb K.L) 0 fun k _ hk =>
    relInv (fun σ s hp h => fragJ_ok F.toDjFWf hB (by omega_using [hk]) h) (fragJ_tr F T hB (by omega_using [hk]))
  rwa [Nat.zero_add] at this

theorem quadJ_tr {n : String} {c : Prog isa} (v : S16Ok c) (F : DjHWf K) {q : Nat} (hq : q < K.L.k * K.L.k / 4) :
    RelCT isa (R K.L fun σ s => EBX F.toDcWfB σ (4 * q) s)
      (quad16 (n, c) K.L.k (4 * q) (sc (K.oA + 512 * (4 * q))) (sc K.oW)) fun _ _ => True := by
  have hc := F.enc.q q hq
  simp only [Enc16.quadEChk, Bool.and_eq_true] at hc
  have h16 : K.L.k * K.L.k ≤ 16 := Nat.mul_le_mul F.k.2 F.k.2
  have hk4 := F.k.2
  refine RelCT.mono (RelCT.exists_ (P := fun ρ x y => RQ (dcR K.L) (dcW K.L) ρ K.L.k (4 * q) 0 x y)
    (Q := fun _ _ => True) fun ρ => quad16_tr (ρ := ρ) v (dcB_bases K.L) (by omega_using [hq, h16])
      (fun t ht => ⟨by have := div_lt_k (show 4 * q + t < K.L.k * K.L.k by omega_using [hq, ht]); omega_using [hk4, this],
        by have := mod_lt_k (show 4 * q + t < K.L.k * K.L.k by omega_using [hq, ht]); omega_using [hk4, this]⟩) hc.1.1.1) ?_ fun _ _ _ => trivial
  rintro x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩
  exact ⟨Enc.rhoE K.L (dcEk K.L σ₁), dc_lrel F.toDcWfB p₁ p₂ pub h₁.i.out.2.dc h₂.i.out.2.dc,
    ⟨h₁.sb, fun _ h => absurd h (Nat.not_lt_zero _)⟩,
    ⟨by rw [h₂.sb, rho_pub pub], fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩

theorem entsJ_tr {n : String} {c : Prog isa} (v : S16Ok c) (F : DjHWf K) :
    RelCT isa (R K.L fun σ s => EBX F.toDcWfB σ (3 * nb K.L) s)
      (ents16 (n, c) K.L.k K.oA (sc K.oW) (3 * nb K.L) (K.L.k * K.L.k - 3 * nb K.L))
      (R K.L fun σ s => EBX F.toDcWfB σ (K.L.k * K.L.k) s) := by
  have h16 : K.L.k * K.L.k ≤ 16 := Nat.mul_le_mul F.k.2 F.k.2
  have := ents16_tr (n, c) K.L.k K.oA (sc K.oW)
    (R := fun e => R K.L fun σ s => 3 * nb K.L ≤ e ∧ EBX F.toDcWfB σ e s)
    (fun e he he' => relFalse fun _ _ ⟨_, _, _, _, _, ⟨h3, _⟩, _⟩ => absurd F.noS (by omega_using [he, he', h3]))
    (fun q hq => relInv (fun σ s hp hs => WP.mono (Enc16.quadE_step v (C := Decaps.dcX F.toDcWfB σ) (by omega_using [h16, hq]) (F.enc.q q hq) hs.2)
        fun _ h => ⟨by omega, h.2⟩)
      (RelCT.mono (quadJ_tr v F hq)
        (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, h₁.2, h₂.2⟩) fun _ _ h => h))
    (K.L.k * K.L.k - 3 * nb K.L) (3 * nb K.L) (by have := F.nbK; omega_using [this]) F.eS
  rw [Nat.add_sub_cancel' F.nbK.2] at this
  exact RelCT.mono this (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, ⟨Nat.le_refl _, h₁⟩,
    ⟨Nat.le_refl _, h₂⟩⟩) fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, h₁.2, h₂.2⟩

theorem matJ_tr {n : String} {c : Prog isa} (v : S16Ok c) (F : DjHWf K) (T : DjTWf K) {b : Prog isa}
    (hB : BatchHOk16 b) :
    RelCT isa (R K.L (GI F.toDcWfB)) (matJ K (n, c) b) (R K.L fun σ s => EBX F.toDcWfB σ (K.L.k * K.L.k) s) := by
  unfold matJ
  exact RelCT.seq (relInv (I' := fun σ s => EBG F.toDcWfB σ 0 s) (fun σ s hp h => rhoJ_ok F h) (rhoJ_tr F T))
    (RelCT.seq (relInv (I' := fun σ s => FJ F.toDcWfB σ 0 s) (fun σ s hp h => hzJ_ok F h) (hzJ_tr F T))
      (RelCT.seq (fragsJ_tr F T hB)
        (RelCT.seq (relInv (I' := fun σ s => EBX F.toDcWfB σ (3 * nb K.L) s) (fun σ s hp h => kbJ_ok F h)
          (kbJ_tr F T)) (entsJ_tr v F))))

/-- The rest of the re-encryption if every `SampleNTT` succeeded. -/
theorem ifRestJ_tr (hK : KpkeOk K.L) (v : Sample4Impl) (F : DjHWf K) :
    RelCT isa (R K.L fun σ s => EBX F.toDcWfB σ (K.L.k * K.L.k) s)
      (ifOk (Top16.encRest K v.callee (.rbp, 384 * K.L.k) (sc oCT16))) fun _ _ => True := by
  refine RelCT.mono (RelCT.exists_ (P := fun ρ x y => LRel (dcR K.L) (dcW K.L) x y ∧
      Enc16.EBρ K (dcXA F.toDcWfB) (.rbp, 384 * K.L.k) ρ (K.L.k * K.L.k) x ∧
      Enc16.EBρ K (dcXA F.toDcWfB) (.rbp, 384 * K.L.k) ρ (K.L.k * K.L.k) y)
    (Q := fun _ _ => True) fun ρ => ?_) ?_ fun _ _ _ => trivial
  · refine ifOk_tr (fun x y ⟨_, ⟨_, _, _, e₁, h₁⟩, ⟨_, _, _, e₂, h₂⟩⟩ => by rw [h₁.m.r15, h₂.m.r15, e₁, e₂])
      (RelCT.mono (Enc16.rest_tr hK v (C := dcXA F.toDcWfB) (show Reg.rbp ∉ argRegs by decide) (by decide) F.k.2 F.enc F.tl
        (ρ := ρ)) ?_
        fun _ _ _ => trivial) fun _ _ _ => trivial
    rintro x y ⟨x₀, y₀, ⟨hl, ⟨ek₁, m₁, r₁, e₁, h₁⟩, ⟨ek₂, m₂, r₂, e₂, h₂⟩⟩, hx, hy, hne⟩
    have o₁ := KeyGen.r15_ne h₁.m.r15 hne
    have o₂ : allOk K.L.k (Enc.rhoE K.L ek₂) (K.L.k * K.L.k) := by rw [e₂, ← e₁]; exact o₁
    exact ⟨hl.post (dcXA F.toDcWfB).bs hx.b hy.b, ⟨ek₁, m₁, r₁, e₁, Enc16.ER0.start (h₁.flag hx F.enc) o₁⟩,
      ⟨ek₂, m₂, r₂, e₂, Enc16.ER0.start (h₂.flag hy F.enc) o₂⟩⟩
  · rintro x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩
    exact ⟨Enc.rhoE K.L (dcEk K.L σ₁), dc_lrel F.toDcWfB p₁ p₂ pub h₁.i.out.2.dc h₂.i.out.2.dc,
      ⟨_, _, _, rfl, Decaps.EIn.any h₁.i, h₁.sb, h₁.m⟩, ⟨_, _, _, (rho_pub pub).symm, Decaps.EIn.any h₂.i, h₂.sb, h₂.m⟩⟩

end DjF16

open Decaps Decaps16 DjF16 in
theorem kemDecapsJ16_ct {K : Kem16} (hK : KpkeOk K.L) (v : Sample4Impl) (F : DjHWf K) (T : DjTWf K)
    {n : String} {c : Prog isa} (hs : v.callee.s16 = some (n, c)) {b : Prog isa} (hb : v.callee.batchH16 = some b) :
    ConstantTime isa (decapsK K.L).pre (decapsK K.L).pub (kemDecapsJ16 K v.callee (n, c) b) := by
  have hB := v.batchH16 b hb
  have hS := v.s16 n c hs
  refine relStart (Q := fun _ _ => True) ?_
  unfold kemDecapsJ16
  refine RelCT.seq (relInv (I' := fun σ s => DC K.L σ s ∧ s.gpr .r15 = 1)
    (fun σ s hp hs => by subst hs; exact pro_ok F.toDcWfB hp) pro_tr) ?_
  refine RelCT.seq (relInv (I' := DM K.L) (fun σ s hp hs => dec_ok hK F.toDc16Wf hp hs.1 hs.2)
    (dec_tr hK F.toDc16Wf)) ?_
  refine RelCT.seq (relInv (I' := GI F.toDcWfB) (fun σ s hp hs => hashG_ok F.toDcWfB hp hs)
    (hashG_tr F.toDcWfB)) ?_
  refine RelCT.seq (matJ_tr hS F T hB) ?_
  refine RelCT.seq (relInv (I' := EncO16 F.toDc16Wf) (fun σ s _ hs => ifRestJ_ok hK v F hs) (ifRestJ_tr hK v F)) ?_
  refine RelCT.seq (relInv (I' := DEnd K.L) (fun σ s _ hs => select_okD F.toDcWfB hs.sel)
    (RelCT.mono (select_tr F.toDcWfB) (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ =>
      ⟨σ₁, σ₂, p₁, p₂, pub, h₁.sel, h₂.sel⟩) fun _ _ h => h)) ?_
  exact RelCT.mono epi_tr (fun _ _ h => h) fun _ _ _ => trivial

end VG.Proof.MlKem.X86_64

end

end

/-! ### `MlKem.X86_64.EkSel16`, which this module and modules that import it used -/

section

/-!
# ML-KEM on x86-64: encapsulation hashing the key, for each implementation

An implementation `v` with a 16-bit sampler and a fragment sampling 16-bit
polynomials (`Callee4.s16`, `Callee4.batchH16`) runs the encapsulation with
16-bit polynomials (`kemEncaps16`); any other, the one with polynomials of
`u32`s (`kemEncaps`). As `Sel16.lean`, with `ek16_ctl` and `ek16_sp` for
the control flow and the stack pointer of `kemEncaps16`, which is proven
for the layout with only the first `n` bytes of `scratch` and leaves the
rest of it as it was (`encapsSel_keep`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64

/-- `ctlOk` of code that calls the 16-bit sampler `c` of the implementation
`v` (`S : S16Ok c`) and the K-PKE functions (`hK`), and inlines the fragment
`b` (`B : BatchHOk16 b`). -/
tactic_template "ek16_ctl " v:ident c:ident b:ident S:ident B:ident hK:ident : tactic =>
  `(tactic| repeat' (first
    | with_reducible exact ($B).ctl | (closed_in $b; s16_ctl $v $c $S $hK; done)
    | (code_whnf; with_reducible apply ctlOk_seq) | (code_whnf; with_reducible apply ctlOk_ite) | rfl))

/-- That code that calls the 16-bit sampler `c` of the implementation `v` and
the K-PKE functions, and inlines the fragment `b`, never writes the stack pointer. -/
tactic_template "ek16_sp " v:ident c:ident b:ident S:ident B:ident hK:ident : tactic =>
  `(tactic| repeat' (first
    | with_reducible exact ($B).sp | (closed_in $b; s16_sp $v $c $S $hK; done)
    | (code_whnf; with_reducible apply all_seq) | (code_whnf; with_reducible apply all_ite) | rfl))

/-- Encapsulation with 16-bit polynomials, against the contract of `K` with
the first `n` bytes of `scratch`. -/
theorem xdLe_batch {k : Nat} {b : Prog isa} (B : BatchHOk16 b) : xdLe k b = true :=
  xdLe_of_le (by rw [B.xd]; exact Nat.zero_le _)

/-- That the calls of code that calls the 16-bit sampler `c` of the
implementation `v` and the K-PKE functions, and inlines the fragment `b`, use
at most `k` bytes of stack (a goal `xdLe k _ = true`). -/
tactic_template "ek16_xd " v:ident c:ident b:ident S:ident B:ident hK:ident : tactic =>
  `(tactic| repeat' (first
    | with_reducible apply xdLe_batch $B | (closed_in $b; s16_xd $v $c $S $hK; done)
    | (code_whnf; with_reducible apply xdLe_seq) | (code_whnf; with_reducible apply xdLe_ite) | rfl))

theorem encaps16_narrow {K : Kem16} {n : Nat} (hn : n ≤ K.L.scr) (hK : KpkeOk K.L) (v : Sample4Impl)
    (F16 : EkF16.Ek16HWf (narrowK K n)) (T16 : EkF16.EkT16Wf (narrowK K n)) {m : String} {c : Prog isa}
    (hs : v.callee.s16 = some (m, c)) {b : Prog isa} (hb : v.callee.batchH16 = some b)
    (hctl : ctlOk (kemEncaps16 K v.callee (m, c) b) = true) (hsat : ∃ s, (encK K.L).pre s) :
    Verified X86_64.target (kemEncaps16 K v.callee (m, c) b) (encK (narrowL K.L n)) :=
  Verified.of_correct (kemEncaps16_correct (K := narrowK K n) (hK.narrow n) v F16 hs hb hctl)
    (kemEncaps16_ct (K := narrowK K n) (hK.narrow n) v F16 T16 hs hb)
    (.refl (hsat.elim fun _ hs => ⟨_, encK_pre hn hs⟩))

theorem encapsSel_verified {K : Kem16} {n : Nat} (hn : n ≤ K.L.scr) (hK : KpkeOk K.L) (v : Sample4Impl)
    (F16 : EkF16.Ek16HWf (narrowK K n)) (T16 : EkF16.EkT16Wf (narrowK K n)) (W : Ek.EkWf K.L)
    {wc wd : List Nat} (C : KemCalls K.L wc wd) {k : Contract isa} (hk : (encK K.L).Implies k)
    (hctl16 : ∀ n c b, S16Ok c → BatchHOk16 b → ctlOk (kemEncaps16 K v.callee (n, c) b) = true)
    (hctl : ctlOk (kemEncaps K.L v.callee) = true) :
    Verified X86_64.target (kemEncapsSel K v.callee) k := by
  unfold kemEncapsSel
  split
  · rename_i p b hs hb
    obtain ⟨m, c⟩ := p
    exact Verified.of_implies (encK_widen hn (encaps16_narrow hn hK v F16 T16 hs hb
      (hctl16 m c b (v.s16 m c hs) (v.batchH16 b hb)) hk.sat_left) hk.sat_left) hk
  · exact Verified.of_correct (kemEncaps_correct v W C hctl) (kemEncaps_ct v W C) hk

/-- Encapsulation with 16-bit polynomials leaves `scratch` from its `n`-th
byte on as it was. -/
theorem encapsSel_keep {K : Kem16} {n : Nat} (hn : n ≤ K.L.scr) (hK : KpkeOk K.L) (v : Sample4Impl)
    (F16 : EkF16.Ek16HWf (narrowK K n)) (T16 : EkF16.EkT16Wf (narrowK K n)) {m : String} {c : Prog isa}
    (hs : v.callee.s16 = some (m, c)) {b : Prog isa} (hb : v.callee.batchH16 = some b)
    (hctl : ctlOk (kemEncaps16 K v.callee (m, c) b) = true) (hsp : SpSafe (kemEncaps16 K v.callee (m, c) b))
    (hd : (kemEncaps16 K v.callee (m, c) b).x86_64Depth ≤ 32) {s : State} (hp : (encK K.L).pre s)
    {t : List Leak} {s' : State} (he : Exec isa (kemEncapsSel K v.callee) s t s') {i : Nat} (hi : n ≤ i)
    (hil : i < K.L.scr) : s'.mem (s.gpr .r8 + BitVec.ofNat 64 i) = s.mem (s.gpr .r8 + BitVec.ofNat 64 i) := by
  unfold kemEncapsSel at he
  rw [hs, hb] at he
  obtain ⟨-, hwr, -, -, -, -, -, -, -, d8, d9, -, -, -, -, -, -, -, -, -, b5, -, -, -, -, o5⟩ := id hp
  refine verified_keepTail (encaps16_narrow hn hK v F16 T16 hs hb hctl ⟨s, hp⟩) hsp hd (encK_pre hn hp)
    (by rw [hwr]; exact prefix3 hn) he o5 (fun r hr => ?_) b5 hi hil
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact .inr d8
  · exact .inr d9
  · exact .inl rfl

/-- No instruction of `kemEncapsSel K c` writes the stack pointer, if neither
of the functions it may run does. -/
theorem encapsSel_sp {K : Kem16} (v : Sample4Impl) {p : Instr → Bool}
    (h16 : ∀ n c b, S16Ok c → BatchHOk16 b → (kemEncaps16 K v.callee (n, c) b).all p = true)
    (h : (kemEncaps K.L v.callee).all p = true) : (kemEncapsSel K v.callee).all p = true := by
  unfold kemEncapsSel
  split
  · rename_i q b hs hb
    obtain ⟨n, c⟩ := q
    exact h16 n c b (v.s16 n c hs) (v.batchH16 b hb)
  · exact h

end VG.Proof.MlKem.X86_64

end

end

/-! ### `MlKem.X86_64.EkTop`, which the modules that import this one used -/

section

/-!
# ML-KEM on x86-64: encapsulation hashing the key

`kemEncaps L v.callee` for any implementation `v` of `vg_mlkem_sample_ntt4`,
with the sponge functions (`EkScalar.lean`), and a state its contract
permits (`encapsSat`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64

/-- A state satisfying the precondition of `vg_mlkem*_encaps` for keys of
`ekLen` bytes, ciphertexts of `ctLen` bytes and `scr` bytes of working space. -/
def encapsSat (ekLen ctLen scr : Nat) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x4000 | .r8 => 0x10000
    | .rsp => 0x80000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, ekLen⟩, ⟨0x2000, 32⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x4000, ctLen⟩, ⟨0x10000, scr⟩]

end VG.Proof.MlKem.X86_64

end

end

/-!
# ML-KEM on x86-64: decapsulation hashing `z ‖ c` in the matrix's fragments, for each implementation

An implementation `v` with a 16-bit sampler and a fragment sampling 16-bit
polynomials (`Callee4.s16`, `Callee4.batchH16`) runs the decapsulation with
16-bit polynomials that hashes `z ‖ c` in the fragments (`kemDecapsJ16`);
any other, the one with polynomials of `u32`s (`kemDecaps`). As
`EkSel16.lean`, whose `ek16_ctl` and `ek16_sp` give its control flow and
stack pointer.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64

/-- Decapsulation hashing `z ‖ c` in the fragments, against the contract of
`K` with the first `n` bytes of `scratch`. -/
theorem decapsJ16_narrow {K : Kem16} {n : Nat} (hn : n ≤ K.L.scr) (hK : KpkeOk K.L) (v : Sample4Impl)
    (F16 : DjF16.DjHWf (narrowK K n)) (T16 : DjF16.DjTWf (narrowK K n)) {m : String} {c : Prog isa}
    (hs : v.callee.s16 = some (m, c)) {b : Prog isa} (hb : v.callee.batchH16 = some b)
    (hctl : ctlOk (kemDecapsJ16 K v.callee (m, c) b) = true) (hsat : ∃ s, (decapsK K.L).pre s) :
    Verified X86_64.target (kemDecapsJ16 K v.callee (m, c) b) (decapsK (narrowL K.L n)) :=
  Verified.of_correct (kemDecapsJ16_correct (K := narrowK K n) (hK.narrow n) v F16 hs hb hctl)
    (kemDecapsJ16_ct (K := narrowK K n) (hK.narrow n) v F16 T16 hs hb)
    (.refl (hsat.elim fun _ hs => ⟨_, decapsK_pre hn hs⟩))

theorem decapsSel_verified {K : Kem16} {n : Nat} (hn : n ≤ K.L.scr) (hK : KpkeOk K.L) (v : Sample4Impl)
    (F16 : DjF16.DjHWf (narrowK K n)) (T16 : DjF16.DjTWf (narrowK K n)) (W : Decaps.DcWf K.L) {wc wd : List Nat}
    (C : KemCalls K.L wc wd) {k : Contract isa} (hk : (decapsK K.L).Implies k)
    (hctl16 : ∀ n c b, S16Ok c → BatchHOk16 b → ctlOk (kemDecapsJ16 K v.callee (n, c) b) = true)
    (hctl : ctlOk (kemDecaps K.L v.callee) = true) :
    Verified X86_64.target (kemDecapsSel K v.callee) k := by
  unfold kemDecapsSel
  split
  · rename_i p b hs hb
    obtain ⟨m, c⟩ := p
    exact Verified.of_implies (decapsK_widen hn (decapsJ16_narrow hn hK v F16 T16 hs hb
      (hctl16 m c b (v.s16 m c hs) (v.batchH16 b hb)) hk.sat_left) hk.sat_left) hk
  · exact Verified.of_correct (kemDecaps_correct v W C hctl) (kemDecaps_ct v W C) hk

/-- Decapsulation hashing `z ‖ c` in the fragments leaves `scratch` from its
`n`-th byte on as it was. -/
theorem decapsSel_keep {K : Kem16} {n : Nat} (hn : n ≤ K.L.scr) (hK : KpkeOk K.L) (v : Sample4Impl)
    (F16 : DjF16.DjHWf (narrowK K n)) (T16 : DjF16.DjTWf (narrowK K n)) {m : String} {c : Prog isa}
    (hs : v.callee.s16 = some (m, c)) {b : Prog isa} (hb : v.callee.batchH16 = some b)
    (hctl : ctlOk (kemDecapsJ16 K v.callee (m, c) b) = true) (hsp : SpSafe (kemDecapsJ16 K v.callee (m, c) b))
    (hd : (kemDecapsJ16 K v.callee (m, c) b).x86_64Depth ≤ 32) {s : State} (hp : (decapsK K.L).pre s)
    {t : List Leak} {s' : State} (he : Exec isa (kemDecapsSel K v.callee) s t s') {i : Nat} (hi : n ≤ i)
    (hil : i < K.L.scr) : s'.mem (s.gpr .rcx + BitVec.ofNat 64 i) = s.mem (s.gpr .rcx + BitVec.ofNat 64 i) := by
  unfold kemDecapsSel at he
  rw [hs, hb] at he
  obtain ⟨-, hwr, -, -, -, -, d5, -, -, -, -, -, -, -, b4, -, -, -, o4⟩ := id hp
  refine verified_keepTail (decapsJ16_narrow hn hK v F16 T16 hs hb hctl ⟨s, hp⟩) hsp hd (decapsK_pre hn hp)
    (by rw [hwr]; exact prefix2 hn) he o4 (fun r hr => ?_) b4 hi hil
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact .inr d5
  · exact .inl rfl

/-- No instruction of `kemDecapsSel K c` writes the stack pointer, if neither
of the functions it may run does. -/
theorem decapsSel_sp {K : Kem16} (v : Sample4Impl) {p : Instr → Bool}
    (h16 : ∀ n c b, S16Ok c → BatchHOk16 b → (kemDecapsJ16 K v.callee (n, c) b).all p = true)
    (h : (kemDecaps K.L v.callee).all p = true) : (kemDecapsSel K v.callee).all p = true := by
  unfold kemDecapsSel
  split
  · rename_i q b hs hb
    obtain ⟨n, c⟩ := q
    exact h16 n c b (v.s16 n c hs) (v.batchH16 b hb)
  · exact h

end VG.Proof.MlKem.X86_64
