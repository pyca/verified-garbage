module

import VerifiedGarbage.Proof.MlKem.X86_64.EkFrag16
public import VerifiedGarbage.Proof.MlKem.X86_64.EkFrag
meta import VerifiedGarbage.Proof.MlKem.X86_64.EkFrag16
public import VerifiedGarbage.Proof.MlKem.X86_64.Dc16Dec
meta import VerifiedGarbage.Proof.MlKem.X86_64.Dc16Dec
public import VerifiedGarbage.Proof.MlKem.X86_64.DcTop
meta import VerifiedGarbage.Proof.MlKem.X86_64.DcTop
public import VerifiedGarbage.Impl.MlKem.X86_64.DecapsJ16
meta import VerifiedGarbage.Impl.MlKem.X86_64.DecapsJ16
import VerifiedGarbage.Proof.Framework.Offset
import all Init.Data.Nat.Bitwise.Basic
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
meta import Mathlib.Tactic.Conv
meta import VerifiedGarbage.Proof.MlKem.X86_64.YLanes

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

/-- The context before `K̄`, in any run. -/
def dcXGA {L : Kem} {oc : Nat} (W : DcWfB L oc) : Ctx (dcR L) (dcW L) where
  Out s := ∃ σ, (decapsK L).pre σ ∧ DCG L σ s
  chk := dcgChk L
  bs := dcB_bases L
  lay := fun ⟨_, hp, h⟩ => h.dc.lay W hp
  step := fun ⟨σ, hp, h⟩ hP hc => ⟨σ, hp, h.step W hp hP hc⟩

/-- `z ‖ c`. -/
abbrev zcE (L : Kem) (σ : State) : List Byte := KPke.dkZ L.p (dcDk L σ) ++ dcC L σ

theorem zcE_length (L : Kem) (σ : State) : (zcE L σ).length = 32 + L.ctLen := by
  simp only [zcE, List.length_append, KPke.dkZ, List.length_take, List.length_drop, dcDk, dcC, bytesAt_length]
  have : L.dkLen = 768 * L.p.k + 96 := rfl
  omega

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
  omega

theorem zc_drop (L : Kem) (σ : State) {n : Nat} (hn : 32 ≤ n) : (zcE L σ).drop n = (dcC L σ).drop (n - 32) := by
  rw [zcE, List.drop_append, List.drop_eq_nil_of_le (by rw [dkZ_length]; omega), List.nil_append, dkZ_length]

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
      · exact Region.sub_prefix (by omega)
      · show Region.Sub ⟨pa s (sc (oHB K + 32)), _⟩ ⟨pa s (sc (oHB K)), 408⟩
        rw [e]; exact Offset.sub_base _ (by omega)
    refine ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
    have A : bytesAt s₂.mem (pa s (sc (oHB K))) 32 = KPke.dkZ K.L.p (dcDk K.L σ) := by
      have k₁ := L₁.keepBytes hP₂.b hkz
      rw [p₂, p₁] at k₁
      rw [k₁, hb₁, slice_of dc.dk (show 768 * K.L.k + 64 + 32 ≤ K.L.dkLen by omega)]
      rfl
    have B : bytesAt s₂.mem (pa s (sc (oHB K + 32))) 376 = (dcC K.L σ).take 376 := by
      have kc := L₀.keepBytes hP₁.b hkc
      rw [r₁, dc.c] at kc
      rw [← p₁, hb₂, r₁, ← bytesAt_take _ _ (show 376 ≤ K.L.ctLen by omega), kc]
    have sp := bytesAt_add s₂.mem (pa s (sc (oHB K))) 32 376
    rw [← e, A, B] at sp
    rw [sp, hbE, ite_eq_left (show 408 * 0 + 408 ≤ (zcE K.L σ).length by omega), Nat.mul_zero, List.drop_zero, zcE,
      List.take_append, List.take_of_length_le (l := KPke.dkZ K.L.p (dcDk K.L σ)) (by rw [dkZ_length]; omega),
      dkZ_length]
  · simp only [h0, ↓reduceIte] at hc ⊢
    have h32 : 32 ≤ 408 * i := by omega
    by_cases hf : 408 * i + 408 ≤ jLen K
    · simp only [hf, ↓reduceIte, Bool.and_eq_true] at hc ⊢
      refine WP.mono (copy_okL L₀ (show Reg.r14 ≠ .rdi by decide) hc.1) fun s' ⟨hP, hb⟩ =>
        ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
      rw [hb, slice_of dc.c (show 408 * i - 32 + 408 ≤ K.L.ctLen by omega), hbE,
        ite_eq_left (show 408 * i + 408 ≤ (zcE K.L σ).length by omega), zc_drop K.L σ h32]
    · simp only [hf, ↓reduceIte, Bool.and_eq_true] at hc ⊢
      obtain ⟨⟨⟨hcp, hin⟩, hkp⟩, -⟩ := hc
      have hii : i = nb K.L - 1 := by omega
      have hlen : 272 < jLen K - 408 * i ∧ jLen K - 408 * i < 406 := by rw [hii]; exact ⟨hl.1, hl.2.1⟩
      have hm8 : (jLen K - 408 * i) % 8 = 0 := by omega
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
          rw [e]; exact Offset.sub_base _ (by omega)
      refine ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
      have k₁ := L₁.keepBytes hP₂.b hkp
      rw [hP₂.pa rbx_cs, hP₁.pa rbx_cs, hb₁] at k₁
      rw [hP₁.pa rbx_cs] at hb₂
      have sp := bytesAt_add s₂.mem (pa s (sc (oHB K))) (jLen K - 408 * i) (408 - (jLen K - 408 * i))
      rw [Nat.add_sub_cancel' (by omega), ← e, hb₂, k₁] at sp
      rw [sp, slice_of dc.c (show 408 * i - 32 + (jLen K - 408 * i) ≤ K.L.ctLen by omega), hbE,
        ite_eq_right (show ¬408 * i + 408 ≤ (zcE K.L σ).length by omega), zc_drop K.L σ h32, hzl,
        List.take_of_length_le (by rw [List.length_drop, dcC, bytesAt_length]; omega)]

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
  refine WP.mono (seed_step L₀ (dcB_bases K.L) (by omega) hs h.sd) fun s' ⟨hP, hS⟩ =>
    ⟨h.fi.keep hP.b (hP.cs .r15 (by decide)) hk, hS, ?_⟩
  rw [L₀.keepBytes hP.b hB]; exact h.hb

theorem blocksJ_eq (F : DjFWf K) {σ : State} {i : Nat} (hi : i < nb K.L) {s : State}
    (hb : bytesAt s.mem (pa s (sc (oHB K))) 408 = hbE (zcE K.L σ) i (BitVec.ofNat 8 0x1f)) {j : Nat} (hj : j < 3) :
    bytesAt s.mem (pa s (sc (K.oW)) + BitVec.ofNat 64 (Sample4.oHB + 136 * j)) 136 =
      blk (zcE K.L σ) (3 * i + j) (BitVec.ofNat 8 0x1f) := by
  have hE : (zcE K.L σ).length = jLen K := zcE_length K.L σ
  have hl := F.last
  have hn := F.nbJ
  rw [← hbE_blk hj (by rw [hE]; omega), ← hb, bytesAt_slice _ _ (by omega)]
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
  · rw [show 3 * (i + 1) = 3 * i + 3 by omega]
    refine EkF16.MatB16.three i₅.fi.eb.m L₅ h₆.b hA ?_ fun t ht f hf => ?_
    · rw [h₆.r15, all3_16, range_all_congr fun k hk => congrArg (fun B => (sampleNTT minIterations B).isSome)
        (seed4_eq i₅.sd (k := k) (by omega))]
    · have := h₆.res t ht f (by rw [seed4_eq i₅.sd (by omega)]; exact hf)
      rwa [poly4W, pBytes_true, pa, off_add] at this
  · have e1 : pa s₅ (sc (oHS K)) = pa s₅ (sc (K.oW)) + BitVec.ofNat 64 Sample4.oHS := (off_add _ _ _).symm
    rw [h₆.b.pa rbx_bases, e1, h₆.hs, ← e1, i₅.fi.hs,
      habs_congr _ 3 fun j hj => blocksJ_eq F hi i₅.hb hj, show 3 * (i + 1) = 3 * i + 3 by omega]
    exact habs_blk hpart (by rw [hlen]; omega)

theorem fragsJ_ok (F : DjFWf K) {b : Prog isa} (hb : BatchHOk16 b) {σ : State} {s : State}
    (h : FJ F.toDcWfB σ 0 s) : WP isa (seqR (frag K b) 0 (nb K.L)) s (FJ F.toDcWfB σ (nb K.L)) := by
  have := seqR_ok (I := FJ F.toDcWfB σ) (nb K.L) 0 (fun k _ hk s hs => fragJ_ok F hb (by omega) hs) s h
  rwa [Nat.zero_add] at this

end VG.Proof.MlKem.X86_64.DjF16
