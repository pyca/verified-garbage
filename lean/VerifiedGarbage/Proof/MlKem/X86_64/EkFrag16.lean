module

public import VerifiedGarbage.Proof.MlKem.X86_64.EkFrag
meta import VerifiedGarbage.Proof.MlKem.X86_64.EkFrag
public import VerifiedGarbage.Proof.MlKem.X86_64.EkInline16
meta import VerifiedGarbage.Proof.MlKem.X86_64.EkInline16
meta import VerifiedGarbage.Proof.MlKem.X86_64.Enc16
public import VerifiedGarbage.Impl.MlKem.X86_64.Encaps16
public import VerifiedGarbage.Proof.MlKem.X86_64.EkBase
public import VerifiedGarbage.Proof.MlKem.X86_64.KgA16
meta import VerifiedGarbage.Impl.MlKem.X86_64.Encaps16
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on x86-64: encapsulation hashing the key with 16-bit polynomials, the fragments

As `EkFrag.lean`, for `kemEncaps16`'s layout `K` (`Encaps16.frag`): the
entries of `Â` are 512 bytes each, from `oA` (`MatB16`), and the fragment
`b`, which meets `sampleHKW true` (`BatchHOk16`), has its working space and
the sponge of `H` in `W` (from `oW`). The blocks of `pad(ek)` and their
padding are `EkFrag.lean`'s (`hbE`, `blk`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.EkF16

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt keccakF)
open VG.Proof.Sha3 (xorAt)
open VG.Proof.MlKem.X86_64.Encaps (ecR ecW ecB ecB_bases ecChk EcWfB)
open VG.Proof.MlKem.X86_64.Ek (EK ekE ekMs)
open VG.Proof.MlKem.HSponge (hstate padBlock)
open VG.Proof.MlKem.X86_64.EkF (blk Partial hstate_blk habs_blk stateAt_keep zeros_ok mov0_ok padList hbE hbE_blk
  allOk_add3 habs_congr)
open VG.Impl.MlKem.X86_64.Encaps (nb)
open VG.Impl.MlKem.X86_64.Encaps16 (oHS oHB padTail hblk frag)
open VG.Impl.MlKem.X86_64.Top16 (aP)

/-! ## The checks of the layout -/

variable (K : Kem16)

/-- A piece writing `ws` keeps `EK`, `ρ` at `SB` and the first `e` entries of `Â`. -/
def fkeep (ws : List (Ptr × Nat)) (e : Nat) : Bool :=
  ecChk K.L ws && keepB (ecB K.L) ws (sc oSB) 32 && (List.range e).all fun e' => keepB (ecB K.L) ws (aP K e') 512

/-- ... and the sponge's state. -/
def hkeep (ws : List (Ptr × Nat)) (e : Nat) : Bool := fkeep K ws e && keepB (ecB K.L) ws (sc (oHS K)) 200

/-- The blocks of fragment `i`. -/
def hbChk (i : Nat) : Bool :=
  (if 408 * i + 408 ≤ K.L.ekLen then copyChk (ecB K.L) (ecW K.L) (sc (oHB K)) (.r14, 408 * i) 408
    else copyChk (ecB K.L) (ecW K.L) (sc (oHB K)) (.r14, 408 * i) (K.L.ekLen - 408 * i) &&
      inB (ecW K.L) (sc (oHB K)) 408 && keepB (ecB K.L) [(sc (oHB K + (K.L.ekLen - 408 * i)), 408 - (K.L.ekLen - 408 * i))]
        (sc (oHB K)) (K.L.ekLen - 408 * i)) &&
  hkeep K [(sc (oHB K), 408)] (3 * i)

/-- The seeds of fragment `i`. -/
def sdChk (i : Nat) : Bool :=
  (List.range 4).all fun J => seedsChk (ecB K.L) (ecW K.L) J && hkeep K (seedW J) (3 * i) &&
    keepB (ecB K.L) (seedW J) (sc (oHB K)) 408

/-- The fragment inlined, of fragment `i`. -/
def smChk (i : Nat) : Bool :=
  s4_16Chk (ecB K.L) (ecW K.L) (K.oA + 512 * (3 * i)) K.oW &&
    fkeep K [(sc (K.oA + 512 * (3 * i)), 2048), (sc K.oW, 8192)] (3 * i)

/-- What each piece of the matrix needs of the layout, evaluated for each parameter set. -/
structure Ek16FWf : Prop extends EcWfB K.L where
  ek8 : K.L.ekLen % 8 = 0 ∧ K.L.ekLen < 2 ^ 20
  part : 0 < K.L.ekLen % 136 ∧ K.L.ekLen % 136 < 135
  nbE : 3 * nb K.L = K.L.ekLen / 136 + 1
  nbK : 0 < nb K.L ∧ 3 * nb K.L ≤ K.L.k * K.L.k
  last : 272 < K.L.ekLen - 408 * (nb K.L - 1) ∧ K.L.ekLen - 408 * (nb K.L - 1) < 406 ∧ K.L.ekLen < 408 * nb K.L
  hbk : oHB K + 408 < 2 ^ 31 ∧ 408 * nb K.L < 2 ^ 31
  rC : (copyChk (ecB K.L) (ecW K.L) (sc oSB) (.r14, 384 * K.L.k) 32 && ecChk K.L [(sc oSB, 32)]) = true
  zC : (inB (ecW K.L) (sc (oHS K)) 200 && fkeep K [(sc (oHS K), 200)] 0) = true
  hb : ∀ i < nb K.L, hbChk K i = true
  sd : ∀ i < nb K.L, sdChk K i = true
  sm : ∀ i < nb K.L, smChk K i = true


/-! ## What holds before each fragment -/

/-- Before fragment `i`. -/
structure FI16 (K : Kem16) (σ : State) (i : Nat) (s : State) : Prop where
  ec : EK K.L σ s
  sb : bytesAt s.mem (pa s (sc oSB)) 32 = Enc.rhoE K.L (ekE K.L σ)
  mat : MatB16 K.L.k K.oA (Enc.rhoE K.L (ekE K.L σ)) (3 * i) s
  hs : stateAt s.mem (pa s (sc (oHS K))) = hstate (ekE K.L σ) (3 * i)


variable {K}

/-- A piece that writes `ws` and keeps `r15` keeps `FI`. -/
theorem FI16.keep (W : EcWfB K.L) {σ : State} (hp : (encK K.L).pre σ) {i : Nat} {s s' : State} (h : FI16 K σ i s)
    {ws : List (Ptr × Nat)} (hP : PPostB s s' ws) (h15 : s'.gpr .r15 = s.gpr .r15)
    (hc : hkeep K ws (3 * i) = true) : FI16 K σ i s' := by
  simp only [hkeep, fkeep, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨hE, hS⟩, hA⟩, hH⟩ := hc
  have L₀ := h.ec.lay W hp
  exact ⟨h.ec.step W hp hP hE, by rw [L₀.keepBytes hP hS]; exact h.sb,
    ⟨by rw [h15]; exact h.mat.r15, fun e he f hf => L₀.keepPoly16 hP (hA e he) (h.mat.mat e he f hf)⟩,
    by rw [stateAt_keep L₀ hP hH]; exact h.hs⟩


theorem padTail16_ok (K : Kem16) {rbs wbs : List (Reg × Nat)} {s : State} (Lx : Lay rbs wbs s) {len : Nat}
    (hlen : len < 406) (h8 : len % 8 = 0) (hin : inB wbs (sc (oHB K)) 408 = true) {d : Nat} (hd : d < 256) :
    WP isa (.block (padTail K len d)) s fun s' => PPost s s' [(sc (oHB K + len), 408 - len)] ∧
      bytesAt s'.mem (pa s (sc (oHB K + len))) (408 - len) =
        BitVec.ofNat 8 d :: (List.replicate (406 - len) 0 ++ [BitVec.ofNat 8 0x80]) := by
  have hc := Lx.cW hin
  have hw : ∀ d n, d + n ≤ 408 → InRegions s.wr (s.gpr .rbx + BitVec.ofNat 64 (oHB K + d)) n :=
    fun d n h => by
      have := hc _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base (pa s (sc (oHB K))) h (by omega)⟩
      rwa [show pa s (sc (oHB K)) = s.gpr .rbx + BitVec.ofNat 64 (oHB K) from rfl, off_add] at this
  unfold padTail
  rw [← List.singleton_append, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (mov0_ok s) fun s₁ ⟨h0, hm1, k1⟩ => ?_
  have e1 : s₁.gpr .rbx = s.gpr .rbx := k1.1 .rbx (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zeros_ok .rbx (oHB K + len) ((408 - len) / 8) s₁ h0 (by omega) fun j hj => by
    rw [k1.2.2, e1, off_add, Nat.add_assoc]; exact hw (len + 8 * j) 8 (by omega)) fun s₂ ⟨k2, f2, z2⟩ => ?_
  have e2 : s₂.gpr .rbx = s.gpr .rbx := by rw [k2.1 .rbx (by simp), e1]
  rw [WP.block_append_iff]
  refine WP.mono (setB_ok (sc (oHB K + len)) d (show Reg.rbx ≠ .rax by decide) hd s₂ (by
    show InRegions s₂.wr (s₂.gpr .rbx + BitVec.ofNat 64 (oHB K + len)) 1
    rw [k2.2.2, k1.2.2, e2, ← Nat.add_zero len]; exact hw _ 1 (by omega))) fun s₃ ⟨m3, k3⟩ => ?_
  have e3 : s₃.gpr .rbx = s.gpr .rbx := by rw [k3.1 .rbx (by decide), e2]
  refine WP.mono (setB_ok (sc (oHB K + 407)) 0x80 (show Reg.rbx ≠ .rax by decide) (by decide) s₃ (by
    show InRegions s₃.wr (s₃.gpr .rbx + BitVec.ofNat 64 (oHB K + 407)) 1
    rw [k3.2.2, k2.2.2, k1.2.2, e3]; exact hw _ 1 (by omega))) fun s₄ ⟨m4, k4⟩ => ?_
  have p6 : pa s₂ (sc (oHB K + len)) = pa s (sc (oHB K + len)) := by
    show s₂.gpr .rbx + _ = s.gpr .rbx + _; rw [e2]
  have p8 : pa s₃ (sc (oHB K + 407)) = pa s (sc (oHB K + len)) + BitVec.ofNat 64 (407 - len) := by
    show s₃.gpr .rbx + _ = s.gpr .rbx + _ + _; rw [e3, off_add, Nat.add_assoc, Nat.add_sub_cancel' (by omega)]
  have hn8 : 8 * ((408 - len) / 8) = 408 - len := by omega
  rw [hn8, e1] at f2 z2
  rw [p6] at m3
  rw [p8] at m4
  have hR : ∀ d n, d + n ≤ 408 - len →
      (⟨pa s (sc (oHB K + len)), 408 - len⟩ : Region).Contains (pa s (sc (oHB K + len)) + BitVec.ofNat 64 d) n :=
    fun d n h => Offset.contains_base _ h (by omega)
  refine ⟨post_of_keep (((k1.trans k2).trans k3).trans k4) (by decide) ?_, ?_⟩
  · show Frame [⟨pa s (sc (oHB K + len)), 408 - len⟩] s.mem s₄.mem
    rw [m4, m3, ← hm1]
    refine (f2.writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ (hR _ 1 (by omega))
    have := hR 0 1 (by omega)
    rwa [BitVec.add_zero] at this
  · have z : bytesAt s₂.mem (pa s (sc (oHB K + len))) (408 - len) = List.replicate (408 - len) 0 := by
      refine List.ext_getElem (by simp [bytesAt]) fun i h₁ _ => ?_
      simp only [bytesAt, List.length_map, List.length_range] at h₁
      simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
      exact z2 i h₁
    have w6 := bytesAt_writeW8 s₂.mem (pa s (sc (oHB K + len))) (i := 0) (len := 408 - len) (by omega)
      (by omega) (BitVec.ofNat 8 d)
    rw [BitVec.add_zero] at w6
    rw [m4, bytesAt_writeW8 _ _ (by omega) (by omega), m3, w6, z, show 408 - len = 406 - len + 2 by omega,
      show 407 - len = 406 - len + 1 by omega, padList]


theorem hblk16_ok (F : Ek16FWf K) {σ : State} (hp : (encK K.L).pre σ) {i : Nat} (hi : i < nb K.L) {s : State}
    (h : FI16 K σ i s) :
    WP isa (hblk K i) s fun s' => PPostB s s' [(sc (oHB K), 408)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      bytesAt s'.mem (pa s (sc (oHB K))) 408 = hbE (ekE K.L σ) i := by
  have L₀ := h.ec.lay F.toEcWfB hp
  have hc := F.hb i hi
  have hE : (ekE K.L σ).length = K.L.ekLen := bytesAt_length _ _ _
  have ek := h.ec.ek
  unfold hbChk at hc
  unfold hblk hbE
  rw [hE]
  by_cases hf : 408 * i + 408 ≤ K.L.ekLen
  · simp only [hf, ↓reduceIte, Bool.and_eq_true] at hc ⊢
    refine WP.mono (copy_okL L₀ (show Reg.r14 ≠ .rdi by decide) hc.1) fun s' ⟨hP, hb⟩ =>
      ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
    rw [hb, ← ek, bytesAt_slice _ _ hf, pa, pa, off_add, Nat.zero_add]
  · simp only [hf, ↓reduceIte, Bool.and_eq_true] at hc ⊢
    obtain ⟨⟨⟨hcp, hin⟩, hkp⟩, -⟩ := hc
    have hl := F.last
    have hn := F.nbE
    have hii : i = nb K.L - 1 := by omega
    have hlen : 272 < K.L.ekLen - 408 * i ∧ K.L.ekLen - 408 * i < 406 := by rw [hii]; exact ⟨hl.1, hl.2.1⟩
    have h8 : (K.L.ekLen - 408 * i) % 8 = 0 := by have := F.ek8.1; omega
    refine WP.seq (WP.mono (copy_okL L₀ (show Reg.r14 ≠ .rdi by decide) hcp) fun s₁ ⟨hP₁, hb₁⟩ => ?_)
    have L₁ := L₀.post hP₁.b (ecB_bases K.L)
    refine WP.mono (padTail16_ok K L₁ hlen.2 h8 hin (d := 6) (by decide)) fun s₂ ⟨hP₂, hb₂⟩ => ?_
    have e : pa s (sc (oHB K + (K.L.ekLen - 408 * i))) = pa s (sc (oHB K)) + BitVec.ofNat 64 (K.L.ekLen - 408 * i) :=
      (off_add _ _ _).symm
    have hP : PPost s s₂ [(sc (oHB K), 408)] := by
      refine (PPost.trans hP₁ hP₂ (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; exact rbx_cs)
        (ws := [(sc (oHB K), K.L.ekLen - 408 * i), (sc (oHB K + (K.L.ekLen - 408 * i)), 408 - (K.L.ekLen - 408 * i))])
        (fun w hw => List.mem_cons.2 (.inl (List.mem_singleton.1 hw)))
        (fun w hw => List.mem_cons.2 (.inr hw))).weaken fun w hw => ⟨_, List.mem_singleton_self _, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact Region.sub_prefix (by omega)
      · show Region.Sub ⟨pa s (sc (oHB K + (K.L.ekLen - 408 * i))), _⟩ ⟨pa s (sc (oHB K)), 408⟩
        rw [e]; exact Offset.sub_base _ (by omega)
    refine ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
    have k₁ := L₁.keepBytes hP₂.b hkp
    rw [hP₂.pa rbx_cs, hP₁.pa rbx_cs, hb₁] at k₁
    rw [hP₁.pa rbx_cs] at hb₂
    have sp := bytesAt_add s₂.mem (pa s (sc (oHB K))) (K.L.ekLen - 408 * i) (408 - (K.L.ekLen - 408 * i))
    rw [Nat.add_sub_cancel' (by omega), ← e, hb₂, k₁] at sp
    rw [sp, ← ek, bytesAt_drop _ _ (by omega), pa, pa, off_add, Nat.zero_add]


/-- The step of three entries. -/
theorem MatB16.three {ρ : List Byte} {e : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State}
    (h : MatB16 K.L.k K.oA ρ e s) (Lx : Lay rbs wbs s) {ws : List (Ptr × Nat)} (hP : PPostB s s' ws)
    (kA : ∀ e' < e, keepB (rbs ++ wbs) ws (aP K e') 512 = true)
    (h15 : s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&&
        (if (List.range 3).all (fun t => (sampleNTT minIterations
          (matSeed ρ ((e + t) / K.L.k) ((e + t) % K.L.k))).isSome) then 1 else 0)))
    (hres : ∀ t < 3, ∀ f, sampleNTT minIterations (matSeed ρ ((e + t) / K.L.k) ((e + t) % K.L.k)) = some f →
        PolyIsW 16 s'.mem (pa s (sc (K.oA + 512 * e + 512 * t))) f) : MatB16 K.L.k K.oA ρ (e + 3) s' := by
  refine ⟨?_, fun e' he' f hf => ?_⟩
  · rw [h15, and_acc h.r15]
    exact ite_congr (propext allOk_add3.symm) (fun _ => rfl) (fun _ => rfl)
  · rcases (by omega : e' < e ∨ e ≤ e') with he'' | he''
    · exact Lx.keepPoly16 hP (kA e' he'') (h.mat e' he'' f hf)
    · have := hres (e' - e) (by omega) f (by rw [Nat.add_sub_cancel' he'']; exact hf)
      rw [hP.pa rbx_bases]
      rwa [show K.oA + 512 * e + 512 * (e' - e) = K.oA + 512 * e' by omega] at this


/-- While the seeds of fragment `i` are written. -/
structure SI16 (K : Kem16) (σ : State) (i J : Nat) (s : State) : Prop where
  fi : FI16 K σ i s
  sd : SeedsIs (Enc.rhoE K.L (ekE K.L σ)) K.L.k (3 * i) J s
  hb : bytesAt s.mem (pa s (sc (oHB K))) 408 = hbE (ekE K.L σ) i

theorem seedI16_ok (F : Ek16FWf K) {σ : State} (hp : (encK K.L).pre σ) {i : Nat} (hi : i < nb K.L) {J : Nat}
    (hJ : J < 4) {s : State} (h : SI16 K σ i J s) :
    WP isa (seedAt J ((3 * i + J) / K.L.k) ((3 * i + J) % K.L.k)) s (SI16 K σ i (J + 1)) := by
  have W := F.toEcWfB
  have hsd := F.sd i hi
  simp only [sdChk, List.all_eq_true, List.mem_range, Bool.and_eq_true] at hsd
  obtain ⟨⟨hs, hk⟩, hB⟩ := hsd J hJ
  have L₀ := h.fi.ec.lay W hp
  have h16 : K.L.k * K.L.k ≤ 16 := Nat.mul_le_mul W.k.2 W.k.2
  have := F.nbK
  refine WP.mono (seed_step L₀ (ecB_bases K.L) (by omega) hs h.sd) fun s' ⟨hP, hS⟩ =>
    ⟨h.fi.keep W hp hP.b (hP.cs .r15 (by decide)) hk, hS, ?_⟩
  rw [L₀.keepBytes hP.b hB]; exact h.hb

theorem blocks16_eq (F : Ek16FWf K) {σ : State} {i : Nat} (hi : i < nb K.L) {s : State}
    (hb : bytesAt s.mem (pa s (sc (oHB K))) 408 = hbE (ekE K.L σ) i) {j : Nat} (hj : j < 3) :
    bytesAt s.mem (pa s (sc (K.oW)) + BitVec.ofNat 64 (Sample4.oHB + 136 * j)) 136 =
      blk (ekE K.L σ) (3 * i + j) := by
  have hE : (ekE K.L σ).length = K.L.ekLen := bytesAt_length _ _ _
  have hl := F.last
  have hn := F.nbE
  rw [← hbE_blk hj (by rw [hE]; omega), ← hb, bytesAt_slice _ _ (by omega)]
  show bytesAt _ (s.gpr .rbx + BitVec.ofNat 64 (K.oW) + BitVec.ofNat 64 (Sample4.oHB + 136 * j)) 136 =
    bytesAt _ (s.gpr .rbx + BitVec.ofNat 64 (K.oW + Sample4.oHB) + BitVec.ofNat 64 (136 * j)) 136
  rw [off_add, off_add, Nat.add_assoc]

theorem frag16_ok (F : Ek16FWf K) {b : Prog isa} (hb : BatchHOk16 b) {σ : State} (hp : (encK K.L).pre σ) {i : Nat}
    (hi : i < nb K.L) {s : State} (h : FI16 K σ i s) : WP isa (frag K b i) s (FI16 K σ (i + 1)) := by
  have W := F.toEcWfB
  have hsm := F.sm i hi
  simp only [smChk, Bool.and_eq_true] at hsm
  have hc := F.hb i hi
  simp only [hbChk, Bool.and_eq_true] at hc
  unfold frag
  refine WP.seq (WP.mono (hblk16_ok F hp hi h) fun s₁ ⟨hP₁, h15₁, hb₁⟩ => ?_)
  have f₁ := h.keep W hp hP₁ h15₁ hc.2
  have i₁ : SI16 K σ i 0 s₁ := ⟨f₁, ⟨f₁.sb, fun _ h => absurd h (Nat.not_lt_zero _)⟩,
    by rw [hP₁.pa rbx_bases]; exact hb₁⟩
  refine WP.seq (WP.mono (seedI16_ok F hp hi (J := 0) (by decide) i₁) fun s₂ i₂ => ?_)
  refine WP.seq (WP.mono (seedI16_ok F hp hi (J := 1) (by decide) i₂) fun s₃ i₃ => ?_)
  refine WP.seq (WP.mono (seedI16_ok F hp hi (J := 2) (by decide) i₃) fun s₄ i₄ => ?_)
  refine WP.seq (WP.mono (seedI16_ok F hp hi (J := 3) (by decide) i₄) fun s₅ i₅ => ?_)
  have L₅ := i₅.fi.ec.lay W hp
  refine WP.mono (sampleHAt16_ok hb (SHH16.of L₅ hsm.1)) fun s₆ h₆ => ?_
  have hk := hsm.2
  simp only [fkeep, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hk
  obtain ⟨⟨hE, hS⟩, hA⟩ := hk
  have hl := F.last
  have hn := F.nbE
  have hpart : Partial (ekE K.L σ) := by
    rw [Partial, show (ekE K.L σ).length = K.L.ekLen from bytesAt_length _ _ _]; exact F.part
  have hlen : (ekE K.L σ).length = K.L.ekLen := bytesAt_length _ _ _
  refine ⟨i₅.fi.ec.step W hp h₆.b hE, by rw [L₅.keepBytes h₆.b hS]; exact i₅.fi.sb, ?_, ?_⟩
  · rw [show 3 * (i + 1) = 3 * i + 3 by omega]
    refine MatB16.three i₅.fi.mat L₅ h₆.b hA ?_ fun t ht f hf => ?_
    · rw [h₆.r15, all3_16, range_all_congr fun k hk => congrArg (fun B => (sampleNTT minIterations B).isSome)
        (seed4_eq i₅.sd (k := k) (by omega))]
    · have := h₆.res t ht f (by rw [seed4_eq i₅.sd (by omega)]; exact hf)
      rwa [poly4W, pBytes_true, pa, off_add] at this
  · have e1 : pa s₅ (sc (oHS K)) = pa s₅ (sc (K.oW)) + BitVec.ofNat 64 Sample4.oHS := (off_add _ _ _).symm
    rw [h₆.b.pa rbx_bases, e1, h₆.hs, ← e1, i₅.fi.hs,
      habs_congr _ 3 fun j hj => blocks16_eq F hi i₅.hb hj, show 3 * (i + 1) = 3 * i + 3 by omega]
    exact habs_blk hpart (by rw [hlen]; omega)

theorem frags16_ok (F : Ek16FWf K) {b : Prog isa} (hb : BatchHOk16 b) {σ : State} (hp : (encK K.L).pre σ) {s : State}
    (h : FI16 K σ 0 s) : WP isa (seqR (frag K b) 0 (nb K.L)) s (FI16 K σ (nb K.L)) := by
  have := seqR_ok (I := FI16 K σ) (nb K.L) 0 (fun k _ hk s hs => frag16_ok F hb hp (by omega) hs) s h
  rwa [Nat.zero_add] at this


end VG.Proof.MlKem.X86_64.EkF16
