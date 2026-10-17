module

public import VerifiedGarbage.Proof.MlKem.X86_64.EkInline
meta import VerifiedGarbage.Proof.MlKem.X86_64.EkInline
public import VerifiedGarbage.Proof.MlKem.HSponge
import VerifiedGarbage.Proof.MlKem.X86_64.S4Absorb
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.MlKem.X86_64.Zero
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
meta import Mathlib.Tactic.Conv
meta import VerifiedGarbage.Proof.MlKem.X86_64.YLanes

/-!
# ML-KEM on x86-64: encapsulation hashing the key, the fragments

The matrix of `kemEncaps` with a fragment `b` (`Encaps.frag`): fragment `i`
copies bytes `408 i` to `408 i + 407` of `pad(ek)` to `HB` (`hblk_ok`: from
`ek`, and for the last, its rest and the padding, `padTail_ok`), as the
blocks `3 i` to `3 i + 2` of `pad(ek)` (`blk`); writes the seeds of entries
`3 i` to `3 i + 3`; and inlines `b` (`sampleHAt_ok`), which samples entries
`3 i` to `3 i + 2` and absorbs the three blocks into the sponge's state at
`HS`. What holds before fragment `i` (`FI`): `EK`, `ρ` at `SB`,
the first `3 i` entries of `Â` (`MatB`), and the sponge's state after `3 i`
blocks (`HSponge.hstate`); the checks of the layout each piece needs are
evaluated for each parameter set (`EkFWf`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.EkF

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt keccakF)
open VG.Proof.Sha3 (xorAt)
open VG.Proof.MlKem.X86_64.Encaps (ecR ecW ecB ecB_bases ecChk EcWf)
open VG.Proof.MlKem.X86_64.Ek (EK ekE ekMs)
open VG.Proof.MlKem.HSponge (hstate padBlock)
open VG.Impl.MlKem.X86_64.Encaps (oHS oHB nb padTail hblk frag)

/-! ## The blocks of `pad(ek)` -/

/-- Block `t` of `pad(E)`, for `E` that does not end at a block boundary. -/
def blk (E : List Byte) (t : Nat) : List Byte :=
  if 136 * t + 136 ≤ E.length then (E.drop (136 * t)).take 136 else padBlock (E.drop (136 * t))

/-- `E`'s length leaves a partial last block, with room for the padding. -/
def Partial (E : List Byte) : Prop := 0 < E.length % 136 ∧ E.length % 136 < 135

theorem hstate_blk {E : List Byte} (hE : Partial E) {t : Nat} (ht : t ≤ E.length / 136) :
    keccakF (xorAt (hstate E t) 0 (blk E t)) = hstate E (t + 1) := by
  unfold blk
  split
  · exact HSponge.hstate_full (by omega)
  · have := Nat.div_add_mod E.length 136
    exact HSponge.hstate_padBlock (by obtain ⟨h1, h2⟩ := hE; omega) (by obtain ⟨h1, h2⟩ := hE; omega)

theorem habs_blk {E : List Byte} (hE : Partial E) {i : Nat} (hi : 3 * i + 3 ≤ E.length / 136 + 1) :
    SH.habs (hstate E (3 * i)) (fun j => blk E (3 * i + j)) 3 = hstate E (3 * i + 3) := by
  simp only [SH.habs, Nat.add_zero]
  rw [hstate_blk hE (by omega), hstate_blk hE (by omega), hstate_blk hE (by omega)]

/-! ## The checks of the layout -/

variable (L : Kem)

/-- A piece writing `ws` keeps `EK`, `ρ` at `SB` and the first `e` entries of `Â`. -/
def fkeep (ws : List (Ptr × Nat)) (e : Nat) : Bool :=
  ecChk L ws && keepB (ecB L) ws (sc oSB) 32 && (List.range e).all fun e' => keepB (ecB L) ws (pS (L.pA + e')) 1024

/-- ... and the sponge's state. -/
def hkeep (ws : List (Ptr × Nat)) (e : Nat) : Bool := fkeep L ws e && keepB (ecB L) ws (sc (oHS L)) 200

/-- The blocks of fragment `i`. -/
def hbChk (i : Nat) : Bool :=
  (if 408 * i + 408 ≤ L.ekLen then copyChk (ecB L) (ecW L) (sc (oHB L)) (.r14, 408 * i) 408
    else copyChk (ecB L) (ecW L) (sc (oHB L)) (.r14, 408 * i) (L.ekLen - 408 * i) &&
      inB (ecW L) (sc (oHB L)) 408 && keepB (ecB L) [(sc (oHB L + (L.ekLen - 408 * i)), 408 - (L.ekLen - 408 * i))]
        (sc (oHB L)) (L.ekLen - 408 * i)) &&
  hkeep L [(sc (oHB L), 408)] (3 * i)

/-- The seeds of fragment `i`. -/
def sdChk (i : Nat) : Bool :=
  (List.range 4).all fun K => seedsChk (ecB L) (ecW L) K && hkeep L (seedW K) (3 * i) &&
    keepB (ecB L) (seedW K) (sc (oHB L)) 408

/-- The fragment inlined, of fragment `i`. -/
def smChk (i : Nat) : Bool :=
  s4Chk (ecB L) (ecW L) (oP (L.pA + 3 * i)) (oP L.pW) &&
    fkeep L [(sc (oP (L.pA + 3 * i)), 4096), (sc (oP L.pW), 8192)] (3 * i)

/-- What each piece of the matrix needs of the layout, evaluated for each parameter set. -/
structure EkFWf : Prop extends EcWf L where
  ek8 : L.ekLen % 8 = 0 ∧ L.ekLen < 2 ^ 20
  part : 0 < L.ekLen % 136 ∧ L.ekLen % 136 < 135
  nbE : 3 * nb L = L.ekLen / 136 + 1
  nbK : 0 < nb L ∧ 3 * nb L ≤ L.k * L.k
  last : 272 < L.ekLen - 408 * (nb L - 1) ∧ L.ekLen - 408 * (nb L - 1) < 406 ∧ L.ekLen < 408 * nb L
  hbk : oHB L + 408 < 2 ^ 31 ∧ 408 * nb L < 2 ^ 31
  rC : (copyChk (ecB L) (ecW L) (sc oSB) (.r14, 384 * L.k) 32 && ecChk L [(sc oSB, 32)]) = true
  zC : (inB (ecW L) (sc (oHS L)) 200 && fkeep L [(sc (oHS L), 200)] 0) = true
  hb : ∀ i < nb L, hbChk L i = true
  sd : ∀ i < nb L, sdChk L i = true
  sm : ∀ i < nb L, smChk L i = true

/-! ## What holds before each fragment -/

/-- Before fragment `i`. -/
structure FI (L : Kem) (σ : State) (i : Nat) (s : State) : Prop where
  ec : EK L σ s
  sb : bytesAt s.mem (pa s (sc oSB)) 32 = Enc.rhoE L (ekE L σ)
  mat : MatB L (Enc.rhoE L (ekE L σ)) (3 * i) s
  hs : stateAt s.mem (pa s (sc (oHS L))) = hstate (ekE L σ) (3 * i)

theorem stateAt_keep {rbs wbs : List (Reg × Nat)} {s s' : State} (Lx : Lay rbs wbs s) {ws : List (Ptr × Nat)}
    (hP : PPostB s s' ws) {p : Ptr} (hc : keepB (rbs ++ wbs) ws p 200 = true) :
    stateAt s'.mem (pa s' p) = stateAt s.mem (pa s p) := by
  have e := Lx.keepBytes hP hc
  rw [hP.pa (keepB_cs hc)] at e ⊢
  refine VG.Proof.Sha3.stateAt_congr fun i hi => ?_
  have := congrArg (fun l => l[i]?) e
  simpa [bytesAt, List.getElem?_map, List.getElem?_range hi] using this

variable {L}

/-- A piece that writes `ws` and keeps `r15` keeps `FI`. -/
theorem FI.keep (W : EcWf L) {σ : State} (hp : (encK L).pre σ) {i : Nat} {s s' : State} (h : FI L σ i s)
    {ws : List (Ptr × Nat)} (hP : PPostB s s' ws) (h15 : s'.gpr .r15 = s.gpr .r15)
    (hc : hkeep L ws (3 * i) = true) : FI L σ i s' := by
  simp only [hkeep, fkeep, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨hE, hS⟩, hA⟩, hH⟩ := hc
  have L₀ := h.ec.lay W hp
  exact ⟨h.ec.step W hp hP hE, by rw [L₀.keepBytes hP hS]; exact h.sb,
    ⟨by rw [h15]; exact h.mat.r15, fun e he f hf => L₀.keepPoly hP (hA e he) (h.mat.mat e he f hf)⟩,
    by rw [stateAt_keep L₀ hP hH]; exact h.hs⟩

/-! ## Zeros and the padding -/


theorem zeros_ok (b : Reg) (off n : Nat) (s : State) (h0 : s.gpr .rax = 0) (hn : 8 * n < 2 ^ 64)
    (hw : ∀ j < n, InRegions s.wr (s.gpr b + BitVec.ofNat 64 off + BitVec.ofNat 64 (8 * j)) 8) :
    WP isa (.block ((List.range n).flatMap fun j => [.store (at_ b (off + 8 * j)) .rax])) s fun s' =>
      Keep [] s s' ∧ Frame [⟨s.gpr b + BitVec.ofNat 64 off, 8 * n⟩] s.mem s'.mem ∧
        ∀ i < 8 * n, s'.mem (s.gpr b + BitVec.ofNat 64 off + BitVec.ofNat 64 i) = 0 := by
  refine wp_range_flatMap (M := isa) (fun k s' => Keep [] s s' ∧
      Frame [⟨s.gpr b + BitVec.ofNat 64 off, 8 * n⟩] s.mem s'.mem ∧
      ∀ i < 8 * k, s'.mem (s.gpr b + BitVec.ofNat 64 off + BitVec.ofNat 64 i) = 0)
    (fun k s' hk ⟨hk', hf, hz⟩ => ?_) n (Nat.le_refl _) s
    ⟨Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have hb : s'.gpr b = s.gpr b := hk'.1 b (by simp)
  have ha : s'.gpr .rax = 0 := by rw [hk'.1 .rax (by simp), h0]
  have e : s.gpr b + BitVec.ofNat 64 (off + 8 * k) = s.gpr b + BitVec.ofNat 64 off + BitVec.ofNat 64 (8 * k) := by
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  refine WP.mono (zeroStep_ok b (off + 8 * k) s' (by rw [hk'.2.2, hb, e]; exact hw k hk))
    fun s'' ⟨hm, hk''⟩ => ⟨(hk'.trans hk'').mono (by simp), ?_, fun i hi => ?_⟩
  · rw [hm, hb, e]
    exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  · rw [hm, hb, e, ha]
    simp only [Mem.writeW, Mem.write]
    split
    · simp
    · rename_i hc
      refine hz i (Nat.lt_of_not_le fun hik => hc ?_)
      rw [Offset.sub_toNat _ hik (by omega)]
      omega

theorem mov0_ok (s : State) :
    WP isa (.block [.mov32 .rax (.imm 0)]) s fun s' => s'.gpr .rax = 0 ∧ s'.mem = s.mem ∧ Keep [.rax] s s' := by
  refine WP.mono (WP.keep [.rax] (Q := fun s' => s'.gpr .rax = 0 ∧ s'.mem = s.mem) ?_ (by rfl))
    fun s' ⟨⟨h0, hm⟩, k⟩ => ⟨h0, hm, k⟩
  xrun []

theorem padList (n : Nat) (a b : Byte) :
    ((List.replicate (n + 2) (0 : Byte)).set 0 a).set (n + 1) b = a :: (List.replicate n 0 ++ [b]) := by
  rw [List.replicate_succ, List.set_cons_zero, List.set_cons_succ, List.replicate_succ', List.set_append_right _ _ (by simp),
    List.length_replicate, Nat.sub_self, List.set_cons_zero]

theorem padTail_ok (L : Kem) {rbs wbs : List (Reg × Nat)} {s : State} (Lx : Lay rbs wbs s) {len : Nat}
    (hlen : len < 406) (h8 : len % 8 = 0) (hin : inB wbs (sc (oHB L)) 408 = true) :
    WP isa (.block (padTail L len)) s fun s' => PPost s s' [(sc (oHB L + len), 408 - len)] ∧
      bytesAt s'.mem (pa s (sc (oHB L + len))) (408 - len) =
        BitVec.ofNat 8 6 :: (List.replicate (406 - len) 0 ++ [BitVec.ofNat 8 0x80]) := by
  have hc := Lx.cW hin
  have hw : ∀ d n, d + n ≤ 408 → InRegions s.wr (s.gpr .rbx + BitVec.ofNat 64 (oHB L + d)) n :=
    fun d n h => by
      have := hc _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base (pa s (sc (oHB L))) h (by omega)⟩
      rwa [show pa s (sc (oHB L)) = s.gpr .rbx + BitVec.ofNat 64 (oHB L) from rfl, off_add] at this
  unfold padTail
  rw [← List.singleton_append, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (mov0_ok s) fun s₁ ⟨h0, hm1, k1⟩ => ?_
  have e1 : s₁.gpr .rbx = s.gpr .rbx := k1.1 .rbx (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zeros_ok .rbx (oHB L + len) ((408 - len) / 8) s₁ h0 (by omega) fun j hj => by
    rw [k1.2.2, e1, off_add, Nat.add_assoc]; exact hw (len + 8 * j) 8 (by omega)) fun s₂ ⟨k2, f2, z2⟩ => ?_
  have e2 : s₂.gpr .rbx = s.gpr .rbx := by rw [k2.1 .rbx (by simp), e1]
  rw [WP.block_append_iff]
  refine WP.mono (setB_ok (sc (oHB L + len)) 6 (show Reg.rbx ≠ .rax by decide) (by decide) s₂ (by
    show InRegions s₂.wr (s₂.gpr .rbx + BitVec.ofNat 64 (oHB L + len)) 1
    rw [k2.2.2, k1.2.2, e2, ← Nat.add_zero len]; exact hw _ 1 (by omega))) fun s₃ ⟨m3, k3⟩ => ?_
  have e3 : s₃.gpr .rbx = s.gpr .rbx := by rw [k3.1 .rbx (by decide), e2]
  refine WP.mono (setB_ok (sc (oHB L + 407)) 0x80 (show Reg.rbx ≠ .rax by decide) (by decide) s₃ (by
    show InRegions s₃.wr (s₃.gpr .rbx + BitVec.ofNat 64 (oHB L + 407)) 1
    rw [k3.2.2, k2.2.2, k1.2.2, e3]; exact hw _ 1 (by omega))) fun s₄ ⟨m4, k4⟩ => ?_
  have p6 : pa s₂ (sc (oHB L + len)) = pa s (sc (oHB L + len)) := by
    show s₂.gpr .rbx + _ = s.gpr .rbx + _; rw [e2]
  have p8 : pa s₃ (sc (oHB L + 407)) = pa s (sc (oHB L + len)) + BitVec.ofNat 64 (407 - len) := by
    show s₃.gpr .rbx + _ = s.gpr .rbx + _ + _; rw [e3, off_add, Nat.add_assoc, Nat.add_sub_cancel' (by omega)]
  have hn8 : 8 * ((408 - len) / 8) = 408 - len := by omega
  rw [hn8, e1] at f2 z2
  rw [p6] at m3
  rw [p8] at m4
  have hR : ∀ d n, d + n ≤ 408 - len →
      (⟨pa s (sc (oHB L + len)), 408 - len⟩ : Region).Contains (pa s (sc (oHB L + len)) + BitVec.ofNat 64 d) n :=
    fun d n h => Offset.contains_base _ h (by omega)
  refine ⟨post_of_keep (((k1.trans k2).trans k3).trans k4) (by decide) ?_, ?_⟩
  · show Frame [⟨pa s (sc (oHB L + len)), 408 - len⟩] s.mem s₄.mem
    rw [m4, m3, ← hm1]
    refine (f2.writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ (hR _ 1 (by omega))
    have := hR 0 1 (by omega)
    rwa [BitVec.add_zero] at this
  · have z : bytesAt s₂.mem (pa s (sc (oHB L + len))) (408 - len) = List.replicate (408 - len) 0 := by
      refine List.ext_getElem (by simp [bytesAt]) fun i h₁ _ => ?_
      simp only [bytesAt, List.length_map, List.length_range] at h₁
      simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
      exact z2 i h₁
    have w6 := bytesAt_writeW8 s₂.mem (pa s (sc (oHB L + len))) (i := 0) (len := 408 - len) (by omega)
      (by omega) (BitVec.ofNat 8 6)
    rw [BitVec.add_zero] at w6
    rw [m4, bytesAt_writeW8 _ _ (by omega) (by omega), m3, w6, z, show 408 - len = 406 - len + 2 by omega,
      show 407 - len = 406 - len + 1 by omega, padList]

/-! ## The blocks of a fragment -/

/-- The 408 bytes of `pad(E)` from `408 i`, for `E` whose last block ends in fragment `i` or later. -/

def hbE (E : List Byte) (i : Nat) : List Byte :=
  if 408 * i + 408 ≤ E.length then (E.drop (408 * i)).take 408
  else E.drop (408 * i) ++ BitVec.ofNat 8 6 :: (List.replicate (406 - (E.length - 408 * i)) 0 ++ [BitVec.ofNat 8 0x80])

theorem hbE_blk {E : List Byte} {i j : Nat} (hj : j < 3)
    (hp : 408 * i + 408 ≤ E.length ∨ (272 < E.length - 408 * i ∧ E.length - 408 * i < 406)) :
    ((hbE E i).drop (136 * j)).take 136 = blk E (3 * i + j) := by
  unfold hbE blk
  split
  · rw [ite_eq_left (show 136 * (3 * i + j) + 136 ≤ E.length by omega), List.drop_take, List.take_take, List.drop_drop]
    rw [show 408 * i + 136 * j = 136 * (3 * i + j) by omega, Nat.min_eq_left (by omega)]
  · rename_i hn
    have hA : (E.drop (408 * i)).length = E.length - 408 * i := List.length_drop
    rcases (by omega : j < 2 ∨ j = 2) with hj2 | rfl
    · rw [ite_eq_left (show 136 * (3 * i + j) + 136 ≤ E.length by omega), List.drop_append_of_le_length (by omega),
        List.take_append_of_le_length (by rw [List.length_drop]; omega), List.drop_drop,
        show 408 * i + 136 * j = 136 * (3 * i + j) by omega]
    · rw [ite_eq_right (show ¬136 * (3 * i + 2) + 136 ≤ E.length by omega), List.drop_append_of_le_length (by omega), List.drop_drop,
        List.take_of_length_le (by simp only [List.length_append, List.length_drop, List.length_cons,
          List.length_replicate, List.length_nil]; omega)]
      simp only [padBlock, List.length_drop, List.append_assoc, List.cons_append, List.nil_append,
        show 408 * i + 136 * 2 = 136 * (3 * i + 2) by omega,
        show 134 - (E.length - 136 * (3 * i + 2)) = 406 - (E.length - 408 * i) by omega]

theorem hblk_ok (F : EkFWf L) {σ : State} (hp : (encK L).pre σ) {i : Nat} (hi : i < nb L) {s : State}
    (h : FI L σ i s) :
    WP isa (hblk L i) s fun s' => PPostB s s' [(sc (oHB L), 408)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      bytesAt s'.mem (pa s (sc (oHB L))) 408 = hbE (ekE L σ) i := by
  have L₀ := h.ec.lay F.toEcWf hp
  have hc := F.hb i hi
  have hE : (ekE L σ).length = L.ekLen := bytesAt_length _ _ _
  have ek := h.ec.ek
  unfold hbChk at hc
  unfold hblk hbE
  rw [hE]
  by_cases hf : 408 * i + 408 ≤ L.ekLen
  · simp only [hf, ↓reduceIte, Bool.and_eq_true] at hc ⊢
    refine WP.mono (copy_okL L₀ (show Reg.r14 ≠ .rdi by decide) hc.1) fun s' ⟨hP, hb⟩ =>
      ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
    rw [hb, ← ek, bytesAt_slice _ _ hf, pa, pa, off_add, Nat.zero_add]
  · simp only [hf, ↓reduceIte, Bool.and_eq_true] at hc ⊢
    obtain ⟨⟨⟨hcp, hin⟩, hkp⟩, -⟩ := hc
    have hl := F.last
    have hn := F.nbE
    have hii : i = nb L - 1 := by omega
    have hlen : 272 < L.ekLen - 408 * i ∧ L.ekLen - 408 * i < 406 := by rw [hii]; exact ⟨hl.1, hl.2.1⟩
    have h8 : (L.ekLen - 408 * i) % 8 = 0 := by have := F.ek8.1; omega
    refine WP.seq (WP.mono (copy_okL L₀ (show Reg.r14 ≠ .rdi by decide) hcp) fun s₁ ⟨hP₁, hb₁⟩ => ?_)
    have L₁ := L₀.post hP₁.b (ecB_bases L)
    refine WP.mono (padTail_ok L L₁ hlen.2 h8 hin) fun s₂ ⟨hP₂, hb₂⟩ => ?_
    have e : pa s (sc (oHB L + (L.ekLen - 408 * i))) = pa s (sc (oHB L)) + BitVec.ofNat 64 (L.ekLen - 408 * i) :=
      (off_add _ _ _).symm
    have hP : PPost s s₂ [(sc (oHB L), 408)] := by
      refine (PPost.trans hP₁ hP₂ (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; exact rbx_cs)
        (ws := [(sc (oHB L), L.ekLen - 408 * i), (sc (oHB L + (L.ekLen - 408 * i)), 408 - (L.ekLen - 408 * i))])
        (fun w hw => List.mem_cons.2 (.inl (List.mem_singleton.1 hw)))
        (fun w hw => List.mem_cons.2 (.inr hw))).weaken fun w hw => ⟨_, List.mem_singleton_self _, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact Region.sub_prefix (by omega)
      · show Region.Sub ⟨pa s (sc (oHB L + (L.ekLen - 408 * i))), _⟩ ⟨pa s (sc (oHB L)), 408⟩
        rw [e]; exact Offset.sub_base _ (by omega)
    refine ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
    have k₁ := L₁.keepBytes hP₂.b hkp
    rw [hP₂.pa rbx_cs, hP₁.pa rbx_cs, hb₁] at k₁
    rw [hP₁.pa rbx_cs] at hb₂
    have sp := bytesAt_add s₂.mem (pa s (sc (oHB L))) (L.ekLen - 408 * i) (408 - (L.ekLen - 408 * i))
    rw [Nat.add_sub_cancel' (by omega), ← e, hb₂, k₁] at sp
    rw [sp, ← ek, bytesAt_drop _ _ (by omega), pa, pa, off_add, Nat.zero_add]

/-! ## The entries of a fragment -/

theorem allOk_add3 {k : Nat} {ρ : List Byte} {e : Nat} :
    allOk k ρ (e + 3) ↔ allOk k ρ e ∧ ((List.range 3).all fun t =>
      (sampleNTT minIterations (matSeed ρ ((e + t) / k) ((e + t) % k))).isSome) = true := by
  simp only [List.all_eq_true, List.mem_range]
  constructor
  · intro h; exact ⟨fun e' he => h e' (by omega), fun t ht => h (e + t) (by omega)⟩
  · rintro ⟨h, h3⟩ e' he
    rcases (by omega : e' < e ∨ e ≤ e') with he' | he'
    · exact h e' he'
    · have := h3 (e' - e) (by omega)
      rwa [Nat.add_sub_cancel' he'] at this

/-- The step of three entries. -/
theorem MatB.three {ρ : List Byte} {e : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State}
    (h : MatB L ρ e s) (Lx : Lay rbs wbs s) {ws : List (Ptr × Nat)} (hP : PPostB s s' ws)
    (kA : ∀ e' < e, keepB (rbs ++ wbs) ws (pS (L.pA + e')) 1024 = true)
    (h15 : s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&&
        (if (List.range 3).all (fun t => (sampleNTT minIterations
          (matSeed ρ ((e + t) / L.k) ((e + t) % L.k))).isSome) then 1 else 0)))
    (hres : ∀ t < 3, ∀ f, sampleNTT minIterations (matSeed ρ ((e + t) / L.k) ((e + t) % L.k)) = some f →
        PolyIs s'.mem (pa s (sc (oP (L.pA + e) + 1024 * t))) f) : MatB L ρ (e + 3) s' := by
  refine ⟨?_, fun e' he' f hf => ?_⟩
  · rw [h15, and_acc h.r15]
    exact ite_congr (propext allOk_add3.symm) (fun _ => rfl) (fun _ => rfl)
  · rcases (by omega : e' < e ∨ e ≤ e') with he'' | he''
    · exact Lx.keepPoly hP (kA e' he'') (h.mat e' he'' f hf)
    · have := hres (e' - e) (by omega) f (by rw [Nat.add_sub_cancel' he'']; exact hf)
      rw [hP.pa rbx_bases]
      rwa [show oP (L.pA + e) + 1024 * (e' - e) = oP (L.pA + e') by simp only [oP]; omega] at this

theorem habs_congr (H : Spec.Sha3.State) {f g : Nat → List Byte} :
    ∀ n, (∀ j < n, f j = g j) → SH.habs H f n = SH.habs H g n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [SH.habs]
    rw [habs_congr H n fun j hj => h j (by omega), h n (by omega)]

/-- While the seeds of fragment `i` are written. -/
structure SI (L : Kem) (σ : State) (i K : Nat) (s : State) : Prop where
  fi : FI L σ i s
  sd : SeedsIs (Enc.rhoE L (ekE L σ)) L.k (3 * i) K s
  hb : bytesAt s.mem (pa s (sc (oHB L))) 408 = hbE (ekE L σ) i

theorem seedI_ok (F : EkFWf L) {σ : State} (hp : (encK L).pre σ) {i : Nat} (hi : i < nb L) {K : Nat}
    (hK : K < 4) {s : State} (h : SI L σ i K s) :
    WP isa (seedAt K ((3 * i + K) / L.k) ((3 * i + K) % L.k)) s (SI L σ i (K + 1)) := by
  have W := F.toEcWf
  have hsd := F.sd i hi
  simp only [sdChk, List.all_eq_true, List.mem_range, Bool.and_eq_true] at hsd
  obtain ⟨⟨hs, hk⟩, hB⟩ := hsd K hK
  have L₀ := h.fi.ec.lay W hp
  have h16 : L.k * L.k ≤ 16 := Nat.mul_le_mul W.k.2 W.k.2
  have := F.nbK
  refine WP.mono (seed_step L₀ (ecB_bases L) (by omega) hs h.sd) fun s' ⟨hP, hS⟩ =>
    ⟨h.fi.keep W hp hP.b (hP.cs .r15 (by decide)) hk, hS, ?_⟩
  rw [L₀.keepBytes hP.b hB]; exact h.hb

theorem blocks_eq (F : EkFWf L) {σ : State} {i : Nat} (hi : i < nb L) {s : State}
    (hb : bytesAt s.mem (pa s (sc (oHB L))) 408 = hbE (ekE L σ) i) {j : Nat} (hj : j < 3) :
    bytesAt s.mem (pa s (sc (oP L.pW)) + BitVec.ofNat 64 (Sample4.oHB + 136 * j)) 136 =
      blk (ekE L σ) (3 * i + j) := by
  have hE : (ekE L σ).length = L.ekLen := bytesAt_length _ _ _
  have hl := F.last
  have hn := F.nbE
  rw [← hbE_blk hj (by rw [hE]; omega), ← hb, bytesAt_slice _ _ (by omega)]
  show bytesAt _ (s.gpr .rbx + BitVec.ofNat 64 (oP L.pW) + BitVec.ofNat 64 (Sample4.oHB + 136 * j)) 136 =
    bytesAt _ (s.gpr .rbx + BitVec.ofNat 64 (oP L.pW + Sample4.oHB) + BitVec.ofNat 64 (136 * j)) 136
  rw [off_add, off_add, Nat.add_assoc]

theorem frag_ok (F : EkFWf L) {b : Prog isa} (hb : BatchHOk b) {σ : State} (hp : (encK L).pre σ) {i : Nat}
    (hi : i < nb L) {s : State} (h : FI L σ i s) : WP isa (frag L b i) s (FI L σ (i + 1)) := by
  have W := F.toEcWf
  have hsm := F.sm i hi
  simp only [smChk, Bool.and_eq_true] at hsm
  have hc := F.hb i hi
  simp only [hbChk, Bool.and_eq_true] at hc
  unfold frag
  refine WP.seq (WP.mono (hblk_ok F hp hi h) fun s₁ ⟨hP₁, h15₁, hb₁⟩ => ?_)
  have f₁ := h.keep W hp hP₁ h15₁ hc.2
  have i₁ : SI L σ i 0 s₁ := ⟨f₁, ⟨f₁.sb, fun _ h => absurd h (Nat.not_lt_zero _)⟩,
    by rw [hP₁.pa rbx_bases]; exact hb₁⟩
  refine WP.seq (WP.mono (seedI_ok F hp hi (K := 0) (by decide) i₁) fun s₂ i₂ => ?_)
  refine WP.seq (WP.mono (seedI_ok F hp hi (K := 1) (by decide) i₂) fun s₃ i₃ => ?_)
  refine WP.seq (WP.mono (seedI_ok F hp hi (K := 2) (by decide) i₃) fun s₄ i₄ => ?_)
  refine WP.seq (WP.mono (seedI_ok F hp hi (K := 3) (by decide) i₄) fun s₅ i₅ => ?_)
  have L₅ := i₅.fi.ec.lay W hp
  refine WP.mono (sampleHAt_ok hb (SHH.of L₅ hsm.1)) fun s₆ h₆ => ?_
  have hk := hsm.2
  simp only [fkeep, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hk
  obtain ⟨⟨hE, hS⟩, hA⟩ := hk
  have hl := F.last
  have hn := F.nbE
  have hpart : Partial (ekE L σ) := by
    rw [Partial, show (ekE L σ).length = L.ekLen from bytesAt_length _ _ _]; exact F.part
  have hlen : (ekE L σ).length = L.ekLen := bytesAt_length _ _ _
  refine ⟨i₅.fi.ec.step W hp h₆.b hE, by rw [L₅.keepBytes h₆.b hS]; exact i₅.fi.sb, ?_, ?_⟩
  · rw [show 3 * (i + 1) = 3 * i + 3 by omega]
    refine MatB.three i₅.fi.mat L₅ h₆.b hA ?_ fun t ht f hf => ?_
    · rw [h₆.r15, all3, range_all_congr fun k hk => congrArg (fun B => (sampleNTT minIterations B).isSome)
        (seed4_eq i₅.sd (k := k) (by omega))]
    · have := h₆.res t ht f (by rw [seed4_eq i₅.sd (by omega)]; exact hf)
      rwa [poly4, pa, off_add] at this
  · have e1 : pa s₅ (sc (oHS L)) = pa s₅ (sc (oP L.pW)) + BitVec.ofNat 64 Sample4.oHS := (off_add _ _ _).symm
    rw [h₆.b.pa rbx_bases, e1, h₆.hs, ← e1, i₅.fi.hs,
      habs_congr _ 3 fun j hj => blocks_eq F hi i₅.hb hj, show 3 * (i + 1) = 3 * i + 3 by omega]
    exact habs_blk hpart (by rw [hlen]; omega)

theorem frags_ok (F : EkFWf L) {b : Prog isa} (hb : BatchHOk b) {σ : State} (hp : (encK L).pre σ) {s : State}
    (h : FI L σ 0 s) : WP isa (seqR (frag L b) 0 (nb L)) s (FI L σ (nb L)) := by
  have := seqR_ok (I := FI L σ) (nb L) 0 (fun k _ hk s hs => frag_ok F hb hp (by omega) hs) s h
  rwa [Nat.zero_add] at this

end VG.Proof.MlKem.X86_64.EkF
