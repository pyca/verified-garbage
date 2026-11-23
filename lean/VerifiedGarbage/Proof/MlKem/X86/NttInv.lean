module

public import VerifiedGarbage.Proof.MlKem.X86.VLanes
public import VerifiedGarbage.Proof.MlKem.X86.Leaf
public import VerifiedGarbage.Proof.MlKem.NttLayer
public import VerifiedGarbage.Proof.MlKem.PolyContract
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.Proof.MlKem.X86.Mcdt
public import VerifiedGarbage.Impl.MlKem.X86.Ntt
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.SseWord
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.MlKem.X86.Common
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.MlKem.X86.Common
meta import VerifiedGarbage.Proof.MlKem.X86.VLanes
meta import VerifiedGarbage.Proof.MlKem.X86.Leaf
meta import VerifiedGarbage.Proof.MlKem.NttLayer
meta import VerifiedGarbage.Proof.MlKem.X86.Mcdt
meta import VerifiedGarbage.Impl.MlKem.X86.Ntt
meta import VerifiedGarbage.Proof.Framework.X86.AllocFrame
meta import VerifiedGarbage.Proof.Framework.X86.Sse
meta import VerifiedGarbage.Proof.Framework.X86.SseDword
meta import VerifiedGarbage.Proof.Framework.X86.SseWord
meta import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
meta import VerifiedGarbage.Proof.Framework.X86.Wp
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# ML-KEM on x86 (32-bit): `vg_mlkem_ntt` and `vg_mlkem_inv_ntt`

The vector code of `Impl/MlKem/X86/Ntt.lean`, against the contracts the
scalar code it replaces had.

* The code of eight butterflies (`CoreOk`: `fCore_ok` for `NTT`, `iCore_ok`
  for `NTT⁻¹`) leaves the vectors `VLanes.lean` describes, and a body
  (`BodyOk`: `lBody_ok`, `body4_ok`, `body2_ok`) stores, at `[eax]` and
  `[eax + d]`, those of the vectors it loads there and the zetas in `xmm5`
  (run an instruction at a time, from a state given by its XMM registers).
* In memory (`Base`, `Co`), the words a layer has done are the coefficients
  of the layer's result `G`, and the others those of its argument `f`;
  `body_step` is a step on two vectors of coefficients, none of which is
  done, whose pairs are a layer's (`NewOk`).
* A layer with `len ≥ 8` (`lay8_piece`) is the loop over its blocks
  (`LInv`) of the loop over a block's groups (`GInv`), with the zeta of the
  block from the table (`blkInit_wp`, `gstep`, `blkEnd_wp`); the layers
  with `len = 4` and `len = 2` (`layFlat_piece`) are one loop (`FInv`,
  `fstep`), whose zetas are loaded for each step (`ZlOk`, `FlatOk`). Before
  each layer (`LS`) every word is the coefficient of the layers so far.
* `init_piece` sets the constants and the table (`wtableN_spec`),
  `pack_piece` copies the coefficients of `f` to the words (`KInv`), and
  `unpack_piece` copies them back (`UInv`), through `scaleCore` for
  `NTT⁻¹`.

Each function (`NttFwd.verified`, `NttInvP.verified`) is its body inside
an allocation of four bytes (`Piece.alloc`) inside the MCDT frame
(`Piece.mcdt`, `wframe_piece`), constant time by the analysis of general
and XMM registers (`Piece.sse`) from `esp` and the pointers `eax`, `ecx`
and `edx` (and the counter `ecx`), which each piece gets from the
arguments.
-/

@[expose] public section

/-! ## The entry state -/

namespace VG.Proof.MlKem.X86.NttLoop

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem

section
variable (s₀ : State)
abbrev fP : BitVec 32 := arg s₀ 0
abbrev sP : BitVec 32 := arg s₀ 1
abbrev fA : Addr := (fP s₀).setWidth 64
abbrev sA : Addr := (sP s₀).setWidth 64
abbrev aR : Region := ⟨argAddr s₀ 0, 8⟩
abbrev stkR : Region := ⟨(E0 s₀).setWidth 64 - 16#64, 16⟩
end

structure Pre (s₀ : State) : Prop where
  sp : 16 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 8 ≤ 2 ^ 32
  rd : s₀.rd = []
  wr : s₀.wr = [polyRegion (fA s₀), polyRegion (sA s₀), aR s₀]
  f_s : (polyRegion (fA s₀)).Disjoint (polyRegion (sA s₀))
  f_a : (polyRegion (fA s₀)).Disjoint (aR s₀)
  s_a : (polyRegion (sA s₀)).Disjoint (aR s₀)
  ret_f : (retR s₀).Disjoint (polyRegion (fA s₀))
  ret_s : (retR s₀).Disjoint (polyRegion (sA s₀))
  ret_a : (retR s₀).Disjoint (aR s₀)
  stk_f : (stkR s₀).Disjoint (polyRegion (fA s₀))
  stk_s : (stkR s₀).Disjoint (polyRegion (sA s₀))
  stk_a : (stkR s₀).Disjoint (aR s₀)
  f_fit : (fP s₀).toNat + 1024 ≤ 2 ^ 32
  s_fit : (sP s₀).toNat + 1024 ≤ 2 ^ 32
  f_red : Reduced s₀.mem (fA s₀)

def Pub (s₀ s₀' : State) : Prop := E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1

theorem Pre.arg_in {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 2) : (aR s₀).Contains (argAddr s₀ i) 4 := by
  have := hp.sp'
  simp only [argAddr, Region.Contains, E0] at this ⊢
  bv_omega

/-- The pointer compared with the end of a polynomial. -/
theorem end_cmp (x : BitVec 32) {X : Nat} (hX : X ≤ 1024) :
    (x + BitVec.ofNat 32 X - (x + 1024) == 0) = decide (X = 1024) := by
  rw [sub_beq_zero, BitVec.toNat_add, BitVec.toNat_add, toNat_ofNat32 (by omega_arith),
    show (1024 : BitVec 32).toNat = 1024 from rfl]
  simp only [Nat.reducePow]
  exact decide_eq_decide.mpr (by constructor <;> intro h <;> omega_arith)

end VG.Proof.MlKem.X86.NttLoop

namespace VG.Proof.MlKem.X86.Vec

open VG VG.X86 VG.X86.Lanes VG.Impl.MlKem.X86
open VG.Proof.MlKem VG.Spec.MlKem
open VG.Proof.MlKem.X86.NttLoop (fP sP fA sA aR stkR Pre Pub)
open VG.Proof.MlKem.X86.Piece (sse)

/-! ## Straight-line XMM code -/

variable {s : State}

/-- An instruction that writes an XMM register, from a state given by its XMM registers. -/
theorem wp_xs {f : XReg → BitVec 128} {i : Instr} {is : List Instr} {Q : State → Prop} {d : XReg} {v : BitVec 128}
    (h : exec i { s with xmm := f } = some (State.setXmm { s with xmm := f } d v))
    (k : WP isa (.block is) { s with xmm := fun r => if r = d then v else f r } Q) :
    WP isa (.block (i :: is)) { s with xmm := f } Q := Wp.cons h k

/-- `pmullw`, inside an MCDT frame. -/
theorem wp_ml {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} {d r : XReg} (hm : 0 < s.mcdt)
    (k : WP isa (.block is) { s with xmm := fun x => if x = d then pmullw (f d) (f r) else f x } Q) :
    WP isa (.block (.pmullw d r :: is)) { s with xmm := f } Q :=
  Wp.cons (show (if 0 < s.mcdt then some _ else none) = _ by rw [ite_eq_left hm]; rfl) k

/-- `pmulhw`, inside an MCDT frame. -/
theorem wp_mh {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} {d r : XReg} (hm : 0 < s.mcdt)
    (k : WP isa (.block is) { s with xmm := fun x => if x = d then pmulhw (f d) (f r) else f x } Q) :
    WP isa (.block (.pmulhw d r :: is)) { s with xmm := f } Q :=
  Wp.cons (show (if 0 < s.mcdt then some _ else none) = _ by rw [ite_eq_left hm]; rfl) k

/-- A 16-byte load. -/
theorem wp_ld {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} {d : XReg} {m : MemOp} {a : Addr}
    (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 16)
    (k : WP isa (.block is) { s with xmm := fun r => if r = d then s.mem.readW a 128 else f r } Q) :
    WP isa (.block (.movdquLoad d m :: is)) { s with xmm := f } Q :=
  Wp.cons (show (State.load128 { s with xmm := f } (s.ea m)).map _ = _ by
    rw [ha, State.load128, ite_eq_left hin]; rfl) k

/-- A 16-byte store. -/
theorem wp_st {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} {r : XReg} {m : MemOp} {a : Addr}
    (ha : s.ea m = a) (hin : InRegions s.wr a 16)
    (k : WP isa (.block is) { ({ s with mem := s.mem.writeW a (f r) } : State) with xmm := f } Q) :
    WP isa (.block (.movdquStore m r :: is)) { s with xmm := f } Q :=
  Wp.cons (show State.store128 { s with xmm := f } (s.ea m) (f r) = _ by
    rw [ha, State.store128, ite_eq_left hin]) k

/-- An 8-byte load. -/
theorem wp_lq {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} {d : XReg} {m : MemOp} {a : Addr}
    (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : WP isa (.block is)
      { s with xmm := fun r => if r = d then (0 : BitVec 64) ++ s.mem.readW a 64 else f r } Q) :
    WP isa (.block (.movqLoad d m :: is)) { s with xmm := f } Q :=
  Wp.cons (show (State.load64 { s with xmm := f } (s.ea m)).map _ = _ by
    rw [ha, State.load64, ite_eq_left hin]; rfl) k

theorem inRdN {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n :=
  let ⟨r, hr, c⟩ := h; ⟨r, List.mem_append_right _ hr, c⟩

/-- The constants: `q` in the words of `xmm7` and `q⁻¹ mod 2¹⁶` in those of `xmm6`. -/
structure VK (f : XReg → BitVec 128) : Prop where
  q : f .xmm7 = qV
  qi : f .xmm6 = qinvV

theorem VK.of_eq {f g : XReg → BitVec 128} (hc : VK f) (h7 : g .xmm7 = f .xmm7) (h6 : g .xmm6 = f .xmm6) : VK g :=
  ⟨h7.trans hc.q, h6.trans hc.qi⟩

/-- `wmont` on `xmm0`, by the words of `xmm5`. -/
theorem wmont_wp {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} (hm : 0 < s.mcdt) (hc : VK f)
    (k : ∀ g : XReg → BitVec 128, g .xmm0 = montV (f .xmm0) (f .xmm5) →
      (∀ r, r ≠ .xmm0 → r ≠ .xmm2 → g r = f r) → WP isa (.block is) { s with xmm := g } Q) :
    WP isa (.block (wmont .xmm0 .xmm5 .xmm2 ++ is)) { s with xmm := f } Q := by
  refine wp_xs rfl (wp_ml hm (wp_ml hm (wp_mh hm (wp_mh hm (wp_xs rfl (k _ ?_ ?_))))))
  · simp only [montV]
    rw [← hc.q, ← hc.qi]
    rfl
  · intro r h0 h2
    simp only [h0, h2, ite_false]

/-- `wcadd` on `xmm0`, `xmm1` or `xmm3`. -/
theorem wcadd_wp {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} {d : XReg}
    (hd : d = .xmm0 ∨ d = .xmm1 ∨ d = .xmm3) (hc : VK f)
    (k : ∀ g : XReg → BitVec 128, g d = caddV (f d) → (∀ r, r ≠ d → r ≠ .xmm2 → g r = f r) →
      WP isa (.block is) { s with xmm := g } Q) :
    WP isa (.block (wcadd d .xmm2 ++ is)) { s with xmm := f } Q := by
  rcases hd with rfl | rfl | rfl
  all_goals
    refine wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_xs rfl (k _ ?_ ?_))))
    · simp only [caddV]
      rw [← hc.q]
      rfl
    · intro r h0 h2
      simp only [h0, h2, ite_false]

/-- `wcsub` on `xmm3`. -/
theorem wcsub_wp {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} (hc : VK f)
    (k : ∀ g : XReg → BitVec 128, g .xmm3 = csubV (f .xmm3) → (∀ r, r ≠ .xmm3 → r ≠ .xmm2 → g r = f r) →
      WP isa (.block is) { s with xmm := g } Q) :
    WP isa (.block (wcsub .xmm3 .xmm2 ++ is)) { s with xmm := f } Q := by
  refine wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_xs rfl (k _ ?_ ?_)))))
  · simp only [csubV, caddV]
    rw [← hc.q]
    rfl
  · intro r h0 h2
    simp only [h0, h2, ite_false]

/-! ## Eight butterflies -/

/-- The code of eight butterflies on the `a`s in `xmm1` and the `b`s in
`xmm0`, with the zetas in `xmm5`: it leaves `FS` of them in `xmm3` and `FD`
in `rd`, and keeps the registers from `xmm4` on. -/
def CoreOk (core : List Instr) (rd : XReg) (FS FD : BitVec 128 → BitVec 128 → BitVec 128 → BitVec 128) : Prop :=
  ∀ (s : State) (f : XReg → BitVec 128) (is : List Instr) (Q : State → Prop), 0 < s.mcdt → VK f →
    (∀ g : XReg → BitVec 128, g .xmm3 = FS (f .xmm1) (f .xmm0) (f .xmm5) →
      g rd = FD (f .xmm1) (f .xmm0) (f .xmm5) →
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm3 → g r = f r) →
      WP isa (.block is) { s with xmm := g } Q) →
    WP isa (.block (core ++ is)) { s with xmm := f } Q

theorem fCore_ok : CoreOk fCore .xmm1 fwdS fwdD := by
  intro s f is Q hm hc k
  rw [show fCore ++ is = wmont .xmm0 .xmm5 .xmm2 ++ (wcadd .xmm0 .xmm2 ++ (wmov .xmm3 .xmm1 ::
      wb .paddw .xmm3 .xmm0 :: (wcsub .xmm3 .xmm2 ++ (wb .psubw .xmm1 .xmm0 :: (wcadd .xmm1 .xmm2 ++ is))))) by
    simp only [fCore, List.append_assoc, List.cons_append, List.nil_append]]
  refine wmont_wp hm hc fun g₁ v₁ r₁ => ?_
  have c₁ : VK g₁ := hc.of_eq (r₁ _ (by decide) (by decide)) (r₁ _ (by decide) (by decide))
  refine wcadd_wp (.inl rfl) c₁ fun g₂ v₂ r₂ => wp_xs rfl (wp_xs rfl ?_)
  have c₂ : VK g₂ := c₁.of_eq (r₂ _ (by decide) (by decide)) (r₂ _ (by decide) (by decide))
  refine wcsub_wp (c₂.of_eq rfl rfl) fun g₃ v₃ r₃ => wp_xs rfl ?_
  have c₃ : VK g₃ := c₂.of_eq (r₃ _ (by decide) (by decide)) (r₃ _ (by decide) (by decide))
  refine wcadd_wp (.inr (.inl rfl)) (c₃.of_eq rfl rfl) fun g₄ v₄ r₄ => k g₄ ?_ ?_ ?_
  · rw [r₄ _ (by decide) (by decide)]
    show g₃ .xmm3 = _
    rw [v₃]
    show csubV (XBinOp.eval .paddw (g₂ .xmm1) (g₂ .xmm0)) = _
    rw [v₂, r₂ _ (by decide) (by decide), v₁, r₁ _ (by decide) (by decide)]
    rfl
  · rw [v₄]
    show caddV (XBinOp.eval .psubw (g₃ .xmm1) (g₃ .xmm0)) = _
    rw [r₃ _ (by decide) (by decide), r₃ _ (by decide) (by decide)]
    show caddV (XBinOp.eval .psubw (g₂ .xmm1) (g₂ .xmm0)) = _
    rw [v₂, r₂ _ (by decide) (by decide), v₁, r₁ _ (by decide) (by decide)]
    rfl
  · intro r h0 h1 h2 h3
    rw [r₄ r h1 h2]
    show (if r = XReg.xmm1 then _ else g₃ r) = _
    rw [ite_eq_right h1, r₃ r h3 h2]
    show (if r = XReg.xmm3 then _ else if r = XReg.xmm3 then _ else g₂ r) = _
    rw [ite_eq_right h3, ite_eq_right h3, r₂ r h0 h2, r₁ r h0 h2]

theorem iCore_ok : CoreOk iCore .xmm0 invS invD := by
  intro s f is Q hm hc k
  rw [show iCore ++ is = wmov .xmm3 .xmm1 :: wb .paddw .xmm3 .xmm0 :: (wcsub .xmm3 .xmm2 ++
      (wb .psubw .xmm0 .xmm1 :: (wmont .xmm0 .xmm5 .xmm2 ++ (wcadd .xmm0 .xmm2 ++ is)))) by
    simp only [iCore, List.append_assoc, List.cons_append, List.nil_append]]
  refine wp_xs rfl (wp_xs rfl (wcsub_wp (hc.of_eq rfl rfl) fun g₁ v₁ r₁ => wp_xs rfl ?_))
  have c₁ : VK g₁ := hc.of_eq (r₁ _ (by decide) (by decide)) (r₁ _ (by decide) (by decide))
  refine wmont_wp hm (c₁.of_eq rfl rfl) fun g₂ v₂ r₂ => ?_
  have c₂ : VK g₂ := c₁.of_eq (r₂ _ (by decide) (by decide)) (r₂ _ (by decide) (by decide))
  refine wcadd_wp (.inl rfl) c₂ fun g₃ v₃ r₃ => k g₃ ?_ ?_ ?_
  · rw [r₃ _ (by decide) (by decide), r₂ _ (by decide) (by decide)]
    show g₁ .xmm3 = _
    rw [v₁]
    rfl
  · rw [v₃, v₂]
    show caddV (montV (XBinOp.eval .psubw (g₁ .xmm0) (g₁ .xmm1)) (g₁ .xmm5)) = _
    rw [r₁ _ (by decide) (by decide), r₁ _ (by decide) (by decide), r₁ _ (by decide) (by decide)]
    rfl
  · intro r h0 h1 h2 h3
    rw [r₃ r h0 h2, r₂ r h0 h2]
    show (if r = XReg.xmm0 then _ else g₁ r) = _
    rw [ite_eq_right h0, r₁ r h3 h2]
    show (if r = XReg.xmm3 then _ else if r = XReg.xmm3 then _ else f r) = _
    rw [ite_eq_right h3, ite_eq_right h3]

/-- The code of eight butterflies: from the vectors at `[eax]` and
`[eax + d]` and the zetas in `xmm5`, it stores `FX` and `FY` of them there,
and keeps the constants (and the zetas, if `keep`). -/
def BodyOk (body : List Instr) (d : Nat) (keep : Bool)
    (FX FY : BitVec 128 → BitVec 128 → BitVec 128 → BitVec 128) : Prop :=
  ∀ (s : State) (f : XReg → BitVec 128) (is : List Instr) (Q : State → Prop) (P P' : Addr), 0 < s.mcdt → VK f →
    s.ea (at_ .eax 0) = P → s.ea (at_ .eax d) = P' → InRegions s.wr P 16 → InRegions s.wr P' 16 →
    (∀ (g : XReg → BitVec 128) (vx vy : BitVec 128),
      vx = FX (s.mem.readW P 128) (s.mem.readW P' 128) (f .xmm5) →
      vy = FY (s.mem.readW P 128) (s.mem.readW P' 128) (f .xmm5) → VK g → (keep = true → g .xmm5 = f .xmm5) →
      WP isa (.block is) { ({ s with mem := (s.mem.writeW P vx).writeW P' vy } : State) with xmm := g } Q) →
    WP isa (.block (body ++ is)) { s with xmm := f } Q

theorem lBody_ok {core : List Instr} {rd : XReg} {FS FD : BitVec 128 → BitVec 128 → BitVec 128 → BitVec 128}
    (hc : CoreOk core rd FS FD) (d : Nat) :
    BodyOk (lBody core rd d) d true (bodyX sh8 FS FD) (bodyY sh8 FS FD) := by
  intro s f is Q P P' hm hk ha ha' hin hin' k
  rw [show lBody core rd d ++ is = .movdquLoad .xmm0 (at_ .eax d) :: .movdquLoad .xmm1 (at_ .eax 0) :: (core ++
      (.movdquStore (at_ .eax 0) .xmm3 :: .movdquStore (at_ .eax d) rd :: is)) by
    simp only [lBody, List.append_assoc, List.cons_append, List.nil_append]]
  refine wp_ld ha' (inRdN hin') (wp_ld ha (inRdN hin) (hc s _ _ _ hm (hk.of_eq rfl rfl) fun g vs vd gr =>
    wp_st ha hin (wp_st ha' hin' (k g _ _ ?_ ?_ ?_ ?_))))
  · rw [vs]; rfl
  · rw [vd]; rfl
  · exact hk.of_eq (gr _ (by decide) (by decide) (by decide) (by decide))
      (gr _ (by decide) (by decide) (by decide) (by decide))
  · intro _
    exact gr _ (by decide) (by decide) (by decide) (by decide)

theorem body4_ok {core : List Instr} {rd : XReg} (hrd : rd = .xmm0 ∨ rd = .xmm1)
    {FS FD : BitVec 128 → BitVec 128 → BitVec 128 → BitVec 128} (hc : CoreOk core rd FS FD) :
    BodyOk (body4 core rd) 16 false (bodyX sh4 FS FD) (bodyY sh4 FS FD) := by
  intro s f is Q P P' hm hk ha ha' hin hin' k
  rw [show body4 core rd ++ is = .movdquLoad .xmm0 (at_ .eax 0) :: .movdquLoad .xmm2 (at_ .eax 16) ::
      wmov .xmm1 .xmm0 :: wb .punpckhqdq .xmm0 .xmm2 :: wb .punpcklqdq .xmm1 .xmm2 :: (core ++
        (wmov .xmm2 .xmm3 :: wb .punpcklqdq .xmm2 rd :: wb .punpckhqdq .xmm3 rd ::
          .movdquStore (at_ .eax 0) .xmm2 :: .movdquStore (at_ .eax 16) .xmm3 :: is)) by
    simp only [body4, gath4, scat4, List.append_assoc, List.cons_append, List.nil_append]]
  refine wp_ld ha (inRdN hin) (wp_ld ha' (inRdN hin') (wp_xs rfl (wp_xs rfl (wp_xs rfl
    (hc s _ _ _ hm (hk.of_eq rfl rfl) fun g vs vd gr => ?_)))))
  rcases hrd with rfl | rfl
  all_goals
    refine wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_st ha hin (wp_st ha' hin' (k _ _ _ ?_ ?_ ?_ ?_)))))
    · show XBinOp.eval .punpcklqdq (g .xmm3) (g _) = _
      rw [vs, vd]; rfl
    · show XBinOp.eval .punpckhqdq (g .xmm3) (g _) = _
      rw [vs, vd]; rfl
    · exact hk.of_eq (gr _ (by decide) (by decide) (by decide) (by decide))
        (gr _ (by decide) (by decide) (by decide) (by decide))
    · intro e; exact absurd e (by decide)

theorem body2_ok {core : List Instr} {rd : XReg} (hrd : rd = .xmm0 ∨ rd = .xmm1)
    {FS FD : BitVec 128 → BitVec 128 → BitVec 128 → BitVec 128} (hc : CoreOk core rd FS FD) :
    BodyOk (body2 core rd) 16 false (bodyX sh2 FS FD) (bodyY sh2 FS FD) := by
  intro s f is Q P P' hm hk ha ha' hin hin' k
  rw [show body2 core rd ++ is = .movdquLoad .xmm0 (at_ .eax 0) :: .movdquLoad .xmm2 (at_ .eax 16) ::
      .xop (.pshufd .xmm0 .xmm0 0xD8) :: .xop (.pshufd .xmm2 .xmm2 0xD8) :: wmov .xmm1 .xmm0 ::
      wb .punpckhqdq .xmm0 .xmm2 :: wb .punpcklqdq .xmm1 .xmm2 :: (core ++
        (wmov .xmm2 .xmm3 :: wb .punpckldq .xmm2 rd :: wb .punpckhdq .xmm3 rd ::
          .movdquStore (at_ .eax 0) .xmm2 :: .movdquStore (at_ .eax 16) .xmm3 :: is)) by
    simp only [body2, gath2, scat2, List.append_assoc, List.cons_append, List.nil_append]]
  refine wp_ld ha (inRdN hin) (wp_ld ha' (inRdN hin') (wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_xs rfl
    (hc s _ _ _ hm (hk.of_eq rfl rfl) fun g vs vd gr => ?_)))))))
  rcases hrd with rfl | rfl
  all_goals
    refine wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_st ha hin (wp_st ha' hin' (k _ _ _ ?_ ?_ ?_ ?_)))))
    · show XBinOp.eval .punpckldq (g .xmm3) (g _) = _
      rw [vs, vd]; rfl
    · show XBinOp.eval .punpckhdq (g .xmm3) (g _) = _
      rw [vs, vd]; rfl
    · exact hk.of_eq (gr _ (by decide) (by decide) (by decide) (by decide))
        (gr _ (by decide) (by decide) (by decide) (by decide))
    · intro e; exact absurd e (by decide)


/-! ## The function's memory -/

/-- `[r + d]` for a pointer `r` at `x + k`, where nothing wraps around. -/
theorem ea_at {s : State} {r : Reg} {d : Nat} {x : BitVec 32} {k : Nat} (h : s.gpr r = x + BitVec.ofNat 32 k)
    (hb : x.toNat + k + d < 2 ^ 32) : s.ea (at_ r d) = x.setWidth 64 + BitVec.ofNat 64 (k + d) := by
  show (s.gpr r + BitVec.ofNat 32 d).setWidth 64 = _
  rw [h, ea_add hb]

/-- Word `i` at `p`. -/
abbrev wAt (m : Mem) (p : Addr) (i : Nat) : BitVec 16 := m.readW (p + BitVec.ofNat 64 (2 * i)) 16

theorem word_rd16 (m : Mem) (p : Addr) (u : Nat) {j : Nat} (hj : j < 8) :
    word (m.readW (p + BitVec.ofNat 64 (16 * u)) 128) j = wAt m p (8 * u + j) := by
  rw [word_readW _ _ hj, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact congrArg (fun k => m.readW (p + BitVec.ofNat 64 k) 16) (by omega_using [])

/-- The words at `p` after a 16-byte store at `p + 16u`. -/
theorem wAt_write16 (m : Mem) (p : Addr) (v : BitVec 128) {u i : Nat} (hu : u < 64) (hi : i < 512) :
    wAt (m.writeW (p + BitVec.ofNat 64 (16 * u)) v) p i =
      if 8 * u ≤ i ∧ i < 8 * u + 8 then word v (i - 8 * u) else wAt m p i := by
  by_cases h : 8 * u ≤ i ∧ i < 8 * u + 8
  · rw [ite_eq_left h]
    have := readW_writeW128_16 m (p + BitVec.ofNat 64 (16 * u)) v (j := i - 8 * u) (by omega_using [h])
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 16 * u + 2 * (i - 8 * u) = 2 * i by omega_using [h]] at this
    exact this
  · rw [ite_eq_right h]
    exact Mem.readW_writeW_sep (Offset.sep p (by omega_using [h]) (by omega_using [hi]) (by omega_using [hu]))
      (by decide)

section
variable (s₀ : State)
/-- The state the body starts in: after the MCDT frame's push and the allocation. -/
abbrev N0 : State := allocFrame 4 (M0 s₀)
end

theorem sp12 {s₀ : State} (hp : Pre s₀) : 12 ≤ (E0 s₀).toNat := by have := hp.sp; omega_using [this]

theorem N0_esp {s₀ : State} (hp : Pre s₀) : (N0 s₀).gpr .esp = E0 s₀ - 16 := by
  rw [allocFrame_esp, M0_esp]
  have := hp.sp
  bv_omega

theorem N0_wr (s₀ : State) :
    (N0 s₀).wr = ⟨((M0 s₀).gpr .esp - BitVec.ofNat 32 4).setWidth 64, 4⟩ :: ⟨(E0 s₀ - 12).setWidth 64, 9⟩ :: s₀.wr :=
  rfl

/-- A region apart from the contract's stack is apart from the MCDT frame. -/
theorem mcdt_disj {s₀ : State} (hp : Pre s₀) {R : Region} (h : (stkR s₀).Disjoint R) :
    (mcdtR s₀).Disjoint R := by
  intro a h₁ h₂
  refine h a ?_ h₂
  have := hp.sp
  have := (E0 s₀).isLt
  simp only [Region.Contains] at h₁ ⊢
  bv_omega

/-- The arguments, at `[esp + 20 + 4i]` in the body. -/
theorem arg_N0 {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 2) :
    ((N0 s₀).gpr .esp + BitVec.ofNat 32 (20 + 4 * i)).setWidth 64 = argAddr s₀ i ∧
      (N0 s₀).mem.readW (argAddr s₀ i) 32 = arg s₀ i := by
  refine ⟨?_, ?_⟩
  · rw [N0_esp hp]; simp only [argAddr, E0]; congr 1; have := hp.sp; bv_omega
  · exact (M0_frame s₀ (sp12 hp)).readW (hp.arg_in hi) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (mcdt_disj hp hp.stk_a).symm) (by decide)

theorem in_s {s₀ : State} (hp : Pre s₀) {s : State} (hw : s.wr = (N0 s₀).wr) {o n : Nat} (h : o + n ≤ 1024) :
    InRegions s.wr (sA s₀ + BitVec.ofNat 64 o) n := by
  rw [hw, N0_wr, hp.wr]
  exact ⟨polyRegion (sA s₀), by simp, Offset.contains_base _ h (by omega_using [h])⟩

theorem in_f {s₀ : State} (hp : Pre s₀) {s : State} (hw : s.wr = (N0 s₀).wr) {o n : Nat} (h : o + n ≤ 1024) :
    InRegions s.wr (fA s₀ + BitVec.ofNat 64 o) n := by
  rw [hw, N0_wr, hp.wr]
  exact ⟨polyRegion (fA s₀), by simp, Offset.contains_base _ h (by omega_using [h])⟩

theorem in_arg {s₀ : State} (hp : Pre s₀) {s : State} (hw : s.wr = (N0 s₀).wr) {i : Nat} (hi : i < 2) :
    InRegions s.wr (argAddr s₀ i) 4 := by
  rw [hw, N0_wr, hp.wr]
  exact ⟨aR s₀, by simp, hp.arg_in hi⟩

/-- What every piece keeps: the stack pointer, the permissions, the MCDT
depth, the callee-saved registers, the table `T` in the first words of
`scratch`, `f` and `scratch + 1024` in the argument slots, and the
constants `VP`. -/
structure Base (s₀ : State) (T : List Nat) (VP : (XReg → BitVec 128) → Prop) (s : State) : Prop where
  esp : s.gpr .esp = (N0 s₀).gpr .esp
  rd : s.rd = (N0 s₀).rd
  wr : s.wr = (N0 s₀).wr
  mcdt : s.mcdt = s₀.mcdt + 1
  saved : ∀ r ∈ [Reg.ebx, .esi, .edi, .ebp], s.gpr r = s₀.gpr r
  frame : Frame [polyRegion (fA s₀), polyRegion (sA s₀), aR s₀] (M0 s₀).mem s.mem
  tbl : ∀ k < 128, wAt s.mem (sA s₀) k = BitVec.ofNat 16 (T.getD k 0)
  arg0 : s.mem.readW (argAddr s₀ 0) 32 = fP s₀
  slot : s.mem.readW (argAddr s₀ 1) 32 = sP s₀ + 1024
  vp : VP s.xmm

/-- Writes to `scratch` that keep the table, and to XMM registers, keep the rest. -/
theorem Base.stepS {s₀ : State} (hp : Pre s₀) {T : List Nat} {VP VP' : (XReg → BitVec 128) → Prop}
    {s : State} (h : Base s₀ T VP s) {m' : Mem} (hf : Frame [polyRegion (sA s₀)] s.mem m')
    (ht : ∀ k < 128, wAt m' (sA s₀) k = wAt s.mem (sA s₀) k)
    {g : XReg → BitVec 128} (hg : VP' g) : Base s₀ T VP' { ({ s with mem := m' } : State) with xmm := g } where
  esp := h.esp
  rd := h.rd
  wr := h.wr
  mcdt := h.mcdt
  saved := h.saved
  frame := h.frame.trans (hf.mono fun r hr => by simp at hr ⊢; exact .inr (.inl hr))
  tbl k hk := (ht k hk).trans (h.tbl k hk)
  arg0 := by
    show m'.readW _ 32 = _
    rw [hf.readW (hp.arg_in (by decide)) (by simpa using hp.s_a.symm) (by decide)]; exact h.arg0
  slot := by
    show m'.readW _ 32 = _
    rw [hf.readW (hp.arg_in (by decide)) (by simpa using hp.s_a.symm) (by decide)]; exact h.slot
  vp := hg

/-- Writes to `f` and to XMM registers keep the rest. -/
theorem Base.stepF {s₀ : State} (hp : Pre s₀) {T : List Nat} {VP VP' : (XReg → BitVec 128) → Prop}
    {s : State} (h : Base s₀ T VP s) {m' : Mem} (hf : Frame [polyRegion (fA s₀)] s.mem m')
    {g : XReg → BitVec 128} (hg : VP' g) : Base s₀ T VP' { ({ s with mem := m' } : State) with xmm := g } where
  esp := h.esp
  rd := h.rd
  wr := h.wr
  mcdt := h.mcdt
  saved := h.saved
  frame := h.frame.trans (hf.mono fun r hr => by simp at hr ⊢; exact .inl hr)
  tbl k hk := by
    show m'.readW _ 16 = _
    rw [hf.readW (r := polyRegion (sA s₀)) (Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk]))
      (by simpa using hp.f_s.symm) (by decide)]
    exact h.tbl k hk
  arg0 := by
    show m'.readW _ 32 = _
    rw [hf.readW (hp.arg_in (by decide)) (by simpa using hp.f_a.symm) (by decide)]; exact h.arg0
  slot := by
    show m'.readW _ 32 = _
    rw [hf.readW (hp.arg_in (by decide)) (by simpa using hp.f_a.symm) (by decide)]; exact h.slot
  vp := hg

/-- `eax`, `ecx`, `edx` and the flags are free, and so are the XMM registers that hold no constant. -/
theorem Base.of_gpr {s₀ : State} {T : List Nat} {VP VP' : (XReg → BitVec 128) → Prop} {s s' : State}
    (h : Base s₀ T VP s) (hg : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hmc : s'.mcdt = s.mcdt) (hmem : s'.mem = s.mem) (hx : VP' s'.xmm) :
    Base s₀ T VP' s' where
  esp := (hg _ (by decide) (by decide) (by decide)).trans h.esp
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  mcdt := hmc.trans h.mcdt
  saved r hr := by
    have := h.saved r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact (hg _ (by decide) (by decide) (by decide)).trans this
  frame := hmem ▸ h.frame
  tbl := hmem ▸ h.tbl
  arg0 := hmem ▸ h.arg0
  slot := hmem ▸ h.slot
  vp := hx

/-- The words in memory, from word 256 of `scratch`: those of `D` are the
coefficients of `G`, and the others those of `f`. -/
def Co (s₀ : State) (m : Mem) (f G : Poly) (D : Nat → Prop) : Prop :=
  ∀ i < 256, (D i → (wAt m (sA s₀) (256 + i)).toNat = (G[i]!).val) ∧
    (¬ D i → (wAt m (sA s₀) (256 + i)).toNat = (f[i]!).val)

theorem Co.congr {s₀ : State} {m : Mem} {f G : Poly} {D D' : Nat → Prop}
    (h : Co s₀ m f G D) (e : ∀ i < 256, (D' i ↔ D i)) : Co s₀ m f G D' :=
  fun i hi => ⟨fun hd => (h i hi).1 ((e i hi).mp hd), fun hn => (h i hi).2 fun hd => hn ((e i hi).mpr hd)⟩

/-- The coefficient at position `p` of the vectors of coefficients `8u` and `8u'`. -/
def idx (u u' p : Nat) : Nat := if p < 8 then 8 * u + p else 8 * u' + (p - 8)

/-- The coefficients of those two vectors. -/
def In16 (u u' i : Nat) : Prop := (8 * u ≤ i ∧ i < 8 * u + 8) ∨ (8 * u' ≤ i ∧ i < 8 * u' + 8)

/-- Eight butterflies on the vectors of coefficients `8u` and `8u'`, none of
which is done: they are, afterwards. -/
theorem body_step {body : List Instr} {d : Nat} {keep : Bool}
    {FX FY : BitVec 128 → BitVec 128 → BitVec 128 → BitVec 128} (hb : BodyOk body d keep FX FY)
    {s₀ : State} (hp : Pre s₀) {T : List Nat} {s : State} (h : Base s₀ T VK s) {u u' : Nat}
    (hu : u < 32) (hu' : u' < 32) (hd : 16 * u + d = 16 * u')
    (heax : s.gpr .eax = sP s₀ + BitVec.ofNat 32 (16 * (32 + u))) {f G : Poly} {D : Nat → Prop}
    (hco : Co s₀ s.mem f G D) (hD : ∀ i, In16 u u' i → ¬ D i)
    (hnew : ∀ X Y, (∀ p < 16, (pos X Y p).toNat = (f[idx u u' p]!).val) →
      ∀ p < 16, (pos (FX X Y (s.xmm .xmm5)) (FY X Y (s.xmm .xmm5)) p).toNat = (G[idx u u' p]!).val)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ (m : Mem) (g : XReg → BitVec 128),
      Base s₀ T VK { ({ s with mem := m } : State) with xmm := g } →
      Co s₀ m f G (fun i => D i ∨ In16 u u' i) → (keep = true → g .xmm5 = s.xmm .xmm5) →
      WP isa (.block is) { ({ s with mem := m } : State) with xmm := g } Q) :
    WP isa (.block (body ++ is)) s Q := by
  have fs := hp.s_fit
  have eP : s.ea (at_ .eax 0) = sA s₀ + BitVec.ofNat 64 (16 * (32 + u)) := by
    rw [ea_at heax (by omega_using [fs, hu]), Nat.add_zero]
  have eP' : s.ea (at_ .eax d) = sA s₀ + BitVec.ofNat 64 (16 * (32 + u')) := by
    rw [ea_at heax (by omega_using [fs, hu', hd])]
    exact congrArg (fun k => sA s₀ + BitVec.ofNat 64 k) (by omega_using [hd])
  have hm : 0 < s.mcdt := by rw [h.mcdt]; exact Nat.succ_pos _
  have hcon : (polyRegion (sA s₀)).Contains (sA s₀ + BitVec.ofNat 64 (16 * (32 + u))) (128 / 8) :=
    Offset.contains_base _ (by omega_using [hu]) (by omega_using [hu])
  have hcon' : (polyRegion (sA s₀)).Contains (sA s₀ + BitVec.ofNat 64 (16 * (32 + u'))) (128 / 8) :=
    Offset.contains_base _ (by omega_using [hu']) (by omega_using [hu'])
  show WP isa (.block (body ++ is)) { s with xmm := s.xmm } Q
  refine hb s s.xmm is Q _ _ hm h.vp eP eP' (in_s hp h.wr (by omega_using [hu])) (in_s hp h.wr (by omega_using [hu']))
    fun g vx vy ex ey hg hk5 => ?_
  have hV : ∀ p < 16, (pos (s.mem.readW (sA s₀ + BitVec.ofNat 64 (16 * (32 + u))) 128)
      (s.mem.readW (sA s₀ + BitVec.ofNat 64 (16 * (32 + u'))) 128) p).toNat = (f[idx u u' p]!).val := fun p hp16 => by
    by_cases h8 : p < 8
    · rw [pos, ite_eq_left h8, idx, ite_eq_left h8, word_rd16 _ _ _ h8,
        show 8 * (32 + u) + p = 256 + (8 * u + p) by omega_using []]
      exact (hco _ (by omega_using [hu, h8])).2 (hD _ (.inl ⟨by omega_using [], by omega_using [h8]⟩))
    · rw [pos, ite_eq_right h8, idx, ite_eq_right h8, word_rd16 _ _ _ (by omega_using [h8, hp16]),
        show 8 * (32 + u') + (p - 8) = 256 + (8 * u' + (p - 8)) by omega_using []]
      exact (hco _ (by omega_using [hu', hp16])).2 (hD _ (.inr ⟨by omega_using [], by omega_using [h8, hp16]⟩))
  have hN := hnew _ _ hV
  refine k _ g (h.stepS hp (((Frame.refl _ _).writeW (List.mem_singleton_self _) vx hcon).writeW
    (List.mem_singleton_self _) vy hcon') (fun j hj => ?_) hg) (fun i hi => ?_) hk5
  · rw [wAt_write16 _ _ _ (by omega_using [hu']) (by omega_using [hj]), ite_eq_right (by omega_using [hj]),
      wAt_write16 _ _ _ (by omega_using [hu]) (by omega_using [hj]), ite_eq_right (by omega_using [hj])]
  rw [wAt_write16 _ _ _ (by omega_using [hu']) (by omega_using [hi]),
    wAt_write16 _ _ _ (by omega_using [hu]) (by omega_using [hi])]
  by_cases h2 : 8 * u' ≤ i ∧ i < 8 * u' + 8
  · rw [ite_eq_left (by omega_using [h2])]
    have := hN (8 + (i - 8 * u')) (by omega_using [h2])
    rw [pos, ite_eq_right (by omega_using []), ← ey, idx, ite_eq_right (by omega_using []),
      show 8 + (i - 8 * u') - 8 = i - 8 * u' by omega_using [],
      show 8 * u' + (i - 8 * u') = i by omega_using [h2]] at this
    rw [show 256 + i - 8 * (32 + u') = i - 8 * u' by omega_using [h2]]
    exact ⟨fun _ => this, fun hn => absurd (.inr (.inr h2)) hn⟩
  · rw [ite_eq_right (by omega_using [h2])]
    by_cases h1 : 8 * u ≤ i ∧ i < 8 * u + 8
    · rw [ite_eq_left (by omega_using [h1])]
      have := hN (i - 8 * u) (by omega_using [h1])
      rw [pos, ite_eq_left (by omega_using [h1]), ← ex, idx, ite_eq_left (by omega_using [h1]),
        show 8 * u + (i - 8 * u) = i by omega_using [h1]] at this
      rw [show 256 + i - 8 * (32 + u) = i - 8 * u by omega_using [h1]]
      exact ⟨fun _ => this, fun hn => absurd (.inr (.inl h1)) hn⟩
    · rw [ite_eq_right (by omega_using [h1])]
      refine ⟨fun hd' => (hco i hi).1 (hd'.resolve_right fun h8 => ?_), fun hn => (hco i hi).2 fun hdi => hn (.inl hdi)⟩
      rcases h8 with h8 | h8
      · exact h1 h8
      · exact h2 h8


/-! ## The zetas -/

/-- The table `T` holds the zetas `zv k` in Montgomery form. -/
def TabOK (T : List Nat) (zv : Nat → Zq) : Prop := ∀ k < 128, T.getD k 0 = (zv k).val * 65536 % 3329

theorem tab_lt {T : List Nat} {zv : Nat → Zq} (hT : TabOK T zv) {k : Nat} (hk : k < 128) : T.getD k 0 < 3329 := by
  rw [hT k hk]; exact Nat.mod_lt _ (by decide)

/-- The words of a quadword loaded by `movq`. -/
theorem word_movq (x : BitVec 64) {i : Nat} (hi : i < 4) :
    word ((0 : BitVec 64) ++ x) i = x.extractLsb' (16 * i) 16 := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [getLsbD_word _ _ _ hk, BitVec.getLsbD_append]
  simp only [BitVec.getLsbD_extractLsb', show 16 * i + k < 64 by omega_using [hi, hk], decide_true, hk, Bool.true_and,
    ↓reduceIte]

theorem ext_readW64 (m : Mem) (a : Addr) {j : Nat} (hj : j < 4) :
    (m.readW a 64).extractLsb' (16 * j) 16 = m.readW (a + BitVec.ofNat 64 (2 * j)) 16 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', Mem.readW, BitVec.getLsbD_setWidth]
  simp only [hi, decide_true, Bool.true_and]
  rw [getLsbD_read _ _ (by omega_using [hj, hi]), getLsbD_read _ _ (by omega_using [hi])]
  rw [show a + BitVec.ofNat 64 ((16 * j + i) / 8) = a + BitVec.ofNat 64 (2 * j) + BitVec.ofNat 64 (i / 8) by
    rw [show (16 * j + i) / 8 = 2 * j + i / 8 by omega_using [], BitVec.ofNat_add, BitVec.add_assoc]]
  simp only [decide_eq_true (show 16 * j + i < 64 by omega_using [hj, hi]), Bool.true_and]
  exact congrArg _ (by omega_using [])

/-- The words `movq` loads at word `j` of `p`. -/
theorem word_movq_rd (m : Mem) (p : Addr) (j : Nat) {i : Nat} (hi : i < 4) :
    word ((0 : BitVec 64) ++ m.readW (p + BitVec.ofNat 64 (2 * j)) 64) i = wAt m p (j + i) := by
  rw [word_movq _ hi, ext_readW64 _ _ hi, BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.mul_add]

theorem word_dup (a : BitVec 128) {i : Nat} (hi : i < 8) : word (XBinOp.eval .punpcklwd a a) i = word a (i / 2) := by
  rw [word_punpcklwd _ _ hi, ite_self]

theorem word_shufDwords (a : BitVec 128) (o : BitVec 8) {k e : Nat} (hk : k < 4) (he : e < 2) :
    word (shufDwords a o) (2 * k + e) = word a (2 * (o.extractLsb' (2 * k) 2).toNat + e) := by
  rw [word_dword _ _ _ he, dword_shufDwords _ _ hk, word_dword _ _ _ he]

/-- What `zl8` leaves in `xmm5`, from the quadword at `a`. -/
def zsel8 (m : Mem) (a : Addr) : BitVec 128 :=
  shufDwords (XBinOp.eval .punpcklwd ((0 : BitVec 64) ++ m.readW a 64) ((0 : BitVec 64) ++ m.readW a 64)) 0

/-- What `zl4` leaves in `xmm5`. -/
def zsel4 (m : Mem) (a : Addr) : BitVec 128 :=
  shufDwords (XBinOp.eval .punpcklwd ((0 : BitVec 64) ++ m.readW a 64) ((0 : BitVec 64) ++ m.readW a 64)) 0x50

/-- What `zl2` leaves in `xmm5`. -/
def zsel2 (m : Mem) (a : Addr) : BitVec 128 :=
  XBinOp.eval .punpcklwd ((0 : BitVec 64) ++ m.readW a 64) ((0 : BitVec 64) ++ m.readW a 64)

theorem word_zsel8 (m : Mem) (p : Addr) (j : Nat) {i : Nat} (hi : i < 8) :
    word (zsel8 m (p + BitVec.ofNat 64 (2 * j))) i = wAt m p j := by
  have key : ∀ k < 4, ∀ e < 2, word (zsel8 m (p + BitVec.ofNat 64 (2 * j))) (2 * k + e) = wAt m p j :=
    fun k hk e he => by
      rw [zsel8, word_shufDwords _ _ hk he,
        show ((0 : BitVec 8).extractLsb' (2 * k) 2).toNat = 0 by
          rcases cases4 hk with rfl | rfl | rfl | rfl <;> rfl,
        word_dup _ (by omega_using [he]), word_movq_rd _ _ _ (by omega_using [he]),
        show j + (2 * 0 + e) / 2 = j by omega_using [he]]
  have := key (i / 2) (by omega_using [hi]) (i % 2) (by omega_using [])
  rwa [show 2 * (i / 2) + i % 2 = i by omega_using []] at this

theorem word_zsel4 (m : Mem) (p : Addr) (j : Nat) {i : Nat} (hi : i < 8) :
    word (zsel4 m (p + BitVec.ofNat 64 (2 * j))) i = wAt m p (j + i / 4) := by
  have key : ∀ k < 4, ∀ e < 2, word (zsel4 m (p + BitVec.ofNat 64 (2 * j))) (2 * k + e) = wAt m p (j + k / 2) :=
    fun k hk e he => by
      have sel : ((0x50 : BitVec 8).extractLsb' (2 * k) 2).toNat = k / 2 := by
        rcases cases4 hk with rfl | rfl | rfl | rfl <;> rfl
      rw [zsel4, word_shufDwords _ _ hk he, sel, word_dup _ (by omega_using [he, hk]),
        word_movq_rd _ _ _ (by omega_using [he, hk]), show (2 * (k / 2) + e) / 2 = k / 2 by omega_using [he]]
  have := key (i / 2) (by omega_using [hi]) (i % 2) (by omega_using [])
  rwa [show 2 * (i / 2) + i % 2 = i by omega_using [], show i / 2 / 2 = i / 4 by omega_using []] at this

theorem word_zsel2 (m : Mem) (p : Addr) (j : Nat) {i : Nat} (hi : i < 8) :
    word (zsel2 m (p + BitVec.ofNat 64 (2 * j))) i = wAt m p (j + i / 2) := by
  rw [zsel2, word_dup _ hi, word_movq_rd _ _ _ (by omega_using [hi])]

/-- The code that loads the zetas of a step, eight bytes at `[edx]`, into `xmm5`. -/
def ZlOk (zl : List Instr) (zsel : Mem → Addr → BitVec 128) : Prop :=
  ∀ (s : State) (f : XReg → BitVec 128) (is : List Instr) (Q : State → Prop) (a : Addr), s.ea (at_ .edx 0) = a →
    InRegions (s.rd ++ s.wr) a 8 →
    (∀ g : XReg → BitVec 128, g .xmm5 = zsel s.mem a → (∀ r, r ≠ .xmm5 → g r = f r) →
      WP isa (.block is) { s with xmm := g } Q) →
    WP isa (.block (zl ++ is)) { s with xmm := f } Q

theorem zl8_ok : ZlOk zl8 zsel8 :=
  fun _ _ _ _ _ ha hin k => wp_lq ha hin (wp_xs rfl (wp_xs rfl (k _ rfl fun r h5 => by simp only [h5, ite_false])))

theorem zl4_ok : ZlOk zl4 zsel4 :=
  fun _ _ _ _ _ ha hin k => wp_lq ha hin (wp_xs rfl (wp_xs rfl (k _ rfl fun r h5 => by simp only [h5, ite_false])))

theorem zl2_ok : ZlOk zl2 zsel2 :=
  fun _ _ _ _ _ ha hin k => wp_lq ha hin (wp_xs rfl (k _ rfl fun r h5 => by simp only [h5, ite_false]))

/-! ## The layers of the specification -/

/-- The layer with `len` from `f` to `G`: coefficient `2 · len · c + r` and
the one `len` further become `sS` and `sD` of them, with the zeta of
number `zp + c`. -/
def LayOk (sS sD : Zq → Zq → Zq → Zq) (zv : Nat → Zq) (f G : Poly) (len zp : Nat) : Prop :=
  ∀ c r, r < len → 2 * len * c + r + len < 256 →
    G[2 * len * c + r]! = sS f[2 * len * c + r]! f[2 * len * c + r + len]! (zv (zp + c)) ∧
      G[2 * len * c + r + len]! = sD f[2 * len * c + r]! f[2 * len * c + r + len]! (zv (zp + c))

theorem div_mod_blk {len c r : Nat} (hr : r < 2 * len) :
    (2 * len * c + r) % (2 * len) = r ∧ (2 * len * c + r) / (2 * len) = c := by
  refine ⟨by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr], ?_⟩
  rw [Nat.mul_add_div (by omega_using [hr]), Nat.div_eq_of_lt hr, Nat.add_zero]

theorem fwd_lay (f : Poly) {len : Nat} (hl : 0 < len) (hd : 2 * len * (128 / len) = 256) :
    LayOk (fun x y ζ => x + ζ * y) (fun x y ζ => x - ζ * y) zeta f (nttLayer f len) len (128 / len) := by
  intro c r hr hx
  obtain ⟨m1, d1⟩ := div_mod_blk (len := len) (c := c) (r := r) (by omega_using [hr])
  obtain ⟨m2, d2⟩ := div_mod_blk (len := len) (c := c) (r := r + len) (by omega_using [hr])
  have e3 : 2 * len * c + (r + len) - len = 2 * len * c + r := by omega_using []
  constructor
  · rw [nttLayer_get f hl hd (by omega_using [hx]), m1, ite_eq_left hr, d1]
  · rw [Nat.add_assoc, nttLayer_get f hl hd (by omega_using [hx]), m2, ite_eq_right (by omega_using []), d2, e3]

/-- The zeta of `NTT⁻¹` of number `k` in the order of use. -/
def zvI (k : Nat) : Zq := zeta ((128 - k) % 128)

theorem inv_lay (f : Poly) {len : Nat} (hl : 0 < len) (hd : 2 * len * (128 / len) = 256)
    (hB : 128 / len ≤ 64) (hq : 256 / len = 2 * (128 / len)) :
    LayOk (fun x y _ => x + y) (fun x y ζ => ζ * (y - x)) zvI f (nttInvLayer f len) len (129 - 256 / len) := by
  intro c r hr hx
  obtain ⟨m1, d1⟩ := div_mod_blk (len := len) (c := c) (r := r) (by omega_using [hr])
  obtain ⟨m2, d2⟩ := div_mod_blk (len := len) (c := c) (r := r + len) (by omega_using [hr])
  have e3 : 2 * len * c + (r + len) - len = 2 * len * c + r := by omega_using []
  have hc : c < 128 / len := by
    refine Nat.lt_of_mul_lt_mul_left (a := 2 * len) ?_
    rw [hd]; omega_using [hx]
  have ez : zvI (129 - 256 / len + c) = zeta (256 / len - 1 - c) := by
    rw [zvI, hq]
    exact congrArg zeta (by omega_using [hc, hB])
  rw [ez]
  constructor
  · rw [nttInvLayer_get f hl hd (by omega_using [hx]), m1, ite_eq_left hr]
  · rw [Nat.add_assoc, nttInvLayer_get f hl hd (by omega_using [hx]), m2, ite_eq_right (by omega_using []), d2, e3]

/-! ## The start of a layer -/

/-- Before a layer: the words are the coefficients of `f`, and `edx` is at
the zeta of number `zp`. -/
structure LS (s₀ : State) (T : List Nat) (VP : (XReg → BitVec 128) → Prop) (f : Poly) (zp : Nat)
    (s : State) : Prop where
  base : Base s₀ T VP s
  edx : s.gpr .edx = sP s₀ + BitVec.ofNat 32 (2 * zp)
  co : ∀ i < 256, (wAt s.mem (sA s₀) (256 + i)).toNat = (f[i]!).val

theorem slot_sub (x : BitVec 32) : x + 1024 - 512 = x + BitVec.ofNat 32 (16 * (32 + 0)) := by
  bv_omega

theorem layStart_wp {s₀ : State} (hp : Pre s₀) {T : List Nat} {VP : (XReg → BitVec 128) → Prop} {s : State}
    (h : Base s₀ T VP s) : WP isa (.block layStart) s fun s' =>
      Base s₀ T VP s' ∧ s'.gpr .eax = sP s₀ + BitVec.ofNat 32 (16 * (32 + 0)) ∧ s'.gpr .edx = s.gpr .edx ∧
        s'.mem = s.mem := by
  obtain ⟨a₁, -⟩ := arg_N0 hp (i := 1) (by decide)
  simp only [Nat.mul_one, Nat.reduceAdd] at a₁
  have ea : (s.gpr .esp + BitVec.ofNat 32 24).setWidth 64 = argAddr s₀ 1 := by rw [h.esp]; exact a₁
  have i₁ : InRegions (s.rd ++ s.wr) (argAddr s₀ 1) 4 := inRdN (in_arg hp h.wr (by decide))
  have sl := h.slot
  apply WP.of_runBlock
  simp only [layStart, at_, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.ea, State.load32,
    State.setReg, arithFlags, State.setFlags, Option.map_some, Option.bind_some, ea, i₁, sl, reduceCtorEq, ↓reduceIte,
    Option.some.injEq, exists_eq_left']
  refine ⟨h.of_gpr (fun r h1 _ _ => by simp only [h1, ite_false]) rfl rfl rfl rfl h.vp, slot_sub _, ?_⟩
  trivial

/-! ## A layer with `len ≥ 8` -/

/-- The coefficients done after `t` groups of block `c`, of `gl` groups. -/
def D8 (gl c t i : Nat) : Prop :=
  i < 16 * (gl * c) ∨ (16 * (gl * c) ≤ i ∧ i < 16 * (gl * c) + 8 * t) ∨
    (16 * (gl * c) + 8 * gl ≤ i ∧ i < 16 * (gl * c) + 8 * gl + 8 * t)

/-- Before block `c` of a layer with `len = 8 · gl`. -/
structure LInv (s₀ : State) (T : List Nat) (f G : Poly) (gl zp c : Nat) (s : State) : Prop where
  base : Base s₀ T VK s
  eax : s.gpr .eax = sP s₀ + BitVec.ofNat 32 (16 * (32 + 2 * (gl * c)))
  edx : s.gpr .edx = sP s₀ + BitVec.ofNat 32 (2 * (zp + c))
  co : Co s₀ s.mem f G (fun i => i < 16 * (gl * c))

/-- After `t` groups of eight butterflies of block `c`. -/
structure GInv (s₀ : State) (T : List Nat) (f G : Poly) (gl zp c t : Nat) (s : State) : Prop where
  base : Base s₀ T VK s
  eax : s.gpr .eax = sP s₀ + BitVec.ofNat 32 (16 * (32 + (2 * (gl * c) + t)))
  ecx : s.gpr .ecx = BitVec.ofNat 32 (gl - t)
  edx : s.gpr .edx = sP s₀ + BitVec.ofNat 32 (2 * (zp + c + 1))
  z : ∀ i < 8, word (s.xmm .xmm5) i = BitVec.ofNat 16 (T.getD (zp + c) 0)
  co : Co s₀ s.mem f G (D8 gl c t)

theorem blkInit_wp {s₀ : State} (hp : Pre s₀) {T : List Nat} {f G : Poly} {gl zp c : Nat} (hz : zp + c < 128)
    {s : State} (h : LInv s₀ T f G gl zp c s) :
    WP isa (.block (blkInit (8 * gl))) s (GInv s₀ T f G gl zp c 0) := by
  have fs := hp.s_fit
  have ez : s.ea (at_ .edx 0) = sA s₀ + BitVec.ofNat 64 (2 * (zp + c)) := by
    rw [ea_at h.edx (by omega_using [fs, hz]), Nat.add_zero]
  show WP isa (.block (zl8 ++ _)) { s with xmm := s.xmm } _
  refine zl8_ok s s.xmm _ _ _ ez (inRdN (in_s hp h.base.wr (by omega_using [hz]))) fun g g5 gr => ?_
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.setReg, arithFlags,
    State.setFlags, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨h.base.of_gpr (fun r h1 h2 h3 => by simp only [h2, h3, ite_false]) rfl rfl rfl rfl
    (h.base.vp.of_eq (gr _ (by decide)) (gr _ (by decide))), ?_, ?_, ?_, fun i hi => ?_, h.co.congr fun i hi => ?_⟩
  · show s.gpr .eax = _
    rw [h.eax, Nat.add_zero]
  · show BitVec.ofNat 32 (8 * gl / 8) = _
    rw [Nat.mul_div_cancel_left gl (by decide), Nat.sub_zero]
  · show s.gpr .edx + 2 = _
    rw [h.edx]; exact ptr_next _ _ 2
  · show word (g .xmm5) i = _
    rw [g5, word_zsel8 _ _ _ hi]; exact h.base.tbl _ hz
  · simp only [D8]; omega_using []

theorem blk_ix (gl c : Nat) : 2 * (8 * gl) * c = 16 * (gl * c) := by
  rw [← Nat.mul_assoc 2 8 gl, Nat.mul_assoc]

theorem zlanes_bc {T : List Nat} {zv : Nat → Zq} (hT : TabOK T zv) {k : Nat} (hk : k < 128) {Z : BitVec 128}
    (hZ : ∀ i < 8, word Z i = BitVec.ofNat 16 (T.getD k 0)) : ZLanes Z (fun _ => zv k) := fun i hi => by
  rw [hZ i hi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans (tab_lt hT hk) (by decide)), hT k hk]

theorem gstep {T : List Nat} {zv : Nat → Zq} {sS sD : Zq → Zq → Zq → Zq} {body : Nat → List Instr}
    {FX FY : BitVec 128 → BitVec 128 → BitVec 128 → BitVec 128} (hb : ∀ d, BodyOk (body d) d true FX FY)
    (hN : NewOk sh8 FX FY sS sD) (hT : TabOK T zv) {s₀ : State}
    (hp : Pre s₀) {f G : Poly} {gl zp : Nat} (hG : LayOk sS sD zv f G (8 * gl) zp) {B c t : Nat}
    (hB : gl * B = 16) (hc : c < B) (ht : t < gl) (hz : zp + c < 128) {s : State}
    (h : GInv s₀ T f G gl zp c t s) :
    WP isa (.block (body (2 * (8 * gl)) ++ groupEnd)) s fun s' =>
      GInv s₀ T f G gl zp c (t + 1) s' ∧ eval .ne s' = some (decide (t + 1 < gl)) := by
  have hL : gl * c + gl ≤ 16 := by
    have := Nat.mul_le_mul_left gl (Nat.succ_le_of_lt hc)
    rw [Nat.mul_succ, hB] at this; exact this
  have i1 : ∀ e < 8, idx (2 * (gl * c) + t) (2 * (gl * c) + t + gl) (sh8.pa e) =
      2 * (8 * gl) * c + (8 * t + e) := fun e he => by
    show (if e < 8 then 8 * (2 * (gl * c) + t) + e else _) = _
    rw [ite_eq_left he, blk_ix]; omega_using []
  have i2 : ∀ e < 8, idx (2 * (gl * c) + t) (2 * (gl * c) + t + gl) (sh8.pb e) =
      2 * (8 * gl) * c + (8 * t + e) + 8 * gl := fun e he => by
    show (if e + 8 < 8 then _ else 8 * (2 * (gl * c) + t + gl) + (e + 8 - 8)) = _
    rw [ite_eq_right (by omega_using []), blk_ix]; omega_using []
  refine body_step (hb _) hp h.base (u := 2 * (gl * c) + t) (u' := 2 * (gl * c) + t + gl) (by omega_using [hL, ht])
    (by omega_using [hL, ht]) (by omega_using []) h.eax h.co (fun i h8 hd => ?_)
    (fun X Y hV => hN f G _ _ (fun _ => zv (zp + c)) (zlanes_bc hT hz h.z) (fun e he => ?_) X Y hV)
    fun m g bs co k5 => ?_
  · simp only [In16] at h8
    simp only [D8] at hd
    omega_using [h8, hd, ht]
  · rw [i1 e he, i2 e he]
    exact hG c (8 * t + e) (by omega_using [ht, he]) (by rw [blk_ix]; omega_using [hL, ht, he])
  · apply WP.of_runBlock
    simp only [groupEnd, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.setReg, arithFlags,
      State.setFlags, Option.bind_some, reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left']
    refine ⟨⟨bs.of_gpr (fun r h1 h2 _ => by simp only [h1, h2, ite_false]) rfl rfl rfl rfl bs.vp, ?_, ?_, h.edx,
      fun i hi => ?_, co.congr fun i hi => ?_⟩, ?_⟩
    · show s.gpr .eax + 16 = _
      rw [h.eax, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, add_ofNat_add]
      exact congrArg (fun k => sP s₀ + BitVec.ofNat 32 k) (by omega_using [])
    · show s.gpr .ecx - 1 = _
      rw [h.ecx]; exact cnt_next ht
    · show word (g .xmm5) i = _
      rw [k5 rfl]; exact h.z i hi
    · simp only [D8, In16]; omega_using []
    · show (some (s.gpr .ecx - 1 == 0) : Option Bool).map (!·) = _
      rw [h.ecx]; exact cnt_ne ht (by omega_using [hL])

theorem blkEnd_wp {s₀ : State} (hp : Pre s₀) {T : List Nat} {f G : Poly}
    {gl zp B c : Nat} (hB : gl * B = 16) (hc : c < B) {s : State} (h : GInv s₀ T f G gl zp c gl s) :
    WP isa (.block (blkEnd (8 * gl))) s fun s' =>
      LInv s₀ T f G gl zp (c + 1) s' ∧ eval .ne s' = some (decide (c + 1 < B)) := by
  have hgl : 0 < gl := Nat.pos_of_ne_zero fun e => by rw [e, Nat.zero_mul] at hB; exact absurd hB (by decide)
  have hL : gl * (c + 1) ≤ 16 := by
    have := Nat.mul_le_mul_left gl (Nat.succ_le_of_lt hc)
    rwa [hB] at this
  obtain ⟨a₁, -⟩ := arg_N0 hp (i := 1) (by decide)
  simp only [Nat.mul_one, Nat.reduceAdd] at a₁
  have ea : (s.gpr .esp + BitVec.ofNat 32 24).setWidth 64 = argAddr s₀ 1 := by rw [h.base.esp]; exact a₁
  have i₁ : InRegions (s.rd ++ s.wr) (argAddr s₀ 1) 4 := inRdN (in_arg hp h.base.wr (by decide))
  have sl := h.base.slot
  have e1 : s.gpr .eax + BitVec.ofNat 32 (2 * (8 * gl)) =
      sP s₀ + BitVec.ofNat 32 (16 * (32 + 2 * (gl * (c + 1)))) := by
    rw [h.eax, add_ofNat_add, Nat.mul_succ]
    exact congrArg (fun k => sP s₀ + BitVec.ofNat 32 k) (by omega_using [])
  apply WP.of_runBlock
  simp only [blkEnd, at_, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.ea, State.load32,
    State.setReg, arithFlags, State.setFlags, Option.bind_some, ea, i₁, sl, reduceCtorEq, ↓reduceIte,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨h.base.of_gpr (fun r h1 _ _ => by simp only [h1, ite_false]) rfl rfl rfl rfl h.base.vp, e1, h.edx,
    h.co.congr fun i hi => ?_⟩, ?_⟩
  · simp only [D8]; rw [Nat.mul_succ]; omega_using []
  · show (some (s.gpr .eax + BitVec.ofNat 32 (2 * (8 * gl)) - (sP s₀ + 1024) == 0) : Option Bool).map (!·) = _
    rw [e1, NttLoop.end_cmp _ (by omega_using [hL])]
    simp only [Option.map_some, Option.some.injEq]
    by_cases h1 : c + 1 < B
    · have := Nat.mul_lt_mul_of_pos_left h1 hgl
      rw [hB] at this
      rw [decide_eq_true h1, decide_eq_false (by omega_using [this])]; rfl
    · have e : c + 1 = B := by omega_using [hc, h1]
      rw [decide_eq_false h1, e, hB]; rfl


theorem pub_esp {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (hq : Pub s₀ s₀') :
    (N0 s₀).gpr .esp = (N0 s₀').gpr .esp := by
  rw [N0_esp hp, N0_esp hp', hq.1]

theorem lay8_piece {T : List Nat} {zv : Nat → Zq} {sS sD : Zq → Zq → Zq → Zq}
    {body : Nat → List Instr} {FX FY : BitVec 128 → BitVec 128 → BitVec 128 → BitVec 128}
    (hb : ∀ d, BodyOk (body d) d true FX FY) (hN : NewOk sh8 FX FY sS sD)
    (hT : TabOK T zv) (gl B zp : Nat) (hB : gl * B = 16) (hz : zp + B ≤ 128) (f G : State → Poly)
    (hG : ∀ s₀, LayOk sS sD zv (f s₀) (G s₀) (8 * gl) zp) {h₁ h₂ h₃ h₄ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.sseTaint.check (τr [.esp]) (.block layStart) h₁).isSome = true)
    (t₂ : (VG.X86.sseTaint.check (τr [.esp, .eax, .edx]) (.block (blkInit (8 * gl))) h₂).isSome = true)
    (t₃ : (VG.X86.sseTaint.check (τr [.esp, .eax, .ecx, .edx]) (.block (body (2 * (8 * gl)) ++ groupEnd))
      h₃).isSome = true)
    (t₄ : (VG.X86.sseTaint.check (τr [.esp, .eax, .edx]) (.block (blkEnd (8 * gl))) h₄).isSome = true) :
    Piece Pre Pub (fun s₀ s => LS s₀ T VK (f s₀) zp s)
      (fun s₀ s => LS s₀ T VK (G s₀) (zp + B) s) (layer8 body (8 * gl)) := by
  have hBp : 0 < B := Nat.pos_of_ne_zero fun e => by rw [e, Nat.mul_zero] at hB; exact absurd hB (by decide)
  have hgl : 0 < gl := Nat.pos_of_ne_zero fun e => by rw [e, Nat.zero_mul] at hB; exact absurd hB (by decide)
  refine Piece.mono (A := fun s₀ s => LS s₀ T VK (f s₀) zp s)
    (B := fun s₀ s => LInv s₀ T (f s₀) (G s₀) gl zp B s)
    (Piece.seq (B := fun s₀ s => LInv s₀ T (f s₀) (G s₀) gl zp 0 s)
    (sse [.esp] (fun s₀ s hp h => (layStart_wp hp h.base).mono fun s' ⟨b, e, d, m⟩ => ?_)
      (fun s₀ s₀' s s' hp hp' hq h h' r hr => ?_) t₁)
    (Piece.loop (fun c s₀ s => LInv s₀ T (f s₀) (G s₀) gl zp c s) hBp fun c hc =>
      Piece.seq (sse [.esp, .eax, .edx] (fun s₀ s hp h => blkInit_wp hp (by omega_using [hz, hc]) h)
          (fun s₀ s₀' s s' hp hp' hq h h' r hr => ?_) t₂)
        (Piece.seq (Piece.loop (fun t s₀ s => GInv s₀ T (f s₀) (G s₀) gl zp c t s) hgl fun t ht =>
            sse [.esp, .eax, .ecx, .edx]
              (fun s₀ s hp h => gstep hb hN hT hp (hG s₀) hB hc ht (by omega_using [hz, hc]) h)
              (fun s₀ s₀' s s' hp hp' hq h h' r hr => ?_) t₃)
          (sse [.esp, .eax, .edx] (fun s₀ s hp h => blkEnd_wp hp hB hc h)
            (fun s₀ s₀' s s' hp hp' hq h h' r hr => ?_) t₄)))) (fun _ _ _ h => h) fun s₀ s _ h => ?_
  · refine ⟨b, ?_, d.trans h.edx, fun i hi => ⟨fun hd => absurd hd (by rw [Nat.mul_zero]; omega_using []),
      fun _ => by rw [m]; exact h.co i hi⟩⟩
    rw [e, Nat.mul_zero]
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.base.esp, h'.base.esp, pub_esp hp hp' hq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h.base.esp, h'.base.esp, pub_esp hp hp' hq]
    · rw [h.eax, h'.eax, sP, sP, hq.2.2]
    · rw [h.edx, h'.edx, sP, sP, hq.2.2]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h.base.esp, h'.base.esp, pub_esp hp hp' hq]
    · rw [h.eax, h'.eax, sP, sP, hq.2.2]
    · rw [h.ecx, h'.ecx]
    · rw [h.edx, h'.edx, sP, sP, hq.2.2]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h.base.esp, h'.base.esp, pub_esp hp hp' hq]
    · rw [h.eax, h'.eax, sP, sP, hq.2.2]
    · rw [h.edx, h'.edx, sP, sP, hq.2.2]
  · exact ⟨h.base, h.edx, fun i hi => (h.co i hi).1 (by rw [hB]; exact hi)⟩

/-! ## The layers with `len = 4` and `len = 2` -/

/-- After `k` steps of sixteen coefficients, each with `nz` zetas. -/
structure FInv (s₀ : State) (T : List Nat) (f G : Poly) (nz zp k : Nat) (s : State) : Prop where
  base : Base s₀ T VK s
  eax : s.gpr .eax = sP s₀ + BitVec.ofNat 32 (16 * (32 + 2 * k))
  edx : s.gpr .edx = sP s₀ + BitVec.ofNat 32 (2 * (zp + nz * k))
  co : Co s₀ s.mem f G (fun i => i < 16 * k)

/-- A layer whose steps are of sixteen coefficients, with `nz` zetas each:
word `e` of the zetas loaded is the zeta of number `zq e` of the step, and
that of the butterfly `e`. -/
structure FlatOk (sh : Shape) (nz len : Nat) (zq : Nat → Nat) (zsel : Mem → Addr → BitVec 128) : Prop where
  zeta : ∀ (m : Mem) (tA : Addr) (T : List Nat) (zv : Nat → Zq), TabOK T zv →
    (∀ j < 128, wAt m tA j = BitVec.ofNat 16 (T.getD j 0)) → ∀ j, j + nz ≤ 128 →
      ZLanes (zsel m (tA + BitVec.ofNat 64 (2 * j))) (fun e => zv (j + zq e))
  pairs : ∀ (sS sD : Zq → Zq → Zq → Zq) (zv : Nat → Zq) (f G : Poly) (zp : Nat), LayOk sS sD zv f G len zp →
    ∀ k < 16, ∀ e < 8,
      G[idx (2 * k) (2 * k + 1) (sh.pa e)]! = sS f[idx (2 * k) (2 * k + 1) (sh.pa e)]!
          f[idx (2 * k) (2 * k + 1) (sh.pb e)]! (zv (zp + nz * k + zq e)) ∧
        G[idx (2 * k) (2 * k + 1) (sh.pb e)]! = sD f[idx (2 * k) (2 * k + 1) (sh.pa e)]!
          f[idx (2 * k) (2 * k + 1) (sh.pb e)]! (zv (zp + nz * k + zq e))

theorem idx_flat (k : Nat) {p : Nat} (hp : p < 16) : idx (2 * k) (2 * k + 1) p = 16 * k + p := by
  rw [idx]
  by_cases h : p < 8
  · rw [ite_eq_left h]; omega_using []
  · rw [ite_eq_right h]; omega_using [h, hp]

theorem tab_word {T : List Nat} {zv : Nat → Zq} (hT : TabOK T zv) {k : Nat} (hk : k < 128) :
    (BitVec.ofNat 16 (T.getD k 0)).toNat = (zv k).val * 65536 % 3329 := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans (tab_lt hT hk) (by decide)), hT k hk]

theorem lay4_at {sS sD : Zq → Zq → Zq → Zq} {zv : Nat → Zq} {f G : Poly} {zp : Nat} (hG : LayOk sS sD zv f G 4 zp)
    {k p : Nat} (hk : k < 16) (hp : p % 8 < 4) (hp16 : p < 16) :
    G[16 * k + p]! = sS f[16 * k + p]! f[16 * k + p + 4]! (zv (zp + 2 * k + p / 8)) ∧
      G[16 * k + p + 4]! = sD f[16 * k + p]! f[16 * k + p + 4]! (zv (zp + 2 * k + p / 8)) := by
  have := hG (2 * k + p / 8) (p % 8) hp (by omega_using [hk, hp16, hp])
  rwa [show 2 * 4 * (2 * k + p / 8) + p % 8 = 16 * k + p by omega_using [], ← Nat.add_assoc zp] at this

theorem flat4 : FlatOk sh4 2 4 (fun e => e / 4) zsel4 where
  zeta m tA T zv hT htb j hj e he := by
    show (word (zsel4 m (tA + BitVec.ofNat 64 (2 * j))) e).toNat = _
    rw [word_zsel4 _ _ _ he, htb _ (by omega_using [hj, he]), tab_word hT (by omega_using [hj, he])]
  pairs sS sD zv f G zp hG k hk e he := by
    rw [idx_flat k (sh4_ok.lt e he).1, idx_flat k (sh4_ok.lt e he).2]
    rcases cases8 he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lay4_at hG hk (p := 0) (by decide) (by decide)
    · exact lay4_at hG hk (p := 1) (by decide) (by decide)
    · exact lay4_at hG hk (p := 2) (by decide) (by decide)
    · exact lay4_at hG hk (p := 3) (by decide) (by decide)
    · exact lay4_at hG hk (p := 8) (by decide) (by decide)
    · exact lay4_at hG hk (p := 9) (by decide) (by decide)
    · exact lay4_at hG hk (p := 10) (by decide) (by decide)
    · exact lay4_at hG hk (p := 11) (by decide) (by decide)

theorem lay2_at {sS sD : Zq → Zq → Zq → Zq} {zv : Nat → Zq} {f G : Poly} {zp : Nat} (hG : LayOk sS sD zv f G 2 zp)
    {k p : Nat} (hk : k < 16) (hp : p % 4 < 2) (hp16 : p < 16) :
    G[16 * k + p]! = sS f[16 * k + p]! f[16 * k + p + 2]! (zv (zp + 4 * k + p / 4)) ∧
      G[16 * k + p + 2]! = sD f[16 * k + p]! f[16 * k + p + 2]! (zv (zp + 4 * k + p / 4)) := by
  have := hG (4 * k + p / 4) (p % 4) hp (by omega_using [hk, hp16, hp])
  rwa [show 2 * 2 * (4 * k + p / 4) + p % 4 = 16 * k + p by omega_using [], ← Nat.add_assoc zp] at this

theorem flat2 : FlatOk sh2 4 2 (fun e => e / 2) zsel2 where
  zeta m tA T zv hT htb j hj e he := by
    show (word (zsel2 m (tA + BitVec.ofNat 64 (2 * j))) e).toNat = _
    rw [word_zsel2 _ _ _ he, htb _ (by omega_using [hj, he]), tab_word hT (by omega_using [hj, he])]
  pairs sS sD zv f G zp hG k hk e he := by
    rw [idx_flat k (sh2_ok.lt e he).1, idx_flat k (sh2_ok.lt e he).2]
    rcases cases8 he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lay2_at hG hk (p := 0) (by decide) (by decide)
    · exact lay2_at hG hk (p := 1) (by decide) (by decide)
    · exact lay2_at hG hk (p := 4) (by decide) (by decide)
    · exact lay2_at hG hk (p := 5) (by decide) (by decide)
    · exact lay2_at hG hk (p := 8) (by decide) (by decide)
    · exact lay2_at hG hk (p := 9) (by decide) (by decide)
    · exact lay2_at hG hk (p := 12) (by decide) (by decide)
    · exact lay2_at hG hk (p := 13) (by decide) (by decide)

theorem fstep {sh : Shape} {nz len : Nat} {zq : Nat → Nat} {zsel : Mem → Addr → BitVec 128}
    (hfl : FlatOk sh nz len zq zsel) (hnz : 0 < nz) {zl : List Instr} (hzl : ZlOk zl zsel)
    {body : List Instr} {FX FY : BitVec 128 → BitVec 128 → BitVec 128 → BitVec 128}
    (hb : BodyOk body 16 false FX FY) {sS sD : Zq → Zq → Zq → Zq}
    (hN : NewOk sh FX FY sS sD) {T : List Nat} {zv : Nat → Zq} (hT : TabOK T zv) {s₀ : State}
    (hp : Pre s₀) {f G : Poly} {zp : Nat} (hG : LayOk sS sD zv f G len zp) (hz : zp + nz * 16 ≤ 128)
    {k : Nat} (hk : k < 16) {s : State} (h : FInv s₀ T f G nz zp k s) :
    WP isa (.block (zl ++ (body ++ flatEnd (2 * nz)))) s fun s' =>
      FInv s₀ T f G nz zp (k + 1) s' ∧ eval .ne s' = some (decide (k + 1 < 16)) := by
  have fs := hp.s_fit
  have hj : zp + nz * k + nz ≤ 128 := by
    have := Nat.mul_le_mul_left nz (Nat.succ_le_of_lt hk)
    rw [Nat.mul_succ] at this; omega_using [hz, this]
  have ez : s.ea (at_ .edx 0) = sA s₀ + BitVec.ofNat 64 (2 * (zp + nz * k)) := by
    rw [ea_at h.edx (by omega_using [fs, hj, hnz]), Nat.add_zero]
  show WP isa (.block (zl ++ (body ++ flatEnd (2 * nz)))) { s with xmm := s.xmm } _
  refine hzl s s.xmm _ _ _ ez (inRdN (in_s hp h.base.wr (by omega_using [hj, hnz]))) fun g g5 gr => ?_
  have bs : Base s₀ T VK { s with xmm := g } :=
    ⟨h.base.esp, h.base.rd, h.base.wr, h.base.mcdt, h.base.saved, h.base.frame, h.base.tbl, h.base.arg0,
      h.base.slot, h.base.vp.of_eq (gr _ (by decide)) (gr _ (by decide))⟩
  refine body_step hb hp bs (u := 2 * k) (u' := 2 * k + 1) (by omega_using [hk]) (by omega_using [hk])
    (by omega_using []) h.eax h.co (fun i h8 hd => ?_)
    (fun X Y hV => hN f G _ _ (fun e => zv (zp + nz * k + zq e)) (fun e he => ?_)
      (hfl.pairs sS sD zv f G zp hG k hk) X Y hV) fun m g' bs' co _ => ?_
  · simp only [In16] at h8; omega_using [h8, hd]
  · show (word (g .xmm5) e).toNat = _
    rw [g5]; exact hfl.zeta _ _ T zv hT h.base.tbl _ hj e he
  · obtain ⟨a₁, -⟩ := arg_N0 hp (i := 1) (by decide)
    simp only [Nat.mul_one, Nat.reduceAdd] at a₁
    have ea : (s.gpr .esp + BitVec.ofNat 32 24).setWidth 64 = argAddr s₀ 1 := by rw [h.base.esp]; exact a₁
    have i₁ : InRegions (s.rd ++ s.wr) (argAddr s₀ 1) 4 := inRdN (in_arg hp h.base.wr (by decide))
    have sl : m.readW (argAddr s₀ 1) 32 = sP s₀ + 1024 := bs'.slot
    have e1 : s.gpr .eax + 32 = sP s₀ + BitVec.ofNat 32 (16 * (32 + 2 * (k + 1))) := by
      rw [h.eax, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl, add_ofNat_add]
      exact congrArg (fun k => sP s₀ + BitVec.ofNat 32 k) (by omega_using [])
    apply WP.of_runBlock
    simp only [flatEnd, at_, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.ea,
      State.load32, State.setReg, arithFlags, State.setFlags, Option.bind_some, ea, i₁, sl,
      reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left']
    refine ⟨⟨bs'.of_gpr (fun r h1 _ h3 => by simp only [h1, h3, ite_false]) rfl rfl rfl rfl bs'.vp, e1, ?_,
      co.congr fun i hi => ?_⟩, ?_⟩
    · show s.gpr .edx + BitVec.ofNat 32 (2 * nz) = _
      rw [h.edx, add_ofNat_add, Nat.mul_succ]
      exact congrArg (fun k => sP s₀ + BitVec.ofNat 32 k) (by omega_using [])
    · simp only [In16]; omega_using []
    · show (some (s.gpr .eax + 32 - (sP s₀ + 1024) == 0) : Option Bool).map (!·) = _
      rw [e1, NttLoop.end_cmp _ (by omega_using [hk])]
      simp only [Option.map_some, Option.some.injEq]
      by_cases h1 : k + 1 < 16
      · rw [decide_eq_true h1, decide_eq_false (by omega_using [h1])]; rfl
      · rw [decide_eq_false h1, decide_eq_true (by omega_using [hk, h1])]; rfl

theorem layFlat_piece {sh : Shape} {nz len : Nat} {zq : Nat → Nat} {zsel : Mem → Addr → BitVec 128}
    (hfl : FlatOk sh nz len zq zsel) (hnz : 0 < nz) {zl : List Instr} (hzl : ZlOk zl zsel)
    {body : List Instr} {FX FY : BitVec 128 → BitVec 128 → BitVec 128 → BitVec 128}
    (hb : BodyOk body 16 false FX FY) {sS sD : Zq → Zq → Zq → Zq}
    (hN : NewOk sh FX FY sS sD) {T : List Nat} {zv : Nat → Zq} (hT : TabOK T zv) (zp : Nat)
    (hz : zp + nz * 16 ≤ 128) (f G : State → Poly) (hG : ∀ s₀, LayOk sS sD zv (f s₀) (G s₀) len zp)
    {h₁ h₂ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.sseTaint.check (τr [.esp]) (.block layStart) h₁).isSome = true)
    (t₂ : (VG.X86.sseTaint.check (τr [.esp, .eax, .edx]) (.block (zl ++ (body ++ flatEnd (2 * nz))))
      h₂).isSome = true) :
    Piece Pre Pub (fun s₀ s => LS s₀ T VK (f s₀) zp s)
      (fun s₀ s => LS s₀ T VK (G s₀) (zp + nz * 16) s) (layerFlat zl body (2 * nz)) := by
  refine Piece.mono (A := fun s₀ s => LS s₀ T VK (f s₀) zp s)
    (B := fun s₀ s => FInv s₀ T (f s₀) (G s₀) nz zp 16 s)
    (Piece.seq (B := fun s₀ s => FInv s₀ T (f s₀) (G s₀) nz zp 0 s)
    (sse [.esp] (fun s₀ s hp h => (layStart_wp hp h.base).mono fun s' ⟨b, e, d, m⟩ => ?_)
      (fun s₀ s₀' s s' hp hp' hq h h' r hr => ?_) t₁)
    (Piece.loop (fun k s₀ s => FInv s₀ T (f s₀) (G s₀) nz zp k s) (by decide) fun k hk =>
      sse [.esp, .eax, .edx] (fun s₀ s hp h => fstep hfl hnz hzl hb hN hT hp (hG s₀) hz hk h)
        (fun s₀ s₀' s s' hp hp' hq h h' r hr => ?_) t₂)) (fun _ _ _ h => h) fun s₀ s _ h => ?_
  · exact ⟨b, e, d.trans h.edx, fun i hi =>
      ⟨fun hd => absurd hd (by omega_using []), fun _ => by rw [m]; exact h.co i hi⟩⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.base.esp, h'.base.esp, pub_esp hp hp' hq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h.base.esp, h'.base.esp, pub_esp hp hp' hq]
    · rw [h.eax, h'.eax, sP, sP, hq.2.2]
    · rw [h.edx, h'.edx, sP, sP, hq.2.2]
  · exact ⟨h.base, h.edx, fun i hi => (h.co i hi).1 hi⟩


/-! ## The constants and the table -/

/-- The polynomial at entry. -/
abbrev F (s₀ : State) : Poly := polyAt s₀.mem (fA s₀)

theorem arg01_sep {s₀ : State} (hp : Pre s₀) : Mem.Sep (argAddr s₀ 0) 4 (argAddr s₀ 1) 4 := by
  have := hp.sp'
  intro x h₁ h₂
  simp only [argAddr, E0] at this h₁ h₂
  bv_omega

/-- What is written apart from `f` keeps `f`. -/
theorem keep_f {s₀ : State} (hp : Pre s₀) {m : Mem}
    (hf : Frame [polyRegion (sA s₀), aR s₀] (M0 s₀).mem m) {i : Nat} (hi : i < 256) :
    coeffAt m (fA s₀) i = coeffAt s₀.mem (fA s₀) i := by
  show m.readW (coeffAddr (fA s₀) i) 32 = s₀.mem.readW (coeffAddr (fA s₀) i) 32
  rw [hf.readW (r := polyRegion (fA s₀)) (coeff_contains _ (by rw [n_eq]; exact hi)) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.f_s
      · exact hp.f_a) (by decide),
    (M0_frame s₀ (sp12 hp)).readW (r := polyRegion (fA s₀)) (coeff_contains _ (by rw [n_eq]; exact hi))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact (mcdt_disj hp hp.stk_f).symm) (by decide)]

/-- After the constants: `eax` is `scratch`. -/
structure S1 (s₀ : State) (s : State) : Prop where
  esp : s.gpr .esp = (N0 s₀).gpr .esp
  eax : s.gpr .eax = sP s₀
  rd : s.rd = (N0 s₀).rd
  wr : s.wr = (N0 s₀).wr
  mem : s.mem = (M0 s₀).mem
  mcdt : s.mcdt = s₀.mcdt + 1
  saved : ∀ r ∈ [Reg.ebx, .esi, .edi, .ebp], s.gpr r = s₀.gpr r
  vk : VK s.xmm

theorem consts_wp {s₀ : State} (hp : Pre s₀) : WP isa (.block nttConsts) (N0 s₀) (S1 s₀) := by
  obtain ⟨a₁, v₁⟩ := arg_N0 hp (i := 1) (by decide)
  simp only [Nat.mul_one, Nat.reduceAdd] at a₁
  have i₁ : InRegions ((N0 s₀).rd ++ (N0 s₀).wr) (argAddr s₀ 1) 4 := inRdN (in_arg hp rfl (by decide))
  apply WP.of_runBlock
  simp only [nttConsts, wconst, at_, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, XOp.exec, State.setXmm, readSrc, State.ea, State.load32, State.setReg, a₁, i₁, v₁, Option.map_some,
    reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun r hr => ?_, ⟨bc_eq _, bc_eq _⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> rfl

/-- `s'` is `s` but for the registers `ds`, the flags and memory. -/
structure Regs (ds : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ ds → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  xmm : s'.xmm = s.xmm
  mcdt : s'.mcdt = s.mcdt

/-- The doubleword of entries `2k` and `2k + 1` of the table. -/
def wpair (T : List Nat) (k : Nat) : BitVec 32 := BitVec.ofNat 32 (T.getD (2 * k) 0 + 65536 * T.getD (2 * k + 1) 0)

/-- Entries `2k` and `2k + 1` of the table. -/
def wentry (T : List Nat) (k : Nat) : List Instr := [.mov .edx (.imm (wpair T k)), .store (at_ .eax (4 * k)) .edx]

/-- The first `2n` entries. -/
def wtableN (T : List Nat) (n : Nat) : List Instr := (List.range n).flatMap (wentry T)

theorem wtable_eq (T : List Nat) : wtable T = wtableN T 64 := rfl

theorem wtableN_succ (T : List Nat) (n : Nat) : wtableN T (n + 1) = wtableN T n ++ wentry T n := by
  simp only [wtableN, List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- The first `2n` entries of `T` at `p`, from `eax` at `p`: only `edx`, the
flags and the words at `p` change. -/
theorem wtableN_spec (T : List Nat) {p : Addr} :
    ∀ (n : Nat) (is : List Instr) (s : State) (P : State → Prop), n ≤ 64 →
      (∀ k < 64, s.ea (at_ .eax (4 * k)) = p + BitVec.ofNat 64 (4 * k)) →
      (∀ k < 64, InRegions s.wr (p + BitVec.ofNat 64 (4 * k)) 4) →
      (∀ s', Regs [.edx] s s' → Frame [polyRegion p] s.mem s'.mem →
        (∀ k < n, s'.mem.readW (p + BitVec.ofNat 64 (4 * k)) 32 = wpair T k) → WP isa (.block is) s' P) →
      WP isa (.block (wtableN T n ++ is)) s P
  | 0, is, s, P, _, _, _, k =>
    k s ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩ (Frame.refl _ _) (fun _ h => absurd h (by omega_using []))
  | n + 1, is, s, P, hn, hea, hin, k => by
    rw [wtableN_succ, List.append_assoc]
    refine wtableN_spec T n _ s P (by omega_using [hn]) hea hin fun s₁ o₁ f₁ c₁ => ?_
    have ea₁ : s₁.ea (at_ .eax (4 * n)) = p + BitVec.ofNat 64 (4 * n) := by
      rw [← hea n (by omega_using [hn])]; simp only [State.ea, at_, o₁.gpr .eax (by decide)]
    refine wp_cons (s' := s₁.setReg .edx (wpair T n)) (by simp only [exec, readSrc, Option.map_some]) ?_
    have hin' : InRegions (s₁.setReg .edx (wpair T n)).wr ((s₁.setReg .edx (wpair T n)).ea (at_ .eax (4 * n))) 4 := by
      simp only [State.ea, at_, State.setReg, show Reg.eax ≠ Reg.edx by decide, ite_false]
      rw [show (s₁.gpr .eax + BitVec.ofNat 32 (4 * n)).setWidth 64 = p + BitVec.ofNat 64 (4 * n) from ea₁, o₁.wr]
      exact hin n (by omega_using [hn])
    refine wp_store hin' ?_
    refine k _ ⟨fun r hr => ?_, o₁.rd, o₁.wr, o₁.xmm, o₁.mcdt⟩ ?_ ?_
    · simp only [List.mem_singleton] at hr
      show (s₁.setReg .edx _).gpr r = s.gpr r
      simp only [State.setReg, hr, ite_false]
      exact o₁.gpr r (by simp [hr])
    · simp only [State.ea, at_, State.setReg, show Reg.eax ≠ Reg.edx by decide, ite_false]
      rw [show (s₁.gpr .eax + BitVec.ofNat 32 (4 * n)).setWidth 64 = p + BitVec.ofNat 64 (4 * n) from ea₁]
      exact f₁.writeW (List.mem_singleton_self _) _
        (Offset.contains_base _ (by omega_using [hn]) (by omega_using [hn]))
    · intro j hj
      simp only [State.ea, at_, State.setReg, show Reg.eax ≠ Reg.edx by decide, ite_false, ite_true]
      rw [show (s₁.gpr .eax + BitVec.ofNat 32 (4 * n)).setWidth 64 = p + BitVec.ofNat 64 (4 * n) from ea₁]
      by_cases e : j = n
      · rw [e]; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep (Offset.sep p (by omega_using [e]) (by omega_using [hj, hn])
          (by omega_using [hn])) (by decide)]
        exact c₁ j (by omega_using [hj, e])

theorem ext_readW32 (m : Mem) (a : Addr) {j : Nat} (hj : j < 2) :
    (m.readW a 32).extractLsb' (16 * j) 16 = m.readW (a + BitVec.ofNat 64 (2 * j)) 16 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', Mem.readW, BitVec.getLsbD_setWidth]
  simp only [hi, decide_true, Bool.true_and]
  rw [getLsbD_read _ _ (by omega_using [hj, hi]), getLsbD_read _ _ (by omega_using [hi])]
  rw [show a + BitVec.ofNat 64 ((16 * j + i) / 8) = a + BitVec.ofNat 64 (2 * j) + BitVec.ofNat 64 (i / 8) by
    rw [show (16 * j + i) / 8 = 2 * j + i / 8 by omega_using [], BitVec.ofNat_add, BitVec.add_assoc]]
  simp only [decide_eq_true (show 16 * j + i < 32 by omega_using [hj, hi]), Bool.true_and]
  exact congrArg _ (by omega_using [])

theorem pack_word {lo : Nat} (hl : lo < 65536) (hi : Nat) :
    (BitVec.ofNat 32 (lo + 65536 * hi)).extractLsb' (16 * 0) 16 = BitVec.ofNat 16 lo ∧
      (BitVec.ofNat 32 (lo + 65536 * hi)).extractLsb' (16 * 1) 16 = BitVec.ofNat 16 hi := by
  constructor <;> apply BitVec.eq_of_toNat_eq <;>
    rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow] <;>
    simp only [Nat.reducePow, Nat.reduceMul, Nat.div_one] <;> omega_using [hl]

/-- The words of the table, from its doublewords. -/
theorem tbl_words {m : Mem} {p : Addr} {T : List Nat} (hT : ∀ k < 128, T.getD k 0 < 65536)
    (h : ∀ k < 64, m.readW (p + BitVec.ofNat 64 (4 * k)) 32 = wpair T k) :
    ∀ k < 128, wAt m p k = BitVec.ofNat 16 (T.getD k 0) := by
  have key : ∀ j < 64, wAt m p (2 * j) = BitVec.ofNat 16 (T.getD (2 * j) 0) ∧
      wAt m p (2 * j + 1) = BitVec.ofNat 16 (T.getD (2 * j + 1) 0) := fun j hj => by
    obtain ⟨p0, p1⟩ := pack_word (hT (2 * j) (by omega_using [hj])) (T.getD (2 * j + 1) 0)
    have e0 := ext_readW32 m (p + BitVec.ofNat 64 (4 * j)) (j := 0) (by decide)
    have e1 := ext_readW32 m (p + BitVec.ofNat 64 (4 * j)) (j := 1) (by decide)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, h j hj] at e0 e1
    refine ⟨?_, ?_⟩
    · rw [wAt, show 2 * (2 * j) = 4 * j + 2 * 0 by omega_using [], ← e0]; exact p0
    · rw [wAt, show 2 * (2 * j + 1) = 4 * j + 2 * 1 by omega_using [], ← e1]; exact p1
  intro k hk
  rcases Nat.mod_two_eq_zero_or_one k with h0 | h1
  · have := (key (k / 2) (by omega_using [hk])).1
    rwa [show 2 * (k / 2) = k by omega_using [h0]] at this
  · have := (key (k / 2) (by omega_using [hk])).2
    rwa [show 2 * (k / 2) + 1 = k by omega_using [h1]] at this

/-- After the table: `edx` is at its entry 1, and `f` is as at entry. -/
structure PS (s₀ : State) (T : List Nat) (s : State) : Prop where
  base : Base s₀ T VK s
  edx : s.gpr .edx = sP s₀ + BitVec.ofNat 32 (2 * 1)
  fk : ∀ i < 256, coeffAt s.mem (fA s₀) i = coeffAt s₀.mem (fA s₀) i

theorem table_wp {s₀ : State} (hp : Pre s₀) (T : List Nat) (hT : ∀ k < 128, T.getD k 0 < 65536) {s : State}
    (h : S1 s₀ s) : WP isa (.block (nttTable T)) s (PS s₀ T) := by
  have fs := hp.s_fit
  obtain ⟨a₀, v₀⟩ := arg_N0 hp (i := 0) (by decide)
  obtain ⟨a₁, -⟩ := arg_N0 hp (i := 1) (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceAdd] at a₀ a₁
  rw [nttTable, wtable_eq]
  refine wtableN_spec T (p := sA s₀) 64 _ _ _ (Nat.le_refl _) (fun k hk => ?_) (fun k hk => ?_) fun s₂ o₂ f₂ c₂ => ?_
  · show (s.gpr .eax + BitVec.ofNat 32 (4 * k)).setWidth 64 = _
    rw [h.eax]
    exact ea_off (by omega_using [fs, hk])
  · exact in_s hp h.wr (by omega_using [hk])
  have esp₂ : s₂.gpr .esp = (N0 s₀).gpr .esp := (o₂.gpr .esp (by decide)).trans h.esp
  have eax₂ : s₂.gpr .eax = sP s₀ := (o₂.gpr .eax (by decide)).trans h.eax
  have rd₂ : s₂.rd = (N0 s₀).rd := o₂.rd.trans h.rd
  have wr₂ : s₂.wr = (N0 s₀).wr := o₂.wr.trans h.wr
  have f₂' : Frame [polyRegion (sA s₀)] (M0 s₀).mem s₂.mem := h.mem ▸ f₂
  have a24 : (s₂.gpr .esp + BitVec.ofNat 32 24).setWidth 64 = argAddr s₀ 1 := by rw [esp₂]; exact a₁
  have in1 : InRegions s₂.wr (argAddr s₀ 1) 4 := in_arg hp wr₂ (by decide)
  have hsa : ∀ r ∈ [polyRegion (sA s₀)], (aR s₀).Disjoint r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact hp.s_a.symm
  have v0 : s₂.mem.readW (argAddr s₀ 0) 32 = fP s₀ := by
    rw [f₂'.readW (hp.arg_in (by decide)) hsa (by decide)]; exact v₀
  apply WP.of_runBlock
  simp only [at_, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.ea,
    State.store32, State.setReg, arithFlags, State.setFlags, Option.map_some, Option.bind_some, a24, in1,
    reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left']
  have fr : Frame [polyRegion (sA s₀), aR s₀] (M0 s₀).mem (s₂.mem.writeW (argAddr s₀ 1) (s₂.gpr .eax + 1024)) :=
    (f₂'.mono fun r hr => by simp at hr ⊢; exact .inl hr).writeW (by simp) _ (hp.arg_in (by decide))
  refine ⟨⟨esp₂, rd₂, wr₂, o₂.mcdt.trans h.mcdt, fun r hr => ?_, fr.mono fun r hr => by simp at hr ⊢; exact .inr hr,
    fun k hk => ?_, ?_, ?_, ?_⟩, ?_, fun i hi => ?_⟩
  · have e : s₂.gpr r = s.gpr r := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact o₂.gpr _ (by decide)
    have e' := h.saved r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact e.trans e'
  · show (s₂.mem.writeW (argAddr s₀ 1) (s₂.gpr .eax + 1024)).readW _ 16 = _
    rw [Mem.readW_writeW_sep (Region.Disjoint.sep hp.s_a (Offset.contains_base _ (by omega_using [hk])
      (by omega_using [hk])) (hp.arg_in (by decide))) (by decide)]
    exact tbl_words hT c₂ k hk
  · show (s₂.mem.writeW (argAddr s₀ 1) (s₂.gpr .eax + 1024)).readW (argAddr s₀ 0) 32 = _
    rw [Mem.readW_writeW_sep (arg01_sep hp) (by decide), v0]
  · show (s₂.mem.writeW (argAddr s₀ 1) (s₂.gpr .eax + 1024)).readW (argAddr s₀ 1) 32 = _
    rw [Mem.readW_writeW_self32, eax₂]
  · show VK s₂.xmm
    rw [o₂.xmm]; exact h.vk
  · show s₂.gpr .eax + 2 = _
    rw [eax₂]; rfl
  · exact keep_f hp fr hi

theorem init_piece (T : List Nat) (hT : ∀ k < 128, T.getD k 0 < 65536) {h₁ h₂ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.sseTaint.check (τr [.esp]) (.block nttConsts) h₁).isSome = true)
    (t₂ : (VG.X86.sseTaint.check (τr [.esp, .eax]) (.block (nttTable T)) h₂).isSome = true) :
    Piece Pre Pub (fun s₀ s => s = N0 s₀) (fun s₀ s => PS s₀ T s) (nttInit T) := by
  refine Piece.seq (B := fun s₀ s => S1 s₀ s)
    (sse [.esp] (fun s₀ s hp e => e ▸ consts_wp hp) (fun s₀ s₀' s s' hp hp' hq e e' r hr => ?_) t₁)
    (sse [.esp, .eax] (fun s₀ s hp h => table_wp hp T hT h) (fun s₀ s₀' s s' hp hp' hq h h' r hr => ?_) t₂)
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', pub_esp hp hp' hq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h.esp, h'.esp, pub_esp hp hp' hq]
    · rw [h.eax, h'.eax, sP, sP, hq.2.2]


/-! ## Between the `u32`s of `f` and the words -/

theorem satSignedWord_small {x : BitVec 32} (h : x.toNat < 32768) : satSignedWord x = x.setWidth 16 := by
  have e : x.toInt = x.toNat := by rw [BitVec.toInt_eq_toNat_cond, ite_eq_left (by omega_using [h])]
  rw [satSignedWord, ite_eq_right (by omega_using [e, h]), ite_eq_right (by omega_using [e, h])]

theorem word_packssdw_small (a b : BitVec 128) {e : Nat} (he : e < 8)
    (ha : ∀ j < 4, (dword a j).toNat < 32768) (hb : ∀ j < 4, (dword b j).toNat < 32768) :
    (word (XBinOp.eval .packssdw a b) e).toNat = if e < 4 then (dword a e).toNat else (dword b (e - 4)).toNat := by
  rw [word_packssdw _ _ he]
  split
  · rename_i h4
    rw [satSignedWord_small (ha e h4), BitVec.toNat_setWidth]; have := ha e h4; omega_using [this]
  · rename_i h4
    rw [satSignedWord_small (hb (e - 4) (by omega_using [he, h4])), BitVec.toNat_setWidth]
    have := hb (e - 4) (by omega_using [he, h4]); omega_using [this]

theorem dword_eq_words (x : BitVec 128) (j : Nat) :
    (dword x j).toNat = (word x (2 * j)).toNat + 65536 * (word x (2 * j + 1)).toNat := by
  have h0 := word_dword x j 0 (by decide)
  have h1 := word_dword x j 1 (by decide)
  rw [Nat.mul_zero, Nat.add_zero] at h0
  rw [h0, h1, BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
    Nat.shiftRight_eq_div_pow]
  have := (dword x j).isLt
  omega_using []

theorem word_zero (i : Nat) : (word (0 : BitVec 128) i).toNat = 0 := by
  rw [word, BitVec.extractLsb'_toNat]; simp

/-- The `u32`s that `punpcklwd` with zeros leaves: the low words, zero-extended. -/
theorem dword_punpcklwd0 (a : BitVec 128) {j : Nat} (hj : j < 4) :
    (dword (XBinOp.eval .punpcklwd a 0) j).toNat = (word a j).toNat := by
  rw [dword_eq_words, word_punpcklwd _ _ (by omega_using [hj]), word_punpcklwd _ _ (by omega_using [hj]),
    ite_eq_left (by omega_using []), ite_eq_right (by omega_using []), show 2 * j / 2 = j by omega_using [],
    show (2 * j + 1) / 2 = j by omega_using [], word_zero, Nat.mul_zero, Nat.add_zero]

/-- The `u32`s that `punpckhwd` with zeros leaves: the high words, zero-extended. -/
theorem dword_punpckhwd0 (a : BitVec 128) {j : Nat} (hj : j < 4) :
    (dword (XBinOp.eval .punpckhwd a 0) j).toNat = (word a (4 + j)).toNat := by
  rw [dword_eq_words, word_punpckhwd _ _ (by omega_using [hj]), word_punpckhwd _ _ (by omega_using [hj]),
    ite_eq_left (by omega_using []), ite_eq_right (by omega_using []), show 4 + 2 * j / 2 = 4 + j by omega_using [],
    show 4 + (2 * j + 1) / 2 = 4 + j by omega_using [], word_zero, Nat.mul_zero, Nat.add_zero]

theorem dword_rd16 (m : Mem) (p : Addr) (u : Nat) {j : Nat} (hj : j < 4) :
    dword (m.readW (p + BitVec.ofNat 64 (16 * u)) 128) j = coeffAt m p (4 * u + j) := by
  rw [dword_readW _ _ hj, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact congrArg (fun k => m.readW (p + BitVec.ofNat 64 k) 32) (by omega_using [])

/-- The coefficients at `p` after a 16-byte store at `p + 16u`. -/
theorem cAt_write16 (m : Mem) (p : Addr) (v : BitVec 128) {u i : Nat} (hu : u < 64) (hi : i < 256) :
    coeffAt (m.writeW (p + BitVec.ofNat 64 (16 * u)) v) p i =
      if 4 * u ≤ i ∧ i < 4 * u + 4 then dword v (i - 4 * u) else coeffAt m p i := by
  by_cases h : 4 * u ≤ i ∧ i < 4 * u + 4
  · rw [ite_eq_left h]
    have := readW_writeW128 m (p + BitVec.ofNat 64 (16 * u)) v (j := i - 4 * u) (by omega_using [h])
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 16 * u + 4 * (i - 4 * u) = 4 * i by omega_using [h]] at this
    exact this
  · rw [ite_eq_right h]
    exact Mem.readW_writeW_sep (Offset.sep p (by omega_using [h]) (by omega_using [hi]) (by omega_using [hu]))
      (by decide)

/-- Before group `k` of the coefficients of `f` goes to the words. -/
structure KInv (s₀ : State) (T : List Nat) (k : Nat) (s : State) : Prop where
  base : Base s₀ T VK s
  edx : s.gpr .edx = sP s₀ + BitVec.ofNat 32 (2 * 1)
  ecx : s.gpr .ecx = fP s₀ + BitVec.ofNat 32 (16 * (2 * k))
  eax : s.gpr .eax = sP s₀ + BitVec.ofNat 32 (16 * (32 + k))
  fk : ∀ i < 256, coeffAt s.mem (fA s₀) i = coeffAt s₀.mem (fA s₀) i
  done : ∀ i < 8 * k, (wAt s.mem (sA s₀) (256 + i)).toNat = ((F s₀)[i]!).val

/-- `ecx ← f` and `eax ←` the words. -/
theorem passStart_wp {s₀ : State} (hp : Pre s₀) {T : List Nat} {VP : (XReg → BitVec 128) → Prop} {s : State}
    (h : Base s₀ T VP s) :
    WP isa (.block [.mov .ecx (.mem (at_ .esp 20)), .mov .eax (.mem (at_ .esp 24)), .alu .sub .eax (.imm 512)]) s
      fun s' => Base s₀ T VP s' ∧ s'.gpr .ecx = fP s₀ ∧ s'.gpr .eax = sP s₀ + BitVec.ofNat 32 (16 * (32 + 0)) ∧
        s'.gpr .edx = s.gpr .edx ∧ s'.mem = s.mem := by
  obtain ⟨a₀, -⟩ := arg_N0 hp (i := 0) (by decide)
  obtain ⟨a₁, -⟩ := arg_N0 hp (i := 1) (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceAdd] at a₀ a₁
  have ea₀ : (s.gpr .esp + BitVec.ofNat 32 20).setWidth 64 = argAddr s₀ 0 := by rw [h.esp]; exact a₀
  have ea₁ : (s.gpr .esp + BitVec.ofNat 32 24).setWidth 64 = argAddr s₀ 1 := by rw [h.esp]; exact a₁
  have i₀ : InRegions (s.rd ++ s.wr) (argAddr s₀ 0) 4 := inRdN (in_arg hp h.wr (by decide))
  have i₁ : InRegions (s.rd ++ s.wr) (argAddr s₀ 1) 4 := inRdN (in_arg hp h.wr (by decide))
  have v₀ := h.arg0
  have sl := h.slot
  apply WP.of_runBlock
  simp only [at_, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.ea, State.load32,
    State.setReg, arithFlags, State.setFlags, Option.map_some, Option.bind_some, ea₀, ea₁, i₀, i₁, v₀, sl,
    reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left']
  refine ⟨h.of_gpr (fun r h1 h2 _ => by simp only [h1, h2, ite_false]) rfl rfl rfl rfl h.vp, trivial, slot_sub _, ?_⟩
  trivial

theorem kstep {s₀ : State} (hp : Pre s₀) {T : List Nat} {k : Nat} (hk : k < 32) {s : State}
    (h : KInv s₀ T k s) :
    WP isa (.block wpackStep) s fun s' => KInv s₀ T (k + 1) s' ∧ eval .ne s' = some (decide (k + 1 < 32)) := by
  have fs := hp.s_fit
  have ff := hp.f_fit
  have eF : s.ea (at_ .ecx 0) = fA s₀ + BitVec.ofNat 64 (16 * (2 * k)) := by
    rw [ea_at h.ecx (by omega_using [ff, hk]), Nat.add_zero]
  have eF' : s.ea (at_ .ecx 16) = fA s₀ + BitVec.ofNat 64 (16 * (2 * k + 1)) := by
    rw [ea_at h.ecx (by omega_using [ff, hk])]
    exact congrArg (fun j => fA s₀ + BitVec.ofNat 64 j) (by omega_using [])
  have eS : s.ea (at_ .eax 0) = sA s₀ + BitVec.ofNat 64 (16 * (32 + k)) := by
    rw [ea_at h.eax (by omega_using [fs, hk]), Nat.add_zero]
  have iS := in_s hp h.base.wr (o := 16 * (32 + k)) (n := 16) (by omega_using [hk])
  have hcon : (polyRegion (sA s₀)).Contains (sA s₀ + BitVec.ofNat 64 (16 * (32 + k))) (128 / 8) :=
    Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])
  show WP isa (.block (.movdquLoad .xmm0 (at_ .ecx 0) :: .movdquLoad .xmm1 (at_ .ecx 16) ::
    wb .packssdw .xmm0 .xmm1 :: .movdquStore (at_ .eax 0) .xmm0 :: _)) { s with xmm := s.xmm } _
  refine wp_ld eF (inRdN (in_f hp h.base.wr (by omega_using [hk]))) (wp_ld eF'
    (inRdN (in_f hp h.base.wr (by omega_using [hk]))) (wp_xs rfl (wp_st eS iS ?_)))
  generalize hV : XBinOp.eval .packssdw (s.mem.readW (fA s₀ + BitVec.ofNat 64 (16 * (2 * k))) 128)
    (s.mem.readW (fA s₀ + BitVec.ofNat 64 (16 * (2 * k + 1))) 128) = V
  have small : ∀ u, u < 64 → ∀ j < 4,
      (dword (s.mem.readW (fA s₀ + BitVec.ofNat 64 (16 * u)) 128) j).toNat = ((F s₀)[4 * u + j]!).val ∧
        (dword (s.mem.readW (fA s₀ + BitVec.ofNat 64 (16 * u)) 128) j).toNat < 32768 := fun u hu j hj => by
    have hi : 4 * u + j < n := by rw [n_eq]; omega_using [hu, hj]
    have hr := hp.f_red _ hi
    rw [dword_rd16 _ _ _ hj, h.fk _ hi, polyAt_val hp.f_red hi]
    exact ⟨rfl, Nat.lt_trans hr (by decide)⟩
  have lanes : ∀ e < 8, (word V e).toNat = ((F s₀)[8 * k + e]!).val := fun e he => by
    rw [← hV, word_packssdw_small _ _ he (fun j hj => (small _ (by omega_using [hk]) j hj).2)
      (fun j hj => (small _ (by omega_using [hk]) j hj).2)]
    by_cases h4 : e < 4
    · rw [ite_eq_left h4, (small _ (by omega_using [hk]) e h4).1]
      exact congrArg (fun i : Nat => ((F s₀)[i]!).val) (by omega_using [])
    · rw [ite_eq_right h4, (small _ (by omega_using [hk]) (e - 4) (by omega_using [he, h4])).1]
      exact congrArg (fun i : Nat => ((F s₀)[i]!).val) (by omega_using [h4])
  have hf : Frame [polyRegion (sA s₀)] s.mem (s.mem.writeW (sA s₀ + BitVec.ofNat 64 (16 * (32 + k))) V) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) V hcon
  have bs : Base s₀ T VK { ({ s with mem := s.mem.writeW (sA s₀ + BitVec.ofNat 64 (16 * (32 + k))) V } : State)
      with xmm := fun r => if r = XReg.xmm0 then V else if r = XReg.xmm1 then
        s.mem.readW (fA s₀ + BitVec.ofNat 64 (16 * (2 * k + 1))) 128 else if r = XReg.xmm0 then
        s.mem.readW (fA s₀ + BitVec.ofNat 64 (16 * (2 * k))) 128 else s.xmm r } :=
    h.base.stepS hp hf (fun j hj => by
      rw [wAt_write16 _ _ _ (by omega_using [hk]) (by omega_using [hj]), ite_eq_right (by omega_using [hj])])
      (h.base.vp.of_eq rfl rfl)
  obtain ⟨a₁, -⟩ := arg_N0 hp (i := 1) (by decide)
  simp only [Nat.mul_one, Nat.reduceAdd] at a₁
  have ea : (s.gpr .esp + BitVec.ofNat 32 24).setWidth 64 = argAddr s₀ 1 := by rw [h.base.esp]; exact a₁
  have i₁ : InRegions (s.rd ++ s.wr) (argAddr s₀ 1) 4 := inRdN (in_arg hp h.base.wr (by decide))
  have sl : (s.mem.writeW (sA s₀ + BitVec.ofNat 64 (16 * (32 + k))) V).readW (argAddr s₀ 1) 32 = sP s₀ + 1024 :=
    bs.slot
  have e1 : s.gpr .eax + 16 = sP s₀ + BitVec.ofNat 32 (16 * (32 + (k + 1))) := by
    rw [h.eax, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, add_ofNat_add]
    exact congrArg (fun j => sP s₀ + BitVec.ofNat 32 j) (by omega_using [])
  subst hV
  apply WP.of_runBlock
  simp only [at_, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.ea, State.load32,
    State.setReg, arithFlags, State.setFlags, Option.bind_some, ea, i₁, sl, reduceCtorEq, ↓reduceIte,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨bs.of_gpr (fun r h1 h2 _ => by simp only [h1, h2, ite_false]) rfl rfl rfl rfl bs.vp, h.edx, ?_, e1,
    fun i hi => ?_, fun i hi => ?_⟩, ?_⟩
  · show s.gpr .ecx + 32 = _
    rw [h.ecx, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl, add_ofNat_add]
    exact congrArg (fun j => fP s₀ + BitVec.ofNat 32 j) (by omega_using [])
  · show (s.mem.writeW _ _).readW (coeffAddr (fA s₀) i) 32 = _
    rw [hf.readW (r := polyRegion (fA s₀)) (coeff_contains _ (by rw [n_eq]; exact hi))
      (by simpa using hp.f_s) (by decide)]
    exact h.fk i hi
  · show (wAt (s.mem.writeW _ _) (sA s₀) (256 + i)).toNat = _
    rw [wAt_write16 _ _ _ (by omega_using [hk]) (by omega_using [hi, hk])]
    by_cases h1 : 8 * k ≤ i
    · rw [ite_eq_left (by omega_using [h1, hi]), show 256 + i - 8 * (32 + k) = i - 8 * k by omega_using [h1],
        lanes _ (by omega_using [h1, hi]), show 8 * k + (i - 8 * k) = i by omega_using [h1]]
    · rw [ite_eq_right (by omega_using [h1])]; exact h.done i (by omega_using [h1])
  · show (some (s.gpr .eax + 16 - (sP s₀ + 1024) == 0) : Option Bool).map (!·) = _
    rw [e1, NttLoop.end_cmp _ (by omega_using [hk])]
    simp only [Option.map_some, Option.some.injEq]
    by_cases h1 : k + 1 < 32
    · rw [decide_eq_true h1, decide_eq_false (by omega_using [h1])]; rfl
    · rw [decide_eq_false h1, decide_eq_true (by omega_using [hk, h1])]; rfl

theorem pack_piece (T : List Nat) {h₁ h₂ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.sseTaint.check (τr [.esp]) (.block (passStart [])) h₁).isSome = true)
    (t₂ : (VG.X86.sseTaint.check (τr [.esp, .eax, .ecx]) (.block wpackStep) h₂).isSome = true) :
    Piece Pre Pub (fun s₀ s => PS s₀ T s) (fun s₀ s => LS s₀ T VK (F s₀) 1 s) wpackPass := by
  refine Piece.mono (A := fun s₀ s => PS s₀ T s) (B := fun s₀ s => KInv s₀ T 32 s)
    (Piece.seq (B := fun s₀ s => KInv s₀ T 0 s)
    (sse [.esp] (fun s₀ s hp h => (passStart_wp hp h.base).mono fun s' ⟨b, c, a, d, m⟩ => ?_)
      (fun s₀ s₀' s s' hp hp' hq h h' r hr => ?_) t₁)
    (Piece.loop (fun k s₀ s => KInv s₀ T k s) (by decide) fun k hk =>
      sse [.esp, .eax, .ecx] (fun s₀ s hp h => kstep hp hk h)
        (fun s₀ s₀' s s' hp hp' hq h h' r hr => ?_) t₂)) (fun _ _ _ h => h) fun s₀ s _ h => ?_
  · refine ⟨b, d.trans h.edx, ?_, a, fun i hi => by rw [m]; exact h.fk i hi, fun i hi => absurd hi (by omega_using [])⟩
    rw [c]; exact (BitVec.add_zero _).symm
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.base.esp, h'.base.esp, pub_esp hp hp' hq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h.base.esp, h'.base.esp, pub_esp hp hp' hq]
    · rw [h.eax, h'.eax, sP, sP, hq.2.2]
    · rw [h.ecx, h'.ecx, fP, fP, hq.2.1]
  · exact ⟨h.base, h.edx, fun i hi => h.done i hi⟩


/-! ## The words back to the `u32`s of `f` -/

/-- Before group `k` of the words goes back to `f`: the coefficients done
are `red` of the words' values. -/
structure UInv (s₀ : State) (T : List Nat) (VP : (XReg → BitVec 128) → Prop) (G : Poly) (red : Zq → Zq)
    (k : Nat) (s : State) : Prop where
  base : Base s₀ T VP s
  ecx : s.gpr .ecx = fP s₀ + BitVec.ofNat 32 (16 * (2 * k))
  eax : s.gpr .eax = sP s₀ + BitVec.ofNat 32 (16 * (32 + k))
  co : ∀ i < 256, (wAt s.mem (sA s₀) (256 + i)).toNat = (G[i]!).val
  done : ∀ i < 8 * k, (coeffAt s.mem (fA s₀) i).toNat = (red G[i]!).val

/-- The code of a pass, on `x` in `xmm0`. -/
def PassOk (core : List Instr) (VP : (XReg → BitVec 128) → Prop) (Fx : BitVec 128 → BitVec 128) : Prop :=
  ∀ (s : State) (f : XReg → BitVec 128) (x : BitVec 128) (is : List Instr) (Q : State → Prop), 0 < s.mcdt → VP f →
    (∀ g : XReg → BitVec 128, g .xmm0 = Fx x → VP g → WP isa (.block is) { s with xmm := g } Q) →
    WP isa (.block (core ++ is)) { s with xmm := fun r => if r = .xmm0 then x else f r } Q

/-- The words `Fx` leaves are `red` of the coefficients. -/
def PassLane (Fx : BitVec 128 → BitVec 128) (red : Zq → Zq) : Prop :=
  ∀ (x : BitVec 128) (ys : Nat → Zq), Lanes x ys → Lanes (Fx x) (fun j => red (ys j))

theorem ustep {core : List Instr} {VP : (XReg → BitVec 128) → Prop} {Fx : BitVec 128 → BitVec 128}
    (hc : PassOk core VP Fx) (h4 : ∀ f, VP f → f .xmm4 = 0)
    (hvp : ∀ f g : XReg → BitVec 128, VP f → (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → g r = f r) → VP g)
    {red : Zq → Zq} (hl : PassLane Fx red) {s₀ : State}
    (hp : Pre s₀) {T : List Nat} {G : Poly} {k : Nat} (hk : k < 32) {s : State}
    (h : UInv s₀ T VP G red k s) :
    WP isa (.block (wunpackStep core)) s fun s' =>
      UInv s₀ T VP G red (k + 1) s' ∧ eval .ne s' = some (decide (k + 1 < 32)) := by
  have fs := hp.s_fit
  have ff := hp.f_fit
  have eF : s.ea (at_ .ecx 0) = fA s₀ + BitVec.ofNat 64 (16 * (2 * k)) := by
    rw [ea_at h.ecx (by omega_using [ff, hk]), Nat.add_zero]
  have eF' : s.ea (at_ .ecx 16) = fA s₀ + BitVec.ofNat 64 (16 * (2 * k + 1)) := by
    rw [ea_at h.ecx (by omega_using [ff, hk])]
    exact congrArg (fun j => fA s₀ + BitVec.ofNat 64 j) (by omega_using [])
  have eS : s.ea (at_ .eax 0) = sA s₀ + BitVec.ofNat 64 (16 * (32 + k)) := by
    rw [ea_at h.eax (by omega_using [fs, hk]), Nat.add_zero]
  have hm : 0 < s.mcdt := by rw [h.base.mcdt]; exact Nat.succ_pos _
  have iF := in_f hp h.base.wr (o := 16 * (2 * k)) (n := 16) (by omega_using [hk])
  have iF' := in_f hp h.base.wr (o := 16 * (2 * k + 1)) (n := 16) (by omega_using [hk])
  have hcon : (polyRegion (fA s₀)).Contains (fA s₀ + BitVec.ofNat 64 (16 * (2 * k))) (128 / 8) :=
    Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])
  have hcon' : (polyRegion (fA s₀)).Contains (fA s₀ + BitVec.ofNat 64 (16 * (2 * k + 1))) (128 / 8) :=
    Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])
  show WP isa (.block (.movdquLoad .xmm0 (at_ .eax 0) :: (core ++ (wmov .xmm1 .xmm0 :: wb .punpcklwd .xmm0 .xmm4 ::
    wb .punpckhwd .xmm1 .xmm4 :: .movdquStore (at_ .ecx 0) .xmm0 :: .movdquStore (at_ .ecx 16) .xmm1 :: _))))
    { s with xmm := s.xmm } _
  refine wp_ld eS (inRdN (in_s hp h.base.wr (by omega_using [hk]))) (hc s _ _ _ _ hm h.base.vp fun g vg cg =>
    wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_st eF iF (wp_st eF' iF' ?_)))))
  have g4 : g .xmm4 = 0 := h4 g cg
  have lanes : Lanes (g .xmm0) (fun j => red G[8 * k + j]!) := by
    rw [vg]
    exact hl _ (fun j => G[8 * k + j]!) fun j hj => by
      rw [word_rd16 _ _ _ hj, show 8 * (32 + k) + j = 256 + (8 * k + j) by omega_using []]
      exact h.co _ (by omega_using [hk, hj])
  have vL : ∀ j < 4, (dword (XBinOp.eval .punpcklwd (g .xmm0) (g .xmm4)) j).toNat = (red G[8 * k + j]!).val :=
    fun j hj => by rw [g4, dword_punpcklwd0 _ hj]; exact lanes j (by omega_using [hj])
  have vH : ∀ j < 4, (dword (XBinOp.eval .punpckhwd (g .xmm0) (g .xmm4)) j).toNat =
      (red G[8 * k + (4 + j)]!).val :=
    fun j hj => by rw [g4, dword_punpckhwd0 _ hj]; exact lanes (4 + j) (by omega_using [hj])
  have hf : Frame [polyRegion (fA s₀)] s.mem ((s.mem.writeW (fA s₀ + BitVec.ofNat 64 (16 * (2 * k)))
      (XBinOp.eval .punpcklwd (g .xmm0) (g .xmm4))).writeW (fA s₀ + BitVec.ofNat 64 (16 * (2 * k + 1)))
      (XBinOp.eval .punpckhwd (g .xmm0) (g .xmm4))) :=
    ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ hcon).writeW (List.mem_singleton_self _) _ hcon'
  have bs := h.base.stepF hp hf (g := fun r => if r = XReg.xmm1 then XBinOp.eval .punpckhwd (g .xmm0) (g .xmm4)
      else if r = XReg.xmm0 then XBinOp.eval .punpcklwd (g .xmm0) (g .xmm4) else if r = XReg.xmm1 then
        XBinOp.eval .movdqa (g .xmm1) (g .xmm0) else g r)
    (hvp g _ cg fun r h0 h1 => by simp only [h0, h1, ite_false])
  obtain ⟨a₁, -⟩ := arg_N0 hp (i := 1) (by decide)
  simp only [Nat.mul_one, Nat.reduceAdd] at a₁
  have ea : (s.gpr .esp + BitVec.ofNat 32 24).setWidth 64 = argAddr s₀ 1 := by rw [h.base.esp]; exact a₁
  have i₁ : InRegions (s.rd ++ s.wr) (argAddr s₀ 1) 4 := inRdN (in_arg hp h.base.wr (by decide))
  have sl : ((s.mem.writeW (fA s₀ + BitVec.ofNat 64 (16 * (2 * k)))
      (XBinOp.eval .punpcklwd (g .xmm0) (g .xmm4))).writeW (fA s₀ + BitVec.ofNat 64 (16 * (2 * k + 1)))
      (XBinOp.eval .punpckhwd (g .xmm0) (g .xmm4))).readW (argAddr s₀ 1) 32 = sP s₀ + 1024 := bs.slot
  have mv : ∀ a b : BitVec 128, XBinOp.eval .movdqa a b = b := fun _ _ => rfl
  have e1 : s.gpr .eax + 16 = sP s₀ + BitVec.ofNat 32 (16 * (32 + (k + 1))) := by
    rw [h.eax, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, add_ofNat_add]
    exact congrArg (fun j => sP s₀ + BitVec.ofNat 32 j) (by omega_using [])
  apply WP.of_runBlock
  simp only [at_, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.ea, State.load32,
    State.setReg, arithFlags, State.setFlags, Option.bind_some, ea, i₁, mv, sl, reduceCtorEq, ↓reduceIte,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨bs.of_gpr (fun r h1 h2 _ => by simp only [h1, h2, ite_false]) rfl rfl rfl rfl bs.vp, ?_, e1,
    fun i hi => ?_, fun i hi => ?_⟩, ?_⟩
  · show s.gpr .ecx + 32 = _
    rw [h.ecx, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl, add_ofNat_add]
    exact congrArg (fun j => fP s₀ + BitVec.ofNat 32 j) (by omega_using [])
  · show (Mem.readW _ (sA s₀ + BitVec.ofNat 64 (2 * (256 + i))) 16).toNat = _
    rw [hf.readW (r := polyRegion (sA s₀)) (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi]))
      (by simpa using hp.f_s.symm) (by decide)]
    exact h.co i hi
  · show (coeffAt (Mem.writeW (Mem.writeW s.mem _ _) _ _) (fA s₀) i).toNat = _
    rw [cAt_write16 _ _ _ (by omega_using [hk]) (by omega_using [hi, hk]),
      cAt_write16 _ _ _ (by omega_using [hk]) (by omega_using [hi, hk])]
    by_cases h2 : 8 * k + 4 ≤ i
    · rw [ite_eq_left (by omega_using [h2, hi]), vH _ (by omega_using [h2, hi])]
      exact congrArg (fun j : Nat => (red G[j]!).val) (by omega_using [h2])
    · rw [ite_eq_right (by omega_using [h2])]
      by_cases h1 : 8 * k ≤ i
      · rw [ite_eq_left (by omega_using [h1, h2]), vL _ (by omega_using [h1, h2])]
        exact congrArg (fun j : Nat => (red G[j]!).val) (by omega_using [h1])
      · rw [ite_eq_right (by omega_using [h1])]; exact h.done i (by omega_using [h1])
  · show (some (s.gpr .eax + 16 - (sP s₀ + 1024) == 0) : Option Bool).map (!·) = _
    rw [e1, NttLoop.end_cmp _ (by omega_using [hk])]
    simp only [Option.map_some, Option.some.injEq]
    by_cases h1 : k + 1 < 32
    · rw [decide_eq_true h1, decide_eq_false (by omega_using [h1])]; rfl
    · rw [decide_eq_false h1, decide_eq_true (by omega_using [hk, h1])]; rfl

theorem unpack_piece {init core : List Instr} {VP : (XReg → BitVec 128) → Prop} {Fx : BitVec 128 → BitVec 128}
    {red : Zq → Zq} {T : List Nat} (hc : PassOk core VP Fx) (h4 : ∀ f, VP f → f .xmm4 = 0)
    (hvp : ∀ f g : XReg → BitVec 128, VP f → (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → g r = f r) → VP g)
    (hl : PassLane Fx red) (G : State → Poly) (zp : Nat)
    (hinit : ∀ s₀ s, Pre s₀ → LS s₀ T VK (G s₀) zp s →
      WP isa (.block (passStart (wb .pxor .xmm4 .xmm4 :: init))) s (UInv s₀ T VP (G s₀) red 0))
    {h₁ h₂ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.sseTaint.check (τr [.esp]) (.block (passStart (wb .pxor .xmm4 .xmm4 :: init))) h₁).isSome = true)
    (t₂ : (VG.X86.sseTaint.check (τr [.esp, .eax, .ecx]) (.block (wunpackStep core)) h₂).isSome = true) :
    Piece Pre Pub (fun s₀ s => LS s₀ T VK (G s₀) zp s)
      (fun s₀ s => UInv s₀ T VP (G s₀) red 32 s) (wunpackPass init core) := by
  refine Piece.seq (B := fun s₀ s => UInv s₀ T VP (G s₀) red 0 s)
    (sse [.esp] hinit (fun s₀ s₀' s s' hp hp' hq h h' r hr => ?_) t₁)
    (Piece.loop (fun k s₀ s => UInv s₀ T VP (G s₀) red k s) (by decide) fun k hk =>
      sse [.esp, .eax, .ecx] (fun s₀ s hp h => ustep hc h4 hvp hl hp hk h)
        (fun s₀ s₀' s s' hp hp' hq h h' r hr => ?_) t₂)
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.base.esp, h'.base.esp, pub_esp hp hp' hq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h.base.esp, h'.base.esp, pub_esp hp hp' hq]
    · rw [h.eax, h'.eax, sP, sP, hq.2.2]
    · rw [h.ecx, h'.ecx, fP, fP, hq.2.1]

/-! ## The last pass of `ntt` -/

/-- `xmm4` is zero. -/
def VU (f : XReg → BitVec 128) : Prop := f .xmm4 = 0

theorem nil_ok : PassOk [] VU id := fun _ _ _ _ _ _ hv k => k _ rfl hv

theorem id_lanes : PassLane id id := fun _ _ h => h

theorem pxor_self (a : BitVec 128) : XBinOp.eval .pxor a a = 0 := BitVec.xor_self

theorem uinitF_wp {s₀ : State} (hp : Pre s₀) {T : List Nat} {G : Poly} {zp : Nat} {s : State}
    (h : LS s₀ T VK G zp s) :
    WP isa (.block (passStart (wb .pxor .xmm4 .xmm4 :: []))) s (UInv s₀ T VU G id 0) := by
  have bs : Base s₀ T VU
      { s with xmm := fun r => if r = XReg.xmm4 then (XBinOp.eval .pxor (s.xmm .xmm4) (s.xmm .xmm4)) else s.xmm r } :=
    ⟨h.base.esp, h.base.rd, h.base.wr, h.base.mcdt, h.base.saved, h.base.frame, h.base.tbl, h.base.arg0,
      h.base.slot, by show XBinOp.eval .pxor _ _ = 0; exact pxor_self _⟩
  show WP isa (.block (wb .pxor .xmm4 .xmm4 :: _)) { s with xmm := s.xmm } _
  refine wp_xs rfl ((passStart_wp hp bs).mono fun s' ⟨b, c, a, _, m⟩ => ⟨b, ?_, a,
    fun i hi => by rw [m]; exact h.co i hi, fun i hi => absurd hi (by omega_using [])⟩)
  rw [c]; exact (BitVec.add_zero _).symm

/-! ## The last pass of `nttInv` -/

/-- `3303 · 2¹⁶ mod q` in each word. -/
abbrev scaleV : BitVec 128 := bc 0x02000200#32

/-- The constants of the last pass of `nttInv`. -/
structure VS (f : XReg → BitVec 128) : Prop where
  zero : f .xmm4 = 0
  vk : VK f
  sc : f .xmm5 = scaleV

/-- The register `scaleCore` leaves. -/
def scaleX (x : BitVec 128) : BitVec 128 := caddV (montV x scaleV)

theorem scaleCore_ok : PassOk scaleCore VS scaleX := by
  intro s f x is Q hm hv k
  rw [show scaleCore ++ is = wmont .xmm0 .xmm5 .xmm2 ++ (wcadd .xmm0 .xmm2 ++ is) by
    simp only [scaleCore, List.append_assoc]]
  refine wmont_wp hm (hv.vk.of_eq rfl rfl) fun g₁ v₁ r₁ => ?_
  have c₁ : VK g₁ := hv.vk.of_eq (r₁ _ (by decide) (by decide)) (r₁ _ (by decide) (by decide))
  refine wcadd_wp (.inl rfl) c₁ fun g₂ v₂ r₂ => k g₂ ?_ ⟨?_, ?_, ?_⟩
  · rw [v₂, v₁, scaleX, ← hv.sc]; rfl
  · rw [r₂ _ (by decide) (by decide), r₁ _ (by decide) (by decide)]; exact hv.zero
  · exact c₁.of_eq (r₂ _ (by decide) (by decide)) (r₂ _ (by decide) (by decide))
  · rw [r₂ _ (by decide) (by decide), r₁ _ (by decide) (by decide)]; exact hv.sc

theorem scale_lanes : PassLane scaleX (· * 3303) := fun x ys h j hj => by
  have hy := val_lt (ys j)
  have bi := W.toInt_of_lt (a := word x j) (by rw [h j hj]; exact hy)
  have hz : (word scaleV j).toNat = (3303 : Zq).val * 65536 % 3329 := by
    rw [word_bc _ hj]
    rcases Nat.mod_two_eq_zero_or_one j with e | e <;> rw [e] <;> rfl
  have hm := W.mulZ_spec (b := word x j) (z := word scaleV j) (y := ys j) (ζ := 3303)
    (by rw [bi, h j hj]; omega_using [hy]) (by rw [bi, h j hj]; omega_using [hy])
    (by rw [bi, h j hj]; omega_using []) hz
  rw [scaleX, word_caddV _ hj, word_montV _ _ hj]
  have n2 := W.toNat_of_toInt (a := W.caddW (W.montW (word x j) (word scaleV j)))
    (by rw [hm]; exact Int.natCast_nonneg _)
  rw [hm] at n2
  show _ = (ys j * 3303).val
  rw [Fin.mul_comm]
  exact Int.ofNat.inj n2

theorem uinitI_wp {s₀ : State} (hp : Pre s₀) {T : List Nat} {G : Poly} {zp : Nat} {s : State}
    (h : LS s₀ T VK G zp s) :
    WP isa (.block (passStart (wb .pxor .xmm4 .xmm4 :: scaleInit))) s (UInv s₀ T VS G (· * 3303) 0) := by
  have key : WP isa (.block (wb .pxor .xmm4 .xmm4 :: scaleInit)) s fun s' =>
      Base s₀ T VS s' ∧ s'.gpr .edx = s.gpr .edx ∧ s'.mem = s.mem := by
    apply WP.of_runBlock
    simp only [scaleInit, wconst, wb, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, State.setXmm,
      readSrc, State.setReg, Option.map_some, reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left']
    refine ⟨h.base.of_gpr (fun r h1 _ _ => by simp only [h1, ite_false]) rfl rfl rfl rfl
      ⟨pxor_self _, h.base.vp.of_eq rfl rfl, bc_eq _⟩, ?_⟩
    trivial
  show WP isa (.block ((wb .pxor .xmm4 .xmm4 :: scaleInit) ++ _)) s _
  rw [WP.block_append_iff]
  refine key.mono fun s₁ ⟨b₁, _, m₁⟩ => (passStart_wp hp b₁).mono fun s' ⟨b, c, a, _, m⟩ =>
    ⟨b, ?_, a, fun i hi => by rw [m, m₁]; exact h.co i hi, fun i hi => absurd hi (by omega_using [])⟩
  rw [c]; exact (BitVec.add_zero _).symm

/-! ## The frame -/

end VG.Proof.MlKem.X86.Vec

namespace VG.Proof.MlKem.X86.Piece

open VG VG.X86

variable {Pre : State → Prop} {Pub : State → State → Prop}

/-- A frame of `bytes` bytes around `body`. -/
theorem alloc {A B : State → State → Prop} {bytes : Nat} {body : Prog isa}
    (h0 : 0 < bytes) (h1 : bytes < 4096) (h4 : bytes % 4 = 0) (hsp : NoSp body)
    (hn : ∀ s₀ s, Pre s₀ → A s₀ s → bytes ≤ (s.gpr .esp).toNat)
    (E : State → BitVec 32) (hE : ∀ s₀ s, Pre s₀ → A s₀ s → s.gpr .esp = E s₀)
    (hb : Piece Pre Pub (fun s₀ s => ∃ s₁, A s₀ s₁ ∧ s = allocFrame bytes s₁)
      (fun s₀ s₂ => ∀ m u, Frame [below (E s₀) bytes] s₂.mem m →
        B s₀ { freed bytes s₂ with mem := m, unknowns := u }) body) :
    Piece Pre Pub A B (.frame (.alloc bytes) body (.free bytes)) where
  wp _ s h₀ ha := WP.frameAlloc h0 h1 h4 (hn _ _ h₀ ha) hsp
    (WP.mono (hb.wp _ _ h₀ ⟨s, ha, rfl⟩) fun s₂ h m u fl => h m u (by rw [← hE _ _ h₀ ha]; exact fl))
  ct _ _ h₀ h₀' hp := RelCT.frameAlloc
    ((hb.ct _ _ h₀ h₀' hp).mono (fun _ _ ⟨s₁, s₂, ⟨h₁, h₂⟩, e₁, e₂⟩ => ⟨⟨s₁, h₁, e₁⟩, s₂, h₂, e₂⟩)
      fun _ _ h => h)

end VG.Proof.MlKem.X86.Piece

namespace VG.Proof.MlKem.X86.Vec

open VG VG.X86 VG.X86.Lanes VG.Impl.MlKem.X86
open VG.Proof.MlKem VG.Spec.MlKem
open VG.Proof.MlKem.X86.NttLoop (fP sP fA sA aR stkR Pre Pub)
open VG.Proof.MlKem.X86.Piece (sse)

/-- The regions the function writes: `f`, `scratch`, the arguments and the allocation. -/
abbrev Wr (s₀ : State) : List Region :=
  [polyRegion (fA s₀), polyRegion (sA s₀), aR s₀, below (E0 s₀ - 12) 4]

/-- The allocation is within the contract's stack. -/
theorem alloc_sub {s₀ : State} (hp : Pre s₀) {R : Region} (h : (stkR s₀).Disjoint R) :
    (below (E0 s₀ - 12) 4).Disjoint R := by
  intro a h₁ h₂
  refine h a ?_ h₂
  have := hp.sp
  have := (E0 s₀).isLt
  simp only [Region.Contains] at h₁ ⊢
  bv_omega

theorem alloc_mcdt (s₀ : State) (h : 16 ≤ (E0 s₀).toNat) :
    (mcdtR s₀).Disjoint (below (E0 s₀ - 12) 4) ∧ (retR s₀).Disjoint (below (E0 s₀ - 12) 4) := by
  have := h
  refine ⟨?_, ?_⟩ <;>
  · intro a h₁ h₂
    simp only [Region.Contains] at h₁ h₂
    have := (E0 s₀).isLt
    bv_omega

theorem hWr {s₀ : State} (hp : Pre s₀) : ∀ r ∈ Wr s₀, (mcdtR s₀).Disjoint r ∧ (retR s₀).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨mcdt_disj hp hp.stk_f, hp.ret_f⟩
  · exact ⟨mcdt_disj hp hp.stk_s, hp.ret_s⟩
  · exact ⟨mcdt_disj hp hp.stk_a, hp.ret_a⟩
  · exact alloc_mcdt s₀ hp.sp

/-- What the function leaves: the coefficients of `R` at `f`. -/
def FinOk (s₀ : State) (R : Poly) (s : State) : Prop :=
  ∀ i < 256, (coeffAt s.mem (fA s₀) i).toNat = (R[i]!).val

/-- A function that is `body` in `wframe`. -/
theorem wframe_piece {body : Prog isa} {T : List Nat} {VP : (XReg → BitVec 128) → Prop} {G : State → Poly}
    {red : Zq → Zq} (hsp : NoSp body) (hsp' : NoSp (.frame (.alloc 4) body (.free 4)))
    (hb : Piece Pre Pub (fun s₀ s => s = N0 s₀) (fun s₀ s => UInv s₀ T VP (G s₀) red 32 s) body) :
    Piece Pre Pub (fun s₀ s => s = s₀)
      (fun s₀ s' => McdtPost (FinOk s₀ ((G s₀).map red)) s₀ s') (wframe body) := by
  refine Piece.mcdt Wr hsp' (fun _ hp => sp12 hp) (fun _ hp => hWr hp)
    (fun _ _ _ _ hq => hq.1) ?_
  refine Piece.alloc (by decide) (by decide) (by decide) hsp (fun s₀ s hp e => ?_) (fun s₀ => E0 s₀ - 12)
    (fun s₀ s _ e => by rw [e, M0_esp]) (hb.mono (fun s₀ s _ ⟨s₁, e₁, e⟩ => by rw [e, e₁]) fun s₀ s₂ hp h m u fl => ?_)
  · rw [e, M0_esp]; have := hp.sp; bv_omega
  · refine ⟨⟨?_, ?_, ?_, ?_, h.base.mcdt, fun r hr => ?_⟩, fun i hi => ?_⟩
    · exact (h.base.frame.mono fun r hr => List.mem_append_left [below (E0 s₀ - 12) 4] hr).trans
        (fl.mono fun r hr => List.mem_append_right [polyRegion (fA s₀), polyRegion (sA s₀), aR s₀] hr)
    · show (freed 4 s₂).gpr .esp = _
      rw [freed_esp, h.base.esp, allocFrame_esp]
      exact BitVec.sub_add_cancel _ _
    · show s₂.rd = _
      rw [h.base.rd]; rfl
    · show s₂.wr.tail = _
      rw [h.base.wr]; rfl
    · have := h.base.saved r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact (freed_gpr 4 s₂ (by decide)).trans this
    · show (m.readW (coeffAddr (fA s₀) i) 32).toNat = _
      rw [fl.readW (r := polyRegion (fA s₀)) (coeff_contains _ (by rw [n_eq]; exact hi))
        (fun r hr => by rw [List.mem_singleton.mp hr]; exact (alloc_sub hp hp.stk_f).symm) (by decide)]
      rw [show ((G s₀).map red)[i]! = red (G s₀)[i]! by
        rw [getElem!_eq _ (by rw [n_eq]; exact hi), Vector.getElem_map, ← getElem!_eq _ (by rw [n_eq]; exact hi)]]
      exact h.done i (by omega_using [hi])

end VG.Proof.MlKem.X86.Vec

/-! ## `vg_mlkem_ntt` -/

namespace VG.Proof.MlKem.X86.NttFwd

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem VG.Spec.MlKem
open VG.Proof.MlKem.X86.Vec
open VG.Proof.MlKem.X86.NttLoop (fP sP fA sA aR stkR Pre Pub)

theorem pre_of {s₀ : State} {stk : Nat} {t : Poly → Poly}
    (h : (inPlaceContract X86.abi t stk).pre s₀) (hs : stk = 16) : Pre s₀ := by
  subst hs
  sig_pre [inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

theorem montZetas_getD {k : Nat} (hk : k < 128) : montZetas.getD k 0 = (zeta k).val * 65536 % 3329 := by
  have h1 : zetaTable.getD k 0 = (zeta k).val := zetas_getD hk
  rw [← h1, montZetas, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (show k < zetaTable.length by rw [show zetaTable.length = 128 from zetas_length]; exact hk)]
  rfl

theorem tab : TabOK montZetas zeta := fun _ hk => montZetas_getD hk

theorem tab_bound {T : List Nat} {zv : Nat → Zq} (hT : TabOK T zv) : ∀ k < 128, T.getD k 0 < 65536 :=
  fun _ hk => Nat.lt_trans (tab_lt hT hk) (by decide)

section
variable (s₀ : State)
abbrev L1 : Poly := nttLayer (F s₀) 128
abbrev L2 : Poly := nttLayer (L1 s₀) 64
abbrev L3 : Poly := nttLayer (L2 s₀) 32
abbrev L4 : Poly := nttLayer (L3 s₀) 16
abbrev L5 : Poly := nttLayer (L4 s₀) 8
abbrev L6 : Poly := nttLayer (L5 s₀) 4
abbrev L7 : Poly := nttLayer (L6 s₀) 2
end

theorem fold_eq (s₀ : State) : nttLens.foldl nttLayer (F s₀) = L7 s₀ := by
  simp only [nttLens, List.foldl_cons, List.foldl_nil]

theorem vu_keep (f g : XReg → BitVec 128) (h : VU f) (hr : ∀ r, r ≠ .xmm0 → r ≠ .xmm1 → g r = f r) : VU g :=
  (hr _ (by decide) (by decide)).trans h

theorem body_piece : Piece Pre Pub (fun s₀ s => s = N0 s₀)
    (fun s₀ s => UInv s₀ montZetas VU (L7 s₀) id 32 s)
    (.seq (nttInit montZetas) (.seq wpackPass
      (.seq (layer8 (lBody fCore .xmm1) 128) (.seq (layer8 (lBody fCore .xmm1) 64)
        (.seq (layer8 (lBody fCore .xmm1) 32) (.seq (layer8 (lBody fCore .xmm1) 16)
          (.seq (layer8 (lBody fCore .xmm1) 8) (.seq (layerFlat zl4 (body4 fCore .xmm1) 4)
            (.seq (layerFlat zl2 (body2 fCore .xmm1) 8) (wunpackPass [] [])))))))))) := by
  refine Piece.seq (init_piece montZetas (tab_bound tab) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (pack_piece montZetas (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (lay8_piece (lBody_ok fCore_ok) (body_new sh8 sh8_ok fwd_core) tab 16 1 1 (by decide) (by decide)
    F L1 (fun s₀ => fwd_lay _ (by decide) (by decide)) (by taint_decide) (by taint_decide) (by taint_decide)
    (by taint_decide)) ?_
  refine Piece.seq (lay8_piece (lBody_ok fCore_ok) (body_new sh8 sh8_ok fwd_core) tab 8 2 2 (by decide) (by decide)
    L1 L2 (fun s₀ => fwd_lay _ (by decide) (by decide)) (by taint_decide) (by taint_decide) (by taint_decide)
    (by taint_decide)) ?_
  refine Piece.seq (lay8_piece (lBody_ok fCore_ok) (body_new sh8 sh8_ok fwd_core) tab 4 4 4 (by decide) (by decide)
    L2 L3 (fun s₀ => fwd_lay _ (by decide) (by decide)) (by taint_decide) (by taint_decide) (by taint_decide)
    (by taint_decide)) ?_
  refine Piece.seq (lay8_piece (lBody_ok fCore_ok) (body_new sh8 sh8_ok fwd_core) tab 2 8 8 (by decide) (by decide)
    L3 L4 (fun s₀ => fwd_lay _ (by decide) (by decide)) (by taint_decide) (by taint_decide) (by taint_decide)
    (by taint_decide)) ?_
  refine Piece.seq (lay8_piece (lBody_ok fCore_ok) (body_new sh8 sh8_ok fwd_core) tab 1 16 16 (by decide)
    (by decide) L4 L5 (fun s₀ => fwd_lay _ (by decide) (by decide)) (by taint_decide) (by taint_decide)
    (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (layFlat_piece flat4 (by decide) zl4_ok (body4_ok (.inr rfl) fCore_ok)
    (body_new sh4 sh4_ok fwd_core) tab 32 (by decide) L5 L6 (fun s₀ => fwd_lay _ (by decide) (by decide))
    (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (layFlat_piece flat2 (by decide) zl2_ok (body2_ok (.inr rfl) fCore_ok)
    (body_new sh2 sh2_ok fwd_core) tab 64 (by decide) L6 L7 (fun s₀ => fwd_lay _ (by decide) (by decide))
    (by taint_decide) (by taint_decide)) ?_
  exact unpack_piece nil_ok (fun _ h => h) vu_keep id_lanes L7 128 (fun _ _ hp h => uinitF_wp hp h)
    (by taint_decide) (by taint_decide)

theorem piece : Piece Pre Pub (fun s₀ s => s = s₀)
    (fun s₀ s' => McdtPost (FinOk s₀ ((L7 s₀).map id)) s₀ s') Impl.MlKem.X86.ntt :=
  wframe_piece (NoSp.of_all (by lit_decide)) (NoSp.of_all (by lit_decide)) body_piece

/-- Memory with the arguments `0` and `0x400` at `0x5004`. -/
def satMem : Mem := fun a => if a = 0x5009 then 4 else 0

theorem satZero (a : Addr) (ha : a.toNat < 0x5000) : satMem a = 0 := by
  simp only [satMem]
  rw [ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega_using [ha])]

theorem sat {t : Poly → Poly} : ∃ s, (inPlaceContract X86.abi t 16).pre s := by
  let st := satState satMem [] [⟨0, 1024⟩, ⟨0x400, 1024⟩, ⟨0x5004, 8⟩]
  have a0 : arg st 0 = 0 := by decide
  have a1 : arg st 1 = 0x400 := by decide
  have e : argAddr st 0 = 0x5004 := by decide
  refine ⟨st, ?_⟩
  sig_pre [inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  simp only [a0, a1, e]
  refine ⟨by decide, by decide, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide,
    reduced_below satZero 0 (by decide)⟩
  all_goals exact Region.disjoint_of_sep (by decide)

theorem verified : Verified X86.target Impl.MlKem.X86.ntt (nttContract X86.abi 16) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => pre_of (t := VG.Spec.MlKem.ntt) h rfl)
    fun s s' _ _ h => by
      sig_pub [nttContract, inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) sat
  obtain ⟨habi, -, -, s, hinv, hm⟩ := hq
  refine ⟨habi, ?_⟩
  sig_post [nttContract, inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  have hp := pre_of (t := VG.Spec.MlKem.ntt) h₀ rfl
  refine polyIs_frame hm (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact (mcdt_disj hp hp.stk_f).symm) ?_
  refine polyIs_of_toNat fun i hi => ?_
  rw [ntt_eq_layers]
  show _ = ((nttLens.foldl nttLayer (F s₀))[i]!).val
  rw [fold_eq]
  have := hinv i hi
  rwa [Vector.map_id] at this

end VG.Proof.MlKem.X86.NttFwd

/-! ## `vg_mlkem_inv_ntt` -/

namespace VG.Proof.MlKem.X86.NttInvP

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem VG.Spec.MlKem
open VG.Proof.MlKem.X86.Vec
open VG.Proof.MlKem.X86.NttLoop (fP sP fA sA aR stkR Pre Pub)
open VG.Proof.MlKem.X86.NttFwd (pre_of montZetas_getD tab_bound sat)

theorem getD_map_range {f : Nat → Nat} {n k : Nat} (hk : k < n) : ((List.range n).map f).getD k 0 = f k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk, Option.map_some, Option.getD_some]

theorem tab : TabOK montZetasRev zvI := fun k hk => by
  rw [montZetasRev, getD_map_range hk, montZetas_getD (Nat.mod_lt _ (by decide))]; rfl

section
variable (s₀ : State)
abbrev I1 : Poly := nttInvLayer (F s₀) 2
abbrev I2 : Poly := nttInvLayer (I1 s₀) 4
abbrev I3 : Poly := nttInvLayer (I2 s₀) 8
abbrev I4 : Poly := nttInvLayer (I3 s₀) 16
abbrev I5 : Poly := nttInvLayer (I4 s₀) 32
abbrev I6 : Poly := nttInvLayer (I5 s₀) 64
abbrev I7 : Poly := nttInvLayer (I6 s₀) 128
end

theorem fold_eq (s₀ : State) : nttInvLens.foldl nttInvLayer (F s₀) = I7 s₀ := by
  simp only [nttInvLens, List.foldl_cons, List.foldl_nil]

theorem vs_keep (f g : XReg → BitVec 128) (h : VS f) (hr : ∀ r, r ≠ .xmm0 → r ≠ .xmm1 → g r = f r) : VS g :=
  ⟨(hr _ (by decide) (by decide)).trans h.zero,
    h.vk.of_eq (hr _ (by decide) (by decide)) (hr _ (by decide) (by decide)),
    (hr _ (by decide) (by decide)).trans h.sc⟩

theorem body_piece : Piece Pre Pub (fun s₀ s => s = N0 s₀)
    (fun s₀ s => UInv s₀ montZetasRev VS (I7 s₀) (· * 3303) 32 s)
    (.seq (nttInit montZetasRev) (.seq wpackPass
      (.seq (layerFlat zl2 (body2 iCore .xmm0) 8) (.seq (layerFlat zl4 (body4 iCore .xmm0) 4)
        (.seq (layer8 (lBody iCore .xmm0) 8) (.seq (layer8 (lBody iCore .xmm0) 16)
          (.seq (layer8 (lBody iCore .xmm0) 32) (.seq (layer8 (lBody iCore .xmm0) 64)
            (.seq (layer8 (lBody iCore .xmm0) 128) (wunpackPass scaleInit scaleCore)))))))))) := by
  refine Piece.seq (init_piece montZetasRev (tab_bound tab) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (pack_piece montZetasRev (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (layFlat_piece flat2 (by decide) zl2_ok (body2_ok (.inl rfl) iCore_ok)
    (body_new sh2 sh2_ok inv_core) tab 1 (by decide) F I1
    (fun s₀ => inv_lay _ (by decide) (by decide) (by decide) (by decide)) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (layFlat_piece flat4 (by decide) zl4_ok (body4_ok (.inl rfl) iCore_ok)
    (body_new sh4 sh4_ok inv_core) tab 65 (by decide) I1 I2
    (fun s₀ => inv_lay _ (by decide) (by decide) (by decide) (by decide)) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (lay8_piece (lBody_ok iCore_ok) (body_new sh8 sh8_ok inv_core) tab 1 16 97 (by decide)
    (by decide) I2 I3 (fun s₀ => inv_lay _ (by decide) (by decide) (by decide) (by decide)) (by taint_decide)
    (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (lay8_piece (lBody_ok iCore_ok) (body_new sh8 sh8_ok inv_core) tab 2 8 113 (by decide)
    (by decide) I3 I4 (fun s₀ => inv_lay _ (by decide) (by decide) (by decide) (by decide)) (by taint_decide)
    (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (lay8_piece (lBody_ok iCore_ok) (body_new sh8 sh8_ok inv_core) tab 4 4 121 (by decide)
    (by decide) I4 I5 (fun s₀ => inv_lay _ (by decide) (by decide) (by decide) (by decide)) (by taint_decide)
    (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (lay8_piece (lBody_ok iCore_ok) (body_new sh8 sh8_ok inv_core) tab 8 2 125 (by decide)
    (by decide) I5 I6 (fun s₀ => inv_lay _ (by decide) (by decide) (by decide) (by decide)) (by taint_decide)
    (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (lay8_piece (lBody_ok iCore_ok) (body_new sh8 sh8_ok inv_core) tab 16 1 127 (by decide)
    (by decide) I6 I7 (fun s₀ => inv_lay _ (by decide) (by decide) (by decide) (by decide)) (by taint_decide)
    (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  exact unpack_piece scaleCore_ok (fun _ h => h.zero) vs_keep scale_lanes I7 128 (fun _ _ hp h => uinitI_wp hp h)
    (by taint_decide) (by taint_decide)

theorem piece : Piece Pre Pub (fun s₀ s => s = s₀)
    (fun s₀ s' => McdtPost (FinOk s₀ ((I7 s₀).map (· * 3303))) s₀ s') Impl.MlKem.X86.nttInv :=
  wframe_piece (NoSp.of_all (by lit_decide)) (NoSp.of_all (by lit_decide)) body_piece

theorem verified : Verified X86.target Impl.MlKem.X86.nttInv (nttInvContract X86.abi 16) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => pre_of (t := VG.Spec.MlKem.nttInv) h rfl)
    fun s s' _ _ h => by
      sig_pub [nttInvContract, inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) sat
  obtain ⟨habi, -, -, s, hinv, hm⟩ := hq
  refine ⟨habi, ?_⟩
  sig_post [nttInvContract, inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  have hp := pre_of (t := VG.Spec.MlKem.nttInv) h₀ rfl
  refine polyIs_frame hm (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact (mcdt_disj hp hp.stk_f).symm) ?_
  refine polyIs_of_toNat fun i hi => ?_
  rw [nttInv_eq_layers]
  show _ = (((nttInvLens.foldl nttInvLayer (F s₀)).map (· * 3303))[i]!).val
  rw [fold_eq]
  exact hinv i hi

end VG.Proof.MlKem.X86.NttInvP
