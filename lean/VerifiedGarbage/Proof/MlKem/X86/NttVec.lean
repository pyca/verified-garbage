module

public import VerifiedGarbage.Proof.MlKem.X86.VLanes
public import VerifiedGarbage.Proof.MlKem.X86.Table
public import VerifiedGarbage.Proof.MlKem.NttLayer
public import VerifiedGarbage.Proof.MlDsa.X86.Arith.Mcdt
public import VerifiedGarbage.Impl.MlKem.X86.NttV
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.SseWord
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.X86.VLanes
meta import VerifiedGarbage.Proof.MlKem.X86.Table
meta import VerifiedGarbage.Proof.MlKem.NttLayer
meta import VerifiedGarbage.Proof.MlDsa.X86.Arith.Mcdt
meta import VerifiedGarbage.Impl.MlKem.X86.NttV
meta import VerifiedGarbage.Proof.Framework.X86.AllocFrame
meta import VerifiedGarbage.Proof.Framework.X86.Sse
meta import VerifiedGarbage.Proof.Framework.X86.SseDword
meta import VerifiedGarbage.Proof.Framework.X86.SseWord
meta import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
meta import VerifiedGarbage.Proof.Framework.X86.Wp
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

@[expose] public section

namespace VG.Proof.MlKem.X86.Vec

open VG VG.X86 VG.X86.Lanes VG.Impl.MlKem.X86
open VG.Proof.MlKem VG.Spec.MlKem
open VG.Proof.MlKem.X86.NttLoop (fP sP fA sA aR stkR Pre Pub)
open VG.Proof.MlDsa.X86.Arith (M0 mcdtR McdtEnd McdtPost M0_esp M0_wr M0_rd M0_frame ret_mcdt)
open VG.Proof.MlDsa.X86.Arith.Piece (sse)

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

end VG.Proof.MlKem.X86.Vec
