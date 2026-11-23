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


/-! ## The function's memory -/

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
    rw [State.ea, at_, heax, ea_add (by omega_using [fs, hu]), Nat.add_zero]
  have eP' : s.ea (at_ .eax d) = sA s₀ + BitVec.ofNat 64 (16 * (32 + u')) := by
    rw [State.ea, at_, heax, ea_add (by omega_using [fs, hu', hd])]
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

end VG.Proof.MlKem.X86.Vec
