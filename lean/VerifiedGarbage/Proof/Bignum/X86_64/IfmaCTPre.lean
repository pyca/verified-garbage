import VerifiedGarbage.Proof.Bignum.X86_64.IfmaPre
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTQ
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTPSub

/-!
# RSA with AVX512_IFMA on x86-64: constant time, before the vector code

`pre` is `gPow`, copies, and for each prime `prepCode`, whose pieces
(`redc`, copies, Montgomery multiplications, and the blocks entering and
leaving the prime's workspace) are constant time: so is `prepCode`
(`prep_ct`), for `prep_ok`'s hypotheses, and `pre` (`pre_ct`), for
`pre_ok`'s. Before each piece, a predicate carries the piece's claim's
hypotheses and what correctness gives after it (`prep_chain`, `pre_chain`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64 CrtCTQ

/-! ## `prepCode` -/

/-- `prep_ok`'s hypotheses, with the public data `p` (`n`'s workspace and
`-n⁻¹`, `n`, and the prime's workspace). -/
def PrepPre (sl : Nat) (p : UPub) (s : State) : Prop :=
  ∃ (mx : BitVec 64) (X : Nat), Good s p.B p.Z p.w p.minv ∧ p.w < 2 ^ 28 ∧ slot p.w 8 ≤ p.o ∧
    p.o + slot p.wx 8 + tabBytes p.wx ≤ p.Z ∧ 2 ≤ p.wx ∧ p.wx ≤ p.w ∧ sl < 32 ∧ sl ≠ Crt.sD ∧ sl ≠ Public.sCnt ∧
    word s.mem p.B (8 * sl) = off p.B p.o ∧ WsAt s.mem p.B p.o p.wx mx ∧ NVals s p.B p.w p.minv p.N ∧
    XVals s p.B p.o p.wx mx X ∧ 1 < X ∧ wv s.mem p.B (slot p.w Public.aY) p.w < p.N

/-- `n`'s workspace. -/
abbrev UPub.nw (p : UPub) : Ws := ⟨p.B, p.Z, p.w⟩

/-- After the second `redc`: in the prime's workspace. -/
def PP5 (p : UPub) (s : State) : Prop := s.gpr .rdi = off p.B p.o

/-- Before the second `redc`. -/
def PP4 (M : Mont) (p : UPub) (s : State) : Prop :=
  RPre Public.aY (xp p) s ∧ WP isa (seqs (redc M.mm Public.aY)) s (PP5 p)

/-- Before entering the prime's workspace again. -/
def PP3 (M : Mont) (sl : Nat) (p : UPub) (s : State) : Prop :=
  s.gpr .rdi = p.B ∧ WP isa (.block [.mov .rdi (.mem (hdr sl))]) s (PP4 M p)

/-- Before `aY := x G`. -/
def PP2 (M : Mont) (sl : Nat) (p : UPub) (s : State) : Prop :=
  GoodW p.nw s ∧ WP isa (M.mm Public.aY Public.aXm Public.aY) s (PP3 M sl p)

/-- Before the first `redc`. -/
def PP1 (M : Mont) (sl : Nat) (p : UPub) (s : State) : Prop :=
  RPre Public.aY (xp p) s ∧
    WP isa (seqs (redc M.mm Public.aY ++ (copyArr Public.aY aXc ++ ([.block [leave]] : List (Prog isa)))))
      s (PP2 M sl p)

/-- Before `prepCode`. -/
def PP0 (M : Mont) (sl : Nat) (p : UPub) (s : State) : Prop :=
  s.gpr .rdi = p.B ∧ WP isa (.block [.mov .rdi (.mem (hdr sl))]) s (PP1 M sl p)

theorem prepCode_eq (mul : Nat → Nat → Nat → Prog isa) (sl : Nat) :
    prepCode mul sl = ([.block [.mov .rdi (.mem (hdr sl))]] : List (Prog isa)) ++
      ((redc mul Public.aY ++ (copyArr Public.aY aXc ++ ([.block [leave]] : List (Prog isa)))) ++
        ([mul Public.aY Public.aXm Public.aY] ++ (([.block [.mov .rdi (.mem (hdr sl))]] : List (Prog isa)) ++
          (redc mul Public.aY ++ ([.block [leave]] : List (Prog isa)))))) := by
  simp only [prepCode, List.append_assoc]

/-- Entering the prime's workspace, from `n`'s. -/
theorem enter_rpre {s : State} {p : UPub} {sl : Nat} {mx : BitVec 64} {X : Nat} (hg : Good s p.B p.Z p.w p.minv)
    (hw28 : p.w < 2 ^ 28) (hlo : slot p.w 8 ≤ p.o) (hhi : p.o + slot p.wx 8 + tabBytes p.wx ≤ p.Z)
    (hwx2 : 2 ≤ p.wx) (hwx : p.wx ≤ p.w) (hsl : sl < 32) (hslv : word s.mem p.B (8 * sl) = off p.B p.o)
    (hws : WsAt s.mem p.B p.o p.wx mx) (hX : XVals s p.B p.o p.wx mx X) (hX1 : 1 < X) :
    WP isa (.block [.mov .rdi (.mem (hdr sl))]) s fun t =>
      RPre Public.aY (xp p) t ∧ SubCtx t p.B p.Z p.o p.w p.wx mx ∧ XVals t p.B p.o p.wx mx X ∧ t.mem = s.mem ∧
        Keep [.rdi] s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = off p.B p.o ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hs.ld (d := 8 * sl) (by omega), hslv]) rfl)
    fun t ⟨⟨hdi, hm⟩, k⟩ => ?_
  have hc : SubCtx t p.B p.Z p.o p.w p.wx mx :=
    SubCtx.mk' (hs.congr k.2.2) (by rw [hm]; exact hg.hdr) (by rw [hm]; exact hws) hdi hlo hhi
  have hX' : XVals t p.B p.o p.wx mx X := by
    rw [show t = { t with mem := s.mem } by rw [← hm]]; exact ⟨hX.n, hX.inv, hX.one⟩
  exact ⟨⟨mx, X, hc, hX', hwx2, hwx, show p.w < 2 ^ 30 by omega, hX1, by decide⟩, hc, hX', hm, k⟩

/-- `prep_ok`'s hypotheses give `PP0`, as `prep_ok` runs the pieces. -/
theorem prep_chain (M : Mont) {sl : Nat} {p : UPub} {s : State} (h : PrepPre sl p s) : PP0 M sl p s := by
  obtain ⟨mx, X, hg, hw28, hlo, hhi, hwx2, hwx, hsl, hsl1, hsl2, hslv, hws, hN, hX, hX1, hYl⟩ := h
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot p.wx 8 := by unfold slot hdrBytes; omega
  have ho64 : p.o < 2 ^ 64 := by omega
  have hoL : p.o + slot p.wx 8 ≤ 2 ^ 64 := by omega
  have hz : p.B.toNat + slot p.w 8 ≤ 2 ^ 64 := by omega
  have hgr := gRanges_le p.w
  -- Into the prime's workspace.
  refine ⟨hg.rdi, WP.mono (enter_rpre hg hw28 hlo hhi hwx2 hwx hsl hslv hws hX hX1)
    fun s₁ ⟨hr₁, hc₁, hX₁, hm₁, k₁⟩ => ⟨hr₁, ?_⟩⟩
  -- `aXc := G R^-K`, `aY := aXc`, and back.
  refine wp_seqs_append (by simp [redc]) (by simp [copyArr]) (WP.mono (redc_ok M hc₁ hX₁ hwx2 hwx (by omega) hX1
    (j := Public.aY) (by decide)) fun s₂ ⟨hc₂, hX₂, _, _, f₂, k₂⟩ => ?_)
  refine wp_seqs_append (by simp [copyArr]) (by simp) (WP.mono (copyArr_ok hc₂.good (Nat.le_refl _) (by omega)
    (by omega) (o := Public.aY) (a := aXc) (by decide) (by decide) (by decide)) fun s₃ ⟨_, ho₃, k₃⟩ => ?_)
  have hc₃ := hc₂.of_frm (rs := [(slot p.wx Public.aY, 8 * p.wx)]) (Frm.of_outside ho₃ (by simp)) (fun r hr => by
    rw [List.mem_singleton.mp hr]
    have := slot_le (w := p.wx) (show Public.aY < 8 by decide)
    have := hdr_lt_slot p.wx Public.aY (show 31 < 32 by decide)
    simp only; omega) k₃.2.2 (k₃.gpr (by decide))
  have hX₃ : XVals s₃ p.B p.o p.wx mx X := hX₂.of_outside ho₃ (by decide) (by decide) (by decide) (by omega)
    (by have := hc₂.good.scr.nowrap; omega)
  have f03 : Frm p.B [xRange p.o p.wx] s.mem s₃.mem := by
    rw [← hm₁]
    exact (f₂.to_x (redcRanges_ok _) hoL (List.mem_singleton_self _)).trans
      (ho₃.mono (o' := slot p.wx Public.aY) (n' := 8 * (p.wx + 2)) (Nat.le_refl _) (by omega) |>.to_x
        (by decide) hoL (List.mem_singleton_self _))
  refine WP.mono (leaveBack_ok hg hc₃ f03 hlo) fun s₄ ⟨hg₄, hm₄, k₄⟩ => ⟨⟨_, hg₄, show slot p.w 8 ≤ p.Z by omega⟩, ?_⟩
  have f04 : Frm p.B (gRanges p.w ++ [xRange p.o p.wx]) s.mem s₄.mem := by
    rw [hm₄]; exact f03.mono fun r hr => List.mem_append_right _ hr
  have hN₄ := hN.of_frm f04 hlo hz (by omega)
  have hY₄ : wv s₄.mem p.B (slot p.w Public.aY) p.w = wv s.mem p.B (slot p.w Public.aY) p.w := by
    rw [hm₄]; exact wv_congr fun i hi => f03.x_below
      (by have := slot_le (w := p.w) (show Public.aY < 8 by decide); omega) ho64
  -- `aY := x G` in `n`'s workspace.
  refine WP.mono (mmY_ok M hg₄ (by omega) (by omega) (by omega) (a := Public.aXm) (by decide) (by decide)
    (by decide) hN₄ (by rw [hY₄]; exact hYl)) fun s₅ ⟨hg₅, _, _, f₅, _⟩ => ⟨hg₅.rdi, ?_⟩
  have hxo : ∀ i < 32, word s₅.mem (off p.B p.o) (8 * i) = word s₄.mem (off p.B p.o) (8 * i) := fun i hi => by
    rw [word_off, word_off]
    exact f₅.word_eq (fun r hr => Or.inr (by have := hgr r hr; omega)) (by omega)
  have hb₅ : word s₅.mem p.B (8 * sl) = off p.B p.o := by
    rw [f₅.word_eq (fun r hr => by
      have := hdr_lt_slot p.w Public.aAcc (show sl < 32 from hsl)
      have := hdr_lt_slot p.w Public.aTmp (show sl < 32 from hsl)
      have := hdr_lt_slot p.w Public.aY (show sl < 32 from hsl)
      simp only [gRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact Or.inl (by omega)
      · exact Or.inl (by omega)
      · exact Or.inl (by omega)
      · show 8 * sl + 8 ≤ 8 * Crt.sD ∨ 8 * Crt.sD + 8 ≤ 8 * sl
        unfold Crt.sD sFn at hsl1 ⊢; omega
      · show 8 * sl + 8 ≤ 8 * Public.sCnt ∨ 8 * Public.sCnt + 8 ≤ 8 * sl
        unfold Public.sCnt sFn at hsl2 ⊢; omega) (by omega)]
    rw [hm₄]; exact (f03.x_below (by have := hdr_lt_slot p.w 8 hsl; omega) ho64).trans hslv
  have hws₅ : WsAt s₅.mem p.B p.o p.wx mx := (by rw [hm₄]; exact hc₃.ws : WsAt s₄.mem p.B p.o p.wx mx).of_words
    fun i hi => hxo i (by omega)
  have hX₅ : XVals s₅ p.B p.o p.wx mx X := (show XVals s₄ p.B p.o p.wx mx X from by
    rw [show s₄ = { s₄ with mem := s₃.mem } by rw [← hm₄]]; exact ⟨hX₃.n, hX₃.inv, hX₃.one⟩).of_below f₅
    (fun r hr => (hgr r hr).trans hlo) hoL
  -- Into the prime's workspace again, and `aXc := x G R^-K`.
  refine WP.mono (enter_rpre hg₅ hw28 hlo hhi hwx2 hwx hsl hb₅ hws₅ hX₅ hX1) fun s₆ ⟨hr₆, hc₆, hX₆, _⟩ =>
    ⟨hr₆, WP.mono (redc_ok M hc₆ hX₆ hwx2 hwx (by omega) hX1 (j := Public.aY) (by decide)) fun _ ⟨hc₇, _⟩ =>
      hc₇.rdi⟩

/-- `prepCode` is constant time. -/
theorem prep_ct (M : Mont) (sl : Nat) (hR : RedcCT M Public.aY) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rdi (.mem (hdr sl))]) hc).isSome = true) :
    RelCT isa (Two (PrepPre sl)) (seqs (prepCode M.mm sl)) fun _ _ => True := by
  refine two_map id (fun _ _ h => prep_chain M h) ?_
  rw [prepCode_eq]
  refine RelCT.seqs_app (by simp) (by simp [redc]) (ct_taint [.rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1, h₂.1]) hT (fun _ _ h => h.2) ?_)
  refine ct_steps (by simp [redc]) (by simp) xp (fun _ _ h => h.1) (fun _ _ h => h.2) (redcCopy_ct M hR) ?_
  refine ct_steps (by simp) (by simp) UPub.nw (fun _ _ h => h.1) (fun _ _ h => h.2)
    (M.ct (by unfold MmUse; decide)) ?_
  refine RelCT.seqs_app (by simp) (by simp [redc]) (ct_taint [.rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1, h₂.1]) hT (fun _ _ h => h.2) ?_)
  exact ct_steps (by simp [redc]) (by simp) xp (fun _ _ h => h.1) (fun _ _ h => h.2) hR
    (two_taint [.rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [show s₁.gpr .rdi = _ from h₁, h₂]) (by taint_decide))

/-! ## `pre` -/

/-- The public data of `pre`: `n`'s workspace, `-n⁻¹`, `n`, and the primes'
workspaces (both of `wp` words). -/
structure PrePub where
  B : Addr
  Z : Nat
  w : Nat
  minv : BitVec 64
  N : Nat
  op : Nat
  oq : Nat
  wp : Nat

abbrev PrePub.nw (p : PrePub) : Ws := ⟨p.B, p.Z, p.w⟩
abbrev PrePub.uq (p : PrePub) : UPub := ⟨p.B, p.Z, p.w, p.minv, p.N, p.oq, p.wp⟩
abbrev PrePub.up (p : PrePub) : UPub := ⟨p.B, p.Z, p.w, p.minv, p.N, p.op, p.wp⟩

/-- `pre_ok`'s hypotheses. -/
def PrePre (p : PrePub) (s : State) : Prop :=
  ∃ (mp mq : BitVec 64) (P Q C : Nat), Good s p.B p.Z p.w p.minv ∧ 8 ≤ p.w ∧ p.w < 2 ^ 28 ∧ slot p.w 8 ≤ p.op ∧
    p.op + slot p.wp 8 + tabBytes p.wp ≤ p.oq ∧ p.oq + slot p.wp 8 + tabBytes p.wp ≤ p.Z ∧ 2 ≤ p.wp ∧
    p.wp ≤ p.w ∧ word s.mem p.B (8 * sWsP) = off p.B p.op ∧ word s.mem p.B (8 * sWsQ) = off p.B p.oq ∧
    WsAt s.mem p.B p.op p.wp mp ∧ WsAt s.mem p.B p.oq p.wp mq ∧ NVals s p.B p.w p.minv p.N ∧ p.N % 2 = 1 ∧
    1 < p.N ∧ wv s.mem p.B (slot p.w Public.aXm) p.w % p.N = C * 2 ^ (64 * p.w) % p.N ∧
    XVals s p.B p.op p.wp mp P ∧ 1 < P ∧ P % 2 = 1 ∧ XVals s p.B p.oq p.wp mq Q ∧ 1 < Q ∧ Q % 2 = 1

/-- Before `p`'s `prepCode`. -/
def PR4 (p : PrePub) (s : State) : Prop := PrepPre sWsP p.up s

/-- Before `aY := G` again. -/
def PR3 (p : PrePub) (s : State) : Prop :=
  GoodW p.nw s ∧ WP isa (seqs (copyArr Public.aY Public.aX)) s (PR4 p)

/-- Before `q`'s `prepCode`. -/
def PR2 (M : Mont) (p : PrePub) (s : State) : Prop :=
  PrepPre sWsQ p.uq s ∧ WP isa (seqs (prepCode M.mm sWsQ)) s (PR3 p)

/-- Before `aX := G`. -/
def PR1 (M : Mont) (p : PrePub) (s : State) : Prop :=
  GoodW p.nw s ∧ WP isa (seqs (copyArr Public.aX Public.aY)) s (PR2 M p)

/-- Before `pre`. -/
def PR0 (M : Mont) (p : PrePub) (s : State) : Prop :=
  GPre sWsQ (gp p.uq) s ∧ WP isa (seqs (Crt.gPow M.mm sWsQ)) s (PR1 M p)

/-- `pre_ok`'s hypotheses give `PR0`, as `pre_ok` runs the pieces. -/
theorem pre_chain (M : Mont) {p : PrePub} {s : State} (h : PrePre p s) : PR0 M p s := by
  obtain ⟨B, Z, w, minv, N, op, oq, wp⟩ := p
  dsimp only [PrePre] at h
  obtain ⟨mp, mq, P, Q, C, hg, hw, hw28, hlo, hpq, hoq, hwp2, hwp, hsp, hsq, hwsp, hwsq, hN, hodd, hN1, hXm, hP,
    hP1, hPodd, hQ, hQ1, hQodd⟩ := h
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot wp 8 := by unfold slot hdrBytes; omega
  have hz : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega
  have lX := slot_le (w := w) (show Public.aX < 8 by decide)
  have lY := slot_le (w := w) (show Public.aY < 8 by decide)
  have lM := slot_le (w := w) (show Public.aXm < 8 by decide)
  have sXY := slot_sep (w := w) (show Public.aX ≠ Public.aY by decide)
  have sXM := slot_sep (w := w) (show Public.aX ≠ Public.aXm by decide)
  have sYM := slot_sep (w := w) (show Public.aY ≠ Public.aXm by decide)
  have hXh := hdr_lt_slot w Public.aX (show 31 < 32 by decide)
  have hYh := hdr_lt_slot w Public.aY (show sWsP < 32 by decide)
  have hgl := gRanges_lt w
  have hsW : InRegions (s.rd ++ s.wr) (off (off B oq) (8 * sW)) 8 :=
    (hs.sub (o := oq) (n := slot wp 8) (by omega) (by omega)).ld (d := 8 * sW) (by unfold sW; omega)
  -- `G` into `aY`.
  refine ⟨by dsimp only [GPre, gp, PrePub.uq]; exact ⟨hg, by omega, by omega, by omega, hN.n, hN.inv, hodd, hN1,
    hN.r2, hN.one, by decide, hsq, hwsq.hdr.hw, hsW, by omega, hwp⟩, WP.mono (gPow_ok M hg (by omega) (by omega) (by omega) hN.n hN.inv hodd hN1 hN.r2 hN.one
      (sl := sWsQ) (by decide) hsq hwsq.hdr.hw hsW (by omega) hwp) fun s₁ ⟨hg₁, hlt₁, hG₁, f₁, k₁⟩ => ?_⟩
  have f₁' : Frm B (gRanges w) s.mem s₁.mem := f₁
  -- `aX := G`.
  refine ⟨⟨minv, hg₁, show slot w 8 ≤ Z by omega⟩, WP.mono (copyArr_ok hg₁ (by omega) (by omega) (by omega)
    (o := Public.aX) (a := Public.aY) (by decide) (by decide) (by decide)) fun s₂ ⟨hv₂, ho₂, k₂⟩ => ?_⟩
  have hY₂ : wv s₂.mem B (slot w Public.aY) w = wv s₁.mem B (slot w Public.aY) w := ho₂.wv (by omega) (by omega)
  have hg₂ := hg₁.of_outsideArr ho₂ k₂
  have hN₂ : NVals s₂ B w minv N := (hN.of_frm (f₁'.mono fun r hr => List.mem_append_left _ hr :
    Frm B (gRanges w ++ [xRange oq wp]) s.mem s₁.mem) (by omega) hz (by omega)).of_outsideArr ho₂ (by decide)
    (by decide) (by decide) (by decide) (by omega) hz
  have fA : Frm B (gRanges w ++ [(slot w Public.aX, 8 * (w + 2))]) s.mem s₂.mem :=
    (f₁'.mono fun r hr => List.mem_append_left _ hr).trans
      (Frm.of_outside (ho₂.mono (o' := slot w Public.aX) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega)) (by simp))
  have hA : ∀ r ∈ gRanges w ++ [(slot w Public.aX, 8 * (w + 2))], r.1 + r.2 ≤ slot w 8 := fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact (hgl r hr).2
    · rw [List.mem_singleton.mp hr]; simp only; omega
  have hAd : ∀ {o}, slot w 8 ≤ o → ∀ r ∈ gRanges w ++ [(slot w Public.aX, 8 * (w + 2))],
      r.1 + r.2 ≤ o ∨ o + slot wp 8 ≤ r.1 := fun ho r hr => .inl (by have := hA r hr; omega)
  have hsq₂ : word s₂.mem B (8 * sWsQ) = off B oq := by
    rw [gRanges_hdr fA (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [hdrBytes]; omega) (by decide)
      (by decide) (by decide) (by unfold sWsQ sFn; omega)]; exact hsq
  have hsp₂ : word s₂.mem B (8 * sWsP) = off B op := by
    rw [gRanges_hdr fA (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [hdrBytes]; omega) (by decide)
      (by decide) (by decide) (by unfold sWsP sFn; omega)]; exact hsp
  have hXm₂ : wv s₂.mem B (slot w Public.aXm) w % N = C * 2 ^ (64 * w) % N := by
    rw [gRanges_arr fA (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega) (by decide)
      (by decide) (by decide) (by decide) (by omega)]; exact hXm
  have hwsq₂ := hwsq.of_disj fA (fun r hr => by rcases hAd (o := oq) (by omega) r hr with h | h <;> omega) (by omega)
  have hQ₂ := hQ.of_disj fA (hAd (by omega)) (by omega)
  -- `q`.
  refine ⟨by dsimp only [PrepPre, PrePub.uq]; exact ⟨mq, Q, hg₂, hw28, by omega, hoq, hwp2, hwp, by decide, by decide, by decide, hsq₂, hwsq₂, hN₂, hQ₂, hQ1,
    by rw [hY₂]; exact hlt₁⟩, WP.mono (prep_ok (C := C) M hg₂ hw hw28 (by omega) hoq hwp2 hwp (by decide) (by decide)
      (by decide) hsq₂ hwsq₂ hN₂ hodd hXm₂ hQ₂ hQ1 hQodd (by rw [hY₂]; exact hlt₁) (by rw [hY₂]; exact hG₁))
    fun s₃ ⟨hg₃, _, _, _, _, _, _, hN₃, fQ, k₃, _⟩ => ?_⟩
  have hQd : ∀ r ∈ gRanges w ++ [xRange oq wp], r.1 + r.2 ≤ op ∨ op + slot wp 8 ≤ r.1 := fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact .inl (by have := (hgl r hr).2; omega)
    · rw [List.mem_singleton.mp hr]; exact .inr (by simp only [xRange]; omega)
  have hsp₃ : word s₃.mem B (8 * sWsP) = off B op := by
    rw [gRanges_hdr fQ (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [xRange, hdrBytes]; omega)
      (by decide) (by decide) (by decide) (by unfold sWsP sFn; omega)]; exact hsp₂
  have hX₃ : wv s₃.mem B (slot w Public.aX) w = wv s₂.mem B (slot w Public.aX) w :=
    gRanges_arr fQ (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (by simp only [xRange]; omega))
      (by decide) (by decide) (by decide) (by decide) (by omega)
  have hwsp₃ := (hwsp.of_disj fA (fun r hr => by rcases hAd (o := op) (by omega) r hr with h | h <;> omega)
    (by omega)).of_disj fQ (fun r hr => by rcases hQd r hr with h | h <;> omega) (by omega)
  have hP₃ := (hP.of_disj fA (hAd (o := op) (by omega)) (by omega)).of_disj fQ hQd (by omega)
  -- `aY := G` again.
  refine ⟨⟨minv, hg₃, show slot w 8 ≤ Z by omega⟩, WP.mono (copyArr_ok hg₃ (by omega) (by omega) (by omega)
    (o := Public.aY) (a := Public.aX) (by decide) (by decide) (by decide)) fun s₄ ⟨hv₄, ho₄, k₄⟩ => ?_⟩
  have fo₄ : Frm B (gRanges w) s₃.mem s₄.mem :=
    Frm.of_outside (ho₄.mono (o' := slot w Public.aY) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega))
      (by simp [gRanges])
  have hr₄ : ∀ r ∈ gRanges w, r.1 + r.2 ≤ op ∨ op + slot wp 8 ≤ r.1 := fun r hr =>
    .inl (by have := (gRanges_lt w r hr).2; omega)
  dsimp only [PR4, PrepPre, PrePub.up]
  exact ⟨mp, P, hg₃.of_outsideArr ho₄ k₄, hw28, hlo, by omega, hwp2, hwp, by decide, by decide, by decide,
    by rw [ho₄.word (Or.inl (by omega)) (by unfold sWsP sFn; omega)]; exact hsp₃,
    hwsp₃.of_words fun i hi => by rw [word_off, word_off]; exact ho₄.word (Or.inr (by omega)) (by omega),
    hN₃.of_outsideArr ho₄ (by decide) (by decide) (by decide) (by decide) (by omega) hz,
    hP₃.of_disj fo₄ hr₄ (by omega), hP1, by rw [hv₄, hX₃, hv₂]; exact hlt₁⟩

/-- `pre` is constant time. -/
theorem pre_ct (M : Mont) (hG : GPowCT M sWsQ) (hR : RedcCT M Public.aY) :
    RelCT isa (Two PrePre) (seqs (CrtIfma.pre M.mm)) fun _ _ => True := by
  refine two_map id (fun _ _ h => pre_chain M h) ?_
  rw [pre_eq]
  refine ct_steps (by simp [Crt.gPow]) (by simp [copyArr]) (fun p : PrePub => gp p.uq) (fun _ _ h => h.1)
    (fun _ _ h => h.2) hG ?_
  refine ct_steps (by simp [copyArr]) (by simp [prepCode]) PrePub.nw (fun _ _ h => h.1) (fun _ _ h => h.2)
    (copyArr_ct (by decide) (by decide) (by taint_decide)) ?_
  refine ct_steps (by simp [prepCode]) (by simp [copyArr]) PrePub.uq (fun _ _ h => h.1) (fun _ _ h => h.2)
    (prep_ct M sWsQ hR (by taint_decide)) ?_
  refine ct_steps (by simp [copyArr]) (by simp [prepCode]) PrePub.nw (fun _ _ h => h.1) (fun _ _ h => h.2)
    (copyArr_ct (by decide) (by decide) (by taint_decide)) ?_
  exact ct_last PrePub.up (fun _ _ h => h) (prep_ct M sWsP hR (by taint_decide))

end VG.Proof.Bignum.X86_64
