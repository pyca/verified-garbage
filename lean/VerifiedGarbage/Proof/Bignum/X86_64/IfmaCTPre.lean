import VerifiedGarbage.Proof.Bignum.X86_64.IfmaPre
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTQ
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTPSub
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc

/-!
# RSA with AVX512_IFMA on x86-64: constant time, before the vector code

`pre` is `prep` for each prime, whose pieces (`redc`, copies, Montgomery
multiplications, and the blocks entering and leaving the prime's
workspace) are constant time: so is `prep` (`prep_ct`), for `prep_ok`'s
hypotheses, and `pre` (`pre_ct`), for `pre_ok`'s. Before each piece, a
predicate carries the piece's claim's hypotheses and what correctness gives
after it (`prep_chain`, `pre_chain`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64 CrtCTQ

/-- `redc` of `n`'s `R² mod n` and of its `x R mod n` is constant time. -/
theorem redc_ct_R2 (M : Mont) : RedcCT M Public.aR2 := redc_ct_of M (by taint_decide)
theorem redc_ct_Xm (M : Mont) : RedcCT M Public.aXm := redc_ct_of M (by taint_decide)

/-! ## `prep` -/

/-- `prep_ok`'s hypotheses, with the public data `p` (`n`'s workspace and
`-n⁻¹`, `n`, and the prime's workspace). -/
def PrepPre (sl : Nat) (p : UPub) (s : State) : Prop :=
  ∃ (mx : BitVec 64) (X : Nat), Good s p.B p.Z p.w p.minv ∧ p.w < 2 ^ 28 ∧ slot p.w 8 ≤ p.o ∧
    p.o + slot p.wx 8 + tabBytes p.wx ≤ p.Z ∧ 2 ≤ p.wx ∧ p.wx ≤ p.w ∧ sl < 32 ∧
    word s.mem p.B (8 * sl) = off p.B p.o ∧ WsAt s.mem p.B p.o p.wx mx ∧ XVals s p.B p.o p.wx mx X ∧ 1 < X

/-- The prime's workspace. -/
abbrev UPub.pw (p : UPub) : Ws := ⟨off p.B p.o, slot p.wx 8, p.wx⟩

/-- Before leaving the prime's workspace. -/
def PP7 (p : UPub) (s : State) : Prop := s.gpr .rdi = off p.B p.o

/-- Before `aY := aY · 1`. -/
def PP6 (M : Mont) (p : UPub) (s : State) : Prop :=
  GoodW p.pw s ∧ WP isa (M.mm Public.aY Public.aY Public.aOne) s (PP7 p)

/-- Before `aXc := aT`. -/
def PP5 (M : Mont) (p : UPub) (s : State) : Prop :=
  GoodW p.pw s ∧ WP isa (seqs (copyArr aXc aT)) s (PP6 M p)

/-- Before `aT := aY aXc`. -/
def PP4 (M : Mont) (p : UPub) (s : State) : Prop :=
  GoodW p.pw s ∧ WP isa (M.mm aT Public.aY aXc) s (PP5 M p)

/-- Before the second `redc`. -/
def PP3 (M : Mont) (p : UPub) (s : State) : Prop :=
  RPre Public.aXm (xp p) s ∧ WP isa (seqs (redc M.mm Public.aXm)) s (PP4 M p)

/-- Before `aY := aXc`. -/
def PP2 (M : Mont) (p : UPub) (s : State) : Prop :=
  GoodW p.pw s ∧ WP isa (seqs (copyArr Public.aY aXc)) s (PP3 M p)

/-- Before the first `redc`. -/
def PP1 (M : Mont) (p : UPub) (s : State) : Prop :=
  RPre Public.aR2 (xp p) s ∧ WP isa (seqs (redc M.mm Public.aR2)) s (PP2 M p)

/-- Before `prep`. -/
def PP0 (M : Mont) (sl : Nat) (p : UPub) (s : State) : Prop :=
  s.gpr .rdi = p.B ∧ WP isa (.block [.mov .rdi (.mem (hdr sl))]) s (PP1 M p)

theorem prep_eq (mul : Nat → Nat → Nat → Prog isa) (sl : Nat) :
    CrtIfma.prep mul sl = ([.block [.mov .rdi (.mem (hdr sl))]] : List (Prog isa)) ++ (redc mul Public.aR2 ++
      (copyArr Public.aY aXc ++ (redc mul Public.aXm ++ (([mul aT Public.aY aXc] : List (Prog isa)) ++
        (copyArr aXc aT ++ [mul Public.aY Public.aY Public.aOne, .block [leave]]))))) := by
  simp only [CrtIfma.prep, List.append_assoc]

/-- Entering the prime's workspace, from `n`'s. -/
theorem enter_rpre {s : State} {p : UPub} {sl j : Nat} (hj : j < 8) {mx : BitVec 64} {X : Nat}
    (hg : Good s p.B p.Z p.w p.minv)
    (hw28 : p.w < 2 ^ 28) (hlo : slot p.w 8 ≤ p.o) (hhi : p.o + slot p.wx 8 + tabBytes p.wx ≤ p.Z)
    (hwx2 : 2 ≤ p.wx) (hwx : p.wx ≤ p.w) (hsl : sl < 32) (hslv : word s.mem p.B (8 * sl) = off p.B p.o)
    (hws : WsAt s.mem p.B p.o p.wx mx) (hX : XVals s p.B p.o p.wx mx X) (hX1 : 1 < X) :
    WP isa (.block [.mov .rdi (.mem (hdr sl))]) s fun t =>
      RPre j (xp p) t ∧ SubCtx t p.B p.Z p.o p.w p.wx mx ∧ XVals t p.B p.o p.wx mx X ∧ t.mem = s.mem ∧
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
  exact ⟨⟨mx, X, hc, hX', hwx2, hwx, show p.w < 2 ^ 30 by omega, hX1, hj⟩, hc, hX', hm, k⟩

/-- `prep_ok`'s hypotheses give `PP0`, as `prep_ok` runs the pieces. -/
theorem prep_chain (M : Mont) {sl : Nat} {p : UPub} {s : State} (h : PrepPre sl p s) : PP0 M sl p s := by
  obtain ⟨mx, X, hg, hw28, hlo, hhi, hwx2, hwx, hsl, hslv, hws, hX, hX1⟩ := h
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot p.wx 8 := by unfold slot hdrBytes; omega
  have lY := slot_le (w := p.wx) (show Public.aY < 8 by decide)
  have hY0 := hdr_lt_slot p.wx Public.aY (show 31 < 32 by decide)
  have lC := slot_le (w := p.wx) (show aXc < 8 by decide)
  have hC0 := hdr_lt_slot p.wx aXc (show 31 < 32 by decide)
  -- Into the prime's workspace.
  refine ⟨hg.rdi, WP.mono (enter_rpre (j := Public.aR2) (by decide) hg hw28 hlo hhi hwx2 hwx hsl hslv hws hX hX1)
    fun s₁ ⟨hr₁, hc₁, hX₁, _, _⟩ => ⟨hr₁, ?_⟩⟩
  -- `redc` of `R_n²`.
  refine WP.mono (redc_ok M hc₁ hX₁ hwx2 hwx (by omega) hX1 (j := Public.aR2) (by decide))
    fun s₂ ⟨hc₂, hX₂, _, _, _, _⟩ => ⟨⟨mx, hc₂.good, Nat.le_refl _⟩, ?_⟩
  -- `aY := aXc`.
  refine WP.mono (copyArr_ok hc₂.good (Nat.le_refl _) (by omega) (by omega) (o := Public.aY) (a := aXc)
    (by decide) (by decide) (by decide)) fun s₃ ⟨_, ho₃, k₃⟩ => ?_
  have hc₃ := hc₂.of_frm (rs := [(slot p.wx Public.aY, 8 * p.wx)]) (Frm.of_outside ho₃ (by simp)) (fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only; omega) k₃.2.2 (k₃.gpr (by decide))
  have hX₃ : XVals s₃ p.B p.o p.wx mx X := hX₂.of_outside ho₃ (by decide) (by decide) (by decide) (by omega)
    (by have := hc₂.good.scr.nowrap; omega)
  refine ⟨⟨mx, X, hc₃, hX₃, hwx2, hwx, show p.w < 2 ^ 30 by omega, hX1, by decide⟩, ?_⟩
  -- `redc` of `x R_n`.
  refine WP.mono (redc_ok M hc₃ hX₃ hwx2 hwx (by omega) hX1 (j := Public.aXm) (by decide))
    fun s₄ ⟨hc₄, hX₄, hlt₄, _, _, _⟩ => ⟨⟨mx, hc₄.good, Nat.le_refl _⟩, ?_⟩
  -- `aT := aY aXc`.
  refine WP.mono (M.mm_ok (o := aT) (a := Public.aY) (b := aXc) hc₄.good (Nat.le_refl _) hwx2 (by omega)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hX₄.inv
    (by rw [hX₄.n]; exact hlt₄)) fun s₅ ⟨_, _, _, ha₅, k₅⟩ => ?_
  obtain ⟨hc₅, hX₅, _⟩ := hc₄.of_arrays hX₄ ha₅ (by
    intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> decide) k₅.2.2 (k₅.gpr (by decide)) (by omega)
  refine ⟨⟨mx, hc₅.good, Nat.le_refl _⟩, ?_⟩
  -- `aXc := aT`.
  refine WP.mono (copyArr_ok hc₅.good (Nat.le_refl _) (by omega) (by omega) (o := aXc) (a := aT)
    (by decide) (by decide) (by decide)) fun s₆ ⟨_, ho₆, k₆⟩ => ?_
  have hc₆ := hc₅.of_frm (rs := [(slot p.wx aXc, 8 * p.wx)]) (Frm.of_outside ho₆ (by simp)) (fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only; omega) k₆.2.2 (k₆.gpr (by decide))
  have hX₆ : XVals s₆ p.B p.o p.wx mx X := hX₅.of_outside ho₆ (by decide) (by decide) (by decide) (by omega)
    (by have := hc₅.good.scr.nowrap; omega)
  -- `aY := aY · 1`.
  exact ⟨⟨mx, hc₆.good, Nat.le_refl _⟩, WP.mono (M.mm_ok (o := Public.aY) (a := Public.aY) (b := Public.aOne)
    hc₆.good (Nat.le_refl _) hwx2 (by omega) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hX₆.inv (by rw [hX₆.n, hX₆.one]; exact hX1)) fun _ h₇ => h₇.1.rdi⟩

/-- `prep` is constant time. -/
theorem prep_ct (M : Mont) (sl : Nat) (hR2 : RedcCT M Public.aR2) (hXm : RedcCT M Public.aXm)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rdi (.mem (hdr sl))]) hc).isSome = true) :
    RelCT isa (Two (PrepPre sl)) (seqs (CrtIfma.prep M.mm sl)) fun _ _ => True := by
  refine two_map id (fun _ _ h => prep_chain M h) ?_
  rw [prep_eq]
  refine RelCT.seqs_app (by simp) (by simp [redc]) (ct_taint [.rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1, h₂.1]) hT (fun _ _ h => h.2) ?_)
  refine ct_steps (by simp [redc]) (by simp [copyArr]) xp (fun _ _ h => h.1) (fun _ _ h => h.2) hR2 ?_
  refine ct_steps (by simp [copyArr]) (by simp [redc]) UPub.pw (fun _ _ h => h.1) (fun _ _ h => h.2)
    (copyArr_ct (by decide) (by decide) (by taint_decide)) ?_
  refine ct_steps (by simp [redc]) (by simp) xp (fun _ _ h => h.1) (fun _ _ h => h.2) hXm ?_
  refine ct_steps (by simp) (by simp [copyArr]) UPub.pw (fun _ _ h => h.1) (fun _ _ h => h.2)
    (M.ct (by unfold MmUse; decide)) ?_
  refine ct_steps (by simp [copyArr]) (by simp) UPub.pw (fun _ _ h => h.1) (fun _ _ h => h.2)
    (copyArr_ct (by decide) (by decide) (by taint_decide)) ?_
  exact ct_step UPub.pw (fun _ _ h => h.1) (fun _ _ h => h.2) (M.ct (by unfold MmUse; decide))
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

abbrev PrePub.uq (p : PrePub) : UPub := ⟨p.B, p.Z, p.w, p.minv, p.N, p.oq, p.wp⟩
abbrev PrePub.up (p : PrePub) : UPub := ⟨p.B, p.Z, p.w, p.minv, p.N, p.op, p.wp⟩

/-- `pre_ok`'s hypotheses. -/
def PrePre (p : PrePub) (s : State) : Prop :=
  ∃ (mp mq : BitVec 64) (P Q C : Nat), Good s p.B p.Z p.w p.minv ∧ p.w < 2 ^ 28 ∧ slot p.w 8 ≤ p.op ∧
    p.op + slot p.wp 8 + tabBytes p.wp ≤ p.oq ∧ p.oq + slot p.wp 8 + tabBytes p.wp ≤ p.Z ∧ 2 ≤ p.wp ∧
    p.w = 2 * p.wp ∧ word s.mem p.B (8 * sWsP) = off p.B p.op ∧ word s.mem p.B (8 * sWsQ) = off p.B p.oq ∧
    WsAt s.mem p.B p.op p.wp mp ∧ WsAt s.mem p.B p.oq p.wp mq ∧ NVals s p.B p.w p.minv p.N ∧
    wv s.mem p.B (slot p.w Public.aXm) p.w % p.N = C * 2 ^ (64 * p.w) % p.N ∧
    XVals s p.B p.op p.wp mp P ∧ 1 < P ∧ P % 2 = 1 ∧ XVals s p.B p.oq p.wp mq Q ∧ 1 < Q ∧ Q % 2 = 1

/-- Before `pre`. -/
def PR0 (M : Mont) (p : PrePub) (s : State) : Prop :=
  PrepPre sWsQ p.uq s ∧ WP isa (seqs (CrtIfma.prep M.mm sWsQ)) s (PrepPre sWsP p.up)

/-- `pre_ok`'s hypotheses give `PR0`, as `pre_ok` runs the pieces. -/
theorem pre_chain (M : Mont) {p : PrePub} {s : State} (h : PrePre p s) : PR0 M p s := by
  obtain ⟨B, Z, w, minv, N, op, oq, wp⟩ := p
  dsimp only [PrePre] at h
  obtain ⟨mp, mq, P, Q, C, hg, hw28, hlo, hpq, hoq, hwp2, hw2, hsp, hsq, hwsp, hwsq, hN, hXm, hP,
    hP1, hPodd, hQ, hQ1, hQodd⟩ := h
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot wp 8 := by unfold slot hdrBytes; omega
  have ho64 : oq < 2 ^ 64 := by omega
  have hQd : ∀ r ∈ [xRange oq wp], r.1 + r.2 ≤ op ∨ op + slot wp 8 ≤ r.1 := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact .inr (by simp only [xRange]; omega)
  refine ⟨by dsimp only [PrepPre, PrePub.uq]; exact ⟨mq, Q, hg, hw28, by omega, hoq, hwp2, by omega, by decide, hsq,
    hwsq, hQ, hQ1⟩,
    WP.mono (prep_ok (C := C) M hg hw28 (by omega) hoq hwp2 hw2 (by decide) hsq hwsq hN hXm hQ hQ1 hQodd)
    fun s₁ ⟨hg₁, _, _, _, _, _, _, fQ, _, _⟩ => ?_⟩
  have hb : ∀ d, d + 8 ≤ oq → word s₁.mem B d = word s.mem B d := fun d hd => fQ.x_below hd ho64
  dsimp only [PrepPre, PrePub.up]
  exact ⟨mp, P, hg₁, hw28, hlo, by omega, hwp2, by omega, by decide,
    by rw [hb _ (by unfold sWsP sFn; omega)]; exact hsp,
    hwsp.of_disj fQ (fun r hr => by rcases hQd r hr with h | h <;> omega) (by omega),
    hP.of_disj fQ hQd (by omega), hP1⟩

/-- `pre` is constant time. -/
theorem pre_ct (M : Mont) (hR2 : RedcCT M Public.aR2) (hXm : RedcCT M Public.aXm) :
    RelCT isa (Two PrePre) (seqs (CrtIfma.pre M.mm)) fun _ _ => True := by
  refine two_map id (fun _ _ h => pre_chain M h) ?_
  refine ct_steps (by simp [CrtIfma.prep]) (by simp [CrtIfma.prep]) PrePub.uq (fun _ _ h => h.1)
    (fun _ _ h => h.2) (prep_ct M sWsQ hR2 hXm (by taint_decide)) ?_
  exact ct_last PrePub.up (fun _ _ h => h) (prep_ct M sWsP hR2 hXm (by taint_decide))

end VG.Proof.Bignum.X86_64
