module

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Pre
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.R2X
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtPreR2
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTQ
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTPSub
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
public import VerifiedGarbage.Impl.Rsa.X86_64.CrtIfma
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Pre
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.R2X
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtPreR2
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTQ
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTPSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
meta import VerifiedGarbage.Impl.Rsa.X86_64.CrtIfma
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# RSA with AVX512_IFMA on x86-64: constant time, before the vector code

`pre` is `prep` for each prime, whose pieces (`redc`, copies, Montgomery
multiplications, and the blocks entering and leaving the prime's
workspace) are constant time: so is `prep` (`prep_ct`), for `prep_ok`'s
hypotheses, and `pre` (`pre_ct`), for `pre_ok`'s. Before each piece, a
predicate carries the piece's claim's hypotheses and what correctness gives
after it (`prep_chain`, `pre_chain`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64 CrtCTQ

theorem redc_ct_Xm (M : Mont) : RedcCT M Public.aXm := redc_ct_of M (by taint_decide)

/-! ## `prep` -/

/-- `prep_ok`'s hypotheses, with the public data `p` (`n`'s workspace and
`-n⁻¹`, `n`, and the prime's workspace). -/
def PrepPre (sl : Nat) (p : UPub) (s : State) : Prop :=
  ∃ (mx : BitVec 64) (X : Nat), Good s p.B p.Z p.w p.minv ∧ p.w < 2 ^ 28 ∧ slot p.w 8 ≤ p.o ∧
    p.o + slot p.wx 8 + wsTab p.wx ≤ p.Z ∧ 2 ≤ p.wx ∧ p.wx ≤ p.w ∧ sl < 32 ∧
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

/-- Entering the prime's workspace, from `n`'s. -/
theorem enter_rpre {s : State} {p : UPub} {sl j : Nat} (hj : j < 8) {mx : BitVec 64} {X : Nat}
    (hg : Good s p.B p.Z p.w p.minv)
    (hw28 : p.w < 2 ^ 28) (hlo : slot p.w 8 ≤ p.o) (hhi : p.o + slot p.wx 8 + wsTab p.wx ≤ p.Z)
    (hwx2 : 2 ≤ p.wx) (hwx : p.wx ≤ p.w) (hsl : sl < 32) (hslv : word s.mem p.B (8 * sl) = off p.B p.o)
    (hws : WsAt s.mem p.B p.o p.wx mx) (hX : XVals s p.B p.o p.wx mx X) (hX1 : 1 < X) :
    WP isa (.block [.mov .rdi (.mem (hdr sl))]) s fun t =>
      RPre j (xp p) t ∧ SubCtx t p.B p.Z p.o p.w p.wx mx ∧ XVals t p.B p.o p.wx mx X ∧ t.mem = s.mem ∧
        Keep [.rdi] s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = off p.B p.o ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hs.ld (d := 8 * sl) (by omega_arith), hslv]) rfl)
    fun t ⟨⟨hdi, hm⟩, k⟩ => ?_
  have hc : SubCtx t p.B p.Z p.o p.w p.wx mx :=
    SubCtx.mk' (hs.congr k.2.2) (by rw [hm]; exact hg.hdr) (by rw [hm]; exact hws) hdi hlo (by have := tabBytes_le_wsTab p.wx; omega_arith)
  have hX' : XVals t p.B p.o p.wx mx X := by
    rw [show t = { t with mem := s.mem } by rw [← hm]]; exact ⟨hX.n, hX.inv, hX.one⟩
  exact ⟨⟨mx, X, hc, hX', hwx2, hwx, show p.w < 2 ^ 30 by omega_arith, hX1, hj⟩, hc, hX', hm, k⟩

/-- `PP3` from the prime's workspace's facts, as `prep_ok` runs the rest of `prep`. -/
theorem prep_chain3 (M : Mont) {p : UPub} {s₃ : State} {mx : BitVec 64} {X : Nat}
    (hc₃ : SubCtx s₃ p.B p.Z p.o p.w p.wx mx) (hX₃ : XVals s₃ p.B p.o p.wx mx X) (hwx2 : 2 ≤ p.wx)
    (hwx : p.wx ≤ p.w) (hw30 : p.w < 2 ^ 30) (hX1 : 1 < X) : PP3 M p s₃ := by
  have hX8 : 256 ≤ slot p.wx 8 := by unfold slot hdrBytes; omega_arith
  have lC := slot_le (w := p.wx) (show aXc < 8 by decide)
  have hC0 := hdr_lt_slot p.wx aXc (show 31 < 32 by decide)
  refine ⟨⟨mx, X, hc₃, hX₃, hwx2, hwx, hw30, hX1, by decide⟩, ?_⟩
  -- `redc` of `x R_n`.
  refine WP.mono (redc_ok M hc₃ hX₃ hwx2 hwx (by omega_arith) hX1 (j := Public.aXm) (by decide))
    fun s₄ ⟨hc₄, hX₄, hlt₄, _, _, _⟩ => ⟨⟨mx, hc₄.good, Nat.le_refl _⟩, ?_⟩
  -- `aT := aY aXc`.
  refine WP.mono (M.mm_ok (o := aT) (a := Public.aY) (b := aXc) hc₄.good (Nat.le_refl _) hwx2 (by omega_arith)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hX₄.inv
    (by rw [hX₄.n]; exact hlt₄)) fun s₅ ⟨_, _, _, ha₅, k₅⟩ => ?_
  obtain ⟨hc₅, hX₅, _⟩ := hc₄.of_arrays hX₄ ha₅ (by
    intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> decide) k₅.2.2 (k₅.gpr (by decide)) (by omega_arith)
  refine ⟨⟨mx, hc₅.good, Nat.le_refl _⟩, ?_⟩
  -- `aXc := aT`.
  refine WP.mono (copyArr_ok hc₅.good (Nat.le_refl _) (by omega_arith) (by omega_arith) (o := aXc) (a := aT)
    (by decide) (by decide) (by decide)) fun s₆ ⟨_, ho₆, k₆⟩ => ?_
  have hc₆ := hc₅.of_frm (rs := [(slot p.wx aXc, 8 * p.wx)]) (Frm.of_outside ho₆ (by simp)) (fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only; omega_arith) k₆.2.2 (k₆.gpr (by decide))
  have hX₆ : XVals s₆ p.B p.o p.wx mx X := hX₅.of_outside ho₆ (by decide) (by decide) (by decide) (by omega_arith)
    (by have := hc₅.good.scr.nowrap; omega_arith)
  -- `aY := aY · 1`.
  exact ⟨⟨mx, hc₆.good, Nat.le_refl _⟩, WP.mono (M.mm_ok (o := Public.aY) (a := Public.aY) (b := Public.aOne)
    hc₆.good (Nat.le_refl _) hwx2 (by omega_arith) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hX₆.inv (by rw [hX₆.n, hX₆.one]; exact hX1)) fun _ h₇ => h₇.1.rdi⟩


/-- `prep` after `aY := aXc`. -/
def prepTail (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  redc mul Public.aXm ++ (([mul aT Public.aY aXc] : List (Prog isa)) ++
    (copyArr aXc aT ++ ([mul Public.aY Public.aY Public.aOne, .block [leave]] : List (Prog isa))))

/-- `prep` after `aY := aXc` is constant time. -/
theorem prepTail_ct (M : Mont) (hXm : RedcCT M Public.aXm) :
    RelCT isa (Two (PP3 M)) (seqs (prepTail M.mm)) fun _ _ => True := by
  unfold prepTail
  refine ct_steps (by simp [redc]) (by simp) xp (fun _ _ h => h.1) (fun _ _ h => h.2) hXm ?_
  refine ct_steps (by simp) (by simp [copyArr]) UPub.pw (fun _ _ h => h.1) (fun _ _ h => h.2)
    (M.ct (by unfold MmUse; decide)) ?_
  refine ct_steps (by simp [copyArr]) (by simp) UPub.pw (fun _ _ h => h.1) (fun _ _ h => h.2)
    (copyArr_ct (by decide) (by decide) (by taint_decide)) ?_
  exact ct_step UPub.pw (fun _ _ h => h.1) (fun _ _ h => h.2) (M.ct (by unfold MmUse; decide))
    (two_taint [.rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [show s₁.gpr .rdi = _ from h₁, h₂]) (by taint_decide))

/-! ## `r2X` -/

/-- The public data of `r2X`: the stack pointer, `pre`'s address, `n`'s
workspace's base and the prime's offset and words. -/
structure RXPub where
  sp : Addr
  A : Addr
  B : Addr
  o : Nat
  wx : Nat

/-- `maskN`'s block, split at the load of `n`'s base. -/
def mnBlk1 : List Instr := [.mov .rax (.mem (hdr sLink))]
def mnBlk2 (j : Nat) : List Instr :=
  [.mov .r15 (.mem (ws .rax Public.sMask)), .mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr j)))]
def mnLoop : Prog isa :=
  wordLoop 0 [.mov .rax (.mem (ix .rbx .r14)), .alu .and .rax (.reg .r15), .store (ix .rbx .r14) .rax]

theorem r2X_eqCT (q : Bool) (j : Nat) : CrtIfma.r2X q j =
    [.block (CrtIfma.r2XBlk q j), copyWords, .block (mnBlk1 ++ mnBlk2 j), mnLoop, .block CrtIfma.orOne] := rfl

/-- Before `orOne`. -/
def X4 (j : Nat) (p : RXPub) (s : State) : Prop := s.gpr .rbx = off (off p.B p.o) (slot p.wx j)

/-- Before the masking loop. -/
def X3 (j : Nat) (p : RXPub) (s : State) : Prop :=
  s.gpr .rbx = off (off p.B p.o) (slot p.wx j) ∧ s.gpr .r12 = BitVec.ofNat 64 p.wx ∧ WP isa mnLoop s (X4 j p)

/-- Before the loads of the mask and the array's base. -/
def X2b (j : Nat) (p : RXPub) (s : State) : Prop :=
  s.gpr .rax = p.B ∧ s.gpr .rdi = off p.B p.o ∧ WP isa (.block (mnBlk2 j)) s (X3 j p)

/-- Before the load of `n`'s base. -/
def X2 (j : Nat) (p : RXPub) (s : State) : Prop :=
  s.gpr .rdi = off p.B p.o ∧ WP isa (.block mnBlk1) s (X2b j p)

/-- Before the copy. -/
def X1 (q : Bool) (j : Nat) (p : RXPub) (s : State) : Prop :=
  s.gpr .rsi = off p.A (8 * r2XOff q p.wx) ∧ s.gpr .rbx = off (off p.B p.o) (slot p.wx j) ∧
    s.gpr .r12 = BitVec.ofNat 64 p.wx ∧ WP isa copyWords s (X2 j p)

/-- Before `r2X`. -/
def X0 (q : Bool) (j : Nat) (p : RXPub) (s : State) : Prop :=
  s.gpr .rsp = p.sp ∧ s.gpr .rdi = off p.B p.o ∧ WP isa (.block (CrtIfma.r2XBlk q j)) s (X1 q j p)

/-- `r2X_ok`'s hypotheses give `X0`, as `r2X_ok` runs the pieces. -/
theorem r2X_chain {q : Bool} {j : Nat} (hj : j < 8) {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64}
    {V : Nat} {c : Bool} (hc : SubCtx s B Z o w wx minv) (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hm : word s.mem B (8 * Public.sMask) = mask c) (hp : PreW s B Z (r2XOff q wx) wx V) :
    X0 q j ⟨s.gpr .rsp, stackArg s 12, B, o, wx⟩ s := by
  have hg := hc.good
  have hBn := hc.scr.nowrap
  have hGn : (off B o).toNat + slot wx 8 ≤ 2 ^ 64 := hg.scr.nowrap
  have hi := hc.hi
  have hlo := hc.lo
  have sJ := slot_le (w := wx) hj
  have hJ0 := hdr_lt_slot wx j (show 31 < 32 by decide)
  have h256 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_arith
  refine ⟨rfl, hc.rdi, WP.mono (r2XBlk_ok hj hc hp) fun t₁ ⟨hsi, hbx, h12, hm₁, k₁⟩ => ⟨hsi, hbx, h12, ?_⟩⟩
  have hs₁ : Scr t₁ (off B o) (slot wx 8) := hg.scr.congr k₁.2.2
  have hout : ∀ i < wx, ∀ b < 8, slot wx 8 ≤
      ofs (off B o) (off (stackArg s 12) (8 * r2XOff q wx + 8 * i) + BitVec.ofNat 64 b) := fun i hi' b hb => by
    have := hp.out i hi' b hb
    rcases ofs_rebase B (off (stackArg s 12) (8 * r2XOff q wx + 8 * i) + BitVec.ofNat 64 b) (o := o)
      (by omega_arith) with ⟨_, h2⟩ | ⟨h1, _⟩
    · omega_arith
    · omega_arith
  refine WP.mono (copyWords_ok (S := stackArg s 12) (eS := 8 * r2XOff q wx) (D := off B o) (eD := slot wx j)
    hsi hbx h12 (by omega_arith) (by omega_arith) (by omega_arith)
    (fun i hi' => by rw [k₁.2.1, k₁.2.2]; exact hp.rd i hi') (fun i hi' => hs₁.st (by omega_arith))
    (fun i hi' b hb => Or.inr (by have := hout i hi' b hb; omega_arith))) fun t₂ ⟨_, _, ho₂, k₂⟩ => ?_
  rw [hm₁] at ho₂
  have k₁₂ := k₁.trans k₂
  have f₂ : Frm (off B o) [(slot wx j, 8 * wx)] s.mem t₂.mem := Frm.of_outside ho₂ (by simp)
  have hc₂ : SubCtx t₂ B Z o w wx minv := hc.of_frm f₂ (fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only; omega_arith) k₁₂.2.2 (k₁₂.gpr (by decide))
  have hM₂ : word t₂.mem B (8 * Public.sMask) = mask c := by
    rw [f₂.word_below (L := slot wx 8) (fun r hr => by rw [List.mem_singleton.mp hr]; simp only; omega_arith)
      (by omega_arith) (by omega_arith) (by have := hdr_lt_slot w 8 (show Public.sMask < 32 by decide); omega_arith)]
    exact hm
  have g₂ := hc₂.good
  have hl : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (off (off B o) (8 * i)) 8 := fun i hi' =>
    g₂.scr.ld (by have := hdr_lt_slot wx 8 hi'; omega_arith)
  have hln : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (off B (8 * i)) 8 := fun i hi' =>
    hc₂.scr.ld (by have := hdr_lt_slot w 8 hi'; omega_arith)
  refine ⟨hc₂.rdi, WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = B ∧ t.mem = t₂.mem)
    (by unfold mnBlk1; xrun [State.ea, hdr, hc₂.rdi, hdrOff, hl Crt.sLink (by decide), hc₂.link]) rfl)
    fun t₃ ⟨⟨hax, hm₃⟩, k₃⟩ => ⟨hax, (k₃.gpr (by decide)).trans hc₂.rdi, ?_⟩⟩
  have hdi₃ : t₃.gpr .rdi = off B o := (k₃.gpr (by decide)).trans hc₂.rdi
  have hl₃ : ∀ i < 32, InRegions (t₃.rd ++ t₃.wr) (off (off B o) (8 * i)) 8 := fun i hi' => by
    rw [k₃.2.1, k₃.2.2]; exact hl i hi'
  have hln₃ : ∀ i < 32, InRegions (t₃.rd ++ t₃.wr) (off B (8 * i)) 8 := fun i hi' => by
    rw [k₃.2.1, k₃.2.2]; exact hln i hi'
  have hM₃ : word t₃.mem B (8 * Public.sMask) = mask c := by rw [hm₃]; exact hM₂
  have hH₃ := g₂.hdr
  rw [← hm₃] at hH₃
  refine WP.mono (WP.keep [.r15, .r12, .rbx] (Q := fun t => t.gpr .r15 = mask c ∧
      t.gpr .r12 = BitVec.ofNat 64 wx ∧ t.gpr .rbx = off (off B o) (slot wx j) ∧ t.mem = t₃.mem)
    (by unfold mnBlk2; xrun [State.ea, hdr, Crt.ws, hdi₃, hax, hdrOff, hln₃ Public.sMask (by decide), hM₃,
      hl₃ (sArr j) (by unfold sArr; omega_arith), hl₃ sW (by decide), hH₃.harr j hj, hH₃.hw]) rfl)
    fun t₄ ⟨⟨h15, h12', hbx', hm₄⟩, k₄⟩ => ⟨hbx', h12', ?_⟩
  have hs₄ : Scr t₄ (off B o) (slot wx 8) := g₂.scr.congr (k₃.2.2 ▸ k₄.2.2)
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = t₄.mem → Keep [.r14] t₄ t → t.cf = t₄.cf →
      MaskInv t₄ (off B o) (slot wx 8) (slot wx j) c 0 t := fun t h14 hm' k _ =>
    ⟨hs₄.congr k.2.2, k.mono (by decide), h14, by rw [hm']; exact Outside.refl _ _ _ _,
      fun i hi' => absurd hi' (Nat.not_lt_zero _)⟩
  exact WP.mono (wordLoop_ok (start := 0) (N := wx) (by omega_arith) (by omega_arith)
    (MaskInv t₄ (off B o) (slot wx 8) (slot wx j) c) h0
    (fun i _ hi' t hI => maskStep_ok hbx' h15 h12' (by omega_arith) (by omega_arith) hi' hI))
    fun t₅ hI => (hI.keep.gpr (by decide)).trans hbx'

/-- `r2X` is constant time. -/
theorem r2X_ct (q : Bool) (j : Nat) {h1 h2 h3 h4 h5 : VG.Taint.Hint VG.X86_64.Taint.T}
    (t1 : (taint.check (Taint.ofRegs [.rsp, .rdi]) (.block (CrtIfma.r2XBlk q j)) h1).isSome = true)
    (t2 : (taint.check (Taint.ofRegs [.rdi]) (.block mnBlk1) h2).isSome = true)
    (t3 : (taint.check (Taint.ofRegs [.rax, .rdi]) (.block (mnBlk2 j)) h3).isSome = true)
    (t4 : (taint.check (Taint.ofRegs [.rbx, .r12]) mnLoop h4).isSome = true)
    (t5 : (taint.check (Taint.ofRegs [.rbx]) (.block CrtIfma.orOne) h5).isSome = true) :
    RelCT isa (Two (X0 q j)) (seqs (CrtIfma.r2X q j)) fun _ _ => True := by
  rw [r2X_eqCT]
  simp only [seqs]
  refine ct_taint [.rsp, .rdi] (pins_of (fun (p : RXPub) r => if r = .rsp then p.sp else off p.B p.o)
    fun p s h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1
      · exact h.2.1) t1 (fun _ _ h => h.2.2) ?_
  refine ct_taint [.rsi, .rbx, .r12] (pins_of (fun (p : RXPub) r => if r = .rsi then off p.A (8 * r2XOff q p.wx)
      else if r = .rbx then off (off p.B p.o) (slot p.wx j) else BitVec.ofNat 64 p.wx)
    fun p s h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.1
      · exact h.2.1
      · exact h.2.2.1) (by taint_decide) (fun _ _ h => h.2.2.2) ?_
  refine RelCT.seq (RelCT.block_append (RelCT.seq
    (two_piece (Ψ := X2b j) [.rdi] (pins_of (fun p _ => off p.B p.o) fun p s h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.1) t2 fun _ _ h => h.2)
    (two_piece (Ψ := X3 j) [.rax, .rdi] (pins_of (fun (p : RXPub) r => if r = .rax then p.B else off p.B p.o)
      fun p s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1
        · exact h.2.1) t3 fun _ _ h => h.2.2))) ?_
  refine ct_taint [.rbx, .r12] (pins_of (fun (p : RXPub) r => if r = .rbx then off (off p.B p.o) (slot p.wx j)
      else BitVec.ofNat 64 p.wx)
    fun p s h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1
      · exact h.2.1) t4 (fun _ _ h => h.2.2) ?_
  exact two_taint [.rbx] (pins_of (fun p _ => off (off p.B p.o) (slot p.wx j)) fun p s h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h) t5

/-! ## `prepP` -/

/-- The public data of `prepP`: `prep`'s, the stack pointer and `pre`'s
address. -/
structure UPubP where
  u : UPub
  sp : Addr
  A : Addr

abbrev UPubP.rx (p : UPubP) : RXPub := ⟨p.sp, p.A, p.u.B, p.u.o, p.u.wx⟩

/-- `prepP_ok`'s hypotheses (with `q`'s words from `pre`), with the public
data `p`. -/
def PrepPreP (sl : Nat) (q : Bool) (p : UPubP) (s : State) : Prop :=
  PrepPre sl p.u s ∧ s.gpr .rsp = p.sp ∧ stackArg s 12 = p.A ∧
    ∃ (c : Bool) (V : Nat), word s.mem p.u.B (8 * Public.sMask) = mask c ∧
      PreW s p.u.B p.u.Z (r2XOff q p.u.wx) p.u.wx V

/-- Before `r2X`. -/
def PPP1 (M : Mont) (q : Bool) (p : UPubP) (s : State) : Prop :=
  X0 q Public.aY p.rx s ∧ WP isa (seqs (CrtIfma.r2X q Public.aY)) s (PP3 M p.u)

/-- Before `prepP`. -/
def PPP0 (M : Mont) (sl : Nat) (q : Bool) (p : UPubP) (s : State) : Prop :=
  s.gpr .rdi = p.u.B ∧ WP isa (.block [.mov .rdi (.mem (hdr sl))]) s (PPP1 M q p)

theorem prepP_split (mul : Nat → Nat → Nat → Prog isa) (sl : Nat) (q : Bool) :
    CrtIfma.prepP mul sl q = ([.block [.mov .rdi (.mem (hdr sl))]] : List (Prog isa)) ++
      (CrtIfma.r2X q Public.aY ++ prepTail mul) := by
  simp only [CrtIfma.prepP, prepTail, List.append_assoc]

/-- `prepP_ok`'s hypotheses give `PPP0`, as `prepP_ok` runs the pieces. -/
theorem prepP_chain (M : Mont) {sl : Nat} {q : Bool} {p : UPubP} {s : State} (h : PrepPreP sl q p s) :
    PPP0 M sl q p s := by
  obtain ⟨⟨mx, X, hg, hw28, hlo, hhi, hwx2, hwx, hsl, hslv, hws, hX, hX1⟩, hsp, hA, c, V, hm, hp⟩ := h
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot p.u.w 8 (show 31 < 32 by decide)
  have lY := slot_le (w := p.u.wx) (show Public.aY < 8 by decide)
  have hY0 := hdr_lt_slot p.u.wx Public.aY (show 31 < 32 by decide)
  refine ⟨hg.rdi, WP.mono (enter_rpre (j := Public.aR2) (by decide) hg hw28 hlo hhi hwx2 hwx hsl hslv hws hX hX1)
    fun s₁ ⟨_, hc₁, hX₁, hm₁, k₁⟩ => ?_⟩
  have hi₁ : InScr p.u.B p.u.Z s.mem s₁.mem := fun x _ => by rw [hm₁]
  have hp₁ := hp.congr hi₁ (k₁.gpr (by decide)) k₁.2.1 k₁.2.2
  have hsp₁ : s₁.gpr .rsp = p.sp := (k₁.gpr (by decide)).trans hsp
  have hA₁ : stackArg s₁ 12 = p.A := (hp.arg_eq hi₁ (k₁.gpr (by decide))).trans hA
  have hm₁' : word s₁.mem p.u.B (8 * Public.sMask) = mask c := by rw [hm₁]; exact hm
  refine ⟨?_, WP.mono (r2X_ok (j := Public.aY) (c := c) (by decide) hc₁ hwx2 hwx (by omega_arith) hm₁' hp₁)
    fun s₃ ⟨hc₃, _, f₃, _⟩ => ?_⟩
  · have := r2X_chain (j := Public.aY) (by decide) hc₁ hwx2 hwx (by omega_arith) hm₁' hp₁
    rw [hsp₁, hA₁] at this
    exact this
  have ho₃ : Outside (off p.u.B p.u.o) (slot p.u.wx Public.aY) (8 * (p.u.wx + 2)) s₁.mem s₃.mem := fun x hx =>
    f₃ x fun r hr => by rw [List.mem_singleton.mp hr]; exact hx
  exact prep_chain3 M hc₃ (hX₁.of_outside ho₃ (by decide) (by decide) (by decide) (Nat.le_refl _)
    (by have := hc₁.good.scr.nowrap; omega_arith)) hwx2 hwx (by omega_arith) hX1

/-- `prepP` is constant time. -/
theorem prepP_ct (M : Mont) (sl : Nat) (q : Bool) (hXm : RedcCT M Public.aXm)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rdi (.mem (hdr sl))]) hc).isSome = true)
    (hR : RelCT isa (Two (X0 q Public.aY)) (seqs (CrtIfma.r2X q Public.aY)) fun _ _ => True) :
    RelCT isa (Two (PrepPreP sl q)) (seqs (CrtIfma.prepP M.mm sl q)) fun _ _ => True := by
  refine two_map id (fun _ _ h => prepP_chain M h) ?_
  rw [prepP_split]
  refine RelCT.seqs_app (by simp) (by simp [CrtIfma.r2X]) (ct_taint [.rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1, h₂.1]) hT (fun _ _ h => h.2) ?_)
  refine ct_steps (by simp [CrtIfma.r2X]) (by simp [prepTail, redc]) UPubP.rx (fun _ _ h => h.1)
    (fun _ _ h => h.2) hR ?_
  exact two_map UPubP.u (fun _ _ h => h) (prepTail_ct M hXm)

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

/-! ## `preP` -/

/-- The public data of `preP`: `pre`'s, the stack pointer and `pre`'s address. -/
structure PrePubP where
  p : PrePub
  sp : Addr
  A : Addr

abbrev PrePubP.uq (p : PrePubP) : UPubP := ⟨p.p.uq, p.sp, p.A⟩
abbrev PrePubP.up (p : PrePubP) : UPubP := ⟨p.p.up, p.sp, p.A⟩

/-- `preP_ok`'s hypotheses. -/
def PrePreP (p : PrePubP) (s : State) : Prop :=
  ∃ (mp mq : BitVec 64) (P Q C VP VQ : Nat) (c : Bool), Good s p.p.B p.p.Z p.p.w p.p.minv ∧ p.p.w < 2 ^ 28 ∧
    slot p.p.w 8 ≤ p.p.op ∧ p.p.op + slot p.p.wp 8 + wsTab p.p.wp ≤ p.p.oq ∧
    p.p.oq + slot p.p.wp 8 + wsTab p.p.wp ≤ p.p.Z ∧ 2 ≤ p.p.wp ∧ p.p.w = 2 * p.p.wp ∧
    word s.mem p.p.B (8 * sWsP) = off p.p.B p.p.op ∧ word s.mem p.p.B (8 * sWsQ) = off p.p.B p.p.oq ∧
    WsAt s.mem p.p.B p.p.op p.p.wp mp ∧ WsAt s.mem p.p.B p.p.oq p.p.wp mq ∧ NVals s p.p.B p.p.w p.p.minv p.p.N ∧
    wv s.mem p.p.B (slot p.p.w Public.aXm) p.p.w % p.p.N = C * 2 ^ (64 * p.p.w) % p.p.N ∧
    XVals s p.p.B p.p.op p.p.wp mp P ∧ 1 < P ∧ P % 2 = 1 ∧ XVals s p.p.B p.p.oq p.p.wp mq Q ∧ 1 < Q ∧
    Q % 2 = 1 ∧ s.gpr .rsp = p.sp ∧ stackArg s 12 = p.A ∧ word s.mem p.p.B (8 * Public.sMask) = mask c ∧
    PreW s p.p.B p.p.Z (r2XOff false p.p.wp) p.p.wp VP ∧ PreW s p.p.B p.p.Z (r2XOff true p.p.wp) p.p.wp VQ ∧
    (c = false → P = 3) ∧ (c = true → VP % P = 2 ^ (64 * p.p.wp * 2) % P) ∧
    (c = false → Q = 3) ∧ (c = true → VQ % Q = 2 ^ (64 * p.p.wp * 2) % Q)

/-- Before `preP`. -/
def PRP0 (M : Mont) (p : PrePubP) (s : State) : Prop :=
  PrepPreP sWsQ true p.uq s ∧ WP isa (seqs (CrtIfma.prepP M.mm sWsQ true)) s (PrepPreP sWsP false p.up)

/-- `preP_ok`'s hypotheses give `PRP0`, as `preP_ok` runs the pieces. -/
theorem preP_chain (M : Mont) {p : PrePubP} {s : State} (h : PrePreP p s) : PRP0 M p s := by
  obtain ⟨⟨B, Z, w, minv, N, op, oq, wp⟩, sp, A⟩ := p
  dsimp only [PrePreP] at h
  obtain ⟨mp, mq, P, Q, C, VP, VQ, c, hg, hw28, hlo, hpq, hoq, hwp2, hw2, hsp, hsq, hwsp, hwsq, hN, hXm, hP,
    hP1, hPodd, hQ, hQ1, hQodd, hrsp, hA, hM, hpP, hpQ, hP3, hVP, hQ3, hVQ⟩ := h
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot wp 8 := by unfold slot hdrBytes; omega_arith
  have ho64 : oq < 2 ^ 64 := by omega_arith
  have hQd : ∀ r ∈ [xRange oq wp], r.1 + r.2 ≤ op ∨ op + slot wp 8 ≤ r.1 := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact .inr (by simp only [xRange]; omega_arith)
  refine ⟨⟨by dsimp only [PrepPre, PrePubP.uq, PrePub.uq]; exact ⟨mq, Q, hg, hw28, by omega_arith, hoq, hwp2,
      by omega_arith, by decide, hsq, hwsq, hQ, hQ1⟩, hrsp, hA, c, VQ, hM, hpQ⟩,
    WP.mono (prepP_ok (C := C) M hg hw28 (by omega_arith) hoq hwp2 hw2 (by decide) hsq hwsq hXm hQ hQ1 hQodd
      hM hpQ hQ3 hVQ) fun s₁ ⟨hg₁, _, _, _, _, _, _, fQ, kQ, _⟩ => ?_⟩
  have hb : ∀ d, d + 8 ≤ oq → word s₁.mem B d = word s.mem B d := fun d hd => fQ.x_below hd ho64
  have hi : InScr B Z s.mem s₁.mem := InScr.of_frm fQ fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only [xRange]; omega_arith
  dsimp only [PrepPreP, PrepPre, PrePubP.up, PrePub.up]
  exact ⟨⟨mp, P, hg₁, hw28, hlo, by omega_arith, hwp2, by omega_arith, by decide,
    by rw [hb _ (by unfold sWsP sFn; omega_arith)]; exact hsp,
    hwsp.of_disj fQ (fun r hr => by rcases hQd r hr with h | h <;> omega_arith) (by omega_arith),
    hP.of_disj fQ hQd (by omega_arith), hP1⟩, (kQ.gpr (by decide)).trans hrsp,
    (hpP.arg_eq hi (kQ.gpr (by decide))).trans hA, c, VP,
    by rw [hb _ (by have := hdr_lt_slot w 8 (show Public.sMask < 32 by decide); omega_arith)]; exact hM,
    hpP.congr hi (kQ.gpr (by decide)) kQ.2.1 kQ.2.2⟩

/-- `preP` is constant time. -/
theorem preP_ct (M : Mont) (hXm : RedcCT M Public.aXm) :
    RelCT isa (Two PrePreP) (seqs (CrtIfma.preP M.mm)) fun _ _ => True := by
  refine two_map id (fun _ _ h => preP_chain M h) ?_
  refine ct_steps (by simp [CrtIfma.prepP]) (by simp [CrtIfma.prepP]) PrePubP.uq (fun _ _ h => h.1)
    (fun _ _ h => h.2) (prepP_ct M sWsQ true hXm (by taint_decide)
      (r2X_ct true Public.aY (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)
        (by taint_decide))) ?_
  exact ct_last PrePubP.up (fun _ _ h => h) (prepP_ct M sWsP false hXm (by taint_decide)
    (r2X_ct false Public.aY (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)
      (by taint_decide)))

end VG.Proof.Bignum.X86_64
