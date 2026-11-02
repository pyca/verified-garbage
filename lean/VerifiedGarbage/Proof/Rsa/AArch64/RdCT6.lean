module

public import VerifiedGarbage.Proof.Rsa.AArch64.RdCT5
public import VerifiedGarbage.Proof.Rsa.AArch64.RdCT3
public import VerifiedGarbage.Proof.Rsa.AArch64.RdCode
import VerifiedGarbage.Proof.Rsa.AArch64.RdMain
import VerifiedGarbage.Proof.Rsa.AArch64.RdHead
import VerifiedGarbage.Proof.Rsa.AArch64.CvFail
import VerifiedGarbage.Proof.Rsa.AArch64.CvCTMain
import VerifiedGarbage.Proof.Rsa.AArch64.CvCTCode
public import VerifiedGarbage.Proof.Rsa.AArch64.RdPieces
import VerifiedGarbage.Proof.Rsa.AArch64.CvCT
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdCT5
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdCT3
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdCode
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdMain
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdHead
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvFail
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvCTMain
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvCTCode
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdPieces
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# `vg_rsa_recover_primes_det` on AArch64: constant time

The prefix (`prefix_ct`: the head, the loads and `M = d e`), `main`
(`rdMain_ct`), the entry and the modulus' check (`rdCode_ct`), and the
contract's `ConstantTime` (`rdCode_constantTime`): the function leaks only
`n`, `e`, the pointers and the lengths.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64.Rd

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.RecoverDet
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Impl.Rsa.AArch64.Recover (aE aD aM sD sDl entry fail prod)

/-! ## The prefix -/

/-- On entry to `main`. -/
def GM (a : Pub) (s : State) : Prop :=
  ∃ I : RpIn, dpub I = a.1 ∧ DPre I s ∧ Spec.Rsa.modulusValid (numN I) I.k = true

theorem pins_GM : Pins GM [.x0] := fun _ _ _ ⟨_, e₁, h₁, _⟩ ⟨_, e₂, h₂, _⟩ r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  rw [h₁.x0, h₂.x0]
  exact (congrArg DP.B e₁).trans (congrArg DP.B e₂).symm

theorem head_w : CTW GM (GC vk XT) (.block (VG.Impl.Rsa.AArch64.Keys.head ++ setNar)) :=
  ⟨two_taint [.x0] pins_GM (by taint_decide), fun _ s ⟨I, e, h, _⟩ =>
    WP.mono (head_ok h) fun _ ⟨g, _⟩ => ⟨I, s.mem, true, e, g, ⟨h.L, ⟨fun i hi => by rw [← h.wr]; exact h.oP.wr i hi,
      fun i hi => by rw [← h.wr]; exact h.oQ.wr i hi, h.oP.sep, h.oQ.sep, h.a⟩⟩, trivial⟩⟩

/-- Leaking the same, then code the taint analysis checks from the pinned `rs`. -/
theorem pin_seq0 {Φ : Pub → State → Prop} {c₁ c₂ : Prog isa} (rs : List Reg) (f : Pub → Reg → BitVec 64)
    (h₁ : RelCT isa (Two Φ) c₁ fun _ _ => True) (hp : ∀ a s, Φ a s → WP isa c₁ s fun t => ∀ r ∈ rs, t.gpr r = f a r)
    {hc₂ : VG.Taint.Hint VG.AArch64.Taint.T} (ht₂ : (taint.check (Taint.ofRegs rs) c₂ hc₂).isSome = true) :
    RelCT isa (Two Φ) (.seq c₁ c₂) fun _ _ => True :=
  RelCT.seq (two_post h₁ hp) (two_taint rs (fun _ _ _ h₁ h₂ r hr => (h₁ r hr).trans (h₂ r hr).symm) ht₂)

/-- A `CTW` and then code leaking the same. -/
theorem ctr_app {Φ Ψ : Pub → State → Prop} {Q : State → State → Prop} {a b : List (Prog isa)} (ha : a ≠ [])
    (hb : b ≠ []) (hA : CTW Φ Ψ (seqs a)) (hB : RelCT isa (Two Ψ) (seqs b) Q) : RelCT isa (Two Φ) (seqs (a ++ b)) Q :=
  RelCT.seqs_append ha hb (RelCT.seq hA.ct hB)

theorem ctr_cons {Φ Ψ : Pub → State → Prop} {Q : State → State → Prop} {e : Prog isa} {l : List (Prog isa)}
    (hl : l ≠ []) (he : CTW Φ Ψ e) (hr : RelCT isa (Two Ψ) (seqs l) Q) : RelCT isa (Two Φ) (seqs (e :: l)) Q := by
  obtain ⟨d, l', rfl⟩ := List.exists_cons_of_ne_nil hl
  exact RelCT.seq he.ct hr

theorem loadA_w {j sPtr sLen : Nat} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32) (ptr : DP → Addr)
    (len : DP → Nat) (bs : RpIn → List Byte)
    (hA : ∀ (I : RpIn) (m₀ : Mem) (c : Bool) (s : State), G I m₀ (vk I.k) c s → RpLens I →
      word s.mem I.B (8 * sPtr) = ptr (dpub I) ∧ word s.mem I.B (8 * sLen) = BitVec.ofNat 64 (len (dpub I)) ∧
      Src s I.B I.Z (ptr (dpub I)) (bs I) ∧ (bs I).length = len (dpub I) ∧ 1 ≤ len (dpub I) ∧
      len (dpub I) ≤ 8 * vk I.k)
    {hc₁ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base j .x8 ++ [movi .x7 0])) zeroAcc)
      hc₁).isSome = true)
    {hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₂ : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ base j .x8 ++ [ldh .x1 sPtr, ldh .x2 sLen]))
      hc₂).isSome = true)
    {hc₃ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₃ : (taint.check (Taint.ofRegs [.x0, .x8, .x1, .x2]) loadBE hc₃).isSome = true) :
    CTW (GC vk XT) (GC vk XT) (seqs (loadA j sPtr sLen)) := by
  have hz := zeroA_w (w := vk) (X := XT) (Y := XT) hj (by intros; trivial) ht₁
  refine ⟨RelCT.assoc (pin_seq0 [.x0, .x8, .x1, .x2]
    (fun a => ioVal a.1.B (off a.1.B (slot (vk a.1.k) j)) (ptr a.1) (len a.1))
    (RelCT.seq hz.ct (two_taint [.x0] pins_GC ht₂)) (fun ⟨P, i⟩ s h => ?_) ht₃), fun ⟨P, i⟩ s h => ?_⟩
  · obtain ⟨I, m₀, c, e, g, L, -⟩ := h
    subst e
    refine WP.seq (WP.mono (zeroA_ok g.ws hj) fun t ⟨_, o, _, _, _, k⟩ => ?_)
    have gt := g.out hj (Nat.le_refl _) o k (by decide)
    obtain ⟨hp, hl, -⟩ := hA I m₀ c t gt L.1
    exact loadBlk_ok gt.ws hP hL hp hl
  · obtain ⟨I, m₀, c, e, g, L, -⟩ := h
    subst e
    obtain ⟨hp, hl, hsrc, hbl, hl1, hlw⟩ := hA I m₀ c s g L.1
    exact WP.mono (loadA_ok g.ws hj hP hL hp hl hsrc hbl hl1 hlw) fun t ⟨_, o, _, _, k⟩ =>
      ⟨I, m₀, c, rfl, g.out hj (Nat.le_refl _) o k (by decide), L, trivial⟩

/-- The registers `prod`'s rows need pinned, at the narrow width. -/
def pv (P : DP) : Reg → BitVec 64
  | .x0 => P.B
  | .x11 => off P.B (slot (vk P.k) aE)
  | .x9 => off P.B (slot (vk P.k) aD)
  | .x8 => off P.B (slot (vk P.k) aM)
  | .x12 => BitVec.ofNat 64 (vk P.k)
  | .x13 => BitVec.ofNat 64 ((P.el + 7) / 8)
  | _ => 0

theorem prodRows_ct : RelCT isa (Two (GC vk XT)) (seqs [.block VG.Proof.Rsa.AArch64.prodBlk,
    VG.Impl.Rsa.AArch64.Crt.mulRows]) fun _ _ => True :=
  pin_seq0 [.x0, .x11, .x9, .x8, .x12, .x13, .x7] (fun a => pv a.1) (two_taint [.x0] pins_GC (by taint_decide))
    (fun ⟨P, i⟩ s h => by
      obtain ⟨I, m₀, c, e, g, L, -⟩ := h
      subst e
      exact WP.mono (prodBlk_ok g.ws g.args.el (by have := L.1.el2; have := L.1.k2; omega))
        fun t ⟨⟨h0, h11, h9, h8, h12, h13, h7, _⟩, _⟩ r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact h0
          · exact h11
          · exact h9
          · exact h8
          · exact h12
          · exact h13
          · exact h7)
    (by taint_decide)

theorem prefix_ct : CTW GM (GC vk XT) (seqs (([.block (VG.Impl.Rsa.AArch64.Keys.head ++ setNar)] : List (Prog isa)) ++
    (loadA Public.aN Public.sN Public.sK ++ (loadA aE Public.sE Public.sElen ++ (loadA aD sD sDl ++ prod))))) := by
  have k8 : ∀ {k : Nat}, k ≤ 8 * vk k := fun {k} => by simp only [vk]; omega
  refine ⟨?_, fun _ s ⟨I, e, h, _⟩ => WP.mono (prefix_ok h) fun _ ⟨g, _⟩ => ⟨I, s.mem, true, e, g,
    ⟨h.L, ⟨fun i hi => by rw [← h.wr]; exact h.oP.wr i hi, fun i hi => by rw [← h.wr]; exact h.oQ.wr i hi, h.oP.sep,
      h.oQ.sep, h.a⟩⟩, trivial⟩⟩
  refine ctr_cons (by simp [loadA]) head_w ?_
  refine ctr_app (a := loadA Public.aN Public.sN Public.sK) (by simp [loadA]) (by simp [loadA])
    (loadA_w (by decide) (by decide) (by decide) DP.pN DP.k
    RpIn.nb (fun I _ _ _ g L => ⟨g.args.n, g.args.k, g.n, L.nbl, Nat.le_trans (by decide) L.k1, k8⟩)
    (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine ctr_app (a := loadA aE Public.sE Public.sElen) (by simp [loadA]) (by simp [loadA])
    (loadA_w (by decide) (by decide) (by decide) DP.pE DP.el
    RpIn.eb (fun I _ _ _ g L => ⟨g.args.e, g.args.el, g.e, L.ebl, L.el1, show I.el ≤ 8 * vk I.k by have := L.el2; have := @k8 I.k; omega⟩)
    (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine ctr_app (a := loadA aD sD sDl) (by simp [loadA]) (by simp [prod])
    (loadA_w (by decide) (by decide) (by decide) DP.pD DP.dl
    RpIn.db (fun I _ _ _ g L => ⟨g.args.d, g.args.dl, g.d, L.dbl, L.dl1, show I.dl ≤ 8 * vk I.k by have := L.dl2; have := @k8 I.k; omega⟩)
    (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  rw [prod_eq]
  refine ctr_cons (by simp) (zeroA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
  exact ctr_cons (by simp) (zeroA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) prodRows_ct

/-! ## `main` -/

theorem pieces_ct [InvLaw] : CTW (GC vk XT) (GC vk XT)
    (seqs [deMinus, twos, gcd, aProd, divA, divB, square, minus4n, sqrt]) :=
  CTW.cons (by simp) deMinus_ct (CTW.cons (by simp) twos_ct (CTW.cons (by simp) gcd_ct (CTW.cons (by simp) aProd_ct
    (CTW.cons (by simp) divA_ct (CTW.cons (by simp) divB_ct (CTW.cons (by simp) square_ct
      (CTW.cons (by simp) minus4n_ct (CTW.one sqrt_ct))))))))

/-- `main` leaks the same in runs from a valid modulus with the same public data. -/
theorem rdMain_ct [InvLaw] : RelCT isa (Two GM) main fun _ _ => True := by
  rw [main_eq]
  refine ctr_app (by simp) (by simp) prefix_ct ?_
  refine ctr_app (a := [deMinus, twos, gcd, aProd, divA, divB, square, minus4n, sqrt]) (by simp) (by simp)
    pieces_ct ?_
  exact ctr_app (a := factorsA) (by simp) (by simp [storeA]) factors_ct stores_ct

/-! ## The code -/

/-- A state the contract allows, with the public data `a.1`. -/
def RDRel (a : Pub) (s : State) : Prop := rdA.pre s ∧ dpub (rpIn s) = a.1

theorem rdEntry_split : entry = ([.ldrSp .x8 16] : List Instr) ++ entry.drop 1 := rfl

/-- After `entry`'s first instruction. -/
def RD1 (a : Pub) (t : State) : Prop :=
  ∃ s, RDRel a s ∧ t.gpr .x8 = a.1.B ∧ t.gpr .x4 = a.1.pN ∧ t.gpr .x5 = BitVec.ofNat 64 a.1.k ∧
    WP isa (.block (entry.drop 1)) t (RpHeadPost s)

/-- After `entry`. -/
def RD2 (a : Pub) (t : State) : Prop := ∃ s, RDRel a s ∧ RpHeadPost s t

/-- After the modulus' check. -/
def RD3 (a : Pub) (t : State) : Prop :=
  ∃ s t₁, RDRel a s ∧ RpHeadPost s t₁ ∧ t.mem = t₁.mem ∧ Keep [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] t₁ t ∧
    t.gpr .x9 = BitVec.ofNat 64 (Spec.Rsa.modulusValid (Spec.Rsa.os2ip a.1.nb) a.1.k).toNat

theorem rdRel_x4 {a : Pub} {s : State} (h : RDRel a s) : s.gpr .x4 = a.1.pN := congrArg DP.pN h.2

theorem rdRel_x5 {a : Pub} {s : State} (h : RDRel a s) : s.gpr .x5 = BitVec.ofNat 64 a.1.k := by
  rw [← congrArg DP.k h.2]; exact (ofNat_toNat64 _).symm

theorem rdEntry_ct : RelCT isa (Two RDRel) (.block entry) (Two RD2) := by
  rw [rdEntry_split]
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := RD1) [.x4, .x5] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [rdRel_x4 h₁, rdRel_x4 h₂]
    · rw [rdRel_x5 h₁, rdRel_x5 h₂]) (by taint_decide) ?_)
    (two_piece [.x8, .x4, .x5] (fun p s₁ s₂ ⟨_, _, a₁, b₁, c₁, _⟩ ⟨_, _, a₂, b₂, c₂, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [a₁, a₂]
      · rw [b₁, b₂]
      · rw [c₁, c₂]) (by taint_decide) fun p t ⟨s, hs, _, _, _, hw⟩ => WP.mono hw fun t' h => ⟨s, hs, h⟩))
  intro p s hs
  have c := rpCtx_of hs.1.1
  have hh : WP isa (.block (([.ldrSp .x8 16] : List Instr) ++ entry.drop 1)) s (RpHeadPost s) := by
    rw [← rdEntry_split]; exact rpHead_ok' c
  have hB' : s.mem.readW (s.sp + BitVec.ofNat 64 16) 64 = stackArg s 2 := rfl
  have ha2 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 16) 8 := c.ha 2 (by decide)
  have ho : 16 % 8 = 0 ∧ 16 < 32768 := ⟨rfl, by decide⟩
  refine WP.mono (WP.and (WP.block_append_iff.mp hh) (WP.keep [.x8] (Q := fun t => t.gpr .x8 = stackArg s 2)
    (by brun [exec_ldrSp ho ha2, hB']) (by decide) (by decide) (by decide +kernel))) fun t ⟨hw, h8, k⟩ =>
      ⟨s, hs, h8.trans (congrArg DP.B hs.2), (k.gpr .x4 (by decide)).trans (rdRel_x4 hs),
        (k.gpr .x5 (by decide)).trans (rdRel_x5 hs), hw⟩

/-! ## `fail` -/

/-- Between the zeros of `fail`. -/
def GFr (a : Pub) (s : State) : Prop :=
  ∃ I : RpIn, dpub I = a.1 ∧ Scr s I.B I.Z ∧ s.gpr .x0 = I.B ∧
    RpArgs s.mem I.B I.k I.el I.dl I.pP I.pQ I.pN I.pE I.pD ∧ s.wr = I.W ∧ RpLens I ∧ DOuts I

theorem pins_GFr : Pins GFr [.x0] := fun _ _ _ ⟨_, e₁, _, h₁, _⟩ ⟨_, e₂, _, h₂, _⟩ r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  rw [h₁, h₂]
  exact (congrArg DP.B e₁).trans (congrArg DP.B e₂).symm

theorem zeroOutR_ct {sPtr : Nat} (hP : sPtr < 32) (ptr : DP → Addr)
    (hA : ∀ (I : RpIn) (m : Mem), RpArgs m I.B I.k I.el I.dl I.pP I.pQ I.pN I.pE I.pD → DOuts I →
      word m I.B (8 * sPtr) = ptr (dpub I) ∧
      (∀ i < I.k, InRegions I.W (ptr (dpub I) + BitVec.ofNat 64 i) 1) ∧
      (∀ i < I.k, I.Z ≤ ofs I.B (ptr (dpub I) + BitVec.ofNat 64 i)))
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x1 sPtr, ldh .x2 Public.sK, movi .x3 0]) hc).isSome
      = true) :
    RelCT isa (Two GFr) (zeroOut sPtr Public.sK) (Two GFr) :=
  pin_ct [.x0] [.x1, .x2] (fun a => zoVal (ptr a.1) a.1.k) pins_GFr ht
    (fun ⟨P, i⟩ s h => by
      obtain ⟨I, rfl, hs, h0, ha, -, L, O⟩ := h
      obtain ⟨hp, -⟩ := hA I s.mem ha O
      have hn := hs.nowrap
      have h256 : 8 * 32 ≤ I.Z := by have := L.z; have := L.k1; omega
      have hl' : ∀ i < 32, InRegions (s.rd ++ s.wr) (off I.B (8 * i)) 8 := fun i hi => hs.ld (by omega)
      refine WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun t => t.gpr .x1 = ptr (dpub I) ∧
        t.gpr .x2 = BitVec.ofNat 64 I.k) (by
        brun [h0, hdr_enc hP, hdr_enc (show Public.sK < 32 by decide), hl' sPtr hP,
          hl' Public.sK (by decide)]
        exact ⟨hp, ha.k⟩) rfl rfl rfl)
        fun t ⟨⟨h1, h2⟩, _⟩ r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h1
      · exact h2)
    (by taint_decide) fun ⟨P, i⟩ s h => by
      obtain ⟨I, rfl, hs, h0, ha, hW, L, O⟩ := h
      obtain ⟨hp, hwr, hsep⟩ := hA I s.mem ha O
      have hn := hs.nowrap
      have h256 : 8 * 32 ≤ I.Z := by have := L.z; have := L.k1; omega
      have hk1 := L.k1
      have hk2 := L.k2
      refine WP.mono (zeroOut_ok hs h0 h256 hP (by decide) hp ha.k (by omega) (by omega)
        ⟨fun i hi => by rw [hW]; exact hwr i hi, hsep⟩) fun t ⟨_, hx, k⟩ => ?_
      have fw : ∀ i < 32, word t.mem I.B (8 * i) = word s.mem I.B (8 * i) :=
        fun i hi => (frm_scr hsep hx).word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by omega))
          (by omega)
      exact ⟨I, rfl, hs.congr k.wr, (k.gpr .x0 (by decide)).trans h0, ha.congr fun i hi => fw i (by
        unfold rArg at hi; omega), k.wr.trans hW, L, O⟩

/-- `fail` leaks the same in two runs with the same public data. -/
theorem failR_ct : RelCT isa (Two GFr) fail fun _ _ => True := by
  unfold fail
  refine (ct_cons (by simp) (zeroOutR_ct (by decide) DP.pP (fun I m ha O => ⟨ha.p, O.p, O.sp⟩) (by taint_decide))
    (ct_cons (by simp) (zeroOutR_ct (by decide) DP.pQ (fun I m ha O => ⟨ha.q, O.q, O.sq⟩) (by taint_decide))
    (ct_one (Ψ := fun (_ : Pub) (_ : State) => True) (two_post (two_taint [.x0] pins_GFr (by taint_decide))
      fun _ _ _ => WP.mono (WP.keep [.x0] (Q := fun _ => True) (by brun; exact ⟨_, rfl⟩) rfl rfl rfl)
        fun _ _ => trivial)))).mono (fun _ _ h => h) fun _ _ _ => trivial

/-- `vg_rsa_recover_primes_det` leaks the same in runs with the same public data. -/
theorem rdCode_ct [InvLaw] : RelCT isa (Two RDRel) code fun _ _ => True := by
  unfold code
  refine RelCT.seq (R := Two RD3) (RelCT.block_append (RelCT.seq rdEntry_ct ?_)) ?_
  -- The modulus' check.
  · refine two_piece [.x2, .x3] (fun p s₁ s₂ ⟨σ₁, c₁, h₁⟩ ⟨σ₂, c₂, h₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.x2, h₂.x2, rdRel_x4 c₁, rdRel_x4 c₂]
      · rw [h₁.x3, h₂.x3, ofNat_toNat64, ofNat_toNat64, rdRel_x5 c₁, rdRel_x5 c₂])
      (by taint_decide) ?_
    rintro p t ⟨s, hs, h⟩
    have c := rpCtx_of hs.1.1
    have hnb := c.n.congrK h.inScr h.keep
    have hnl : (rpIn s).nb.length = (s.gpr .x5).toNat := bytesAt_length _ _ _
    refine WP.mono (WP.keep [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] (invalid_ok h.x2 h.x3 c.L.k1 c.L.k2 hnl
      (fun i hi => hnb.rd i (by rw [hnl]; exact hi)) (fun i hi => hnb.val i _))
      (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨hz, hm, _⟩, k⟩ => ⟨s, t, hs, h, hm, k, ?_⟩
    rw [hz, ← hs.2]
    rfl
  -- `fail` or `main`.
  refine two_ite (fun p s₁ s₂ ⟨_, _, _, _, _, _, z₁⟩ ⟨_, _, _, _, _, _, z₂⟩ => by
    rw [eval_zero, eval_zero, z₁, z₂]) ?_ ?_
  · refine failR_ct.mono (fun _ _ h => two_mono (fun p t ⟨⟨s, t₁, hs, h, hm, k, z⟩, hf⟩ => ?_) h) fun _ _ h => h
    have hpre := rpPre_of (rpCtx_of hs.1.1) h hm k
    have e : dpub (rpIn s) = p.1 := hs.2
    have z' : t.gpr .x9 = BitVec.ofNat 64 (Spec.Rsa.modulusValid (Spec.Rsa.os2ip (rpIn s).nb) (rpIn s).k).toNat := by
      rw [z, ← e]; rfl
    rw [eval_zero, z'] at hf
    have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (rpIn s).nb) (rpIn s).k = false := by
      revert hf; cases Spec.Rsa.modulusValid (Spec.Rsa.os2ip (rpIn s).nb) (rpIn s).k <;> simp
    exact ⟨rpIn s, e, hpre.scr, hpre.x0, hpre.args, hpre.wr, hpre.L, ⟨fun i hi => by rw [← hpre.wr]; exact hpre.oP.wr i hi,
      fun i hi => by rw [← hpre.wr]; exact hpre.oQ.wr i hi, hpre.oP.sep, hpre.oQ.sep, hpre.a⟩⟩
  · refine rdMain_ct.mono (fun _ _ h => two_mono (fun p t ⟨⟨s, t₁, hs, h, hm, k, z⟩, hf⟩ => ?_) h) fun _ _ h => h
    have hpre := rpPre_of (rpCtx_of hs.1.1) h hm k
    have e : dpub (rpIn s) = p.1 := hs.2
    have z' : t.gpr .x9 = BitVec.ofNat 64 (Spec.Rsa.modulusValid (Spec.Rsa.os2ip (rpIn s).nb) (rpIn s).k).toNat := by
      rw [z, ← e]; rfl
    rw [eval_zero, z'] at hf
    refine ⟨rpIn s, e, ⟨hpre.scr, hpre.x0, hpre.args, hpre.n, hpre.e, hpre.d, hpre.L, hs.1.2, hpre.oP, hpre.oQ,
      hpre.a, hpre.wr⟩, ?_⟩
    show Spec.Rsa.modulusValid (Spec.Rsa.os2ip (rpIn s).nb) (rpIn s).k = true
    revert hf
    cases Spec.Rsa.modulusValid (Spec.Rsa.os2ip (rpIn s).nb) (rpIn s).k <;> simp

/-- `vg_rsa_recover_primes_det` is constant time but for `n`, `e`, the
pointers and the lengths. -/
theorem rdCode_constantTime [InvLaw] : ConstantTime isa rdA.pre rdA.pub code := by
  refine RelCT.constantTime (rdCode_ct.mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨(dpub (rpIn s₁), 0), ⟨h₁, rfl⟩, ⟨h₂, ?_⟩,
    hp.2.1⟩) fun _ _ h => h)
  obtain ⟨hr, hsp, ha, hn, he⟩ := hp
  have r : ∀ r ∈ argRegs, s₂.gpr r = s₁.gpr r := fun r h => (hr r h).symm
  have a : ∀ j < 4, stackArg s₂ j = stackArg s₁ j := fun j hj => by
    have := congrArg (fun l => l[j]?) ha
    simp only [List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.some.injEq] at this
    exact this.symm
  have w₁ := h₁.1.2.2.1
  have w₂ := h₂.1.2.2.1
  simp only [dpub, rpIn, DP.mk.injEq]
  refine ⟨a 2 (by decide), by rw [a 3 (by decide)], by rw [r .x5 (by decide)], by rw [r .x7 (by decide)],
    by rw [a 1 (by decide)], r .x0 (by decide), r .x2 (by decide), r .x4 (by decide), r .x6 (by decide),
    a 0 (by decide), hn.symm, he.symm, ?_⟩
  rw [w₁, w₂, r .x0 (by decide), r .x1 (by decide), r .x2 (by decide), r .x3 (by decide), a 2 (by decide),
    a 3 (by decide)]

end VG.Proof.Rsa.AArch64.Rd
