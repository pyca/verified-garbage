module

public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Pieces
public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Twos
public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Stages
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
import VerifiedGarbage.Proof.Rsa.X86_64.CvLoad
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Rsa.X86_64.Div
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Prod
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Pieces
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Twos
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Stages
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvLoad
meta import VerifiedGarbage.Proof.Rsa.X86_64.Loops
meta import VerifiedGarbage.Proof.Rsa.X86_64.Inv
meta import VerifiedGarbage.Proof.Rsa.X86_64.Div
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Prod
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Entry
import VerifiedGarbage.Proof.Bignum.X86_64.PubR2
public import VerifiedGarbage.Impl.Rsa.X86_64.RecoverDet
import VerifiedGarbage.Proof.Rsa.Ranges
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Entry
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubR2
meta import VerifiedGarbage.Impl.Rsa.X86_64.RecoverDet
meta import VerifiedGarbage.Proof.Rsa.Ranges
meta import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Rsa.TwosMath
public import VerifiedGarbage.Proof.Rsa.X86_64.InvLaw
public import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Args
import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
import VerifiedGarbage.Proof.Rsa.X86_64.CvCTCode
import VerifiedGarbage.Proof.Rsa.X86_64.CvFail
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Rsa.TwosMath
meta import VerifiedGarbage.Proof.Rsa.X86_64.InvLaw
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Args
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvCTCode
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! ### `Rsa.X86_64.Rd.CTFail`, which this module and modules that import it used -/

section

/-!
# `vg_rsa_recover_primes_det` on x86-64: the public data, and the failure path in constant time

`RpP`: the public data (the working space, the pointers and lengths, `n` and
`e`). The failure path leaks only those (`Rp.failR_ct`), as do the entry
and the check of the modulus (`rpEntry_split`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN)

/-- The public data of `vg_rsa_recover_primes_det`. -/
structure RpP where
  B : Addr
  Z : Nat
  k : Nat
  el : Nat
  dl : Nat
  pP : Addr
  pQ : Addr
  pN : Addr
  pE : Addr
  pD : Addr
  nb : List Byte
  eb : List Byte
  W : List Region
  sp : Addr
  deriving Inhabited

/-- The public part of the inputs. -/
def RpIn.pub (I : RpIn) : RpP :=
  ⟨I.B, I.Z, I.k, I.el, I.dl, I.pP, I.pQ, I.pN, I.pE, I.pD, I.nb, I.eb, I.W, I.sp⟩

/-- The outputs: writable, outside the working space, and apart. -/
structure RpOuts (I : RpIn) : Prop where
  p : ∀ i < I.k, InRegions I.W (I.pP + BitVec.ofNat 64 i) 1
  q : ∀ i < I.k, InRegions I.W (I.pQ + BitVec.ofNat 64 i) 1
  sp : ∀ i < I.k, I.Z ≤ ofs I.B (I.pP + BitVec.ofNat 64 i)
  sq : ∀ i < I.k, I.Z ≤ ofs I.B (I.pQ + BitVec.ofNat 64 i)
  a : Apart I.pP I.k I.pQ I.k

theorem RpPre.outs {I : RpIn} {s : State} (h : RpPre I s) : RpOuts I :=
  ⟨fun i hi => by rw [← h.wr]; exact h.oP.wr i hi, fun i hi => by rw [← h.wr]; exact h.oQ.wr i hi,
    h.oP.sep, h.oQ.sep, h.a⟩

end VG.Proof.Rsa.X86_64

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

namespace Rp

/-! ## `fail` -/

/-- Between the zeros of `fail`. -/
def GFr (p : RpP) (s : State) : Prop :=
  ∃ I : RpIn, I.pub = p ∧ Scr s I.B I.Z ∧ s.gpr .rdi = I.B ∧
    RpArgs s.mem I.B I.k I.el I.dl I.pP I.pQ I.pN I.pE I.pD I.sv ∧ s.wr = I.W ∧ RpLens I ∧ RpOuts I

theorem pins_GFr : Pins GFr [.rdi] := fun _ _ _ ⟨_, e₁, _, h₁, _⟩ ⟨_, e₂, _, h₂, _⟩ r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  rw [h₁, h₂]
  exact (congrArg RpP.B e₁).trans (congrArg RpP.B e₂).symm

theorem zeroOutR_ct {sPtr : Nat} (hP : sPtr < 32) (ptr : RpP → Addr)
    (hA : ∀ p s, GFr p s → word s.mem p.B (8 * sPtr) = ptr p ∧
      (∀ i < p.k, InRegions p.W (ptr p + BitVec.ofNat 64 i) 1) ∧
      (∀ i < p.k, p.Z ≤ ofs p.B (ptr p + BitVec.ofNat 64 i)))
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rsi (.mem (hdr sPtr)),
      .mov .rcx (.mem (hdr Impl.Bignum.X86_64.Public.sK)), .mov32 .rax (.imm 0)]) hc).isSome = true) :
    RelCT isa (Two GFr) (zeroOut sPtr Impl.Bignum.X86_64.Public.sK) (Two GFr) :=
  pin_ct [.rdi] [.rsi, .rcx] (fun p => zoVal (ptr p) p.k) pins_GFr ht
    (fun p s h => by
      obtain ⟨hp, -⟩ := hA p s h
      obtain ⟨I, rfl, hs, hdi, ha, -, L, -⟩ := h
      have hn := hs.nowrap
      have h256 : 8 * 32 ≤ I.Z := by have := L.z; have := L.k1; omega_arith
      have hl' : ∀ i < 32, InRegions (s.rd ++ s.wr) (off I.B (8 * i)) 8 := fun i hi => hs.ld (by omega_arith)
      refine WP.mono (WP.keep [.rsi, .rcx, .rax] (Q := fun t => t.gpr .rsi = ptr I.pub ∧
        t.gpr .rcx = BitVec.ofNat 64 I.k) (by
        xrun [State.ea, hdr, hdi, hdrOff, hl' sPtr hP, hl' Impl.Bignum.X86_64.Public.sK (by decide)]
        exact ⟨hp, ha.k⟩) rfl) fun t ⟨⟨h1, h2⟩, _⟩ r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h1
      · exact h2)
    (by taint_decide) fun p s h => by
      obtain ⟨hp, hwr, hsep⟩ := hA p s h
      obtain ⟨I, rfl, hs, hdi, ha, hW, L, O⟩ := h
      dsimp only [RpIn.pub] at hp hwr hsep ⊢
      have hn := hs.nowrap
      have h256 : 8 * 32 ≤ I.Z := by have := L.z; have := L.k1; omega_arith
      have hk1 := L.k1
      have hk2 := L.k2
      refine WP.mono (zeroOut_ok hs hdi h256 hP (by decide) hp ha.k (by omega_arith) (by omega_arith)
        ⟨fun i hi => by rw [hW]; exact hwr i hi, hsep⟩) fun t ⟨_, hx, k⟩ => ?_
      have fw : ∀ i < 32, word t.mem I.B (8 * i) = word s.mem I.B (8 * i) :=
        fun i hi => (frm_scr hsep hx).word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by omega_arith))
          (by omega_arith)
      exact ⟨I, rfl, hs.congr k.2.2, (k.gpr (by decide)).trans hdi, ha.congr fun i hi => fw i (by
        unfold rArg at hi; omega_arith), k.2.2.trans hW, L, O⟩

/-- `fail` leaks the same in two runs with the same public data. -/
theorem failR_ct : RelCT isa (Two GFr) fail fun _ _ => True := by
  unfold fail
  refine (ct_cons (by simp) (zeroOutR_ct (by decide) RpP.pP (fun p s h => ?_) (by taint_decide))
    (ct_cons (by simp) (zeroOutR_ct (by decide) RpP.pQ (fun p s h => ?_) (by taint_decide))
    (ct_one (Ψ := fun (_ : RpP) (_ : State) => True)
      ((two_taint [.rdi] pins_GFr (by taint_decide)).mono (fun _ _ h => h)
        fun _ _ _ => ⟨default, trivial, trivial⟩)))).mono (fun _ _ h => h) fun _ _ _ => trivial
  all_goals
    obtain ⟨I, rfl, -, -, ha, -, L, O⟩ := h
    dsimp only [RpIn.pub]
  · exact ⟨ha.p, O.p, O.sp⟩
  · exact ⟨ha.q, O.q, O.sq⟩

end Rp

/-! ## The code -/

theorem rpEntry_split : entry ++ ([.mov .rdx (.mem (hdr Impl.Bignum.X86_64.Public.sN)),
    .mov .rcx (.mem (hdr Impl.Bignum.X86_64.Public.sK))] : List Instr) =
    ([.mov .r11 (.mem { base := .rsp, disp := 40 })] : List Instr) ++
      ((entry.drop 1) ++ [.mov .rdx (.mem (hdr Impl.Bignum.X86_64.Public.sN)),
        .mov .rcx (.mem (hdr Impl.Bignum.X86_64.Public.sK))]) := rfl

end VG.Proof.Rsa.X86_64

end

end

/-!
# `vg_rsa_recover_primes_det` on x86-64: constant time, the pieces

The public data is `RpP` of the inputs with `d`
replaced by zeros of its length (`pubD`): its working space, pointers and
lengths, `n` and `e`. Between the pieces of `main`, `GD w F p` holds: `DS`
at the width `w`, the mask a mask, and the facts `F`. Every piece leaks the
same in two runs from `GD w F p` (`*_ct`), and keeps it (`*_gd`), for facts
that writes to the arrays keep (`Arr`), or as the piece's lemma says.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Rd

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.RecoverDet
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Rsa.X86_64 (copyWords)

/-- `I` with `d` replaced by zeros of its length. -/
def fk (I : RpIn) : RpIn := { I with db := List.replicate I.dl 0 }

/-- The public data of `vg_rsa_recover_primes_det`'s inputs. -/
def pubD (I : RpIn) : RpP := (fk I).pub

/-- Between the pieces of `main`, at the width `w k`, with the facts `F`. -/
def GD (w : Nat → Nat) (F : RpIn → State → Prop) (p : RpP) (s : State) : Prop :=
  ∃ (I : RpIn) (m₀ : Mem), pubD I = p ∧ DS I m₀ (w I.k) s ∧ RpLens I ∧ RpOuts I ∧ I.el ≤ 8 ∧
    (∃ c, mw s.mem I.B = mask c) ∧ F I s

/-- Facts that writes to the offsets `Q` (below `Z`) keep. -/
def Stab (F : RpIn → State → Prop) (Q : Nat → Prop) : Prop :=
  ∀ (I : RpIn) (s t : State) (P : Nat → Prop), F I s → FrmP I.B P s.mem t.mem →
    (∀ y, P y → Q y ∧ y < I.Z) → t.rd = s.rd → t.wr = s.wr → F I t

/-- Facts that writes to the arrays keep. -/
abbrev Arr (F : RpIn → State → Prop) : Prop := Stab F fun y => 256 ≤ y

theorem stab_true {Q : Nat → Prop} : Stab (fun _ _ => True) Q := fun _ _ _ _ _ _ _ _ _ => trivial

/-- A header word, which writes elsewhere keep. -/
theorem stab_hdr {i : Nat} (hi : i < 32) (v : RpIn → BitVec 64) {Q : Nat → Prop}
    (hQ : ∀ y, Q y → y < 8 * i ∨ 8 * i + 8 ≤ y) : Stab (fun I s => word s.mem I.B (8 * i) = v I) Q :=
  fun _ _ _ _ h hf hP _ _ => (hf.word_eq (fun y h1 h2 hy => by have := hQ y (hP y hy).1; omega_arith)
    (by omega_arith)).trans h

theorem Stab.and {F G : RpIn → State → Prop} {Q : Nat → Prop} (hF : Stab F Q) (hG : Stab G Q) :
    Stab (fun I s => F I s ∧ G I s) Q :=
  fun I s t P h hf hP h1 h2 => ⟨hF I s t P h.1 hf hP h1 h2, hG I s t P h.2 hf hP h1 h2⟩


theorem GD.ws {w : Nat → Nat} {F : RpIn → State → Prop} {p : RpP} {s : State} (h : GD w F p s) :
    Ws s p.B p.Z (w p.k) := by
  obtain ⟨I, m₀, rfl, h, -⟩ := h
  exact h.ws

theorem pins_GD {w : Nat → Nat} {F : RpIn → State → Prop} : Pins (GD w F) [.rdi] := fun _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ws.rdi, h₂.ws.rdi]

theorem GD.mono {w : Nat → Nat} {F F' : RpIn → State → Prop} {p : RpP} {s : State} (h : GD w F p s)
    (hF : ∀ I, pubD I = p → F I s → F' I s) : GD w F' p s := by
  obtain ⟨I, m₀, e, h, L, O, he, hm, hF₀⟩ := h
  exact ⟨I, m₀, e, h, L, O, he, hm, hF I e hF₀⟩

/-- `GD` after a piece that changes only offsets that `DOk` allows. -/
theorem GD.next {w : Nat → Nat} {F F' : RpIn → State → Prop} {p : RpP} {s t : State} (h : GD w F p s)
    {P : Nat → Prop} (hf : FrmP p.B P s.mem t.mem) (hP : ∀ y, P y → DOk y ∧ y < p.Z) {regs : List Reg}
    (k : Keep regs s t) (hr : .rdi ∉ regs ∧ .rsp ∉ regs)
    (hm : ∀ c, mw s.mem p.B = mask c → ∃ c', mw t.mem p.B = mask c')
    (hF : ∀ I, pubD I = p → F I s → F' I t) : GD w F' p t := by
  obtain ⟨I, m₀, rfl, h, L, O, he, ⟨c, hc⟩, hF₀⟩ := h
  exact ⟨I, m₀, rfl, h.step hf hP k hr, L, O, he, hm c hc, hF I rfl hF₀⟩

/-- The mask, after writes that miss it. -/
theorem mw_frm {B : Addr} {P : Nat → Prop} {m m' : Mem} (hf : FrmP B P m m') (hP : ∀ y, P y → 256 ≤ y) :
    mw m' B = mw m B :=
  hf.word_eq (fun y h1 h2 hy => by have := hP y hy; simp only [Impl.Bignum.X86_64.Public.sMask, sFn] at h2; omega_arith)
    (by simp only [Impl.Bignum.X86_64.Public.sMask, sFn]; omega_arith)

/-- `GD` after a piece that changes only arrays. -/
theorem GD.arr {w : Nat → Nat} {F : RpIn → State → Prop} {p : RpP} {s t : State} (h : GD w F p s)
    {P : Nat → Prop} (hf : FrmP p.B P s.mem t.mem) (hP : ∀ y, P y → 256 ≤ y ∧ y < p.Z) {regs : List Reg}
    (k : Keep regs s t) (hr : .rdi ∉ regs ∧ .rsp ∉ regs) (hF : Arr F) : GD w F p t := by
  obtain ⟨I, m₀, rfl, h, L, O, he, ⟨c, hc⟩, hF₀⟩ := h
  exact ⟨I, m₀, rfl, h.step hf (fun y hy => ⟨.inl (hP y hy).1, (hP y hy).2⟩) k hr, L, O, he,
    ⟨c, (mw_frm hf fun y hy => (hP y hy).1).trans hc⟩, hF I s t P hF₀ hf hP k.2.1 k.2.2⟩

/-- `GD` after a piece that changes only `n` bytes from array `j`. -/
theorem GD.out {w : Nat → Nat} {F : RpIn → State → Prop} {p : RpP} {s t : State} (h : GD w F p s)
    {o n : Nat} (ho : Outside p.B o n s.mem t.mem) (h256 : 256 ≤ o) (hon : o + n ≤ p.Z) {regs : List Reg}
    (k : Keep regs s t) (hr : .rdi ∉ regs ∧ .rsp ∉ regs) (hF : Arr F) : GD w F p t :=
  h.arr (FrmP.of_out ho fun _ h1 h2 => ⟨h1, h2⟩) (P := fun y => o ≤ y ∧ y < o + n)
    (fun _ hy => ⟨by have := hy.1; omega_arith, by have := hy.2; omega_arith⟩)
    k hr hF

/-- `GD` after a piece that changes nothing in memory. -/
theorem GD.same {w : Nat → Nat} {F : RpIn → State → Prop} {p : RpP} {s t : State} (h : GD w F p s)
    (hm : t.mem = s.mem) {regs : List Reg} (k : Keep regs s t) (hr : .rdi ∉ regs ∧ .rsp ∉ regs) (hF : Arr F) :
    GD w F p t :=
  h.arr (P := fun _ => False) (FrmP.of_eq hm) (fun _ h => h.elim) k hr hF

/-! ## The pieces over arrays -/

section
variable {w : Nat → Nat} {F : RpIn → State → Prop}

theorem slot_Z {p : RpP} {s : State} (h : GD w F p s) {j : Nat} (hj : j < 16) :
    slot (w p.k) j + 8 * (w p.k + 2) ≤ p.Z := h.ws.sl hj


theorem zeroA_gd {j : Nat} (hj : j < 16) (hF : Arr F) (p : RpP) (s : State) (h : GD w F p s) :
    WP isa (zeroA j) s (GD w F p) :=
  WP.mono (zeroA_ok h.ws hj) fun _ ⟨_, o, k⟩ => h.out o (slot_256 _ _) (slot_Z h hj) k (by decide) hF

theorem zeroA_ct {j : Nat} (hj : j < 16) (hF : Arr F) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .r8)) zeroAccLoop) hc).isSome = true) :
    RelCT isa (Two (GD w F)) (zeroA j) (Two (GD w F)) :=
  ws_ct RpP.B RpP.Z (fun p => w p.k) (fun _ _ h => h.ws) ht (zeroA_gd hj hF)

theorem copyA_gd {o a : Nat} (ho : o < 16) (ha : a < 16) (hoa : o ≠ a) (hF : Arr F) (p : RpP) (s : State)
    (h : GD w F p s) : WP isa (copyA o a) s (GD w F p) :=
  WP.mono (copyA_ok h.ws ho ha hoa) fun _ ⟨_, o', k⟩ =>
    h.out o' (slot_256 _ _) (by have := slot_Z h ho; omega_arith) k (by decide) hF

theorem copyA_ct {o a : Nat} (ho : o < 16) (ha : a < 16) (hoa : o ≠ a) (hF : Arr F)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base a .rsi ++ base o .rbx)) copyWords)
      hc).isSome = true) :
    RelCT isa (Two (GD w F)) (copyA o a) (Two (GD w F)) := by
  have e : copyA o a = .seq (.block (ws ++ (base a .rsi ++ base o .rbx))) copyWords := by
    simp only [copyA, List.append_assoc]
  rw [e]
  exact ws_ct RpP.B RpP.Z (fun p => w p.k) (fun _ _ h => h.ws) ht fun p s h => by
    rw [← e]; exact copyA_gd ho ha hoa hF p s h

/-- `GD` and `rbp` a mask. -/
def GR (w : Nat → Nat) (F : RpIn → State → Prop) (p : RpP) (s : State) : Prop :=
  GD w F p s ∧ ∃ c, s.gpr .rbp = mask c

theorem pins_GR {w : Nat → Nat} {F : RpIn → State → Prop} : Pins (GR w F) [.rdi] := fun _ _ _ h₁ h₂ r hr =>
  pins_GD _ _ _ h₁.1 h₂.1 r hr

theorem subA_gd {t a b : Nat} (ht : t < 16) (ha : a < 16) (hb : b < 16) (hta : t ≠ a) (htb : t ≠ b) (hF : Arr F)
    (p : RpP) (s : State) (h : GD w F p s) : WP isa (subA t a b) s (GR w F p) :=
  WP.mono (subA_ok h.ws ht ha hb hta htb) fun _ ⟨hbp, _, o, k⟩ =>
    ⟨h.out o (slot_256 _ _) (by have := slot_Z h ht; omega_arith) k (by decide) hF, _, hbp⟩

theorem subA_eq (t a b : Nat) : subA t a b = .seq (.block (ws ++ (([.mov32 .rbp (.imm 0)] : List Instr) ++
    base a .r8 ++ base b .r10 ++ base t .rsi))) (wordLoop 0 subBody) := by
  simp only [subA, List.append_assoc]

theorem subA_ct {t a b : Nat} (ht' : t < 16) (ha : a < 16) (hb : b < 16) (hta : t ≠ a) (htb : t ≠ b) (hF : Arr F)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (([.mov32 .rbp (.imm 0)] : List Instr) ++
      base a .r8 ++ base b .r10 ++ base t .rsi)) (wordLoop 0 subBody)) hc).isSome = true) :
    RelCT isa (Two (GD w F)) (subA t a b) (Two (GR w F)) := by
  rw [subA_eq]
  exact ws_ct RpP.B RpP.Z (fun p => w p.k) (fun _ _ h => h.ws) ht fun p s h => by
    rw [← subA_eq]; exact subA_gd ht' ha hb hta htb hF p s h

theorem addA_gd {o a b : Nat} (ho : o < 16) (ha : a < 16) (hb : b < 16) (hoa : o ≠ a) (hob : o ≠ b) (hF : Arr F)
    (p : RpP) (s : State) (h : GD w F p s) : WP isa (addA o a b) s (GD w F p) :=
  WP.mono (addA_ok h.ws ho ha hb hoa hob) fun _ ⟨_, o', k⟩ =>
    h.out o' (slot_256 _ _) (by have := slot_Z h ho; omega_arith) k (by decide) hF

theorem addA_eq (o a b : Nat) : addA o a b = .seq (.block (ws ++ (([.mov .r15 (.imm (BitVec.ofInt 32 (-1))),
    .mov32 .rbp (.imm 0)] : List Instr) ++ base b .r10 ++ base a .r8 ++ base o .rbx))) (wordLoop 0 addMBody) := by
  simp only [addA, List.append_assoc]

theorem addA_ct {o a b : Nat} (ho : o < 16) (ha : a < 16) (hb : b < 16) (hoa : o ≠ a) (hob : o ≠ b) (hF : Arr F)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (([.mov .r15 (.imm (BitVec.ofInt 32 (-1))),
      .mov32 .rbp (.imm 0)] : List Instr) ++ base b .r10 ++ base a .r8 ++ base o .rbx)) (wordLoop 0 addMBody))
      hc).isSome = true) :
    RelCT isa (Two (GD w F)) (addA o a b) (Two (GD w F)) := by
  rw [addA_eq]
  exact ws_ct RpP.B RpP.Z (fun p => w p.k) (fun _ _ h => h.ws) ht fun p s h => by
    rw [← addA_eq]; exact addA_gd ho ha hb hoa hob hF p s h

end

/-! ## More pieces -/

section
variable {w : Nat → Nat} {F : RpIn → State → Prop}

/-- `ws_ct` from any predicate that gives `GD`. -/
theorem wsG_ct {Φ Ψ : RpP → State → Prop} (hΦ : ∀ p s, Φ p s → GD w F p s) {rest : List Instr}
    {body : Prog isa} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block rest) body) hc).isSome = true)
    (hw : ∀ p s, Φ p s → WP isa (.seq (.block (ws ++ rest)) body) s (Ψ p)) :
    RelCT isa (Two Φ) (.seq (.block (ws ++ rest)) body) (Two Ψ) :=
  ws_ct RpP.B RpP.Z (fun p => w p.k) (fun p s h => (hΦ p s h).ws) ht hw

/-- `ws_block_ct` from any predicate that gives `GD`. -/
theorem wsG_block_ct {Φ Ψ : RpP → State → Prop} (hΦ : ∀ p s, Φ p s → GD w F p s) {rest : List Instr}
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block rest) hc).isSome = true)
    (hw : ∀ p s, Φ p s → WP isa (.block (ws ++ rest)) s (Ψ p)) :
    RelCT isa (Two Φ) (.block (ws ++ rest)) (Two Ψ) :=
  ws_block_ct RpP.B RpP.Z (fun p => w p.k) (fun p s h => (hΦ p s h).ws) ht hw

/-- `shrA`, for what it changes. -/
theorem shrA_frm {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j : Nat} (hj : j < 16) :
    WP isa (shrA j) s fun s' => Outside B (slot w j) (8 * w) s.mem s'.mem ∧
      Keep [.r12, .r9, .r8, .rsi, .rax, .rdx, .r14] s s' := by
  have hn := h.scr.nowrap
  have sj := h.sl hj
  have hw1 := h.w1
  have hw2 := h.w2
  unfold shrA
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ =>
    WP.mono (base2_ok j j (r₁ := .r8) (r₂ := .rsi) (w := w) (by decide) (by decide) (by decide)
      ((k₁.gpr (by decide)).trans h.rdi) h9 (by decide)) fun s₂ ⟨h8, hsi, m₂, k₂⟩ => ?_))
  refine WP.mono (shr_ok (h.scr.congr (k₁.trans k₂).2.2) hsi h8 ((k₂.gpr (by decide)).trans h12) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (.inl (Nat.le_refl _))) fun t ⟨_, ho, k₃⟩ => ?_
  rw [m₂, m₁] at ho
  exact ⟨ho, ((k₁.trans k₂).trans k₃).mono (by simp)⟩

theorem shrA_eq (j : Nat) : shrA j = .seq (.block (ws ++ (base j .r8 ++ base j .rsi))) (wordLoop 0 shrBody) := by
  simp only [shrA, List.append_assoc]

theorem shrA_gd {j : Nat} (hj : j < 16) (hF : Arr F) (p : RpP) (s : State) (h : GD w F p s) :
    WP isa (shrA j) s (GD w F p) :=
  WP.mono (shrA_frm h.ws hj) fun _ ⟨o, k⟩ =>
    h.out o (slot_256 _ _) (by have := slot_Z h hj; omega_arith) k (by decide) hF

theorem shrA_ct {j : Nat} (hj : j < 16) (hF : Arr F) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .r8 ++ base j .rsi))
      (wordLoop 0 shrBody)) hc).isSome = true) :
    RelCT isa (Two (GD w F)) (shrA j) (Two (GD w F)) := by
  rw [shrA_eq]
  exact wsG_ct (fun _ _ h => h) ht fun p s h => by rw [← shrA_eq]; exact shrA_gd hj hF p s h

/-- What `shlA`'s `pre` needs. -/
def ShlPre (pre : List Instr) (c₀ : Bool) (s : State) : Prop :=
  ∀ t : State, t.mem = s.mem → t.gpr .rbp = s.gpr .rbp → t.gpr .rdi = s.gpr .rdi → t.rd = s.rd →
    t.wr = s.wr → WP isa (.block pre) t fun t' => (t'.gpr .rbp = mask c₀ ∧ t'.mem = t.mem) ∧ Keep [.rbp] t t'

theorem shlPre_zero (s : State) : ShlPre [.mov32 .rbp (.imm 0)] false s := fun _ _ _ _ _ _ =>
  WP.keep [.rbp] (Q := fun t' => t'.gpr .rbp = mask false ∧ _) (by xrun) rfl

theorem shlA_eq (wide : Bool) (j : Nat) (pre : List Instr) : shlA wide j pre =
    .seq (.block (ws ++ ((if wide then wideR else []) ++ (base j .rbx ++ pre)))) (wordLoop 0 shlBody) := by
  simp only [shlA, List.append_assoc]

theorem shlA_gd {Φ : RpP → State → Prop} (hΦ : ∀ p s, Φ p s → GD w F p s) (wide : Bool) {j : Nat}
    {pre : List Instr} (hj : j + (if wide then 2 else 1) ≤ 16) (hF : Arr F)
    (hpre : ∀ p s, Φ p s → ∃ c₀, ShlPre pre c₀ s) (p : RpP) (s : State) (h : Φ p s) :
    WP isa (shlA wide j pre) s (GR w F p) := by
  have g := hΦ p s h
  obtain ⟨c₀, hp⟩ := hpre p s h
  refine WP.mono (shlA_ok g.ws wide hj hp) fun t ⟨c, hc, _, o, k⟩ => ⟨g.out o (slot_256 _ _) ?_ k (by decide) hF, c, hc⟩
  have r1 := slot_room (w := w p.k) hj
  have r2 := g.ws.hZ
  cases wide <;> simp only [shlN, ↓reduceIte, Bool.false_eq_true] at r1 ⊢ <;> omega_arith

theorem shlA_ct {Φ : RpP → State → Prop} (hΦ : ∀ p s, Φ p s → GD w F p s) (wide : Bool) {j : Nat}
    {pre : List Instr} (hj : j + (if wide then 2 else 1) ≤ 16) (hF : Arr F)
    (hpre : ∀ p s, Φ p s → ∃ c₀, ShlPre pre c₀ s) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block ((if wide then wideR else []) ++
      (base j .rbx ++ pre))) (wordLoop 0 shlBody)) hc).isSome = true) :
    RelCT isa (Two Φ) (shlA wide j pre) (Two (GR w F)) := by
  rw [shlA_eq]
  exact wsG_ct hΦ ht fun p s h => by rw [← shlA_eq]; exact shlA_gd hΦ wide hj hF hpre p s h

/-- A select, `[j] := keep ? [j] : [o]`, for the mask that `pre` leaves. -/
theorem sel_gd {Φ : RpP → State → Prop} (hΦ : ∀ p s, Φ p s → GD w F p s) (wide : Bool) {j o : Nat}
    (hj : j + (if wide then 2 else 1) ≤ 16) (ho : o + (if wide then 2 else 1) ≤ 16)
    (hjo : ∀ w, slot w j + 8 * shlN wide w ≤ slot w o ∨ slot w o + 8 * shlN wide w ≤ slot w j) {pre : List Instr}
    (hF : Arr F) (hpre : ∀ p s, Φ p s → ∃ keep, MaskPre p.B p.Z s.mem pre keep) (p : RpP) (s : State) (h : Φ p s) :
    WP isa (.seq (.block (ws ++ (if wide then wideR else []) ++ base j .r8 ++ base o .rsi ++ pre))
      (wordLoop 0 selBody)) s (GD w F p) := by
  have g := hΦ p s h
  obtain ⟨keep, hp⟩ := hpre p s h
  refine WP.mono (selPre_ok g.ws wide hj ho (hjo _) hp) fun t ⟨_, o', k⟩ => g.out o' (slot_256 _ _) ?_ k (by decide) hF
  have r1 := slot_room (w := w p.k) hj
  have r2 := g.ws.hZ
  cases wide <;> simp only [shlN, ↓reduceIte, Bool.false_eq_true] at r1 ⊢ <;> omega_arith

theorem eqA_gd {a b : Nat} (ha : a < 16) (hb : b < 16) (hF : Arr F) (p : RpP) (s : State) (h : GD w F p s) :
    WP isa (seqs (eqA a b)) s (GD w F p) :=
  WP.mono (eqA_ok h.ws ha hb) fun _ ⟨_, hm, k⟩ => h.same hm k (by decide) hF

theorem eqA_ct {a b : Nat} (ha : a < 16) (hb : b < 16) (hF : Arr F) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base a .rbx ++ (base b .r10 ++
      ([.mov32 .rbp (.imm 0)] : List Instr)))) (wordLoop 0 xorBody)) hc).isSome = true) :
    RelCT isa (Two (GD w F)) (seqs (eqA a b)) (Two (GD w F)) := by
  have e : seqs (eqA a b) = .seq (.block (ws ++ (base a .rbx ++ (base b .r10 ++
      ([.mov32 .rbp (.imm 0)] : List Instr))))) (wordLoop 0 xorBody) := by
    simp only [eqA, seqs, List.append_assoc]
  rw [e]
  exact wsG_ct (fun _ _ h => h) ht fun p s h => by rw [← e]; exact eqA_gd ha hb hF p s h

/-- `GD` after a store to a header slot the pieces may change. -/
theorem GD.hdrW {F' : RpIn → State → Prop} {p : RpP} {s t : State} (h : GD w F p s) {i : Nat}
    {v : BitVec 64} (hm : t.mem = s.mem.writeW (off p.B (8 * i)) v) (hi : DOk (8 * i)) (hi' : i < 32)
    {regs : List Reg} (k : Keep regs s t) (hr : .rdi ∉ regs ∧ .rsp ∉ regs)
    (hmw : i = Impl.Bignum.X86_64.Public.sMask → ∃ c, v = mask c)
    (hF : ∀ I, pubD I = p → F I s → F' I t) : GD w F' p t := by
  have hn := h.ws.scr.nowrap
  have h256 := h.ws.h256
  have hf : FrmP p.B (fun y => 8 * i ≤ y ∧ y < 8 * i + 8) s.mem t.mem := by
    rw [hm]; exact FrmP.of_writeW _ (by omega_arith) fun _ h1 h2 => ⟨h1, h2⟩
  refine h.next hf (fun y hy => ⟨by unfold DOk at hi ⊢; omega_arith, by omega_arith⟩) k hr (fun c hc => ?_) hF
  by_cases e : i = Impl.Bignum.X86_64.Public.sMask
  · obtain ⟨c', hc'⟩ := hmw e
    subst e
    exact ⟨c', by unfold mw; rw [hm, word_writeW_self, hc']⟩
  · refine ⟨c, (hf.word_eq (fun y h1 h2 hy => ?_) (by simp only [Impl.Bignum.X86_64.Public.sMask, sFn]; omega_arith)).trans hc⟩
    simp only [Impl.Bignum.X86_64.Public.sMask, sFn] at e h1 h2
    omega_arith

/-- A stored header word, and facts the store keeps. -/
theorem stab_writeW {F : RpIn → State → Prop} {I : RpIn} {s t : State} {i : Nat} {v : BitVec 64}
    (hF : Stab F fun y => 8 * i ≤ y ∧ y < 8 * i + 8) (hi : 256 ≤ I.Z) (hi' : i < 32) (h : F I s)
    (hm : t.mem = s.mem.writeW (off I.B (8 * i)) v) (h1 : t.rd = s.rd) (h2 : t.wr = s.wr) :
    F I t ∧ word t.mem I.B (8 * i) = v :=
  ⟨hF I s t _ h (by rw [hm]; exact FrmP.of_writeW _ (by omega_arith) fun _ h1 h2 => ⟨h1, h2⟩)
    (fun y hy => ⟨hy, by omega_arith⟩) h1 h2, by rw [hm, word_writeW_self]⟩

theorem andZero_gd (hF : Stab F fun y => 176 ≤ y ∧ y < 184) (p : RpP) (s : State) (h : GD w F p s) :
    WP isa (.block CrtValues.andZero) s (GD w F p) := by
  obtain ⟨I, m₀, e, h', L, O, he, ⟨c, hc⟩, hF₀⟩ := id h
  subst e
  exact WP.mono (andZero_ok (z := s.gpr .rbp = 0) h'.ws hc Iff.rfl) fun t ⟨hm, k⟩ =>
    h.hdrW hm (by unfold DOk; simp only [Impl.Bignum.X86_64.Public.sMask, sFn]; omega_arith) (by decide) k (by decide)
      (fun _ => ⟨_, rfl⟩) fun J e hJ => by
        have eB : J.B = I.B := congrArg RpP.B e
        have eZ : J.Z = I.Z := congrArg RpP.Z e
        exact (stab_writeW (i := Impl.Bignum.X86_64.Public.sMask) hF (by rw [eZ]; exact h'.ws.h256) (by decide) hJ
          (by rw [eB]; exact hm) k.2.1 k.2.2).1

theorem andZero_ct (hF : Stab F fun y => 176 ≤ y ∧ y < 184) :
    RelCT isa (Two (GD w F)) (.block CrtValues.andZero) (Two (GD w F)) :=
  two_piece [.rdi] pins_GD (by taint_decide) (andZero_gd hF)

theorem andNz_gd (hF : Stab F fun y => 176 ≤ y ∧ y < 184) (p : RpP) (s : State) (h : GR w F p s) :
    WP isa (.block andNz) s (GD w F p) := by
  obtain ⟨⟨I, m₀, e, h', L, O, he, ⟨c, hc⟩, hF₀⟩, b, hb⟩ := id h
  subst e
  exact WP.mono (andNz_ok h'.ws hc hb) fun t ⟨hm, k⟩ =>
    h.1.hdrW hm (by unfold DOk; simp only [Impl.Bignum.X86_64.Public.sMask, sFn]; omega_arith) (by decide) k
      (by decide) (fun _ => ⟨_, rfl⟩) fun J e hJ => by
        have eB : J.B = I.B := congrArg RpP.B e
        have eZ : J.Z = I.Z := congrArg RpP.Z e
        exact (stab_writeW (i := Impl.Bignum.X86_64.Public.sMask) hF (by rw [eZ]; exact h'.ws.h256) (by decide) hJ
          (by rw [eB]; exact hm) k.2.1 k.2.2).1

theorem andNz_ct (hF : Stab F fun y => 176 ≤ y ∧ y < 184) :
    RelCT isa (Two (GR w F)) (.block andNz) (Two (GD w F)) :=
  two_piece [.rdi] pins_GR (by taint_decide) (andNz_gd hF)

theorem setOneA_gd {j : Nat} (hj : j < 16) (hF : Arr F) (p : RpP) (s : State) (h : GD w F p s) :
    WP isa (.block (setOneA j)) s (GD w F p) := by
  have hw := h.ws
  refine WP.mono (setOneA_ok hw hj) fun t ⟨hm, k⟩ => ?_
  have sl := slot_Z h hj
  have o := writeW_outside s.mem p.B (1 : BitVec 64) (d := slot (w p.k) j) (by have := hw.scr.nowrap; omega_arith)
  rw [← hm] at o
  exact h.out o (slot_256 _ _) (by omega_arith) k (by decide) hF

theorem setOneA_ct {j : Nat} (hj : j < 16) (hF : Arr F) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block (base j .rbx ++ ([.mov32 .rax (.imm 1),
      .store (at0 .rbx) .rax] : List Instr))) hc).isSome = true) :
    RelCT isa (Two (GD w F)) (.block (setOneA j)) (Two (GD w F)) := by
  have e : setOneA j = ws ++ (base j .rbx ++ ([.mov32 .rax (.imm 1), .store (at0 .rbx) .rax] : List Instr)) := by
    simp only [setOneA, List.append_assoc]
  rw [e]
  exact wsG_block_ct (fun _ _ h => h) ht fun p s h => by rw [← e]; exact setOneA_gd hj hF p s h

/-- `GD` after a piece that changes only the ranges `rs`, of the arrays. -/
theorem GD.frm {p : RpP} {s t : State} (h : GD w F p s) {rs : List (Nat × Nat)} (hf : Frm p.B rs s.mem t.mem)
    (hrs : ∀ r ∈ rs, 256 ≤ r.1 ∧ r.1 + r.2 ≤ p.Z) {regs : List Reg} (k : Keep regs s t)
    (hr : .rdi ∉ regs ∧ .rsp ∉ regs) (hF : Arr F) : GD w F p t :=
  h.arr (P := fun y => ∃ r ∈ rs, r.1 ≤ y ∧ y < r.1 + r.2) (FrmP.of_frm hf fun r hr y h1 h2 => ⟨r, hr, h1, h2⟩)
    (fun y ⟨r, hr, h1, h2⟩ => by have := hrs r hr; omega_arith) k hr hF

theorem gcdW_gd [InvLaw] {iU iV iM : Nat} (hZ26 : ∀ p s, GD w F p s → slot (w p.k) 26 ≤ p.Z)
    (hw20 : ∀ p s, GD w F p s → w p.k < 2 ^ 20) (hU : iU < 16) (hV : iV < 16) (hM : iM < 16)
    (hF : Arr F) (p : RpP) (s : State) (h : GD w F p s) :
    WP isa (gcdW iU iV iM) s (GD w F p) := by
  refine WP.mono (gcdW_ok h.ws (hZ26 p s h) (hw20 p s h) hU hV hM) fun t ⟨f, k, _⟩ =>
    h.frm f (fun r hr => ?_) k (by decide) hF
  have z26 := hZ26 p s h
  have l26 := slot_lin (w p.k) 26
  have l16 := slot_lin (w p.k) 16
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨slot_256 _ _, by have := slot_Z h hV; dsimp only; omega_arith⟩
  · exact ⟨slot_256 _ _, by dsimp only; omega_arith⟩

theorem gcdW_ct [InvLaw] {iU iV iM : Nat} (hZ26 : ∀ p s, GD w F p s → slot (w p.k) 26 ≤ p.Z)
    (hw20 : ∀ p s, GD w F p s → w p.k < 2 ^ 20) (hU : iU < 16) (hV : iV < 16) (hM : iM < 16)
    (hF : Arr F) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block ([.mov .r13 (.reg .r12)] : List Instr))
      (gcdN iU iV iM)) hc).isSome = true) :
    RelCT isa (Two (GD w F)) (gcdW iU iV iM) (Two (GD w F)) := by
  have e : gcdW iU iV iM = .seq (.block (ws ++ ([.mov .r13 (.reg .r12)] : List Instr)))
      (gcdN iU iV iM) := rfl
  rw [e]
  exact wsG_ct (fun _ _ h => h) ht fun p s h => by
    rw [← e]; exact gcdW_gd hZ26 hw20 hU hV hM hF p s h

end

end VG.Proof.Rsa.X86_64.Rd
