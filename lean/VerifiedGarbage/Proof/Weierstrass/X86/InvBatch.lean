module

import VerifiedGarbage.Proof.Weierstrass.X86.InvLayout
import VerifiedGarbage.Proof.Weierstrass.X86.InvHalf
public import VerifiedGarbage.Proof.X25519.X86.Column
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
import VerifiedGarbage.Proof.Weierstrass.X86.InvRead
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import VerifiedGarbage.Impl.Weierstrass.X86.InvCfg
public import VerifiedGarbage.Proof.Divstep.Word32Def
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Loop
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Weierstrass.X86.InvLinear
public import VerifiedGarbage.Proof.Weierstrass.X86.InvState
public import VerifiedGarbage.TCB.Mem
public import VerifiedGarbage.Proof.Weierstrass.MontContract
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Proof.Weierstrass.X86.InvClob
import VerifiedGarbage.Proof.Weierstrass.X86.InvCount
import Mathlib.Data.BitVec
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
public import VerifiedGarbage.Proof.Divstep.BatchBasic

/-! ### `Weierstrass.X86.InvFg`, which only this module used -/

section

/-! # Applying both matrix rows to the signed divstep values -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

local macro "apart" : tactic => `(tactic|
  plain_simp_names ((try simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
                     InvCfg.sF, InvCfg.sG, InvCfg.sA, InvCfg.sB, InvCfg.sNF, InvCfg.sNG, InvCfg.sT, InvCfg.sU, InvCfg.sW]) <;> omega_arith))

theorem fgUpdate_ok {P : InvCfg} {s : State} {base : Addr} {size p : Nat} {T : Divstep.MSt} {f g : Int}
    (hs : Scr s base size) (ht : P.tbl + 320 ≤ size) (hT : MatrixAt P base T s)
    (huv : |T.u| + |T.v| ≤ 2 ^ 30) (hqr : |T.q| + |T.r| ≤ 2 ^ 30)
    (hf : (val32 s.mem base P.sF 9 : Int) % 2 ^ 288 = f % 2 ^ 288)
    (hg : (val32 s.mem base P.sG 9 : Int) % 2 ^ 288 = g % 2 ^ 288)
    (hfb : |f| ≤ p) (hgb : |g| ≤ p) (hp : p < 2 ^ 256)
    (hdivF : 2 ^ 30 ∣ T.u * f + T.v * g) (hdivG : 2 ^ 30 ∣ T.q * f + T.r * g) :
    WP isa (.block P.fgUpdate) s fun z =>
      (val32 z.mem base P.sF 9 : Int) % 2 ^ 288 = ((T.u * f + T.v * g) / 2 ^ 30) % 2 ^ 288 ∧
      (val32 z.mem base P.sG 9 : Int) % 2 ^ 288 = ((T.q * f + T.r * g) / 2 ^ 30) % 2 ^ 288 ∧
      Keeps clob s z ∧ Outside base P.tbl 288 s.mem z.mem ∧
      val32 z.mem base P.sA 8 = val32 s.mem base P.sA 8 ∧
      val32 z.mem base P.sB 8 = val32 s.mem base P.sB 8 := by
  have hn := hs.nowrap
  obtain L₁ : LinearLay size (P.sW + 12) (P.sW + 16) P.sT P.sF P.sG P.sU 9 7 := by
    simpa only [Nat.mul_zero, Nat.add_zero] using fgLayout ht (row := 0) (by decide)
  obtain L₂ : LinearLay size (P.sW + 20) (P.sW + 24) P.sT P.sF P.sG P.sU 9 7 := by
    simpa only [Nat.mul_one, Nat.add_assoc, Nat.reduceAdd] using fgLayout ht (row := 1) (by decide)
  unfold InvCfg.fgUpdate
  rw [show VG.Impl.Weierstrass.X86.Inv.linear (P.sW + 12) (P.sW + 16) P.sT P.sF P.sG P.sU 9 7 ++
      VG.Impl.Weierstrass.X86.Inv.shr30 P.sNF P.sT 9 ++
      VG.Impl.Weierstrass.X86.Inv.linear (P.sW + 20) (P.sW + 24) P.sT P.sF P.sG P.sU 9 7 ++
      VG.Impl.Weierstrass.X86.Inv.shr30 P.sNG P.sT 9 =
      (VG.Impl.Weierstrass.X86.Inv.linear (P.sW + 12) (P.sW + 16) P.sT P.sF P.sG P.sU 9 7 ++
       VG.Impl.Weierstrass.X86.Inv.shr30 P.sNF P.sT 9) ++
      (VG.Impl.Weierstrass.X86.Inv.linear (P.sW + 20) (P.sW + 24) P.sT P.sF P.sG P.sU 9 7 ++
       VG.Impl.Weierstrass.X86.Inv.shr30 P.sNG P.sT 9) by simp only [List.append_assoc]]
  refine WP.block_append (WP.block_append (WP.block_append (WP.mono
    (fHalf_ok hs L₁ (dst := P.sNF) (by apart) (by apart) hT.u hT.v huv hf hg hfb hgb hp hdivF)
    fun s₁ ⟨F₁, K₁, O₁⟩ => ?_)))
  obtain hs₁ := hs.of_keeps K₁ (by decide)
  obtain q₁ : s₁.mem.readW (off base (P.sW + 20)) 32 = BitVec.ofInt 32 T.q := by
    rw [read32_unch O₁ (by apart) (by apart), hT.q]
  obtain r₁ : s₁.mem.readW (off base (P.sW + 24)) 32 = BitVec.ofInt 32 T.r := by
    rw [read32_unch O₁ (by apart) (by apart), hT.r]
  refine WP.mono (fHalf_ok hs₁ L₂ (dst := P.sNG) (by apart) (by apart) q₁ r₁ hqr
    (by rw [Outs.val32 O₁ (by apart) (by apart)]; exact hf)
    (by rw [Outs.val32 O₁ (by apart) (by apart)]; exact hg) hfb hgb hp hdivG)
    fun s₂ ⟨G₂, K₂, O₂⟩ => ?_
  obtain hs₂ := hs₁.of_keeps K₂ (by decide)
  refine WP.mono (copy_ok 9 hs₂ (o := P.sF) (a := P.sNF) (by apart) (by apart) (by apart))
    fun s₃ ⟨F₃, K₃, O₃⟩ => ?_
  obtain hs₃ := hs₂.of_keeps K₃ (by decide)
  refine WP.mono (copy_ok 9 hs₃ (o := P.sG) (a := P.sNG) (by apart) (by apart) (by apart))
    fun z ⟨G₄, K₄, O₄⟩ => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [O₄.val32 (by apart) (by apart), F₃, Outs.val32 O₂ (by apart) (by apart)]
    exact F₁
  · rw [G₄, O₃.val32 (by apart) (by apart)]
    exact G₂
  · exact ((K₁.trans K₂).trans (K₃.mono (by decide))).trans (K₄.mono (by decide))
  · have H₁ : Outside base P.tbl 288 s.mem s₁.mem := O₁.outside (by apart)
    obtain H₂ : Outside base P.tbl 288 s₁.mem s₂.mem := O₂.outside (by apart)
    exact ((H₁.trans H₂).trans (O₃.mono (by apart) (by apart))).trans (O₄.mono (by apart) (by apart))

  · rw [O₄.val32 (by apart) (by apart), O₃.val32 (by apart) (by apart),
      Outs.val32 O₂ (by apart) (by apart), Outs.val32 O₁ (by apart) (by apart)]
  · rw [O₄.val32 (by apart) (by apart), O₃.val32 (by apart) (by apart),
      Outs.val32 O₂ (by apart) (by apart), Outs.val32 O₁ (by apart) (by apart)]

end VG.Proof.Weierstrass.X86.Inv

end

end

/-! ### `Weierstrass.X86.InvAb`, which only this module used -/

section

/-! # Applying both matrix rows to the reduced inverse coefficients -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

local macro "apart" : tactic => `(tactic|
  plain_simp_names ((try simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
                     InvCfg.sF, InvCfg.sG, InvCfg.sA, InvCfg.sB, InvCfg.sNF, InvCfg.sT, InvCfg.sU, InvCfg.sW]) <;> omega_arith))

theorem abUpdate_ok {P : InvCfg} {s : State} {base : Addr} {size p : Nat} {T : Divstep.MSt} {a b : Int}
    (hs : Scr s base size) (L : WorkLay P size) (hT : MatrixAt P base T s)
    (huv : |T.u| + |T.v| ≤ 2 ^ 30) (hqr : |T.q| + |T.r| ≤ 2 ^ 30)
    (hp : 0 < p) (hm : val32 s.mem base P.M.mo 8 = p)
    (hinv : (p * (minv32 P.M).toNat + 1) % 2 ^ 32 = 0)
    (ha : (val32 s.mem base P.sA 8 : Int) = a) (hb : (val32 s.mem base P.sB 8 : Int) = b)
    (hab : |a| ≤ p) (hbb : |b| ≤ p) :
    WP isa (.block P.abUpdate) s fun z =>
      (val32 z.mem base P.sA 8 : Int) = Divstep.W32.mred p (minv32 P.M).toNat (T.u * a + T.v * b) ∧
      (val32 z.mem base P.sB 8 : Int) = Divstep.W32.mred p (minv32 P.M).toNat (T.q * a + T.r * b) ∧
      Keeps wordClob s z ∧ Unch base [(P.tbl, 288), (P.M.tmp, 32)] s.mem z.mem ∧
      val32 z.mem base P.sF 9 = val32 s.mem base P.sF 9 ∧
      val32 z.mem base P.sG 9 = val32 s.mem base P.sG 9 := by
  have hn := hs.nowrap
  obtain ht := L.tbl_bound; have hmod := L.mod_bound; have htmp := L.tmp_bound
  obtain htm := L.tbl_mod; have htt := L.tbl_tmp; have hmt := L.mod_tmp
  obtain L₁ : LinearLay size (P.sW + 12) (P.sW + 16) P.sT P.sA P.sB P.sU 8 7 := by
    simpa only [Nat.mul_zero, Nat.add_zero] using abLayout ht (row := 0) (by decide)
  obtain L₂ : LinearLay size (P.sW + 20) (P.sW + 24) P.sT P.sA P.sB P.sU 8 7 := by
    simpa only [Nat.mul_one, Nat.add_assoc, Nat.reduceAdd] using abLayout ht (row := 1) (by decide)
  unfold InvCfg.abUpdate
  rw [List.append_assoc
    (VG.Impl.Weierstrass.X86.Inv.linear (P.sW + 12) (P.sW + 16) P.sT P.sA P.sB P.sU 8 7 ++
      VG.Impl.Weierstrass.X86.Inv.reduce P.M P.sT P.sU P.sNF)
    (VG.Impl.Weierstrass.X86.Inv.linear (P.sW + 20) (P.sW + 24) P.sT P.sA P.sB P.sU 8 7)]
  refine WP.block_append (WP.block_append (WP.mono
    (abHalf_ok hs L₁ (redLayout L (.inl rfl)) hp hm hinv hT.u hT.v huv ha hb hab hbb)
    fun s₁ ⟨A₁, K₁, O₁⟩ => ?_))
  obtain hs₁ := hs.of_keeps K₁ (by decide)
  obtain q₁ : s₁.mem.readW (off base (P.sW + 20)) 32 = BitVec.ofInt 32 T.q := by
    rw [read32_unch O₁ (by apart) (by apart), hT.q]
  obtain r₁ : s₁.mem.readW (off base (P.sW + 24)) 32 = BitVec.ofInt 32 T.r := by
    rw [read32_unch O₁ (by apart) (by apart), hT.r]
  refine WP.mono (abHalf_ok hs₁ L₂ (redLayout L (.inr rfl)) hp
    (by rw [Outs.val32 O₁ (by apart) (by apart)]; exact hm) hinv q₁ r₁ hqr
    (by rw [Outs.val32 O₁ (by apart) (by apart)]; exact ha)
    (by rw [Outs.val32 O₁ (by apart) (by apart)]; exact hb) hab hbb)
    fun s₂ ⟨B₂, K₂, O₂⟩ => ?_
  obtain hs₂ := hs₁.of_keeps K₂ (by decide)
  refine WP.mono (copy_ok 8 hs₂ (o := P.sA) (a := P.sNF) (by apart) (by apart) (by apart))
    fun z ⟨A₃, K₃, O₃⟩ => ⟨?_, ?_, (K₁.trans K₂).trans (K₃.mono (by decide)), ?_, ?_, ?_⟩
  · rw [A₃, Outs.val32 O₂ (by apart) (by apart)]
    exact A₁
  · rw [O₃.val32 (by apart) (by apart)]
    exact B₂
  · intro x hx
    obtain ht' := hx (P.tbl, 288) (by simp)
    obtain hm' := hx (P.M.tmp, 32) (by simp)
    rw [O₃ x (by apart), O₂ x (by apart), O₁ x (by apart)]

  · rw [O₃.val32 (by apart) (by apart), Outs.val32 O₂ (by apart) (by apart),
      Outs.val32 O₁ (by apart) (by apart)]
  · rw [O₃.val32 (by apart) (by apart), Outs.val32 O₂ (by apart) (by apart),
      Outs.val32 O₁ (by apart) (by apart)]

end VG.Proof.Weierstrass.X86.Inv

end

end


/-! # A complete thirty-step inversion batch -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

local macro "apart" : tactic => `(tactic|
  plain_simp_names ((try simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
                     InvCfg.sF, InvCfg.sG, InvCfg.sA, InvCfg.sB, InvCfg.sW, InvCfg.sCount]) <;> omega_arith))

theorem batch_ok {P : InvCfg} {s : State} {base : Addr} {size p j : Nat} {I : Divstep.W32.IState}
    (hs : Scr s base size) (L : WorkLay P size) (hI : StateAt P base I s)
    (hd : |I.d| + 64 < 2 ^ 30) (hf : I.f % 2 = 1)
    (hfb : |I.f| ≤ p) (hgb : |I.g| ≤ p) (hab : |I.a| ≤ p) (hbb : |I.b| ≤ p)
    (hp : 0 < p) (hp256 : p < 2 ^ 256) (hm : val32 s.mem base P.M.mo 8 = p)
    (hinv : (p * (minv32 P.M).toNat + 1) % 2 ^ 32 = 0)
    (hj : 1 ≤ j) (hj32 : j < 2 ^ 32) (hc : w32 s.mem base P.sCount = j)
    (hbound : let T := Divstep.msteps 30 (Divstep.MSt.init I.d I.f I.g)
      |T.u| + |T.v| ≤ 2 ^ 30 ∧ |T.q| + |T.r| ≤ 2 ^ 30)
    (hdiv : let T := Divstep.msteps 30 (Divstep.MSt.init I.d I.f I.g)
      2 ^ 30 ∣ T.u * I.f + T.v * I.g ∧ 2 ^ 30 ∣ T.q * I.f + T.r * I.g) :
    WP isa P.batch s fun z =>
      StateAt P base (Divstep.W32.batch 30 p (minv32 P.M).toNat I) z ∧
      w32 z.mem base P.sCount = j - 1 ∧ z.zf = some (decide (j - 1 = 0)) ∧
      Keeps wordClob s z ∧ Unch base [(P.tbl, 320), (P.M.tmp, 32)] s.mem z.mem := by
  have hn := hs.nowrap
  obtain ht := L.tbl_bound; have hmod := L.mod_bound; have htmp := L.tmp_bound
  obtain htm := L.tbl_mod; have htt := L.tbl_tmp
  let T := Divstep.msteps 30 (Divstep.MSt.init I.d I.f I.g)
  change |T.u| + |T.v| ≤ 2 ^ 30 ∧ |T.q| + |T.r| ≤ 2 ^ 30 at hbound
  change 2 ^ 30 ∣ T.u * I.f + T.v * I.g ∧ 2 ^ 30 ∣ T.q * I.f + T.r * I.g at hdiv
  unfold InvCfg.batch
  refine WP.seq (WP.mono (words_ok hs ht hI hd hf) fun s₁ ⟨Mat₁, K₁, O₁⟩ => ?_)
  obtain hs₁ := hs.of_keeps K₁ (by decide)
  refine WP.block_append (WP.block_append (WP.mono
    (fgUpdate_ok hs₁ ht Mat₁ hbound.1 hbound.2
      (by rw [O₁.val32 (by apart) (by apart)]; exact hI.f)
      (by rw [O₁.val32 (by apart) (by apart)]; exact hI.g) hfb hgb hp256 hdiv.1 hdiv.2)
    fun s₂ ⟨F₂, G₂, K₂, O₂, A₂, B₂⟩ => ?_))
  obtain hs₂ := hs₁.of_keeps K₂ (by decide)
  obtain Mat₂ : MatrixAt P base T s₂ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [read32_unch O₂.unch (by apart) (by apart)]; exact Mat₁.d
    · rw [read32_unch O₂.unch (by apart) (by apart)]; exact Mat₁.u
    · rw [read32_unch O₂.unch (by apart) (by apart)]; exact Mat₁.v
    · rw [read32_unch O₂.unch (by apart) (by apart)]; exact Mat₁.q
    · rw [read32_unch O₂.unch (by apart) (by apart)]; exact Mat₁.r
  refine WP.mono (abUpdate_ok hs₂ L Mat₂ hbound.1 hbound.2 hp
    (by rw [O₂.val32 (by apart) (by apart), O₁.val32 (by apart) (by apart), hm]) hinv
    (by rw [A₂, O₁.val32 (by apart) (by apart)]; exact hI.a)
    (by rw [B₂, O₁.val32 (by apart) (by apart)]; exact hI.b) hab hbb)
    fun s₃ ⟨A₃, B₃, K₃, O₃, F₃, G₃⟩ => ?_
  obtain hs₃ := hs₂.of_keeps K₃ (by decide)
  obtain Count : w32 s₃.mem base P.sCount = j := by
    rw [word_unch O₃ (by apart) (by apart), O₂.w32 (by apart) (by apart),
      O₁.w32 (by apart) (by apart), hc]
  refine WP.mono (batchEnd_ok hs₃ ht hj hj32 Count) fun z ⟨C₄, Z₄, K₄, O₄⟩ =>
    ⟨?_, C₄, Z₄, ((K₁.trans (K₂.mono (by decide))).trans K₃).trans (K₄.mono (by decide)), ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [read32_unch O₄.unch (by apart) (by apart), read32_unch O₃ (by apart) (by apart)]
      rw [Divstep.W32.batch_d]
      exact Mat₂.d
    · rw [O₄.val32 (by apart) (by apart), F₃]
      exact F₂
    · rw [O₄.val32 (by apart) (by apart), G₃]
      exact G₂
    · rw [O₄.val32 (by apart) (by apart)]
      rw [Divstep.W32.batch_a]
      exact A₃
    · rw [O₄.val32 (by apart) (by apart)]
      rw [Divstep.W32.batch_b]
      exact B₃
  · intro x hx
    obtain ht' := hx (P.tbl, 320) (by simp)
    obtain hm' := hx (P.M.tmp, 32) (by simp)
    rw [O₄ x (by apart), O₃ x (by apart), O₂ x (by apart), O₁ x (by apart)]

end VG.Proof.Weierstrass.X86.Inv
