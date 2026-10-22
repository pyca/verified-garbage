module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.GRange
public import VerifiedGarbage.Proof.Framework.RelCTChain
import VerifiedGarbage.Proof.Dsa.X86.PowCall
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.OutsFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Dsa.X86.Generation.Base
import VerifiedGarbage.Proof.Dsa.X86.Generation.Flags
import VerifiedGarbage.Proof.Dsa.X86.Generation.LoadStore

/-! # `g = h^((p − 1)/q) mod p` and its check `g > 1` (A.2.1 steps 4–5) -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Mont.X86 (sc)
open VG.Impl.Mont.X86.Dynamic (chainW selectsW slot stride contextBytes)

/-- The first `k` of `k + r` words, when their value fits in `k`. -/
theorem val32_prefix {m : Mem} {base : Addr} {d k r v : Nat} (h : val32 m base d (k + r) = v)
    (hv : v < 2 ^ (32 * k)) : val32 m base d k = v := by
  rw [val32_append] at h
  have := val32_lt m base d k
  have hm : 2 ^ (32 * k) * val32 m base (d + 4 * k) r = 0 := by
    rcases Nat.eq_zero_or_pos (val32 m base (d + 4 * k) r) with h0 | h0
    · rw [h0, Nat.mul_zero]
    · have := Nat.mul_le_mul_left (2 ^ (32 * k)) h0; omega
  omega

/-- The ranges `g`'s computation changes: the exponentiation's working space
below the header, the temporary, `g` in p||q||g and `fG`. -/
def wRanges (g : Geo) : List (Nat × Nat) := [(0, 7168), (aTmp, 400), (sPk + g.pLen + g.qLen, g.pLen), (fG, 4)]

theorem wRanges_apart {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) : E.Apart (wRanges g) := by
  have sz := v.size_ge
  have bd := G.bounds
  intro o ho
  simp only [wRanges, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl <;> simp only [aTmp, arr, sPk, fG, fOut, fWitLen, hdr] <;> omega

/-- `h^((p − 1)/q) mod p`, as the exponentiation computes it. -/
def gVal (h p x : Nat) : Nat := h ^ x % p

/-- After `g` from `h`: `fG` := 1 with `g` in p||q||g if `g > 1`. -/
structure PowPost (E : Env) (g : Geo) (gv F : Nat) (s t : State) : Prop where
  base : Base E t
  fg : t.mem.readW (off E.base fG) 32 = BitVec.ofNat 32 (if 1 < gv then 1 else F)
  gb : 1 < gv → Spec.Rsa.bytesAt t.mem (off E.base (sPk + g.pLen + g.qLen)) g.pLen = Spec.Dsa.encodeBE g.pLen gv
  chg : E.Chg (wRanges g) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  syms : t.syms = s.syms

/-- A change within one range of `scratch` is a change within a range around it. -/
theorem Env.Chg.of_outside {E : Env} (v : E.Valid) {os : List (Nat × Nat)} {m m' : Mem} {o n o' n' : Nat}
    (O : Outside E.base o n m m') (ho : (o', n') ∈ os) (h₁ : o' ≤ o) (h₂ : o + n ≤ o' + n')
    (fit : o' + n' ≤ E.size) : E.Chg os m m' := by
  have nw := v.scratchFit
  refine Env.Chg.of_frame (VG.Proof.Bignum.outs_frame (Outs.of_outside O (List.mem_singleton_self _)) ?_) ?_
  · intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    show o + n ≤ 2 ^ 64
    omega
  · intro r hr
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hr; subst hr
    exact Env.in_range ho h₁ h₂

/-- Before the check `g > 1`: `g` in the exponentiation's result, ZF set
exactly when `g ≤ 1`. -/
structure PowMid (E : Env) (g : Geo) (gv F : Nat) (s t : State) : Prop where
  base : Base E t
  zf : isa.eval .e t = some (!decide (1 < gv))
  res : val32 t.mem E.base (slot g.n64 6) g.n32 = gv
  fg : t.mem.readW (off E.base fG) 32 = BitVec.ofNat 32 F
  chg : E.Chg (wRanges g) s.mem t.mem
  keeps : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t
  syms : t.syms = s.syms

/-- After the exponentiation's arguments are in place. -/
structure SelPost (E : Env) (g : Geo) (p h x F : Nat) (s t : State) : Prop where
  scr : Scr t E.base E.size
  sp : t.gpr .esp = E.sp
  modv : wordsVal t.mem E.base (slot g.n64 0) g.n64 = p
  basev : val32 t.mem E.base (slot g.n64 5) g.n32 = h
  expv : val32 t.mem E.base (slot g.n64 8) g.e = x
  one : val32 t.mem E.base aOne g.n32 = 1
  fg : t.mem.readW (off E.base fG) 32 = BitVec.ofNat 32 F
  chg : E.Chg [(0, 7168), (aTmp, 400)] s.mem t.mem
  keeps : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t
  syms : t.syms = s.syms

/-- p, h and `(p − 1)/q` into the exponentiation's arrays. -/
theorem gPowSel_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {s : State} (B : Base E s) {p h x F : Nat}
    (hP : val32 s.mem E.base aP g.n32 = p) (hH : val32 s.mem E.base aH g.n32 = h)
    (hE : val32 s.mem E.base aE g.n32 = x) (hx : x < 2 ^ (32 * g.e)) (hone : val32 s.mem E.base aOne g.n32 = 1)
    (hF : s.mem.readW (off E.base fG) 32 = BitVec.ofNat 32 F)
    {P : Prog isa} {Q : State → Prop} (k : ∀ t, SelPost E g p h x F s t → WP isa P t Q) :
    WP isa (Prog.chain [.block [.mov .ecx (.imm 0)],
      selectsW g.n32 aP aP (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).modulus,
      .block [.mov .ecx (.imm 0)], selectsW g.n32 aH aH (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).base,
      .block [.mov .ecx (.imm 0)], selectsW g.e aE aE (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).exponent] P) s Q := by
  have sz := v.size_ge
  have bd := G.bounds
  have nw := v.scratchFit
  have n64 : g.n64 = g.pLen / 8 := rfl
  have n32 : g.n32 = g.pLen / 4 := rfl
  have h2 : 2 * g.n64 = g.n32 := by
    rcases G.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> simp only [n64, n32, h]
  have h8 : 8 * g.n64 = g.pLen := by
    rcases G.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> simp only [n64, h]
  have he : 1 < g.e ∧ g.e ≤ 2 * g.n64 ∧ g.e ≤ g.n32 := by
    rw [G.e, n64, n32]
    rcases G.lengths with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h, h'] <;> decide
  have slots : ∀ i, i ≤ 9 → slot g.n64 i ≤ 7048 := fun i hi => by
    simp only [slot, stride]; have := Nat.mul_le_mul hi (show 16 * g.n64 + 8 ≤ 776 by omega); omega
  have cb : contextBytes g.n64 ≤ 7048 := slots 9 (Nat.le_refl _)
  have sl : ∀ i, slot g.n64 i + 8 * g.n64 ≤ slot g.n64 (i + 1) := fun i => by
    simp only [slot, stride, Nat.succ_mul]; omega
  have mod : (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).modulus = slot g.n64 0 := rfl
  have bas : (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).base = slot g.n64 5 := rfl
  have exn : (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).exponent = slot g.n64 8 := rfl
  have res : (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).result = slot g.n64 6 := rfl
  rw [mod, bas, exn]
  have s0 := slots 0 (by omega); have s5 := slots 5 (by omega); have s6 := slots 6 (by omega)
  have s8 := slots 8 (by omega); have s9 := slots 9 (by omega); have s1 := slots 1 (by omega)
  have l0 : slot g.n64 0 + 8 * g.n64 ≤ slot g.n64 1 := sl 0
  have l5 : slot g.n64 5 + 8 * g.n64 ≤ slot g.n64 6 := sl 5
  have l6 : slot g.n64 6 + 8 * g.n64 ≤ slot g.n64 7 := sl 6
  have l8 : slot g.n64 8 + 8 * g.n64 ≤ slot g.n64 9 := sl 8
  have s7 := slots 7 (by omega)
  have o15 : slot g.n64 1 ≤ slot g.n64 5 := by simp only [slot]; omega
  have o18 : slot g.n64 1 ≤ slot g.n64 8 := by simp only [slot]; omega
  have o68 : slot g.n64 6 ≤ slot g.n64 8 := by simp only [slot]; omega
  have o56 : slot g.n64 5 ≤ slot g.n64 6 := by simp only [slot]; omega
  have s00 : 64 ≤ slot g.n64 0 := by simp only [slot]; omega
  simp only [Prog.chain]
  -- p, h and `(p − 1)/q` into the exponentiation's arrays.
  refine WP.seq (wp_movi fun s₁ u₁ => WP.block_nil ?_)
  have hs₁ : Scr s₁ E.base E.size := Scr.of_eq B.scr (u₁.other _ (by decide)) (u₁.other _ (by decide)) u₁.wr
  refine WP.seq (VG.X86.WP.mono_syms (selectsW_ok hs₁ (src := aP) (tmp := aP) (o := slot g.n64 0) (n := g.n32) false
    (by rw [u₁.gpr]; rfl) (by omega) (by simp only [aP, arr]; omega) (by simp only [aP, arr]; omega) (by omega)
    (by right; left; simp only [aP, arr]; omega) (by right; left; simp only [aP, arr]; omega))
    fun s₂ ⟨O₂, V₂, K₂⟩ sy₂ => ?_)
  simp only [Bool.false_eq_true, ↓reduceIte] at V₂
  rw [u₁.mem, hP] at V₂
  have hs₂ := hs₁.of_keeps K₂ (by decide)
  have far : ∀ {m m' : Mem} {o k d n : Nat}, Outside E.base o k m m' → o + k ≤ 7168 → 9728 ≤ d →
      d + 4 * n ≤ E.size → val32 m' E.base d n = val32 m E.base d n := fun O h₁ h₂ h₃ =>
    O.val32 (by right; omega) (by omega)
  refine WP.seq (wp_movi fun s₃ u₃ => WP.block_nil ?_)
  have hs₃ : Scr s₃ E.base E.size := Scr.of_eq hs₂ (u₃.other _ (by decide)) (u₃.other _ (by decide)) u₃.wr
  refine WP.seq (VG.X86.WP.mono_syms (selectsW_ok hs₃ (src := aH) (tmp := aH) (o := slot g.n64 5) (n := g.n32) false
    (by rw [u₃.gpr]; rfl) (by omega) (by simp only [aH, arr]; omega) (by simp only [aH, arr]; omega) (by omega)
    (by right; left; simp only [aH, arr]; omega) (by right; left; simp only [aH, arr]; omega))
    fun s₄ ⟨O₄, V₄, K₄⟩ sy₄ => ?_)
  simp only [Bool.false_eq_true, ↓reduceIte] at V₄
  rw [u₃.mem, far O₂ (by omega) (by simp only [aH, arr]; omega) (by simp only [aH, arr]; omega), u₁.mem, hH] at V₄
  have hs₄ := hs₃.of_keeps K₄ (by decide)
  refine WP.seq (wp_movi fun s₅ u₅ => WP.block_nil ?_)
  have hs₅ : Scr s₅ E.base E.size := Scr.of_eq hs₄ (u₅.other _ (by decide)) (u₅.other _ (by decide)) u₅.wr
  refine WP.seq (VG.X86.WP.mono_syms (selectsW_ok hs₅ (src := aE) (tmp := aE) (o := slot g.n64 8) (n := g.e) false
    (by rw [u₅.gpr]; rfl) (by omega) (by simp only [aE, arr]; omega) (by simp only [aE, arr]; omega) (by omega)
    (by right; left; simp only [aE, arr]; omega) (by right; left; simp only [aE, arr]; omega))
    fun s₆ ⟨O₆, V₆, K₆⟩ sy₆ => ?_)
  simp only [Bool.false_eq_true, ↓reduceIte] at V₆
  have xE : val32 s.mem E.base aE g.e = x :=
    val32_prefix (k := g.e) (r := g.n32 - g.e) (by rw [Nat.add_sub_cancel' he.2.2]; exact hE) hx
  rw [u₅.mem, far O₄ (by omega) (by simp only [aE, arr]; omega) (by simp only [aE, arr]; omega), u₃.mem,
    far O₂ (by omega) (by simp only [aE, arr]; omega) (by simp only [aE, arr]; omega), u₁.mem, xE] at V₆
  have hs₆ := hs₅.of_keeps K₆ (by decide)
  have sp₆ : s₆.gpr .esp = E.sp := by
    rw [K₆.1 _ (by decide), u₅.other _ (by decide), K₄.1 _ (by decide), u₃.other _ (by decide), K₂.1 _ (by decide),
      u₁.other _ (by decide), B.sp]
  have hv : wordsVal s₆.mem E.base (slot g.n64 0) g.n64 = p := by
    rw [wordsVal_eq_val32, h2, O₆.val32 (by left; omega) (by omega), u₅.mem, O₄.val32 (by left; omega) (by omega),
      u₃.mem, V₂]
  have w0 : (0, 7168) ∈ [(0, 7168), (aTmp, 400)] := by simp
  have C₂ := Env.Chg.of_outside v O₂ w0 (Nat.zero_le _) (by omega) (by omega)
  have C₄ := Env.Chg.of_outside v O₄ w0 (Nat.zero_le _) (by omega) (by omega)
  have C₆ := Env.Chg.of_outside v O₆ w0 (Nat.zero_le _) (by omega) (by omega)
  have C₆' : E.Chg [(0, 7168), (aTmp, 400)] s.mem s₆.mem :=
    (by rw [← u₁.mem]; exact C₂ : E.Chg [(0, 7168), (aTmp, 400)] s.mem s₂.mem).trans
      ((by rw [← u₃.mem]; exact C₄ : E.Chg [(0, 7168), (aTmp, 400)] s₂.mem s₄.mem).trans
      (by rw [← u₅.mem]; exact C₆ : E.Chg [(0, 7168), (aTmp, 400)] s₄.mem s₆.mem))
  have k₁ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s s₁ :=
    ⟨fun r hr => u₁.other r (fun e => hr (e ▸ by simp)), u₁.rd, u₁.wr⟩
  have k₃ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s₂ s₃ :=
    ⟨fun r hr => u₃.other r (fun e => hr (e ▸ by simp)), u₃.rd, u₃.wr⟩
  have k₅ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s₄ s₅ :=
    ⟨fun r hr => u₅.other r (fun e => hr (e ▸ by simp)), u₅.rd, u₅.wr⟩
  refine k s₆ ⟨hs₆, sp₆, hv, ?_, V₆, ?_, ?_, C₆', ?_, ?_⟩
  · rw [O₆.val32 (by left; omega) (by omega), u₅.mem, V₄]
  · rw [far O₆ (by omega) (by simp only [aOne, arr]; omega) (by simp only [aOne, arr]; omega), u₅.mem,
      far O₄ (by omega) (by simp only [aOne, arr]; omega) (by simp only [aOne, arr]; omega), u₃.mem,
      far O₂ (by omega) (by simp only [aOne, arr]; omega) (by simp only [aOne, arr]; omega), u₁.mem, hone]
  · rw [Env.Chg.word v C₆' (by simp only [fG, hdr]; omega) (fun o ho => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl <;> simp only [aTmp, arr, fG, hdr] <;> omega), hF]
  · exact k₁.trans ((K₂.mono (by decide)).trans (k₃.trans ((K₄.mono (by decide)).trans (k₅.trans
      (K₆.mono (by decide))))))
  · rw [sy₆, u₅.syms, sy₄, u₃.syms, sy₂, u₁.syms]

/-- The exponentiation keeps `esp` and `edi`. -/
theorem gPowCall_regs {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {s : State} {p h x F : Nat}
    (hp1 : 1 < p) (hodd : p % 2 = 1) {s₆ : State} (S : SelPost E g p h x F s s₆) :
    WP isa (VG.Impl.Dsa.X86.Pow.call g.n64 g.e) s₆ fun u => u.gpr .esp = s₆.gpr .esp ∧ u.gpr .edi = s₆.gpr .edi := by
  have sz := v.size_ge
  have bd := G.bounds
  have nw := v.scratchFit
  have n64 : g.n64 = g.pLen / 8 := rfl
  have n32 : g.n32 = g.pLen / 4 := rfl
  have h2 : 2 * g.n64 = g.n32 := by
    rcases G.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> simp only [n64, n32, h]
  have h8 : 8 * g.n64 = g.pLen := by
    rcases G.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> simp only [n64, h]
  have he : 1 < g.e ∧ g.e ≤ 2 * g.n64 ∧ g.e ≤ g.n32 := by
    rw [G.e, n64, n32]
    rcases G.lengths with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h, h'] <;> decide
  have slots : ∀ i, i ≤ 9 → slot g.n64 i ≤ 7048 := fun i hi => by
    simp only [slot, stride]; have := Nat.mul_le_mul hi (show 16 * g.n64 + 8 ≤ 776 by omega); omega
  have cb : contextBytes g.n64 ≤ 7048 := slots 9 (Nat.le_refl _)
  have sl : ∀ i, slot g.n64 i + 8 * g.n64 ≤ slot g.n64 (i + 1) := fun i => by
    simp only [slot, stride, Nat.succ_mul]; omega
  have mod : (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).modulus = slot g.n64 0 := rfl
  have bas : (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).base = slot g.n64 5 := rfl
  have exn : (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).exponent = slot g.n64 8 := rfl
  have res : (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).result = slot g.n64 6 := rfl
  have s0 := slots 0 (by omega); have s5 := slots 5 (by omega); have s6 := slots 6 (by omega)
  have s8 := slots 8 (by omega); have s9 := slots 9 (by omega); have s1 := slots 1 (by omega)
  have l0 : slot g.n64 0 + 8 * g.n64 ≤ slot g.n64 1 := sl 0
  have l5 : slot g.n64 5 + 8 * g.n64 ≤ slot g.n64 6 := sl 5
  have l6 : slot g.n64 6 + 8 * g.n64 ≤ slot g.n64 7 := sl 6
  have l8 : slot g.n64 8 + 8 * g.n64 ≤ slot g.n64 9 := sl 8
  have s7 := slots 7 (by omega)
  have o15 : slot g.n64 1 ≤ slot g.n64 5 := by simp only [slot]; omega
  have o18 : slot g.n64 1 ≤ slot g.n64 8 := by simp only [slot]; omega
  have o68 : slot g.n64 6 ≤ slot g.n64 8 := by simp only [slot]; omega
  have o56 : slot g.n64 5 ≤ slot g.n64 6 := by simp only [slot]; omega
  have s00 : 64 ≤ slot g.n64 0 := by simp only [slot]; omega
  have low := v.low
  have ss := v.stackScratch
  exact VG.X86.WP.mono_syms (VG.Proof.Dsa.X86.Pow.call_ok S.scr
    (by rw [S.sp]; exact ⟨by omega, ss.elim (fun h => .inl h) (fun h => .inr (by omega))⟩)
    (by omega) (by simp only [VG.Impl.Dsa.Layout.usedBytes]; omega) (by omega) (by omega) he.1 he.2.1 S.modv hp1 hodd)
    fun u ⟨_, _, K⟩ _ => ⟨K.1 _ (by decide), K.1 _ (by decide)⟩

/-- The exponentiation, and the check `g > 1` up to its branch. -/
theorem gPowCall_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {s : State} (B : Base E s) {p h x F : Nat}
    (hp1 : 1 < p) (hodd : p % 2 = 1) {s₆ : State} (S : SelPost E g p h x F s s₆)
    {P : Prog isa} {Q : State → Prop} (k : ∀ t, PowMid E g (gVal h p x) F s t → WP isa P t Q) :
    WP isa (Prog.chain [VG.Impl.Dsa.X86.Pow.call g.n64 g.e,
      chainW .sbb g.n32 aTmp aOne (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).result,
      .block [.alu .cmp .ecx (.imm 0)]] P) s₆ Q := by
  have sz := v.size_ge
  have bd := G.bounds
  have nw := v.scratchFit
  have n64 : g.n64 = g.pLen / 8 := rfl
  have n32 : g.n32 = g.pLen / 4 := rfl
  have h2 : 2 * g.n64 = g.n32 := by
    rcases G.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> simp only [n64, n32, h]
  have h8 : 8 * g.n64 = g.pLen := by
    rcases G.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> simp only [n64, h]
  have he : 1 < g.e ∧ g.e ≤ 2 * g.n64 ∧ g.e ≤ g.n32 := by
    rw [G.e, n64, n32]
    rcases G.lengths with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h, h'] <;> decide
  have slots : ∀ i, i ≤ 9 → slot g.n64 i ≤ 7048 := fun i hi => by
    simp only [slot, stride]; have := Nat.mul_le_mul hi (show 16 * g.n64 + 8 ≤ 776 by omega); omega
  have cb : contextBytes g.n64 ≤ 7048 := slots 9 (Nat.le_refl _)
  have sl : ∀ i, slot g.n64 i + 8 * g.n64 ≤ slot g.n64 (i + 1) := fun i => by
    simp only [slot, stride, Nat.succ_mul]; omega
  have mod : (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).modulus = slot g.n64 0 := rfl
  have bas : (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).base = slot g.n64 5 := rfl
  have exn : (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).exponent = slot g.n64 8 := rfl
  have res : (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).result = slot g.n64 6 := rfl
  rw [res]
  have s0 := slots 0 (by omega); have s5 := slots 5 (by omega); have s6 := slots 6 (by omega)
  have s8 := slots 8 (by omega); have s9 := slots 9 (by omega); have s1 := slots 1 (by omega)
  have l0 : slot g.n64 0 + 8 * g.n64 ≤ slot g.n64 1 := sl 0
  have l5 : slot g.n64 5 + 8 * g.n64 ≤ slot g.n64 6 := sl 5
  have l6 : slot g.n64 6 + 8 * g.n64 ≤ slot g.n64 7 := sl 6
  have l8 : slot g.n64 8 + 8 * g.n64 ≤ slot g.n64 9 := sl 8
  have s7 := slots 7 (by omega)
  have o15 : slot g.n64 1 ≤ slot g.n64 5 := by simp only [slot]; omega
  have o18 : slot g.n64 1 ≤ slot g.n64 8 := by simp only [slot]; omega
  have o68 : slot g.n64 6 ≤ slot g.n64 8 := by simp only [slot]; omega
  have o56 : slot g.n64 5 ≤ slot g.n64 6 := by simp only [slot]; omega
  have s00 : 64 ≤ slot g.n64 0 := by simp only [slot]; omega
  simp only [Prog.chain]
  -- The exponentiation.
  have sp₆ := S.sp
  have hs₆ := S.scr
  have low := v.low
  have ss := v.stackScratch
  have hv := S.modv
  refine WP.seq (VG.X86.WP.mono_syms (VG.Proof.Dsa.X86.Pow.call_ok hs₆
    (by rw [sp₆]; exact ⟨by omega, ss.elim (fun h => .inl h) (fun h => .inr (by omega))⟩)
    (by omega) (by simp only [VG.Impl.Dsa.Layout.usedBytes]; omega) (by omega) (by omega) he.1 he.2.1 hv hp1 hodd)
    fun s₇ ⟨V₇, SO₇, K₇⟩ sy₇ => ?_)
  rw [wordsVal_eq_val32, wordsVal_eq_val32, h2, S.basev, S.expv] at V₇
  have hs₇ := hs₆.of_keeps K₇ (by decide)
  have one₇ : val32 s₇.mem E.base aOne g.n32 = 1 := by
    rw [SO₇.val32 (fun r hr => by
        simp only [VG.Impl.Dsa.X86.Pow.scratch, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only [aOne, arr, contextBytes] at cb ⊢ <;> omega)
        (by simp only [aOne, arr, VG.Impl.Dsa.Layout.usedBytes]; omega), S.one]
  -- `g > 1`.
  refine WP.seq (VG.X86.WP.mono_syms (chainSubW_ok hs₇ (k := g.n32) (o := aTmp) (a := aOne) (b := slot g.n64 6)
    (by omega) (by simp only [aTmp, arr]; omega) (by simp only [aOne, arr]; omega) (by omega)
    (by simp only [aTmp, aOne, arr]; omega) (by right; simp only [aTmp, arr]; omega))
    fun s₈ ⟨O₈, ⟨c₈, e₈, E₈⟩, K₈⟩ sy₈ => ?_)
  rw [one₇, V₇] at E₈
  have c₈v := borrow_lt E₈ (val32_lt _ _ _ _)
  have hs₈ := hs₇.of_keeps K₈ (by decide)
  refine WP.seq (wp_cmpi fun s₉ f₉ _ z₉ => WP.block_nil ?_)
  have zf₉ : isa.eval .e s₉ = some (!decide (1 < gVal h p x)) := by
    show s₉.zf = _
    rw [z₉, e₈, cmask_zf, c₈v]; rfl
  have hs₉ : Scr s₉ E.base E.size := Scr.of_eq hs₈ (by rw [f₉.gpr]) (by rw [f₉.gpr]) f₉.wr
  -- What changed.
  have Aw := wRanges_apart G v
  have w0 : (0, 7168) ∈ [(0, 7168), (aTmp, 400)] := by simp
  have C₇ : E.Chg [(0, 7168), (aTmp, 400)] s₆.mem s₇.mem := by
    rw [sp₆] at SO₇
    refine (Env.Chg.of_stackOuts v SO₇ fun r hr => ?_).widen fun r hr => ⟨(0, 7168), w0, Nat.zero_le _, ?_⟩
    · simp only [VG.Impl.Dsa.X86.Pow.scratch, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [contextBytes] at cb ⊢ <;> omega
    · simp only [VG.Impl.Dsa.X86.Pow.scratch, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [contextBytes] at cb ⊢ <;> omega
  have C₈ := Env.Chg.of_outside v O₈ (os := [(0, 7168), (aTmp, 400)]) (o' := aTmp) (n' := 400) (by simp)
    (Nat.le_refl _) (by simp only [aTmp, arr]; omega) (by simp only [aTmp, arr]; omega)
  have C₉' : E.Chg [(0, 7168), (aTmp, 400)] s.mem s₉.mem := by
    rw [f₉.mem]
    exact S.chg.trans (C₇.trans C₈)
  have C₉ : E.Chg (wRanges g) s.mem s₉.mem := C₉'.widen fun o ho => ⟨o, by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> simp [wRanges], Nat.le_refl _, Nat.le_refl _⟩
  have k₉ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s₈ s₉ := ⟨fun r _ => by rw [f₉.gpr], f₉.rd, f₉.wr⟩
  have K₉ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s s₉ :=
    S.keeps.trans ((K₇.mono (by decide)).trans ((K₈.mono (by decide)).trans k₉))
  have sy₉ : s₉.syms = s.syms := by
    rw [f₉.syms, sy₈, sy₇, S.syms]
  have B₉ : Base E s₉ := B.keep v C₉ Aw (K₉.1 _ (by decide)) (K₉.1 _ (by decide)) K₉.2.1 K₉.2.2 sy₉
  have g₉ : val32 s₉.mem E.base (slot g.n64 6) g.n32 = gVal h p x := by
    rw [f₉.mem, O₈.val32 (by left; simp only [aTmp, arr]; omega) (by omega), V₇]; rfl
  have fG₉ : s₉.mem.readW (off E.base fG) 32 = BitVec.ofNat 32 F := by
    rw [Env.Chg.word v (by rw [f₉.mem]; exact C₇.trans C₈ : E.Chg [(0, 7168), (aTmp, 400)] s₆.mem s₉.mem) (by simp only [fG, hdr]; omega) (fun o ho => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl <;> simp only [aTmp, arr, fG, hdr] <;> omega), S.fg]
  exact k s₉ ⟨B₉, zf₉, g₉, fG₉, C₉, K₉, sy₉⟩

/-- `g` from `h`, `p` and `(p − 1)/q` in their arrays, up to the check `g > 1`. -/
theorem gPowMid_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {s : State} (B : Base E s) {p h x F : Nat}
    (hP : val32 s.mem E.base aP g.n32 = p) (hH : val32 s.mem E.base aH g.n32 = h)
    (hE : val32 s.mem E.base aE g.n32 = x) (hx : x < 2 ^ (32 * g.e)) (hone : val32 s.mem E.base aOne g.n32 = 1)
    (hp1 : 1 < p) (hodd : p % 2 = 1)
    (hF : s.mem.readW (off E.base fG) 32 = BitVec.ofNat 32 F)
    {P : Prog isa} {Q : State → Prop} (k : ∀ t, PowMid E g (gVal h p x) F s t → WP isa P t Q) :
    WP isa (Prog.chain [.block [.mov .ecx (.imm 0)],
      selectsW g.n32 aP aP (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).modulus,
      .block [.mov .ecx (.imm 0)], selectsW g.n32 aH aH (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).base,
      .block [.mov .ecx (.imm 0)], selectsW g.e aE aE (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).exponent,
      VG.Impl.Dsa.X86.Pow.call g.n64 g.e,
      chainW .sbb g.n32 aTmp aOne (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).result,
      .block [.alu .cmp .ecx (.imm 0)]] P) s Q :=
  gPowSel_ok G v B hP hH hE hx hone hF fun _ S => gPowCall_ok G v B hp1 hodd S k

/-- `g` from `h`, `p` and `(p − 1)/q` in their arrays. -/
theorem gPow_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {s : State} (B : Base E s) {p h x F : Nat}
    (hP : val32 s.mem E.base aP g.n32 = p) (hH : val32 s.mem E.base aH g.n32 = h)
    (hE : val32 s.mem E.base aE g.n32 = x) (hx : x < 2 ^ (32 * g.e)) (hone : val32 s.mem E.base aOne g.n32 = 1)
    (hp1 : 1 < p) (hodd : p % 2 = 1) (hplt : p < 2 ^ (8 * g.pLen))
    (hF : s.mem.readW (off E.base fG) 32 = BitVec.ofNat 32 F) :
    WP isa (seqs [.block [.mov .ecx (.imm 0)],
      selectsW g.n32 aP aP (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).modulus,
      .block [.mov .ecx (.imm 0)], selectsW g.n32 aH aH (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).base,
      .block [.mov .ecx (.imm 0)], selectsW g.e aE aE (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).exponent,
      VG.Impl.Dsa.X86.Pow.call g.n64 g.e,
      chainW .sbb g.n32 aTmp aOne (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).result,
      .block [.alu .cmp .ecx (.imm 0)],
      .ite .e (.block [])
        (seqs [storeS (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).result (sPk + g.pLen + g.qLen) g.pLen,
          .block (stImm fG 1)])]) s (PowPost E g (gVal h p x) F s) := by
  have sz := v.size_ge
  have bd := G.bounds
  have nw := v.scratchFit
  have n64 : g.n64 = g.pLen / 8 := rfl
  have n32 : g.n32 = g.pLen / 4 := rfl
  have h2 : 2 * g.n64 = g.n32 := by
    rcases G.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> simp only [n64, n32, h]
  have h8 : 8 * g.n64 = g.pLen := by
    rcases G.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> simp only [n64, h]
  have he : 1 < g.e ∧ g.e ≤ 2 * g.n64 ∧ g.e ≤ g.n32 := by
    rw [G.e, n64, n32]
    rcases G.lengths with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h, h'] <;> decide
  have slots : ∀ i, i ≤ 9 → slot g.n64 i ≤ 7048 := fun i hi => by
    simp only [slot, stride]; have := Nat.mul_le_mul hi (show 16 * g.n64 + 8 ≤ 776 by omega); omega
  have cb : contextBytes g.n64 ≤ 7048 := slots 9 (Nat.le_refl _)
  have sl : ∀ i, slot g.n64 i + 8 * g.n64 ≤ slot g.n64 (i + 1) := fun i => by
    simp only [slot, stride, Nat.succ_mul]; omega
  have mod : (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).modulus = slot g.n64 0 := rfl
  have bas : (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).base = slot g.n64 5 := rfl
  have exn : (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).exponent = slot g.n64 8 := rfl
  have res : (VG.Impl.Dsa.X86.Pow.layout g.n64 g.e).result = slot g.n64 6 := rfl
  rw [mod, bas, exn, res]
  have s0 := slots 0 (by omega); have s5 := slots 5 (by omega); have s6 := slots 6 (by omega)
  have s8 := slots 8 (by omega); have s9 := slots 9 (by omega); have s1 := slots 1 (by omega)
  have l0 : slot g.n64 0 + 8 * g.n64 ≤ slot g.n64 1 := sl 0
  have l5 : slot g.n64 5 + 8 * g.n64 ≤ slot g.n64 6 := sl 5
  have l6 : slot g.n64 6 + 8 * g.n64 ≤ slot g.n64 7 := sl 6
  have l8 : slot g.n64 8 + 8 * g.n64 ≤ slot g.n64 9 := sl 8
  have s7 := slots 7 (by omega)
  have o15 : slot g.n64 1 ≤ slot g.n64 5 := by simp only [slot]; omega
  have o18 : slot g.n64 1 ≤ slot g.n64 8 := by simp only [slot]; omega
  have o68 : slot g.n64 6 ≤ slot g.n64 8 := by simp only [slot]; omega
  have o56 : slot g.n64 5 ≤ slot g.n64 6 := by simp only [slot]; omega
  have s00 : 64 ≤ slot g.n64 0 := by simp only [slot]; omega
  refine gPowMid_ok (P := .ite .e _ _) G v B hP hH hE hx hone hp1 hodd hF fun s₉ M => ?_
  have hs₉ : Scr s₉ E.base E.size := M.base.scr
  have Aw := wRanges_apart G v
  have B₉ := M.base; have zf₉ := M.zf; have g₉ := M.res; have fG₉ := M.fg; have C₉ := M.chg
  have K₉ := M.keeps; have sy₉ := M.syms
  refine WP.ite _ zf₉ (fun hz => WP.block_nil ⟨B₉, ?_, ?_, C₉, K₉.2.1, K₉.2.2, sy₉⟩) (fun hz => ?_)
  · have : ¬ 1 < gVal h p x := by simpa using hz
    simp only [this, ↓reduceIte]; exact fG₉
  · intro hg; have : ¬ 1 < gVal h p x := by simpa using hz
    exact absurd hg this
  have hg : 1 < gVal h p x := by simpa using hz
  have glt : gVal h p x < 2 ^ (8 * g.pLen) := by
    have := Nat.mod_lt (h ^ x) (show 0 < p by omega); unfold gVal; omega
  refine WP.seq (VG.X86.WP.mono_syms (storeS_ok hs₉ (o := slot g.n64 6) (dst := sPk + g.pLen + g.qLen)
    (len := g.pLen) (n := g.n64) (by omega) (by omega) (by omega) (by simp only [sPk]; omega)
    (by left; simp only [sPk]; omega) (by rw [h2, g₉]; exact glt)) fun s₁₀ ⟨G₁₀, F₁₀, K₁₀⟩ sy₁₀ => ?_)
  rw [h2, g₉] at G₁₀
  have hs₁₀ := hs₉.of_keeps K₁₀ (by decide)
  refine stImm_end hs₁₀ (o := fG) (v := 1) (by simp only [fG, hdr]; omega) fun s₁₁ g₁₁ m₁₁ rd₁₁ wr₁₁ sy₁₁ => ?_
  have pk : (sPk + g.pLen + g.qLen, g.pLen) ∈ wRanges g := by simp [wRanges]
  have fg : (fG, 4) ∈ wRanges g := by simp [wRanges]
  have C₁₀ : E.Chg (wRanges g) s.mem s₁₀.mem := C₉.trans (Env.Chg.of_frame F₁₀ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Env.in_range pk (Nat.le_refl _) (Nat.le_refl _))
  have C₁₁ : E.Chg (wRanges g) s.mem s₁₁.mem := by
    rw [m₁₁]; exact C₁₀.store fg (by decide) _
  have K₁₁ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s s₁₁ :=
    K₉.trans ((K₁₀.mono (by decide)).trans ⟨fun r hr => g₁₁ r (fun e => hr (e ▸ by simp)), rd₁₁, wr₁₁⟩)
  have sy : s₁₁.syms = s.syms := by rw [sy₁₁, sy₁₀, sy₉]
  refine ⟨B.keep v C₁₁ Aw (K₁₁.1 _ (by decide)) (K₁₁.1 _ (by decide)) K₁₁.2.1 K₁₁.2.2 sy, ?_, fun _ => ?_, C₁₁,
    K₁₁.2.1, K₁₁.2.2, sy⟩
  · rw [m₁₁, Mem.readW_writeW_self32]; simp only [hg, ↓reduceIte]
  · rw [m₁₁, Env.Chg.scratch v ((Env.Chg.refl [(fG, 4)] s₁₀.mem).store (List.mem_singleton_self _) (by decide) _)
      (by simp only [sPk]; omega) (fun o ho => by
        simp only [List.mem_singleton] at ho; subst ho; simp only [fG, sPk, hdr]; omega), G₁₀]

end VG.Proof.Dsa.X86.Generation
