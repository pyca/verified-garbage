module

public import VerifiedGarbage.Proof.RsaPss.AArch64.EncPre
public import VerifiedGarbage.Impl.RsaPss.AArch64.Encoding
public import VerifiedGarbage.Proof.RsaPss.AArch64.Basic
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
import VerifiedGarbage.Proof.RsaPss.AArch64.MaskBits
import VerifiedGarbage.Proof.RsaPss.AArch64.SignFrame
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-!
# EMSA-PSS's encoding on AArch64: the prologue

`prologue_ok`: the callee-saved registers and the arguments in their slots
of the frame (`FrE`), `scratch` in `x20`, `x19` and `x21` set, `emLen` in
`x23`, the mask `0xFF >>> z` in `sC` and `lo = 0` in `sLo` (`AtE`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_addImm wp_ldrx wp_strx)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_addSp wp_mov wp_ldrSp)
open VG.Proof.RsaPss.AArch64 (off maskBits_ok)
open VG.Proof.RsaPss.AArch64.Sgn (fb in_frame wr_frame kR frame_sub0 stackArgAddr_fb)

/-- The argument registers kept in slots of the frame. -/
def encSlots : List (Reg × Nat) := [(.x0, sOut), (.x2, sDig), (.x3, sSalt), (.x4, sSaltLen)]

theorem fits : Spill.Fits (saved ++ encSlots) := by decide

/-- `z = 8 emLen - emBits`, and the mask of `maskedDB`'s top bits. -/
abbrev zE (s : State) : Nat := 8 * (s.gpr .x1).toNat - (s.gpr .x5).toNat
abbrev cE (s : State) : Byte := (0xFF : Byte) >>> zE s

/-- The frame's slots that the code reads: the saved registers, the
arguments. -/
structure FrE (s : State) (m : Mem) : Prop where
  sv : Spill.Saved (fb s) s.gpr saved m
  rs : Spill.Saved (fb s) s.gpr encSlots m

/-- The slots of `FrE`: `[96, 248)` of the frame. -/
abbrev frA (s : State) : Region := ⟨fb s + BitVec.ofNat 64 96, 152⟩

theorem FrE.frame {s : State} {m m' : Mem} (h : FrE s m) {rs : List Region} (hf : Frame rs m m')
    (hA : ∀ r ∈ rs, (frA s).Disjoint r) : FrE s m' :=
  ⟨h.sv.frame_in (lo := 96) (n := 152) (by decide) hf hA, h.rs.frame_in (lo := 96) (n := 152) (by decide) hf hA⟩

/-- After the prologue. -/
structure AtE (s u : State) : Prop where
  sp : u.sp = fb s
  rd : u.rd = s.rd
  wr : u.wr = ⟨fb s, frameBytes⟩ :: s.wr
  x19 : u.gpr .x19 = off (s.gpr .x6) oSt
  x20 : u.gpr .x20 = s.gpr .x6
  x21 : u.gpr .x21 = off (s.gpr .x6) oDig
  x23 : u.gpr .x23 = s.gpr .x1
  v : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  mem : Frame [⟨fb s, frameBytes⟩] s.mem u.mem
  fr : FrE s u.mem
  lo : u.mem.readW (fb s + BitVec.ofNat 64 sLo) 64 = BitVec.ofNat 64 0
  c : u.mem.readW (fb s + BitVec.ofNat 64 sC) 64 = BitVec.setWidth 64 (cE s)

theorem prologue_ok {D : Nat} {tsH tsG : List FnTable} {s u : State} (hp : PreE D tsH tsG s) (hsp : u.sp = fb s) (hrd : u.rd = s.rd)
    (hwr : u.wr = ⟨fb s, frameBytes⟩ :: s.wr) (hm : u.mem = s.mem) (hg : ∀ r, u.gpr r = s.gpr r)
    (hv : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) :
    WP isa (.block encPrologue) u (AtE s) := by
  unfold encPrologue save regsUp
  simp only [List.cons_append, List.append_assoc, List.nil_append]
  refine wp_addSp (by decide) fun u₁ o₁ e₁ => ?_
  rw [hsp, BitVec.add_zero] at e₁
  have hin : ∀ p ∈ saved ++ encSlots, InRegions u₁.wr (u₁.gpr .x16 + BitVec.ofNat 64 p.2) 8 := fun p hp' => by
    rw [e₁, o₁.wr]
    exact wr_frame hwr (by revert p; decide)
  refine Spill.save_ok (b := .x16) (l := saved ++ encSlots) fits.1 hin ?_
  generalize hm₂ : Spill.saveMem u₁.mem (u₁.gpr .x16) u₁.gpr (saved ++ encSlots) = m₂
  have fr₂ : Frame [⟨fb s, frameBytes⟩] s.mem m₂ := by
    rw [← hm₂, e₁, o₁.mem, hm]
    exact Spill.saveMem_frame_base (fun p hp' => by revert p; decide) (by decide) _ _ _
  have sv₂ : Spill.Saved (fb s) s.gpr (saved ++ encSlots) m₂ := by
    rw [← hm₂, e₁]
    intro p hp'
    rw [Spill.saveMem_saved fits _ _ _ p hp']
    have : p.1 ≠ .x16 := by revert p; decide
    rw [o₁.get p.1 (by simpa using this), hg]
  have gs : ∀ r, r ≠ .x16 → u₁.gpr r = s.gpr r := fun r h => by rw [o₁.gpr r (by simpa using h), hg]
  refine wp_mov fun u₃ o₃ e₃ => wp_mov fun u₄ o₄ e₄ => wp_addImm (by decide) fun u₅ o₅ e₅ =>
    wp_addImm (by decide) fun u₆ o₆ e₆ => ?_
  have O₆ : Only [.x23, .x20, .x19, .x21] { u₁ with mem := m₂ } u₆ := (o₃.trans (o₄.trans (o₅.trans o₆))).mono
  have sp₆ : u₆.sp = fb s := by rw [O₆.sp]; show u₁.sp = _; rw [o₁.sp, hsp]
  have wr₆ : u₆.wr = ⟨fb s, frameBytes⟩ :: s.wr := by rw [O₆.wr]; show u₁.wr = _; rw [o₁.wr, hwr]
  have x20₆ : u₆.gpr .x20 = s.gpr .x6 := by
    rw [o₆.get .x20, o₅.get .x20, e₄, o₃.get .x6]; exact gs .x6 (by decide)
  have x23₆ : u₆.gpr .x23 = s.gpr .x1 := by
    rw [o₆.get .x23, o₅.get .x23, o₄.get .x23, e₃]; exact gs .x1 (by decide)
  have x5₆ : u₆.gpr .x5 = s.gpr .x5 := by rw [O₆.get .x5]; exact gs .x5 (by decide)
  have hk2 := hp.k2
  have hz := hp.z
  refine WP.mono (maskBits_ok (F := fb s) sp₆ (by rw [wr₆]; exact in_frame s _ (by decide))
    (by rw [wr₆]; exact in_frame s _ (by decide)) (r := .x5) (by decide) (k := (s.gpr .x1).toNat)
    (eb := (s.gpr .x5).toNat) (by rw [x23₆, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (by rw [x5₆, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hz.1 hz.2 (by omega)) fun u₇ ⟨K, hm₇⟩ => ?_
  have hm₇' : u₇.mem = (m₂.writeW (fb s + BitVec.ofNat 64 sC) (BitVec.setWidth 64 (cE s))).writeW
      (fb s + BitVec.ofNat 64 sLo) (0 : BitVec 64) := by rw [hm₇, O₆.mem]
  have W2 : Frame [⟨fb s + BitVec.ofNat 64 sC, 8⟩, ⟨fb s + BitVec.ofNat 64 sLo, 8⟩] m₂ u₇.mem := by
    rw [hm₇']
    exact ((Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)).writeW (by simp) _
      (Region.contains_self _ _)
  exact {
    sp := K.sp.trans sp₆
    rd := by rw [K.rd, O₆.rd]; show u₁.rd = _; rw [o₁.rd, hrd]
    wr := K.wr.trans wr₆
    x19 := by rw [K.get .x19, o₆.get .x19, e₅, e₄, o₃.get .x6, gs .x6 (by decide)]
    x20 := by rw [K.get .x20, x20₆]
    x21 := by rw [K.get .x21, e₆, o₅.get .x20, e₄, o₃.get .x6, gs .x6 (by decide)]
    x23 := by rw [K.get .x23, x23₆]
    v := fun r hr => by
      rw [K.vcs r hr, O₆.vcs r hr]
      show (u₁.v r).extractLsb' 0 64 = _
      rw [o₁.vcs r hr, hv r hr]
    mem := by
      rw [hm₇']
      exact (fr₂.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))).writeW
        (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
    fr := by
      have sv₇ := sv₂.frame W2 fun p hp' r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;>
          exact Offset.disjoint _ (by revert p; decide) (by revert p; decide) (by decide)
      exact ⟨sv₇.sub fun p hp => List.mem_append_left _ hp, sv₇.sub fun p hp => List.mem_append_right _ hp⟩
    lo := by rw [hm₇', Mem.readW_writeW_self64]; rfl
    c := by
      rw [hm₇', Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self64] }

/-! ## The tables' words to their slots -/

/-- After `tabSlots`: the prologue's facts, and the slots of the tables'
words. -/
structure AtT (s u : State) : Prop where
  e : AtE s u
  wm : u.mem.readW (fb s + BitVec.ofNat 64 sMgfT) 64 = stackArg s 1
  wi : u.mem.readW (fb s + BitVec.ofNat 64 sIniH) 64 = s.mem.readW (stackArg s 0) 64
  wc : u.mem.readW (fb s + BitVec.ofNat 64 sCmpH) 64 = s.mem.readW (stackArg s 0 + BitVec.ofNat 64 24) 64
  wd : u.mem.readW (fb s + BitVec.ofNat 64 sDigH) 64 = s.mem.readW (stackArg s 0 + BitVec.ofNat 64 32) 64
  sy : u.syms = s.syms

/-- What `AtE` says, after writes to slots apart from its own. -/
theorem AtE.writes {s u v : State} (h : AtE s u) {m : Mem} (hv : v.mem = m) (hsp : v.sp = u.sp) (hrd : v.rd = u.rd)
    (hwr : v.wr = u.wr) (hg : ∀ r ∈ [Reg.x19, .x20, .x21, .x23], v.gpr r = u.gpr r)
    (hvv : ∀ r ∈ preservedV, (v.v r).extractLsb' 0 64 = (u.v r).extractLsb' 0 64)
    {ds : List Nat} (hd : ∀ d ∈ ds, 248 ≤ d ∧ d + 8 ≤ frameBytes ∧ (d + 8 ≤ sLo ∨ sLo + 8 ≤ d) ∧
      (d + 8 ≤ sC ∨ sC + 8 ≤ d)) (hf : Frame (ds.map fun d => (⟨fb s + BitVec.ofNat 64 d, 8⟩ : Region)) u.mem m) :
    AtE s v where
  sp := hsp.trans h.sp
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  x19 := (hg _ (by simp)).trans h.x19
  x20 := (hg _ (by simp)).trans h.x20
  x21 := (hg _ (by simp)).trans h.x21
  x23 := (hg _ (by simp)).trans h.x23
  v := fun r hr => (hvv r hr).trans (h.v r hr)
  mem := by
    rw [hv]
    exact h.mem.trans (hf.sub fun r hr => by
      obtain ⟨d, hd', rfl⟩ := List.mem_map.mp hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (hd d hd').2.1⟩)
  fr := by
    rw [hv]
    exact h.fr.frame hf fun r hr => by
      obtain ⟨d, hd', rfl⟩ := List.mem_map.mp hr
      have := hd d hd'
      exact Offset.disjoint _ (by omega) (by unfold frameBytes at this; omega) (by unfold frameBytes at this; omega)
  lo := by
    rw [hv, hf.readW (r := ⟨fb s + BitVec.ofNat 64 sLo, 8⟩) (Region.contains_self _ _) (fun r hr => by
      obtain ⟨d, hd', rfl⟩ := List.mem_map.mp hr
      have := hd d hd'
      exact Offset.disjoint _ this.2.2.1.symm (by decide) (by unfold frameBytes at this; omega)) (by decide)]
    exact h.lo
  c := by
    rw [hv, hf.readW (r := ⟨fb s + BitVec.ofNat 64 sC, 8⟩) (Region.contains_self _ _) (fun r hr => by
      obtain ⟨d, hd', rfl⟩ := List.mem_map.mp hr
      have := hd d hd'
      exact Offset.disjoint _ this.2.2.2.symm (by decide) (by unfold frameBytes at this; omega)) (by decide)]
    exact h.c

theorem tabSlots_ok {D : Nat} {tsH tsG : List FnTable} {s u : State} (hp : PreE D tsH tsG s) (hu : AtE s u)
    (hsy : u.syms = s.syms) :
    WP isa (.block tabSlots) u (AtT s) := by
  have rA : ∀ d, d + 8 ≤ 16 → InRegions (u.rd ++ u.wr) (stackArgAddr s 0 + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [hu.rd, hp.hrd]
    exact ⟨aR s, by simp, Offset.contains_base _ hd (by have := hp.sp2; simp; omega)⟩
  have rT : ∀ d, d + 8 ≤ 88 → InRegions (u.rd ++ u.wr) (stackArg s 0 + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [hu.rd, hp.hrd]
    exact ⟨tHR s, by simp, Offset.contains_base _ hd (by have := hp.wtH; omega)⟩
  have kF : ∀ {R : Region}, (kR 288 s).Disjoint R → ∀ r ∈ [(⟨fb s, frameBytes⟩ : Region)], R.Disjoint r :=
    fun hR r hr => by rw [List.mem_singleton.mp hr]; exact (hR.sub_left (frame_sub0 288 s)).symm
  have mT : ∀ {m : Mem}, Frame [⟨fb s, frameBytes⟩] s.mem m → ∀ d, d + 8 ≤ 88 →
      m.readW (stackArg s 0 + BitVec.ofNat 64 d) 64 = s.mem.readW (stackArg s 0 + BitVec.ofNat 64 d) 64 :=
    fun hf d hd => hf.readW (r := tHR s) (Offset.contains_base _ hd (by have := hp.wtH; omega)) (kF hp.ktH) (by decide)
  have mA : ∀ {m : Mem}, Frame [⟨fb s, frameBytes⟩] s.mem m → ∀ j, j < 2 →
      m.readW (stackArgAddr s j) 64 = stackArg s j := fun hf j hj =>
    hf.readW (r := aR s) (by
      rw [show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by simp [stackArgAddr]]
      exact Offset.contains_base _ (by omega) (by have := hp.sp2; simp; omega)) (kF hp.kA) (by decide)
  unfold tabSlots arg st
  simp only [List.cons_append, List.nil_append]
  refine WP.of_syms ?_
  have r0 : InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 (frameBytes + 8 * 0)) 8 := by
    have := rA 0 (by decide)
    rwa [BitVec.add_zero, stackArgAddr_fb, ← hu.sp] at this
  refine wp_ldrSp (by decide) r0 fun u₁ o₁ e₁ => ?_
  rw [hu.sp, ← stackArgAddr_fb, mA hu.mem 0 (by decide)] at e₁
  refine wp_ldrx (by decide) (by rw [e₁]) (by rw [o₁.rd, o₁.wr]; exact rT 0 (by decide)) fun u₂ o₂ e₂ => ?_
  refine wp_addSp (by decide) fun u₃ o₃ e₃ => ?_
  refine wp_strx (by decide) (by rw [e₃, o₂.sp, o₁.sp, hu.sp, BitVec.add_zero])
    (by rw [o₃.wr, o₂.wr, o₁.wr, hu.wr]; exact in_frame s _ (by decide)) fun u₄ m₄ => ?_
  have f₄ : Frame [⟨fb s, frameBytes⟩] s.mem u₄.mem := by
    rw [m₄.mem, o₃.mem, o₂.mem, o₁.mem]
    exact hu.mem.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  refine wp_ldrx (by decide) (by rw [m₄.gpr, o₃.get .x9, o₂.get .x9, e₁])
    (by rw [m₄.rd, o₃.rd, o₂.rd, o₁.rd, m₄.wr, o₃.wr, o₂.wr, o₁.wr]; exact rT 24 (by decide)) fun u₅ o₅ e₅ => ?_
  rw [mT f₄ 24 (by decide)] at e₅
  refine wp_addSp (by decide) fun u₆ o₆ e₆ => ?_
  refine wp_strx (by decide) (by rw [e₆, o₅.sp, m₄.sp, o₃.sp, o₂.sp, o₁.sp, hu.sp, BitVec.add_zero])
    (by rw [o₆.wr, o₅.wr, m₄.wr, o₃.wr, o₂.wr, o₁.wr, hu.wr]; exact in_frame s _ (by decide)) fun u₇ m₇ => ?_
  have f₇ : Frame [⟨fb s, frameBytes⟩] s.mem u₇.mem := by
    rw [m₇.mem, o₆.mem, o₅.mem]
    exact f₄.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  refine wp_ldrx (by decide) (by rw [m₇.gpr, o₆.get .x9, o₅.get .x9, m₄.gpr, o₃.get .x9, o₂.get .x9, e₁])
    (by rw [m₇.rd, o₆.rd, o₅.rd, m₄.rd, o₃.rd, o₂.rd, o₁.rd, m₇.wr, o₆.wr, o₅.wr, m₄.wr, o₃.wr, o₂.wr, o₁.wr]
        exact rT 32 (by decide)) fun u₈ o₈ e₈ => ?_
  rw [mT f₇ 32 (by decide)] at e₈
  refine wp_addSp (by decide) fun u₉ o₉ e₉ => ?_
  have sp₉ : u₉.sp = fb s := by rw [o₉.sp, o₈.sp, m₇.sp, o₆.sp, o₅.sp, m₄.sp, o₃.sp, o₂.sp, o₁.sp, hu.sp]
  have wr₉ : u₉.wr = ⟨fb s, frameBytes⟩ :: s.wr := by
    rw [o₉.wr, o₈.wr, m₇.wr, o₆.wr, o₅.wr, m₄.wr, o₃.wr, o₂.wr, o₁.wr, hu.wr]
  have rd₉ : u₉.rd = u.rd := by rw [o₉.rd, o₈.rd, m₇.rd, o₆.rd, o₅.rd, m₄.rd, o₃.rd, o₂.rd, o₁.rd]
  refine wp_strx (by decide) (by rw [e₉, ← o₉.sp, sp₉, BitVec.add_zero]) (by rw [wr₉]; exact in_frame s _ (by decide))
    fun u₁₀ m₁₀ => ?_
  have f₁₀ : Frame [⟨fb s, frameBytes⟩] s.mem u₁₀.mem := by
    rw [m₁₀.mem, o₉.mem, o₈.mem]
    exact f₇.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  have r1 : InRegions (u₁₀.rd ++ u₁₀.wr) (u₁₀.sp + BitVec.ofNat 64 (frameBytes + 8 * 1)) 8 := by
    rw [m₁₀.sp, sp₉, m₁₀.rd, rd₉, m₁₀.wr, ← stackArgAddr_fb]
    have := rA 8 (by decide)
    rw [show stackArgAddr s 0 + BitVec.ofNat 64 8 = stackArgAddr s 1 by simp [stackArgAddr]] at this
    rw [wr₉, ← hu.wr]; exact this
  refine wp_ldrSp (by decide) r1 fun u₁₁ o₁₁ e₁₁ => ?_
  rw [m₁₀.sp, sp₉, ← stackArgAddr_fb, mA f₁₀ 1 (by decide)] at e₁₁
  refine wp_addSp (by decide) fun u₁₂ o₁₂ e₁₂ => ?_
  refine wp_strx (by decide) (by rw [e₁₂, o₁₁.sp, m₁₀.sp, sp₉, BitVec.add_zero])
    (by rw [o₁₂.wr, o₁₁.wr, m₁₀.wr, wr₉]; exact in_frame s _ (by decide)) fun u₁₃ m₁₃ => wp_nil fun sy => ?_
  have hm : u₁₃.mem = (((u.mem.writeW (fb s + BitVec.ofNat 64 sIniH) (s.mem.readW (stackArg s 0 + 0#64) 64)).writeW
      (fb s + BitVec.ofNat 64 sCmpH) (s.mem.readW (stackArg s 0 + BitVec.ofNat 64 24) 64)).writeW
      (fb s + BitVec.ofNat 64 sDigH) (s.mem.readW (stackArg s 0 + BitVec.ofNat 64 32) 64)).writeW
      (fb s + BitVec.ofNat 64 sMgfT) (stackArg s 1) := by
    have v1 : u₃.gpr .x10 = s.mem.readW (stackArg s 0 + 0#64) 64 := by
      rw [o₃.get .x10, e₂, o₁.mem, mT hu.mem 0 (by decide)]
    have v2 : u₆.gpr .x10 = s.mem.readW (stackArg s 0 + BitVec.ofNat 64 24) 64 := by rw [o₆.get .x10, e₅]
    have v3 : u₉.gpr .x10 = s.mem.readW (stackArg s 0 + BitVec.ofNat 64 32) 64 := by rw [o₉.get .x10, e₈]
    rw [m₁₃.mem, o₁₂.mem, o₁₁.mem, m₁₀.mem, o₉.mem, o₈.mem, m₇.mem, o₆.mem, o₅.mem, m₄.mem, o₃.mem, o₂.mem,
      o₁.mem, o₁₂.get .x9, e₁₁, v3, v2, v1]
  have K : Keep [.x9, .x10, .x16] u u₁₃ :=
    ((((((((((((o₁.keep.trans o₂.keep).trans o₃.keep).trans m₄.keep).trans o₅.keep).trans o₆.keep).trans
      m₇.keep).trans o₈.keep).trans o₉.keep).trans m₁₀.keep).trans o₁₁.keep).trans o₁₂.keep).trans m₁₃.keep).mono
  have hds : ∀ d ∈ [sIniH, sCmpH, sDigH, sMgfT], 248 ≤ d ∧ d + 8 ≤ frameBytes ∧ (d + 8 ≤ sLo ∨ sLo + 8 ≤ d) ∧
      (d + 8 ≤ sC ∨ sC + 8 ≤ d) := by decide
  have hf : Frame ([sIniH, sCmpH, sDigH, sMgfT].map fun d => (⟨fb s + BitVec.ofNat 64 d, 8⟩ : Region)) u.mem
      u₁₃.mem := by
    rw [hm]
    exact ((((Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)).writeW (by simp) _
      (Region.contains_self _ _)).writeW (by simp) _ (Region.contains_self _ _)).writeW (by simp) _
      (Region.contains_self _ _)
  have sep : ∀ a b : Nat, b + 8 ≤ a ∨ a + 8 ≤ b → a + 8 ≤ 336 → b + 8 ≤ 336 →
      ∀ (m : Mem) (v : BitVec 64), (m.writeW (fb s + BitVec.ofNat 64 a) v).readW (fb s + BitVec.ofNat 64 b) 64 =
        m.readW (fb s + BitVec.ofNat 64 b) 64 := fun a b hab ha hb m v =>
    Mem.readW_writeW_sep (Offset.sep _ hab (by omega) (by omega))
      (by decide)
  refine ⟨AtE.writes hu rfl K.sp K.rd K.wr (fun r hr => K.get r (by revert r; decide)) K.vcs hds hf, ?_, ?_, ?_, ?_,
    sy.trans hsy⟩
  · rw [hm, Mem.readW_writeW_self64]
  · rw [hm, sep _ _ (by decide) (by decide) (by decide), sep _ _ (by decide) (by decide) (by decide),
      sep _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64, BitVec.add_zero]
  · rw [hm, sep _ _ (by decide) (by decide) (by decide), sep _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self64]
  · rw [hm, sep _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
