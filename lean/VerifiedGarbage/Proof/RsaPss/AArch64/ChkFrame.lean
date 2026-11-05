module

public import VerifiedGarbage.Proof.RsaPss.AArch64.ChkPre
public import VerifiedGarbage.Impl.RsaPss.AArch64.Encoding
public import VerifiedGarbage.Proof.RsaPss.AArch64.Basic
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
import VerifiedGarbage.Proof.RsaPss.AArch64.MaskBits
import VerifiedGarbage.Proof.RsaPss.AArch64.SignFrame
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset

/-!
# EMSA-PSS's check of an encoding on AArch64: the prologue

`prologue_ok`: the callee-saved registers and the arguments in their slots
of the frame (`FrC`; `any_salt_len`'s 32 bits in `sAny`), `scratch` in
`x20`, `x19` and `x21` set, `emLen` in `x23`, the mask `0xFF >>> z` in `sC`
and `lo = 0` in `sLo` (`AtC`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Chk

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil wp_addImm wp_ldrx wp_strx)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_addSp wp_mov wp_movw wp_ldrSp)
open VG.Proof.RsaPss.AArch64 (off maskBits_ok)
open VG.Proof.RsaPss.AArch64.Sgn (fb in_frame wr_frame kR frame_sub0 stackArgAddr_fb)

/-- The argument registers kept in slots of the frame. -/
def chkSlots : List (Reg × Nat) := [(.x0, sDig), (.x4, sSaltLen), (.x5, sAny)]

theorem fits : Spill.Fits (saved ++ chkSlots) := by decide

/-- `any_salt_len`'s 32 bits. -/
abbrev anyC (s : State) : BitVec 64 := ((s.gpr .x5).setWidth 32).setWidth 64

/-- `z = 8 emLen - emBits`, and the mask of `maskedDB`'s top bits. -/
abbrev zC (s : State) : Nat := 8 * (s.gpr .x2).toNat - (s.gpr .x3).toNat
abbrev cC (s : State) : Byte := (0xFF : Byte) >>> zC s

/-- The frame's slots that the code reads: the saved registers, the
arguments. -/
structure FrC (s : State) (m : Mem) : Prop where
  sv : Spill.Saved (fb s) s.gpr saved m
  dig : m.readW (fb s + BitVec.ofNat 64 sDig) 64 = s.gpr .x0
  sl : m.readW (fb s + BitVec.ofNat 64 sSaltLen) 64 = s.gpr .x4
  any : m.readW (fb s + BitVec.ofNat 64 sAny) 64 = anyC s

/-- The slots of `FrC`: `[96, 248)` and `[264, 272)` of the frame. -/
abbrev frA (s : State) : Region := ⟨fb s + BitVec.ofNat 64 96, 152⟩
abbrev frB (s : State) : Region := ⟨fb s + BitVec.ofNat 64 264, 8⟩

theorem FrC.frame {s : State} {m m' : Mem} (h : FrC s m) {rs : List Region} (hf : Frame rs m m')
    (hA : ∀ r ∈ rs, (frA s).Disjoint r) (hB : ∀ r ∈ rs, (frB s).Disjoint r) : FrC s m' := by
  have hw : ∀ {d : Nat}, (96 ≤ d ∧ d + 8 ≤ 248) → m'.readW (fb s + BitVec.ofNat 64 d) 64 =
      m.readW (fb s + BitVec.ofNat 64 d) 64 := fun hd =>
    hf.readW (r := ⟨fb s + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hA r hr).sub_left (Offset.sub _ hd.1 (by omega))) (by decide)
  refine ⟨h.sv.frame_in (lo := 96) (n := 152) (by decide) hf hA, by rw [hw (by decide)]; exact h.dig,
    by rw [hw (by decide)]; exact h.sl, ?_⟩
  rw [hf.readW (r := ⟨fb s + BitVec.ofNat 64 sAny, 8⟩) (Region.contains_self _ _)
    (fun r hr => (hB r hr).sub_left (Offset.sub _ (by decide) (by decide))) (by decide)]
  exact h.any

/-- After the prologue. -/
structure AtC (s u : State) : Prop where
  sp : u.sp = fb s
  rd : u.rd = s.rd
  wr : u.wr = ⟨fb s, frameBytes⟩ :: s.wr
  x19 : u.gpr .x19 = off (s.gpr .x6) oSt
  x20 : u.gpr .x20 = s.gpr .x6
  x21 : u.gpr .x21 = off (s.gpr .x6) oDig
  x23 : u.gpr .x23 = s.gpr .x2
  x1 : u.gpr .x1 = s.gpr .x1
  v : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  mem : Frame [⟨fb s, frameBytes⟩, ⟨s.gpr .x6, oRsa⟩] s.mem u.mem
  fr : FrC s u.mem
  lo : u.mem.readW (fb s + BitVec.ofNat 64 sLo) 64 = BitVec.ofNat 64 0
  c : u.mem.readW (fb s + BitVec.ofNat 64 sC) 64 = BitVec.setWidth 64 (cC s)

theorem prologue_ok {D : Nat} {tsH tsG : List FnTable} {s u : State} (hp : PreC D tsH tsG s) (hsp : u.sp = fb s) (hrd : u.rd = s.rd)
    (hwr : u.wr = ⟨fb s, frameBytes⟩ :: s.wr) (hm : u.mem = s.mem) (hg : ∀ r, u.gpr r = s.gpr r)
    (hv : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) :
    WP isa (.block chkPrologue) u (AtC s) := by
  unfold chkPrologue save regsUp
  simp only [List.cons_append, List.append_assoc, List.nil_append]
  refine wp_movw fun u₀ o₀ e₀ => wp_addSp (by decide) fun u₁ o₁ e₁ => ?_
  rw [o₀.sp, hsp, BitVec.add_zero] at e₁
  have hin : ∀ p ∈ saved ++ chkSlots, InRegions u₁.wr (u₁.gpr .x16 + BitVec.ofNat 64 p.2) 8 := fun p hp' => by
    rw [e₁, o₁.wr, o₀.wr]
    exact wr_frame hwr (by revert p; decide)
  refine Spill.save_ok (b := .x16) (l := saved ++ chkSlots) fits.1 hin ?_
  generalize hm₂ : Spill.saveMem u₁.mem (u₁.gpr .x16) u₁.gpr (saved ++ chkSlots) = m₂
  have gs : ∀ r, r ≠ .x16 → r ≠ .x5 → u₁.gpr r = s.gpr r := fun r h h' => by
    rw [o₁.gpr r (by simpa using h), o₀.gpr r (by simpa using h'), hg]
  have g5 : u₁.gpr .x5 = anyC s := by rw [o₁.get .x5, e₀, hg]
  have fr₂ : Frame [⟨fb s, frameBytes⟩] s.mem m₂ := by
    rw [← hm₂, e₁, o₁.mem, o₀.mem, hm]
    exact Spill.saveMem_frame_base (fun p hp' => by revert p; decide) (by decide) _ _ _
  have sv₂ : Spill.Saved (fb s) u₁.gpr (saved ++ chkSlots) m₂ := by
    rw [← hm₂, e₁]; exact Spill.saveMem_saved fits _ _ _
  refine wp_mov fun u₃ o₃ e₃ => wp_mov fun u₄ o₄ e₄ => wp_addImm (by decide) fun u₅ o₅ e₅ =>
    wp_addImm (by decide) fun u₆ o₆ e₆ => ?_
  have O₆ : Only [.x23, .x20, .x19, .x21] { u₁ with mem := m₂ } u₆ := (o₃.trans (o₄.trans (o₅.trans o₆))).mono
  have sp₆ : u₆.sp = fb s := by rw [O₆.sp]; show u₁.sp = _; rw [o₁.sp, o₀.sp, hsp]
  have wr₆ : u₆.wr = ⟨fb s, frameBytes⟩ :: s.wr := by rw [O₆.wr]; show u₁.wr = _; rw [o₁.wr, o₀.wr, hwr]
  have x20₆ : u₆.gpr .x20 = s.gpr .x6 := by
    rw [o₆.get .x20, o₅.get .x20, e₄, o₃.get .x6]; exact gs .x6 (by decide) (by decide)
  have x23₆ : u₆.gpr .x23 = s.gpr .x2 := by
    rw [o₆.get .x23, o₅.get .x23, o₄.get .x23, e₃]; exact gs .x2 (by decide) (by decide)
  have x3₆ : u₆.gpr .x3 = s.gpr .x3 := by rw [O₆.get .x3]; exact gs .x3 (by decide) (by decide)
  have hk2 := hp.k2
  have hz := hp.z
  refine WP.mono (maskBits_ok (F := fb s) sp₆ (by rw [wr₆]; exact in_frame s _ (by decide))
    (by rw [wr₆]; exact in_frame s _ (by decide)) (r := .x3) (by decide) (k := (s.gpr .x2).toNat)
    (eb := (s.gpr .x3).toNat) (by rw [x23₆, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (by rw [x3₆, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hz.1 hz.2 (by omega)) fun u₇ ⟨K, hm₇⟩ => ?_
  have hm₇' : u₇.mem = (m₂.writeW (fb s + BitVec.ofNat 64 sC) (BitVec.setWidth 64 (cC s))).writeW
      (fb s + BitVec.ofNat 64 sLo) (0 : BitVec 64) := by rw [hm₇, O₆.mem]
  have W2 : Frame [⟨fb s + BitVec.ofNat 64 sC, 8⟩, ⟨fb s + BitVec.ofNat 64 sLo, 8⟩] m₂ u₇.mem := by
    rw [hm₇']
    exact ((Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)).writeW (by simp) _
      (Region.contains_self _ _)
  have sv₇ := sv₂.frame W2 fun p hp' r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;>
      exact Offset.disjoint _ (by revert p; decide) (by revert p; decide) (by decide)
  exact {
    sp := K.sp.trans sp₆
    rd := by rw [K.rd, O₆.rd]; show u₁.rd = _; rw [o₁.rd, o₀.rd, hrd]
    wr := K.wr.trans wr₆
    x19 := by rw [K.get .x19, o₆.get .x19, e₅, e₄, o₃.get .x6, gs .x6 (by decide) (by decide)]
    x20 := by rw [K.get .x20, x20₆]
    x21 := by rw [K.get .x21, e₆, o₅.get .x20, e₄, o₃.get .x6, gs .x6 (by decide) (by decide)]
    x23 := by rw [K.get .x23, x23₆]
    x1 := by rw [K.get .x1, O₆.get .x1]; exact gs .x1 (by decide) (by decide)
    v := fun r hr => by
      rw [K.vcs r hr, O₆.vcs r hr]
      show (u₁.v r).extractLsb' 0 64 = _
      rw [o₁.vcs r hr, o₀.vcs r hr, hv r hr]
    mem := by
      rw [hm₇']
      exact ((fr₂.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))).writeW
        (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))).mono (by simp)
    fr := {
      sv := fun p hp' => by
        rw [sv₇ p (List.mem_append_left _ hp')]
        exact gs p.1 (by revert p; decide) (by revert p; decide)
      dig := by rw [sv₇ (.x0, sDig) (by simp [chkSlots])]; exact gs .x0 (by decide) (by decide)
      sl := by rw [sv₇ (.x4, sSaltLen) (by simp [chkSlots])]; exact gs .x4 (by decide) (by decide)
      any := by rw [sv₇ (.x5, sAny) (by simp [chkSlots])]; exact g5 }
    lo := by rw [hm₇', Mem.readW_writeW_self64]; rfl
    c := by
      rw [hm₇', Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self64] }

/-- Our part of the working space. -/
theorem rsa_subC {D : Nat} {tsH tsG : List FnTable} {s : State} (hp : PreC D tsH tsG s) :
    Region.Sub ⟨s.gpr .x6, oRsa⟩ (sR s) :=
  Region.sub_prefix (by have := hp.hs; unfold oRsa Proof.RsaPss.encScratch at *; omega)

/-! ## The tables' words to their slots -/

/-- After `tabSlots`: the prologue's facts, and the slots of the tables'
words. -/
structure AtCT (s u : State) : Prop where
  e : AtC s u
  wm : u.mem.readW (fb s + BitVec.ofNat 64 sMgfT) 64 = stackArg s 1
  wi : u.mem.readW (fb s + BitVec.ofNat 64 sIniH) 64 = s.mem.readW (stackArg s 0) 64
  wc : u.mem.readW (fb s + BitVec.ofNat 64 sCmpH) 64 = s.mem.readW (stackArg s 0 + BitVec.ofNat 64 24) 64
  wd : u.mem.readW (fb s + BitVec.ofNat 64 sDigH) 64 = s.mem.readW (stackArg s 0 + BitVec.ofNat 64 32) 64
  sy : u.syms = s.syms

/-- What `AtC` says, after writes to slots apart from its own. -/
theorem AtC.writes {s u v : State} (h : AtC s u) {m : Mem} (hv : v.mem = m) (hsp : v.sp = u.sp) (hrd : v.rd = u.rd)
    (hwr : v.wr = u.wr) (hg : ∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x1], v.gpr r = u.gpr r)
    (hvv : ∀ r ∈ preservedV, (v.v r).extractLsb' 0 64 = (u.v r).extractLsb' 0 64)
    {ds : List Nat} (hd : ∀ d ∈ ds, 248 ≤ d ∧ d + 8 ≤ frameBytes ∧ (d + 8 ≤ sLo ∨ sLo + 8 ≤ d) ∧
      (d + 8 ≤ sC ∨ sC + 8 ≤ d) ∧ (d + 8 ≤ 264 ∨ 272 ≤ d)) (hf : Frame (ds.map fun d => (⟨fb s + BitVec.ofNat 64 d, 8⟩ : Region)) u.mem m) :
    AtC s v where
  sp := hsp.trans h.sp
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  x19 := (hg _ (by simp)).trans h.x19
  x20 := (hg _ (by simp)).trans h.x20
  x21 := (hg _ (by simp)).trans h.x21
  x23 := (hg _ (by simp)).trans h.x23
  x1 := (hg _ (by simp)).trans h.x1
  v := fun r hr => (hvv r hr).trans (h.v r hr)
  mem := by
    rw [hv]
    exact h.mem.trans (hf.sub fun r hr => by
      obtain ⟨d, hd', rfl⟩ := List.mem_map.mp hr
      exact ⟨_, List.mem_cons_self, Offset.sub_base _ (hd d hd').2.1⟩)
  fr := by
    rw [hv]
    refine h.fr.frame hf (fun r hr => ?_) fun r hr => ?_
    all_goals obtain ⟨d, hd', rfl⟩ := List.mem_map.mp hr
    all_goals have := hd d hd'
    · exact Offset.disjoint _ (by omega) (by unfold frameBytes at this; omega) (by unfold frameBytes at this; omega)
    · exact Offset.disjoint _ (by omega) (by unfold frameBytes at this; omega) (by unfold frameBytes at this; omega)
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
      exact Offset.disjoint _ this.2.2.2.1.symm (by decide) (by unfold frameBytes at this; omega)) (by decide)]
    exact h.c

/-- `tabSlots` after its first load, of the table's address into `x9`. -/
theorem tabSlotsT_ok {D : Nat} {tsH tsG : List FnTable} {s u u₁ : State} (hp : PreC D tsH tsG s) (hu : AtC s u)
    (o₁ : Only [.x9] u u₁) (e₁ : u₁.gpr .x9 = stackArg s 0) (hsy : u₁.syms = s.syms) :
    WP isa (.block tabSlots.tail) u₁ (AtCT s) := by
  have rA : ∀ d, d + 8 ≤ 16 → InRegions (u.rd ++ u.wr) (stackArgAddr s 0 + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [hu.rd, hp.hrd]
    exact ⟨aR s, by simp, Offset.contains_base _ hd (by have := hp.sp2; simp; omega)⟩
  have rT : ∀ d, d + 8 ≤ 88 → InRegions (u.rd ++ u.wr) (stackArg s 0 + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [hu.rd, hp.hrd]
    exact ⟨tHR s, by simp, Offset.contains_base _ hd (by have := hp.wtH; omega)⟩
  have kF : ∀ {R : Region}, (kR 288 s).Disjoint R → (sR s).Disjoint R →
      ∀ r ∈ [(⟨fb s, frameBytes⟩ : Region), ⟨s.gpr .x6, oRsa⟩], R.Disjoint r := fun hR hS r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hR.sub_left (frame_sub0 288 s)).symm
    · exact (hS.sub_left (rsa_subC hp)).symm
  have mT : ∀ {m : Mem}, Frame [⟨fb s, frameBytes⟩, ⟨s.gpr .x6, oRsa⟩] s.mem m → ∀ d, d + 8 ≤ 88 →
      m.readW (stackArg s 0 + BitVec.ofNat 64 d) 64 = s.mem.readW (stackArg s 0 + BitVec.ofNat 64 d) 64 :=
    fun hf d hd => hf.readW (r := tHR s) (Offset.contains_base _ hd (by have := hp.wtH; omega)) (kF hp.ktH hp.stH) (by decide)
  have mA : ∀ {m : Mem}, Frame [⟨fb s, frameBytes⟩, ⟨s.gpr .x6, oRsa⟩] s.mem m → ∀ j, j < 2 →
      m.readW (stackArgAddr s j) 64 = stackArg s j := fun hf j hj =>
    hf.readW (r := aR s) (by
      rw [show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by simp [stackArgAddr]]
      exact Offset.contains_base _ (by omega) (by have := hp.sp2; simp; omega)) (kF hp.kA hp.sA) (by decide)
  unfold tabSlots arg st
  simp only [List.cons_append, List.nil_append, List.tail_cons]
  refine WP.of_syms ?_
  refine wp_ldrx (by decide) (by rw [e₁]) (by rw [o₁.rd, o₁.wr]; exact rT 0 (by decide)) fun u₂ o₂ e₂ => ?_
  refine wp_addSp (by decide) fun u₃ o₃ e₃ => ?_
  refine wp_strx (by decide) (by rw [e₃, o₂.sp, o₁.sp, hu.sp, BitVec.add_zero])
    (by rw [o₃.wr, o₂.wr, o₁.wr, hu.wr]; exact in_frame s _ (by decide)) fun u₄ m₄ => ?_
  have f₄ : Frame [⟨fb s, frameBytes⟩, ⟨s.gpr .x6, oRsa⟩] s.mem u₄.mem := by
    rw [m₄.mem, o₃.mem, o₂.mem, o₁.mem]
    exact hu.mem.writeW (r := ⟨fb s, frameBytes⟩) (by simp) _ (Offset.contains_base _ (by decide) (by decide))
  refine wp_ldrx (by decide) (by rw [m₄.gpr, o₃.get .x9, o₂.get .x9, e₁])
    (by rw [m₄.rd, o₃.rd, o₂.rd, o₁.rd, m₄.wr, o₃.wr, o₂.wr, o₁.wr]; exact rT 24 (by decide)) fun u₅ o₅ e₅ => ?_
  rw [mT f₄ 24 (by decide)] at e₅
  refine wp_addSp (by decide) fun u₆ o₆ e₆ => ?_
  refine wp_strx (by decide) (by rw [e₆, o₅.sp, m₄.sp, o₃.sp, o₂.sp, o₁.sp, hu.sp, BitVec.add_zero])
    (by rw [o₆.wr, o₅.wr, m₄.wr, o₃.wr, o₂.wr, o₁.wr, hu.wr]; exact in_frame s _ (by decide)) fun u₇ m₇ => ?_
  have f₇ : Frame [⟨fb s, frameBytes⟩, ⟨s.gpr .x6, oRsa⟩] s.mem u₇.mem := by
    rw [m₇.mem, o₆.mem, o₅.mem]
    exact f₄.writeW (r := ⟨fb s, frameBytes⟩) (by simp) _ (Offset.contains_base _ (by decide) (by decide))
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
  have f₁₀ : Frame [⟨fb s, frameBytes⟩, ⟨s.gpr .x6, oRsa⟩] s.mem u₁₀.mem := by
    rw [m₁₀.mem, o₉.mem, o₈.mem]
    exact f₇.writeW (r := ⟨fb s, frameBytes⟩) (by simp) _ (Offset.contains_base _ (by decide) (by decide))
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
      (d + 8 ≤ sC ∨ sC + 8 ≤ d) ∧ (d + 8 ≤ 264 ∨ 272 ≤ d) := by decide
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
  refine ⟨AtC.writes hu rfl K.sp K.rd K.wr (fun r hr => K.get r (by revert r; decide)) K.vcs hds hf, ?_, ?_, ?_, ?_,
    sy.trans hsy⟩
  · rw [hm, Mem.readW_writeW_self64]
  · rw [hm, sep _ _ (by decide) (by decide) (by decide), sep _ _ (by decide) (by decide) (by decide),
      sep _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64, BitVec.add_zero]
  · rw [hm, sep _ _ (by decide) (by decide) (by decide), sep _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self64]
  · rw [hm, sep _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]

/-- `tabSlots`' first load: the table's address into `x9`. -/
theorem arg0_ok {D : Nat} {tsH tsG : List FnTable} {s u : State} (hp : PreC D tsH tsG s) (hu : AtC s u) :
    WP isa (.block [arg .x9 0]) u fun u₁ => Only [.x9] u u₁ ∧ u₁.gpr .x9 = stackArg s 0 := by
  have rA : ∀ d, d + 8 ≤ 16 → InRegions (u.rd ++ u.wr) (stackArgAddr s 0 + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [hu.rd, hp.hrd]
    exact ⟨aR s, by simp, Offset.contains_base _ hd (by have := hp.sp2; simp; omega)⟩
  have kF : ∀ {R : Region}, (kR 288 s).Disjoint R → (sR s).Disjoint R →
      ∀ r ∈ [(⟨fb s, frameBytes⟩ : Region), ⟨s.gpr .x6, oRsa⟩], R.Disjoint r := fun hR hS r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hR.sub_left (frame_sub0 288 s)).symm
    · exact (hS.sub_left (rsa_subC hp)).symm
  have mA : ∀ {m : Mem}, Frame [⟨fb s, frameBytes⟩, ⟨s.gpr .x6, oRsa⟩] s.mem m →
      m.readW (stackArgAddr s 0) 64 = stackArg s 0 := fun hf =>
    hf.readW (r := aR s) (by
      rw [show stackArgAddr s 0 = stackArgAddr s 0 + BitVec.ofNat 64 0 by simp]
      exact Offset.contains_base _ (by omega) (by omega)) (kF hp.kA hp.sA) (by decide)
  have r0 : InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 (frameBytes + 8 * 0)) 8 := by
    have := rA 0 (by decide)
    rwa [BitVec.add_zero, stackArgAddr_fb, ← hu.sp] at this
  refine wp_ldrSp (by decide) r0 fun u₁ o₁ e₁ => wp_nil ⟨o₁, ?_⟩
  rw [e₁, hu.sp, ← stackArgAddr_fb, mA hu.mem]

theorem tabSlots_ok {D : Nat} {tsH tsG : List FnTable} {s u : State} (hp : PreC D tsH tsG s) (hu : AtC s u)
    (hsy : u.syms = s.syms) :
    WP isa (.block tabSlots) u (AtCT s) := by
  have e : tabSlots = [arg .x9 0] ++ tabSlots.tail := rfl
  rw [e, WP.block_append_iff]
  exact WP.mono_syms (arg0_ok hp hu) fun u₁ ⟨o₁, e₁⟩ sy₁ => tabSlotsT_ok hp hu o₁ e₁ (sy₁.trans hsy)
