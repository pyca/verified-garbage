module

public import VerifiedGarbage.Proof.RsaPss.AArch64.EncPre
public import VerifiedGarbage.Impl.RsaPss.AArch64.Encoding
public import VerifiedGarbage.Proof.RsaPss.AArch64.Basic
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
import VerifiedGarbage.Proof.RsaPss.AArch64.MaskBits
import VerifiedGarbage.Proof.RsaPss.AArch64.SignFrame
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hash
public import VerifiedGarbage.Proof.Mgf1.Basic
public import VerifiedGarbage.Proof.RsaPss.AArch64.Mgf
public import VerifiedGarbage.Proof.RsaPss.EncBytes
import VerifiedGarbage.Proof.RsaPss.AArch64.SignEncOk
import VerifiedGarbage.Proof.RsaPss.AArch64.SignEnc
import VerifiedGarbage.Proof.RsaPss.AArch64.SignChecks
import VerifiedGarbage.Proof.RsaPss.AArch64.Restore
import VerifiedGarbage.Proof.RsaPss.AArch64.CtComp
import VerifiedGarbage.Proof.RsaPss.AArch64.CtHash
import VerifiedGarbage.Proof.RsaPss.EncodeEq
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Encode
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem

/-! ### `RsaPss.AArch64.EncFrame`, which only this module used -/

section

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
    (by rw [x5₆, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hz.1 hz.2 (by omega_using [hk2])) fun u₇ ⟨K, hm₇⟩ => ?_
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
      exact Offset.disjoint _ (by omega_using [this]) (by unfold frameBytes at this; omega_using []) (by unfold frameBytes at this; omega_using [this])
  lo := by
    rw [hv, hf.readW (r := ⟨fb s + BitVec.ofNat 64 sLo, 8⟩) (Region.contains_self _ _) (fun r hr => by
      obtain ⟨d, hd', rfl⟩ := List.mem_map.mp hr
      have := hd d hd'
      exact Offset.disjoint _ this.2.2.1.symm (by decide) (by unfold frameBytes at this; omega_using [this])) (by decide)]
    exact h.lo
  c := by
    rw [hv, hf.readW (r := ⟨fb s + BitVec.ofNat 64 sC, 8⟩) (Region.contains_self _ _) (fun r hr => by
      obtain ⟨d, hd', rfl⟩ := List.mem_map.mp hr
      have := hd d hd'
      exact Offset.disjoint _ this.2.2.2.symm (by decide) (by unfold frameBytes at this; omega_using [this])) (by decide)]
    exact h.c

/-- `tabSlots` after its first load, of the table's address into `x9`. -/
theorem tabSlotsT_ok {D : Nat} {tsH tsG : List FnTable} {s u u₁ : State} (hp : PreE D tsH tsG s) (hu : AtE s u)
    (o₁ : Only [.x9] u u₁) (e₁ : u₁.gpr .x9 = stackArg s 0) (hsy : u₁.syms = s.syms) :
    WP isa (.block tabSlots.tail) u₁ (AtT s) := by
  have rA : ∀ d, d + 8 ≤ 16 → InRegions (u.rd ++ u.wr) (stackArgAddr s 0 + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [hu.rd, hp.hrd]
    exact ⟨aR s, by simp, Offset.contains_base _ hd (by have := hp.sp2; simp; omega_using [hd])⟩
  have rT : ∀ d, d + 8 ≤ 88 → InRegions (u.rd ++ u.wr) (stackArg s 0 + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [hu.rd, hp.hrd]
    exact ⟨tHR s, by simp, Offset.contains_base _ hd (by have := hp.wtH; omega_using [hd])⟩
  have kF : ∀ {R : Region}, (kR 288 s).Disjoint R → ∀ r ∈ [(⟨fb s, frameBytes⟩ : Region)], R.Disjoint r :=
    fun hR r hr => by rw [List.mem_singleton.mp hr]; exact (hR.sub_left (frame_sub0 288 s)).symm
  have mT : ∀ {m : Mem}, Frame [⟨fb s, frameBytes⟩] s.mem m → ∀ d, d + 8 ≤ 88 →
      m.readW (stackArg s 0 + BitVec.ofNat 64 d) 64 = s.mem.readW (stackArg s 0 + BitVec.ofNat 64 d) 64 :=
    fun hf d hd => hf.readW (r := tHR s) (Offset.contains_base _ hd (by have := hp.wtH; omega_using [hd])) (kF hp.ktH) (by decide)
  have mA : ∀ {m : Mem}, Frame [⟨fb s, frameBytes⟩] s.mem m → ∀ j, j < 2 →
      m.readW (stackArgAddr s j) 64 = stackArg s j := fun hf j hj =>
    hf.readW (r := aR s) (by
      rw [show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by simp [stackArgAddr]]
      exact Offset.contains_base _ (by omega_using [hj]) (by have := hp.sp2; simp; omega_using [hj])) (kF hp.kA) (by decide)
  unfold tabSlots arg st
  simp only [List.cons_append, List.nil_append, List.tail_cons]
  refine WP.of_syms ?_
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
    Mem.readW_writeW_sep (Offset.sep _ hab (by omega_using [hb]) (by omega_using [ha]))
      (by decide)
  refine ⟨AtE.writes hu rfl K.sp K.rd K.wr (fun r hr => K.get r (by revert r; decide)) K.vcs hds hf, ?_, ?_, ?_, ?_,
    sy.trans hsy⟩
  · rw [hm, Mem.readW_writeW_self64]
  · rw [hm, sep _ _ (by decide) (by decide) (by decide), sep _ _ (by decide) (by decide) (by decide),
      sep _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64, BitVec.add_zero]
  · rw [hm, sep _ _ (by decide) (by decide) (by decide), sep _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self64]
  · rw [hm, sep _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]

/-- `tabSlots`' first load: the table's address into `x9`. -/
theorem arg0_ok {D : Nat} {tsH tsG : List FnTable} {s u : State} (hp : PreE D tsH tsG s) (hu : AtE s u) :
    WP isa (.block [arg .x9 0]) u fun u₁ => Only [.x9] u u₁ ∧ u₁.gpr .x9 = stackArg s 0 := by
  have rA : ∀ d, d + 8 ≤ 16 → InRegions (u.rd ++ u.wr) (stackArgAddr s 0 + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [hu.rd, hp.hrd]
    exact ⟨aR s, by simp, Offset.contains_base _ hd (by have := hp.sp2; simp; omega_using [hd])⟩
  have kF : ∀ {R : Region}, (kR 288 s).Disjoint R → ∀ r ∈ [(⟨fb s, frameBytes⟩ : Region)], R.Disjoint r :=
    fun hR r hr => by rw [List.mem_singleton.mp hr]; exact (hR.sub_left (frame_sub0 288 s)).symm
  have mA : ∀ {m : Mem}, Frame [⟨fb s, frameBytes⟩] s.mem m →
      m.readW (stackArgAddr s 0) 64 = stackArg s 0 := fun hf =>
    hf.readW (r := aR s) (by
      rw [show stackArgAddr s 0 = stackArgAddr s 0 + BitVec.ofNat 64 0 by simp]
      exact Offset.contains_base _ (by omega_using []) (by omega_using [])) (kF hp.kA) (by decide)
  have r0 : InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 (frameBytes + 8 * 0)) 8 := by
    have := rA 0 (by decide)
    rwa [BitVec.add_zero, stackArgAddr_fb, ← hu.sp] at this
  refine wp_ldrSp (by decide) r0 fun u₁ o₁ e₁ => wp_nil ⟨o₁, ?_⟩
  rw [e₁, hu.sp, ← stackArgAddr_fb, mA hu.mem]

theorem tabSlots_ok {D : Nat} {tsH tsG : List FnTable} {s u : State} (hp : PreE D tsH tsG s) (hu : AtE s u)
    (hsy : u.syms = s.syms) :
    WP isa (.block tabSlots) u (AtT s) := by
  have e : tabSlots = [arg .x9 0] ++ tabSlots.tail := rfl
  rw [e, WP.block_append_iff]
  exact WP.mono_syms (arg0_ok hp hu) fun u₁ ⟨o₁, e₁⟩ sy₁ => tabSlotsT_ok hp hu o₁ e₁ (sy₁.trans hsy)

end VG.Proof.RsaPss.AArch64.Enc
end

end


/-!
# EMSA-PSS's encoding on AArch64: correctness

`code_ok`: `encode` keeps the calling convention, and returns 1 with `em`
holding `Spec.RsaPss.encode`'s encoding, or 0 if it fails (`Post`). After
the prologue, the checks of the lengths (`fitH_ok`, `saltFits_ok`), then the
encoding (`signEnc_ok`, with `k = emLen` and `lo = 0`) and its copy to `em`
(`encMain_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaPss.AArch64 VG.WriteBytes
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil wp_movz wp_addImm eval_nonzero)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_ldrSp wp_mov copy_ok)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.RsaPss.AArch64 (off off_add Lay mgfWr signEnc_ok fitH_ok saltFits_ok restore_frame_ok ld_slot
  slot_not_below)
open VG.Proof.RsaPss.AArch64.Sgn (fb kR frame_sub frame_sub0 below_sub)

/-- What `encodeTContract.post` asks for: the encoding with the hash function
`Hs` (of digests of `D` bytes) and MGF1's `Gs`. -/
def encOut (D : Nat) (Hs Gs : Spec.Mgf1.Hash) (s : State) : Option (List Byte) :=
  Spec.RsaPss.encode Hs Gs (Spec.Rsa.bytesAt s.mem (s.gpr .x2) D)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) (s.gpr .x5).toNat

/-- The outcome, from the memory and `x0`. -/
def OutOk (D : Nat) (Hs Gs : Spec.Mgf1.Hash) (s : State) (m : Mem) (r : BitVec 64) : Prop :=
  match encOut D Hs Gs s with
  | some e => r.setWidth 32 = 1 ∧ Spec.Rsa.bytesAt m (s.gpr .x0) (s.gpr .x1).toNat = e
  | none => r.setWidth 32 = 0

/-- In the frame: the slots and the callee-saved registers' values. -/
structure MidE (s t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  v : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  fr : FrE s t.mem

theorem AtE.toMid {s u : State} (h : AtE s u) : MidE s u := ⟨h.sp, h.rd, h.wr, h.v, h.fr⟩

/-- `AtE` after code that writes registers other than ours. -/
theorem AtE.only {s u u' : State} (h : AtE s u) {rs : List Reg} (o : Only rs u u')
    (hr : ∀ r ∈ [Reg.x19, .x20, .x21, .x23], r ∉ rs := by decide) : AtE s u' where
  sp := o.sp.trans h.sp
  rd := o.rd.trans h.rd
  wr := o.wr.trans h.wr
  x19 := (o.gpr .x19 (hr _ (by simp))).trans h.x19
  x20 := (o.gpr .x20 (hr _ (by simp))).trans h.x20
  x21 := (o.gpr .x21 (hr _ (by simp))).trans h.x21
  x23 := (o.gpr .x23 (hr _ (by simp))).trans h.x23
  v := fun r hr' => (o.vcs r hr').trans (h.v r hr')
  mem := o.mem ▸ h.mem
  fr := o.mem ▸ h.fr
  lo := o.mem ▸ h.lo
  c := o.mem ▸ h.c

/-- `AtT` after code that writes registers other than ours. -/
theorem AtT.only {s u u' : State} (h : AtT s u) {rs : List Reg} (o : Only rs u u') (hsy : u'.syms = u.syms)
    (hr : ∀ r ∈ [Reg.x19, .x20, .x21, .x23], r ∉ rs := by decide) : AtT s u' :=
  ⟨h.e.only o hr, o.mem ▸ h.wm, o.mem ▸ h.wi, o.mem ▸ h.wc, o.mem ▸ h.wd, hsy.trans h.sy⟩

/-- Our part of the working space. -/
theorem rsa_sub {D : Nat} {tsH tsG : List FnTable} {s : State} (hp : PreE D tsH tsG s) : Region.Sub ⟨s.gpr .x6, oRsa⟩ (sR s) :=
  Region.sub_prefix (by have := hp.hs; unfold oRsa Proof.RsaPss.encScratch at *; omega_using [this])

/-- The 16 bytes below the frame, in the stack. -/
theorem below16_sub (s : State) : Region.Sub (below (fb s) 16) (kR 288 s) := fun x h =>
  below_sub 288 s x (Offset.sub_below (fb s) (a := 16) (n := 16) (b := 288) (m := 288) (by decide) (by decide) x h)

/-- Our working space and the frame, laid out. -/
theorem lay_of {D : Nat} {tsH tsG : List FnTable} {s w : State} (hp : PreE D tsH tsG s) (hsp : w.sp = fb s) (h20 : w.gpr .x20 = s.gpr .x6)
    (hwr : w.wr = ⟨fb s, frameBytes⟩ :: s.wr) : Lay w (fb s) (s.gpr .x6) := by
  have hfb := fb_toNat hp
  have := s.sp.isLt
  have hws := hp.ws
  have hhs := hp.hs
  exact {
    sp := hsp
    x20 := h20
    fw := by rw [hwr]; exact List.mem_cons_self
    sw := ⟨sR s, by rw [hwr, hp.hwr]; simp, ⟨rfl, show oRsa ≤ (s.gpr .x7).toNat * 8 by unfold oRsa Proof.RsaPss.encScratch at *; omega_using [hhs]⟩⟩
    Fw := by omega_using [hfb]
    Sw := by unfold oRsa Proof.RsaPss.encScratch at *; omega_using [hws, hhs]
    dFS := (hp.ks.sub_left (frame_sub0 288 s)).sub_right (rsa_sub hp)
    dB := (hp.ks.sub_left (below16_sub s)).sub_right (rsa_sub hp) }

/-- A buffer apart from the stack and the working space is apart from what
the encoding writes. -/
theorem mgfWr_disj {D : Nat} {tsH tsG : List FnTable} {s : State} (hp : PreE D tsH tsG s) {R : Region} (hk : (kR 288 s).Disjoint R)
    (hs : R.Disjoint (sR s)) : ∀ r ∈ mgfWr (fb s) (s.gpr .x6), R.Disjoint r := by
  intro r hr
  simp only [mgfWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hs.sub_right (rsa_sub hp)
  · exact (hk.sub_left (below16_sub s)).symm
  · exact (hk.sub_left (frame_sub 288 s (by decide))).symm
  · exact (hk.sub_left (frame_sub 288 s (by decide))).symm
  · rw [mgfFrame_eq]; exact (hk.sub_left (below_sub 288 s)).symm

/-- What the encoding writes keeps `FrE`. -/
theorem fr_mgf {D : Nat} {tsH tsG : List FnTable} {s : State} (hp : PreE D tsH tsG s) {m m' : Mem} (h : FrE s m)
    (hf : Frame (mgfWr (fb s) (s.gpr .x6)) m m') : FrE s m' := by
  refine h.frame hf fun r hr => ?_
  simp only [mgfWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (hp.ks.sub_left (frame_sub 288 s (d := 96) (n := 152) (by decide))).sub_right (rsa_sub hp)
  · exact Offset.disjoint_below _ (by omega_using [])
  · exact Offset.disjoint _ (by decide) (by decide) (by decide)
  · exact Offset.disjoint _ (by decide) (by decide) (by decide)
  · exact Offset.disjoint_below _ (by rw [mgfFrame_eq]; omega_using [])

/-- An input, in memory changed only in the frame. -/
theorem bytes_frame {s : State} {m : Mem} (hf : Frame [⟨fb s, frameBytes⟩] s.mem m) {R : Region}
    (hk : (kR 288 s).Disjoint R) (hl : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len :=
  VG.Proof.RsaPkcs1Sig.bytes_apart hf (hk.sub_left (frame_sub0 288 s)).symm hl

/-- A refusal: 0. -/
theorem ret0_ok {D : Nat} {Hs Gs : Spec.Mgf1.Hash} {s u : State} (hu : AtE s u) (hn : encOut D Hs Gs s = none) :
    WP isa ret0 u fun t => MidE s t ∧ OutOk D Hs Gs s t.mem (t.gpr .x0) := by
  unfold ret0
  refine wp_movz fun t o e => wp_nil ⟨(hu.only o).toMid, ?_⟩
  simp only [OutOk, hn, e]
  rfl

/-- The encoding's bytes, from the entry state: `emLen = k` bytes with
`lo = 0`. -/
def encF (Hs Gs : Spec.Mgf1.Hash) (D : Nat) (s : State) : Nat → Byte :=
  RsaPss.emT 0 ((s.gpr .x1).toNat - 0 - D - 1) (s.gpr .x4).toNat
    (Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)
    (Hs.hash (Spec.RsaPss.zeros 8 ++ Spec.Rsa.bytesAt s.mem (s.gpr .x2) D ++
      Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat))
    (Spec.Mgf1.mgf1 Gs (Hs.hash (Spec.RsaPss.zeros 8 ++ Spec.Rsa.bytesAt s.mem (s.gpr .x2) D ++
      Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)) ((s.gpr .x1).toNat - 0 - D - 1)) (cE s)

/-- After `signEnc`: `EM` holds `em`. -/
structure AtCopy (s : State) (em : Nat → Byte) (t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  x20 : t.gpr .x20 = s.gpr .x6
  x23 : t.gpr .x23 = s.gpr .x1
  v : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  fr : FrE s t.mem
  em : ∀ i < (s.gpr .x1).toNat, t.mem (off (s.gpr .x6) (oEm + i)) = em i

/-- The slots of the table of `MdHash`, from the table at the entry. -/
theorem ht_of {H : Hash} {dn : String} {f : MdFns} {G : Impl.Pbkdf2.Md.AArch64.Stream}
    {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns} {s w : State} (ht : TabsAt H dn f G g (stackArg s 0) (stackArg s 1) s)
    (hw : AtT s w) : HT H dn f (fb s) w.mem w.syms where
  wi := hw.wi.trans (ht.h0.trans (by rw [hw.sy]))
  wc := hw.wc.trans (ht.h3.trans (by rw [hw.sy]))
  wd := hw.wd.trans (ht.h4.trans (by rw [hw.sy]))
  fi := by rw [hw.sy]; exact ht.fi
  fc := by rw [hw.sy]; exact ht.fc
  fd := by rw [hw.sy]; exact ht.fd

/-- MGF1's working space, in ours. -/
theorem mgfScr_sub {D : Nat} {tsH tsG : List FnTable} {s : State} (hp : PreE D tsH tsG s) :
    Region.Sub ⟨off (s.gpr .x6) mgfOff, 8192⟩ (sR s) :=
  Offset.sub_base _ (by have := hp.hs; unfold mgfOff Proof.RsaPss.encScratch at *; omega_using [this])

/-- Where MGF1 works, and the table of `MdHash`, from the table at the entry. -/
theorem env_of {D : Nat} {tsH tsG : List FnTable} {H : Hash} {dn : String} {f : MdFns}
    {G : Impl.Pbkdf2.Md.AArch64.Stream} {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns} {s w : State}
    (hp : PreE D tsH tsG s) (ht : TabsAt H dn f G g (stackArg s 0) (stackArg s 1) s) (hw : AtT s w) :
    Env G g w (fb s) (s.gpr .x6) (stackArg s 1) := by
  have hfb := fb_toNat hp
  have hsp1 := hp.sp1
  have hwtG := hp.wtG
  have hws := hp.ws
  have hhs := hp.hs
  have hS := mgfScr_sub hp
  have kG : ∀ {R : Region}, R.Sub (kR 288 s) → Region.Disjoint ⟨stackArg s 1, 88⟩ R := fun hR =>
    (hp.ktG.sub_left hR).symm
  have sG : ∀ {R : Region}, R.Sub (sR s) → Region.Disjoint ⟨stackArg s 1, 88⟩ R := fun hR =>
    (hp.stG.sub_left hR).symm
  have hd : ∀ r ∈ mgfWr (fb s) (s.gpr .x6) ++ [⟨off (s.gpr .x6) mgfOff, 8192⟩, slotR (fb s) sPos],
      Region.Disjoint ⟨stackArg s 1, 88⟩ r := by
    intro r hr
    simp only [mgfWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact sG (rsa_sub hp)
    · exact kG (below16_sub s)
    · exact kG (frame_sub 288 s (by decide))
    · exact kG (frame_sub 288 s (by decide))
    · rw [mgfFrame_eq]; exact (hp.ktG.sub_left (below_sub 288 s)).symm
    · exact sG hS
    · exact kG (frame_sub 288 s (by decide))
  have hd0 : ∀ r ∈ [(⟨fb s, frameBytes⟩ : Region)], Region.Disjoint ⟨stackArg s 1, 88⟩ r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact kG (frame_sub0 288 s)
  have hin : ∀ d, d + 8 ≤ 88 → InRegions (w.rd ++ w.wr) (off (stackArg s 1) d) 8 := fun d hd' => by
    rw [hw.e.rd, hp.hrd]
    exact ⟨tGR s, by simp, Offset.contains_base _ (k := 88) (by omega_using [hd']) (by omega_using [hd'])⟩
  exact {
    slot := hw.wm
    ok := by rw [hw.sy]; exact ht.gok
    rd := fun j hj => hin (8 * j) (by omega_using [hj])
    rdD := hin 48 (by decide)
    mem := fun m hm => by
      rw [hw.sy]
      exact ⟨TabMem.keep (TabMem.keep ht.gm hw.e.mem hd0) hm hd,
        ((tabG_keep hm hd (by decide)).trans (tabG_keep hw.e.mem hd0 (by decide))).trans ht.gD⟩
    sc := Covers.one (by
      rw [hw.e.wr, hp.hwr]
      exact ⟨sR s, by simp, Offset.contains_base _ (by unfold mgfOff Proof.RsaPss.encScratch at *; omega_using [hhs])
        (by unfold mgfOff; omega_using [])⟩)
    F288 := by rw [mgfFrame_eq]; unfold encStack Sgn.stk at hsp1; omega_using [hfb, hsp1]
    dStk := by rw [mgfFrame_eq]; exact (hp.ks.sub_left (below_sub 288 s)).sub_right hS
    Sw := by simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; unfold mgfOff Proof.RsaPss.encScratch at *; omega_using [hws, hhs]
    dFw := (hp.ks.sub_left (frame_sub0 288 s)).sub_right hS }

section
variable {H : Hash} (hH : HashOK H) {Gm : Impl.Pbkdf2.Md.AArch64.Stream}
  (hGm : VG.Proof.Pbkdf2.Md.AArch64.Calls.StreamOK Gm) {Hs Gs : Spec.Mgf1.Hash}
  (hHs : ∀ x, Hs.hash x = hH.SH.H.hash x) (hGh : ∀ x, Gs.hash x = hGm.SH.H.hash x) (hGl : Gs.len = Gm.D)
  (hGv : Proof.Mgf1.Valid Gs) {f : MdFns} {dn : String} (hdo : DigOK H.P) {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns}

include hH hHs hGh hGl hGv hdo in
/-- After the checks: the encoding. -/
theorem enc_ok {tsH tsG : List FnTable} {s w : State} (hp : PreE H.D tsH tsG s)
    (ht : TabsAt H dn f Gm g (stackArg s 0) (stackArg s 1) s) (hw : AtT s w)
    (h9 : w.gpr .x9 = BitVec.ofNat 64 ((s.gpr .x1).toNat - (H.D + 2)))
    (hfit : H.D + (s.gpr .x4).toNat + 2 ≤ (s.gpr .x1).toNat) :
    WP isa (signEnc f H g) w (AtCopy s (encF Hs Gs H.D s)) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have L := lay_of hp hw.e.sp hw.e.x20 hw.e.wr
  have hwd := hp.wd; have hwsa := hp.wsa
  have hdR : ∀ j < H.D, InRegions (w.rd ++ w.wr) (s.gpr .x2 + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [hw.e.rd, hp.hrd]
    exact ⟨dgR H.D s, by simp, Offset.contains_base _ (by omega_using [hj]) (by omega_using [hfit, hj])⟩
  have hqR : ∀ j < (s.gpr .x4).toNat, InRegions (w.rd ++ w.wr) (s.gpr .x3 + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [hw.e.rd, hp.hrd]
    exact ⟨saR s, by simp, Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩
  have hbd : Spec.Rsa.bytesAt w.mem (s.gpr .x2) H.D = Spec.Rsa.bytesAt s.mem (s.gpr .x2) H.D :=
    bytes_frame (R := dgR H.D s) hw.e.mem hp.kd (by dsimp only; omega_using [hfit])
  have hbs : Spec.Rsa.bytesAt w.mem (s.gpr .x3) (s.gpr .x4).toNat =
      Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat :=
    bytes_frame (R := saR s) hw.e.mem hp.ksa (by dsimp only; omega_using [])
  refine WP.mono (signEnc_ok hH hGm hGh hGl hGv hHs hdo L (fun _ _ => rfl) (k := (s.gpr .x1).toNat) (lo := 0)
    (sl := (s.gpr .x4).toNat) (c := cE s) (dig := s.gpr .x2) (q := s.gpr .x3) hw.e.x19 hw.e.x21
    (by rw [hw.e.x23, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by rw [h9, Nat.sub_zero]) hw.e.lo hw.e.c
    (hw.e.fr.rs (.x2, sDig) (by simp [encSlots])) (hw.e.fr.rs (.x3, sSalt) (by simp [encSlots]))
    (by rw [hw.e.fr.rs (.x4, sSaltLen) (by simp [encSlots]), BitVec.ofNat_toNat, BitVec.setWidth_eq])
    hk2 (Nat.zero_le 1) (by omega_using [hfit]) hdR (mgfWr_disj hp hp.kd hp.ds) hqR (mgfWr_disj hp hp.ksa hp.sas)
    (ht_of ht hw) (env_of hp ht hw)) fun t ⟨sp₁, rd₁, wr₁, cs₁, v₁, f₁, em₁⟩ => ?_
  rw [hbd, hbs] at em₁
  exact {
    sp := sp₁.trans hw.e.sp
    rd := rd₁.trans hw.e.rd
    wr := wr₁.trans hw.e.wr
    x20 := (cs₁ .x20 (by decide)).trans hw.e.x20
    x23 := (cs₁ .x23 (by decide)).trans hw.e.x23
    v := fun r hr => (v₁ r hr).trans (hw.e.v r hr)
    fr := fr_mgf hp hw.e.fr f₁
    em := em₁ }

end

/-- The arguments of the copy: `EM`, `em` and `emLen`. -/
theorem copyArgs_ok {D : Nat} {tsH tsG : List FnTable} {s t : State} {em : Nat → Byte} (hp : PreE D tsH tsG s) (ht : AtCopy s em t) :
    WP isa (.block [.addImm .x .x11 .x20 oEm, ld .x14 sOut, VG.Impl.MdStream.AArch64.mov .x12 .x23]) t
      fun u => Only [.x11, .x14, .x12] t u ∧ u.gpr .x11 = off (s.gpr .x6) oEm ∧ u.gpr .x14 = s.gpr .x0 ∧
        u.gpr .x12 = s.gpr .x1 := by
  have L := lay_of hp ht.sp ht.x20 ht.wr
  refine wp_addImm (by decide) fun u₁ o₁ e₁ => wp_ldrSp (by decide)
    (by rw [o₁.sp, o₁.rd, o₁.wr]; exact ld_slot L (by decide)) fun u₂ o₂ e₂ => wp_mov fun u₃ o₃ e₃ =>
    wp_nil ⟨(o₁.trans (o₂.trans o₃)).mono, ?_, ?_, ?_⟩
  · rw [o₃.get .x11, o₂.get .x11, e₁, ht.x20]
  · rw [o₃.get .x14, e₂, o₁.mem, o₁.sp, ht.sp]
    exact ht.fr.rs (.x0, sOut) (by simp [encSlots])
  · rw [e₃, o₂.get .x23, o₁.get .x23, ht.x23]

/-- The copy of `EM` to `em`, and 1. -/
theorem copy_ok' {D : Nat} {tsH tsG : List FnTable} {s t : State} {em : Nat → Byte} (hp : PreE D tsH tsG s) (ht : AtCopy s em t) :
    WP isa (.seq copyOut (.block [movi .x0 1])) t fun t' => MidE s t' ∧ t'.gpr .x0 = BitVec.ofNat 64 1 ∧
      Spec.Rsa.bytesAt t'.mem (s.gpr .x0) (s.gpr .x1).toNat = (List.range (s.gpr .x1).toNat).map em := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hwe := hp.we
  have L := lay_of hp ht.sp ht.x20 ht.wr
  generalize hk : (s.gpr .x1).toNat = k at hk1 hk2 hwe
  unfold copyOut
  refine WP.seq (WP.seq (WP.mono (copyArgs_ok hp ht) fun u ⟨O, h11, h14, h12⟩ => ?_))
  have hd : ∀ j < k, ∀ i < k, off (s.gpr .x6) oEm + BitVec.ofNat 64 j ≠ s.gpr .x0 + BitVec.ofNat 64 i := by
    intro j hj i hi h
    have h₁ : (emR s).Contains (s.gpr .x0 + BitVec.ofNat 64 i) 1 :=
      Offset.contains_base (s.gpr .x0) (d := i) (n := 1) (k := (s.gpr .x1).toNat) (by omega_using [hk, hi]) (by omega_using [hk, hi])
    have h₂ : (⟨s.gpr .x6, oRsa⟩ : Region).Contains (s.gpr .x0 + BitVec.ofNat 64 i) 1 := by
      rw [← h, off_add]
      exact Offset.contains_base _ (by unfold oEm oRsa; omega_using [hk2, hj]) (by unfold oEm; omega_using [hk2, hj])
    exact hp.es _ h₁ (rsa_sub hp _ h₂)
  refine WP.mono (copy_ok (p := s.gpr .x0) (q := off (s.gpr .x6) oEm) (n := k) (by omega_using [hk1]) (by omega_using [hk]) h14 h11
    (by rw [h12, ← hk, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (fun j hj => by rw [O.rd, O.wr, off_add]; exact L.ld (by simp only [oEm, oRsa]; omega_using [hk2, hj]))
    (fun i hi => by
      rw [O.wr, ht.wr, hp.hwr]
      exact ⟨emR s, by simp, Offset.contains_base _ (by omega_using [hk, hi]) (by omega_using [hk, hi])⟩) hd) fun u₄ ⟨K₄, m₄⟩ => ?_
  refine wp_movz fun t₅ o₅ e₅ => wp_nil ⟨⟨?_, ?_, ?_, ?_, ?_⟩, by rw [e₅]; rfl, ?_⟩
  · rw [o₅.sp, K₄.sp, O.sp, ht.sp]
  · rw [o₅.rd, K₄.rd, O.rd, ht.rd]
  · rw [o₅.wr, K₄.wr, O.wr, ht.wr]
  · intro r hr; rw [o₅.vcs r hr, K₄.vcs r hr, O.vcs r hr, ht.v r hr]
  · rw [o₅.mem, m₄, O.mem]
    refine ht.fr.frame (writeBytes_frame _ _ _ (Region.contains_self _ _)) fun r hr => ?_
    rw [List.mem_singleton.mp hr, VG.Proof.RsaPkcs1Sig.bytesAt_length]
    have := hp.ke.sub_left (frame_sub 288 s (d := 96) (n := 152) (by decide))
    dsimp only [emR] at this
    rwa [hk] at this
  rw [o₅.mem, m₄, O.mem]
  have hx := VG.Proof.RsaPkcs1Sig.bytesAt_writeBytes t.mem (s.gpr .x0)
    (Spec.Rsa.bytesAt t.mem (off (s.gpr .x6) oEm) k) (by rw [VG.Proof.RsaPkcs1Sig.bytesAt_length]; omega_using [hk])
  rw [VG.Proof.RsaPkcs1Sig.bytesAt_length] at hx
  rw [hx, show Spec.Rsa.bytesAt t.mem (off (s.gpr .x6) oEm) k =
    (List.range k).map fun i => t.mem (off (s.gpr .x6) oEm + BitVec.ofNat 64 i) from rfl]
  refine List.map_congr_left fun i hi => ?_
  rw [off_add, ht.em i (by rw [hk]; exact List.mem_range.mp hi)]

section
variable {H : Hash} (hH : HashOK H) {Gm : Impl.Pbkdf2.Md.AArch64.Stream}
  (hGm : VG.Proof.Pbkdf2.Md.AArch64.Calls.StreamOK Gm) {Hs Gs : Spec.Mgf1.Hash}
  (hHs : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D) (hHv : Proof.Mgf1.Valid Hs)
  (hGh : ∀ x, Gs.hash x = hGm.SH.H.hash x) (hGl : Gs.len = Gm.D)
  (hGv : Proof.Mgf1.Valid Gs) {f : MdFns} {dn : String} (hdo : DigOK H.P) {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns}

include hH hHs hHl hHv hGh hGl hGv hdo in
/-- After the checks: the encoding, its copy to `em`, and 1. -/
theorem encMain_ok {tsH tsG : List FnTable} {s w : State} (hp : PreE H.D tsH tsG s)
    (ht : TabsAt H dn f Gm g (stackArg s 0) (stackArg s 1) s) (hw : AtT s w)
    (h9 : w.gpr .x9 = BitVec.ofNat 64 ((s.gpr .x1).toNat - (H.D + 2)))
    (hfit : H.D + (s.gpr .x4).toNat + 2 ≤ (s.gpr .x1).toNat) :
    WP isa (encMain f H g) w fun t => MidE s t ∧ OutOk H.D Hs Gs s t.mem (t.gpr .x0) := by
  unfold encMain seqs seqs
  refine WP.seq (WP.mono (enc_ok hH hGm hHs hGh hGl hGv hdo hp ht hw h9 hfit) fun t ht => ?_)
  refine WP.mono (copy_ok' hp ht) fun t' ⟨m, h0, hb⟩ => ⟨m, ?_⟩
  have hsl' : (Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat).length = (s.gpr .x4).toNat :=
    VG.Proof.RsaPkcs1Sig.bytesAt_length _ _ _
  have he := RsaPss.encode_eq₂ Hs Gs hHv hGv (mHash := Spec.Rsa.bytesAt s.mem (s.gpr .x2) H.D)
    (salt := Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) (emBits := (s.gpr .x5).toNat)
    (emLen := (s.gpr .x1).toNat) (db := (s.gpr .x1).toNat - 0 - H.D - 1)
    (by rw [VG.Proof.RsaPkcs1Sig.bytesAt_length, hHl])
    hp.hel.symm (by rw [hHl]; omega_using []) (by rw [hsl', hHl]; omega_using [hfit])
  simp only [OutOk, encOut, he]
  refine ⟨by rw [h0]; rfl, ?_⟩
  rw [hb, hsl']
  rfl

end

end VG.Proof.RsaPss.AArch64.Enc
