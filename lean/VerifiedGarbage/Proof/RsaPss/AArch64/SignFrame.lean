module

public import VerifiedGarbage.Proof.RsaPss.AArch64.SignPre
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callee
public import VerifiedGarbage.Proof.RsaPss.AArch64.ArgSlots

/-!
# RSASSA-PSS signing on AArch64: the prologue

`prologue_ok`: the callee-saved registers and the arguments in their slots
of the frame (`Fr`), `scratch` in `x20`, `x19` and `x21` set, `k` in `x23`
and `n₀` in `x10` (`AtChk`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Sgn

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_strx wp_nil wp_addImm wp_ldrb)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_addSp wp_ldrSp wp_mov)
open VG.Proof.RsaPss.AArch64 (off argSlot_ok argSlotW_ok rd_self rd_ws)

/-- The argument registers kept in slots of the frame. -/
def regSlots : List (Reg × Nat) := [(.x0, sOut), (.x2, sN), (.x4, sE), (.x5, sEl), (.x6, sP), (.x7, sPl)]

theorem regSlots_ho : ∀ p ∈ regSlots, p.2 % 8 = 0 ∧ p.2 < 32768 := by decide

theorem fits : Spill.Fits (saved ++ regSlots) := by decide

/-- A number, as the prologue zero-extends it from 32 bits. -/
abbrev zx (v : BitVec 64) : BitVec 64 := (v.setWidth 32).setWidth 64

/-- The frame's slots that the code reads: the saved registers, the
arguments. -/
structure Fr (s : State) (m : Mem) : Prop where
  sv : Spill.Saved (fb s) s.gpr saved m
  rs : Spill.Saved (fb s) s.gpr regSlots m
  dig : m.readW (fb s + BitVec.ofNat 64 sDig) 64 = stackArg s 8
  hl : m.readW (fb s + BitVec.ofNat 64 sHLen) 64 = stackArg s 9
  salt : m.readW (fb s + BitVec.ofNat 64 sSalt) 64 = stackArg s 10
  sl : m.readW (fb s + BitVec.ofNat 64 sSaltLen) 64 = stackArg s 11
  scr : m.readW (fb s + BitVec.ofNat 64 sScrLen) 64 = stackArg s 13
  hsh : m.readW (fb s + BitVec.ofNat 64 sHash) 64 = zx (stackArg s 14)
  mgf : m.readW (fb s + BitVec.ofNat 64 sMgf) 64 = zx (stackArg s 15)

/-- The slots of `Fr`: `[96, 248)`, `[288, 304)` and `[328, 352)` of the
frame. -/
abbrev frA (s : State) : Region := ⟨fb s + BitVec.ofNat 64 96, 152⟩
abbrev frB (s : State) : Region := ⟨fb s + BitVec.ofNat 64 288, 16⟩
abbrev frC (s : State) : Region := ⟨fb s + BitVec.ofNat 64 328, 24⟩

theorem Fr.frame {s : State} {m m' : Mem} (h : Fr s m) {rs : List Region} (hf : Frame rs m m')
    (hA : ∀ r ∈ rs, (frA s).Disjoint r) (hB : ∀ r ∈ rs, (frB s).Disjoint r) (hC : ∀ r ∈ rs, (frC s).Disjoint r) :
    Fr s m' := by
  have hw : ∀ {d : Nat}, (96 ≤ d ∧ d + 8 ≤ 248) → m'.readW (fb s + BitVec.ofNat 64 d) 64 =
      m.readW (fb s + BitVec.ofNat 64 d) 64 := fun hd =>
    hf.readW (r := ⟨fb s + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hA r hr).sub_left (Offset.sub _ hd.1 (by omega))) (by decide)
  have hc : ∀ {d : Nat}, (328 ≤ d ∧ d + 8 ≤ 352) → m'.readW (fb s + BitVec.ofNat 64 d) 64 =
      m.readW (fb s + BitVec.ofNat 64 d) 64 := fun hd =>
    hf.readW (r := ⟨fb s + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hC r hr).sub_left (Offset.sub _ hd.1 (by omega))) (by decide)
  refine ⟨h.sv.frame_in (lo := 96) (n := 152) (by decide) hf hA, fun p hp => ?_, by rw [hw (by decide)]; exact h.dig,
    by rw [hc (by decide)]; exact h.hl, by rw [hw (by decide)]; exact h.salt, by rw [hw (by decide)]; exact h.sl,
    by rw [hw (by decide)]; exact h.scr, by rw [hc (by decide)]; exact h.hsh, by rw [hc (by decide)]; exact h.mgf⟩
  simp only [regSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [hw (by decide)]; exact h.rs _ (by simp [regSlots])
  · rw [hw (by decide)]; exact h.rs _ (by simp [regSlots])
  · rw [hw (by decide)]; exact h.rs _ (by simp [regSlots])
  · rw [hw (by decide)]; exact h.rs _ (by simp [regSlots])
  · rw [hf.readW (r := ⟨fb s + BitVec.ofNat 64 sP, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hB r hr).sub_left (Offset.sub _ (by decide) (by decide))) (by decide)]
    exact h.rs _ (by simp [regSlots])
  · rw [hf.readW (r := ⟨fb s + BitVec.ofNat 64 sPl, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hB r hr).sub_left (Offset.sub _ (by decide) (by decide))) (by decide)]
    exact h.rs _ (by simp [regSlots])

/-- Before the checks. -/
structure AtChk (s u : State) : Prop where
  sp : u.sp = fb s
  rd : u.rd = s.rd
  wr : u.wr = ⟨fb s, frameBytes⟩ :: s.wr
  g : ∀ r, r ∉ [Reg.x9, .x10, .x16, .x19, .x20, .x21, .x23] → u.gpr r = s.gpr r
  x10 : u.gpr .x10 = (s.mem (s.gpr .x2)).setWidth 64
  x19 : u.gpr .x19 = off (stackArg s 12) oSt
  x20 : u.gpr .x20 = stackArg s 12
  x21 : u.gpr .x21 = off (stackArg s 12) oDig
  x23 : u.gpr .x23 = s.gpr .x3
  v : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  mem : Frame [⟨fb s, frameBytes⟩] s.mem u.mem
  fr : Fr s u.mem

theorem wr_frame {s t : State} (hwr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr) {d n : Nat}
    (h : d + n ≤ frameBytes) : InRegions t.wr (fb s + BitVec.ofNat 64 d) n := by
  rw [hwr]; exact in_frame s _ h

/-- During the prologue: the frame's place, `x16` its base, and only it
written. -/
structure InPro (s u : State) : Prop where
  sp : u.sp = fb s
  rd : u.rd = s.rd
  wr : u.wr = ⟨fb s, frameBytes⟩ :: s.wr
  x16 : u.gpr .x16 = fb s
  fr : Frame [⟨fb s, frameBytes⟩] s.mem u.mem

theorem InPro.step {s u u' : State} (h : InPro s u) {r : Reg} (k : Keep [r] u u') (hr : r ≠ .x16) {d : Nat}
    (hd : d + 8 ≤ frameBytes) {v : BitVec 64} (hm : u'.mem = u.mem.writeW (fb s + BitVec.ofNat 64 d) v) :
    InPro s u' :=
  ⟨k.sp.trans h.sp, k.rd.trans h.rd, k.wr.trans h.wr, by rw [k.gpr .x16 (by simpa using hr.symm)]; exact h.x16,
    by rw [hm]; exact h.fr.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ hd (by
      unfold frameBytes at hd; omega))⟩

theorem prologue_ok {D K : Nat} {s u : State} (hp : PreS D K s) (hsp : u.sp = fb s) (hrd : u.rd = s.rd)
    (hwr : u.wr = ⟨fb s, frameBytes⟩ :: s.wr) (hm : u.mem = s.mem) (hg : ∀ r, u.gpr r = s.gpr r)
    (hv : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) :
    WP isa (.block (signPrologue ++ n0 .x2)) u (AtChk s) := by
  unfold signPrologue save regsUp n0 hashArgs
  simp only [List.cons_append, List.append_assoc, List.nil_append]
  refine wp_addSp (by decide) fun u₁ o₁ e₁ => ?_
  rw [hsp, BitVec.add_zero] at e₁
  have hin : ∀ p ∈ saved ++ regSlots, InRegions u₁.wr (u₁.gpr .x16 + BitVec.ofNat 64 p.2) 8 := fun p hp' => by
    rw [e₁, o₁.wr]
    exact wr_frame hwr (by revert p; decide)
  refine Spill.save_ok (b := .x16) (l := saved ++ regSlots) fits.1 hin ?_
  generalize hm₂ : Spill.saveMem u₁.mem (u₁.gpr .x16) u₁.gpr (saved ++ regSlots) = m₂
  have fr₂ : Frame [⟨fb s, frameBytes⟩] s.mem m₂ := by
    rw [← hm₂, e₁, o₁.mem, hm]
    exact Spill.saveMem_frame_base (fun p hp' => by revert p; decide) (by decide) _ _ _
  have sv₂ : Spill.Saved (fb s) s.gpr (saved ++ regSlots) m₂ := by
    rw [← hm₂, e₁]
    intro p hp'
    rw [Spill.saveMem_saved fits _ _ _ p hp']
    have : p.1 ≠ .x16 := by revert p; decide
    rw [o₁.get p.1 (by simpa using this), hg]
  have gs : ∀ r, r ≠ .x16 → u₁.gpr r = s.gpr r := fun r h => by rw [o₁.gpr r (by simpa using h), hg]
  refine wp_mov fun u₃ o₃ e₃ => ?_
  have I₃ : InPro s u₃ := ⟨by rw [o₃.sp]; show u₁.sp = _; rw [o₁.sp, hsp],
    by rw [o₃.rd]; show u₁.rd = _; rw [o₁.rd, hrd], by rw [o₃.wr]; show u₁.wr = _; rw [o₁.wr, hwr],
    by rw [o₃.get .x16]; exact e₁, by rw [o₃.mem]; exact fr₂⟩
  have m₃ : u₃.mem = m₂ := o₃.mem
  -- The stack arguments, from memory the prologue changed only in the frame.
  have ag : ∀ {u : State}, InPro s u → ∀ j, j < 16 →
      InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 (frameBytes + 8 * j)) 8 ∧
      u.mem.readW (u.sp + BitVec.ofNat 64 (frameBytes + 8 * j)) 64 = stackArg s j := fun h j hj =>
    ⟨by rw [h.sp, ← stackArgAddr_fb, h.rd]; exact arg_in hp (Covers.left (Covers.refl _)) hj,
      by rw [h.sp, ← stackArgAddr_fb]; exact arg_frame hp h.fr hj⟩
  have sw : ∀ {u : State}, InPro s u → ∀ {d : Nat}, d + 8 ≤ frameBytes →
      InRegions u.wr (fb s + BitVec.ofNat 64 d) 8 := fun h _ hd => wr_frame h.wr hd
  refine argSlot_ok (v := stackArg s 8) (d := sDig) (by decide) (ag I₃ 8 (by decide)).1 (ag I₃ 8 (by decide)).2
    I₃.x16 (by decide) (by decide) (sw I₃ (by decide)) fun u₄ k₄ _ m₄ => ?_
  have I₄ := I₃.step k₄ (by decide) (by decide) m₄
  refine argSlot_ok (v := stackArg s 9) (d := sHLen) (by decide) (ag I₄ 9 (by decide)).1 (ag I₄ 9 (by decide)).2
    I₄.x16 (by decide) (by decide) (sw I₄ (by decide)) fun u₅ k₅ _ m₅ => ?_
  have I₅ := I₄.step k₅ (by decide) (by decide) m₅
  refine argSlot_ok (v := stackArg s 10) (d := sSalt) (by decide) (ag I₅ 10 (by decide)).1 (ag I₅ 10 (by decide)).2
    I₅.x16 (by decide) (by decide) (sw I₅ (by decide)) fun u₆ k₆ _ m₆ => ?_
  have I₆ := I₅.step k₆ (by decide) (by decide) m₆
  refine argSlot_ok (v := stackArg s 11) (d := sSaltLen) (by decide) (ag I₆ 11 (by decide)).1
    (ag I₆ 11 (by decide)).2 I₆.x16 (by decide) (by decide) (sw I₆ (by decide)) fun u₇ k₇ _ m₇ => ?_
  have I₇ := I₆.step k₇ (by decide) (by decide) m₇
  unfold arg
  refine wp_ldrSp (by decide) (ag I₇ 12 (by decide)).1 fun u₈ o₈ e₈ => ?_
  rw [(ag I₇ 12 (by decide)).2] at e₈
  have I₈ : InPro s u₈ := ⟨o₈.sp.trans I₇.sp, o₈.rd.trans I₇.rd, o₈.wr.trans I₇.wr,
    by rw [o₈.get .x16]; exact I₇.x16, by rw [o₈.mem]; exact I₇.fr⟩
  refine argSlot_ok (v := stackArg s 13) (d := sScrLen) (by decide) (ag I₈ 13 (by decide)).1
    (ag I₈ 13 (by decide)).2 I₈.x16 (by decide) (by decide) (sw I₈ (by decide)) fun u₉ k₉ _ m₉ => ?_
  have I₉ := I₈.step k₉ (by decide) (by decide) m₉
  refine argSlotW_ok (v := stackArg s 14) (d := sHash) (by decide) (ag I₉ 14 (by decide)).1
    (ag I₉ 14 (by decide)).2 I₉.x16 (by decide) (by decide) (sw I₉ (by decide)) fun u₁₀ k₁₀ m₁₀ => ?_
  have I₁₀ := I₉.step k₁₀ (by decide) (by decide) m₁₀
  refine argSlotW_ok (v := stackArg s 15) (d := sMgf) (by decide) (ag I₁₀ 15 (by decide)).1
    (ag I₁₀ 15 (by decide)).2 I₁₀.x16 (by decide) (by decide) (sw I₁₀ (by decide)) fun u₁₂ k₁₂ m₁₂ => ?_
  have I₁₂ := I₁₀.step k₁₂ (by decide) (by decide) m₁₂
  refine wp_addImm (by decide) fun u₁₃ o₁₃ e₁₃ => wp_addImm (by decide) fun u₁₄ o₁₄ e₁₄ => ?_
  have hm₁₂ : u₁₂.mem = ((((((m₂.writeW (fb s + BitVec.ofNat 64 sDig) (stackArg s 8)).writeW
      (fb s + BitVec.ofNat 64 sHLen) (stackArg s 9)).writeW
      (fb s + BitVec.ofNat 64 sSalt) (stackArg s 10)).writeW (fb s + BitVec.ofNat 64 sSaltLen) (stackArg s 11)).writeW
      (fb s + BitVec.ofNat 64 sScrLen) (stackArg s 13)).writeW (fb s + BitVec.ofNat 64 sHash) (zx (stackArg s 14))).writeW
      (fb s + BitVec.ofNat 64 sMgf) (zx (stackArg s 15)) := by
    rw [m₁₂, m₁₀, m₉, o₈.mem, m₇, m₆, m₅, m₄, m₃]
  have W7 : Frame [⟨fb s + BitVec.ofNat 64 sDig, 8⟩, ⟨fb s + BitVec.ofNat 64 sHLen, 8⟩,
      ⟨fb s + BitVec.ofNat 64 sSalt, 8⟩, ⟨fb s + BitVec.ofNat 64 sSaltLen, 8⟩, ⟨fb s + BitVec.ofNat 64 sScrLen, 8⟩,
      ⟨fb s + BitVec.ofNat 64 sHash, 8⟩, ⟨fb s + BitVec.ofNat 64 sMgf, 8⟩] m₂ u₁₂.mem := by
    rw [hm₁₂]
    exact (((((((Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)).writeW (by simp) _
      (Region.contains_self _ _)).writeW (by simp) _ (Region.contains_self _ _)).writeW (by simp) _
      (Region.contains_self _ _)).writeW (by simp) _ (Region.contains_self _ _)).writeW (by simp) _
      (Region.contains_self _ _)).writeW (by simp) _ (Region.contains_self _ _)
  have sv₁₂ : Spill.Saved (fb s) s.gpr (saved ++ regSlots) u₁₂.mem := sv₂.frame W7 fun p hp' r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact Offset.disjoint _ (by revert p; decide) (by revert p; decide) (by decide)
  have K₁₄ : Keep [.x9, .x10, .x16, .x19, .x20, .x21, .x23] { u₁ with mem := m₂ } u₁₄ :=
    (o₃.keep.trans (k₄.trans (k₅.trans (k₆.trans (k₇.trans (o₈.keep.trans (k₉.trans (k₁₀.trans
      (k₁₂.trans (o₁₃.keep.trans o₁₄.keep)))))))))).mono
  have x2₁₄ : u₁₄.gpr .x2 = s.gpr .x2 := by
    rw [K₁₄.gpr .x2 (by decide)]; exact gs .x2 (by decide)
  have hk1 := hp.k1
  have rn : InRegions (u₁₄.rd ++ u₁₄.wr) (s.gpr .x2) 1 := by
    rw [o₁₄.rd, o₁₃.rd, o₁₄.wr, o₁₃.wr, I₁₂.rd, I₁₂.wr]
    refine Covers.left (Covers.trans (Covers.of_mem fun x hx => by
      rw [List.mem_singleton.mp hx]; simp) hp.hrd) _ _ ⟨nR s, List.mem_singleton_self _, ?_⟩
    have := Offset.contains_base (s.gpr .x2) (d := 0) (n := 1) (k := (s.gpr .x3).toNat) (by omega) (by omega)
    rwa [BitVec.add_zero] at this
  refine wp_ldrb (by decide) (by rw [x2₁₄, BitVec.add_zero]) rn fun u₁₆ o₁₆ e₁₆ => wp_nil ?_
  have mem₁₄ : u₁₄.mem = u₁₂.mem := by rw [o₁₄.mem, o₁₃.mem]
  have hn₀ : u₁₄.mem (s.gpr .x2) = s.mem (s.gpr .x2) := by
    rw [mem₁₄]
    refine I₁₂.fr _ fun r hr hc => ?_
    rw [List.mem_singleton.mp hr] at hc
    have := Offset.contains_base (s.gpr .x2) (d := 0) (n := 1) (k := (s.gpr .x3).toNat) (by omega) (by omega)
    rw [BitVec.add_zero] at this
    exact hp.kn _ (frame_sub0 K s _ hc) this
  have K : Keep [.x9, .x10, .x16, .x19, .x20, .x21, .x23] { u₁ with mem := m₂ } u₁₆ := (K₁₄.trans o₁₆.keep).mono
  have mem₁₆ : u₁₆.mem = u₁₂.mem := by rw [o₁₆.mem, mem₁₄]
  have x20 : u₁₂.gpr .x20 = stackArg s 12 := by
    rw [k₁₂.gpr .x20 (by decide), k₁₀.gpr .x20 (by decide), k₉.gpr .x20 (by decide), e₈]
  refine ⟨?sp, ?rd, ?wr, ?g, ?x10, ?x19, ?x20, ?x21, ?x23, ?v, ?mem, ?fr⟩
  case sp => rw [o₁₆.sp, o₁₄.sp, o₁₃.sp, I₁₂.sp]
  case rd => rw [o₁₆.rd, o₁₄.rd, o₁₃.rd, I₁₂.rd]
  case wr => rw [o₁₆.wr, o₁₄.wr, o₁₃.wr, I₁₂.wr]
  case g =>
    intro r hr
    rw [K.gpr r hr]
    exact gs r fun h => hr (by rw [h]; decide)
  case x10 => rw [e₁₆, hn₀]
  case x19 => rw [o₁₆.get .x19, o₁₄.get .x19, e₁₃, x20]
  case x20 => rw [o₁₆.get .x20, o₁₄.get .x20, o₁₃.get .x20, x20]
  case x21 => rw [o₁₆.get .x21, e₁₄, o₁₃.get .x20, x20]
  case x23 =>
    rw [o₁₆.get .x23, o₁₄.get .x23, o₁₃.get .x23, k₁₂.gpr .x23 (by decide), k₁₀.gpr .x23 (by decide),
      k₉.gpr .x23 (by decide), o₈.get .x23, k₇.gpr .x23 (by decide), k₆.gpr .x23 (by decide),
      k₅.gpr .x23 (by decide), k₄.gpr .x23 (by decide), e₃]
    exact gs .x3 (by decide)
  case v =>
    intro r hr
    rw [K.vcs r hr]
    show (u₁.v r).extractLsb' 0 64 = _
    rw [o₁.vcs r hr, hv r hr]
  case mem => rw [mem₁₆]; exact I₁₂.fr
  case fr =>
    rw [mem₁₆]
    refine ⟨sv₁₂.sub fun p hp => List.mem_append_left _ hp, sv₁₂.sub fun p hp => List.mem_append_right _ hp,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [hm₁₂] <;> simp (disch := decide) only [rd_ws, rd_self]

end VG.Proof.RsaPss.AArch64.Sgn
