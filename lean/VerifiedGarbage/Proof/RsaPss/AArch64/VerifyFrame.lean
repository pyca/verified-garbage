import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyPre
import VerifiedGarbage.Proof.RsaPss.AArch64.SignFrame

/-!
# RSASSA-PSS verification on AArch64: the prologue

`prologue_ok`: the callee-saved registers and the arguments in their slots
of the frame (`Fr`), `scratch` in `x20`, `x19` and `x21` set, `k` in `x23`
and `n₀` in `x10` (`AtChk`).
-/

namespace VG.Proof.RsaPss.AArch64.Vfy

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_strx wp_nil wp_addImm wp_ldrb)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_addSp wp_ldrSp wp_mov wp_movw)
open VG.Proof.RsaPss.AArch64 (off)
open VG.Proof.RsaPss.AArch64.Sgn (stk kR fb kb frame_sub0 stackArgAddr_fb in_frame wr_frame)

/-- The argument registers kept in slots of the frame. -/
def regSlots : List (Reg × Nat) := [(.x0, sN), (.x2, sE), (.x3, sEl), (.x4, sDig), (.x5, sOut), (.x7, sSaltLen)]

theorem fits : Spill.Fits (saved ++ regSlots) := by decide

/-- `any_salt_len`, zero-extended from its 32 bits. -/
abbrev anyV (s : State) : BitVec 64 := ((stackArg s 0).setWidth 32).setWidth 64

/-- The frame's slots that the code reads: the saved registers, the
arguments. -/
structure Fr (s : State) (m : Mem) : Prop where
  sv : Spill.Saved (fb s) s.gpr saved m
  rs : Spill.Saved (fb s) s.gpr regSlots m
  scr : m.readW (fb s + BitVec.ofNat 64 sScrLen) 64 = stackArg s 2
  any : m.readW (fb s + BitVec.ofNat 64 sAny) 64 = anyV s
  pre : m.readW (fb s + BitVec.ofNat 64 sPre) 64 = stackArg s 3
  preLen : m.readW (fb s + BitVec.ofNat 64 sPreLen) 64 = stackArg s 4

/-- The slots of `Fr`: `[96, 248)`, `[264, 272)` and `[312, 328)` of the
frame. -/
abbrev frA (s : State) : Region := ⟨fb s + BitVec.ofNat 64 96, 152⟩
abbrev frB (s : State) : Region := ⟨fb s + BitVec.ofNat 64 264, 8⟩
abbrev frC (s : State) : Region := ⟨fb s + BitVec.ofNat 64 312, 16⟩

theorem Fr.frame {s : State} {m m' : Mem} (h : Fr s m) {rs : List Region} (hf : Frame rs m m')
    (hA : ∀ r ∈ rs, (frA s).Disjoint r) (hB : ∀ r ∈ rs, (frB s).Disjoint r) (hC : ∀ r ∈ rs, (frC s).Disjoint r) :
    Fr s m' := by
  have hw : ∀ {d : Nat}, (96 ≤ d ∧ d + 8 ≤ 248) → m'.readW (fb s + BitVec.ofNat 64 d) 64 =
      m.readW (fb s + BitVec.ofNat 64 d) 64 := fun hd =>
    hf.readW (r := ⟨fb s + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hA r hr).sub_left (Offset.sub _ hd.1 (by omega))) (by decide)
  have hc : ∀ {d : Nat}, (312 ≤ d ∧ d + 8 ≤ 328) → m'.readW (fb s + BitVec.ofNat 64 d) 64 =
      m.readW (fb s + BitVec.ofNat 64 d) 64 := fun hd =>
    hf.readW (r := ⟨fb s + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hC r hr).sub_left (Offset.sub _ hd.1 (by omega))) (by decide)
  refine ⟨h.sv.frame_in (lo := 96) (n := 152) (by decide) hf hA, fun p hp => ?_, by rw [hw (by decide)]; exact h.scr,
    by rw [hf.readW (r := frB s) (Region.contains_self _ _) hB (by decide)]; exact h.any,
    by rw [hc (by decide)]; exact h.pre, by rw [hc (by decide)]; exact h.preLen⟩
  rw [hw (by revert p; decide)]
  exact h.rs p hp

/-- Before the checks. -/
structure AtChk (s u : State) : Prop where
  sp : u.sp = fb s
  rd : u.rd = s.rd
  wr : u.wr = ⟨fb s, frameBytes⟩ :: s.wr
  g : ∀ r, r ∉ [Reg.x9, .x10, .x16, .x19, .x20, .x21, .x23] → u.gpr r = s.gpr r
  x10 : u.gpr .x10 = (s.mem (s.gpr .x0)).setWidth 64
  x19 : u.gpr .x19 = off (stackArg s 1) oSt
  x20 : u.gpr .x20 = stackArg s 1
  x21 : u.gpr .x21 = off (stackArg s 1) oDig
  x23 : u.gpr .x23 = s.gpr .x1
  v : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  mem : Frame [⟨fb s, frameBytes⟩] s.mem u.mem
  fr : Fr s u.mem

theorem prologue_ok {D K : Nat} {s u : State} (hp : PreV D K s) (hsp : u.sp = fb s) (hrd : u.rd = s.rd)
    (hwr : u.wr = ⟨fb s, frameBytes⟩ :: s.wr) (hm : u.mem = s.mem) (hg : ∀ r, u.gpr r = s.gpr r)
    (hv : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) :
    WP isa (.block (verifyPrologue ++ n0)) u (AtChk s) := by
  unfold verifyPrologue save regsUp n0 arg ld
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
  have sp₃ : u₃.sp = fb s := by rw [o₃.sp]; show u₁.sp = _; rw [o₁.sp, hsp]
  have rd₃ : u₃.rd = s.rd := by rw [o₃.rd]; show u₁.rd = _; rw [o₁.rd, hrd]
  have wr₃ : u₃.wr = ⟨fb s, frameBytes⟩ :: s.wr := by rw [o₃.wr]; show u₁.wr = _; rw [o₁.wr, hwr]
  have x16₃ : u₃.gpr .x16 = fb s := by rw [o₃.get .x16]; exact e₁
  have aj : ∀ j, u₃.sp + BitVec.ofNat 64 (frameBytes + 8 * j) = stackArgAddr s j := fun j => by
    rw [sp₃, stackArgAddr_fb]
  have rj : ∀ j, j < 5 → InRegions (u₃.rd ++ u₃.wr) (stackArgAddr s j) 8 := fun j hj => by
    rw [rd₃]; exact arg_in hp (Covers.left (Covers.refl _)) hj
  -- `any_salt_len`.
  refine wp_ldrSp (by decide) (by rw [aj]; exact rj 0 (by decide)) fun u₄ o₄ e₄ => ?_
  rw [aj, o₃.mem, show ({ u₁ with mem := m₂ } : State).mem = m₂ from rfl, arg_frame hp fr₂ (by decide)] at e₄
  refine wp_movw fun u₄' o₄' e₄' => ?_
  rw [e₄] at e₄'
  refine wp_strx (by decide) (by rw [o₄'.get .x16, o₄.get .x16, x16₃])
    (by rw [o₄'.wr, o₄.wr, wr₃]; exact in_frame s _ (by decide)) fun u₅ m₅ => ?_
  have fr₅ : Frame [⟨fb s, frameBytes⟩] s.mem u₅.mem := by
    rw [m₅.mem, o₄'.mem, o₄.mem, o₃.mem]
    exact fr₂.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  have sp₅ : u₅.sp = u₃.sp := by rw [m₅.sp, o₄'.sp, o₄.sp]
  have rd₅ : u₅.rd = u₃.rd := by rw [m₅.rd, o₄'.rd, o₄.rd]
  have wr₅ : u₅.wr = u₃.wr := by rw [m₅.wr, o₄'.wr, o₄.wr]
  -- `scratch` and `scratch_len`.
  refine wp_ldrSp (by decide) (by rw [sp₅, rd₅, wr₅, aj]; exact rj 1 (by decide)) fun u₁₀ o₁₀ e₁₀ => ?_
  rw [sp₅, aj, arg_frame hp fr₅ (by decide)] at e₁₀
  refine wp_ldrSp (by decide) (by rw [o₁₀.sp, o₁₀.rd, o₁₀.wr, sp₅, rd₅, wr₅, aj]; exact rj 2 (by decide))
    fun u₁₁ o₁₁ e₁₁ => ?_
  rw [o₁₀.sp, sp₅, aj, o₁₀.mem, arg_frame hp fr₅ (by decide)] at e₁₁
  have x16₁₁ : u₁₁.gpr .x16 = fb s := by
    rw [o₁₁.get .x16, o₁₀.get .x16, m₅.gpr, o₄'.get .x16, o₄.get .x16, x16₃]
  refine wp_strx (by decide) (by rw [x16₁₁]) (by rw [o₁₁.wr, o₁₀.wr, wr₅, wr₃]; exact in_frame s _ (by decide))
    fun w₁ n₁ => ?_
  have fw₁ : Frame [⟨fb s, frameBytes⟩] s.mem w₁.mem := by
    rw [n₁.mem, o₁₁.mem, o₁₀.mem]
    exact fr₅.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  have sp₁ : w₁.sp = u₃.sp := by rw [n₁.sp, o₁₁.sp, o₁₀.sp, sp₅]
  have rd₁ : w₁.rd = u₃.rd := by rw [n₁.rd, o₁₁.rd, o₁₀.rd, rd₅]
  have wr₁ : w₁.wr = u₃.wr := by rw [n₁.wr, o₁₁.wr, o₁₀.wr, wr₅]
  -- `pre` and `pre_len`.
  refine wp_ldrSp (by decide) (by rw [sp₁, rd₁, wr₁, aj]; exact rj 3 (by decide)) fun w₂ p₂ f₂ => ?_
  rw [sp₁, aj, arg_frame hp fw₁ (by decide)] at f₂
  have x16₂ : w₂.gpr .x16 = fb s := by rw [p₂.get .x16, n₁.gpr, x16₁₁]
  refine wp_strx (by decide) (by rw [x16₂]) (by rw [p₂.wr, wr₁, wr₃]; exact in_frame s _ (by decide))
    fun w₃ n₃ => ?_
  have fw₃ : Frame [⟨fb s, frameBytes⟩] s.mem w₃.mem := by
    rw [n₃.mem, p₂.mem]
    exact fw₁.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  have r₄ : InRegions (w₃.rd ++ w₃.wr) (w₃.sp + BitVec.ofNat 64 (frameBytes + 8 * 4)) 8 := by
    rw [n₃.sp, p₂.sp, n₃.rd, p₂.rd, n₃.wr, p₂.wr, sp₁, rd₁, wr₁, aj]; exact rj 4 (by decide)
  refine wp_ldrSp (by decide) r₄ fun w₄ p₄ f₄ => ?_
  rw [n₃.sp, p₂.sp, sp₁, aj, arg_frame hp fw₃ (by decide)] at f₄
  refine wp_strx (by decide) (by rw [p₄.get .x16, n₃.gpr, x16₂])
    (by rw [p₄.wr, n₃.wr, p₂.wr, wr₁, wr₃]; exact in_frame s _ (by decide)) fun u₁₂ m₁₂ => ?_
  refine wp_addImm (by decide) fun u₁₃ o₁₃ e₁₃ => wp_addImm (by decide) fun u₁₄ o₁₄ e₁₄ => ?_
  have hm₁₂ : u₁₂.mem = (((m₂.writeW (fb s + BitVec.ofNat 64 sAny) (anyV s)).writeW
      (fb s + BitVec.ofNat 64 sScrLen) (stackArg s 2)).writeW (fb s + BitVec.ofNat 64 sPre) (stackArg s 3)).writeW
      (fb s + BitVec.ofNat 64 sPreLen) (stackArg s 4) := by
    rw [m₁₂.mem, p₄.mem, f₄, n₃.mem, p₂.mem, f₂, n₁.mem, o₁₁.mem, o₁₀.mem, m₅.mem, o₄'.mem, o₄.mem, o₃.mem, e₁₁,
      e₄']
  have W4 : Frame [⟨fb s + BitVec.ofNat 64 sAny, 8⟩, ⟨fb s + BitVec.ofNat 64 sScrLen, 8⟩,
      ⟨fb s + BitVec.ofNat 64 sPre, 8⟩, ⟨fb s + BitVec.ofNat 64 sPreLen, 8⟩] m₂ u₁₂.mem := by
    rw [hm₁₂]
    exact ((((Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)).writeW (by simp) _
      (Region.contains_self _ _)).writeW (by simp) _ (Region.contains_self _ _)).writeW (by simp) _
      (Region.contains_self _ _)
  have sv₁₂ : Spill.Saved (fb s) s.gpr (saved ++ regSlots) u₁₂.mem := sv₂.frame W4 fun p hp' r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact Offset.disjoint _ (by revert p; decide) (by revert p; decide) (by decide)
  have fr₁₂ : Frame [⟨fb s, frameBytes⟩] s.mem u₁₂.mem := by
    rw [m₁₂.mem, p₄.mem]
    exact fw₃.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  have sp₁₄ : u₁₄.sp = fb s := by rw [o₁₄.sp, o₁₃.sp, m₁₂.sp, p₄.sp, n₃.sp, p₂.sp, sp₁, sp₃]
  have rd₁₄ : u₁₄.rd = s.rd := by rw [o₁₄.rd, o₁₃.rd, m₁₂.rd, p₄.rd, n₃.rd, p₂.rd, rd₁, rd₃]
  have wr₁₄ : u₁₄.wr = ⟨fb s, frameBytes⟩ :: s.wr := by
    rw [o₁₄.wr, o₁₃.wr, m₁₂.wr, p₄.wr, n₃.wr, p₂.wr, wr₁, wr₃]
  have mem₁₄ : u₁₄.mem = u₁₂.mem := by rw [o₁₄.mem, o₁₃.mem]
  have rN : InRegions (u₁₄.rd ++ u₁₄.wr) (u₁₄.sp + BitVec.ofNat 64 sN) 8 := by
    rw [sp₁₄, rd₁₄, wr₁₄]
    exact InRegions_append_cons.mpr (.inl (Offset.contains_base _ (by decide) (by decide)))
  refine wp_ldrSp (by decide) rN fun u₁₅ o₁₅ e₁₅ => ?_
  rw [sp₁₄, mem₁₄, sv₁₂ (.x0, sN) (by simp [regSlots])] at e₁₅
  have hk1 := hp.k1
  have rn : InRegions (u₁₅.rd ++ u₁₅.wr) (s.gpr .x0) 1 := by
    rw [o₁₅.rd, o₁₅.wr, rd₁₄, wr₁₄]
    refine Covers.left (Covers.trans (Covers.of_mem fun x hx => by
      rw [List.mem_singleton.mp hx]; simp) hp.hrd) _ _ ⟨nR s, List.mem_singleton_self _, ?_⟩
    have := Offset.contains_base (s.gpr .x0) (d := 0) (n := 1) (k := (s.gpr .x1).toNat) (by omega) (by omega)
    rwa [BitVec.add_zero] at this
  refine wp_ldrb (by decide) (by rw [e₁₅, BitVec.add_zero]) rn fun u₁₆ o₁₆ e₁₆ => wp_nil ?_
  have hn₀ : u₁₅.mem (s.gpr .x0) = s.mem (s.gpr .x0) := by
    rw [o₁₅.mem, mem₁₄]
    refine fr₁₂ _ fun r hr hc => ?_
    rw [List.mem_singleton.mp hr] at hc
    have := Offset.contains_base (s.gpr .x0) (d := 0) (n := 1) (k := (s.gpr .x1).toNat) (by omega) (by omega)
    rw [BitVec.add_zero] at this
    exact hp.kn _ (frame_sub0 K s _ hc) this
  have K : Keep [.x9, .x10, .x16, .x19, .x20, .x21, .x23] { u₁ with mem := m₂ } u₁₆ :=
    (o₃.keep.trans (o₄.keep.trans (o₄'.keep.trans (m₅.keep.trans
      (o₁₀.keep.trans (o₁₁.keep.trans (n₁.keep.trans (p₂.keep.trans (n₃.keep.trans (p₄.keep.trans
      (m₁₂.keep.trans (o₁₃.keep.trans (o₁₄.keep.trans (o₁₅.keep.trans o₁₆.keep)))))))))))))).mono
  have mem₁₆ : u₁₆.mem = u₁₂.mem := by rw [o₁₆.mem, o₁₅.mem, mem₁₄]
  have x20 : u₁₂.gpr .x20 = stackArg s 1 := by rw [m₁₂.gpr, p₄.get .x20, n₃.gpr, p₂.get .x20, n₁.gpr, o₁₁.get .x20, e₁₀]
  refine ⟨?sp, ?rd, ?wr, ?g, ?x10, ?x19, ?x20, ?x21, ?x23, ?v, ?mem, ?fr⟩
  case sp => rw [o₁₆.sp, o₁₅.sp, sp₁₄]
  case rd => rw [o₁₆.rd, o₁₅.rd, rd₁₄]
  case wr => rw [o₁₆.wr, o₁₅.wr, wr₁₄]
  case g =>
    intro r hr
    rw [K.gpr r hr]
    exact gs r fun h => hr (by rw [h]; decide)
  case x10 => rw [e₁₆, hn₀]
  case x19 => rw [o₁₆.get .x19, o₁₅.get .x19, o₁₄.get .x19, e₁₃, x20]
  case x20 => rw [o₁₆.get .x20, o₁₅.get .x20, o₁₄.get .x20, o₁₃.get .x20, x20]
  case x21 => rw [o₁₆.get .x21, o₁₅.get .x21, e₁₄, o₁₃.get .x20, x20]
  case x23 =>
    rw [o₁₆.get .x23, o₁₅.get .x23, o₁₄.get .x23, o₁₃.get .x23, m₁₂.gpr, p₄.get .x23, n₃.gpr, p₂.get .x23,
      n₁.gpr, o₁₁.get .x23, o₁₀.get .x23, m₅.gpr, o₄'.get .x23, o₄.get .x23, e₃]
    exact gs .x1 (by decide)
  case v =>
    intro r hr
    rw [K.vcs r hr]
    show (u₁.v r).extractLsb' 0 64 = _
    rw [o₁.vcs r hr, hv r hr]
  case mem => rw [mem₁₆]; exact fr₁₂
  case fr =>
    rw [mem₁₆]
    have r2 : ∀ {d : Nat}, d + 8 ≤ frameBytes → (d + 8 ≤ sPre ∨ sPreLen + 8 ≤ d) →
        u₁₂.mem.readW (fb s + BitVec.ofNat 64 d) 64 = Mem.readW ((m₂.writeW (fb s + BitVec.ofNat 64 sAny)
          (anyV s)).writeW (fb s + BitVec.ofNat 64 sScrLen) (stackArg s 2)) (fb s + BitVec.ofNat 64 d) 64 :=
      fun hd h => by
        rw [hm₁₂, Mem.readW_writeW_sep (Offset.sep _ (by unfold sPre sPreLen at *; omega)
          (by unfold frameBytes at hd; omega) (by decide)) (by decide),
          Mem.readW_writeW_sep (Offset.sep _ (by unfold sPre sPreLen at *; omega)
          (by unfold frameBytes at hd; omega) (by decide)) (by decide)]
    refine ⟨sv₁₂.sub fun p hp => List.mem_append_left _ hp, sv₁₂.sub fun p hp => List.mem_append_right _ hp,
      by rw [r2 (by decide) (by decide), Mem.readW_writeW_self64], ?_, ?_, ?_⟩
    · rw [r2 (by decide) (by decide), Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide))
        (by decide), Mem.readW_writeW_self64]
    · rw [hm₁₂, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self64]
    · rw [hm₁₂, Mem.readW_writeW_self64]

end VG.Proof.RsaPss.AArch64.Vfy
