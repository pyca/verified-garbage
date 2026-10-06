import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyFrame
import VerifiedGarbage.Proof.RsaPss.AArch64.SignCall
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callee

/-!
# RSASSA-PSS verification on AArch64: the call of the public operation

`pubArgs_ok`: after `dbRegs` (`PreCall`), the call's stack arguments and
registers (`AtCall`); `call_ok`: the call writes RSAVP1 of the signature (or
zeros) to `EM` and keeps the frame and our registers (`AfterCall`).
-/

namespace VG.Proof.RsaPss.AArch64.Vfy

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_strx wp_nil wp_movz wp_add wp_addImm wp_subImm)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_addSp wp_ldrSp wp_mov setWidth_ofNat16 PdChecked PdOk PubLay pdRd
  pubWr pdCall sa0)
open VG.Proof.RsaPss.AArch64 (off)
open VG.Proof.RsaPss.AArch64.Sgn (stk kR fb kb fb_eq frame_sub frame_sub0 below_fb below_sub in_frame)

/-- The working space. -/
abbrev scr (s : State) : Addr := stackArg s 1

/-- `EM`, and the call's working space. -/
abbrev emR (s : State) : Region := ⟨off (scr s) oEm, (s.gpr .x1).toNat⟩
abbrev scR (s : State) : Region := ⟨off (scr s) oRsa, (stackArg s 2 - BitVec.ofNat 64 1024).toNat * 8⟩

theorem scr_toNat {D K : Nat} {s : State} (hp : PreV D K s) :
    (stackArg s 2 - BitVec.ofNat 64 1024).toNat = (stackArg s 2).toNat - 1024 := by
  have := hp.hs
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := (stackArg s 2).isLt
  omega

theorem em_sub {D K : Nat} {s : State} (hp : PreV D K s) : Region.Sub (emR s) (sR s) :=
  Offset.sub_base _ (by have := hp.hs; have := hp.k2; unfold oEm; omega)

theorem sc_sub {D K : Nat} {s : State} (hp : PreV D K s) : Region.Sub (scR s) (sR s) :=
  Offset.sub_base _ (by rw [scr_toNat hp]; have := hp.hs; unfold oRsa; omega)

theorem rsa_sub {D K : Nat} {s : State} (hp : PreV D K s) : Region.Sub ⟨scr s, oRsa⟩ (sR s) :=
  Region.sub_prefix (by have := hp.hs; unfold oRsa; omega)

theorem a16_sub (K : Nat) (s : State) : Region.Sub ⟨fb s, 16⟩ (kR K s) := by
  have := frame_sub K s (d := 0) (n := 16) (by decide); rwa [BitVec.add_zero] at this

/-- After `dbRegs`, with `lo` and the mask `c` in their slots. -/
structure PreCall (D : Nat) (s : State) (lo : Nat) (c : Byte) (w : State) : Prop where
  sp : w.sp = fb s
  rd : w.rd = s.rd
  wr : w.wr = ⟨fb s, frameBytes⟩ :: s.wr
  x19 : w.gpr .x19 = off (scr s) oSt
  x20 : w.gpr .x20 = scr s
  x21 : w.gpr .x21 = off (scr s) oDig
  x23 : w.gpr .x23 = s.gpr .x1
  x24 : w.gpr .x24 = off (scr s) (oEm + lo)
  x25 : w.gpr .x25 = BitVec.ofNat 64 ((s.gpr .x1).toNat - lo - D - 1)
  v : ∀ r ∈ preservedV, (w.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  mem : Frame [⟨fb s, frameBytes⟩] s.mem w.mem
  fr : Fr s w.mem
  lo : w.mem.readW (fb s + BitVec.ofNat 64 sLo) 64 = BitVec.ofNat 64 lo
  c : w.mem.readW (fb s + BitVec.ofNat 64 sC) 64 = BitVec.setWidth 64 c

/-- At the call. -/
structure AtCall (D : Nat) (s : State) (lo : Nat) (c : Byte) (t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  x0 : t.gpr .x0 = off (scr s) oEm
  x1 : t.gpr .x1 = s.gpr .x1
  x2 : t.gpr .x2 = stackArg s 3
  x3 : t.gpr .x3 = stackArg s 4
  x4 : t.gpr .x4 = s.gpr .x2
  x5 : t.gpr .x5 = s.gpr .x3
  x6 : t.gpr .x6 = s.gpr .x5
  x7 : t.gpr .x7 = s.gpr .x1
  x19 : t.gpr .x19 = off (scr s) oSt
  x20 : t.gpr .x20 = scr s
  x21 : t.gpr .x21 = off (scr s) oDig
  x23 : t.gpr .x23 = s.gpr .x1
  x24 : t.gpr .x24 = off (scr s) (oEm + lo)
  x25 : t.gpr .x25 = BitVec.ofNat 64 ((s.gpr .x1).toNat - lo - D - 1)
  v : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  a0 : stackArg t 0 = off (scr s) oRsa
  a1 : stackArg t 1 = stackArg s 2 - BitVec.ofNat 64 1024
  mem : Frame [⟨fb s, frameBytes⟩] s.mem t.mem
  fr : Fr s t.mem
  lo : t.mem.readW (fb s + BitVec.ofNat 64 sLo) 64 = BitVec.ofNat 64 lo
  c : t.mem.readW (fb s + BitVec.ofNat 64 sC) 64 = BitVec.setWidth 64 c

theorem fr16 (s : State) : ∀ r ∈ [(⟨fb s, 16⟩ : Region)],
    (frA s).Disjoint r ∧ (frB s).Disjoint r ∧ (frC s).Disjoint r := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact ⟨Offset.disjoint_base _ (by decide) (by decide), Offset.disjoint_base _ (by decide) (by decide),
    Offset.disjoint_base _ (by decide) (by decide)⟩

theorem pubArgs_ok {D : Nat} {s w : State} {lo : Nat} {c : Byte} (hm : PreCall D s lo c w) :
    WP isa (.block pubArgs) w (AtCall D s lo c) := by
  unfold pubArgs ld
  have rsl : ∀ {u : State} {d : Nat}, u.sp = fb s → u.rd = s.rd → u.wr = ⟨fb s, frameBytes⟩ :: s.wr →
      d + 8 ≤ frameBytes → InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 d) 8 := fun hsp hrd hwr hd => by
    rw [hsp, hrd, hwr]
    exact InRegions_append_cons.mpr (.inl (Offset.contains_base _ hd (by unfold frameBytes at hd; omega)))
  refine wp_addSp (by decide) fun u₁ o₁ e₁ => wp_movz fun u₂ o₂ e₂ => wp_add fun u₃ o₃ e₃ => ?_
  rw [hm.sp, BitVec.add_zero] at e₁
  have O₃ : Only [.x16, .x9] w u₃ := (o₁.trans (o₂.trans o₃)).mono
  have x9₃ : u₃.gpr .x9 = off (scr s) oRsa := by
    rw [e₃, e₂, o₂.get .x20, o₁.get .x20, hm.x20, setWidth_ofNat16 (by decide)]
  refine wp_strx (a := fb s + BitVec.ofNat 64 0) (by decide) (by rw [o₃.get .x16, o₂.get .x16, e₁])
    (by rw [O₃.wr, hm.wr]; exact in_frame _ _ (by decide)) fun u₄ m₄ => ?_
  have sp₄ : u₄.sp = fb s := by rw [m₄.sp, O₃.sp, hm.sp]
  have rd₄ : u₄.rd = s.rd := by rw [m₄.rd, O₃.rd, hm.rd]
  have wr₄ : u₄.wr = ⟨fb s, frameBytes⟩ :: s.wr := by rw [m₄.wr, O₃.wr, hm.wr]
  have f₄ : Frame [(⟨fb s, 16⟩ : Region)] w.mem u₄.mem := by
    rw [m₄.mem, O₃.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  have frX : ∀ {m : Mem}, Frame [(⟨fb s, 16⟩ : Region)] w.mem m → Fr s m := fun h =>
    hm.fr.frame h (fun r hr => ((fr16 s) r hr).1) (fun r hr => ((fr16 s) r hr).2.1) (fun r hr => ((fr16 s) r hr).2.2)
  refine wp_ldrSp (by decide) (rsl sp₄ rd₄ wr₄ (by decide)) fun u₅ o₅ e₅ => ?_
  rw [sp₄, (frX f₄).scr] at e₅
  refine wp_subImm (by decide) fun u₆ o₆ e₆ => ?_
  have x16₆ : u₆.gpr .x16 = fb s := by rw [o₆.get .x16, o₅.get .x16, m₄.gpr, o₃.get .x16, o₂.get .x16, e₁]
  refine wp_strx (a := fb s + BitVec.ofNat 64 8) (by decide) (by rw [x16₆])
    (by rw [o₆.wr, o₅.wr, wr₄]; exact in_frame _ _ (by decide)) fun u₇ m₇ => ?_
  have hm₇ : u₇.mem = (w.mem.writeW (fb s + BitVec.ofNat 64 0) (off (scr s) oRsa)).writeW
      (fb s + BitVec.ofNat 64 8) (stackArg s 2 - BitVec.ofNat 64 1024) := by
    rw [m₇.mem, o₆.mem, o₅.mem, e₆, e₅, m₄.mem, O₃.mem, x9₃]
  have f₇ : Frame [(⟨fb s, 16⟩ : Region)] w.mem u₇.mem := by
    rw [hm₇]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  have F₇ := frX f₇
  have sp₇ : u₇.sp = fb s := by rw [m₇.sp, o₆.sp, o₅.sp, sp₄]
  have rd₇ : u₇.rd = s.rd := by rw [m₇.rd, o₆.rd, o₅.rd, rd₄]
  have wr₇ : u₇.wr = ⟨fb s, frameBytes⟩ :: s.wr := by rw [m₇.wr, o₆.wr, o₅.wr, wr₄]
  have K₇ : Keep [.x16, .x9] w u₇ := (O₃.keep.trans (m₄.keep.trans (o₅.keep.trans (o₆.keep.trans m₇.keep)))).mono
  refine wp_addImm (by decide) fun u₈ o₈ e₈ => wp_mov fun u₉ o₉ e₉ => ?_
  refine wp_ldrSp (by decide) (by rw [o₉.sp, o₈.sp, o₉.rd, o₈.rd, o₉.wr, o₈.wr]; exact rsl sp₇ rd₇ wr₇ (by decide))
    fun u₁₀ o₁₀ e₁₀ => ?_
  have r₁₀ : InRegions (u₁₀.rd ++ u₁₀.wr) (u₁₀.sp + BitVec.ofNat 64 sPreLen) 8 := by
    rw [o₁₀.sp, o₉.sp, o₈.sp, o₁₀.rd, o₉.rd, o₈.rd, o₁₀.wr, o₉.wr, o₈.wr]; exact rsl sp₇ rd₇ wr₇ (by decide)
  refine wp_ldrSp (by decide) r₁₀ fun u₁₁ o₁₁ e₁₁ => ?_
  have sp₁₁ : u₁₁.sp = fb s := by rw [o₁₁.sp, o₁₀.sp, o₉.sp, o₈.sp, sp₇]
  have rd₁₁ : u₁₁.rd = s.rd := by rw [o₁₁.rd, o₁₀.rd, o₉.rd, o₈.rd, rd₇]
  have wr₁₁ : u₁₁.wr = ⟨fb s, frameBytes⟩ :: s.wr := by rw [o₁₁.wr, o₁₀.wr, o₉.wr, o₈.wr, wr₇]
  have mem₁₁ : u₁₁.mem = u₇.mem := by rw [o₁₁.mem, o₁₀.mem, o₉.mem, o₈.mem]
  refine wp_ldrSp (by decide) (rsl sp₁₁ rd₁₁ wr₁₁ (by decide)) fun u₁₂ o₁₂ e₁₂ => ?_
  refine wp_ldrSp (by decide) (by rw [o₁₂.sp, o₁₂.rd, o₁₂.wr]; exact rsl sp₁₁ rd₁₁ wr₁₁ (by decide))
    fun u₁₃ o₁₃ e₁₃ => ?_
  have r₁₃ : InRegions (u₁₃.rd ++ u₁₃.wr) (u₁₃.sp + BitVec.ofNat 64 sOut) 8 := by
    rw [o₁₃.sp, o₁₂.sp, o₁₃.rd, o₁₂.rd, o₁₃.wr, o₁₂.wr]; exact rsl sp₁₁ rd₁₁ wr₁₁ (by decide)
  refine wp_ldrSp (by decide) r₁₃ fun u₁₄ o₁₄ e₁₄ => wp_mov fun u₁₅ o₁₅ e₁₅ => wp_nil ?_
  have O : Only [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7] u₇ u₁₅ :=
    (o₈.trans (o₉.trans (o₁₀.trans (o₁₁.trans (o₁₂.trans (o₁₃.trans (o₁₄.trans o₁₅))))))).mono
  have x23 : u₇.gpr .x23 = s.gpr .x1 := by rw [K₇.get .x23, hm.x23]
  rw [o₉.sp, o₈.sp, sp₇, o₉.mem, o₈.mem, F₇.pre] at e₁₀
  rw [o₁₀.sp, o₉.sp, o₈.sp, sp₇, o₁₀.mem, o₉.mem, o₈.mem, F₇.preLen] at e₁₁
  rw [sp₁₁, mem₁₁, F₇.rs (.x2, sE) (by simp [regSlots])] at e₁₂
  rw [o₁₂.sp, sp₁₁, o₁₂.mem, mem₁₁, F₇.rs (.x3, sEl) (by simp [regSlots])] at e₁₃
  rw [o₁₃.sp, o₁₂.sp, sp₁₁, o₁₃.mem, o₁₂.mem, mem₁₁, F₇.rs (.x5, sOut) (by simp [regSlots])] at e₁₄
  have mem₁₅ : u₁₅.mem = u₇.mem := O.mem
  exact {
    sp := by rw [o₁₅.sp, o₁₄.sp, o₁₃.sp, o₁₂.sp, sp₁₁]
    rd := by rw [o₁₅.rd, o₁₄.rd, o₁₃.rd, o₁₂.rd, rd₁₁]
    wr := by rw [o₁₅.wr, o₁₄.wr, o₁₃.wr, o₁₂.wr, wr₁₁]
    x0 := by
      rw [o₁₅.get .x0, o₁₄.get .x0, o₁₃.get .x0, o₁₂.get .x0, o₁₁.get .x0, o₁₀.get .x0, o₉.get .x0, e₈,
        K₇.get .x20, hm.x20]
    x1 := by rw [o₁₅.get .x1, o₁₄.get .x1, o₁₃.get .x1, o₁₂.get .x1, o₁₁.get .x1, o₁₀.get .x1, e₉, o₈.get .x23, x23]
    x2 := by rw [o₁₅.get .x2, o₁₄.get .x2, o₁₃.get .x2, o₁₂.get .x2, o₁₁.get .x2, e₁₀]
    x3 := by rw [o₁₅.get .x3, o₁₄.get .x3, o₁₃.get .x3, o₁₂.get .x3, e₁₁]
    x4 := by rw [o₁₅.get .x4, o₁₄.get .x4, o₁₃.get .x4, e₁₂]
    x5 := by rw [o₁₅.get .x5, o₁₄.get .x5, e₁₃]
    x6 := by rw [o₁₅.get .x6, e₁₄]
    x7 := by
      rw [e₁₅, o₁₄.get .x23, o₁₃.get .x23, o₁₂.get .x23, o₁₁.get .x23, o₁₀.get .x23, o₉.get .x23, o₈.get .x23, x23]
    x19 := by rw [O.get .x19, K₇.get .x19, hm.x19]
    x20 := by rw [O.get .x20, K₇.get .x20, hm.x20]
    x21 := by rw [O.get .x21, K₇.get .x21, hm.x21]
    x23 := by rw [O.get .x23, K₇.get .x23, hm.x23]
    x24 := by rw [O.get .x24, K₇.get .x24, hm.x24]
    x25 := by rw [O.get .x25, K₇.get .x25, hm.x25]
    v := fun r hr => by rw [O.vcs r hr, K₇.vcs r hr, hm.v r hr]
    a0 := by
      show u₁₅.mem.readW (stackArgAddr u₁₅ 0) 64 = _
      rw [sa0, mem₁₅, o₁₅.sp, o₁₄.sp, o₁₃.sp, o₁₂.sp, sp₁₁, hm₇]
      conv => lhs; arg 2; rw [← BitVec.add_zero (fb s)]
      rw [Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self64]
    a1 := by
      show u₁₅.mem.readW (stackArgAddr u₁₅ 1) 64 = _
      rw [stackArgAddr, mem₁₅, o₁₅.sp, o₁₄.sp, o₁₃.sp, o₁₂.sp, sp₁₁, hm₇]
      exact Mem.readW_writeW_self64 _ _ _
    mem := by
      rw [mem₁₅]
      exact hm.mem.trans (f₇.sub fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact ⟨⟨fb s, frameBytes⟩, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩)
    fr := by rw [mem₁₅]; exact F₇
    lo := by
      rw [mem₁₅, hm₇, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide), hm.lo]
    c := by
      rw [mem₁₅, hm₇, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide), hm.c] }

/-! ## The call -/

/-- RSAVP1 of the signature, as the entry state gives it. -/
def pubOut (s : State) : Option (List Byte) :=
  Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .x5) (s.gpr .x1).toNat)

/-- `pre` holds the modulus' precomputed values. -/
def Cons (s : State) : Prop :=
  Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 3) (stackArg s 4).toNat)

/-- After the call. -/
structure AfterCall (D K : Nat) (s : State) (lo : Nat) (c : Byte) (t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  x19 : t.gpr .x19 = off (scr s) oSt
  x20 : t.gpr .x20 = scr s
  x21 : t.gpr .x21 = off (scr s) oDig
  x23 : t.gpr .x23 = s.gpr .x1
  x24 : t.gpr .x24 = off (scr s) (oEm + lo)
  x25 : t.gpr .x25 = BitVec.ofNat 64 ((s.gpr .x1).toNat - lo - D - 1)
  v : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  mem : Frame [kR K s, sR s] s.mem t.mem
  fr : Fr s t.mem
  lo : t.mem.readW (fb s + BitVec.ofNat 64 sLo) 64 = BitVec.ofNat 64 lo
  c : t.mem.readW (fb s + BitVec.ofNat 64 sC) 64 = BitVec.setWidth 64 c
  res : Cons s → Spec.Rsa.written t.mem (off (scr s) oEm) (s.gpr .x1).toNat ((t.gpr .x0).setWidth 32) (pubOut s)

theorem pdOk_of (c : PdChecked) {D K : Nat} {s t : State} (hp : PreV D K s) (hcK : c.stack ≤ K) {lo : Nat}
    {cb : Byte} (ha : AtCall D s lo cb t) : PdOk c.stack t := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hfb := fb_toNat hp
  have hkb := kb_toNat hp
  have hcl := c.le
  have hpos := c.pos
  have hws : (scr s).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64 := hp.ws
  have hsc := scr_toNat hp
  have hhs := hp.hs
  have hK : Region.Sub ⟨fb s - BitVec.ofNat 64 c.stack, c.stack⟩ (kR K s) := fun a h =>
    (Offset.sub_below (fb s) (a := c.stack) (b := K) (n := c.stack) (m := K) hcK (by omega) a h) |>
      fun h' => by
        have e : fb s - BitVec.ofNat 64 K = kb K s := by rw [fb_eq K, BitVec.add_sub_cancel]
        rw [e] at h'
        exact Region.sub_prefix (by unfold stk; omega) a h'
  have hsg : (⟨s.gpr .x5, (s.gpr .x1).toNat⟩ : Region) = sgR s := by rw [sgR, hp.sgl]
  have s16 := a16_sub K s
  have hSem := em_sub hp
  have hSsc := sc_sub hp
  have hwem : (off (scr s) oEm).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 := by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; unfold oEm at *; omega
  have hwsc : (off (scr s) oRsa).toNat + (stackArg s 2 - BitVec.ofNat 64 1024).toNat * 8 ≤ 2 ^ 64 := by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; rw [hsc]; unfold oRsa at *; omega
  refine ⟨?hl, ?hrd, ?hwr, ?hk, ?h3, ?h7, ?he1, ?he2, ?hs⟩
  case hl =>
    rw [ha.x0, ha.x1, ha.x2, ha.x3, ha.x4, ha.x5, ha.x6, ha.x7, ha.sp, ha.a0, ha.a1]
    have hsgS : (⟨s.gpr .x5, (s.gpr .x1).toNat⟩ : Region).Disjoint (sR s) := by rw [hsg]; exact hp.sgs
    have hsgK : (kR K s).Disjoint ⟨s.gpr .x5, (s.gpr .x1).toNat⟩ := by rw [hsg]; exact hp.ksg
    exact {
      sp1 := by unfold stk at *; omega
      sp2 := by omega
      on := hp.sP.sub_left hSem
      oe := (hp.es.sub_right hSem).symm
      oi := (hsgS.sub_right hSem).symm
      os := Offset.disjoint _ (Or.inl (by unfold oEm oRsa; omega)) (by unfold oEm; omega)
        (by rw [hsc]; unfold oRsa; omega)
      oa := ((hp.ks.sub_left s16).sub_right hSem).symm
      ns := (hp.sP.sub_left hSsc).symm
      es := hp.es.sub_right hSsc
      is := hsgS.sub_right hSsc
      sa := ((hp.ks.sub_left s16).symm.sub_left hSsc)
      ko := (hp.ks.sub_left hK).sub_right hSem
      kn := hp.kP.sub_left hK
      ke := hp.ke.sub_left hK
      ki := hsgK.sub_left hK
      ks := (hp.ks.sub_left hK).sub_right hSsc
      ka := (Offset.base_disjoint_below (fb s) (n := c.stack) (k := 16) (by omega)).symm
      wo := hwem
      wn := hp.wP
      we := hp.we
      wi := by have := hp.wsg; rw [hp.sgl] at this; exact this
      ws := hwsc }
  case hrd =>
    simp only [pdRd]
    rw [ha.x2, ha.x3, ha.x4, ha.x5, ha.x6, ha.x7, ha.sp, ha.rd, ha.wr, hsg]
    have hm : ∀ r ∈ [nR s, eR s, dgR D s, sgR s, pR s, aR s], Covers [r] (s.rd ++ (⟨fb s, frameBytes⟩ :: s.wr)) :=
      fun r hr => Covers.left (Covers.trans (Covers.of_mem fun x hx => by rw [List.mem_singleton.mp hx]; exact hr)
        hp.hrd)
    refine Covers.cons (hm (pR s) (by simp)) (Covers.cons (hm _ (by simp)) (Covers.cons (hm _ (by simp))
      (Covers.right (Covers.one ?_))))
    simpa using in_frame s s.wr (d := 0) (n := 16) (by decide)
  case hwr =>
    simp only [pubWr]
    rw [ha.x0, ha.x1, ha.a0, ha.a1, ha.wr]
    exact Covers.cons (Covers.one ⟨sR s, List.mem_cons_of_mem _ hp.hws,
        Offset.contains_base _ (by unfold oEm; omega) (by unfold oEm; omega)⟩)
      (Covers.one ⟨sR s, List.mem_cons_of_mem _ hp.hws,
        Offset.contains_base _ (by rw [hsc]; unfold oRsa; omega) (by unfold oRsa; omega)⟩)
  case hk => rw [ha.x1]; exact ⟨hk1, hk2⟩
  case h3 => rw [ha.x3, ha.x1]; exact hp.hl
  case h7 => rw [ha.x7, ha.x1]
  case he1 => rw [ha.x5]; exact hp.e1
  case he2 => rw [ha.x5, ha.x1]; exact hp.e2
  case hs => rw [ha.a1, ha.x1, hsc]; unfold Spec.Rsa.scratchWords; omega

theorem call_ok (c : PdChecked) {D K : Nat} {s t : State} (hp : PreV D K s) (hcK : c.stack ≤ K)
    {lo : Nat} {cb : Byte} (ha : AtCall D s lo cb t) :
    WP isa (.call c.name c.code) t (AfterCall D K s lo cb) := by
  have hfb := fb_toNat hp
  have hkb := kb_toNat hp
  have hcl := c.le
  have hd := c.depth
  refine pdCall c (pdOk_of c hp hcK ha) fun s' hrd' hwr' hsp' hf hpres hvs hpost => ?_
  simp only [pubWr] at hf
  rw [ha.x0, ha.x1, ha.a0, ha.a1, ha.sp] at hf
  have hbs : Region.Sub (below (fb s) (16 * c.code.aarch64Depth)) (kR K s) := fun a h =>
    below_sub K s a (Offset.sub_below (fb s) (a := 16 * c.code.aarch64Depth) (b := K)
      (n := 16 * c.code.aarch64Depth) (m := K) (by omega) (by omega) a h)
  have hf' : Frame [kR K s, sR s] t.mem s'.mem := hf.sub fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), em_sub hp⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), sc_sub hp⟩
    · exact ⟨_, List.mem_cons_self .., hbs⟩
  have hfr0 : Frame [kR K s, sR s] s.mem t.mem := ha.mem.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., frame_sub0 K s⟩
  have hbt : ∀ {p : Addr} {len : Nat}, (kR K s).Disjoint ⟨p, len⟩ → (sR s).Disjoint ⟨p, len⟩ →
      len ≤ 2 ^ 64 → ∀ i < len, t.mem (p + BitVec.ofNat 64 i) = s.mem (p + BitVec.ofNat 64 i) :=
    fun hk hs hl i hi => hfr0.bytes (R := ⟨_, _⟩) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hk.symm
      · exact hs.symm) hl hi
  have hbytes : ∀ {p : Addr} {len : Nat}, (kR K s).Disjoint ⟨p, len⟩ → (sR s).Disjoint ⟨p, len⟩ →
      len ≤ 2 ^ 64 → Spec.Rsa.bytesAt t.mem p len = Spec.Rsa.bytesAt s.mem p len := fun hk hs hl => by
    simp only [Spec.Rsa.bytesAt]
    exact List.map_congr_left fun i hi => hbt hk hs hl i (List.mem_range.mp hi)
  have hsg : (⟨s.gpr .x5, (s.gpr .x1).toNat⟩ : Region) = sgR s := by rw [sgR, hp.sgl]
  have hwords : Spec.Rsa.wordsAt t.mem (stackArg s 3) (stackArg s 4).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 3) (stackArg s 4).toNat := by
    simp only [Spec.Rsa.wordsAt]
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    exact hfr0.readW (r := pR s) (Offset.contains_base _ (by omega) (by have := hp.wP; omega)) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.kP.symm
      · exact hp.sP.symm) (by decide)
  have hA : ∀ {d n : Nat}, d + n ≤ frameBytes → ∀ r ∈ [emR s, scR s] ++ [below (fb s) (16 * c.code.aarch64Depth)],
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, n⟩ r := fun hdn r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hp.ks.sub_left (frame_sub K s hdn)).sub_right (em_sub hp)
    · exact (hp.ks.sub_left (frame_sub K s hdn)).sub_right (sc_sub hp)
    · exact Offset.disjoint_below _ (by unfold frameBytes at hdn; omega)
  have hsl : ∀ {d : Nat}, d + 8 ≤ frameBytes → s'.mem.readW (fb s + BitVec.ofNat 64 d) 64 =
      t.mem.readW (fb s + BitVec.ofNat 64 d) 64 := fun hd =>
    hf.readW (r := ⟨fb s + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _) (hA hd) (by decide)
  exact {
    sp := hsp'.trans ha.sp
    rd := hrd'.trans ha.rd
    wr := hwr'.trans ha.wr
    x19 := (hpres .x19 (by decide) (by decide)).trans ha.x19
    x20 := (hpres .x20 (by decide) (by decide)).trans ha.x20
    x21 := (hpres .x21 (by decide) (by decide)).trans ha.x21
    x23 := (hpres .x23 (by decide) (by decide)).trans ha.x23
    x24 := (hpres .x24 (by decide) (by decide)).trans ha.x24
    x25 := (hpres .x25 (by decide) (by decide)).trans ha.x25
    v := fun r hr => (hvs r hr).trans (ha.v r hr)
    mem := hfr0.trans hf'
    fr := ha.fr.frame hf (hA (by decide)) (hA (by decide)) (hA (by decide))
    lo := by rw [hsl (by decide), ha.lo]
    c := by rw [hsl (by decide), ha.c]
    res := fun hc => by
      have := hpost (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
        (by rw [VG.Proof.RsaPkcs1Sig.bytesAt_length, ha.x1]) (by rw [ha.x2, ha.x3, hwords]; exact hc)
      rw [ha.x0, ha.x1, ha.x4, ha.x5, ha.x6, hbytes hp.ke hp.es.symm (by have := hp.we; omega),
        hbytes (len := (s.gpr .x1).toNat) (by rw [hsg]; exact hp.ksg) (by rw [hsg]; exact hp.sgs.symm)
          (by have := hp.wsg; rw [hp.sgl] at this; omega)] at this
      exact this }

end VG.Proof.RsaPss.AArch64.Vfy
