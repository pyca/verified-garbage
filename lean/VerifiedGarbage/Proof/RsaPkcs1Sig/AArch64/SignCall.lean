import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.SignFrame
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Encode

/-!
# `vg_rsa_pkcs1_sign` on AArch64: the call of `vg_rsa_private_checked`

`callArgs_ok`: after the encoding into `EM`, the function's stack arguments
`p` … `scratch_len` are copied to the call's (`copies_ok`), and the
registers set up (`AtCall`); `call_ok`: the call writes the signature of
`EM` to `out` and keeps `k` in `x19` and the saved slots (`AfterCall`).
-/

namespace VG.Proof.RsaPkcs1Sig.AArch64.Sgn

open VG VG.AArch64 VG.Impl.RsaPkcs1Sig.AArch64.Sign VG.WriteBytes
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_strx wp_nil)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_addSp wp_ldrSp wp_mov wp_movw clob)
open VG.Proof.RsaPkcs1Sig (bytesAt_length bytesAt_writeBytes frame_writeBytes bytes_apart)

/-! ## The stack arguments -/

/-- After copying `n` stack arguments from `v₀`. -/
structure Copied (s v₀ : State) (n : Nat) (v : State) : Prop where
  sp : v.sp = v₀.sp
  rd : v.rd = v₀.rd
  wr : v.wr = v₀.wr
  g : ∀ r, r ≠ .x15 → v.gpr r = v₀.gpr r
  vc : ∀ r ∈ preservedV, (v.v r).extractLsb' 0 64 = (v₀.v r).extractLsb' 0 64
  mem : Frame [⟨fb s, 96⟩] v₀.mem v.mem
  args : ∀ i < n, v.mem.readW (fb s + BitVec.ofNat 64 (8 * i)) 64 = stackArg s (i + 1)

theorem copies_ok {K : Nat} {s v₀ : State} (hp : PreS K s) (hsp : v₀.sp = fb s) (h16 : v₀.gpr .x16 = fb s)
    (hrd : v₀.rd = s.rd) (hwr : v₀.wr = ⟨fb s, frameBytes⟩ :: s.wr) (hm : Frame [⟨fb s, frameBytes⟩] s.mem v₀.mem) :
    ∀ n ≤ 12, WP isa (.block ((List.range n).flatMap copyArg)) v₀ (Copied s v₀ n) := by
  intro n hn
  induction n with
  | zero => exact wp_nil ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, Frame.refl _ _, fun i hi => absurd hi (by omega)⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun v hv => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, copyArg, List.append_nil]
    have a₁ : v.sp + BitVec.ofNat 64 (frameBytes + 8 * (n + 1)) = stackArgAddr s (n + 1) := by
      rw [hv.sp, hsp, stackArgAddr_fb]
    have hmv : Frame [⟨fb s, frameBytes⟩] s.mem v.mem := hm.trans (hv.mem.sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨⟨fb s, frameBytes⟩, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩)
    refine wp_ldrSp (by unfold frameBytes; omega) (by
      rw [a₁, hv.rd, hrd]; exact arg_in hp (Covers.left (Covers.refl _)) (by omega)) fun v₁ o₁ e₁ => ?_
    rw [a₁, arg_frame hp hmv (by omega)] at e₁
    have x16 : v₁.gpr .x16 = fb s := by rw [o₁.get .x16, hv.g .x16 (by decide), h16]
    refine wp_strx (a := fb s + BitVec.ofNat 64 (8 * n)) (by omega) (by rw [x16])
      (by rw [o₁.wr, hv.wr, hwr]; exact in_frame _ _ (by unfold frameBytes; omega)) fun v₂ m₂ => wp_nil ?_
    have mem₂ : v₂.mem = v.mem.writeW (fb s + BitVec.ofNat 64 (8 * n)) (stackArg s (n + 1)) := by
      rw [m₂.mem, o₁.mem, e₁]
    refine ⟨by rw [m₂.sp, o₁.sp, hv.sp], by rw [m₂.rd, o₁.rd, hv.rd], by rw [m₂.wr, o₁.wr, hv.wr],
      fun r hr => by rw [m₂.gpr, o₁.gpr r (by simpa using hr), hv.g r hr],
      fun r hr => by rw [m₂.vcs r hr, o₁.vcs r hr, hv.vc r hr], ?_, fun i hi => ?_⟩
    · rw [mem₂]
      exact hv.mem.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    · rw [mem₂]
      rcases (by omega : i < n ∨ i = n) with h | rfl
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide), hv.args i h]
      · exact Mem.readW_writeW_self64 _ _ _


/-! ## The call's arguments -/

/-- `EM`, of `k` bytes. -/
abbrev emR (s : State) : Region := ⟨fb s + BitVec.ofNat 64 oEM, (s.gpr .x3).toNat⟩

theorem em_sub {K : Nat} {s : State} (hp : PreS K s) : Region.Sub (emR s) (kR K s) :=
  frame_sub K s (by have := hp.k2; unfold oEM frameBytes; omega)

theorem a96_sub (K : Nat) (s : State) : Region.Sub ⟨fb s, 96⟩ (kR K s) :=
  fun a h => frame_sub0 K s a (Region.sub_prefix (by decide) a h)

/-- The slots of the saved registers are apart from `EM`. -/
theorem slots_em {K : Nat} {s : State} (hp : PreS K s) {n : Nat} (hn : n ≤ (s.gpr .x3).toNat) :
    Region.Disjoint ⟨fb s + BitVec.ofNat 64 96, 16⟩ ⟨fb s + BitVec.ofNat 64 oEM, n⟩ :=
  Offset.disjoint _ (by unfold oEM; omega) (by decide) (by have := hp.k2; unfold oEM; omega)

/-- At the call: `k` in `x19`, the arguments of `vg_rsa_private_checked`
set up, and `EM` holding `em`. -/
structure AtCall (s : State) (em : List Byte) (t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  x0 : t.gpr .x0 = s.gpr .x0
  x1 : t.gpr .x1 = s.gpr .x1
  x2 : t.gpr .x2 = s.gpr .x2
  x3 : t.gpr .x3 = s.gpr .x3
  x4 : t.gpr .x4 = s.gpr .x4
  x5 : t.gpr .x5 = s.gpr .x5
  x6 : t.gpr .x6 = fb s + BitVec.ofNat 64 oEM
  x7 : t.gpr .x7 = s.gpr .x3
  x19 : t.gpr .x19 = s.gpr .x3
  hi : ∀ r ∈ [Reg.x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28], t.gpr r = s.gpr r
  v : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  args : ∀ i < 12, stackArg t i = stackArg s (i + 1)
  mem : Frame [⟨fb s, frameBytes⟩] s.mem t.mem
  sv : Spill.Saved (fb s) s.gpr saved t.mem
  em : Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oEM) (s.gpr .x3).toNat = em

theorem callArgs_ok {K : Nat} {s u w : State} (hp : PreS K s) (hu : AtEnc s u) (hK : Keep clob u w)
    {em : List Byte} (hme : w.mem = writeBytes u.mem (u.gpr .x8) em) (hl : em.length = (s.gpr .x3).toNat) :
    WP isa (.block callArgs) w (AtCall s em) := by
  have hk2 := hp.k2
  have g : ∀ r, r ∉ clob → r ∉ [Reg.x8, .x9, .x10, .x11, .x12, .x16, .x17, .x19] → w.gpr r = s.gpr r :=
    fun r h₁ h₂ => by rw [hK.gpr r h₁, hu.g r h₂]
  have fw : Frame [⟨fb s + BitVec.ofNat 64 oEM, em.length⟩] u.mem w.mem := by
    rw [hme, hu.x8]; exact frame_writeBytes _ _ _
  have hmw : Frame [⟨fb s, frameBytes⟩] s.mem w.mem := hu.mem.trans (fw.sub fun r hr => by
    rw [List.mem_singleton.mp hr, hl]
    exact ⟨⟨fb s, frameBytes⟩, List.mem_singleton_self _, Offset.sub_base _ (by unfold oEM frameBytes; omega)⟩)
  have svw : Spill.Saved (fb s) s.gpr saved w.mem := hu.sv.frame_in saved_offs fw fun r hr => by
    rw [List.mem_singleton.mp hr, hl]; exact slots_em hp (Nat.le_refl _)
  have emw : Spec.Rsa.bytesAt w.mem (fb s + BitVec.ofNat 64 oEM) (s.gpr .x3).toNat = em := by
    rw [hme, hu.x8, ← hl, bytesAt_writeBytes _ _ _ (by omega)]
  unfold callArgs
  rw [WP.block_append_iff]
  refine WP.mono (copies_ok hp (v₀ := w) (by rw [hK.sp, hu.sp]) (by rw [hK.get .x16, hu.x16])
    (by rw [hK.rd, hu.rd]) (by rw [hK.wr, hu.wr]) hmw 12 (Nat.le_refl _)) fun v hv => ?_
  refine wp_mov fun v₁ o₁ e₁ => wp_mov fun v₂ o₂ e₂ => wp_mov fun v₃ o₃ e₃ => wp_nil ?_
  have O₃ : Only [.x0, .x6, .x7] v v₃ := (o₁.trans (o₂.trans o₃)).mono
  have hv15 : ∀ r, r ∉ clob → r ∉ [Reg.x8, .x9, .x10, .x11, .x12, .x16, .x17, .x19] → r ≠ .x15 →
      r ∉ [Reg.x0, .x6, .x7] → v₃.gpr r = s.gpr r := fun r h₁ h₂ h₃ h₄ => by
    rw [O₃.gpr r h₄, hv.g r h₃, g r h₁ h₂]
  have d96 : ∀ {R : Region}, R.Disjoint ⟨fb s, 96⟩ → R.len ≤ 2 ^ 64 →
      Spec.Rsa.bytesAt v₃.mem R.base R.len = Spec.Rsa.bytesAt w.mem R.base R.len := fun hd hl' => by
    rw [O₃.mem]; exact bytes_apart hv.mem hd hl'
  refine ⟨?sp, ?rd, ?wr, ?x0, ?x1, ?x2, ?x3, ?x4, ?x5, ?x6, ?x7, ?x19, ?hi, ?v, ?args, ?mem, ?sv, ?em⟩
  case sp => rw [O₃.sp, hv.sp, hK.sp, hu.sp]
  case rd => rw [O₃.rd, hv.rd, hK.rd, hu.rd]
  case wr => rw [O₃.wr, hv.wr, hK.wr, hu.wr]
  case x0 => rw [o₃.get .x0, o₂.get .x0, e₁, hv.g .x17 (by decide), hK.get .x17, hu.x17]
  case x1 => exact hv15 .x1 (by decide) (by decide) (by decide) (by decide)
  case x2 => exact hv15 .x2 (by decide) (by decide) (by decide) (by decide)
  case x3 => exact hv15 .x3 (by decide) (by decide) (by decide) (by decide)
  case x4 => exact hv15 .x4 (by decide) (by decide) (by decide) (by decide)
  case x5 => exact hv15 .x5 (by decide) (by decide) (by decide) (by decide)
  case x6 => rw [o₃.get .x6, e₂, o₁.get .x8, hv.g .x8 (by decide), hK.get .x8, hu.x8]
  case x7 => rw [e₃, o₂.get .x19, o₁.get .x19, hv.g .x19 (by decide), hK.get .x19, hu.x19]
  case x19 => rw [O₃.get .x19, hv.g .x19 (by decide), hK.get .x19, hu.x19]
  case hi =>
    intro r hr
    exact hv15 r (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
  case v =>
    intro r hr
    rw [O₃.vcs r hr, hv.vc r hr, hK.vcs r hr, hu.v r hr]
  case args =>
    intro i hi
    show v₃.mem.readW (v₃.sp + BitVec.ofNat 64 (8 * i)) 64 = _
    rw [O₃.mem, O₃.sp, hv.sp, hK.sp, hu.sp, hv.args i hi]
  case mem =>
    rw [O₃.mem]
    exact hmw.trans (hv.mem.sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨⟨fb s, frameBytes⟩, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩)
  case sv =>
    rw [O₃.mem]
    exact svw.frame_in saved_offs hv.mem fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by decide) (by decide)
  case em =>
    rw [← emw]
    exact d96 (R := ⟨fb s + BitVec.ofNat 64 oEM, (s.gpr .x3).toNat⟩)
      (Offset.disjoint_base _ (by unfold oEM; omega) (by unfold oEM; omega)) (by dsimp only; omega)


/-! ## The call -/

theorem privOk_of (c : PrivChecked) {s t : State} (hp : PreS c.stack s) {em : List Byte} (ha : AtCall s em t) :
    PrivOk c.stack t := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hfb := fb_toNat hp
  have hkb := kb_toNat hp
  have hcl := c.le
  have hpos := c.pos
  have hfK : fb s - BitVec.ofNat 64 c.stack = kb c.stack s := by rw [fb_eq c.stack, BitVec.add_sub_cancel]
  have hkK : Region.Sub ⟨kb c.stack s, c.stack⟩ (kR c.stack s) := Region.sub_prefix (by unfold stk; omega)
  have a1 := ha.args 0 (by decide); have a2 := ha.args 1 (by decide); have a3 := ha.args 2 (by decide)
  have a4 := ha.args 3 (by decide); have a5 := ha.args 4 (by decide); have a6 := ha.args 5 (by decide)
  have a7 := ha.args 6 (by decide); have a8 := ha.args 7 (by decide); have a9 := ha.args 8 (by decide)
  have a10 := ha.args 9 (by decide); have a11 := ha.args 10 (by decide); have a12 := ha.args 11 (by decide)
  have hem : (⟨fb s + BitVec.ofNat 64 oEM, (s.gpr .x3).toNat⟩ : Region) =
      ⟨kb c.stack s + BitVec.ofNat 64 (c.stack + oEM), (s.gpr .x3).toNat⟩ := by rw [off_fb c.stack]
  have ha96 : (⟨fb s, 96⟩ : Region) = ⟨kb c.stack s + BitVec.ofNat 64 c.stack, 96⟩ := by rw [fb_eq c.stack]
  have hfbE : (fb s + BitVec.ofNat 64 oEM).toNat = (fb s).toNat + oEM := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; unfold oEM frameBytes at *; omega
  refine ⟨?hl, ?hrd, ?hwr, ?hk, ?h1, ?h7, ?he1, ?he2, ?hp1, ?hp2, ?hq1, ?hq2, ?hdp, ?hqi, ?hdq, ?hs⟩
  case hl =>
    simp only [Nat.zero_add, Nat.reduceAdd] at a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
    rw [ha.x0, ha.x1, ha.x2, ha.x3, ha.x4, ha.x5, ha.x6, ha.x7, ha.sp, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
      a11, a12]
    exact {
      sp1 := by unfold stk at *; omega
      sp2 := by omega
      on := hp.on
      oe := hp.oe
      oi := (hp.ko.sub_left (em_sub hp)).symm
      op := hp.op
      oq := hp.oq
      odp := hp.odp
      odq := hp.odq
      oqi := hp.oqi
      os := hp.os
      oa := (hp.ko.sub_left (a96_sub c.stack s)).symm
      ns := hp.ns
      es := hp.es
      is := hp.ks.sub_left (em_sub hp)
      ps := hp.ps
      qs := hp.qs
      dps := hp.dps
      dqs := hp.dqs
      qis := hp.qis
      sa := (hp.ks.sub_left (a96_sub c.stack s)).symm
      ko := by rw [hfK]; exact hp.ko.sub_left hkK
      kn := by rw [hfK]; exact hp.kn.sub_left hkK
      ke := by rw [hfK]; exact hp.ke.sub_left hkK
      ki := by
        rw [hfK, hem]
        exact Offset.base_disjoint _ (by unfold oEM; omega) (by unfold oEM stk frameBytes at *; omega)
      kp := by rw [hfK]; exact hp.kp.sub_left hkK
      kq := by rw [hfK]; exact hp.kq.sub_left hkK
      kdp := by rw [hfK]; exact hp.kdp.sub_left hkK
      kdq := by rw [hfK]; exact hp.kdq.sub_left hkK
      kqi := by rw [hfK]; exact hp.kqi.sub_left hkK
      ks := by rw [hfK]; exact hp.ks.sub_left hkK
      ka := by rw [hfK, ha96]; exact Offset.base_disjoint _ (by omega) (by unfold stk at *; omega)
      wo := hp.wo
      wn := hp.wn
      we := hp.we
      wi := by dsimp only; rw [hfbE]; unfold oEM frameBytes at *; omega
      wp := hp.wp
      wq := hp.wq
      wdp := hp.wdp
      wdq := hp.wdq
      wqi := hp.wqi
      ws := hp.ws }
  case hrd =>
    simp only [privRd]
    simp only [Nat.zero_add, Nat.reduceAdd] at a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
    rw [ha.x2, ha.x3, ha.x4, ha.x5, ha.x6, ha.x7, ha.sp, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, ha.rd, ha.wr]
    have hm : ∀ r ∈ [nR s, eR s, dR s, pR s, qR s, dpR s, dqR s, qiR s, aR s],
        Covers [r] (s.rd ++ (⟨fb s, frameBytes⟩ :: s.wr)) :=
      fun r hr => Covers.left (Covers.trans (Covers.of_mem fun x hx => by rw [List.mem_singleton.mp hx]; exact hr)
        hp.hrd)
    refine Covers.cons (hm _ (by simp)) (Covers.cons (hm _ (by simp)) (Covers.cons
      (Covers.right (Covers.one (in_frame _ _ (by unfold oEM frameBytes; omega))))
      (Covers.cons (hm _ (by simp)) (Covers.cons (hm _ (by simp)) (Covers.cons (hm _ (by simp))
      (Covers.cons (hm _ (by simp)) (Covers.cons (hm _ (by simp))
      (Covers.right (Covers.one ?_)))))))))
    simpa using in_frame s s.wr (d := 0) (n := 96) (by decide)
  case hwr =>
    simp only [privWr]
    have a11' := a11; have a12' := a12
    simp only [Nat.reduceAdd] at a11' a12'
    rw [ha.x0, ha.x1, a11', a12', ha.wr]
    exact Covers.cons (Covers.of_mem fun x hx => by rw [List.mem_singleton.mp hx]; exact List.mem_cons_of_mem _ hp.hwo)
      (Covers.of_mem fun x hx => by rw [List.mem_singleton.mp hx]; exact List.mem_cons_of_mem _ hp.hws)
  case hk => rw [ha.x3]; exact ⟨hk1, hk2⟩
  case h1 => rw [ha.x1, ha.x3, hp.ol]
  case h7 => rw [ha.x7, ha.x3]
  case he1 => rw [ha.x5]; exact hp.e1
  case he2 => rw [ha.x5, ha.x3]; exact hp.e2
  case hp1 => rw [a2]; exact hp.p1
  case hp2 => rw [a2, ha.x3]; exact hp.p2
  case hq1 => rw [a4]; exact hp.q1
  case hq2 => rw [a4, ha.x3]; exact hp.q2
  case hdp => rw [a6, a2]; exact hp.hdp
  case hqi => rw [a10, a2]; exact hp.hqi
  case hdq => rw [a8, a4]; exact hp.hdq
  case hs => rw [a12, ha.x3]; unfold Spec.Rsa.scratchWords; exact hp.hs


/-- The private operation on `em`, with the key as the entry state gives it. -/
def privOut (s : State) (em : List Byte) : Spec.Rsa.Outcome :=
  Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) em
    (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 2).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 2).toNat)

/-- In the frame after the call: the registers saved, `k` in `x19`. -/
structure Mid (s t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  x19 : t.gpr .x19 = s.gpr .x3
  hi : ∀ r ∈ [Reg.x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28], t.gpr r = s.gpr r
  v : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  sv : Spill.Saved (fb s) s.gpr saved t.mem

/-- After the call: `Mid`, and `out` written with the result. -/
structure AfterCall (s : State) (em : List Byte) (t : State) : Prop extends Mid s t where
  res : Spec.Rsa.writtenOutcome t.mem (s.gpr .x0) (s.gpr .x3).toNat ((t.gpr .x0).setWidth 32) (privOut s em)

/-- A buffer of the caller, in memory changed only in the frame. -/
theorem bytes_frame {K : Nat} {s : State} {m : Mem} (hf : Frame [⟨fb s, frameBytes⟩] s.mem m) {p : Addr}
    {len : Nat} (hk : (kR K s).Disjoint ⟨p, len⟩) (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m p len = Spec.Rsa.bytesAt s.mem p len :=
  bytes_apart (R := ⟨p, len⟩) hf (hk.sub_left (frame_sub0 K s)).symm hl

theorem call_ok (c : PrivChecked) {s t : State} (hp : PreS c.stack s) {em : List Byte} (ha : AtCall s em t) :
    WP isa (.call c.name c.code) t (AfterCall s em) := by
  have hfb := fb_toNat hp
  have hkb := kb_toNat hp
  have hcl := c.le
  have hd := c.depth
  have a1 := ha.args 0 (by decide); have a2 := ha.args 1 (by decide); have a3 := ha.args 2 (by decide)
  have a4 := ha.args 3 (by decide); have a5 := ha.args 4 (by decide); have a6 := ha.args 5 (by decide)
  have a7 := ha.args 6 (by decide); have a8 := ha.args 7 (by decide); have a9 := ha.args 8 (by decide)
  have a10 := ha.args 9 (by decide); have a11 := ha.args 10 (by decide); have a12 := ha.args 11 (by decide)
  simp only [Nat.zero_add, Nat.reduceAdd] at a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
  refine privCall c (privOk_of c hp ha) fun s' hrd' hwr' hsp' hf hpres hvs hpost => ?_
  simp only [privWr] at hf
  rw [ha.x0, ha.x1, a11, a12, ha.sp] at hf
  have hl : ∀ {p : Addr} {len : Nat}, p.toNat + len ≤ 2 ^ 64 → len ≤ 2 ^ 64 := fun h => by omega
  rw [ha.x0, ha.x2, ha.x3, ha.x4, ha.x5, ha.x6, a1, a2, a3, a4, a5, a7, a9, ha.em,
    bytes_frame ha.mem hp.kn (hl hp.wn), bytes_frame ha.mem hp.ke (hl hp.we),
    bytes_frame ha.mem hp.kp (hl hp.wp), bytes_frame ha.mem hp.kq (hl hp.wq),
    bytes_frame ha.mem (len := (stackArg s 2).toNat) (by rw [← hp.hdp]; exact hp.kdp)
      (by have := hp.wdp; rw [hp.hdp] at this; omega),
    bytes_frame ha.mem (len := (stackArg s 4).toNat) (by rw [← hp.hdq]; exact hp.kdq)
      (by have := hp.wdq; rw [hp.hdq] at this; omega),
    bytes_frame ha.mem (len := (stackArg s 2).toNat) (by rw [← hp.hqi]; exact hp.kqi)
      (by have := hp.wqi; rw [hp.hqi] at this; omega)] at hpost
  exact {
    sp := hsp'.trans ha.sp
    rd := hrd'.trans ha.rd
    wr := hwr'.trans ha.wr
    x19 := (hpres .x19 (by decide) (by decide)).trans ha.x19
    hi := fun r hr => (hpres r (by revert r; decide) (by revert r; decide)).trans (ha.hi r hr)
    v := fun r hr => (hvs r hr).trans (ha.v r hr)
    sv := ha.sv.frame_in saved_offs hf fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.ko.sub_left (frame_sub c.stack s (d := 96) (n := 16) (by decide))
      · exact hp.ks.sub_left (frame_sub c.stack s (d := 96) (n := 16) (by decide))
      · exact Offset.disjoint_below (fb s) (by omega)
    res := hpost }

end VG.Proof.RsaPkcs1Sig.AArch64.Sgn
