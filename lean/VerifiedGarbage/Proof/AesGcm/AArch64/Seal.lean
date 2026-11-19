module

import VerifiedGarbage.Proof.AesGcm.AArch64.Cmp
import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.AesGcm.AArch64.Front
public import VerifiedGarbage.Proof.AesGcm.AArch64.Body
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contract
public import VerifiedGarbage.Proof.AesGcm.AArch64.FinTag
public import VerifiedGarbage.Proof.AesGcm.AArch64.OneEntry
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamInit

/-! ### `AesGcm.AArch64.OneShot`, which this module and modules that import it used -/

section

/-!
# AES-GCM on AArch64: what `seal` and `open` share

Untrusted: everything here is checked by Lean. The layout of a one-shot call
(`oneLay`): the state at `W + 16`, inside `work`; everything the pieces
write is inside `work`, but for the data (`*_work`) and the tag.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- `work`. -/
abbrev workR (Wn : Nat) (W : Addr) : Region := ⟨W, Wn⟩

theorem stW {Wn : Nat} {W : Addr} {d k : Nat} (h : d + k ≤ 80) :
    Region.Sub ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 d, k⟩ (workR Wn W) := by
  rw [add_ofNat_assoc]; exact Lay.wSub (by omega_using [h])

theorem keep_of_sub {Wn : Nat} {rs : List Region} {W : Addr} (hs : ∀ r ∈ rs, Region.Sub r (workR Wn W)) {X : Region}
    (hX : X.Disjoint (workR Wn W)) : ∀ r ∈ rs, X.Disjoint r := fun r hr => hX.sub_right (hs r hr)

theorem entryR_work {Wn : Nat} (W : Addr) : ∀ r ∈ [entryR W], Region.Sub r (workR Wn W) := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact Lay.wSub (by decide)

theorem frontFrame_work {Wn : Nat} (W : Addr) : ∀ r ∈ frontFrame (W + BitVec.ofNat 64 16) W, Region.Sub r (workR Wn W) := by
  intro r hr
  simp only [frontFrame, j0Frame, absFrame, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Lay.wSub (by decide)
  · exact Lay.wSub (by decide)
  · exact Lay.wSub (by decide)
  · exact stW (by decide)
  · exact stW (by decide)
  · exact Lay.wSub (by decide)

theorem finFrame_work {Wn : Nat} (W : Addr) {o : Nat} (ho : o = 0 ∨ o = 112) :
    ∀ r ∈ finFrame (W + BitVec.ofNat 64 16) W o, Region.Sub r (workR Wn W) := by
  intro r hr
  simp only [finFrame, tFrame, tagFrame, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact stW (by decide)
  · exact Lay.wSub (by decide)
  · exact Lay.wSub (by decide)
  · exact Lay.wSub (by decide)
  · exact Lay.wSub (by decide)
  · exact Lay.wSub (by omega_using [ho])
  · exact Lay.wSub (by decide)

/-- The regions a body writes: in `work`, or the data. -/
theorem bodyFrame_work {Wn : Nat} (W D : Addr) (n : Nat) :
    ∀ r ∈ bodyFrame (W + BitVec.ofNat 64 16) W D n, Region.Sub r (workR Wn W) ∨ r = ⟨D, n⟩ := by
  intro r hr
  simp only [bodyFrame, tFrame, crFrame, absFrame, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl (stW (by decide))
  · exact .inl (Lay.wSub (by decide))
  · exact .inl (Lay.wSub (by decide))
  · exact .inr rfl
  · exact .inl (stW (by decide))
  · exact .inl (Lay.wSub (by decide))
  · exact .inl (stW (by decide))
  · exact .inl (stW (by decide))
  · exact .inl (Lay.wSub (by decide))

theorem keep_body {Wn : Nat} {W D : Addr} {n : Nat} {X : Region} (hX : X.Disjoint (workR Wn W)) (hD : X.Disjoint ⟨D, n⟩) :
    ∀ r ∈ bodyFrame (W + BitVec.ofNat 64 16) W D n, X.Disjoint r := fun r hr => by
  rcases bodyFrame_work W D n r hr with h | rfl
  · exact hX.sub_right h
  · exact hD

/-- What `oneCore` gives, with `work` the `w`-th of the `n` arguments on the stack. -/
structure OneLay (Wn : Nat) (s : State) (n w : Nat) : Prop where
  lay : Lay Wn (s.gpr .x0) (stackArg s w + BitVec.ofNat 64 16) (stackArg s w)
  perm : Perm Wn (s.gpr .x0) (stackArg s w + BitVec.ofNat 64 16) (stackArg s w) s
  hsp : ∀ i < n, InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * i)) 8
  nonce : (⟨s.gpr .x2, (s.gpr .x3).toNat⟩ : Region).Disjoint (workR Wn (stackArg s w))
  aad : (⟨s.gpr .x4, (s.gpr .x5).toNat⟩ : Region).Disjoint (workR Wn (stackArg s w))
  data : (⟨s.gpr .x6, (s.gpr .x7).toNat⟩ : Region).Disjoint (workR Wn (stackArg s w))
  ctx : (⟨s.gpr .x0, 256⟩ : Region).Disjoint (workR Wn (stackArg s w))
  args : (args s n).Disjoint (workR Wn (stackArg s w))
  nd : (⟨s.gpr .x2, (s.gpr .x3).toNat⟩ : Region).Disjoint ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
  ad : (⟨s.gpr .x4, (s.gpr .x5).toNat⟩ : Region).Disjoint ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
  cd : (⟨s.gpr .x0, 256⟩ : Region).Disjoint ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
  nw : (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64
  aw : (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64
  dw : (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64
  rounds : rounds (s.gpr .x1)
  nonceR : Covers [⟨s.gpr .x2, (s.gpr .x3).toNat⟩] (s.rd ++ s.wr)
  aadR : Covers [⟨s.gpr .x4, (s.gpr .x5).toNat⟩] (s.rd ++ s.wr)
  dataW : Covers [⟨s.gpr .x6, (s.gpr .x7).toNat⟩] s.wr

theorem oneLay {Wn : Nat} {s : State} {n w : Nat} (hs : oneCore n w s) : OneLay Wn s n w := by
  simp only [oneCore] at hs
  sig_split hs
  rename_i mc mn ma mg md mw dcd dcw dnd dnw dad daw ddw dda dwa wc wn wa wd ww wsp
  have hR := hs
  clear hs
  have sub16 : Region.Sub ⟨stackArg s w + BitVec.ofNat 64 16, 80⟩ (workR Wn (stackArg s w)) := Lay.wSub (by decide)
  refine ⟨⟨wc, ?_, ww, dcw.sub_right sub16, dcw, ?_, ?_⟩, ⟨covers_mem (List.mem_append_left _ mc),
    covers_off (k := Wn) (covers_of_mem mw) (show 16 + 80 ≤ 512 by decide) (by decide),
    covers_of_mem mw⟩,
    fun i hi => ?_, dnw, daw, ddw, dcw, dwa.symm, dnd, dad, dcd, wn, wa, wd, hR,
    covers_mem (List.mem_append_left _ mn), covers_mem (List.mem_append_left _ ma), covers_of_mem md⟩
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16) (by decide), Nat.mod_eq_of_lt (by omega_using [ww])]
    omega_using [ww]
  · simpa using Offset.disjoint (stackArg s w) (d := 16) (n := 80) (e := 0) (k := 16) (.inr (by decide))
      (by decide) (by decide)
  · have := Offset.disjoint (stackArg s w) (d := 16) (n := 80) (e := 96) (k := Wn - 96) (.inl (by decide))
      (by decide) (by decide)
    exact this
  · refine ⟨args s n, List.mem_append_left _ mg, ?_⟩
    have e : stackArgAddr s 0 = s.sp := by simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
    simp only [args, e]
    exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [wsp, hi])

end VG.Proof.AesGcm.AArch64

end

end

/-!
# AES-GCM on AArch64: `vg_aes_gcm_seal`

Untrusted: everything here is checked by Lean. The entry and `front_ok`
start the state at `W + 16` and absorb the additional data, and keep `tag`
at `W + 248` (`entryStash_ok`); `encBody` encrypts the data and absorbs the
ciphertext, `finBody 0` writes the tag to `W`, and `tagOut` copies it to `tag`
(`seal_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput inc32 ctxH ctxCiph gctr)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

theorem slots_bodyFrame {Wn : Nat} {Ctx W D : Addr} {n : Nat} (L : Lay Wn Ctx (W + BitVec.ofNat 64 16) W)
    (hd : (⟨D, n⟩ : Region).Disjoint (workR Wn W)) :
    ∀ r ∈ bodyFrame (W + BitVec.ofNat 64 16) W D n, (⟨W + BitVec.ofNat 64 216, 40⟩ : Region).Disjoint r := by
  obtain hWn := L.hWn
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hd.sub_right (Lay.wSub (by decide))).symm
      · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact slots_absFrame L r hr

theorem saved_bodyFrame {Wn : Nat} {Ctx W D : Addr} {n : Nat} (L : Lay Wn Ctx (W + BitVec.ofNat 64 16) W)
    (hd : (⟨D, n⟩ : Region).Disjoint (workR Wn W)) :
    ∀ r ∈ bodyFrame (W + BitVec.ofNat 64 16) W D n, (savedR W).Disjoint r := by
  obtain hWn := L.hWn
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_append.mp hr with hr | hr
    · exact saved_tFrame L (.inr rfl) r hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hd.sub_right (Lay.wSub (by decide))).symm
      · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact saved_absFrame L (.inr rfl) r hr

theorem st0_bodyFrame {Wn : Nat} {Ctx W D : Addr} {n : Nat} (L : Lay Wn Ctx (W + BitVec.ofNat 64 16) W)
    (hd : (⟨D, n⟩ : Region).Disjoint (workR Wn W)) :
    ∀ r ∈ bodyFrame (W + BitVec.ofNat 64 16) W D n, (⟨W + BitVec.ofNat 64 16, 16⟩ : Region).Disjoint r := by
  obtain hWn := L.hWn
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact st0_disj L (by decide) (by decide)
      · exact st0_w L ⟨by decide, by decide⟩
      · exact st0_w L ⟨by decide, by decide⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hd.sub_right (Lay.wSub (by decide))).symm
      · exact st0_disj L (by decide) (by decide)
      · exact st0_w L ⟨by decide, by decide⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact st0_disj L (by decide) (by decide)
    · exact st0_disj L (by decide) (by decide)
    · exact st0_w L ⟨by decide, by decide⟩

theorem ofNat_toNat' (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `finPrep`: the lengths from their slots. -/
theorem finPrep_ok {Wn : Nat} {s : State} {W : Addr} (h19 : s.gpr .x19 = W) (hr : Covers [⟨W, Wn⟩] (s.rd ++ s.wr))
    {al n : Nat} (sL : s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al)
    (sN : s.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n) :
    WP isa (.block finPrep) s fun s' => s'.gpr .x26 = BitVec.ofNat 64 al ∧ s'.gpr .x27 = BitVec.ofNat 64 n ∧
      Regs [.x26, .x27] s s' := by
  obtain q₁ := in_off hr (show 224 + 8 ≤ 512 by decide) (by decide)
  obtain q₂ := in_off hr (show 240 + 8 ≤ 512 by decide) (by decide)
  refine WP.run ⟨_, by simp only [finPrep]; arun [h19, q₁, q₂], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]
    rw [show s.mem.read (W + 224#64) 8 = s.mem.readW (W + BitVec.ofNat 64 224) 64 from rfl, sL]; rfl
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]
    rw [show s.mem.read (W + 240#64) 8 = s.mem.readW (W + BitVec.ofNat 64 240) 64 from rfl, sN]; rfl

/-- The load of the slot at `W + 248` into `x28`. -/
theorem ldr28_ok {Wn : Nat} {Ctx W SP : Addr} {V : BitVec 64} {s : State} (he : Env Wn Ctx (W + BitVec.ofNat 64 16) W SP s)
    (sT : s.mem.readW (W + BitVec.ofNat 64 248) 64 = V) :
    WP isa (.block [.ldr .x .x28 .x19 tlO]) s fun s' => s'.gpr .x28 = V ∧ Regs [.x28] s s' := by
  obtain hWn := he.perm.hWn
  obtain q := he.perm.wR (show 248 + 8 ≤ 512 by decide)
  refine WP.run ⟨_, by arun [he.x19, q], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  simp only [gpr_write, ite_true, ite_false, reduceCtorEq]
  rw [show s.mem.read (W + 248#64) 8 = s.mem.readW (W + BitVec.ofNat 64 248) 64 from rfl, sT]; rfl

/-- `stashArg k`: the stack argument at `sp + k` kept at `W + 248` and in `x28`. -/
theorem stashArg_ok {Wn : Nat} {s : State} {W : Addr} {k : Nat} {V : BitVec 64} (hk : k % 8 = 0 ∧ k < 32768)
    (h19 : s.gpr .x19 = W) (hw : Covers [⟨W, Wn⟩] s.wr)
    (hsp : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 k) 8)
    (hV : s.mem.readW (s.sp + BitVec.ofNat 64 k) 64 = V) :
    WP isa (.block (stashArg k)) s fun s' =>
      s'.gpr .x28 = V ∧ s'.mem = s.mem.writeW (W + BitVec.ofNat 64 248) V ∧
      Others [.x10, .x28] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain w := in_off hw (show 248 + 8 ≤ 512 by decide) (by decide)
  refine WP.run ⟨_, by simp only [stashArg]; arun [h19, hsp, w, hk], rfl⟩ fun s' hs' => ?_
  subst hs'
  obtain e : s.mem.read (s.sp + BitVec.ofNat 64 k) 8 = V := by rw [← hV]; rfl
  refine ⟨by simp [gpr_write, e], ?_, by others_tac, rfl, rfl, rfl⟩
  simp only [mem_write, Mem.writeW, gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, e]

/-- The entry of `seal` and `open`, with `work` at `sp + k`, and the stack argument at `sp + j`
kept at `W + 248` and in `x28`. -/
theorem entryStash_ok {Wn : Nat} {s : State} {Ctx W : Addr} {k j : Nat} {V : BitVec 64} (hk : k % 8 = 0 ∧ k < 32768)
    (hj : j % 8 = 0 ∧ j < 32768) (hW : s.mem.readW (s.sp + BitVec.ofNat 64 k) 64 = W)
    (hspk : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 k) 8)
    (hspj : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 j) 8)
    (hV : s.mem.readW (s.sp + BitVec.ofNat 64 j) 64 = V)
    (hdj : (⟨s.sp + BitVec.ofNat 64 j, 8⟩ : Region).Disjoint (workR Wn W))
    (hCtx : s.gpr .x0 = Ctx) (hperm : Perm Wn Ctx (W + BitVec.ofNat 64 16) W s) :
    WP isa (.block (oneEntry k ++ stashArg j)) s fun s' => Env Wn Ctx (W + BitVec.ofNat 64 16) W s.sp s' ∧
      s'.gpr .x22 = s.gpr .x1 ∧ s'.gpr .x23 = s.gpr .x2 ∧ s'.gpr .x24 = s.gpr .x3 ∧
      s'.gpr .x26 = s.gpr .x3 ∧ s'.gpr .x27 = 0 ∧ s'.gpr .x28 = V ∧
      s'.mem.readW (W + BitVec.ofNat 64 216) 64 = s.gpr .x4 ∧
      s'.mem.readW (W + BitVec.ofNat 64 224) 64 = s.gpr .x5 ∧
      s'.mem.readW (W + BitVec.ofNat 64 232) 64 = s.gpr .x6 ∧
      s'.mem.readW (W + BitVec.ofNat 64 240) 64 = s.gpr .x7 ∧
      s'.mem.readW (W + BitVec.ofNat 64 248) 64 = V ∧
      Frame [entryR W] s.mem s'.mem ∧ SavedAt s'.mem W s ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain hWn := hperm.hWn
  refine WP.block_append (WP.mono (oneEntry_ok hk hW hspk hCtx hperm)
    fun s₁ ⟨he₁, x22₁, x23₁, x24₁, x26₁, x27₁, sl₁, sl₂, sl₃, sl₄, f₁, sv₁, rd₁, wr₁⟩ =>
      WP.mono (stashArg_ok (V := V) hj he₁.x19 he₁.perm.w (by rw [rd₁, wr₁, he₁.sp]; exact hspj)
        (by rw [he₁.sp, f₁.readW (r := ⟨s.sp + BitVec.ofNat 64 j, 8⟩) (Region.contains_self _ _)
          (keep_of_sub (entryR_work W) hdj) (by decide), hV]))
      fun s₂ ⟨x28₂, m₂, og₂, sp₂, rd₂, wr₂⟩ => ?_)
  have so (d : Nat) (hd : d + 8 ≤ 248) : s₂.mem.readW (W + BitVec.ofNat 64 d) 64 =
      s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := by
    rw [m₂, readW_writeW_other _ _ _ (.inl hd) (by omega_arith) (by decide)]
  obtain g₂ : ∀ r ∈ [Reg.x22, .x23, .x24, .x26, .x27], s₂.gpr r = s₁.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact og₂ r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  refine ⟨he₁.keep (fun r hr => og₂ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp₂ rd₂ wr₂,
    by rw [g₂ .x22 (by simp), x22₁], by rw [g₂ .x23 (by simp), x23₁], by rw [g₂ .x24 (by simp), x24₁],
    by rw [g₂ .x26 (by simp), x26₁], by rw [g₂ .x27 (by simp), x27₁], x28₂,
    by rw [so 216 (by decide), sl₁], by rw [so 224 (by decide), sl₂], by rw [so 232 (by decide), sl₃],
    by rw [so 240 (by decide), sl₄], by rw [m₂, Mem.readW_writeW_self64], ?_, ?_, by rw [rd₂, rd₁],
    by rw [wr₂, wr₁]⟩
  · rw [m₂]; exact f₁.writeW (List.mem_singleton_self _) _ (entry_contains W (by decide) (by decide))
  · rw [m₂]
    exact sv₁.frame (rs := [⟨W + BitVec.ofNat 64 248, 8⟩])
      ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide))

/-- `sealPre`'s common arguments. -/
theorem sealCore {w : Nat} {extra extraW : List Region} {s : State} (hs : sealPreXW w extra s extraW) :
    oneCore (w + 1) w s := by
  simp only [sealPreXW] at hs
  sig_split hs
  rename_i hrd hwr dcd dcw dnd dnw dad daw hdrop8 ddw dda hdrop11 dwa wc wn wa wd ww wsp
  clear hdrop8 hdrop11
  have hR := hs
  clear hs
  exact ⟨by rw [hrd]; simp, by rw [hrd]; simp, by rw [hrd]; simp, by rw [hrd]; simp, by rw [hwr]; simp,
    by rw [hwr]; simp, dcd, dcw, dnd, dnw, dad, daw, ddw, dda, dwa, wc, wn, wa, wd, ww, wsp, hR⟩

/-- What `sealPre` gives. -/
theorem sealLay {Wn : Nat} {w : Nat} {extra extraW : List Region} {s : State} (hs : sealPreXW w extra s extraW) :
    OneLay Wn s (w + 1) w ∧ Covers [⟨stackArg s 0, 16⟩] s.wr ∧
      (⟨stackArg s 0, 16⟩ : Region).Disjoint (workR Wn (stackArg s w)) ∧
      (⟨s.gpr .x6, (s.gpr .x7).toNat⟩ : Region).Disjoint ⟨stackArg s 0, 16⟩ := by
  have hs' := hs
  simp only [sealPreXW] at hs'
  obtain ⟨-, hwr, -, -, -, -, -, -, ddt, -, -, dtw, -⟩ := hs'
  exact ⟨oneLay (sealCore hs), covers_of_mem (by rw [hwr]; simp), dtw, ddt⟩

/-- What the entry of `seal` leaves, from `s`, with `work` the stack argument `w`. -/
structure SealEntry (Wn : Nat) (w : Nat) (s s₁ : State) : Prop where
  env : Env Wn (s.gpr .x0) (stackArg s w + BitVec.ofNat 64 16) (stackArg s w) s.sp s₁
  x22 : s₁.gpr .x22 = s.gpr .x1
  x23 : s₁.gpr .x23 = s.gpr .x2
  x24 : s₁.gpr .x24 = s.gpr .x3
  x26 : s₁.gpr .x26 = s.gpr .x3
  x27 : s₁.gpr .x27 = 0
  x28 : s₁.gpr .x28 = stackArg s 0
  sA : s₁.mem.readW (stackArg s w + BitVec.ofNat 64 216) 64 = s.gpr .x4
  sL : s₁.mem.readW (stackArg s w + BitVec.ofNat 64 224) 64 = s.gpr .x5
  sD : s₁.mem.readW (stackArg s w + BitVec.ofNat 64 232) 64 = s.gpr .x6
  sN : s₁.mem.readW (stackArg s w + BitVec.ofNat 64 240) 64 = s.gpr .x7
  sT : s₁.mem.readW (stackArg s w + BitVec.ofNat 64 248) 64 = stackArg s 0
  frame : Frame [entryR (stackArg s w)] s.mem s₁.mem
  saved : SavedAt s₁.mem (stackArg s w) s
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

/-- The entry of `seal`. -/
theorem sealEntry_ok {Wn : Nat} {w : Nat} (hw : w = 1 ∨ w = 2) {extra extraW : List Region} {s : State}
    (hs : sealPreXW w extra s extraW) :
    WP isa (.block (oneEntry (8 * w) ++ stashArg 0)) s (SealEntry Wn w s) := by
  obtain ⟨ol, -, -, -⟩ := sealLay hs
  obtain ⟨L, perm, hsp, dnW, daW, ddW, dcW, daA, dnd, dad, dcd, wn, wa, wd, hR, nR, aR, dW⟩ := ol
  have hW8 : s.mem.readW (s.sp + BitVec.ofNat 64 (8 * w)) 64 = stackArg s w := rfl
  have hT0 : s.mem.readW (s.sp + BitVec.ofNat 64 0) 64 = stackArg s 0 := rfl
  obtain hsp8 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * w)) 8 := hsp w (by omega_arith)
  obtain hsp0 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 0) 8 := hsp 0 (by omega_arith)
  obtain darg : (⟨s.sp + BitVec.ofNat 64 0, 8⟩ : Region).Disjoint (workR Wn (stackArg s w)) := by
    refine daA.sub_left ?_
    show Region.Sub ⟨s.sp + BitVec.ofNat 64 0, 8⟩ ⟨s.sp + BitVec.ofNat 64 (8 * 0), 8 * (w + 1)⟩
    exact Region.sub_prefix (by omega_arith)
  exact WP.mono (entryStash_ok (k := 8 * w) (j := 0) (V := stackArg s 0) (by omega_arith) (by decide) hW8 hsp8 hsp0
      hT0 darg rfl perm)
    fun s₁ ⟨he₁, x22₁, x23₁, x24₁, x26₁, x27₁, x28₁, sl₁, sl₂, sl₃, sl₄, sl₅, f₁, sv₁, rd₁, wr₁⟩ =>
      ⟨he₁, x22₁, x23₁, x24₁, x26₁, x27₁, x28₁, sl₁, sl₂, sl₃, sl₄, sl₅, f₁, sv₁, rd₁, wr₁⟩

/-- `seal` after its entry. -/
theorem sealRest_ok {Wn : Nat} (v : GcmImpl) {w : Nat} {extra extraW : List Region} {s s₁ : State}
    (hs : sealPreXW w extra s extraW) (h₁ : SealEntry Wn w s s₁) :
    WP isa (sealRest v.callees) s₁ fun s' => GprAbi s s' ∧ sealAArch64.post s s' := by
  obtain ⟨he₁, x22₁, x23₁, x24₁, x26₁, x27₁, _, sl₁, sl₂, sl₃, sl₄, sl₅, f₁, sv₁, rd₁, wr₁⟩ := h₁
  obtain ⟨ol, tW, dtw, ddt⟩ := sealLay hs
  simp only [sealAArch64]
  obtain ⟨L, perm, hsp, dnW, daW, ddW, dcW, daA, dnd, dad, dcd, wn, wa, wd, hR, nR, aR, dW⟩ := ol
  obtain h3 := ofNat_toNat' (s.gpr .x3)
  obtain h5 := ofNat_toNat' (s.gpr .x5)
  obtain h7 := ofNat_toNat' (s.gpr .x7)
  generalize hW : stackArg s w = W at *
  generalize hTg : stackArg s 0 = Tg at *
  generalize hCtx : s.gpr .x0 = Ctx at *
  generalize hRR : (s.gpr .x1).toNat = R at *
  generalize hNp : s.gpr .x2 = Np at *
  generalize hnl : (s.gpr .x3).toNat = nl at *
  generalize hA : s.gpr .x4 = A at *
  generalize hal : (s.gpr .x5).toNat = al at *
  generalize hD : s.gpr .x6 = D at *
  generalize hn : (s.gpr .x7).toNat = n at *
  obtain hRb : R = 10 ∨ R = 12 ∨ R = 14 := by rw [← hRR]; exact hR
  obtain hnlt : n < 2 ^ 64 := hn ▸ (s.gpr .x7).isLt
  unfold sealRest
  rw [← h5] at sl₂
  rw [← h7] at sl₄
  obtain sub16 : Region.Sub ⟨W + BitVec.ofNat 64 16, 80⟩ (workR Wn W) := Lay.wSub (by decide)
  obtain kc := keep_of_sub (entryR_work W) (dcW.sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide)))
  obtain hH₁ : blockAt s₁.mem (Ctx + BitVec.ofNat 64 240) = ctxH s.mem Ctx := blockAt_frame f₁ kc
  obtain hnon : DataOk Wn (W + BitVec.ofNat 64 16) W s₁ Np nl :=
    ⟨by rw [rd₁, wr₁]; exact nR, hnl ▸ (s.gpr .x3).isLt, wn, dnW.sub_right sub16, dnW⟩
  obtain haad : DataOk Wn (W + BitVec.ofNat 64 16) W s₁ A al :=
    ⟨by rw [rd₁, wr₁]; exact aR, hal ▸ (s.gpr .x5).isLt, wa, daW.sub_right sub16, daW⟩
  obtain iv₁ : bytesAt s₁.mem Np nl = bytesAt s.mem Np nl :=
    bytesAt_frame f₁ (keep_of_sub (entryR_work W) dnW) (by omega_arith)
  obtain a₁ : bytesAt s₁.mem A al = bytesAt s.mem A al :=
    bytesAt_frame f₁ (keep_of_sub (entryR_work W) daW) (by omega_arith)
  refine front_ok L v he₁ (fun _ _ => rfl : Kept s₁.gpr s₁) x23₁ (by rw [x24₁, ← h3])
    (by rw [x26₁, ← h3]) x27₁ hnon haad hH₁ sl₁ sl₂ sl₃ sl₄ fun s₂ h₂ => ?_
  rw [iv₁, a₁] at h₂
  obtain x22₂ : s₂.gpr .x22 = BitVec.ofNat 64 R := by rw [h₂.x22, x22₁, ← hRR, ofNat_toNat']
  obtain hdat₂ : DataW Wn Ctx (W + BitVec.ofNat 64 16) W s₂ D n :=
    ⟨⟨covers_left (by rw [h₂.wr, wr₁]; exact dW), hnlt, wd, ddW.sub_right sub16, ddW⟩,
      by rw [h₂.wr, wr₁]; exact dW, dcd⟩
  obtain hB : BodyIn Ctx (W + BitVec.ofNat 64 16) W s.sp s₂.gpr R n 0 D (bytesAt s.mem A al) [] (ctxH s.mem Ctx) s₂ :=
    ⟨h₂.env, fun _ _ => rfl, x22₂, hRb, h₂.x25, h₂.x26, h₂.x27, h₂.x28, rfl, by decide, hdat₂, h₂.hH⟩
  refine WP.seq (WP.mono (WP.with_rdwr (encBody_ok L v hB (inc32 (Spec.Gcm.j0 (ctxH s.mem Ctx)
    (bytesAt s.mem Np nl))))) fun s₃ ⟨h₃, rd₃, wr₃⟩ => ?_)
  obtain ⟨o₁, o₂, o₃⟩ := h₃.post h₂.abs (Proof.Gcm.ctr_zero _ _ _ _ h₂.cb)
  obtain slot₃ : ∀ d, 216 ≤ d → d + 8 ≤ 256 →
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂' => by
    rw [slot_kept h₃.frame (slots_bodyFrame L ddW) h₁ h₂', slot_kept h₂.frame (slots_frontFrame L) h₁ h₂']
  refine WP.seq (WP.mono (finPrep_ok (al := al) (n := n) h₃.env.x19 (covers_left h₃.env.perm.w)
    (by rw [slot₃ 224 (by decide) (by decide), sl₂]) (by rw [slot₃ 240 (by decide) (by decide), sl₄]))
    fun s₄ ⟨x26₄, x27₄, r₄⟩ => ?_)
  obtain he₄ := h₃.env.of_regs r₄
  refine WP.seq (WP.mono (ldr28_ok (V := Tg) he₄ (by rw [r₄.mem, slot₃ 248 (by decide) (by decide), sl₅]))
    fun s₄' ⟨x28₄', r₄'⟩ => ?_)
  obtain he₄' := he₄.of_regs r₄'
  obtain x22₄ : s₄'.gpr .x22 = BitVec.ofNat 64 R := by
    rw [r₄'.others _ (by decide), r₄.others _ (by decide), h₃.kept .x22 (by decide), x22₂]
  obtain x26₄' : s₄'.gpr .x26 = BitVec.ofNat 64 al := by rw [r₄'.others _ (by decide), x26₄]
  obtain x27₄' : s₄'.gpr .x27 = BitVec.ofNat 64 n := by rw [r₄'.others _ (by decide), x27₄]
  obtain m₄ : s₄'.mem = s₃.mem := by rw [r₄'.mem, r₄.mem]
  obtain kcd : ∀ r ∈ bodyFrame (W + BitVec.ofNat 64 16) W D n, (⟨Ctx, 256⟩ : Region).Disjoint r :=
    keep_body dcW dcd
  obtain hc₃ : ciphOf s₃.mem Ctx R = ciphOf s.mem Ctx R := by
    rw [ciph_frame h₃.frame kcd hRb, ciph_frame h₂.frame (keep_of_sub (frontFrame_work W) dcW) hRb,
      ciph_frame f₁ (keep_of_sub (entryR_work W) dcW) hRb]
  obtain hD₂ : bytesAt s₂.mem D n = bytesAt s.mem D n := by
    rw [bytesAt_frame h₂.frame (keep_of_sub (frontFrame_work W) ddW) (by omega_arith),
      bytesAt_frame f₁ (keep_of_sub (entryR_work W) ddW) (by omega_arith)]
  obtain hc₂ : ciphOf s₂.mem Ctx R = ciphOf s.mem Ctx R := by
    rw [ciph_frame h₂.frame (keep_of_sub (frontFrame_work W) dcW) hRb,
      ciph_frame f₁ (keep_of_sub (entryR_work W) dcW) hRb]
  obtain hH₄ : blockAt s₄'.mem (Ctx + BitVec.ofNat 64 240) = ctxH s.mem Ctx := by
    rw [m₄, blockAt_frame h₃.frame fun r hr => (kcd r hr).sub_left (Lay.ctxSub (by decide)), h₂.hH]
  obtain hlen : ([] ++ xorKs (ciphOf s₂.mem Ctx R) (inc32 (Spec.Gcm.j0 (ctxH s.mem Ctx) (bytesAt s.mem Np nl))) 0
      (bytesAt s₂.mem D n)).length = n := by
    rw [List.nil_append, Proof.Gcm.length_xorKs, length_bytesAt]
  refine WP.seq (WP.mono (WP.with_rdwr (finBody_ok L v (.inl rfl) (a := bytesAt s.mem A al) (H := ctxH s.mem Ctx)
    (c := [] ++ xorKs (ciphOf s₂.mem Ctx R) (inc32 (Spec.Gcm.j0 (ctxH s.mem Ctx) (bytesAt s.mem Np nl))) 0
      (bytesAt s₂.mem D n))
    he₄' (fun _ _ => rfl) x22₄ hRb (by rw [x26₄', length_bytesAt]) (by rw [x27₄', hlen]) (by rw [hlen]; exact hnlt)
    hH₄)) fun s₅ ⟨⟨he₅, hk₅, f₅, out₅⟩, _, wr₅⟩ => ?_)
  obtain sv₅ : SavedAt s₅.mem W s := by
    have := (sv₁.frame h₂.frame (saved_frontFrame L)).frame h₃.frame (saved_bodyFrame L ddW)
    rw [← m₄] at this
    exact this.frame f₅ (saved_finFrame L (.inl rfl))
  obtain x28₅ : s₅.gpr .x28 = Tg := by rw [hk₅ .x28 (by decide), x28₄']
  obtain wr₅' : s₅.wr = s.wr := by rw [wr₅, r₄'.wr, r₄.wr, wr₃, h₂.wr, wr₁]
  refine WP.seq (WP.mono (tagOut_ok he₅.x19 x28₅ (covers_left he₅.perm.w) (by rw [wr₅']; exact tW)
    (dtw.sub_right (Region.sub_prefix (by decide)))) fun s₆ ⟨out₆, f₆, og₆, sp₆, rd₆, wr₆⟩ => ?_)
  obtain he₆ : Env Wn Ctx (W + BitVec.ofNat 64 16) W s.sp s₆ := he₅.keep (fun r hr => og₆ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₆ rd₆ wr₆
  obtain sv₆ : SavedAt s₆.mem W s := sv₅.frame f₆ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (dtw.sub_right (Lay.wSub (by decide))).symm
  refine WP.mono (exit_ok he₆.x19 he₆.sp (covers_left he₆.perm.w) sv₆) fun s' ⟨ga, hm, _⟩ => ⟨ga, ?_⟩
  rw [hm]
  obtain hdata : bytesAt s₆.mem D n = gctr (ctxCiph s.mem Ctx R)
      (inc32 (Spec.Gcm.j0 (ctxH s.mem Ctx) (bytesAt s.mem Np nl))) (bytesAt s.mem D n) := by
    rw [bytesAt_frame f₆ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ddt) (by omega_arith),
      bytesAt_frame f₅ (keep_of_sub (finFrame_work W (.inl rfl)) ddW) (by omega_arith), m₄, o₃, hc₂, hD₂,
      Proof.Gcm.gctr_eq]
    rfl
  obtain hj₄ : blockAt s₄'.mem (W + BitVec.ofNat 64 16) = Spec.Gcm.j0 (ctxH s.mem Ctx) (bytesAt s.mem Np nl) := by
    rw [m₄, blockAt_frame h₃.frame (st0_bodyFrame L ddW), h₂.j0]
  obtain htag := out₅ (by rw [m₄]; exact o₁)
  rw [add_ofNat_zero, m₄, hc₃, ← m₄, hj₄] at htag
  obtain he : [] ++ xorKs (ciphOf s₂.mem Ctx R) (inc32 (Spec.Gcm.j0 (ctxH s.mem Ctx) (bytesAt s.mem Np nl))) 0
      (bytesAt s₂.mem D n) = gctr (ctxCiph s.mem Ctx R)
        (inc32 (Spec.Gcm.j0 (ctxH s.mem Ctx) (bytesAt s.mem Np nl))) (bytesAt s.mem D n) := by
    rw [List.nil_append, hc₂, hD₂, Proof.Gcm.gctr_eq]; rfl
  rw [he] at htag
  rw [hdata, out₆, htag, Spec.Gcm.encryptWith, Proof.Gcm.fullTag_eq,
    List.take_of_length_le (by rw [Proof.Cmac.toBytes_length])]
  rfl

theorem seal_wp (v : GcmImpl) {s : State} (hs : sealAArch64.pre s) :
    WP isa («seal» v.callees) s fun s' => GprAbi s s' ∧ sealAArch64.post s s' :=
  WP.seq (WP.mono (sealEntry_ok (.inl rfl) (sealPreX_W hs)) fun _ h₁ => sealRest_ok v (sealPreX_W hs) h₁)

end VG.Proof.AesGcm.AArch64
