import VerifiedGarbage.Proof.AesGcm.AArch64.Front
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamVerify

/-!
# AES-GCM on AArch64: what `seal` and `open` share

Untrusted: everything here is checked by Lean. The layout of a one-shot call
(`oneLay`): the state at `W + 16`, inside `work`; everything the pieces
write is inside `work`, but for the data (`*_work`) and the tag.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- `work`. -/
abbrev workR (W : Addr) : Region := ⟨W, 2560⟩

theorem stW {W : Addr} {d k : Nat} (h : d + k ≤ 80) :
    Region.Sub ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 d, k⟩ (workR W) := by
  rw [add_ofNat_assoc]; exact Lay.wSub (by omega)

theorem keep_of_sub {rs : List Region} {W : Addr} (hs : ∀ r ∈ rs, Region.Sub r (workR W)) {X : Region}
    (hX : X.Disjoint (workR W)) : ∀ r ∈ rs, X.Disjoint r := fun r hr => hX.sub_right (hs r hr)

theorem entryR_work (W : Addr) : ∀ r ∈ [entryR W], Region.Sub r (workR W) := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact Lay.wSub (by decide)

theorem frontFrame_work (W : Addr) : ∀ r ∈ frontFrame (W + BitVec.ofNat 64 16) W, Region.Sub r (workR W) := by
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

theorem finFrame_work (W : Addr) {o : Nat} (ho : o = 0 ∨ o = 112) :
    ∀ r ∈ finFrame (W + BitVec.ofNat 64 16) W o, Region.Sub r (workR W) := by
  intro r hr
  simp only [finFrame, tFrame, tagFrame, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact stW (by decide)
  · exact Lay.wSub (by decide)
  · exact Lay.wSub (by decide)
  · exact Lay.wSub (by decide)
  · exact Lay.wSub (by decide)
  · exact Lay.wSub (by omega)
  · exact Lay.wSub (by decide)

/-- The regions a body writes: in `work`, or the data. -/
theorem bodyFrame_work (W D : Addr) (n : Nat) :
    ∀ r ∈ bodyFrame (W + BitVec.ofNat 64 16) W D n, Region.Sub r (workR W) ∨ r = ⟨D, n⟩ := by
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

theorem keep_body {W D : Addr} {n : Nat} {X : Region} (hX : X.Disjoint (workR W)) (hD : X.Disjoint ⟨D, n⟩) :
    ∀ r ∈ bodyFrame (W + BitVec.ofNat 64 16) W D n, X.Disjoint r := fun r hr => by
  rcases bodyFrame_work W D n r hr with h | rfl
  · exact hX.sub_right h
  · exact hD

/-- What `oneCore` gives, with `work` the `w`-th of the `n` arguments on the stack. -/
structure OneLay (s : State) (n w : Nat) : Prop where
  lay : Lay (s.gpr .x0) (stackArg s w + BitVec.ofNat 64 16) (stackArg s w)
  perm : Perm (s.gpr .x0) (stackArg s w + BitVec.ofNat 64 16) (stackArg s w) s
  hsp : ∀ i < n, InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * i)) 8
  nonce : (⟨s.gpr .x2, (s.gpr .x3).toNat⟩ : Region).Disjoint (workR (stackArg s w))
  aad : (⟨s.gpr .x4, (s.gpr .x5).toNat⟩ : Region).Disjoint (workR (stackArg s w))
  data : (⟨s.gpr .x6, (s.gpr .x7).toNat⟩ : Region).Disjoint (workR (stackArg s w))
  ctx : (⟨s.gpr .x0, 256⟩ : Region).Disjoint (workR (stackArg s w))
  args : (args s n).Disjoint (workR (stackArg s w))
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

theorem oneLay {s : State} {n w : Nat} (hs : oneCore n w s) : OneLay s n w := by
  simp only [oneCore] at hs
  obtain ⟨mc, mn, ma, mg, md, mw, dcd, dcw, dnd, dnw, dad, daw, ddw, dda, dwa, wc, wn, wa, wd, ww, wsp, hR⟩ := hs
  have sub16 : Region.Sub ⟨stackArg s w + BitVec.ofNat 64 16, 80⟩ (workR (stackArg s w)) := Lay.wSub (by decide)
  refine ⟨⟨wc, ?_, ww, dcw.sub_right sub16, dcw, ?_, ?_⟩, ⟨covers_mem (List.mem_append_left _ mc),
    covers_off (k := 2560) (covers_of_mem mw) (show 16 + 80 ≤ 2560 by decide) (by decide),
    covers_of_mem mw⟩,
    fun i hi => ?_, dnw, daw, ddw, dcw, dwa.symm, dnd, dad, dcd, wn, wa, wd, hR,
    covers_mem (List.mem_append_left _ mn), covers_mem (List.mem_append_left _ ma), covers_of_mem md⟩
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16) (by decide), Nat.mod_eq_of_lt (by omega)]
    omega
  · simpa using Offset.disjoint (stackArg s w) (d := 16) (n := 80) (e := 0) (k := 16) (.inr (by decide))
      (by decide) (by decide)
  · have := Offset.disjoint (stackArg s w) (d := 16) (n := 80) (e := 96) (k := 2464) (.inl (by decide))
      (by decide) (by decide)
    exact this
  · refine ⟨args s n, List.mem_append_left _ mg, ?_⟩
    have e : stackArgAddr s 0 = s.sp := by simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
    simp only [args, e]
    exact Offset.contains_base _ (by omega) (by omega)

end VG.Proof.AesGcm.AArch64
