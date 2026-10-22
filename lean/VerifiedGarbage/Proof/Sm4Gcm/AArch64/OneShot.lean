module

public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Front
public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Body
public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Contract
public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.FinTag
public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.OneEntry
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamInit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-!
# SM4-GCM on AArch64: what `seal` and `open` share

Untrusted: everything here is checked by Lean. The layout of a one-shot call
(`oneLay`): the state at `W + 16`, inside `work`; everything the pieces
write is inside `work`, but for the data (`*_work`) and the tag.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Sm4Gcm.AArch64
open VG.Impl.AesGcm.AArch64 (aadO alenO cmp cmp16 cmpSeg copy copy4 copy8 copyB copyLoop copyW dataO fo imm initState j012 lenO minK mov ptr rO restore save saved scrO stashArg tO tagIn tagLenOk tagOut textArgs tlO uO vO verRet xor xor4 xor8 xorB xorLoop xorW Fn)
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- `work`. -/
abbrev workR (W : Addr) : Region := ⟨W, 768⟩

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

theorem finFrame_work (W SP : Addr) {o : Nat} (ho : o = 0 ∨ o = 112) :
    ∀ r ∈ finFrame (W + BitVec.ofNat 64 16) W SP o, Region.Sub r (workR W) ∨ r = stk SP := by
  intro r hr
  simp only [finFrame, tFrame, tagFrame, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl (stW (by decide))
  · exact .inl (Lay.wSub (by decide))
  · exact .inl (Lay.wSub (by decide))
  · exact .inl (Lay.wSub (by decide))
  · exact .inl (Lay.wSub (by decide))
  · exact .inl (Lay.wSub (by omega))
  · exact .inl (Lay.wSub (by decide))
  · exact .inr rfl

theorem keep_fin {W SP : Addr} {o : Nat} (ho : o = 0 ∨ o = 112) {X : Region} (hX : X.Disjoint (workR W))
    (hS : X.Disjoint (stk SP)) : ∀ r ∈ finFrame (W + BitVec.ofNat 64 16) W SP o, X.Disjoint r := fun r hr => by
  rcases finFrame_work W SP ho r hr with h | rfl
  · exact hX.sub_right h
  · exact hS

/-- The regions a body writes: in `work`, the data, or the callee's stack. -/
theorem bodyFrame_work (W SP D : Addr) (n : Nat) :
    ∀ r ∈ bodyFrame (W + BitVec.ofNat 64 16) W SP D n,
      Region.Sub r (workR W) ∨ r = ⟨D, n⟩ ∨ r = stk SP := by
  intro r hr
  simp only [bodyFrame, tFrame, crFrame, absFrame, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl (stW (by decide))
  · exact .inl (Lay.wSub (by decide))
  · exact .inl (Lay.wSub (by decide))
  · exact .inr (.inl rfl)
  · exact .inl (stW (by decide))
  · exact .inr (.inr rfl)
  · exact .inl (stW (by decide))
  · exact .inl (stW (by decide))
  · exact .inl (Lay.wSub (by decide))

theorem keep_body {W SP D : Addr} {n : Nat} {X : Region} (hX : X.Disjoint (workR W)) (hD : X.Disjoint ⟨D, n⟩)
    (hS : X.Disjoint (stk SP)) : ∀ r ∈ bodyFrame (W + BitVec.ofNat 64 16) W SP D n, X.Disjoint r := fun r hr => by
  rcases bodyFrame_work W SP D n r hr with h | rfl | rfl
  · exact hX.sub_right h
  · exact hD
  · exact hS

/-- What `seal` and `open` share: `ctx`, `nonce`, `aad`, the `n` stack
arguments, `data`, and `work` the `w`-th of them. -/
def oneCore (n w : Nat) (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .x0, 256⟩
  let nonce : Region := ⟨s.gpr .x1, (s.gpr .x2).toNat⟩
  let aad : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
  let data : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
  let work : Region := ⟨stackArg s w, 768⟩
  ctx ∈ s.rd ∧ nonce ∈ s.rd ∧ aad ∈ s.rd ∧ args s n ∈ s.rd ∧ data ∈ s.wr ∧ work ∈ s.wr ∧
    ctx.Disjoint data ∧ ctx.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧
    data.Disjoint work ∧ data.Disjoint (args s n) ∧ work.Disjoint (args s n) ∧
    (stk s.sp).Disjoint ctx ∧ (stk s.sp).Disjoint nonce ∧ (stk s.sp).Disjoint aad ∧
    (stk s.sp).Disjoint data ∧ (stk s.sp).Disjoint work ∧
    (s.gpr .x0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + (s.gpr .x2).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64 ∧ (s.gpr .x5).toNat + (s.gpr .x6).toNat ≤ 2 ^ 64 ∧
    (stackArg s w).toNat + 768 ≤ 2 ^ 64 ∧ s.sp.toNat + 8 * n ≤ 2 ^ 64 ∧ 3264 ≤ s.sp.toNat

/-- What `oneCore` gives, with `work` the `w`-th of the `n` arguments on the stack. -/
structure OneLay (s : State) (n w : Nat) : Prop where
  lay : Lay (s.gpr .x0) (stackArg s w + BitVec.ofNat 64 16) (stackArg s w) s.sp
  perm : Perm (s.gpr .x0) (stackArg s w + BitVec.ofNat 64 16) (stackArg s w) s
  hsp : ∀ i < n, InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * i)) 8
  nonce : (⟨s.gpr .x1, (s.gpr .x2).toNat⟩ : Region).Disjoint (workR (stackArg s w))
  aad : (⟨s.gpr .x3, (s.gpr .x4).toNat⟩ : Region).Disjoint (workR (stackArg s w))
  data : (⟨s.gpr .x5, (s.gpr .x6).toNat⟩ : Region).Disjoint (workR (stackArg s w))
  ctx : (⟨s.gpr .x0, 256⟩ : Region).Disjoint (workR (stackArg s w))
  args : (args s n).Disjoint (workR (stackArg s w))
  nd : (⟨s.gpr .x1, (s.gpr .x2).toNat⟩ : Region).Disjoint ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
  ad : (⟨s.gpr .x3, (s.gpr .x4).toNat⟩ : Region).Disjoint ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
  cd : (⟨s.gpr .x0, 256⟩ : Region).Disjoint ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
  nw : (s.gpr .x1).toNat + (s.gpr .x2).toNat ≤ 2 ^ 64
  aw : (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64
  dw : (s.gpr .x5).toNat + (s.gpr .x6).toNat ≤ 2 ^ 64
  kn : (stk s.sp).Disjoint ⟨s.gpr .x1, (s.gpr .x2).toNat⟩
  ka : (stk s.sp).Disjoint ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
  kd : (stk s.sp).Disjoint ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
  nonceR : Covers [⟨s.gpr .x1, (s.gpr .x2).toNat⟩] (s.rd ++ s.wr)
  aadR : Covers [⟨s.gpr .x3, (s.gpr .x4).toNat⟩] (s.rd ++ s.wr)
  dataW : Covers [⟨s.gpr .x5, (s.gpr .x6).toNat⟩] s.wr

theorem oneLay {s : State} {n w : Nat} (hs : oneCore n w s) : OneLay s n w := by
  simp only [oneCore] at hs
  sig_split hs
  rename_i mc mn ma mg md mw dcd dcw dnd dnw dad daw ddw dda dwa kc kn ka kd kw wc wn wa wd ww wsp
  have hsp := hs
  clear hs
  have sub16 : Region.Sub ⟨stackArg s w + BitVec.ofNat 64 16, 80⟩ (workR (stackArg s w)) := Lay.wSub (by decide)
  refine ⟨⟨wc, ?_, ww, dcw.sub_right sub16, dcw, ?_, ?_, hsp, kc, kw.sub_right sub16, kw⟩,
    ⟨covers_mem (List.mem_append_left _ mc),
      covers_off (k := 768) (covers_of_mem mw) (show 16 + 80 ≤ 768 by decide) (by decide),
      covers_of_mem mw⟩,
    fun i hi => ?_, dnw, daw, ddw, dcw, dwa.symm, dnd, dad, dcd, wn, wa, wd, kn, ka, kd,
    covers_mem (List.mem_append_left _ mn), covers_mem (List.mem_append_left _ ma), covers_of_mem md⟩
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16) (by decide), Nat.mod_eq_of_lt (by omega)]
    omega
  · simpa using Offset.disjoint (stackArg s w) (d := 16) (n := 80) (e := 0) (k := 16) (.inr (by decide))
      (by decide) (by decide)
  · exact Offset.disjoint (stackArg s w) (d := 16) (n := 80) (e := 96) (k := 672) (.inl (by decide))
      (by decide) (by decide)
  · refine ⟨args s n, List.mem_append_left _ mg, ?_⟩
    have e : stackArgAddr s 0 = s.sp := by simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
    simp only [args, e]
    exact Offset.contains_base _ (by omega) (by omega)

end VG.Proof.Sm4Gcm.AArch64
