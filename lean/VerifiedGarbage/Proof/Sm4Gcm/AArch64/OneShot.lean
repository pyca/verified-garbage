module

public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Front
public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Body
public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Contract
public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.FinTag
public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Env
import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Save
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Spec.Gcm
public import VerifiedGarbage.Proof.AesGcm.AArch64.Save
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamInit

/-! ### `Sm4Gcm.AArch64.OneEntry`, which only this module used -/

section

/-!
# SM4-GCM on AArch64: the entry of `seal` and `open`

Untrusted: everything here is checked by Lean. `work` comes from the stack
(`ldrSp_ok`); the entry saves our caller's registers there, keeps the arguments it needs
later at `W + 216` (`oneEntry_ok`, `OneE`), and puts the state at
`W + 16` (`oneLay`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Sm4Gcm.AArch64
open VG.Impl.AesGcm.AArch64 (aadO alenO cmp cmp16 cmpSeg copy copy4 copy8 copyB copyLoop copyW dataO fo imm initState j012 lenO minK mov ptr rO restore save saved scrO stashArg tO tagIn tagLenOk tagOut textArgs tlO uO vO verRet xor xor4 xor8 xorB xorLoop xorW Fn)
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- The memory after the entry: the registers saved and the arguments kept. -/
def entryMem (m : Mem) (W : Addr) (g : Reg → BitVec 64) : Mem :=
  ((((savedMem m W g).writeW (W + BitVec.ofNat 64 216) (g .x3)).writeW (W + BitVec.ofNat 64 224) (g .x4)).writeW
    (W + BitVec.ofNat 64 232) (g .x5)).writeW (W + BitVec.ofNat 64 240) (g .x6)

/-- What the entry keeps at `W + 128`. -/
abbrev entryR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 128, 128⟩

theorem entry_contains (W : Addr) {d : Nat} (h₁ : 128 ≤ d) (h₂ : d + 8 ≤ 256) :
    (entryR W).Contains (W + BitVec.ofNat 64 d) 8 := by
  rw [show W + BitVec.ofNat 64 d = (W + BitVec.ofNat 64 128) + BitVec.ofNat 64 (d - 128) from
    (Offset.add_add_eq W (by omega_using [h₁])).symm]
  exact Offset.contains_base _ (by omega_using [h₂]) (by omega_using [h₂])

theorem entryMem_frame (m : Mem) (W : Addr) (g : Reg → BitVec 64) : Frame [entryR W] m (entryMem m W g) := by
  have c (d : Nat) (h₁ : 128 ≤ d) (h₂ : d + 8 ≤ 256) := entry_contains W h₁ h₂
  exact (((((savedMem_frame m W g).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩).writeW
    (List.mem_singleton_self _) _ (c 216 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (c 224 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (c 232 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (c 240 (by decide) (by decide))

theorem entryMem_saved (m : Mem) (W : Addr) {g : Reg → BitVec 64} {s₀ : State}
    (hg : ∀ p ∈ saved, g p.1 = s₀.gpr p.1) : SavedAt (entryMem m W g) W s₀ := by
  have h₀ : SavedAt (savedMem m W g) W s₀ := fun p hp => (savedMem_slot m W g p hp).trans (hg p hp)
  refine h₀.frame (rs := [⟨W + BitVec.ofNat 64 216, 32⟩]) ?_ ?_
  · have c (d : Nat) (h₁ : 216 ≤ d) (h₂ : d + 8 ≤ 248) :
        (⟨W + BitVec.ofNat 64 216, 32⟩ : Region).Contains (W + BitVec.ofNat 64 d) 8 := by
      rw [show W + BitVec.ofNat 64 d = (W + BitVec.ofNat 64 216) + BitVec.ofNat 64 (d - 216) from
        (Offset.add_add_eq W (by omega_using [h₁])).symm]
      exact Offset.contains_base _ (by omega_using [h₂]) (by omega_using [h₂])
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 216 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 224 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 232 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 240 (by decide) (by decide))
  · intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)

theorem entryMem_slot (m : Mem) (W : Addr) (g : Reg → BitVec 64) :
    (entryMem m W g).readW (W + BitVec.ofNat 64 216) 64 = g .x3 ∧
    (entryMem m W g).readW (W + BitVec.ofNat 64 224) 64 = g .x4 ∧
    (entryMem m W g).readW (W + BitVec.ofNat 64 232) 64 = g .x5 ∧
    (entryMem m W g).readW (W + BitVec.ofNat 64 240) 64 = g .x6 := by
  simp only [entryMem]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  repeat (first
    | rw [Mem.readW_writeW_self64]
    | rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide)])

/-- The load of a stack argument, at `sp + k`. -/
theorem ldrSp_ok {s : State} {t : Reg} {k : Nat} {V : BitVec 64} (hk : k % 8 = 0 ∧ k < 32768)
    (hV : s.mem.readW (s.sp + BitVec.ofNat 64 k) 64 = V)
    (hsp : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 k) 8) :
    ∃ s', runBlock isa [.ldrSp t k] s = some s' ∧ s'.gpr t = V ∧ (∀ r, r ≠ t → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by arun [hsp, hk], ?_⟩
  refine ⟨?_, fun r hr => by simp [gpr_write, hr], rfl, rfl, rfl, rfl⟩
  rw [← hV]
  simp [gpr_write, Mem.readW]

/-- After the entry, with `work` at `sp + k`. -/
theorem oneEntry_ok {s : State} {Ctx W : Addr} {k : Nat} (hk : k % 8 = 0 ∧ k < 32768)
    (hW : s.mem.readW (s.sp + BitVec.ofNat 64 k) 64 = W)
    (hsp : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 k) 8) (hCtx : s.gpr .x0 = Ctx)
    (hperm : Perm Ctx (W + BitVec.ofNat 64 16) W s) :
    WP isa (.block (oneEntry k)) s fun s' => Env Ctx (W + BitVec.ofNat 64 16) W s.sp s' ∧
      s'.gpr .x23 = s.gpr .x1 ∧ s'.gpr .x24 = s.gpr .x2 ∧
      s'.gpr .x26 = s.gpr .x2 ∧ s'.gpr .x27 = 0 ∧ s'.gpr .x7 = s.gpr .x7 ∧
      s'.mem.readW (W + BitVec.ofNat 64 216) 64 = s.gpr .x3 ∧
      s'.mem.readW (W + BitVec.ofNat 64 224) 64 = s.gpr .x4 ∧
      s'.mem.readW (W + BitVec.ofNat 64 232) 64 = s.gpr .x5 ∧
      s'.mem.readW (W + BitVec.ofNat 64 240) 64 = s.gpr .x6 ∧
      Frame [entryR W] s.mem s'.mem ∧ SavedAt s'.mem W s ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₀, run₀, x9₀, g₀, sp₀, m₀, rd₀, wr₀⟩ := ldrSp_ok (t := .x9) hk hW hsp
  have hperm₀ : Perm Ctx (W + BitVec.ofNat 64 16) W s₀ := hperm.of_eq rd₀ wr₀
  obtain ⟨s₁, run₁, g₁, sp₁, rd₁, wr₁, m₁⟩ := save_ok s₀ .x9 x9₀ hperm₀.w
  have w (d : Nat) (h : d + 8 ≤ 768) := in_off hperm₀.w h (by decide)
  rw [← wr₁] at w
  obtain ⟨s₂, run₂, x19₂, x20₂, x21₂, x23₂, x24₂, x26₂, x27₂, x7₂, sp₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [mov .x19 .x9, ptr .x20 .x19 16, mov .x21 .x0, .str .x .x3 .x19 aadO,
        .str .x .x4 .x19 alenO, .str .x .x5 .x19 dataO, .str .x .x6 .x19 lenO, mov .x23 .x1,
        mov .x24 .x2, mov .x26 .x2, imm .x27 0] s₁ = some s₂ ∧
      s₂.gpr .x19 = W ∧ s₂.gpr .x20 = W + BitVec.ofNat 64 16 ∧ s₂.gpr .x21 = Ctx ∧
      s₂.gpr .x23 = s.gpr .x1 ∧ s₂.gpr .x24 = s.gpr .x2 ∧ s₂.gpr .x26 = s.gpr .x2 ∧ s₂.gpr .x27 = 0 ∧ s₂.gpr .x7 = s.gpr .x7 ∧
      s₂.sp = s₁.sp ∧
      s₂.mem = (((s₁.mem.writeW (W + BitVec.ofNat 64 216) (s.gpr .x3)).writeW (W + BitVec.ofNat 64 224)
        (s.gpr .x4)).writeW (W + BitVec.ofNat 64 232) (s.gpr .x5)).writeW (W + BitVec.ofNat 64 240) (s.gpr .x6) ∧
      s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    have gx : ∀ r, r ≠ .x9 → s₁.gpr r = s.gpr r := fun r hr => by rw [g₁, g₀ r hr]
    have x9₁ : s₁.gpr .x9 = W := by rw [g₁, x9₀]
    have w₁ := w 216 (by decide)
    have w₂ := w 224 (by decide)
    have w₃ := w 232 (by decide)
    have w₄ := w 240 (by decide)
    refine ⟨_, by arun [x9₁, BitVec.add_zero, w₁, w₂, w₃, w₄], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, rfl, rfl⟩
    · simp [gpr_write, x9₁]
    · simp [gpr_write, x9₁]
    · simp [gpr_write, gx .x0 (by decide), hCtx]
    · simp [gpr_write, gx .x1 (by decide)]
    · simp [gpr_write, gx .x2 (by decide)]
    · simp [gpr_write, gx .x2 (by decide)]
    · simp [gpr_write]
    · simp [gpr_write, gx .x7 (by decide)]
    · simp only [mem_write, Mem.writeW, BitVec.setWidth_eq, gpr_write, ite_true, ite_false, reduceCtorEq,
        gx .x3 (by decide), gx .x4 (by decide), gx .x5 (by decide), gx .x6 (by decide), x9₁]
  refine WP.block_append (WP.block_append (WP.of_runBlock ⟨s₀, run₀, WP.of_runBlock ⟨s₁, run₁,
    WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩⟩))
  have hm : s₂.mem = entryMem s.mem W s₀.gpr := by
    rw [m₂, m₁, m₀, entryMem, g₀ .x3 (by decide), g₀ .x4 (by decide), g₀ .x5 (by decide), g₀ .x6 (by decide)]
  obtain ⟨e₁, e₂, e₃, e₄⟩ := entryMem_slot s.mem W s₀.gpr
  rw [g₀ .x3 (by decide)] at e₁
  rw [g₀ .x4 (by decide)] at e₂
  rw [g₀ .x5 (by decide)] at e₃
  rw [g₀ .x6 (by decide)] at e₄
  refine ⟨⟨x19₂, x20₂, x21₂, by rw [sp₂, sp₁, sp₀], hperm.of_eq (by rw [rd₂, rd₁, rd₀]) (by rw [wr₂, wr₁, wr₀])⟩,
    x23₂, x24₂, x26₂, x27₂, x7₂, by rw [hm]; exact e₁, by rw [hm]; exact e₂, by rw [hm]; exact e₃,
    by rw [hm]; exact e₄, by rw [hm]; exact entryMem_frame _ _ _,
    by rw [hm]; exact entryMem_saved _ _ fun p hp => g₀ p.1 (by
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
    by rw [rd₂, rd₁, rd₀], by rw [wr₂, wr₁, wr₀]⟩

end VG.Proof.Sm4Gcm.AArch64

end

end


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
  rw [add_ofNat_assoc]; exact Lay.wSub (by omega_using [h])

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
  · exact .inl (Lay.wSub (by omega_using [ho]))
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
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16) (by decide), Nat.mod_eq_of_lt (by omega_using [ww])]
    omega_using [ww]
  · simpa using Offset.disjoint (stackArg s w) (d := 16) (n := 80) (e := 0) (k := 16) (.inr (by decide))
      (by decide) (by decide)
  · exact Offset.disjoint (stackArg s w) (d := 16) (n := 80) (e := 96) (k := 672) (.inl (by decide))
      (by decide) (by decide)
  · refine ⟨args s n, List.mem_append_left _ mg, ?_⟩
    have e : stackArgAddr s 0 = s.sp := by simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
    simp only [args, e]
    exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [wsp, hi])

end VG.Proof.Sm4Gcm.AArch64
