import VerifiedGarbage.Proof.AesOcb.X86_64.SealCT
import VerifiedGarbage.Proof.AesOcb.X86_64.Open

/-!
# AES-OCB on x86-64: `vg_aes_ocb_open` is constant time

Untrusted: everything here is checked by Lean. As `seal` (`front_rel`), then
the copy of the received tag to `W`, the comparison, the mask and `restore`,
which pass the taint analysis from the public slots and the address of the
tag at `W + tgO`: the comparison's result is a value, not a branch.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (BlocksImpl)

section
variable {s₀ s₀' : State} {K W SP N A D : Addr} {R nl al n tl : Nat} {Tg : Addr}
  (T : Two s₀ s₀' K W SP N A D R nl al n tl Tg)
include T

/-- `recv` keeps the public arguments. -/
theorem recv_one {s : State} (o : OneT K W SP R N A D nl n tl Tg s) :
    WP isa recv s (One K W SP R N A D nl n tl) := by
  refine WP.mono (recv_ok o.1.env T.ar.t1 T.ar.t16 o.2.1 o.1.sl.tl o.2.2 T.ar.tag.w) fun t ⟨m, g, rd, wr⟩ => ?_
  have fr : Frame (mutR W SP D n) s.mem t.mem := by
    rw [m]
    refine (writeBytes_frame _ _ _ (by rw [Proof.AesCcm.X86_64.length_bytesAt]; exact Region.contains_self _ _)).sub
      fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by have := T.ar.t16; omega)⟩
  exact o.1.step T.ar.lay T.ar.data.w (o.1.env.keep g rd wr) wr fr

/-- The comparison keeps the public arguments, and leaves 1 or 0 at `W`. -/
theorem cmpRes {s : State} (o : One K W SP R N A D nl n tl s) :
    WP isa cmp s fun t => One K W SP R N A D nl n tl t ∧
      ∃ c : Bool, t.mem.readW (W + BitVec.ofNat 64 tagO) 64 = if c then 1#64 else 0#64 := by
  refine WP.mono (cmp_ok o.env T.ar.t1 T.ar.t16 o.sl.tl) fun t ⟨m, g, rd, wr⟩ => ?_
  have E : Env K W SP t := o.env.keep (fun r hr => g r
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)) rd wr
  have fr : Frame (mutR W SP D n) s.mem t.mem := by
    rw [m]
    refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)).sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., sub_wA (by decide)⟩
  refine ⟨o.step T.ar.lay T.ar.data.w E wr fr, decide (bytesAt s.mem W tl = bytesAt s.mem (W + BitVec.ofNat 64 t2O) tl),
    ?_⟩
  rw [m, Mem.readW_writeW_self64]; simp only [decide_eq_true_eq]

/-- The mask keeps the public arguments. -/
theorem mask_one {s : State} (o : One K W SP R N A D nl n tl s) {c : Bool}
    (hok : s.mem.readW (W + BitVec.ofNat 64 tagO) 64 = if c then 1#64 else 0#64) :
    WP isa mask s (One K W SP R N A D nl n tl) := by
  refine WP.mono (mask_ok o.env o.sl.data o.sl.len (T.ar.data.of_one o) hok) fun t ⟨E, _, wr, m⟩ => ?_
  have fr : Frame (mutR W SP D n) s.mem t.mem := by
    rw [m]
    refine (writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)).sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  exact o.step T.ar.lay T.ar.data.w E wr fr

variable (hw : s₀.wr = [⟨D, n⟩, ⟨W, 3584⟩]) (hw' : s₀'.wr = [⟨D, n⟩, ⟨W, 3584⟩])
include hw hw'

/-- `vg_aes_ocb_open` in two runs. -/
theorem open_rel (v : BlocksImpl) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') («open» (callees v)) fun _ _ => True := by
  have hDW := T.ar.data.w
  have hn : n ≤ 2 ^ 64 := Nat.le_of_lt T.ar.data.lt
  have fr := front_rel T hw hw' v false (.inr rfl)
  have rr := (rel_taintC [] [tgO] hDW hn (fun a b (h : True ∧ OneT K W SP R N A D nl n tl Tg a ∧
    OneT K W SP R N A D nl n tl Tg b) => ⟨h.2.1.1.env, h.2.2.1.env, h.2.1.1.sl, h.2.2.1.sl, h.2.1.1.wr, h.2.2.1.wr,
      fun _ h => (nomatch h), fun d hd => by
        simp only [List.mem_singleton] at hd; subst hd; exact ⟨by decide, by rw [h.2.1.2.1, h.2.2.2.1]⟩⟩)
    (c := recv) ⟨_, by taint_decide⟩).wp
    (F₁ := One K W SP R N A D nl n tl) (F₂ := One K W SP R N A D nl n tl)
    fun a b h => ⟨recv_one T h.2.1, recv_one T h.2.2⟩
  have cc := (rel_taintC [] [] hDW hn (fun a b (h : True ∧ One K W SP R N A D nl n tl a ∧
    One K W SP R N A D nl n tl b) => Both.of h.2.1 h.2.2) (c := cmp) ⟨_, by taint_decide⟩).wp
    (F₁ := fun (s : State) => One K W SP R N A D nl n tl s ∧ ∃ c : Bool, s.mem.readW (W + BitVec.ofNat 64 tagO) 64 =
      if c then 1#64 else 0#64)
    (F₂ := fun (s : State) => One K W SP R N A D nl n tl s ∧ ∃ c : Bool, s.mem.readW (W + BitVec.ofNat 64 tagO) 64 =
      if c then 1#64 else 0#64)
    fun a b h => ⟨cmpRes T h.2.1, cmpRes T h.2.2⟩
  have mm := (rel_taintC [] [] hDW hn (fun a b (h : True ∧ (One K W SP R N A D nl n tl a ∧
      ∃ c : Bool, a.mem.readW (W + BitVec.ofNat 64 tagO) 64 = if c then 1#64 else 0#64) ∧
    (One K W SP R N A D nl n tl b ∧
      ∃ c : Bool, b.mem.readW (W + BitVec.ofNat 64 tagO) 64 = if c then 1#64 else 0#64)) => Both.of h.2.1.1 h.2.2.1)
    (c := mask) ⟨_, by taint_decide⟩).wp
    (F₁ := One K W SP R N A D nl n tl) (F₂ := One K W SP R N A D nl n tl)
    fun a b h => ⟨mask_one T h.2.1.1 h.2.1.2.choose_spec, mask_one T h.2.2.1 h.2.2.2.choose_spec⟩
  have rs := rel_taintC [] [] hDW hn (fun a b (h : True ∧ One K W SP R N A D nl n tl a ∧
    One K W SP R N A D nl n tl b) => Both.of h.2.1 h.2.2) (c := .block ([ld .rax .r15 tagO] ++ restore))
    ⟨_, by taint_decide⟩
  unfold «open»
  exact RelCT.seq fr (RelCT.seq rr (RelCT.seq cc (RelCT.seq mm rs)))

end

/-- `vg_aes_ocb_open` is constant time. -/
theorem open_ct (v : BlocksImpl) : ConstantTime isa openX86_64.pre openX86_64.pub («open» (callees v)) :=
  fun s₁ s₂ _ _ _ _ h₁ h₂ hq e₁ e₂ => by
    have T := Two.of hq.1 (openArgs_of h₁) (openArgs_of h₂)
    obtain ⟨⟨q1, q2, q3, q4, q5, q6, q7, q8⟩, -⟩ := hq
    have hw₂ : s₂.wr = [⟨arg s₁ 0, (arg s₁ 1).toNat⟩, ⟨arg s₁ 4, 3584⟩] := by
      rw [h₂.2.1, q8 0 (by decide), q8 1 (by decide), q8 4 (by decide)]
    exact (open_rel T h₁.2.1 hw₂ v _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesOcb.X86_64
