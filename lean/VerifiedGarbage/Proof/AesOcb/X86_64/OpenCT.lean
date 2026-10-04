import VerifiedGarbage.Proof.AesOcb.X86_64.SealCT
import VerifiedGarbage.Proof.AesOcb.X86_64.Open

/-!
# AES-OCB on x86-64: `vg_aes_ocb_open` is constant time

Untrusted: everything here is checked by Lean. As `seal` (`pre_rel`,
`bodyOpen_rel`, `tag_rel`), then the comparison, the mask and `restore`,
which pass the taint analysis from the public slots: the comparison's
result is a value, not a branch.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (BlocksImpl)

section
variable {s₀ s₀' : State} {K W SP N A D : Addr} {R nl al n tl : Nat} (T : Two s₀ s₀' K W SP N A D R nl al n tl)
include T

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

/-- `vg_aes_ocb_open` in two runs. -/
theorem open_rel (v : BlocksImpl) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') («open» (callees v)) fun _ _ => True := by
  have L := T.ar.lay
  have hDW := T.ar.data.w
  have hn : n ≤ 2 ^ 64 := Nat.le_of_lt T.ar.data.lt
  have pre := (pre_rel T v).wp (F₁ := Pre K W SP N A D R nl al n tl s₀) (F₂ := Pre K W SP N A D R nl al n tl s₀')
    fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨pre_wp' v T.ar T.sp T.dd T.nn T.ww T.tt T.di T.si T.dx T.cx T.r8 T.r9,
        pre_wp' v T.ar' T.sp' T.dd' T.nn' T.ww' T.tt' T.di' T.si' T.dx' T.cx' T.r8' T.r9'⟩
  have body1 : ∀ {σ s : State}, Args σ K W SP N A D R nl al n tl → Pre K W SP N A D R nl al n tl σ s →
      WP isa (body (callees v) false) s (One K W SP R N A D nl n tl) := fun Ar P =>
    WP.mono (bodyOpen_ok v L P.env Ar.rounds P.slots.rounds (Ar.data.of_eq P.rd P.wr) P.slots.data P.slots.len P.ofs
      P.o0 P.ck (by rw [P.l0, P.lstar])) fun t B =>
      (brun_of Ar P).1.step L hDW B.env B.wr (bodyR_mut B.frame)
  have bb := (bodyOpen_rel v L T.ar.rounds hDW T.ar.data.lt
    (P := fun a b => True ∧ Pre K W SP N A D R nl al n tl s₀ a ∧ Pre K W SP N A D R nl al n tl s₀' b)
    fun a b h => ⟨brun_of T.ar h.2.1, brun_of T.ar' h.2.2⟩).wp
    (F₁ := One K W SP R N A D nl n tl) (F₂ := One K W SP R N A D nl n tl)
    fun a b h => ⟨body1 T.ar h.2.1, body1 T.ar' h.2.2⟩
  have tt := (tag_rel v L T.ar.rounds hDW hn (d := t2O) (.inr rfl)
    (P := fun a b => True ∧ One K W SP R N A D nl n tl a ∧ One K W SP R N A D nl n tl b) fun _ _ h => h.2).wp
    (F₁ := One K W SP R N A D nl n tl) (F₂ := One K W SP R N A D nl n tl)
    fun a b h => ⟨tag_one T v (.inr rfl) h.2.1, tag_one T v (.inr rfl) h.2.2⟩
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
  exact Proof.AesCcm.X86_64.rel_assoc3 (RelCT.seq pre (RelCT.seq bb (RelCT.seq tt (RelCT.seq cc (RelCT.seq mm rs)))))

end

/-- `vg_aes_ocb_open` is constant time. -/
theorem open_ct (v : BlocksImpl) : ConstantTime isa openX86_64.pre openX86_64.pub («open» (callees v)) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (open_rel (Two.of h₁ h₂ hq.1) v _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesOcb.X86_64
