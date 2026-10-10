import VerifiedGarbage.Proof.Ed25519.X86.Point32.Verified

/-!
# Calls of `vg_ed25519_r32_point_add` on x86 (32-bit)

`addCall` (`Impl/Ed25519/X86/Point32.lean`) pushes the working space at
`edi` as the argument of `vg_ed25519_r32_point_add` and calls it
(`addCall_ok`): from a working space of 8192 bytes apart from the 8 bytes of
stack the call uses (`Ctx`'s `stk`), it keeps what the field arithmetic
keeps (`Keep`), changes memory only in slots 0–3 and 8–15, bytes 864 to
1023 of the working space and that stack, and leaves in slots 0–3 the sum
of the points in slots 0–3 and 4–7, if slot 16 holds `d`. The call's
correctness is the function's own (`addFn_ok`, through `WP.callWith`).
-/

namespace VG.Proof.Ed25519.X86.Point32

open VG VG.X86 VG.Impl.Ed25519.X86 VG.Impl.Ed25519.X86.Point32 VG.Proof.Ed25519.X86
open VG.Impl.X25519.X86 (T)

theorem addFn_noSp : NoSp addFn := NoSp.of_all (by lit_decide)

theorem addFn_stack : stackUse addFn = 0 := rfl

theorem addCall_ok {x : BitVec 32} {s : State} (hc : Ctx x s) :
    WP isa addCall s fun t => Keep s t ∧ Frame (addW x ++ [callStk s]) s.mem t.mem ∧
      (env s.mem x 16 = Spec.Ed25519.d → point (env t.mem x) 0 1 2 3 =
        Spec.Ed25519.pointAdd (point (env s.mem x) 0 1 2 3) (point (env s.mem x) 4 5 6 7)) := by
  obtain ⟨hE, hdis⟩ := hc.stk rfl (Nat.le_refl _)
  have hfit := hc.fit
  have fit : 4 * [Reg.edi].length + 4 ≤ (s.gpr .esp).toNat := hE
  let rd : List Region := [below (s.gpr .esp) 4]
  let wr : List Region := [scR 8192 x]
  obtain ⟨e, he⟩ : ∃ e, e = (pushed [.edi] s).callEntry.withRegions rd wr := ⟨_, rfl⟩
  have esp_e : e.gpr .esp = s.gpr .esp - BitVec.ofNat 32 8 := by
    rw [he, State.withRegions_gpr]; exact callEntry_esp' [.edi] s
  have entry : Entry e x := by
    refine ⟨?_, hfit, by rw [he]; exact List.mem_singleton_self _, ?_⟩
    · rw [he, arg_withRegions, callEntry_arg fit (by decide) (by decide)]; exact hc.edi
    · rw [he, argAddr_withRegions, callEntry_argAddr0]
      exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _), Region.contains_self _ _⟩
  have hret : (⟨(e.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (scR 8192 x) := by
    rw [esp_e]
    exact (hdis.sub_right (Region.sub_prefix (len := 4) (len' := 8) (by decide))).symm
  let K : Contract isa :=
    { pre := fun t => t = e
      post := fun t t' => Frame (addW x) t.mem t'.mem ∧
        (env t.mem x 16 = Spec.Ed25519.d → point (env t'.mem x) 0 1 2 3 =
          Spec.Ed25519.pointAdd (point (env t.mem x) 0 1 2 3) (point (env t.mem x) 4 5 6 7))
      pub := fun _ _ => True }
  have hK : ∀ t, K.pre t → ∃ tr t', Exec isa addFn t tr t' ∧ abiPreserved t t' ∧ K.post t t' := by
    intro t ht
    change t = e at ht
    subst ht
    obtain ⟨tr, t', ex, hcs, -, -, hf, hv⟩ := addFn_ok entry
    refine ⟨tr, t', ex, ⟨hcs, ?_⟩, hf, hv⟩
    refine hf.readW (Region.contains_self _ _) (fun r hr => hret.sub_right ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [scR_eq]
    rcases hr with rfl | rfl | rfl
    · exact sub_sub hfit (Nat.zero_le _) (by decide) (by decide)
    · exact sub_sub hfit (Nat.zero_le _) (by decide) (by decide)
    · exact sub_sub hfit (Nat.zero_le _) (by simp only [T]; decide) (by simp only [T]; decide)
  have cov : ∀ ts : List Region, scR 8192 x ∈ ts → Covers wr ts := fun ts h => Covers.of_mem fun r hr => by
    rw [List.mem_singleton.mp hr]; exact h
  refine WP.callWith (k := K) (rd := rd) (wr := wr) hK addFn_noSp (by decide) (by decide)
    (by rw [addFn_stack]; exact hE)
    ⟨he.symm, Covers.append_left (Covers.of_mem fun r hr => by
        rw [List.mem_singleton.mp hr]; exact List.mem_append_right _ List.mem_cons_self)
        (cov _ (List.mem_append_right _ (List.mem_cons_of_mem _ hc.wr))),
      cov _ (List.mem_cons_of_mem _ hc.wr)⟩
    fun s' hrd hwr hcs _ ⟨s₂, hm2, hf2, hv⟩ => ?_
  rw [← he] at hf2 hv
  -- Memory: the call's stack, then the function's writes.
  have fs : Frame [callStk s] s.mem e.mem := by
    rw [he, State.withRegions_mem]; exact callEntry_frame (rs := [.edi]) fit (by decide)
  have fenv : env e.mem x = env s.mem x := funext fun i =>
    congrArg VG.Proof.X25519.toFe (fe_frame fun k hk => wd_frame fs fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hdis.sub_left (by
        rw [scR_eq]; exact sub_sub hfit (Nat.zero_le _) (by simp only [offset]; omega)
          (by simp only [offset]; omega)))
  refine ⟨⟨hcs .esi (by decide), hcs .edi (by decide), hcs .esp (by decide), hrd, hwr⟩, ?_, ?_⟩
  · rw [← hm2]
    exact (fs.mono fun r hr => by
      rw [List.mem_singleton.mp hr]; simp) |>.trans (hf2.mono fun r hr => List.mem_append_left _ hr)
  · rw [← hm2, ← fenv]
    exact hv

end VG.Proof.Ed25519.X86.Point32

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86
open VG.Impl.X25519.X86 (T)

/-- A call of `vg_ed25519_r32_point_add`, as the code that calls it states
what it keeps (`CallKeep`): the sum in slots 0–3, and slots 16 on as they
were. -/
theorem pointAddCall_ok {s : State} {base : BitVec 32} (hs : Ctx base s)
    (hd : env s.mem base 16 = Spec.Ed25519.d) :
    WP isa Point32.addCall s fun t =>
      CallKeep base s t ∧ point (env t.mem base) 0 1 2 3 =
        Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) (point (env s.mem base) 4 5 6 7) ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i := by
  have hfit := hs.fit
  refine WP.mono (Point32.addCall_ok hs) fun t ⟨hk, hf, hv⟩ => ⟨⟨hk, hf.sub fun r hr => ?_⟩, hv hd, fun i hi => ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., sub_sub hfit (Nat.le_refl _) (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., sub_sub hfit (by decide) (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., sub_sub hfit (by simp only [T]; decide) (by simp only [T]; decide)
        (by simp only [T]; decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩
  · have hi' := i.isLt
    apply congrArg VG.Proof.X25519.toFe
    refine fe_frame fun k hk => wd_frameS hs (rs := Point32.addW base) hf
      (by simp only [offset]; omega) fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact sub_disj (by simp only [offset]; omega) (by omega) (.inr (by simp only [offset]; omega))
    · exact sub_disj (by simp only [offset]; omega) (by omega) (.inr (by simp only [offset]; omega))
    · exact sub_disj (by simp only [offset]; omega) (by simp only [T]; omega)
        (.inl (by simp only [offset, T]; omega))

end VG.Proof.Ed25519.X86
