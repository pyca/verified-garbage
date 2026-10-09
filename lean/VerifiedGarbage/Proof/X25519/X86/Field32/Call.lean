import VerifiedGarbage.Proof.X25519.X86.Field32.Verified

/-!
# Calls of `vg_gf25519_r32_pow250` on x86 (32-bit)

`pow250Call` (`Impl/X25519/X86/Field32.lean`) pushes the working space at
`edi` as the argument of `vg_gf25519_r32_pow250` and calls it
(`pow250Call_ok`): from a working space of 8192 bytes apart from the 8
bytes of stack the call uses (`Ctx`'s `stk`), it keeps what the field
arithmetic keeps (`Keep`), changes memory only in bytes 512 to 1023 of the
working space and that stack, and leaves `a^(2^250 - 1)` at byte 544 and
`a^11` at byte 512, for `a` the element at byte 128. The call's correctness
is the function's own (`pow250Fn_ok`, through `WP.callWith`).
-/

namespace VG.Proof.X25519.X86.Field32

open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.X25519.X86.Field32 VG.Proof.X25519.X86 VG.Spec.X25519
open VG.Proof.X25519 (pw)

theorem pow250Fn_noSp : NoSp pow250Fn := NoSp.of_all (by lit_decide)

theorem pow250Fn_stack : stackUse pow250Fn = 0 := rfl

/-- A region of the working space of 8192 bytes, apart from the stack a call uses. -/
theorem sub_apart {x : BitVec 32} {s : State} (hc : Ctx 8192 x s) {d n : Nat} (hd : d + n ≤ 8192) (hn : 0 < n) :
    (sub x d n).Disjoint (callStk s) :=
  (hc.stk rfl (Nat.le_refl _)).2.sub_left (by
    rw [scR_eq]; exact sub_sub hc.fit (Nat.zero_le _) (by omega) (by omega))

theorem pow250Call_ok {x : BitVec 32} {s : State} (hc : Ctx 8192 x s) :
    WP isa pow250Call s fun t => Keep s t ∧ Frame [sub x 512 512, callStk s] s.mem t.mem ∧
      F t.mem x E1 = pw (F s.mem x Spec.X25519.Field32.aAt) (2 ^ 250 - 1) ∧
      F t.mem x E0 = pw (F s.mem x Spec.X25519.Field32.aAt) 11 := by
  obtain ⟨hE, hdis⟩ := hc.stk rfl (Nat.le_refl _)
  have hfit8 := hc.fit
  have hfit : x.toNat + 4096 ≤ 2 ^ 32 := by omega
  have fit : 4 * [Reg.edi].length + 4 ≤ (s.gpr .esp).toNat := hE
  let rd : List Region := [below (s.gpr .esp) 4]
  let wr : List Region := [scR 4096 x]
  obtain ⟨e, he⟩ : ∃ e, e = (pushed [.edi] s).callEntry.withRegions rd wr := ⟨_, rfl⟩
  have esp_e : e.gpr .esp = s.gpr .esp - BitVec.ofNat 32 8 := by
    rw [he, State.withRegions_gpr]; exact callEntry_esp' [.edi] s
  have sub4 : Region.Sub (scR 4096 x) (scR 8192 x) := Region.sub_prefix (by decide)
  have dis4 : (scR 4096 x).Disjoint (callStk s) := hdis.sub_left sub4
  have entry : Entry e x := by
    refine ⟨?_, hfit, by rw [he]; exact List.mem_singleton_self _, ?_⟩
    · rw [he, arg_withRegions, callEntry_arg fit (by decide) (by decide)]; exact hc.edi
    · rw [he, argAddr_withRegions, callEntry_argAddr0]
      exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _), Region.contains_self _ _⟩
  let K : Contract isa :=
    { pre := fun t => t = e
      post := fun t t' => Frame (powW x) t.mem t'.mem ∧
        F t'.mem x E1 = pw (F t.mem x Spec.X25519.Field32.aAt) (2 ^ 250 - 1) ∧
        F t'.mem x E0 = pw (F t.mem x Spec.X25519.Field32.aAt) 11
      pub := fun _ _ => True }
  have hret : (⟨(e.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (scR 4096 x) := by
    rw [esp_e]
    exact (dis4.sub_right (Region.sub_prefix (len := 4) (len' := 8) (by decide))).symm
  have hK : ∀ t, K.pre t → ∃ tr t', Exec isa pow250Fn t tr t' ∧ abiPreserved t t' ∧ K.post t t' := by
    intro t ht
    change t = e at ht
    subst ht
    obtain ⟨tr, t', ex, hcs, -, -, hf, h1, h0⟩ := pow250Fn_ok entry
    refine ⟨tr, t', ex, ⟨hcs, ?_⟩, hf, h1, h0⟩
    refine hf.readW (Region.contains_self _ _) (fun r hr => hret.sub_right ?_) (by decide)
    rw [List.mem_singleton.mp hr, scR_eq]
    exact sub_sub hfit (Nat.zero_le _) (by decide) (by decide)
  have cov4 : ∀ ts : List Region, scR 8192 x ∈ ts → Covers wr ts := fun ts h =>
    Covers.of_sub fun r hr => ⟨scR 8192 x, h, 0, by
      rw [List.mem_singleton.mp hr]; exact (BitVec.add_zero _).symm, by
      rw [List.mem_singleton.mp hr]; show 0 + 4096 ≤ 8192; decide⟩
  refine WP.callWith (k := K) (rd := rd) (wr := wr) hK pow250Fn_noSp (by decide) (by decide)
    (by rw [pow250Fn_stack]; exact hE)
    ⟨he.symm, Covers.append_left (Covers.of_mem fun r hr => by
        rw [List.mem_singleton.mp hr]; exact List.mem_append_right _ List.mem_cons_self)
        (cov4 _ (List.mem_append_right _ (List.mem_cons_of_mem _ hc.wr))),
      cov4 _ (List.mem_cons_of_mem _ hc.wr)⟩
    fun s' hrd hwr hcs _ ⟨s₂, hm2, hf2, h1, h0⟩ => ?_
  rw [← he] at hf2 h1 h0
  -- Memory: the call's stack, then the function's writes.
  have fs : Frame [callStk s] s.mem e.mem := by
    rw [he, State.withRegions_mem]; exact callEntry_frame (rs := [.edi]) fit (by decide)
  have fstk : ∀ q, q + 32 ≤ 4096 → F e.mem x q = F s.mem x q := fun q hq =>
    congrArg VG.Proof.X25519.toFe (fe_frame fun k hk => wd_frame fs fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact dis4.sub_left (by rw [scR_eq]; exact sub_sub hfit (Nat.zero_le _) (by omega) (by omega)))
  refine ⟨⟨hcs .esi (by decide), hcs .edi (by decide), hcs .esp (by decide), hrd, hwr⟩, ?_, ?_, ?_⟩
  · rw [← hm2]
    exact (fs.mono fun r hr => by
      rw [List.mem_singleton.mp hr]; simp) |>.trans (hf2.mono fun r hr => by
      rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..)
  · rw [← hm2, h1, fstk _ (by decide)]
  · rw [← hm2, h0, fstk _ (by decide)]

end VG.Proof.X25519.X86.Field32
