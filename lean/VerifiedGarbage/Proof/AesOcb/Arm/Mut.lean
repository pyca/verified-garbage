import VerifiedGarbage.Proof.AesOcb.Arm.Calls

/-!
# AES-OCB on ARMv7: what the pieces write

Untrusted: everything here is checked by Lean. The pieces after the entry
write only `W` but for our caller's saved registers, the stack below `SP`
and the data (`mutR`), which miss the key context, the nonce, the
associated data, the tag (`open`'s received one), the stack arguments and the
saved registers: those are the same in every state after the entry
(`sched_mut`, `lstar_mut`, `bytes_mut`, `Args.mut`, `saved_mut`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm
open VG.Spec.Ocb (Block blockAtMem)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (below)

/-- What the pieces after the entry write. -/
abbrev mutR (p : Prm) : List Region :=
  [⟨State.addr p.W, 128⟩, ⟨State.addr p.W + BitVec.ofNat 64 164, 2396⟩, below p.SP, ⟨State.addr p.D, p.n⟩]

/-- Our caller's saved registers in `W`. -/
abbrev savedR (p : Prm) : Region := ⟨State.addr p.W + BitVec.ofNat 64 128, 36⟩

section
variable {p : Prm} (L : Lay p)
include L

omit L in
/-- A part of `W` but the saved registers is in `mutR`. -/
theorem w_mut (_L : Lay p) {a l : Nat} (h : a + l ≤ 128 ∨ (164 ≤ a ∧ a + l ≤ 2560)) :
    ∃ r' ∈ mutR p, Region.Sub ⟨State.addr p.W + BitVec.ofNat 64 a, l⟩ r' := by
  rcases h with h | h
  · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ h⟩
  · exact ⟨⟨State.addr p.W + BitVec.ofNat 64 164, 2396⟩, by simp, Offset.sub _ h.1 (by omega)⟩

omit L in
theorem below_mut (_L : Lay p) : ∃ r' ∈ mutR p, Region.Sub (below p.SP) r' := ⟨_, by simp, fun _ h => h⟩

omit L in
theorem data_mut (_L : Lay p) {a l : Nat} (h : a + l ≤ p.n) :
    ∃ r' ∈ mutR p, Region.Sub ⟨State.addr p.D + BitVec.ofNat 64 a, l⟩ r' :=
  ⟨_, by simp, Offset.sub_base _ h⟩

omit L in
/-- A region apart from `W`, the stack below `SP` and the data misses `mutR`. -/
theorem disj_mut (_L : Lay p) {r : Region} (hw : r.Disjoint ⟨State.addr p.W, 2560⟩) (hb : (below p.SP).Disjoint r)
    (hd : r.Disjoint ⟨State.addr p.D, p.n⟩) : ∀ r' ∈ mutR p, r.Disjoint r' := by
  intro r' hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hw.sub_right (Region.sub_prefix (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hb.symm
  · exact hd

theorem saved_mut : ∀ r ∈ mutR p, (savedR p).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · simpa using L.w_w (a := 128) (n := 36) (d := 0) (k := 128) (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.bw' (by decide)).symm
  · exact (L.d_w' (by decide)).symm

theorem args_mut : ∀ r ∈ mutR p, (argR p.SP).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.w_args.symm.sub_right (Region.sub_prefix (by decide))
  · exact L.args_w' (by decide)
  · exact L.args_below
  · exact L.d_args.symm

theorem k_mut : ∀ r ∈ mutR p, (⟨State.addr p.K, 256⟩ : Region).Disjoint r :=
  disj_mut L L.k_w L.bk L.k_d

theorem sched_mut {m m' : Mem} (h : Frame (mutR p) m m') : sched p m' = sched p m :=
  Proof.Cmac.bytesAt_frame h (fun r hr => (k_mut L r hr).sub_left
    (Region.sub_prefix (by have := L.rounds_le; omega))) (by have := L.rounds_le; omega)

theorem lstar_mut {m m' : Mem} (h : Frame (mutR p) m m') :
    Spec.Ocb.ctxLstar m' (State.addr p.K) = Spec.Ocb.ctxLstar m (State.addr p.K) := by
  unfold Spec.Ocb.ctxLstar
  exact Proof.Ocb.blockAtMem_frame h fun r hr => (k_mut L r hr).sub_left (Offset.sub_base _ (by decide))

theorem nonce_mut {m m' : Mem} (h : Frame (mutR p) m m') :
    bytesAt m' (State.addr p.N) p.nl = bytesAt m (State.addr p.N) p.nl :=
  Proof.Cmac.bytesAt_frame h (disj_mut L L.n_w L.bn L.n_d) (by have := L.nl15; omega)

theorem aad_mut {m m' : Mem} (h : Frame (mutR p) m m') :
    bytesAt m' (State.addr p.A) p.al = bytesAt m (State.addr p.A) p.al :=
  Proof.Cmac.bytesAt_frame h (disj_mut L L.a_w L.ba L.a_d) (by have := L.al_lt; omega)

theorem tag_mut {m m' : Mem} (h : Frame (mutR p) m m') :
    bytesAt m' (State.addr p.T) p.tl = bytesAt m (State.addr p.T) p.tl :=
  Proof.Cmac.bytesAt_frame h (disj_mut L L.t_w L.bt L.t_d) (by have := L.tl16; omega)

/-- A block of the associated data. -/
theorem aadBlk_mut {m m' : Mem} (h : Frame (mutR p) m m') {k : Nat} (hk : k + 16 ≤ p.al) :
    blockAtMem m' (State.addr p.A + BitVec.ofNat 64 k) = blockAtMem m (State.addr p.A + BitVec.ofNat 64 k) :=
  Proof.Ocb.blockAtMem_frame h fun r hr => (disj_mut L L.a_w L.ba L.a_d r hr).sub_left (Offset.sub_base _ hk)

theorem Args.mut {m m' : Mem} (A : Args p m) (h : Frame (mutR p) m m') : Args p m' :=
  A.frame L h (args_mut L)

end

end VG.Proof.AesOcb.Arm
