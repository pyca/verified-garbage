import VerifiedGarbage.Proof.Weierstrass.X86.InvWord

/-! # A public-count loop of word divsteps -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86 VG.Proof.Mont

def wordClob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi]

theorem wordSteps_ok {s : State} {base : Addr} {size t n : Nat} (hs : Scr s base size)
    (ht : t + 28 ≤ size) (hn : 1 ≤ n) (hn32 : n < 2 ^ 32) :
    WP isa (wordSteps t n) s fun u =>
      wordState u.mem base t = Divstep.W32.wsteps n (wordState s.mem base t) ∧
      Keeps wordClob s u ∧ Outside base t 28 s.mem u.mem := by
  unfold wordSteps
  refine WP.seq (wp_movS rfl fun s₁ U₁ _ => WP.block_nil ?_)
  let Inv := fun j u =>
    Scr u base size ∧ u.gpr .esi = BitVec.ofNat 32 j ∧
    wordState u.mem base t = Divstep.W32.wsteps (n - j) (wordState s.mem base t) ∧
    Keeps wordClob s u ∧ Outside base t 28 s.mem u.mem
  refine countLoop_ok (Inv := Inv) (n := n) ?_ ?_ hn ?_
  · intro j v hj hjn hI
    obtain ⟨hv, ev, Wv, Kv, Ov⟩ := hI
    refine wp_decCounter hj ev fun v₁ E₁ K₁ M₁ => ?_
    have hv₁ := hv.of_keeps K₁ (by decide)
    refine WP.block_append (WP.mono (wordStep_ok hv₁ ht) fun v₂ ⟨W₂, K₂, O₂⟩ => ?_)
    have e₂ : v₂.gpr .esi = BitVec.ofNat 32 (j - 1) := by rw [K₂.1 _ (by decide), E₁]
    refine wp_testCounter (by omega) e₂ fun u F hz => WP.block_nil ⟨?_, hz⟩
    refine ⟨(hv₁.of_keeps K₂ (by decide)).of_keeps (F.keeps []) (by decide),
      by rw [F.gpr]; exact e₂, ?_,
      (((Kv.trans (K₁.mono (by decide))).trans (K₂.mono (by decide))).trans (F.keeps _)), ?_⟩
    · rw [F.mem, W₂, M₁, Wv, show n - (j - 1) = (n - j) + 1 by omega,
        Divstep.W32.wsteps_succ]
    · intro x hx
      rw [F.mem, O₂ x hx, M₁, Ov x hx]
  · intro u ⟨_, _, W, K, O⟩
    exact ⟨by simpa only [Nat.sub_zero] using W, K, O⟩
  · refine ⟨hs.of_keeps U₁.keeps (by decide), U₁.gpr, ?_, U₁.keeps.mono (by decide), ?_⟩
    · rw [U₁.mem, Nat.sub_self]; rfl
    · rw [U₁.mem]; exact fun _ _ => rfl

end VG.Proof.Weierstrass.X86.Inv
