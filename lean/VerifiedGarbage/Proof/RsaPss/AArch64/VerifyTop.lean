import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyBody
import VerifiedGarbage.Proof.RsaPss.AArch64.SignTop

/-!
# RSASSA-PSS verification on AArch64: the whole function

The restores and the frame's release (`restore_ok`), and the function
(`code_ok`): the calling convention, and the result as `RsaPss.verify` says
(`Post`).
-/

namespace VG.Proof.RsaPss.AArch64.Vfy

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_addSp PdChecked)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.RsaPss.AArch64.Sgn (stk fb preserved_saved saved_ho saved_offs)

/-- The restores, then the frame's release: the caller's registers are back,
and `x0` and memory are kept. -/
theorem restore_ok {s w : State} (hm : Mid s w) :
    WP isa (.block restore) w fun w' =>
      abiPreserved s (freed frameBytes w') ∧ (freed frameBytes w').gpr .x0 = w.gpr .x0 ∧
        (freed frameBytes w').mem = w.mem := by
  unfold restore
  refine wp_addSp (by decide) fun w₁ o₁ e₁ => ?_
  rw [hm.sp, BitVec.add_zero] at e₁
  refine WP.mono (Spill.restore_wp (b := .x16) (l := saved) (B := fb s) e₁ saved_ho (by decide)
    (fun p hp' => by
      rw [o₁.rd, o₁.wr, hm.wr]
      exact InRegions_append_cons (xs := w.rd) |>.mpr (.inl (Offset.contains_base _
        (by have := saved_offs p hp'; unfold frameBytes; omega) (by have := saved_offs p hp'; omega))))
    (by rw [o₁.mem]; exact hm.fr.sv)) fun w' hr => ⟨⟨fun r hr' => ?_, ?_, fun r hr' => ?_⟩, ?_, ?_⟩
  · simp only [freed]
    obtain ⟨p, hp', rfl⟩ := List.mem_map.mp (preserved_saved r hr')
    exact hr.gpr p hp'
  · simp only [freed]
    rw [hr.sp, o₁.sp, hm.sp, BitVec.sub_add_cancel]
  · simp only [freed]
    rw [hr.v, o₁.vcs r hr', hm.v r hr']
  · simp only [freed]
    rw [hr.other .x0 (by decide), o₁.get .x0]
  · simp only [freed]
    rw [hr.mem, o₁.mem]

/-- Verifying's result, if `pre` holds the modulus' values, and the calling
convention. -/
def Post (G : Spec.Mgf1.Hash) (s s' : State) : Prop :=
  abiPreserved s s' ∧ (Cons s → (s'.gpr .x0).setWidth 32 = if verifyOut G s then 1 else 0)

theorem code_ok {H : Hash} (hH : HashOK H) {G : Spec.Mgf1.Hash} (hGh : ∀ x, G.hash x = hH.SH.H.hash x)
    (hGl : G.len = H.D) (hG : Proof.Mgf1.Valid G) (c : PdChecked) {K : Nat} (hK : 16 ≤ K) (hcK : c.stack ≤ K)
    {s : State} (hp : PreV H.D K s) :
    WP isa (verifyPrecomputed H c.name c.code) s (Post G s) := by
  unfold verifyPrecomputed
  refine WP.alloc (by decide) (by have := hp.sp1; unfold stk at this; omega) ?_
  unfold verifyBody seqs seqs seqs
  refine WP.seq (WP.mono (prologue_ok hp (by simp [allocated]) (by simp [allocated]) (by simp [allocated])
    (by simp [allocated]) (fun r => by simp [allocated]) (fun r _ => by simp [allocated])) fun u hu => ?_)
  refine WP.seq (WP.mono (body_ok hH hGh hGl hG c hp hK hcK hu) fun t ⟨m, r⟩ => ?_)
  exact WP.mono (restore_ok m) fun w ⟨habi, hx0, _⟩ => ⟨habi, fun hc => by rw [hx0]; exact r hc⟩

end VG.Proof.RsaPss.AArch64.Vfy
