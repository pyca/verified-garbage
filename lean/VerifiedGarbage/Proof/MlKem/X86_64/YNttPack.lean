module

public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.Proof.MlKem.X86_64.YNttLay
import VerifiedGarbage.Proof.MlKem.X86_64.MulAvx2
import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
import VerifiedGarbage.Proof.MlKem.X86_64.VPack
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on x86-64: AVX2 constants and packing

The packing of the lanes of two registers into words (`lanes_pack2`), and
the constants `yconsts` loads (`yconsts_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-! ## Packing -/

/-- The eight coefficients of a reduced polynomial, four at `coeffAddr p j`
and four at `coeffAddr p j'`, as the words `packssdw` makes of them. -/
theorem lanes_pack2 {m : Mem} {p : Addr} {F : Poly} (hF : PolyIs m p F) {j j' : Nat} (hj : j + 4 ≤ 256)
    (hj' : j' + 4 ≤ 256) :
    Lanes (XBinOp.eval .packssdw (m.readW (coeffAddr p j) 128) (m.readW (coeffAddr p j') 128))
      (fun e => if e < 4 then F[j + e]! else F[j' + (e - 4)]!) := fun e he => by
  have hc : ∀ k, k < 256 → (coeffAt m p k).toNat = (F[k]!).val := fun k hk =>
    polyIs_toNat hF (by rw [n_eq]; exact hk)
  rw [word_packssdw_small _ _ he (fun k hk => by
      rw [dword_readW _ _ hk, coeffAddr_off, ← coeffAt_eq, hc _ (by bdd_omega)]; have := val_lt F[j + k]!; omega)
    (fun k hk => by
      rw [dword_readW _ _ hk, coeffAddr_off, ← coeffAt_eq, hc _ (by bdd_omega)]; have := val_lt F[j' + k]!; omega)]
  split
  · rw [dword_readW _ _ (by bdd_omega), coeffAddr_off, ← coeffAt_eq, hc _ (by bdd_omega)]; dsimp only; rw [ifp ‹_›]
  · rw [dword_readW _ _ (by bdd_omega), coeffAddr_off, ← coeffAt_eq, hc _ (by bdd_omega)]; dsimp only; rw [ifn ‹_›]

/-! ## The prologue and the epilogue -/

theorem yconsts_ok (s : State) :
    WP isa (.block yconsts) s fun s' => YConsts s' ∧ s'.mem = s.mem ∧ Keep [.rax] s s' := by
  simp only [yconsts]
  rw [WP.block_append_iff]
  refine WP.mono (yconst_ok .xmm15 _ s) fun s1 ⟨q1, k1, m1, _, _⟩ => ?_
  refine WP.mono (yconst_ok .xmm14 _ s1) fun s2 ⟨q2, k2, m2, _, o2⟩ => ?_
  refine ⟨fun l hl => ⟨?_, ?_⟩, by rw [m2, m1], (k1.trans k2).mono (by simp)⟩
  · rw [State.proj_xmm, o2 _ (by decide) l hl, q1 l hl]; decide
  · rw [State.proj_xmm, q2 l hl]; decide

end VG.Proof.MlKem.X86_64
