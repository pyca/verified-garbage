import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.LoopStep
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.FinalCommon
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.HashBuffer

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block)
open VG.Impl.Gcm.X86_64.StitchAvx8 (hash8 prepare finish)

theorem finalEnc_ok {s₀ s : State} {P : Nat → Block} {g : Nat}
    (hp : SPre s₀) (hlaw : HashLaw s₀ P) (h : LoopInv s₀ P false g s) (hn : nb s₀ = g + 16) :
    WP isa (.block (hash8 ++ (List.range 8).flatMap (fun i => prepare (8 + i)) ++ hash8 ++ finish)) s
      (EPost s₀) := by
  have hd : DataInv s₀ (nb s₀) s.mem := by rw [hn]; exact h.core.data
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (hashBuffer_ok hp hlaw h.core.env h.buffered) fun t ⟨htE, htY, htF⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (prepareRun_ok hp t htE 8 (by decide)
    (fun i hi => by
      rw [htF.gpr, h.core.addr]
      exact in_rdwr (in_sub hp.d_in (by omega)))
    (fun i hi => by
      rw [htF.gpr, h.core.addr]
      exact hp.d_p.sub_left (Offset.sub_base (dp s₀) (d := 16 * (g + (8 + i))) (n := 16)
        (k := 16 * nb s₀) (by omega))) 8 (by decide)) fun u ⟨huE, huB, huF, huM⟩ => ?_
  have huB' : ∀ i < 8, u.mem.readW (hashAddr s₀ i) 128 = window s₀ false (g + 8) i := by
    intro i hi
    rw [huB i hi, htF.mem, htF.gpr, h.core.addr, hd _ (by omega), ite_eq_left (by omega : g + (8 + i) < nb s₀)]
    simp [window, hashBlock, Nat.add_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (hashBuffer_ok hp hlaw huE huB') fun v ⟨hvE, hvY, hvF⟩ => ?_
  refine finish_complete hp false hvE ?_ ?_ ?_
  · rw [hvF.mem]
    have htD : DataInv s₀ (nb s₀) t.mem := htF.mem ▸ hd
    exact htD.frame huM (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact hp.d_p.sub_right (Offset.sub_base (pp s₀) (d := 512) (n := 128) (k := 1024) (by decide)))
  · rw [hvF.gpr, huF.gpr .r8 (by decide), htF.gpr, h.core.counter, hn]
    rfl
  · rw [hvY, huF.lane, htY, h.core.hash]
    change Spec.Gcm.ghashFrom (hk s₀)
      (Spec.Gcm.ghashFrom (hk s₀) (hashPrefix s₀ false g) ((List.range 8).map (fun i => hashBlock s₀ false (g + i))))
      ((List.range 8).map (fun i => hashBlock s₀ false (g + 8 + i))) = _
    simp only [hashPrefix]
    rw [← ghash_append8 (hk s₀) (y₀ s₀) (hashBlock s₀ false) g,
      ← ghash_append8 (hk s₀) (y₀ s₀) (hashBlock s₀ false) (g + 8)]
    rw [hn]

end VG.Proof.Gcm.X86_64.StitchAvx8
