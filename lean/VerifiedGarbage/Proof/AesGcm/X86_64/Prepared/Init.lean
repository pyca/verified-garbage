import VerifiedGarbage.Proof.AesGcm.X86_64.InitP
import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Convert

/-! # Key setup with a prepared GHASH power table -/

namespace VG.Proof.AesGcm
open VG VG.X86_64
/-- The same internal setup contract, with the reviewed prepared representation. -/
def initPreparedX86_64 : Contract isa where
  pre := initPreL 1024
  post s s' := Spec.Gcm.KeyRepr s'.mem (s.gpr .rdx)
      (Spec.Aes.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) ∧
    Spec.Gcm.PreparedPowersRepr s'.mem (s.gpr .rdx)
  pub := initX86_64.pub
end VG.Proof.AesGcm

namespace VG.Proof.AesGcm.X86_64
open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- `vg_aes_gcm_init_prepared`. -/
theorem initPrepared_wp (v : GcmImpl) {s : State} (hp : Proof.AesGcm.initPreparedX86_64.pre s) :
    WP isa (Prepared.init v.callees) s fun s' =>
      gprPreserved s s' ∧ Proof.AesGcm.initPreparedX86_64.post s s' := by
  obtain ⟨L, pC, pW⟩ := IPLay.of hp
  have hl : (s.gpr .rsi).toNat = 16 ∨ (s.gpr .rsi).toNat = 24 ∨ (s.gpr .rsi).toNat = 32 :=
    hp.2.2.2.2.2.2.2.2.2.2.2.2
  refine initWith_wp v (by decide) hp fun s₅ D => ?_
  have pC₅ : Covers [⟨s.gpr .rdx, 1024⟩] s₅.wr := by rw [D.wr]; exact pC
  have pW₅ : Covers [⟨s.gpr .rcx, 2560⟩] s₅.wr := by rw [D.wr]; exact pW
  refine WP.seq (WP.mono (powStart_ok L pC₅ D.r13 D.r15 D.rsp) fun t I => ?_)
  refine WP.seq (WP.mono (powSteps_ok v L pC₅ pW₅ 47 (Nat.le_refl _) I) fun t' I' => ?_)
  have dS : ∀ r ∈ [(⟨s.gpr .rdx + BitVec.ofNat 64 256, 768⟩ : Region), ⟨s.gpr .rcx + BitVec.ofNat 64 512, 256⟩,
      below (s.gpr .rsp) 8], (savedR (s.gpr .rcx)).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ((L.cs.sub_left (Offset.sub_base _ (by decide))).sub_right (Offset.sub_base _ (by decide))).symm
    · exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
    · exact (L.ks.sub_right (Offset.sub_base _ (by decide))).symm
  have hret : t'.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
    rw [ret_kept I'.frame (fun r hr => ?_), D.ret]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact L.rc.sub_right (Offset.sub_base _ (by decide))
    · exact L.rs.sub_right (Offset.sub_base _ (by decide))
    · exact ret_below _
  have rawPost : Proof.AesGcm.initPrecomputedX86_64.post s t' := by
    have dC : ∀ {d : Nat}, d + 16 ≤ 256 → ∀ r ∈ [(⟨s.gpr .rdx + BitVec.ofNat 64 256, 768⟩ : Region),
        ⟨s.gpr .rcx + BitVec.ofNat 64 512, 256⟩, below (s.gpr .rsp) 8],
        (⟨s.gpr .rdx + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := by
      intro d hd r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Offset.disjoint _ (.inl hd) (by omega) (by decide)
      · exact (L.cs.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by decide))
      · exact (L.kc.sub_right (Offset.sub_base _ (by omega))).symm
    have hH : Spec.Gcm.ctxH t'.mem (s.gpr .rdx) = blockAt s₅.mem (s.gpr .rdx + BitVec.ofNat 64 240) :=
      blockAt_frame I'.frame (dC (by decide))
    refine ⟨keyRepr_frame I'.frame (by rw [length_bytesAt]; exact hl) (fun r hr => ?_) D.key,
      fun k hk => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Offset.base_disjoint _ (by decide) (by have := L.cw; omega)
      · exact (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide))
      · exact (L.kc.sub_right (Region.sub_prefix (by decide))).symm
    · rw [hH]; exact I'.pows k (by omega)

  simp only [List.cons_append, List.nil_append]
  rw [WP.block_cons_iff]
  let u := t'.setReg .rdi (t'.gpr .r13)
  refine ⟨u, rfl, ?_⟩
  rw [WP.block_append_iff]
  have udi : u.gpr .rdi = s.gpr .rdx := by simp only [u, gpr_setReg_self, I'.r13]
  have u15 : u.gpr .r15 = s.gpr .rcx := by simp [u, gpr_setReg, I'.r15]
  have usp : u.gpr .rsp = s.gpr .rsp := by simp [u, gpr_setReg, I'.rsp]
  have um : u.mem = t'.mem := rfl
  have pCu : Covers [⟨s.gpr .rdx, 1024⟩] u.wr := by
    rw [show u.wr = t'.wr from rfl, I'.wr]
    exact pC₅
  refine WP.mono (Gcm.X86_64.Prepared.convert_ok u
    (by rw [udi]; exact pCu _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)
    (by rw [udi]; exact L.cw) (by rw [udi, um]; exact rawPost.2))
    fun z ⟨powers, frame, g, rd, wr⟩ => ?_
  rw [udi] at powers frame
  rw [um] at frame
  have ds : ∀ r ∈ [⟨s.gpr .rdx + BitVec.ofNat 64 256, 768⟩], (savedR (s.gpr .rcx)).Disjoint r := by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact dS _ (List.mem_cons_self ..)
  have hret' : z.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
    rw [ret_kept frame (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact L.rc.sub_right (Offset.sub_base _ (by decide))), hret]
  refine WP.mono (exit_ok (by rw [g _ (by decide), u15]) (by rw [g _ (by decide), usp])
    (covers_left (by rw [wr, show u.wr = t'.wr from rfl, I'.wr]; exact pW₅))
    ((D.saved.frame I'.frame dS).frame frame ds) hret') fun s' ⟨hg, hm, _⟩ => ⟨hg, ?_⟩
  change Spec.Gcm.KeyRepr s'.mem (s.gpr .rdx) _ ∧ Spec.Gcm.PreparedPowersRepr s'.mem (s.gpr .rdx)
  rw [hm]
  exact ⟨keyRepr_frame frame (by rw [length_bytesAt]; exact hl) (fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact Offset.base_disjoint _ (by decide) (by have := L.cw; omega)) rawPost.1, powers⟩

end VG.Proof.AesGcm.X86_64
