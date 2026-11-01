module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.Partial
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Run

-- separate module: restore the public source arguments after nonce/AAD processing.
/-! # The split-seal body -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.SealSplit
open VG VG.PPC64LE
open VG.Proof.AesGcm.PPC64LE.SealFused


def sourceState (s : State) : State :=
  (s.write .r7 (s.mem.readW (s.gpr .r31+112) 64)).write .r8 (s.mem.readW (s.gpr .r31+120) 64)


theorem source_ok {V : Reg → BitVec 64} {sp : Addr} {s : State} (he : Env V sp s) :
    WP isa (.block Impl.AesGcm.PPC64LE.SealSplit.sourceArgs) s (· = sourceState s) := by
  have h112 : InRegions (s.rd++s.wr) (s.gpr .r31+BitVec.ofNat 64 112) 8 := by
    rw [he.r31]
    exact in_left (in_off he.perm.w (by decide) (by decide))
  have h120 : InRegions (s.rd++s.wr) (s.gpr .r31+BitVec.ofNat 64 120) 8 := by
    rw [he.r31]
    exact in_left (in_off he.perm.w (by decide) (by decide))
  let u := s.write .r7 (s.mem.readW (s.gpr .r31+112#64) 64)
  have h120' : InRegions (u.rd++u.wr) (u.gpr .r31+120#64) 8 := h120
  rw [Impl.AesGcm.PPC64LE.SealSplit.sourceArgs]
  refine WP.block_cons_iff.mpr ⟨u,exec_load_d (n := .r31) (off := 112) (by decide) ⟨by decide,by decide⟩ h112,?_⟩
  refine WP.block_cons_iff.mpr ⟨_,exec_load_d (s := u) (n := .r31) (off := 120) (by decide) ⟨by decide,by decide⟩ h120',?_⟩
  exact WP.block_nil rfl



theorem source_env {V : Reg → BitVec 64} {sp : Addr} {s : State} (he : Env V sp s) :
    Env V sp (sourceState s) := by
  have hk : Keep [.r7,.r8] s (sourceState s) := by
    obtain ⟨_,_,_,eq,hk⟩ := WP.keep [.r7,.r8] (source_ok he) (by decide) (by decide)
    subst eq
    exact hk
  exact he.keep (fun r hr => hk.gpr (by
    have hp : ∀ r ∈ frozen, r∉[Reg.r7,.r8] := by decide
    exact hp r hr)) rfl hk.2.1 hk.2.2


theorem body_ok [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {V : Reg → BitVec 64} {sp S : Addr} {count R : Nat} {s : State} {a : List Byte}
    (L : Lay (V .r29) (V .r30) (V .r31)) (he : Env V sp s)
    (hd : DataW (V .r29) (V .r30) (V .r31) s (V .r27) (V .r23).toNat)
    (lay : Call.Layout V sp S count (sourceState s)) (hR : V .r28=BitVec.ofNat 64 R) (hv : R=10 ∨ R=12 ∨ R=14)
    (ha : (V .r22).toNat=a.length)
    (hab : Proof.Gcm.Absorbed s.mem (V .r30+16) (V .r30+32) (Spec.Gcm.ctxH s.mem (V .r29))
      (a++Spec.Gcm.zeros (Spec.Gcm.padLen a.length))) :
    WP isa Impl.AesGcm.PPC64LE.SealSplit.body s
      (fun t => BodyOutWith V sp R (Spec.Gcm.ctxH s.mem (V .r29)) a s.mem
        (Spec.Aes.bytesAt s.mem S count ++ (Spec.Aes.bytesAt s.mem (V .r27) (V .r23).toNat).drop count)
        t [⟨sp+96,8⟩]) := by
  refine WP.ite (decide ((V .r23).toNat=0))
    (eval_zero (by simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using he.fr .r23 (by decide)) (V .r23).isLt) (fun hz => ?_) (fun hn => ?_)
  · have hz : (V .r23).toNat=0 := by simpa using hz
    have hc : count=0 := by have := lay.bound; omega
    refine WP.mono (smallBody_ok L he hd hR hv ha hab) fun t ht => ?_
    change BodyOutWith _ _ _ _ _ _ _ _ at ht
    simp only [hc,Spec.Aes.bytesAt,List.range_zero,List.map_nil,List.nil_append,List.drop_zero] at ht ⊢
    exact ⟨ht.env,ht.ciphertext,ht.tag,ht.frame.mono (fun _ hr => List.mem_append_left _ hr)⟩
  · have hn : 0<(V .r23).toNat := by
      have hh : (V .r23).toNat≠0 := by simpa using hn
      omega
    refine WP.seq (WP.mono (source_ok he) fun u hu => ?_)
    subst u
    exact partial_ok L (source_env he) (hd.of_eq rfl rfl) lay hR hv ha hn hab

end VG.Proof.AesGcm.PPC64LE.SealSplit
