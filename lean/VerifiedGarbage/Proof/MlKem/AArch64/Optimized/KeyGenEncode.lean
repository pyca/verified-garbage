module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenTables
public import VerifiedGarbage.Proof.MlKem.AArch64.KgEnd
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Encode the precomputed secret polynomials without resampling them -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Impl.MlKem.AArch64.Noise (noiseOff)
variable {P : KemLay}

structure EncodeInv (P : KemLay) (s₀ : State) (mB mN : Mem) (v : BitVec 64) (j : Nat) (s : State) : Prop where
  c : CInv P s₀ mB v s
  sp : ∀ j < P.k, PolyIs s.mem (kA s₀ 3+BitVec.ofNat 64 (sOff P j)) (KPke.kgS P.params (dB s₀) j)
  errors : Errors P s₀ s
  dk : ∀ j' < j, Spec.Sha3.bytesAt s.mem (kA s₀ 2+BitVec.ofNat 64 (384*j')) 384 =
    encode12 (KPke.kgS P.params (dB s₀) j')
  frame : Frame [R (kA s₀) 2 0 (384*j)] mN s.mem

theorem encode_step {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P)
    {mB mN : Mem} {v : BitVec 64} {j : Nat} (hj : j < P.k) (h : EncodeInv P s₀ mB mN v j s) :
    WP isa (kgEnc (sOff P j) .x27 (384*j)) s (EncodeInv P s₀ mB mN v (j+1)) := by
  have hw := hp.wf
  have fd : 384*j+384 ≤ kL P 2 := by kl
  refine WP.mono (enc_ok hp (off := sOff P j) (b := 2) (o := 384*j)
    (po_s hw hj) (.inr rfl) fd h.c.kb (h.sp j hj).1) fun t ⟨kt,ft,bt,xt⟩ => ?_
  refine ⟨h.c.frame kt xt ft (one_far hp (by decide) fd (.inl (by decide))),?_,?_,?_,?_⟩
  · intro i hi
    exact polyIs_frame ft (fun r hh => by
      rw [List.mem_singleton.mp hh]
      exact hp.args.rdisj (by decide) (by decide) (by kl) fd (.inl (by decide))) (h.sp i hi)
  · intro i hi
    exact polyIs_frame ft (fun r hh => by
      rw [List.mem_singleton.mp hh]
      exact hp.args.rdisj (by decide) (by decide) (Noise.noise_fits hr hi) fd (.inl (by decide))) (h.errors i hi)
  · intro i hi
    rcases (by omega : i<j ∨ i=j) with hi | rfl
    · rw [bytesAt_frame ft (fun r hh => by
        rw [List.mem_singleton.mp hh]
        exact hp.args.rdisj (by decide) (by decide) (by kl) fd (.inr (.inl (by omega)))) (by decide)]
      exact h.dk i hi
    · rw [bt,(h.sp i hj).2]
  · exact (h.frame.sub (fun r hh => by
      rw [List.mem_singleton.mp hh]
      exact ⟨_,List.mem_singleton_self _,R.sub2 (by omega) (by omega)⟩)).trans
      (ft.sub (fun r hh => by
        rw [List.mem_singleton.mp hh]
        exact ⟨_,List.mem_singleton_self _,R.sub2 (by omega) (by omega)⟩))

theorem encode_ok {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P)
    {mB mN : Mem} {v : BitVec 64} (h : EncodeInv P s₀ mB mN v 0 s) :
    WPs ((List.range P.k).map fun j => kgEnc (sOff P j) .x27 (384*j)) s (EncodeInv P s₀ mB mN v P.k) :=
  WPs.range (fun _ hj _ h => encode_step hp hr hj h) h

theorem EncodeInv.tl {s₀ s : State} {mB mN : Mem} {v : BitVec 64}
    (h : EncodeInv P s₀ mB mN v P.k s) : TL P s₀ mB v 0 s :=
  ⟨h.c,h.sp,h.dk,fun _ hi => by omega⟩

end VG.Proof.MlKem.AArch64.KeyGen
