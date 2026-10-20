module

public import VerifiedGarbage.Proof.MlKem.AArch64.KgH.Inv
import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.KgOps
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenNoise
import VerifiedGarbage.Proof.MlKem.AArch64.KgH.Row
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-! # Before the matrix: the noise, `ŝ` into `dk`, the all-zero third state

`pre_ok`: after `G`, `Kem16.kgPre` establishes the interleaved invariant with
nothing of the matrix, the rows or the hash done. -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt)
open VG.Proof.MlKem.AArch64.Optimized
open VG.Proof.MlKem.AArch64.Hybrid (TStk)

variable {P : KemLay}

/-- The third state, `scratch`'s first 200 bytes, is apart from the other values. -/
theorem st_far {s₀ : State} (hp : Pre P s₀) {b o l : Nat} (hb : b < 4) (f : o + l ≤ kL P b)
    (hs : b ≠ 3 ∨ 200 ≤ o) : (R (kA s₀) b o l).Disjoint (R (kA s₀) 3 0 200) := by
  have hw := hp.wf
  exact hp.args.rdisj hb (by decide) f (by kl) (by rcases hs with hs | hs <;> omega)

/-- The all-zero third state. -/
theorem zero_ok {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P) {mB mN : Mem} {v : BitVec 64}
    (h : EncodeInvW P s₀ mB mN v 0 P.k s) :
    WP isa (.block (zeroState .x28 KG.ST)) s fun t =>
      EncodeInvW P s₀ mB t.mem v 0 P.k t ∧ stateAt t.mem (kA s₀ 3) = Spec.Sha3.zero := by
  have hw := hp.wf
  have kb := h.c.kb
  refine WP.mono (zeroState_ok (hsetup hp kb (rate := 136) (by decide)) ⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩)
    fun t ⟨kt, zt⟩ => ?_
  have e : STr .x28 KG.ST s = R (kA s₀) 3 0 200 := by simp only [STr, R, kb.x28, KG.ST]
  rw [e] at kt
  rw [kb.x28, show KG.ST = 0 from rfl, ptr_zero] at zt
  have kbt := kb.call kt fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨(st_far hp (b := 3) (o := SV P) (l := 48) (by decide) hp.sv (.inr (by lom))),
      st_far hp (by decide) (by kl) (.inl (by decide))⟩
  have far : ∀ {b o l : Nat}, b < 4 → o + l ≤ kL P b → (b ≠ 3 ∨ 200 ≤ o) →
      ∀ r ∈ [R (kA s₀) 3 0 200], (R (kA s₀) b o l).Disjoint r := fun hb f hs r hr => by
    rw [List.mem_singleton.mp hr]; exact st_far hp hb f hs
  refine ⟨⟨h.c.frame kbt (kt.cs .x24 (by decide) (by decide)) kt.frame fun r hr => ⟨far (by decide) (by kl) (.inr (by decide)) r hr,
      far (by decide) (by kl) (.inr (by decide)) r hr, far (by decide) (by kl) (.inr (by lom)) r hr⟩,
    fun j hj => polyIsW_frame_poly (w16 := true) kt.frame (far (by decide) (by kl) (.inr (by lom))) (h.sp j hj),
    fun j hj => ?_, fun j hj => ?_, Frame.refl _ _⟩, zt⟩
  · exact polyIsW_frame_poly (w16 := true) kt.frame (far (by decide) (Noise.noise_fits hr hj)
      (.inr (by have := Noise.noise_past_kg hr j; lom))) (h.errors j hj)
  · rw [bytesAt_frame kt.frame (far (by decide) (by kl) (.inl (by decide))) (by decide)]
    exact h.dk j hj

/-- **The noise, `ŝ` into `dk` and the all-zero third state**, after `G`. -/
theorem pre_ok {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P) (hA : AfterA P s₀ s) (ta : Tables s)
    (tk : TStk s) (depth : (Impl.MlKem.AArch64.Kem16.kgPre P).aarch64Depth ≤ 1) :
    WP isa (Impl.MlKem.AArch64.Kem16.kgPre P) s (IL P s₀ 0 0 0) := by
  have hw := hp.wf
  have c : CInvW P s₀ s.mem (s.gpr .x24) 0 s :=
    ⟨hA.kb, hA.rho, hA.sig, rfl, Nat.zero_le _, fun e he => absurd he (Nat.not_lt_zero _)⟩
  have body : WP isa (Impl.MlKem.AArch64.Kem16.kgPre P) s fun v => ∃ mN,
      EncodeInvW P s₀ s.mem mN (s.gpr .x24) 0 P.k v ∧ stateAt v.mem (kA s₀ 3) = Spec.Sha3.zero := by
    unfold Impl.MlKem.AArch64.Kem16.kgPre
    refine WPs.seqs (by simp) (WPs.append (WPs.append ?_))
    refine WPs.cons (WP.mono (readonly_noise_encodeW hp hr ta.transforms c) fun t ⟨_, et⟩ => ?_)
    simp only [WPs]
    exact WPs.mono (encode_okW hp hr et) fun u eu =>
      WPs.single (WP.mono (zero_ok hp hr eu) fun v ⟨ev, zv⟩ => ⟨_, ev, zv⟩)
  refine WP.mono_syms (WP.tablesDepth body ta depth) fun v ⟨⟨mN, ev, zv⟩, tv⟩ hs => ?_
  have kbv := ev.c.kb
  refine ⟨⟨kbv, ev.c.rho, ev.c.sig, ?_, fun e he => absurd he (Nat.not_lt_zero _),
      fun e he => absurd he (Nat.not_lt_zero _)⟩,
    ev.sp, ev.errors, ev.dk, fun i hi => absurd hi (Nat.not_lt_zero _), by simp,
    Nat.zero_le _, Nat.zero_le _, ?_, by simp, tv,
    tk.of hs (by rw [kbv.sp, hA.kb.sp])⟩
  · rw [ev.c.x24, hA.x24, ite_eq_left (show allOk P s₀ 0 from fun e he => absurd he (Nat.not_lt_zero e))]
  · rw [zv, Hybrid.hstate_zero]

end VG.Proof.MlKem.AArch64.KeyGen
