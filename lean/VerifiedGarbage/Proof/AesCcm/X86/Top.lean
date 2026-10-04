import VerifiedGarbage.Proof.AesCcm.X86.Args

/-!
# AES-CCM on x86: the start of both functions

Untrusted: everything here is checked by Lean. `seal` and `open` both start
with the entry and `Ctr₀` (`start_ok`); after them, the slots hold the
arguments and `W + 48` holds `Ctr₀`, and the key schedule, the nonce, the
associated data, the data, the received tag and the return address are as
they were (`Started`). The pieces after them write only `mutR`, which keeps
all of that but the data (`Started.mut`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.Impl.AesCcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86 (w64 slotv SavedAt ret_below ofNat_toNat32)

/-- After the entry and `Ctr₀`. -/
structure Started (s : State) (K W SP N A D : BitVec 32) (R nl al n tl : Nat) (s' : State) : Prop where
  env : Env K W SP s'
  slots : Slots W K R N A D nl al n tl s'.mem
  saved : SavedAt s'.mem W s
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  c0 : bytesAt s'.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem (w64 N) nl) 0
  ciph : Spec.Ccm.ctxCiph s'.mem (w64 K) R = Spec.Ccm.ctxCiph s.mem (w64 K) R
  aadB : bytesAt s'.mem (w64 A) al = bytesAt s.mem (w64 A) al
  dataB : bytesAt s'.mem (w64 D) n = bytesAt s.mem (w64 D) n
  tagB : bytesAt s'.mem (w64 W) tl = bytesAt s.mem (w64 W) tl
  ret : s'.mem.readW (w64 SP) 32 = s.mem.readW (w64 SP) 32

/-- The entry and `Ctr₀`. -/
theorem start_ok {s : State} {K W SP N A D : BitVec 32} {R nl al n tl : Nat}
    (Ar : Args s K W SP N A D R nl al n tl) (hsp : s.gpr .esp = SP) (a0 : arg s 0 = K)
    (a1 : arg s 1 = BitVec.ofNat 32 R) (a2 : arg s 2 = N) (a3 : arg s 3 = BitVec.ofNat 32 nl) (a4 : arg s 4 = A)
    (a5 : arg s 5 = BitVec.ofNat 32 al) (a6 : arg s 6 = D) (a7 : arg s 7 = BitVec.ofNat 32 n) (a8 : arg s 8 = W)
    (a9 : arg s 9 = BitVec.ofNat 32 tl) :
    WP isa (.seq ccmEntry ctrs) s (Started s K W SP N A D R nl al n tl) := by
  have L := Ar.lay
  refine WP.seq (WP.mono (entry_ok a8 Ar.perm.w (by rw [hsp]; exact Ar.args) (by rw [hsp]; exact Ar.argsW)
    (by rw [hsp]; exact Ar.fa) L.fw) fun s₁ E₀ => ?_)
  have E₁ : Env K W SP s₁ := ⟨E₀.ebp, by rw [E₀.esp, hsp], Ar.perm.of_eq E₀.rd E₀.wr⟩
  have sl : ∀ p ∈ entryPs, slotv s₁.mem W p.2 = arg s p.1 := E₀.slots
  have S₁ : Slots W K R N A D nl al n tl s₁.mem :=
    ⟨by rw [sl (0, ctxO) (by simp), a0], by rw [sl (1, roundsO) (by simp), a1],
      by rw [sl (2, nonceO) (by simp), a2], by rw [sl (3, nlenO) (by simp), a3],
      by rw [sl (4, aadO) (by simp), a4], by rw [sl (5, alenO) (by simp), a5],
      by rw [sl (6, dataO) (by simp), a6], by rw [sl (7, lenO) (by simp), a7],
      by rw [sl (9, Impl.AesGcm.X86.tglO) (by simp), a9], E₀.tp⟩
  have fE := E₀.frame
  have bE : ∀ {P : BitVec 32} {len : Nat}, Buf W SP s P len → bytesAt s₁.mem (w64 P) len = bytesAt s.mem (w64 P) len :=
    fun hP => Proof.AesGcm.X86.bytesAt_frame fE (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by have := hP.lt; omega)
  have hRb : 16 * (R + 1) ≤ 240 := by rcases Ar.rounds with h | h | h <;> subst h <;> decide
  have cE : Spec.Ccm.ctxCiph s₁.mem (w64 K) R = Spec.Ccm.ctxCiph s.mem (w64 K) R :=
    ctxCiph_frame fE (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_right (Lay.wSub (by decide))) hRb
  refine WP.mono (ctrs_ok L E₁ S₁.nonce S₁.nlen (Ar.nonce.of_eq E₀.rd E₀.wr) Ar.h7 Ar.h13)
    fun s₂ ⟨E₂, f₂, c₂, rd₂, wr₂⟩ => ?_
  have f₂' : Frame (mutR W SP D n) s₁.mem s₂.mem := f₂.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨wA W, by simp, Offset.sub_base _ (by decide)⟩
  have b₂ : ∀ {P : BitVec 32} {len : Nat}, Buf W SP s P len → bytesAt s₂.mem (w64 P) len = bytesAt s₁.mem (w64 P) len :=
    fun hP => Proof.AesGcm.X86.bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by have := hP.lt; omega)
  refine ⟨E₂, slots_mut L Ar.data.w f₂' S₁, saved_mut L Ar.data.w f₂' E₀.saved, by rw [rd₂, E₀.rd],
    by rw [wr₂, E₀.wr], by rw [c₂, bE Ar.nonce], ?_, by rw [b₂ Ar.aad, bE Ar.aad], by rw [b₂ Ar.data, bE Ar.data],
    ?_, ?_⟩
  · rw [ctxCiph_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_right (Lay.wSub (by decide))) hRb, cE]
  · have ht := Ar.t16
    rw [Proof.AesGcm.X86.bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        simpa using Lay.w_w (W := W) (a := 0) (n := tl) (d := 48) (k := 16) (.inl (by omega)) (by omega) (by decide))
        (by omega),
      Proof.AesGcm.X86.bytesAt_frame fE (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        simpa using Lay.w_w (W := W) (a := 0) (n := tl) (d := 128) (k := 2432) (.inl (by omega)) (by omega) (by decide))
        (by omega)]
  · rw [Proof.AesGcm.X86.ret_kept f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Ar.retW.sub_right (Lay.wSub (by decide))),
      Proof.AesGcm.X86.ret_kept fE (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Ar.retW.sub_right (Lay.wSub (by decide)))]

/-- What the pieces after the start keep. -/
theorem Started.mut {s : State} {K W SP N A D : BitVec 32} {R nl al n tl : Nat}
    (Ar : Args s K W SP N A D R nl al n tl) {s₁ : State} (St : Started s K W SP N A D R nl al n tl s₁) {m : Mem}
    (hf : Frame (mutR W SP D n) s₁.mem m) :
    Slots W K R N A D nl al n tl m ∧ SavedAt m W s ∧
      Spec.Ccm.ctxCiph m (w64 K) R = Spec.Ccm.ctxCiph s.mem (w64 K) R ∧
      bytesAt m (w64 A) al = bytesAt s.mem (w64 A) al ∧ m.readW (w64 SP) 32 = s.mem.readW (w64 SP) 32 := by
  have L := Ar.lay
  refine ⟨slots_mut L Ar.data.w hf St.slots, saved_mut L Ar.data.w hf St.saved,
    by rw [ciph_mut L Ar.dk Ar.rounds hf, St.ciph], by rw [buf_mut Ar.aad Ar.ad hf, St.aadB], ?_⟩
  rw [Proof.AesGcm.X86.ret_kept hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Ar.retW.sub_right (Region.sub_prefix (by decide))
    · exact Ar.retW.sub_right (Lay.wSub (by decide))
    · exact Ar.retW.sub_right (Lay.wSub (by decide))
    · exact Ar.retW.sub_right (Lay.wSub (by decide))
    · exact ret_below L.sp
    · exact Ar.retD), St.ret]

end VG.Proof.AesCcm.X86
