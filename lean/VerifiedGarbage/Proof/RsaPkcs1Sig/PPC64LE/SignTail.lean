module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.SignCall
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# `vg_rsa_pkcs1_sign` on PPC64LE: zeros and the restores

`zeroLoop` writes zeros (`zero_ok`): to `out` when the encoding fails
(`zeroOut_ok`), and over `EM` after the call (`wipe_ok`). Then the restores
give back our caller's registers (`restore_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.PPC64LE.Sign

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE.Sign VG.WriteBytes
open VG.Proof.RsaPkcs1Sig.PPC64LE (wp_stb wp_addi wp_subi wp_nil ofNat_succ')

/-- `zeroLoop` writes `n` zeros from `r7 = p`, counted down in `r8`. -/
theorem zero_ok {s : State} {p : Addr} {n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 64)
    (h7 : s.gpr .r7 = p) (h8 : s.gpr .r8 = BitVec.ofNat 64 n) (h0 : (s.gpr .r0).setWidth 8 = 0)
    (hw : ∀ i < n, InRegions s.wr (p + BitVec.ofNat 64 i) 1) :
    WP isa zeroLoop s fun t =>
      RsaPkcs1Sig.PPC64LE.Keep [.r7, .r8] s t ∧ t.mem = writeBytes s.mem p (List.replicate n 0) := by
  refine WP.mono (Proof.Bignum.PPC64LE.wp_countdown (cnt := .r8) hn' hn
    (fun i t => RsaPkcs1Sig.PPC64LE.Keep [.r7, .r8] s t ∧ t.mem = writeBytes s.mem p (List.replicate i 0) ∧
      t.gpr .r7 = p + BitVec.ofNat 64 i) ?_
    ⟨RsaPkcs1Sig.PPC64LE.Keep.refl _ _, by simp [writeBytes_nil], by simp [h7]⟩ h8)
    fun t h => ⟨h.1, h.2.1⟩
  intro i hi t ⟨hK, hm, h7'⟩ _
  have hA : InRegions t.wr (t.gpr .r7 + BitVec.ofNat 64 0) 1 := by
    rw [h7', hK.wr, BitVec.add_zero]; exact hw _ hi
  refine wp_stb rfl hA fun s₁ m₁ => ?_
  refine wp_addi fun s₂ o₂ e₂ => ?_
  refine wp_subi fun s₃ o₃ e₃ => wp_nil ?_
  have hK' : RsaPkcs1Sig.PPC64LE.Keep [.r7, .r8] t s₃ := (m₁.keep.trans (o₂.keep.trans o₃.keep)).mono
  refine ⟨⟨(hK.trans hK').mono, ?_, ?_⟩, ?_⟩
  · rw [o₃.mem, o₂.mem, m₁.mem, hK.get .r0, h0, h7', BitVec.add_zero, hm, List.replicate_succ',
      writeBytes_snoc _ _ _ _ (by simp; omega)]
    simp
  · rw [o₃.get .r7, e₂, m₁.gpr, h7', ofNat_succ']
  · rw [e₃, o₂.get .r8, m₁.gpr]

theorem gpr_ofNat (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by simp

/-- `out` is in the regions it may write. -/
theorem out_in {s : State} (h : SPre s) {i : Nat} (hi : i < (s.gpr .r6).toNat) :
    InRegions (fr s :: s.wr) (s.gpr .r3 + BitVec.ofNat 64 i) 1 := by
  rw [h.hwr]
  exact ⟨oR s, by simp, Offset.contains_base _ (by rw [h.h4]; omega) (by have := h.wo; omega)⟩

theorem Fr.fr2 {s t : State} (F : Fr s t) : Fr2 s t :=
  ⟨F.sp, F.rd, F.wr, F.hi, F.mem.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩,
    F.sv, F.ls⟩

/-- Zeros to `out`, once the encoding failed. -/
theorem zeroOut_ok {s u : State} (h : SPre s) (A : AtAft s u) (h3 : u.gpr .r3 = 0) :
    WP isa zeroOut u fun v => Fr2 s v ∧ v.gpr .r3 = 0 ∧
      Spec.Rsa.bytesAt v.mem (s.gpr .r3) (s.gpr .r6).toNat = List.replicate (s.gpr .r6).toNat 0 := by
  have hk := h.k2
  have hk1 := h.k1
  unfold zeroOut
  refine WP.seq (WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r7, .r8, .r0] (Q := fun w =>
    w.gpr .r7 = s.gpr .r3 ∧ w.gpr .r8 = BitVec.ofNat 64 (s.gpr .r6).toNat ∧ w.gpr .r0 = 0 ∧ w.mem = u.mem) ?_ rfl)
    fun w ⟨⟨w7, w8, w0, wm⟩, kw⟩ => ?_)
  · prun [A.r26, A.r28, BitVec.or_self, Impl.AesGcm.PPC64LE.mov]
    exact ⟨gpr_ofNat _, rfl⟩
  refine WP.mono (zero_ok (by omega) (by omega) w7 w8 (by rw [w0]; rfl) fun i hi => by
    rw [kw.wr, A.wr]; exact out_in h hi) fun v ⟨kv, vm⟩ => ?_
  have hO : (oR s).Contains (s.gpr .r3) (List.replicate (s.gpr .r6).toNat (0 : Byte)).length := by
    rw [List.length_replicate, ← h.h4]; exact Region.contains_self _ _
  have fo : Frame [oR s] u.mem v.mem := by rw [vm, wm]; exact writeBytes_frame _ _ _ hO
  refine ⟨⟨kv.sp.trans (kw.sp.trans A.sp), kv.rd.trans (kw.rd.trans A.rd), kv.wr.trans (kw.wr.trans A.wr),
    fun r hr => (kv.gpr r (by revert r; decide)).trans ((kw.gpr r (by revert r; decide)).trans (A.hi r hr)),
    (A.fr2.mem).trans (fo.sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩),
    A.sv.frame fo fun p hp r hr => by
      rw [List.mem_singleton.mp hr]; exact h.ko.sub_left (frame_sub s (by have := saved_offs p hp; unfold oSave frameBytes at *; omega)),
    ?_⟩, ?_, ?_⟩
  · rw [fo.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact h.ko.sub_left (frame_sub s (by decide))) (by decide)]; exact A.ls
  · rw [kv.gpr _ (by decide), kw.gpr _ (by decide)]; exact h3
  · rw [vm, wm]
    have := Proof.RsaPkcs1Sig.bytesAt_writeBytes u.mem (s.gpr .r3) (List.replicate (s.gpr .r6).toNat (0 : Byte))
      (by simp; omega)
    rwa [List.length_replicate] at this

theorem wo_congr {m m' : Mem} {out : Addr} {k : Nat} {r : BitVec 32} {o : Spec.Rsa.Outcome}
    (hb : Spec.Rsa.bytesAt m' out k = Spec.Rsa.bytesAt m out k) (h : Spec.Rsa.writtenOutcome m out k r o) :
    Spec.Rsa.writtenOutcome m' out k r o := by
  cases o <;> simp only [Spec.Rsa.writtenOutcome, hb] at h ⊢ <;> exact h

/-- `EM` overwritten with zeros, after the call. -/
theorem wipe_ok {s u : State} {em : List Byte} (h : SPre s) (R : AtRet s u em) :
    WP isa wipe u fun v => Fr2 s v ∧ privOut s em v := by
  have hk := h.k2
  have hk1 := h.k1
  have c1 : oEM < 2 ^ 15 := by decide
  unfold wipe
  refine WP.seq (WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r12, .r7, .r8, .r0] (Q := fun w =>
    w.gpr .r7 = fb s + BitVec.ofNat 64 oEM ∧ w.gpr .r8 = BitVec.ofNat 64 (s.gpr .r6).toNat ∧ w.gpr .r0 = 0 ∧
      w.mem = u.mem) ?_ rfl) fun w ⟨⟨w7, w8, w0, wm⟩, kw⟩ => ?_)
  · prun [exec_addSp0, R.sp, R.r28, BitVec.or_self, Impl.AesGcm.PPC64LE.mov,
      exec_addi (show Reg.r12 ≠ .r0 by decide) c1]
    exact ⟨gpr_ofNat _, rfl⟩
  refine WP.mono (zero_ok (by omega) (by omega) w7 w8 (by rw [w0]; rfl) fun i hi => by
    rw [kw.wr, R.wr]; exact em_in h _ hi) fun v ⟨kv, vm⟩ => ?_
  have hE : (emR s).Contains (fb s + BitVec.ofNat 64 oEM) (List.replicate (s.gpr .r6).toNat (0 : Byte)).length := by
    rw [List.length_replicate]; exact Region.contains_self _ _
  have fe : Frame [emR s] u.mem v.mem := by rw [vm, wm]; exact writeBytes_frame _ _ _ hE
  refine ⟨⟨kv.sp.trans (kw.sp.trans R.sp), kv.rd.trans (kw.rd.trans R.rd), kv.wr.trans (kw.wr.trans R.wr),
    fun r hr => (kv.gpr r (by revert r; decide)).trans ((kw.gpr r (by revert r; decide)).trans (R.hi r hr)),
    R.mem.trans (fe.sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., em_sub h⟩),
    R.sv.frame fe fun p hp r hr => below_em h (by have := saved_offs p hp; unfold oSave oEM at *; omega) hr, ?_⟩, ?_⟩
  · rw [fe.readW (Region.contains_self _ _) (fun r hr => below_em h (by decide) hr) (by decide)]; exact R.ls
  · have hb : Spec.Rsa.bytesAt v.mem (s.gpr .r3) (s.gpr .r6).toNat = Spec.Rsa.bytesAt u.mem (s.gpr .r3) (s.gpr .r6).toNat :=
      bytes_of_frame (s := u) fe (fun r hr => by
        rw [List.mem_singleton.mp hr, show (⟨s.gpr .r3, (s.gpr .r6).toNat⟩ : Region) = oR s by simp only [oR, h.h4]]
        exact (h.ko.sub_left (em_sub h)).symm) (by omega)
    show Spec.Rsa.writtenOutcome _ _ _ ((v.gpr .r3).setWidth 32) _
    rw [kv.gpr _ (by decide), kw.gpr _ (by decide)]
    exact wo_congr hb R.out

/-- The restores. -/
theorem restore_ok {s w : State} (F : Fr2 s w) :
    WP isa (.block restore) w fun v =>
      (∀ r ∈ preserved, v.gpr r = s.gpr r) ∧ v.lr = s.lr ∧ v.sp = fb s ∧ v.mem = w.mem ∧ v.gpr .r3 = w.gpr .r3 := by
  have iLr : InRegions (w.rd ++ w.wr) (fb s + BitVec.ofNat 64 oLr) 8 := by
    rw [F.wr]; exact in_fr' s _ _ (by decide) (by decide)
  have c1 : oLr < 2 ^ 15 := by decide
  have c2 : oLr % 4 = 0 := by decide
  rw [restore_eq]
  refine WP.block_append_iff.mpr (WP.mono (Q := fun v => v = { ((w.write .r12 w.sp).write .r0
      (w.mem.readW (fb s + BitVec.ofNat 64 oLr) 64)) with lr := w.mem.readW (fb s + BitVec.ofNat 64 oLr) 64 })
    ?_ fun v e => ?_)
  · prun [exec_addSp0, F.sp, iLr, c1, c2, exec_mtlr]
  · subst e
    refine WP.mono (Spill.restore_wp (b := .r12) (B := fb s) (by decide) (by simp [State.write, F.sp])
      saved_ho (by decide) (fun p hp => by
        have := saved_offs p hp
        show InRegions (w.rd ++ w.wr) _ 8
        rw [F.wr]; exact in_fr' s _ _ (by unfold oSave at this; omega) (by unfold oSave at this; unfold frameBytes; omega))
      F.sv) fun v R => ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · rcases preserved_split hr with hs | hs
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs
        exact R.gpr p hp
      · have : r ∉ saved.map Prod.fst := by revert r; decide
        rw [R.other r this]
        have h12 : r ≠ .r12 := by revert r; decide
        have h0 : r ≠ .r0 := by revert r; decide
        simp only [State.write, h12, h0, ite_false]
        exact F.hi r hs
    · rw [R.lr]; exact F.ls
    · rw [R.sp]; exact F.sp
    · rw [R.mem]; rfl
    · rw [R.other _ (by decide)]; simp [State.write]

end VG.Proof.RsaPkcs1Sig.PPC64LE.Sign
