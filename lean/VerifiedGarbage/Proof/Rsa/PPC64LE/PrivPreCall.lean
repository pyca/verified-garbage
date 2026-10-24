module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivCrt
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PreFn
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd

/-!
# `vg_rsa_private_checked` on PPC64LE: the call of `vg_rsa_public_precompute`

The CRT's status kept in the frame (`preArgs_ok`, into `AtPre`), then the
call by the callee's contract on its registers (`Pre.fnContract`,
`Pre.fn_correct`): `n`'s values into the frame (`preCall_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Priv

open VG VG.PPC64LE VG.Impl.Rsa.PPC64LE.Priv
open VG.Proof.Bignum.PPC64LE (Keep)

theorem written_congr {m m' : Mem} {out : Addr} {k : Nat} {r : BitVec 32} {o : Option (List Byte)}
    (hb : Spec.Rsa.bytesAt m' out k = Spec.Rsa.bytesAt m out k) (h : Spec.Rsa.written m out k r o) :
    Spec.Rsa.written m' out k r o := by
  cases o <;> simp only [Spec.Rsa.written, hb] at h ⊢ <;> exact h

/-- `m` and the CRT's status kept in the frame. -/
abbrev crtOutM (s u : State) : Prop :=
  Spec.Rsa.written u.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .r6).toNat
    ((u.mem.readW (fb s + BitVec.ofNat 64 oSt) 64).setWidth 32)
    (Spec.Rsa.privateCrt (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r6).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat))

/-- A word of the frame above the slots, in it. -/
theorem word_in {s : State} {d : Nat} (hd : oLr + 8 ≤ d) (hd' : d + 8 ≤ frameBytes) (rs : List Region) :
    InRegions (fr s :: rs) (fb s + BitVec.ofNat 64 d) 8 :=
  in_fr s rs (by unfold oLr at hd; omega) hd'

/-- `Mid` is kept by a write of a word of the frame above the slots. -/
theorem Mid.store {s t : State} (M : Mid s t) {d : Nat} (hd : oLr + 8 ≤ d) (hd' : d + 8 ≤ frameBytes)
    (v : BitVec 64) {u : State} (hg : ∀ r ∈ preserved, u.gpr r = t.gpr r) (hsp : u.sp = t.sp)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) (hm : u.mem = t.mem.writeW (fb s + BitVec.ofNat 64 d) v) :
    Mid s u := by
  have hd1 : ∀ {e : Nat}, e + 8 ≤ oLr + 8 →
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 e, 8⟩ ⟨fb s + BitVec.ofNat 64 d, 8⟩ := fun he =>
    Offset.disjoint _ (.inl (by omega)) (by unfold oLr at he; omega) (by unfold frameBytes at hd'; omega)
  have fw : Frame [⟨fb s + BitVec.ofNat 64 d, 8⟩] t.mem u.mem := by
    rw [hm]; exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hsp.trans M.sp, hrd.trans M.rd, hwr.trans M.wr, (hg _ (by decide)).trans M.r24,
    (hg _ (by decide)).trans M.r25, (hg _ (by decide)).trans M.r26, (hg _ (by decide)).trans M.r27,
    (hg _ (by decide)).trans M.r28, (hg _ (by decide)).trans M.r29,
    fun r hr => (hg r (by revert r; decide)).trans (M.hi r hr), ?_,
    M.sv.frame fw fun p hp r hr => by
      rw [List.mem_singleton.mp hr]; exact hd1 (by have := saved_offs p hp; unfold oSave oLr at *; omega), ?_⟩
  · rw [hm]; exact M.mem.writeW (List.mem_cons_self ..) _ (frame_contains s hd')
  · rw [fw.readW (Region.contains_self _ _) (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd1 (by decide))
      (by decide)]
    exact M.ls

/-- Our stack argument `j`, after the frame and the working space changed. -/
theorem arg_read2 {s : State} (h : PreP s) {m : Mem} (hm : Frame [kR s, sR s] s.mem m) {j : Nat} (hj : j < 12) :
    m.readW (fb s + BitVec.ofNat 64 (arg j)) 64 = stackArg s j := by
  rw [← stackArgAddr_fb]
  refine hm.readW (in_aR hj) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.ka.symm
  · exact h.sa.symm

/-- At the call of `vg_rsa_public_precompute`. -/
structure AtPre (s u : State) : Prop extends Mid s u where
  crt : crtOutM s u
  r3 : u.gpr .r3 = fb s + BitVec.ofNat 64 oPre
  r4 : u.gpr .r4 = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .r6).toNat)
  r5 : u.gpr .r5 = s.gpr .r5
  r6 : u.gpr .r6 = s.gpr .r6
  r7 : u.gpr .r7 = stackArg s 10
  r8 : u.gpr .r8 = stackArg s 11

theorem gpr_ofNat (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by simp

theorem preLen_val {k : Nat} (hk : k ≤ 1024) :
    (BitVec.ofNat 64 k + BitVec.ofNat 64 7) >>> 3 <<< 1 = BitVec.ofNat 64 (Spec.Rsa.precomputedWords k) := by
  rw [Proof.Bignum.PPC64LE.Pre.ofNat_add7_shr3 k (by omega), Proof.Bignum.PPC64LE.Pre.ofNat_shl1]; rfl

theorem preArgs_ok {s t : State} (h : PreP s) (M : Mid s t) (C : crtOut s t) :
    WP isa (.block preArgs) t (AtPre s) := by
  have hk := h.k2
  have e26 : t.gpr .r26 = BitVec.ofNat 64 (s.gpr .r6).toNat := M.r26.trans (gpr_ofNat _)
  have ho : InRegions t.wr (fb s + BitVec.ofNat 64 oSt) 8 := by
    rw [M.wr]; exact word_in (by decide) (by decide) _
  have rdm : t.rd = s.rd := M.rd
  have hrdw : ∀ {j : Nat}, j < 12 → (t.mem.writeW (fb s + BitVec.ofNat 64 oSt) (t.gpr .r3)).readW
      (fb s + BitVec.ofNat 64 (arg j)) 64 = stackArg s j := fun hj => by
    rw [Mem.readW_writeW_sep (Offset.sep _ (.inr (by unfold oSt arg frameBytes; omega))
      (by unfold arg frameBytes; omega) (by decide)) (by decide)]
    exact arg_read2 h M.mem hj
  have a10 := hrdw (j := 10) (by decide)
  have a11 := hrdw (j := 11) (by decide)
  have i10 := arg_in h rdm (j := 10) (by decide)
  have i11 := arg_in h rdm (j := 11) (by decide)
  have c1 : oSt < 2 ^ 15 := by decide
  have c2 : oSt % 4 = 0 := by decide
  have c3 : oPre < 2 ^ 15 := by decide
  have c4 : arg 10 < 2 ^ 15 := by decide
  have c5 : arg 11 < 2 ^ 15 := by decide
  have c6 : arg 10 % 4 = 0 := by decide
  have c7 : arg 11 % 4 = 0 := by decide
  refine WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r12, .r3, .r4, .r5, .r6, .r7, .r8] (Q := fun u =>
    u.gpr .r3 = fb s + BitVec.ofNat 64 oPre ∧
      u.gpr .r4 = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .r6).toNat) ∧ u.gpr .r5 = s.gpr .r5 ∧
      u.gpr .r6 = s.gpr .r6 ∧ u.gpr .r7 = stackArg s 10 ∧ u.gpr .r8 = stackArg s 11 ∧
      u.mem = t.mem.writeW (fb s + BitVec.ofNat 64 oSt) (t.gpr .r3)) ?_ rfl) fun u ⟨⟨u3, u4, u5, u6, u7, u8, um⟩, k⟩ => ?_
  · unfold preArgs preLen
    prun [exec_addSp0, M.sp, ho, c1, c2, c3, c4, c5, c6, c7, i10, i11, a10, a11, e26, preLen_val hk, M.r25, M.r26,
      BitVec.or_self, exec_addi (show Reg.r12 ≠ .r0 by decide) c3, Impl.AesGcm.PPC64LE.mov]
    all_goals exact (gpr_ofNat _).symm
  · refine ⟨M.store (d := oSt) (by decide) (by decide) _ (fun r hr => k.gpr r (by revert r; decide)) k.sp k.rd
      k.wr um, ?_, u3, u4, u5, u6, u7, u8⟩
    have hb : Spec.Rsa.bytesAt u.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .r6).toNat =
        Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .r6).toNat := by
      simp only [Spec.Rsa.bytesAt]
      refine List.map_congr_left fun i hi => ?_
      have hi := List.mem_range.mp hi
      rw [um]
      exact Frame.bytes (R := mR s) (Frame.writeW (Frame.refl [⟨fb s + BitVec.ofNat 64 oSt, 8⟩] t.mem)
        (List.mem_singleton_self _) _ (Region.contains_self _ _))
        (fun r hr => by
          rw [List.mem_singleton.mp hr]
          exact Offset.disjoint _ (.inr (by decide)) (by unfold oM; omega) (by decide))
        (show (s.gpr .r6).toNat ≤ 2 ^ 64 by omega) hi
    show Spec.Rsa.written _ _ _ _ _
    rw [um, Mem.readW_writeW_self64, ← um]
    exact written_congr hb C

end VG.Proof.Rsa.PPC64LE.Priv
