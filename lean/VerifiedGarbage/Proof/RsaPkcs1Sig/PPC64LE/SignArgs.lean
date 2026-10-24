module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.SignEnc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd

/-!
# `vg_rsa_pkcs1_sign` on PPC64LE: the call's arguments

`vg_rsa_private_checked`'s twelve stack arguments copied from ours and its
arguments in registers (`callArgs_ok`, into `AtCall`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.PPC64LE.Sign

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE.Sign
open VG.Proof.Bignum.PPC64LE (Keep)
open VG.PPC64LE.RegUpd (gpr_write_self gpr_write_of_ne mem_write)

/-- The Parameter Save Area of the call. -/
abbrev psaR (s : State) : Region := ⟨fb s + BitVec.ofNat 64 96, 96⟩

/-- At the call of `vg_rsa_private_checked`, with `EM` holding `em`. -/
structure AtCall (s t : State) (em : List Byte) : Prop extends Fr s t where
  em : Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oEM) (s.gpr .r6).toNat = em
  r3 : t.gpr .r3 = s.gpr .r3
  r4 : t.gpr .r4 = s.gpr .r6
  r5 : t.gpr .r5 = s.gpr .r5
  r6 : t.gpr .r6 = s.gpr .r6
  r7 : t.gpr .r7 = s.gpr .r7
  r8 : t.gpr .r8 = s.gpr .r8
  r9 : t.gpr .r9 = fb s + BitVec.ofNat 64 oEM
  r10 : t.gpr .r10 = s.gpr .r6
  r26 : t.gpr .r26 = s.gpr .r3
  r28 : t.gpr .r28 = s.gpr .r6
  psa : ∀ i < 12, t.mem.readW (fb s + BitVec.ofNat 64 (96 + 8 * i)) 64 = stackArg s (1 + i)

/-- After copying the first `n` stack arguments, from `w`. -/
structure CI (s w : State) (n : Nat) (t : State) : Prop where
  keep : Keep [.r0] w t
  mem : Frame [psaR s] w.mem t.mem
  psa : ∀ i < n, t.mem.readW (fb s + BitVec.ofNat 64 (96 + 8 * i)) 64 = stackArg s (1 + i)

theorem copy_step {s w : State} (h : SPre s) (hw12 : w.gpr .r12 = fb s) (hrd : w.rd = s.rd)
    (hwr : w.wr = fr s :: s.wr) (hm : Frame [kR s] s.mem w.mem) {n : Nat} (hn : n < 12) {t : State}
    (hc : CI s w n t) : WP isa (.block (copyArg n)) t (CI s w (n + 1)) := by
  have t12 : t.gpr .r12 = fb s := (hc.keep.gpr _ (by decide)).trans hw12
  have psa_sub : Region.Sub (psaR s) (kR s) := frame_sub s (by decide)
  have hmt : Frame [kR s] s.mem t.mem := hm.trans (hc.mem.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, psa_sub⟩)
  have hin : InRegions (t.rd ++ t.wr) (t.gpr .r12 + BitVec.ofNat 64 (arg (1 + n))) 8 := by
    rw [t12]; exact arg_in h (hc.keep.rd.trans hrd) (by omega)
  have hv : t.mem.readW (t.gpr .r12 + BitVec.ofNat 64 (arg (1 + n))) 64 = stackArg s (1 + n) := by
    rw [t12]; exact arg_read h hmt (by omega)
  have ho : InRegions t.wr (t.gpr .r12 + BitVec.ofNat 64 (96 + 8 * n)) 8 := by
    rw [t12, hc.keep.wr, hwr]; exact in_fr s _ (by omega) (by unfold frameBytes; omega)
  have harg : arg (1 + n) < 2 ^ 15 ∧ arg (1 + n) % 4 = 0 := by unfold arg frameBytes; omega
  apply WP.of_runBlock
  simp only [copyArg, runBlock_cons, runStep_some, exec_load_d (show Reg.r12 ≠ .r0 by decide) harg hin]
  rw [exec_store_d (show Reg.r12 ≠ .r0 by decide) ⟨by omega, by omega⟩
    (by rw [gpr_write_of_ne _ _ (show Reg.r12 ≠ .r0 by decide)]; exact ho)]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']
  rw [gpr_write_of_ne _ _ (show Reg.r12 ≠ .r0 by decide), gpr_write_self, mem_write, hv, t12]
  refine ⟨⟨fun r hr => ?_, hc.keep.rd, hc.keep.wr, hc.keep.sp, hc.keep.lr⟩, ?_, fun i hi => ?_⟩
  · show (t.write .r0 _).gpr r = w.gpr r
    rw [gpr_write_of_ne _ _ (by simpa using hr)]; exact hc.keep.gpr r hr
  · exact hc.mem.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by decide))
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide)]
      exact hc.psa i hi
    · rw [Mem.readW_writeW_self64]

theorem copies_ok {s w : State} (h : SPre s) (hw12 : w.gpr .r12 = fb s) (hrd : w.rd = s.rd)
    (hwr : w.wr = fr s :: s.wr) (hm : Frame [kR s] s.mem w.mem) :
    WP isa (.block ((List.range 12).flatMap copyArg)) w (CI s w 12) :=
  wp_range_flatMap (M := isa) (CI s w) (fun _ _ hn hc => copy_step h hw12 hrd hwr hm hn hc) 12 (Nat.le_refl _) w
    ⟨Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem callArgs_ok {s u : State} (h : SPre s) (A : AtAft s u) {em : List Byte}
    (hem : Spec.Rsa.bytesAt u.mem (fb s + BitVec.ofNat 64 oEM) (s.gpr .r6).toNat = em) :
    WP isa (.block callArgs) u fun t => AtCall s t em := by
  have hk := h.k2
  unfold callArgs
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r12] (Q := fun w => w.gpr .r12 = fb s ∧ w.mem = u.mem) ?_ rfl)
    fun w ⟨⟨w12, wm⟩, kw⟩ => ?_
  · prun [exec_addSp0, A.sp]
  rw [WP.block_append_iff]
  refine WP.mono (copies_ok h w12 (kw.rd.trans A.rd) (kw.wr.trans A.wr) (wm ▸ A.mem)) fun v hc => ?_
  have v12 : v.gpr .r12 = fb s := (hc.keep.gpr _ (by decide)).trans w12
  have c1 : oEM < 2 ^ 15 := by decide
  have kv : ∀ r, r ≠ .r12 → r ≠ .r0 → v.gpr r = u.gpr r := fun r h1 h2 =>
    (hc.keep.gpr r (by simpa using h2)).trans (kw.gpr r (by simpa using h1))
  refine WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10] (Q := fun t =>
    t.gpr .r3 = s.gpr .r3 ∧ t.gpr .r4 = s.gpr .r6 ∧ t.gpr .r5 = s.gpr .r5 ∧ t.gpr .r6 = s.gpr .r6 ∧
      t.gpr .r7 = s.gpr .r7 ∧ t.gpr .r8 = s.gpr .r8 ∧ t.gpr .r9 = fb s + BitVec.ofNat 64 oEM ∧
      t.gpr .r10 = s.gpr .r6 ∧ t.mem = v.mem) ?_ rfl) fun t ⟨⟨t3, t4, t5, t6, t7, t8, t9, t10, tm⟩, kt⟩ => ?_
  · prun [v12, c1, kv .r26 (by decide) (by decide), kv .r27 (by decide) (by decide),
      kv .r28 (by decide) (by decide), kv .r29 (by decide) (by decide), kv .r30 (by decide) (by decide),
      A.r26, A.r27, A.r28, A.r29, A.r30, BitVec.or_self, exec_addi (show Reg.r12 ≠ .r0 by decide) c1,
      Impl.AesGcm.PPC64LE.mov]
  have psa_sub : Region.Sub (psaR s) (kR s) := frame_sub s (by decide)
  have hm : Frame [psaR s] u.mem t.mem := by rw [tm, ← wm]; exact hc.mem
  have hd : ∀ {d n : Nat}, 96 + 96 ≤ d → d + n ≤ frameBytes →
      ∀ r ∈ [psaR s], Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, n⟩ r :=
    fun hdn hdn' r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inr hdn) (by unfold frameBytes at hdn'; omega) (by decide)
  have kk : ∀ r, r ∉ [Reg.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r12, .r0] → t.gpr r = u.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [kt.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1]), kv r hr.2.2.2.2.2.2.2.2.1 hr.2.2.2.2.2.2.2.2.2]
  refine ⟨⟨kt.sp.trans (hc.keep.sp.trans (kw.sp.trans A.sp)), kt.rd.trans (hc.keep.rd.trans (kw.rd.trans A.rd)),
    kt.wr.trans (hc.keep.wr.trans (kw.wr.trans A.wr)), kt.lr.trans (hc.keep.lr.trans (kw.lr.trans A.lr)),
    fun r hr => (kk r (by revert r; decide)).trans (A.hi r hr),
    A.mem.trans (hm.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, psa_sub⟩),
    A.sv.frame hm fun p hp => by
      have := saved_offs p hp; exact hd (by unfold oSave at this; omega) (by unfold oSave frameBytes at *; omega),
    ?_⟩, ?_, t3, t4, t5, t6, t7, t8, t9, t10, (kk _ (by decide)).trans A.r26, (kk _ (by decide)).trans A.r28,
    fun i hi => by rw [tm]; exact hc.psa i hi⟩
  · rw [hm.readW (Region.contains_self _ _) (hd (by decide) (by decide)) (by decide)]; exact A.ls
  · rw [← hem]
    exact bytes_of_frame (s := u) hm (hd (by decide) (by unfold oEM frameBytes; omega)) (by omega)

end VG.Proof.RsaPkcs1Sig.PPC64LE.Sign
