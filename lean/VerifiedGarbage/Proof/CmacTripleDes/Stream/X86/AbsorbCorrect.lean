module

import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86.Absorb
public import VerifiedGarbage.Proof.Framework.Omega
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic.Conv
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.CmacTripleDes.Stream.X86
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86.Contract
public import VerifiedGarbage.Proof.CmacTripleDes.X86.RoundLit
public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.TripleDes.SboxTables
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.CmacTripleDes.X86.Update
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.CmacTripleDes.X86.Finalize
import VerifiedGarbage.Proof.CmacTripleDes.X86.Init

/-!
# Streaming TDEA-CMAC on x86: `vg_cmac_triple_des_absorb` is correct

After `absorbPre`, the first run of `update` chains the block held back if
data is left (`b1`), the second the whole blocks of the data left but its
last 1 to 8 bytes (`nb`), and the last copy holds those back. If no data is
left (`len ≤ 8 - h`), the runs chain nothing and the copy copies nothing,
and the data is appended to the bytes held back (`repr_fill`); otherwise
`repr_chain`.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.X86

open VG VG.X86 VG.Impl.CmacTripleDes.Stream.X86

open VG.WriteBytes

open VG.Proof.CmacTripleDes.Stream (held held_le)
open VG.Proof.CmacTripleDes.X86 (ciphAt scheduleAt_frame)

theorem frame_at {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hp : p.toNat + n ≤ 2 ^ 64) {i : Nat} (hi : i < n) :
    m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) :=
  hf _ fun r hr hc => hd r hr _ (Offset.contains_base p (by omega_using [hi]) (by omega_using [hp, hi])) hc

theorem blocksAt_zero (m : Mem) (p : Addr) : Spec.Cmac.blocksAt m p 8 0 = [] := rfl

theorem blocksAt_one (m : Mem) (p : Addr) :
    Spec.Cmac.blocksAt m p 8 1 = [Spec.Aes.bytesAt m p 8] := by
  simp [Spec.Cmac.blocksAt, k0]
where k0 : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

theorem bytesAt_zero (m : Mem) (p : Addr) : Spec.Aes.bytesAt m p 0 = [] := rfl

theorem absorb_wp {s₀ : State} (h0 : absorbX86.pre s₀) :
    WP isa absorb s₀ fun s' => abiPreserved s₀ s' ∧ absorbX86.post s₀ s' := by
  have hp := APre.of h0
  have hL := hp.lt
  have fSt : (aSt s₀).toNat + 416 ≤ 2 ^ 32 := hp.fSt
  have fD : (aD s₀).toNat + aL s₀ ≤ 2 ^ 32 := hp.fD
  have fS : (aSc s₀).toNat + 688 ≤ 2 ^ 32 := hp.fS
  have e24 := hp.esp24
  have ⟨hfL, hfh⟩ := f_le (aC s₀) (aL s₀)
  have hsum := nb_le (aC s₀) (aL s₀)
  have hrr := rest_le (aC s₀) (aL s₀)
  have hh := held_le (aC s₀)
  unfold absorb
  refine WP.seq (WP.mono (absorbPre_wp hp) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (upd_wp h₅.args) fun s₆ h₆ => ?_)
  have a₆ := upd_aft hp (h₅.mem ▸ m4_big hp) h₅.ctx h₅.ebp h₆
  refine WP.seq (WP.mono (chain2_mid hp a₆) fun s₇ ⟨h₇, m₇⟩ => ?_)
  refine WP.seq (WP.mono (upd_wp h₇.args) fun s₈ h₈ => ?_)
  have a₈ := upd_aft hp h₇.aft.frame h₇.aft.ctx h₇.aft.ebp h₈
  unfold absorbPost
  refine WP.seq (WP.mono (rest_wp hp a₈.ctx a₈.ebp) fun s₉ h₉ => ?_)
  -- The last copy.
  have hsrc : 0 < restOf (aC s₀) (aL s₀) →
      (aD s₀ + BitVec.ofNat 32 (fOf (aC s₀) (aL s₀) + 8 * nbOf (aC s₀) (aL s₀))).setWidth 64 =
        (aD s₀).setWidth 64 + BitVec.ofNat 64 (fOf (aC s₀) (aL s₀) + 8 * nbOf (aC s₀) (aL s₀)) :=
    fun _ => add_setWidth (by omega_arith)
  have p408 : (aSt s₀ + BitVec.ofNat 32 408).setWidth 64 = (aSt s₀).setWidth 64 + BitVec.ofNat 64 408 :=
    add_setWidth (by omega_using [fSt])
  refine WP.seq (WP.mono (copy_wp (L := restOf (aC s₀) (aL s₀)) (by omega_using [hrr]) h₉.esi h₉.edi h₉.ecx
    (fun _ => by rw [add_toNat (by omega_arith)]; omega_using [fD, hsum]) (fun _ => by rw [add_toNat (by omega_using [fSt])]; omega_using [fSt, hrr])
    (fun h => by
      rw [h₉.ctx.rd, h₉.ctx.wr, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨adR s₀, by simp, _, hsrc h, by simp; omega_using [hsum]⟩)
    (fun _ => by
      rw [h₉.ctx.wr, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨astR s₀, by simp, 408, p408, by simp; omega_using [hrr]⟩)
    (fun h => by
      rw [hsrc h, p408]
      exact (hp.st_d.sub_left (Offset.sub_base (d := 408) (n := restOf (aC s₀) (aL s₀)) _ (by omega_using [hrr]))).symm.sub_left
        (Offset.sub_base (d := fOf (aC s₀) (aL s₀) + 8 * nbOf (aC s₀) (aL s₀)) (n := restOf (aC s₀) (aL s₀)) _
          (by omega_using [hsum])))) fun s₁₀ h₁₀ => ?_)
  obtain ⟨m₁₀, g₁₀, rd₁₀, wr₁₀⟩ := h₁₀
  -- The frames.
  have f6 : Frame [⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 400, 8⟩, ⟨(aSc s₀).setWidth 64, 640⟩,
      below (aE s₀) 24] s₅.mem s₆.mem := by
    have := h₆.frame; rw [h₅.ctx.esp, add_setWidth (by omega_using [fSt])] at this; exact this
  have f8 : Frame [⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 400, 8⟩, ⟨(aSc s₀).setWidth 64, 640⟩,
      below (aE s₀) 24] s₆.mem s₈.mem := by
    have := h₈.frame; rw [h₇.aft.ctx.esp, add_setWidth (by omega_using [fSt]), m₇] at this; exact this
  have m₁₀' : s₁₀.mem = writeBytes s₈.mem ((aSt s₀).setWidth 64 + BitVec.ofNat 64 408)
      (Spec.Aes.bytesAt s₈.mem ((aD s₀).setWidth 64 + BitVec.ofNat 64 (fOf (aC s₀) (aL s₀) + 8 * nbOf (aC s₀) (aL s₀)))
        (restOf (aC s₀) (aL s₀))) := by
    rw [m₁₀, h₉.mem, p408]
    by_cases hr0 : restOf (aC s₀) (aL s₀) = 0
    · rw [hr0, bytesAt_zero, bytesAt_zero]
    · rw [hsrc (by omega_using [hr0])]
  have hlr : (Spec.Aes.bytesAt s₈.mem ((aD s₀).setWidth 64 + BitVec.ofNat 64 (fOf (aC s₀) (aL s₀) +
      8 * nbOf (aC s₀) (aL s₀))) (restOf (aC s₀) (aL s₀))).length = restOf (aC s₀) (aL s₀) :=
    Proof.Cmac.bytesAt_length _ _ _
  have fC2 : Frame [⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 408, restOf (aC s₀) (aL s₀)⟩] s₈.mem s₁₀.mem := by
    rw [m₁₀']; exact writeBytes_frame _ _ _ (by rw [hlr]; exact Region.contains_self _ _)
  have fSv : Frame [⟨(aSc s₀).setWidth 64 + BitVec.ofNat 64 640, 16⟩] s₀.mem (savedMem s₀ (aSc s₀)) :=
    savedMem_frame _ _
  have fC1 : Frame [⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 (408 + held (aC s₀)), fOf (aC s₀) (aL s₀)⟩]
      (savedMem s₀ (aSc s₀)) s₅.mem := by rw [h₅.mem]; exact m4_frame s₀
  let K : List Region := [⟨(aSc s₀).setWidth 64 + BitVec.ofNat 64 640, 16⟩,
    ⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 (408 + held (aC s₀)), fOf (aC s₀) (aL s₀)⟩,
    ⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 400, 8⟩, ⟨(aSc s₀).setWidth 64, 640⟩, below (aE s₀) 24,
    ⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 408, restOf (aC s₀) (aL s₀)⟩]
  have F5 : Frame K s₀.mem s₅.mem := (fSv.mono (by simp [K])).trans (fC1.mono (by simp [K]))
  have F6 : Frame K s₀.mem s₆.mem := F5.trans (f6.mono (by simp [K]))
  have F8 : Frame K s₀.mem s₈.mem := F6.trans (f8.mono (by simp [K]))
  have F10 : Frame K s₀.mem s₁₀.mem := F8.trans (fC2.mono (by simp [K]))
  have KB : Frame (ABig s₀) s₀.mem s₁₀.mem := F10.sub fun r hr => by
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ascR s₀, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨astR s₀, by simp, Offset.sub_base _ (by omega_using [hfh])⟩
    · exact ⟨astR s₀, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨ascR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨astR s₀, by simp, Offset.sub_base _ (by omega_using [hrr])⟩
  -- The saved registers.
  have slots : ∀ r d, (r, d) ∈ saved →
      s₁₀.mem.readW ((aSc s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.gpr r := fun r d hrd => by
    have hb := saved_bound _ hrd
    have Fp : Frame K.tail (savedMem s₀ (aSc s₀)) s₁₀.mem :=
      ((fC1.mono (by simp [K])).trans (f6.mono (by simp [K]))).trans
        ((f8.mono (by simp [K])).trans (fC2.mono (by simp [K])))
    have sub : Region.Sub ⟨(aSc s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩ (ascR s₀) := Offset.sub_base _ (by omega_using [hb])
    rw [Fp.readW (Region.contains_self _ _) (fun q hq => ?_) (by decide)]
    · exact saveMem_slot _ _ _ hrd
    simp only [K, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact (hp.st_s.sub_left (Offset.sub_base _ (by omega_using [hfh]))).symm.sub_left sub
    · exact (hp.st_s.sub_left (Offset.sub_base _ (by decide))).symm.sub_left sub
    · exact Offset.disjoint_base _ (by omega_using [hb]) (by omega_using [hb])
    · exact hp.b_s.symm.sub_left sub
    · exact (hp.st_s.sub_left (Offset.sub_base _ (by omega_using [hrr]))).symm.sub_left sub
  have esp₁₀ : s₁₀.gpr .esp = aE s₀ := by
    rw [g₁₀ _ (by decide) (by decide) (by decide) (by decide), h₉.ctx.esp]
  refine WP.mono (restore_wp (s₀ := s₀) (i := 5) (Sc := aSc s₀) esp₁₀
    (by rw [rd₁₀, wr₁₀, h₉.ctx.rd, h₉.ctx.wr]; exact hp.arg_in (by decide)) (hp.keep KB (by decide)) fS (by
      rw [rd₁₀, wr₁₀, h₉.ctx.rd, h₉.ctx.wr, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨ascR s₀, by simp, 0, by simp, by simp⟩) slots)
    fun s₁₁ ⟨hcs, m₁₁⟩ => ?_
  have F11 : Frame K s₀.mem s₁₁.mem := m₁₁ ▸ F10
  -- The key, the data and the return address are in none of these.
  have dK : ∀ r ∈ K, (⟨(aSt s₀).setWidth 64, 400⟩ : Region).Disjoint r := by
    intro r hr
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide))
    · exact Offset.base_disjoint _ (by omega_using []) (by omega_using [hfh])
    · exact Offset.base_disjoint _ (by omega_using []) (by omega_using [])
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    · exact (hp.b_st.sub_right (Region.sub_prefix (by decide))).symm
    · exact Offset.base_disjoint _ (by omega_using []) (by omega_using [hrr])
  have dDat : ∀ r ∈ K, (adR s₀).Disjoint r := by
    intro r hr
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hp.d_s.sub_right (Offset.sub_base _ (by decide))
    · exact hp.st_d.symm.sub_right (Offset.sub_base _ (by omega_using [hfh]))
    · exact hp.st_d.symm.sub_right (Offset.sub_base _ (by decide))
    · exact hp.d_s.sub_right (Region.sub_prefix (by decide))
    · exact hp.b_d.symm
    · exact hp.st_d.symm.sub_right (Offset.sub_base _ (by omega_using [hrr]))
  have dRet : ∀ r ∈ K, (⟨(aE s₀).setWidth 64, 4⟩ : Region).Disjoint r := by
    intro r hr
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hp.ret_s.sub_right (Offset.sub_base _ (by decide))
    · exact hp.ret_st.sub_right (Offset.sub_base _ (by omega_using [hfh]))
    · exact hp.ret_st.sub_right (Offset.sub_base _ (by decide))
    · exact hp.ret_s.sub_right (Region.sub_prefix (by decide))
    · exact ret_below e24
    · exact hp.ret_st.sub_right (Offset.sub_base _ (by omega_using [hrr]))
  refine ⟨⟨hcs, F11.readW (r := ⟨(aE s₀).setWidth 64, 4⟩) (Region.contains_self _ _) dRet (by decide)⟩, ?_⟩
  intro key msg hr hcnt hlen
  show Spec.Cmac.tdesRepr s₁₁.mem ((aSt s₀).setWidth 64) key
    (msg ++ Spec.Aes.bytesAt s₀.mem ((aD s₀).setWidth 64) (aL s₀))
  have hcm : aC s₀ = msg.length := by
    show (countX86 s₀).toNat = _
    rw [hcnt, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [hlen])
  have hsch := ((Proof.CmacTripleDes.Stream.repr_iff _ _ _ _).mp hr).1.2.1
  have ciph : ∀ m : Mem, Frame K s₀.mem m → ciphAt m ((aSt s₀).setWidth 64) = Spec.Cmac.tdes key := fun m hf => by
    simp only [ciphAt, Spec.Cmac.tdes]
    rw [scheduleAt_frame hf fun r hr => (dK r hr).sub_left (Region.sub_prefix (by decide)), hsch]
  -- The data, wherever it is read.
  have dat : ∀ m : Mem, Frame K s₀.mem m → ∀ a b : Nat, a + b ≤ aL s₀ →
      Spec.Aes.bytesAt m ((aD s₀).setWidth 64 + BitVec.ofNat 64 a) b =
        ((Spec.Aes.bytesAt s₀.mem ((aD s₀).setWidth 64) (aL s₀)).drop a).take b := fun m hf a b hab => by
    rw [Proof.Cmac.Stream.bytesAt_offset m _ hab, Proof.Cmac.bytesAt_frame hf dDat (by omega_using [fD])]
  have fS' : Frame K s₀.mem (savedMem s₀ (aSc s₀)) := fSv.mono (by simp [K])
  -- The chaining value.
  have cv5 : Spec.Aes.bytesAt s₅.mem ((aSt s₀).setWidth 64 + BitVec.ofNat 64 400) 8 =
      Spec.Aes.bytesAt s₀.mem ((aSt s₀).setWidth 64 + BitVec.ofNat 64 400) 8 := by
    rw [Proof.Cmac.bytesAt_frame fC1 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega_using []) (by omega_using []) (by omega_using [hfh]))
        (by decide),
      Proof.Cmac.bytesAt_frame fSv (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.st_s.sub_left (Offset.sub_base _ (by decide))).sub_right (Offset.sub_base _ (by decide)))
        (by decide)]
  have cv11 : Spec.Aes.bytesAt s₁₁.mem ((aSt s₀).setWidth 64 + BitVec.ofNat 64 400) 8 =
      Spec.Aes.bytesAt s₈.mem ((aSt s₀).setWidth 64 + BitVec.ofNat 64 400) 8 := by
    rw [m₁₁]
    exact Proof.Cmac.bytesAt_frame fC2 (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega_using []) (by omega_using []) (by omega_using [hrr]))
      (by decide)
  have out6 := h₆.out
  rw [add_setWidth (by omega_using [fSt]), add_setWidth (by omega_using [fSt]), ciph _ F5] at out6
  have out8 := h₈.out
  rw [add_setWidth (by omega_using [fSt]), m₇, ciph _ F6] at out8
  have hk : ∀ i < 400, s₁₁.mem ((aSt s₀).setWidth 64 + BitVec.ofNat 64 i) =
      s₀.mem ((aSt s₀).setWidth 64 + BitVec.ofNat 64 i) :=
    fun i hi => frame_at F11 dK (by simp only [BitVec.toNat_setWidth]; omega_using []) hi
  have hdl : (Spec.Aes.bytesAt s₀.mem ((aD s₀).setWidth 64) (aL s₀)).length = aL s₀ :=
    Proof.Cmac.bytesAt_length _ _ _
  have hlf : (Spec.Aes.bytesAt (savedMem s₀ (aSc s₀)) ((aD s₀).setWidth 64) (fOf (aC s₀) (aL s₀))).length =
      fOf (aC s₀) (aL s₀) := Proof.Cmac.bytesAt_length _ _ _
  -- The bytes held back so far, and the first `f` bytes of data after them.
  have hb5 : Spec.Aes.bytesAt s₅.mem ((aSt s₀).setWidth 64 + BitVec.ofNat 64 408)
      (held (aC s₀) + fOf (aC s₀) (aL s₀)) =
      Spec.Aes.bytesAt s₀.mem ((aSt s₀).setWidth 64 + BitVec.ofNat 64 408) (held (aC s₀)) ++
        (Spec.Aes.bytesAt s₀.mem ((aD s₀).setWidth 64) (aL s₀)).take (fOf (aC s₀) (aL s₀)) := by
    have e := bytesAt_writeBytes (savedMem s₀ (aSc s₀)) ((aSt s₀).setWidth 64 + BitVec.ofNat 64 408) (held (aC s₀))
      (Spec.Aes.bytesAt (savedMem s₀ (aSc s₀)) ((aD s₀).setWidth 64) (fOf (aC s₀) (aL s₀))) (by rw [hlf]; omega_using [hfh])
    rw [hlf] at e
    rw [h₅.mem, m4, ← Offset.add_add, e,
      Proof.Cmac.bytesAt_frame fSv (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.st_s.sub_left (Offset.sub_base _ (by omega_using [hh]))).sub_right (Offset.sub_base _ (by decide)))
        (by omega_using [hh])]
    refine congrArg (_ ++ ·) ?_
    have := dat _ fS' 0 (fOf (aC s₀) (aL s₀)) (by omega_using [hsum])
    rwa [BitVec.add_zero, List.drop_zero] at this
  generalize hd : Spec.Aes.bytesAt s₀.mem ((aD s₀).setWidth 64) (aL s₀) = d at hdl hb5 dat ⊢
  by_cases hx : leftOf (aC s₀) (aL s₀) = 0
  · -- Everything fits in the block held back.
    have hfL' : fOf (aC s₀) (aL s₀) = aL s₀ := by unfold leftOf at hx; omega_using [hsum, hx]
    have hb : b1Of (aC s₀) (aL s₀) = 0 := by simp [b1Of, hx]
    have hn : nbOf (aC s₀) (aL s₀) = 0 := by simp [nbOf, hx]
    have hr0 : restOf (aC s₀) (aL s₀) = 0 := rest_zero hx
    have m118 : s₁₁.mem = s₈.mem := by
      rw [m₁₁, m₁₀', hr0, bytesAt_zero, writeBytes_nil]
    refine Proof.CmacTripleDes.Stream.repr_fill hr hk (by rw [hdl, ← hcm]; omega_using [hfh, hfL']) ?_ ?_
    · show Spec.Aes.bytesAt _ ((aSt s₀).setWidth 64 + BitVec.ofNat 64 400) _ =
        Spec.Aes.bytesAt _ ((aSt s₀).setWidth 64 + BitVec.ofNat 64 400) _
      rw [cv11, out8, hn, blocksAt_zero, out6, hb, blocksAt_zero]
      exact cv5
    · show Spec.Aes.bytesAt _ ((aSt s₀).setWidth 64 + BitVec.ofNat 64 408) _ =
        Spec.Aes.bytesAt _ ((aSt s₀).setWidth 64 + BitVec.ofNat 64 408) _ ++ _
      rw [← hcm, hdl]
      have sub : Region.Sub ⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 408, held (aC s₀) + aL s₀⟩ (astR s₀) :=
        Offset.sub_base _ (by omega_using [hfh, hfL'])
      have dj : ∀ r ∈ [⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 400, 8⟩, ⟨(aSc s₀).setWidth 64, 640⟩,
          below (aE s₀) 24], (⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 408, held (aC s₀) + aL s₀⟩ : Region).Disjoint r := by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Offset.disjoint _ (by omega_using []) (by omega_using [hfh, hfL']) (by omega_using [])
        · exact (hp.st_s.sub_left sub).sub_right (Region.sub_prefix (by decide))
        · exact (hp.b_st.sub_right sub).symm
      have hb5' := hb5
      rw [hfL', List.take_of_length_le (by rw [hdl])] at hb5'
      rw [m118, Proof.Cmac.bytesAt_frame f8 dj (by omega_using [hfh, hfL']), Proof.Cmac.bytesAt_frame f6 dj (by omega_using [hfh, hfL']), hb5']
  · -- The block held back is complete, and more blocks may follow.
    have hlt : 8 - held (aC s₀) < aL s₀ := by unfold leftOf fOf at hx; omega_using [hx]
    have hf' : fOf (aC s₀) (aL s₀) = 8 - held (aC s₀) := by unfold fOf; omega_using [hlt]
    have hb : b1Of (aC s₀) (aL s₀) = 1 := by simp [b1Of, hx]
    have hn : nbOf (aC s₀) (aL s₀) = Proof.CmacTripleDes.Stream.nblocks (aC s₀) (aL s₀) := by
      simp only [nbOf, hx, ↓reduceIte]
      unfold leftOf Proof.CmacTripleDes.Stream.nblocks
      rw [hf']
    have hd2 : (d2Of s₀).setWidth 64 = (aD s₀).setWidth 64 + BitVec.ofNat 64 (fOf (aC s₀) (aL s₀)) := by
      simp only [d2Of, hx, ↓reduceIte]; exact add_setWidth (by omega_using [fD, hlt, hf'])
    have hb5' := hb5
    rw [hf', Nat.add_sub_cancel' hh] at hb5'
    refine Proof.CmacTripleDes.Stream.repr_chain hr hk (by rw [hdl, ← hcm]; exact hlt) ?_ ?_
    · show Spec.Aes.bytesAt _ ((aSt s₀).setWidth 64 + BitVec.ofNat 64 400) _ =
        Spec.Cmac.chain _ (Spec.Aes.bytesAt _ ((aSt s₀).setWidth 64 + BitVec.ofNat 64 400) _)
          ([Spec.Aes.bytesAt _ ((aSt s₀).setWidth 64 + BitVec.ofNat 64 408) _ ++ _] ++ _)
      rw [← hcm, hdl]
      rw [cv11, out8, out6, hb, blocksAt_one, cv5, Proof.Cmac.chain_append, hd2, Proof.CmacTripleDes.Stream.blocksAt_eq,
        dat _ F6 _ _ (by omega_using [hsum]), hb5', hf', hn]
    · show Spec.Aes.bytesAt _ ((aSt s₀).setWidth 64 + BitVec.ofNat 64 408) _ = _
      rw [← hcm, hdl]
      have e := bytesAt_writeBytes_self s₈.mem ((aSt s₀).setWidth 64 + BitVec.ofNat 64 408)
        (xs := Spec.Aes.bytesAt s₈.mem ((aD s₀).setWidth 64 + BitVec.ofNat 64 (fOf (aC s₀) (aL s₀) +
          8 * nbOf (aC s₀) (aL s₀))) (restOf (aC s₀) (aL s₀))) (by rw [hlr]; omega_using [hrr])
      rw [hlr] at e
      have hr' : aL s₀ - (8 - held (aC s₀)) - 8 * Proof.CmacTripleDes.Stream.nblocks (aC s₀) (aL s₀) =
          restOf (aC s₀) (aL s₀) := by
        rw [← hn, ← hf']; rfl
      rw [hr', m₁₁, m₁₀', e, dat _ F8 _ _ (by omega_using [hsum]),
        List.take_of_length_le (by simp only [List.length_drop, hdl]; unfold restOf leftOf; omega_using []),
        List.drop_drop, ← hn, hf']

end VG.Proof.CmacTripleDes.Stream.X86
