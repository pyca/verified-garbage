module

public import VerifiedGarbage.Proof.Ed448.PPC64LE.VChecks
public import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Ed448.PPC64LE.BaseInit
import VerifiedGarbage.Proof.Ed448.PPC64LE.BaseBits
import VerifiedGarbage.Proof.Ed448.PPC64LE.BaseSel
import VerifiedGarbage.Proof.X448.Field
import VerifiedGarbage.Proof.X448.PPC64LE.Invert
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.X25519.PPC64LE.Pass

/-!
# Ed448's verification on PPC64LE: the setup

`vSetup` copies the inputs into the working space (`copyB_ok`), points `r3`
at `OUT`, clears `BAD`, and writes `d`, `B` and 1 (`vSetup_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE VG.Proof.X448.PPC64LE
open VG.Proof.X25519.PPC64LE hiding V FS V_lt pass_ok limb_frame
open VG.Spec.X448 (P Fe)

section
variable {b : Addr}

/-- After `k` bytes of a copy from `src` to `o`. -/
structure CopyInv (b src : Addr) (o : Nat) (s0 : State) (k : Nat) (s : State) : Prop where
  rest : Rest [.r7] s0 s
  frame : Frame [⟨b + BitVec.ofNat 64 o, k⟩] s0.mem s.mem
  bytes : ∀ i < k, s.mem (b + BitVec.ofNat 64 (o + i)) = s0.mem (src + BitVec.ofNat 64 i)

theorem copyB_ok {s0 : State} (hc : Ctx b s0) {rs : Reg} (hrs : rs ≠ .r0 ∧ rs ≠ .r7 ∧ rs ≠ .r6) {src : Addr}
    (h : s0.gpr rs = src) {n o : Nat} (hin : (⟨src, n⟩ : Region) ∈ s0.rd ++ s0.wr)
    (hd : Region.Disjoint ⟨src, n⟩ ⟨b + BitVec.ofNat 64 o, n⟩) (ho : o + n ≤ 4096) (hn : n < 2 ^ 15) :
    WP isa (.block (copyBytes rs o n)) s0 (CopyInv b src o s0 n) := by
  obtain ⟨h0, h7, h6⟩ := hrs
  refine wp_range_flatMap (M := isa) (CopyInv b src o s0) (fun k s hk h' => ?_) n (Nat.le_refl _) s0
    ⟨Rest.refl _ _, Frame.refl _ _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  have hcs : Ctx b s := hc.of_rest h'.rest (by decide)
  refine wp_lbz (a := src + BitVec.ofNat 64 k) h0 (by omega) (by rw [h'.rest.gpr _ (by simpa using h7), h])
    (by rw [h'.rest.rd, h'.rest.wr]; exact in_base hin (by omega) (by omega)) fun s1 u1 => ?_
  refine wp_stb (a := b + BitVec.ofNat 64 (o + k)) (by decide) (by omega)
    (by rw [u1.other _ (by decide), h'.rest.gpr _ (by decide), hc.r6])
    (by rw [u1.wr, h'.rest.wr]; exact hc.inW (by omega)) fun s2 u2 => WP.block_nil ?_
  have hm2 : s2.mem = s.mem.writeW (b + BitVec.ofNat 64 (o + k)) ((s1.gpr .r7).setWidth 8) := by rw [u2.mem, u1.mem]
  have hsrc : s.mem (src + BitVec.ofNat 64 k) = s0.mem (src + BitVec.ofNat 64 k) :=
    h'.frame _ fun r hr hcon => by
      rw [List.mem_singleton.mp hr] at hcon
      exact hd _ (Offset.contains_base _ (by omega) (by omega)) (Region.sub_prefix (by omega) _ hcon)
  refine ⟨h'.rest.trans ((u1.rest (by decide)).trans (u2.rest _)), ?_, fun i hi => ?_⟩
  · rw [hm2]
    exact (h'.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (Nat.le_add_right _ _) (by omega) (by omega))
  · rw [hm2, VG.WriteBytes.writeW8_apply]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [X448.PPC64LE.iteF (Offset.add_ofNat_ne _ (by omega) (by omega) (by omega))]; exact h'.bytes i hi
    · rw [X448.PPC64LE.iteT rfl, u1.gpr, ← hsrc]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      have := (s.mem (src + BitVec.ofNat 64 i)).isLt
      omega

/-- The bytes of a region apart from a frame's regions stay. -/
theorem bytes_keep {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n < 2 ^ 64) :
    Spec.Ed448.bytesAt m' p n = Spec.Ed448.bytesAt m p n := by
  simp only [Spec.Ed448.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  exact hf _ fun r hr hc => hd r hr _ (Offset.contains_base _ (by omega) (by omega)) hc

theorem bytes_copy {m m0 : Mem} {src : Addr} {o n : Nat}
    (h : ∀ i < n, m (b + BitVec.ofNat 64 (o + i)) = m0 (src + BitVec.ofNat 64 i)) :
    Spec.Ed448.bytesAt m (b + BitVec.ofNat 64 o) n = Spec.Ed448.bytesAt m0 src n := by
  simp only [Spec.Ed448.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  rw [Offset.add_add]; exact h i (List.mem_range.mp hi)

/-- The precondition, by register: `pk` in `r3`, the signature in `r4`, the
challenge in `r5` and `scratch` in `r6`. -/
structure VPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r3, 57⟩, ⟨s.gpr .r4, 114⟩, ⟨s.gpr .r5, 57⟩]
  wr : s.wr = [⟨s.gpr .r6, 8192⟩]
  pk_ws : (⟨s.gpr .r3, 57⟩ : Region).Disjoint ⟨s.gpr .r6, 8192⟩
  sig_ws : (⟨s.gpr .r4, 114⟩ : Region).Disjoint ⟨s.gpr .r6, 8192⟩
  ch_ws : (⟨s.gpr .r5, 57⟩ : Region).Disjoint ⟨s.gpr .r6, 8192⟩

/-- The regions the setup writes after the copy of `pk`. -/
abbrev setW (b : Addr) : List Region :=
  [⟨b + BitVec.ofNat 64 SG, 114⟩, ⟨b + BitVec.ofNat 64 CH, 57⟩, ⟨b + BitVec.ofNat 64 BAD, 8⟩,
    ⟨b + BitVec.ofNat 64 DK, 56⟩, ⟨b + BitVec.ofNat 64 BX, 56⟩, ⟨b + BitVec.ofNat 64 BY, 56⟩,
    ⟨b + BitVec.ofNat 64 ONE, 56⟩]

theorem vSetup_ok {s : State} (hp : VPre s) :
    WP isa (.block vSetup) s fun t => VCtx (s.gpr .r6) t ∧ Rest [.r3, .r7] s t ∧
      Frame [⟨s.gpr .r6, 8192⟩] s.mem t.mem ∧
      Spec.Ed448.bytesAt t.mem (s.gpr .r6 + BitVec.ofNat 64 PK) 57 = Spec.Ed448.bytesAt s.mem (s.gpr .r3) 57 ∧
      Spec.Ed448.bytesAt t.mem (s.gpr .r6 + BitVec.ofNat 64 SG) 114 = Spec.Ed448.bytesAt s.mem (s.gpr .r4) 114 ∧
      Spec.Ed448.bytesAt t.mem (s.gpr .r6 + BitVec.ofNat 64 CH) 57 = Spec.Ed448.bytesAt s.mem (s.gpr .r5) 57 ∧
      bad t.mem (s.gpr .r6) = 0 ∧ FS t.mem (s.gpr .r6) DK = Spec.Ed448.d ∧
      FS t.mem (s.gpr .r6) BX = Spec.Ed448.basePoint.X ∧ FS t.mem (s.gpr .r6) BY = Spec.Ed448.basePoint.Y ∧
      FS t.mem (s.gpr .r6) ONE = 1 := by
  obtain ⟨b, hb⟩ : ∃ b, b = s.gpr .r6 := ⟨_, rfl⟩
  rw [← hb]
  obtain ⟨o1, o2, o3, o4⟩ := offs
  have hPK : PK = 3288 := rfl
  have hSG : SG = 3345 := rfl
  have hCH : CH = 3459 := rfl
  have hDK : DK = 336 := rfl
  have hBX : BX = 2896 := rfl
  have hBY : BY = 2952 := rfl
  have hON : ONE = 3232 := rfl
  have hws : (⟨b, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr, hb]; simp
  have hc : Ctx b s := ⟨hb.symm, ⟨8192, by decide, hws⟩⟩
  have sub8 : ∀ {o n : Nat}, o + n ≤ 8192 → Region.Sub ⟨b + BitVec.ofNat 64 o, n⟩ ⟨b, 8192⟩ :=
    fun h => Offset.sub_base _ h
  unfold vSetup
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  -- The copies.
  refine WP.append (copyB_ok hc (rs := .r3) (by decide) rfl (n := 57) (o := PK) (by rw [hp.rd]; simp)
    (hp.pk_ws.sub_right (by rw [← hb]; exact sub8 (by omega))) (by omega) (by decide)) fun s1 h1 => ?_
  have hc1 : Ctx b s1 := hc.of_rest h1.rest (by decide)
  refine WP.append (copyB_ok hc1 (rs := .r4) (by decide) (by rw [h1.rest.gpr _ (by decide)]) (n := 114) (o := SG)
    (by rw [h1.rest.rd, h1.rest.wr, hp.rd]; simp)
    (hp.sig_ws.sub_right (by rw [← hb]; exact sub8 (by omega))) (by omega) (by decide)) fun s2 h2 => ?_
  have hc2 : Ctx b s2 := hc1.of_rest h2.rest (by decide)
  refine WP.append (copyB_ok hc2 (rs := .r5) (by decide)
    (by rw [h2.rest.gpr _ (by decide), h1.rest.gpr _ (by decide)]) (n := 57) (o := CH)
    (by rw [h2.rest.rd, h2.rest.wr, h1.rest.rd, h1.rest.wr, hp.rd]; simp)
    (hp.ch_ws.sub_right (by rw [← hb]; exact sub8 (by omega))) (by omega) (by decide)) fun s3 h3 => ?_
  have hc3 : Ctx b s3 := hc2.of_rest h3.rest (by decide)
  -- `r3`, `BAD` and the constants.
  refine wp_addi (by decide) (by decide) fun s4 u4 => wp_li (by decide) fun s5 u5 => ?_
  have hr5 : Rest [.r3, .r7] s3 s5 := (u4.rest (by decide)).trans (u5.rest (by decide))
  have hc5 : Ctx b s5 := hc3.of_rest hr5 (by decide)
  refine wp_stdd (a := b + BitVec.ofNat 64 BAD) (by decide) (by decide) (by rw [hc5.r6])
    (by rw [hr5.wr, h3.rest.wr, h2.rest.wr, h1.rest.wr]; exact in_base hws (by omega) (by omega)) fun s6 u6 => ?_
  have hc6 : Ctx b s6 := hc5.of_rest (u6.rest []) (by decide)
  have hm6 : s6.mem = s3.mem.writeW (b + BitVec.ofNat 64 BAD) (BitVec.ofNat 64 0) := by
    rw [u6.mem, u5.gpr, u5.mem, u4.mem]
  refine WP.append (constField_ok hc6 (o := DK) (by decide) (fe_lt _)) fun s7 ⟨r7, f7, v7⟩ => ?_
  have hc7 := hc6.of_rest r7 (by decide)
  refine WP.append (constField_ok hc7 (o := BX) (by decide) (fe_lt _)) fun s8 ⟨r8, f8, v8⟩ => ?_
  have hc8 := hc7.of_rest r8 (by decide)
  refine WP.append (constField_ok hc8 (o := BY) (by decide) (fe_lt _)) fun s9 ⟨r9, f9, v9⟩ => ?_
  have hc9 := hc8.of_rest r9 (by decide)
  refine WP.mono (constField_ok hc9 (o := ONE) (by decide) (v := 1) (by decide)) fun t ⟨rt, ft, vt⟩ => ?_
  -- The frames.
  have fB : Frame [⟨b + BitVec.ofNat 64 BAD, 8⟩] s3.mem s6.mem := by
    rw [hm6]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ (64 / 8))
  let L3 : List Region := (setW b).drop 2
  let L2 : List Region := (setW b).drop 1
  have F3 : Frame L3 s3.mem t.mem := by
    refine (fB.mono (by simp [L3])).trans ((f7.mono (by simp [L3])).trans ((f8.mono (by simp [L3])).trans
      ((f9.mono (by simp [L3])).trans (ft.mono (by simp [L3])))))
  have F2 : Frame L2 s2.mem t.mem :=
    (h3.frame.mono (by simp [L2])).trans (F3.mono fun r hr => by
      simp only [L3, L2, List.drop, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h | h | h <;> simp [h])
  have F1 : Frame (setW b) s1.mem t.mem :=
    (h2.frame.mono (by simp)).trans (F2.mono fun r hr => by
      simp only [L2, List.drop, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h | h | h | h <;> simp [h])
  have sw : ∀ r ∈ setW b, Region.Sub r ⟨b, 8192⟩ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact sub8 (by omega)
  have hrt : Rest [.r3, .r7] s t := (h1.rest.mono (by decide)).trans ((h2.rest.mono (by decide)).trans
    ((h3.rest.mono (by decide)).trans (hr5.trans ((u6.rest _).trans ((r7.mono (by decide)).trans
      ((r8.mono (by decide)).trans ((r9.mono (by decide)).trans (rt.mono (by decide)))))))))
  -- The values.
  refine ⟨⟨hc9.of_rest rt (by decide), by rw [hrt.wr]; exact hws, ?_⟩, hrt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rt.gpr _ (by decide), r9.gpr _ (by decide), r8.gpr _ (by decide), r7.gpr _ (by decide), u6.gpr,
      u5.other _ (by decide), u4.gpr, hc3.r6]
  · refine (h1.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact sub8 (by omega)⟩).trans (F1.sub fun r hr => ⟨_, List.mem_singleton_self _, sw r hr⟩)
  · rw [bytes_keep F1 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact Offset.disjoint _ (by omega) (by omega) (by omega))
      (by decide), bytes_copy h1.bytes]
  · rw [bytes_keep F2 (fun r hr => by
      simp only [L2, List.drop, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Offset.disjoint _ (by omega) (by omega) (by omega))
      (by decide), bytes_copy h2.bytes,
      bytes_keep h1.frame (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact hp.sig_ws.sub_right (by rw [← hb]; exact sub8 (by omega))) (by decide)]
  · rw [bytes_keep F3 (fun r hr => by
      simp only [L3, List.drop, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact Offset.disjoint _ (by omega) (by omega) (by omega))
      (by decide), bytes_copy h3.bytes,
      bytes_keep h2.frame (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact hp.ch_ws.sub_right (by rw [← hb]; exact sub8 (by omega))) (by decide),
      bytes_keep h1.frame (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact hp.ch_ws.sub_right (by rw [← hb]; exact sub8 (by omega))) (by decide)]
  · have f6t : Frame (L3.drop 1) s6.mem t.mem := by
      refine (f7.mono (by simp [L3])).trans ((f8.mono (by simp [L3])).trans ((f9.mono (by simp [L3])).trans
        (ft.mono (by simp [L3]))))
    unfold bad
    rw [f6t.readW (Region.contains_self _ (64 / 8)) (fun r hr => by
        simp only [L3, List.drop, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide),
      hm6, Mem.readW_writeW_self64]
    rfl
  · rw [FS, slot_keep ft (by omega) (by omega) (by omega), slot_keep f9 (by omega) (by omega) (by omega),
      slot_keep f8 (by omega) (by omega) (by omega), v7, VG.Proof.X448.toFe_self]
  · rw [FS, slot_keep ft (by omega) (by omega) (by omega), slot_keep f9 (by omega) (by omega) (by omega), v8,
      VG.Proof.X448.toFe_self]
  · rw [FS, slot_keep ft (by omega) (by omega) (by omega), v9, VG.Proof.X448.toFe_self]
  · rw [FS, vt, VG.Proof.X448.toFe_one]

end

end VG.Proof.Ed448.PPC64LE
