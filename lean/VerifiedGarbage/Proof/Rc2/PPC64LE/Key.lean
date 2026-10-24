module

public import VerifiedGarbage.Proof.Rc2.PPC64LE.KeyLoop
import VerifiedGarbage.Proof.Rc2.PPC64LE.KeyInit
import VerifiedGarbage.Proof.Rc2.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Rc2.PPC64LE.ExpandKey
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep

/-!
# RC2 on PPC64LE: key expansion

`expandKey_wp`: the schedule at `r6` becomes the expansion of the key at
`r3`; our caller's `r14` and `r15` are saved in the working space at `r7`
and restored.
-/

@[expose] public section

namespace VG.Proof.Rc2.PPC64LE

open VG VG.PPC64LE VG.Impl.Rc2.PPC64LE

theorem copyFill_run {K S W : Addr} {len bits : Nat} {key : List Byte} {g : Reg → BitVec 64}
    (R : KRegions K S W len) (hk : key.length = len) (s : State) (E : KEnv K S W len bits key g s)
    (h8 : s.gpr .r8 = 0#64) :
    WP isa expandCopyFill s fun t =>
      KEnv K S W len bits key g t ∧ Proof.Rc2.BytesPrefix t.mem S (Proof.Rc2.fill key (128 - len)) 128 := by
  have hl := R.hlen
  unfold expandCopyFill
  apply WP.seq
  refine WP.mono (copy_loop R s E h8) fun t₁ ⟨E₁, a₁, P₁⟩ => ?_
  apply WP.seq
  refine WP.mono (WP.keep [.r0] (c := .block [.li .r0 128, .sub .r0 .r8 .r0]) (Q := fun t =>
      t.gpr .r0 = BitVec.ofNat 64 len - BitVec.ofNat 64 128 ∧ t.mem = t₁.mem) (by rrun [a₁])
    (by simp [writesOnly, Code.allInstrs_eq, instrs, dstOf]) rfl) fun t₂ ⟨⟨a₂, m₂⟩, k₂⟩ => ?_
  have E₂ := E₁.keep k₂ (by decide) m₂
  have hb : isa.eval (.zero .d .r0) t₂ = some (decide (len = 128)) := by
    rw [eval_zero, a₂]
    exact congrArg some (Offset.ofNat_sub_ofNat_beq (by omega) (by omega))
  refine WP.ite _ hb (fun ht => WP.block_nil ⟨E₂, ?_⟩) (fun hf => ?_)
  · have e : len = 128 := of_decide_eq_true ht
    rw [m₂, e, Nat.sub_self]; rw [e] at P₁; exact P₁
  · have e : len ≠ 128 := of_decide_eq_false hf
    exact WP.mono (fill_loop R hk (by omega) t₂ E₂ (by rw [k₂.gpr (by decide), a₁]) (by rw [m₂]; exact P₁))
      fun _ ⟨a, _, c⟩ => ⟨a, c⟩

theorem setWidth_ofNat8 (x : Nat) : (BitVec.ofNat 64 x).setWidth 8 = BitVec.ofNat 8 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd _ (by decide)

theorem reducePhase_run {K S W : Addr} {len bits : Nat} {key : List Byte} {g : Reg → BitVec 64}
    (R : KRegions K S W len) (hb : 1 ≤ bits ∧ bits ≤ 1024) (s : State) (E : KEnv K S W len bits key g s)
    {l : Proof.Rc2.KeyBytes} (P : Proof.Rc2.BytesPrefix s.mem S l 128) :
    WP isa expandReduce s fun t =>
      KEnv K S W len bits key g t ∧ Proof.Rc2.BytesPrefix t.mem S
        (Proof.Rc2.descend (Proof.Rc2.reduce l bits) ((bits + 7) / 8) (128 - (bits + 7) / 8)) 128 := by
  let t8 := (bits + 7) / 8
  have ht8 : 1 ≤ t8 ∧ t8 ≤ 128 := ⟨by omega, by omega⟩
  unfold expandReduce
  apply WP.seq
  refine WP.mono (reduceSetup_run s hb.2 E.r5) fun t₁ ⟨a₁, b₁, m₁, k₁⟩ => ?_
  have E₁ := E.keep k₁ (by decide) m₁
  apply WP.seq
  refine WP.mono (maskCode_run t₁ (by omega) E₁.r5) fun t₂ ⟨a₂, m₂, k₂⟩ => ?_
  have E₂ := E₁.keep k₂ (by decide) m₂
  have h8₂ : t₂.gpr .r8 = BitVec.ofNat 64 (128 - t8) := by rw [k₂.gpr (by decide), b₁]
  have at₂ : t₂.gpr .r6 + t₂.gpr .r8 = S + BitVec.ofNat 64 (128 - t8) := by rw [E₂.r6, h8₂]
  have inS : InRegions t₂.wr (S + BitVec.ofNat 64 (128 - t8)) 1 := by
    rw [E₂.wr]; exact ⟨⟨S, 128⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  apply WP.seq
  refine WP.mono (reduce_run t₂ E₂.pi (by rw [at₂]; obtain ⟨r, hr, hc⟩ := inS; exact ⟨r, List.mem_append_right _ hr, hc⟩)
    (by rw [at₂]; exact inS)) fun t₃ ⟨m₃, k₃⟩ => ?_
  have P₂ : Proof.Rc2.BytesPrefix t₂.mem S l 128 := by rw [m₂, m₁]; exact P
  rw [at₂, a₂, setWidth_ofNat8, P₂ _ (by omega), maskVal_eq] at m₃
  have E₃ := E₂.write R (k₃.mono (by simp)) (by omega) m₃
  have P₃ : Proof.Rc2.BytesPrefix t₃.mem S (Proof.Rc2.reduce l bits) 128 := by
    rw [m₃]; exact P₂.write (by decide) (by omega) _
  have h8₃ : t₃.gpr .r8 = BitVec.ofNat 64 (128 - t8) := by rw [k₃.gpr (by decide), h8₂]
  have hz : isa.eval (.zero .d .r8) t₃ = some (decide (128 - t8 = 0)) := by
    rw [eval_zero, h8₃, ofNat_beq_zero (by omega)]
  refine WP.ite _ hz (fun ht => WP.block_nil ⟨E₃, ?_⟩) (fun hf => ?_)
  · have e : 128 - t8 = 0 := of_decide_eq_true ht
    show Proof.Rc2.BytesPrefix t₃.mem S (Proof.Rc2.descend (Proof.Rc2.reduce l bits) t8 (128 - t8)) 128
    rw [e]; exact P₃
  · have e : 128 - t8 ≠ 0 := of_decide_eq_false hf
    exact descend_loop R ⟨ht8.1, by omega⟩ _ t₃ E₃ h8₃
      (by rw [k₃.gpr (by decide), k₂.gpr (by decide), a₁]) P₃

/-- What key expansion may assume. -/
structure KeyPre (s : State) : Prop where
  valid : Spec.Rc2.validKey (s.gpr .r4).toNat (s.gpr .r5).toNat
  rd : s.rd = [⟨s.gpr .r3, (s.gpr .r4).toNat⟩]
  wr : s.wr = [⟨s.gpr .r6, 128⟩, ⟨s.gpr .r7, 512⟩]
  kS : (⟨s.gpr .r3, (s.gpr .r4).toNat⟩ : Region).Disjoint ⟨s.gpr .r6, 128⟩
  kW : (⟨s.gpr .r3, (s.gpr .r4).toNat⟩ : Region).Disjoint ⟨s.gpr .r7, 512⟩
  SW : (⟨s.gpr .r6, 128⟩ : Region).Disjoint ⟨s.gpr .r7, 512⟩

/-- What key expansion guarantees. -/
structure KeyPost (s s' : State) : Prop where
  sched : Spec.Rc2.scheduleAt s'.mem (s.gpr .r6) =
    Spec.Rc2.expandKey (Spec.Rc2.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat) (s.gpr .r5).toNat
  saved : ∀ r ∈ keySaved.map Prod.fst, s'.gpr r = s.gpr r

theorem keySave_eq : keySave = Spill.saveCode .r7 keySaved := rfl
theorem keyRestore_eq : keyRestore = Spill.restoreCode .r7 keySaved := rfl

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Rc2.bytesAt m p n).length = n := by
  simp [Spec.Rc2.bytesAt]

theorem expandKey_wp {s : State} (h : KeyPre s) : WP isa expandKey s (KeyPost s) := by
  let K := s.gpr .r3
  let len := (s.gpr .r4).toNat
  let bits := (s.gpr .r5).toNat
  let S := s.gpr .r6
  let W := s.gpr .r7
  let key := Spec.Rc2.bytesAt s.mem K len
  have hv := h.valid
  unfold Spec.Rc2.validKey at hv
  have R : KRegions K S W len := ⟨⟨hv.1, hv.2.1⟩, h.kS, h.SW⟩
  have wW : ∀ d, d + 8 ≤ 512 → InRegions s.wr (W + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [h.wr]; exact ⟨⟨W, 512⟩, by simp [W], Offset.contains_base _ hd (by omega)⟩
  unfold expandKey
  apply WP.seq
  rw [List.append_assoc, keySave_eq]
  refine Spill.save_ok (by decide) (by decide) (fun p hp => by
    simp only [keySaved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> exact wW _ (by decide)) ?_
  let M₀ := Spill.saveMem s.mem W s.gpr keySaved
  have F₀ : Frame [⟨W, 512⟩] s.mem M₀ := Spill.saveMem_frame_base (by decide) (by decide) _ _ _
  rw [WP.block_append_iff]
  refine WP.mono (piInit_run { s with mem := M₀ } rfl fun k hk => wW _ (by omega)) fun t₁ ⟨held, F₁, k₁⟩ => ?_
  refine WP.mono (WP.keep [.r8] (c := .block [.li .r8 0]) (Q := fun t => t.gpr .r8 = 0#64 ∧ t.mem = t₁.mem)
    (by rrun) (by simp [writesOnly, Code.allInstrs_eq, instrs, dstOf]) rfl) fun t₀ ⟨⟨a₀, m₀⟩, k₀⟩ => ?_
  have k01 := k₁.trans k₀
  have E₀ : KEnv K S W len bits key s.gpr t₀ := by
    refine ⟨k01.gpr (by decide), by rw [k01.gpr (by decide)]; exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm,
      by rw [k01.gpr (by decide)]; exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm,
      k01.gpr (by decide), ⟨k01.gpr (by decide), fun j hj => ?_, by rw [m₀]; exact held⟩,
      by rw [k01.2.1]; exact h.rd, by rw [k01.2.2]; exact h.wr, fun c hc => ?_, ?_⟩
    · rw [k01.2.1, k01.2.2]
      obtain ⟨r, hr, hc⟩ := wW (8 * j) (by omega)
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · rw [m₀, F₁.bytes (R := ⟨K, len⟩) (by simpa using h.kW.sub_right (Region.sub_prefix (show 256 ≤ 512 by decide)))
        (by simp; omega) hc]
      show M₀ (K + BitVec.ofNat 64 c) = _
      rw [F₀.bytes (R := ⟨K, len⟩) (by simpa using h.kW) (by simp; omega) hc]
      exact (Proof.Rc2.bytesAt_getD _ _ _ _ hc).symm
    · rw [m₀]
      refine (Spill.saveMem_saved (by decide) s.mem W s.gpr).frame F₁ fun p hp r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      simp only [keySaved, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> exact Offset.disjoint_base _ (by decide) (by decide)
  have hk : key.length = len := bytesAt_length _ _ _
  apply WP.seq
  refine WP.mono (copyFill_run R hk t₀ E₀ a₀) fun t₂ ⟨E₂, P₂⟩ => ?_
  apply WP.seq
  refine WP.mono (reducePhase_run R ⟨hv.2.2.1, hv.2.2.2⟩ t₂ E₂ P₂) fun t₃ ⟨E₃, P₃⟩ => ?_
  rw [keyRestore_eq]
  refine WP.mono (Spill.restore_wp (by decide) E₃.pi.r7 (by decide) (by decide) (fun p hp => ?_) E₃.saved)
    fun s' Rs => ⟨?_, fun r hr => ?_⟩
  · rw [E₃.rd, E₃.wr]
    simp only [keySaved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> exact ⟨⟨W, 512⟩, by simp, Offset.contains_base _ (by decide) (by decide)⟩
  · rw [Rs.mem]
    refine Proof.Rc2.scheduleAt_expanded ?_
    rw [Proof.Rc2.expandBytes_eq, hk]
    exact P₃
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    exact Rs.gpr p hp

end VG.Proof.Rc2.PPC64LE
