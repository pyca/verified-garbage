module

public import VerifiedGarbage.Proof.Rc2.RISCV64.KeyLoop
import VerifiedGarbage.Proof.Rc2.RISCV64.KeyInit
import VerifiedGarbage.Proof.Rc2.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Impl.Rc2.RISCV64.ExpandKey
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep

/-!
# RC2 on RISC-V: key expansion

`expandKey_wp`: the schedule at `a3` becomes the expansion of the key at
`a0`, with PITABLE written to the working space at `a4`.
-/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64

theorem copyFill_run {K S W : Addr} {len bits : Nat} {key : List Byte}
    (R : KRegions K S W len) (hk : key.length = len) (s : State) (E : KEnv K S W len bits key s)
    (h8 : s.gpr .a5 = 0#64) :
    WP isa expandCopyFill s fun t =>
      KEnv K S W len bits key t ∧ Proof.Rc2.BytesPrefix t.mem S (Proof.Rc2.fill key (128 - len)) 128 := by
  have hl := R.hlen
  unfold expandCopyFill
  apply WP.seq
  refine WP.mono (copy_loop R s E h8) fun t₁ ⟨E₁, a₁, P₁⟩ => ?_
  apply WP.seq
  refine WP.mono (WP.keep [.a7] (c := .block [.li .a7 128, .sub .a7 .a5 .a7]) (Q := fun t =>
      t.gpr .a7 = BitVec.ofNat 64 len - BitVec.ofNat 64 128 ∧ t.mem = t₁.mem) (by rrun [a₁])
    (by rfl) rfl) fun t₂ ⟨⟨a₂, m₂⟩, k₂⟩ => ?_
  have E₂ := E₁.keep k₂ (by decide) m₂
  have hb : isa.eval (.zero .a7) t₂ = some (decide (len = 128)) := by
    rw [Steps.eval_zero, a₂]
    exact congrArg some (Offset.ofNat_sub_ofNat_beq (by omega_arith) (by omega_arith))
  refine WP.ite _ hb (fun ht => WP.block_nil ⟨E₂, ?_⟩) (fun hf => ?_)
  · have e : len = 128 := of_decide_eq_true ht
    rw [m₂, e, Nat.sub_self]; rw [e] at P₁; exact P₁
  · have e : len ≠ 128 := of_decide_eq_false hf
    exact WP.mono (fill_loop R hk (by omega_arith) t₂ E₂ (by rw [k₂.gpr (by decide), a₁]) (by rw [m₂]; exact P₁))
      fun _ ⟨a, _, c⟩ => ⟨a, c⟩

theorem setWidth_ofNat8 (x : Nat) : (BitVec.ofNat 64 x).setWidth 8 = BitVec.ofNat 8 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd _ (by decide)

theorem reducePhase_run {K S W : Addr} {len bits : Nat} {key : List Byte}
    (R : KRegions K S W len) (hb : 1 ≤ bits ∧ bits ≤ 1024) (s : State) (E : KEnv K S W len bits key s)
    {l : Proof.Rc2.KeyBytes} (P : Proof.Rc2.BytesPrefix s.mem S l 128) :
    WP isa expandReduce s fun t =>
      KEnv K S W len bits key t ∧ Proof.Rc2.BytesPrefix t.mem S
        (Proof.Rc2.descend (Proof.Rc2.reduce l bits) ((bits + 7) / 8) (128 - (bits + 7) / 8)) 128 := by
  let t8 := (bits + 7) / 8
  have ht8 : 1 ≤ t8 ∧ t8 ≤ 128 := ⟨by omega_arith, by omega_arith⟩
  unfold expandReduce
  apply WP.seq
  refine WP.mono (reduceSetup_run s hb.2 E.a2) fun t₁ ⟨a₁, b₁, m₁, k₁⟩ => ?_
  have E₁ := E.keep k₁ (by decide) m₁
  apply WP.seq
  refine WP.mono (maskCode_run t₁ (by omega_arith) E₁.a2) fun t₂ ⟨a₂, m₂, k₂⟩ => ?_
  have E₂ := E₁.keep k₂ (by decide) m₂
  have h8₂ : t₂.gpr .a5 = BitVec.ofNat 64 (128 - t8) := by rw [k₂.gpr (by decide), b₁]
  have at₂ : t₂.gpr .a3 + t₂.gpr .a5 = S + BitVec.ofNat 64 (128 - t8) := by rw [E₂.a3, h8₂]
  have inS : InRegions t₂.wr (S + BitVec.ofNat 64 (128 - t8)) 1 := by
    rw [E₂.wr]; exact ⟨⟨S, 128⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  apply WP.seq
  refine WP.mono (reduce_run t₂ E₂.pi (by rw [at₂]; obtain ⟨r, hr, hc⟩ := inS; exact ⟨r, List.mem_append_right _ hr, hc⟩)
    (by rw [at₂]; exact inS)) fun t₃ ⟨m₃, k₃⟩ => ?_
  have P₂ : Proof.Rc2.BytesPrefix t₂.mem S l 128 := by rw [m₂, m₁]; exact P
  rw [at₂, a₂, setWidth_ofNat8, P₂ _ (by omega_arith), maskVal_eq] at m₃
  have E₃ := E₂.write R (k₃.mono (by simp)) (by omega_arith) m₃
  have P₃ : Proof.Rc2.BytesPrefix t₃.mem S (Proof.Rc2.reduce l bits) 128 := by
    rw [m₃]; exact P₂.write (by decide) (by omega_arith) _
  have h8₃ : t₃.gpr .a5 = BitVec.ofNat 64 (128 - t8) := by rw [k₃.gpr (by decide), h8₂]
  have hz : isa.eval (.zero .a5) t₃ = some (decide (128 - t8 = 0)) := by
    rw [Steps.eval_zero, h8₃, Steps.ofNat_beq_zero (by omega_arith)]
  refine WP.ite _ hz (fun ht => WP.block_nil ⟨E₃, ?_⟩) (fun hf => ?_)
  · have e : 128 - t8 = 0 := of_decide_eq_true ht
    show Proof.Rc2.BytesPrefix t₃.mem S (Proof.Rc2.descend (Proof.Rc2.reduce l bits) t8 (128 - t8)) 128
    rw [e]; exact P₃
  · have e : 128 - t8 ≠ 0 := of_decide_eq_false hf
    exact descend_loop R ⟨ht8.1, by omega_arith⟩ _ t₃ E₃ h8₃
      (by rw [k₃.gpr (by decide), k₂.gpr (by decide), a₁]) P₃

/-- What key expansion may assume. -/
structure KeyPre (s : State) : Prop where
  valid : Spec.Rc2.validKey (s.gpr .a1).toNat (s.gpr .a2).toNat
  rd : s.rd = [⟨s.gpr .a0, (s.gpr .a1).toNat⟩]
  wr : s.wr = [⟨s.gpr .a3, 128⟩, ⟨s.gpr .a4, 512⟩]
  al : (s.gpr .a4).toNat % 8 = 0
  kS : (⟨s.gpr .a0, (s.gpr .a1).toNat⟩ : Region).Disjoint ⟨s.gpr .a3, 128⟩
  kW : (⟨s.gpr .a0, (s.gpr .a1).toNat⟩ : Region).Disjoint ⟨s.gpr .a4, 512⟩
  SW : (⟨s.gpr .a3, 128⟩ : Region).Disjoint ⟨s.gpr .a4, 512⟩

/-- What key expansion guarantees. -/
noncomputable def KeyPost (s s' : State) : Prop :=
  Spec.Rc2.scheduleAt s'.mem (s.gpr .a3) =
    Spec.Rc2.expandKey (Spec.Rc2.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) (s.gpr .a2).toNat

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Rc2.bytesAt m p n).length = n := by
  simp [Spec.Rc2.bytesAt]

theorem expandKey_wp {s : State} (h : KeyPre s) : WP isa expandKey s (KeyPost s) := by
  let K := s.gpr .a0
  let len := (s.gpr .a1).toNat
  let bits := (s.gpr .a2).toNat
  let S := s.gpr .a3
  let W := s.gpr .a4
  let key := Spec.Rc2.bytesAt s.mem K len
  have hv := h.valid
  unfold Spec.Rc2.validKey at hv
  have R : KRegions K S W len := ⟨⟨hv.1, hv.2.1⟩, h.kS, h.SW⟩
  have wW : ∀ d, d + 8 ≤ 512 → InRegions s.wr (W + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [h.wr]; exact ⟨⟨W, 512⟩, by simp [W], Offset.contains_base _ hd (by omega_arith)⟩
  unfold expandKey
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (piInit_run s rfl h.al fun k hk => wW _ (by omega_arith)) fun t₁ ⟨held, F₁, k₁⟩ => ?_
  refine WP.mono (WP.keep [.a5] (c := .block [.li .a5 0]) (Q := fun t => t.gpr .a5 = 0#64 ∧ t.mem = t₁.mem)
    (by rrun) (by rfl) rfl) fun t₀ ⟨⟨a₀, m₀⟩, k₀⟩ => ?_
  have k01 := k₁.trans k₀
  have E₀ : KEnv K S W len bits key t₀ := by
    refine ⟨k01.gpr (by decide), by rw [k01.gpr (by decide)]; exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm,
      by rw [k01.gpr (by decide)]; exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm,
      k01.gpr (by decide), ⟨k01.gpr (by decide), h.al, fun j hj => ?_, by rw [m₀]; exact held⟩,
      by rw [k01.2.1]; exact h.rd, by rw [k01.2.2]; exact h.wr, fun c hc => ?_⟩
    · rw [k01.2.1, k01.2.2]
      obtain ⟨r, hr, hc⟩ := wW (8 * j) (by omega_arith)
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · rw [m₀, F₁.bytes (R := ⟨K, len⟩) (by simpa using h.kW.sub_right (Region.sub_prefix (show 256 ≤ 512 by decide)))
        (by simp; omega_arith) hc]
      exact (Proof.Rc2.bytesAt_getD _ _ _ _ hc).symm
  have hk : key.length = len := bytesAt_length _ _ _
  apply WP.seq
  refine WP.mono (copyFill_run R hk t₀ E₀ a₀) fun t₂ ⟨E₂, P₂⟩ => ?_
  refine WP.mono (reducePhase_run R ⟨hv.2.2.1, hv.2.2.2⟩ t₂ E₂ P₂) fun t₃ ⟨_, P₃⟩ => ?_
  refine Proof.Rc2.scheduleAt_expanded ?_
  rw [Proof.Rc2.expandBytes_eq, hk]
  exact P₃

end VG.Proof.Rc2.RISCV64
