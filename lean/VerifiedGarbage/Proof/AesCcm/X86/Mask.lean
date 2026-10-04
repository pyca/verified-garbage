import VerifiedGarbage.Proof.AesCcm.X86.Top

/-!
# AES-CCM on x86: masking the data, and the received tag

Untrusted: everything here is checked by Lean. `mask` ANDs every byte of the
data with `0 − ok`: the data if `ok = 1`, zeros if `ok = 0` (`mask_ok`).
`recv` copies the `tag_len` bytes of the received tag, at `W` itself, padded
with zeros, to `W + rO` (`recvW_ok`, as AES-GCM's `recv_ok`, whose tag is
outside `W`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ccm (zeros)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 recv tglO tpO rO)
open VG.Proof.AesGcm.X86 (w64 w64_add slotv in_of_covers covers_left succ_ofNat32 add_zero32 pred_count pred_beq bytesAt_succ
  length_bytesAt and_self_beq32 WEnv padLoop_ok zero4_fold toNat_ofNat32)

/-! ## `mask` -/

theorem mask_byte32 (b : Byte) (c : Bool) :
    ((b.setWidth 32 &&& ((0 : BitVec 32) - (if c then 1 else 0))).setWidth 8) = if c then b else 0 := by
  cases c
  · simp
  · rw [show (if true = true then (1 : BitVec 32) else 0) = 1 from rfl,
      show (0 : BitVec 32) - 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes]
    simp

abbrev maskBody : List Instr :=
  [.movzx8 .edx (at_ .edi 0), .alu .and .edx (.reg .ebx), .store8 (at_ .edi 0) .dl, .alu .add .edi (imm 1),
    .alu .sub .ecx (imm 1)]

theorem maskStep_ok (s : State) {P : BitVec 32} {i n : Nat} {c : Bool} (hs : s.gpr .edi = P + BitVec.ofNat 32 i)
    (hc : s.gpr .ecx = BitVec.ofNat 32 (n - i)) (hb : s.gpr .ebx = 0 - (if c then 1 else 0))
    (eP : w64 (P + BitVec.ofNat 32 i) = w64 P + BitVec.ofNat 64 i)
    (r : InRegions (s.rd ++ s.wr) (w64 P + BitVec.ofNat 64 i) 1) (w : InRegions s.wr (w64 P + BitVec.ofNat 64 i) 1) :
    ∃ s', runBlock isa maskBody s = some s' ∧
      s'.mem = s.mem.writeW (w64 P + BitVec.ofNat 64 i) ((if c then s.mem (w64 P + BitVec.ofNat 64 i) else 0 : Byte)) ∧
      s'.gpr .edi = P + BitVec.ofNat 32 (i + 1) ∧ s'.gpr .ecx = BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 ∧
      s'.zf = some (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) ∧
      (∀ r, r ≠ .edx → r ≠ .edi → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [maskBody, add_zero32, hs, eP, r, w], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cmems [hb, mask_byte32]
  · cregs [hs, succ_ofNat32]
  · cregs [hc]
  · cmems [hc]
  · intro r h₁ h₂ h₃; cregs [h₁, h₂, h₃]
  all_goals cmems []

theorem length_mask (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P j else zeros j).length = j := by
  cases c <;> simp [zeros, length_bytesAt]

theorem mask_succ (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P (j + 1) else zeros (j + 1)) =
      (if c then bytesAt m P j else zeros j) ++ [if c then m (P + BitVec.ofNat 64 j) else 0] := by
  cases c <;> simp [zeros, bytesAt_succ, List.replicate_succ']

/-- Every byte of the data ANDed with `0 − ok`, for `ok` (at `W + okO`) 1 or 0. -/
theorem mask_ok {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) {D : BitVec 32} {n : Nat}
    (hDp : slotv s.mem W dataO = D) (hlen : slotv s.mem W lenO = BitVec.ofNat 32 n) (hn32 : n < 2 ^ 32)
    (hD : Buf W SP s D n) (hDw : Covers [⟨w64 D, n⟩] s.wr) {c : Bool}
    (hok : slotv s.mem W okO = if c then 1 else 0) :
    WP isa mask s fun s' => Env K W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = writeBytes s.mem (w64 D) (if c then bytesAt s.mem (w64 D) n else zeros n) := by
  obtain ⟨s₁, run₁, m₁, cx₁, zf₁, bp₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [.mov .ecx (slot lenO), .alu .test .ecx (.reg .ecx)] s = some s₁ ∧ s₁.mem = s.mem ∧
      s₁.gpr .ecx = BitVec.ofNat 32 n ∧ s₁.zf = some (decide (n = 0)) ∧ s₁.gpr .ebp = W ∧ s₁.gpr .esp = SP ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hlen], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · cregs [hlen]
    · cmems [hlen]; rw [and_self_beq32 hn32]
    · cregs [E.ebp]
    · cregs [E.esp]
    all_goals cmems []
  have E₁ : Env K W SP s₁ := E.keep (by rw [bp₁, E.ebp]) (by rw [sp₁, E.esp]) rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n = 0)) (eval_e zf₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hn0 : n = 0 := of_decide_eq_true hb
    subst hn0
    refine ⟨E₁, rd₁, wr₁, ?_⟩
    rw [m₁]
    cases c <;> simp [Spec.Aes.bytesAt, zeros, writeBytes_nil]
  have hn0 : 0 < n := Nat.pos_of_ne_zero (of_decide_eq_false hb)
  obtain ⟨s₂, run₂, m₂, bx₂, di₂, cx₂, bp₂, sp₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [.mov .ebx (imm 0), .alu .sub .ebx (slot okO), .mov .edi (slot dataO)] s₁ = some s₂ ∧ s₂.mem = s.mem ∧
      s₂.gpr .ebx = 0 - (if c then 1 else 0) ∧ s₂.gpr .edi = D ∧ s₂.gpr .ecx = BitVec.ofNat 32 n ∧
      s₂.gpr .ebp = W ∧ s₂.gpr .esp = SP ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    have hok₁ : slotv s₁.mem W okO = if c then 1 else 0 := by rw [m₁]; exact hok
    have hd₁ : slotv s₁.mem W dataO = D := by rw [m₁]; exact hDp
    refine ⟨_, by crun [bp₁, L.aW, E₁.perm.wR, hok₁, hd₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · cmems [m₁]
    · cregs [hok₁]; rfl
    · cregs [hd₁]
    · cregs [cx₁]
    · cregs [bp₁]
    · cregs [sp₁]
    · cmems [rd₁]
    · cmems [wr₁]
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have hfD := hD.wrap
  refine WP.loop (M := isa) (body := .block maskBody) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ j, k = n - j ∧ j < n ∧ t.gpr .edi = D + BitVec.ofNat 32 j ∧
      t.gpr .ecx = BitVec.ofNat 32 (n - j) ∧
      t.mem = writeBytes s.mem (w64 D) (if c then bytesAt s.mem (w64 D) j else zeros j) ∧
      (∀ r, r ≠ .edx → r ≠ .edi → r ≠ .ecx → t.gpr r = s₂.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, hn0, by rw [di₂, add_zero32], by rw [cx₂, Nat.sub_zero], by
      rw [m₂]; cases c <;> simp [Spec.Aes.bytesAt, zeros, writeBytes_nil], fun r _ _ _ => rfl, rd₂, wr₂⟩
  rintro k t ⟨j, rfl, hj, di, cx, mem, g, rd, wr⟩
  obtain ⟨t', run', mem', di', cx', zf', g', rd', wr'⟩ := maskStep_ok t (P := D) (i := j) (n := n) (c := c) di cx
    (by rw [g _ (by decide) (by decide) (by decide), bx₂]) (w64_add (by omega))
    (by rw [rd, wr]; exact in_of_covers hD.rd hj (by omega))
    (by rw [wr]; exact in_of_covers hDw hj (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have fr : Frame [⟨w64 D, j⟩] s.mem t.mem := by
    rw [mem]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)
  have hq : t.mem (w64 D + BitVec.ofNat 64 j) = s.mem (w64 D + BitVec.ofNat 64 j) :=
    fr _ fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains, Mem.sub_ofNat_toNat (w64 D) (show j < 2 ^ 64 by omega)] at hcon; omega
  have hmem : t'.mem = writeBytes s.mem (w64 D) (if c then bytesAt s.mem (w64 D) (j + 1) else zeros (j + 1)) := by
    rw [mem', hq, mem, mask_succ, writeBytes_snoc _ _ _ _ (by rw [length_mask]; omega), length_mask]
  have hz : t'.zf = some (decide (j + 1 = n)) := by rw [zf', pred_beq hj hn32]
  have gg : ∀ r, r ≠ .edx → r ≠ .edi → r ≠ .ecx → t'.gpr r = s₂.gpr r := fun r h₁ h₂ h₃ => by
    rw [g' r h₁ h₂ h₃, g r h₁ h₂ h₃]
  have E' : Env K W SP t' := ⟨by rw [gg _ (by decide) (by decide) (by decide), bp₂],
    by rw [gg _ (by decide) (by decide) (by decide), sp₂], E.perm.of_eq (by rw [rd', rd]) (by rw [wr', wr])⟩
  by_cases he : j + 1 = n
  · left
    exact ⟨by simp [eval, hz, he], E', by rw [rd', rd], by rw [wr', wr], by rw [hmem, he]⟩
  · right
    refine ⟨by simp [eval, hz, he], n - (j + 1), by omega, j + 1, rfl, by omega, di',
      by rw [cx', pred_count hj hn32], hmem, gg, by rw [rd', rd], by rw [wr', wr]⟩

/-! ## The received tag -/

/-- `recv`: the `t` bytes of the received tag at `W` (kept at `W + tpO`),
padded, at `W + rO`. -/
theorem recvW_ok {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) {t : Nat}
    (hv : slotv s.mem W tglO = BitVec.ofNat 32 t) (hT : slotv s.mem W tpO = W) (ht1 : 1 ≤ t) (ht : t ≤ 16) :
    WP isa recv s fun s' => bytesAt s'.mem (w64 W + BitVec.ofNat 64 rO) 16 = bytesAt s.mem (w64 W) t ++ zeros (16 - t) ∧
      Frame [⟨w64 W + BitVec.ofNat 64 rO, 16⟩] s.mem s'.mem ∧ Env K W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have he : WEnv W s := ⟨E.ebp, E.perm.w, L.fw⟩
  have hz := zero4_fold s.mem W 196
  simp only [Nat.reduceAdd] at hz
  have fz : Frame [⟨w64 W + BitVec.ofNat 64 196, 16⟩] s.mem (Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 196)) :=
    Cmac.frame_store4 _ _ _ _ _
  have kz : ∀ o, 196 + 16 ≤ o ∨ o + 4 ≤ 196 → o + 4 ≤ 2560 →
      slotv (Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 196)) W o = slotv s.mem W o := fun o ho hb =>
    fz.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (by omega) (by omega) (by omega)) (by decide)
  have hv' := kz tglO (by decide) (by decide)
  have hT' := kz tpO (by decide) (by decide)
  rw [hv] at hv'
  rw [hT] at hT'
  obtain ⟨s₁, run₁, hm₁, hdi, hdx, hcx, hbp, hsp, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      (zero4 rO ++ [.mov .edi (slot tpO), .mov .edx (.reg .ebp), .alu .add .edx (imm rO), .mov .ecx (slot tglO)]) s =
        some s₁ ∧ s₁.mem = Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 196) ∧ s₁.gpr .edi = W ∧
      s₁.gpr .edx = W + BitVec.ofNat 32 196 ∧ s₁.gpr .ecx = BitVec.ofNat 32 t ∧ s₁.gpr .ebp = W ∧
      s₁.gpr .esp = SP ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [zero4, E.ebp, L.aW, E.perm.wW, E.perm.wR, hz, hv', hT'], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · cmems [hz]
    · cregs [hT']
    · cregs [E.ebp]
    · cregs [hv']
    · cregs [E.ebp]
    · cregs [E.esp]
    all_goals cmems []
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have tw : (⟨w64 W, t⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 196, 16⟩ := by
    simpa using Lay.w_w (W := W) (a := 0) (n := t) (d := 196) (k := 16) (.inl (by omega)) (by omega) (by decide)
  refine WP.mono (padLoop_ok (S := W) (d := 196) (t := t) (m := s.mem) (he.keep (by rw [hbp, E.ebp]) hwr₁) hm₁ hdi
    hdx hcx ht1 ht (by rw [hrd₁, hwr₁]; simpa using covers_left (E.perm.wC (d := 0) (n := t) (by omega)))
    (by have := L.fw; omega) tw (by decide)) fun s' ⟨b, f, g, rd, wr⟩ => ⟨b, f, ?_, ?_, ?_⟩
  · exact ⟨by rw [g _ (by decide) (by decide) (by decide) (by decide), hbp],
      by rw [g _ (by decide) (by decide) (by decide) (by decide), hsp], E.perm.of_eq (by rw [rd, hrd₁])
        (by rw [wr, hwr₁])⟩
  · rw [rd, hrd₁]
  · rw [wr, hwr₁]

end VG.Proof.AesCcm.X86
