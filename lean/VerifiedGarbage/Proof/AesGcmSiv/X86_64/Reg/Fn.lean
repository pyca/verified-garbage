module

public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Reg.Crypt
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Reg.Loops
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Fn
import VerifiedGarbage.Proof.AesGcm.X86_64.Mask
import VerifiedGarbage.Proof.GcmSiv.Spec
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Interleave
import VerifiedGarbage.Proof.Framework.Cold

/-!
# AES-GCM-SIV in registers on x86-64: `vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open`

Untrusted: everything here is checked by Lean. `cmp`, `mask`, `recv` and
`tagOut` are the first implementation's, in this one's working space
(`cmp_ok`, `mask_ok`, `recv_ok`, `tagOut_ok`); `seal_wp` and `open_wp` put
the pieces together.
-/

-- separate module: the functions, apart from their pieces

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSivReg.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (toNat_ofNat_of_lt in_off)
open VG.Proof.AesGcmSiv.X86_64 (add_ofNat_assoc ok_val bytes16_eq bytesAt_copy2)

theorem cmp_ok {K W SP : Addr} {t : State} (E : Env K W SP t) :
    ∃ t' : State, runBlock isa cmp t = some t' ∧
      t'.mem = t.mem.writeW (W + BitVec.ofNat 64 192)
        (if bytesAt t.mem W 16 = bytesAt t.mem (W + BitVec.ofNat 64 128) 16 then 1#64 else 0#64) ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have h15 := E.r15
  obtain r₀ : InRegions (t.rd ++ t.wr) W 8 := by simpa using E.perm.wR (show 0 + 8 ≤ 744 by decide)
  obtain r₈ := E.perm.wR (show 8 + 8 ≤ 744 by decide)
  obtain u₀ := E.perm.wR (show 128 + 8 ≤ 744 by decide)
  obtain u₈ := E.perm.wR (show 136 + 8 ≤ 744 by decide)
  obtain wo := E.perm.wW (show 192 + 8 ≤ 744 by decide)
  refine ⟨_, by srun [Impl.AesGcmSiv.X86_64.cmp, h15, r₀, r₈, u₀, u₈, wo], ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, mem_setFlags, gpr_setReg, gpr_arithFlags, cf_arithFlags, cf_setReg,
      ite_true, ite_false, reduceCtorEq]
    obtain hb := bytes16_eq t.mem W (W + BitVec.ofNat 64 128)
    rw [add_ofNat_assoc] at hb
    simp only [ok_val, hb]
  · intro r hr; simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
  all_goals rfl

/-- What `mask` leaves, from `t`, when `ok` is whether `c` holds. -/
structure MaskPost (K W SP : Addr) (D : Addr) (n : Nat) (c : Prop) [Decidable c] (t t' : State) : Prop where
  env : Env K W SP t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame [⟨D, n⟩] t.mem t'.mem
  data : bytesAt t'.mem D n = if c then bytesAt t.mem D n else Spec.GcmSiv.zeros n

theorem mask_ok {K W SP : Addr} {t : State} (E : Env K W SP t) {R : Nat} {N A D : Addr} {al n : Nat}
    (S : Slots W R N A D al n t.mem) (hD : Buf K W SP t D n) (hDw : Covers [⟨D, n⟩] t.wr) {c : Prop} [Decidable c]
    (hok : t.mem.readW (W + BitVec.ofNat 64 192) 64 = if c then 1#64 else 0#64) :
    WP isa mask t (MaskPost K W SP D n c t) := by
  have h15 := E.r15
  have hn := hD.lt
  obtain rD := E.perm.wR (show 232 + 8 ≤ 744 by decide)
  obtain rL := E.perm.wR (show 240 + 8 ≤ 744 by decide)
  obtain rO := E.perm.wR (show 192 + 8 ≤ 744 by decide)
  have sD := S.data
  have sL := S.len
  obtain hok' : t.mem.readW (W + BitVec.ofNat 64 192) 64 = if decide c then 1 else 0 := by
    rw [hok]; by_cases hc : c <;> simp [hc]
  obtain ⟨t₁, run₁, h12₁, hbp₁, h11₁, h10₁, rcx₁, hzf₁, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ t₁ : State, runBlock isa
      [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO)), .mov32 .r11 (imm 0),
        .alu .sub .r11 (.mem (at_ .r15 okO)), .mov32 .r10 (imm 0), .mov .rcx (.reg .rbp),
        .shift .shr .rcx 4, .alu .test .rcx (.reg .rcx)] t = some t₁ ∧
      t₁.gpr .r12 = D ∧ t₁.gpr .rbp = BitVec.ofNat 64 n ∧
      t₁.gpr .r11 = 0 - (if decide c then 1 else 0) ∧ t₁.gpr .r10 = BitVec.ofNat 64 0 ∧
      t₁.gpr .rcx = BitVec.ofNat 64 (n / 16) ∧ t₁.zf = some (decide (n / 16 = 0)) ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp], t₁.gpr r = t.gpr r) ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by srun [h15, rD, rL, rO], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, sD]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, sL]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hok']; rfl
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, sL,
        Proof.AesGcm.X86_64.ofNat_shr4 hn]
    · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, sL,
        Proof.AesGcm.X86_64.ofNat_shr4 hn, Proof.AesGcm.X86_64.and_self_beq (show n / 16 < 2 ^ 64 by omega_arith)]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  obtain E₁ : Env K W SP t₁ := E.keep hg₁ hrd₁ hwr₁
  refine WP.mono (Proof.AesGcm.X86_64.maskTail_wp hn (by rw [hrd₁, hwr₁]; exact hD.rd) (by rw [hwr₁]; exact hDw)
    h12₁ h11₁ hbp₁ h10₁ rcx₁ hzf₁) fun t₂ M => ?_
  obtain hl : (Proof.AesGcm.X86_64.masked t₁.mem D (decide c) n).length = n :=
    Proof.AesGcm.X86_64.length_masked _ _ _ _
  refine ⟨E₁.keep (fun r hr => M.keep r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
    M.rd M.wr, M.rd.trans hrd₁, M.wr.trans hwr₁, by rw [M.mem, ← hm₁]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _),
    ?_⟩
  obtain e := bytesAt_writeBytes_self t₁.mem D (Proof.AesGcm.X86_64.masked t₁.mem D (decide c) n)
    (by omega_arith)
  rw [hl] at e
  rw [M.mem, e, hm₁]
  by_cases hc : c <;> simp [Proof.AesGcm.X86_64.masked, hc, Spec.GcmSiv.zeros]

/-- `okTest`, with `ok` either 1 or 0: ZF set if it is 0. -/
theorem okTest_run {K W SP : Addr} {t : State} (E : Env K W SP t) {v : BitVec 64}
    (hv : t.mem.readW (W + BitVec.ofNat 64 192) 64 = v) (h01 : v = 1#64 ∨ v = 0#64) :
    ∃ t₁ : State, runBlock isa Impl.AesGcmSiv.X86_64Reg.okTest t = some t₁ ∧ t₁.zf = some (decide (v = 0#64)) ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp], t₁.gpr r = t.gpr r) ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have h15 := E.r15
  obtain rO := E.perm.wR (show 192 + 8 ≤ 744 by decide)
  refine ⟨_, by srun [Impl.AesGcmSiv.X86_64Reg.okTest, h15, rO], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [zf_arithFlags, gpr_setReg, ite_true, hv]
    rcases h01 with rfl | rfl <;> decide
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
  all_goals rfl

/-- `wipeBad` leaves what `mask` does: nothing changed if the tags are equal. -/
theorem wipeBad_ok {K W SP : Addr} {t : State} (E : Env K W SP t) {R : Nat} {N A D : Addr} {al n : Nat}
    (S : Slots W R N A D al n t.mem) (hD : Buf K W SP t D n) (hDw : Covers [⟨D, n⟩] t.wr) {c : Prop} [Decidable c]
    (hok : t.mem.readW (W + BitVec.ofNat 64 192) 64 = if c then 1#64 else 0#64) :
    WP isa Impl.AesGcmSiv.X86_64Reg.wipeBad t (MaskPost K W SP D n c t) := by
  obtain ⟨t₁, run₁, hzf₁, hg₁, hm₁, hrd₁, hwr₁⟩ := okTest_run E hok (by by_cases hc : c <;> simp [hc])
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  obtain E₁ : Env K W SP t₁ := E.keep hg₁ hrd₁ hwr₁
  refine WP.iteCold_iff.mpr (WP.ite _ hzf₁ (fun hb => ?_) (fun hb => WP.block_nil ?_))
  · refine WP.mono (mask_ok E₁ (by rw [hm₁]; exact S) (hD.of_eq hrd₁ hwr₁) (by rw [hwr₁]; exact hDw)
      (by rw [hm₁]; exact hok)) fun t₂ Mk => ?_
    exact ⟨Mk.env, Mk.rd.trans hrd₁, Mk.wr.trans hwr₁, by rw [← hm₁]; exact Mk.frame, by rw [← hm₁]; exact Mk.data⟩
  · have hc : c := by by_cases hc : c <;> simp [hc] at hb ⊢
    exact ⟨E₁, hrd₁, hwr₁, by rw [hm₁]; exact Frame.refl _ _, by rw [hm₁]; simp only [hc, ↓reduceIte]⟩

/-! ## The tag's copies -/

/-- `recv`: the received tag, at `T`, whose address is at `SP + 16`, copied
to `W`. -/
theorem recv_ok {K W SP T : Addr} {s : State} (E : Env K W SP s)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T) (hTa : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 16) 8)
    (hB : Buf K W SP s T 16) :
    ∃ s', runBlock isa recv s = some s' ∧ Frame [⟨W, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem W 16 = bytesAt s.mem T 16 ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have h15 := E.r15
  have hsp := E.rsp
  obtain t₀ : InRegions (s.rd ++ s.wr) T 8 := by simpa using in_off (d := 0) (n := 8) hB.rd (by decide) (by decide)
  obtain t₈ := in_off (d := 8) (n := 8) hB.rd (by decide) (by decide)
  obtain w₀ : InRegions s.wr W 8 := by simpa using E.perm.wW (show 0 + 8 ≤ 744 by decide)
  obtain w₈ := E.perm.wW (show 8 + 8 ≤ 744 by decide)
  obtain hs : Mem.Sep (T + BitVec.ofNat 64 8) (64 / 8) W (64 / 8) :=
    hB.w.sep (Offset.contains_base T (d := 8) (n := 8) (k := 16) (by decide) (by decide))
      (by simpa using Offset.contains_base W (d := 0) (n := 8) (k := 744) (by decide) (by decide))
  refine ⟨_, by srun [recv, h15, hsp, hT, hTa, t₀, t₈, w₀, w₈], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg]; exact Proof.Cmac.frame_store2 _ _ _
  · simp only [mem_setReg]; exact bytesAt_copy2 _ _ _ hs
  · intro r hr; simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]
  all_goals rfl

/-- `tagOut`: the tag at `W` copied to `T`, whose address is at `SP + 16`. -/
theorem tagOut_ok {K W SP T : Addr} {s : State} (E : Env K W SP s)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T) (hTa : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 16) 8)
    (hTw : Covers [⟨T, 16⟩] s.wr) (hTW : (⟨T, 16⟩ : Region).Disjoint ⟨W, 744⟩) :
    ∃ s', runBlock isa tagOut s = some s' ∧ Frame [⟨T, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem T 16 = bytesAt s.mem W 16 ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have h15 := E.r15
  have hsp := E.rsp
  obtain t₀ : InRegions s.wr T 8 := by simpa using in_off (d := 0) (n := 8) hTw (by decide) (by decide)
  obtain t₈ := in_off (d := 8) (n := 8) hTw (by decide) (by decide)
  obtain w₀ : InRegions (s.rd ++ s.wr) W 8 := by simpa using E.perm.wR (show 0 + 8 ≤ 744 by decide)
  obtain w₈ := E.perm.wR (show 8 + 8 ≤ 744 by decide)
  obtain hs : Mem.Sep (W + BitVec.ofNat 64 8) (64 / 8) T (64 / 8) :=
    hTW.symm.sep (Offset.contains_base W (d := 8) (n := 8) (k := 744) (by decide) (by decide))
      (by simpa using Offset.contains_base T (d := 0) (n := 8) (k := 16) (by decide) (by decide))
  refine ⟨_, by srun [tagOut, h15, hsp, hT, hTa, t₀, t₈, w₀, w₈], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg]; exact Proof.Cmac.frame_store2 _ _ _
  · simp only [mem_setReg]; exact bytesAt_copy2 _ _ _ hs
  · intro r hr; simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]
  all_goals rfl

/-! ## What the pieces write -/

section
variable {θ : Nat} {K W SP D : Addr} {n : Nat} {m m' : Mem}

/-- A piece that writes within the first 144 bytes of `W`. -/
theorem frA {d k : Nat} (h : d + k ≤ 144) (f : Frame [⟨W + BitVec.ofNat 64 d, k⟩] m m') :
    Frame (mutR W SP D n) m m' :=
  f.sub fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq
    exact ⟨wA W, by simp, Offset.sub_base W h⟩

/-- A piece that writes the schedule. -/
theorem frC (f : Frame [⟨W + BitVec.ofNat 64 248, 240⟩] m m') : Frame (mutR W SP D n) m m' :=
  f.sub fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq
    exact ⟨wC W, by simp, Offset.sub W (by decide) (by decide)⟩

/-- What `seal` and `open` write, by the data's length: the save area and
the slots, the tag and the message keys, `ok`, the schedule, what the pieces
with the loops write (`lRn`) and the data. -/
abbrev fineR (θ : Nat) (W D : Addr) (n : Nat) : List Region :=
  entryR W :: ⟨W, 64⟩ :: wO W :: ⟨W + BitVec.ofNat 64 248, 240⟩ :: (lRn θ W n ++ [⟨D, n⟩])

theorem fine_e (f : Frame [entryR W] m m') : Frame (fineR θ W D n) m m' :=
  f.sub fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact ⟨_, List.mem_cons_self, fun _ h => h⟩

theorem fine_w {d k : Nat} (h : d + k ≤ 64) (f : Frame [⟨W + BitVec.ofNat 64 d, k⟩] m m') :
    Frame (fineR θ W D n) m m' :=
  f.sub fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq
    exact ⟨⟨W, 64⟩, by simp, Offset.sub_base W h⟩

theorem fine_w0 (f : Frame [⟨W, 16⟩] m m') : Frame (fineR θ W D n) m m' :=
  f.sub fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq
    exact ⟨⟨W, 64⟩, by simp, Region.sub_prefix (by decide)⟩

theorem fine_c (f : Frame [⟨W + BitVec.ofNat 64 248, 240⟩] m m') : Frame (fineR θ W D n) m m' :=
  f.sub fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact ⟨_, by simp, fun _ h => h⟩

theorem fine_o (f : Frame [wO W] m m') : Frame (fineR θ W D n) m m' :=
  f.sub fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact ⟨_, by simp, fun _ h => h⟩

theorem fine_ld (f : Frame (lRn θ W n ++ [⟨D, n⟩]) m m') : Frame (fineR θ W D n) m m' :=
  f.sub fun q hq => ⟨q, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ hq))), fun _ h => h⟩

theorem fine_l (f : Frame (lRn θ W n) m m') : Frame (fineR θ W D n) m m' :=
  fine_ld (f.sub fun q hq => ⟨q, List.mem_append_left _ hq, fun _ h => h⟩)

theorem fine_d (f : Frame [⟨D, n⟩] m m') : Frame (fineR θ W D n) m m' :=
  fine_ld (f.sub fun q hq => ⟨q, List.mem_append_right _ hq, fun _ h => h⟩)

/-- A buffer, through pieces that write only what `mutR` lists. -/
theorem buf_mut {s : State} {P : Addr} {len : Nat} (hP : Buf K W SP s P len)
    (hPD : (⟨P, len⟩ : Region).Disjoint ⟨D, n⟩) (hf : Frame (mutR W SP D n) m m') :
    bytesAt m' P len = bytesAt m P len :=
  Proof.AesGcm.X86_64.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hP.w.sub_right (Region.sub_prefix (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.stk.symm
    · exact hPD) (Nat.le_of_lt hP.lt)

/-- A buffer, through a piece that writes only in `W`. -/
theorem buf_w {s : State} {P : Addr} {len d k : Nat} (hP : Buf K W SP s P len) (h : d + k ≤ 744)
    (hf : Frame [⟨W + BitVec.ofNat 64 d, k⟩] m m') : bytesAt m' P len = bytesAt m P len :=
  Proof.AesGcm.X86_64.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hP.w.sub_right (Lay.wSub h)) (Nat.le_of_lt hP.lt)

/-- A part of `W`, through a piece that writes another. -/
theorem w_keep (L : Lay K W SP) {a l d k : Nat} (h : a + l ≤ d ∨ d + k ≤ a) (ha : a + l ≤ 744) (hd : d + k ≤ 744)
    (hf : Frame [⟨W + BitVec.ofNat 64 d, k⟩] m m') (hl : l ≤ 2 ^ 64) :
    bytesAt m' (W + BitVec.ofNat 64 a) l = bytesAt m (W + BitVec.ofNat 64 a) l :=
  Proof.AesGcm.X86_64.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact L.w_w h ha hd) hl

/-- The return address is outside what the entry and the pieces write. -/
theorem ret_disj (L : Lay K W SP) (hW : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 744⟩)
    (hD : (⟨SP, 8⟩ : Region).Disjoint ⟨D, n⟩) :
    ∀ r ∈ entryR W :: mutR W SP D n, (⟨SP, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact hW.sub_right (Region.sub_prefix (by decide))
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact Offset.base_disjoint_below SP (by have := L.sp; omega_arith)
  · exact hD

end

/-! ## `vg_aes_gcm_siv_seal` -/

/-- The tag input, from POLYVAL as GHASH of the padded additional data, the
padded data and the lengths block. -/
theorem tagInput_ghash (hpv : GcmSiv.Polyval.PolyvalEq) (a nonce pt aad : List Byte) :
    Spec.GcmSiv.tagInput a nonce pt aad = GcmSiv.tagOf (Spec.GcmSiv.toBytes
      (Spec.Gcm.ghashFrom (GcmSiv.Polyval.mulXG (Spec.GcmSiv.ofBytes a)) 0
        (Spec.GcmSiv.elems (Spec.GcmSiv.pad16 aad) ++ Spec.GcmSiv.elems (Spec.GcmSiv.pad16 pt) ++
          [Spec.GcmSiv.ofBytes (Spec.GcmSiv.le64 (8 * aad.length) ++ Spec.GcmSiv.le64 (8 * pt.length))]))) nonce := by
  obtain hp : (Spec.GcmSiv.pad16 aad ++ Spec.GcmSiv.pad16 pt).length % 16 = 0 := by
    rw [List.length_append]; have := GcmSiv.pad16_mod aad; have := GcmSiv.pad16_mod pt; omega_arith
  rw [GcmSiv.tagInput_eq, Spec.GcmSiv.polyval, hpv, GcmSiv.elems_append hp,
    GcmSiv.elems_append (GcmSiv.pad16_mod _),
    GcmSiv.elems_single (bs := Spec.GcmSiv.le64 (8 * aad.length) ++ Spec.GcmSiv.le64 (8 * pt.length))
      (by simp [Spec.GcmSiv.le64])]

theorem seal_wpG (F : MulFacts) {θ : Nat} {pv cr : Prog isa}
    (hpv : ∀ {K W SP : Addr} (_ : Lay K W SP) {t : State} (_ : Env K W SP t) {R : Nat} {N A D : Addr} {al n : Nat}
      (_ : Slots W R N A D al n t.mem) (_ : Buf K W SP t A al) (_ : Buf K W SP t D n),
      WP isa pv t (PolyPostL θ K W SP A D al n t))
    (hcr : ∀ {K W SP : Addr} (_ : Lay K W SP) {R : Nat} (_ : R = 10 ∨ R = 14) {t : State} (_ : Env K W SP t)
      {N A D : Addr} {al n : Nat} (_ : Slots W R N A D al n t.mem) (_ : Buf K W SP t D n)
      (_ : Covers [⟨D, n⟩] t.wr), WP isa cr t (CryptPostL θ K W SP R D n t))
    {s : State} {K W SP N A D T : Addr} {R al n : Nat}
    (Ar : Args s K W SP N A D R al n) (Tb : TagBuf W SP D n T) (hTw : Covers [⟨T, 16⟩] s.wr)
    (hrT : (⟨SP, 8⟩ : Region).Disjoint ⟨T, 16⟩) (hsp : s.gpr .rsp = SP)
    (hn : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = A) (hr8 : s.gpr .r8 = BitVec.ofNat 64 al) (hr9 : s.gpr .r9 = D) :
    WP isa (.seq (.block entry) (.seq Impl.AesGcmSiv.X86_64Reg.keys (.seq pv
        (.seq (Impl.AesGcmSiv.X86_64Reg.tag tagO) (.seq cr (.block (tagOut ++ restore))))))) s fun s' =>
      gprPreserved s s' ∧
      Spec.GcmSiv.encryptWith (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt s.mem N 12)
        (bytesAt s.mem D n) (bytesAt s.mem A al) = (bytesAt s'.mem D n, bytesAt s'.mem T 16) ∧
      Frame (⟨T, 16⟩ :: fineR θ W D n) s.mem s'.mem := by
  have L := Ar.lay
  have hR := Ar.rounds
  obtain hRb : 16 * (R + 1) ≤ 240 := by rcases hR with h | h <;> subst h <;> decide
  obtain hkl : Spec.GcmSiv.keyLen R ≤ 32 := by unfold Spec.GcmSiv.keyLen; omega_arith
  obtain ⟨s₁, run₁, E₁, S₁, sv₁, f₁, rd₁, wr₁⟩ := entry_ok Ar.perm hsp Ar.args hn hW hdi hsi hdx hcx hr8 hr9
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain hent : ∀ {P : Addr} {len : Nat}, Buf K W SP s P len → bytesAt s₁.mem P len = bytesAt s.mem P len :=
    fun hP => buf_w hP (by decide) f₁
  obtain hK₁ : Spec.GcmSiv.ctxCiph s₁.mem K R = Spec.GcmSiv.ctxCiph s.mem K R :=
    ctxCiph_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_right (Lay.wSub (by decide))) hRb
  obtain bN₁ := Ar.nonce.of_eq rd₁ wr₁
  obtain bA₁ := Ar.aad.of_eq rd₁ wr₁
  obtain bD₁ := Ar.data.of_eq rd₁ wr₁
  -- The keys.
  refine WP.seq ?_
  unfold Impl.AesGcmSiv.X86_64Reg.keys
  refine WP.seq (WP.mono (derive_ok L hR E₁ S₁ bN₁) fun s₂ Dv => ?_)
  obtain f₂ : Frame (mutR W SP D n) s₁.mem s₂.mem := frA (d := 16) (k := 48) (by decide) Dv.frame
  obtain g₂ : Frame (fineR θ W D n) s₁.mem s₂.mem := fine_w (d := 16) (k := 48) (by decide) Dv.frame
  obtain S₂ := slots_mut L Ar.data.w f₂ S₁
  refine WP.mono (expand_ok hR Ar.retW Dv.env S₂) fun s₃ X => ?_
  obtain f₃ : Frame (mutR W SP D n) s₂.mem s₃.mem := frC X.frame
  obtain g₃ : Frame (fineR θ W D n) s₂.mem s₃.mem := fine_c X.frame
  obtain S₃ := slots_mut L Ar.data.w f₃ S₂
  obtain rd₃ : s₃.rd = s.rd := by rw [X.rd, Dv.rd, rd₁]
  obtain wr₃ : s₃.wr = s.wr := by rw [X.wr, Dv.wr, wr₁]
  obtain b3 : ∀ {P : Addr} {len : Nat}, Buf K W SP s P len → bytesAt s₃.mem P len = bytesAt s.mem P len :=
    fun hP => by rw [buf_w hP (by decide) X.frame, buf_w hP (by decide) Dv.frame, hent hP]
  -- POLYVAL.
  refine WP.seq (WP.mono (hpv L X.env S₃ (Ar.aad.of_eq rd₃ wr₃) (Ar.data.of_eq rd₃ wr₃)) fun s₄ Po => ?_)
  obtain f₄ : Frame (mutR W SP D n) s₃.mem s₄.mem := frL Po.frame
  obtain g₄ : Frame (fineR θ W D n) s₃.mem s₄.mem := fine_l Po.fine
  obtain S₄ := slots_mut L Ar.data.w f₄ S₃
  obtain rd₄ : s₄.rd = s.rd := Po.rd.trans rd₃
  obtain wr₄ : s₄.wr = s.wr := Po.wr.trans wr₃
  obtain b4 : ∀ {P : Addr} {len : Nat}, Buf K W SP s P len → bytesAt s₄.mem P len = bytesAt s.mem P len :=
    fun hP => by rw [bufL hP Po.frame, b3 hP]
  -- The tag.
  refine WP.seq (WP.mono (tag_ok L hR Po.env S₄ (Ar.nonce.of_eq rd₄ wr₄) (o := 0) (.inl rfl)) fun s₅ Tg => ?_)
  obtain f₅ : Frame (mutR W SP D n) s₄.mem s₅.mem := frA (d := 0) (k := 16) (by decide) Tg.frame
  obtain g₅ : Frame (fineR θ W D n) s₄.mem s₅.mem := fine_w (d := 0) (k := 16) (by decide) Tg.frame
  obtain S₅ := slots_mut L Ar.data.w f₅ S₄
  obtain rd₅ : s₅.rd = s.rd := Tg.rd.trans rd₄
  obtain wr₅ : s₅.wr = s.wr := Tg.wr.trans wr₄
  obtain b5 : ∀ {P : Addr} {len : Nat}, Buf K W SP s P len → bytesAt s₅.mem P len = bytesAt s.mem P len :=
    fun hP => by rw [buf_w hP (by decide) Tg.frame, b4 hP]
  -- Counter mode.
  refine WP.seq (WP.mono (hcr L hR Tg.env S₅ (Ar.data.of_eq rd₅ wr₅) (by rw [wr₅]; exact Ar.dw))
    fun s₆ Cr => ?_)
  obtain f₆ : Frame (mutR W SP D n) s₅.mem s₆.mem := frLD Cr.frame
  obtain gall : Frame (fineR θ W D n) s.mem s₆.mem :=
    (fine_e f₁).trans ((((g₂.trans g₃).trans g₄).trans g₅).trans (fine_ld Cr.fine))
  obtain f₁₆ : Frame (mutR W SP D n) s₁.mem s₆.mem := (((f₂.trans f₃).trans f₄).trans f₅).trans f₆
  obtain fall : Frame (entryR W :: mutR W SP D n) s.mem s₆.mem :=
    (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩).trans
    (f₁₆.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)
  obtain r₆ : s₆.rd = s.rd := Cr.rd.trans rd₅
  obtain w₆ : s₆.wr = s.wr := Cr.wr.trans wr₅
  -- The copy of the tag, and `restore`.
  obtain hTa : InRegions (s₆.rd ++ s₆.wr) (SP + BitVec.ofNat 64 16) 8 := by
    obtain h := Proof.AesGcm.X86_64.in_off (d := 8) (n := 8) Ar.args (by decide) (by decide)
    rw [add_ofNat_assoc] at h
    rw [r₆, w₆]; exact h
  obtain ⟨s₇, run₇, fT, hT₇, hg₇, rd₇, wr₇⟩ := tagOut_ok Cr.env (by rw [argT_kept fall Ar.argsW Ar.argsD, hT]) hTa
    (by rw [w₆]; exact hTw) Tb.w
  obtain E₇ : Env K W SP s₇ := Cr.env.of_saved hg₇ rd₇ wr₇
  obtain dT : ∀ q ∈ [(⟨T, 16⟩ : Region)], ∀ p ∈ saved, (⟨W + BitVec.ofNat 64 p.2, 8⟩ : Region).Disjoint q := by
    intro q hq p hp
    simp only [List.mem_singleton] at hq; subst hq
    obtain hd : 144 ≤ p.2 ∧ p.2 + 8 ≤ 192 := by
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (Tb.w.sub_right (Lay.wSub (by omega_arith))).symm
  obtain sv₇ : Saved s₇.mem W s.gpr := fun p hp => by
    rw [← saved_mut L Ar.data.w f₁₆ sv₁ p hp]
    exact fT.readW (r := ⟨W + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _)
      (fun q hq => dT q hq p hp) (by decide)
  obtain ⟨s₈, run₈, hg₈, hm₈, hsp₈, _⟩ := restore_ok E₇ sv₇
  refine WP.of_runBlock ⟨s₈, by rw [VG.Interleave.runBlock_append, run₇]; exact run₈, ⟨fun r hr => ?_, ?_⟩, ?_, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg₈ (.rbx, 144) (by decide)
    · exact hg₈ (.rbp, 152) (by decide)
    · rw [hsp₈, E₇.rsp, hsp]
    · exact hg₈ (.r12, 160) (by decide)
    · exact hg₈ (.r13, 168) (by decide)
    · exact hg₈ (.r14, 176) (by decide)
    · exact hg₈ (.r15, 184) (by decide)
  · rw [hm₈, hsp, fT.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact hrT) (by decide)]
    exact fall.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (ret_disj L Ar.retW Ar.retD) (by decide)
  · have hk := Dv.keys hR
    rw [hK₁, hent Ar.nonce] at hk
    obtain a₃ : bytesAt s₃.mem (W + BitVec.ofNat 64 16) 16 = bytesAt s₂.mem (W + BitVec.ofNat 64 16) 16 :=
      w_keep L (.inl (by decide)) (by decide) (by decide) X.frame (by decide)
    obtain key₄ : Spec.GcmSiv.ctxCiph s₄.mem (W + BitVec.ofNat 64 248) R =
        Spec.GcmSiv.ctxCiph s₃.mem (W + BitVec.ofNat 64 248) R := keyL L Po.frame hRb
    obtain key₅ : Spec.GcmSiv.ctxCiph s₅.mem (W + BitVec.ofNat 64 248) R =
        Spec.GcmSiv.ctxCiph s₄.mem (W + BitVec.ofNat 64 248) R :=
      ctxCiph_frame Tg.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.w_w (.inr (by decide)) (by decide) (by decide)) hRb
    obtain tg : bytesAt s₅.mem W 16 = Spec.GcmSiv.aes (bytesAt s₂.mem (W + BitVec.ofNat 64 32) (Spec.GcmSiv.keyLen R))
        (Spec.GcmSiv.tagInput (bytesAt s₂.mem (W + BitVec.ofNat 64 16) 16) (bytesAt s.mem N 12) (bytesAt s.mem D n)
          (bytesAt s.mem A al)) := by
      have := Tg.out
      rw [show W + BitVec.ofNat 64 0 = W from BitVec.add_zero W] at this
      rw [this, key₄, X.ciph, Po.out, hOf, a₃, b4 Ar.nonce, b3 Ar.aad, b3 Ar.data, tagInput_ghash F.pv,
        Proof.Cmac.bytesAt_length, Proof.Cmac.bytesAt_length]
    obtain t₆ : bytesAt s₆.mem W 16 = bytesAt s₅.mem W 16 := tagLD L Ar.data.w Cr.frame
    obtain d₈ : bytesAt s₈.mem D n = bytesAt s₆.mem D n := by
      rw [hm₈]; exact Proof.AesGcm.X86_64.bytesAt_frame fT (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact Tb.d.symm) (Nat.le_of_lt Ar.data.lt)
    unfold Spec.GcmSiv.encryptWith
    rw [hk, d₈, hm₈, hT₇, Cr.data, t₆, b5 Ar.data, key₅, key₄, X.ciph, tg]

  · rw [hm₈]
    exact (gall.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩).trans (fT.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩)

/-- `vg_aes_gcm_siv_seal`, for its arguments. -/
theorem seal_wp' (F : MulFacts) {s : State} {K W SP N A D T : Addr} {R al n : Nat}
    (Ar : Args s K W SP N A D R al n) (Tb : TagBuf W SP D n T) (hTw : Covers [⟨T, 16⟩] s.wr)
    (hrT : (⟨SP, 8⟩ : Region).Disjoint ⟨T, 16⟩) (hsp : s.gpr .rsp = SP)
    (hn : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = A) (hr8 : s.gpr .r8 = BitVec.ofNat 64 al) (hr9 : s.gpr .r9 = D) :
    WP isa Impl.AesGcmSiv.X86_64Reg.seal s fun s' => gprPreserved s s' ∧
      Spec.GcmSiv.encryptWith (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt s.mem N 12)
        (bytesAt s.mem D n) (bytesAt s.mem A al) = (bytesAt s'.mem D n, bytesAt s'.mem T 16) ∧
      Frame (⟨T, 16⟩ :: fineR (2 ^ 64) W D n) s.mem s'.mem :=
  seal_wpG F
    (fun L _ E _ _ _ _ _ _ S hA hD => WP.mono (polyval_ok F L E S hA hD) fun _ P =>
      ⟨P.env, P.rd, P.wr, toL P.frame, toLn P.frame, P.out⟩)
    (fun L _ hR _ E _ _ _ _ _ S hD hDw => WP.mono (crypt_ok L hR E S hD hDw) fun _ P =>
      ⟨P.env, P.rd, P.wr, toLD P.frame, toLDn P.frame, P.data⟩)
    Ar Tb hTw hrT hsp hn hT hW hdi hsi hdx hcx hr8 hr9

/-- `vg_aes_gcm_siv_seal` with the loops, for its arguments. -/
theorem sealL_wp' (F : MulFacts) {lp : Impl.AesGcmSiv.X86_64Stitch.Loops}
    (hlp : Proof.AesGcmSiv.X86_64.Stitch.LoopsOk lp) {s : State} {K W SP N A D T : Addr} {R al n : Nat}
    (Ar : Args s K W SP N A D R al n) (Tb : TagBuf W SP D n T) (hTw : Covers [⟨T, 16⟩] s.wr)
    (hrT : (⟨SP, 8⟩ : Region).Disjoint ⟨T, 16⟩) (hsp : s.gpr .rsp = SP)
    (hn : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = A) (hr8 : s.gpr .r8 = BitVec.ofNat 64 al) (hr9 : s.gpr .r9 = D) :
    WP isa (Impl.AesGcmSiv.X86_64Reg.sealL lp) s fun s' => gprPreserved s s' ∧
      Spec.GcmSiv.encryptWith (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt s.mem N 12)
        (bytesAt s.mem D n) (bytesAt s.mem A al) = (bytesAt s'.mem D n, bytesAt s'.mem T 16) ∧
      Frame (⟨T, 16⟩ :: fineR 256 W D n) s.mem s'.mem :=
  seal_wpG F (fun L _ E _ _ _ _ _ _ S hA hD => polyvalL_ok F hlp L E S hA hD)
    (fun L _ hR _ E _ _ _ _ _ S hD hDw => cryptL_ok hlp L hR E S hD hDw)
    Ar Tb hTw hrT hsp hn hT hW hdi hsi hdx hcx hr8 hr9

/-- `vg_aes_gcm_siv_seal` with the loops. -/
theorem sealL_wp (F : MulFacts) {lp : Impl.AesGcmSiv.X86_64Stitch.Loops}
    (hlp : Proof.AesGcmSiv.X86_64.Stitch.LoopsOk lp) {s : State} (h : sealPre s) :
    WP isa (Impl.AesGcmSiv.X86_64Reg.sealL lp) s fun s' => gprPreserved s s' ∧ sealX86_64.post s s' ∧
      Frame (⟨arg s 1, 16⟩ :: fineR 256 (arg s 2) (s.gpr .r9) (arg s 0).toNat) s.mem s'.mem := by
  obtain ⟨⟨Ar, Tb⟩, hTw, hrT⟩ := args_of_seal h
  exact sealL_wp' F hlp Ar Tb hTw hrT rfl (ofNat_toNat64 _).symm rfl rfl rfl (ofNat_toNat64 _).symm rfl rfl
    (ofNat_toNat64 _).symm rfl

/-- `vg_aes_gcm_siv_seal`. -/
theorem seal_wp (F : MulFacts) {s : State} (h : sealPre s) :
    WP isa Impl.AesGcmSiv.X86_64Reg.seal s fun s' => gprPreserved s s' ∧ sealX86_64.post s s' ∧
      Frame (⟨arg s 1, 16⟩ :: fineR (2 ^ 64) (arg s 2) (s.gpr .r9) (arg s 0).toNat) s.mem s'.mem := by
  obtain ⟨⟨Ar, Tb⟩, hTw, hrT⟩ := args_of_seal h
  exact seal_wp' F Ar Tb hTw hrT rfl (ofNat_toNat64 _).symm rfl rfl rfl (ofNat_toNat64 _).symm rfl rfl
    (ofNat_toNat64 _).symm rfl

/-! ## `vg_aes_gcm_siv_open` -/

/-- `open`'s code as its head and its tail (`openHead`, `openTail`). -/
theorem open_shape {e r k m tg cm tl : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq e (.seq r (.seq k (.seq m (.seq tg (.seq cm tl)))))) s Q) :
    WP isa (.seq (.seq e (.seq r (.seq k (.seq m (.seq tg cm))))) tl) s Q :=
  WP.seq (WP.seq (WP.mono (WP.seq_iff.mp h) fun _ h => WP.seq (WP.mono (WP.seq_iff.mp h) fun _ h =>
    WP.seq (WP.mono (WP.seq_iff.mp h) fun _ h => WP.seq (WP.mono (WP.seq_iff.mp h) fun _ h =>
      WP.seq (WP.mono (WP.seq_iff.mp h) fun _ h => WP.seq_iff.mp h))))))

theorem open_wpG (F : MulFacts) {θ : Nat} {mid mk : Prog isa}
    (hmid : ∀ {K W SP : Addr} (_ : Lay K W SP) {R : Nat} (_ : R = 10 ∨ R = 14) {t : State} (_ : Env K W SP t)
      {N A D : Addr} {al n : Nat} (_ : Slots W R N A D al n t.mem) (_ : Buf K W SP t A al) (_ : Buf K W SP t D n)
      (_ : Covers [⟨D, n⟩] t.wr) (_ : (⟨A, al⟩ : Region).Disjoint ⟨D, n⟩),
      WP isa mid t (DecPost θ K W SP R A D al n t))
    (hmk : ∀ {K W SP : Addr} {t : State} (_ : Env K W SP t) {R : Nat} {N A D : Addr} {al n : Nat}
      (_ : Slots W R N A D al n t.mem) (_ : Buf K W SP t D n) (_ : Covers [⟨D, n⟩] t.wr) {c : Prop} [Decidable c]
      (_ : t.mem.readW (W + BitVec.ofNat 64 192) 64 = if c then 1#64 else 0#64),
      WP isa mk t (MaskPost K W SP D n c t))
    {s : State} {K W SP N A D T : Addr} {R al n : Nat}
    (Ar : Args s K W SP N A D R al n) (Tb : TagBuf W SP D n T) (hTr : Covers [⟨T, 16⟩] (s.rd ++ s.wr))
    (hsp : s.gpr .rsp = SP)
    (hn : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = A) (hr8 : s.gpr .r8 = BitVec.ofNat 64 al) (hr9 : s.gpr .r9 = D) :
    WP isa (.seq (.block entry) (.seq (.block recv) (.seq Impl.AesGcmSiv.X86_64Reg.keys (.seq mid
        (.seq (Impl.AesGcmSiv.X86_64Reg.tag bO) (.seq (.block cmp) (.seq mk
          (.block (([.mov .rax (.mem (at_ .r15 okO))] : List Instr) ++ restore))))))))) s fun s' =>
      gprPreserved s s' ∧
      openPost (Spec.GcmSiv.decryptWith (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt s.mem N 12)
        (bytesAt s.mem D n) (bytesAt s.mem A al) (bytesAt s.mem T 16)) s' D n ∧
      Frame (fineR θ W D n) s.mem s'.mem := by
  have L := Ar.lay
  have hR := Ar.rounds
  obtain hRb : 16 * (R + 1) ≤ 240 := by rcases hR with h | h <;> subst h <;> decide
  obtain ⟨s₀, run₀, E₀, S₀, sv₀, f₀, rd₀, wr₀⟩ := entry_ok Ar.perm hsp Ar.args hn hW hdi hsi hdx hcx hr8 hr9
  refine WP.seq (WP.of_runBlock ⟨s₀, run₀, ?_⟩)
  obtain f₀' : Frame (entryR W :: mutR W SP D n) s.mem s₀.mem :=
    f₀.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  -- The received tag, copied to `W`.
  obtain hTa : InRegions (s₀.rd ++ s₀.wr) (SP + BitVec.ofNat 64 16) 8 := by
    obtain h := Proof.AesGcm.X86_64.in_off (d := 8) (n := 8) Ar.args (by decide) (by decide)
    rw [add_ofNat_assoc] at h
    rw [rd₀, wr₀]; exact h
  obtain ⟨s₁, run₁, fR, hR₁, hgR, rdR, wrR⟩ := recv_ok E₀ (by rw [argT_kept f₀' Ar.argsW Ar.argsD, hT]) hTa
    ((Tb.buf (s := s) hTr).of_eq rd₀ wr₀)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain E₁ : Env K W SP s₁ := E₀.of_saved hgR rdR wrR
  obtain fR' : Frame (mutR W SP D n) s₀.mem s₁.mem := fR.sub fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact ⟨wA W, by simp, Region.sub_prefix (by decide)⟩
  obtain S₁ := slots_mut L Ar.data.w fR' S₀
  obtain rd₁ : s₁.rd = s.rd := by rw [rdR, rd₀]
  obtain wr₁ : s₁.wr = s.wr := by rw [wrR, wr₀]
  obtain f₁ : Frame (entryR W :: mutR W SP D n) s.mem s₁.mem :=
    f₀'.trans (fR'.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)
  obtain f₀₁ : Frame [entryR W, ⟨W, 16⟩] s.mem s₁.mem :=
    (f₀.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩).trans
    (fR.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨⟨W, 16⟩, by simp, fun _ h => h⟩)
  obtain hent : ∀ {P : Addr} {len : Nat}, Buf K W SP s P len → bytesAt s₁.mem P len = bytesAt s.mem P len :=
    fun hP => Proof.AesGcm.X86_64.bytesAt_frame f₀₁ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hP.w.sub_right (Lay.wSub (by decide))
      · exact hP.w.sub_right (Region.sub_prefix (by decide)))
      (Nat.le_of_lt hP.lt)
  obtain hK₁ : Spec.GcmSiv.ctxCiph s₁.mem K R = Spec.GcmSiv.ctxCiph s.mem K R :=
    ctxCiph_frame f₀₁ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.k_w.sub_right (Lay.wSub (by decide))
      · exact L.k_w.sub_right (Region.sub_prefix (by decide))) hRb
  obtain hT₁ : bytesAt s₁.mem W 16 = bytesAt s.mem T 16 := by
    rw [hR₁]; exact tag_kept Tb f₀'
  obtain bN₁ := Ar.nonce.of_eq rd₁ wr₁
  -- A block at `W`, through a piece that writes elsewhere in `W`.
  obtain w0 : ∀ {m m' : Mem} {d k : Nat}, 16 ≤ d → d + k ≤ 744 → Frame [⟨W + BitVec.ofNat 64 d, k⟩] m m' →
      bytesAt m' W 16 = bytesAt m W 16 := fun h₁ h₂ hf =>
    Proof.AesGcm.X86_64.bytesAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simpa using L.w_w (a := 0) (n := 16) (.inl h₁) (by decide) h₂) (by decide)
  -- The keys.
  refine WP.seq ?_
  unfold Impl.AesGcmSiv.X86_64Reg.keys
  refine WP.seq (WP.mono (derive_ok L hR E₁ S₁ bN₁) fun s₂ Dv => ?_)
  obtain f₂ : Frame (mutR W SP D n) s₁.mem s₂.mem := frA (d := 16) (k := 48) (by decide) Dv.frame
  obtain g₂ : Frame (fineR θ W D n) s₁.mem s₂.mem := fine_w (d := 16) (k := 48) (by decide) Dv.frame
  obtain S₂ := slots_mut L Ar.data.w f₂ S₁
  refine WP.mono (expand_ok hR Ar.retW Dv.env S₂) fun s₃ X => ?_
  obtain f₃ : Frame (mutR W SP D n) s₂.mem s₃.mem := frC X.frame
  obtain g₃ : Frame (fineR θ W D n) s₂.mem s₃.mem := fine_c X.frame
  obtain S₃ := slots_mut L Ar.data.w f₃ S₂
  obtain rd₃ : s₃.rd = s.rd := by rw [X.rd, Dv.rd, rd₁]
  obtain wr₃ : s₃.wr = s.wr := by rw [X.wr, Dv.wr, wr₁]
  obtain b3 : ∀ {P : Addr} {len : Nat}, Buf K W SP s P len → bytesAt s₃.mem P len = bytesAt s.mem P len :=
    fun hP => by rw [buf_w hP (by decide) X.frame, buf_w hP (by decide) Dv.frame, hent hP]
  obtain tag₃ : bytesAt s₃.mem W 16 = bytesAt s.mem T 16 := by
    rw [w0 (by decide) (by decide) X.frame, w0 (by decide) (by decide) Dv.frame, hT₁]
  -- Counter mode from the received tag, and POLYVAL of the plaintext.
  refine WP.seq (WP.mono (hmid L hR X.env S₃ (Ar.aad.of_eq rd₃ wr₃) (Ar.data.of_eq rd₃ wr₃)
    (by rw [wr₃]; exact Ar.dw) Ar.ad) fun s₅ Dc => ?_)
  obtain f₅ : Frame (mutR W SP D n) s₃.mem s₅.mem := frLD Dc.frame
  obtain g₅ : Frame (fineR θ W D n) s₃.mem s₅.mem := fine_ld Dc.fine
  obtain S₅ := slots_mut L Ar.data.w f₅ S₃
  obtain rd₅ : s₅.rd = s.rd := Dc.rd.trans rd₃
  obtain wr₅ : s₅.wr = s.wr := Dc.wr.trans wr₃
  -- What is outside the data, through them.
  obtain cK : ∀ {P : Addr} {len : Nat}, (⟨P, len⟩ : Region).Disjoint ⟨W, 744⟩ →
      (⟨P, len⟩ : Region).Disjoint ⟨D, n⟩ → len ≤ 2 ^ 64 → bytesAt s₅.mem P len = bytesAt s₃.mem P len :=
    fun hPW hPD hl => Proof.AesGcm.X86_64.bytesAt_frame Dc.frame (fun q hq => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact hPW.sub_right (Lay.wSub (by decide))
      · exact hPW.sub_right (Lay.wSub (by decide))
      · exact hPD) hl
  obtain wD : ∀ {d k : Nat}, d + k ≤ 744 → (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint ⟨D, n⟩ :=
    fun h => (Ar.data.w.sub_right (Lay.wSub h)).symm
  -- Its tag at `W + 128`.
  refine WP.seq (WP.mono (tag_ok L hR Dc.env S₅ (Ar.nonce.of_eq rd₅ wr₅) (o := 128) (.inr rfl)) fun s₆ Tg => ?_)
  obtain f₆ : Frame (mutR W SP D n) s₅.mem s₆.mem := frA (d := 128) (k := 16) (by decide) Tg.frame
  obtain g₆ : Frame (fineR θ W D n) s₅.mem s₆.mem := fine_l (toLn Tg.frame)
  obtain S₆ := slots_mut L Ar.data.w f₆ S₅
  obtain rd₆ : s₆.rd = s.rd := Tg.rd.trans rd₅
  obtain wr₆ : s₆.wr = s.wr := Tg.wr.trans wr₅
  -- The comparison.
  obtain ⟨s₇, run₇, hm₇, hg₇, hrd₇, hwr₇⟩ := cmp_ok Tg.env
  refine WP.seq (WP.of_runBlock ⟨s₇, run₇, ?_⟩)
  obtain E₇ : Env K W SP s₇ := Tg.env.of_saved hg₇ hrd₇ hwr₇
  obtain fO : Frame [wO W] s₆.mem s₇.mem := by
    rw [hm₇]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain f₇ : Frame (mutR W SP D n) s₆.mem s₇.mem :=
    fO.sub fun q hq => ⟨q, by simp only [List.mem_singleton] at hq; subst hq; simp, fun _ h => h⟩
  obtain S₇ := slots_mut L Ar.data.w f₇ S₆
  obtain hok : s₇.mem.readW (W + BitVec.ofNat 64 192) 64 =
      if bytesAt s₆.mem (W + BitVec.ofNat 64 128) 16 = bytesAt s₆.mem W 16 then 1#64 else 0#64 := by
    rw [hm₇, Mem.readW_writeW_self64]
    by_cases hc : bytesAt s₆.mem W 16 = bytesAt s₆.mem (W + BitVec.ofNat 64 128) 16
    · simp only [hc, ↓reduceIte]
    · simp only [hc, Ne.symm hc, ↓reduceIte]
  -- The mask.
  refine WP.seq (WP.mono (hmk E₇ S₇ (Ar.data.of_eq (by rw [hrd₇, rd₆]) (by rw [hwr₇, wr₆]))
    (by rw [hwr₇, wr₆]; exact Ar.dw) hok) fun s₈ Mk => ?_)
  -- `ok` and the restore.
  have h15₈ := Mk.env.r15
  obtain rO := Mk.env.perm.wR (show 192 + 8 ≤ 744 by decide)
  obtain ⟨s₉, run₉, hax₉, hm₉, hg₉, hrd₉, hwr₉⟩ : ∃ s₉ : State, runBlock isa [.mov .rax (.mem (at_ .r15 okO))] s₈ =
      some s₉ ∧ s₉.gpr .rax = s₈.mem.readW (W + BitVec.ofNat 64 192) 64 ∧ s₉.mem = s₈.mem ∧
      (∀ r, r ≠ .rax → s₉.gpr r = s₈.gpr r) ∧ s₉.rd = s₈.rd ∧ s₉.wr = s₈.wr := by
    refine ⟨_, by srun [h15₈, rO], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true]
    · rfl
    · intro r h; simp only [gpr_setReg, h, ite_false]
    all_goals rfl
  obtain E₉ : Env K W SP s₉ := Mk.env.keep (fun r hr => hg₉ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)) hrd₉ hwr₉
  obtain fall : Frame (mutR W SP D n) s₁.mem s₈.mem :=
    (((((f₂.trans f₃).trans f₅).trans f₆).trans f₇)).trans
      (Mk.frame.sub fun q hq => ⟨q, by simp only [List.mem_singleton] at hq; subst hq; simp, fun _ h => h⟩)
  obtain ⟨s₁₀, run₁₀, hg₁₀, hm₁₀, hsp₁₀, hax₁₀⟩ :=
    restore_ok E₉ (by rw [hm₉]; exact saved_mut L Ar.data.w (fR'.trans fall) sv₀)
  refine WP.of_runBlock ⟨s₁₀, by rw [VG.Interleave.runBlock_append, run₉]; exact run₁₀, ⟨fun r hr => ?_, ?_⟩, ?_, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg₁₀ (.rbx, 144) (by decide)
    · exact hg₁₀ (.rbp, 152) (by decide)
    · rw [hsp₁₀, E₉.rsp, hsp]
    · exact hg₁₀ (.r12, 160) (by decide)
    · exact hg₁₀ (.r13, 168) (by decide)
    · exact hg₁₀ (.r14, 176) (by decide)
    · exact hg₁₀ (.r15, 184) (by decide)
  · have fall' : Frame (entryR W :: mutR W SP D n) s.mem s₈.mem :=
      f₁.trans (fall.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)
    rw [hm₁₀, hm₉, hsp]
    exact fall'.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (ret_disj L Ar.retW Ar.retD) (by decide)
  · have hk := Dv.keys hR
    rw [hK₁, hent Ar.nonce] at hk
    obtain a₃ : bytesAt s₃.mem (W + BitVec.ofNat 64 16) 16 = bytesAt s₂.mem (W + BitVec.ofNat 64 16) 16 :=
      w_keep L (.inl (by decide)) (by decide) (by decide) X.frame (by decide)
    obtain key₅ : Spec.GcmSiv.ctxCiph s₅.mem (W + BitVec.ofNat 64 248) R =
        Spec.GcmSiv.ctxCiph s₃.mem (W + BitVec.ofNat 64 248) R := ctxCiph_frame Dc.frame (key_lR L Ar.data) hRb
    have pt₄ := Dc.data
    rw [tag₃, b3 Ar.data, X.ciph] at pt₄
    obtain n₅ : bytesAt s₅.mem N 12 = bytesAt s.mem N 12 := by
      rw [cK Ar.nonce.w Ar.nd (by decide), b3 Ar.nonce]
    obtain tg : bytesAt s₆.mem (W + BitVec.ofNat 64 128) 16 =
        Spec.GcmSiv.aes (bytesAt s₂.mem (W + BitVec.ofNat 64 32) (Spec.GcmSiv.keyLen R))
        (Spec.GcmSiv.tagInput (bytesAt s₂.mem (W + BitVec.ofNat 64 16) 16) (bytesAt s.mem N 12) (bytesAt s₅.mem D n)
          (bytesAt s.mem A al)) := by
      rw [Tg.out, key₅, X.ciph, Dc.out, hOf, a₃, n₅, b3 Ar.aad, tagInput_ghash F.pv,
        Proof.Cmac.bytesAt_length, Proof.Cmac.bytesAt_length]
    obtain tag₆ : bytesAt s₆.mem W 16 = bytesAt s.mem T 16 := by
      rw [w0 (by decide) (by decide) Tg.frame, tagLD L Ar.data.w Dc.frame, tag₃]
    obtain d₇ : bytesAt s₇.mem D n = bytesAt s₅.mem D n := by
      rw [buf_w Ar.data (d := 192) (k := 8) (by decide) fO, buf_w Ar.data (by decide) Tg.frame]
    obtain ax : s₁₀.gpr .rax = s₇.mem.readW (W + BitVec.ofNat 64 192) 64 := by
      rw [hax₁₀, hax₉, Mk.frame.readW (r := ⟨W + BitVec.ofNat 64 192, 8⟩) (Region.contains_self _ _) (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact wD (by decide)) (by decide)]
    have md := Mk.data
    obtain ax' := ax.trans hok
    obtain e1 : bytesAt s₂.mem (W + BitVec.ofNat 64 16) 16 = (Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem K R)
        (Spec.GcmSiv.keyLen R) (bytesAt s.mem N 12)).1 := by rw [hk]
    obtain e2 : bytesAt s₂.mem (W + BitVec.ofNat 64 32) (Spec.GcmSiv.keyLen R) =
        (Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt s.mem N 12)).2 := by
      rw [hk]
    rw [tg, tag₆, pt₄, e1, e2] at ax'
    rw [tg, tag₆, d₇, pt₄, e1, e2] at md
    obtain hdec : Spec.GcmSiv.decryptWith (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt s.mem N 12)
        (bytesAt s.mem D n) (bytesAt s.mem A al) (bytesAt s.mem T 16) =
        let dk := Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt s.mem N 12)
        if Spec.GcmSiv.aes dk.2 (Spec.GcmSiv.tagInput dk.1 (bytesAt s.mem N 12)
            (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem T 16)) (bytesAt s.mem D n))
            (bytesAt s.mem A al)) = bytesAt s.mem T 16 then
          some (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem T 16)) (bytesAt s.mem D n))
        else none := by
      unfold Spec.GcmSiv.decryptWith
      rw [← Prod.eta (Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R)
        (bytesAt s.mem N 12))]
    simp only at hdec
    generalize Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt s.mem N 12) = dk
      at md ax' hdec
    rw [hdec]
    refine Or.elim (Classical.em (Spec.GcmSiv.aes dk.2 (Spec.GcmSiv.tagInput dk.1 (bytesAt s.mem N 12)
      (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem T 16)) (bytesAt s.mem D n))
      (bytesAt s.mem A al)) = bytesAt s.mem T 16)) (fun hc => ?_) (fun hc => ?_)
    · refine openPost_some (by rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]) ?_ ?_
      · rw [ax']; simp only [hc, ↓reduceIte]; decide
      · rw [hm₁₀, hm₉, md]; simp only [hc, ↓reduceIte]
    · refine openPost_none (by rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]) ?_ ?_
      · rw [ax']; simp only [hc, ↓reduceIte]; decide
      · rw [hm₁₀, hm₉, md]; simp only [hc, ↓reduceIte]

  · rw [hm₁₀, hm₉]
    exact (fine_e f₀).trans ((fine_w0 fR).trans (((((g₂.trans g₃).trans g₅).trans g₆).trans (fine_o fO)).trans
      (fine_d Mk.frame)))

/-- `vg_aes_gcm_siv_open`, for its arguments. -/
theorem open_wp' (F : MulFacts) {s : State} {K W SP N A D T : Addr} {R al n : Nat}
    (Ar : Args s K W SP N A D R al n) (Tb : TagBuf W SP D n T) (hTr : Covers [⟨T, 16⟩] (s.rd ++ s.wr))
    (hsp : s.gpr .rsp = SP)
    (hn : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = A) (hr8 : s.gpr .r8 = BitVec.ofNat 64 al) (hr9 : s.gpr .r9 = D) :
    WP isa Impl.AesGcmSiv.X86_64Reg.open s fun s' => gprPreserved s s' ∧
      openPost (Spec.GcmSiv.decryptWith (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt s.mem N 12)
        (bytesAt s.mem D n) (bytesAt s.mem A al) (bytesAt s.mem T 16)) s' D n ∧
      Frame (fineR (2 ^ 64) W D n) s.mem s'.mem := by
  have h := open_wpG F (θ := 2 ^ 64) (mid := .seq Impl.AesGcmSiv.X86_64Reg.crypt Impl.AesGcmSiv.X86_64Reg.polyval)
    (fun L _ hR _ E _ _ _ _ _ S hA hD hDw hAD => decS_ok F L hR E S hA hD hDw hAD) wipeBad_ok
    Ar Tb hTr hsp hn hT hW hdi hsi hdx hcx hr8 hr9
  exact open_shape h

/-- `vg_aes_gcm_siv_open` with the loops, for its arguments. -/
theorem openL_wp' (F : MulFacts) {lp : Impl.AesGcmSiv.X86_64Stitch.Loops}
    (hlp : Proof.AesGcmSiv.X86_64.Stitch.LoopsOk lp) {s : State} {K W SP N A D T : Addr} {R al n : Nat}
    (Ar : Args s K W SP N A D R al n) (Tb : TagBuf W SP D n T) (hTr : Covers [⟨T, 16⟩] (s.rd ++ s.wr))
    (hsp : s.gpr .rsp = SP)
    (hn : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = A) (hr8 : s.gpr .r8 = BitVec.ofNat 64 al) (hr9 : s.gpr .r9 = D) :
    WP isa (Impl.AesGcmSiv.X86_64Reg.openL lp) s fun s' => gprPreserved s s' ∧
      openPost (Spec.GcmSiv.decryptWith (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt s.mem N 12)
        (bytesAt s.mem D n) (bytesAt s.mem A al) (bytesAt s.mem T 16)) s' D n ∧
      Frame (fineR 256 W D n) s.mem s'.mem := by
  have h := open_wpG F
    (mid := .seq (.block Impl.AesGcmSiv.X86_64Reg.lenCmp) (.ite .b
      (.seq Impl.AesGcmSiv.X86_64Reg.crypt Impl.AesGcmSiv.X86_64Reg.polyval) (Impl.AesGcmSiv.X86_64Reg.decL lp)))
    (fun L _ hR _ E _ _ _ _ _ S hA hD hDw hAD => decMid_ok F hlp L hR E S hA hD hDw hAD) wipeBad_ok
    Ar Tb hTr hsp hn hT hW hdi hsi hdx hcx hr8 hr9
  exact open_shape h

/-- `open` up to the comparison, then the mask at every outcome: what the
constant-time proof asks of the comparison's outcome. -/
theorem openL_probe (F : MulFacts) {lp : Impl.AesGcmSiv.X86_64Stitch.Loops}
    (hlp : Proof.AesGcmSiv.X86_64.Stitch.LoopsOk lp) {s : State} (h : openPre s) :
    WP isa (.seq (Impl.AesGcmSiv.X86_64Reg.openHead (.seq (.block Impl.AesGcmSiv.X86_64Reg.lenCmp) (.ite .b
        (.seq Impl.AesGcmSiv.X86_64Reg.crypt Impl.AesGcmSiv.X86_64Reg.polyval) (Impl.AesGcmSiv.X86_64Reg.decL lp))))
      (.seq mask (.block (([.mov .rax (.mem (at_ .r15 okO))] : List Instr) ++ restore)))) s fun s' =>
      gprPreserved s s' ∧ openX86_64.post s s' := by
  obtain ⟨⟨Ar, Tb⟩, hTr⟩ := args_of_open h
  exact WP.mono (open_shape (open_wpG F (fun L _ hR _ E _ _ _ _ _ S hA hD hDw hAD => decMid_ok F hlp L hR E S hA hD hDw hAD)
    mask_ok Ar Tb hTr rfl (ofNat_toNat64 _).symm rfl rfl rfl (ofNat_toNat64 _).symm rfl rfl (ofNat_toNat64 _).symm rfl))
    fun _ h => ⟨h.1, h.2.1⟩

/-- As `openL_probe`, without the loops. -/
theorem open_probe (F : MulFacts) {s : State} (h : openPre s) :
    WP isa (.seq (Impl.AesGcmSiv.X86_64Reg.openHead
        (.seq Impl.AesGcmSiv.X86_64Reg.crypt Impl.AesGcmSiv.X86_64Reg.polyval))
      (.seq mask (.block (([.mov .rax (.mem (at_ .r15 okO))] : List Instr) ++ restore)))) s fun s' =>
      gprPreserved s s' ∧ openX86_64.post s s' := by
  obtain ⟨⟨Ar, Tb⟩, hTr⟩ := args_of_open h
  exact WP.mono (open_shape (open_wpG F (θ := 2 ^ 64) (fun L _ hR _ E _ _ _ _ _ S hA hD hDw hAD => decS_ok F L hR E S hA hD hDw hAD)
    mask_ok Ar Tb hTr rfl (ofNat_toNat64 _).symm rfl rfl rfl (ofNat_toNat64 _).symm rfl rfl (ofNat_toNat64 _).symm rfl))
    fun _ h => ⟨h.1, h.2.1⟩

/-- `vg_aes_gcm_siv_open` with the loops. -/
theorem openL_wp (F : MulFacts) {lp : Impl.AesGcmSiv.X86_64Stitch.Loops}
    (hlp : Proof.AesGcmSiv.X86_64.Stitch.LoopsOk lp) {s : State} (h : openPre s) :
    WP isa (Impl.AesGcmSiv.X86_64Reg.openL lp) s fun s' => gprPreserved s s' ∧ openX86_64.post s s' ∧
      Frame (fineR 256 (arg s 2) (s.gpr .r9) (arg s 0).toNat) s.mem s'.mem := by
  obtain ⟨⟨Ar, Tb⟩, hTr⟩ := args_of_open h
  exact openL_wp' F hlp Ar Tb hTr rfl (ofNat_toNat64 _).symm rfl rfl rfl (ofNat_toNat64 _).symm rfl rfl
    (ofNat_toNat64 _).symm rfl

/-- `vg_aes_gcm_siv_open`. -/
theorem open_wp (F : MulFacts) {s : State} (h : openPre s) :
    WP isa Impl.AesGcmSiv.X86_64Reg.open s fun s' => gprPreserved s s' ∧ openX86_64.post s s' ∧
      Frame (fineR (2 ^ 64) (arg s 2) (s.gpr .r9) (arg s 0).toNat) s.mem s'.mem := by
  obtain ⟨⟨Ar, Tb⟩, hTr⟩ := args_of_open h
  exact open_wp' F Ar Tb hTr rfl (ofNat_toNat64 _).symm rfl rfl rfl (ofNat_toNat64 _).symm rfl rfl
    (ofNat_toNat64 _).symm rfl

end VG.Proof.AesGcmSivReg.X86_64
