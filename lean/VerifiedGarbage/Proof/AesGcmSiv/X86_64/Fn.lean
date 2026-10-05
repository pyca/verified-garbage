import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Crypt
import VerifiedGarbage.Proof.AesGcm.X86_64.Mask

/-!
# AES-GCM-SIV on x86-64: comparing the tags, and `vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open`

Untrusted: everything here is checked by Lean. `cmp` stores at `W + 192`
whether the received tag at `W` equals the computed one at `W + 128`,
without a branch (`cmp_ok`); `mask` ANDs every byte of the data with
`0 − ok`, leaving it if the tags are equal and zeroing it if not
(`mask_ok`). `recv` copies the received tag to `W` (`recv_ok`), and
`tagOut` the computed one from `W` to `tag` (`tagOut_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG.Proof.Aes.X86_64 (BlocksImpl)

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_snoc)
open VG.Proof.AesGcm.X86_64 (toNat_ofNat_of_lt in_off)

/-- `ok` from the XOR of the tags' words: 1 if both are equal, 0 if not. -/
theorem ok_val (a b c d : BitVec 64) :
    BitVec.setWidth 64 (BitVec.setWidth 32 0#64 + BitVec.setWidth 32
      (BitVec.ofBool (decide ((a ^^^ b ||| c ^^^ d).toNat < (1#64).toNat)))) =
      if a = b ∧ c = d then 1#64 else 0#64 := by
  by_cases h : a = b ∧ c = d
  · obtain ⟨rfl, rfl⟩ := h; simp
  · rw [ite_eq_right_iff.mpr (fun h' => absurd h' h)]
    have : decide ((a ^^^ b ||| c ^^^ d).toNat < (1#64).toNat) = false := decide_eq_false fun hl => h (by
      have e : (a ^^^ b ||| c ^^^ d) = 0#64 := BitVec.eq_of_toNat_eq (by
        rw [BitVec.toNat_ofNat]; rw [BitVec.toNat_ofNat] at hl; omega)
      rw [BitVec.or_eq_zero_iff] at e
      exact ⟨BitVec.xor_eq_zero_iff.mp e.1, BitVec.xor_eq_zero_iff.mp e.2⟩)
    rw [this]
    decide

theorem le8_inj {a b : BitVec 64} (h : Proof.Cmac.le8 a = Proof.Cmac.le8 b) : a = b :=
  BitVec.eq_of_toNat_eq (by rw [← GcmSiv.leNat_le8, h, GcmSiv.leNat_le8])

/-- Two blocks in memory are equal when their words are. -/
theorem bytes16_eq (m : Mem) (p q : Addr) :
    bytesAt m p 16 = bytesAt m q 16 ↔
      m.readW p 64 = m.readW q 64 ∧ m.readW (p + BitVec.ofNat 64 8) 64 = m.readW (q + BitVec.ofNat 64 8) 64 := by
  rw [Proof.Cmac.bytesAt_split m p, Proof.Cmac.bytesAt_split m q, ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW,
    ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW]
  constructor
  · intro h
    obtain ⟨h₁, h₂⟩ := List.append_inj h (by rw [Proof.Cmac.length_le8, Proof.Cmac.length_le8])
    exact ⟨le8_inj h₁, le8_inj h₂⟩
  · rintro ⟨h₁, h₂⟩; rw [h₁, h₂]

theorem cmp_ok {K W SP : Addr} {t : State} (E : Env K W SP t) :
    ∃ t' : State, runBlock isa cmp t = some t' ∧
      t'.mem = t.mem.writeW (W + BitVec.ofNat 64 192)
        (if bytesAt t.mem W 16 = bytesAt t.mem (W + BitVec.ofNat 64 128) 16 then 1#64 else 0#64) ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have h15 := E.r15
  have r₀ : InRegions (t.rd ++ t.wr) W 8 := by simpa using E.perm.wR (show 0 + 8 ≤ 3816 by decide)
  have r₈ := E.perm.wR (show 8 + 8 ≤ 3816 by decide)
  have u₀ := E.perm.wR (show 128 + 8 ≤ 3816 by decide)
  have u₈ := E.perm.wR (show 136 + 8 ≤ 3816 by decide)
  have wo := E.perm.wW (show 192 + 8 ≤ 3816 by decide)
  refine ⟨_, by srun [Impl.AesGcmSiv.X86_64.cmp, h15, r₀, r₈, u₀, u₈, wo], ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, mem_setFlags, gpr_setReg, gpr_arithFlags, cf_arithFlags, cf_setReg,
      ite_true, ite_false, reduceCtorEq]
    have hb := bytes16_eq t.mem W (W + BitVec.ofNat 64 128)
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
  have rD := E.perm.wR (show 232 + 8 ≤ 3816 by decide)
  have rL := E.perm.wR (show 240 + 8 ≤ 3816 by decide)
  have rO := E.perm.wR (show 192 + 8 ≤ 3816 by decide)
  have sD := S.data
  have sL := S.len
  have hok' : t.mem.readW (W + BitVec.ofNat 64 192) 64 = if decide c then 1 else 0 := by
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
        Proof.AesGcm.X86_64.ofNat_shr4 hn, Proof.AesGcm.X86_64.and_self_beq (show n / 16 < 2 ^ 64 by omega)]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have E₁ : Env K W SP t₁ := E.keep hg₁ hrd₁ hwr₁
  refine WP.mono (Proof.AesGcm.X86_64.maskTail_wp hn (by rw [hrd₁, hwr₁]; exact hD.rd) (by rw [hwr₁]; exact hDw)
    h12₁ h11₁ hbp₁ h10₁ rcx₁ hzf₁) fun t₂ M => ?_
  have hl : (Proof.AesGcm.X86_64.masked t₁.mem D (decide c) n).length = n :=
    Proof.AesGcm.X86_64.length_masked _ _ _ _
  refine ⟨E₁.keep (fun r hr => M.keep r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
    M.rd M.wr, M.rd.trans hrd₁, M.wr.trans hwr₁, by rw [M.mem, ← hm₁]; exact Proof.AesGcm.X86_64.writeBytes_frame' _ hl,
    ?_⟩
  have e := Proof.AesGcm.X86_64.bytesAt_writeBytes_self t₁.mem D (Proof.AesGcm.X86_64.masked t₁.mem D (decide c) n)
    (by omega)
  rw [hl] at e
  rw [M.mem, e, hm₁]
  by_cases hc : c <;> simp [Proof.AesGcm.X86_64.masked, hc, Spec.GcmSiv.zeros]

/-! ## The tag's copies -/

/-- A 16-byte block copied from `S` to `T`, by words. -/
theorem bytesAt_copy2 (m : Mem) (S T : Addr) (hs : Mem.Sep (S + BitVec.ofNat 64 8) (64 / 8) T (64 / 8)) :
    bytesAt ((m.writeW T (m.readW S 64)).writeW (T + BitVec.ofNat 64 8)
      ((m.writeW T (m.readW S 64)).readW (S + BitVec.ofNat 64 8) 64)) T 16 = bytesAt m S 16 := by
  rw [Mem.readW_writeW_sep hs (by decide), Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_readW, Proof.Cmac.le8_readW,
    ← Proof.Cmac.bytesAt_split]

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
  have t₀ : InRegions (s.rd ++ s.wr) T 8 := by simpa using in_off (d := 0) (n := 8) hB.rd (by decide) (by decide)
  have t₈ := in_off (d := 8) (n := 8) hB.rd (by decide) (by decide)
  have w₀ : InRegions s.wr W 8 := by simpa using E.perm.wW (show 0 + 8 ≤ 3816 by decide)
  have w₈ := E.perm.wW (show 8 + 8 ≤ 3816 by decide)
  have hs : Mem.Sep (T + BitVec.ofNat 64 8) (64 / 8) W (64 / 8) :=
    hB.w.sep (Offset.contains_base T (d := 8) (n := 8) (k := 16) (by decide) (by decide))
      (by simpa using Offset.contains_base W (d := 0) (n := 8) (k := 3816) (by decide) (by decide))
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
    (hTw : Covers [⟨T, 16⟩] s.wr) (hTW : (⟨T, 16⟩ : Region).Disjoint ⟨W, 3816⟩) :
    ∃ s', runBlock isa tagOut s = some s' ∧ Frame [⟨T, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem T 16 = bytesAt s.mem W 16 ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have h15 := E.r15
  have hsp := E.rsp
  have t₀ : InRegions s.wr T 8 := by simpa using in_off (d := 0) (n := 8) hTw (by decide) (by decide)
  have t₈ := in_off (d := 8) (n := 8) hTw (by decide) (by decide)
  have w₀ : InRegions (s.rd ++ s.wr) W 8 := by simpa using E.perm.wR (show 0 + 8 ≤ 3816 by decide)
  have w₈ := E.perm.wR (show 8 + 8 ≤ 3816 by decide)
  have hs : Mem.Sep (W + BitVec.ofNat 64 8) (64 / 8) T (64 / 8) :=
    hTW.symm.sep (Offset.contains_base W (d := 8) (n := 8) (k := 3816) (by decide) (by decide))
      (by simpa using Offset.contains_base T (d := 0) (n := 8) (k := 16) (by decide) (by decide))
  refine ⟨_, by srun [tagOut, h15, hsp, hT, hTa, t₀, t₈, w₀, w₈], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg]; exact Proof.Cmac.frame_store2 _ _ _
  · simp only [mem_setReg]; exact bytesAt_copy2 _ _ _ hs
  · intro r hr; simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]
  all_goals rfl

end VG.Proof.AesGcmSiv.X86_64

/-!
## The keys, and what the pieces write

Untrusted: everything here is checked by Lean. `keys` derives the message
keys, expands the encryption key and sets up GHASH's key and accumulator
(`keys_ok`). Every piece but counter mode and the mask writes only parts of
`W` and the stack below `SP` (`mutW`), which miss the buffers, the key
schedule and what the entry keeps in `W`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl)

/-- What the pieces before counter mode write. -/
abbrev mutW (W SP : Addr) : List Region := [wA W, wO W, wC W, below SP 8]

theorem mutW_mut (W SP D : Addr) (n : Nat) : ∀ r ∈ mutW W SP, ∃ r' ∈ mutR W SP D n, Region.Sub r r' :=
  fun r hr => ⟨r, by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp, fun _ h => h⟩

/-- `⟨W + d, k⟩` within `[0, 144)` of `W`. -/
theorem sub_wA {W SP : Addr} {d k : Nat} (h : d + k ≤ 144) :
    ∃ r' ∈ mutW W SP, Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r' :=
  ⟨wA W, by simp, Offset.sub_base W h⟩

/-- `⟨W + d, k⟩` within `[248, 3816)` of `W`. -/
theorem sub_wC {W SP : Addr} {d k : Nat} (h₁ : 248 ≤ d) (h₂ : d + k ≤ 3816) :
    ∃ r' ∈ mutW W SP, Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r' :=
  ⟨wC W, by simp, Offset.sub W h₁ (by omega)⟩

theorem sub_stk {W SP : Addr} : ∃ r' ∈ mutW W SP, Region.Sub (below SP 8) r' := ⟨_, by simp, fun _ h => h⟩

theorem buf_mutW {K W SP : Addr} {s : State} {P : Addr} {len : Nat} (hP : Buf K W SP s P len) {m m' : Mem}
    (hf : Frame (mutW W SP) m m') : bytesAt m' P len = bytesAt m P len :=
  Proof.AesGcm.X86_64.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hP.w.sub_right (Region.sub_prefix (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.stk.symm) (by have := hP.lt; omega)

theorem mutW_frame {K W SP : Addr} (L : Lay K W SP) {d k : Nat}
    (hd : 144 ≤ d ∧ d + k ≤ 192 ∨ 200 ≤ d ∧ d + k ≤ 248) :
    ∀ r ∈ mutW W SP, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · simpa using L.w_w (a := d) (n := k) (d := 0) (k := 144) (.inr (by omega)) (by omega) (by decide)
  · rcases hd with hd | hd
    · exact L.w_w (.inl (by omega)) (by omega) (by decide)
    · exact L.w_w (.inr (by omega)) (by omega) (by decide)
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.stk_w' (by omega)).symm

/-- What `keys` writes: the keys, GHASH's key and accumulator, the blocks
the calls use, the encryption key's schedule and the working spaces. -/
abbrev keyR (W SP : Addr) : List Region := [⟨W + BitVec.ofNat 64 16, 128⟩, wC W, below SP 8]

theorem keyR_mutW (W SP : Addr) : ∀ r ∈ keyR W SP, ∃ r' ∈ mutW W SP, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact sub_wA (by decide)
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact sub_stk

/-- What `keys` leaves, from `σ`. -/
structure KeysPost (K W SP : Addr) (R : Nat) (N : Addr) (σ t : State) : Prop where
  env : Env K W SP t
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr
  frame : Frame (keyR W SP) σ.mem t.mem
  auth : (Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt σ.mem N 12)).1 =
    bytesAt t.mem (W + BitVec.ofNat 64 16) 16
  ciph : Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R = Spec.GcmSiv.aes
    (Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt σ.mem N 12)).2
  hkey : Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 64) =
    GcmSiv.Polyval.mulXG (Spec.GcmSiv.ofBytes (bytesAt t.mem (W + BitVec.ofNat 64 16) 16))
  acc : Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 80) = 0

theorem keys_ok (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14)
    {N A D : Addr} {al n : Nat} {σ : State} (E : Env K W SP σ) (S : Slots W R N A D al n σ.mem)
    (hN : Buf K W SP σ N 12) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) :
    WP isa (keys v.callees) σ (KeysPost K W SP R N σ) := by
  refine WP.seq (WP.mono (derive_ok v L hR E S hN hDW) fun t₂ I => ?_)
  have f₂ : Frame (keyR W SP) σ.mem t₂.mem := I.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨W + BitVec.ofNat 64 16, 128⟩, by simp, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨⟨W + BitVec.ofNat 64 16, 128⟩, by simp, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨wC W, by simp, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  have S₂ := slots_mut L hDW ((f₂.sub (keyR_mutW W SP)).sub (mutW_mut W SP D n)) S
  refine WP.seq (WP.mono (expand_ok v L hR I.env S₂) fun t₃ X => ?_)
  obtain ⟨t₄, run₄, hG, hY, f₄, hg₄, hrd₄, hwr₄⟩ := hkey_ok X.env
  refine WP.of_runBlock ⟨t₄, run₄, ?_⟩
  have fX := X.frame
  have f₃ : Frame (keyR W SP) t₂.mem t₃.mem := fX.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨wC W, by simp, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨wC W, by simp, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  have dA : ∀ q ∈ [(⟨W + BitVec.ofNat 64 248, 240⟩ : Region), ⟨W + BitVec.ofNat 64 1768, 512⟩, below SP 8],
      (⟨W + BitVec.ofNat 64 16, 16⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm
  have d64 : ∀ q ∈ [(⟨W + BitVec.ofNat 64 64, 32⟩ : Region)], (⟨W + BitVec.ofNat 64 16, 16⟩ : Region).Disjoint q :=
    fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inl (by decide)) (by decide) (by decide)
  have hA₄ : bytesAt t₄.mem (W + BitVec.ofNat 64 16) 16 = bytesAt t₂.mem (W + BitVec.ofNat 64 16) 16 := by
    rw [Proof.AesGcm.X86_64.bytesAt_frame f₄ d64 (by decide), Proof.AesGcm.X86_64.bytesAt_frame fX dA (by decide)]
  have hK := I.keys hR
  refine ⟨X.env.keep (fun r hr => ?_) hrd₄ hwr₄, by rw [hrd₄, X.rd, I.rd], by rw [hwr₄, X.wr, I.wr],
    (f₂.trans f₃).trans (f₄.sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ⟨⟨W + BitVec.ofNat 64 16, 128⟩, by simp, Offset.sub W (by decide) (by decide)⟩),
    ?_, ?_,
    by rw [hG, hA₄, ← Proof.AesGcm.X86_64.bytesAt_frame fX dA (by decide)], hY⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₄ _ (by simp)
  · rw [hK, hA₄]
  · rw [ctxCiph_frame f₄ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide))
      (by rcases hR with h | h <;> subst h <;> decide), X.ciph, hK]

end VG.Proof.AesGcmSiv.X86_64

/-!
## `vg_aes_gcm_siv_seal` (correctness)

Untrusted: everything here is checked by Lean. The entry, the keys, POLYVAL
and the tag input, the tag at `W`, counter mode on the data from it, the
copy of the tag to `tag` and the restore compute `encryptWith` (RFC 8452
§4) of the arguments (`seal_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl)

/-- The return address misses everything the code writes. -/
theorem ret_disj {K W SP D : Addr} {n : Nat} (L : Lay K W SP) (hW : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 3816⟩)
    (hD : (⟨SP, 8⟩ : Region).Disjoint ⟨D, n⟩) : ∀ r ∈ entryR W :: mutR W SP D n, (⟨SP, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact hW.sub_right (Region.sub_prefix (by decide))
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact Offset.base_disjoint_below SP (by have := L.sp; omega)
  · exact hD

theorem cryR_mut (W SP D : Addr) (n : Nat) : ∀ r ∈ cryR W SP D n, ∃ r' ∈ mutR W SP D n, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨wA W, by simp, Offset.sub_base W (by decide)⟩
  · exact ⟨wC W, by simp, Offset.sub W (by decide) (by decide)⟩
  · exact ⟨wC W, by simp, Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

theorem polyR_mutW (W SP : Addr) : ∀ r ∈ polyR W SP, ∃ r' ∈ mutW W SP, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact sub_wA (by decide)
  · exact sub_wA (by decide)
  · exact sub_wA (by decide)
  · exact sub_wC (by decide) (by decide)
  · exact sub_wC (by decide) (by decide)
  · exact sub_stk

theorem tagR_mutW (W SP : Addr) {o : Nat} (ho : o + 16 ≤ 144) : ∀ r ∈ tagR W SP o, ∃ r' ∈ mutW W SP, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact sub_wA (by decide)
  · exact sub_wA ho
  · exact sub_wC (by decide) (by decide)
  · exact sub_stk

theorem key_polyR {K W SP : Addr} (L : Lay K W SP) :
    ∀ r ∈ polyR W SP, (⟨W + BitVec.ofNat 64 248, 240⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w' (by decide)).symm

theorem key_tagR {K W SP : Addr} (L : Lay K W SP) {o : Nat} (ho : o + 16 ≤ 248) :
    ∀ r ∈ tagR W SP o, (⟨W + BitVec.ofNat 64 248, 240⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inr ho) (by decide) (by omega)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w' (by decide)).symm

/-- `vg_aes_gcm_siv_seal`, for its arguments. -/
theorem seal_wp' (v : GcmImpl) (eb : Proof.Aes.X86_64.BlocksImpl) (hpv : GcmSiv.Polyval.PolyvalEq) {s : State} {K W SP N A D T : Addr} {R al n : Nat}
    (Ar : Args s K W SP N A D R al n) (Tb : TagBuf W SP D n T) (hTw : Covers [⟨T, 16⟩] s.wr)
    (hrT : (⟨SP, 8⟩ : Region).Disjoint ⟨T, 16⟩) (hsp : s.gpr .rsp = SP)
    (hn : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = A) (hr8 : s.gpr .r8 = BitVec.ofNat 64 al) (hr9 : s.gpr .r9 = D) :
    WP isa («seal» v.callees ⟨eb.enc.name, eb.enc.code⟩) s fun s' => gprPreserved s s' ∧
      Spec.GcmSiv.encryptWith (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt s.mem N 12)
        (bytesAt s.mem D n) (bytesAt s.mem A al) = (bytesAt s'.mem D n, bytesAt s'.mem T 16) := by
  have L := Ar.lay
  have hRb : 16 * (R + 1) ≤ 240 := by rcases Ar.rounds with h | h <;> subst h <;> decide
  obtain ⟨s₁, run₁, E₁, S₁, sv₁, f₁, rd₁, wr₁⟩ := entry_ok Ar.perm hsp Ar.args hn hW hdi hsi hdx hcx hr8 hr9
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hent : ∀ {P : Addr} {len : Nat}, Buf K W SP s P len → bytesAt s₁.mem P len = bytesAt s.mem P len :=
    fun hP => Proof.AesGcm.X86_64.bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by have := hP.lt; omega)
  have hK₁ : Spec.GcmSiv.ctxCiph s₁.mem K R = Spec.GcmSiv.ctxCiph s.mem K R :=
    ctxCiph_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_right (Lay.wSub (by decide))) hRb
  have bN₁ := Ar.nonce.of_eq rd₁ wr₁
  have bA₁ := Ar.aad.of_eq rd₁ wr₁
  have bD₁ := Ar.data.of_eq rd₁ wr₁
  -- The keys.
  refine WP.seq (WP.mono (keys_ok v L Ar.rounds E₁ S₁ bN₁ Ar.data.w) fun s₂ Ky => ?_)
  have fK : Frame (mutW W SP) s₁.mem s₂.mem := Ky.frame.sub (keyR_mutW W SP)
  have S₂ := slots_mut L Ar.data.w (fK.sub (mutW_mut W SP D n)) S₁
  -- POLYVAL and the tag input.
  refine WP.seq (WP.mono (polyval_ok v L Ky.env S₂ (bA₁.of_eq Ky.rd Ky.wr) (bD₁.of_eq Ky.rd Ky.wr)
    (bN₁.of_eq Ky.rd Ky.wr) Ky.hkey Ky.acc) fun s₃ Po => ?_)
  have f₃ : Frame (mutW W SP) s₂.mem s₃.mem := Po.frame.sub (polyR_mutW W SP)
  have S₃ := slots_mut L Ar.data.w (f₃.sub (mutW_mut W SP D n)) S₂
  -- The tag.
  refine WP.seq (WP.mono (tag_ok v L Ar.rounds Po.env S₃ (o := 0) (by decide)) fun s₄ Tg => ?_)
  have f₄ : Frame (mutW W SP) s₃.mem s₄.mem := Tg.frame.sub (tagR_mutW W SP (by decide))
  have S₄ := slots_mut L Ar.data.w (f₄.sub (mutW_mut W SP D n)) S₃
  have f₁₄ : Frame (mutW W SP) s₁.mem s₄.mem := (fK.trans f₃).trans f₄
  -- Counter mode.
  have bD₄ : Buf K W SP s₄ D n := bD₁.of_eq (by rw [Tg.rd, Po.rd, Ky.rd]) (by rw [Tg.wr, Po.wr, Ky.wr])
  refine WP.seq (WP.mono (crypt_ok v eb L Ar.rounds Tg.env S₄ bD₄
    (by rw [Tg.wr, Po.wr, Ky.wr, wr₁]; exact Ar.dw)) fun s₅ Cr => ?_)
  have f₁₅ : Frame (mutR W SP D n) s₁.mem s₅.mem := (f₁₄.sub (mutW_mut W SP D n)).trans (Cr.frame.sub (cryR_mut W SP D n))
  have fall : Frame (entryR W :: mutR W SP D n) s.mem s₅.mem :=
    (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩).trans
    (f₁₅.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)
  have r₅ : s₅.rd = s.rd := by rw [Cr.rd, Tg.rd, Po.rd, Ky.rd, rd₁]
  have w₅ : s₅.wr = s.wr := by rw [Cr.wr, Tg.wr, Po.wr, Ky.wr, wr₁]
  -- The copy of the tag, and `restore`.
  have hTa : InRegions (s₅.rd ++ s₅.wr) (SP + BitVec.ofNat 64 16) 8 := by
    have h := Proof.AesGcm.X86_64.in_off (d := 8) (n := 8) Ar.args (by decide) (by decide)
    rw [add_ofNat_assoc] at h
    rw [r₅, w₅]; exact h
  obtain ⟨s₆, run₆, fT, hT₆, hg₆, rd₆, wr₆⟩ := tagOut_ok Cr.env (by rw [argT_kept fall Ar.argsW Ar.argsD, hT]) hTa
    (by rw [w₅]; exact hTw) Tb.w
  have E₆ : Env K W SP s₆ := Cr.env.of_saved hg₆ rd₆ wr₆
  have dT : ∀ q ∈ [(⟨T, 16⟩ : Region)], ∀ p ∈ saved, (⟨W + BitVec.ofNat 64 p.2, 8⟩ : Region).Disjoint q := by
    intro q hq p hp
    simp only [List.mem_singleton] at hq; subst hq
    have hd : 144 ≤ p.2 ∧ p.2 + 8 ≤ 192 := by
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (Tb.w.sub_right (Lay.wSub (by omega))).symm
  have sv₆ : Saved s₆.mem W s.gpr := fun p hp => by
    rw [← saved_mut L Ar.data.w f₁₅ sv₁ p hp]
    exact fT.readW (r := ⟨W + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _)
      (fun q hq => dT q hq p hp) (by decide)
  obtain ⟨s₇, run₇, hg₇, hm₇, hsp₇, _⟩ := restore_ok E₆ sv₆
  refine WP.of_runBlock ⟨s₇, by rw [runBlock_append, run₆]; exact run₇, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg₇ (.rbx, 144) (by decide)
    · exact hg₇ (.rbp, 152) (by decide)
    · rw [hsp₇, E₆.rsp, hsp]
    · exact hg₇ (.r12, 160) (by decide)
    · exact hg₇ (.r13, 168) (by decide)
    · exact hg₇ (.r14, 176) (by decide)
    · exact hg₇ (.r15, 184) (by decide)
  · rw [hm₇, hsp, fT.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact hrT) (by decide)]
    exact fall.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (ret_disj L Ar.retW Ar.retD) (by decide)
  · have key₃ : Spec.GcmSiv.ctxCiph s₃.mem (W + BitVec.ofNat 64 248) R =
        Spec.GcmSiv.ctxCiph s₂.mem (W + BitVec.ofNat 64 248) R := ctxCiph_frame Po.frame (key_polyR L) hRb
    have key₄ : Spec.GcmSiv.ctxCiph s₄.mem (W + BitVec.ofNat 64 248) R =
        Spec.GcmSiv.ctxCiph s₃.mem (W + BitVec.ofNat 64 248) R := ctxCiph_frame Tg.frame (key_tagR L (by decide)) hRb
    have n₂ : bytesAt s₂.mem N 12 = bytesAt s.mem N 12 := by rw [buf_mutW bN₁ fK, hent Ar.nonce]
    have a₂ : bytesAt s₂.mem A al = bytesAt s.mem A al := by rw [buf_mutW bA₁ fK, hent Ar.aad]
    have d₂ : bytesAt s₂.mem D n = bytesAt s.mem D n := by rw [buf_mutW bD₁ fK, hent Ar.data]
    have d₄ : bytesAt s₄.mem D n = bytesAt s.mem D n := by rw [buf_mutW bD₁ f₁₄, hent Ar.data]
    have t₅ : bytesAt s₅.mem W 16 = bytesAt s₄.mem W 16 := Proof.AesGcm.X86_64.bytesAt_frame Cr.frame (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl
      · simpa using L.w_w (a := 0) (n := 16) (d := 96) (k := 48) (.inl (by decide)) (by decide) (by decide)
      · simpa using L.w_w (a := 0) (n := 16) (d := 488) (k := 1024) (.inl (by decide)) (by decide) (by decide)
      · simpa using L.w_w (a := 0) (n := 16) (d := 1768) (k := 2048) (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w.sub_right (Region.sub_prefix (by decide))).symm
      · exact (Ar.data.w.sub_right (Region.sub_prefix (by decide))).symm) (by decide)
    have d₇ : bytesAt s₇.mem D n = bytesAt s₅.mem D n := by
      rw [hm₇]; exact Proof.AesGcm.X86_64.bytesAt_frame fT (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact Tb.d.symm) (by have := Ar.data.lt; omega)
    have tg := Tg.out
    rw [BitVec.add_zero] at tg
    have au := Ky.auth
    have ci := Ky.ciph
    rw [hK₁, hent Ar.nonce] at au ci
    have po := Po.out hpv
    rw [n₂, a₂, d₂] at po
    rw [d₇, hm₇, hT₆, Cr.data, t₅, d₄, key₄, key₃, ci, tg, key₃, ci, po, ← au]
    unfold Spec.GcmSiv.encryptWith
    generalize Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt s.mem N 12) = dk
    obtain ⟨a, e⟩ := dk
    rfl

/-- `vg_aes_gcm_siv_seal`. -/
theorem seal_wp (v : GcmImpl) (eb : Proof.Aes.X86_64.BlocksImpl) (hpv : GcmSiv.Polyval.PolyvalEq) {s : State} (h : sealPre s) :
    WP isa («seal» v.callees ⟨eb.enc.name, eb.enc.code⟩) s fun s' => gprPreserved s s' ∧ sealX86_64.post s s' := by
  obtain ⟨⟨Ar, Tb⟩, hTw, hrT⟩ := args_of_seal h
  exact seal_wp' v eb hpv Ar Tb hTw hrT rfl (ofNat_toNat64 _).symm rfl rfl rfl (ofNat_toNat64 _).symm rfl rfl
    (ofNat_toNat64 _).symm rfl

end VG.Proof.AesGcmSiv.X86_64

/-!
## `vg_aes_gcm_siv_open` (correctness)

Untrusted: everything here is checked by Lean. The entry, the copy of the
received tag to `W`, the keys, counter mode on the data from it, POLYVAL of
the result and the tag input, its tag at `W + 128`, the comparison, the mask
and the restore compute `decryptWith` (RFC 8452 §5) of the arguments
(`open_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl)

theorem w0_keyR {K W SP : Addr} (L : Lay K W SP) : ∀ r ∈ keyR W SP, (⟨W, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · simpa using L.w_w (a := 0) (n := 16) (d := 16) (k := 128) (.inl (by decide)) (by decide) (by decide)
  · simpa using L.w_w (a := 0) (n := 16) (d := 248) (k := 3568) (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w.sub_right (Region.sub_prefix (by decide))).symm

theorem w0_cryR {K W SP D : Addr} {n : Nat} (L : Lay K W SP) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) :
    ∀ r ∈ cryR W SP D n, (⟨W, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using L.w_w (a := 0) (n := 16) (d := 96) (k := 48) (.inl (by decide)) (by decide) (by decide)
  · simpa using L.w_w (a := 0) (n := 16) (d := 488) (k := 1024) (.inl (by decide)) (by decide) (by decide)
  · simpa using L.w_w (a := 0) (n := 16) (d := 1768) (k := 2048) (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w.sub_right (Region.sub_prefix (by decide))).symm
  · exact (hD.sub_right (Region.sub_prefix (by decide))).symm

theorem w0_polyR {K W SP : Addr} (L : Lay K W SP) : ∀ r ∈ polyR W SP, (⟨W, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using L.w_w (a := 0) (n := 16) (d := 96) (k := 16) (.inl (by decide)) (by decide) (by decide)
  · simpa using L.w_w (a := 0) (n := 16) (d := 80) (k := 16) (.inl (by decide)) (by decide) (by decide)
  · simpa using L.w_w (a := 0) (n := 16) (d := 128) (k := 16) (.inl (by decide)) (by decide) (by decide)
  · simpa using L.w_w (a := 0) (n := 16) (d := 488) (k := 1024) (.inl (by decide)) (by decide) (by decide)
  · simpa using L.w_w (a := 0) (n := 16) (d := 1512) (k := 256) (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w.sub_right (Region.sub_prefix (by decide))).symm

theorem w0_tagR {K W SP : Addr} (L : Lay K W SP) : ∀ r ∈ tagR W SP 128, (⟨W, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · simpa using L.w_w (a := 0) (n := 16) (d := 112) (k := 16) (.inl (by decide)) (by decide) (by decide)
  · simpa using L.w_w (a := 0) (n := 16) (d := 128) (k := 16) (.inl (by decide)) (by decide) (by decide)
  · simpa using L.w_w (a := 0) (n := 16) (d := 1768) (k := 2048) (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w.sub_right (Region.sub_prefix (by decide))).symm

/-- `vg_aes_gcm_siv_open`, for its arguments. -/
theorem open_wp' (v : GcmImpl) (eb : Proof.Aes.X86_64.BlocksImpl) (hpv : GcmSiv.Polyval.PolyvalEq) {s : State} {K W SP N A D T : Addr} {R al n : Nat}
    (Ar : Args s K W SP N A D R al n) (Tb : TagBuf W SP D n T) (hTr : Covers [⟨T, 16⟩] (s.rd ++ s.wr))
    (hsp : s.gpr .rsp = SP)
    (hn : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = A) (hr8 : s.gpr .r8 = BitVec.ofNat 64 al) (hr9 : s.gpr .r9 = D) :
    WP isa («open» v.callees ⟨eb.enc.name, eb.enc.code⟩) s fun s' => gprPreserved s s' ∧
      openPost (Spec.GcmSiv.decryptWith (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt s.mem N 12)
        (bytesAt s.mem D n) (bytesAt s.mem A al) (bytesAt s.mem T 16)) s' D n := by
  have L := Ar.lay
  have hRb : 16 * (R + 1) ≤ 240 := by rcases Ar.rounds with h | h <;> subst h <;> decide
  obtain ⟨s₀, run₀, E₀, S₀, sv₀, f₀, rd₀, wr₀⟩ := entry_ok Ar.perm hsp Ar.args hn hW hdi hsi hdx hcx hr8 hr9
  refine WP.seq (WP.of_runBlock ⟨s₀, run₀, ?_⟩)
  have f₀' : Frame (entryR W :: mutR W SP D n) s.mem s₀.mem :=
    f₀.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  -- The received tag, copied to `W`.
  have hTa : InRegions (s₀.rd ++ s₀.wr) (SP + BitVec.ofNat 64 16) 8 := by
    have h := Proof.AesGcm.X86_64.in_off (d := 8) (n := 8) Ar.args (by decide) (by decide)
    rw [add_ofNat_assoc] at h
    rw [rd₀, wr₀]; exact h
  obtain ⟨s₁, run₁, fR, hR₁, hgR, rdR, wrR⟩ := recv_ok E₀ (by rw [argT_kept f₀' Ar.argsW Ar.argsD, hT]) hTa
    ((Tb.buf (s := s) hTr).of_eq rd₀ wr₀)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have E₁ : Env K W SP s₁ := E₀.of_saved hgR rdR wrR
  have fR' : Frame (mutR W SP D n) s₀.mem s₁.mem := fR.sub fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact ⟨wA W, by simp, Region.sub_prefix (by decide)⟩
  have S₁ := slots_mut L Ar.data.w fR' S₀
  have rd₁ : s₁.rd = s.rd := by rw [rdR, rd₀]
  have wr₁ : s₁.wr = s.wr := by rw [wrR, wr₀]
  have f₁ : Frame (entryR W :: mutR W SP D n) s.mem s₁.mem :=
    f₀'.trans (fR'.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)
  have f₀₁ : Frame [entryR W, ⟨W, 16⟩] s.mem s₁.mem :=
    (f₀.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩).trans
    (fR.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨⟨W, 16⟩, by simp, fun _ h => h⟩)
  have hent : ∀ {P : Addr} {len : Nat}, Buf K W SP s P len → bytesAt s₁.mem P len = bytesAt s.mem P len :=
    fun hP => Proof.AesGcm.X86_64.bytesAt_frame f₀₁ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hP.w.sub_right (Lay.wSub (by decide))
      · exact hP.w.sub_right (Region.sub_prefix (by decide)))
      (by have := hP.lt; omega)
  have hK₁ : Spec.GcmSiv.ctxCiph s₁.mem K R = Spec.GcmSiv.ctxCiph s.mem K R :=
    ctxCiph_frame f₀₁ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.k_w.sub_right (Lay.wSub (by decide))
      · exact L.k_w.sub_right (Region.sub_prefix (by decide))) hRb
  have hT₁ : bytesAt s₁.mem W 16 = bytesAt s.mem T 16 := by
    rw [hR₁]; exact tag_kept Tb f₀'
  have bN₁ := Ar.nonce.of_eq rd₁ wr₁
  have bA₁ := Ar.aad.of_eq rd₁ wr₁
  have bD₁ := Ar.data.of_eq rd₁ wr₁
  -- The keys.
  refine WP.seq (WP.mono (keys_ok v L Ar.rounds E₁ S₁ bN₁ Ar.data.w) fun s₂ Ky => ?_)
  have fK : Frame (mutW W SP) s₁.mem s₂.mem := Ky.frame.sub (keyR_mutW W SP)
  have S₂ := slots_mut L Ar.data.w (fK.sub (mutW_mut W SP D n)) S₁
  -- Counter mode from the received tag.
  refine WP.seq (WP.mono (crypt_ok v eb L Ar.rounds Ky.env S₂ (bD₁.of_eq Ky.rd Ky.wr)
    (by rw [Ky.wr, wr₁]; exact Ar.dw)) fun s₃ Cr => ?_)
  have S₃ := S₂.of_frame Cr.frame (slots_cryR L Ar.data)
  have dK : ∀ {d k : Nat}, 16 ≤ d → d + k ≤ 96 → ∀ q ∈ cryR W SP D n, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint q :=
    fun h₁ h₂ q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
      · exact L.w_w (.inl (by omega)) (by omega) (by decide)
      · exact (L.stk_w' (by omega)).symm
      · exact (Ar.data.w.sub_right (Lay.wSub (by omega))).symm
  have hA₃ : bytesAt s₃.mem (W + BitVec.ofNat 64 16) 16 = bytesAt s₂.mem (W + BitVec.ofNat 64 16) 16 :=
    Proof.AesGcm.X86_64.bytesAt_frame Cr.frame (dK (by decide) (by decide)) (by decide)
  have hG₃ : Spec.Gcm.blockAt s₃.mem (W + BitVec.ofNat 64 64) =
      GcmSiv.Polyval.mulXG (Spec.GcmSiv.ofBytes (bytesAt s₃.mem (W + BitVec.ofNat 64 16) 16)) := by
    rw [Proof.AesGcm.X86_64.blockAt_frame Cr.frame (dK (by decide) (by decide)), Ky.hkey, hA₃]
  have hY₃ : Spec.Gcm.blockAt s₃.mem (W + BitVec.ofNat 64 80) = 0 := by
    rw [Proof.AesGcm.X86_64.blockAt_frame Cr.frame (dK (by decide) (by decide)), Ky.acc]
  have nA : ∀ {P : Addr} {len : Nat}, Buf K W SP s P len → (⟨P, len⟩ : Region).Disjoint ⟨D, n⟩ →
      bytesAt s₃.mem P len = bytesAt s.mem P len := fun hP hPD => by
    rw [Proof.AesGcm.X86_64.bytesAt_frame Cr.frame (fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl
        · exact hP.w.sub_right (Lay.wSub (by decide))
        · exact hP.w.sub_right (Lay.wSub (by decide))
        · exact hP.w.sub_right (Lay.wSub (by decide))
        · exact hP.stk.symm
        · exact hPD) (by have := hP.lt; omega),
      buf_mutW (hP.of_eq rd₁ wr₁) fK, hent hP]
  -- POLYVAL of the plaintext and the tag input.
  have r₃ : s₃.rd = s₁.rd := by rw [Cr.rd, Ky.rd]
  have w₃ : s₃.wr = s₁.wr := by rw [Cr.wr, Ky.wr]
  refine WP.seq (WP.mono (polyval_ok v L Cr.env S₃ (bA₁.of_eq r₃ w₃) (bD₁.of_eq r₃ w₃) (bN₁.of_eq r₃ w₃) hG₃ hY₃)
    fun s₄ Po => ?_)
  have S₄ := slots_mut L Ar.data.w ((Po.frame.sub (polyR_mutW W SP)).sub (mutW_mut W SP D n)) S₃
  -- Its tag at `W + 128`.
  refine WP.seq (WP.mono (tag_ok v L Ar.rounds Po.env S₄ (o := 128) (by decide)) fun s₅ Tg => ?_)
  -- The comparison.
  obtain ⟨s₆, run₆, hm₆, hg₆, hrd₆, hwr₆⟩ := cmp_ok Tg.env
  refine WP.seq (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
  have E₆ : Env K W SP s₆ := Tg.env.of_saved hg₆ hrd₆ hwr₆
  have fO : Frame [wO W] s₅.mem s₆.mem := by
    rw [hm₆]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have S₅ := slots_mut L Ar.data.w ((Tg.frame.sub (tagR_mutW W SP (by decide))).sub (mutW_mut W SP D n)) S₄
  have S₆ := S₅.of_frame fO (fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide))
  have r₅ : s₅.rd = s₁.rd := by rw [Tg.rd, Po.rd, r₃]
  have w₅ : s₅.wr = s₁.wr := by rw [Tg.wr, Po.wr, w₃]
  have hok : s₆.mem.readW (W + BitVec.ofNat 64 192) 64 =
      if bytesAt s₅.mem (W + BitVec.ofNat 64 128) 16 = bytesAt s₅.mem W 16 then 1#64 else 0#64 := by
    rw [hm₆, Mem.readW_writeW_self64]
    by_cases hc : bytesAt s₅.mem W 16 = bytesAt s₅.mem (W + BitVec.ofNat 64 128) 16
    · simp only [hc, ↓reduceIte]
    · simp only [hc, Ne.symm hc, ↓reduceIte]
  -- The mask.
  refine WP.seq (WP.mono (mask_ok E₆ S₆ (bD₁.of_eq (by rw [hrd₆, r₅]) (by rw [hwr₆, w₅]))
    (by rw [hwr₆, w₅, wr₁]; exact Ar.dw) hok) fun s₇ Mk => ?_)
  -- `ok` and the restore.
  have h15₇ := Mk.env.r15
  have rO := Mk.env.perm.wR (show 192 + 8 ≤ 3816 by decide)
  obtain ⟨s₈, run₈, hax₈, hm₈, hg₈, hrd₈, hwr₈⟩ : ∃ s₈ : State, runBlock isa [.mov .rax (.mem (at_ .r15 okO))] s₇ =
      some s₈ ∧ s₈.gpr .rax = s₇.mem.readW (W + BitVec.ofNat 64 192) 64 ∧ s₈.mem = s₇.mem ∧
      (∀ r, r ≠ .rax → s₈.gpr r = s₇.gpr r) ∧ s₈.rd = s₇.rd ∧ s₈.wr = s₇.wr := by
    refine ⟨_, by srun [h15₇, rO], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true]
    · rfl
    · intro r h; simp only [gpr_setReg, h, ite_false]
    all_goals rfl
  have E₈ : Env K W SP s₈ := Mk.env.keep (fun r hr => hg₈ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)) hrd₈ hwr₈
  have fall : Frame (mutR W SP D n) s₁.mem s₇.mem :=
    ((((fK.sub (mutW_mut W SP D n)).trans (Cr.frame.sub (cryR_mut W SP D n))).trans
      ((Po.frame.sub (polyR_mutW W SP)).sub (mutW_mut W SP D n))).trans
      (((Tg.frame.sub (tagR_mutW W SP (by decide))).sub (mutW_mut W SP D n)).trans
        (fO.sub fun q hq => ⟨q, by simp only [List.mem_singleton] at hq; subst hq; simp, fun _ h => h⟩))).trans
      (Mk.frame.sub fun q hq => ⟨q, by simp only [List.mem_singleton] at hq; subst hq; simp, fun _ h => h⟩)
  obtain ⟨s₉, run₉, hg₉, hm₉, hsp₉, hax₉⟩ :=
    restore_ok E₈ (by rw [hm₈]; exact saved_mut L Ar.data.w (fR'.trans fall) sv₀)
  refine WP.of_runBlock ⟨s₉, by rw [runBlock_append, run₈]; exact run₉, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg₉ (.rbx, 144) (by decide)
    · exact hg₉ (.rbp, 152) (by decide)
    · rw [hsp₉, E₈.rsp, hsp]
    · exact hg₉ (.r12, 160) (by decide)
    · exact hg₉ (.r13, 168) (by decide)
    · exact hg₉ (.r14, 176) (by decide)
    · exact hg₉ (.r15, 184) (by decide)
  · have fall' : Frame (entryR W :: mutR W SP D n) s.mem s₇.mem :=
      f₁.trans (fall.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)
    rw [hm₉, hm₈, hsp]
    exact fall'.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (ret_disj L Ar.retW Ar.retD) (by decide)
  · have au := Ky.auth
    have ci := Ky.ciph
    rw [hK₁, hent Ar.nonce] at au ci
    have tag₂ : bytesAt s₂.mem W 16 = bytesAt s.mem T 16 := by
      rw [Proof.AesGcm.X86_64.bytesAt_frame Ky.frame (w0_keyR L) (by decide), hT₁]
    have tag₅ : bytesAt s₅.mem W 16 = bytesAt s.mem T 16 := by
      rw [Proof.AesGcm.X86_64.bytesAt_frame Tg.frame (w0_tagR L) (by decide),
        Proof.AesGcm.X86_64.bytesAt_frame Po.frame (w0_polyR L) (by decide),
        Proof.AesGcm.X86_64.bytesAt_frame Cr.frame (w0_cryR L Ar.data.w) (by decide), tag₂]
    have ct₂ : bytesAt s₂.mem D n = bytesAt s.mem D n := by rw [buf_mutW bD₁ fK, hent Ar.data]
    have ci₄ : Spec.GcmSiv.ctxCiph s₄.mem (W + BitVec.ofNat 64 248) R =
        Spec.GcmSiv.ctxCiph s₂.mem (W + BitVec.ofNat 64 248) R := by
      rw [ctxCiph_frame Po.frame (key_polyR L) hRb, ctxCiph_frame Cr.frame (key_cryR L Ar.data) hRb]
    have pt₃ := Cr.data
    rw [tag₂, ct₂, ci] at pt₃
    have po := Po.out hpv
    rw [hA₃, ← au, nA Ar.nonce Ar.nd, nA Ar.aad Ar.ad, pt₃] at po
    have tg := Tg.out
    rw [ci₄, ci, po] at tg
    have dD : ∀ q ∈ tagR W SP 128, (⟨D, n⟩ : Region).Disjoint q := fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.stk.symm
    have dP : ∀ q ∈ polyR W SP, (⟨D, n⟩ : Region).Disjoint q := fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.stk.symm
    have d₆ : bytesAt s₆.mem D n = bytesAt s₃.mem D n := by
      rw [Proof.AesGcm.X86_64.bytesAt_frame fO (fun q hq => by
          simp only [List.mem_singleton] at hq; subst hq; exact Ar.data.w.sub_right (Lay.wSub (by decide)))
          (by have := Ar.data.lt; omega),
        Proof.AesGcm.X86_64.bytesAt_frame Tg.frame dD (by have := Ar.data.lt; omega),
        Proof.AesGcm.X86_64.bytesAt_frame Po.frame dP (by have := Ar.data.lt; omega)]
    have ax : s₉.gpr .rax = s₆.mem.readW (W + BitVec.ofNat 64 192) 64 := by
      rw [hax₉, hax₈, Mk.frame.readW (r := ⟨W + BitVec.ofNat 64 192, 8⟩) (Region.contains_self _ _) (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact (Ar.data.w.sub_right (Lay.wSub (by decide))).symm)
        (by decide)]
    have md := Mk.data
    have ax' := ax.trans hok
    rw [tg, tag₅] at ax'
    rw [tg, tag₅, d₆, pt₃] at md
    have hdec : Spec.GcmSiv.decryptWith (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt s.mem N 12)
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
      · rw [hm₉, hm₈, md]; simp only [hc, ↓reduceIte]
    · refine openPost_none (by rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]) ?_ ?_
      · rw [ax']; simp only [hc, ↓reduceIte]; decide
      · rw [hm₉, hm₈, md]; simp only [hc, ↓reduceIte]

/-- `vg_aes_gcm_siv_open`. -/
theorem open_wp (v : GcmImpl) (eb : Proof.Aes.X86_64.BlocksImpl) (hpv : GcmSiv.Polyval.PolyvalEq) {s : State} (h : openPre s) :
    WP isa («open» v.callees ⟨eb.enc.name, eb.enc.code⟩) s fun s' => gprPreserved s s' ∧ openX86_64.post s s' := by
  obtain ⟨⟨Ar, Tb⟩, hTr⟩ := args_of_open h
  exact open_wp' v eb hpv Ar Tb hTr rfl (ofNat_toNat64 _).symm rfl rfl rfl (ofNat_toNat64 _).symm rfl rfl
    (ofNat_toNat64 _).symm rfl

end VG.Proof.AesGcmSiv.X86_64
