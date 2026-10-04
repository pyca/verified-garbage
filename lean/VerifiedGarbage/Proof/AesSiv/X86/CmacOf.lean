import VerifiedGarbage.Proof.AesSiv.X86.Entry
import VerifiedGarbage.Proof.AesSiv.CtrPart
import VerifiedGarbage.Proof.AesGcm.X86.Cmp

/-!
# AES-SIV on x86: the CMAC of a string (`cmacOf`)

Untrusted: everything here is checked by Lean. `cmacOf stOff` computes the
CMAC of the string at `W + strO` (`W + slenO` bytes) with the context's PRF
into the state at `W + 144`: the code zeroes the state, computes `16 nb`,
the bytes of the whole blocks before the last 1 to 16
(`Spec.Cmac.chainedLen`, `chained_bv`), stores it at `W + nbO`, chains the
`nb` blocks with `vg_cmac_aes_update` and finalizes the rest with
`vg_cmac_aes_finalize` from the context's subkeys (`Siv.cmacWith_chained`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 toNat_add32 slotv zero4_fold length_bytesAt shr4 ofNat_sub32
  and_self_beq32 covers_left readW_writeW_off)

/-! ## The length of the whole blocks -/

/-- `and` with `0xfffffff0`: rounding down to a multiple of 16. -/
theorem and_m16 (x : BitVec 32) : x &&& BitVec.ofNat 32 4294967280 = BitVec.ofNat 32 (x.toNat / 16 * 16) := by
  have : BitVec.ofNat 32 4294967280 = BitVec.ofNat 32 ((2 ^ 28 - 1) <<< 4) := by decide
  rw [this]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hx := x.isLt
  generalize x.toNat = n at *
  rw [Nat.mod_eq_of_lt (by decide), Nat.mod_eq_of_lt (by omega),
    show n / 16 * 16 = (n >>> 4) <<< 4 by rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one]
  by_cases hi : 4 ≤ i
  · by_cases h2 : i - 4 < 28
    · simp [hi, h2, show 4 + (i - 4) = i by omega]
    · have : n.testBit i = false := Nat.testBit_lt_two_pow (by
        calc n < 2 ^ 32 := hx
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega))
      simp [hi, h2, this, show 4 + (i - 4) = i by omega]
  · simp [hi]

/-- `chainedLen 16 k` as the code computes it, for `k > 0`: `(k − 1) & ~15`. -/
theorem chained_bv {k : Nat} (h0 : 0 < k) (hk : k < 2 ^ 32) :
    (BitVec.ofNat 32 k - BitVec.ofNat 32 1) &&& BitVec.ofNat 32 4294967280 =
      BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 k) := by
  rw [show (1#32 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ofNat_sub32 h0 hk, and_m16, toNat_ofNat32 (by omega)]
  congr 1
  simp only [Spec.Cmac.chainedLen]
  omega

theorem chainedLen_le (k : Nat) : Spec.Cmac.chainedLen 16 k ≤ k := by
  simp only [Spec.Cmac.chainedLen]; omega

theorem chainedLen_rest (k : Nat) : k - Spec.Cmac.chainedLen 16 k ≤ 16 := by
  simp only [Spec.Cmac.chainedLen]; omega

theorem chainedLen_div (k : Nat) : 16 * (Spec.Cmac.chainedLen 16 k / 16) = Spec.Cmac.chainedLen 16 k := by
  simp only [Spec.Cmac.chainedLen]; omega

/-! ## What `cmacOf` writes -/

/-- The CMAC state, `16 nb` at `W + nbO`, the working space of the functions
called and the stack below `SP`. -/
abbrev cmacR (W SP : BitVec 32) : List Region :=
  [⟨w64 W + BitVec.ofNat 64 stOff, 16⟩, ⟨w64 W + BitVec.ofNat 64 nbO, 4⟩, ⟨w64 W + BitVec.ofNat 64 256, 2176⟩,
    below SP 56]

/-- What `cmacOf` leaves: the CMAC of `S` with the context's PRF in the state
at `W + 144`. -/
structure CmacPost (C W SP : BitVec 32) (R : Nat) (s : State) (S : List Byte) (s' : State) : Prop where
  env : Env C W SP s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame (cmacR W SP) s.mem s'.mem
  out : bytesAt s'.mem (w64 W + BitVec.ofNat 64 stOff) 16 = Spec.Siv.ctxMac s.mem (w64 C) R S

/-- What the string's CMAC needs: the key context and the rounds in their
slots, the string `P` (`k` bytes) at `W + strO` and `W + slenO`. -/
structure CmacPre (C W SP : BitVec 32) (R : Nat) (P : BitVec 32) (k : Nat) (s : State) : Prop where
  env : Env C W SP s
  ctx : slotv s.mem W ctxO = C
  rounds : slotv s.mem W roundsO = BitVec.ofNat 32 R
  str : slotv s.mem W strO = P
  slen : slotv s.mem W slenO = BitVec.ofNat 32 k
  k32 : k < 2 ^ 32
  buf : Buf W SP s P k

/-! ## Before the update -/

theorem cmacA_ok {C W SP : BitVec 32} (L : Lay C W SP) {R : Nat} {P : BitVec 32} {k : Nat} {s : State}
    (h : CmacPre C W SP R P k s) :
    ∃ s₁, runBlock isa (zero4 stOff ++ ([.mov .ecx (imm 0), .mov .eax (slot slenO), .alu .test .eax (.reg .eax)] :
        List Instr)) s = some s₁ ∧
      s₁.mem = Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 stOff) ∧ s₁.gpr .ecx = BitVec.ofNat 32 0 ∧
      s₁.gpr .eax = BitVec.ofNat 32 k ∧ s₁.zf = some (decide (k = 0)) ∧ s₁.gpr .ebp = W ∧ s₁.gpr .esp = SP ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have E := h.env
  have hk := h.buf.lt
  have hz := zero4_fold s.mem W stOff
  simp only [Nat.reduceAdd, stOff] at hz
  have fz : Frame [⟨w64 W + BitVec.ofNat 64 144, 16⟩] s.mem (Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 144)) :=
    Cmac.frame_store4 _ _ _ _ _
  have hk' : slotv (Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 144)) W slenO = BitVec.ofNat 32 k := by
    exact (fz.readW (w := 32) (r := ⟨w64 W + BitVec.ofNat 64 slenO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (by decide) (by decide) (by decide))
      (by decide)).trans h.slen
  refine ⟨_, by crun [zero4, E.ebp, L.aW, E.perm.wW, E.perm.wR, hz, hk'], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cmems [hz]
  · cregs []
  · cregs [hk']
  · cmems [hk']; rw [and_self_beq32 h.k32]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []

theorem cmacB_ok {s : State} {k : Nat} (hax : s.gpr .eax = BitVec.ofNat 32 k) (h0 : 0 < k) (hk : k < 2 ^ 32) :
    ∃ s', runBlock isa [.mov .ecx (.reg .eax), .alu .sub .ecx (imm 1), .alu .and .ecx (imm 0xfffffff0)] s =
        some s' ∧
      s'.gpr .ecx = BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 k) ∧ s'.gpr .ebp = s.gpr .ebp ∧
      s'.gpr .esp = s.gpr .esp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cregs [hax, chained_bv h0 hk]
  · cregs []
  · cregs []
  all_goals cmems []

theorem cmacC_ok {C W SP : BitVec 32} (L : Lay C W SP) {R : Nat} {P : BitVec 32} {s : State}
    (E : Env C W SP s) (hc : slotv s.mem W ctxO = C) (hr : slotv s.mem W roundsO = BitVec.ofNat 32 R)
    (hp : slotv s.mem W strO = P) {c : Nat} (hcl : c < 2 ^ 32) (hcx : s.gpr .ecx = BitVec.ofNat 32 c) :
    ∃ s', runBlock isa ([.store (at_ .ebp nbO) .ecx, .mov .esi (.reg .ecx), .shift .shr .esi 4,
        .mov .ebx (slot strO)] ++ macArgs stOff) s = some s' ∧
      s'.mem = s.mem.writeW (w64 W + BitVec.ofNat 64 nbO) (BitVec.ofNat 32 c) ∧
      s'.gpr .eax = C ∧ s'.gpr .ecx = BitVec.ofNat 32 R ∧ s'.gpr .edx = W + BitVec.ofNat 32 144 ∧
      s'.gpr .ebx = P ∧ s'.gpr .esi = BitVec.ofNat 32 (c / 16) ∧ s'.gpr .edi = W + BitVec.ofNat 32 256 ∧
      s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hsh := shr4 hcl
  have rd : ∀ o, o + 4 ≤ nbO →
      slotv (s.mem.writeW (w64 W + BitVec.ofNat 64 nbO) (BitVec.ofNat 32 c)) W o = slotv s.mem W o :=
    fun o h₁ => readW_writeW_off _ _ _ (.inl h₁) (by simp only [nbO] at h₁; omega) (by decide)
  have hc' := (rd ctxO (by decide)).trans hc
  have hr' := (rd roundsO (by decide)).trans hr
  have hp' := (rd strO (by decide)).trans hp
  refine ⟨_, by crun [macArgs, E.ebp, L.aW, E.perm.wW, E.perm.wR, hcx, hc', hr', hp'], ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · cmems [hcx]
  · cregs [hc']
  · cregs [hr']
  · cregs [E.ebp]
  · cregs [hp']
  · cregs [hcx, hsh]
  · cregs [E.ebp]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []

/-- What `cmacPre` leaves: the arguments of `vg_cmac_aes_update` for the
whole blocks before the last bytes, the zero state, and their length at
`W + nbO`. -/
structure CmacMid (C W SP : BitVec 32) (R : Nat) (P : BitVec 32) (k : Nat) (s s₁ : State) : Prop where
  env : Env C W SP s₁
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr
  mem : s₁.mem = (Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 stOff)).writeW (w64 W + BitVec.ofNat 64 nbO)
    (BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 k))
  eax : s₁.gpr .eax = C
  ecx : s₁.gpr .ecx = BitVec.ofNat 32 R
  edx : s₁.gpr .edx = W + BitVec.ofNat 32 144
  ebx : s₁.gpr .ebx = P
  esi : s₁.gpr .esi = BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 k / 16)
  edi : s₁.gpr .edi = W + BitVec.ofNat 32 256

theorem cmacPre_ok {C W SP : BitVec 32} (L : Lay C W SP) {R : Nat} {P : BitVec 32} {k : Nat} {s : State}
    (h : CmacPre C W SP R P k s) : WP isa (cmacPre stOff) s (CmacMid C W SP R P k s) := by
  have E := h.env
  have hk := h.buf.lt
  have hk32 := h.k32
  have hcl := chainedLen_le k
  obtain ⟨s₁, run₁, m₁, cx₁, ax₁, zf₁, bp₁, sp₁, rd₁, wr₁⟩ := cmacA_ok L h
  have E₁ : Env C W SP s₁ := ⟨bp₁, sp₁, E.perm.of_eq rd₁ wr₁⟩
  have fz : Frame [⟨w64 W + BitVec.ofNat 64 144, 16⟩] s.mem s₁.mem := by
    rw [m₁]; exact Cmac.frame_store4 _ _ _ _ _
  have keep : ∀ o, 176 ≤ o → o + 4 ≤ 208 → slotv s₁.mem W o = slotv s.mem W o := fun o h₁ h₂ =>
    fz.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by omega)) (by omega) (by decide))
      (by decide)
  have last (s₂ : State) (E₂ : Env C W SP s₂) (rd₂ : s₂.rd = s.rd) (wr₂ : s₂.wr = s.wr) (m₂ : s₂.mem = s₁.mem)
      (cx₂ : s₂.gpr .ecx = BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 k)) :
      WP isa (.block ([.store (at_ .ebp nbO) .ecx, .mov .esi (.reg .ecx), .shift .shr .esi 4,
        .mov .ebx (slot strO)] ++ macArgs stOff)) s₂ (CmacMid C W SP R P k s) := by
    obtain ⟨s₃, run₃, m₃, ax₃, cx₃, dx₃, bx₃, si₃, di₃, bp₃, sp₃, rd₃, wr₃⟩ := cmacC_ok (R := R) (P := P) L E₂
      (by rw [m₂, keep _ (by decide) (by decide)]; exact h.ctx)
      (by rw [m₂, keep _ (by decide) (by decide)]; exact h.rounds)
      (by rw [m₂, keep _ (by decide) (by decide)]; exact h.str) (by omega) cx₂
    exact WP.of_runBlock ⟨s₃, run₃, ⟨bp₃, sp₃, E.perm.of_eq (by rw [rd₃, rd₂]) (by rw [wr₃, wr₂])⟩,
      by rw [rd₃, rd₂], by rw [wr₃, wr₂], by rw [m₃, m₂, m₁], ax₃, cx₃, dx₃, bx₃, si₃, di₃⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have mid : WP isa (.ite .e (.block []) (.block [.mov .ecx (.reg .eax), .alu .sub .ecx (imm 1),
      .alu .and .ecx (imm 0xfffffff0)])) s₁ fun s₂ =>
      s₂.gpr .ecx = BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 k) ∧ Env C W SP s₂ ∧ s₂.rd = s.rd ∧
        s₂.wr = s.wr ∧ s₂.mem = s₁.mem := by
    refine WP.ite (decide (k = 0)) (eval_e zf₁) (fun hz => ?_) (fun hz => ?_)
    · have hk0 : k = 0 := of_decide_eq_true hz
      refine WP.of_runBlock ⟨s₁, rfl, ?_, E₁, rd₁, wr₁, rfl⟩
      rw [cx₁, hk0]; rfl
    · have hk0 : 0 < k := Nat.pos_of_ne_zero (of_decide_eq_false hz)
      obtain ⟨s₂, run₂, cx₂, bp₂, sp₂, m₂, rd₂, wr₂⟩ := cmacB_ok ax₁ hk0 hk32
      exact WP.of_runBlock ⟨s₂, run₂, cx₂, E₁.keep bp₂ sp₂ rd₂ wr₂, by rw [rd₂, rd₁], by rw [wr₂, wr₁], m₂⟩
  exact WP.seq (WP.mono mid fun s₂ ⟨cx₂, E₂, rd₂, wr₂, m₂⟩ => last s₂ E₂ rd₂ wr₂ m₂ cx₂)

theorem chainedLen_lt {k : Nat} (h0 : 0 < k) : Spec.Cmac.chainedLen 16 k < k := by
  simp only [Spec.Cmac.chainedLen]; omega

/-! ## Between the calls -/

theorem cmacMid_ok {C W SP : BitVec 32} (L : Lay C W SP) {R : Nat} {P : BitVec 32} {k c : Nat} {s : State}
    (E : Env C W SP s) (hc : slotv s.mem W ctxO = C) (hr : slotv s.mem W roundsO = BitVec.ofNat 32 R)
    (hp : slotv s.mem W strO = P) (hk : slotv s.mem W slenO = BitVec.ofNat 32 k)
    (hn : slotv s.mem W nbO = BitVec.ofNat 32 c) (hck : c ≤ k) (hk32 : k < 2 ^ 32) :
    ∃ s', runBlock isa (cmacMid stOff) s = some s' ∧ s'.mem = s.mem ∧
      s'.gpr .eax = C ∧ s'.gpr .ecx = BitVec.ofNat 32 R ∧ s'.gpr .edx = W + BitVec.ofNat 32 144 ∧
      s'.gpr .ebx = P + BitVec.ofNat 32 c ∧ s'.gpr .esi = BitVec.ofNat 32 (k - c) ∧
      s'.gpr .edi = W + BitVec.ofNat 32 256 ∧ s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hsub := ofNat_sub32 hck hk32
  refine ⟨_, by crun [cmacMid, macArgs, E.ebp, L.aW, E.perm.wR, hc, hr, hp, hk, hn], ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rfl
  · cregs [hc]
  · cregs [hr]
  · cregs [E.ebp]
  · cregs [hp, hn]
  · cregs [hk, hn, hsub]
  · cregs [E.ebp]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals rfl

/-! ## The whole -/

theorem cmacR_c {C W SP : BitVec 32} (L : Lay C W SP) {d n : Nat} (hd : d + n ≤ 512) :
    ∀ r ∈ cmacR W SP, (⟨w64 C + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.c_w' hd (by decide)
  · exact L.c_w' hd (by decide)
  · exact L.c_w' hd (by decide)
  · exact (L.stk_c' hd).symm

theorem cmacR_buf {W SP : BitVec 32} {s : State} {P : BitVec 32} {k : Nat} (B : Buf W SP s P k) :
    ∀ r ∈ cmacR W SP, (⟨w64 P, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact B.w.sub_right (Lay.wSub (by decide))
  · exact B.w.sub_right (Lay.wSub (by decide))
  · exact B.w.sub_right (Lay.wSub (by decide))
  · exact B.stk.symm

theorem sub_cmacR {W SP : BitVec 32} {rs : List Region} (h : ∀ r ∈ rs, ∃ r' ∈ cmacR W SP, Region.Sub r r')
    {m m' : Mem} (hf : Frame rs m m') : Frame (cmacR W SP) m m' := hf.sub h

/-- The CMAC of the string at `W + strO`. -/
theorem cmacOf_ok (v : Ctr32Impl) {C W SP : BitVec 32} (L : Lay C W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {P : BitVec 32} {k : Nat} {s : State} (h : CmacPre C W SP R P k s) :
    WP isa (cmacOf v.callee v.suffix stOff) s (CmacPost C W SP R s (bytesAt s.mem (w64 P) k)) := by
  have hk32 := h.k32
  have hcl := chainedLen_le k
  have hrest := chainedLen_rest k
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with h | h | h <;> omega
  refine WP.seq (WP.mono (cmacPre_ok L h) fun s₁ M => ?_)
  -- The whole blocks.
  have B₁ : Buf W SP s₁ P (16 * (Spec.Cmac.chainedLen 16 k / 16)) :=
    (h.buf.take (by rw [chainedLen_div]; exact hcl)).of_eq M.rd M.wr
  refine WP.seq (WP.mono (updCall_ok v L M.env hR (y := 144) (.inl (by decide)) (srcBuf B₁)
    (B₁.w.sub_right (Lay.wSub (by decide))) (by rw [chainedLen_div]; omega) M.eax M.ecx M.edx M.ebx M.esi M.edi)
    fun s₂ ⟨E₂, rd₂, wr₂, _, f₂, o₂⟩ => ?_)
  -- The slots after the update.
  have fz : Frame [⟨w64 W + BitVec.ofNat 64 144, 16⟩, ⟨w64 W + BitVec.ofNat 64 nbO, 4⟩] s.mem s₁.mem := by
    rw [M.mem]
    exact ((Cmac.frame_store4 _ _ _ _ _).sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩).writeW (by simp) _
      (Region.contains_self _ _)
  have f₁₂ : Frame (cmacR W SP) s.mem s₂.mem := by
    refine (fz.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  have keep₂ : ∀ o, 176 ≤ o → o + 4 ≤ 208 → slotv s₂.mem W o = slotv s.mem W o := fun o h₁ h₂ =>
    f₁₂.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact Lay.w_w (.inr (by simp only [stOff]; omega)) (by omega) (by decide)
      · exact Lay.w_w (.inl (by simp only [nbO]; omega)) (by omega) (by decide)
      · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
      · exact (L.stk_w' (by omega)).symm) (by decide)
  have hn₂ : slotv s₂.mem W nbO = BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 k) := by
    rw [show slotv s₂.mem W nbO = slotv s₁.mem W nbO from f₂.readW (r := ⟨w64 W + BitVec.ofNat 64 nbO, 4⟩)
      (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact (L.stk_w' (by decide)).symm) (by decide), M.mem]
    exact Mem.readW_writeW_self32 _ _ _
  -- Between the calls.
  obtain ⟨s₃, run₃, m₃, ax₃, cx₃, dx₃, bx₃, si₃, di₃, bp₃, sp₃, rd₃, wr₃⟩ := cmacMid_ok (C := C) (R := R) (P := P) (k := k) L E₂
    (by rw [keep₂ _ (by decide) (by decide)]; exact h.ctx) (by rw [keep₂ _ (by decide) (by decide)]; exact h.rounds)
    (by rw [keep₂ _ (by decide) (by decide)]; exact h.str) (by rw [keep₂ _ (by decide) (by decide)]; exact h.slen)
    hn₂ hcl hk32
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have E₃ : Env C W SP s₃ := ⟨bp₃, sp₃, E₂.perm.of_eq rd₃ wr₃⟩
  -- The last bytes.
  have hwc : P.toNat + Spec.Cmac.chainedLen 16 k < 2 ^ 32 := by
    have := h.buf.wrap
    have := P.isLt
    by_cases h0 : k = 0
    · subst h0; simp only [Spec.Cmac.chainedLen]; omega
    · have := chainedLen_lt (Nat.pos_of_ne_zero h0); omega
  have B₃ : Buf W SP s₃ (P + BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 k)) (k - Spec.Cmac.chainedLen 16 k) :=
    (h.buf.drop hcl hwc).of_eq (by rw [rd₃, rd₂, M.rd]) (by rw [wr₃, wr₂, M.wr])
  refine WP.mono (finCall_ok v L E₃ hR (y := 144) (.inl (by decide)) hrest (srcBuf B₃)
    (B₃.w.sub_right (Lay.wSub (by decide))) ax₃ cx₃ dx₃ bx₃ si₃ di₃) fun s₄ ⟨E₄, rd₄, wr₄, _, f₄, o₄⟩ => ?_
  have f₁₄ : Frame (cmacR W SP) s.mem s₄.mem := f₁₂.trans (by
    rw [← m₃]
    exact f₄.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩)
  refine ⟨E₄, by rw [rd₄, rd₃, rd₂, M.rd], by rw [wr₄, wr₃, wr₂, M.wr], f₁₄, ?_⟩
  -- The bytes the calls read are those at the start.
  have hC {d n : Nat} (hd : d + n ≤ 512) (m : Mem) (hm : Frame (cmacR W SP) s.mem m) :
      bytesAt m (w64 C + BitVec.ofNat 64 d) n = bytesAt s.mem (w64 C + BitVec.ofNat 64 d) n :=
    Proof.AesGcm.X86.bytesAt_frame hm (cmacR_c L hd) (by omega)
  have hP {d n : Nat} (hd : d + n ≤ k) (m : Mem) (hm : Frame (cmacR W SP) s.mem m) :
      bytesAt m (w64 P + BitVec.ofNat 64 d) n = bytesAt s.mem (w64 P + BitVec.ofNat 64 d) n :=
    Proof.AesGcm.X86.bytesAt_frame hm (fun r hr => (cmacR_buf h.buf r hr).sub_left (Offset.sub_base _ hd))
      (by have := h.buf.lt; omega)
  have f₁₃ : Frame (cmacR W SP) s.mem s₃.mem := by rw [m₃]; exact f₁₂
  have f₁₁ : Frame (cmacR W SP) s.mem s₁.mem := fz.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  have sch₃ := hC (d := 0) (n := 16 * (R + 1)) (by omega) _ f₁₃
  have sch₁ := hC (d := 0) (n := 16 * (R + 1)) (by omega) _ f₁₁
  have k1 := hC (d := 240) (n := 16) (by decide) _ f₁₃
  have k2 := hC (d := 256) (n := 16) (by decide) _ f₁₃
  have pre := hP (d := 0) (n := Spec.Cmac.chainedLen 16 k) (by omega) _ f₁₁
  have rest := hP (d := Spec.Cmac.chainedLen 16 k) (n := k - Spec.Cmac.chainedLen 16 k) (by omega) _ f₁₃
  rw [BitVec.add_zero] at sch₃ sch₁ pre
  have hz : bytesAt s₁.mem (w64 W + BitVec.ofNat 64 144) 16 = Spec.Cmac.zeros 16 := by
    rw [M.mem, Proof.AesGcm.X86.bytesAt_frame (rs := [⟨w64 W + BitVec.ofNat 64 nbO, 4⟩])
      ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide))
      (by decide), Cmac.zero4_bytes]
  have hS : (bytesAt s.mem (w64 P) k).length = k := length_bytesAt _ _ _
  have hsplit : k = Spec.Cmac.chainedLen 16 k + (k - Spec.Cmac.chainedLen 16 k) := by omega
  have aP : w64 (P + BitVec.ofNat 32 (Spec.Cmac.chainedLen 16 k)) =
      w64 P + BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 k) := Buf.ptr hwc
  rw [o₄, sch₃, k1, k2, aP, rest, m₃, o₂, Proof.Cmac.Stream.blocksAt_eq, chainedLen_div, sch₁, hz, pre,
    Spec.Siv.ctxMac, Spec.Siv.schedCiph, Siv.cmacWith_chained, hS]
  have tk : (bytesAt s.mem (w64 P) k).take (Spec.Cmac.chainedLen 16 k) =
      bytesAt s.mem (w64 P) (Spec.Cmac.chainedLen 16 k) := by
    have := take_bytesAt s.mem (w64 P) (a := Spec.Cmac.chainedLen 16 k) (b := k - Spec.Cmac.chainedLen 16 k)
    rwa [← hsplit] at this
  have dr : (bytesAt s.mem (w64 P) k).drop (Spec.Cmac.chainedLen 16 k) =
      bytesAt s.mem (w64 P + BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 k)) (k - Spec.Cmac.chainedLen 16 k) := by
    have := drop_bytesAt s.mem (w64 P) (a := Spec.Cmac.chainedLen 16 k) (b := k - Spec.Cmac.chainedLen 16 k)
    rwa [← hsplit] at this
  rw [tk, dr, Proof.Cmac.xor_comm]
  rfl

end VG.Proof.AesSiv.X86
