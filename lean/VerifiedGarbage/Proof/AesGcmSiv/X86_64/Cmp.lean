import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Crypt

/-!
# AES-GCM-SIV on x86-64: comparing the tags and masking (`cmp`, `mask`)

Untrusted: everything here is checked by Lean. `cmp` stores at `W + 208`
whether the received tag at `W` equals the computed one at `W + 144`,
without a branch (`cmp_ok`); `mask` ANDs every byte of the data with
`0 − ok`, leaving it if the tags are equal and zeroing it if not
(`mask_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_snoc)
open VG.Proof.AesGcm.X86_64 (toNat_ofNat_of_lt)

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

theorem cmp_ok {K W SP : Addr} (L : Lay K W SP) {t : State} (E : Env K W SP t) :
    ∃ t' : State, runBlock isa cmp t = some t' ∧
      t'.mem = t.mem.writeW (W + BitVec.ofNat 64 208)
        (if bytesAt t.mem W 16 = bytesAt t.mem (W + BitVec.ofNat 64 144) 16 then 1#64 else 0#64) ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have h15 := E.r15
  have r₀ : InRegions (t.rd ++ t.wr) W 8 := by simpa using E.perm.wR (show 0 + 8 ≤ 4096 by decide)
  have r₈ := E.perm.wR (show 8 + 8 ≤ 4096 by decide)
  have u₀ := E.perm.wR (show 144 + 8 ≤ 4096 by decide)
  have u₈ := E.perm.wR (show 152 + 8 ≤ 4096 by decide)
  have wo := E.perm.wW (show 208 + 8 ≤ 4096 by decide)
  refine ⟨_, by srun [Impl.AesGcmSiv.X86_64.cmp, h15, r₀, r₈, u₀, u₈, wo], ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, mem_setFlags, gpr_setReg, gpr_arithFlags, cf_arithFlags, cf_setReg,
      ite_true, ite_false, reduceCtorEq]
    have hb := bytes16_eq t.mem W (W + BitVec.ofNat 64 144)
    rw [add_ofNat_assoc] at hb
    simp only [ok_val, hb]
  · intro r hr; simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
  all_goals rfl

abbrev maskBody : List Instr :=
  [.movzx8 .rax maskByte, .alu .and .rax (.reg .r11), .store8 maskByte .rax, .alu .add .r10 (imm 1),
    .alu .cmp .r10 (.reg .rbp)]

theorem setWidth8_and (a : Byte) (k : BitVec 64) : ((a.setWidth 64 &&& k : BitVec 64)).setWidth 8 = a &&& k.setWidth 8 := by
  ext j hj; simp

theorem maskStep_ok (s : State) {D : Addr} {i n : Nat} (hd : s.gpr .r12 = D)
    (hi : s.gpr .r10 = BitVec.ofNat 64 i) (hn : s.gpr .rbp = BitVec.ofNat 64 n)
    (w : InRegions s.wr (D + BitVec.ofNat 64 i) 1) :
    ∃ s', runBlock isa maskBody s = some s' ∧
      s'.mem = s.mem.writeW (D + BitVec.ofNat 64 i) (s.mem (D + BitVec.ofNat 64 i) &&& (s.gpr .r11).setWidth 8) ∧
      s'.gpr .r10 = BitVec.ofNat 64 i + 1 ∧
      s'.zf = some (BitVec.ofNat 64 i + 1 - BitVec.ofNat 64 n == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e₁ := Proof.AesGcm.X86_64.ea_idx s .r12 hd hi
  have wr' : InRegions (s.rd ++ s.wr) (D + BitVec.ofNat 64 i) 1 := by
    obtain ⟨x, hx, hc⟩ := w; exact ⟨x, List.mem_append_right _ hx, hc⟩
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceAdd, Nat.reduceMod, Nat.reducePow, BitVec.reduceSignExtend,
      maskBody, maskByte, imm, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, State.load8,
      State.store8, State.ea, Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags, mem_setReg,
      mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, ite_true, ite_false, e₁, w, wr']
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl⟩
  · simp only [mem_setReg, mem_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq,
      setWidth8_and]
  · simp [gpr_setReg, hi]
  · simp [hi, hn]
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]

/-- Byte `i` at `D`, not yet written. -/
theorem dst_kept {m : Mem} {D : Addr} {i : Nat} (hi : i < 2 ^ 64) (xs : List Byte)
    (hxs : xs.length = i) : writeBytes m D xs (D + BitVec.ofNat 64 i) = m (D + BitVec.ofNat 64 i) := by
  simp only [writeBytes, hxs, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.lt_irrefl,
    ite_false]

/-- The first `i` bytes at `D`, each ANDed with `k`. -/
abbrev maskBytes (m : Mem) (D : Addr) (k : Byte) (i : Nat) : List Byte := (bytesAt m D i).map (· &&& k)

theorem maskLoop_ok (s : State) {D : Addr} {n : Nat} (hd : s.gpr .r12 = D) (hn : s.gpr .rbp = BitVec.ofNat 64 n)
    (hi : s.gpr .r10 = BitVec.ofNat 64 0) (hn1 : 1 ≤ n) (hnl : n < 2 ^ 64) (hw : Covers [⟨D, n⟩] s.wr) :
    WP isa (.loop (.block maskBody) .ne) s fun s' =>
      s'.mem = writeBytes s.mem D (maskBytes s.mem D ((s.gpr .r11).setWidth 8) n) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.loop (M := isa) (body := .block maskBody) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .r10 = BitVec.ofNat 64 i ∧
      t.mem = writeBytes s.mem D (maskBytes s.mem D ((s.gpr .r11).setWidth 8) i) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, hn1, hi, by simp [maskBytes, bytesAt, writeBytes_nil], fun _ _ _ => rfl, rfl, rfl⟩
  rintro k t ⟨i, rfl, hi', r10, mem, g, rd, wr⟩
  obtain ⟨t', run', mem', r10', zf', g', rd', wr'⟩ := maskStep_ok t
    (by rw [g _ (by decide) (by decide), hd]) r10 (by rw [g _ (by decide) (by decide), hn])
    (by rw [wr]; exact Proof.AesGcm.X86_64.in_of_covers hw hi' (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen : (maskBytes s.mem D ((s.gpr .r11).setWidth 8) i).length = i := by
    simp [maskBytes, Proof.Cmac.bytesAt_length]
  have hmem : t'.mem = writeBytes s.mem D (maskBytes s.mem D ((s.gpr .r11).setWidth 8) (i + 1)) := by
    rw [mem', mem, dst_kept (by omega) _ hlen, g _ (by decide) (by decide)]
    simp only [maskBytes]
    rw [Proof.AesGcm.X86_64.bytesAt_succ, List.map_append, List.map_cons, List.map_nil,
      writeBytes_snoc s.mem D _ _ (by rw [List.length_map, Proof.Cmac.bytesAt_length]; omega),
      List.length_map, Proof.Cmac.bytesAt_length]
  have hz : t'.zf = some (decide (i + 1 = n)) := by
    rw [zf', Proof.AesGcm.X86_64.succ_ofNat, Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
  have gg : ∀ r, r ≠ .rax → r ≠ .r10 → t'.gpr r = s.gpr r := fun r h₁ h₂ => by rw [g' r h₁ h₂, g r h₁ h₂]
  by_cases he : i + 1 = n
  · left
    refine ⟨by simp [eval, hz, he], by rw [hmem, he], gg, by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by simp [eval, hz, he], n - (i + 1), by omega, i + 1, rfl, by omega,
      by rw [r10', Proof.AesGcm.X86_64.succ_ofNat], hmem, gg, by rw [rd', rd], by rw [wr', wr]⟩

theorem map_and_ff (xs : List Byte) : xs.map (· &&& (0#64 - 1#64 : BitVec 64).setWidth 8) = xs := by
  rw [show (0#64 - 1#64 : BitVec 64).setWidth 8 = BitVec.allOnes 8 by decide,
    show (fun x : Byte => x &&& BitVec.allOnes 8) = id from funext fun x => BitVec.and_allOnes, List.map_id]

theorem map_and_zero (xs : List Byte) : xs.map (· &&& (0#64 - 0#64 : BitVec 64).setWidth 8) =
    Spec.GcmSiv.zeros xs.length := by
  rw [show (0#64 - 0#64 : BitVec 64).setWidth 8 = 0#8 by decide]
  simp [Spec.GcmSiv.zeros, List.map_const']

/-- What `mask` leaves, from `t`, when `ok` is whether `c` holds. -/
structure MaskPost (K W SP : Addr) (D : Addr) (n : Nat) (c : Prop) [Decidable c] (t t' : State) : Prop where
  env : Env K W SP t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame [⟨D, n⟩] t.mem t'.mem
  data : bytesAt t'.mem D n = if c then bytesAt t.mem D n else Spec.GcmSiv.zeros n

theorem mask_ok {K W SP : Addr} {t : State} (E : Env K W SP t) {R : Nat} {N A D : Addr} {al n : Nat}
    (S : Slots W R N A D al n t.mem) (hD : Buf K W SP t D n) (hDw : Covers [⟨D, n⟩] t.wr) {c : Prop} [Decidable c]
    (hok : t.mem.readW (W + BitVec.ofNat 64 208) 64 = if c then 1#64 else 0#64) :
    WP isa mask t (MaskPost K W SP D n c t) := by
  have h15 := E.r15
  have hn := hD.lt
  have rD := E.perm.wR (show 304 + 8 ≤ 4096 by decide)
  have rL := E.perm.wR (show 312 + 8 ≤ 4096 by decide)
  have rO := E.perm.wR (show 208 + 8 ≤ 4096 by decide)
  have sD := S.data
  have sL := S.len
  obtain ⟨t₁, run₁, h12₁, hbp₁, h11₁, h10₁, hzf₁, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ t₁ : State, runBlock isa
      [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO)), .mov32 .r11 (imm 0),
        .alu .sub .r11 (.mem (at_ .r15 okO)), .mov32 .r10 (imm 0), .alu .test .rbp (.reg .rbp)] t = some t₁ ∧
      t₁.gpr .r12 = D ∧ t₁.gpr .rbp = BitVec.ofNat 64 n ∧
      t₁.gpr .r11 = 0#64 - t.mem.readW (W + BitVec.ofNat 64 208) 64 ∧ t₁.gpr .r10 = BitVec.ofNat 64 0 ∧
      t₁.zf = some (decide (n = 0)) ∧ (∀ r ∈ [Reg.r13, .r15, .rsp], t₁.gpr r = t.gpr r) ∧ t₁.mem = t.mem ∧
      t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by srun [h15, rD, rL, rO], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, sD]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, sL]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, sL]
      rw [Proof.AesGcm.X86_64.and_self_beq hn]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have E₁ : Env K W SP t₁ := E.keep hg₁ hrd₁ hwr₁
  refine WP.ite (decide (n = 0)) (eval_e hzf₁) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    refine WP.block_nil ⟨E₁, hrd₁, hwr₁, by rw [hm₁]; exact Frame.refl _ _, ?_⟩
    simp [bytesAt, Spec.GcmSiv.zeros]
  · have h0 : n ≠ 0 := by simpa using hf
    refine WP.mono (maskLoop_ok t₁ h12₁ hbp₁ h10₁ (by omega) (by omega) (by rw [hwr₁]; exact hDw))
      fun t₂ ⟨hm₂, hg₂, hrd₂, hwr₂⟩ => ?_
    have hl : (maskBytes t₁.mem D ((t₁.gpr .r11).setWidth 8) n).length = n := by
      simp [maskBytes, Proof.Cmac.bytesAt_length]
    refine ⟨E₁.keep (fun r hr => ?_) hrd₂ hwr₂, hrd₂.trans hrd₁, hwr₂.trans hwr₁,
      by rw [hm₂, hm₁] at *; exact Proof.AesGcm.X86_64.writeBytes_frame' _ hl, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide)
    · have e := Proof.AesGcm.X86_64.bytesAt_writeBytes_self t₁.mem D
        (maskBytes t₁.mem D ((t₁.gpr .r11).setWidth 8) n) (by omega)
      rw [hl] at e
      rw [hm₂, e, h11₁, hok, hm₁]
      simp only [maskBytes]
      split
      · exact map_and_ff _
      · rw [map_and_zero, Proof.Cmac.bytesAt_length]

end VG.Proof.AesGcmSiv.X86_64
