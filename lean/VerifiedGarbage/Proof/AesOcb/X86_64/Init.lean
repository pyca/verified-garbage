import VerifiedGarbage.Proof.AesOcb.X86_64.Seal

/-!
# AES-OCB on x86-64: `vg_aes_ocb_init`

Untrusted: everything here is checked by Lean. `init` saves `rbx`, `rbp` and
`r12` in the scratch buffer, expands the key into the key context, enciphers
a zero block at byte 240 of it in place, for `L_*`, and restores the
registers (`init_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem)
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesCcm.X86_64 (runBlock_append length_bytesAt bytesAt_frame toNat_ofNat_of_lt)

/-- What `vg_aes_ocb_init` is given: the key (`KL` bytes at `Kp`), the key
context at `C` and the scratch buffer at `S`. -/
structure IArgs (s : State) (Kp C S : Addr) (KL : Nat) : Prop where
  rd : s.rd = [⟨Kp, KL⟩]
  wr : s.wr = [⟨C, 256⟩, ⟨S, 2560⟩]
  kc : (⟨Kp, KL⟩ : Region).Disjoint ⟨C, 256⟩
  ks : (⟨Kp, KL⟩ : Region).Disjoint ⟨S, 2560⟩
  cs : (⟨C, 256⟩ : Region).Disjoint ⟨S, 2560⟩
  retC : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨C, 256⟩
  retS : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨S, 2560⟩
  stkK : (below (s.gpr .rsp) 8).Disjoint ⟨Kp, KL⟩
  stkC : (below (s.gpr .rsp) 8).Disjoint ⟨C, 256⟩
  stkS : (below (s.gpr .rsp) 8).Disjoint ⟨S, 2560⟩
  wK : Kp.toNat + KL ≤ 2 ^ 64
  wC : C.toNat + 256 ≤ 2 ^ 64
  wS : S.toNat + 2560 ≤ 2 ^ 64
  sp : 8 ≤ (s.gpr .rsp).toNat
  klen : KL = 16 ∨ KL = 24 ∨ KL = 32

theorem IArgs.of {s : State} (h : initX86_64.pre s) :
    IArgs s (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .rsi).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o⟩

/-- The rounds, as `shr 2; add 6` computes them from the key length. -/
theorem rounds_bv {KL : Nat} (h : KL = 16 ∨ KL = 24 ∨ KL = 32) :
    BitVec.ofNat 64 KL >>> 2 + BitVec.ofNat 64 6 = BitVec.ofNat 64 (KL / 4 + 6) := by
  rcases h with rfl | rfl | rfl <;> decide

theorem rounds_of {KL : Nat} (h : KL = 16 ∨ KL = 24 ∨ KL = 32) :
    KL / 4 + 6 = 10 ∨ KL / 4 + 6 = 12 ∨ KL / 4 + 6 = 14 := by
  rcases h with rfl | rfl | rfl <;> decide

/-- A read of a word in a region, through a write in a region apart from it. -/
theorem readW_writeW_off' {m : Mem} {a b : Addr} {r r' : Region} {v : BitVec 64} (ha : r.Contains a (64 / 8))
    (hd : r.Disjoint r') (hb : r'.Contains b (64 / 8) := by exact Region.contains_self _ _) :
    (m.writeW b v).readW a 64 = m.readW a 64 :=
  Mem.readW_writeW_sep (hd.sep ha hb) (by decide)

/-- The registers saved and the arguments of the key expansion. -/
theorem init1_ok {s : State} {Kp C S : Addr} {KL : Nat} (Ar : IArgs s Kp C S KL)
    (hdi : s.gpr .rdi = Kp) (hsi : s.gpr .rsi = BitVec.ofNat 64 KL) (hdx : s.gpr .rdx = C) (hcx : s.gpr .rcx = S) :
    ∃ s₁, runBlock isa
      [st .rcx 0 .rbx, st .rcx 8 .rbp, st .rcx 16 .r12, mvr .rbx .rdx, mvr .rbp .rsi, .shift .shr .rbp 2,
        addi .rbp 6, mvr .r12 .rcx, addi .rcx scrO] s = some s₁ ∧
      s₁.gpr .rbx = C ∧ s₁.gpr .rbp = BitVec.ofNat 64 (KL / 4 + 6) ∧ s₁.gpr .r12 = S ∧
      (∀ r, r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ≠ .rcx → s₁.gpr r = s.gpr r) ∧
      s₁.mem = ((s.mem.writeW (S + BitVec.ofNat 64 0) (s.gpr .rbx)).writeW (S + BitVec.ofNat 64 8) (s.gpr .rbp)).writeW
        (S + BitVec.ofNat 64 16) (s.gpr .r12) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧
      KCall s₁ Kp C (S + BitVec.ofNat 64 512) KL ∧ s₁.gpr .rsp = s.gpr .rsp := by
  have hR := rounds_of Ar.klen
  have hKL : KL < 2 ^ 64 := by rcases Ar.klen with h | h | h <;> omega
  have inS : ∀ {d : Nat}, d + 8 ≤ 2560 → InRegions s.wr (S + BitVec.ofNat 64 d) 8 := fun h => by
    rw [Ar.wr]; exact ⟨⟨S, 2560⟩, by simp, Offset.contains_base _ h (by have := Ar.wS; omega)⟩
  have e6 : BitVec.signExtend 64 (BitVec.ofNat 32 6) = BitVec.ofNat 64 6 := by decide
  -- The registers saved, the arguments of the key expansion.
  obtain ⟨s₁, run₁, rdi₁, rsi₁, rdx₁, rcx₁, rbx₁, rbp₁, r12₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [st .rcx 0 .rbx, st .rcx 8 .rbp, st .rcx 16 .r12, mvr .rbx .rdx, mvr .rbp .rsi, .shift .shr .rbp 2,
        addi .rbp 6, mvr .r12 .rcx, addi .rcx scrO] s = some s₁ ∧
      s₁.gpr .rdi = Kp ∧ s₁.gpr .rsi = BitVec.ofNat 64 KL ∧ s₁.gpr .rdx = C ∧ s₁.gpr .rcx = S + BitVec.ofNat 64 512 ∧
      s₁.gpr .rbx = C ∧ s₁.gpr .rbp = BitVec.ofNat 64 (KL / 4 + 6) ∧ s₁.gpr .r12 = S ∧
      (∀ r, r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ≠ .rcx → s₁.gpr r = s.gpr r) ∧
      s₁.mem = ((s.mem.writeW (S + BitVec.ofNat 64 0) (s.gpr .rbx)).writeW (S + BitVec.ofNat 64 8) (s.gpr .rbp)).writeW
        (S + BitVec.ofNat 64 16) (s.gpr .r12) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by orun [hcx, inS (d := 0) (by decide), inS (d := 8) (by decide), inS (d := 16) (by decide)],
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h₁ h₂ h₃ h₄ => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hdi]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hsi]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hdx]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hcx]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hdx]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hsi, e6,
        rounds_bv Ar.klen]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hcx]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, h₁, h₂, h₃, h₄, ite_false]
    · simp only [mem_setReg, mem_arithFlags, mem_setFlags, hcx]
    all_goals rfl
  have SP := s.gpr .rsp
  have hsp₁ : s₁.gpr .rsp = s.gpr .rsp := g₁ _ (by decide) (by decide) (by decide) (by decide)
  have f₁ : Frame [⟨S, 24⟩] s.mem s₁.mem := by
    have c : ∀ d, d + 8 ≤ 24 → (⟨S, 24⟩ : Region).Contains (S + BitVec.ofNat 64 d) (64 / 8) := fun d hd =>
      Offset.contains_base _ hd (by have := Ar.wS; omega)
    rw [m₁]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 0 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 8 (by decide))).writeW (List.mem_singleton_self _) _ (c 16 (by decide))
  have sub_S : ∀ {d k : Nat}, d + k ≤ 2560 → Region.Sub ⟨S + BitVec.ofNat 64 d, k⟩ ⟨S, 2560⟩ :=
    fun h => Offset.sub_base S h
  have sub_C : ∀ {d k : Nat}, d + k ≤ 256 → Region.Sub ⟨C + BitVec.ofNat 64 d, k⟩ ⟨C, 256⟩ :=
    fun h => Offset.sub_base C h
  -- The key schedule.
  have K₁ : KCall s₁ Kp C (S + BitVec.ofNat 64 512) KL :=
    { rdi := rdi₁, rsi := rsi₁, rdx := rdx₁, rcx := rcx₁, klen := Ar.klen
      kc := Ar.kc.sub_right (Region.sub_prefix (by decide))
      ks := Ar.ks.sub_right (sub_S (by decide))
      cs := (Ar.cs.sub_left (Region.sub_prefix (by decide))).sub_right (sub_S (by decide))
      stkK := by rw [hsp₁]; exact Ar.stkK
      stkC := by rw [hsp₁]; exact Ar.stkC.sub_right (Region.sub_prefix (by decide))
      stkS := by rw [hsp₁]; exact Ar.stkS.sub_right (sub_S (by decide))
      reads := by
        rw [rd₁, wr₁, Ar.rd, Ar.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨⟨Kp, KL⟩, by simp, 0, by simp, by simp⟩
        · exact ⟨⟨C, 256⟩, by simp, 0, by simp, by simp⟩
        · exact ⟨⟨S, 2560⟩, by simp, 512, rfl, by simp⟩
      writes := by
        rw [wr₁, Ar.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨⟨C, 256⟩, by simp, 0, by simp, by simp⟩
        · exact ⟨⟨S, 2560⟩, by simp, 512, rfl, by simp⟩ }
  exact ⟨s₁, run₁, rbx₁, rbp₁, r12₁, g₁, m₁, rd₁, wr₁, K₁, hsp₁⟩

/-- A zero block at byte 240 of the key context and the arguments of its encipherment. -/
theorem init3_ok {s : State} {Kp C S : Addr} {KL : Nat} (Ar : IArgs s Kp C S KL) {s₂ : State}
    (h3 : s₂.gpr .rbx = C) (h5 : s₂.gpr .rbp = BitVec.ofNat 64 (KL / 4 + 6)) (h12 : s₂.gpr .r12 = S)
    (hrd : s₂.rd = s.rd) (hwr : s₂.wr = s.wr) (hsp : s₂.gpr .rsp = s.gpr .rsp) :
    ∃ s₃, runBlock isa
      [.alu .xor .rax (.reg .rax), st .rbx 240 .rax, st .rbx 248 .rax, mvr .rdi .rbx, mvr .rsi .rbp,
        mvr .rdx .rbx, addi .rdx 240, .mov .rcx (.imm 1), mvr .r8 .r12, addi .r8 scrO] s₂ = some s₃ ∧
      (∀ r ∈ calleeSaved, s₃.gpr r = s₂.gpr r) ∧
      s₃.mem = (s₂.mem.writeW (C + BitVec.ofNat 64 240) 0#64).writeW (C + BitVec.ofNat 64 248) 0#64 ∧
      s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr ∧
      BCall s₃ C (C + BitVec.ofNat 64 240) (S + BitVec.ofNat 64 512) (KL / 4 + 6) 1 ∧ s₃.gpr .rsp = s.gpr .rsp := by
  have hR := rounds_of Ar.klen
  have sub_S : ∀ {d k : Nat}, d + k ≤ 2560 → Region.Sub ⟨S + BitVec.ofNat 64 d, k⟩ ⟨S, 2560⟩ :=
    fun h => Offset.sub_base S h
  have sub_C : ∀ {d k : Nat}, d + k ≤ 256 → Region.Sub ⟨C + BitVec.ofNat 64 d, k⟩ ⟨C, 256⟩ :=
    fun h => Offset.sub_base C h
  -- `L_*`: a zero block at byte 240, enciphered.
  have w₁ : InRegions s₂.wr (C + BitVec.ofNat 64 240) 8 := by
    rw [hwr, Ar.wr]; exact ⟨⟨C, 256⟩, by simp, Offset.contains_base _ (by decide) (by have := Ar.wC; omega)⟩
  have w₂ : InRegions s₂.wr (C + BitVec.ofNat 64 248) 8 := by
    rw [hwr, Ar.wr]; exact ⟨⟨C, 256⟩, by simp, Offset.contains_base _ (by decide) (by have := Ar.wC; omega)⟩
  obtain ⟨s₃, run₃, rdi₃, rsi₃, rdx₃, rcx₃, r8₃, g₃, m₃, rd₃, wr₃⟩ : ∃ s₃, runBlock isa
      [.alu .xor .rax (.reg .rax), st .rbx 240 .rax, st .rbx 248 .rax, mvr .rdi .rbx, mvr .rsi .rbp,
        mvr .rdx .rbx, addi .rdx 240, .mov .rcx (.imm 1), mvr .r8 .r12, addi .r8 scrO] s₂ = some s₃ ∧
      s₃.gpr .rdi = C ∧ s₃.gpr .rsi = BitVec.ofNat 64 (KL / 4 + 6) ∧ s₃.gpr .rdx = C + BitVec.ofNat 64 240 ∧
      s₃.gpr .rcx = BitVec.ofNat 64 1 ∧ s₃.gpr .r8 = S + BitVec.ofNat 64 512 ∧
      (∀ r ∈ calleeSaved, s₃.gpr r = s₂.gpr r) ∧
      s₃.mem = (s₂.mem.writeW (C + BitVec.ofNat 64 240) 0#64).writeW (C + BitVec.ofNat 64 248) 0#64 ∧
      s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    refine ⟨_, by orun [h3, w₁, w₂], ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h3]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h5]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h3]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, sext1]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h12]
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    · simp only [mem_setReg, mem_arithFlags, BitVec.xor_self]
    all_goals rfl
  have hsp₃ : s₃.gpr .rsp = s.gpr .rsp := by rw [g₃ _ (by decide), hsp]
  have dC : (⟨C, 240⟩ : Region).Disjoint ⟨C + BitVec.ofNat 64 240, 16 * 1⟩ :=
    Offset.base_disjoint C (Nat.le_refl _) (by decide)
  have B₃ : BCall s₃ C (C + BitVec.ofNat 64 240) (S + BitVec.ofNat 64 512) (KL / 4 + 6) 1 :=
    { rdi := rdi₃, rsi := rsi₃, rdx := rdx₃, rcx := rcx₃, r8 := r8₃, rounds := hR
      wrap := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := Ar.wC; omega
      kd := dC
      ks := (Ar.cs.sub_left (Region.sub_prefix (by decide))).sub_right (sub_S (by decide))
      ds := (Ar.cs.sub_left (sub_C (by decide))).sub_right (sub_S (by decide))
      stkK := by rw [hsp₃]; exact Ar.stkC.sub_right (Region.sub_prefix (by decide))
      stkD := by rw [hsp₃]; exact Ar.stkC.sub_right (sub_C (by decide))
      stkS := by rw [hsp₃]; exact Ar.stkS.sub_right (sub_S (by decide))
      reads := by
        rw [rd₃, wr₃, hrd, hwr, Ar.rd, Ar.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨⟨C, 256⟩, by simp, 0, by simp, by simp⟩
        · exact ⟨⟨C, 256⟩, by simp, 240, rfl, by simp⟩
        · exact ⟨⟨S, 2560⟩, by simp, 512, rfl, by simp⟩
      writes := by
        rw [wr₃, hwr, Ar.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨⟨C, 256⟩, by simp, 240, rfl, by simp⟩
        · exact ⟨⟨S, 2560⟩, by simp, 512, rfl, by simp⟩ }
  exact ⟨s₃, run₃, g₃, m₃, rd₃, wr₃, B₃, hsp₃⟩

/-- `vg_aes_ocb_init`, for its arguments. -/
theorem init_wp' (v : BlocksImpl) {s : State} {Kp C S : Addr} {KL : Nat} (Ar : IArgs s Kp C S KL)
    (hdi : s.gpr .rdi = Kp) (hsi : s.gpr .rsi = BitVec.ofNat 64 KL) (hdx : s.gpr .rdx = C) (hcx : s.gpr .rcx = S) :
    WP isa (init (callees v)) s fun s' => gprPreserved s s' ∧
      Spec.Ocb.KeyRepr s'.mem C (bytesAt s.mem Kp KL) := by
  have hR := rounds_of Ar.klen
  have hKL : KL < 2 ^ 64 := by rcases Ar.klen with h | h | h <;> omega
  have inS : ∀ {d : Nat}, d + 8 ≤ 2560 → InRegions s.wr (S + BitVec.ofNat 64 d) 8 := fun h => by
    rw [Ar.wr]; exact ⟨⟨S, 2560⟩, by simp, Offset.contains_base _ h (by have := Ar.wS; omega)⟩
  obtain ⟨s₁, run₁, rbx₁, rbp₁, r12₁, g₁, m₁, rd₁, wr₁, K₁, hsp₁⟩ := init1_ok Ar hdi hsi hdx hcx
  have f₁ : Frame [⟨S, 24⟩] s.mem s₁.mem := by
    have c : ∀ d, d + 8 ≤ 24 → (⟨S, 24⟩ : Region).Contains (S + BitVec.ofNat 64 d) (64 / 8) := fun d hd =>
      Offset.contains_base _ hd (by have := Ar.wS; omega)
    rw [m₁]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 0 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 8 (by decide))).writeW (List.mem_singleton_self _) _ (c 16 (by decide))
  have sub_S : ∀ {d k : Nat}, d + k ≤ 2560 → Region.Sub ⟨S + BitVec.ofNat 64 d, k⟩ ⟨S, 2560⟩ :=
    fun h => Offset.sub_base S h
  have sub_C : ∀ {d k : Nat}, d + k ≤ 256 → Region.Sub ⟨C + BitVec.ofNat 64 d, k⟩ ⟨C, 256⟩ :=
    fun h => Offset.sub_base C h
  unfold init
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (key_call v K₁) fun s₂ P₂ => ?_)
  have sv₂ : ∀ r ∈ calleeSaved, s₂.gpr r = s₁.gpr r := P₂.saved
  obtain ⟨s₃, run₃, g₃, m₃, rd₃, wr₃, B₃, hsp₃⟩ := init3_ok Ar (by rw [sv₂ _ (by decide), rbx₁])
    (by rw [sv₂ _ (by decide), rbp₁]) (by rw [sv₂ _ (by decide), r12₁]) (by rw [P₂.rd, rd₁]) (by rw [P₂.wr, wr₁])
    (by rw [sv₂ _ (by decide), hsp₁])
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  refine WP.seq (WP.mono (blk_call v.encOk v.encNosp v.encDepth B₃) fun s₄ P₄ => ?_)
  -- The registers back.
  have h12₄ : s₄.gpr .r12 = S := by rw [P₄.saved _ (by decide), g₃ _ (by decide), sv₂ _ (by decide), r12₁]
  have rS : ∀ {d : Nat}, d + 8 ≤ 2560 → InRegions (s₄.rd ++ s₄.wr) (S + BitVec.ofNat 64 d) 8 := fun h => by
    rw [P₄.rd, P₄.wr, rd₃, wr₃, P₂.rd, P₂.wr, rd₁, wr₁]; exact Proof.AesCcm.X86_64.in_left (inS h)
  -- What the code after the first block keeps of the save area.
  have dS : ∀ {d k : Nat}, d + k ≤ 2560 → 512 ≤ d → (⟨S, 24⟩ : Region).Disjoint ⟨S + BitVec.ofNat 64 d, k⟩ :=
    fun h₁ h₂ => Offset.base_disjoint S (by omega) (by omega)
  have dSC : ∀ {d k : Nat}, d + k ≤ 256 → (⟨S, 24⟩ : Region).Disjoint ⟨C + BitVec.ofNat 64 d, k⟩ :=
    fun h => (Ar.cs.symm.sub_left (Region.sub_prefix (by decide))).sub_right (sub_C h)
  have dSs : (⟨S, 24⟩ : Region).Disjoint (below (s.gpr .rsp) 8) :=
    (Ar.stkS.sub_right (Region.sub_prefix (by decide))).symm
  have keep : ∀ {d : Nat}, d + 8 ≤ 24 →
      s₄.mem.readW (S + BitVec.ofNat 64 d) 64 = s₁.mem.readW (S + BitVec.ofNat 64 d) 64 := fun {d} hd => by
    have hc : (⟨S, 24⟩ : Region).Contains (S + BitVec.ofNat 64 d) (64 / 8) :=
      Offset.contains_base _ hd (by have := Ar.wS; omega)
    rw [P₄.frame.readW hc (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact dSC (by decide)
        · exact dS (by decide) (by decide)
        · rw [hsp₃]; exact dSs) (by decide),
      m₃, readW_writeW_off' hc (dSC (d := 248) (k := 8) (by decide)),
      readW_writeW_off' hc (dSC (d := 240) (k := 8) (by decide)),
      P₂.frame.readW hc (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · simpa using dSC (d := 0) (k := 240) (by decide)
        · exact dS (by decide) (by decide)
        · rw [hsp₁]; exact dSs) (by decide)]
  have sp : ∀ (a b : Nat), a + 8 ≤ b ∨ b + 8 ≤ a → a + 8 ≤ 2560 → b + 8 ≤ 2560 →
      Mem.Sep (S + BitVec.ofNat 64 a) (64 / 8) (S + BitVec.ofNat 64 b) (64 / 8) := fun a b h ha hb =>
    Offset.sep S h (by omega) (by omega)
  have v0 : s₄.mem.readW (S + BitVec.ofNat 64 0) 64 = s.gpr .rbx := by
    rw [keep (by decide), m₁, Mem.readW_writeW_sep (sp 0 16 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sp 0 8 (by omega) (by omega) (by omega)) (by decide), Mem.readW_writeW_self64]
  have v8 : s₄.mem.readW (S + BitVec.ofNat 64 8) 64 = s.gpr .rbp := by
    rw [keep (by decide), m₁, Mem.readW_writeW_sep (sp 8 16 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]
  have v16 : s₄.mem.readW (S + BitVec.ofNat 64 16) 64 = s.gpr .r12 := by
    rw [keep (by decide), m₁, Mem.readW_writeW_self64]
  obtain ⟨s₅, run₅, rbx₅, rbp₅, r12₅, g₅, m₅⟩ : ∃ s₅, runBlock isa
      [ld .rbx .r12 0, ld .rbp .r12 8, ld .r12 .r12 16] s₄ = some s₅ ∧
      s₅.gpr .rbx = s.gpr .rbx ∧ s₅.gpr .rbp = s.gpr .rbp ∧ s₅.gpr .r12 = s.gpr .r12 ∧
      (∀ r, r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → s₅.gpr r = s₄.gpr r) ∧ s₅.mem = s₄.mem := by
    refine ⟨_, by orun [h12₄, rS (d := 0) (by decide), rS (d := 8) (by decide), rS (d := 16) (by decide), v0, v8,
      v16], ?_, ?_, ?_, fun r h₁ h₂ h₃ => ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, h₁, h₂, h₃, ite_false]
    · rfl
  refine WP.of_runBlock ⟨s₅, run₅, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · have hr' := hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rbx₅
    · exact rbp₅
    · rw [g₅ _ (by decide) (by decide) (by decide), P₄.saved _ hr, g₃ _ hr, sv₂ _ hr, hsp₁]
    · exact r12₅
    all_goals rw [g₅ _ (by decide) (by decide) (by decide), P₄.saved _ hr, g₃ _ hr, sv₂ _ hr,
      g₁ _ (by decide) (by decide) (by decide) (by decide)]
  · -- The return address.
    have f₃ : Frame [⟨C + BitVec.ofNat 64 240, 16⟩] s₂.mem s₃.mem := by
      rw [m₃, show C + BitVec.ofNat 64 248 = C + BitVec.ofNat 64 240 + BitVec.ofNat 64 8 from (addr8 C 240).symm]
      exact frame_store2 _ _ _ _
    have fall : Frame [⟨C, 256⟩, ⟨S, 2560⟩, below (s.gpr .rsp) 8] s.mem s₄.mem := by
      refine (((f₁.sub fun r hr => ?_).trans (P₂.frame.sub fun r hr => ?_)).trans (f₃.sub fun r hr => ?_)).trans
        (P₄.frame.sub fun r hr => ?_)
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by decide)⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), sub_S (by decide)⟩
        · rw [hsp₁]; exact ⟨_, by simp, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self .., sub_C (by decide)⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self .., sub_C (by decide)⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), sub_S (by decide)⟩
        · rw [hsp₃]; exact ⟨_, by simp, fun _ h => h⟩
    rw [m₅]
    exact fall.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Ar.retC
      · exact Ar.retS
      · exact Offset.base_disjoint_below _ (by have := Ar.sp; omega)) (by decide)
  · -- The key context.
    have hn : 16 * (KL / 4 + 6 + 1) ≤ 240 := by rcases Ar.klen with h | h | h <;> subst h <;> decide
    have k₃ : bytesAt s₃.mem C (16 * (KL / 4 + 6 + 1)) = Spec.Aes.expandKey (bytesAt s.mem Kp KL) := by
      rw [m₃, bytesAt_frame (show Frame [⟨C + BitVec.ofNat 64 240, 16⟩] s₂.mem
          ((s₂.mem.writeW (C + BitVec.ofNat 64 240) 0#64).writeW (C + BitVec.ofNat 64 248) 0#64) by
          rw [show C + BitVec.ofNat 64 248 = C + BitVec.ofNat 64 240 + BitVec.ofNat 64 8 from (addr8 C 240).symm]
          exact frame_store2 _ _ _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Offset.base_disjoint C hn (by decide)) (by omega)]
      have := P₂.out
      rw [bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Ar.ks.sub_right (Region.sub_prefix (by decide)))
        (by omega)] at this
      exact this
    have k₄ : bytesAt s₄.mem C (16 * (KL / 4 + 6 + 1)) = Spec.Aes.expandKey (bytesAt s.mem Kp KL) := by
      rw [bytesAt_frame P₄.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Offset.base_disjoint C hn (by decide)
        · exact (Ar.cs.sub_left (Region.sub_prefix (by omega))).sub_right (sub_S (by decide))
        · rw [hsp₃]; exact (Ar.stkC.sub_right (Region.sub_prefix (by omega))).symm) (by omega), k₃]
    refine ⟨?_, ?_⟩
    · rw [length_bytesAt, m₅]; exact k₄
    · have := P₄.enc (i := 0) (by decide)
      rw [show 16 * 0 = 0 from rfl, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at this
      show blockAtMem s₅.mem (C + BitVec.ofNat 64 240) = _
      rw [m₅, this, k₃, m₃,
        show C + BitVec.ofNat 64 248 = C + BitVec.ofNat 64 240 + BitVec.ofNat 64 8 from (addr8 C 240).symm,
        blockAtMem_store2, Spec.Ocb.aes, length_bytesAt]
      rfl

/-- `vg_aes_ocb_init`. -/
theorem init_wp (v : BlocksImpl) {s : State} (h : initX86_64.pre s) :
    WP isa (init (callees v)) s fun s' => gprPreserved s s' ∧ initX86_64.post s s' :=
  init_wp' v (IArgs.of h) rfl (ofNat_toNat64 _).symm rfl rfl

end VG.Proof.AesOcb.X86_64
