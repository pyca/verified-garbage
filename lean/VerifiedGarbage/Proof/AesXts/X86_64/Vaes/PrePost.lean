import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Step
import VerifiedGarbage.Proof.Aes.X86_64.VaesBlocks.Blocks

/-!
# One-pass XTS-AES on x86-64: the tweaks XORed in, before and after

For one block register `b` and two blocks: `pre1_ok` loads the blocks at
`r11 + d` and XORs in the two tweaks at `r8 + e`; `post1_ok` XORs them in
again and stores the register to `r11 + d`.
-/

namespace VG.Proof.AesXts.X86_64.Vaes

open VG VG.X86_64
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Proof.Aes.X86_64.AesNi (ea_at inRegions_wr)
open VG.Proof.Aes.X86_64.Vaes (load256_lo load256_hi)

theorem pre1_ok (b : XReg) (d e : Nat) (s : State)
    (hd : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofInt 64 (d : Int)) 32)
    (he : InRegions (s.rd ++ s.wr) (s.gpr .r8 + BitVec.ofInt 64 (e : Int)) 32) :
    WP isa (.block [.vmovdquLoad .l256 b (at_ .r11 d), .vbinLoad .vpxor .l256 b b (at_ .r8 e)]) s fun s' =>
      s'.lane b 0 = s.mem.readW (s.gpr .r11 + BitVec.ofInt 64 (d : Int)) 128 ^^^
        s.mem.readW (s.gpr .r8 + BitVec.ofInt 64 (e : Int)) 128 ∧
      s'.lane b 1 = s.mem.readW (s.gpr .r11 + BitVec.ofInt 64 (d : Int) + BitVec.ofNat 64 16) 128 ^^^
        s.mem.readW (s.gpr .r8 + BitVec.ofInt 64 (e : Int) + BitVec.ofNat 64 16) 128 ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ b → ∀ l < 2, s'.lane r l = s.lane r l) := by
  let v := s.mem.readW (s.gpr .r11 + BitVec.ofInt 64 (d : Int)) 256
  let u := s.mem.readW (s.gpr .r8 + BitVec.ofInt 64 (e : Int)) 256
  let s₁ := s.setV .l256 b (v.extractLsb' 0 128) (v.extractLsb' 128 128)
  rw [WP.block_cons_iff]
  refine ⟨s₁, by simp only [isa, exec, State.load256, ea_at, hd, ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨s₁.setV .l256 b (VBinOp.vpxor.sse.eval (s₁.lane b 0) (u.extractLsb' 0 128))
      (VBinOp.vpxor.sse.eval (s₁.lane b 1) (u.extractLsb' 128 128)), by
    simp only [isa, exec, State.load256, ea_at, s₁, State.setV_gpr, State.setV_mem, State.setV_rd, State.setV_wr,
      he, ite_true, Option.map_some]; rfl, WP.block_nil ?_⟩
  refine ⟨?_, ?_, by simp [s₁], by simp [s₁], by simp [s₁], by simp [s₁], fun r hr l _ => by
    simp [s₁, State.lane_setV256, hr]⟩
  · simp [s₁, State.lane_setV256, v, u, load256_lo, VBinOp.sse]; rfl
  · simp [s₁, State.lane_setV256, v, u, load256_hi, VBinOp.sse]; rfl

theorem post1_ok (b : XReg) (d e : Nat) (s : State)
    (hd : InRegions s.wr (s.gpr .r11 + BitVec.ofInt 64 (d : Int)) 32)
    (he : InRegions (s.rd ++ s.wr) (s.gpr .r8 + BitVec.ofInt 64 (e : Int)) 32) :
    WP isa (.block [.vbinLoad .vpxor .l256 b b (at_ .r8 e), .vmovdquStore .l256 (at_ .r11 d) b]) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .r11 + BitVec.ofInt 64 (d : Int))
        ((s.lane b 1 ^^^ s.mem.readW (s.gpr .r8 + BitVec.ofInt 64 (e : Int) + BitVec.ofNat 64 16) 128) ++
          (s.lane b 0 ^^^ s.mem.readW (s.gpr .r8 + BitVec.ofInt 64 (e : Int)) 128)) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ b → ∀ l < 2, s'.lane r l = s.lane r l) := by
  let u := s.mem.readW (s.gpr .r8 + BitVec.ofInt 64 (e : Int)) 256
  let s₁ := s.setV .l256 b (VBinOp.vpxor.sse.eval (s.lane b 0) (u.extractLsb' 0 128))
      (VBinOp.vpxor.sse.eval (s.lane b 1) (u.extractLsb' 128 128))
  rw [WP.block_cons_iff]
  refine ⟨s₁, by simp only [isa, exec, State.load256, ea_at, he, ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨s₁.setMem (s.mem.writeW (s.gpr .r11 + BitVec.ofInt 64 (d : Int)) (s₁.ymm b)), by
    simp only [isa, exec, State.store256_eq, ea_at, s₁, State.setV_gpr, State.setV_mem, State.setV_wr, hd,
      ite_true], WP.block_nil ?_⟩
  refine ⟨?_, by simp [s₁], by simp [s₁], by simp [s₁], fun r hr l _ => by simp [s₁, State.lane_setV256, hr]⟩
  simp only [State.setMem_mem, State.ymm_eq]
  refine congrArg _ ?_
  simp [s₁, State.lane_setV256, u, load256_lo, load256_hi, VBinOp.sse]
  rfl

/-- Lane `l` of the 32 bytes at `p + o`. -/
theorem addr2 (p : Addr) (o l : Nat) (hl : l < 2) :
    p + BitVec.ofNat 64 (o + 16 * l) =
      if l = 0 then p + BitVec.ofInt 64 (o : Int) else p + BitVec.ofInt 64 (o : Int) + BitVec.ofNat 64 16 := by
  rw [Aes.X86_64.AesNi.ofInt_natCast]
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · simp
  · simp only [Nat.one_ne_zero, ite_false, Nat.mul_one]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]

open VG.Impl.AesXts.X86_64Vaes (preXor postXor bufOff)

theorem preList_ok (regs : List XReg) (j : Nat) (s : State) (hnd : regs.Nodup)
    (hd : ∀ k < regs.length, InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofInt 64 ((32 * (j + k) : Nat) : Int)) 32)
    (he : ∀ k < regs.length,
      InRegions (s.rd ++ s.wr) (s.gpr .r8 + BitVec.ofInt 64 ((bufOff + 32 * (j + k) : Nat) : Int)) 32) :
    WP isa (.block (preXor regs j)) s fun s' =>
      (∀ k (h : k < regs.length), ∀ l < 2, s'.lane regs[k] l =
        s.mem.readW (s.gpr .r11 + BitVec.ofNat 64 (32 * (j + k) + 16 * l)) 128 ^^^
          s.mem.readW (s.gpr .r8 + BitVec.ofNat 64 (bufOff + 32 * (j + k) + 16 * l)) 128) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ regs → ∀ l < 2, s'.lane r l = s.lane r l) := by
  induction regs generalizing j s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩
  | cons b bs ih =>
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    simp only [List.length_cons] at hd he
    rw [preXor, WP.block_append_iff]
    have hd0 := hd 0 (by omega)
    have he0 := he 0 (by omega)
    rw [Nat.add_zero] at hd0 he0
    refine WP.mono (pre1_ok b (32 * j) (bufOff + 32 * j) s hd0 he0)
      fun s₁ ⟨lo₁, hi₁, g₁, m₁, rd₁, wr₁, o₁⟩ => ?_
    refine WP.mono (ih (j + 1) s₁ (List.nodup_cons.mp hnd).2
        (fun k hk => by rw [rd₁, wr₁, g₁, show j + 1 + k = j + (k + 1) by omega]; exact hd (k + 1) (by omega))
        (fun k hk => by rw [rd₁, wr₁, g₁, show j + 1 + k = j + (k + 1) by omega]; exact he (k + 1) (by omega)))
      fun s' ⟨hb, g, m, rd, wr, hx⟩ => ?_
    rw [g₁, m₁] at hb
    refine ⟨fun k hk l hl => ?_, g.trans g₁, m.trans m₁, rd.trans rd₁, wr.trans wr₁, fun r hr l hl => ?_⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [hx b hbs l hl, addr2 _ _ _ hl, show bufOff + 32 * j + 16 * l = bufOff + 32 * j + 16 * l from rfl,
          addr2 _ _ _ hl]
        rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · simp only [ite_true]; rw [lo₁]
        · simp only [Nat.one_ne_zero, ite_false]; rw [hi₁]
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [hb k (by simpa using hk) l hl, show j + 1 + k = j + (k + 1) by omega]
    · simp only [List.mem_cons, not_or] at hr
      rw [hx r hr.2 l hl, o₁ r hr.1 l hl]

theorem readW_write_lo (m : Mem) (a : Addr) (lo hi : BitVec 128) : (m.writeW a (hi ++ lo)).readW a 128 = lo := by
  have e := readW_writeW_inside m a (hi ++ lo) (k := 0) (n := 16) (by decide) (by decide)
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.reduceMul] at e
  rw [e, Aes.X86_64.Vaes.extract_lo]

theorem readW_write_hi (m : Mem) (a : Addr) (lo hi : BitVec 128) :
    (m.writeW a (hi ++ lo)).readW (a + BitVec.ofNat 64 16) 128 = hi := by
  have e := readW_writeW_inside m a (hi ++ lo) (k := 16) (n := 16) (by decide) (by decide)
  simp only [Nat.reduceMul] at e
  rw [e, Aes.X86_64.Vaes.extract_hi]

theorem postList_ok (regs : List XReg) (j : Nat) (s : State) (hnd : regs.Nodup)
    (hd : ∀ k < regs.length, InRegions s.wr (s.gpr .r11 + BitVec.ofInt 64 ((32 * (j + k) : Nat) : Int)) 32)
    (he : ∀ k < regs.length,
      InRegions (s.rd ++ s.wr) (s.gpr .r8 + BitVec.ofInt 64 ((bufOff + 32 * (j + k) : Nat) : Int)) 32)
    (hw : (s.gpr .r11).toNat + 32 * (j + regs.length) ≤ 2 ^ 64)
    (hsep : ∀ k < regs.length, ∀ l < 2,
      Region.Disjoint ⟨s.gpr .r8 + BitVec.ofNat 64 (bufOff + 32 * (j + k) + 16 * l), 16⟩
        ⟨s.gpr .r11 + BitVec.ofNat 64 (32 * j), 32 * regs.length⟩) :
    WP isa (.block (postXor regs j)) s fun s' =>
      (∀ k (h : k < regs.length), ∀ l < 2,
        s'.mem.readW (s.gpr .r11 + BitVec.ofNat 64 (32 * (j + k) + 16 * l)) 128 =
          s.lane regs[k] l ^^^ s.mem.readW (s.gpr .r8 + BitVec.ofNat 64 (bufOff + 32 * (j + k) + 16 * l)) 128) ∧
      Frame [⟨s.gpr .r11 + BitVec.ofNat 64 (32 * j), 32 * regs.length⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ regs → ∀ l < 2, s'.lane r l = s.lane r l) := by
  induction regs generalizing j s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), Frame.refl _ _, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩
  | cons b bs ih =>
    simp only [List.length_cons] at hd he hw hsep
    rw [postXor, WP.block_append_iff]
    have hd0 := hd 0 (by omega)
    have he0 := he 0 (by omega)
    rw [Nat.add_zero] at hd0 he0
    refine WP.mono (post1_ok b (32 * j) (bufOff + 32 * j) s hd0 he0) fun s₁ ⟨m₁, g₁, rd₁, wr₁, x₁⟩ => ?_
    have h11 : s₁.gpr .r11 = s.gpr .r11 := by rw [g₁]
    have h8 : s₁.gpr .r8 = s.gpr .r8 := by rw [g₁]
    rw [Aes.X86_64.AesNi.ofInt_natCast] at m₁
    -- The block written is not where the later tweaks are.
    have hblk : Frame [⟨s.gpr .r11 + BitVec.ofNat 64 (32 * j), 32⟩] s.mem s₁.mem := by
      rw [m₁]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by
        simp only [Region.Contains, BitVec.sub_self]; simp)
    have hslot : ∀ k < bs.length, ∀ l < 2,
        s₁.mem.readW (s.gpr .r8 + BitVec.ofNat 64 (bufOff + 32 * (j + 1 + k) + 16 * l)) 128 =
          s.mem.readW (s.gpr .r8 + BitVec.ofNat 64 (bufOff + 32 * (j + 1 + k) + 16 * l)) 128 := by
      intro k hk l hl
      refine hblk.readW (r := ⟨_, 16⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      have := hsep (k + 1) (by omega) l hl
      rw [show j + (k + 1) = j + 1 + k by omega] at this
      exact this.sub_right (Region.sub_prefix (by omega))
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    refine WP.mono (ih (j + 1) s₁ (List.nodup_cons.mp hnd).2 (fun k hk => by
        rw [wr₁, h11, show j + 1 + k = j + (k + 1) by omega]; exact hd (k + 1) (by omega))
      (fun k hk => by
        rw [rd₁, wr₁, h8, show j + 1 + k = j + (k + 1) by omega]; exact he (k + 1) (by omega))
      (by rw [h11]; omega)
      (fun k hk l hl => by
        rw [h8, h11]
        have := hsep (k + 1) (by omega) l hl
        rw [show j + (k + 1) = j + 1 + k by omega] at this
        refine this.sub_right ?_
        intro a ha
        simp only [Region.Contains] at ha ⊢
        rw [Aes.X86_64.AesNi.off_toNat _ _ (by omega)] at ha ⊢
        have := (a - s.gpr .r11).isLt
        omega)) fun s' ⟨hb, hf, g, rd, wr, xs⟩ => ?_
    rw [h11, h8] at hb
    rw [h11] at hf
    -- Block `j` is not in the rest's frame.
    have hdj : ∀ l < 2, ∀ r ∈ [(⟨s.gpr .r11 + BitVec.ofNat 64 (32 * (j + 1)), 32 * bs.length⟩ : Region)],
        Region.Disjoint ⟨s.gpr .r11 + BitVec.ofNat 64 (32 * j + 16 * l), 16⟩ r := by
      intro l hl
      simp only [List.mem_singleton, forall_eq]
      intro a h₁ h₂
      simp only [Region.Contains] at h₁ h₂
      rw [Aes.X86_64.AesNi.off_toNat _ _ (by omega)] at h₁ h₂
      have := (a - s.gpr .r11).isLt
      omega
    refine ⟨fun k hk l hl => ?_, ?_, g.trans g₁, rd.trans rd₁, wr.trans wr₁, fun r hr l hl => ?_⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [hf.readW (Region.contains_self _ _) (hdj l hl) (by decide), m₁, addr2 _ _ _ hl, addr2 _ _ _ hl,
          Aes.X86_64.AesNi.ofInt_natCast, Aes.X86_64.AesNi.ofInt_natCast]
        rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · simp only [ite_true]; rw [readW_write_lo]
        · simp only [Nat.one_ne_zero, ite_false]; rw [readW_write_hi]
      | succ k =>
        simp only [List.getElem_cons_succ]
        have hk' : k < bs.length := by simpa using hk
        have hne : bs[k] ≠ b := fun h => hbs (h ▸ List.getElem_mem hk')
        rw [show j + (k + 1) = j + 1 + k by omega, hb k hk' l hl, x₁ _ hne l hl, hslot k hk' l hl]
    · rw [m₁] at hf
      refine (Frame.writeW (Frame.refl [⟨s.gpr .r11 + BitVec.ofNat 64 (32 * j), 32 * (bs.length + 1)⟩]
        s.mem) List.mem_cons_self _ (by simp only [Region.Contains, BitVec.sub_self]; simp; omega)).trans
        (hf.sub fun r hr => ⟨_, List.mem_cons_self, fun a ha => ?_⟩)
      simp only [List.mem_singleton] at hr
      subst hr
      simp only [Region.Contains] at ha ⊢
      rw [Aes.X86_64.AesNi.off_toNat _ _ (by omega)] at ha ⊢
      have := (a - s.gpr .r11).isLt
      omega
    · simp only [List.mem_cons, not_or] at hr
      rw [xs r hr.2 l hl, x₁ r hr.1 l hl]

open VG.Impl.AesXts.X86_64Vaes (stepT)

/-- The first `n` pairs of tweaks times `α¹⁶`. -/
theorem stepsN_ok (s : State) (hK : ∀ l < 2, qword (s.lane .xmm11 l) 0 = 0x87)
    (hin : ∀ k < 8, InRegions s.wr (s.gpr .r8 + BitVec.ofInt 64 ((bufOff + 32 * k : Nat) : Int)) 32)
    (hw : (s.gpr .r8).toNat + bufOff + 256 ≤ 2 ^ 64) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap stepT)) s fun s' =>
      (∀ j < 16, s'.mem.readW (s.gpr .r8 + BitVec.ofNat 64 (bufOff + 16 * j)) 128 =
        if j < 2 * n then stepW (s.mem.readW (s.gpr .r8 + BitVec.ofNat 64 (bufOff + 16 * j)) 128)
        else s.mem.readW (s.gpr .r8 + BitVec.ofNat 64 (bufOff + 16 * j)) 128) ∧
      Frame [⟨s.gpr .r8 + BitVec.ofNat 64 bufOff, 256⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .xmm9 → r ≠ .xmm10 → ∀ l < 2, s'.lane r l = s.lane r l)
  | 0, _ => WP.block_nil ⟨fun j _ => by simp, Frame.refl _ _, rfl, rfl, rfl, fun _ _ _ _ _ => rfl⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (stepsN_ok s hK hin hw n (by omega)) fun s₁ ⟨v₁, f₁, g₁, rd₁, wr₁, x₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have hK₁ : ∀ l < 2, qword (s₁.lane .xmm11 l) 0 = 0x87 := fun l hl => by
      rw [x₁ _ (by decide) (by decide) l hl]; exact hK l hl
    refine WP.mono (stepT_ok n s₁ hK₁ (by rw [g₁, wr₁]; exact hin n (by omega)))
      fun s' ⟨m', g', rd', wr', x'⟩ => ?_
    rw [g₁, Aes.X86_64.AesNi.ofInt_natCast] at m'
    have hb : bufOff = 256 := rfl
    have e0 : s.gpr .r8 + BitVec.ofNat 64 (bufOff + 16 * (2 * n)) = s.gpr .r8 + BitVec.ofNat 64 (bufOff + 32 * n) := by
      congr 2; omega
    have e1 : s.gpr .r8 + BitVec.ofNat 64 (bufOff + 16 * (2 * n + 1)) =
        s.gpr .r8 + BitVec.ofNat 64 (bufOff + 32 * n) + BitVec.ofNat 64 16 := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
    refine ⟨fun j hj => ?_, ?_, g'.trans g₁, rd'.trans rd₁, wr'.trans wr₁,
      fun r h1 h2 l hl => (x' r h1 h2 l hl).trans (x₁ r h1 h2 l hl)⟩
    · rw [m']
      by_cases hj2 : j = 2 * n
      · subst hj2
        rw [e0, readW_write_lo, ← e0, v₁ _ hj]
        simp only [show ¬ 2 * n < 2 * n by omega, ite_false, show 2 * n < 2 * (n + 1) by omega, ite_true]
      · by_cases hj3 : j = 2 * n + 1
        · subst hj3
          rw [e1, readW_write_hi, ← e1, v₁ _ hj]
          simp only [show ¬ 2 * n + 1 < 2 * n by omega, ite_false, show 2 * n + 1 < 2 * (n + 1) by omega, ite_true]
        · rw [Mem.readW_writeW_sep ?_ (by decide), v₁ j hj]
          · by_cases hlt : j < 2 * n
            · simp only [hlt, ite_true, show j < 2 * (n + 1) by omega]
            · simp only [hlt, ite_false, show ¬ j < 2 * (n + 1) by omega]
          · have := Offset.sep (s.gpr .r8) (d := bufOff + 16 * j) (n := 16) (e := bufOff + 32 * n) (k := 32)
              (by omega) (by omega) (by rw [hb]; omega)
            simpa using this
    · rw [m']
      refine f₁.trans ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_)
      rw [show s.gpr .r8 + BitVec.ofNat 64 (bufOff + 32 * n) = s.gpr .r8 + BitVec.ofNat 64 bufOff + BitVec.ofNat 64 (32 * n)
        by rw [BitVec.add_assoc, ← BitVec.ofNat_add]]
      exact Offset.contains_base _ (d := 32 * n) (n := 32) (k := 256) (by omega) (by omega)

end VG.Proof.AesXts.X86_64.Vaes
