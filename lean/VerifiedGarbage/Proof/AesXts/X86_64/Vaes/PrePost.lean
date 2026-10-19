module

public import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Step
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Ctr32
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.AesXts.X86_64.Steps
import VerifiedGarbage.Proof.Framework.X86_64.Call

/-!
# One-pass XTS-AES on x86-64: the tweaks XORed in, before and after

For one block register `b`, its tweak register `t` and two blocks:
`pre1_ok` loads the blocks at `r11 + d` and XORs in the tweaks; `post1_ok`
XORs them in again and stores the register to `r11 + d`. `stepsN_ok`: every
tweak register times `α⁸`; `ldT_ok` and `stT_ok`: the tweak registers from
and to the buffer at `scratch + 256`.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.Vaes

open VG VG.X86_64
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Proof.Aes.X86_64.AesNi (ea_at inRegions_wr ofInt_natCast)
open VG.Proof.Aes.X86_64.Vaes (load256_lo load256_hi)

theorem pre1_ok (b t : XReg) (hbt : t ≠ b) (d : Nat) (s : State)
    (hd : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofInt 64 (d : Int)) 32) :
    WP isa (.block [.vmovdquLoad .l256 b (at_ .r11 d), .vop (.vbin .vpxor .l256 b b t)]) s fun s' =>
      s'.lane b 0 = s.mem.readW (s.gpr .r11 + BitVec.ofInt 64 (d : Int)) 128 ^^^ s.lane t 0 ∧
      s'.lane b 1 = s.mem.readW (s.gpr .r11 + BitVec.ofInt 64 (d : Int) + BitVec.ofNat 64 16) 128 ^^^ s.lane t 1 ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ b → ∀ l < 2, s'.lane r l = s.lane r l) := by
  let v := s.mem.readW (s.gpr .r11 + BitVec.ofInt 64 (d : Int)) 256
  let s₁ := s.setV .l256 b (v.extractLsb' 0 128) (v.extractLsb' 128 128)
  rw [WP.block_cons_iff]
  refine ⟨s₁, by simp only [isa, exec, State.load256, ea_at, hd, ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨(VOp.vbin .vpxor .l256 b b t).exec s₁, rfl, WP.block_nil ?_⟩
  refine ⟨?_, ?_, by simp [s₁], by simp [s₁], by simp [s₁], by simp [s₁], fun r hr l _ => by
    simp [s₁, State.lane_setV256, hr]⟩
  · simp [s₁, State.lane_setV256, v, load256_lo, VBinOp.sse, hbt]; rfl
  · simp [s₁, State.lane_setV256, v, load256_hi, VBinOp.sse, hbt]; rfl

theorem post1_ok (b t : XReg) (d : Nat) (s : State)
    (hd : InRegions s.wr (s.gpr .r11 + BitVec.ofInt 64 (d : Int)) 32) :
    WP isa (.block [.vop (.vbin .vpxor .l256 b b t), .vmovdquStore .l256 (at_ .r11 d) b]) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .r11 + BitVec.ofInt 64 (d : Int))
        ((s.lane b 1 ^^^ s.lane t 1) ++ (s.lane b 0 ^^^ s.lane t 0)) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ b → ∀ l < 2, s'.lane r l = s.lane r l) := by
  let s₁ := (VOp.vbin .vpxor .l256 b b t).exec s
  rw [WP.block_cons_iff]
  refine ⟨s₁, rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨s₁.setMem (s.mem.writeW (s.gpr .r11 + BitVec.ofInt 64 (d : Int)) (s₁.ymm b)), by
    simp only [isa, exec, State.store256_eq, ea_at, s₁, VOp.exec_gpr, VOp.exec_mem, VOp.exec_wr, hd,
      ite_true], WP.block_nil ?_⟩
  refine ⟨?_, by simp [s₁], by simp [s₁], by simp [s₁], fun r hr l _ => by simp [s₁, hr]⟩
  simp only [State.setMem_mem, State.ymm_eq]
  refine congrArg _ ?_
  simp [s₁, VBinOp.sse]
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

theorem preList_ok (regs ts : List XReg) (j : Nat) (s : State) (hnd : regs.Nodup) (hlen : ts.length = regs.length)
    (hdis : ∀ t ∈ ts, t ∉ regs)
    (hd : ∀ k < regs.length, InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofInt 64 ((32 * (j + k) : Nat) : Int)) 32) :
    WP isa (.block (preXor regs ts j)) s fun s' =>
      (∀ k (h : k < regs.length), ∀ l < 2, s'.lane regs[k] l =
        s.mem.readW (s.gpr .r11 + BitVec.ofNat 64 (32 * (j + k) + 16 * l)) 128 ^^^ s.lane (ts[k]'(by omega)) l) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ regs → ∀ l < 2, s'.lane r l = s.lane r l) := by
  induction regs generalizing ts j s with
  | nil =>
    cases ts with
    | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩
    | cons _ _ => simp at hlen
  | cons b bs ih =>
    cases ts with
    | nil => simp at hlen
    | cons t ts =>
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    simp only [List.length_cons] at hd hlen
    have htb : t ≠ b := fun h => hdis t List.mem_cons_self (h ▸ List.mem_cons_self)
    rw [preXor, WP.block_append_iff]
    have hd0 := hd 0 (by omega)
    rw [Nat.add_zero] at hd0
    refine WP.mono (pre1_ok b t htb (32 * j) s hd0) fun s₁ ⟨lo₁, hi₁, g₁, m₁, rd₁, wr₁, o₁⟩ => ?_
    refine WP.mono (ih ts (j + 1) s₁ (List.nodup_cons.mp hnd).2 (by omega)
        (fun t' ht' hb => hdis t' (List.mem_cons_of_mem _ ht') (List.mem_cons_of_mem _ hb))
        (fun k hk => by rw [rd₁, wr₁, g₁, show j + 1 + k = j + (k + 1) by omega]; exact hd (k + 1) (by omega)))
      fun s' ⟨hb, g, m, rd, wr, hx⟩ => ?_
    rw [g₁, m₁] at hb
    refine ⟨fun k hk l hl => ?_, g.trans g₁, m.trans m₁, rd.trans rd₁, wr.trans wr₁, fun r hr l hl => ?_⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [hx b hbs l hl, addr2 _ _ _ hl]
        rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · simp only [ite_true]; rw [lo₁]
        · simp only [Nat.one_ne_zero, ite_false]; rw [hi₁]
      | succ k =>
        simp only [List.getElem_cons_succ]
        have hk' : k < bs.length := by simpa using hk
        have hkt' : k < ts.length := by omega
        have hkt : ts[k] ≠ b := fun h =>
          hdis _ (List.mem_cons_of_mem _ (List.getElem_mem hkt')) (by rw [h]; exact List.mem_cons_self)
        rw [hb k hk' l hl, show j + 1 + k = j + (k + 1) by omega, o₁ _ hkt l hl]
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

theorem postList_ok (regs ts : List XReg) (j : Nat) (s : State) (hnd : regs.Nodup) (hlen : ts.length = regs.length)
    (hdis : ∀ t ∈ ts, t ∉ regs)
    (hd : ∀ k < regs.length, InRegions s.wr (s.gpr .r11 + BitVec.ofInt 64 ((32 * (j + k) : Nat) : Int)) 32)
    (hw : (s.gpr .r11).toNat + 32 * (j + regs.length) ≤ 2 ^ 64) :
    WP isa (.block (postXor regs ts j)) s fun s' =>
      (∀ k (h : k < regs.length), ∀ l < 2,
        s'.mem.readW (s.gpr .r11 + BitVec.ofNat 64 (32 * (j + k) + 16 * l)) 128 =
          s.lane regs[k] l ^^^ s.lane (ts[k]'(by omega)) l) ∧
      Frame [⟨s.gpr .r11 + BitVec.ofNat 64 (32 * j), 32 * regs.length⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ regs → ∀ l < 2, s'.lane r l = s.lane r l) := by
  induction regs generalizing ts j s with
  | nil =>
    cases ts with
    | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), Frame.refl _ _, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩
    | cons _ _ => simp at hlen
  | cons b bs ih =>
    cases ts with
    | nil => simp at hlen
    | cons t ts =>
    simp only [List.length_cons] at hd hw hlen
    rw [postXor, WP.block_append_iff]
    have hd0 := hd 0 (by omega)
    rw [Nat.add_zero] at hd0
    refine WP.mono (post1_ok b t (32 * j) s hd0) fun s₁ ⟨m₁, g₁, rd₁, wr₁, x₁⟩ => ?_
    have h11 : s₁.gpr .r11 = s.gpr .r11 := by rw [g₁]
    rw [Aes.X86_64.AesNi.ofInt_natCast] at m₁
    -- The block written is not where the later tweaks are.
    have hblk : Frame [⟨s.gpr .r11 + BitVec.ofNat 64 (32 * j), 32⟩] s.mem s₁.mem := by
      rw [m₁]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by
        simp only [Region.Contains, BitVec.sub_self]; simp)
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    have htb : ∀ t' ∈ t :: ts, t' ≠ b := fun t' ht' h => hdis t' ht' (h ▸ List.mem_cons_self)
    refine WP.mono (ih ts (j + 1) s₁ (List.nodup_cons.mp hnd).2 (by omega)
      (fun t' ht' hb => hdis t' (List.mem_cons_of_mem _ ht') (List.mem_cons_of_mem _ hb))
      (fun k hk => by
        rw [wr₁, h11, show j + 1 + k = j + (k + 1) by omega]; exact hd (k + 1) (by omega))
      (by rw [h11]; omega)) fun s' ⟨hb, hf, g, rd, wr, xs⟩ => ?_
    rw [h11] at hb
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
        rw [hf.readW (Region.contains_self _ _) (hdj l hl) (by decide), m₁, addr2 _ _ _ hl,
          Aes.X86_64.AesNi.ofInt_natCast]
        rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · simp only [ite_true]; rw [readW_write_lo]
        · simp only [Nat.one_ne_zero, ite_false]; rw [readW_write_hi]
      | succ k =>
        simp only [List.getElem_cons_succ]
        have hk' : k < bs.length := by simpa using hk
        have hne : bs[k] ≠ b := fun h => hbs (h ▸ List.getElem_mem hk')
        have hkt' : k < ts.length := by omega
        have hkt : ts[k] ≠ b := htb _ (List.mem_cons_of_mem _ (List.getElem_mem hkt'))
        rw [show j + (k + 1) = j + 1 + k by omega, hb k hk' l hl, x₁ _ hne l hl, x₁ _ hkt l hl]
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

open VG.Impl.AesXts.X86_64Vaes (stepT ldT stT)

/-- Every tweak register in `ts` times `α⁸`. -/
theorem stepsN_ok (ts : List XReg) (hnd : ts.Nodup) (h10 : XReg.xmm10 ∉ ts) (h11 : XReg.xmm11 ∉ ts) (s : State)
    (hK : ∀ l < 2, qword (s.lane .xmm11 l) 0 = 0x87) :
    WP isa (.block (ts.flatMap stepT)) s fun s' =>
      (∀ t ∈ ts, ∀ l < 2, s'.lane t l = stepW (s.lane t l)) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ ts → r ≠ .xmm10 → ∀ l < 2, s'.lane r l = s.lane r l) := by
  induction ts generalizing s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), rfl, rfl, rfl, rfl, fun _ _ _ _ _ => rfl⟩
  | cons t ts ih =>
    simp only [List.mem_cons, not_or] at h10 h11
    rw [List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (stepT_ok t (Ne.symm h10.1) s hK) fun s₁ ⟨e₁, g₁, m₁, rd₁, wr₁, x₁⟩ => ?_
    have hK₁ : ∀ l < 2, qword (s₁.lane .xmm11 l) 0 = 0x87 := fun l hl => by
      rw [x₁ _ h11.1 (by decide) l hl]; exact hK l hl
    have htn : t ∉ ts := (List.nodup_cons.mp hnd).1
    refine WP.mono (ih (List.nodup_cons.mp hnd).2 h10.2 h11.2 s₁ hK₁) fun s' ⟨e, g, m, rd, wr, x⟩ => ?_
    refine ⟨fun t' ht' l hl => ?_, g.trans g₁, m.trans m₁, rd.trans rd₁, wr.trans wr₁, fun r hr h10' l hl => ?_⟩
    · rcases List.mem_cons.mp ht' with rfl | ht'
      · rw [x _ htn (Ne.symm h10.1) l hl, e₁ l hl]
      · have hne : t' ≠ t := fun h => htn (h ▸ ht')
        rw [e t' ht' l hl, x₁ _ hne (fun h => h10.2 (h ▸ ht')) l hl]
    · simp only [List.mem_cons, not_or] at hr
      rw [x r hr.2 h10' l hl, x₁ r hr.1 h10' l hl]

/-- The tweak registers `ts` from the buffer at `r8 + bufOff + 32 j`. -/
theorem ldT_ok (ts : List XReg) (j : Nat) (s : State) (hnd : ts.Nodup)
    (he : ∀ k < ts.length,
      InRegions (s.rd ++ s.wr) (s.gpr .r8 + BitVec.ofInt 64 ((bufOff + 32 * (j + k) : Nat) : Int)) 32) :
    WP isa (.block (ldT ts j)) s fun s' =>
      (∀ k (h : k < ts.length), ∀ l < 2, s'.lane ts[k] l =
        s.mem.readW (s.gpr .r8 + BitVec.ofNat 64 (bufOff + 32 * (j + k) + 16 * l)) 128) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ ts → ∀ l < 2, s'.lane r l = s.lane r l) := by
  induction ts generalizing j s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩
  | cons t ts ih =>
    have htn : t ∉ ts := (List.nodup_cons.mp hnd).1
    simp only [List.length_cons] at he
    have he0 := he 0 (by omega)
    rw [Nat.add_zero] at he0
    let v := s.mem.readW (s.gpr .r8 + BitVec.ofInt 64 ((bufOff + 32 * j : Nat) : Int)) 256
    let s₁ := s.setV .l256 t (v.extractLsb' 0 128) (v.extractLsb' 128 128)
    rw [ldT, WP.block_cons_iff]
    refine ⟨s₁, by simp only [isa, exec, State.load256, ea_at, he0, ite_true, Option.map_some]; rfl, ?_⟩
    refine WP.mono (ih (j + 1) s₁ (List.nodup_cons.mp hnd).2 (fun k hk => by
        simp only [s₁, State.setV_rd, State.setV_wr, State.setV_gpr]
        rw [show j + 1 + k = j + (k + 1) by omega]; exact he (k + 1) (by omega)))
      fun s' ⟨e, g, m, rd, wr, x⟩ => ?_
    have g₁ : s₁.gpr = s.gpr := by simp [s₁]
    have m₁ : s₁.mem = s.mem := by simp [s₁]
    rw [g₁, m₁] at e
    refine ⟨fun k hk l hl => ?_, by rw [g, g₁], by rw [m, m₁], by rw [rd]; simp [s₁], by rw [wr]; simp [s₁],
      fun r hr l hl => ?_⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [x t htn l hl, State.lane_setV256, addr2 _ _ _ hl]
        simp only [ite_true]
        rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · simp [v, load256_lo]
        · simp [v, load256_hi]
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [e k (by simpa using hk) l hl, show j + 1 + k = j + (k + 1) by omega]
    · simp only [List.mem_cons, not_or] at hr
      rw [x r hr.2 l hl]; simp [s₁, State.lane_setV256, hr.1]

/-- The tweak registers `ts` back to the buffer at `r8 + bufOff + 32 j`. -/
theorem stT_ok (ts : List XReg) (j : Nat) (s : State)
    (he : ∀ k < ts.length,
      InRegions s.wr (s.gpr .r8 + BitVec.ofInt 64 ((bufOff + 32 * (j + k) : Nat) : Int)) 32)
    (hw : (s.gpr .r8).toNat + bufOff + 32 * (j + ts.length) ≤ 2 ^ 64) :
    WP isa (.block (stT ts j)) s fun s' =>
      (∀ k (h : k < ts.length), ∀ l < 2,
        s'.mem.readW (s.gpr .r8 + BitVec.ofNat 64 (bufOff + 32 * (j + k) + 16 * l)) 128 = s.lane ts[k] l) ∧
      Frame [⟨s.gpr .r8 + BitVec.ofNat 64 (bufOff + 32 * j), 32 * ts.length⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r l, s'.lane r l = s.lane r l) := by
  induction ts generalizing j s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), Frame.refl _ _, rfl, rfl, rfl, fun _ _ => rfl⟩
  | cons t ts ih =>
    simp only [List.length_cons] at he hw
    have he0 := he 0 (by omega)
    rw [Nat.add_zero] at he0
    let a := s.gpr .r8 + BitVec.ofInt 64 ((bufOff + 32 * j : Nat) : Int)
    let s₁ := s.setMem (s.mem.writeW a (s.ymm t))
    rw [stT, WP.block_cons_iff]
    refine ⟨s₁, by simp only [isa, exec, State.store256_eq, ea_at, he0, ite_true]; rfl, ?_⟩
    have g₁ : s₁.gpr = s.gpr := rfl
    have hb : bufOff = 256 := rfl
    refine WP.mono (ih (j + 1) s₁ (fun k hk => by
        rw [show j + 1 + k = j + (k + 1) by omega]; exact he (k + 1) (by omega)) (by rw [g₁]; omega))
      fun s' ⟨e, hf, g, rd, wr, x⟩ => ?_
    rw [g₁] at e hf
    have ha : a = s.gpr .r8 + BitVec.ofNat 64 (bufOff + 32 * j) := by simp only [a, ofInt_natCast]
    -- Lane `l` of the register just stored lies below the rest's frame.
    have hdj : ∀ l < 2, ∀ r ∈ [(⟨s.gpr .r8 + BitVec.ofNat 64 (bufOff + 32 * (j + 1)), 32 * ts.length⟩ : Region)],
        Region.Disjoint ⟨s.gpr .r8 + BitVec.ofNat 64 (bufOff + 32 * j + 16 * l), 16⟩ r := by
      intro l hl r hr
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
    refine ⟨fun k hk l hl => ?_, ?_, g, rd, wr, x⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [hf.readW (Region.contains_self _ _) (hdj l hl) (by decide)]
        show (s.mem.writeW a (s.ymm t)).readW _ 128 = _
        rw [State.ymm_eq, addr2 _ _ _ hl]
        rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · simp only [ite_true]; exact readW_write_lo _ _ _ _
        · simp only [Nat.one_ne_zero, ite_false]; exact readW_write_hi _ _ _ _
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [show j + (k + 1) = j + 1 + k by omega]; exact e k (by simpa using hk) l hl
    · refine ((Frame.refl [⟨s.gpr .r8 + BitVec.ofNat 64 (bufOff + 32 * j), 32 * (ts.length + 1)⟩] s.mem).writeW
        List.mem_cons_self _ ?_).trans (hf.sub fun r hr => ⟨_, List.mem_cons_self, ?_⟩)
      · rw [ha]; simp only [Region.Contains, BitVec.sub_self]; simp; omega
      · simp only [List.mem_singleton] at hr; subst hr
        rw [show s.gpr .r8 + BitVec.ofNat 64 (bufOff + 32 * (j + 1)) =
          s.gpr .r8 + BitVec.ofNat 64 (bufOff + 32 * j) + BitVec.ofNat 64 32 by
            rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2]
        exact Offset.sub_base _ (by omega)

end VG.Proof.AesXts.X86_64.Vaes
