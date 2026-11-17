module

public import VerifiedGarbage.Proof.AesCbc.X86_64.Loop
public import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Rounds
public import VerifiedGarbage.Proof.AesCbc.Spec
public import VerifiedGarbage.Proof.AesXts.Alpha16
import VerifiedGarbage.Proof.AesXts.Alpha
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Step
public import VerifiedGarbage.Proof.Framework.X86_64.YFrame
import VerifiedGarbage.Proof.AesCbc.X86_64.Body
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Ctr32
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Taint

/-! ### `AesXts.X86_64.Vaes.PrePost`, which this module and modules that import it used -/

section

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
  rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl
  · simp
  · simp only [Nat.one_ne_zero, ite_false, Nat.mul_one]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]

open VG.Impl.AesXts.X86_64Vaes (preXor postXor bufOff)

theorem preList_ok (regs ts : List XReg) (j : Nat) (s : State) (hnd : regs.Nodup) (hlen : ts.length = regs.length)
    (hdis : ∀ t ∈ ts, t ∉ regs)
    (hd : ∀ k < regs.length, InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofInt 64 ((32 * (j + k) : Nat) : Int)) 32) :
    WP isa (.block (preXor regs ts j)) s fun s' =>
      (∀ k (h : k < regs.length), ∀ l < 2, s'.lane regs[k] l =
        s.mem.readW (s.gpr .r11 + BitVec.ofNat 64 (32 * (j + k) + 16 * l)) 128 ^^^ s.lane (ts[k]'(by omega_arith)) l) ∧
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
    have hd0 := hd 0 (by omega_arith)
    rw [Nat.add_zero] at hd0
    refine WP.mono (pre1_ok b t htb (32 * j) s hd0) fun s₁ ⟨lo₁, hi₁, g₁, m₁, rd₁, wr₁, o₁⟩ => ?_
    refine WP.mono (ih ts (j + 1) s₁ (List.nodup_cons.mp hnd).2 (by omega_arith)
        (fun t' ht' hb => hdis t' (List.mem_cons_of_mem _ ht') (List.mem_cons_of_mem _ hb))
        (fun k hk => by rw [rd₁, wr₁, g₁, show j + 1 + k = j + (k + 1) by omega_arith]; exact hd (k + 1) (by omega_arith)))
      fun s' ⟨hb, g, m, rd, wr, hx⟩ => ?_
    rw [g₁, m₁] at hb
    refine ⟨fun k hk l hl => ?_, g.trans g₁, m.trans m₁, rd.trans rd₁, wr.trans wr₁, fun r hr l hl => ?_⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [hx b hbs l hl, addr2 _ _ _ hl]
        rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl
        · simp only [ite_true]; rw [lo₁]
        · simp only [Nat.one_ne_zero, ite_false]; rw [hi₁]
      | succ k =>
        simp only [List.getElem_cons_succ]
        have hk' : k < bs.length := by simpa using hk
        have hkt' : k < ts.length := by omega_arith
        have hkt : ts[k] ≠ b := fun h =>
          hdis _ (List.mem_cons_of_mem _ (List.getElem_mem hkt')) (by rw [h]; exact List.mem_cons_self)
        rw [hb k hk' l hl, show j + 1 + k = j + (k + 1) by omega_arith, o₁ _ hkt l hl]
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
          s.lane regs[k] l ^^^ s.lane (ts[k]'(by omega_arith)) l) ∧
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
    have hd0 := hd 0 (by omega_arith)
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
    refine WP.mono (ih ts (j + 1) s₁ (List.nodup_cons.mp hnd).2 (by omega_arith)
      (fun t' ht' hb => hdis t' (List.mem_cons_of_mem _ ht') (List.mem_cons_of_mem _ hb))
      (fun k hk => by
        rw [wr₁, h11, show j + 1 + k = j + (k + 1) by omega_arith]; exact hd (k + 1) (by omega_arith))
      (by rw [h11]; omega_arith)) fun s' ⟨hb, hf, g, rd, wr, xs⟩ => ?_
    rw [h11] at hb
    rw [h11] at hf
    -- Block `j` is not in the rest's frame.
    have hdj : ∀ l < 2, ∀ r ∈ [(⟨s.gpr .r11 + BitVec.ofNat 64 (32 * (j + 1)), 32 * bs.length⟩ : Region)],
        Region.Disjoint ⟨s.gpr .r11 + BitVec.ofNat 64 (32 * j + 16 * l), 16⟩ r := by
      intro l hl
      simp only [List.mem_singleton, forall_eq]
      intro a h₁ h₂
      simp only [Region.Contains] at h₁ h₂
      rw [Aes.X86_64.AesNi.off_toNat _ _ (by omega_arith)] at h₁ h₂
      have := (a - s.gpr .r11).isLt
      omega_arith
    refine ⟨fun k hk l hl => ?_, ?_, g.trans g₁, rd.trans rd₁, wr.trans wr₁, fun r hr l hl => ?_⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [hf.readW (Region.contains_self _ _) (hdj l hl) (by decide), m₁, addr2 _ _ _ hl,
          Aes.X86_64.AesNi.ofInt_natCast]
        rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl
        · simp only [ite_true]; rw [readW_write_lo]
        · simp only [Nat.one_ne_zero, ite_false]; rw [readW_write_hi]
      | succ k =>
        simp only [List.getElem_cons_succ]
        have hk' : k < bs.length := by simpa using hk
        have hne : bs[k] ≠ b := fun h => hbs (h ▸ List.getElem_mem hk')
        have hkt' : k < ts.length := by omega_arith
        have hkt : ts[k] ≠ b := htb _ (List.mem_cons_of_mem _ (List.getElem_mem hkt'))
        rw [show j + (k + 1) = j + 1 + k by omega_arith, hb k hk' l hl, x₁ _ hne l hl, x₁ _ hkt l hl]
    · rw [m₁] at hf
      refine (Frame.writeW (Frame.refl [⟨s.gpr .r11 + BitVec.ofNat 64 (32 * j), 32 * (bs.length + 1)⟩]
        s.mem) List.mem_cons_self _ (by simp only [Region.Contains, BitVec.sub_self]; simp; omega_arith)).trans
        (hf.sub fun r hr => ⟨_, List.mem_cons_self, fun a ha => ?_⟩)
      simp only [List.mem_singleton] at hr
      subst hr
      simp only [Region.Contains] at ha ⊢
      rw [Aes.X86_64.AesNi.off_toNat _ _ (by omega_arith)] at ha ⊢
      have := (a - s.gpr .r11).isLt
      omega_arith
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
    have he0 := he 0 (by omega_arith)
    rw [Nat.add_zero] at he0
    let v := s.mem.readW (s.gpr .r8 + BitVec.ofInt 64 ((bufOff + 32 * j : Nat) : Int)) 256
    let s₁ := s.setV .l256 t (v.extractLsb' 0 128) (v.extractLsb' 128 128)
    rw [ldT, WP.block_cons_iff]
    refine ⟨s₁, by simp only [isa, exec, State.load256, ea_at, he0, ite_true, Option.map_some]; rfl, ?_⟩
    refine WP.mono (ih (j + 1) s₁ (List.nodup_cons.mp hnd).2 (fun k hk => by
        simp only [s₁, State.setV_rd, State.setV_wr, State.setV_gpr]
        rw [show j + 1 + k = j + (k + 1) by omega_arith]; exact he (k + 1) (by omega_arith)))
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
        rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl
        · simp [v, load256_lo]
        · simp [v, load256_hi]
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [e k (by simpa using hk) l hl, show j + 1 + k = j + (k + 1) by omega_arith]
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
    have he0 := he 0 (by omega_arith)
    rw [Nat.add_zero] at he0
    let a := s.gpr .r8 + BitVec.ofInt 64 ((bufOff + 32 * j : Nat) : Int)
    let s₁ := s.setMem (s.mem.writeW a (s.ymm t))
    rw [stT, WP.block_cons_iff]
    refine ⟨s₁, by simp only [isa, exec, State.store256_eq, ea_at, he0, ite_true]; rfl, ?_⟩
    have g₁ : s₁.gpr = s.gpr := rfl
    have hb : bufOff = 256 := rfl
    refine WP.mono (ih (j + 1) s₁ (fun k hk => by
        rw [show j + 1 + k = j + (k + 1) by omega_arith]; exact he (k + 1) (by omega_arith)) (by rw [g₁]; omega_arith))
      fun s' ⟨e, hf, g, rd, wr, x⟩ => ?_
    rw [g₁] at e hf
    have ha : a = s.gpr .r8 + BitVec.ofNat 64 (bufOff + 32 * j) := by simp only [a, ofInt_natCast]
    -- Lane `l` of the register just stored lies below the rest's frame.
    have hdj : ∀ l < 2, ∀ r ∈ [(⟨s.gpr .r8 + BitVec.ofNat 64 (bufOff + 32 * (j + 1)), 32 * ts.length⟩ : Region)],
        Region.Disjoint ⟨s.gpr .r8 + BitVec.ofNat 64 (bufOff + 32 * j + 16 * l), 16⟩ r := by
      intro l hl r hr
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
    refine ⟨fun k hk l hl => ?_, ?_, g, rd, wr, x⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [hf.readW (Region.contains_self _ _) (hdj l hl) (by decide)]
        show (s.mem.writeW a (s.ymm t)).readW _ 128 = _
        rw [State.ymm_eq, addr2 _ _ _ hl]
        rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl
        · simp only [ite_true]; exact readW_write_lo _ _ _ _
        · simp only [Nat.one_ne_zero, ite_false]; exact readW_write_hi _ _ _ _
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [show j + (k + 1) = j + 1 + k by omega_arith]; exact e k (by simpa using hk) l hl
    · refine ((Frame.refl [⟨s.gpr .r8 + BitVec.ofNat 64 (bufOff + 32 * j), 32 * (ts.length + 1)⟩] s.mem).writeW
        List.mem_cons_self _ ?_).trans (hf.sub fun r hr => ⟨_, List.mem_cons_self, ?_⟩)
      · rw [ha]; simp only [Region.Contains, BitVec.sub_self]; simp; omega_arith
      · simp only [List.mem_singleton] at hr; subst hr
        rw [show s.gpr .r8 + BitVec.ofNat 64 (bufOff + 32 * (j + 1)) =
          s.gpr .r8 + BitVec.ofNat 64 (bufOff + 32 * j) + BitVec.ofNat 64 32 by
            rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2]
        exact Offset.sub_base _ (by omega_arith)

end VG.Proof.AesXts.X86_64.Vaes

end

end

/-! ### `AesXts.X86_64.Vaes.Common`, which only this module used -/

section

/-!
# One-pass XTS-AES on x86-64: blocks as words

The one-pass functions (`Impl/AesXts/X86_64Vaes.lean`) hold blocks and
tweaks as 128-bit words, in registers and in memory. Their bytes are `b16`
of the word (`bytesAt_b16`, `st_toList`); XOR of words is XOR of their bytes
(`b16_xor`); and the cipher of a register's state is the cipher of its bytes
(`ciphOf_b16`). `xtsWord`: the XTS of a block from its words, as the
functions compute it.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.Vaes

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesXts (b16)
open VG.Proof.Aes.X86_64.AesNi (st)
open VG.Proof.AesCbc (ciphOf)

theorem bytesAt_b16 (m : Mem) (p : Addr) : bytesAt m p 16 = b16 (m.readW p 128) :=
  AesXts.bytesAt_readW (k := 16) m p

theorem b16_xor (a b : BitVec 128) : b16 (a ^^^ b) = Spec.Cbc.xor (b16 a) (b16 b) := by
  apply List.ext_getElem (by simp [b16, Spec.Cbc.xor])
  intro k h₁ h₂
  obtain hk : k < 16 := by simpa [b16] using h₁
  simp only [b16, Spec.Cbc.xor, List.getElem_map, List.getElem_range, List.getElem_zipWith]
  ext j hj
  simp

theorem st_toList (v : BitVec 128) : (st v).toList = b16 v := by
  rw [Aes.X86_64.AesNi.st_toList]; rfl

/-- The function of states of a direction: the cipher or its inverse. -/
def stF (enc : Bool) (nr : Nat) (w : List Byte) : Spec.Aes.State → Spec.Aes.State :=
  if enc then Spec.Aes.cipher nr w else Spec.Aes.invCipher nr w

theorem ciphOf_b16 (enc : Bool) (nr : Nat) (w : List Byte) (v : BitVec 128) :
    ciphOf enc nr w (b16 v) = (stF enc nr w (st v)).toList := by
  obtain e : (Vector.ofFn fun i : Fin 16 => (b16 v).getD i.1 0) = st v := by
    apply Vector.ext
    intro i hi
    simp [b16, st, X86_64.byte]
  cases enc
  · simp only [ciphOf, stF, Bool.false_eq_true, ↓reduceIte, Spec.Cbc.aesInvWith, e]
  · simp only [ciphOf, stF, ↓reduceIte, Spec.Cbc.aesWith, e]

/-- A block `d` through XTS with the tweak `t`, as words, when `c` is the
word of the cipher of `d ⊕ t`'s state. -/
theorem xts_word (enc : Bool) (nr : Nat) (w : List Byte) (d t c : BitVec 128)
    (hc : st c = stF enc nr w (st (d ^^^ t))) :
    b16 (c ^^^ t) = Spec.Xts.block (ciphOf enc nr w) (b16 t) (b16 d) := by
  rw [Spec.Xts.block, b16_xor, ← st_toList c, hc, ← ciphOf_b16, b16_xor]

end VG.Proof.AesXts.X86_64.Vaes

end

end


/-!
# One-pass XTS-AES on x86-64: eight blocks at a time

`GInv enc KP s₀ b c`: after `c` blocks, with the tweaks of blocks `b … b + 7`
at `scratch + 256`: the registers hold the moved arguments (the tweak pointer
still in `rdx`), only the data and the scratch buffer have changed, and the
first `c` blocks are XTS's (`outBlk`) and the rest unchanged. `KP` is what the rounds need (the key schedule, and for
decryption the round keys through `aesimc` in the scratch buffer below the
tweaks), kept by writes to the data and the tweaks (`Stable`).

`TwR s₀ c`: the tweak registers `ymm4`–`ymm7` hold the tweaks of blocks
`c … c + 7`, and `ymm11` the constant `0x87` in both lanes. `group_wp`: one
run of `group f8` takes `GInv b c ∧ TwR c` to `c + 8`, for rounds `f8`
computing the cipher (or its inverse) on both lanes of `ymm0`–`ymm3`
(`Blk8`); it writes only the data.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.Vaes

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.X86_64 (W R Iv Dp N S schR ivR dataR scrR stkR UPre blk wK iv0)
open VG.Impl.AesXts.X86_64Vaes (bufOff group preXor postXor steps regs4 tws)
open VG.Proof.AesXts (b16 next_b8)
open VG.Proof.Aes.X86_64.AesNi (st inRegions_wr ofInt_natCast)

/-- The tweak of block `b + j` is at `slot s₀ j`. -/
abbrev slot (s₀ : State) (j : Nat) : Addr := S s₀ + BitVec.ofNat 64 (bufOff + 16 * j)

/-- The scratch buffer from the tweaks on. -/
abbrev bufR (s₀ : State) : Region := ⟨S s₀ + BitVec.ofNat 64 bufOff, 1920⟩

/-- What the rounds need is kept by writes to the data and the tweaks. -/
def Stable (KP : State → Prop) (s₀ : State) : Prop :=
  ∀ s s', KP s → s'.gpr .rdi = s.gpr .rdi → s'.gpr .rsi = s.gpr .rsi → s'.gpr .r8 = s.gpr .r8 →
    s'.gpr .r10 = s.gpr .r10 → s'.rd = s.rd → s'.wr = s.wr → Frame [dataR s₀, bufR s₀] s.mem s'.mem → KP s'

/-- `f8` computes the cipher (or its inverse) on both lanes of `ymm0`–`ymm3`. -/
def Blk8 (enc : Bool) (f8 : List XReg → Prog isa) (KP : State → Prop) (s₀ : State) : Prop :=
  ∀ s, KP s → WP isa (f8 regs4) s fun s' =>
    (∀ b ∈ regs4, ∀ l < 2, st (s'.lane b l) = stF enc (R s₀) (wK s₀) (st (s.lane b l))) ∧
      YFrame (.xmm8 :: regs4) s s'

/-- Block `k` after XTS. -/
abbrev outBlk (enc : Bool) (s₀ : State) (k : Nat) : List Byte :=
  Spec.Xts.block (ciphOf enc (R s₀) (wK s₀)) (Spec.Xts.next (iv0 s₀) k) (bytesAt s₀.mem (blk s₀ k) 16)

structure GInv (enc : Bool) (KP : State → Prop) (s₀ : State) (b c : Nat) (s : State) : Prop where
  kp : KP s
  le : c ≤ N s₀
  r8 : s.gpr .r8 = S s₀
  r9 : s.gpr .r9 = BitVec.ofNat 64 (N s₀ - c)
  r11 : s.gpr .r11 = blk s₀ c
  r10 : s.gpr .r10 = W s₀ + BitVec.ofNat 64 (16 * R s₀)
  keep : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [dataR s₀, scrR s₀] s₀.mem s.mem
  data : ∀ k < N s₀, bytesAt s.mem (blk s₀ k) 16 = if k < c then outBlk enc s₀ k else bytesAt s₀.mem (blk s₀ k) 16
  buf : ∀ j < 8, bytesAt s.mem (slot s₀ j) 16 = Spec.Xts.next (iv0 s₀) (b + j)
  rdx : s.gpr .rdx = Iv s₀

/-- In the loop: the tweaks of blocks `c … c + 7` in `ymm4`–`ymm7`, and
`0x87` in both lanes of `ymm11`. -/
structure TwR (s₀ : State) (c : Nat) (s : State) : Prop where
  tw : ∀ k (h : k < tws.length), ∀ l < 2, b16 (s.lane tws[k] l) = Spec.Xts.next (iv0 s₀) (c + (2 * k + l))
  k87 : ∀ l < 2, qword (s.lane .xmm11 l) 0 = 0x87

theorem next_add (t : List Byte) (a b : Nat) : Spec.Xts.next t (a + b) = Spec.Xts.next (Spec.Xts.next t a) b := by
  induction b with
  | zero => rfl
  | succ b ih => rw [← Nat.add_assoc, Spec.Xts.next, Nat.repeat, ← Spec.Xts.next, ih]; rfl

section
variable {s₀ : State}

/-- Block `c + 2k + l` from block `c`. -/
theorem blk_lane (c k l : Nat) : blk s₀ c + BitVec.ofNat 64 (32 * (0 + k) + 16 * l) = blk s₀ (c + (2 * k + l)) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega_arith

theorem slot_scr {j : Nat} (hj : j < 16) : Region.Sub ⟨slot s₀ j, 16⟩ (scrR s₀) :=
  UPre.scr_sub (by simp only [bufOff]; omega_arith)

/-- The blocks of a group lie in the data. -/
theorem group_data {c : Nat} (hc : c + 8 ≤ N s₀) : Region.Sub ⟨blk s₀ c, 128⟩ (dataR s₀) := by
  rw [blk]; exact Offset.sub_base _ (by omega_arith)

theorem buf_scr : Region.Sub (bufR s₀) (scrR s₀) := UPre.scr_sub (d := bufOff) (n := 1920) (by decide)

end

theorem tws_regs4 : ∀ t ∈ tws, t ∉ regs4 := by decide

/-- One group of eight blocks. -/
theorem group_wp {enc : Bool} {KP : State → Prop} {f8 : List XReg → Prog isa} {s₀ : State} (hp : UPre s₀)
    (hst : Stable KP s₀) (hf : Blk8 enc f8 KP s₀) {b c : Nat} (hc : c + 8 ≤ N s₀) {s : State}
    (h : GInv enc KP s₀ b c s) (ht : TwR s₀ c s) :
    WP isa (group f8) s fun s' =>
      (GInv enc KP s₀ b (c + 8) s' ∧ TwR s₀ (c + 8) s') ∧ s'.cf = some (decide (N s₀ - (c + 8) < 8)) := by
  have hw := hp.data_wrap
  obtain hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  obtain inD : ∀ k < 4, InRegions s.wr (s.gpr .r11 + BitVec.ofInt 64 ((32 * (0 + k) : Nat) : Int)) 32 := by
    intro k hk
    refine ⟨dataR s₀, by rw [hW]; simp, ?_⟩
    rw [h.r11, ofInt_natCast, blk, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  -- The tweaks XORed in.
  refine WP.seq (WP.mono (preList_ok regs4 tws 0 s (by decide) rfl tws_regs4
    (fun k hk => inRegions_wr (inD k hk))) fun s₁ ⟨e₁, g₁, m₁, rd₁, wr₁, x₁⟩ => ?_)
  obtain kp₁ : KP s₁ := hst s s₁ h.kp (by rw [g₁]) (by rw [g₁]) (by rw [g₁]) (by rw [g₁]) rd₁ wr₁
    (by rw [m₁]; exact Frame.refl _ _)
  -- The rounds.
  refine WP.seq (WP.mono (hf s₁ kp₁) fun s₂ ⟨e₂, f₂⟩ => ?_)
  obtain kp₂ : KP s₂ := hst s₁ s₂ kp₁ (by rw [f₂.gpr]) (by rw [f₂.gpr]) (by rw [f₂.gpr]) (by rw [f₂.gpr])
    f₂.rd f₂.wr (by rw [f₂.mem]; exact Frame.refl _ _)
  obtain g₂ : s₂.gpr = s.gpr := f₂.gpr.trans g₁
  obtain m₂ : s₂.mem = s.mem := f₂.mem.trans m₁
  obtain wr₂ : s₂.wr = s.wr := f₂.wr.trans wr₁
  obtain rd₂ : s₂.rd = s.rd := f₂.rd.trans rd₁
  -- Registers outside the blocks' are as they were.
  obtain o₂ : ∀ r, r ∉ regs4 → r ≠ .xmm8 → ∀ l < 2, s₂.lane r l = s.lane r l := fun r hr h8 l hl => by
    rw [f₂.lane r (by simp [h8, hr]) l hl, x₁ r hr l hl]
  -- The tweaks XORed in again, and the blocks stored.
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (postList_ok regs4 tws 0 s₂ (by decide) rfl tws_regs4
    (fun k hk => by rw [wr₂, g₂]; exact inD k hk)
    (by rw [g₂, h.r11, hp.blk_toNat (by omega_arith)]; show _ + 32 * (0 + 4) ≤ _; omega_arith))
    fun s₃ ⟨e₃, f₃, g₃, rd₃, wr₃, x₃⟩ => ?_
  rw [g₂, h.r11, Nat.mul_zero, BitVec.add_zero, m₂, show 32 * regs4.length = 128 from rfl] at f₃
  obtain g₃' : s₃.gpr = s.gpr := g₃.trans g₂
  obtain kp₃ : KP s₃ := hst s₂ s₃ kp₂ (by rw [g₃]) (by rw [g₃]) (by rw [g₃]) (by rw [g₃]) rd₃ wr₃ (by
    rw [m₂]; exact f₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dataR s₀, by simp, group_data hc⟩)
  obtain o₃ : ∀ r, r ∉ regs4 → r ≠ .xmm8 → ∀ l < 2, s₃.lane r l = s.lane r l := fun r hr h8 l hl => by
    rw [x₃ r hr l hl, o₂ r hr h8 l hl]
  obtain hK₃ : ∀ l < 2, qword (s₃.lane .xmm11 l) 0 = 0x87 := fun l hl => by
    rw [o₃ _ (by decide) (by decide) l hl]; exact ht.k87 l hl
  -- The tweaks times `α⁸`.
  rw [WP.block_append_iff]
  refine WP.mono (stepsN_ok tws (by decide) (by decide) (by decide) s₃ hK₃)
    fun s₄ ⟨e₄, g₄, m₄, rd₄, wr₄, x₄⟩ => ?_
  obtain g₄' : s₄.gpr = s.gpr := g₄.trans g₃'
  obtain kp₄ : KP s₄ := hst s₃ s₄ kp₃ (by rw [g₄]) (by rw [g₄]) (by rw [g₄]) (by rw [g₄]) rd₄ wr₄
    (by rw [m₄]; exact Frame.refl _ _)
  obtain hK₄ : ∀ l < 2, qword (s₄.lane .xmm11 l) 0 = 0x87 := fun l hl => by
    rw [x₄ _ (by decide) (by decide) l hl]; exact hK₃ l hl
  -- The memory after the group.
  obtain fr : Frame [dataR s₀, scrR s₀] s₀.mem s₄.mem := by
    rw [m₄]
    exact h.frame.trans (f₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dataR s₀, by simp, group_data hc⟩)
  obtain hdata : ∀ k < N s₀, bytesAt s₄.mem (blk s₀ k) 16 = if k < c + 8 then outBlk enc s₀ k
      else bytesAt s₀.mem (blk s₀ k) 16 := by
    intro k hk
    rw [m₄]
    by_cases hin : c ≤ k ∧ k < c + 8
    · obtain ⟨i, rfl⟩ : ∃ i, k = c + i := ⟨k - c, by omega_arith⟩
      obtain hi : i < 8 := by omega_arith
      obtain hkk : i / 2 < regs4.length := by have : regs4.length = 4 := rfl; omega_arith
      obtain hkt : i / 2 < tws.length := by have : tws.length = 4 := rfl; omega_arith
      obtain hl : i % 2 < 2 := Nat.mod_lt _ (by decide)
      obtain ab : blk s₀ (c + i) = s.gpr .r11 + BitVec.ofNat 64 (32 * (0 + i / 2) + 16 * (i % 2)) := by
        rw [h.r11, blk_lane]; congr 2; omega_arith
      rw [g₂] at e₃
      rw [bytesAt_b16, ab, e₃ _ hkk _ hl, ← ab]
      obtain hT : s₂.lane tws[i / 2] (i % 2) = s.lane tws[i / 2] (i % 2) :=
        o₂ _ (tws_regs4 _ (List.getElem_mem hkt)) (by
          have : tws[i / 2] ∈ tws := List.getElem_mem hkt
          intro h8; rw [h8] at this; exact absurd this (by decide)) _ hl
      obtain e1 := e₁ _ hkk _ hl
      rw [← ab] at e1
      obtain hc' : st (s₂.lane regs4[i / 2] (i % 2)) = stF enc (R s₀) (wK s₀)
          (st (s.mem.readW (blk s₀ (c + i)) 128 ^^^ s.lane tws[i / 2] (i % 2))) :=
        (e₂ _ (List.getElem_mem hkk) _ hl).trans (congrArg (fun v => stF enc (R s₀) (wK s₀) (st v)) e1)
      rw [hT]
      refine (xts_word enc (R s₀) (wK s₀) _ _ _ hc').trans ?_
      rw [← bytesAt_b16, ht.tw _ hkt _ hl, h.data _ hk, show c + (2 * (i / 2) + i % 2) = c + i by omega_arith]
      simp only [show ¬ c + i < c by omega_arith, ite_false, show c + i < c + 8 by omega_arith, ite_true]
    · rw [AesCbc.X86_64.bytesAt_frame f₃ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [blk, blk]
          exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide), h.data k hk]
      by_cases hlt : k < c
      · simp only [hlt, ite_true, show k < c + 8 by omega_arith]
      · simp only [hlt, ite_false, show ¬ k < c + 8 by omega_arith]
  obtain hbuf : ∀ j < 8, bytesAt s₄.mem (slot s₀ j) 16 = Spec.Xts.next (iv0 s₀) (b + j) := by
    intro j hj
    rw [m₄, AesCbc.X86_64.bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((hp.data_scr.sub_left (group_data hc)).sub_right (slot_scr (j := j) (by omega_arith))).symm) (by decide),
      h.buf j hj]
  obtain htw : ∀ k (hk : k < tws.length), ∀ l < 2,
      b16 (s₄.lane tws[k] l) = Spec.Xts.next (iv0 s₀) (c + 8 + (2 * k + l)) := by
    intro k hk l hl
    obtain hm : tws[k] ∈ tws := List.getElem_mem hk
    rw [e₄ _ hm l hl, o₃ _ (tws_regs4 _ hm) (by intro h8; rw [h8] at hm; exact absurd hm (by decide)) l hl,
      stepW, ← next_b8, ht.tw k hk l hl, ← next_add]
    congr 1; omega_arith
  obtain hrd : s₄.rd = s₀.rd := by rw [rd₄, rd₃, rd₂, h.rd]
  obtain hwr : s₄.wr = s₀.wr := by rw [wr₄, wr₃, wr₂, h.wr]
  -- `add r11, 128`, `sub r9, 8` and `cmp r9, 8`.
  obtain e128 : BitVec.signExtend 64 (128 : BitVec 32) = 128 := by decide
  obtain e8 : BitVec.signExtend 64 (8 : BitVec 32) = 8 := by decide
  obtain hr11 : s₄.gpr .r11 = blk s₀ c := by rw [g₄', h.r11]
  obtain hr9 : s₄.gpr .r9 = BitVec.ofNat 64 (N s₀ - c) := by rw [g₄', h.r9]
  obtain hsub : BitVec.ofNat 64 (N s₀ - c) - 8 = BitVec.ofNat 64 (N s₀ - (c + 8)) := by
    rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, Offset.ofNat_sub_ofNat (by omega_arith), Nat.sub_sub]
  obtain hadd : blk s₀ c + 128 = blk s₀ (c + 8) := by
    rw [blk, blk, show (128 : BitVec 64) = BitVec.ofNat 64 128 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add,
      show 16 * c + 128 = 16 * (c + 8) by omega_arith]
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e128, e8, hr11, hr9,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  have hN := hp.data_wrap
  refine ⟨⟨⟨hst s₄ _ kp₄ (by simp) (by simp) (by simp) (by simp) rfl rfl (Frame.refl _ _), hc,
      by simp [g₄', h.r8], by simp; exact hsub, by simp; exact hadd, by simp [g₄', h.r10],
      fun r h1 h2 h3 h4 h5 h6 h7 => by simp [h5, h7, g₄', h.keep r h1 h2 h3 h4 h5 h6 h7],
      hrd, hwr, fr, hdata, hbuf, by simp [g₄', h.rdx]⟩, ⟨htw, hK₄⟩⟩, ?_⟩
  simp only [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show N s₀ - (c + 8) < 2 ^ 64 by omega_arith),
    show (8 : BitVec 64).toNat = 8 from rfl]

end VG.Proof.AesXts.X86_64.Vaes
