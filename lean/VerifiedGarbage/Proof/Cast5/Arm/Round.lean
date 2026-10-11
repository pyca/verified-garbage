import VerifiedGarbage.Proof.Cast5.Arm.Scan
import VerifiedGarbage.Proof.Cast5.Rotate
import VerifiedGarbage.Proof.Cast5.Round

/-!
# CAST5 on ARMv7: a round

`round up` computes `I` (`byType mix`, `rotate`), spreads its bytes over
`r4`–`r7` (`spread`), scans `tab1234` and combines the four values into `f`
(`byType comb`), makes the Feistel step (`feistel`), and moves the type and
the count of rounds left on (`next`).
-/

namespace VG.Proof.Cast5.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Cast5.Arm

/-! ## Choosing by the type -/

/-- The address of the slot at `off` of the working space at `r12`. -/
scoped notation:max "slot " s:max off:max => State.addr (State.gpr s Reg.r12 + BitVec.ofNat 32 off)

theorem eval_eq (s : State) : eval .eq s = some s.z := rfl
theorem eval_ne (s : State) : eval .ne s = some !s.z := rfl

theorem byType_ok (s : State) (f : Nat → List Instr) {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3)
    (hin : InRegions (s.rd ++ s.wr) (slot s 20) 4) (hv : s.mem.readW (slot s 20) 32 = BitVec.ofNat 32 t)
    {Q : State → Prop} (hQ : ∀ u, Keep [.r0] s u → u.mem = s.mem → WP isa (.block (f t)) u Q) :
    WP isa (byType f) s Q := by
  unfold byType
  refine WP.seq ?_
  crun [typeOff, hin, hv]
  rcases ht with rfl | rfl | rfl
  · refine WP.ite true rfl (fun _ => hQ _ ⟨fun r hr => ?_, rfl, rfl, rfl⟩ rfl)
      (fun h => absurd h (by decide))
    simp only [List.mem_singleton] at hr
    simp only [gpr_sub]; exact gpr_setReg_of_ne _ _ hr
  · refine WP.ite false rfl (fun h => absurd h (by decide)) (fun _ => ?_)
    refine WP.seq ?_
    crun
    refine WP.ite true rfl (fun _ => hQ _ ⟨fun r hr => ?_, rfl, rfl, rfl⟩ rfl)
      (fun h => absurd h (by decide))
    simp only [List.mem_singleton] at hr
    simp only [gpr_sub]; exact gpr_setReg_of_ne _ _ hr
  · refine WP.ite false rfl (fun h => absurd h (by decide)) (fun _ => ?_)
    refine WP.seq ?_
    crun
    refine WP.ite false rfl (fun h => absurd h (by decide)) (fun _ =>
      hQ _ ⟨fun r hr => ?_, rfl, rfl, rfl⟩ rfl)
    simp only [List.mem_singleton] at hr
    simp only [gpr_sub]; exact gpr_setReg_of_ne _ _ hr

/-! ## The pieces of a round -/

theorem mix_ok (s : State) {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) {km d : Spec.Cast5.Word}
    (h3 : s.gpr .r3 = d) (hin : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .lr + BitVec.ofNat 32 0)) 4)
    (hv : s.mem.readW (State.addr (s.gpr .lr + BitVec.ofNat 32 0)) 32 = km) :
    WP isa (.block (Impl.Cast5.Arm.mix t)) s fun u => u.gpr .r1 = Proof.Cast5.mix t km d ∧ Keep [.r1] s u ∧ u.mem = s.mem := by
  rcases ht with rfl | rfl | rfl <;>
  · unfold Impl.Cast5.Arm.mix
    crun [hin, hv, h3]
    exact ⟨rfl, ⟨fun r hr => by simp only [List.mem_singleton] at hr; simp only [gpr_setReg, hr, ite_false], rfl, rfl, rfl⟩⟩

theorem rotateStep_ok (s : State) {b : Nat} (hb : b < 5) {a kb : BitVec 32}
    (h1 : s.gpr .r1 = a) (h0 : s.gpr .r0 = kb) :
    WP isa (.block (rotateStep b)) s fun u =>
      u.gpr .r1 = Proof.Cast5.step a kb b ∧ u.gpr .r0 = (if b < 4 then kb >>> 1 else kb) ∧
      Keep [.r0, .r1, .r4, .r5] s u ∧ u.mem = s.mem := by
  have hn : 1 ≤ 32 - 2 ^ b ∧ 32 - 2 ^ b ≤ 31 := by
    rcases (show b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 by omega) with h | h | h | h | h <;>
      subst h <;> decide
  unfold rotateStep
  by_cases h4 : b < 4
  · rw [ite_eq_left h4]
    crun [h1, h0, hn]
    exact ⟨rfl, by rw [ite_eq_left h4], ⟨by keep_regs, rfl, rfl, rfl⟩⟩
  · rw [ite_eq_right h4]
    crun [h1, h0, hn]
    exact ⟨rfl, by rw [ite_eq_right h4], ⟨by keep_regs, rfl, rfl, rfl⟩⟩

theorem rotate_ok (s : State) {a kr : BitVec 32} (h1 : s.gpr .r1 = a)
    (hin : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .lr + BitVec.ofNat 32 64)) 4)
    (hv : s.mem.readW (State.addr (s.gpr .lr + BitVec.ofNat 32 64)) 32 = kr) :
    WP isa (.block rotate) s fun u =>
      u.gpr .r1 = a.rotateLeft (kr.toNat % 32) ∧ Keep [.r0, .r1, .r4, .r5] s u ∧ u.mem = s.mem := by
  have e : rotate = [.ldr .r0 .lr 64] ++ rotateStep 0 ++ rotateStep 1 ++ rotateStep 2 ++ rotateStep 3 ++
      rotateStep 4 := rfl
  rw [e, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff]
  have k0 : WP isa (.block [.ldr .r0 .lr 64]) s fun u =>
      u.gpr .r0 = kr ∧ u.gpr .r1 = a ∧ Keep [.r0, .r1, .r4, .r5] s u ∧ u.mem = s.mem := by
    crun [hin, hv, h1]
    exact ⟨fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; simp only [gpr_setReg, hr.1, ite_false],
      rfl, rfl, rfl⟩
  refine WP.mono k0 fun t₀ ⟨k₀, a₀, p₀, m₀⟩ => ?_
  refine WP.mono (rotateStep_ok t₀ (by decide) a₀ k₀) fun t₁ ⟨a₁, k₁, p₁, m₁⟩ => ?_
  rw [ite_eq_left (by decide)] at k₁
  refine WP.mono (rotateStep_ok t₁ (by decide) a₁ k₁) fun t₂ ⟨a₂, k₂, p₂, m₂⟩ => ?_
  rw [ite_eq_left (by decide)] at k₂
  refine WP.mono (rotateStep_ok t₂ (by decide) a₂ k₂) fun t₃ ⟨a₃, k₃, p₃, m₃⟩ => ?_
  rw [ite_eq_left (by decide)] at k₃
  refine WP.mono (rotateStep_ok t₃ (by decide) a₃ k₃) fun t₄ ⟨a₄, k₄, p₄, m₄⟩ => ?_
  rw [ite_eq_left (by decide)] at k₄
  refine WP.mono (rotateStep_ok t₄ (by decide) a₄ k₄) fun t₅ ⟨a₅, _, p₅, m₅⟩ => ?_
  refine ⟨?_, p₀.trans (p₁.trans (p₂.trans (p₃.trans (p₄.trans p₅)))), by rw [m₅, m₄, m₃, m₂, m₁, m₀]⟩
  rw [a₅, Proof.Cast5.steps_eq]

/-- Index `k` of a scan of `I`: byte `k` of `I` (from the least significant). -/
def idx (i : BitVec 32) : Nat → BitVec 32
  | 0 => i &&& 255
  | 1 => i >>> 8 &&& 255
  | 2 => i >>> 16 &&& 255
  | _ => i >>> 24

theorem idx_toNat (i : BitVec 32) {k : Nat} (hk : k < 4) :
    (idx i k).toNat = i.toNat / 2 ^ (8 * k) % 256 := by
  have := i.isLt
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;>
    simp only [idx, BitVec.toNat_ushiftRight, BitVec.toNat_and, Nat.shiftRight_eq_div_pow,
      show (255 : BitVec 32).toNat = 255 from rfl, show (255 : Nat) = 2 ^ 8 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod] <;> omega

theorem idx_lt (i : BitVec 32) {k : Nat} (hk : k < 4) : (idx i k).toNat < 256 := by
  rw [idx_toNat i hk]; omega

theorem idx_byte (i : BitVec 32) {k : Nat} (hk : k < 4) :
    BitVec.ofNat 8 (idx i k).toNat = Spec.Cast5.byte i (3 - k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, idx_toNat i hk]
  simp only [Spec.Cast5.byte, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;> omega

theorem spread_ok (s : State) {i : BitVec 32} (h1 : s.gpr .r1 = i) :
    WP isa (.block spread) s fun u =>
      (∀ k < 4, u.gpr (idxReg k) = idx i k) ∧ Keep [.r4, .r5, .r6, .r7] s u ∧ u.mem = s.mem := by
  unfold spread
  crun [h1]
  refine ⟨fun k hk => ?_, ⟨fun r hr => ?_, rfl, rfl, rfl⟩⟩
  · rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem comb_ok (s : State) {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) :
    WP isa (.block (Impl.Cast5.Arm.comb t)) s fun u =>
      u.gpr .r1 = Proof.Cast5.comb t (s.gpr .r11) (s.gpr .r10) (s.gpr .r9) (s.gpr .r8) ∧ Keep [.r1] s u ∧
        u.mem = s.mem := by
  rcases ht with rfl | rfl | rfl <;>
  · unfold Impl.Cast5.Arm.comb
    crun
    exact ⟨rfl, ⟨fun r hr => by simp only [List.mem_singleton] at hr; simp only [gpr_setReg, hr, ite_false], rfl, rfl, rfl⟩⟩

theorem feistel_ok (s : State) (up : Bool) :
    WP isa (.block (feistel up)) s fun u =>
      u.gpr .r2 = s.gpr .r3 ∧ u.gpr .r3 = s.gpr .r1 ^^^ s.gpr .r2 ∧
      u.gpr .lr = (if up then s.gpr .lr + 4 else s.gpr .lr - 4) ∧ Keep [.r1, .r2, .r3, .lr] s u ∧
      u.mem = s.mem := by
  cases up <;>
  · unfold feistel
    crun
    exact ⟨by keep_regs, rfl, rfl, rfl⟩

/-- The type after `t`. -/
def nextT (up : Bool) (t : Nat) : Nat :=
  if up then (if t = 3 then 1 else t + 1) else (if t = 1 then 3 else t - 1)

theorem nextT_mem {up : Bool} {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) :
    nextT up t = 1 ∨ nextT up t = 2 ∨ nextT up t = 3 := by
  cases up <;> rcases ht with rfl | rfl | rfl <;> decide

/-- The type `v` (in `r0`) to its slot, then the count of rounds left down. -/
theorem nextTail_ok (s : State) {v cnt : BitVec 32} (h0 : s.gpr .r0 = v)
    (hinT : InRegions s.wr (slot s 20) 4)
    (hinC : InRegions s.wr (slot s 16) 4) (hvC : (s.mem.writeW (slot s 20) v).readW (slot s 16) 32 = cnt) :
    WP isa (.block [.str .r0 .r12 typeOff, .ldr .r0 .r12 cntOff, .subs .r0 .r0 (.imm 1), .str .r0 .r12 cntOff]) s
      fun u => u.mem = (s.mem.writeW (slot s 20) v).writeW (slot s 16) (cnt - 1) ∧ u.z = (cnt - 1 == 0) ∧
        Keep [.r0] s u := by
  have hinC' : InRegions (s.rd ++ s.wr) (slot s 16) 4 := by
    obtain ⟨g, hg, hc⟩ := hinC; exact ⟨g, List.mem_append_right _ hg, hc⟩
  crun [typeOff, cntOff, h0, hinT, hinC, hinC', hvC]
  exact ⟨by keep_regs, rfl, rfl, rfl⟩

theorem next_ok (s : State) (up : Bool) {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) {cnt : BitVec 32}
    (hinT : InRegions s.wr (slot s 20) 4) (hvT : s.mem.readW (slot s 20) 32 = BitVec.ofNat 32 t)
    (hinC : InRegions s.wr (slot s 16) 4) (hvC : s.mem.readW (slot s 16) 32 = cnt)
    (hsep : Mem.Sep (slot s 16) 4 (slot s 20) 4) :
    WP isa (next up) s fun u =>
      u.mem = (s.mem.writeW (slot s 20) (BitVec.ofNat 32 (nextT up t))).writeW (slot s 16) (cnt - 1) ∧
      u.z = (cnt - 1 == 0) ∧ Keep [.r0] s u := by
  have hinT' : InRegions (s.rd ++ s.wr) (slot s 20) 4 := by
    obtain ⟨g, hg, hc⟩ := hinT; exact ⟨g, List.mem_append_right _ hg, hc⟩
  have hvC' (v : BitVec 32) : (s.mem.writeW (slot s 20) v).readW (slot s 16) 32 = cnt := by
    rw [Mem.readW_writeW_sep hsep (by decide), hvC]
  -- The rest, from the state after the branch, which wrote only `r0` and the flags.
  have tail : ∀ u : State, Keep [.r0] s u → u.mem = s.mem → u.gpr .r0 = BitVec.ofNat 32 (nextT up t) →
      WP isa (.block [.str .r0 .r12 typeOff, .ldr .r0 .r12 cntOff, .subs .r0 .r0 (.imm 1),
        .str .r0 .r12 cntOff]) u fun w =>
      w.mem = (s.mem.writeW (slot s 20) (BitVec.ofNat 32 (nextT up t))).writeW (slot s 16) (cnt - 1) ∧
      w.z = (cnt - 1 == 0) ∧ Keep [.r0] s w := by
    intro u uk um u0
    have e12 : u.gpr .r12 = s.gpr .r12 := uk.gpr _ (by decide)
    have es (off : Nat) : slot u off = slot s off := by rw [e12]
    refine WP.mono (nextTail_ok u u0 (by rw [es, uk.wr]; exact hinT) (by rw [es, uk.wr]; exact hinC)
      (by rw [es, es, um]; exact hvC' _)) fun w ⟨wm, wz, wk⟩ => ⟨by rw [wm, es, es, um], wz, uk.trans wk⟩
  unfold next
  cases up <;> rcases ht with rfl | rfl | rfl
  all_goals
    refine WP.seq ?_
    crun [typeOff, hinT', hvT]
  all_goals
    refine WP.seq (wp_ite_eq (fun h => ?_) (fun h => ?_))
  all_goals first
    | exact absurd (h.symm.trans (z_sub _ _ _)) (by decide)
    | refine WP.mono (Q := fun u : State => Keep [.r0] s u ∧ u.mem = s.mem ∧
          u.gpr .r0 = BitVec.ofNat 32 (nextT _ _)) ?_ fun u ⟨a, b, c⟩ => tail u a b c
      crun
      exact ⟨⟨by keep_regs, rfl, rfl, rfl⟩, by decide⟩

/-! ## The round -/

/-- `f` of a round of type `t` with the subkeys `km`, `kr`, on `D = d`. -/
def fT (t : Nat) (km kr d : Spec.Cast5.Word) : Spec.Cast5.Word :=
  let i := (Proof.Cast5.mix t km d).rotateLeft (kr.toNat % 32)
  Proof.Cast5.comb t (Spec.Cast5.S1 (Spec.Cast5.byte i 0)) (Spec.Cast5.S2 (Spec.Cast5.byte i 1))
    (Spec.Cast5.S3 (Spec.Cast5.byte i 2)) (Spec.Cast5.S4 (Spec.Cast5.byte i 3))

/-- What a round needs: `(L, R)` in `(r2, r3)`; `Kmᵢ` at `lr` and `Krᵢ` at
`lr + 64`; the type `t` and the count `cnt` of rounds left in their slots. -/
structure RoundPre (s : State) (km kr l r : Spec.Cast5.Word) (t : Nat) (cnt : BitVec 32) : Prop where
  r2 : s.gpr .r2 = l
  r3 : s.gpr .r3 = r
  inM : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .lr + BitVec.ofNat 32 0)) 4
  valM : s.mem.readW (State.addr (s.gpr .lr + BitVec.ofNat 32 0)) 32 = km
  inR : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .lr + BitVec.ofNat 32 64)) 4
  valR : s.mem.readW (State.addr (s.gpr .lr + BitVec.ofNat 32 64)) 32 = kr
  ht : t = 1 ∨ t = 2 ∨ t = 3
  inT : InRegions s.wr (slot s 20) 4
  valT : s.mem.readW (slot s 20) 32 = BitVec.ofNat 32 t
  inC : InRegions s.wr (slot s 16) 4
  valC : s.mem.readW (slot s 16) 32 = cnt
  sep : Mem.Sep (slot s 16) 4 (slot s 20) 4

theorem RoundPre.inT' {s : State} {km kr l r : Spec.Cast5.Word} {t : Nat} {cnt : BitVec 32}
    (h : RoundPre s km kr l r t cnt) : InRegions (s.rd ++ s.wr) (slot s 20) 4 := by
  obtain ⟨g, hg, hc⟩ := h.inT; exact ⟨g, List.mem_append_right _ hg, hc⟩

theorem mem_r12 : Reg.r12 ∉ [Reg.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr] := by
  decide

/-- The registers a round writes before its Feistel step. -/
def preRegs : List Reg := [.r0, .r1, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]

/-- The registers a round writes. -/
def roundRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr]

theorem round_ok (s : State) (up : Bool) {km kr l r : Spec.Cast5.Word} {t : Nat} {cnt : BitVec 32}
    (h : RoundPre s km kr l r t cnt) :
    WP isa (round up) s fun u =>
      u.gpr .r2 = r ∧ u.gpr .r3 = l ^^^ fT t km kr r ∧
      u.gpr .lr = (if up then s.gpr .lr + 4 else s.gpr .lr - 4) ∧
      u.mem = (s.mem.writeW (slot s 20) (BitVec.ofNat 32 (nextT up t))).writeW (slot s 16) (cnt - 1) ∧
      u.z = (cnt - 1 == 0) ∧ Keep roundRegs s u := by
  have ht := h.ht
  unfold round
  -- `I` before the rotation.
  refine WP.seq (WP.mono (byType_ok s Impl.Cast5.Arm.mix (Q := fun v => v.gpr .r1 = Proof.Cast5.mix t km r ∧
      Keep [.r0, .r1] s v ∧ v.mem = s.mem) ht h.inT' h.valT fun u uk um => ?_) fun v hv => ?_)
  · have g (q : Reg) (hq : q ≠ .r0) : u.gpr q = s.gpr q := uk.gpr q (by simpa using hq)
    exact WP.mono (mix_ok u ht (by rw [g _ (by decide)]; exact h.r3)
      (by rw [uk.rd, uk.wr, g _ (by decide)]; exact h.inM) (by rw [um, g _ (by decide)]; exact h.valM))
      fun v ⟨v1, vk, vm⟩ => ⟨v1, (uk.mono (by decide)).trans (vk.mono (by decide)), vm.trans um⟩
  obtain ⟨v1, vk, vm⟩ := hv
  have gv (q : Reg) (hq : q ∉ [Reg.r0, .r1]) : v.gpr q = s.gpr q := vk.gpr q hq
  -- The rotation, the indices and the scan.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine (WP.mono (rotate_ok v v1 (kr := kr) (by rw [vk.rd, vk.wr, gv _ (by decide)]; exact h.inR)
    (by rw [vm, gv _ (by decide)]; exact h.valR)) fun w ⟨w1, wk, wm⟩ => ?_)
  obtain ⟨i, hi⟩ : ∃ i, (Proof.Cast5.mix t km r).rotateLeft (kr.toNat % 32) = i := ⟨_, rfl⟩
  rw [hi] at w1
  refine WP.mono (spread_ok w w1) fun x ⟨xi, xk, xm⟩ => ?_
  refine WP.seq (WP.mono (scan_ok x tab1234 fun k hk => by rw [xi k hk]; exact idx_lt i hk) fun y ⟨ya, yk, ym⟩ => ?_)
  have kxy := (vk.mono (by decide)).trans ((wk.mono (by decide)).trans ((xk.mono (by decide)).trans
    (yk.mono (show ∀ r ∈ [Reg.r0, .r1, .r8, .r9, .r10, .r11], r ∈ preRegs by decide))))
  have my : y.mem = s.mem := ym.trans (xm.trans (wm.trans vm))
  have r12y : y.gpr .r12 = s.gpr .r12 := kxy.gpr _ (by decide)
  -- `f`.
  refine WP.seq (WP.mono (byType_ok y Impl.Cast5.Arm.comb (Q := fun z => z.gpr .r1 = fT t km kr r ∧
      Keep preRegs s z ∧ z.mem = s.mem) ht (by rw [kxy.rd, kxy.wr, r12y]; exact h.inT')
      (by rw [my, r12y]; exact h.valT) fun u uk um => ?_) fun z hz => ?_)
  · have g (q : Reg) (hq : q ≠ .r0) : u.gpr q = y.gpr q := uk.gpr q (by simpa using hq)
    refine WP.mono (comb_ok u ht) fun z ⟨z1, zk, zm⟩ => ⟨?_, kxy.trans ((uk.mono (by decide)).trans
      (zk.mono (by decide))), zm.trans (um.trans my)⟩
    have a0 : y.gpr .r8 = _ := ya 0 (by decide)
    have a1 : y.gpr .r9 = _ := ya 1 (by decide)
    have a2 : y.gpr .r10 = _ := ya 2 (by decide)
    have a3 : y.gpr .r11 = _ := ya 3 (by decide)
    rw [z1, g _ (by decide), g _ (by decide), g _ (by decide), g _ (by decide), a0, a1, a2, a3,
      xi 0 (by decide), xi 1 (by decide),
      xi 2 (by decide), xi 3 (by decide)]
    unfold fT
    rw [hi]
    simp only [tab1234_eq (idx_lt i (show 0 < 4 by decide)) (show 0 < 4 by decide),
      tab1234_eq (idx_lt i (show 1 < 4 by decide)) (show 1 < 4 by decide),
      tab1234_eq (idx_lt i (show 2 < 4 by decide)) (show 2 < 4 by decide),
      tab1234_eq (idx_lt i (show 3 < 4 by decide)) (show 3 < 4 by decide), tabOf, idx_byte i (show 0 < 4 by decide), idx_byte i (show 1 < 4 by decide),
      idx_byte i (show 2 < 4 by decide), idx_byte i (show 3 < 4 by decide)]
  obtain ⟨z1, zk, zm⟩ := hz
  have gz (q : Reg) (hq : q ∉ preRegs) : z.gpr q = s.gpr q := zk.gpr q hq
  -- The Feistel step, then the type and the count.
  refine WP.seq (WP.mono (feistel_ok z up) fun a ⟨a2, a3, alr, ak, am⟩ => ?_)
  have ka := (zk.mono (show ∀ q ∈ preRegs, q ∈ roundRegs by decide)).trans
    (ak.mono (show ∀ q ∈ [Reg.r1, .r2, .r3, .lr], q ∈ roundRegs by decide))
  have r12a : a.gpr .r12 = s.gpr .r12 := ka.gpr _ (by decide)
  have es (off : Nat) : slot a off = slot s off := by rw [r12a]
  have ma : a.mem = s.mem := am.trans zm
  refine WP.mono (next_ok a up ht (cnt := cnt) (by rw [es, ka.wr]; exact h.inT) (by rw [es, ma]; exact h.valT)
    (by rw [es, ka.wr]; exact h.inC) (by rw [es, ma]; exact h.valC) (by rw [es, es]; exact h.sep))
    fun b ⟨bm, bz, bk⟩ => ?_
  have gb (q : Reg) (hq : q ≠ .r0) : b.gpr q = a.gpr q := bk.gpr q (by simpa using hq)
  refine ⟨by rw [gb _ (by decide), a2, gz _ (by decide), h.r3], ?_, ?_, by rw [bm, es, es, ma], bz,
    ka.trans (bk.mono (by decide))⟩
  · rw [gb _ (by decide), a3, z1, gz _ (by decide), h.r2, BitVec.xor_comm]
  · rw [gb _ (by decide), alr, gz _ (by decide)]

end VG.Proof.Cast5.Arm
