import VerifiedGarbage.Proof.Blowfish.Arm.F
import VerifiedGarbage.Proof.Blowfish.Feistel

/-!
# Blowfish on ARMv7: the block function

`cipher_run`: `cipher up` takes the halves in `r1` and `r2` to their
encryption (`up`) or decryption under the schedule at `r0`, changing only
`r1`, `r2`, `r4`–`r12`, `lr` and the flags.
-/

namespace VG.Proof.Blowfish.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Blowfish.Arm VG.Spec.Blowfish VG.Proof.Blowfish

/-- The P-array entry of round `m`. -/
def ord (up : Bool) (m : Nat) : Nat := if up then m else 17 - m

/-- `pPtr`'s offset in the schedule after `i` rounds. -/
def pBase (up : Bool) (i : Nat) : Nat := if up then 4096 + 4 * i else 4160 - 4 * i

/-- The registers the block function writes. -/
def cRegs : List Reg := [.r1, .r2, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]

/-- What the block function needs: the schedule at `r0` readable, without
wrapping around. -/
structure CipherEnv (s : State) : Prop where
  fit : (s.gpr .r0).toNat + 4168 ≤ 2 ^ 32
  rd : ∀ o, o + 4 ≤ 4168 → InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0) + BitVec.ofNat 64 o) 4

theorem CipherEnv.keep {s t : State} (E : CipherEnv s) {rs : List Reg} (h : Keep rs s t)
    (h0 : Reg.r0 ∉ rs) : CipherEnv t := by
  refine ⟨by rw [h.gpr h0]; exact E.fit, fun o ho => ?_⟩
  rw [h.gpr h0, h.2.1, h.2.2.1]; exact E.rd o ho

theorem CipherEnv.look {s : State} (E : CipherEnv s) (h8 : s.gpr .r8 = BitVec.allOnes 32) : LookEnv s :=
  ⟨E.fit, E.rd, h8⟩

/-- The address of the P-array entry of round `i`. -/
theorem addr_P {S : BitVec 32} (fit : S.toNat + 4168 ≤ 2 ^ 32) (up : Bool) {i : Nat} (hi : i < 16) :
    State.addr (S + BitVec.ofNat 32 (pBase up i) + BitVec.ofNat 32 (pAt up)) =
      State.addr S + BitVec.ofNat 64 (4096 + 4 * ord up i) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, addr_add (by cases up <;> simp [pBase, pAt] <;> omega)]
  congr 2; cases up <;> simp [pBase, pAt, ord] <;> omega

/-- After `i` rounds from `s₀`. -/
structure CInv (s₀ : State) (up : Bool) (i : Nat) (u : State) : Prop where
  le : i ≤ 16
  p : u.gpr .r12 = s₀.gpr .r0 + BitVec.ofNat 32 (pBase up i)
  halves : (u.gpr .r1, u.gpr .r2) =
    iter (scheduleAt s₀.mem (State.addr (s₀.gpr .r0))) (ord up) i (s₀.gpr .r1, s₀.gpr .r2)
  ones : u.gpr .r8 = BitVec.allOnes 32
  keep : Keep cRegs s₀ u
  mem : u.mem = s₀.mem

theorem round_head (u : State) (up : Bool) {P : BitVec 32} {a : Addr}
    (hp : State.addr (u.gpr .r12 + BitVec.ofNat 32 (pAt up)) = a)
    (hr : InRegions (u.rd ++ u.wr) a 4) (hP : u.mem.readW a 32 = P) :
    WP isa (.block [.ldr tmp pPtr (pAt up), .dp .eor xL xL (.reg tmp)]) u fun t =>
      t.gpr .r1 = u.gpr .r1 ^^^ P ∧ t.mem = u.mem := by
  have ho : pAt up < 4096 := by cases up <;> decide
  rw [← hp] at hr hP
  brun [ho, hr, hP]

theorem round_tail (u : State) (up : Bool) (S : BitVec 32) {i : Nat} (hi : i < 16)
    (h0 : u.gpr .r0 = S) (h12 : u.gpr .r12 = S + BitVec.ofNat 32 (pBase up i)) :
    WP isa (.block [.dp .eor xR xR (.reg fReg), .mov tmp (.reg xL), .mov xL (.reg xR), .mov xR (.reg tmp),
        .dp (if up then .add else .sub) pPtr pPtr (imm 4), .dp .sub tmp pPtr (.reg sch),
        .cmp tmp (imm (if up then pOff + 64 else pOff))]) u fun t =>
      t.gpr .r1 = u.gpr .r2 ^^^ u.gpr .lr ∧ t.gpr .r2 = u.gpr .r1 ∧
        t.gpr .r12 = S + BitVec.ofNat 32 (pBase up (i + 1)) ∧
        t.z = decide (i + 1 = 16) ∧ t.mem = u.mem := by
  cases up
  · brun [h0, h12, pOff]
    simp only [pBase, Bool.false_eq_true, ite_false]
    refine ⟨ofs_sub S (by omega), ?_⟩
    rw [ofs_sub S (by omega), ofs_diff, ofNat_sub_beq (by omega) (by decide)]
    congr 1; apply propext; omega
  · brun [h0, h12, pOff]
    simp only [pBase, ite_true]
    refine ⟨ofs_add S _ _, ?_⟩
    rw [ofs_add, ofs_diff, ofNat_sub_beq (by omega) (by decide)]
    congr 1; apply propext; omega

theorem keep_reads {s t : State} {rs : List Reg} (k : Keep rs s t) : t.rd ++ t.wr = s.rd ++ s.wr := by
  rw [k.2.1, k.2.2.1]

theorem round_step {s₀ : State} (E : CipherEnv s₀) (up : Bool) {i : Nat} (hi : i < 16) {u : State}
    (I : CInv s₀ up i u) :
    WP isa (round up) u fun u' => CInv s₀ up (i + 1) u' ∧ u'.z = decide (i + 1 = 16) := by
  have fit := E.fit
  have ho : ord up i < 18 := by cases up <;> simp [ord] <;> omega
  let K := scheduleAt s₀.mem (State.addr (s₀.gpr .r0))
  have u0 : u.gpr .r0 = s₀.gpr .r0 := I.keep.gpr (by decide)
  unfold round
  apply WP.seq
  refine WP.mono (WP.keep [.r1, .r9] (round_head u up (P := pEntry K (ord up i))
    (by rw [I.p, addr_P fit up hi]) (by rw [keep_reads I.keep]; exact E.rd _ (by omega))
    (by rw [I.mem, pEntry_read _ _ ho])) (by cases up <;> decide)) fun v ⟨⟨v1, vm⟩, vk⟩ => ?_
  have kv : Keep cRegs s₀ v := I.keep.trans_sub vk (by decide)
  have Ev : LookEnv v := (E.keep kv (by decide)).look (by rw [vk.gpr (by decide), I.ones])
  apply WP.seq
  refine WP.mono (f_run Ev) fun w ⟨w3, wk, wm⟩ => ?_
  have w0 : w.gpr .r0 = s₀.gpr .r0 := by rw [wk.gpr (by decide), vk.gpr (by decide), u0]
  have w12 : w.gpr .r12 = s₀.gpr .r0 + BitVec.ofNat 32 (pBase up i) := by
    rw [wk.gpr (by decide), vk.gpr (by decide), I.p]
  refine WP.mono (WP.keep [.r1, .r2, .r9, .r12] (round_tail w up _ hi w0 w12) (by
    cases up <;> decide)) fun x ⟨⟨x1, x2, x12, xz, xm⟩, xk⟩ => ?_
  have hK : scheduleAt v.mem (State.addr (v.gpr .r0)) = K := by rw [vm, I.mem, vk.gpr (by decide), u0]
  refine ⟨⟨by omega, x12, ?_, ?_, (kv.trans_sub wk (by decide)).trans_sub xk (by decide),
    by rw [xm, wm, vm, I.mem]⟩, xz⟩
  · have w1 : w.gpr .r1 = u.gpr .r1 ^^^ pEntry K (ord up i) := by rw [wk.gpr (by decide), v1]
    have w2 : w.gpr .r2 = u.gpr .r2 := by rw [wk.gpr (by decide), vk.gpr (by decide)]
    rw [x1, x2, w3, hK, w1, w2, iter_succ, ← I.halves]
    simp only [roundStep]
    rw [BitVec.xor_comm, v1]
  · rw [xk.gpr (by decide), wk.gpr (by decide), vk.gpr (by decide), I.ones]

theorem ones_eq : ((0xFFFF : BitVec 16) ++
    (((0xFFFF : BitVec 16).setWidth 32).extractLsb' 0 16) : BitVec 32) = BitVec.allOnes 32 := by
  decide

theorem cipher_start (s : State) (up : Bool) :
    WP isa (.block (setOnes ++ ([.dp .add pPtr sch (imm (if up then pOff else pOff + 64))] : List Instr))) s fun t =>
      t.gpr .r8 = BitVec.allOnes 32 ∧ t.gpr .r12 = s.gpr .r0 + BitVec.ofNat 32 (pBase up 0) ∧
        t.mem = s.mem := by
  cases up <;> brun [setOnes, pOff, pBase, ones_eq]

theorem rounds_run {s : State} (E : CipherEnv s) (up : Bool) {u : State} (I : CInv s up 0 u) :
    WP isa (.loop (round up) .ne) u (CInv s up 16) := by
  refine WP.loop (M := isa) (Q := CInv s up 16)
    (fun (n : Nat) (v : State) => ∃ i, i < 16 ∧ n = 16 - i ∧ CInv s up i v) ?_ 16 u ⟨0, by decide, rfl, I⟩
  intro n v ⟨i, hi, hn, J⟩
  refine WP.mono (round_step E up hi J) fun v' ⟨J', hz⟩ => ?_
  rw [eval_ne, hz]
  by_cases e : i + 1 = 16
  · left
    exact ⟨by rw [e]; rfl, e ▸ J'⟩
  · right
    exact ⟨by simp [e], n - 1, by omega, i + 1, by omega, by omega, J'⟩

/-- The addresses of the last P-array entries. -/
theorem addr_last {S : BitVec 32} (fit : S.toNat + 4168 ≤ 2 ^ 32) (up : Bool) :
    State.addr (S + BitVec.ofNat 32 (pBase up 16) + BitVec.ofNat 32 (pAt up)) =
        State.addr S + BitVec.ofNat 64 (4096 + 4 * ord up 16) ∧
      State.addr (S + BitVec.ofNat 32 (pBase up 16) + BitVec.ofNat 32 (4 - pAt up)) =
        State.addr S + BitVec.ofNat 64 (4096 + 4 * ord up 17) := by
  constructor <;>
  · rw [ofs_add, addr_add (by cases up <;> simp [pBase, pAt] <;> omega)]
    congr 2; cases up <;> simp [pBase, pAt, ord]

theorem cipher_end (u : State) (up : Bool) {P₁₆ P₁₇ : BitVec 32} {a b : Addr}
    (ha : State.addr (u.gpr .r12 + BitVec.ofNat 32 (pAt up)) = a)
    (hb : State.addr (u.gpr .r12 + BitVec.ofNat 32 (4 - pAt up)) = b)
    (hra : InRegions (u.rd ++ u.wr) a 4) (hrb : InRegions (u.rd ++ u.wr) b 4)
    (h16 : u.mem.readW a 32 = P₁₆) (h17 : u.mem.readW b 32 = P₁₇) :
    WP isa (.block [.ldr tmp pPtr (pAt up), .dp .eor tmp xL (.reg tmp),
        .ldr xL pPtr (4 - pAt up), .dp .eor xL xL (.reg xR), .mov xR (.reg tmp)]) u fun t =>
      t.gpr .r1 = P₁₇ ^^^ u.gpr .r2 ∧ t.gpr .r2 = u.gpr .r1 ^^^ P₁₆ ∧ t.mem = u.mem := by
  have ho : pAt up < 4096 := by cases up <;> decide
  have ho' : 4 - pAt up < 4096 := by cases up <;> decide
  rw [← ha] at hra h16
  rw [← hb] at hrb h17
  brun [ho, ho', hra, hrb, h16, h17]

/-- The block function. -/
theorem cipher_run {s : State} (E : CipherEnv s) (up : Bool) :
    WP isa (cipher up) s fun t =>
      (t.gpr .r1, t.gpr .r2) =
        feistel (scheduleAt s.mem (State.addr (s.gpr .r0))) (ord up) (s.gpr .r1) (s.gpr .r2) ∧
      Keep cRegs s t ∧ t.mem = s.mem := by
  have fit := E.fit
  unfold cipher
  apply WP.seq
  refine WP.mono (WP.keep [.r8, .r12] (cipher_start s up) (by cases up <;> decide))
    fun u ⟨⟨u8, u12, um⟩, uk⟩ => ?_
  have I0 : CInv s up 0 u :=
    ⟨by decide, u12, by rw [uk.gpr (by decide), uk.gpr (by decide)]; rfl, u8, uk.mono (by decide), um⟩
  apply WP.seq
  refine WP.mono (rounds_run E up I0) fun v V => ?_
  obtain ⟨a16, a17⟩ := addr_last fit up
  have hrd := keep_reads V.keep
  let K := scheduleAt s.mem (State.addr (s.gpr .r0))
  have r16 : 4096 + 4 * ord up 16 + 4 ≤ 4168 := by cases up <;> decide
  have r17 : 4096 + 4 * ord up 17 + 4 ≤ 4168 := by cases up <;> decide
  have o16 : ord up 16 < 18 := by cases up <;> decide
  have o17 : ord up 17 < 18 := by cases up <;> decide
  refine WP.mono (WP.keep [.r1, .r2, .r9] (cipher_end v up (P₁₆ := pEntry K (ord up 16))
    (P₁₇ := pEntry K (ord up 17)) (a := State.addr (s.gpr .r0) + BitVec.ofNat 64 (4096 + 4 * ord up 16))
    (b := State.addr (s.gpr .r0) + BitVec.ofNat 64 (4096 + 4 * ord up 17)) (by rw [V.p]; exact a16) (by rw [V.p]; exact a17)
    (by rw [hrd]; exact E.rd _ r16) (by rw [hrd]; exact E.rd _ r17)
    (by rw [V.mem, pEntry_read _ _ o16]) (by rw [V.mem, pEntry_read _ _ o17])) (by cases up <;> decide))
    fun t ⟨⟨t1, t2, tm⟩, tk⟩ => ?_
  refine ⟨?_, V.keep.trans_sub tk (by decide), by rw [tm, V.mem]⟩
  rw [t1, t2, feistel_eq, ← V.halves, BitVec.xor_comm]

end VG.Proof.Blowfish.Arm
