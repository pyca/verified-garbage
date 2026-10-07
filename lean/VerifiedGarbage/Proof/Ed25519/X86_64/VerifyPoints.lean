import VerifiedGarbage.Proof.Ed25519.X86_64.WindowSlide
import VerifiedGarbage.Proof.Ed25519.X86_64.RecodeAll
import VerifiedGarbage.Proof.Ed25519.X86_64.Bits
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCounter
import VerifiedGarbage.Proof.Ed25519.Window
import VerifiedGarbage.Proof.Ed25519.X86_64.PointEqual
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMul
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# Verification's equation, from the windows

`k`'s zero bytes above its low 32 are skipped (`skipZero`, `SkipLoop`), both scalars recoded
(`recodeAll`), and the windows (`EdWindows`) leave a representative of `[k]A - [S]B`, compared
with `-R`: they are equal exactly when `[S]B = R + [k]A`, which, as `A` and `R` represent points
of the group, is the specification's comparison.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open VG.Proof.X25519.X86_64 (off ofs Keeps clob Outside)

variable {fld : Arith} [EdArith fld]

theorem ByteKeep.bytesK {base kp sp T : Addr} {A : EPoint dZ} {s t : State} (h : WinCtx base kp sp T A s)
    (k : ByteKeep base s t) : Spec.Ed25519.bytesAt t.mem kp 64 = Spec.Ed25519.bytesAt s.mem kp 64 :=
  outside_bytes k.mem (by decide) h.kFar

theorem ByteKeep.bytesS {base kp sp T : Addr} {A : EPoint dZ} {s t : State} (h : WinCtx base kp sp T A s)
    (k : ByteKeep base s t) :
    Spec.Ed25519.bytesAt t.mem (off sp 32) 32 = Spec.Ed25519.bytesAt s.mem (off sp 32) 32 :=
  outside_bytes k.mem (by decide) h.sFar

theorem BaseTbl.of_powers {s t : State} {base T : Addr} {o n : Nat} (h : BaseTbl s base T)
    (k : PowersKeep base o n s t) (hn : o + n ≤ 8192) : BaseTbl t base T :=
  h.of_mem k.rd k.wr fun p hp => k.mem p (by omega) (Or.inr (by omega))

theorem counterCmp_ok {s : State} {base : Addr} (hs : Scratch s base) (i : Nat) (hi : i ≤ 64)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i) :
    WP isa (.block [.mov .rbx (.mem (Impl.X25519.X86_64.sc 56)), .alu .cmp .rbx (.imm 32)]) s
      fun t => t.zf = some (decide (i = 32)) ∧ Keeps [.rbx] s t := by
  have hr : InRegions (s.rd ++ s.wr) (off base 56) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by decide) (by decide)⟩
  have hz : (BitVec.ofNat 64 i - (32 : BitVec 32).signExtend 64 == 0) = decide (i = 32) := by
    rw [show (32 : BitVec 32).signExtend 64 = BitVec.ofNat 64 32 from rfl]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    bv_omega_using [hi]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, State.load64,
    Proof.X25519.X86_64.ea_sc, RegUpd.gpr_setReg, RegUpd.zf_arithFlags, hs.rdi, hr, hc, hz,
    ite_true, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem scalar_byte {m : Mem} {p : Addr} {n i : Nat} (hi : i < n) :
    (m (off p i)).toNat = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p n) / 256 ^ i % 256 := by
  rw [decodeLE_byte, input_byte m p n i hi]

/-- Skipping `k`'s zero bytes, with `c` bytes left. -/
structure SkipLoop (s₀ : State) (base kp sp T : Addr) (A : EPoint dZ) (K S c : Nat) (s : State) : Prop where
  ctx : WinCtx base kp sp T A s
  d : env s.mem base 16 = Spec.Ed25519.d
  counter : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 c
  kVal : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) = K
  sVal : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sp 32) 32) = S
  value : Rep (point (env s.mem base) 0 1 2 3) ((K / 256 ^ c) • A + (S / 256 ^ c) • (-baseAff))
  keep : ByteKeep base s₀ s

/-- What moving the counter may change: the counter, and the registers a byte may. -/
structure CounterKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ clob → r ≠ .rbx → r ≠ .rsi → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside base 56 8 s.mem t.mem

theorem CounterKeep.trans {base : Addr} {s t u : State} (h : CounterKeep base s t)
    (k : CounterKeep base t u) : CounterKeep base s u :=
  ⟨fun r a b c => (k.gpr r a b c).trans (h.gpr r a b c), k.rd.trans h.rd, k.wr.trans h.wr,
    h.mem.trans k.mem⟩

theorem CounterKeep.of_keeps {base : Addr} {s t : State} {rs : List Reg} (h : Keeps rs s t)
    (hrs : ∀ r ∈ rs, r = .rbx ∨ r = .rsi ∨ r ∈ clob) : CounterKeep base s t :=
  ⟨fun r hc hb hs => h.1 r fun hm => by
    rcases hrs r hm with rfl | rfl | hm'
    · exact hb rfl
    · exact hs rfl
    · exact hc hm', h.2.2.1, h.2.2.2, fun x _ => by rw [h.2.1]⟩

theorem CounterKeep.byte {base : Addr} {s t : State} (h : CounterKeep base s t) : ByteKeep base s t :=
  ⟨h.gpr, h.rd, h.wr, h.mem.mono (by decide) (by decide)⟩

/-- The loops' invariant, with the counter moved from `c` to `c'` where the scalars'
quotients agree. -/
theorem SkipLoop.of_counter {s₀ s t : State} {base kp sp T : Addr} {A : EPoint dZ} {K S c c' : Nat}
    (h : SkipLoop s₀ base kp sp T A K S c s) (k : CounterKeep base s t)
    (hc : t.mem.readW (off base 56) 64 = BitVec.ofNat 64 c')
    (hK : K / 256 ^ c' = K / 256 ^ c) (hS : S / 256 ^ c' = S / 256 ^ c) :
    SkipLoop s₀ base kp sp T A K S c' t :=
  ⟨h.ctx.of_byte k.byte, by rw [header_env k.mem]; exact h.d, hc,
    by rw [k.byte.bytesK h.ctx, h.kVal], by rw [k.byte.bytesS h.ctx, h.sVal],
    by rw [header_env k.mem, hK, hS]; exact h.value, h.keep.trans k.byte⟩

/-! ## Skipping the leading zero bytes of `k` -/

theorem skipStop_ok {s : State} {base : Addr} (hs : Scratch s base) (j : Nat)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 j) :
    WP isa (.block skipStop) s fun t => t.zf = some true ∧
      t.mem.readW (off base 56) 64 = BitVec.ofNat 64 (j + 1) ∧ CounterKeep base s t := by
  have hw : InRegions s.wr (off base 56) 8 :=
    ⟨_, hs.wr, Offset.contains_base _ (by decide) (by decide)⟩
  have hr : InRegions (s.rd ++ s.wr) (off base 56) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by decide) (by decide)⟩
  have he : BitVec.ofNat 64 j + (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (j + 1) := by
    rw [show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add]
  apply WP.of_runBlock
  simp only [skipStop, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    State.load64, State.store64, Proof.X25519.X86_64.ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.zf_arithFlags, RegUpd.rd_setReg, RegUpd.rd_arithFlags, RegUpd.wr_setReg,
    RegUpd.wr_arithFlags, RegUpd.mem_setReg, RegUpd.mem_arithFlags, hs.rdi, hr, hw, hc, he,
    BitVec.sub_self, ite_true, ite_false, reduceCtorEq, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, Mem.readW_writeW_self64 _ _ _, ⟨fun r hr _ _ => ?_, rfl, rfl,
    VG.Proof.X25519.X86_64.writeW_outside _ _ _ (by decide)⟩⟩
  simp only [RegUpd.gpr_arithFlags, RegUpd.gpr_setReg, show r ≠ .rax from fun h => hr (h ▸ by decide),
    ite_false]

private theorem byte_zero : ∀ b : BitVec 8,
    (b.setWidth 64 &&& b.setWidth 64 == 0) = decide (b.toNat = 0) := by decide

theorem testByte_ok (s : State) (b : BitVec 8) (hc : s.gpr .rbx = b.setWidth 64) :
    WP isa (.block [.alu .test .rbx (.reg .rbx)]) s fun t =>
      t.zf = some (decide (b.toNat = 0)) ∧ Keeps [] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.zf_arithFlags, hc, byte_zero, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun _ _ => rfl, rfl, rfl, rfl⟩

/-- The counter moved down from `j + 1` to `j`, and byte `j` of `k` tested. -/
theorem skipLoad_ok {s : State} {base kp sp T : Addr} {A : EPoint dZ} (h : WinCtx base kp sp T A s)
    (j : Nat) (hj : j < 64) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (j + 1)) :
    WP isa (.block skipLoad) s fun t => t.zf = some (decide ((s.mem (off kp j)).toNat = 0)) ∧
      t.mem.readW (off base 56) 64 = BitVec.ofNat 64 j ∧ CounterKeep base s t := by
  rw [skipLoad, List.append_assoc, WP.block_append_iff]
  refine WP.mono (batchBegin_ok h.scratch j hc) fun a ⟨_, ac, ag, ar, aw, am⟩ => ?_
  have ka : CounterKeep base s a := ⟨fun r _ hb _ => ag r hb, ar, aw, am⟩
  have ha := h.of_byte ka.byte
  rw [WP.block_append_iff]
  refine WP.mono (digitByte_ok ha.scratch 7952 0 (by decide) (by decide) ha.kHeader j ac
    (by rw [off_zero]; exact ha.kRead j hj)) fun b ⟨bv, kb⟩ => ?_
  have hm : a.mem (off kp j) = s.mem (off kp j) := am _ (by have := h.kFar j hj; omega)
  rw [off_zero, hm] at bv
  refine WP.mono (testByte_ok b _ bv) fun t ⟨tz, kt⟩ => ?_
  refine ⟨tz, by rw [kt.2.1, kb.2.1]; exact ac, ka.trans ((CounterKeep.of_keeps kb (by decide)).trans
    (CounterKeep.of_keeps kt (by decide)))⟩

/-- Skipping: `c = 32 + n` bytes are left, and the bytes of `k` from `c` on are zero. -/
def SkipInv (s₀ : State) (base kp sp T : Addr) (A : EPoint dZ) (K S : Nat) (n : Nat) (s : State) : Prop :=
  SkipLoop s₀ base kp sp T A K S (32 + n) s ∧ K / 256 ^ (32 + n) = 0 ∧ 0 < n ∧ n ≤ 32

/-- Whether the skipping goes on below `32 + j + 1` bytes left: byte `32 + j` of `k` is zero,
and more than 32 bytes are left after it. -/
def skipOn (K j : Nat) : Bool := decide (K / 256 ^ (32 + j) % 256 = 0 ∧ j ≠ 0)

/-- Where the skipping stops below `32 + j + 1` bytes left, if it does. -/
def skipEnd (K j : Nat) : Nat := if K / 256 ^ (32 + j) % 256 = 0 then 32 else 32 + (j + 1)

theorem skipEnd_range (K j : Nat) (hj : j < 32) : 32 ≤ skipEnd K j ∧ skipEnd K j ≤ 64 := by
  unfold skipEnd; split <;> omega

theorem skipBody_ok {s₀ t : State} {base kp sp T : Addr} {A : EPoint dZ} {K S j : Nat}
    (h : SkipInv s₀ base kp sp T A K S (j + 1) t) :
    WP isa skipBody t fun u => u.zf.map (!·) = some (skipOn K j) ∧
      (skipOn K j = false → SkipLoop s₀ base kp sp T A K S (skipEnd K j) u ∧ K / 256 ^ skipEnd K j = 0) ∧
      (skipOn K j = true → SkipInv s₀ base kp sp T A K S j u) := by
  obtain ⟨hl, hz, _, hn⟩ := h
  have hS : S < 256 ^ 32 := hl.sVal ▸ decodeLE_lt32 _ _
  have hb : (t.mem (off kp (32 + j))).toNat = K / 256 ^ (32 + j) % 256 := by
    rw [scalar_byte (n := 64) (by omega), hl.kVal]
  rw [skipBody]
  refine WP.seq (WP.mono (skipLoad_ok hl.ctx (32 + j) (by omega) (by rw [hl.counter]; rfl))
    fun a ⟨az, ac, ka⟩ => ?_)
  rw [hb] at az
  refine WP.ite (!decide (K / 256 ^ (32 + j) % 256 = 0)) (by simp only [eval, az, Option.map_some])
    (fun hy => ?_) (fun hy => ?_)
  · have h0 : K / 256 ^ (32 + j) % 256 ≠ 0 := by simpa using hy
    have hoff : skipOn K j = false := by simp only [skipOn, h0, false_and, decide_false]
    refine WP.mono (skipStop_ok (ka.byte.scratch hl.ctx.scratch) (32 + j) ac) fun u ⟨uz, uc, ku⟩ => ?_
    have e : skipEnd K j = 32 + (j + 1) := by simp only [skipEnd, h0, ↓reduceIte]
    refine ⟨by rw [uz, hoff]; rfl, fun _ => ?_, fun ht => absurd ht (by rw [hoff]; decide)⟩
    rw [e]
    exact ⟨hl.of_counter (ka.trans ku) uc rfl rfl, hz⟩
  · have h0 : K / 256 ^ (32 + j) % 256 = 0 := by simpa using hy
    have hK : K / 256 ^ (32 + j) = 0 := by
      have := div_split K (32 + j)
      rw [show 32 + j + 1 = 32 + (j + 1) by omega, hz] at this
      omega
    have hw := hl.of_counter ka ac (by rw [hK, hz]) (by rw [high_zero hS (by omega), high_zero hS (by omega)])
    have he : skipOn K j = decide (j ≠ 0) := by simp only [skipOn, h0, true_and]
    rw [counterCmp]
    refine WP.mono (counterCmp_ok hw.ctx.scratch (32 + j) (by omega) hw.counter) fun u ⟨uz, ku⟩ => ?_
    have hu := hw.of_counter (CounterKeep.of_keeps ku (by decide)) (by rw [ku.2.1]; exact hw.counter) rfl rfl
    refine ⟨by rw [uz, he]; simp, fun hf => ?_, fun ht => ⟨hu, hK, by rw [he] at ht; have := of_decide_eq_true ht; omega,
      by omega⟩⟩
    have hj : j = 0 := by rw [he] at hf; simpa using hf
    subst hj
    have e : skipEnd K 0 = 32 := by simp only [skipEnd, h0, ↓reduceIte]
    rw [e]
    exact ⟨hu, hK⟩

theorem skipZero_ok {s₀ s : State} {base kp sp T : Addr} {A : EPoint dZ} {K S : Nat}
    (h : SkipLoop s₀ base kp sp T A K S 64 s) :
    WP isa skipZero s fun t => ∃ c, 32 ≤ c ∧ c ≤ 64 ∧ SkipLoop s₀ base kp sp T A K S c t ∧
      K / 256 ^ c = 0 := by
  have hK : K / 256 ^ 64 = 0 := Nat.div_eq_of_lt (h.kVal ▸ decodeLE_lt64 _ _)
  rw [skipZero]
  apply WP.loop (SkipInv s₀ base kp sp T A K S) (n := 32)
  · intro n t ht
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := ht.2.2.1; omega : n ≠ 0)
    have hj : j < 32 := by have := ht.2.2.2; omega
    refine WP.mono (skipBody_ok ht) fun u ⟨uz, uf, ut⟩ => ?_
    cases hs : skipOn K j
    · exact Or.inl ⟨by show u.zf.map (!·) = _; rw [uz, hs], skipEnd K j, (skipEnd_range K j hj).1,
        (skipEnd_range K j hj).2, (uf hs).1, (uf hs).2⟩
    · exact Or.inr ⟨by show u.zf.map (!·) = _; rw [uz, hs], j, by omega, ut hs⟩
  · exact ⟨h, hK, by decide, by decide⟩


/-! ## The windows -/

/-- A run of the windows: from a state satisfying `R₀`, after position `p`. -/
def LoopRun (R₀ : State → Prop) (base kp sp T : Addr) (A : EPoint dZ) (fA fB : Nat → Nat) (top p : Nat)
    (x : State) : Prop :=
  ∃ s₀, R₀ s₀ ∧ WinLoop s₀ base kp sp T A fA fB top p x

/-- A run of the windows at their start, one above `top`. -/
def StartRun (R₀ : State → Prop) (base kp sp T : Addr) (A : EPoint dZ) (fA fB : Nat → Nat) (top : Nat)
    (x : State) : Prop :=
  ∃ s₀, R₀ s₀ ∧ SkipAt s₀ base kp sp T A fA fB top (top + 1) x

/-- The windows after the recoding, from one above the top position (the identity accumulated)
to after position 0, as `windows` runs them (`Ifma.windows` too): the loops' invariant, and a
trace that depends on the run's start alone. -/
class EdWindows (win : Prog isa) : Prop where
  ok : ∀ {s₀ s : State} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat} {top : Nat},
    Digits fA fB top → SkipAt s₀ base kp sp T A fA fB top (top + 1) s →
      WP isa win s (WinLoop s₀ base kp sp T A fA fB top 0)
  ct : ∀ {R₀ : State → Prop} {base kp sp T : Addr} {A : EPoint dZ} {fA fB : Nat → Nat} {top : Nat},
    Digits fA fB top →
    RelCT isa (fun x y => StartRun R₀ base kp sp T A fA fB top x ∧ StartRun R₀ base kp sp T A fA fB top y) win
      (fun x y => LoopRun R₀ base kp sp T A fA fB top 0 x ∧ LoopRun R₀ base kp sp T A fA fB top 0 y)

variable {win : Prog isa} [EdWindows win]

theorem PowersKeep.of_byte {base : Addr} {s t : State} (h : ByteKeep base s t) :
    PowersKeep base 56 7752 s t :=
  ⟨fun r hb hs hc => h.gpr r hc hb hs, h.rd, h.wr, TableFrame.table (h.mem.mono (by decide) (by decide))⟩

theorem PowersKeep.of_all {base : Addr} {s t : State} (h : AllKeep base s t) :
    PowersKeep base 56 7752 s t := by
  refine ⟨fun r hb hs hc => h.gpr r ?_, h.rd, h.wr, fun p _ hp => h.mem p ?_⟩
  · simp only [recRegs, List.mem_cons, List.not_mem_nil, or_false]
    rintro (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp_all [clob]
  · omega

theorem WinCtx.of_all {base kp sp T : Addr} {A : EPoint dZ} {s t : State} (h : WinCtx base kp sp T A s)
    (k : AllKeep base s t) : WinCtx base kp sp T A t := by
  have hb := h.scratch.nowrap
  have word (d : Nat) (hd : 3216 ≤ d) (hd' : d + 8 ≤ 8192) :
      t.mem.readW (off base d) 64 = s.mem.readW (off base d) 64 :=
    Mem.readW_congr fun i hi => k.mem _ (Or.inr (Or.inr (by
      rw [VG.Proof.X25519.X86_64.ofs_off base (by omega)]; omega)))
  refine ⟨⟨(k.gpr _ (by decide)).trans h.scratch.rdi, k.wr ▸ h.scratch.wr, hb⟩,
    (word 7952 (by decide) (by decide)).trans h.kHeader, (word 7944 (by decide) (by decide)).trans h.sHeader,
    fun i hi => by rw [k.rd, k.wr]; exact h.kRead i hi, fun i hi => by rw [k.rd, k.wr]; exact h.sRead i hi,
    h.kFar, h.sFar, fun i hi => by rw [k.rd, k.wr]; exact h.kRead8 i hi,
    fun i hi => by rw [k.rd, k.wr]; exact h.sRead8 i hi, fun e he => ?_,
    (word 7960 (by decide) (by decide)).trans h.bHeader,
    h.bTab.of_mem k.rd k.wr fun p hp => k.mem p (Or.inr (Or.inr (by omega)))⟩
  obtain ⟨q, hq, hr⟩ := h.aTab e he
  have tf : TableFrame base 56 3160 s.mem t.mem := fun p _ hp => k.mem p (by omega)
  exact ⟨q, by rw [tf.point (by omega) (Or.inr (by omega)) (by omega)]; exact hq, hr⟩

theorem negR_eval (e : Env) :
    point (evalOps [.const 8 0, .sub 4 8 4, .sub 7 8 7] e) 0 1 2 3 = point e 0 1 2 3 ∧
    point (evalOps [.const 8 0, .sub 4 8 4, .sub 7 8 7] e) 4 5 6 7 = negPoint (point e 4 5 6 7) :=
  ⟨rfl, rfl⟩

/-- `-R`, beside the accumulator. -/
theorem negR_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (.block (negR fld)) s fun t => Keep base s t ∧
      point (env t.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 ∧
      point (env t.mem base) 4 5 6 7 = negPoint (tablePoint s.mem base 7552) := by
  rw [negR, List.append_assoc, WP.block_append_iff]
  refine WP.mono (tableStart_ok hs.rdi 7552) fun a ⟨ap, ka⟩ => ?_
  have kae : Keep base s a := Keep.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pointFromTableQ_ok (hs.of_keep kae) ap (by decide) (by decide)) fun b ⟨pb, kb⟩ => ?_
  have kbe := Keep.of_tableQ kb
  have b_low : ∀ i : Slot, i.val < 4 → env b.mem base i = env s.mem base i := by
    intro i hi
    change Proof.X25519.X86_64.F b.mem base (offset i) = Proof.X25519.X86_64.F s.mem base (offset i)
    rw [Outside_F kb.mem (by simp only [offset]; omega) (Or.inl (by simp only [offset]; omega)), ka.2.1]
  refine WP.mono (fieldCodeWide_ok ((hs.of_keep kae).of_keep kbe) _) fun t ⟨kt, vt⟩ => ?_
  refine ⟨(kae.trans kbe).trans kt, ?_, ?_⟩
  · rw [vt, (negR_eval _).1]
    simp only [point, b_low 0 (by decide), b_low 1 (by decide), b_low 2 (by decide),
      b_low 3 (by decide)]
  · rw [vt, (negR_eval _).2, pb, ka.2.1]

/-- Verification's code before the windows, regrouped. -/
def windowPrep (fld : Arith) : Prog isa :=
  .seq (.seq (.block windowSetup) (aTable fld)) (.block (windowInit fld))

/-- Before the windows: the tables, an accumulator representing `0` and the counter at 64. -/
theorem windowPrep_ok {s : State} {base sig challenge : Addr} {Aa : EPoint dZ}
    (hs : Scratch s base)
    (hp : s.mem.readW (off base 7944) 64 = sig)
    (hc : s.mem.readW (off base 7952) 64 = challenge)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off sig 32) i) 1)
    (hf : ∀ i < 32, 8192 ≤ ofs base (off (off sig 32) i))
    (hcr : ∀ i < 64, InRegions (s.rd ++ s.wr) (off challenge i) 1)
    (hcf : ∀ i < 64, 8192 ≤ ofs base (off challenge i))
    (hcr8 : ∀ j < 8, InRegions (s.rd ++ s.wr) (off challenge (8 * j)) 8)
    (hsr8 : ∀ j < 4, InRegions (s.rd ++ s.wr) (off sig (32 + 8 * j)) 8)
    (hA : Rep (tablePoint s.mem base 7424) Aa) {T : Addr} (hT : s.mem.readW (off base 7960) 64 = T)
    (hbt : BaseTbl s base T) :
    WP isa (windowPrep fld) s fun e => SkipLoop e base challenge sig T Aa
      (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64))
      (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32)) 64 e ∧
      PowersKeep base 56 7752 s e ∧ tablePoint e.mem base 7552 = tablePoint s.mem base 7552 := by
  rw [windowPrep]
  -- The constant `d`.
  refine WP.seq (WP.seq (WP.mono (constFieldWide_ok hs 16 Spec.Ed25519.d) fun a ⟨ka, va⟩ => ?_))
  have ad : env a.mem base 16 = Spec.Ed25519.d := by rw [va]; exact Function.update_self ..
  have aA : tablePoint a.mem base 7424 = tablePoint s.mem base 7424 :=
    workspace_tablePoint ka.mem (by decide) (by decide)
  have aR : tablePoint a.mem base 7552 = tablePoint s.mem base 7552 :=
    workspace_tablePoint ka.mem (by decide) (by decide)
  have ksa : PowersKeep base 56 7752 s a := PowersKeep.of_keep ka
  -- The multiples of `A`.
  refine WP.mono (aTable_ok (ksa.scratch hs) ad (by rw [aA]; exact hA)) fun b hb => ?_
  have ksb := ksa.trans (hb.keep.mono (by decide) (by decide))
  have bR : tablePoint b.mem base 7552 = tablePoint s.mem base 7552 := by
    rw [hb.keep.mem.point (by decide) (Or.inr (by decide)) (by decide), aR]
  have cA : TableOf cache b.mem base 5376 Aa := fun e he => hb.table e he
  -- The accumulator and the byte counter.
  rw [windowInit, WP.block_append_iff]
  refine WP.mono (fieldCodeWide_ok (ksb.scratch hs) (constPointOps Spec.Ed25519.identity))
    fun d ⟨kd, vd⟩ => ?_
  have kcd : PowersKeep base 56 7752 b d := PowersKeep.of_keep kd
  refine WP.mono (mulCounterInit_ok ((ksb.trans kcd).scratch hs) 64) fun e ⟨ec, eg, er, ew, em⟩ => ?_
  have kde : ByteKeep base d e :=
    ⟨fun r _ _ _ => eg r (by rintro rfl; contradiction), er, ew, em.mono (by decide) (by decide)⟩
  have kce : ByteKeep base b e := (ByteKeep.of_win (WinKeep.of_keep kd)).trans kde
  have kse := ksb.trans (PowersKeep.of_byte kce)
  have eR : tablePoint e.mem base 7552 = tablePoint s.mem base 7552 := by
    rw [win_tablePoint kce.mem (by decide) (by decide), bR]
  have ed : env e.mem base 16 = Spec.Ed25519.d := by rw [header_env em, vd]; exact hb.d
  have ctx : WinCtx base challenge sig T Aa e :=
    ⟨kse.scratch hs, (kse.header (by decide) (by decide) (by decide)).trans hc,
      (kse.header (by decide) (by decide) (by decide)).trans hp,
      fun i hi => by rw [kse.rd, kse.wr]; exact hcr i hi,
      fun i hi => by rw [kse.rd, kse.wr]; exact hr i hi, hcf, hf,
      fun i hi => by rw [kse.rd, kse.wr]; exact hcr8 i hi,
      fun i hi => by rw [kse.rd, kse.wr]; exact hsr8 i hi,
      cA.of_win kce.mem (by decide) (by decide),
      (kse.header (by decide) (by decide) (by decide)).trans hT, hbt.of_powers kse (by decide)⟩
  have hK : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt e.mem challenge 64) < 256 ^ 64 := by
    have h := decodeLE_lt (Spec.Ed25519.bytesAt e.mem challenge 64)
    rwa [show (Spec.Ed25519.bytesAt e.mem challenge 64).length = 64 by
      simp [Spec.Ed25519.bytesAt]] at h
  have hS := decodeLE_lt32 e.mem (off sig 32)
  have eK := outside_bytes (tableFrame_work kse.mem (by decide) (by decide)) (by decide) hcf
  have eS := outside_bytes (tableFrame_work kse.mem (by decide) (by decide)) (by decide) hf
  refine ⟨⟨ctx, ed, ec, by rw [eK], by rw [eS], ?_, ⟨fun _ _ _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩⟩,
    kse, eR⟩
  rw [← eK, ← eS, Nat.div_eq_of_lt hK, Nat.div_eq_of_lt (Nat.lt_trans hS (by decide)), zero_smul,
    zero_smul, add_zero, header_env em, vd, constPoint_eval]
  exact identity_rep

/-- The windows' start, from the recoded digits. -/
theorem skipAt_of_recode {s₀ f g : State} {base kp sp T : Addr} {A : EPoint dZ} {K S c : Nat}
    (hf : SkipLoop s₀ base kp sp T A K S c f) (hK : K / 256 ^ c = 0) (hc32 : 32 ≤ c) (hc64 : c ≤ 64)
    (k : AllKeep base f g) (hdig : DigitsAre g.mem base (Recode.digits 5 K (8 * c)) (Recode.digits 8 S (8 * 32)))
    (hcount : g.mem.readW (off base 56) 64 = BitVec.ofNat 64 (8 * c + 9)) :
    SkipAt g base kp sp T A (Recode.digits 5 K (8 * c)) (Recode.digits 8 S (8 * 32)) (8 * c + 8)
      (8 * c + 8 + 1) g := by
  have hb := hf.ctx.scratch.nowrap
  have hS : S < 256 ^ 32 := hf.sVal ▸ decodeLE_lt32 _ _
  have henv : env g.mem base = env f.mem base := by
    funext i
    simp only [env, Proof.X25519.X86_64.F, Proof.X25519.X86_64.fe]
    have w (d : Nat) (hd : 64 ≤ d) (hd' : d + 8 ≤ 2048) :
        Proof.X25519.X86_64.word g.mem base d = Proof.X25519.X86_64.word f.mem base d :=
      Mem.readW_congr fun j hj => k.mem _ (Or.inr (Or.inl ⟨by
        rw [VG.Proof.X25519.X86_64.ofs_off base (by omega)]; omega, by
        rw [VG.Proof.X25519.X86_64.ofs_off base (by omega)]; omega⟩))
    have hi := i.isLt
    simp only [offset]
    rw [w _ (by omega) (by omega), w _ (by omega) (by omega), w _ (by omega) (by omega),
      w _ (by omega) (by omega)]
  have h0 : Rep (point (env g.mem base) 0 1 2 3) 0 := by
    have v := hf.value
    rw [hK, Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hS (Nat.pow_le_pow_right (by decide) hc32)), zero_smul,
      zero_smul, add_zero] at v
    rw [henv]; exact v
  have htop : winVal A (Recode.digits 5 K (8 * c)) (Recode.digits 8 S (8 * 32)) (8 * c + 8) (8 * c + 8 + 1) = 0 := by
    simp only [winVal, hiVal, Nat.sub_self, Recode.hsum_zero, zero_smul, add_zero]
  refine ⟨⟨hf.ctx.of_all k, by rw [henv]; exact hf.d, by rw [hcount], hdig, by rw [htop]; exact h0.proj,
    ByteKeep.refl _ _⟩, fun j h1 h2 => by omega, h0, by omega, le_refl _⟩

theorem verifyEquationPoints_ok {s : State} {base sig challenge : Addr} {Aa Ra : EPoint dZ}
    (hs : Scratch s base)
    (hp : s.mem.readW (off base 7944) 64 = sig)
    (hc : s.mem.readW (off base 7952) 64 = challenge)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off sig 32) i) 1)
    (hf : ∀ i < 32, 8192 ≤ ofs base (off (off sig 32) i))
    (hcr : ∀ i < 64, InRegions (s.rd ++ s.wr) (off challenge i) 1)
    (hcf : ∀ i < 64, 8192 ≤ ofs base (off challenge i))
    (hcr8 : ∀ j < 8, InRegions (s.rd ++ s.wr) (off challenge (8 * j)) 8)
    (hsr8 : ∀ j < 4, InRegions (s.rd ++ s.wr) (off sig (32 + 8 * j)) 8)
    (hA : Rep (tablePoint s.mem base 7424) Aa) (hR : Rep (tablePoint s.mem base 7552) Ra)
    {T : Addr} (hT : s.mem.readW (off base 7960) 64 = T) (hbt : BaseTbl s base T) :
    WP isa (verifyEquationPoints fld win) s fun t => PowersKeep base 56 7752 s t ∧
      t.gpr .rax = signWord (Spec.Ed25519.pointEqual
        (Spec.Ed25519.pointMul
          (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32)) Spec.Ed25519.basePoint)
        (Spec.Ed25519.pointAdd (tablePoint s.mem base 7552)
          (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64))
            (tablePoint s.mem base 7424)))) := by
  rw [verifyEquationPoints]
  apply WP.assoc; apply WP.assoc
  refine WP.seq (WP.mono (windowPrep_ok hs hp hc hr hf hcr hcf hcr8 hsr8 hA hT hbt) fun e ⟨w0, kse, eR⟩ => ?_)
  generalize hKd : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64) = K at w0 ⊢
  generalize hSd : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32) = S at w0 ⊢
  -- `k`'s zero bytes.
  refine WP.seq (WP.mono (skipZero_ok w0) fun f ⟨c, hc32, hc64, hf', hK⟩ => ?_)
  -- The digits.
  have fctx := hf'.ctx
  refine WP.seq (WP.mono (recodeAll_ok fctx.scratch hf'.counter hc32 hc64 fctx.kHeader fctx.sHeader
    fctx.kRead8 fctx.sRead8 fctx.kFar (fun j hj => by
      rw [show off sig (32 + j) = off (off sig 32) j from (Offset.add_add _ _ _).symm]; exact fctx.sFar j hj))
    fun g ⟨gA, gB, gc, kg⟩ => ?_)
  rw [hf'.kVal] at gA
  rw [hf'.sVal] at gB
  have gdig : DigitsAre g.mem base (Recode.digits 5 K (8 * c)) (Recode.digits 8 S (8 * 32)) :=
    fun p hp => ⟨gA p hp, gB p hp⟩
  have hg := skipAt_of_recode hf' hK hc32 hc64 kg gdig gc
  have hdg : Digits (Recode.digits 5 K (8 * c)) (Recode.digits 8 S (8 * 32)) (8 * c + 8) :=
    ⟨by omega, fun p => Recode.digits_le (by decide) p, fun p => Recode.digits_le (by decide) p⟩
  -- The windows.
  refine WP.seq (WP.mono (EdWindows.ok hdg hg) fun h hh => ?_)
  have ksh := ((kse.trans (PowersKeep.of_byte hf'.keep)).trans (PowersKeep.of_all kg)).trans
    (PowersKeep.of_byte hh.keep)
  -- The comparison with `-R`.
  refine WP.seq (WP.mono (negR_ok (ksh.scratch hs)) fun u ⟨ku, u0, u4⟩ => ?_)
  have ksu := ksh.trans (PowersKeep.of_keep ku)
  refine WP.mono (pointEqual_ok (ksu.scratch hs)) fun t ⟨kt, tv⟩ => ?_
  refine ⟨ksu.trans (PowersKeep.of_keep kt), ?_⟩
  have hKlt : K < 2 ^ (8 * c) := by
    have := Nat.lt_of_div_eq_zero (by positivity) hK
    rwa [show (256 : Nat) ^ c = 2 ^ (8 * c) by rw [Nat.pow_mul]] at this
  have hSlt : S < 2 ^ (8 * 32) := hSd ▸ decodeLE_lt32 _ _
  have gv := hh.value
  simp only [winVal, hiVal, Nat.sub_zero] at gv
  rw [Recode.digits_sum (by decide) hKlt (by omega), Recode.digits_sum (by decide) hSlt (by omega),
    natCast_zsmul, natCast_zsmul] at gv
  have tf : TableFrame base 56 3160 f.mem g.mem := fun p _ hp => kg.mem p (by omega)
  have hR' : tablePoint h.mem base 7552 = tablePoint s.mem base 7552 := by
    rw [win_tablePoint hh.keep.mem (by decide) (by decide), tf.point (by decide) (Or.inr (by decide)) (by decide),
      win_tablePoint hf'.keep.mem (by decide) (by decide), eR]
  rw [tv, u0, u4, hR', ← hKd, ← hSd]
  rw [← hKd, ← hSd] at gv
  exact congrArg signWord (window_equation hA hR gv hR.neg.proj)

end VG.Proof.Ed25519.X86_64
