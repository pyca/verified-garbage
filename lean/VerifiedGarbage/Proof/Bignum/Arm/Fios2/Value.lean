module

public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Arm.FiosState
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Impl.Bignum.Arm.MontCallWith
public import VerifiedGarbage.Proof.Bignum.Arm.MontCallWithLaw
public import VerifiedGarbage.Proof.Bignum.Arm.MontCallEntry
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.Inline
public import VerifiedGarbage.Impl.Bignum.Arm.Fios2
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Bignum.Arm.FiosArithmetic
import VerifiedGarbage.Proof.Bignum.Arm.MontCallCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.SquareOpCT
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Proof.Bignum.Arm.MontState
public import VerifiedGarbage.Impl.Bignum.Arm.MontPipeline
public import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineLoop

/-! ### `Bignum.Arm.Fios2.Mac`, which the modules that import this one used -/

section

/-! ### `Bignum.Arm.MontPipelinePair`, which the modules that import this one used -/

section

/-! # Rounds of two rows

A round may do the rows of two words of the first operand at once (the
operand's word count is even): its contract is `RoundPost`'s, with the
header two rounds on and the accumulator divided by `2⁶⁴` after adding both
words' products and a two-word multiple of the modulus. Its loop reaches the
same invariant as a loop of single rounds. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.MontPipeline
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

structure PairPost (s t : State) (base : BitVec 32) (tmp a b mod acc n i : Nat) (inv : BitVec 32) : Prop where
  hdr : RoundMeta t.mem base tmp a b mod acc n (i + 2) inv
  ptr : t.gpr .r0 = base + BitVec.ofNat 32 tmp
  value : ∃ q < 2 ^ 64, 2 ^ 64 * val32 t.mem (State.addr base) acc (n + 2) =
    val32 s.mem (State.addr base) acc (n + 2) +
      (w32 s.mem (State.addr base) (a + 4 * i) + 2 ^ 32 * w32 s.mem (State.addr base) (a + 4 * i + 4)) *
        val32 s.mem (State.addr base) b n +
      q * val32 s.mem (State.addr base) mod n
  bound : val32 t.mem (State.addr base) acc (n + 2) < 2 * val32 s.mem (State.addr base) mod n
  outside : Outs (State.addr base) [(acc, 4 * (n + 2)), (tmp + 16, 8)] s.mem t.mem
  zero : t.z = decide (i + 2 = n)
  rest : Rest roundClobbers s t

/-- A round of two rows, from an even round index. -/
def PairLaw (round : Prog isa) : Prop :=
  ∀ (s : State) {base : BitVec 32} {size tmp a b mod acc n i : Nat} {inv : BitVec 32},
    RoundCtx s base size tmp a b mod acc n → n % 2 = 0 →
    RoundMeta s.mem base tmp a b mod acc n i inv → i + 2 ≤ n →
    s.gpr .r0 = base + BitVec.ofNat 32 tmp →
    val32 s.mem (State.addr base) acc (n + 2) < 2 * val32 s.mem (State.addr base) mod n →
    val32 s.mem (State.addr base) b n < val32 s.mem (State.addr base) mod n →
    (val32 s.mem (State.addr base) mod n * inv.toNat + 1) % 2 ^ 32 = 0 →
    WP isa round s fun t => PairPost s t base tmp a b mod acc n i inv

/-- `round_step` for two rows. -/
theorem pair_step {P T T' a b u m A : Nat} (h : 2 ^ 64 * T' = T + a * b + u * m)
    (hI : P * T % m = A * b % m) : P * 2 ^ 64 * T' % m = (A + P * a) * b % m := by
  have e : P * 2 ^ 64 * T' = P * T + P * a * b + P * u * m := by
    rw [Nat.mul_assoc, h, Nat.mul_add, Nat.mul_add, Nat.mul_assoc P a, Nat.mul_assoc P u]
  rw [e, Nat.add_mul_mod_self_right, Nat.add_mod, hI, ← Nat.add_mod, Nat.add_mul]

/-- Two rows keep the accumulator below `2m`. -/
theorem pair_lt {T T' A b U m : Nat} (h : 2 ^ 64 * T' = T + A * b + U * m) (hT : T < 2 * m)
    (hA : A < 2 ^ 64) (hb : b < m) (hU : U < 2 ^ 64) : T' < 2 * m := by
  have h1 : A * b ≤ (2 ^ 64 - 1) * (m - 1) := Nat.mul_le_mul (by omega_arith) (by omega_arith)
  have h2 : U * m ≤ (2 ^ 64 - 1) * m := Nat.mul_le_mul_right _ (by omega_arith)
  have : 2 ^ 64 * T' < 2 ^ 64 * (2 * m) := by omega_arith
  exact Nat.lt_of_mul_lt_mul_left this

theorem pairBody_ok (round : Prog isa) (law : PairLaw round) {s0 s : State} {base : BitVec 32}
    {size tmp a b mod acc n i : Nat} {inv : BitVec 32}
    (ctx : RoundCtx s0 base size tmp a b mod acc n) (even : n % 2 = 0)
    (h : MontInv s0 base tmp a b mod acc n i inv s) (hi : i + 2 ≤ n)
    (hB : val32 s0.mem (State.addr base) b n < val32 s0.mem (State.addr base) mod n)
    (hInv : (val32 s0.mem (State.addr base) mod n * inv.toNat + 1) % 2 ^ 32 = 0) :
    WP isa round s fun t => MontInv s0 base tmp a b mod acc n (i + 2) inv t ∧
      t.z = decide (i + 2 = n) := by
  have nowrap := ctx.workspace.nowrap
  have fa := ctx.aFits
  have fb := ctx.bFits
  have fm := ctx.mFits
  have aa := ctx.accA
  have ab := ctx.accB
  have am := ctx.accM
  have ta := ctx.tmpA
  have tb := ctx.tmpB
  have tm := ctx.tmpM
  have oldB := h.outside.val32 (d := b) (k := n) (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega_arith) (by omega_arith)
  have oldM := h.outside.val32 (d := mod) (k := n) (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega_arith) (by omega_arith)
  have oldA0 := outs_word32 h.outside (d := a + 4 * i) (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega_arith) (by omega_arith)
  have oldA1 := outs_word32 h.outside (d := a + 4 * i + 4) (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega_arith) (by omega_arith)
  refine WP.mono (law s (ctx.congr h.rest.wr) even h.hdr hi h.ptr
    (by rw [oldM]; exact h.bound) (by rw [oldB, oldM]; exact hB) (by rw [oldM]; exact hInv)) ?_
  intro t post
  obtain ⟨q, _, value⟩ := post.value
  rw [oldA0, oldA1, oldB, oldM] at value
  refine ⟨⟨by omega_arith, post.hdr, post.ptr, ?_, ?_, h.outside.trans post.outside,
    h.rest.trans post.rest⟩, post.zero⟩
  · have pw : 2 ^ (32 * (i + 2)) = 2 ^ (32 * i) * 2 ^ 64 := by
      rw [show 32 * (i + 2) = 32 * i + 64 by omega_arith]; exact Nat.pow_add 2 (32 * i) 64
    have va : val32 s0.mem (State.addr base) a (i + 2) = val32 s0.mem (State.addr base) a i +
        2 ^ (32 * i) * (w32 s0.mem (State.addr base) (a + 4 * i) +
          2 ^ 32 * w32 s0.mem (State.addr base) (a + 4 * i + 4)) := by
      rw [val32_append]
      simp only [val32, Nat.mul_zero, Nat.add_zero]
    rw [pw, va]
    exact pair_step value h.value
  · simpa only [oldM] using post.bound

theorem pair_rounds_ok (round : Prog isa) (law : PairLaw round) (s : State) {base : BitVec 32}
    {size tmp a b mod acc n : Nat} {inv : BitVec 32}
    (ctx : RoundCtx s base size tmp a b mod acc n) (even : n % 2 = 0)
    (hdr : RoundMeta s.mem base tmp a b mod acc n 0 inv)
    (ptr : s.gpr .r0 = base + BitVec.ofNat 32 tmp)
    (hzero : val32 s.mem (State.addr base) acc (n + 2) = 0)
    (hB : val32 s.mem (State.addr base) b n < val32 s.mem (State.addr base) mod n)
    (hInv : (val32 s.mem (State.addr base) mod n * inv.toNat + 1) % 2 ^ 32 = 0) :
    WP isa (VG.Impl.Bignum.Arm.MontPipeline.rounds round) s (MontInv s base tmp a b mod acc n n inv) := by
  have hn := ctx.count
  let loopInv := fun k t => ∃ i, i + 2 * k = n ∧ 0 < k ∧ MontInv s base tmp a b mod acc n i inv t
  unfold VG.Impl.Bignum.Arm.MontPipeline.rounds
  refine WP.loop (M := isa) loopInv ?_ (n / 2) s ?_
  · intro k t h
    obtain ⟨i, hik, hk, hi⟩ := h
    refine WP.mono (pairBody_ok round law ctx even hi (by omega_arith) hB hInv) ?_
    rintro u ⟨hu, hz⟩
    by_cases he : i + 2 = n
    · left
      refine ⟨?_, he ▸ hu⟩
      change some (!u.z) = some false
      simp only [hz, he, decide_true, Bool.not_true]
    · right
      refine ⟨?_, k - 1, by omega_arith, i + 2, by omega_arith, by omega_arith, hu⟩
      change some (!u.z) = some true
      simp only [hz, he, decide_false, Bool.not_false]
  · refine ⟨0, by omega_arith, by omega_arith, ?_⟩
    refine ⟨by omega_arith, hdr, ptr, ?_, ?_, Outs.refl _ _ _, Rest.refl _ _⟩
    · rw [hzero]
      simp only [val32, Nat.mul_zero, Nat.zero_mul, Nat.zero_mod]
    · rw [hzero]
      omega_arith

theorem PairLaw.loop {round : Prog isa} (law : PairLaw round) : LoopLaw round :=
  fun s _ _ _ _ _ _ _ _ _ ctx even hdr ptr hzero hB hInv => pair_rounds_ok round law s ctx even hdr ptr hzero hB hInv

end VG.Proof.Bignum.Arm.MontPipeline

end

end

/-! ### `Bignum.Arm.MontCallWithCT`, which the modules that import this one used -/

section

/-! Constant-time AAPCS framing of a verified Montgomery dispatcher. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt Operand)

theorem montCallWithFn_ct (arithmetic : Prog isa) (law : CallArithmeticLaw arithmetic) {base : BitVec 32} {len w o a b : Nat}
    (ho : Operand o) (ha : Operand a) (hb : Operand b) :
    RelCT isa (fun s t => CallInput base len w o a b s ∧ CallInput base len w o a b t ∧ s.sp = t.sp)
      (MontCallWith.code arithmetic) (fun _ _ => True) := by
  unfold MontCallWith.code
  apply RelCT.frame (fun _ _ h => h.2.2)
  intro s t tr1 tr2 u v hp e1 e2
  obtain ⟨s0, t0, ⟨hs, ht, sp⟩, ps, pt⟩ := hp
  have ps' := push_pushed (rs := MontCall.savedRegs) (by decide) hs.stackFit
  have pt' := push_pushed (rs := MontCall.savedRegs) (by decide) ht.stackFit
  have es : callPushed s0 = s := Option.some.inj (ps'.symm.trans ps)
  have et : callPushed t0 = t := Option.some.inj (pt'.symm.trans pt)
  subst s; subst t
  cases e1 with
  | seq entry1 tail1 =>
    cases e2 with
    | seq entry2 tail2 =>
      obtain ⟨trace, sp'⟩ := loadStack_ct .r12 40 _ _ _ _ _ _ (by simp only [callPushed, pushed_sp, sp]) entry1 entry2
      obtain ⟨_, s1, run1, ready1, mem1, rest1⟩ := call_entry_ok s0 hs hb.1
      obtain ⟨_, t1, run2, ready2, mem2, rest2⟩ := call_entry_ok t0 ht hb.1
      obtain ⟨-, rfl⟩ := Exec.det entry1 run1
      obtain ⟨-, rfl⟩ := Exec.det entry2 run2
      have hw : 2 ≤ w := hs.width ▸ hs.layout.1
      have fit : arrAt w 8 ≤ 8 * len := hs.width ▸ hs.layout.2.2.1
      have tmpFits : arrAt w 3 + 32 ≤ 8 * len := by
        have := array_end_le (w := w) (j := 3) (k := 8) (by decide)
        omega_using [hw, fit, this]
      have body := relCT_keep_sp (law.ct (base := base) ho ha hb tmpFits) (fun _ _ h => h.2.2)
      obtain ⟨tailTrace, _⟩ := body.seq montCallRestore_ct _ _ _ _ _ _
        ⟨callBodyReady_of_entry s0 hs _ ready1 mem1 rest1,
          callBodyReady_of_entry t0 ht _ ready2 mem2 rest2, sp'⟩ tail1 tail2
      exact ⟨by rw [trace, tailTrace], trivial⟩

end VG.Proof.Bignum.Arm

end

end

/-! One word of `b` or `m` times a row's scalar into the word in flight. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios2
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_ldr)

/-- `macAt p k c x`: `r6 + 2³² c` becomes the word at `p + k` times `x`
plus `r6` and `c`; only `r3`, `r6` and `c` change. -/
theorem macAt_ok (s : State) {base : BitVec 32} {size o k : Nat} {p c x : Reg}
    (ws : Workspace s base size) (pp : s.gpr p = base + BitVec.ofNat 32 o)
    (fit : o + k + 4 ≤ size) (hk : k < 4096)
    (c6 : c ≠ .r6) (c3 : c ≠ .r3) (x3 : x ≠ .r3) :
    WP isa (VG.Impl.Bignum.Arm.Fios2.macAt p k c x) s fun t =>
      (t.gpr .r6).toNat + 2^32 * (t.gpr c).toNat =
        w32 s.mem (State.addr base) (o + k) * (s.gpr x).toNat + (s.gpr .r6).toNat + (s.gpr c).toNat ∧
      t.mem = s.mem ∧ Rest [.r3, .r6, c] s t := by
  rw [VG.Impl.Bignum.Arm.Fios2.macAt, WP.seq_iff]
  refine wp_ldr (a := off (State.addr base) (o + k)) hk (ws.ea pp (by omega_using [fit])) (ws.read fit)
    fun u hu => WP.block_nil ?_
  refine WP.mono (Fios.umaal_ok u .r6 c .r3 x (Ne.symm c6)) ?_
  rintro t ⟨value, frame⟩
  rw [hu.gpr, hu.other x x3, hu.other .r6 (by decide), hu.other c c3] at value
  refine ⟨by simpa only [w32] using value, frame.mem.trans hu.mem, ?_⟩
  exact (hu.rest (by simp)).trans
    ⟨fun r hr => frame.regs r (by simp_all), frame.rd, frame.wr, frame.sp⟩

end VG.Proof.Bignum.Arm.Fios2

end

end

/-! ### `Bignum.Arm.Fios2.State`, which the modules that import this one used -/

section

/-! ### `Bignum.Arm.MontCallWithFn`, which the modules that import this one used -/

section

/-! # Callable Montgomery multiplication preserves the ARM procedure-call ABI -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt wOf numAt Operand Keeps)

theorem montCallWithFn_ok (arithmetic : Prog isa) (law : CallArithmeticLaw arithmetic) (s : State) {base : BitVec 32} {len w o a b : Nat}
    (h : CallInput base len w o a b s) (ho : Operand o) (ha : Operand a) (hb : Operand b) :
    WP isa (MontCallWith.code arithmetic) s fun t => abiPreserved s t ∧
      numAt t.mem (State.addr base) w o < numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w o * 2 ^ (64 * w) % numAt s.mem (State.addr base) w 0 =
        numAt s.mem (State.addr base) w a * numAt s.mem (State.addr base) w b % numAt s.mem (State.addr base) w 0 ∧
      Keeps (State.addr base) len w o s.mem t.mem := by
  have nowrap := h.workspace.nowrap
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have eq := h.pushed_eq
  have framePush := FrameStack.pushed_frameA (rs := MontCall.savedRegs) h.stackFit
  unfold MontCallWith.code
  refine WP.frame (by decide) h.stackFit (by decide) ?_
  rw [WP.seq_iff]
  refine WP.mono (call_entry_ok s h hb.1) ?_
  rintro u ⟨ready, memU, restU⟩
  rw [WP.seq_iff]
  have savedPush := call_push_saved s h.stackFit
  have stackRead : InRegions (u.rd ++ u.wr) (State.addr u.sp) 4 := by
    rw [restU.rd, restU.wr, restU.sp]
    refine ⟨⟨State.addr (callPushed s).sp, 40⟩, List.mem_append_right _ List.mem_cons_self, ?_⟩
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
  have stackSep : Region.Disjoint ⟨State.addr u.sp, 4⟩ ⟨State.addr base, 8 * len⟩ := by
    rw [restU.sp]
    exact h.stackWorkspace.sub_left (Region.sub_prefix (by decide))
  have savedBase : u.mem.readW (State.addr u.sp) 32 = base := by
    rw [memU, restU.sp]
    change (callPushed s).mem.readW (State.addr (s.sp - 40)) 32 = base
    simpa only [BitVec.add_zero] using (savedPush (.r0, 0) (by decide)).trans h.ptr
  have callReady : CallBodyReady base len w o a b u := ⟨ready, stackRead, stackSep, savedBase⟩
  have body := law.correct u callReady ho ha hb
  refine WP.mono body ?_
  rintro v ⟨lt, value, keeps, frameBody, restV⟩
  have spV : v.sp = s.sp - BitVec.ofNat 32 40 := restV.sp.trans restU.sp
  have wrV : v.wr = (callPushed s).wr := restV.wr.trans restU.wr
  rw [memU] at lt value keeps frameBody
  have saved : Spill.Saved v.mem (State.addr v.sp) s.gpr callAllSaved := by
    rw [spV]
    have savedPush : Spill.Saved (callPushed s).mem (State.addr (s.sp - BitVec.ofNat 32 40)) s.gpr callAllSaved :=
      call_push_saved s h.stackFit
    exact savedPush.frame (lo := 0) (hi := 40) (by decide) frameBody (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      simpa only [FrameStack.belowA, BitVec.add_zero, Nat.sub_zero] using h.stackWorkspace)
  have stackFit : v.sp.toNat + 40 ≤ 2 ^ 32 := by
    rw [spV, FrameStack.sub_toNat' h.stackFit]
    have := s.sp.isLt
    omega_using []
  have writable : (⟨State.addr v.sp, 40⟩ : Region) ∈ v.wr := by
    rw [wrV, spV]
    exact List.mem_cons_self
  refine WP.mono (call_restore_ok v s.gpr stackFit ⟨_, List.mem_append_right _ writable, Region.contains_self _ _⟩ saved) ?_
  rintro t ⟨restored, memT, restT⟩ ml ul hfl
  have spT : t.sp = s.sp - BitVec.ofNat 32 40 := restT.sp.trans spV
  have oldM := eq.number fits (by decide : 0 < 8)
  have oldA := eq.number fits ha.1
  have oldB := eq.number fits hb.1
  rw [oldM] at lt
  rw [oldM, oldA, oldB] at value
  have lostEq : WorkspaceEq (State.addr base) (8 * len) t.mem ml :=
    WorkspaceEq.of_frame (by omega_using [nowrap]) hfl (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.stackWorkspace.symm)
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro r hr
    have ne : r ≠ .r12 := by intro he; subst r; simp [preserved] at hr
    rw [popped_gpr ne]
    have member : r ∈ callCalleeSaved.map Prod.fst := by
      simpa only [callCalleeSaved, List.map_cons, List.map_nil, preserved] using hr
    obtain ⟨p, hp, eqr⟩ := List.mem_map.mp member
    rw [← eqr]
    exact restored p hp
  · rw [popped_sp, spT]
    exact BitVec.sub_add_cancel _ _
  · dsimp only; rw [lostEq.number fits ho.1, memT]; exact lt
  · dsimp only; rw [lostEq.number fits ho.1, memT]; exact value
  · intro i hi separate
    dsimp only
    rw [show ml (State.addr base + BitVec.ofNat 64 i) = t.mem (State.addr base + BitVec.ofNat 64 i)
      from lost_byte hfl (R := ⟨State.addr base, 8 * len⟩) h.stackWorkspace.symm hi, memT, keeps i hi separate]
    exact framePush.bytes (R := ⟨State.addr base, 8 * len⟩)
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.stackWorkspace.symm)
      (by change 8 * len ≤ 2 ^ 64; omega_using [nowrap]) hi

end VG.Proof.Bignum.Arm

end

end

/-! # The invariant of the two-row scan

After the scan has stored `j` words of row `i + 1`'s output, row `i` has
taken `j + 2` words of `b` and `m` and row `i + 1` has taken `j + 1`; row
`i`'s outputs never reach memory, so the invariant states both rows at once:
the stored words times `2⁶⁴` plus the four carries at word `j + 2` are the
old accumulator's first `j + 2` words plus both rows' products so far. The
pointers are at word `p`, `j` or up to two below it inside the loop body, and the
count is the words left after `p`. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios2
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

/-- The sum of the four carries. -/
abbrev carries (s : State) : Nat :=
  (s.gpr .r7).toNat + (s.gpr .r8).toNat + (s.gpr .r5).toNat + (s.gpr .r11).toNat

structure Inv (s0 : State) (a0 q0 a1 q1 base : BitVec 32) (acc b mod n j p : Nat) (s : State) : Prop where
  index : j + 2 ≤ n
  lag : p ≤ j ∧ j ≤ p + 2
  outPtr : s.gpr .r0 = base + BitVec.ofNat 32 (acc + 4 * p)
  bPtr : s.gpr .r12 = base + BitVec.ofNat 32 (b + 4 * p)
  mPtr : s.gpr .r4 = base + BitVec.ofNat 32 (mod + 4 * p)
  count : s.gpr .lr = BitVec.ofNat 32 (n - 2 - p)
  scalar0 : s.gpr .r1 = a0
  quotient0 : s.gpr .r2 = q0
  scalar1 : s.gpr .r9 = a1
  quotient1 : s.gpr .r10 = q1
  outside : Outside (State.addr base) acc (4 * j) s0.mem s.mem
  value : 2 ^ 64 * val32 s.mem (State.addr base) acc j + 2 ^ (32 * (j + 2)) * carries s =
    val32 s0.mem (State.addr base) acc (j + 2) +
      a0.toNat * val32 s0.mem (State.addr base) b (j + 2) +
      q0.toNat * val32 s0.mem (State.addr base) mod (j + 2) +
      2 ^ 32 * (a1.toNat * val32 s0.mem (State.addr base) b (j + 1) +
        q1.toNat * val32 s0.mem (State.addr base) mod (j + 1))
  rest : Rest roundClobbers s0 s

end VG.Proof.Bignum.Arm.Fios2

end

end

/-! The two-row identity extended by one word of each row. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios2
open VG VG.Proof.Mont

theorem value_extend {mem0 mem mem' : Mem} {base : Addr} {acc b mod j a0 q0 a1 q1 C C' u : Nat}
    (prior : 2 ^ 64 * val32 mem base acc j + 2 ^ (32 * (j + 2)) * C =
      val32 mem0 base acc (j + 2) + a0 * val32 mem0 base b (j + 2) + q0 * val32 mem0 base mod (j + 2) +
        2 ^ 32 * (a1 * val32 mem0 base b (j + 1) + q1 * val32 mem0 base mod (j + 1)))
    (step : u + 2 ^ 32 * C' =
      w32 mem0 base (acc + 4 * (j + 2)) + a0 * w32 mem0 base (b + 4 * (j + 2)) +
        q0 * w32 mem0 base (mod + 4 * (j + 2)) + a1 * w32 mem0 base (b + 4 * (j + 1)) +
        q1 * w32 mem0 base (mod + 4 * (j + 1)) + C)
    (stored : val32 mem' base acc (j + 1) = val32 mem base acc j + 2 ^ (32 * j) * u) :
    2 ^ 64 * val32 mem' base acc (j + 1) + 2 ^ (32 * (j + 1 + 2)) * C' =
      val32 mem0 base acc (j + 1 + 2) + a0 * val32 mem0 base b (j + 1 + 2) +
        q0 * val32 mem0 base mod (j + 1 + 2) +
        2 ^ 32 * (a1 * val32 mem0 base b (j + 1 + 1) + q1 * val32 mem0 base mod (j + 1 + 1)) := by
  have p3 : 2 ^ (32 * (j + 2 + 1)) = 2 ^ 96 * 2 ^ (32 * j) := by
    rw [show 32 * (j + 2 + 1) = 96 + 32 * j by omega_using []]; exact Nat.pow_add 2 96 (32 * j)
  have p2 : 2 ^ (32 * (j + 2)) = 2 ^ 64 * 2 ^ (32 * j) := by
    rw [show 32 * (j + 2) = 64 + 32 * j by omega_using []]; exact Nat.pow_add 2 64 (32 * j)
  have p1 : 2 ^ (32 * (j + 1)) = 2 ^ 32 * 2 ^ (32 * j) := pow32_succ _
  have eT := val32_succ mem0 base acc (j + 2)
  have eB2 := val32_succ mem0 base b (j + 2)
  have eM2 := val32_succ mem0 base mod (j + 2)
  have eB1 := val32_succ mem0 base b (j + 1)
  have eM1 := val32_succ mem0 base mod (j + 1)
  rw [p2] at eT eB2 eM2 prior
  rw [p1] at eB1 eM1
  rw [show j + 1 + 2 = j + 2 + 1 by omega_using [], show j + 1 + 1 = j + 2 by omega_using [], p3, stored]
  rw [show j + 2 = j + 1 + 1 by omega_using []] at eB1 eM1
  rw [eT, eB2, eM2]
  rw [show j + 1 + 1 = j + 2 by omega_using []] at eB1 eM1
  rw [eB1, eM1] at prior ⊢
  have scaled := congrArg (fun z => 2 ^ 64 * 2 ^ (32 * j) * z) step
  generalize 2 ^ (32 * j) = P at prior scaled ⊢
  generalize val32 mem base acc j = S at prior scaled ⊢
  generalize val32 mem0 base acc (j + 2) = T at prior scaled ⊢
  generalize val32 mem0 base b (j + 1) = B at prior scaled ⊢
  generalize val32 mem0 base mod (j + 1) = M at prior scaled ⊢
  generalize w32 mem0 base (acc + 4 * (j + 2)) = wT at prior scaled ⊢
  generalize w32 mem0 base (b + 4 * (j + 2)) = wB2 at prior scaled ⊢
  generalize w32 mem0 base (mod + 4 * (j + 2)) = wM2 at prior scaled ⊢
  generalize w32 mem0 base (b + 4 * (j + 1)) = wB1 at prior scaled ⊢
  generalize w32 mem0 base (mod + 4 * (j + 1)) = wM1 at prior scaled ⊢
  grind

/-- The first words of both rows: the two cancelled words are zero. -/
theorem first_value {T0 T1 B0 B1 M0 M1 a0 a1 q0 q1 u1 u3 u4 u5 c7 c8 c7' c8' c5 c11 : Nat}
    (x1 : u1 + 2 ^ 32 * c7 = B0 * a0 + T0)
    (x2 : 0 + 2 ^ 32 * c8 = M0 * q0 + u1)
    (x3 : u3 + 2 ^ 32 * c7' = B1 * a0 + T1 + c7)
    (x4 : u4 + 2 ^ 32 * c8' = M1 * q0 + u3 + c8)
    (x5 : u5 + 2 ^ 32 * c5 = B0 * a1 + u4)
    (x6 : 0 + 2 ^ 32 * c11 = M0 * q1 + u5) :
    2 ^ 64 * (c7' + c8' + c5 + c11) =
      (T0 + 2 ^ 32 * T1) + a0 * (B0 + 2 ^ 32 * B1) + q0 * (M0 + 2 ^ 32 * M1) +
        2 ^ 32 * (a1 * B0 + q1 * M0) := by
  grind

/-- The tops of both rows complete the two-row identity. -/
theorem top_value {S S' C T Tn Tn1 B Bl M Ml a0 a1 q0 q1 W P : Nat}
    (prior : 2 ^ 64 * S + 2 ^ 64 * P * C =
      T + a0 * (B + 2 ^ 32 * P * Bl) + q0 * (M + 2 ^ 32 * P * Ml) + 2 ^ 32 * (a1 * B + q1 * M))
    (step : W = Bl * a1 + Ml * q1 + (Tn + 2 ^ 32 * Tn1) + C)
    (stored : S' = S + P * W) :
    2 ^ 64 * S' = (T + 2 ^ 64 * P * (Tn + 2 ^ 32 * Tn1)) + (a0 + 2 ^ 32 * a1) * (B + 2 ^ 32 * P * Bl) +
      (q0 + 2 ^ 32 * q1) * (M + 2 ^ 32 * P * Ml) := by
  subst stored step
  grind

end VG.Proof.Bignum.Arm.Fios2
