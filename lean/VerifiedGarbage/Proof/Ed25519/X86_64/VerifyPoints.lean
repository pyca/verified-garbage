import VerifiedGarbage.Proof.Ed25519.X86_64.WindowStep
import VerifiedGarbage.Proof.Ed25519.X86_64.Bits
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCounter
import VerifiedGarbage.Proof.Ed25519.Window
import VerifiedGarbage.Proof.Ed25519.X86_64.PointEqual
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMul
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! Merged from `Proof.Ed25519.X86_64.WindowByte`. -/
section
/-!
# Verification's bytes: two windows per byte of the scalars

Byte `i` of `k` (and of `S`) gives two digits, high nibble first; after it,
the accumulator represents `[k / 256^i]A - [S / 256^i]B`.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open VG.Proof.X25519.X86_64 (off ofs Keeps clob Outside)

variable {fld : Arith} [EdArith fld]
variable {dbl : Prog isa} [EdDouble dbl]

/-- What a byte of the scalars may change. -/
structure ByteKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ clob → r ≠ .rbx → r ≠ .rsi → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside base 56 1832 s.mem t.mem

theorem ByteKeep.trans {base : Addr} {s t u : State} (h : ByteKeep base s t) (k : ByteKeep base t u) :
    ByteKeep base s u :=
  ⟨fun r a b c => (k.gpr r a b c).trans (h.gpr r a b c), k.rd.trans h.rd, k.wr.trans h.wr,
    h.mem.trans k.mem⟩

theorem ByteKeep.of_win {base : Addr} {s t : State} (h : WinKeep base s t) : ByteKeep base s t :=
  ⟨h.gpr, h.rd, h.wr, Outside.widen h.mem⟩

theorem ByteKeep.of_keeps {base : Addr} {s t : State} {rs : List Reg} (h : Keeps rs s t)
    (hrs : ∀ r ∈ rs, r = .rbx ∨ r = .rsi ∨ r ∈ clob) : ByteKeep base s t :=
  ByteKeep.of_win (WinKeep.of_keeps h hrs)

theorem ByteKeep.scratch {base : Addr} {s t : State} (h : ByteKeep base s t) (hs : Scratch s base) :
    Scratch t base := ⟨(h.gpr _ (by decide) (by decide) (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

theorem WinCtx.of_byte {base kp sp : Addr} {A : EPoint dZ} {s t : State} (h : WinCtx base kp sp A s)
    (k : ByteKeep base s t) : WinCtx base kp sp A t := by
  refine ⟨k.scratch h.scratch, (k.mem.word (Or.inr (by decide)) (by decide)).trans h.kHeader,
    (k.mem.word (Or.inr (by decide)) (by decide)).trans h.sHeader, ?_, ?_, h.kFar, h.sFar,
    h.aTab.of_win k.mem (by decide) (by decide), h.bTab.of_win k.mem (by decide) (by decide)⟩
  · intro i hi; rw [k.rd, k.wr]; exact h.kRead i hi
  · intro i hi; rw [k.rd, k.wr]; exact h.sRead i hi

theorem ByteKeep.bytesK {base kp sp : Addr} {A : EPoint dZ} {s t : State} (h : WinCtx base kp sp A s)
    (k : ByteKeep base s t) : Spec.Ed25519.bytesAt t.mem kp 64 = Spec.Ed25519.bytesAt s.mem kp 64 :=
  outside_bytes k.mem (by decide) h.kFar

theorem ByteKeep.bytesS {base kp sp : Addr} {A : EPoint dZ} {s t : State} (h : WinCtx base kp sp A s)
    (k : ByteKeep base s t) :
    Spec.Ed25519.bytesAt t.mem (off sp 32) 32 = Spec.Ed25519.bytesAt s.mem (off sp 32) 32 :=
  outside_bytes k.mem (by decide) h.sFar

/-! ## Digits from the inputs -/

theorem digitKHigh {base kp sp : Addr} {A : EPoint dZ} {s : State} (h : WinCtx base kp sp A s)
    {i : Nat} (hi : i < 64) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i) :
    DigitSpec base s (digitHigh 7952 0) ((s.mem (off kp i)).toNat / 16) := by
  intro t kt
  have ht := h.of_keep kt
  refine WP.mono (digitHigh_ok ht.scratch 7952 0 (by decide) (by decide) ht.kHeader i
    (kt.counter.trans hc) (by rw [off_zero]; exact ht.kRead i hi)) fun u ⟨uv, uz, ku⟩ => ?_
  rw [off_zero, h.byteK kt hi] at uv uz
  exact ⟨uv, uz, ku⟩

theorem digitKLow {base kp sp : Addr} {A : EPoint dZ} {s : State} (h : WinCtx base kp sp A s)
    {i : Nat} (hi : i < 64) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i) :
    DigitSpec base s (digitLow 7952 0) ((s.mem (off kp i)).toNat % 16) := by
  intro t kt
  have ht := h.of_keep kt
  refine WP.mono (digitLow_ok ht.scratch 7952 0 (by decide) (by decide) ht.kHeader i
    (kt.counter.trans hc) (by rw [off_zero]; exact ht.kRead i hi)) fun u ⟨uv, uz, ku⟩ => ?_
  rw [off_zero, h.byteK kt hi] at uv uz
  exact ⟨uv, uz, ku⟩

theorem digitSHigh {base kp sp : Addr} {A : EPoint dZ} {s : State} (h : WinCtx base kp sp A s)
    {i : Nat} (hi : i < 32) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i) :
    DigitSpec base s (digitHigh 7944 32) ((s.mem (off (off sp 32) i)).toNat / 16) := by
  intro t kt
  have ht := h.of_keep kt
  refine WP.mono (digitHigh_ok ht.scratch 7944 32 (by decide) (by decide) ht.sHeader i
    (kt.counter.trans hc) (ht.sRead i hi)) fun u ⟨uv, uz, ku⟩ => ?_
  rw [h.byteS kt hi] at uv uz
  exact ⟨uv, uz, ku⟩

theorem digitSLow {base kp sp : Addr} {A : EPoint dZ} {s : State} (h : WinCtx base kp sp A s)
    {i : Nat} (hi : i < 32) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i) :
    DigitSpec base s (digitLow 7944 32) ((s.mem (off (off sp 32) i)).toNat % 16) := by
  intro t kt
  have ht := h.of_keep kt
  refine WP.mono (digitLow_ok ht.scratch 7944 32 (by decide) (by decide) ht.sHeader i
    (kt.counter.trans hc) (ht.sRead i hi)) fun u ⟨uv, uz, ku⟩ => ?_
  rw [h.byteS kt hi] at uv uz
  exact ⟨uv, uz, ku⟩

/-! ## A byte -/

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

theorem byteStepA_ok {s : State} {base kp sp : Addr} {A : EPoint dZ} (h : WinCtx base kp sp A s)
    (hd : env s.mem base 16 = Spec.Ed25519.d) {i : Nat} (hi32 : 32 ≤ i) (hi : i < 64)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (i + 1)) {S : Nat} (hS : S < 256 ^ 32)
    (ha : Rep (point (env s.mem base) 0 1 2 3)
      ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) / 256 ^ (i + 1)) • A +
        (S / 256 ^ (i + 1)) • (-baseAff))) :
    WP isa (byteStepA fld dbl) s fun t => t.zf = some (decide (i = 32)) ∧
      t.mem.readW (off base 56) 64 = BitVec.ofNat 64 i ∧ env t.mem base 16 = Spec.Ed25519.d ∧
      Rep (point (env t.mem base) 0 1 2 3)
        ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) / 256 ^ i) • A +
          (S / 256 ^ i) • (-baseAff)) ∧ ByteKeep base s t := by
  rw [byteStepA]
  refine WP.seq (WP.mono (batchBegin_ok h.scratch i hc) fun a ⟨_, av, ag, ar, aw, am⟩ => ?_)
  have ka : ByteKeep base s a := ⟨fun r _ hb _ => ag r hb, ar, aw, am.mono (by decide) (by decide)⟩
  have ae := header_env am
  have ha' := h.of_byte ka
  set K := Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) with hK
  have hb : (a.mem (off kp i)).toNat = K / 256 ^ i % 256 := by
    rw [scalar_byte (n := 64) hi, ka.bytesK h]
  refine WP.seq (WP.mono (windowA_ok (a := (K / 256 ^ (i + 1)) • A + (S / 256 ^ (i + 1)) • (-baseAff))
    ha' (by rw [ae]; exact hd) (by rw [ae]; exact ha) (Nat.div_lt_of_lt_mul (by have := (a.mem (off kp i)).isLt; omega)) (digitKHigh ha' hi av))
    fun b ⟨br, bd, kb⟩ => ?_)
  have hb' := ha'.of_keep kb
  refine WP.seq (WP.mono (windowA_ok hb' bd br (Nat.mod_lt _ (by decide))
    (digitKLow hb' hi (kb.counter.trans av))) fun c ⟨cr, cd, kc⟩ => ?_)
  have hc' := hb'.of_keep kc
  refine WP.mono (counterCmp_ok hc'.scratch i hi.le (kc.counter.trans (kb.counter.trans av)))
    fun t ⟨tz, kt⟩ => ?_
  refine ⟨tz, ?_, by rw [kt.2.1]; exact cd, ?_, ((ka.trans (ByteKeep.of_win kb)).trans
    (ByteKeep.of_win kc)).trans (ByteKeep.of_keeps kt (by decide))⟩
  · rw [kt.2.1]; exact kc.counter.trans (kb.counter.trans av)
  · rw [ha'.byteK kb hi] at cr
    rw [kt.2.1]
    convert cr using 1
    rw [byte_split K i _ hb, high_zero hS hi32, high_zero hS (by omega : 32 ≤ i + 1)]
    module

theorem byteStepAB_ok {s : State} {base kp sp : Addr} {A : EPoint dZ} (h : WinCtx base kp sp A s)
    (hd : env s.mem base 16 = Spec.Ed25519.d) {i : Nat} (hi : i < 32)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (i + 1))
    (ha : Rep (point (env s.mem base) 0 1 2 3)
      ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) / 256 ^ (i + 1)) • A +
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sp 32) 32) / 256 ^ (i + 1)) •
          (-baseAff))) :
    WP isa (byteStepAB fld dbl) s fun t => t.zf = some (decide (i = 0)) ∧
      t.mem.readW (off base 56) 64 = BitVec.ofNat 64 i ∧ env t.mem base 16 = Spec.Ed25519.d ∧
      Rep (point (env t.mem base) 0 1 2 3)
        ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) / 256 ^ i) • A +
          (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sp 32) 32) / 256 ^ i) •
            (-baseAff)) ∧ ByteKeep base s t := by
  rw [byteStepAB]
  refine WP.seq (WP.mono (batchBegin_ok h.scratch i hc) fun a ⟨_, av, ag, ar, aw, am⟩ => ?_)
  have ka : ByteKeep base s a := ⟨fun r _ hb _ => ag r hb, ar, aw, am.mono (by decide) (by decide)⟩
  have ae := header_env am
  have ha' := h.of_byte ka
  set K := Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) with hK
  set S := Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sp 32) 32) with hSdef
  have hbK : (a.mem (off kp i)).toNat = K / 256 ^ i % 256 := by
    rw [scalar_byte (n := 64) (by omega), ka.bytesK h]
  have hbS : (a.mem (off (off sp 32) i)).toNat = S / 256 ^ i % 256 := by
    rw [scalar_byte (n := 32) hi, ka.bytesS h]
  have lt16 (b : Byte) : b.toNat / 16 < 16 := Nat.div_lt_of_lt_mul (by have := b.isLt; omega)
  refine WP.seq (WP.mono (windowAB_ok (a := (K / 256 ^ (i + 1)) • A + (S / 256 ^ (i + 1)) • (-baseAff))
    ha' (by rw [ae]; exact hd) (by rw [ae]; exact ha) (lt16 _) (lt16 _)
    (digitKHigh ha' (by omega) av) (digitSHigh ha' hi av)) fun b ⟨br, bd, kb⟩ => ?_)
  have hb' := ha'.of_keep kb
  refine WP.seq (WP.mono (windowAB_ok hb' bd br (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
    (digitKLow hb' (by omega) (kb.counter.trans av)) (digitSLow hb' hi (kb.counter.trans av)))
    fun c ⟨cr, cd, kc⟩ => ?_)
  have hc' := hb'.of_keep kc
  refine WP.mono (batchTest_ok hc'.scratch i (by omega) (kc.counter.trans (kb.counter.trans av)))
    fun t ⟨tz, kt⟩ => ?_
  refine ⟨tz, ?_, by rw [kt.2.1]; exact cd, ?_, ((ka.trans (ByteKeep.of_win kb)).trans
    (ByteKeep.of_win kc)).trans (ByteKeep.of_keeps kt (by decide))⟩
  · rw [kt.2.1]; exact kc.counter.trans (kb.counter.trans av)
  · rw [ha'.byteK kb (by omega), ha'.byteS kb hi] at cr
    rw [kt.2.1]
    convert cr using 1
    rw [byte_split K i _ hbK, byte_split S i _ hbS]
    module

end VG.Proof.Ed25519.X86_64
end

/-! Merged from `Proof.Ed25519.X86_64.WindowLoop`. -/
section
/-!
# Verification's loops over the bytes of the scalars

Bytes 63 down to 32 hold digits of `k` alone, bytes 31 down to 0 of both
scalars; after the loops the accumulator represents `[k]A - [S]B`.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open VG.Proof.X25519.X86_64 (off ofs Keeps clob Outside)

variable {fld : Arith} [EdArith fld]
variable {dbl : Prog isa} [EdDouble dbl]

/-- The loops' invariant, with `c` bytes left. -/
structure WinLoop (s₀ : State) (base kp sp : Addr) (A : EPoint dZ) (K S c : Nat) (s : State) : Prop where
  ctx : WinCtx base kp sp A s
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
theorem WinLoop.of_counter {s₀ s t : State} {base kp sp : Addr} {A : EPoint dZ} {K S c c' : Nat}
    (h : WinLoop s₀ base kp sp A K S c s) (k : CounterKeep base s t)
    (hc : t.mem.readW (off base 56) 64 = BitVec.ofNat 64 c')
    (hK : K / 256 ^ c' = K / 256 ^ c) (hS : S / 256 ^ c' = S / 256 ^ c) :
    WinLoop s₀ base kp sp A K S c' t :=
  ⟨h.ctx.of_byte k.byte, by rw [header_env k.mem]; exact h.d, hc,
    by rw [k.byte.bytesK h.ctx, h.kVal], by rw [k.byte.bytesS h.ctx, h.sVal],
    by rw [header_env k.mem, hK, hS]; exact h.value, h.keep.trans k.byte⟩

/-- A byte of `k` alone, from `32 + j + 1` bytes left to `32 + j`. -/
theorem stepA_ok {s₀ t : State} {base kp sp : Addr} {A : EPoint dZ} {K S j : Nat} (hj : j < 32)
    (ht : WinLoop s₀ base kp sp A K S (32 + (j + 1)) t) :
    WP isa (byteStepA fld dbl) t fun u => u.zf = some (decide (j = 0)) ∧ WinLoop s₀ base kp sp A K S (32 + j) u := by
  have hS : S < 256 ^ 32 := ht.sVal ▸ decodeLE_lt32 _ _
  refine WP.mono (byteStepA_ok (i := 32 + j) ht.ctx ht.d (by omega) (by omega)
    (by rw [ht.counter]; rfl) hS (by rw [ht.kVal]; exact ht.value)) fun u ⟨uz, uc, ud, uv, uk⟩ => ?_
  refine ⟨by rw [uz]; simp, ht.ctx.of_byte uk, ud, uc, by rw [uk.bytesK ht.ctx, ht.kVal],
    by rw [uk.bytesS ht.ctx, ht.sVal], by rw [ht.kVal] at uv; exact uv, ht.keep.trans uk⟩

/-- A byte of both scalars, from `j + 1` bytes left to `j`. -/
theorem stepB_ok {s₀ t : State} {base kp sp : Addr} {A : EPoint dZ} {K S j : Nat} (hj : j < 32)
    (ht : WinLoop s₀ base kp sp A K S (j + 1) t) :
    WP isa (byteStepAB fld dbl) t fun u => u.zf = some (decide (j = 0)) ∧ WinLoop s₀ base kp sp A K S j u := by
  refine WP.mono (byteStepAB_ok (i := j) ht.ctx ht.d hj ht.counter
    (by rw [ht.kVal, ht.sVal]; exact ht.value)) fun u ⟨uz, uc, ud, uv, uk⟩ => ?_
  exact ⟨uz, ht.ctx.of_byte uk, ud, uc, by rw [uk.bytesK ht.ctx, ht.kVal],
    by rw [uk.bytesS ht.ctx, ht.sVal], by rw [ht.kVal, ht.sVal] at uv; exact uv, ht.keep.trans uk⟩

theorem loopA_ok {s₀ s : State} {base kp sp : Addr} {A : EPoint dZ} {K S : Nat} (n : Nat)
    (hn0 : 0 < n) (hn : n ≤ 32) (h : WinLoop s₀ base kp sp A K S (32 + n) s) :
    WP isa (.loop (byteStepA fld dbl) .ne) s (WinLoop s₀ base kp sp A K S 32) := by
  apply WP.loop (fun (n : Nat) (t : State) => WinLoop s₀ base kp sp A K S (32 + n) t ∧ 0 < n ∧ n ≤ 32)
    (n := n)
  · intro n t ⟨ht, hn0, hn⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    refine WP.mono (stepA_ok (by omega) ht) fun u ⟨uz, hu⟩ => ?_
    by_cases hj : j = 0
    · subst hj
      exact Or.inl ⟨by simp only [eval, uz, decide_true, Option.map_some, Bool.not_true], hu⟩
    · exact Or.inr ⟨by simp only [eval, uz, decide_eq_false hj, Option.map_some, Bool.not_false],
        j, by omega, hu, by omega, by omega⟩
  · exact ⟨h, hn0, hn⟩

theorem windowsA_ok {s₀ s : State} {base kp sp : Addr} {A : EPoint dZ} {K S c : Nat}
    (hc32 : 32 ≤ c) (hc64 : c ≤ 64) (h : WinLoop s₀ base kp sp A K S c s) :
    WP isa (windowsA fld dbl) s (WinLoop s₀ base kp sp A K S 32) := by
  rw [windowsA, counterCmp]
  refine WP.seq (WP.mono (counterCmp_ok h.ctx.scratch c hc64 h.counter) fun a ⟨az, ka⟩ => ?_)
  have ha := h.of_counter (CounterKeep.of_keeps ka (by decide)) (by rw [ka.2.1]; exact h.counter) rfl rfl
  refine WP.ite (!decide (c = 32)) (by simp only [eval, az, Option.map_some]) (fun hy => ?_) (fun hy => ?_)
  · obtain ⟨n, rfl⟩ : ∃ n, c = 32 + n := ⟨c - 32, by omega⟩
    have hn : n ≠ 0 := fun h0 => by subst h0; simp at hy
    exact loopA_ok n (by omega) (by omega) ha
  · have : c = 32 := by simpa using hy
    subst this
    exact WP.block_nil ha

theorem loopB_ok {s₀ s : State} {base kp sp : Addr} {A : EPoint dZ} {K S : Nat}
    (h : WinLoop s₀ base kp sp A K S 32 s) :
    WP isa (.loop (byteStepAB fld dbl) .ne) s (WinLoop s₀ base kp sp A K S 0) := by
  apply WP.loop (fun (n : Nat) (t : State) => WinLoop s₀ base kp sp A K S n t ∧ 0 < n ∧ n ≤ 32)
    (n := 32)
  · intro n t ⟨ht, hn0, hn⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    refine WP.mono (stepB_ok (by omega) ht) fun u ⟨uz, hu⟩ => ?_
    by_cases hj : j = 0
    · subst hj
      exact Or.inl ⟨by simp only [eval, uz, decide_true, Option.map_some, Bool.not_true], hu⟩
    · exact Or.inr ⟨by simp only [eval, uz, decide_eq_false hj, Option.map_some, Bool.not_false],
        j, by omega, hu, by omega, by omega⟩
  · exact ⟨h, by decide, by decide⟩

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
theorem skipLoad_ok {s : State} {base kp sp : Addr} {A : EPoint dZ} (h : WinCtx base kp sp A s)
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
def SkipInv (s₀ : State) (base kp sp : Addr) (A : EPoint dZ) (K S : Nat) (n : Nat) (s : State) : Prop :=
  WinLoop s₀ base kp sp A K S (32 + n) s ∧ K / 256 ^ (32 + n) = 0 ∧ 0 < n ∧ n ≤ 32

/-- Whether the skipping goes on below `32 + j + 1` bytes left: byte `32 + j` of `k` is zero,
and more than 32 bytes are left after it. -/
def skipOn (K j : Nat) : Bool := decide (K / 256 ^ (32 + j) % 256 = 0 ∧ j ≠ 0)

/-- Where the skipping stops below `32 + j + 1` bytes left, if it does. -/
def skipEnd (K j : Nat) : Nat := if K / 256 ^ (32 + j) % 256 = 0 then 32 else 32 + (j + 1)

theorem skipEnd_range (K j : Nat) (hj : j < 32) : 32 ≤ skipEnd K j ∧ skipEnd K j ≤ 64 := by
  unfold skipEnd; split <;> omega

theorem skipBody_ok {s₀ t : State} {base kp sp : Addr} {A : EPoint dZ} {K S j : Nat}
    (h : SkipInv s₀ base kp sp A K S (j + 1) t) :
    WP isa skipBody t fun u => u.zf.map (!·) = some (skipOn K j) ∧
      (skipOn K j = false → WinLoop s₀ base kp sp A K S (skipEnd K j) u) ∧
      (skipOn K j = true → SkipInv s₀ base kp sp A K S j u) := by
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
    exact hl.of_counter (ka.trans ku) uc rfl rfl
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
    exact hu

theorem skipZero_ok {s₀ s : State} {base kp sp : Addr} {A : EPoint dZ} {K S : Nat}
    (h : WinLoop s₀ base kp sp A K S 64 s) :
    WP isa skipZero s fun t => ∃ c, 32 ≤ c ∧ c ≤ 64 ∧ WinLoop s₀ base kp sp A K S c t := by
  have hK : K / 256 ^ 64 = 0 := Nat.div_eq_of_lt (h.kVal ▸ decodeLE_lt64 _ _)
  rw [skipZero]
  apply WP.loop (SkipInv s₀ base kp sp A K S) (n := 32)
  · intro n t ht
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := ht.2.2.1; omega : n ≠ 0)
    have hj : j < 32 := by have := ht.2.2.2; omega
    refine WP.mono (skipBody_ok ht) fun u ⟨uz, uf, ut⟩ => ?_
    cases hs : skipOn K j
    · exact Or.inl ⟨by show u.zf.map (!·) = _; rw [uz, hs], skipEnd K j, (skipEnd_range K j hj).1,
        (skipEnd_range K j hj).2, uf hs⟩
    · exact Or.inr ⟨by show u.zf.map (!·) = _; rw [uz, hs], j, by omega, ut hs⟩
  · exact ⟨h, hK, by decide, by decide⟩

end VG.Proof.Ed25519.X86_64
end

/-!
# Verification's equation, from the windows

The windows leave a representative of `[k]A - [S]B`, compared with `-R`: they
are equal exactly when `[S]B = R + [k]A`, which, as `A` and `R` represent
points of the group, is the specification's comparison.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open VG.Proof.X25519.X86_64 (off ofs Keeps clob Outside)

variable {fld : Arith} [EdArith fld]
variable {dbl : Prog isa} [EdDouble dbl]

theorem PowersKeep.of_byte {base : Addr} {s t : State} (h : ByteKeep base s t) :
    PowersKeep base 56 7752 s t :=
  ⟨fun r hb hs hc => h.gpr r hc hb hs, h.rd, h.wr, TableFrame.table (h.mem.mono (by decide) (by decide))⟩

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
  .seq (.seq (.seq (.block windowSetup) (aTable fld)) (.block bTable)) (.block (windowInit fld))

/-- Before the windows: the tables, an accumulator representing `0` and the counter at 64. -/
theorem windowPrep_ok {s : State} {base sig challenge : Addr} {Aa : EPoint dZ}
    (hs : Scratch s base)
    (hp : s.mem.readW (off base 7944) 64 = sig)
    (hc : s.mem.readW (off base 7952) 64 = challenge)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off sig 32) i) 1)
    (hf : ∀ i < 32, 8192 ≤ ofs base (off (off sig 32) i))
    (hcr : ∀ i < 64, InRegions (s.rd ++ s.wr) (off challenge i) 1)
    (hcf : ∀ i < 64, 8192 ≤ ofs base (off challenge i))
    (hA : Rep (tablePoint s.mem base 7424) Aa) :
    WP isa (windowPrep fld) s fun e => WinLoop e base challenge sig Aa
      (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64))
      (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32)) 64 e ∧
      PowersKeep base 56 7752 s e ∧ tablePoint e.mem base 7552 = tablePoint s.mem base 7552 := by
  rw [windowPrep]
  -- The constant `d`.
  refine WP.seq (WP.seq (WP.seq (WP.mono (constFieldWide_ok hs 16 Spec.Ed25519.d) fun a ⟨ka, va⟩ => ?_)))
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
  -- The negated multiples of `B`.
  refine WP.mono (bTable_ok hb.scratch) fun c hc' => ?_
  have kbc : PowersKeep base 56 7752 b c :=
    ⟨fun r _ _ hr => hc'.gpr r (fun hm => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl <;> decide)), hc'.rd, hc'.wr,
      TableFrame.table (hc'.mem.mono (by decide) (by decide))⟩
  have ksc := ksb.trans kbc
  have cR : tablePoint c.mem base 7552 = tablePoint s.mem base 7552 := by
    rw [(TableFrame.table hc'.mem).point (by decide) (Or.inr (by decide)) (by decide), bR]
  have cd : env c.mem base 16 = Spec.Ed25519.d := by rw [table_env hc'.mem (by decide)]; exact hb.d
  have cA : TableOf cache c.mem base 5376 Aa := fun j hj => by
    obtain ⟨q, hq, hr⟩ := hb.table j hj
    exact ⟨q, ((TableFrame.table hc'.mem).point (by omega) (Or.inr (by omega)) (by omega)).trans hq, hr⟩
  have cB : TableOf cache c.mem base 2048 (-baseAff) := fun j hj => by
    obtain ⟨q, hq, hr⟩ := negBaseCached_ok j hj
    exact ⟨q, by rw [hc'.table j hj, hq], hr⟩
  -- The accumulator and the byte counter.
  rw [windowInit, WP.block_append_iff]
  refine WP.mono (fieldCodeWide_ok (ksc.scratch hs) (constPointOps Spec.Ed25519.identity))
    fun d ⟨kd, vd⟩ => ?_
  have kcd : PowersKeep base 56 7752 c d := PowersKeep.of_keep kd
  refine WP.mono (mulCounterInit_ok ((ksc.trans kcd).scratch hs) 64) fun e ⟨ec, eg, er, ew, em⟩ => ?_
  have kde : ByteKeep base d e :=
    ⟨fun r _ _ _ => eg r (by rintro rfl; contradiction), er, ew, em.mono (by decide) (by decide)⟩
  have kce : ByteKeep base c e := (ByteKeep.of_win (WinKeep.of_keep kd)).trans kde
  have kse := ksc.trans (PowersKeep.of_byte kce)
  have eR : tablePoint e.mem base 7552 = tablePoint s.mem base 7552 := by
    rw [win_tablePoint kce.mem (by decide) (by decide), cR]
  have ed : env e.mem base 16 = Spec.Ed25519.d := by rw [header_env em, vd]; exact cd
  have ctx : WinCtx base challenge sig Aa e :=
    ⟨kse.scratch hs, (kse.header (by decide) (by decide) (by decide)).trans hc,
      (kse.header (by decide) (by decide) (by decide)).trans hp,
      fun i hi => by rw [kse.rd, kse.wr]; exact hcr i hi,
      fun i hi => by rw [kse.rd, kse.wr]; exact hr i hi, hcf, hf,
      cA.of_win kce.mem (by decide) (by decide), cB.of_win kce.mem (by decide) (by decide)⟩
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

theorem verifyEquationPoints_ok {s : State} {base sig challenge : Addr} {Aa Ra : EPoint dZ}
    (hs : Scratch s base)
    (hp : s.mem.readW (off base 7944) 64 = sig)
    (hc : s.mem.readW (off base 7952) 64 = challenge)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off sig 32) i) 1)
    (hf : ∀ i < 32, 8192 ≤ ofs base (off (off sig 32) i))
    (hcr : ∀ i < 64, InRegions (s.rd ++ s.wr) (off challenge i) 1)
    (hcf : ∀ i < 64, 8192 ≤ ofs base (off challenge i))
    (hA : Rep (tablePoint s.mem base 7424) Aa) (hR : Rep (tablePoint s.mem base 7552) Ra) :
    WP isa (verifyEquationPoints fld dbl) s fun t => PowersKeep base 56 7752 s t ∧
      t.gpr .rax = signWord (Spec.Ed25519.pointEqual
        (Spec.Ed25519.pointMul
          (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32)) Spec.Ed25519.basePoint)
        (Spec.Ed25519.pointAdd (tablePoint s.mem base 7552)
          (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64))
            (tablePoint s.mem base 7424)))) := by
  rw [verifyEquationPoints]
  apply WP.assoc; apply WP.assoc; apply WP.assoc
  refine WP.seq (WP.mono (windowPrep_ok hs hp hc hr hf hcr hcf hA) fun e ⟨w0, kse, eR⟩ => ?_)
  -- The windows.
  refine WP.seq (WP.mono (skipZero_ok w0) fun f ⟨c, hc32, hc64, hf⟩ => ?_)
  refine WP.seq (WP.mono (windowsA_ok hc32 hc64 hf) fun f' hf' => ?_)
  refine WP.seq (WP.mono (loopB_ok hf') fun g hg => ?_)
  have ksg := kse.trans (PowersKeep.of_byte hg.keep)
  -- The comparison with `-R`.
  refine WP.seq (WP.mono (negR_ok (ksg.scratch hs)) fun u ⟨ku, u0, u4⟩ => ?_)
  have ksu := ksg.trans (PowersKeep.of_keep ku)
  refine WP.mono (pointEqual_ok (ksu.scratch hs)) fun t ⟨kt, tv⟩ => ?_
  refine ⟨ksu.trans (PowersKeep.of_keep kt), ?_⟩
  have gv := hg.value
  simp only [pow_zero, Nat.div_one] at gv
  rw [tv, u0, u4, win_tablePoint hg.keep.mem (by decide) (by decide), eR,
    window_equation hA hR gv.proj hR.neg.proj]

end VG.Proof.Ed25519.X86_64
