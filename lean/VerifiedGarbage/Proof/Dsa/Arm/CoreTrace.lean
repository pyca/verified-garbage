module

public import VerifiedGarbage.Proof.Dsa.Arm.CoreOps
public import VerifiedGarbage.Proof.Dsa.Arm.Leaves
public import VerifiedGarbage.Proof.Dsa.SameTrace
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA on 32-bit ARM: the arithmetic's traces

Two runs of an arithmetic operation leak the same trace when their working
spaces have the same base and their operands' pointers are the same: the
pointers are the only values read from memory that steer an address. Each
proof follows its operation's correctness proof (`CoreOps.lean`) only as far
as the last pointer it reads, which the correctness of each run keeps the
same across the parts before it; past it, the analysis of the code alone
(`Leaves.lean`) shows the rest. An exponentiation's call leaks the same trace
in both runs by the called function's constant time (`Pow.call_trace`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm VG.Impl.Dsa.Layout
open VG.Proof.X25519.Arm (Rest)

theorem addr_inj {a b : BitVec 32} (h : State.addr a = State.addr b) : a = b :=
  BitVec.eq_of_toNat_eq (by rw [← VG.Proof.X25519.Arm.addr_toNat a, ← VG.Proof.X25519.Arm.addr_toNat b, h])

theorem Ws.r12_eq {s₁ s₂ : State} {base : Addr} {size₁ size₂ : Nat} (h₁ : Ws s₁ base size₁)
    (h₂ : Ws s₂ base size₂) : s₁.gpr .r12 = s₂.gpr .r12 :=
  addr_inj (h₁.wb.trans h₂.wb.symm)

/-- `r12`, and `r11` and `lr` if `p` and `q`, agree. -/
theorem agreeWs {s₁ s₂ : State} {base : Addr} {size₁ size₂ : Nat} (p q : Bool) (h₁ : Ws s₁ base size₁)
    (h₂ : Ws s₂ base size₂) (h11 : p = true → s₁.gpr .r11 = s₂.gpr .r11)
    (hlr : q = true → s₁.gpr .lr = s₂.gpr .lr) : VG.Arm.Taint.Agree (wsT p q) s₁ s₂ := by
  refine Taint.agree_ofRegs fun r hr => ?_
  cases p <;> cases q <;>
    simp only [wsRegs, Bool.false_eq_true, ↓reduceIte, List.nil_append, List.append_nil, List.cons_append,
      List.mem_cons, List.not_mem_nil, or_false] at hr <;>
    rcases hr with rfl | rfl | rfl <;>
    first | exact Ws.r12_eq h₁ h₂ | exact h11 rfl | exact hlr rfl

theorem agree0 {s₁ s₂ : State} {base : Addr} {size₁ size₂ : Nat} (h₁ : Ws s₁ base size₁) (h₂ : Ws s₂ base size₂) :
    VG.Arm.Taint.Agree T0 s₁ s₂ :=
  agreeWs false false h₁ h₂ (fun h => nomatch h) (fun h => nomatch h)

/-- The pointer is the same in both runs. -/
abbrev PtrEq (base : Addr) (s₁ s₂ : State) (p : Pointer) : Prop := pointerValue base s₁ p = pointerValue base s₂ p

/-! ## Loads -/

/-- A load, followed by code whose analysis needs `r12` and `r10` public. -/
theorem loadThen_trace {s₁ s₂ : State} {base : Addr} {size₁ size₂ n len dst : Nat} {p : Pointer} {rest : Prog isa}
    {Q : State → State → Prop} (h₁ : Ws s₁ base size₁) (h₂ : Ws s₂ base size₂) (hz₁ : 120 ≤ size₁)
    (hz₂ : 120 ≤ size₂) (hp : PtrOk p) (he : PtrEq base s₁ s₂ p)
    (H : RelCT isa (VG.Arm.Taint.Agree T10) rest Q) :
    SameTrace isa (.seq (Core.load n len dst p) rest) s₁ s₂ := by
  unfold Core.load
  refine SameTrace.assoc_left (SameTrace.seq (SameTrace.of_relCT (pointer_relCT p) (agree0 h₁ h₂))
    (pointer_ok h₁ hz₁ hp) (pointer_ok h₂ hz₂ hp) fun u₁ u₂ ⟨P₁, R₁, _⟩ ⟨P₂, R₂, _⟩ => ?_)
  exact SameTrace.of_relCT (RelCT.seq (loadComponent_relCT len n dst) H)
    (agreeWs true false (h₁.of_rest R₁ (by decide)) (h₂.of_rest R₂ (by decide)) (fun _ => by rw [P₁, P₂, he])
      (fun h => nomatch h))

theorem load_trace {s₁ s₂ : State} {base : Addr} {size₁ size₂ n len dst : Nat} {p : Pointer}
    (h₁ : Ws s₁ base size₁) (h₂ : Ws s₂ base size₂) (hz₁ : 120 ≤ size₁) (hz₂ : 120 ≤ size₂) (hp : PtrOk p)
    (he : PtrEq base s₁ s₂ p) : SameTrace isa (Core.load n len dst p) s₁ s₂ := by
  unfold Core.load
  refine SameTrace.seq (SameTrace.of_relCT (pointer_relCT p) (agree0 h₁ h₂))
    (pointer_ok h₁ hz₁ hp) (pointer_ok h₂ hz₂ hp) fun u₁ u₂ ⟨P₁, R₁, _⟩ ⟨P₂, R₂, _⟩ => ?_
  exact SameTrace.of_relCT (loadComponent_relCT len n dst)
    (agreeWs true false (h₁.of_rest R₁ (by decide)) (h₂.of_rest R₂ (by decide)) (fun _ => by rw [P₁, P₂, he])
      (fun h => nomatch h))

/-! ## The operations -/

/-- What one run of an operation needs: its correctness's hypotheses. -/
structure OpPre (s : State) (base : Addr) (size len n m : Nat) (modulus : Field) : Prop where
  ws : Ws s base size
  hz : 4960 ≤ size
  w : Width len n
  R : Ready s base (.input modulus) len
  hm : operand base s (.input modulus) len = m
  hm1 : 1 < m
  hodd : m % 2 = 1

theorem setup_trace {s₁ s₂ : State} {base : Addr} {size₁ size₂ len n m₁ m₂ : Nat} {modulus : Field}
    (P₁ : OpPre s₁ base size₁ len n m₁ modulus) (P₂ : OpPre s₂ base size₂ len n m₂ modulus)
    (he : PtrEq base s₁ s₂ (.input modulus)) :
    SameTrace isa (Core.setup len modulus) s₁ s₂ := by
  unfold Core.setup
  rw [← P₁.w.n_eq]
  obtain ⟨n0, n48, hl, hl'⟩ := P₁.w.bounds
  have s0 := slot_lt (i := 0) n48 (by decide)
  have z₁ := P₁.hz
  have z₂ := P₂.hz
  refine SameTrace.seq (load_trace P₁.ws P₂.ws (by omega) (by omega) P₁.R.ok he)
    (load_ok (n := n) (dst := modS n) P₁.ws (by omega) P₁.R (by simp only [modS]; omega)
      (by simp only [modS]; omega) (by omega) P₁.w.four hl P₁.w.word (by simp only [modS]; omega))
    (load_ok (n := n) (dst := modS n) P₂.ws (by omega) P₂.R (by simp only [modS]; omega)
      (by simp only [modS]; omega) (by omega) P₁.w.four hl P₁.w.word (by simp only [modS]; omega))
    fun u₁ u₂ ⟨w₁, _⟩ ⟨w₂, _⟩ => ?_
  exact SameTrace.of_relCT (contextSetup_relCT false false n) (agree0 w₁ w₂)

/-- After the setup of an operation, its operands' pointers are still the same. -/
theorem ptrEq_setup {s₁ s₂ u₁ u₂ : State} {base : Addr} {p : Pointer} (hp : PtrOk p) (he : PtrEq base s₁ s₂ p)
    (R₁ : Rest coreClob s₁ u₁) (O₁ : Outs base arithRanges s₁.mem u₁.mem)
    (R₂ : Rest coreClob s₂ u₂) (O₂ : Outs base arithRanges s₂.mem u₂.mem) : PtrEq base u₁ u₂ p := by
  unfold PtrEq
  rw [pointerValue_keep (R₁.gpr .r12 (by decide)) O₁ arith_hdr hp,
    pointerValue_keep (R₂.gpr .r12 (by decide)) O₂ arith_hdr hp]
  exact he

/-- An operation's two loads, followed by code from `r12` public. -/
theorem twoLoads_trace {s₁ s₂ : State} {base : Addr} {size₁ size₂ len expLen n : Nat}
    {a b : Pointer} {rest : Prog isa} (w₁ : Ws s₁ base size₁) (w₂ : Ws s₂ base size₂) (z₁ : 4960 ≤ size₁)
    (z₂ : 4960 ≤ size₂) (w : Width len n)
    (Ra₁ : Ready s₁ base a len) (Ra₂ : Ready s₂ base a len) (Rb₁ : Ready s₁ base b expLen)
    (hea : PtrEq base s₁ s₂ a) (heb : PtrEq base s₁ s₂ b)
    (H : RelCT isa (VG.Arm.Taint.Agree T0) rest (fun _ _ => True)) :
    SameTrace isa (.seq (.seq (Core.load n len (baseS n) a) (Core.load n expLen (expS n) b)) rest) s₁ s₂ := by
  obtain ⟨n0, n48, hl, hl'⟩ := w.bounds
  have s8 := slot_lt (i := 8) n48 (by decide)
  refine SameTrace.assoc_left (SameTrace.seq (load_trace w₁ w₂ (by omega) (by omega) Ra₁.ok hea)
    (load_ok (n := n) (dst := baseS n) w₁ (by omega) Ra₁ (by simp only [baseS]; omega)
      (by simp only [baseS]; omega) (by omega) w.four hl w.word (by simp only [baseS]; omega))
    (load_ok (n := n) (dst := baseS n) w₂ (by omega) Ra₂ (by simp only [baseS]; omega)
      (by simp only [baseS]; omega) (by omega) w.four hl w.word (by simp only [baseS]; omega))
    fun u₁ u₂ ⟨v₁, _, R₁, O₁⟩ ⟨v₂, _, R₂, O₂⟩ => ?_)
  refine loadThen_trace v₁ v₂ (by omega) (by omega) Rb₁.ok ?_
    (RelCT.mono H (fun _ _ A => agree_weaken rfl A) fun _ _ h => h)
  unfold PtrEq
  rw [pointerValue_keep (R₁.gpr .r12 (by decide)) (Outs.of_slot (i := 8) O₁ (by decide) n48) arith_hdr Rb₁.ok,
    pointerValue_keep (R₂.gpr .r12 (by decide)) (Outs.of_slot (i := 8) O₂ (by decide) n48) arith_hdr Rb₁.ok]
  exact heb

theorem power_trace {s₁ s₂ : State} {base : Addr} {size₁ size₂ len expLen n m₁ m₂ output : Nat} {modulus : Field}
    {a b : Pointer} (P₁ : OpPre s₁ base size₁ len n m₁ modulus) (P₂ : OpPre s₂ base size₂ len n m₂ modulus)
    (Ra₁ : Ready s₁ base a len) (Ra₂ : Ready s₂ base a len) (Rb₁ : Ready s₁ base b expLen)
    (hem : PtrEq base s₁ s₂ (.input modulus)) (hea : PtrEq base s₁ s₂ a) (heb : PtrEq base s₁ s₂ b)
    (Rb₂ : Ready s₂ base b expLen) (he4 : 4 ≤ expLen) (he : expLen ≤ len) (hwe : expLen % 4 = 0) :
    SameTrace isa (Core.power len expLen modulus a b output) s₁ s₂ := by
  unfold Core.power
  dsimp only
  rw [← P₁.w.n_eq]
  obtain ⟨n0, n48, hl, hl'⟩ := P₁.w.bounds
  have s0 := slot_lt (i := 0) n48 (by decide)
  have s8 := slot_lt (i := 8) n48 (by decide)
  have s11 := slot_lt (i := 11) n48 (by decide)
  have z₁ := P₁.hz
  have z₂ := P₂.hz
  have cb := contextBytes_le n48
  have ek : (expLen + 3) / 4 ≤ 2 * n := by omega
  -- One run's loads, and what the call needs of them.
  have loads : ∀ {s : State} {size m : Nat}, OpPre s base size len n m modulus → Ready s base a len →
      Ready s base b expLen →
      WP isa (Core.load n len (modS n) (.input modulus)) s fun u => Ws u base size ∧
        val32 u.mem base (slot n 0) (2 * n) = m ∧ Rest [.r4, .r8, .r9, .r10, .r11] s u ∧
        Outs base arithRanges s.mem u.mem ∧ WP isa (.seq (Core.load n len (baseS n) a)
          (Core.load n expLen (expS n) b)) u fun v => Ws v base size ∧
            val32 v.mem base (slot n 0) (2 * n) = m ∧ Rest [.r4, .r8, .r9, .r10, .r11] u v := by
    intro s size m P Ra Rb
    have z := P.hz
    refine WP.mono (load_ok (n := n) (dst := modS n) P.ws (by omega) P.R (by simp only [modS]; omega)
      (by simp only [modS]; omega) (by omega) P.w.four hl P.w.word (by simp only [modS]; omega))
      fun u ⟨wu, Vu, Ru, Ou⟩ => ⟨wu, Vu.trans P.hm, Ru, Outs.of_slot (i := 0) Ou (by decide) n48, ?_⟩
    have Ou' := Outs.of_slot (i := 0) Ou (by decide) n48
    refine WP.seq (WP.mono (load_ok (n := n) (dst := baseS n) wu (by omega)
      (Ra.keep_rest Ru (O := Ou') (hO := arith_hdr)) (by simp only [baseS]; omega)
      (by simp only [baseS]; omega) (by omega) P.w.four hl P.w.word (by simp only [baseS]; omega))
      fun u₁ ⟨w₁, _, R₁, O₁⟩ => ?_)
    refine WP.mono (load_ok (n := n) (dst := expS n) w₁ (by omega)
      ((Rb.keep_rest Ru (O := Ou') (hO := arith_hdr)).keep_rest R₁
        (O := Outs.of_slot (i := 8) O₁ (by decide) n48) (hO := arith_hdr))
      (by simp only [expS]; omega) (by simp only [expS]; omega) (by omega) he4 (by omega) hwe
      (by simp only [expS]; omega)) fun u₂ ⟨w₂, _, R₂, O₂⟩ => ⟨w₂, ?_, R₁.trans R₂⟩
    rw [O₂.val32 (by simp only [expS, slot, stride]; omega) (by simp only [slot, stride]; omega),
      O₁.val32 (by simp only [baseS, slot, stride]; omega) (by simp only [slot, stride]; omega)]
    exact Vu.trans P.hm
  refine SameTrace.seq (load_trace P₁.ws P₂.ws (by omega) (by omega) P₁.R.ok hem) (loads P₁ Ra₁ Rb₁)
    (loads P₂ Ra₂ Rb₂) fun u₁ u₂ ⟨w₁, _, R₁, O₁, L₁⟩ ⟨w₂, _, R₂, O₂, L₂⟩ => ?_
  have pe : ∀ {p : Pointer}, PtrOk p → PtrEq base s₁ s₂ p → PtrEq base u₁ u₂ p := fun hp he => by
    unfold PtrEq
    rw [pointerValue_keep (R₁.gpr .r12 (by decide)) O₁ arith_hdr hp,
      pointerValue_keep (R₂.gpr .r12 (by decide)) O₂ arith_hdr hp]
    exact he
  refine SameTrace.seq ?_ L₁ L₂ fun v₁ v₂ ⟨x₁, V₁, _⟩ ⟨x₂, V₂, _⟩ => ?_
  · have Ra₁' := Ra₁.keep_rest R₁ (O := O₁) (hO := arith_hdr)
    refine SameTrace.seq (load_trace w₁ w₂ (by omega) (by omega) Ra₁.ok (pe Ra₁.ok hea))
      (load_ok (n := n) (dst := baseS n) w₁ (by omega) Ra₁' (by simp only [baseS]; omega)
        (by simp only [baseS]; omega) (by omega) P₁.w.four hl P₁.w.word (by simp only [baseS]; omega))
      (load_ok (n := n) (dst := baseS n) w₂ (by omega) (Ra₂.keep_rest R₂ (O := O₂) (hO := arith_hdr))
        (by simp only [baseS]; omega) (by simp only [baseS]; omega) (by omega) P₁.w.four hl P₁.w.word
        (by simp only [baseS]; omega)) fun y₁ y₂ ⟨k₁, _, Q₁, N₁⟩ ⟨k₂, _, Q₂, N₂⟩ => ?_
    refine load_trace k₁ k₂ (by omega) (by omega) Rb₁.ok ?_
    unfold PtrEq
    rw [pointerValue_keep (Q₁.gpr .r12 (by decide)) (Outs.of_slot (i := 8) N₁ (by decide) n48) arith_hdr Rb₁.ok,
      pointerValue_keep (Q₂.gpr .r12 (by decide)) (Outs.of_slot (i := 8) N₂ (by decide) n48) arith_hdr Rb₁.ok]
    exact pe Rb₁.ok heb
  · have m₁ := P₁.hm1
    have m₂ := P₂.hm1
    refine SameTrace.seq (Pow.call_trace x₁ x₂ (by omega) (by omega) n0 n48 (by omega) ek
        (by rw [V₁]; exact P₁.hodd) (by rw [V₁]; exact m₁) (by rw [V₂]; exact P₂.hodd) (by rw [V₂]; exact m₂))
      (Pow.call_ok x₁ (by omega) n0 n48 (by omega) ek V₁ m₁ P₁.hodd)
      (Pow.call_ok x₂ (by omega) n0 n48 (by omega) ek V₂ m₂ P₂.hodd) fun t₁ t₂ ⟨y₁, _⟩ ⟨y₂, _⟩ => ?_
    exact SameTrace.of_relCT (store_relCT len output) (agree0 y₁ y₂)

theorem productMod_trace {s₁ s₂ : State} {base : Addr} {size₁ size₂ len n m₁ m₂ output : Nat} {modulus : Field}
    {a b : Pointer} (P₁ : OpPre s₁ base size₁ len n m₁ modulus) (P₂ : OpPre s₂ base size₂ len n m₂ modulus)
    (Ra₁ : Ready s₁ base a len) (Ra₂ : Ready s₂ base a len) (Rb₁ : Ready s₁ base b len)
    (hem : PtrEq base s₁ s₂ (.input modulus)) (hea : PtrEq base s₁ s₂ a) (heb : PtrEq base s₁ s₂ b) :
    SameTrace isa (Core.productMod len modulus a b output) s₁ s₂ := by
  unfold Core.productMod
  dsimp only
  rw [← P₁.w.n_eq]
  refine SameTrace.seq (setup_trace P₁ P₂ hem) (setup_ok P₁.ws P₁.hz P₁.w P₁.R P₁.hm P₁.hm1 P₁.hodd)
    (setup_ok P₂.ws P₂.hz P₁.w P₂.R P₂.hm P₂.hm1 P₂.hodd) fun u₁ u₂ ⟨c₁, _, _, O₁, R₁⟩ ⟨c₂, _, _, O₂, R₂⟩ => ?_
  exact twoLoads_trace c₁.ws c₂.ws P₁.hz P₂.hz P₁.w (Ra₁.keep_rest R₁ (O := O₁) (hO := arith_hdr))
    (Ra₂.keep_rest R₂ (O := O₂) (hO := arith_hdr)) (Rb₁.keep_rest R₁ (O := O₁) (hO := arith_hdr))
    (ptrEq_setup Ra₁.ok hea R₁ O₁ R₂ O₂) (ptrEq_setup Rb₁.ok heb R₁ O₁ R₂ O₂)
    ((RelCT.seq (ordinaryMul_relCT n) (store_relCT len output)).mono (fun _ _ h => h) fun _ _ _ => trivial)

theorem sum_trace {s₁ s₂ : State} {base : Addr} {size₁ size₂ len n m₁ m₂ output : Nat}
    {a b : Pointer} (P₁ : OpPre s₁ base size₁ len n m₁ .q) (P₂ : OpPre s₂ base size₂ len n m₂ .q)
    (Ra₁ : Ready s₁ base a len) (Ra₂ : Ready s₂ base a len) (Rb₁ : Ready s₁ base b len)
    (hem : PtrEq base s₁ s₂ (.input .q)) (hea : PtrEq base s₁ s₂ a) (heb : PtrEq base s₁ s₂ b) :
    SameTrace isa (Core.sum len a b output) s₁ s₂ := by
  unfold Core.sum
  dsimp only
  rw [← P₁.w.n_eq]
  refine SameTrace.seq (setup_trace P₁ P₂ hem) (setup_ok P₁.ws P₁.hz P₁.w P₁.R P₁.hm P₁.hm1 P₁.hodd)
    (setup_ok P₂.ws P₂.hz P₁.w P₂.R P₂.hm P₂.hm1 P₂.hodd) fun u₁ u₂ ⟨c₁, _, _, O₁, R₁⟩ ⟨c₂, _, _, O₂, R₂⟩ => ?_
  exact twoLoads_trace c₁.ws c₂.ws P₁.hz P₂.hz P₁.w (Ra₁.keep_rest R₁ (O := O₁) (hO := arith_hdr))
    (Ra₂.keep_rest R₂ (O := O₂) (hO := arith_hdr)) (Rb₁.keep_rest R₁ (O := O₁) (hO := arith_hdr))
    (ptrEq_setup Ra₁.ok hea R₁ O₁ R₂ O₂) (ptrEq_setup Rb₁.ok heb R₁ O₁ R₂ O₂)
    ((RelCT.seq (ordinaryAdd_relCT n) (store_relCT len output)).mono (fun _ _ h => h) fun _ _ _ => trivial)

/-! ## Reductions -/

theorem reduceHead_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (hz : 120 ≤ size)
    {input : Pointer} (hp : PtrOk input) {count : Core.Count} (hc : CountOk count) :
    WP isa (.block (Core.pointer input ++ Core.countEnd count)) s fun x =>
      x.gpr .r11 = pointerValue base s input ∧
      x.gpr .lr = pointerValue base s input + BitVec.ofNat 32 (countValue base s count) ∧
      Rest [.r4, .r11, .lr] s x ∧ x.mem = s.mem := by
  refine VG.Proof.X25519.Arm.WP.append (pointer_ok hs hz hp) fun v ⟨Pv, Rv, Mv⟩ =>
    WP.mono (countEnd_ok (hs.of_rest Rv (by decide)) hz hc) fun x ⟨Lx, Rx, Mx⟩ => ⟨?_, ?_, ?_, by rw [Mx, Mv]⟩
  · rw [Rx.gpr .r11 (by decide), Pv]
  · have Cv : countValue base v count = countValue base s count :=
      countValue_keep (rs := []) (fun x _ => by rw [Mv]) (by simp) hc
    rw [Lx, Cv, Pv]
  · exact (Rv.mono (by decide)).trans (Rx.mono (by decide))

theorem reduce_trace {s₁ s₂ : State} {base : Addr} {size₁ size₂ len n m₁ m₂ output : Nat} {count : Core.Count}
    {input : Pointer} (P₁ : OpPre s₁ base size₁ len n m₁ .q) (P₂ : OpPre s₂ base size₂ len n m₂ .q)
    (hp : PtrOk input) (hc : CountOk count)
    (hem : PtrEq base s₁ s₂ (.input .q)) (hei : PtrEq base s₁ s₂ input)
    (hec : countValue base s₁ count = countValue base s₂ count) :
    SameTrace isa (Core.reduce len count input output) s₁ s₂ := by
  unfold Core.reduce
  dsimp only
  rw [← P₁.w.n_eq]
  have z₁ := P₁.hz
  have z₂ := P₂.hz
  refine SameTrace.seq (setup_trace P₁ P₂ hem) (setup_ok P₁.ws P₁.hz P₁.w P₁.R P₁.hm P₁.hm1 P₁.hodd)
    (setup_ok P₂.ws P₂.hz P₁.w P₂.R P₂.hm P₂.hm1 P₂.hodd) fun u₁ u₂ ⟨c₁, _, _, O₁, R₁⟩ ⟨c₂, _, _, O₂, R₂⟩ => ?_
  have pe := ptrEq_setup hp hei R₁ O₁ R₂ O₂
  have ce : countValue base u₁ count = countValue base u₂ count := by
    rw [countValue_keep O₁ arith_hdr hc, countValue_keep O₂ arith_hdr hc]; exact hec
  refine SameTrace.seq (SameTrace.of_relCT (reduceHead_relCT input count) (agree0 c₁.ws c₂.ws))
    (reduceHead_ok c₁.ws (by omega) hp hc) (reduceHead_ok c₂.ws (by omega) hp hc)
    fun x₁ x₂ ⟨A₁, L₁, Q₁, _⟩ ⟨A₂, L₂, Q₂, _⟩ => ?_
  exact SameTrace.of_relCT (RelCT.seq (reduceStream_relCT n)
      ((store_relCT len output).mono (fun _ _ A => agree_weaken rfl A) fun _ _ h => h))
    (agreeWs true true (c₁.ws.of_rest Q₁ (by decide)) (c₂.ws.of_rest Q₂ (by decide))
      (fun _ => by rw [A₁, A₂, pe]) (fun _ => by rw [L₁, L₂, pe, ce]))

end VG.Proof.Dsa.Arm
