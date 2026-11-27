module

import VerifiedGarbage.Proof.Mont.X86.Rt.ScalarVerified
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Double
public import VerifiedGarbage.Proof.Mont.X86.OutsZ
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public import Init.Core
public import VerifiedGarbage.Impl.Mont.X86.MulRt
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Mont.X86.ArgWs
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr

/-! ### `Bignum.X86.PublicRt.MulArgs`, which this module and modules that import it used -/

section

/-! # The arguments of a multiplication in public RSA at a run-time width

`mulArgs o a b` stores the nine arguments of `vg_rsa_mont_mul_at` into the
frame of 36 bytes at `esp` (`mulArgs_ok`): word `i` is `mulArg … i`.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont VG.Proof.Mont.X86

/-- Argument `i` of the call for the numbers `o`, `a` and `b`, from `edi` and `ws_len`. -/
def mulArg (len o a b : Nat) (edi wsLen : BitVec 32) : Nat → BitVec 32
  | 0 => edi
  | 1 => wsLen
  | 2 => BitVec.ofNat 32 (Spec.Rsa.modulusWords len)
  | 3 => BitVec.ofNat 32 numOff
  | 4 => BitVec.ofNat 32 invOff
  | 5 => BitVec.ofNat 32 (numAt len 5)
  | 6 => BitVec.ofNat 32 (numAt len o)
  | 7 => BitVec.ofNat 32 (numAt len a)
  | _ => BitVec.ofNat 32 (numAt len b)

/-- `offEax j`: `eax = 256 + j B`, from `edx = B`. -/
theorem offEax_ok {s : State} {is : List Instr} {Q : State → Prop} {len j : Nat}
    (hedx : s.gpr .edx = BitVec.ofNat 32 (wb len)) (hl : len ≤ 1024) (hj : j ≤ 8)
    (kk : ∀ u, Keeps [.eax] s u → u.mem = s.mem → u.gpr .eax = BitVec.ofNat 32 (numAt len j) →
      WP isa (.block is) u Q) :
    WP isa (.block (offEax j ++ is)) s Q := by
  obtain hw := wb_le hl
  simp only [offEax, List.cons_append]
  refine wp_movS rfl fun s₁ u₁ _ => adds_ok (r := .eax) (t := .edx) (by decide) j fun u K m e => ?_
  refine kk u (u₁.keeps.trans K) (by rw [m, u₁.mem]) ?_
  rw [e, u₁.gpr, u₁.other _ (by decide), hedx]
  apply BitVec.eq_of_toNat_eq
  have : j * wb len ≤ 8 * 1024 := Nat.mul_le_mul hj hw
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, numAt, numOff]
  rw [Nat.mod_eq_of_lt (a := wb len) (by omega_using [hw]), Nat.mod_eq_of_lt (a := j * wb len) (by omega_using [this])]

/-- A store into the frame at `esp`. -/
theorem frame_store {t : State} {P : Addr} (hP : (t.gpr .esp).setWidth 64 = P) (hesp : (t.gpr .esp).toNat + 36 ≤ 2 ^ 32)
    (hfr : (⟨P, 36⟩ : Region) ∈ t.wr) {k : Nat} (hk : k + 4 ≤ 36) :
    t.ea (at_ .esp k) = P + BitVec.ofNat 64 k ∧ InRegions t.wr (P + BitVec.ofNat 64 k) 4 := by
  refine ⟨?_, ⟨_, hfr, Offset.contains_base _ hk (by omega_using [hk])⟩⟩
  rw [at_, ea_mk, addr_eq (by omega_using [hesp, hk]), hP]

/-- A word of the frame, after a store to another. -/
theorem frame_other (m : Mem) (P : Addr) (v : BitVec 32) {k j : Nat} (h : j + 4 ≤ k ∨ k + 4 ≤ j)
    (hk : k + 4 ≤ 36) (hj : j + 4 ≤ 36) :
    (m.writeW (P + BitVec.ofNat 64 k) v).readW (P + BitVec.ofNat 64 j) 32 = m.readW (P + BitVec.ofNat 64 j) 32 :=
  Mem.readW_writeW_sep (Offset.sep P h (by omega_using [hj]) (by omega_using [hk])) (by decide)

theorem mulArgs_ok {f : State} {len o a b wl : Nat} {wsLen : BitVec 32}
    (hr3 : readSrc f (.mem (argAt 9 1)) = some (BitVec.ofNat 32 len))
    (hr9 : readSrc f (.mem (argAt 9 wl)) = some wsLen)
    (hl : len ≤ 1024) (ho : o ≤ 8) (ha : a ≤ 8) (hb : b ≤ 8)
    (hesp : (f.gpr .esp).toNat + 36 ≤ 2 ^ 32) (hfr : (⟨(f.gpr .esp).setWidth 64, 36⟩ : Region) ∈ f.wr) :
    WP isa (.block (mulArgs o a b wl)) f fun g =>
      Keeps [.eax, .edx] f g ∧ Frame [⟨(f.gpr .esp).setWidth 64, 36⟩] f.mem g.mem ∧
      ∀ i < 9, g.mem.readW ((f.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 * i)) 32 =
        mulArg len o a b (f.gpr .edi) wsLen i := by
  obtain hw := wb_le hl
  generalize hP : (f.gpr .esp).setWidth 64 = P at hfr ⊢
  simp only [mulArgs, List.append_assoc, List.cons_append, List.nil_append]
  refine widthB_ok hr3 hl fun s₁ K₁ m₁ e₁ => ?_
  -- A state reached by registers but `esp`: the same frame.
  obtain fr : ∀ t : State, t.gpr .esp = f.gpr .esp → t.wr = f.wr → ∀ k, k + 4 ≤ 36 →
      t.ea (at_ .esp k) = P + BitVec.ofNat 64 k ∧ InRegions t.wr (P + BitVec.ofNat 64 k) 4 :=
    fun t he hw' k hk => frame_store (by rw [he, hP]) (by rw [he]; exact hesp) (by rw [hw']; exact hfr) hk
  obtain sp₁ : s₁.gpr .esp = f.gpr .esp := K₁.1 _ (by decide)
  obtain edi₁ : s₁.gpr .edi = f.gpr .edi := K₁.1 _ (by decide)
  obtain hr9₁ : readSrc s₁ (.mem (argAt 9 wl)) = some wsLen := by
    rw [← hr9]; simp only [readSrc, State.load32, State.ea, argAt, at_, sp₁, m₁, K₁.2.1, K₁.2.2]; rfl
  refine wp_movS hr9₁ fun s₂ u₂ _ => ?_
  obtain K₂ : Keeps [.eax, .edx] f s₂ := (K₁.mono (by decide)).trans (u₂.keeps.mono (by decide))
  obtain ⟨a₄, w₄⟩ := fr s₂ (K₂.1 _ (by decide)) K₂.2.2 4 (by decide)
  refine wp_storeS a₄ w₄ fun s₃ m₃ => ?_
  obtain ⟨a₀, w₀⟩ := fr s₃ (by rw [m₃.gpr]; exact K₂.1 _ (by decide)) (by rw [m₃.wr]; exact K₂.2.2) 0 (by decide)
  refine wp_storeS a₀ w₀ fun s₄ m₄ => ?_
  obtain K₄ : Keeps [.eax, .edx] f s₄ := (K₂.trans (m₃.keeps _)).trans (m₄.keeps _)
  refine wp_movS rfl fun s₅ u₅ _ => wp_shr (by decide) fun s₆ u₆ => ?_
  obtain K₆ : Keeps [.eax, .edx] f s₆ := (K₄.trans (u₅.keeps.mono (by decide))).trans (u₆.keeps.mono (by decide))
  obtain ⟨a₈, w₈⟩ := fr s₆ (K₆.1 _ (by decide)) K₆.2.2 8 (by decide)
  refine wp_storeS a₈ w₈ fun s₇ m₇ => wp_movS rfl fun s₈ u₈ _ => ?_
  obtain K₈ : Keeps [.eax, .edx] f s₈ := (K₆.trans (m₇.keeps _)).trans (u₈.keeps.mono (by decide))
  obtain ⟨a₁₂, w₁₂⟩ := fr s₈ (K₈.1 _ (by decide)) K₈.2.2 12 (by decide)
  refine wp_storeS a₁₂ w₁₂ fun s₉ m₉ => wp_movS rfl fun s₁₀ u₁₀ _ => ?_
  obtain K₁₀ : Keeps [.eax, .edx] f s₁₀ := (K₈.trans (m₉.keeps _)).trans (u₁₀.keeps.mono (by decide))
  obtain ⟨a₁₆, w₁₆⟩ := fr s₁₀ (K₁₀.1 _ (by decide)) K₁₀.2.2 16 (by decide)
  refine wp_storeS a₁₆ w₁₆ fun s₁₁ m₁₁ => ?_
  obtain K₁₁ : Keeps [.eax, .edx] f s₁₁ := K₁₀.trans (m₁₁.keeps _)
  -- `edx` holds `B` from `widthB` on.
  obtain edx : ∀ t : State, Keeps [.eax] s₁ t → t.gpr .edx = BitVec.ofNat 32 (wb len) :=
    fun t K => by rw [K.1 _ (by decide), e₁]
  obtain edx₁₁ : s₁₁.gpr .edx = BitVec.ofNat 32 (wb len) := edx s₁₁ (by
    refine ⟨fun r hr => ?_, ?_, ?_⟩
    · rw [m₁₁.gpr, u₁₀.other _ (by simpa using hr), m₉.gpr, u₈.other _ (by simpa using hr), m₇.gpr,
        u₆.other _ (by simpa using hr), u₅.other _ (by simpa using hr), m₄.gpr, m₃.gpr,
        u₂.other _ (by simpa using hr)]
    · rw [m₁₁.rd, u₁₀.rd, m₉.rd, u₈.rd, m₇.rd, u₆.rd, u₅.rd, m₄.rd, m₃.rd, u₂.rd]
    · rw [m₁₁.wr, u₁₀.wr, m₉.wr, u₈.wr, m₇.wr, u₆.wr, u₅.wr, m₄.wr, m₃.wr, u₂.wr])
  refine offEax_ok (j := 5) edx₁₁ hl (by decide) fun s₁₂ K₁₂ m₁₂ e₁₂ => ?_
  obtain K₁₂' : Keeps [.eax, .edx] f s₁₂ := K₁₁.trans (K₁₂.mono (by decide))
  obtain ⟨a₂₀, w₂₀⟩ := fr s₁₂ (K₁₂'.1 _ (by decide)) K₁₂'.2.2 20 (by decide)
  refine wp_storeS a₂₀ w₂₀ fun s₁₃ m₁₃ => ?_
  obtain edx₁₃ : s₁₃.gpr .edx = BitVec.ofNat 32 (wb len) := by rw [m₁₃.gpr, K₁₂.1 _ (by decide), edx₁₁]
  refine offEax_ok (j := o) edx₁₃ hl ho fun s₁₄ K₁₄ m₁₄ e₁₄ => ?_
  obtain K₁₄' : Keeps [.eax, .edx] f s₁₄ := (K₁₂'.trans (m₁₃.keeps _)).trans (K₁₄.mono (by decide))
  obtain ⟨a₂₄, w₂₄⟩ := fr s₁₄ (K₁₄'.1 _ (by decide)) K₁₄'.2.2 24 (by decide)
  refine wp_storeS a₂₄ w₂₄ fun s₁₅ m₁₅ => ?_
  obtain edx₁₅ : s₁₅.gpr .edx = BitVec.ofNat 32 (wb len) := by rw [m₁₅.gpr, K₁₄.1 _ (by decide), edx₁₃]
  refine offEax_ok (j := a) edx₁₅ hl ha fun s₁₆ K₁₆ m₁₆ e₁₆ => ?_
  obtain K₁₆' : Keeps [.eax, .edx] f s₁₆ := (K₁₄'.trans (m₁₅.keeps _)).trans (K₁₆.mono (by decide))
  obtain ⟨a₂₈, w₂₈⟩ := fr s₁₆ (K₁₆'.1 _ (by decide)) K₁₆'.2.2 28 (by decide)
  refine wp_storeS a₂₈ w₂₈ fun s₁₇ m₁₇ => ?_
  obtain edx₁₇ : s₁₇.gpr .edx = BitVec.ofNat 32 (wb len) := by rw [m₁₇.gpr, K₁₆.1 _ (by decide), edx₁₅]
  refine offEax_ok (j := b) edx₁₇ hl hb fun s₁₈ K₁₈ m₁₈ e₁₈ => ?_
  obtain K₁₈' : Keeps [.eax, .edx] f s₁₈ := (K₁₆'.trans (m₁₇.keeps _)).trans (K₁₈.mono (by decide))
  obtain ⟨a₃₂, w₃₂⟩ := fr s₁₈ (K₁₈'.1 _ (by decide)) K₁₈'.2.2 32 (by decide)
  refine wp_storeS a₃₂ w₃₂ fun g mg => WP.block_nil ?_
  obtain edx₄ : s₄.gpr .edx = BitVec.ofNat 32 (wb len) := by rw [m₄.gpr, m₃.gpr, u₂.other _ (by decide), e₁]
  obtain eW : s₆.gpr .eax = BitVec.ofNat 32 (Spec.Rsa.modulusWords len) := by
    rw [u₆.gpr, u₅.gpr, edx₄]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, wb]
    have : 8 * Spec.Rsa.modulusWords len ≤ 1024 := hw
    rw [Nat.mod_eq_of_lt (by omega_using [this]), Nat.mod_eq_of_lt (by simp only [Spec.Rsa.modulusWords]; omega_using [hl])]
    omega_using []
  obtain mem : g.mem = ((((((((f.mem.writeW (P + BitVec.ofNat 64 4) wsLen).writeW (P + BitVec.ofNat 64 0)
      (f.gpr .edi)).writeW (P + BitVec.ofNat 64 8) (BitVec.ofNat 32 (Spec.Rsa.modulusWords len))).writeW
      (P + BitVec.ofNat 64 12) (BitVec.ofNat 32 numOff)).writeW (P + BitVec.ofNat 64 16)
      (BitVec.ofNat 32 invOff)).writeW (P + BitVec.ofNat 64 20) (BitVec.ofNat 32 (numAt len 5))).writeW
      (P + BitVec.ofNat 64 24) (BitVec.ofNat 32 (numAt len o))).writeW (P + BitVec.ofNat 64 28)
      (BitVec.ofNat 32 (numAt len a))).writeW (P + BitVec.ofNat 64 32) (BitVec.ofNat 32 (numAt len b)) := by
    rw [mg.mem, m₁₈, m₁₇.mem, m₁₆, m₁₅.mem, m₁₄, m₁₃.mem, m₁₂, m₁₁.mem, u₁₀.mem, m₉.mem, u₈.mem, m₇.mem,
      u₆.mem, u₅.mem, m₄.mem, m₃.mem, u₂.mem, m₁, e₁₈, e₁₆, e₁₄, e₁₂, u₁₀.gpr, u₈.gpr, eW, m₃.gpr,
      u₂.gpr, u₂.other .edi (by decide), edi₁]
  refine ⟨K₁₈'.trans (mg.keeps _), ?_, ?_⟩
  · have fw : ∀ {m : Mem} (k : Nat) (v : BitVec 32), k + 4 ≤ 36 → Frame [⟨P, 36⟩] f.mem m →
        Frame [⟨P, 36⟩] f.mem (m.writeW (P + BitVec.ofNat 64 k) v) := fun k v hk F =>
      F.writeW (List.mem_singleton_self _) v (Offset.contains_base _ hk (by omega_using [hk]))
    rw [mem]
    exact fw _ _ (by decide) <| fw _ _ (by decide) <| fw _ _ (by decide) <| fw _ _ (by decide) <|
      fw _ _ (by decide) <| fw _ _ (by decide) <| fw _ _ (by decide) <| fw _ _ (by decide) <|
      fw _ _ (by decide) (Frame.refl _ _)
  · intro i hi
    rw [mem]
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i
    all_goals first
      | omega
      | simp (disch := decide) only [frame_other, Mem.readW_writeW_self32, mulArg, Nat.mul_zero, Nat.reduceMul,
          Nat.reduceAdd, Nat.zero_add]

end VG.Proof.Bignum.X86.PublicRt

end

end

/-! # The precondition of a call of `vg_rsa_mont_mul_at` from public RSA

From the frame of its arguments (`mulArgs_ok`) below the caller's `esp`,
apart from the working space (`CallRoom`): the callee's state, with its
permissions narrowed to its arguments and the working space, meets its
precondition (`callee_abi`, `callee_pre`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Rsa.MontMul (Apart scratchBytes)

/-- The callee's precondition from its facts and the 56 bytes of stack below
its `esp`, apart from the working space and the arguments. -/
theorem rtPre_of {s : State} (A : RtABI s) (stackLo : 56 ≤ (s.gpr .esp).toNat)
    (stkScratch : (⟨(s.gpr .esp).setWidth 64 - 56#64, 56⟩ : Region).Disjoint ⟨wsOf s, lenOf s⟩)
    (stkArgs : (⟨(s.gpr .esp).setWidth 64 - 56#64, 56⟩ : Region).Disjoint ⟨argAddr s 0, 36⟩) :
    (Proof.Rsa.MontMul.mulContract abi 56).pre s := by
  cases A
  sig_pre [Proof.Rsa.MontMul.mulContract, Proof.Rsa.MontMul.sig, abi, argSlots, argVal, argBytes, stackBelow]
  sig_and_intros
  all_goals with_reducible assumption

/-- The callee's state: the call's, with the permissions of the arguments and the working space. -/
abbrev calleeOf (g : State) (base : Addr) (bytes : Nat) : State :=
  g.callEntry.withRegions [⟨argAddr g.callEntry 0, 36⟩] [⟨base, bytes⟩]

/-- An address of the stack, as a number. -/
theorem setWidth_toNat (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]

theorem callee_abi {s g : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : RtIn base bytes len args s) (hbytes : bytes = (args 9).toNat * 8)
    (R : CallRoom (s.gpr .esp) base bytes) {o a b : Nat} (ho : o ≤ 4) (ha : a ≤ 4) (hb : b ≤ 4)
    (ho0 : o ≠ 0) (hesp : g.gpr .esp = s.gpr .esp - BitVec.ofNat 32 36)
    (hFg : Frame [below (s.gpr .esp) 36] s.mem g.mem)
    (hread : ∀ i < 9, g.mem.readW ((g.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 * i)) 32 =
        mulArg len o a b (s.gpr .edi) (args 9) i)
    (hinv : (val32 s.mem base numOff (nw len) * w32 s.mem base invOff + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem base (numAt len b) (nw len) < val32 s.mem base numOff (nw len)) :
    RtABI (calleeOf g base bytes) := by
  have low := R.low
  obtain hsp := (s.gpr .esp).isLt
  have nwr := h.scratch.nowrap
  obtain hw := wb_le h.upper
  have dims := h.dimensions
  obtain f5 := (h.fits (j := 5) (by decide)).2
  obtain wbe := wb_eq len
  obtain gEsp : (g.gpr .esp).toNat = (s.gpr .esp).toNat - 36 := by rw [hesp, sub_toNat (by omega_arith)]
  obtain argc : ∀ i < 9, arg (calleeOf g base bytes) i = mulArg len o a b (s.gpr .edi) (args 9) i := by
    intro i hi
    show arg g.callEntry i = _
    rw [arg_callEntry (by omega_arith) (by omega_arith)]
    obtain e := addr_eq (x := g.gpr .esp) (k := 4 * i) (by omega_arith)
    simp only [addr] at e
    rw [e, hread i hi]
  obtain v8 : ∀ j ≤ 8, numAt len j < 2 ^ 32 := fun j hj => by
    have := Nat.mul_le_mul hj hw; simp only [numAt, numOff]; omega_arith
  obtain v0 : (arg (calleeOf g base bytes) 0).toNat = base.toNat := by rw [argc 0 (by decide)]; exact h.edi
  obtain v1 : (arg (calleeOf g base bytes) 1).toNat * 8 = bytes := by rw [argc 1 (by decide)]; exact hbytes.symm
  obtain vn : ∀ {v : Nat}, v < 2 ^ 32 → (BitVec.ofNat 32 v).toNat = v := fun hv => by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
  obtain v2 : (arg (calleeOf g base bytes) 2).toNat = Spec.Rsa.modulusWords len := by
    rw [argc 2 (by decide)]; exact vn (by simp only [Spec.Rsa.modulusWords]; omega_arith)
  obtain v3 : (arg (calleeOf g base bytes) 3).toNat = numOff := by rw [argc 3 (by decide)]; exact vn (by decide)
  obtain v4 : (arg (calleeOf g base bytes) 4).toNat = invOff := by rw [argc 4 (by decide)]; exact vn (by decide)
  obtain v5 : (arg (calleeOf g base bytes) 5).toNat = numAt len 5 := by
    rw [argc 5 (by decide)]; exact vn (v8 5 (by decide))
  obtain v6 : (arg (calleeOf g base bytes) 6).toNat = numAt len o := by
    rw [argc 6 (by decide)]; exact vn (v8 o (by omega_arith))
  obtain v7 : (arg (calleeOf g base bytes) 7).toNat = numAt len a := by
    rw [argc 7 (by decide)]; exact vn (v8 a (by omega_arith))
  obtain v8' : (arg (calleeOf g base bytes) 8).toNat = numAt len b := by
    rw [argc 8 (by decide)]; exact vn (v8 b (by omega_arith))
  obtain ws : wsOf (calleeOf g base bytes) = base := by
    show (arg (calleeOf g base bytes) 0).setWidth 64 = base
    rw [argc 0 (by decide)]; exact h.scratch.edi
  have ln : lenOf (calleeOf g base bytes) = bytes := v1
  -- The memory of the working space is the caller's.
  obtain Fc : Frame [below (s.gpr .esp) 40] s.mem (calleeOf g base bytes).mem := by
    obtain F₁ : Frame [below (g.gpr .esp) 4] g.mem g.callEntry.mem :=
      Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (below_top (Nat.le_refl 4) (by omega_arith) (by decide))
    refine (hFg.sub fun r hr => ?_).trans (F₁.sub fun r hr => ?_)
    · rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, below_sub (by decide) (by omega_arith)⟩
    · rw [List.mem_singleton.mp hr, hesp]
      exact ⟨_, List.mem_singleton_self _, below_inner (by decide) (by omega_arith)⟩
  obtain numc : ∀ d k, d + k ≤ bytes → Proof.Rsa.MontMul.numAt (calleeOf g base bytes).mem base d k =
      Proof.Rsa.MontMul.numAt s.mem base d k := fun d k hdk => by
    unfold Proof.Rsa.MontMul.numAt
    rw [Fc.read (r := ⟨base, bytes⟩) (Offset.contains_base _ hdk (by omega_arith))
      (fun r' hr' => by rw [List.mem_singleton.mp hr']; exact R.apart40.symm) (by omega_arith)]
  obtain argAddr0 : argAddr (calleeOf g base bytes) 0 = (g.gpr .esp).setWidth 64 := by
    show argAddr g.callEntry 0 = _
    rw [argAddr_callEntry]; simp
  obtain retBase : ((calleeOf g base bytes).gpr .esp).setWidth 64 = (g.gpr .esp - 4).setWidth 64 := by
    simp [calleeOf]
  have W2 : 2 * Spec.Rsa.modulusWords len = nw len := rfl
  obtain e04 : numAt len 4 + wb len ≤ numAt len 5 := by simp only [numAt]; omega_arith
  obtain so : ∀ j ≤ 4, numAt len j + wb len ≤ numAt len 5 := fun j hj => by
    have := Nat.mul_le_mul_right (wb len) hj; simp only [numAt] at *; omega_arith
  obtain fo := (h.fits (j := o) (by omega_arith)).1
  obtain fa := (h.fits (j := a) (by omega_arith)).1
  obtain fb := (h.fits (j := b) (by omega_arith)).1
  obtain f0 := (h.fits (j := 0) (by decide)).1
  have ewb : wb len = 8 * Spec.Rsa.modulusWords len := rfl
  obtain n0 : numAt len 0 = numOff := by simp [numAt]
  obtain no : numOff + wb len ≤ numAt len o := by
    have := Nat.mul_le_mul_right (wb len) (Nat.one_le_iff_ne_zero.mpr ho0); simp only [numAt] at *; omega_arith
  refine ⟨?_, rfl, by rw [ws, ln]; rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · show (g.gpr .esp - 4).toNat + 4 + 36 ≤ 2 ^ 32
    rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, sub_toNat (by omega_arith)]; omega_arith
  · rw [ws, ln, argAddr0, hesp]; exact (R.apart.sub_left (below_sub (by decide) low)).symm
  · rw [retBase, ws, ln, hesp]; exact R.apart.sub_left (below_inner (a := 4) (k := 36) (b := 96) (by decide) low)
  · rw [retBase, argAddr0]
    refine Region.disjoint_of_le (.inl ?_) ?_ ?_ <;> simp only [setWidth_toNat] <;>
      (try rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, sub_toNat (by omega_arith)]) <;> omega_arith
  · rw [v0, ln]; exact nwr
  · rw [v2]; exact dims.1
  · rw [v3, v2]; simp only [numOff] at f0 n0 ⊢; omega_arith
  · rw [v4]; simp only [numOff, invOff] at f0 n0 ⊢; omega_arith
  · rw [v5, v2]; simp only [scratchBytes]; omega_arith
  · rw [v6, v2]; omega_arith
  · rw [v7, v2]; omega_arith
  · rw [v8', v2]; omega_arith
  · rw [v3, v5, v2]; unfold Apart; have := so 0 (by decide); simp only [scratchBytes]; rw [n0] at this; omega_arith
  · rw [v4, v5, v2]; unfold Apart; have := so 0 (by decide); simp only [scratchBytes, invOff]; rw [n0] at this
    simp only [numOff] at this; omega_arith
  · rw [v6, v5, v2]; unfold Apart; have := so o ho; omega_arith
  · rw [v7, v5, v2]; unfold Apart; have := so a ha; omega_arith
  · rw [v8', v5, v2]; unfold Apart; have := so b hb; omega_arith
  · rw [v6, v3, v2]; unfold Apart; omega_arith
  · rw [v6, v4, v2]; unfold Apart; simp only [numOff, invOff] at no ⊢; omega_arith
  · rw [ws, v3, v2, v4, numc _ _ (by rw [← n0]; omega_arith), numc _ _ (by simp only [invOff, numOff] at n0 ⊢; omega_arith),
      numAt_val32, numAt_w32]
    exact hinv
  · rw [ws, v8', v3, v2, numc _ _ (by omega_arith), numc _ _ (by rw [← n0]; omega_arith), numAt_val32, numAt_val32]
    exact hB

/-- The callee's precondition, at a call 36 bytes below `esp`: its 56 bytes
of stack are among the 96 of the call's room. -/
theorem callee_pre {s g : State} {base : Addr} {bytes : Nat} (A : RtABI (calleeOf g base bytes))
    (R : CallRoom (s.gpr .esp) base bytes) (hesp : g.gpr .esp = s.gpr .esp - BitVec.ofNat 32 36) :
    (Proof.Rsa.MontMul.mulContract abi 56).pre (calleeOf g base bytes) := by
  have low := R.low
  obtain hsp := (s.gpr .esp).isLt
  obtain eW : (⟨wsOf (calleeOf g base bytes), lenOf (calleeOf g base bytes)⟩ : Region) = ⟨base, bytes⟩ := by
    have h := A.wr
    simp only [calleeOf, State.withRegions_wr, List.cons.injEq, and_true] at h
    exact h.symm
  obtain e : (calleeOf g base bytes).gpr .esp = s.gpr .esp - BitVec.ofNat 32 40 := by
    show g.callEntry.gpr .esp = _
    rw [State.callEntry_esp, hesp, BitVec.sub_sub]; rfl
  obtain e40 : (s.gpr .esp - BitVec.ofNat 32 40).toNat = (s.gpr .esp).toNat - 40 := sub_toNat (by omega_using [low])
  obtain e56 : ((calleeOf g base bytes).gpr .esp).setWidth 64 - 56#64 =
      (s.gpr .esp - BitVec.ofNat 32 40 - BitVec.ofNat 32 56).setWidth 64 := by
    rw [e]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_using [low]
  obtain sub : Region.Sub ⟨((calleeOf g base bytes).gpr .esp).setWidth 64 - 56#64, 56⟩ (below (s.gpr .esp) 96) := by
    rw [e56]; exact below_inner (a := 56) (k := 40) (b := 96) (by decide) low
  refine rtPre_of A (by rw [e, e40]; omega_using [low]) (by rw [eW]; exact R.apart.sub_left sub) ?_
  obtain argA : argAddr (calleeOf g base bytes) 0 = (g.gpr .esp).setWidth 64 := by
    show argAddr g.callEntry 0 = _
    rw [argAddr_callEntry]; simp
  obtain e96 : (s.gpr .esp - BitVec.ofNat 32 40 - BitVec.ofNat 32 56).toNat = (s.gpr .esp).toNat - 96 := by
    rw [sub_toNat (by rw [e40]; omega_using [low]), e40]; omega_using []
  obtain e36 : (s.gpr .esp - BitVec.ofNat 32 36).toNat = (s.gpr .esp).toNat - 36 := sub_toNat (by omega_using [low])
  rw [argA, e56, hesp]
  refine Region.disjoint_of_le (.inl ?_) ?_ ?_ <;> simp only [setWidth_toNat, e96, e36] <;> omega_arith

end VG.Proof.Bignum.X86.PublicRt
