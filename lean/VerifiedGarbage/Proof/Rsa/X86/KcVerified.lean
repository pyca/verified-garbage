module

public import VerifiedGarbage.Proof.Rsa.X86.KcBuffers
public import VerifiedGarbage.Impl.Rsa.X86.KeyCheckRt
public import VerifiedGarbage.Proof.Rsa.X86.KcFrames
public import VerifiedGarbage.Proof.Rsa.X86.KcTimeCheck
public import VerifiedGarbage.Proof.Rsa.X86.KcResult
public import VerifiedGarbage.Proof.Rsa.X86.KcLoads
public import VerifiedGarbage.Proof.Rsa.X86.WordRt.Time
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Rsa.X86.KcStart
import VerifiedGarbage.Proof.Rsa.X86.InvParts
import VerifiedGarbage.Proof.Rsa.X86.KcLoad
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Ops
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Rsa.X86.WordRt.Mul
import VerifiedGarbage.Proof.Rsa.X86.WordRt.Loop
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeExp
public import VerifiedGarbage.Proof.Rsa.X86.KcInputs
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Framework.RegSet
public import VerifiedGarbage.Proof.Framework.Slots
public import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.X86.ExponentCheckTiming
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86.PublicExponentArgs
import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Spec.RsaKeyGen
public import VerifiedGarbage.Impl.Rsa.X86.KeyCheck
public import VerifiedGarbage.Proof.Bignum.X86.PublicArgumentTiming
public import VerifiedGarbage.Proof.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.X86.PublicEntryTiming
import VerifiedGarbage.Proof.Bignum.MemoryFrame
public import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Bignum.X86.PublicReturn
import VerifiedGarbage.Proof.Bignum.X86.PublicSave
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Weierstrass.Env
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Bignum.X86.ModulusCheck
import VerifiedGarbage.Proof.Bignum.X86.ExponentCheck
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Spec.Weierstrass

/-! ### `Rsa.X86.KcInstalled`, which only this module used -/

section

/-! # Install key-check call resources after saving the caller's registers -/

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/KcEntry.lean`, which only this module imported.
section

/-! # Establishing the arithmetic workspace while preserving the caller ABI -/

section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.X86.Wp VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Bignum.X86 VG.Proof.Bignum.X86

theorem entry_ok (full : Bool) {s : State} {base : Addr} {size : Nat} {ptr : BitVec 32}
    (read : readSrc s (.mem (PublicFn.argument (VG.Impl.Rsa.X86.KeyCheck.scratchArg full))) = some ptr)
    (hb : ptr.setWidth 64 = base) (hf : ptr.toNat + size ≤ 2 ^ 32) (hz : 16 ≤ size)
    (hw : (⟨base, size⟩ : Region) ∈ s.wr) (stk : StkOk (s.gpr .esp) base size) :
    WP isa (.block (VG.Impl.Rsa.X86.KeyCheck.entry full)) s fun t =>
      Scr t base size ∧ Saved t.mem (off base) s.gpr PublicFn.savedRegisters ∧
      Keeps [.eax, .edi] s t ∧ Outside base 0 size s.mem t.mem := by
  unfold VG.Impl.Rsa.X86.KeyCheck.entry
  simp only [List.singleton_append]
  refine wp_movS read fun u U _ => ?_
  refine WP.block_append (WP.mono (entrySave_ok (base := base) (size := size) (by rw [U.gpr]; exact hb)
    (by rw [U.gpr]; exact hf) hz (by rw [U.wr]; exact hw)) fun v ⟨G, Rd, Wr, S, F⟩ => ?_)
  refine wp_movS rfl fun t T _ => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [T.gpr, G, U.gpr]; exact hb
    · rw [T.wr, Wr, U.wr]; exact hw
    · rw [← hb, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans ptr.isLt (by decide))]
      exact hf
    · rw [T.other _ (by decide), G, U.other _ (by decide)]
      exact stk
  · intro p hp
    rw [T.mem, S p hp]
    have H : p.1 ≠ .eax := by
      simp only [PublicFn.savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> decide
    exact U.other _ H
  · refine ⟨?_, ?_, ?_⟩
    · intro reg hr
      rw [T.other reg (by intro H; subst reg; exact hr (by simp)), G]
      exact U.other reg (by intro H; subst reg; exact hr (by simp))
    · rw [T.rd, Rd, U.rd]
    · rw [T.wr, Wr, U.wr]
  · intro a ha
    rw [T.mem]
    have H : ¬ InRegions [⟨base, size⟩] a 1 := by
      simp only [InRegions, List.mem_singleton, exists_eq_left, Region.Contains]
      change ¬ (ofs base a + 1 ≤ size)
      omega
    exact (F a (by intro reg hreg hcontains; exact H ⟨reg, hreg, hcontains⟩)).trans (congrFun U.mem a)

end VG.Proof.Rsa.X86.KeyCheck
end

end

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Bignum.X86 VG.Impl.Rsa.X86.KeyCheck

theorem installed_ok {full : Bool} {s : State} (a : ABI full s) :
    WP isa (.block (entry full)) s fun t => Inputs (caller full s) t ∧
      Spill.Saved t.mem (off (caller full s).base) s.gpr PublicFn.savedRegisters ∧
      Keeps [.eax, .edi] s t ∧ Outside (caller full s).base 0 (caller full s).size s.mem t.mem := by
  refine WP.mono (entry_ok full (base := (caller full s).base) (ptr := arg s (scratchArg full))
    (a.stackArgument (by omega_using [] : scratchArg full < scratchArg full + 2)).readSrc
    rfl a.scratchBound (by have := a.used; omega_using [this]) (by rw [a.wr]; simp) a.stack)
    fun t ⟨sc, saved, k, o⟩ => ?_
  refine ⟨?_, saved, k, o⟩
  have w := a.width
  refine ⟨⟨sc, a.space, by omega_using [w], by omega_using [w]⟩, w.1, w.2.1, ?_, ?_,
    (fun i hi => (a.inputLength hi).1), (fun i hi => (a.inputLength hi).2),
    (fun i hi => a.inputFit hi), ?_, ?_⟩
  · intro i hi
    exact (CallArgument.mk (a.stackArgument hi) rfl).keep k (by decide) o
  · intro i hi r hr
    rw [show stackAddress t i = stackAddress s i by simp only [stackAddress, k.1 .esp (by decide)]]
    exact a.stackApart hi hr
  · intro i hi
    rw [k.2.1, k.2.2]
    exact ⟨_, List.mem_append_left _ (a.inputMember hi), Region.contains_self _ _⟩
  · intro i hi r hr
    simp only [CallGeometry.writes, List.mem_singleton] at hr
    subst r
    exact a.inApart _ (a.inputMember hi)
end VG.Proof.Rsa.X86.KeyCheck

end

end

/-! ### `Rsa.X86.KcBounds`, which only this module used -/

section

/-! # The signature's byte-length bounds imply the arithmetic factor bounds -/

-- Formerly `VerifiedGarbage/Proof/Rsa/KeyByteBounds.lean`, which only this module imported.
section

/-! # A factor shorter than the modulus leaves room for modular addition -/

section
namespace VG.Proof.Rsa
open VG

theorem short_factor_bounds {bs : List Byte} {k w : Nat} (short : bs.length < k) (fits : k ≤ 4 * w) :
    Spec.Rsa.os2ip bs < 256 ^ (k - 1) ∧
    2 * Spec.Rsa.os2ip bs ≤ 2 ^ (32 * w) ∧ Spec.Rsa.os2ip bs < 2 ^ (32 * w) := by
  have value := lt_of_os2ip bs
  have small : 256 ^ bs.length ≤ 256 ^ (k - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have room : 2 * 256 ^ bs.length ≤ 2 ^ (32 * w) := by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul, ← Nat.pow_succ']
    exact Nat.pow_le_pow_right (by decide) (by omega)
  exact ⟨Nat.lt_of_lt_of_le value small, by omega, by omega⟩
end VG.Proof.Rsa
end

end

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.KeyCheck

theorem ABI.numberBounds {full : Bool} {s : State} (a : ABI full s) (m : Mem) :
    Bounds (geometry (caller full s)) (arg s 1).toNat (numbers (caller full s) m) := by
  have width : (arg s 1).toNat ≤ 4 * (2 * (caller full s).n) := by have := a.width.2.2; omega_using [this]
  have pLen : (inputBytes (caller full s) m (if full then 3 else 2)).length < (arg s 1).toNat := by
    rw [inputBytes, VG.Proof.Bignum.bytesAt_length]
    cases full <;> exact a.pSmall
  have qLen : (inputBytes (caller full s) m (if full then 4 else 3)).length < (arg s 1).toNat := by
    rw [inputBytes, VG.Proof.Bignum.bytesAt_length]
    cases full <;> exact a.qSmall
  have p := VG.Proof.Rsa.short_factor_bounds pLen width
  have q := VG.Proof.Rsa.short_factor_bounds qLen width
  exact ⟨p.1, q.1, p.2.1, q.2.1⟩

theorem numbers_entry {full : Bool} {s : State} {m : Mem} (a : ABI full s)
    (o : Outside (caller full s).base 0 (caller full s).size s.mem m) :
    numbers (caller full s) m = numbers (caller full s) s.mem := by
  have same (i : Nat) (hi : 2 * i < scratchArg full) :
      inputBytes (caller full s) m i = inputBytes (caller full s) s.mem i :=
    VG.Proof.Bignum.scratch_bytes o
      (by have := (a.inputLength hi).2; have := a.width.2.1; omega_arith)
      (a.inApart _ (a.inputMember hi))
  cases full
  · simp only [numbers, show (caller false s).full = false from rfl, Bool.false_eq_true, ite_false]
    rw [same 0 (by decide), same 1 (by decide), same 2 (by decide), same 3 (by decide),
      same 4 (by decide), same 5 (by decide), same 6 (by decide)]
  · simp only [numbers, show (caller true s).full = true from rfl, ite_true]
    rw [same 0 (by decide), same 1 (by decide), same 2 (by decide), same 3 (by decide),
      same 4 (by decide), same 5 (by decide), same 6 (by decide), same 7 (by decide)]
end VG.Proof.Rsa.X86.KeyCheck

end

end

/-! ### `Rsa.X86.KcBodyPublic`, which only this module used -/

section

/-! ### `Rsa.X86.KcPublic`, which this module and modules that import it used -/

section

/-! # Public modulus and exponent validation for both key-check APIs -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.KeyCheck

theorem modulus_ok {g : CallGeometry} {s : State} (h : Inputs g s)
    (lo : 64 ≤ (g.args 1).toNat) (hi : (g.args 1).toNat ≤ 1024) :
    WP isa (.seq (.block (VG.Impl.Rsa.X86.CrtValues.inputArgs 0))
      (.block VG.Impl.Bignum.X86.modulusCheck)) s fun t =>
      t.zf = some (Spec.Rsa.modulusValid (numbers g s.mem).n (g.args 1).toNat) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have zero : 2 * 0 < scratchArg g.full := by cases g.full <;> decide
  refine WP.seq (WP.mono (argumentPair_ok (d := .esi) (by decide) (by decide)
    (h.arguments 0 (by cases g.full <;> decide)).readSrc
    (h.arguments 1 (by cases g.full <;> decide)).readSrc) fun u ⟨p, c, m, r⟩ => ?_)
  refine WP.mono (modulusCheck_ok u lo hi (by rw [p]; exact h.inputFit 0 zero)
    (by rw [p, r.2.1, r.2.2]; exact h.inputRead 0 zero)
    (by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using c)) fun t ⟨z, mt, rt⟩ => ?_
  rw [p, m] at z
  exact ⟨z, mt.trans m, (r.mono (by decide)).trans (rt.mono (by decide))⟩

theorem exponent_ok {g : CallGeometry} {s : State} (h : Inputs g s) :
    WP isa (.seq (.block (VG.Impl.Rsa.X86.CrtValues.inputArgs 2)) VG.Impl.Bignum.X86.exponentCheck) s
      fun t => t.gpr .eax = BitVec.ofNat 32 (Spec.Rsa.exponentValid (numbers g s.mem).e).toNat ∧
        t.mem = s.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have one : 2 * 1 < scratchArg g.full := by cases g.full <;> decide
  refine WP.seq (WP.mono (argumentPair_ok (d := .esi) (by decide) (by decide)
    (h.arguments 2 (by cases g.full <;> decide)).readSrc
    (h.arguments 3 (by cases g.full <;> decide)).readSrc) fun u ⟨p, c, m, r⟩ => ?_)
  refine WP.mono (exponentCheck_ok u (eb := inputBytes g s.mem 1)
    (by rw [inputBytes, bytesAt_length]; exact h.inputPositive 1 one)
    (by rw [inputBytes, bytesAt_length]; exact (g.args 3).isLt)
    (by rw [inputBytes, bytesAt_length]; exact h.inputFit 1 one)
    (by rw [inputBytes, bytesAt_length, r.2.1, r.2.2]; exact h.inputRead 1 one)
    (by intro i hi; rw [m]; simp only [inputBytes, Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]; rfl)
    p (by rw [inputBytes, bytesAt_length]; simpa only [CallGeometry.buffer, BitVec.ofNat_toNat, BitVec.setWidth_eq] using c)) fun t ⟨v, mt, rt⟩ => ?_
  exact ⟨v, mt.trans m, (r.mono (by decide)).trans (rt.mono (by decide))⟩

theorem failure_ok {g : CallGeometry} {s : State} (h : Inputs g s) :
    WP isa failure s fun t => Inputs g t ∧ t.gpr .eax = 0 ∧ t.mem = s.mem ∧ Keeps [.eax] s t := by
  refine wp_movS rfl fun t T _ => WP.block_nil ?_
  exact ⟨h.after T.keeps (by decide) (by decide) (by rw [T.mem]; exact Frame.refl _ _), T.gpr, T.mem, T.keeps⟩

theorem invalid_modulus (full : Bool) (k : Nat) (v : Vals) (h : Spec.Rsa.modulusValid v.n k = false) :
    validity full k v = false := by
  cases full <;> simp only [validity, Bool.false_eq_true, ite_false, ite_true,
    Spec.Rsa.keyValid, Spec.Rsa.crtKeyValid, h, Bool.false_and]

theorem invalid_exponent (full : Bool) (k : Nat) (v : Vals) (h : Spec.Rsa.exponentValid v.e = false) :
    validity full k v = false := by
  cases full <;> simp only [validity, Bool.false_eq_true, ite_false, ite_true,
    Spec.Rsa.keyValid, Spec.Rsa.crtKeyValid, h, Bool.and_false, Bool.false_and]
end VG.Proof.Rsa.X86.KeyCheck

end

end

/-! ### `Rsa.X86.KcSized`, which this module and modules that import it used -/

section

/-! # Complete key validation at the selected public word width -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.KeyCheck
open VG.Proof.Rsa.X86.Keys

theorem sized_ok {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g)
    (b : Bounds (geometry g) (g.args 1).toNat (numbers g s.mem))
    (hm : Spec.Rsa.modulusValid (numbers g s.mem).n (g.args 1).toNat = true)
    (he : Spec.Rsa.exponentValid (numbers g s.mem).e = true) :
    WP isa (VG.Impl.Rsa.X86.KeyCheckRt.sized g.full) s fun t => Inputs g t ∧
      t.gpr .eax = BitVec.ofNat 32 (validity g.full (g.args 1).toNat (numbers g s.mem)).toNat ∧
      Outside g.base 16 (g.size - 16) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have kwEq : VG.Proof.Rsa.X86.KeyRt.kw (g.args 1).toNat = 2 * g.n := by rw [len.width]
  unfold VG.Impl.Rsa.X86.KeyCheckRt.sized
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (loads_ok h len) fun u ⟨hu, bu, fu, ru⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (checks_ok bu b hm he) fun v ⟨A, live, hv⟩ => ?_
  have full := VG.Proof.Rsa.X86.KeyRt.keep_outside bu.ws.ws hv.keep (fun j hj => List.mem_range.mp hj) (by decide)
  have keep' : Keep g.base (2 * g.n) (List.range nArr) bodySlots u.mem v.mem := by rw [← kwEq]; exact hv.keep
  have body := hu.keepBody keep' (fun j hj => List.mem_range.mp hj) (by decide)
  have iv := hu.after hv.rest (by decide) (by decide) (hu.scratchFrame full)
  refine wp_movS (readSrc_sc iv.ws.workspace (by have := iv.ws.hdr_le; unfold sMask hdr at *; omega_using [this]))
    fun t T _ => WP.block_nil ?_
  refine ⟨iv.after T.keeps (by decide) (by decide) (by rw [T.mem]; exact Frame.refl _ _), ?_, ?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    rw [T.gpr]
    change slot v.mem (geometry g).B sMask = _
    rw [hv.mask, show (geometry g).full = g.full from rfl]; cases validity g.full (g.args 1).toNat (numbers g s.mem) <;> rfl
  · rw [T.mem]; exact fu.trans body
  · exact ru.trans ((hv.rest.mono (by decide)).trans (T.keeps.mono (by decide)))
/-- The checks run, whatever the numbers. -/
theorem bodies_ok {g : Geo} {v : Vals} {s : State} (h : BodyIn g v s) :
    WP isa (if g.full then VG.Impl.Rsa.X86.KeyCheckRt.keyBody g.full else VG.Impl.Rsa.X86.KeyCheckRt.crtBody g.full) s
      fun t => ∃ A live c, Stg g s A live c t := by
  obtain ⟨B, Z, len, full⟩ := g
  cases full
  · exact WP.mono (crtBody_ok h) fun _ ⟨_, _, _, _, A, live, ht⟩ => ⟨A, live, _, ht⟩
  · exact WP.mono (keyBody_ok h) fun _ ⟨_, _, _, _, _, _, _, A, live, ht⟩ => ⟨A, live, _, ht⟩

/-- `sized` runs from `Inputs`, whatever the numbers. -/
theorem sized_wp {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g) :
    WP isa (VG.Impl.Rsa.X86.KeyCheckRt.sized g.full) s fun t => Inputs g t := by
  unfold VG.Impl.Rsa.X86.KeyCheckRt.sized
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (loads_ok h len) fun u ⟨hu, bu, _, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (bodies_ok bu) fun v ⟨A, live, c, hv⟩ => ?_
  have full := VG.Proof.Rsa.X86.KeyRt.keep_outside bu.ws.ws hv.keep (fun j hj => List.mem_range.mp hj) (by decide)
  have iv := hu.after hv.rest (by decide) (by decide) (hu.scratchFrame full)
  refine wp_movS (readSrc_sc iv.ws.workspace (by have := iv.ws.hdr_le; unfold sMask hdr at *; omega_using [this]))
    fun t T _ => WP.block_nil ?_
  exact iv.after T.keeps (by decide) (by decide) (by rw [T.mem]; exact Frame.refl _ _)

end VG.Proof.Rsa.X86.KeyCheck

end

end

/-! # Public rejection branches and full key validation have the same result contract -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.KeyCheck

def Post (g : CallGeometry) (m : Mem) (t : State) : Prop := Inputs g t ∧
  t.gpr .eax = BitVec.ofNat 32 (validity g.full (g.args 1).toNat (numbers g m)).toNat ∧
  Outside g.base 16 (g.size - 16) m t.mem

theorem checkExponent_ok {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g)
    (b : Bounds (geometry g) (g.args 1).toNat (numbers g s.mem))
    (hm : Spec.Rsa.modulusValid (numbers g s.mem).n (g.args 1).toNat = true) :
    WP isa (VG.Impl.Rsa.X86.KeyCheckRt.checkExponent g.full) s fun t => Post g s.mem t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold VG.Impl.Rsa.X86.KeyCheckRt.checkExponent
  refine WP.seq (WP.mono (exponent_ok h) fun u ⟨value, memU, restU⟩ => ?_)
  refine WP.seq (WP.mono (exponentFlag_ok _ value) fun v ⟨flag, memV, restV⟩ => ?_)
  have mem : v.mem = s.mem := memV.trans memU
  have rest := restU.trans (restV.mono (by decide))
  have hv := h.after rest (by decide) (by decide) (by rw [mem]; exact Frame.refl _ _)
  refine WP.ite (!Spec.Rsa.exponentValid (numbers g s.mem).e) flag ?_ ?_
  · intro bad
    have invalid : Spec.Rsa.exponentValid (numbers g s.mem).e = false := by simpa using bad
    refine WP.mono (failure_ok hv) fun t ⟨ht, zero, mt, rt⟩ => ?_
    refine ⟨⟨ht, ?_, ?_⟩, rest.trans (rt.mono (by decide))⟩
    · rw [invalid_exponent _ _ _ invalid]; exact zero
    · rw [mt, mem]; exact Outside.refl _ _ _ _
  · intro good
    have accepted : Spec.Rsa.exponentValid (numbers g s.mem).e = true := by simpa using good
    refine WP.mono (sized_ok hv len (mem ▸ b) (mem ▸ hm) (mem ▸ accepted))
      fun t ⟨ht, value, frame, rt⟩ => ?_
    exact ⟨⟨ht, mem ▸ value, mem ▸ frame⟩, rest.trans rt⟩

theorem body_ok {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g)
    (b : Bounds (geometry g) (g.args 1).toNat (numbers g s.mem)) :
    WP isa (VG.Impl.Rsa.X86.KeyCheckRt.body g.full) s fun t => Post g s.mem t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold VG.Impl.Rsa.X86.KeyCheckRt.body
  refine WP.seq (WP.mono (modulus_ok h len.lower len.upper) fun u ⟨flag, mem, rest⟩ => ?_)
  have hu := h.after rest (by decide) (by decide) (by rw [mem]; exact Frame.refl _ _)
  refine WP.ite (Spec.Rsa.modulusValid (numbers g s.mem).n (g.args 1).toNat) flag ?_ ?_
  · intro accepted
    refine WP.mono (checkExponent_ok hu len (mem ▸ b) (mem ▸ accepted)) fun t ⟨post, rt⟩ => ?_
    exact ⟨mem ▸ post, rest.trans rt⟩
  · intro rejected
    refine WP.mono (failure_ok hu) fun t ⟨ht, zero, mt, rt⟩ => ?_
    refine ⟨⟨ht, ?_, ?_⟩, rest.trans (rt.mono (by decide))⟩
    · rw [invalid_modulus _ _ _ rejected]; exact zero
    · rw [mt, mem]; exact Outside.refl _ _ _ _
end VG.Proof.Rsa.X86.KeyCheck

end

end

/-! ### `Rsa.X86.KcPair`, which only this module used -/

section

/-! # Relate CRT calls with equal public pointers, lengths, and stack position -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum.X86 VG.Proof.Dsa.X86

structure Pair (g : CallGeometry) (s t : State) : Prop where
  left : Inputs g s
  right : Inputs g t
  sp : s.gpr .esp = t.gpr .esp

theorem Pair.agree {g : CallGeometry} {s t : State} (h : Pair g s t) :
    VG.X86.Taint.Agree argumentTaint s t := by
  apply agree_regs (rs := [.edi, .esp])
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact BitVec.eq_of_toNat_eq (h.left.ws.workspace.edi_toNat.trans h.right.ws.workspace.edi_toNat.symm)
  · exact h.sp

theorem Pair.workspace {g : CallGeometry} {s t : State} (h : Pair g s t) :
    VG.X86.Taint.Agree (VG.Proof.Mont.X86.Dynamic.workspaceTaint false) s t := by
  apply agree_regs
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact h.agree.rf.1 _ (by decide)

theorem Pair.after {g : CallGeometry} {s t u v : State} {regs : List Reg} (h : Pair g s t)
    (hu : Inputs g u) (hv : Inputs g v) (ku : Keeps regs s u) (kv : Keeps regs t v)
    (sp : .esp ∉ regs) : Pair g u v :=
  ⟨hu, hv, (ku.1 _ sp).trans (h.sp.trans (kv.1 _ sp).symm)⟩

theorem Pair.keepMem {g : CallGeometry} {s t u v : State} {regs : List Reg} (h : Pair g s t)
    (ks : Keeps regs s u) (kt : Keeps regs t v) (di : .edi ∉ regs) (sp : .esp ∉ regs)
    (ms : u.mem = s.mem) (mt : v.mem = t.mem) : Pair g u v :=
  h.after (h.left.after ks di sp (by rw [ms]; exact Frame.refl _ _))
    (h.right.after kt di sp (by rw [mt]; exact Frame.refl _ _)) ks kt sp

end VG.Proof.Rsa.X86.KeyCheck

end

end

/-! ### `Rsa.X86.KcOperationTiming`, which only this module used -/

section

/-! ### `Rsa.X86.KcBodyTiming`, which only this module used -/

section

/-! ### `Rsa.X86.KcBranchTiming`, which only this module used -/

section

/-! ### `Rsa.X86.KcTime`, which only this module used -/

section

/-! # The traces of the checks of an RSA key on i686

The runs are related piece by piece: what the taint analysis checks with
the arguments, `edi` and `esp` public (`τV`), from states that keep them
(`Run`), and the loops counted in the header by `WordRt`'s relations. Up to
the guard, each run's values are known (`Stg`); the guard, of the arguments
and `n`'s top word, is the same in both runs when their `n` is; after it,
each piece keeps only the frame (`Fm`).
-/

/-! ## Once the modulus and exponent are accepted

The width is read from the arguments on the stack, so the taint analysis
takes them public with `edi` and `esp` (`τV`, `sizedCheck`), from states whose
permissions are narrowed to the working space, apart from the arguments
(`ArgsOk`); runs of `sized` from the states themselves leak the same traces
(`sizedNarrow_relCT`).
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.KeyCheck VG.Impl.Rsa.X86.KeyCheckRt
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa.X86.WordRt (MLen wq mw Bal Top top_iff val32_low sub0_beq exec_seqs_append RelCT.seqs_append RelCT.seqs_cons RelCT.seqs_all relLift)

/-! ## Runs -/

/-- The return address and the arguments lie apart from every writable region. -/
def ArgsOk (full : Bool) (s : State) : Prop :=
  (s.gpr .esp).toNat + argSpan full ≤ 2 ^ 32 ∧
    ∀ r ∈ s.wr, Region.Disjoint ⟨(s.gpr .esp).setWidth 64, argSpan full⟩ r

theorem τV_wf {full : Bool} {s : State} (A : ArgsOk full s) : VG.X86.Taint.Wf (τV full) s :=
  VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => A, fun _ h => (List.not_mem_nil h).elim⟩

theorem agreeV {g : CallGeometry} {s₁ s₂ : State} (h₁ : Inputs g s₁) (h₂ : Inputs g s₂)
    (A₁ : ArgsOk g.full s₁) (A₂ : ArgsOk g.full s₂) (sp : s₁.gpr .esp = s₂.gpr .esp) :
    VG.X86.Taint.Agree (τV g.full) s₁ s₂ := by
  have f₁ := A₁.1
  have f₂ := A₂.1
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, τV_wf A₁, τV_wf A₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [τV, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact BitVec.eq_of_toNat_eq (h₁.ws.workspace.edi_toNat.trans h₂.ws.workspace.edi_toNat.symm)
    · exact sp
  · simp only [τV, argSpan] at hk
    rw [show VG.X86.Taint.depth (τV g.full).stk = 0 from rfl, Nat.zero_add,
      VG.X86.Taint.argByte_eq f₁ h4 hk, VG.X86.Taint.argByte_eq f₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (show arg s₁ _ = arg s₂ _ from
      (h₁.arguments _ (by omega_using [hk])).value.trans (h₂.arguments _ (by omega_using [hk])).value.symm)

/-- What a narrowed run of `sized` keeps: the inputs, the arguments apart and `esp`. -/
def Run (g : CallGeometry) (sp : BitVec 32) (s : State) : Prop :=
  Inputs g s ∧ ArgsOk g.full s ∧ s.gpr .esp = sp

/-- A run through a frame of the working space. -/
theorem Run.frame {g : CallGeometry} {sp : BitVec 32} {u t : State} (h : Run g sp u) {rs : List Reg}
    (K : Keeps rs u t) (di : .edi ∉ rs) (spn : .esp ∉ rs) (O : Outside g.base 0 g.size u.mem t.mem) :
    Run g sp t :=
  ⟨h.1.after K di spn (h.1.scratchFrame O), ⟨by rw [K.1 _ spn]; exact h.2.1.1, by rw [K.2.2, K.1 _ spn]; exact h.2.1.2⟩,
    (K.1 _ spn).trans h.2.2⟩

theorem Run.agree {g : CallGeometry} {sp : BitVec 32} {t₁ t₂ : State} (h₁ : Run g sp t₁) (h₂ : Run g sp t₂) :
    VG.X86.Taint.Agree (τV g.full) t₁ t₂ :=
  agreeV h₁.1 h₂.1 h₁.2.1 h₂.2.1 (h₁.2.2.trans h₂.2.2.symm)

/-! ## The frame -/

/-- The frame of the checks, from the state `u` they start from: `Stg` without the values. -/
structure Fm (G : Geo) (u t : State) : Prop where
  ws : VG.Proof.Rsa.X86.KeyRt.RtWs G.L t G.B G.Z G.len nArr
  keep : Keep G.B G.w (List.range nArr) bodySlots u.mem t.mem
  rest : Keeps bodyRegs u t
  mask : slot t.mem G.B sMask ≤ 1

theorem Stg.fm {G : Geo} {u t : State} {A : Nat → Nat} {live : List Nat} {c : Bool} (h : Stg G u A live c t) :
    Fm G u t := ⟨h.ws, h.keep, h.rest, bit_le h.mask⟩

theorem Fm.next {G : Geo} {u s t : State} (h : Fm G u s) {js ds : List Nat} {rs : List Reg}
    (hw : VG.Proof.Rsa.X86.KeyRt.RtWs G.L t G.B G.Z G.len nArr)
    (k : Keep G.B G.w js ds s.mem t.mem) (hjs : ∀ j ∈ js, j < nArr) (hds : ∀ d ∈ ds, d ∈ bodySlots)
    (r : Keeps rs s t) (hrs : ∀ x ∈ rs, x ∈ bodyRegs) (mk : slot t.mem G.B sMask ≤ 1) : Fm G u t :=
  ⟨hw, h.keep.trans (k.mono (fun j hj => List.mem_range.2 (hjs j hj)) hds), h.rest.trans (r.mono hrs), mk⟩

theorem Fm.mask_keep {G : Geo} {u s : State} (h : Fm G u s) {js ds : List Nat} {m' : Mem}
    (k : Keep G.B G.w js ds s.mem m') (hd : ∀ d ∈ ds, sMask + 4 ≤ d ∨ d + 4 ≤ sMask) :
    slot m' G.B sMask ≤ 1 := by
  rw [k.slot (by decide) hd]; exact h.mask

/-- A run's frame from its start. -/
theorem Fm.run {g : CallGeometry} {sp : BitVec 32} {u t : State} (h : Fm (geometry g) u t) (r : Run g sp u) :
    Run g sp t :=
  r.frame h.rest (by decide) (by decide)
    (VG.Proof.Rsa.X86.KeyRt.keep_outside h.ws.ws h.keep (fun j hj => List.mem_range.mp hj) (by decide))

/-! ## The frame through the pieces of the word steps -/

theorem fm_ltA {G : Geo} {u t : State} (h : Fm G u t) {a b : Nat} (ha : a < nArr) (hb : b < nArr) :
    WP isa (seqs (ltA G.full a b)) t (Fm G u) := by
  rw [ltA, wp_seqs_cons (by simp)]
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.sub3_ok h.ws (o := aW) (a := a) (b := b) (by decide) ha hb)
    fun t1 ⟨h1, k1, _, b1, r1⟩ => ?_
  have f1 := h.next h1 k1 (by decide) (by simp) r1 subRegs_body (h.mask_keep k1 (by simp))
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.storeSlot_ok h1 (d := sF) (by decide) .ebx) fun t2 ⟨h2, k2, e2, r2⟩ => ?_
  have f2 := f1.next h2 k2 (by simp) (by decide) r2 (by simp) (f1.mask_keep k2 (by decide))
  show WP isa (.block acc) t2 _
  unfold acc
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.andS_ok h2 (d := sMask) (a := sMask) (b := sF) (by decide) (by decide)
    (by decide) f2.mask (by rw [e2]; exact b1)) fun t3 ⟨h3, k3, e3, r3⟩ =>
      f2.next h3 k3 (by simp) (by decide) r3 (by decide) (by rw [e3]; split <;> decide)

theorem fm_eqA {G : Geo} {u t : State} (h : Fm G u t) {a b : Nat} (ha : a < nArr) (hb : b < nArr)
    (haW : aW ≠ a) (hbW : aW ≠ b) :
    WP isa (seqs (eqA G.full a b)) t (Fm G u) := by
  rw [eqA, wp_seqs_cons (by simp)]
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.eqS_ok h.ws (d := sF) (a := a) (b := b) (t := aW) (by decide) ha hb haW hbW
    (by decide)) fun t1 ⟨h1, k1, e1, r1⟩ => ?_
  have f1 := h.next h1 k1 (by decide) (by decide) r1 opRegs_body (h.mask_keep k1 (by decide))
  show WP isa (.block acc) t1 _
  unfold acc
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.andS_ok h1 (d := sMask) (a := sMask) (b := sF) (by decide) (by decide)
    (by decide) f1.mask (by rw [e1]; split <;> decide)) fun t3 ⟨h3, k3, e3, r3⟩ =>
      f1.next h3 k3 (by simp) (by decide) r3 (by decide) (by rw [e3]; split <;> decide)

theorem fm_mulShort {G : Geo} {u t : State} (h : Fm G u t) {o a b : Nat} (hw2 : 2 ≤ G.w) (ho : o + 1 < nArr)
    (ha : a < nArr) (hb : b < nArr) (hao : a ≠ o) (hao1 : a ≠ o + 1) (hbo : b ≠ o) (hbo1 : b ≠ o + 1) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.mulShort G.L o a b) t (Fm G u) :=
  WP.mono (VG.Proof.Rsa.X86.WordRt.mulShort_ok h.ws hw2 ho ha hb hao hao1 hbo hbo1) fun _ ⟨h1, k1, _, r1⟩ =>
    h.next h1 k1 (by simp; omega_using [ho]) (by decide) r1 wordRegs_body (h.mask_keep k1 (by decide))

theorem fm_wordMod {G : Geo} {u t : State} (h : Fm G u t) {x r m a : Nat} {top : Option Nat}
    (hm : MLen t G.B G.Z (pLenArg G.full) a) (h4 : 4 ≤ wq a) (hw : wq a ≤ G.w)
    (htop : ∀ k, top = some k → wq a + k ≤ G.w)
    (hx : x < nArr) (hr : r < nArr) (hmN : m < nArr)
    (hrT : r ≠ aT) (hmT : m ≠ aT) (hrm : r ≠ m) (hxr : r ≠ x) (hxt : aT ≠ x) (hxm : m ≠ x) :
    WP isa (wordMod G.full x r m top) t (Fm G u) :=
  WP.mono (VG.Proof.Rsa.X86.WordRt.wordMod_ok h.ws hm hx hr hmN (by decide) hrT hmT hrm hxr hxt hxm
    h4 hw htop) fun _ ⟨h1, k1, _, _, _, r1⟩ =>
    h.next h1 k1 (by
      intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl
      · exact hmN
      · exact hr
      · decide) (by decide) r1 wordRegs_body (h.mask_keep k1 (by decide))

/-! ## The word steps' relation -/

/-- A run in the word steps: from its start `u`, with `p`'s length `a` that the guard admits. -/
def WIn (g : CallGeometry) (sp : BitVec 32) (a : Nat) (u t : State) : Prop :=
  Run g sp u ∧ Fm (geometry g) u t ∧ MLen u g.base g.size (pLenArg g.full) a ∧ 4 ≤ wq a ∧
    wq a + 2 ≤ (geometry g).w

/-- Both runs in the word steps. -/
def WR (g : CallGeometry) (sp : BitVec 32) (a : Nat) (t₁ t₂ : State) : Prop :=
  ∃ u₁ u₂, True ∧ WIn g sp a u₁ t₁ ∧ WIn g sp a u₂ t₂

theorem WIn.run {g : CallGeometry} {sp : BitVec 32} {a : Nat} {u t : State} (h : WIn g sp a u t) : Run g sp t :=
  h.2.1.run h.1

theorem WIn.mlen {g : CallGeometry} {sp : BitVec 32} {a : Nat} {u t : State} (h : WIn g sp a u t) :
    MLen t g.base g.size (pLenArg g.full) a :=
  h.2.2.1.keep h.2.1.rest (by decide)
    (VG.Proof.Rsa.X86.KeyRt.keep_outside h.2.1.ws.ws h.2.1.keep (fun j hj => List.mem_range.mp hj) (by decide))

theorem τV_regs (full : Bool) : ∀ r ∈ [Reg.edi, .esp], (τV full).regs.mem r = true := by
  intro r hr
  change r ∈ RegSet.ofList [Reg.edi, .esp]
  simpa only [RegSet.mem_ofList] using hr

/-- A piece the taint analysis checks. -/
theorem wTaint {g : CallGeometry} {sp : BitVec 32} {a : Nat} {c : Prog isa}
    (hc : ∃ hint, (VG.Taint.check sseTaint (τV g.full) c hint).isSome = true)
    (hf : ∀ u t, Fm (geometry g) u t → WP isa c t (Fm (geometry g) u)) :
    RelCT isa (WR g sp a) c (WR g sp a) := by
  obtain ⟨_, hc⟩ := hc
  exact relLift (Rel := fun _ _ => True) (P := WIn g sp a)
    (VG.RelCT.taint (A := sseTaint) (τV g.full) (fun t₁ t₂ ⟨_, _, _, h₁, h₂⟩ => h₁.run.agree h₂.run) hc)
    fun u t h => WP.mono (hf u t h.2.1) fun t' f => ⟨h.1, f, h.2.2⟩

theorem wMulShort {g : CallGeometry} {sp : BitVec 32} {a : Nat} {o x b : Nat} (ck : RowsCk g.full o x b (some 2))
    (ho : o + 1 < nArr) (hx : x < nArr) (hb : b < nArr) (hxo : x ≠ o) (hxo1 : x ≠ o + 1) (hbo : b ≠ o)
    (hbo1 : b ≠ o + 1) :
    RelCT isa (WR g sp a) (VG.Impl.Rsa.X86.WordModRt.mulShort (lay g.full) o x b) (WR g sp a) := by
  refine relLift (Rel := fun _ _ => True) (P := WIn g sp a) ?_ fun u t h =>
    WP.mono (fm_mulShort h.2.1 (by have := h.2.2.2.2; omega_using [this]) ho hx hb hxo hxo1 hbo hbo1) fun t' f => ⟨h.1, f, h.2.2⟩
  have w2 : ∀ {u t : State}, WIn g sp a u t → 2 ≤ VG.Proof.Rsa.X86.KeyRt.kw (g.args 1).toNat := fun h => by
    have := h.2.2.2.2; have := h.2.2.2.1; simp only [geometry, Geo.w] at *; omega_arith
  refine fun t₁ t₂ t₁' t₂' s₁ s₂ hp e₁ e₂ => ?_
  obtain ⟨_, _, _, h₁, h₂⟩ := hp
  exact VG.Proof.Rsa.X86.WordRt.mulRows_relCT (τ := τV g.full) (Fr := Run g sp) (B := g.base) (Z := g.size)
    (fun _ _ a b => a.agree b) (fun f K d e O => f.frame K d e O) (τV_regs g.full)
    (rows := some 2) (by show 1 ≤ 2; decide) (by show 2 ≤ _; exact w2 h₁) (fun k hk => by cases hk; decide)
    ho hx hb hxo hxo1 hbo hbo1 ck.c₀ ck.c₁ ck.c₂
    _ _ _ _ _ _ ⟨⟨h₁.2.1.ws, h₁.run⟩, ⟨h₂.2.1.ws, h₂.run⟩⟩ e₁ e₂

theorem fm_mulHalf {G : Geo} {u t : State} (h : Fm G u t) {o a b : Nat} (ho : o + 1 < nArr)
    (ha : a < nArr) (hb : b < nArr) (hao : a ≠ o) (hao1 : a ≠ o + 1) (hbo : b ≠ o) (hbo1 : b ≠ o + 1) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.mulHalf G.L o a b) t (Fm G u) :=
  WP.mono (VG.Proof.Rsa.X86.WordRt.mulHalf_ok h.ws ho ha hb hao hao1 hbo hbo1) fun _ ⟨h1, k1, _, r1⟩ =>
    h.next h1 k1 (by simp; omega_using [ho]) (by decide) r1 wordRegs_body (h.mask_keep k1 (by decide))

theorem wMulHalf {g : CallGeometry} {sp : BitVec 32} {a : Nat} {o x b : Nat} (ck : HalfCk g.full o x b)
    (ho : o + 1 < nArr) (hx : x < nArr) (hb : b < nArr) (hxo : x ≠ o) (hxo1 : x ≠ o + 1) (hbo : b ≠ o)
    (hbo1 : b ≠ o + 1) :
    RelCT isa (WR g sp a) (VG.Impl.Rsa.X86.WordModRt.mulHalf (lay g.full) o x b) (WR g sp a) := by
  refine relLift (Rel := fun _ _ => True) (P := WIn g sp a) ?_ fun u t h =>
    WP.mono (fm_mulHalf h.2.1 ho hx hb hxo hxo1 hbo hbo1) fun t' f => ⟨h.1, f, h.2.2⟩
  refine fun t₁ t₂ t₁' t₂' s₁ s₂ hp e₁ e₂ => ?_
  obtain ⟨_, _, _, h₁, h₂⟩ := hp
  exact VG.Proof.Rsa.X86.WordRt.mulHalf_relCT (τ := τV g.full) (Fr := Run g sp) (B := g.base) (Z := g.size)
    (fun _ _ a b => a.agree b) (fun f K d e O => f.frame K d e O) (τV_regs g.full)
    (by show 1 ≤ VG.Proof.Rsa.X86.KeyRt.kw _; exact h₁.2.1.ws.kw_pos)
    ho hx hb hxo hxo1 hbo hbo1 ck.c₀ ck.c₁ ck.c₂
    _ _ _ _ _ _ ⟨⟨h₁.2.1.ws, h₁.run⟩, ⟨h₂.2.1.ws, h₂.run⟩⟩ e₁ e₂

theorem wWordMod {g : CallGeometry} {sp : BitVec 32} {a : Nat} {x r m : Nat} {top : Option Nat}
    (ck : ModCk g.full x r m top) (htop : ∀ k ∈ top, k ≤ 2)
    (hx : x < nArr) (hr : r < nArr) (hmN : m < nArr)
    (hrT : r ≠ aT) (hmT : m ≠ aT) (hrm : r ≠ m) (hxr : r ≠ x) (hxt : aT ≠ x) (hxm : m ≠ x) :
    RelCT isa (WR g sp a) (wordMod g.full x r m top) (WR g sp a) := by
  have ht : ∀ {u t : State}, WIn g sp a u t → ∀ k, top = some k → wq a + k ≤ (geometry g).w :=
    fun h k e => by have := htop k (by rw [e]; rfl); have := h.2.2.2.2; omega_arith
  refine relLift (Rel := fun _ _ => True) (P := WIn g sp a) ?_ fun u t h =>
    WP.mono (fm_wordMod h.2.1 h.mlen h.2.2.2.1 (by have := h.2.2.2.2; simp only [Geo.w] at this ⊢; omega_using [this]) (ht h)
      hx hr hmN hrT hmT hrm hxr hxt hxm) fun t' f => ⟨h.1, f, h.2.2⟩
  refine fun t₁ t₂ t₁' t₂' s₁ s₂ hp e₁ e₂ => ?_
  obtain ⟨_, _, _, h₁, h₂⟩ := hp
  exact VG.Proof.Rsa.X86.WordRt.wordMod_relCT (τ := τV g.full) (Fr := Run g sp) (B := g.base) (Z := g.size)
    (fun _ _ a b => a.agree b) (fun f K d e O => f.frame K d e O) (τV_regs g.full)
    hx hr hmN (by decide) hrT hmT hrm hxr hxt hxm h₁.2.2.2.1
    (by have := h₁.2.2.2.2; simp only [geometry, Geo.w] at this ⊢; omega_using [this]) (ht h₁)
    ck.c₀ ck.c₁ ck.c₂ _ _ _ _ _ _ ⟨⟨h₁.2.1.ws, h₁.run, h₁.mlen⟩, ⟨h₂.2.1.ws, h₂.run, h₂.mlen⟩⟩ e₁ e₂

/-! ## The word branch -/

theorem wEWord {g : CallGeometry} {sp : BitVec 32} {a x m : Nat}
    (hl : ∃ hint, (VG.Taint.check sseTaint (τV g.full) (seqs (ltA g.full x m)) hint).isSome = true)
    (he : ∃ hint, (VG.Taint.check sseTaint (τV g.full) (seqs (eqA g.full aA aOne)) hint).isSome = true)
    (rk : RowsCk g.full aY x aE (some 2)) (mk : ModCk g.full aY aA m (some 2))
    (hx : x < nArr) (hm : m < nArr) (hxY : x ≠ aY) (hxX : x ≠ aY + 1) (hmT : m ≠ aT) (hmA : m ≠ aA)
    (hmY : m ≠ aY) :
    RelCT isa (WR g sp a) (seqs (eWord g.full x m)) (WR g sp a) := by
  unfold eWord
  refine RelCT.seqs_append (by simp [ltA]) (by simp [eqA]) (VG.RelCT.seq
    (RelCT.seqs_append (by simp [ltA]) (by simp) (VG.RelCT.seq (wTaint hl fun _ _ h => fm_ltA h hx hm)
      (RelCT.seqs_cons (by simp) (wMulShort rk (by decide) hx (by decide) hxY hxX (by decide) (by decide))
        (wWordMod mk (by simp) (by decide) (by decide) hm (by decide) hmT (fun e => hmA e.symm) (by decide) (by decide)
          hmY))))
    (wTaint he fun _ _ h => fm_eqA h (by decide) (by decide) (by decide) (by decide)))

theorem wQInv {g : CallGeometry} {sp : BitVec 32} {a : Nat} (ck : WCk g.full) :
    RelCT isa (WR g sp a) (seqs (qInvWord g.full)) (WR g sp a) := by
  unfold qInvWord
  refine RelCT.seqs_append (by simp [ltA]) (by simp [eqA]) (VG.RelCT.seq
    (RelCT.seqs_append (by simp [ltA]) (by simp) (VG.RelCT.seq (wTaint ck.ltQI fun _ _ h => fm_ltA h (by decide) (by decide))
      (RelCT.seqs_cons (by simp) (wMulHalf ck.rQI (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide))
        (wWordMod ck.mP (by simp) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide)))))
    (wTaint ck.eqOne fun _ _ h => fm_eqA h (by decide) (by decide) (by decide) (by decide)))

theorem wProducts {g : CallGeometry} {sp : BitVec 32} {a : Nat} (ck : WCk g.full) :
    RelCT isa (WR g sp a) (wordProducts g.full) (WR g sp a) := by
  unfold wordProducts
  refine RelCT.seqs_append (by simp [eWord, ltA]) (by simp [qInvWord, ltA]) (VG.RelCT.seq
    (RelCT.seqs_append (by simp [eWord, ltA]) (by simp [eWord, ltA]) (VG.RelCT.seq
      (wEWord ck.ltDP ck.eqOne ck.rDP ck.mM1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide))
      (wEWord ck.ltDQ ck.eqOne ck.rDQ ck.mM2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide))))
    (wQInv ck))

theorem wDWords {g : CallGeometry} {sp : BitVec 32} {a : Nat} (ck : WCk g.full) :
    RelCT isa (WR g sp a) (dWords g.full) (WR g sp a) := by
  have m₁ : RelCT isa (WR g sp a) (wordMod g.full aD aVR aM1) (WR g sp a) :=
    wWordMod ck.dM1 (by simp) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  have m₂ : RelCT isa (WR g sp a) (wordMod g.full aD aVR aM2) (WR g sp a) :=
    wWordMod ck.dM2 (by simp) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  have e₁ := wTaint (sp := sp) (a := a) ck.eqDP fun _ _ h => fm_eqA h (by decide) (by decide) (by decide) (by decide)
  have e₂ := wTaint (sp := sp) (a := a) ck.eqDQ fun _ _ h => fm_eqA h (by decide) (by decide) (by decide) (by decide)
  have l := wTaint (sp := sp) (a := a) ck.ltD fun _ _ h => fm_ltA h (by decide) (by decide)
  unfold dWords
  refine RelCT.seqs_append (by simp [ltA]) (by simp [eqA]) (VG.RelCT.seq ?_ e₂)
  refine RelCT.seqs_append (by simp [ltA]) (by simp) (VG.RelCT.seq ?_ m₂)
  refine RelCT.seqs_append (by simp [ltA]) (by simp [eqA]) (VG.RelCT.seq ?_ e₁)
  exact RelCT.seqs_append (by simp [ltA]) (by simp) (VG.RelCT.seq l m₁)

theorem wBranch {g : CallGeometry} {sp : BitVec 32} {a : Nat} (ck : WCk g.full) :
    RelCT isa (WR g sp a) (wordBranch g.full) (WR g sp a) := by
  unfold wordBranch
  split
  · exact VG.RelCT.seq (wProducts ck) (wDWords ck)
  · exact wProducts ck

/-! ## The checks -/

/-- The guard, of the arguments and `n`. -/
def BalN (g : CallGeometry) (n : Nat) : Prop :=
  (g.args 1).toNat % 8 = 0 ∧ 2 * (g.args (pLenArg g.full)).toNat = (g.args 1).toNat ∧
    2 * (g.args (qLenArg g.full)).toNat = (g.args 1).toNat ∧ 128 ≤ (g.args 1).toNat ∧
    2 ^ (32 * (geometry g).w - 1) ≤ n

theorem pLen_lt (full : Bool) : pLenArg full < scratchArg full + 2 := by cases full <;> decide
theorem qLen_lt (full : Bool) : qLenArg full < scratchArg full + 2 := by cases full <;> decide
theorem nLen_lt (full : Bool) : 1 < scratchArg full + 2 := by cases full <;> decide

theorem arg_val {s : State} {B : Addr} {Z i a : Nat} {v : BitVec 32}
    (h : VG.Proof.Bignum.X86.CallArgument s B Z i (BitVec.ofNat 32 a)) (h' : VG.Proof.Bignum.X86.CallArgument s B Z i v)
    (ha : a ≤ 1024) : a = v.toNat := by
  have e := h.value.symm.trans h'.value
  rw [← e, BitVec.toNat_ofNat]; omega_using [ha]

theorem Inputs.arg {g : CallGeometry} {s : State} (h : Inputs g s) {i a : Nat}
    (c : VG.Proof.Bignum.X86.CallArgument s g.base g.size i (BitVec.ofNat 32 a)) (ha : a ≤ 1024)
    (hi : i < scratchArg g.full + 2) : a = (g.args i).toNat :=
  arg_val c (h.arguments i hi) ha

/-- Each run's start: what the checks start from, and its numbers. -/
abbrev RunBase (g : CallGeometry) (sp : BitVec 32) (x : Vals × State) : Prop :=
  Run g sp x.2 ∧ BodyIn (geometry g) x.1 x.2

/-- Both runs, each from its own start, with the same `n`. -/
def Both₂ (P : Vals × State → State → Prop) (t₁ t₂ : State) : Prop :=
  ∃ x₁ x₂, (fun x₁ x₂ : Vals × State => x₁.1.n = x₂.1.n) x₁ x₂ ∧ P x₁ t₁ ∧ P x₂ t₂

theorem taintLift {g : CallGeometry} {sp : BitVec 32} {c : Prog isa} {P Q : Vals × State → State → Prop}
    (hc : ∃ hint, (VG.Taint.check sseTaint (τV g.full) c hint).isSome = true)
    (hr : ∀ x t, P x t → Run g sp t) (hw : ∀ x t, P x t → WP isa c t (Q x)) :
    RelCT isa (Both₂ P) c (Both₂ Q) := by
  obtain ⟨_, hc⟩ := hc
  exact relLift (Rel := fun x₁ x₂ : Vals × State => x₁.1.n = x₂.1.n)
    (VG.RelCT.taint (A := sseTaint) (τV g.full) (fun t₁ t₂ ⟨x₁, x₂, _, h₁, h₂⟩ => (hr x₁ t₁ h₁).agree (hr x₂ t₂ h₂)) hc) hw

theorem stg_run {g : CallGeometry} {sp : BitVec 32} {u t : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (r : Run g sp u) (h : Stg (geometry g) u A live c t) : Run g sp t := h.fm.run r

/-- What `start` leaves. -/
def AtStart (g : CallGeometry) (sp : BitVec 32) (x : Vals × State) (t : State) : Prop :=
  RunBase g sp x ∧ Stg (geometry g) x.2 (aStart x.1) live0
    (decide (x.1.p % 2 = 1) && decide (x.1.p * x.1.q = x.1.n)) t

/-- Before the product: the guard in `sG`. -/
def AtBal (g : CallGeometry) (sp : BitVec 32) (x : Vals × State) (t : State) : Prop :=
  RunBase g sp x ∧ Stg (geometry g) x.2 (aStart x.1) live0 (decide (x.1.p % 2 = 1)) t ∧
    (slot t.mem g.base sG = 0 ↔ BalN g x.1.n)

/-- After the product. -/
def AtProd (g : CallGeometry) (sp : BitVec 32) (x : Vals × State) (t : State) : Prop :=
  RunBase g sp x ∧ Stg (geometry g) x.2 (aStart x.1) live0 (decide (x.1.p % 2 = 1)) t ∧
    val32 t.mem (geometry g).B (arr (geometry g).w aVQ) (2 * (geometry g).w) = x.1.p * x.1.q

theorem startBal_ok {g : CallGeometry} {sp : BitVec 32} {x : Vals × State} {t : State}
    (h : RunBase g sp x ∧ Stg (geometry g) x.2 (aStart x.1) live0 (decide (x.1.p % 2 = 1)) t) :
    WP isa (.block (VG.Impl.Rsa.X86.WordModRt.balanced (lay g.full) 1 (pLenArg g.full) (qLenArg g.full) aN sG)) t
      (AtBal g sp x) := by
  obtain ⟨⟨r, b⟩, h6⟩ := h
  obtain ⟨ap, -, hap, -, parg⟩ := b.pLen
  obtain ⟨aq, -, haq, -, qarg⟩ := b.qLen
  have ep := r.1.arg parg hap (pLen_lt g.full)
  have eq := r.1.arg qarg haq (qLen_lt g.full)
  refine WP.mono (h6.balanced_ok (h6.arg parg) (h6.arg qarg) hap haq (by decide))
    fun t7 ⟨h7, an, han, cn, _, hg⟩ => ⟨⟨r, b⟩, h7, ?_⟩
  have ea := (stg_run r h6).1.arg cn han (nLen_lt g.full)
  have nv : num t.mem g.base (geometry g).w aN = x.1.n := h6.arrs.get (by decide)
  have tp : 2 ^ 31 ≤ mw t.mem g.base (geometry g).w aN ((geometry g).w - 1) ↔
      2 ^ (32 * (geometry g).w - 1) ≤ x.1.n := by
    rw [← nv]; exact top_iff h6.ws.ws.wpos
  refine hg.trans ?_
  subst ea ep eq
  exact ⟨fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, tp.mp e⟩, fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, tp.mpr e⟩⟩

theorem startGuard_ok {g : CallGeometry} {sp : BitVec 32} {x : Vals × State} {t : State} (h : AtBal g sp x t) :
    WP isa (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc sG)), .alu .cmp .eax (.imm 0)]) t fun t' =>
      AtBal g sp x t' ∧ t'.zf = some (decide (slot t'.mem g.base sG = 0)) := by
  obtain ⟨rb, hs, hg⟩ := h
  refine wp_movS (readSrc_sc hs.ws.ws.workspace (by have := hs.ws.ws.hdr_le; unfold sG hdr at *; omega_using [this]))
    fun u U _ => wp_cmpi fun t' T _ z => WP.block_nil ?_
  have hs' := (hs.regs U.keeps U.mem (by decide)).regs (T.keeps []) T.mem (by decide)
  have mm : t'.mem = t.mem := T.mem.trans U.mem
  have sl : slot t'.mem g.base sG = slot t.mem g.base sG := by rw [mm]
  refine ⟨⟨rb, hs', by rw [sl]; exact hg⟩, ?_⟩
  rw [z, U.gpr, sub0_beq, sl]; rfl

/-- Under the guard, the product over the primes' `w / 2` words. -/
theorem halfProd_ok {g : CallGeometry} {sp : BitVec 32} {x : Vals × State} {t : State}
    (h : AtBal g sp x t ∧ BalN g x.1.n) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.mulHalf (lay g.full) aVQ aP aQ) t (AtProd g sp x) := by
  obtain ⟨⟨⟨r, b⟩, hs, _⟩, bal⟩ := h
  obtain ⟨a, -, ha, plt, parg⟩ := b.pLen
  obtain ⟨a', -, ha', qlt, qarg⟩ := b.qLen
  have ea := r.1.arg parg ha (pLen_lt g.full)
  have ea' := r.1.arg qarg ha' (qLen_lt g.full)
  subst ea ea'
  obtain ⟨h8, hp, hq, -, -⟩ := bal
  have e8 : 32 * ((geometry g).w / 2) = 8 * (g.args (pLenArg g.full)).toNat := by
    simp only [geometry, Geo.w, VG.Proof.Rsa.X86.KeyRt.kw, Spec.Rsa.modulusWords]; omega_using [h8, hp]
  exact WP.mono (hs.mulHalf_ok (o := aVQ) (a := aP) (b := aQ) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by show x.1.p < _; rw [e8]; exact plt)
    (by show x.1.q < _; rw [e8, show 8 * (g.args (pLenArg g.full)).toNat = 8 * (g.args (qLenArg g.full)).toNat by
      omega_using [hp, hq]]; exact qlt)) fun _ ⟨ht, e⟩ => ⟨⟨r, b⟩, ht, e⟩

theorem start_relCT {g : CallGeometry} {sp : BitVec 32} (ck : KcCk g.full) :
    RelCT isa (Both₂ fun x t => RunBase g sp x ∧ t = x.2) (start g.full) (Both₂ (AtStart g sp)) := by
  unfold start
  simp only [seqs]
  -- `setOne` and `bitOf`.
  refine VG.RelCT.assoc (VG.RelCT.seq (R := Both₂ fun x t => RunBase g sp x ∧
    Stg (geometry g) x.2 (aStart x.1) live0 (decide (x.1.p % 2 = 1)) t)
    (taintLift ck.first (fun x t h => h.2 ▸ h.1.1) fun x t h => by
      obtain ⟨hb, rfl⟩ := h; exact WP.mono (first_ok hb.2) fun _ ht => ⟨hb, ht⟩) ?_)
  -- The guard.
  refine VG.RelCT.seq (R := Both₂ (AtBal g sp))
    (taintLift ck.bal (fun x t h => stg_run h.1.1 h.2) fun x t h => startBal_ok h) ?_
  -- The product `p q`: over the primes' `w / 2` words where the guard holds.
  refine VG.RelCT.seq (R := Both₂ (AtProd g sp)) ?_ ?_
  · unfold VG.Impl.Rsa.X86.WordModRt.ifBalanced
    have zEq : ∀ {t₁ t₂ : State}, Both₂ (fun x t => AtBal g sp x t ∧ t.zf = some (decide (slot t.mem g.base sG = 0)))
        t₁ t₂ → t₁.zf = t₂.zf := fun {t₁ t₂} ⟨x₁, x₂, hn, ⟨g₁, z₁⟩, ⟨g₂, z₂⟩⟩ => by
      rw [z₁, z₂]
      have : (slot t₁.mem g.base sG = 0) ↔ (slot t₂.mem g.base sG = 0) := by
        rw [g₁.2.2, g₂.2.2]; change BalN g x₁.1.n ↔ BalN g x₂.1.n; rw [hn]
      simp only [this]
    refine VG.RelCT.seq (R := Both₂ fun x t => AtBal g sp x t ∧ t.zf = some (decide (slot t.mem g.base sG = 0)))
      (taintLift ck.guard (fun x t h => stg_run h.1.1 h.2.1) fun x t h => startGuard_ok h)
      (VG.RelCT.ite (M := isa) (c := .e) (fun t₁ t₂ h => zEq h) ?_ ?_)
    · refine (relLift (Rel := fun x₁ x₂ : Vals × State => x₁.1.n = x₂.1.n)
        (P := fun x t => AtBal g sp x t ∧ BalN g x.1.n) ?_ fun x t h => halfProd_ok h).mono ?_ fun _ _ h => h
      · refine fun t₁ t₂ t₁' t₂' s₁ s₂ hp e₁ e₂ => ?_
        obtain ⟨x₁, x₂, _, h₁, h₂⟩ := hp
        exact VG.Proof.Rsa.X86.WordRt.mulHalf_relCT (τ := τV g.full) (Fr := Run g sp) (B := g.base) (Z := g.size)
          (fun _ _ a b => a.agree b) (fun f K d e O => f.frame K d e O) (τV_regs g.full)
          (by show 1 ≤ VG.Proof.Rsa.X86.KeyRt.kw _; exact h₁.1.2.1.ws.kw_pos)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          ck.half.c₀ ck.half.c₁ ck.half.c₂ _ _ _ _ _ _
          ⟨⟨h₁.1.2.1.ws, stg_run h₁.1.1.1 h₁.1.2.1⟩, ⟨h₂.1.2.1.ws, stg_run h₂.1.1.1 h₂.1.2.1⟩⟩ e₁ e₂
      · rintro t₁ t₂ ⟨hb, et⟩
        have et₂ : isa.eval .e t₂ = some true := (zEq hb).symm.trans et
        obtain ⟨x₁, x₂, hn, ⟨g₁, z₁⟩, ⟨g₂, z₂⟩⟩ := hb
        have b₁ : BalN g x₁.1.n := g₁.2.2.mp (by
          change t₁.zf = _ at et; rw [z₁] at et; simpa using et)
        have b₂ : BalN g x₂.1.n := g₂.2.2.mp (by
          change t₂.zf = _ at et₂; rw [z₂] at et₂; simpa using et₂)
        exact ⟨x₁, x₂, hn, ⟨g₁, b₁⟩, ⟨g₂, b₂⟩⟩
    · refine (relLift (Rel := fun x₁ x₂ : Vals × State => x₁.1.n = x₂.1.n) (P := AtBal g sp) ?_ fun x t h =>
        WP.mono (h.2.1.mulWide_ok (o := aVQ) (a := aP) (b := aQ) (by decide) (by decide) (by decide) (by decide)
          (by decide)) fun _ ⟨ht, e⟩ => ⟨h.1, ht, e⟩).mono ?_ fun _ _ h => h
      · refine fun t₁ t₂ t₁' t₂' s₁ s₂ hp e₁ e₂ => ?_
        obtain ⟨x₁, x₂, _, h₁, h₂⟩ := hp
        exact VG.Proof.Rsa.X86.WordRt.mulRows_relCT (τ := τV g.full) (Fr := Run g sp) (B := g.base) (Z := g.size)
          (fun _ _ a b => a.agree b) (fun f K d e O => f.frame K d e O) (τV_regs g.full)
          (rows := none) (by show 1 ≤ VG.Proof.Rsa.X86.KeyRt.kw _; exact h₁.2.1.ws.kw_pos) (Nat.le_refl _)
          (fun k hk => by cases hk) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          ck.rows.c₀ ck.rows.c₁ ck.rows.c₂ _ _ _ _ _ _
          ⟨⟨h₁.2.1.ws, stg_run h₁.1.1 h₁.2.1⟩, ⟨h₂.2.1.ws, stg_run h₂.1.1 h₂.2.1⟩⟩ e₁ e₂
      · rintro t₁ t₂ ⟨⟨x₁, x₂, hn, ⟨g₁, _⟩, ⟨g₂, _⟩⟩, _⟩
        exact ⟨x₁, x₂, hn, g₁, g₂⟩
  · -- `p q = n`, and'ed into the mask.
    refine taintLift ck.eqAcc (fun x t h => stg_run h.1.1 h.2.1) fun x t h => ?_
    refine WP.seq (WP.mono (h.2.1.eqWide_ok (o := aVQ) (n := aN) (by decide) (by decide)) fun t1 ⟨h1, e1⟩ => ?_)
    refine WP.mono (h1.acc_ok (d := decide (x.1.p * x.1.q = x.1.n)) ?_) fun _ ht => ⟨h.1, ht⟩
    rw [e1, h.2.2]
    change (if x.1.p * x.1.q = x.1.n then 1 else 0) = _
    by_cases hh : x.1.p * x.1.q = x.1.n <;> simp [hh]

/-- Before the guard's branch: `p - 1`, `q - 1`, and the guard in `sG`. -/
def AtGuard (g : CallGeometry) (sp : BitVec 32) (x : Vals × State) (t : State) : Prop :=
  RunBase g sp x ∧ (∃ c, Stg (geometry g) x.2 (aFin x.1) liveFin c t) ∧
    (slot t.mem g.base sG = 0 ↔ BalN g x.1.n)

/-- After either branch: the frame. -/
def Done (g : CallGeometry) (sp : BitVec 32) (t₁ t₂ : State) : Prop :=
  ∃ u₁ u₂, (Run g sp u₁ ∧ Fm (geometry g) u₁ t₁) ∧ (Run g sp u₂ ∧ Fm (geometry g) u₂ t₂)

theorem guardPre_ok {g : CallGeometry} {sp : BitVec 32} {x : Vals × State} {t : State} (h : AtStart g sp x t) :
    WP isa (seqs [VG.Impl.Rsa.X86.KeyRt.copy (lay g.full) aM1 aP, .block (VG.Impl.Rsa.X86.KeyRt.clrLow (lay g.full) aM1),
      VG.Impl.Rsa.X86.KeyRt.copy (lay g.full) aM2 aQ, .block (VG.Impl.Rsa.X86.KeyRt.clrLow (lay g.full) aM2),
      .block (VG.Impl.Rsa.X86.WordModRt.balanced (lay g.full) 1 (pLenArg g.full) (qLenArg g.full) aN sG)]) t
      (AtGuard g sp x) := by
  obtain ⟨⟨r, b⟩, h⟩ := h
  obtain ⟨ap, -, hap, -, parg⟩ := b.pLen
  obtain ⟨aq, -, haq, -, qarg⟩ := b.qLen
  have ep := r.1.arg parg hap (pLen_lt g.full)
  have eq := r.1.arg qarg haq (qLen_lt g.full)
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (h.copy_ok (o := aM1) (a := aP) (by decide) (by decide) (by decide)) fun t3 h3 => ?_
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (h3.clrLow_ok (j := aM1) (by decide)) fun t4 h4 => ?_
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (h4.copy_ok (o := aM2) (a := aQ) (by decide) (by decide) (by decide)) fun t5 h5 => ?_
  rw [wp_seqs_cons (by simp)]
  refine WP.mono (h5.clrLow_ok (j := aM2) (by decide)) fun t6 h6 => ?_
  have h6' : Stg (geometry g) x.2 (aFin x.1) liveFin _ t6 := h6.congr rfl
  refine WP.mono (h6'.balanced_ok (h6'.arg parg) (h6'.arg qarg) hap haq (by decide))
    fun t7 ⟨h7, an, han, cn, _, hg⟩ => ⟨⟨r, b⟩, ⟨_, h7⟩, ?_⟩
  have ea := (stg_run r h6').1.arg cn han (nLen_lt g.full)
  have nv : num t6.mem g.base (geometry g).w aN = x.1.n := h6'.arrs.get (by decide)
  have tp : 2 ^ 31 ≤ mw t6.mem g.base (geometry g).w aN ((geometry g).w - 1) ↔
      2 ^ (32 * (geometry g).w - 1) ≤ x.1.n := by
    rw [← nv]; exact top_iff h6'.ws.ws.wpos
  refine hg.trans ?_
  subst ea ep eq
  exact ⟨fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, tp.mp e⟩, fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, tp.mpr e⟩⟩

theorem guard_ok {g : CallGeometry} {sp : BitVec 32} {x : Vals × State} {t : State} (h : AtGuard g sp x t) :
    WP isa (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc sG)), .alu .cmp .eax (.imm 0)]) t fun t' =>
      AtGuard g sp x t' ∧ t'.zf = some (decide (slot t'.mem g.base sG = 0)) := by
  obtain ⟨rb, ⟨c, hs⟩, hg⟩ := h
  refine wp_movS (readSrc_sc hs.ws.ws.workspace (by have := hs.ws.ws.hdr_le; unfold sG hdr at *; omega_using [this]))
    fun u U _ => wp_cmpi fun t' T _ z => WP.block_nil ?_
  have hs' := (hs.regs U.keeps U.mem (by decide)).regs (T.keeps []) T.mem (by decide)
  have mm : t'.mem = t.mem := T.mem.trans U.mem
  have sl : slot t'.mem g.base sG = slot t.mem g.base sG := by rw [mm]
  refine ⟨⟨rb, ⟨c, hs'⟩, by rw [sl]; exact hg⟩, ?_⟩
  rw [z, U.gpr, sub0_beq, sl]; rfl

theorem bits_ok {g : CallGeometry} {sp : BitVec 32} {x : Vals × State} {t : State} (h : AtGuard g sp x t) :
    WP isa (bitsBranch g.full) t fun t' => Run g sp x.2 ∧ Fm (geometry g) x.2 t' := by
  obtain ⟨⟨r, b⟩, ⟨c, hs⟩, _⟩ := h
  unfold bitsBranch
  split
  · refine WP.seq (WP.mono (hs.productsP_ok b.qLen) fun t1 ⟨_, _, _, _, h1⟩ => ?_)
    exact WP.mono (dBits_ok h1) fun _ ⟨_, _, _, _, _, _, h2⟩ => ⟨r, h2.fm⟩
  · exact WP.mono (hs.productsP_ok b.qLen) fun _ ⟨_, _, _, _, h1⟩ => ⟨r, h1.fm⟩

/-- Under the guard, a run is in the word steps. -/
theorem AtGuard.win {g : CallGeometry} {sp : BitVec 32} {x : Vals × State} {t : State} (h : AtGuard g sp x t)
    (bal : BalN g x.1.n) : WIn g sp (g.args (pLenArg g.full)).toNat x.2 t := by
  obtain ⟨⟨r, b⟩, ⟨c, hs⟩, _⟩ := h
  obtain ⟨a, -, ha, -, parg⟩ := b.pLen
  have ea := r.1.arg parg ha (pLen_lt g.full)
  subst ea
  obtain ⟨h8, hp, -, h128, -⟩ := bal
  refine ⟨r, hs.fm, ⟨parg, ha⟩, ?_, ?_⟩
  · simp only [wq]; omega_using [hp, h128]
  · simp only [wq, geometry, Geo.w, VG.Proof.Rsa.X86.KeyRt.kw, Spec.Rsa.modulusWords]; omega_using [hp, h128]

theorem crtChecks_relCT {g : CallGeometry} {sp : BitVec 32} (ck : KcCk g.full) :
    RelCT isa (Both₂ (AtStart g sp)) (crtChecks g.full (wordBranch g.full) (bitsBranch g.full)) (Done g sp) := by
  unfold crtChecks
  refine RelCT.seqs_append (l₁ := [VG.Impl.Rsa.X86.KeyRt.copy (lay g.full) aM1 aP,
      .block (VG.Impl.Rsa.X86.KeyRt.clrLow (lay g.full) aM1), VG.Impl.Rsa.X86.KeyRt.copy (lay g.full) aM2 aQ,
      .block (VG.Impl.Rsa.X86.KeyRt.clrLow (lay g.full) aM2),
      .block (VG.Impl.Rsa.X86.WordModRt.balanced (lay g.full) 1 (pLenArg g.full) (qLenArg g.full) aN sG)])
    (l₂ := [VG.Impl.Rsa.X86.WordModRt.ifBalanced sG (wordBranch g.full) (bitsBranch g.full)]) (by simp) (by simp)
    (VG.RelCT.seq (taintLift ck.pre (fun x t h => stg_run h.1.1 h.2) fun x t h => guardPre_ok h) ?_)
  show RelCT isa _ (VG.Impl.Rsa.X86.WordModRt.ifBalanced sG _ _) _
  unfold VG.Impl.Rsa.X86.WordModRt.ifBalanced
  have zEq : ∀ {t₁ t₂ : State}, Both₂ (fun x t => AtGuard g sp x t ∧ t.zf = some (decide (slot t.mem g.base sG = 0)))
      t₁ t₂ → t₁.zf = t₂.zf := fun {t₁ t₂} ⟨x₁, x₂, hn, ⟨g₁, z₁⟩, ⟨g₂, z₂⟩⟩ => by
    rw [z₁, z₂]
    have : (slot t₁.mem g.base sG = 0) ↔ (slot t₂.mem g.base sG = 0) := by
      rw [g₁.2.2, g₂.2.2]; change BalN g x₁.1.n ↔ BalN g x₂.1.n; rw [hn]
    simp only [this]
  refine VG.RelCT.seq (R := Both₂ fun x t => AtGuard g sp x t ∧ t.zf = some (decide (slot t.mem g.base sG = 0)))
    (taintLift ck.guard (fun x t h => stg_run h.1.1 h.2.1.choose_spec) fun x t h => guard_ok h)
    (VG.RelCT.ite (M := isa) (c := .e) (fun t₁ t₂ h => zEq h) ?_ ?_)
  · -- Under the guard: the word steps.
    refine (wBranch (sp := sp) (a := (g.args (pLenArg g.full)).toNat) ck.word).mono ?_
      fun _ _ ⟨u₁, u₂, _, w₁, w₂⟩ => ⟨u₁, u₂, ⟨w₁.1, w₁.2.1⟩, ⟨w₂.1, w₂.2.1⟩⟩
    rintro t₁ t₂ ⟨hb, et⟩
    have et₂ : isa.eval .e t₂ = some true := (zEq hb).symm.trans et
    obtain ⟨x₁, x₂, _, ⟨g₁, z₁⟩, ⟨g₂, z₂⟩⟩ := hb
    have b₁ : BalN g x₁.1.n := g₁.2.2.mp (by
      change t₁.zf = _ at et; rw [z₁] at et; simpa using et)
    have b₂ : BalN g x₂.1.n := g₂.2.2.mp (by
      change t₂.zf = _ at et₂; rw [z₂] at et₂; simpa using et₂)
    exact ⟨x₁.2, x₂.2, trivial, g₁.win b₁, g₂.win b₂⟩
  · -- Else bit by bit.
    refine ((taintLift (P := AtGuard g sp) ck.bits (fun x t h => stg_run h.1.1 h.2.1.choose_spec)
      fun x t h => bits_ok h).mono (fun t₁ t₂ ⟨⟨x₁, x₂, hn, ⟨g₁, _⟩, ⟨g₂, _⟩⟩, _⟩ => ⟨x₁, x₂, hn, g₁, g₂⟩)
      fun _ _ ⟨x₁, x₂, _, h₁, h₂⟩ => ⟨x₁.2, x₂.2, h₁, h₂⟩)

/-! ## `sized` -/

theorem body_eq (full : Bool) : (if full then keyBody full else crtBody full) =
    seqs [start full, crtChecks full (wordBranch full) (bitsBranch full)] := by
  cases full <;> rfl

theorem loads_run {g : CallGeometry} {sp : BitVec 32} {s t : State} (h : Run g sp s) (it : Inputs g t)
    (K : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t) : Run g sp t :=
  ⟨it, ⟨by rw [K.1 _ (by decide)]; exact h.2.1.1, by rw [K.2.2, K.1 _ (by decide)]; exact h.2.1.2⟩,
    (K.1 _ (by decide)).trans h.2.2⟩

/-- Two runs of `sized` with the same `n` leak the same trace. -/
theorem sized_relCT (g : CallGeometry) (len : Lengths g) (sp : BitVec 32) :
    RelCT isa (fun s₁ s₂ => (Run g sp s₁ ∧ Run g sp s₂) ∧ inputBytes g s₁.mem 0 = inputBytes g s₂.mem 0)
      (sized g.full) fun _ _ => True := by
  have ck := kcCk g.full
  unfold sized
  simp only [seqs]
  refine VG.RelCT.seq (R := Both₂ fun x t => RunBase g sp x ∧ t = x.2) ?_ (VG.RelCT.seq (R := Done g sp) ?_ ?_)
  · obtain ⟨_, hc⟩ := ck.loads
    have T := VG.RelCT.wpDep (VG.RelCT.taint (A := sseTaint) (τV g.full)
      (P := fun s₁ s₂ => (Run g sp s₁ ∧ Run g sp s₂) ∧ inputBytes g s₁.mem 0 = inputBytes g s₂.mem 0)
      (fun t₁ t₂ h => h.1.1.agree h.1.2) hc)
      (F := fun (σ t : State) => Run g sp t ∧ BodyIn (geometry g) (numbers g σ.mem) t) fun s₁ s₂ h =>
        ⟨WP.mono (loads_ok h.1.1.1 len) fun t ⟨it, b, _, K⟩ => ⟨loads_run h.1.1 it K, b⟩,
          WP.mono (loads_ok h.1.2.1 len) fun t ⟨it, b, _, K⟩ => ⟨loads_run h.1.2 it K, b⟩⟩
    refine T.mono (fun _ _ h => h) ?_
    rintro t₁ t₂ ⟨_, σ₁, σ₂, hp, ⟨r₁, b₁⟩, ⟨r₂, b₂⟩⟩
    refine ⟨(numbers g σ₁.mem, t₁), (numbers g σ₂.mem, t₂), ?_, ⟨⟨r₁, b₁⟩, rfl⟩, ⟨⟨r₂, b₂⟩, rfl⟩⟩
    show Spec.Rsa.os2ip (inputBytes g σ₁.mem 0) = Spec.Rsa.os2ip (inputBytes g σ₂.mem 0)
    rw [hp.2]
  · rw [body_eq]
    exact RelCT.seqs_cons (by simp) (start_relCT ck) (crtChecks_relCT ck)
  · obtain ⟨_, hc⟩ := ck.last
    exact VG.RelCT.taint (A := sseTaint) (τV g.full)
      (fun t₁ t₂ ⟨_, _, ⟨r₁, f₁⟩, ⟨r₂, f₂⟩⟩ => (f₁.run r₁).agree (f₂.run r₂)) hc

open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.KeyCheckRt (sized)
open VG.Proof.Bignum.X86.PublicRt (Both relCT_narrow)

/-- What the runs of `sized` from the states themselves need: the inputs, `esp`, and the arguments apart
from what the body writes. -/
def SizedAt (g : CallGeometry) (sp : BitVec 32) (s : State) : Prop :=
  Inputs g s ∧ s.gpr .esp = sp ∧ sp.toNat + argSpan g.full ≤ 2 ^ 32 ∧
    ∀ r ∈ g.writes, Region.Disjoint ⟨sp.setWidth 64, argSpan g.full⟩ r

theorem narrow_inputs {g : CallGeometry} {s : State} (h : Inputs g s) :
    Inputs g (s.withRegions (s.rd ++ s.wr) g.writes) := by
  refine ⟨⟨⟨h.ws.workspace.edi, by simp [State.withRegions, CallGeometry.writes], h.ws.workspace.nowrap,
      h.ws.workspace.stk⟩, h.ws.fits, h.ws.wpos, h.ws.wle⟩, h.lower, h.upper,
    fun i hi => ⟨⟨?_, (h.arguments i hi).stack.apart⟩, (h.arguments i hi).value⟩, h.stackApart, h.inputPositive,
    h.inputBound, h.inputFit, fun j hj => ?_, h.inputApart⟩
  · obtain ⟨r, hr, hc⟩ := (h.arguments i hi).stack.read
    exact ⟨r, List.mem_append_left _ hr, hc⟩
  · obtain ⟨r, hr, hc⟩ := h.inputRead j hj
    exact ⟨r, List.mem_append_left _ hr, hc⟩

theorem narrow_run {g : CallGeometry} {sp : BitVec 32} {s : State} (S : SizedAt g sp s) :
    Run g sp (s.withRegions (s.rd ++ s.wr) g.writes) := by
  obtain ⟨h, esp, fit, apart⟩ := S
  refine ⟨narrow_inputs h, ⟨?_, fun r hr => ?_⟩, esp⟩
  · show (s.gpr .esp).toNat + argSpan g.full ≤ _; rw [esp]; exact fit
  · show Region.Disjoint ⟨(s.gpr .esp).setWidth 64, argSpan g.full⟩ r; rw [esp]; exact apart r hr

theorem sizedNarrow_relCT (g : CallGeometry) (len : Lengths g) (sp : BitVec 32) :
    RelCT isa (fun s₁ s₂ => Both (SizedAt g sp) s₁ s₂ ∧ inputBytes g s₁.mem 0 = inputBytes g s₂.mem 0)
      (sized g.full) fun _ _ => True := by
  refine relCT_narrow (Pn := fun s₁ s₂ => (Run g sp s₁ ∧ Run g sp s₂) ∧ inputBytes g s₁.mem 0 = inputBytes g s₂.mem 0)
    (fun s => s.rd ++ s.wr) (fun _ => g.writes) (fun s₁ s₂ ⟨⟨S₁, S₂⟩, hn⟩ => ?_) (sized_relCT g len sp)
  have cov : ∀ {s : State}, SizedAt g sp s → Covers g.writes s.wr := by
    intro s S
    apply Covers.of_forall
    intro r hr
    simp only [CallGeometry.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact Covers.of_mem (by simpa using S.1.ws.workspace.wr)
  have wp : ∀ {s : State}, SizedAt g sp s →
      ∃ F, WP isa (sized g.full) (s.withRegions (s.rd ++ s.wr) g.writes) F :=
    fun S => ⟨_, sized_wp (narrow_inputs S.1) len⟩
  exact ⟨Covers.append_left (Covers.refl _) (Covers.right (cov S₁)), cov S₁,
    Covers.append_left (Covers.refl _) (Covers.right (cov S₂)), cov S₂, wp S₁, wp S₂,
    ⟨narrow_run S₁, narrow_run S₂⟩, hn⟩

end VG.Proof.Rsa.X86.KeyCheck

end

end

/-! ### `Rsa.X86.KcExponentTiming`, which only this module used -/

section

/-! # Exponent-validation traces depend only on the declared public exponent bytes -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum VG.Proof.Bignum.X86

theorem exponent_trace {g : CallGeometry} {s t : State}
    (H : Pair g s t)
    (same : Spec.Rsa.bytesAt s.mem (byteAddr (g.args 2)) (g.args 3).toNat =
      Spec.Rsa.bytesAt t.mem (byteAddr (g.args 2)) (g.args 3).toNat)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa (.seq (.block (VG.Impl.Rsa.X86.CrtValues.inputArgs 2)) exponentCheck) s tr sf) (F : Exec isa (.seq (.block (VG.Impl.Rsa.X86.CrtValues.inputArgs 2)) exponentCheck) t ur tf) : tr = ur := by
  cases E with
  | seq E1 E2 =>
    cases F with
    | seq F1 F2 =>
      have T1 := (loadArguments_relCT 2 3 (g.args 2) (g.args 3) _ _ _ _ _ _
        ⟨H.agree, (H.left.arguments 2 (by cases g.full <;> decide)).readSrc, (H.right.arguments 2 (by cases g.full <;> decide)).readSrc,
          (H.left.arguments 3 (by cases g.full <;> decide)).readSrc, (H.right.arguments 3 (by cases g.full <;> decide)).readSrc⟩ E1 F1).1
      obtain ⟨Ps, Cs, Ms, Ks⟩ := wp_result (argumentPair_ok (by decide) (by decide)
        (H.left.arguments 2 (by cases g.full <;> decide)).readSrc (H.left.arguments 3 (by cases g.full <;> decide)).readSrc) E1
      obtain ⟨Pt, Ct, Mt, Kt⟩ := wp_result (argumentPair_ok (by decide) (by decide)
        (H.right.arguments 2 (by cases g.full <;> decide)).readSrc (H.right.arguments 3 (by cases g.full <;> decide)).readSrc) F1
      have T2 := exponentCheck_trace (ep := g.args 2)
        (eb := Spec.Rsa.bytesAt s.mem (byteAddr (g.args 2)) (g.args 3).toNat)
        (by rw [bytesAt_length]; exact H.left.inputPositive 1 (by cases g.full <;> decide))
        (by rw [bytesAt_length]; exact (g.args 3).isLt)
        (by rw [bytesAt_length]; exact H.left.inputFit 1 (by cases g.full <;> decide))
        (by rw [bytesAt_length, Ks.2.1, Ks.2.2]; exact H.left.inputRead 1 (by cases g.full <;> decide))
        (by rw [bytesAt_length, Kt.2.1, Kt.2.2]; exact H.right.inputRead 1 (by cases g.full <;> decide))
        (by intro i hi; rw [Ms]; simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range])
        (by
          intro i hi
          rw [Mt]
          have Eq := List.getElem_of_eq same hi
          simpa only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range] using Eq.symm)
        Ps Pt (by rw [bytesAt_length, BitVec.ofNat_toNat]; exact Cs)
        (by rw [bytesAt_length, BitVec.ofNat_toNat]; exact Ct) E2 F2
      rw [T1, T2]

end VG.Proof.Rsa.X86.KeyCheck

end

end


/-! # Public exponent rejection and width dispatch have matching traces -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum.X86 VG.Impl.Rsa.X86.KeyCheck
open VG.Impl.Rsa.X86.KeyCheckRt (checkExponent)

def ExponentPair (g : CallGeometry) (sp : BitVec 32) (s t : State) : Prop :=
  ((Pair g s t ∧ s.gpr .esp = sp) ∧
    ∃ b : Bool, s.gpr .eax = BitVec.ofNat 32 b.toNat ∧ t.gpr .eax = BitVec.ofNat 32 b.toNat) ∧
  inputBytes g s.mem 0 = inputBytes g t.mem 0

theorem scan_relCT (g : CallGeometry) (sp : BitVec 32) :
    RelCT isa (fun s t => ((Pair g s t ∧ s.gpr .esp = sp) ∧ inputBytes g s.mem 1 = inputBytes g t.mem 1) ∧
      inputBytes g s.mem 0 = inputBytes g t.mem 0)
      (.seq (.block (VG.Impl.Rsa.X86.CrtValues.inputArgs 2)) VG.Impl.Bignum.X86.exponentCheck)
      (ExponentPair g sp) := by
  intro s t tr ur sf tf ⟨⟨⟨h, esp⟩, same⟩, same0⟩ es et
  have trace := exponent_trace h same es et
  obtain ⟨vs, ms, ks⟩ := wp_result (exponent_ok h.left) es
  obtain ⟨vt, mt, kt⟩ := wp_result (exponent_ok h.right) et
  refine ⟨trace, ⟨⟨h.keepMem ks kt (by decide) (by decide) ms mt, (ks.1 _ (by decide)).trans esp⟩, _, vs, ?_⟩,
    by rw [ms, mt]; exact same0⟩
  change tf.gpr .eax = BitVec.ofNat 32 (Spec.Rsa.exponentValid (Spec.Rsa.os2ip (inputBytes g s.mem 1))).toNat
  rw [same]; exact vt

theorem flag_relCT (g : CallGeometry) (sp : BitVec 32) :
    RelCT isa (ExponentPair g sp) (.block [.alu .cmp .eax (.imm 0)])
      (fun s t => ((Pair g s t ∧ s.gpr .esp = sp) ∧ s.zf = t.zf) ∧ inputBytes g s.mem 0 = inputBytes g t.mem 0) := by
  have trace : RelCT isa (fun _ _ => True) (.block [.alu .cmp .eax (.imm 0)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (τr []) (fun _ _ _ => agree_regs (by simp)) (hc := .block [])
    rfl
  intro s t tr ur sf tf ⟨⟨⟨h, esp⟩, b, vs, vt⟩, same0⟩ es et
  obtain ⟨zs, ms, ks⟩ := wp_result (exponentFlag_ok b vs) es
  obtain ⟨zt, mt, kt⟩ := wp_result (exponentFlag_ok b vt) et
  exact ⟨(trace _ _ _ _ _ _ trivial es et).1,
    ⟨⟨h.keepMem ks kt (by simp) (by simp) ms mt, (ks.1 _ (by simp)).trans esp⟩, zs.trans zt.symm⟩,
    by rw [ms, mt]; exact same0⟩

theorem failure_relCT : RelCT isa (fun _ _ => True) failure (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (τr []) (fun _ _ _ => agree_regs (by simp)) (hc := .block [])
  rfl

theorem checkExponent_relCT (g : CallGeometry) (len : Lengths g) (sp : BitVec 32)
    (fit : sp.toNat + argSpan g.full ≤ 2 ^ 32)
    (apart : ∀ r ∈ g.writes, Region.Disjoint ⟨sp.setWidth 64, argSpan g.full⟩ r) :
    RelCT isa (fun s t => ((Pair g s t ∧ s.gpr .esp = sp) ∧ inputBytes g s.mem 1 = inputBytes g t.mem 1) ∧
      inputBytes g s.mem 0 = inputBytes g t.mem 0)
      (checkExponent g.full) (fun _ _ => True) := by
  apply VG.RelCT.seq (scan_relCT g sp)
  apply VG.RelCT.seq (flag_relCT g sp)
  apply VG.RelCT.ite (M := isa) (c := .e)
  · exact fun _ _ h => h.1.2
  · exact failure_relCT.mono (fun _ _ _ => trivial) (fun _ _ h => h)
  · exact (sizedNarrow_relCT g len sp).mono
      (fun _ _ h => ⟨⟨⟨h.1.1.1.1.left, h.1.1.1.2, fit, apart⟩,
        ⟨h.1.1.1.1.right, h.1.1.1.1.sp.symm.trans h.1.1.1.2, fit, apart⟩⟩, h.1.2⟩)
      (fun _ _ h => h)
end VG.Proof.Rsa.X86.KeyCheck

end

end


/-! # Key-validation timing reveals only the public modulus and exponent -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum.X86 VG.Impl.Rsa.X86.KeyCheck
open VG.Impl.Rsa.X86.KeyCheckRt (body checkExponent)

theorem modulus_relCT (g : CallGeometry) :
    RelCT isa (Pair g) (.seq (.block (VG.Impl.Rsa.X86.CrtValues.inputArgs 0))
      (.block VG.Impl.Bignum.X86.modulusCheck)) (fun _ _ => True) := by
  have check : RelCT isa (VG.X86.Taint.Agree loadTaint) (.block VG.Impl.Bignum.X86.modulusCheck)
      (fun _ _ => True) := by
    apply RelCT.taint (A := taint) loadTaint (fun _ _ h => h) (hc := .block [])
    rfl
  apply (VG.RelCT.seq (loadArguments_relCT 0 1 (g.args 0) (g.args 1)) check).mono
  · intro s t h
    exact ⟨h.agree,
      (h.left.arguments 0 (by cases g.full <;> decide)).readSrc,
      (h.right.arguments 0 (by cases g.full <;> decide)).readSrc,
      (h.left.arguments 1 (by cases g.full <;> decide)).readSrc,
      (h.right.arguments 1 (by cases g.full <;> decide)).readSrc⟩
  · exact fun _ _ h => h

theorem body_relCT (g : CallGeometry) (len : Lengths g) (sp : BitVec 32)
    (fit : sp.toNat + argSpan g.full ≤ 2 ^ 32)
    (apart : ∀ r ∈ g.writes, Region.Disjoint ⟨sp.setWidth 64, argSpan g.full⟩ r) :
    RelCT isa (fun s t => (Pair g s t ∧ s.gpr .esp = sp) ∧ inputBytes g s.mem 0 = inputBytes g t.mem 0 ∧
      inputBytes g s.mem 1 = inputBytes g t.mem 1) (body g.full) (fun _ _ => True) := by
  let r := fun s t => (Pair g s t ∧ s.gpr .esp = sp) ∧ inputBytes g s.mem 1 = inputBytes g t.mem 1 ∧ s.zf = t.zf ∧
    inputBytes g s.mem 0 = inputBytes g t.mem 0
  have branch : RelCT isa r (.ite .e (checkExponent g.full) failure) (fun _ _ => True) := by
    apply VG.RelCT.ite (M := isa) (c := .e) (P := r)
    · exact fun _ _ h => h.2.2.1
    · exact (checkExponent_relCT g len sp fit apart).mono (fun _ _ h => ⟨⟨h.1.1, h.1.2.1⟩, h.1.2.2.2⟩)
        (fun _ _ h => h)
    · exact failure_relCT.mono (fun _ _ _ => trivial) (fun _ _ h => h)
  intro s t tr ur sf tf ⟨⟨h, esp⟩, modulus, exponent⟩ es et
  cases es with
  | @seq _ _ _ u _ _ _ e1 e2 =>
    cases et with
    | @seq _ _ _ v _ _ _ f1 f2 =>
      have eq1 := (modulus_relCT g _ _ _ _ _ _ h e1 f1).1
      obtain ⟨zs, ms, ks⟩ := wp_result (modulus_ok h.left len.lower len.upper) e1
      obtain ⟨zt, mt, kt⟩ := wp_result (modulus_ok h.right len.lower len.upper) f1
      have next := h.keepMem ks kt (by decide) (by decide) ms mt
      have flags : u.zf = v.zf := by
        rw [zs, zt]
        change some (Spec.Rsa.modulusValid (Spec.Rsa.os2ip (inputBytes g s.mem 0)) _) = _
        rw [modulus]; rfl
      have eq2 := (branch _ _ _ _ _ _ ⟨⟨next, (ks.1 _ (by decide)).trans esp⟩, by rw [ms, mt]; exact exponent, flags,
        by rw [ms, mt]; exact modulus⟩ e2 f2).1
      exact ⟨by rw [eq1, eq2], trivial⟩
end VG.Proof.Rsa.X86.KeyCheck

end

end

/-! ### `Rsa.X86.KcEntryTiming`, which only this module used -/

section

/-! # Saving and restoring registers has a trace fixed by public addresses -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Dsa.X86 VG.Proof.Mont.X86.Dynamic

theorem entry_relCT (full : Bool) :
    RelCT isa (fun s t => s.gpr .esp = t.gpr .esp ∧ stackValue s (VG.Impl.Rsa.X86.KeyCheck.scratchArg full) = stackValue t (VG.Impl.Rsa.X86.KeyCheck.scratchArg full) ∧
      readSrc s (.mem (PublicFn.argument (VG.Impl.Rsa.X86.KeyCheck.scratchArg full))) = some (stackValue s (VG.Impl.Rsa.X86.KeyCheck.scratchArg full)) ∧
      readSrc t (.mem (PublicFn.argument (VG.Impl.Rsa.X86.KeyCheck.scratchArg full))) = some (stackValue t (VG.Impl.Rsa.X86.KeyCheck.scratchArg full)))
      (.block (VG.Impl.Rsa.X86.KeyCheck.entry full)) (VG.X86.Taint.Agree argumentTaint) := by
  unfold VG.Impl.Rsa.X86.KeyCheck.entry
  rw [List.append_assoc]
  apply VG.RelCT.block_append
  exact VG.RelCT.seq (scratchArgument_relCT (VG.Impl.Rsa.X86.KeyCheck.scratchArg full))
    (checkedProgramChange (τ' := { argumentTaint with regs := .ofList [.esp, .edi, .eax] })
      (hint := .block []) rfl rfl)

end VG.Proof.Rsa.X86.KeyCheck

end

end

/-! ### `Rsa.X86.KcArgumentsEq`, which only this module used -/

section

/-! # Only the declared cdecl arguments matter to key-check caller geometry -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.Proof.Bignum.X86

theorem Inputs.argsEq {g : CallGeometry} {s : State} {args : Nat → BitVec 32} (h : Inputs g s)
    (eq : ∀ i < VG.Impl.Rsa.X86.KeyCheck.scratchArg g.full + 2, args i = g.args i) : Inputs {g with args := args} s := by
  have buffers (i : Nat) (hi : i + 1 < VG.Impl.Rsa.X86.KeyCheck.scratchArg g.full + 2) :
      ({g with args := args} : CallGeometry).buffer i = g.buffer i := by
    simp only [CallGeometry.buffer, eq i (by omega_using [hi]), eq (i + 1) hi]
  have writes : ({g with args := args} : CallGeometry).writes = g.writes := rfl
  refine ⟨h.ws, h.lower, h.upper, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    change CallArgument s g.base g.size i (args i)
    rw [eq i hi]
    exact h.arguments i hi
  · intro i hi r hr
    rw [writes] at hr
    exact h.stackApart i hi r hr
  · intro i hi; change 2 * i < VG.Impl.Rsa.X86.KeyCheck.scratchArg g.full at hi; rw [buffers _ (by omega_using [hi])]; exact h.inputPositive i hi
  · intro i hi; change 2 * i < VG.Impl.Rsa.X86.KeyCheck.scratchArg g.full at hi; rw [buffers _ (by omega_using [hi])]; exact h.inputBound i hi
  · intro i hi
    change 2 * i < VG.Impl.Rsa.X86.KeyCheck.scratchArg g.full at hi
    rw [buffers _ (by omega_using [hi])]
    change (args (2 * i)).toNat + _ ≤ _
    rw [eq (2 * i) (by omega_using [hi])]
    exact h.inputFit i hi
  · intro i hi; change 2 * i < VG.Impl.Rsa.X86.KeyCheck.scratchArg g.full at hi; rw [buffers _ (by omega_using [hi])]; exact h.inputRead i hi
  · intro i hi r hr; change 2 * i < VG.Impl.Rsa.X86.KeyCheck.scratchArg g.full at hi; rw [writes] at hr; rw [buffers _ (by omega_using [hi])]; exact h.inputApart i hi r hr

end VG.Proof.Rsa.X86.KeyCheck

end

end

/-! ### `Rsa.X86.KcObservations`, which only this module used -/

section

/-! # Public observations of both RSA key-validation contracts -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.Impl.Rsa.X86.KeyCheck

theorem arguments_eq {full : Bool} {s t : State} (h : (contract full).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ ∀ i < scratchArg full + 2, arg s i = arg t i := by
  cases full
  · change (Proof.Rsa.checkCrtKeyContract abi 20).pub s t at h
    sig_pub [Proof.Rsa.checkCrtKeyContract, Proof.Rsa.checkCrtKeySig, abi, argSlots, argVal, argBytes] at h
    sig_split h
    constructor
    · assumption
    · intro i hi
      change i < 16 at hi
      have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega_using [hi]
      rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  · change (Spec.Rsa.checkKeyContract abi 20).pub s t at h
    sig_pub [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argSlots, argVal, argBytes] at h
    sig_split h
    constructor
    · assumption
    · intro i hi
      change i < 18 at hi
      have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 := by omega_using [hi]
      rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem publicBytes_eq {full : Bool} {s t : State} (h : (contract full).pub s t) :
    inputBytes (caller full s) s.mem 0 = inputBytes (caller full t) t.mem 0 ∧
    inputBytes (caller full s) s.mem 1 = inputBytes (caller full t) t.mem 1 := by
  have args := arguments_eq h
  have leak : ((inputBytes (caller full s) s.mem 0) ++ (inputBytes (caller full s) s.mem 1)).map (·.toNat) =
      ((inputBytes (caller full t) t.mem 0) ++ (inputBytes (caller full t) t.mem 1)).map (·.toNat) := by
    cases full
    · change (Proof.Rsa.checkCrtKeyContract abi 20).pub s t at h
      sig_pub [Proof.Rsa.checkCrtKeyContract, Proof.Rsa.checkCrtKeySig, abi, argSlots, argVal, argBytes] at h
      exact h.2.1
    · change (Spec.Rsa.checkKeyContract abi 20).pub s t at h
      sig_pub [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argSlots, argVal, argBytes] at h
      exact h.2.1
  have both := (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp leak
  have sameLength : (inputBytes (caller full s) s.mem 0).length = (inputBytes (caller full t) t.mem 0).length := by
    simp only [inputBytes, Spec.Rsa.bytesAt, List.length_map, List.length_range]
    change (arg s 1).toNat = (arg t 1).toNat
    rw [args.2 1 (by cases full <;> decide)]
  exact ⟨List.append_inj_left both sameLength, List.append_inj_right both sameLength⟩
end VG.Proof.Rsa.X86.KeyCheck

end

end


/-! # The complete key-validation operation leaks only the contract's declared public inputs -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.KeyCheck
open VG.Impl.Rsa.X86.KeyCheckRt (code)

theorem operation_trace {full : Bool} {s t : State} (a : ABI full s) (b : ABI full t)
    (args : ∀ i < scratchArg full + 2, arg s i = arg t i) (sp : s.gpr .esp = t.gpr .esp)
    (modulus : inputBytes (caller full s) s.mem 0 = inputBytes (caller full t) t.mem 0)
    (exponent : inputBytes (caller full s) s.mem 1 = inputBytes (caller full t) t.mem 1)
    {tr ur : List Leak} {sf tf : State} (es : Exec isa (code full) s tr sf) (et : Exec isa (code full) t ur tf) : tr = ur := by
  have a1 := args 1 (by cases full <;> decide)
  have ac := args (scratchArg full) (by omega_using [])
  have al := args (scratchArg full + 1) (by omega_using [])
  cases es with
  | @seq _ _ _ u _ _ _ e1 er =>
    cases et with
    | @seq _ _ _ v _ _ _ f1 fr =>
      have eq1 := (entry_relCT full _ _ _ _ _ _
        ⟨sp, ac, (a.stackArgument (by omega_using [] : scratchArg full < scratchArg full + 2)).readSrc,
          (b.stackArgument (by omega_using [] : scratchArg full < scratchArg full + 2)).readSrc⟩ e1 f1).1
      obtain ⟨hs, _, ks, os⟩ := wp_result (installed_ok a) e1
      obtain ⟨ht, _, kt, ot⟩ := wp_result (installed_ok b) f1
      have hv : Inputs (caller full s) v := by
        have j := ht.argsEq args
        simpa only [caller, argumentPointer, ← a1, ← ac, ← al] using j
      have pair : Pair (caller full s) u v :=
        ⟨hs, hv, (ks.1 _ (by decide)).trans (sp.trans (kt.1 _ (by decide)).symm)⟩
      have same (i : Nat) (hi : 2 * i < scratchArg full)
          (initial : inputBytes (caller full s) s.mem i = inputBytes (caller full t) t.mem i) :
          inputBytes (caller full s) u.mem i = inputBytes (caller full s) v.mem i := by
        have ns := VG.Proof.Bignum.scratch_bytes os
          (by have := (a.inputLength hi).2; have := a.width.2.1; omega_using [])
          (a.inApart _ (a.inputMember hi))
        have nt := VG.Proof.Bignum.scratch_bytes ot
          (by have := (b.inputLength hi).2; have := b.width.2.1; omega_using [])
          (b.inApart _ (b.inputMember hi))
        change inputBytes (caller full s) u.mem i = inputBytes (caller full s) s.mem i at ns
        change inputBytes (caller full t) v.mem i = inputBytes (caller full t) t.mem i at nt
        have align : inputBytes (caller full s) v.mem i = inputBytes (caller full t) v.mem i := by
          simp only [inputBytes, caller, CallGeometry.buffer]
          rw [args (2 * i) (by omega_using [hi]), args (2 * i + 1) (by omega_using [hi])]
        exact ns.trans (initial.trans (align.trans nt).symm)
      have len : Lengths (caller full s) := a.lengths_ok
      cases er with
      | @seq _ _ _ x _ _ _ e2 e3 =>
        cases fr with
        | @seq _ _ _ y _ _ _ f2 f3 =>
          have espu : u.gpr .esp = s.gpr .esp := ks.1 _ (by decide)
          have span : argSpan full = 4 + 4 * (scratchArg full + 2) := by unfold argSpan; omega_using []
          have fit : (u.gpr .esp).toNat + argSpan (caller full s).full ≤ 2 ^ 32 := by
            rw [espu]; change _ + argSpan full ≤ _; have := a.stackBound; omega_using [span, this]
          have apart : ∀ r ∈ (caller full s).writes,
              Region.Disjoint ⟨(u.gpr .esp).setWidth 64, argSpan (caller full s).full⟩ r := by
            intro r hr
            simp only [CallGeometry.writes, List.mem_singleton] at hr
            subst r
            rw [espu]
            change Region.Disjoint ⟨_, argSpan full⟩ _
            rw [span]
            exact VG.X86.Taint.frame_disjoint (by have := a.stackBound; omega_using [this]) a.retApart a.argsApart
          have eq2 := (body_relCT (caller full s) len _ fit apart _ _ _ _ _ _
            ⟨⟨pair, rfl⟩, same 0 (by cases full <;> decide) modulus, same 1 (by cases full <;> decide) exponent⟩ e2 f2).1
          obtain ⟨hx, kx⟩ := wp_result (body_ok hs len (a.numberBounds u.mem)) e2
          obtain ⟨hy, ky⟩ := wp_result (body_ok hv len (a.numberBounds v.mem)) f2
          have next := pair.after hx.1 hy.1 kx ky (by decide)
          have eq3 := (publicRestore_relCT _ _ _ _ _ _ next.workspace e3 f3).1
          rw [eq1, eq2, eq3]

theorem constantTime (full : Bool) : ConstantTime isa (contract full).pre
    (contract full).pub (code full) := by
  intro s t tr ur sf tf hs ht h es et
  have args := arguments_eq h
  have bytes := publicBytes_eq h
  exact operation_trace (abi_of hs) (abi_of ht) args.2 args.1 bytes.1 bytes.2 es et

end VG.Proof.Rsa.X86.KeyCheck

end

end

/-! # Complete i686 certificates for RSA key validation -/

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/KcReturn.lean`, which only this module imported.
section

/-! # Key validation preserves saved registers and the return address -/

section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum hiding off Outside
open VG.Proof.Bignum.X86 VG.Impl.Bignum.X86
open VG.Impl.Rsa.X86.KeyCheck

theorem body_saved {g : CallGeometry} {s : State} {m m' : Mem} {regs : Reg → BitVec 32}
    (h : Inputs g s) (f : Outside g.base 16 (g.size - 16) m m')
    (saved : Saved m (off g.base) regs PublicFn.savedRegisters) :
    Saved m' (off g.base) regs PublicFn.savedRegisters := by
  have low : 16 ≤ g.size := by have := h.ws.hdr_le; unfold VG.Impl.Rsa.X86.Keys.hdr at this; omega
  have high : g.size ≤ 2 ^ 64 := by have := h.ws.workspace.nowrap; omega
  have frame := outside_frame f (by omega)
  intro p hp
  have bound : p.2 + 4 ≤ 16 := by
    simp only [PublicFn.savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> decide
  refine (frame.readW (r := ⟨g.base, 16⟩) (Offset.contains_base _ bound (by omega)) ?_ (by decide)).trans (saved p hp)
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact Offset.base_disjoint g.base (Nat.le_refl 16) (by omega)

theorem operation_ok {full : Bool} {s : State} (a : ABI full s) :
    WP isa (VG.Impl.Rsa.X86.KeyCheckRt.code full) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (validity full (arg s 1).toNat (numbers (caller full s) s.mem)).toNat ∧
      abiPreserved s t := by
  have low : 16 ≤ (caller full s).size := by have := a.used; omega
  have high : (caller full s).size ≤ 2 ^ 64 := by have := a.scratchBound; omega
  unfold VG.Impl.Rsa.X86.KeyCheckRt.code
  refine WP.seq (WP.mono (installed_ok a) fun u ⟨inputs, saved, ku, ou⟩ => ?_)
  refine WP.seq (WP.mono (body_ok inputs a.lengths_ok (a.numberBounds u.mem))
    fun v ⟨⟨iv, value, frame⟩, kv⟩ => ?_)
  have saveV := body_saved inputs frame saved
  have whole : Frame [⟨(caller full s).base, (caller full s).size⟩] s.mem v.mem := by
    have f := outside_frame (ou.trans (frame.mono (by omega) (by omega))) (by omega)
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using f
  have ret : v.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32 :=
    whole.readW (Region.contains_self _ 4) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr; exact a.retApart) (by decide)
  refine WP.mono (entryRestore_ok iv.ws.workspace low saveV) fun t restored => ?_
  refine ⟨?_, publicRestored_abi restored ((kv.1 _ (by decide)).trans (ku.1 _ (by decide))) ret⟩
  rw [numbers_entry a ou] at value
  rw [restored.other .eax (by decide)]
  exact value
end VG.Proof.Rsa.X86.KeyCheck
end

end

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/KcCorrect.lean`, which only this module imported.
section

/-! # Both i686 key-check operations satisfy their existing shared contracts -/

section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.Proof.Dsa.X86

private theorem bool_result (b : Bool) : BitVec.ofNat 32 b.toNat = (if b then 1 else 0) := by
  cases b <;> rfl

theorem correct (full : Bool) (s : State) (h : (contract full).pre s) :
    ∃ trace t, Exec isa (VG.Impl.Rsa.X86.KeyCheckRt.code full) s trace t ∧ abiPreserved s t ∧
      (contract full).post s t := by
  have a := abi_of h
  obtain ⟨trace, t, run, value, preserved⟩ := operation_ok a
  refine ⟨trace, t, run, preserved, ?_⟩
  cases full
  · change (Proof.Rsa.checkCrtKeyContract abi 20).post s t
    sig_post [Proof.Rsa.checkCrtKeyContract, Proof.Rsa.checkCrtKeySig, abi, argSlots, argVal, argBytes]
    rw [BitVec.setWidth_append_eq_right]
    simp only [validity, numbers, caller, inputBytes, CallGeometry.buffer, Bool.false_eq_true, ite_false] at value
    have dp : (arg s 9).toNat = (arg s 5).toNat := a.dpLen
    have dq : (arg s 11).toNat = (arg s 7).toNat := a.dqLen
    have qi : (arg s 13).toNat = (arg s 5).toNat := a.qiLen
    simp only [Nat.reduceAdd, Nat.reduceMul] at value
    rw [dp, dq, qi] at value
    unfold Spec.Rsa.checkCrtKey
    rw [value]
    rw [VG.Proof.Bignum.bytesAt_length]
    exact bool_result _
  · change (Spec.Rsa.checkKeyContract abi 20).post s t
    sig_post [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argSlots, argVal, argBytes]
    rw [BitVec.setWidth_append_eq_right]
    simp only [validity, numbers, caller, inputBytes, CallGeometry.buffer, ite_true] at value
    have dp : (arg s 11).toNat = (arg s 7).toNat := a.dpLen
    have dq : (arg s 13).toNat = (arg s 9).toNat := a.dqLen
    have qi : (arg s 15).toNat = (arg s 7).toNat := a.qiLen
    simp only [Nat.reduceAdd, Nat.reduceMul] at value
    rw [dp, dq, qi] at value
    unfold Spec.Rsa.checkKey
    rw [value]
    rw [VG.Proof.Bignum.bytesAt_length]
    exact bool_result _
end VG.Proof.Rsa.X86.KeyCheck
end

end

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86
open VG.Impl.Rsa.X86.KeyCheck
open VG.Impl.Rsa.X86.KeyCheckRt (code)

def crtState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x20005 then 16
    else if a = 0x20008 then 64
    else if a = 0x2000d then 32
    else if a = 0x20010 then 3
    else if a = 0x20015 then 48
    else if a = 0x20018 then 32
    else if a = 0x2001d then 64
    else if a = 0x20020 then 32
    else if a = 0x20025 then 80
    else if a = 0x20028 then 32
    else if a = 0x2002d then 96
    else if a = 0x20030 then 32
    else if a = 0x20035 then 112
    else if a = 0x20038 then 32
    else if a = 0x2003e then 1
    else if a = 0x20040 then 32
    else if a = 0x20041 then 4 else 0
  rd := [⟨4096, 64⟩, ⟨8192, 3⟩, ⟨12288, 32⟩, ⟨16384, 32⟩, ⟨20480, 32⟩, ⟨24576, 32⟩, ⟨28672, 32⟩]
  wr := [⟨0x10000, 8448⟩, ⟨0x20004, 64⟩]

theorem crt_satisfiable : ∃ s, (Proof.Rsa.checkCrtKeyContract abi 20).pre s := by
  have a0 : arg crtState 0 = 4096 := by decide
  have a1 : arg crtState 1 = 64 := by decide
  have a2 : arg crtState 2 = 8192 := by decide
  have a3 : arg crtState 3 = 3 := by decide
  have a4 : arg crtState 4 = 12288 := by decide
  have a5 : arg crtState 5 = 32 := by decide
  have a6 : arg crtState 6 = 16384 := by decide
  have a7 : arg crtState 7 = 32 := by decide
  have a8 : arg crtState 8 = 20480 := by decide
  have a9 : arg crtState 9 = 32 := by decide
  have a10 : arg crtState 10 = 24576 := by decide
  have a11 : arg crtState 11 = 32 := by decide
  have a12 : arg crtState 12 = 28672 := by decide
  have a13 : arg crtState 13 = 32 := by decide
  have a14 : arg crtState 14 = 65536 := by decide
  have a15 : arg crtState 15 = 1056 := by decide
  have e : argAddr crtState 0 = 0x20004 := by decide
  have esp : crtState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Proof.Rsa.checkCrtKeyContract, Proof.Rsa.checkCrtKeySig, abi, argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, e, esp, crtState, Spec.Rsa.lenValid, Spec.Rsa.scratchWords] using crtState

def keyState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x20005 then 16
    else if a = 0x20008 then 64
    else if a = 0x2000d then 32
    else if a = 0x20010 then 3
    else if a = 0x20015 then 48
    else if a = 0x20018 then 64
    else if a = 0x2001d then 64
    else if a = 0x20020 then 32
    else if a = 0x20025 then 80
    else if a = 0x20028 then 32
    else if a = 0x2002d then 96
    else if a = 0x20030 then 32
    else if a = 0x20035 then 112
    else if a = 0x20038 then 32
    else if a = 0x2003d then 128
    else if a = 0x20040 then 32
    else if a = 0x20046 then 1
    else if a = 0x20048 then 32
    else if a = 0x20049 then 4 else 0
  rd := [⟨4096, 64⟩, ⟨8192, 3⟩, ⟨12288, 64⟩, ⟨16384, 32⟩, ⟨20480, 32⟩, ⟨24576, 32⟩, ⟨28672, 32⟩, ⟨32768, 32⟩]
  wr := [⟨0x10000, 8448⟩, ⟨0x20004, 72⟩]

theorem key_satisfiable : ∃ s, (Spec.Rsa.checkKeyContract abi 20).pre s := by
  have a0 : arg keyState 0 = 4096 := by decide
  have a1 : arg keyState 1 = 64 := by decide
  have a2 : arg keyState 2 = 8192 := by decide
  have a3 : arg keyState 3 = 3 := by decide
  have a4 : arg keyState 4 = 12288 := by decide
  have a5 : arg keyState 5 = 64 := by decide
  have a6 : arg keyState 6 = 16384 := by decide
  have a7 : arg keyState 7 = 32 := by decide
  have a8 : arg keyState 8 = 20480 := by decide
  have a9 : arg keyState 9 = 32 := by decide
  have a10 : arg keyState 10 = 24576 := by decide
  have a11 : arg keyState 11 = 32 := by decide
  have a12 : arg keyState 12 = 28672 := by decide
  have a13 : arg keyState 13 = 32 := by decide
  have a14 : arg keyState 14 = 32768 := by decide
  have a15 : arg keyState 15 = 32 := by decide
  have a16 : arg keyState 16 = 65536 := by decide
  have a17 : arg keyState 17 = 1056 := by decide
  have e : argAddr keyState 0 = 0x20004 := by decide
  have esp : keyState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, e, esp, keyState, Spec.Rsa.lenValid, Spec.Rsa.scratchWords] using keyState

theorem satisfiable (full : Bool) : ∃ s, (contract full).pre s := by
  cases full
  · exact crt_satisfiable
  · exact key_satisfiable

theorem verified (full : Bool) : Verified target (code full) (contract full) :=
  ⟨correct full, constantTime full, satisfiable full⟩

end VG.Proof.Rsa.X86.KeyCheck
