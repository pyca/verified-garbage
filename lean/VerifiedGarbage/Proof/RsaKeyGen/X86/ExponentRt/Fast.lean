module

public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveStack
public import VerifiedGarbage.Impl.Bignum.X86.PublicContext
public import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentRt
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words

import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.Pointer
import VerifiedGarbage.Proof.RsaKeyGen.X86.FilterStack
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Data.Nat.Prime.Basic
import VerifiedGarbage.Impl.RsaKeyGen.X86.FermatExponent
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialDivisor
import VerifiedGarbage.Proof.Mont.X86.Instr
/-! # The 65537 filter over the saved candidate minus one at a run-time width -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/FermatExponent.lean`, which only this module imported.
section

/-! # Coprimality for RSA's usual public exponent

65537 is prime, so a candidate minus one is coprime to it exactly when
its whole-word trial reduction is nonzero. This permits the normal exponent
to reuse the native trial kernel; other exponents need the general check.
-/

section
namespace VG.Proof.RsaKeyGen

theorem prime65537 : Nat.Prime 65537 := by
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

theorem coprime65537 (c : Nat) : Nat.gcd c 65537 = 1 ↔ c % 65537 ≠ 0 := by
  change Nat.Coprime c 65537 ↔ _
  rw [Nat.coprime_comm, prime65537.coprime_iff_not_dvd, Nat.dvd_iff_mod_eq_zero]

end VG.Proof.RsaKeyGen
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/FermatExponent.lean`, which only this module imported.
section

/-! # The usual RSA exponent needs one whole-word reduction and no general gcd -/

section
namespace VG.Proof.RsaKeyGen.X86.FermatExponent
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.FermatExponent

theorem xor_one {s : State} {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Upd s t .eax (s.gpr .eax ^^^ 1) → WP isa (.block is) t Q) :
    WP isa (.block (.alu .xor .eax (.imm 1) :: is)) s Q :=
  cons (by simp only [exec, execAlu, readSrc, Option.bind_some]; rfl)
    (k _ (Upd.flags _ _ _ _ _ _))

theorem code_ok (s : State) (p : BitVec 32) (w endOffset : Nat)
    (positive : 0 < w) (lengthBound : 4 * (2 * w) < 2 ^ 32) (fit : p.toNat + 4 * (2 * w) ≤ 2 ^ 32)
    (candidateRead : ∀ i < 2 * w, InRegions (s.rd ++ s.wr) (off (p.setWidth 64) (4 * i)) 4)
    (endRead : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) endOffset) 4)
    (endValue : s.mem.readW (addr (s.gpr .esp) endOffset) 32 = p + BitVec.ofNat 32 (4 * (2 * w)))
    (ptr : s.gpr .edi = p) :
    WP isa (code endOffset) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (decide (Nat.gcd (val32 s.mem (p.setWidth 64) 0 (2 * w)) 65537 = 1)).toNat ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s t := by
  unfold code init
  refine WP.seq (wp_movS rfl fun a A _ => wp_movS rfl fun b B _ => wp_movS rfl fun c C _ => WP.block_nil ?_)
  have K : Keeps [.ebx, .esi, .ebp] s c := ((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps
  have M : c.mem = s.mem := C.mem.trans (B.mem.trans A.mem)
  have prime : c.gpr .ebx = 65537#32 := by rw [C.other .ebx (by decide), B.other .ebx (by decide), A.gpr]; rfl
  have inv : c.gpr .esi = 65535#32 := by rw [C.other .esi (by decide), B.gpr]; rfl
  have sp : c.gpr .esp = s.gpr .esp := K.1 .esp (by decide)
  refine WP.seq (WP.mono (Trial.divisor_ok c p w endOffset positive lengthBound fit
    (by intro i index; rw [K.2.1, K.2.2]; exact candidateRead i index)
    (by rw [K.2.1, K.2.2, sp]; exact endRead)
    (by rw [M, sp]; exact endValue) ((K.1 .edi (by decide)).trans ptr) C.gpr
    (by rw [prime]; decide) (by rw [prime]; decide) (by rw [prime]; decide)
    (by rw [prime, inv]; decide +kernel)) fun d ⟨V, Md, Kd⟩ => ?_)
  have Kall : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s d := (K.mono (by decide)).widen Kd
  refine xor_one fun t T => WP.block_nil ?_
  refine ⟨?_, T.mem.trans (Md.trans M), Kall.widen T.keeps⟩
  rw [T.gpr, V, M, prime]
  change BitVec.ofNat 32 (decide (val32 s.mem (p.setWidth 64) 0 (2 * w) % 65537 = 0)).toNat ^^^ 1 = _
  have coprime := VG.Proof.RsaKeyGen.coprime65537 (val32 s.mem (p.setWidth 64) 0 (2 * w))
  by_cases divides : val32 s.mem (p.setWidth 64) 0 (2 * w) % 65537 = 0
  · rw [decide_eq_true divides, decide_eq_false (by omega : ¬ Nat.gcd (val32 s.mem (p.setWidth 64) 0 (2 * w)) 65537 = 1)]
    rfl
  · rw [decide_eq_false divides, decide_eq_true (coprime.mpr divides)]
    rfl

end VG.Proof.RsaKeyGen.X86.FermatExponent
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.Bignum.X86.PublicContext VG.Impl.RsaKeyGen.X86.ExponentRt

theorem val32_off (m : Mem) (base : Addr) (start d n : Nat) :
    val32 m (off base start) d n = val32 m base (start + d) n := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    simp only [val32, ih, w32, off, BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [Nat.add_assoc]

theorem fastArgs_ok {p : BitVec 32} {w : Nat} {s : State} {base : Addr} {size : Nat}
    (C : VG.Proof.RsaKeyGen.X86.Sieve.StackContext p s) (S : Scr s base size) (header : 8 ≤ size)
    (len : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w)) :
    WP isa (.block fastArgs) s fun t =>
      t.gpr .edi = s.gpr .edi + BitVec.ofNat 32 (slot w 5) ∧
      t.mem.readW (off (p.setWidth 64) 4) 32 = s.gpr .edi + BitVec.ofNat 32 (slot w 5) + BitVec.ofNat 32 (8 * w) ∧
      t.mem.readW (off (p.setWidth 64) 0) 32 = s.gpr .edi ∧
      Outside (p.setWidth 64) 0 8 s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .edi] s t := by
  unfold fastArgs
  refine savedPtr_ok S header len (by decide) (by decide) (by decide) fun a Ka Ma eaxA => ?_
  have Sa := S.of_keeps Ka (by decide)
  refine wp_movS (readSrc_sc Sa (by omega)) fun b B _ => ?_
  have Kb : Keeps [.eax, .ecx, .edx] s b := (Ka.mono (by decide)).trans (B.keeps.mono (by decide))
  have Cb := C.keep Kb (by decide)
  refine wp_storeS (Cb.address 0 (by decide)) (ws_write Cb.ws (by decide)) fun c D => ?_
  have Cc := Cb.keep (D.keeps []) (by decide)
  refine wp_movS rfl fun d E _ => wp_addS rfl fun e F _ => ?_
  have K : Keeps [.eax, .ecx, .edx, .edi] s e :=
    (((Kb.mono (by decide)).trans ((D.keeps []).mono (by decide))).trans (E.keeps.mono (by decide))).trans
      (F.keeps.mono (by decide))
  have Ce := C.keep K (by decide)
  refine wp_storeS (Ce.address 4 (by decide)) (ws_write Ce.ws (by decide)) fun t T => WP.block_nil ?_
  have ediS : b.gpr .edi = s.gpr .edi := Kb.1 .edi (by decide)
  have eaxD : d.gpr .eax = s.gpr .edi + BitVec.ofNat 32 (slot w 5) := by
    rw [E.other .eax (by decide), D.gpr, B.other .eax (by decide), eaxA]
  have value : e.gpr .eax = s.gpr .edi + BitVec.ofNat 32 (slot w 5) + BitVec.ofNat 32 (8 * w) := by
    rw [F.gpr, eaxD, F.other .ecx (by decide) |>.symm.trans (F.other .ecx (by decide)), E.other .ecx (by decide),
      D.gpr, B.gpr, Ma, len]
  have memE : e.mem = c.mem := F.mem.trans E.mem
  have Oc : Outside (p.setWidth 64) 0 4 s.mem c.mem := by
    rw [D.mem, B.mem, Ma]
    exact writeW32_outside _ _ _ (by decide)
  have Ot : Outside (p.setWidth 64) 4 4 c.mem t.mem := by
    rw [T.mem, memE]
    exact writeW32_outside _ _ _ (by decide)
  refine ⟨?_, ?_, ?_, (Oc.mono (by decide) (by decide)).trans (Ot.mono (by decide) (by decide)),
    K.widen (T.keeps [])⟩
  · rw [T.gpr, F.other .edi (by decide), E.gpr, D.gpr, B.other .eax (by decide), eaxA]
  · rw [T.mem, Mem.readW_writeW_self32, value]
  · rw [BitVec.eq_of_toNat_eq (Ot.w32 (d := 0) (by decide) (by decide)), D.mem, Mem.readW_writeW_self32, ediS]

theorem fast_ok {s : State} {base : Addr} {size w candidate : Nat}
    (S : Scr s base size) (width : 4 ≤ w) (widthBound : w ≤ 64)
    (space : slot w 5 + 8 * w ≤ size) (len : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w))
    (saved : val32 s.mem base (slot w 5) (2 * w) = candidate - 1)
    (fit : 40 ≤ (s.gpr .esp).toNat)
    (separate : (s.gpr .esp).toNat ≤ base.toNat ∨ base.toNat + size + 40 ≤ (s.gpr .esp).toNat) :
    WP isa fast s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (decide (Nat.gcd (candidate - 1) 65537 = 1)).toNat ∧
      Frame [below (s.gpr .esp) 20] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  let p := s.gpr .edi + BitVec.ofNat 32 (slot w 5)
  have slotBound : slot w 5 + 8 * w ≤ 2 ^ 32 := Nat.le_trans space (by have := S.nowrap; omega)
  have pbase : p.setWidth 64 = off base (slot w 5) := S.ea (d := slot w 5) (by omega)
  have pnat : p.toNat = base.toNat + slot w 5 := by
    change (s.gpr .edi + BitVec.ofNat 32 (slot w 5)).toNat = base.toNat + slot w 5
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, S.edi_toNat]
    rw [Nat.mod_eq_of_lt (a := slot w 5) (by omega),
      Nat.mod_eq_of_lt (by have := S.nowrap; omega)]
  have far : (⟨base, size⟩ : Region).Disjoint (below (s.gpr .esp) 20) :=
    VG.Proof.RsaKeyGen.X86.FilterStack.allocated_apart (by omega) S.nowrap
      (by rcases separate with h | h; exact Or.inl h; exact Or.inr (by omega))
  have sourceFar : (⟨p.setWidth 64, 8 * w⟩ : Region).Disjoint (below (s.gpr .esp) 20) := by
    apply Region.Disjoint.sub_left far
    intro x hx
    rw [pbase] at hx
    exact Offset.sub_base base space x hx
  have sourceRead : ∀ i < 2 * w, InRegions (s.rd ++ s.wr) (off (p.setWidth 64) (4 * i)) 4 := by
    intro i index
    rw [pbase]
    simpa only [off, BitVec.add_assoc, ← BitVec.ofNat_add] using S.read (d := slot w 5 + 4 * i) (n := 4) (by omega)
  unfold fast
  refine WP.frameAlloc (by decide) (by decide) (by decide) (by omega) (NoSp.of_all (by rfl)) ?_
  let initial := allocFrame 20 s
  have C : VG.Proof.RsaKeyGen.X86.Sieve.StackContext (s.gpr .esp - 20#32) initial :=
    VG.Proof.RsaKeyGen.X86.FilterStack.allocated_context (by omega)
  have Si : Scr initial base size := VG.Proof.RsaKeyGen.X86.FilterStack.allocated_scratch S (by omega)
    (by rcases separate with h | h; exact Or.inl h; exact Or.inr (by omega))
  refine WP.seq (WP.mono (fastArgs_ok (w := w) C Si (by omega) (by rw [allocFrame_mem]; exact len))
    fun a ⟨ptrA, endA, savedA, Oa, Ka⟩ => ?_)
  have ptr : a.gpr .edi = p := by rw [ptrA, allocFrame_gpr _ _ (by decide)]
  have Ca := C.keep Ka (by decide)
  have frameA : Frame [below (s.gpr .esp) 20] s.mem a.mem := by
    simpa only [allocFrame_mem, below, off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] using
      VG.Proof.Bignum.outside_frame (Oa.mono (o' := 0) (n' := 20) (by decide) (by decide)) (by decide)
  have value : val32 a.mem (p.setWidth 64) 0 (2 * w) = val32 s.mem (p.setWidth 64) 0 (2 * w) := by
    apply val32_congr
    intro i index
    exact congrArg BitVec.toNat (frameA.readW (r := ⟨p.setWidth 64, 8 * w⟩)
      (Offset.contains_base _ (by omega) (by omega))
      (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact sourceFar) (by decide))
  refine WP.seq (WP.mono (VG.Proof.RsaKeyGen.X86.FermatExponent.code_ok a p w 4 (by omega) (by omega)
    (by rw [pnat]; have := S.nowrap; omega)
    (by
      intro i index
      rw [Ka.2.1, Ka.2.2]
      obtain ⟨r, mem, contains⟩ := sourceRead i index
      refine ⟨r, ?_, contains⟩
      rcases List.mem_append.mp mem with mem | mem
      · exact List.mem_append_left _ mem
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ mem))
    (Ca.access 4 (by decide)) (by
      change a.mem.readW (a.ea (VG.Impl.RsaKeyGen.X86.Sieve.slot 4)) 32 = _
      rw [Ca.address 4 (by decide), endA, allocFrame_gpr _ _ (by decide)]
      rw [show 4 * (2 * w) = 8 * w by omega]) ptr) fun b ⟨result, Mb, Kb⟩ => ?_)
  have Cb := Ca.keep Kb (by decide)
  refine wp_movS (v := initial.gpr .edi) (by
    change readSrc b (.mem (VG.Impl.RsaKeyGen.X86.Sieve.slot 0)) = some (initial.gpr .edi)
    rw [Cb.read 0 (by decide), Mb, savedA]) fun t T _ => WP.block_nil ?_
  have Kall : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] initial t :=
    ((Ka.mono (by decide)).trans Kb).widen T.keeps
  have restored : t.gpr .edi = initial.gpr .edi := T.gpr
  have Kbody : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] initial t := by
    refine ⟨?_, Kall.2⟩
    intro r mem
    by_cases same : r = .edi
    · subst r; exact restored
    · exact Kall.1 r (by cases r <;> simp_all)
  refine ⟨?_, ?_, VG.Proof.RsaKeyGen.X86.FilterStack.freed_keeps Kbody (by decide)⟩
  · rw [freed_gpr _ _ (by decide), T.other .eax (by decide), result, value, pbase,
      val32_off, Nat.add_zero, saved]
  · rw [freed_mem, T.mem, Mb]
    exact frameA

end VG.Proof.RsaKeyGen.X86.ExponentRt
