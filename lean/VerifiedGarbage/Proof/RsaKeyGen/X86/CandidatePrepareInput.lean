module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinState
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Prepare
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareData
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Constants
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedContext
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedDataGap
import VerifiedGarbage.Proof.Mont.RangeCover
public import VerifiedGarbage.Impl.RsaKeyGen.X86.PrepareHeader
public import VerifiedGarbage.Impl.RsaKeyGen.X86.HeaderRt
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2State
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.RsaKeyGen.X86.Gcd64Words
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.Proof.MillerRabin.Contract
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.RsaKeyGen.X86.LowWord
import VerifiedGarbage.Proof.MillerRabin.X86.Context
public import VerifiedGarbage.Impl.RsaKeyGen.X86.InverseLift
public import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialWord
public import VerifiedGarbage.TCB.X86.Isa
import Mathlib.Data.Int.Basic
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Impl.RsaKeyGen.X86.MontInverse
import VerifiedGarbage.Proof.Mont.X86.Inverse
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Exponent
public import Init.Data.BitVec.Basic
public import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.RsaKeyGen.X86.HalfPass
import VerifiedGarbage.Proof.Mont.Halve32
import Init.Prelude
import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentShift
import VerifiedGarbage.Proof.RsaKeyGen.MrWindow
import VerifiedGarbage.Proof.RsaKeyGen.X86.SigMask
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentMarker
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Rsa.TwosMath
public import VerifiedGarbage.Impl.RsaKeyGen.X86.LowPair
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Impl.RsaKeyGen.X86.LowBit
import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64Subtract
import VerifiedGarbage.Proof.Mont.X86.ExponentWord
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Header
import VerifiedGarbage.Proof.Framework.Block

/-! ### `RsaKeyGen.X86.Header`, which only this module used -/

section

/-! # Complete initialization of the public prepared header -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/HeaderPointer.lean`, which only this module imported.
section

/-! # Initialize one public prepared-array pointer -/

section
namespace VG.Proof.RsaKeyGen.X86.Header
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Bignum.X86.PublicContext VG.Impl.RsaKeyGen.X86.Header

theorem pointer_ok {s : State} {base : Addr} {size w i : Nat}
    (scratch : Scr s base size) (fit : 64 + 8 * i + 8 ≤ size) (zero : s.gpr .edx = 0#32) :
    WP isa (.block (pointer w i)) s fun t =>
      t.mem = s.mem.writeW (off base (64 + 8 * i))
        (0#32 ++ (s.gpr .edi + BitVec.ofNat 32 (slot w i))) ∧
      Outside base (64 + 8 * i) 8 s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold pointer
  refine wp_movS rfl fun a A _ => wp_addS rfl fun b B _ => ?_
  have K : Keeps [.eax] s b := A.keeps.trans B.keeps
  have addr : 68 + 8 * i = 64 + 8 * i + 4 := by omega
  rw [addr]
  refine WP.mono (storePair_ok (scratch.of_keeps K (by decide)) fit) fun t ⟨M, O, Kt⟩ => ?_
  refine ⟨?_, ?_, K.widen Kt⟩
  · rw [M, B.mem, A.mem, K.1 .edx (by decide), zero, B.gpr, A.gpr]
  · rw [B.mem, A.mem] at O
    exact O

end VG.Proof.RsaKeyGen.X86.Header
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/HeaderPointers.lean`, which only this module imported.
section

/-! # Initialize all prepared pointers while retaining the public workspace base -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Header
open VG VG.X86 VG.Impl.Bignum.X86.PublicContext VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.Header

def pointerMemory (base : Addr) (p : BitVec 32) (w : Nat) (m : Mem) (i : Nat) : Mem :=
  m.writeW (off base (64 + 8 * i)) (0#32 ++ (p + BitVec.ofNat 32 (slot w i)))

theorem pointers_ok (indices : List Nat) {s : State} {base : Addr} {size w : Nat}
    (scratch : Scr s base size) (fit : ∀ i ∈ indices, 64 + 8 * i + 8 ≤ size)
    (zero : s.gpr .edx = 0#32) :
    WP isa (.block (indices.flatMap (pointer w))) s fun t =>
      t.mem = indices.foldl (pointerMemory base (s.gpr .edi) w) s.mem ∧ Keeps [.eax] s t := by
  induction indices generalizing s with
  | nil => exact WP.block_nil ⟨rfl, Keeps.refl _ _⟩
  | cons i indices ih =>
    rw [List.flatMap_cons]
    refine WP.block_append (WP.mono (pointer_ok scratch (fit i (by simp)) zero) fun a ⟨M, _, K⟩ => ?_)
    refine WP.mono (ih (scratch.of_keeps K (by decide))
      (fun j mem => fit j (List.mem_cons_of_mem _ mem)) ((K.1 .edx (by decide)).trans zero))
      fun t ⟨Mt, Kt⟩ => ?_
    refine ⟨?_, K.trans Kt⟩
    rw [Mt, K.1 .edi (by decide), M]
    rfl

end VG.Proof.RsaKeyGen.X86.Header
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Header
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Bignum.X86.PublicContext VG.Impl.RsaKeyGen.X86.Header

def headerMemory (base : Addr) (p : BitVec 32) (w : Nat) (m : Mem) : Mem :=
  (List.range 8).foldl (pointerMemory base p w)
    ((m.writeW (off base 48) (0#32 ++ BitVec.ofNat 32 w)).writeW
      (off base 224) (0#32 ++ BitVec.ofNat 32 (stride w)))

theorem code_ok {s : State} {base : Addr} {size w : Nat}
    (scratch : Scr s base size) (fit : 256 ≤ size) :
    WP isa (.block (code w)) s fun t =>
      t.mem = headerMemory base (s.gpr .edi) w s.mem ∧ Keeps [.eax, .edx] s t := by
  unfold code
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_movS rfl fun a A _ => ?_
  refine WP.block_append (WP.mono (literal_ok (scratch.of_keeps A.keeps (by decide)) (by omega_using [fit]) A.gpr)
    fun b ⟨Mb, _, Kb⟩ => ?_)
  have K : Keeps [.eax, .edx] s b := (A.keeps.mono (by decide)).widen Kb
  have zeroB : b.gpr .edx = 0#32 := (Kb.1 .edx (by decide)).trans A.gpr
  refine WP.block_append (WP.mono (literal_ok (scratch.of_keeps K (by decide)) (by omega_using [fit]) zeroB)
    fun c ⟨Mc, _, Kc⟩ => ?_)
  have K' : Keeps [.eax, .edx] s c := K.widen Kc
  have zeroC : c.gpr .edx = 0#32 := (Kc.1 .edx (by decide)).trans zeroB
  refine WP.mono (pointers_ok (List.range 8) (scratch.of_keeps K' (by decide))
    (fun i mem => by have := List.mem_range.mp mem; omega_using [fit, this]) zeroC) fun t ⟨Mt, Kt⟩ => ?_
  refine ⟨?_, K'.widen Kt⟩
  rw [Mt, K'.1 .edi (by decide), Mc, Mb, A.mem]
  rfl

end VG.Proof.RsaKeyGen.X86.Header

end

end

/-! ### `RsaKeyGen.X86.ExponentReady`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.LowPairScan`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.LowPairStep`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.LowPair`, which this module and modules that import it used -/

section

/-! # The paired low-word scan keeps its first nonzero value under masks -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.LowPair
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.LowPair

theorem mask_pair (lo hi : BitVec 32) :
    cmask (decide ((lo ||| hi).toNat < 1)) = if lo = 0#32 ∧ hi = 0#32 then BitVec.allOnes 32 else 0#32 := by
  have zero : (lo ||| hi).toNat < 1 ↔ lo = 0#32 ∧ hi = 0#32 := by
    rw [show (lo ||| hi).toNat < 1 ↔ (lo ||| hi).toNat = 0 by omega_using [],
      show (lo ||| hi).toNat = 0 ↔ lo ||| hi = 0#32 from @BitVec.toNat_inj 32 (lo ||| hi) (0#32), BitVec.or_eq_zero_iff]
  rw [show decide ((lo ||| hi).toNat < 1) = decide (lo = 0#32 ∧ hi = 0#32) from decide_eq_decide.mpr zero]
  by_cases h : lo = 0#32 ∧ hi = 0#32 <;> simp [cmask, h]

theorem choose_ok (s : State) :
    WP isa (.block choose) s fun t =>
      (t.gpr .ebx, t.gpr .esi) =
        (if s.gpr .ebx = 0#32 ∧ s.gpr .esi = 0#32 then (s.gpr .eax, s.gpr .ecx) else (s.gpr .ebx, s.gpr .esi)) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ecx, .edx, .ebx, .esi] s t := by
  unfold choose
  refine wp_movS rfl fun a A _ => wp_orS rfl fun b B => wp_cmpi fun c C cf _ => ?_
  refine wp_sbb_self cf fun d D => wp_and fun e E => wp_and fun f F => wp_orS rfl fun g G =>
    wp_orS rfl fun t T => WP.block_nil ?_
  have K : Keeps [.eax, .ecx, .edx, .ebx, .esi] s t :=
    (((((((A.keeps.mono (by decide)).widen B.keeps).trans (C.keeps _)).widen D.keeps).widen E.keeps).widen
      F.keeps).widen G.keeps).widen T.keeps
  have mask : d.gpr .edx = if s.gpr .ebx = 0#32 ∧ s.gpr .esi = 0#32 then BitVec.allOnes 32 else 0#32 := by
    rw [D.gpr, B.gpr, A.gpr, A.other .esi (by decide)]
    exact mask_pair _ _
  have low : t.gpr .ebx = s.gpr .ebx ||| (s.gpr .eax &&& d.gpr .edx) := by
    rw [T.other .ebx (by decide), G.gpr, F.other .ebx (by decide), E.other .ebx (by decide),
      D.other .ebx (by decide), C.gpr, B.other .ebx (by decide), A.other .ebx (by decide),
      F.other .eax (by decide), E.gpr, D.other .eax (by decide), C.gpr,
      B.other .eax (by decide), A.other .eax (by decide)]
  have high : t.gpr .esi = s.gpr .esi ||| (s.gpr .ecx &&& d.gpr .edx) := by
    rw [T.gpr, G.other .esi (by decide), F.other .esi (by decide), E.other .esi (by decide),
      D.other .esi (by decide), C.gpr, B.other .esi (by decide), A.other .esi (by decide),
      G.other .ecx (by decide), F.gpr, E.other .ecx (by decide), D.other .ecx (by decide),
      C.gpr, B.other .ecx (by decide), A.other .ecx (by decide), E.other .edx (by decide)]
  refine ⟨?_, ?_, K⟩
  · rw [low, high, mask]
    by_cases h : s.gpr .ebx = 0#32 ∧ s.gpr .esi = 0#32
    · simp only [ite_eq_left h]
      rw [BitVec.and_allOnes, BitVec.and_allOnes, h.1, h.2, BitVec.zero_or, BitVec.zero_or]
    · simp only [ite_eq_right h, BitVec.and_zero, BitVec.or_zero]
  · rw [T.mem, G.mem, F.mem, E.mem, D.mem, C.mem, B.mem, A.mem]

end VG.Proof.RsaKeyGen.X86.LowPair

end

end

/-! # Each public scan position reads one native pair, without modifying memory -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.LowPair
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.LowPair

def pairAt (m : Mem) (base : Addr) (offset : Nat) : BitVec 32 × BitVec 32 :=
  (m.readW (VG.Proof.Mont.off base offset) 32, m.readW (VG.Proof.Mont.off base (offset + 4)) 32)

def select (before next : BitVec 32 × BitVec 32) : BitVec 32 × BitVec 32 :=
  if before.1 = 0#32 ∧ before.2 = 0#32 then next else before

theorem step_ok {s : State} {base : Addr} {size src index : Nat} (scratch : Scr s base size)
    (fit : src + 8 * index + 8 ≤ size) :
    WP isa (.block (step src index)) s fun t =>
      (t.gpr .ebx, t.gpr .esi) = select (s.gpr .ebx, s.gpr .esi) (pairAt s.mem base (src + 8 * index)) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ecx, .edx, .ebx, .esi] s t := by
  unfold step
  refine WP.block_append (wp_movS (readSrc_sc scratch (by omega_using [fit])) fun a A _ =>
    wp_movS (readSrc_sc (scratch.of_keeps A.keeps (by decide)) (by omega_using [fit])) fun b B _ => WP.block_nil ?_)
  have K : Keeps [.eax, .ecx] s b := (A.keeps.mono (by decide)).widen B.keeps
  have M : b.mem = s.mem := B.mem.trans A.mem
  refine WP.mono (choose_ok b) fun t ⟨V, Mt, Kt⟩ => ?_
  rw [K.1 .ebx (by decide), K.1 .esi (by decide), B.gpr, B.other .eax (by decide), A.gpr, A.mem] at V
  exact ⟨V, Mt.trans M, (K.mono (by decide)).trans Kt⟩

end VG.Proof.RsaKeyGen.X86.LowPair

end

end

/-! # The fixed paired-word scan returns the first nonzero word -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.LowPair
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.LowPair

def first (m : Mem) (base : Addr) (src : Nat) :
    (BitVec 32 × BitVec 32) → Nat → Nat → BitVec 32 × BitVec 32
  | before, _, 0 => before
  | before, start, count + 1 => first m base src (select before (pairAt m base (src + 8 * start))) (start + 1) count

theorem steps_ok {s : State} {base : Addr} {size src start count : Nat} (scratch : Scr s base size)
    (fit : src + 8 * (start + count) ≤ size) :
    WP isa (steps src start count) s fun t =>
      (t.gpr .ebx, t.gpr .esi) = first s.mem base src (s.gpr .ebx, s.gpr .esi) start count ∧
      t.mem = s.mem ∧ Keeps [.eax, .ecx, .edx, .ebx, .esi] s t := by
  induction count generalizing s start with
  | zero => exact WP.block_nil ⟨rfl, rfl, Keeps.refl _ _⟩
  | succ count ih =>
    refine WP.seq (WP.mono (step_ok scratch (by omega_using [fit])) fun a ⟨V, M, K⟩ => ?_)
    refine WP.mono (ih (scratch.of_keeps K (by decide)) (by omega_using [fit])) fun t ⟨Vt, Mt, Kt⟩ => ?_
    exact ⟨by rw [Vt, M, V]; rfl, Mt.trans M, K.trans Kt⟩

theorem scan_ok {s : State} {base : Addr} {size src count : Nat} (scratch : Scr s base size)
    (fit : src + 8 * count ≤ size) :
    WP isa (scan src count) s fun t =>
      (t.gpr .ebx, t.gpr .esi) = first s.mem base src (0#32, 0#32) 0 count ∧
      t.mem = s.mem ∧ Keeps [.eax, .ecx, .edx, .ebx, .esi] s t := by
  refine WP.seq (wp_movS rfl fun a A _ => wp_movS rfl fun b B _ => WP.block_nil ?_)
  have K : Keeps [.ebx, .esi] s b := (A.keeps.mono (by decide)).widen B.keeps
  refine WP.mono (steps_ok (scratch.of_keeps K (by decide)) (by omega_using [fit])) fun t ⟨V, M, Kt⟩ => ?_
  rw [B.mem, A.mem, B.gpr, B.other .ebx (by decide), A.gpr] at V
  exact ⟨V, M.trans (B.mem.trans A.mem), (K.mono (by decide)).trans Kt⟩

end VG.Proof.RsaKeyGen.X86.LowPair

end

end

/-! ### `RsaKeyGen.X86.HalfPassWord`, which this module and modules that import it used -/

section

/-! # One exponent word is halved or retained under the secret mask -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.HalfPass
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.HalfPass

theorem select_word (old shifted : BitVec 32) (choice : Bool) :
    old ^^^ ((shifted ^^^ old) &&& cmask choice) = if choice then shifted else old := by
  cases choice
  · rw [show cmask false = 0#32 from rfl, BitVec.and_zero, BitVec.xor_zero]
    rfl
  · rw [show cmask true = BitVec.allOnes 32 from rfl, BitVec.and_allOnes, BitVec.xor_comm shifted old,
      ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    rfl

theorem step_ok {s : State} {base : Addr} {size src out index : Nat} (scratch : Scr s base size)
    (pointer : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * index))
    (srcFit : src + 4 * index + 8 ≤ size) (outFit : out + 4 * index + 4 ≤ size)
    {choice : Bool} (mask : s.gpr .ecx = cmask choice) :
    WP isa (.block (step src out)) s fun t =>
      Outside base (out + 4 * index) 4 s.mem t.mem ∧
      w32 t.mem base (out + 4 * index) =
        (if choice then w32 s.mem base (src + 4 * index) / 2 +
          2 ^ 31 * (w32 s.mem base (src + 4 * index + 4) % 2) else w32 s.mem base (src + 4 * index)) ∧
      Keeps [.eax, .ebx, .edx] s t := by
  unfold step
  refine wp_movS (readSrc_at' scratch pointer (by omega_using [srcFit])) fun a A _ =>
    wp_logicS (.inl rfl) rfl fun b B => wp_ror (by decide) fun c C => ?_
  have Kc : Keeps [.eax, .ebx, .edx] s c := ((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps
  have pc : c.gpr .ebp = c.gpr .edi + BitVec.ofNat 32 (4 * index) := by
    rw [Kc.1 .ebp (by decide), Kc.1 .edi (by decide)]; exact pointer
  refine wp_movS (readSrc_at' (scratch.of_keeps Kc (by decide)) pc (by omega_using [srcFit])) fun d D _ =>
    wp_shr (by decide) fun e E _ => wp_addS rfl fun f F _ => ?_
  have Kf : Keeps [.eax, .ebx, .edx] s f := ((Kc.widen D.keeps).widen E.keeps).widen F.keeps
  have pf : f.gpr .ebp = f.gpr .edi + BitVec.ofNat 32 (4 * index) := by
    rw [Kf.1 .ebp (by decide), Kf.1 .edi (by decide)]; exact pointer
  refine wp_movS (readSrc_at' (scratch.of_keeps Kf (by decide)) pf (by omega_using [srcFit])) fun g G _ =>
    wp_xor fun h H => wp_and fun i I => wp_xor fun j J => ?_
  have Kj : Keeps [.eax, .ebx, .edx] s j := (((Kf.widen G.keeps).widen H.keeps).widen I.keeps).widen J.keeps
  have pj : j.gpr .ebp = j.gpr .edi + BitVec.ofNat 32 (4 * index) := by
    rw [Kj.1 .ebp (by decide), Kj.1 .edi (by decide)]; exact pointer
  have Sj := scratch.of_keeps Kj (by decide)
  refine wp_storeS (Sj.ea_at' pj (by omega_using [outFit])) (Sj.write outFit) fun t T => WP.block_nil ?_
  have M : j.mem = s.mem := J.mem.trans (I.mem.trans (H.mem.trans (G.mem.trans
    (F.mem.trans (E.mem.trans (D.mem.trans (C.mem.trans (B.mem.trans A.mem))))))))
  have old : g.gpr .ebx = s.mem.readW (off base (src + 4 * index)) 32 := by
    rw [G.gpr, F.mem, E.mem, D.mem, C.mem, B.mem, A.mem]
  have half : f.gpr .edx = (s.mem.readW (off base (src + 4 * index)) 32 >>> 1) +
      (s.mem.readW (off base (src + 4 * index + 4)) 32 &&& 1).rotateRight 1 := by
    rw [F.gpr, E.gpr, D.gpr, E.other .eax (by decide), D.other .eax (by decide), C.gpr, B.gpr, A.gpr,
      C.mem, B.mem, A.mem]
    rw [show src + 4 + 4 * index = src + 4 * index + 4 by omega_using []]
    rfl
  have selected : j.gpr .ebx = if choice then f.gpr .edx else g.gpr .ebx := by
    rw [J.gpr, I.other .ebx (by decide), H.other .ebx (by decide), I.gpr, H.gpr,
      G.other .edx (by decide), H.other .ecx (by decide),
      G.other .ecx (by decide), Kf.1 .ecx (by decide), mask, select_word]
  refine ⟨?_, ?_, Kj.widen (T.keeps [])⟩
  · rw [T.mem, M]
    exact writeW32_outside _ _ _ (by have := scratch.nowrap; omega_using [outFit, this])
  · rw [T.mem, w32_write_self, selected, old, half]
    cases choice
    · rfl
    · exact VG.Proof.Mont.X86.Dynamic.shifted_word _ _

end VG.Proof.RsaKeyGen.X86.HalfPass

end

end

/-! ### `RsaKeyGen.X86.ExponentMarker`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.LowBit`, which this module and modules that import it used -/

section

/-! # Native subtraction and masking isolate the paired word's lowest set bit -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/NegPair.lean`, which only this module imported.
section

/-! # Native subtraction through the borrow forms the negation of a 64-bit pair -/

section
namespace VG.Proof.RsaKeyGen.X86.LowBit
open VG VG.Proof.Mont.X86

theorem neg_pair (lo hi : BitVec 32) :
    (0#32 - hi - (BitVec.ofBool (decide (0 < lo.toNat))).setWidth 32) ++ (0#32 - lo) = -(hi ++ lo) := by
  let borrow := decide (0 < lo.toNat)
  let carry := decide (0 < hi.toNat + borrow.toNat)
  have L := Mod64.sub_rel (0#32) lo
  have H := sbb_rel (0#32) hi borrow
  simp only [BitVec.toNat_zero, Nat.zero_add] at L H
  change (0#32 - lo).toNat + lo.toNat = 2 ^ 32 * borrow.toNat at L
  change (0#32 - hi - (BitVec.ofBool borrow).setWidth 32).toNat + hi.toNat + borrow.toNat =
    2 ^ 32 * carry.toNat at H
  have paired : ((0#32 - hi - (BitVec.ofBool borrow).setWidth 32) ++ (0#32 - lo)).toNat +
      (hi ++ lo).toNat = 2 ^ 64 * carry.toNat := by
    rw [Gcd64.append_pair, Gcd64.append_pair]
    unfold Mod64.pair
    omega
  have outputBound := ((0#32 - hi - (BitVec.ofBool borrow).setWidth 32) ++ (0#32 - lo)).isLt
  have inputBound := (hi ++ lo).isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_neg]
  change ((0#32 - hi - (BitVec.ofBool borrow).setWidth 32) ++ (0#32 - lo)).toNat = _
  cases C : carry <;> rw [C] at paired <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one] at paired <;> omega

end VG.Proof.RsaKeyGen.X86.LowBit
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.LowBit
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.LowBit

theorem code_ok (s : State) :
    WP isa (.block code) s fun t =>
      t.gpr .edx ++ t.gpr .eax = (s.gpr .esi ++ s.gpr .ebx) &&& -(s.gpr .esi ++ s.gpr .ebx) ∧
      t.mem = s.mem ∧ Keeps [.eax, .edx] s t := by
  unfold code
  refine wp_movS rfl fun a A _ => wp_subS rfl fun b B cfB => wp_movS rfl fun c C cfC => ?_
  refine wp_sbbS rfl (cfC.trans cfB) fun d D _ => wp_and fun e E => wp_and fun t T => WP.block_nil ?_
  have low : t.gpr .eax = (0#32 - s.gpr .ebx) &&& s.gpr .ebx := by
    rw [T.other .eax (by decide), E.gpr, D.other .eax (by decide), C.other .eax (by decide),
      B.gpr, A.gpr, A.other .ebx (by decide), D.other .ebx (by decide), C.other .ebx (by decide),
      B.other .ebx (by decide), A.other .ebx (by decide)]
    rfl
  have high : t.gpr .edx = (0#32 - s.gpr .esi - (BitVec.ofBool (decide (0 < (s.gpr .ebx).toNat))).setWidth 32)
      &&& s.gpr .esi := by
    rw [T.gpr, E.other .edx (by decide), D.gpr, C.gpr, C.other .esi (by decide), B.other .esi (by decide),
      A.other .esi (by decide), A.gpr, A.other .ebx (by decide),
      E.other .esi (by decide), D.other .esi (by decide), C.other .esi (by decide), B.other .esi (by decide),
      A.other .esi (by decide)]
    rfl
  refine ⟨?_, ?_, (((((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps).widen D.keeps).widen E.keeps).widen T.keeps⟩
  · rw [low, high, ← BitVec.and_append, neg_pair, BitVec.and_comm]
  · rw [T.mem, E.mem, D.mem, C.mem, B.mem, A.mem]

end VG.Proof.RsaKeyGen.X86.LowBit

end

end

/-! ### `RsaKeyGen.X86.LowPairTwos`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.LowPairFirst`, which only this module used -/

section

/-! # The paired scan retains exactly the first nonzero source word -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.LowPair
open VG

theorem first_keep (m : Mem) (base : Addr) (src start count : Nat) (before : BitVec 32 × BitVec 32)
    (nonzero : ¬(before.1 = 0#32 ∧ before.2 = 0#32)) : first m base src before start count = before := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    unfold first select
    rw [ite_eq_right nonzero]
    exact ih (start + 1)

theorem first_hit (m : Mem) (base : Addr) (src start count index : Nat)
    (lo : start ≤ index) (hi : index < start + count)
    (below : ∀ j, start ≤ j → j < index → pairAt m base (src + 8 * j) = (0#32, 0#32))
    (hit : pairAt m base (src + 8 * index) ≠ (0#32, 0#32)) :
    first m base src (0#32, 0#32) start count = pairAt m base (src + 8 * index) := by
  induction count generalizing start with
  | zero => omega
  | succ count ih =>
    change first m base src (pairAt m base (src + 8 * start)) (start + 1) count = _
    by_cases same : start = index
    · subst start
      exact first_keep m base src (index + 1) count _ (fun ⟨a, b⟩ => hit (Prod.ext a b))
    · rw [below start (Nat.le_refl _) (by omega_using [lo, same])]
      exact ih (start + 1) (by omega_using [lo, same]) (by omega_using [hi]) (fun j hj lt => below j (by omega_using [hj]) lt)

end VG.Proof.RsaKeyGen.X86.LowPair

end

end

/-! # The native pair scan finds the word containing the exponent's lowest set bit -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/LowPairWord.lean`, which only this module imported.
section

/-! # Native halves read by the masked scan form the original 64-bit word -/

section
namespace VG.Proof.RsaKeyGen.X86.LowPair
open VG VG.Proof.Mont

theorem pairAt_word (m : Mem) (base : Addr) (src : Nat) :
    (pairAt m base src).2 ++ (pairAt m base src).1 = word m base src := by
  rw [word, VG.Proof.Rc2.Word32.read64_pair, VG.Offset.add_add]
  rfl

theorem pairAt_zero_iff (m : Mem) (base : Addr) (src : Nat) :
    pairAt m base src = (0#32, 0#32) ↔ word m base src = 0#64 := by
  constructor
  · intro h
    rw [← pairAt_word, h]
    rfl
  · intro h
    have value := congrArg BitVec.toNat h
    rw [word_eq_w32] at value
    change w32 m base src + 2 ^ 32 * w32 m base (src + 4) = 0 at value
    have low : w32 m base src = 0 := by omega
    have high : w32 m base (src + 4) = 0 := by omega
    exact Prod.ext (BitVec.eq_of_toNat_eq low) (BitVec.eq_of_toNat_eq high)

end VG.Proof.RsaKeyGen.X86.LowPair
end

end

-- Formerly `VerifiedGarbage/Proof/Mont/Digits64.lean`, which only this module imported.
section

/-! # A native paired word is a base-2⁶⁴ digit of its integer -/

section
namespace VG.Proof.Mont
open VG

theorem word_digit64 (m : Mem) (base : Addr) (src n index : Nat) (bound : index < n) :
    (word m base (src + 8 * index)).toNat = wordsVal m base src n / 2 ^ (64 * index) % 2 ^ 64 := by
  have bridge : ∀ k, wordsVal m base src k = VG.Proof.Bignum.wv m base src k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [wordsVal_succ_top, VG.Proof.Bignum.wv, ih]
  rw [bridge]
  exact VG.Proof.Bignum.word_of_wv m base src n bound

end VG.Proof.Mont
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.LowPair
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.LowPair

/-- The first nonzero pair of `count` pairs whose value is `N > 0` is the
64-bit word holding `N`'s lowest set bit. -/
theorem first_twos {m : Mem} {base : Addr} {src count N : Nat}
    (value : val32 m base src (2 * count) = N) (positive : 0 < N) :
    ((first m base src (0#32, 0#32) 0 count).2 ++ (first m base src (0#32, 0#32) 0 count).1).toNat =
      N / 2 ^ (64 * ((Spec.Rsa.splitTwos N).1 / 64)) % 2 ^ 64 := by
  obtain ⟨factor, odd⟩ := VG.Proof.Rsa.splitTwos_spec positive
  rw [Nat.mul_comm] at factor
  let a := (Spec.Rsa.splitTwos N).1
  obtain ⟨zero, bit, lower⟩ := VG.Proof.RsaKeyGen.lowWord_bits factor odd
  have bound : a < 64 * count := by
    have small : N < 2 ^ (64 * count) := by
      rw [← value, ← wordsVal_eq_val32]
      exact wordsVal_lt _ _ _ _
    by_cases h : a < 64 * count
    · exact h
    · have pow := Nat.pow_le_pow_right (n := 2) (by decide) (show 64 * count ≤ a by omega_using [h])
      have mul := Nat.le_mul_of_pos_left (2 ^ a) (show 0 < (Spec.Rsa.splitTwos N).2 by omega_using [odd])
      rw [← factor] at mul
      omega
  have digit {j : Nat} (index : j < count) :
      (word m base (src + 8 * j)).toNat = N / 2 ^ (64 * j) % 2 ^ 64 := by
    rw [word_digit64 _ _ _ _ _ index, wordsVal_eq_val32, value]
  have below (j : Nat) (_ : 0 ≤ j) (hj : j < a / 64) :
      pairAt m base (src + 8 * j) = (0#32, 0#32) := by
    apply (pairAt_zero_iff _ _ _).mpr
    apply BitVec.eq_of_toNat_eq
    rw [digit (by omega_using [bound, hj]), zero j hj]
    rfl
  have hit : pairAt m base (src + 8 * (a / 64)) ≠ (0#32, 0#32) := by
    intro h
    have empty := congrArg BitVec.toNat ((pairAt_zero_iff _ _ _).mp h)
    rw [digit (by omega_using [bound])] at empty
    have notZero : N / 2 ^ (64 * (a / 64)) % 2 ^ 64 ≠ 0 := by
      intro h
      rw [h, Nat.zero_testBit] at bit
      contradiction
    exact notZero empty
  rw [first_hit m base src 0 count (a / 64) (by omega_using []) (by omega_using [bound]) below hit, pairAt_word, digit (by omega_using [bound])]

theorem scan_twos {s : State} {base : Addr} {size src count N : Nat} (scratch : Scr s base size)
    (fit : src + 8 * count ≤ size) (value : val32 s.mem base src (2 * count) = N) (positive : 0 < N) :
    WP isa (scan src count) s fun t =>
      (t.gpr .esi ++ t.gpr .ebx).toNat = N / 2 ^ (64 * ((Spec.Rsa.splitTwos N).1 / 64)) % 2 ^ 64 ∧
      t.mem = s.mem ∧ Keeps [.eax, .ecx, .edx, .ebx, .esi] s t := by
  refine WP.mono (scan_ok scratch fit) fun t ⟨V, M, K⟩ => ?_
  have pair := congrArg (fun p : BitVec 32 × BitVec 32 => p.2 ++ p.1) V
  dsimp only at pair
  exact ⟨by rw [pair]; exact first_twos value positive, M, K⟩

end VG.Proof.RsaKeyGen.X86.LowPair

end

end

/-! # The native alignment marker is exactly 2^(v2(N) mod 64) -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentMarker
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.ExponentMarker

/-- `LowBit` on the 64-bit word holding `N`'s lowest set bit, in `esi:ebx`. -/
theorem lowBit_marker {a : State} {N : Nat} (positive : 0 < N)
    (selectedWord : (a.gpr .esi ++ a.gpr .ebx).toNat = N / 2 ^ (64 * ((Spec.Rsa.splitTwos N).1 / 64)) % 2 ^ 64) :
    WP isa (.block VG.Impl.RsaKeyGen.X86.LowBit.code) a fun t =>
      t.gpr .edx ++ t.gpr .eax = BitVec.twoPow 64 ((Spec.Rsa.splitTwos N).1 % 64) ∧
      t.mem = a.mem ∧ Keeps [.eax, .edx] a t := by
  refine WP.mono (LowBit.code_ok a) fun t ⟨marker, Mt, Kt⟩ => ?_
  obtain ⟨factor, odd⟩ := VG.Proof.Rsa.splitTwos_spec positive
  rw [Nat.mul_comm] at factor
  obtain ⟨_, bit, below⟩ := VG.Proof.RsaKeyGen.lowWord_bits factor odd
  have setBit : (a.gpr .esi ++ a.gpr .ebx).getLsbD ((Spec.Rsa.splitTwos N).1 % 64) = true := by
    change (a.gpr .esi ++ a.gpr .ebx).toNat.testBit _ = true
    rw [selectedWord]
    exact bit
  have clearBit (j : Nat) (lt : j < (Spec.Rsa.splitTwos N).1 % 64) :
      (a.gpr .esi ++ a.gpr .ebx).getLsbD j = false := by
    change (a.gpr .esi ++ a.gpr .ebx).toNat.testBit j = false
    rw [selectedWord]
    exact below j lt
  exact ⟨marker.trans (VG.Proof.RsaKeyGen.and_neg_eq_twoPow (Nat.mod_lt _ (by decide)) setBit clearBit), Mt, Kt⟩

theorem code_ok {s : State} {base : Addr} {size src count N : Nat} (scratch : Scr s base size)
    (fit : src + 8 * count ≤ size) (value : val32 s.mem base src (2 * count) = N) (positive : 0 < N) :
    WP isa (code src count) s fun t =>
      t.gpr .edx ++ t.gpr .eax = BitVec.twoPow 64 ((Spec.Rsa.splitTwos N).1 % 64) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ecx, .edx, .ebx, .esi] s t := by
  refine WP.seq (WP.mono (LowPair.scan_twos scratch fit value positive) fun a ⟨selectedWord, M, K⟩ => ?_)
  refine WP.mono (lowBit_marker positive selectedWord) fun t ⟨marker, Mt, Kt⟩ => ?_
  exact ⟨marker, Mt.trans M, K.widen Kt⟩

end VG.Proof.RsaKeyGen.X86.ExponentMarker

end

end

/-! ### `RsaKeyGen.X86.Exponent`, which only this module used -/

section

/-! ### `RsaKeyGen.X86.HalfPassLoop`, which only this module used -/

section

/-! # A single masked pass halves or retains the complete native exponent -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.HalfPass
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.HalfPass

theorem code_ok {s : State} {base : Addr} {size n src out : Nat} (scratch : Scr s base size)
    (positive : 0 < n) (srcFit : src + 4 * (n + 1) ≤ size) (outFit : out + 4 * n ≤ size)
    (sep : src = out ∨ src + 4 * (n + 1) ≤ out ∨ out + 4 * n ≤ src)
    (top : w32 s.mem base (src + 4 * n) = 0)
    {choice : Bool} (mask : s.gpr .ecx = cmask choice) :
    WP isa (code n src out) s fun t =>
      Outside base out (4 * n) s.mem t.mem ∧
      val32 t.mem base out n = (if choice then val32 s.mem base src n / 2 else val32 s.mem base src n) ∧
      Keeps [.eax, .ebx, .edx, .ebp] s t := by
  let P (j : Nat) (t : State) : Prop :=
    Keeps [.eax, .ebx, .edx, .ebp] s t ∧ Outside base out (4 * j) s.mem t.mem ∧
    ∀ i < j, w32 t.mem base (out + 4 * i) =
      if choice then w32 s.mem base (src + 4 * i) / 2 +
        2 ^ 31 * (w32 s.mem base (src + 4 * i + 4) % 2) else w32 s.mem base (src + 4 * i)
  refine wordLoop_ok P positive (by have := scratch.size_lt; omega_using [srcFit, this])
    (fun j t u ⟨K, O, V⟩ ⟨M, rd, wr, regs⟩ =>
      ⟨⟨fun r hr => (regs r (by simp_all) (by simp_all)).trans (K.1 r hr), rd.trans K.2.1, wr.trans K.2.2⟩,
        M ▸ O, M ▸ V⟩)
    ⟨Keeps.refl _ _, Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩ ?_ ?_
  · intro j hj t ⟨K, O, V⟩ pointer
    have St := scratch.of_keeps K (by decide)
    refine WP.mono (step_ok (choice := choice) St pointer (by omega_using [srcFit, hj]) (by omega_using [outFit, hj]) (by rw [K.1 .ecx (by decide)]; exact mask))
      fun u ⟨Ou, value, Ku⟩ => ?_
    have sameLo : w32 t.mem base (src + 4 * j) = w32 s.mem base (src + 4 * j) :=
      O.w32 (by rcases sep with h | h | h <;> omega_arith) (by have := scratch.nowrap; omega_using [srcFit, hj, this])
    have sameHi : w32 t.mem base (src + 4 * j + 4) = w32 s.mem base (src + 4 * j + 4) :=
      O.w32 (by rcases sep with h | h | h <;> omega_arith) (by have := scratch.nowrap; omega_using [srcFit, hj, this])
    refine ⟨⟨K.widen Ku, (O.mono (by omega_using []) (by omega_using [])).trans (Ou.mono (by omega_using []) (by omega_using [])), ?_⟩,
      Ku.1 .ebp (by decide), Ku.1 .edi (by decide)⟩
    intro i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with before | rfl
    · rw [Ou.w32 (by omega_using [before]) (by have := scratch.nowrap; omega_using [outFit, hj, hi, this])]
      exact V i before
    · rw [value, sameLo, sameHi]
  · intro t ⟨K, O, V⟩
    refine ⟨O, ?_, K⟩
    cases choice
    · exact val32_congr_at s.mem t.mem base n src out V
    · apply val32_halve_at s.mem t.mem base n src out
      intro i hi
      rw [V i hi, show src + 4 * i + 4 = src + 4 * (i + 1) by omega_using []]
      by_cases last : i + 1 = n
      · rw [ite_eq_left last, last, top]
        rfl
      · rw [ite_eq_right last]
        rfl

end VG.Proof.RsaKeyGen.X86.HalfPass

end

end

/-! # Complete native exponent and alignment-marker preparation -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/ExponentClear.lean`, which only this module imported.
section

/-! # Zero top sentinels supply the incoming bits for fixed masked halving -/

section
namespace VG.Proof.RsaKeyGen.X86.Exponent
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Exponent

theorem clearTops_ok {s : State} {base : Addr} {size n src out : Nat} (scratch : Scr s base size)
    (srcFit : src + 4 * (n + 1) ≤ size) (outFit : out + 4 * (n + 1) ≤ size)
    (sep : src + 4 * (n + 1) ≤ out) :
    WP isa (.block (clearTops n src out)) s fun t =>
      w32 t.mem base (src + 4 * n) = 0 ∧ w32 t.mem base (out + 4 * n) = 0 ∧
      t.gpr .ecx = cmask true ∧
      Outs base [(src + 4 * n, 4), (out + 4 * n, 4)] s.mem t.mem ∧ Keeps [.eax, .ecx] s t := by
  unfold clearTops
  refine wp_movS rfl fun a A _ => ?_
  have Sa := scratch.of_keeps A.keeps (by decide)
  refine wp_storeS (Sa.ea (by omega)) (Sa.write (by omega)) fun b B => ?_
  have Kb : Keeps [.eax] s b := A.keeps.widen (B.keeps [])
  have Sb := scratch.of_keeps Kb (by decide)
  refine wp_storeS (Sb.ea (by omega)) (Sb.write (by omega)) fun c C => wp_movS rfl fun t T _ => WP.block_nil ?_
  have Mb : b.mem = s.mem.writeW (off base (src + 4 * n)) (0#32) := by
    rw [B.mem, A.mem, A.gpr]
    rfl
  have Mc : c.mem = b.mem.writeW (off base (out + 4 * n)) (0#32) := by
    rw [C.mem, (B.keeps []).1 .eax (by decide), A.gpr]
    rfl
  have Os : Outside base (src + 4 * n) 4 s.mem b.mem := by
    rw [Mb]
    exact writeW32_outside _ _ _ (by have := scratch.nowrap; omega)
  have Oo : Outside base (out + 4 * n) 4 b.mem c.mem := by
    rw [Mc]
    exact writeW32_outside _ _ _ (by have := scratch.nowrap; omega)
  refine ⟨?_, ?_, T.gpr, ?_, ((Kb.mono (by decide : ∀ r : Reg, r ∈ [.eax] → r ∈ [.eax, .ecx])).widen (C.keeps [])).widen T.keeps⟩
  · rw [T.mem, Oo.w32 (by omega) (by have := scratch.nowrap; omega), Mb, w32_write_self]
    rfl
  · rw [T.mem, Mc, w32_write_self]
    rfl
  · rw [T.mem]
    exact (Outs.of_outside Os (List.mem_cons_self ..)).trans
      (Outs.of_outside Oo (List.mem_cons_of_mem _ (List.mem_singleton_self _)))

end VG.Proof.RsaKeyGen.X86.Exponent
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/ExponentFirst.lean`, which only this module imported.
section

/-! # The first native pass copies c/2 into the exponent and retains its zero sentinel -/

section
namespace VG.Proof.RsaKeyGen.X86.Exponent
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Exponent

def firstRanges (n src out : Nat) : List (Nat × Nat) :=
  [(src + 4 * n, 4), (out + 4 * n, 4), (out, 4 * n)]

theorem firstPass_ok {s : State} {base : Addr} {size n src out : Nat} (scratch : Scr s base size)
    (positive : 0 < n) (srcFit : src + 4 * (n + 1) ≤ size) (outFit : out + 4 * (n + 1) ≤ size)
    (sep : src + 4 * (n + 1) ≤ out) :
    WP isa (firstPass n src out) s fun t =>
      val32 t.mem base out n = val32 s.mem base src n / 2 ∧ w32 t.mem base (out + 4 * n) = 0 ∧
      Outs base (firstRanges n src out) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  refine WP.seq (WP.mono (clearTops_ok scratch srcFit outFit sep) fun a ⟨srcTop, outTop, mask, Oa, Ka⟩ => ?_)
  refine WP.mono (HalfPass.code_ok (scratch.of_keeps Ka (by decide)) positive srcFit (by omega)
    (Or.inr (Or.inl sep)) srcTop mask) fun t ⟨Ot, V, Kt⟩ => ?_
  have before : val32 a.mem base src n = val32 s.mem base src n :=
    Oa.val32 (fun r mem => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl <;> left <;> omega) (by have := scratch.nowrap; omega)
  refine ⟨by rw [before] at V; exact V, ?_, ?_, (Ka.mono (by decide)).widen Kt⟩
  · rw [Ot.w32 (Or.inr (Nat.le_refl _)) (by have := scratch.nowrap; omega)]
    exact outTop
  · exact (Oa.mono (fun r mem => by
      simp only [firstRanges, List.mem_cons, List.not_mem_nil, or_false] at mem ⊢
      rcases mem with rfl | rfl <;> simp)).trans
      (Outs.of_outside Ot (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))

end VG.Proof.RsaKeyGen.X86.Exponent
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/ExponentShift.lean`, which only this module imported.
section

/-! # An alignment pass halves exactly when sigma exceeds its public index -/

section
namespace VG.Proof.RsaKeyGen.X86.ExponentShift
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.ExponentShift

theorem halfIf_ok {s : State} {base : Addr} {size n marker out j k : Nat} (scratch : Scr s base size)
    (positive : 0 < n) (fit : out + 4 * (n + 1) ≤ size) (markerFit : marker + 8 ≤ size)
    (top : w32 s.mem base (out + 4 * n) = 0) (index : k < 64) (choice : 1 ≤ j ∧ j ≤ 3)
    (value : word s.mem base marker = BitVec.twoPow 64 k) :
    WP isa (halfIf n marker out j) s fun t =>
      Outside base out (4 * n) s.mem t.mem ∧
      val32 t.mem base out n = (if j < VG.Proof.RsaKeyGen.sigOf k then val32 s.mem base out n / 2
        else val32 s.mem base out n) ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  refine WP.seq (WP.mono (SigMask.code_sig scratch markerFit index choice value) fun a ⟨mask, M, K⟩ => ?_)
  refine WP.mono (HalfPass.code_ok (scratch.of_keeps K (by decide)) positive fit (by omega) (Or.inl rfl)
    (by rw [M]; exact top) mask) fun t ⟨O, V, Kt⟩ => ?_
  rw [M] at O V
  exact ⟨O, by simpa only [decide_eq_true_eq] using V, (K.mono (by decide)).widen Kt⟩

end VG.Proof.RsaKeyGen.X86.ExponentShift
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/ExponentShiftContext.lean`, which only this module imported.
section

/-! # Alignment marker and top sentinel remain available across all three passes -/

section
namespace VG.Proof.RsaKeyGen.X86.ExponentShift
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.ExponentShift

structure Context (base : Addr) (size n marker out k : Nat) (s : State) : Prop where
  scratch : Scr s base size
  positive : 0 < n
  fit : out + 4 * (n + 1) ≤ size
  markerFit : marker + 8 ≤ size
  apart : marker + 8 ≤ out
  index : k < 64
  value : word s.mem base marker = BitVec.twoPow 64 k
  top : w32 s.mem base (out + 4 * n) = 0

theorem halfIf_context {s : State} {base : Addr} {size n marker out j k : Nat}
    (C : Context base size n marker out k s) (choice : 1 ≤ j ∧ j ≤ 3) :
    WP isa (halfIf n marker out j) s fun t =>
      Context base size n marker out k t ∧ Outside base out (4 * n) s.mem t.mem ∧
      val32 t.mem base out n = (if j < VG.Proof.RsaKeyGen.sigOf k then val32 s.mem base out n / 2
        else val32 s.mem base out n) ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  refine WP.mono (halfIf_ok C.scratch C.positive C.fit C.markerFit C.top C.index choice C.value)
    fun t ⟨O, V, K⟩ => ?_
  refine ⟨⟨C.scratch.of_keeps K (by decide), C.positive, C.fit, C.markerFit, C.apart, C.index, ?_, ?_⟩, O, V, K⟩
  · rw [O.word (Or.inl C.apart) (by have := C.scratch.nowrap; have := C.markerFit; omega)]
    exact C.value
  · rw [O.w32 (Or.inr (Nat.le_refl _)) (by have := C.scratch.nowrap; have := C.fit; omega)]
    exact C.top

end VG.Proof.RsaKeyGen.X86.ExponentShift
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/ExponentShiftPasses.lean`, which only this module imported.
section

/-! # The three masked native passes produce the reviewed exponent -/

section
namespace VG.Proof.RsaKeyGen.X86.ExponentShift
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.ExponentShift

theorem passes_ok {s : State} {base : Addr} {size n marker out k : Nat}
    (C : Context base size n marker out k s) :
    WP isa (passes n marker out) s fun t =>
      Context base size n marker out k t ∧ Outside base out (4 * n) s.mem t.mem ∧
      val32 t.mem base out n =
        (let x := val32 s.mem base out n
         let x1 := if 1 < VG.Proof.RsaKeyGen.sigOf k then x / 2 else x
         let x2 := if 2 < VG.Proof.RsaKeyGen.sigOf k then x1 / 2 else x1
         if 3 < VG.Proof.RsaKeyGen.sigOf k then x2 / 2 else x2) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  refine WP.seq (WP.mono (halfIf_context C (j := 1) (by decide)) fun a ⟨A, Oa, Va, Ka⟩ => ?_)
  refine WP.seq (WP.mono (halfIf_context A (j := 2) (by decide)) fun b ⟨B, Ob, Vb, Kb⟩ => ?_)
  refine WP.mono (halfIf_context B (j := 3) (by decide)) fun t ⟨T, Ot, Vt, Kt⟩ => ?_
  exact ⟨T, (Oa.trans Ob).trans Ot, by rw [Vt, Vb, Va], (Ka.trans Kb).trans Kt⟩

theorem passes_exponent {s : State} {base : Addr} {size n marker out c : Nat}
    (C : Context base size n marker out ((Spec.Rsa.splitTwos (c - 1)).1 % 64) s)
    (odd : c % 2 = 1) (value : val32 s.mem base out n = c / 2) :
    WP isa (passes n marker out) s fun t =>
      Context base size n marker out ((Spec.Rsa.splitTwos (c - 1)).1 % 64) t ∧
      Outside base out (4 * n) s.mem t.mem ∧ val32 t.mem base out n = Proof.MillerRabin.Round.exponent c ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  refine WP.mono (passes_ok C) fun t ⟨T, O, V, K⟩ => ?_
  rw [value, VG.Proof.RsaKeyGen.sigOf_mod] at V
  exact ⟨T, O, V.trans (VG.Proof.RsaKeyGen.mrE_halves odd), K⟩

end VG.Proof.RsaKeyGen.X86.ExponentShift
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/ExponentFinish.lean`, which only this module imported.
section

/-! # Store the complete paired alignment marker after the prepared exponent -/

section
namespace VG.Proof.RsaKeyGen.X86.Exponent
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Exponent

theorem finish_ok {s : State} {base : Addr} {size n out : Nat} (scratch : Scr s base size)
    (markerFit : markerOffset + 8 ≤ size) (outFit : out + 4 * n + 8 ≤ size) :
    WP isa (.block (finish n out)) s fun t =>
      word t.mem base (out + 4 * n) = word s.mem base markerOffset ∧
      Outside base (out + 4 * n) 8 s.mem t.mem ∧ Keeps [.eax, .edx] s t := by
  unfold finish
  refine wp_movS (readSrc_sc scratch (by omega)) fun a A _ =>
    wp_movS (readSrc_sc (scratch.of_keeps A.keeps (by decide)) (by omega)) fun b B _ => ?_
  have K : Keeps [.eax, .edx] s b := (A.keeps.mono (by decide)).widen B.keeps
  refine WP.mono (Header.storePair_ok (scratch.of_keeps K (by decide)) outFit) fun t ⟨M, O, Kt⟩ => ?_
  have pair : b.gpr .edx ++ b.gpr .eax = word s.mem base markerOffset := by
    rw [B.gpr, B.other .eax (by decide), A.gpr, A.mem,
      VG.Proof.Mont.word, VG.Proof.Rc2.Word32.read64_pair, VG.Offset.add_add]
  refine ⟨?_, ?_, K.widen Kt⟩
  · rw [VG.Proof.Mont.word, M, Mem.readW_writeW_self64, pair]
  · rw [B.mem, A.mem] at O
    exact O

end VG.Proof.RsaKeyGen.X86.Exponent
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Exponent
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Exponent

def ranges (w src out : Nat) : List (Nat × Nat) := [(markerOffset, 8), (src + 8 * w, 4), (out, 8 * w + 8)]
def clob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi]

theorem code_ok {s : State} {base : Addr} {size w minusOne src out c : Nat} (scratch : Scr s base size)
    (positive : 0 < w) (minusFit : minusOne + 8 * w ≤ size) (srcFit : src + 8 * w + 4 ≤ size)
    (outFit : out + 8 * w + 8 ≤ size) (lo : markerOffset + 8 ≤ src) (sep : src + 8 * w + 4 ≤ out)
    (candidate : val32 s.mem base src (2 * w) = c)
    (minusValue : val32 s.mem base minusOne (2 * w) = c - 1) (odd : c % 2 = 1) (large : 1 < c) :
    WP isa (code w minusOne src out) s fun t =>
      val32 t.mem base out (2 * w) = Proof.MillerRabin.Round.exponent c ∧
      word t.mem base (out + 8 * w) = BitVec.twoPow 64 ((Spec.Rsa.splitTwos (c - 1)).1 % 64) ∧
      Outs base (ranges w src out) s.mem t.mem ∧ Keeps clob s t := by
  refine WP.seq (WP.mono (ExponentMarker.code_ok scratch minusFit minusValue (by omega_using [large]))
    fun a ⟨marker, Ma, Ka⟩ => ?_)
  have Sa := scratch.of_keeps Ka (by decide)
  have markerFit : markerOffset + 8 ≤ size := by omega_using [srcFit, lo]
  refine WP.seq (WP.mono (Header.storePair_ok Sa markerFit) fun b ⟨Mb, Ob, Kb⟩ => ?_)
  have Ksb : Keeps clob s b := (Ka.mono (by unfold clob; decide)).widen Kb
  have Sb := scratch.of_keeps Ksb (by unfold clob; decide)
  have candidateB : val32 b.mem base src (2 * w) = c := by
    rw [Ob.val32 (Or.inr lo) (by have := scratch.nowrap; omega_using [srcFit, this]), Ma]
    exact candidate
  have markerB : word b.mem base markerOffset = BitVec.twoPow 64 ((Spec.Rsa.splitTwos (c - 1)).1 % 64) := by
    rw [VG.Proof.Mont.word, Mb, Mem.readW_writeW_self64, marker]
  refine WP.seq (WP.mono (firstPass_ok Sb (by omega_using [positive]) (by omega_using [srcFit]) (by omega_using [outFit]) (by omega_using [sep]))
    fun d ⟨valueD, topD, Od, Kd⟩ => ?_)
  have Ksd : Keeps clob s d := Ksb.widen Kd
  have Sd := scratch.of_keeps Ksd (by unfold clob; decide)
  have markerD : word d.mem base markerOffset = BitVec.twoPow 64 ((Spec.Rsa.splitTwos (c - 1)).1 % 64) := by
    rw [Od.word (fun r mem => by
      simp only [firstRanges, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl <;> left <;> omega_arith) (by have := scratch.nowrap; omega_using [srcFit, lo, this])]
    exact markerB
  have C : ExponentShift.Context base size (2 * w) markerOffset out
      ((Spec.Rsa.splitTwos (c - 1)).1 % 64) d :=
    ⟨Sd, by omega_using [positive], by omega_using [outFit], markerFit, by omega_using [lo, sep], Nat.mod_lt _ (by decide), markerD, topD⟩
  have valueD' : val32 d.mem base out (2 * w) = c / 2 := by rw [valueD, candidateB]
  refine WP.seq (WP.mono (ExponentShift.passes_exponent C odd valueD') fun e ⟨Ce, Oe, Ve, Ke⟩ => ?_)
  refine WP.mono (finish_ok Ce.scratch markerFit (by omega_using [outFit])) fun t ⟨markerT, Ot, Kt⟩ => ?_
  refine ⟨?_, ?_, ?_, (Ksd.widen Ke).widen Kt⟩
  · rw [Ot.val32 (Or.inl (by omega_using [])) (by have := scratch.nowrap; omega_using [outFit, this])]
    exact Ve
  · have : out + 4 * (2 * w) = out + 8 * w := by omega_using []
    rw [this] at markerT
    exact markerT.trans Ce.value
  · have Fsb : Outs base (ranges w src out) s.mem b.mem := by
      rw [← Ma]
      exact Outs.of_outside Ob (List.mem_cons_self ..)
    have Fd : Outs base (ranges w src out) b.mem d.mem := Od.cover (by
      intro r mem
      simp only [firstRanges, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl
      · exact ⟨(src + 8 * w, 4), by simp [ranges], by omega_using [], by omega_using []⟩
      · exact ⟨(out, 8 * w + 8), by simp [ranges], by omega_using [], by omega_using []⟩
      · exact ⟨(out, 8 * w + 8), by simp [ranges], by omega_using [], by omega_using []⟩)
    have Fe : Outs base (ranges w src out) d.mem e.mem :=
      Outs.of_outside (Oe.mono (by omega_using []) (by omega_using [])) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
    have Ft : Outs base (ranges w src out) e.mem t.mem :=
      Outs.of_outside (Ot.mono (by omega_using []) (by omega_using [])) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
    exact ((Fsb.trans Fd).trans Fe).trans Ft

end VG.Proof.RsaKeyGen.X86.Exponent

end

end


/-! # Preparing the exponent retains the prepared Montgomery context and constants -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Exponent
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen.X86.PreparedR2

def preparedRanges (g : Geometry) : List (Nat × Nat) := ranges g.w (g.array 0) (g.array 27)

theorem prepared_preserve {g : Geometry} (v : g.Valid) {s t : Mem} (O : Outs g.W (preparedRanges g) s t)
    {j : Nat} (index : j = 4 ∨ j = 5 ∨ j = 9 ∨ j = 10) :
    val32 t g.W (g.array j) g.words = val32 s g.W (g.array j) g.words := by
  apply O.val32
  · intro r mem
    simp only [preparedRanges, ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases index with rfl | rfl | rfl | rfl <;> rcases mem with rfl | rfl | rfl <;>
      simp only [Geometry.array, Geometry.words, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes,
        VG.Impl.RsaKeyGen.X86.Exponent.markerOffset] <;> omega_using []
  · have bound := v.maxWidth
    rcases index with rfl | rfl | rfl | rfl <;>
      simp only [Geometry.array, Geometry.words, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] <;> omega_using [bound]

/-- `Ready` kept by writes to the exponent's ranges. -/
theorem ready_keep {g : Geometry} (v : g.Valid) {s t : State} {c capacity : Nat} {p : BitVec 32}
    (S : Ready g c capacity p s) (O : Outs g.W (preparedRanges g) s.mem t.mem) (K : Keeps clob s t) :
    Ready g c capacity p t := by
  have srcFit := Prepared.paddedFit v (j := 0) (by decide)
  have outFit := Prepared.paddedFit v (j := 27) (by decide)
  have head := v.headerFit
  have fits : ∀ r ∈ preparedRanges g, r.1 + r.2 ≤ g.L := by
    intro r mem
    simp only [preparedRanges, ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl <;> simp only [VG.Impl.RsaKeyGen.X86.Exponent.markerOffset] <;> omega_arith
  have metadata : ∀ r ∈ preparedRanges g, (128 ≤ r.1 ∧ r.1 + r.2 ≤ 224) ∨ 256 ≤ r.1 := by
    intro r mem
    simp only [preparedRanges, ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl
    · left; decide
    · right; have := v.arrayHeader 0; omega
    · right; exact v.arrayHeader 27
  have F := WorkspaceFrame.of_outs S.scratch.nowrap O
  refine ⟨Prepared.keepGaps v S.context K (by unfold clob; decide) O metadata,
    S.modulus.keep v F (fun r mem => by have := metadata r mem; omega_using [this]) ?_,
    S.caller.keepOuts K (by unfold clob; decide) O fits,
    S.scratch.of_keeps K (by unfold clob; decide)⟩
  intro r mem
  simp only [preparedRanges, ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
  have top := v.arrayHeader 0
  have before := g.arrayBefore (i := 0) (j := 27) (by decide)
  rcases mem with rfl | rfl | rfl
  · right; unfold VG.Impl.RsaKeyGen.X86.Exponent.markerOffset; omega_using [top]
  · left; unfold Geometry.words; omega_using []
  · left; exact before

theorem ready_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (S : Ready g c capacity p s) (minusOne : val32 s.mem g.W (g.array 5) g.words = c - 1)
    (odd : c % 2 = 1) (large : 1 < c) :
    WP isa (VG.Impl.RsaKeyGen.X86.Exponent.code g.w (g.array 5) (g.array 0) (g.array 27)) s fun t =>
      Ready g c capacity p t ∧ val32 t.mem g.W (g.array 27) g.words = Proof.MillerRabin.Round.exponent c ∧
      word t.mem g.W (g.array 27 + 8 * g.w) = BitVec.twoPow 64 ((Spec.Rsa.splitTwos (c - 1)).1 % 64) ∧
      Outs g.W (preparedRanges g) s.mem t.mem ∧ Keeps clob s t := by
  have srcFit := Prepared.paddedFit v (j := 0) (by decide)
  have outFit := Prepared.paddedFit v (j := 27) (by decide)
  have apart := Prepared.paddedBefore g (i := 0) (j := 27) (by decide)
  have head := v.headerFit
  refine WP.mono (code_ok S.scratch (by have := v.minWidth; omega_using [this])
    (by have := v.arrayFit (j := 5) (by decide); unfold Geometry.words at this; omega_using [this])
    (by omega_using [srcFit]) (by omega_using [outFit]) (by have := v.arrayHeader 0; unfold VG.Impl.RsaKeyGen.X86.Exponent.markerOffset; omega_using [this])
    (by omega_using [apart]) S.modulus.candidate minusOne odd large) fun t ⟨E, marker, O, K⟩ => ?_
  exact ⟨ready_keep v S O K, E, marker, O, K⟩

end VG.Proof.RsaKeyGen.X86.Exponent

end

end

/-! ### `RsaKeyGen.X86.PrepareMetadata`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.Prepare`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.PreparedR2Frame`, which this module and modules that import it used -/

section

/-! # Fast R² setup retains the saved c-1 and the prepared exponent -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.PreparedR2
open VG VG.Proof.Mont VG.Proof.MillerRabin.X86

theorem preserve {g : Geometry} (v : g.Valid) {s t : Mem} (F : WorkspaceFrame g (ranges g) s t)
    {j : Nat} (index : j = 5 ∨ j = 27) :
    val32 t g.W (g.array j) g.words = val32 s g.W (g.array j) g.words := by
  apply F.val32 (v.arrayFit (by omega_using [index]))
  intro r mem
  simp only [ranges, coreRanges, phaseRanges, montWrites, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at mem
  rcases index with rfl | rfl <;>
    rcases mem with ((rfl | rfl | rfl) | (rfl | rfl | rfl)) | rfl <;>
    simp only [Geometry.array, Geometry.words, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes,
      VG.Proof.Mont.X86.accLen, VG.Impl.Bignum.X86.PublicContext.modulus, VG.Impl.Mont.X86.words] <;> omega_using []

end VG.Proof.RsaKeyGen.X86.PreparedR2

end

end

/-! ### `RsaKeyGen.X86.PrepareHeader`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.HeaderRead`, which only this module used -/

section

/-! # Pointer initialization preserves the scalar metadata and inverse -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Header
open VG VG.Proof.Mont

theorem read64_write {base : Addr} {m : Mem} {d e : Nat} {v : BitVec 64}
    (apart : d + 8 ≤ e ∨ e + 8 ≤ d) (readFit : d + 8 ≤ 2 ^ 64) (writeFit : e + 8 ≤ 2 ^ 64) :
    (m.writeW (off base e) v).readW (off base d) 64 = m.readW (off base d) 64 :=
  Mem.readW_writeW_sep (Offset.sep base apart readFit writeFit) (by decide)

theorem pointers_read64 (indices : List Nat) {base : Addr} {p : BitVec 32} {w d : Nat} {m : Mem}
    (bound : ∀ i ∈ indices, i < 8) (fit : d + 8 ≤ 2 ^ 64)
    (apart : d + 8 ≤ 64 ∨ 128 ≤ d) :
    (indices.foldl (pointerMemory base p w) m).readW (off base d) 64 = m.readW (off base d) 64 := by
  induction indices generalizing m with
  | nil => rfl
  | cons i indices ih =>
    rw [List.foldl_cons, ih (fun j mem => bound j (List.mem_cons_of_mem _ mem))]
    unfold pointerMemory
    apply read64_write _ fit
    · have := bound i (List.mem_cons_self ..)
      omega_using [this]
    · have := bound i (List.mem_cons_self ..)
      omega_using [apart, this]

theorem header_width {base : Addr} {p : BitVec 32} {w : Nat} {m : Mem} :
    (headerMemory base p w m).readW (off base 48) 64 = 0#32 ++ BitVec.ofNat 32 w := by
  unfold headerMemory
  rw [pointers_read64 _ (fun _ mem => List.mem_range.mp mem) (by decide) (by decide),
    read64_write (by decide) (by decide) (by decide), Mem.readW_writeW_self64]

theorem header_stride {base : Addr} {p : BitVec 32} {w : Nat} {m : Mem} :
    (headerMemory base p w m).readW (off base 224) 64 =
      0#32 ++ BitVec.ofNat 32 (VG.Impl.Bignum.X86.PublicContext.stride w) := by
  unfold headerMemory
  rw [pointers_read64 _ (fun _ mem => List.mem_range.mp mem) (by decide) (by decide),
    Mem.readW_writeW_self64]

theorem pointers_read64_at (indices : List Nat) {base : Addr} {p : BitVec 32} {w j : Nat} {m : Mem}
    (bound : ∀ i ∈ indices, i < 8) (index : j < 8) :
    (indices.foldl (pointerMemory base p w) m).readW (off base (64 + 8 * j)) 64 =
      if j ∈ indices then 0#32 ++ (p + BitVec.ofNat 32 (VG.Impl.Bignum.X86.PublicContext.slot w j))
      else m.readW (off base (64 + 8 * j)) 64 := by
  induction indices generalizing m with
  | nil => rfl
  | cons i indices ih =>
    rw [List.foldl_cons, ih (fun k mem => bound k (List.mem_cons_of_mem _ mem))]
    by_cases tail : j ∈ indices
    · simp only [tail, ite_true, List.mem_cons, or_true]
    · rw [ite_eq_right tail]
      by_cases same : j = i
      · subst i
        simp only [List.mem_cons, true_or, ite_true, pointerMemory, Mem.readW_writeW_self64]
      · simp only [List.mem_cons, same, false_or, tail, ite_false]
        unfold pointerMemory
        apply read64_write
        · omega_using [same]
        · omega_using [index]
        · have := bound i (List.mem_cons_self ..)
          omega_using [this]

theorem header_pointer {base : Addr} {p : BitVec 32} {w j : Nat} {m : Mem} (index : j < 8) :
    (headerMemory base p w m).readW (off base (64 + 8 * j)) 64 =
      0#32 ++ (p + BitVec.ofNat 32 (VG.Impl.Bignum.X86.PublicContext.slot w j)) := by
  unfold headerMemory
  rw [pointers_read64_at _ (fun _ mem => List.mem_range.mp mem) index, ite_eq_left (List.mem_range.mpr index)]

end VG.Proof.RsaKeyGen.X86.Header

end

end

/-! ### `RsaKeyGen.X86.HeaderFrame`, which this module and modules that import it used -/

section

/-! # Public header initialization preserves arguments, the inverse and all arrays -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Header
open VG VG.Proof.Mont

def ranges : List (Nat × Nat) := [(48, 8), (64, 64), (224, 8)]

theorem pointers_frame (indices : List Nat) {base : Addr} {p : BitVec 32} {w : Nat} {m : Mem}
    (bound : ∀ i ∈ indices, i < 8) :
    Outs base ranges m (indices.foldl (pointerMemory base p w) m) := by
  induction indices generalizing m with
  | nil => exact Outs.refl _ _ _
  | cons i indices ih =>
    rw [List.foldl_cons]
    have first : Outs base ranges m (pointerMemory base p w m i) :=
      Outs.of_outside ((writeW_outside _ base _ (by have := bound i (by simp); omega_using [this])).mono
        (by omega_using []) (by have := bound i (by simp); omega_using [this]))
        (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    exact first.trans (ih (fun j mem => bound j (List.mem_cons_of_mem _ mem)))

theorem header_frame {base : Addr} {p : BitVec 32} {w : Nat} {m : Mem} :
    Outs base ranges m (headerMemory base p w m) := by
  have width : Outs base ranges m (m.writeW (off base 48) (0#32 ++ BitVec.ofNat 32 w)) :=
    Outs.of_outside (writeW_outside _ base _ (by decide)) (List.mem_cons_self ..)
  have stride : Outs base ranges (m.writeW (off base 48) (0#32 ++ BitVec.ofNat 32 w))
      ((m.writeW (off base 48) (0#32 ++ BitVec.ofNat 32 w)).writeW (off base 224)
        (0#32 ++ BitVec.ofNat 32 (VG.Impl.Bignum.X86.PublicContext.stride w))) :=
    Outs.of_outside (writeW_outside _ base _ (by decide))
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  exact (width.trans stride).trans (pointers_frame (List.range 8) (fun _ mem => List.mem_range.mp mem))

end VG.Proof.RsaKeyGen.X86.Header

end

end

/-! ### `RsaKeyGen.X86.HeaderRt`, which only this module used -/

section

/-! # The run-time header writes `Header.code`'s memory for the width at byte 4 -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.HeaderRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Bignum.X86.PublicContext VG.Impl.RsaKeyGen.X86.HeaderRt
open VG.Proof.RsaKeyGen.X86.Header (headerMemory pointerMemory storePair_ok)
open VG.Impl.Mont.X86 (sc)

theorem pointers_ok {w : Nat} (k : Nat) : ∀ (n : Nat) {s : State} {base : Addr} {size : Nat}
    (_ : Scr s base size) (_ : 64 + 8 * (k + n) ≤ size) (_ : s.gpr .edx = 0#32)
    (_ : s.gpr .eax = s.gpr .edi + BitVec.ofNat 32 (slot w k))
    (_ : s.gpr .ecx = BitVec.ofNat 32 (stride w)),
    WP isa (.block ((List.range' k n).flatMap pointer)) s fun t =>
      t.mem = (List.range' k n).foldl (pointerMemory base (s.gpr .edi) w) s.mem ∧ Keeps [.eax] s t
  | 0, _, _, _, _, _, _, _, _ => WP.block_nil ⟨rfl, Keeps.refl _ _⟩
  | n + 1, s, base, size, scratch, fit, zero, eax, ecx => by
    rw [List.range'_succ, List.flatMap_cons]
    unfold pointer
    refine WP.block_append (WP.block_append (WP.mono (storePair_ok scratch (offset := 64 + 8 * k) (by omega_using [fit]))
      fun a ⟨M, _, K⟩ => ?_))
    refine wp_addS rfl fun b B _ => WP.block_nil ?_
    have Kb : Keeps [.eax] s b := (K.mono (by decide)).widen B.keeps
    have ih := pointers_ok (w := w) (k + 1) n (s := b) (scratch.of_keeps Kb (by decide)) (by omega_using [fit])
      (by rw [Kb.1 .edx (by decide)]; exact zero)
      (by
        rw [B.gpr, K.1 .eax (by decide), K.1 .ecx (by decide), eax, ecx, BitVec.add_assoc, ← BitVec.ofNat_add, Kb.1 .edi (by decide)]
        congr 2
        simp only [slot, stride, Nat.succ_mul]
        omega_using [])
      (by rw [Kb.1 .ecx (by decide)]; exact ecx)
    refine WP.mono ih fun t ⟨Mt, Kt⟩ => ⟨?_, Kb.trans Kt⟩
    rw [Mt, Kb.1 .edi (by decide), B.mem, M, eax, zero, List.foldl_cons]
    rfl

theorem code_ok {s : State} {base : Addr} {size w : Nat} (scratch : Scr s base size) (fit : 256 ≤ size)
    (bound : w ≤ 128) (len : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w)) :
    WP isa (.block code) s fun t =>
      t.mem = headerMemory base (s.gpr .edi) w s.mem ∧ Keeps [.eax, .ecx, .edx] s t := by
  unfold code
  simp only [List.cons_append]
  refine wp_movS (readSrc_sc scratch (d := 4) (by omega_using [fit])) fun a A _ => wp_movS rfl fun b B _ =>
    VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun c C => wp_movS rfl fun d D _ => ?_
  have Kd : Keeps [.eax, .ecx, .edx] s d :=
    (((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps).widen D.keeps
  have zero : d.gpr .edx = 0#32 := D.gpr
  have width : d.gpr .eax = BitVec.ofNat 32 w := by
    rw [D.other .eax (by decide), C.gpr, B.gpr, A.gpr, len]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega_using [bound]
  have Md : d.mem = s.mem := by rw [D.mem, C.mem, B.mem, A.mem]
  show WP isa (.block ([.store (sc 48) .eax, .store (sc (48 + 4)) .edx] ++ _)) d _
  refine WP.block_append (WP.mono (storePair_ok (scratch.of_keeps Kd (by decide)) (offset := 48) (by omega_using [fit]))
    fun e ⟨Me, _, Ke⟩ => ?_)
  refine wp_addS rfl fun f F _ => wp_movS rfl fun h H _ => ?_
  have Kh : Keeps [.eax, .ecx, .edx] s h := ((Kd.widen Ke).widen F.keeps).widen H.keeps
  have strideF : f.gpr .ecx = BitVec.ofNat 32 (stride w) := by
    rw [F.gpr, Ke.1 .ecx (by decide), D.other .ecx (by decide), C.other .ecx (by decide), B.other .ecx (by decide),
      A.gpr, len]
    apply BitVec.eq_of_toNat_eq
    have sixteen : (16 : BitVec 32).toNat = 16 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, stride, sixteen]
    omega_using []
  have zeroH : h.gpr .edx = 0#32 := by
    rw [H.other .edx (by decide), F.other .edx (by decide), Ke.1 .edx (by decide)]; exact zero
  show WP isa (.block ([.store (sc 224) .eax, .store (sc (224 + 4)) .edx] ++ _)) h _
  refine WP.block_append (WP.mono (storePair_ok (scratch.of_keeps Kh (by decide)) (offset := 224) (by omega_using [fit]))
    fun i ⟨Mi, _, Ki⟩ => ?_)
  refine wp_movS rfl fun j J _ => wp_addS rfl fun l Lr _ => ?_
  have Kl : Keeps [.eax, .ecx, .edx] s l := ((Kh.widen Ki).widen J.keeps).widen Lr.keeps
  have edi : l.gpr .edi = s.gpr .edi := Kl.1 .edi (by decide)
  have eaxL : l.gpr .eax = l.gpr .edi + BitVec.ofNat 32 (slot w 0) := by
    rw [Lr.gpr, J.gpr, edi, Ki.1 .edi (by decide), Kh.1 .edi (by decide),
      show slot w 0 = 256 by simp [slot, VG.Impl.Bignum.hdrBytes]]
    rfl
  have ecxL : l.gpr .ecx = BitVec.ofNat 32 (stride w) := by
    rw [Lr.other .ecx (by decide), J.other .ecx (by decide), Ki.1 .ecx (by decide), H.other .ecx (by decide)]
    exact strideF
  have zeroL : l.gpr .edx = 0#32 := by
    rw [Lr.other .edx (by decide), J.other .edx (by decide), Ki.1 .edx (by decide)]; exact zeroH
  rw [List.range_eq_range']
  refine WP.mono (pointers_ok 0 8 (scratch.of_keeps Kl (by decide)) (by omega_using [fit]) zeroL eaxL ecxL)
    fun t ⟨Mt, Kt⟩ => ⟨?_, Kl.widen Kt⟩
  have strideH : h.gpr .eax = BitVec.ofNat 32 (stride w) := by rw [H.gpr]; exact strideF
  rw [Mt, edi, Lr.mem, J.mem, Mi, strideH, zeroH, H.mem, F.mem, Me, width, zero, Md]
  unfold headerMemory
  rw [List.range_eq_range']

end VG.Proof.RsaKeyGen.X86.HeaderRt

end

end

/-! ### `RsaKeyGen.X86.HeaderLayout`, which only this module used -/

section

/-! # The initialized header satisfies the existing Montgomery layout contract -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Header
open VG VG.X86 VG.Proof.Mont VG.Impl.Bignum.X86.PublicContext

theorem zeroHigh (x : BitVec 32) : 0#32 ++ x = x.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_append, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or]
  have := x.isLt
  omega_using []

theorem width_eq {base : Addr} {p : BitVec 32} {w : Nat} {m : Mem} (bound : w < 2 ^ 32) :
    Proof.Rsa.Mont.wOf (headerMemory base p w m) base = w := by
  change ((headerMemory base p w m).readW (off base 48) 64).toNat = w
  rw [header_width, zeroHigh]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_using [bound]

theorem slot_eq (w j : Nat) : slot w j = Proof.Rsa.Mont.arrAt w j := by
  unfold slot stride VG.Impl.Bignum.hdrBytes Proof.Rsa.Mont.arrAt Proof.Rsa.Mont.hdrBytes
  simp only [Nat.mul_add]

theorem layout {base : Addr} {p : BitVec 32} {w wsLen : Nat} {m : Mem}
    (baseEq : p.setWidth 64 = base) (positive : 2 ≤ w) (bound : w < 2 ^ 31)
    (fit : Proof.Rsa.Mont.arrAt w 8 ≤ 8 * wsLen) (nowrap : base.toNat + 8 * wsLen ≤ 2 ^ 32) :
    Proof.Rsa.Mont.Layout (headerMemory base p w m) base wsLen := by
  unfold Proof.Rsa.Mont.Layout
  rw [width_eq (by omega_using [bound])]
  refine ⟨positive, bound, fit, ?_⟩
  intro j index
  change (headerMemory base p w m).readW (off base (8 * (8 + j))) 64 = _
  rw [show 8 * (8 + j) = 64 + 8 * j by omega_using [], header_pointer index, zeroHigh]
  change addr p (slot w j) = _
  rw [addr_eq, baseEq, slot_eq]
  have pNat : p.toNat = base.toNat := by
    rw [← baseEq, BitVec.toNat_setWidth]
    have := p.isLt
    omega_using []
  have offset : slot w j < Proof.Rsa.Mont.arrAt w 8 := by
    rw [← slot_eq]
    unfold slot stride
    have := Nat.mul_lt_mul_of_pos_right index (by omega_using [] : 0 < 8 * w + 16)
    omega_using [this]
  omega_using [fit, nowrap, pNat, offset]

end VG.Proof.RsaKeyGen.X86.Header

end

end

/-! ### `RsaKeyGen.X86.InverseLift`, which only this module used -/

section

/-! # Execute the three-product inverse lift without memory accesses -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/InverseLift.lean`, which only this module imported.
section

/-! # A one-step negative-inverse lift expressed in native-word parts -/

section
namespace VG.Proof.RsaKeyGen

theorem inverse_lift_identity {b c x k q y : Int}
    (inverse : c * x + 1 = b * k) (split : x * k = b * q + y) :
    c * (x + b * y) + 1 = b * b * (k * k - c * q) := by
  grind

theorem inverse_lift_dvd {b c x k q y : Int}
    (inverse : c * x + 1 = b * k) (split : x * k = b * q + y) :
    b * b ∣ c * (x + b * y) + 1 :=
  ⟨k * k - c * q, inverse_lift_identity inverse split⟩

theorem inverse_lift_nat {b c x : Nat} (inverse : (c * x + 1) % b = 0) :
    (c * (x + b * (x * ((c * x + 1) / b) % b)) + 1) % (b * b) = 0 := by
  let k := (c * x + 1) / b
  have eq₁ : c * x + 1 = b * k := by
    have := Nat.div_add_mod (c * x + 1) b
    rw [inverse, Nat.add_zero] at this
    exact this.symm
  have eq₂ : x * k = b * (x * k / b) + x * k % b := (Nat.div_add_mod (x * k) b).symm
  have I : (c : Int) * x + 1 = (b : Int) * k := by
    simpa only [Int.natCast_add, Int.natCast_mul, Int.natCast_one] using congrArg (fun n : Nat => (n : Int)) eq₁
  have S : (x : Int) * k = (b : Int) * (x * k / b : Nat) + (x * k % b : Nat) := by
    simpa only [Int.natCast_add, Int.natCast_mul] using congrArg (fun n : Nat => (n : Int)) eq₂
  have D : ((b * b : Nat) : Int) ∣ ((c * (x + b * (x * k % b)) + 1 : Nat) : Int) := by
    simpa only [Int.natCast_add, Int.natCast_mul, Int.natCast_one] using inverse_lift_dvd I S
  exact Nat.mod_eq_zero_of_dvd (Int.natCast_dvd_natCast.mp D)

end VG.Proof.RsaKeyGen
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.InverseLift
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.InverseLift

def highCarry (a x : BitVec 32) : BitVec 32 :=
  BitVec.ofNat 32 (a.toNat * x.toNat / 2 ^ 32) +
    Trial.carryWord (Trial.carry (BitVec.ofNat 32 (a.toNat * x.toNat)) 1)

def upper (a b x : BitVec 32) : BitVec 32 :=
  BitVec.ofNat 32 (x.toNat *
    (BitVec.ofNat 32 (b.toNat * x.toNat) + highCarry a x).toNat)

theorem code_ok (s : State) :
    WP isa (.block code) s fun t =>
      t.gpr .eax = upper (s.gpr .ebx) (s.gpr .esi) (s.gpr .ecx) ∧
      t.mem = s.mem ∧ Keeps [.eax, .edx, .ebp] s t := by
  unfold code
  refine wp_movS rfl fun a A _ => wp_mul fun b B => wp_addS rfl fun c C cfC =>
    wp_adcS rfl cfC fun d D _ => ?_
  have Kd : Keeps [.eax, .edx] s d :=
    (((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps).widen D.keeps
  have high : d.gpr .edx = highCarry (s.gpr .ebx) (s.gpr .ecx) := by
    rw [D.gpr, C.other .edx (by decide), B.edx, A.gpr, A.other .ecx (by decide)]
    change _ + 0#32 + _ = _
    rw [BitVec.add_zero, B.eax, A.gpr, A.other .ecx (by decide)]
    rfl
  refine wp_movS rfl fun e E _ => wp_movS rfl fun f F _ => wp_mul fun h H =>
    wp_addS rfl fun i I _ => wp_movS rfl fun j J _ => wp_movS rfl fun k K _ =>
    wp_mul fun t T => WP.block_nil ?_
  have keep : Keeps [.eax, .edx, .ebp] s t :=
    (((((((Kd.mono (by decide)).widen E.keeps).widen F.keeps).widen H.keeps).widen I.keeps).widen
      J.keeps).widen K.keeps).widen T.keeps
  refine ⟨?_, ?_, keep⟩
  · rw [T.eax, K.gpr, J.other .ecx (by decide), I.other .ecx (by decide),
      H.other .ecx (by decide) (by decide), F.other .ecx (by decide), E.other .ecx (by decide),
      Kd.1 .ecx (by decide), K.other .ebp (by decide), J.gpr, I.gpr, H.eax, F.gpr,
      E.other .esi (by decide), Kd.1 .esi (by decide), F.other .ecx (by decide),
      E.other .ecx (by decide), Kd.1 .ecx (by decide), H.other .ebp (by decide) (by decide),
      F.other .ebp (by decide), E.gpr, high]
    rfl
  · rw [T.mem, K.mem, J.mem, I.mem, H.mem, F.mem, E.mem, D.mem, C.mem, B.mem, A.mem]

theorem highCarry_toNat (a x : BitVec 32) :
    (highCarry a x).toNat = (a.toNat * x.toNat + 1) / 2 ^ 32 := by
  have product := Nat.mul_le_mul (show a.toNat ≤ 2 ^ 32 - 1 by have := a.isLt; omega_using [])
    (show x.toNat ≤ 2 ^ 32 - 1 by have := x.isLt; omega_using [])
  have split := Nat.div_add_mod (a.toNat * x.toNat) (2 ^ 32)
  have remainder := Nat.mod_lt (a.toNat * x.toNat) (by decide : 0 < 2 ^ 32)
  unfold highCarry
  rw [BitVec.toNat_add, Trial.carryWord_toNat, Trial.carry_toNat]
  simp only [BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
  omega_using [product]

theorem upper_toNat (a b x : BitVec 32) :
    (upper a b x).toNat =
      x.toNat * ((a.toNat * x.toNat + 1) / 2 ^ 32 + b.toNat * x.toNat) % 2 ^ 32 := by
  unfold upper
  rw [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat, highCarry_toNat]
  rw [Nat.mod_add_mod, Nat.mul_mod_mod]
  congr 2
  omega_using []

theorem upper_inverse (a b x : BitVec 32)
    (inverse : (a.toNat * x.toNat + 1) % 2 ^ 32 = 0) :
    ((a.toNat + 2 ^ 32 * b.toNat) * (x.toNat + 2 ^ 32 * (upper a b x).toNat) + 1) % 2 ^ 64 = 0 := by
  have rearrange : (a.toNat + 2 ^ 32 * b.toNat) * x.toNat + 1 =
      a.toNat * x.toNat + 1 + 2 ^ 32 * (b.toNat * x.toNat) := by grind
  have full : ((a.toNat + 2 ^ 32 * b.toNat) * x.toNat + 1) % 2 ^ 32 = 0 := by
    rw [rearrange, Nat.add_mul_mod_self_left]
    exact inverse
  have result := VG.Proof.RsaKeyGen.inverse_lift_nat full
  rw [rearrange, Nat.add_mul_div_left _ _ (by decide)] at result
  rw [upper_toNat]
  exact result

theorem inverse_ok (s : State)
    (inverse : ((s.gpr .ebx).toNat * (s.gpr .ecx).toNat + 1) % 2 ^ 32 = 0) :
    WP isa (.block code) s fun t =>
      (((s.gpr .ebx).toNat + 2 ^ 32 * (s.gpr .esi).toNat) *
        ((t.gpr .ecx).toNat + 2 ^ 32 * (t.gpr .eax).toNat) + 1) % 2 ^ 64 = 0 ∧
      t.mem = s.mem ∧ Keeps [.eax, .edx, .ebp] s t :=
  WP.mono (code_ok s) fun t ⟨value, mem, keep⟩ =>
    ⟨by rw [value, keep.1 .ecx (by decide)]; exact upper_inverse _ _ _ inverse, mem, keep⟩

end VG.Proof.RsaKeyGen.X86.InverseLift

end

end

/-! # A fresh candidate reaches the existing prepared Montgomery contract -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/HeaderContext.lean`, which only this module imported.
section

/-! # The public header prepares the native callable Miller–Rabin context -/

section
namespace VG.Proof.RsaKeyGen.X86.Header
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.MillerRabin.X86

theorem low_word (m : Mem) (base : Addr) (d : Nat) : w32 m base d = (word m base d).toNat % 2 ^ 32 := by
  rw [word_eq_w32, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (m.readW (off base d) 32).isLt]

/-- The context and frame of any code that writes the header's memory. -/
theorem context_of {g : Geometry} (v : g.Valid) {s t : State} (scratch : Scr s g.W g.L) {rs : List Reg}
    (K : Keeps rs s t) (edi : .edi ∉ rs) (M : t.mem = headerMemory g.W (s.gpr .edi) g.w s.mem) :
    Context g t ∧ Outs g.W ranges s.mem t.mem := by
  have wBound : g.w < 2 ^ 32 := by have := v.maxWidth; omega
  have strideBound : VG.Impl.Bignum.X86.PublicContext.stride g.w < 2 ^ 32 := by
    have := v.maxWidth
    unfold VG.Impl.Bignum.X86.PublicContext.stride
    omega
  have baseBound : g.W.toNat < 2 ^ 32 := by have := scratch.nowrap; have := v.headerFit; omega
  refine ⟨⟨⟨K.2.2 ▸ scratch.wr, scratch.nowrap⟩, ?_, ?_, ?_, ?_⟩, M ▸ header_frame⟩
  · rw [PtrAt, K.1 .edi edi, scratch.edi_toNat, Nat.add_zero, Nat.mod_eq_of_lt baseBound]
  · rw [M, low_word, VG.Proof.Mont.word, header_width, zeroHigh, BitVec.toNat_setWidth_of_le (by decide),
      BitVec.toNat_ofNat, Nat.mod_mod, Nat.mod_eq_of_lt wBound]
  · rw [M, low_word, VG.Proof.Mont.word, header_stride, zeroHigh, BitVec.toNat_setWidth_of_le (by decide),
      BitVec.toNat_ofNat, Nat.mod_mod, Nat.mod_eq_of_lt strideBound]
    rfl
  · intro j index
    rw [M, low_word, VG.Proof.Mont.word, header_pointer index, zeroHigh, BitVec.toNat_setWidth_of_le (by decide),
      Nat.mod_eq_of_lt (s.gpr .edi + BitVec.ofNat 32 (VG.Impl.Bignum.X86.PublicContext.slot g.w j)).isLt,
      BitVec.toNat_add, BitVec.toNat_ofNat, scratch.edi_toNat, Prepared.slot_eq]
    omega

end VG.Proof.RsaKeyGen.X86.Header
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/InverseSetup.lean`, which only this module imported.
section

/-! # Complete the prepared workspace's 64-bit negative inverse -/

section
namespace VG.Proof.RsaKeyGen.X86.InverseLift
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.RsaKeyGen.X86.InverseLift

theorem setup_ok {s : State} {base : Addr} {size mo inv : Nat}
    (scratch : Scr s base size) (modulus : mo + 8 ≤ size) (slot : inv + 8 ≤ size)
    (inverse : (w32 s.mem base mo * w32 s.mem base inv + 1) % 2 ^ 32 = 0) :
    WP isa (.block (setup mo inv)) s fun t =>
      ((w32 s.mem base mo + 2 ^ 32 * w32 s.mem base (mo + 4)) *
        (w32 s.mem base inv + 2 ^ 32 * w32 t.mem base (inv + 4)) + 1) % 2 ^ 64 = 0 ∧
      Outside base (inv + 4) 4 s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold setup
  simp only [List.cons_append, List.nil_append]
  refine wp_movS (readSrc_sc scratch (by omega)) fun a A _ => ?_
  have Sa := scratch.of_keeps A.keeps (by decide)
  refine wp_movS (readSrc_sc Sa (by omega)) fun b B _ => ?_
  have Kb : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s b := (A.keeps.mono (by decide)).widen B.keeps
  have Sb := scratch.of_keeps Kb (by decide)
  refine wp_movS (readSrc_sc Sb (by omega)) fun c C _ => ?_
  have lo : c.gpr .ebx = s.mem.readW (off base mo) 32 := by
    rw [C.other .ebx (by decide), B.other .ebx (by decide), A.gpr]
  have hi : c.gpr .esi = s.mem.readW (off base (mo + 4)) 32 := by
    rw [C.other .esi (by decide), B.gpr, A.mem]
  have ix : c.gpr .ecx = s.mem.readW (off base inv) 32 := by
    rw [C.gpr, B.mem, A.mem]
  refine WP.block_append (WP.mono (inverse_ok c (by rw [lo, ix]; exact inverse)) fun d ⟨value, mem, Kd⟩ => ?_)
  have K : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s d := (Kb.widen C.keeps).widen Kd
  have Sd := scratch.of_keeps K (by decide)
  refine wp_storeS (Sd.ea (by omega)) (Sd.write (by omega)) fun t T => WP.block_nil ?_
  refine ⟨?_, ?_, K.widen (T.keeps [])⟩
  · rw [T.mem, w32_write_self]
    rw [Kd.1 .ecx (by decide), lo, hi, ix] at value
    exact value
  · rw [T.mem, mem, C.mem, B.mem, A.mem]
    exact writeW32_outside _ _ _ (by have := scratch.nowrap; omega)

end VG.Proof.RsaKeyGen.X86.InverseLift
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/MontInverse.lean`, which only this module imported.
section

/-! # The compact prepared kernel receives the reviewed full 64-bit inverse -/

section
namespace VG.Proof.RsaKeyGen.X86.MontInverse
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.MontInverse

theorem code_ok {s : State} {base : Addr} {size modulus inverse : Nat} (scratch : Scr s base size)
    (modFit : modulus + 8 ≤ size) (invFit : inverse + 8 ≤ size)
    (apart : inverse + 8 ≤ modulus ∨ modulus + 8 ≤ inverse) (odd : w32 s.mem base modulus % 2 = 1) :
    WP isa (code modulus inverse) s fun t =>
      ((word t.mem base modulus).toNat * (word t.mem base inverse).toNat + 1) % 2 ^ 64 = 0 ∧
      Outside base inverse 8 s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  refine WP.seq (WP.mono (VG.Proof.Mont.X86.Dynamic.setupInverse_ok scratch (by omega) (by omega) odd)
    fun a ⟨inverseA, Oa, Ka⟩ => ?_)
  have low : (w32 a.mem base modulus * w32 a.mem base inverse + 1) % 2 ^ 32 = 0 := by
    rw [Oa.w32 (by omega) (by have := scratch.nowrap; omega)]
    exact inverseA
  refine WP.mono (InverseLift.setup_ok (scratch.of_keeps Ka (by decide)) modFit invFit low)
    fun t ⟨inverseT, Ot, Kt⟩ => ?_
  refine ⟨?_, (Oa.mono (by omega) (by omega)).trans (Ot.mono (by omega) (by omega)), ?_⟩
  · rw [word_eq_w32, word_eq_w32,
      Ot.w32 (d := modulus) (by omega) (by have := scratch.nowrap; omega),
      Ot.w32 (d := modulus + 4) (by omega) (by have := scratch.nowrap; omega),
      Ot.w32 (d := inverse) (by omega) (by have := scratch.nowrap; omega)]
    exact inverseT
  · exact (Ka.mono (by decide)).trans Kt

end VG.Proof.RsaKeyGen.X86.MontInverse
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.PrepareHeader
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.MillerRabin.X86
open VG.Proof.RsaKeyGen.X86.PreparedR2

def ranges : List (Nat × Nat) := Header.ranges ++ [(56, 8)]
def clob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi]

/-- The header written by any code that writes `Header.code`'s memory, then the inverse. -/
theorem codeWith_ok {hdr : List Instr} {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat}
    {p : BitVec 32} (scratch : Scr s g.W g.L) (caller : Caller g capacity p s) (length : g.L = 8 * capacity)
    (candidate : val32 s.mem g.W (g.array 0) g.words = c) (odd : c % 2 = 1)
    (header : WP isa (.block hdr) s fun t =>
      t.mem = Header.headerMemory g.W (s.gpr .edi) g.w s.mem ∧ Keeps [.eax, .ecx, .edx] s t) :
    WP isa (.seq (.block hdr) (VG.Impl.RsaKeyGen.X86.MontInverse.code (g.array 0) 56)) s fun t =>
      Ready g c capacity p t ∧ Outs g.W ranges s.mem t.mem ∧ Keeps clob s t ∧
      word t.mem g.W 224 = BitVec.ofNat 64 (8 * (g.w + 2)) := by
  refine WP.seq (WP.mono header fun a ⟨Ma, Ka⟩ => ?_)
  obtain ⟨Ca, Oa⟩ := Header.context_of v scratch Ka (by decide) Ma
  have Sa := scratch.of_keeps Ka (by decide)
  have candidateA : val32 a.mem g.W (g.array 0) g.words = c := by
    rw [Oa.val32 (fun r mem => by
      simp only [Header.ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
      have h := v.arrayHeader 0
      rcases mem with rfl | rfl | rfl <;> right <;> omega_using [h])
      (by have := scratch.nowrap; have := v.arrayFit (j := 0) (by decide); omega_arith)]
    exact candidate
  have oddLow : w32 a.mem g.W (g.array 0) % 2 = 1 := by
    rw [← LowWord.parity _ _ _ g.words (by have := v.minWidth; unfold Geometry.words; omega_using [this]), candidateA]
    exact odd
  have callerA := caller.keepOuts Ka (by decide) Oa (fun r mem => by
    simp only [Header.ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
    have := v.headerFit
    rcases mem with rfl | rfl | rfl <;> omega_using [this])
  have widthA : Proof.Rsa.Mont.wOf a.mem g.W = g.w := by
    rw [Ma]
    exact Header.width_eq (by have := v.maxWidth; omega_using [this])
  have layoutA : Proof.Rsa.Mont.Layout a.mem g.W capacity := by
    rw [Ma]
    apply Header.layout scratch.edi (by have := v.minWidth; omega_using [this]) (by have := v.maxWidth; omega_using [this])
    · rw [← length]
      have fit := v.arraysFit
      unfold Proof.Rsa.Mont.arrAt Proof.Rsa.Mont.hdrBytes at *
      omega_using [fit]
    · rw [← length]
      exact scratch.nowrap
  refine WP.mono (MontInverse.code_ok Sa
    (by have := v.arrayFit (j := 0) (by decide); have := v.minWidth; unfold Geometry.words at *; omega_arith)
    (by have := v.headerFit; omega_using [this]) (Or.inl (by have := v.arrayHeader 0; omega_using [this])) oddLow)
    fun t ⟨inverse, Ot, Kt⟩ => ?_
  have St := Sa.of_keeps Kt (by decide)
  have Ct : Context g t := by
    refine ⟨Ca.ws.of_keeps Kt, ?_, ?_, ?_, ?_⟩
    · rw [PtrAt, Kt.1 .edi (by decide)]; exact Ca.base
    · rw [Ot.w32 (by decide) (by decide)]; exact Ca.width
    · rw [Ot.w32 (by decide) (by decide)]; exact Ca.stride
    · intro j hj
      rw [Ot.w32 (by omega_using []) (by omega_using [hj])]; exact Ca.pointers j hj
  have Mt : Modulus g c t.mem := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · change (word t.mem g.W 48).toNat = g.w
      rw [Ot.word (by decide) (by decide)]
      exact widthA
    · intro j hj
      change word t.mem g.W (8 * Proof.Rsa.Mont.arrWord j) = _
      rw [Ot.word (Or.inr (by unfold Proof.Rsa.Mont.arrWord; omega_using [])) (by unfold Proof.Rsa.Mont.arrWord; omega_using [hj])]
      simpa only [widthA, Geometry.array, VG.Proof.Mont.word, VG.Proof.Mont.off, Proof.Rsa.Mont.wordAt] using layoutA.2.2.2 j hj
    · rw [Ot.val32 (Or.inr (by have := v.arrayHeader 0; omega_using [this]))
        (by have := scratch.nowrap; have := v.arrayFit (j := 0) (by decide); omega_arith)]
      exact candidateA
    · exact inverse
  refine ⟨⟨Ct, Mt, callerA.keepOuts Kt (by decide) (Outs.of_outside Ot (List.mem_singleton_self _))
    (fun r mem => by obtain rfl := List.mem_singleton.mp mem; have := v.headerFit; omega_using [this]), St⟩, ?_, ?_, ?_⟩
  · exact (Oa.mono (fun r mem => List.mem_append_left _ mem)).trans
      (Outs.of_outside Ot (List.mem_append_right _ (List.mem_singleton_self _)))
  · exact (Ka.mono (by unfold clob; decide)).trans Kt
  · rw [Ot.word (by decide) (by decide), Ma]
    change (Header.headerMemory g.W (s.gpr .edi) g.w s.mem).readW (off g.W 224) 64 = _
    rw [Header.header_stride, Header.zeroHigh]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, VG.Impl.Bignum.X86.PublicContext.stride]
    have := v.maxWidth
    omega_using [this]

theorem code_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (scratch : Scr s g.W g.L) (caller : Caller g capacity p s) (length : g.L = 8 * capacity)
    (candidate : val32 s.mem g.W (g.array 0) g.words = c) (odd : c % 2 = 1) :
    WP isa (VG.Impl.RsaKeyGen.X86.PrepareHeader.code g.w) s fun t =>
      Ready g c capacity p t ∧ Outs g.W ranges s.mem t.mem ∧ Keeps clob s t ∧
      word t.mem g.W 224 = BitVec.ofNat 64 (8 * (g.w + 2)) := by
  unfold VG.Impl.RsaKeyGen.X86.PrepareHeader.code
  rw [Prepared.slot_eq]
  exact codeWith_ok v scratch caller length candidate odd
    (WP.mono (Header.code_ok scratch v.headerFit) fun _ ⟨M, K⟩ => ⟨M, K.mono (by decide)⟩)

/-- `HeaderRt.prepare`: the header at the width that header byte 4 gives. -/
theorem prepareRt_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (scratch : Scr s g.W g.L) (caller : Caller g capacity p s) (length : g.L = 8 * capacity)
    (candidate : val32 s.mem g.W (g.array 0) g.words = c) (odd : c % 2 = 1)
    (len : s.mem.readW (off g.W 4) 32 = BitVec.ofNat 32 (8 * g.w)) :
    WP isa VG.Impl.RsaKeyGen.X86.HeaderRt.prepare s fun t =>
      Ready g c capacity p t ∧ Outs g.W ranges s.mem t.mem ∧ Keeps clob s t ∧
      word t.mem g.W 224 = BitVec.ofNat 64 (8 * (g.w + 2)) := by
  have base : g.array 0 = 256 := by
    simp [Geometry.array, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
  unfold VG.Impl.RsaKeyGen.X86.HeaderRt.prepare
  rw [← base]
  exact codeWith_ok v scratch caller length candidate odd
    (HeaderRt.code_ok scratch v.headerFit v.maxWidth len)

end VG.Proof.RsaKeyGen.X86.PrepareHeader

end

end

/-! # Complete candidate preparation reuses all expensive state across witnesses -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Prepare
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

def clob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi]

def ranges (g : Geometry) : List (Nat × Nat) :=
  PrepareHeader.ranges ++ PreparedR2.ranges g ++ Constants.ranges g ++ Exponent.preparedRanges g

theorem code_full_okAt {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {g : Geometry} (v : g.Valid) (bound : g.w ≤ 64) {s : State} {c capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) {e : Nat} (I : Input g c capacity p s e) (positive : 1 ≤ e) (eLt : e < 64 * g.w) :
    WP isa (VG.Impl.RsaKeyGen.X86.Prepare.codeAt e g.w name mont) s fun t =>
      Data g c capacity p t ∧ Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem t.mem ∧ Keeps clob s t ∧
      WorkspaceFrame g (ranges g) s.mem t.mem := by
  unfold VG.Impl.RsaKeyGen.X86.Prepare.codeAt
  rw [Prepared.slot_eq, Prepared.slot_eq, Prepared.slot_eq]
  refine WP.seq (WP.mono (PrepareHeader.code_ok v I.scratch I.caller length I.candidate I.odd)
    fun a ⟨A, Oa, Ka, strideA⟩ => ?_)
  have minusA : val32 a.mem g.W (g.array 5) g.words = c - 1 := by
    rw [Oa.val32 (fun r mem => by
      simp only [PrepareHeader.ranges, Header.ranges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mem
      have := v.arrayHeader 5
      rcases mem with (rfl | rfl | rfl) | rfl <;> right <;> omega_using [this])
      (by have := I.scratch.nowrap; have := v.arrayFit (j := 5) (by decide); omega_arith)]
    exact I.minusOne
  refine WP.seq (WP.mono (PreparedR2.code_okAt verified noSp stack v length A bound I.odd positive eLt I.top)
    fun b ⟨B, r2B, Fb, Kb, Wb⟩ => ?_)
  have strideB : word b.mem g.W 224 = BitVec.ofNat 64 (8 * (g.w + 2)) := by
    change b.mem.readW (off g.W 224) 64 = _
    rw [Wb.read64 (by have := v.headerFit; omega_using [this]) (fun r mem => by
      simp only [PreparedR2.ranges, PreparedR2.coreRanges, PreparedR2.phaseRanges, montWrites, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with ((rfl | rfl | rfl) | (rfl | rfl | rfl)) | rfl <;>
        exact Or.inl (by have := v.arrayHeader 1; simp only [Geometry.array, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]; omega_using []))]
    exact strideA
  have minusB := (PreparedR2.preserve v Wb (j := 5) (Or.inl rfl)).trans minusA
  refine WP.seq (WP.mono (Constants.code_ok verified noSp stack v length B I.odd (by have := I.large; omega_using [this]) r2B)
    fun d ⟨D, oneD, minusD, Wd, Fd, Kd⟩ => ?_)
  have strideD : word d.mem g.W 224 = BitVec.ofNat 64 (8 * (g.w + 2)) := by
    change d.mem.readW (off g.W 224) 64 = _
    rw [Wd.read64 (by have := v.headerFit; omega_using [this]) (fun r mem => by
      simp only [Constants.ranges, montWrites, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with (rfl | rfl | rfl) | (rfl | rfl) <;> exact Or.inl (by have := v.arrayHeader 1; simp only [Geometry.array, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]; omega_using []))]
    exact strideB
  have minusSaved := (Constants.preserve v Wd (j := 5) (Or.inr (Or.inl rfl))).trans minusB
  have r2D := (Constants.preserve v Wd (j := 4) (Or.inl rfl)).trans r2B
  refine WP.mono (Exponent.ready_ok v D minusSaved I.odd I.large) fun t ⟨T, exponentT, markerT, Ot, Kt⟩ => ?_
  have Fa : Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem a.mem :=
    (workspaceGlobalFrame Oa (fun r mem => by
      simp only [PrepareHeader.ranges, Header.ranges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at mem
      have := v.headerFit
      rcases mem with (rfl | rfl | rfl) | rfl <;> omega_using [this])).mono (fun r mem => List.mem_append_left _ mem)
  have Ft : Frame ([⟨g.W, g.L⟩] ++ [below p 80]) d.mem t.mem :=
    (workspaceGlobalFrame Ot (fun r mem => by
      simp only [Exponent.preparedRanges, Exponent.ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
      have srcFit := Prepared.paddedFit v (j := 0) (by decide)
      have outFit := Prepared.paddedFit v (j := 27) (by decide)
      have := v.headerFit
      rcases mem with rfl | rfl | rfl <;>
        simp only [VG.Impl.RsaKeyGen.X86.Exponent.markerOffset] <;> omega_arith)).mono
      (fun r mem => List.mem_append_left _ mem)
  have Wa : WorkspaceFrame g PrepareHeader.ranges s.mem a.mem := WorkspaceFrame.of_outs I.scratch.nowrap Oa
  have Wt : WorkspaceFrame g (Exponent.preparedRanges g) d.mem t.mem := WorkspaceFrame.of_outs I.scratch.nowrap Ot
  have allWrites : WorkspaceFrame g (ranges g) s.mem t.mem :=
    (((Wa.mono (fun _ mem => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ mem)))).trans
      (Wb.mono (fun _ mem => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ mem))))).trans
      (Wd.mono (fun _ mem => List.mem_append_left _ (List.mem_append_right _ mem)))).trans
      (Wt.mono (fun _ mem => List.mem_append_right _ mem))
  refine ⟨⟨T, ?_, ?_, ?_, exponentT, markerT, ?_⟩, ((Fa.trans Fb).trans Fd).trans Ft, ?_, allWrites⟩
  · exact (Exponent.prepared_preserve v Ot (j := 4) (Or.inl rfl)).trans r2D
  · exact (Exponent.prepared_preserve v Ot (j := 9) (Or.inr (Or.inr (Or.inl rfl)))).trans oneD
  · exact (Exponent.prepared_preserve v Ot (j := 10) (Or.inr (Or.inr (Or.inr rfl)))).trans minusD
  · rw [Ot.word (fun r mem => by
      simp only [Exponent.preparedRanges, Exponent.ranges, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl
      · right; decide
      · left; have := v.arrayHeader 0; omega
      · left; have := v.arrayHeader 27; omega) (by decide)]
    exact strideD
  · exact (((Ka.mono (by unfold clob PrepareHeader.clob; decide)).widen Kb).widen Kd).widen Kt

end VG.Proof.RsaKeyGen.X86.Prepare

end

end

/-! # Preparation preserves candidate arguments and the entropy cursor -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Prepare
open VG VG.Proof.Mont VG.Proof.MillerRabin.X86

def protectedHeader (d bytes : Nat) : Prop :=
  d + bytes ≤ 48 ∨ 128 ≤ d ∧ d + bytes ≤ 136 ∨ 144 ≤ d ∧ d + bytes ≤ 224

theorem ranges_apart {g : Geometry} {d bytes : Nat} (safe : protectedHeader d bytes)
    {r : Nat × Nat} (mem : r ∈ ranges g) : d + bytes ≤ r.1 ∨ r.1 + r.2 ≤ d := by
  simp only [ranges, PrepareHeader.ranges, Header.ranges, PreparedR2.ranges,
    PreparedR2.coreRanges, PreparedR2.phaseRanges, Constants.ranges, montWrites,
    Exponent.preparedRanges, Exponent.ranges, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at mem
  repeat' first
    | (rcases mem with mem | mem)
    | (rcases mem with rfl)
  all_goals
    simp only [Geometry.array, Geometry.words, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes,
      VG.Impl.RsaKeyGen.X86.Exponent.markerOffset]
    unfold protectedHeader at safe
    omega_using [safe]

theorem metadata32 {g : Geometry} (v : g.Valid) {m m' : Mem}
    (W : WorkspaceFrame g (ranges g) m m') {d : Nat} (safe : protectedHeader d 4) :
    m'.readW (off g.W d) 32 = m.readW (off g.W d) 32 := by
  apply W.read32 (by have := v.headerFit; unfold protectedHeader at safe; omega_using [safe, this])
  exact fun _ mem => ranges_apart safe mem

end VG.Proof.RsaKeyGen.X86.Prepare

end

end

/-! # Candidate preparation retains every input needed by the blinded loop -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidatePrepare
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Proof.RsaKeyGen

structure Input (P : MillerRabinLoop.Parameters) (s : State) : Prop where
  prepare : Prepare.Input P.g P.candidate P.capacity P.p s P.seed
  readable : InRegions (s.rd ++ s.wr) (P.rand.setWidth 64) P.randLen
  entropy : Spec.Rsa.bytesAt s.mem (P.rand.setWidth 64) P.randLen = P.entropy
  randPtr : s.mem.readW (off P.g.W 28) 32 = P.rand
  randLength : w32 s.mem P.g.W 32 = P.randLen
  used : w32 s.mem P.g.W 152 = P.start

structure Ready (P : MillerRabinLoop.Parameters) (s : State) : Prop where
  prepared : Prepare.Data P.g P.candidate P.capacity P.p s
  readable : InRegions (s.rd ++ s.wr) (P.rand.setWidth 64) P.randLen
  entropy : Spec.Rsa.bytesAt s.mem (P.rand.setWidth 64) P.randLen = P.entropy
  randPtr : s.mem.readW (off P.g.W 28) 32 = P.rand
  randLength : w32 s.mem P.g.W 32 = P.randLen
  used : w32 s.mem P.g.W 152 = P.start

theorem code_ok {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {P : MillerRabinLoop.Parameters} (v : P.Valid) (bound : P.g.w ≤ 64) {s : State} (I : Input P s) :
    WP isa (VG.Impl.RsaKeyGen.X86.Prepare.codeAt P.seed P.g.w name mont) s fun t =>
      Ready P t ∧ WorkspaceFrame P.g (Prepare.ranges P.g) s.mem t.mem ∧
      Frame ([⟨P.g.W, P.g.L⟩] ++ [below P.p 80]) s.mem t.mem ∧ Keeps Prepare.clob s t := by
  refine WP.mono (Prepare.code_full_okAt verified noSp stack v.geometry bound v.length I.prepare v.seedPos v.seedLt)
    fun t ⟨T, F, K, W⟩ => ?_
  refine ⟨⟨T, ?_, ?_, ?_, ?_, ?_⟩, W, F, K⟩
  · rw [K.2.1, K.2.2]; exact I.readable
  · rw [frame_bytesAt F (by
      intro r mem
      simp only [List.mem_append, List.mem_singleton] at mem
      rcases mem with rfl | rfl
      · exact v.randSeparate
      · exact v.randStackFar.sub_right (below_sub (by decide) v.low)) (by have := v.randLenFit; omega_using [this])]
    exact I.entropy
  · rw [Prepare.metadata32 v.geometry W (d := 28) (by unfold Prepare.protectedHeader; omega_using [])]
    exact I.randPtr
  · rw [w32, Prepare.metadata32 v.geometry W (d := 32) (by unfold Prepare.protectedHeader; omega_using [])]
    exact I.randLength
  · rw [w32, Prepare.metadata32 v.geometry W (d := 152) (by unfold Prepare.protectedHeader; omega_using [])]
    exact I.used

end VG.Proof.RsaKeyGen.X86.CandidatePrepare
