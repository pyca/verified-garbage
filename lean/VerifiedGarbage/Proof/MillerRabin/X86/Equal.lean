module

public import VerifiedGarbage.Proof.MillerRabin.X86.Context
public import VerifiedGarbage.Impl.MillerRabin.X86.Ops
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.MillerRabin.X86.Copy
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Impl.MillerRabin.X86.Layout
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power

/-! ### `MillerRabin.X86.EqualLoop`, which this module and modules that import it used -/

section

/-! # A runtime comparison accumulates every native-word difference -/

-- Formerly `VerifiedGarbage/Proof/MillerRabin/Equality32.lean`, which only this module imported.
section

/-! # Native-word XOR accumulation is equality of the represented integers -/

@[expose] public section
namespace VG.Proof.MillerRabin
open VG VG.Proof.Mont

def xorWords (m : Mem) (W : Addr) (a b : Nat) : Nat → BitVec 32
  | 0 => 0#32
  | n + 1 => (m.readW (off W a) 32 ^^^ m.readW (off W b) 32) ||| xorWords m W (a + 4) (b + 4) n

theorem val32_cons_eq (m : Mem) (W : Addr) (a b n : Nat) :
    val32 m W a (n + 1) = val32 m W b (n + 1) ↔
      w32 m W a = w32 m W b ∧ val32 m W (a + 4) n = val32 m W (b + 4) n := by
  have lowA : w32 m W a < 2 ^ 32 := (m.readW (off W a) 32).isLt
  have lowB : w32 m W b < 2 ^ 32 := (m.readW (off W b) 32).isLt
  change w32 m W a + 2 ^ 32 * val32 m W (a + 4) n =
    w32 m W b + 2 ^ 32 * val32 m W (b + 4) n ↔ _
  omega_using [lowA, lowB]

theorem xorWords_zero (m : Mem) (W : Addr) (a b n : Nat) :
    xorWords m W a b n = 0#32 ↔ val32 m W a n = val32 m W b n := by
  induction n generalizing a b with
  | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | succ n ih =>
    rw [xorWords, BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff, ih, val32_cons_eq]
    constructor
    · rintro ⟨H, V⟩
      exact ⟨congrArg BitVec.toNat H, V⟩
    · rintro ⟨H, V⟩
      exact ⟨BitVec.eq_of_toNat_eq H, V⟩

theorem xorWords_succ (m : Mem) (W : Addr) (a b n : Nat) :
    xorWords m W a b (n + 1) = xorWords m W a b n |||
      (m.readW (off W (a + 4 * n)) 32 ^^^ m.readW (off W (b + 4 * n)) 32) := by
  induction n generalizing a b with
  | zero => simp only [xorWords, Nat.mul_zero, Nat.add_zero, BitVec.or_zero, BitVec.zero_or]
  | succ n ih =>
    change (m.readW (off W a) 32 ^^^ m.readW (off W b) 32) |||
      xorWords m W (a + 4) (b + 4) (n + 1) =
      ((m.readW (off W a) 32 ^^^ m.readW (off W b) 32) ||| xorWords m W (a + 4) (b + 4) n) |||
        (m.readW (off W (a + 4 * (n + 1))) 32 ^^^ m.readW (off W (b + 4 * (n + 1))) 32)
    rw [ih (a + 4) (b + 4), BitVec.or_assoc]
    rw [show a + 4 + 4 * n = a + 4 * (n + 1) by omega_using [],
      show b + 4 + 4 * n = b + 4 * (n + 1) by omega_using []]

end VG.Proof.MillerRabin
end

end

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Bignum.X86.PublicRt (countLoop count1_zf ptr4)

def equalBody : List Instr :=
  [.mov .eax (.mem (at_ .ebp 0)), .alu .xor .eax (.mem (at_ .ecx 0)),
    .alu .or .ebx (.reg .eax), .alu .add .ebp (.imm 4), .alu .add .ecx (.imm 4),
    .alu .sub .esi (.imm 1)]

theorem equalLoop_ok {s : State} {W : Addr} {L x y N : Nat} (hw : Ws s W L)
    (positive : 0 < N) (aFit : x + 4 * N ≤ L) (bFit : y + 4 * N ≤ L)
    (aPtr : PtrAt s W .ebp x) (bPtr : PtrAt s W .ecx y)
    (count : (s.gpr .esi).toNat = N) (zero : s.gpr .ebx = 0#32) :
    WP isa (.loop (.block equalBody) .ne) s fun t =>
      t.mem = s.mem ∧ t.gpr .ebx = xorWords s.mem W x y N ∧
      Keeps [.eax, .ebx, .ebp, .ecx, .esi] s t := by
  refine WP.mono (countLoop positive (fun i t => Keeps [.eax, .ebx, .ebp, .ecx, .esi] s t ∧
    PtrAt t W .ebp (x + 4 * i) ∧ PtrAt t W .ecx (y + 4 * i) ∧
    (t.gpr .esi).toNat = N - i ∧ t.mem = s.mem ∧ t.gpr .ebx = xorWords s.mem W x y i) ?_
    ⟨Keeps.refl _ _, by simpa using aPtr, by simpa using bPtr, by simpa using count, rfl, zero⟩)
    fun t ⟨K, _, _, _, M, V⟩ => ⟨M, V, K⟩
  rintro i t index ⟨K, bp, cx, countI, M, V⟩
  have ht := hw.of_keeps K
  unfold equalBody
  refine wp_movS (readSrc_ptr ht bp (d := 0) (by omega_using [aFit, index])) fun a A _ => ?_
  have cxA : PtrAt a W .ecx (y + 4 * i) := by rw [PtrAt, A.other .ecx (by decide)]; exact cx
  refine wp_logicS (.inr rfl) (readSrc_ptr (ht.of_keeps A.keeps) cxA (d := 0) (by omega_using [bFit, index])) fun b B => ?_
  refine wp_orS rfl fun c C => ?_
  refine wp_addS rfl fun d D _ => wp_addS rfl fun e E _ => wp_subZ rfl fun u U Z => WP.block_nil ?_
  have esiE : e.gpr .esi = t.gpr .esi := by
    rw [E.other .esi (by decide), D.other .esi (by decide), C.other .esi (by decide),
      B.other .esi (by decide), A.other .esi (by decide)]
  obtain ⟨nextCount, last⟩ := count1_zf countI index
  refine ⟨⟨(((((K.widen A.keeps).widen B.keeps).widen C.keeps).widen D.keeps).widen E.keeps).widen U.keeps,
    ?_, ?_, by rw [U.gpr, esiE]; exact nextCount, ?_, ?_⟩, by rw [Z, esiE, last]⟩
  · rw [PtrAt, U.other .ebp (by decide), E.other .ebp (by decide), D.gpr,
      C.other .ebp (by decide), B.other .ebp (by decide), A.other .ebp (by decide)]
    exact ptr4 bp
  · rw [PtrAt, U.other .ecx (by decide), E.gpr, D.other .ecx (by decide),
      C.other .ecx (by decide), B.other .ecx (by decide), A.other .ecx (by decide)]
    exact ptr4 cx
  · rw [U.mem, E.mem, D.mem, C.mem, B.mem, A.mem, M]
  · rw [U.other .ebx (by decide), E.other .ebx (by decide), D.other .ebx (by decide),
      C.gpr, B.other .ebx (by decide), A.other .ebx (by decide), V,
      B.gpr, A.gpr, A.mem, M, Nat.add_zero, Nat.add_zero, xorWords_succ]
    rfl

end VG.Proof.MillerRabin.X86

end

end

/-! # Full runtime-width equality of two prepared arrays -/

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/EqualFinish.lean`, which only this module imported.
section

/-! # Branch-free conversion of a word comparison into a stored bit -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem equalFinish_ok {s : State} {W : Addr} {L result : Nat} (hw : Ws s W L)
    (base : PtrAt s W .edi 0) (fit : result + 4 ≤ L) :
    WP isa (.block [.mov .eax (.imm 0), .alu .sub .ebx (.imm 1),
      .alu .adc .eax (.imm 0), .store (slot result) .eax]) s fun t =>
      w32 t.mem W result = (decide (s.gpr .ebx = 0#32)).toNat ∧
      Outside W result 4 s.mem t.mem ∧ Keeps [.eax, .ebx] s t := by
  refine wp_movS rfl fun a A _ => wp_subS rfl fun b B cf => wp_adcS rfl cf fun c C _ => ?_
  have K : Keeps [.eax, .ebx] s c := ((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps
  have hc := hw.of_keeps K
  have baseC : PtrAt c W .edi 0 := by rw [PtrAt, K.1 .edi (by decide)]; exact base
  refine wp_storeS (ea_ptr hc baseC (d := result) (by omega))
    (ws_write hc (y := 0 + result) (n := 4) (by omega)) fun t T => WP.block_nil ?_
  have M : c.mem = s.mem := C.mem.trans (B.mem.trans A.mem)
  have value : c.gpr .eax = BitVec.ofNat 32 (decide (s.gpr .ebx = 0#32)).toNat := by
    rw [C.gpr, B.other .eax (by decide), A.gpr, A.other .ebx (by decide)]
    have test : decide ((s.gpr .ebx).toNat < (1 : BitVec 32).toNat) = decide (s.gpr .ebx = 0#32) := by
      have iffZero : (s.gpr .ebx).toNat < (1 : BitVec 32).toNat ↔ s.gpr .ebx = 0#32 := by
        rw [← BitVec.toNat_inj]
        change (s.gpr .ebx).toNat < 1 ↔ (s.gpr .ebx).toNat = 0
        omega
      simp only [iffZero]
    rw [test]
    cases decide (s.gpr .ebx = 0#32) <;> rfl
  refine ⟨?_, ?_, K.widen (T.keeps [])⟩
  · rw [T.mem, Nat.zero_add, w32_write_self, value, BitVec.toNat_ofNat]
    cases decide (s.gpr .ebx = 0#32) <;> rfl
  · rw [T.mem, Nat.zero_add, M]
    exact writeW32_outside _ _ _ (by have := hw.nowrap; omega)

end VG.Proof.MillerRabin.X86
end

end

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem equal_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s)
    (result a b : Nat) (resultFit : result + 4 ≤ g.L) (aIndex : a < 28) (bIndex : b < 28) :
    WP isa (equal result a b) s fun t =>
      w32 t.mem g.W result =
        (decide (val32 s.mem g.W (g.array a) g.words = val32 s.mem g.W (g.array b) g.words)).toNat ∧
      Outside g.W result 4 s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold equal
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (C.ptr v a aIndex .ebp (by decide) (by decide))
    fun u ⟨P, M, K⟩ => ?_))
  have Cu := C.keepMem K (by decide) M
  refine WP.block_append (WP.mono (Cu.ptr v b bIndex .ecx (by decide) (by decide))
    fun b₁ ⟨Pb, Mb, Kb⟩ => ?_)
  have Cb := Cu.keepMem Kb (by decide) Mb
  refine WP.block_append (WP.mono (words_ok v Cb) fun c ⟨Count, Mc, Kc⟩ => ?_)
  refine wp_movS rfl fun d D _ => WP.block_nil ?_
  have keep : Keeps [.ebx, .ecx, .edx, .ebp, .esi] s d :=
    (((K.mono (by decide)).trans (Kb.mono (by decide))).trans (Kc.mono (by decide))).widen D.keeps
  have mem : d.mem = s.mem := D.mem.trans (Mc.trans (Mb.trans M))
  have bp : PtrAt d g.W .ebp (g.array a) := by
    rw [PtrAt, D.other .ebp (by decide), Kc.1 .ebp (by decide), Kb.1 .ebp (by decide)]; exact P
  have cx : PtrAt d g.W .ecx (g.array b) := by
    rw [PtrAt, D.other .ecx (by decide), Kc.1 .ecx (by decide)]; exact Pb
  refine WP.seq (WP.mono (equalLoop_ok (C.ws.of_keeps keep)
    (by have := v.minWidth; unfold Geometry.words; omega_using [this]) (v.arrayFit aIndex) (v.arrayFit bIndex)
    bp cx (by rw [D.other .esi (by decide)]; exact Count) D.gpr) fun e ⟨Me, V, Ke⟩ => ?_)
  have Kall : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s e :=
    (keep.mono (by decide)).trans (Ke.mono (by decide))
  have Ce := C.keepMem Kall (by decide) (Me.trans mem)
  refine WP.mono (equalFinish_ok Ce.ws Ce.base resultFit) fun t ⟨Value, O, Kt⟩ => ?_
  simp only [V, mem, xorWords_zero] at Value
  rw [Me, mem] at O
  exact ⟨Value, O, Kall.widen Kt⟩

end VG.Proof.MillerRabin.X86
