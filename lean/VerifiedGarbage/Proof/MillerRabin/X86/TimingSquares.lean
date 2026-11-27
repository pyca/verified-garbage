module

public import VerifiedGarbage.Proof.MillerRabin.X86.StageSlots
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingMultiply
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBase
import VerifiedGarbage.Proof.MillerRabin.X86.TimingPointers
public import VerifiedGarbage.Proof.MillerRabin.X86.Data
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.MillerRabin.Word32
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Impl.MillerRabin.X86.Ops
public import VerifiedGarbage.Proof.MillerRabin.X86.MontFrame
import VerifiedGarbage.Proof.MillerRabin.X86.Caller
import VerifiedGarbage.Proof.MillerRabin.X86.Multiply
public import VerifiedGarbage.Proof.MillerRabin.X86.Context
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.MillerRabin.X86.Copy
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Impl.MillerRabin.X86.Layout
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
public import VerifiedGarbage.Proof.MillerRabin.X86.Modulus

/-! ### `MillerRabin.X86.DataScalar`, which this module and modules that import it used -/

section

/-! # Updating a scratch word preserves all known array and other scalar values -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont

theorem Data.afterScalar {g : Geometry} (v : g.Valid) {A : Nat → Nat} {Js : List Nat}
    {V : Nat → BitVec 32} {Ds : List Nat} {s t : State} (D : Data g A Js V Ds s)
    (C : Context g t) (d : Nat) (scratch : scratchWord d) (value : BitVec 32)
    (O : Outside g.W d 4 s.mem t.mem) (stored : t.mem.readW (off g.W d) 32 = value) :
    Data g A Js (setAt V d value) (d :: Ds) t := by
  have fit := scratch_fit scratch
  refine ⟨C, ?_, ?_⟩
  · intro j known
    obtain ⟨index, read⟩ := D.arrayValues j known
    have header := v.arrayHeader j
    refine ⟨index, ?_⟩
    rw [O.val32 (by omega_using [fit, header]) (by have := v.arrayFit index; have := C.ws.nowrap; omega_arith), read]
  · intro e known
    by_cases same : e = d
    · subst e
      exact ⟨scratch, by rw [setAt_self]; exact stored⟩
    · have old : e ∈ Ds := by
        rcases List.mem_cons.mp known with bad | old
        · exact False.elim (same bad)
        · exact old
      obtain ⟨es, read⟩ := D.slotValues e old
      have apart := scratch_apart es scratch same
      have bound := scratch_fit es
      refine ⟨es, ?_⟩
      have unchanged := BitVec.eq_of_toNat_eq (O.w32 (d := e) (by omega_using [apart]) (by omega_using [bound]))
      rw [unchanged, read, setAt_other V value same]

end VG.Proof.MillerRabin.X86

end

end

/-! ### `MillerRabin.X86.ModulusKeep`, which this module and modules that import it used -/

section

/-! # Scratch updates and array copies keep the candidate prepared -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.Proof.Mont

theorem Modulus.keepScalar {g : Geometry} (v : g.Valid) {c d : Nat} {m m' : Mem}
    (M : Modulus g c m) (nowrap : g.W.toNat + g.L ≤ 2 ^ 32)
    (scratch : scratchWord d) (O : Outside g.W d 4 m m') : Modulus g c m' := by
  have bound := scratch_fit scratch
  refine M.keep v (WorkspaceFrame.of_outs nowrap (Outs.of_outside O (List.mem_singleton_self _))) ?_ ?_
  · intro r mem
    obtain rfl := List.mem_singleton.mp mem
    unfold scratchWord at scratch
    dsimp only
    omega_using [scratch]
  · intro r mem
    obtain rfl := List.mem_singleton.mp mem
    right
    exact Nat.le_trans bound (v.arrayHeader 0)

theorem Modulus.keepArray {g : Geometry} (v : g.Valid) {c j : Nat} {m m' : Mem}
    (M : Modulus g c m) (nowrap : g.W.toNat + g.L ≤ 2 ^ 32)
    (notMod : 0 < j) (O : Outside g.W (g.array j) (4 * g.words) m m') : Modulus g c m' := by
  refine M.keep v (WorkspaceFrame.of_outs nowrap (Outs.of_outside O (List.mem_singleton_self _))) ?_ ?_
  · intro r mem
    obtain rfl := List.mem_singleton.mp mem
    exact Or.inl (Nat.le_trans (by decide) (v.arrayHeader j))
  · intro r mem
    obtain rfl := List.mem_singleton.mp mem
    exact Or.inl (g.arrayBefore notMod)

end VG.Proof.MillerRabin.X86

end

end

/-! ### `MillerRabin.X86.TimingPrivate`, which this module and modules that import it used -/

section

/-! # Timing composition retains independent secret values for the two runs -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Dsa.X86

/-- The shared geometry is public; each execution retains its own private state. -/
def Two {α : Type} (g : Geometry) (F : α → State → Prop) (s t : State) : Prop :=
  Pair g [.edi] s t ∧ (∃ σ, F σ s) ∧ (∃ σ, F σ t)

theorem private_lift {α : Type} {g : Geometry} {F G : α → State → Prop} {code : Prog isa}
    (trace : RelCT isa (Pair g [.edi]) code (Pair g [.edi]))
    (step : ∀ σ s, F σ s → WP isa code s (G σ)) :
    RelCT isa (Two g F) code (Two g G) := by
  intro s t tr ur u z ⟨H, ⟨σ, S⟩, ⟨ρ, T⟩⟩ E B
  obtain ⟨same, P⟩ := trace _ _ _ _ _ _ H E B
  exact ⟨same, P, ⟨σ, wp_result (step σ s S) E⟩, ⟨ρ, wp_result (step ρ t T) B⟩⟩

theorem private_count_loop {α : Type} {g : Geometry} {F : Nat → α → State → Prop} {code : Prog isa}
    (step : ∀ q, 0 < q → RelCT isa (Two g (F q)) code fun s t =>
      Two g (F (q - 1)) s t ∧ isa.eval .ne s = some (decide (1 < q)) ∧ isa.eval .ne t = some (decide (1 < q)))
    (q : Nat) (positive : 0 < q) :
    RelCT isa (Two g (F q)) (.loop code .ne) (Two g (F 0)) := by
  have loop := RelCT.loop (M := isa) (body := code) (c := .ne)
    (I := fun q s t => 0 < q ∧ Two g (F q) s t) (Q := Two g (F 0)) ?_ q
  · exact loop.mono (fun _ _ H => ⟨positive, H⟩) (fun _ _ H => H)
  · intro n s t tr ur u z ⟨pos, H⟩ E B
    obtain ⟨same, T, Eu, Ez⟩ := step n pos _ _ _ _ _ _ H E B
    refine ⟨same, Eu.trans Ez.symm, ?_, ?_⟩
    · intro exit
      have small : ¬ 1 < n := by rw [Eu] at exit; simpa using exit
      have eq : n - 1 = 0 := by omega_using [small]
      rw [eq] at T
      exact T
    · intro next
      have more : 1 < n := by rw [Eu] at next; simpa using next
      exact ⟨n - 1, by omega_using [pos], by omega_using [more], T⟩

end VG.Proof.MillerRabin.X86

end

end

/-! ### `MillerRabin.X86.SquareStep`, which this module and modules that import it used -/

section

/-! ### `MillerRabin.X86.Equal`, which this module and modules that import it used -/

section

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

end

end

/-! ### `MillerRabin.X86.RoundArrayFrame`, which this module and modules that import it used -/

section

/-! # Prepared products and table copies stay within the reviewed round footprint -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.Proof.Mont

def roundArray (j : Nat) : Prop :=
  j = 2 ∨ j = 3 ∨ j = 5 ∨ j = 6 ∨ j = 8 ∨ 11 ≤ j ∧ j < 27

theorem array_roundRange (g : Geometry) {j n : Nat} (allowed : roundArray j)
    (size : n ≤ 8 * (g.w + 2)) :
    ∃ R ∈ roundWrites g, R.1 ≤ g.array j ∧ g.array j + n ≤ R.1 + R.2 := by
  unfold roundArray at allowed
  rcases allowed with rfl | rfl | rfl | rfl | rfl | table
  · refine ⟨(g.array 2, 16 * (g.w + 2)), by simp [roundWrites], Nat.le_refl _, ?_⟩
    dsimp only
    omega_using [size]
  · refine ⟨(g.array 2, 16 * (g.w + 2)), by simp [roundWrites], ?_, ?_⟩ <;>
      unfold Geometry.array Proof.Rsa.Mont.arrAt Proof.Rsa.Mont.hdrBytes <;> omega_arith
  · refine ⟨(g.array 5, 16 * (g.w + 2)), by simp [roundWrites], Nat.le_refl _, ?_⟩
    dsimp only
    omega_using [size]
  · refine ⟨(g.array 5, 16 * (g.w + 2)), by simp [roundWrites], ?_, ?_⟩ <;>
      unfold Geometry.array Proof.Rsa.Mont.arrAt Proof.Rsa.Mont.hdrBytes <;> omega_arith
  · refine ⟨(g.array 8, 8 * (g.w + 2)), by simp [roundWrites], Nat.le_refl _, ?_⟩
    dsimp only
    omega_using [size]
  · have lower := Nat.mul_le_mul_right (8 * (g.w + 2)) table.1
    have upper := g.strideBefore table.2
    refine ⟨(g.array 11, 128 * (g.w + 2)), by simp [roundWrites], ?_, ?_⟩ <;>
      unfold Geometry.array Proof.Rsa.Mont.arrAt Proof.Rsa.Mont.hdrBytes at * <;> omega_arith

theorem array_roundFrame {g : Geometry} {j : Nat} {m m' : Mem}
    (nowrap : g.W.toNat + g.L ≤ 2 ^ 32) (allowed : roundArray j)
    (O : Outside g.W (g.array j) (4 * g.words) m m') :
    WorkspaceFrame g (roundWrites g) m m' := by
  apply (WorkspaceFrame.of_outs nowrap (Outs.of_outside O (List.mem_singleton_self _))).cover
  intro r mem
  obtain rfl := List.mem_singleton.mp mem
  exact array_roundRange g allowed (by unfold Geometry.words; omega_using [])

theorem mont_roundFrame {g : Geometry} {m m' : Mem}
    (O : WorkspaceFrame g (montWrites g 6) m m') : WorkspaceFrame g (roundWrites g) m m' := by
  apply O.cover
  intro r mem
  simp only [montWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl
  · exact array_roundRange g (j := 2) (by unfold roundArray; simp) (Nat.le_refl _)
  · exact array_roundRange g (j := 3) (by unfold roundArray; simp) (Nat.le_refl _)
  · exact array_roundRange g (j := 6) (by unfold roundArray; simp) (Nat.le_refl _)

end VG.Proof.MillerRabin.X86

end

end

/-! ### `MillerRabin.X86.StageMultiply`, which this module and modules that import it used -/

section

/-! # A prepared Montgomery product composes with the next round stage -/

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/DataMultiply.lean`, which only this module imported.
section

/-! # A prepared product updates only the accumulator's known value -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Data.multiply {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {A : Nat → Nat} {Js : List Nat}
    {V : Nat → BitVec 32} {Ds : List Nat} {s : State} (D : Data g A Js V Ds s)
    {capacity b c : Nat} {p : BitVec 32} (length : g.L = 8 * capacity)
    (M : Modulus g c s.mem) (C : Caller g capacity p s)
    (right : Proof.Rsa.Mont.Operand b) (odd : c % 2 = 1) (rightLt : A b < c)
    (bKnown : b ∈ Js) (yKnown : 6 ∈ Js) (noScratch : ∀ j ∈ Js, j ≠ 2 ∧ j ≠ 3) :
    WP isa (mulY name code b) s fun t =>
      Data g (setAt A 6 (Word32.mm c g.w (A 6) (A b))) Js V Ds t ∧
      Modulus g c t.mem ∧ Caller g capacity p t ∧
      WorkspaceFrame g (montWrites g 6) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx] s t := by
  have bv := D.arrayValues b bKnown
  have yv := D.arrayValues 6 yKnown
  refine WP.mono (mulY_ok verified noSp stack v D.context length M right odd
    (by rw [bv.2]; exact rightLt) C.readLen (by rw [C.sp]; exact C.low)
    (by rw [C.sp]; exact C.stackFar)) fun t ⟨Value, O, K, Ct, Mt, F⟩ => ?_
  have caller := C.keepFrame K (by decide) (by rw [C.sp] at F; exact F)
  refine ⟨⟨Ct, ?_, ?_⟩, Mt, caller, O, K⟩
  · intro j known
    obtain ⟨index, read⟩ := D.arrayValues j known
    by_cases same : j = 6
    · subst j
      exact ⟨index, by rw [setAt_self, Value, yv.2, bv.2]⟩
    · have noScr := noScratch j known
      refine ⟨index, ?_⟩
      rw [O.val32 (v.arrayFit index) (by
        intro r mem
        simp only [montWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl | rfl
        · exact g.readApart noScr.1
        · exact g.readApart noScr.2
        · exact g.readApart same), read, setAt_other A _ same]
  · intro d known
    obtain ⟨scratch, read⟩ := D.slotValues d known
    refine ⟨scratch, ?_⟩
    rw [O.read32 (by have := scratch_fit scratch; have := v.headerFit; omega) (by
      intro r mem
      simp only [montWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl
      · exact Or.inl (Nat.le_trans (scratch_fit scratch) (v.arrayHeader 2))
      · exact Or.inl (Nat.le_trans (scratch_fit scratch) (v.arrayHeader 3))
      · exact Or.inl (Nat.le_trans (scratch_fit scratch) (v.arrayHeader 6))), read]

end VG.Proof.MillerRabin.X86
end

end

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Stage.multiply {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p A Js V Ds s) (length : g.L = 8 * capacity)
    (b : Nat) (right : Proof.Rsa.Mont.Operand b) (odd : c % 2 = 1) (rightLt : A b < c)
    (bKnown : b ∈ Js) (yKnown : aY ∈ Js) :
    WP isa (mulY name code b) s fun t =>
      Stage g capacity c p (setAt A aY (Word32.mm c g.w (A aY) (A b))) Js V Ds t ∧
      WorkspaceFrame g (montWrites g aY) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx] s t := by
  refine WP.mono (S.data.multiply verified noSp stack v length S.modulus S.caller right odd
    rightLt bKnown yKnown S.noScratch) fun t ⟨D, M, C, O, K⟩ => ?_
  exact ⟨⟨D, M, C, S.noScratch⟩, O, K⟩

end VG.Proof.MillerRabin.X86

end

end

/-! ### `MillerRabin.X86.StageEqual`, which this module and modules that import it used -/

section

/-! # Equality records a flag while retaining the prepared call invariants -/

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/DataEqual.lean`, which only this module imported.
section

/-! # A prepared-array comparison records its exact equality bit -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Data.equal {g : Geometry} (v : g.Valid) {A : Nat → Nat} {Js : List Nat}
    {V : Nat → BitVec 32} {Ds : List Nat} {s : State} (D : Data g A Js V Ds s)
    (d a b : Nat) (scratch : scratchWord d) (aKnown : a ∈ Js) (bKnown : b ∈ Js) :
    WP isa (equal d a b) s fun t =>
      Data g A Js (setAt V d (BitVec.ofNat 32 (decide (A a = A b)).toNat)) (d :: Ds) t ∧
      Outside g.W d 4 s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have av := D.arrayValues a aKnown
  have bv := D.arrayValues b bKnown
  have bound := scratch_fit scratch
  refine WP.mono (equal_ok v D.context d a b (by have := v.headerFit; omega) av.1 bv.1)
    fun t ⟨Value, O, K⟩ => ?_
  have C := D.context.keepScalar K (by decide) O scratch
  rw [av.2, bv.2] at Value
  have stored : t.mem.readW (off g.W d) 32 = BitVec.ofNat 32 (decide (A a = A b)).toNat := by
    apply BitVec.eq_of_toNat_eq
    change w32 t.mem g.W d = _
    rw [Value]
    cases decide (A a = A b) <;> rfl
  exact ⟨D.afterScalar v C d scratch _ O stored, O, K⟩

end VG.Proof.MillerRabin.X86
end

end

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Stage.equal {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p A Js V Ds s)
    (d a b : Nat) (scratch : scratchWord d) (aKnown : a ∈ Js) (bKnown : b ∈ Js) :
    WP isa (equal d a b) s fun t =>
      Stage g capacity c p A Js (setAt V d (BitVec.ofNat 32 (decide (A a = A b)).toNat)) (d :: Ds) t ∧
      Outside g.W d 4 s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  refine WP.mono (S.data.equal v d a b scratch aKnown bKnown) fun t ⟨D, O, K⟩ => ?_
  refine ⟨⟨D, S.modulus.keepScalar v S.data.context.ws.nowrap scratch O, ?_, S.noScratch⟩, O, K⟩
  exact S.caller.keepOuts K (by decide) (Outs.of_outside O (List.mem_singleton_self _)) (by
    intro r mem
    obtain rfl := List.mem_singleton.mp mem
    exact Nat.le_trans (scratch_fit scratch) v.headerFit)

end VG.Proof.MillerRabin.X86

end

end

/-! # One prepared square, equality check and masked flag update -/

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/StageSquareControl.lean`, which only this module imported.
section

/-! # A square's public countdown keeps the complete prepared stage usable -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Stage.squareFlag {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p A Js V Ds s)
    {q r : Nat} (positive : 0 < q) (qBound : q < 2 ^ 31) (rBound : r < 2 ^ 31) (E F : Bool)
    (known : ∀ d ∈ [sSquares, sThreshold, sEq2, sFlag], d ∈ Ds)
    (count : V sSquares = BitVec.ofNat 32 q) (threshold : V sThreshold = BitVec.ofNat 32 r)
    (eqBit : V sEq2 = BitVec.ofNat 32 E.toNat) (flag : V sFlag = BitVec.ofNat 32 F.toNat) :
    WP isa (.block squareFlag) s fun t =>
      Stage g capacity c p A Js (squareSlots V q r E F) ([sFlag, sSquares] ++ Ds) t ∧
      t.zf = some (decide (q = 1)) ∧ WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx] s t := by
  have scratch : ∀ d ∈ [sFlag, sSquares], scratchWord d := by
    intro d mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · unfold scratchWord sFlag; simp
    · unfold scratchWord sSquares; simp
  refine WP.mono (S.data.squareFlag v positive qBound rBound E F known count threshold eqBit flag)
    fun t ⟨D, Z, O, K⟩ => ?_
  exact ⟨S.afterSlots v D [sFlag, sSquares] scratch O K (by decide), Z,
    scalar_roundFrame S.data.context.ws.nowrap scratch O, K⟩

end VG.Proof.MillerRabin.X86
end

end

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem squareStep_ok {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity c q r : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p A Js V Ds s) (length : g.L = 8 * capacity)
    (odd : c % 2 = 1) (Ylt : A aY < c) (yKnown : aY ∈ Js) (minusKnown : aMinusOne ∈ Js)
    (positive : 0 < q) (qBound : q < 2 ^ 31) (rBound : r < 2 ^ 31) (F : Bool)
    (known : ∀ d ∈ [sSquares, sThreshold, sFlag], d ∈ Ds)
    (count : V sSquares = BitVec.ofNat 32 q) (threshold : V sThreshold = BitVec.ofNat 32 r)
    (flag : V sFlag = BitVec.ofNat 32 F.toNat) :
    let Y := Word32.mm c g.w (A aY) (A aY)
    let E := decide (Y = A aMinusOne)
    WP isa (squareStep name code) s fun t =>
      Stage g capacity c p (setAt A aY Y) Js
        (squareSlots (setAt V sEq2 (BitVec.ofNat 32 E.toNat)) q r E F)
        ([sFlag, sSquares] ++ sEq2 :: Ds) t ∧
      t.zf = some (decide (q = 1)) ∧ WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  dsimp only
  change WP isa (.seq (mulY name code aY)
    (.seq (equal sEq2 aY aMinusOne) (.block squareFlag))) s _
  refine WP.seq (WP.mono (S.multiply verified noSp stack v length aY
    (by change 6 < 8 ∧ 6 ≠ 2 ∧ 6 ≠ 3; decide) odd Ylt yKnown yKnown) fun a ⟨Sa, Oa, Ka⟩ => ?_)
  refine WP.seq (WP.mono (Sa.equal v sEq2 aY aMinusOne (by unfold scratchWord sEq2; simp)
    yKnown minusKnown) fun b ⟨Sb, Ob, Kb⟩ => ?_)
  refine WP.mono (Sb.squareFlag v positive qBound rBound
    (decide (Word32.mm c g.w (A aY) (A aY) = A aMinusOne)) F ?_ ?_ ?_ ?_ ?_)
    fun t ⟨St, Z, Ot, Kt⟩ => ?_
  · intro d mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl
    · exact List.mem_cons_of_mem _ (known _ (by simp))
    · exact List.mem_cons_of_mem _ (known _ (by simp))
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (known _ (by simp))
  · exact count
  · exact threshold
  · rfl
  · exact flag
  · refine ⟨St, Z, ?_, ((Ka.mono (by decide)).trans Kb).trans (Kt.mono (by decide))⟩
    have EqFrame : WorkspaceFrame g (roundWrites g) a.mem b.mem :=
      scalar_roundFrame Sa.data.context.ws.nowrap (rs := [sEq2]) (by
        intro d mem
        obtain rfl := List.mem_singleton.mp mem
        unfold scratchWord sEq2; simp) (Outs.of_outside Ob (List.mem_singleton_self _))
    exact ((mont_roundFrame Oa).trans EqFrame).trans Ot

end VG.Proof.MillerRabin.X86

end

end

/-! ### `MillerRabin.X86.TimingSquareStep`, which this module and modules that import it used -/

section

/-! ### `MillerRabin.X86.TimingEqual`, which this module and modules that import it used -/

section

/-! ### `MillerRabin.X86.TimingReadonly`, which this module and modules that import it used -/

section

/-! # Retain the prepared geometry across read-only timing blocks -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Dsa.X86

theorem readonly_relCT {g : Geometry} {code : Prog isa} {before after : List Reg}
    (raw : RelCT isa (VG.X86.Taint.Agree (roundTaint before)) code (VG.X86.Taint.Agree (roundTaint after)))
    (correct : ∀ s, Context g s → WP isa code s fun t => t.mem = s.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t) :
    RelCT isa (Pair g before) code (Pair g after) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, A⟩ := raw _ _ _ _ _ _ H.2.2 E G
  obtain ⟨Mu, Ku⟩ := wp_result (correct s H.1) E
  obtain ⟨Mz, Kz⟩ := wp_result (correct t H.2.1) G
  exact ⟨trace, H.1.keepMem Ku (by decide) Mu, H.2.1.keepMem Kz (by decide) Mz, A⟩

end VG.Proof.MillerRabin.X86

end

end

/-! # Full-width equality scans use public addresses and counters -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.MillerRabin.X86 VG.Proof.Dsa.X86

def equalRegisters : List Reg := [.esi, .ecx, .ebp, .edi]

theorem equalZero_relCT {g : Geometry} :
    RelCT isa (Pair g equalRegisters) (.block [.mov .ebx (.imm 0)]) (Pair g equalRegisters) := by
  refine readonly_relCT (checkedProgramChange (hint := .block [])
    (τ' := roundTaint (.ebx :: equalRegisters)) (by kernel_rfl) (by kernel_rfl)) ?_
  intro s _
  exact wp_movS rfl fun t T _ => WP.block_nil ⟨T.mem, T.keeps.mono (by decide)⟩

theorem equalLoop_raw : RelCT isa (VG.X86.Taint.Agree (roundTaint equalRegisters))
    (.loop (.block equalBody) .ne) (VG.X86.Taint.Agree (roundTaint equalRegisters)) :=
  checkedProgramChange (τ' := roundTaint equalRegisters true)
    (hint := VG.Taint.hintOf taint (roundTaint equalRegisters) (.loop (.block equalBody) .ne)) (by kernel_rfl) (by kernel_rfl)

theorem equalFinish_raw (result : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi]))
      (.block [.mov .eax (.imm 0), .alu .sub .ebx (.imm 1), .alu .adc .eax (.imm 0), .store (slot result) .eax])
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT _ (.block [.mov .eax (.imm 0), .alu .sub .ebx (.imm 1),
    .alu .adc .eax (.imm 0), .store (slot 0) .eax]) (.block []) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

theorem equal_trace {g : Geometry} (v : g.Valid) (result a b : Nat) (ai : a < 28) (bi : b < 28) :
    RelCT isa (Pair g [.edi]) (equal result a b) (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  unfold equal
  simp only [List.append_assoc]
  refine RelCT.seq (RelCT.block_append (RelCT.seq
    (pointer_pair_relCT v .ebp a (by decide) ai [.edi] (by decide))
    (RelCT.block_append (RelCT.seq
      (pointer_pair_relCT v .ecx b (by decide) bi [.ebp, .edi] (by decide))
      (RelCT.block_append (RelCT.seq
        (words_pair_relCT v [.ecx, .ebp, .edi] (by decide)) equalZero_relCT)))))) ?_
  refine RelCT.seq (equalLoop_raw.mono (P' := Pair g equalRegisters) (fun _ _ H => H.2.2) (fun _ _ H => H)) ?_
  exact (equalFinish_raw result).mono (fun _ _ H => round_add_regs (round_forget H) fun r mem =>
    round_regs H (by obtain rfl := List.mem_singleton.mp mem; decide)) (fun _ _ H => H)

theorem equal_relCT {g : Geometry} (v : g.Valid) (result a b : Nat)
    (scratch : scratchWord result) (ai : a < 28) (bi : b < 28) :
    RelCT isa (Pair g [.edi]) (equal result a b) (Pair g [.edi]) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, A⟩ := equal_trace v result a b ai bi _ _ _ _ _ _ H E G
  have fit : result + 4 ≤ g.L := Nat.le_trans (scratch_fit scratch) v.headerFit
  obtain ⟨_, Ou, Ku⟩ := wp_result (equal_ok v H.1 result a b fit ai bi) E
  obtain ⟨_, Oz, Kz⟩ := wp_result (equal_ok v H.2.1 result a b fit ai bi) G
  exact ⟨trace, H.1.keepScalar Ku (by decide) Ou scratch, H.2.1.keepScalar Kz (by decide) Oz scratch, A⟩

end VG.Proof.MillerRabin.X86

end

end

/-! # Squaring and masked flag updates have a public-address trace -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86

theorem squareStep_trace {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} (length : g.L = 8 * capacity) :
    RelCT isa (fun s t => Pair g [.edi] s t ∧ MulInput g capacity aY p s ∧ MulInput g capacity aY p t)
      (squareStep name code) (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  change RelCT isa _ (.seq (mulY name code aY)
    (.seq (equal sEq2 aY aMinusOne) (.block squareFlag))) _
  refine RelCT.seq (mulY_relCT verified noSp stack v length (by change 6 < 8 ∧ 6 ≠ 2 ∧ 6 ≠ 3; decide)) ?_
  exact RelCT.seq (equal_relCT v sEq2 aY aMinusOne (by unfold scratchWord sEq2; simp) (by decide) (by decide))
    (squareFlag_relCT.mono (fun _ _ H => H.2.2) (fun _ _ H => H))

end VG.Proof.MillerRabin.X86

end

end

/-! # A public square count controls the loop; the threshold remains secret -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.MillerRabin.X86 VG.Proof.Dsa.X86

def SquareInput (g : Geometry) (capacity : Nat) (p : BitVec 32) (q : Nat) (s : State) : Prop :=
  ∃ c A V r, ∃ flag : Bool,
    Stage g capacity c p A [aY, aMinusOne] V [sSquares, sThreshold, sFlag] s ∧
    c % 2 = 1 ∧ A aY < c ∧ r < 2 ^ 31 ∧ q < 2 ^ 31 ∧
    V sSquares = BitVec.ofNat 32 q ∧ V sThreshold = BitVec.ofNat 32 r ∧ V sFlag = BitVec.ofNat 32 flag.toNat

theorem SquareInput.context {g : Geometry} {capacity q : Nat} {p : BitVec 32} {s : State}
    (I : SquareInput g capacity p q s) : Context g s := by
  obtain ⟨_, _, _, _, _, S, _⟩ := I
  exact S.data.context

theorem SquareInput.mulInput {g : Geometry} {capacity q : Nat} {p : BitVec 32} {s : State}
    (I : SquareInput g capacity p q s) : MulInput g capacity aY p s := by
  obtain ⟨c, A, V, r, F, S, odd, lt, _⟩ := I
  refine ⟨S.data.context, ⟨c, S.modulus, odd, ?_⟩, S.caller⟩
  rw [(S.data.arrayValues aY (by decide)).2]
  exact lt

theorem SquareInput.step {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity q : Nat} {p : BitVec 32} {s : State}
    (I : SquareInput g capacity p q s) (length : g.L = 8 * capacity) (positive : 0 < q) :
    WP isa (squareStep name code) s fun t => SquareInput g capacity p (q - 1) t ∧ t.zf = some (decide (q = 1)) := by
  obtain ⟨c, A, V, r, F, S, odd, lt, rBound, qBound, count, threshold, flag⟩ := I
  refine WP.mono (squareStep_ok verified noSp stack v S length odd lt (by decide) (by decide)
    positive qBound rBound F (by intro d mem; exact mem) count threshold flag) fun t ⟨St, Z, _, _⟩ => ?_
  let Y := Word32.mm c g.w (A aY) (A aY)
  let E := decide (Y = A aMinusOne)
  refine ⟨⟨c, setAt A aY Y, squareSlots (setAt V sEq2 (BitVec.ofNat 32 E.toNat)) q r E F,
    r, F || (decide (r < q) && E), ?_, odd, ?_, rBound, by omega_using [qBound], rfl, ?_, ?_⟩, Z⟩
  · exact St.mono (fun j mem => ⟨mem, rfl⟩) (by
      intro d mem
      refine ⟨?_, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem ⊢
      rcases mem with rfl | rfl | rfl <;> simp)
  · rw [setAt_self]
    exact Word32.mm_lt (by omega_using [odd] : 0 < c)
  · exact threshold
  · change BitVec.ofNat 32 (F || (E && decide (r < q))).toNat = _
    rw [Bool.and_comm]

end VG.Proof.MillerRabin.X86
