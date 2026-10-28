module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.PrepareRt
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2State
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessRt.Blocks
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Array 6 zeroed, seeded with the candidate's top bit, or set to one, at the run-time width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.PrepareRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.MillerRabin.X86
open VG.Proof.RsaKeyGen.X86.PreparedR2 (Ready)
open VG.Impl.RsaKeyGen.X86.PrepareRt

/-- What leaves the prepared state: a write to an array above the candidate. -/
theorem _root_.VG.Proof.RsaKeyGen.X86.PreparedR2.Ready.keepRange {g : Geometry} (v : g.Valid) {s t : State} {c capacity : Nat} {p : BitVec 32}
    (S : Ready g c capacity p s) {d n : Nat} (low : g.array 0 + 4 * g.words ≤ d) (fit : d + n ≤ g.L)
    {rs : List Reg} (K : Keeps rs s t) (edi : .edi ∉ rs) (esp : .esp ∉ rs)
    (O : Outside g.W d n s.mem t.mem) : Ready g c capacity p t := by
  have header := v.arrayHeader 0
  have W := Outs.of_outside O (List.mem_singleton_self _)
  have F := WorkspaceFrame.of_outs S.scratch.nowrap W
  exact ⟨S.context.keepOutside K edi O (by omega),
    S.modulus.keep v F (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact Or.inl (by omega))
      (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact Or.inl low),
    S.caller.keepOuts K esp W (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact fit),
    S.scratch.of_keeps K edi esp⟩

/-- What leaves the prepared state: no write to memory. -/
theorem _root_.VG.Proof.RsaKeyGen.X86.PreparedR2.Ready.keepSame {g : Geometry} {s t : State} {c capacity : Nat}
    {p : BitVec 32} (S : Ready g c capacity p s) {rs : List Reg} (K : Keeps rs s t) (edi : .edi ∉ rs)
    (esp : .esp ∉ rs) (M : t.mem = s.mem) : Ready g c capacity p t :=
  ⟨S.context.keepMem K edi M, by rw [M]; exact S.modulus,
    S.caller.keepFrame K esp (by rw [M]; exact Frame.refl _ _), S.scratch.of_keeps K edi esp⟩

/-- `ebp` at array 6, `ecx` its octets and `eax` zero. -/
theorem zeroArgs_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s) :
    WP isa (.block zeroArgs) s fun t =>
      PtrAt t g.W .ebp (g.array 6) ∧ (t.gpr .ecx).toNat = 4 * g.words ∧ t.gpr .eax = 0 ∧ t.mem = s.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp] s t := by
  obtain ⟨-, -, -, words⟩ := WitnessRt.fits v
  have bound := v.maxWidth
  unfold zeroArgs
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (WitnessRt.ptr_short v C 6 (by decide) .ebp) fun a ⟨P, Ma, Ka⟩ => ?_)
  have Ca := C.keepMem Ka (by decide) Ma
  refine WP.block_append (WP.mono (WitnessRt.draw_ok v Ca) fun b ⟨D, Mb, Kb⟩ => ?_)
  refine wp_movS rfl fun d Dd _ => wp_movS rfl fun e E _ => WP.block_nil ⟨?_, ?_, E.gpr,
    by rw [E.mem, Dd.mem, Mb, Ma], (((Ka.mono (by decide)).widen Kb).widen Dd.keeps).widen E.keeps⟩
  · rw [PtrAt, E.other .ebp (by decide), Dd.other .ebp (by decide), Kb.1 .ebp (by decide)]; exact P
  · rw [E.other .ecx (by decide), Dd.gpr, D, BitVec.toNat_ofNat]; omega

/-- The zeroing loop, from `zeroArgs`. -/
theorem zeroLoop_run {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (S : Ready g c capacity p s) (P : PtrAt s g.W .ebp (g.array 6)) (count : (s.gpr .ecx).toNat = 4 * g.words)
    (zero : s.gpr .eax = 0) :
    WP isa zeroLoop s fun t =>
      Ready g c capacity p t ∧ val32 t.mem g.W (g.array 6) g.words = 0 ∧
      Outside g.W (g.array 6) (4 * g.words) s.mem t.mem ∧ Keeps [.ebp, .ecx] s t := by
  obtain ⟨fit, below, many, -⟩ := WitnessRt.fits v
  exact WP.mono (VG.Proof.Bignum.X86.PublicRt.zeroLoop_ok S.context.ws (N := g.words) (by omega) fit P count zero)
    fun t ⟨O, V, Kt⟩ => ⟨S.keepRange v below fit Kt (by decide) (by decide) O, V, O, Kt⟩

theorem zero_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (S : Ready g c capacity p s) :
    WP isa zero s fun t =>
      Ready g c capacity p t ∧ val32 t.mem g.W (g.array 6) g.words = 0 ∧
      Outside g.W (g.array 6) (4 * g.words) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  unfold zero
  refine WP.seq (WP.mono (zeroArgs_ok v S.context) fun e ⟨P, count, zero, Me, K⟩ => ?_)
  have E : Ready g c capacity p e := S.keepSame K (by decide) (by decide) Me
  refine WP.mono (zeroLoop_run v E P count zero) fun t ⟨T, V, O, Kt⟩ => ⟨T, V, ?_, K.trans (Kt.mono (by decide))⟩
  rw [Me] at O
  exact O

/-- `ebp` at array 6 and `edx` its octets. -/
theorem topArgs_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s) :
    WP isa (.block topArgs) s fun t =>
      PtrAt t g.W .ebp (g.array 6) ∧ t.gpr .edx = BitVec.ofNat 32 (8 * g.w) ∧ t.mem = s.mem ∧
      Keeps [.edx, .ebp] s t := by
  unfold topArgs
  refine WP.block_append (WP.mono (WitnessRt.ptr_short v C 6 (by decide) .ebp) fun a ⟨P, Ma, Ka⟩ => ?_)
  refine WP.mono (WitnessRt.draw_ok v (C.keepMem Ka (by decide) Ma)) fun b ⟨D, Mb, Kb⟩ =>
    ⟨by rw [PtrAt, Kb.1 .ebp (by decide)]; exact P, D, by rw [Mb, Ma], (Ka.mono (by decide)).widen Kb⟩

/-- `2^31` in array 6's top word, from `topArgs`. -/
theorem topStore_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (S : Ready g c capacity p s) (P : PtrAt s g.W .ebp (g.array 6)) (D : s.gpr .edx = BitVec.ofNat 32 (8 * g.w)) :
    WP isa (.block topStore) s fun t =>
      Ready g c capacity p t ∧ w32 t.mem g.W (g.array 6 + 4 * g.words - 4) = 2 ^ 31 ∧
      Outside g.W (g.array 6 + 4 * g.words - 4) 4 s.mem t.mem ∧ Keeps [.eax, .ebp] s t := by
  obtain ⟨fit, below, many, words⟩ := WitnessRt.fits v
  have bound := v.maxWidth
  have nowrap := S.scratch.nowrap
  unfold topStore
  refine wp_addS rfl fun d Dd _ => wp_subS rfl fun e E _ => wp_movS rfl fun f F _ => ?_
  have Kf : Keeps [.eax, .ebp] s f := ((Dd.keeps.mono (by decide)).widen E.keeps).widen F.keeps
  have hw := S.context.ws.of_keeps Kf
  have sum : PtrAt d g.W .ebp (g.array 6 + 4 * g.words) := by
    rw [PtrAt, Dd.gpr, ptr_add P, D, BitVec.toNat_ofNat]
    congr 2
    omega
  have ebp : PtrAt f g.W .ebp (g.array 6 + 4 * g.words - 4) := by
    rw [PtrAt, F.other .ebp (by decide), E.gpr, ptr_sub sum 4 (by change 4 ≤ _; omega)]
    rfl
  refine wp_storeS (ea_ptr hw ebp (d := 0) (by omega))
    (ws_write hw (y := g.array 6 + 4 * g.words - 4 + 0) (n := 4) (by omega)) fun t T => WP.block_nil ?_
  have Mt : t.mem = s.mem.writeW (off g.W (g.array 6 + 4 * g.words - 4)) (f.gpr .eax) := by
    rw [T.mem, F.mem, E.mem, Dd.mem, Nat.add_zero]
  have O : Outside g.W (g.array 6 + 4 * g.words - 4) 4 s.mem t.mem := by
    rw [Mt]; exact writeW32_outside _ _ _ (by omega)
  have Kt := Kf.widen (T.keeps [])
  refine ⟨S.keepRange v (by omega) (by omega) Kt (by decide) (by decide) O, ?_, O, Kt⟩
  rw [Mt, w32_write_self, F.gpr]
  rfl

/-- The top word of array 6 set to `2^31`. -/
theorem top_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (S : Ready g c capacity p s) :
    WP isa (.block top) s fun t =>
      Ready g c capacity p t ∧ w32 t.mem g.W (g.array 6 + 4 * g.words - 4) = 2 ^ 31 ∧
      Outside g.W (g.array 6 + 4 * g.words - 4) 4 s.mem t.mem ∧ Keeps [.eax, .edx, .ebp] s t := by
  unfold top
  refine WP.block_append (WP.mono (topArgs_ok v S.context) fun a ⟨P, D, Ma, Ka⟩ => ?_)
  have A : Ready g c capacity p a := S.keepSame Ka (by decide) (by decide) Ma
  refine WP.mono (topStore_ok v A P D) fun t ⟨T, V, O, Kt⟩ => ⟨T, V, ?_, (Ka.mono (by decide)).trans (Kt.mono (by decide))⟩
  rw [Ma] at O
  exact O

theorem seed_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (S : Ready g c capacity p s) :
    WP isa seed s fun t =>
      Ready g c capacity p t ∧ val32 t.mem g.W (g.array 6) g.words = 2 ^ (64 * g.w - 1) ∧
      Outside g.W (g.array 6) (4 * g.words) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  obtain ⟨fit, below, many, words⟩ := WitnessRt.fits v
  have nowrap := S.scratch.nowrap
  unfold seed
  refine WP.seq (WP.mono (zero_ok v S) fun a ⟨A, Va, Oa, Ka⟩ => ?_)
  refine WP.mono (top_ok v A) fun t ⟨T, topT, Ot, Kt⟩ => ⟨T, ?_, Oa.trans (Ot.mono (by omega) (by omega)),
    Ka.trans (Kt.mono (by decide))⟩
  have split := val32_succ t.mem g.W (g.array 6) (g.words - 1)
  have lowA := val32_succ a.mem g.W (g.array 6) (g.words - 1)
  rw [Nat.sub_add_cancel (by omega)] at split lowA
  have zeroLow : val32 a.mem g.W (g.array 6) (g.words - 1) = 0 := by omega
  have sameLow : val32 t.mem g.W (g.array 6) (g.words - 1) = val32 a.mem g.W (g.array 6) (g.words - 1) :=
    Ot.val32 (Or.inl (by omega)) (by omega)
  rw [split, sameLow, zeroLow, show g.array 6 + 4 * (g.words - 1) = g.array 6 + 4 * g.words - 4 by omega, topT,
    Nat.zero_add, ← Nat.pow_add]
  congr 1
  omega

/-- One in array 6's lowest word, from `ebp` at array 6. -/
theorem oneStore_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (S : Ready g c capacity p s) (P : PtrAt s g.W .ebp (g.array 6)) :
    WP isa (.block oneStore) s fun t =>
      Ready g c capacity p t ∧ t.mem = s.mem.writeW (off g.W (g.array 6)) (1#32) ∧
      Outside g.W (g.array 6) 4 s.mem t.mem ∧ Keeps [.eax] s t := by
  obtain ⟨fit, below, many, -⟩ := WitnessRt.fits v
  have nowrap := S.scratch.nowrap
  unfold oneStore
  refine wp_movS rfl fun d Dd _ => ?_
  have hw := S.context.ws.of_keeps Dd.keeps
  have ebp : PtrAt d g.W .ebp (g.array 6) := by rw [PtrAt, Dd.other .ebp (by decide)]; exact P
  refine wp_storeS (ea_ptr hw ebp (d := 0) (by omega)) (ws_write hw (y := g.array 6 + 0) (n := 4) (by omega))
    fun t T => WP.block_nil ?_
  have Mt : t.mem = s.mem.writeW (off g.W (g.array 6)) (1#32) := by
    rw [T.mem, Dd.mem, Nat.add_zero, Dd.gpr]; rfl
  have Ot : Outside g.W (g.array 6) 4 s.mem t.mem := by rw [Mt]; exact writeW32_outside _ _ _ (by omega)
  have Kt : Keeps [.eax] s t := Dd.keeps.widen (T.keeps [])
  exact ⟨S.keepRange v below (by omega) Kt (by decide) (by decide) Ot, Mt, Ot, Kt⟩

theorem one_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (S : Ready g c capacity p s) :
    WP isa one s fun t =>
      Ready g c capacity p t ∧ val32 t.mem g.W (g.array 6) g.words = 1 ∧
      Outside g.W (g.array 6) (4 * g.words) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  obtain ⟨fit, below, many, words⟩ := WitnessRt.fits v
  have nowrap := S.scratch.nowrap
  unfold one
  refine WP.seq (WP.mono (zero_ok v S) fun a ⟨A, Va, Oa, Ka⟩ => ?_)
  refine WP.block_append (WP.mono (WitnessRt.ptr_short v A.context 6 (by decide) .ebp) fun b ⟨P, Mb, Kb⟩ => ?_)
  have B : Ready g c capacity p b := A.keepSame Kb (by decide) (by decide) Mb
  refine WP.mono (oneStore_ok v B P) fun t ⟨T, Mt, Ot, Kt⟩ => ?_
  rw [Mb] at Mt Ot
  refine ⟨T, ?_, Oa.trans (Ot.mono (by omega) (by omega)), Ka.trans ((Kb.mono (by decide)).widen Kt)⟩
  have rest : val32 t.mem g.W (g.array 6 + 4) (g.words - 1) = val32 a.mem g.W (g.array 6 + 4) (g.words - 1) :=
    Ot.val32 (Or.inr (by omega)) (by omega)
  have restZero : val32 a.mem g.W (g.array 6 + 4) (g.words - 1) = 0 := by
    have := Va
    rw [show g.words = g.words - 1 + 1 by omega, val32] at this
    omega
  rw [show g.words = g.words - 1 + 1 by omega, val32, rest, restZero, Mt, w32_write_self]
  rfl

end VG.Proof.RsaKeyGen.X86.PrepareRt
