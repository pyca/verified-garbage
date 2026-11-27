module

public import VerifiedGarbage.Proof.MillerRabin.X86.Context
public import VerifiedGarbage.Impl.MillerRabin.X86.Ops
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
public import VerifiedGarbage.Impl.MillerRabin.X86.Layout

/-! ### `MillerRabin.X86.CopyLoop`, which this module and modules that import it used -/

section

/-! # A runtime native-word copy preserves its source and every other byte -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Bignum.X86.PublicRt (countLoop count1_zf ptr4)

def copyBody : List Instr :=
  [.mov .eax (.mem (at_ .ebx 0)), .store (at_ .ebp 0) .eax,
    .alu .add .ebx (.imm 4), .alu .add .ebp (.imm 4), .alu .sub .esi (.imm 1)]

/-- The copy loop copies `N` words from `y` to `x`, and leaves the pointers
past the words copied. -/
theorem copyLoop_ends {s : State} {W : Addr} {L x y N : Nat} (hw : Ws s W L)
    (positive : 0 < N) (dstFit : x + 4 * N ≤ L) (srcFit : y + 4 * N ≤ L)
    (apart : x = y ∨ x + 4 * N ≤ y ∨ y + 4 * N ≤ x)
    (dst : PtrAt s W .ebp x) (src : PtrAt s W .ebx y) (count : (s.gpr .esi).toNat = N) :
    WP isa (.loop (.block copyBody) .ne) s fun t =>
      Outside W x (4 * N) s.mem t.mem ∧ val32 t.mem W x N = val32 s.mem W y N ∧
      Keeps [.eax, .ebx, .ebp, .esi] s t ∧ PtrAt t W .ebp (x + 4 * N) ∧ PtrAt t W .ebx (y + 4 * N) := by
  have nowrap := hw.nowrap
  refine WP.mono (countLoop positive (fun i t => Keeps [.eax, .ebx, .ebp, .esi] s t ∧
    PtrAt t W .ebp (x + 4 * i) ∧ PtrAt t W .ebx (y + 4 * i) ∧ (t.gpr .esi).toNat = N - i ∧
    Outside W x (4 * i) s.mem t.mem ∧ val32 t.mem W x i = val32 s.mem W y i) ?_
    ⟨Keeps.refl _ _, by simpa using dst, by simpa using src, by simpa using count, Outside.refl _ _ _ _, rfl⟩)
    fun t ⟨K, bp, bx, _, O, V⟩ => ⟨O, V, K, bp, bx⟩
  rintro i t index ⟨K, bp, bx, countI, O, V⟩
  have ht := hw.of_keeps K
  unfold copyBody
  refine wp_movS (readSrc_ptr ht bx (d := 0) (by omega_using [srcFit, index])) fun a A _ => ?_
  have bpA : PtrAt a W .ebp (x + 4 * i) := by rw [PtrAt, A.other .ebp (by decide)]; exact bp
  refine wp_storeS (ea_ptr (ht.of_keeps A.keeps) bpA (d := 0) (by omega_using [dstFit, index]))
    (ws_write (ht.of_keeps A.keeps) (y := x + 4 * i + 0) (n := 4) (by omega_using [dstFit, index])) fun b B => ?_
  refine wp_addS rfl fun c C _ => wp_addS rfl fun d D _ => wp_subZ rfl fun u U Z => WP.block_nil ?_
  have esiD : d.gpr .esi = t.gpr .esi := by
    rw [D.other .esi (by decide), C.other .esi (by decide), B.gpr, A.other .esi (by decide)]
  obtain ⟨nextCount, last⟩ := count1_zf countI index
  have word : w32 t.mem W (y + 4 * i) = w32 s.mem W (y + 4 * i) :=
    O.w32 (by rcases apart with apart | apart <;> omega_arith) (by omega_using [srcFit, nowrap, index])
  refine ⟨⟨((((K.widen A.keeps).widen (B.keeps [])).widen C.keeps).widen D.keeps).widen U.keeps,
    ?_, ?_, by rw [U.gpr, esiD]; exact nextCount, ?_, ?_⟩, by rw [Z, esiD, last]⟩
  · rw [PtrAt, U.other .ebp (by decide), D.gpr, C.other .ebp (by decide), B.gpr, A.other .ebp (by decide)]
    exact ptr4 bp
  · rw [PtrAt, U.other .ebx (by decide), D.other .ebx (by decide), C.gpr, B.gpr, A.other .ebx (by decide)]
    exact ptr4 bx
  · rw [U.mem, D.mem, C.mem, B.mem, A.mem, Nat.add_zero]
    exact (O.mono (by omega_using []) (by omega_using [])).trans
      ((writeW32_outside _ _ _ (by omega_using [dstFit, nowrap, index])).mono (by omega_using []) (by omega_using []))
  · rw [U.mem, D.mem, C.mem, B.mem, A.mem, Nat.add_zero, val32_store nowrap (by omega_using [dstFit, index]),
      V, A.gpr, Nat.add_zero, val32_succ s.mem W y]
    change _ + _ * w32 t.mem W (y + 4 * i) = _
    rw [word]

end VG.Proof.MillerRabin.X86

end

end

/-! # Runtime-width prepared array copies on i686 -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem words_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s) :
    WP isa (.block words) s fun t => (t.gpr .esi).toNat = g.words ∧ t.mem = s.mem ∧ Keeps [.esi] s t := by
  unfold words
  refine wp_movS (readSrc_ptr C.ws C.base (d := 48) (by have := v.headerFit; omega_using [this])) fun a A _ => ?_
  refine wp_addS rfl fun t T _ => WP.block_nil ⟨?_, T.mem.trans A.mem, A.keeps.trans T.keeps⟩
  rw [T.gpr, A.gpr, BitVec.toNat_add, Nat.zero_add]
  change (w32 s.mem g.W 48 + w32 s.mem g.W 48) % 2 ^ 32 = g.words
  rw [C.width]
  have bound := v.maxWidth
  unfold Geometry.words
  omega_using [bound]

/-- `copy_ok`, with `ebp` and `ebx` past the destination and the source. -/
theorem copy_ends {g : Geometry} (v : g.Valid) {s : State} (C : Context g s)
    (dst src : Nat) (dstIndex : dst < 28) (srcIndex : src < 28) :
    WP isa (copy dst src) s fun t =>
      val32 t.mem g.W (g.array dst) g.words = val32 s.mem g.W (g.array src) g.words ∧
      Outside g.W (g.array dst) (4 * g.words) s.mem t.mem ∧
      Keeps [.eax, .ebx, .edx, .ebp, .esi] s t ∧ Context g t ∧
      PtrAt t g.W .ebp (g.array dst + 4 * g.words) ∧ PtrAt t g.W .ebx (g.array src + 4 * g.words) := by
  unfold copy
  rw [List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (C.ptr v dst dstIndex .ebp (by decide) (by decide))
    fun a ⟨P, M, K⟩ => ?_))
  have Ca := C.keepMem K (by decide) M
  refine WP.block_append (WP.mono (Ca.ptr v src srcIndex .ebx (by decide) (by decide))
    fun b ⟨Pb, Mb, Kb⟩ => ?_)
  have Cb := Ca.keepMem Kb (by decide) Mb
  refine WP.mono (words_ok v Cb) fun c ⟨Count, Mc, Kc⟩ => ?_
  have keep : Keeps [.ebx, .edx, .ebp, .esi] s c :=
    ((K.mono (by decide)).trans (Kb.mono (by decide))).trans (Kc.mono (by decide))
  have mem : c.mem = s.mem := Mc.trans (Mb.trans M)
  have bp : PtrAt c g.W .ebp (g.array dst) := by
    rw [PtrAt, Kc.1 .ebp (by decide), Kb.1 .ebp (by decide)]; exact P
  have bx : PtrAt c g.W .ebx (g.array src) := by
    rw [PtrAt, Kc.1 .ebx (by decide)]; exact Pb
  refine WP.mono (copyLoop_ends (C.ws.of_keeps keep) (by have := v.minWidth; unfold Geometry.words; omega_using [this])
    (v.arrayFit dstIndex) (v.arrayFit srcIndex) (g.arraysApart dst src) bp bx Count) ?_
  rintro t ⟨O, V, Kt, bp', bx'⟩
  have Kall : Keeps [.eax, .ebx, .edx, .ebp, .esi] s t := (keep.mono (by decide)).trans (Kt.mono (by decide))
  rw [mem] at O V
  exact ⟨V, O, Kall, C.keepOutside Kall (by decide) O (v.arrayHeader dst), bp', bx'⟩

theorem copy_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s)
    (dst src : Nat) (dstIndex : dst < 28) (srcIndex : src < 28) :
    WP isa (copy dst src) s fun t =>
      val32 t.mem g.W (g.array dst) g.words = val32 s.mem g.W (g.array src) g.words ∧
      Outside g.W (g.array dst) (4 * g.words) s.mem t.mem ∧
      Keeps [.eax, .ebx, .edx, .ebp, .esi] s t ∧ Context g t :=
  WP.mono (copy_ends v C dst src dstIndex srcIndex) fun _ ⟨V, O, K, C', _⟩ => ⟨V, O, K, C'⟩

end VG.Proof.MillerRabin.X86
