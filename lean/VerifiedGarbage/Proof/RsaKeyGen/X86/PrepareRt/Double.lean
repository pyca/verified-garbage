module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.PrepareRt
public import VerifiedGarbage.Proof.MillerRabin.X86.Context
public import VerifiedGarbage.Proof.MillerRabin.X86.Modulus
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveStack
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareRt.DoubleMath
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessRt.Blocks
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops2
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.MillerRabin.X86.WorkspaceFrame
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # One doubling of array 6 modulo the candidate, inside the doublings' frame

`ebp`, `ebx` and `edi` walk arrays 2, 0 and 6; the workspace pointer, saved
at the frame's base, is read back before the next pointers and at the end. -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.PrepareRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.MillerRabin.X86
open VG.Impl.RsaKeyGen.X86.PrepareRt
open VG.Proof.RsaKeyGen.X86.Sieve (StackContext)

/-- Where a doubling writes: the sum with its carry, and array 6. -/
def doubleRanges (g : Geometry) : List (Nat × Nat) := [(g.array 2, 4 * g.words + 4), (g.array 6, 4 * g.words)]

/-- A context back once `edi` is: the header is outside what changed. -/
theorem Context.restore {g : Geometry} {s t : State} (C : Context g s) (wr : t.wr = s.wr)
    (edi : t.gpr .edi = s.gpr .edi) {rs : List (Nat × Nat)} (O : Outs g.W rs s.mem t.mem)
    (above : ∀ r ∈ rs, 256 ≤ r.1) : Context g t := by
  have word {d : Nat} (fit : d + 4 ≤ 256) : w32 t.mem g.W d = w32 s.mem g.W d :=
    congrArg BitVec.toNat (Mem.readW_congr fun i hi => O _ fun r mem => by
      have := above r mem
      rw [ofs_off g.W (by omega)]; omega)
  refine ⟨⟨wr ▸ C.ws.wr, C.ws.nowrap⟩, by rw [PtrAt, edi]; exact C.base, ?_, ?_, ?_⟩
  · rw [word (by decide)]; exact C.width
  · rw [word (by decide)]; exact C.stride
  · intro j index
    rw [word (by omega)]; exact C.pointers j index

/-- `ebx` at array 6, `ebp` at array 2, `edx` their octets and no carry. -/
theorem doubleArgs_ok {g : Geometry} (v : g.Valid) {a : State} (C : Context g a) :
    WP isa (.block doubleArgs) a fun b =>
      PtrAt b g.W .ebx (g.array 6) ∧ PtrAt b g.W .ebp (g.array 2) ∧ (b.gpr .edx).toNat = 4 * g.words ∧
      b.gpr .ecx = cmask false ∧ b.mem = a.mem ∧ Keeps [.ebx, .ebp, .edx, .ecx] a b := by
  obtain ⟨-, -, -, words⟩ := WitnessRt.fits v
  have bound := v.maxWidth
  unfold doubleArgs
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (WitnessRt.ptr_short v C 6 (by decide) .ebx) fun a1 ⟨P1, M1, K1⟩ => ?_)
  have C1 := C.keepMem K1 (by decide) M1
  refine WP.block_append (WP.mono (WitnessRt.ptr_short v C1 2 (by decide) .ebp) fun a2 ⟨P2, M2, K2⟩ => ?_)
  have C2 := C1.keepMem K2 (by decide) M2
  refine WP.block_append (WP.mono (WitnessRt.draw_ok v C2) fun a3 ⟨D3, M3, K3⟩ => ?_)
  refine wp_movS rfl fun b B _ => WP.block_nil ⟨?_, ?_, ?_, B.gpr, by rw [B.mem, M3, M2, M1],
    (((K1.mono (by decide)).widen K2).widen K3).widen B.keeps⟩
  · rw [PtrAt, B.other .ebx (by decide), K3.1 .ebx (by decide), K2.1 .ebx (by decide)]; exact P1
  · rw [PtrAt, B.other .ebp (by decide), K3.1 .ebp (by decide)]; exact P2
  · rw [B.other .edx (by decide), D3, BitVec.toNat_ofNat]; omega

/-- `ebp` at the sum (array 2), `ebx` at the candidate, `edi` at array 6, `edx` their octets, no borrow. -/
theorem reduceArgs_ok {g : Geometry} (v : g.Valid) {e : State} (C : Context g e) :
    WP isa (.block reduceArgs) e fun f =>
      PtrAt f g.W .ebp (g.array 2) ∧ PtrAt f g.W .ebx (g.array 0) ∧ PtrAt f g.W .edi (g.array 6) ∧
      (f.gpr .edx).toNat = 4 * g.words ∧ f.gpr .ecx = cmask false ∧ f.mem = e.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] e f := by
  obtain ⟨-, -, -, words⟩ := WitnessRt.fits v
  have bound := v.maxWidth
  unfold reduceArgs
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (WitnessRt.ptr_short v C 2 (by decide) .ebp) fun f1 ⟨Q1, N1, L1⟩ => ?_)
  have Cf1 := C.keepMem L1 (by decide) N1
  refine WP.block_append (WP.mono (WitnessRt.ptr_short v Cf1 0 (by decide) .ebx) fun f2 ⟨Q2, N2, L2⟩ => ?_)
  have Cf2 := Cf1.keepMem L2 (by decide) N2
  refine WP.block_append (WP.mono (WitnessRt.ptr_short v Cf2 6 (by decide) .eax) fun f3 ⟨Q3, N3, L3⟩ => ?_)
  have Cf3 := Cf2.keepMem L3 (by decide) N3
  refine WP.block_append (WP.mono (WitnessRt.draw_ok v Cf3) fun f4 ⟨D4, N4, L4⟩ => ?_)
  refine wp_movS rfl fun f5 F5 _ => wp_movS rfl fun f F _ => WP.block_nil ⟨?_, ?_, ?_, ?_, F.gpr,
    by rw [F.mem, F5.mem, N4, N3, N2, N1],
    (((((L1.mono (by decide)).widen L2).widen L3).widen L4).widen F5.keeps).widen F.keeps⟩
  · rw [PtrAt, F.other .ebp (by decide), F5.other .ebp (by decide), L4.1 .ebp (by decide), L3.1 .ebp (by decide),
      L2.1 .ebp (by decide)]; exact Q1
  · rw [PtrAt, F.other .ebx (by decide), F5.other .ebx (by decide), L4.1 .ebx (by decide), L3.1 .ebx (by decide)]
    exact Q2
  · rw [PtrAt, F.other .edi (by decide), F5.gpr, L4.1 .eax (by decide)]; exact Q3
  · rw [F.other .edx (by decide), F5.other .edx (by decide), D4, BitVec.toNat_ofNat]; omega

/-- `ebp` at the sum, `ebx` at array 6, `edi` their octets. -/
theorem selectArgs_ok {g : Geometry} (v : g.Valid) {i : State} (C : Context g i) :
    WP isa (.block selectArgs) i fun j =>
      PtrAt j g.W .ebp (g.array 2) ∧ PtrAt j g.W .ebx (g.array 6) ∧ (j.gpr .edi).toNat = 4 * g.words ∧
      j.mem = i.mem ∧ Keeps [.ebx, .edx, .ebp, .edi] i j := by
  obtain ⟨-, -, -, words⟩ := WitnessRt.fits v
  have bound := v.maxWidth
  unfold selectArgs
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (WitnessRt.ptr_short v C 2 (by decide) .ebp) fun j1 ⟨R1, Mj1, J1⟩ => ?_)
  have Cj1 := C.keepMem J1 (by decide) Mj1
  refine WP.block_append (WP.mono (WitnessRt.ptr_short v Cj1 6 (by decide) .ebx) fun j2 ⟨R2, Mj2, J2⟩ => ?_)
  have Cj2 := Cj1.keepMem J2 (by decide) Mj2
  refine WP.block_append (WP.mono (WitnessRt.draw_ok v Cj2) fun j3 ⟨D5, Mj3, J3⟩ => ?_)
  refine wp_movS rfl fun j J _ => WP.block_nil ⟨?_, ?_, ?_, by rw [J.mem, Mj3, Mj2, Mj1],
    (((J1.mono (by decide)).widen J2).widen J3).widen J.keeps⟩
  · rw [PtrAt, J.other .ebp (by decide), J3.1 .ebp (by decide), J2.1 .ebp (by decide)]; exact R1
  · rw [PtrAt, J.other .ebx (by decide), J3.1 .ebx (by decide)]; exact R2
  · rw [J.gpr, D5, BitVec.toNat_ofNat]; omega

theorem sum_ok {g : Geometry} (v : g.Valid) {a : State} {T : Nat} (C : Context g a)
    (value : val32 a.mem g.W (g.array 6) g.words = T) :
    WP isa sum a fun e =>
      Context g e ∧ Outside g.W (g.array 2) (4 * g.words + 4) a.mem e.mem ∧
      (∃ c0 : Bool, val32 e.mem g.W (g.array 2) g.words + 2 ^ (32 * g.words) * c0.toNat = T + T ∧
        w32 e.mem g.W (g.array 2 + 4 * g.words) = c0.toNat) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] a e := by
  obtain ⟨fit6, -, many, words⟩ := WitnessRt.fits v
  have bound := v.maxWidth
  have nowrap := C.ws.nowrap
  have a26 : g.array 2 + 4 * g.words + 4 ≤ g.array 6 := by
    unfold Geometry.array Geometry.words Proof.Rsa.Mont.arrAt Proof.Rsa.Mont.hdrBytes; omega
  unfold sum
  refine WP.seq (WP.mono (doubleArgs_ok v C) fun b ⟨ebxB, ebpB, edxB, ecxB, Mb, Kb⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86.PublicRt.doubleLoop_ok (C.ws.of_keeps Kb) (x := g.array 6)
    (a := g.array 2) (N := g.words) (by omega) fit6 (by omega) (Or.inl (by omega)) ebxB ebpB edxB ecxB)
    fun d ⟨Od, Pd, ⟨c0, ecxD, sumD⟩, Kd⟩ => ?_)
  rw [Mb, value] at sumD
  unfold carry
  refine wp_movS rfl fun e1 E1 _ => ?_
  refine wp_subS rfl fun e2 E2 _ => ?_
  have Ke2 : Keeps [.eax] d e2 := E1.keeps.trans E2.keeps
  have Kae2 : Keeps [.eax, .ebx, .ecx, .edx, .ebp] a e2 :=
    ((Kb.mono (by decide)).trans (Kd.mono (by decide))).trans (Ke2.mono (by decide))
  have hw2 := C.ws.of_keeps Kae2
  have Pe2 : PtrAt e2 g.W .ebp (g.array 2 + 4 * g.words) := by rw [PtrAt, Ke2.1 .ebp (by decide)]; exact Pd
  refine wp_storeS (ea_ptr hw2 Pe2 (d := 0) (by omega))
    (ws_write hw2 (y := g.array 2 + 4 * g.words + 0) (n := 4) (by omega)) fun e E => WP.block_nil ?_
  have Me : e.mem = d.mem.writeW (off g.W (g.array 2 + 4 * g.words)) (e2.gpr .eax) := by
    rw [E.mem, E2.mem, E1.mem, Nat.add_zero]
  have Oe : Outside g.W (g.array 2 + 4 * g.words) 4 d.mem e.mem := by
    rw [Me]; exact writeW32_outside _ _ _ (by omega)
  have Ke : Keeps [.eax, .ebx, .ecx, .edx, .ebp] a e := Kae2.widen (E.keeps [])
  have Oae : Outside g.W (g.array 2) (4 * g.words + 4) a.mem e.mem := by
    rw [← Mb]; exact (Od.mono (by omega) (by omega)).trans (Oe.mono (by omega) (by omega))
  refine ⟨C.keepOutside Ke (by decide) Oae (v.arrayHeader 2), Oae, ⟨c0, ?_, ?_⟩, Ke⟩
  · rw [Oe.val32 (Or.inl (by omega)) (by omega)]; exact sumD
  · rw [Me, w32_write_self, E2.gpr, E1.gpr, E1.other .ecx (by decide), ecxD]
    cases c0 <;> rfl

theorem reduce_ok {g : Geometry} (v : g.Valid) {e : State} (C : Context g e) :
    WP isa reduce e fun h =>
      Outside g.W (g.array 6) (4 * g.words) e.mem h.mem ∧ PtrAt h g.W .ebp (g.array 2 + 4 * g.words) ∧
      (∃ c1 : Bool, h.gpr .ecx = cmask c1 ∧ val32 h.mem g.W (g.array 6) g.words + val32 e.mem g.W (g.array 0) g.words =
        val32 e.mem g.W (g.array 2) g.words + 2 ^ (32 * g.words) * c1.toNat) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] e h := by
  obtain ⟨fit6, -, many, words⟩ := WitnessRt.fits v
  have bound := v.maxWidth
  have a26 : g.array 2 + 4 * g.words + 4 ≤ g.array 6 := by
    unfold Geometry.array Geometry.words Proof.Rsa.Mont.arrAt Proof.Rsa.Mont.hdrBytes; omega
  have a02 : g.array 0 + 4 * g.words ≤ g.array 2 := g.arrayBefore (by decide)
  unfold reduce
  refine WP.seq (WP.mono (reduceArgs_ok v C) fun f ⟨ebpF, ebxF, ediF, edxF, ecxF, Mf, Lf⟩ => ?_)
  refine WP.mono (VG.Proof.Bignum.X86.PublicRt.reduceLoop_ok (C.ws.of_keeps Lf) (a := g.array 2)
    (m := g.array 0) (d := g.array 6) (N := g.words) (by omega) (by omega) (by omega) fit6 (Or.inr (by omega))
    (Or.inr (by omega)) ebpF ebxF ediF edxF ecxF) fun h ⟨Oh, Ph, diff, Kh⟩ => ?_
  rw [Mf] at Oh diff
  exact ⟨Oh, Ph, diff, Lf.trans Kh⟩

theorem below_ok {h : State} {W : Addr} {L x : Nat} (hw : Ws h W L) (P : PtrAt h W .ebp x) (fit : x + 4 ≤ L)
    {q : BitVec 32} (St : StackContext q h) {c0 c1 : Bool} (carry : w32 h.mem W x = c0.toNat)
    (mask : h.gpr .ecx = cmask c1) :
    WP isa (.block VG.Impl.RsaKeyGen.X86.PrepareRt.below) h fun i =>
      i.gpr .ecx = cmask (decide (c0.toNat < c1.toNat)) ∧
      i.gpr .edi = h.mem.readW (off (q.setWidth 64) 0) 32 ∧ i.mem = h.mem ∧ Keeps [.eax, .ecx, .edi] h i := by
  unfold VG.Impl.RsaKeyGen.X86.PrepareRt.below
  refine wp_movS (readSrc_ptr hw P (d := 0) (by omega)) fun i1 I1 _ => ?_
  refine VG.Proof.Bignum.X86.PublicRt.wp_carry (c := c1) (by rw [I1.other .ecx (by decide)]; exact mask)
    fun i2 I2 cf2 => ?_
  refine wp_sbbS rfl cf2 fun i3 I3 cf3 => wp_sbb_self cf3 fun i4 I4 => wp_movS rfl fun i5 I5 _ => ?_
  have K5 : Keeps [.eax, .ecx] h i5 :=
    ((((I1.keeps.mono (by decide)).widen I2.keeps).widen I3.keeps).widen I4.keeps).widen I5.keeps
  have M5 : i5.mem = h.mem := by rw [I5.mem, I4.mem, I3.mem, I2.mem, I1.mem]
  refine wp_movS ((St.keep K5 (by decide)).read 0 (by decide)) fun i I _ => WP.block_nil ?_
  have carryI : (i2.gpr .eax).toNat = c0.toNat := by
    rw [I2.other .eax (by decide), I1.gpr, Nat.add_zero]; exact carry
  refine ⟨?_, by rw [I.gpr, M5], by rw [I.mem, M5], (K5.mono (by decide)).widen I.keeps⟩
  rw [I.other .ecx (by decide), I5.gpr, I4.gpr]
  have zero : (0 : BitVec 32).toNat = 0 := rfl
  simp only [carryI, zero, Nat.zero_add]

theorem select_ok {g : Geometry} (v : g.Valid) {i : State} {q : BitVec 32} {k : Nat} (C : Context g i)
    (St : StackContext q i) {b : Bool} (mask : i.gpr .ecx = cmask b)
    (count : i.gpr .esi = BitVec.ofNat 32 (k + 1)) (kBound : k + 1 < 2 ^ 32) :
    WP isa select i fun t =>
      val32 t.mem g.W (g.array 6) g.words =
        (if b then val32 i.mem g.W (g.array 2) g.words else val32 i.mem g.W (g.array 6) g.words) ∧
      Outside g.W (g.array 6) (4 * g.words) i.mem t.mem ∧
      t.gpr .edi = t.mem.readW (off (q.setWidth 64) 0) 32 ∧ t.gpr .esi = BitVec.ofNat 32 k ∧
      t.zf = some (decide (k = 0)) ∧ Keeps [.eax, .ebx, .edx, .ebp, .esi, .edi] i t := by
  obtain ⟨fit6, -, many, words⟩ := WitnessRt.fits v
  have bound := v.maxWidth
  have a26 : g.array 2 + 4 * g.words + 4 ≤ g.array 6 := by
    unfold Geometry.array Geometry.words Proof.Rsa.Mont.arrAt Proof.Rsa.Mont.hdrBytes; omega
  unfold select
  refine WP.seq (WP.mono (selectArgs_ok v C) fun j ⟨ebpJ, ebxJ, ediJ, Mj, Kij⟩ => ?_)
  have ecxJ : j.gpr .ecx = cmask b := by rw [Kij.1 .ecx (by decide)]; exact mask
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86.PublicRt.selectLoop_ok (C.ws.of_keeps Kij) (x := g.array 2)
    (d := g.array 6) (N := g.words) b (by omega) (by omega) fit6 (Or.inr (by omega))
    ebpJ ebxJ ediJ ecxJ) fun l ⟨Ol, Vl, _, Kl⟩ => ?_)
  rw [Mj] at Ol Vl
  unfold next
  have Kil : Keeps [.eax, .ebx, .edx, .ebp, .edi] i l := (Kij.mono (by decide)).trans Kl
  refine wp_movS ((St.keep Kil (by decide)).read 0 (by decide)) fun t1 T1 _ => wp_subZ rfl fun t T zt => WP.block_nil ?_
  have Mt : t.mem = l.mem := by rw [T.mem, T1.mem]
  have esiT1 : (t1.gpr .esi).toNat = (k + 1) - 0 := by
    rw [T1.other .esi (by decide), Kil.1 .esi (by decide), count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt kBound, Nat.sub_zero]
  obtain ⟨next, last⟩ := VG.Proof.Bignum.X86.PublicRt.count1_zf esiT1 (by omega)
  refine ⟨by rw [Mt]; exact Vl, by rw [Mt]; exact Ol, by rw [T.other .edi (by decide), T1.gpr, Mt], ?_, ?_,
    ((Kil.mono (by decide)).widen T1.keeps).widen T.keeps⟩
  · apply BitVec.eq_of_toNat_eq
    rw [T.gpr, next, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [zt, last]
    congr 1
    exact decide_eq_decide.mpr (by omega)

theorem double_ok {g : Geometry} (v : g.Valid) {a : State} {c T k : Nat} {q : BitVec 32}
    (C : Context g a) (M : Modulus g c a.mem) (St : StackContext q a)
    (saved : a.mem.readW (off (q.setWidth 64) 0) 32 = a.gpr .edi)
    (far : ∀ i < 4, ∀ r ∈ doubleRanges g, ofs g.W (off (q.setWidth 64) 0 + BitVec.ofNat 64 i) < r.1 ∨
      r.1 + r.2 ≤ ofs g.W (off (q.setWidth 64) 0 + BitVec.ofNat 64 i))
    (value : val32 a.mem g.W (g.array 6) g.words = T) (lt : T < c)
    (count : a.gpr .esi = BitVec.ofNat 32 (k + 1)) (kBound : k + 1 < 2 ^ 32) :
    WP isa double a fun t =>
      Context g t ∧ Modulus g c t.mem ∧ StackContext q t ∧
      t.mem.readW (off (q.setWidth 64) 0) 32 = t.gpr .edi ∧
      val32 t.mem g.W (g.array 6) g.words = (T + T) % c ∧ t.gpr .esi = BitVec.ofNat 32 k ∧
      t.zf = some (decide (k = 0)) ∧ Outs g.W (doubleRanges g) a.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] a t := by
  obtain ⟨fit6, -, many, words⟩ := WitnessRt.fits v
  have nowrap := C.ws.nowrap
  have a26 : g.array 2 + 4 * g.words + 4 ≤ g.array 6 := by
    unfold Geometry.array Geometry.words Proof.Rsa.Mont.arrAt Proof.Rsa.Mont.hdrBytes; omega
  have a02 : g.array 0 + 4 * g.words ≤ g.array 2 := g.arrayBefore (by decide)
  have h0 := v.arrayHeader 0
  have h2 := v.arrayHeader 2
  have cand := M.candidate
  have above : ∀ r ∈ doubleRanges g, 256 ≤ r.1 := fun r mem => by
    simp only [doubleRanges, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl <;> omega
  have readSaved {m : Mem} (O : Outs g.W (doubleRanges g) a.mem m) :
      m.readW (off (q.setWidth 64) 0) 32 = a.gpr .edi := by
    rw [← saved]
    exact Mem.readW_congr fun j hj => O _ (far j hj)
  unfold double
  refine WP.seq (WP.mono (sum_ok v C value) fun e ⟨Ce, Oe, ⟨c0, sumE, carryE⟩, Ke⟩ => ?_)
  refine WP.seq (WP.mono (reduce_ok v Ce) fun h ⟨Oh, Ph, ⟨c1, ecxH, diffH⟩, Kh⟩ => ?_)
  have Oah : Outs g.W (doubleRanges g) a.mem h.mem :=
    (Outs.of_outside Oe (by simp [doubleRanges])).trans (Outs.of_outside Oh (by simp [doubleRanges]))
  have Kah : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] a h := (Ke.mono (by decide)).trans Kh
  have carryH : w32 h.mem g.W (g.array 2 + 4 * g.words) = c0.toNat := by
    rw [Oh.w32 (Or.inl (by omega)) (by omega)]; exact carryE
  refine WP.seq (WP.mono (below_ok (C.ws.of_keeps Kah) Ph (by omega) (St.keep Kah (by decide)) carryH ecxH)
    fun i ⟨maskI, ediI, Mi, Ki⟩ => ?_)
  rw [readSaved Oah] at ediI
  have Kai : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] a i := Kah.trans (Ki.mono (by decide))
  have Ci : Context g i := Context.restore C Kai.2.2 ediI (by rw [Mi]; exact Oah) above
  have esiI : i.gpr .esi = BitVec.ofNat 32 (k + 1) := by rw [Kai.1 .esi (by decide)]; exact count
  refine WP.mono (select_ok v Ci (St.keep Kai (by decide)) maskI esiI kBound)
    fun t ⟨Vt, Ot, ediT, esiT, zt, Kt⟩ => ?_
  rw [Mi] at Vt Ot
  have Oat : Outs g.W (doubleRanges g) a.mem t.mem := Oah.trans (Outs.of_outside Ot (by simp [doubleRanges]))
  rw [readSaved Oat] at ediT
  have Kall : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi, .esi] a t := (Kai.mono (by decide)).trans (Kt.mono (by decide))
  have K : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] a t := by
    refine ⟨fun r mem => ?_, Kall.2⟩
    by_cases same : r = .edi
    · subst r; exact ediT
    · exact Kall.1 r (by cases r <;> simp_all)
  refine ⟨Context.restore C K.2.2 ediT Oat above,
    M.keep v (WorkspaceFrame.of_outs nowrap Oat) (fun r mem => Or.inl (by have := above r mem; omega))
      (fun r mem => by
        simp only [doubleRanges, List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl <;> left <;> omega),
    St.keep K (by decide), by rw [readSaved Oat, ediT], ?_, esiT, zt, Oat, K⟩
  rw [Vt]
  have candE : val32 e.mem g.W (g.array 0) g.words = c := by
    rw [Oe.val32 (Or.inl (by omega)) (by omega)]; exact cand
  rw [candE] at diffH
  have sameSum : val32 h.mem g.W (g.array 2) g.words = val32 e.mem g.W (g.array 2) g.words :=
    Oh.val32 (Or.inl (by omega)) (by omega)
  rw [sameSum]
  simp only [decide_eq_true_eq]
  have hc : c < 2 ^ (32 * g.words) := by rw [← cand]; exact val32_lt _ _ _ _
  exact double_mod (B := 2 ^ (32 * g.words)) hc lt (Bool.toNat_le c0) (Bool.toNat_le c1)
    (val32_lt _ _ _ _) sumE diffH

end VG.Proof.RsaKeyGen.X86.PrepareRt
