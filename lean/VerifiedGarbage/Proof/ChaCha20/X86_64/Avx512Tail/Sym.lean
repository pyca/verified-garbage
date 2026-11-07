module
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Sym

import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.Block

/-!
# ChaCha20 on x86-64 with AVX-512, the last bytes: straight-line code

As for the sixteen blocks (`Avx512/Sym.lean`), every instruction of the code
around the rounds moves, adds or XORs doublewords of `zmm` registers and of
three regions of memory, here the state (at `rdi`), `buf` (at `r9`, of which
the first 256 bytes are written) and `4 D` bytes of data (at `rsi`).
`run` computes each doubleword after a block of such instructions as a term
(`Avx512.T`) in the doublewords before it, and `srun_ok` proves the machine
agrees. `vporq` of a register with itself moves it. From a source to a
destination (`to`, `runT`, `SRelT`), as for the sixteen blocks, the data at
`rsi` is the source and the destination, at `rsi + r11`, region 3
(`Avx512.dstR`). The regions and the destination serve the code of
`Avx2Tail` too.
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.Avx512Tail

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx512Tail
open VG.Spec.ChaCha20 (Word)
open VG.Proof.ChaCha20.X86_64.Avx512 (T Sym Sym.init Sym.setReg zbinT dwordwise zw zw_split zw_lk
  sel2 sel2_eq sel2_lt pick4_same pick4_ext dword_read512 add_ofNat' ofInt_ofNat xidx xidx_lt xidx_inj
  div4_lt mod4_lt zreg_xidx dword_rep4 pick4_fn dstR slotD slotD_ok symStore clean3 clean3_of Ctx3 src_keep
  zmm_dword)

/-- The base register of region `b`: the state, `buf` and the data. -/
def baseR : Nat → Reg
  | 0 => .rdi | 1 => .r9 | _ => .rsi

/-- The doublewords of region `b`, with `D` of data. -/
def bsize (D : Nat) : Nat → Nat
  | 0 => 16 | 1 => 80 | _ => D

/-- The doublewords of region `b` that may be written. -/
def wsize (D : Nat) : Nat → Nat
  | 0 => 0 | 1 => 64 | _ => D

def bidx : Reg → Option Nat
  | .rdi => some 0 | .r9 => some 1 | .rsi => some 2 | _ => none

theorem bidx_some {r : Reg} {b : Nat} (h : bidx r = some b) : r = baseR b ∧ b < 3 := by
  cases r <;> simp only [bidx, reduceCtorEq, Option.some.injEq] at h <;> subst h <;> decide

/-- Region `b`, where the code starts. -/
def regn (D : Nat) (s₀ : State) (b : Nat) : Region := ⟨s₀.gpr (baseR b), 4 * bsize D b⟩

/-- The regions written. -/
def wregs (D : Nat) (s₀ : State) : List Region := [⟨s₀.gpr .r9, 256⟩, ⟨s₀.gpr .rsi, 4 * D⟩]

/-- Where region `b` starts: from a source to a destination, the
destination is region 3. -/
def memBase (D : Nat) (s₀ : State) (b : Nat) : Addr :=
  if b = 3 then (dstR D s₀).base else (regn D s₀ b).base

theorem memBase_0 (D : Nat) (s₀ : State) : memBase D s₀ 0 = s₀.gpr .rdi := rfl
theorem memBase_1 (D : Nat) (s₀ : State) : memBase D s₀ 1 = s₀.gpr .r9 := rfl
theorem memBase_2 (D : Nat) (s₀ : State) : memBase D s₀ 2 = s₀.gpr .rsi := rfl
theorem memBase_3 (D : Nat) (s₀ : State) : memBase D s₀ 3 = (dstR D s₀).base := rfl
theorem memBase_lt {D : Nat} {s₀ : State} {b : Nat} (hb : b < 3) : memBase D s₀ b = (regn D s₀ b).base := by
  simp only [memBase, show b ≠ 3 by omega_arith, ite_false]

def T.eval (D : Nat) (s₀ : State) : T → Word
  | .reg r p => zw s₀ (VG.Impl.ChaCha20.X86_64.Avx512.zreg r) p
  | .mem b i => s₀.mem.readW (memBase D s₀ b + BitVec.ofNat 64 (4 * i)) 32
  | .add a b => T.eval D s₀ a + T.eval D s₀ b
  | .xor a b => T.eval D s₀ a ^^^ T.eval D s₀ b
  | .inp i => VG.Proof.ChaCha20.X86_64.Avx512.inpW s₀ i

/-- The region and first doubleword of an access of `n` doublewords, within
the first `lim b` doublewords of its region `b`. -/
def slot (m : MemOp) (n : Nat) (lim : Nat → Nat) : Option (Nat × Nat) :=
  match bidx m.base, m.index, m.disp with
  | some b, none, .ofNat d => if d % 4 = 0 ∧ d / 4 + n ≤ lim b then some (b, d / 4) else none
  | _, _, _ => none

def stepT (to : Bool) (D : Nat) (σ : Sym) : Instr → Option Sym
  | .zop (.zbin op d a b) =>
    if dwordwise op then some (σ.setReg (xidx d) (zbinT op (σ.reg (xidx a)) (σ.reg (xidx b))))
    else if op = .vporq ∧ a = b then some (σ.setReg (xidx d) (σ.reg (xidx a)))
    else none
  | .zop (.vpshufd d a o) =>
    some (σ.setReg (xidx d) fun p => σ.reg (xidx a) (4 * (p / 4) + sel2 o.toNat (p % 4)))
  | .zop (.vshufi32x4 d a b n) =>
    some (σ.setReg (xidx d) fun p =>
      (if p / 4 < 2 then σ.reg (xidx a) else σ.reg (xidx b)) (4 * sel2 n.toNat (p / 4) + p % 4))
  | .vmovdqu32Load d m => (slot m 16 (bsize D)).bind fun (b, i) =>
    if to = true ∧ b = 2 ∧ clean3 σ i 16 = false then none
    else some (σ.setReg (xidx d) fun p => σ.mem b (i + p))
  | .vbroadcasti32x4 d m => (slot m 4 (bsize D)).bind fun (b, i) =>
    if to = true ∧ b = 2 ∧ clean3 σ i 4 = false then none
    else some (σ.setReg (xidx d) fun p => σ.mem b (i + p % 4))
  | .vmovdqu32Store m r =>
    if to then
      match slotD m 16 D with
      | some i => some (symStore σ 3 i 16 (xidx r))
      | none => (slot m 16 (wsize 0)).map fun (b, i) => symStore σ b i 16 (xidx r)
    else (slot m 16 (wsize D)).map fun (b, i) => symStore σ b i 16 (xidx r)
  | .vpbroadcastdZ d m => (slot m 1 (bsize D)).bind fun (b, i) =>
    if to = true ∧ b = 2 ∧ clean3 σ i 1 = false then none
    else some (σ.setReg (xidx d) fun _ => σ.mem b i)
  | .zbcstd .vpaddd d a m => (slot m 1 (bsize D)).bind fun (b, i) =>
    if to = true ∧ b = 2 ∧ clean3 σ i 1 = false then none
    else some (σ.setReg (xidx d) fun p => .add (σ.reg (xidx a) p) (σ.mem b i))
  | _ => none

def runT (to : Bool) (D : Nat) (σ : Sym) : List Instr → Option Sym
  | [] => some σ
  | i :: is => (stepT to D σ i).bind fun σ' => runT to D σ' is

/-- In place. -/
abbrev step (D : Nat) := stepT false D
abbrev run (D : Nat) := runT false D

/-! ## The machine agrees -/

theorem slot_ok {m : MemOp} {n : Nat} {lim : Nat → Nat} {b i : Nat} (h : slot m n lim = some (b, i)) :
    b < 3 ∧ i + n ≤ lim b ∧ ∀ s : State, s.ea m = s.gpr (baseR b) + BitVec.ofNat 64 (4 * i) := by
  unfold slot at h
  split at h
  · rename_i b' d hb hi hd
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨e, hb3⟩ := bidx_some hb
      refine ⟨hb3, hc.2, fun s => ?_⟩
      simp only [State.ea, hi, hd, ofInt_ofNat, ← e]
      rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hc.1)]
    · cases h
  · cases h

theorem wsize_le (D b : Nat) : wsize D b ≤ bsize D b := by
  unfold wsize bsize; split <;> omega_arith

/-- The regions: writable (and so readable) and disjoint. -/
structure Ctx (D : Nat) (s₀ : State) : Prop where
  w : ∀ b i n, b < 3 → i + n ≤ bsize D b → 0 < n →
    InRegions s₀.wr ((regn D s₀ b).base + BitVec.ofNat 64 (4 * i)) (4 * n)
  d : ∀ b b', b < 3 → b' < 3 → b ≠ b' → (regn D s₀ b).Disjoint (regn D s₀ b')
  small : D ≤ 128

theorem bsize_le {D : Nat} (h : D ≤ 128) (b : Nat) : bsize D b ≤ 128 := by
  unfold bsize; split <;> omega_arith

theorem regn_contains {D : Nat} (hD : D ≤ 128) (s₀ : State) {b i n : Nat} (h : i + n ≤ bsize D b) :
    (regn D s₀ b).Contains ((regn D s₀ b).base + BitVec.ofNat 64 (4 * i)) (4 * n) := by
  have := bsize_le hD b
  simp only [Region.Contains]
  rw [Mem.sub_ofNat_toNat _ (by omega_arith)]
  simp only [regn]; omega_arith

/-- The regions, in place or from a source to a destination (`to`): the
state and `buf` as `Ctx 0` has them, the source and the destination as
`Ctx3`. -/
def CtxT : Bool → Nat → State → Prop
  | false, D, s₀ => Ctx D s₀
  | true, D, s₀ => Ctx 0 s₀ ∧ Ctx3 (regn D s₀) D s₀ ∧ D ≤ 128

/-- The regions written. -/
def wregsT : Bool → Nat → State → List Region
  | false, D, s₀ => wregs D s₀
  | true, D, s₀ => [⟨s₀.gpr .r9, 256⟩, dstR D s₀]

/-- The terms `σ` hold in `s`: in the registers, and in regions 0 to 2 (from
a source to a destination, in the source where its destination is as on
entry) and the destination. -/
structure SRelT (to : Bool) (D : Nat) (σ : Sym) (s₀ s : State) : Prop where
  reg : ∀ r p, p < 16 → zw s r p = T.eval D s₀ (σ.reg (xidx r) p)
  mem : ∀ b i, b < 3 → i < bsize D b → (to = true → b = 2 → σ.mem 3 i = .mem 3 i) →
    s.mem.readW ((regn D s₀ b).base + BitVec.ofNat 64 (4 * i)) 32 = T.eval D s₀ (σ.mem b i)
  mem3 : to = true → ∀ i < D,
    s.mem.readW ((dstR D s₀).base + BitVec.ofNat 64 (4 * i)) 32 = T.eval D s₀ (σ.mem 3 i)
  src : to = true → ∀ i, σ.mem 2 i = .mem 2 i
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (wregsT to D s₀) s₀.mem s.mem
  clean : σ.dirty = false → s.mem = s₀.mem

/-- In place. -/
abbrev SRel (D : Nat) := SRelT false D

theorem SRel.mem {D : Nat} {σ : Sym} {s₀ s : State} (h : SRel D σ s₀ s) :
    ∀ b i, b < 3 → i < bsize D b →
      s.mem.readW ((regn D s₀ b).base + BitVec.ofNat 64 (4 * i)) 32 = T.eval D s₀ (σ.mem b i) :=
  fun b i hb hi => SRelT.mem h b i hb hi (fun e => nomatch e)

/-- In place, from what `SRelT` asks of the registers and the regions. -/
theorem SRel.mk' {D : Nat} {σ : Sym} {s₀ s : State} (hr : ∀ r p, p < 16 → zw s r p = T.eval D s₀ (σ.reg (xidx r) p))
    (hm : ∀ b i, b < 3 → i < bsize D b →
      s.mem.readW ((regn D s₀ b).base + BitVec.ofNat 64 (4 * i)) 32 = T.eval D s₀ (σ.mem b i))
    (hg : s.gpr = s₀.gpr) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hf : Frame (wregs D s₀) s₀.mem s.mem)
    (hc : σ.dirty = false → s.mem = s₀.mem) : SRel D σ s₀ s :=
  ⟨hr, fun b i hb hi _ => hm b i hb hi, (fun e => nomatch e), (fun e => nomatch e), hg, hrd, hwr, hf, hc⟩

theorem SRelT.init (to : Bool) (D : Nat) (s₀ : State) : SRelT to D Sym.init s₀ s₀ :=
  ⟨fun r p _ => by simp only [Sym.init, T.eval, zreg_xidx],
   fun b i hb _ _ => by simp only [Sym.init, T.eval, memBase_lt hb],
   fun _ i _ => by simp only [Sym.init, T.eval, memBase_3],
   fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ => rfl⟩

theorem SRel.init (D : Nat) (s₀ : State) : SRel D Sym.init s₀ s₀ := SRelT.init false D s₀

theorem SRelT.setReg {to : Bool} {D : Nat} {σ : Sym} {s₀ s s' : State} (h : SRelT to D σ s₀ s) {d : XReg}
    {f : Nat → T} (hz : ∀ r p, p < 16 → zw s' r p = if r = d then T.eval D s₀ (f p) else zw s r p)
    (hm : s'.mem = s.mem) (hg : s'.gpr = s.gpr) (hr : s'.rd = s.rd) (hw : s'.wr = s.wr) :
    SRelT to D (σ.setReg (xidx d) f) s₀ s' := by
  refine ⟨fun r p hp => ?_, fun b i hb hi hc => by rw [hm]; exact h.mem b i hb hi hc,
    fun ht i hi => by rw [hm]; exact h.mem3 ht i hi, h.src, hg.trans h.gpr,
    hr.trans h.rd, hw.trans h.wr, hm ▸ h.frame, fun hd => hm.trans (h.clean hd)⟩
  rw [hz r p hp]
  simp only [Sym.setReg, xidx_inj]
  split
  · rfl
  · exact h.reg r p hp

theorem SRel.setReg {D : Nat} {σ : Sym} {s₀ s s' : State} (h : SRel D σ s₀ s) {d : XReg} {f : Nat → T}
    (hz : ∀ r p, p < 16 → zw s' r p = if r = d then T.eval D s₀ (f p) else zw s r p)
    (hm : s'.mem = s.mem) (hg : s'.gpr = s.gpr) (hr : s'.rd = s.rd) (hw : s'.wr = s.wr) :
    SRel D (σ.setReg (xidx d) f) s₀ s' :=
  SRelT.setReg h hz hm hg hr hw

theorem in_regn {D : Nat} {s₀ s : State} (hc : Ctx D s₀) {b : Nat} (hb : b < 3) (hw : s.wr = s₀.wr)
    {i n : Nat} (h : i + n ≤ bsize D b) (hn : 0 < n) :
    InRegions s.wr ((regn D s₀ b).base + BitVec.ofNat 64 (4 * i)) (4 * n) :=
  hw ▸ hc.w b i n hb h hn

theorem in_regn' {D : Nat} {s₀ s : State} (hc : Ctx D s₀) {b : Nat} (hb : b < 3) (hw : s.wr = s₀.wr)
    {i n : Nat} (h : i + n ≤ bsize D b) (hn : 0 < n) :
    InRegions (s.rd ++ s.wr) ((regn D s₀ b).base + BitVec.ofNat 64 (4 * i)) (4 * n) :=
  let ⟨r, hr, hc'⟩ := in_regn hc hb hw h hn; ⟨r, List.mem_append_right _ hr, hc'⟩

theorem zbinT_eval {D : Nat} {op : ZBinOp} (hop : dwordwise op = true) {A B : Nat → T} {s₀ : State}
    {x y : BitVec 128} {p : Nat}
    (hA : ∀ k, k < 4 → T.eval D s₀ (A (4 * (p / 4) + k)) = dword x k)
    (hB : ∀ k, k < 4 → T.eval D s₀ (B (4 * (p / 4) + k)) = dword y k) :
    T.eval D s₀ (zbinT op A B p) = dword (op.sse.eval x y) (p % 4) := by
  have hq : p % 4 < 4 := Nat.mod_lt _ (by decide)
  simp only [zbinT]
  generalize p % 4 = q at *
  generalize 4 * (p / 4) = l at *
  have a0 := hA 0 (by decide); have a1 := hA 1 (by decide)
  have a2 := hA 2 (by decide); have a3 := hA 3 (by decide)
  have b0 := hB 0 (by decide); have b1 := hB 1 (by decide)
  have b2 := hB 2 (by decide); have b3 := hB 3 (by decide)
  rcases cases4 hq with rfl | rfl | rfl | rfl <;> cases op <;> (try cases hop) <;>
    simp only [ZBinOp.sse, T.eval, dword_paddd _ _ (show (0 : Nat) < 4 by decide),
      dword_paddd _ _ (show (1 : Nat) < 4 by decide), dword_paddd _ _ (show (2 : Nat) < 4 by decide),
      dword_paddd _ _ (show (3 : Nat) < 4 by decide), dword_pxor, dword_punpckldq, dword_punpckhdq,
      punpcklqdq_eq, punpckhqdq_eq, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2,
      dword_ofDwords_3, Nat.reduceMod, Nat.reduceDiv, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff,
      ite_true, ite_false, a0, a1, a2, a3, b0, b1, b2, b3]

theorem por_self (x : BitVec 128) : XBinOp.eval .por x x = x := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [XBinOp.eval]

theorem CtxT.small {to : Bool} {D : Nat} {s₀ : State} (hc : CtxT to D s₀) : D ≤ 128 := by
  cases to
  · exact Ctx.small hc
  · exact hc.2.2

/-- Reads of regions 0 to 2 are permitted. -/
theorem CtxT.rd {to : Bool} {D : Nat} {s₀ s : State} (hc : CtxT to D s₀) {b : Nat} (hb : b < 3)
    (hr : s.rd = s₀.rd) (hw : s.wr = s₀.wr) {i n : Nat} (h : i + n ≤ bsize D b) (hn : 0 < n) :
    InRegions (s.rd ++ s.wr) ((regn D s₀ b).base + BitVec.ofNat 64 (4 * i)) (4 * n) := by
  cases to
  · exact in_regn' hc hb hw h hn
  · rcases (by omega_arith : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl
    · exact in_regn' hc.1 (b := 0) (by decide) hw h hn
    · exact in_regn' hc.1 (b := 1) (by decide) hw h hn
    · rw [hr, hw]; exact hc.2.1.src i n h hn

/-- From a source to a destination: the source where its destination is as
on entry is as on entry (`Avx512.src_keep`). -/
theorem src_after {D : Nat} {s₀ : State} (hc : Ctx 0 s₀ ∧ Ctx3 (regn D s₀) D s₀ ∧ D ≤ 128) {t : Mem}
    (hf : Frame (wregsT true D s₀) s₀.mem t) {i : Nat} (hi : i < D)
    (h3 : t.readW ((dstR D s₀).base + BitVec.ofNat 64 (4 * i)) 32 =
      s₀.mem.readW ((dstR D s₀).base + BitVec.ofNat 64 (4 * i)) 32) :
    t.readW ((regn D s₀ 2).base + BitVec.ofNat 64 (4 * i)) 32 =
      s₀.mem.readW ((regn D s₀ 2).base + BitVec.ofNat 64 (4 * i)) 32 :=
  src_keep hc.2.1 rfl (B := ⟨s₀.gpr .r9, 256⟩)
    (by simp only [regn, baseR, bsize]; exact Region.sub_prefix (by omega_arith)) hf
    (regn_contains hc.2.2 s₀ (n := 1) (by simp only [bsize]; omega_arith)) h3

theorem dst_contains {D : Nat} (hD : D ≤ 128) (s₀ : State) {j n : Nat} (hj : j + n ≤ D) :
    (dstR D s₀).Contains ((dstR D s₀).base + BitVec.ofNat 64 (4 * j)) (4 * n) := by
  simp only [Region.Contains, dstR]; rw [Mem.sub_ofNat_toNat _ (by omega_arith)]; omega_arith

/-- A store in place, to `buf` or the data. -/
theorem store_ok {D : Nat} {s₀ : State} (hc : Ctx D s₀) {σ : Sym} {s : State} (h : SRel D σ s₀ s)
    {m : MemOp} {r : XReg} {b i : Nat} (hs : slot m 16 (wsize D) = some (b, i)) :
    ∃ s', exec (.vmovdqu32Store m r) s = some s' ∧ SRel D (symStore σ b i 16 (xidx r)) s₀ s' := by
  have hD := hc.small
  obtain ⟨hb, hi, hea⟩ := slot_ok hs
  have hi' : i + 16 ≤ bsize D b := Nat.le_trans hi (wsize_le D b)
  have hb0 : b = 1 ∨ b = 2 := by
    rcases (by omega_arith : b = 0 ∨ b = 1 ∨ b = 2) with rfl | e | e
    · simp [wsize] at hi
    · exact .inl e
    · exact .inr e
  have ea : s.ea m = (regn D s₀ b).base + BitVec.ofNat 64 (4 * i) := by rw [hea, h.gpr]; rfl
  have hin := in_regn hc hb h.wr hi' (by decide)
  refine ⟨s.setMem (s.mem.writeW ((regn D s₀ b).base + BitVec.ofNat 64 (4 * i)) (s.zmm r)),
    by simp only [exec, ea, State.store512_eq, hin, ite_true], SRel.mk' (fun r' p hp => ?_)
    (fun b' i' hb' hi'' => ?_) (by simp [h.gpr]) (by simp [h.rd]) (by simp [h.wr]) ?_ fun hd => by cases hd⟩
  · simp only [zw_split, State.setMem_zlane]; exact h.reg r' p hp
  · simp only [State.setMem_mem, symStore]
    by_cases e : b' = b
    · subst e
      rw [Avx512.read_store16 (by have := bsize_le hD b'; omega_arith) hi' hi'']
      by_cases hx : i ≤ i' ∧ i' < i + 16
      · rw [ite_eq_left hx, ite_eq_left ⟨rfl, hx⟩, zmm_dword _ _ (by omega_arith)]
        exact h.reg r _ (by omega_arith)
      · rw [ite_eq_right hx, ite_eq_right (fun h' => hx h'.2)]
        exact h.mem b' i' hb' hi''
    · have f := (Frame.refl [regn D s₀ b] s.mem).writeW (List.mem_singleton_self _) (s.zmm r)
        (regn_contains hD s₀ (n := 16) hi')
      rw [f.readW (r := regn D s₀ b') (regn_contains hD s₀ (n := 1) (by omega_arith))
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hc.d b' b hb' hb e)
        (by decide), ite_eq_right (fun hx => e hx.1)]
      exact h.mem b' i' hb' hi''
  · simp only [State.setMem_mem]
    refine h.frame.writeW (r := if b = 1 then ⟨s₀.gpr .r9, 256⟩ else ⟨s₀.gpr .rsi, 4 * D⟩)
      (by rcases hb0 with rfl | rfl <;> simp [wregsT, wregs]) _ ?_
    rcases hb0 with rfl | rfl
    · simp only [regn, baseR, Region.Contains, ite_true]
      simp only [wsize] at hi; rw [Mem.sub_ofNat_toNat _ (by omega_arith)]; omega_arith
    · simp only [regn, baseR, Region.Contains, show (2 : Nat) ≠ 1 by decide, ite_false]
      simp only [wsize] at hi; rw [Mem.sub_ofNat_toNat _ (by omega_arith)]; omega_arith

/-- From a source to a destination: a store to the destination. -/
theorem store3_ok {D : Nat} {s₀ : State} (hc : Ctx 0 s₀ ∧ Ctx3 (regn D s₀) D s₀ ∧ D ≤ 128) {σ : Sym}
    {s : State} (h : SRelT true D σ s₀ s) {m : MemOp} {r : XReg} {i : Nat} (hs : slotD m 16 D = some i) :
    ∃ s', exec (.vmovdqu32Store m r) s = some s' ∧ SRelT true D (symStore σ 3 i 16 (xidx r)) s₀ s' := by
  have hD := hc.2.2
  obtain ⟨hi, hea⟩ := slotD_ok hs
  have ea : s.ea m = (dstR D s₀).base + BitVec.ofNat 64 (4 * i) := by rw [hea, h.gpr]; rfl
  have hin : InRegions s.wr ((dstR D s₀).base + BitVec.ofNat 64 (4 * i)) (4 * 16) := by
    rw [h.wr]; exact hc.2.1.w i 16 hi (by decide)
  have f := (Frame.refl [dstR D s₀] s.mem).writeW (List.mem_singleton_self _) (s.zmm r) (dst_contains hD s₀ hi)
  have F : Frame (wregsT true D s₀) s₀.mem
      (s.mem.writeW ((dstR D s₀).base + BitVec.ofNat 64 (4 * i)) (s.zmm r)) :=
    h.frame.writeW (r := dstR D s₀) (by simp [wregsT]) _ (dst_contains hD s₀ hi)
  have m3 : ∀ j < D, (s.mem.writeW ((dstR D s₀).base + BitVec.ofNat 64 (4 * i)) (s.zmm r)).readW
      ((dstR D s₀).base + BitVec.ofNat 64 (4 * j)) 32 = T.eval D s₀ ((symStore σ 3 i 16 (xidx r)).mem 3 j) := by
    intro j hj
    rw [Avx512.read_store16 (by omega_arith) hi hj]
    simp only [symStore, true_and]
    by_cases hx : i ≤ j ∧ j < i + 16
    · rw [ite_eq_left hx, ite_eq_left hx, zmm_dword _ _ (by omega_arith)]
      exact h.reg r _ (by omega_arith)
    · rw [ite_eq_right hx, ite_eq_right hx]
      exact h.mem3 rfl j hj
  have hs2 : ∀ j, (symStore σ 3 i 16 (xidx r)).mem 2 j = .mem 2 j := fun j => by
    simp only [symStore, show (2 : Nat) ≠ 3 by decide, false_and, ite_false]; exact h.src rfl j
  refine ⟨s.setMem (s.mem.writeW ((dstR D s₀).base + BitVec.ofNat 64 (4 * i)) (s.zmm r)),
    by simp only [exec, ea, State.store512_eq, hin, ite_true], ⟨fun r' p hp => ?_,
    fun b' i' hb' hi'' hcl => ?_, fun _ => m3, fun _ => hs2, by simp [h.gpr], by simp [h.rd],
    by simp [h.wr], F, fun hd => by cases hd⟩⟩
  · simp only [zw_split, State.setMem_zlane]; exact h.reg r' p hp
  · simp only [State.setMem_mem]
    have e3 : (symStore σ 3 i 16 (xidx r)).mem b' i' = σ.mem b' i' := by
      simp only [symStore, show b' ≠ 3 by omega_arith, false_and, ite_false]
    rcases (by omega_arith : b' = 0 ∨ b' = 1 ∨ b' = 2) with rfl | rfl | rfl
    · rw [e3, f.readW (r := regn D s₀ 0) (regn_contains hD s₀ (n := 1) (by omega_arith))
        (by simpa using (hc.2.1.d 0 (by decide)).1) (by decide)]
      exact h.mem 0 i' hb' hi'' (fun _ e => nomatch e)
    · rw [e3, f.readW (r := regn D s₀ 1) (regn_contains hD s₀ (n := 1) (by omega_arith))
        (by simpa using (hc.2.1.d 1 (by decide)).1) (by decide)]
      exact h.mem 1 i' hb' hi'' (fun _ e => nomatch e)
    · have hi2 : i' < D := by simpa [bsize] using hi''
      rw [hs2 i']
      simp only [T.eval, memBase_2]
      refine src_after hc F hi2 ?_
      have := m3 i' hi2
      rw [hcl rfl rfl] at this
      simpa only [T.eval, memBase_3] using this

/-- From a source to a destination: a store to `buf`. -/
theorem storeB_ok {D : Nat} {s₀ : State} (hc : Ctx 0 s₀ ∧ Ctx3 (regn D s₀) D s₀ ∧ D ≤ 128) {σ : Sym}
    {s : State} (h : SRelT true D σ s₀ s) {m : MemOp} {r : XReg} {b i : Nat} (hs : slot m 16 (wsize 0) = some (b, i)) :
    ∃ s', exec (.vmovdqu32Store m r) s = some s' ∧ SRelT true D (symStore σ b i 16 (xidx r)) s₀ s' := by
  have hD := hc.2.2
  obtain ⟨hb, hi, hea⟩ := slot_ok hs
  have hb1 : b = 1 := by
    rcases (by omega_arith : b = 0 ∨ b = 1 ∨ b = 2) with rfl | e | rfl
    · simp [wsize] at hi
    · exact e
    · simp [wsize] at hi
  subst hb1
  have hi' : i + 16 ≤ bsize D 1 := Nat.le_trans hi (by simp [wsize, bsize])
  have ea : s.ea m = (regn D s₀ 1).base + BitVec.ofNat 64 (4 * i) := by rw [hea, h.gpr]; rfl
  have hin : InRegions s.wr ((regn D s₀ 1).base + BitVec.ofNat 64 (4 * i)) (4 * 16) :=
    in_regn hc.1 (b := 1) (by decide) h.wr hi' (by decide)
  have f := (Frame.refl [regn D s₀ 1] s.mem).writeW (List.mem_singleton_self _) (s.zmm r)
    (regn_contains hD s₀ (n := 16) hi')
  have F : Frame (wregsT true D s₀) s₀.mem
      (s.mem.writeW ((regn D s₀ 1).base + BitVec.ofNat 64 (4 * i)) (s.zmm r)) :=
    h.frame.writeW (r := ⟨s₀.gpr .r9, 256⟩) (by simp [wregsT]) _ (by
      simp only [regn, baseR, Region.Contains]
      simp only [wsize] at hi; rw [Mem.sub_ofNat_toNat _ (by omega_arith)]; omega_arith)
  have m3 : ∀ j < D, (s.mem.writeW ((regn D s₀ 1).base + BitVec.ofNat 64 (4 * i)) (s.zmm r)).readW
      ((dstR D s₀).base + BitVec.ofNat 64 (4 * j)) 32 = T.eval D s₀ ((symStore σ 1 i 16 (xidx r)).mem 3 j) := by
    intro j hj
    rw [f.readW (r := dstR D s₀) (dst_contains hD s₀ (n := 1) (by omega_arith))
      (by simpa using (hc.2.1.d 1 (by decide)).1.symm) (by decide)]
    simp only [symStore, show (3 : Nat) ≠ 1 by decide, false_and, ite_false]
    exact h.mem3 rfl j hj
  have hs2 : ∀ j, (symStore σ 1 i 16 (xidx r)).mem 2 j = .mem 2 j := fun j => by
    simp only [symStore, show (2 : Nat) ≠ 1 by decide, false_and, ite_false]; exact h.src rfl j
  refine ⟨s.setMem (s.mem.writeW ((regn D s₀ 1).base + BitVec.ofNat 64 (4 * i)) (s.zmm r)),
    by simp only [exec, ea, State.store512_eq, hin, ite_true], ⟨fun r' p hp => ?_,
    fun b' i' hb' hi'' hcl => ?_, fun _ => m3, fun _ => hs2, by simp [h.gpr], by simp [h.rd],
    by simp [h.wr], F, fun hd => by cases hd⟩⟩
  · simp only [zw_split, State.setMem_zlane]; exact h.reg r' p hp
  · simp only [State.setMem_mem]
    rcases (by omega_arith : b' = 0 ∨ b' = 1 ∨ b' = 2) with rfl | rfl | rfl
    · rw [f.readW (r := regn D s₀ 0) (regn_contains hD s₀ (n := 1) (by omega_arith))
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact hc.1.d 0 1 (by decide) (by decide) (by decide))
        (by decide)]
      simp only [symStore, show (0 : Nat) ≠ 1 by decide, false_and, ite_false]
      exact h.mem 0 i' hb' hi'' (fun _ e => nomatch e)
    · rw [Avx512.read_store16 (by have := bsize_le hD 1; omega_arith) hi' hi'']
      simp only [symStore, true_and]
      by_cases hx : i ≤ i' ∧ i' < i + 16
      · rw [ite_eq_left hx, ite_eq_left hx, zmm_dword _ _ (by omega_arith)]
        exact h.reg r _ (by omega_arith)
      · rw [ite_eq_right hx, ite_eq_right hx]
        exact h.mem 1 i' hb' hi'' (fun _ e => nomatch e)
    · have hi2 : i' < D := by simpa [bsize] using hi''
      rw [hs2 i']
      simp only [T.eval, memBase_2]
      refine src_after hc F hi2 ?_
      have := m3 i' hi2
      rw [hcl rfl rfl] at this
      simpa only [T.eval, memBase_3] using this

/-- One instruction. -/
theorem sstepT_ok {to : Bool} {D : Nat} {s₀ : State} (hc : CtxT to D s₀) {σ σ' : Sym} {s : State}
    (h : SRelT to D σ s₀ s) {i : Instr} (e : stepT to D σ i = some σ') :
    ∃ s', exec i s = some s' ∧ SRelT to D σ' s₀ s' := by
  have hD := hc.small
  unfold stepT at e
  split at e
  · rename_i op d a b
    split at e
    · rename_i hop
      cases e
      refine ⟨_, rfl, h.setReg (fun r p hp => ?_) (by simp) (by simp) (by simp) (by simp)⟩
      rw [zw_split, zlane_zbin _ _ _ _ _ _ (div4_lt hp)]
      split
      · exact (zbinT_eval hop (fun k hk => (h.reg a _ (by omega_arith)).symm.trans (zw_lk s a hk))
          (fun k hk => (h.reg b _ (by omega_arith)).symm.trans (zw_lk s b hk))).symm
      · rfl
    · split at e
      · rename_i hor
        obtain ⟨rfl, rfl⟩ := hor
        cases e
        refine ⟨_, rfl, h.setReg (fun r p hp => ?_) (by simp) (by simp) (by simp) (by simp)⟩
        rw [zw_split, zlane_zbin _ _ _ _ _ _ (div4_lt hp)]
        split
        · simp only [ZBinOp.sse, por_self]
          rw [← zw_split]; exact h.reg a p hp
        · rfl
      · cases e
  · rename_i d a o
    cases e
    refine ⟨_, rfl, h.setReg (fun r p hp => ?_) (by simp) (by simp) (by simp) (by simp)⟩
    rw [zw_split, zlane_vpshufd _ _ _ _ _ (div4_lt hp)]
    split
    · rw [dword_shufDwords _ _ (mod4_lt p), sel2_eq, ← zw_lk s a (sel2_lt _ _)]
      exact h.reg a _ (by have := sel2_lt o.toNat (p % 4); omega_arith)
    · rfl
  · rename_i d a b n
    cases e
    refine ⟨_, rfl, h.setReg (fun r p hp => ?_) (by simp) (by simp) (by simp) (by simp)⟩
    rw [zw_split, zlane_vshufi32x4 _ _ _ _ _ _ (div4_lt hp)]
    split
    · rw [shuf4Lanes_eq, sel2_eq]
      have := sel2_lt n.toNat (p / 4)
      by_cases hl : p / 4 < 2
      · simp only [hl, ite_true]
        rw [← zw_lk s a (mod4_lt p)]; exact h.reg a _ (by omega_arith)
      · simp only [hl, ite_false]
        rw [← zw_lk s b (mod4_lt p)]; exact h.reg b _ (by omega_arith)
    · rfl
  · rename_i d m
    obtain ⟨⟨b, i⟩, hs, e⟩ := Option.bind_eq_some_iff.1 e
    dsimp only at e
    by_cases hcl : to = true ∧ b = 2 ∧ clean3 σ i 16 = false
    · rw [ite_eq_left hcl] at e; cases e
    rw [ite_eq_right hcl, Option.some.injEq] at e
    subst e
    obtain ⟨hb, hi, hea⟩ := slot_ok hs
    have ea : s.ea m = (regn D s₀ b).base + BitVec.ofNat 64 (4 * i) := by rw [hea, h.gpr]; rfl
    have hin := hc.rd hb h.rd h.wr hi (by decide)
    refine ⟨s.setZ d ((s.mem.readW ((regn D s₀ b).base + BitVec.ofNat 64 (4 * i)) 512).extractLsb' 0 128)
      ((s.mem.readW ((regn D s₀ b).base + BitVec.ofNat 64 (4 * i)) 512).extractLsb' 128 128)
      ((s.mem.readW ((regn D s₀ b).base + BitVec.ofNat 64 (4 * i)) 512).extractLsb' 256 128)
      ((s.mem.readW ((regn D s₀ b).base + BitVec.ofNat 64 (4 * i)) 512).extractLsb' 384 128),
      by simp only [exec, ea, State.load512, hin, ite_true, Option.map_some],
      h.setReg (fun r p hp => ?_) (by simp) (by simp) (by simp) (by simp)⟩
    rw [zw_split, State.zlane_setZ _ _ _ _ _ _ _ (div4_lt hp)]
    split
    · rw [pick4_ext _ (div4_lt hp), dword_read512 _ _ hp, add_ofNat', ← Nat.mul_add]
      exact h.mem b (i + p) hb (by omega_arith) (Avx512.clean_of hcl hp)
    · rfl
  · rename_i d m
    obtain ⟨⟨b, i⟩, hs, e⟩ := Option.bind_eq_some_iff.1 e
    dsimp only at e
    by_cases hcl : to = true ∧ b = 2 ∧ clean3 σ i 4 = false
    · rw [ite_eq_left hcl] at e; cases e
    rw [ite_eq_right hcl, Option.some.injEq] at e
    subst e
    obtain ⟨hb, hi, hea⟩ := slot_ok hs
    have ea : s.ea m = (regn D s₀ b).base + BitVec.ofNat 64 (4 * i) := by rw [hea, h.gpr]; rfl
    have hin := hc.rd hb h.rd h.wr hi (by decide)
    refine ⟨s.setZ d (s.mem.readW ((regn D s₀ b).base + BitVec.ofNat 64 (4 * i)) 128)
      (s.mem.readW ((regn D s₀ b).base + BitVec.ofNat 64 (4 * i)) 128)
      (s.mem.readW ((regn D s₀ b).base + BitVec.ofNat 64 (4 * i)) 128)
      (s.mem.readW ((regn D s₀ b).base + BitVec.ofNat 64 (4 * i)) 128),
      by simp only [exec, ea, State.load128, hin, ite_true, Option.map_some],
      h.setReg (fun r p hp => ?_) (by simp) (by simp) (by simp) (by simp)⟩
    rw [zw_split, State.zlane_setZ _ _ _ _ _ _ _ (div4_lt hp)]
    split
    · rw [pick4_same _ (div4_lt hp), dword_readW _ _ (mod4_lt p), add_ofNat', ← Nat.mul_add]
      exact h.mem b (i + p % 4) hb (by have := mod4_lt p; omega_arith) (Avx512.clean_of hcl (mod4_lt p))
    · rfl
  · rename_i m r
    cases to
    · simp only [Bool.false_eq_true, ite_false] at e
      obtain ⟨⟨b, i⟩, hs, rfl⟩ := Option.map_eq_some_iff.1 e
      exact store_ok hc h hs
    · simp only [ite_true] at e
      split at e
      · rename_i j hj
        cases e
        exact store3_ok hc h hj
      · obtain ⟨⟨b, i⟩, hs, rfl⟩ := Option.map_eq_some_iff.1 e
        exact storeB_ok hc h hs
  · rename_i d m
    obtain ⟨⟨b, i⟩, hs, e⟩ := Option.bind_eq_some_iff.1 e
    dsimp only at e
    by_cases hcl : to = true ∧ b = 2 ∧ clean3 σ i 1 = false
    · rw [ite_eq_left hcl] at e; cases e
    rw [ite_eq_right hcl, Option.some.injEq] at e
    subst e
    obtain ⟨hb, hi, hea⟩ := slot_ok hs
    have ea : s.ea m = (regn D s₀ b).base + BitVec.ofNat 64 (4 * i) := by rw [hea, h.gpr]; rfl
    have hin := hc.rd hb h.rd h.wr hi (by decide)
    have hv := h.mem b i hb (by omega_arith) (Avx512.clean_of (p := 0) hcl (by decide))
    generalize hvd : s.mem.readW ((regn D s₀ b).base + BitVec.ofNat 64 (4 * i)) 32 = v at hv
    refine ⟨s.setZ d (v ++ v ++ v ++ v) (v ++ v ++ v ++ v) (v ++ v ++ v ++ v) (v ++ v ++ v ++ v), ?_,
      h.setReg (fun r p hp => ?_) (by simp) (by simp) (by simp) (by simp)⟩
    · simp only [exec, ea, State.load32, hin, ite_true, Option.map_some, hvd]
    · rw [zw_split, State.zlane_setZ _ _ _ _ _ _ _ (div4_lt hp)]
      split
      · rw [pick4_same _ (div4_lt hp), dword_rep4 _ (mod4_lt p)]; exact hv
      · rfl
  · rename_i d a m
    obtain ⟨⟨b, i⟩, hs, e⟩ := Option.bind_eq_some_iff.1 e
    dsimp only at e
    by_cases hcl : to = true ∧ b = 2 ∧ clean3 σ i 1 = false
    · rw [ite_eq_left hcl] at e; cases e
    rw [ite_eq_right hcl, Option.some.injEq] at e
    subst e
    obtain ⟨hb, hi, hea⟩ := slot_ok hs
    have ea : s.ea m = (regn D s₀ b).base + BitVec.ofNat 64 (4 * i) := by rw [hea, h.gpr]; rfl
    have hin := hc.rd hb h.rd h.wr hi (by decide)
    have hv := h.mem b i hb (by omega_arith) (Avx512.clean_of (p := 0) hcl (by decide))
    generalize hvd : s.mem.readW ((regn D s₀ b).base + BitVec.ofNat 64 (4 * i)) 32 = v at hv
    refine ⟨s.setZ d (XBinOp.eval .paddd (s.zlane a 0) (v ++ v ++ v ++ v))
      (XBinOp.eval .paddd (s.zlane a 1) (v ++ v ++ v ++ v)) (XBinOp.eval .paddd (s.zlane a 2) (v ++ v ++ v ++ v))
      (XBinOp.eval .paddd (s.zlane a 3) (v ++ v ++ v ++ v)), ?_,
      h.setReg (fun r p hp => ?_) (by simp) (by simp) (by simp) (by simp)⟩
    · simp only [exec, ea, State.load32, hin, ite_true, Option.map_some, ZBcstDOp.sse, hvd]
    · rw [zw_split, State.zlane_setZ _ _ _ _ _ _ _ (div4_lt hp)]
      split
      · rw [pick4_fn (fun l => XBinOp.eval .paddd (s.zlane a l) (v ++ v ++ v ++ v)) (div4_lt hp),
          dword_paddd _ _ (mod4_lt p), dword_rep4 _ (mod4_lt p), T.eval, ← hv, ← zw_split]
        exact congrArg (· + v) (h.reg a p hp)
      · rfl
  · cases e

/-- A block of instructions. -/
theorem srunT_ok {to : Bool} {D : Nat} {s₀ : State} (hc : CtxT to D s₀) :
    ∀ (is : List Instr) {σ σ' : Sym} {s : State}, SRelT to D σ s₀ s → runT to D σ is = some σ' →
      WP isa (.block is) s (SRelT to D σ' s₀)
  | [], _, _, _, h, e => by cases e; exact WP.block_nil h
  | i :: is, _, _, _, h, e => by
    simp only [runT, Option.bind_eq_some_iff] at e
    obtain ⟨σ₁, e₁, e₂⟩ := e
    obtain ⟨s₁, hx, h₁⟩ := sstepT_ok hc h e₁
    exact WP.block_cons_iff.2 ⟨s₁, hx, srunT_ok hc is h₁ e₂⟩

/-- A block of instructions, in place. -/
theorem srun_ok {D : Nat} {s₀ : State} (hc : Ctx D s₀) (is : List Instr) {σ σ' : Sym} {s : State}
    (h : SRel D σ s₀ s) (e : run D σ is = some σ') : WP isa (.block is) s (SRel D σ' s₀) :=
  srunT_ok (to := false) hc is h e

end VG.Proof.ChaCha20.X86_64.Avx512Tail
