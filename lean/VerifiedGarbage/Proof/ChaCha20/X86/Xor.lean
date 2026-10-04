import VerifiedGarbage.Proof.ChaCha20.X86.Block
import VerifiedGarbage.Proof.ChaCha20.X86.Quad
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.ChaCha20.Keystream
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Impl.ChaCha20.X86.Xor
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.ChaCha20.X86.Lit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.ChaCha20.X86.Bytes
import VerifiedGarbage.Proof.ChaCha20.X86.Kernels

/-!
# ChaCha20 keystream XOR on x86 (32-bit)

The invariant before each group of four blocks (`OInv`) holds before the
loop over four blocks (`body4_ok`, with the setup, rounds and output of
`Quad.lean`), which ends with the data done or at most 64 bytes left; those
are the block function's output XORed into the data (`tail_ok`). The call
runs in a frame holding its two arguments (`WP.frame`), and the block
function's own `Verified` proof gives its effect (`WP.call`); the frame and
the return address are in the 12 bytes of stack below `esp` that the
contract reserves.

Constant time is the taint analysis's, which follows the frames and the
calls into the block function. `xor_eax` states that `eax` holds `buf` on
return.
-/

namespace VG.Proof.ChaCha20

open Spec.ChaCha20 VG.X86

/-- X86 (32-bit) contract for `vg_chacha20_xor(state: *mut [u32; 16], data: *mut
u8, len: usize, buf: *mut [u32; 80])`, whose arguments are on the stack (cdecl):
XORs the first `len` bytes of the keystream of the state at `state` into the
`len` bytes at `data`.

The code may read and write the arguments (16 bytes above the return
address), `state` (64 bytes; its contents on exit are unspecified), `data`
(`len` bytes) and `buf` (320 bytes of working space). These may not overlap
each other; the buffers may not overlap the return address or the 12 bytes
of stack below it, where the calls of the block function store their
arguments and return address; nothing may wrap around the end of the
(32-bit) address space. `esp` and the arguments (the pointers and the length)
are public; the state and the data are secret. -/
def xorX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 64⟩
    let data : Region := ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩
    let buf : Region := ⟨(arg s 3).setWidth 64, 320⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 12, 12⟩
    s.rd = [] ∧ s.wr = [state, data, buf, args] ∧
    state.Disjoint data ∧ state.Disjoint buf ∧ data.Disjoint buf ∧
    args.Disjoint state ∧ args.Disjoint data ∧ args.Disjoint buf ∧
    ret.Disjoint state ∧ ret.Disjoint data ∧ ret.Disjoint buf ∧
    stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint buf ∧
    (arg s 0).toNat + 64 ≤ 2 ^ 32 ∧ (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32 ∧
    (arg s 3).toNat + 320 ≤ 2 ^ 32 ∧ 12 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  post s s' :=
    bytesAt s'.mem ((arg s 1).setWidth 64) (arg s 2).toNat =
      List.zipWith (· ^^^ ·) (bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat)
        (keystream (stateAt s.mem ((arg s 0).setWidth 64)) (arg s 2).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, arg s₁ i = arg s₂ i

end VG.Proof.ChaCha20

namespace VG.Proof.ChaCha20.X86.Xor

open VG VG.X86 VG.Impl.ChaCha20.X86.Xor
open VG.Impl.ChaCha20.X86 (at_)
open VG.Proof.ChaCha20.X86 (contains_off contains_sub toNat_ofNat_lt readW_writeW_off block_correct)
open VG.Proof.ChaCha20.X86.Bytes (toNat_ofNat_lt32 ptr_add BPre BPost WPre xorBytes_ok xorWide_ok and_m16
  and_15 setWidth_add ofNat32_add_toNat)
open VG.Spec.ChaCha20 (stateAt keystream serialize bytesAt)

/-! ## The entry state -/

section
variable (s₀ : State)
abbrev E : BitVec 32 := s₀.gpr .esp
abbrev ST : BitVec 32 := arg s₀ 0
abbrev DP : BitVec 32 := arg s₀ 1
abbrev LN : BitVec 32 := arg s₀ 2
abbrev BP : BitVec 32 := arg s₀ 3
abbrev L : Nat := (LN s₀).toNat
abbrev st : Addr := (ST s₀).setWidth 64
abbrev dp : Addr := (DP s₀).setWidth 64
abbrev bp : Addr := (BP s₀).setWidth 64
abbrev stR : Region := ⟨st s₀, 64⟩
abbrev dR : Region := ⟨dp s₀, L s₀⟩
abbrev bR : Region := ⟨bp s₀, 320⟩
abbrev aR : Region := ⟨argAddr s₀ 0, 16⟩
abbrev retR : Region := ⟨(E s₀).setWidth 64, 4⟩
abbrev stackR : Region := ⟨(E s₀).setWidth 64 - 12, 12⟩
/-- The state, the data and the keystream on entry. -/
abbrev S0 : CState := stateAt s₀.mem (st s₀)
abbrev D0 (k : Nat) : Byte := s₀.mem (dp s₀ + BitVec.ofNat 64 k)
abbrev KS : List Byte := keystream (S0 s₀) (L s₀)
/-- The bytes of data done before block `j`. -/
abbrev P (j : Nat) : Nat := min (64 * j) (L s₀)
/-- How many bytes of block `j` are used. -/
abbrev C (j : Nat) : Nat := min 64 (L s₀ - P s₀ j)
end

theorem L_lt (s₀ : State) : L s₀ < 2 ^ 32 := (LN s₀).isLt

structure XPre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR s₀, dR s₀, bR s₀, aR s₀]
  st_d : (stR s₀).Disjoint (dR s₀)
  st_b : (stR s₀).Disjoint (bR s₀)
  d_b : (dR s₀).Disjoint (bR s₀)
  a_st : (aR s₀).Disjoint (stR s₀)
  a_d : (aR s₀).Disjoint (dR s₀)
  a_b : (aR s₀).Disjoint (bR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_d : (retR s₀).Disjoint (dR s₀)
  ret_b : (retR s₀).Disjoint (bR s₀)
  stk_st : (stackR s₀).Disjoint (stR s₀)
  stk_d : (stackR s₀).Disjoint (dR s₀)
  stk_b : (stackR s₀).Disjoint (bR s₀)
  st_fit : (ST s₀).toNat + 64 ≤ 2 ^ 32
  d_fit : (DP s₀).toNat + L s₀ ≤ 2 ^ 32
  b_fit : (BP s₀).toNat + 320 ≤ 2 ^ 32
  sp_lo : 12 ≤ (E s₀).toNat
  sp_hi : (E s₀).toNat + 20 ≤ 2 ^ 32

theorem XPre.of (s₀ : State) (h : Proof.ChaCha20.xorX86.pre s₀) : XPre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩

/-- Our caller's `ebx, esi, edi, ebp`, saved in `buf[256, 272)`. -/
abbrev Saved (s₀ : State) (m : Mem) : Prop := Spill.Saved m (bp s₀ + BitVec.ofNat 64 ·) s₀.gpr saved

theorem saved_fits : Spill.Fits 272 saved := by decide

/-- The regions the code writes: its buffers and the 12 bytes of stack of its calls. -/
abbrev frameR (s₀ : State) : List Region := [stR s₀, dR s₀, bR s₀, stackR s₀]

/-- Before block `j` (the loop's invariant); the counter (word 12 of the
state) is block `j`'s while there are bytes left. -/
structure OInv (s₀ : State) (j : Nat) (s : State) : Prop where
  ebx : s.gpr .ebx = ST s₀
  esi : s.gpr .esi = DP s₀ + BitVec.ofNat 32 (P s₀ j)
  edi : s.gpr .edi = BP s₀
  ebp : s.gpr .ebp = BitVec.ofNat 32 (L s₀ - P s₀ j)
  esp : s.gpr .esp = E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  cnt : P s₀ j < L s₀ → stateAt s.mem (st s₀) = ctr (S0 s₀) j
  data : ∀ k < L s₀, s.mem (dp s₀ + BitVec.ofNat 64 k) =
    if k < P s₀ j then D0 s₀ k ^^^ (KS s₀).getD k 0 else D0 s₀ k
  saved : Saved s₀ s.mem
  frame : Frame (frameR s₀) s₀.mem s.mem

/-! ## Memory -/

namespace XPre
variable {s₀ : State} (hp : XPre s₀)
include hp

theorem w_b : bR s₀ ∈ s₀.wr := by simp [hp.wr]

theorem eaS {d : Nat} (hd : d < 64) : addr (ST s₀) d = st s₀ + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.st_fit; omega)

theorem eaB {d : Nat} (hd : d < 320) : addr (BP s₀) d = bp s₀ + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.b_fit; omega)

theorem eaE {d : Nat} (hd : d < 20) : addr (E s₀) d = (E s₀).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.sp_hi; omega)

theorem out_b {d n : Nat} (h : d + n ≤ 320) : InRegions s₀.wr (bp s₀ + BitVec.ofNat 64 d) n :=
  ⟨bR s₀, hp.w_b, contains_off h (by lit_omega)⟩

theorem arg_contains {i : Nat} (hi : i < 4) : (aR s₀).Contains (argAddr s₀ i) 4 := by
  simp only [aR]
  rw [show argAddr s₀ i = addr (E s₀) (4 + 4 * i) from rfl, hp.eaE (by lit_omega),
    show argAddr s₀ 0 = addr (E s₀) 4 from rfl, hp.eaE (by lit_omega)]
  exact contains_sub _ (by lit_omega) (by lit_omega) (by lit_omega)

theorem in_arg {i : Nat} (hi : i < 4) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 :=
  ⟨aR s₀, by simp [hp.wr], hp.arg_contains hi⟩

end XPre

theorem contains_ofNat {b : Addr} {len d n : Nat} (h : d + n ≤ len) (hd : d < 2 ^ 64) :
    (⟨b, len⟩ : Region).Contains (b + BitVec.ofNat 64 d) n := contains_off h hd

/-- A state in memory outside a frame is unchanged. -/
theorem stateAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 64⟩ : Region).Disjoint r) : stateAt m' p = stateAt m p := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn]
  exact hf.readW (contains_ofNat (by lit_omega) (by lit_omega)) hd (by decide)

/-- `buf[256, 272)`, where our caller's registers are saved. -/
abbrev savR (s₀ : State) : Region := ⟨bp s₀ + BitVec.ofNat 64 256, 16⟩

theorem savR_sub (s₀ : State) : Region.Sub (savR s₀) (bR s₀) := Offset.sub_base _ (by lit_omega)

/-- The saved registers survive a frame that does not touch them. -/
theorem Saved.frame {s₀ : State} {rs : List Region} {m m' : Mem} (h : Saved s₀ m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (savR s₀).Disjoint r) : Saved s₀ m' :=
  Spill.Saved.of_frame h hf (fun p hp => by
    have := saved_fits.1 p hp
    have : 256 ≤ p.2 := by revert p hp; decide
    exact Offset.contains _ this (by lit_omega) (by lit_omega)) hd

/-! ## The prologue -/

theorem load_buf_ok {s₀ : State} (hp : XPre s₀) :
    WP isa (.block [.mov .eax (.mem (at_ .esp 16))]) s₀ fun s => s = s₀.setReg .eax (BP s₀) := by
  have i₃ : InRegions (s₀.rd ++ s₀.wr) ((s₀.gpr .esp + BitVec.ofNat 32 16).setWidth 64) 4 :=
    hp.in_arg (i := 3) (by lit_omega)
  have v₃ : s₀.mem.readW ((s₀.gpr .esp + BitVec.ofNat 32 16).setWidth 64) 32 = BP s₀ := rfl
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.ea, at_, State.load32,
    i₃, v₃, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']

/-- The memory after the prologue's stores. -/
abbrev saveMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (bp s₀ + BitVec.ofNat 64 ·) s₀.gpr saved

theorem saveMem_frame {s₀ : State} (hp : XPre s₀) : Frame [bR s₀] s₀.mem (saveMem s₀) :=
  have _ := hp
  Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p h =>
    have := saved_fits.1 p h; contains_off (by lit_omega) (by lit_omega)

theorem saveMem_saved (s₀ : State) : Saved s₀ (saveMem s₀) :=
  Spill.saveMem_saved_ofNat _ _ _ saved_fits (by decide)

theorem saveMem_arg {s₀ : State} (hp : XPre s₀) {i : Nat} (hi : i < 4) :
    (saveMem s₀).readW (argAddr s₀ i) 32 = arg s₀ i :=
  (saveMem_frame hp).readW (hp.arg_contains hi) (by simpa using hp.a_b) (by decide)

theorem save_ok {s₀ : State} (hp : XPre s₀) :
    WP isa (.block save) (s₀.setReg .eax (BP s₀)) fun s₁ =>
      s₁.gpr = (s₀.setReg .eax (BP s₀)).gpr ∧ s₁.mem = saveMem s₀ ∧ s₁.rd = s₀.rd ∧
        s₁.wr = s₀.wr := by
  have e : ∀ p ∈ saved, addr (BP s₀) p.2 = bp s₀ + BitVec.ofNat 64 p.2 :=
    fun p h => hp.eaB (by have := saved_fits.1 p h; lit_omega)
  have geax : (s₀.setReg .eax (BP s₀)).gpr .eax = BP s₀ := RegUpd.gpr_setReg_self _ _ _
  rw [show save = Spill.saveCode .eax saved ++ [] from rfl]
  refine Spill.save_ok saved (fun p h => by
      rw [geax, e p h]; exact hp.out_b (by have := saved_fits.1 p h; lit_omega))
    fun s₁ u => WP.block_nil ⟨u.gpr, ?_, u.rd, u.wr⟩
  rw [u.mem, geax]
  exact Spill.saveMem_congr _ _ e fun p h => RegUpd.gpr_setReg_of_ne _ _ (by revert p h; decide)

set_option simprocs false in
theorem load_ok {s₀ : State} (hp : XPre s₀) {s₁ : State}
    (hg : s₁.gpr = (s₀.setReg .eax (BP s₀)).gpr) (hm : s₁.mem = saveMem s₀) (hr : s₁.rd = s₀.rd)
    (hw : s₁.wr = s₀.wr) :
    WP isa (.block [.mov .edi (.reg .eax), .mov .ebx (.mem (at_ .esp 4)),
      .mov .esi (.mem (at_ .esp 8)), .mov .ebp (.mem (at_ .esp 12))]) s₁ (OInv s₀ 0) := by
  have i₀ : InRegions (s₁.rd ++ s₁.wr) ((s₀.gpr .esp + BitVec.ofNat 32 4).setWidth 64) 4 :=
    hr ▸ hw ▸ hp.in_arg (i := 0) (by lit_omega)
  have i₁ : InRegions (s₁.rd ++ s₁.wr) ((s₀.gpr .esp + BitVec.ofNat 32 8).setWidth 64) 4 :=
    hr ▸ hw ▸ hp.in_arg (i := 1) (by lit_omega)
  have i₂ : InRegions (s₁.rd ++ s₁.wr) ((s₀.gpr .esp + BitVec.ofNat 32 12).setWidth 64) 4 :=
    hr ▸ hw ▸ hp.in_arg (i := 2) (by lit_omega)
  have v₀ : (saveMem s₀).readW ((s₀.gpr .esp + BitVec.ofNat 32 4).setWidth 64) 32 = ST s₀ :=
    saveMem_arg hp (i := 0) (by lit_omega)
  have v₁ : (saveMem s₀).readW ((s₀.gpr .esp + BitVec.ofNat 32 8).setWidth 64) 32 = DP s₀ :=
    saveMem_arg hp (i := 1) (by lit_omega)
  have v₂ : (saveMem s₀).readW ((s₀.gpr .esp + BitVec.ofNat 32 12).setWidth 64) 32 = LN s₀ :=
    saveMem_arg hp (i := 2) (by lit_omega)
  have gesp : s₁.gpr .esp = s₀.gpr .esp := by rw [hg]; rfl
  have geax : s₁.gpr .eax = BP s₀ := by rw [hg]; rfl
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.ea, at_, State.load32, State.setReg, gesp, geax, hm,
    i₀, i₁, i₂, v₀, v₁, v₂, ite_true, ite_false, Option.map_some,
    Option.some.injEq, exists_eq_left']
  have hf := saveMem_frame hp
  refine ⟨by simp (config := {decide := true}), by simp (config := {decide := true}) [P],
    by simp (config := {decide := true}), by simp (config := {decide := true}) [P],
    by simp (config := {decide := true}) [hg, State.setReg], hr, hw, ?_, fun k hk => ?_,
    saveMem_saved s₀, hf.mono (by simp)⟩
  · intro _; rw [stateAt_frame hf (by simpa using hp.st_b), ctr_zero]
  · simp only [P, Nat.mul_zero, Nat.zero_min, Nat.not_lt_zero, ite_false]
    exact hf.bytes (R := dR s₀) (by simpa using hp.d_b) (show L s₀ ≤ 2 ^ 64 by have := L_lt s₀; omega) hk

theorem prologue_ok {s₀ : State} (hp : XPre s₀) :
    WP isa (.block prologue) (s₀.setReg .eax (BP s₀)) (OInv s₀ 0) := by
  rw [show prologue = save ++ [.mov .edi (.reg .eax), .mov .ebx (.mem (at_ .esp 4)),
      .mov .esi (.mem (at_ .esp 8)), .mov .ebp (.mem (at_ .esp 12))]
    from rfl, WP.block_append_iff]
  exact WP.mono (save_ok hp) fun s₁ ⟨hg, hm, hr, hw⟩ => load_ok hp hg hm hr hw

/-! ## Calling the block function -/

/-- `esp` as a 64-bit address. -/
abbrev Es (s₀ : State) : Addr := (E s₀).setWidth 64

theorem setWidth_sub {x : BitVec 32} {d : Nat} (h : d ≤ x.toNat) :
    (x - BitVec.ofNat 32 d).setWidth 64 = x.setWidth 64 - BitVec.ofNat 64 d := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := d) (by lit_omega), Nat.mod_eq_of_lt (a := x.toNat) (by lit_omega),
    Nat.mod_eq_of_lt (a := d) (by lit_omega)]
  omega

/-- The 8 bytes of the frame holding the block function's arguments. -/
abbrev fR (s₀ : State) : Region := ⟨Es s₀ - 8, 8⟩
/-- The block function's return address. -/
abbrev cR (s₀ : State) : Region := ⟨Es s₀ - 12, 4⟩
/-- The first 256 bytes of `buf`, which the block function may write. -/
abbrev b256 (s₀ : State) : Region := ⟨bp s₀, 256⟩

theorem fR_sub (s₀ : State) : Region.Sub (fR s₀) (stackR s₀) := Offset.sub_below _ (by decide) (by decide)

theorem cR_sub (s₀ : State) : Region.Sub (cR s₀) (stackR s₀) := Offset.sub_below _ (by decide) (by decide)

theorem b256_sub (s₀ : State) : Region.Sub (b256 s₀) (bR s₀) := Region.sub_prefix (by lit_omega)

theorem savR_b256 (s₀ : State) : (savR s₀).Disjoint (b256 s₀) := Offset.disjoint_base _ (by lit_omega) (by lit_omega)

/-- The permissions the block function is called with. -/
abbrev rdC (s₀ : State) : List Region := [stR s₀, fR s₀]
abbrev wrC (s₀ : State) : List Region := [b256 s₀]

/-- The state the block function is entered in, from `s`. -/
abbrev entry (s : State) : State := (pushed [.edi, .ebx] s).callEntry

theorem entry_esp (s : State) :
    (entry s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 8 - 4 := by
  simp only [entry, State.callEntry_esp, pushed_esp]; rfl

theorem entry_mem (s : State) :
    (entry s).mem = ((s.mem.writeW ((s.gpr .esp - 4).setWidth 64) (s.gpr .edi)).writeW
      ((s.gpr .esp - 4 - 4).setWidth 64) (s.gpr .ebx)).writeW
      ((s.gpr .esp - BitVec.ofNat 32 8 - 4).setWidth 64) (s.unknowns 0) := by
  simp only [entry, State.callEntry_mem, pushed_esp]
  simp [pushed, pushRegs, State.setReg]

/-- The words at `esp - 4`, `esp - 8` and `esp - 12` lie in the 12 bytes below `esp`. -/
theorem stack_contains (e : Addr) :
    (⟨e - 12, 12⟩ : Region).Contains (e - 4) (32 / 8) ∧ (⟨e - 12, 12⟩ : Region).Contains (e - 8) (32 / 8) ∧
      (⟨e - 12, 12⟩ : Region).Contains (e - 12) (32 / 8) :=
  ⟨Offset.contains_below e (by decide) (by decide) (by decide),
    Offset.contains_below e (by decide) (by decide) (by decide),
    Offset.contains_below e (by decide) (by decide) (by decide)⟩

/-- The words at `esp - 4`, `esp - 8` and `esp - 12` do not overlap. -/
theorem stack_seps (e : Addr) :
    Mem.Sep (e - 8) (32 / 8) (e - 12) (32 / 8) ∧ Mem.Sep (e - 4) (32 / 8) (e - 12) (32 / 8) ∧
      Mem.Sep (e - 4) (32 / 8) (e - 8) (32 / 8) :=
  ⟨Offset.sep_below e 12 (by decide) (by decide) (by decide) (by decide) (by decide),
    Offset.sep_below e 12 (by decide) (by decide) (by decide) (by decide) (by decide),
    Offset.sep_below e 12 (by decide) (by decide) (by decide) (by decide) (by decide)⟩

section
variable {s₀ : State} (hp : XPre s₀) {s : State} (hE : s.gpr .esp = E s₀)
include hp hE

theorem entry_addrs :
    ((s.gpr .esp - 4).setWidth 64 = Es s₀ - 4) ∧ ((s.gpr .esp - 4 - 4).setWidth 64 = Es s₀ - 8) ∧
    ((s.gpr .esp - BitVec.ofNat 32 8 - 4).setWidth 64 = Es s₀ - 12) := by
  have hlo := hp.sp_lo
  rw [hE]
  refine ⟨setWidth_sub (d := 4) (by lit_omega), ?_, ?_⟩
  · rw [show E s₀ - 4 - 4 = E s₀ - BitVec.ofNat 32 8 by rw [BitVec.sub_sub]; rfl, setWidth_sub (by lit_omega)]; rfl
  · rw [show E s₀ - BitVec.ofNat 32 8 - 4 = E s₀ - BitVec.ofNat 32 12 by rw [BitVec.sub_sub]; rfl,
      setWidth_sub (by lit_omega)]; rfl

theorem entry_frame : Frame [stackR s₀] s.mem (entry s).mem := by
  obtain ⟨a₁, a₂, a₃⟩ := entry_addrs hp hE
  obtain ⟨c4, c8, c12⟩ := stack_contains (Es s₀)
  rw [entry_mem, a₁, a₂, a₃]
  exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c4).writeW
    (List.mem_singleton_self _) _ c8).writeW (List.mem_singleton_self _) _ c12

theorem entry_argAddr0 : argAddr (entry s) 0 = Es s₀ - 8 := by
  have hlo := hp.sp_lo
  simp only [argAddr, entry_esp, hE]
  rw [show E s₀ - BitVec.ofNat 32 8 - 4 + BitVec.ofNat 32 (4 + 4 * 0) = E s₀ - BitVec.ofNat 32 8 by
    rw [BitVec.sub_sub, Offset.sub_ofNat_eq (E s₀) (show 8 ≤ 12 by decide)]; rfl, setWidth_sub (by lit_omega)]; rfl

theorem entry_argAddr1 : argAddr (entry s) 1 = Es s₀ - 4 := by
  have hlo := hp.sp_lo
  simp only [argAddr, entry_esp, hE]
  rw [show E s₀ - BitVec.ofNat 32 8 - 4 + BitVec.ofNat 32 (4 + 4 * 1) = E s₀ - BitVec.ofNat 32 4 by
    rw [BitVec.sub_sub, Offset.sub_ofNat_eq (E s₀) (show 4 ≤ 12 by decide)]; rfl, setWidth_sub (by lit_omega)]; rfl

theorem entry_arg0 (hb : s.gpr .ebx = ST s₀) : arg (entry s) 0 = ST s₀ := by
  obtain ⟨a₁, a₂, a₃⟩ := entry_addrs hp hE
  show (entry s).mem.readW (argAddr (entry s) 0) 32 = ST s₀
  rw [entry_argAddr0 hp hE, entry_mem, a₁, a₂, a₃,
    Mem.readW_writeW_sep (stack_seps _).1 (by decide), Mem.readW_writeW_self32, hb]

theorem entry_arg1 (hd : s.gpr .edi = BP s₀) : arg (entry s) 1 = BP s₀ := by
  obtain ⟨a₁, a₂, a₃⟩ := entry_addrs hp hE
  show (entry s).mem.readW (argAddr (entry s) 1) 32 = BP s₀
  rw [entry_argAddr1 hp hE, entry_mem, a₁, a₂, a₃,
    Mem.readW_writeW_sep (stack_seps _).2.1 (by decide),
    Mem.readW_writeW_sep (stack_seps _).2.2 (by decide), Mem.readW_writeW_self32, hd]

theorem entry_esp64 : ((entry s).gpr .esp).setWidth 64 = Es s₀ - 12 := by
  rw [entry_esp]; exact (entry_addrs hp hE).2.2

theorem entry_esp_fit : ((entry s).gpr .esp).toNat + 12 ≤ 2 ^ 32 := by
  have hlo := hp.sp_lo
  rw [entry_esp, hE, show E s₀ - BitVec.ofNat 32 8 - 4 = E s₀ - BitVec.ofNat 32 12 by
    rw [BitVec.sub_sub]; rfl,
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def, toNat_ofNat_lt32 (by lit_omega)]; omega),
    toNat_ofNat_lt32 (by lit_omega)]
  have := (E s₀).isLt
  omega

end

/-- The block function's precondition, from the facts about its entry state. -/
theorem pre_block_of {s₀ s' : State} (hp : XPre s₀) (h₀ : arg s' 0 = ST s₀) (h₁ : arg s' 1 = BP s₀)
    (ha : argAddr s' 0 = Es s₀ - 8) (hr : (s'.gpr .esp).setWidth 64 = Es s₀ - 12)
    (ht : (s'.gpr .esp).toNat + 12 ≤ 2 ^ 32) (hrd : s'.rd = rdC s₀) (hwr : s'.wr = wrC s₀) :
    Proof.ChaCha20.blockX86.pre s' := by
  show s'.rd = [⟨(arg s' 0).setWidth 64, 64⟩, ⟨argAddr s' 0, 8⟩] ∧
    s'.wr = [⟨(arg s' 1).setWidth 64, 256⟩] ∧
    Region.Disjoint ⟨(arg s' 1).setWidth 64, 256⟩ ⟨(arg s' 0).setWidth 64, 64⟩ ∧
    Region.Disjoint ⟨argAddr s' 0, 8⟩ ⟨(arg s' 1).setWidth 64, 256⟩ ∧
    Region.Disjoint ⟨(s'.gpr .esp).setWidth 64, 4⟩ ⟨(arg s' 1).setWidth 64, 256⟩ ∧
    (arg s' 0).toNat + 64 ≤ 2 ^ 32 ∧ (arg s' 1).toNat + 256 ≤ 2 ^ 32 ∧
    (s'.gpr .esp).toNat + 12 ≤ 2 ^ 32
  rw [h₀, h₁, ha, hr]
  exact ⟨hrd, hwr, (hp.st_b.sub_right (b256_sub s₀)).symm,
    (hp.stk_b.sub_left (fR_sub s₀)).sub_right (b256_sub s₀),
    (hp.stk_b.sub_left (cR_sub s₀)).sub_right (b256_sub s₀), hp.st_fit,
    by have := hp.b_fit; omega, ht⟩

/-- The block function's precondition holds when it is called. -/
theorem entry_pre {s₀ : State} (hp : XPre s₀) {s : State} (hE : s.gpr .esp = E s₀)
    (hb : s.gpr .ebx = ST s₀) (hd : s.gpr .edi = BP s₀) :
    Proof.ChaCha20.blockX86.pre ((entry s).withRegions (rdC s₀) (wrC s₀)) :=
  pre_block_of (s' := (entry s).withRegions (rdC s₀) (wrC s₀)) hp (entry_arg0 (s := s) hp hE hb)
    (entry_arg1 (s := s) hp hE hd) (entry_argAddr0 (s := s) hp hE) (entry_esp64 (s := s) hp hE)
    (entry_esp_fit (s := s) hp hE) rfl rfl

/-- After the block function: `buf` holds block `j`'s keystream. -/
structure AInv (s₀ : State) (j : Nat) (s : State) : Prop extends OInv s₀ j s where
  ks : ∀ t < 64, s.mem (bp s₀ + BitVec.ofNat 64 t) =
    (serialize (Spec.ChaCha20.block (ctr (S0 s₀) j))).getD t 0

theorem pushed_wr_eq {s₀ : State} (hp : XPre s₀) {s : State} (hE : s.gpr .esp = E s₀) :
    (pushed [.edi, .ebx] s).wr = fR s₀ :: s.wr := by
  have hlo := hp.sp_lo
  rw [pushed_wr, hE]
  show below (E s₀) 8 :: s.wr = _
  simp only [below]
  rw [setWidth_sub (by lit_omega)]; rfl

theorem call_covers {s₀ : State} (hp : XPre s₀) {s : State} (hE : s.gpr .esp = E s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    Covers (rdC s₀ ++ wrC s₀) ((pushed [.edi, .ebx] s).rd ++ (pushed [.edi, .ebx] s).wr) ∧
      Covers (wrC s₀) (pushed [.edi, .ebx] s).wr := by
  rw [pushed_rd, pushed_wr_eq hp hE, hrd, hwr, hp.rd, hp.wr]
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀, by simp, 0, by simp, show 0 + 64 ≤ 64 by omega⟩
    · exact ⟨fR s₀, by simp, 0, by simp, show 0 + 8 ≤ 8 by omega⟩
    · exact ⟨bR s₀, by simp, 0, by simp, show 0 + 256 ≤ 320 by omega⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨bR s₀, by simp, 0, by simp, show 0 + 256 ≤ 320 by omega⟩

/-! ### The frame's pop -/

theorem popped_esp (r : Reg) (k : Nat) (s : State) :
    (popped r k s).gpr .esp = s.gpr .esp + BitVec.ofNat 32 (4 * k) := (popReg_eq s r k).2.2.1

theorem popped_gpr (r : Reg) (k : Nat) (s : State) {q : Reg} (h₁ : q ≠ .esp) (h₂ : q ≠ r) :
    (popped r k s).gpr q = s.gpr q := (popReg_eq s r k).2.2.2 q h₁ h₂

theorem popped_rd (r : Reg) (k : Nat) (s : State) : (popped r k s).rd = s.rd := (popReg_eq s r k).1

theorem popped_wr (r : Reg) (k : Nat) (s : State) : (popped r k s).wr = s.wr.tail := rfl

theorem popped_mem (r : Reg) (k : Nat) (s : State) : (popped r k s).mem = s.mem :=
  (popReg_rest s r k).1

/-! ### The call -/

theorem block_nosp : NoSp Impl.ChaCha20.X86.block := by
  have : ((instrs Impl.ChaCha20.X86.block).all fun i => !Taint.clobbers i .esp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  intro i hi
  simpa using List.all_eq_true.mp this i hi

theorem block_stackUse : stackUse Impl.ChaCha20.X86.block = 0 := by lit_decide

theorem stackR_eq {s₀ : State} (hp : XPre s₀) : stackR s₀ = below (E s₀) 12 := by
  simp only [stackR, below]
  rw [setWidth_sub hp.sp_lo]
  rfl

theorem call_ok {s₀ : State} (hp : XPre s₀) {j : Nat} (hj : P s₀ j < L s₀) {s : State} (h : OInv s₀ j s) :
    WP isa callBlock s (AInv s₀ j) := by
  have hlo := hp.sp_lo
  obtain ⟨hc, hw⟩ := call_covers hp h.esp h.rd h.wr
  have hn : 4 * [Reg.edi, .ebx].length ≤ (s.gpr .esp).toNat := by
    rw [h.esp]; simp only [List.length_cons, List.length_nil]; omega
  have hd : stackUse Impl.ChaCha20.X86.block + 4 ≤ ((pushed [.edi, .ebx] s).gpr .esp).toNat := by
    rw [block_stackUse, pushed_esp, sub_toNat hn, h.esp]
    simp only [List.length_cons, List.length_nil]; omega
  refine WP.frame (rs := [.edi, .ebx]) (r := .eax) (by simp) (by decide) (by decide) hn block_nosp ?_
  refine WP.call (k := Proof.ChaCha20.blockX86) block_correct block_nosp hd (rd := rdC s₀)
    (wr := wrC s₀) (entry_pre hp h.esp h.ebx h.edi) hc hw
    fun s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩ => ?_
  have hsp : s'.gpr .esp = (pushed [.edi, .ebx] s).gpr .esp := hcs .esp (by simp [calleeSaved])
  -- The frame, the return address and the block function's writes.
  have hF : Frame [b256 s₀, stackR s₀] s.mem s'.mem := by
    rw [stackR_eq hp]
    refine (Frame.sub (pushed_frame (by decide) hn) fun r hr => ?_).trans (Frame.sub hf fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨below (E s₀) 12, by simp, by rw [h.esp]; exact below_sub (by decide) hlo⟩
    · simp only [wrC, block_stackUse, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨b256 s₀, by simp, fun _ h => h⟩
      · refine ⟨below (E s₀) 12, by simp, ?_⟩
        rw [pushed_esp, h.esp]
        exact below_inner (by decide) hlo
  have hd : ∀ R : Region, R.Disjoint (b256 s₀) → R.Disjoint (stackR s₀) →
      ∀ r ∈ [b256 s₀, stackR s₀], R.Disjoint r := by
    intro R h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> with_reducible assumption
  have hst : stateAt s'.mem (st s₀) = stateAt s.mem (st s₀) :=
    stateAt_frame hF (hd _ (hp.st_b.sub_right (b256_sub s₀)) hp.stk_st.symm)
  have g : ∀ r ∈ calleeSaved, r ≠ .esp → r ≠ .eax → (popped .eax [Reg.edi, .ebx].length s').gpr r = s.gpr r := by
    intro r hr h₁ h₂
    rw [popped_gpr _ _ _ h₁ h₂, hcs r hr, pushed_gpr _ _ h₁]
  have e0 : arg ((entry s).withRegions (rdC s₀) (wrC s₀)) 0 = ST s₀ := entry_arg0 (s := s) hp h.esp h.ebx
  have e1 : arg ((entry s).withRegions (rdC s₀) (wrC s₀)) 1 = BP s₀ := entry_arg1 (s := s) hp h.esp h.edi
  have hpost' : stateAt s'.mem (bp s₀) = Spec.ChaCha20.block (ctr (S0 s₀) j) := by
    have := (show stateAt s₂.mem ((arg ((entry s).withRegions (rdC s₀) (wrC s₀)) 1).setWidth 64) =
      Spec.ChaCha20.block (stateAt ((entry s).withRegions (rdC s₀) (wrC s₀)).mem
        ((arg ((entry s).withRegions (rdC s₀) (wrC s₀)) 0).setWidth 64)) from hpost)
    rw [e0, e1, hm₂, State.withRegions_mem,
      stateAt_frame (entry_frame hp h.esp) (by simpa using hp.stk_st.symm), h.cnt hj] at this
    exact this
  refine ⟨⟨by rw [g .ebx (by simp [calleeSaved]) (by decide) (by decide), h.ebx],
    by rw [g .esi (by simp [calleeSaved]) (by decide) (by decide), h.esi],
    by rw [g .edi (by simp [calleeSaved]) (by decide) (by decide), h.edi],
    by rw [g .ebp (by simp [calleeSaved]) (by decide) (by decide), h.ebp],
    ?_, by rw [popped_rd, hrd, pushed_rd, h.rd],
    by rw [popped_wr, hwr, pushed_wr_eq hp h.esp, List.tail_cons, h.wr],
    fun _ => by rw [popped_mem, hst, h.cnt hj], fun k hk => ?_, ?_, ?_⟩, fun t ht => ?_⟩
  · rw [popped_esp, hsp, pushed_esp, h.esp]
    simp only [List.length_cons, List.length_nil]
    exact BitVec.sub_add_cancel _ _
  · rw [popped_mem, hF.bytes (R := dR s₀) (hd _ (hp.d_b.sub_right (b256_sub s₀)) hp.stk_d.symm)
      (show L s₀ ≤ 2 ^ 64 by have := L_lt s₀; omega) hk]
    exact h.data k hk
  · rw [popped_mem]
    exact h.saved.frame hF (hd _ (savR_b256 s₀) (hp.stk_b.symm.sub_left (savR_sub s₀)))
  · rw [popped_mem]
    exact h.frame.trans (hF.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨bR s₀, by simp, b256_sub s₀⟩
      · exact ⟨stackR s₀, by simp, fun _ h => h⟩)
  · rw [popped_mem, ← serialize_stateAt s'.mem (bp s₀) ht, hpost']

theorem P_le (s₀ : State) (j : Nat) : P s₀ j ≤ L s₀ := Nat.min_le_right _ _

/-! ## The end of a block -/

/-- The state after its counter (word 12) is stored. -/
theorem stateAt_writeW_counter (m : Mem) (p : Addr) (v : BitVec 32) :
    stateAt (m.writeW (p + BitVec.ofNat 64 48) v) p = (stateAt m p).set 12 v := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn, Vector.getElem_set]
  by_cases h : 12 = i
  · subst h
    simp only [ite_true]
    exact Mem.readW_writeW_self32 _ _ _
  · simp only [h, ite_false]
    exact readW_writeW_off m p v (by lit_omega) (by lit_omega) (by lit_omega)

/-! ## Four blocks at once -/

section Quad
open Quad (dW slotsR ctrR)

theorem ctx_of {s₀ : State} (hp : XPre s₀) {s : State} (hb : s.gpr .ebx = ST s₀)
    (hd : s.gpr .edi = BP s₀) (hw : s.wr = s₀.wr) : Quad.Ctx (st s₀) (bp s₀) s :=
  ⟨fun d h => by show addr (s.gpr .ebx) d = _; rw [hb]; exact hp.eaS h,
   fun d h => by show addr (s.gpr .edi) d = _; rw [hd]; exact hp.eaB h,
   by rw [hw, hp.wr]; simp, by rw [hw, hp.wr]; simp, hp.st_b⟩

theorem ptr_add2 (x : BitVec 32) {k d : Nat} (h : x.toNat + k + d < 2 ^ 32) :
    (x + BitVec.ofNat 32 k + BitVec.ofNat 32 d).setWidth 64 =
      x.setWidth 64 + BitVec.ofNat 64 k + BitVec.ofNat 64 d := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The data of the four blocks after `j`. -/
abbrev win (s₀ : State) (j : Nat) : Addr := dp s₀ + BitVec.ofNat 64 (P s₀ j)

/-- How many bytes of data the four blocks after `j` are for. -/
abbrev Wn (s₀ : State) (j : Nat) : Nat := min (L s₀ - P s₀ j) 256

theorem Wn_le (s₀ : State) (j : Nat) : Wn s₀ j ≤ L s₀ - P s₀ j ∧ Wn s₀ j ≤ 256 :=
  ⟨Nat.min_le_left _ _, Nat.min_le_right _ _⟩

theorem dctx_of {s₀ : State} (hp : XPre s₀) {j : Nat} {s : State}
    (hsi : s.gpr .esi = DP s₀ + BitVec.ofNat 32 (P s₀ j)) (hw : s.wr = s₀.wr) :
    Quad.DCtx (win s₀ j) (Wn s₀ j) s :=
  ⟨fun d h => by
      show addr (s.gpr .esi) d = _
      rw [hsi]; exact ptr_add2 _ (by have := hp.d_fit; have := P_le s₀ j; have := Wn_le s₀ j; omega),
   fun off n h => ⟨dR s₀, by rw [hw, hp.wr]; simp, by
      have := L_lt s₀
      have := P_le s₀ j
      have := Wn_le s₀ j
      rw [Offset.add_add]; exact contains_ofNat (by omega) (by lit_omega)⟩⟩

theorem ctr_ctr (S : CState) (a b : Nat) : ctr (ctr S a) b = ctr S (a + b) := by
  simp only [ctr, Vector.set_set, Vector.getElem_set_self, BitVec.ofNat_add, BitVec.add_assoc]

theorem ctr_add (S : CState) (j n : Nat) :
    (ctr S j).set 12 ((ctr S j)[12] + BitVec.ofNat 32 n) = ctr S (j + n) := by
  rw [← ctr_ctr]; rfl

/-- The regions four blocks write: the slots, the counters and `buf[0, 16)`
in `buf`, the data of the four blocks, and the state (its counter). -/
abbrev qR (s₀ : State) (j : Nat) : List Region :=
  [slotsR (bp s₀), ctrR (bp s₀), dW (win s₀ j) (Wn s₀ j), Quad.stashR (bp s₀), stR s₀]

theorem slots_sub (s₀ : State) : Region.Sub (slotsR (bp s₀)) (bR s₀) := Region.sub_prefix (by decide)
theorem ctrR_sub (s₀ : State) : Region.Sub (ctrR (bp s₀)) (bR s₀) := Offset.sub_base _ (by decide)
theorem stash_sub (s₀ : State) : Region.Sub (Quad.stashR (bp s₀)) (bR s₀) := Region.sub_prefix (by decide)
theorem dW_sub (s₀ : State) (j : Nat) : Region.Sub (dW (win s₀ j) (Wn s₀ j)) (dR s₀) :=
  Offset.sub_base _ (by have := P_le s₀ j; have := Wn_le s₀ j; omega)

theorem qR_frame (s₀ : State) (j : Nat) : ∀ r ∈ qR s₀ j, ∃ r' ∈ frameR s₀, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨bR s₀, by simp, slots_sub s₀⟩
  · exact ⟨bR s₀, by simp, ctrR_sub s₀⟩
  · exact ⟨dR s₀, by simp, dW_sub s₀ j⟩
  · exact ⟨bR s₀, by simp, stash_sub s₀⟩
  · exact ⟨stR s₀, by simp, fun _ h => h⟩

theorem qR_saved {s₀ : State} (hp : XPre s₀) (j : Nat) : ∀ r ∈ qR s₀ j, (savR s₀).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact Offset.disjoint_base _ (by decide) (by decide)
  · exact Offset.disjoint _ (by simp only [ctrOff]; omega) (by decide) (by decide)
  · exact (hp.d_b.symm.sub_left (savR_sub s₀)).sub_right (dW_sub s₀ j)
  · exact Offset.disjoint_base _ (by decide) (by decide)
  · exact (hp.st_b.symm.sub_left (savR_sub s₀))

/-- The keystream of the four blocks after `j`: the rounds' result plus the
input states, the counter being block `j`'s. -/
abbrev B4 (C : CState) : Nat → CState :=
  Quad.blk (fun l => Nat.repeat Spec.ChaCha20.innerBlock 10 (ctr C l)) C

theorem ksb_eq {s₀ : State} {j t : Nat} (hPj : P s₀ j = 64 * j) (ht : P s₀ j + t < L s₀) :
    Quad.ksb (B4 (ctr (S0 s₀) j)) t = (KS s₀).getD (P s₀ j + t) 0 := by
  show (serialize (Spec.ChaCha20.block (ctr (ctr (S0 s₀) j) (t / 64)))).getD (t % 64) 0 = _
  rw [KS, keystream_getD _ ht, ctr_ctr, hPj, show j + t / 64 = (64 * j + t) / 64 by omega,
    show t % 64 = (64 * j + t) % 64 by omega]

/-- What the setup, the rounds and the output leave: the keystream XORed
into the data (but for the bytes past the last multiple of 16, if any, whose
keystream is in `buf[0, 16)`), and everything else as it was but `eax` and
the regions of `qR` (not the state). -/
structure Q4 (s₀ : State) (j : Nat) (s s' : State) : Prop where
  data : ∀ k, k < Wn s₀ j → s'.mem (win s₀ j + BitVec.ofNat 64 k) =
    if Quad.Full (Wn s₀ j) k then
      s.mem (win s₀ j + BitVec.ofNat 64 k) ^^^ Quad.ksb (B4 (stateAt s.mem (st s₀))) k
    else s.mem (win s₀ j + BitVec.ofNat 64 k)
  stash : Quad.Stashed (bp s₀) (B4 (stateAt s.mem (st s₀))) (Wn s₀ j) (fun _ => True) s'.mem
  keep : ∀ r, r ≠ .eax → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [slotsR (bp s₀), ctrR (bp s₀), dW (win s₀ j) (Wn s₀ j), Quad.stashR (bp s₀)] s.mem s'.mem
  st : stateAt s'.mem (st s₀) = stateAt s.mem (st s₀)

theorem kR_sub (s₀ : State) : Region.Sub (Quad.kR (bp s₀)) (bR s₀) := Offset.sub_base _ (by decide)

/-- What the four blocks write is outside `buf[288, 320)`. -/
theorem kR_qR {s₀ : State} (hp : XPre s₀) (j : Nat) : ∀ r ∈ qR s₀ j, (Quad.kR (bp s₀)).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact Quad.kR_slots _
  · exact Offset.disjoint _ (by simp only [ctrOff]; omega) (by decide) (by decide)
  · exact (hp.d_b.symm.sub_left (kR_sub s₀)).sub_right (dW_sub s₀ j)
  · exact Offset.disjoint_base _ (by decide) (by decide)
  · exact hp.st_b.symm.sub_left (kR_sub s₀)

theorem quad4_ok {k : Kernel} (Kk : Quad.KernelOk k) {s₀ : State} (hp : XPre s₀) {j : Nat}
    (hj : P s₀ j + 65 ≤ L s₀) {s : State} (h : OInv s₀ j s) (hinv : Kk.Inv (bp s₀) s.mem)
    {C : Prog isa} {Q : State → Prop} (hk : ∀ s₃, Q4 s₀ j s s₃ → WP isa C s₃ Q) :
    WP isa (.seq (.block setup4) (.seq (rounds10 k) (.seq finish4 C))) s Q := by
  have hL := L_lt s₀
  have hc := ctx_of hp h.ebx h.edi h.wr
  have sl_st : (stR s₀).Disjoint (slotsR (bp s₀)) := hp.st_b.sub_right (slots_sub s₀)
  have ct_st : (stR s₀).Disjoint (ctrR (bp s₀)) := hp.st_b.sub_right (ctrR_sub s₀)
  have db : (dW (win s₀ j) (Wn s₀ j)).Disjoint (Quad.bufR (bp s₀)) := hp.d_b.sub_left (dW_sub s₀ j)
  have ds : (dW (win s₀ j) (Wn s₀ j)).Disjoint (Quad.stR (st s₀)) := hp.st_d.symm.sub_left (dW_sub s₀ j)
  -- The setup.
  refine WP.seq (WP.mono (Quad.setup4_ok hc) fun s₁ h₁ => ?_)
  have hc₁ : Quad.Ctx (st s₀) (bp s₀) s₁ := ctx_of hp (by rw [h₁.keep _ (by decide), h.ebx])
    (by rw [h₁.keep _ (by decide), h.edi]) (by rw [h₁.wr, h.wr])
  -- The rounds.
  refine WP.seq (WP.mono (Quad.rounds_ok hc₁.eaB hc₁.wb Kk (Kk.inv_frame hinv h₁.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact kR_qR hp j _ (by simp)
      · exact kR_qR hp j _ (by simp))) h₁.holds) fun s₂ h₂ => ?_)
  have hc₂ : Quad.Ctx (st s₀) (bp s₀) s₂ := hc₁.of h₂.gpr h₂.wr
  have hg₂ : ∀ r, r ≠ .eax → s₂.gpr r = s.gpr r := fun r hr => by rw [h₂.gpr, h₁.keep r hr]
  have hd₂ : Quad.DCtx (win s₀ j) (Wn s₀ j) s₂ := dctx_of hp (by rw [hg₂ _ (by decide), h.esi])
    (by rw [h₂.wr, h₁.wr, h.wr])
  have hct₂ : Quad.Ctrs (bp s₀) (stateAt s.mem (st s₀)) 4 s₂.mem := fun l hl => by
    rw [h₂.frame.readW (r := ctrR (bp s₀)) (Offset.contains _ (by omega) (by omega) (by decide))
      (by simp only [List.mem_singleton, forall_eq]; exact Offset.disjoint_base _ (by decide) (by decide))
      (by decide)]
    exact h₁.ctrs l hl
  have hC₂ : stateAt s₂.mem (st s₀) = stateAt s.mem (st s₀) :=
    (Quad.stateAt_frame h₂.frame (by simpa using sl_st)).trans
      (Quad.stateAt_frame h₁.frame (by simpa using ⟨sl_st, ct_st⟩))
  -- The output.
  refine WP.seq (WP.mono (Quad.finish4_ok hc₂ hd₂ (L_lt s₀ |> fun h' => by omega) rfl
    (by rw [hg₂ _ (by decide), h.ebp]) db ds h₂.holds hct₂ hC₂) fun s₃ h₃ => hk s₃ ?_)
  have hf₃ : Frame [slotsR (bp s₀), ctrR (bp s₀), dW (win s₀ j) (Wn s₀ j), Quad.stashR (bp s₀)] s.mem s₃.mem :=
    ((h₁.frame.mono (by simp)).trans (h₂.frame.mono (by simp))).trans (h₃.frame.mono (by simp))
  have hW : Wn s₀ j ≤ 256 := Nat.min_le_right _ _
  refine ⟨fun k hk => ?_, fun hz _ => h₃.stash hz (by simp only [Quad.sOff]; omega),
    fun r hr => by rw [h₃.gpr, hg₂ r hr], by rw [h₃.rd, h₂.rd, h₁.rd], by rw [h₃.wr, h₂.wr, h₁.wr], hf₃, ?_⟩
  · have e₂ : s₂.mem (win s₀ j + BitVec.ofNat 64 k) = s.mem (win s₀ j + BitVec.ofNat 64 k) :=
      (h₁.frame.trans (h₂.frame.mono (by simp))).bytes (R := dW (win s₀ j) (Wn s₀ j))
        (by simpa using ⟨db.sub_right (slots_sub s₀), db.sub_right (ctrR_sub s₀)⟩)
        (show Wn s₀ j ≤ 2 ^ 64 by omega) hk
    rw [h₃.data k hk, e₂]
    by_cases c : Quad.Full (Wn s₀ j) k
    · rw [ite_eq_left ⟨by omega, c⟩, ite_eq_left c]
    · rw [ite_eq_right (by omega), ite_eq_right c]
  · exact Quad.stateAt_frame hf₃ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl)
      · exact sl_st
      · exact ct_st
      · exact ds.symm
      · exact hp.st_b.sub_right (stash_sub s₀))

/-- The data before four blocks `j` that `Q4` leaves: what it was, outside
the `W` bytes of the four blocks. -/
theorem Q4.outside {s₀ : State} (hp : XPre s₀) {j : Nat} {s s₃ : State} (h₃ : Q4 s₀ j s s₃) {k : Nat}
    (hk : k < L s₀) (hw : ¬ (P s₀ j ≤ k ∧ k < P s₀ j + Wn s₀ j)) :
    s₃.mem (dp s₀ + BitVec.ofNat 64 k) = s.mem (dp s₀ + BitVec.ofNat 64 k) := by
  have hL := L_lt s₀
  have := P_le s₀ j
  have := Wn_le s₀ j
  refine h₃.frame _ fun r hr => ?_
  have hin : (dR s₀).Contains (dp s₀ + BitVec.ofNat 64 k) 1 := contains_ofNat (by omega) (by lit_omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hp.d_b.sub_right (slots_sub s₀)) _ hin
  · exact (hp.d_b.sub_right (ctrR_sub s₀)) _ hin
  · simp only [Region.Contains]
    rw [Offset.sub_toNat' _ (by lit_omega) (by lit_omega)]
    split <;> omega
  · exact (hp.d_b.sub_right (stash_sub s₀)) _ hin

/-- More than 256 bytes left: the counter advanced by 4, and the data by 256 bytes. -/
theorem next_ok {s₀ : State} (hp : XPre s₀) {j : Nat} (hj : P s₀ j + 257 ≤ L s₀) {s s₃ : State}
    (h : OInv s₀ j s) (h₃ : Q4 s₀ j s s₃) :
    WP isa (.block next4) s₃ fun s' => OInv s₀ (j + 4) s' ∧ Frame [stR s₀] s₃.mem s'.mem := by
  have hL := L_lt s₀
  have hPj : P s₀ j = 64 * j := by simp only [P] at *; omega
  have hP4 : P s₀ (j + 4) = P s₀ j + 256 := by simp only [P] at *; omega
  have hW : Wn s₀ j = 256 := by simp only [Wn]; omega
  have hcnt := h.cnt (by omega)
  unfold next4
  have e48 : addr (ST s₀) 48 = st s₀ + BitVec.ofNat 64 48 := hp.eaS (by decide)
  have i48 : InRegions (s₃.rd ++ s₃.wr) (addr (ST s₀) 48) 4 := by
    rw [e48, h₃.rd, h₃.wr, h.rd, h.wr]
    exact Quad.in_st (by rw [hp.wr]; simp) (by decide)
  refine Wp.wp_ldm (by rw [h₃.keep _ (by decide), h.ebx]) i48 fun s₄ u₄ => ?_
  refine Wp.wp_addi fun s₅ u₅ => ?_
  have o48 : InRegions s₅.wr (addr (ST s₀) 48) 4 := by
    rw [e48, u₅.wr, u₄.wr, h₃.wr, h.wr]
    exact Quad.out_st (by rw [hp.wr]; simp) (by decide)
  refine Wp.wp_stm (by rw [u₅.other _ (by decide), u₄.other _ (by decide), h₃.keep _ (by decide), h.ebx])
    o48 fun s₆ u₆ => ?_
  refine Wp.wp_addi fun s₇ u₇ => ?_
  refine Wp.wp_subi fun s₈ u₈ _ _ => WP.block_nil ?_
  have hg : ∀ r, r ≠ .eax → r ≠ .esi → r ≠ .ebp → s₈.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₈.other r h3, u₇.other r h2, u₆.gpr, u₅.other r h1, u₄.other r h1, h₃.keep r h1]
  have hv : s₃.mem.readW (st s₀ + BitVec.ofNat 64 48) 32 = (ctr (S0 s₀) j)[12] := by
    rw [← hcnt, ← h₃.st]
    simp [stateAt]
  have hm : s₈.mem = s₃.mem.writeW (st s₀ + BitVec.ofNat 64 48) ((ctr (S0 s₀) j)[12] + 4) := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.gpr, u₅.mem, u₄.gpr, u₄.mem, e48, hv]
  have fW : Frame [stR s₀] s₃.mem s₈.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_ofNat (by decide) (by decide))
  have hf : Frame (qR s₀ j) s.mem s₈.mem := (h₃.frame.mono (by simp)).trans (fW.mono (by simp))
  refine ⟨⟨by rw [hg _ (by decide) (by decide) (by decide), h.ebx], ?_,
    by rw [hg _ (by decide) (by decide) (by decide), h.edi], ?_,
    by rw [hg _ (by decide) (by decide) (by decide), h.esp],
    by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, h₃.rd, h.rd],
    by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, h₃.wr, h.wr], fun _ => ?_, fun k hk => ?_,
    h.saved.frame hf (qR_saved hp j), h.frame.trans (hf.sub (qR_frame s₀ j))⟩, fW⟩
  · rw [u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      h₃.keep _ (by decide), h.esi, show (256 : BitVec 32) = BitVec.ofNat 32 256 from rfl, Offset.add_add, hP4]
  · rw [u₈.gpr, u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      h₃.keep _ (by decide), h.ebp, show (256 : BitVec 32) = BitVec.ofNat 32 256 from rfl,
      Wp.sub_ofNat (by omega), hP4, Nat.sub_sub]
  · rw [hm, stateAt_writeW_counter, h₃.st, hcnt, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, ctr_add]
  · -- The data.
    have e₁ : s₈.mem (dp s₀ + BitVec.ofNat 64 k) = s₃.mem (dp s₀ + BitVec.ofNat 64 k) :=
      fW.bytes (R := dR s₀) (by simpa using hp.st_d.symm) (show L s₀ ≤ 2 ^ 64 by omega) hk
    rw [e₁]
    by_cases hw : P s₀ j ≤ k ∧ k < P s₀ j + 256
    · have ea : dp s₀ + BitVec.ofNat 64 k = win s₀ j + BitVec.ofNat 64 (k - P s₀ j) := by
        rw [Offset.add_add, Nat.add_sub_cancel' hw.1]
      rw [ea, h₃.data _ (by omega), ite_eq_left (by simp only [Quad.Full]; omega), ← ea, h.data k hk,
        ite_eq_right (by omega), ite_eq_left (by omega : k < P s₀ (j + 4)), hcnt,
        ksb_eq hPj (by omega), Nat.add_sub_cancel' hw.1]
    · rw [h₃.outside hp hk (by omega), h.data k hk]
      by_cases hk' : k < P s₀ j
      · rw [ite_eq_left hk', ite_eq_left (by omega)]
      · rw [ite_eq_right hk', ite_eq_right (by omega)]

/-- At most 256 bytes left: the bytes after the last multiple of 16 XORed
with the keystream in `buf[0, 16)`, and no bytes left. -/
theorem last_ok {s₀ : State} (hp : XPre s₀) {j : Nat} (hj : P s₀ j + 65 ≤ L s₀) (hle : L s₀ ≤ P s₀ j + 256)
    {s s₃ : State} (h : OInv s₀ j s) (h₃ : Q4 s₀ j s s₃) :
    WP isa last s₃ fun s' => OInv s₀ (j + 4) s' ∧ Frame [dR s₀] s₃.mem s'.mem := by
  have hL := L_lt s₀
  have hd := hp.d_fit
  have hb := hp.b_fit
  have hPj : P s₀ j = 64 * j := by simp only [P] at *; omega
  have hP4 : P s₀ (j + 4) = L s₀ := by simp only [P] at *; omega
  have hW : Wn s₀ j = L s₀ - P s₀ j := by simp only [Wn]; omega
  have hcnt := h.cnt (by omega)
  generalize hn : L s₀ - P s₀ j = n at hW
  have hq : n / 16 * 16 ≤ n := Nat.div_mul_le_self n 16
  -- The pointers and the count.
  unfold last
  refine WP.seq (WP.mono (Q := fun s₉ : State =>
      BPre s₉ (DP s₀ + BitVec.ofNat 32 (P s₀ j + n / 16 * 16)) (BP s₀) (n % 16) ∧
        (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .ebp → s₉.gpr r = s.gpr r) ∧
        s₉.gpr .ebp = 0 ∧ s₉.mem = s₃.mem ∧ s₉.rd = s₀.rd ∧ s₉.wr = s₀.wr)
    (Wp.wp_mov fun s₄ u₄ => Wp.wp_andi fun s₅ u₅ => Wp.wp_andi fun s₆ u₆ =>
      Wp.wp_add fun s₇ u₇ _ => Wp.wp_mov fun s₈ u₈ => Wp.wp_movi fun s₉ u₉ => WP.block_nil ?_)
    fun s₁₀ hb₁₀ => ?_)
  · have hebp : s₃.gpr .ebp = BitVec.ofNat 32 n := by rw [h₃.keep _ (by decide), h.ebp, hn]
    have hesi : s₃.gpr .esi = DP s₀ + BitVec.ofNat 32 (P s₀ j) := by rw [h₃.keep _ (by decide), h.esi]
    have g : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .ebp → s₉.gpr r = s.gpr r :=
      fun r h1 h2 h3 h4 h5 => by
        rw [u₉.other r h5, u₈.other r h3, u₇.other r h4, u₆.other r h5, u₅.other r h2, u₄.other r h2,
          h₃.keep r h1]
    have hrd : s₉.rd = s₀.rd := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, h₃.rd, h.rd]
    have hwr : s₉.wr = s₀.wr := by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, h₃.wr, h.wr]
    have hm : s₉.mem = s₃.mem := by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, fun k hk => ?_, fun k hk => ?_, fun a ha b hb' he => ?_⟩, g, u₉.gpr, hm, hrd, hwr⟩
    · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₆.other .esi (by decide),
        u₅.other .esi (by decide), u₅.other .ebp (by decide), u₄.other .esi (by decide),
        u₄.other .ebp (by decide), hesi, hebp, and_m16, toNat_ofNat_lt32 (by omega), BitVec.add_assoc,
        BitVec.ofNat_add_ofNat]
    · rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), u₄.other _ (by decide), h₃.keep _ (by decide), h.edi]
    · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.gpr, u₄.gpr, hebp, and_15, toNat_ofNat_lt32 (by omega)]
    · by_cases hz : n % 16 = 0
      · rw [hz]; exact Nat.le_of_lt (BitVec.isLt _)
      · rw [ofNat32_add_toNat _ (by omega)]; omega
    · omega
    · rw [hwr, setWidth_add _ (by omega), Offset.add_add]
      exact ⟨dR s₀, by simp [hp.wr], contains_ofNat (by omega) (by lit_omega)⟩
    · rw [hrd, hwr]
      exact ⟨bR s₀, by simp [hp.wr], contains_ofNat (by omega) (by lit_omega)⟩
    · rw [setWidth_add _ (by omega), Offset.add_add] at he
      exact hp.d_b _ (contains_ofNat (show P s₀ j + n / 16 * 16 + a + 1 ≤ L s₀ by omega) (by lit_omega))
        (by rw [he]; exact contains_ofNat (show b + 1 ≤ 320 by omega) (by lit_omega))
  -- The bytes.
  obtain ⟨hb₁, g₁, hebp₁, hm₁, hrd₁, hwr₁⟩ := hb₁₀
  refine WP.mono (xorBytes_ok hb₁) fun s' h' => ?_
  have hg : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .ebp → s'.gpr r = s.gpr r :=
    fun r a b c d e => by rw [h'.keep r a b c d, g₁ r a b c d e]
  have hf' : Frame [dR s₀] s₁₀.mem s'.mem := h'.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨dR s₀, List.mem_singleton_self _, ?_⟩
    by_cases hz : n % 16 = 0
    · rw [hz]; intro x hx; simp only [Region.Contains] at hx; omega
    · rw [setWidth_add _ (by omega)]
      exact Offset.sub_base _ (by omega)
  have hf : Frame (frameR s₀) s.mem s'.mem :=
    (h₃.frame.sub fun r hr => qR_frame s₀ j r (by
      simp only [qR, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp)).trans (hm₁ ▸ hf'.mono (by simp))
  refine ⟨⟨by rw [hg _ (by decide) (by decide) (by decide) (by decide) (by decide), h.ebx], ?_,
    by rw [hg _ (by decide) (by decide) (by decide) (by decide) (by decide), h.edi], ?_,
    by rw [hg _ (by decide) (by decide) (by decide) (by decide) (by decide), h.esp],
    by rw [h'.rd, hrd₁, hp.rd], by rw [h'.wr, hwr₁], fun hlt => absurd hlt (by omega), fun k hk => ?_,
    (h.saved.frame h₃.frame (fun r hr => qR_saved hp j r (by
      simp only [qR, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp))).frame (hm₁ ▸ hf') (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.d_b.symm.sub_left (savR_sub s₀)),
    h.frame.trans hf⟩, by rw [← hm₁]; exact hf'⟩
  · rw [h'.esi, BitVec.add_assoc, BitVec.ofNat_add_ofNat, hP4]
    congr 2; omega
  · rw [h'.keep _ (by decide) (by decide) (by decide) (by decide), hebp₁, hP4, Nat.sub_self]; rfl
  · -- The data.
    rw [ite_eq_left (by omega)]
    have hD : ∀ i, i < n % 16 → ((DP s₀ + BitVec.ofNat 32 (P s₀ j + n / 16 * 16)).setWidth 64 + BitVec.ofNat 64 i) =
        dp s₀ + BitVec.ofNat 64 (P s₀ j + n / 16 * 16 + i) := fun i hi => by
      rw [setWidth_add _ (by omega), Offset.add_add]
    have hwin : ∀ t, win s₀ j + BitVec.ofNat 64 t = dp s₀ + BitVec.ofNat 64 (P s₀ j + t) :=
      fun t => Offset.add_add _ _ _
    have hout : ∀ k, k < P s₀ j + n / 16 * 16 → s'.mem (dp s₀ + BitVec.ofNat 64 k) = s₁₀.mem (dp s₀ + BitVec.ofNat 64 k) :=
      fun k hk' => h'.frame _ fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        simp only [Region.Contains] at hcon
        have : 0 < n % 16 := by omega
        rw [setWidth_add _ (by omega), Offset.sub_toNat' _ (by lit_omega) (by lit_omega)] at hcon
        split at hcon <;> omega
    by_cases ha : k < P s₀ j
    · rw [hout k (by omega), hm₁, h₃.outside hp hk (by omega), h.data k hk, ite_eq_left ha]
    by_cases hb' : k < P s₀ j + n / 16 * 16
    · obtain ⟨t, rfl⟩ : ∃ t, k = P s₀ j + t := ⟨k - P s₀ j, by omega⟩
      rw [hout _ hb', hm₁, ← hwin, h₃.data t (by omega), ite_eq_left (by simp only [Quad.Full]; omega),
        hwin, h.data _ hk, ite_eq_right ha, hcnt, ksb_eq hPj (by omega)]
    · obtain ⟨i, rfl⟩ : ∃ i, k = P s₀ j + n / 16 * 16 + i := ⟨k - (P s₀ j + n / 16 * 16), by omega⟩
      have h3 := h'.data i (by omega)
      rw [hD i (by omega)] at h3
      rw [h3, hm₁, show P s₀ j + n / 16 * 16 + i = P s₀ j + (n / 16 * 16 + i) by omega, ← hwin,
        h₃.data _ (by omega), ite_eq_right (by simp only [Quad.Full]; omega), hwin, h.data _ (by omega),
        ite_eq_right (by omega)]
      congr 1
      have hs := h₃.stash (by omega) trivial i (by omega)
      rw [hW, show Quad.sOff n = n / 16 * 16 from rfl] at hs
      rw [show bp s₀ = (BP s₀).setWidth 64 from rfl] at hs
      rw [hs, hcnt, ksb_eq hPj (by omega)]

end Quad

theorem Q4.of {s₀ : State} {j : Nat} {s s₃ s₄ : State} (h : Q4 s₀ j s s₃) (hg : s₄.gpr = s₃.gpr)
    (hm : s₄.mem = s₃.mem) (hr : s₄.rd = s₃.rd) (hw : s₄.wr = s₃.wr) : Q4 s₀ j s s₄ :=
  ⟨fun k hk => by rw [hm]; exact h.data k hk, fun a b => by rw [hm]; exact h.stash a b,
    fun r hr' => by rw [hg]; exact h.keep r hr', by rw [hr, h.rd], by rw [hw, h.wr], hm ▸ h.frame,
    by rw [hm]; exact h.st⟩

theorem OInv.of {s₀ : State} {j : Nat} {s s' : State} (h : OInv s₀ j s) (hg : s'.gpr = s.gpr)
    (hm : s'.mem = s.mem) (hr : s'.rd = s.rd) (hw : s'.wr = s.wr) : OInv s₀ j s' :=
  ⟨by rw [hg, h.ebx], by rw [hg, h.esi], by rw [hg, h.edi], by rw [hg, h.ebp], by rw [hg, h.esp],
    by rw [hr, h.rd], by rw [hw, h.wr], fun hl => by rw [hm]; exact h.cnt hl,
    fun k hk => by rw [hm, h.data k hk], by rw [hm]; exact h.saved, by rw [hm]; exact h.frame⟩

/-! ## Four blocks: the loop body -/

theorem body4_ok {k : Kernel} (Kk : Quad.KernelOk k) {s₀ : State} (hp : XPre s₀) {j : Nat}
    (hj : P s₀ j + 65 ≤ L s₀) {s : State} (h : OInv s₀ j s) (hinv : Kk.Inv (bp s₀) s.mem) :
    WP isa (body4 k) s fun s' => (OInv s₀ (j + 4) s' ∧ Kk.Inv (bp s₀) s'.mem) ∧
      s'.cf = some (decide (L s₀ - P s₀ (j + 4) < 65)) := by
  have hL := L_lt s₀
  unfold body4
  refine quad4_ok Kk hp hj h hinv fun s₃ h₃ => ?_
  have hinv₃ : Kk.Inv (bp s₀) s₃.mem := Kk.inv_frame hinv h₃.frame fun r hr => kR_qR hp j r (by
    simp only [qR, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl <;> simp)
  refine WP.seq (WP.mono (Bytes.cmpi_ok s₃ .ebp 257) fun s₄ ⟨g₄, m₄, _, r₄, w₄, c₄⟩ => ?_)
  have hebp : s₃.gpr .ebp = BitVec.ofNat 32 (L s₀ - P s₀ j) := by rw [h₃.keep _ (by decide), h.ebp]
  rw [hebp, toNat_ofNat_lt32 (by omega), show (257 : BitVec 32).toNat = 257 from rfl] at c₄
  have h₄ := h₃.of g₄ m₄ r₄ w₄
  have hinv₄ : Kk.Inv (bp s₀) s₄.mem := m₄ ▸ hinv₃
  refine WP.seq (WP.mono (Q := fun s₅ : State => OInv s₀ (j + 4) s₅ ∧ Kk.Inv (bp s₀) s₅.mem)
    (WP.ite (decide (L s₀ - P s₀ j < 257)) (by show eval .b s₄ = _; simp only [eval, c₄])
      (fun hlt => WP.mono (last_ok hp hj (by simp only [decide_eq_true_eq] at hlt; omega) h h₄)
        fun s₅ ⟨h₅, f₅⟩ => ⟨h₅, Kk.inv_frame hinv₄ f₅ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact hp.d_b.symm.sub_left (kR_sub s₀))⟩)
      (fun hge => WP.mono (next_ok hp (by simp only [decide_eq_false_iff_not] at hge; omega) h h₄)
        fun s₅ ⟨h₅, f₅⟩ => ⟨h₅, Kk.inv_frame hinv₄ f₅ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact hp.st_b.symm.sub_left (kR_sub s₀))⟩))
    fun s₅ ⟨h₅, i₅⟩ => ?_)
  refine Wp.wp_cmpi fun s₆ u₆ hcf _ => WP.block_nil ⟨⟨h₅.of u₆.gpr u₆.mem u₆.rd u₆.wr, u₆.mem ▸ i₅⟩, ?_⟩
  rw [hcf, h₅.ebp, toNat_ofNat_lt32 (by omega)]; rfl

/-! ## The last bytes -/

/-- What the epilogue needs: the data done, and our caller's registers saved. -/
structure Done (s₀ : State) (s : State) : Prop where
  edi : s.gpr .edi = BP s₀
  esp : s.gpr .esp = E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  data : ∀ k < L s₀, s.mem (dp s₀ + BitVec.ofNat 64 k) = D0 s₀ k ^^^ (KS s₀).getD k 0
  saved : Saved s₀ s.mem
  frame : Frame (frameR s₀) s₀.mem s.mem

theorem OInv.done {s₀ : State} {j : Nat} {s : State} (h : OInv s₀ j s) (hj : P s₀ j = L s₀) : Done s₀ s :=
  ⟨h.edi, h.esp, h.rd, h.wr, fun k hk => by rw [h.data k hk, ite_eq_left (by omega)], h.saved, h.frame⟩

theorem tail_ok {s₀ : State} (hp : XPre s₀) {j : Nat} (hj : P s₀ j < L s₀) (hle : L s₀ ≤ P s₀ j + 64)
    {s : State} (h : OInv s₀ j s) : WP isa tail s (Done s₀) := by
  have hL := L_lt s₀
  have hd := hp.d_fit
  have hb := hp.b_fit
  have hPj : P s₀ j = 64 * j := by simp only [P] at *; omega
  unfold tail
  refine WP.seq (WP.mono (call_ok hp hj h) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (Q := fun s₃ : State => WPre s₃ (DP s₀ + BitVec.ofNat 32 (P s₀ j)) (BP s₀) (L s₀ - P s₀ j) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → s₃.gpr r = s₁.gpr r) ∧ s₃.mem = s₁.mem ∧
      s₃.rd = s₁.rd ∧ s₃.wr = s₁.wr)
    (Wp.wp_mov fun s₂ u₂ => Wp.wp_mov fun s₃ u₃ => WP.block_nil ?_) fun s₄ ⟨hw₄, g₄, m₄, r₄, w₄⟩ => ?_)
  · refine ⟨⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), h₁.esi],
      by rw [u₃.other _ (by decide), u₂.gpr, h₁.edi], by rw [u₃.gpr, u₂.other _ (by decide), h₁.ebp],
      by rw [ofNat32_add_toNat _ (by omega)] <;> omega, by omega, fun o n hn => ?_, fun o n hn => ?_, ?_⟩,
      fun r a b c d => by rw [u₃.other r b, u₂.other r c], by rw [u₃.mem, u₂.mem], by rw [u₃.rd, u₂.rd],
      by rw [u₃.wr, u₂.wr]⟩
    · rw [u₃.wr, u₂.wr, h₁.wr, setWidth_add _ (by omega), Offset.add_add]
      exact ⟨dR s₀, by simp [hp.wr], contains_ofNat (by omega) (by lit_omega)⟩
    · rw [u₃.rd, u₂.rd, u₃.wr, u₂.wr, h₁.rd, h₁.wr]
      exact ⟨bR s₀, by simp [hp.wr], contains_ofNat (by omega) (by lit_omega)⟩
    · rw [setWidth_add _ (by omega)]
      exact (hp.d_b.sub_left (Offset.sub_base _ (by omega))).sub_right (Region.sub_prefix (by omega))
  refine WP.mono (xorWide_ok hw₄) fun s' h' => ?_
  have hf' : Frame [dR s₀] s₄.mem s'.mem := h'.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨dR s₀, List.mem_singleton_self _, ?_⟩
    rw [setWidth_add _ (by omega)]
    exact Offset.sub_base _ (by omega)
  have hg : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → s'.gpr r = s₁.gpr r :=
    fun r a b c d => by rw [h'.keep r a b c d, g₄ r a b c d]
  refine ⟨by rw [hg _ (by decide) (by decide) (by decide) (by decide), h₁.edi],
    by rw [hg _ (by decide) (by decide) (by decide) (by decide), h₁.esp],
    by rw [h'.rd, r₄, h₁.rd], by rw [h'.wr, w₄, h₁.wr], fun k hk => ?_,
    h₁.saved.frame (m₄ ▸ hf') (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.d_b.symm.sub_left (savR_sub s₀)),
    h₁.frame.trans (m₄ ▸ hf'.mono (by simp))⟩
  by_cases ha : k < P s₀ j
  · have e : s'.mem (dp s₀ + BitVec.ofNat 64 k) = s₄.mem (dp s₀ + BitVec.ofNat 64 k) := by
      refine h'.frame _ fun r hr hcon => ?_
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains] at hcon
      rw [setWidth_add _ (by omega), Offset.sub_toNat' _ (by lit_omega) (by lit_omega)] at hcon
      split at hcon <;> omega
    rw [e, m₄, h₁.data k hk, ite_eq_left ha]
  · obtain ⟨t, rfl⟩ : ∃ t, k = P s₀ j + t := ⟨k - P s₀ j, by omega⟩
    have h3 := h'.data t (by omega)
    rw [setWidth_add _ (by omega), Offset.add_add] at h3
    rw [h3, m₄, h₁.data _ hk, ite_eq_right ha]
    congr 1
    rw [h₁.ks t (by omega), KS, keystream_getD _ hk, hPj, show (64 * j + t) / 64 = j by omega,
      show (64 * j + t) % 64 = t by omega]

/-! ## The epilogue -/

theorem restore_eq : restore = Spill.restoreCode .eax saved ++ [] := rfl

theorem ret_stack (s₀ : State) : (retR s₀).Disjoint (stackR s₀) := by
  have := Offset.disjoint_base (Es s₀ - BitVec.ofNat 64 12) (d := 12) (n := 4) (k := 12) (by decide) (by decide)
  rwa [BitVec.sub_add_cancel] at this

set_option simprocs false in
theorem epilogue_ok {s₀ : State} (hp : XPre s₀) {s : State} (h : Done s₀ s) :
    WP isa (.block (.mov .eax (.reg .edi) :: restore)) s fun s' =>
      (abiPreserved s₀ s' ∧ Proof.ChaCha20.xorX86.post s₀ s') ∧ s'.gpr .eax = BP s₀ := by
  have e : ∀ p ∈ saved, addr (BP s₀) p.2 = bp s₀ + BitVec.ofNat 64 p.2 :=
    fun p h => hp.eaB (by have := saved_fits.1 p h; lit_omega)
  rw [restore_eq]
  refine Wp.wp_mov fun s₁ u₁ => ?_
  have hB : s₁.gpr .eax = BP s₀ := by rw [u₁.gpr, h.edi]
  refine Spill.restore_ok saved (by decide) (fun p hp' => ?_)
    (by rw [hB, u₁.mem]; exact h.saved.congr (fun p h => (e p h).symm) fun _ _ => rfl)
    fun s' r' => WP.block_nil ⟨⟨⟨r'.abi (by decide) (by decide) (by rw [u₁.other _ (by decide), h.esp]), ?_⟩, ?_⟩,
      by rw [r'.other _ (by decide), hB]⟩
  · have := saved_fits.1 p hp'
    rw [hB, u₁.rd, u₁.wr, e p hp']
    exact ⟨bR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], contains_off (by lit_omega) (by lit_omega)⟩
  · rw [r'.mem, u₁.mem]
    refine h.frame.readW (Region.contains_self _ _) ?_ (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.ret_st
    · exact hp.ret_d
    · exact hp.ret_b
    · exact ret_stack s₀
  · show bytesAt s'.mem _ _ = _
    rw [r'.mem, u₁.mem]
    exact bytesAt_xor (length_keystream _ _) fun k hk => h.data k hk

/-! ## The whole function -/

theorem xor_eq (k : Kernel) : xorWith k =
    .seq (.block [.mov .eax (.mem (at_ .esp 16))]) (.seq (.block prologue) (.seq (.block k.init)
    (.seq (.block [.alu .cmp .ebp (.imm 65)])
    (.seq (.ite .b (.block []) (.loop (body4 k) .ae))
    (.seq (.block [.alu .test .ebp (.reg .ebp)])
    (.seq (.ite .e (.block []) tail) (.block (.mov .eax (.reg .edi) :: restore)))))))) := rfl

/-- The quarter round's constants stored in `buf[288, 320)`. -/
theorem init_ok {k : Kernel} (Kk : Quad.KernelOk k) {s₀ : State} (hp : XPre s₀) {s : State}
    (h : OInv s₀ 0 s) : WP isa (.block k.init) s fun s' => OInv s₀ 0 s' ∧ Kk.Inv (bp s₀) s'.mem := by
  have hL := L_lt s₀
  have hc := ctx_of hp h.ebx h.edi h.wr
  refine WP.mono (Kk.init_ok s hc.eaB hc.wb) fun s' ⟨hi, hf, hg, hr, hw⟩ => ⟨⟨by rw [hg _ (by decide), h.ebx],
    by rw [hg _ (by decide), h.esi], by rw [hg _ (by decide), h.edi], by rw [hg _ (by decide), h.ebp],
    by rw [hg _ (by decide), h.esp], by rw [hr, h.rd], by rw [hw, h.wr], fun hl => ?_, fun k hk => ?_,
    h.saved.frame hf (by simpa using (Offset.disjoint (bp s₀) (d := 256) (n := 16) (e := 288) (k := 32)
      (by omega) (by decide) (by decide))),
    h.frame.trans (hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨bR s₀, by simp, kR_sub s₀⟩)⟩, hi⟩
  · rw [stateAt_frame hf (by simpa using hp.st_b.sub_right (kR_sub s₀)), h.cnt hl]
  · rw [hf.bytes (R := dR s₀) (by simpa using hp.d_b.sub_right (kR_sub s₀)) (show L s₀ ≤ 2 ^ 64 by omega) hk,
      h.data k hk]

theorem cmp65_ok {s₀ : State} {s : State} (h : OInv s₀ 0 s) {I : Mem → Prop} (hi : I s.mem) :
    WP isa (.block [.alu .cmp .ebp (.imm 65)]) s fun s' =>
      (OInv s₀ 0 s' ∧ I s'.mem) ∧ s'.cf = some (decide (L s₀ < 65)) := by
  have hL := L_lt s₀
  refine Wp.wp_cmpi fun s' u hcf _ => WP.block_nil ⟨⟨h.of u.gpr u.mem u.rd u.wr, u.mem ▸ hi⟩, ?_⟩
  rw [hcf, h.ebp, toNat_ofNat_lt32 (by simp only [P]; omega)]
  simp [P]

theorem loop4_ok {k : Kernel} (Kk : Quad.KernelOk k) {s₀ : State} (hp : XPre s₀) {s : State}
    (h : OInv s₀ 0 s) (hinv : Kk.Inv (bp s₀) s.mem) (hL : 65 ≤ L s₀) :
    WP isa (.loop (body4 k) .ae) s fun s' => ∃ j, L s₀ - P s₀ j < 65 ∧ OInv s₀ j s' := by
  let Inv : Nat → State → Prop := fun n s =>
    ∃ j, n = L s₀ - P s₀ j ∧ P s₀ j + 65 ≤ L s₀ ∧ OInv s₀ j s ∧ Kk.Inv (bp s₀) s.mem
  have hstep : ∀ n s, Inv n s → WP isa (body4 k) s (fun s' =>
      (eval .ae s' = some false ∧ ∃ j, L s₀ - P s₀ j < 65 ∧ OInv s₀ j s') ∨
      (eval .ae s' = some true ∧ ∃ n' < n, Inv n' s')) := by
    rintro n s ⟨j, rfl, hj, hI, hi⟩
    refine WP.mono (body4_ok Kk hp hj hI hi) fun s' ⟨⟨h', hi'⟩, hc'⟩ => ?_
    have hP : P s₀ j < P s₀ (j + 4) := by simp only [P] at *; omega
    by_cases hl : L s₀ - P s₀ (j + 4) < 65
    · exact .inl ⟨by simp [eval, hc', hl], j + 4, hl, h'⟩
    · exact .inr ⟨by simp [eval, hc', hl], L s₀ - P s₀ (j + 4), by omega, j + 4, rfl, by omega, h', hi'⟩
  exact WP.loop (M := isa) Inv hstep (L s₀ - P s₀ 0) s ⟨0, rfl, by simp [P]; omega, h, hinv⟩

theorem test_ok {s₀ : State} {j : Nat} {s : State} (h : OInv s₀ j s) :
    WP isa (.block [.alu .test .ebp (.reg .ebp)]) s fun s' =>
      OInv s₀ j s' ∧ s'.zf = some (decide (L s₀ - P s₀ j = 0)) := by
  have hL := L_lt s₀
  refine Wp.wp_test fun s' u hz => WP.block_nil ⟨h.of u.gpr u.mem u.rd u.wr, ?_⟩
  rw [hz, h.ebp, BitVec.and_self, Wp.ofNat_beq_zero (by omega)]

theorem correct {k : Kernel} (Kk : Quad.KernelOk k) {s₀ : State} (hp : XPre s₀) :
    WP isa (xorWith k) s₀ fun s' =>
      (abiPreserved s₀ s' ∧ Proof.ChaCha20.xorX86.post s₀ s') ∧ s'.gpr .eax = BP s₀ := by
  rw [xor_eq]
  refine WP.seq (WP.mono (load_buf_ok hp) fun s e => ?_)
  subst e
  refine WP.seq (WP.mono (prologue_ok hp) fun s₀' h₀ => ?_)
  refine WP.seq (WP.mono (init_ok Kk hp h₀) fun s₀'' ⟨h₀', i₀⟩ => ?_)
  refine WP.seq (WP.mono (cmp65_ok h₀' i₀) fun s₁ ⟨⟨h₁, i₁⟩, hc⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ j, L s₀ - P s₀ j < 65 ∧ OInv s₀ j s) ?_
    fun s₂ ⟨j, hj, h₂⟩ => ?_)
  · refine WP.ite (decide (L s₀ < 65)) (by simp [eval, hc]) (fun h => ?_) (fun h => ?_)
    · simp only [decide_eq_true_eq] at h
      exact WP.block_nil (M := isa) ⟨0, by simp [P]; omega, h₁⟩
    · simp only [decide_eq_false_iff_not] at h
      exact loop4_ok Kk hp h₁ i₁ (by omega)
  refine WP.seq (WP.mono (test_ok h₂) fun s₃ ⟨h₃, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := Done s₀) ?_ fun s₄ h₄ => epilogue_ok hp h₄)
  have hle := P_le s₀ j
  refine WP.ite (decide (L s₀ - P s₀ j = 0)) (by simp [eval, hz]) (fun h => ?_) (fun h => ?_)
  · simp only [decide_eq_true_eq] at h
    exact WP.block_nil (M := isa) (h₃.done (by omega))
  · simp only [decide_eq_false_iff_not] at h
    exact tail_ok hp (by omega) (by omega) h₃

/-- `vg_chacha20_xor` returns with `eax` holding `buf`, for a caller that
recomputes pointers from it. -/
theorem xor_eax (s : State) (hs : Proof.ChaCha20.xorX86.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20.X86.Xor.xor s t s' ∧ abiPreserved s s' ∧
      (Proof.ChaCha20.xorX86.post s s' ∧ s'.gpr .eax = arg s 3) := by
  obtain ⟨t, s', he, ⟨h, hr⟩⟩ := correct Kernels.sse2Ok (XPre.of s hs)
  exact ⟨t, s', he, h.1, h.2, hr⟩

/-- `vg_chacha20_xor_ssse3` returns with `eax` holding `buf`. -/
theorem xorSsse3_eax (s : State) (hs : Proof.ChaCha20.xorX86.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20.X86.Xor.xorSsse3 s t s' ∧ abiPreserved s s' ∧
      (Proof.ChaCha20.xorX86.post s s' ∧ s'.gpr .eax = arg s 3) := by
  obtain ⟨t, s', he, ⟨h, hr⟩⟩ := correct Kernels.ssse3Ok (XPre.of s hs)
  exact ⟨t, s', he, h.1, h.2, hr⟩

/-! ## Constant time

The taint analysis follows the frames and the calls into the block function.
On entry it knows `esp` and where the writable regions are: `state`, the data
(whose length varies), `buf` and the arguments, which are public and at
`esp + 4`, and whose words 0 and 3 are the base addresses of `state` and
`buf`; and that the 12 bytes below `esp` are free for the frames and the
return addresses of the calls. -/

def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [64, 0, 320, 16], bases := [(.esp, 3, 4)],
    slots := [(3, 0, 16)], wbases := [(3, 0, 0), (3, 12, 2)], room := 12 }

theorem setWidth_toNat (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := x.isLt; omega)

theorem argWord_eq {s : State} (hsp : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32) {k : Nat} (hk : k < 16) :
    addr (s.gpr .esp) 4 + BitVec.ofNat 64 k = argAddr s (k / 4) + BitVec.ofNat 64 (k % 4) := by
  simp only [argAddr]
  rw [show (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * (k / 4))).setWidth 64 = addr (s.gpr .esp) (4 + 4 * (k / 4))
    from rfl, addr_eq (by lit_omega), addr_eq (by lit_omega), BitVec.add_assoc, BitVec.add_assoc,
    ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  congr 2; omega

theorem wf₀ {s : State} (hp : XPre s) : VG.X86.Taint.Wf τ₀ s := by
  have hst := hp.st_fit; have hd := hp.d_fit; have hb := hp.b_fit
  have hs : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 := hp.sp_hi
  have hlo : 12 ≤ (s.gpr .esp).toNat := hp.sp_lo
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩, ?_, ?_, fun h => absurd h (Nat.lt_irrefl 0),
    fun _ h => (List.not_mem_nil h).elim⟩ fun _ => ⟨hlo, ?_⟩
  · rw [hp.wr]
    exact .cons (Nat.le_refl _) (.cons (Nat.zero_le _) (.cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil)))
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨hp.st_d, hp.st_b, hp.a_st.symm⟩, ⟨hp.d_b, hp.a_d.symm⟩, hp.a_b.symm, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · simp only [st, setWidth_toNat]; omega
    · simp only [dp, setWidth_toNat]; omega
    · simp only [bp, setWidth_toNat]; omega
    · show (addr (s.gpr .esp) 4).toNat + 16 ≤ 2 ^ 32
      rw [addr_eq (by lit_omega), BitVec.toNat_add, setWidth_toNat, BitVec.toNat_ofNat]; omega
  · intro p hp'
    simp only [τ₀, List.mem_singleton] at hp'
    subst hp'
    show addr (s.gpr .esp) 4 = (VG.X86.Taint.region s 3).base
    rw [VG.X86.Taint.region, hp.wr]; rfl
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    · refine ⟨by decide, ?_⟩
      simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, hp.wr]
      show addr (s.mem.readW (addr (s.gpr .esp) 4 + BitVec.ofNat 64 0) 32) 0 = st s
      simp [addr, st, ST, arg, argAddr]
    · refine ⟨by decide, ?_⟩
      simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, hp.wr]
      show addr (s.mem.readW (addr (s.gpr .esp) 4 + BitVec.ofNat 64 12) 32) 0 = bp s
      rw [argWord_eq hs (k := 12) (by lit_omega)]
      simp [addr, bp, BP, arg]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.stk_st
    · exact hp.stk_d
    · exact hp.stk_b
    · intro x h₁ h₂
      simp only [Region.Contains, τ₀] at h₁ h₂
      rw [show argAddr s 0 = addr (s.gpr .esp) 4 from rfl, addr_eq (by lit_omega)] at h₂
      have := (s.gpr .esp).isLt
      have hE := setWidth_toNat (s.gpr .esp)
      generalize (s.gpr .esp).setWidth 64 = E at *
      bv_omega

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.ChaCha20.xorX86.pre s₁) (h₂ : Proof.ChaCha20.xorX86.pre s₂)
    (hpub : Proof.ChaCha20.xorX86.pub s₁ s₂) : VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := XPre.of _ h₁; have hp₂ := XPre.of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ hp₁, wf₀ hp₂, ?_, ?_,
    fun h => absurd h (Nat.lt_irrefl 0), fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [stR, dR, bR, aR, st, dp, bp, L, ST, DP, LN, BP, argAddr, ha 0 (by lit_omega),
      ha 1 (by lit_omega), ha 2 (by lit_omega), ha 3 (by lit_omega), hesp]
  · intro sl hsl
    simp only [τ₀, List.mem_singleton] at hsl
    subst hsl; decide
  · intro sl hsl k _ hk
    simp only [τ₀, List.mem_singleton] at hsl
    subst hsl
    simp only [Nat.zero_add] at hk
    simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, hp₁.wr, hp₂.wr]
    show s₁.mem (addr (s₁.gpr .esp) 4 + BitVec.ofNat 64 k) = s₂.mem (addr (s₂.gpr .esp) 4 + BitVec.ofNat 64 k)
    rw [argWord_eq hp₁.sp_hi hk, argWord_eq hp₂.sp_hi hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by lit_omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by lit_omega))]
    exact congrArg _ (ha _ (by lit_omega))

/-- Memory whose four argument slots (at `0x5004`) hold `0x1000`, `0x2000`,
`0` and `0x3000`. -/
def satMem : Mem := fun a =>
  if a = 0x5005 then 0x10 else if a = 0x5009 then 0x20 else if a = 0x5011 then 0x30 else 0

/-- A state satisfying the precondition (with no data). -/
def sat : State where
  gpr r := match r with
    | .esp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := []
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 0⟩, ⟨0x3000, 320⟩, ⟨0x5004, 16⟩]

theorem xor_correct (s : State) (hs : Proof.ChaCha20.xorX86.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20.X86.Xor.xor s t s' ∧ abiPreserved s s' ∧
      Proof.ChaCha20.xorX86.post s s' :=
  (xor_eax s hs).imp fun _ ⟨s', he, h, hp, _⟩ => ⟨s', he, h, hp⟩

theorem xorSsse3_correct (s : State) (hs : Proof.ChaCha20.xorX86.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20.X86.Xor.xorSsse3 s t s' ∧ abiPreserved s s' ∧
      Proof.ChaCha20.xorX86.post s s' :=
  (xorSsse3_eax s hs).imp fun _ ⟨s', he, h, hp, _⟩ => ⟨s', he, h, hp⟩

theorem xor_ct : ConstantTime isa Proof.ChaCha20.xorX86.pre Proof.ChaCha20.xorX86.pub
    Impl.ChaCha20.X86.Xor.xor :=
  VG.Taint.constantTime (A := sseTaint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide)

theorem xorSsse3_ct : ConstantTime isa Proof.ChaCha20.xorX86.pre Proof.ChaCha20.xorX86.pub
    Impl.ChaCha20.X86.Xor.xorSsse3 :=
  VG.Taint.constantTime (A := sseTaint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide)

theorem xorX86_implies : Proof.ChaCha20.xorX86.Implies (Spec.ChaCha20.xorContract X86.abi 12) := by
  have a0 : arg sat 0 = 0x1000 := by decide
  have a1 : arg sat 1 = 0x2000 := by decide
  have a2 : arg sat 2 = 0 := by decide
  have a3 : arg sat 3 = 0x3000 := by decide
  have e : argAddr sat 0 = 0x5004 := by decide
  have esp : sat.gpr .esp = 0x5000 := rfl
  sig_implies [Spec.ChaCha20.xorContract, Spec.ChaCha20.xorSig, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, Proof.ChaCha20.xorX86] [a0, a1, a2, a3, e, esp] using sat

theorem xor_verified :
    Verified X86.target Impl.ChaCha20.X86.Xor.xor (Spec.ChaCha20.xorContract X86.abi 12) :=
  Verified.of_correct xor_correct xor_ct xorX86_implies

theorem xorSsse3_verified :
    Verified X86.target Impl.ChaCha20.X86.Xor.xorSsse3 (Spec.ChaCha20.xorContract X86.abi 12) :=
  Verified.of_correct xorSsse3_correct xorSsse3_ct xorX86_implies

end VG.Proof.ChaCha20.X86.Xor
