import VerifiedGarbage.Proof.Scrypt.Spec
import VerifiedGarbage.Spec.Scrypt.Contract
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Sha256.X86.Stream.Common
import VerifiedGarbage.Proof.Scrypt.Memory
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Scrypt.X86.SalsaRounds
import VerifiedGarbage.Impl.Scrypt.X86.Salsa

/-!
# The Salsa20/8 Core on x86 (32-bit)

The contracts the proofs of this directory are written against, and the proof of
`vg_salsa20_8`: the rows of `b` are loaded (`load_ok`), put into the diagonal
layout and through the double rounds (`Proof/Scrypt/X86/SalsaRounds.lean`), put
back, and added to the input, which `b` keeps until then (`addRows_ok`). The
proof is written against a contract under which the code only reads its
arguments (which it does), and moved to the shared contract with
`Verified.narrowTo`.
-/

namespace VG.Proof.Scrypt

open Spec.Scrypt

open VG.X86 in
/-- X86 (32-bit) contract for `vg_salsa20_8(b: *mut [u8; 64], scratch: *mut
[u32; 16])`, whose arguments are on the stack (cdecl): replaces the 64 bytes at
`b` by their Salsa20/8 Core.

The code may read the arguments (8 bytes above the return address), and read
and write `b` and `scratch` (64 bytes each, the contents of `scratch` on
exit unspecified), which may not overlap each other, the arguments or the
return address, or wrap around the end of the (32-bit) address space. `esp`
and the pointers are public; the data is secret. -/
def salsaX86 : Contract X86.isa where
  pre s :=
    let b : Region := ⟨(arg s 0).setWidth 64, 64⟩
    let scratch : Region := ⟨(arg s 1).setWidth 64, 64⟩
    let args : Region := ⟨argAddr s 0, 8⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [args] ∧ s.wr = [b, scratch] ∧
    b.Disjoint scratch ∧ args.Disjoint b ∧ args.Disjoint scratch ∧ ret.Disjoint b ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 64 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 64 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 12 ≤ 2 ^ 32
  post s s' :=
    bytesAt s'.mem ((arg s 0).setWidth 64) 64 = salsa (bytesAt s.mem ((arg s 0).setWidth 64) 64)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1

open VG.X86 in
/-- X86 (32-bit) contract for `vg_scrypt_blockmix(b: *const [u8; 128], r: usize,
y: *mut [u8; 128], ry: usize, scratch: *mut [u32; 32])`, whose arguments are on
the stack (cdecl): if `ry = r > 0`, writes scryptBlockMix of the `128 r` bytes
at `b` to `y`.

The code may read the arguments (20 bytes above the return address) and
`b`, and read and write `y` and `scratch` (128 bytes). The written regions
may not overlap each other, `b`, the arguments or the return address; none
of the buffers may overlap the 12 bytes of stack below the return address
(where the code calls `vg_salsa20_8`); nothing may wrap around the end of
the (32-bit) address space. `esp` and the arguments are public; the data is
secret. -/
def blockMixX86 : Contract X86.isa where
  pre s :=
    let r := (arg s 1).toNat
    let b : Region := ⟨(arg s 0).setWidth 64, r * 128⟩
    let y : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat * 128⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 128⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 12, 12⟩
    s.rd = [b, args] ∧ s.wr = [y, scratch] ∧
    y.Disjoint scratch ∧ b.Disjoint y ∧ b.Disjoint scratch ∧ args.Disjoint y ∧ args.Disjoint scratch ∧
    ret.Disjoint y ∧ ret.Disjoint scratch ∧ stack.Disjoint b ∧ stack.Disjoint y ∧
    stack.Disjoint scratch ∧
    (arg s 0).toNat + r * 128 ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat * 128 ≤ 2 ^ 32 ∧
    (arg s 4).toNat + 128 ≤ 2 ^ 32 ∧ 12 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧
    arg s 3 = arg s 1 ∧ 0 < r
  post s s' := let r := (arg s 1).toNat
    bytesAt s'.mem ((arg s 2).setWidth 64) (128 * r) =
      blockMix r (bytesAt s.mem ((arg s 0).setWidth 64) (128 * r))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

open VG.X86 in
/-- X86 (32-bit) contract for `vg_scrypt_romix(b: *mut [u8; 128], r: usize, v:
*mut [u8; 128], vlen: usize, scratch: *mut [u8; 128], slen: usize)`, whose
arguments are on the stack (cdecl): if `r > 0`, `vlen = N r` for a power of two
`N`, and `slen = r + 2`, replaces the `128 r` bytes at `b` by their scryptROMix.

The code may read the arguments (24 bytes above the return address), and
read and write `b`, `v` and `scratch`, which may not overlap each other, the
arguments, the return address or the 36 bytes of stack below it (where the
code calls `vg_scrypt_blockmix`), or wrap around the end of the (32-bit)
address space. `esp`, the arguments and the indices `j` of step 3 are
public. -/
def roMixX86 : Contract X86.isa where
  pre s :=
    let r := (arg s 1).toNat
    let b : Region := ⟨(arg s 0).setWidth 64, r * 128⟩
    let v : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat * 128⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, (arg s 5).toNat * 128⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 36, 36⟩
    s.rd = [args] ∧ s.wr = [b, v, scratch] ∧
    b.Disjoint v ∧ b.Disjoint scratch ∧ v.Disjoint scratch ∧
    args.Disjoint b ∧ args.Disjoint v ∧ args.Disjoint scratch ∧
    ret.Disjoint b ∧ ret.Disjoint v ∧ ret.Disjoint scratch ∧
    stack.Disjoint b ∧ stack.Disjoint v ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + r * 128 ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat * 128 ≤ 2 ^ 32 ∧
    (arg s 4).toNat + (arg s 5).toNat * 128 ≤ 2 ^ 32 ∧ 36 ≤ (s.gpr .esp).toNat ∧
    (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧
    0 < r ∧ (arg s 3).toNat % r = 0 ∧ ((arg s 3).toNat / r).isPowerOfTwo ∧ (arg s 5).toNat = r + 2
  post s s' := let r := (arg s 1).toNat
    bytesAt s'.mem ((arg s 0).setWidth 64) (128 * r) =
      roMix r ((arg s 3).toNat / r) (bytesAt s.mem ((arg s 0).setWidth 64) (128 * r))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ (∀ i < 6, arg s₁ i = arg s₂ i) ∧
    roMixIndices (arg s₁ 1).toNat ((arg s₁ 3).toNat / (arg s₁ 1).toNat)
        (bytesAt s₁.mem ((arg s₁ 0).setWidth 64) (128 * (arg s₁ 1).toNat)) =
      roMixIndices (arg s₂ 1).toNat ((arg s₂ 3).toNat / (arg s₂ 1).toNat)
        (bytesAt s₂.mem ((arg s₂ 0).setWidth 64) (128 * (arg s₂ 1).toNat))

end VG.Proof.Scrypt

namespace VG.Proof.Scrypt.X86

open VG VG.X86 VG.Impl.Scrypt.X86
open VG.Spec.Scrypt (Word)
open VG.Proof.Scrypt
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_mov wp_movm wp_store addr_toNat)
open VG.Proof.Scrypt.Memory (contains_off)

/-! ## Instructions with a memory operand -/

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = addr (s.gpr b) d := rfl

/-! ## The precondition -/

section
variable (s₀ : State)
/-- `b`. -/
abbrev bP : BitVec 32 := arg s₀ 0
/-- `scratch`. -/
abbrev scP : BitVec 32 := arg s₀ 1
abbrev bA : Addr := (bP s₀).setWidth 64
abbrev sA : Addr := (scP s₀).setWidth 64
abbrev bR : Region := ⟨bA s₀, 64⟩
abbrev sR : Region := ⟨sA s₀, 64⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 8⟩
abbrev retR : Region := ⟨(s₀.gpr .esp).setWidth 64, 4⟩
/-- The input words. -/
def V : Vector Word 16 := Vector.ofFn fun j => s₀.mem.readW (bA s₀ + BitVec.ofNat 64 (4 * j.1)) 32
/-- The result of the rounds. -/
abbrev Rs : Vector Word 16 := Nat.repeat Spec.Scrypt.doubleRound 4 (V s₀)
end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [argR s₀]
  wr : s₀.wr = [bR s₀, sR s₀]
  disj : (bR s₀).Disjoint (sR s₀)
  a_b : (argR s₀).Disjoint (bR s₀)
  a_s : (argR s₀).Disjoint (sR s₀)
  ret_b : (retR s₀).Disjoint (bR s₀)
  ret_s : (retR s₀).Disjoint (sR s₀)
  b_fit : (bP s₀).toNat + 64 ≤ 2 ^ 32
  s_fit : (scP s₀).toNat + 64 ≤ 2 ^ 32
  sp_fit : (s₀.gpr .esp).toNat + 12 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : Proof.Scrypt.salsaX86.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem V_get (s₀ : State) {k : Nat} (hk : k < 16) :
    (V s₀)[k] = s₀.mem.readW (bA s₀ + BitVec.ofNat 64 (4 * k)) 32 := by
  simp only [V, Vector.getElem_ofFn]

theorem V_get! (s₀ : State) {k : Nat} (hk : k < 16) :
    (V s₀)[k]! = s₀.mem.readW (bA s₀ + BitVec.ofNat 64 (4 * k)) 32 := by
  rw [getElem!_pos (V s₀) k hk, V_get _ hk]

/-- `eax` is `b`, the other general-purpose registers are those on entry,
and so are the permissions. -/
structure Keep (s₀ s : State) : Prop where
  eax : s.gpr .eax = bP s₀
  gpr : ∀ r, r ≠ .eax → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem Keep.same {s₀ s s' : State} (h : Keep s₀ s) (e : Same s s') : Keep s₀ s' :=
  ⟨by rw [e.gpr, h.eax], fun r hr => by rw [e.gpr, h.gpr r hr], e.rd.trans h.rd, e.wr.trans h.wr⟩

/-! ## 16-byte loads and stores -/

/-- The general-purpose registers and the permissions are unchanged. -/
structure Regs (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Keep.regs {s₀ s s' : State} (h : Keep s₀ s) (e : Regs s s') : Keep s₀ s' :=
  ⟨by rw [e.gpr, h.eax], fun r hr => by rw [e.gpr, h.gpr r hr], e.rd.trans h.rd, e.wr.trans h.wr⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `movdqu d, [m]` -/
theorem wp_ldq {d : XReg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 16)
    (k : ∀ s', Regs s s' → s'.mem = s.mem → s'.xmm d = s.mem.readW a 128 →
      (∀ r, r ≠ d → s'.xmm r = s.xmm r) → WP isa (.block is) s' Q) :
    WP isa (.block (.movdquLoad d m :: is)) s Q :=
  Proof.Sha256.X86.Stream.WP.cons (s' := s.setXmm d (s.mem.readW a 128))
    (by simp only [exec, State.load128, ha, hin, ite_true, Option.map_some])
    (k _ ⟨rfl, rfl, rfl⟩ rfl (RegUpd.xmm_setXmm_self _ _ _) fun _ h => RegUpd.xmm_setXmm_of_ne _ _ h)

/-- `movdqu [m], r` -/
theorem wp_stq {r : XReg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 16)
    (k : ∀ s', Regs s s' → s'.mem = s.mem.writeW a (s.xmm r) → s'.xmm = s.xmm → WP isa (.block is) s' Q) :
    WP isa (.block (.movdquStore m r :: is)) s Q :=
  Proof.Sha256.X86.Stream.WP.cons (s' := { s with mem := s.mem.writeW a (s.xmm r) })
    (by simp only [exec, State.store128, ha, hout, ite_true]) (k _ ⟨rfl, rfl, rfl⟩ rfl rfl)

/-- `op d, r` on XMM registers. -/
theorem wp_xbin {op : XBinOp} {d r : XReg}
    (k : ∀ s', Regs s s' → s'.mem = s.mem → s'.xmm d = op.eval (s.xmm d) (s.xmm r) →
      (∀ q, q ≠ d → s'.xmm q = s.xmm q) → WP isa (.block is) s' Q) :
    WP isa (.block (xb op d r :: is)) s Q :=
  Proof.Sha256.X86.Stream.WP.cons (s' := s.setXmm d (op.eval (s.xmm d) (s.xmm r))) rfl
    (k _ ⟨rfl, rfl, rfl⟩ rfl (RegUpd.xmm_setXmm_self _ _ _) fun _ h => RegUpd.xmm_setXmm_of_ne _ _ h)

end

/-! ## Loading the rows -/

theorem arg_in {s₀ : State} (hp : Pre s₀) {d : Nat} (h1 : 4 ≤ d) (h2 : d + 4 ≤ 12) :
    InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .esp) d) 4 := by
  have hs := hp.sp_fit
  refine ⟨argR s₀, by simp [hp.rd], ?_⟩
  show (addr (s₀.gpr .esp) d - addr (s₀.gpr .esp) 4).toNat + 4 ≤ 8
  rw [addr_eq (by omega), addr_eq (by omega),
    show (s₀.gpr .esp).setWidth 64 + BitVec.ofNat 64 d - ((s₀.gpr .esp).setWidth 64 + BitVec.ofNat 64 4) =
      BitVec.ofNat 64 (d - 4) by rw [show d = (d - 4) + 4 by omega, BitVec.ofNat_add]; bv_omega,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-- Where `eax`-relative operands point, and that the code may access them. -/
theorem ea_b {s₀ s : State} (hp : Pre s₀) (h : Keep s₀ s) {d : Nat} (hd : d ≤ 48) :
    s.ea (at_ .eax d) = bA s₀ + BitVec.ofNat 64 d := by
  rw [ea_at, h.eax]; exact addr_eq (by have := hp.b_fit; omega)

theorem out_b16 {s₀ s : State} (hp : Pre s₀) (h : Keep s₀ s) {d : Nat} (hd : d + 16 ≤ 64) :
    InRegions s.wr (bA s₀ + BitVec.ofNat 64 d) 16 := by
  rw [h.wr]; exact ⟨bR s₀, by simp [hp.wr], contains_off (by omega) (by omega)⟩

theorem in_b16 {s₀ s : State} (hp : Pre s₀) (h : Keep s₀ s) {d : Nat} (hd : d + 16 ≤ 64) :
    InRegions (s.rd ++ s.wr) (bA s₀ + BitVec.ofNat 64 d) 16 :=
  let ⟨r, hr, hc⟩ := out_b16 hp h hd; ⟨r, List.mem_append_right _ hr, hc⟩

/-- Doubleword `q` of the row at `b + 16 k` is word `4 k + q`. -/
theorem row_word (s₀ : State) {k q : Nat} (hk : k < 4) (hq : q < 4) :
    dword (s₀.mem.readW (bA s₀ + BitVec.ofNat 64 (16 * k)) 128) q = (V s₀)[4 * k + q]! := by
  rw [dword_readW _ _ hq, Offset.add_add, V_get! _ (by omega)]
  exact congrArg (fun o => s₀.mem.readW (bA s₀ + BitVec.ofNat 64 o) 32) (by omega)

/-- The pointer and the rows, loaded. -/
theorem load_ok {s₀ : State} (hp : Pre s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s, Keep s₀ s → s.mem = s₀.mem → Arr rowIdx (V s₀) s → WP isa (.block rest) s Q) :
    WP isa (.block (load ++ rest)) s₀ Q := by
  simp only [load, List.cons_append, List.nil_append]
  refine wp_movm (a := addr (s₀.gpr .esp) 4) rfl (arg_in hp (by omega) (by omega)) fun s₁ u₁ => ?_
  have k₁ : Keep s₀ s₁ := ⟨by rw [u₁.gpr]; rfl, fun r h => u₁.other r h, u₁.rd, u₁.wr⟩
  refine wp_ldq (ea_b hp k₁ (d := 0) (by omega)) (in_b16 hp k₁ (by omega)) fun s₂ R₂ m₂ x₂ o₂ => ?_
  have k₂ := k₁.regs R₂
  refine wp_ldq (ea_b hp k₂ (d := 16) (by omega)) (in_b16 hp k₂ (by omega)) fun s₃ R₃ m₃ x₃ o₃ => ?_
  have k₃ := k₂.regs R₃
  refine wp_ldq (ea_b hp k₃ (d := 32) (by omega)) (in_b16 hp k₃ (by omega)) fun s₄ R₄ m₄ x₄ o₄ => ?_
  have k₄ := k₃.regs R₄
  refine wp_ldq (ea_b hp k₄ (d := 48) (by omega)) (in_b16 hp k₄ (by omega)) fun s₅ R₅ m₅ x₅ o₅ => ?_
  have k₅ := k₄.regs R₅
  have e₁ : s₁.mem = s₀.mem := u₁.mem
  refine k s₅ k₅ (by rw [m₅, m₄, m₃, m₂, e₁]) ⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · rw [o₅ .xmm0 (by decide), o₄ .xmm0 (by decide), o₃ .xmm0 (by decide), x₂, e₁]
    exact row_word s₀ (k := 0) (by omega) hq
  · rw [o₅ .xmm1 (by decide), o₄ .xmm1 (by decide), x₃, m₂, e₁]
    exact row_word s₀ (k := 1) (by omega) hq
  · rw [o₅ .xmm2 (by decide), x₄, m₃, m₂, e₁]
    exact row_word s₀ (k := 2) (by omega) hq
  · rw [x₅, m₄, m₃, m₂, e₁]
    exact row_word s₀ (k := 3) (by omega) hq

/-! ## Adding the input -/

/-- Word `j` after four 16-byte stores at `p`, `p + 16`, `p + 32` and `p + 48`. -/
theorem rows_read (m : Mem) (p : Addr) (X₀ X₁ X₂ X₃ : BitVec 128) {j : Nat} (hj : j < 16) :
    ((((m.writeW (p + BitVec.ofNat 64 0) X₀).writeW (p + BitVec.ofNat 64 16) X₁).writeW
      (p + BitVec.ofNat 64 32) X₂).writeW (p + BitVec.ofNat 64 48) X₃).readW (p + BitVec.ofNat 64 (4 * j)) 32 =
      dword (if j < 4 then X₀ else if j < 8 then X₁ else if j < 12 then X₂ else X₃) (j % 4) := by
  have hq : j % 4 < 4 := Nat.mod_lt _ (by decide)
  rcases (show j < 4 ∨ (4 ≤ j ∧ j < 8) ∨ (8 ≤ j ∧ j < 12) ∨ 12 ≤ j by omega) with h | h | h | h
  · rw [Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide),
      ← Offset.add_add_eq p (show 0 + 4 * (j % 4) = 4 * j by omega), readW_writeW128 _ _ _ hq,
      ite_eq_left h]
  · rw [Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide),
      ← Offset.add_add_eq p (show 16 + 4 * (j % 4) = 4 * j by omega), readW_writeW128 _ _ _ hq,
      ite_eq_right (by omega), ite_eq_left h.2]
  · rw [Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide),
      ← Offset.add_add_eq p (show 32 + 4 * (j % 4) = 4 * j by omega), readW_writeW128 _ _ _ hq,
      ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h.2]
  · rw [← Offset.add_add_eq p (show 48 + 4 * (j % 4) = 4 * j by omega), readW_writeW128 _ _ _ hq,
      ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

/-- Doubleword `q` of the sum of row `k` of the result and of the input. -/
theorem sum_word {s₀ s : State} {R : Vector Word 16} {x : XReg} {k q : Nat} (hk : k < 4) (hq : q < 4)
    (hx : dword (s.xmm x) q = R[4 * k + q]!) :
    dword (XBinOp.eval .paddd (s.xmm x) (s₀.mem.readW (bA s₀ + BitVec.ofNat 64 (16 * k)) 128)) q =
      R[4 * k + q]! + (V s₀)[4 * k + q]! := by
  rw [dword_paddd _ _ hq, hx, row_word s₀ hk hq]

theorem addRows_ok {s₀ : State} (hp : Pre s₀) {R : Vector Word 16} {s : State} (hk : Keep s₀ s)
    (hm : s.mem = s₀.mem) (h : Out R s) :
    WP isa (.block addRows) s fun s' => Keep s₀ s' ∧
      ∀ j < 16, s'.mem.readW (bA s₀ + BitVec.ofNat 64 (4 * j)) 32 = R[j]! + (V s₀)[j]! := by
  unfold addRows
  refine wp_ldq (ea_b hp hk (d := 0) (by omega)) (in_b16 hp hk (by omega)) fun s₁ R₁ m₁ x₁ o₁ => ?_
  have k₁ := hk.regs R₁
  refine wp_ldq (ea_b hp k₁ (d := 16) (by omega)) (in_b16 hp k₁ (by omega)) fun s₂ R₂ m₂ x₂ o₂ => ?_
  have k₂ := k₁.regs R₂
  refine wp_ldq (ea_b hp k₂ (d := 32) (by omega)) (in_b16 hp k₂ (by omega)) fun s₃ R₃ m₃ x₃ o₃ => ?_
  have k₃ := k₂.regs R₃
  refine wp_ldq (ea_b hp k₃ (d := 48) (by omega)) (in_b16 hp k₃ (by omega)) fun s₄ R₄ m₄ x₄ o₄ => ?_
  have k₄ := k₃.regs R₄
  refine wp_xbin fun s₅ R₅ m₅ x₅ o₅ => wp_xbin fun s₆ R₆ m₆ x₆ o₆ => wp_xbin fun s₇ R₇ m₇ x₇ o₇ =>
    wp_xbin fun s₈ R₈ m₈ x₈ o₈ => ?_
  have k₈ := (((k₄.regs R₅).regs R₆).regs R₇).regs R₈
  refine wp_stq (ea_b hp k₈ (d := 0) (by omega)) (out_b16 hp k₈ (by omega)) fun s₉ R₉ m₉ x₉ => ?_
  have k₉ := k₈.regs R₉
  refine wp_stq (ea_b hp k₉ (d := 16) (by omega)) (out_b16 hp k₉ (by omega)) fun s₁₀ R₁₀ m₁₀ x₁₀ => ?_
  have k₁₀ := k₉.regs R₁₀
  refine wp_stq (ea_b hp k₁₀ (d := 32) (by omega)) (out_b16 hp k₁₀ (by omega)) fun s₁₁ R₁₁ m₁₁ x₁₁ => ?_
  have k₁₁ := k₁₀.regs R₁₁
  refine wp_stq (ea_b hp k₁₁ (d := 48) (by omega)) (out_b16 hp k₁₁ (by omega)) fun s₁₂ R₁₂ m₁₂ x₁₂ => ?_
  refine WP.block_nil ⟨k₁₁.regs R₁₂, fun j hj => ?_⟩
  -- The rows stored, as sums of the loaded rows and those of the result.
  have l₀ : s₄.mem = s.mem := by rw [m₄, m₃, m₂, m₁]
  have y₀ : s₈.xmm .xmm0 = XBinOp.eval .paddd (s.xmm .xmm0) (s₀.mem.readW (bA s₀ + BitVec.ofNat 64 0) 128) := by
    rw [o₈ .xmm0 (by decide), o₇ .xmm0 (by decide), o₆ .xmm0 (by decide), x₅, o₄ .xmm0 (by
      decide), o₃ .xmm0 (by decide), o₂ .xmm0 (by decide), o₁ .xmm0 (by decide), o₄ .xmm3 (by
      decide), o₃ .xmm3 (by decide), o₂ .xmm3 (by decide), x₁, hm]
  have y₁ : s₉.xmm .xmm1 = XBinOp.eval .paddd (s.xmm .xmm1) (s₀.mem.readW (bA s₀ + BitVec.ofNat 64 16) 128) := by
    rw [x₉, o₈ .xmm1 (by decide), o₇ .xmm1 (by decide), x₆, o₅ .xmm1 (by decide), o₄ .xmm1 (by
      decide), o₃ .xmm1 (by decide), o₂ .xmm1 (by decide), o₁ .xmm1 (by decide), o₅ .xmm5 (by
      decide), o₄ .xmm5 (by decide), o₃ .xmm5 (by decide), x₂, m₁, hm]
  have y₂ : s₁₀.xmm .xmm2 = XBinOp.eval .paddd (s.xmm .xmm2) (s₀.mem.readW (bA s₀ + BitVec.ofNat 64 32) 128) := by
    rw [x₁₀, x₉, o₈ .xmm2 (by decide), x₇, o₆ .xmm2 (by decide), o₅ .xmm2 (by decide), o₄ .xmm2
      (by decide), o₃ .xmm2 (by decide), o₂ .xmm2 (by decide), o₁ .xmm2 (by decide), o₆ .xmm6
      (by decide), o₅ .xmm6 (by decide), o₄ .xmm6 (by decide), x₃, m₂, m₁, hm]
  have y₃ : s₁₁.xmm .xmm4 = XBinOp.eval .paddd (s.xmm .xmm4) (s₀.mem.readW (bA s₀ + BitVec.ofNat 64 48) 128) := by
    rw [x₁₁, x₁₀, x₉, x₈, o₇ .xmm4 (by decide), o₆ .xmm4 (by decide), o₅ .xmm4 (by decide), o₄
      .xmm4 (by decide), o₃ .xmm4 (by decide), o₂ .xmm4 (by decide), o₁ .xmm4 (by decide), o₇
      .xmm7 (by decide), o₆ .xmm7 (by decide), o₅ .xmm7 (by decide), x₄, m₃, m₂, m₁, hm]
  rw [m₁₂, m₁₁, m₁₀, m₉, m₈, m₇, m₆, m₅, l₀, y₃, y₂, y₁, y₀, rows_read _ _ _ _ _ _ hj]
  have hq : j % 4 < 4 := Nat.mod_lt _ (by decide)
  rcases (show j < 4 ∨ (4 ≤ j ∧ j < 8) ∨ (8 ≤ j ∧ j < 12) ∨ 12 ≤ j by omega) with c | c | c | c
  · rw [ite_eq_left c]
    refine (sum_word (k := 0) (by decide) hq ((h.r0 _ hq).trans
      (congrArg (fun i => R[i]!) (by omega)))).trans (congrArg (fun i => R[i]! + (V s₀)[i]!) (by omega))
  · rw [ite_eq_right (by omega), ite_eq_left c.2]
    refine (sum_word (k := 1) (by decide) hq ((h.r1 _ hq).trans
      (congrArg (fun i => R[i]!) (by omega)))).trans (congrArg (fun i => R[i]! + (V s₀)[i]!) (by omega))
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left c.2]
    refine (sum_word (k := 2) (by decide) hq ((h.r2 _ hq).trans
      (congrArg (fun i => R[i]!) (by omega)))).trans (congrArg (fun i => R[i]! + (V s₀)[i]!) (by omega))
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    refine (sum_word (k := 3) (by decide) hq ((h.r3 _ hq).trans
      (congrArg (fun i => R[i]!) (by omega)))).trans (congrArg (fun i => R[i]! + (V s₀)[i]!) (by omega))

/-! ## The whole function -/

/-- The input words are those the specification reads from the bytes. -/
theorem input_eq (s₀ : State) :
    (Vector.ofFn fun j : Fin 16 => Spec.Scrypt.wordLE (Spec.Scrypt.bytesAt s₀.mem (bA s₀) 64) j.1) =
      V s₀ := by
  apply Vector.ext
  intro j hj
  rw [Vector.getElem_ofFn, V_get _ hj, wordLE_bytesAt _ _ (by omega)]

/-- The result words are where the specification writes its bytes. -/
theorem post_of {s₀ : State} {m : Mem}
    (h : ∀ j < 16, m.readW (bA s₀ + BitVec.ofNat 64 (4 * j)) 32 = (Rs s₀)[j]! + (V s₀)[j]!) :
    Spec.Scrypt.bytesAt m (bA s₀) 64 = Spec.Scrypt.salsa (Spec.Scrypt.bytesAt s₀.mem (bA s₀) 64) := by
  rw [Spec.Scrypt.salsa, input_eq]
  refine bytesAt_eq_serialize _ _ _ fun j hj => ?_
  rw [Spec.Scrypt.core, Vector.getElem_zipWith, h j hj, getElem!_pos _ j hj, getElem!_pos _ j hj]

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa salsa s₀ fun s' => Keep s₀ s' ∧ Proof.Scrypt.salsaX86.post s₀ s' := by
  refine WP.seq (load_ok hp fun s₁ k₁ m₁ a₁ => ?_)
  refine WP.mono (toDiag_ok a₁) fun s₂ ⟨a₂, g₂, m₂, r₂, w₂⟩ => ?_
  have k₂ := k₁.same ⟨g₂, m₂, r₂, w₂⟩
  refine WP.seq (WP.mono (rounds_ok a₂ 4) fun s₃ ⟨a₃, e₃⟩ => ?_)
  have k₃ := k₂.same e₃
  rw [finish, WP.block_append_iff]
  refine WP.mono (fromDiag_ok a₃) fun s₄ ⟨o₄, g₄, m₄, r₄, w₄⟩ => ?_
  refine WP.mono (addRows_ok hp (k₃.same ⟨g₄, m₄, r₄, w₄⟩) (by rw [m₄, e₃.mem, m₂, m₁]) o₄)
    fun s' ⟨k', h'⟩ => ⟨k', ?_⟩
  show Spec.Scrypt.bytesAt s'.mem (bA s₀) 64 = Spec.Scrypt.salsa (Spec.Scrypt.bytesAt s₀.mem (bA s₀) 64)
  exact post_of h'

theorem salsa_correct (s : State) (hs : Proof.Scrypt.salsaX86.pre s) :
    ∃ t s', Exec isa Impl.Scrypt.X86.salsa s t s' ∧ abiPreserved s s' ∧
      Proof.Scrypt.salsaX86.post s s' := by
  have hp := pre_of s hs
  obtain ⟨t, s', he, hk, h₂⟩ := correct hp
  refine ⟨t, s', he, ⟨fun r hr => ?_, ?_⟩, h₂⟩
  · refine hk.gpr r ?_; rintro rfl; simp [calleeSaved] at hr
  · obtain ⟨-, -, hf⟩ := Exec.regions he (by decide)
    rw [hp.wr] at hf
    refine hf.readW (r := retR s) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [hp.ret_b, hp.ret_s]

/-! ## Constant time -/

/-- The taint analysis starts with `esp` public, and the words holding `b`
and `scratch` known to be the base addresses of the writable regions. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [64, 64], argLen := 12,
    argBases := [(4, 0), (8, 1)] }

theorem wf₀ {s : State} (hp : Pre s) : VG.X86.Taint.Wf τ₀ s := by
  have hb := hp.b_fit; have hsc := hp.s_fit; have hs := hp.sp_fit
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, τ₀], by simpa [hp.wr] using hp.disj, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 8) (by omega) hp.ret_b hp.a_b
    · exact VG.X86.Taint.frame_disjoint (n := 8) (by omega) hp.ret_s hp.a_s
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Scrypt.salsaX86.pre s₁)
    (h₂ : Proof.Scrypt.salsaX86.pre s₂) (hpub : Proof.Scrypt.salsaX86.pub s₁ s₂) :
    VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, a0, a1⟩ := hpub
  have hp₁ := pre_of _ h₁; have hp₂ := pre_of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ hp₁, wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]; simp only [bR, sR, bA, sA, bP, scP, a0, a1]
  · simp only [τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq hp₁.sp_fit h4 hk, VG.X86.Taint.argByte_eq hp₂.sp_fit h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    have : (k - 4) / 4 = 0 ∨ (k - 4) / 4 = 1 := by omega
    rcases this with h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1

theorem salsa_ct : ConstantTime isa Proof.Scrypt.salsaX86.pre Proof.Scrypt.salsaX86.pub
    Impl.Scrypt.X86.salsa :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) τ₀ (fun _ _ h₁ h₂ hpub => agree₀ h₁ h₂ hpub)
    (by taint_decide)

/-- Memory holding the arguments `0x1000, 0x2000` at `0x4004`. -/
def satMem : Mem := fun a => if a = 0x4005 then 0x10 else if a = 0x4009 then 0x20 else 0

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x4004, 8⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 64⟩]

theorem sat_pre : Proof.Scrypt.salsaX86.pre satState := by
  have a0 : arg satState 0 = 0x1000 := by decide
  have a1 : arg satState 1 = 0x2000 := by decide
  have e : argAddr satState 0 = 0x4004 := by decide
  simp only [Proof.Scrypt.salsaX86, a0, a1, e]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide⟩ <;>
  exact Region.disjoint_of_sep (by decide)

/-! ## The shared contract -/

/-- `salsaX86` with its arguments writable, as the shared contract lets them be. -/
def salsaWide : Contract isa :=
  { Proof.Scrypt.salsaX86 with
    pre := fun s =>
      let b : Region := ⟨(arg s 0).setWidth 64, 64⟩
      let scratch : Region := ⟨(arg s 1).setWidth 64, 64⟩
      let args : Region := ⟨argAddr s 0, 8⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      s.rd = [] ∧ s.wr = [b, scratch, args] ∧
      b.Disjoint scratch ∧ args.Disjoint b ∧ args.Disjoint scratch ∧ ret.Disjoint b ∧
      ret.Disjoint scratch ∧
      (arg s 0).toNat + 64 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 64 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 12 ≤ 2 ^ 32 }

/-- The regions `salsaX86` lets the code read and write. -/
def narrowRd (s : State) : List Region := [⟨argAddr s 0, 8⟩]
def narrowWr (s : State) : List Region := [⟨(arg s 0).setWidth 64, 64⟩, ⟨(arg s 1).setWidth 64, 64⟩]

/-- Rewrites the contracts at a narrowed state (`arg` does not unfold
cheaply). -/
local macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [Proof.Scrypt.salsaX86, VG.Proof.Scrypt.X86.salsaWide,
    VG.Proof.Scrypt.X86.narrowRd, VG.Proof.Scrypt.X86.narrowWr, VG.X86.arg_withRegions,
    VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
    VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr] $(loc)?)

theorem salsaWide_pre (s : State) (h : salsaWide.pre s) :
    Proof.Scrypt.salsaX86.pre (s.withRegions (narrowRd s) (narrowWr s)) := by
  obtain ⟨_, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩ := h
  narrow
  exact ⟨trivial, trivial, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩

/-- A state satisfying `salsaWide.pre`. -/
def wideSat : State := { satState with rd := [], wr := [⟨0x1000, 64⟩, ⟨0x2000, 64⟩, ⟨0x4004, 8⟩] }

theorem salsaWide_implies : salsaWide.Implies (Spec.Scrypt.salsaContract X86.abi) := by
  have a0 : arg wideSat 0 = 0x1000 := by decide
  have a1 : arg wideSat 1 = 0x2000 := by decide
  have e : argAddr wideSat 0 = 0x4004 := by decide
  have esp : wideSat.gpr .esp = 0x4000 := rfl
  sig_implies [Spec.Scrypt.salsaContract, Spec.Scrypt.salsaSig, salsaWide, Proof.Scrypt.salsaX86,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [a0, a1, e, esp] using wideSat

/-- The proof is written against `salsaX86`, widened to writable arguments. -/
theorem salsa_verified :
    Verified X86.target Impl.Scrypt.X86.salsa (Spec.Scrypt.salsaContract X86.abi) :=
  have hsat := salsaWide_implies.sat_left
  (Verified.narrowTo (Verified.of_correct salsa_correct salsa_ct (.refl ⟨satState, sat_pre⟩))
    narrowRd narrowWr salsaWide_pre
    (fun _ h => by
      obtain ⟨h₁, h₂, _⟩ := h
      rw [h₁, h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [narrowRd, narrowWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [narrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩)
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat).of_implies salsaWide_implies

end VG.Proof.Scrypt.X86
