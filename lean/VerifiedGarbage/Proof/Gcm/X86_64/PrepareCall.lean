module

public import VerifiedGarbage.Impl.Gcm.X86_64.PrepareCall
public import VerifiedGarbage.Spec.Gcm.Prepared
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Gcm.X86_64.Ghash
import VerifiedGarbage.Proof.Gcm.X86_64.Bits
import VerifiedGarbage.Proof.Gcm.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Proof.AesGcm.X86_64.GhashImpls
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Gcm.Poly
import VerifiedGarbage.Proof.Gcm.Powers
meta import VerifiedGarbage.Impl.Gcm.X86_64.PrepareCall
meta import VerifiedGarbage.Spec.Gcm.Prepared
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Gcm.X86_64.Ghash
meta import VerifiedGarbage.Proof.Gcm.X86_64.Bits
meta import VerifiedGarbage.Proof.Gcm.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Call
meta import VerifiedGarbage.Proof.Framework.X86_64.Registration
meta import VerifiedGarbage.Proof.AesGcm.X86_64.GhashImpls
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.X86_64.Inline
meta import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Gcm.Poly
meta import VerifiedGarbage.Proof.Gcm.Powers

/-!
# The 48 prepared powers of a key context, by calls of `vg_ghash` (x86-64)

`prepare_verified` proves `Impl.Gcm.X86_64.PrepareCall.prepare`
(`vg_aes_gcm_prepare` calling an implementation `G` of `vg_ghash`) against
`Spec.Gcm.prepareContract`. `St n` is what holds before step `n`: `Hⁿ` in
its slot, at `rsi`, the prepared powers below `n` in theirs, and the copy of
`H`, the zero block and the saved registers in the scratch buffer at `r8`.
`setup_ok` establishes `St 1`; `step_ok` takes `St n` to `St (n + 1)`, by
`copy_ok`, `pp_ok` (`hInv_ok`: the prepared power), `add_ok` and `mulH_ok`
(`call_ok`: `WP.call` with `vg_ghash`'s contract); `pairs_ok` composes the
pairs by induction; `final_ok` stores `H⁴⁸`'s and restores the registers.
Constant time, and the checks that evaluate the code, are per implementation
of `vg_ghash` (`Gh`): `taint_decide` with `ctx`, `scratch` and `rsp` public,
which `vg_ghash` keeps public in `rsi` and `r8`.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.PrepareCall

/-- `inner`, calling `vg_ghash`. -/
def innerScalar : Prog X86_64.isa := Impl.Gcm.X86_64.PrepareCall.inner "vg_ghash" Impl.Gcm.X86_64.ghash

end VG.Proof.Gcm.X86_64.PrepareCall

namespace VG

materialize_code Proof.Gcm.X86_64.PrepareCall.innerScalar

end VG

namespace VG.Proof.Gcm.X86_64.PrepareCall

open VG VG.X86_64
open VG.Impl.Gcm.X86_64.PrepareCall
open VG.Spec.Gcm (Block blockAt hpow preparedPower)

/-- `inner`'s contract, on the registers: the context at `rdi`, its 312
bytes of working space at `rsi`, both writable and apart from each other and
from the return address and the 8 bytes below it, which its calls use. -/
def innerX86_64 : Contract isa where
  pre s :=
    let ctx : Region := ⟨s.gpr .rdi, 1024⟩
    let scr : Region := ⟨s.gpr .rsi, 312⟩
    s.rd = [] ∧ s.wr = [ctx, scr] ∧ (s.gpr .rdi).toNat + 1024 ≤ 2 ^ 64 ∧
    (s.gpr .rsi).toNat + 312 ≤ 2 ^ 64 ∧ ctx.Disjoint scr ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ctx ∧ (⟨s.gpr .rsp, 8⟩ : Region).Disjoint scr ∧
    (below (s.gpr .rsp) 8).Disjoint ctx ∧ (below (s.gpr .rsp) 8).Disjoint scr ∧
    8 ≤ (s.gpr .rsp).toNat
  post s s' := Spec.Aes.bytesAt s'.mem (s.gpr .rdi) 256 = Spec.Aes.bytesAt s.mem (s.gpr .rdi) 256 ∧
    Spec.Gcm.PreparedPowersRepr s'.mem (s.gpr .rdi)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `inner`'s contract: `vg_aes_gcm_prepare`'s, with its working space as
an argument. -/
abbrev innerContract : Contract isa :=
  Sig.scratchContract X86_64.abi Spec.Gcm.prepareSig "scratch" .u64 39 (Curry.const (fun _ => True) _)
    (Spec.Gcm.preparePost 64) true 8

theorem innerScalar_ct : ConstantTime isa innerX86_64.pre innerX86_64.pub innerScalar := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rsp]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [h1, h2, h3]

open VG.Proof.AesGcm.X86_64 (GhashImpl GhashName)

/-- An implementation of `vg_ghash` that `inner` may call: one that writes
neither `rsi` nor `r8`, with `inner`'s checks when it calls it (its code
evaluated). -/
structure Gh where
  g : GhashImpl
  rsi : ∀ i ∈ instrs g.fn.code, Taint.clobbers i .rsi = false
  r8 : ∀ i ∈ instrs g.fn.code, Taint.clobbers i .r8 = false
  ct : ConstantTime isa innerX86_64.pre innerX86_64.pub (inner g.fn.name g.fn.code)
  mxcsr : (inner g.fn.name g.fn.code).allInstrs (fun i => !loadsMxcsr i) = true
  spSafe : (inner g.fn.name g.fn.code).all (fun i => !isa.writesSp i) = true
  depth : (inner g.fn.name g.fn.code).x86_64Depth ≤ 8

/-- `vg_ghash` never writes `r`. -/
theorem keeps_of {c : Prog isa} {r : Reg} (h : c.allInstrs (fun i => !Taint.clobbers i r) = true) :
    ∀ i ∈ instrs c, Taint.clobbers i r = false := by
  rw [Code.allInstrs_eq, List.all_eq_true] at h
  intro i hi; simpa using h i hi

theorem scalar_rsi : ∀ i ∈ instrs Impl.Gcm.X86_64.ghash, Taint.clobbers i .rsi = false :=
  keeps_of (by lit_decide)
theorem scalar_r8 : ∀ i ∈ instrs Impl.Gcm.X86_64.ghash, Taint.clobbers i .r8 = false :=
  keeps_of (by lit_decide)
theorem scalar_mxcsr : innerScalar.allInstrs (fun i => !loadsMxcsr i) = true := by lit_decide
theorem scalar_spSafe : innerScalar.all (fun i => !isa.writesSp i) = true := Code.all_of_allInstrs (by lit_decide)
theorem scalar_depth : innerScalar.x86_64Depth ≤ 8 := by lit_decide

def Gh.scalar : Gh :=
  ⟨.scalar, scalar_rsi, scalar_r8, innerScalar_ct, scalar_mxcsr, scalar_spSafe, scalar_depth⟩

/-- `inner` calling the implementation `n` of `vg_ghash`, for the
implementations with no `vg_aes_gcm_prepare` of their own: none for those
of `vg_ghash_pclmul` and `vg_ghash_vpclmul`, whose suffixes are those of
`vg_aes_gcm_prepare_pclmul` and `vg_aes_gcm_prepare_vpclmul`
(`Artifacts/Gcm/X86_64.lean`), which compute the powers with their own
carry-less multiplications. -/
def Gh.ofName : GhashName → Option Gh
  | .scalar => some .scalar
  | .pclmul => none
  | .vpclmul => none

set_option linter.unusedSimpArgs false

/-! ## Addresses and memory -/

theorem offset_nat (i : Nat) : BitVec.ofInt 64 (i : Int) = BitVec.ofNat 64 i := rfl

theorem imm_ofNat {n : Nat} (h : n < 2 ^ 31) : (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  have hm : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; simp; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-- A read 8 bytes apart from a write, at offsets from the same address. -/
theorem rw_off (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32) (he : e < 2 ^ 32)
    (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (p + BitVec.ofNat 64 e) v).readW (p + BitVec.ofNat 64 d) 64 = m.readW (p + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep p h (by omega) (by omega)) (by decide)

/-- A read in one region and a write in another, apart from it. -/
theorem rw_disj {C S : Addr} {kc ks : Nat} (h : (⟨C, kc⟩ : Region).Disjoint ⟨S, ks⟩) (m : Mem) (v : BitVec 64)
    {d e : Nat} (hd : d + 8 ≤ kc) (he : e + 8 ≤ ks) (hkc : kc < 2 ^ 32) (hks : ks < 2 ^ 32) :
    (m.writeW (S + BitVec.ofNat 64 e) v).readW (C + BitVec.ofNat 64 d) 64 = m.readW (C + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (h.sep (Offset.contains_base C hd (by omega)) (Offset.contains_base S he (by omega)))
    (by decide)

/-- `readW` of 16 bytes is the high 8 after the low 8. -/
theorem readW128 (m : Mem) (a : Addr) :
    m.readW a 128 = m.readW (a + BitVec.ofNat 64 8) 64 ++ m.readW a 64 := by
  apply BitVec.eq_of_toNat_eq
  have h := Proof.Mont.read_toNat_add m 8 8 a
  have e1 : (m.readW a 128).toNat = (m.read a (8 + 8)).toNat := by
    simp only [Mem.readW, BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (m.read a (8 + 8)).isLt
  have e2 : ∀ b, (m.readW b 64).toNat = (m.read b 8).toNat := fun b => by
    simp only [Mem.readW, BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (m.read b 8).isLt
  rw [e1, BitVec.toNat_append, e2, e2, h, ← Nat.shiftLeft_add_eq_or_of_lt (m.read a 8).isLt,
    Nat.shiftLeft_eq]
  omega

/-- A block, from its two 8-byte words. -/
theorem blockAt_words (m : Mem) (p : Addr) (d : Nat) :
    blockAt m (p + BitVec.ofNat 64 d) =
      X86_64.bswap64 (m.readW (p + BitVec.ofNat 64 d) 64) ++
        X86_64.bswap64 (m.readW (p + BitVec.ofNat 64 (d + 8)) 64) := by
  rw [← Proof.Gcm.X86_64.blockAt_bswap, BitVec.add_zero, Offset.add_add]

/-! ## The state on entry -/

section
variable {s₀ : State} (hp : innerX86_64.pre s₀)
include hp

theorem inC {d n : Nat} (h : d + n ≤ 1024) : InRegions s₀.wr (s₀.gpr .rdi + BitVec.ofNat 64 d) n :=
  ⟨_, by rw [hp.2.1]; exact List.mem_cons_self .., Offset.contains_base _ h (by omega)⟩

theorem inS {d n : Nat} (h : d + n ≤ 312) : InRegions s₀.wr (s₀.gpr .rsi + BitVec.ofNat 64 d) n :=
  ⟨_, by rw [hp.2.1]; simp, Offset.contains_base _ h (by omega)⟩

theorem inC' {d n : Nat} (h : d + n ≤ 1024) :
    InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rdi + BitVec.ofNat 64 d) n := by
  rw [hp.1, List.nil_append]; exact inC hp h

theorem inS' {d n : Nat} (h : d + n ≤ 312) :
    InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsi + BitVec.ofNat 64 d) n := by
  rw [hp.1, List.nil_append]; exact inS hp h

end

/-- Runs a block of the instructions `inner` uses. -/
macro "prun" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp (disch := first | decide | omega) only [imm_ofNat, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, execAlu, State.load64, State.store64, State.ea, offset_nat, Impl.Gcm.X86_64.at_, BitVec.add_zero,
    Option.bind_some, Option.map_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_setReg,
    RegUpd.mem_arithFlags, RegUpd.rd_setReg, RegUpd.rd_arithFlags, RegUpd.wr_setReg, RegUpd.wr_arithFlags,
    ite_true, ite_false, reduceCtorEq, ↓reduceIte, Nat.reduceAdd, and_self, and_true, true_and, Option.some.injEq, exists_eq_left', $ts,*]))

/-! ## The state between steps -/

/-- The offset in the context of power `n`'s slot: pair `k` is `H²ᵏ⁺²`,
then `H²ᵏ⁺¹`. -/
def slot (n : Nat) : Nat := if n % 2 = 1 then 256 + 16 * n else 224 + 16 * n

theorem slot_lo {n : Nat} (h : 1 ≤ n) : 256 ≤ slot n := by unfold slot; split <;> omega

theorem slot_hi {n : Nat} (h : n ≤ 48) : slot n + 16 ≤ 1024 := by unfold slot; split <;> omega

theorem slot_sep {j k : Nat} (hjk : j ≠ k) : slot j + 16 ≤ slot k ∨ slot k + 16 ≤ slot j := by
  unfold slot; split <;> split <;> omega

/-- The hash subkey. -/
abbrev Hk (s₀ : State) : Block := Spec.Gcm.ctxH s₀.mem (s₀.gpr .rdi)

/-- Where `inner` writes: the powers' half of the context, the scratch
buffer and the 8 bytes below the stack pointer, where its calls put their
return address. -/
abbrev fr (s₀ : State) : List Region :=
  [⟨s₀.gpr .rdi + BitVec.ofNat 64 256, 768⟩, ⟨s₀.gpr .rsi, 312⟩, below (s₀.gpr .rsp) 8]

/-- What holds before step `n`: `Hⁿ` in its slot, at `rsi`, and the prepared
powers below `n` in theirs. -/
structure St (s₀ : State) (n : Nat) (s : State) : Prop where
  rsi : s.gpr .rsi = s₀.gpr .rdi + BitVec.ofNat 64 (slot n)
  r8 : s.gpr .r8 = s₀.gpr .rsi
  rsp : s.gpr .rsp = s₀.gpr .rsp
  keep : ∀ r ∈ [Reg.rbx, .rbp, .r15], s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (fr s₀) s₀.mem s.mem
  sv12 : s.mem.readW (s₀.gpr .rsi + BitVec.ofNat 64 288) 64 = s₀.gpr .r12
  sv13 : s.mem.readW (s₀.gpr .rsi + BitVec.ofNat 64 296) 64 = s₀.gpr .r13
  sv14 : s.mem.readW (s₀.gpr .rsi + BitVec.ofNat 64 304) 64 = s₀.gpr .r14
  h : blockAt s.mem (s₀.gpr .rsi + BitVec.ofNat 64 256) = Hk s₀
  z : blockAt s.mem (s₀.gpr .rsi + BitVec.ofNat 64 272) = 0
  y : blockAt s.mem (s₀.gpr .rdi + BitVec.ofNat 64 (slot n)) = hpow (Hk s₀) n
  st : ∀ j, 1 ≤ j → j < n →
    s.mem.readW (s₀.gpr .rdi + BitVec.ofNat 64 (slot j)) 128 = preparedPower (hpow (Hk s₀) j)

/-! ## Regions -/

section
variable {s₀ : State} (hp : innerX86_64.pre s₀)
include hp

/-- Bytes of the context are apart from bytes of the scratch buffer. -/
theorem cs_disj {d n e k : Nat} (hd : d + n ≤ 1024) (he : e + k ≤ 312) :
    (⟨s₀.gpr .rdi + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨s₀.gpr .rsi + BitVec.ofNat 64 e, k⟩ :=
  (hp.2.2.2.2.1.sub_left (Offset.sub_base _ hd)).sub_right (Offset.sub_base _ he)

/-- Bytes of the context are apart from the 8 below the stack pointer. -/
theorem cb_disj {d n : Nat} (hd : d + n ≤ 1024) :
    (⟨s₀.gpr .rdi + BitVec.ofNat 64 d, n⟩ : Region).Disjoint (below (s₀.gpr .rsp) 8) :=
  (hp.2.2.2.2.2.2.2.1.sub_right (Offset.sub_base _ hd)).symm

/-- Bytes of the scratch buffer are apart from the 8 below the stack pointer. -/
theorem sb_disj {e k : Nat} (he : e + k ≤ 312) :
    (⟨s₀.gpr .rsi + BitVec.ofNat 64 e, k⟩ : Region).Disjoint (below (s₀.gpr .rsp) 8) :=
  (hp.2.2.2.2.2.2.2.2.1.sub_right (Offset.sub_base _ he)).symm

end

/-- The words the scratch buffer keeps, from byte 256, are apart from what
`vg_ghash` writes there. -/
theorem s_hi_disj (s₀ : State) {e k : Nat} (h : 256 ≤ e) (he : e + k ≤ 312) :
    (⟨s₀.gpr .rsi + BitVec.ofNat 64 e, k⟩ : Region).Disjoint ⟨s₀.gpr .rsi, 256⟩ :=
  Offset.disjoint_base _ h (by omega)

/-- Two slots. -/
theorem slots_disj (s₀ : State) {j k : Nat} (hj : j ≤ 48) (hk : k ≤ 48) (hjk : j ≠ k) :
    (⟨s₀.gpr .rdi + BitVec.ofNat 64 (slot j), 16⟩ : Region).Disjoint
      ⟨s₀.gpr .rdi + BitVec.ofNat 64 (slot k), 16⟩ :=
  Offset.disjoint _ (slot_sep hjk) (by have := slot_hi hj; omega) (by have := slot_hi hk; omega)

/-! ## The steps -/

theorem add_ofInt_zero (p : Addr) : p + BitVec.ofInt 64 0 = p := BitVec.add_zero p

theorem ofInt_eight : BitVec.ofInt 64 8 = BitVec.ofNat 64 8 := rfl

theorem add_ofNat_zero (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

/-- An address `d` bytes from slot `a`, which is slot `b`. -/
theorem shift_eq (p : Addr) {a b : Nat} {d : Int} (h : (b : Int) = a + d) :
    p + BitVec.ofNat 64 a + BitVec.ofInt 64 d = p + BitVec.ofNat 64 b := by
  rw [BitVec.add_assoc]
  congr 1
  rw [show BitVec.ofNat 64 a + BitVec.ofInt 64 d = BitVec.ofInt 64 (a + d) by
    rw [BitVec.ofInt_add, BitVec.ofInt_natCast], ← h, BitVec.ofInt_natCast]

theorem blockAt_P (m : Mem) (P : Addr) :
    blockAt m P = X86_64.bswap64 (m.readW P 64) ++ X86_64.bswap64 (m.readW (P + BitVec.ofNat 64 8) 64) := by
  have := blockAt_words m P 0
  rwa [add_ofNat_zero] at this

theorem inApp {rd wr : List Region} {a : Addr} {n : Nat} (h : InRegions wr a n) : InRegions (rd ++ wr) a n :=
  let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩

/-- `pp`: the block at `rsi`, at `P`, turned into its prepared power. -/
theorem pp_ok {s : State} {P : Addr} (hP : s.gpr .rsi = P) (h0 : InRegions s.wr P 8)
    (h8 : InRegions s.wr (P + BitVec.ofNat 64 8) 8) :
    WP isa (.block pp) s fun s' =>
      s'.mem.readW P 128 = preparedPower (blockAt s.mem P) ∧
      Frame [⟨P, 16⟩] s.mem s'.mem ∧
      (∀ r, r ∉ [Reg.rdi, .rax, .r11, .r12, .r13, .r14] → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have c0 : (⟨P, 16⟩ : Region).Contains P (64 / 8) := by
    have := Offset.contains_base P (d := 0) (n := 8) (k := 16) (by decide) (by decide)
    rwa [add_ofNat_zero] at this
  have c8 : (⟨P, 16⟩ : Region).Contains (P + BitVec.ofNat 64 8) (64 / 8) :=
    Offset.contains_base P (d := 8) (n := 8) (k := 16) (by decide) (by decide)
  have hx : Proof.Gcm.X86_64.Ctmul.xInv = 0xc2000000000000000000000000000001 := by decide
  simp only [pp, List.singleton_append]
  rw [WP.block_append_iff, WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  have e0 : (s.setReg .rdi (s.gpr .rsi)).gpr .rdi + BitVec.ofInt 64 ((0 : Nat) : Int) = P := by
    simp only [RegUpd.gpr_setReg, ↓reduceIte, offset_nat, add_ofNat_zero, hP]
  have e8 : (s.setReg .rdi (s.gpr .rsi)).gpr .rdi + BitVec.ofInt 64 ((8 : Nat) : Int) = P + BitVec.ofNat 64 8 := by
    simp only [RegUpd.gpr_setReg, ↓reduceIte, offset_nat, hP]
  have ew : (s.setReg .rdi (s.gpr .rsi)).wr = s.wr := RegUpd.wr_setReg ..
  have er : (s.setReg .rdi (s.gpr .rsi)).rd = s.rd := RegUpd.rd_setReg ..
  have em : (s.setReg .rdi (s.gpr .rsi)).mem = s.mem := RegUpd.mem_setReg ..
  refine WP.mono (Proof.Gcm.X86_64.hInv_ok _ (by rw [e0, er, ew]; exact inApp h0)
    (by rw [e8, er, ew]; exact inApp h8)) fun s₂ ⟨hK, _, hk⟩ => ?_
  beta_reduce at hK
  rw [e0, e8, em, ← blockAt_P] at hK
  obtain ⟨hg, hm, hrd, hwr⟩ := hk
  have hrsi : s₂.gpr .rsi = P := by
    rw [hg _ (by decide)]; simp only [RegUpd.gpr_setReg, reduceCtorEq, ↓reduceIte, hP]
  have w0 : InRegions s₂.wr P 8 := by rw [hwr, ew]; exact h0
  have w8 : InRegions s₂.wr (P + BitVec.ofNat 64 8) 8 := by rw [hwr, ew]; exact h8
  apply WP.of_runBlock
  prun [hrsi, w0, w8, add_ofNat_zero]
  refine ⟨?_, ?_, fun r hr => ?_, ?_, ?_⟩
  · rw [readW128, Mem.readW_writeW_self64,
      Mem.readW_writeW_sep (Offset.sep_base P (n := 8) (e := 8) (k := 8) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self64, Spec.Gcm.preparedPower, ← hx]
    exact hK
  · rw [hm, em]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _ c8
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨r1, r2, r3, r4, r5, r6⟩ := hr
    rw [hg r (by simp [Impl.Gcm.X86_64.AL, Impl.Gcm.X86_64.AH, Impl.Gcm.X86_64.PL, Impl.Gcm.X86_64.PH, r2, r3, r4, r5, r6]),
      RegUpd.gpr_setReg]
    simp only [r1, ↓reduceIte]
  · rw [hrd, er]
  · rw [hwr, ew]

/-- `copy d`: the block at `rsi`, at `P`, copied to `Q`, `d` bytes on. -/
theorem copy_ok {s : State} {P Q : Addr} {d : Int} (hP : s.gpr .rsi = P)
    (hQ : P + BitVec.ofInt 64 d = Q) (hQ8 : P + BitVec.ofInt 64 (d + 8) = Q + BitVec.ofNat 64 8)
    (hPQ : (⟨P, 16⟩ : Region).Disjoint ⟨Q, 16⟩)
    (r0 : InRegions (s.rd ++ s.wr) P 8) (r8 : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 8) 8)
    (w0 : InRegions s.wr Q 8) (w8 : InRegions s.wr (Q + BitVec.ofNat 64 8) 8) :
    WP isa (.block (copy d)) s fun s' =>
      blockAt s'.mem Q = blockAt s.mem P ∧ Frame [⟨Q, 16⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have c0 : (⟨Q, 16⟩ : Region).Contains Q (64 / 8) := by
    have := Offset.contains_base Q (d := 0) (n := 8) (k := 16) (by decide) (by decide)
    rwa [add_ofNat_zero] at this
  have c8 : (⟨Q, 16⟩ : Region).Contains (Q + BitVec.ofNat 64 8) (64 / 8) :=
    Offset.contains_base Q (d := 8) (n := 8) (k := 16) (by decide) (by decide)
  have p8 : (⟨P, 16⟩ : Region).Contains (P + BitVec.ofNat 64 8) (64 / 8) :=
    Offset.contains_base P (d := 8) (n := 8) (k := 16) (by decide) (by decide)
  have sep : (Mem.writeW s.mem Q (s.mem.readW P 64)).readW (P + BitVec.ofNat 64 8) 64 =
      s.mem.readW (P + BitVec.ofNat 64 8) 64 :=
    Mem.readW_writeW_sep (hPQ.sep p8 c0) (by decide)
  apply WP.of_runBlock
  simp only [copy]
  prun [hP, hQ, hQ8, r0, r8, w0, w8, add_ofNat_zero, sep, add_ofInt_zero, ofInt_eight]
  refine ⟨?_, ?_, fun r hr => ?_⟩
  · rw [blockAt_P, blockAt_P, Mem.readW_writeW_self64,
      Mem.readW_writeW_sep (Offset.sep_base Q (n := 8) (e := 8) (k := 8) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self64]
  · exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _ c8
  · simp only [hr, ↓reduceIte]

theorem bytesAt_fr {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
    Spec.Aes.bytesAt m' p n = Spec.Aes.bytesAt m p n := by
  simp only [Spec.Aes.bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

theorem blockAt_fr {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 16⟩ : Region).Disjoint r) : blockAt m' p = blockAt m p := by
  rw [blockAt, blockAt, bytesAt_fr hf hd (by decide)]

/-- The return address a call stores. -/
theorem callEntry_fr (s : State) : Frame [below (s.gpr .rsp) 8] s.mem s.callEntry.mem := by
  rw [State.callEntry_mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))

theorem blocksAt_one_eq (m : Mem) (p : Addr) : Spec.Gcm.blocksAt m p 1 = [blockAt m p] := by
  simp [Spec.Gcm.blocksAt, add_ofNat_zero]

/-- A call of `vg_ghash` on the block at `C + e`, with the copy of `H` and the
zero block of the scratch buffer. -/
theorem call_ok (G : Gh) {s₀ : State} (hp : innerX86_64.pre s₀) {s : State} {e : Nat} (he : e + 16 ≤ 1024)
    (hrdi : s.gpr .rdi = s₀.gpr .rsi + BitVec.ofNat 64 256)
    (hrsi : s.gpr .rsi = s₀.gpr .rdi + BitVec.ofNat 64 e)
    (hrdx : s.gpr .rdx = s₀.gpr .rsi + BitVec.ofNat 64 272) (hrcx : s.gpr .rcx = BitVec.ofNat 64 1)
    (hr8 : s.gpr .r8 = s₀.gpr .rsi)
    (hrsp : s.gpr .rsp = s₀.gpr .rsp) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hz : blockAt s.mem (s₀.gpr .rsi + BitVec.ofNat 64 272) = 0) :
    WP isa (.call G.g.fn.name G.g.fn.code) s fun s' =>
      blockAt s'.mem (s₀.gpr .rdi + BitVec.ofNat 64 e) =
        Spec.Gcm.mul (blockAt s.mem (s₀.gpr .rdi + BitVec.ofNat 64 e))
          (blockAt s.mem (s₀.gpr .rsi + BitVec.ofNat 64 256)) ∧
      Frame [⟨s₀.gpr .rdi + BitVec.ofNat 64 e, 16⟩, ⟨s₀.gpr .rsi, 256⟩, below (s₀.gpr .rsp) 8] s.mem s'.mem ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.gpr .rsi = s.gpr .rsi ∧ s'.gpr .r8 = s.gpr .r8 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hS0 : s₀.gpr .rsi = s₀.gpr .rsi + BitVec.ofNat 64 0 := (add_ofNat_zero _).symm
  have yS : (⟨s₀.gpr .rdi + BitVec.ofNat 64 e, 16⟩ : Region).Disjoint ⟨s₀.gpr .rsi, 256⟩ := by
    have := cs_disj hp (d := e) (n := 16) (e := 0) (k := 256) he (by decide)
    rwa [add_ofNat_zero] at this
  have hd1 : (16 * (BitVec.ofNat 64 1).toNat) = 16 := rfl
  have hwr' : s.wr = [⟨s₀.gpr .rdi, 1024⟩, ⟨s₀.gpr .rsi, 312⟩] := hwr.trans hp.2.1
  have hrd' : s.rd = [] := hrd.trans hp.1
  have cov : ∀ r ∈ ([⟨s₀.gpr .rsi + BitVec.ofNat 64 256, 16⟩, ⟨s₀.gpr .rsi + BitVec.ofNat 64 272, 16⟩] ++
      [⟨s₀.gpr .rdi + BitVec.ofNat 64 e, 16⟩, ⟨s₀.gpr .rsi, 256⟩] : List Region),
      ∃ r' ∈ s.wr, ∃ off, r.base = r'.base + BitVec.ofNat 64 off ∧ off + r.len ≤ r'.len := by
    rw [hwr']
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), 256, rfl, (by decide : 256 + 16 ≤ 312)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), 272, rfl, (by decide : 272 + 16 ≤ 312)⟩
    · exact ⟨_, List.mem_cons_self .., e, rfl, he⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), 0, hS0, (by decide : 0 + 256 ≤ 312)⟩
  refine WP.call (k := Proof.Gcm.ghashX86_64) G.g.ok G.g.nosp (by rw [G.g.depth]; decide)
    (rd := [⟨s₀.gpr .rsi + BitVec.ofNat 64 256, 16⟩, ⟨s₀.gpr .rsi + BitVec.ofNat 64 272, 16⟩])
    (wr := [⟨s₀.gpr .rdi + BitVec.ofNat 64 e, 16⟩, ⟨s₀.gpr .rsi, 256⟩]) ?_
    (Covers.right (Covers.of_sub cov))
    (Covers.of_sub fun r hr => cov r (List.mem_append_right _ hr))
    ?_
  · simp only [Proof.Gcm.ghashX86_64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
      State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
      State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp),
      hrdi, hrsi, hrdx, hrcx, hr8, hrsp, hd1]
    refine ⟨trivial, trivial, (cs_disj hp he (by decide)).symm, s_hi_disj s₀ (by decide) (by decide),
      cs_disj hp he (by decide), yS, s_hi_disj s₀ (by decide) (by decide), (cb_disj hp he).symm, ?_⟩
    have := (sb_disj hp (e := 0) (k := 256) (by decide)).symm
    rwa [add_ofNat_zero] at this
  · intro s' hrd₂ hwr₂ hcs hf hkeep ⟨s₂, hm₂, _, hpost⟩
    rw [G.g.depth] at hf
    simp only [Proof.Gcm.ghashX86_64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
      State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
      hrdi, hrsi, hrdx, hrcx, hm₂, blocksAt_one_eq] at hpost
    have fE := callEntry_fr s
    rw [hrsp] at fE
    have dE : ∀ {d : Nat}, d + 16 ≤ 312 → ∀ r ∈ [below (s₀.gpr .rsp) 8],
        (⟨s₀.gpr .rsi + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := fun hd r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact sb_disj hp hd
    have eZ : blockAt s.callEntry.mem (s₀.gpr .rsi + BitVec.ofNat 64 272) = 0 :=
      (blockAt_fr fE (dE (d := 272) (by decide))).trans hz
    have eY : blockAt s.callEntry.mem (s₀.gpr .rdi + BitVec.ofNat 64 e) =
        blockAt s.mem (s₀.gpr .rdi + BitVec.ofNat 64 e) :=
      blockAt_fr fE fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact cb_disj hp he
    have eH : blockAt s.callEntry.mem (s₀.gpr .rsi + BitVec.ofNat 64 256) =
        blockAt s.mem (s₀.gpr .rsi + BitVec.ofNat 64 256) :=
      blockAt_fr fE (dE (d := 256) (by decide))
    have e1 : (BitVec.ofNat 64 1).toNat = 1 := rfl
    have xz : ∀ x : Block, x ^^^ 0 = x := fun x => BitVec.xor_zero
    rw [e1, blocksAt_one_eq, eZ, eY, Spec.Gcm.ghashFrom, List.foldl_cons, List.foldl_nil, xz, eH] at hpost
    refine ⟨hpost, ?_, hcs, hkeep _ G.rsi, hkeep _ G.r8,
      hrd₂, hwr₂⟩
    rw [hrsp] at hf
    exact hf.mono (by simp)

/-- `mulH`: the block at `rsi`, at `C + e`, multiplied by the copy of `H`. -/
theorem mulH_ok (G : Gh) {s₀ : State} (hp : innerX86_64.pre s₀) {s : State} {e : Nat} (he : e + 16 ≤ 1024)
    (hrsi : s.gpr .rsi = s₀.gpr .rdi + BitVec.ofNat 64 e) (hr8 : s.gpr .r8 = s₀.gpr .rsi)
    (hrsp : s.gpr .rsp = s₀.gpr .rsp) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hz : blockAt s.mem (s₀.gpr .rsi + BitVec.ofNat 64 272) = 0) :
    WP isa (mulH G.g.fn.name G.g.fn.code) s fun s' =>
      blockAt s'.mem (s₀.gpr .rdi + BitVec.ofNat 64 e) =
        Spec.Gcm.mul (blockAt s.mem (s₀.gpr .rdi + BitVec.ofNat 64 e))
          (blockAt s.mem (s₀.gpr .rsi + BitVec.ofNat 64 256)) ∧
      Frame [⟨s₀.gpr .rdi + BitVec.ofNat 64 e, 16⟩, ⟨s₀.gpr .rsi, 256⟩, below (s₀.gpr .rsp) 8] s.mem s'.mem ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.gpr .rsi = s.gpr .rsi ∧ s'.gpr .r8 = s.gpr .r8 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.seq ?_
  apply WP.of_runBlock
  simp only [hO, zO]
  prun [hr8]
  refine WP.mono (call_ok G hp he ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) fun s' ⟨h1, h2, h3, h4, h5, h6, h7⟩ => ?_
  all_goals try simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_setReg, RegUpd.mem_arithFlags,
    RegUpd.rd_setReg, RegUpd.rd_arithFlags, RegUpd.wr_setReg, RegUpd.wr_arithFlags, reduceCtorEq, ↓reduceIte, hr8,
    hrsi, hrsp, hrd, hwr, hz] at *
  · decide
  · refine ⟨h1, h2, fun r hr => ?_, h4, h5, h6, h7⟩
    rw [h3 r hr]
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [reduceCtorEq, ↓reduceIte]

/-- The regions a step writes are within `fr`. -/
theorem step_sub {s₀ : State} {a b : Nat} (ha : 256 ≤ a) (ha' : a + 16 ≤ 1024) (hb : 256 ≤ b)
    (hb' : b + 16 ≤ 1024) :
    ∀ r ∈ ([⟨s₀.gpr .rdi + BitVec.ofNat 64 a, 16⟩, ⟨s₀.gpr .rdi + BitVec.ofNat 64 b, 16⟩,
      ⟨s₀.gpr .rsi, 256⟩, below (s₀.gpr .rsp) 8] : List Region), ∃ r' ∈ fr s₀, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., Offset.sub _ ha (by omega)⟩
  · exact ⟨_, List.mem_cons_self .., Offset.sub _ hb (by omega)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), fun _ h => h⟩

/-- 16 bytes of the context outside two slots and the scratch buffer. -/
theorem c_disj {s₀ : State} (hp : innerX86_64.pre s₀) {a b c : Nat} (hc : c + 16 ≤ 1024)
    (hca : c + 16 ≤ a ∨ a + 16 ≤ c) (hcb : c + 16 ≤ b ∨ b + 16 ≤ c) (ha : a + 16 ≤ 1024)
    (hb : b + 16 ≤ 1024) :
    ∀ r ∈ ([⟨s₀.gpr .rdi + BitVec.ofNat 64 a, 16⟩, ⟨s₀.gpr .rdi + BitVec.ofNat 64 b, 16⟩,
      ⟨s₀.gpr .rsi, 256⟩, below (s₀.gpr .rsp) 8] : List Region),
      (⟨s₀.gpr .rdi + BitVec.ofNat 64 c, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Offset.disjoint _ hca (by omega) (by omega)
  · exact Offset.disjoint _ hcb (by omega) (by omega)
  · have := cs_disj hp (d := c) (n := 16) (e := 0) (k := 256) hc (by decide)
    rwa [add_ofNat_zero] at this
  · exact cb_disj hp hc

/-- Bytes of the scratch buffer from 256 on, outside two slots, `vg_ghash`'s
working space and the stack below. -/
theorem s_disj {s₀ : State} (hp : innerX86_64.pre s₀) {a b e k : Nat} (he : 256 ≤ e) (hek : e + k ≤ 312)
    (ha : a + 16 ≤ 1024) (hb : b + 16 ≤ 1024) :
    ∀ r ∈ ([⟨s₀.gpr .rdi + BitVec.ofNat 64 a, 16⟩, ⟨s₀.gpr .rdi + BitVec.ofNat 64 b, 16⟩,
      ⟨s₀.gpr .rsi, 256⟩, below (s₀.gpr .rsp) 8] : List Region),
      (⟨s₀.gpr .rsi + BitVec.ofNat 64 e, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (cs_disj hp ha hek).symm
  · exact (cs_disj hp hb hek).symm
  · exact s_hi_disj s₀ he hek
  · exact sb_disj hp hek

/-- `rsi` moved `d` bytes on. -/
theorem add_ok {s : State} {d : Int} (hsx : (BitVec.ofInt 32 d).signExtend 64 = BitVec.ofInt 64 d) :
    WP isa (.block [.alu .add .rsi (.imm (BitVec.ofInt 32 d))]) s fun s' =>
      s'.gpr .rsi = s.gpr .rsi + BitVec.ofInt 64 d ∧ (∀ r, r ≠ .rsi → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  prun [hsx]
  intro r hr
  simp only [hr, ↓reduceIte]

/-- Step `n`: `Hⁿ⁺¹` from `Hⁿ`, which is then prepared in place. -/
theorem step_ok (G : Gh) {s₀ : State} (hp : innerX86_64.pre s₀) {n : Nat} {d : Int} (hn1 : 1 ≤ n) (hn : n + 1 ≤ 48)
    (hd : (slot (n + 1) : Int) = slot n + d) (hsx : (BitVec.ofInt 32 d).signExtend 64 = BitVec.ofInt 64 d)
    {s : State} (hs : St s₀ n s) : WP isa (step G.g.fn.name G.g.fn.code d) s (St s₀ (n + 1)) := by
  have lo := slot_lo hn1
  have hi := slot_hi (n := n) (by omega)
  have lo' := slot_lo (n := n + 1) (by omega)
  have hi' := slot_hi hn
  have sep := slot_sep (j := n) (k := n + 1) (by omega)
  have hQ : s₀.gpr .rdi + BitVec.ofNat 64 (slot n) + BitVec.ofInt 64 d =
      s₀.gpr .rdi + BitVec.ofNat 64 (slot (n + 1)) := shift_eq _ hd
  have hQ8 : s₀.gpr .rdi + BitVec.ofNat 64 (slot n) + BitVec.ofInt 64 (d + 8) =
      s₀.gpr .rdi + BitVec.ofNat 64 (slot (n + 1)) + BitVec.ofNat 64 8 := by
    rw [Offset.add_add, shift_eq _ (b := slot (n + 1) + 8) (by push_cast; omega)]
  have p8 : s₀.gpr .rdi + BitVec.ofNat 64 (slot n) + BitVec.ofNat 64 8 =
      s₀.gpr .rdi + BitVec.ofNat 64 (slot n + 8) := Offset.add_add ..
  have q8 : s₀.gpr .rdi + BitVec.ofNat 64 (slot (n + 1)) + BitVec.ofNat 64 8 =
      s₀.gpr .rdi + BitVec.ofNat 64 (slot (n + 1) + 8) := Offset.add_add ..
  have hPQ := slots_disj s₀ (j := n) (k := n + 1) (by omega) hn (by omega)
  have wP : InRegions s.wr (s₀.gpr .rdi + BitVec.ofNat 64 (slot n)) 8 := by
    rw [hs.wr]; exact inC hp (by omega)
  have wP8 : InRegions s.wr (s₀.gpr .rdi + BitVec.ofNat 64 (slot n) + BitVec.ofNat 64 8) 8 := by
    rw [hs.wr, p8]; exact inC hp (by omega)
  have wQ : InRegions s.wr (s₀.gpr .rdi + BitVec.ofNat 64 (slot (n + 1))) 8 := by
    rw [hs.wr]; exact inC hp (by omega)
  have wQ8 : InRegions s.wr (s₀.gpr .rdi + BitVec.ofNat 64 (slot (n + 1)) + BitVec.ofNat 64 8) 8 := by
    rw [hs.wr, q8]; exact inC hp (by omega)
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copy_ok hs.rsi hQ hQ8 hPQ (inApp wP) (inApp wP8) wQ wQ8) fun s₁ ⟨c1, cf, cg, crd, cwr⟩ => ?_
  refine WP.mono (pp_ok (P := s₀.gpr .rdi + BitVec.ofNat 64 (slot n)) (by rw [cg _ (by decide), hs.rsi]) (by rw [cwr]; exact wP) (by rw [cwr]; exact wP8))
    fun s₂ ⟨p1, pf, pg, prd, pwr⟩ => ?_
  have g2 : ∀ r, r ∉ [Reg.rdi, .rax, .r11, .r12, .r13, .r14] → s₂.gpr r = s.gpr r := fun r hr =>
    (pg r hr).trans (cg r (by intro h; subst h; exact hr (by simp)))
  refine WP.mono (add_ok hsx) fun s₃ ⟨a1, a2, a3, a4, a5⟩ => ?_
  rw [g2 .rsi (by decide), hs.rsi, hQ] at a1
  have fP : ∀ r ∈ [(⟨s₀.gpr .rdi + BitVec.ofNat 64 (slot n), 16⟩ : Region)],
      (⟨s₀.gpr .rdi + BitVec.ofNat 64 (slot (n + 1)), 16⟩ : Region).Disjoint r := by
    intro r hr; rw [List.mem_singleton] at hr; subst hr; exact hPQ.symm
  have y2 : blockAt s₂.mem (s₀.gpr .rdi + BitVec.ofNat 64 (slot (n + 1))) = hpow (Hk s₀) n := by
    rw [blockAt_fr pf fP, c1, hs.y]
  have h2 : blockAt s₂.mem (s₀.gpr .rsi + BitVec.ofNat 64 256) = Hk s₀ := by
    rw [← hs.h]
    exact blockAt_fr ((cf.mono (by simp)).trans (pf.mono (by simp)) :
      Frame [⟨s₀.gpr .rdi + BitVec.ofNat 64 (slot n), 16⟩, ⟨s₀.gpr .rdi + BitVec.ofNat 64 (slot (n + 1)), 16⟩,
        ⟨s₀.gpr .rsi, 256⟩, below (s₀.gpr .rsp) 8] s.mem s₂.mem)
      (s_disj hp (by decide) (by decide) (by omega) (by omega))
  have z2 : blockAt s₂.mem (s₀.gpr .rsi + BitVec.ofNat 64 272) = 0 := by
    rw [← hs.z]
    exact blockAt_fr ((cf.mono (by simp)).trans (pf.mono (by simp)) :
      Frame [⟨s₀.gpr .rdi + BitVec.ofNat 64 (slot n), 16⟩, ⟨s₀.gpr .rdi + BitVec.ofNat 64 (slot (n + 1)), 16⟩,
        ⟨s₀.gpr .rsi, 256⟩, below (s₀.gpr .rsp) 8] s.mem s₂.mem)
      (s_disj hp (by decide) (by decide) (by omega) (by omega))
  have g3 : ∀ r, r ∉ [Reg.rsi, .rdi, .rax, .r11, .r12, .r13, .r14] → s₃.gpr r = s.gpr r := fun r hr =>
    (a2 r (by intro h; subst h; exact hr (by simp))).trans (g2 r (by intro h; exact hr (by simp_all)))
  have r8₃ : s₃.gpr .r8 = s₀.gpr .rsi := (g3 .r8 (by decide)).trans hs.r8
  have rsp₃ : s₃.gpr .rsp = s₀.gpr .rsp := (g3 .rsp (by decide)).trans hs.rsp
  have rd₃ : s₃.rd = s₀.rd := a4.trans (prd.trans (crd.trans hs.rd))
  have wr₃ : s₃.wr = s₀.wr := a5.trans (pwr.trans (cwr.trans hs.wr))
  refine WP.mono (mulH_ok G hp hi' a1 r8₃ rsp₃ rd₃ wr₃ (by rw [a3]; exact z2))
    fun s' ⟨m1, m2, m3, m4, m5, m6, m7⟩ => ?_
  rw [a3] at m1 m2
  have fstep : Frame [⟨s₀.gpr .rdi + BitVec.ofNat 64 (slot n), 16⟩,
      ⟨s₀.gpr .rdi + BitVec.ofNat 64 (slot (n + 1)), 16⟩, ⟨s₀.gpr .rsi, 256⟩, below (s₀.gpr .rsp) 8]
      s.mem s'.mem :=
    ((cf.mono (by simp)).trans (pf.mono (by simp))).trans (m2.mono (by simp))
  have sD : ∀ {e k : Nat}, 256 ≤ e → e + k ≤ 312 → ∀ r ∈ ([⟨s₀.gpr .rdi + BitVec.ofNat 64 (slot n), 16⟩,
      ⟨s₀.gpr .rdi + BitVec.ofNat 64 (slot (n + 1)), 16⟩, ⟨s₀.gpr .rsi, 256⟩, below (s₀.gpr .rsp) 8] : List Region),
      (⟨s₀.gpr .rsi + BitVec.ofNat 64 e, k⟩ : Region).Disjoint r := fun he hek => s_disj hp he hek hi hi'
  refine ⟨m4.trans a1, m5.trans r8₃, (m3 .rsp (by decide)).trans rsp₃, fun r hr => ?_, m6.trans rd₃,
    m7.trans wr₃, hs.frame.trans (fstep.sub (step_sub lo hi lo' hi')), ?_, ?_, ?_, ?_, ?_, ?_,
    fun j hj1 hjn => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      exact (m3 _ (by decide)).trans ((g3 _ (by decide)).trans (hs.keep _ (by simp)))
  · exact (fstep.readW (Region.contains_self _ _) (sD (k := 64 / 8) (by decide) (by decide)) (by decide)).trans hs.sv12
  · exact (fstep.readW (Region.contains_self _ _) (sD (k := 64 / 8) (by decide) (by decide)) (by decide)).trans hs.sv13
  · exact (fstep.readW (Region.contains_self _ _) (sD (k := 64 / 8) (by decide) (by decide)) (by decide)).trans hs.sv14
  · exact (blockAt_fr fstep (sD (e := 256) (by decide) (by decide))).trans hs.h
  · exact (blockAt_fr fstep (sD (e := 272) (by decide) (by decide))).trans hs.z
  · rw [m1, y2, h2]; rfl
  · rcases (by omega : j = n ∨ j < n) with rfl | hjn'
    · have dP : ∀ r ∈ ([⟨s₀.gpr .rdi + BitVec.ofNat 64 (slot (j + 1)), 16⟩, ⟨s₀.gpr .rsi, 256⟩,
          below (s₀.gpr .rsp) 8] : List Region),
          (⟨s₀.gpr .rdi + BitVec.ofNat 64 (slot j), 128 / 8⟩ : Region).Disjoint r := by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hPQ
        · have := cs_disj hp (d := slot j) (n := 16) (e := 0) (k := 256) hi (by decide)
          rwa [add_ofNat_zero] at this
        · exact cb_disj hp hi
      rw [m2.readW (Region.contains_self _ _) dP (by decide), p1,
        blockAt_fr cf (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hPQ), hs.y]
    · have sj := slot_lo hj1
      have hj' := slot_hi (n := j) (by omega)
      rw [fstep.readW (Region.contains_self _ (128 / 8))
        (c_disj hp hj' (slot_sep (by omega)) (slot_sep (by omega)) hi hi') (by decide)]
      exact hs.st j hj1 hjn' 

theorem hpow_one (H : Block) : hpow H 1 = H :=
  Poly.φ_inj (by rw [Poly.φ_hpow, pow_one])

theorem ctxH_words (m : Mem) (C : Addr) :
    Spec.Gcm.ctxH m C = X86_64.bswap64 (m.readW (C + BitVec.ofNat 64 240) 64) ++
      X86_64.bswap64 (m.readW (C + BitVec.ofNat 64 248) 64) :=
  blockAt_words m C 240

/-- The set-up: `H¹ = H` in its slot, its copy and the zero block in the
scratch buffer, and the registers saved. -/
theorem setup_ok {s₀ : State} (hp : innerX86_64.pre s₀) : WP isa (.block setup) s₀ (St s₀ 1) := by
  have hCS := hp.2.2.2.2.1
  have l0 := inC' hp (d := 240) (n := 8) (by decide)
  have l8 := inC' hp (d := 248) (n := 8) (by decide)
  have w0 := inS hp (d := 288) (n := 8) (by decide)
  have w1 := inS hp (d := 296) (n := 8) (by decide)
  have w2 := inS hp (d := 304) (n := 8) (by decide)
  have w3 := inS hp (d := 256) (n := 8) (by decide)
  have w4 := inS hp (d := 264) (n := 8) (by decide)
  have w5 := inC hp (d := 272) (n := 8) (by decide)
  have w6 := inC hp (d := 280) (n := 8) (by decide)
  have w7 := inS hp (d := 272) (n := 8) (by decide)
  have w8 := inS hp (d := 280) (n := 8) (by decide)
  have z0 : (0 : BitVec 32).signExtend 64 = 0 := by decide
  have i272 : (272 : BitVec 32).signExtend 64 = BitVec.ofNat 64 272 := by decide
  have bz : X86_64.bswap64 0 = 0 := by decide
  have s1 : slot 1 = 272 := rfl
  apply WP.of_runBlock
  simp only [setup, save, saved, hO, zO, savedO, List.map, List.cons_append, List.nil_append]
  prun [l0, l8, w0, w1, w2, w3, w4, w5, w6, w7, w8, z0, i272]
  have sC : ∀ {e : Nat}, e + 8 ≤ 312 → (⟨s₀.gpr .rsi, 312⟩ : Region).Contains (s₀.gpr .rsi + BitVec.ofNat 64 e) (64 / 8) :=
    fun he => Offset.contains_base _ he (by omega)
  have cC : ∀ {e : Nat}, 256 ≤ e → e + 8 ≤ 1024 →
      (⟨s₀.gpr .rdi + BitVec.ofNat 64 256, 768⟩ : Region).Contains (s₀.gpr .rdi + BitVec.ofNat 64 e) (64 / 8) :=
    fun h1 h2 => Offset.contains _ h1 (by omega) (by omega)
  have mS : (⟨s₀.gpr .rsi, 312⟩ : Region) ∈ fr s₀ := List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have mC : (⟨s₀.gpr .rdi + BitVec.ofNat 64 256, 768⟩ : Region) ∈ fr s₀ := List.mem_cons_self ..
  refine ⟨?_, rfl, rfl, fun r hr => ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j h1 h2 => absurd h2 (by omega)⟩
  all_goals simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_setReg, RegUpd.mem_arithFlags,
    reduceCtorEq, ↓reduceIte]
  · rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [reduceCtorEq, ↓reduceIte]
  · exact (((((((((Frame.refl _ _).writeW mS _ (sC (e := 288) (by decide))).writeW mS _
      (sC (e := 296) (by decide))).writeW mS _ (sC (e := 304) (by decide))).writeW mS _
      (sC (e := 256) (by decide))).writeW mS _ (sC (e := 264) (by decide))).writeW mC _
      (cC (e := 272) (by decide) (by decide))).writeW mC _ (cC (e := 280) (by decide) (by decide))).writeW mS _
      (sC (e := 272) (by decide))).writeW mS _ (sC (e := 280) (by decide))
  all_goals simp (disch := decide) only [blockAt_words, Nat.reduceAdd, s1, hpow_one, ctxH_words,
    rw_off, rw_disj hCS, rw_disj hCS.symm, Mem.readW_writeW_self64, bz]
  decide

/-- Pair `k`: steps `2k + 1` and `2k + 2`. -/
theorem pair_ok (G : Gh) {s₀ : State} (hp : innerX86_64.pre s₀) {k : Nat} (hk : k < 23) {s : State}
    (hs : St s₀ (2 * k + 1) s) : WP isa (pair G.g.fn.name G.g.fn.code) s (St s₀ (2 * (k + 1) + 1)) := by
  have d1 : (slot (2 * k + 1 + 1) : Int) = slot (2 * k + 1) + (-16) := by unfold slot; split <;> split <;> omega
  have d2 : (slot (2 * k + 2 + 1) : Int) = slot (2 * k + 2) + 48 := by unfold slot; split <;> split <;> omega
  refine WP.seq (WP.mono (step_ok G hp (by omega) (by omega) d1 (by decide) hs) fun s' h => ?_)
  rw [show 2 * (k + 1) + 1 = 2 * k + 2 + 1 by omega]
  exact step_ok G hp (by omega) (by omega) d2 (by decide) h

theorem pairs_ok (G : Gh) {s₀ : State} (hp : innerX86_64.pre s₀) (k : Nat) (hk : k ≤ 23) {s : State}
    (hs : St s₀ 1 s) : WP isa (pairs G.g.fn.name G.g.fn.code k) s (St s₀ (2 * k + 1)) := by
  induction k with
  | zero => exact WP.block_nil hs
  | succ k ih => exact WP.seq (WP.mono (ih (by omega)) fun s' h => pair_ok G hp (by omega) h)

/-- The last power prepared, and the registers restored. -/
theorem final_ok {s₀ : State} (hp : innerX86_64.pre s₀) {s : State} (hs : St s₀ 48 s) :
    WP isa (.block (pp ++ restore)) s fun s' => gprPreserved s₀ s' ∧ innerX86_64.post s₀ s' := by
  have hi := slot_hi (n := 48) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pp_ok hs.rsi (by rw [hs.wr]; exact inC hp (by omega))
    (by rw [hs.wr, Offset.add_add]; exact inC hp (by omega))) fun s₁ ⟨p1, pf, pg, prd, pwr⟩ => ?_
  have r8 : s₁.gpr .r8 = s₀.gpr .rsi := (pg .r8 (by decide)).trans hs.r8
  have fr₁ : Frame (fr s₀) s₀.mem s₁.mem :=
    hs.frame.trans (pf.sub fun r hr => ⟨_, List.mem_cons_self .., by
      rw [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (slot_lo (by decide)) (by omega)⟩)
  have dP : ∀ {e : Nat}, 256 ≤ e → e + 8 ≤ 312 → ∀ r ∈ [(⟨s₀.gpr .rdi + BitVec.ofNat 64 (slot 48), 16⟩ : Region)],
      (⟨s₀.gpr .rsi + BitVec.ofNat 64 e, 64 / 8⟩ : Region).Disjoint r := fun _ he r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact (cs_disj hp hi he).symm
  have v12 : s₁.mem.readW (s₀.gpr .rsi + BitVec.ofNat 64 288) 64 = s₀.gpr .r12 :=
    (pf.readW (Region.contains_self _ _) (dP (by decide) (by decide)) (by decide)).trans hs.sv12
  have v13 : s₁.mem.readW (s₀.gpr .rsi + BitVec.ofNat 64 296) 64 = s₀.gpr .r13 :=
    (pf.readW (Region.contains_self _ _) (dP (by decide) (by decide)) (by decide)).trans hs.sv13
  have v14 : s₁.mem.readW (s₀.gpr .rsi + BitVec.ofNat 64 304) 64 = s₀.gpr .r14 :=
    (pf.readW (Region.contains_self _ _) (dP (by decide) (by decide)) (by decide)).trans hs.sv14
  have i12 : InRegions (s₁.rd ++ s₁.wr) (s₀.gpr .rsi + BitVec.ofNat 64 288) 8 := by
    rw [prd, pwr, hs.rd, hs.wr]; exact inS' hp (by decide)
  have i13 : InRegions (s₁.rd ++ s₁.wr) (s₀.gpr .rsi + BitVec.ofNat 64 296) 8 := by
    rw [prd, pwr, hs.rd, hs.wr]; exact inS' hp (by decide)
  have i14 : InRegions (s₁.rd ++ s₁.wr) (s₀.gpr .rsi + BitVec.ofNat 64 304) 8 := by
    rw [prd, pwr, hs.rd, hs.wr]; exact inS' hp (by decide)
  apply WP.of_runBlock
  simp only [restore, saved, savedO, List.map]
  prun [r8, i12, i13, i14, v12, v13, v14]
  -- the context's first 256 bytes, and so `H`, are kept
  have d256 : ∀ r ∈ fr s₀, (⟨s₀.gpr .rdi, 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.base_disjoint _ (by decide) (by decide)
    · exact hp.2.2.2.2.1.sub_left (Region.sub_prefix (by decide))
    · exact (hp.2.2.2.2.2.2.2.1.sub_right (Region.sub_prefix (by decide))).symm
  have hH : Spec.Gcm.ctxH s₁.mem (s₀.gpr .rdi) = Hk s₀ := by
    simp only [Hk, Spec.Gcm.ctxH]
    exact blockAt_fr fr₁ fun r hr => (d256 r hr).sub_left (Offset.sub_base _ (by decide))
  have stored : ∀ j, 1 ≤ j → j ≤ 48 →
      s₁.mem.readW (s₀.gpr .rdi + BitVec.ofNat 64 (slot j)) 128 = preparedPower (hpow (Hk s₀) j) := by
    intro j h1 h2
    rcases (by omega : j = 48 ∨ j < 48) with rfl | hj
    · rw [p1, hs.y]
    · have := slot_lo h1
      have := slot_hi (n := j) (by omega)
      rw [pf.readW (Region.contains_self _ (128 / 8)) (fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (slot_sep (by omega)) (by omega) (by omega)) (by decide)]
      exact hs.st j h1 hj
  refine ⟨⟨fun r hr => ?_, ?_⟩, bytesAt_fr fr₁ d256 (by decide), fun k hk => ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [RegUpd.gpr_setReg, reduceCtorEq, ↓reduceIte]
    · exact (pg _ (by decide)).trans (hs.keep _ (by simp))
    · exact (pg _ (by decide)).trans (hs.keep _ (by simp))
    · exact (pg _ (by decide)).trans hs.rsp
    · exact (pg _ (by decide)).trans (hs.keep _ (by simp))
  · simp only [RegUpd.mem_setReg]
    refine fr₁.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.2.2.2.2.2.1.sub_right (Offset.sub_base _ (by decide))
    · exact hp.2.2.2.2.2.2.1
    · exact Offset.base_disjoint_below _ (by decide)
  · simp only [RegUpd.mem_setReg]
    rw [hH]
    have e2 : slot (2 * k + 2) = 256 + 32 * k := by unfold slot; split <;> omega
    have e1 : slot (2 * k + 1) = 272 + 32 * k := by unfold slot; split <;> omega
    exact ⟨e2 ▸ stored (2 * k + 2) (by omega) (by omega), e1 ▸ stored (2 * k + 1) (by omega) (by omega)⟩

theorem inner_correct (G : Gh) (s : State) (hs : innerX86_64.pre s) :
    ∃ t s', Exec isa (inner G.g.fn.name G.g.fn.code) s t s' ∧ abiPreserved s s' ∧ innerX86_64.post s s' := by
  have hw : WP isa (inner G.g.fn.name G.g.fn.code) s fun s' => gprPreserved s s' ∧ innerX86_64.post s s' :=
    WP.seq (WP.mono (setup_ok hs) fun s₁ h₁ => WP.seq (WP.mono (pairs_ok G hs 23 (by decide) h₁) fun s₂ h₂ =>
      WP.seq (WP.mono (step_ok G hs (n := 47) (d := -16) (by decide) (by decide) (by decide) (by decide) h₂)
        fun s₃ h₃ => final_ok hs h₃)))
  obtain ⟨t, s', he, h⟩ := hw
  exact ⟨t, s', he, abiPreserved_of_exec G.mxcsr he h.1, h.2⟩

/-- A state meeting `innerContract`'s precondition. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x10000 | .rsi => 0x20000 | .rsp => 0x50000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x10000, 1024⟩, ⟨0x20000, 312⟩]

theorem inner_verified (G : Gh) : Verified X86_64.target (inner G.g.fn.name G.g.fn.code) innerContract :=
  Verified.of_correct (inner_correct G) G.ct (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Gcm.prepareSig,
      Spec.Gcm.preparePost, innerX86_64, X86_64.abi, X86_64.argRegs] [satState] using satState)

/-- `preparePost` reads the memory on return only within the context. -/
theorem postOut_local : ∀ vs m m₁ m₂ r, vs.length = (Spec.Gcm.prepareSig.words X86_64.abi.ptrBits).length →
    (∀ b ∈ Sig.bufs Spec.Gcm.prepareSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.Gcm.prepareSig.words X86_64.abi.ptrBits) (Spec.Gcm.preparePost X86_64.abi.ptrBits) vs m m₁ r →
      Curry.apply (Spec.Gcm.prepareSig.words X86_64.abi.ptrBits) (Spec.Gcm.preparePost X86_64.abi.ptrBits)
        vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨C, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 0) hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [Spec.Gcm.prepareSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
    Elem.size] at hb
  have hs : ∀ i < 1024, m₂ (C + BitVec.ofNat 64 i) = m₁ (C + BitVec.ofNat 64 i) := fun i hi =>
    (hb _ (Offset.contains_base _ (by omega) (by omega))).symm
  have rw128 : ∀ {d : Nat}, d + 16 ≤ 1024 → m₂.readW (C + BitVec.ofNat 64 d) 128 = m₁.readW (C + BitVec.ofNat 64 d) 128 :=
    fun {d} hd => Mem.readW_congr fun i hi => by
      have : i < 16 := hi
      rw [Offset.add_add]; exact hs (d + i) (by omega)
  have hbytes : ∀ {d n : Nat}, d + n ≤ 1024 →
      Spec.Aes.bytesAt m₂ (C + BitVec.ofNat 64 d) n = Spec.Aes.bytesAt m₁ (C + BitVec.ofNat 64 d) n :=
    fun hd => by
      simp only [Spec.Aes.bytesAt]
      apply List.map_congr_left
      intro i hi
      have := List.mem_range.mp hi
      rw [Offset.add_add]; exact hs _ (by omega)
  change Curry.apply [ArgWord.addr] (Spec.Gcm.preparePost 64) _ m m₁ r at h
  change Curry.apply [ArgWord.addr] (Spec.Gcm.preparePost 64) _ m m₂ r
  dsimp only [Curry.apply, Spec.Gcm.preparePost, ArgWord.ofRaw] at h ⊢
  obtain ⟨h1, h2⟩ := h
  have hH : Spec.Gcm.ctxH m₂ C = Spec.Gcm.ctxH m₁ C := by
    simp only [Spec.Gcm.ctxH, Spec.Gcm.blockAt]
    exact congrArg Spec.Gcm.ofBytes (hbytes (d := 240) (n := 16) (by decide))
  refine ⟨?_, fun k hk => ?_⟩
  · rw [← h1]
    have := hbytes (d := 0) (n := 256) (by decide)
    rwa [add_ofNat_zero] at this
  · rw [hH, rw128 (by omega), rw128 (by omega)]
    exact h2 k hk

/-- `vg_aes_gcm_prepare` in the baseline ISA. -/
theorem prepare_verified (G : Gh) :
    Verified X86_64.target (prepare G.g.fn.name G.g.fn.code)
      (Spec.Gcm.prepareContract X86_64.abi (8 + (8 + scratchBytes))) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Gcm.prepareSig) (nm := "scratch") (e := .u64) (n := 39)
    (post := Spec.Gcm.preparePost X86_64.abi.ptrBits) (wa := true) (stack := 8) (bytes := 8 + scratchBytes)
    (inner_verified G) (by decide) (by decide) (by decide) G.spSafe G.depth
    (by decide) postOut_local
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-- `prepare` changes the stack pointer only by its frame and calls. -/
theorem prepare_spSafe (G : Gh) : (prepare G.g.fn.name G.g.fn.code).all (fun i => !isa.writesSp i) = true := by
  unfold prepare Impl.StackScratch.X86_64.withStackScratchWiped
  refine X86_64.withStackScratch_spSafe_of ?_
  simp only [Code.all, G.spSafe, Bool.true_and]
  decide

end VG.Proof.Gcm.X86_64.PrepareCall
