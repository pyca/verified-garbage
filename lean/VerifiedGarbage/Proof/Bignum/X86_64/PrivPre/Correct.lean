module

public import VerifiedGarbage.Proof.Bignum.X86_64.PrivPre.Out
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Bignum.X86_64.PubMain
import VerifiedGarbage.Proof.Bignum.X86_64.PcCode
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Bignum.X86_64.CrtBack
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtFront
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Bignum.CrtResult
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Rsa.X86_64.PrivPre
public import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtContract
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.MlKem.X86_64.Wp

/-! ### `Bignum.X86_64.PrivPre.Head`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86_64.PrivPre.Contract`, which this module and modules that import it used -/

section

/-!
# `vg_rsa_private_precompute` on x86-64: the contract on the registers

`ppContract` states the shared contract on the registers and the stack
(`pp_implies`), with 8 bytes of stack, the return address of the calls of
Montgomery multiplication.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.PrivPre

open VG VG.X86_64

/-- `vg_rsa_private_precompute(pre = rdi, pre_len = rsi, n = rdx,
n_len = rcx, p = r8, p_len = r9, q = [rsp + 8], q_len = [rsp + 16],
scratch = [rsp + 24], scratch_len = [rsp + 32])`. -/
def ppContract : Contract isa where
  pre s :=
    let pre : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat * 8⟩
    let n : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let p : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let q : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
    let scr : Region := ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 32⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    (s.gpr .rsp).toNat + 40 ≤ 2 ^ 64 ∧
      s.rd = [n, p, q, args] ∧ s.wr = [pre, scr] ∧
      pre.Disjoint n ∧ pre.Disjoint p ∧ pre.Disjoint q ∧ pre.Disjoint scr ∧ pre.Disjoint args ∧
      n.Disjoint scr ∧ p.Disjoint scr ∧ q.Disjoint scr ∧ scr.Disjoint args ∧
      ret.Disjoint pre ∧ ret.Disjoint n ∧ ret.Disjoint p ∧ ret.Disjoint q ∧ ret.Disjoint scr ∧
      ret.Disjoint args ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat * 8 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
      (stackArg s 2).toNat + (stackArg s 3).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .rcx).toNat ∧ 1 ≤ (s.gpr .r9).toNat ∧ (s.gpr .r9).toNat < (s.gpr .rcx).toNat ∧
      1 ≤ (stackArg s 1).toNat ∧ (stackArg s 1).toNat < (s.gpr .rcx).toNat ∧
      (s.gpr .rsi).toNat = Spec.Rsa.privatePrecomputedWords (s.gpr .rcx).toNat (s.gpr .r9).toNat
        (stackArg s 1).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .rcx).toNat ≤ (stackArg s 3).toNat
  post s s' :=
    match Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat) with
    | some ws => (s'.gpr .rax).setWidth 32 = 1 ∧ Spec.Rsa.wordsAt s'.mem (s.gpr .rdi) (s.gpr .rsi).toNat = ws
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧
      Spec.Rsa.wordsAt s'.mem (s.gpr .rdi) (s.gpr .rsi).toNat = List.replicate (s.gpr .rsi).toNat 0
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
      stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2 ∧
      stackArg s₁ 3 = stackArg s₂ 3 ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdx) (s₁.gpr .rcx).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdx) (s₂.gpr .rcx).toNat

theorem stackArgs_four (s : State) :
    List.map (stackArg s) (List.range 4) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3] := rfl

/-- A state meeting `ppContract.pre`: a 512-bit modulus, one-byte primes,
and the stack arguments at `0x6008`. -/
def ppSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 20 | .rdx => 0x2000 | .rcx => 64 | .r8 => 0x3000 | .r9 => 1
    | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := bif Nat.beq a.toNat 0x6009 then 0x40 else bif Nat.beq a.toNat 0x6010 then 1
    else bif Nat.beq a.toNat 0x6019 then 0x80 else bif Nat.beq a.toNat 0x6020 then 0x20
    else bif Nat.beq a.toNat 0x6021 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 1⟩, ⟨0x6008, 32⟩]
  wr := [⟨0x1000, 160⟩, ⟨0x8000, 8448⟩]

theorem pp_implies : ppContract.Implies (Spec.Rsa.privatePrecomputeContract abi 8) where
  pre := by
    intro s h
    sig_pre [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, ppContract, stackArgs_four, List.append_eq, List.range, List.range.loop] at h
    sig_split h
    sig_reduce [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, ppContract, stackArgs_four, List.append_eq, List.range, List.range.loop]
    sig_and_intros
    sig_close
  post := by sig_implies_post [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, ppContract, stackArgs_four, List.append_eq, List.range, List.range.loop]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, ppContract, stackArgs_four, List.append_eq, List.range, List.range.loop] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3⟩ := h
    refine ⟨?_, a0, a1, a2, a3, (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, ppContract, stackArgs_four, List.append_eq] [ppSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using ppSatState

end VG.Proof.Bignum.X86_64.PrivPre

end

end

/-!
# `vg_rsa_private_precompute` on x86-64: up to `vg_rsa_private_crt`'s code

What the code uses of `ppContract.pre` (`ppCtx_of`), and `entry`, which
saves the callee-saved registers and the arguments in the header of the
working space and leaves its base in `rdi` (`entry_ok`). After `entry`, `zeroPre` writes zeros to `pre` (`zeroPre_ok`), and `n` and
`k` are reloaded (`head_ok`); from there, with `pre` read as the input and
as `qInv` (zeros) and `p`, `q` as the exponents, the state is one that
`vg_rsa_private_crt`'s code starts from (`ppPre_of`, `CrtPre`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.PrivPre

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Crt VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64
open VG.WriteBytes (writeW8_apply)
/-! ## The precondition, as the code uses it -/

/-- What the code uses of its contract's precondition, for the working
space (stack argument 2) of `(stackArg s 3).toNat * 8` bytes. -/
structure PPCtx (s : State) : Prop where
  hk1 : 64 ≤ (s.gpr .rcx).toNat
  hk2 : (s.gpr .rcx).toNat ≤ 1024
  hpl1 : 1 ≤ (s.gpr .r9).toNat
  hpl2 : (s.gpr .r9).toNat < (s.gpr .rcx).toNat
  hql1 : 1 ≤ (stackArg s 1).toNat
  hql2 : (stackArg s 1).toNat < (s.gpr .rcx).toNat
  hL : (s.gpr .rsi).toNat = Spec.Rsa.privatePrecomputedWords (s.gpr .rcx).toNat (s.gpr .r9).toNat
    (stackArg s 1).toNat
  hZ : 128 * (s.gpr .rcx).toNat + 256 ≤ (stackArg s 3).toNat * 8
  hs : Scr s (stackArg s 2) ((stackArg s 3).toNat * 8)
  ha : ∀ j < 4, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8
  hnb : Src s (stackArg s 2) ((stackArg s 3).toNat * 8) (s.gpr .rdx)
    (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  hpb : Src s (stackArg s 2) ((stackArg s 3).toNat * 8) (s.gpr .r8)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
  hqb : Src s (stackArg s 2) ((stackArg s 3).toNat * 8) (stackArg s 0)
    (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
  hout : ∀ j < (s.gpr .rsi).toNat * 8, InRegions s.wr (s.gpr .rdi + BitVec.ofNat 64 j) 1
  houts : ∀ j < (s.gpr .rsi).toNat * 8, (stackArg s 3).toNat * 8 ≤ ofs (stackArg s 2) (s.gpr .rdi + BitVec.ofNat 64 j)
  hwrap : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat * 8 ≤ 2 ^ 64
  hon : ∀ j < (s.gpr .rsi).toNat * 8, ∀ i < (s.gpr .rcx).toNat, s.gpr .rdi + BitVec.ofNat 64 j ≠ s.gpr .rdx + BitVec.ofNat 64 i
  hop : ∀ j < (s.gpr .rsi).toNat * 8, ∀ i < (s.gpr .r9).toNat, s.gpr .rdi + BitVec.ofNat 64 j ≠ s.gpr .r8 + BitVec.ofNat 64 i
  hoq : ∀ j < (s.gpr .rsi).toNat * 8, ∀ i < (stackArg s 1).toNat,
    s.gpr .rdi + BitVec.ofNat 64 j ≠ stackArg s 0 + BitVec.ofNat 64 i
  hret : ∀ b < 8, (stackArg s 3).toNat * 8 ≤ ofs (stackArg s 2) (s.gpr .rsp + BitVec.ofNat 64 b) ∧
    ∀ j < (s.gpr .rsi).toNat * 8, s.gpr .rsp + BitVec.ofNat 64 b ≠ s.gpr .rdi + BitVec.ofNat 64 j
  hpreR : (⟨s.gpr .rdi, (s.gpr .rsi).toNat * 8⟩ : Region) ∈ s.wr
  hS : ∀ x, ofs (stackArg s 2) x < (stackArg s 3).toNat * 8 → (s.gpr .rsi).toNat * 8 ≤ ofs (s.gpr .rdi) x
  hretP : ∀ b < 8, (s.gpr .rsi).toNat * 8 ≤ ofs (s.gpr .rdi) (s.gpr .rsp + BitVec.ofNat 64 b)

/-- Bytes of two disjoint regions differ. -/
theorem disjoint_ne {a b : Addr} {la lb : Nat} (hd : (⟨a, la⟩ : Region).Disjoint ⟨b, lb⟩) (ha : la ≤ 2 ^ 64)
    (hb : lb ≤ 2 ^ 64) : ∀ j < la, ∀ i < lb, a + BitVec.ofNat 64 j ≠ b + BitVec.ofNat 64 i := by
  intro j hj i hi he
  exact hd _ (contains_byte a hj ha) (by rw [he]; exact contains_byte b hi hb)

theorem ppCtx_of {s : State} (h : ppContract.pre s) : PPCtx s := by
  simp only [ppContract] at h
  sig_split h
  rename_i hsp hrd hwr dPn dPp dPq dPs dPa dns dps dqs dsa dRo dRn dRp dRq dRs dRa wO wN wP wQ wS hk hpl1 hpl2
    hql1 hql2 hL
  have hsl := h
  obtain ⟨hk1, hk2⟩ := hk
  unfold Spec.Rsa.scratchWords at hsl
  obtain hs : Scr s (stackArg s 2) ((stackArg s 3).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) wS
  have hn := hs.nowrap
  obtain hargs : (⟨stackArgAddr s 0, 32⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  refine ⟨hk1, hk2, hpl1, hpl2, hql1, hql2, hL, by omega_arith, hs,
    fun j hj => ⟨_, hargs, by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩,
    src_of_region (by rw [hrd]; simp) (by omega_arith) dns,
    src_of_region (by rw [hrd]; simp) (by omega_arith) dps,
    src_of_region (by rw [hrd]; simp) (by omega_arith) dqs,
    fun j hj => ⟨_, by rw [hwr]; exact List.mem_cons_self, contains_byte _ hj (by omega_arith)⟩,
    fun j hj => out_scr dPs (contains_byte _ hj (by omega_arith)), wO,
    disjoint_ne dPn (by omega_arith) (by omega_arith), disjoint_ne dPp (by omega_arith) (by omega_arith),
    disjoint_ne dPq (by omega_arith) (by omega_arith), fun b hb => ?_, by rw [hwr]; exact List.mem_cons_self,
    fun x hx => ?_, fun b hb => ?_⟩
  · have hc := contains_byte (s.gpr .rsp) (i := b) (len := 8) hb (by omega_arith)
    exact ⟨out_scr dRs hc, fun j hj he => dRo _ hc (by rw [he]; exact contains_byte _ hj (by omega_arith))⟩
  · refine Nat.le_of_not_lt fun h' => dPs x ?_ ?_
    · show (x - s.gpr .rdi).toNat + 1 ≤ (s.gpr .rsi).toNat * 8
      unfold ofs at h'; omega_using [h']
    · show (x - stackArg s 2).toNat + 1 ≤ (stackArg s 3).toNat * 8
      unfold ofs at hx; omega_using [hx]
  · have hc := contains_byte (s.gpr .rsp) (i := b) (len := 8) hb (by omega_arith)
    refine Nat.le_of_not_lt fun h' => dRo _ hc ?_
    show (s.gpr .rsp + BitVec.ofNat 64 b - s.gpr .rdi).toNat + 1 ≤ (s.gpr .rsi).toNat * 8
    unfold ofs at h'; omega_using [h']

/-! ## The entry -/

theorem entry_eq : PrivPre.entry = ([.mov .r11 (.mem { base := .rsp, disp := 24 }),
    .mov .r10 (.mem { base := .rsp, disp := 8 }), .mov .rax (.mem { base := .rsp, disp := 16 }),
    .store (hdr11 0) .rbx, .store (hdr11 1) .rbp, .store (hdr11 2) .r12, .store (hdr11 3) .r13,
    .store (hdr11 4) .r14, .store (hdr11 5) .r15,
    .store (hdr11 sOut) .rdi, .store (hdr11 sN) .rdx, .store (hdr11 sK) .rcx, .store (hdr11 sIn) .rdi,
    .store (hdr11 sP) .r8, .store (hdr11 sPlen) .r9, .store (hdr11 sDp) .r8, .store (hdr11 sQinv) .rdi,
    .store (hdr11 sQ) .r10, .store (hdr11 sDq) .r10, .store (hdr11 sQlen) .rax,
    .mov .rdi (.reg .r11)] : List Instr) := rfl

/-- The header after the entry's stores. -/
def entryMem (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vo vn vk vp vpl vq vql : BitVec 64) : Mem :=
  ((((((((((((((((m.writeW (off B (8 * 0)) v0).writeW (off B (8 * 1)) v1).writeW (off B (8 * 2)) v2).writeW
    (off B (8 * 3)) v3).writeW (off B (8 * 4)) v4).writeW (off B (8 * 5)) v5).writeW (off B (8 * sOut)) vo).writeW
    (off B (8 * sN)) vn).writeW (off B (8 * sK)) vk).writeW (off B (8 * sIn)) vo).writeW
    (off B (8 * sP)) vp).writeW (off B (8 * sPlen)) vpl).writeW (off B (8 * sDp)) vp).writeW
    (off B (8 * sQinv)) vo).writeW (off B (8 * sQ)) vq).writeW (off B (8 * sDq)) vq).writeW (off B (8 * sQlen)) vql

theorem entryMem_facts (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vo vn vk vp vpl vq vql : BitVec 64) :
    let m' := entryMem m B v0 v1 v2 v3 v4 v5 vo vn vk vp vpl vq vql
    word m' B (8 * 0) = v0 ∧ word m' B (8 * 1) = v1 ∧ word m' B (8 * 2) = v2 ∧ word m' B (8 * 3) = v3 ∧
    word m' B (8 * 4) = v4 ∧ word m' B (8 * 5) = v5 ∧ word m' B (8 * sOut) = vo ∧ word m' B (8 * sN) = vn ∧
    word m' B (8 * sK) = vk ∧ word m' B (8 * sIn) = vo ∧ word m' B (8 * sP) = vp ∧ word m' B (8 * sPlen) = vpl ∧
    word m' B (8 * sQ) = vq ∧ word m' B (8 * sQlen) = vql ∧ word m' B (8 * sDp) = vp ∧
    word m' B (8 * sDq) = vq ∧ word m' B (8 * sQinv) = vo ∧ Outside B 0 (8 * 32) m m' := by
  intro m'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold m' entryMem
  all_goals first
    | (repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) |
        exact word_writeW_self _ _ _ _)); done
    | (repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _))

/-- `entry`: the header, from the arguments, and the working space's base
(stack argument 2) in `rdi`. -/
theorem entry_ok {s : State} (c : PPCtx s) :
    WP isa (.block PrivPre.entry) s fun t => t.gpr .rdi = stackArg s 2 ∧
      (∀ i < 6, word t.mem (stackArg s 2) (8 * i) = s.gpr (saved.getD i .rax)) ∧
      word t.mem (stackArg s 2) (8 * sOut) = s.gpr .rdi ∧ word t.mem (stackArg s 2) (8 * sN) = s.gpr .rdx ∧
      word t.mem (stackArg s 2) (8 * sK) = s.gpr .rcx ∧ word t.mem (stackArg s 2) (8 * sIn) = s.gpr .rdi ∧
      word t.mem (stackArg s 2) (8 * sP) = s.gpr .r8 ∧ word t.mem (stackArg s 2) (8 * sPlen) = s.gpr .r9 ∧
      word t.mem (stackArg s 2) (8 * sQ) = stackArg s 0 ∧ word t.mem (stackArg s 2) (8 * sQlen) = stackArg s 1 ∧
      word t.mem (stackArg s 2) (8 * sDp) = s.gpr .r8 ∧ word t.mem (stackArg s 2) (8 * sDq) = stackArg s 0 ∧
      word t.mem (stackArg s 2) (8 * sQinv) = s.gpr .rdi ∧
      Outside (stackArg s 2) 0 (8 * 32) s.mem t.mem ∧ Keep [.r11, .r10, .rax, .rdi] s t := by
  have hn := c.hs.nowrap
  have hZ := c.hZ
  have hk1 := c.hk1
  obtain hw : ∀ i < 32, InRegions s.wr (off (stackArg s 2) (8 * i)) 8 := fun i hi => c.hs.st (by omega_arith)
  have e0 : s.gpr .rsp + BitVec.ofInt 64 8 = stackArgAddr s 0 := rfl
  have e1 : s.gpr .rsp + BitVec.ofInt 64 16 = stackArgAddr s 1 := rfl
  have e2 : s.gpr .rsp + BitVec.ofInt 64 24 = stackArgAddr s 2 := rfl
  have r0 : s.mem.readW (stackArgAddr s 0) 64 = stackArg s 0 := rfl
  have r1 : s.mem.readW (stackArgAddr s 1) 64 = stackArg s 1 := rfl
  have r2 : s.mem.readW (stackArgAddr s 2) 64 = stackArg s 2 := rfl
  rw [entry_eq]
  refine WP.mono (WP.keep [.r11, .r10, .rax, .rdi] (Q := fun t => t.gpr .rdi = stackArg s 2 ∧
      t.mem = entryMem s.mem (stackArg s 2) (s.gpr .rbx) (s.gpr .rbp) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14)
        (s.gpr .r15) (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r8) (s.gpr .r9) (stackArg s 0)
        (stackArg s 1)) ?_ rfl) fun t ⟨⟨hdi, hm⟩, k⟩ => ?_
  · xrun [State.ea, hdr11, e0, e1, e2, c.ha 0 (by decide), c.ha 1 (by decide), c.ha 2 (by decide), r0, r1, r2,
      hdrOff, hw 0 (by decide), hw 1 (by decide), hw 2 (by decide), hw 3 (by decide), hw 4 (by decide),
      hw 5 (by decide), hw sOut (by decide), hw sN (by decide), hw sK (by decide), hw sIn (by decide),
      hw sP (by decide), hw sPlen (by decide), hw sDp (by decide), hw sQinv (by decide), hw sQ (by decide),
      hw sDq (by decide), hw sQlen (by decide)]
    rfl
  rw [hm]
  obtain ⟨h0, h1, h2, h3, h4, h5, hO, hN, hK, hI, hP, hPl, hQ, hQl, hDp, hDq, hQi, ho⟩ :=
    entryMem_facts s.mem (stackArg s 2) (s.gpr .rbx) (s.gpr .rbp) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14)
      (s.gpr .r15) (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r8) (s.gpr .r9) (stackArg s 0) (stackArg s 1)
  refine ⟨hdi, fun i hi => ?_, hO, hN, hK, hI, hP, hPl, hQ, hQl, hDp, hDq, hQi, ho, k⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_using [hi]) with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
theorem ofNat_toNat_self (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

theorem eight_w (r : BitVec 64) {L : Nat} (h : r = BitVec.ofNat 64 L) :
    r + r + (r + r) + (r + r + (r + r)) = BitVec.ofNat 64 (L * 8) := by
  subst h; simp only [BitVec.ofNat_add_ofNat]; congr 1; omega_using []

/-- `zeroPre`: zeros to the `8 L` bytes at `op`, which `sOut` holds. -/
theorem zeroPre_ok {t : State} {B : Addr} {Z L : Nat} {op : Addr} (hs : Scr t B Z) (hdi : t.gpr .rdi = B)
    (hZ : 8 * 32 ≤ Z) (hL1 : 1 ≤ L) (hL : L * 8 < 2 ^ 31) (hsi : t.gpr .rsi = BitVec.ofNat 64 L)
    (hO : word t.mem B (8 * sOut) = op) (hout : ∀ j < L * 8, InRegions t.wr (op + BitVec.ofNat 64 j) 1) :
    WP isa PrivPre.zeroPre t fun u =>
      (∀ j < L * 8, u.mem (op + BitVec.ofNat 64 j) = 0) ∧
      (∀ x, (∀ j < L * 8, x ≠ op + BitVec.ofNat 64 j) → u.mem x = t.mem x) ∧ Keep [.rcx, .rsi, .rax] t u := by
  have hn := hs.nowrap
  obtain hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega_using [hZ, hi])
  unfold PrivPre.zeroPre
  refine WP.seq (WP.mono (WP.keep [.rsi, .rcx, .rax] (Q := fun t' => t'.gpr .rsi = op ∧
      t'.gpr .rcx = BitVec.ofNat 64 (L * 8) ∧ t'.gpr .rax = 0 ∧ t'.mem = t.mem) (by
    xrun [State.ea, hdr, hdi, hdrOff, hl sOut (by decide), hO, eight_w _ hsi]) rfl)
      fun s₁ ⟨⟨hsi₁, hcx, hax, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (wp_upto (a := 0) (N := L * 8) (by omega_using [hL1]) (FailInv s₁ op (L * 8)) ?_ (fun t h => h)
    ⟨Keep.refl _ _, by rw [hsi₁, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero], by rw [hcx, Nat.sub_zero],
      fun i hi => absurd hi (by omega_using []), fun x _ => rfl⟩) fun u hI => ⟨hI.bytes, fun x hx => by
        rw [hI.frame x hx, hm₁], (k₁.trans hI.keep).mono (by decide)⟩
  intro j _ hj u hI
  obtain hst : InRegions u.wr (op + BitVec.ofNat 64 j) 1 := by
    rw [hI.keep.2.2, k₁.2.2]; exact hout j hj
  obtain hax' : (u.gpr .rax).setWidth 8 = 0 := by rw [hI.keep.gpr (by decide), hax]; rfl
  refine WP.mono (WP.keep [.rsi, .rcx] (Q := fun t' =>
      t'.mem = u.mem.writeW (op + BitVec.ofNat 64 j) (0 : BitVec 8) ∧
      t'.gpr .rsi = op + BitVec.ofNat 64 (j + 1) ∧ t'.gpr .rcx = BitVec.ofNat 64 (L * 8 - (j + 1)) ∧
      t'.zf = some (decide (j + 1 = L * 8))) (by
    xrun [State.ea, at0, hI.rsi, hI.rcx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hst, hax',
      ofNat64_pred (show 1 ≤ L * 8 - j by omega_using [hj]) (by omega_using [hL]), BitVec.add_assoc, ofNat_add_one,
      ofNat64_beq_zero (show L * 8 - j - 1 < 2 ^ 64 by omega_using [hL])]
    exact ⟨by rw [show L * 8 - j - 1 = L * 8 - (j + 1) by omega_using []], decide_eq_decide.mpr (by omega_using [hj])⟩) rfl)
    fun t' ⟨⟨hm, hsi', hcx', hz⟩, k'⟩ => ⟨hz, (hI.keep.trans k').mono (by decide), hsi', hcx', ?_, ?_⟩
  · intro i hi
    rw [hm, writeW8_apply]
    by_cases hij : i = j
    · subst hij; simp
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega_using [hL, hj, hi]) (by omega_using [hL, hj]) hij))]
      exact hI.bytes i (by omega_using [hi, hij])
  · intro x hx
    rw [hm, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega_using [])))]
    exact hI.frame x fun i hi => hx i (by omega_using [hi])

/-- After `entry`, `zeroPre` and the reloads of `n` and `k`, from `s`. -/
structure PPHead (s t : State) : Prop where
  scr : Scr t (stackArg s 2) ((stackArg s 3).toNat * 8)
  rdi : t.gpr .rdi = stackArg s 2
  rdx : t.gpr .rdx = s.gpr .rdx
  rcx : t.gpr .rcx = BitVec.ofNat 64 (s.gpr .rcx).toNat
  saved : ∀ i < 6, word t.mem (stackArg s 2) (8 * i) = s.gpr (saved.getD i .rax)
  hO : word t.mem (stackArg s 2) (8 * sOut) = s.gpr .rdi
  hN : word t.mem (stackArg s 2) (8 * sN) = s.gpr .rdx
  hK : word t.mem (stackArg s 2) (8 * sK) = BitVec.ofNat 64 (s.gpr .rcx).toNat
  hIn : word t.mem (stackArg s 2) (8 * sIn) = s.gpr .rdi
  hP : word t.mem (stackArg s 2) (8 * sP) = s.gpr .r8
  hPl : word t.mem (stackArg s 2) (8 * sPlen) = BitVec.ofNat 64 (s.gpr .r9).toNat
  hQ : word t.mem (stackArg s 2) (8 * sQ) = stackArg s 0
  hQl : word t.mem (stackArg s 2) (8 * sQlen) = BitVec.ofNat 64 (stackArg s 1).toNat
  hDp : word t.mem (stackArg s 2) (8 * sDp) = s.gpr .r8
  hDq : word t.mem (stackArg s 2) (8 * sDq) = stackArg s 0
  hQi : word t.mem (stackArg s 2) (8 * sQinv) = s.gpr .rdi
  zero : ∀ j < (s.gpr .rsi).toNat * 8, t.mem (s.gpr .rdi + BitVec.ofNat 64 j) = 0
  frame : ∀ x, (∀ j < (s.gpr .rsi).toNat * 8, x ≠ s.gpr .rdi + BitVec.ofNat 64 j) →
    (stackArg s 3).toNat * 8 ≤ ofs (stackArg s 2) x → t.mem x = s.mem x
  inScr : ∀ x, (stackArg s 3).toNat * 8 ≤ ofs (stackArg s 2) x →
    (∀ j < (s.gpr .rsi).toNat * 8, x ≠ s.gpr .rdi + BitVec.ofNat 64 j) → t.mem x = s.mem x
  keep : Keep [.r11, .r10, .rax, .rdi, .rcx, .rsi, .rdx] s t

/-- `entry`, `zeroPre`, and `n` and `k` into `rdx` and `rcx`. -/
theorem head_ok {s : State} (c : PPCtx s) :
    WP isa (.block PrivPre.entry) s fun t₁ => WP isa PrivPre.zeroPre t₁ fun t₂ =>
      WP isa (.block [.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))]) t₂ (PPHead s) := by
  have hn := c.hs.nowrap
  have hZ := c.hZ
  have hk1 := c.hk1
  have hk2 := c.hk2
  have hL := c.hL
  have hpl2 := c.hpl2
  have hql2 := c.hql2
  simp only [Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords, Spec.Rsa.primeWords,
    Spec.Rsa.modulusWords] at hL
  refine WP.mono (entry_ok c) fun t₀ ⟨hdi, hsv, hO, hN, hK, hI, hP, hPl, hQ, hQl, hDp, hDq, hQi, ho₀, k₀⟩ => ?_
  obtain hs₀ := c.hs.congr k₀.2.2
  refine WP.mono (zeroPre_ok hs₀ hdi (by omega_using [hZ]) (L := (s.gpr .rsi).toNat) (by omega_using [hL]) (by omega_using [hk2, hL, hpl2, hql2])
    (by rw [k₀.gpr (by decide), ofNat_toNat_self]) hO (fun j hj => by rw [k₀.2.2]; exact c.hout j hj))
    fun t₁ ⟨hz₁, hf₁, k₁⟩ => ?_
  obtain hs₁ := hs₀.congr k₁.2.2
  -- The header is not in `pre`.
  obtain hh : ∀ i < 32, word t₁.mem (stackArg s 2) (8 * i) = word t₀.mem (stackArg s 2) (8 * i) := fun i hi =>
    Mem.readW_congr fun b hb => hf₁ _ (fun j hj => scr_ne_out c.houts (d := 8 * i) (i := b) (by omega_using [hZ, hi, hb])
      (by omega_using [hn]) j hj)
  obtain hdi₁ : t₁.gpr .rdi = stackArg s 2 := (k₁.gpr (by decide)).trans hdi
  refine WP.mono (WP.keep [.rdx, .rcx] (Q := fun t => t.gpr .rdx = s.gpr .rdx ∧
      t.gpr .rcx = s.gpr .rcx ∧ t.mem = t₁.mem) (by
    xrun [State.ea, hdr, hdi₁, hdrOff, hs₁.ld (d := 8 * sN) (by unfold sN sFn; omega_using [hZ]),
      hs₁.ld (d := 8 * sK) (by unfold sK sFn; omega_using [hZ]), hh sN (by decide), hh sK (by decide), hN, hK]) rfl)
    fun t ⟨⟨hdx, hcx, hm⟩, k₂⟩ => ?_
  obtain hw : ∀ i < 32, word t.mem (stackArg s 2) (8 * i) = word t₀.mem (stackArg s 2) (8 * i) := fun i hi => by
    rw [hm]; exact hh i hi
  obtain kk := (k₀.trans k₁).trans k₂
  obtain hfr : ∀ x, (∀ j < (s.gpr .rsi).toNat * 8, x ≠ s.gpr .rdi + BitVec.ofNat 64 j) →
      (stackArg s 3).toNat * 8 ≤ ofs (stackArg s 2) x → t.mem x = s.mem x := fun x hx hxz => by
    rw [hm, hf₁ x hx, ho₀ x (by omega_using [hZ, hxz])]
  exact ⟨hs₁.congr k₂.2.2, (k₂.gpr (by decide)).trans hdi₁, hdx, by rw [hcx, ofNat_toNat_self],
    fun i hi => by rw [hw i (by omega_using [hi])]; exact hsv i hi,
    by rw [hw _ (by decide)]; exact hO, by rw [hw _ (by decide)]; exact hN,
    by rw [hw _ (by decide), hK, ofNat_toNat_self], by rw [hw _ (by decide)]; exact hI,
    by rw [hw _ (by decide)]; exact hP, by rw [hw _ (by decide), hPl, ofNat_toNat_self],
    by rw [hw _ (by decide)]; exact hQ, by rw [hw _ (by decide), hQl, ofNat_toNat_self],
    by rw [hw _ (by decide)]; exact hDp, by rw [hw _ (by decide)]; exact hDq, by rw [hw _ (by decide)]; exact hQi,
    fun j hj => by rw [hm]; exact hz₁ j hj, hfr, fun x hxz hx => hfr x hx hxz, kk.mono (by decide)⟩

/-- Bytes outside `pre` and the working space, as they were. -/
theorem Src.of_head {s t : State} {p : Addr} {bs : List Byte}
    (h : Src s (stackArg s 2) ((stackArg s 3).toNat * 8) p bs)
    (hne : ∀ j < (s.gpr .rsi).toNat * 8, ∀ i < bs.length, s.gpr .rdi + BitVec.ofNat 64 j ≠ p + BitVec.ofNat 64 i)
    (hf : ∀ x, (∀ j < (s.gpr .rsi).toNat * 8, x ≠ s.gpr .rdi + BitVec.ofNat 64 j) →
      (stackArg s 3).toNat * 8 ≤ ofs (stackArg s 2) x → t.mem x = s.mem x)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : Src t (stackArg s 2) ((stackArg s 3).toNat * 8) p bs :=
  ⟨fun i hi => by rw [hrd, hwr]; exact h.rd i hi,
    fun i hi => by rw [hf _ (fun j hj he => hne j hj i hi he.symm) (h.out i hi)]; exact h.val i hi, h.out⟩

/-- `pre`'s first bytes, zeros, as a byte string the code reads. -/
theorem src_zeros {s t : State} {n : Nat} (c : PPCtx s) (hn : n ≤ (s.gpr .rsi).toNat * 8)
    (hz : ∀ j < (s.gpr .rsi).toNat * 8, t.mem (s.gpr .rdi + BitVec.ofNat 64 j) = 0) (hwr : t.wr = s.wr) :
    Src t (stackArg s 2) ((stackArg s 3).toNat * 8) (s.gpr .rdi) (List.replicate n 0) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => c.houts i (by simp at hi; omega_using [hn, hi])⟩
  · simp only [List.length_replicate] at hi
    obtain ⟨r, hr, hc⟩ := c.hout i (by omega_using [hn, hi])
    exact ⟨r, List.mem_append_right _ (by rw [hwr]; exact hr), hc⟩
  · simp only [List.length_replicate] at hi
    rw [hz i (by omega_using [hn, hi]), List.getElem_replicate]

/-- `vg_rsa_private_crt`'s precondition, after the head and the modulus'
check, with `pre` (zeros) as the input and as `qInv`. -/
theorem ppPre_of {s t₁ t : State} (c : PPCtx s) (h : PPHead s t₁) (hm : t.mem = t₁.mem)
    (k : Keep [.rax, .rbp, .rsi] t₁ t) :
    CrtPre t (stackArg s 2) ((stackArg s 3).toNat * 8) (s.gpr .rcx).toNat (s.gpr .rdi) (s.gpr .rdx)
      (s.gpr .rdi) (s.gpr .r8) (stackArg s 0) (s.gpr .r8) (stackArg s 0) (s.gpr .rdi)
      (s.gpr .r9).toNat (stackArg s 1).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
      (List.replicate (s.gpr .rcx).toNat 0)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
      (List.replicate (s.gpr .r9).toNat 0) := by
  obtain kk := h.keep.trans k
  have hZ := c.hZ
  have hk1 := c.hk1
  have hk2 := c.hk2
  have hpl2 := c.hpl2
  have hql2 := c.hql2
  have hL := c.hL
  simp only [Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords, Spec.Rsa.primeWords,
    Spec.Rsa.modulusWords] at hL
  obtain hdi : t.gpr .rdi = stackArg s 2 := (k.gpr (by decide)).trans h.rdi
  obtain hf : ∀ x, (∀ j < (s.gpr .rsi).toNat * 8, x ≠ s.gpr .rdi + BitVec.ofNat 64 j) →
      (stackArg s 3).toNat * 8 ≤ ofs (stackArg s 2) x → t.mem x = s.mem x := fun x hx hxz => by
    rw [hm]; exact h.frame x hx hxz
  obtain hz : ∀ j < (s.gpr .rsi).toNat * 8, t.mem (s.gpr .rdi + BitVec.ofNat 64 j) = 0 := fun j hj => by
    rw [hm]; exact h.zero j hj
  obtain hz8 : offQ (((s.gpr .rcx).toNat + 7) / 8) (s.gpr .r9).toNat + slot (wsWords (stackArg s 1).toNat) 8 +
      wsTab (wsWords (stackArg s 1).toNat) ≤ (stackArg s 3).toNat * 8 :=
    crt_room hk1 hpl2 hql2 hZ
  obtain hnb := Src.of_head (t := t) c.hnb (by rw [bytesAt_length]; exact c.hon) hf kk.2.1 kk.2.2
  obtain hpb := Src.of_head (t := t) c.hpb (by rw [bytesAt_length]; exact c.hop) hf kk.2.1 kk.2.2
  obtain hqb := Src.of_head (t := t) c.hqb (by rw [bytesAt_length]; exact c.hoq) hf kk.2.1 kk.2.2
  exact
    { scr := h.scr.congr k.2.2, rdi := hdi, z := hz8, zk := (by omega_using [hZ]), k1 := hk1, k2 := hk2,
      hO := (by rw [hm]; exact h.hO), hN := (by rw [hm]; exact h.hN), hK := (by rw [hm]; exact h.hK),
      hIn := (by rw [hm]; exact h.hIn), hP := (by rw [hm]; exact h.hP), hPl := (by rw [hm]; exact h.hPl),
      hQ := (by rw [hm]; exact h.hQ), hQl := (by rw [hm]; exact h.hQl), hDp := (by rw [hm]; exact h.hDp),
      hDq := (by rw [hm]; exact h.hDq), hQi := (by rw [hm]; exact h.hQi), n := hnb,
      x := src_zeros c (by omega_using [hL]) hz kk.2.2, p := hpb, q := hqb, dp := hpb, dq := hqb,
      qi := src_zeros c (by omega_using [hL]) hz kk.2.2, nl := bytesAt_length _ _ _, xl := List.length_replicate,
      pbl := bytesAt_length _ _ _, qbl := bytesAt_length _ _ _, dpl := bytesAt_length _ _ _,
      dql := bytesAt_length _ _ _, qil := List.length_replicate, pl1 := c.hpl1, pl2 := hpl2, ql1 := c.hql1,
      ql2 := hql2, out := (fun j hj => by rw [kk.2.2]; exact c.hout j (by omega_using [hL, hj])),
      outSep := (fun j hj => c.houts j (by omega_using [hL, hj])) }
end VG.Proof.Bignum.X86_64.PrivPre

end

end

/-!
# `vg_rsa_private_precompute` on x86-64: correctness

From a state `ppContract` allows, `PrivPre.code` writes `privatePrecompute`
of `n`, `p` and `q` to `pre` and returns whether it is `some`
(`code_correct`): on an invalid modulus `fail` writes zeros to its first
`k` bytes of the zeros `zeroPre` wrote; otherwise the mask is that of
`p q = n`, and `pre`'s words those `out` writes, from its four parts, each
word and-ed with the mask (`wordsAt_out`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.PrivPre

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Crt VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64
theorem wordsAt_append (m : Mem) (p : Addr) (a b : Nat) :
    Spec.Rsa.wordsAt m p (a + b) =
      Spec.Rsa.wordsAt m p a ++ Spec.Rsa.wordsAt m (p + BitVec.ofNat 64 (8 * a)) b := by
  rw [Spec.Rsa.wordsAt, Spec.Rsa.wordsAt, Spec.Rsa.wordsAt, List.range_add, List.map_append, List.map_map]
  refine congrArg _ (List.map_congr_left fun i _ => ?_)
  simp only [Function.comp_apply]
  rw [Offset.add_add, Nat.mul_add]

/-- A part of `pre`, word by word. -/
theorem seg_eq {m : Mem} {D : Addr} {e n : Nat} {f : Nat → BitVec 64}
    (h : ∀ i < n, word m D (e + 8 * i) = f i) :
    Spec.Rsa.wordsAt m (D + BitVec.ofNat 64 e) n = (List.range n).map f := by
  refine List.map_congr_left fun i hi => ?_
  rw [Offset.add_add]
  exact h i (List.mem_range.mp hi)

theorem and_mask (x : BitVec 64) (c : Bool) : x &&& mask c = if c then x else 0 := by
  cases c
  · simp [mask_false]
  · rw [mask_true, BitVec.and_allOnes]; rfl

/-- `pre`'s words, from its four parts. -/
theorem wordsAt_out {m : Mem} {D : Addr} {w wp wq : Nat} {M : Bool} {VN VR VP VQ : Nat}
    (hN : ∀ i < w, word m D (8 * i) = BitVec.ofNat 64 (VN / 2 ^ (64 * i)) &&& mask M)
    (hR : ∀ i < w, word m D (8 * w + 8 * i) = BitVec.ofNat 64 (VR / 2 ^ (64 * i)) &&& mask M)
    (hP : ∀ i < wp, word m D (16 * w + 8 * i) = BitVec.ofNat 64 (VP / 2 ^ (64 * i)) &&& mask M)
    (hQ : ∀ i < wq, word m D (16 * w + 8 * wp + 8 * i) = BitVec.ofNat 64 (VQ / 2 ^ (64 * i)) &&& mask M) :
    Spec.Rsa.wordsAt m D (2 * w + wp + wq) = if M then
      Spec.Rsa.toWords VN w ++ Spec.Rsa.toWords VR w ++ Spec.Rsa.toWords VP wp ++ Spec.Rsa.toWords VQ wq
    else List.replicate (2 * w + wp + wq) 0 := by
  rw [show 2 * w + wp + wq = w + w + wp + wq by omega_using [], wordsAt_append, wordsAt_append, wordsAt_append]
  have h0 : Spec.Rsa.wordsAt m D w = (List.range w).map fun i => BitVec.ofNat 64 (VN / 2 ^ (64 * i)) &&& mask M := by
    have := seg_eq (m := m) (D := D) (e := 0) (n := w) (f := fun i => BitVec.ofNat 64 (VN / 2 ^ (64 * i)) &&& mask M)
      (fun i hi => by rw [Nat.zero_add]; exact hN i hi)
    simpa using this
  have eP : 8 * (w + w) = 16 * w := by omega_using []
  have eQ : 8 * (w + w + wp) = 16 * w + 8 * wp := by omega_using []
  rw [eP, eQ]
  rw [h0, seg_eq (f := fun i => BitVec.ofNat 64 (VR / 2 ^ (64 * i)) &&& mask M) hR,
    seg_eq (f := fun i => BitVec.ofNat 64 (VP / 2 ^ (64 * i)) &&& mask M) hP,
    seg_eq (f := fun i => BitVec.ofNat 64 (VQ / 2 ^ (64 * i)) &&& mask M) hQ]
  cases M
  · simp only [and_mask, Bool.false_eq_true, ↓reduceIte, List.map_const', List.length_range,
      List.replicate_append_replicate]
  · simp only [and_mask, ↓reduceIte, Spec.Rsa.toWords]
theorem os2ip_replicate_zero (n : Nat) : Spec.Rsa.os2ip (List.replicate n 0) = 0 := by
  unfold Spec.Rsa.os2ip
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ', List.foldl_append, ih]; rfl

theorem readW_add (m : Mem) (p : Addr) (i : Nat) :
    m.readW (p + BitVec.ofNat 64 (8 * i)) 64 = word m p (8 * i) := rfl

/-- `pre` all zeros, from its bytes. -/
theorem wordsAt_zero {m : Mem} {D : Addr} {L : Nat} (h : ∀ j < L * 8, m (D + BitVec.ofNat 64 j) = 0) :
    Spec.Rsa.wordsAt m D L = List.replicate L 0 := by
  rw [Spec.Rsa.wordsAt, List.eq_replicate_iff]
  refine ⟨by simp, fun x hx => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  refine readW_zero fun b hb => ?_
  have hi := List.mem_range.mp hi
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact h _ (by omega_using [hb, hi])


/-- The callee-saved registers and the return address, from the header the
entry wrote and the memory outside `pre` and the working space. -/
theorem gpr_of {s t₃ t₄ t : State} (c : PPCtx s) (h : PPHead s t₃) (hm : t₄.mem = t₃.mem)
    (k : Keep [.rax, .rbp, .rsi] t₃ t₄)
    (hsv : ∀ i < 6, t.gpr (saved.getD i .rax) = word t₄.mem (stackArg s 2) (8 * i))
    (hrsp : t.gpr .rsp = t₄.gpr .rsp)
    (hfr : ∀ x, (stackArg s 3).toNat * 8 ≤ ofs (stackArg s 2) x →
      (∀ j < (s.gpr .rsi).toNat * 8, x ≠ s.gpr .rdi + BitVec.ofNat 64 j) → t.mem x = t₄.mem x) :
    gprPreserved s t := by
  refine ⟨fun reg hreg => ?_, Mem.readW_congr fun b hb => ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hreg
    rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hsv 0 (by decide)).trans (by rw [hm]; exact h.saved 0 (by decide))
    · exact (hsv 1 (by decide)).trans (by rw [hm]; exact h.saved 1 (by decide))
    · exact hrsp.trans ((k.gpr (by decide)).trans (h.keep.gpr (by decide)))
    · exact (hsv 2 (by decide)).trans (by rw [hm]; exact h.saved 2 (by decide))
    · exact (hsv 3 (by decide)).trans (by rw [hm]; exact h.saved 3 (by decide))
    · exact (hsv 4 (by decide)).trans (by rw [hm]; exact h.saved 4 (by decide))
    · exact (hsv 5 (by decide)).trans (by rw [hm]; exact h.saved 5 (by decide))
  · obtain ⟨hZx, hne⟩ := c.hret b hb
    rw [hfr _ hZx (fun j hj he => hne j hj he), hm, h.frame _ (fun j hj he => hne j hj he) hZx]

/-- An invalid modulus: zeros and 0. -/
theorem fail_post {s t₃ t₄ t : State} (c : PPCtx s) (h : PPHead s t₃) (hm : t₄.mem = t₃.mem)
    (k : Keep [.rax, .rbp, .rsi] t₃ t₄)
    (hp : MainPost t₄ t (stackArg s 2) ((stackArg s 3).toNat * 8) (s.gpr .rcx).toNat (s.gpr .rdi) 0 false)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
      (s.gpr .rcx).toNat = false) :
    gprPreserved s t ∧ ppContract.post s t := by
  have hL := c.hL
  have hk1 := c.hk1
  have hk2 := c.hk2
  have hkL : (s.gpr .rcx).toNat ≤ (s.gpr .rsi).toNat * 8 := by
    rw [hL]; simp only [Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords]; omega_using []
  refine ⟨gpr_of c h hm k hp.saved (hp.keep.gpr (by decide)) fun x hx hne => hp.frame x hx fun j hj he =>
    hne j (by omega_using [hkL, hj]) he, ?_⟩
  have hnone : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat) = none := by
    unfold Spec.Rsa.privatePrecompute
    split <;> simp [Spec.Rsa.publicPrecompute, bytesAt_length, hv]
  show match Spec.Rsa.privatePrecompute _ _ _ with
    | some ws => _ | none => _
  rw [hnone]
  refine ⟨by rw [hp.rax]; rfl, wordsAt_zero fun j hj => ?_⟩
  by_cases hjk : j < (s.gpr .rcx).toNat
  · have := congrArg (fun l => l[j]?) hp.bytes
    simp only [i2osp_zero', List.getElem?_map, List.getElem?_range hjk, List.getElem?_replicate, hjk,
      ↓reduceIte, Option.map_some, Option.some.injEq] at this
    exact this
  · have := c.hwrap
    rw [hp.frame _ (c.houts j hj) (fun j' hj' he => out_ne (by omega_using [hj, this]) (by omega_using [hj']) (show j ≠ j' by omega_using [hjk, hj']) he), hm]
    exact h.zero j hj

/-- `pre`'s length in words: the four parts'. -/
theorem preWords {s : State} (c : PPCtx s) :
    (s.gpr .rsi).toNat = 2 * (((s.gpr .rcx).toNat + 7) / 8) + wsWords (s.gpr .r9).toNat +
      wsWords (stackArg s 1).toNat := by
  rw [c.hL]; rfl

/-- A valid modulus: the mask is that of `p q = n`, and `pre` holds
`privatePrecompute`'s words, or zeros. -/
theorem main_post {s t₃ t₄ t₆ u : State} (c : PPCtx s) (h : PPHead s t₃) (hm : t₄.mem = t₃.mem)
    (k : Keep [.rax, .rbp, .rsi] t₃ t₄) {minv mp mq : BitVec 64} {Mk : Bool}
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
      (s.gpr .rcx).toNat = true)
    (hN1 : 1 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
    (hR : R2Done t₄ t₆ (stackArg s 2) ((stackArg s 3).toNat * 8) (((s.gpr .rcx).toNat + 7) / 8) (s.gpr .r9).toNat
      (stackArg s 1).toNat minv mp mq (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat))
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)) Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip (List.replicate (s.gpr .rcx).toNat 0) <
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)))
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat))
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat))
      (Spec.Rsa.os2ip (List.replicate (s.gpr .r9).toNat 0)))
    (ho : OutPost t₆ u (stackArg s 2) (s.gpr .rdi) (((s.gpr .rcx).toNat + 7) / 8) (wsWords (s.gpr .r9).toNat)
      (wsWords (stackArg s 1).toNat) ((s.gpr .rsi).toNat * 8) (offP (((s.gpr .rcx).toNat + 7) / 8))
      (offQ (((s.gpr .rcx).toNat + 7) / 8) (s.gpr .r9).toNat) Mk) :
    gprPreserved s u ∧ ppContract.post s u := by
  refine ⟨gpr_of c h hm k (fun i hi => (ho.saved i hi).trans (hR.hfix i (by omega_using [hi]) (by simp [hFixed, hi])))
    (ho.rsp.trans (hR.keep.gpr (by decide))) fun x hx hne => ?_, ?_⟩
  · rw [ho.frame x (Nat.le_of_not_lt fun h' => hne _ h' (eq_add_ofs _ x)), hR.iscr x hx]
  have hL := preWords c
  simp only [ppContract]
  generalize hnb : Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat = nb at *
  generalize hpb : Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat = pb at *
  generalize hqb : Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat = qb at *
  have lnb : nb.length = (s.gpr .rcx).toNat := by rw [← hnb, bytesAt_length]
  have lpb : pb.length = (s.gpr .r9).toNat := by rw [← hpb, bytesAt_length]
  have lqb : qb.length = (stackArg s 1).toNat := by rw [← hqb, bytesAt_length]
  rw [os2ip_replicate_zero, os2ip_replicate_zero] at hMk
  generalize (s.gpr .rcx).toNat = kk at *
  generalize hww : ((kk + 7) / 8) = w at *
  have hMk' : Mk = decide (Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = Spec.Rsa.os2ip nb) := by
    rw [hMk]
    by_cases hpq : Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = Spec.Rsa.os2ip nb
    · have : 0 < Spec.Rsa.os2ip pb := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.zero_mul] at hpq; omega_using [hN1, hpq]
      simp [keyMask, hpq, this, show 0 < Spec.Rsa.os2ip nb by omega_using [hN1]]
    · simp [keyMask, hpq]
  have hw := wordsAt_out (m := u.mem) (D := s.gpr .rdi) (M := Mk) (VN := Spec.Rsa.os2ip nb)
    (VR := 2 ^ (128 * w) % Spec.Rsa.os2ip nb)
    (VP := if Mk then 2 ^ (128 * wsWords (s.gpr .r9).toNat) % Spec.Rsa.os2ip pb else 0)
    (VQ := if Mk then 2 ^ (128 * wsWords (stackArg s 1).toNat) % Spec.Rsa.os2ip qb else 0)
    (fun i hi => by rw [ho.segN i hi, word_eq_ofNat _ _ _ w hi, hR.nv.n])
    (fun i hi => by
      have r2 := hR.nv.r2
      rw [Nat.mod_eq_of_lt hR.nv.r2lt, ← Nat.pow_add, show 64 * w + 64 * w = 128 * w by omega_using []] at r2
      rw [ho.segR i hi, word_eq_ofNat _ _ _ w hi, r2])
    (fun i hi => by
      rw [ho.segP i hi]
      cases hm : Mk
      · simp [mask]
      · rw [word_eq_ofNat _ _ _ _ hi, hR.py hm]; simp)
    (fun i hi => by
      rw [ho.segQ i hi]
      cases hm : Mk
      · simp [mask]
      · rw [word_eq_ofNat _ _ _ _ hi, hR.qy hm]; simp)
  rw [hL]
  by_cases hpq : Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = Spec.Rsa.os2ip nb
  · have hM : Mk = true := by rw [hMk']; exact decide_eq_true hpq
    subst hM
    simp only [Spec.Rsa.privatePrecompute, hpq, ↓reduceIte, Spec.Rsa.publicPrecompute, lnb, hv, Option.map_some,
      Spec.Rsa.primeR2, lpb, lqb]
    refine ⟨by rw [ho.rax]; rfl, ?_⟩
    rw [hw]
    simp only [↓reduceIte, Spec.Rsa.modulusWords, hww]
    rfl
  · have hM : Mk = false := by rw [hMk']; exact decide_eq_false hpq
    subst hM
    simp only [Spec.Rsa.privatePrecompute, hpq, ↓reduceIte]
    exact ⟨by rw [ho.rax]; rfl, by rw [hw]; rfl⟩


/-- `PrivPre.code` with Montgomery multiplication `M`, from a state its
contract allows. -/
theorem code_wp (M : Mont) {s : State} (c : PPCtx s) :
    WP isa (PrivPre.code M.mm) s fun s' => gprPreserved s s' ∧ ppContract.post s s' := by
  have hZ := c.hZ
  have hk1 := c.hk1
  have hk2 := c.hk2
  have hpl2 := c.hpl2
  have hql2 := c.hql2
  unfold PrivPre.code
  refine WP.seq (WP.mono (head_ok c) fun t₁ h₁ => WP.seq (WP.mono h₁ fun t₂ h₂ => ?_))
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono h₂ fun t₃ h₃ => ?_
  have hnb₃ := Src.of_head (t := t₃) c.hnb (by rw [bytesAt_length]; exact c.hon) h₃.frame h₃.keep.2.1 h₃.keep.2.2
  refine WP.mono (invalid_ok h₃.rdx h₃.rcx hk1 hk2 (bytesAt_length _ _ _) (fun i hi => hnb₃.rd i (by
    rw [bytesAt_length]; exact hi)) (fun i hi => hnb₃.val i _)) fun t₄ ⟨hz, hm, k⟩ => ?_
  have hpre := ppPre_of c h₃ hm k
  refine WP.ite (!Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
    (s.gpr .rcx).toNat) (by simp [eval, hz]) (fun hb => ?_) (fun hb => ?_)
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
        (s.gpr .rcx).toNat = false := by simpa using hb
    exact WP.mono (fail_ok hpre.scr hpre.rdi (by omega_using [hZ]) (by omega_using [hk1]) (by omega_using [hk2]) hpre.hO hpre.hK hpre.out
      hpre.outSep)
      fun t hp => fail_post c h₃ hm k hp hv
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
        (s.gpr .rcx).toNat = true := by simpa using hb
    obtain ⟨-, hN1, -, -⟩ := crt_bounds hpre hv
    unfold PrivPre.main
    refine wp_seqs_append (by simp [Crt.nSetup]) (by simp [PrivPre.out]) (wp_seqs_append (by simp [Crt.nSetup])
      (by simp [PrivPre.r2Phase, PrivPre.r2At]) (WP.mono (front_ok M hpre hv) fun t₅ ⟨minv, mp, mq, hr⟩ =>
        WP.mono (r2Phase_ok M hpre hv hr rfl) fun t₆ hR => ?_))
    refine WP.mono (out_ok hR (by omega_using [hk1]) (by omega_using [hk2]) (by omega_using [hk2, hpl2]) (by omega_using [hk2, hql2]) hpre.z
      ((hR.hfix sOut (by decide) (by decide)).trans hpre.hO) (by rw [preWords c, Nat.mul_comm]) c.hwrap
      (by rw [hR.keep.2.2, k.2.2, h₃.keep.2.2]; exact c.hpreR) c.hS) fun u ho => main_post c h₃ hm k hv hN1 hR rfl ho

/-- `vg_rsa_private_precompute` with Montgomery multiplication `M`, given
that its code never loads MXCSR (which the registration file evaluates). -/
theorem code_correct (M : Mont) (hmx : (PrivPre.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : ppContract.pre s) :
    ∃ t s', Exec isa (PrivPre.code M.mm) s t s' ∧ abiPreserved s s' ∧ ppContract.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := code_wp M (ppCtx_of h)
  exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, hp⟩
end VG.Proof.Bignum.X86_64.PrivPre
