module

public import VerifiedGarbage.Proof.Dsa.RISCV64.Prime.CT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32

-- separate module: the probable-prime tests' contract, which builds beside the search's proofs, both of which the search's instances import

/-!
# DSA's probable-prime test on RISC-V: verified

As on PPC64LE (`Proof/Dsa/PPC64LE/Prime/Verified.lean`). `correct`: the
contract's postcondition (with the table, `abi.withConsts`, and 512 bytes
of stack, of which the round uses 96), from `code_ok`. `constantTime`: from
`code_ct`, the contract's public data (the arguments, the stack pointer, the
candidate, the tape's octets and the table's address) giving the same `PD`
in both runs. `satisfiable`: an all-ones candidate and an empty tape.
`verified`; `stack_le`: the code uses at most the contract's stack.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.Prime
open VG VG.RISCV64
open VG.Impl.Dsa.RISCV64.ProbablePrime
open VG.Proof.MillerRabin.RISCV64 (RoundImpl)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Two)

/-- The contract, with the table. -/
abbrev contract (bits : Nat) : Contract isa :=
  Proof.Dsa.ProbablePrime.contract (layout bits) (abi.withConsts VG.Impl.RsaKeyGen.TrialTable32.consts) 512

theorem consts_eq : VG.Impl.RsaKeyGen.TrialTable32.consts =
    [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)] := rfl

/-- `CIn` of the state without the table's region gives it of the state. -/
theorem CIn.ofStrip {bits : Nat} {σ : State} (h : CIn bits (stripConsts K σ)) : CIn bits σ :=
  ⟨h.sp16, h.spLo, List.mem_of_mem_take h.rd, h.wr, h.wR, h.wU, h.rU, h.sW, h.sR, h.sU, h.fw, h.fr, h.fu, h.size,
    h.odd, h.bl, h.alW, h.alU⟩

theorem pre_of {bits : Nat} {s : State} (hs : (contract bits).pre s) : CIn bits s ∧ ConstsOk K 512 s := by
  unfold contract Proof.Dsa.ProbablePrime.contract at hs
  rw [consts_eq] at hs
  obtain ⟨hp, hk⟩ := pre_consts.mp hs
  exact ⟨CIn.ofStrip (cin_of_pre bits _ hp), hk⟩

theorem correct (Ri : RoundImpl) {bits : Nat} (hb : Bits bits) (s : State) (hs : (contract bits).pre s) :
    ∃ t s', Exec isa (code bits Ri.name Ri.code) s t s' ∧ abiPreserved s s' ∧ (contract bits).post s s' := by
  obtain ⟨h, hk⟩ := pre_of hs
  obtain ⟨t, s', he, hc⟩ := code_ok Ri hb h hk
  refine ⟨t, s', he, hc.abi, ?_⟩
  unfold contract Proof.Dsa.ProbablePrime.contract
  rw [consts_eq]
  refine post_consts.mpr ?_
  sig_post [Proof.Dsa.ProbablePrime.sig, abi, argRegs]
  refine ⟨?_, hc.keeps, hc.used⟩
  rw [hc.a0, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have := status_le (res bits s)
  simp only [res, cand, tape] at this ⊢
  omega

theorem constantTime (Ri : RoundImpl) {bits : Nat} (hb : Bits bits) :
    ConstantTime isa (contract bits).pre (contract bits).pub (code bits Ri.name Ri.code) := by
  refine RelCT.constantTime ((code_ct Ri hb).mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ?_) fun _ _ h => h)
  obtain ⟨c₁, k₁⟩ := pre_of h₁
  obtain ⟨c₂, k₂⟩ := pre_of h₂
  unfold contract Proof.Dsa.ProbablePrime.contract at hp
  rw [consts_eq] at hp
  obtain ⟨hp, hsy⟩ := pub_consts.mp hp
  sig_pub [Proof.Dsa.ProbablePrime.sig, abi, argRegs] at hp
  obtain ⟨hsp, hl, h0, h1, h2, h3, h4⟩ := hp
  obtain ⟨hc, ht⟩ := List.cons.inj hl
  have ht' : tape s₁ = tape s₂ :=
    (List.map_inj_right fun _ _ e => BitVec.eq_of_toNat_eq e).mp ht
  refine ⟨⟨s₁.gpr .a0, s₁.gpr .a1, s₁.gpr .a2, s₁.gpr .a3, s₁.gpr .a4, s₁.sp,
    s₁.syms VG.Impl.RsaKeyGen.TrialTable32.symbol, cand bits s₁, tape s₁⟩,
    ⟨hb, c₁, k₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨hb, c₂, k₂, h0.symm, h1.symm, h2.symm, h3.symm, h4.symm, hsp.symm, (hsy _ List.mem_cons_self).symm,
      hc.symm, ht'.symm⟩⟩

/-! ## A state that meets the precondition -/

/-- The witness's memory: an all-ones candidate at `0x10000`, the table at
`0x30000`. -/
def satMemory (bits : Nat) : Mem := fun a =>
  if (a - 0x10000#64).toNat < bits / 8 then 0xFF#8
  else constMem 0x30000#64 VG.Impl.RsaKeyGen.TrialTable32.packed a

/-- The witness: `ws` of 2000 words at `0x10000`, an empty tape at
`0x5000`, `used` at `0x2000`, the stack below `0x20000`. -/
def satState (bits : Nat) : State where
  gpr r := if r = .a0 then 0x10000 else if r = .a1 then 2000 else if r = .a2 then 0x5000 else
    if r = .a4 then 0x2000 else 0
  sp := 0x20000
  mem := satMemory bits
  rd := [⟨0x5000, 0⟩, ⟨0x30000, 8192⟩]
  wr := [⟨0x10000, 16000⟩, ⟨0x2000, 8⟩]
  unknowns _ := 0
  syms _ := 0x30000

theorem os2ip_ones : ∀ (n acc : Nat),
    (List.replicate n (0xFF#8)).foldl (fun x b => 256 * x + b.toNat) acc = acc * 256 ^ n + (256 ^ n - 1)
  | 0, acc => by simp
  | n + 1, acc => by
    rw [List.replicate_succ, List.foldl_cons, os2ip_ones n, Nat.pow_succ]
    have ff : (0xFF#8).toNat = 255 := rfl
    rw [ff]
    have pos : 0 < 256 ^ n := Nat.pow_pos (by decide)
    generalize 256 ^ n = p at *
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    grind

theorem sat_candidate {bits : Nat} (hb : Bits bits) :
    Proof.Dsa.ProbablePrime.candidateAt (layout bits) (satMemory bits) 0x10000#64 = 2 ^ bits - 1 := by
  have hs := shape_of hb
  have h384 : bits / 8 ≤ 384 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  have bytes : Spec.Rsa.bytesAt (satMemory bits) (0x10000#64 + BitVec.ofNat 64 (layout bits).candidate)
      ((layout bits).bits / 8) = List.replicate (bits / 8) 0xFF#8 := by
    change Spec.Rsa.bytesAt (satMemory bits) (0x10000#64 + BitVec.ofNat 64 0) (bits / 8) = _
    unfold Spec.Rsa.bytesAt
    apply List.ext_getElem (by simp)
    intro i hi _
    simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
    simp only [List.length_map, List.length_range] at hi
    unfold satMemory
    rw [ite_eq_left (by simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)]
  unfold Proof.Dsa.ProbablePrime.candidateAt
  rw [bytes, VG.Proof.Dsa.decodeBE_os2ip]
  unfold Spec.Rsa.os2ip
  rw [os2ip_ones, Nat.zero_mul, Nat.zero_add]
  rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul, show 8 * (bits / 8) = bits by rw [← hs.hlen]; exact hs.hlen8]

theorem sat_odd {bits : Nat} (hb : Bits bits) :
    Proof.Dsa.ProbablePrime.candidateAt (layout bits) (satMemory bits) 0x10000#64 % 2 = 1 := by
  rw [sat_candidate hb]
  have : 2 ^ bits % 2 = 0 := by
    rw [show bits = (bits - 1) + 1 by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide, Nat.pow_succ]; omega
  have := Nat.two_pow_pos bits
  omega

theorem sat_length {bits : Nat} (hb : Bits bits) :
    Spec.Dsa.bitLength (Proof.Dsa.ProbablePrime.candidateAt (layout bits) (satMemory bits) 0x10000#64) = bits := by
  rw [sat_candidate hb]
  have low : 1 ≤ bits := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  have half : 2 ^ bits = 2 ^ (bits - 1) * 2 := by
    rw [← Nat.pow_succ]; congr 1; omega
  have pos := Nat.two_pow_pos (bits - 1)
  exact (VG.Proof.Dsa.bitLength_iff_bounds (by omega)).mpr ⟨by omega, by omega⟩

theorem sat_table {bits : Nat} (hb : Bits bits) :
    Abi.constsHeld (satMemory bits) (fun _ => 0x30000#64) VG.Impl.RsaKeyGen.TrialTable32.consts := by
  intro c mem
  obtain rfl := List.mem_singleton.mp mem
  intro i index
  dsimp only at index ⊢
  have fit : 8 * VG.Impl.RsaKeyGen.TrialTable32.packed.length ≤ 2 ^ 64 := by
    rw [VG.Proof.RsaKeyGen.TrialTable32.packed_length]; decide
  have small : i < 1024 := by rw [VG.Proof.RsaKeyGen.TrialTable32.packed_length] at index; exact index
  have h384 : bits / 8 ≤ 384 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  refine Eq.trans (Mem.readW_congr (m := satMemory bits)
    (m' := constMem 0x30000 VG.Impl.RsaKeyGen.TrialTable32.packed) ?_)
    (constMem_held 0x30000 VG.Impl.RsaKeyGen.TrialTable32.packed fit i index)
  intro j hj
  change (if _ then _ else _) = _
  rw [ite_eq_right (by simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)]
  rfl

theorem packed_regions (f : String → Addr) :
    Abi.constRegions f [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)] =
      [⟨f VG.Impl.RsaKeyGen.TrialTable32.symbol, 8192⟩] := by
  rw [Abi.constRegions_cons, Abi.constRegions_nil, VG.Proof.RsaKeyGen.TrialTable32.packed_length]

theorem satisfiable {bits : Nat} (hb : Bits bits) : ∃ s, (contract bits).pre s := by
  have hs := shape_of hb
  have hkw : keyOff + 8 * keyWords bits ≤ 16000 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  refine ⟨satState bits, ?_⟩
  unfold contract Proof.Dsa.ProbablePrime.contract
  rw [consts_eq]
  refine pre_consts.mpr ⟨?_, ?_⟩
  · sig_pre [Proof.Dsa.ProbablePrime.sig, abi, argRegs, stripConsts]
    sig_and_intros
    all_goals first
      | exact sat_odd hb
      | exact sat_length hb
      | (show _ ≤ 8 * 2000; omega)
      | decide
      | exact Region.disjoint_of_sep (by decide)
  · refine ⟨?_, consts_eq ▸ sat_table hb, ?_, ?_⟩
    · simp only [constRegs, packed_regions]; rfl
    · simp only [constRegs, packed_regions]
      simp only [List.forall_mem_singleton, satState, abi, List.forall_mem_cons, stackBelow]
      exact ⟨by decide, ⟨Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide)⟩,
        Region.disjoint_of_sep (by decide)⟩
    · simp only [constRegs, packed_regions, List.forall_mem_singleton, satState]
      decide

/-- `vg_dsa_probable_prime_{bits}`, calling the round `Ri`, is verified. -/
theorem verified (Ri : RoundImpl) (bits : Nat) (hb : Bits bits := by decide) :
    Verified target (code bits Ri.name Ri.code) (contract bits) :=
  ⟨correct Ri hb, constantTime Ri hb, satisfiable hb⟩

/-- The test uses the stack of the round it calls. -/
theorem prime_stack (bits : Nat) (name : String) (rc : Prog isa) :
    sdepth (code bits name rc) ≤ sdepth rc := by
  simp only [code, body, loadC, exit, sdepth, VG.Impl.MillerRabin.RISCV64.Blinded.millerRabin,
    VG.Impl.MillerRabin.RISCV64.Blinded.draw, VG.Impl.MillerRabin.RISCV64.Blinded.round,
    VG.Impl.RsaKeyGen.RISCV64.Trial.trial, VG.Impl.MillerRabin.RISCV64.Search.roundCall, Nat.max_le,
    Nat.zero_le, Nat.le_refl, true_and, and_true]
  have z : ∀ c, sdepth c = 0 → sdepth c ≤ sdepth rc := fun _ h => h ▸ Nat.zero_le _
  exact ⟨z _ (by decide), z _ (by decide), z _ (by decide), z _ (by decide), z _ (by decide), z _ (by decide)⟩

/-- The test uses at most the contract's 512 bytes of stack. -/
theorem stack_le (Ri : RoundImpl) (bits : Nat) : sdepth (code bits Ri.name Ri.code) ≤ 512 :=
  Nat.le_trans (prime_stack bits Ri.name Ri.code) (Nat.le_trans Ri.stack (by decide))

end VG.Proof.Dsa.RISCV64.Prime
