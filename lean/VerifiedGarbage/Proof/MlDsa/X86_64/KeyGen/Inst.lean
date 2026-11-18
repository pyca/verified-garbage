module

import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Top
public import VerifiedGarbage.Impl.MlDsa.X86_64.KeyGen.Inst
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttShortCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejBoundedShortCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.SimpleBitPack
import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.BitPack
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Backend
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Same
public import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Base
public import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Call
import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Montgomery
import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
public import VerifiedGarbage.Proof.MlDsa.X86_64.Round.Contracts
public import VerifiedGarbage.Proof.MlDsa.X86_64.Round.Arith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Round.Contracts
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Round.Arith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `MlDsa.X86_64.Round.Power2Round`, which only this module used -/

section

/-!
# ML-DSA on x86-64: `vg_mldsa_power2round`
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Round

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Round VG.Proof.MlDsa.Round
open VG.Spec.MlDsa
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep writesOnly gprPreserved_of)

/-- `a + 4095`, in 64 bits. -/
abbrev p2rX (x : BitVec 32) : BitVec 64 := BitVec.setWidth 64 x + BitVec.signExtend 64 (4095 : BitVec 32)

/-- The `t1` the body stores. -/
def t1V (x : BitVec 32) : BitVec 32 := BitVec.setWidth 32 (p2rX x >>> 13)

/-- The `t0` the body stores. -/
def t0V (x : BitVec 32) : BitVec 32 :=
  BitVec.setWidth 32 (condAddV (p2rX x &&& BitVec.signExtend 64 (8191 : BitVec 32))
    (BitVec.signExtend 64 (4095 : BitVec 32)) qImm)

theorem p2rBody_ok (s : State) (h1 : InRegions (s.rd ++ s.wr) (cfAddr (s.gpr .rdi) (s.gpr .rcx)) 4)
    (h2 : InRegions s.wr (cfAddr (s.gpr .rsi) (s.gpr .rcx)) 4)
    (h3 : InRegions s.wr (cfAddr (s.gpr .rdx) (s.gpr .rcx)) 4) :
    WP isa (.block (p2rBody ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      (s'.mem = (s.mem.writeW (cfAddr (s.gpr .rsi) (s.gpr .rcx))
          (t1V (s.mem.readW (cfAddr (s.gpr .rdi) (s.gpr .rcx)) 32))).writeW (cfAddr (s.gpr .rdx) (s.gpr .rcx))
          (t0V (s.mem.readW (cfAddr (s.gpr .rdi) (s.gpr .rcx)) 32)) ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0)) ∧
      Keep [.rax, .r8, .r9, .rcx] s s' := by
  refine WP.keep _ ?_ (Proof.MlKem.X86_64.writesOnly_of (by decide))
  unfold p2rBody condAdd
  xrun [h1, h2, h3, ea_cf, List.cons_append, List.nil_append, t1V, t0V, condAddV]

theorem p2rX_toNat {x : BitVec 32} (hx : x.toNat < q) : (p2rX x).toNat = x.toNat + 4095 := by
  rw [q_eq] at hx
  rw [BitVec.toNat_add, setWidth64_toNat, sx_toNat (by decide)]
  have : (4095 : BitVec 32).toNat = 4095 := rfl
  omega

theorem t1V_toNat {x : BitVec 32} (hx : x.toNat < q) : (t1V x).toNat = (x.toNat + 4095) / 8192 := by
  have e : (p2rX x >>> 13).toNat = (x.toNat + 4095) / 8192 := by
    rw [BitVec.toNat_ushiftRight, p2rX_toNat hx, Nat.shiftRight_eq_div_pow]
  rw [q_eq] at hx
  rw [t1V, BitVec.toNat_setWidth, e]
  omega_using []

theorem t0V_toNat {x : BitVec 32} (hx : x.toNat < q) :
    (t0V x).toNat = if (x.toNat + 4095) % 8192 < 4095 then (x.toNat + 4095) % 8192 + q - 4095
      else (x.toNat + 4095) % 8192 - 4095 := by
  have e : (p2rX x &&& BitVec.signExtend 64 (8191 : BitVec 32)).toNat = (x.toNat + 4095) % 8192 := by
    rw [BitVec.toNat_and, p2rX_toNat hx, sx_toNat (by decide),
      show (8191 : BitVec 32).toNat = 2 ^ 13 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have hs : (BitVec.signExtend 64 (4095 : BitVec 32)).toNat = 4095 := by decide
  have hq : qImm.toNat = q := rfl
  rw [t0V, BitVec.toNat_setWidth, condAddV_toNat (by decide) (by rw [e, hs, hq, q_eq]; omega_using []), e, hs, hq]
  have := Nat.mod_lt (x.toNat + 4095) (show 8192 > 0 by decide)
  rw [q_eq] at *
  split <;> omega_using []

section
variable {s₀ : State} (hp : power2RoundK.pre s₀)
include hp

theorem p2r_layout : Layout s₀ [.rdi] [.rsi, .rdx] where
  rd p hp' := by
    simp only [List.mem_singleton] at hp'; subst hp'; rw [hp.1]; simp
  wr o ho := by
    rw [hp.2.1]; simp only [List.mem_cons, List.not_mem_nil, or_false] at ho ⊢
    rcases ho with rfl | rfl <;> simp
  dis p hp' o ho := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp' ho
    subst hp'
    rcases ho with rfl | rfl
    exacts [hp.2.2.1, hp.2.2.2.1]
  pw := List.pairwise_cons.mpr ⟨fun b hb => by
    simp only [List.mem_singleton] at hb; subst hb; exact hp.2.2.2.2.1, List.pairwise_singleton _ _⟩

/-- The values the loop writes. -/
def p2rV (s₀ : State) (o : Reg) (k : Nat) : BitVec 32 :=
  if o = .rsi then t1V (coeffAt s₀.mem (s₀.gpr .rdi) k) else t0V (coeffAt s₀.mem (s₀.gpr .rdi) k)

theorem p2r_loop :
    WP isa (mapLoop p2rBody) s₀ (Inv s₀ [.rdi, .rsi, .rdx] [.rsi, .rdx] (p2rV s₀) (fun _ _ => True) 256) := by
  have hL := p2r_layout hp
  refine loop_ok (clob := [.rax, .r8, .r9, .rcx]) hL (by decide) (by decide) (fun _ _ _ _ => trivial)
    fun i hi s hI hc => ?_
  have ha : ∀ p ∈ [Reg.rdi, .rsi, .rdx], cfAddr (s.gpr p) (s.gpr .rcx) = coeffAddr (s₀.gpr p) (255 - i) :=
    fun p hp' => hI.addr hc hi hp'
  refine WP.mono (p2rBody_ok s (by rw [ha _ (by simp)]; exact hI.inR hL (by simp) (by omega_using []))
    (by rw [ha _ (by simp)]; exact hI.inW hL (by simp) (by omega_using []))
    (by rw [ha _ (by simp)]; exact hI.inW hL (by simp) (by omega_using []))) fun s' ⟨⟨hm, hc', hz⟩, hk⟩ =>
      ⟨⟨?_, hc', hz, trivial⟩, hk⟩
  rw [hm, ha _ (by simp), ha _ (by simp), ha _ (by simp), hI.read hL (by simp) (by omega_using [])]
  rfl

theorem p2r_correct :
    ∃ t s', Exec isa power2Round s₀ t s' ∧ abiPreserved s₀ s' ∧ power2RoundK.post s₀ s' := by
  obtain ⟨t, s', he, hI, hk⟩ := WP.keep [.rax, .rcx, .r8, .r9] (p2r_loop hp) (Proof.MlKem.X86_64.writesOnly_of (by decide))
  have hr : Reduced s₀.mem (s₀.gpr .rdi) := hp.2.2.2.2.2.2.2.2
  refine ⟨t, s', he, abiPreserved_of_exec (by decide) he (gprPreserved_of hk (by decide) hI.frame ?_), ?_, ?_⟩
  · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq]
    exact ⟨hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.1⟩
  · refine natPolyIs_of_toNat fun k hk => ?_
    rw [hI.done .rsi (by simp) k (by omega_using []) hk, map_get _ _ hk, p2rV, ite_eq_left_of_eq_true _ _ (eq_true rfl), t1V_toNat (hr k hk),
      power2Round_eq, ← polyAt_val hr hk]
    exact (Int.toNat_natCast _).symm
  · refine polyIs_of_toNat fun k hk => ?_
    rw [hI.done .rdx (by simp) k (by omega_using []) hk, map_get _ _ hk, p2rV, ite_eq_right_of_eq_false _ _ (eq_false (by decide)), t0V_toNat (hr k hk),
      power2Round_t0, polyAt_val hr hk]

end

theorem p2r_ct : ConstantTime isa power2RoundK.pre power2RoundK.pub power2Round :=
  VG.Taint.constantTime (A := X86_64.taint) (regsLo [.rdi, .rsi, .rdx, .rsp] [])
    (fun _ _ _ _ hp => agree_regsLo (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2]) fun _ h => by cases h)
    (by taint_decide)

/-- A state satisfying the precondition. -/
def p2rSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 1024⟩]

theorem power2Round_verified :
    Verified X86_64.target power2Round (power2RoundContract X86_64.abi) :=
  Verified.of_correct (fun _ hp => p2r_correct hp) p2r_ct (by
    round_implies [power2RoundContract, power2RoundSig, power2RoundK, X86_64.abi, X86_64.argRegs] [p2rSat]
      using p2rSat)

end VG.Proof.MlDsa.X86_64.Round

end

end

/-!
# ML-DSA key generation on x86-64, with this library's primitives

The x86-64 implementations of the primitives (`prims`) are verified, use at
most 16 bytes of stack (24 for `vg_mldsa_rej_ntt_poly4`), and never write
`rsp` but by calls nested at most twice (three times for
`vg_mldsa_rej_ntt_poly4`), with any implementation `v` of the polynomial
arithmetic (`prims_okWith`), so key generation with them is verified
(`keyGen_verifiedWith`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.KeyGen

open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.KeyGen

open VG.Proof.MlDsa.X86_64 (FnOk ArithImpl Comp Same Same.ok Code.allInstrs_of_all)
open VG.Impl.MlDsa.X86_64.Arith (Backend)

/-- A function of the polynomial arithmetic satisfies what the proofs of key generation need of it. -/
theorem calleeOf {k : Nat → Contract isa} {c : Prog isa} (h : FnOk k c) : Callee c k :=
  ⟨⟨0, by decide, h.ver⟩, h.nosp, h.mx, h.depth⟩

theorem prims_okWith (v : ArithImpl) : PrimsOk (primsWith v.code) where
  ntt := calleeOf v.ok.ntt
  add := calleeOf v.ok.add
  rejNtt := (have h := nospMx_of (c := prims.rejNtt) (by decide +kernel)
    ⟨⟨16, by decide, Sample.RejNttShort.verified⟩, h.1, h.2, by decide +kernel⟩ : Callee prims.rejNtt _)
  rejBounded := (have h := nospMx_of (c := prims.rejBounded) (by decide +kernel)
    ⟨⟨16, by decide, Sample.RejBoundedShort.verified⟩, h.1, h.2, by decide +kernel⟩ : Callee prims.rejBounded _)
  power2Round := (have h := nospMx_of (c := prims.power2Round) (by decide +kernel)
    ⟨⟨0, by decide, Round.power2Round_verified⟩, h.1, h.2, by decide +kernel⟩ : Callee prims.power2Round _)
  simpleBitPack := (have h := nospMx_of (c := prims.simpleBitPack) (by decide +kernel)
    ⟨⟨0, by decide, Pack.simpleBitPack_verified⟩, h.1, h.2, by decide +kernel⟩ : Callee prims.simpleBitPack _)
  bitPack := (have h := nospMx_of (c := prims.bitPack) (by decide +kernel)
    ⟨⟨0, by decide, Pack.bitPack_verified⟩, h.1, h.2, by decide +kernel⟩ : Callee prims.bitPack _)
  rej4 := ⟨v.ok.rej4.ver, v.ok.rej4.nosp, v.ok.rej4.mx, v.ok.rej4.depth⟩
  dotInv := fun c hc => calleeOf (v.ok.dotInv c hc)

/-! For any implementation of the polynomial arithmetic, that key
generation never writes `rsp` is checked by evaluating it with every
function of it empty (`keyGen_same`, as `sign_same`). -/

theorem keyGen_same {m mc : Prog isa → Bool} (hm : Comp m mc) {B : Backend} (h1 : mc B.ntt = true)
    (h5 : mc B.add = true) (h6 : mc B.rej4 = true) (h7 : mc B.dotInv4 = true) (h8 : mc B.dotInv5 = true)
    (h9 : mc B.dotInv7 = true) (p : Spec.MlDsa.Params) : Same m (keyGen (primsWith B) p) (keyGen (primsWith .empty) p) := by
  have hd : mc ((primsWith B).dotInv p.ℓ) = true := by
    unfold Prims.dotInv; split
    · exact h7
    · split
      · exact h8
      · exact h9
  have he : (primsWith Backend.empty).dotInv p.ℓ = .block [] := by
    unfold Prims.dotInv; split
    · rfl
    · split <;> rfl
  unfold keyGen
  same_tac hm
  all_goals rw [he]; exact Same.call hm hd _ _

theorem keyGen0_sp {p : Spec.MlDsa.Params}
    (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) :
    (keyGen (primsWith .empty) p).allInstrs (fun i => !isa.writesSp i) = true := by
  rcases hp with rfl | rfl | rfl <;> decide +kernel

variable (v : ArithImpl) {p : Spec.MlDsa.Params}
  (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87)
include hp

theorem keyGen_spSafe : (keyGen (primsWith v.code) p).all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (Same.ok (keyGen_same (Comp.all _) (Code.allInstrs_of_all v.ok.ntt.sp)
    (Code.allInstrs_of_all v.ok.add.sp) (Code.allInstrs_of_all v.ok.rej4.sp)
    (Code.allInstrs_of_all (v.ok.dotInv 4 (.inl rfl)).sp) (Code.allInstrs_of_all (v.ok.dotInv 5 (.inr (.inl rfl))).sp)
    (Code.allInstrs_of_all (v.ok.dotInv 7 (.inr (.inr rfl))).sp) p) (keyGen0_sp hp))

theorem keyGen_verifiedWith :
    Verified X86_64.target (keyGen (primsWith v.code) p) (Spec.MlDsa.keyGenContract p X86_64.abi 32) :=
  keyGen_verified (prims_okWith v) p hp

end VG.Proof.MlDsa.X86_64.KeyGen
